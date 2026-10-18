import NativeReceiptInvariants




set_option autoImplicit false
set_option maxRecDepth 16384
set_option maxHeartbeats 4000000
set_option linter.constructorNameAsVariable false
noncomputable section
namespace AgentUCTNativeBudget
open AgentUCTPanelAllocation AgentUCTNativeRepair AgentUCTNativeRefinement AgentUCTPaper
variable {Qid : Type*} [DecidableEq Qid] [Encodable Qid]

theorem list_sum_point_error {R : Type*} (prices target : R → ℝ) (epsilon : ℝ)
    (resources : List R) (he : ∀ r,|prices r-target r| ≤ epsilon) :
    |(resources.map prices).sum-(resources.map target).sum| ≤ (resources.length : ℝ)*epsilon := by
  induction resources with
  | nil => simp
  | cons r resources ih =>
      calc
        _ = |(prices r-target r)+((resources.map prices).sum-(resources.map target).sum)| := by
          simp only [List.map_cons,List.sum_cons]; congr 1; ring
        _ ≤ |prices r-target r|+|(resources.map prices).sum-(resources.map target).sum| := abs_add_le _ _
        _ ≤ epsilon+(resources.length : ℝ)*epsilon := add_le_add (he r) ih
        _ = _ := by simp; ring

theorem next_unpaid_stable_support_error {R : Type*} [DecidableEq R] (prices target : R → ℝ)
    (epsilon : ℝ) (he : 0 ≤ epsilon) (resources : List R)
    (hp : ∀ r,|prices r-target r| ≤ epsilon)
    (hs : ∀ r,prices r ≤ 0 ↔ target r ≤ 0) :
    |nextUnpaidBill ∅ prices resources-nextUnpaidBill ∅ target resources| ≤ epsilon := by
  induction resources with
  | nil => simpa [nextUnpaidBill] using he
  | cons r resources ih =>
      simp only [nextUnpaidBill,Finset.notMem_empty,false_or]
      by_cases hn : target r ≤ 0
      · rw [if_pos hn,if_pos ((hs r).mpr hn)]
        exact ih
      · rw [if_neg hn,if_neg (fun h => hn ((hs r).mp h))]
        exact hp r

omit [Encodable Qid] in
theorem source_suffix_length_le (cache : Finset (Qid × List Act)) (free : Qid → List Act → Bool)
    (qid : Qid) (path : List Act) : (sourceSuffix cache free qid path).length ≤ path.length+1 := by
  dsimp only [sourceSuffix]
  have h1 := List.length_filter_le (fun resource : Qid × List Act => !free resource.1 resource.2)
    (((List.range (path.length+1)).filter (fun i => lastWarmDepth cache qid path < i)).map (fun i => (qid,path.take i)))
  have h2 := List.length_filter_le (fun i => decide (lastWarmDepth cache qid path < i)) (List.range (path.length+1))
  simp only [List.length_map,List.length_range] at h1 h2
  exact h1.trans h2

omit [Encodable Qid] in
theorem source_terminal_quote_error (mode : ForecastMode) (cache : Finset (Qid × List Act))
    (free : Qid → List Act → Bool) (prices target : Qid × List Act → ℝ) (epsilon : ℝ)
    (he : 0 ≤ epsilon) (hp : ∀ r,|prices r-target r| ≤ epsilon)
    (hs : ∀ r,prices r ≤ 0 ↔ target r ≤ 0) (qid : Qid) (path : List Act) (hl : path.length = 9) :
    |sourceQidQuote mode cache free prices qid path-sourceQidQuote mode cache free target qid path| ≤ 10*epsilon := by
  cases mode with
  | unpriced => simpa [sourceQidQuote] using mul_nonneg (by norm_num : (0:ℝ) ≤ 10) he
  | complete =>
      have hh := list_sum_point_error prices target epsilon (sourceSuffix cache free qid path) hp
      have hn : ((sourceSuffix cache free qid path).length : ℝ) ≤ 10 := by
        exact_mod_cast (by simpa only [hl] using source_suffix_length_le cache free qid path)
      exact hh.trans (mul_le_mul_of_nonneg_right hn he)
  | next =>
      exact (next_unpaid_stable_support_error prices target epsilon he _ hp hs).trans (by nlinarith)

theorem task_live_support_stable (qids : Finset Qid) (t : TariffInput) (priors caps : Act → ℝ)
    (qid : Qid) (epsilon : ℝ) (he : 0 ≤ epsilon) (hc : ∀ a,tariff t a ≤ caps a)
    (hp : ∀ a,|min (caps a) (priors a)-tariff t a| ≤ epsilon)
    (hz : ∀ a,tariff t a = 0 → min (caps a) (priors a) = 0)
    (hf : ∀ a,tariff t a = 0 ∨ epsilon < tariff t a)
    (before : List (TreeEvaluation Act)) (r : Qid × List Act) :
    liveReceiptPrice priors caps (taskMeans qids t caps qid before) r ≤ 0 ↔ tariff t (resourceAction r) ≤ 0 := by
  rcases hf (resourceAction r) with ht | ht
  · rw [task_live_zero_action_exact qids t priors caps qid hc hz before r ht,ht]
  · have hh := task_live_price_error_from_initial_priors qids t priors caps qid epsilon he hc hp before r
    have hlo := (abs_le.mp hh).1
    have htpos : 0 < tariff t (resourceAction r) := lt_of_le_of_lt he ht
    have hppos : 0 < liveReceiptPrice priors caps (taskMeans qids t caps qid before) r := by linarith
    exact iff_of_false (not_le.mpr hppos) (not_le.mpr htpos)

def causalPenalty (qids : Finset Qid) (mode : ForecastMode) (t : TariffInput)
    (priors caps : Act → ℝ) (qid : Qid) (beta Cref : ℝ) :=
  livePanelPenalty qids mode budgetTape (fun _ _ => false) priors caps (taskMeans qids t caps qid)
    (fun _ _ => 0) beta Cref

theorem causal_panel_mc16_error (qids : Finset Qid) (mode : ForecastMode) (t : TariffInput)
    (priors caps : Act → ℝ) (qid : Qid) (epsilon : ℝ) (he : 0 ≤ epsilon) (hc : ∀ a,tariff t a ≤ caps a)
    (hp : ∀ a,|min (caps a) (priors a)-tariff t a| ≤ epsilon)
    (hz : ∀ a,tariff t a = 0 → min (caps a) (priors a) = 0)
    (hf : ∀ a,tariff t a = 0 ∨ epsilon < tariff t a)
    (before : List (TreeEvaluation Act)) (p : List Act) (a : Act)
    (hl : Legal p) (ha : a ∈ available p) :
    |sourcePanelMC16 qids mode (ownPanelCache qids before) (fun _ _ => false)
       (liveReceiptPrice priors caps (taskMeans qids t caps qid before)) (budgetTape.completion before p a)-
     sourcePanelMC16 qids mode (ownPanelCache qids before) (fun _ _ => false)
       (fun r => tariff t (resourceAction r)) (budgetTape.completion before p a)| ≤
      (qids.card : ℝ)*(10*epsilon) := by
  have hh : ∀ i : Fin 16, ∀ q ∈ qids,
      |sourceQidQuote mode (ownPanelCache qids before) (fun _ _ => false)
         (liveReceiptPrice priors caps (taskMeans qids t caps qid before)) q (budgetTape.completion before p a i)-
       sourceQidQuote mode (ownPanelCache qids before) (fun _ _ => false)
         (fun r => tariff t (resourceAction r)) q (budgetTape.completion before p a i)| ≤ 10*epsilon := by
    intro i q hq
    exact source_terminal_quote_error mode _ _ _ _ epsilon he
      (task_live_price_error_from_initial_priors qids t priors caps qid epsilon he hc hp before)
      (task_live_support_stable qids t priors caps qid epsilon he hc hp hz hf before) q _
      (budget_tape_supported.2 before p a i hl ha).1.2
  have hs : ∀ i : Fin 16,
      |sourcePanelSample qids mode (ownPanelCache qids before) (fun _ _ => false)
         (liveReceiptPrice priors caps (taskMeans qids t caps qid before)) (budgetTape.completion before p a i)-
       sourcePanelSample qids mode (ownPanelCache qids before) (fun _ _ => false)
         (fun r => tariff t (resourceAction r)) (budgetTape.completion before p a i)| ≤ (qids.card : ℝ)*(10*epsilon) := by
    intro i
    simp only [sourcePanelSample,← Finset.sum_sub_distrib]
    exact (Finset.abs_sum_le_sum_abs _ _).trans (by simpa using Finset.sum_le_sum (fun q hq => hh i q hq))
  unfold sourcePanelMC16
  rw [← sub_div,abs_div,show |(16:ℝ)| = 16 by norm_num]
  apply (div_le_iff₀ (by norm_num : (0:ℝ) < 16)).mpr
  rw [← Finset.sum_sub_distrib]
  have hsum := Finset.sum_le_sum (s := (Finset.univ : Finset (Fin 16))) (fun i _ => hs i)
  exact (Finset.abs_sum_le_sum_abs _ _).trans (by simpa [mul_comm] using hsum)

theorem causal_root_index_error (qids : Finset Qid) (mode : ForecastMode) (t : TariffInput)
    (priors caps : Act → ℝ) (qid : Qid) (epsilon c beta Cref : ℝ) (he : 0 ≤ epsilon)
    (hscale : 0 ≤ beta/Cref) (hc : ∀ a,tariff t a ≤ caps a)
    (hp : ∀ a,|min (caps a) (priors a)-tariff t a| ≤ epsilon)
    (hz : ∀ a,tariff t a = 0 → min (caps a) (priors a) = 0)
    (hf : ∀ a,tariff t a = 0 ∨ epsilon < tariff t a)
    (before : List (TreeEvaluation Act)) (q : Fin 8) :
    |indexScore c (causalPenalty qids mode t priors caps qid beta Cref) before [] (.query q)-
      indexScore c (referencePenalty qids mode t beta Cref) before [] (.query q)| ≤
      10*(penaltyScale qids beta Cref)*epsilon := by
  have hh := causal_panel_mc16_error qids mode t priors caps qid epsilon he hc hp hz hf before [] (.query q)
    legal_nil (by simp [available,rootOrder])
  have ho : (if mode = .next ∨ mode = .unpriced then 0 else (0:ℝ)) = 0 := by split_ifs <;> rfl
  let d := sourcePanelMC16 qids mode (ownPanelCache qids before) (fun _ _ => false)
          (liveReceiptPrice priors caps (taskMeans qids t caps qid before)) (budgetTape.completion before [] (.query q))-
        sourcePanelMC16 qids mode (ownPanelCache qids before) (fun _ _ => false)
          (fun r => tariff t (resourceAction r)) (budgetTape.completion before [] (.query q))
  have hid : indexScore c (causalPenalty qids mode t priors caps qid beta Cref) before [] (.query q)-
      indexScore c (referencePenalty qids mode t beta Cref) before [] (.query q) = -(beta/Cref)*d := by
    dsimp only [d,indexScore,treeIndex,causalPenalty,livePanelPenalty,livePanelForecast,referencePenalty]
    rw [ho,add_zero]
    ring
  rw [hid,abs_mul,abs_neg,abs_of_nonneg hscale]
  exact (mul_le_mul_of_nonneg_left hh hscale).trans_eq (by unfold penaltyScale; ring)

end AgentUCTNativeBudget
