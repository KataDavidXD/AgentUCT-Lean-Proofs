import NativeCausalGenerated





set_option autoImplicit false
set_option maxRecDepth 16384
set_option maxHeartbeats 4000000
set_option linter.constructorNameAsVariable false
noncomputable section
namespace AgentUCTNativeBudget
open AgentUCTPanelAllocation AgentUCTNativeRepair AgentUCTNativeRefinement AgentUCTPaper

theorem root_margin_positive_error_exists (t : TariffInput) (c gamma delta good : ℝ)
    (hm : RootMargins t c gamma delta good) :
    ∃ epsilon : ℝ,0 < epsilon ∧ epsilon < 1/2 ∧ ErrorMargins t c gamma delta good (10*gamma*epsilon) := by
  let s := min delta (min (delta-gamma*(t.w4-t.bge))
    (min (gamma*(t.w4-t.bge)) (min (gamma*(normalForecastBill t-(t.bge+tailBill t))-delta)
    (min (gamma*normalForecastBill t-delta-bonusGap2 c)
    (min (gamma*normalForecastBill t-delta-bonusGap3 c)
      (gamma*(t.w4-t.bge)+bonusGap2 c-good))))))
  have hs : 0 < s := by
    dsimp only [s]
    simp only [lt_min_iff]
    refine ⟨hm.delta_pos,?_,hm.next_other_gap,?_,?_,?_,?_⟩
    · linarith [hm.next_initial_gap]
    · linarith [hm.complete_initial_gap]
    · linarith [hm.complete_after9_gap]
    · linarith [hm.complete_after10_gap]
    · linarith [hm.next_after9_gap]
  have bounds : s ≤ delta ∧ s ≤ delta-gamma*(t.w4-t.bge) ∧ s ≤ gamma*(t.w4-t.bge) ∧
      s ≤ gamma*(normalForecastBill t-(t.bge+tailBill t))-delta ∧
      s ≤ gamma*normalForecastBill t-delta-bonusGap2 c ∧
      s ≤ gamma*normalForecastBill t-delta-bonusGap3 c ∧
      s ≤ gamma*(t.w4-t.bge)+bonusGap2 c-good := by
    have h : s ≤ s := le_rfl
    conv at h => rhs; dsimp only [s]
    simpa only [le_min_iff] using h
  let epsilon := min (s/(40*gamma+4)) (1/4)
  have hd : 0 < 40*gamma+4 := by linarith [hm.gamma_pos]
  have hep : 0 < epsilon := lt_min (div_pos hs hd) (by norm_num)
  have hequarter : epsilon ≤ 1/4 := min_le_right _ _
  have hemul : epsilon*(40*gamma+4) ≤ s := (le_div_iff₀ hd).mp (min_le_left _ _)
  have herr : 2*(10*gamma*epsilon) < s := by nlinarith
  refine ⟨epsilon,hep,by linarith,?_⟩
  rcases bounds with ⟨b1,b2,b3,b4,b5,b6,b7⟩
  constructor <;> linarith

theorem feasible_tariffs_positive_floor (c : ℝ) (hc : 0 < c) (a : Act) :
    tariff (feasibleTariffs c) a = 0 ∨ 1/2 ≤ tariff (feasibleTariffs c) a := by
  have hg := positive_bounded_feasible_good c hc
  have hdelta : 0 < feasibleDelta c := by unfold feasibleDelta; nlinarith [hg.1]
  have h2 := bonus_gap_two_positive c hc
  have h3 := bonus_gap_three_positive c hc
  cases a <;> dsimp only [tariff,taskTariff,feasibleTariffs] <;>
    (try split_ifs) <;> (try simp_all only [true_or]) <;> (try norm_num) <;> (try right) <;> nlinarith

def perturbedPriors (t : TariffInput) (epsilon : ℝ) (a : Act) : ℝ :=
  if tariff t a = 0 then 0 else tariff t a+epsilon/2

def perturbedCaps (t : TariffInput) (epsilon : ℝ) (a : Act) : ℝ :=
  if tariff t a = 0 then 0 else tariff t a+epsilon

theorem perturbed_initial_prices_admissible (t : TariffInput) (epsilon : ℝ)
    (he : 0 < epsilon) (hehalf : epsilon < 1/2)
    (hf : ∀ a,tariff t a = 0 ∨ 1/2 ≤ tariff t a) :
    AdmissibleInitialPrices t (perturbedPriors t epsilon) (perturbedCaps t epsilon) epsilon := by
  have hclip : ∀ a,min (perturbedCaps t epsilon a) (perturbedPriors t epsilon a) = perturbedPriors t epsilon a := by
    intro a
    apply min_eq_right
    unfold perturbedCaps perturbedPriors
    split_ifs <;> linarith
  refine ⟨he.le,?_,?_,?_,?_⟩
  · intro a
    unfold perturbedCaps
    split_ifs with hz <;> linarith
  · intro a
    rw [hclip]
    unfold perturbedPriors
    split_ifs with hz
    · simp [hz,he.le]
    · rw [show tariff t a+epsilon/2-tariff t a = epsilon/2 by ring,abs_of_pos (by linarith : 0 < epsilon/2)]
      linarith
  · intro a hz
    rw [hclip]
    simp [perturbedPriors,hz]
  · intro a
    rcases hf a with hz | hn
    · exact Or.inl hz
    · exact Or.inr (lt_of_lt_of_le hehalf hn)

theorem perturbed_initial_nonzero_action_error (t : TariffInput) (epsilon : ℝ) (a : Act)
    (he : 0 < epsilon) (ha : tariff t a ≠ 0) :
    0 < |min (perturbedCaps t epsilon a) (perturbedPriors t epsilon a)-tariff t a| := by
  simp only [perturbedCaps,perturbedPriors,if_neg ha]
  rw [min_eq_right (by linarith),show tariff t a+epsilon/2-tariff t a = epsilon/2 by ring,
    abs_of_pos (by linarith : 0 < epsilon/2)]
  linarith

theorem causal_error_class_nonempty (c : ℝ) (hc : 0 < c) :
    ∃ epsilon : ℝ,0 < epsilon ∧
      AdmissibleInitialPrices (feasibleTariffs c) (perturbedPriors (feasibleTariffs c) epsilon)
        (perturbedCaps (feasibleTariffs c) epsilon) epsilon ∧
      ErrorMargins (feasibleTariffs c) c 1 (feasibleDelta c) (feasibleGood c) (10*epsilon) ∧
      0 < |min (perturbedCaps (feasibleTariffs c) epsilon (.hydeRetriever 1))
        (perturbedPriors (feasibleTariffs c) epsilon (.hydeRetriever 1))-
        tariff (feasibleTariffs c) (.hydeRetriever 1)| := by
  obtain ⟨epsilon,he,hh,hm⟩ := root_margin_positive_error_exists _ c 1 _ _ (root_structural_conditions_nonempty c hc)
  refine ⟨epsilon,he,perturbed_initial_prices_admissible _ epsilon he hh
    (feasible_tariffs_positive_floor c hc),by simpa using hm,?_⟩
  exact perturbed_initial_nonzero_action_error _ epsilon _ he (by simp [tariff,feasibleTariffs,taskTariff])

theorem initial_unit_resources_no_bge (r : Unit × List Act) (hr : r ∈ initialCache) :
    resourceAction r ≠ .hydeRetriever 1 := by
  have h : ∀ r ∈ initialCache,resourceAction r ≠ .hydeRetriever 1 := by decide
  exact h r hr

variable {Qid : Type*} [DecidableEq Qid] [Encodable Qid]
theorem common_initial_bge_pool_empty (qids : Finset Qid) (t : TariffInput) (caps : Act → ℝ)
    (qid : Qid) (reward : List Act → ℝ) (r : Qid × List Act) (ha : resourceAction r = .hydeRetriever 1) :
    selectedCallPool (taskMeans qids t caps qid (initialization reward)) r = ∅ := by
  apply Finset.eq_empty_iff_forall_notMem.mpr
  intro i hi
  obtain ⟨hseen,hact⟩ := selected_call_pool_valid _ r i hi
  obtain ⟨hs,hp,hm⟩ := task_means_full_cache_metadata_and_bill qids t caps qid (initialization reward)
  rw [hs] at hseen
  obtain ⟨s,hs,hid⟩ := Finset.mem_image.mp hseen
  rw [← hid,(hm s hs).1,ha] at hact
  have hu : ((),s.2) ∈ initialCache := by
    have hprod := hs
    rw [own_panel_cache_product] at hprod
    have hp := (Finset.mem_product.mp hprod).2
    rw [← initialization_cache_exact reward,← unit_panel_cache_is_own,own_panel_cache_product]
    exact Finset.mem_product.mpr ⟨by simp,hp⟩
  exact initial_unit_resources_no_bge _ hu (by simpa [resourceAction] using hact)

theorem common_initial_bge_actual_nonzero_error (qids : Finset Qid) (t : TariffInput)
    (qid : Qid) (reward : List Act → ℝ) (epsilon : ℝ) (he : 0 < epsilon)
    (hb : t.bge ≠ 0) :
    0 < |liveReceiptPrice (perturbedPriors t epsilon) (perturbedCaps t epsilon)
      (taskMeans qids t (perturbedCaps t epsilon) qid (initialization reward)) (qid,aCold.take 2)-t.bge| := by
  have ha : resourceAction (qid,aCold.take 2) = .hydeRetriever 1 := by
    simp [resourceAction,aCold,leaf]
  unfold liveReceiptPrice
  rw [common_initial_bge_pool_empty qids t _ qid reward _ ha]
  simp only [onlineMean,Finset.card_empty,Finset.sum_empty,Nat.cast_zero,zero_add,add_zero,div_one,ha]
  have ht : tariff t (.hydeRetriever 1) = t.bge := by simp [tariff,taskTariff]
  simpa only [ht] using perturbed_initial_nonzero_action_error t epsilon (.hydeRetriever 1) he (by rwa [ht])

end AgentUCTNativeBudget
