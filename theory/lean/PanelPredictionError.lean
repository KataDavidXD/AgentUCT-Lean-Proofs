import PanelBudgetReporting





set_option autoImplicit false
set_option maxRecDepth 8192
set_option maxHeartbeats 4000000
set_option linter.constructorNameAsVariable false
noncomputable section
namespace AgentUCTPanelAllocation
open AgentUCTNativeRefinement AgentUCTNativeRepair AgentUCTPaper
variable {Qid : Type*} [DecidableEq Qid]

theorem online_mean_absolute_error {I : Type*} (prior target epsilon : ℝ)
    (samples : Finset I) (value : I → ℝ)
    (hp : |prior-target| ≤ epsilon)
    (hv : ∀ i ∈ samples, |value i-target| ≤ epsilon) :
    |onlineMean prior samples value-target| ≤ epsilon := by
  have hd : (0 : ℝ) < (samples.card : ℝ)+1 := by positivity
  obtain ⟨hpl,hpu⟩ := abs_le.mp hp
  have hsumlo : (samples.card : ℝ)*(target-epsilon) ≤ ∑ i ∈ samples,value i := by
    calc
      _ = ∑ _i ∈ samples,(target-epsilon) := by simp; ring
      _ ≤ _ := Finset.sum_le_sum (fun i hi => by have hh := (abs_le.mp (hv i hi)).1; linarith)
  have hsumhi : (∑ i ∈ samples,value i) ≤ (samples.card : ℝ)*(target+epsilon) := by
    calc
      _ ≤ ∑ _i ∈ samples,(target+epsilon) := Finset.sum_le_sum
        (fun i hi => by have hh := (abs_le.mp (hv i hi)).2; linarith)
      _ = _ := by simp; ring
  apply abs_le.mpr
  constructor
  · have hl : target-epsilon ≤ onlineMean prior samples value := by
      unfold onlineMean
      apply (le_div_iff₀ hd).mpr
      nlinarith
    linarith
  · have hu : onlineMean prior samples value ≤ target+epsilon := by
      unfold onlineMean
      apply (div_le_iff₀ hd).mpr
      nlinarith
    linarith

def ReceiptPriceError (tariff : Act → ℝ) (epsilon : ℝ) (s : ReceiptMeans Qid) : Prop :=
  ∀ i ∈ s.seen, |s.quotedValue i-tariff (resourceAction (s.resource i))| ≤ epsilon

theorem stationary_receipt_preserves_price_error (tariff caps : Act → ℝ) (epsilon : ℝ)
    (s : ReceiptMeans Qid) (r : PhysicalReceipt Qid) (he : 0 ≤ epsilon)
    (ht : r.actual = tariff (resourceAction r.resource))
    (hc : tariff (resourceAction r.resource) ≤ caps (resourceAction r.resource))
    (hb : ReceiptPriceError tariff epsilon s) :
    ReceiptPriceError tariff epsilon (observeReceipt caps s r) := by
  by_cases hn : r.callId ∈ s.seen
  · simpa [observeReceipt,hn] using hb
  · intro i hi
    simp only [observeReceipt,if_neg hn,Finset.mem_insert] at hi
    rcases hi with rfl | hi
    · simpa [observeReceipt,hn,ht,min_eq_left hc] using he
    · have hne : i ≠ r.callId := by intro heq; subst i; exact hn hi
      simpa [observeReceipt,hn,hne] using hb i hi

theorem stationary_replay_preserves_initial_price_error (tariff caps : Act → ℝ) (epsilon : ℝ)
    (receipts : List (PhysicalReceipt Qid)) (he : 0 ≤ epsilon)
    (ht : ∀ r ∈ receipts, r.actual = tariff (resourceAction r.resource))
    (hc : ∀ a, tariff a ≤ caps a) (initial : ReceiptMeans Qid)
    (hi : ReceiptPriceError tariff epsilon initial) :
    ReceiptPriceError tariff epsilon (replayReceipts caps receipts initial) := by
  induction receipts generalizing initial with
  | nil => exact hi
  | cons r receipts ih =>
      exact ih (fun r hr => ht r (List.mem_cons_of_mem _ hr)) _
        (stationary_receipt_preserves_price_error tariff caps epsilon initial r he
          (ht r (by simp)) (hc _) hi)

theorem live_receipt_price_error (priors caps tariff : Act → ℝ) (epsilon : ℝ)
    (s : ReceiptMeans Qid)
    (hp : ∀ a, |min (caps a) (priors a)-tariff a| ≤ epsilon)
    (hr : ReceiptPriceError tariff epsilon s) (r : Qid × List Act) :
    |liveReceiptPrice priors caps s r-tariff (resourceAction r)| ≤ epsilon := by
  apply online_mean_absolute_error
  · exact hp _
  · intro i hi
    obtain ⟨hseen,ha⟩ := selected_call_pool_valid s r i hi
    simpa only [ha] using hr i hseen

theorem live_receipt_price_exact_stationary (priors caps tariff : Act → ℝ)
    (s : ReceiptMeans Qid) (hp : ∀ a, min (caps a) (priors a) = tariff a)
    (hr : ReceiptPriceError tariff 0 s) (r : Qid × List Act) :
    liveReceiptPrice priors caps s r = tariff (resourceAction r) := by
  have he := live_receipt_price_error priors caps tariff 0 s (by intro a; simp [hp a]) hr r
  exact sub_eq_zero.mp (abs_nonpos_iff.mp he)

def weightedOverlap (qids : Finset Qid) (price : Qid × List Act → ℝ)
    (before : List (TreeEvaluation Act)) (path : List Act) : ℝ :=
  cacheWeight price (ownPanelCache qids before ∩ panelDemand qids path)

theorem own_cache_cold_plus_overlap (qids : Finset Qid) (price : Qid × List Act → ℝ)
    (before : List (TreeEvaluation Act)) (path : List Act) :
    coldWork price (ownPanelCache qids before) (panelDemand qids path) +
      weightedOverlap qids price before path = cacheWeight price (panelDemand qids path) := by
  unfold coldWork weightedOverlap cacheWeight
  have hdis : Disjoint (panelDemand qids path \ ownPanelCache qids before)
      (ownPanelCache qids before ∩ panelDemand qids path) := by
    apply Finset.disjoint_left.mpr
    intro r hr hc
    exact (Finset.mem_sdiff.mp hr).2 (Finset.mem_inter.mp hc).1
  rw [← Finset.sum_union hdis]
  congr 1
  ext r
  simp only [Finset.mem_union,Finset.mem_sdiff,Finset.mem_inter]
  tauto

theorem own_cache_overlap_after_publication (qids : Finset Qid) (price : Qid × List Act → ℝ)
    (before : List (TreeEvaluation Act)) (event : TreeEvaluation Act) :
    weightedOverlap qids price (before++[event]) event.terminal = cacheWeight price (panelDemand qids event.terminal) := by
  have hs : panelDemand qids event.terminal ⊆ ownPanelCache qids (before++[event]) := by
    simp only [ownPanelCache,List.foldl_append,List.foldl_cons,List.foldl_nil]
    exact Finset.subset_union_right
  unfold weightedOverlap
  rw [Finset.inter_eq_right.mpr hs]

end AgentUCTPanelAllocation
