import AgentUCTPaper.TreeRate

/-! # From tree quality regret to training recommendation and own-cache policy costs -/

set_option autoImplicit false

noncomputable section

namespace AgentUCTPaper

open Finset

variable {Action Qid : Type*} [DecidableEq Action] [DecidableEq Qid]

omit [DecidableEq Qid] in
theorem best_training_after_coverage (terminals : Finset (List Action))
    (reward : List Action → ℝ) (c H : ℝ)
    (penalty : List (TreeEvaluation Action) → List Action → Action → ℝ)
    (events : List (TreeEvaluation Action)) (run : BoundedTreeRun terminals c H penalty events)
    (hTable : FixedTableEvents terminals reward events) (hc : 0 < c) (hH : 0 ≤ H)
    (hAntichain : ∀ p ∈ terminals, ∀ q ∈ terminals, p <+: q → p = q)
    (hCount : coverageVisits terminals c H (topologyDepth terminals) ≤ events.length)
    (best : TreeEvaluation Action) (hBest : bestCompleted events = some best) :
    best.reward = subtreeValue terminals reward [] := by
  have hSpec := bestCompleted_spec events best hBest
  have hBestTable := hTable best hSpec.1
  have hNonempty : (subtreeTerminals terminals []).Nonempty :=
    ⟨best.terminal, mem_filter.mpr ⟨hBestTable.1, List.nil_prefix⟩⟩
  obtain ⟨leaf, hl, _, hValue⟩ := subtreeValue_attained terminals reward [] hNonempty
  obtain ⟨event, he, hTerminal⟩ := visited_terminal_observed terminals events run.terminal hAntichain
    leaf hl (actual_terminal_coverage terminals c H penalty events run hc hH hAntichain hCount leaf hl)
  have hLower := hSpec.2 event he
  rw [(hTable event he).2, hTerminal, ← hValue] at hLower
  have hUpper := subtreeValue_upper terminals reward [] best.terminal hBestTable.1 List.nil_prefix
  rw [← hBestTable.2] at hUpper
  exact le_antisymm hUpper hLower

def meteredSearchCost (qids : Finset Qid) (root : List Action)
    (weight : Qid × List Action → ℝ) (overhead : TreeEvaluation Action → ℝ)
    (events : List (TreeEvaluation Action)) (initial : MeteredTreeState Qid Action) : ℝ :=
  (replayMetered qids (fun p ↦ root ++ p) weight overhead events initial).totalPaid - initial.totalPaid

theorem meteredSearchCost_nonnegative (qids : Finset Qid) (root : List Action)
    (weight : Qid × List Action → ℝ) (hWeight : ∀ r, 0 ≤ weight r)
    (overhead : TreeEvaluation Action → ℝ) (events : List (TreeEvaluation Action))
    (hOverhead : ∀ e ∈ events, 0 ≤ overhead e) (initial : MeteredTreeState Qid Action) :
    0 ≤ meteredSearchCost qids root weight overhead events initial := by
  unfold meteredSearchCost
  rw [replayMetered_total]
  apply add_nonneg
  · exact sub_nonneg.mpr (cacheWeight_mono weight hWeight
      (replayMetered_initial_cache_subset qids (fun p ↦ root ++ p) weight overhead events initial))
  · exact List.sum_nonneg (by
      intro x hx
      obtain ⟨e, he, rfl⟩ := List.mem_map.mp hx
      exact hOverhead e he)

theorem meteredSearchCost_upper (qids : Finset Qid) (root : List Action)
    (terminals : Finset (List Action)) (weight : Qid × List Action → ℝ)
    (hWeight : ∀ r, 0 ≤ weight r) (overhead : TreeEvaluation Action → ℝ)
    (events : List (TreeEvaluation Action)) (initial : MeteredTreeState Qid Action)
    (hInitial : initial.materialized ⊆ workflowResources qids root terminals)
    (hTerminal : ∀ e ∈ events, e.terminal ∈ terminals) :
    meteredSearchCost qids root weight overhead events initial ≤
      cacheWeight weight (workflowResources qids root terminals) -
        cacheWeight weight initial.materialized + (events.map overhead).sum := by
  unfold meteredSearchCost
  rw [replayMetered_total]
  apply add_le_add_right
  apply sub_le_sub_right
  exact cacheWeight_mono weight hWeight
    (replayMetered_cache_subset qids (fun p ↦ root ++ p) weight overhead events initial
      (workflowResources qids root terminals) hInitial
      (fun e he ↦ terminal_demand_subset_resources qids root terminals e.terminal (hTerminal e he)))

def cumulativePolicyNetRegret (lambda : ℝ) (actual comparator : List (TreeEvaluation Action))
    (actualCost comparatorCost : ℝ) : ℝ :=
  (comparator.map TreeEvaluation.reward).sum - (actual.map TreeEvaluation.reward).sum +
    lambda * (actualCost - comparatorCost)

omit [DecidableEq Qid] in
theorem policy_net_regret_from_quality (value lambda actualCost comparatorCost budget : ℝ)
    (actual comparator : List (TreeEvaluation Action)) (hLambda : 0 ≤ lambda)
    (hLength : actual.length = comparator.length)
    (hComparator : ∀ e ∈ comparator, e.reward ≤ value)
    (hCost : actualCost - comparatorCost ≤ budget) :
    cumulativePolicyNetRegret lambda actual comparator actualCost comparatorCost ≤
      backedDeficit value actual [] + lambda * budget := by
  have hSum := sum_returns_le_best value comparator hComparator
  have hWeighted := mul_le_mul_of_nonneg_left hCost hLambda
  rw [backedDeficit_identity, root_count_eq_length]
  have hReturn : backedReturn actual [] = (actual.map TreeEvaluation.reward).sum := by
    simp [backedReturn]
  rw [hReturn, hLength]
  unfold cumulativePolicyNetRegret
  linarith

/-- The two trajectories pay against their own caches; comparator cost is not evaluated in K_t. -/
theorem own_cache_policy_regret_bound (qids : Finset Qid) (root : List Action)
    (terminals : Finset (List Action)) (reward : List Action → ℝ) (lambda : ℝ)
    (weight : Qid × List Action → ℝ) (hWeight : ∀ r, 0 ≤ weight r)
    (actualOverhead comparatorOverhead : TreeEvaluation Action → ℝ)
    (actual comparator : List (TreeEvaluation Action))
    (actualInitial comparatorInitial : MeteredTreeState Qid Action)
    (hLambda : 0 ≤ lambda) (hLength : actual.length = comparator.length)
    (hActual : ∀ e ∈ actual, e.terminal ∈ terminals)
    (hComparator : FixedTableEvents terminals reward comparator)
    (hInitial : actualInitial.materialized ⊆ workflowResources qids root terminals)
    (hComparatorOverhead : ∀ e ∈ comparator, 0 ≤ comparatorOverhead e) :
    cumulativePolicyNetRegret lambda actual comparator
      (meteredSearchCost qids root weight actualOverhead actual actualInitial)
      (meteredSearchCost qids root weight comparatorOverhead comparator comparatorInitial) ≤
    backedDeficit (subtreeValue terminals reward []) actual [] + lambda *
      (cacheWeight weight (workflowResources qids root terminals) -
        cacheWeight weight actualInitial.materialized + (actual.map actualOverhead).sum) := by
  apply policy_net_regret_from_quality _ _ _ _ _ actual comparator hLambda hLength
  · intro e he
    rw [(hComparator e he).2]
    exact subtreeValue_upper terminals reward [] e.terminal (hComparator e he).1 List.nil_prefix
  · have hUpper := meteredSearchCost_upper qids root terminals weight hWeight actualOverhead
      actual actualInitial hInitial hActual
    have hLower := meteredSearchCost_nonnegative qids root weight hWeight comparatorOverhead
      comparator hComparatorOverhead comparatorInitial
    linarith

theorem own_cache_cost_difference_common_overhead (qids : Finset Qid) (root : List Action)
    (terminals : Finset (List Action)) (weight : Qid × List Action → ℝ)
    (hWeight : ∀ r, 0 ≤ weight r) (actualOverhead comparatorOverhead : TreeEvaluation Action → ℝ)
    (actual comparator : List (TreeEvaluation Action))
    (actualInitial comparatorInitial : MeteredTreeState Qid Action)
    (hActual : ∀ e ∈ actual, e.terminal ∈ terminals)
    (hInitial : actualInitial.materialized ⊆ workflowResources qids root terminals)
    (hSameOverhead : (actual.map actualOverhead).sum = (comparator.map comparatorOverhead).sum) :
    meteredSearchCost qids root weight actualOverhead actual actualInitial -
      meteredSearchCost qids root weight comparatorOverhead comparator comparatorInitial ≤
    cacheWeight weight (workflowResources qids root terminals) -
      cacheWeight weight actualInitial.materialized := by
  have hUpper := meteredSearchCost_upper qids root terminals weight hWeight actualOverhead
    actual actualInitial hInitial hActual
  have hLower := cacheWeight_mono weight hWeight (replayMetered_initial_cache_subset qids
    (fun p ↦ root ++ p) weight comparatorOverhead comparator comparatorInitial)
  unfold meteredSearchCost at hUpper ⊢
  rw [replayMetered_total] at hUpper ⊢
  rw [replayMetered_total, hSameOverhead]
  linarith

end AgentUCTPaper
