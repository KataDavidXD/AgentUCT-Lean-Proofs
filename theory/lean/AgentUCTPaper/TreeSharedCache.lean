import AgentUCTPaper.TreeEstimatorDynamics

/-! # Fixed reward panels sharing qid-prefix materializations

Each panel owns its tree and raw-reward statistics. Other panels may publish
additional restorable resources between its visits. Their observations are not
backed up into this panel. Thus its reward table remains fixed, while its bill
depends on the full bipartite cache. The theorem allows arbitrary extra cache
contents: own successful publications are always retained.
-/

set_option autoImplicit false
noncomputable section

namespace AgentUCTPaper

variable {Qid Action : Type*} [DecidableEq Qid] [DecidableEq Action]

/-- A panel's own publication history plus materializations from other panels. -/
def sharedColdPenalty (qids : Finset Qid) (root : List Action)
    (terminals : Finset (List Action)) (prediction : Qid × List Action → ℝ) (gamma : ℝ)
    (law : List (TreeEvaluation Action) → List Action → Action → List Action → ℝ)
    (initial : PersistentCaches Qid Action)
    (extra : List (TreeEvaluation Action) → Finset (Qid × List Action))
    (before : List (TreeEvaluation Action)) (p : List Action) (a : Action) : ℝ :=
  gamma * referenceColdCost qids root terminals prediction (law before p a)
    ((replayPublished qids (fun x ↦ root ++ x) before initial).restorable ∪ extra before)
    (p ++ [a])

/-- Sharing saved prefixes preserves the whole-tree logarithmic quality bound.
The extra cache may depend on the entire external schedule, encoded along the
local history. Rewards and tree statistics still belong to this fixed panel. -/
theorem shared_cache_uniform_root_log_bound (qids : Finset Qid) (root : List Action)
    (terminals : Finset (List Action)) (hTerminals : terminals.Nonempty)
    (reward : List Action → ℝ)
    (hReward : ∀ leaf ∈ terminals, 0 ≤ reward leaf ∧ reward leaf ≤ 1)
    (hAntichain : ∀ p ∈ terminals, ∀ q ∈ terminals, p <+: q → p = q)
    (prediction : Qid × List Action → ℝ) (hPrediction : ∀ r, 0 ≤ prediction r)
    (gamma c : ℝ) (hGamma : 0 ≤ gamma) (hc : 0 < c)
    (law : List (TreeEvaluation Action) → List Action → Action → List Action → ℝ)
    (hLaw : ∀ before p a, a ∈ availableChildren terminals p →
      ∀ leaf ∈ subtreeTerminals terminals (p ++ [a]), 0 ≤ law before p a leaf)
    (hMass : ∀ before p a, a ∈ availableChildren terminals p →
      ∑ leaf ∈ subtreeTerminals terminals (p ++ [a]), law before p a leaf = 1)
    (initial : PersistentCaches Qid Action)
    (hInitial : initial.restorable = initial.everMaterialized)
    (extra : List (TreeEvaluation Action) → Finset (Qid × List Action)) :
    ∃ delta : ℝ, 0 < delta ∧ ∀ events : List (TreeEvaluation Action),
      FixedTableEvents terminals reward events →
      LegalTreeRun (fun p ↦ p ∈ terminals) {[]} events →
      TreeAllocationRule terminals c
        (sharedColdPenalty qids root terminals prediction gamma law initial extra) events →
      let H := gamma * cacheWeight prediction (workflowResources qids root terminals)
      let cacheTime := coverageVisits terminals c H (topologyDepth terminals)
      let constants := treeRateConstants terminals c H delta cacheTime
        (topologyDepth terminals)
      backedDeficit (subtreeValue terminals reward []) events [] ≤
        constants.1 * Real.log (events.length + 1 : ℕ) + constants.2 := by
  obtain ⟨delta, hDelta, hGaps⟩ := finite_tree_positive_edge_gap terminals reward
  refine ⟨delta, hDelta, ?_⟩
  intro events hTable hLegal hRule
  let H := gamma * cacheWeight prediction (workflowResources qids root terminals)
  let penalty := sharedColdPenalty qids root terminals prediction gamma law initial extra
  let cacheTime := coverageVisits terminals c H (topologyDepth terminals)
  have hH : 0 ≤ H := mul_nonneg hGamma (Finset.sum_nonneg (fun r _ ↦ hPrediction r))
  have run : BoundedTreeRun terminals c H penalty events := {
    terminal := fun event he ↦ (hTable event he).1
    reward := by
      intro event he
      rw [(hTable event he).2]
      exact hReward event.terminal (hTable event he).1
    legal := hLegal
    rule := hRule
    penalty_bounded := by
      intro before _ p a ha
      obtain ⟨h0, h1⟩ := referenceColdCost_bounded qids root terminals prediction hPrediction
        (law before p a) _ (p ++ [a]) (hLaw before p a ha) (hMass before p a ha)
      exact ⟨mul_nonneg hGamma h0, mul_le_mul_of_nonneg_left h1 hGamma⟩ }
  have hZero : ∀ before, before <+: events → cacheTime ≤ before.length →
      ∀ p ∈ workflowNodes terminals, ∀ a ∈ availableChildren terminals p,
        penalty before p a = 0 := by
    intro before hp ht p _ a _
    have hCovered := actual_restorable_coverage qids root terminals c H penalty
      (fun _ ↦ 0) (fun _ ↦ 0) before
      ⟨emptyStatistics, initial.everMaterialized, 0, 0⟩ initial hInitial rfl
      (run.prefix hp) hc hH hAntichain ht
    change gamma * referenceColdCost qids root terminals prediction _ _ _ = 0
    rw [referenceColdCost_zero qids root terminals prediction _ _ _
      (hCovered.trans Finset.subset_union_left), mul_zero]
  obtain ⟨leaf, hl⟩ := hTerminals
  have hRoot : [] ∈ workflowNodes terminals :=
    (workflowNodes_mem terminals []).mpr ⟨leaf, hl, List.nil_prefix⟩
  have hResult := actual_subtree_log_deficit terminals reward c H delta cacheTime
    penalty hReward hc hH hDelta hAntichain hGaps (topologyDepth terminals) events run
    hTable hZero [] hRoot (by simp)
  simpa only [root_count_eq_length] using hResult

/-- A fixed finite family of panel bounds gives a logarithmic scheduled bound. -/
theorem fixed_panel_family_log_bound {Context : Type*} (contexts : Finset Context)
    (regret A B : Context → ℝ) (visits : Context → ℕ) (T : ℕ)
    (hA : ∀ j ∈ contexts, 0 ≤ A j)
    (hVisits : ∀ j ∈ contexts, visits j ≤ T)
    (hBound : ∀ j ∈ contexts,
      regret j ≤ A j * Real.log (visits j + 1 : ℕ) + B j) :
    (∑ j ∈ contexts, regret j) ≤
      (∑ j ∈ contexts, A j) * Real.log (T + 1 : ℕ) + ∑ j ∈ contexts, B j := by
  rw [Finset.sum_mul, ← Finset.sum_add_distrib]
  apply Finset.sum_le_sum
  intro j hj
  have hLog : Real.log (visits j + 1 : ℕ) ≤ Real.log (T + 1 : ℕ) :=
    Real.log_le_log (by positivity) (by exact_mod_cast Nat.add_le_add_right (hVisits j hj) 1)
  exact (hBound j hj).trans (add_le_add_right (mul_le_mul_of_nonneg_left hLog (hA j hj)) _)

end AgentUCTPaper

namespace AgentUCTPaper

variable {Qid Action : Type*} [DecidableEq Qid] [DecidableEq Action]

/-- Nonnegative cold-cost truncations inherit the shared-panel quality rate.
This covers a first-unpaid estimate once its pointwise domination by the
complete forecast is established. Equality with ordinary UCT is not assumed. -/
theorem dominated_cold_shared_root_log_bound (qids : Finset Qid) (root : List Action)
    (terminals : Finset (List Action)) (hTerminals : terminals.Nonempty)
    (reward : List Action → ℝ)
    (hReward : ∀ leaf ∈ terminals, 0 ≤ reward leaf ∧ reward leaf ≤ 1)
    (hAntichain : ∀ p ∈ terminals, ∀ q ∈ terminals, p <+: q → p = q)
    (prediction : Qid × List Action → ℝ) (hPrediction : ∀ r, 0 ≤ prediction r)
    (gamma c : ℝ) (hGamma : 0 ≤ gamma) (hc : 0 < c)
    (law : List (TreeEvaluation Action) → List Action → Action → List Action → ℝ)
    (hLaw : ∀ before p a, a ∈ availableChildren terminals p →
      ∀ leaf ∈ subtreeTerminals terminals (p ++ [a]), 0 ≤ law before p a leaf)
    (hMass : ∀ before p a, a ∈ availableChildren terminals p →
      ∑ leaf ∈ subtreeTerminals terminals (p ++ [a]), law before p a leaf = 1)
    (initial : PersistentCaches Qid Action)
    (hInitial : initial.restorable = initial.everMaterialized)
    (extra : List (TreeEvaluation Action) → Finset (Qid × List Action))
    (penalty : List (TreeEvaluation Action) → List Action → Action → ℝ)
    (hNonneg : ∀ before p a, a ∈ availableChildren terminals p → 0 ≤ penalty before p a)
    (hDominated : ∀ before p a, a ∈ availableChildren terminals p →
      penalty before p a ≤ sharedColdPenalty qids root terminals prediction gamma law initial extra before p a) :
    ∃ delta : ℝ, 0 < delta ∧ ∀ events : List (TreeEvaluation Action),
      FixedTableEvents terminals reward events →
      LegalTreeRun (fun p ↦ p ∈ terminals) {[]} events →
      TreeAllocationRule terminals c penalty events →
      let H := gamma * cacheWeight prediction (workflowResources qids root terminals)
      let cacheTime := coverageVisits terminals c H (topologyDepth terminals)
      let constants := treeRateConstants terminals c H delta cacheTime (topologyDepth terminals)
      backedDeficit (subtreeValue terminals reward []) events [] ≤
        constants.1 * Real.log (events.length + 1 : ℕ) + constants.2 := by
  -- Q8支配版1：delta先于任意历史固定；实际罚项由统一非负完成冷账支配。
  obtain ⟨delta, hDelta, hGaps⟩ := finite_tree_positive_edge_gap terminals reward
  refine ⟨delta, hDelta, ?_⟩
  intro events hTable hLegal hRule
  let H := gamma * cacheWeight prediction (workflowResources qids root terminals)
  let cacheTime := coverageVisits terminals c H (topologyDepth terminals)
  have hH : 0 ≤ H := mul_nonneg hGamma (Finset.sum_nonneg (fun r _ ↦ hPrediction r))
  have run : BoundedTreeRun terminals c H penalty events := {
    terminal := fun event he ↦ (hTable event he).1
    reward := by
      intro event he
      rw [(hTable event he).2]
      exact hReward event.terminal (hTable event he).1
    legal := hLegal
    rule := hRule
    penalty_bounded := by
      intro before _ p a ha
      obtain ⟨_, h1⟩ := referenceColdCost_bounded qids root terminals prediction hPrediction
        (law before p a) _ (p ++ [a]) (hLaw before p a ha) (hMass before p a ha)
      exact ⟨hNonneg before p a ha,
        (hDominated before p a ha).trans (mul_le_mul_of_nonneg_left h1 hGamma)⟩ }
  have hZero : ∀ before, before <+: events → cacheTime ≤ before.length →
      ∀ p ∈ workflowNodes terminals, ∀ a ∈ availableChildren terminals p,
        penalty before p a = 0 := by
    intro before hp ht p _ a ha
    have hCovered := actual_restorable_coverage qids root terminals c H penalty
      (fun _ ↦ 0) (fun _ ↦ 0) before
      ⟨emptyStatistics, initial.everMaterialized, 0, 0⟩ initial hInitial rfl
      (run.prefix hp) hc hH hAntichain ht
    have hFull : sharedColdPenalty qids root terminals prediction gamma law initial extra before p a = 0 := by
      -- Q4支配版2：本树成功持久发布已覆盖全部资源，额外共享并集保留覆盖。
      change gamma * referenceColdCost qids root terminals prediction _ _ _ = 0
      rw [referenceColdCost_zero qids root terminals prediction _ _ _
        (hCovered.trans Finset.subset_union_left), mul_zero]
    exact le_antisymm ((hDominated before p a ha).trans_eq hFull) (hNonneg before p a ha)
    -- 0≤实际罚项≤完整冷罚项=0，由反对称性给严格归零，再接Q7深度归纳。
  obtain ⟨leaf, hl⟩ := hTerminals
  have hRoot : [] ∈ workflowNodes terminals :=
    (workflowNodes_mem terminals []).mpr ⟨leaf, hl, List.nil_prefix⟩
  have hResult := actual_subtree_log_deficit terminals reward c H delta cacheTime
    penalty hReward hc hH hDelta hAntichain hGaps (topologyDepth terminals) events run
    hTable hZero [] hRoot (by simp)
  simpa only [root_count_eq_length] using hResult

end AgentUCTPaper
