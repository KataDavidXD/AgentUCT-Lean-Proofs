import AgentUCTPaper.TreeCostEstimation
import AgentUCTPaper.TreeObjectives
import AgentUCTPaper.TreeReduced

/-! # Cache accumulation, prediction savings, and next-edge net regret

Physical publication and counterfactual cost forecasts are separate operations.
Savings compare a fixed demand law and fixed weights before and after publication.
The net-regret corollary compares policies running against their own caches.
-/

set_option autoImplicit false

noncomputable section

namespace AgentUCTPaper

open Finset

variable {Resource : Type*} [DecidableEq Resource]

/-- More saved resources reduce a fixed bill; no estimator is involved. -/
theorem coldWork_cache_antitone (weight : Resource → ℝ) (hWeight : ∀ r, 0 ≤ weight r)
    (cached larger demand : Finset Resource) (hCache : cached ⊆ larger) :
    coldWork weight larger demand ≤ coldWork weight cached demand := by
  exact sum_le_sum_of_subset_of_nonneg (sdiff_subset_sdiff subset_rfl hCache)
    (fun r _ _ ↦ hWeight r)

/-- A bill computed at the initial snapshot already accounts for sequential cache growth. -/
theorem coldWork_sequential_union (weight : Resource → ℝ)
    (cached first later : Finset Resource) :
    coldWork weight cached (first ∪ later) =
      coldWork weight cached first + coldWork weight (cached ∪ first) later := by
  have h := cache_union_accounting weight cached (first ∪ later)
  rw [← union_assoc, cache_union_accounting, cache_union_accounting] at h
  linarith

/-- Exactly the newly published resources shared with the later demand become free. -/
theorem coldWork_publication_savings (weight : Resource → ℝ)
    (cached published demand : Finset Resource) :
    coldWork weight cached demand - coldWork weight (cached ∪ published) demand =
      coldWork weight cached (demand ∩ published) := by
  have hSplit : demand \ cached =
      (demand \ (cached ∪ published)) ∪ ((demand ∩ published) \ cached) := by
    ext r
    simp only [mem_sdiff, mem_union, mem_inter]
    tauto
  have hDisjoint : Disjoint (demand \ (cached ∪ published))
      ((demand ∩ published) \ cached) := by
    apply disjoint_left.mpr
    intro r ha hb
    exact (mem_sdiff.mp ha).2 (mem_union_right cached (mem_inter.mp (mem_sdiff.mp hb).1).2)
  unfold coldWork
  rw [hSplit, sum_union hDisjoint]
  ring

variable {Qid Action : Type*} [DecidableEq Qid] [DecidableEq Action]

/-- A rollout-only prefix is published even though it receives no tree-statistics update. -/
theorem rollout_publication_without_backup (qids : Finset Qid)
    (weight : Qid × List Action → ℝ) (overhead : TreeEvaluation Action → ℝ)
    (state : MeteredTreeState Qid Action) (event : TreeEvaluation Action)
    (qid : Qid) (p : List Action) (hQid : qid ∈ qids)
    (hPrefix : p ∈ executionPrefixes event.terminal) (hOffTree : ¬ p <+: event.expanded) :
    (qid, p) ∈ (meterStep qids id weight overhead state event).materialized ∧
      (meterStep qids id weight overhead state event).stats p = state.stats p := by
  constructor
  · exact mem_union_right _ ((panelDemand_mem qids event.terminal p qid).mpr ⟨hQid, hPrefix⟩)
  · rw [meterStep_stats]
    exact backupEvent_off_path state.stats event p hOffTree

/-- Frozen-law prediction change isolates the effect of newly published cache objects. -/
theorem referenceColdCost_publication_savings (qids : Finset Qid) (root : List Action)
    (terminals : Finset (List Action)) (prediction : Qid × List Action → ℝ)
    (law : List Action → ℝ) (cached published : Finset (Qid × List Action)) (p : List Action) :
    referenceColdCost qids root terminals prediction law cached p -
      referenceColdCost qids root terminals prediction law (cached ∪ published) p =
    ∑ leaf ∈ subtreeTerminals terminals p, law leaf *
      coldWork prediction cached (panelDemand qids (root ++ leaf) ∩ published) := by
  unfold referenceColdCost
  rw [← sum_sub_distrib]
  apply sum_congr rfl
  intro leaf _
  rw [← mul_sub, coldWork_publication_savings]

/-- Monotonicity holds with the continuation law and predictor held fixed. -/
theorem referenceColdCost_cache_antitone (qids : Finset Qid) (root : List Action)
    (terminals : Finset (List Action)) (prediction : Qid × List Action → ℝ)
    (hPrediction : ∀ r, 0 ≤ prediction r) (law : List Action → ℝ)
    (cached larger : Finset (Qid × List Action)) (p : List Action)
    (hLaw : ∀ leaf ∈ subtreeTerminals terminals p, 0 ≤ law leaf)
    (hCache : cached ⊆ larger) :
    referenceColdCost qids root terminals prediction law larger p ≤
      referenceColdCost qids root terminals prediction law cached p := by
  apply sum_le_sum
  intro leaf hl
  exact mul_le_mul_of_nonneg_left
    (coldWork_cache_antitone prediction hPrediction cached larger _ hCache) (hLaw leaf hl)

/-- A local same-state comparison accumulates omitted-tail variation explicitly.
An own-cache policy comparison needs the separate accounting theorem below. -/
theorem next_edge_tail_regret_transfer {Arm : Type*}
    (reward edge tail : ℕ → Arm → ℝ) (chosen comparator : ℕ → Arm)
    (eta : ℝ) (hEta : 0 ≤ eta) (variation : ℕ → ℝ) (T : ℕ)
    (hVariation : ∀ t ∈ range T, tail t (chosen t) - tail t (comparator t) ≤ variation t) :
    (∑ t ∈ range T,
      (AgentUCT.net (reward t (comparator t))
          (edge t (comparator t) + tail t (comparator t)) eta -
        AgentUCT.net (reward t (chosen t)) (edge t (chosen t) + tail t (chosen t)) eta)) ≤
    (∑ t ∈ range T,
      (AgentUCT.net (reward t (comparator t)) (edge t (comparator t)) eta -
        AgentUCT.net (reward t (chosen t)) (edge t (chosen t)) eta)) +
      eta * ∑ t ∈ range T, variation t := by
  rw [mul_sum, ← sum_add_distrib]
  apply sum_le_sum
  intro t ht
  have h := mul_le_mul_of_nonneg_left (hVariation t ht) hEta
  unfold AgentUCT.net
  nlinarith

/-- Next-edge has logarithmic own-cache net regret for cold work or equal total overhead.
This is an upper bound, not an improvement over UCT or an endpoint-utility guarantee. -/
theorem next_edge_own_cache_log_bound (qids : Finset Qid) (root : List Action)
    (terminals : Finset (List Action)) (hTerminals : terminals.Nonempty)
    (reward : List Action → ℝ)
    (hReward : ∀ leaf ∈ terminals, 0 ≤ reward leaf ∧ reward leaf ≤ 1)
    (hAntichain : ∀ p ∈ terminals, ∀ q ∈ terminals, p <+: q → p = q)
    (prediction : Qid × List Action → ℝ) (hPrediction : ∀ r, 0 ≤ prediction r)
    (weight : Qid × List Action → ℝ) (hWeight : ∀ r, 0 ≤ weight r)
    (gamma c eta : ℝ) (hc : 0 < c) (hEta : 0 ≤ eta)
    (initial : PersistentCaches Qid Action)
    (hInitial : initial.restorable = initial.everMaterialized)
    (hResources : initial.everMaterialized ⊆ workflowResources qids root terminals) :
    ∃ delta : ℝ, 0 < delta ∧ ∀ actual comparator : List (TreeEvaluation Action),
      FixedTableEvents terminals reward actual →
      LegalTreeRun (fun p ↦ p ∈ terminals) {[]} actual →
      TreeAllocationRule terminals c (nextEdgePenalty qids root prediction gamma initial) actual →
      FixedTableEvents terminals reward comparator → actual.length = comparator.length →
      ∀ (actualOverhead comparatorOverhead : TreeEvaluation Action → ℝ)
        (comparatorInitial : MeteredTreeState Qid Action),
      (actual.map actualOverhead).sum = (comparator.map comparatorOverhead).sum →
      let constants := treeRateConstants terminals c 0 delta 0 (topologyDepth terminals)
      cumulativePolicyNetRegret eta actual comparator
        (meteredSearchCost qids root weight actualOverhead actual
          ⟨emptyStatistics, initial.everMaterialized, 0, 0⟩)
        (meteredSearchCost qids root weight comparatorOverhead comparator comparatorInitial) ≤
      constants.1 * Real.log (actual.length + 1 : ℕ) + constants.2 +
        eta * (cacheWeight weight (workflowResources qids root terminals) -
          cacheWeight weight initial.everMaterialized) := by
  obtain ⟨delta, hd, hQuality⟩ := next_edge_uniform_root_log_bound qids root terminals hTerminals
    reward hReward hAntichain prediction hPrediction gamma c hc initial hInitial
  refine ⟨delta, hd, ?_⟩
  intro actual comparator hActual hLegal hRule hComparator hLength actualOverhead
    comparatorOverhead comparatorInitial hSame
  have hCost := own_cache_cost_difference_common_overhead qids root terminals weight hWeight
    actualOverhead comparatorOverhead actual comparator
    ⟨emptyStatistics, initial.everMaterialized, 0, 0⟩ comparatorInitial
    (fun e he ↦ (hActual e he).1) hResources hSame
  have hNet := policy_net_regret_from_quality (subtreeValue terminals reward []) eta _ _ _
    actual comparator hEta hLength (by
      intro e he
      rw [(hComparator e he).2]
      exact subtreeValue_upper terminals reward [] e.terminal (hComparator e he).1 List.nil_prefix)
    hCost
  exact hNet.trans (add_le_add_right (hQuality actual hActual hLegal hRule) _)

end AgentUCTPaper
