import AgentUCTPaper.TreeCoverage

/-! # Reference completion costs attached to the actual persistent cache -/

set_option autoImplicit false

noncomputable section

namespace AgentUCTPaper

open Finset

variable {Qid Action : Type*} [DecidableEq Qid] [DecidableEq Action]

def referenceColdCost (qids : Finset Qid) (root : List Action)
    (terminals : Finset (List Action)) (prediction : Qid × List Action → ℝ)
    (law : List Action → ℝ) (cached : Finset (Qid × List Action)) (p : List Action) : ℝ :=
  ∑ leaf ∈ subtreeTerminals terminals p,
    law leaf * coldWork prediction cached (panelDemand qids (root ++ leaf))

theorem terminal_demand_subset_resources (qids : Finset Qid) (root : List Action)
    (terminals : Finset (List Action)) (leaf : List Action) (hl : leaf ∈ terminals) :
    panelDemand qids (root ++ leaf) ⊆ workflowResources qids root terminals := by
  intro r hr
  exact mem_biUnion.mpr ⟨leaf, hl, hr⟩

theorem referenceColdCost_bounded (qids : Finset Qid) (root : List Action)
    (terminals : Finset (List Action)) (prediction : Qid × List Action → ℝ)
    (hPrediction : ∀ r, 0 ≤ prediction r) (law : List Action → ℝ)
    (cached : Finset (Qid × List Action)) (p : List Action)
    (hLaw : ∀ leaf ∈ subtreeTerminals terminals p, 0 ≤ law leaf)
    (hMass : ∑ leaf ∈ subtreeTerminals terminals p, law leaf = 1) :
    0 ≤ referenceColdCost qids root terminals prediction law cached p ∧
      referenceColdCost qids root terminals prediction law cached p ≤
        cacheWeight prediction (workflowResources qids root terminals) := by
  constructor
  · exact sum_nonneg (fun leaf hl ↦ mul_nonneg (hLaw leaf hl)
      (coldWork_nonnegative prediction hPrediction _ _))
  · unfold referenceColdCost
    calc
      _ ≤ ∑ leaf ∈ subtreeTerminals terminals p,
          law leaf * cacheWeight prediction (workflowResources qids root terminals) := by
        apply sum_le_sum
        intro leaf hl
        apply mul_le_mul_of_nonneg_left _ (hLaw leaf hl)
        exact (coldWork_le_fullWork prediction hPrediction _ _).trans
          (cacheWeight_mono prediction hPrediction
            (terminal_demand_subset_resources qids root terminals leaf (mem_filter.mp hl).1))
      _ = _ := by rw [← sum_mul, hMass, one_mul]

theorem referenceColdCost_zero (qids : Finset Qid) (root : List Action)
    (terminals : Finset (List Action)) (prediction : Qid × List Action → ℝ)
    (law : List Action → ℝ) (cached : Finset (Qid × List Action)) (p : List Action)
    (hCache : workflowResources qids root terminals ⊆ cached) :
    referenceColdCost qids root terminals prediction law cached p = 0 := by
  apply sum_eq_zero
  intro leaf hl
  rw [cached_demand_is_free prediction cached _
    ((terminal_demand_subset_resources qids root terminals leaf (mem_filter.mp hl).1).trans hCache)]
  exact mul_zero _

def coldForecastPenalty (qids : Finset Qid) (root : List Action)
    (terminals : Finset (List Action)) (prediction : Qid × List Action → ℝ) (gamma : ℝ)
    (law : List (TreeEvaluation Action) → List Action → Action → List Action → ℝ)
    (initial : PersistentCaches Qid Action) (before : List (TreeEvaluation Action))
    (p : List Action) (a : Action) : ℝ :=
  gamma * referenceColdCost qids root terminals prediction (law before p a)
    (replayPublished qids (fun x ↦ root ++ x) before initial).restorable (p ++ [a])

theorem coldForecastPenalty_bounded (qids : Finset Qid) (root : List Action)
    (terminals : Finset (List Action)) (prediction : Qid × List Action → ℝ)
    (hPrediction : ∀ r, 0 ≤ prediction r) (gamma : ℝ) (hGamma : 0 ≤ gamma)
    (law : List (TreeEvaluation Action) → List Action → Action → List Action → ℝ)
    (initial : PersistentCaches Qid Action) (before : List (TreeEvaluation Action))
    (p : List Action) (a : Action)
    (hLaw : ∀ leaf ∈ subtreeTerminals terminals (p ++ [a]), 0 ≤ law before p a leaf)
    (hMass : ∑ leaf ∈ subtreeTerminals terminals (p ++ [a]), law before p a leaf = 1) :
    0 ≤ coldForecastPenalty qids root terminals prediction gamma law initial before p a ∧
      coldForecastPenalty qids root terminals prediction gamma law initial before p a ≤
        gamma * cacheWeight prediction (workflowResources qids root terminals) := by
  obtain ⟨h0, h1⟩ := referenceColdCost_bounded qids root terminals prediction hPrediction
    (law before p a) _ (p ++ [a]) hLaw hMass
  exact ⟨mul_nonneg hGamma h0, mul_le_mul_of_nonneg_left h1 hGamma⟩

/-- Zero follows from proved operational coverage, independently of forecast calibration. -/
theorem coldForecastPenalty_after_coverage (qids : Finset Qid) (root : List Action)
    (terminals : Finset (List Action)) (prediction : Qid × List Action → ℝ) (gamma c H : ℝ)
    (law : List (TreeEvaluation Action) → List Action → Action → List Action → ℝ)
    (initial : PersistentCaches Qid Action)
    (hCache : initial.restorable = initial.everMaterialized)
    (events : List (TreeEvaluation Action))
    (run : BoundedTreeRun terminals c H
      (coldForecastPenalty qids root terminals prediction gamma law initial) events)
    (hc : 0 < c) (hH : 0 ≤ H)
    (hAntichain : ∀ p ∈ terminals, ∀ q ∈ terminals, p <+: q → p = q)
    (hCount : coverageVisits terminals c H (topologyDepth terminals) ≤ events.length)
    (p : List Action) (a : Action) :
    coldForecastPenalty qids root terminals prediction gamma law initial events p a = 0 := by
  -- Q4.2：先证明所有终局需求已可恢复；每个合法完成missing集合为空。
  have hCovered := actual_restorable_coverage qids root terminals c H
    (coldForecastPenalty qids root terminals prediction gamma law initial)
    (fun _ ↦ 0) (fun _ ↦ 0) events
    ⟨emptyStatistics, initial.everMaterialized, 0, 0⟩ initial hCache rfl run hc hH hAntichain hCount
  unfold coldForecastPenalty
  -- Q4.3：空有限和为0，任意gamma乘0仍为0；无需预测准确性假设。
  rw [referenceColdCost_zero qids root terminals prediction _ _ _ hCovered, mul_zero]

end AgentUCTPaper
