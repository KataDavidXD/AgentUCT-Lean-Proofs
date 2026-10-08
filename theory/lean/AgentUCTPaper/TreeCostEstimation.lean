import AgentUCTPaper.TreeForecast
import AgentUCTPaper.CostModel
import AgentUCTPaper.Greedy

/-! # Executable reference costs, legacy reduction, and explicit error components -/

set_option autoImplicit false

noncomputable section

namespace AgentUCTPaper

open Finset

variable {Qid Action : Type*} [DecidableEq Qid] [DecidableEq Action]

def uniformTerminalLaw (terminals : Finset (List Action)) (p : List Action) (_leaf : List Action) :
    ℝ := 1 / (subtreeTerminals terminals p).card

omit [DecidableEq Qid] in
theorem uniformTerminalLaw_probability (terminals : Finset (List Action)) (p : List Action)
    (hNonempty : (subtreeTerminals terminals p).Nonempty) :
    (∀ leaf, 0 ≤ uniformTerminalLaw terminals p leaf) ∧
      (∑ leaf ∈ subtreeTerminals terminals p, uniformTerminalLaw terminals p leaf) = 1 := by
  have hCard : ((subtreeTerminals terminals p).card : ℝ) ≠ 0 := by
    exact_mod_cast (card_ne_zero.mpr hNonempty)
  constructor
  · intro leaf
    unfold uniformTerminalLaw
    positivity
  · simp [uniformTerminalLaw, hCard]

def coldResourceInclusion (qids : Finset Qid) (root : List Action)
    (terminals : Finset (List Action)) (law : List Action → ℝ)
    (cached : Finset (Qid × List Action)) (p : List Action) (r : Qid × List Action) : ℝ :=
  ∑ leaf ∈ subtreeTerminals terminals p,
    if r ∈ panelDemand qids (root ++ leaf) \ cached then law leaf else 0

theorem referenceColdCost_resource_form (qids : Finset Qid) (root : List Action)
    (terminals : Finset (List Action)) (prediction : Qid × List Action → ℝ)
    (law : List Action → ℝ) (cached : Finset (Qid × List Action)) (p : List Action) :
    referenceColdCost qids root terminals prediction law cached p =
      ∑ r ∈ workflowResources qids root terminals,
        coldResourceInclusion qids root terminals law cached p r * prediction r := by
  have hBill (leaf : List Action) (hl : leaf ∈ subtreeTerminals terminals p) :
      coldWork prediction cached (panelDemand qids (root ++ leaf)) =
        ∑ r ∈ workflowResources qids root terminals,
          if r ∈ panelDemand qids (root ++ leaf) \ cached then prediction r else 0 := by
    have hSubset : panelDemand qids (root ++ leaf) \ cached ⊆
        workflowResources qids root terminals := sdiff_subset.trans
      (terminal_demand_subset_resources qids root terminals leaf (mem_filter.mp hl).1)
    have hFilter : (workflowResources qids root terminals).filter
        (fun r ↦ r ∈ panelDemand qids (root ++ leaf) \ cached) =
        panelDemand qids (root ++ leaf) \ cached := by
      ext r
      simp only [mem_filter]
      exact ⟨fun h ↦ h.2, fun h ↦ ⟨hSubset h, h⟩⟩
    rw [← sum_filter, hFilter]
    rfl
  unfold referenceColdCost
  calc
    _ = ∑ leaf ∈ subtreeTerminals terminals p, law leaf *
        ∑ r ∈ workflowResources qids root terminals,
          if r ∈ panelDemand qids (root ++ leaf) \ cached then prediction r else 0 := by
      apply sum_congr rfl
      intro leaf hl
      rw [hBill leaf hl]
    _ = _ := by
      simp_rw [mul_sum]
      rw [sum_comm]
      apply sum_congr rfl
      intro r _
      rw [coldResourceInclusion, sum_mul]
      apply sum_congr rfl
      intro leaf _
      split_ifs <;> simp

theorem coldWork_demand_mono (weight : Qid × List Action → ℝ)
    (hWeight : ∀ r, 0 ≤ weight r) (cached small large : Finset (Qid × List Action))
    (hSubset : small ⊆ large) : coldWork weight cached small ≤ coldWork weight cached large := by
  exact sum_le_sum_of_subset_of_nonneg (sdiff_subset_sdiff hSubset subset_rfl)
    (fun r _ _ ↦ hWeight r)

def legacyContinuationCold (qids : Finset Qid) (root : List Action)
    (terminals : Finset (List Action)) (prediction : Qid × List Action → ℝ)
    (law : List Action → ℝ) (cached : Finset (Qid × List Action)) (p : List Action) (a : Action) : ℝ :=
  ∑ leaf ∈ subtreeTerminals terminals (p ++ [a]), law leaf * max 0
    (coldWork prediction cached (panelDemand qids (root ++ leaf)) -
      coldWork prediction cached (panelDemand qids (root ++ p)))

/-- Under ledger/set-difference semantics clipping is inactive; suffix equivalence additionally
requires the prefix-complete invariant proved in TreeCheckpoint. -/
theorem legacyContinuationCold_common_shift (qids : Finset Qid) (root : List Action)
    (terminals : Finset (List Action)) (prediction : Qid × List Action → ℝ)
    (hPrediction : ∀ r, 0 ≤ prediction r) (law : List Action → ℝ)
    (cached : Finset (Qid × List Action)) (p : List Action) (a : Action)
    (hMass : ∑ leaf ∈ subtreeTerminals terminals (p ++ [a]), law leaf = 1) :
    legacyContinuationCold qids root terminals prediction law cached p a =
      referenceColdCost qids root terminals prediction law cached (p ++ [a]) -
        coldWork prediction cached (panelDemand qids (root ++ p)) := by
  have hCold (leaf : List Action) (hl : leaf ∈ subtreeTerminals terminals (p ++ [a])) :
      0 ≤ coldWork prediction cached (panelDemand qids (root ++ leaf)) -
        coldWork prediction cached (panelDemand qids (root ++ p)) := by
    apply sub_nonneg.mpr
    apply coldWork_demand_mono prediction hPrediction
    apply panelDemand_prefix_mono
    exact (List.prefix_append_right_inj root).mpr
      ((List.prefix_append p [a]).trans (mem_filter.mp hl).2)
  unfold legacyContinuationCold referenceColdCost
  calc
    _ = ∑ leaf ∈ subtreeTerminals terminals (p ++ [a]), law leaf *
        (coldWork prediction cached (panelDemand qids (root ++ leaf)) -
          coldWork prediction cached (panelDemand qids (root ++ p))) := by
      apply sum_congr rfl
      intro leaf hl
      rw [max_eq_right (hCold leaf hl)]
    _ = _ := by simp_rw [mul_sub]; rw [sum_sub_distrib, ← sum_mul, hMass, one_mul]

def referenceFullCost (qids : Finset Qid) (root : List Action)
    (terminals : Finset (List Action)) (weight : Qid × List Action → ℝ)
    (overhead law : List Action → ℝ) (cached : Finset (Qid × List Action)) (p : List Action) : ℝ :=
  ∑ leaf ∈ subtreeTerminals terminals p,
    law leaf * (coldWork weight cached (panelDemand qids (root ++ leaf)) + overhead leaf)

theorem full_reference_cost_error (qids : Finset Qid) (root : List Action)
    (terminals : Finset (List Action)) (predicted actual radius : Qid × List Action → ℝ)
    (predictedOverhead actualOverhead overheadRadius predictedLaw actualLaw : List Action → ℝ)
    (cached : Finset (Qid × List Action)) (p : List Action) (billBound : ℝ)
    (hLaw : ∀ leaf ∈ subtreeTerminals terminals p, 0 ≤ predictedLaw leaf)
    (hError : ∀ r ∈ workflowResources qids root terminals, |predicted r - actual r| ≤ radius r)
    (hOverhead : ∀ leaf ∈ subtreeTerminals terminals p,
      |predictedOverhead leaf - actualOverhead leaf| ≤ overheadRadius leaf)
    (hBill : ∀ leaf ∈ subtreeTerminals terminals p,
      |coldWork actual cached (panelDemand qids (root ++ leaf)) + actualOverhead leaf| ≤ billBound) :
    |referenceFullCost qids root terminals predicted predictedOverhead predictedLaw cached p -
      referenceFullCost qids root terminals actual actualOverhead actualLaw cached p| ≤
      (∑ leaf ∈ subtreeTerminals terminals p, predictedLaw leaf *
        ((∑ r ∈ panelDemand qids (root ++ leaf) \ cached, radius r) + overheadRadius leaf)) +
      billBound * ∑ leaf ∈ subtreeTerminals terminals p, |predictedLaw leaf - actualLaw leaf| := by
  apply reference_law_cost_error_of_radius _ _ _ _ _ _ billBound hLaw hBill
  intro leaf hl
  have hSubset := terminal_demand_subset_resources qids root terminals leaf (mem_filter.mp hl).1
  have h := total_search_cost_forecast_error (panelDemand qids (root ++ leaf) \ cached)
    (fun _ ↦ 1) predicted actual radius (predictedOverhead leaf) (actualOverhead leaf)
    (overheadRadius leaf) (by intros; norm_num)
    (fun r hr ↦ hError r (hSubset (mem_sdiff.mp hr).1)) (hOverhead leaf hl)
  simpa only [one_mul, coldWork] using h

omit [DecidableEq Qid] in
theorem tree_allocation_common_overhead_iff (terminals : Finset (List Action)) (c : ℝ)
    (penalty : List (TreeEvaluation Action) → List Action → Action → ℝ)
    (common : List (TreeEvaluation Action) → List Action → ℝ)
    (events : List (TreeEvaluation Action)) :
    TreeAllocationRule terminals c (fun before p a ↦ penalty before p a + common before p) events ↔
      TreeAllocationRule terminals c penalty events := by
  unfold TreeAllocationRule treeIndex
  simp only [sub_add_eq_sub_sub, sub_le_sub_iff_right]

end AgentUCTPaper
