import AgentUCTPaper.DynamicCompletion

/-! # A separation reachable by overlapping-pair evaluations from an empty cache

Both histories use the same panel order, publish complete two-query panels,
and pay the same cold bill.
Every branch total agrees. The active pair's bills and budget-feasible action
are reversed. Thus the witness does not require arbitrary warm-cache entries.
-/

set_option autoImplicit false
noncomputable section
namespace AgentUCTPaper.ReachablePairs
open Finset

def firstPanel : Finset ℕ := {0, 1}
def secondPanel : Finset ℕ := {1, 2}
def allQueries : Finset ℕ := {0, 1, 2}
def demand (panel : Finset ℕ) (branch : Bool) : Finset (ℕ × Bool) :=
  panel ×ˢ {branch}
def leftCache := demand firstPanel false ∪ demand secondPanel true
def rightCache := demand secondPanel false ∪ demand firstPanel true
def price (_ : ℕ × Bool) : ℝ := 1

/-- The two cache states are the unions of actual complete overlapping-panel demands. -/
theorem reachable_from_empty :
    dynamicDemand [demand firstPanel false, demand secondPanel true] = leftCache ∧
    dynamicDemand [demand firstPanel true, demand secondPanel false] = rightCache := by
  simp [dynamicDemand, leftCache, rightCache, union_comm]

/-- Materializing either two-evaluation history consumes four unit-price resources. -/
theorem equal_warmup_cost :
    dynamicSpend price ∅ [demand firstPanel false, demand secondPanel true] = 4 ∧
    dynamicSpend price ∅ [demand firstPanel true, demand secondPanel false] = 4 := by
  simp [dynamicSpend, demand, firstPanel, secondPanel, coldWork, price]
  norm_cast

/-- Counts and weighted residuals per branch are identical in the two histories. -/
theorem equal_full_panel_residuals (branch : Bool) :
    coldWork price leftCache (demand allQueries branch) = 1 ∧
    coldWork price rightCache (demand allQueries branch) = 1 := by
  cases branch <;>
    norm_num [coldWork, demand, allQueries, leftCache, rightCache,
      firstPanel, secondPanel, price] <;> norm_cast

/-- At the same active panel, exact completion bills have opposite rankings. -/
theorem active_pair_ranking_reverses :
    coldWork price leftCache (demand firstPanel false) = 0 ∧
    coldWork price leftCache (demand firstPanel true) = 1 ∧
    coldWork price rightCache (demand firstPanel false) = 1 ∧
    coldWork price rightCache (demand firstPanel true) = 0 := by
  norm_num [coldWork, demand, leftCache, rightCache, firstPanel, secondPanel, price]
  norm_cast

/-- Adding one unit of common recurring work yields opposite budget-feasible choices. -/
theorem affordable_action_reverses :
    1 + coldWork price leftCache (demand firstPanel false) ≤ 1 ∧
    ¬ 1 + coldWork price leftCache (demand firstPanel true) ≤ 1 ∧
    ¬ 1 + coldWork price rightCache (demand firstPanel false) ≤ 1 ∧
    1 + coldWork price rightCache (demand firstPanel true) ≤ 1 := by
  obtain ⟨h1, h2, h3, h4⟩ := active_pair_ranking_reverses
  rw [h1, h2, h3, h4]
  norm_num

end AgentUCTPaper.ReachablePairs
