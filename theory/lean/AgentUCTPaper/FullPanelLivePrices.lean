import AgentUCTPaper.TreeDemandQuotient

/-! # Full-panel accounting when checkpoint observations change predicted prices

At one decision, summing residual prices over queries is exact. Across decisions,
publication and price revision are distinct updates. A fixed-price residual table
alone does not describe how a predictor derives its new prices from saved state.
-/

set_option autoImplicit false
noncomputable section

namespace AgentUCTPaper
open Finset

variable {Q P X : Type*} [DecidableEq Q] [DecidableEq P]

/-- A supplied full-panel completion law can use residual prefix sums exactly,
including query-dependent prices inferred from the current checkpoint state. -/
theorem full_panel_live_completion_quotient (weight : Q × P → ℝ)
    (cached : Finset (Q × P)) (qids : Finset Q) (outcomes : Finset X)
    (law : X → ℝ) (prefixes : X → Finset P) :
    (∑ x ∈ outcomes, law x * coldWork weight cached (qids ×ˢ prefixes x)) =
      ∑ x ∈ outcomes, law x *
        ∑ p ∈ prefixes x, ∑ q ∈ qids, if (q, p) ∈ cached then 0 else weight (q, p) := by
  apply sum_congr rfl
  intro x _
  rw [full_panel_residual_quotient]

/-- Publication zeros its prefixes; all other residual totals also receive the
sum of the new-minus-old prices over the still-uncached query resources. -/
theorem full_panel_live_price_update (old next : Q × P → ℝ)
    (cached : Finset (Q × P)) (qids : Finset Q) (published : Finset P) (p : P) :
    (∑ q ∈ qids, if (q, p) ∈ cached ∪ (qids ×ˢ published) then 0 else next (q, p)) =
      if p ∈ published then 0 else
        (∑ q ∈ qids, if (q, p) ∈ cached then 0 else old (q, p)) +
        ∑ q ∈ qids, if (q, p) ∈ cached then 0 else next (q, p) - old (q, p) := by
  rw [full_panel_residual_update]
  split_ifs
  · rfl
  · rw [← sum_add_distrib]
    apply sum_congr rfl
    intro q _
    split_ifs <;> ring

/-- Even without publication, a scalar residual can change when a predictor learns
a zero-work guard. The price update cannot be replaced by cache publication alone. -/
theorem unpublished_price_revision_changes_residual :
    (∑ q ∈ ({()} : Finset Unit),
      if (q, ()) ∈ (∅ : Finset (Unit × Unit)) then 0 else (1 : ℝ)) = 1 ∧
    (∑ q ∈ ({()} : Finset Unit),
      if (q, ()) ∈ (∅ : Finset (Unit × Unit)) then 0 else (0 : ℝ)) = 0 := by
  simp

end AgentUCTPaper
