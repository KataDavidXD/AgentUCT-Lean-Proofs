import AgentUCTPaper.TreeEstimatorDynamics

/-! # Information retained by a qid-prefix cache

Full-panel execution admits a prefix-level quotient, even for a nonrectangular cache
when fixed resource weights are aggregated as residual bills. Query-selective demands
can distinguish caches with identical per-prefix hit counts and residual bills.
The counterexample uses two one-step terminal prefixes, so prefix completeness holds.
-/

set_option autoImplicit false
noncomputable section

namespace AgentUCTPaper
open Finset

variable {Q P : Type*} [DecidableEq Q] [DecidableEq P]

/-- A fixed full panel only needs the residual bill of each prefix for its next bill. -/
theorem full_panel_residual_quotient (weight : Q × P → ℝ)
    (cached : Finset (Q × P)) (qids : Finset Q) (prefixes : Finset P) :
    coldWork weight cached (qids ×ˢ prefixes) =
      ∑ p ∈ prefixes, ∑ q ∈ qids, if (q, p) ∈ cached then 0 else weight (q, p) := by
  simp only [coldWork, sdiff_eq_filter, sum_filter, sum_product]
  rw [sum_comm]
  apply sum_congr rfl
  intro p _
  apply sum_congr rfl
  intro q _
  split_ifs <;> rfl

/-- Rectangular caches reduce exactly to a weighted prefix cache. -/
theorem rectangular_cache_cost_quotient (weight : Q × P → ℝ)
    (qids : Finset Q) (saved demanded : Finset P) :
    coldWork weight (qids ×ˢ saved) (qids ×ˢ demanded) =
      coldWork (fun p ↦ ∑ q ∈ qids, weight (q, p)) saved demanded := by
  rw [full_panel_residual_quotient]
  simp only [coldWork, sdiff_eq_filter, sum_filter]
  apply sum_congr rfl
  intro p _
  by_cases hp : p ∈ saved
  · simp only [mem_product, hp, and_true, not_true_eq_false, if_false]
    exact sum_eq_zero (fun q hq ↦ if_pos hq)
  · simp only [mem_product, hp, and_false, if_false, not_false_eq_true, if_true]

/-- A complete-panel publication preserves rectangularity. -/
theorem full_panel_publication_rectangular (qids : Finset Q) (saved demanded : Finset P) :
    (qids ×ˢ saved) ∪ (qids ×ˢ demanded) = qids ×ˢ (saved ∪ demanded) := by
  exact product_union.symm

/-- The quotient is preserved along every finite full-panel publication history. -/
theorem full_panel_history_rectangular (qids : Finset Q) (saved : Finset P)
    (demands : List (Finset P)) :
    demands.foldl (fun cached demand ↦ cached ∪ (qids ×ˢ demand)) (qids ×ˢ saved) =
      qids ×ˢ demands.foldl (fun cached demand ↦ cached ∪ demand) saved := by
  induction demands generalizing saved with
  | nil => rfl
  | cons demand rest ih =>
    simpa only [List.foldl_cons, full_panel_publication_rectangular] using ih (saved ∪ demand)

/-- Full-panel publication also updates residual prefix bills without qid identities. -/
theorem full_panel_residual_update (weight : Q × P → ℝ) (cached : Finset (Q × P))
    (qids : Finset Q) (published : Finset P) (p : P) :
    (∑ q ∈ qids, if (q, p) ∈ cached ∪ (qids ×ˢ published) then 0 else weight (q, p)) =
      if p ∈ published then 0 else
        ∑ q ∈ qids, if (q, p) ∈ cached then 0 else weight (q, p) := by
  by_cases hp : p ∈ published
  · simp only [hp, if_true]
    apply sum_eq_zero
    intro q hq
    simp [hq, hp]
  · simp [hp]

namespace GraphWitness

def leftCache : Finset (Bool × Bool) := {(false, false), (true, true)}
def rightCache : Finset (Bool × Bool) := {(true, false), (false, true)}
def hitCount (cached : Finset (Bool × Bool)) (p : Bool) : ℕ :=
  ((univ : Finset Bool).filter (fun q ↦ (q, p) ∈ cached)).card
def bill (cached : Finset (Bool × Bool)) (action : Bool) : ℝ :=
  coldWork (fun _ ↦ 1) cached {(false, action)}

end GraphWitness

open GraphWitness

/-- Prefix counts discard exactly the query identity needed by the next partial panel. -/
theorem GraphWitness.counts_equal : hitCount leftCache = hitCount rightCache := by
  funext p
  cases p <;> decide

/-- Even the exact residual full-panel bill is identical in both states. -/
theorem GraphWitness.residual_bills_equal (p : Bool) :
    coldWork (fun _ ↦ (1 : ℝ)) leftCache (univ ×ˢ {p}) =
      coldWork (fun _ ↦ (1 : ℝ)) rightCache (univ ×ˢ {p}) := by
  cases p <;> norm_num [coldWork, leftCache, rightCache] <;> decide

/-- For the same active qid, the two prefixes exchange their cold bills. -/
theorem GraphWitness.bills_reverse :
    bill leftCache false = 0 ∧ bill leftCache true = 1 ∧
      bill rightCache false = 1 ∧ bill rightCache true = 0 := by
  norm_num [bill, coldWork, leftCache, rightCache]
  decide

/-- No deterministic count-only policy minimizes the next bill in both states. -/
theorem GraphWitness.no_count_only_optimal_policy :
    ¬ ∃ choose : (Bool → ℕ) → Bool,
      (∀ a, bill leftCache (choose (hitCount leftCache)) ≤ bill leftCache a) ∧
      (∀ a, bill rightCache (choose (hitCount rightCache)) ≤ bill rightCache a) := by
  rintro ⟨choose, hl, hr⟩
  have hl' := hl false
  have hr' := hr true
  rw [← counts_equal] at hr'
  rcases bills_reverse with ⟨h00, h01, h10, h11⟩
  cases h : choose (hitCount leftCache)
  · rw [h, h10, h11] at hr'
    norm_num at hr'
  · rw [h, h01, h00] at hl'
    norm_num at hl'

/-- An identity-blind randomized choice incurs at least half a unit in one state.
Here p is its probability of choosing the first action in either indistinguishable state. -/
theorem GraphWitness.randomized_excess_lower_bound (p : ℝ) :
    (1 / 2 : ℝ) ≤ max (1 - p) p := by
  have h1 := le_max_left (1 - p) p
  have h2 := le_max_right (1 - p) p
  linarith

/-- A single predicted bill for indistinguishable zero/one bills has irreducible error. -/
theorem GraphWitness.common_estimate_error_lower_bound (estimate : ℝ) :
    (1 / 2 : ℝ) ≤ max |estimate| |estimate - 1| := by
  have h1 := le_abs_self estimate
  have h2 := neg_le_abs (estimate - 1)
  have h3 := le_max_left |estimate| |estimate - 1|
  have h4 := le_max_right |estimate| |estimate - 1|
  linarith

/-- With a unit recurring bill and a unit remaining budget, feasibility reverses. -/
theorem GraphWitness.budget_feasibility_reverses :
    (1 + bill leftCache false ≤ 1 ∧ ¬ 1 + bill leftCache true ≤ 1) ∧
      (1 + bill rightCache true ≤ 1 ∧ ¬ 1 + bill rightCache false ≤ 1) := by
  rcases bills_reverse with ⟨h00, h01, h10, h11⟩
  rw [h00, h01, h10, h11]
  norm_num

end AgentUCTPaper
