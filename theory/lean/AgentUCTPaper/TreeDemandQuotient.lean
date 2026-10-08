import AgentUCTPaper.TreeGraphInformation

/-! # Exact cache compression for a fixed family of query demands

Queries may be grouped when every allowed panel treats all members of a group
identically. Weighted residual bills per group and prefix are sufficient both
for billing and for publication updates. Merging queries that a panel separates
loses information, even with unit prices and binary missing-resource vectors.
This is a statement about information; no particular storage layout is required.
-/

set_option autoImplicit false
noncomputable section
namespace AgentUCTPaper
open Finset

variable {Q C P : Type*} [Fintype Q] [DecidableEq Q] [DecidableEq C] [DecidableEq P]

def groupedQuantity (group : Q → C) (quantity : Q → ℝ) (c : C) : ℝ :=
  ∑ q : Q, if group q = c then quantity q else 0

def groupedResidual (group : Q → C) (weight : Q × P → ℝ)
    (cached : Finset (Q × P)) (c : C) (p : P) : ℝ :=
  groupedQuantity group (fun q ↦ if (q, p) ∈ cached then 0 else weight (q, p)) c

omit [DecidableEq Q] in
/-- Group totals recover every panel that is a union of groups. -/
theorem grouped_panel_sum (group : Q → C) (quantity : Q → ℝ) (selected : Finset C) :
    (∑ q ∈ univ.filter (fun q ↦ group q ∈ selected), quantity q) =
      ∑ c ∈ selected, groupedQuantity group quantity c := by
  unfold groupedQuantity
  rw [sum_comm]
  simp [sum_filter]

/-- Group residuals give exactly the physical bill of every allowed completion. -/
theorem demand_group_cost_quotient (group : Q → C) (weight : Q × P → ℝ)
    (cached : Finset (Q × P)) (selected : Finset C) (prefixes : Finset P) :
    coldWork weight cached ((univ.filter (fun q ↦ group q ∈ selected)) ×ˢ prefixes) =
      ∑ p ∈ prefixes, ∑ c ∈ selected, groupedResidual group weight cached c p := by
  rw [full_panel_residual_quotient]
  apply sum_congr rfl
  intro p _
  exact grouped_panel_sum group _ selected

/-- Publication is closed on the same summary: affected group-prefix cells become zero. -/
theorem demand_group_publication (group : Q → C) (weight : Q × P → ℝ)
    (cached : Finset (Q × P)) (selected : Finset C) (prefixes : Finset P)
    (c : C) (p : P) :
    groupedResidual group weight
      (cached ∪ ((univ.filter (fun q ↦ group q ∈ selected)) ×ˢ prefixes)) c p =
      if c ∈ selected ∧ p ∈ prefixes then 0 else groupedResidual group weight cached c p := by
  unfold groupedResidual groupedQuantity
  by_cases hc : c ∈ selected <;> by_cases hp : p ∈ prefixes
  · simp only [hc, hp, and_self, if_true]
    apply sum_eq_zero
    intro q _
    by_cases hq : group q = c <;> simp [hq, hc, hp]
  · simp [hp]
  · simp only [hc, false_and, if_false]
    apply sum_congr rfl
    intro q _
    by_cases hq : group q = c <;> simp [hq, hc, hp]
  · simp [hp]

/-- The canonical grouping is the vector of memberships in the allowed panels. -/
def panelProfile {J : Type*} (panels : J → Finset Q) (q : Q) : J → Prop :=
  fun j ↦ q ∈ panels j

omit [Fintype Q] [DecidableEq Q] [DecidableEq C] in
/-- A grouping respects every panel exactly when equal groups have equal profiles. -/
theorem grouping_respects_profiles {J : Type*} (panels : J → Finset Q) (group : Q → C) :
    (∀ q r, group q = group r → panelProfile panels q = panelProfile panels r) ↔
      ∀ j q r, group q = group r → (q ∈ panels j ↔ r ∈ panels j) := by
  constructor
  · intro h j q r hqr
    exact Iff.of_eq (congrFun (h q r hqr) j)
  · intro h q r hqr
    funext j
    exact propext (h j q r hqr)

private theorem grouped_singleton (group : Q → C) (q : Q) (c : C) :
    groupedQuantity group (fun r ↦ if r = q then 1 else 0) c =
      if group q = c then 1 else 0 := by
  unfold groupedQuantity
  rw [sum_eq_single q]
  · simp
  · intro r _ hr
    simp [hr]
  · simp

/-- A group that merges two differently demanded queries cannot determine every bill.
The witness quantities are realizable binary residuals with unit physical prices. -/
theorem demand_separating_merge_loses_information (group : Q → C) (panel : Finset Q)
    (q r : Q) (hGroup : group q = group r) (hq : q ∈ panel) (hr : r ∉ panel) :
    ¬ ∃ decode : (C → ℝ) → ℝ, ∀ quantity : Q → ℝ,
      (∀ x, quantity x = 0 ∨ quantity x = 1) →
      decode (groupedQuantity group quantity) = ∑ x ∈ panel, quantity x := by
  rintro ⟨decode, hDecode⟩
  have hb (a : Q) (x : Q) : (if x = a then (1 : ℝ) else 0) = 0 ∨
      (if x = a then (1 : ℝ) else 0) = 1 := by split_ifs <;> simp
  have hLeft := hDecode (fun x ↦ if x = q then 1 else 0) (hb q)
  have hRight := hDecode (fun x ↦ if x = r then 1 else 0) (hb r)
  have hSame : groupedQuantity group (fun x ↦ if x = q then 1 else 0) =
      groupedQuantity group (fun x ↦ if x = r then 1 else 0) := by
    funext c
    simp only [grouped_singleton, hGroup]
  rw [hSame] at hLeft
  simp [hq] at hLeft
  simp [hr] at hRight
  linarith

end AgentUCTPaper
