import AgentUCTPaper.TreeProtocol

/-! # Exact adaptive backup deficit for a fixed finite terminal table

There is no sampling or independence assumption. The missing rate problem is made explicit:
Q at an internal node differs from its best terminal value by its actual cumulative
descendant deficit divided by the number of backed-up evaluations.
-/

set_option autoImplicit false

noncomputable section

namespace AgentUCTPaper

open Finset

variable {Action : Type*} [DecidableEq Action]

def subtreeTerminals (terminals : Finset (List Action)) (p : List Action) :
    Finset (List Action) := terminals.filter (fun leaf ↦ p <+: leaf)

def subtreeValue (terminals : Finset (List Action)) (reward : List Action → ℝ)
    (p : List Action) : ℝ :=
  if h : (subtreeTerminals terminals p).Nonempty then
    (subtreeTerminals terminals p).sup' h reward
  else 0

def FixedTableEvents (terminals : Finset (List Action)) (reward : List Action → ℝ)
    (events : List (TreeEvaluation Action)) : Prop :=
  ∀ event ∈ events, event.terminal ∈ terminals ∧ event.reward = reward event.terminal

theorem subtreeValue_upper (terminals : Finset (List Action)) (reward : List Action → ℝ)
    (p leaf : List Action) (hLeaf : leaf ∈ terminals) (hPath : p <+: leaf) :
    reward leaf ≤ subtreeValue terminals reward p := by
  have hm : leaf ∈ subtreeTerminals terminals p := mem_filter.mpr ⟨hLeaf, hPath⟩
  have hn : (subtreeTerminals terminals p).Nonempty := ⟨leaf, hm⟩
  simp only [subtreeValue, dif_pos hn]
  exact Finset.le_sup' reward hm

theorem subtreeValue_attained (terminals : Finset (List Action)) (reward : List Action → ℝ)
    (p : List Action) (h : (subtreeTerminals terminals p).Nonempty) :
    ∃ leaf ∈ terminals, p <+: leaf ∧ subtreeValue terminals reward p = reward leaf := by
  obtain ⟨leaf, hm, he⟩ := Finset.exists_mem_eq_sup' h reward
  exact ⟨leaf, (mem_filter.mp hm).1, (mem_filter.mp hm).2, by simp [subtreeValue, h, he]⟩

theorem subtreeValue_at_terminal (terminals : Finset (List Action)) (reward : List Action → ℝ)
    (hAntichain : ∀ p ∈ terminals, ∀ q ∈ terminals, p <+: q → p = q)
    (leaf : List Action) (hLeaf : leaf ∈ terminals) :
    subtreeValue terminals reward leaf = reward leaf := by
  have h : (subtreeTerminals terminals leaf).Nonempty :=
    ⟨leaf, mem_filter.mpr ⟨hLeaf, List.prefix_refl _⟩⟩
  obtain ⟨other, ho, hp, hv⟩ := subtreeValue_attained terminals reward leaf h
  have he := hAntichain leaf hLeaf other ho hp
  simpa [← he] using hv

def backedDeficit (value : ℝ) (events : List (TreeEvaluation Action)) (p : List Action) : ℝ :=
  (events.map (fun event ↦ if p <+: event.expanded then value - event.reward else 0)).sum

theorem backedDeficit_identity (value : ℝ) (events : List (TreeEvaluation Action))
    (p : List Action) :
    backedDeficit value events p = (backedCount events p : ℝ) * value - backedReturn events p := by
  induction events with
  | nil => simp [backedDeficit, backedCount, backedReturn]
  | cons event events ih =>
    by_cases h : p <+: event.expanded
    · simp [backedDeficit, backedCount, backedReturn, h] at ih ⊢
      linarith
    · simpa [backedDeficit, backedCount, backedReturn, h] using ih

theorem operational_mean_deficit (value : ℝ) (events : List (TreeEvaluation Action))
    (p : List Action) (hCount : 0 < backedCount events p) :
    (replayBackup events emptyStatistics p).mean =
      value - backedDeficit value events p / backedCount events p := by
  rw [replayBackup_mean, backedDeficit_identity]
  have hn : (backedCount events p : ℝ) ≠ 0 := Nat.cast_ne_zero.mpr (Nat.ne_of_gt hCount)
  field_simp
  ring

theorem subtree_backedDeficit_nonnegative (terminals : Finset (List Action))
    (reward : List Action → ℝ) (events : List (TreeEvaluation Action))
    (hTable : FixedTableEvents terminals reward events) (p : List Action) :
    0 ≤ backedDeficit (subtreeValue terminals reward p) events p := by
  apply List.sum_nonneg
  intro x hx
  obtain ⟨event, he, rfl⟩ := List.mem_map.mp hx
  split_ifs with hp
  · rw [(hTable event he).2]
    exact sub_nonneg.mpr (subtreeValue_upper terminals reward p event.terminal
      (hTable event he).1 (hp.trans event.expanded_is_prefix))
  · exact le_rfl

theorem operational_mean_le_subtreeValue (terminals : Finset (List Action))
    (reward : List Action → ℝ) (events : List (TreeEvaluation Action))
    (hTable : FixedTableEvents terminals reward events) (p : List Action)
    (hCount : 0 < backedCount events p) :
    (replayBackup events emptyStatistics p).mean ≤ subtreeValue terminals reward p := by
  rw [operational_mean_deficit _ events p hCount]
  exact sub_le_self _ (div_nonneg
    (subtree_backedDeficit_nonnegative terminals reward events hTable p) (Nat.cast_nonneg _))

theorem terminal_backedDeficit_zero (terminals : Finset (List Action))
    (reward : List Action → ℝ) (events : List (TreeEvaluation Action))
    (hTable : FixedTableEvents terminals reward events)
    (hAntichain : ∀ p ∈ terminals, ∀ q ∈ terminals, p <+: q → p = q)
    (leaf : List Action) (hLeaf : leaf ∈ terminals) :
    backedDeficit (reward leaf) events leaf = 0 := by
  apply List.sum_eq_zero
  intro x hx
  obtain ⟨event, he, rfl⟩ := List.mem_map.mp hx
  split_ifs with hp
  · have hEq := hAntichain leaf hLeaf event.terminal (hTable event he).1
      (hp.trans event.expanded_is_prefix)
    simp [(hTable event he).2, hEq]
  · rfl

theorem operational_terminal_mean_exact (terminals : Finset (List Action))
    (reward : List Action → ℝ) (events : List (TreeEvaluation Action))
    (hTable : FixedTableEvents terminals reward events)
    (hAntichain : ∀ p ∈ terminals, ∀ q ∈ terminals, p <+: q → p = q)
    (leaf : List Action) (hLeaf : leaf ∈ terminals) (hCount : 0 < backedCount events leaf) :
    (replayBackup events emptyStatistics leaf).mean = reward leaf := by
  rw [operational_mean_deficit _ events leaf hCount,
    terminal_backedDeficit_zero terminals reward events hTable hAntichain leaf hLeaf]
  simp

theorem root_deficit_is_terminal_quality_regret (value : ℝ)
    (events : List (TreeEvaluation Action)) :
    backedDeficit value events [] = (events.map (fun event ↦ value - event.reward)).sum := by
  simp [backedDeficit]

omit [DecidableEq Action] in
theorem sum_returns_le_best (value : ℝ) (events : List (TreeEvaluation Action))
    (hBound : ∀ event ∈ events, event.reward ≤ value) :
    (events.map TreeEvaluation.reward).sum ≤ events.length * value := by
  induction events with
  | nil => simp
  | cons event events ih =>
    have hTail := ih (fun e he ↦ hBound e (by simp [he]))
    have hHead := hBound event (by simp)
    simp only [List.map_cons, List.sum_cons, List.length_cons, Nat.cast_add, Nat.cast_one]
    nlinarith

/-- This connects an actual root quality-regret bound to the training endpoint only. -/
theorem best_training_simple_gap (value : ℝ) (events : List (TreeEvaluation Action))
    (best : TreeEvaluation Action) (hBest : bestCompleted events = some best) :
    value - best.reward ≤ backedDeficit value events [] / events.length := by
  have hSpec := bestCompleted_spec events best hBest
  have hLen : 0 < events.length := List.length_pos_iff.mpr (by
    intro hNil
    simp [hNil, bestCompleted] at hBest)
  have hSum := sum_returns_le_best best.reward events hSpec.2
  rw [le_div_iff₀ (Nat.cast_pos.mpr hLen), backedDeficit_identity]
  simp only [backedCount, List.nil_prefix, decide_true, List.filter_true,
    backedReturn, if_true] at *
  nlinarith

end AgentUCTPaper
