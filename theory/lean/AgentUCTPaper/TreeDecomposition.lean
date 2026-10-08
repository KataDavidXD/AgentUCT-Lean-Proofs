import AgentUCTPaper.TreeTopology

/-! # Exact recursive decomposition of backed-up terminal-quality loss -/

set_option autoImplicit false

noncomputable section

namespace AgentUCTPaper

open Finset

variable {Action : Type*} [DecidableEq Action]

def birthDeficit (value : ℝ) (events : List (TreeEvaluation Action)) (p : List Action) : ℝ :=
  (events.map (fun event ↦ if event.expanded = p then value - event.reward else 0)).sum

theorem backedDeficit_cons (value : ℝ) (event : TreeEvaluation Action)
    (events : List (TreeEvaluation Action)) (p : List Action) :
    backedDeficit value (event :: events) p =
      (if p <+: event.expanded then value - event.reward else 0) + backedDeficit value events p := rfl

theorem birthDeficit_cons (value : ℝ) (event : TreeEvaluation Action)
    (events : List (TreeEvaluation Action)) (p : List Action) :
    birthDeficit value (event :: events) p =
      (if event.expanded = p then value - event.reward else 0) + birthDeficit value events p := rfl

theorem event_child_partition (terminals : Finset (List Action))
    (event : TreeEvaluation Action) (hTerminal : event.terminal ∈ terminals)
    (p : List Action) (value : ℝ) :
    (if p <+: event.expanded then value - event.reward else 0) =
      (if event.expanded = p then value - event.reward else 0) +
        ∑ a ∈ availableChildren terminals p,
          if p ++ [a] <+: event.expanded then value - event.reward else 0 := by
  by_cases hp : p <+: event.expanded
  · rcases prefix_eq_or_childAfter p event.expanded hp with he | ⟨a, ha⟩
    · have hNoChild : ∀ a : Action, ¬ p ++ [a] <+: p := by
        intro a hpre
        have hlen := hpre.length_le
        simp at hlen
      simp [he, hNoChild]
    · have hNe : event.expanded ≠ p := by
        intro he
        simp [he, childAfter_self] at ha
      have hLegal : a ∈ availableChildren terminals p :=
        (availableChildren_mem terminals p a).mpr ⟨event.terminal, hTerminal,
          ((childAfter_some_iff p event.expanded a).mp ha).trans event.expanded_is_prefix⟩
      have hOnly : ∀ b : Action, p ++ [b] <+: event.expanded ↔ b = a := by
        intro b
        rw [← childAfter_some_iff, ha, Option.some.injEq, eq_comm]
      simp [hp, hNe, hOnly, hLegal]
  · have hNe : event.expanded ≠ p := by
      intro he
      exact hp (he ▸ List.prefix_refl _)
    have hNoChild : ∀ a : Action, ¬ p ++ [a] <+: event.expanded := by
      exact fun a hpre ↦ hp ((List.prefix_append p [a]).trans hpre)
    simp [hp, hNe, hNoChild]

theorem parent_deficit_partition (terminals : Finset (List Action))
    (events : List (TreeEvaluation Action))
    (hTerminal : ∀ event ∈ events, event.terminal ∈ terminals) (p : List Action) (value : ℝ) :
    backedDeficit value events p = birthDeficit value events p +
      ∑ a ∈ availableChildren terminals p, backedDeficit value events (p ++ [a]) := by
  induction events with
  | nil => simp [backedDeficit, birthDeficit]
  | cons event events ih =>
    have hTail := ih (fun e he ↦ hTerminal e (by simp [he]))
    have hHead := event_child_partition terminals event (hTerminal event (by simp)) p value
    simp_rw [backedDeficit_cons, birthDeficit_cons]
    rw [Finset.sum_add_distrib]
    linarith

/-- Parent and children use the same global history and operational visit counts. -/
theorem operational_subtree_deficit_decomposition (terminals : Finset (List Action))
    (reward : List Action → ℝ) (events : List (TreeEvaluation Action))
    (hTerminal : ∀ event ∈ events, event.terminal ∈ terminals) (p : List Action) :
    backedDeficit (subtreeValue terminals reward p) events p =
      birthDeficit (subtreeValue terminals reward p) events p +
        ∑ a ∈ availableChildren terminals p,
          ((backedCount events (p ++ [a]) : ℝ) * edgeGap terminals reward p a +
            backedDeficit (subtreeValue terminals reward (p ++ [a])) events (p ++ [a])) := by
  rw [parent_deficit_partition terminals events hTerminal p]
  congr 1
  apply Finset.sum_congr rfl
  intro a _
  rw [backedDeficit_identity, backedDeficit_identity]
  unfold edgeGap
  ring

theorem birthDeficit_le_birthCount (value : ℝ) (hValue : value ≤ 1)
    (events : List (TreeEvaluation Action)) (hReward : ∀ e ∈ events, 0 ≤ e.reward)
    (p : List Action) : birthDeficit value events p ≤ birthCount events p := by
  induction events with
  | nil => simp [birthDeficit, birthCount]
  | cons event events ih =>
    have hTail := ih (fun e he ↦ hReward e (by simp [he]))
    have hHead := hReward event (by simp)
    by_cases he : event.expanded = p
    · simp [birthDeficit, birthCount, he] at hTail ⊢
      linarith
    · simpa [birthDeficit, birthCount, he] using hTail

theorem subtree_birthDeficit_nonnegative (terminals : Finset (List Action))
    (reward : List Action → ℝ) (events : List (TreeEvaluation Action))
    (hTable : FixedTableEvents terminals reward events) (p : List Action) :
    0 ≤ birthDeficit (subtreeValue terminals reward p) events p := by
  apply List.sum_nonneg
  intro x hx
  obtain ⟨event, he, rfl⟩ := List.mem_map.mp hx
  split_ifs with hp
  · rw [(hTable event he).2]
    exact sub_nonneg.mpr (subtreeValue_upper terminals reward p event.terminal
      (hTable event he).1 (hp ▸ event.expanded_is_prefix))
  · exact le_rfl

theorem internal_birthDeficit_le_one (terminals : Finset (List Action))
    (reward : List Action → ℝ)
    (hReward : ∀ leaf ∈ terminals, 0 ≤ reward leaf ∧ reward leaf ≤ 1)
    (events : List (TreeEvaluation Action)) (hTable : FixedTableEvents terminals reward events)
    (hLegal : LegalTreeRun (fun p ↦ p ∈ terminals) {[]} events)
    (p : List Action) (hInternal : p ∉ terminals) :
    birthDeficit (subtreeValue terminals reward p) events p ≤ 1 := by
  have hScores : ∀ e ∈ events, 0 ≤ e.reward := by
    intro e he
    rw [(hTable e he).2]
    exact (hReward e.terminal (hTable e he).1).1
  have hb := birthDeficit_le_birthCount _
    (subtreeValue_bounded terminals reward hReward p).2 events hScores p
  have hc := nonterminal_birth_count (fun p ↦ p ∈ terminals) events {[]} p hInternal hLegal
  have hc1 : birthCount events p ≤ 1 := by split_ifs at hc <;> omega
  exact hb.trans (by exact_mod_cast hc1)

theorem root_birthDeficit_zero (terminals : Finset (List Action)) (reward : List Action → ℝ)
    (hReward : ∀ leaf ∈ terminals, 0 ≤ reward leaf ∧ reward leaf ≤ 1)
    (events : List (TreeEvaluation Action)) (hTable : FixedTableEvents terminals reward events)
    (hLegal : LegalTreeRun (fun p ↦ p ∈ terminals) {[]} events) (hRoot : [] ∉ terminals) :
    birthDeficit (subtreeValue terminals reward []) events [] = 0 := by
  have hScores : ∀ e ∈ events, 0 ≤ e.reward := by
    intro e he
    rw [(hTable e he).2]
    exact (hReward e.terminal (hTable e he).1).1
  have hb := birthDeficit_le_birthCount _
    (subtreeValue_bounded terminals reward hReward []).2 events hScores []
  have hc := nonterminal_birth_count (fun p ↦ p ∈ terminals) events {[]} [] hRoot hLegal
  simp at hc
  rw [hc] at hb
  norm_num at hb
  have hn := subtree_birthDeficit_nonnegative terminals reward events hTable []
  exact le_antisymm hb hn

end AgentUCTPaper
