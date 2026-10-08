import AgentUCTPaper.TreeBackup

/-! # Expansion, commit, and training recommendation

All paths are relative to the fixed caller-owned root. A complete evaluation inserts at most
one child; its rollout can be deeper. Selection-index conditions are imposed separately.
-/

set_option autoImplicit false

noncomputable section

namespace AgentUCTPaper

variable {Action : Type*} [DecidableEq Action]

def PrefixClosed (nodes : Finset (List Action)) : Prop :=
  ∀ p ∈ nodes, ∀ q, q <+: p → q ∈ nodes

def LegalTreeEvent (terminal : List Action → Prop) (nodes : Finset (List Action))
    (event : TreeEvaluation Action) : Prop :=
  terminal event.terminal ∧
    ((event.expanded ∈ nodes ∧ terminal event.expanded) ∨
      ∃ p ∈ nodes, ∃ a, event.expanded = p ++ [a] ∧ event.expanded ∉ nodes)

def growTree (nodes : Finset (List Action)) (event : TreeEvaluation Action) :
    Finset (List Action) := insert event.expanded nodes

def replayTree (events : List (TreeEvaluation Action))
    (initial : Finset (List Action) := {[]}) : Finset (List Action) :=
  events.foldl growTree initial

def LegalTreeRun (terminal : List Action → Prop) :
    Finset (List Action) → List (TreeEvaluation Action) → Prop
  | _, [] => True
  | nodes, event :: events =>
      LegalTreeEvent terminal nodes event ∧ LegalTreeRun terminal (growTree nodes event) events

omit [DecidableEq Action] in
theorem root_prefixClosed : PrefixClosed ({[]} : Finset (List Action)) := by
  intro p hp q hq
  simp only [Finset.mem_singleton] at hp ⊢
  subst p
  simpa using hq

theorem insert_child_prefixClosed (nodes : Finset (List Action)) (p : List Action)
    (a : Action) (hClosed : PrefixClosed nodes) (hp : p ∈ nodes) :
    PrefixClosed (insert (p ++ [a]) nodes) := by
  intro x hx q hq
  rcases Finset.mem_insert.mp hx with rfl | hx
  · by_cases hlen : q.length ≤ p.length
    · exact Finset.mem_insert_of_mem
        (hClosed p hp q (List.prefix_of_prefix_length_le hq (List.prefix_append p [a]) hlen))
    · have heq : q = p ++ [a] := hq.eq_of_length_le
        (by simp only [List.length_append, List.length_singleton]; omega)
      rw [heq]
      exact Finset.mem_insert_self _ _
  · exact Finset.mem_insert_of_mem (hClosed x hx q hq)

theorem growTree_prefixClosed (terminal : List Action → Prop)
    (nodes : Finset (List Action)) (event : TreeEvaluation Action)
    (hClosed : PrefixClosed nodes) (hLegal : LegalTreeEvent terminal nodes event) :
    PrefixClosed (growTree nodes event) := by
  rcases hLegal.2 with hOld | ⟨p, hp, a, he, _⟩
  · simpa [growTree, Finset.insert_eq_of_mem hOld.1] using hClosed
  · simpa [growTree, he] using insert_child_prefixClosed nodes p a hClosed hp

theorem replayTree_prefixClosed (terminal : List Action → Prop)
    (events : List (TreeEvaluation Action)) (initial : Finset (List Action))
    (hClosed : PrefixClosed initial) (hLegal : LegalTreeRun terminal initial events) :
    PrefixClosed (replayTree events initial) := by
  induction events generalizing initial with
  | nil => exact hClosed
  | cons event events ih =>
    exact ih _ (growTree_prefixClosed terminal initial event hClosed hLegal.1) hLegal.2

theorem replayTree_card (events : List (TreeEvaluation Action))
    (initial : Finset (List Action)) :
    (replayTree events initial).card ≤ initial.card + events.length := by
  induction events generalizing initial with
  | nil => simp [replayTree]
  | cons event events ih =>
    have h := ih (growTree initial event)
    have hc : (growTree initial event).card ≤ initial.card + 1 :=
      Finset.card_insert_le event.expanded initial
    change (replayTree events (growTree initial event)).card ≤ initial.card + (events.length + 1)
    omega

/-- Membership records expanded paths only, even when the terminal completion is longer. -/
theorem replayTree_mem (events : List (TreeEvaluation Action))
    (initial : Finset (List Action)) (p : List Action) :
    p ∈ replayTree events initial ↔ p ∈ initial ∨ ∃ event ∈ events, p = event.expanded := by
  induction events generalizing initial with
  | nil => simp [replayTree]
  | cons event events ih =>
    change p ∈ replayTree events (growTree initial event) ↔ _
    rw [ih]
    simp only [growTree, Finset.mem_insert, List.mem_cons]
    aesop

/-- A node absent from the expanded tree has received no earlier ancestor update. -/
theorem replayBackup_nonnode_zero (terminal : List Action → Prop)
    (events : List (TreeEvaluation Action)) (p : List Action)
    (hLegal : LegalTreeRun terminal {[]} events) (hAbsent : p ∉ replayTree events {[]}) :
    (replayBackup events emptyStatistics p).visits = 0 ∧
      (replayBackup events emptyStatistics p).rewardSum = 0 := by
  have hClosed := replayTree_prefixClosed terminal events {[]} root_prefixClosed hLegal
  have hMiss : ∀ e ∈ events, ¬ p <+: e.expanded := by
    intro e he hp
    exact hAbsent (hClosed e.expanded ((replayTree_mem events {[]} e.expanded).mpr
      (Or.inr ⟨e, he, rfl⟩)) p hp)
  have hCount : backedCount events p = 0 := by
    simpa [backedCount, List.filter_eq_nil_iff] using hMiss
  have hReturn : backedReturn events p = 0 := by
    apply List.sum_eq_zero
    intro x hx
    obtain ⟨e, he, rfl⟩ := List.mem_map.mp hx
    simp [hMiss e he]
  simp [replayBackup_visits, replayBackup_rewardSum, emptyStatistics, hCount, hReturn]

theorem inserted_node_first_visit (terminal : List Action → Prop)
    (events : List (TreeEvaluation Action)) (event : TreeEvaluation Action)
    (hLegal : LegalTreeRun terminal {[]} events)
    (hNew : event.expanded ∉ replayTree events {[]}) :
    (replayBackup (events ++ [event]) emptyStatistics event.expanded).visits = 1 := by
  have h0 := (replayBackup_nonnode_zero terminal events event.expanded hLegal hNew).1
  rw [replayBackup_append_one]
  simp [backupEvent, h0]

/-- A failed or partial evaluator result is not a completed reward observation. -/
def commitComplete (stats : TreeStatistics Action) (outcome : Option (TreeEvaluation Action)) :
    TreeStatistics Action :=
  match outcome with
  | none => stats
  | some event => backupEvent stats event

theorem incomplete_does_not_backup (stats : TreeStatistics Action) :
    commitComplete stats none = stats := rfl

def keepBest (best event : TreeEvaluation Action) : TreeEvaluation Action :=
  if best.reward < event.reward then event else best

def bestFrom (initial : TreeEvaluation Action) (events : List (TreeEvaluation Action)) :
    TreeEvaluation Action := events.foldl keepBest initial

def bestCompleted : List (TreeEvaluation Action) → Option (TreeEvaluation Action)
  | [] => none
  | event :: events => some (bestFrom event events)

omit [DecidableEq Action] in
theorem bestFrom_mem (initial : TreeEvaluation Action) (events : List (TreeEvaluation Action)) :
    bestFrom initial events ∈ initial :: events := by
  induction events generalizing initial with
  | nil => simp [bestFrom]
  | cons event events ih =>
    change bestFrom (keepBest initial event) events ∈ initial :: event :: events
    rcases List.mem_cons.mp (ih (keepBest initial event)) with h | h
    · rw [h]
      unfold keepBest
      split_ifs <;> simp
    · simp [h]

omit [DecidableEq Action] in
theorem keepBest_left_le (initial event : TreeEvaluation Action) :
    initial.reward ≤ (keepBest initial event).reward := by
  unfold keepBest
  split_ifs with h
  · exact h.le
  · exact le_rfl

omit [DecidableEq Action] in
theorem keepBest_right_le (initial event : TreeEvaluation Action) :
    event.reward ≤ (keepBest initial event).reward := by
  unfold keepBest
  split_ifs with h
  · exact le_rfl
  · exact le_of_not_gt h

omit [DecidableEq Action] in
theorem bestFrom_initial_le (initial : TreeEvaluation Action)
    (events : List (TreeEvaluation Action)) :
    initial.reward ≤ (bestFrom initial events).reward := by
  induction events generalizing initial with
  | nil => exact le_rfl
  | cons event events ih =>
    exact (keepBest_left_le initial event).trans (ih (keepBest initial event))

omit [DecidableEq Action] in
theorem bestFrom_all_le (initial : TreeEvaluation Action)
    (events : List (TreeEvaluation Action)) (event : TreeEvaluation Action) (he : event ∈ events) :
    event.reward ≤ (bestFrom initial events).reward := by
  induction events generalizing initial with
  | nil => simp at he
  | cons head events ih =>
    rcases List.mem_cons.mp he with rfl | he
    · exact (keepBest_right_le initial event).trans (bestFrom_initial_le _ _)
    · exact ih _ he

omit [DecidableEq Action] in
theorem bestCompleted_spec (events : List (TreeEvaluation Action))
    (best : TreeEvaluation Action) (hBest : bestCompleted events = some best) :
    best ∈ events ∧ ∀ event ∈ events, event.reward ≤ best.reward := by
  cases events with
  | nil => simp [bestCompleted] at hBest
  | cons head events =>
    simp only [bestCompleted, Option.some.injEq] at hBest
    subst best
    refine ⟨bestFrom_mem head events, ?_⟩
    intro event he
    rcases List.mem_cons.mp he with rfl | he
    · exact bestFrom_initial_le event events
    · exact bestFrom_all_le head events event he

omit [DecidableEq Action] in
theorem keepBest_tie_keeps_first (initial event : TreeEvaluation Action)
    (hTie : initial.reward = event.reward) : keepBest initial event = initial := by
  simp [keepBest, hTie]

end AgentUCTPaper
