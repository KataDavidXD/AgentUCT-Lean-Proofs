import AgentUCTPaper.TreeReturns
import AgentUCTPaper.TreeAllocation

/-! # Deriving local child histories from whole-tree events -/

set_option autoImplicit false

noncomputable section

namespace AgentUCTPaper

variable {Action : Type*} [DecidableEq Action]

def childAfter (p path : List Action) : Option Action :=
  if p <+: path then (path.drop p.length).head? else none

theorem childAfter_self (p : List Action) : childAfter p p = none := by
  simp [childAfter]

theorem childAfter_append (p : List Action) (a : Action) (tail : List Action) :
    childAfter p (p ++ a :: tail) = some a := by
  simp [childAfter]

theorem childAfter_some_iff (p path : List Action) (a : Action) :
    childAfter p path = some a ↔ p ++ [a] <+: path := by
  constructor
  · intro h
    unfold childAfter at h
    split_ifs at h with hp
    · obtain ⟨tail, ht⟩ := List.head?_eq_some_iff.mp h
      have hPath := (List.prefix_iff_eq_append.mp hp).symm
      rw [ht] at hPath
      rw [hPath]
      exact ⟨tail, by simp⟩
  · intro h
    obtain ⟨tail, rfl⟩ := h
    simpa [List.append_assoc] using childAfter_append p a tail

theorem prefix_eq_or_childAfter (p path : List Action) (h : p <+: path) :
    path = p ∨ ∃ a, childAfter p path = some a := by
  obtain ⟨tail, rfl⟩ := h
  cases tail with
  | nil => simp
  | cons a tail => exact Or.inr ⟨a, childAfter_append p a tail⟩

def localActions (events : List (TreeEvaluation Action)) (p : List Action) : List Action :=
  events.filterMap (fun event ↦ childAfter p event.expanded)

def actionOccurrences (actions : List Action) (a : Action) : ℕ :=
  (actions.filter (fun x ↦ decide (x = a))).length

def birthCount (events : List (TreeEvaluation Action)) (p : List Action) : ℕ :=
  (events.filter (fun event ↦ decide (event.expanded = p))).length

theorem localActions_append (before after : List (TreeEvaluation Action)) (p : List Action) :
    localActions (before ++ after) p = localActions before p ++ localActions after p := by
  simp [localActions]

theorem localActions_child_count (events : List (TreeEvaluation Action))
    (p : List Action) (a : Action) :
    actionOccurrences (localActions events p) a = backedCount events (p ++ [a]) := by
  induction events with
  | nil => simp [localActions, actionOccurrences, backedCount]
  | cons event events ih =>
    cases h : childAfter p event.expanded with
    | none =>
      have hn : ¬ p ++ [a] <+: event.expanded := by
        intro hp
        have hs := (childAfter_some_iff p event.expanded a).mpr hp
        simp [h] at hs
      simpa [localActions, actionOccurrences, backedCount, h, hn] using ih
    | some b =>
      have hChild : p ++ [a] <+: event.expanded ↔ b = a := by
        rw [← childAfter_some_iff, h, Option.some.injEq]
      by_cases hb : b = a
      · simp [localActions, actionOccurrences, backedCount, h, hChild, hb] at ih ⊢
        omega
      · simpa [localActions, actionOccurrences, backedCount, h, hChild, hb] using ih

/-- Child observations are the same terminal evaluations selected through that local action. -/
theorem child_event_subsequence (events : List (TreeEvaluation Action))
    (p : List Action) (a : Action) :
    events.filter (fun e ↦ decide (childAfter p e.expanded = some a)) =
      events.filter (fun e ↦ decide (p ++ [a] <+: e.expanded)) := by
  simp only [childAfter_some_iff]

theorem parent_count_decomposition (events : List (TreeEvaluation Action)) (p : List Action) :
    backedCount events p = (localActions events p).length + birthCount events p := by
  induction events with
  | nil => simp [backedCount, localActions, birthCount]
  | cons event events ih =>
    by_cases hp : p <+: event.expanded
    · rcases prefix_eq_or_childAfter p event.expanded hp with he | ⟨a, ha⟩
      · simp [backedCount, localActions, birthCount, he, childAfter_self] at ih ⊢
        omega
      · have hne : event.expanded ≠ p := by
          intro he
          simp [he, childAfter_self] at ha
        simp [backedCount, localActions, birthCount, hp, ha, hne] at ih ⊢
        omega
    · have hne : event.expanded ≠ p := by
        intro he
        exact hp (he ▸ List.prefix_refl _)
      have hn : childAfter p event.expanded = none := by simp [childAfter, hp]
      simpa [backedCount, localActions, birthCount, hp, hn, hne] using ih

/-- An internal node contributes a birth rollout at most once, and never after it already exists. -/
theorem nonterminal_birth_count (terminal : List Action → Prop)
    (events : List (TreeEvaluation Action)) (initial : Finset (List Action))
    (p : List Action) (hNonterminal : ¬ terminal p) (hLegal : LegalTreeRun terminal initial events) :
    birthCount events p ≤ if p ∈ initial then 0 else 1 := by
  induction events generalizing initial with
  | nil => simp [birthCount]
  | cons event events ih =>
    have ht := ih (growTree initial event) hLegal.2
    by_cases he : event.expanded = p
    · have hAbsent : p ∉ initial := by
        rcases hLegal.1.2 with hOld | ⟨q, hq, a, ha, hNew⟩
        · exact (hNonterminal (he ▸ hOld.2)).elim
        · simpa [he] using hNew
      simp [growTree, he] at ht
      simp [birthCount, he, hAbsent]
      simpa [birthCount] using ht
    · have he' : p ≠ event.expanded := Ne.symm he
      simpa [birthCount, growTree, he, he'] using ht

theorem parent_count_birth_offset (terminal : List Action → Prop)
    (events : List (TreeEvaluation Action)) (initial : Finset (List Action))
    (p : List Action) (hNonterminal : ¬ terminal p) (hLegal : LegalTreeRun terminal initial events) :
    ∃ offset : ℕ, offset ≤ 1 ∧
      backedCount events p = (localActions events p).length + offset := by
  refine ⟨birthCount events p, ?_, parent_count_decomposition events p⟩
  have h := nonterminal_birth_count terminal events initial p hNonterminal hLegal
  split_ifs at h <;> omega

theorem root_count_has_zero_offset (terminal : List Action → Prop)
    (events : List (TreeEvaluation Action)) (hRoot : ¬ terminal [])
    (hLegal : LegalTreeRun terminal {[]} events) :
    backedCount events [] = (localActions events []).length := by
  have h := nonterminal_birth_count terminal events {[]} [] hRoot hLegal
  simp at h
  simpa [h] using parent_count_decomposition events []

def historyOf (action : ℕ → Action) (n : ℕ) : List Action := (List.range n).map action

theorem pullCount_historyOf (action : ℕ → Action) (a : Action) (n : ℕ) :
    AgentUCT.pullCount action a n = actionOccurrences (historyOf action n) a := by
  induction n with
  | zero => simp [AgentUCT.pullCount, actionOccurrences, historyOf]
  | succ n ih =>
    by_cases h : action n = a
    · simp [AgentUCT.pullCount, Finset.range_add_one, Finset.filter_insert,
        actionOccurrences, historyOf,
        List.range_succ, h] at ih ⊢
      exact ih
    · simp [AgentUCT.pullCount, Finset.range_add_one, Finset.filter_insert,
        actionOccurrences, historyOf,
        List.range_succ, h] at ih ⊢
      exact ih

/-- No auxiliary count process: any stream extending the projected history has the same counts. -/
theorem operational_child_visits_eq_pullCount (events : List (TreeEvaluation Action))
    (p : List Action) (a : Action) (action : ℕ → Action) (n : ℕ)
    (hHistory : localActions events p = historyOf action n) :
    (replayBackup events emptyStatistics (p ++ [a])).visits = AgentUCT.pullCount action a n := by
  rw [replayBackup_visits, pullCount_historyOf, ← hHistory, localActions_child_count]
  simp [emptyStatistics]

def extendHistory (history : List Action) (fallback : Action) (n : ℕ) : Action :=
  history[n]?.getD fallback

omit [DecidableEq Action] in
theorem historyOf_extendHistory_take (history : List Action) (fallback : Action)
    (n : ℕ) (hn : n ≤ history.length) :
    historyOf (extendHistory history fallback) n = history.take n := by
  apply List.ext_getElem
  · simp [historyOf, List.length_take, Nat.min_eq_left hn]
  · intro i hi hj
    have hin : i < n := by simpa [historyOf] using hi
    have hix : i < history.length := lt_of_lt_of_le hin hn
    simp [historyOf, extendHistory, List.getElem?_eq_getElem hix]

omit [DecidableEq Action] in
theorem historyOf_extendHistory (history : List Action) (fallback : Action) :
    historyOf (extendHistory history fallback) history.length = history := by
  simpa using historyOf_extendHistory_take history fallback history.length le_rfl

theorem localActions_prefix (before all : List (TreeEvaluation Action)) (p : List Action)
    (hPrefix : before <+: all) : localActions before p <+: localActions all p :=
  List.IsPrefix.filterMap (fun event : TreeEvaluation Action ↦ childAfter p event.expanded) hPrefix

/-- The local stream is constructed from this tree history, not supplied independently. -/
theorem local_history_before_global_prefix (events : List (TreeEvaluation Action))
    (p : List Action) (fallback : Action) (t : ℕ) :
    localActions (events.take t) p =
      historyOf (extendHistory (localActions events p) fallback)
        (localActions (events.take t) p).length := by
  have hp := localActions_prefix (events.take t) events p (List.take_prefix t events)
  rw [historyOf_extendHistory_take _ _ _ hp.length_le]
  exact List.prefix_iff_eq_take.mp hp

theorem child_visits_at_global_time (events : List (TreeEvaluation Action))
    (p : List Action) (a fallback : Action) (t : ℕ) :
    (replayBackup (events.take t) emptyStatistics (p ++ [a])).visits =
      AgentUCT.pullCount (extendHistory (localActions events p) fallback) a
        (localActions (events.take t) p).length :=
  operational_child_visits_eq_pullCount _ p a _ _
    (local_history_before_global_prefix events p fallback t)

omit [DecidableEq Action] in
theorem extendHistory_append_next (before after : List Action) (a fallback : Action) :
    extendHistory (before ++ a :: after) fallback before.length = a := by
  simp [extendHistory]

theorem local_chosen_action (before after : List (TreeEvaluation Action))
    (event : TreeEvaluation Action) (p : List Action) (a fallback : Action)
    (hChild : childAfter p event.expanded = some a) :
    extendHistory (localActions (before ++ event :: after) p) fallback
      (localActions before p).length = a := by
  simp [localActions, hChild, extendHistory]

theorem exists_backed_event_of_count_pos (events : List (TreeEvaluation Action))
    (p : List Action) (hCount : 0 < backedCount events p) :
    ∃ event ∈ events, p <+: event.expanded := by
  by_contra! hMiss
  have hZero : backedCount events p = 0 := by
    simpa [backedCount, List.filter_eq_nil_iff] using hMiss
  omega

theorem backed_node_in_replayTree (terminal : List Action → Prop)
    (events : List (TreeEvaluation Action)) (p : List Action)
    (hLegal : LegalTreeRun terminal {[]} events) (hCount : 0 < backedCount events p) :
    p ∈ replayTree events {[]} := by
  obtain ⟨event, he, hp⟩ := exists_backed_event_of_count_pos events p hCount
  exact replayTree_prefixClosed terminal events {[]} root_prefixClosed hLegal event.expanded
    ((replayTree_mem events {[]} event.expanded).mpr (Or.inr ⟨event, he, rfl⟩)) p hp

theorem visited_nonroot_birth_count_one (terminal : List Action → Prop)
    (events : List (TreeEvaluation Action)) (p : List Action)
    (hLegal : LegalTreeRun terminal {[]} events) (hNonterminal : ¬ terminal p)
    (hNonroot : p ≠ []) (hCount : 0 < backedCount events p) : birthCount events p = 1 := by
  have hNode := backed_node_in_replayTree terminal events p hLegal hCount
  obtain ⟨event, he, hp⟩ : ∃ event ∈ events, p = event.expanded := by
    have h := (replayTree_mem events {[]} p).mp hNode
    simpa [hNonroot] using h
  have hBirth : 0 < birthCount events p := by
    apply List.length_pos_iff.mpr
    intro hNil
    have hm : event ∈ events.filter (fun e ↦ decide (e.expanded = p)) := by
      simp [he, hp]
    simp [hNil] at hm
  have hUpper := nonterminal_birth_count terminal events {[]} p hNonterminal hLegal
  simp [hNonroot] at hUpper
  omega

/-- After a non-root internal node is born, the offset is exactly one, not a changing bias. -/
theorem visited_parent_count_exact_offset (terminal : List Action → Prop)
    (events : List (TreeEvaluation Action)) (p : List Action)
    (hLegal : LegalTreeRun terminal {[]} events) (hNonterminal : ¬ terminal p)
    (hCount : 0 < backedCount events p) :
    backedCount events p = (localActions events p).length + if p = [] then 0 else 1 := by
  by_cases hRoot : p = []
  · subst p
    simpa using root_count_has_zero_offset terminal events hNonterminal hLegal
  · rw [parent_count_decomposition,
      visited_nonroot_birth_count_one terminal events p hLegal hNonterminal hRoot hCount]
    simp [hRoot]

end AgentUCTPaper
