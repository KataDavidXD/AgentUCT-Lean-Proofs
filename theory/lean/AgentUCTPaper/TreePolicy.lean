import AgentUCTPaper.TreeTopology

/-! # The observed UCT decisions projected to a finite local action stream -/

set_option autoImplicit false

noncomputable section

namespace AgentUCTPaper

variable {Action : Type*} [DecidableEq Action]

omit [DecidableEq Action] in
theorem filterMap_step_exists {Item : Type*} (items : List Item) (f : Item → Option Action)
    (n : ℕ) (hn : n < (items.filterMap f).length) :
    ∃ before event after a, items = before ++ event :: after ∧
      (before.filterMap f).length = n ∧ f event = some a := by
  induction items generalizing n with
  | nil => simp at hn
  | cons event items ih =>
    cases h : f event with
    | none =>
      have ht : n < (items.filterMap f).length := by simpa [h] using hn
      obtain ⟨before, next, after, a, hs, ht, ha⟩ := ih n ht
      exact ⟨event :: before, next, after, a, by simp [hs], by simp [h, ht], ha⟩
    | some a =>
      cases n with
      | zero => exact ⟨[], event, items, a, by simp, by simp, h⟩
      | succ n =>
        have ht : n < (items.filterMap f).length := by simpa [h] using hn
        obtain ⟨before, next, after, b, hs, ht, hb⟩ := ih n ht
        exact ⟨event :: before, next, after, b, by simp [hs], by simp [h, ht], hb⟩

structure LocalStep (events : List (TreeEvaluation Action)) (p : List Action) (n : ℕ) where
  before : List (TreeEvaluation Action)
  event : TreeEvaluation Action
  after : List (TreeEvaluation Action)
  chosen : Action
  split : events = before ++ event :: after
  time : (localActions before p).length = n
  child : childAfter p event.expanded = some chosen

theorem localStep_nonempty (events : List (TreeEvaluation Action)) (p : List Action) (n : ℕ)
    (hn : n < (localActions events p).length) : Nonempty (LocalStep events p n) := by
  obtain ⟨before, event, after, a, hs, ht, ha⟩ :=
    filterMap_step_exists events (fun e ↦ childAfter p e.expanded) n hn
  exact ⟨⟨before, event, after, a, hs, ht, ha⟩⟩

def observedLocalStep (events : List (TreeEvaluation Action)) (p : List Action) (n : ℕ)
    (hn : n < (localActions events p).length) : LocalStep events p n :=
  Classical.choice (localStep_nonempty events p n hn)

def localBefore (events : List (TreeEvaluation Action)) (p : List Action) (n : ℕ) :
    List (TreeEvaluation Action) :=
  if hn : n < (localActions events p).length then (observedLocalStep events p n hn).before
  else events

theorem localBefore_prefix (events : List (TreeEvaluation Action)) (p : List Action) (n : ℕ) :
    localBefore events p n <+: events := by
  unfold localBefore
  split_ifs with hn
  · exact ⟨_, (observedLocalStep events p n hn).split.symm⟩
  · exact List.prefix_refl _

theorem localBefore_time (events : List (TreeEvaluation Action)) (p : List Action) (n : ℕ)
    (hn : n < (localActions events p).length) :
    (localActions (localBefore events p n) p).length = n := by
  simpa [localBefore, hn] using (observedLocalStep events p n hn).time

theorem localBefore_history (events : List (TreeEvaluation Action)) (p : List Action)
    (fallback : Action) (n : ℕ) (hn : n < (localActions events p).length) :
    localActions (localBefore events p n) p =
      historyOf (extendHistory (localActions events p) fallback) n := by
  have hp := localActions_prefix _ _ p (localBefore_prefix events p n)
  have ht := localBefore_time events p n hn
  rw [historyOf_extendHistory_take _ _ _ hn.le]
  simpa only [ht] using List.prefix_iff_eq_take.mp hp

theorem localBefore_child_count (events : List (TreeEvaluation Action)) (p : List Action)
    (a fallback : Action) (n : ℕ) (hn : n < (localActions events p).length) :
    (replayBackup (localBefore events p n) emptyStatistics (p ++ [a])).visits =
      AgentUCT.pullCount (extendHistory (localActions events p) fallback) a n :=
  operational_child_visits_eq_pullCount _ p a _ n
    (localBefore_history events p fallback n hn)

theorem legalTreeRun_append (terminal : List Action → Prop)
    (before after : List (TreeEvaluation Action)) (initial : Finset (List Action)) :
    LegalTreeRun terminal initial (before ++ after) ↔
      LegalTreeRun terminal initial before ∧
        LegalTreeRun terminal (replayTree before initial) after := by
  induction before generalizing initial with
  | nil => simp [LegalTreeRun, replayTree]
  | cons event before ih =>
    simp [LegalTreeRun, replayTree, ih, and_assoc]

theorem legalTreeRun_prefix (terminal : List Action → Prop)
    (before events : List (TreeEvaluation Action)) (initial : Finset (List Action))
    (hp : before <+: events) (hLegal : LegalTreeRun terminal initial events) :
    LegalTreeRun terminal initial before := by
  obtain ⟨after, rfl⟩ := hp
  exact (legalTreeRun_append terminal before after initial).mp hLegal |>.1

theorem localBefore_parent_count (terminals : Finset (List Action))
    (events : List (TreeEvaluation Action)) (p : List Action) (n : ℕ)
    (hLegal : LegalTreeRun (fun p ↦ p ∈ terminals) {[]} events)
    (hInternal : p ∉ terminals) (hPos : 0 < n) (hn : n < (localActions events p).length) :
    (replayBackup (localBefore events p n) emptyStatistics p).visits =
      n + if p = [] then 0 else 1 := by
  have hPrefix := legalTreeRun_prefix _ _ _ _ (localBefore_prefix events p n) hLegal
  have ht := localBefore_time events p n hn
  have hCount : 0 < backedCount (localBefore events p n) p := by
    rw [parent_count_decomposition, ht]
    omega
  simpa [replayBackup_visits, emptyStatistics, ht] using
    visited_parent_count_exact_offset _ _ p hPrefix hInternal hCount

omit [DecidableEq Action] in
theorem extendHistory_mem (arms : Finset Action) (history : List Action) (fallback : Action)
    (hHistory : ∀ a ∈ history, a ∈ arms) (hFallback : fallback ∈ arms) (n : ℕ) :
    extendHistory history fallback n ∈ arms := by
  unfold extendHistory
  cases h : history[n]? with
  | none => simpa [h] using hFallback
  | some a => simpa [h] using hHistory a (List.mem_of_getElem? h)

def restrictActions (arms : Finset Action) (action : ℕ → Action)
    (hAction : ∀ n, action n ∈ arms) : ℕ → ↥arms := fun n ↦ ⟨action n, hAction n⟩

theorem restrictActions_count (arms : Finset Action) (action : ℕ → Action)
    (hAction : ∀ n, action n ∈ arms) (a : ↥arms) (n : ℕ) :
    AgentUCT.pullCount (restrictActions arms action hAction) a n =
      AgentUCT.pullCount action a.val n := by
  unfold AgentUCT.pullCount
  congr 1
  ext t
  simp [restrictActions, Subtype.ext_iff]

/-- Exactly the selection conditions, with observed backup statistics and a predictable bill. -/
def TreeAllocationRule (terminals : Finset (List Action)) (c : ℝ)
    (penalty : List (TreeEvaluation Action) → List Action → Action → ℝ)
    (events : List (TreeEvaluation Action)) : Prop :=
  ∀ before event after, events = before ++ event :: after →
    ∀ p a, childAfter p event.expanded = some a →
      (∀ b ∈ availableChildren terminals p,
        (replayBackup before emptyStatistics (p ++ [b])).visits = 0 →
          (replayBackup before emptyStatistics (p ++ [a])).visits = 0) ∧
      ((∀ b ∈ availableChildren terminals p,
          0 < (replayBackup before emptyStatistics (p ++ [b])).visits) →
        ∀ b ∈ availableChildren terminals p,
          treeIndex (replayBackup before emptyStatistics (p ++ [b])).mean c
            (penalty before p b) (replayBackup before emptyStatistics p).visits
            (replayBackup before emptyStatistics (p ++ [b])).visits ≤
          treeIndex (replayBackup before emptyStatistics (p ++ [a])).mean c
            (penalty before p a) (replayBackup before emptyStatistics p).visits
            (replayBackup before emptyStatistics (p ++ [a])).visits)

theorem projected_unvisited_first (terminals : Finset (List Action)) (c : ℝ)
    (penalty : List (TreeEvaluation Action) → List Action → Action → ℝ)
    (events : List (TreeEvaluation Action)) (p : List Action) (fallback : Action)
    (hRule : TreeAllocationRule terminals c penalty events) (n : ℕ)
    (hn : n < (localActions events p).length) (b : Action)
    (hb : b ∈ availableChildren terminals p)
    (hZero : AgentUCT.pullCount (extendHistory (localActions events p) fallback) b n = 0) :
    AgentUCT.pullCount (extendHistory (localActions events p) fallback)
      (extendHistory (localActions events p) fallback n) n = 0 := by
  let step := observedLocalStep events p n hn
  have hChosen : extendHistory (localActions events p) fallback n = step.chosen := by
    have hs := local_chosen_action step.before step.after step.event p
      step.chosen fallback step.child
    simpa only [step.time, ← step.split] using hs
  have hBefore : localBefore events p n = step.before := by simp [localBefore, hn, step]
  have hCounts := localBefore_child_count events p b fallback n hn
  rw [hBefore, hZero] at hCounts
  have hDecision := (hRule step.before step.event step.after step.split
    p step.chosen step.child).1 b hb hCounts
  rw [← hChosen, ← hBefore, localBefore_child_count events p _ fallback n hn] at hDecision
  exact hDecision

theorem projected_index_max (terminals : Finset (List Action)) (c : ℝ)
    (penalty : List (TreeEvaluation Action) → List Action → Action → ℝ)
    (events : List (TreeEvaluation Action)) (p : List Action) (fallback : Action)
    (hRule : TreeAllocationRule terminals c penalty events)
    (hLegal : LegalTreeRun (fun p ↦ p ∈ terminals) {[]} events)
    (hInternal : p ∉ terminals) (n : ℕ) (hPos : 0 < n)
    (hn : n < (localActions events p).length)
    (hInitialized : ∀ a ∈ availableChildren terminals p,
      0 < AgentUCT.pullCount (extendHistory (localActions events p) fallback) a n)
    (b : Action) (hb : b ∈ availableChildren terminals p) :
    let action := extendHistory (localActions events p) fallback
    let before := localBefore events p n
    treeIndex (replayBackup before emptyStatistics (p ++ [b])).mean c (penalty before p b)
      (n + if p = [] then 0 else 1) (AgentUCT.pullCount action b n) ≤
    treeIndex (replayBackup before emptyStatistics (p ++ [action n])).mean c
      (penalty before p (action n)) (n + if p = [] then 0 else 1)
      (AgentUCT.pullCount action (action n) n) := by
  dsimp only
  let step := observedLocalStep events p n hn
  have hChosen : extendHistory (localActions events p) fallback n = step.chosen := by
    have hs := local_chosen_action step.before step.after step.event p
      step.chosen fallback step.child
    simpa only [step.time, ← step.split] using hs
  have hBefore : localBefore events p n = step.before := by simp [localBefore, hn, step]
  have hInit : ∀ a ∈ availableChildren terminals p,
      0 < (replayBackup step.before emptyStatistics (p ++ [a])).visits := by
    intro a ha
    rw [← hBefore, localBefore_child_count events p a fallback n hn]
    exact hInitialized a ha
  have hDecision := (hRule step.before step.event step.after step.split
    p step.chosen step.child).2 hInit b hb
  rw [← hChosen, ← hBefore,
    localBefore_parent_count terminals events p n hLegal hInternal hPos hn,
    localBefore_child_count events p b fallback n hn,
    localBefore_child_count events p _ fallback n hn] at hDecision
  exact hDecision

end AgentUCTPaper
