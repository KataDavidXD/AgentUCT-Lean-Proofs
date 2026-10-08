import AgentUCTPaper.TreePolicy
import AgentUCTPaper.TreeWindow

/-! # Exploration derived from the actual finite tree run -/

set_option autoImplicit false

noncomputable section

namespace AgentUCTPaper

variable {Action : Type*} [DecidableEq Action]

structure BoundedTreeRun (terminals : Finset (List Action)) (c H : ℝ)
    (penalty : List (TreeEvaluation Action) → List Action → Action → ℝ)
    (events : List (TreeEvaluation Action)) : Prop where
  terminal : ∀ event ∈ events, event.terminal ∈ terminals
  reward : ∀ event ∈ events, 0 ≤ event.reward ∧ event.reward ≤ 1
  legal : LegalTreeRun (fun p ↦ p ∈ terminals) {[]} events
  rule : TreeAllocationRule terminals c penalty events
  penalty_bounded : ∀ before, before <+: events → ∀ p, ∀ a ∈ availableChildren terminals p,
    0 ≤ penalty before p a ∧ penalty before p a ≤ H

theorem treeAllocationRule_prefix (terminals : Finset (List Action)) (c : ℝ)
    (penalty : List (TreeEvaluation Action) → List Action → Action → ℝ)
    (before events : List (TreeEvaluation Action)) (hp : before <+: events)
    (hRule : TreeAllocationRule terminals c penalty events) :
    TreeAllocationRule terminals c penalty before := by
  obtain ⟨tail, rfl⟩ := hp
  intro past event after hs p a ha
  apply hRule past event (after ++ tail) _ p a ha
  simp [hs, List.append_assoc]

theorem BoundedTreeRun.prefix {terminals : Finset (List Action)} {c H : ℝ}
    {penalty : List (TreeEvaluation Action) → List Action → Action → ℝ}
    {events before : List (TreeEvaluation Action)}
    (run : BoundedTreeRun terminals c H penalty events) (hp : before <+: events) :
    BoundedTreeRun terminals c H penalty before where
  terminal e he := run.terminal e (hp.subset he)
  reward e he := run.reward e (hp.subset he)
  legal := legalTreeRun_prefix _ _ _ _ hp run.legal
  rule := treeAllocationRule_prefix terminals c penalty before events hp run.rule
  penalty_bounded past ht := run.penalty_bounded past (ht.trans hp)

def legalLocalStream (terminals : Finset (List Action))
    (events : List (TreeEvaluation Action)) (p : List Action) (fallback : ChildArm terminals p)
    (hTerminal : ∀ event ∈ events, event.terminal ∈ terminals) : ℕ → ChildArm terminals p :=
  restrictActions (availableChildren terminals p)
    (extendHistory (localActions events p) fallback.val)
    (extendHistory_mem _ _ _ (projected_action_is_legal terminals events hTerminal p)
      fallback.property)

theorem legalLocalStream_count (terminals : Finset (List Action))
    (events : List (TreeEvaluation Action)) (p : List Action) (fallback : ChildArm terminals p)
    (hTerminal : ∀ event ∈ events, event.terminal ∈ terminals)
    (a : ChildArm terminals p) (n : ℕ) :
    AgentUCT.pullCount (legalLocalStream terminals events p fallback hTerminal) a n =
      AgentUCT.pullCount (extendHistory (localActions events p) fallback.val) a.val n :=
  restrictActions_count _ _ _ a n

theorem operational_local_initialized (terminals : Finset (List Action)) (c H : ℝ)
    (penalty : List (TreeEvaluation Action) → List Action → Action → ℝ)
    (events : List (TreeEvaluation Action)) (run : BoundedTreeRun terminals c H penalty events)
    (p : List Action) (fallback : ChildArm terminals p)
    (hEnough : Fintype.card (ChildArm terminals p) ≤ (localActions events p).length) :
    ∀ a, 0 < AgentUCT.pullCount (legalLocalStream terminals events p fallback run.terminal)
      a (Fintype.card (ChildArm terminals p)) := by
  apply initialized_after_unvisited_first
  intro t ht a ha
  rw [legalLocalStream_count] at ha ⊢
  exact projected_unvisited_first terminals c penalty events p fallback.val run.rule t
    (ht.trans_le hEnough) a.val a.property ha

/-- This is an actual child-visitation theorem, not an independently assumed bandit process. -/
theorem actual_children_explored (terminals : Finset (List Action)) (c H : ℝ)
    (penalty : List (TreeEvaluation Action) → List Action → Action → ℝ)
    (events : List (TreeEvaluation Action)) (run : BoundedTreeRun terminals c H penalty events)
    (hc : 0 < c) (hH : 0 ≤ H) (p : List Action) (hInternal : p ∉ terminals)
    (m : ℕ) (hEnough : 2 * explorationWindowStart c H
      (Fintype.card (ChildArm terminals p)) m ≤ (localActions events p).length)
    (a : Action) (ha : a ∈ availableChildren terminals p) :
    m < backedCount events (p ++ [a]) := by
  let fallback : ChildArm terminals p := ⟨a, ha⟩
  let action := legalLocalStream terminals events p fallback run.terminal
  let horizon := (localActions events p).length
  let K := Fintype.card (ChildArm terminals p)
  let q : ℕ → ChildArm terminals p → ℝ := fun n b ↦
    (replayBackup (localBefore events p n) emptyStatistics (p ++ [b.val])).mean
  let costs : ℕ → ChildArm terminals p → ℝ := fun n b ↦ penalty (localBefore events p n) p b.val
  have hKPos : 0 < K := Fintype.card_pos_iff.mpr ⟨fallback⟩
  have hKEnough : K ≤ horizon := by
    have h := (explorationWindow_bounds c H K m).1
    have hKL : K ≤ explorationWindowStart c H K m := by
      have hr : (K : ℝ) ≤ explorationWindowStart c H K m := by linarith
      exact_mod_cast hr
    change 2 * explorationWindowStart c H K m ≤ horizon at hEnough
    omega
  have hInit := operational_local_initialized terminals c H penalty events run p fallback hKEnough
  have hResult := finite_explicit_window_explores action q costs c H
    (if p = [] then 0 else 1) m horizon fallback hc hH (by split_ifs <;> omega) hEnough hInit
    (by
      intro t ht b
      exact replayBackup_mean_mem_unit _
        (fun e he ↦ run.reward e ((localBefore_prefix events p t).subset he)) _)
    (by
      intro t ht b
      exact run.penalty_bounded _ (localBefore_prefix events p t) p b.val b.property)
    (by
      intro t ht hKt b
      have hCounts : ∀ b ∈ availableChildren terminals p,
          0 < AgentUCT.pullCount (extendHistory (localActions events p) fallback.val) b t := by
        intro b hb
        have hi := (hInit ⟨b, hb⟩).trans_le (pullCount_monotone action ⟨b, hb⟩ hKt)
        simpa only [action, legalLocalStream_count] using hi
      have hMax := projected_index_max terminals c penalty events p fallback.val run.rule
        run.legal hInternal t (lt_of_lt_of_le hKPos hKt) ht hCounts b.val b.property
      simpa only [action, q, costs, legalLocalStream_count] using hMax)
  have hCount : AgentUCT.pullCount action fallback horizon = backedCount events (p ++ [a]) := by
    rw [legalLocalStream_count, pullCount_historyOf, historyOf_extendHistory]
    exact localActions_child_count events p a
  rwa [hCount] at hResult

end AgentUCTPaper
