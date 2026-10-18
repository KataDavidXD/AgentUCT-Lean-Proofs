import NativeSelectionRun



set_option autoImplicit false
set_option maxRecDepth 8192
set_option maxHeartbeats 4000000
set_option linter.constructorNameAsVariable false
noncomputable section
namespace AgentUCTPanelAllocation
open AgentUCTNativeRefinement AgentUCTNativeRepair AgentUCTPaper

def EventAllocation (c : ℝ) (penalty : List (TreeEvaluation Act) → List Act → Act → ℝ)
    (before : List (TreeEvaluation Act)) (event : TreeEvaluation Act) : Prop :=
  ∀ p a, childAfter p event.expanded = some a → LocalAllocation c penalty before p a

theorem allocation_append_one (c : ℝ)
    (penalty : List (TreeEvaluation Act) → List Act → Act → ℝ)
    (before : List (TreeEvaluation Act)) (event : TreeEvaluation Act)
    (hbefore : TreeAllocationRule nativeTerminals c penalty before)
    (hevent : EventAllocation c penalty before event) :
    TreeAllocationRule nativeTerminals c penalty (before++[event]) := by
  intro pre e after hsplit p a hchild
  have hcases := List.append_eq_append_iff.mp hsplit
  rcases hcases with ⟨rest,hpre,hrest⟩ | ⟨rest,hb,hrest⟩
  · have hlen := congrArg List.length hrest
    simp only [List.length_cons,List.length_nil,List.length_append] at hlen
    have hr : rest = [] := List.length_eq_zero.mp (by omega)
    have ha : after = [] := List.length_eq_zero.mp (by omega)
    subst rest; subst after
    simp only [List.append_nil] at hpre
    subst pre
    have he : event = e := List.cons.inj hrest |>.1
    subst e
    exact hevent p a hchild
  · cases rest with
    | nil =>
        simp only [List.append_nil] at hb
        subst before
        have he : e = event := List.cons.inj hrest |>.1
        subst e
        exact hevent p a hchild
    | cons x rest =>
        simp only [List.cons_append] at hrest
        have he : e = x := List.cons.inj hrest |>.1
        subst x
        exact hbefore pre e rest hb p a hchild

def nativeEvent (tape : SharedTape) (c : ℝ)
    (penalty : List (TreeEvaluation Act) → List Act → Act → ℝ)
    (reward : List Act → ℝ) (before : List (TreeEvaluation Act)) : TreeEvaluation Act :=
  let expanded := nativeSelect tape c penalty before 9 []
  let terminal := repairedRollout tape before 9 expanded
  ⟨expanded,terminal,reward terminal,0,repaired_rollout_prefix tape before 9 expanded⟩

theorem native_event_valid (tape : SharedTape) (ht : LegalSupportedTape tape) (c : ℝ)
    (penalty : List (TreeEvaluation Act) → List Act → Act → ℝ)
    (reward : List Act → ℝ) (before : List (TreeEvaluation Act)) :
    ValidEvent (nativeEvent tape c penalty reward before) := by
  have hl := native_select_legal tape ht c penalty before 9 [] legal_nil
  exact ⟨hl,repaired_rollout_terminal tape ht before 9 _ hl (by omega)⟩

theorem native_event_legal_tree (tape : SharedTape) (ht : LegalSupportedTape tape) (c : ℝ)
    (penalty : List (TreeEvaluation Act) → List Act → Act → ℝ)
    (reward : List Act → ℝ) (before : List (TreeEvaluation Act)) :
    LegalTreeEvent Terminal (replayTree before {[]}) (nativeEvent tape c penalty reward before) := by
  refine ⟨(native_event_valid tape ht c penalty reward before).2,?_⟩
  change InsertOutcome (replayTree before {[]}) (nativeSelect tape c penalty before 9 [])
  rw [← expanded_nodes_eq_replay_tree]
  exact native_select_insert_outcome tape ht c penalty before 9 [] legal_nil
    (by simp [expandedNodes]) (by simp)

theorem native_event_allocation (tape : SharedTape) (ht : LegalSupportedTape tape) (c : ℝ)
    (penalty : List (TreeEvaluation Act) → List Act → Act → ℝ)
    (reward : List Act → ℝ) (before : List (TreeEvaluation Act))
    (hrun : LegalTreeRun Terminal {[]} before) :
    EventAllocation c penalty before (nativeEvent tape c penalty reward before) := by
  intro p a hchild
  exact native_select_local_decisions tape ht c penalty before hrun 9 [] legal_nil p a
    List.nil_prefix hchild

def nativeAfter (tape : SharedTape) (c : ℝ)
    (penalty : List (TreeEvaluation Act) → List Act → Act → ℝ)
    (actualBill : List (TreeEvaluation Act) → ℝ) (B : ℝ) (reward : List Act → ℝ) :
    ℕ → List (TreeEvaluation Act) → List (TreeEvaluation Act)
  | 0,before => before
  | fuel+1,before => if targetReached (actualBill before) B then before else
      nativeAfter tape c penalty actualBill B reward fuel (before++[nativeEvent tape c penalty reward before])

theorem native_after_legal_tree (tape : SharedTape) (ht : LegalSupportedTape tape) (c : ℝ)
    (penalty : List (TreeEvaluation Act) → List Act → Act → ℝ)
    (actualBill : List (TreeEvaluation Act) → ℝ) (B : ℝ) (reward : List Act → ℝ)
    (fuel : ℕ) (before : List (TreeEvaluation Act)) (hb : LegalTreeRun Terminal {[]} before) :
    LegalTreeRun Terminal {[]} (nativeAfter tape c penalty actualBill B reward fuel before) := by
  induction fuel generalizing before with
  | zero => exact hb
  | succ fuel ih =>
      simp only [nativeAfter]
      split_ifs
      · exact hb
      · apply ih
        rw [legalTreeRun_append]
        exact ⟨hb,native_event_legal_tree tape ht c penalty reward before,trivial⟩

theorem native_after_allocation (tape : SharedTape) (ht : LegalSupportedTape tape) (c : ℝ)
    (penalty : List (TreeEvaluation Act) → List Act → Act → ℝ)
    (actualBill : List (TreeEvaluation Act) → ℝ) (B : ℝ) (reward : List Act → ℝ)
    (fuel : ℕ) (before : List (TreeEvaluation Act)) (hb : LegalTreeRun Terminal {[]} before)
    (ha : TreeAllocationRule nativeTerminals c penalty before) :
    TreeAllocationRule nativeTerminals c penalty (nativeAfter tape c penalty actualBill B reward fuel before) := by
  induction fuel generalizing before with
  | zero => exact ha
  | succ fuel ih =>
      simp only [nativeAfter]
      split_ifs
      · exact ha
      · apply ih
        · rw [legalTreeRun_append]
          exact ⟨hb,native_event_legal_tree tape ht c penalty reward before,trivial⟩
        · exact allocation_append_one c penalty before _ ha
            (native_event_allocation tape ht c penalty reward before hb)

end AgentUCTPanelAllocation
