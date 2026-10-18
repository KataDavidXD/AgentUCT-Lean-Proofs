import NativeGeneratedAllocation



set_option autoImplicit false
set_option maxRecDepth 8192
set_option maxHeartbeats 4000000
set_option linter.constructorNameAsVariable false
noncomputable section
namespace AgentUCTPanelAllocation
open AgentUCTNativeRefinement AgentUCTNativeRepair AgentUCTPaper

theorem expanded_nodes_append (before : List (TreeEvaluation Act)) (event : TreeEvaluation Act) :
    expandedNodes (before++[event]) = insert event.expanded (expandedNodes before) := by
  ext p
  simp only [expandedNodes,Finset.mem_insert,List.mem_toFinset,List.map_append,List.mem_append,
    List.map_cons,List.map_nil,List.mem_singleton]
  tauto

def FreshRoots (roots : List (Fin 8)) (before : List (TreeEvaluation Act)) : Prop :=
  ∀ q ∈ roots, [.query q] ∉ expandedNodes before

theorem initial_event_legal_tree (tape : SharedTape) (ht : LegalSupportedTape tape)
    (reward : List Act → ℝ) (before : List (TreeEvaluation Act)) (q : Fin 8)
    (hfresh : [.query q] ∉ expandedNodes before) :
    LegalTreeEvent Terminal (replayTree before {[]}) (initialEvent tape reward before q) := by
  refine ⟨(initial_event_valid tape ht reward before q).2,Or.inr ⟨[],?_,.query q,rfl,?_⟩⟩
  · rw [← expanded_nodes_eq_replay_tree]; simp [expandedNodes]
  · simpa only [← expanded_nodes_eq_replay_tree] using hfresh

theorem initial_event_allocation (tape : SharedTape) (c : ℝ)
    (penalty : List (TreeEvaluation Act) → List Act → Act → ℝ)
    (reward : List Act → ℝ) (before : List (TreeEvaluation Act))
    (hrun : LegalTreeRun Terminal {[]} before) (q : Fin 8)
    (hfresh : [.query q] ∉ expandedNodes before) :
    EventAllocation c penalty before (initialEvent tape reward before q) := by
  intro p a hchild
  have hpre := (childAfter_some_iff p [.query q] a).mp hchild
  have hlen := hpre.length_le
  simp only [List.length_cons,List.length_nil,List.length_append] at hlen
  have hp : p = [] := List.length_eq_zero.mp (by omega)
  subst p
  have ha : a = .query q := Option.some.inj (hchild.symm.trans
    ((childAfter_some_iff ([] : List Act) [Act.query q] (Act.query q)).mpr (List.prefix_refl _)))
  subst a
  exact newly_expanded_child_local_allocation c penalty before hrun [] legal_nil (.query q)
    (by rw [ordered_legal_member_iff legal_nil]; simp [available,rootOrder]) hfresh

theorem fresh_roots_after_initial (tape : SharedTape) (reward : List Act → ℝ)
    (before : List (TreeEvaluation Act)) (q : Fin 8) (roots : List (Fin 8))
    (hnodup : (q::roots).Nodup) (hfresh : FreshRoots (q::roots) before) :
    FreshRoots roots (before++[initialEvent tape reward before q]) := by
  intro r hr
  rw [expanded_nodes_append]
  simp only [Finset.mem_insert,not_or]
  constructor
  · intro he
    have hrq : r = q := by simpa only [initialEvent,List.cons.injEq,Act.query.injEq,and_true] using he
    exact (List.nodup_cons.mp hnodup).1 (hrq ▸ hr)
  · exact hfresh r (List.mem_cons_of_mem _ hr)

theorem initialize_from_legal_and_allocation (tape : SharedTape) (ht : LegalSupportedTape tape)
    (c : ℝ) (penalty : List (TreeEvaluation Act) → List Act → Act → ℝ)
    (reward : List Act → ℝ) (roots : List (Fin 8)) (before : List (TreeEvaluation Act))
    (hnodup : roots.Nodup) (hfresh : FreshRoots roots before)
    (hb : LegalTreeRun Terminal {[]} before) (ha : TreeAllocationRule nativeTerminals c penalty before) :
    LegalTreeRun Terminal {[]} (initializeFrom tape reward roots before) ∧
      TreeAllocationRule nativeTerminals c penalty (initializeFrom tape reward roots before) := by
  induction roots generalizing before with
  | nil => exact ⟨hb,ha⟩
  | cons q roots ih =>
      apply ih _ (List.nodup_cons.mp hnodup).2
        (fresh_roots_after_initial tape reward before q roots hnodup hfresh)
      · rw [legalTreeRun_append]
        exact ⟨hb,initial_event_legal_tree tape ht reward before q (hfresh q (by simp)),trivial⟩
      · exact allocation_append_one c penalty before _ ha
          (initial_event_allocation tape c penalty reward before hb q (hfresh q (by simp)))

theorem native_common_initialization_legal_and_allocation (tape : SharedTape)
    (ht : LegalSupportedTape tape) (c : ℝ)
    (penalty : List (TreeEvaluation Act) → List Act → Act → ℝ) (reward : List Act → ℝ) :
    LegalTreeRun Terminal {[]} (repairedInitialization tape reward) ∧
      TreeAllocationRule nativeTerminals c penalty (repairedInitialization tape reward) := by
  apply initialize_from_legal_and_allocation tape ht c penalty reward (List.finRange 8) []
  · exact List.nodup_finRange 8
  · intro q hq; simp [expandedNodes]
  · trivial
  · intro before event after hsplit
    have hlen := congrArg List.length hsplit
    simp only [List.length_nil,List.length_append,List.length_cons] at hlen
    omega

def nativeGenerate (tape : SharedTape) (c : ℝ)
    (penalty : List (TreeEvaluation Act) → List Act → Act → ℝ)
    (actualBill : List (TreeEvaluation Act) → ℝ) (B : ℝ) (reward : List Act → ℝ)
    (cap : ℕ) : List (TreeEvaluation Act) :=
  nativeAfter tape c penalty actualBill B reward (cap-8) (repairedInitialization tape reward)

theorem native_generated_legal_tree (tape : SharedTape) (ht : LegalSupportedTape tape) (c : ℝ)
    (penalty : List (TreeEvaluation Act) → List Act → Act → ℝ)
    (actualBill : List (TreeEvaluation Act) → ℝ) (B : ℝ) (reward : List Act → ℝ) (cap : ℕ) :
    LegalTreeRun Terminal {[]} (nativeGenerate tape c penalty actualBill B reward cap) :=
  native_after_legal_tree tape ht c penalty actualBill B reward _ _
    (native_common_initialization_legal_and_allocation tape ht c penalty reward).1

theorem native_generated_tree_allocation_rule (tape : SharedTape) (ht : LegalSupportedTape tape)
    (c : ℝ) (penalty : List (TreeEvaluation Act) → List Act → Act → ℝ)
    (actualBill : List (TreeEvaluation Act) → ℝ) (B : ℝ) (reward : List Act → ℝ) (cap : ℕ) :
    TreeAllocationRule nativeTerminals c penalty (nativeGenerate tape c penalty actualBill B reward cap) :=
  native_after_allocation tape ht c penalty actualBill B reward _ _
    (native_common_initialization_legal_and_allocation tape ht c penalty reward).1
    (native_common_initialization_legal_and_allocation tape ht c penalty reward).2

end AgentUCTPanelAllocation
