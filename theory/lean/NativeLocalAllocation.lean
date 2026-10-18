import NativeTerminalTopology



set_option autoImplicit false
set_option maxRecDepth 8192
set_option maxHeartbeats 4000000


set_option linter.constructorNameAsVariable false
noncomputable section
namespace AgentUCTPanelAllocation
open AgentUCTNativeRefinement AgentUCTNativeRepair AgentUCTPaper

def rawVisits (before : List (TreeEvaluation Act)) (p : List Act) : ℕ :=
  (replayBackup before emptyStatistics p).visits

def nativeFirstChoice (score : Act → ℝ) (before : List (TreeEvaluation Act))
    (p : List Act) : Act :=
  match (orderedLegalAvailable p).filter (fun a => rawVisits before (p++[a]) = 0) with
  | [] => firstMaximum score (orderedLegalAvailable p)
  | a::_ => a

theorem native_first_choice_eq_repaired (mode : ForecastMode) (tape : SharedTape)
    (prices : Unit × List Act → ℝ) (c gamma : ℝ) (before : List (TreeEvaluation Act))
    (p : List Act) :
    nativeFirstChoice (nodeScore mode tape prices c gamma before p) before p =
      repairedVisitedChoice mode tape prices c gamma before p := by
  dsimp only [nativeFirstChoice,repairedVisitedChoice,rawVisits]
  cases hf : (orderedLegalAvailable p).filter
    (fun a => (replayBackup before emptyStatistics (p++[a])).visits = 0) <;> rfl

theorem native_first_choice_member (score : Act → ℝ) (before : List (TreeEvaluation Act))
    (p : List Act) (hne : orderedLegalAvailable p ≠ []) :
    nativeFirstChoice score before p ∈ orderedLegalAvailable p := by
  unfold nativeFirstChoice
  cases hf : (orderedLegalAvailable p).filter (fun a => rawVisits before (p++[a]) = 0) with
  | nil => exact firstMaximum_member _ _ hne
  | cons a rest =>
      have ha : a ∈ (orderedLegalAvailable p).filter (fun a => rawVisits before (p++[a]) = 0) := by
        rw [hf]; simp
      exact (List.mem_filter.mp ha).1

theorem native_first_choice_unvisited (score : Act → ℝ) (before : List (TreeEvaluation Act))
    (p : List Act) (b : Act) (hb : b ∈ orderedLegalAvailable p)
    (hzero : rawVisits before (p++[b]) = 0) :
    rawVisits before (p++[nativeFirstChoice score before p]) = 0 := by
  unfold nativeFirstChoice
  cases hf : (orderedLegalAvailable p).filter (fun a => rawVisits before (p++[a]) = 0) with
  | nil =>
      have hb' : b ∈ (orderedLegalAvailable p).filter (fun a => rawVisits before (p++[a]) = 0) := by
        simp [hb,hzero]
      rw [hf] at hb'
      exact False.elim (List.not_mem_nil hb')
  | cons a rest =>
      have ha : a ∈ (orderedLegalAvailable p).filter (fun a => rawVisits before (p++[a]) = 0) := by
        rw [hf]; simp
      simpa using (List.mem_filter.mp ha).2

theorem native_first_choice_all_visited (score : Act → ℝ)
    (before : List (TreeEvaluation Act)) (p : List Act)
    (hpos : ∀ b ∈ orderedLegalAvailable p, 0 < rawVisits before (p++[b])) :
    nativeFirstChoice score before p = firstMaximum score (orderedLegalAvailable p) := by
  have hf : (orderedLegalAvailable p).filter (fun a => rawVisits before (p++[a]) = 0) = [] := by
    apply List.eq_nil_iff_forall_not_mem.mpr
    intro b hb
    have hz : rawVisits before (p++[b]) = 0 := by simpa using (List.mem_filter.mp hb).2
    have hp := hpos b (List.mem_filter.mp hb).1
    omega
  simp [nativeFirstChoice,hf]

theorem native_first_choice_first_ordered_max (score : Act → ℝ)
    (before : List (TreeEvaluation Act)) (p : List Act)
    (hne : orderedLegalAvailable p ≠ [])
    (hpos : ∀ b ∈ orderedLegalAvailable p, 0 < rawVisits before (p++[b])) :
    FirstOrderedMax score (orderedLegalAvailable p) (nativeFirstChoice score before p) := by
  rw [native_first_choice_all_visited score before p hpos]
  exact firstMaximum_first_ordered_max score _ hne

def indexScore (c : ℝ) (penalty : List (TreeEvaluation Act) → List Act → Act → ℝ)
    (before : List (TreeEvaluation Act)) (p : List Act) (a : Act) : ℝ :=
  treeIndex (replayBackup before emptyStatistics (p++[a])).mean c
    (penalty before p a) (rawVisits before p) (rawVisits before (p++[a]))

def LocalAllocation (c : ℝ) (penalty : List (TreeEvaluation Act) → List Act → Act → ℝ)
    (before : List (TreeEvaluation Act)) (p : List Act) (a : Act) : Prop :=
  (∀ b ∈ availableChildren nativeTerminals p, rawVisits before (p++[b]) = 0 →
    rawVisits before (p++[a]) = 0) ∧
  ((∀ b ∈ availableChildren nativeTerminals p, 0 < rawVisits before (p++[b])) →
    ∀ b ∈ availableChildren nativeTerminals p,
      indexScore c penalty before p b ≤ indexScore c penalty before p a)

theorem native_first_choice_local_allocation (c : ℝ)
    (penalty : List (TreeEvaluation Act) → List Act → Act → ℝ)
    (before : List (TreeEvaluation Act)) (p : List Act) (hp : Legal p)
    (hne : orderedLegalAvailable p ≠ []) :
    LocalAllocation c penalty before p
      (nativeFirstChoice (indexScore c penalty before p) before p) := by
  unfold LocalAllocation
  rw [native_available_children_eq hp]
  constructor
  · intro b hb hz
    exact native_first_choice_unvisited _ before p b (List.mem_toFinset.mp hb) hz
  · intro hpos b hb
    have hpl : ∀ b ∈ orderedLegalAvailable p, 0 < rawVisits before (p++[b]) :=
      fun b hb => hpos b (List.mem_toFinset.mpr hb)
    rw [native_first_choice_all_visited _ before p hpl]
    exact firstMaximum_max _ _ hne b (List.mem_toFinset.mp hb)

theorem expanded_nodes_eq_replay_tree (before : List (TreeEvaluation Act)) :
    expandedNodes before = replayTree before {[]} := by
  ext p
  simp only [expandedNodes,Finset.mem_insert,List.mem_toFinset,List.mem_map,replayTree_mem,
    Finset.mem_singleton]
  aesop

theorem newly_expanded_child_local_allocation (c : ℝ)
    (penalty : List (TreeEvaluation Act) → List Act → Act → ℝ)
    (before : List (TreeEvaluation Act))
    (hrun : LegalTreeRun Terminal {[]} before) (p : List Act) (hp : Legal p)
    (a : Act) (ha : a ∈ orderedLegalAvailable p) (hnew : p++[a] ∉ expandedNodes before) :
    LocalAllocation c penalty before p a := by
  have hz : rawVisits before (p++[a]) = 0 := by
    exact (replayBackup_nonnode_zero Terminal before _ hrun
      (by simpa only [← expanded_nodes_eq_replay_tree] using hnew)).1
  constructor
  · intro b hb hbzero
    exact hz
  · intro hpos
    have hpzero := hpos a (by rw [native_available_children_eq hp]; exact List.mem_toFinset.mpr ha)
    omega

end AgentUCTPanelAllocation
