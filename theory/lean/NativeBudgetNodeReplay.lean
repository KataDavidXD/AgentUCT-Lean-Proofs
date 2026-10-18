import NativeMarginFeasibility



set_option autoImplicit false
set_option maxRecDepth 16384
set_option maxHeartbeats 4000000
set_option linter.constructorNameAsVariable false
noncomputable section
namespace AgentUCTNativeBudget
open AgentUCTPanelAllocation AgentUCTNativeRepair AgentUCTNativeRefinement AgentUCTPaper

def initialNodes : Finset (List Act) := insert [] (Finset.univ.image fun q : Fin 8 => [.query q])
def a9Nodes := insert [.query hyde,.hydeRetriever 1] initialNodes
def a10Nodes := insert [.query hyde,.hydeRetriever 0] a9Nodes
def b9Nodes := insert [.query branchB,.normalRetriever 1] initialNodes

theorem initialization_nodes_exact (reward : List Act → ℝ) : expandedNodes (initialization reward) = initialNodes := by
  ext p
  simp [expandedNodes,initialization,seedEvent,initialNodes]

theorem a9_nodes_exact (reward : List Act → ℝ) : expandedNodes (aNine reward) = a9Nodes := by
  rw [aNine,expanded_nodes_append,initialization_nodes_exact]
  rfl

theorem a10_nodes_exact (reward : List Act → ℝ) : expandedNodes (aTen reward) = a10Nodes := by
  rw [aTen,expanded_nodes_append,a9_nodes_exact]
  rfl

theorem b9_nodes_exact (reward : List Act → ℝ) : expandedNodes (bNine reward) = b9Nodes := by
  rw [bNine,expanded_nodes_append,initialization_nodes_exact]
  rfl

theorem roots_in_initial_nodes (q : Fin 8) : [.query q] ∈ initialNodes := by simp [initialNodes]

theorem initialized_root_filter_empty (before : List (TreeEvaluation Act))
    (hp : ∀ q : Fin 8,[.query q] ∈ expandedNodes before) :
    ((orderedLegalAvailable []).filter fun a => ([]++[a]) ∉ expandedNodes before) = [] := by
  apply List.eq_nil_iff_forall_not_mem.mpr
  intro a ha
  have hh := List.mem_filter.mp ha
  rw [ordered_legal_root_order] at hh
  obtain ⟨q,hq,rfl⟩ := List.mem_map.mp hh.1
  have hn : [.query q] ∉ expandedNodes before := by simpa using hh.2
  exact hn (hp q)

theorem initialized_root_selection_recursion (tape : SharedTape) (before : List (TreeEvaluation Act))
    (hp : ∀ q : Fin 8,[.query q] ∈ expandedNodes before) (c : ℝ)
    (penalty : List (TreeEvaluation Act) → List Act → Act → ℝ) (fuel : ℕ) :
    nativeSelect tape c penalty before (fuel+1) [] = nativeSelect tape c penalty before fuel
      [nativeFirstChoice (indexScore c penalty before []) before []] := by
  have hf : ((orderedLegalAvailable []).filter fun a => [a] ∉ expandedNodes before) = [] := by
    simpa only [List.nil_append] using initialized_root_filter_empty before hp
  simp only [nativeSelect,if_neg (show orderedLegalAvailable [] ≠ [] by decide),
    List.nil_append,hf,ite_true]

def unexpandedAt (nodes : Finset (List Act)) (p : List Act) : List Act :=
  (orderedLegalAvailable p).filter fun a => p++[a] ∉ nodes

theorem initial_A_unexpanded : unexpandedAt initialNodes [.query hyde] =
    [.hydeRetriever 1,.hydeRetriever 0,.hydeRetriever 2] := by decide
theorem after_a9_A_unexpanded : unexpandedAt a9Nodes [.query hyde] = [.hydeRetriever 0,.hydeRetriever 2] := by decide
theorem after_a10_A_unexpanded : unexpandedAt a10Nodes [.query hyde] = [.hydeRetriever 2] := by decide
theorem initial_B_unexpanded : unexpandedAt initialNodes [.query branchB] = orderedLegalAvailable [.query branchB] := by decide
theorem after_b9_A_unexpanded : unexpandedAt b9Nodes [.query hyde] =
    [.hydeRetriever 1,.hydeRetriever 0,.hydeRetriever 2] := by decide

theorem native_query_expansion_step (tape : SharedTape) (before : List (TreeEvaluation Act))
    (c : ℝ) (penalty : List (TreeEvaluation Act) → List Act → Act → ℝ) (fuel : ℕ)
    (q : Fin 8) (hn : unexpandedAt (expandedNodes before) [.query q] ≠ []) :
    nativeSelect tape c penalty before (fuel+1) [.query q] = [.query q]++
      [tape.action before .expansion [.query q] (unexpandedAt (expandedNodes before) [.query q])] := by
  have ha : orderedLegalAvailable [.query q] ≠ [] := by fin_cases q <;> decide
  simp only [nativeSelect,if_neg ha]
  exact if_neg hn

end AgentUCTNativeBudget
