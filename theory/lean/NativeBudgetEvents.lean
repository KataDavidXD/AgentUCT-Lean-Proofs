import NativeBudgetNodeReplay





set_option autoImplicit false
set_option maxRecDepth 16384
set_option maxHeartbeats 4000000
set_option linter.constructorNameAsVariable false
noncomputable section
namespace AgentUCTNativeBudget
open AgentUCTPanelAllocation AgentUCTNativeRepair AgentUCTNativeRefinement AgentUCTPaper
variable {Qid : Type*} [DecidableEq Qid]

theorem resolved_A_expansion (before : List (TreeEvaluation Act)) (hb : 8 ≤ before.length)
    (candidates : List Act) :
    budgetTape.action before .expansion [.query hyde] candidates =
      choosePreferences [.hydeRetriever 1,.hydeRetriever 0,.hydeRetriever 2] candidates := by
  simp [budgetTape,routePreferences,show ¬ before.length < 8 by omega]

theorem resolved_B_expansion (before : List (TreeEvaluation Act)) (hb : 8 ≤ before.length)
    (candidates : List Act) :
    budgetTape.action before .expansion [.query branchB] candidates =
      choosePreferences [.normalRetriever 1,.normalRetriever 0] candidates := by
  simp [budgetTape,routePreferences,show ¬ before.length < 8 by omega,
    show branchB ≠ hyde by decide]

theorem root_then_expand (before : List (TreeEvaluation Act)) (c : ℝ)
    (penalty : List (TreeEvaluation Act) → List Act → Act → ℝ) (q : Fin 8)
    (hp : ∀ r : Fin 8,[.query r] ∈ expandedNodes before)
    (hc : nativeFirstChoice (indexScore c penalty before []) before [] = .query q)
    (hu : unexpandedAt (expandedNodes before) [.query q] ≠ []) :
    nativeSelect budgetTape c penalty before 9 [] = [.query q]++
      [budgetTape.action before .expansion [.query q]
        (unexpandedAt (expandedNodes before) [.query q])] := by
  rw [initialized_root_selection_recursion budgetTape before hp c penalty 8,hc]
  exact native_query_expansion_step budgetTape before c penalty 7 q hu

theorem reference_complete_initial_expanded (qids : Finset Qid) (t : TariffInput)
    (reward : List Act → ℝ) (delta good c beta Cref : ℝ) (hs : SeedTable reward delta)
    (hm : RootMargins t c (penaltyScale qids beta Cref) delta good) :
    nativeSelect budgetTape c (referencePenalty qids .complete t beta Cref)
      (initialization reward) 9 [] = [.query hyde,.hydeRetriever 1] := by
  have hp : ∀ q : Fin 8,[.query q] ∈ expandedNodes (initialization reward) := by
    intro q; rw [initialization_nodes_exact]; exact roots_in_initial_nodes q
  have hu : unexpandedAt (expandedNodes (initialization reward)) [.query hyde] =
      [.hydeRetriever 1,.hydeRetriever 0,.hydeRetriever 2] := by
    rw [initialization_nodes_exact]; exact initial_A_unexpanded
  rw [root_then_expand _ _ _ hyde hp
    (reference_complete_first_root qids t reward delta good c beta Cref hs hm)
    (by rw [hu]; decide),hu,resolved_A_expansion _ (by simp [initialization])]
  rfl

theorem reference_next_initial_expanded (qids : Finset Qid) (t : TariffInput)
    (reward : List Act → ℝ) (delta good c beta Cref : ℝ) (hs : SeedTable reward delta)
    (hm : RootMargins t c (penaltyScale qids beta Cref) delta good) :
    nativeSelect budgetTape c (referencePenalty qids .next t beta Cref)
      (initialization reward) 9 [] = [.query branchB,.normalRetriever 1] := by
  have hp : ∀ q : Fin 8,[.query q] ∈ expandedNodes (initialization reward) := by
    intro q; rw [initialization_nodes_exact]; exact roots_in_initial_nodes q
  have hu : unexpandedAt (expandedNodes (initialization reward)) [.query branchB] =
      orderedLegalAvailable [.query branchB] := by
    rw [initialization_nodes_exact]; exact initial_B_unexpanded
  rw [root_then_expand _ _ _ branchB hp
    (reference_next_first_root qids t reward delta good c beta Cref hs hm)
    (by rw [hu]; decide),hu,resolved_B_expansion _ (by simp [initialization])]
  exact congrArg (fun a => [.query branchB]++[a]) b_expansion_first_computation

theorem reference_complete_a9_expanded (qids : Finset Qid) (t : TariffInput)
    (reward : List Act → ℝ) (delta good c beta Cref : ℝ) (hs : SeedTable reward delta)
    (hr : 0 ≤ reward aCold)
    (hm : RootMargins t c (penaltyScale qids beta Cref) delta good) :
    nativeSelect budgetTape c (referencePenalty qids .complete t beta Cref)
      (aNine reward) 9 [] = [.query hyde,.hydeRetriever 0] := by
  have hp : ∀ q : Fin 8,[.query q] ∈ expandedNodes (aNine reward) := by
    intro q; rw [a9_nodes_exact]; exact Finset.mem_insert_of_mem (roots_in_initial_nodes q)
  have hu : unexpandedAt (expandedNodes (aNine reward)) [.query hyde] =
      [.hydeRetriever 0,.hydeRetriever 2] := by rw [a9_nodes_exact]; exact after_a9_A_unexpanded
  rw [root_then_expand _ _ _ hyde hp
    (reference_complete_second_root qids t reward delta good c beta Cref hs hr hm)
    (by rw [hu]; decide),hu,resolved_A_expansion _ (by rw [(resource_history_lengths reward).1]; omega)]
  rfl

theorem reference_complete_a10_expanded (qids : Finset Qid) (t : TariffInput)
    (reward : List Act → ℝ) (delta good c beta Cref : ℝ) (hs : SeedTable reward delta)
    (hr : 0 ≤ reward aCold)
    (hm : RootMargins t c (penaltyScale qids beta Cref) delta good) :
    nativeSelect budgetTape c (referencePenalty qids .complete t beta Cref)
      (aTen reward) 9 [] = [.query hyde,.hydeRetriever 2] := by
  have hp : ∀ q : Fin 8,[.query q] ∈ expandedNodes (aTen reward) := by
    intro q; rw [a10_nodes_exact]
    exact Finset.mem_insert_of_mem (Finset.mem_insert_of_mem (roots_in_initial_nodes q))
  have hu : unexpandedAt (expandedNodes (aTen reward)) [.query hyde] =
      [.hydeRetriever 2] := by rw [a10_nodes_exact]; exact after_a10_A_unexpanded
  rw [root_then_expand _ _ _ hyde hp
    (reference_complete_third_root qids t reward delta good c beta Cref hs hr hm)
    (by rw [hu]; decide),hu,resolved_A_expansion _ (by rw [(resource_history_lengths reward).2.1]; omega)]
  rfl

theorem reference_next_b9_expanded (qids : Finset Qid) (t : TariffInput)
    (reward : List Act → ℝ) (delta good c beta Cref : ℝ) (hs : SeedTable reward delta)
    (hr : reward bCold ≤ good)
    (hm : RootMargins t c (penaltyScale qids beta Cref) delta good) :
    nativeSelect budgetTape c (referencePenalty qids .next t beta Cref)
      (bNine reward) 9 [] = [.query hyde,.hydeRetriever 1] := by
  have hp : ∀ q : Fin 8,[.query q] ∈ expandedNodes (bNine reward) := by
    intro q; rw [b9_nodes_exact]; exact Finset.mem_insert_of_mem (roots_in_initial_nodes q)
  have hu : unexpandedAt (expandedNodes (bNine reward)) [.query hyde] =
      [.hydeRetriever 1,.hydeRetriever 0,.hydeRetriever 2] := by
    rw [b9_nodes_exact]; exact after_b9_A_unexpanded
  rw [root_then_expand _ _ _ hyde hp
    (reference_next_second_root qids t reward delta good c beta Cref hs hr hm)
    (by rw [hu]; decide),hu,resolved_A_expansion _ (by rw [(resource_history_lengths reward).2.2.2.1]; omega)]
  rfl

theorem native_route_event_of_computation (before : List (TreeEvaluation Act)) (c : ℝ)
    (penalty : List (TreeEvaluation Act) → List Act → Act → ℝ) (reward : List Act → ℝ)
    (q : Fin 8) (r : Act) (w : Fin 4) (m : Fin 3)
    (hs : nativeSelect budgetTape c penalty before 9 [] = [.query q,r])
    (hr : repairedRollout budgetTape before 9 [.query q,r] = leaf q r w m) :
    nativeEvent budgetTape c penalty reward before = routeEvent reward q r w m := by
  simp only [nativeEvent,hs,hr]
  rfl

theorem reference_complete_initial_event (qids : Finset Qid) (t : TariffInput)
    (reward : List Act → ℝ) (delta good c beta Cref : ℝ) (hs : SeedTable reward delta)
    (hm : RootMargins t c (penaltyScale qids beta Cref) delta good) :
    nativeEvent budgetTape c (referencePenalty qids .complete t beta Cref) reward
      (initialization reward) = aColdEvent reward := by
  exact native_route_event_of_computation _ _ _ _ _ _ _ _
    (reference_complete_initial_expanded qids t reward delta good c beta Cref hs hm)
    (resolved_four_rollouts _ (by simp [initialization])).1

theorem reference_next_initial_event (qids : Finset Qid) (t : TariffInput)
    (reward : List Act → ℝ) (delta good c beta Cref : ℝ) (hs : SeedTable reward delta)
    (hm : RootMargins t c (penaltyScale qids beta Cref) delta good) :
    nativeEvent budgetTape c (referencePenalty qids .next t beta Cref) reward
      (initialization reward) = bColdEvent reward := by
  exact native_route_event_of_computation _ _ _ _ _ _ _ _
    (reference_next_initial_expanded qids t reward delta good c beta Cref hs hm)
    (resolved_four_rollouts _ (by simp [initialization])).2.2.2

theorem reference_complete_a9_event (qids : Finset Qid) (t : TariffInput)
    (reward : List Act → ℝ) (delta good c beta Cref : ℝ) (hs : SeedTable reward delta)
    (hr : 0 ≤ reward aCold)
    (hm : RootMargins t c (penaltyScale qids beta Cref) delta good) :
    nativeEvent budgetTape c (referencePenalty qids .complete t beta Cref) reward
      (aNine reward) = aWarmEvent reward := by
  exact native_route_event_of_computation _ _ _ _ _ _ _ _
    (reference_complete_a9_expanded qids t reward delta good c beta Cref hs hr hm)
    (resolved_four_rollouts _ (by rw [(resource_history_lengths reward).1]; omega)).2.1

theorem reference_complete_a10_event (qids : Finset Qid) (t : TariffInput)
    (reward : List Act → ℝ) (delta good c beta Cref : ℝ) (hs : SeedTable reward delta)
    (hr : 0 ≤ reward aCold)
    (hm : RootMargins t c (penaltyScale qids beta Cref) delta good) :
    nativeEvent budgetTape c (referencePenalty qids .complete t beta Cref) reward
      (aTen reward) = aCrossEvent reward := by
  exact native_route_event_of_computation _ _ _ _ _ _ _ _
    (reference_complete_a10_expanded qids t reward delta good c beta Cref hs hr hm)
    (resolved_four_rollouts _ (by rw [(resource_history_lengths reward).2.1]; omega)).2.2.1

theorem reference_next_b9_event (qids : Finset Qid) (t : TariffInput)
    (reward : List Act → ℝ) (delta good c beta Cref : ℝ) (hs : SeedTable reward delta)
    (hr : reward bCold ≤ good)
    (hm : RootMargins t c (penaltyScale qids beta Cref) delta good) :
    nativeEvent budgetTape c (referencePenalty qids .next t beta Cref) reward
      (bNine reward) = aColdEvent reward := by
  exact native_route_event_of_computation _ _ _ _ _ _ _ _
    (reference_next_b9_expanded qids t reward delta good c beta Cref hs hr hm)
    (resolved_four_rollouts _ (by rw [(resource_history_lengths reward).2.2.2.1]; omega)).1

end AgentUCTNativeBudget
