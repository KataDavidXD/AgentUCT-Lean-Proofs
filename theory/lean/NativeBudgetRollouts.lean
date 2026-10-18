import NativeBudgetStatistics




set_option autoImplicit false
set_option maxRecDepth 16384
set_option maxHeartbeats 4000000
set_option linter.constructorNameAsVariable false
noncomputable section
namespace AgentUCTNativeBudget
open AgentUCTPanelAllocation AgentUCTNativeRepair AgentUCTNativeRefinement AgentUCTPaper

def routeRollout : ℕ → List Act → List Act
  | 0,p => p
  | fuel+1,p => if orderedLegalAvailable p = [] then p else
      routeRollout fuel (p++[choosePreferences
        [((rolloutGoal p).drop p.length).headD .stop] (orderedLegalAvailable p)])

theorem after_eight_rollout_computed (before : List (TreeEvaluation Act)) (hb : 8 ≤ before.length)
    (fuel : ℕ) (p : List Act) : repairedRollout budgetTape before fuel p = routeRollout fuel p := by
  have hn : ¬ before.length < 8 := by omega
  induction fuel generalizing p with
  | zero => rfl
  | succ fuel ih =>
      simp only [repairedRollout,routeRollout]
      split_ifs
      · rfl
      · simpa [budgetTape,routePreferences,hn] using ih
          (p++[choosePreferences [((rolloutGoal p).drop p.length).headD .stop] (orderedLegalAvailable p)])

theorem a_cold_rollout_computation : routeRollout 9 [.query hyde,.hydeRetriever 1] = aCold := by decide
theorem a_warm_rollout_computation : routeRollout 9 [.query hyde,.hydeRetriever 0] = aWarm := by decide
theorem a_cross_rollout_computation : routeRollout 9 [.query hyde,.hydeRetriever 2] = aCross := by decide
theorem b_cold_rollout_computation : routeRollout 9 [.query branchB,.normalRetriever 1] = bCold := by decide

theorem resolved_four_rollouts (before : List (TreeEvaluation Act)) (hb : 8 ≤ before.length) :
    repairedRollout budgetTape before 9 [.query hyde,.hydeRetriever 1] = aCold ∧
    repairedRollout budgetTape before 9 [.query hyde,.hydeRetriever 0] = aWarm ∧
    repairedRollout budgetTape before 9 [.query hyde,.hydeRetriever 2] = aCross ∧
    repairedRollout budgetTape before 9 [.query branchB,.normalRetriever 1] = bCold := by
  simp only [after_eight_rollout_computed before hb,a_cold_rollout_computation,a_warm_rollout_computation,
    a_cross_rollout_computation,b_cold_rollout_computation,and_self]

theorem a_expansion_first_computation :
    choosePreferences [.hydeRetriever 1,.hydeRetriever 0,.hydeRetriever 2]
      (orderedLegalAvailable [.query hyde]) = .hydeRetriever 1 := by decide

theorem a_expansion_second_computation :
    choosePreferences [.hydeRetriever 1,.hydeRetriever 0,.hydeRetriever 2]
      ((orderedLegalAvailable [.query hyde]).filter (fun a => a ≠ .hydeRetriever 1)) = .hydeRetriever 0 := by decide

theorem a_expansion_third_computation :
    choosePreferences [.hydeRetriever 1,.hydeRetriever 0,.hydeRetriever 2]
      ((orderedLegalAvailable [.query hyde]).filter (fun a => a ≠ .hydeRetriever 1 ∧ a ≠ .hydeRetriever 0)) = .hydeRetriever 2 := by decide

theorem b_expansion_first_computation :
    choosePreferences [.normalRetriever 1,.normalRetriever 0]
      (orderedLegalAvailable [.query branchB]) = .normalRetriever 1 := by decide

theorem mc_root_hyde_completion (before : List (TreeEvaluation Act)) (i : Fin 16) :
    budgetTape.completion before [] (.query hyde) i = aCold := by
  change safeCompletion [.query hyde] = aCold
  decide

theorem mc_root_normal_completion (before : List (TreeEvaluation Act)) (q : Fin 8) (hq : q ≠ hyde) (i : Fin 16) :
    budgetTape.completion before [] (.query q) i = fullLeaf q (.normalRetriever 0) 0 1 1 2 0 := by
  fin_cases q <;> simp_all +decide [budgetTape,safeCompletion,mcGoal,Terminal,Legal,followLegal,
    fullLeaf,available,retrievers,hyde,rootOrder]

theorem resolved_mc16_supported_same_history (before : List (TreeEvaluation Act)) (p : List Act)
    (hp : Legal p) (a : Act) (ha : a ∈ available p) (i : Fin 16) :
    budgetTape.completion before p a i ∈ subtreeTerminals nativeTerminals (p++[a]) ∧
    ∃ tail, budgetTape.completion before p a i = (p++[a])++tail ∧
      0 < pathProbability before 1 (p++[a]) tail :=
  ⟨supported_mc16_in_native_subtree budgetTape budget_tape_supported before p hp a ha i,
   supported_completion_historical_positive budgetTape budget_tape_supported before p hp a ha i 1 (by norm_num)⟩

end AgentUCTNativeBudget
