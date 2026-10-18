import NativeEightInitialization



set_option autoImplicit false
set_option maxRecDepth 8192
set_option maxHeartbeats 4000000
set_option linter.constructorNameAsVariable false
noncomputable section
namespace AgentUCTPanelAllocation
open AgentUCTNativeRefinement AgentUCTNativeRepair AgentUCTPaper

theorem legal_ordered_available_eq {p : List Act} (hp : Legal p) :
    orderedLegalAvailable p = orderedAvailable p := by
  simp only [orderedLegalAvailable,legal_available_eq hp,orderedAvailable]

theorem repaired_visited_choice_eq_native (mode : ForecastMode) (tape : SharedTape)
    (prices : Unit × List Act → ℝ) (c gamma : ℝ) (before : List (TreeEvaluation Act))
    (p : List Act) (hp : Legal p) :
    repairedVisitedChoice mode tape prices c gamma before p =
      visitedChoice mode tape prices c gamma before p := by
  dsimp only [repairedVisitedChoice,visitedChoice]
  rw [legal_ordered_available_eq hp]
  cases hh : ((orderedAvailable p).filter fun a =>
    (replayBackup before emptyStatistics (p++[a])).visits = 0).head?
  · exact (left_ordered_maximum_eq_firstMaximum
      (nodeScore mode tape prices c gamma before p) (orderedAvailable p)).symm
  · rfl

def frozenUnitPenalty (mode : ForecastMode) (tape : SharedTape)
    (prices : Unit × List Act → ℝ) (gamma : ℝ)
    (before : List (TreeEvaluation Act)) (p : List Act) (a : Act) : ℝ :=
  gamma * forecast mode tape prices before p a

theorem unit_index_score_eq_node_score (mode : ForecastMode) (tape : SharedTape)
    (prices : Unit × List Act → ℝ) (c gamma : ℝ) (before : List (TreeEvaluation Act))
    (p : List Act) :
    indexScore c (frozenUnitPenalty mode tape prices gamma) before p =
      nodeScore mode tape prices c gamma before p := rfl

theorem native_select_eq_repaired_selection (mode : ForecastMode) (tape : SharedTape)
    (prices : Unit × List Act → ℝ) (c gamma : ℝ) (before : List (TreeEvaluation Act))
    (fuel : ℕ) (p : List Act) :
    nativeSelect tape c (frozenUnitPenalty mode tape prices gamma) before fuel p =
      repairedSelection mode tape prices c gamma before fuel p := by
  induction fuel generalizing p with
  | zero => rfl
  | succ fuel ih =>
      simp only [nativeSelect,repairedSelection,unit_index_score_eq_node_score,
        native_first_choice_eq_repaired,ih]

theorem repaired_selection_eq_native_selection (mode : ForecastMode) (tape : SharedTape)
    (ht : LegalSupportedTape tape) (prices : Unit × List Act → ℝ) (c gamma : ℝ)
    (before : List (TreeEvaluation Act)) (fuel : ℕ) (p : List Act) (hp : Legal p) :
    repairedSelection mode tape prices c gamma before fuel p =
      selectExpansion mode tape prices c gamma before fuel p := by
  induction fuel generalizing p with
  | zero => rfl
  | succ fuel ih =>
      simp only [repairedSelection,selectExpansion,legal_ordered_available_eq hp]
      by_cases hn : available p = []
      · have ho := (ordered_legal_nil_iff hp).mpr hn
        rw [legal_ordered_available_eq hp] at ho
        simp only [hn,ho,if_pos]
      · have ho : orderedAvailable p ≠ [] := by
          intro he
          exact hn ((ordered_legal_nil_iff hp).mp (by rw [legal_ordered_available_eq hp]; exact he))
        simp only [if_neg hn,if_neg ho]
        by_cases hu : (orderedAvailable p).filter (fun a => p++[a] ∉ expandedNodes before) = []
        · simp only [hu,if_pos]
          rw [← repaired_visited_choice_eq_native mode tape prices c gamma before p hp]
          apply ih
          exact (legal_append_action p _).mpr ⟨hp,(ordered_legal_member_iff hp _).mp
            (repaired_visited_choice_member mode tape prices c gamma before p
              (by rw [legal_ordered_available_eq hp]; exact ho))⟩
        · simp only [hu,if_false]

theorem native_select_eq_frozen_native (mode : ForecastMode) (tape : SharedTape)
    (ht : LegalSupportedTape tape) (prices : Unit × List Act → ℝ) (c gamma : ℝ)
    (before : List (TreeEvaluation Act)) (fuel : ℕ) (p : List Act) (hp : Legal p) :
    nativeSelect tape c (frozenUnitPenalty mode tape prices gamma) before fuel p =
      selectExpansion mode tape prices c gamma before fuel p := by
  rw [native_select_eq_repaired_selection]
  exact repaired_selection_eq_native_selection mode tape ht prices c gamma before fuel p hp

end AgentUCTPanelAllocation
