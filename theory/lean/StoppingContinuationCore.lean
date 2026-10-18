import WindowFiniteBudget





set_option autoImplicit false
set_option maxRecDepth 16384
set_option maxHeartbeats 4000000
noncomputable section
namespace AgentUCT32MContinuation
open AgentUCTSavedBudget AgentUCTObservability AgentUCTObservabilityBoundary AgentUCTPhysicalDiagnostic
  AgentUCTNativeBudget AgentUCTPanelAllocation AgentUCTNativeRepair AgentUCTNativeRefinement AgentUCTPaper

theorem native_after_length_bounds (tape : SharedTape) (c : ℝ)
    (penalty : List (TreeEvaluation Act) → List Act → Act → ℝ)
    (actualBill : List (TreeEvaluation Act) → ℝ) (B : ℝ) (reward : List Act → ℝ)
    (fuel : ℕ) (before : List (TreeEvaluation Act)) :
    before.length ≤ (nativeAfter tape c penalty actualBill B reward fuel before).length ∧
    (nativeAfter tape c penalty actualBill B reward fuel before).length ≤ before.length+fuel := by
  induction fuel generalizing before with
  | zero => simp [nativeAfter]
  | succ fuel ih =>
      simp only [nativeAfter]
      split_ifs
      · constructor <;> omega
      · have hh := ih (before++[nativeEvent tape c penalty reward before])
        simp only [List.length_append,List.length_singleton] at hh
        constructor <;> omega

theorem native_after_exhausts_fuel_or_reaches_actual_target (tape : SharedTape) (c : ℝ)
    (penalty : List (TreeEvaluation Act) → List Act → Act → ℝ)
    (actualBill : List (TreeEvaluation Act) → ℝ) (B : ℝ) (reward : List Act → ℝ)
    (fuel : ℕ) (before : List (TreeEvaluation Act)) :
    (nativeAfter tape c penalty actualBill B reward fuel before).length = before.length+fuel ∨
    targetReached (actualBill (nativeAfter tape c penalty actualBill B reward fuel before)) B := by
  induction fuel generalizing before with
  | zero => exact Or.inl (by simp [nativeAfter])
  | succ fuel ih =>
      simp only [nativeAfter]
      split_ifs with h
      · exact Or.inr h
      · rcases ih (before++[nativeEvent tape c penalty reward before]) with hh | hh
        · left
          simp only [List.length_append,List.length_singleton] at hh
          omega
        · exact Or.inr hh

theorem full_control_run_is_legal_allocated_and_target_or_cap
    (Cref epsilon : ℝ) (unused : Act → Fin 8 → ℕ)
    (mode : ForecastMode) (adverse : Bool) (cap : ℕ) (hcap : 8 ≤ cap) :
    LegalTreeRun Terminal {[]} (controlRun Cref savedTarget epsilon unused mode adverse cap) ∧
    TreeAllocationRule nativeTerminals (7/5) (controlPenalty Cref epsilon unused mode)
      (controlRun Cref savedTarget epsilon unused mode adverse cap) ∧
    ((controlRun Cref savedTarget epsilon unused mode adverse cap).length = cap ∨
      targetReached (completedBill unused (controlRun Cref savedTarget epsilon unused mode adverse cap)) savedTarget) := by
  let reward := taskReward adverse (2/5) (1/2)
  have hinit := budget_initialization_legal_and_allocation reward (7/5) (controlPenalty Cref epsilon unused mode)
  unfold controlRun nativeGenerate
  rw [budget_common_eight_initialization]
  refine ⟨native_after_legal_tree _ budget_tape_supported _ _ _ _ _ _ _ hinit.1,
    native_after_allocation _ budget_tape_supported _ _ _ _ _ _ _ hinit.1 hinit.2,?_⟩
  rcases native_after_exhausts_fuel_or_reaches_actual_target budgetTape (7/5)
    (controlPenalty Cref epsilon unused mode) (completedBill unused) savedTarget reward
    (cap-8) (initialization reward) with hh | hh
  · left
    have hi : (initialization reward).length = 8 := by simp [initialization]
    rw [hi] at hh
    exact hh.trans (by omega)
  · exact Or.inr hh

end AgentUCT32MContinuation
