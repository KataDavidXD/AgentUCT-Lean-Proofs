import StoppingContinuationCore




set_option autoImplicit false
set_option maxRecDepth 16384
set_option maxHeartbeats 4000000
noncomputable section
namespace AgentUCT32MContinuation
open AgentUCTSavedBudget AgentUCTObservability AgentUCTObservabilityBoundary AgentUCTPhysicalDiagnostic
  AgentUCTNativeBudget AgentUCTPanelAllocation AgentUCTNativeRepair AgentUCTNativeRefinement AgentUCTPaper

theorem native_after_emitted_proper_prefix_below_target (tape : SharedTape) (c : ℝ)
    (penalty : List (TreeEvaluation Act) → List Act → Act → ℝ)
    (actualBill : List (TreeEvaluation Act) → ℝ) (B : ℝ) (reward : List Act → ℝ)
    (fuel : ℕ) (before : List (TreeEvaluation Act)) :
    ∀ k,before.length ≤ k →
      k < (nativeAfter tape c penalty actualBill B reward fuel before).length →
      actualBill ((nativeAfter tape c penalty actualBill B reward fuel before).take k) < B := by
  induction fuel generalizing before with
  | zero => intro k hk hlen; simp only [nativeAfter] at hlen; omega
  | succ fuel ih =>
      intro k hk hlen
      simp only [nativeAfter] at hlen ⊢
      split_ifs at hlen ⊢ with ht
      · omega
      · by_cases heq : k = before.length
        · subst k
          have hp := native_after_initial_prefix tape c penalty actualBill B reward fuel
            (before++[nativeEvent tape c penalty reward before])
          obtain ⟨rest,hp⟩ := hp
          rw [← hp,List.append_assoc]
          simp only [List.take_left]
          exact not_le.mp ht
        · apply ih
          · simp only [List.length_append,List.length_singleton]; omega
          · exact hlen

theorem native_after_total_strict_proper_prefixes (tape : SharedTape) (c : ℝ)
    (penalty : List (TreeEvaluation Act) → List Act → Act → ℝ)
    (actualBill : List (TreeEvaluation Act) → ℝ) (B : ℝ) (reward : List Act → ℝ)
    (fuel : ℕ) (before : List (TreeEvaluation Act))
    (hinit : ∀ k,k < before.length → actualBill (before.take k) < B) :
    ∀ k,k < (nativeAfter tape c penalty actualBill B reward fuel before).length →
      actualBill ((nativeAfter tape c penalty actualBill B reward fuel before).take k) < B := by
  intro k hk
  by_cases hbefore : k < before.length
  · have hp := native_after_initial_prefix tape c penalty actualBill B reward fuel before
    obtain ⟨rest,hp⟩ := hp
    rw [← hp,List.take_append_of_le_length (by omega)]
    exact hinit k hbefore
  · exact native_after_emitted_proper_prefix_below_target tape c penalty actualBill B reward fuel before k (by omega) hk

theorem physical_control_run_strict_proper_prefixes (Cref epsilon : ℝ)
    (unused : Act → Fin 8 → ℕ) (mode : ForecastMode) (adverse : Bool) (cap : ℕ)
    (hprice : ∀ a,0 ≤ completedPrice unused a) :
    ∀ k,k < (controlRun Cref savedTarget epsilon unused mode adverse cap).length →
      completedBill unused ((controlRun Cref savedTarget epsilon unused mode adverse cap).take k) < savedTarget := by
  let reward := taskReward adverse (2/5) (1/2)
  have hfit := (initial_checkpoints_below_saved_target unused reward).1
  unfold controlRun nativeGenerate
  rw [budget_common_eight_initialization]
  apply native_after_total_strict_proper_prefixes
  intro k hk
  have hm := panel_actual_bill_prefix_monotone panel150
    (fun r => completedPrice unused (resourceAction r)) (fun r => hprice (resourceAction r))
    ((initialization reward).take k) (initialization reward) (List.take_prefix _ _)
  exact hm.trans_lt hfit

theorem target_reached_before_cap_is_first_complete_crossing
    (Cref epsilon : ℝ) (unused : Act → Fin 8 → ℕ) (mode : ForecastMode)
    (adverse : Bool) (cap : ℕ) (hcap : 8 ≤ cap)
    (hprice : ∀ a,0 ≤ completedPrice unused a)
    (hexhaust : (controlRun Cref savedTarget epsilon unused mode adverse cap).length < cap) :
    targetReached (completedBill unused (controlRun Cref savedTarget epsilon unused mode adverse cap)) savedTarget ∧
    ∀ k,k < (controlRun Cref savedTarget epsilon unused mode adverse cap).length →
      completedBill unused ((controlRun Cref savedTarget epsilon unused mode adverse cap).take k) < savedTarget := by
  have hs := (full_control_run_is_legal_allocated_and_target_or_cap Cref epsilon unused mode adverse cap hcap).2.2
  refine ⟨?_,physical_control_run_strict_proper_prefixes Cref epsilon unused mode adverse cap hprice⟩
  rcases hs with hs | hs
  · omega
  · exact hs

end AgentUCT32MContinuation
