import FirstContinuedChoice
set_option autoImplicit false
set_option maxRecDepth 16384
set_option maxHeartbeats 16000000
noncomputable section
namespace AgentUCT32MConcrete
open AgentUCT32MContinuation AgentUCTSavedBudget AgentUCTObservability
  AgentUCTPhysicalDiagnostic AgentUCTNativeBudget AgentUCTPanelAllocation
  AgentUCTNativeRepair AgentUCTNativeRefinement AgentUCTPaper AgentUCTRealIndex

theorem complete_initial_proposal_eq (adverse : Bool) :
    (if adverse then adverseCompleteProposal else favorableCompleteProposal).take 11 =
      aEleven (taskReward adverse (2/5) (1/2)) := by
  cases adverse <;> rfl

theorem next_initial_proposal_eq (adverse : Bool) :
    (if adverse then adverseNextProposal else favorableNextProposal).take 10 =
      bTen (taskReward adverse (2/5) (1/2)) := by
  cases adverse <;> rfl

theorem control_saved32M_complete_base (adverse : Bool) :
    controlRun savedCref savedTarget uniformQuoteError unitRoleUnused .complete adverse 11 =
      (if adverse then adverseCompleteProposal else favorableCompleteProposal).take 11 := by
  obtain ⟨hp,he⟩ := uniform_quote_only_error_inputs savedCref saved_reference_in_control_interval
  have h := (control_prefixes_with_native_remainder savedCref savedTarget uniformQuoteError unitRoleUnused
    adverse 11 (by omega) saved_reference_in_control_interval hp he
    (initial_checkpoints_below_saved_target _ _)).1
  rw [complete_initial_proposal_eq]
  simpa only [Nat.sub_self,nativeAfter] using h

theorem control_saved32M_next_base (adverse : Bool) :
    controlRun savedCref savedTarget uniformQuoteError unitRoleUnused .next adverse 10 =
      (if adverse then adverseNextProposal else favorableNextProposal).take 10 := by
  obtain ⟨hp,he⟩ := uniform_quote_only_error_inputs savedCref saved_reference_in_control_interval
  obtain ⟨h1,h2,h3,h4,h5⟩ := control_five_causal_events savedCref uniformQuoteError unitRoleUnused
    adverse saved_reference_in_control_interval hp he
  have hb := initial_checkpoints_below_saved_target unitRoleUnused (taskReward adverse (2/5) (1/2))
  unfold controlRun nativeGenerate
  rw [budget_common_eight_initialization]
  rw [next_initial_proposal_eq]
  change nativeAfter budgetTape (7/5) _ _ _ _ 2 _ = _
  rw [nativeAfter]
  simp only [targetReached]
  rw [if_neg (not_le.mpr hb.1),h2]
  change nativeAfter budgetTape (7/5) _ _ _ _ 1 (bNine _) = _
  rw [nativeAfter]
  simp only [targetReached]
  rw [if_neg (not_le.mpr hb.2.2.2),h5]
  rfl

theorem favorable_complete_twelve_generated :
    controlRun savedCref savedTarget uniformQuoteError unitRoleUnused .complete false 12 =
      favorableCompleteProposal.take 12 := by
  have hb : completedBill unitRoleUnused favorableCompleteH11 < savedTarget := by
    change completedBill unitRoleUnused (aEleven (taskReward false (2/5) (1/2))) < savedTarget
    unfold completedBill
    rw [(completed_raw_and_retained_bills unitRoleUnused (taskReward false (2/5) (1/2))).1]
    norm_num [savedTarget,panel150,baseBill,tailBill,crossBill,eightBill,integerTariffs,generatorRate,e5Rate,bgeRate,embeddingRate,identityQuery,Fin.sum_univ_succ,Fin.succ] <;> simp +decide <;> norm_num
  obtain ⟨hp,he⟩ := uniform_quote_only_error_inputs savedCref saved_reference_in_control_interval
  have h := (control_prefixes_with_native_remainder savedCref savedTarget uniformQuoteError unitRoleUnused
    false 12 (by omega) saved_reference_in_control_interval hp he
    (initial_checkpoints_below_saved_target _ _)).1
  change controlRun savedCref savedTarget uniformQuoteError unitRoleUnused .complete false 12 =
    nativeAfter budgetTape (7/5) (controlPenalty savedCref uniformQuoteError unitRoleUnused .complete)
      (completedBill unitRoleUnused) savedTarget (taskReward false (2/5) (1/2)) 1 favorableCompleteH11 at h
  rw [h,nativeAfter]
  simp only [targetReached]
  rw [if_neg (not_le.mpr hb),favorable_complete_12_actual_event]
  rfl

end AgentUCT32MConcrete
