import EndpointBudgetProposals
import NativeAfterCertificate
import FavorableCompleteChoices12To19
import FavorableCompleteChoices20To27
import FavorableCompleteChoices28To35
import FavorableCompleteChoices36To44
import FavorableNextChoices11To18
import FavorableNextChoices19To26
import FavorableNextChoices27To37
import AdverseCompleteChoices12To19
import AdverseCompleteChoices20To27
import AdverseCompleteChoices28To35
import AdverseCompleteChoices36To45
import AdverseNextChoices11To18
import AdverseNextChoices19To26
import AdverseNextChoices27To36
set_option autoImplicit false
set_option maxRecDepth 16384
set_option maxHeartbeats 100000000
noncomputable section
namespace AgentUCT32MConcrete
open AgentUCT32MContinuation AgentUCTSavedBudget AgentUCTObservability
  AgentUCTPhysicalDiagnostic AgentUCTNativeBudget AgentUCTPanelAllocation
  AgentUCTNativeRepair AgentUCTNativeRefinement AgentUCTPaper AgentUCTRealIndex

theorem favorableComplete_all_actual_steps (i : ℕ) (hb : 11 ≤ i) (hi : i < favorableCompleteProposal.length) :
    nativeEvent budgetTape (7/5) (controlPenalty savedCref uniformQuoteError unitRoleUnused .complete) (taskReward false (2/5) (1/2))
      (favorableCompleteProposal.take i) = favorableCompleteProposal[i] := by
  have hlimit : i < 44 := by simpa only [favorableComplete_proposal_length] using hi
  interval_cases i
  · change nativeEvent budgetTape (7/5) (controlPenalty savedCref uniformQuoteError unitRoleUnused .complete) (taskReward false (2/5) (1/2)) (favorableCompleteProposal.take 11) = favorableCompleteEvent12
    exact favorableCompleteS12ActualEvent
  · change nativeEvent budgetTape (7/5) (controlPenalty savedCref uniformQuoteError unitRoleUnused .complete) (taskReward false (2/5) (1/2)) (favorableCompleteProposal.take 12) = favorableCompleteEvent13
    exact favorableCompleteS13ActualEvent
  · change nativeEvent budgetTape (7/5) (controlPenalty savedCref uniformQuoteError unitRoleUnused .complete) (taskReward false (2/5) (1/2)) (favorableCompleteProposal.take 13) = favorableCompleteEvent14
    exact favorableCompleteS14ActualEvent
  · change nativeEvent budgetTape (7/5) (controlPenalty savedCref uniformQuoteError unitRoleUnused .complete) (taskReward false (2/5) (1/2)) (favorableCompleteProposal.take 14) = favorableCompleteEvent15
    exact favorableCompleteS15ActualEvent
  · change nativeEvent budgetTape (7/5) (controlPenalty savedCref uniformQuoteError unitRoleUnused .complete) (taskReward false (2/5) (1/2)) (favorableCompleteProposal.take 15) = favorableCompleteEvent16
    exact favorableCompleteS16ActualEvent
  · change nativeEvent budgetTape (7/5) (controlPenalty savedCref uniformQuoteError unitRoleUnused .complete) (taskReward false (2/5) (1/2)) (favorableCompleteProposal.take 16) = favorableCompleteEvent17
    exact favorableCompleteS17ActualEvent
  · change nativeEvent budgetTape (7/5) (controlPenalty savedCref uniformQuoteError unitRoleUnused .complete) (taskReward false (2/5) (1/2)) (favorableCompleteProposal.take 17) = favorableCompleteEvent18
    exact favorableCompleteS18ActualEvent
  · change nativeEvent budgetTape (7/5) (controlPenalty savedCref uniformQuoteError unitRoleUnused .complete) (taskReward false (2/5) (1/2)) (favorableCompleteProposal.take 18) = favorableCompleteEvent19
    exact favorableCompleteS19ActualEvent
  · change nativeEvent budgetTape (7/5) (controlPenalty savedCref uniformQuoteError unitRoleUnused .complete) (taskReward false (2/5) (1/2)) (favorableCompleteProposal.take 19) = favorableCompleteEvent20
    exact favorableCompleteS20ActualEvent
  · change nativeEvent budgetTape (7/5) (controlPenalty savedCref uniformQuoteError unitRoleUnused .complete) (taskReward false (2/5) (1/2)) (favorableCompleteProposal.take 20) = favorableCompleteEvent21
    exact favorableCompleteS21ActualEvent
  · change nativeEvent budgetTape (7/5) (controlPenalty savedCref uniformQuoteError unitRoleUnused .complete) (taskReward false (2/5) (1/2)) (favorableCompleteProposal.take 21) = favorableCompleteEvent22
    exact favorableCompleteS22ActualEvent
  · change nativeEvent budgetTape (7/5) (controlPenalty savedCref uniformQuoteError unitRoleUnused .complete) (taskReward false (2/5) (1/2)) (favorableCompleteProposal.take 22) = favorableCompleteEvent23
    exact favorableCompleteS23ActualEvent
  · change nativeEvent budgetTape (7/5) (controlPenalty savedCref uniformQuoteError unitRoleUnused .complete) (taskReward false (2/5) (1/2)) (favorableCompleteProposal.take 23) = favorableCompleteEvent24
    exact favorableCompleteS24ActualEvent
  · change nativeEvent budgetTape (7/5) (controlPenalty savedCref uniformQuoteError unitRoleUnused .complete) (taskReward false (2/5) (1/2)) (favorableCompleteProposal.take 24) = favorableCompleteEvent25
    exact favorableCompleteS25ActualEvent
  · change nativeEvent budgetTape (7/5) (controlPenalty savedCref uniformQuoteError unitRoleUnused .complete) (taskReward false (2/5) (1/2)) (favorableCompleteProposal.take 25) = favorableCompleteEvent26
    exact favorableCompleteS26ActualEvent
  · change nativeEvent budgetTape (7/5) (controlPenalty savedCref uniformQuoteError unitRoleUnused .complete) (taskReward false (2/5) (1/2)) (favorableCompleteProposal.take 26) = favorableCompleteEvent27
    exact favorableCompleteS27ActualEvent
  · change nativeEvent budgetTape (7/5) (controlPenalty savedCref uniformQuoteError unitRoleUnused .complete) (taskReward false (2/5) (1/2)) (favorableCompleteProposal.take 27) = favorableCompleteEvent28
    exact favorableCompleteS28ActualEvent
  · change nativeEvent budgetTape (7/5) (controlPenalty savedCref uniformQuoteError unitRoleUnused .complete) (taskReward false (2/5) (1/2)) (favorableCompleteProposal.take 28) = favorableCompleteEvent29
    exact favorableCompleteS29ActualEvent
  · change nativeEvent budgetTape (7/5) (controlPenalty savedCref uniformQuoteError unitRoleUnused .complete) (taskReward false (2/5) (1/2)) (favorableCompleteProposal.take 29) = favorableCompleteEvent30
    exact favorableCompleteS30ActualEvent
  · change nativeEvent budgetTape (7/5) (controlPenalty savedCref uniformQuoteError unitRoleUnused .complete) (taskReward false (2/5) (1/2)) (favorableCompleteProposal.take 30) = favorableCompleteEvent31
    exact favorableCompleteS31ActualEvent
  · change nativeEvent budgetTape (7/5) (controlPenalty savedCref uniformQuoteError unitRoleUnused .complete) (taskReward false (2/5) (1/2)) (favorableCompleteProposal.take 31) = favorableCompleteEvent32
    exact favorableCompleteS32ActualEvent
  · change nativeEvent budgetTape (7/5) (controlPenalty savedCref uniformQuoteError unitRoleUnused .complete) (taskReward false (2/5) (1/2)) (favorableCompleteProposal.take 32) = favorableCompleteEvent33
    exact favorableCompleteS33ActualEvent
  · change nativeEvent budgetTape (7/5) (controlPenalty savedCref uniformQuoteError unitRoleUnused .complete) (taskReward false (2/5) (1/2)) (favorableCompleteProposal.take 33) = favorableCompleteEvent34
    exact favorableCompleteS34ActualEvent
  · change nativeEvent budgetTape (7/5) (controlPenalty savedCref uniformQuoteError unitRoleUnused .complete) (taskReward false (2/5) (1/2)) (favorableCompleteProposal.take 34) = favorableCompleteEvent35
    exact favorableCompleteS35ActualEvent
  · change nativeEvent budgetTape (7/5) (controlPenalty savedCref uniformQuoteError unitRoleUnused .complete) (taskReward false (2/5) (1/2)) (favorableCompleteProposal.take 35) = favorableCompleteEvent36
    exact favorableCompleteS36ActualEvent
  · change nativeEvent budgetTape (7/5) (controlPenalty savedCref uniformQuoteError unitRoleUnused .complete) (taskReward false (2/5) (1/2)) (favorableCompleteProposal.take 36) = favorableCompleteEvent37
    exact favorableCompleteS37ActualEvent
  · change nativeEvent budgetTape (7/5) (controlPenalty savedCref uniformQuoteError unitRoleUnused .complete) (taskReward false (2/5) (1/2)) (favorableCompleteProposal.take 37) = favorableCompleteEvent38
    exact favorableCompleteS38ActualEvent
  · change nativeEvent budgetTape (7/5) (controlPenalty savedCref uniformQuoteError unitRoleUnused .complete) (taskReward false (2/5) (1/2)) (favorableCompleteProposal.take 38) = favorableCompleteEvent39
    exact favorableCompleteS39ActualEvent
  · change nativeEvent budgetTape (7/5) (controlPenalty savedCref uniformQuoteError unitRoleUnused .complete) (taskReward false (2/5) (1/2)) (favorableCompleteProposal.take 39) = favorableCompleteEvent40
    exact favorableCompleteS40ActualEvent
  · change nativeEvent budgetTape (7/5) (controlPenalty savedCref uniformQuoteError unitRoleUnused .complete) (taskReward false (2/5) (1/2)) (favorableCompleteProposal.take 40) = favorableCompleteEvent41
    exact favorableCompleteS41ActualEvent
  · change nativeEvent budgetTape (7/5) (controlPenalty savedCref uniformQuoteError unitRoleUnused .complete) (taskReward false (2/5) (1/2)) (favorableCompleteProposal.take 41) = favorableCompleteEvent42
    exact favorableCompleteS42ActualEvent
  · change nativeEvent budgetTape (7/5) (controlPenalty savedCref uniformQuoteError unitRoleUnused .complete) (taskReward false (2/5) (1/2)) (favorableCompleteProposal.take 42) = favorableCompleteEvent43
    exact favorableCompleteS43ActualEvent
  · change nativeEvent budgetTape (7/5) (controlPenalty savedCref uniformQuoteError unitRoleUnused .complete) (taskReward false (2/5) (1/2)) (favorableCompleteProposal.take 43) = favorableCompleteEvent44
    exact favorableCompleteS44ActualEvent

theorem favorableComplete_actual_control_run (cap : ℕ) (hcap : 45 ≤ cap) :
    controlRun savedCref savedTarget uniformQuoteError unitRoleUnused .complete false cap = favorableCompleteProposal := by
  obtain ⟨hp,he⟩ := uniform_quote_only_error_inputs savedCref saved_reference_in_control_interval
  have hr := (control_prefixes_with_native_remainder savedCref savedTarget uniformQuoteError unitRoleUnused false cap
    (by omega) saved_reference_in_control_interval hp he (initial_checkpoints_below_saved_target _ _)).1
  have hbase : aEleven (taskReward false (2/5) (1/2)) = favorableCompleteProposal.take 11 :=
    (complete_initial_proposal_eq false).symm
  rw [hr,hbase]
  apply native_after_from_base_certificate budgetTape (7/5) (controlPenalty savedCref uniformQuoteError unitRoleUnused .complete)
    (completedBill unitRoleUnused) savedTarget (taskReward false (2/5) (1/2)) favorableCompleteProposal 11 cap
  · rw [favorableComplete_proposal_length]; omega
  · rw [favorableComplete_proposal_length]; omega
  · intro i hb hi
    apply favorableComplete_proposal_all_proper_prefixes i
    simpa only [favorableComplete_proposal_length] using hi
  · have hf := favorableComplete_proposal_invoice_window.2
    linarith
  · exact favorableComplete_all_actual_steps

theorem favorableNext_all_actual_steps (i : ℕ) (hb : 10 ≤ i) (hi : i < favorableNextProposal.length) :
    nativeEvent budgetTape (7/5) (controlPenalty savedCref uniformQuoteError unitRoleUnused .next) (taskReward false (2/5) (1/2))
      (favorableNextProposal.take i) = favorableNextProposal[i] := by
  have hlimit : i < 37 := by simpa only [favorableNext_proposal_length] using hi
  interval_cases i
  · change nativeEvent budgetTape (7/5) (controlPenalty savedCref uniformQuoteError unitRoleUnused .next) (taskReward false (2/5) (1/2)) (favorableNextProposal.take 10) = favorableNextEvent11
    exact favorableNextS11ActualEvent
  · change nativeEvent budgetTape (7/5) (controlPenalty savedCref uniformQuoteError unitRoleUnused .next) (taskReward false (2/5) (1/2)) (favorableNextProposal.take 11) = favorableNextEvent12
    exact favorableNextS12ActualEvent
  · change nativeEvent budgetTape (7/5) (controlPenalty savedCref uniformQuoteError unitRoleUnused .next) (taskReward false (2/5) (1/2)) (favorableNextProposal.take 12) = favorableNextEvent13
    exact favorableNextS13ActualEvent
  · change nativeEvent budgetTape (7/5) (controlPenalty savedCref uniformQuoteError unitRoleUnused .next) (taskReward false (2/5) (1/2)) (favorableNextProposal.take 13) = favorableNextEvent14
    exact favorableNextS14ActualEvent
  · change nativeEvent budgetTape (7/5) (controlPenalty savedCref uniformQuoteError unitRoleUnused .next) (taskReward false (2/5) (1/2)) (favorableNextProposal.take 14) = favorableNextEvent15
    exact favorableNextS15ActualEvent
  · change nativeEvent budgetTape (7/5) (controlPenalty savedCref uniformQuoteError unitRoleUnused .next) (taskReward false (2/5) (1/2)) (favorableNextProposal.take 15) = favorableNextEvent16
    exact favorableNextS16ActualEvent
  · change nativeEvent budgetTape (7/5) (controlPenalty savedCref uniformQuoteError unitRoleUnused .next) (taskReward false (2/5) (1/2)) (favorableNextProposal.take 16) = favorableNextEvent17
    exact favorableNextS17ActualEvent
  · change nativeEvent budgetTape (7/5) (controlPenalty savedCref uniformQuoteError unitRoleUnused .next) (taskReward false (2/5) (1/2)) (favorableNextProposal.take 17) = favorableNextEvent18
    exact favorableNextS18ActualEvent
  · change nativeEvent budgetTape (7/5) (controlPenalty savedCref uniformQuoteError unitRoleUnused .next) (taskReward false (2/5) (1/2)) (favorableNextProposal.take 18) = favorableNextEvent19
    exact favorableNextS19ActualEvent
  · change nativeEvent budgetTape (7/5) (controlPenalty savedCref uniformQuoteError unitRoleUnused .next) (taskReward false (2/5) (1/2)) (favorableNextProposal.take 19) = favorableNextEvent20
    exact favorableNextS20ActualEvent
  · change nativeEvent budgetTape (7/5) (controlPenalty savedCref uniformQuoteError unitRoleUnused .next) (taskReward false (2/5) (1/2)) (favorableNextProposal.take 20) = favorableNextEvent21
    exact favorableNextS21ActualEvent
  · change nativeEvent budgetTape (7/5) (controlPenalty savedCref uniformQuoteError unitRoleUnused .next) (taskReward false (2/5) (1/2)) (favorableNextProposal.take 21) = favorableNextEvent22
    exact favorableNextS22ActualEvent
  · change nativeEvent budgetTape (7/5) (controlPenalty savedCref uniformQuoteError unitRoleUnused .next) (taskReward false (2/5) (1/2)) (favorableNextProposal.take 22) = favorableNextEvent23
    exact favorableNextS23ActualEvent
  · change nativeEvent budgetTape (7/5) (controlPenalty savedCref uniformQuoteError unitRoleUnused .next) (taskReward false (2/5) (1/2)) (favorableNextProposal.take 23) = favorableNextEvent24
    exact favorableNextS24ActualEvent
  · change nativeEvent budgetTape (7/5) (controlPenalty savedCref uniformQuoteError unitRoleUnused .next) (taskReward false (2/5) (1/2)) (favorableNextProposal.take 24) = favorableNextEvent25
    exact favorableNextS25ActualEvent
  · change nativeEvent budgetTape (7/5) (controlPenalty savedCref uniformQuoteError unitRoleUnused .next) (taskReward false (2/5) (1/2)) (favorableNextProposal.take 25) = favorableNextEvent26
    exact favorableNextS26ActualEvent
  · change nativeEvent budgetTape (7/5) (controlPenalty savedCref uniformQuoteError unitRoleUnused .next) (taskReward false (2/5) (1/2)) (favorableNextProposal.take 26) = favorableNextEvent27
    exact favorableNextS27ActualEvent
  · change nativeEvent budgetTape (7/5) (controlPenalty savedCref uniformQuoteError unitRoleUnused .next) (taskReward false (2/5) (1/2)) (favorableNextProposal.take 27) = favorableNextEvent28
    exact favorableNextS28ActualEvent
  · change nativeEvent budgetTape (7/5) (controlPenalty savedCref uniformQuoteError unitRoleUnused .next) (taskReward false (2/5) (1/2)) (favorableNextProposal.take 28) = favorableNextEvent29
    exact favorableNextS29ActualEvent
  · change nativeEvent budgetTape (7/5) (controlPenalty savedCref uniformQuoteError unitRoleUnused .next) (taskReward false (2/5) (1/2)) (favorableNextProposal.take 29) = favorableNextEvent30
    exact favorableNextS30ActualEvent
  · change nativeEvent budgetTape (7/5) (controlPenalty savedCref uniformQuoteError unitRoleUnused .next) (taskReward false (2/5) (1/2)) (favorableNextProposal.take 30) = favorableNextEvent31
    exact favorableNextS31ActualEvent
  · change nativeEvent budgetTape (7/5) (controlPenalty savedCref uniformQuoteError unitRoleUnused .next) (taskReward false (2/5) (1/2)) (favorableNextProposal.take 31) = favorableNextEvent32
    exact favorableNextS32ActualEvent
  · change nativeEvent budgetTape (7/5) (controlPenalty savedCref uniformQuoteError unitRoleUnused .next) (taskReward false (2/5) (1/2)) (favorableNextProposal.take 32) = favorableNextEvent33
    exact favorableNextS33ActualEvent
  · change nativeEvent budgetTape (7/5) (controlPenalty savedCref uniformQuoteError unitRoleUnused .next) (taskReward false (2/5) (1/2)) (favorableNextProposal.take 33) = favorableNextEvent34
    exact favorableNextS34ActualEvent
  · change nativeEvent budgetTape (7/5) (controlPenalty savedCref uniformQuoteError unitRoleUnused .next) (taskReward false (2/5) (1/2)) (favorableNextProposal.take 34) = favorableNextEvent35
    exact favorableNextS35ActualEvent
  · change nativeEvent budgetTape (7/5) (controlPenalty savedCref uniformQuoteError unitRoleUnused .next) (taskReward false (2/5) (1/2)) (favorableNextProposal.take 35) = favorableNextEvent36
    exact favorableNextS36ActualEvent
  · change nativeEvent budgetTape (7/5) (controlPenalty savedCref uniformQuoteError unitRoleUnused .next) (taskReward false (2/5) (1/2)) (favorableNextProposal.take 36) = favorableNextEvent37
    exact favorableNextS37ActualEvent

theorem favorableNext_actual_control_run (cap : ℕ) (hcap : 45 ≤ cap) :
    controlRun savedCref savedTarget uniformQuoteError unitRoleUnused .next false cap = favorableNextProposal := by
  obtain ⟨hp,he⟩ := uniform_quote_only_error_inputs savedCref saved_reference_in_control_interval
  have hr := (control_prefixes_with_native_remainder savedCref savedTarget uniformQuoteError unitRoleUnused false cap
    (by omega) saved_reference_in_control_interval hp he (initial_checkpoints_below_saved_target _ _)).2
  have hbase : bTen (taskReward false (2/5) (1/2)) = favorableNextProposal.take 10 :=
    (next_initial_proposal_eq false).symm
  rw [hr,hbase]
  apply native_after_from_base_certificate budgetTape (7/5) (controlPenalty savedCref uniformQuoteError unitRoleUnused .next)
    (completedBill unitRoleUnused) savedTarget (taskReward false (2/5) (1/2)) favorableNextProposal 10 cap
  · rw [favorableNext_proposal_length]; omega
  · rw [favorableNext_proposal_length]; omega
  · intro i hb hi
    apply favorableNext_proposal_all_proper_prefixes i
    simpa only [favorableNext_proposal_length] using hi
  · have hf := favorableNext_proposal_invoice_window.2
    linarith
  · exact favorableNext_all_actual_steps

theorem adverseComplete_all_actual_steps (i : ℕ) (hb : 11 ≤ i) (hi : i < adverseCompleteProposal.length) :
    nativeEvent budgetTape (7/5) (controlPenalty savedCref uniformQuoteError unitRoleUnused .complete) (taskReward true (2/5) (1/2))
      (adverseCompleteProposal.take i) = adverseCompleteProposal[i] := by
  have hlimit : i < 45 := by simpa only [adverseComplete_proposal_length] using hi
  interval_cases i
  · change nativeEvent budgetTape (7/5) (controlPenalty savedCref uniformQuoteError unitRoleUnused .complete) (taskReward true (2/5) (1/2)) (adverseCompleteProposal.take 11) = adverseCompleteEvent12
    exact adverseCompleteS12ActualEvent
  · change nativeEvent budgetTape (7/5) (controlPenalty savedCref uniformQuoteError unitRoleUnused .complete) (taskReward true (2/5) (1/2)) (adverseCompleteProposal.take 12) = adverseCompleteEvent13
    exact adverseCompleteS13ActualEvent
  · change nativeEvent budgetTape (7/5) (controlPenalty savedCref uniformQuoteError unitRoleUnused .complete) (taskReward true (2/5) (1/2)) (adverseCompleteProposal.take 13) = adverseCompleteEvent14
    exact adverseCompleteS14ActualEvent
  · change nativeEvent budgetTape (7/5) (controlPenalty savedCref uniformQuoteError unitRoleUnused .complete) (taskReward true (2/5) (1/2)) (adverseCompleteProposal.take 14) = adverseCompleteEvent15
    exact adverseCompleteS15ActualEvent
  · change nativeEvent budgetTape (7/5) (controlPenalty savedCref uniformQuoteError unitRoleUnused .complete) (taskReward true (2/5) (1/2)) (adverseCompleteProposal.take 15) = adverseCompleteEvent16
    exact adverseCompleteS16ActualEvent
  · change nativeEvent budgetTape (7/5) (controlPenalty savedCref uniformQuoteError unitRoleUnused .complete) (taskReward true (2/5) (1/2)) (adverseCompleteProposal.take 16) = adverseCompleteEvent17
    exact adverseCompleteS17ActualEvent
  · change nativeEvent budgetTape (7/5) (controlPenalty savedCref uniformQuoteError unitRoleUnused .complete) (taskReward true (2/5) (1/2)) (adverseCompleteProposal.take 17) = adverseCompleteEvent18
    exact adverseCompleteS18ActualEvent
  · change nativeEvent budgetTape (7/5) (controlPenalty savedCref uniformQuoteError unitRoleUnused .complete) (taskReward true (2/5) (1/2)) (adverseCompleteProposal.take 18) = adverseCompleteEvent19
    exact adverseCompleteS19ActualEvent
  · change nativeEvent budgetTape (7/5) (controlPenalty savedCref uniformQuoteError unitRoleUnused .complete) (taskReward true (2/5) (1/2)) (adverseCompleteProposal.take 19) = adverseCompleteEvent20
    exact adverseCompleteS20ActualEvent
  · change nativeEvent budgetTape (7/5) (controlPenalty savedCref uniformQuoteError unitRoleUnused .complete) (taskReward true (2/5) (1/2)) (adverseCompleteProposal.take 20) = adverseCompleteEvent21
    exact adverseCompleteS21ActualEvent
  · change nativeEvent budgetTape (7/5) (controlPenalty savedCref uniformQuoteError unitRoleUnused .complete) (taskReward true (2/5) (1/2)) (adverseCompleteProposal.take 21) = adverseCompleteEvent22
    exact adverseCompleteS22ActualEvent
  · change nativeEvent budgetTape (7/5) (controlPenalty savedCref uniformQuoteError unitRoleUnused .complete) (taskReward true (2/5) (1/2)) (adverseCompleteProposal.take 22) = adverseCompleteEvent23
    exact adverseCompleteS23ActualEvent
  · change nativeEvent budgetTape (7/5) (controlPenalty savedCref uniformQuoteError unitRoleUnused .complete) (taskReward true (2/5) (1/2)) (adverseCompleteProposal.take 23) = adverseCompleteEvent24
    exact adverseCompleteS24ActualEvent
  · change nativeEvent budgetTape (7/5) (controlPenalty savedCref uniformQuoteError unitRoleUnused .complete) (taskReward true (2/5) (1/2)) (adverseCompleteProposal.take 24) = adverseCompleteEvent25
    exact adverseCompleteS25ActualEvent
  · change nativeEvent budgetTape (7/5) (controlPenalty savedCref uniformQuoteError unitRoleUnused .complete) (taskReward true (2/5) (1/2)) (adverseCompleteProposal.take 25) = adverseCompleteEvent26
    exact adverseCompleteS26ActualEvent
  · change nativeEvent budgetTape (7/5) (controlPenalty savedCref uniformQuoteError unitRoleUnused .complete) (taskReward true (2/5) (1/2)) (adverseCompleteProposal.take 26) = adverseCompleteEvent27
    exact adverseCompleteS27ActualEvent
  · change nativeEvent budgetTape (7/5) (controlPenalty savedCref uniformQuoteError unitRoleUnused .complete) (taskReward true (2/5) (1/2)) (adverseCompleteProposal.take 27) = adverseCompleteEvent28
    exact adverseCompleteS28ActualEvent
  · change nativeEvent budgetTape (7/5) (controlPenalty savedCref uniformQuoteError unitRoleUnused .complete) (taskReward true (2/5) (1/2)) (adverseCompleteProposal.take 28) = adverseCompleteEvent29
    exact adverseCompleteS29ActualEvent
  · change nativeEvent budgetTape (7/5) (controlPenalty savedCref uniformQuoteError unitRoleUnused .complete) (taskReward true (2/5) (1/2)) (adverseCompleteProposal.take 29) = adverseCompleteEvent30
    exact adverseCompleteS30ActualEvent
  · change nativeEvent budgetTape (7/5) (controlPenalty savedCref uniformQuoteError unitRoleUnused .complete) (taskReward true (2/5) (1/2)) (adverseCompleteProposal.take 30) = adverseCompleteEvent31
    exact adverseCompleteS31ActualEvent
  · change nativeEvent budgetTape (7/5) (controlPenalty savedCref uniformQuoteError unitRoleUnused .complete) (taskReward true (2/5) (1/2)) (adverseCompleteProposal.take 31) = adverseCompleteEvent32
    exact adverseCompleteS32ActualEvent
  · change nativeEvent budgetTape (7/5) (controlPenalty savedCref uniformQuoteError unitRoleUnused .complete) (taskReward true (2/5) (1/2)) (adverseCompleteProposal.take 32) = adverseCompleteEvent33
    exact adverseCompleteS33ActualEvent
  · change nativeEvent budgetTape (7/5) (controlPenalty savedCref uniformQuoteError unitRoleUnused .complete) (taskReward true (2/5) (1/2)) (adverseCompleteProposal.take 33) = adverseCompleteEvent34
    exact adverseCompleteS34ActualEvent
  · change nativeEvent budgetTape (7/5) (controlPenalty savedCref uniformQuoteError unitRoleUnused .complete) (taskReward true (2/5) (1/2)) (adverseCompleteProposal.take 34) = adverseCompleteEvent35
    exact adverseCompleteS35ActualEvent
  · change nativeEvent budgetTape (7/5) (controlPenalty savedCref uniformQuoteError unitRoleUnused .complete) (taskReward true (2/5) (1/2)) (adverseCompleteProposal.take 35) = adverseCompleteEvent36
    exact adverseCompleteS36ActualEvent
  · change nativeEvent budgetTape (7/5) (controlPenalty savedCref uniformQuoteError unitRoleUnused .complete) (taskReward true (2/5) (1/2)) (adverseCompleteProposal.take 36) = adverseCompleteEvent37
    exact adverseCompleteS37ActualEvent
  · change nativeEvent budgetTape (7/5) (controlPenalty savedCref uniformQuoteError unitRoleUnused .complete) (taskReward true (2/5) (1/2)) (adverseCompleteProposal.take 37) = adverseCompleteEvent38
    exact adverseCompleteS38ActualEvent
  · change nativeEvent budgetTape (7/5) (controlPenalty savedCref uniformQuoteError unitRoleUnused .complete) (taskReward true (2/5) (1/2)) (adverseCompleteProposal.take 38) = adverseCompleteEvent39
    exact adverseCompleteS39ActualEvent
  · change nativeEvent budgetTape (7/5) (controlPenalty savedCref uniformQuoteError unitRoleUnused .complete) (taskReward true (2/5) (1/2)) (adverseCompleteProposal.take 39) = adverseCompleteEvent40
    exact adverseCompleteS40ActualEvent
  · change nativeEvent budgetTape (7/5) (controlPenalty savedCref uniformQuoteError unitRoleUnused .complete) (taskReward true (2/5) (1/2)) (adverseCompleteProposal.take 40) = adverseCompleteEvent41
    exact adverseCompleteS41ActualEvent
  · change nativeEvent budgetTape (7/5) (controlPenalty savedCref uniformQuoteError unitRoleUnused .complete) (taskReward true (2/5) (1/2)) (adverseCompleteProposal.take 41) = adverseCompleteEvent42
    exact adverseCompleteS42ActualEvent
  · change nativeEvent budgetTape (7/5) (controlPenalty savedCref uniformQuoteError unitRoleUnused .complete) (taskReward true (2/5) (1/2)) (adverseCompleteProposal.take 42) = adverseCompleteEvent43
    exact adverseCompleteS43ActualEvent
  · change nativeEvent budgetTape (7/5) (controlPenalty savedCref uniformQuoteError unitRoleUnused .complete) (taskReward true (2/5) (1/2)) (adverseCompleteProposal.take 43) = adverseCompleteEvent44
    exact adverseCompleteS44ActualEvent
  · change nativeEvent budgetTape (7/5) (controlPenalty savedCref uniformQuoteError unitRoleUnused .complete) (taskReward true (2/5) (1/2)) (adverseCompleteProposal.take 44) = adverseCompleteEvent45
    exact adverseCompleteS45ActualEvent

theorem adverseComplete_actual_control_run (cap : ℕ) (hcap : 45 ≤ cap) :
    controlRun savedCref savedTarget uniformQuoteError unitRoleUnused .complete true cap = adverseCompleteProposal := by
  obtain ⟨hp,he⟩ := uniform_quote_only_error_inputs savedCref saved_reference_in_control_interval
  have hr := (control_prefixes_with_native_remainder savedCref savedTarget uniformQuoteError unitRoleUnused true cap
    (by omega) saved_reference_in_control_interval hp he (initial_checkpoints_below_saved_target _ _)).1
  have hbase : aEleven (taskReward true (2/5) (1/2)) = adverseCompleteProposal.take 11 :=
    (complete_initial_proposal_eq true).symm
  rw [hr,hbase]
  apply native_after_from_base_certificate budgetTape (7/5) (controlPenalty savedCref uniformQuoteError unitRoleUnused .complete)
    (completedBill unitRoleUnused) savedTarget (taskReward true (2/5) (1/2)) adverseCompleteProposal 11 cap
  · rw [adverseComplete_proposal_length]; omega
  · rw [adverseComplete_proposal_length]; omega
  · intro i hb hi
    apply adverseComplete_proposal_all_proper_prefixes i
    simpa only [adverseComplete_proposal_length] using hi
  · have hf := adverseComplete_proposal_invoice_window.2
    linarith
  · exact adverseComplete_all_actual_steps

theorem adverseNext_all_actual_steps (i : ℕ) (hb : 10 ≤ i) (hi : i < adverseNextProposal.length) :
    nativeEvent budgetTape (7/5) (controlPenalty savedCref uniformQuoteError unitRoleUnused .next) (taskReward true (2/5) (1/2))
      (adverseNextProposal.take i) = adverseNextProposal[i] := by
  have hlimit : i < 36 := by simpa only [adverseNext_proposal_length] using hi
  interval_cases i
  · change nativeEvent budgetTape (7/5) (controlPenalty savedCref uniformQuoteError unitRoleUnused .next) (taskReward true (2/5) (1/2)) (adverseNextProposal.take 10) = adverseNextEvent11
    exact adverseNextS11ActualEvent
  · change nativeEvent budgetTape (7/5) (controlPenalty savedCref uniformQuoteError unitRoleUnused .next) (taskReward true (2/5) (1/2)) (adverseNextProposal.take 11) = adverseNextEvent12
    exact adverseNextS12ActualEvent
  · change nativeEvent budgetTape (7/5) (controlPenalty savedCref uniformQuoteError unitRoleUnused .next) (taskReward true (2/5) (1/2)) (adverseNextProposal.take 12) = adverseNextEvent13
    exact adverseNextS13ActualEvent
  · change nativeEvent budgetTape (7/5) (controlPenalty savedCref uniformQuoteError unitRoleUnused .next) (taskReward true (2/5) (1/2)) (adverseNextProposal.take 13) = adverseNextEvent14
    exact adverseNextS14ActualEvent
  · change nativeEvent budgetTape (7/5) (controlPenalty savedCref uniformQuoteError unitRoleUnused .next) (taskReward true (2/5) (1/2)) (adverseNextProposal.take 14) = adverseNextEvent15
    exact adverseNextS15ActualEvent
  · change nativeEvent budgetTape (7/5) (controlPenalty savedCref uniformQuoteError unitRoleUnused .next) (taskReward true (2/5) (1/2)) (adverseNextProposal.take 15) = adverseNextEvent16
    exact adverseNextS16ActualEvent
  · change nativeEvent budgetTape (7/5) (controlPenalty savedCref uniformQuoteError unitRoleUnused .next) (taskReward true (2/5) (1/2)) (adverseNextProposal.take 16) = adverseNextEvent17
    exact adverseNextS17ActualEvent
  · change nativeEvent budgetTape (7/5) (controlPenalty savedCref uniformQuoteError unitRoleUnused .next) (taskReward true (2/5) (1/2)) (adverseNextProposal.take 17) = adverseNextEvent18
    exact adverseNextS18ActualEvent
  · change nativeEvent budgetTape (7/5) (controlPenalty savedCref uniformQuoteError unitRoleUnused .next) (taskReward true (2/5) (1/2)) (adverseNextProposal.take 18) = adverseNextEvent19
    exact adverseNextS19ActualEvent
  · change nativeEvent budgetTape (7/5) (controlPenalty savedCref uniformQuoteError unitRoleUnused .next) (taskReward true (2/5) (1/2)) (adverseNextProposal.take 19) = adverseNextEvent20
    exact adverseNextS20ActualEvent
  · change nativeEvent budgetTape (7/5) (controlPenalty savedCref uniformQuoteError unitRoleUnused .next) (taskReward true (2/5) (1/2)) (adverseNextProposal.take 20) = adverseNextEvent21
    exact adverseNextS21ActualEvent
  · change nativeEvent budgetTape (7/5) (controlPenalty savedCref uniformQuoteError unitRoleUnused .next) (taskReward true (2/5) (1/2)) (adverseNextProposal.take 21) = adverseNextEvent22
    exact adverseNextS22ActualEvent
  · change nativeEvent budgetTape (7/5) (controlPenalty savedCref uniformQuoteError unitRoleUnused .next) (taskReward true (2/5) (1/2)) (adverseNextProposal.take 22) = adverseNextEvent23
    exact adverseNextS23ActualEvent
  · change nativeEvent budgetTape (7/5) (controlPenalty savedCref uniformQuoteError unitRoleUnused .next) (taskReward true (2/5) (1/2)) (adverseNextProposal.take 23) = adverseNextEvent24
    exact adverseNextS24ActualEvent
  · change nativeEvent budgetTape (7/5) (controlPenalty savedCref uniformQuoteError unitRoleUnused .next) (taskReward true (2/5) (1/2)) (adverseNextProposal.take 24) = adverseNextEvent25
    exact adverseNextS25ActualEvent
  · change nativeEvent budgetTape (7/5) (controlPenalty savedCref uniformQuoteError unitRoleUnused .next) (taskReward true (2/5) (1/2)) (adverseNextProposal.take 25) = adverseNextEvent26
    exact adverseNextS26ActualEvent
  · change nativeEvent budgetTape (7/5) (controlPenalty savedCref uniformQuoteError unitRoleUnused .next) (taskReward true (2/5) (1/2)) (adverseNextProposal.take 26) = adverseNextEvent27
    exact adverseNextS27ActualEvent
  · change nativeEvent budgetTape (7/5) (controlPenalty savedCref uniformQuoteError unitRoleUnused .next) (taskReward true (2/5) (1/2)) (adverseNextProposal.take 27) = adverseNextEvent28
    exact adverseNextS28ActualEvent
  · change nativeEvent budgetTape (7/5) (controlPenalty savedCref uniformQuoteError unitRoleUnused .next) (taskReward true (2/5) (1/2)) (adverseNextProposal.take 28) = adverseNextEvent29
    exact adverseNextS29ActualEvent
  · change nativeEvent budgetTape (7/5) (controlPenalty savedCref uniformQuoteError unitRoleUnused .next) (taskReward true (2/5) (1/2)) (adverseNextProposal.take 29) = adverseNextEvent30
    exact adverseNextS30ActualEvent
  · change nativeEvent budgetTape (7/5) (controlPenalty savedCref uniformQuoteError unitRoleUnused .next) (taskReward true (2/5) (1/2)) (adverseNextProposal.take 30) = adverseNextEvent31
    exact adverseNextS31ActualEvent
  · change nativeEvent budgetTape (7/5) (controlPenalty savedCref uniformQuoteError unitRoleUnused .next) (taskReward true (2/5) (1/2)) (adverseNextProposal.take 31) = adverseNextEvent32
    exact adverseNextS32ActualEvent
  · change nativeEvent budgetTape (7/5) (controlPenalty savedCref uniformQuoteError unitRoleUnused .next) (taskReward true (2/5) (1/2)) (adverseNextProposal.take 32) = adverseNextEvent33
    exact adverseNextS33ActualEvent
  · change nativeEvent budgetTape (7/5) (controlPenalty savedCref uniformQuoteError unitRoleUnused .next) (taskReward true (2/5) (1/2)) (adverseNextProposal.take 33) = adverseNextEvent34
    exact adverseNextS34ActualEvent
  · change nativeEvent budgetTape (7/5) (controlPenalty savedCref uniformQuoteError unitRoleUnused .next) (taskReward true (2/5) (1/2)) (adverseNextProposal.take 34) = adverseNextEvent35
    exact adverseNextS35ActualEvent
  · change nativeEvent budgetTape (7/5) (controlPenalty savedCref uniformQuoteError unitRoleUnused .next) (taskReward true (2/5) (1/2)) (adverseNextProposal.take 35) = adverseNextEvent36
    exact adverseNextS36ActualEvent

theorem adverseNext_actual_control_run (cap : ℕ) (hcap : 45 ≤ cap) :
    controlRun savedCref savedTarget uniformQuoteError unitRoleUnused .next true cap = adverseNextProposal := by
  obtain ⟨hp,he⟩ := uniform_quote_only_error_inputs savedCref saved_reference_in_control_interval
  have hr := (control_prefixes_with_native_remainder savedCref savedTarget uniformQuoteError unitRoleUnused true cap
    (by omega) saved_reference_in_control_interval hp he (initial_checkpoints_below_saved_target _ _)).2
  have hbase : bTen (taskReward true (2/5) (1/2)) = adverseNextProposal.take 10 :=
    (next_initial_proposal_eq true).symm
  rw [hr,hbase]
  apply native_after_from_base_certificate budgetTape (7/5) (controlPenalty savedCref uniformQuoteError unitRoleUnused .next)
    (completedBill unitRoleUnused) savedTarget (taskReward true (2/5) (1/2)) adverseNextProposal 10 cap
  · rw [adverseNext_proposal_length]; omega
  · rw [adverseNext_proposal_length]; omega
  · intro i hb hi
    apply adverseNext_proposal_all_proper_prefixes i
    simpa only [adverseNext_proposal_length] using hi
  · have hf := adverseNext_proposal_invoice_window.2
    linarith
  · exact adverseNext_all_actual_steps

end AgentUCT32MConcrete
