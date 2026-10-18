import ProposalRewards
import TrajectoryBonus
import InitialConcreteBridge
import CompleteNormalQuote
import CachedSuffixCertificate
import RootHydeWarmSuffix
set_option autoImplicit false
set_option maxRecDepth 16384
set_option maxHeartbeats 100000000
set_option linter.unusedSimpArgs false
set_option linter.unreachableTactic false
set_option linter.unusedTactic false
noncomputable section
namespace AgentUCT32MConcrete
open AgentUCT32MContinuation AgentUCTSavedBudget AgentUCTObservability
  AgentUCTPhysicalDiagnostic AgentUCTNativeBudget AgentUCTPanelAllocation
  AgentUCTNativeRepair AgentUCTNativeRefinement AgentUCTPaper AgentUCTRealIndex

def adverseCompleteS36Before := adverseCompleteProposal.take 35

theorem adverseCompleteS36Choice0 : nativeFirstChoice (indexScore (7/5) (controlPenalty savedCref uniformQuoteError unitRoleUnused .complete) adverseCompleteS36Before []) adverseCompleteS36Before [] = .query 1 := by
  apply complete_root_from_physical_gap adverseCompleteS36Before (adverseComplete_prefix_rewards 35) (by decide)
  · intro q; fin_cases q <;> decide
  · exact AgentUCTNextExact.adverse_complete_hyde_root_suffix_empty 35 (by omega)
  · intro q hq
    exact AgentUCTNextExact.adverse_complete_normal_root_physical_quote_exact 35 (by omega) q hq

theorem adverseCompleteS36D1I0 : indexScore (7/5) (controlPenalty savedCref uniformQuoteError unitRoleUnused .complete) adverseCompleteS36Before [.query 1] (.hydeRetriever 1) = treeIndex ((0/1)/9) (7/5) 0 28 9 := by
  have hs : replayBackup adverseCompleteS36Before emptyStatistics ([.query 1]++[.hydeRetriever 1]) = ⟨9,(0/1)⟩ := by
    rw [replayBackup_empty_closed_form]
    simp +decide [backedEvents,adverseCompleteS36Before,adverseCompleteProposal,adverseCompleteEvent1,adverseCompleteEvent2,adverseCompleteEvent3,adverseCompleteEvent4,adverseCompleteEvent5,adverseCompleteEvent6,adverseCompleteEvent7,adverseCompleteEvent8,adverseCompleteEvent9,adverseCompleteEvent10,adverseCompleteEvent11,adverseCompleteEvent12,adverseCompleteEvent13,adverseCompleteEvent14,adverseCompleteEvent15,adverseCompleteEvent16,adverseCompleteEvent17,adverseCompleteEvent18,adverseCompleteEvent19,adverseCompleteEvent20,adverseCompleteEvent21,adverseCompleteEvent22,adverseCompleteEvent23,adverseCompleteEvent24,adverseCompleteEvent25,adverseCompleteEvent26,adverseCompleteEvent27,adverseCompleteEvent28,adverseCompleteEvent29,adverseCompleteEvent30,adverseCompleteEvent31,adverseCompleteEvent32,adverseCompleteEvent33,adverseCompleteEvent34,adverseCompleteEvent35,taskReward]
    <;> norm_num
  have hp : rawVisits adverseCompleteS36Before [.query 1] = 28 := by decide
  have hn : rawVisits adverseCompleteS36Before ([.query 1]++[.hydeRetriever 1]) = 9 := by decide
  have hz : (controlPenalty savedCref uniformQuoteError unitRoleUnused .complete) adverseCompleteS36Before [.query 1] (.hydeRetriever 1) = 0 := by
    apply control_penalty_empty_of_prior_terminal .complete savedCref uniformQuoteError adverseCompleteS36Before [.query 1] (.hydeRetriever 1) 8 (by decide)
    · decide
    · decide
  unfold indexScore
  rw [hs,hp,hn,hz]
  simp only [BackupStat.mean]
  norm_num

theorem adverseCompleteS36D1I1 : indexScore (7/5) (controlPenalty savedCref uniformQuoteError unitRoleUnused .complete) adverseCompleteS36Before [.query 1] (.hydeRetriever 0) = treeIndex ((0/1)/9) (7/5) 0 28 9 := by
  have hs : replayBackup adverseCompleteS36Before emptyStatistics ([.query 1]++[.hydeRetriever 0]) = ⟨9,(0/1)⟩ := by
    rw [replayBackup_empty_closed_form]
    simp +decide [backedEvents,adverseCompleteS36Before,adverseCompleteProposal,adverseCompleteEvent1,adverseCompleteEvent2,adverseCompleteEvent3,adverseCompleteEvent4,adverseCompleteEvent5,adverseCompleteEvent6,adverseCompleteEvent7,adverseCompleteEvent8,adverseCompleteEvent9,adverseCompleteEvent10,adverseCompleteEvent11,adverseCompleteEvent12,adverseCompleteEvent13,adverseCompleteEvent14,adverseCompleteEvent15,adverseCompleteEvent16,adverseCompleteEvent17,adverseCompleteEvent18,adverseCompleteEvent19,adverseCompleteEvent20,adverseCompleteEvent21,adverseCompleteEvent22,adverseCompleteEvent23,adverseCompleteEvent24,adverseCompleteEvent25,adverseCompleteEvent26,adverseCompleteEvent27,adverseCompleteEvent28,adverseCompleteEvent29,adverseCompleteEvent30,adverseCompleteEvent31,adverseCompleteEvent32,adverseCompleteEvent33,adverseCompleteEvent34,adverseCompleteEvent35,taskReward]
    <;> norm_num
  have hp : rawVisits adverseCompleteS36Before [.query 1] = 28 := by decide
  have hn : rawVisits adverseCompleteS36Before ([.query 1]++[.hydeRetriever 0]) = 9 := by decide
  have hz : (controlPenalty savedCref uniformQuoteError unitRoleUnused .complete) adverseCompleteS36Before [.query 1] (.hydeRetriever 0) = 0 := by
    apply control_penalty_empty_of_prior_terminal .complete savedCref uniformQuoteError adverseCompleteS36Before [.query 1] (.hydeRetriever 0) 1 (by decide)
    · decide
    · decide
  unfold indexScore
  rw [hs,hp,hn,hz]
  simp only [BackupStat.mean]
  norm_num

theorem adverseCompleteS36D1I2 : indexScore (7/5) (controlPenalty savedCref uniformQuoteError unitRoleUnused .complete) adverseCompleteS36Before [.query 1] (.hydeRetriever 2) = treeIndex ((0/1)/9) (7/5) 0 28 9 := by
  have hs : replayBackup adverseCompleteS36Before emptyStatistics ([.query 1]++[.hydeRetriever 2]) = ⟨9,(0/1)⟩ := by
    rw [replayBackup_empty_closed_form]
    simp +decide [backedEvents,adverseCompleteS36Before,adverseCompleteProposal,adverseCompleteEvent1,adverseCompleteEvent2,adverseCompleteEvent3,adverseCompleteEvent4,adverseCompleteEvent5,adverseCompleteEvent6,adverseCompleteEvent7,adverseCompleteEvent8,adverseCompleteEvent9,adverseCompleteEvent10,adverseCompleteEvent11,adverseCompleteEvent12,adverseCompleteEvent13,adverseCompleteEvent14,adverseCompleteEvent15,adverseCompleteEvent16,adverseCompleteEvent17,adverseCompleteEvent18,adverseCompleteEvent19,adverseCompleteEvent20,adverseCompleteEvent21,adverseCompleteEvent22,adverseCompleteEvent23,adverseCompleteEvent24,adverseCompleteEvent25,adverseCompleteEvent26,adverseCompleteEvent27,adverseCompleteEvent28,adverseCompleteEvent29,adverseCompleteEvent30,adverseCompleteEvent31,adverseCompleteEvent32,adverseCompleteEvent33,adverseCompleteEvent34,adverseCompleteEvent35,taskReward]
    <;> norm_num
  have hp : rawVisits adverseCompleteS36Before [.query 1] = 28 := by decide
  have hn : rawVisits adverseCompleteS36Before ([.query 1]++[.hydeRetriever 2]) = 9 := by decide
  have hz : (controlPenalty savedCref uniformQuoteError unitRoleUnused .complete) adverseCompleteS36Before [.query 1] (.hydeRetriever 2) = 0 := by
    apply control_penalty_empty_of_prior_terminal .complete savedCref uniformQuoteError adverseCompleteS36Before [.query 1] (.hydeRetriever 2) 10 (by decide)
    · decide
    · decide
  unfold indexScore
  rw [hs,hp,hn,hz]
  simp only [BackupStat.mean]
  norm_num

theorem adverseCompleteS36D1Cmp1 : indexScore (7/5) (controlPenalty savedCref uniformQuoteError unitRoleUnused .complete) adverseCompleteS36Before [.query 1] (.hydeRetriever 0) ≤ indexScore (7/5) (controlPenalty savedCref uniformQuoteError unitRoleUnused .complete) adverseCompleteS36Before [.query 1] (.hydeRetriever 1) := by
  rw [adverseCompleteS36D1I1,adverseCompleteS36D1I0]

theorem adverseCompleteS36D1Cmp2 : indexScore (7/5) (controlPenalty savedCref uniformQuoteError unitRoleUnused .complete) adverseCompleteS36Before [.query 1] (.hydeRetriever 2) ≤ indexScore (7/5) (controlPenalty savedCref uniformQuoteError unitRoleUnused .complete) adverseCompleteS36Before [.query 1] (.hydeRetriever 1) := by
  rw [adverseCompleteS36D1I2,adverseCompleteS36D1I0]

theorem adverseCompleteS36Choice1 : nativeFirstChoice (indexScore (7/5) (controlPenalty savedCref uniformQuoteError unitRoleUnused .complete) adverseCompleteS36Before [.query 1]) adverseCompleteS36Before [.query 1] = .hydeRetriever 1 := by
  apply visited_choice_from_ordered_certificate _ _ [.query 1] [] [.hydeRetriever 0,.hydeRetriever 2] (.hydeRetriever 1) (by decide)
  · intro a ha
    have ho : orderedLegalAvailable [.query 1] = [.hydeRetriever 1,.hydeRetriever 0,.hydeRetriever 2] := by decide
    rw [ho] at ha
    simp only [List.mem_cons,List.not_mem_nil,or_false] at ha
    rcases ha with rfl | rfl | rfl <;> decide
  · simp
  · intro a ha
    simp only [List.mem_cons,List.not_mem_nil,or_false] at ha
    rcases ha with rfl | rfl
    · exact adverseCompleteS36D1Cmp1
    · exact adverseCompleteS36D1Cmp2

theorem adverseCompleteS36D2I0 : indexScore (7/5) (controlPenalty savedCref uniformQuoteError unitRoleUnused .complete) adverseCompleteS36Before [.query 1,.hydeRetriever 1] (.selection 1) = treeIndex ((0/1)/2) (7/5) 0 9 2 := by
  have hs : replayBackup adverseCompleteS36Before emptyStatistics ([.query 1,.hydeRetriever 1]++[.selection 1]) = ⟨2,(0/1)⟩ := by
    rw [replayBackup_empty_closed_form]
    simp +decide [backedEvents,adverseCompleteS36Before,adverseCompleteProposal,adverseCompleteEvent1,adverseCompleteEvent2,adverseCompleteEvent3,adverseCompleteEvent4,adverseCompleteEvent5,adverseCompleteEvent6,adverseCompleteEvent7,adverseCompleteEvent8,adverseCompleteEvent9,adverseCompleteEvent10,adverseCompleteEvent11,adverseCompleteEvent12,adverseCompleteEvent13,adverseCompleteEvent14,adverseCompleteEvent15,adverseCompleteEvent16,adverseCompleteEvent17,adverseCompleteEvent18,adverseCompleteEvent19,adverseCompleteEvent20,adverseCompleteEvent21,adverseCompleteEvent22,adverseCompleteEvent23,adverseCompleteEvent24,adverseCompleteEvent25,adverseCompleteEvent26,adverseCompleteEvent27,adverseCompleteEvent28,adverseCompleteEvent29,adverseCompleteEvent30,adverseCompleteEvent31,adverseCompleteEvent32,adverseCompleteEvent33,adverseCompleteEvent34,adverseCompleteEvent35,taskReward]
    <;> norm_num
  have hp : rawVisits adverseCompleteS36Before [.query 1,.hydeRetriever 1] = 9 := by decide
  have hn : rawVisits adverseCompleteS36Before ([.query 1,.hydeRetriever 1]++[.selection 1]) = 2 := by decide
  have hz : (controlPenalty savedCref uniformQuoteError unitRoleUnused .complete) adverseCompleteS36Before [.query 1,.hydeRetriever 1] (.selection 1) = 0 := by
    apply control_penalty_empty_of_prior_terminal .complete savedCref uniformQuoteError adverseCompleteS36Before [.query 1,.hydeRetriever 1] (.selection 1) 14 (by decide)
    · decide
    · decide
  unfold indexScore
  rw [hs,hp,hn,hz]
  simp only [BackupStat.mean]
  norm_num

theorem adverseCompleteS36D2I1 : indexScore (7/5) (controlPenalty savedCref uniformQuoteError unitRoleUnused .complete) adverseCompleteS36Before [.query 1,.hydeRetriever 1] (.selection 2) = treeIndex ((0/1)/2) (7/5) 0 9 2 := by
  have hs : replayBackup adverseCompleteS36Before emptyStatistics ([.query 1,.hydeRetriever 1]++[.selection 2]) = ⟨2,(0/1)⟩ := by
    rw [replayBackup_empty_closed_form]
    simp +decide [backedEvents,adverseCompleteS36Before,adverseCompleteProposal,adverseCompleteEvent1,adverseCompleteEvent2,adverseCompleteEvent3,adverseCompleteEvent4,adverseCompleteEvent5,adverseCompleteEvent6,adverseCompleteEvent7,adverseCompleteEvent8,adverseCompleteEvent9,adverseCompleteEvent10,adverseCompleteEvent11,adverseCompleteEvent12,adverseCompleteEvent13,adverseCompleteEvent14,adverseCompleteEvent15,adverseCompleteEvent16,adverseCompleteEvent17,adverseCompleteEvent18,adverseCompleteEvent19,adverseCompleteEvent20,adverseCompleteEvent21,adverseCompleteEvent22,adverseCompleteEvent23,adverseCompleteEvent24,adverseCompleteEvent25,adverseCompleteEvent26,adverseCompleteEvent27,adverseCompleteEvent28,adverseCompleteEvent29,adverseCompleteEvent30,adverseCompleteEvent31,adverseCompleteEvent32,adverseCompleteEvent33,adverseCompleteEvent34,adverseCompleteEvent35,taskReward]
    <;> norm_num
  have hp : rawVisits adverseCompleteS36Before [.query 1,.hydeRetriever 1] = 9 := by decide
  have hn : rawVisits adverseCompleteS36Before ([.query 1,.hydeRetriever 1]++[.selection 2]) = 2 := by decide
  have hz : (controlPenalty savedCref uniformQuoteError unitRoleUnused .complete) adverseCompleteS36Before [.query 1,.hydeRetriever 1] (.selection 2) = 0 := by
    apply control_penalty_empty_of_prior_terminal .complete savedCref uniformQuoteError adverseCompleteS36Before [.query 1,.hydeRetriever 1] (.selection 2) 17 (by decide)
    · decide
    · decide
  unfold indexScore
  rw [hs,hp,hn,hz]
  simp only [BackupStat.mean]
  norm_num

theorem adverseCompleteS36D2I2 : indexScore (7/5) (controlPenalty savedCref uniformQuoteError unitRoleUnused .complete) adverseCompleteS36Before [.query 1,.hydeRetriever 1] (.selection 3) = treeIndex ((0/1)/2) (7/5) 0 9 2 := by
  have hs : replayBackup adverseCompleteS36Before emptyStatistics ([.query 1,.hydeRetriever 1]++[.selection 3]) = ⟨2,(0/1)⟩ := by
    rw [replayBackup_empty_closed_form]
    simp +decide [backedEvents,adverseCompleteS36Before,adverseCompleteProposal,adverseCompleteEvent1,adverseCompleteEvent2,adverseCompleteEvent3,adverseCompleteEvent4,adverseCompleteEvent5,adverseCompleteEvent6,adverseCompleteEvent7,adverseCompleteEvent8,adverseCompleteEvent9,adverseCompleteEvent10,adverseCompleteEvent11,adverseCompleteEvent12,adverseCompleteEvent13,adverseCompleteEvent14,adverseCompleteEvent15,adverseCompleteEvent16,adverseCompleteEvent17,adverseCompleteEvent18,adverseCompleteEvent19,adverseCompleteEvent20,adverseCompleteEvent21,adverseCompleteEvent22,adverseCompleteEvent23,adverseCompleteEvent24,adverseCompleteEvent25,adverseCompleteEvent26,adverseCompleteEvent27,adverseCompleteEvent28,adverseCompleteEvent29,adverseCompleteEvent30,adverseCompleteEvent31,adverseCompleteEvent32,adverseCompleteEvent33,adverseCompleteEvent34,adverseCompleteEvent35,taskReward]
    <;> norm_num
  have hp : rawVisits adverseCompleteS36Before [.query 1,.hydeRetriever 1] = 9 := by decide
  have hn : rawVisits adverseCompleteS36Before ([.query 1,.hydeRetriever 1]++[.selection 3]) = 2 := by decide
  have hz : (controlPenalty savedCref uniformQuoteError unitRoleUnused .complete) adverseCompleteS36Before [.query 1,.hydeRetriever 1] (.selection 3) = 0 := by
    apply control_penalty_empty_of_prior_terminal .complete savedCref uniformQuoteError adverseCompleteS36Before [.query 1,.hydeRetriever 1] (.selection 3) 20 (by decide)
    · decide
    · decide
  unfold indexScore
  rw [hs,hp,hn,hz]
  simp only [BackupStat.mean]
  norm_num

theorem adverseCompleteS36D2I3 : indexScore (7/5) (controlPenalty savedCref uniformQuoteError unitRoleUnused .complete) adverseCompleteS36Before [.query 1,.hydeRetriever 1] (.selection 0) = treeIndex ((0/1)/2) (7/5) 0 9 2 := by
  have hs : replayBackup adverseCompleteS36Before emptyStatistics ([.query 1,.hydeRetriever 1]++[.selection 0]) = ⟨2,(0/1)⟩ := by
    rw [replayBackup_empty_closed_form]
    simp +decide [backedEvents,adverseCompleteS36Before,adverseCompleteProposal,adverseCompleteEvent1,adverseCompleteEvent2,adverseCompleteEvent3,adverseCompleteEvent4,adverseCompleteEvent5,adverseCompleteEvent6,adverseCompleteEvent7,adverseCompleteEvent8,adverseCompleteEvent9,adverseCompleteEvent10,adverseCompleteEvent11,adverseCompleteEvent12,adverseCompleteEvent13,adverseCompleteEvent14,adverseCompleteEvent15,adverseCompleteEvent16,adverseCompleteEvent17,adverseCompleteEvent18,adverseCompleteEvent19,adverseCompleteEvent20,adverseCompleteEvent21,adverseCompleteEvent22,adverseCompleteEvent23,adverseCompleteEvent24,adverseCompleteEvent25,adverseCompleteEvent26,adverseCompleteEvent27,adverseCompleteEvent28,adverseCompleteEvent29,adverseCompleteEvent30,adverseCompleteEvent31,adverseCompleteEvent32,adverseCompleteEvent33,adverseCompleteEvent34,adverseCompleteEvent35,taskReward]
    <;> norm_num
  have hp : rawVisits adverseCompleteS36Before [.query 1,.hydeRetriever 1] = 9 := by decide
  have hn : rawVisits adverseCompleteS36Before ([.query 1,.hydeRetriever 1]++[.selection 0]) = 2 := by decide
  have hz : (controlPenalty savedCref uniformQuoteError unitRoleUnused .complete) adverseCompleteS36Before [.query 1,.hydeRetriever 1] (.selection 0) = 0 := by
    apply control_penalty_empty_of_prior_terminal .complete savedCref uniformQuoteError adverseCompleteS36Before [.query 1,.hydeRetriever 1] (.selection 0) 8 (by decide)
    · decide
    · decide
  unfold indexScore
  rw [hs,hp,hn,hz]
  simp only [BackupStat.mean]
  norm_num

theorem adverseCompleteS36D2Cmp1 : indexScore (7/5) (controlPenalty savedCref uniformQuoteError unitRoleUnused .complete) adverseCompleteS36Before [.query 1,.hydeRetriever 1] (.selection 2) ≤ indexScore (7/5) (controlPenalty savedCref uniformQuoteError unitRoleUnused .complete) adverseCompleteS36Before [.query 1,.hydeRetriever 1] (.selection 1) := by
  rw [adverseCompleteS36D2I1,adverseCompleteS36D2I0]

theorem adverseCompleteS36D2Cmp2 : indexScore (7/5) (controlPenalty savedCref uniformQuoteError unitRoleUnused .complete) adverseCompleteS36Before [.query 1,.hydeRetriever 1] (.selection 3) ≤ indexScore (7/5) (controlPenalty savedCref uniformQuoteError unitRoleUnused .complete) adverseCompleteS36Before [.query 1,.hydeRetriever 1] (.selection 1) := by
  rw [adverseCompleteS36D2I2,adverseCompleteS36D2I0]

theorem adverseCompleteS36D2Cmp3 : indexScore (7/5) (controlPenalty savedCref uniformQuoteError unitRoleUnused .complete) adverseCompleteS36Before [.query 1,.hydeRetriever 1] (.selection 0) ≤ indexScore (7/5) (controlPenalty savedCref uniformQuoteError unitRoleUnused .complete) adverseCompleteS36Before [.query 1,.hydeRetriever 1] (.selection 1) := by
  rw [adverseCompleteS36D2I3,adverseCompleteS36D2I0]

theorem adverseCompleteS36Choice2 : nativeFirstChoice (indexScore (7/5) (controlPenalty savedCref uniformQuoteError unitRoleUnused .complete) adverseCompleteS36Before [.query 1,.hydeRetriever 1]) adverseCompleteS36Before [.query 1,.hydeRetriever 1] = .selection 1 := by
  apply visited_choice_from_ordered_certificate _ _ [.query 1,.hydeRetriever 1] [] [.selection 2,.selection 3,.selection 0] (.selection 1) (by decide)
  · intro a ha
    have ho : orderedLegalAvailable [.query 1,.hydeRetriever 1] = [.selection 1,.selection 2,.selection 3,.selection 0] := by decide
    rw [ho] at ha
    simp only [List.mem_cons,List.not_mem_nil,or_false] at ha
    rcases ha with rfl | rfl | rfl | rfl <;> decide
  · simp
  · intro a ha
    simp only [List.mem_cons,List.not_mem_nil,or_false] at ha
    rcases ha with rfl | rfl | rfl
    · exact adverseCompleteS36D2Cmp1
    · exact adverseCompleteS36D2Cmp2
    · exact adverseCompleteS36D2Cmp3

theorem adverseCompleteS36ActualEvent : nativeEvent budgetTape (7/5) (controlPenalty savedCref uniformQuoteError unitRoleUnused .complete)
    (taskReward true (2/5) (1/2)) adverseCompleteS36Before = adverseCompleteEvent36 := by
  have hs0 := native_select_existing_step budgetTape (7/5) (controlPenalty savedCref uniformQuoteError unitRoleUnused .complete) adverseCompleteS36Before 8 [] (.query 1)
    (by decide) (by decide) adverseCompleteS36Choice0
  have hs1 := native_select_existing_step budgetTape (7/5) (controlPenalty savedCref uniformQuoteError unitRoleUnused .complete) adverseCompleteS36Before 7 [.query 1] (.hydeRetriever 1)
    (by decide) (by decide) adverseCompleteS36Choice1
  have hs2 := native_select_existing_step budgetTape (7/5) (controlPenalty savedCref uniformQuoteError unitRoleUnused .complete) adverseCompleteS36Before 6 [.query 1,.hydeRetriever 1] (.selection 1)
    (by decide) (by decide) adverseCompleteS36Choice2
  have hnew := native_select_new_step budgetTape (7/5) (controlPenalty savedCref uniformQuoteError unitRoleUnused .complete) adverseCompleteS36Before 5 [.query 1,.hydeRetriever 1,.selection 1]
    [.width 3,.width 1,.width 2] (.width 3) (by decide) (by decide) (by decide) (by decide)
  have hs : nativeSelect budgetTape (7/5) (controlPenalty savedCref uniformQuoteError unitRoleUnused .complete) adverseCompleteS36Before 9 [] = [.query 1,.hydeRetriever 1,.selection 1,.width 3] := by
    rw [hs0]
    change nativeSelect budgetTape (7/5) (controlPenalty savedCref uniformQuoteError unitRoleUnused .complete) adverseCompleteS36Before 8 [.query 1] = _
    rw [hs1]
    change nativeSelect budgetTape (7/5) (controlPenalty savedCref uniformQuoteError unitRoleUnused .complete) adverseCompleteS36Before 7 [.query 1,.hydeRetriever 1] = _
    rw [hs2]
    change nativeSelect budgetTape (7/5) (controlPenalty savedCref uniformQuoteError unitRoleUnused .complete) adverseCompleteS36Before 6 [.query 1,.hydeRetriever 1,.selection 1] = _
    rw [hnew] <;> rfl
  have hr : repairedRollout budgetTape adverseCompleteS36Before 9 [.query 1,.hydeRetriever 1,.selection 1,.width 3] = [.query 1,.hydeRetriever 1,.selection 1,.width 3,.stop,.reranker 0,.topm 0,.context 0,.answer 0] := by decide
  simp only [nativeEvent,hs,hr]
  rfl

def adverseCompleteS37Before := adverseCompleteProposal.take 36

theorem adverseCompleteS37Choice0 : nativeFirstChoice (indexScore (7/5) (controlPenalty savedCref uniformQuoteError unitRoleUnused .complete) adverseCompleteS37Before []) adverseCompleteS37Before [] = .query 1 := by
  apply complete_root_from_physical_gap adverseCompleteS37Before (adverseComplete_prefix_rewards 36) (by decide)
  · intro q; fin_cases q <;> decide
  · exact AgentUCTNextExact.adverse_complete_hyde_root_suffix_empty 36 (by omega)
  · intro q hq
    exact AgentUCTNextExact.adverse_complete_normal_root_physical_quote_exact 36 (by omega) q hq

theorem adverseCompleteS37D1I0 : indexScore (7/5) (controlPenalty savedCref uniformQuoteError unitRoleUnused .complete) adverseCompleteS37Before [.query 1] (.hydeRetriever 1) = treeIndex ((0/1)/10) (7/5) 0 29 10 := by
  have hs : replayBackup adverseCompleteS37Before emptyStatistics ([.query 1]++[.hydeRetriever 1]) = ⟨10,(0/1)⟩ := by
    rw [replayBackup_empty_closed_form]
    simp +decide [backedEvents,adverseCompleteS37Before,adverseCompleteProposal,adverseCompleteEvent1,adverseCompleteEvent2,adverseCompleteEvent3,adverseCompleteEvent4,adverseCompleteEvent5,adverseCompleteEvent6,adverseCompleteEvent7,adverseCompleteEvent8,adverseCompleteEvent9,adverseCompleteEvent10,adverseCompleteEvent11,adverseCompleteEvent12,adverseCompleteEvent13,adverseCompleteEvent14,adverseCompleteEvent15,adverseCompleteEvent16,adverseCompleteEvent17,adverseCompleteEvent18,adverseCompleteEvent19,adverseCompleteEvent20,adverseCompleteEvent21,adverseCompleteEvent22,adverseCompleteEvent23,adverseCompleteEvent24,adverseCompleteEvent25,adverseCompleteEvent26,adverseCompleteEvent27,adverseCompleteEvent28,adverseCompleteEvent29,adverseCompleteEvent30,adverseCompleteEvent31,adverseCompleteEvent32,adverseCompleteEvent33,adverseCompleteEvent34,adverseCompleteEvent35,adverseCompleteEvent36,taskReward]
    <;> norm_num
  have hp : rawVisits adverseCompleteS37Before [.query 1] = 29 := by decide
  have hn : rawVisits adverseCompleteS37Before ([.query 1]++[.hydeRetriever 1]) = 10 := by decide
  have hz : (controlPenalty savedCref uniformQuoteError unitRoleUnused .complete) adverseCompleteS37Before [.query 1] (.hydeRetriever 1) = 0 := by
    apply control_penalty_empty_of_prior_terminal .complete savedCref uniformQuoteError adverseCompleteS37Before [.query 1] (.hydeRetriever 1) 8 (by decide)
    · decide
    · decide
  unfold indexScore
  rw [hs,hp,hn,hz]
  simp only [BackupStat.mean]
  norm_num

theorem adverseCompleteS37D1I1 : indexScore (7/5) (controlPenalty savedCref uniformQuoteError unitRoleUnused .complete) adverseCompleteS37Before [.query 1] (.hydeRetriever 0) = treeIndex ((0/1)/9) (7/5) 0 29 9 := by
  have hs : replayBackup adverseCompleteS37Before emptyStatistics ([.query 1]++[.hydeRetriever 0]) = ⟨9,(0/1)⟩ := by
    rw [replayBackup_empty_closed_form]
    simp +decide [backedEvents,adverseCompleteS37Before,adverseCompleteProposal,adverseCompleteEvent1,adverseCompleteEvent2,adverseCompleteEvent3,adverseCompleteEvent4,adverseCompleteEvent5,adverseCompleteEvent6,adverseCompleteEvent7,adverseCompleteEvent8,adverseCompleteEvent9,adverseCompleteEvent10,adverseCompleteEvent11,adverseCompleteEvent12,adverseCompleteEvent13,adverseCompleteEvent14,adverseCompleteEvent15,adverseCompleteEvent16,adverseCompleteEvent17,adverseCompleteEvent18,adverseCompleteEvent19,adverseCompleteEvent20,adverseCompleteEvent21,adverseCompleteEvent22,adverseCompleteEvent23,adverseCompleteEvent24,adverseCompleteEvent25,adverseCompleteEvent26,adverseCompleteEvent27,adverseCompleteEvent28,adverseCompleteEvent29,adverseCompleteEvent30,adverseCompleteEvent31,adverseCompleteEvent32,adverseCompleteEvent33,adverseCompleteEvent34,adverseCompleteEvent35,adverseCompleteEvent36,taskReward]
    <;> norm_num
  have hp : rawVisits adverseCompleteS37Before [.query 1] = 29 := by decide
  have hn : rawVisits adverseCompleteS37Before ([.query 1]++[.hydeRetriever 0]) = 9 := by decide
  have hz : (controlPenalty savedCref uniformQuoteError unitRoleUnused .complete) adverseCompleteS37Before [.query 1] (.hydeRetriever 0) = 0 := by
    apply control_penalty_empty_of_prior_terminal .complete savedCref uniformQuoteError adverseCompleteS37Before [.query 1] (.hydeRetriever 0) 1 (by decide)
    · decide
    · decide
  unfold indexScore
  rw [hs,hp,hn,hz]
  simp only [BackupStat.mean]
  norm_num

theorem adverseCompleteS37D1I2 : indexScore (7/5) (controlPenalty savedCref uniformQuoteError unitRoleUnused .complete) adverseCompleteS37Before [.query 1] (.hydeRetriever 2) = treeIndex ((0/1)/9) (7/5) 0 29 9 := by
  have hs : replayBackup adverseCompleteS37Before emptyStatistics ([.query 1]++[.hydeRetriever 2]) = ⟨9,(0/1)⟩ := by
    rw [replayBackup_empty_closed_form]
    simp +decide [backedEvents,adverseCompleteS37Before,adverseCompleteProposal,adverseCompleteEvent1,adverseCompleteEvent2,adverseCompleteEvent3,adverseCompleteEvent4,adverseCompleteEvent5,adverseCompleteEvent6,adverseCompleteEvent7,adverseCompleteEvent8,adverseCompleteEvent9,adverseCompleteEvent10,adverseCompleteEvent11,adverseCompleteEvent12,adverseCompleteEvent13,adverseCompleteEvent14,adverseCompleteEvent15,adverseCompleteEvent16,adverseCompleteEvent17,adverseCompleteEvent18,adverseCompleteEvent19,adverseCompleteEvent20,adverseCompleteEvent21,adverseCompleteEvent22,adverseCompleteEvent23,adverseCompleteEvent24,adverseCompleteEvent25,adverseCompleteEvent26,adverseCompleteEvent27,adverseCompleteEvent28,adverseCompleteEvent29,adverseCompleteEvent30,adverseCompleteEvent31,adverseCompleteEvent32,adverseCompleteEvent33,adverseCompleteEvent34,adverseCompleteEvent35,adverseCompleteEvent36,taskReward]
    <;> norm_num
  have hp : rawVisits adverseCompleteS37Before [.query 1] = 29 := by decide
  have hn : rawVisits adverseCompleteS37Before ([.query 1]++[.hydeRetriever 2]) = 9 := by decide
  have hz : (controlPenalty savedCref uniformQuoteError unitRoleUnused .complete) adverseCompleteS37Before [.query 1] (.hydeRetriever 2) = 0 := by
    apply control_penalty_empty_of_prior_terminal .complete savedCref uniformQuoteError adverseCompleteS37Before [.query 1] (.hydeRetriever 2) 10 (by decide)
    · decide
    · decide
  unfold indexScore
  rw [hs,hp,hn,hz]
  simp only [BackupStat.mean]
  norm_num

theorem adverseCompleteS37D1Cmp0 : indexScore (7/5) (controlPenalty savedCref uniformQuoteError unitRoleUnused .complete) adverseCompleteS37Before [.query 1] (.hydeRetriever 1) < indexScore (7/5) (controlPenalty savedCref uniformQuoteError unitRoleUnused .complete) adverseCompleteS37Before [.query 1] (.hydeRetriever 0) := by
  rw [adverseCompleteS37D1I0,adverseCompleteS37D1I1]
  have h := index_strict_order_from_intervals ((0/1)/9) ((0/1)/10) 0 0 (8606423/10000000) (40823853/50000000)
    (treeBonus (7/5) 29 9) (treeBonus (7/5) 29 10)
    (trajectory_bonus_29_9).1 (trajectory_bonus_29_10).2 (by norm_num)
  simpa only [treeIndex,sub_zero] using h

theorem adverseCompleteS37D1Cmp2 : indexScore (7/5) (controlPenalty savedCref uniformQuoteError unitRoleUnused .complete) adverseCompleteS37Before [.query 1] (.hydeRetriever 2) ≤ indexScore (7/5) (controlPenalty savedCref uniformQuoteError unitRoleUnused .complete) adverseCompleteS37Before [.query 1] (.hydeRetriever 0) := by
  rw [adverseCompleteS37D1I2,adverseCompleteS37D1I1]

theorem adverseCompleteS37Choice1 : nativeFirstChoice (indexScore (7/5) (controlPenalty savedCref uniformQuoteError unitRoleUnused .complete) adverseCompleteS37Before [.query 1]) adverseCompleteS37Before [.query 1] = .hydeRetriever 0 := by
  apply visited_choice_from_ordered_certificate _ _ [.query 1] [.hydeRetriever 1] [.hydeRetriever 2] (.hydeRetriever 0) (by decide)
  · intro a ha
    have ho : orderedLegalAvailable [.query 1] = [.hydeRetriever 1,.hydeRetriever 0,.hydeRetriever 2] := by decide
    rw [ho] at ha
    simp only [List.mem_cons,List.not_mem_nil,or_false] at ha
    rcases ha with rfl | rfl | rfl <;> decide
  · intro a ha
    simp only [List.mem_cons,List.not_mem_nil,or_false] at ha
    rcases ha with rfl
    · exact adverseCompleteS37D1Cmp0
  · intro a ha
    simp only [List.mem_cons,List.not_mem_nil,or_false] at ha
    rcases ha with rfl
    · exact adverseCompleteS37D1Cmp2

theorem adverseCompleteS37D2I0 : indexScore (7/5) (controlPenalty savedCref uniformQuoteError unitRoleUnused .complete) adverseCompleteS37Before [.query 1,.hydeRetriever 0] (.selection 1) = treeIndex ((0/1)/2) (7/5) 0 9 2 := by
  have hs : replayBackup adverseCompleteS37Before emptyStatistics ([.query 1,.hydeRetriever 0]++[.selection 1]) = ⟨2,(0/1)⟩ := by
    rw [replayBackup_empty_closed_form]
    simp +decide [backedEvents,adverseCompleteS37Before,adverseCompleteProposal,adverseCompleteEvent1,adverseCompleteEvent2,adverseCompleteEvent3,adverseCompleteEvent4,adverseCompleteEvent5,adverseCompleteEvent6,adverseCompleteEvent7,adverseCompleteEvent8,adverseCompleteEvent9,adverseCompleteEvent10,adverseCompleteEvent11,adverseCompleteEvent12,adverseCompleteEvent13,adverseCompleteEvent14,adverseCompleteEvent15,adverseCompleteEvent16,adverseCompleteEvent17,adverseCompleteEvent18,adverseCompleteEvent19,adverseCompleteEvent20,adverseCompleteEvent21,adverseCompleteEvent22,adverseCompleteEvent23,adverseCompleteEvent24,adverseCompleteEvent25,adverseCompleteEvent26,adverseCompleteEvent27,adverseCompleteEvent28,adverseCompleteEvent29,adverseCompleteEvent30,adverseCompleteEvent31,adverseCompleteEvent32,adverseCompleteEvent33,adverseCompleteEvent34,adverseCompleteEvent35,adverseCompleteEvent36,taskReward]
    <;> norm_num
  have hp : rawVisits adverseCompleteS37Before [.query 1,.hydeRetriever 0] = 9 := by decide
  have hn : rawVisits adverseCompleteS37Before ([.query 1,.hydeRetriever 0]++[.selection 1]) = 2 := by decide
  have hz : (controlPenalty savedCref uniformQuoteError unitRoleUnused .complete) adverseCompleteS37Before [.query 1,.hydeRetriever 0] (.selection 1) = 0 := by
    apply control_penalty_empty_of_prior_terminal .complete savedCref uniformQuoteError adverseCompleteS37Before [.query 1,.hydeRetriever 0] (.selection 1) 15 (by decide)
    · decide
    · decide
  unfold indexScore
  rw [hs,hp,hn,hz]
  simp only [BackupStat.mean]
  norm_num

theorem adverseCompleteS37D2I1 : indexScore (7/5) (controlPenalty savedCref uniformQuoteError unitRoleUnused .complete) adverseCompleteS37Before [.query 1,.hydeRetriever 0] (.selection 2) = treeIndex ((0/1)/2) (7/5) 0 9 2 := by
  have hs : replayBackup adverseCompleteS37Before emptyStatistics ([.query 1,.hydeRetriever 0]++[.selection 2]) = ⟨2,(0/1)⟩ := by
    rw [replayBackup_empty_closed_form]
    simp +decide [backedEvents,adverseCompleteS37Before,adverseCompleteProposal,adverseCompleteEvent1,adverseCompleteEvent2,adverseCompleteEvent3,adverseCompleteEvent4,adverseCompleteEvent5,adverseCompleteEvent6,adverseCompleteEvent7,adverseCompleteEvent8,adverseCompleteEvent9,adverseCompleteEvent10,adverseCompleteEvent11,adverseCompleteEvent12,adverseCompleteEvent13,adverseCompleteEvent14,adverseCompleteEvent15,adverseCompleteEvent16,adverseCompleteEvent17,adverseCompleteEvent18,adverseCompleteEvent19,adverseCompleteEvent20,adverseCompleteEvent21,adverseCompleteEvent22,adverseCompleteEvent23,adverseCompleteEvent24,adverseCompleteEvent25,adverseCompleteEvent26,adverseCompleteEvent27,adverseCompleteEvent28,adverseCompleteEvent29,adverseCompleteEvent30,adverseCompleteEvent31,adverseCompleteEvent32,adverseCompleteEvent33,adverseCompleteEvent34,adverseCompleteEvent35,adverseCompleteEvent36,taskReward]
    <;> norm_num
  have hp : rawVisits adverseCompleteS37Before [.query 1,.hydeRetriever 0] = 9 := by decide
  have hn : rawVisits adverseCompleteS37Before ([.query 1,.hydeRetriever 0]++[.selection 2]) = 2 := by decide
  have hz : (controlPenalty savedCref uniformQuoteError unitRoleUnused .complete) adverseCompleteS37Before [.query 1,.hydeRetriever 0] (.selection 2) = 0 := by
    apply control_penalty_empty_of_prior_terminal .complete savedCref uniformQuoteError adverseCompleteS37Before [.query 1,.hydeRetriever 0] (.selection 2) 18 (by decide)
    · decide
    · decide
  unfold indexScore
  rw [hs,hp,hn,hz]
  simp only [BackupStat.mean]
  norm_num

theorem adverseCompleteS37D2I2 : indexScore (7/5) (controlPenalty savedCref uniformQuoteError unitRoleUnused .complete) adverseCompleteS37Before [.query 1,.hydeRetriever 0] (.selection 3) = treeIndex ((0/1)/2) (7/5) 0 9 2 := by
  have hs : replayBackup adverseCompleteS37Before emptyStatistics ([.query 1,.hydeRetriever 0]++[.selection 3]) = ⟨2,(0/1)⟩ := by
    rw [replayBackup_empty_closed_form]
    simp +decide [backedEvents,adverseCompleteS37Before,adverseCompleteProposal,adverseCompleteEvent1,adverseCompleteEvent2,adverseCompleteEvent3,adverseCompleteEvent4,adverseCompleteEvent5,adverseCompleteEvent6,adverseCompleteEvent7,adverseCompleteEvent8,adverseCompleteEvent9,adverseCompleteEvent10,adverseCompleteEvent11,adverseCompleteEvent12,adverseCompleteEvent13,adverseCompleteEvent14,adverseCompleteEvent15,adverseCompleteEvent16,adverseCompleteEvent17,adverseCompleteEvent18,adverseCompleteEvent19,adverseCompleteEvent20,adverseCompleteEvent21,adverseCompleteEvent22,adverseCompleteEvent23,adverseCompleteEvent24,adverseCompleteEvent25,adverseCompleteEvent26,adverseCompleteEvent27,adverseCompleteEvent28,adverseCompleteEvent29,adverseCompleteEvent30,adverseCompleteEvent31,adverseCompleteEvent32,adverseCompleteEvent33,adverseCompleteEvent34,adverseCompleteEvent35,adverseCompleteEvent36,taskReward]
    <;> norm_num
  have hp : rawVisits adverseCompleteS37Before [.query 1,.hydeRetriever 0] = 9 := by decide
  have hn : rawVisits adverseCompleteS37Before ([.query 1,.hydeRetriever 0]++[.selection 3]) = 2 := by decide
  have hz : (controlPenalty savedCref uniformQuoteError unitRoleUnused .complete) adverseCompleteS37Before [.query 1,.hydeRetriever 0] (.selection 3) = 0 := by
    apply control_penalty_empty_of_prior_terminal .complete savedCref uniformQuoteError adverseCompleteS37Before [.query 1,.hydeRetriever 0] (.selection 3) 21 (by decide)
    · decide
    · decide
  unfold indexScore
  rw [hs,hp,hn,hz]
  simp only [BackupStat.mean]
  norm_num

theorem adverseCompleteS37D2I3 : indexScore (7/5) (controlPenalty savedCref uniformQuoteError unitRoleUnused .complete) adverseCompleteS37Before [.query 1,.hydeRetriever 0] (.selection 0) = treeIndex ((0/1)/2) (7/5) 0 9 2 := by
  have hs : replayBackup adverseCompleteS37Before emptyStatistics ([.query 1,.hydeRetriever 0]++[.selection 0]) = ⟨2,(0/1)⟩ := by
    rw [replayBackup_empty_closed_form]
    simp +decide [backedEvents,adverseCompleteS37Before,adverseCompleteProposal,adverseCompleteEvent1,adverseCompleteEvent2,adverseCompleteEvent3,adverseCompleteEvent4,adverseCompleteEvent5,adverseCompleteEvent6,adverseCompleteEvent7,adverseCompleteEvent8,adverseCompleteEvent9,adverseCompleteEvent10,adverseCompleteEvent11,adverseCompleteEvent12,adverseCompleteEvent13,adverseCompleteEvent14,adverseCompleteEvent15,adverseCompleteEvent16,adverseCompleteEvent17,adverseCompleteEvent18,adverseCompleteEvent19,adverseCompleteEvent20,adverseCompleteEvent21,adverseCompleteEvent22,adverseCompleteEvent23,adverseCompleteEvent24,adverseCompleteEvent25,adverseCompleteEvent26,adverseCompleteEvent27,adverseCompleteEvent28,adverseCompleteEvent29,adverseCompleteEvent30,adverseCompleteEvent31,adverseCompleteEvent32,adverseCompleteEvent33,adverseCompleteEvent34,adverseCompleteEvent35,adverseCompleteEvent36,taskReward]
    <;> norm_num
  have hp : rawVisits adverseCompleteS37Before [.query 1,.hydeRetriever 0] = 9 := by decide
  have hn : rawVisits adverseCompleteS37Before ([.query 1,.hydeRetriever 0]++[.selection 0]) = 2 := by decide
  have hz : (controlPenalty savedCref uniformQuoteError unitRoleUnused .complete) adverseCompleteS37Before [.query 1,.hydeRetriever 0] (.selection 0) = 0 := by
    apply control_penalty_empty_of_prior_terminal .complete savedCref uniformQuoteError adverseCompleteS37Before [.query 1,.hydeRetriever 0] (.selection 0) 1 (by decide)
    · decide
    · decide
  unfold indexScore
  rw [hs,hp,hn,hz]
  simp only [BackupStat.mean]
  norm_num

theorem adverseCompleteS37D2Cmp1 : indexScore (7/5) (controlPenalty savedCref uniformQuoteError unitRoleUnused .complete) adverseCompleteS37Before [.query 1,.hydeRetriever 0] (.selection 2) ≤ indexScore (7/5) (controlPenalty savedCref uniformQuoteError unitRoleUnused .complete) adverseCompleteS37Before [.query 1,.hydeRetriever 0] (.selection 1) := by
  rw [adverseCompleteS37D2I1,adverseCompleteS37D2I0]

theorem adverseCompleteS37D2Cmp2 : indexScore (7/5) (controlPenalty savedCref uniformQuoteError unitRoleUnused .complete) adverseCompleteS37Before [.query 1,.hydeRetriever 0] (.selection 3) ≤ indexScore (7/5) (controlPenalty savedCref uniformQuoteError unitRoleUnused .complete) adverseCompleteS37Before [.query 1,.hydeRetriever 0] (.selection 1) := by
  rw [adverseCompleteS37D2I2,adverseCompleteS37D2I0]

theorem adverseCompleteS37D2Cmp3 : indexScore (7/5) (controlPenalty savedCref uniformQuoteError unitRoleUnused .complete) adverseCompleteS37Before [.query 1,.hydeRetriever 0] (.selection 0) ≤ indexScore (7/5) (controlPenalty savedCref uniformQuoteError unitRoleUnused .complete) adverseCompleteS37Before [.query 1,.hydeRetriever 0] (.selection 1) := by
  rw [adverseCompleteS37D2I3,adverseCompleteS37D2I0]

theorem adverseCompleteS37Choice2 : nativeFirstChoice (indexScore (7/5) (controlPenalty savedCref uniformQuoteError unitRoleUnused .complete) adverseCompleteS37Before [.query 1,.hydeRetriever 0]) adverseCompleteS37Before [.query 1,.hydeRetriever 0] = .selection 1 := by
  apply visited_choice_from_ordered_certificate _ _ [.query 1,.hydeRetriever 0] [] [.selection 2,.selection 3,.selection 0] (.selection 1) (by decide)
  · intro a ha
    have ho : orderedLegalAvailable [.query 1,.hydeRetriever 0] = [.selection 1,.selection 2,.selection 3,.selection 0] := by decide
    rw [ho] at ha
    simp only [List.mem_cons,List.not_mem_nil,or_false] at ha
    rcases ha with rfl | rfl | rfl | rfl <;> decide
  · simp
  · intro a ha
    simp only [List.mem_cons,List.not_mem_nil,or_false] at ha
    rcases ha with rfl | rfl | rfl
    · exact adverseCompleteS37D2Cmp1
    · exact adverseCompleteS37D2Cmp2
    · exact adverseCompleteS37D2Cmp3

theorem adverseCompleteS37ActualEvent : nativeEvent budgetTape (7/5) (controlPenalty savedCref uniformQuoteError unitRoleUnused .complete)
    (taskReward true (2/5) (1/2)) adverseCompleteS37Before = adverseCompleteEvent37 := by
  have hs0 := native_select_existing_step budgetTape (7/5) (controlPenalty savedCref uniformQuoteError unitRoleUnused .complete) adverseCompleteS37Before 8 [] (.query 1)
    (by decide) (by decide) adverseCompleteS37Choice0
  have hs1 := native_select_existing_step budgetTape (7/5) (controlPenalty savedCref uniformQuoteError unitRoleUnused .complete) adverseCompleteS37Before 7 [.query 1] (.hydeRetriever 0)
    (by decide) (by decide) adverseCompleteS37Choice1
  have hs2 := native_select_existing_step budgetTape (7/5) (controlPenalty savedCref uniformQuoteError unitRoleUnused .complete) adverseCompleteS37Before 6 [.query 1,.hydeRetriever 0] (.selection 1)
    (by decide) (by decide) adverseCompleteS37Choice2
  have hnew := native_select_new_step budgetTape (7/5) (controlPenalty savedCref uniformQuoteError unitRoleUnused .complete) adverseCompleteS37Before 5 [.query 1,.hydeRetriever 0,.selection 1]
    [.width 3,.width 1,.width 2] (.width 3) (by decide) (by decide) (by decide) (by decide)
  have hs : nativeSelect budgetTape (7/5) (controlPenalty savedCref uniformQuoteError unitRoleUnused .complete) adverseCompleteS37Before 9 [] = [.query 1,.hydeRetriever 0,.selection 1,.width 3] := by
    rw [hs0]
    change nativeSelect budgetTape (7/5) (controlPenalty savedCref uniformQuoteError unitRoleUnused .complete) adverseCompleteS37Before 8 [.query 1] = _
    rw [hs1]
    change nativeSelect budgetTape (7/5) (controlPenalty savedCref uniformQuoteError unitRoleUnused .complete) adverseCompleteS37Before 7 [.query 1,.hydeRetriever 0] = _
    rw [hs2]
    change nativeSelect budgetTape (7/5) (controlPenalty savedCref uniformQuoteError unitRoleUnused .complete) adverseCompleteS37Before 6 [.query 1,.hydeRetriever 0,.selection 1] = _
    rw [hnew] <;> rfl
  have hr : repairedRollout budgetTape adverseCompleteS37Before 9 [.query 1,.hydeRetriever 0,.selection 1,.width 3] = [.query 1,.hydeRetriever 0,.selection 1,.width 3,.stop,.reranker 0,.topm 0,.context 0,.answer 0] := by decide
  simp only [nativeEvent,hs,hr]
  rfl

def adverseCompleteS38Before := adverseCompleteProposal.take 37

theorem adverseCompleteS38Choice0 : nativeFirstChoice (indexScore (7/5) (controlPenalty savedCref uniformQuoteError unitRoleUnused .complete) adverseCompleteS38Before []) adverseCompleteS38Before [] = .query 1 := by
  apply complete_root_from_physical_gap adverseCompleteS38Before (adverseComplete_prefix_rewards 37) (by decide)
  · intro q; fin_cases q <;> decide
  · exact AgentUCTNextExact.adverse_complete_hyde_root_suffix_empty 37 (by omega)
  · intro q hq
    exact AgentUCTNextExact.adverse_complete_normal_root_physical_quote_exact 37 (by omega) q hq

theorem adverseCompleteS38D1I0 : indexScore (7/5) (controlPenalty savedCref uniformQuoteError unitRoleUnused .complete) adverseCompleteS38Before [.query 1] (.hydeRetriever 1) = treeIndex ((0/1)/10) (7/5) 0 30 10 := by
  have hs : replayBackup adverseCompleteS38Before emptyStatistics ([.query 1]++[.hydeRetriever 1]) = ⟨10,(0/1)⟩ := by
    rw [replayBackup_empty_closed_form]
    simp +decide [backedEvents,adverseCompleteS38Before,adverseCompleteProposal,adverseCompleteEvent1,adverseCompleteEvent2,adverseCompleteEvent3,adverseCompleteEvent4,adverseCompleteEvent5,adverseCompleteEvent6,adverseCompleteEvent7,adverseCompleteEvent8,adverseCompleteEvent9,adverseCompleteEvent10,adverseCompleteEvent11,adverseCompleteEvent12,adverseCompleteEvent13,adverseCompleteEvent14,adverseCompleteEvent15,adverseCompleteEvent16,adverseCompleteEvent17,adverseCompleteEvent18,adverseCompleteEvent19,adverseCompleteEvent20,adverseCompleteEvent21,adverseCompleteEvent22,adverseCompleteEvent23,adverseCompleteEvent24,adverseCompleteEvent25,adverseCompleteEvent26,adverseCompleteEvent27,adverseCompleteEvent28,adverseCompleteEvent29,adverseCompleteEvent30,adverseCompleteEvent31,adverseCompleteEvent32,adverseCompleteEvent33,adverseCompleteEvent34,adverseCompleteEvent35,adverseCompleteEvent36,adverseCompleteEvent37,taskReward]
    <;> norm_num
  have hp : rawVisits adverseCompleteS38Before [.query 1] = 30 := by decide
  have hn : rawVisits adverseCompleteS38Before ([.query 1]++[.hydeRetriever 1]) = 10 := by decide
  have hz : (controlPenalty savedCref uniformQuoteError unitRoleUnused .complete) adverseCompleteS38Before [.query 1] (.hydeRetriever 1) = 0 := by
    apply control_penalty_empty_of_prior_terminal .complete savedCref uniformQuoteError adverseCompleteS38Before [.query 1] (.hydeRetriever 1) 8 (by decide)
    · decide
    · decide
  unfold indexScore
  rw [hs,hp,hn,hz]
  simp only [BackupStat.mean]
  norm_num

theorem adverseCompleteS38D1I1 : indexScore (7/5) (controlPenalty savedCref uniformQuoteError unitRoleUnused .complete) adverseCompleteS38Before [.query 1] (.hydeRetriever 0) = treeIndex ((0/1)/10) (7/5) 0 30 10 := by
  have hs : replayBackup adverseCompleteS38Before emptyStatistics ([.query 1]++[.hydeRetriever 0]) = ⟨10,(0/1)⟩ := by
    rw [replayBackup_empty_closed_form]
    simp +decide [backedEvents,adverseCompleteS38Before,adverseCompleteProposal,adverseCompleteEvent1,adverseCompleteEvent2,adverseCompleteEvent3,adverseCompleteEvent4,adverseCompleteEvent5,adverseCompleteEvent6,adverseCompleteEvent7,adverseCompleteEvent8,adverseCompleteEvent9,adverseCompleteEvent10,adverseCompleteEvent11,adverseCompleteEvent12,adverseCompleteEvent13,adverseCompleteEvent14,adverseCompleteEvent15,adverseCompleteEvent16,adverseCompleteEvent17,adverseCompleteEvent18,adverseCompleteEvent19,adverseCompleteEvent20,adverseCompleteEvent21,adverseCompleteEvent22,adverseCompleteEvent23,adverseCompleteEvent24,adverseCompleteEvent25,adverseCompleteEvent26,adverseCompleteEvent27,adverseCompleteEvent28,adverseCompleteEvent29,adverseCompleteEvent30,adverseCompleteEvent31,adverseCompleteEvent32,adverseCompleteEvent33,adverseCompleteEvent34,adverseCompleteEvent35,adverseCompleteEvent36,adverseCompleteEvent37,taskReward]
    <;> norm_num
  have hp : rawVisits adverseCompleteS38Before [.query 1] = 30 := by decide
  have hn : rawVisits adverseCompleteS38Before ([.query 1]++[.hydeRetriever 0]) = 10 := by decide
  have hz : (controlPenalty savedCref uniformQuoteError unitRoleUnused .complete) adverseCompleteS38Before [.query 1] (.hydeRetriever 0) = 0 := by
    apply control_penalty_empty_of_prior_terminal .complete savedCref uniformQuoteError adverseCompleteS38Before [.query 1] (.hydeRetriever 0) 1 (by decide)
    · decide
    · decide
  unfold indexScore
  rw [hs,hp,hn,hz]
  simp only [BackupStat.mean]
  norm_num

theorem adverseCompleteS38D1I2 : indexScore (7/5) (controlPenalty savedCref uniformQuoteError unitRoleUnused .complete) adverseCompleteS38Before [.query 1] (.hydeRetriever 2) = treeIndex ((0/1)/9) (7/5) 0 30 9 := by
  have hs : replayBackup adverseCompleteS38Before emptyStatistics ([.query 1]++[.hydeRetriever 2]) = ⟨9,(0/1)⟩ := by
    rw [replayBackup_empty_closed_form]
    simp +decide [backedEvents,adverseCompleteS38Before,adverseCompleteProposal,adverseCompleteEvent1,adverseCompleteEvent2,adverseCompleteEvent3,adverseCompleteEvent4,adverseCompleteEvent5,adverseCompleteEvent6,adverseCompleteEvent7,adverseCompleteEvent8,adverseCompleteEvent9,adverseCompleteEvent10,adverseCompleteEvent11,adverseCompleteEvent12,adverseCompleteEvent13,adverseCompleteEvent14,adverseCompleteEvent15,adverseCompleteEvent16,adverseCompleteEvent17,adverseCompleteEvent18,adverseCompleteEvent19,adverseCompleteEvent20,adverseCompleteEvent21,adverseCompleteEvent22,adverseCompleteEvent23,adverseCompleteEvent24,adverseCompleteEvent25,adverseCompleteEvent26,adverseCompleteEvent27,adverseCompleteEvent28,adverseCompleteEvent29,adverseCompleteEvent30,adverseCompleteEvent31,adverseCompleteEvent32,adverseCompleteEvent33,adverseCompleteEvent34,adverseCompleteEvent35,adverseCompleteEvent36,adverseCompleteEvent37,taskReward]
    <;> norm_num
  have hp : rawVisits adverseCompleteS38Before [.query 1] = 30 := by decide
  have hn : rawVisits adverseCompleteS38Before ([.query 1]++[.hydeRetriever 2]) = 9 := by decide
  have hz : (controlPenalty savedCref uniformQuoteError unitRoleUnused .complete) adverseCompleteS38Before [.query 1] (.hydeRetriever 2) = 0 := by
    apply control_penalty_empty_of_prior_terminal .complete savedCref uniformQuoteError adverseCompleteS38Before [.query 1] (.hydeRetriever 2) 10 (by decide)
    · decide
    · decide
  unfold indexScore
  rw [hs,hp,hn,hz]
  simp only [BackupStat.mean]
  norm_num

theorem adverseCompleteS38D1Cmp0 : indexScore (7/5) (controlPenalty savedCref uniformQuoteError unitRoleUnused .complete) adverseCompleteS38Before [.query 1] (.hydeRetriever 1) < indexScore (7/5) (controlPenalty savedCref uniformQuoteError unitRoleUnused .complete) adverseCompleteS38Before [.query 1] (.hydeRetriever 2) := by
  rw [adverseCompleteS38D1I0,adverseCompleteS38D1I2]
  have h := index_strict_order_from_intervals ((0/1)/9) ((0/1)/10) 0 0 (21619521/25000000) (5127521/6250000)
    (treeBonus (7/5) 30 9) (treeBonus (7/5) 30 10)
    (trajectory_bonus_30_9).1 (trajectory_bonus_30_10).2 (by norm_num)
  simpa only [treeIndex,sub_zero] using h

theorem adverseCompleteS38D1Cmp1 : indexScore (7/5) (controlPenalty savedCref uniformQuoteError unitRoleUnused .complete) adverseCompleteS38Before [.query 1] (.hydeRetriever 0) < indexScore (7/5) (controlPenalty savedCref uniformQuoteError unitRoleUnused .complete) adverseCompleteS38Before [.query 1] (.hydeRetriever 2) := by
  rw [adverseCompleteS38D1I1,adverseCompleteS38D1I2]
  have h := index_strict_order_from_intervals ((0/1)/9) ((0/1)/10) 0 0 (21619521/25000000) (5127521/6250000)
    (treeBonus (7/5) 30 9) (treeBonus (7/5) 30 10)
    (trajectory_bonus_30_9).1 (trajectory_bonus_30_10).2 (by norm_num)
  simpa only [treeIndex,sub_zero] using h

theorem adverseCompleteS38Choice1 : nativeFirstChoice (indexScore (7/5) (controlPenalty savedCref uniformQuoteError unitRoleUnused .complete) adverseCompleteS38Before [.query 1]) adverseCompleteS38Before [.query 1] = .hydeRetriever 2 := by
  apply visited_choice_from_ordered_certificate _ _ [.query 1] [.hydeRetriever 1,.hydeRetriever 0] [] (.hydeRetriever 2) (by decide)
  · intro a ha
    have ho : orderedLegalAvailable [.query 1] = [.hydeRetriever 1,.hydeRetriever 0,.hydeRetriever 2] := by decide
    rw [ho] at ha
    simp only [List.mem_cons,List.not_mem_nil,or_false] at ha
    rcases ha with rfl | rfl | rfl <;> decide
  · intro a ha
    simp only [List.mem_cons,List.not_mem_nil,or_false] at ha
    rcases ha with rfl | rfl
    · exact adverseCompleteS38D1Cmp0
    · exact adverseCompleteS38D1Cmp1
  · simp

theorem adverseCompleteS38D2I0 : indexScore (7/5) (controlPenalty savedCref uniformQuoteError unitRoleUnused .complete) adverseCompleteS38Before [.query 1,.hydeRetriever 2] (.selection 1) = treeIndex ((0/1)/2) (7/5) 0 9 2 := by
  have hs : replayBackup adverseCompleteS38Before emptyStatistics ([.query 1,.hydeRetriever 2]++[.selection 1]) = ⟨2,(0/1)⟩ := by
    rw [replayBackup_empty_closed_form]
    simp +decide [backedEvents,adverseCompleteS38Before,adverseCompleteProposal,adverseCompleteEvent1,adverseCompleteEvent2,adverseCompleteEvent3,adverseCompleteEvent4,adverseCompleteEvent5,adverseCompleteEvent6,adverseCompleteEvent7,adverseCompleteEvent8,adverseCompleteEvent9,adverseCompleteEvent10,adverseCompleteEvent11,adverseCompleteEvent12,adverseCompleteEvent13,adverseCompleteEvent14,adverseCompleteEvent15,adverseCompleteEvent16,adverseCompleteEvent17,adverseCompleteEvent18,adverseCompleteEvent19,adverseCompleteEvent20,adverseCompleteEvent21,adverseCompleteEvent22,adverseCompleteEvent23,adverseCompleteEvent24,adverseCompleteEvent25,adverseCompleteEvent26,adverseCompleteEvent27,adverseCompleteEvent28,adverseCompleteEvent29,adverseCompleteEvent30,adverseCompleteEvent31,adverseCompleteEvent32,adverseCompleteEvent33,adverseCompleteEvent34,adverseCompleteEvent35,adverseCompleteEvent36,adverseCompleteEvent37,taskReward]
    <;> norm_num
  have hp : rawVisits adverseCompleteS38Before [.query 1,.hydeRetriever 2] = 9 := by decide
  have hn : rawVisits adverseCompleteS38Before ([.query 1,.hydeRetriever 2]++[.selection 1]) = 2 := by decide
  have hz : (controlPenalty savedCref uniformQuoteError unitRoleUnused .complete) adverseCompleteS38Before [.query 1,.hydeRetriever 2] (.selection 1) = 0 := by
    apply control_penalty_empty_of_prior_terminal .complete savedCref uniformQuoteError adverseCompleteS38Before [.query 1,.hydeRetriever 2] (.selection 1) 16 (by decide)
    · decide
    · decide
  unfold indexScore
  rw [hs,hp,hn,hz]
  simp only [BackupStat.mean]
  norm_num

theorem adverseCompleteS38D2I1 : indexScore (7/5) (controlPenalty savedCref uniformQuoteError unitRoleUnused .complete) adverseCompleteS38Before [.query 1,.hydeRetriever 2] (.selection 2) = treeIndex ((0/1)/2) (7/5) 0 9 2 := by
  have hs : replayBackup adverseCompleteS38Before emptyStatistics ([.query 1,.hydeRetriever 2]++[.selection 2]) = ⟨2,(0/1)⟩ := by
    rw [replayBackup_empty_closed_form]
    simp +decide [backedEvents,adverseCompleteS38Before,adverseCompleteProposal,adverseCompleteEvent1,adverseCompleteEvent2,adverseCompleteEvent3,adverseCompleteEvent4,adverseCompleteEvent5,adverseCompleteEvent6,adverseCompleteEvent7,adverseCompleteEvent8,adverseCompleteEvent9,adverseCompleteEvent10,adverseCompleteEvent11,adverseCompleteEvent12,adverseCompleteEvent13,adverseCompleteEvent14,adverseCompleteEvent15,adverseCompleteEvent16,adverseCompleteEvent17,adverseCompleteEvent18,adverseCompleteEvent19,adverseCompleteEvent20,adverseCompleteEvent21,adverseCompleteEvent22,adverseCompleteEvent23,adverseCompleteEvent24,adverseCompleteEvent25,adverseCompleteEvent26,adverseCompleteEvent27,adverseCompleteEvent28,adverseCompleteEvent29,adverseCompleteEvent30,adverseCompleteEvent31,adverseCompleteEvent32,adverseCompleteEvent33,adverseCompleteEvent34,adverseCompleteEvent35,adverseCompleteEvent36,adverseCompleteEvent37,taskReward]
    <;> norm_num
  have hp : rawVisits adverseCompleteS38Before [.query 1,.hydeRetriever 2] = 9 := by decide
  have hn : rawVisits adverseCompleteS38Before ([.query 1,.hydeRetriever 2]++[.selection 2]) = 2 := by decide
  have hz : (controlPenalty savedCref uniformQuoteError unitRoleUnused .complete) adverseCompleteS38Before [.query 1,.hydeRetriever 2] (.selection 2) = 0 := by
    apply control_penalty_empty_of_prior_terminal .complete savedCref uniformQuoteError adverseCompleteS38Before [.query 1,.hydeRetriever 2] (.selection 2) 19 (by decide)
    · decide
    · decide
  unfold indexScore
  rw [hs,hp,hn,hz]
  simp only [BackupStat.mean]
  norm_num

theorem adverseCompleteS38D2I2 : indexScore (7/5) (controlPenalty savedCref uniformQuoteError unitRoleUnused .complete) adverseCompleteS38Before [.query 1,.hydeRetriever 2] (.selection 3) = treeIndex ((0/1)/2) (7/5) 0 9 2 := by
  have hs : replayBackup adverseCompleteS38Before emptyStatistics ([.query 1,.hydeRetriever 2]++[.selection 3]) = ⟨2,(0/1)⟩ := by
    rw [replayBackup_empty_closed_form]
    simp +decide [backedEvents,adverseCompleteS38Before,adverseCompleteProposal,adverseCompleteEvent1,adverseCompleteEvent2,adverseCompleteEvent3,adverseCompleteEvent4,adverseCompleteEvent5,adverseCompleteEvent6,adverseCompleteEvent7,adverseCompleteEvent8,adverseCompleteEvent9,adverseCompleteEvent10,adverseCompleteEvent11,adverseCompleteEvent12,adverseCompleteEvent13,adverseCompleteEvent14,adverseCompleteEvent15,adverseCompleteEvent16,adverseCompleteEvent17,adverseCompleteEvent18,adverseCompleteEvent19,adverseCompleteEvent20,adverseCompleteEvent21,adverseCompleteEvent22,adverseCompleteEvent23,adverseCompleteEvent24,adverseCompleteEvent25,adverseCompleteEvent26,adverseCompleteEvent27,adverseCompleteEvent28,adverseCompleteEvent29,adverseCompleteEvent30,adverseCompleteEvent31,adverseCompleteEvent32,adverseCompleteEvent33,adverseCompleteEvent34,adverseCompleteEvent35,adverseCompleteEvent36,adverseCompleteEvent37,taskReward]
    <;> norm_num
  have hp : rawVisits adverseCompleteS38Before [.query 1,.hydeRetriever 2] = 9 := by decide
  have hn : rawVisits adverseCompleteS38Before ([.query 1,.hydeRetriever 2]++[.selection 3]) = 2 := by decide
  have hz : (controlPenalty savedCref uniformQuoteError unitRoleUnused .complete) adverseCompleteS38Before [.query 1,.hydeRetriever 2] (.selection 3) = 0 := by
    apply control_penalty_empty_of_prior_terminal .complete savedCref uniformQuoteError adverseCompleteS38Before [.query 1,.hydeRetriever 2] (.selection 3) 22 (by decide)
    · decide
    · decide
  unfold indexScore
  rw [hs,hp,hn,hz]
  simp only [BackupStat.mean]
  norm_num

theorem adverseCompleteS38D2I3 : indexScore (7/5) (controlPenalty savedCref uniformQuoteError unitRoleUnused .complete) adverseCompleteS38Before [.query 1,.hydeRetriever 2] (.selection 0) = treeIndex ((0/1)/2) (7/5) 0 9 2 := by
  have hs : replayBackup adverseCompleteS38Before emptyStatistics ([.query 1,.hydeRetriever 2]++[.selection 0]) = ⟨2,(0/1)⟩ := by
    rw [replayBackup_empty_closed_form]
    simp +decide [backedEvents,adverseCompleteS38Before,adverseCompleteProposal,adverseCompleteEvent1,adverseCompleteEvent2,adverseCompleteEvent3,adverseCompleteEvent4,adverseCompleteEvent5,adverseCompleteEvent6,adverseCompleteEvent7,adverseCompleteEvent8,adverseCompleteEvent9,adverseCompleteEvent10,adverseCompleteEvent11,adverseCompleteEvent12,adverseCompleteEvent13,adverseCompleteEvent14,adverseCompleteEvent15,adverseCompleteEvent16,adverseCompleteEvent17,adverseCompleteEvent18,adverseCompleteEvent19,adverseCompleteEvent20,adverseCompleteEvent21,adverseCompleteEvent22,adverseCompleteEvent23,adverseCompleteEvent24,adverseCompleteEvent25,adverseCompleteEvent26,adverseCompleteEvent27,adverseCompleteEvent28,adverseCompleteEvent29,adverseCompleteEvent30,adverseCompleteEvent31,adverseCompleteEvent32,adverseCompleteEvent33,adverseCompleteEvent34,adverseCompleteEvent35,adverseCompleteEvent36,adverseCompleteEvent37,taskReward]
    <;> norm_num
  have hp : rawVisits adverseCompleteS38Before [.query 1,.hydeRetriever 2] = 9 := by decide
  have hn : rawVisits adverseCompleteS38Before ([.query 1,.hydeRetriever 2]++[.selection 0]) = 2 := by decide
  have hz : (controlPenalty savedCref uniformQuoteError unitRoleUnused .complete) adverseCompleteS38Before [.query 1,.hydeRetriever 2] (.selection 0) = 0 := by
    apply control_penalty_empty_of_prior_terminal .complete savedCref uniformQuoteError adverseCompleteS38Before [.query 1,.hydeRetriever 2] (.selection 0) 10 (by decide)
    · decide
    · decide
  unfold indexScore
  rw [hs,hp,hn,hz]
  simp only [BackupStat.mean]
  norm_num

theorem adverseCompleteS38D2Cmp1 : indexScore (7/5) (controlPenalty savedCref uniformQuoteError unitRoleUnused .complete) adverseCompleteS38Before [.query 1,.hydeRetriever 2] (.selection 2) ≤ indexScore (7/5) (controlPenalty savedCref uniformQuoteError unitRoleUnused .complete) adverseCompleteS38Before [.query 1,.hydeRetriever 2] (.selection 1) := by
  rw [adverseCompleteS38D2I1,adverseCompleteS38D2I0]

theorem adverseCompleteS38D2Cmp2 : indexScore (7/5) (controlPenalty savedCref uniformQuoteError unitRoleUnused .complete) adverseCompleteS38Before [.query 1,.hydeRetriever 2] (.selection 3) ≤ indexScore (7/5) (controlPenalty savedCref uniformQuoteError unitRoleUnused .complete) adverseCompleteS38Before [.query 1,.hydeRetriever 2] (.selection 1) := by
  rw [adverseCompleteS38D2I2,adverseCompleteS38D2I0]

theorem adverseCompleteS38D2Cmp3 : indexScore (7/5) (controlPenalty savedCref uniformQuoteError unitRoleUnused .complete) adverseCompleteS38Before [.query 1,.hydeRetriever 2] (.selection 0) ≤ indexScore (7/5) (controlPenalty savedCref uniformQuoteError unitRoleUnused .complete) adverseCompleteS38Before [.query 1,.hydeRetriever 2] (.selection 1) := by
  rw [adverseCompleteS38D2I3,adverseCompleteS38D2I0]

theorem adverseCompleteS38Choice2 : nativeFirstChoice (indexScore (7/5) (controlPenalty savedCref uniformQuoteError unitRoleUnused .complete) adverseCompleteS38Before [.query 1,.hydeRetriever 2]) adverseCompleteS38Before [.query 1,.hydeRetriever 2] = .selection 1 := by
  apply visited_choice_from_ordered_certificate _ _ [.query 1,.hydeRetriever 2] [] [.selection 2,.selection 3,.selection 0] (.selection 1) (by decide)
  · intro a ha
    have ho : orderedLegalAvailable [.query 1,.hydeRetriever 2] = [.selection 1,.selection 2,.selection 3,.selection 0] := by decide
    rw [ho] at ha
    simp only [List.mem_cons,List.not_mem_nil,or_false] at ha
    rcases ha with rfl | rfl | rfl | rfl <;> decide
  · simp
  · intro a ha
    simp only [List.mem_cons,List.not_mem_nil,or_false] at ha
    rcases ha with rfl | rfl | rfl
    · exact adverseCompleteS38D2Cmp1
    · exact adverseCompleteS38D2Cmp2
    · exact adverseCompleteS38D2Cmp3

theorem adverseCompleteS38ActualEvent : nativeEvent budgetTape (7/5) (controlPenalty savedCref uniformQuoteError unitRoleUnused .complete)
    (taskReward true (2/5) (1/2)) adverseCompleteS38Before = adverseCompleteEvent38 := by
  have hs0 := native_select_existing_step budgetTape (7/5) (controlPenalty savedCref uniformQuoteError unitRoleUnused .complete) adverseCompleteS38Before 8 [] (.query 1)
    (by decide) (by decide) adverseCompleteS38Choice0
  have hs1 := native_select_existing_step budgetTape (7/5) (controlPenalty savedCref uniformQuoteError unitRoleUnused .complete) adverseCompleteS38Before 7 [.query 1] (.hydeRetriever 2)
    (by decide) (by decide) adverseCompleteS38Choice1
  have hs2 := native_select_existing_step budgetTape (7/5) (controlPenalty savedCref uniformQuoteError unitRoleUnused .complete) adverseCompleteS38Before 6 [.query 1,.hydeRetriever 2] (.selection 1)
    (by decide) (by decide) adverseCompleteS38Choice2
  have hnew := native_select_new_step budgetTape (7/5) (controlPenalty savedCref uniformQuoteError unitRoleUnused .complete) adverseCompleteS38Before 5 [.query 1,.hydeRetriever 2,.selection 1]
    [.width 3,.width 1,.width 2] (.width 3) (by decide) (by decide) (by decide) (by decide)
  have hs : nativeSelect budgetTape (7/5) (controlPenalty savedCref uniformQuoteError unitRoleUnused .complete) adverseCompleteS38Before 9 [] = [.query 1,.hydeRetriever 2,.selection 1,.width 3] := by
    rw [hs0]
    change nativeSelect budgetTape (7/5) (controlPenalty savedCref uniformQuoteError unitRoleUnused .complete) adverseCompleteS38Before 8 [.query 1] = _
    rw [hs1]
    change nativeSelect budgetTape (7/5) (controlPenalty savedCref uniformQuoteError unitRoleUnused .complete) adverseCompleteS38Before 7 [.query 1,.hydeRetriever 2] = _
    rw [hs2]
    change nativeSelect budgetTape (7/5) (controlPenalty savedCref uniformQuoteError unitRoleUnused .complete) adverseCompleteS38Before 6 [.query 1,.hydeRetriever 2,.selection 1] = _
    rw [hnew] <;> rfl
  have hr : repairedRollout budgetTape adverseCompleteS38Before 9 [.query 1,.hydeRetriever 2,.selection 1,.width 3] = [.query 1,.hydeRetriever 2,.selection 1,.width 3,.stop,.reranker 0,.topm 0,.context 0,.answer 0] := by decide
  simp only [nativeEvent,hs,hr]
  rfl

def adverseCompleteS39Before := adverseCompleteProposal.take 38

theorem adverseCompleteS39Choice0 : nativeFirstChoice (indexScore (7/5) (controlPenalty savedCref uniformQuoteError unitRoleUnused .complete) adverseCompleteS39Before []) adverseCompleteS39Before [] = .query 1 := by
  apply complete_root_from_physical_gap adverseCompleteS39Before (adverseComplete_prefix_rewards 38) (by decide)
  · intro q; fin_cases q <;> decide
  · exact AgentUCTNextExact.adverse_complete_hyde_root_suffix_empty 38 (by omega)
  · intro q hq
    exact AgentUCTNextExact.adverse_complete_normal_root_physical_quote_exact 38 (by omega) q hq

theorem adverseCompleteS39D1I0 : indexScore (7/5) (controlPenalty savedCref uniformQuoteError unitRoleUnused .complete) adverseCompleteS39Before [.query 1] (.hydeRetriever 1) = treeIndex ((0/1)/10) (7/5) 0 31 10 := by
  have hs : replayBackup adverseCompleteS39Before emptyStatistics ([.query 1]++[.hydeRetriever 1]) = ⟨10,(0/1)⟩ := by
    rw [replayBackup_empty_closed_form]
    simp +decide [backedEvents,adverseCompleteS39Before,adverseCompleteProposal,adverseCompleteEvent1,adverseCompleteEvent2,adverseCompleteEvent3,adverseCompleteEvent4,adverseCompleteEvent5,adverseCompleteEvent6,adverseCompleteEvent7,adverseCompleteEvent8,adverseCompleteEvent9,adverseCompleteEvent10,adverseCompleteEvent11,adverseCompleteEvent12,adverseCompleteEvent13,adverseCompleteEvent14,adverseCompleteEvent15,adverseCompleteEvent16,adverseCompleteEvent17,adverseCompleteEvent18,adverseCompleteEvent19,adverseCompleteEvent20,adverseCompleteEvent21,adverseCompleteEvent22,adverseCompleteEvent23,adverseCompleteEvent24,adverseCompleteEvent25,adverseCompleteEvent26,adverseCompleteEvent27,adverseCompleteEvent28,adverseCompleteEvent29,adverseCompleteEvent30,adverseCompleteEvent31,adverseCompleteEvent32,adverseCompleteEvent33,adverseCompleteEvent34,adverseCompleteEvent35,adverseCompleteEvent36,adverseCompleteEvent37,adverseCompleteEvent38,taskReward]
    <;> norm_num
  have hp : rawVisits adverseCompleteS39Before [.query 1] = 31 := by decide
  have hn : rawVisits adverseCompleteS39Before ([.query 1]++[.hydeRetriever 1]) = 10 := by decide
  have hz : (controlPenalty savedCref uniformQuoteError unitRoleUnused .complete) adverseCompleteS39Before [.query 1] (.hydeRetriever 1) = 0 := by
    apply control_penalty_empty_of_prior_terminal .complete savedCref uniformQuoteError adverseCompleteS39Before [.query 1] (.hydeRetriever 1) 8 (by decide)
    · decide
    · decide
  unfold indexScore
  rw [hs,hp,hn,hz]
  simp only [BackupStat.mean]
  norm_num

theorem adverseCompleteS39D1I1 : indexScore (7/5) (controlPenalty savedCref uniformQuoteError unitRoleUnused .complete) adverseCompleteS39Before [.query 1] (.hydeRetriever 0) = treeIndex ((0/1)/10) (7/5) 0 31 10 := by
  have hs : replayBackup adverseCompleteS39Before emptyStatistics ([.query 1]++[.hydeRetriever 0]) = ⟨10,(0/1)⟩ := by
    rw [replayBackup_empty_closed_form]
    simp +decide [backedEvents,adverseCompleteS39Before,adverseCompleteProposal,adverseCompleteEvent1,adverseCompleteEvent2,adverseCompleteEvent3,adverseCompleteEvent4,adverseCompleteEvent5,adverseCompleteEvent6,adverseCompleteEvent7,adverseCompleteEvent8,adverseCompleteEvent9,adverseCompleteEvent10,adverseCompleteEvent11,adverseCompleteEvent12,adverseCompleteEvent13,adverseCompleteEvent14,adverseCompleteEvent15,adverseCompleteEvent16,adverseCompleteEvent17,adverseCompleteEvent18,adverseCompleteEvent19,adverseCompleteEvent20,adverseCompleteEvent21,adverseCompleteEvent22,adverseCompleteEvent23,adverseCompleteEvent24,adverseCompleteEvent25,adverseCompleteEvent26,adverseCompleteEvent27,adverseCompleteEvent28,adverseCompleteEvent29,adverseCompleteEvent30,adverseCompleteEvent31,adverseCompleteEvent32,adverseCompleteEvent33,adverseCompleteEvent34,adverseCompleteEvent35,adverseCompleteEvent36,adverseCompleteEvent37,adverseCompleteEvent38,taskReward]
    <;> norm_num
  have hp : rawVisits adverseCompleteS39Before [.query 1] = 31 := by decide
  have hn : rawVisits adverseCompleteS39Before ([.query 1]++[.hydeRetriever 0]) = 10 := by decide
  have hz : (controlPenalty savedCref uniformQuoteError unitRoleUnused .complete) adverseCompleteS39Before [.query 1] (.hydeRetriever 0) = 0 := by
    apply control_penalty_empty_of_prior_terminal .complete savedCref uniformQuoteError adverseCompleteS39Before [.query 1] (.hydeRetriever 0) 1 (by decide)
    · decide
    · decide
  unfold indexScore
  rw [hs,hp,hn,hz]
  simp only [BackupStat.mean]
  norm_num

theorem adverseCompleteS39D1I2 : indexScore (7/5) (controlPenalty savedCref uniformQuoteError unitRoleUnused .complete) adverseCompleteS39Before [.query 1] (.hydeRetriever 2) = treeIndex ((0/1)/10) (7/5) 0 31 10 := by
  have hs : replayBackup adverseCompleteS39Before emptyStatistics ([.query 1]++[.hydeRetriever 2]) = ⟨10,(0/1)⟩ := by
    rw [replayBackup_empty_closed_form]
    simp +decide [backedEvents,adverseCompleteS39Before,adverseCompleteProposal,adverseCompleteEvent1,adverseCompleteEvent2,adverseCompleteEvent3,adverseCompleteEvent4,adverseCompleteEvent5,adverseCompleteEvent6,adverseCompleteEvent7,adverseCompleteEvent8,adverseCompleteEvent9,adverseCompleteEvent10,adverseCompleteEvent11,adverseCompleteEvent12,adverseCompleteEvent13,adverseCompleteEvent14,adverseCompleteEvent15,adverseCompleteEvent16,adverseCompleteEvent17,adverseCompleteEvent18,adverseCompleteEvent19,adverseCompleteEvent20,adverseCompleteEvent21,adverseCompleteEvent22,adverseCompleteEvent23,adverseCompleteEvent24,adverseCompleteEvent25,adverseCompleteEvent26,adverseCompleteEvent27,adverseCompleteEvent28,adverseCompleteEvent29,adverseCompleteEvent30,adverseCompleteEvent31,adverseCompleteEvent32,adverseCompleteEvent33,adverseCompleteEvent34,adverseCompleteEvent35,adverseCompleteEvent36,adverseCompleteEvent37,adverseCompleteEvent38,taskReward]
    <;> norm_num
  have hp : rawVisits adverseCompleteS39Before [.query 1] = 31 := by decide
  have hn : rawVisits adverseCompleteS39Before ([.query 1]++[.hydeRetriever 2]) = 10 := by decide
  have hz : (controlPenalty savedCref uniformQuoteError unitRoleUnused .complete) adverseCompleteS39Before [.query 1] (.hydeRetriever 2) = 0 := by
    apply control_penalty_empty_of_prior_terminal .complete savedCref uniformQuoteError adverseCompleteS39Before [.query 1] (.hydeRetriever 2) 10 (by decide)
    · decide
    · decide
  unfold indexScore
  rw [hs,hp,hn,hz]
  simp only [BackupStat.mean]
  norm_num

theorem adverseCompleteS39D1Cmp1 : indexScore (7/5) (controlPenalty savedCref uniformQuoteError unitRoleUnused .complete) adverseCompleteS39Before [.query 1] (.hydeRetriever 0) ≤ indexScore (7/5) (controlPenalty savedCref uniformQuoteError unitRoleUnused .complete) adverseCompleteS39Before [.query 1] (.hydeRetriever 1) := by
  rw [adverseCompleteS39D1I1,adverseCompleteS39D1I0]

theorem adverseCompleteS39D1Cmp2 : indexScore (7/5) (controlPenalty savedCref uniformQuoteError unitRoleUnused .complete) adverseCompleteS39Before [.query 1] (.hydeRetriever 2) ≤ indexScore (7/5) (controlPenalty savedCref uniformQuoteError unitRoleUnused .complete) adverseCompleteS39Before [.query 1] (.hydeRetriever 1) := by
  rw [adverseCompleteS39D1I2,adverseCompleteS39D1I0]

theorem adverseCompleteS39Choice1 : nativeFirstChoice (indexScore (7/5) (controlPenalty savedCref uniformQuoteError unitRoleUnused .complete) adverseCompleteS39Before [.query 1]) adverseCompleteS39Before [.query 1] = .hydeRetriever 1 := by
  apply visited_choice_from_ordered_certificate _ _ [.query 1] [] [.hydeRetriever 0,.hydeRetriever 2] (.hydeRetriever 1) (by decide)
  · intro a ha
    have ho : orderedLegalAvailable [.query 1] = [.hydeRetriever 1,.hydeRetriever 0,.hydeRetriever 2] := by decide
    rw [ho] at ha
    simp only [List.mem_cons,List.not_mem_nil,or_false] at ha
    rcases ha with rfl | rfl | rfl <;> decide
  · simp
  · intro a ha
    simp only [List.mem_cons,List.not_mem_nil,or_false] at ha
    rcases ha with rfl | rfl
    · exact adverseCompleteS39D1Cmp1
    · exact adverseCompleteS39D1Cmp2

theorem adverseCompleteS39D2I0 : indexScore (7/5) (controlPenalty savedCref uniformQuoteError unitRoleUnused .complete) adverseCompleteS39Before [.query 1,.hydeRetriever 1] (.selection 1) = treeIndex ((0/1)/3) (7/5) 0 10 3 := by
  have hs : replayBackup adverseCompleteS39Before emptyStatistics ([.query 1,.hydeRetriever 1]++[.selection 1]) = ⟨3,(0/1)⟩ := by
    rw [replayBackup_empty_closed_form]
    simp +decide [backedEvents,adverseCompleteS39Before,adverseCompleteProposal,adverseCompleteEvent1,adverseCompleteEvent2,adverseCompleteEvent3,adverseCompleteEvent4,adverseCompleteEvent5,adverseCompleteEvent6,adverseCompleteEvent7,adverseCompleteEvent8,adverseCompleteEvent9,adverseCompleteEvent10,adverseCompleteEvent11,adverseCompleteEvent12,adverseCompleteEvent13,adverseCompleteEvent14,adverseCompleteEvent15,adverseCompleteEvent16,adverseCompleteEvent17,adverseCompleteEvent18,adverseCompleteEvent19,adverseCompleteEvent20,adverseCompleteEvent21,adverseCompleteEvent22,adverseCompleteEvent23,adverseCompleteEvent24,adverseCompleteEvent25,adverseCompleteEvent26,adverseCompleteEvent27,adverseCompleteEvent28,adverseCompleteEvent29,adverseCompleteEvent30,adverseCompleteEvent31,adverseCompleteEvent32,adverseCompleteEvent33,adverseCompleteEvent34,adverseCompleteEvent35,adverseCompleteEvent36,adverseCompleteEvent37,adverseCompleteEvent38,taskReward]
    <;> norm_num
  have hp : rawVisits adverseCompleteS39Before [.query 1,.hydeRetriever 1] = 10 := by decide
  have hn : rawVisits adverseCompleteS39Before ([.query 1,.hydeRetriever 1]++[.selection 1]) = 3 := by decide
  have hz : (controlPenalty savedCref uniformQuoteError unitRoleUnused .complete) adverseCompleteS39Before [.query 1,.hydeRetriever 1] (.selection 1) = 0 := by
    apply control_penalty_empty_of_prior_terminal .complete savedCref uniformQuoteError adverseCompleteS39Before [.query 1,.hydeRetriever 1] (.selection 1) 14 (by decide)
    · decide
    · decide
  unfold indexScore
  rw [hs,hp,hn,hz]
  simp only [BackupStat.mean]
  norm_num

theorem adverseCompleteS39D2I1 : indexScore (7/5) (controlPenalty savedCref uniformQuoteError unitRoleUnused .complete) adverseCompleteS39Before [.query 1,.hydeRetriever 1] (.selection 2) = treeIndex ((0/1)/2) (7/5) 0 10 2 := by
  have hs : replayBackup adverseCompleteS39Before emptyStatistics ([.query 1,.hydeRetriever 1]++[.selection 2]) = ⟨2,(0/1)⟩ := by
    rw [replayBackup_empty_closed_form]
    simp +decide [backedEvents,adverseCompleteS39Before,adverseCompleteProposal,adverseCompleteEvent1,adverseCompleteEvent2,adverseCompleteEvent3,adverseCompleteEvent4,adverseCompleteEvent5,adverseCompleteEvent6,adverseCompleteEvent7,adverseCompleteEvent8,adverseCompleteEvent9,adverseCompleteEvent10,adverseCompleteEvent11,adverseCompleteEvent12,adverseCompleteEvent13,adverseCompleteEvent14,adverseCompleteEvent15,adverseCompleteEvent16,adverseCompleteEvent17,adverseCompleteEvent18,adverseCompleteEvent19,adverseCompleteEvent20,adverseCompleteEvent21,adverseCompleteEvent22,adverseCompleteEvent23,adverseCompleteEvent24,adverseCompleteEvent25,adverseCompleteEvent26,adverseCompleteEvent27,adverseCompleteEvent28,adverseCompleteEvent29,adverseCompleteEvent30,adverseCompleteEvent31,adverseCompleteEvent32,adverseCompleteEvent33,adverseCompleteEvent34,adverseCompleteEvent35,adverseCompleteEvent36,adverseCompleteEvent37,adverseCompleteEvent38,taskReward]
    <;> norm_num
  have hp : rawVisits adverseCompleteS39Before [.query 1,.hydeRetriever 1] = 10 := by decide
  have hn : rawVisits adverseCompleteS39Before ([.query 1,.hydeRetriever 1]++[.selection 2]) = 2 := by decide
  have hz : (controlPenalty savedCref uniformQuoteError unitRoleUnused .complete) adverseCompleteS39Before [.query 1,.hydeRetriever 1] (.selection 2) = 0 := by
    apply control_penalty_empty_of_prior_terminal .complete savedCref uniformQuoteError adverseCompleteS39Before [.query 1,.hydeRetriever 1] (.selection 2) 17 (by decide)
    · decide
    · decide
  unfold indexScore
  rw [hs,hp,hn,hz]
  simp only [BackupStat.mean]
  norm_num

theorem adverseCompleteS39D2I2 : indexScore (7/5) (controlPenalty savedCref uniformQuoteError unitRoleUnused .complete) adverseCompleteS39Before [.query 1,.hydeRetriever 1] (.selection 3) = treeIndex ((0/1)/2) (7/5) 0 10 2 := by
  have hs : replayBackup adverseCompleteS39Before emptyStatistics ([.query 1,.hydeRetriever 1]++[.selection 3]) = ⟨2,(0/1)⟩ := by
    rw [replayBackup_empty_closed_form]
    simp +decide [backedEvents,adverseCompleteS39Before,adverseCompleteProposal,adverseCompleteEvent1,adverseCompleteEvent2,adverseCompleteEvent3,adverseCompleteEvent4,adverseCompleteEvent5,adverseCompleteEvent6,adverseCompleteEvent7,adverseCompleteEvent8,adverseCompleteEvent9,adverseCompleteEvent10,adverseCompleteEvent11,adverseCompleteEvent12,adverseCompleteEvent13,adverseCompleteEvent14,adverseCompleteEvent15,adverseCompleteEvent16,adverseCompleteEvent17,adverseCompleteEvent18,adverseCompleteEvent19,adverseCompleteEvent20,adverseCompleteEvent21,adverseCompleteEvent22,adverseCompleteEvent23,adverseCompleteEvent24,adverseCompleteEvent25,adverseCompleteEvent26,adverseCompleteEvent27,adverseCompleteEvent28,adverseCompleteEvent29,adverseCompleteEvent30,adverseCompleteEvent31,adverseCompleteEvent32,adverseCompleteEvent33,adverseCompleteEvent34,adverseCompleteEvent35,adverseCompleteEvent36,adverseCompleteEvent37,adverseCompleteEvent38,taskReward]
    <;> norm_num
  have hp : rawVisits adverseCompleteS39Before [.query 1,.hydeRetriever 1] = 10 := by decide
  have hn : rawVisits adverseCompleteS39Before ([.query 1,.hydeRetriever 1]++[.selection 3]) = 2 := by decide
  have hz : (controlPenalty savedCref uniformQuoteError unitRoleUnused .complete) adverseCompleteS39Before [.query 1,.hydeRetriever 1] (.selection 3) = 0 := by
    apply control_penalty_empty_of_prior_terminal .complete savedCref uniformQuoteError adverseCompleteS39Before [.query 1,.hydeRetriever 1] (.selection 3) 20 (by decide)
    · decide
    · decide
  unfold indexScore
  rw [hs,hp,hn,hz]
  simp only [BackupStat.mean]
  norm_num

theorem adverseCompleteS39D2I3 : indexScore (7/5) (controlPenalty savedCref uniformQuoteError unitRoleUnused .complete) adverseCompleteS39Before [.query 1,.hydeRetriever 1] (.selection 0) = treeIndex ((0/1)/2) (7/5) 0 10 2 := by
  have hs : replayBackup adverseCompleteS39Before emptyStatistics ([.query 1,.hydeRetriever 1]++[.selection 0]) = ⟨2,(0/1)⟩ := by
    rw [replayBackup_empty_closed_form]
    simp +decide [backedEvents,adverseCompleteS39Before,adverseCompleteProposal,adverseCompleteEvent1,adverseCompleteEvent2,adverseCompleteEvent3,adverseCompleteEvent4,adverseCompleteEvent5,adverseCompleteEvent6,adverseCompleteEvent7,adverseCompleteEvent8,adverseCompleteEvent9,adverseCompleteEvent10,adverseCompleteEvent11,adverseCompleteEvent12,adverseCompleteEvent13,adverseCompleteEvent14,adverseCompleteEvent15,adverseCompleteEvent16,adverseCompleteEvent17,adverseCompleteEvent18,adverseCompleteEvent19,adverseCompleteEvent20,adverseCompleteEvent21,adverseCompleteEvent22,adverseCompleteEvent23,adverseCompleteEvent24,adverseCompleteEvent25,adverseCompleteEvent26,adverseCompleteEvent27,adverseCompleteEvent28,adverseCompleteEvent29,adverseCompleteEvent30,adverseCompleteEvent31,adverseCompleteEvent32,adverseCompleteEvent33,adverseCompleteEvent34,adverseCompleteEvent35,adverseCompleteEvent36,adverseCompleteEvent37,adverseCompleteEvent38,taskReward]
    <;> norm_num
  have hp : rawVisits adverseCompleteS39Before [.query 1,.hydeRetriever 1] = 10 := by decide
  have hn : rawVisits adverseCompleteS39Before ([.query 1,.hydeRetriever 1]++[.selection 0]) = 2 := by decide
  have hz : (controlPenalty savedCref uniformQuoteError unitRoleUnused .complete) adverseCompleteS39Before [.query 1,.hydeRetriever 1] (.selection 0) = 0 := by
    apply control_penalty_empty_of_prior_terminal .complete savedCref uniformQuoteError adverseCompleteS39Before [.query 1,.hydeRetriever 1] (.selection 0) 8 (by decide)
    · decide
    · decide
  unfold indexScore
  rw [hs,hp,hn,hz]
  simp only [BackupStat.mean]
  norm_num

theorem adverseCompleteS39D2Cmp0 : indexScore (7/5) (controlPenalty savedCref uniformQuoteError unitRoleUnused .complete) adverseCompleteS39Before [.query 1,.hydeRetriever 1] (.selection 1) < indexScore (7/5) (controlPenalty savedCref uniformQuoteError unitRoleUnused .complete) adverseCompleteS39Before [.query 1,.hydeRetriever 1] (.selection 2) := by
  rw [adverseCompleteS39D2I0,adverseCompleteS39D2I1]
  have h := index_strict_order_from_intervals ((0/1)/2) ((0/1)/3) 0 0 (38323761/25000000) (1251649/1000000)
    (treeBonus (7/5) 10 2) (treeBonus (7/5) 10 3)
    (trajectory_bonus_10_2).1 (trajectory_bonus_10_3).2 (by norm_num)
  simpa only [treeIndex,sub_zero] using h

theorem adverseCompleteS39D2Cmp2 : indexScore (7/5) (controlPenalty savedCref uniformQuoteError unitRoleUnused .complete) adverseCompleteS39Before [.query 1,.hydeRetriever 1] (.selection 3) ≤ indexScore (7/5) (controlPenalty savedCref uniformQuoteError unitRoleUnused .complete) adverseCompleteS39Before [.query 1,.hydeRetriever 1] (.selection 2) := by
  rw [adverseCompleteS39D2I2,adverseCompleteS39D2I1]

theorem adverseCompleteS39D2Cmp3 : indexScore (7/5) (controlPenalty savedCref uniformQuoteError unitRoleUnused .complete) adverseCompleteS39Before [.query 1,.hydeRetriever 1] (.selection 0) ≤ indexScore (7/5) (controlPenalty savedCref uniformQuoteError unitRoleUnused .complete) adverseCompleteS39Before [.query 1,.hydeRetriever 1] (.selection 2) := by
  rw [adverseCompleteS39D2I3,adverseCompleteS39D2I1]

theorem adverseCompleteS39Choice2 : nativeFirstChoice (indexScore (7/5) (controlPenalty savedCref uniformQuoteError unitRoleUnused .complete) adverseCompleteS39Before [.query 1,.hydeRetriever 1]) adverseCompleteS39Before [.query 1,.hydeRetriever 1] = .selection 2 := by
  apply visited_choice_from_ordered_certificate _ _ [.query 1,.hydeRetriever 1] [.selection 1] [.selection 3,.selection 0] (.selection 2) (by decide)
  · intro a ha
    have ho : orderedLegalAvailable [.query 1,.hydeRetriever 1] = [.selection 1,.selection 2,.selection 3,.selection 0] := by decide
    rw [ho] at ha
    simp only [List.mem_cons,List.not_mem_nil,or_false] at ha
    rcases ha with rfl | rfl | rfl | rfl <;> decide
  · intro a ha
    simp only [List.mem_cons,List.not_mem_nil,or_false] at ha
    rcases ha with rfl
    · exact adverseCompleteS39D2Cmp0
  · intro a ha
    simp only [List.mem_cons,List.not_mem_nil,or_false] at ha
    rcases ha with rfl | rfl
    · exact adverseCompleteS39D2Cmp2
    · exact adverseCompleteS39D2Cmp3

theorem adverseCompleteS39ActualEvent : nativeEvent budgetTape (7/5) (controlPenalty savedCref uniformQuoteError unitRoleUnused .complete)
    (taskReward true (2/5) (1/2)) adverseCompleteS39Before = adverseCompleteEvent39 := by
  have hs0 := native_select_existing_step budgetTape (7/5) (controlPenalty savedCref uniformQuoteError unitRoleUnused .complete) adverseCompleteS39Before 8 [] (.query 1)
    (by decide) (by decide) adverseCompleteS39Choice0
  have hs1 := native_select_existing_step budgetTape (7/5) (controlPenalty savedCref uniformQuoteError unitRoleUnused .complete) adverseCompleteS39Before 7 [.query 1] (.hydeRetriever 1)
    (by decide) (by decide) adverseCompleteS39Choice1
  have hs2 := native_select_existing_step budgetTape (7/5) (controlPenalty savedCref uniformQuoteError unitRoleUnused .complete) adverseCompleteS39Before 6 [.query 1,.hydeRetriever 1] (.selection 2)
    (by decide) (by decide) adverseCompleteS39Choice2
  have hnew := native_select_new_step budgetTape (7/5) (controlPenalty savedCref uniformQuoteError unitRoleUnused .complete) adverseCompleteS39Before 5 [.query 1,.hydeRetriever 1,.selection 2]
    [.width 3,.width 1,.width 2] (.width 3) (by decide) (by decide) (by decide) (by decide)
  have hs : nativeSelect budgetTape (7/5) (controlPenalty savedCref uniformQuoteError unitRoleUnused .complete) adverseCompleteS39Before 9 [] = [.query 1,.hydeRetriever 1,.selection 2,.width 3] := by
    rw [hs0]
    change nativeSelect budgetTape (7/5) (controlPenalty savedCref uniformQuoteError unitRoleUnused .complete) adverseCompleteS39Before 8 [.query 1] = _
    rw [hs1]
    change nativeSelect budgetTape (7/5) (controlPenalty savedCref uniformQuoteError unitRoleUnused .complete) adverseCompleteS39Before 7 [.query 1,.hydeRetriever 1] = _
    rw [hs2]
    change nativeSelect budgetTape (7/5) (controlPenalty savedCref uniformQuoteError unitRoleUnused .complete) adverseCompleteS39Before 6 [.query 1,.hydeRetriever 1,.selection 2] = _
    rw [hnew] <;> rfl
  have hr : repairedRollout budgetTape adverseCompleteS39Before 9 [.query 1,.hydeRetriever 1,.selection 2,.width 3] = [.query 1,.hydeRetriever 1,.selection 2,.width 3,.stop,.reranker 0,.topm 0,.context 0,.answer 0] := by decide
  simp only [nativeEvent,hs,hr]
  rfl

def adverseCompleteS40Before := adverseCompleteProposal.take 39

theorem adverseCompleteS40Choice0 : nativeFirstChoice (indexScore (7/5) (controlPenalty savedCref uniformQuoteError unitRoleUnused .complete) adverseCompleteS40Before []) adverseCompleteS40Before [] = .query 1 := by
  apply complete_root_from_physical_gap adverseCompleteS40Before (adverseComplete_prefix_rewards 39) (by decide)
  · intro q; fin_cases q <;> decide
  · exact AgentUCTNextExact.adverse_complete_hyde_root_suffix_empty 39 (by omega)
  · intro q hq
    exact AgentUCTNextExact.adverse_complete_normal_root_physical_quote_exact 39 (by omega) q hq

theorem adverseCompleteS40D1I0 : indexScore (7/5) (controlPenalty savedCref uniformQuoteError unitRoleUnused .complete) adverseCompleteS40Before [.query 1] (.hydeRetriever 1) = treeIndex ((0/1)/11) (7/5) 0 32 11 := by
  have hs : replayBackup adverseCompleteS40Before emptyStatistics ([.query 1]++[.hydeRetriever 1]) = ⟨11,(0/1)⟩ := by
    rw [replayBackup_empty_closed_form]
    simp +decide [backedEvents,adverseCompleteS40Before,adverseCompleteProposal,adverseCompleteEvent1,adverseCompleteEvent2,adverseCompleteEvent3,adverseCompleteEvent4,adverseCompleteEvent5,adverseCompleteEvent6,adverseCompleteEvent7,adverseCompleteEvent8,adverseCompleteEvent9,adverseCompleteEvent10,adverseCompleteEvent11,adverseCompleteEvent12,adverseCompleteEvent13,adverseCompleteEvent14,adverseCompleteEvent15,adverseCompleteEvent16,adverseCompleteEvent17,adverseCompleteEvent18,adverseCompleteEvent19,adverseCompleteEvent20,adverseCompleteEvent21,adverseCompleteEvent22,adverseCompleteEvent23,adverseCompleteEvent24,adverseCompleteEvent25,adverseCompleteEvent26,adverseCompleteEvent27,adverseCompleteEvent28,adverseCompleteEvent29,adverseCompleteEvent30,adverseCompleteEvent31,adverseCompleteEvent32,adverseCompleteEvent33,adverseCompleteEvent34,adverseCompleteEvent35,adverseCompleteEvent36,adverseCompleteEvent37,adverseCompleteEvent38,adverseCompleteEvent39,taskReward]
    <;> norm_num
  have hp : rawVisits adverseCompleteS40Before [.query 1] = 32 := by decide
  have hn : rawVisits adverseCompleteS40Before ([.query 1]++[.hydeRetriever 1]) = 11 := by decide
  have hz : (controlPenalty savedCref uniformQuoteError unitRoleUnused .complete) adverseCompleteS40Before [.query 1] (.hydeRetriever 1) = 0 := by
    apply control_penalty_empty_of_prior_terminal .complete savedCref uniformQuoteError adverseCompleteS40Before [.query 1] (.hydeRetriever 1) 8 (by decide)
    · decide
    · decide
  unfold indexScore
  rw [hs,hp,hn,hz]
  simp only [BackupStat.mean]
  norm_num

theorem adverseCompleteS40D1I1 : indexScore (7/5) (controlPenalty savedCref uniformQuoteError unitRoleUnused .complete) adverseCompleteS40Before [.query 1] (.hydeRetriever 0) = treeIndex ((0/1)/10) (7/5) 0 32 10 := by
  have hs : replayBackup adverseCompleteS40Before emptyStatistics ([.query 1]++[.hydeRetriever 0]) = ⟨10,(0/1)⟩ := by
    rw [replayBackup_empty_closed_form]
    simp +decide [backedEvents,adverseCompleteS40Before,adverseCompleteProposal,adverseCompleteEvent1,adverseCompleteEvent2,adverseCompleteEvent3,adverseCompleteEvent4,adverseCompleteEvent5,adverseCompleteEvent6,adverseCompleteEvent7,adverseCompleteEvent8,adverseCompleteEvent9,adverseCompleteEvent10,adverseCompleteEvent11,adverseCompleteEvent12,adverseCompleteEvent13,adverseCompleteEvent14,adverseCompleteEvent15,adverseCompleteEvent16,adverseCompleteEvent17,adverseCompleteEvent18,adverseCompleteEvent19,adverseCompleteEvent20,adverseCompleteEvent21,adverseCompleteEvent22,adverseCompleteEvent23,adverseCompleteEvent24,adverseCompleteEvent25,adverseCompleteEvent26,adverseCompleteEvent27,adverseCompleteEvent28,adverseCompleteEvent29,adverseCompleteEvent30,adverseCompleteEvent31,adverseCompleteEvent32,adverseCompleteEvent33,adverseCompleteEvent34,adverseCompleteEvent35,adverseCompleteEvent36,adverseCompleteEvent37,adverseCompleteEvent38,adverseCompleteEvent39,taskReward]
    <;> norm_num
  have hp : rawVisits adverseCompleteS40Before [.query 1] = 32 := by decide
  have hn : rawVisits adverseCompleteS40Before ([.query 1]++[.hydeRetriever 0]) = 10 := by decide
  have hz : (controlPenalty savedCref uniformQuoteError unitRoleUnused .complete) adverseCompleteS40Before [.query 1] (.hydeRetriever 0) = 0 := by
    apply control_penalty_empty_of_prior_terminal .complete savedCref uniformQuoteError adverseCompleteS40Before [.query 1] (.hydeRetriever 0) 1 (by decide)
    · decide
    · decide
  unfold indexScore
  rw [hs,hp,hn,hz]
  simp only [BackupStat.mean]
  norm_num

theorem adverseCompleteS40D1I2 : indexScore (7/5) (controlPenalty savedCref uniformQuoteError unitRoleUnused .complete) adverseCompleteS40Before [.query 1] (.hydeRetriever 2) = treeIndex ((0/1)/10) (7/5) 0 32 10 := by
  have hs : replayBackup adverseCompleteS40Before emptyStatistics ([.query 1]++[.hydeRetriever 2]) = ⟨10,(0/1)⟩ := by
    rw [replayBackup_empty_closed_form]
    simp +decide [backedEvents,adverseCompleteS40Before,adverseCompleteProposal,adverseCompleteEvent1,adverseCompleteEvent2,adverseCompleteEvent3,adverseCompleteEvent4,adverseCompleteEvent5,adverseCompleteEvent6,adverseCompleteEvent7,adverseCompleteEvent8,adverseCompleteEvent9,adverseCompleteEvent10,adverseCompleteEvent11,adverseCompleteEvent12,adverseCompleteEvent13,adverseCompleteEvent14,adverseCompleteEvent15,adverseCompleteEvent16,adverseCompleteEvent17,adverseCompleteEvent18,adverseCompleteEvent19,adverseCompleteEvent20,adverseCompleteEvent21,adverseCompleteEvent22,adverseCompleteEvent23,adverseCompleteEvent24,adverseCompleteEvent25,adverseCompleteEvent26,adverseCompleteEvent27,adverseCompleteEvent28,adverseCompleteEvent29,adverseCompleteEvent30,adverseCompleteEvent31,adverseCompleteEvent32,adverseCompleteEvent33,adverseCompleteEvent34,adverseCompleteEvent35,adverseCompleteEvent36,adverseCompleteEvent37,adverseCompleteEvent38,adverseCompleteEvent39,taskReward]
    <;> norm_num
  have hp : rawVisits adverseCompleteS40Before [.query 1] = 32 := by decide
  have hn : rawVisits adverseCompleteS40Before ([.query 1]++[.hydeRetriever 2]) = 10 := by decide
  have hz : (controlPenalty savedCref uniformQuoteError unitRoleUnused .complete) adverseCompleteS40Before [.query 1] (.hydeRetriever 2) = 0 := by
    apply control_penalty_empty_of_prior_terminal .complete savedCref uniformQuoteError adverseCompleteS40Before [.query 1] (.hydeRetriever 2) 10 (by decide)
    · decide
    · decide
  unfold indexScore
  rw [hs,hp,hn,hz]
  simp only [BackupStat.mean]
  norm_num

theorem adverseCompleteS40D1Cmp0 : indexScore (7/5) (controlPenalty savedCref uniformQuoteError unitRoleUnused .complete) adverseCompleteS40Before [.query 1] (.hydeRetriever 1) < indexScore (7/5) (controlPenalty savedCref uniformQuoteError unitRoleUnused .complete) adverseCompleteS40Before [.query 1] (.hydeRetriever 0) := by
  rw [adverseCompleteS40D1I0,adverseCompleteS40D1I1]
  have h := index_strict_order_from_intervals ((0/1)/10) ((0/1)/11) 0 0 (41391889/50000000) (39465629/50000000)
    (treeBonus (7/5) 32 10) (treeBonus (7/5) 32 11)
    (trajectory_bonus_32_10).1 (trajectory_bonus_32_11).2 (by norm_num)
  simpa only [treeIndex,sub_zero] using h

theorem adverseCompleteS40D1Cmp2 : indexScore (7/5) (controlPenalty savedCref uniformQuoteError unitRoleUnused .complete) adverseCompleteS40Before [.query 1] (.hydeRetriever 2) ≤ indexScore (7/5) (controlPenalty savedCref uniformQuoteError unitRoleUnused .complete) adverseCompleteS40Before [.query 1] (.hydeRetriever 0) := by
  rw [adverseCompleteS40D1I2,adverseCompleteS40D1I1]

theorem adverseCompleteS40Choice1 : nativeFirstChoice (indexScore (7/5) (controlPenalty savedCref uniformQuoteError unitRoleUnused .complete) adverseCompleteS40Before [.query 1]) adverseCompleteS40Before [.query 1] = .hydeRetriever 0 := by
  apply visited_choice_from_ordered_certificate _ _ [.query 1] [.hydeRetriever 1] [.hydeRetriever 2] (.hydeRetriever 0) (by decide)
  · intro a ha
    have ho : orderedLegalAvailable [.query 1] = [.hydeRetriever 1,.hydeRetriever 0,.hydeRetriever 2] := by decide
    rw [ho] at ha
    simp only [List.mem_cons,List.not_mem_nil,or_false] at ha
    rcases ha with rfl | rfl | rfl <;> decide
  · intro a ha
    simp only [List.mem_cons,List.not_mem_nil,or_false] at ha
    rcases ha with rfl
    · exact adverseCompleteS40D1Cmp0
  · intro a ha
    simp only [List.mem_cons,List.not_mem_nil,or_false] at ha
    rcases ha with rfl
    · exact adverseCompleteS40D1Cmp2

theorem adverseCompleteS40D2I0 : indexScore (7/5) (controlPenalty savedCref uniformQuoteError unitRoleUnused .complete) adverseCompleteS40Before [.query 1,.hydeRetriever 0] (.selection 1) = treeIndex ((0/1)/3) (7/5) 0 10 3 := by
  have hs : replayBackup adverseCompleteS40Before emptyStatistics ([.query 1,.hydeRetriever 0]++[.selection 1]) = ⟨3,(0/1)⟩ := by
    rw [replayBackup_empty_closed_form]
    simp +decide [backedEvents,adverseCompleteS40Before,adverseCompleteProposal,adverseCompleteEvent1,adverseCompleteEvent2,adverseCompleteEvent3,adverseCompleteEvent4,adverseCompleteEvent5,adverseCompleteEvent6,adverseCompleteEvent7,adverseCompleteEvent8,adverseCompleteEvent9,adverseCompleteEvent10,adverseCompleteEvent11,adverseCompleteEvent12,adverseCompleteEvent13,adverseCompleteEvent14,adverseCompleteEvent15,adverseCompleteEvent16,adverseCompleteEvent17,adverseCompleteEvent18,adverseCompleteEvent19,adverseCompleteEvent20,adverseCompleteEvent21,adverseCompleteEvent22,adverseCompleteEvent23,adverseCompleteEvent24,adverseCompleteEvent25,adverseCompleteEvent26,adverseCompleteEvent27,adverseCompleteEvent28,adverseCompleteEvent29,adverseCompleteEvent30,adverseCompleteEvent31,adverseCompleteEvent32,adverseCompleteEvent33,adverseCompleteEvent34,adverseCompleteEvent35,adverseCompleteEvent36,adverseCompleteEvent37,adverseCompleteEvent38,adverseCompleteEvent39,taskReward]
    <;> norm_num
  have hp : rawVisits adverseCompleteS40Before [.query 1,.hydeRetriever 0] = 10 := by decide
  have hn : rawVisits adverseCompleteS40Before ([.query 1,.hydeRetriever 0]++[.selection 1]) = 3 := by decide
  have hz : (controlPenalty savedCref uniformQuoteError unitRoleUnused .complete) adverseCompleteS40Before [.query 1,.hydeRetriever 0] (.selection 1) = 0 := by
    apply control_penalty_empty_of_prior_terminal .complete savedCref uniformQuoteError adverseCompleteS40Before [.query 1,.hydeRetriever 0] (.selection 1) 15 (by decide)
    · decide
    · decide
  unfold indexScore
  rw [hs,hp,hn,hz]
  simp only [BackupStat.mean]
  norm_num

theorem adverseCompleteS40D2I1 : indexScore (7/5) (controlPenalty savedCref uniformQuoteError unitRoleUnused .complete) adverseCompleteS40Before [.query 1,.hydeRetriever 0] (.selection 2) = treeIndex ((0/1)/2) (7/5) 0 10 2 := by
  have hs : replayBackup adverseCompleteS40Before emptyStatistics ([.query 1,.hydeRetriever 0]++[.selection 2]) = ⟨2,(0/1)⟩ := by
    rw [replayBackup_empty_closed_form]
    simp +decide [backedEvents,adverseCompleteS40Before,adverseCompleteProposal,adverseCompleteEvent1,adverseCompleteEvent2,adverseCompleteEvent3,adverseCompleteEvent4,adverseCompleteEvent5,adverseCompleteEvent6,adverseCompleteEvent7,adverseCompleteEvent8,adverseCompleteEvent9,adverseCompleteEvent10,adverseCompleteEvent11,adverseCompleteEvent12,adverseCompleteEvent13,adverseCompleteEvent14,adverseCompleteEvent15,adverseCompleteEvent16,adverseCompleteEvent17,adverseCompleteEvent18,adverseCompleteEvent19,adverseCompleteEvent20,adverseCompleteEvent21,adverseCompleteEvent22,adverseCompleteEvent23,adverseCompleteEvent24,adverseCompleteEvent25,adverseCompleteEvent26,adverseCompleteEvent27,adverseCompleteEvent28,adverseCompleteEvent29,adverseCompleteEvent30,adverseCompleteEvent31,adverseCompleteEvent32,adverseCompleteEvent33,adverseCompleteEvent34,adverseCompleteEvent35,adverseCompleteEvent36,adverseCompleteEvent37,adverseCompleteEvent38,adverseCompleteEvent39,taskReward]
    <;> norm_num
  have hp : rawVisits adverseCompleteS40Before [.query 1,.hydeRetriever 0] = 10 := by decide
  have hn : rawVisits adverseCompleteS40Before ([.query 1,.hydeRetriever 0]++[.selection 2]) = 2 := by decide
  have hz : (controlPenalty savedCref uniformQuoteError unitRoleUnused .complete) adverseCompleteS40Before [.query 1,.hydeRetriever 0] (.selection 2) = 0 := by
    apply control_penalty_empty_of_prior_terminal .complete savedCref uniformQuoteError adverseCompleteS40Before [.query 1,.hydeRetriever 0] (.selection 2) 18 (by decide)
    · decide
    · decide
  unfold indexScore
  rw [hs,hp,hn,hz]
  simp only [BackupStat.mean]
  norm_num

theorem adverseCompleteS40D2I2 : indexScore (7/5) (controlPenalty savedCref uniformQuoteError unitRoleUnused .complete) adverseCompleteS40Before [.query 1,.hydeRetriever 0] (.selection 3) = treeIndex ((0/1)/2) (7/5) 0 10 2 := by
  have hs : replayBackup adverseCompleteS40Before emptyStatistics ([.query 1,.hydeRetriever 0]++[.selection 3]) = ⟨2,(0/1)⟩ := by
    rw [replayBackup_empty_closed_form]
    simp +decide [backedEvents,adverseCompleteS40Before,adverseCompleteProposal,adverseCompleteEvent1,adverseCompleteEvent2,adverseCompleteEvent3,adverseCompleteEvent4,adverseCompleteEvent5,adverseCompleteEvent6,adverseCompleteEvent7,adverseCompleteEvent8,adverseCompleteEvent9,adverseCompleteEvent10,adverseCompleteEvent11,adverseCompleteEvent12,adverseCompleteEvent13,adverseCompleteEvent14,adverseCompleteEvent15,adverseCompleteEvent16,adverseCompleteEvent17,adverseCompleteEvent18,adverseCompleteEvent19,adverseCompleteEvent20,adverseCompleteEvent21,adverseCompleteEvent22,adverseCompleteEvent23,adverseCompleteEvent24,adverseCompleteEvent25,adverseCompleteEvent26,adverseCompleteEvent27,adverseCompleteEvent28,adverseCompleteEvent29,adverseCompleteEvent30,adverseCompleteEvent31,adverseCompleteEvent32,adverseCompleteEvent33,adverseCompleteEvent34,adverseCompleteEvent35,adverseCompleteEvent36,adverseCompleteEvent37,adverseCompleteEvent38,adverseCompleteEvent39,taskReward]
    <;> norm_num
  have hp : rawVisits adverseCompleteS40Before [.query 1,.hydeRetriever 0] = 10 := by decide
  have hn : rawVisits adverseCompleteS40Before ([.query 1,.hydeRetriever 0]++[.selection 3]) = 2 := by decide
  have hz : (controlPenalty savedCref uniformQuoteError unitRoleUnused .complete) adverseCompleteS40Before [.query 1,.hydeRetriever 0] (.selection 3) = 0 := by
    apply control_penalty_empty_of_prior_terminal .complete savedCref uniformQuoteError adverseCompleteS40Before [.query 1,.hydeRetriever 0] (.selection 3) 21 (by decide)
    · decide
    · decide
  unfold indexScore
  rw [hs,hp,hn,hz]
  simp only [BackupStat.mean]
  norm_num

theorem adverseCompleteS40D2I3 : indexScore (7/5) (controlPenalty savedCref uniformQuoteError unitRoleUnused .complete) adverseCompleteS40Before [.query 1,.hydeRetriever 0] (.selection 0) = treeIndex ((0/1)/2) (7/5) 0 10 2 := by
  have hs : replayBackup adverseCompleteS40Before emptyStatistics ([.query 1,.hydeRetriever 0]++[.selection 0]) = ⟨2,(0/1)⟩ := by
    rw [replayBackup_empty_closed_form]
    simp +decide [backedEvents,adverseCompleteS40Before,adverseCompleteProposal,adverseCompleteEvent1,adverseCompleteEvent2,adverseCompleteEvent3,adverseCompleteEvent4,adverseCompleteEvent5,adverseCompleteEvent6,adverseCompleteEvent7,adverseCompleteEvent8,adverseCompleteEvent9,adverseCompleteEvent10,adverseCompleteEvent11,adverseCompleteEvent12,adverseCompleteEvent13,adverseCompleteEvent14,adverseCompleteEvent15,adverseCompleteEvent16,adverseCompleteEvent17,adverseCompleteEvent18,adverseCompleteEvent19,adverseCompleteEvent20,adverseCompleteEvent21,adverseCompleteEvent22,adverseCompleteEvent23,adverseCompleteEvent24,adverseCompleteEvent25,adverseCompleteEvent26,adverseCompleteEvent27,adverseCompleteEvent28,adverseCompleteEvent29,adverseCompleteEvent30,adverseCompleteEvent31,adverseCompleteEvent32,adverseCompleteEvent33,adverseCompleteEvent34,adverseCompleteEvent35,adverseCompleteEvent36,adverseCompleteEvent37,adverseCompleteEvent38,adverseCompleteEvent39,taskReward]
    <;> norm_num
  have hp : rawVisits adverseCompleteS40Before [.query 1,.hydeRetriever 0] = 10 := by decide
  have hn : rawVisits adverseCompleteS40Before ([.query 1,.hydeRetriever 0]++[.selection 0]) = 2 := by decide
  have hz : (controlPenalty savedCref uniformQuoteError unitRoleUnused .complete) adverseCompleteS40Before [.query 1,.hydeRetriever 0] (.selection 0) = 0 := by
    apply control_penalty_empty_of_prior_terminal .complete savedCref uniformQuoteError adverseCompleteS40Before [.query 1,.hydeRetriever 0] (.selection 0) 1 (by decide)
    · decide
    · decide
  unfold indexScore
  rw [hs,hp,hn,hz]
  simp only [BackupStat.mean]
  norm_num

theorem adverseCompleteS40D2Cmp0 : indexScore (7/5) (controlPenalty savedCref uniformQuoteError unitRoleUnused .complete) adverseCompleteS40Before [.query 1,.hydeRetriever 0] (.selection 1) < indexScore (7/5) (controlPenalty savedCref uniformQuoteError unitRoleUnused .complete) adverseCompleteS40Before [.query 1,.hydeRetriever 0] (.selection 2) := by
  rw [adverseCompleteS40D2I0,adverseCompleteS40D2I1]
  have h := index_strict_order_from_intervals ((0/1)/2) ((0/1)/3) 0 0 (38323761/25000000) (1251649/1000000)
    (treeBonus (7/5) 10 2) (treeBonus (7/5) 10 3)
    (trajectory_bonus_10_2).1 (trajectory_bonus_10_3).2 (by norm_num)
  simpa only [treeIndex,sub_zero] using h

theorem adverseCompleteS40D2Cmp2 : indexScore (7/5) (controlPenalty savedCref uniformQuoteError unitRoleUnused .complete) adverseCompleteS40Before [.query 1,.hydeRetriever 0] (.selection 3) ≤ indexScore (7/5) (controlPenalty savedCref uniformQuoteError unitRoleUnused .complete) adverseCompleteS40Before [.query 1,.hydeRetriever 0] (.selection 2) := by
  rw [adverseCompleteS40D2I2,adverseCompleteS40D2I1]

theorem adverseCompleteS40D2Cmp3 : indexScore (7/5) (controlPenalty savedCref uniformQuoteError unitRoleUnused .complete) adverseCompleteS40Before [.query 1,.hydeRetriever 0] (.selection 0) ≤ indexScore (7/5) (controlPenalty savedCref uniformQuoteError unitRoleUnused .complete) adverseCompleteS40Before [.query 1,.hydeRetriever 0] (.selection 2) := by
  rw [adverseCompleteS40D2I3,adverseCompleteS40D2I1]

theorem adverseCompleteS40Choice2 : nativeFirstChoice (indexScore (7/5) (controlPenalty savedCref uniformQuoteError unitRoleUnused .complete) adverseCompleteS40Before [.query 1,.hydeRetriever 0]) adverseCompleteS40Before [.query 1,.hydeRetriever 0] = .selection 2 := by
  apply visited_choice_from_ordered_certificate _ _ [.query 1,.hydeRetriever 0] [.selection 1] [.selection 3,.selection 0] (.selection 2) (by decide)
  · intro a ha
    have ho : orderedLegalAvailable [.query 1,.hydeRetriever 0] = [.selection 1,.selection 2,.selection 3,.selection 0] := by decide
    rw [ho] at ha
    simp only [List.mem_cons,List.not_mem_nil,or_false] at ha
    rcases ha with rfl | rfl | rfl | rfl <;> decide
  · intro a ha
    simp only [List.mem_cons,List.not_mem_nil,or_false] at ha
    rcases ha with rfl
    · exact adverseCompleteS40D2Cmp0
  · intro a ha
    simp only [List.mem_cons,List.not_mem_nil,or_false] at ha
    rcases ha with rfl | rfl
    · exact adverseCompleteS40D2Cmp2
    · exact adverseCompleteS40D2Cmp3

theorem adverseCompleteS40ActualEvent : nativeEvent budgetTape (7/5) (controlPenalty savedCref uniformQuoteError unitRoleUnused .complete)
    (taskReward true (2/5) (1/2)) adverseCompleteS40Before = adverseCompleteEvent40 := by
  have hs0 := native_select_existing_step budgetTape (7/5) (controlPenalty savedCref uniformQuoteError unitRoleUnused .complete) adverseCompleteS40Before 8 [] (.query 1)
    (by decide) (by decide) adverseCompleteS40Choice0
  have hs1 := native_select_existing_step budgetTape (7/5) (controlPenalty savedCref uniformQuoteError unitRoleUnused .complete) adverseCompleteS40Before 7 [.query 1] (.hydeRetriever 0)
    (by decide) (by decide) adverseCompleteS40Choice1
  have hs2 := native_select_existing_step budgetTape (7/5) (controlPenalty savedCref uniformQuoteError unitRoleUnused .complete) adverseCompleteS40Before 6 [.query 1,.hydeRetriever 0] (.selection 2)
    (by decide) (by decide) adverseCompleteS40Choice2
  have hnew := native_select_new_step budgetTape (7/5) (controlPenalty savedCref uniformQuoteError unitRoleUnused .complete) adverseCompleteS40Before 5 [.query 1,.hydeRetriever 0,.selection 2]
    [.width 3,.width 1,.width 2] (.width 3) (by decide) (by decide) (by decide) (by decide)
  have hs : nativeSelect budgetTape (7/5) (controlPenalty savedCref uniformQuoteError unitRoleUnused .complete) adverseCompleteS40Before 9 [] = [.query 1,.hydeRetriever 0,.selection 2,.width 3] := by
    rw [hs0]
    change nativeSelect budgetTape (7/5) (controlPenalty savedCref uniformQuoteError unitRoleUnused .complete) adverseCompleteS40Before 8 [.query 1] = _
    rw [hs1]
    change nativeSelect budgetTape (7/5) (controlPenalty savedCref uniformQuoteError unitRoleUnused .complete) adverseCompleteS40Before 7 [.query 1,.hydeRetriever 0] = _
    rw [hs2]
    change nativeSelect budgetTape (7/5) (controlPenalty savedCref uniformQuoteError unitRoleUnused .complete) adverseCompleteS40Before 6 [.query 1,.hydeRetriever 0,.selection 2] = _
    rw [hnew] <;> rfl
  have hr : repairedRollout budgetTape adverseCompleteS40Before 9 [.query 1,.hydeRetriever 0,.selection 2,.width 3] = [.query 1,.hydeRetriever 0,.selection 2,.width 3,.stop,.reranker 0,.topm 0,.context 0,.answer 0] := by decide
  simp only [nativeEvent,hs,hr]
  rfl

def adverseCompleteS41Before := adverseCompleteProposal.take 40

theorem adverseCompleteS41Choice0 : nativeFirstChoice (indexScore (7/5) (controlPenalty savedCref uniformQuoteError unitRoleUnused .complete) adverseCompleteS41Before []) adverseCompleteS41Before [] = .query 1 := by
  apply complete_root_from_physical_gap adverseCompleteS41Before (adverseComplete_prefix_rewards 40) (by decide)
  · intro q; fin_cases q <;> decide
  · exact AgentUCTNextExact.adverse_complete_hyde_root_suffix_empty 40 (by omega)
  · intro q hq
    exact AgentUCTNextExact.adverse_complete_normal_root_physical_quote_exact 40 (by omega) q hq

theorem adverseCompleteS41D1I0 : indexScore (7/5) (controlPenalty savedCref uniformQuoteError unitRoleUnused .complete) adverseCompleteS41Before [.query 1] (.hydeRetriever 1) = treeIndex ((0/1)/11) (7/5) 0 33 11 := by
  have hs : replayBackup adverseCompleteS41Before emptyStatistics ([.query 1]++[.hydeRetriever 1]) = ⟨11,(0/1)⟩ := by
    rw [replayBackup_empty_closed_form]
    simp +decide [backedEvents,adverseCompleteS41Before,adverseCompleteProposal,adverseCompleteEvent1,adverseCompleteEvent2,adverseCompleteEvent3,adverseCompleteEvent4,adverseCompleteEvent5,adverseCompleteEvent6,adverseCompleteEvent7,adverseCompleteEvent8,adverseCompleteEvent9,adverseCompleteEvent10,adverseCompleteEvent11,adverseCompleteEvent12,adverseCompleteEvent13,adverseCompleteEvent14,adverseCompleteEvent15,adverseCompleteEvent16,adverseCompleteEvent17,adverseCompleteEvent18,adverseCompleteEvent19,adverseCompleteEvent20,adverseCompleteEvent21,adverseCompleteEvent22,adverseCompleteEvent23,adverseCompleteEvent24,adverseCompleteEvent25,adverseCompleteEvent26,adverseCompleteEvent27,adverseCompleteEvent28,adverseCompleteEvent29,adverseCompleteEvent30,adverseCompleteEvent31,adverseCompleteEvent32,adverseCompleteEvent33,adverseCompleteEvent34,adverseCompleteEvent35,adverseCompleteEvent36,adverseCompleteEvent37,adverseCompleteEvent38,adverseCompleteEvent39,adverseCompleteEvent40,taskReward]
    <;> norm_num
  have hp : rawVisits adverseCompleteS41Before [.query 1] = 33 := by decide
  have hn : rawVisits adverseCompleteS41Before ([.query 1]++[.hydeRetriever 1]) = 11 := by decide
  have hz : (controlPenalty savedCref uniformQuoteError unitRoleUnused .complete) adverseCompleteS41Before [.query 1] (.hydeRetriever 1) = 0 := by
    apply control_penalty_empty_of_prior_terminal .complete savedCref uniformQuoteError adverseCompleteS41Before [.query 1] (.hydeRetriever 1) 8 (by decide)
    · decide
    · decide
  unfold indexScore
  rw [hs,hp,hn,hz]
  simp only [BackupStat.mean]
  norm_num

theorem adverseCompleteS41D1I1 : indexScore (7/5) (controlPenalty savedCref uniformQuoteError unitRoleUnused .complete) adverseCompleteS41Before [.query 1] (.hydeRetriever 0) = treeIndex ((0/1)/11) (7/5) 0 33 11 := by
  have hs : replayBackup adverseCompleteS41Before emptyStatistics ([.query 1]++[.hydeRetriever 0]) = ⟨11,(0/1)⟩ := by
    rw [replayBackup_empty_closed_form]
    simp +decide [backedEvents,adverseCompleteS41Before,adverseCompleteProposal,adverseCompleteEvent1,adverseCompleteEvent2,adverseCompleteEvent3,adverseCompleteEvent4,adverseCompleteEvent5,adverseCompleteEvent6,adverseCompleteEvent7,adverseCompleteEvent8,adverseCompleteEvent9,adverseCompleteEvent10,adverseCompleteEvent11,adverseCompleteEvent12,adverseCompleteEvent13,adverseCompleteEvent14,adverseCompleteEvent15,adverseCompleteEvent16,adverseCompleteEvent17,adverseCompleteEvent18,adverseCompleteEvent19,adverseCompleteEvent20,adverseCompleteEvent21,adverseCompleteEvent22,adverseCompleteEvent23,adverseCompleteEvent24,adverseCompleteEvent25,adverseCompleteEvent26,adverseCompleteEvent27,adverseCompleteEvent28,adverseCompleteEvent29,adverseCompleteEvent30,adverseCompleteEvent31,adverseCompleteEvent32,adverseCompleteEvent33,adverseCompleteEvent34,adverseCompleteEvent35,adverseCompleteEvent36,adverseCompleteEvent37,adverseCompleteEvent38,adverseCompleteEvent39,adverseCompleteEvent40,taskReward]
    <;> norm_num
  have hp : rawVisits adverseCompleteS41Before [.query 1] = 33 := by decide
  have hn : rawVisits adverseCompleteS41Before ([.query 1]++[.hydeRetriever 0]) = 11 := by decide
  have hz : (controlPenalty savedCref uniformQuoteError unitRoleUnused .complete) adverseCompleteS41Before [.query 1] (.hydeRetriever 0) = 0 := by
    apply control_penalty_empty_of_prior_terminal .complete savedCref uniformQuoteError adverseCompleteS41Before [.query 1] (.hydeRetriever 0) 1 (by decide)
    · decide
    · decide
  unfold indexScore
  rw [hs,hp,hn,hz]
  simp only [BackupStat.mean]
  norm_num

theorem adverseCompleteS41D1I2 : indexScore (7/5) (controlPenalty savedCref uniformQuoteError unitRoleUnused .complete) adverseCompleteS41Before [.query 1] (.hydeRetriever 2) = treeIndex ((0/1)/10) (7/5) 0 33 10 := by
  have hs : replayBackup adverseCompleteS41Before emptyStatistics ([.query 1]++[.hydeRetriever 2]) = ⟨10,(0/1)⟩ := by
    rw [replayBackup_empty_closed_form]
    simp +decide [backedEvents,adverseCompleteS41Before,adverseCompleteProposal,adverseCompleteEvent1,adverseCompleteEvent2,adverseCompleteEvent3,adverseCompleteEvent4,adverseCompleteEvent5,adverseCompleteEvent6,adverseCompleteEvent7,adverseCompleteEvent8,adverseCompleteEvent9,adverseCompleteEvent10,adverseCompleteEvent11,adverseCompleteEvent12,adverseCompleteEvent13,adverseCompleteEvent14,adverseCompleteEvent15,adverseCompleteEvent16,adverseCompleteEvent17,adverseCompleteEvent18,adverseCompleteEvent19,adverseCompleteEvent20,adverseCompleteEvent21,adverseCompleteEvent22,adverseCompleteEvent23,adverseCompleteEvent24,adverseCompleteEvent25,adverseCompleteEvent26,adverseCompleteEvent27,adverseCompleteEvent28,adverseCompleteEvent29,adverseCompleteEvent30,adverseCompleteEvent31,adverseCompleteEvent32,adverseCompleteEvent33,adverseCompleteEvent34,adverseCompleteEvent35,adverseCompleteEvent36,adverseCompleteEvent37,adverseCompleteEvent38,adverseCompleteEvent39,adverseCompleteEvent40,taskReward]
    <;> norm_num
  have hp : rawVisits adverseCompleteS41Before [.query 1] = 33 := by decide
  have hn : rawVisits adverseCompleteS41Before ([.query 1]++[.hydeRetriever 2]) = 10 := by decide
  have hz : (controlPenalty savedCref uniformQuoteError unitRoleUnused .complete) adverseCompleteS41Before [.query 1] (.hydeRetriever 2) = 0 := by
    apply control_penalty_empty_of_prior_terminal .complete savedCref uniformQuoteError adverseCompleteS41Before [.query 1] (.hydeRetriever 2) 10 (by decide)
    · decide
    · decide
  unfold indexScore
  rw [hs,hp,hn,hz]
  simp only [BackupStat.mean]
  norm_num

theorem adverseCompleteS41D1Cmp0 : indexScore (7/5) (controlPenalty savedCref uniformQuoteError unitRoleUnused .complete) adverseCompleteS41Before [.query 1] (.hydeRetriever 1) < indexScore (7/5) (controlPenalty savedCref uniformQuoteError unitRoleUnused .complete) adverseCompleteS41Before [.query 1] (.hydeRetriever 2) := by
  rw [adverseCompleteS41D1I0,adverseCompleteS41D1I2]
  have h := index_strict_order_from_intervals ((0/1)/10) ((0/1)/11) 0 0 (10392053/12500000) (9908437/12500000)
    (treeBonus (7/5) 33 10) (treeBonus (7/5) 33 11)
    (trajectory_bonus_33_10).1 (trajectory_bonus_33_11).2 (by norm_num)
  simpa only [treeIndex,sub_zero] using h

theorem adverseCompleteS41D1Cmp1 : indexScore (7/5) (controlPenalty savedCref uniformQuoteError unitRoleUnused .complete) adverseCompleteS41Before [.query 1] (.hydeRetriever 0) < indexScore (7/5) (controlPenalty savedCref uniformQuoteError unitRoleUnused .complete) adverseCompleteS41Before [.query 1] (.hydeRetriever 2) := by
  rw [adverseCompleteS41D1I1,adverseCompleteS41D1I2]
  have h := index_strict_order_from_intervals ((0/1)/10) ((0/1)/11) 0 0 (10392053/12500000) (9908437/12500000)
    (treeBonus (7/5) 33 10) (treeBonus (7/5) 33 11)
    (trajectory_bonus_33_10).1 (trajectory_bonus_33_11).2 (by norm_num)
  simpa only [treeIndex,sub_zero] using h

theorem adverseCompleteS41Choice1 : nativeFirstChoice (indexScore (7/5) (controlPenalty savedCref uniformQuoteError unitRoleUnused .complete) adverseCompleteS41Before [.query 1]) adverseCompleteS41Before [.query 1] = .hydeRetriever 2 := by
  apply visited_choice_from_ordered_certificate _ _ [.query 1] [.hydeRetriever 1,.hydeRetriever 0] [] (.hydeRetriever 2) (by decide)
  · intro a ha
    have ho : orderedLegalAvailable [.query 1] = [.hydeRetriever 1,.hydeRetriever 0,.hydeRetriever 2] := by decide
    rw [ho] at ha
    simp only [List.mem_cons,List.not_mem_nil,or_false] at ha
    rcases ha with rfl | rfl | rfl <;> decide
  · intro a ha
    simp only [List.mem_cons,List.not_mem_nil,or_false] at ha
    rcases ha with rfl | rfl
    · exact adverseCompleteS41D1Cmp0
    · exact adverseCompleteS41D1Cmp1
  · simp

theorem adverseCompleteS41D2I0 : indexScore (7/5) (controlPenalty savedCref uniformQuoteError unitRoleUnused .complete) adverseCompleteS41Before [.query 1,.hydeRetriever 2] (.selection 1) = treeIndex ((0/1)/3) (7/5) 0 10 3 := by
  have hs : replayBackup adverseCompleteS41Before emptyStatistics ([.query 1,.hydeRetriever 2]++[.selection 1]) = ⟨3,(0/1)⟩ := by
    rw [replayBackup_empty_closed_form]
    simp +decide [backedEvents,adverseCompleteS41Before,adverseCompleteProposal,adverseCompleteEvent1,adverseCompleteEvent2,adverseCompleteEvent3,adverseCompleteEvent4,adverseCompleteEvent5,adverseCompleteEvent6,adverseCompleteEvent7,adverseCompleteEvent8,adverseCompleteEvent9,adverseCompleteEvent10,adverseCompleteEvent11,adverseCompleteEvent12,adverseCompleteEvent13,adverseCompleteEvent14,adverseCompleteEvent15,adverseCompleteEvent16,adverseCompleteEvent17,adverseCompleteEvent18,adverseCompleteEvent19,adverseCompleteEvent20,adverseCompleteEvent21,adverseCompleteEvent22,adverseCompleteEvent23,adverseCompleteEvent24,adverseCompleteEvent25,adverseCompleteEvent26,adverseCompleteEvent27,adverseCompleteEvent28,adverseCompleteEvent29,adverseCompleteEvent30,adverseCompleteEvent31,adverseCompleteEvent32,adverseCompleteEvent33,adverseCompleteEvent34,adverseCompleteEvent35,adverseCompleteEvent36,adverseCompleteEvent37,adverseCompleteEvent38,adverseCompleteEvent39,adverseCompleteEvent40,taskReward]
    <;> norm_num
  have hp : rawVisits adverseCompleteS41Before [.query 1,.hydeRetriever 2] = 10 := by decide
  have hn : rawVisits adverseCompleteS41Before ([.query 1,.hydeRetriever 2]++[.selection 1]) = 3 := by decide
  have hz : (controlPenalty savedCref uniformQuoteError unitRoleUnused .complete) adverseCompleteS41Before [.query 1,.hydeRetriever 2] (.selection 1) = 0 := by
    apply control_penalty_empty_of_prior_terminal .complete savedCref uniformQuoteError adverseCompleteS41Before [.query 1,.hydeRetriever 2] (.selection 1) 16 (by decide)
    · decide
    · decide
  unfold indexScore
  rw [hs,hp,hn,hz]
  simp only [BackupStat.mean]
  norm_num

theorem adverseCompleteS41D2I1 : indexScore (7/5) (controlPenalty savedCref uniformQuoteError unitRoleUnused .complete) adverseCompleteS41Before [.query 1,.hydeRetriever 2] (.selection 2) = treeIndex ((0/1)/2) (7/5) 0 10 2 := by
  have hs : replayBackup adverseCompleteS41Before emptyStatistics ([.query 1,.hydeRetriever 2]++[.selection 2]) = ⟨2,(0/1)⟩ := by
    rw [replayBackup_empty_closed_form]
    simp +decide [backedEvents,adverseCompleteS41Before,adverseCompleteProposal,adverseCompleteEvent1,adverseCompleteEvent2,adverseCompleteEvent3,adverseCompleteEvent4,adverseCompleteEvent5,adverseCompleteEvent6,adverseCompleteEvent7,adverseCompleteEvent8,adverseCompleteEvent9,adverseCompleteEvent10,adverseCompleteEvent11,adverseCompleteEvent12,adverseCompleteEvent13,adverseCompleteEvent14,adverseCompleteEvent15,adverseCompleteEvent16,adverseCompleteEvent17,adverseCompleteEvent18,adverseCompleteEvent19,adverseCompleteEvent20,adverseCompleteEvent21,adverseCompleteEvent22,adverseCompleteEvent23,adverseCompleteEvent24,adverseCompleteEvent25,adverseCompleteEvent26,adverseCompleteEvent27,adverseCompleteEvent28,adverseCompleteEvent29,adverseCompleteEvent30,adverseCompleteEvent31,adverseCompleteEvent32,adverseCompleteEvent33,adverseCompleteEvent34,adverseCompleteEvent35,adverseCompleteEvent36,adverseCompleteEvent37,adverseCompleteEvent38,adverseCompleteEvent39,adverseCompleteEvent40,taskReward]
    <;> norm_num
  have hp : rawVisits adverseCompleteS41Before [.query 1,.hydeRetriever 2] = 10 := by decide
  have hn : rawVisits adverseCompleteS41Before ([.query 1,.hydeRetriever 2]++[.selection 2]) = 2 := by decide
  have hz : (controlPenalty savedCref uniformQuoteError unitRoleUnused .complete) adverseCompleteS41Before [.query 1,.hydeRetriever 2] (.selection 2) = 0 := by
    apply control_penalty_empty_of_prior_terminal .complete savedCref uniformQuoteError adverseCompleteS41Before [.query 1,.hydeRetriever 2] (.selection 2) 19 (by decide)
    · decide
    · decide
  unfold indexScore
  rw [hs,hp,hn,hz]
  simp only [BackupStat.mean]
  norm_num

theorem adverseCompleteS41D2I2 : indexScore (7/5) (controlPenalty savedCref uniformQuoteError unitRoleUnused .complete) adverseCompleteS41Before [.query 1,.hydeRetriever 2] (.selection 3) = treeIndex ((0/1)/2) (7/5) 0 10 2 := by
  have hs : replayBackup adverseCompleteS41Before emptyStatistics ([.query 1,.hydeRetriever 2]++[.selection 3]) = ⟨2,(0/1)⟩ := by
    rw [replayBackup_empty_closed_form]
    simp +decide [backedEvents,adverseCompleteS41Before,adverseCompleteProposal,adverseCompleteEvent1,adverseCompleteEvent2,adverseCompleteEvent3,adverseCompleteEvent4,adverseCompleteEvent5,adverseCompleteEvent6,adverseCompleteEvent7,adverseCompleteEvent8,adverseCompleteEvent9,adverseCompleteEvent10,adverseCompleteEvent11,adverseCompleteEvent12,adverseCompleteEvent13,adverseCompleteEvent14,adverseCompleteEvent15,adverseCompleteEvent16,adverseCompleteEvent17,adverseCompleteEvent18,adverseCompleteEvent19,adverseCompleteEvent20,adverseCompleteEvent21,adverseCompleteEvent22,adverseCompleteEvent23,adverseCompleteEvent24,adverseCompleteEvent25,adverseCompleteEvent26,adverseCompleteEvent27,adverseCompleteEvent28,adverseCompleteEvent29,adverseCompleteEvent30,adverseCompleteEvent31,adverseCompleteEvent32,adverseCompleteEvent33,adverseCompleteEvent34,adverseCompleteEvent35,adverseCompleteEvent36,adverseCompleteEvent37,adverseCompleteEvent38,adverseCompleteEvent39,adverseCompleteEvent40,taskReward]
    <;> norm_num
  have hp : rawVisits adverseCompleteS41Before [.query 1,.hydeRetriever 2] = 10 := by decide
  have hn : rawVisits adverseCompleteS41Before ([.query 1,.hydeRetriever 2]++[.selection 3]) = 2 := by decide
  have hz : (controlPenalty savedCref uniformQuoteError unitRoleUnused .complete) adverseCompleteS41Before [.query 1,.hydeRetriever 2] (.selection 3) = 0 := by
    apply control_penalty_empty_of_prior_terminal .complete savedCref uniformQuoteError adverseCompleteS41Before [.query 1,.hydeRetriever 2] (.selection 3) 22 (by decide)
    · decide
    · decide
  unfold indexScore
  rw [hs,hp,hn,hz]
  simp only [BackupStat.mean]
  norm_num

theorem adverseCompleteS41D2I3 : indexScore (7/5) (controlPenalty savedCref uniformQuoteError unitRoleUnused .complete) adverseCompleteS41Before [.query 1,.hydeRetriever 2] (.selection 0) = treeIndex ((0/1)/2) (7/5) 0 10 2 := by
  have hs : replayBackup adverseCompleteS41Before emptyStatistics ([.query 1,.hydeRetriever 2]++[.selection 0]) = ⟨2,(0/1)⟩ := by
    rw [replayBackup_empty_closed_form]
    simp +decide [backedEvents,adverseCompleteS41Before,adverseCompleteProposal,adverseCompleteEvent1,adverseCompleteEvent2,adverseCompleteEvent3,adverseCompleteEvent4,adverseCompleteEvent5,adverseCompleteEvent6,adverseCompleteEvent7,adverseCompleteEvent8,adverseCompleteEvent9,adverseCompleteEvent10,adverseCompleteEvent11,adverseCompleteEvent12,adverseCompleteEvent13,adverseCompleteEvent14,adverseCompleteEvent15,adverseCompleteEvent16,adverseCompleteEvent17,adverseCompleteEvent18,adverseCompleteEvent19,adverseCompleteEvent20,adverseCompleteEvent21,adverseCompleteEvent22,adverseCompleteEvent23,adverseCompleteEvent24,adverseCompleteEvent25,adverseCompleteEvent26,adverseCompleteEvent27,adverseCompleteEvent28,adverseCompleteEvent29,adverseCompleteEvent30,adverseCompleteEvent31,adverseCompleteEvent32,adverseCompleteEvent33,adverseCompleteEvent34,adverseCompleteEvent35,adverseCompleteEvent36,adverseCompleteEvent37,adverseCompleteEvent38,adverseCompleteEvent39,adverseCompleteEvent40,taskReward]
    <;> norm_num
  have hp : rawVisits adverseCompleteS41Before [.query 1,.hydeRetriever 2] = 10 := by decide
  have hn : rawVisits adverseCompleteS41Before ([.query 1,.hydeRetriever 2]++[.selection 0]) = 2 := by decide
  have hz : (controlPenalty savedCref uniformQuoteError unitRoleUnused .complete) adverseCompleteS41Before [.query 1,.hydeRetriever 2] (.selection 0) = 0 := by
    apply control_penalty_empty_of_prior_terminal .complete savedCref uniformQuoteError adverseCompleteS41Before [.query 1,.hydeRetriever 2] (.selection 0) 10 (by decide)
    · decide
    · decide
  unfold indexScore
  rw [hs,hp,hn,hz]
  simp only [BackupStat.mean]
  norm_num

theorem adverseCompleteS41D2Cmp0 : indexScore (7/5) (controlPenalty savedCref uniformQuoteError unitRoleUnused .complete) adverseCompleteS41Before [.query 1,.hydeRetriever 2] (.selection 1) < indexScore (7/5) (controlPenalty savedCref uniformQuoteError unitRoleUnused .complete) adverseCompleteS41Before [.query 1,.hydeRetriever 2] (.selection 2) := by
  rw [adverseCompleteS41D2I0,adverseCompleteS41D2I1]
  have h := index_strict_order_from_intervals ((0/1)/2) ((0/1)/3) 0 0 (38323761/25000000) (1251649/1000000)
    (treeBonus (7/5) 10 2) (treeBonus (7/5) 10 3)
    (trajectory_bonus_10_2).1 (trajectory_bonus_10_3).2 (by norm_num)
  simpa only [treeIndex,sub_zero] using h

theorem adverseCompleteS41D2Cmp2 : indexScore (7/5) (controlPenalty savedCref uniformQuoteError unitRoleUnused .complete) adverseCompleteS41Before [.query 1,.hydeRetriever 2] (.selection 3) ≤ indexScore (7/5) (controlPenalty savedCref uniformQuoteError unitRoleUnused .complete) adverseCompleteS41Before [.query 1,.hydeRetriever 2] (.selection 2) := by
  rw [adverseCompleteS41D2I2,adverseCompleteS41D2I1]

theorem adverseCompleteS41D2Cmp3 : indexScore (7/5) (controlPenalty savedCref uniformQuoteError unitRoleUnused .complete) adverseCompleteS41Before [.query 1,.hydeRetriever 2] (.selection 0) ≤ indexScore (7/5) (controlPenalty savedCref uniformQuoteError unitRoleUnused .complete) adverseCompleteS41Before [.query 1,.hydeRetriever 2] (.selection 2) := by
  rw [adverseCompleteS41D2I3,adverseCompleteS41D2I1]

theorem adverseCompleteS41Choice2 : nativeFirstChoice (indexScore (7/5) (controlPenalty savedCref uniformQuoteError unitRoleUnused .complete) adverseCompleteS41Before [.query 1,.hydeRetriever 2]) adverseCompleteS41Before [.query 1,.hydeRetriever 2] = .selection 2 := by
  apply visited_choice_from_ordered_certificate _ _ [.query 1,.hydeRetriever 2] [.selection 1] [.selection 3,.selection 0] (.selection 2) (by decide)
  · intro a ha
    have ho : orderedLegalAvailable [.query 1,.hydeRetriever 2] = [.selection 1,.selection 2,.selection 3,.selection 0] := by decide
    rw [ho] at ha
    simp only [List.mem_cons,List.not_mem_nil,or_false] at ha
    rcases ha with rfl | rfl | rfl | rfl <;> decide
  · intro a ha
    simp only [List.mem_cons,List.not_mem_nil,or_false] at ha
    rcases ha with rfl
    · exact adverseCompleteS41D2Cmp0
  · intro a ha
    simp only [List.mem_cons,List.not_mem_nil,or_false] at ha
    rcases ha with rfl | rfl
    · exact adverseCompleteS41D2Cmp2
    · exact adverseCompleteS41D2Cmp3

theorem adverseCompleteS41ActualEvent : nativeEvent budgetTape (7/5) (controlPenalty savedCref uniformQuoteError unitRoleUnused .complete)
    (taskReward true (2/5) (1/2)) adverseCompleteS41Before = adverseCompleteEvent41 := by
  have hs0 := native_select_existing_step budgetTape (7/5) (controlPenalty savedCref uniformQuoteError unitRoleUnused .complete) adverseCompleteS41Before 8 [] (.query 1)
    (by decide) (by decide) adverseCompleteS41Choice0
  have hs1 := native_select_existing_step budgetTape (7/5) (controlPenalty savedCref uniformQuoteError unitRoleUnused .complete) adverseCompleteS41Before 7 [.query 1] (.hydeRetriever 2)
    (by decide) (by decide) adverseCompleteS41Choice1
  have hs2 := native_select_existing_step budgetTape (7/5) (controlPenalty savedCref uniformQuoteError unitRoleUnused .complete) adverseCompleteS41Before 6 [.query 1,.hydeRetriever 2] (.selection 2)
    (by decide) (by decide) adverseCompleteS41Choice2
  have hnew := native_select_new_step budgetTape (7/5) (controlPenalty savedCref uniformQuoteError unitRoleUnused .complete) adverseCompleteS41Before 5 [.query 1,.hydeRetriever 2,.selection 2]
    [.width 3,.width 1,.width 2] (.width 3) (by decide) (by decide) (by decide) (by decide)
  have hs : nativeSelect budgetTape (7/5) (controlPenalty savedCref uniformQuoteError unitRoleUnused .complete) adverseCompleteS41Before 9 [] = [.query 1,.hydeRetriever 2,.selection 2,.width 3] := by
    rw [hs0]
    change nativeSelect budgetTape (7/5) (controlPenalty savedCref uniformQuoteError unitRoleUnused .complete) adverseCompleteS41Before 8 [.query 1] = _
    rw [hs1]
    change nativeSelect budgetTape (7/5) (controlPenalty savedCref uniformQuoteError unitRoleUnused .complete) adverseCompleteS41Before 7 [.query 1,.hydeRetriever 2] = _
    rw [hs2]
    change nativeSelect budgetTape (7/5) (controlPenalty savedCref uniformQuoteError unitRoleUnused .complete) adverseCompleteS41Before 6 [.query 1,.hydeRetriever 2,.selection 2] = _
    rw [hnew] <;> rfl
  have hr : repairedRollout budgetTape adverseCompleteS41Before 9 [.query 1,.hydeRetriever 2,.selection 2,.width 3] = [.query 1,.hydeRetriever 2,.selection 2,.width 3,.stop,.reranker 0,.topm 0,.context 0,.answer 0] := by decide
  simp only [nativeEvent,hs,hr]
  rfl

def adverseCompleteS42Before := adverseCompleteProposal.take 41

theorem adverseCompleteS42Choice0 : nativeFirstChoice (indexScore (7/5) (controlPenalty savedCref uniformQuoteError unitRoleUnused .complete) adverseCompleteS42Before []) adverseCompleteS42Before [] = .query 1 := by
  apply complete_root_from_physical_gap adverseCompleteS42Before (adverseComplete_prefix_rewards 41) (by decide)
  · intro q; fin_cases q <;> decide
  · exact AgentUCTNextExact.adverse_complete_hyde_root_suffix_empty 41 (by omega)
  · intro q hq
    exact AgentUCTNextExact.adverse_complete_normal_root_physical_quote_exact 41 (by omega) q hq

theorem adverseCompleteS42D1I0 : indexScore (7/5) (controlPenalty savedCref uniformQuoteError unitRoleUnused .complete) adverseCompleteS42Before [.query 1] (.hydeRetriever 1) = treeIndex ((0/1)/11) (7/5) 0 34 11 := by
  have hs : replayBackup adverseCompleteS42Before emptyStatistics ([.query 1]++[.hydeRetriever 1]) = ⟨11,(0/1)⟩ := by
    rw [replayBackup_empty_closed_form]
    simp +decide [backedEvents,adverseCompleteS42Before,adverseCompleteProposal,adverseCompleteEvent1,adverseCompleteEvent2,adverseCompleteEvent3,adverseCompleteEvent4,adverseCompleteEvent5,adverseCompleteEvent6,adverseCompleteEvent7,adverseCompleteEvent8,adverseCompleteEvent9,adverseCompleteEvent10,adverseCompleteEvent11,adverseCompleteEvent12,adverseCompleteEvent13,adverseCompleteEvent14,adverseCompleteEvent15,adverseCompleteEvent16,adverseCompleteEvent17,adverseCompleteEvent18,adverseCompleteEvent19,adverseCompleteEvent20,adverseCompleteEvent21,adverseCompleteEvent22,adverseCompleteEvent23,adverseCompleteEvent24,adverseCompleteEvent25,adverseCompleteEvent26,adverseCompleteEvent27,adverseCompleteEvent28,adverseCompleteEvent29,adverseCompleteEvent30,adverseCompleteEvent31,adverseCompleteEvent32,adverseCompleteEvent33,adverseCompleteEvent34,adverseCompleteEvent35,adverseCompleteEvent36,adverseCompleteEvent37,adverseCompleteEvent38,adverseCompleteEvent39,adverseCompleteEvent40,adverseCompleteEvent41,taskReward]
    <;> norm_num
  have hp : rawVisits adverseCompleteS42Before [.query 1] = 34 := by decide
  have hn : rawVisits adverseCompleteS42Before ([.query 1]++[.hydeRetriever 1]) = 11 := by decide
  have hz : (controlPenalty savedCref uniformQuoteError unitRoleUnused .complete) adverseCompleteS42Before [.query 1] (.hydeRetriever 1) = 0 := by
    apply control_penalty_empty_of_prior_terminal .complete savedCref uniformQuoteError adverseCompleteS42Before [.query 1] (.hydeRetriever 1) 8 (by decide)
    · decide
    · decide
  unfold indexScore
  rw [hs,hp,hn,hz]
  simp only [BackupStat.mean]
  norm_num

theorem adverseCompleteS42D1I1 : indexScore (7/5) (controlPenalty savedCref uniformQuoteError unitRoleUnused .complete) adverseCompleteS42Before [.query 1] (.hydeRetriever 0) = treeIndex ((0/1)/11) (7/5) 0 34 11 := by
  have hs : replayBackup adverseCompleteS42Before emptyStatistics ([.query 1]++[.hydeRetriever 0]) = ⟨11,(0/1)⟩ := by
    rw [replayBackup_empty_closed_form]
    simp +decide [backedEvents,adverseCompleteS42Before,adverseCompleteProposal,adverseCompleteEvent1,adverseCompleteEvent2,adverseCompleteEvent3,adverseCompleteEvent4,adverseCompleteEvent5,adverseCompleteEvent6,adverseCompleteEvent7,adverseCompleteEvent8,adverseCompleteEvent9,adverseCompleteEvent10,adverseCompleteEvent11,adverseCompleteEvent12,adverseCompleteEvent13,adverseCompleteEvent14,adverseCompleteEvent15,adverseCompleteEvent16,adverseCompleteEvent17,adverseCompleteEvent18,adverseCompleteEvent19,adverseCompleteEvent20,adverseCompleteEvent21,adverseCompleteEvent22,adverseCompleteEvent23,adverseCompleteEvent24,adverseCompleteEvent25,adverseCompleteEvent26,adverseCompleteEvent27,adverseCompleteEvent28,adverseCompleteEvent29,adverseCompleteEvent30,adverseCompleteEvent31,adverseCompleteEvent32,adverseCompleteEvent33,adverseCompleteEvent34,adverseCompleteEvent35,adverseCompleteEvent36,adverseCompleteEvent37,adverseCompleteEvent38,adverseCompleteEvent39,adverseCompleteEvent40,adverseCompleteEvent41,taskReward]
    <;> norm_num
  have hp : rawVisits adverseCompleteS42Before [.query 1] = 34 := by decide
  have hn : rawVisits adverseCompleteS42Before ([.query 1]++[.hydeRetriever 0]) = 11 := by decide
  have hz : (controlPenalty savedCref uniformQuoteError unitRoleUnused .complete) adverseCompleteS42Before [.query 1] (.hydeRetriever 0) = 0 := by
    apply control_penalty_empty_of_prior_terminal .complete savedCref uniformQuoteError adverseCompleteS42Before [.query 1] (.hydeRetriever 0) 1 (by decide)
    · decide
    · decide
  unfold indexScore
  rw [hs,hp,hn,hz]
  simp only [BackupStat.mean]
  norm_num

theorem adverseCompleteS42D1I2 : indexScore (7/5) (controlPenalty savedCref uniformQuoteError unitRoleUnused .complete) adverseCompleteS42Before [.query 1] (.hydeRetriever 2) = treeIndex ((0/1)/11) (7/5) 0 34 11 := by
  have hs : replayBackup adverseCompleteS42Before emptyStatistics ([.query 1]++[.hydeRetriever 2]) = ⟨11,(0/1)⟩ := by
    rw [replayBackup_empty_closed_form]
    simp +decide [backedEvents,adverseCompleteS42Before,adverseCompleteProposal,adverseCompleteEvent1,adverseCompleteEvent2,adverseCompleteEvent3,adverseCompleteEvent4,adverseCompleteEvent5,adverseCompleteEvent6,adverseCompleteEvent7,adverseCompleteEvent8,adverseCompleteEvent9,adverseCompleteEvent10,adverseCompleteEvent11,adverseCompleteEvent12,adverseCompleteEvent13,adverseCompleteEvent14,adverseCompleteEvent15,adverseCompleteEvent16,adverseCompleteEvent17,adverseCompleteEvent18,adverseCompleteEvent19,adverseCompleteEvent20,adverseCompleteEvent21,adverseCompleteEvent22,adverseCompleteEvent23,adverseCompleteEvent24,adverseCompleteEvent25,adverseCompleteEvent26,adverseCompleteEvent27,adverseCompleteEvent28,adverseCompleteEvent29,adverseCompleteEvent30,adverseCompleteEvent31,adverseCompleteEvent32,adverseCompleteEvent33,adverseCompleteEvent34,adverseCompleteEvent35,adverseCompleteEvent36,adverseCompleteEvent37,adverseCompleteEvent38,adverseCompleteEvent39,adverseCompleteEvent40,adverseCompleteEvent41,taskReward]
    <;> norm_num
  have hp : rawVisits adverseCompleteS42Before [.query 1] = 34 := by decide
  have hn : rawVisits adverseCompleteS42Before ([.query 1]++[.hydeRetriever 2]) = 11 := by decide
  have hz : (controlPenalty savedCref uniformQuoteError unitRoleUnused .complete) adverseCompleteS42Before [.query 1] (.hydeRetriever 2) = 0 := by
    apply control_penalty_empty_of_prior_terminal .complete savedCref uniformQuoteError adverseCompleteS42Before [.query 1] (.hydeRetriever 2) 10 (by decide)
    · decide
    · decide
  unfold indexScore
  rw [hs,hp,hn,hz]
  simp only [BackupStat.mean]
  norm_num

theorem adverseCompleteS42D1Cmp1 : indexScore (7/5) (controlPenalty savedCref uniformQuoteError unitRoleUnused .complete) adverseCompleteS42Before [.query 1] (.hydeRetriever 0) ≤ indexScore (7/5) (controlPenalty savedCref uniformQuoteError unitRoleUnused .complete) adverseCompleteS42Before [.query 1] (.hydeRetriever 1) := by
  rw [adverseCompleteS42D1I1,adverseCompleteS42D1I0]

theorem adverseCompleteS42D1Cmp2 : indexScore (7/5) (controlPenalty savedCref uniformQuoteError unitRoleUnused .complete) adverseCompleteS42Before [.query 1] (.hydeRetriever 2) ≤ indexScore (7/5) (controlPenalty savedCref uniformQuoteError unitRoleUnused .complete) adverseCompleteS42Before [.query 1] (.hydeRetriever 1) := by
  rw [adverseCompleteS42D1I2,adverseCompleteS42D1I0]

theorem adverseCompleteS42Choice1 : nativeFirstChoice (indexScore (7/5) (controlPenalty savedCref uniformQuoteError unitRoleUnused .complete) adverseCompleteS42Before [.query 1]) adverseCompleteS42Before [.query 1] = .hydeRetriever 1 := by
  apply visited_choice_from_ordered_certificate _ _ [.query 1] [] [.hydeRetriever 0,.hydeRetriever 2] (.hydeRetriever 1) (by decide)
  · intro a ha
    have ho : orderedLegalAvailable [.query 1] = [.hydeRetriever 1,.hydeRetriever 0,.hydeRetriever 2] := by decide
    rw [ho] at ha
    simp only [List.mem_cons,List.not_mem_nil,or_false] at ha
    rcases ha with rfl | rfl | rfl <;> decide
  · simp
  · intro a ha
    simp only [List.mem_cons,List.not_mem_nil,or_false] at ha
    rcases ha with rfl | rfl
    · exact adverseCompleteS42D1Cmp1
    · exact adverseCompleteS42D1Cmp2

theorem adverseCompleteS42D2I0 : indexScore (7/5) (controlPenalty savedCref uniformQuoteError unitRoleUnused .complete) adverseCompleteS42Before [.query 1,.hydeRetriever 1] (.selection 1) = treeIndex ((0/1)/3) (7/5) 0 11 3 := by
  have hs : replayBackup adverseCompleteS42Before emptyStatistics ([.query 1,.hydeRetriever 1]++[.selection 1]) = ⟨3,(0/1)⟩ := by
    rw [replayBackup_empty_closed_form]
    simp +decide [backedEvents,adverseCompleteS42Before,adverseCompleteProposal,adverseCompleteEvent1,adverseCompleteEvent2,adverseCompleteEvent3,adverseCompleteEvent4,adverseCompleteEvent5,adverseCompleteEvent6,adverseCompleteEvent7,adverseCompleteEvent8,adverseCompleteEvent9,adverseCompleteEvent10,adverseCompleteEvent11,adverseCompleteEvent12,adverseCompleteEvent13,adverseCompleteEvent14,adverseCompleteEvent15,adverseCompleteEvent16,adverseCompleteEvent17,adverseCompleteEvent18,adverseCompleteEvent19,adverseCompleteEvent20,adverseCompleteEvent21,adverseCompleteEvent22,adverseCompleteEvent23,adverseCompleteEvent24,adverseCompleteEvent25,adverseCompleteEvent26,adverseCompleteEvent27,adverseCompleteEvent28,adverseCompleteEvent29,adverseCompleteEvent30,adverseCompleteEvent31,adverseCompleteEvent32,adverseCompleteEvent33,adverseCompleteEvent34,adverseCompleteEvent35,adverseCompleteEvent36,adverseCompleteEvent37,adverseCompleteEvent38,adverseCompleteEvent39,adverseCompleteEvent40,adverseCompleteEvent41,taskReward]
    <;> norm_num
  have hp : rawVisits adverseCompleteS42Before [.query 1,.hydeRetriever 1] = 11 := by decide
  have hn : rawVisits adverseCompleteS42Before ([.query 1,.hydeRetriever 1]++[.selection 1]) = 3 := by decide
  have hz : (controlPenalty savedCref uniformQuoteError unitRoleUnused .complete) adverseCompleteS42Before [.query 1,.hydeRetriever 1] (.selection 1) = 0 := by
    apply control_penalty_empty_of_prior_terminal .complete savedCref uniformQuoteError adverseCompleteS42Before [.query 1,.hydeRetriever 1] (.selection 1) 14 (by decide)
    · decide
    · decide
  unfold indexScore
  rw [hs,hp,hn,hz]
  simp only [BackupStat.mean]
  norm_num

theorem adverseCompleteS42D2I1 : indexScore (7/5) (controlPenalty savedCref uniformQuoteError unitRoleUnused .complete) adverseCompleteS42Before [.query 1,.hydeRetriever 1] (.selection 2) = treeIndex ((0/1)/3) (7/5) 0 11 3 := by
  have hs : replayBackup adverseCompleteS42Before emptyStatistics ([.query 1,.hydeRetriever 1]++[.selection 2]) = ⟨3,(0/1)⟩ := by
    rw [replayBackup_empty_closed_form]
    simp +decide [backedEvents,adverseCompleteS42Before,adverseCompleteProposal,adverseCompleteEvent1,adverseCompleteEvent2,adverseCompleteEvent3,adverseCompleteEvent4,adverseCompleteEvent5,adverseCompleteEvent6,adverseCompleteEvent7,adverseCompleteEvent8,adverseCompleteEvent9,adverseCompleteEvent10,adverseCompleteEvent11,adverseCompleteEvent12,adverseCompleteEvent13,adverseCompleteEvent14,adverseCompleteEvent15,adverseCompleteEvent16,adverseCompleteEvent17,adverseCompleteEvent18,adverseCompleteEvent19,adverseCompleteEvent20,adverseCompleteEvent21,adverseCompleteEvent22,adverseCompleteEvent23,adverseCompleteEvent24,adverseCompleteEvent25,adverseCompleteEvent26,adverseCompleteEvent27,adverseCompleteEvent28,adverseCompleteEvent29,adverseCompleteEvent30,adverseCompleteEvent31,adverseCompleteEvent32,adverseCompleteEvent33,adverseCompleteEvent34,adverseCompleteEvent35,adverseCompleteEvent36,adverseCompleteEvent37,adverseCompleteEvent38,adverseCompleteEvent39,adverseCompleteEvent40,adverseCompleteEvent41,taskReward]
    <;> norm_num
  have hp : rawVisits adverseCompleteS42Before [.query 1,.hydeRetriever 1] = 11 := by decide
  have hn : rawVisits adverseCompleteS42Before ([.query 1,.hydeRetriever 1]++[.selection 2]) = 3 := by decide
  have hz : (controlPenalty savedCref uniformQuoteError unitRoleUnused .complete) adverseCompleteS42Before [.query 1,.hydeRetriever 1] (.selection 2) = 0 := by
    apply control_penalty_empty_of_prior_terminal .complete savedCref uniformQuoteError adverseCompleteS42Before [.query 1,.hydeRetriever 1] (.selection 2) 17 (by decide)
    · decide
    · decide
  unfold indexScore
  rw [hs,hp,hn,hz]
  simp only [BackupStat.mean]
  norm_num

theorem adverseCompleteS42D2I2 : indexScore (7/5) (controlPenalty savedCref uniformQuoteError unitRoleUnused .complete) adverseCompleteS42Before [.query 1,.hydeRetriever 1] (.selection 3) = treeIndex ((0/1)/2) (7/5) 0 11 2 := by
  have hs : replayBackup adverseCompleteS42Before emptyStatistics ([.query 1,.hydeRetriever 1]++[.selection 3]) = ⟨2,(0/1)⟩ := by
    rw [replayBackup_empty_closed_form]
    simp +decide [backedEvents,adverseCompleteS42Before,adverseCompleteProposal,adverseCompleteEvent1,adverseCompleteEvent2,adverseCompleteEvent3,adverseCompleteEvent4,adverseCompleteEvent5,adverseCompleteEvent6,adverseCompleteEvent7,adverseCompleteEvent8,adverseCompleteEvent9,adverseCompleteEvent10,adverseCompleteEvent11,adverseCompleteEvent12,adverseCompleteEvent13,adverseCompleteEvent14,adverseCompleteEvent15,adverseCompleteEvent16,adverseCompleteEvent17,adverseCompleteEvent18,adverseCompleteEvent19,adverseCompleteEvent20,adverseCompleteEvent21,adverseCompleteEvent22,adverseCompleteEvent23,adverseCompleteEvent24,adverseCompleteEvent25,adverseCompleteEvent26,adverseCompleteEvent27,adverseCompleteEvent28,adverseCompleteEvent29,adverseCompleteEvent30,adverseCompleteEvent31,adverseCompleteEvent32,adverseCompleteEvent33,adverseCompleteEvent34,adverseCompleteEvent35,adverseCompleteEvent36,adverseCompleteEvent37,adverseCompleteEvent38,adverseCompleteEvent39,adverseCompleteEvent40,adverseCompleteEvent41,taskReward]
    <;> norm_num
  have hp : rawVisits adverseCompleteS42Before [.query 1,.hydeRetriever 1] = 11 := by decide
  have hn : rawVisits adverseCompleteS42Before ([.query 1,.hydeRetriever 1]++[.selection 3]) = 2 := by decide
  have hz : (controlPenalty savedCref uniformQuoteError unitRoleUnused .complete) adverseCompleteS42Before [.query 1,.hydeRetriever 1] (.selection 3) = 0 := by
    apply control_penalty_empty_of_prior_terminal .complete savedCref uniformQuoteError adverseCompleteS42Before [.query 1,.hydeRetriever 1] (.selection 3) 20 (by decide)
    · decide
    · decide
  unfold indexScore
  rw [hs,hp,hn,hz]
  simp only [BackupStat.mean]
  norm_num

theorem adverseCompleteS42D2I3 : indexScore (7/5) (controlPenalty savedCref uniformQuoteError unitRoleUnused .complete) adverseCompleteS42Before [.query 1,.hydeRetriever 1] (.selection 0) = treeIndex ((0/1)/2) (7/5) 0 11 2 := by
  have hs : replayBackup adverseCompleteS42Before emptyStatistics ([.query 1,.hydeRetriever 1]++[.selection 0]) = ⟨2,(0/1)⟩ := by
    rw [replayBackup_empty_closed_form]
    simp +decide [backedEvents,adverseCompleteS42Before,adverseCompleteProposal,adverseCompleteEvent1,adverseCompleteEvent2,adverseCompleteEvent3,adverseCompleteEvent4,adverseCompleteEvent5,adverseCompleteEvent6,adverseCompleteEvent7,adverseCompleteEvent8,adverseCompleteEvent9,adverseCompleteEvent10,adverseCompleteEvent11,adverseCompleteEvent12,adverseCompleteEvent13,adverseCompleteEvent14,adverseCompleteEvent15,adverseCompleteEvent16,adverseCompleteEvent17,adverseCompleteEvent18,adverseCompleteEvent19,adverseCompleteEvent20,adverseCompleteEvent21,adverseCompleteEvent22,adverseCompleteEvent23,adverseCompleteEvent24,adverseCompleteEvent25,adverseCompleteEvent26,adverseCompleteEvent27,adverseCompleteEvent28,adverseCompleteEvent29,adverseCompleteEvent30,adverseCompleteEvent31,adverseCompleteEvent32,adverseCompleteEvent33,adverseCompleteEvent34,adverseCompleteEvent35,adverseCompleteEvent36,adverseCompleteEvent37,adverseCompleteEvent38,adverseCompleteEvent39,adverseCompleteEvent40,adverseCompleteEvent41,taskReward]
    <;> norm_num
  have hp : rawVisits adverseCompleteS42Before [.query 1,.hydeRetriever 1] = 11 := by decide
  have hn : rawVisits adverseCompleteS42Before ([.query 1,.hydeRetriever 1]++[.selection 0]) = 2 := by decide
  have hz : (controlPenalty savedCref uniformQuoteError unitRoleUnused .complete) adverseCompleteS42Before [.query 1,.hydeRetriever 1] (.selection 0) = 0 := by
    apply control_penalty_empty_of_prior_terminal .complete savedCref uniformQuoteError adverseCompleteS42Before [.query 1,.hydeRetriever 1] (.selection 0) 8 (by decide)
    · decide
    · decide
  unfold indexScore
  rw [hs,hp,hn,hz]
  simp only [BackupStat.mean]
  norm_num

theorem adverseCompleteS42D2Cmp0 : indexScore (7/5) (controlPenalty savedCref uniformQuoteError unitRoleUnused .complete) adverseCompleteS42Before [.query 1,.hydeRetriever 1] (.selection 1) < indexScore (7/5) (controlPenalty savedCref uniformQuoteError unitRoleUnused .complete) adverseCompleteS42Before [.query 1,.hydeRetriever 1] (.selection 3) := by
  rw [adverseCompleteS42D2I0,adverseCompleteS42D2I2]
  have h := index_strict_order_from_intervals ((0/1)/2) ((0/1)/3) 0 0 (39012883/25000000) (7963473/6250000)
    (treeBonus (7/5) 11 2) (treeBonus (7/5) 11 3)
    (trajectory_bonus_11_2).1 (trajectory_bonus_11_3).2 (by norm_num)
  simpa only [treeIndex,sub_zero] using h

theorem adverseCompleteS42D2Cmp1 : indexScore (7/5) (controlPenalty savedCref uniformQuoteError unitRoleUnused .complete) adverseCompleteS42Before [.query 1,.hydeRetriever 1] (.selection 2) < indexScore (7/5) (controlPenalty savedCref uniformQuoteError unitRoleUnused .complete) adverseCompleteS42Before [.query 1,.hydeRetriever 1] (.selection 3) := by
  rw [adverseCompleteS42D2I1,adverseCompleteS42D2I2]
  have h := index_strict_order_from_intervals ((0/1)/2) ((0/1)/3) 0 0 (39012883/25000000) (7963473/6250000)
    (treeBonus (7/5) 11 2) (treeBonus (7/5) 11 3)
    (trajectory_bonus_11_2).1 (trajectory_bonus_11_3).2 (by norm_num)
  simpa only [treeIndex,sub_zero] using h

theorem adverseCompleteS42D2Cmp3 : indexScore (7/5) (controlPenalty savedCref uniformQuoteError unitRoleUnused .complete) adverseCompleteS42Before [.query 1,.hydeRetriever 1] (.selection 0) ≤ indexScore (7/5) (controlPenalty savedCref uniformQuoteError unitRoleUnused .complete) adverseCompleteS42Before [.query 1,.hydeRetriever 1] (.selection 3) := by
  rw [adverseCompleteS42D2I3,adverseCompleteS42D2I2]

theorem adverseCompleteS42Choice2 : nativeFirstChoice (indexScore (7/5) (controlPenalty savedCref uniformQuoteError unitRoleUnused .complete) adverseCompleteS42Before [.query 1,.hydeRetriever 1]) adverseCompleteS42Before [.query 1,.hydeRetriever 1] = .selection 3 := by
  apply visited_choice_from_ordered_certificate _ _ [.query 1,.hydeRetriever 1] [.selection 1,.selection 2] [.selection 0] (.selection 3) (by decide)
  · intro a ha
    have ho : orderedLegalAvailable [.query 1,.hydeRetriever 1] = [.selection 1,.selection 2,.selection 3,.selection 0] := by decide
    rw [ho] at ha
    simp only [List.mem_cons,List.not_mem_nil,or_false] at ha
    rcases ha with rfl | rfl | rfl | rfl <;> decide
  · intro a ha
    simp only [List.mem_cons,List.not_mem_nil,or_false] at ha
    rcases ha with rfl | rfl
    · exact adverseCompleteS42D2Cmp0
    · exact adverseCompleteS42D2Cmp1
  · intro a ha
    simp only [List.mem_cons,List.not_mem_nil,or_false] at ha
    rcases ha with rfl
    · exact adverseCompleteS42D2Cmp3

theorem adverseCompleteS42ActualEvent : nativeEvent budgetTape (7/5) (controlPenalty savedCref uniformQuoteError unitRoleUnused .complete)
    (taskReward true (2/5) (1/2)) adverseCompleteS42Before = adverseCompleteEvent42 := by
  have hs0 := native_select_existing_step budgetTape (7/5) (controlPenalty savedCref uniformQuoteError unitRoleUnused .complete) adverseCompleteS42Before 8 [] (.query 1)
    (by decide) (by decide) adverseCompleteS42Choice0
  have hs1 := native_select_existing_step budgetTape (7/5) (controlPenalty savedCref uniformQuoteError unitRoleUnused .complete) adverseCompleteS42Before 7 [.query 1] (.hydeRetriever 1)
    (by decide) (by decide) adverseCompleteS42Choice1
  have hs2 := native_select_existing_step budgetTape (7/5) (controlPenalty savedCref uniformQuoteError unitRoleUnused .complete) adverseCompleteS42Before 6 [.query 1,.hydeRetriever 1] (.selection 3)
    (by decide) (by decide) adverseCompleteS42Choice2
  have hnew := native_select_new_step budgetTape (7/5) (controlPenalty savedCref uniformQuoteError unitRoleUnused .complete) adverseCompleteS42Before 5 [.query 1,.hydeRetriever 1,.selection 3]
    [.width 3,.width 1,.width 2] (.width 3) (by decide) (by decide) (by decide) (by decide)
  have hs : nativeSelect budgetTape (7/5) (controlPenalty savedCref uniformQuoteError unitRoleUnused .complete) adverseCompleteS42Before 9 [] = [.query 1,.hydeRetriever 1,.selection 3,.width 3] := by
    rw [hs0]
    change nativeSelect budgetTape (7/5) (controlPenalty savedCref uniformQuoteError unitRoleUnused .complete) adverseCompleteS42Before 8 [.query 1] = _
    rw [hs1]
    change nativeSelect budgetTape (7/5) (controlPenalty savedCref uniformQuoteError unitRoleUnused .complete) adverseCompleteS42Before 7 [.query 1,.hydeRetriever 1] = _
    rw [hs2]
    change nativeSelect budgetTape (7/5) (controlPenalty savedCref uniformQuoteError unitRoleUnused .complete) adverseCompleteS42Before 6 [.query 1,.hydeRetriever 1,.selection 3] = _
    rw [hnew] <;> rfl
  have hr : repairedRollout budgetTape adverseCompleteS42Before 9 [.query 1,.hydeRetriever 1,.selection 3,.width 3] = [.query 1,.hydeRetriever 1,.selection 3,.width 3,.stop,.reranker 0,.topm 0,.context 0,.answer 0] := by decide
  simp only [nativeEvent,hs,hr]
  rfl

def adverseCompleteS43Before := adverseCompleteProposal.take 42

theorem adverseCompleteS43Choice0 : nativeFirstChoice (indexScore (7/5) (controlPenalty savedCref uniformQuoteError unitRoleUnused .complete) adverseCompleteS43Before []) adverseCompleteS43Before [] = .query 1 := by
  apply complete_root_from_physical_gap adverseCompleteS43Before (adverseComplete_prefix_rewards 42) (by decide)
  · intro q; fin_cases q <;> decide
  · exact AgentUCTNextExact.adverse_complete_hyde_root_suffix_empty 42 (by omega)
  · intro q hq
    exact AgentUCTNextExact.adverse_complete_normal_root_physical_quote_exact 42 (by omega) q hq

theorem adverseCompleteS43D1I0 : indexScore (7/5) (controlPenalty savedCref uniformQuoteError unitRoleUnused .complete) adverseCompleteS43Before [.query 1] (.hydeRetriever 1) = treeIndex ((0/1)/12) (7/5) 0 35 12 := by
  have hs : replayBackup adverseCompleteS43Before emptyStatistics ([.query 1]++[.hydeRetriever 1]) = ⟨12,(0/1)⟩ := by
    rw [replayBackup_empty_closed_form]
    simp +decide [backedEvents,adverseCompleteS43Before,adverseCompleteProposal,adverseCompleteEvent1,adverseCompleteEvent2,adverseCompleteEvent3,adverseCompleteEvent4,adverseCompleteEvent5,adverseCompleteEvent6,adverseCompleteEvent7,adverseCompleteEvent8,adverseCompleteEvent9,adverseCompleteEvent10,adverseCompleteEvent11,adverseCompleteEvent12,adverseCompleteEvent13,adverseCompleteEvent14,adverseCompleteEvent15,adverseCompleteEvent16,adverseCompleteEvent17,adverseCompleteEvent18,adverseCompleteEvent19,adverseCompleteEvent20,adverseCompleteEvent21,adverseCompleteEvent22,adverseCompleteEvent23,adverseCompleteEvent24,adverseCompleteEvent25,adverseCompleteEvent26,adverseCompleteEvent27,adverseCompleteEvent28,adverseCompleteEvent29,adverseCompleteEvent30,adverseCompleteEvent31,adverseCompleteEvent32,adverseCompleteEvent33,adverseCompleteEvent34,adverseCompleteEvent35,adverseCompleteEvent36,adverseCompleteEvent37,adverseCompleteEvent38,adverseCompleteEvent39,adverseCompleteEvent40,adverseCompleteEvent41,adverseCompleteEvent42,taskReward]
    <;> norm_num
  have hp : rawVisits adverseCompleteS43Before [.query 1] = 35 := by decide
  have hn : rawVisits adverseCompleteS43Before ([.query 1]++[.hydeRetriever 1]) = 12 := by decide
  have hz : (controlPenalty savedCref uniformQuoteError unitRoleUnused .complete) adverseCompleteS43Before [.query 1] (.hydeRetriever 1) = 0 := by
    apply control_penalty_empty_of_prior_terminal .complete savedCref uniformQuoteError adverseCompleteS43Before [.query 1] (.hydeRetriever 1) 8 (by decide)
    · decide
    · decide
  unfold indexScore
  rw [hs,hp,hn,hz]
  simp only [BackupStat.mean]
  norm_num

theorem adverseCompleteS43D1I1 : indexScore (7/5) (controlPenalty savedCref uniformQuoteError unitRoleUnused .complete) adverseCompleteS43Before [.query 1] (.hydeRetriever 0) = treeIndex ((0/1)/11) (7/5) 0 35 11 := by
  have hs : replayBackup adverseCompleteS43Before emptyStatistics ([.query 1]++[.hydeRetriever 0]) = ⟨11,(0/1)⟩ := by
    rw [replayBackup_empty_closed_form]
    simp +decide [backedEvents,adverseCompleteS43Before,adverseCompleteProposal,adverseCompleteEvent1,adverseCompleteEvent2,adverseCompleteEvent3,adverseCompleteEvent4,adverseCompleteEvent5,adverseCompleteEvent6,adverseCompleteEvent7,adverseCompleteEvent8,adverseCompleteEvent9,adverseCompleteEvent10,adverseCompleteEvent11,adverseCompleteEvent12,adverseCompleteEvent13,adverseCompleteEvent14,adverseCompleteEvent15,adverseCompleteEvent16,adverseCompleteEvent17,adverseCompleteEvent18,adverseCompleteEvent19,adverseCompleteEvent20,adverseCompleteEvent21,adverseCompleteEvent22,adverseCompleteEvent23,adverseCompleteEvent24,adverseCompleteEvent25,adverseCompleteEvent26,adverseCompleteEvent27,adverseCompleteEvent28,adverseCompleteEvent29,adverseCompleteEvent30,adverseCompleteEvent31,adverseCompleteEvent32,adverseCompleteEvent33,adverseCompleteEvent34,adverseCompleteEvent35,adverseCompleteEvent36,adverseCompleteEvent37,adverseCompleteEvent38,adverseCompleteEvent39,adverseCompleteEvent40,adverseCompleteEvent41,adverseCompleteEvent42,taskReward]
    <;> norm_num
  have hp : rawVisits adverseCompleteS43Before [.query 1] = 35 := by decide
  have hn : rawVisits adverseCompleteS43Before ([.query 1]++[.hydeRetriever 0]) = 11 := by decide
  have hz : (controlPenalty savedCref uniformQuoteError unitRoleUnused .complete) adverseCompleteS43Before [.query 1] (.hydeRetriever 0) = 0 := by
    apply control_penalty_empty_of_prior_terminal .complete savedCref uniformQuoteError adverseCompleteS43Before [.query 1] (.hydeRetriever 0) 1 (by decide)
    · decide
    · decide
  unfold indexScore
  rw [hs,hp,hn,hz]
  simp only [BackupStat.mean]
  norm_num

theorem adverseCompleteS43D1I2 : indexScore (7/5) (controlPenalty savedCref uniformQuoteError unitRoleUnused .complete) adverseCompleteS43Before [.query 1] (.hydeRetriever 2) = treeIndex ((0/1)/11) (7/5) 0 35 11 := by
  have hs : replayBackup adverseCompleteS43Before emptyStatistics ([.query 1]++[.hydeRetriever 2]) = ⟨11,(0/1)⟩ := by
    rw [replayBackup_empty_closed_form]
    simp +decide [backedEvents,adverseCompleteS43Before,adverseCompleteProposal,adverseCompleteEvent1,adverseCompleteEvent2,adverseCompleteEvent3,adverseCompleteEvent4,adverseCompleteEvent5,adverseCompleteEvent6,adverseCompleteEvent7,adverseCompleteEvent8,adverseCompleteEvent9,adverseCompleteEvent10,adverseCompleteEvent11,adverseCompleteEvent12,adverseCompleteEvent13,adverseCompleteEvent14,adverseCompleteEvent15,adverseCompleteEvent16,adverseCompleteEvent17,adverseCompleteEvent18,adverseCompleteEvent19,adverseCompleteEvent20,adverseCompleteEvent21,adverseCompleteEvent22,adverseCompleteEvent23,adverseCompleteEvent24,adverseCompleteEvent25,adverseCompleteEvent26,adverseCompleteEvent27,adverseCompleteEvent28,adverseCompleteEvent29,adverseCompleteEvent30,adverseCompleteEvent31,adverseCompleteEvent32,adverseCompleteEvent33,adverseCompleteEvent34,adverseCompleteEvent35,adverseCompleteEvent36,adverseCompleteEvent37,adverseCompleteEvent38,adverseCompleteEvent39,adverseCompleteEvent40,adverseCompleteEvent41,adverseCompleteEvent42,taskReward]
    <;> norm_num
  have hp : rawVisits adverseCompleteS43Before [.query 1] = 35 := by decide
  have hn : rawVisits adverseCompleteS43Before ([.query 1]++[.hydeRetriever 2]) = 11 := by decide
  have hz : (controlPenalty savedCref uniformQuoteError unitRoleUnused .complete) adverseCompleteS43Before [.query 1] (.hydeRetriever 2) = 0 := by
    apply control_penalty_empty_of_prior_terminal .complete savedCref uniformQuoteError adverseCompleteS43Before [.query 1] (.hydeRetriever 2) 10 (by decide)
    · decide
    · decide
  unfold indexScore
  rw [hs,hp,hn,hz]
  simp only [BackupStat.mean]
  norm_num

theorem adverseCompleteS43D1Cmp0 : indexScore (7/5) (controlPenalty savedCref uniformQuoteError unitRoleUnused .complete) adverseCompleteS43Before [.query 1] (.hydeRetriever 1) < indexScore (7/5) (controlPenalty savedCref uniformQuoteError unitRoleUnused .complete) adverseCompleteS43Before [.query 1] (.hydeRetriever 0) := by
  rw [adverseCompleteS43D1I0,adverseCompleteS43D1I1]
  have h := index_strict_order_from_intervals ((0/1)/11) ((0/1)/12) 0 0 (7990731/10000000) (19126359/25000000)
    (treeBonus (7/5) 35 11) (treeBonus (7/5) 35 12)
    (trajectory_bonus_35_11).1 (trajectory_bonus_35_12).2 (by norm_num)
  simpa only [treeIndex,sub_zero] using h

theorem adverseCompleteS43D1Cmp2 : indexScore (7/5) (controlPenalty savedCref uniformQuoteError unitRoleUnused .complete) adverseCompleteS43Before [.query 1] (.hydeRetriever 2) ≤ indexScore (7/5) (controlPenalty savedCref uniformQuoteError unitRoleUnused .complete) adverseCompleteS43Before [.query 1] (.hydeRetriever 0) := by
  rw [adverseCompleteS43D1I2,adverseCompleteS43D1I1]

theorem adverseCompleteS43Choice1 : nativeFirstChoice (indexScore (7/5) (controlPenalty savedCref uniformQuoteError unitRoleUnused .complete) adverseCompleteS43Before [.query 1]) adverseCompleteS43Before [.query 1] = .hydeRetriever 0 := by
  apply visited_choice_from_ordered_certificate _ _ [.query 1] [.hydeRetriever 1] [.hydeRetriever 2] (.hydeRetriever 0) (by decide)
  · intro a ha
    have ho : orderedLegalAvailable [.query 1] = [.hydeRetriever 1,.hydeRetriever 0,.hydeRetriever 2] := by decide
    rw [ho] at ha
    simp only [List.mem_cons,List.not_mem_nil,or_false] at ha
    rcases ha with rfl | rfl | rfl <;> decide
  · intro a ha
    simp only [List.mem_cons,List.not_mem_nil,or_false] at ha
    rcases ha with rfl
    · exact adverseCompleteS43D1Cmp0
  · intro a ha
    simp only [List.mem_cons,List.not_mem_nil,or_false] at ha
    rcases ha with rfl
    · exact adverseCompleteS43D1Cmp2

theorem adverseCompleteS43D2I0 : indexScore (7/5) (controlPenalty savedCref uniformQuoteError unitRoleUnused .complete) adverseCompleteS43Before [.query 1,.hydeRetriever 0] (.selection 1) = treeIndex ((0/1)/3) (7/5) 0 11 3 := by
  have hs : replayBackup adverseCompleteS43Before emptyStatistics ([.query 1,.hydeRetriever 0]++[.selection 1]) = ⟨3,(0/1)⟩ := by
    rw [replayBackup_empty_closed_form]
    simp +decide [backedEvents,adverseCompleteS43Before,adverseCompleteProposal,adverseCompleteEvent1,adverseCompleteEvent2,adverseCompleteEvent3,adverseCompleteEvent4,adverseCompleteEvent5,adverseCompleteEvent6,adverseCompleteEvent7,adverseCompleteEvent8,adverseCompleteEvent9,adverseCompleteEvent10,adverseCompleteEvent11,adverseCompleteEvent12,adverseCompleteEvent13,adverseCompleteEvent14,adverseCompleteEvent15,adverseCompleteEvent16,adverseCompleteEvent17,adverseCompleteEvent18,adverseCompleteEvent19,adverseCompleteEvent20,adverseCompleteEvent21,adverseCompleteEvent22,adverseCompleteEvent23,adverseCompleteEvent24,adverseCompleteEvent25,adverseCompleteEvent26,adverseCompleteEvent27,adverseCompleteEvent28,adverseCompleteEvent29,adverseCompleteEvent30,adverseCompleteEvent31,adverseCompleteEvent32,adverseCompleteEvent33,adverseCompleteEvent34,adverseCompleteEvent35,adverseCompleteEvent36,adverseCompleteEvent37,adverseCompleteEvent38,adverseCompleteEvent39,adverseCompleteEvent40,adverseCompleteEvent41,adverseCompleteEvent42,taskReward]
    <;> norm_num
  have hp : rawVisits adverseCompleteS43Before [.query 1,.hydeRetriever 0] = 11 := by decide
  have hn : rawVisits adverseCompleteS43Before ([.query 1,.hydeRetriever 0]++[.selection 1]) = 3 := by decide
  have hz : (controlPenalty savedCref uniformQuoteError unitRoleUnused .complete) adverseCompleteS43Before [.query 1,.hydeRetriever 0] (.selection 1) = 0 := by
    apply control_penalty_empty_of_prior_terminal .complete savedCref uniformQuoteError adverseCompleteS43Before [.query 1,.hydeRetriever 0] (.selection 1) 15 (by decide)
    · decide
    · decide
  unfold indexScore
  rw [hs,hp,hn,hz]
  simp only [BackupStat.mean]
  norm_num

theorem adverseCompleteS43D2I1 : indexScore (7/5) (controlPenalty savedCref uniformQuoteError unitRoleUnused .complete) adverseCompleteS43Before [.query 1,.hydeRetriever 0] (.selection 2) = treeIndex ((0/1)/3) (7/5) 0 11 3 := by
  have hs : replayBackup adverseCompleteS43Before emptyStatistics ([.query 1,.hydeRetriever 0]++[.selection 2]) = ⟨3,(0/1)⟩ := by
    rw [replayBackup_empty_closed_form]
    simp +decide [backedEvents,adverseCompleteS43Before,adverseCompleteProposal,adverseCompleteEvent1,adverseCompleteEvent2,adverseCompleteEvent3,adverseCompleteEvent4,adverseCompleteEvent5,adverseCompleteEvent6,adverseCompleteEvent7,adverseCompleteEvent8,adverseCompleteEvent9,adverseCompleteEvent10,adverseCompleteEvent11,adverseCompleteEvent12,adverseCompleteEvent13,adverseCompleteEvent14,adverseCompleteEvent15,adverseCompleteEvent16,adverseCompleteEvent17,adverseCompleteEvent18,adverseCompleteEvent19,adverseCompleteEvent20,adverseCompleteEvent21,adverseCompleteEvent22,adverseCompleteEvent23,adverseCompleteEvent24,adverseCompleteEvent25,adverseCompleteEvent26,adverseCompleteEvent27,adverseCompleteEvent28,adverseCompleteEvent29,adverseCompleteEvent30,adverseCompleteEvent31,adverseCompleteEvent32,adverseCompleteEvent33,adverseCompleteEvent34,adverseCompleteEvent35,adverseCompleteEvent36,adverseCompleteEvent37,adverseCompleteEvent38,adverseCompleteEvent39,adverseCompleteEvent40,adverseCompleteEvent41,adverseCompleteEvent42,taskReward]
    <;> norm_num
  have hp : rawVisits adverseCompleteS43Before [.query 1,.hydeRetriever 0] = 11 := by decide
  have hn : rawVisits adverseCompleteS43Before ([.query 1,.hydeRetriever 0]++[.selection 2]) = 3 := by decide
  have hz : (controlPenalty savedCref uniformQuoteError unitRoleUnused .complete) adverseCompleteS43Before [.query 1,.hydeRetriever 0] (.selection 2) = 0 := by
    apply control_penalty_empty_of_prior_terminal .complete savedCref uniformQuoteError adverseCompleteS43Before [.query 1,.hydeRetriever 0] (.selection 2) 18 (by decide)
    · decide
    · decide
  unfold indexScore
  rw [hs,hp,hn,hz]
  simp only [BackupStat.mean]
  norm_num

theorem adverseCompleteS43D2I2 : indexScore (7/5) (controlPenalty savedCref uniformQuoteError unitRoleUnused .complete) adverseCompleteS43Before [.query 1,.hydeRetriever 0] (.selection 3) = treeIndex ((0/1)/2) (7/5) 0 11 2 := by
  have hs : replayBackup adverseCompleteS43Before emptyStatistics ([.query 1,.hydeRetriever 0]++[.selection 3]) = ⟨2,(0/1)⟩ := by
    rw [replayBackup_empty_closed_form]
    simp +decide [backedEvents,adverseCompleteS43Before,adverseCompleteProposal,adverseCompleteEvent1,adverseCompleteEvent2,adverseCompleteEvent3,adverseCompleteEvent4,adverseCompleteEvent5,adverseCompleteEvent6,adverseCompleteEvent7,adverseCompleteEvent8,adverseCompleteEvent9,adverseCompleteEvent10,adverseCompleteEvent11,adverseCompleteEvent12,adverseCompleteEvent13,adverseCompleteEvent14,adverseCompleteEvent15,adverseCompleteEvent16,adverseCompleteEvent17,adverseCompleteEvent18,adverseCompleteEvent19,adverseCompleteEvent20,adverseCompleteEvent21,adverseCompleteEvent22,adverseCompleteEvent23,adverseCompleteEvent24,adverseCompleteEvent25,adverseCompleteEvent26,adverseCompleteEvent27,adverseCompleteEvent28,adverseCompleteEvent29,adverseCompleteEvent30,adverseCompleteEvent31,adverseCompleteEvent32,adverseCompleteEvent33,adverseCompleteEvent34,adverseCompleteEvent35,adverseCompleteEvent36,adverseCompleteEvent37,adverseCompleteEvent38,adverseCompleteEvent39,adverseCompleteEvent40,adverseCompleteEvent41,adverseCompleteEvent42,taskReward]
    <;> norm_num
  have hp : rawVisits adverseCompleteS43Before [.query 1,.hydeRetriever 0] = 11 := by decide
  have hn : rawVisits adverseCompleteS43Before ([.query 1,.hydeRetriever 0]++[.selection 3]) = 2 := by decide
  have hz : (controlPenalty savedCref uniformQuoteError unitRoleUnused .complete) adverseCompleteS43Before [.query 1,.hydeRetriever 0] (.selection 3) = 0 := by
    apply control_penalty_empty_of_prior_terminal .complete savedCref uniformQuoteError adverseCompleteS43Before [.query 1,.hydeRetriever 0] (.selection 3) 21 (by decide)
    · decide
    · decide
  unfold indexScore
  rw [hs,hp,hn,hz]
  simp only [BackupStat.mean]
  norm_num

theorem adverseCompleteS43D2I3 : indexScore (7/5) (controlPenalty savedCref uniformQuoteError unitRoleUnused .complete) adverseCompleteS43Before [.query 1,.hydeRetriever 0] (.selection 0) = treeIndex ((0/1)/2) (7/5) 0 11 2 := by
  have hs : replayBackup adverseCompleteS43Before emptyStatistics ([.query 1,.hydeRetriever 0]++[.selection 0]) = ⟨2,(0/1)⟩ := by
    rw [replayBackup_empty_closed_form]
    simp +decide [backedEvents,adverseCompleteS43Before,adverseCompleteProposal,adverseCompleteEvent1,adverseCompleteEvent2,adverseCompleteEvent3,adverseCompleteEvent4,adverseCompleteEvent5,adverseCompleteEvent6,adverseCompleteEvent7,adverseCompleteEvent8,adverseCompleteEvent9,adverseCompleteEvent10,adverseCompleteEvent11,adverseCompleteEvent12,adverseCompleteEvent13,adverseCompleteEvent14,adverseCompleteEvent15,adverseCompleteEvent16,adverseCompleteEvent17,adverseCompleteEvent18,adverseCompleteEvent19,adverseCompleteEvent20,adverseCompleteEvent21,adverseCompleteEvent22,adverseCompleteEvent23,adverseCompleteEvent24,adverseCompleteEvent25,adverseCompleteEvent26,adverseCompleteEvent27,adverseCompleteEvent28,adverseCompleteEvent29,adverseCompleteEvent30,adverseCompleteEvent31,adverseCompleteEvent32,adverseCompleteEvent33,adverseCompleteEvent34,adverseCompleteEvent35,adverseCompleteEvent36,adverseCompleteEvent37,adverseCompleteEvent38,adverseCompleteEvent39,adverseCompleteEvent40,adverseCompleteEvent41,adverseCompleteEvent42,taskReward]
    <;> norm_num
  have hp : rawVisits adverseCompleteS43Before [.query 1,.hydeRetriever 0] = 11 := by decide
  have hn : rawVisits adverseCompleteS43Before ([.query 1,.hydeRetriever 0]++[.selection 0]) = 2 := by decide
  have hz : (controlPenalty savedCref uniformQuoteError unitRoleUnused .complete) adverseCompleteS43Before [.query 1,.hydeRetriever 0] (.selection 0) = 0 := by
    apply control_penalty_empty_of_prior_terminal .complete savedCref uniformQuoteError adverseCompleteS43Before [.query 1,.hydeRetriever 0] (.selection 0) 1 (by decide)
    · decide
    · decide
  unfold indexScore
  rw [hs,hp,hn,hz]
  simp only [BackupStat.mean]
  norm_num

theorem adverseCompleteS43D2Cmp0 : indexScore (7/5) (controlPenalty savedCref uniformQuoteError unitRoleUnused .complete) adverseCompleteS43Before [.query 1,.hydeRetriever 0] (.selection 1) < indexScore (7/5) (controlPenalty savedCref uniformQuoteError unitRoleUnused .complete) adverseCompleteS43Before [.query 1,.hydeRetriever 0] (.selection 3) := by
  rw [adverseCompleteS43D2I0,adverseCompleteS43D2I2]
  have h := index_strict_order_from_intervals ((0/1)/2) ((0/1)/3) 0 0 (39012883/25000000) (7963473/6250000)
    (treeBonus (7/5) 11 2) (treeBonus (7/5) 11 3)
    (trajectory_bonus_11_2).1 (trajectory_bonus_11_3).2 (by norm_num)
  simpa only [treeIndex,sub_zero] using h

theorem adverseCompleteS43D2Cmp1 : indexScore (7/5) (controlPenalty savedCref uniformQuoteError unitRoleUnused .complete) adverseCompleteS43Before [.query 1,.hydeRetriever 0] (.selection 2) < indexScore (7/5) (controlPenalty savedCref uniformQuoteError unitRoleUnused .complete) adverseCompleteS43Before [.query 1,.hydeRetriever 0] (.selection 3) := by
  rw [adverseCompleteS43D2I1,adverseCompleteS43D2I2]
  have h := index_strict_order_from_intervals ((0/1)/2) ((0/1)/3) 0 0 (39012883/25000000) (7963473/6250000)
    (treeBonus (7/5) 11 2) (treeBonus (7/5) 11 3)
    (trajectory_bonus_11_2).1 (trajectory_bonus_11_3).2 (by norm_num)
  simpa only [treeIndex,sub_zero] using h

theorem adverseCompleteS43D2Cmp3 : indexScore (7/5) (controlPenalty savedCref uniformQuoteError unitRoleUnused .complete) adverseCompleteS43Before [.query 1,.hydeRetriever 0] (.selection 0) ≤ indexScore (7/5) (controlPenalty savedCref uniformQuoteError unitRoleUnused .complete) adverseCompleteS43Before [.query 1,.hydeRetriever 0] (.selection 3) := by
  rw [adverseCompleteS43D2I3,adverseCompleteS43D2I2]

theorem adverseCompleteS43Choice2 : nativeFirstChoice (indexScore (7/5) (controlPenalty savedCref uniformQuoteError unitRoleUnused .complete) adverseCompleteS43Before [.query 1,.hydeRetriever 0]) adverseCompleteS43Before [.query 1,.hydeRetriever 0] = .selection 3 := by
  apply visited_choice_from_ordered_certificate _ _ [.query 1,.hydeRetriever 0] [.selection 1,.selection 2] [.selection 0] (.selection 3) (by decide)
  · intro a ha
    have ho : orderedLegalAvailable [.query 1,.hydeRetriever 0] = [.selection 1,.selection 2,.selection 3,.selection 0] := by decide
    rw [ho] at ha
    simp only [List.mem_cons,List.not_mem_nil,or_false] at ha
    rcases ha with rfl | rfl | rfl | rfl <;> decide
  · intro a ha
    simp only [List.mem_cons,List.not_mem_nil,or_false] at ha
    rcases ha with rfl | rfl
    · exact adverseCompleteS43D2Cmp0
    · exact adverseCompleteS43D2Cmp1
  · intro a ha
    simp only [List.mem_cons,List.not_mem_nil,or_false] at ha
    rcases ha with rfl
    · exact adverseCompleteS43D2Cmp3

theorem adverseCompleteS43ActualEvent : nativeEvent budgetTape (7/5) (controlPenalty savedCref uniformQuoteError unitRoleUnused .complete)
    (taskReward true (2/5) (1/2)) adverseCompleteS43Before = adverseCompleteEvent43 := by
  have hs0 := native_select_existing_step budgetTape (7/5) (controlPenalty savedCref uniformQuoteError unitRoleUnused .complete) adverseCompleteS43Before 8 [] (.query 1)
    (by decide) (by decide) adverseCompleteS43Choice0
  have hs1 := native_select_existing_step budgetTape (7/5) (controlPenalty savedCref uniformQuoteError unitRoleUnused .complete) adverseCompleteS43Before 7 [.query 1] (.hydeRetriever 0)
    (by decide) (by decide) adverseCompleteS43Choice1
  have hs2 := native_select_existing_step budgetTape (7/5) (controlPenalty savedCref uniformQuoteError unitRoleUnused .complete) adverseCompleteS43Before 6 [.query 1,.hydeRetriever 0] (.selection 3)
    (by decide) (by decide) adverseCompleteS43Choice2
  have hnew := native_select_new_step budgetTape (7/5) (controlPenalty savedCref uniformQuoteError unitRoleUnused .complete) adverseCompleteS43Before 5 [.query 1,.hydeRetriever 0,.selection 3]
    [.width 3,.width 1,.width 2] (.width 3) (by decide) (by decide) (by decide) (by decide)
  have hs : nativeSelect budgetTape (7/5) (controlPenalty savedCref uniformQuoteError unitRoleUnused .complete) adverseCompleteS43Before 9 [] = [.query 1,.hydeRetriever 0,.selection 3,.width 3] := by
    rw [hs0]
    change nativeSelect budgetTape (7/5) (controlPenalty savedCref uniformQuoteError unitRoleUnused .complete) adverseCompleteS43Before 8 [.query 1] = _
    rw [hs1]
    change nativeSelect budgetTape (7/5) (controlPenalty savedCref uniformQuoteError unitRoleUnused .complete) adverseCompleteS43Before 7 [.query 1,.hydeRetriever 0] = _
    rw [hs2]
    change nativeSelect budgetTape (7/5) (controlPenalty savedCref uniformQuoteError unitRoleUnused .complete) adverseCompleteS43Before 6 [.query 1,.hydeRetriever 0,.selection 3] = _
    rw [hnew] <;> rfl
  have hr : repairedRollout budgetTape adverseCompleteS43Before 9 [.query 1,.hydeRetriever 0,.selection 3,.width 3] = [.query 1,.hydeRetriever 0,.selection 3,.width 3,.stop,.reranker 0,.topm 0,.context 0,.answer 0] := by decide
  simp only [nativeEvent,hs,hr]
  rfl

def adverseCompleteS44Before := adverseCompleteProposal.take 43

theorem adverseCompleteS44Choice0 : nativeFirstChoice (indexScore (7/5) (controlPenalty savedCref uniformQuoteError unitRoleUnused .complete) adverseCompleteS44Before []) adverseCompleteS44Before [] = .query 1 := by
  apply complete_root_from_physical_gap adverseCompleteS44Before (adverseComplete_prefix_rewards 43) (by decide)
  · intro q; fin_cases q <;> decide
  · exact AgentUCTNextExact.adverse_complete_hyde_root_suffix_empty 43 (by omega)
  · intro q hq
    exact AgentUCTNextExact.adverse_complete_normal_root_physical_quote_exact 43 (by omega) q hq

theorem adverseCompleteS44D1I0 : indexScore (7/5) (controlPenalty savedCref uniformQuoteError unitRoleUnused .complete) adverseCompleteS44Before [.query 1] (.hydeRetriever 1) = treeIndex ((0/1)/12) (7/5) 0 36 12 := by
  have hs : replayBackup adverseCompleteS44Before emptyStatistics ([.query 1]++[.hydeRetriever 1]) = ⟨12,(0/1)⟩ := by
    rw [replayBackup_empty_closed_form]
    simp +decide [backedEvents,adverseCompleteS44Before,adverseCompleteProposal,adverseCompleteEvent1,adverseCompleteEvent2,adverseCompleteEvent3,adverseCompleteEvent4,adverseCompleteEvent5,adverseCompleteEvent6,adverseCompleteEvent7,adverseCompleteEvent8,adverseCompleteEvent9,adverseCompleteEvent10,adverseCompleteEvent11,adverseCompleteEvent12,adverseCompleteEvent13,adverseCompleteEvent14,adverseCompleteEvent15,adverseCompleteEvent16,adverseCompleteEvent17,adverseCompleteEvent18,adverseCompleteEvent19,adverseCompleteEvent20,adverseCompleteEvent21,adverseCompleteEvent22,adverseCompleteEvent23,adverseCompleteEvent24,adverseCompleteEvent25,adverseCompleteEvent26,adverseCompleteEvent27,adverseCompleteEvent28,adverseCompleteEvent29,adverseCompleteEvent30,adverseCompleteEvent31,adverseCompleteEvent32,adverseCompleteEvent33,adverseCompleteEvent34,adverseCompleteEvent35,adverseCompleteEvent36,adverseCompleteEvent37,adverseCompleteEvent38,adverseCompleteEvent39,adverseCompleteEvent40,adverseCompleteEvent41,adverseCompleteEvent42,adverseCompleteEvent43,taskReward]
    <;> norm_num
  have hp : rawVisits adverseCompleteS44Before [.query 1] = 36 := by decide
  have hn : rawVisits adverseCompleteS44Before ([.query 1]++[.hydeRetriever 1]) = 12 := by decide
  have hz : (controlPenalty savedCref uniformQuoteError unitRoleUnused .complete) adverseCompleteS44Before [.query 1] (.hydeRetriever 1) = 0 := by
    apply control_penalty_empty_of_prior_terminal .complete savedCref uniformQuoteError adverseCompleteS44Before [.query 1] (.hydeRetriever 1) 8 (by decide)
    · decide
    · decide
  unfold indexScore
  rw [hs,hp,hn,hz]
  simp only [BackupStat.mean]
  norm_num

theorem adverseCompleteS44D1I1 : indexScore (7/5) (controlPenalty savedCref uniformQuoteError unitRoleUnused .complete) adverseCompleteS44Before [.query 1] (.hydeRetriever 0) = treeIndex ((0/1)/12) (7/5) 0 36 12 := by
  have hs : replayBackup adverseCompleteS44Before emptyStatistics ([.query 1]++[.hydeRetriever 0]) = ⟨12,(0/1)⟩ := by
    rw [replayBackup_empty_closed_form]
    simp +decide [backedEvents,adverseCompleteS44Before,adverseCompleteProposal,adverseCompleteEvent1,adverseCompleteEvent2,adverseCompleteEvent3,adverseCompleteEvent4,adverseCompleteEvent5,adverseCompleteEvent6,adverseCompleteEvent7,adverseCompleteEvent8,adverseCompleteEvent9,adverseCompleteEvent10,adverseCompleteEvent11,adverseCompleteEvent12,adverseCompleteEvent13,adverseCompleteEvent14,adverseCompleteEvent15,adverseCompleteEvent16,adverseCompleteEvent17,adverseCompleteEvent18,adverseCompleteEvent19,adverseCompleteEvent20,adverseCompleteEvent21,adverseCompleteEvent22,adverseCompleteEvent23,adverseCompleteEvent24,adverseCompleteEvent25,adverseCompleteEvent26,adverseCompleteEvent27,adverseCompleteEvent28,adverseCompleteEvent29,adverseCompleteEvent30,adverseCompleteEvent31,adverseCompleteEvent32,adverseCompleteEvent33,adverseCompleteEvent34,adverseCompleteEvent35,adverseCompleteEvent36,adverseCompleteEvent37,adverseCompleteEvent38,adverseCompleteEvent39,adverseCompleteEvent40,adverseCompleteEvent41,adverseCompleteEvent42,adverseCompleteEvent43,taskReward]
    <;> norm_num
  have hp : rawVisits adverseCompleteS44Before [.query 1] = 36 := by decide
  have hn : rawVisits adverseCompleteS44Before ([.query 1]++[.hydeRetriever 0]) = 12 := by decide
  have hz : (controlPenalty savedCref uniformQuoteError unitRoleUnused .complete) adverseCompleteS44Before [.query 1] (.hydeRetriever 0) = 0 := by
    apply control_penalty_empty_of_prior_terminal .complete savedCref uniformQuoteError adverseCompleteS44Before [.query 1] (.hydeRetriever 0) 1 (by decide)
    · decide
    · decide
  unfold indexScore
  rw [hs,hp,hn,hz]
  simp only [BackupStat.mean]
  norm_num

theorem adverseCompleteS44D1I2 : indexScore (7/5) (controlPenalty savedCref uniformQuoteError unitRoleUnused .complete) adverseCompleteS44Before [.query 1] (.hydeRetriever 2) = treeIndex ((0/1)/11) (7/5) 0 36 11 := by
  have hs : replayBackup adverseCompleteS44Before emptyStatistics ([.query 1]++[.hydeRetriever 2]) = ⟨11,(0/1)⟩ := by
    rw [replayBackup_empty_closed_form]
    simp +decide [backedEvents,adverseCompleteS44Before,adverseCompleteProposal,adverseCompleteEvent1,adverseCompleteEvent2,adverseCompleteEvent3,adverseCompleteEvent4,adverseCompleteEvent5,adverseCompleteEvent6,adverseCompleteEvent7,adverseCompleteEvent8,adverseCompleteEvent9,adverseCompleteEvent10,adverseCompleteEvent11,adverseCompleteEvent12,adverseCompleteEvent13,adverseCompleteEvent14,adverseCompleteEvent15,adverseCompleteEvent16,adverseCompleteEvent17,adverseCompleteEvent18,adverseCompleteEvent19,adverseCompleteEvent20,adverseCompleteEvent21,adverseCompleteEvent22,adverseCompleteEvent23,adverseCompleteEvent24,adverseCompleteEvent25,adverseCompleteEvent26,adverseCompleteEvent27,adverseCompleteEvent28,adverseCompleteEvent29,adverseCompleteEvent30,adverseCompleteEvent31,adverseCompleteEvent32,adverseCompleteEvent33,adverseCompleteEvent34,adverseCompleteEvent35,adverseCompleteEvent36,adverseCompleteEvent37,adverseCompleteEvent38,adverseCompleteEvent39,adverseCompleteEvent40,adverseCompleteEvent41,adverseCompleteEvent42,adverseCompleteEvent43,taskReward]
    <;> norm_num
  have hp : rawVisits adverseCompleteS44Before [.query 1] = 36 := by decide
  have hn : rawVisits adverseCompleteS44Before ([.query 1]++[.hydeRetriever 2]) = 11 := by decide
  have hz : (controlPenalty savedCref uniformQuoteError unitRoleUnused .complete) adverseCompleteS44Before [.query 1] (.hydeRetriever 2) = 0 := by
    apply control_penalty_empty_of_prior_terminal .complete savedCref uniformQuoteError adverseCompleteS44Before [.query 1] (.hydeRetriever 2) 10 (by decide)
    · decide
    · decide
  unfold indexScore
  rw [hs,hp,hn,hz]
  simp only [BackupStat.mean]
  norm_num

theorem adverseCompleteS44D1Cmp0 : indexScore (7/5) (controlPenalty savedCref uniformQuoteError unitRoleUnused .complete) adverseCompleteS44Before [.query 1] (.hydeRetriever 1) < indexScore (7/5) (controlPenalty savedCref uniformQuoteError unitRoleUnused .complete) adverseCompleteS44Before [.query 1] (.hydeRetriever 2) := by
  rw [adverseCompleteS44D1I0,adverseCompleteS44D1I2]
  have h := index_strict_order_from_intervals ((0/1)/11) ((0/1)/12) 0 0 (40106101/50000000) (1535947/2000000)
    (treeBonus (7/5) 36 11) (treeBonus (7/5) 36 12)
    (trajectory_bonus_36_11).1 (trajectory_bonus_36_12).2 (by norm_num)
  simpa only [treeIndex,sub_zero] using h

theorem adverseCompleteS44D1Cmp1 : indexScore (7/5) (controlPenalty savedCref uniformQuoteError unitRoleUnused .complete) adverseCompleteS44Before [.query 1] (.hydeRetriever 0) < indexScore (7/5) (controlPenalty savedCref uniformQuoteError unitRoleUnused .complete) adverseCompleteS44Before [.query 1] (.hydeRetriever 2) := by
  rw [adverseCompleteS44D1I1,adverseCompleteS44D1I2]
  have h := index_strict_order_from_intervals ((0/1)/11) ((0/1)/12) 0 0 (40106101/50000000) (1535947/2000000)
    (treeBonus (7/5) 36 11) (treeBonus (7/5) 36 12)
    (trajectory_bonus_36_11).1 (trajectory_bonus_36_12).2 (by norm_num)
  simpa only [treeIndex,sub_zero] using h

theorem adverseCompleteS44Choice1 : nativeFirstChoice (indexScore (7/5) (controlPenalty savedCref uniformQuoteError unitRoleUnused .complete) adverseCompleteS44Before [.query 1]) adverseCompleteS44Before [.query 1] = .hydeRetriever 2 := by
  apply visited_choice_from_ordered_certificate _ _ [.query 1] [.hydeRetriever 1,.hydeRetriever 0] [] (.hydeRetriever 2) (by decide)
  · intro a ha
    have ho : orderedLegalAvailable [.query 1] = [.hydeRetriever 1,.hydeRetriever 0,.hydeRetriever 2] := by decide
    rw [ho] at ha
    simp only [List.mem_cons,List.not_mem_nil,or_false] at ha
    rcases ha with rfl | rfl | rfl <;> decide
  · intro a ha
    simp only [List.mem_cons,List.not_mem_nil,or_false] at ha
    rcases ha with rfl | rfl
    · exact adverseCompleteS44D1Cmp0
    · exact adverseCompleteS44D1Cmp1
  · simp

theorem adverseCompleteS44D2I0 : indexScore (7/5) (controlPenalty savedCref uniformQuoteError unitRoleUnused .complete) adverseCompleteS44Before [.query 1,.hydeRetriever 2] (.selection 1) = treeIndex ((0/1)/3) (7/5) 0 11 3 := by
  have hs : replayBackup adverseCompleteS44Before emptyStatistics ([.query 1,.hydeRetriever 2]++[.selection 1]) = ⟨3,(0/1)⟩ := by
    rw [replayBackup_empty_closed_form]
    simp +decide [backedEvents,adverseCompleteS44Before,adverseCompleteProposal,adverseCompleteEvent1,adverseCompleteEvent2,adverseCompleteEvent3,adverseCompleteEvent4,adverseCompleteEvent5,adverseCompleteEvent6,adverseCompleteEvent7,adverseCompleteEvent8,adverseCompleteEvent9,adverseCompleteEvent10,adverseCompleteEvent11,adverseCompleteEvent12,adverseCompleteEvent13,adverseCompleteEvent14,adverseCompleteEvent15,adverseCompleteEvent16,adverseCompleteEvent17,adverseCompleteEvent18,adverseCompleteEvent19,adverseCompleteEvent20,adverseCompleteEvent21,adverseCompleteEvent22,adverseCompleteEvent23,adverseCompleteEvent24,adverseCompleteEvent25,adverseCompleteEvent26,adverseCompleteEvent27,adverseCompleteEvent28,adverseCompleteEvent29,adverseCompleteEvent30,adverseCompleteEvent31,adverseCompleteEvent32,adverseCompleteEvent33,adverseCompleteEvent34,adverseCompleteEvent35,adverseCompleteEvent36,adverseCompleteEvent37,adverseCompleteEvent38,adverseCompleteEvent39,adverseCompleteEvent40,adverseCompleteEvent41,adverseCompleteEvent42,adverseCompleteEvent43,taskReward]
    <;> norm_num
  have hp : rawVisits adverseCompleteS44Before [.query 1,.hydeRetriever 2] = 11 := by decide
  have hn : rawVisits adverseCompleteS44Before ([.query 1,.hydeRetriever 2]++[.selection 1]) = 3 := by decide
  have hz : (controlPenalty savedCref uniformQuoteError unitRoleUnused .complete) adverseCompleteS44Before [.query 1,.hydeRetriever 2] (.selection 1) = 0 := by
    apply control_penalty_empty_of_prior_terminal .complete savedCref uniformQuoteError adverseCompleteS44Before [.query 1,.hydeRetriever 2] (.selection 1) 16 (by decide)
    · decide
    · decide
  unfold indexScore
  rw [hs,hp,hn,hz]
  simp only [BackupStat.mean]
  norm_num

theorem adverseCompleteS44D2I1 : indexScore (7/5) (controlPenalty savedCref uniformQuoteError unitRoleUnused .complete) adverseCompleteS44Before [.query 1,.hydeRetriever 2] (.selection 2) = treeIndex ((0/1)/3) (7/5) 0 11 3 := by
  have hs : replayBackup adverseCompleteS44Before emptyStatistics ([.query 1,.hydeRetriever 2]++[.selection 2]) = ⟨3,(0/1)⟩ := by
    rw [replayBackup_empty_closed_form]
    simp +decide [backedEvents,adverseCompleteS44Before,adverseCompleteProposal,adverseCompleteEvent1,adverseCompleteEvent2,adverseCompleteEvent3,adverseCompleteEvent4,adverseCompleteEvent5,adverseCompleteEvent6,adverseCompleteEvent7,adverseCompleteEvent8,adverseCompleteEvent9,adverseCompleteEvent10,adverseCompleteEvent11,adverseCompleteEvent12,adverseCompleteEvent13,adverseCompleteEvent14,adverseCompleteEvent15,adverseCompleteEvent16,adverseCompleteEvent17,adverseCompleteEvent18,adverseCompleteEvent19,adverseCompleteEvent20,adverseCompleteEvent21,adverseCompleteEvent22,adverseCompleteEvent23,adverseCompleteEvent24,adverseCompleteEvent25,adverseCompleteEvent26,adverseCompleteEvent27,adverseCompleteEvent28,adverseCompleteEvent29,adverseCompleteEvent30,adverseCompleteEvent31,adverseCompleteEvent32,adverseCompleteEvent33,adverseCompleteEvent34,adverseCompleteEvent35,adverseCompleteEvent36,adverseCompleteEvent37,adverseCompleteEvent38,adverseCompleteEvent39,adverseCompleteEvent40,adverseCompleteEvent41,adverseCompleteEvent42,adverseCompleteEvent43,taskReward]
    <;> norm_num
  have hp : rawVisits adverseCompleteS44Before [.query 1,.hydeRetriever 2] = 11 := by decide
  have hn : rawVisits adverseCompleteS44Before ([.query 1,.hydeRetriever 2]++[.selection 2]) = 3 := by decide
  have hz : (controlPenalty savedCref uniformQuoteError unitRoleUnused .complete) adverseCompleteS44Before [.query 1,.hydeRetriever 2] (.selection 2) = 0 := by
    apply control_penalty_empty_of_prior_terminal .complete savedCref uniformQuoteError adverseCompleteS44Before [.query 1,.hydeRetriever 2] (.selection 2) 19 (by decide)
    · decide
    · decide
  unfold indexScore
  rw [hs,hp,hn,hz]
  simp only [BackupStat.mean]
  norm_num

theorem adverseCompleteS44D2I2 : indexScore (7/5) (controlPenalty savedCref uniformQuoteError unitRoleUnused .complete) adverseCompleteS44Before [.query 1,.hydeRetriever 2] (.selection 3) = treeIndex ((0/1)/2) (7/5) 0 11 2 := by
  have hs : replayBackup adverseCompleteS44Before emptyStatistics ([.query 1,.hydeRetriever 2]++[.selection 3]) = ⟨2,(0/1)⟩ := by
    rw [replayBackup_empty_closed_form]
    simp +decide [backedEvents,adverseCompleteS44Before,adverseCompleteProposal,adverseCompleteEvent1,adverseCompleteEvent2,adverseCompleteEvent3,adverseCompleteEvent4,adverseCompleteEvent5,adverseCompleteEvent6,adverseCompleteEvent7,adverseCompleteEvent8,adverseCompleteEvent9,adverseCompleteEvent10,adverseCompleteEvent11,adverseCompleteEvent12,adverseCompleteEvent13,adverseCompleteEvent14,adverseCompleteEvent15,adverseCompleteEvent16,adverseCompleteEvent17,adverseCompleteEvent18,adverseCompleteEvent19,adverseCompleteEvent20,adverseCompleteEvent21,adverseCompleteEvent22,adverseCompleteEvent23,adverseCompleteEvent24,adverseCompleteEvent25,adverseCompleteEvent26,adverseCompleteEvent27,adverseCompleteEvent28,adverseCompleteEvent29,adverseCompleteEvent30,adverseCompleteEvent31,adverseCompleteEvent32,adverseCompleteEvent33,adverseCompleteEvent34,adverseCompleteEvent35,adverseCompleteEvent36,adverseCompleteEvent37,adverseCompleteEvent38,adverseCompleteEvent39,adverseCompleteEvent40,adverseCompleteEvent41,adverseCompleteEvent42,adverseCompleteEvent43,taskReward]
    <;> norm_num
  have hp : rawVisits adverseCompleteS44Before [.query 1,.hydeRetriever 2] = 11 := by decide
  have hn : rawVisits adverseCompleteS44Before ([.query 1,.hydeRetriever 2]++[.selection 3]) = 2 := by decide
  have hz : (controlPenalty savedCref uniformQuoteError unitRoleUnused .complete) adverseCompleteS44Before [.query 1,.hydeRetriever 2] (.selection 3) = 0 := by
    apply control_penalty_empty_of_prior_terminal .complete savedCref uniformQuoteError adverseCompleteS44Before [.query 1,.hydeRetriever 2] (.selection 3) 22 (by decide)
    · decide
    · decide
  unfold indexScore
  rw [hs,hp,hn,hz]
  simp only [BackupStat.mean]
  norm_num

theorem adverseCompleteS44D2I3 : indexScore (7/5) (controlPenalty savedCref uniformQuoteError unitRoleUnused .complete) adverseCompleteS44Before [.query 1,.hydeRetriever 2] (.selection 0) = treeIndex ((0/1)/2) (7/5) 0 11 2 := by
  have hs : replayBackup adverseCompleteS44Before emptyStatistics ([.query 1,.hydeRetriever 2]++[.selection 0]) = ⟨2,(0/1)⟩ := by
    rw [replayBackup_empty_closed_form]
    simp +decide [backedEvents,adverseCompleteS44Before,adverseCompleteProposal,adverseCompleteEvent1,adverseCompleteEvent2,adverseCompleteEvent3,adverseCompleteEvent4,adverseCompleteEvent5,adverseCompleteEvent6,adverseCompleteEvent7,adverseCompleteEvent8,adverseCompleteEvent9,adverseCompleteEvent10,adverseCompleteEvent11,adverseCompleteEvent12,adverseCompleteEvent13,adverseCompleteEvent14,adverseCompleteEvent15,adverseCompleteEvent16,adverseCompleteEvent17,adverseCompleteEvent18,adverseCompleteEvent19,adverseCompleteEvent20,adverseCompleteEvent21,adverseCompleteEvent22,adverseCompleteEvent23,adverseCompleteEvent24,adverseCompleteEvent25,adverseCompleteEvent26,adverseCompleteEvent27,adverseCompleteEvent28,adverseCompleteEvent29,adverseCompleteEvent30,adverseCompleteEvent31,adverseCompleteEvent32,adverseCompleteEvent33,adverseCompleteEvent34,adverseCompleteEvent35,adverseCompleteEvent36,adverseCompleteEvent37,adverseCompleteEvent38,adverseCompleteEvent39,adverseCompleteEvent40,adverseCompleteEvent41,adverseCompleteEvent42,adverseCompleteEvent43,taskReward]
    <;> norm_num
  have hp : rawVisits adverseCompleteS44Before [.query 1,.hydeRetriever 2] = 11 := by decide
  have hn : rawVisits adverseCompleteS44Before ([.query 1,.hydeRetriever 2]++[.selection 0]) = 2 := by decide
  have hz : (controlPenalty savedCref uniformQuoteError unitRoleUnused .complete) adverseCompleteS44Before [.query 1,.hydeRetriever 2] (.selection 0) = 0 := by
    apply control_penalty_empty_of_prior_terminal .complete savedCref uniformQuoteError adverseCompleteS44Before [.query 1,.hydeRetriever 2] (.selection 0) 10 (by decide)
    · decide
    · decide
  unfold indexScore
  rw [hs,hp,hn,hz]
  simp only [BackupStat.mean]
  norm_num

theorem adverseCompleteS44D2Cmp0 : indexScore (7/5) (controlPenalty savedCref uniformQuoteError unitRoleUnused .complete) adverseCompleteS44Before [.query 1,.hydeRetriever 2] (.selection 1) < indexScore (7/5) (controlPenalty savedCref uniformQuoteError unitRoleUnused .complete) adverseCompleteS44Before [.query 1,.hydeRetriever 2] (.selection 3) := by
  rw [adverseCompleteS44D2I0,adverseCompleteS44D2I2]
  have h := index_strict_order_from_intervals ((0/1)/2) ((0/1)/3) 0 0 (39012883/25000000) (7963473/6250000)
    (treeBonus (7/5) 11 2) (treeBonus (7/5) 11 3)
    (trajectory_bonus_11_2).1 (trajectory_bonus_11_3).2 (by norm_num)
  simpa only [treeIndex,sub_zero] using h

theorem adverseCompleteS44D2Cmp1 : indexScore (7/5) (controlPenalty savedCref uniformQuoteError unitRoleUnused .complete) adverseCompleteS44Before [.query 1,.hydeRetriever 2] (.selection 2) < indexScore (7/5) (controlPenalty savedCref uniformQuoteError unitRoleUnused .complete) adverseCompleteS44Before [.query 1,.hydeRetriever 2] (.selection 3) := by
  rw [adverseCompleteS44D2I1,adverseCompleteS44D2I2]
  have h := index_strict_order_from_intervals ((0/1)/2) ((0/1)/3) 0 0 (39012883/25000000) (7963473/6250000)
    (treeBonus (7/5) 11 2) (treeBonus (7/5) 11 3)
    (trajectory_bonus_11_2).1 (trajectory_bonus_11_3).2 (by norm_num)
  simpa only [treeIndex,sub_zero] using h

theorem adverseCompleteS44D2Cmp3 : indexScore (7/5) (controlPenalty savedCref uniformQuoteError unitRoleUnused .complete) adverseCompleteS44Before [.query 1,.hydeRetriever 2] (.selection 0) ≤ indexScore (7/5) (controlPenalty savedCref uniformQuoteError unitRoleUnused .complete) adverseCompleteS44Before [.query 1,.hydeRetriever 2] (.selection 3) := by
  rw [adverseCompleteS44D2I3,adverseCompleteS44D2I2]

theorem adverseCompleteS44Choice2 : nativeFirstChoice (indexScore (7/5) (controlPenalty savedCref uniformQuoteError unitRoleUnused .complete) adverseCompleteS44Before [.query 1,.hydeRetriever 2]) adverseCompleteS44Before [.query 1,.hydeRetriever 2] = .selection 3 := by
  apply visited_choice_from_ordered_certificate _ _ [.query 1,.hydeRetriever 2] [.selection 1,.selection 2] [.selection 0] (.selection 3) (by decide)
  · intro a ha
    have ho : orderedLegalAvailable [.query 1,.hydeRetriever 2] = [.selection 1,.selection 2,.selection 3,.selection 0] := by decide
    rw [ho] at ha
    simp only [List.mem_cons,List.not_mem_nil,or_false] at ha
    rcases ha with rfl | rfl | rfl | rfl <;> decide
  · intro a ha
    simp only [List.mem_cons,List.not_mem_nil,or_false] at ha
    rcases ha with rfl | rfl
    · exact adverseCompleteS44D2Cmp0
    · exact adverseCompleteS44D2Cmp1
  · intro a ha
    simp only [List.mem_cons,List.not_mem_nil,or_false] at ha
    rcases ha with rfl
    · exact adverseCompleteS44D2Cmp3

theorem adverseCompleteS44ActualEvent : nativeEvent budgetTape (7/5) (controlPenalty savedCref uniformQuoteError unitRoleUnused .complete)
    (taskReward true (2/5) (1/2)) adverseCompleteS44Before = adverseCompleteEvent44 := by
  have hs0 := native_select_existing_step budgetTape (7/5) (controlPenalty savedCref uniformQuoteError unitRoleUnused .complete) adverseCompleteS44Before 8 [] (.query 1)
    (by decide) (by decide) adverseCompleteS44Choice0
  have hs1 := native_select_existing_step budgetTape (7/5) (controlPenalty savedCref uniformQuoteError unitRoleUnused .complete) adverseCompleteS44Before 7 [.query 1] (.hydeRetriever 2)
    (by decide) (by decide) adverseCompleteS44Choice1
  have hs2 := native_select_existing_step budgetTape (7/5) (controlPenalty savedCref uniformQuoteError unitRoleUnused .complete) adverseCompleteS44Before 6 [.query 1,.hydeRetriever 2] (.selection 3)
    (by decide) (by decide) adverseCompleteS44Choice2
  have hnew := native_select_new_step budgetTape (7/5) (controlPenalty savedCref uniformQuoteError unitRoleUnused .complete) adverseCompleteS44Before 5 [.query 1,.hydeRetriever 2,.selection 3]
    [.width 3,.width 1,.width 2] (.width 3) (by decide) (by decide) (by decide) (by decide)
  have hs : nativeSelect budgetTape (7/5) (controlPenalty savedCref uniformQuoteError unitRoleUnused .complete) adverseCompleteS44Before 9 [] = [.query 1,.hydeRetriever 2,.selection 3,.width 3] := by
    rw [hs0]
    change nativeSelect budgetTape (7/5) (controlPenalty savedCref uniformQuoteError unitRoleUnused .complete) adverseCompleteS44Before 8 [.query 1] = _
    rw [hs1]
    change nativeSelect budgetTape (7/5) (controlPenalty savedCref uniformQuoteError unitRoleUnused .complete) adverseCompleteS44Before 7 [.query 1,.hydeRetriever 2] = _
    rw [hs2]
    change nativeSelect budgetTape (7/5) (controlPenalty savedCref uniformQuoteError unitRoleUnused .complete) adverseCompleteS44Before 6 [.query 1,.hydeRetriever 2,.selection 3] = _
    rw [hnew] <;> rfl
  have hr : repairedRollout budgetTape adverseCompleteS44Before 9 [.query 1,.hydeRetriever 2,.selection 3,.width 3] = [.query 1,.hydeRetriever 2,.selection 3,.width 3,.stop,.reranker 0,.topm 0,.context 0,.answer 0] := by decide
  simp only [nativeEvent,hs,hr]
  rfl

def adverseCompleteS45Before := adverseCompleteProposal.take 44

theorem adverseCompleteS45Choice0 : nativeFirstChoice (indexScore (7/5) (controlPenalty savedCref uniformQuoteError unitRoleUnused .complete) adverseCompleteS45Before []) adverseCompleteS45Before [] = .query 1 := by
  apply complete_root_from_physical_gap adverseCompleteS45Before (adverseComplete_prefix_rewards 44) (by decide)
  · intro q; fin_cases q <;> decide
  · exact AgentUCTNextExact.adverse_complete_hyde_root_suffix_empty 44 (by omega)
  · intro q hq
    exact AgentUCTNextExact.adverse_complete_normal_root_physical_quote_exact 44 (by omega) q hq

theorem adverseCompleteS45D1I0 : indexScore (7/5) (controlPenalty savedCref uniformQuoteError unitRoleUnused .complete) adverseCompleteS45Before [.query 1] (.hydeRetriever 1) = treeIndex ((0/1)/12) (7/5) 0 37 12 := by
  have hs : replayBackup adverseCompleteS45Before emptyStatistics ([.query 1]++[.hydeRetriever 1]) = ⟨12,(0/1)⟩ := by
    rw [replayBackup_empty_closed_form]
    simp +decide [backedEvents,adverseCompleteS45Before,adverseCompleteProposal,adverseCompleteEvent1,adverseCompleteEvent2,adverseCompleteEvent3,adverseCompleteEvent4,adverseCompleteEvent5,adverseCompleteEvent6,adverseCompleteEvent7,adverseCompleteEvent8,adverseCompleteEvent9,adverseCompleteEvent10,adverseCompleteEvent11,adverseCompleteEvent12,adverseCompleteEvent13,adverseCompleteEvent14,adverseCompleteEvent15,adverseCompleteEvent16,adverseCompleteEvent17,adverseCompleteEvent18,adverseCompleteEvent19,adverseCompleteEvent20,adverseCompleteEvent21,adverseCompleteEvent22,adverseCompleteEvent23,adverseCompleteEvent24,adverseCompleteEvent25,adverseCompleteEvent26,adverseCompleteEvent27,adverseCompleteEvent28,adverseCompleteEvent29,adverseCompleteEvent30,adverseCompleteEvent31,adverseCompleteEvent32,adverseCompleteEvent33,adverseCompleteEvent34,adverseCompleteEvent35,adverseCompleteEvent36,adverseCompleteEvent37,adverseCompleteEvent38,adverseCompleteEvent39,adverseCompleteEvent40,adverseCompleteEvent41,adverseCompleteEvent42,adverseCompleteEvent43,adverseCompleteEvent44,taskReward]
    <;> norm_num
  have hp : rawVisits adverseCompleteS45Before [.query 1] = 37 := by decide
  have hn : rawVisits adverseCompleteS45Before ([.query 1]++[.hydeRetriever 1]) = 12 := by decide
  have hz : (controlPenalty savedCref uniformQuoteError unitRoleUnused .complete) adverseCompleteS45Before [.query 1] (.hydeRetriever 1) = 0 := by
    apply control_penalty_empty_of_prior_terminal .complete savedCref uniformQuoteError adverseCompleteS45Before [.query 1] (.hydeRetriever 1) 8 (by decide)
    · decide
    · decide
  unfold indexScore
  rw [hs,hp,hn,hz]
  simp only [BackupStat.mean]
  norm_num

theorem adverseCompleteS45D1I1 : indexScore (7/5) (controlPenalty savedCref uniformQuoteError unitRoleUnused .complete) adverseCompleteS45Before [.query 1] (.hydeRetriever 0) = treeIndex ((0/1)/12) (7/5) 0 37 12 := by
  have hs : replayBackup adverseCompleteS45Before emptyStatistics ([.query 1]++[.hydeRetriever 0]) = ⟨12,(0/1)⟩ := by
    rw [replayBackup_empty_closed_form]
    simp +decide [backedEvents,adverseCompleteS45Before,adverseCompleteProposal,adverseCompleteEvent1,adverseCompleteEvent2,adverseCompleteEvent3,adverseCompleteEvent4,adverseCompleteEvent5,adverseCompleteEvent6,adverseCompleteEvent7,adverseCompleteEvent8,adverseCompleteEvent9,adverseCompleteEvent10,adverseCompleteEvent11,adverseCompleteEvent12,adverseCompleteEvent13,adverseCompleteEvent14,adverseCompleteEvent15,adverseCompleteEvent16,adverseCompleteEvent17,adverseCompleteEvent18,adverseCompleteEvent19,adverseCompleteEvent20,adverseCompleteEvent21,adverseCompleteEvent22,adverseCompleteEvent23,adverseCompleteEvent24,adverseCompleteEvent25,adverseCompleteEvent26,adverseCompleteEvent27,adverseCompleteEvent28,adverseCompleteEvent29,adverseCompleteEvent30,adverseCompleteEvent31,adverseCompleteEvent32,adverseCompleteEvent33,adverseCompleteEvent34,adverseCompleteEvent35,adverseCompleteEvent36,adverseCompleteEvent37,adverseCompleteEvent38,adverseCompleteEvent39,adverseCompleteEvent40,adverseCompleteEvent41,adverseCompleteEvent42,adverseCompleteEvent43,adverseCompleteEvent44,taskReward]
    <;> norm_num
  have hp : rawVisits adverseCompleteS45Before [.query 1] = 37 := by decide
  have hn : rawVisits adverseCompleteS45Before ([.query 1]++[.hydeRetriever 0]) = 12 := by decide
  have hz : (controlPenalty savedCref uniformQuoteError unitRoleUnused .complete) adverseCompleteS45Before [.query 1] (.hydeRetriever 0) = 0 := by
    apply control_penalty_empty_of_prior_terminal .complete savedCref uniformQuoteError adverseCompleteS45Before [.query 1] (.hydeRetriever 0) 1 (by decide)
    · decide
    · decide
  unfold indexScore
  rw [hs,hp,hn,hz]
  simp only [BackupStat.mean]
  norm_num

theorem adverseCompleteS45D1I2 : indexScore (7/5) (controlPenalty savedCref uniformQuoteError unitRoleUnused .complete) adverseCompleteS45Before [.query 1] (.hydeRetriever 2) = treeIndex ((0/1)/12) (7/5) 0 37 12 := by
  have hs : replayBackup adverseCompleteS45Before emptyStatistics ([.query 1]++[.hydeRetriever 2]) = ⟨12,(0/1)⟩ := by
    rw [replayBackup_empty_closed_form]
    simp +decide [backedEvents,adverseCompleteS45Before,adverseCompleteProposal,adverseCompleteEvent1,adverseCompleteEvent2,adverseCompleteEvent3,adverseCompleteEvent4,adverseCompleteEvent5,adverseCompleteEvent6,adverseCompleteEvent7,adverseCompleteEvent8,adverseCompleteEvent9,adverseCompleteEvent10,adverseCompleteEvent11,adverseCompleteEvent12,adverseCompleteEvent13,adverseCompleteEvent14,adverseCompleteEvent15,adverseCompleteEvent16,adverseCompleteEvent17,adverseCompleteEvent18,adverseCompleteEvent19,adverseCompleteEvent20,adverseCompleteEvent21,adverseCompleteEvent22,adverseCompleteEvent23,adverseCompleteEvent24,adverseCompleteEvent25,adverseCompleteEvent26,adverseCompleteEvent27,adverseCompleteEvent28,adverseCompleteEvent29,adverseCompleteEvent30,adverseCompleteEvent31,adverseCompleteEvent32,adverseCompleteEvent33,adverseCompleteEvent34,adverseCompleteEvent35,adverseCompleteEvent36,adverseCompleteEvent37,adverseCompleteEvent38,adverseCompleteEvent39,adverseCompleteEvent40,adverseCompleteEvent41,adverseCompleteEvent42,adverseCompleteEvent43,adverseCompleteEvent44,taskReward]
    <;> norm_num
  have hp : rawVisits adverseCompleteS45Before [.query 1] = 37 := by decide
  have hn : rawVisits adverseCompleteS45Before ([.query 1]++[.hydeRetriever 2]) = 12 := by decide
  have hz : (controlPenalty savedCref uniformQuoteError unitRoleUnused .complete) adverseCompleteS45Before [.query 1] (.hydeRetriever 2) = 0 := by
    apply control_penalty_empty_of_prior_terminal .complete savedCref uniformQuoteError adverseCompleteS45Before [.query 1] (.hydeRetriever 2) 10 (by decide)
    · decide
    · decide
  unfold indexScore
  rw [hs,hp,hn,hz]
  simp only [BackupStat.mean]
  norm_num

theorem adverseCompleteS45D1Cmp1 : indexScore (7/5) (controlPenalty savedCref uniformQuoteError unitRoleUnused .complete) adverseCompleteS45Before [.query 1] (.hydeRetriever 0) ≤ indexScore (7/5) (controlPenalty savedCref uniformQuoteError unitRoleUnused .complete) adverseCompleteS45Before [.query 1] (.hydeRetriever 1) := by
  rw [adverseCompleteS45D1I1,adverseCompleteS45D1I0]

theorem adverseCompleteS45D1Cmp2 : indexScore (7/5) (controlPenalty savedCref uniformQuoteError unitRoleUnused .complete) adverseCompleteS45Before [.query 1] (.hydeRetriever 2) ≤ indexScore (7/5) (controlPenalty savedCref uniformQuoteError unitRoleUnused .complete) adverseCompleteS45Before [.query 1] (.hydeRetriever 1) := by
  rw [adverseCompleteS45D1I2,adverseCompleteS45D1I0]

theorem adverseCompleteS45Choice1 : nativeFirstChoice (indexScore (7/5) (controlPenalty savedCref uniformQuoteError unitRoleUnused .complete) adverseCompleteS45Before [.query 1]) adverseCompleteS45Before [.query 1] = .hydeRetriever 1 := by
  apply visited_choice_from_ordered_certificate _ _ [.query 1] [] [.hydeRetriever 0,.hydeRetriever 2] (.hydeRetriever 1) (by decide)
  · intro a ha
    have ho : orderedLegalAvailable [.query 1] = [.hydeRetriever 1,.hydeRetriever 0,.hydeRetriever 2] := by decide
    rw [ho] at ha
    simp only [List.mem_cons,List.not_mem_nil,or_false] at ha
    rcases ha with rfl | rfl | rfl <;> decide
  · simp
  · intro a ha
    simp only [List.mem_cons,List.not_mem_nil,or_false] at ha
    rcases ha with rfl | rfl
    · exact adverseCompleteS45D1Cmp1
    · exact adverseCompleteS45D1Cmp2

theorem adverseCompleteS45D2I0 : indexScore (7/5) (controlPenalty savedCref uniformQuoteError unitRoleUnused .complete) adverseCompleteS45Before [.query 1,.hydeRetriever 1] (.selection 1) = treeIndex ((0/1)/3) (7/5) 0 12 3 := by
  have hs : replayBackup adverseCompleteS45Before emptyStatistics ([.query 1,.hydeRetriever 1]++[.selection 1]) = ⟨3,(0/1)⟩ := by
    rw [replayBackup_empty_closed_form]
    simp +decide [backedEvents,adverseCompleteS45Before,adverseCompleteProposal,adverseCompleteEvent1,adverseCompleteEvent2,adverseCompleteEvent3,adverseCompleteEvent4,adverseCompleteEvent5,adverseCompleteEvent6,adverseCompleteEvent7,adverseCompleteEvent8,adverseCompleteEvent9,adverseCompleteEvent10,adverseCompleteEvent11,adverseCompleteEvent12,adverseCompleteEvent13,adverseCompleteEvent14,adverseCompleteEvent15,adverseCompleteEvent16,adverseCompleteEvent17,adverseCompleteEvent18,adverseCompleteEvent19,adverseCompleteEvent20,adverseCompleteEvent21,adverseCompleteEvent22,adverseCompleteEvent23,adverseCompleteEvent24,adverseCompleteEvent25,adverseCompleteEvent26,adverseCompleteEvent27,adverseCompleteEvent28,adverseCompleteEvent29,adverseCompleteEvent30,adverseCompleteEvent31,adverseCompleteEvent32,adverseCompleteEvent33,adverseCompleteEvent34,adverseCompleteEvent35,adverseCompleteEvent36,adverseCompleteEvent37,adverseCompleteEvent38,adverseCompleteEvent39,adverseCompleteEvent40,adverseCompleteEvent41,adverseCompleteEvent42,adverseCompleteEvent43,adverseCompleteEvent44,taskReward]
    <;> norm_num
  have hp : rawVisits adverseCompleteS45Before [.query 1,.hydeRetriever 1] = 12 := by decide
  have hn : rawVisits adverseCompleteS45Before ([.query 1,.hydeRetriever 1]++[.selection 1]) = 3 := by decide
  have hz : (controlPenalty savedCref uniformQuoteError unitRoleUnused .complete) adverseCompleteS45Before [.query 1,.hydeRetriever 1] (.selection 1) = 0 := by
    apply control_penalty_empty_of_prior_terminal .complete savedCref uniformQuoteError adverseCompleteS45Before [.query 1,.hydeRetriever 1] (.selection 1) 14 (by decide)
    · decide
    · decide
  unfold indexScore
  rw [hs,hp,hn,hz]
  simp only [BackupStat.mean]
  norm_num

theorem adverseCompleteS45D2I1 : indexScore (7/5) (controlPenalty savedCref uniformQuoteError unitRoleUnused .complete) adverseCompleteS45Before [.query 1,.hydeRetriever 1] (.selection 2) = treeIndex ((0/1)/3) (7/5) 0 12 3 := by
  have hs : replayBackup adverseCompleteS45Before emptyStatistics ([.query 1,.hydeRetriever 1]++[.selection 2]) = ⟨3,(0/1)⟩ := by
    rw [replayBackup_empty_closed_form]
    simp +decide [backedEvents,adverseCompleteS45Before,adverseCompleteProposal,adverseCompleteEvent1,adverseCompleteEvent2,adverseCompleteEvent3,adverseCompleteEvent4,adverseCompleteEvent5,adverseCompleteEvent6,adverseCompleteEvent7,adverseCompleteEvent8,adverseCompleteEvent9,adverseCompleteEvent10,adverseCompleteEvent11,adverseCompleteEvent12,adverseCompleteEvent13,adverseCompleteEvent14,adverseCompleteEvent15,adverseCompleteEvent16,adverseCompleteEvent17,adverseCompleteEvent18,adverseCompleteEvent19,adverseCompleteEvent20,adverseCompleteEvent21,adverseCompleteEvent22,adverseCompleteEvent23,adverseCompleteEvent24,adverseCompleteEvent25,adverseCompleteEvent26,adverseCompleteEvent27,adverseCompleteEvent28,adverseCompleteEvent29,adverseCompleteEvent30,adverseCompleteEvent31,adverseCompleteEvent32,adverseCompleteEvent33,adverseCompleteEvent34,adverseCompleteEvent35,adverseCompleteEvent36,adverseCompleteEvent37,adverseCompleteEvent38,adverseCompleteEvent39,adverseCompleteEvent40,adverseCompleteEvent41,adverseCompleteEvent42,adverseCompleteEvent43,adverseCompleteEvent44,taskReward]
    <;> norm_num
  have hp : rawVisits adverseCompleteS45Before [.query 1,.hydeRetriever 1] = 12 := by decide
  have hn : rawVisits adverseCompleteS45Before ([.query 1,.hydeRetriever 1]++[.selection 2]) = 3 := by decide
  have hz : (controlPenalty savedCref uniformQuoteError unitRoleUnused .complete) adverseCompleteS45Before [.query 1,.hydeRetriever 1] (.selection 2) = 0 := by
    apply control_penalty_empty_of_prior_terminal .complete savedCref uniformQuoteError adverseCompleteS45Before [.query 1,.hydeRetriever 1] (.selection 2) 17 (by decide)
    · decide
    · decide
  unfold indexScore
  rw [hs,hp,hn,hz]
  simp only [BackupStat.mean]
  norm_num

theorem adverseCompleteS45D2I2 : indexScore (7/5) (controlPenalty savedCref uniformQuoteError unitRoleUnused .complete) adverseCompleteS45Before [.query 1,.hydeRetriever 1] (.selection 3) = treeIndex ((0/1)/3) (7/5) 0 12 3 := by
  have hs : replayBackup adverseCompleteS45Before emptyStatistics ([.query 1,.hydeRetriever 1]++[.selection 3]) = ⟨3,(0/1)⟩ := by
    rw [replayBackup_empty_closed_form]
    simp +decide [backedEvents,adverseCompleteS45Before,adverseCompleteProposal,adverseCompleteEvent1,adverseCompleteEvent2,adverseCompleteEvent3,adverseCompleteEvent4,adverseCompleteEvent5,adverseCompleteEvent6,adverseCompleteEvent7,adverseCompleteEvent8,adverseCompleteEvent9,adverseCompleteEvent10,adverseCompleteEvent11,adverseCompleteEvent12,adverseCompleteEvent13,adverseCompleteEvent14,adverseCompleteEvent15,adverseCompleteEvent16,adverseCompleteEvent17,adverseCompleteEvent18,adverseCompleteEvent19,adverseCompleteEvent20,adverseCompleteEvent21,adverseCompleteEvent22,adverseCompleteEvent23,adverseCompleteEvent24,adverseCompleteEvent25,adverseCompleteEvent26,adverseCompleteEvent27,adverseCompleteEvent28,adverseCompleteEvent29,adverseCompleteEvent30,adverseCompleteEvent31,adverseCompleteEvent32,adverseCompleteEvent33,adverseCompleteEvent34,adverseCompleteEvent35,adverseCompleteEvent36,adverseCompleteEvent37,adverseCompleteEvent38,adverseCompleteEvent39,adverseCompleteEvent40,adverseCompleteEvent41,adverseCompleteEvent42,adverseCompleteEvent43,adverseCompleteEvent44,taskReward]
    <;> norm_num
  have hp : rawVisits adverseCompleteS45Before [.query 1,.hydeRetriever 1] = 12 := by decide
  have hn : rawVisits adverseCompleteS45Before ([.query 1,.hydeRetriever 1]++[.selection 3]) = 3 := by decide
  have hz : (controlPenalty savedCref uniformQuoteError unitRoleUnused .complete) adverseCompleteS45Before [.query 1,.hydeRetriever 1] (.selection 3) = 0 := by
    apply control_penalty_empty_of_prior_terminal .complete savedCref uniformQuoteError adverseCompleteS45Before [.query 1,.hydeRetriever 1] (.selection 3) 20 (by decide)
    · decide
    · decide
  unfold indexScore
  rw [hs,hp,hn,hz]
  simp only [BackupStat.mean]
  norm_num

theorem adverseCompleteS45D2I3 : indexScore (7/5) (controlPenalty savedCref uniformQuoteError unitRoleUnused .complete) adverseCompleteS45Before [.query 1,.hydeRetriever 1] (.selection 0) = treeIndex ((0/1)/2) (7/5) 0 12 2 := by
  have hs : replayBackup adverseCompleteS45Before emptyStatistics ([.query 1,.hydeRetriever 1]++[.selection 0]) = ⟨2,(0/1)⟩ := by
    rw [replayBackup_empty_closed_form]
    simp +decide [backedEvents,adverseCompleteS45Before,adverseCompleteProposal,adverseCompleteEvent1,adverseCompleteEvent2,adverseCompleteEvent3,adverseCompleteEvent4,adverseCompleteEvent5,adverseCompleteEvent6,adverseCompleteEvent7,adverseCompleteEvent8,adverseCompleteEvent9,adverseCompleteEvent10,adverseCompleteEvent11,adverseCompleteEvent12,adverseCompleteEvent13,adverseCompleteEvent14,adverseCompleteEvent15,adverseCompleteEvent16,adverseCompleteEvent17,adverseCompleteEvent18,adverseCompleteEvent19,adverseCompleteEvent20,adverseCompleteEvent21,adverseCompleteEvent22,adverseCompleteEvent23,adverseCompleteEvent24,adverseCompleteEvent25,adverseCompleteEvent26,adverseCompleteEvent27,adverseCompleteEvent28,adverseCompleteEvent29,adverseCompleteEvent30,adverseCompleteEvent31,adverseCompleteEvent32,adverseCompleteEvent33,adverseCompleteEvent34,adverseCompleteEvent35,adverseCompleteEvent36,adverseCompleteEvent37,adverseCompleteEvent38,adverseCompleteEvent39,adverseCompleteEvent40,adverseCompleteEvent41,adverseCompleteEvent42,adverseCompleteEvent43,adverseCompleteEvent44,taskReward]
    <;> norm_num
  have hp : rawVisits adverseCompleteS45Before [.query 1,.hydeRetriever 1] = 12 := by decide
  have hn : rawVisits adverseCompleteS45Before ([.query 1,.hydeRetriever 1]++[.selection 0]) = 2 := by decide
  have hz : (controlPenalty savedCref uniformQuoteError unitRoleUnused .complete) adverseCompleteS45Before [.query 1,.hydeRetriever 1] (.selection 0) = 0 := by
    apply control_penalty_empty_of_prior_terminal .complete savedCref uniformQuoteError adverseCompleteS45Before [.query 1,.hydeRetriever 1] (.selection 0) 8 (by decide)
    · decide
    · decide
  unfold indexScore
  rw [hs,hp,hn,hz]
  simp only [BackupStat.mean]
  norm_num

theorem adverseCompleteS45D2Cmp0 : indexScore (7/5) (controlPenalty savedCref uniformQuoteError unitRoleUnused .complete) adverseCompleteS45Before [.query 1,.hydeRetriever 1] (.selection 1) < indexScore (7/5) (controlPenalty savedCref uniformQuoteError unitRoleUnused .complete) adverseCompleteS45Before [.query 1,.hydeRetriever 1] (.selection 0) := by
  rw [adverseCompleteS45D2I0,adverseCompleteS45D2I3]
  have h := index_strict_order_from_intervals ((0/1)/2) ((0/1)/3) 0 0 (79272473/50000000) (6472571/5000000)
    (treeBonus (7/5) 12 2) (treeBonus (7/5) 12 3)
    (trajectory_bonus_12_2).1 (trajectory_bonus_12_3).2 (by norm_num)
  simpa only [treeIndex,sub_zero] using h

theorem adverseCompleteS45D2Cmp1 : indexScore (7/5) (controlPenalty savedCref uniformQuoteError unitRoleUnused .complete) adverseCompleteS45Before [.query 1,.hydeRetriever 1] (.selection 2) < indexScore (7/5) (controlPenalty savedCref uniformQuoteError unitRoleUnused .complete) adverseCompleteS45Before [.query 1,.hydeRetriever 1] (.selection 0) := by
  rw [adverseCompleteS45D2I1,adverseCompleteS45D2I3]
  have h := index_strict_order_from_intervals ((0/1)/2) ((0/1)/3) 0 0 (79272473/50000000) (6472571/5000000)
    (treeBonus (7/5) 12 2) (treeBonus (7/5) 12 3)
    (trajectory_bonus_12_2).1 (trajectory_bonus_12_3).2 (by norm_num)
  simpa only [treeIndex,sub_zero] using h

theorem adverseCompleteS45D2Cmp2 : indexScore (7/5) (controlPenalty savedCref uniformQuoteError unitRoleUnused .complete) adverseCompleteS45Before [.query 1,.hydeRetriever 1] (.selection 3) < indexScore (7/5) (controlPenalty savedCref uniformQuoteError unitRoleUnused .complete) adverseCompleteS45Before [.query 1,.hydeRetriever 1] (.selection 0) := by
  rw [adverseCompleteS45D2I2,adverseCompleteS45D2I3]
  have h := index_strict_order_from_intervals ((0/1)/2) ((0/1)/3) 0 0 (79272473/50000000) (6472571/5000000)
    (treeBonus (7/5) 12 2) (treeBonus (7/5) 12 3)
    (trajectory_bonus_12_2).1 (trajectory_bonus_12_3).2 (by norm_num)
  simpa only [treeIndex,sub_zero] using h

theorem adverseCompleteS45Choice2 : nativeFirstChoice (indexScore (7/5) (controlPenalty savedCref uniformQuoteError unitRoleUnused .complete) adverseCompleteS45Before [.query 1,.hydeRetriever 1]) adverseCompleteS45Before [.query 1,.hydeRetriever 1] = .selection 0 := by
  apply visited_choice_from_ordered_certificate _ _ [.query 1,.hydeRetriever 1] [.selection 1,.selection 2,.selection 3] [] (.selection 0) (by decide)
  · intro a ha
    have ho : orderedLegalAvailable [.query 1,.hydeRetriever 1] = [.selection 1,.selection 2,.selection 3,.selection 0] := by decide
    rw [ho] at ha
    simp only [List.mem_cons,List.not_mem_nil,or_false] at ha
    rcases ha with rfl | rfl | rfl | rfl <;> decide
  · intro a ha
    simp only [List.mem_cons,List.not_mem_nil,or_false] at ha
    rcases ha with rfl | rfl | rfl
    · exact adverseCompleteS45D2Cmp0
    · exact adverseCompleteS45D2Cmp1
    · exact adverseCompleteS45D2Cmp2
  · simp

theorem adverseCompleteS45ActualEvent : nativeEvent budgetTape (7/5) (controlPenalty savedCref uniformQuoteError unitRoleUnused .complete)
    (taskReward true (2/5) (1/2)) adverseCompleteS45Before = adverseCompleteEvent45 := by
  have hs0 := native_select_existing_step budgetTape (7/5) (controlPenalty savedCref uniformQuoteError unitRoleUnused .complete) adverseCompleteS45Before 8 [] (.query 1)
    (by decide) (by decide) adverseCompleteS45Choice0
  have hs1 := native_select_existing_step budgetTape (7/5) (controlPenalty savedCref uniformQuoteError unitRoleUnused .complete) adverseCompleteS45Before 7 [.query 1] (.hydeRetriever 1)
    (by decide) (by decide) adverseCompleteS45Choice1
  have hs2 := native_select_existing_step budgetTape (7/5) (controlPenalty savedCref uniformQuoteError unitRoleUnused .complete) adverseCompleteS45Before 6 [.query 1,.hydeRetriever 1] (.selection 0)
    (by decide) (by decide) adverseCompleteS45Choice2
  have hnew := native_select_new_step budgetTape (7/5) (controlPenalty savedCref uniformQuoteError unitRoleUnused .complete) adverseCompleteS45Before 5 [.query 1,.hydeRetriever 1,.selection 0]
    [.width 3,.width 0,.width 2] (.width 3) (by decide) (by decide) (by decide) (by decide)
  have hs : nativeSelect budgetTape (7/5) (controlPenalty savedCref uniformQuoteError unitRoleUnused .complete) adverseCompleteS45Before 9 [] = [.query 1,.hydeRetriever 1,.selection 0,.width 3] := by
    rw [hs0]
    change nativeSelect budgetTape (7/5) (controlPenalty savedCref uniformQuoteError unitRoleUnused .complete) adverseCompleteS45Before 8 [.query 1] = _
    rw [hs1]
    change nativeSelect budgetTape (7/5) (controlPenalty savedCref uniformQuoteError unitRoleUnused .complete) adverseCompleteS45Before 7 [.query 1,.hydeRetriever 1] = _
    rw [hs2]
    change nativeSelect budgetTape (7/5) (controlPenalty savedCref uniformQuoteError unitRoleUnused .complete) adverseCompleteS45Before 6 [.query 1,.hydeRetriever 1,.selection 0] = _
    rw [hnew] <;> rfl
  have hr : repairedRollout budgetTape adverseCompleteS45Before 9 [.query 1,.hydeRetriever 1,.selection 0,.width 3] = [.query 1,.hydeRetriever 1,.selection 0,.width 3,.stop,.reranker 0,.topm 0,.context 0,.answer 0] := by decide
  simp only [nativeEvent,hs,hr]
  rfl

end AgentUCT32MConcrete
