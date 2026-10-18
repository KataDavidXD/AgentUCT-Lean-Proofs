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

def favorableCompleteS36Before := favorableCompleteProposal.take 35

theorem favorableCompleteS36Choice0 : nativeFirstChoice (indexScore (7/5) (controlPenalty savedCref uniformQuoteError unitRoleUnused .complete) favorableCompleteS36Before []) favorableCompleteS36Before [] = .query 1 := by
  apply complete_root_from_physical_gap favorableCompleteS36Before (favorableComplete_prefix_rewards 35) (by decide)
  · intro q; fin_cases q <;> decide
  · exact AgentUCTNextExact.favorable_complete_hyde_root_suffix_empty 35 (by omega)
  · intro q hq
    exact AgentUCTNextExact.favorable_complete_normal_root_physical_quote_exact 35 (by omega) q hq

theorem favorableCompleteS36D1I0 : indexScore (7/5) (controlPenalty savedCref uniformQuoteError unitRoleUnused .complete) favorableCompleteS36Before [.query 1] (.hydeRetriever 1) = treeIndex ((3/2)/11) (7/5) 0 28 11 := by
  have hs : replayBackup favorableCompleteS36Before emptyStatistics ([.query 1]++[.hydeRetriever 1]) = ⟨11,(3/2)⟩ := by
    rw [replayBackup_empty_closed_form]
    simp +decide [backedEvents,favorableCompleteS36Before,favorableCompleteProposal,favorableCompleteEvent1,favorableCompleteEvent2,favorableCompleteEvent3,favorableCompleteEvent4,favorableCompleteEvent5,favorableCompleteEvent6,favorableCompleteEvent7,favorableCompleteEvent8,favorableCompleteEvent9,favorableCompleteEvent10,favorableCompleteEvent11,favorableCompleteEvent12,favorableCompleteEvent13,favorableCompleteEvent14,favorableCompleteEvent15,favorableCompleteEvent16,favorableCompleteEvent17,favorableCompleteEvent18,favorableCompleteEvent19,favorableCompleteEvent20,favorableCompleteEvent21,favorableCompleteEvent22,favorableCompleteEvent23,favorableCompleteEvent24,favorableCompleteEvent25,favorableCompleteEvent26,favorableCompleteEvent27,favorableCompleteEvent28,favorableCompleteEvent29,favorableCompleteEvent30,favorableCompleteEvent31,favorableCompleteEvent32,favorableCompleteEvent33,favorableCompleteEvent34,favorableCompleteEvent35,taskReward]
    <;> norm_num
  have hp : rawVisits favorableCompleteS36Before [.query 1] = 28 := by decide
  have hn : rawVisits favorableCompleteS36Before ([.query 1]++[.hydeRetriever 1]) = 11 := by decide
  have hz : (controlPenalty savedCref uniformQuoteError unitRoleUnused .complete) favorableCompleteS36Before [.query 1] (.hydeRetriever 1) = 0 := by
    apply control_penalty_empty_of_prior_terminal .complete savedCref uniformQuoteError favorableCompleteS36Before [.query 1] (.hydeRetriever 1) 8 (by decide)
    · decide
    · decide
  unfold indexScore
  rw [hs,hp,hn,hz]
  simp only [BackupStat.mean]
  norm_num

theorem favorableCompleteS36D1I1 : indexScore (7/5) (controlPenalty savedCref uniformQuoteError unitRoleUnused .complete) favorableCompleteS36Before [.query 1] (.hydeRetriever 0) = treeIndex ((0/1)/8) (7/5) 0 28 8 := by
  have hs : replayBackup favorableCompleteS36Before emptyStatistics ([.query 1]++[.hydeRetriever 0]) = ⟨8,(0/1)⟩ := by
    rw [replayBackup_empty_closed_form]
    simp +decide [backedEvents,favorableCompleteS36Before,favorableCompleteProposal,favorableCompleteEvent1,favorableCompleteEvent2,favorableCompleteEvent3,favorableCompleteEvent4,favorableCompleteEvent5,favorableCompleteEvent6,favorableCompleteEvent7,favorableCompleteEvent8,favorableCompleteEvent9,favorableCompleteEvent10,favorableCompleteEvent11,favorableCompleteEvent12,favorableCompleteEvent13,favorableCompleteEvent14,favorableCompleteEvent15,favorableCompleteEvent16,favorableCompleteEvent17,favorableCompleteEvent18,favorableCompleteEvent19,favorableCompleteEvent20,favorableCompleteEvent21,favorableCompleteEvent22,favorableCompleteEvent23,favorableCompleteEvent24,favorableCompleteEvent25,favorableCompleteEvent26,favorableCompleteEvent27,favorableCompleteEvent28,favorableCompleteEvent29,favorableCompleteEvent30,favorableCompleteEvent31,favorableCompleteEvent32,favorableCompleteEvent33,favorableCompleteEvent34,favorableCompleteEvent35,taskReward]
    <;> norm_num
  have hp : rawVisits favorableCompleteS36Before [.query 1] = 28 := by decide
  have hn : rawVisits favorableCompleteS36Before ([.query 1]++[.hydeRetriever 0]) = 8 := by decide
  have hz : (controlPenalty savedCref uniformQuoteError unitRoleUnused .complete) favorableCompleteS36Before [.query 1] (.hydeRetriever 0) = 0 := by
    apply control_penalty_empty_of_prior_terminal .complete savedCref uniformQuoteError favorableCompleteS36Before [.query 1] (.hydeRetriever 0) 1 (by decide)
    · decide
    · decide
  unfold indexScore
  rw [hs,hp,hn,hz]
  simp only [BackupStat.mean]
  norm_num

theorem favorableCompleteS36D1I2 : indexScore (7/5) (controlPenalty savedCref uniformQuoteError unitRoleUnused .complete) favorableCompleteS36Before [.query 1] (.hydeRetriever 2) = treeIndex ((0/1)/8) (7/5) 0 28 8 := by
  have hs : replayBackup favorableCompleteS36Before emptyStatistics ([.query 1]++[.hydeRetriever 2]) = ⟨8,(0/1)⟩ := by
    rw [replayBackup_empty_closed_form]
    simp +decide [backedEvents,favorableCompleteS36Before,favorableCompleteProposal,favorableCompleteEvent1,favorableCompleteEvent2,favorableCompleteEvent3,favorableCompleteEvent4,favorableCompleteEvent5,favorableCompleteEvent6,favorableCompleteEvent7,favorableCompleteEvent8,favorableCompleteEvent9,favorableCompleteEvent10,favorableCompleteEvent11,favorableCompleteEvent12,favorableCompleteEvent13,favorableCompleteEvent14,favorableCompleteEvent15,favorableCompleteEvent16,favorableCompleteEvent17,favorableCompleteEvent18,favorableCompleteEvent19,favorableCompleteEvent20,favorableCompleteEvent21,favorableCompleteEvent22,favorableCompleteEvent23,favorableCompleteEvent24,favorableCompleteEvent25,favorableCompleteEvent26,favorableCompleteEvent27,favorableCompleteEvent28,favorableCompleteEvent29,favorableCompleteEvent30,favorableCompleteEvent31,favorableCompleteEvent32,favorableCompleteEvent33,favorableCompleteEvent34,favorableCompleteEvent35,taskReward]
    <;> norm_num
  have hp : rawVisits favorableCompleteS36Before [.query 1] = 28 := by decide
  have hn : rawVisits favorableCompleteS36Before ([.query 1]++[.hydeRetriever 2]) = 8 := by decide
  have hz : (controlPenalty savedCref uniformQuoteError unitRoleUnused .complete) favorableCompleteS36Before [.query 1] (.hydeRetriever 2) = 0 := by
    apply control_penalty_empty_of_prior_terminal .complete savedCref uniformQuoteError favorableCompleteS36Before [.query 1] (.hydeRetriever 2) 10 (by decide)
    · decide
    · decide
  unfold indexScore
  rw [hs,hp,hn,hz]
  simp only [BackupStat.mean]
  norm_num

theorem favorableCompleteS36D1Cmp1 : indexScore (7/5) (controlPenalty savedCref uniformQuoteError unitRoleUnused .complete) favorableCompleteS36Before [.query 1] (.hydeRetriever 0) ≤ indexScore (7/5) (controlPenalty savedCref uniformQuoteError unitRoleUnused .complete) favorableCompleteS36Before [.query 1] (.hydeRetriever 1) := by
  rw [favorableCompleteS36D1I1,favorableCompleteS36D1I0]
  have h := index_weak_order_from_intervals ((3/2)/11) ((0/1)/8) 0 0 (38729537/50000000) (22707209/25000000)
    (treeBonus (7/5) 28 11) (treeBonus (7/5) 28 8)
    (trajectory_bonus_28_11).1 (trajectory_bonus_28_8).2 (by norm_num)
  simpa only [treeIndex,sub_zero] using h

theorem favorableCompleteS36D1Cmp2 : indexScore (7/5) (controlPenalty savedCref uniformQuoteError unitRoleUnused .complete) favorableCompleteS36Before [.query 1] (.hydeRetriever 2) ≤ indexScore (7/5) (controlPenalty savedCref uniformQuoteError unitRoleUnused .complete) favorableCompleteS36Before [.query 1] (.hydeRetriever 1) := by
  rw [favorableCompleteS36D1I2,favorableCompleteS36D1I0]
  have h := index_weak_order_from_intervals ((3/2)/11) ((0/1)/8) 0 0 (38729537/50000000) (22707209/25000000)
    (treeBonus (7/5) 28 11) (treeBonus (7/5) 28 8)
    (trajectory_bonus_28_11).1 (trajectory_bonus_28_8).2 (by norm_num)
  simpa only [treeIndex,sub_zero] using h

theorem favorableCompleteS36Choice1 : nativeFirstChoice (indexScore (7/5) (controlPenalty savedCref uniformQuoteError unitRoleUnused .complete) favorableCompleteS36Before [.query 1]) favorableCompleteS36Before [.query 1] = .hydeRetriever 1 := by
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
    · exact favorableCompleteS36D1Cmp1
    · exact favorableCompleteS36D1Cmp2

theorem favorableCompleteS36D2I0 : indexScore (7/5) (controlPenalty savedCref uniformQuoteError unitRoleUnused .complete) favorableCompleteS36Before [.query 1,.hydeRetriever 1] (.selection 1) = treeIndex ((0/1)/2) (7/5) 0 11 2 := by
  have hs : replayBackup favorableCompleteS36Before emptyStatistics ([.query 1,.hydeRetriever 1]++[.selection 1]) = ⟨2,(0/1)⟩ := by
    rw [replayBackup_empty_closed_form]
    simp +decide [backedEvents,favorableCompleteS36Before,favorableCompleteProposal,favorableCompleteEvent1,favorableCompleteEvent2,favorableCompleteEvent3,favorableCompleteEvent4,favorableCompleteEvent5,favorableCompleteEvent6,favorableCompleteEvent7,favorableCompleteEvent8,favorableCompleteEvent9,favorableCompleteEvent10,favorableCompleteEvent11,favorableCompleteEvent12,favorableCompleteEvent13,favorableCompleteEvent14,favorableCompleteEvent15,favorableCompleteEvent16,favorableCompleteEvent17,favorableCompleteEvent18,favorableCompleteEvent19,favorableCompleteEvent20,favorableCompleteEvent21,favorableCompleteEvent22,favorableCompleteEvent23,favorableCompleteEvent24,favorableCompleteEvent25,favorableCompleteEvent26,favorableCompleteEvent27,favorableCompleteEvent28,favorableCompleteEvent29,favorableCompleteEvent30,favorableCompleteEvent31,favorableCompleteEvent32,favorableCompleteEvent33,favorableCompleteEvent34,favorableCompleteEvent35,taskReward]
    <;> norm_num
  have hp : rawVisits favorableCompleteS36Before [.query 1,.hydeRetriever 1] = 11 := by decide
  have hn : rawVisits favorableCompleteS36Before ([.query 1,.hydeRetriever 1]++[.selection 1]) = 2 := by decide
  have hz : (controlPenalty savedCref uniformQuoteError unitRoleUnused .complete) favorableCompleteS36Before [.query 1,.hydeRetriever 1] (.selection 1) = 0 := by
    apply control_penalty_empty_of_prior_terminal .complete savedCref uniformQuoteError favorableCompleteS36Before [.query 1,.hydeRetriever 1] (.selection 1) 14 (by decide)
    · decide
    · decide
  unfold indexScore
  rw [hs,hp,hn,hz]
  simp only [BackupStat.mean]
  norm_num

theorem favorableCompleteS36D2I1 : indexScore (7/5) (controlPenalty savedCref uniformQuoteError unitRoleUnused .complete) favorableCompleteS36Before [.query 1,.hydeRetriever 1] (.selection 2) = treeIndex ((0/1)/2) (7/5) 0 11 2 := by
  have hs : replayBackup favorableCompleteS36Before emptyStatistics ([.query 1,.hydeRetriever 1]++[.selection 2]) = ⟨2,(0/1)⟩ := by
    rw [replayBackup_empty_closed_form]
    simp +decide [backedEvents,favorableCompleteS36Before,favorableCompleteProposal,favorableCompleteEvent1,favorableCompleteEvent2,favorableCompleteEvent3,favorableCompleteEvent4,favorableCompleteEvent5,favorableCompleteEvent6,favorableCompleteEvent7,favorableCompleteEvent8,favorableCompleteEvent9,favorableCompleteEvent10,favorableCompleteEvent11,favorableCompleteEvent12,favorableCompleteEvent13,favorableCompleteEvent14,favorableCompleteEvent15,favorableCompleteEvent16,favorableCompleteEvent17,favorableCompleteEvent18,favorableCompleteEvent19,favorableCompleteEvent20,favorableCompleteEvent21,favorableCompleteEvent22,favorableCompleteEvent23,favorableCompleteEvent24,favorableCompleteEvent25,favorableCompleteEvent26,favorableCompleteEvent27,favorableCompleteEvent28,favorableCompleteEvent29,favorableCompleteEvent30,favorableCompleteEvent31,favorableCompleteEvent32,favorableCompleteEvent33,favorableCompleteEvent34,favorableCompleteEvent35,taskReward]
    <;> norm_num
  have hp : rawVisits favorableCompleteS36Before [.query 1,.hydeRetriever 1] = 11 := by decide
  have hn : rawVisits favorableCompleteS36Before ([.query 1,.hydeRetriever 1]++[.selection 2]) = 2 := by decide
  have hz : (controlPenalty savedCref uniformQuoteError unitRoleUnused .complete) favorableCompleteS36Before [.query 1,.hydeRetriever 1] (.selection 2) = 0 := by
    apply control_penalty_empty_of_prior_terminal .complete savedCref uniformQuoteError favorableCompleteS36Before [.query 1,.hydeRetriever 1] (.selection 2) 15 (by decide)
    · decide
    · decide
  unfold indexScore
  rw [hs,hp,hn,hz]
  simp only [BackupStat.mean]
  norm_num

theorem favorableCompleteS36D2I2 : indexScore (7/5) (controlPenalty savedCref uniformQuoteError unitRoleUnused .complete) favorableCompleteS36Before [.query 1,.hydeRetriever 1] (.selection 3) = treeIndex ((0/1)/2) (7/5) 0 11 2 := by
  have hs : replayBackup favorableCompleteS36Before emptyStatistics ([.query 1,.hydeRetriever 1]++[.selection 3]) = ⟨2,(0/1)⟩ := by
    rw [replayBackup_empty_closed_form]
    simp +decide [backedEvents,favorableCompleteS36Before,favorableCompleteProposal,favorableCompleteEvent1,favorableCompleteEvent2,favorableCompleteEvent3,favorableCompleteEvent4,favorableCompleteEvent5,favorableCompleteEvent6,favorableCompleteEvent7,favorableCompleteEvent8,favorableCompleteEvent9,favorableCompleteEvent10,favorableCompleteEvent11,favorableCompleteEvent12,favorableCompleteEvent13,favorableCompleteEvent14,favorableCompleteEvent15,favorableCompleteEvent16,favorableCompleteEvent17,favorableCompleteEvent18,favorableCompleteEvent19,favorableCompleteEvent20,favorableCompleteEvent21,favorableCompleteEvent22,favorableCompleteEvent23,favorableCompleteEvent24,favorableCompleteEvent25,favorableCompleteEvent26,favorableCompleteEvent27,favorableCompleteEvent28,favorableCompleteEvent29,favorableCompleteEvent30,favorableCompleteEvent31,favorableCompleteEvent32,favorableCompleteEvent33,favorableCompleteEvent34,favorableCompleteEvent35,taskReward]
    <;> norm_num
  have hp : rawVisits favorableCompleteS36Before [.query 1,.hydeRetriever 1] = 11 := by decide
  have hn : rawVisits favorableCompleteS36Before ([.query 1,.hydeRetriever 1]++[.selection 3]) = 2 := by decide
  have hz : (controlPenalty savedCref uniformQuoteError unitRoleUnused .complete) favorableCompleteS36Before [.query 1,.hydeRetriever 1] (.selection 3) = 0 := by
    apply control_penalty_empty_of_prior_terminal .complete savedCref uniformQuoteError favorableCompleteS36Before [.query 1,.hydeRetriever 1] (.selection 3) 18 (by decide)
    · decide
    · decide
  unfold indexScore
  rw [hs,hp,hn,hz]
  simp only [BackupStat.mean]
  norm_num

theorem favorableCompleteS36D2I3 : indexScore (7/5) (controlPenalty savedCref uniformQuoteError unitRoleUnused .complete) favorableCompleteS36Before [.query 1,.hydeRetriever 1] (.selection 0) = treeIndex ((1/1)/4) (7/5) 0 11 4 := by
  have hs : replayBackup favorableCompleteS36Before emptyStatistics ([.query 1,.hydeRetriever 1]++[.selection 0]) = ⟨4,(1/1)⟩ := by
    rw [replayBackup_empty_closed_form]
    simp +decide [backedEvents,favorableCompleteS36Before,favorableCompleteProposal,favorableCompleteEvent1,favorableCompleteEvent2,favorableCompleteEvent3,favorableCompleteEvent4,favorableCompleteEvent5,favorableCompleteEvent6,favorableCompleteEvent7,favorableCompleteEvent8,favorableCompleteEvent9,favorableCompleteEvent10,favorableCompleteEvent11,favorableCompleteEvent12,favorableCompleteEvent13,favorableCompleteEvent14,favorableCompleteEvent15,favorableCompleteEvent16,favorableCompleteEvent17,favorableCompleteEvent18,favorableCompleteEvent19,favorableCompleteEvent20,favorableCompleteEvent21,favorableCompleteEvent22,favorableCompleteEvent23,favorableCompleteEvent24,favorableCompleteEvent25,favorableCompleteEvent26,favorableCompleteEvent27,favorableCompleteEvent28,favorableCompleteEvent29,favorableCompleteEvent30,favorableCompleteEvent31,favorableCompleteEvent32,favorableCompleteEvent33,favorableCompleteEvent34,favorableCompleteEvent35,taskReward]
    <;> norm_num
  have hp : rawVisits favorableCompleteS36Before [.query 1,.hydeRetriever 1] = 11 := by decide
  have hn : rawVisits favorableCompleteS36Before ([.query 1,.hydeRetriever 1]++[.selection 0]) = 4 := by decide
  have hz : (controlPenalty savedCref uniformQuoteError unitRoleUnused .complete) favorableCompleteS36Before [.query 1,.hydeRetriever 1] (.selection 0) = 0 := by
    apply control_penalty_empty_of_prior_terminal .complete savedCref uniformQuoteError favorableCompleteS36Before [.query 1,.hydeRetriever 1] (.selection 0) 8 (by decide)
    · decide
    · decide
  unfold indexScore
  rw [hs,hp,hn,hz]
  simp only [BackupStat.mean]
  norm_num

theorem favorableCompleteS36D2Cmp1 : indexScore (7/5) (controlPenalty savedCref uniformQuoteError unitRoleUnused .complete) favorableCompleteS36Before [.query 1,.hydeRetriever 1] (.selection 2) ≤ indexScore (7/5) (controlPenalty savedCref uniformQuoteError unitRoleUnused .complete) favorableCompleteS36Before [.query 1,.hydeRetriever 1] (.selection 1) := by
  rw [favorableCompleteS36D2I1,favorableCompleteS36D2I0]

theorem favorableCompleteS36D2Cmp2 : indexScore (7/5) (controlPenalty savedCref uniformQuoteError unitRoleUnused .complete) favorableCompleteS36Before [.query 1,.hydeRetriever 1] (.selection 3) ≤ indexScore (7/5) (controlPenalty savedCref uniformQuoteError unitRoleUnused .complete) favorableCompleteS36Before [.query 1,.hydeRetriever 1] (.selection 1) := by
  rw [favorableCompleteS36D2I2,favorableCompleteS36D2I0]

theorem favorableCompleteS36D2Cmp3 : indexScore (7/5) (controlPenalty savedCref uniformQuoteError unitRoleUnused .complete) favorableCompleteS36Before [.query 1,.hydeRetriever 1] (.selection 0) ≤ indexScore (7/5) (controlPenalty savedCref uniformQuoteError unitRoleUnused .complete) favorableCompleteS36Before [.query 1,.hydeRetriever 1] (.selection 1) := by
  rw [favorableCompleteS36D2I3,favorableCompleteS36D2I0]
  have h := index_weak_order_from_intervals ((0/1)/2) ((1/1)/4) 0 0 (39012883/25000000) (27586279/25000000)
    (treeBonus (7/5) 11 2) (treeBonus (7/5) 11 4)
    (trajectory_bonus_11_2).1 (trajectory_bonus_11_4).2 (by norm_num)
  simpa only [treeIndex,sub_zero] using h

theorem favorableCompleteS36Choice2 : nativeFirstChoice (indexScore (7/5) (controlPenalty savedCref uniformQuoteError unitRoleUnused .complete) favorableCompleteS36Before [.query 1,.hydeRetriever 1]) favorableCompleteS36Before [.query 1,.hydeRetriever 1] = .selection 1 := by
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
    · exact favorableCompleteS36D2Cmp1
    · exact favorableCompleteS36D2Cmp2
    · exact favorableCompleteS36D2Cmp3

theorem favorableCompleteS36ActualEvent : nativeEvent budgetTape (7/5) (controlPenalty savedCref uniformQuoteError unitRoleUnused .complete)
    (taskReward false (2/5) (1/2)) favorableCompleteS36Before = favorableCompleteEvent36 := by
  have hs0 := native_select_existing_step budgetTape (7/5) (controlPenalty savedCref uniformQuoteError unitRoleUnused .complete) favorableCompleteS36Before 8 [] (.query 1)
    (by decide) (by decide) favorableCompleteS36Choice0
  have hs1 := native_select_existing_step budgetTape (7/5) (controlPenalty savedCref uniformQuoteError unitRoleUnused .complete) favorableCompleteS36Before 7 [.query 1] (.hydeRetriever 1)
    (by decide) (by decide) favorableCompleteS36Choice1
  have hs2 := native_select_existing_step budgetTape (7/5) (controlPenalty savedCref uniformQuoteError unitRoleUnused .complete) favorableCompleteS36Before 6 [.query 1,.hydeRetriever 1] (.selection 1)
    (by decide) (by decide) favorableCompleteS36Choice2
  have hnew := native_select_new_step budgetTape (7/5) (controlPenalty savedCref uniformQuoteError unitRoleUnused .complete) favorableCompleteS36Before 5 [.query 1,.hydeRetriever 1,.selection 1]
    [.width 3,.width 1,.width 2] (.width 3) (by decide) (by decide) (by decide) (by decide)
  have hs : nativeSelect budgetTape (7/5) (controlPenalty savedCref uniformQuoteError unitRoleUnused .complete) favorableCompleteS36Before 9 [] = [.query 1,.hydeRetriever 1,.selection 1,.width 3] := by
    rw [hs0]
    change nativeSelect budgetTape (7/5) (controlPenalty savedCref uniformQuoteError unitRoleUnused .complete) favorableCompleteS36Before 8 [.query 1] = _
    rw [hs1]
    change nativeSelect budgetTape (7/5) (controlPenalty savedCref uniformQuoteError unitRoleUnused .complete) favorableCompleteS36Before 7 [.query 1,.hydeRetriever 1] = _
    rw [hs2]
    change nativeSelect budgetTape (7/5) (controlPenalty savedCref uniformQuoteError unitRoleUnused .complete) favorableCompleteS36Before 6 [.query 1,.hydeRetriever 1,.selection 1] = _
    rw [hnew] <;> rfl
  have hr : repairedRollout budgetTape favorableCompleteS36Before 9 [.query 1,.hydeRetriever 1,.selection 1,.width 3] = [.query 1,.hydeRetriever 1,.selection 1,.width 3,.stop,.reranker 0,.topm 0,.context 0,.answer 0] := by decide
  simp only [nativeEvent,hs,hr]
  rfl

def favorableCompleteS37Before := favorableCompleteProposal.take 36

theorem favorableCompleteS37Choice0 : nativeFirstChoice (indexScore (7/5) (controlPenalty savedCref uniformQuoteError unitRoleUnused .complete) favorableCompleteS37Before []) favorableCompleteS37Before [] = .query 1 := by
  apply complete_root_from_physical_gap favorableCompleteS37Before (favorableComplete_prefix_rewards 36) (by decide)
  · intro q; fin_cases q <;> decide
  · exact AgentUCTNextExact.favorable_complete_hyde_root_suffix_empty 36 (by omega)
  · intro q hq
    exact AgentUCTNextExact.favorable_complete_normal_root_physical_quote_exact 36 (by omega) q hq

theorem favorableCompleteS37D1I0 : indexScore (7/5) (controlPenalty savedCref uniformQuoteError unitRoleUnused .complete) favorableCompleteS37Before [.query 1] (.hydeRetriever 1) = treeIndex ((3/2)/12) (7/5) 0 29 12 := by
  have hs : replayBackup favorableCompleteS37Before emptyStatistics ([.query 1]++[.hydeRetriever 1]) = ⟨12,(3/2)⟩ := by
    rw [replayBackup_empty_closed_form]
    simp +decide [backedEvents,favorableCompleteS37Before,favorableCompleteProposal,favorableCompleteEvent1,favorableCompleteEvent2,favorableCompleteEvent3,favorableCompleteEvent4,favorableCompleteEvent5,favorableCompleteEvent6,favorableCompleteEvent7,favorableCompleteEvent8,favorableCompleteEvent9,favorableCompleteEvent10,favorableCompleteEvent11,favorableCompleteEvent12,favorableCompleteEvent13,favorableCompleteEvent14,favorableCompleteEvent15,favorableCompleteEvent16,favorableCompleteEvent17,favorableCompleteEvent18,favorableCompleteEvent19,favorableCompleteEvent20,favorableCompleteEvent21,favorableCompleteEvent22,favorableCompleteEvent23,favorableCompleteEvent24,favorableCompleteEvent25,favorableCompleteEvent26,favorableCompleteEvent27,favorableCompleteEvent28,favorableCompleteEvent29,favorableCompleteEvent30,favorableCompleteEvent31,favorableCompleteEvent32,favorableCompleteEvent33,favorableCompleteEvent34,favorableCompleteEvent35,favorableCompleteEvent36,taskReward]
    <;> norm_num
  have hp : rawVisits favorableCompleteS37Before [.query 1] = 29 := by decide
  have hn : rawVisits favorableCompleteS37Before ([.query 1]++[.hydeRetriever 1]) = 12 := by decide
  have hz : (controlPenalty savedCref uniformQuoteError unitRoleUnused .complete) favorableCompleteS37Before [.query 1] (.hydeRetriever 1) = 0 := by
    apply control_penalty_empty_of_prior_terminal .complete savedCref uniformQuoteError favorableCompleteS37Before [.query 1] (.hydeRetriever 1) 8 (by decide)
    · decide
    · decide
  unfold indexScore
  rw [hs,hp,hn,hz]
  simp only [BackupStat.mean]
  norm_num

theorem favorableCompleteS37D1I1 : indexScore (7/5) (controlPenalty savedCref uniformQuoteError unitRoleUnused .complete) favorableCompleteS37Before [.query 1] (.hydeRetriever 0) = treeIndex ((0/1)/8) (7/5) 0 29 8 := by
  have hs : replayBackup favorableCompleteS37Before emptyStatistics ([.query 1]++[.hydeRetriever 0]) = ⟨8,(0/1)⟩ := by
    rw [replayBackup_empty_closed_form]
    simp +decide [backedEvents,favorableCompleteS37Before,favorableCompleteProposal,favorableCompleteEvent1,favorableCompleteEvent2,favorableCompleteEvent3,favorableCompleteEvent4,favorableCompleteEvent5,favorableCompleteEvent6,favorableCompleteEvent7,favorableCompleteEvent8,favorableCompleteEvent9,favorableCompleteEvent10,favorableCompleteEvent11,favorableCompleteEvent12,favorableCompleteEvent13,favorableCompleteEvent14,favorableCompleteEvent15,favorableCompleteEvent16,favorableCompleteEvent17,favorableCompleteEvent18,favorableCompleteEvent19,favorableCompleteEvent20,favorableCompleteEvent21,favorableCompleteEvent22,favorableCompleteEvent23,favorableCompleteEvent24,favorableCompleteEvent25,favorableCompleteEvent26,favorableCompleteEvent27,favorableCompleteEvent28,favorableCompleteEvent29,favorableCompleteEvent30,favorableCompleteEvent31,favorableCompleteEvent32,favorableCompleteEvent33,favorableCompleteEvent34,favorableCompleteEvent35,favorableCompleteEvent36,taskReward]
    <;> norm_num
  have hp : rawVisits favorableCompleteS37Before [.query 1] = 29 := by decide
  have hn : rawVisits favorableCompleteS37Before ([.query 1]++[.hydeRetriever 0]) = 8 := by decide
  have hz : (controlPenalty savedCref uniformQuoteError unitRoleUnused .complete) favorableCompleteS37Before [.query 1] (.hydeRetriever 0) = 0 := by
    apply control_penalty_empty_of_prior_terminal .complete savedCref uniformQuoteError favorableCompleteS37Before [.query 1] (.hydeRetriever 0) 1 (by decide)
    · decide
    · decide
  unfold indexScore
  rw [hs,hp,hn,hz]
  simp only [BackupStat.mean]
  norm_num

theorem favorableCompleteS37D1I2 : indexScore (7/5) (controlPenalty savedCref uniformQuoteError unitRoleUnused .complete) favorableCompleteS37Before [.query 1] (.hydeRetriever 2) = treeIndex ((0/1)/8) (7/5) 0 29 8 := by
  have hs : replayBackup favorableCompleteS37Before emptyStatistics ([.query 1]++[.hydeRetriever 2]) = ⟨8,(0/1)⟩ := by
    rw [replayBackup_empty_closed_form]
    simp +decide [backedEvents,favorableCompleteS37Before,favorableCompleteProposal,favorableCompleteEvent1,favorableCompleteEvent2,favorableCompleteEvent3,favorableCompleteEvent4,favorableCompleteEvent5,favorableCompleteEvent6,favorableCompleteEvent7,favorableCompleteEvent8,favorableCompleteEvent9,favorableCompleteEvent10,favorableCompleteEvent11,favorableCompleteEvent12,favorableCompleteEvent13,favorableCompleteEvent14,favorableCompleteEvent15,favorableCompleteEvent16,favorableCompleteEvent17,favorableCompleteEvent18,favorableCompleteEvent19,favorableCompleteEvent20,favorableCompleteEvent21,favorableCompleteEvent22,favorableCompleteEvent23,favorableCompleteEvent24,favorableCompleteEvent25,favorableCompleteEvent26,favorableCompleteEvent27,favorableCompleteEvent28,favorableCompleteEvent29,favorableCompleteEvent30,favorableCompleteEvent31,favorableCompleteEvent32,favorableCompleteEvent33,favorableCompleteEvent34,favorableCompleteEvent35,favorableCompleteEvent36,taskReward]
    <;> norm_num
  have hp : rawVisits favorableCompleteS37Before [.query 1] = 29 := by decide
  have hn : rawVisits favorableCompleteS37Before ([.query 1]++[.hydeRetriever 2]) = 8 := by decide
  have hz : (controlPenalty savedCref uniformQuoteError unitRoleUnused .complete) favorableCompleteS37Before [.query 1] (.hydeRetriever 2) = 0 := by
    apply control_penalty_empty_of_prior_terminal .complete savedCref uniformQuoteError favorableCompleteS37Before [.query 1] (.hydeRetriever 2) 10 (by decide)
    · decide
    · decide
  unfold indexScore
  rw [hs,hp,hn,hz]
  simp only [BackupStat.mean]
  norm_num

theorem favorableCompleteS37D1Cmp0 : indexScore (7/5) (controlPenalty savedCref uniformQuoteError unitRoleUnused .complete) favorableCompleteS37Before [.query 1] (.hydeRetriever 1) < indexScore (7/5) (controlPenalty savedCref uniformQuoteError unitRoleUnused .complete) favorableCompleteS37Before [.query 1] (.hydeRetriever 0) := by
  rw [favorableCompleteS37D1I0,favorableCompleteS37D1I1]
  have h := index_strict_order_from_intervals ((0/1)/8) ((3/2)/12) 0 0 (912849/1000000) (9316727/12500000)
    (treeBonus (7/5) 29 8) (treeBonus (7/5) 29 12)
    (trajectory_bonus_29_8).1 (trajectory_bonus_29_12).2 (by norm_num)
  simpa only [treeIndex,sub_zero] using h

theorem favorableCompleteS37D1Cmp2 : indexScore (7/5) (controlPenalty savedCref uniformQuoteError unitRoleUnused .complete) favorableCompleteS37Before [.query 1] (.hydeRetriever 2) ≤ indexScore (7/5) (controlPenalty savedCref uniformQuoteError unitRoleUnused .complete) favorableCompleteS37Before [.query 1] (.hydeRetriever 0) := by
  rw [favorableCompleteS37D1I2,favorableCompleteS37D1I1]

theorem favorableCompleteS37Choice1 : nativeFirstChoice (indexScore (7/5) (controlPenalty savedCref uniformQuoteError unitRoleUnused .complete) favorableCompleteS37Before [.query 1]) favorableCompleteS37Before [.query 1] = .hydeRetriever 0 := by
  apply visited_choice_from_ordered_certificate _ _ [.query 1] [.hydeRetriever 1] [.hydeRetriever 2] (.hydeRetriever 0) (by decide)
  · intro a ha
    have ho : orderedLegalAvailable [.query 1] = [.hydeRetriever 1,.hydeRetriever 0,.hydeRetriever 2] := by decide
    rw [ho] at ha
    simp only [List.mem_cons,List.not_mem_nil,or_false] at ha
    rcases ha with rfl | rfl | rfl <;> decide
  · intro a ha
    simp only [List.mem_cons,List.not_mem_nil,or_false] at ha
    rcases ha with rfl
    · exact favorableCompleteS37D1Cmp0
  · intro a ha
    simp only [List.mem_cons,List.not_mem_nil,or_false] at ha
    rcases ha with rfl
    · exact favorableCompleteS37D1Cmp2

theorem favorableCompleteS37D2I0 : indexScore (7/5) (controlPenalty savedCref uniformQuoteError unitRoleUnused .complete) favorableCompleteS37Before [.query 1,.hydeRetriever 0] (.selection 1) = treeIndex ((0/1)/2) (7/5) 0 8 2 := by
  have hs : replayBackup favorableCompleteS37Before emptyStatistics ([.query 1,.hydeRetriever 0]++[.selection 1]) = ⟨2,(0/1)⟩ := by
    rw [replayBackup_empty_closed_form]
    simp +decide [backedEvents,favorableCompleteS37Before,favorableCompleteProposal,favorableCompleteEvent1,favorableCompleteEvent2,favorableCompleteEvent3,favorableCompleteEvent4,favorableCompleteEvent5,favorableCompleteEvent6,favorableCompleteEvent7,favorableCompleteEvent8,favorableCompleteEvent9,favorableCompleteEvent10,favorableCompleteEvent11,favorableCompleteEvent12,favorableCompleteEvent13,favorableCompleteEvent14,favorableCompleteEvent15,favorableCompleteEvent16,favorableCompleteEvent17,favorableCompleteEvent18,favorableCompleteEvent19,favorableCompleteEvent20,favorableCompleteEvent21,favorableCompleteEvent22,favorableCompleteEvent23,favorableCompleteEvent24,favorableCompleteEvent25,favorableCompleteEvent26,favorableCompleteEvent27,favorableCompleteEvent28,favorableCompleteEvent29,favorableCompleteEvent30,favorableCompleteEvent31,favorableCompleteEvent32,favorableCompleteEvent33,favorableCompleteEvent34,favorableCompleteEvent35,favorableCompleteEvent36,taskReward]
    <;> norm_num
  have hp : rawVisits favorableCompleteS37Before [.query 1,.hydeRetriever 0] = 8 := by decide
  have hn : rawVisits favorableCompleteS37Before ([.query 1,.hydeRetriever 0]++[.selection 1]) = 2 := by decide
  have hz : (controlPenalty savedCref uniformQuoteError unitRoleUnused .complete) favorableCompleteS37Before [.query 1,.hydeRetriever 0] (.selection 1) = 0 := by
    apply control_penalty_empty_of_prior_terminal .complete savedCref uniformQuoteError favorableCompleteS37Before [.query 1,.hydeRetriever 0] (.selection 1) 16 (by decide)
    · decide
    · decide
  unfold indexScore
  rw [hs,hp,hn,hz]
  simp only [BackupStat.mean]
  norm_num

theorem favorableCompleteS37D2I1 : indexScore (7/5) (controlPenalty savedCref uniformQuoteError unitRoleUnused .complete) favorableCompleteS37Before [.query 1,.hydeRetriever 0] (.selection 2) = treeIndex ((0/1)/2) (7/5) 0 8 2 := by
  have hs : replayBackup favorableCompleteS37Before emptyStatistics ([.query 1,.hydeRetriever 0]++[.selection 2]) = ⟨2,(0/1)⟩ := by
    rw [replayBackup_empty_closed_form]
    simp +decide [backedEvents,favorableCompleteS37Before,favorableCompleteProposal,favorableCompleteEvent1,favorableCompleteEvent2,favorableCompleteEvent3,favorableCompleteEvent4,favorableCompleteEvent5,favorableCompleteEvent6,favorableCompleteEvent7,favorableCompleteEvent8,favorableCompleteEvent9,favorableCompleteEvent10,favorableCompleteEvent11,favorableCompleteEvent12,favorableCompleteEvent13,favorableCompleteEvent14,favorableCompleteEvent15,favorableCompleteEvent16,favorableCompleteEvent17,favorableCompleteEvent18,favorableCompleteEvent19,favorableCompleteEvent20,favorableCompleteEvent21,favorableCompleteEvent22,favorableCompleteEvent23,favorableCompleteEvent24,favorableCompleteEvent25,favorableCompleteEvent26,favorableCompleteEvent27,favorableCompleteEvent28,favorableCompleteEvent29,favorableCompleteEvent30,favorableCompleteEvent31,favorableCompleteEvent32,favorableCompleteEvent33,favorableCompleteEvent34,favorableCompleteEvent35,favorableCompleteEvent36,taskReward]
    <;> norm_num
  have hp : rawVisits favorableCompleteS37Before [.query 1,.hydeRetriever 0] = 8 := by decide
  have hn : rawVisits favorableCompleteS37Before ([.query 1,.hydeRetriever 0]++[.selection 2]) = 2 := by decide
  have hz : (controlPenalty savedCref uniformQuoteError unitRoleUnused .complete) favorableCompleteS37Before [.query 1,.hydeRetriever 0] (.selection 2) = 0 := by
    apply control_penalty_empty_of_prior_terminal .complete savedCref uniformQuoteError favorableCompleteS37Before [.query 1,.hydeRetriever 0] (.selection 2) 19 (by decide)
    · decide
    · decide
  unfold indexScore
  rw [hs,hp,hn,hz]
  simp only [BackupStat.mean]
  norm_num

theorem favorableCompleteS37D2I2 : indexScore (7/5) (controlPenalty savedCref uniformQuoteError unitRoleUnused .complete) favorableCompleteS37Before [.query 1,.hydeRetriever 0] (.selection 3) = treeIndex ((0/1)/2) (7/5) 0 8 2 := by
  have hs : replayBackup favorableCompleteS37Before emptyStatistics ([.query 1,.hydeRetriever 0]++[.selection 3]) = ⟨2,(0/1)⟩ := by
    rw [replayBackup_empty_closed_form]
    simp +decide [backedEvents,favorableCompleteS37Before,favorableCompleteProposal,favorableCompleteEvent1,favorableCompleteEvent2,favorableCompleteEvent3,favorableCompleteEvent4,favorableCompleteEvent5,favorableCompleteEvent6,favorableCompleteEvent7,favorableCompleteEvent8,favorableCompleteEvent9,favorableCompleteEvent10,favorableCompleteEvent11,favorableCompleteEvent12,favorableCompleteEvent13,favorableCompleteEvent14,favorableCompleteEvent15,favorableCompleteEvent16,favorableCompleteEvent17,favorableCompleteEvent18,favorableCompleteEvent19,favorableCompleteEvent20,favorableCompleteEvent21,favorableCompleteEvent22,favorableCompleteEvent23,favorableCompleteEvent24,favorableCompleteEvent25,favorableCompleteEvent26,favorableCompleteEvent27,favorableCompleteEvent28,favorableCompleteEvent29,favorableCompleteEvent30,favorableCompleteEvent31,favorableCompleteEvent32,favorableCompleteEvent33,favorableCompleteEvent34,favorableCompleteEvent35,favorableCompleteEvent36,taskReward]
    <;> norm_num
  have hp : rawVisits favorableCompleteS37Before [.query 1,.hydeRetriever 0] = 8 := by decide
  have hn : rawVisits favorableCompleteS37Before ([.query 1,.hydeRetriever 0]++[.selection 3]) = 2 := by decide
  have hz : (controlPenalty savedCref uniformQuoteError unitRoleUnused .complete) favorableCompleteS37Before [.query 1,.hydeRetriever 0] (.selection 3) = 0 := by
    apply control_penalty_empty_of_prior_terminal .complete savedCref uniformQuoteError favorableCompleteS37Before [.query 1,.hydeRetriever 0] (.selection 3) 23 (by decide)
    · decide
    · decide
  unfold indexScore
  rw [hs,hp,hn,hz]
  simp only [BackupStat.mean]
  norm_num

theorem favorableCompleteS37D2I3 : indexScore (7/5) (controlPenalty savedCref uniformQuoteError unitRoleUnused .complete) favorableCompleteS37Before [.query 1,.hydeRetriever 0] (.selection 0) = treeIndex ((0/1)/1) (7/5) 0 8 1 := by
  have hs : replayBackup favorableCompleteS37Before emptyStatistics ([.query 1,.hydeRetriever 0]++[.selection 0]) = ⟨1,(0/1)⟩ := by
    rw [replayBackup_empty_closed_form]
    simp +decide [backedEvents,favorableCompleteS37Before,favorableCompleteProposal,favorableCompleteEvent1,favorableCompleteEvent2,favorableCompleteEvent3,favorableCompleteEvent4,favorableCompleteEvent5,favorableCompleteEvent6,favorableCompleteEvent7,favorableCompleteEvent8,favorableCompleteEvent9,favorableCompleteEvent10,favorableCompleteEvent11,favorableCompleteEvent12,favorableCompleteEvent13,favorableCompleteEvent14,favorableCompleteEvent15,favorableCompleteEvent16,favorableCompleteEvent17,favorableCompleteEvent18,favorableCompleteEvent19,favorableCompleteEvent20,favorableCompleteEvent21,favorableCompleteEvent22,favorableCompleteEvent23,favorableCompleteEvent24,favorableCompleteEvent25,favorableCompleteEvent26,favorableCompleteEvent27,favorableCompleteEvent28,favorableCompleteEvent29,favorableCompleteEvent30,favorableCompleteEvent31,favorableCompleteEvent32,favorableCompleteEvent33,favorableCompleteEvent34,favorableCompleteEvent35,favorableCompleteEvent36,taskReward]
    <;> norm_num
  have hp : rawVisits favorableCompleteS37Before [.query 1,.hydeRetriever 0] = 8 := by decide
  have hn : rawVisits favorableCompleteS37Before ([.query 1,.hydeRetriever 0]++[.selection 0]) = 1 := by decide
  have hz : (controlPenalty savedCref uniformQuoteError unitRoleUnused .complete) favorableCompleteS37Before [.query 1,.hydeRetriever 0] (.selection 0) = 0 := by
    apply control_penalty_empty_of_prior_terminal .complete savedCref uniformQuoteError favorableCompleteS37Before [.query 1,.hydeRetriever 0] (.selection 0) 1 (by decide)
    · decide
    · decide
  unfold indexScore
  rw [hs,hp,hn,hz]
  simp only [BackupStat.mean]
  norm_num

theorem favorableCompleteS37D2Cmp0 : indexScore (7/5) (controlPenalty savedCref uniformQuoteError unitRoleUnused .complete) favorableCompleteS37Before [.query 1,.hydeRetriever 0] (.selection 1) < indexScore (7/5) (controlPenalty savedCref uniformQuoteError unitRoleUnused .complete) favorableCompleteS37Before [.query 1,.hydeRetriever 0] (.selection 0) := by
  rw [favorableCompleteS37D2I0,favorableCompleteS37D2I3]
  have h := index_strict_order_from_intervals ((0/1)/1) ((0/1)/2) 0 0 (103761259/50000000) (1146411/781250)
    (treeBonus (7/5) 8 1) (treeBonus (7/5) 8 2)
    (trajectory_bonus_8_1).1 (trajectory_bonus_8_2).2 (by norm_num)
  simpa only [treeIndex,sub_zero] using h

theorem favorableCompleteS37D2Cmp1 : indexScore (7/5) (controlPenalty savedCref uniformQuoteError unitRoleUnused .complete) favorableCompleteS37Before [.query 1,.hydeRetriever 0] (.selection 2) < indexScore (7/5) (controlPenalty savedCref uniformQuoteError unitRoleUnused .complete) favorableCompleteS37Before [.query 1,.hydeRetriever 0] (.selection 0) := by
  rw [favorableCompleteS37D2I1,favorableCompleteS37D2I3]
  have h := index_strict_order_from_intervals ((0/1)/1) ((0/1)/2) 0 0 (103761259/50000000) (1146411/781250)
    (treeBonus (7/5) 8 1) (treeBonus (7/5) 8 2)
    (trajectory_bonus_8_1).1 (trajectory_bonus_8_2).2 (by norm_num)
  simpa only [treeIndex,sub_zero] using h

theorem favorableCompleteS37D2Cmp2 : indexScore (7/5) (controlPenalty savedCref uniformQuoteError unitRoleUnused .complete) favorableCompleteS37Before [.query 1,.hydeRetriever 0] (.selection 3) < indexScore (7/5) (controlPenalty savedCref uniformQuoteError unitRoleUnused .complete) favorableCompleteS37Before [.query 1,.hydeRetriever 0] (.selection 0) := by
  rw [favorableCompleteS37D2I2,favorableCompleteS37D2I3]
  have h := index_strict_order_from_intervals ((0/1)/1) ((0/1)/2) 0 0 (103761259/50000000) (1146411/781250)
    (treeBonus (7/5) 8 1) (treeBonus (7/5) 8 2)
    (trajectory_bonus_8_1).1 (trajectory_bonus_8_2).2 (by norm_num)
  simpa only [treeIndex,sub_zero] using h

theorem favorableCompleteS37Choice2 : nativeFirstChoice (indexScore (7/5) (controlPenalty savedCref uniformQuoteError unitRoleUnused .complete) favorableCompleteS37Before [.query 1,.hydeRetriever 0]) favorableCompleteS37Before [.query 1,.hydeRetriever 0] = .selection 0 := by
  apply visited_choice_from_ordered_certificate _ _ [.query 1,.hydeRetriever 0] [.selection 1,.selection 2,.selection 3] [] (.selection 0) (by decide)
  · intro a ha
    have ho : orderedLegalAvailable [.query 1,.hydeRetriever 0] = [.selection 1,.selection 2,.selection 3,.selection 0] := by decide
    rw [ho] at ha
    simp only [List.mem_cons,List.not_mem_nil,or_false] at ha
    rcases ha with rfl | rfl | rfl | rfl <;> decide
  · intro a ha
    simp only [List.mem_cons,List.not_mem_nil,or_false] at ha
    rcases ha with rfl | rfl | rfl
    · exact favorableCompleteS37D2Cmp0
    · exact favorableCompleteS37D2Cmp1
    · exact favorableCompleteS37D2Cmp2
  · simp

theorem favorableCompleteS37ActualEvent : nativeEvent budgetTape (7/5) (controlPenalty savedCref uniformQuoteError unitRoleUnused .complete)
    (taskReward false (2/5) (1/2)) favorableCompleteS37Before = favorableCompleteEvent37 := by
  have hs0 := native_select_existing_step budgetTape (7/5) (controlPenalty savedCref uniformQuoteError unitRoleUnused .complete) favorableCompleteS37Before 8 [] (.query 1)
    (by decide) (by decide) favorableCompleteS37Choice0
  have hs1 := native_select_existing_step budgetTape (7/5) (controlPenalty savedCref uniformQuoteError unitRoleUnused .complete) favorableCompleteS37Before 7 [.query 1] (.hydeRetriever 0)
    (by decide) (by decide) favorableCompleteS37Choice1
  have hs2 := native_select_existing_step budgetTape (7/5) (controlPenalty savedCref uniformQuoteError unitRoleUnused .complete) favorableCompleteS37Before 6 [.query 1,.hydeRetriever 0] (.selection 0)
    (by decide) (by decide) favorableCompleteS37Choice2
  have hnew := native_select_new_step budgetTape (7/5) (controlPenalty savedCref uniformQuoteError unitRoleUnused .complete) favorableCompleteS37Before 5 [.query 1,.hydeRetriever 0,.selection 0]
    [.width 3,.width 0,.width 1,.width 2] (.width 0) (by decide) (by decide) (by decide) (by decide)
  have hs : nativeSelect budgetTape (7/5) (controlPenalty savedCref uniformQuoteError unitRoleUnused .complete) favorableCompleteS37Before 9 [] = [.query 1,.hydeRetriever 0,.selection 0,.width 0] := by
    rw [hs0]
    change nativeSelect budgetTape (7/5) (controlPenalty savedCref uniformQuoteError unitRoleUnused .complete) favorableCompleteS37Before 8 [.query 1] = _
    rw [hs1]
    change nativeSelect budgetTape (7/5) (controlPenalty savedCref uniformQuoteError unitRoleUnused .complete) favorableCompleteS37Before 7 [.query 1,.hydeRetriever 0] = _
    rw [hs2]
    change nativeSelect budgetTape (7/5) (controlPenalty savedCref uniformQuoteError unitRoleUnused .complete) favorableCompleteS37Before 6 [.query 1,.hydeRetriever 0,.selection 0] = _
    rw [hnew] <;> rfl
  have hr : repairedRollout budgetTape favorableCompleteS37Before 9 [.query 1,.hydeRetriever 0,.selection 0,.width 0] = [.query 1,.hydeRetriever 0,.selection 0,.width 0,.stop,.reranker 0,.topm 0,.context 0,.answer 0] := by decide
  simp only [nativeEvent,hs,hr]
  rfl

def favorableCompleteS38Before := favorableCompleteProposal.take 37

theorem favorableCompleteS38Choice0 : nativeFirstChoice (indexScore (7/5) (controlPenalty savedCref uniformQuoteError unitRoleUnused .complete) favorableCompleteS38Before []) favorableCompleteS38Before [] = .query 1 := by
  apply complete_root_from_physical_gap favorableCompleteS38Before (favorableComplete_prefix_rewards 37) (by decide)
  · intro q; fin_cases q <;> decide
  · exact AgentUCTNextExact.favorable_complete_hyde_root_suffix_empty 37 (by omega)
  · intro q hq
    exact AgentUCTNextExact.favorable_complete_normal_root_physical_quote_exact 37 (by omega) q hq

theorem favorableCompleteS38D1I0 : indexScore (7/5) (controlPenalty savedCref uniformQuoteError unitRoleUnused .complete) favorableCompleteS38Before [.query 1] (.hydeRetriever 1) = treeIndex ((3/2)/12) (7/5) 0 30 12 := by
  have hs : replayBackup favorableCompleteS38Before emptyStatistics ([.query 1]++[.hydeRetriever 1]) = ⟨12,(3/2)⟩ := by
    rw [replayBackup_empty_closed_form]
    simp +decide [backedEvents,favorableCompleteS38Before,favorableCompleteProposal,favorableCompleteEvent1,favorableCompleteEvent2,favorableCompleteEvent3,favorableCompleteEvent4,favorableCompleteEvent5,favorableCompleteEvent6,favorableCompleteEvent7,favorableCompleteEvent8,favorableCompleteEvent9,favorableCompleteEvent10,favorableCompleteEvent11,favorableCompleteEvent12,favorableCompleteEvent13,favorableCompleteEvent14,favorableCompleteEvent15,favorableCompleteEvent16,favorableCompleteEvent17,favorableCompleteEvent18,favorableCompleteEvent19,favorableCompleteEvent20,favorableCompleteEvent21,favorableCompleteEvent22,favorableCompleteEvent23,favorableCompleteEvent24,favorableCompleteEvent25,favorableCompleteEvent26,favorableCompleteEvent27,favorableCompleteEvent28,favorableCompleteEvent29,favorableCompleteEvent30,favorableCompleteEvent31,favorableCompleteEvent32,favorableCompleteEvent33,favorableCompleteEvent34,favorableCompleteEvent35,favorableCompleteEvent36,favorableCompleteEvent37,taskReward]
    <;> norm_num
  have hp : rawVisits favorableCompleteS38Before [.query 1] = 30 := by decide
  have hn : rawVisits favorableCompleteS38Before ([.query 1]++[.hydeRetriever 1]) = 12 := by decide
  have hz : (controlPenalty savedCref uniformQuoteError unitRoleUnused .complete) favorableCompleteS38Before [.query 1] (.hydeRetriever 1) = 0 := by
    apply control_penalty_empty_of_prior_terminal .complete savedCref uniformQuoteError favorableCompleteS38Before [.query 1] (.hydeRetriever 1) 8 (by decide)
    · decide
    · decide
  unfold indexScore
  rw [hs,hp,hn,hz]
  simp only [BackupStat.mean]
  norm_num

theorem favorableCompleteS38D1I1 : indexScore (7/5) (controlPenalty savedCref uniformQuoteError unitRoleUnused .complete) favorableCompleteS38Before [.query 1] (.hydeRetriever 0) = treeIndex ((0/1)/9) (7/5) 0 30 9 := by
  have hs : replayBackup favorableCompleteS38Before emptyStatistics ([.query 1]++[.hydeRetriever 0]) = ⟨9,(0/1)⟩ := by
    rw [replayBackup_empty_closed_form]
    simp +decide [backedEvents,favorableCompleteS38Before,favorableCompleteProposal,favorableCompleteEvent1,favorableCompleteEvent2,favorableCompleteEvent3,favorableCompleteEvent4,favorableCompleteEvent5,favorableCompleteEvent6,favorableCompleteEvent7,favorableCompleteEvent8,favorableCompleteEvent9,favorableCompleteEvent10,favorableCompleteEvent11,favorableCompleteEvent12,favorableCompleteEvent13,favorableCompleteEvent14,favorableCompleteEvent15,favorableCompleteEvent16,favorableCompleteEvent17,favorableCompleteEvent18,favorableCompleteEvent19,favorableCompleteEvent20,favorableCompleteEvent21,favorableCompleteEvent22,favorableCompleteEvent23,favorableCompleteEvent24,favorableCompleteEvent25,favorableCompleteEvent26,favorableCompleteEvent27,favorableCompleteEvent28,favorableCompleteEvent29,favorableCompleteEvent30,favorableCompleteEvent31,favorableCompleteEvent32,favorableCompleteEvent33,favorableCompleteEvent34,favorableCompleteEvent35,favorableCompleteEvent36,favorableCompleteEvent37,taskReward]
    <;> norm_num
  have hp : rawVisits favorableCompleteS38Before [.query 1] = 30 := by decide
  have hn : rawVisits favorableCompleteS38Before ([.query 1]++[.hydeRetriever 0]) = 9 := by decide
  have hz : (controlPenalty savedCref uniformQuoteError unitRoleUnused .complete) favorableCompleteS38Before [.query 1] (.hydeRetriever 0) = 0 := by
    apply control_penalty_empty_of_prior_terminal .complete savedCref uniformQuoteError favorableCompleteS38Before [.query 1] (.hydeRetriever 0) 1 (by decide)
    · decide
    · decide
  unfold indexScore
  rw [hs,hp,hn,hz]
  simp only [BackupStat.mean]
  norm_num

theorem favorableCompleteS38D1I2 : indexScore (7/5) (controlPenalty savedCref uniformQuoteError unitRoleUnused .complete) favorableCompleteS38Before [.query 1] (.hydeRetriever 2) = treeIndex ((0/1)/8) (7/5) 0 30 8 := by
  have hs : replayBackup favorableCompleteS38Before emptyStatistics ([.query 1]++[.hydeRetriever 2]) = ⟨8,(0/1)⟩ := by
    rw [replayBackup_empty_closed_form]
    simp +decide [backedEvents,favorableCompleteS38Before,favorableCompleteProposal,favorableCompleteEvent1,favorableCompleteEvent2,favorableCompleteEvent3,favorableCompleteEvent4,favorableCompleteEvent5,favorableCompleteEvent6,favorableCompleteEvent7,favorableCompleteEvent8,favorableCompleteEvent9,favorableCompleteEvent10,favorableCompleteEvent11,favorableCompleteEvent12,favorableCompleteEvent13,favorableCompleteEvent14,favorableCompleteEvent15,favorableCompleteEvent16,favorableCompleteEvent17,favorableCompleteEvent18,favorableCompleteEvent19,favorableCompleteEvent20,favorableCompleteEvent21,favorableCompleteEvent22,favorableCompleteEvent23,favorableCompleteEvent24,favorableCompleteEvent25,favorableCompleteEvent26,favorableCompleteEvent27,favorableCompleteEvent28,favorableCompleteEvent29,favorableCompleteEvent30,favorableCompleteEvent31,favorableCompleteEvent32,favorableCompleteEvent33,favorableCompleteEvent34,favorableCompleteEvent35,favorableCompleteEvent36,favorableCompleteEvent37,taskReward]
    <;> norm_num
  have hp : rawVisits favorableCompleteS38Before [.query 1] = 30 := by decide
  have hn : rawVisits favorableCompleteS38Before ([.query 1]++[.hydeRetriever 2]) = 8 := by decide
  have hz : (controlPenalty savedCref uniformQuoteError unitRoleUnused .complete) favorableCompleteS38Before [.query 1] (.hydeRetriever 2) = 0 := by
    apply control_penalty_empty_of_prior_terminal .complete savedCref uniformQuoteError favorableCompleteS38Before [.query 1] (.hydeRetriever 2) 10 (by decide)
    · decide
    · decide
  unfold indexScore
  rw [hs,hp,hn,hz]
  simp only [BackupStat.mean]
  norm_num

theorem favorableCompleteS38D1Cmp0 : indexScore (7/5) (controlPenalty savedCref uniformQuoteError unitRoleUnused .complete) favorableCompleteS38Before [.query 1] (.hydeRetriever 1) < indexScore (7/5) (controlPenalty savedCref uniformQuoteError unitRoleUnused .complete) favorableCompleteS38Before [.query 1] (.hydeRetriever 2) := by
  rw [favorableCompleteS38D1I0,favorableCompleteS38D1I2]
  have h := index_strict_order_from_intervals ((0/1)/8) ((3/2)/12) 0 0 (9172387/10000000) (7489223/10000000)
    (treeBonus (7/5) 30 8) (treeBonus (7/5) 30 12)
    (trajectory_bonus_30_8).1 (trajectory_bonus_30_12).2 (by norm_num)
  simpa only [treeIndex,sub_zero] using h

theorem favorableCompleteS38D1Cmp1 : indexScore (7/5) (controlPenalty savedCref uniformQuoteError unitRoleUnused .complete) favorableCompleteS38Before [.query 1] (.hydeRetriever 0) < indexScore (7/5) (controlPenalty savedCref uniformQuoteError unitRoleUnused .complete) favorableCompleteS38Before [.query 1] (.hydeRetriever 2) := by
  rw [favorableCompleteS38D1I1,favorableCompleteS38D1I2]
  have h := index_strict_order_from_intervals ((0/1)/8) ((0/1)/9) 0 0 (9172387/10000000) (43239049/50000000)
    (treeBonus (7/5) 30 8) (treeBonus (7/5) 30 9)
    (trajectory_bonus_30_8).1 (trajectory_bonus_30_9).2 (by norm_num)
  simpa only [treeIndex,sub_zero] using h

theorem favorableCompleteS38Choice1 : nativeFirstChoice (indexScore (7/5) (controlPenalty savedCref uniformQuoteError unitRoleUnused .complete) favorableCompleteS38Before [.query 1]) favorableCompleteS38Before [.query 1] = .hydeRetriever 2 := by
  apply visited_choice_from_ordered_certificate _ _ [.query 1] [.hydeRetriever 1,.hydeRetriever 0] [] (.hydeRetriever 2) (by decide)
  · intro a ha
    have ho : orderedLegalAvailable [.query 1] = [.hydeRetriever 1,.hydeRetriever 0,.hydeRetriever 2] := by decide
    rw [ho] at ha
    simp only [List.mem_cons,List.not_mem_nil,or_false] at ha
    rcases ha with rfl | rfl | rfl <;> decide
  · intro a ha
    simp only [List.mem_cons,List.not_mem_nil,or_false] at ha
    rcases ha with rfl | rfl
    · exact favorableCompleteS38D1Cmp0
    · exact favorableCompleteS38D1Cmp1
  · simp

theorem favorableCompleteS38D2I0 : indexScore (7/5) (controlPenalty savedCref uniformQuoteError unitRoleUnused .complete) favorableCompleteS38Before [.query 1,.hydeRetriever 2] (.selection 1) = treeIndex ((0/1)/2) (7/5) 0 8 2 := by
  have hs : replayBackup favorableCompleteS38Before emptyStatistics ([.query 1,.hydeRetriever 2]++[.selection 1]) = ⟨2,(0/1)⟩ := by
    rw [replayBackup_empty_closed_form]
    simp +decide [backedEvents,favorableCompleteS38Before,favorableCompleteProposal,favorableCompleteEvent1,favorableCompleteEvent2,favorableCompleteEvent3,favorableCompleteEvent4,favorableCompleteEvent5,favorableCompleteEvent6,favorableCompleteEvent7,favorableCompleteEvent8,favorableCompleteEvent9,favorableCompleteEvent10,favorableCompleteEvent11,favorableCompleteEvent12,favorableCompleteEvent13,favorableCompleteEvent14,favorableCompleteEvent15,favorableCompleteEvent16,favorableCompleteEvent17,favorableCompleteEvent18,favorableCompleteEvent19,favorableCompleteEvent20,favorableCompleteEvent21,favorableCompleteEvent22,favorableCompleteEvent23,favorableCompleteEvent24,favorableCompleteEvent25,favorableCompleteEvent26,favorableCompleteEvent27,favorableCompleteEvent28,favorableCompleteEvent29,favorableCompleteEvent30,favorableCompleteEvent31,favorableCompleteEvent32,favorableCompleteEvent33,favorableCompleteEvent34,favorableCompleteEvent35,favorableCompleteEvent36,favorableCompleteEvent37,taskReward]
    <;> norm_num
  have hp : rawVisits favorableCompleteS38Before [.query 1,.hydeRetriever 2] = 8 := by decide
  have hn : rawVisits favorableCompleteS38Before ([.query 1,.hydeRetriever 2]++[.selection 1]) = 2 := by decide
  have hz : (controlPenalty savedCref uniformQuoteError unitRoleUnused .complete) favorableCompleteS38Before [.query 1,.hydeRetriever 2] (.selection 1) = 0 := by
    apply control_penalty_empty_of_prior_terminal .complete savedCref uniformQuoteError favorableCompleteS38Before [.query 1,.hydeRetriever 2] (.selection 1) 17 (by decide)
    · decide
    · decide
  unfold indexScore
  rw [hs,hp,hn,hz]
  simp only [BackupStat.mean]
  norm_num

theorem favorableCompleteS38D2I1 : indexScore (7/5) (controlPenalty savedCref uniformQuoteError unitRoleUnused .complete) favorableCompleteS38Before [.query 1,.hydeRetriever 2] (.selection 2) = treeIndex ((0/1)/2) (7/5) 0 8 2 := by
  have hs : replayBackup favorableCompleteS38Before emptyStatistics ([.query 1,.hydeRetriever 2]++[.selection 2]) = ⟨2,(0/1)⟩ := by
    rw [replayBackup_empty_closed_form]
    simp +decide [backedEvents,favorableCompleteS38Before,favorableCompleteProposal,favorableCompleteEvent1,favorableCompleteEvent2,favorableCompleteEvent3,favorableCompleteEvent4,favorableCompleteEvent5,favorableCompleteEvent6,favorableCompleteEvent7,favorableCompleteEvent8,favorableCompleteEvent9,favorableCompleteEvent10,favorableCompleteEvent11,favorableCompleteEvent12,favorableCompleteEvent13,favorableCompleteEvent14,favorableCompleteEvent15,favorableCompleteEvent16,favorableCompleteEvent17,favorableCompleteEvent18,favorableCompleteEvent19,favorableCompleteEvent20,favorableCompleteEvent21,favorableCompleteEvent22,favorableCompleteEvent23,favorableCompleteEvent24,favorableCompleteEvent25,favorableCompleteEvent26,favorableCompleteEvent27,favorableCompleteEvent28,favorableCompleteEvent29,favorableCompleteEvent30,favorableCompleteEvent31,favorableCompleteEvent32,favorableCompleteEvent33,favorableCompleteEvent34,favorableCompleteEvent35,favorableCompleteEvent36,favorableCompleteEvent37,taskReward]
    <;> norm_num
  have hp : rawVisits favorableCompleteS38Before [.query 1,.hydeRetriever 2] = 8 := by decide
  have hn : rawVisits favorableCompleteS38Before ([.query 1,.hydeRetriever 2]++[.selection 2]) = 2 := by decide
  have hz : (controlPenalty savedCref uniformQuoteError unitRoleUnused .complete) favorableCompleteS38Before [.query 1,.hydeRetriever 2] (.selection 2) = 0 := by
    apply control_penalty_empty_of_prior_terminal .complete savedCref uniformQuoteError favorableCompleteS38Before [.query 1,.hydeRetriever 2] (.selection 2) 20 (by decide)
    · decide
    · decide
  unfold indexScore
  rw [hs,hp,hn,hz]
  simp only [BackupStat.mean]
  norm_num

theorem favorableCompleteS38D2I2 : indexScore (7/5) (controlPenalty savedCref uniformQuoteError unitRoleUnused .complete) favorableCompleteS38Before [.query 1,.hydeRetriever 2] (.selection 3) = treeIndex ((0/1)/2) (7/5) 0 8 2 := by
  have hs : replayBackup favorableCompleteS38Before emptyStatistics ([.query 1,.hydeRetriever 2]++[.selection 3]) = ⟨2,(0/1)⟩ := by
    rw [replayBackup_empty_closed_form]
    simp +decide [backedEvents,favorableCompleteS38Before,favorableCompleteProposal,favorableCompleteEvent1,favorableCompleteEvent2,favorableCompleteEvent3,favorableCompleteEvent4,favorableCompleteEvent5,favorableCompleteEvent6,favorableCompleteEvent7,favorableCompleteEvent8,favorableCompleteEvent9,favorableCompleteEvent10,favorableCompleteEvent11,favorableCompleteEvent12,favorableCompleteEvent13,favorableCompleteEvent14,favorableCompleteEvent15,favorableCompleteEvent16,favorableCompleteEvent17,favorableCompleteEvent18,favorableCompleteEvent19,favorableCompleteEvent20,favorableCompleteEvent21,favorableCompleteEvent22,favorableCompleteEvent23,favorableCompleteEvent24,favorableCompleteEvent25,favorableCompleteEvent26,favorableCompleteEvent27,favorableCompleteEvent28,favorableCompleteEvent29,favorableCompleteEvent30,favorableCompleteEvent31,favorableCompleteEvent32,favorableCompleteEvent33,favorableCompleteEvent34,favorableCompleteEvent35,favorableCompleteEvent36,favorableCompleteEvent37,taskReward]
    <;> norm_num
  have hp : rawVisits favorableCompleteS38Before [.query 1,.hydeRetriever 2] = 8 := by decide
  have hn : rawVisits favorableCompleteS38Before ([.query 1,.hydeRetriever 2]++[.selection 3]) = 2 := by decide
  have hz : (controlPenalty savedCref uniformQuoteError unitRoleUnused .complete) favorableCompleteS38Before [.query 1,.hydeRetriever 2] (.selection 3) = 0 := by
    apply control_penalty_empty_of_prior_terminal .complete savedCref uniformQuoteError favorableCompleteS38Before [.query 1,.hydeRetriever 2] (.selection 3) 24 (by decide)
    · decide
    · decide
  unfold indexScore
  rw [hs,hp,hn,hz]
  simp only [BackupStat.mean]
  norm_num

theorem favorableCompleteS38D2I3 : indexScore (7/5) (controlPenalty savedCref uniformQuoteError unitRoleUnused .complete) favorableCompleteS38Before [.query 1,.hydeRetriever 2] (.selection 0) = treeIndex ((0/1)/1) (7/5) 0 8 1 := by
  have hs : replayBackup favorableCompleteS38Before emptyStatistics ([.query 1,.hydeRetriever 2]++[.selection 0]) = ⟨1,(0/1)⟩ := by
    rw [replayBackup_empty_closed_form]
    simp +decide [backedEvents,favorableCompleteS38Before,favorableCompleteProposal,favorableCompleteEvent1,favorableCompleteEvent2,favorableCompleteEvent3,favorableCompleteEvent4,favorableCompleteEvent5,favorableCompleteEvent6,favorableCompleteEvent7,favorableCompleteEvent8,favorableCompleteEvent9,favorableCompleteEvent10,favorableCompleteEvent11,favorableCompleteEvent12,favorableCompleteEvent13,favorableCompleteEvent14,favorableCompleteEvent15,favorableCompleteEvent16,favorableCompleteEvent17,favorableCompleteEvent18,favorableCompleteEvent19,favorableCompleteEvent20,favorableCompleteEvent21,favorableCompleteEvent22,favorableCompleteEvent23,favorableCompleteEvent24,favorableCompleteEvent25,favorableCompleteEvent26,favorableCompleteEvent27,favorableCompleteEvent28,favorableCompleteEvent29,favorableCompleteEvent30,favorableCompleteEvent31,favorableCompleteEvent32,favorableCompleteEvent33,favorableCompleteEvent34,favorableCompleteEvent35,favorableCompleteEvent36,favorableCompleteEvent37,taskReward]
    <;> norm_num
  have hp : rawVisits favorableCompleteS38Before [.query 1,.hydeRetriever 2] = 8 := by decide
  have hn : rawVisits favorableCompleteS38Before ([.query 1,.hydeRetriever 2]++[.selection 0]) = 1 := by decide
  have hz : (controlPenalty savedCref uniformQuoteError unitRoleUnused .complete) favorableCompleteS38Before [.query 1,.hydeRetriever 2] (.selection 0) = 0 := by
    apply control_penalty_empty_of_prior_terminal .complete savedCref uniformQuoteError favorableCompleteS38Before [.query 1,.hydeRetriever 2] (.selection 0) 10 (by decide)
    · decide
    · decide
  unfold indexScore
  rw [hs,hp,hn,hz]
  simp only [BackupStat.mean]
  norm_num

theorem favorableCompleteS38D2Cmp0 : indexScore (7/5) (controlPenalty savedCref uniformQuoteError unitRoleUnused .complete) favorableCompleteS38Before [.query 1,.hydeRetriever 2] (.selection 1) < indexScore (7/5) (controlPenalty savedCref uniformQuoteError unitRoleUnused .complete) favorableCompleteS38Before [.query 1,.hydeRetriever 2] (.selection 0) := by
  rw [favorableCompleteS38D2I0,favorableCompleteS38D2I3]
  have h := index_strict_order_from_intervals ((0/1)/1) ((0/1)/2) 0 0 (103761259/50000000) (1146411/781250)
    (treeBonus (7/5) 8 1) (treeBonus (7/5) 8 2)
    (trajectory_bonus_8_1).1 (trajectory_bonus_8_2).2 (by norm_num)
  simpa only [treeIndex,sub_zero] using h

theorem favorableCompleteS38D2Cmp1 : indexScore (7/5) (controlPenalty savedCref uniformQuoteError unitRoleUnused .complete) favorableCompleteS38Before [.query 1,.hydeRetriever 2] (.selection 2) < indexScore (7/5) (controlPenalty savedCref uniformQuoteError unitRoleUnused .complete) favorableCompleteS38Before [.query 1,.hydeRetriever 2] (.selection 0) := by
  rw [favorableCompleteS38D2I1,favorableCompleteS38D2I3]
  have h := index_strict_order_from_intervals ((0/1)/1) ((0/1)/2) 0 0 (103761259/50000000) (1146411/781250)
    (treeBonus (7/5) 8 1) (treeBonus (7/5) 8 2)
    (trajectory_bonus_8_1).1 (trajectory_bonus_8_2).2 (by norm_num)
  simpa only [treeIndex,sub_zero] using h

theorem favorableCompleteS38D2Cmp2 : indexScore (7/5) (controlPenalty savedCref uniformQuoteError unitRoleUnused .complete) favorableCompleteS38Before [.query 1,.hydeRetriever 2] (.selection 3) < indexScore (7/5) (controlPenalty savedCref uniformQuoteError unitRoleUnused .complete) favorableCompleteS38Before [.query 1,.hydeRetriever 2] (.selection 0) := by
  rw [favorableCompleteS38D2I2,favorableCompleteS38D2I3]
  have h := index_strict_order_from_intervals ((0/1)/1) ((0/1)/2) 0 0 (103761259/50000000) (1146411/781250)
    (treeBonus (7/5) 8 1) (treeBonus (7/5) 8 2)
    (trajectory_bonus_8_1).1 (trajectory_bonus_8_2).2 (by norm_num)
  simpa only [treeIndex,sub_zero] using h

theorem favorableCompleteS38Choice2 : nativeFirstChoice (indexScore (7/5) (controlPenalty savedCref uniformQuoteError unitRoleUnused .complete) favorableCompleteS38Before [.query 1,.hydeRetriever 2]) favorableCompleteS38Before [.query 1,.hydeRetriever 2] = .selection 0 := by
  apply visited_choice_from_ordered_certificate _ _ [.query 1,.hydeRetriever 2] [.selection 1,.selection 2,.selection 3] [] (.selection 0) (by decide)
  · intro a ha
    have ho : orderedLegalAvailable [.query 1,.hydeRetriever 2] = [.selection 1,.selection 2,.selection 3,.selection 0] := by decide
    rw [ho] at ha
    simp only [List.mem_cons,List.not_mem_nil,or_false] at ha
    rcases ha with rfl | rfl | rfl | rfl <;> decide
  · intro a ha
    simp only [List.mem_cons,List.not_mem_nil,or_false] at ha
    rcases ha with rfl | rfl | rfl
    · exact favorableCompleteS38D2Cmp0
    · exact favorableCompleteS38D2Cmp1
    · exact favorableCompleteS38D2Cmp2
  · simp

theorem favorableCompleteS38ActualEvent : nativeEvent budgetTape (7/5) (controlPenalty savedCref uniformQuoteError unitRoleUnused .complete)
    (taskReward false (2/5) (1/2)) favorableCompleteS38Before = favorableCompleteEvent38 := by
  have hs0 := native_select_existing_step budgetTape (7/5) (controlPenalty savedCref uniformQuoteError unitRoleUnused .complete) favorableCompleteS38Before 8 [] (.query 1)
    (by decide) (by decide) favorableCompleteS38Choice0
  have hs1 := native_select_existing_step budgetTape (7/5) (controlPenalty savedCref uniformQuoteError unitRoleUnused .complete) favorableCompleteS38Before 7 [.query 1] (.hydeRetriever 2)
    (by decide) (by decide) favorableCompleteS38Choice1
  have hs2 := native_select_existing_step budgetTape (7/5) (controlPenalty savedCref uniformQuoteError unitRoleUnused .complete) favorableCompleteS38Before 6 [.query 1,.hydeRetriever 2] (.selection 0)
    (by decide) (by decide) favorableCompleteS38Choice2
  have hnew := native_select_new_step budgetTape (7/5) (controlPenalty savedCref uniformQuoteError unitRoleUnused .complete) favorableCompleteS38Before 5 [.query 1,.hydeRetriever 2,.selection 0]
    [.width 3,.width 0,.width 1,.width 2] (.width 0) (by decide) (by decide) (by decide) (by decide)
  have hs : nativeSelect budgetTape (7/5) (controlPenalty savedCref uniformQuoteError unitRoleUnused .complete) favorableCompleteS38Before 9 [] = [.query 1,.hydeRetriever 2,.selection 0,.width 0] := by
    rw [hs0]
    change nativeSelect budgetTape (7/5) (controlPenalty savedCref uniformQuoteError unitRoleUnused .complete) favorableCompleteS38Before 8 [.query 1] = _
    rw [hs1]
    change nativeSelect budgetTape (7/5) (controlPenalty savedCref uniformQuoteError unitRoleUnused .complete) favorableCompleteS38Before 7 [.query 1,.hydeRetriever 2] = _
    rw [hs2]
    change nativeSelect budgetTape (7/5) (controlPenalty savedCref uniformQuoteError unitRoleUnused .complete) favorableCompleteS38Before 6 [.query 1,.hydeRetriever 2,.selection 0] = _
    rw [hnew] <;> rfl
  have hr : repairedRollout budgetTape favorableCompleteS38Before 9 [.query 1,.hydeRetriever 2,.selection 0,.width 0] = [.query 1,.hydeRetriever 2,.selection 0,.width 0,.stop,.reranker 0,.topm 2,.context 0,.answer 2] := by decide
  simp only [nativeEvent,hs,hr]
  rfl

def favorableCompleteS39Before := favorableCompleteProposal.take 38

theorem favorableCompleteS39Choice0 : nativeFirstChoice (indexScore (7/5) (controlPenalty savedCref uniformQuoteError unitRoleUnused .complete) favorableCompleteS39Before []) favorableCompleteS39Before [] = .query 1 := by
  apply complete_root_from_physical_gap favorableCompleteS39Before (favorableComplete_prefix_rewards 38) (by decide)
  · intro q; fin_cases q <;> decide
  · exact AgentUCTNextExact.favorable_complete_hyde_root_suffix_empty 38 (by omega)
  · intro q hq
    exact AgentUCTNextExact.favorable_complete_normal_root_physical_quote_exact 38 (by omega) q hq

theorem favorableCompleteS39D1I0 : indexScore (7/5) (controlPenalty savedCref uniformQuoteError unitRoleUnused .complete) favorableCompleteS39Before [.query 1] (.hydeRetriever 1) = treeIndex ((3/2)/12) (7/5) 0 31 12 := by
  have hs : replayBackup favorableCompleteS39Before emptyStatistics ([.query 1]++[.hydeRetriever 1]) = ⟨12,(3/2)⟩ := by
    rw [replayBackup_empty_closed_form]
    simp +decide [backedEvents,favorableCompleteS39Before,favorableCompleteProposal,favorableCompleteEvent1,favorableCompleteEvent2,favorableCompleteEvent3,favorableCompleteEvent4,favorableCompleteEvent5,favorableCompleteEvent6,favorableCompleteEvent7,favorableCompleteEvent8,favorableCompleteEvent9,favorableCompleteEvent10,favorableCompleteEvent11,favorableCompleteEvent12,favorableCompleteEvent13,favorableCompleteEvent14,favorableCompleteEvent15,favorableCompleteEvent16,favorableCompleteEvent17,favorableCompleteEvent18,favorableCompleteEvent19,favorableCompleteEvent20,favorableCompleteEvent21,favorableCompleteEvent22,favorableCompleteEvent23,favorableCompleteEvent24,favorableCompleteEvent25,favorableCompleteEvent26,favorableCompleteEvent27,favorableCompleteEvent28,favorableCompleteEvent29,favorableCompleteEvent30,favorableCompleteEvent31,favorableCompleteEvent32,favorableCompleteEvent33,favorableCompleteEvent34,favorableCompleteEvent35,favorableCompleteEvent36,favorableCompleteEvent37,favorableCompleteEvent38,taskReward]
    <;> norm_num
  have hp : rawVisits favorableCompleteS39Before [.query 1] = 31 := by decide
  have hn : rawVisits favorableCompleteS39Before ([.query 1]++[.hydeRetriever 1]) = 12 := by decide
  have hz : (controlPenalty savedCref uniformQuoteError unitRoleUnused .complete) favorableCompleteS39Before [.query 1] (.hydeRetriever 1) = 0 := by
    apply control_penalty_empty_of_prior_terminal .complete savedCref uniformQuoteError favorableCompleteS39Before [.query 1] (.hydeRetriever 1) 8 (by decide)
    · decide
    · decide
  unfold indexScore
  rw [hs,hp,hn,hz]
  simp only [BackupStat.mean]
  norm_num

theorem favorableCompleteS39D1I1 : indexScore (7/5) (controlPenalty savedCref uniformQuoteError unitRoleUnused .complete) favorableCompleteS39Before [.query 1] (.hydeRetriever 0) = treeIndex ((0/1)/9) (7/5) 0 31 9 := by
  have hs : replayBackup favorableCompleteS39Before emptyStatistics ([.query 1]++[.hydeRetriever 0]) = ⟨9,(0/1)⟩ := by
    rw [replayBackup_empty_closed_form]
    simp +decide [backedEvents,favorableCompleteS39Before,favorableCompleteProposal,favorableCompleteEvent1,favorableCompleteEvent2,favorableCompleteEvent3,favorableCompleteEvent4,favorableCompleteEvent5,favorableCompleteEvent6,favorableCompleteEvent7,favorableCompleteEvent8,favorableCompleteEvent9,favorableCompleteEvent10,favorableCompleteEvent11,favorableCompleteEvent12,favorableCompleteEvent13,favorableCompleteEvent14,favorableCompleteEvent15,favorableCompleteEvent16,favorableCompleteEvent17,favorableCompleteEvent18,favorableCompleteEvent19,favorableCompleteEvent20,favorableCompleteEvent21,favorableCompleteEvent22,favorableCompleteEvent23,favorableCompleteEvent24,favorableCompleteEvent25,favorableCompleteEvent26,favorableCompleteEvent27,favorableCompleteEvent28,favorableCompleteEvent29,favorableCompleteEvent30,favorableCompleteEvent31,favorableCompleteEvent32,favorableCompleteEvent33,favorableCompleteEvent34,favorableCompleteEvent35,favorableCompleteEvent36,favorableCompleteEvent37,favorableCompleteEvent38,taskReward]
    <;> norm_num
  have hp : rawVisits favorableCompleteS39Before [.query 1] = 31 := by decide
  have hn : rawVisits favorableCompleteS39Before ([.query 1]++[.hydeRetriever 0]) = 9 := by decide
  have hz : (controlPenalty savedCref uniformQuoteError unitRoleUnused .complete) favorableCompleteS39Before [.query 1] (.hydeRetriever 0) = 0 := by
    apply control_penalty_empty_of_prior_terminal .complete savedCref uniformQuoteError favorableCompleteS39Before [.query 1] (.hydeRetriever 0) 1 (by decide)
    · decide
    · decide
  unfold indexScore
  rw [hs,hp,hn,hz]
  simp only [BackupStat.mean]
  norm_num

theorem favorableCompleteS39D1I2 : indexScore (7/5) (controlPenalty savedCref uniformQuoteError unitRoleUnused .complete) favorableCompleteS39Before [.query 1] (.hydeRetriever 2) = treeIndex ((0/1)/9) (7/5) 0 31 9 := by
  have hs : replayBackup favorableCompleteS39Before emptyStatistics ([.query 1]++[.hydeRetriever 2]) = ⟨9,(0/1)⟩ := by
    rw [replayBackup_empty_closed_form]
    simp +decide [backedEvents,favorableCompleteS39Before,favorableCompleteProposal,favorableCompleteEvent1,favorableCompleteEvent2,favorableCompleteEvent3,favorableCompleteEvent4,favorableCompleteEvent5,favorableCompleteEvent6,favorableCompleteEvent7,favorableCompleteEvent8,favorableCompleteEvent9,favorableCompleteEvent10,favorableCompleteEvent11,favorableCompleteEvent12,favorableCompleteEvent13,favorableCompleteEvent14,favorableCompleteEvent15,favorableCompleteEvent16,favorableCompleteEvent17,favorableCompleteEvent18,favorableCompleteEvent19,favorableCompleteEvent20,favorableCompleteEvent21,favorableCompleteEvent22,favorableCompleteEvent23,favorableCompleteEvent24,favorableCompleteEvent25,favorableCompleteEvent26,favorableCompleteEvent27,favorableCompleteEvent28,favorableCompleteEvent29,favorableCompleteEvent30,favorableCompleteEvent31,favorableCompleteEvent32,favorableCompleteEvent33,favorableCompleteEvent34,favorableCompleteEvent35,favorableCompleteEvent36,favorableCompleteEvent37,favorableCompleteEvent38,taskReward]
    <;> norm_num
  have hp : rawVisits favorableCompleteS39Before [.query 1] = 31 := by decide
  have hn : rawVisits favorableCompleteS39Before ([.query 1]++[.hydeRetriever 2]) = 9 := by decide
  have hz : (controlPenalty savedCref uniformQuoteError unitRoleUnused .complete) favorableCompleteS39Before [.query 1] (.hydeRetriever 2) = 0 := by
    apply control_penalty_empty_of_prior_terminal .complete savedCref uniformQuoteError favorableCompleteS39Before [.query 1] (.hydeRetriever 2) 10 (by decide)
    · decide
    · decide
  unfold indexScore
  rw [hs,hp,hn,hz]
  simp only [BackupStat.mean]
  norm_num

theorem favorableCompleteS39D1Cmp1 : indexScore (7/5) (controlPenalty savedCref uniformQuoteError unitRoleUnused .complete) favorableCompleteS39Before [.query 1] (.hydeRetriever 0) ≤ indexScore (7/5) (controlPenalty savedCref uniformQuoteError unitRoleUnused .complete) favorableCompleteS39Before [.query 1] (.hydeRetriever 1) := by
  rw [favorableCompleteS39D1I1,favorableCompleteS39D1I0]
  have h := index_weak_order_from_intervals ((3/2)/12) ((0/1)/9) 0 0 (9404703/12500000) (5429809/6250000)
    (treeBonus (7/5) 31 12) (treeBonus (7/5) 31 9)
    (trajectory_bonus_31_12).1 (trajectory_bonus_31_9).2 (by norm_num)
  simpa only [treeIndex,sub_zero] using h

theorem favorableCompleteS39D1Cmp2 : indexScore (7/5) (controlPenalty savedCref uniformQuoteError unitRoleUnused .complete) favorableCompleteS39Before [.query 1] (.hydeRetriever 2) ≤ indexScore (7/5) (controlPenalty savedCref uniformQuoteError unitRoleUnused .complete) favorableCompleteS39Before [.query 1] (.hydeRetriever 1) := by
  rw [favorableCompleteS39D1I2,favorableCompleteS39D1I0]
  have h := index_weak_order_from_intervals ((3/2)/12) ((0/1)/9) 0 0 (9404703/12500000) (5429809/6250000)
    (treeBonus (7/5) 31 12) (treeBonus (7/5) 31 9)
    (trajectory_bonus_31_12).1 (trajectory_bonus_31_9).2 (by norm_num)
  simpa only [treeIndex,sub_zero] using h

theorem favorableCompleteS39Choice1 : nativeFirstChoice (indexScore (7/5) (controlPenalty savedCref uniformQuoteError unitRoleUnused .complete) favorableCompleteS39Before [.query 1]) favorableCompleteS39Before [.query 1] = .hydeRetriever 1 := by
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
    · exact favorableCompleteS39D1Cmp1
    · exact favorableCompleteS39D1Cmp2

theorem favorableCompleteS39D2I0 : indexScore (7/5) (controlPenalty savedCref uniformQuoteError unitRoleUnused .complete) favorableCompleteS39Before [.query 1,.hydeRetriever 1] (.selection 1) = treeIndex ((0/1)/3) (7/5) 0 12 3 := by
  have hs : replayBackup favorableCompleteS39Before emptyStatistics ([.query 1,.hydeRetriever 1]++[.selection 1]) = ⟨3,(0/1)⟩ := by
    rw [replayBackup_empty_closed_form]
    simp +decide [backedEvents,favorableCompleteS39Before,favorableCompleteProposal,favorableCompleteEvent1,favorableCompleteEvent2,favorableCompleteEvent3,favorableCompleteEvent4,favorableCompleteEvent5,favorableCompleteEvent6,favorableCompleteEvent7,favorableCompleteEvent8,favorableCompleteEvent9,favorableCompleteEvent10,favorableCompleteEvent11,favorableCompleteEvent12,favorableCompleteEvent13,favorableCompleteEvent14,favorableCompleteEvent15,favorableCompleteEvent16,favorableCompleteEvent17,favorableCompleteEvent18,favorableCompleteEvent19,favorableCompleteEvent20,favorableCompleteEvent21,favorableCompleteEvent22,favorableCompleteEvent23,favorableCompleteEvent24,favorableCompleteEvent25,favorableCompleteEvent26,favorableCompleteEvent27,favorableCompleteEvent28,favorableCompleteEvent29,favorableCompleteEvent30,favorableCompleteEvent31,favorableCompleteEvent32,favorableCompleteEvent33,favorableCompleteEvent34,favorableCompleteEvent35,favorableCompleteEvent36,favorableCompleteEvent37,favorableCompleteEvent38,taskReward]
    <;> norm_num
  have hp : rawVisits favorableCompleteS39Before [.query 1,.hydeRetriever 1] = 12 := by decide
  have hn : rawVisits favorableCompleteS39Before ([.query 1,.hydeRetriever 1]++[.selection 1]) = 3 := by decide
  have hz : (controlPenalty savedCref uniformQuoteError unitRoleUnused .complete) favorableCompleteS39Before [.query 1,.hydeRetriever 1] (.selection 1) = 0 := by
    apply control_penalty_empty_of_prior_terminal .complete savedCref uniformQuoteError favorableCompleteS39Before [.query 1,.hydeRetriever 1] (.selection 1) 14 (by decide)
    · decide
    · decide
  unfold indexScore
  rw [hs,hp,hn,hz]
  simp only [BackupStat.mean]
  norm_num

theorem favorableCompleteS39D2I1 : indexScore (7/5) (controlPenalty savedCref uniformQuoteError unitRoleUnused .complete) favorableCompleteS39Before [.query 1,.hydeRetriever 1] (.selection 2) = treeIndex ((0/1)/2) (7/5) 0 12 2 := by
  have hs : replayBackup favorableCompleteS39Before emptyStatistics ([.query 1,.hydeRetriever 1]++[.selection 2]) = ⟨2,(0/1)⟩ := by
    rw [replayBackup_empty_closed_form]
    simp +decide [backedEvents,favorableCompleteS39Before,favorableCompleteProposal,favorableCompleteEvent1,favorableCompleteEvent2,favorableCompleteEvent3,favorableCompleteEvent4,favorableCompleteEvent5,favorableCompleteEvent6,favorableCompleteEvent7,favorableCompleteEvent8,favorableCompleteEvent9,favorableCompleteEvent10,favorableCompleteEvent11,favorableCompleteEvent12,favorableCompleteEvent13,favorableCompleteEvent14,favorableCompleteEvent15,favorableCompleteEvent16,favorableCompleteEvent17,favorableCompleteEvent18,favorableCompleteEvent19,favorableCompleteEvent20,favorableCompleteEvent21,favorableCompleteEvent22,favorableCompleteEvent23,favorableCompleteEvent24,favorableCompleteEvent25,favorableCompleteEvent26,favorableCompleteEvent27,favorableCompleteEvent28,favorableCompleteEvent29,favorableCompleteEvent30,favorableCompleteEvent31,favorableCompleteEvent32,favorableCompleteEvent33,favorableCompleteEvent34,favorableCompleteEvent35,favorableCompleteEvent36,favorableCompleteEvent37,favorableCompleteEvent38,taskReward]
    <;> norm_num
  have hp : rawVisits favorableCompleteS39Before [.query 1,.hydeRetriever 1] = 12 := by decide
  have hn : rawVisits favorableCompleteS39Before ([.query 1,.hydeRetriever 1]++[.selection 2]) = 2 := by decide
  have hz : (controlPenalty savedCref uniformQuoteError unitRoleUnused .complete) favorableCompleteS39Before [.query 1,.hydeRetriever 1] (.selection 2) = 0 := by
    apply control_penalty_empty_of_prior_terminal .complete savedCref uniformQuoteError favorableCompleteS39Before [.query 1,.hydeRetriever 1] (.selection 2) 15 (by decide)
    · decide
    · decide
  unfold indexScore
  rw [hs,hp,hn,hz]
  simp only [BackupStat.mean]
  norm_num

theorem favorableCompleteS39D2I2 : indexScore (7/5) (controlPenalty savedCref uniformQuoteError unitRoleUnused .complete) favorableCompleteS39Before [.query 1,.hydeRetriever 1] (.selection 3) = treeIndex ((0/1)/2) (7/5) 0 12 2 := by
  have hs : replayBackup favorableCompleteS39Before emptyStatistics ([.query 1,.hydeRetriever 1]++[.selection 3]) = ⟨2,(0/1)⟩ := by
    rw [replayBackup_empty_closed_form]
    simp +decide [backedEvents,favorableCompleteS39Before,favorableCompleteProposal,favorableCompleteEvent1,favorableCompleteEvent2,favorableCompleteEvent3,favorableCompleteEvent4,favorableCompleteEvent5,favorableCompleteEvent6,favorableCompleteEvent7,favorableCompleteEvent8,favorableCompleteEvent9,favorableCompleteEvent10,favorableCompleteEvent11,favorableCompleteEvent12,favorableCompleteEvent13,favorableCompleteEvent14,favorableCompleteEvent15,favorableCompleteEvent16,favorableCompleteEvent17,favorableCompleteEvent18,favorableCompleteEvent19,favorableCompleteEvent20,favorableCompleteEvent21,favorableCompleteEvent22,favorableCompleteEvent23,favorableCompleteEvent24,favorableCompleteEvent25,favorableCompleteEvent26,favorableCompleteEvent27,favorableCompleteEvent28,favorableCompleteEvent29,favorableCompleteEvent30,favorableCompleteEvent31,favorableCompleteEvent32,favorableCompleteEvent33,favorableCompleteEvent34,favorableCompleteEvent35,favorableCompleteEvent36,favorableCompleteEvent37,favorableCompleteEvent38,taskReward]
    <;> norm_num
  have hp : rawVisits favorableCompleteS39Before [.query 1,.hydeRetriever 1] = 12 := by decide
  have hn : rawVisits favorableCompleteS39Before ([.query 1,.hydeRetriever 1]++[.selection 3]) = 2 := by decide
  have hz : (controlPenalty savedCref uniformQuoteError unitRoleUnused .complete) favorableCompleteS39Before [.query 1,.hydeRetriever 1] (.selection 3) = 0 := by
    apply control_penalty_empty_of_prior_terminal .complete savedCref uniformQuoteError favorableCompleteS39Before [.query 1,.hydeRetriever 1] (.selection 3) 18 (by decide)
    · decide
    · decide
  unfold indexScore
  rw [hs,hp,hn,hz]
  simp only [BackupStat.mean]
  norm_num

theorem favorableCompleteS39D2I3 : indexScore (7/5) (controlPenalty savedCref uniformQuoteError unitRoleUnused .complete) favorableCompleteS39Before [.query 1,.hydeRetriever 1] (.selection 0) = treeIndex ((1/1)/4) (7/5) 0 12 4 := by
  have hs : replayBackup favorableCompleteS39Before emptyStatistics ([.query 1,.hydeRetriever 1]++[.selection 0]) = ⟨4,(1/1)⟩ := by
    rw [replayBackup_empty_closed_form]
    simp +decide [backedEvents,favorableCompleteS39Before,favorableCompleteProposal,favorableCompleteEvent1,favorableCompleteEvent2,favorableCompleteEvent3,favorableCompleteEvent4,favorableCompleteEvent5,favorableCompleteEvent6,favorableCompleteEvent7,favorableCompleteEvent8,favorableCompleteEvent9,favorableCompleteEvent10,favorableCompleteEvent11,favorableCompleteEvent12,favorableCompleteEvent13,favorableCompleteEvent14,favorableCompleteEvent15,favorableCompleteEvent16,favorableCompleteEvent17,favorableCompleteEvent18,favorableCompleteEvent19,favorableCompleteEvent20,favorableCompleteEvent21,favorableCompleteEvent22,favorableCompleteEvent23,favorableCompleteEvent24,favorableCompleteEvent25,favorableCompleteEvent26,favorableCompleteEvent27,favorableCompleteEvent28,favorableCompleteEvent29,favorableCompleteEvent30,favorableCompleteEvent31,favorableCompleteEvent32,favorableCompleteEvent33,favorableCompleteEvent34,favorableCompleteEvent35,favorableCompleteEvent36,favorableCompleteEvent37,favorableCompleteEvent38,taskReward]
    <;> norm_num
  have hp : rawVisits favorableCompleteS39Before [.query 1,.hydeRetriever 1] = 12 := by decide
  have hn : rawVisits favorableCompleteS39Before ([.query 1,.hydeRetriever 1]++[.selection 0]) = 4 := by decide
  have hz : (controlPenalty savedCref uniformQuoteError unitRoleUnused .complete) favorableCompleteS39Before [.query 1,.hydeRetriever 1] (.selection 0) = 0 := by
    apply control_penalty_empty_of_prior_terminal .complete savedCref uniformQuoteError favorableCompleteS39Before [.query 1,.hydeRetriever 1] (.selection 0) 8 (by decide)
    · decide
    · decide
  unfold indexScore
  rw [hs,hp,hn,hz]
  simp only [BackupStat.mean]
  norm_num

theorem favorableCompleteS39D2Cmp0 : indexScore (7/5) (controlPenalty savedCref uniformQuoteError unitRoleUnused .complete) favorableCompleteS39Before [.query 1,.hydeRetriever 1] (.selection 1) < indexScore (7/5) (controlPenalty savedCref uniformQuoteError unitRoleUnused .complete) favorableCompleteS39Before [.query 1,.hydeRetriever 1] (.selection 2) := by
  rw [favorableCompleteS39D2I0,favorableCompleteS39D2I1]
  have h := index_strict_order_from_intervals ((0/1)/2) ((0/1)/3) 0 0 (79272473/50000000) (6472571/5000000)
    (treeBonus (7/5) 12 2) (treeBonus (7/5) 12 3)
    (trajectory_bonus_12_2).1 (trajectory_bonus_12_3).2 (by norm_num)
  simpa only [treeIndex,sub_zero] using h

theorem favorableCompleteS39D2Cmp2 : indexScore (7/5) (controlPenalty savedCref uniformQuoteError unitRoleUnused .complete) favorableCompleteS39Before [.query 1,.hydeRetriever 1] (.selection 3) ≤ indexScore (7/5) (controlPenalty savedCref uniformQuoteError unitRoleUnused .complete) favorableCompleteS39Before [.query 1,.hydeRetriever 1] (.selection 2) := by
  rw [favorableCompleteS39D2I2,favorableCompleteS39D2I1]

theorem favorableCompleteS39D2Cmp3 : indexScore (7/5) (controlPenalty savedCref uniformQuoteError unitRoleUnused .complete) favorableCompleteS39Before [.query 1,.hydeRetriever 1] (.selection 0) ≤ indexScore (7/5) (controlPenalty savedCref uniformQuoteError unitRoleUnused .complete) favorableCompleteS39Before [.query 1,.hydeRetriever 1] (.selection 2) := by
  rw [favorableCompleteS39D2I3,favorableCompleteS39D2I1]
  have h := index_weak_order_from_intervals ((0/1)/2) ((1/1)/4) 0 0 (79272473/50000000) (5605411/5000000)
    (treeBonus (7/5) 12 2) (treeBonus (7/5) 12 4)
    (trajectory_bonus_12_2).1 (trajectory_bonus_12_4).2 (by norm_num)
  simpa only [treeIndex,sub_zero] using h

theorem favorableCompleteS39Choice2 : nativeFirstChoice (indexScore (7/5) (controlPenalty savedCref uniformQuoteError unitRoleUnused .complete) favorableCompleteS39Before [.query 1,.hydeRetriever 1]) favorableCompleteS39Before [.query 1,.hydeRetriever 1] = .selection 2 := by
  apply visited_choice_from_ordered_certificate _ _ [.query 1,.hydeRetriever 1] [.selection 1] [.selection 3,.selection 0] (.selection 2) (by decide)
  · intro a ha
    have ho : orderedLegalAvailable [.query 1,.hydeRetriever 1] = [.selection 1,.selection 2,.selection 3,.selection 0] := by decide
    rw [ho] at ha
    simp only [List.mem_cons,List.not_mem_nil,or_false] at ha
    rcases ha with rfl | rfl | rfl | rfl <;> decide
  · intro a ha
    simp only [List.mem_cons,List.not_mem_nil,or_false] at ha
    rcases ha with rfl
    · exact favorableCompleteS39D2Cmp0
  · intro a ha
    simp only [List.mem_cons,List.not_mem_nil,or_false] at ha
    rcases ha with rfl | rfl
    · exact favorableCompleteS39D2Cmp2
    · exact favorableCompleteS39D2Cmp3

theorem favorableCompleteS39ActualEvent : nativeEvent budgetTape (7/5) (controlPenalty savedCref uniformQuoteError unitRoleUnused .complete)
    (taskReward false (2/5) (1/2)) favorableCompleteS39Before = favorableCompleteEvent39 := by
  have hs0 := native_select_existing_step budgetTape (7/5) (controlPenalty savedCref uniformQuoteError unitRoleUnused .complete) favorableCompleteS39Before 8 [] (.query 1)
    (by decide) (by decide) favorableCompleteS39Choice0
  have hs1 := native_select_existing_step budgetTape (7/5) (controlPenalty savedCref uniformQuoteError unitRoleUnused .complete) favorableCompleteS39Before 7 [.query 1] (.hydeRetriever 1)
    (by decide) (by decide) favorableCompleteS39Choice1
  have hs2 := native_select_existing_step budgetTape (7/5) (controlPenalty savedCref uniformQuoteError unitRoleUnused .complete) favorableCompleteS39Before 6 [.query 1,.hydeRetriever 1] (.selection 2)
    (by decide) (by decide) favorableCompleteS39Choice2
  have hnew := native_select_new_step budgetTape (7/5) (controlPenalty savedCref uniformQuoteError unitRoleUnused .complete) favorableCompleteS39Before 5 [.query 1,.hydeRetriever 1,.selection 2]
    [.width 3,.width 1,.width 2] (.width 3) (by decide) (by decide) (by decide) (by decide)
  have hs : nativeSelect budgetTape (7/5) (controlPenalty savedCref uniformQuoteError unitRoleUnused .complete) favorableCompleteS39Before 9 [] = [.query 1,.hydeRetriever 1,.selection 2,.width 3] := by
    rw [hs0]
    change nativeSelect budgetTape (7/5) (controlPenalty savedCref uniformQuoteError unitRoleUnused .complete) favorableCompleteS39Before 8 [.query 1] = _
    rw [hs1]
    change nativeSelect budgetTape (7/5) (controlPenalty savedCref uniformQuoteError unitRoleUnused .complete) favorableCompleteS39Before 7 [.query 1,.hydeRetriever 1] = _
    rw [hs2]
    change nativeSelect budgetTape (7/5) (controlPenalty savedCref uniformQuoteError unitRoleUnused .complete) favorableCompleteS39Before 6 [.query 1,.hydeRetriever 1,.selection 2] = _
    rw [hnew] <;> rfl
  have hr : repairedRollout budgetTape favorableCompleteS39Before 9 [.query 1,.hydeRetriever 1,.selection 2,.width 3] = [.query 1,.hydeRetriever 1,.selection 2,.width 3,.stop,.reranker 0,.topm 0,.context 0,.answer 0] := by decide
  simp only [nativeEvent,hs,hr]
  rfl

def favorableCompleteS40Before := favorableCompleteProposal.take 39

theorem favorableCompleteS40Choice0 : nativeFirstChoice (indexScore (7/5) (controlPenalty savedCref uniformQuoteError unitRoleUnused .complete) favorableCompleteS40Before []) favorableCompleteS40Before [] = .query 1 := by
  apply complete_root_from_physical_gap favorableCompleteS40Before (favorableComplete_prefix_rewards 39) (by decide)
  · intro q; fin_cases q <;> decide
  · exact AgentUCTNextExact.favorable_complete_hyde_root_suffix_empty 39 (by omega)
  · intro q hq
    exact AgentUCTNextExact.favorable_complete_normal_root_physical_quote_exact 39 (by omega) q hq

theorem favorableCompleteS40D1I0 : indexScore (7/5) (controlPenalty savedCref uniformQuoteError unitRoleUnused .complete) favorableCompleteS40Before [.query 1] (.hydeRetriever 1) = treeIndex ((3/2)/13) (7/5) 0 32 13 := by
  have hs : replayBackup favorableCompleteS40Before emptyStatistics ([.query 1]++[.hydeRetriever 1]) = ⟨13,(3/2)⟩ := by
    rw [replayBackup_empty_closed_form]
    simp +decide [backedEvents,favorableCompleteS40Before,favorableCompleteProposal,favorableCompleteEvent1,favorableCompleteEvent2,favorableCompleteEvent3,favorableCompleteEvent4,favorableCompleteEvent5,favorableCompleteEvent6,favorableCompleteEvent7,favorableCompleteEvent8,favorableCompleteEvent9,favorableCompleteEvent10,favorableCompleteEvent11,favorableCompleteEvent12,favorableCompleteEvent13,favorableCompleteEvent14,favorableCompleteEvent15,favorableCompleteEvent16,favorableCompleteEvent17,favorableCompleteEvent18,favorableCompleteEvent19,favorableCompleteEvent20,favorableCompleteEvent21,favorableCompleteEvent22,favorableCompleteEvent23,favorableCompleteEvent24,favorableCompleteEvent25,favorableCompleteEvent26,favorableCompleteEvent27,favorableCompleteEvent28,favorableCompleteEvent29,favorableCompleteEvent30,favorableCompleteEvent31,favorableCompleteEvent32,favorableCompleteEvent33,favorableCompleteEvent34,favorableCompleteEvent35,favorableCompleteEvent36,favorableCompleteEvent37,favorableCompleteEvent38,favorableCompleteEvent39,taskReward]
    <;> norm_num
  have hp : rawVisits favorableCompleteS40Before [.query 1] = 32 := by decide
  have hn : rawVisits favorableCompleteS40Before ([.query 1]++[.hydeRetriever 1]) = 13 := by decide
  have hz : (controlPenalty savedCref uniformQuoteError unitRoleUnused .complete) favorableCompleteS40Before [.query 1] (.hydeRetriever 1) = 0 := by
    apply control_penalty_empty_of_prior_terminal .complete savedCref uniformQuoteError favorableCompleteS40Before [.query 1] (.hydeRetriever 1) 8 (by decide)
    · decide
    · decide
  unfold indexScore
  rw [hs,hp,hn,hz]
  simp only [BackupStat.mean]
  norm_num

theorem favorableCompleteS40D1I1 : indexScore (7/5) (controlPenalty savedCref uniformQuoteError unitRoleUnused .complete) favorableCompleteS40Before [.query 1] (.hydeRetriever 0) = treeIndex ((0/1)/9) (7/5) 0 32 9 := by
  have hs : replayBackup favorableCompleteS40Before emptyStatistics ([.query 1]++[.hydeRetriever 0]) = ⟨9,(0/1)⟩ := by
    rw [replayBackup_empty_closed_form]
    simp +decide [backedEvents,favorableCompleteS40Before,favorableCompleteProposal,favorableCompleteEvent1,favorableCompleteEvent2,favorableCompleteEvent3,favorableCompleteEvent4,favorableCompleteEvent5,favorableCompleteEvent6,favorableCompleteEvent7,favorableCompleteEvent8,favorableCompleteEvent9,favorableCompleteEvent10,favorableCompleteEvent11,favorableCompleteEvent12,favorableCompleteEvent13,favorableCompleteEvent14,favorableCompleteEvent15,favorableCompleteEvent16,favorableCompleteEvent17,favorableCompleteEvent18,favorableCompleteEvent19,favorableCompleteEvent20,favorableCompleteEvent21,favorableCompleteEvent22,favorableCompleteEvent23,favorableCompleteEvent24,favorableCompleteEvent25,favorableCompleteEvent26,favorableCompleteEvent27,favorableCompleteEvent28,favorableCompleteEvent29,favorableCompleteEvent30,favorableCompleteEvent31,favorableCompleteEvent32,favorableCompleteEvent33,favorableCompleteEvent34,favorableCompleteEvent35,favorableCompleteEvent36,favorableCompleteEvent37,favorableCompleteEvent38,favorableCompleteEvent39,taskReward]
    <;> norm_num
  have hp : rawVisits favorableCompleteS40Before [.query 1] = 32 := by decide
  have hn : rawVisits favorableCompleteS40Before ([.query 1]++[.hydeRetriever 0]) = 9 := by decide
  have hz : (controlPenalty savedCref uniformQuoteError unitRoleUnused .complete) favorableCompleteS40Before [.query 1] (.hydeRetriever 0) = 0 := by
    apply control_penalty_empty_of_prior_terminal .complete savedCref uniformQuoteError favorableCompleteS40Before [.query 1] (.hydeRetriever 0) 1 (by decide)
    · decide
    · decide
  unfold indexScore
  rw [hs,hp,hn,hz]
  simp only [BackupStat.mean]
  norm_num

theorem favorableCompleteS40D1I2 : indexScore (7/5) (controlPenalty savedCref uniformQuoteError unitRoleUnused .complete) favorableCompleteS40Before [.query 1] (.hydeRetriever 2) = treeIndex ((0/1)/9) (7/5) 0 32 9 := by
  have hs : replayBackup favorableCompleteS40Before emptyStatistics ([.query 1]++[.hydeRetriever 2]) = ⟨9,(0/1)⟩ := by
    rw [replayBackup_empty_closed_form]
    simp +decide [backedEvents,favorableCompleteS40Before,favorableCompleteProposal,favorableCompleteEvent1,favorableCompleteEvent2,favorableCompleteEvent3,favorableCompleteEvent4,favorableCompleteEvent5,favorableCompleteEvent6,favorableCompleteEvent7,favorableCompleteEvent8,favorableCompleteEvent9,favorableCompleteEvent10,favorableCompleteEvent11,favorableCompleteEvent12,favorableCompleteEvent13,favorableCompleteEvent14,favorableCompleteEvent15,favorableCompleteEvent16,favorableCompleteEvent17,favorableCompleteEvent18,favorableCompleteEvent19,favorableCompleteEvent20,favorableCompleteEvent21,favorableCompleteEvent22,favorableCompleteEvent23,favorableCompleteEvent24,favorableCompleteEvent25,favorableCompleteEvent26,favorableCompleteEvent27,favorableCompleteEvent28,favorableCompleteEvent29,favorableCompleteEvent30,favorableCompleteEvent31,favorableCompleteEvent32,favorableCompleteEvent33,favorableCompleteEvent34,favorableCompleteEvent35,favorableCompleteEvent36,favorableCompleteEvent37,favorableCompleteEvent38,favorableCompleteEvent39,taskReward]
    <;> norm_num
  have hp : rawVisits favorableCompleteS40Before [.query 1] = 32 := by decide
  have hn : rawVisits favorableCompleteS40Before ([.query 1]++[.hydeRetriever 2]) = 9 := by decide
  have hz : (controlPenalty savedCref uniformQuoteError unitRoleUnused .complete) favorableCompleteS40Before [.query 1] (.hydeRetriever 2) = 0 := by
    apply control_penalty_empty_of_prior_terminal .complete savedCref uniformQuoteError favorableCompleteS40Before [.query 1] (.hydeRetriever 2) 10 (by decide)
    · decide
    · decide
  unfold indexScore
  rw [hs,hp,hn,hz]
  simp only [BackupStat.mean]
  norm_num

theorem favorableCompleteS40D1Cmp0 : indexScore (7/5) (controlPenalty savedCref uniformQuoteError unitRoleUnused .complete) favorableCompleteS40Before [.query 1] (.hydeRetriever 1) < indexScore (7/5) (controlPenalty savedCref uniformQuoteError unitRoleUnused .complete) favorableCompleteS40Before [.query 1] (.hydeRetriever 0) := by
  rw [favorableCompleteS40D1I0,favorableCompleteS40D1I1]
  have h := index_strict_order_from_intervals ((0/1)/9) ((3/2)/13) 0 0 (43630881/50000000) (36303099/50000000)
    (treeBonus (7/5) 32 9) (treeBonus (7/5) 32 13)
    (trajectory_bonus_32_9).1 (trajectory_bonus_32_13).2 (by norm_num)
  simpa only [treeIndex,sub_zero] using h

theorem favorableCompleteS40D1Cmp2 : indexScore (7/5) (controlPenalty savedCref uniformQuoteError unitRoleUnused .complete) favorableCompleteS40Before [.query 1] (.hydeRetriever 2) ≤ indexScore (7/5) (controlPenalty savedCref uniformQuoteError unitRoleUnused .complete) favorableCompleteS40Before [.query 1] (.hydeRetriever 0) := by
  rw [favorableCompleteS40D1I2,favorableCompleteS40D1I1]

theorem favorableCompleteS40Choice1 : nativeFirstChoice (indexScore (7/5) (controlPenalty savedCref uniformQuoteError unitRoleUnused .complete) favorableCompleteS40Before [.query 1]) favorableCompleteS40Before [.query 1] = .hydeRetriever 0 := by
  apply visited_choice_from_ordered_certificate _ _ [.query 1] [.hydeRetriever 1] [.hydeRetriever 2] (.hydeRetriever 0) (by decide)
  · intro a ha
    have ho : orderedLegalAvailable [.query 1] = [.hydeRetriever 1,.hydeRetriever 0,.hydeRetriever 2] := by decide
    rw [ho] at ha
    simp only [List.mem_cons,List.not_mem_nil,or_false] at ha
    rcases ha with rfl | rfl | rfl <;> decide
  · intro a ha
    simp only [List.mem_cons,List.not_mem_nil,or_false] at ha
    rcases ha with rfl
    · exact favorableCompleteS40D1Cmp0
  · intro a ha
    simp only [List.mem_cons,List.not_mem_nil,or_false] at ha
    rcases ha with rfl
    · exact favorableCompleteS40D1Cmp2

theorem favorableCompleteS40D2I0 : indexScore (7/5) (controlPenalty savedCref uniformQuoteError unitRoleUnused .complete) favorableCompleteS40Before [.query 1,.hydeRetriever 0] (.selection 1) = treeIndex ((0/1)/2) (7/5) 0 9 2 := by
  have hs : replayBackup favorableCompleteS40Before emptyStatistics ([.query 1,.hydeRetriever 0]++[.selection 1]) = ⟨2,(0/1)⟩ := by
    rw [replayBackup_empty_closed_form]
    simp +decide [backedEvents,favorableCompleteS40Before,favorableCompleteProposal,favorableCompleteEvent1,favorableCompleteEvent2,favorableCompleteEvent3,favorableCompleteEvent4,favorableCompleteEvent5,favorableCompleteEvent6,favorableCompleteEvent7,favorableCompleteEvent8,favorableCompleteEvent9,favorableCompleteEvent10,favorableCompleteEvent11,favorableCompleteEvent12,favorableCompleteEvent13,favorableCompleteEvent14,favorableCompleteEvent15,favorableCompleteEvent16,favorableCompleteEvent17,favorableCompleteEvent18,favorableCompleteEvent19,favorableCompleteEvent20,favorableCompleteEvent21,favorableCompleteEvent22,favorableCompleteEvent23,favorableCompleteEvent24,favorableCompleteEvent25,favorableCompleteEvent26,favorableCompleteEvent27,favorableCompleteEvent28,favorableCompleteEvent29,favorableCompleteEvent30,favorableCompleteEvent31,favorableCompleteEvent32,favorableCompleteEvent33,favorableCompleteEvent34,favorableCompleteEvent35,favorableCompleteEvent36,favorableCompleteEvent37,favorableCompleteEvent38,favorableCompleteEvent39,taskReward]
    <;> norm_num
  have hp : rawVisits favorableCompleteS40Before [.query 1,.hydeRetriever 0] = 9 := by decide
  have hn : rawVisits favorableCompleteS40Before ([.query 1,.hydeRetriever 0]++[.selection 1]) = 2 := by decide
  have hz : (controlPenalty savedCref uniformQuoteError unitRoleUnused .complete) favorableCompleteS40Before [.query 1,.hydeRetriever 0] (.selection 1) = 0 := by
    apply control_penalty_empty_of_prior_terminal .complete savedCref uniformQuoteError favorableCompleteS40Before [.query 1,.hydeRetriever 0] (.selection 1) 16 (by decide)
    · decide
    · decide
  unfold indexScore
  rw [hs,hp,hn,hz]
  simp only [BackupStat.mean]
  norm_num

theorem favorableCompleteS40D2I1 : indexScore (7/5) (controlPenalty savedCref uniformQuoteError unitRoleUnused .complete) favorableCompleteS40Before [.query 1,.hydeRetriever 0] (.selection 2) = treeIndex ((0/1)/2) (7/5) 0 9 2 := by
  have hs : replayBackup favorableCompleteS40Before emptyStatistics ([.query 1,.hydeRetriever 0]++[.selection 2]) = ⟨2,(0/1)⟩ := by
    rw [replayBackup_empty_closed_form]
    simp +decide [backedEvents,favorableCompleteS40Before,favorableCompleteProposal,favorableCompleteEvent1,favorableCompleteEvent2,favorableCompleteEvent3,favorableCompleteEvent4,favorableCompleteEvent5,favorableCompleteEvent6,favorableCompleteEvent7,favorableCompleteEvent8,favorableCompleteEvent9,favorableCompleteEvent10,favorableCompleteEvent11,favorableCompleteEvent12,favorableCompleteEvent13,favorableCompleteEvent14,favorableCompleteEvent15,favorableCompleteEvent16,favorableCompleteEvent17,favorableCompleteEvent18,favorableCompleteEvent19,favorableCompleteEvent20,favorableCompleteEvent21,favorableCompleteEvent22,favorableCompleteEvent23,favorableCompleteEvent24,favorableCompleteEvent25,favorableCompleteEvent26,favorableCompleteEvent27,favorableCompleteEvent28,favorableCompleteEvent29,favorableCompleteEvent30,favorableCompleteEvent31,favorableCompleteEvent32,favorableCompleteEvent33,favorableCompleteEvent34,favorableCompleteEvent35,favorableCompleteEvent36,favorableCompleteEvent37,favorableCompleteEvent38,favorableCompleteEvent39,taskReward]
    <;> norm_num
  have hp : rawVisits favorableCompleteS40Before [.query 1,.hydeRetriever 0] = 9 := by decide
  have hn : rawVisits favorableCompleteS40Before ([.query 1,.hydeRetriever 0]++[.selection 2]) = 2 := by decide
  have hz : (controlPenalty savedCref uniformQuoteError unitRoleUnused .complete) favorableCompleteS40Before [.query 1,.hydeRetriever 0] (.selection 2) = 0 := by
    apply control_penalty_empty_of_prior_terminal .complete savedCref uniformQuoteError favorableCompleteS40Before [.query 1,.hydeRetriever 0] (.selection 2) 19 (by decide)
    · decide
    · decide
  unfold indexScore
  rw [hs,hp,hn,hz]
  simp only [BackupStat.mean]
  norm_num

theorem favorableCompleteS40D2I2 : indexScore (7/5) (controlPenalty savedCref uniformQuoteError unitRoleUnused .complete) favorableCompleteS40Before [.query 1,.hydeRetriever 0] (.selection 3) = treeIndex ((0/1)/2) (7/5) 0 9 2 := by
  have hs : replayBackup favorableCompleteS40Before emptyStatistics ([.query 1,.hydeRetriever 0]++[.selection 3]) = ⟨2,(0/1)⟩ := by
    rw [replayBackup_empty_closed_form]
    simp +decide [backedEvents,favorableCompleteS40Before,favorableCompleteProposal,favorableCompleteEvent1,favorableCompleteEvent2,favorableCompleteEvent3,favorableCompleteEvent4,favorableCompleteEvent5,favorableCompleteEvent6,favorableCompleteEvent7,favorableCompleteEvent8,favorableCompleteEvent9,favorableCompleteEvent10,favorableCompleteEvent11,favorableCompleteEvent12,favorableCompleteEvent13,favorableCompleteEvent14,favorableCompleteEvent15,favorableCompleteEvent16,favorableCompleteEvent17,favorableCompleteEvent18,favorableCompleteEvent19,favorableCompleteEvent20,favorableCompleteEvent21,favorableCompleteEvent22,favorableCompleteEvent23,favorableCompleteEvent24,favorableCompleteEvent25,favorableCompleteEvent26,favorableCompleteEvent27,favorableCompleteEvent28,favorableCompleteEvent29,favorableCompleteEvent30,favorableCompleteEvent31,favorableCompleteEvent32,favorableCompleteEvent33,favorableCompleteEvent34,favorableCompleteEvent35,favorableCompleteEvent36,favorableCompleteEvent37,favorableCompleteEvent38,favorableCompleteEvent39,taskReward]
    <;> norm_num
  have hp : rawVisits favorableCompleteS40Before [.query 1,.hydeRetriever 0] = 9 := by decide
  have hn : rawVisits favorableCompleteS40Before ([.query 1,.hydeRetriever 0]++[.selection 3]) = 2 := by decide
  have hz : (controlPenalty savedCref uniformQuoteError unitRoleUnused .complete) favorableCompleteS40Before [.query 1,.hydeRetriever 0] (.selection 3) = 0 := by
    apply control_penalty_empty_of_prior_terminal .complete savedCref uniformQuoteError favorableCompleteS40Before [.query 1,.hydeRetriever 0] (.selection 3) 23 (by decide)
    · decide
    · decide
  unfold indexScore
  rw [hs,hp,hn,hz]
  simp only [BackupStat.mean]
  norm_num

theorem favorableCompleteS40D2I3 : indexScore (7/5) (controlPenalty savedCref uniformQuoteError unitRoleUnused .complete) favorableCompleteS40Before [.query 1,.hydeRetriever 0] (.selection 0) = treeIndex ((0/1)/2) (7/5) 0 9 2 := by
  have hs : replayBackup favorableCompleteS40Before emptyStatistics ([.query 1,.hydeRetriever 0]++[.selection 0]) = ⟨2,(0/1)⟩ := by
    rw [replayBackup_empty_closed_form]
    simp +decide [backedEvents,favorableCompleteS40Before,favorableCompleteProposal,favorableCompleteEvent1,favorableCompleteEvent2,favorableCompleteEvent3,favorableCompleteEvent4,favorableCompleteEvent5,favorableCompleteEvent6,favorableCompleteEvent7,favorableCompleteEvent8,favorableCompleteEvent9,favorableCompleteEvent10,favorableCompleteEvent11,favorableCompleteEvent12,favorableCompleteEvent13,favorableCompleteEvent14,favorableCompleteEvent15,favorableCompleteEvent16,favorableCompleteEvent17,favorableCompleteEvent18,favorableCompleteEvent19,favorableCompleteEvent20,favorableCompleteEvent21,favorableCompleteEvent22,favorableCompleteEvent23,favorableCompleteEvent24,favorableCompleteEvent25,favorableCompleteEvent26,favorableCompleteEvent27,favorableCompleteEvent28,favorableCompleteEvent29,favorableCompleteEvent30,favorableCompleteEvent31,favorableCompleteEvent32,favorableCompleteEvent33,favorableCompleteEvent34,favorableCompleteEvent35,favorableCompleteEvent36,favorableCompleteEvent37,favorableCompleteEvent38,favorableCompleteEvent39,taskReward]
    <;> norm_num
  have hp : rawVisits favorableCompleteS40Before [.query 1,.hydeRetriever 0] = 9 := by decide
  have hn : rawVisits favorableCompleteS40Before ([.query 1,.hydeRetriever 0]++[.selection 0]) = 2 := by decide
  have hz : (controlPenalty savedCref uniformQuoteError unitRoleUnused .complete) favorableCompleteS40Before [.query 1,.hydeRetriever 0] (.selection 0) = 0 := by
    apply control_penalty_empty_of_prior_terminal .complete savedCref uniformQuoteError favorableCompleteS40Before [.query 1,.hydeRetriever 0] (.selection 0) 1 (by decide)
    · decide
    · decide
  unfold indexScore
  rw [hs,hp,hn,hz]
  simp only [BackupStat.mean]
  norm_num

theorem favorableCompleteS40D2Cmp1 : indexScore (7/5) (controlPenalty savedCref uniformQuoteError unitRoleUnused .complete) favorableCompleteS40Before [.query 1,.hydeRetriever 0] (.selection 2) ≤ indexScore (7/5) (controlPenalty savedCref uniformQuoteError unitRoleUnused .complete) favorableCompleteS40Before [.query 1,.hydeRetriever 0] (.selection 1) := by
  rw [favorableCompleteS40D2I1,favorableCompleteS40D2I0]

theorem favorableCompleteS40D2Cmp2 : indexScore (7/5) (controlPenalty savedCref uniformQuoteError unitRoleUnused .complete) favorableCompleteS40Before [.query 1,.hydeRetriever 0] (.selection 3) ≤ indexScore (7/5) (controlPenalty savedCref uniformQuoteError unitRoleUnused .complete) favorableCompleteS40Before [.query 1,.hydeRetriever 0] (.selection 1) := by
  rw [favorableCompleteS40D2I2,favorableCompleteS40D2I0]

theorem favorableCompleteS40D2Cmp3 : indexScore (7/5) (controlPenalty savedCref uniformQuoteError unitRoleUnused .complete) favorableCompleteS40Before [.query 1,.hydeRetriever 0] (.selection 0) ≤ indexScore (7/5) (controlPenalty savedCref uniformQuoteError unitRoleUnused .complete) favorableCompleteS40Before [.query 1,.hydeRetriever 0] (.selection 1) := by
  rw [favorableCompleteS40D2I3,favorableCompleteS40D2I0]

theorem favorableCompleteS40Choice2 : nativeFirstChoice (indexScore (7/5) (controlPenalty savedCref uniformQuoteError unitRoleUnused .complete) favorableCompleteS40Before [.query 1,.hydeRetriever 0]) favorableCompleteS40Before [.query 1,.hydeRetriever 0] = .selection 1 := by
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
    · exact favorableCompleteS40D2Cmp1
    · exact favorableCompleteS40D2Cmp2
    · exact favorableCompleteS40D2Cmp3

theorem favorableCompleteS40ActualEvent : nativeEvent budgetTape (7/5) (controlPenalty savedCref uniformQuoteError unitRoleUnused .complete)
    (taskReward false (2/5) (1/2)) favorableCompleteS40Before = favorableCompleteEvent40 := by
  have hs0 := native_select_existing_step budgetTape (7/5) (controlPenalty savedCref uniformQuoteError unitRoleUnused .complete) favorableCompleteS40Before 8 [] (.query 1)
    (by decide) (by decide) favorableCompleteS40Choice0
  have hs1 := native_select_existing_step budgetTape (7/5) (controlPenalty savedCref uniformQuoteError unitRoleUnused .complete) favorableCompleteS40Before 7 [.query 1] (.hydeRetriever 0)
    (by decide) (by decide) favorableCompleteS40Choice1
  have hs2 := native_select_existing_step budgetTape (7/5) (controlPenalty savedCref uniformQuoteError unitRoleUnused .complete) favorableCompleteS40Before 6 [.query 1,.hydeRetriever 0] (.selection 1)
    (by decide) (by decide) favorableCompleteS40Choice2
  have hnew := native_select_new_step budgetTape (7/5) (controlPenalty savedCref uniformQuoteError unitRoleUnused .complete) favorableCompleteS40Before 5 [.query 1,.hydeRetriever 0,.selection 1]
    [.width 3,.width 1,.width 2] (.width 3) (by decide) (by decide) (by decide) (by decide)
  have hs : nativeSelect budgetTape (7/5) (controlPenalty savedCref uniformQuoteError unitRoleUnused .complete) favorableCompleteS40Before 9 [] = [.query 1,.hydeRetriever 0,.selection 1,.width 3] := by
    rw [hs0]
    change nativeSelect budgetTape (7/5) (controlPenalty savedCref uniformQuoteError unitRoleUnused .complete) favorableCompleteS40Before 8 [.query 1] = _
    rw [hs1]
    change nativeSelect budgetTape (7/5) (controlPenalty savedCref uniformQuoteError unitRoleUnused .complete) favorableCompleteS40Before 7 [.query 1,.hydeRetriever 0] = _
    rw [hs2]
    change nativeSelect budgetTape (7/5) (controlPenalty savedCref uniformQuoteError unitRoleUnused .complete) favorableCompleteS40Before 6 [.query 1,.hydeRetriever 0,.selection 1] = _
    rw [hnew] <;> rfl
  have hr : repairedRollout budgetTape favorableCompleteS40Before 9 [.query 1,.hydeRetriever 0,.selection 1,.width 3] = [.query 1,.hydeRetriever 0,.selection 1,.width 3,.stop,.reranker 0,.topm 0,.context 0,.answer 0] := by decide
  simp only [nativeEvent,hs,hr]
  rfl

def favorableCompleteS41Before := favorableCompleteProposal.take 40

theorem favorableCompleteS41Choice0 : nativeFirstChoice (indexScore (7/5) (controlPenalty savedCref uniformQuoteError unitRoleUnused .complete) favorableCompleteS41Before []) favorableCompleteS41Before [] = .query 1 := by
  apply complete_root_from_physical_gap favorableCompleteS41Before (favorableComplete_prefix_rewards 40) (by decide)
  · intro q; fin_cases q <;> decide
  · exact AgentUCTNextExact.favorable_complete_hyde_root_suffix_empty 40 (by omega)
  · intro q hq
    exact AgentUCTNextExact.favorable_complete_normal_root_physical_quote_exact 40 (by omega) q hq

theorem favorableCompleteS41D1I0 : indexScore (7/5) (controlPenalty savedCref uniformQuoteError unitRoleUnused .complete) favorableCompleteS41Before [.query 1] (.hydeRetriever 1) = treeIndex ((3/2)/13) (7/5) 0 33 13 := by
  have hs : replayBackup favorableCompleteS41Before emptyStatistics ([.query 1]++[.hydeRetriever 1]) = ⟨13,(3/2)⟩ := by
    rw [replayBackup_empty_closed_form]
    simp +decide [backedEvents,favorableCompleteS41Before,favorableCompleteProposal,favorableCompleteEvent1,favorableCompleteEvent2,favorableCompleteEvent3,favorableCompleteEvent4,favorableCompleteEvent5,favorableCompleteEvent6,favorableCompleteEvent7,favorableCompleteEvent8,favorableCompleteEvent9,favorableCompleteEvent10,favorableCompleteEvent11,favorableCompleteEvent12,favorableCompleteEvent13,favorableCompleteEvent14,favorableCompleteEvent15,favorableCompleteEvent16,favorableCompleteEvent17,favorableCompleteEvent18,favorableCompleteEvent19,favorableCompleteEvent20,favorableCompleteEvent21,favorableCompleteEvent22,favorableCompleteEvent23,favorableCompleteEvent24,favorableCompleteEvent25,favorableCompleteEvent26,favorableCompleteEvent27,favorableCompleteEvent28,favorableCompleteEvent29,favorableCompleteEvent30,favorableCompleteEvent31,favorableCompleteEvent32,favorableCompleteEvent33,favorableCompleteEvent34,favorableCompleteEvent35,favorableCompleteEvent36,favorableCompleteEvent37,favorableCompleteEvent38,favorableCompleteEvent39,favorableCompleteEvent40,taskReward]
    <;> norm_num
  have hp : rawVisits favorableCompleteS41Before [.query 1] = 33 := by decide
  have hn : rawVisits favorableCompleteS41Before ([.query 1]++[.hydeRetriever 1]) = 13 := by decide
  have hz : (controlPenalty savedCref uniformQuoteError unitRoleUnused .complete) favorableCompleteS41Before [.query 1] (.hydeRetriever 1) = 0 := by
    apply control_penalty_empty_of_prior_terminal .complete savedCref uniformQuoteError favorableCompleteS41Before [.query 1] (.hydeRetriever 1) 8 (by decide)
    · decide
    · decide
  unfold indexScore
  rw [hs,hp,hn,hz]
  simp only [BackupStat.mean]
  norm_num

theorem favorableCompleteS41D1I1 : indexScore (7/5) (controlPenalty savedCref uniformQuoteError unitRoleUnused .complete) favorableCompleteS41Before [.query 1] (.hydeRetriever 0) = treeIndex ((0/1)/10) (7/5) 0 33 10 := by
  have hs : replayBackup favorableCompleteS41Before emptyStatistics ([.query 1]++[.hydeRetriever 0]) = ⟨10,(0/1)⟩ := by
    rw [replayBackup_empty_closed_form]
    simp +decide [backedEvents,favorableCompleteS41Before,favorableCompleteProposal,favorableCompleteEvent1,favorableCompleteEvent2,favorableCompleteEvent3,favorableCompleteEvent4,favorableCompleteEvent5,favorableCompleteEvent6,favorableCompleteEvent7,favorableCompleteEvent8,favorableCompleteEvent9,favorableCompleteEvent10,favorableCompleteEvent11,favorableCompleteEvent12,favorableCompleteEvent13,favorableCompleteEvent14,favorableCompleteEvent15,favorableCompleteEvent16,favorableCompleteEvent17,favorableCompleteEvent18,favorableCompleteEvent19,favorableCompleteEvent20,favorableCompleteEvent21,favorableCompleteEvent22,favorableCompleteEvent23,favorableCompleteEvent24,favorableCompleteEvent25,favorableCompleteEvent26,favorableCompleteEvent27,favorableCompleteEvent28,favorableCompleteEvent29,favorableCompleteEvent30,favorableCompleteEvent31,favorableCompleteEvent32,favorableCompleteEvent33,favorableCompleteEvent34,favorableCompleteEvent35,favorableCompleteEvent36,favorableCompleteEvent37,favorableCompleteEvent38,favorableCompleteEvent39,favorableCompleteEvent40,taskReward]
    <;> norm_num
  have hp : rawVisits favorableCompleteS41Before [.query 1] = 33 := by decide
  have hn : rawVisits favorableCompleteS41Before ([.query 1]++[.hydeRetriever 0]) = 10 := by decide
  have hz : (controlPenalty savedCref uniformQuoteError unitRoleUnused .complete) favorableCompleteS41Before [.query 1] (.hydeRetriever 0) = 0 := by
    apply control_penalty_empty_of_prior_terminal .complete savedCref uniformQuoteError favorableCompleteS41Before [.query 1] (.hydeRetriever 0) 1 (by decide)
    · decide
    · decide
  unfold indexScore
  rw [hs,hp,hn,hz]
  simp only [BackupStat.mean]
  norm_num

theorem favorableCompleteS41D1I2 : indexScore (7/5) (controlPenalty savedCref uniformQuoteError unitRoleUnused .complete) favorableCompleteS41Before [.query 1] (.hydeRetriever 2) = treeIndex ((0/1)/9) (7/5) 0 33 9 := by
  have hs : replayBackup favorableCompleteS41Before emptyStatistics ([.query 1]++[.hydeRetriever 2]) = ⟨9,(0/1)⟩ := by
    rw [replayBackup_empty_closed_form]
    simp +decide [backedEvents,favorableCompleteS41Before,favorableCompleteProposal,favorableCompleteEvent1,favorableCompleteEvent2,favorableCompleteEvent3,favorableCompleteEvent4,favorableCompleteEvent5,favorableCompleteEvent6,favorableCompleteEvent7,favorableCompleteEvent8,favorableCompleteEvent9,favorableCompleteEvent10,favorableCompleteEvent11,favorableCompleteEvent12,favorableCompleteEvent13,favorableCompleteEvent14,favorableCompleteEvent15,favorableCompleteEvent16,favorableCompleteEvent17,favorableCompleteEvent18,favorableCompleteEvent19,favorableCompleteEvent20,favorableCompleteEvent21,favorableCompleteEvent22,favorableCompleteEvent23,favorableCompleteEvent24,favorableCompleteEvent25,favorableCompleteEvent26,favorableCompleteEvent27,favorableCompleteEvent28,favorableCompleteEvent29,favorableCompleteEvent30,favorableCompleteEvent31,favorableCompleteEvent32,favorableCompleteEvent33,favorableCompleteEvent34,favorableCompleteEvent35,favorableCompleteEvent36,favorableCompleteEvent37,favorableCompleteEvent38,favorableCompleteEvent39,favorableCompleteEvent40,taskReward]
    <;> norm_num
  have hp : rawVisits favorableCompleteS41Before [.query 1] = 33 := by decide
  have hn : rawVisits favorableCompleteS41Before ([.query 1]++[.hydeRetriever 2]) = 9 := by decide
  have hz : (controlPenalty savedCref uniformQuoteError unitRoleUnused .complete) favorableCompleteS41Before [.query 1] (.hydeRetriever 2) = 0 := by
    apply control_penalty_empty_of_prior_terminal .complete savedCref uniformQuoteError favorableCompleteS41Before [.query 1] (.hydeRetriever 2) 10 (by decide)
    · decide
    · decide
  unfold indexScore
  rw [hs,hp,hn,hz]
  simp only [BackupStat.mean]
  norm_num

theorem favorableCompleteS41D1Cmp0 : indexScore (7/5) (controlPenalty savedCref uniformQuoteError unitRoleUnused .complete) favorableCompleteS41Before [.query 1] (.hydeRetriever 1) < indexScore (7/5) (controlPenalty savedCref uniformQuoteError unitRoleUnused .complete) favorableCompleteS41Before [.query 1] (.hydeRetriever 2) := by
  rw [favorableCompleteS41D1I0,favorableCompleteS41D1I2]
  have h := index_strict_order_from_intervals ((0/1)/9) ((3/2)/13) 0 0 (8763349/10000000) (36457743/50000000)
    (treeBonus (7/5) 33 9) (treeBonus (7/5) 33 13)
    (trajectory_bonus_33_9).1 (trajectory_bonus_33_13).2 (by norm_num)
  simpa only [treeIndex,sub_zero] using h

theorem favorableCompleteS41D1Cmp1 : indexScore (7/5) (controlPenalty savedCref uniformQuoteError unitRoleUnused .complete) favorableCompleteS41Before [.query 1] (.hydeRetriever 0) < indexScore (7/5) (controlPenalty savedCref uniformQuoteError unitRoleUnused .complete) favorableCompleteS41Before [.query 1] (.hydeRetriever 2) := by
  rw [favorableCompleteS41D1I1,favorableCompleteS41D1I2]
  have h := index_strict_order_from_intervals ((0/1)/9) ((0/1)/10) 0 0 (8763349/10000000) (41568219/50000000)
    (treeBonus (7/5) 33 9) (treeBonus (7/5) 33 10)
    (trajectory_bonus_33_9).1 (trajectory_bonus_33_10).2 (by norm_num)
  simpa only [treeIndex,sub_zero] using h

theorem favorableCompleteS41Choice1 : nativeFirstChoice (indexScore (7/5) (controlPenalty savedCref uniformQuoteError unitRoleUnused .complete) favorableCompleteS41Before [.query 1]) favorableCompleteS41Before [.query 1] = .hydeRetriever 2 := by
  apply visited_choice_from_ordered_certificate _ _ [.query 1] [.hydeRetriever 1,.hydeRetriever 0] [] (.hydeRetriever 2) (by decide)
  · intro a ha
    have ho : orderedLegalAvailable [.query 1] = [.hydeRetriever 1,.hydeRetriever 0,.hydeRetriever 2] := by decide
    rw [ho] at ha
    simp only [List.mem_cons,List.not_mem_nil,or_false] at ha
    rcases ha with rfl | rfl | rfl <;> decide
  · intro a ha
    simp only [List.mem_cons,List.not_mem_nil,or_false] at ha
    rcases ha with rfl | rfl
    · exact favorableCompleteS41D1Cmp0
    · exact favorableCompleteS41D1Cmp1
  · simp

theorem favorableCompleteS41D2I0 : indexScore (7/5) (controlPenalty savedCref uniformQuoteError unitRoleUnused .complete) favorableCompleteS41Before [.query 1,.hydeRetriever 2] (.selection 1) = treeIndex ((0/1)/2) (7/5) 0 9 2 := by
  have hs : replayBackup favorableCompleteS41Before emptyStatistics ([.query 1,.hydeRetriever 2]++[.selection 1]) = ⟨2,(0/1)⟩ := by
    rw [replayBackup_empty_closed_form]
    simp +decide [backedEvents,favorableCompleteS41Before,favorableCompleteProposal,favorableCompleteEvent1,favorableCompleteEvent2,favorableCompleteEvent3,favorableCompleteEvent4,favorableCompleteEvent5,favorableCompleteEvent6,favorableCompleteEvent7,favorableCompleteEvent8,favorableCompleteEvent9,favorableCompleteEvent10,favorableCompleteEvent11,favorableCompleteEvent12,favorableCompleteEvent13,favorableCompleteEvent14,favorableCompleteEvent15,favorableCompleteEvent16,favorableCompleteEvent17,favorableCompleteEvent18,favorableCompleteEvent19,favorableCompleteEvent20,favorableCompleteEvent21,favorableCompleteEvent22,favorableCompleteEvent23,favorableCompleteEvent24,favorableCompleteEvent25,favorableCompleteEvent26,favorableCompleteEvent27,favorableCompleteEvent28,favorableCompleteEvent29,favorableCompleteEvent30,favorableCompleteEvent31,favorableCompleteEvent32,favorableCompleteEvent33,favorableCompleteEvent34,favorableCompleteEvent35,favorableCompleteEvent36,favorableCompleteEvent37,favorableCompleteEvent38,favorableCompleteEvent39,favorableCompleteEvent40,taskReward]
    <;> norm_num
  have hp : rawVisits favorableCompleteS41Before [.query 1,.hydeRetriever 2] = 9 := by decide
  have hn : rawVisits favorableCompleteS41Before ([.query 1,.hydeRetriever 2]++[.selection 1]) = 2 := by decide
  have hz : (controlPenalty savedCref uniformQuoteError unitRoleUnused .complete) favorableCompleteS41Before [.query 1,.hydeRetriever 2] (.selection 1) = 0 := by
    apply control_penalty_empty_of_prior_terminal .complete savedCref uniformQuoteError favorableCompleteS41Before [.query 1,.hydeRetriever 2] (.selection 1) 17 (by decide)
    · decide
    · decide
  unfold indexScore
  rw [hs,hp,hn,hz]
  simp only [BackupStat.mean]
  norm_num

theorem favorableCompleteS41D2I1 : indexScore (7/5) (controlPenalty savedCref uniformQuoteError unitRoleUnused .complete) favorableCompleteS41Before [.query 1,.hydeRetriever 2] (.selection 2) = treeIndex ((0/1)/2) (7/5) 0 9 2 := by
  have hs : replayBackup favorableCompleteS41Before emptyStatistics ([.query 1,.hydeRetriever 2]++[.selection 2]) = ⟨2,(0/1)⟩ := by
    rw [replayBackup_empty_closed_form]
    simp +decide [backedEvents,favorableCompleteS41Before,favorableCompleteProposal,favorableCompleteEvent1,favorableCompleteEvent2,favorableCompleteEvent3,favorableCompleteEvent4,favorableCompleteEvent5,favorableCompleteEvent6,favorableCompleteEvent7,favorableCompleteEvent8,favorableCompleteEvent9,favorableCompleteEvent10,favorableCompleteEvent11,favorableCompleteEvent12,favorableCompleteEvent13,favorableCompleteEvent14,favorableCompleteEvent15,favorableCompleteEvent16,favorableCompleteEvent17,favorableCompleteEvent18,favorableCompleteEvent19,favorableCompleteEvent20,favorableCompleteEvent21,favorableCompleteEvent22,favorableCompleteEvent23,favorableCompleteEvent24,favorableCompleteEvent25,favorableCompleteEvent26,favorableCompleteEvent27,favorableCompleteEvent28,favorableCompleteEvent29,favorableCompleteEvent30,favorableCompleteEvent31,favorableCompleteEvent32,favorableCompleteEvent33,favorableCompleteEvent34,favorableCompleteEvent35,favorableCompleteEvent36,favorableCompleteEvent37,favorableCompleteEvent38,favorableCompleteEvent39,favorableCompleteEvent40,taskReward]
    <;> norm_num
  have hp : rawVisits favorableCompleteS41Before [.query 1,.hydeRetriever 2] = 9 := by decide
  have hn : rawVisits favorableCompleteS41Before ([.query 1,.hydeRetriever 2]++[.selection 2]) = 2 := by decide
  have hz : (controlPenalty savedCref uniformQuoteError unitRoleUnused .complete) favorableCompleteS41Before [.query 1,.hydeRetriever 2] (.selection 2) = 0 := by
    apply control_penalty_empty_of_prior_terminal .complete savedCref uniformQuoteError favorableCompleteS41Before [.query 1,.hydeRetriever 2] (.selection 2) 20 (by decide)
    · decide
    · decide
  unfold indexScore
  rw [hs,hp,hn,hz]
  simp only [BackupStat.mean]
  norm_num

theorem favorableCompleteS41D2I2 : indexScore (7/5) (controlPenalty savedCref uniformQuoteError unitRoleUnused .complete) favorableCompleteS41Before [.query 1,.hydeRetriever 2] (.selection 3) = treeIndex ((0/1)/2) (7/5) 0 9 2 := by
  have hs : replayBackup favorableCompleteS41Before emptyStatistics ([.query 1,.hydeRetriever 2]++[.selection 3]) = ⟨2,(0/1)⟩ := by
    rw [replayBackup_empty_closed_form]
    simp +decide [backedEvents,favorableCompleteS41Before,favorableCompleteProposal,favorableCompleteEvent1,favorableCompleteEvent2,favorableCompleteEvent3,favorableCompleteEvent4,favorableCompleteEvent5,favorableCompleteEvent6,favorableCompleteEvent7,favorableCompleteEvent8,favorableCompleteEvent9,favorableCompleteEvent10,favorableCompleteEvent11,favorableCompleteEvent12,favorableCompleteEvent13,favorableCompleteEvent14,favorableCompleteEvent15,favorableCompleteEvent16,favorableCompleteEvent17,favorableCompleteEvent18,favorableCompleteEvent19,favorableCompleteEvent20,favorableCompleteEvent21,favorableCompleteEvent22,favorableCompleteEvent23,favorableCompleteEvent24,favorableCompleteEvent25,favorableCompleteEvent26,favorableCompleteEvent27,favorableCompleteEvent28,favorableCompleteEvent29,favorableCompleteEvent30,favorableCompleteEvent31,favorableCompleteEvent32,favorableCompleteEvent33,favorableCompleteEvent34,favorableCompleteEvent35,favorableCompleteEvent36,favorableCompleteEvent37,favorableCompleteEvent38,favorableCompleteEvent39,favorableCompleteEvent40,taskReward]
    <;> norm_num
  have hp : rawVisits favorableCompleteS41Before [.query 1,.hydeRetriever 2] = 9 := by decide
  have hn : rawVisits favorableCompleteS41Before ([.query 1,.hydeRetriever 2]++[.selection 3]) = 2 := by decide
  have hz : (controlPenalty savedCref uniformQuoteError unitRoleUnused .complete) favorableCompleteS41Before [.query 1,.hydeRetriever 2] (.selection 3) = 0 := by
    apply control_penalty_empty_of_prior_terminal .complete savedCref uniformQuoteError favorableCompleteS41Before [.query 1,.hydeRetriever 2] (.selection 3) 24 (by decide)
    · decide
    · decide
  unfold indexScore
  rw [hs,hp,hn,hz]
  simp only [BackupStat.mean]
  norm_num

theorem favorableCompleteS41D2I3 : indexScore (7/5) (controlPenalty savedCref uniformQuoteError unitRoleUnused .complete) favorableCompleteS41Before [.query 1,.hydeRetriever 2] (.selection 0) = treeIndex ((0/1)/2) (7/5) 0 9 2 := by
  have hs : replayBackup favorableCompleteS41Before emptyStatistics ([.query 1,.hydeRetriever 2]++[.selection 0]) = ⟨2,(0/1)⟩ := by
    rw [replayBackup_empty_closed_form]
    simp +decide [backedEvents,favorableCompleteS41Before,favorableCompleteProposal,favorableCompleteEvent1,favorableCompleteEvent2,favorableCompleteEvent3,favorableCompleteEvent4,favorableCompleteEvent5,favorableCompleteEvent6,favorableCompleteEvent7,favorableCompleteEvent8,favorableCompleteEvent9,favorableCompleteEvent10,favorableCompleteEvent11,favorableCompleteEvent12,favorableCompleteEvent13,favorableCompleteEvent14,favorableCompleteEvent15,favorableCompleteEvent16,favorableCompleteEvent17,favorableCompleteEvent18,favorableCompleteEvent19,favorableCompleteEvent20,favorableCompleteEvent21,favorableCompleteEvent22,favorableCompleteEvent23,favorableCompleteEvent24,favorableCompleteEvent25,favorableCompleteEvent26,favorableCompleteEvent27,favorableCompleteEvent28,favorableCompleteEvent29,favorableCompleteEvent30,favorableCompleteEvent31,favorableCompleteEvent32,favorableCompleteEvent33,favorableCompleteEvent34,favorableCompleteEvent35,favorableCompleteEvent36,favorableCompleteEvent37,favorableCompleteEvent38,favorableCompleteEvent39,favorableCompleteEvent40,taskReward]
    <;> norm_num
  have hp : rawVisits favorableCompleteS41Before [.query 1,.hydeRetriever 2] = 9 := by decide
  have hn : rawVisits favorableCompleteS41Before ([.query 1,.hydeRetriever 2]++[.selection 0]) = 2 := by decide
  have hz : (controlPenalty savedCref uniformQuoteError unitRoleUnused .complete) favorableCompleteS41Before [.query 1,.hydeRetriever 2] (.selection 0) = 0 := by
    apply control_penalty_empty_of_prior_terminal .complete savedCref uniformQuoteError favorableCompleteS41Before [.query 1,.hydeRetriever 2] (.selection 0) 10 (by decide)
    · decide
    · decide
  unfold indexScore
  rw [hs,hp,hn,hz]
  simp only [BackupStat.mean]
  norm_num

theorem favorableCompleteS41D2Cmp1 : indexScore (7/5) (controlPenalty savedCref uniformQuoteError unitRoleUnused .complete) favorableCompleteS41Before [.query 1,.hydeRetriever 2] (.selection 2) ≤ indexScore (7/5) (controlPenalty savedCref uniformQuoteError unitRoleUnused .complete) favorableCompleteS41Before [.query 1,.hydeRetriever 2] (.selection 1) := by
  rw [favorableCompleteS41D2I1,favorableCompleteS41D2I0]

theorem favorableCompleteS41D2Cmp2 : indexScore (7/5) (controlPenalty savedCref uniformQuoteError unitRoleUnused .complete) favorableCompleteS41Before [.query 1,.hydeRetriever 2] (.selection 3) ≤ indexScore (7/5) (controlPenalty savedCref uniformQuoteError unitRoleUnused .complete) favorableCompleteS41Before [.query 1,.hydeRetriever 2] (.selection 1) := by
  rw [favorableCompleteS41D2I2,favorableCompleteS41D2I0]

theorem favorableCompleteS41D2Cmp3 : indexScore (7/5) (controlPenalty savedCref uniformQuoteError unitRoleUnused .complete) favorableCompleteS41Before [.query 1,.hydeRetriever 2] (.selection 0) ≤ indexScore (7/5) (controlPenalty savedCref uniformQuoteError unitRoleUnused .complete) favorableCompleteS41Before [.query 1,.hydeRetriever 2] (.selection 1) := by
  rw [favorableCompleteS41D2I3,favorableCompleteS41D2I0]

theorem favorableCompleteS41Choice2 : nativeFirstChoice (indexScore (7/5) (controlPenalty savedCref uniformQuoteError unitRoleUnused .complete) favorableCompleteS41Before [.query 1,.hydeRetriever 2]) favorableCompleteS41Before [.query 1,.hydeRetriever 2] = .selection 1 := by
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
    · exact favorableCompleteS41D2Cmp1
    · exact favorableCompleteS41D2Cmp2
    · exact favorableCompleteS41D2Cmp3

theorem favorableCompleteS41ActualEvent : nativeEvent budgetTape (7/5) (controlPenalty savedCref uniformQuoteError unitRoleUnused .complete)
    (taskReward false (2/5) (1/2)) favorableCompleteS41Before = favorableCompleteEvent41 := by
  have hs0 := native_select_existing_step budgetTape (7/5) (controlPenalty savedCref uniformQuoteError unitRoleUnused .complete) favorableCompleteS41Before 8 [] (.query 1)
    (by decide) (by decide) favorableCompleteS41Choice0
  have hs1 := native_select_existing_step budgetTape (7/5) (controlPenalty savedCref uniformQuoteError unitRoleUnused .complete) favorableCompleteS41Before 7 [.query 1] (.hydeRetriever 2)
    (by decide) (by decide) favorableCompleteS41Choice1
  have hs2 := native_select_existing_step budgetTape (7/5) (controlPenalty savedCref uniformQuoteError unitRoleUnused .complete) favorableCompleteS41Before 6 [.query 1,.hydeRetriever 2] (.selection 1)
    (by decide) (by decide) favorableCompleteS41Choice2
  have hnew := native_select_new_step budgetTape (7/5) (controlPenalty savedCref uniformQuoteError unitRoleUnused .complete) favorableCompleteS41Before 5 [.query 1,.hydeRetriever 2,.selection 1]
    [.width 3,.width 1,.width 2] (.width 3) (by decide) (by decide) (by decide) (by decide)
  have hs : nativeSelect budgetTape (7/5) (controlPenalty savedCref uniformQuoteError unitRoleUnused .complete) favorableCompleteS41Before 9 [] = [.query 1,.hydeRetriever 2,.selection 1,.width 3] := by
    rw [hs0]
    change nativeSelect budgetTape (7/5) (controlPenalty savedCref uniformQuoteError unitRoleUnused .complete) favorableCompleteS41Before 8 [.query 1] = _
    rw [hs1]
    change nativeSelect budgetTape (7/5) (controlPenalty savedCref uniformQuoteError unitRoleUnused .complete) favorableCompleteS41Before 7 [.query 1,.hydeRetriever 2] = _
    rw [hs2]
    change nativeSelect budgetTape (7/5) (controlPenalty savedCref uniformQuoteError unitRoleUnused .complete) favorableCompleteS41Before 6 [.query 1,.hydeRetriever 2,.selection 1] = _
    rw [hnew] <;> rfl
  have hr : repairedRollout budgetTape favorableCompleteS41Before 9 [.query 1,.hydeRetriever 2,.selection 1,.width 3] = [.query 1,.hydeRetriever 2,.selection 1,.width 3,.stop,.reranker 0,.topm 0,.context 0,.answer 0] := by decide
  simp only [nativeEvent,hs,hr]
  rfl

def favorableCompleteS42Before := favorableCompleteProposal.take 41

theorem favorableCompleteS42Choice0 : nativeFirstChoice (indexScore (7/5) (controlPenalty savedCref uniformQuoteError unitRoleUnused .complete) favorableCompleteS42Before []) favorableCompleteS42Before [] = .query 1 := by
  apply complete_root_from_physical_gap favorableCompleteS42Before (favorableComplete_prefix_rewards 41) (by decide)
  · intro q; fin_cases q <;> decide
  · exact AgentUCTNextExact.favorable_complete_hyde_root_suffix_empty 41 (by omega)
  · intro q hq
    exact AgentUCTNextExact.favorable_complete_normal_root_physical_quote_exact 41 (by omega) q hq

theorem favorableCompleteS42D1I0 : indexScore (7/5) (controlPenalty savedCref uniformQuoteError unitRoleUnused .complete) favorableCompleteS42Before [.query 1] (.hydeRetriever 1) = treeIndex ((3/2)/13) (7/5) 0 34 13 := by
  have hs : replayBackup favorableCompleteS42Before emptyStatistics ([.query 1]++[.hydeRetriever 1]) = ⟨13,(3/2)⟩ := by
    rw [replayBackup_empty_closed_form]
    simp +decide [backedEvents,favorableCompleteS42Before,favorableCompleteProposal,favorableCompleteEvent1,favorableCompleteEvent2,favorableCompleteEvent3,favorableCompleteEvent4,favorableCompleteEvent5,favorableCompleteEvent6,favorableCompleteEvent7,favorableCompleteEvent8,favorableCompleteEvent9,favorableCompleteEvent10,favorableCompleteEvent11,favorableCompleteEvent12,favorableCompleteEvent13,favorableCompleteEvent14,favorableCompleteEvent15,favorableCompleteEvent16,favorableCompleteEvent17,favorableCompleteEvent18,favorableCompleteEvent19,favorableCompleteEvent20,favorableCompleteEvent21,favorableCompleteEvent22,favorableCompleteEvent23,favorableCompleteEvent24,favorableCompleteEvent25,favorableCompleteEvent26,favorableCompleteEvent27,favorableCompleteEvent28,favorableCompleteEvent29,favorableCompleteEvent30,favorableCompleteEvent31,favorableCompleteEvent32,favorableCompleteEvent33,favorableCompleteEvent34,favorableCompleteEvent35,favorableCompleteEvent36,favorableCompleteEvent37,favorableCompleteEvent38,favorableCompleteEvent39,favorableCompleteEvent40,favorableCompleteEvent41,taskReward]
    <;> norm_num
  have hp : rawVisits favorableCompleteS42Before [.query 1] = 34 := by decide
  have hn : rawVisits favorableCompleteS42Before ([.query 1]++[.hydeRetriever 1]) = 13 := by decide
  have hz : (controlPenalty savedCref uniformQuoteError unitRoleUnused .complete) favorableCompleteS42Before [.query 1] (.hydeRetriever 1) = 0 := by
    apply control_penalty_empty_of_prior_terminal .complete savedCref uniformQuoteError favorableCompleteS42Before [.query 1] (.hydeRetriever 1) 8 (by decide)
    · decide
    · decide
  unfold indexScore
  rw [hs,hp,hn,hz]
  simp only [BackupStat.mean]
  norm_num

theorem favorableCompleteS42D1I1 : indexScore (7/5) (controlPenalty savedCref uniformQuoteError unitRoleUnused .complete) favorableCompleteS42Before [.query 1] (.hydeRetriever 0) = treeIndex ((0/1)/10) (7/5) 0 34 10 := by
  have hs : replayBackup favorableCompleteS42Before emptyStatistics ([.query 1]++[.hydeRetriever 0]) = ⟨10,(0/1)⟩ := by
    rw [replayBackup_empty_closed_form]
    simp +decide [backedEvents,favorableCompleteS42Before,favorableCompleteProposal,favorableCompleteEvent1,favorableCompleteEvent2,favorableCompleteEvent3,favorableCompleteEvent4,favorableCompleteEvent5,favorableCompleteEvent6,favorableCompleteEvent7,favorableCompleteEvent8,favorableCompleteEvent9,favorableCompleteEvent10,favorableCompleteEvent11,favorableCompleteEvent12,favorableCompleteEvent13,favorableCompleteEvent14,favorableCompleteEvent15,favorableCompleteEvent16,favorableCompleteEvent17,favorableCompleteEvent18,favorableCompleteEvent19,favorableCompleteEvent20,favorableCompleteEvent21,favorableCompleteEvent22,favorableCompleteEvent23,favorableCompleteEvent24,favorableCompleteEvent25,favorableCompleteEvent26,favorableCompleteEvent27,favorableCompleteEvent28,favorableCompleteEvent29,favorableCompleteEvent30,favorableCompleteEvent31,favorableCompleteEvent32,favorableCompleteEvent33,favorableCompleteEvent34,favorableCompleteEvent35,favorableCompleteEvent36,favorableCompleteEvent37,favorableCompleteEvent38,favorableCompleteEvent39,favorableCompleteEvent40,favorableCompleteEvent41,taskReward]
    <;> norm_num
  have hp : rawVisits favorableCompleteS42Before [.query 1] = 34 := by decide
  have hn : rawVisits favorableCompleteS42Before ([.query 1]++[.hydeRetriever 0]) = 10 := by decide
  have hz : (controlPenalty savedCref uniformQuoteError unitRoleUnused .complete) favorableCompleteS42Before [.query 1] (.hydeRetriever 0) = 0 := by
    apply control_penalty_empty_of_prior_terminal .complete savedCref uniformQuoteError favorableCompleteS42Before [.query 1] (.hydeRetriever 0) 1 (by decide)
    · decide
    · decide
  unfold indexScore
  rw [hs,hp,hn,hz]
  simp only [BackupStat.mean]
  norm_num

theorem favorableCompleteS42D1I2 : indexScore (7/5) (controlPenalty savedCref uniformQuoteError unitRoleUnused .complete) favorableCompleteS42Before [.query 1] (.hydeRetriever 2) = treeIndex ((0/1)/10) (7/5) 0 34 10 := by
  have hs : replayBackup favorableCompleteS42Before emptyStatistics ([.query 1]++[.hydeRetriever 2]) = ⟨10,(0/1)⟩ := by
    rw [replayBackup_empty_closed_form]
    simp +decide [backedEvents,favorableCompleteS42Before,favorableCompleteProposal,favorableCompleteEvent1,favorableCompleteEvent2,favorableCompleteEvent3,favorableCompleteEvent4,favorableCompleteEvent5,favorableCompleteEvent6,favorableCompleteEvent7,favorableCompleteEvent8,favorableCompleteEvent9,favorableCompleteEvent10,favorableCompleteEvent11,favorableCompleteEvent12,favorableCompleteEvent13,favorableCompleteEvent14,favorableCompleteEvent15,favorableCompleteEvent16,favorableCompleteEvent17,favorableCompleteEvent18,favorableCompleteEvent19,favorableCompleteEvent20,favorableCompleteEvent21,favorableCompleteEvent22,favorableCompleteEvent23,favorableCompleteEvent24,favorableCompleteEvent25,favorableCompleteEvent26,favorableCompleteEvent27,favorableCompleteEvent28,favorableCompleteEvent29,favorableCompleteEvent30,favorableCompleteEvent31,favorableCompleteEvent32,favorableCompleteEvent33,favorableCompleteEvent34,favorableCompleteEvent35,favorableCompleteEvent36,favorableCompleteEvent37,favorableCompleteEvent38,favorableCompleteEvent39,favorableCompleteEvent40,favorableCompleteEvent41,taskReward]
    <;> norm_num
  have hp : rawVisits favorableCompleteS42Before [.query 1] = 34 := by decide
  have hn : rawVisits favorableCompleteS42Before ([.query 1]++[.hydeRetriever 2]) = 10 := by decide
  have hz : (controlPenalty savedCref uniformQuoteError unitRoleUnused .complete) favorableCompleteS42Before [.query 1] (.hydeRetriever 2) = 0 := by
    apply control_penalty_empty_of_prior_terminal .complete savedCref uniformQuoteError favorableCompleteS42Before [.query 1] (.hydeRetriever 2) 10 (by decide)
    · decide
    · decide
  unfold indexScore
  rw [hs,hp,hn,hz]
  simp only [BackupStat.mean]
  norm_num

theorem favorableCompleteS42D1Cmp1 : indexScore (7/5) (controlPenalty savedCref uniformQuoteError unitRoleUnused .complete) favorableCompleteS42Before [.query 1] (.hydeRetriever 0) ≤ indexScore (7/5) (controlPenalty savedCref uniformQuoteError unitRoleUnused .complete) favorableCompleteS42Before [.query 1] (.hydeRetriever 1) := by
  rw [favorableCompleteS42D1I1,favorableCompleteS42D1I0]
  have h := index_weak_order_from_intervals ((3/2)/13) ((0/1)/10) 0 0 (3660727/5000000) (1669549/2000000)
    (treeBonus (7/5) 34 13) (treeBonus (7/5) 34 10)
    (trajectory_bonus_34_13).1 (trajectory_bonus_34_10).2 (by norm_num)
  simpa only [treeIndex,sub_zero] using h

theorem favorableCompleteS42D1Cmp2 : indexScore (7/5) (controlPenalty savedCref uniformQuoteError unitRoleUnused .complete) favorableCompleteS42Before [.query 1] (.hydeRetriever 2) ≤ indexScore (7/5) (controlPenalty savedCref uniformQuoteError unitRoleUnused .complete) favorableCompleteS42Before [.query 1] (.hydeRetriever 1) := by
  rw [favorableCompleteS42D1I2,favorableCompleteS42D1I0]
  have h := index_weak_order_from_intervals ((3/2)/13) ((0/1)/10) 0 0 (3660727/5000000) (1669549/2000000)
    (treeBonus (7/5) 34 13) (treeBonus (7/5) 34 10)
    (trajectory_bonus_34_13).1 (trajectory_bonus_34_10).2 (by norm_num)
  simpa only [treeIndex,sub_zero] using h

theorem favorableCompleteS42Choice1 : nativeFirstChoice (indexScore (7/5) (controlPenalty savedCref uniformQuoteError unitRoleUnused .complete) favorableCompleteS42Before [.query 1]) favorableCompleteS42Before [.query 1] = .hydeRetriever 1 := by
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
    · exact favorableCompleteS42D1Cmp1
    · exact favorableCompleteS42D1Cmp2

theorem favorableCompleteS42D2I0 : indexScore (7/5) (controlPenalty savedCref uniformQuoteError unitRoleUnused .complete) favorableCompleteS42Before [.query 1,.hydeRetriever 1] (.selection 1) = treeIndex ((0/1)/3) (7/5) 0 13 3 := by
  have hs : replayBackup favorableCompleteS42Before emptyStatistics ([.query 1,.hydeRetriever 1]++[.selection 1]) = ⟨3,(0/1)⟩ := by
    rw [replayBackup_empty_closed_form]
    simp +decide [backedEvents,favorableCompleteS42Before,favorableCompleteProposal,favorableCompleteEvent1,favorableCompleteEvent2,favorableCompleteEvent3,favorableCompleteEvent4,favorableCompleteEvent5,favorableCompleteEvent6,favorableCompleteEvent7,favorableCompleteEvent8,favorableCompleteEvent9,favorableCompleteEvent10,favorableCompleteEvent11,favorableCompleteEvent12,favorableCompleteEvent13,favorableCompleteEvent14,favorableCompleteEvent15,favorableCompleteEvent16,favorableCompleteEvent17,favorableCompleteEvent18,favorableCompleteEvent19,favorableCompleteEvent20,favorableCompleteEvent21,favorableCompleteEvent22,favorableCompleteEvent23,favorableCompleteEvent24,favorableCompleteEvent25,favorableCompleteEvent26,favorableCompleteEvent27,favorableCompleteEvent28,favorableCompleteEvent29,favorableCompleteEvent30,favorableCompleteEvent31,favorableCompleteEvent32,favorableCompleteEvent33,favorableCompleteEvent34,favorableCompleteEvent35,favorableCompleteEvent36,favorableCompleteEvent37,favorableCompleteEvent38,favorableCompleteEvent39,favorableCompleteEvent40,favorableCompleteEvent41,taskReward]
    <;> norm_num
  have hp : rawVisits favorableCompleteS42Before [.query 1,.hydeRetriever 1] = 13 := by decide
  have hn : rawVisits favorableCompleteS42Before ([.query 1,.hydeRetriever 1]++[.selection 1]) = 3 := by decide
  have hz : (controlPenalty savedCref uniformQuoteError unitRoleUnused .complete) favorableCompleteS42Before [.query 1,.hydeRetriever 1] (.selection 1) = 0 := by
    apply control_penalty_empty_of_prior_terminal .complete savedCref uniformQuoteError favorableCompleteS42Before [.query 1,.hydeRetriever 1] (.selection 1) 14 (by decide)
    · decide
    · decide
  unfold indexScore
  rw [hs,hp,hn,hz]
  simp only [BackupStat.mean]
  norm_num

theorem favorableCompleteS42D2I1 : indexScore (7/5) (controlPenalty savedCref uniformQuoteError unitRoleUnused .complete) favorableCompleteS42Before [.query 1,.hydeRetriever 1] (.selection 2) = treeIndex ((0/1)/3) (7/5) 0 13 3 := by
  have hs : replayBackup favorableCompleteS42Before emptyStatistics ([.query 1,.hydeRetriever 1]++[.selection 2]) = ⟨3,(0/1)⟩ := by
    rw [replayBackup_empty_closed_form]
    simp +decide [backedEvents,favorableCompleteS42Before,favorableCompleteProposal,favorableCompleteEvent1,favorableCompleteEvent2,favorableCompleteEvent3,favorableCompleteEvent4,favorableCompleteEvent5,favorableCompleteEvent6,favorableCompleteEvent7,favorableCompleteEvent8,favorableCompleteEvent9,favorableCompleteEvent10,favorableCompleteEvent11,favorableCompleteEvent12,favorableCompleteEvent13,favorableCompleteEvent14,favorableCompleteEvent15,favorableCompleteEvent16,favorableCompleteEvent17,favorableCompleteEvent18,favorableCompleteEvent19,favorableCompleteEvent20,favorableCompleteEvent21,favorableCompleteEvent22,favorableCompleteEvent23,favorableCompleteEvent24,favorableCompleteEvent25,favorableCompleteEvent26,favorableCompleteEvent27,favorableCompleteEvent28,favorableCompleteEvent29,favorableCompleteEvent30,favorableCompleteEvent31,favorableCompleteEvent32,favorableCompleteEvent33,favorableCompleteEvent34,favorableCompleteEvent35,favorableCompleteEvent36,favorableCompleteEvent37,favorableCompleteEvent38,favorableCompleteEvent39,favorableCompleteEvent40,favorableCompleteEvent41,taskReward]
    <;> norm_num
  have hp : rawVisits favorableCompleteS42Before [.query 1,.hydeRetriever 1] = 13 := by decide
  have hn : rawVisits favorableCompleteS42Before ([.query 1,.hydeRetriever 1]++[.selection 2]) = 3 := by decide
  have hz : (controlPenalty savedCref uniformQuoteError unitRoleUnused .complete) favorableCompleteS42Before [.query 1,.hydeRetriever 1] (.selection 2) = 0 := by
    apply control_penalty_empty_of_prior_terminal .complete savedCref uniformQuoteError favorableCompleteS42Before [.query 1,.hydeRetriever 1] (.selection 2) 15 (by decide)
    · decide
    · decide
  unfold indexScore
  rw [hs,hp,hn,hz]
  simp only [BackupStat.mean]
  norm_num

theorem favorableCompleteS42D2I2 : indexScore (7/5) (controlPenalty savedCref uniformQuoteError unitRoleUnused .complete) favorableCompleteS42Before [.query 1,.hydeRetriever 1] (.selection 3) = treeIndex ((0/1)/2) (7/5) 0 13 2 := by
  have hs : replayBackup favorableCompleteS42Before emptyStatistics ([.query 1,.hydeRetriever 1]++[.selection 3]) = ⟨2,(0/1)⟩ := by
    rw [replayBackup_empty_closed_form]
    simp +decide [backedEvents,favorableCompleteS42Before,favorableCompleteProposal,favorableCompleteEvent1,favorableCompleteEvent2,favorableCompleteEvent3,favorableCompleteEvent4,favorableCompleteEvent5,favorableCompleteEvent6,favorableCompleteEvent7,favorableCompleteEvent8,favorableCompleteEvent9,favorableCompleteEvent10,favorableCompleteEvent11,favorableCompleteEvent12,favorableCompleteEvent13,favorableCompleteEvent14,favorableCompleteEvent15,favorableCompleteEvent16,favorableCompleteEvent17,favorableCompleteEvent18,favorableCompleteEvent19,favorableCompleteEvent20,favorableCompleteEvent21,favorableCompleteEvent22,favorableCompleteEvent23,favorableCompleteEvent24,favorableCompleteEvent25,favorableCompleteEvent26,favorableCompleteEvent27,favorableCompleteEvent28,favorableCompleteEvent29,favorableCompleteEvent30,favorableCompleteEvent31,favorableCompleteEvent32,favorableCompleteEvent33,favorableCompleteEvent34,favorableCompleteEvent35,favorableCompleteEvent36,favorableCompleteEvent37,favorableCompleteEvent38,favorableCompleteEvent39,favorableCompleteEvent40,favorableCompleteEvent41,taskReward]
    <;> norm_num
  have hp : rawVisits favorableCompleteS42Before [.query 1,.hydeRetriever 1] = 13 := by decide
  have hn : rawVisits favorableCompleteS42Before ([.query 1,.hydeRetriever 1]++[.selection 3]) = 2 := by decide
  have hz : (controlPenalty savedCref uniformQuoteError unitRoleUnused .complete) favorableCompleteS42Before [.query 1,.hydeRetriever 1] (.selection 3) = 0 := by
    apply control_penalty_empty_of_prior_terminal .complete savedCref uniformQuoteError favorableCompleteS42Before [.query 1,.hydeRetriever 1] (.selection 3) 18 (by decide)
    · decide
    · decide
  unfold indexScore
  rw [hs,hp,hn,hz]
  simp only [BackupStat.mean]
  norm_num

theorem favorableCompleteS42D2I3 : indexScore (7/5) (controlPenalty savedCref uniformQuoteError unitRoleUnused .complete) favorableCompleteS42Before [.query 1,.hydeRetriever 1] (.selection 0) = treeIndex ((1/1)/4) (7/5) 0 13 4 := by
  have hs : replayBackup favorableCompleteS42Before emptyStatistics ([.query 1,.hydeRetriever 1]++[.selection 0]) = ⟨4,(1/1)⟩ := by
    rw [replayBackup_empty_closed_form]
    simp +decide [backedEvents,favorableCompleteS42Before,favorableCompleteProposal,favorableCompleteEvent1,favorableCompleteEvent2,favorableCompleteEvent3,favorableCompleteEvent4,favorableCompleteEvent5,favorableCompleteEvent6,favorableCompleteEvent7,favorableCompleteEvent8,favorableCompleteEvent9,favorableCompleteEvent10,favorableCompleteEvent11,favorableCompleteEvent12,favorableCompleteEvent13,favorableCompleteEvent14,favorableCompleteEvent15,favorableCompleteEvent16,favorableCompleteEvent17,favorableCompleteEvent18,favorableCompleteEvent19,favorableCompleteEvent20,favorableCompleteEvent21,favorableCompleteEvent22,favorableCompleteEvent23,favorableCompleteEvent24,favorableCompleteEvent25,favorableCompleteEvent26,favorableCompleteEvent27,favorableCompleteEvent28,favorableCompleteEvent29,favorableCompleteEvent30,favorableCompleteEvent31,favorableCompleteEvent32,favorableCompleteEvent33,favorableCompleteEvent34,favorableCompleteEvent35,favorableCompleteEvent36,favorableCompleteEvent37,favorableCompleteEvent38,favorableCompleteEvent39,favorableCompleteEvent40,favorableCompleteEvent41,taskReward]
    <;> norm_num
  have hp : rawVisits favorableCompleteS42Before [.query 1,.hydeRetriever 1] = 13 := by decide
  have hn : rawVisits favorableCompleteS42Before ([.query 1,.hydeRetriever 1]++[.selection 0]) = 4 := by decide
  have hz : (controlPenalty savedCref uniformQuoteError unitRoleUnused .complete) favorableCompleteS42Before [.query 1,.hydeRetriever 1] (.selection 0) = 0 := by
    apply control_penalty_empty_of_prior_terminal .complete savedCref uniformQuoteError favorableCompleteS42Before [.query 1,.hydeRetriever 1] (.selection 0) 8 (by decide)
    · decide
    · decide
  unfold indexScore
  rw [hs,hp,hn,hz]
  simp only [BackupStat.mean]
  norm_num

theorem favorableCompleteS42D2Cmp0 : indexScore (7/5) (controlPenalty savedCref uniformQuoteError unitRoleUnused .complete) favorableCompleteS42Before [.query 1,.hydeRetriever 1] (.selection 1) < indexScore (7/5) (controlPenalty savedCref uniformQuoteError unitRoleUnused .complete) favorableCompleteS42Before [.query 1,.hydeRetriever 1] (.selection 3) := by
  rw [favorableCompleteS42D2I0,favorableCompleteS42D2I2]
  have h := index_strict_order_from_intervals ((0/1)/2) ((0/1)/3) 0 0 (80409511/50000000) (65654099/50000000)
    (treeBonus (7/5) 13 2) (treeBonus (7/5) 13 3)
    (trajectory_bonus_13_2).1 (trajectory_bonus_13_3).2 (by norm_num)
  simpa only [treeIndex,sub_zero] using h

theorem favorableCompleteS42D2Cmp1 : indexScore (7/5) (controlPenalty savedCref uniformQuoteError unitRoleUnused .complete) favorableCompleteS42Before [.query 1,.hydeRetriever 1] (.selection 2) < indexScore (7/5) (controlPenalty savedCref uniformQuoteError unitRoleUnused .complete) favorableCompleteS42Before [.query 1,.hydeRetriever 1] (.selection 3) := by
  rw [favorableCompleteS42D2I1,favorableCompleteS42D2I2]
  have h := index_strict_order_from_intervals ((0/1)/2) ((0/1)/3) 0 0 (80409511/50000000) (65654099/50000000)
    (treeBonus (7/5) 13 2) (treeBonus (7/5) 13 3)
    (trajectory_bonus_13_2).1 (trajectory_bonus_13_3).2 (by norm_num)
  simpa only [treeIndex,sub_zero] using h

theorem favorableCompleteS42D2Cmp3 : indexScore (7/5) (controlPenalty savedCref uniformQuoteError unitRoleUnused .complete) favorableCompleteS42Before [.query 1,.hydeRetriever 1] (.selection 0) ≤ indexScore (7/5) (controlPenalty savedCref uniformQuoteError unitRoleUnused .complete) favorableCompleteS42Before [.query 1,.hydeRetriever 1] (.selection 3) := by
  rw [favorableCompleteS42D2I3,favorableCompleteS42D2I2]
  have h := index_weak_order_from_intervals ((0/1)/2) ((1/1)/4) 0 0 (80409511/50000000) (14214529/12500000)
    (treeBonus (7/5) 13 2) (treeBonus (7/5) 13 4)
    (trajectory_bonus_13_2).1 (trajectory_bonus_13_4).2 (by norm_num)
  simpa only [treeIndex,sub_zero] using h

theorem favorableCompleteS42Choice2 : nativeFirstChoice (indexScore (7/5) (controlPenalty savedCref uniformQuoteError unitRoleUnused .complete) favorableCompleteS42Before [.query 1,.hydeRetriever 1]) favorableCompleteS42Before [.query 1,.hydeRetriever 1] = .selection 3 := by
  apply visited_choice_from_ordered_certificate _ _ [.query 1,.hydeRetriever 1] [.selection 1,.selection 2] [.selection 0] (.selection 3) (by decide)
  · intro a ha
    have ho : orderedLegalAvailable [.query 1,.hydeRetriever 1] = [.selection 1,.selection 2,.selection 3,.selection 0] := by decide
    rw [ho] at ha
    simp only [List.mem_cons,List.not_mem_nil,or_false] at ha
    rcases ha with rfl | rfl | rfl | rfl <;> decide
  · intro a ha
    simp only [List.mem_cons,List.not_mem_nil,or_false] at ha
    rcases ha with rfl | rfl
    · exact favorableCompleteS42D2Cmp0
    · exact favorableCompleteS42D2Cmp1
  · intro a ha
    simp only [List.mem_cons,List.not_mem_nil,or_false] at ha
    rcases ha with rfl
    · exact favorableCompleteS42D2Cmp3

theorem favorableCompleteS42ActualEvent : nativeEvent budgetTape (7/5) (controlPenalty savedCref uniformQuoteError unitRoleUnused .complete)
    (taskReward false (2/5) (1/2)) favorableCompleteS42Before = favorableCompleteEvent42 := by
  have hs0 := native_select_existing_step budgetTape (7/5) (controlPenalty savedCref uniformQuoteError unitRoleUnused .complete) favorableCompleteS42Before 8 [] (.query 1)
    (by decide) (by decide) favorableCompleteS42Choice0
  have hs1 := native_select_existing_step budgetTape (7/5) (controlPenalty savedCref uniformQuoteError unitRoleUnused .complete) favorableCompleteS42Before 7 [.query 1] (.hydeRetriever 1)
    (by decide) (by decide) favorableCompleteS42Choice1
  have hs2 := native_select_existing_step budgetTape (7/5) (controlPenalty savedCref uniformQuoteError unitRoleUnused .complete) favorableCompleteS42Before 6 [.query 1,.hydeRetriever 1] (.selection 3)
    (by decide) (by decide) favorableCompleteS42Choice2
  have hnew := native_select_new_step budgetTape (7/5) (controlPenalty savedCref uniformQuoteError unitRoleUnused .complete) favorableCompleteS42Before 5 [.query 1,.hydeRetriever 1,.selection 3]
    [.width 3,.width 1,.width 2] (.width 3) (by decide) (by decide) (by decide) (by decide)
  have hs : nativeSelect budgetTape (7/5) (controlPenalty savedCref uniformQuoteError unitRoleUnused .complete) favorableCompleteS42Before 9 [] = [.query 1,.hydeRetriever 1,.selection 3,.width 3] := by
    rw [hs0]
    change nativeSelect budgetTape (7/5) (controlPenalty savedCref uniformQuoteError unitRoleUnused .complete) favorableCompleteS42Before 8 [.query 1] = _
    rw [hs1]
    change nativeSelect budgetTape (7/5) (controlPenalty savedCref uniformQuoteError unitRoleUnused .complete) favorableCompleteS42Before 7 [.query 1,.hydeRetriever 1] = _
    rw [hs2]
    change nativeSelect budgetTape (7/5) (controlPenalty savedCref uniformQuoteError unitRoleUnused .complete) favorableCompleteS42Before 6 [.query 1,.hydeRetriever 1,.selection 3] = _
    rw [hnew] <;> rfl
  have hr : repairedRollout budgetTape favorableCompleteS42Before 9 [.query 1,.hydeRetriever 1,.selection 3,.width 3] = [.query 1,.hydeRetriever 1,.selection 3,.width 3,.stop,.reranker 0,.topm 0,.context 0,.answer 0] := by decide
  simp only [nativeEvent,hs,hr]
  rfl

def favorableCompleteS43Before := favorableCompleteProposal.take 42

theorem favorableCompleteS43Choice0 : nativeFirstChoice (indexScore (7/5) (controlPenalty savedCref uniformQuoteError unitRoleUnused .complete) favorableCompleteS43Before []) favorableCompleteS43Before [] = .query 1 := by
  apply complete_root_from_physical_gap favorableCompleteS43Before (favorableComplete_prefix_rewards 42) (by decide)
  · intro q; fin_cases q <;> decide
  · exact AgentUCTNextExact.favorable_complete_hyde_root_suffix_empty 42 (by omega)
  · intro q hq
    exact AgentUCTNextExact.favorable_complete_normal_root_physical_quote_exact 42 (by omega) q hq

theorem favorableCompleteS43D1I0 : indexScore (7/5) (controlPenalty savedCref uniformQuoteError unitRoleUnused .complete) favorableCompleteS43Before [.query 1] (.hydeRetriever 1) = treeIndex ((3/2)/14) (7/5) 0 35 14 := by
  have hs : replayBackup favorableCompleteS43Before emptyStatistics ([.query 1]++[.hydeRetriever 1]) = ⟨14,(3/2)⟩ := by
    rw [replayBackup_empty_closed_form]
    simp +decide [backedEvents,favorableCompleteS43Before,favorableCompleteProposal,favorableCompleteEvent1,favorableCompleteEvent2,favorableCompleteEvent3,favorableCompleteEvent4,favorableCompleteEvent5,favorableCompleteEvent6,favorableCompleteEvent7,favorableCompleteEvent8,favorableCompleteEvent9,favorableCompleteEvent10,favorableCompleteEvent11,favorableCompleteEvent12,favorableCompleteEvent13,favorableCompleteEvent14,favorableCompleteEvent15,favorableCompleteEvent16,favorableCompleteEvent17,favorableCompleteEvent18,favorableCompleteEvent19,favorableCompleteEvent20,favorableCompleteEvent21,favorableCompleteEvent22,favorableCompleteEvent23,favorableCompleteEvent24,favorableCompleteEvent25,favorableCompleteEvent26,favorableCompleteEvent27,favorableCompleteEvent28,favorableCompleteEvent29,favorableCompleteEvent30,favorableCompleteEvent31,favorableCompleteEvent32,favorableCompleteEvent33,favorableCompleteEvent34,favorableCompleteEvent35,favorableCompleteEvent36,favorableCompleteEvent37,favorableCompleteEvent38,favorableCompleteEvent39,favorableCompleteEvent40,favorableCompleteEvent41,favorableCompleteEvent42,taskReward]
    <;> norm_num
  have hp : rawVisits favorableCompleteS43Before [.query 1] = 35 := by decide
  have hn : rawVisits favorableCompleteS43Before ([.query 1]++[.hydeRetriever 1]) = 14 := by decide
  have hz : (controlPenalty savedCref uniformQuoteError unitRoleUnused .complete) favorableCompleteS43Before [.query 1] (.hydeRetriever 1) = 0 := by
    apply control_penalty_empty_of_prior_terminal .complete savedCref uniformQuoteError favorableCompleteS43Before [.query 1] (.hydeRetriever 1) 8 (by decide)
    · decide
    · decide
  unfold indexScore
  rw [hs,hp,hn,hz]
  simp only [BackupStat.mean]
  norm_num

theorem favorableCompleteS43D1I1 : indexScore (7/5) (controlPenalty savedCref uniformQuoteError unitRoleUnused .complete) favorableCompleteS43Before [.query 1] (.hydeRetriever 0) = treeIndex ((0/1)/10) (7/5) 0 35 10 := by
  have hs : replayBackup favorableCompleteS43Before emptyStatistics ([.query 1]++[.hydeRetriever 0]) = ⟨10,(0/1)⟩ := by
    rw [replayBackup_empty_closed_form]
    simp +decide [backedEvents,favorableCompleteS43Before,favorableCompleteProposal,favorableCompleteEvent1,favorableCompleteEvent2,favorableCompleteEvent3,favorableCompleteEvent4,favorableCompleteEvent5,favorableCompleteEvent6,favorableCompleteEvent7,favorableCompleteEvent8,favorableCompleteEvent9,favorableCompleteEvent10,favorableCompleteEvent11,favorableCompleteEvent12,favorableCompleteEvent13,favorableCompleteEvent14,favorableCompleteEvent15,favorableCompleteEvent16,favorableCompleteEvent17,favorableCompleteEvent18,favorableCompleteEvent19,favorableCompleteEvent20,favorableCompleteEvent21,favorableCompleteEvent22,favorableCompleteEvent23,favorableCompleteEvent24,favorableCompleteEvent25,favorableCompleteEvent26,favorableCompleteEvent27,favorableCompleteEvent28,favorableCompleteEvent29,favorableCompleteEvent30,favorableCompleteEvent31,favorableCompleteEvent32,favorableCompleteEvent33,favorableCompleteEvent34,favorableCompleteEvent35,favorableCompleteEvent36,favorableCompleteEvent37,favorableCompleteEvent38,favorableCompleteEvent39,favorableCompleteEvent40,favorableCompleteEvent41,favorableCompleteEvent42,taskReward]
    <;> norm_num
  have hp : rawVisits favorableCompleteS43Before [.query 1] = 35 := by decide
  have hn : rawVisits favorableCompleteS43Before ([.query 1]++[.hydeRetriever 0]) = 10 := by decide
  have hz : (controlPenalty savedCref uniformQuoteError unitRoleUnused .complete) favorableCompleteS43Before [.query 1] (.hydeRetriever 0) = 0 := by
    apply control_penalty_empty_of_prior_terminal .complete savedCref uniformQuoteError favorableCompleteS43Before [.query 1] (.hydeRetriever 0) 1 (by decide)
    · decide
    · decide
  unfold indexScore
  rw [hs,hp,hn,hz]
  simp only [BackupStat.mean]
  norm_num

theorem favorableCompleteS43D1I2 : indexScore (7/5) (controlPenalty savedCref uniformQuoteError unitRoleUnused .complete) favorableCompleteS43Before [.query 1] (.hydeRetriever 2) = treeIndex ((0/1)/10) (7/5) 0 35 10 := by
  have hs : replayBackup favorableCompleteS43Before emptyStatistics ([.query 1]++[.hydeRetriever 2]) = ⟨10,(0/1)⟩ := by
    rw [replayBackup_empty_closed_form]
    simp +decide [backedEvents,favorableCompleteS43Before,favorableCompleteProposal,favorableCompleteEvent1,favorableCompleteEvent2,favorableCompleteEvent3,favorableCompleteEvent4,favorableCompleteEvent5,favorableCompleteEvent6,favorableCompleteEvent7,favorableCompleteEvent8,favorableCompleteEvent9,favorableCompleteEvent10,favorableCompleteEvent11,favorableCompleteEvent12,favorableCompleteEvent13,favorableCompleteEvent14,favorableCompleteEvent15,favorableCompleteEvent16,favorableCompleteEvent17,favorableCompleteEvent18,favorableCompleteEvent19,favorableCompleteEvent20,favorableCompleteEvent21,favorableCompleteEvent22,favorableCompleteEvent23,favorableCompleteEvent24,favorableCompleteEvent25,favorableCompleteEvent26,favorableCompleteEvent27,favorableCompleteEvent28,favorableCompleteEvent29,favorableCompleteEvent30,favorableCompleteEvent31,favorableCompleteEvent32,favorableCompleteEvent33,favorableCompleteEvent34,favorableCompleteEvent35,favorableCompleteEvent36,favorableCompleteEvent37,favorableCompleteEvent38,favorableCompleteEvent39,favorableCompleteEvent40,favorableCompleteEvent41,favorableCompleteEvent42,taskReward]
    <;> norm_num
  have hp : rawVisits favorableCompleteS43Before [.query 1] = 35 := by decide
  have hn : rawVisits favorableCompleteS43Before ([.query 1]++[.hydeRetriever 2]) = 10 := by decide
  have hz : (controlPenalty savedCref uniformQuoteError unitRoleUnused .complete) favorableCompleteS43Before [.query 1] (.hydeRetriever 2) = 0 := by
    apply control_penalty_empty_of_prior_terminal .complete savedCref uniformQuoteError favorableCompleteS43Before [.query 1] (.hydeRetriever 2) 10 (by decide)
    · decide
    · decide
  unfold indexScore
  rw [hs,hp,hn,hz]
  simp only [BackupStat.mean]
  norm_num

theorem favorableCompleteS43D1Cmp0 : indexScore (7/5) (controlPenalty savedCref uniformQuoteError unitRoleUnused .complete) favorableCompleteS43Before [.query 1] (.hydeRetriever 1) < indexScore (7/5) (controlPenalty savedCref uniformQuoteError unitRoleUnused .complete) favorableCompleteS43Before [.query 1] (.hydeRetriever 0) := by
  rw [favorableCompleteS43D1I0,favorableCompleteS43D1I1]
  have h := index_strict_order_from_intervals ((0/1)/10) ((3/2)/14) 0 0 (41903743/50000000) (7083027/10000000)
    (treeBonus (7/5) 35 10) (treeBonus (7/5) 35 14)
    (trajectory_bonus_35_10).1 (trajectory_bonus_35_14).2 (by norm_num)
  simpa only [treeIndex,sub_zero] using h

theorem favorableCompleteS43D1Cmp2 : indexScore (7/5) (controlPenalty savedCref uniformQuoteError unitRoleUnused .complete) favorableCompleteS43Before [.query 1] (.hydeRetriever 2) ≤ indexScore (7/5) (controlPenalty savedCref uniformQuoteError unitRoleUnused .complete) favorableCompleteS43Before [.query 1] (.hydeRetriever 0) := by
  rw [favorableCompleteS43D1I2,favorableCompleteS43D1I1]

theorem favorableCompleteS43Choice1 : nativeFirstChoice (indexScore (7/5) (controlPenalty savedCref uniformQuoteError unitRoleUnused .complete) favorableCompleteS43Before [.query 1]) favorableCompleteS43Before [.query 1] = .hydeRetriever 0 := by
  apply visited_choice_from_ordered_certificate _ _ [.query 1] [.hydeRetriever 1] [.hydeRetriever 2] (.hydeRetriever 0) (by decide)
  · intro a ha
    have ho : orderedLegalAvailable [.query 1] = [.hydeRetriever 1,.hydeRetriever 0,.hydeRetriever 2] := by decide
    rw [ho] at ha
    simp only [List.mem_cons,List.not_mem_nil,or_false] at ha
    rcases ha with rfl | rfl | rfl <;> decide
  · intro a ha
    simp only [List.mem_cons,List.not_mem_nil,or_false] at ha
    rcases ha with rfl
    · exact favorableCompleteS43D1Cmp0
  · intro a ha
    simp only [List.mem_cons,List.not_mem_nil,or_false] at ha
    rcases ha with rfl
    · exact favorableCompleteS43D1Cmp2

theorem favorableCompleteS43D2I0 : indexScore (7/5) (controlPenalty savedCref uniformQuoteError unitRoleUnused .complete) favorableCompleteS43Before [.query 1,.hydeRetriever 0] (.selection 1) = treeIndex ((0/1)/3) (7/5) 0 10 3 := by
  have hs : replayBackup favorableCompleteS43Before emptyStatistics ([.query 1,.hydeRetriever 0]++[.selection 1]) = ⟨3,(0/1)⟩ := by
    rw [replayBackup_empty_closed_form]
    simp +decide [backedEvents,favorableCompleteS43Before,favorableCompleteProposal,favorableCompleteEvent1,favorableCompleteEvent2,favorableCompleteEvent3,favorableCompleteEvent4,favorableCompleteEvent5,favorableCompleteEvent6,favorableCompleteEvent7,favorableCompleteEvent8,favorableCompleteEvent9,favorableCompleteEvent10,favorableCompleteEvent11,favorableCompleteEvent12,favorableCompleteEvent13,favorableCompleteEvent14,favorableCompleteEvent15,favorableCompleteEvent16,favorableCompleteEvent17,favorableCompleteEvent18,favorableCompleteEvent19,favorableCompleteEvent20,favorableCompleteEvent21,favorableCompleteEvent22,favorableCompleteEvent23,favorableCompleteEvent24,favorableCompleteEvent25,favorableCompleteEvent26,favorableCompleteEvent27,favorableCompleteEvent28,favorableCompleteEvent29,favorableCompleteEvent30,favorableCompleteEvent31,favorableCompleteEvent32,favorableCompleteEvent33,favorableCompleteEvent34,favorableCompleteEvent35,favorableCompleteEvent36,favorableCompleteEvent37,favorableCompleteEvent38,favorableCompleteEvent39,favorableCompleteEvent40,favorableCompleteEvent41,favorableCompleteEvent42,taskReward]
    <;> norm_num
  have hp : rawVisits favorableCompleteS43Before [.query 1,.hydeRetriever 0] = 10 := by decide
  have hn : rawVisits favorableCompleteS43Before ([.query 1,.hydeRetriever 0]++[.selection 1]) = 3 := by decide
  have hz : (controlPenalty savedCref uniformQuoteError unitRoleUnused .complete) favorableCompleteS43Before [.query 1,.hydeRetriever 0] (.selection 1) = 0 := by
    apply control_penalty_empty_of_prior_terminal .complete savedCref uniformQuoteError favorableCompleteS43Before [.query 1,.hydeRetriever 0] (.selection 1) 16 (by decide)
    · decide
    · decide
  unfold indexScore
  rw [hs,hp,hn,hz]
  simp only [BackupStat.mean]
  norm_num

theorem favorableCompleteS43D2I1 : indexScore (7/5) (controlPenalty savedCref uniformQuoteError unitRoleUnused .complete) favorableCompleteS43Before [.query 1,.hydeRetriever 0] (.selection 2) = treeIndex ((0/1)/2) (7/5) 0 10 2 := by
  have hs : replayBackup favorableCompleteS43Before emptyStatistics ([.query 1,.hydeRetriever 0]++[.selection 2]) = ⟨2,(0/1)⟩ := by
    rw [replayBackup_empty_closed_form]
    simp +decide [backedEvents,favorableCompleteS43Before,favorableCompleteProposal,favorableCompleteEvent1,favorableCompleteEvent2,favorableCompleteEvent3,favorableCompleteEvent4,favorableCompleteEvent5,favorableCompleteEvent6,favorableCompleteEvent7,favorableCompleteEvent8,favorableCompleteEvent9,favorableCompleteEvent10,favorableCompleteEvent11,favorableCompleteEvent12,favorableCompleteEvent13,favorableCompleteEvent14,favorableCompleteEvent15,favorableCompleteEvent16,favorableCompleteEvent17,favorableCompleteEvent18,favorableCompleteEvent19,favorableCompleteEvent20,favorableCompleteEvent21,favorableCompleteEvent22,favorableCompleteEvent23,favorableCompleteEvent24,favorableCompleteEvent25,favorableCompleteEvent26,favorableCompleteEvent27,favorableCompleteEvent28,favorableCompleteEvent29,favorableCompleteEvent30,favorableCompleteEvent31,favorableCompleteEvent32,favorableCompleteEvent33,favorableCompleteEvent34,favorableCompleteEvent35,favorableCompleteEvent36,favorableCompleteEvent37,favorableCompleteEvent38,favorableCompleteEvent39,favorableCompleteEvent40,favorableCompleteEvent41,favorableCompleteEvent42,taskReward]
    <;> norm_num
  have hp : rawVisits favorableCompleteS43Before [.query 1,.hydeRetriever 0] = 10 := by decide
  have hn : rawVisits favorableCompleteS43Before ([.query 1,.hydeRetriever 0]++[.selection 2]) = 2 := by decide
  have hz : (controlPenalty savedCref uniformQuoteError unitRoleUnused .complete) favorableCompleteS43Before [.query 1,.hydeRetriever 0] (.selection 2) = 0 := by
    apply control_penalty_empty_of_prior_terminal .complete savedCref uniformQuoteError favorableCompleteS43Before [.query 1,.hydeRetriever 0] (.selection 2) 19 (by decide)
    · decide
    · decide
  unfold indexScore
  rw [hs,hp,hn,hz]
  simp only [BackupStat.mean]
  norm_num

theorem favorableCompleteS43D2I2 : indexScore (7/5) (controlPenalty savedCref uniformQuoteError unitRoleUnused .complete) favorableCompleteS43Before [.query 1,.hydeRetriever 0] (.selection 3) = treeIndex ((0/1)/2) (7/5) 0 10 2 := by
  have hs : replayBackup favorableCompleteS43Before emptyStatistics ([.query 1,.hydeRetriever 0]++[.selection 3]) = ⟨2,(0/1)⟩ := by
    rw [replayBackup_empty_closed_form]
    simp +decide [backedEvents,favorableCompleteS43Before,favorableCompleteProposal,favorableCompleteEvent1,favorableCompleteEvent2,favorableCompleteEvent3,favorableCompleteEvent4,favorableCompleteEvent5,favorableCompleteEvent6,favorableCompleteEvent7,favorableCompleteEvent8,favorableCompleteEvent9,favorableCompleteEvent10,favorableCompleteEvent11,favorableCompleteEvent12,favorableCompleteEvent13,favorableCompleteEvent14,favorableCompleteEvent15,favorableCompleteEvent16,favorableCompleteEvent17,favorableCompleteEvent18,favorableCompleteEvent19,favorableCompleteEvent20,favorableCompleteEvent21,favorableCompleteEvent22,favorableCompleteEvent23,favorableCompleteEvent24,favorableCompleteEvent25,favorableCompleteEvent26,favorableCompleteEvent27,favorableCompleteEvent28,favorableCompleteEvent29,favorableCompleteEvent30,favorableCompleteEvent31,favorableCompleteEvent32,favorableCompleteEvent33,favorableCompleteEvent34,favorableCompleteEvent35,favorableCompleteEvent36,favorableCompleteEvent37,favorableCompleteEvent38,favorableCompleteEvent39,favorableCompleteEvent40,favorableCompleteEvent41,favorableCompleteEvent42,taskReward]
    <;> norm_num
  have hp : rawVisits favorableCompleteS43Before [.query 1,.hydeRetriever 0] = 10 := by decide
  have hn : rawVisits favorableCompleteS43Before ([.query 1,.hydeRetriever 0]++[.selection 3]) = 2 := by decide
  have hz : (controlPenalty savedCref uniformQuoteError unitRoleUnused .complete) favorableCompleteS43Before [.query 1,.hydeRetriever 0] (.selection 3) = 0 := by
    apply control_penalty_empty_of_prior_terminal .complete savedCref uniformQuoteError favorableCompleteS43Before [.query 1,.hydeRetriever 0] (.selection 3) 23 (by decide)
    · decide
    · decide
  unfold indexScore
  rw [hs,hp,hn,hz]
  simp only [BackupStat.mean]
  norm_num

theorem favorableCompleteS43D2I3 : indexScore (7/5) (controlPenalty savedCref uniformQuoteError unitRoleUnused .complete) favorableCompleteS43Before [.query 1,.hydeRetriever 0] (.selection 0) = treeIndex ((0/1)/2) (7/5) 0 10 2 := by
  have hs : replayBackup favorableCompleteS43Before emptyStatistics ([.query 1,.hydeRetriever 0]++[.selection 0]) = ⟨2,(0/1)⟩ := by
    rw [replayBackup_empty_closed_form]
    simp +decide [backedEvents,favorableCompleteS43Before,favorableCompleteProposal,favorableCompleteEvent1,favorableCompleteEvent2,favorableCompleteEvent3,favorableCompleteEvent4,favorableCompleteEvent5,favorableCompleteEvent6,favorableCompleteEvent7,favorableCompleteEvent8,favorableCompleteEvent9,favorableCompleteEvent10,favorableCompleteEvent11,favorableCompleteEvent12,favorableCompleteEvent13,favorableCompleteEvent14,favorableCompleteEvent15,favorableCompleteEvent16,favorableCompleteEvent17,favorableCompleteEvent18,favorableCompleteEvent19,favorableCompleteEvent20,favorableCompleteEvent21,favorableCompleteEvent22,favorableCompleteEvent23,favorableCompleteEvent24,favorableCompleteEvent25,favorableCompleteEvent26,favorableCompleteEvent27,favorableCompleteEvent28,favorableCompleteEvent29,favorableCompleteEvent30,favorableCompleteEvent31,favorableCompleteEvent32,favorableCompleteEvent33,favorableCompleteEvent34,favorableCompleteEvent35,favorableCompleteEvent36,favorableCompleteEvent37,favorableCompleteEvent38,favorableCompleteEvent39,favorableCompleteEvent40,favorableCompleteEvent41,favorableCompleteEvent42,taskReward]
    <;> norm_num
  have hp : rawVisits favorableCompleteS43Before [.query 1,.hydeRetriever 0] = 10 := by decide
  have hn : rawVisits favorableCompleteS43Before ([.query 1,.hydeRetriever 0]++[.selection 0]) = 2 := by decide
  have hz : (controlPenalty savedCref uniformQuoteError unitRoleUnused .complete) favorableCompleteS43Before [.query 1,.hydeRetriever 0] (.selection 0) = 0 := by
    apply control_penalty_empty_of_prior_terminal .complete savedCref uniformQuoteError favorableCompleteS43Before [.query 1,.hydeRetriever 0] (.selection 0) 1 (by decide)
    · decide
    · decide
  unfold indexScore
  rw [hs,hp,hn,hz]
  simp only [BackupStat.mean]
  norm_num

theorem favorableCompleteS43D2Cmp0 : indexScore (7/5) (controlPenalty savedCref uniformQuoteError unitRoleUnused .complete) favorableCompleteS43Before [.query 1,.hydeRetriever 0] (.selection 1) < indexScore (7/5) (controlPenalty savedCref uniformQuoteError unitRoleUnused .complete) favorableCompleteS43Before [.query 1,.hydeRetriever 0] (.selection 2) := by
  rw [favorableCompleteS43D2I0,favorableCompleteS43D2I1]
  have h := index_strict_order_from_intervals ((0/1)/2) ((0/1)/3) 0 0 (38323761/25000000) (1251649/1000000)
    (treeBonus (7/5) 10 2) (treeBonus (7/5) 10 3)
    (trajectory_bonus_10_2).1 (trajectory_bonus_10_3).2 (by norm_num)
  simpa only [treeIndex,sub_zero] using h

theorem favorableCompleteS43D2Cmp2 : indexScore (7/5) (controlPenalty savedCref uniformQuoteError unitRoleUnused .complete) favorableCompleteS43Before [.query 1,.hydeRetriever 0] (.selection 3) ≤ indexScore (7/5) (controlPenalty savedCref uniformQuoteError unitRoleUnused .complete) favorableCompleteS43Before [.query 1,.hydeRetriever 0] (.selection 2) := by
  rw [favorableCompleteS43D2I2,favorableCompleteS43D2I1]

theorem favorableCompleteS43D2Cmp3 : indexScore (7/5) (controlPenalty savedCref uniformQuoteError unitRoleUnused .complete) favorableCompleteS43Before [.query 1,.hydeRetriever 0] (.selection 0) ≤ indexScore (7/5) (controlPenalty savedCref uniformQuoteError unitRoleUnused .complete) favorableCompleteS43Before [.query 1,.hydeRetriever 0] (.selection 2) := by
  rw [favorableCompleteS43D2I3,favorableCompleteS43D2I1]

theorem favorableCompleteS43Choice2 : nativeFirstChoice (indexScore (7/5) (controlPenalty savedCref uniformQuoteError unitRoleUnused .complete) favorableCompleteS43Before [.query 1,.hydeRetriever 0]) favorableCompleteS43Before [.query 1,.hydeRetriever 0] = .selection 2 := by
  apply visited_choice_from_ordered_certificate _ _ [.query 1,.hydeRetriever 0] [.selection 1] [.selection 3,.selection 0] (.selection 2) (by decide)
  · intro a ha
    have ho : orderedLegalAvailable [.query 1,.hydeRetriever 0] = [.selection 1,.selection 2,.selection 3,.selection 0] := by decide
    rw [ho] at ha
    simp only [List.mem_cons,List.not_mem_nil,or_false] at ha
    rcases ha with rfl | rfl | rfl | rfl <;> decide
  · intro a ha
    simp only [List.mem_cons,List.not_mem_nil,or_false] at ha
    rcases ha with rfl
    · exact favorableCompleteS43D2Cmp0
  · intro a ha
    simp only [List.mem_cons,List.not_mem_nil,or_false] at ha
    rcases ha with rfl | rfl
    · exact favorableCompleteS43D2Cmp2
    · exact favorableCompleteS43D2Cmp3

theorem favorableCompleteS43ActualEvent : nativeEvent budgetTape (7/5) (controlPenalty savedCref uniformQuoteError unitRoleUnused .complete)
    (taskReward false (2/5) (1/2)) favorableCompleteS43Before = favorableCompleteEvent43 := by
  have hs0 := native_select_existing_step budgetTape (7/5) (controlPenalty savedCref uniformQuoteError unitRoleUnused .complete) favorableCompleteS43Before 8 [] (.query 1)
    (by decide) (by decide) favorableCompleteS43Choice0
  have hs1 := native_select_existing_step budgetTape (7/5) (controlPenalty savedCref uniformQuoteError unitRoleUnused .complete) favorableCompleteS43Before 7 [.query 1] (.hydeRetriever 0)
    (by decide) (by decide) favorableCompleteS43Choice1
  have hs2 := native_select_existing_step budgetTape (7/5) (controlPenalty savedCref uniformQuoteError unitRoleUnused .complete) favorableCompleteS43Before 6 [.query 1,.hydeRetriever 0] (.selection 2)
    (by decide) (by decide) favorableCompleteS43Choice2
  have hnew := native_select_new_step budgetTape (7/5) (controlPenalty savedCref uniformQuoteError unitRoleUnused .complete) favorableCompleteS43Before 5 [.query 1,.hydeRetriever 0,.selection 2]
    [.width 3,.width 1,.width 2] (.width 3) (by decide) (by decide) (by decide) (by decide)
  have hs : nativeSelect budgetTape (7/5) (controlPenalty savedCref uniformQuoteError unitRoleUnused .complete) favorableCompleteS43Before 9 [] = [.query 1,.hydeRetriever 0,.selection 2,.width 3] := by
    rw [hs0]
    change nativeSelect budgetTape (7/5) (controlPenalty savedCref uniformQuoteError unitRoleUnused .complete) favorableCompleteS43Before 8 [.query 1] = _
    rw [hs1]
    change nativeSelect budgetTape (7/5) (controlPenalty savedCref uniformQuoteError unitRoleUnused .complete) favorableCompleteS43Before 7 [.query 1,.hydeRetriever 0] = _
    rw [hs2]
    change nativeSelect budgetTape (7/5) (controlPenalty savedCref uniformQuoteError unitRoleUnused .complete) favorableCompleteS43Before 6 [.query 1,.hydeRetriever 0,.selection 2] = _
    rw [hnew] <;> rfl
  have hr : repairedRollout budgetTape favorableCompleteS43Before 9 [.query 1,.hydeRetriever 0,.selection 2,.width 3] = [.query 1,.hydeRetriever 0,.selection 2,.width 3,.stop,.reranker 0,.topm 0,.context 0,.answer 0] := by decide
  simp only [nativeEvent,hs,hr]
  rfl

def favorableCompleteS44Before := favorableCompleteProposal.take 43

theorem favorableCompleteS44Choice0 : nativeFirstChoice (indexScore (7/5) (controlPenalty savedCref uniformQuoteError unitRoleUnused .complete) favorableCompleteS44Before []) favorableCompleteS44Before [] = .query 1 := by
  apply complete_root_from_physical_gap favorableCompleteS44Before (favorableComplete_prefix_rewards 43) (by decide)
  · intro q; fin_cases q <;> decide
  · exact AgentUCTNextExact.favorable_complete_hyde_root_suffix_empty 43 (by omega)
  · intro q hq
    exact AgentUCTNextExact.favorable_complete_normal_root_physical_quote_exact 43 (by omega) q hq

theorem favorableCompleteS44D1I0 : indexScore (7/5) (controlPenalty savedCref uniformQuoteError unitRoleUnused .complete) favorableCompleteS44Before [.query 1] (.hydeRetriever 1) = treeIndex ((3/2)/14) (7/5) 0 36 14 := by
  have hs : replayBackup favorableCompleteS44Before emptyStatistics ([.query 1]++[.hydeRetriever 1]) = ⟨14,(3/2)⟩ := by
    rw [replayBackup_empty_closed_form]
    simp +decide [backedEvents,favorableCompleteS44Before,favorableCompleteProposal,favorableCompleteEvent1,favorableCompleteEvent2,favorableCompleteEvent3,favorableCompleteEvent4,favorableCompleteEvent5,favorableCompleteEvent6,favorableCompleteEvent7,favorableCompleteEvent8,favorableCompleteEvent9,favorableCompleteEvent10,favorableCompleteEvent11,favorableCompleteEvent12,favorableCompleteEvent13,favorableCompleteEvent14,favorableCompleteEvent15,favorableCompleteEvent16,favorableCompleteEvent17,favorableCompleteEvent18,favorableCompleteEvent19,favorableCompleteEvent20,favorableCompleteEvent21,favorableCompleteEvent22,favorableCompleteEvent23,favorableCompleteEvent24,favorableCompleteEvent25,favorableCompleteEvent26,favorableCompleteEvent27,favorableCompleteEvent28,favorableCompleteEvent29,favorableCompleteEvent30,favorableCompleteEvent31,favorableCompleteEvent32,favorableCompleteEvent33,favorableCompleteEvent34,favorableCompleteEvent35,favorableCompleteEvent36,favorableCompleteEvent37,favorableCompleteEvent38,favorableCompleteEvent39,favorableCompleteEvent40,favorableCompleteEvent41,favorableCompleteEvent42,favorableCompleteEvent43,taskReward]
    <;> norm_num
  have hp : rawVisits favorableCompleteS44Before [.query 1] = 36 := by decide
  have hn : rawVisits favorableCompleteS44Before ([.query 1]++[.hydeRetriever 1]) = 14 := by decide
  have hz : (controlPenalty savedCref uniformQuoteError unitRoleUnused .complete) favorableCompleteS44Before [.query 1] (.hydeRetriever 1) = 0 := by
    apply control_penalty_empty_of_prior_terminal .complete savedCref uniformQuoteError favorableCompleteS44Before [.query 1] (.hydeRetriever 1) 8 (by decide)
    · decide
    · decide
  unfold indexScore
  rw [hs,hp,hn,hz]
  simp only [BackupStat.mean]
  norm_num

theorem favorableCompleteS44D1I1 : indexScore (7/5) (controlPenalty savedCref uniformQuoteError unitRoleUnused .complete) favorableCompleteS44Before [.query 1] (.hydeRetriever 0) = treeIndex ((0/1)/11) (7/5) 0 36 11 := by
  have hs : replayBackup favorableCompleteS44Before emptyStatistics ([.query 1]++[.hydeRetriever 0]) = ⟨11,(0/1)⟩ := by
    rw [replayBackup_empty_closed_form]
    simp +decide [backedEvents,favorableCompleteS44Before,favorableCompleteProposal,favorableCompleteEvent1,favorableCompleteEvent2,favorableCompleteEvent3,favorableCompleteEvent4,favorableCompleteEvent5,favorableCompleteEvent6,favorableCompleteEvent7,favorableCompleteEvent8,favorableCompleteEvent9,favorableCompleteEvent10,favorableCompleteEvent11,favorableCompleteEvent12,favorableCompleteEvent13,favorableCompleteEvent14,favorableCompleteEvent15,favorableCompleteEvent16,favorableCompleteEvent17,favorableCompleteEvent18,favorableCompleteEvent19,favorableCompleteEvent20,favorableCompleteEvent21,favorableCompleteEvent22,favorableCompleteEvent23,favorableCompleteEvent24,favorableCompleteEvent25,favorableCompleteEvent26,favorableCompleteEvent27,favorableCompleteEvent28,favorableCompleteEvent29,favorableCompleteEvent30,favorableCompleteEvent31,favorableCompleteEvent32,favorableCompleteEvent33,favorableCompleteEvent34,favorableCompleteEvent35,favorableCompleteEvent36,favorableCompleteEvent37,favorableCompleteEvent38,favorableCompleteEvent39,favorableCompleteEvent40,favorableCompleteEvent41,favorableCompleteEvent42,favorableCompleteEvent43,taskReward]
    <;> norm_num
  have hp : rawVisits favorableCompleteS44Before [.query 1] = 36 := by decide
  have hn : rawVisits favorableCompleteS44Before ([.query 1]++[.hydeRetriever 0]) = 11 := by decide
  have hz : (controlPenalty savedCref uniformQuoteError unitRoleUnused .complete) favorableCompleteS44Before [.query 1] (.hydeRetriever 0) = 0 := by
    apply control_penalty_empty_of_prior_terminal .complete savedCref uniformQuoteError favorableCompleteS44Before [.query 1] (.hydeRetriever 0) 1 (by decide)
    · decide
    · decide
  unfold indexScore
  rw [hs,hp,hn,hz]
  simp only [BackupStat.mean]
  norm_num

theorem favorableCompleteS44D1I2 : indexScore (7/5) (controlPenalty savedCref uniformQuoteError unitRoleUnused .complete) favorableCompleteS44Before [.query 1] (.hydeRetriever 2) = treeIndex ((0/1)/10) (7/5) 0 36 10 := by
  have hs : replayBackup favorableCompleteS44Before emptyStatistics ([.query 1]++[.hydeRetriever 2]) = ⟨10,(0/1)⟩ := by
    rw [replayBackup_empty_closed_form]
    simp +decide [backedEvents,favorableCompleteS44Before,favorableCompleteProposal,favorableCompleteEvent1,favorableCompleteEvent2,favorableCompleteEvent3,favorableCompleteEvent4,favorableCompleteEvent5,favorableCompleteEvent6,favorableCompleteEvent7,favorableCompleteEvent8,favorableCompleteEvent9,favorableCompleteEvent10,favorableCompleteEvent11,favorableCompleteEvent12,favorableCompleteEvent13,favorableCompleteEvent14,favorableCompleteEvent15,favorableCompleteEvent16,favorableCompleteEvent17,favorableCompleteEvent18,favorableCompleteEvent19,favorableCompleteEvent20,favorableCompleteEvent21,favorableCompleteEvent22,favorableCompleteEvent23,favorableCompleteEvent24,favorableCompleteEvent25,favorableCompleteEvent26,favorableCompleteEvent27,favorableCompleteEvent28,favorableCompleteEvent29,favorableCompleteEvent30,favorableCompleteEvent31,favorableCompleteEvent32,favorableCompleteEvent33,favorableCompleteEvent34,favorableCompleteEvent35,favorableCompleteEvent36,favorableCompleteEvent37,favorableCompleteEvent38,favorableCompleteEvent39,favorableCompleteEvent40,favorableCompleteEvent41,favorableCompleteEvent42,favorableCompleteEvent43,taskReward]
    <;> norm_num
  have hp : rawVisits favorableCompleteS44Before [.query 1] = 36 := by decide
  have hn : rawVisits favorableCompleteS44Before ([.query 1]++[.hydeRetriever 2]) = 10 := by decide
  have hz : (controlPenalty savedCref uniformQuoteError unitRoleUnused .complete) favorableCompleteS44Before [.query 1] (.hydeRetriever 2) = 0 := by
    apply control_penalty_empty_of_prior_terminal .complete savedCref uniformQuoteError favorableCompleteS44Before [.query 1] (.hydeRetriever 2) 10 (by decide)
    · decide
    · decide
  unfold indexScore
  rw [hs,hp,hn,hz]
  simp only [BackupStat.mean]
  norm_num

theorem favorableCompleteS44D1Cmp0 : indexScore (7/5) (controlPenalty savedCref uniformQuoteError unitRoleUnused .complete) favorableCompleteS44Before [.query 1] (.hydeRetriever 1) < indexScore (7/5) (controlPenalty savedCref uniformQuoteError unitRoleUnused .complete) favorableCompleteS44Before [.query 1] (.hydeRetriever 2) := by
  rw [favorableCompleteS44D1I0,favorableCompleteS44D1I2]
  have h := index_strict_order_from_intervals ((0/1)/10) ((3/2)/14) 0 0 (42063637/50000000) (3555027/5000000)
    (treeBonus (7/5) 36 10) (treeBonus (7/5) 36 14)
    (trajectory_bonus_36_10).1 (trajectory_bonus_36_14).2 (by norm_num)
  simpa only [treeIndex,sub_zero] using h

theorem favorableCompleteS44D1Cmp1 : indexScore (7/5) (controlPenalty savedCref uniformQuoteError unitRoleUnused .complete) favorableCompleteS44Before [.query 1] (.hydeRetriever 0) < indexScore (7/5) (controlPenalty savedCref uniformQuoteError unitRoleUnused .complete) favorableCompleteS44Before [.query 1] (.hydeRetriever 2) := by
  rw [favorableCompleteS44D1I1,favorableCompleteS44D1I2]
  have h := index_strict_order_from_intervals ((0/1)/10) ((0/1)/11) 0 0 (42063637/50000000) (10026527/12500000)
    (treeBonus (7/5) 36 10) (treeBonus (7/5) 36 11)
    (trajectory_bonus_36_10).1 (trajectory_bonus_36_11).2 (by norm_num)
  simpa only [treeIndex,sub_zero] using h

theorem favorableCompleteS44Choice1 : nativeFirstChoice (indexScore (7/5) (controlPenalty savedCref uniformQuoteError unitRoleUnused .complete) favorableCompleteS44Before [.query 1]) favorableCompleteS44Before [.query 1] = .hydeRetriever 2 := by
  apply visited_choice_from_ordered_certificate _ _ [.query 1] [.hydeRetriever 1,.hydeRetriever 0] [] (.hydeRetriever 2) (by decide)
  · intro a ha
    have ho : orderedLegalAvailable [.query 1] = [.hydeRetriever 1,.hydeRetriever 0,.hydeRetriever 2] := by decide
    rw [ho] at ha
    simp only [List.mem_cons,List.not_mem_nil,or_false] at ha
    rcases ha with rfl | rfl | rfl <;> decide
  · intro a ha
    simp only [List.mem_cons,List.not_mem_nil,or_false] at ha
    rcases ha with rfl | rfl
    · exact favorableCompleteS44D1Cmp0
    · exact favorableCompleteS44D1Cmp1
  · simp

theorem favorableCompleteS44D2I0 : indexScore (7/5) (controlPenalty savedCref uniformQuoteError unitRoleUnused .complete) favorableCompleteS44Before [.query 1,.hydeRetriever 2] (.selection 1) = treeIndex ((0/1)/3) (7/5) 0 10 3 := by
  have hs : replayBackup favorableCompleteS44Before emptyStatistics ([.query 1,.hydeRetriever 2]++[.selection 1]) = ⟨3,(0/1)⟩ := by
    rw [replayBackup_empty_closed_form]
    simp +decide [backedEvents,favorableCompleteS44Before,favorableCompleteProposal,favorableCompleteEvent1,favorableCompleteEvent2,favorableCompleteEvent3,favorableCompleteEvent4,favorableCompleteEvent5,favorableCompleteEvent6,favorableCompleteEvent7,favorableCompleteEvent8,favorableCompleteEvent9,favorableCompleteEvent10,favorableCompleteEvent11,favorableCompleteEvent12,favorableCompleteEvent13,favorableCompleteEvent14,favorableCompleteEvent15,favorableCompleteEvent16,favorableCompleteEvent17,favorableCompleteEvent18,favorableCompleteEvent19,favorableCompleteEvent20,favorableCompleteEvent21,favorableCompleteEvent22,favorableCompleteEvent23,favorableCompleteEvent24,favorableCompleteEvent25,favorableCompleteEvent26,favorableCompleteEvent27,favorableCompleteEvent28,favorableCompleteEvent29,favorableCompleteEvent30,favorableCompleteEvent31,favorableCompleteEvent32,favorableCompleteEvent33,favorableCompleteEvent34,favorableCompleteEvent35,favorableCompleteEvent36,favorableCompleteEvent37,favorableCompleteEvent38,favorableCompleteEvent39,favorableCompleteEvent40,favorableCompleteEvent41,favorableCompleteEvent42,favorableCompleteEvent43,taskReward]
    <;> norm_num
  have hp : rawVisits favorableCompleteS44Before [.query 1,.hydeRetriever 2] = 10 := by decide
  have hn : rawVisits favorableCompleteS44Before ([.query 1,.hydeRetriever 2]++[.selection 1]) = 3 := by decide
  have hz : (controlPenalty savedCref uniformQuoteError unitRoleUnused .complete) favorableCompleteS44Before [.query 1,.hydeRetriever 2] (.selection 1) = 0 := by
    apply control_penalty_empty_of_prior_terminal .complete savedCref uniformQuoteError favorableCompleteS44Before [.query 1,.hydeRetriever 2] (.selection 1) 17 (by decide)
    · decide
    · decide
  unfold indexScore
  rw [hs,hp,hn,hz]
  simp only [BackupStat.mean]
  norm_num

theorem favorableCompleteS44D2I1 : indexScore (7/5) (controlPenalty savedCref uniformQuoteError unitRoleUnused .complete) favorableCompleteS44Before [.query 1,.hydeRetriever 2] (.selection 2) = treeIndex ((0/1)/2) (7/5) 0 10 2 := by
  have hs : replayBackup favorableCompleteS44Before emptyStatistics ([.query 1,.hydeRetriever 2]++[.selection 2]) = ⟨2,(0/1)⟩ := by
    rw [replayBackup_empty_closed_form]
    simp +decide [backedEvents,favorableCompleteS44Before,favorableCompleteProposal,favorableCompleteEvent1,favorableCompleteEvent2,favorableCompleteEvent3,favorableCompleteEvent4,favorableCompleteEvent5,favorableCompleteEvent6,favorableCompleteEvent7,favorableCompleteEvent8,favorableCompleteEvent9,favorableCompleteEvent10,favorableCompleteEvent11,favorableCompleteEvent12,favorableCompleteEvent13,favorableCompleteEvent14,favorableCompleteEvent15,favorableCompleteEvent16,favorableCompleteEvent17,favorableCompleteEvent18,favorableCompleteEvent19,favorableCompleteEvent20,favorableCompleteEvent21,favorableCompleteEvent22,favorableCompleteEvent23,favorableCompleteEvent24,favorableCompleteEvent25,favorableCompleteEvent26,favorableCompleteEvent27,favorableCompleteEvent28,favorableCompleteEvent29,favorableCompleteEvent30,favorableCompleteEvent31,favorableCompleteEvent32,favorableCompleteEvent33,favorableCompleteEvent34,favorableCompleteEvent35,favorableCompleteEvent36,favorableCompleteEvent37,favorableCompleteEvent38,favorableCompleteEvent39,favorableCompleteEvent40,favorableCompleteEvent41,favorableCompleteEvent42,favorableCompleteEvent43,taskReward]
    <;> norm_num
  have hp : rawVisits favorableCompleteS44Before [.query 1,.hydeRetriever 2] = 10 := by decide
  have hn : rawVisits favorableCompleteS44Before ([.query 1,.hydeRetriever 2]++[.selection 2]) = 2 := by decide
  have hz : (controlPenalty savedCref uniformQuoteError unitRoleUnused .complete) favorableCompleteS44Before [.query 1,.hydeRetriever 2] (.selection 2) = 0 := by
    apply control_penalty_empty_of_prior_terminal .complete savedCref uniformQuoteError favorableCompleteS44Before [.query 1,.hydeRetriever 2] (.selection 2) 20 (by decide)
    · decide
    · decide
  unfold indexScore
  rw [hs,hp,hn,hz]
  simp only [BackupStat.mean]
  norm_num

theorem favorableCompleteS44D2I2 : indexScore (7/5) (controlPenalty savedCref uniformQuoteError unitRoleUnused .complete) favorableCompleteS44Before [.query 1,.hydeRetriever 2] (.selection 3) = treeIndex ((0/1)/2) (7/5) 0 10 2 := by
  have hs : replayBackup favorableCompleteS44Before emptyStatistics ([.query 1,.hydeRetriever 2]++[.selection 3]) = ⟨2,(0/1)⟩ := by
    rw [replayBackup_empty_closed_form]
    simp +decide [backedEvents,favorableCompleteS44Before,favorableCompleteProposal,favorableCompleteEvent1,favorableCompleteEvent2,favorableCompleteEvent3,favorableCompleteEvent4,favorableCompleteEvent5,favorableCompleteEvent6,favorableCompleteEvent7,favorableCompleteEvent8,favorableCompleteEvent9,favorableCompleteEvent10,favorableCompleteEvent11,favorableCompleteEvent12,favorableCompleteEvent13,favorableCompleteEvent14,favorableCompleteEvent15,favorableCompleteEvent16,favorableCompleteEvent17,favorableCompleteEvent18,favorableCompleteEvent19,favorableCompleteEvent20,favorableCompleteEvent21,favorableCompleteEvent22,favorableCompleteEvent23,favorableCompleteEvent24,favorableCompleteEvent25,favorableCompleteEvent26,favorableCompleteEvent27,favorableCompleteEvent28,favorableCompleteEvent29,favorableCompleteEvent30,favorableCompleteEvent31,favorableCompleteEvent32,favorableCompleteEvent33,favorableCompleteEvent34,favorableCompleteEvent35,favorableCompleteEvent36,favorableCompleteEvent37,favorableCompleteEvent38,favorableCompleteEvent39,favorableCompleteEvent40,favorableCompleteEvent41,favorableCompleteEvent42,favorableCompleteEvent43,taskReward]
    <;> norm_num
  have hp : rawVisits favorableCompleteS44Before [.query 1,.hydeRetriever 2] = 10 := by decide
  have hn : rawVisits favorableCompleteS44Before ([.query 1,.hydeRetriever 2]++[.selection 3]) = 2 := by decide
  have hz : (controlPenalty savedCref uniformQuoteError unitRoleUnused .complete) favorableCompleteS44Before [.query 1,.hydeRetriever 2] (.selection 3) = 0 := by
    apply control_penalty_empty_of_prior_terminal .complete savedCref uniformQuoteError favorableCompleteS44Before [.query 1,.hydeRetriever 2] (.selection 3) 24 (by decide)
    · decide
    · decide
  unfold indexScore
  rw [hs,hp,hn,hz]
  simp only [BackupStat.mean]
  norm_num

theorem favorableCompleteS44D2I3 : indexScore (7/5) (controlPenalty savedCref uniformQuoteError unitRoleUnused .complete) favorableCompleteS44Before [.query 1,.hydeRetriever 2] (.selection 0) = treeIndex ((0/1)/2) (7/5) 0 10 2 := by
  have hs : replayBackup favorableCompleteS44Before emptyStatistics ([.query 1,.hydeRetriever 2]++[.selection 0]) = ⟨2,(0/1)⟩ := by
    rw [replayBackup_empty_closed_form]
    simp +decide [backedEvents,favorableCompleteS44Before,favorableCompleteProposal,favorableCompleteEvent1,favorableCompleteEvent2,favorableCompleteEvent3,favorableCompleteEvent4,favorableCompleteEvent5,favorableCompleteEvent6,favorableCompleteEvent7,favorableCompleteEvent8,favorableCompleteEvent9,favorableCompleteEvent10,favorableCompleteEvent11,favorableCompleteEvent12,favorableCompleteEvent13,favorableCompleteEvent14,favorableCompleteEvent15,favorableCompleteEvent16,favorableCompleteEvent17,favorableCompleteEvent18,favorableCompleteEvent19,favorableCompleteEvent20,favorableCompleteEvent21,favorableCompleteEvent22,favorableCompleteEvent23,favorableCompleteEvent24,favorableCompleteEvent25,favorableCompleteEvent26,favorableCompleteEvent27,favorableCompleteEvent28,favorableCompleteEvent29,favorableCompleteEvent30,favorableCompleteEvent31,favorableCompleteEvent32,favorableCompleteEvent33,favorableCompleteEvent34,favorableCompleteEvent35,favorableCompleteEvent36,favorableCompleteEvent37,favorableCompleteEvent38,favorableCompleteEvent39,favorableCompleteEvent40,favorableCompleteEvent41,favorableCompleteEvent42,favorableCompleteEvent43,taskReward]
    <;> norm_num
  have hp : rawVisits favorableCompleteS44Before [.query 1,.hydeRetriever 2] = 10 := by decide
  have hn : rawVisits favorableCompleteS44Before ([.query 1,.hydeRetriever 2]++[.selection 0]) = 2 := by decide
  have hz : (controlPenalty savedCref uniformQuoteError unitRoleUnused .complete) favorableCompleteS44Before [.query 1,.hydeRetriever 2] (.selection 0) = 0 := by
    apply control_penalty_empty_of_prior_terminal .complete savedCref uniformQuoteError favorableCompleteS44Before [.query 1,.hydeRetriever 2] (.selection 0) 10 (by decide)
    · decide
    · decide
  unfold indexScore
  rw [hs,hp,hn,hz]
  simp only [BackupStat.mean]
  norm_num

theorem favorableCompleteS44D2Cmp0 : indexScore (7/5) (controlPenalty savedCref uniformQuoteError unitRoleUnused .complete) favorableCompleteS44Before [.query 1,.hydeRetriever 2] (.selection 1) < indexScore (7/5) (controlPenalty savedCref uniformQuoteError unitRoleUnused .complete) favorableCompleteS44Before [.query 1,.hydeRetriever 2] (.selection 2) := by
  rw [favorableCompleteS44D2I0,favorableCompleteS44D2I1]
  have h := index_strict_order_from_intervals ((0/1)/2) ((0/1)/3) 0 0 (38323761/25000000) (1251649/1000000)
    (treeBonus (7/5) 10 2) (treeBonus (7/5) 10 3)
    (trajectory_bonus_10_2).1 (trajectory_bonus_10_3).2 (by norm_num)
  simpa only [treeIndex,sub_zero] using h

theorem favorableCompleteS44D2Cmp2 : indexScore (7/5) (controlPenalty savedCref uniformQuoteError unitRoleUnused .complete) favorableCompleteS44Before [.query 1,.hydeRetriever 2] (.selection 3) ≤ indexScore (7/5) (controlPenalty savedCref uniformQuoteError unitRoleUnused .complete) favorableCompleteS44Before [.query 1,.hydeRetriever 2] (.selection 2) := by
  rw [favorableCompleteS44D2I2,favorableCompleteS44D2I1]

theorem favorableCompleteS44D2Cmp3 : indexScore (7/5) (controlPenalty savedCref uniformQuoteError unitRoleUnused .complete) favorableCompleteS44Before [.query 1,.hydeRetriever 2] (.selection 0) ≤ indexScore (7/5) (controlPenalty savedCref uniformQuoteError unitRoleUnused .complete) favorableCompleteS44Before [.query 1,.hydeRetriever 2] (.selection 2) := by
  rw [favorableCompleteS44D2I3,favorableCompleteS44D2I1]

theorem favorableCompleteS44Choice2 : nativeFirstChoice (indexScore (7/5) (controlPenalty savedCref uniformQuoteError unitRoleUnused .complete) favorableCompleteS44Before [.query 1,.hydeRetriever 2]) favorableCompleteS44Before [.query 1,.hydeRetriever 2] = .selection 2 := by
  apply visited_choice_from_ordered_certificate _ _ [.query 1,.hydeRetriever 2] [.selection 1] [.selection 3,.selection 0] (.selection 2) (by decide)
  · intro a ha
    have ho : orderedLegalAvailable [.query 1,.hydeRetriever 2] = [.selection 1,.selection 2,.selection 3,.selection 0] := by decide
    rw [ho] at ha
    simp only [List.mem_cons,List.not_mem_nil,or_false] at ha
    rcases ha with rfl | rfl | rfl | rfl <;> decide
  · intro a ha
    simp only [List.mem_cons,List.not_mem_nil,or_false] at ha
    rcases ha with rfl
    · exact favorableCompleteS44D2Cmp0
  · intro a ha
    simp only [List.mem_cons,List.not_mem_nil,or_false] at ha
    rcases ha with rfl | rfl
    · exact favorableCompleteS44D2Cmp2
    · exact favorableCompleteS44D2Cmp3

theorem favorableCompleteS44ActualEvent : nativeEvent budgetTape (7/5) (controlPenalty savedCref uniformQuoteError unitRoleUnused .complete)
    (taskReward false (2/5) (1/2)) favorableCompleteS44Before = favorableCompleteEvent44 := by
  have hs0 := native_select_existing_step budgetTape (7/5) (controlPenalty savedCref uniformQuoteError unitRoleUnused .complete) favorableCompleteS44Before 8 [] (.query 1)
    (by decide) (by decide) favorableCompleteS44Choice0
  have hs1 := native_select_existing_step budgetTape (7/5) (controlPenalty savedCref uniformQuoteError unitRoleUnused .complete) favorableCompleteS44Before 7 [.query 1] (.hydeRetriever 2)
    (by decide) (by decide) favorableCompleteS44Choice1
  have hs2 := native_select_existing_step budgetTape (7/5) (controlPenalty savedCref uniformQuoteError unitRoleUnused .complete) favorableCompleteS44Before 6 [.query 1,.hydeRetriever 2] (.selection 2)
    (by decide) (by decide) favorableCompleteS44Choice2
  have hnew := native_select_new_step budgetTape (7/5) (controlPenalty savedCref uniformQuoteError unitRoleUnused .complete) favorableCompleteS44Before 5 [.query 1,.hydeRetriever 2,.selection 2]
    [.width 3,.width 1,.width 2] (.width 3) (by decide) (by decide) (by decide) (by decide)
  have hs : nativeSelect budgetTape (7/5) (controlPenalty savedCref uniformQuoteError unitRoleUnused .complete) favorableCompleteS44Before 9 [] = [.query 1,.hydeRetriever 2,.selection 2,.width 3] := by
    rw [hs0]
    change nativeSelect budgetTape (7/5) (controlPenalty savedCref uniformQuoteError unitRoleUnused .complete) favorableCompleteS44Before 8 [.query 1] = _
    rw [hs1]
    change nativeSelect budgetTape (7/5) (controlPenalty savedCref uniformQuoteError unitRoleUnused .complete) favorableCompleteS44Before 7 [.query 1,.hydeRetriever 2] = _
    rw [hs2]
    change nativeSelect budgetTape (7/5) (controlPenalty savedCref uniformQuoteError unitRoleUnused .complete) favorableCompleteS44Before 6 [.query 1,.hydeRetriever 2,.selection 2] = _
    rw [hnew] <;> rfl
  have hr : repairedRollout budgetTape favorableCompleteS44Before 9 [.query 1,.hydeRetriever 2,.selection 2,.width 3] = [.query 1,.hydeRetriever 2,.selection 2,.width 3,.stop,.reranker 0,.topm 0,.context 0,.answer 0] := by decide
  simp only [nativeEvent,hs,hr]
  rfl

end AgentUCT32MConcrete
