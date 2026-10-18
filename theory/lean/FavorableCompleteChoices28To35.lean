import ProposalRewards
import TrajectoryBonus
import InitialConcreteBridge
import CompleteNormalQuote
import CachedSuffixCertificate
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

def favorableCompleteS28Before := favorableCompleteProposal.take 27

theorem favorableCompleteS28Choice0 : nativeFirstChoice (indexScore (7/5) (controlPenalty savedCref uniformQuoteError unitRoleUnused .complete) favorableCompleteS28Before []) favorableCompleteS28Before [] = .query 1 := by
  apply complete_root_from_physical_gap favorableCompleteS28Before (favorableComplete_prefix_rewards 27) (by decide)
  · intro q; fin_cases q <;> decide
  · decide
  · intro q hq
    exact AgentUCTNextExact.favorable_complete_normal_root_physical_quote_exact 27 (by omega) q hq

theorem favorableCompleteS28D1I0 : indexScore (7/5) (controlPenalty savedCref uniformQuoteError unitRoleUnused .complete) favorableCompleteS28Before [.query 1] (.hydeRetriever 1) = treeIndex ((3/2)/8) (7/5) 0 20 8 := by
  have hs : replayBackup favorableCompleteS28Before emptyStatistics ([.query 1]++[.hydeRetriever 1]) = ⟨8,(3/2)⟩ := by
    rw [replayBackup_empty_closed_form]
    simp +decide [backedEvents,favorableCompleteS28Before,favorableCompleteProposal,favorableCompleteEvent1,favorableCompleteEvent2,favorableCompleteEvent3,favorableCompleteEvent4,favorableCompleteEvent5,favorableCompleteEvent6,favorableCompleteEvent7,favorableCompleteEvent8,favorableCompleteEvent9,favorableCompleteEvent10,favorableCompleteEvent11,favorableCompleteEvent12,favorableCompleteEvent13,favorableCompleteEvent14,favorableCompleteEvent15,favorableCompleteEvent16,favorableCompleteEvent17,favorableCompleteEvent18,favorableCompleteEvent19,favorableCompleteEvent20,favorableCompleteEvent21,favorableCompleteEvent22,favorableCompleteEvent23,favorableCompleteEvent24,favorableCompleteEvent25,favorableCompleteEvent26,favorableCompleteEvent27,taskReward]
    <;> norm_num
  have hp : rawVisits favorableCompleteS28Before [.query 1] = 20 := by decide
  have hn : rawVisits favorableCompleteS28Before ([.query 1]++[.hydeRetriever 1]) = 8 := by decide
  have hz : (controlPenalty savedCref uniformQuoteError unitRoleUnused .complete) favorableCompleteS28Before [.query 1] (.hydeRetriever 1) = 0 := by
    apply control_penalty_empty_of_prior_terminal .complete savedCref uniformQuoteError favorableCompleteS28Before [.query 1] (.hydeRetriever 1) 8 (by decide)
    · decide
    · decide
  unfold indexScore
  rw [hs,hp,hn,hz]
  simp only [BackupStat.mean]
  norm_num

theorem favorableCompleteS28D1I1 : indexScore (7/5) (controlPenalty savedCref uniformQuoteError unitRoleUnused .complete) favorableCompleteS28Before [.query 1] (.hydeRetriever 0) = treeIndex ((0/1)/6) (7/5) 0 20 6 := by
  have hs : replayBackup favorableCompleteS28Before emptyStatistics ([.query 1]++[.hydeRetriever 0]) = ⟨6,(0/1)⟩ := by
    rw [replayBackup_empty_closed_form]
    simp +decide [backedEvents,favorableCompleteS28Before,favorableCompleteProposal,favorableCompleteEvent1,favorableCompleteEvent2,favorableCompleteEvent3,favorableCompleteEvent4,favorableCompleteEvent5,favorableCompleteEvent6,favorableCompleteEvent7,favorableCompleteEvent8,favorableCompleteEvent9,favorableCompleteEvent10,favorableCompleteEvent11,favorableCompleteEvent12,favorableCompleteEvent13,favorableCompleteEvent14,favorableCompleteEvent15,favorableCompleteEvent16,favorableCompleteEvent17,favorableCompleteEvent18,favorableCompleteEvent19,favorableCompleteEvent20,favorableCompleteEvent21,favorableCompleteEvent22,favorableCompleteEvent23,favorableCompleteEvent24,favorableCompleteEvent25,favorableCompleteEvent26,favorableCompleteEvent27,taskReward]
    <;> norm_num
  have hp : rawVisits favorableCompleteS28Before [.query 1] = 20 := by decide
  have hn : rawVisits favorableCompleteS28Before ([.query 1]++[.hydeRetriever 0]) = 6 := by decide
  have hz : (controlPenalty savedCref uniformQuoteError unitRoleUnused .complete) favorableCompleteS28Before [.query 1] (.hydeRetriever 0) = 0 := by
    apply control_penalty_empty_of_prior_terminal .complete savedCref uniformQuoteError favorableCompleteS28Before [.query 1] (.hydeRetriever 0) 1 (by decide)
    · decide
    · decide
  unfold indexScore
  rw [hs,hp,hn,hz]
  simp only [BackupStat.mean]
  norm_num

theorem favorableCompleteS28D1I2 : indexScore (7/5) (controlPenalty savedCref uniformQuoteError unitRoleUnused .complete) favorableCompleteS28Before [.query 1] (.hydeRetriever 2) = treeIndex ((0/1)/5) (7/5) 0 20 5 := by
  have hs : replayBackup favorableCompleteS28Before emptyStatistics ([.query 1]++[.hydeRetriever 2]) = ⟨5,(0/1)⟩ := by
    rw [replayBackup_empty_closed_form]
    simp +decide [backedEvents,favorableCompleteS28Before,favorableCompleteProposal,favorableCompleteEvent1,favorableCompleteEvent2,favorableCompleteEvent3,favorableCompleteEvent4,favorableCompleteEvent5,favorableCompleteEvent6,favorableCompleteEvent7,favorableCompleteEvent8,favorableCompleteEvent9,favorableCompleteEvent10,favorableCompleteEvent11,favorableCompleteEvent12,favorableCompleteEvent13,favorableCompleteEvent14,favorableCompleteEvent15,favorableCompleteEvent16,favorableCompleteEvent17,favorableCompleteEvent18,favorableCompleteEvent19,favorableCompleteEvent20,favorableCompleteEvent21,favorableCompleteEvent22,favorableCompleteEvent23,favorableCompleteEvent24,favorableCompleteEvent25,favorableCompleteEvent26,favorableCompleteEvent27,taskReward]
    <;> norm_num
  have hp : rawVisits favorableCompleteS28Before [.query 1] = 20 := by decide
  have hn : rawVisits favorableCompleteS28Before ([.query 1]++[.hydeRetriever 2]) = 5 := by decide
  have hz : (controlPenalty savedCref uniformQuoteError unitRoleUnused .complete) favorableCompleteS28Before [.query 1] (.hydeRetriever 2) = 0 := by
    apply control_penalty_empty_of_prior_terminal .complete savedCref uniformQuoteError favorableCompleteS28Before [.query 1] (.hydeRetriever 2) 10 (by decide)
    · decide
    · decide
  unfold indexScore
  rw [hs,hp,hn,hz]
  simp only [BackupStat.mean]
  norm_num

theorem favorableCompleteS28D1Cmp0 : indexScore (7/5) (controlPenalty savedCref uniformQuoteError unitRoleUnused .complete) favorableCompleteS28Before [.query 1] (.hydeRetriever 1) < indexScore (7/5) (controlPenalty savedCref uniformQuoteError unitRoleUnused .complete) favorableCompleteS28Before [.query 1] (.hydeRetriever 2) := by
  rw [favorableCompleteS28D1I0,favorableCompleteS28D1I2]
  have h := index_strict_order_from_intervals ((0/1)/5) ((3/2)/8) 0 0 (54622631/50000000) (21591493/25000000)
    (treeBonus (7/5) 20 5) (treeBonus (7/5) 20 8)
    (trajectory_bonus_20_5).1 (trajectory_bonus_20_8).2 (by norm_num)
  simpa only [treeIndex,sub_zero] using h

theorem favorableCompleteS28D1Cmp1 : indexScore (7/5) (controlPenalty savedCref uniformQuoteError unitRoleUnused .complete) favorableCompleteS28Before [.query 1] (.hydeRetriever 0) < indexScore (7/5) (controlPenalty savedCref uniformQuoteError unitRoleUnused .complete) favorableCompleteS28Before [.query 1] (.hydeRetriever 2) := by
  rw [favorableCompleteS28D1I1,favorableCompleteS28D1I2]
  have h := index_strict_order_from_intervals ((0/1)/5) ((0/1)/6) 0 0 (54622631/50000000) (9972683/10000000)
    (treeBonus (7/5) 20 5) (treeBonus (7/5) 20 6)
    (trajectory_bonus_20_5).1 (trajectory_bonus_20_6).2 (by norm_num)
  simpa only [treeIndex,sub_zero] using h

theorem favorableCompleteS28Choice1 : nativeFirstChoice (indexScore (7/5) (controlPenalty savedCref uniformQuoteError unitRoleUnused .complete) favorableCompleteS28Before [.query 1]) favorableCompleteS28Before [.query 1] = .hydeRetriever 2 := by
  apply visited_choice_from_ordered_certificate _ _ [.query 1] [.hydeRetriever 1,.hydeRetriever 0] [] (.hydeRetriever 2) (by decide)
  · intro a ha
    have ho : orderedLegalAvailable [.query 1] = [.hydeRetriever 1,.hydeRetriever 0,.hydeRetriever 2] := by decide
    rw [ho] at ha
    simp only [List.mem_cons,List.not_mem_nil,or_false] at ha
    rcases ha with rfl | rfl | rfl <;> decide
  · intro a ha
    simp only [List.mem_cons,List.not_mem_nil,or_false] at ha
    rcases ha with rfl | rfl
    · exact favorableCompleteS28D1Cmp0
    · exact favorableCompleteS28D1Cmp1
  · simp

theorem favorableCompleteS28D2I0 : indexScore (7/5) (controlPenalty savedCref uniformQuoteError unitRoleUnused .complete) favorableCompleteS28Before [.query 1,.hydeRetriever 2] (.selection 1) = treeIndex ((0/1)/1) (7/5) 0 5 1 := by
  have hs : replayBackup favorableCompleteS28Before emptyStatistics ([.query 1,.hydeRetriever 2]++[.selection 1]) = ⟨1,(0/1)⟩ := by
    rw [replayBackup_empty_closed_form]
    simp +decide [backedEvents,favorableCompleteS28Before,favorableCompleteProposal,favorableCompleteEvent1,favorableCompleteEvent2,favorableCompleteEvent3,favorableCompleteEvent4,favorableCompleteEvent5,favorableCompleteEvent6,favorableCompleteEvent7,favorableCompleteEvent8,favorableCompleteEvent9,favorableCompleteEvent10,favorableCompleteEvent11,favorableCompleteEvent12,favorableCompleteEvent13,favorableCompleteEvent14,favorableCompleteEvent15,favorableCompleteEvent16,favorableCompleteEvent17,favorableCompleteEvent18,favorableCompleteEvent19,favorableCompleteEvent20,favorableCompleteEvent21,favorableCompleteEvent22,favorableCompleteEvent23,favorableCompleteEvent24,favorableCompleteEvent25,favorableCompleteEvent26,favorableCompleteEvent27,taskReward]
    <;> norm_num
  have hp : rawVisits favorableCompleteS28Before [.query 1,.hydeRetriever 2] = 5 := by decide
  have hn : rawVisits favorableCompleteS28Before ([.query 1,.hydeRetriever 2]++[.selection 1]) = 1 := by decide
  have hz : (controlPenalty savedCref uniformQuoteError unitRoleUnused .complete) favorableCompleteS28Before [.query 1,.hydeRetriever 2] (.selection 1) = 0 := by
    apply control_penalty_empty_of_prior_terminal .complete savedCref uniformQuoteError favorableCompleteS28Before [.query 1,.hydeRetriever 2] (.selection 1) 17 (by decide)
    · decide
    · decide
  unfold indexScore
  rw [hs,hp,hn,hz]
  simp only [BackupStat.mean]
  norm_num

theorem favorableCompleteS28D2I1 : indexScore (7/5) (controlPenalty savedCref uniformQuoteError unitRoleUnused .complete) favorableCompleteS28Before [.query 1,.hydeRetriever 2] (.selection 2) = treeIndex ((0/1)/1) (7/5) 0 5 1 := by
  have hs : replayBackup favorableCompleteS28Before emptyStatistics ([.query 1,.hydeRetriever 2]++[.selection 2]) = ⟨1,(0/1)⟩ := by
    rw [replayBackup_empty_closed_form]
    simp +decide [backedEvents,favorableCompleteS28Before,favorableCompleteProposal,favorableCompleteEvent1,favorableCompleteEvent2,favorableCompleteEvent3,favorableCompleteEvent4,favorableCompleteEvent5,favorableCompleteEvent6,favorableCompleteEvent7,favorableCompleteEvent8,favorableCompleteEvent9,favorableCompleteEvent10,favorableCompleteEvent11,favorableCompleteEvent12,favorableCompleteEvent13,favorableCompleteEvent14,favorableCompleteEvent15,favorableCompleteEvent16,favorableCompleteEvent17,favorableCompleteEvent18,favorableCompleteEvent19,favorableCompleteEvent20,favorableCompleteEvent21,favorableCompleteEvent22,favorableCompleteEvent23,favorableCompleteEvent24,favorableCompleteEvent25,favorableCompleteEvent26,favorableCompleteEvent27,taskReward]
    <;> norm_num
  have hp : rawVisits favorableCompleteS28Before [.query 1,.hydeRetriever 2] = 5 := by decide
  have hn : rawVisits favorableCompleteS28Before ([.query 1,.hydeRetriever 2]++[.selection 2]) = 1 := by decide
  have hz : (controlPenalty savedCref uniformQuoteError unitRoleUnused .complete) favorableCompleteS28Before [.query 1,.hydeRetriever 2] (.selection 2) = 0 := by
    apply control_penalty_empty_of_prior_terminal .complete savedCref uniformQuoteError favorableCompleteS28Before [.query 1,.hydeRetriever 2] (.selection 2) 20 (by decide)
    · decide
    · decide
  unfold indexScore
  rw [hs,hp,hn,hz]
  simp only [BackupStat.mean]
  norm_num

theorem favorableCompleteS28D2I2 : indexScore (7/5) (controlPenalty savedCref uniformQuoteError unitRoleUnused .complete) favorableCompleteS28Before [.query 1,.hydeRetriever 2] (.selection 3) = treeIndex ((0/1)/1) (7/5) 0 5 1 := by
  have hs : replayBackup favorableCompleteS28Before emptyStatistics ([.query 1,.hydeRetriever 2]++[.selection 3]) = ⟨1,(0/1)⟩ := by
    rw [replayBackup_empty_closed_form]
    simp +decide [backedEvents,favorableCompleteS28Before,favorableCompleteProposal,favorableCompleteEvent1,favorableCompleteEvent2,favorableCompleteEvent3,favorableCompleteEvent4,favorableCompleteEvent5,favorableCompleteEvent6,favorableCompleteEvent7,favorableCompleteEvent8,favorableCompleteEvent9,favorableCompleteEvent10,favorableCompleteEvent11,favorableCompleteEvent12,favorableCompleteEvent13,favorableCompleteEvent14,favorableCompleteEvent15,favorableCompleteEvent16,favorableCompleteEvent17,favorableCompleteEvent18,favorableCompleteEvent19,favorableCompleteEvent20,favorableCompleteEvent21,favorableCompleteEvent22,favorableCompleteEvent23,favorableCompleteEvent24,favorableCompleteEvent25,favorableCompleteEvent26,favorableCompleteEvent27,taskReward]
    <;> norm_num
  have hp : rawVisits favorableCompleteS28Before [.query 1,.hydeRetriever 2] = 5 := by decide
  have hn : rawVisits favorableCompleteS28Before ([.query 1,.hydeRetriever 2]++[.selection 3]) = 1 := by decide
  have hz : (controlPenalty savedCref uniformQuoteError unitRoleUnused .complete) favorableCompleteS28Before [.query 1,.hydeRetriever 2] (.selection 3) = 0 := by
    apply control_penalty_empty_of_prior_terminal .complete savedCref uniformQuoteError favorableCompleteS28Before [.query 1,.hydeRetriever 2] (.selection 3) 24 (by decide)
    · decide
    · decide
  unfold indexScore
  rw [hs,hp,hn,hz]
  simp only [BackupStat.mean]
  norm_num

theorem favorableCompleteS28D2I3 : indexScore (7/5) (controlPenalty savedCref uniformQuoteError unitRoleUnused .complete) favorableCompleteS28Before [.query 1,.hydeRetriever 2] (.selection 0) = treeIndex ((0/1)/1) (7/5) 0 5 1 := by
  have hs : replayBackup favorableCompleteS28Before emptyStatistics ([.query 1,.hydeRetriever 2]++[.selection 0]) = ⟨1,(0/1)⟩ := by
    rw [replayBackup_empty_closed_form]
    simp +decide [backedEvents,favorableCompleteS28Before,favorableCompleteProposal,favorableCompleteEvent1,favorableCompleteEvent2,favorableCompleteEvent3,favorableCompleteEvent4,favorableCompleteEvent5,favorableCompleteEvent6,favorableCompleteEvent7,favorableCompleteEvent8,favorableCompleteEvent9,favorableCompleteEvent10,favorableCompleteEvent11,favorableCompleteEvent12,favorableCompleteEvent13,favorableCompleteEvent14,favorableCompleteEvent15,favorableCompleteEvent16,favorableCompleteEvent17,favorableCompleteEvent18,favorableCompleteEvent19,favorableCompleteEvent20,favorableCompleteEvent21,favorableCompleteEvent22,favorableCompleteEvent23,favorableCompleteEvent24,favorableCompleteEvent25,favorableCompleteEvent26,favorableCompleteEvent27,taskReward]
    <;> norm_num
  have hp : rawVisits favorableCompleteS28Before [.query 1,.hydeRetriever 2] = 5 := by decide
  have hn : rawVisits favorableCompleteS28Before ([.query 1,.hydeRetriever 2]++[.selection 0]) = 1 := by decide
  have hz : (controlPenalty savedCref uniformQuoteError unitRoleUnused .complete) favorableCompleteS28Before [.query 1,.hydeRetriever 2] (.selection 0) = 0 := by
    apply control_penalty_empty_of_prior_terminal .complete savedCref uniformQuoteError favorableCompleteS28Before [.query 1,.hydeRetriever 2] (.selection 0) 10 (by decide)
    · decide
    · decide
  unfold indexScore
  rw [hs,hp,hn,hz]
  simp only [BackupStat.mean]
  norm_num

theorem favorableCompleteS28D2Cmp1 : indexScore (7/5) (controlPenalty savedCref uniformQuoteError unitRoleUnused .complete) favorableCompleteS28Before [.query 1,.hydeRetriever 2] (.selection 2) ≤ indexScore (7/5) (controlPenalty savedCref uniformQuoteError unitRoleUnused .complete) favorableCompleteS28Before [.query 1,.hydeRetriever 2] (.selection 1) := by
  rw [favorableCompleteS28D2I1,favorableCompleteS28D2I0]

theorem favorableCompleteS28D2Cmp2 : indexScore (7/5) (controlPenalty savedCref uniformQuoteError unitRoleUnused .complete) favorableCompleteS28Before [.query 1,.hydeRetriever 2] (.selection 3) ≤ indexScore (7/5) (controlPenalty savedCref uniformQuoteError unitRoleUnused .complete) favorableCompleteS28Before [.query 1,.hydeRetriever 2] (.selection 1) := by
  rw [favorableCompleteS28D2I2,favorableCompleteS28D2I0]

theorem favorableCompleteS28D2Cmp3 : indexScore (7/5) (controlPenalty savedCref uniformQuoteError unitRoleUnused .complete) favorableCompleteS28Before [.query 1,.hydeRetriever 2] (.selection 0) ≤ indexScore (7/5) (controlPenalty savedCref uniformQuoteError unitRoleUnused .complete) favorableCompleteS28Before [.query 1,.hydeRetriever 2] (.selection 1) := by
  rw [favorableCompleteS28D2I3,favorableCompleteS28D2I0]

theorem favorableCompleteS28Choice2 : nativeFirstChoice (indexScore (7/5) (controlPenalty savedCref uniformQuoteError unitRoleUnused .complete) favorableCompleteS28Before [.query 1,.hydeRetriever 2]) favorableCompleteS28Before [.query 1,.hydeRetriever 2] = .selection 1 := by
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
    · exact favorableCompleteS28D2Cmp1
    · exact favorableCompleteS28D2Cmp2
    · exact favorableCompleteS28D2Cmp3

theorem favorableCompleteS28ActualEvent : nativeEvent budgetTape (7/5) (controlPenalty savedCref uniformQuoteError unitRoleUnused .complete)
    (taskReward false (2/5) (1/2)) favorableCompleteS28Before = favorableCompleteEvent28 := by
  have hs0 := native_select_existing_step budgetTape (7/5) (controlPenalty savedCref uniformQuoteError unitRoleUnused .complete) favorableCompleteS28Before 8 [] (.query 1)
    (by decide) (by decide) favorableCompleteS28Choice0
  have hs1 := native_select_existing_step budgetTape (7/5) (controlPenalty savedCref uniformQuoteError unitRoleUnused .complete) favorableCompleteS28Before 7 [.query 1] (.hydeRetriever 2)
    (by decide) (by decide) favorableCompleteS28Choice1
  have hs2 := native_select_existing_step budgetTape (7/5) (controlPenalty savedCref uniformQuoteError unitRoleUnused .complete) favorableCompleteS28Before 6 [.query 1,.hydeRetriever 2] (.selection 1)
    (by decide) (by decide) favorableCompleteS28Choice2
  have hnew := native_select_new_step budgetTape (7/5) (controlPenalty savedCref uniformQuoteError unitRoleUnused .complete) favorableCompleteS28Before 5 [.query 1,.hydeRetriever 2,.selection 1]
    [.width 3,.width 0,.width 1,.width 2] (.width 0) (by decide) (by decide) (by decide) (by decide)
  have hs : nativeSelect budgetTape (7/5) (controlPenalty savedCref uniformQuoteError unitRoleUnused .complete) favorableCompleteS28Before 9 [] = [.query 1,.hydeRetriever 2,.selection 1,.width 0] := by
    rw [hs0]
    change nativeSelect budgetTape (7/5) (controlPenalty savedCref uniformQuoteError unitRoleUnused .complete) favorableCompleteS28Before 8 [.query 1] = _
    rw [hs1]
    change nativeSelect budgetTape (7/5) (controlPenalty savedCref uniformQuoteError unitRoleUnused .complete) favorableCompleteS28Before 7 [.query 1,.hydeRetriever 2] = _
    rw [hs2]
    change nativeSelect budgetTape (7/5) (controlPenalty savedCref uniformQuoteError unitRoleUnused .complete) favorableCompleteS28Before 6 [.query 1,.hydeRetriever 2,.selection 1] = _
    rw [hnew] <;> rfl
  have hr : repairedRollout budgetTape favorableCompleteS28Before 9 [.query 1,.hydeRetriever 2,.selection 1,.width 0] = [.query 1,.hydeRetriever 2,.selection 1,.width 0,.stop,.reranker 0,.topm 0,.context 0,.answer 0] := by decide
  simp only [nativeEvent,hs,hr]
  rfl

def favorableCompleteS29Before := favorableCompleteProposal.take 28

theorem favorableCompleteS29Choice0 : nativeFirstChoice (indexScore (7/5) (controlPenalty savedCref uniformQuoteError unitRoleUnused .complete) favorableCompleteS29Before []) favorableCompleteS29Before [] = .query 1 := by
  apply complete_root_from_physical_gap favorableCompleteS29Before (favorableComplete_prefix_rewards 28) (by decide)
  · intro q; fin_cases q <;> decide
  · decide
  · intro q hq
    exact AgentUCTNextExact.favorable_complete_normal_root_physical_quote_exact 28 (by omega) q hq

theorem favorableCompleteS29D1I0 : indexScore (7/5) (controlPenalty savedCref uniformQuoteError unitRoleUnused .complete) favorableCompleteS29Before [.query 1] (.hydeRetriever 1) = treeIndex ((3/2)/8) (7/5) 0 21 8 := by
  have hs : replayBackup favorableCompleteS29Before emptyStatistics ([.query 1]++[.hydeRetriever 1]) = ⟨8,(3/2)⟩ := by
    rw [replayBackup_empty_closed_form]
    simp +decide [backedEvents,favorableCompleteS29Before,favorableCompleteProposal,favorableCompleteEvent1,favorableCompleteEvent2,favorableCompleteEvent3,favorableCompleteEvent4,favorableCompleteEvent5,favorableCompleteEvent6,favorableCompleteEvent7,favorableCompleteEvent8,favorableCompleteEvent9,favorableCompleteEvent10,favorableCompleteEvent11,favorableCompleteEvent12,favorableCompleteEvent13,favorableCompleteEvent14,favorableCompleteEvent15,favorableCompleteEvent16,favorableCompleteEvent17,favorableCompleteEvent18,favorableCompleteEvent19,favorableCompleteEvent20,favorableCompleteEvent21,favorableCompleteEvent22,favorableCompleteEvent23,favorableCompleteEvent24,favorableCompleteEvent25,favorableCompleteEvent26,favorableCompleteEvent27,favorableCompleteEvent28,taskReward]
    <;> norm_num
  have hp : rawVisits favorableCompleteS29Before [.query 1] = 21 := by decide
  have hn : rawVisits favorableCompleteS29Before ([.query 1]++[.hydeRetriever 1]) = 8 := by decide
  have hz : (controlPenalty savedCref uniformQuoteError unitRoleUnused .complete) favorableCompleteS29Before [.query 1] (.hydeRetriever 1) = 0 := by
    apply control_penalty_empty_of_prior_terminal .complete savedCref uniformQuoteError favorableCompleteS29Before [.query 1] (.hydeRetriever 1) 8 (by decide)
    · decide
    · decide
  unfold indexScore
  rw [hs,hp,hn,hz]
  simp only [BackupStat.mean]
  norm_num

theorem favorableCompleteS29D1I1 : indexScore (7/5) (controlPenalty savedCref uniformQuoteError unitRoleUnused .complete) favorableCompleteS29Before [.query 1] (.hydeRetriever 0) = treeIndex ((0/1)/6) (7/5) 0 21 6 := by
  have hs : replayBackup favorableCompleteS29Before emptyStatistics ([.query 1]++[.hydeRetriever 0]) = ⟨6,(0/1)⟩ := by
    rw [replayBackup_empty_closed_form]
    simp +decide [backedEvents,favorableCompleteS29Before,favorableCompleteProposal,favorableCompleteEvent1,favorableCompleteEvent2,favorableCompleteEvent3,favorableCompleteEvent4,favorableCompleteEvent5,favorableCompleteEvent6,favorableCompleteEvent7,favorableCompleteEvent8,favorableCompleteEvent9,favorableCompleteEvent10,favorableCompleteEvent11,favorableCompleteEvent12,favorableCompleteEvent13,favorableCompleteEvent14,favorableCompleteEvent15,favorableCompleteEvent16,favorableCompleteEvent17,favorableCompleteEvent18,favorableCompleteEvent19,favorableCompleteEvent20,favorableCompleteEvent21,favorableCompleteEvent22,favorableCompleteEvent23,favorableCompleteEvent24,favorableCompleteEvent25,favorableCompleteEvent26,favorableCompleteEvent27,favorableCompleteEvent28,taskReward]
    <;> norm_num
  have hp : rawVisits favorableCompleteS29Before [.query 1] = 21 := by decide
  have hn : rawVisits favorableCompleteS29Before ([.query 1]++[.hydeRetriever 0]) = 6 := by decide
  have hz : (controlPenalty savedCref uniformQuoteError unitRoleUnused .complete) favorableCompleteS29Before [.query 1] (.hydeRetriever 0) = 0 := by
    apply control_penalty_empty_of_prior_terminal .complete savedCref uniformQuoteError favorableCompleteS29Before [.query 1] (.hydeRetriever 0) 1 (by decide)
    · decide
    · decide
  unfold indexScore
  rw [hs,hp,hn,hz]
  simp only [BackupStat.mean]
  norm_num

theorem favorableCompleteS29D1I2 : indexScore (7/5) (controlPenalty savedCref uniformQuoteError unitRoleUnused .complete) favorableCompleteS29Before [.query 1] (.hydeRetriever 2) = treeIndex ((0/1)/6) (7/5) 0 21 6 := by
  have hs : replayBackup favorableCompleteS29Before emptyStatistics ([.query 1]++[.hydeRetriever 2]) = ⟨6,(0/1)⟩ := by
    rw [replayBackup_empty_closed_form]
    simp +decide [backedEvents,favorableCompleteS29Before,favorableCompleteProposal,favorableCompleteEvent1,favorableCompleteEvent2,favorableCompleteEvent3,favorableCompleteEvent4,favorableCompleteEvent5,favorableCompleteEvent6,favorableCompleteEvent7,favorableCompleteEvent8,favorableCompleteEvent9,favorableCompleteEvent10,favorableCompleteEvent11,favorableCompleteEvent12,favorableCompleteEvent13,favorableCompleteEvent14,favorableCompleteEvent15,favorableCompleteEvent16,favorableCompleteEvent17,favorableCompleteEvent18,favorableCompleteEvent19,favorableCompleteEvent20,favorableCompleteEvent21,favorableCompleteEvent22,favorableCompleteEvent23,favorableCompleteEvent24,favorableCompleteEvent25,favorableCompleteEvent26,favorableCompleteEvent27,favorableCompleteEvent28,taskReward]
    <;> norm_num
  have hp : rawVisits favorableCompleteS29Before [.query 1] = 21 := by decide
  have hn : rawVisits favorableCompleteS29Before ([.query 1]++[.hydeRetriever 2]) = 6 := by decide
  have hz : (controlPenalty savedCref uniformQuoteError unitRoleUnused .complete) favorableCompleteS29Before [.query 1] (.hydeRetriever 2) = 0 := by
    apply control_penalty_empty_of_prior_terminal .complete savedCref uniformQuoteError favorableCompleteS29Before [.query 1] (.hydeRetriever 2) 10 (by decide)
    · decide
    · decide
  unfold indexScore
  rw [hs,hp,hn,hz]
  simp only [BackupStat.mean]
  norm_num

theorem favorableCompleteS29D1Cmp1 : indexScore (7/5) (controlPenalty savedCref uniformQuoteError unitRoleUnused .complete) favorableCompleteS29Before [.query 1] (.hydeRetriever 0) ≤ indexScore (7/5) (controlPenalty savedCref uniformQuoteError unitRoleUnused .complete) favorableCompleteS29Before [.query 1] (.hydeRetriever 1) := by
  rw [favorableCompleteS29D1I1,favorableCompleteS29D1I0]
  have h := index_weak_order_from_intervals ((3/2)/8) ((0/1)/6) 0 0 (43511643/50000000) (50242927/50000000)
    (treeBonus (7/5) 21 8) (treeBonus (7/5) 21 6)
    (trajectory_bonus_21_8).1 (trajectory_bonus_21_6).2 (by norm_num)
  simpa only [treeIndex,sub_zero] using h

theorem favorableCompleteS29D1Cmp2 : indexScore (7/5) (controlPenalty savedCref uniformQuoteError unitRoleUnused .complete) favorableCompleteS29Before [.query 1] (.hydeRetriever 2) ≤ indexScore (7/5) (controlPenalty savedCref uniformQuoteError unitRoleUnused .complete) favorableCompleteS29Before [.query 1] (.hydeRetriever 1) := by
  rw [favorableCompleteS29D1I2,favorableCompleteS29D1I0]
  have h := index_weak_order_from_intervals ((3/2)/8) ((0/1)/6) 0 0 (43511643/50000000) (50242927/50000000)
    (treeBonus (7/5) 21 8) (treeBonus (7/5) 21 6)
    (trajectory_bonus_21_8).1 (trajectory_bonus_21_6).2 (by norm_num)
  simpa only [treeIndex,sub_zero] using h

theorem favorableCompleteS29Choice1 : nativeFirstChoice (indexScore (7/5) (controlPenalty savedCref uniformQuoteError unitRoleUnused .complete) favorableCompleteS29Before [.query 1]) favorableCompleteS29Before [.query 1] = .hydeRetriever 1 := by
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
    · exact favorableCompleteS29D1Cmp1
    · exact favorableCompleteS29D1Cmp2

theorem favorableCompleteS29D2I0 : indexScore (7/5) (controlPenalty savedCref uniformQuoteError unitRoleUnused .complete) favorableCompleteS29Before [.query 1,.hydeRetriever 1] (.selection 1) = treeIndex ((0/1)/2) (7/5) 0 8 2 := by
  have hs : replayBackup favorableCompleteS29Before emptyStatistics ([.query 1,.hydeRetriever 1]++[.selection 1]) = ⟨2,(0/1)⟩ := by
    rw [replayBackup_empty_closed_form]
    simp +decide [backedEvents,favorableCompleteS29Before,favorableCompleteProposal,favorableCompleteEvent1,favorableCompleteEvent2,favorableCompleteEvent3,favorableCompleteEvent4,favorableCompleteEvent5,favorableCompleteEvent6,favorableCompleteEvent7,favorableCompleteEvent8,favorableCompleteEvent9,favorableCompleteEvent10,favorableCompleteEvent11,favorableCompleteEvent12,favorableCompleteEvent13,favorableCompleteEvent14,favorableCompleteEvent15,favorableCompleteEvent16,favorableCompleteEvent17,favorableCompleteEvent18,favorableCompleteEvent19,favorableCompleteEvent20,favorableCompleteEvent21,favorableCompleteEvent22,favorableCompleteEvent23,favorableCompleteEvent24,favorableCompleteEvent25,favorableCompleteEvent26,favorableCompleteEvent27,favorableCompleteEvent28,taskReward]
    <;> norm_num
  have hp : rawVisits favorableCompleteS29Before [.query 1,.hydeRetriever 1] = 8 := by decide
  have hn : rawVisits favorableCompleteS29Before ([.query 1,.hydeRetriever 1]++[.selection 1]) = 2 := by decide
  have hz : (controlPenalty savedCref uniformQuoteError unitRoleUnused .complete) favorableCompleteS29Before [.query 1,.hydeRetriever 1] (.selection 1) = 0 := by
    apply control_penalty_empty_of_prior_terminal .complete savedCref uniformQuoteError favorableCompleteS29Before [.query 1,.hydeRetriever 1] (.selection 1) 14 (by decide)
    · decide
    · decide
  unfold indexScore
  rw [hs,hp,hn,hz]
  simp only [BackupStat.mean]
  norm_num

theorem favorableCompleteS29D2I1 : indexScore (7/5) (controlPenalty savedCref uniformQuoteError unitRoleUnused .complete) favorableCompleteS29Before [.query 1,.hydeRetriever 1] (.selection 2) = treeIndex ((0/1)/2) (7/5) 0 8 2 := by
  have hs : replayBackup favorableCompleteS29Before emptyStatistics ([.query 1,.hydeRetriever 1]++[.selection 2]) = ⟨2,(0/1)⟩ := by
    rw [replayBackup_empty_closed_form]
    simp +decide [backedEvents,favorableCompleteS29Before,favorableCompleteProposal,favorableCompleteEvent1,favorableCompleteEvent2,favorableCompleteEvent3,favorableCompleteEvent4,favorableCompleteEvent5,favorableCompleteEvent6,favorableCompleteEvent7,favorableCompleteEvent8,favorableCompleteEvent9,favorableCompleteEvent10,favorableCompleteEvent11,favorableCompleteEvent12,favorableCompleteEvent13,favorableCompleteEvent14,favorableCompleteEvent15,favorableCompleteEvent16,favorableCompleteEvent17,favorableCompleteEvent18,favorableCompleteEvent19,favorableCompleteEvent20,favorableCompleteEvent21,favorableCompleteEvent22,favorableCompleteEvent23,favorableCompleteEvent24,favorableCompleteEvent25,favorableCompleteEvent26,favorableCompleteEvent27,favorableCompleteEvent28,taskReward]
    <;> norm_num
  have hp : rawVisits favorableCompleteS29Before [.query 1,.hydeRetriever 1] = 8 := by decide
  have hn : rawVisits favorableCompleteS29Before ([.query 1,.hydeRetriever 1]++[.selection 2]) = 2 := by decide
  have hz : (controlPenalty savedCref uniformQuoteError unitRoleUnused .complete) favorableCompleteS29Before [.query 1,.hydeRetriever 1] (.selection 2) = 0 := by
    apply control_penalty_empty_of_prior_terminal .complete savedCref uniformQuoteError favorableCompleteS29Before [.query 1,.hydeRetriever 1] (.selection 2) 15 (by decide)
    · decide
    · decide
  unfold indexScore
  rw [hs,hp,hn,hz]
  simp only [BackupStat.mean]
  norm_num

theorem favorableCompleteS29D2I2 : indexScore (7/5) (controlPenalty savedCref uniformQuoteError unitRoleUnused .complete) favorableCompleteS29Before [.query 1,.hydeRetriever 1] (.selection 3) = treeIndex ((0/1)/1) (7/5) 0 8 1 := by
  have hs : replayBackup favorableCompleteS29Before emptyStatistics ([.query 1,.hydeRetriever 1]++[.selection 3]) = ⟨1,(0/1)⟩ := by
    rw [replayBackup_empty_closed_form]
    simp +decide [backedEvents,favorableCompleteS29Before,favorableCompleteProposal,favorableCompleteEvent1,favorableCompleteEvent2,favorableCompleteEvent3,favorableCompleteEvent4,favorableCompleteEvent5,favorableCompleteEvent6,favorableCompleteEvent7,favorableCompleteEvent8,favorableCompleteEvent9,favorableCompleteEvent10,favorableCompleteEvent11,favorableCompleteEvent12,favorableCompleteEvent13,favorableCompleteEvent14,favorableCompleteEvent15,favorableCompleteEvent16,favorableCompleteEvent17,favorableCompleteEvent18,favorableCompleteEvent19,favorableCompleteEvent20,favorableCompleteEvent21,favorableCompleteEvent22,favorableCompleteEvent23,favorableCompleteEvent24,favorableCompleteEvent25,favorableCompleteEvent26,favorableCompleteEvent27,favorableCompleteEvent28,taskReward]
    <;> norm_num
  have hp : rawVisits favorableCompleteS29Before [.query 1,.hydeRetriever 1] = 8 := by decide
  have hn : rawVisits favorableCompleteS29Before ([.query 1,.hydeRetriever 1]++[.selection 3]) = 1 := by decide
  have hz : (controlPenalty savedCref uniformQuoteError unitRoleUnused .complete) favorableCompleteS29Before [.query 1,.hydeRetriever 1] (.selection 3) = 0 := by
    apply control_penalty_empty_of_prior_terminal .complete savedCref uniformQuoteError favorableCompleteS29Before [.query 1,.hydeRetriever 1] (.selection 3) 18 (by decide)
    · decide
    · decide
  unfold indexScore
  rw [hs,hp,hn,hz]
  simp only [BackupStat.mean]
  norm_num

theorem favorableCompleteS29D2I3 : indexScore (7/5) (controlPenalty savedCref uniformQuoteError unitRoleUnused .complete) favorableCompleteS29Before [.query 1,.hydeRetriever 1] (.selection 0) = treeIndex ((1/1)/2) (7/5) 0 8 2 := by
  have hs : replayBackup favorableCompleteS29Before emptyStatistics ([.query 1,.hydeRetriever 1]++[.selection 0]) = ⟨2,(1/1)⟩ := by
    rw [replayBackup_empty_closed_form]
    simp +decide [backedEvents,favorableCompleteS29Before,favorableCompleteProposal,favorableCompleteEvent1,favorableCompleteEvent2,favorableCompleteEvent3,favorableCompleteEvent4,favorableCompleteEvent5,favorableCompleteEvent6,favorableCompleteEvent7,favorableCompleteEvent8,favorableCompleteEvent9,favorableCompleteEvent10,favorableCompleteEvent11,favorableCompleteEvent12,favorableCompleteEvent13,favorableCompleteEvent14,favorableCompleteEvent15,favorableCompleteEvent16,favorableCompleteEvent17,favorableCompleteEvent18,favorableCompleteEvent19,favorableCompleteEvent20,favorableCompleteEvent21,favorableCompleteEvent22,favorableCompleteEvent23,favorableCompleteEvent24,favorableCompleteEvent25,favorableCompleteEvent26,favorableCompleteEvent27,favorableCompleteEvent28,taskReward]
    <;> norm_num
  have hp : rawVisits favorableCompleteS29Before [.query 1,.hydeRetriever 1] = 8 := by decide
  have hn : rawVisits favorableCompleteS29Before ([.query 1,.hydeRetriever 1]++[.selection 0]) = 2 := by decide
  have hz : (controlPenalty savedCref uniformQuoteError unitRoleUnused .complete) favorableCompleteS29Before [.query 1,.hydeRetriever 1] (.selection 0) = 0 := by
    apply control_penalty_empty_of_prior_terminal .complete savedCref uniformQuoteError favorableCompleteS29Before [.query 1,.hydeRetriever 1] (.selection 0) 8 (by decide)
    · decide
    · decide
  unfold indexScore
  rw [hs,hp,hn,hz]
  simp only [BackupStat.mean]
  norm_num

theorem favorableCompleteS29D2Cmp0 : indexScore (7/5) (controlPenalty savedCref uniformQuoteError unitRoleUnused .complete) favorableCompleteS29Before [.query 1,.hydeRetriever 1] (.selection 1) < indexScore (7/5) (controlPenalty savedCref uniformQuoteError unitRoleUnused .complete) favorableCompleteS29Before [.query 1,.hydeRetriever 1] (.selection 3) := by
  rw [favorableCompleteS29D2I0,favorableCompleteS29D2I2]
  have h := index_strict_order_from_intervals ((0/1)/1) ((0/1)/2) 0 0 (103761259/50000000) (1146411/781250)
    (treeBonus (7/5) 8 1) (treeBonus (7/5) 8 2)
    (trajectory_bonus_8_1).1 (trajectory_bonus_8_2).2 (by norm_num)
  simpa only [treeIndex,sub_zero] using h

theorem favorableCompleteS29D2Cmp1 : indexScore (7/5) (controlPenalty savedCref uniformQuoteError unitRoleUnused .complete) favorableCompleteS29Before [.query 1,.hydeRetriever 1] (.selection 2) < indexScore (7/5) (controlPenalty savedCref uniformQuoteError unitRoleUnused .complete) favorableCompleteS29Before [.query 1,.hydeRetriever 1] (.selection 3) := by
  rw [favorableCompleteS29D2I1,favorableCompleteS29D2I2]
  have h := index_strict_order_from_intervals ((0/1)/1) ((0/1)/2) 0 0 (103761259/50000000) (1146411/781250)
    (treeBonus (7/5) 8 1) (treeBonus (7/5) 8 2)
    (trajectory_bonus_8_1).1 (trajectory_bonus_8_2).2 (by norm_num)
  simpa only [treeIndex,sub_zero] using h

theorem favorableCompleteS29D2Cmp3 : indexScore (7/5) (controlPenalty savedCref uniformQuoteError unitRoleUnused .complete) favorableCompleteS29Before [.query 1,.hydeRetriever 1] (.selection 0) ≤ indexScore (7/5) (controlPenalty savedCref uniformQuoteError unitRoleUnused .complete) favorableCompleteS29Before [.query 1,.hydeRetriever 1] (.selection 3) := by
  rw [favorableCompleteS29D2I3,favorableCompleteS29D2I2]
  have h := index_weak_order_from_intervals ((0/1)/1) ((1/1)/2) 0 0 (103761259/50000000) (1146411/781250)
    (treeBonus (7/5) 8 1) (treeBonus (7/5) 8 2)
    (trajectory_bonus_8_1).1 (trajectory_bonus_8_2).2 (by norm_num)
  simpa only [treeIndex,sub_zero] using h

theorem favorableCompleteS29Choice2 : nativeFirstChoice (indexScore (7/5) (controlPenalty savedCref uniformQuoteError unitRoleUnused .complete) favorableCompleteS29Before [.query 1,.hydeRetriever 1]) favorableCompleteS29Before [.query 1,.hydeRetriever 1] = .selection 3 := by
  apply visited_choice_from_ordered_certificate _ _ [.query 1,.hydeRetriever 1] [.selection 1,.selection 2] [.selection 0] (.selection 3) (by decide)
  · intro a ha
    have ho : orderedLegalAvailable [.query 1,.hydeRetriever 1] = [.selection 1,.selection 2,.selection 3,.selection 0] := by decide
    rw [ho] at ha
    simp only [List.mem_cons,List.not_mem_nil,or_false] at ha
    rcases ha with rfl | rfl | rfl | rfl <;> decide
  · intro a ha
    simp only [List.mem_cons,List.not_mem_nil,or_false] at ha
    rcases ha with rfl | rfl
    · exact favorableCompleteS29D2Cmp0
    · exact favorableCompleteS29D2Cmp1
  · intro a ha
    simp only [List.mem_cons,List.not_mem_nil,or_false] at ha
    rcases ha with rfl
    · exact favorableCompleteS29D2Cmp3

theorem favorableCompleteS29ActualEvent : nativeEvent budgetTape (7/5) (controlPenalty savedCref uniformQuoteError unitRoleUnused .complete)
    (taskReward false (2/5) (1/2)) favorableCompleteS29Before = favorableCompleteEvent29 := by
  have hs0 := native_select_existing_step budgetTape (7/5) (controlPenalty savedCref uniformQuoteError unitRoleUnused .complete) favorableCompleteS29Before 8 [] (.query 1)
    (by decide) (by decide) favorableCompleteS29Choice0
  have hs1 := native_select_existing_step budgetTape (7/5) (controlPenalty savedCref uniformQuoteError unitRoleUnused .complete) favorableCompleteS29Before 7 [.query 1] (.hydeRetriever 1)
    (by decide) (by decide) favorableCompleteS29Choice1
  have hs2 := native_select_existing_step budgetTape (7/5) (controlPenalty savedCref uniformQuoteError unitRoleUnused .complete) favorableCompleteS29Before 6 [.query 1,.hydeRetriever 1] (.selection 3)
    (by decide) (by decide) favorableCompleteS29Choice2
  have hnew := native_select_new_step budgetTape (7/5) (controlPenalty savedCref uniformQuoteError unitRoleUnused .complete) favorableCompleteS29Before 5 [.query 1,.hydeRetriever 1,.selection 3]
    [.width 3,.width 0,.width 1,.width 2] (.width 0) (by decide) (by decide) (by decide) (by decide)
  have hs : nativeSelect budgetTape (7/5) (controlPenalty savedCref uniformQuoteError unitRoleUnused .complete) favorableCompleteS29Before 9 [] = [.query 1,.hydeRetriever 1,.selection 3,.width 0] := by
    rw [hs0]
    change nativeSelect budgetTape (7/5) (controlPenalty savedCref uniformQuoteError unitRoleUnused .complete) favorableCompleteS29Before 8 [.query 1] = _
    rw [hs1]
    change nativeSelect budgetTape (7/5) (controlPenalty savedCref uniformQuoteError unitRoleUnused .complete) favorableCompleteS29Before 7 [.query 1,.hydeRetriever 1] = _
    rw [hs2]
    change nativeSelect budgetTape (7/5) (controlPenalty savedCref uniformQuoteError unitRoleUnused .complete) favorableCompleteS29Before 6 [.query 1,.hydeRetriever 1,.selection 3] = _
    rw [hnew] <;> rfl
  have hr : repairedRollout budgetTape favorableCompleteS29Before 9 [.query 1,.hydeRetriever 1,.selection 3,.width 0] = [.query 1,.hydeRetriever 1,.selection 3,.width 0,.stop,.reranker 0,.topm 0,.context 0,.answer 0] := by decide
  simp only [nativeEvent,hs,hr]
  rfl

def favorableCompleteS30Before := favorableCompleteProposal.take 29

theorem favorableCompleteS30Choice0 : nativeFirstChoice (indexScore (7/5) (controlPenalty savedCref uniformQuoteError unitRoleUnused .complete) favorableCompleteS30Before []) favorableCompleteS30Before [] = .query 1 := by
  apply complete_root_from_physical_gap favorableCompleteS30Before (favorableComplete_prefix_rewards 29) (by decide)
  · intro q; fin_cases q <;> decide
  · decide
  · intro q hq
    exact AgentUCTNextExact.favorable_complete_normal_root_physical_quote_exact 29 (by omega) q hq

theorem favorableCompleteS30D1I0 : indexScore (7/5) (controlPenalty savedCref uniformQuoteError unitRoleUnused .complete) favorableCompleteS30Before [.query 1] (.hydeRetriever 1) = treeIndex ((3/2)/9) (7/5) 0 22 9 := by
  have hs : replayBackup favorableCompleteS30Before emptyStatistics ([.query 1]++[.hydeRetriever 1]) = ⟨9,(3/2)⟩ := by
    rw [replayBackup_empty_closed_form]
    simp +decide [backedEvents,favorableCompleteS30Before,favorableCompleteProposal,favorableCompleteEvent1,favorableCompleteEvent2,favorableCompleteEvent3,favorableCompleteEvent4,favorableCompleteEvent5,favorableCompleteEvent6,favorableCompleteEvent7,favorableCompleteEvent8,favorableCompleteEvent9,favorableCompleteEvent10,favorableCompleteEvent11,favorableCompleteEvent12,favorableCompleteEvent13,favorableCompleteEvent14,favorableCompleteEvent15,favorableCompleteEvent16,favorableCompleteEvent17,favorableCompleteEvent18,favorableCompleteEvent19,favorableCompleteEvent20,favorableCompleteEvent21,favorableCompleteEvent22,favorableCompleteEvent23,favorableCompleteEvent24,favorableCompleteEvent25,favorableCompleteEvent26,favorableCompleteEvent27,favorableCompleteEvent28,favorableCompleteEvent29,taskReward]
    <;> norm_num
  have hp : rawVisits favorableCompleteS30Before [.query 1] = 22 := by decide
  have hn : rawVisits favorableCompleteS30Before ([.query 1]++[.hydeRetriever 1]) = 9 := by decide
  have hz : (controlPenalty savedCref uniformQuoteError unitRoleUnused .complete) favorableCompleteS30Before [.query 1] (.hydeRetriever 1) = 0 := by
    apply control_penalty_empty_of_prior_terminal .complete savedCref uniformQuoteError favorableCompleteS30Before [.query 1] (.hydeRetriever 1) 8 (by decide)
    · decide
    · decide
  unfold indexScore
  rw [hs,hp,hn,hz]
  simp only [BackupStat.mean]
  norm_num

theorem favorableCompleteS30D1I1 : indexScore (7/5) (controlPenalty savedCref uniformQuoteError unitRoleUnused .complete) favorableCompleteS30Before [.query 1] (.hydeRetriever 0) = treeIndex ((0/1)/6) (7/5) 0 22 6 := by
  have hs : replayBackup favorableCompleteS30Before emptyStatistics ([.query 1]++[.hydeRetriever 0]) = ⟨6,(0/1)⟩ := by
    rw [replayBackup_empty_closed_form]
    simp +decide [backedEvents,favorableCompleteS30Before,favorableCompleteProposal,favorableCompleteEvent1,favorableCompleteEvent2,favorableCompleteEvent3,favorableCompleteEvent4,favorableCompleteEvent5,favorableCompleteEvent6,favorableCompleteEvent7,favorableCompleteEvent8,favorableCompleteEvent9,favorableCompleteEvent10,favorableCompleteEvent11,favorableCompleteEvent12,favorableCompleteEvent13,favorableCompleteEvent14,favorableCompleteEvent15,favorableCompleteEvent16,favorableCompleteEvent17,favorableCompleteEvent18,favorableCompleteEvent19,favorableCompleteEvent20,favorableCompleteEvent21,favorableCompleteEvent22,favorableCompleteEvent23,favorableCompleteEvent24,favorableCompleteEvent25,favorableCompleteEvent26,favorableCompleteEvent27,favorableCompleteEvent28,favorableCompleteEvent29,taskReward]
    <;> norm_num
  have hp : rawVisits favorableCompleteS30Before [.query 1] = 22 := by decide
  have hn : rawVisits favorableCompleteS30Before ([.query 1]++[.hydeRetriever 0]) = 6 := by decide
  have hz : (controlPenalty savedCref uniformQuoteError unitRoleUnused .complete) favorableCompleteS30Before [.query 1] (.hydeRetriever 0) = 0 := by
    apply control_penalty_empty_of_prior_terminal .complete savedCref uniformQuoteError favorableCompleteS30Before [.query 1] (.hydeRetriever 0) 1 (by decide)
    · decide
    · decide
  unfold indexScore
  rw [hs,hp,hn,hz]
  simp only [BackupStat.mean]
  norm_num

theorem favorableCompleteS30D1I2 : indexScore (7/5) (controlPenalty savedCref uniformQuoteError unitRoleUnused .complete) favorableCompleteS30Before [.query 1] (.hydeRetriever 2) = treeIndex ((0/1)/6) (7/5) 0 22 6 := by
  have hs : replayBackup favorableCompleteS30Before emptyStatistics ([.query 1]++[.hydeRetriever 2]) = ⟨6,(0/1)⟩ := by
    rw [replayBackup_empty_closed_form]
    simp +decide [backedEvents,favorableCompleteS30Before,favorableCompleteProposal,favorableCompleteEvent1,favorableCompleteEvent2,favorableCompleteEvent3,favorableCompleteEvent4,favorableCompleteEvent5,favorableCompleteEvent6,favorableCompleteEvent7,favorableCompleteEvent8,favorableCompleteEvent9,favorableCompleteEvent10,favorableCompleteEvent11,favorableCompleteEvent12,favorableCompleteEvent13,favorableCompleteEvent14,favorableCompleteEvent15,favorableCompleteEvent16,favorableCompleteEvent17,favorableCompleteEvent18,favorableCompleteEvent19,favorableCompleteEvent20,favorableCompleteEvent21,favorableCompleteEvent22,favorableCompleteEvent23,favorableCompleteEvent24,favorableCompleteEvent25,favorableCompleteEvent26,favorableCompleteEvent27,favorableCompleteEvent28,favorableCompleteEvent29,taskReward]
    <;> norm_num
  have hp : rawVisits favorableCompleteS30Before [.query 1] = 22 := by decide
  have hn : rawVisits favorableCompleteS30Before ([.query 1]++[.hydeRetriever 2]) = 6 := by decide
  have hz : (controlPenalty savedCref uniformQuoteError unitRoleUnused .complete) favorableCompleteS30Before [.query 1] (.hydeRetriever 2) = 0 := by
    apply control_penalty_empty_of_prior_terminal .complete savedCref uniformQuoteError favorableCompleteS30Before [.query 1] (.hydeRetriever 2) 10 (by decide)
    · decide
    · decide
  unfold indexScore
  rw [hs,hp,hn,hz]
  simp only [BackupStat.mean]
  norm_num

theorem favorableCompleteS30D1Cmp0 : indexScore (7/5) (controlPenalty savedCref uniformQuoteError unitRoleUnused .complete) favorableCompleteS30Before [.query 1] (.hydeRetriever 1) < indexScore (7/5) (controlPenalty savedCref uniformQuoteError unitRoleUnused .complete) favorableCompleteS30Before [.query 1] (.hydeRetriever 0) := by
  rw [favorableCompleteS30D1I0,favorableCompleteS30D1I1]
  have h := index_strict_order_from_intervals ((0/1)/6) ((3/2)/9) 0 0 (10120579/10000000) (41317101/50000000)
    (treeBonus (7/5) 22 6) (treeBonus (7/5) 22 9)
    (trajectory_bonus_22_6).1 (trajectory_bonus_22_9).2 (by norm_num)
  simpa only [treeIndex,sub_zero] using h

theorem favorableCompleteS30D1Cmp2 : indexScore (7/5) (controlPenalty savedCref uniformQuoteError unitRoleUnused .complete) favorableCompleteS30Before [.query 1] (.hydeRetriever 2) ≤ indexScore (7/5) (controlPenalty savedCref uniformQuoteError unitRoleUnused .complete) favorableCompleteS30Before [.query 1] (.hydeRetriever 0) := by
  rw [favorableCompleteS30D1I2,favorableCompleteS30D1I1]

theorem favorableCompleteS30Choice1 : nativeFirstChoice (indexScore (7/5) (controlPenalty savedCref uniformQuoteError unitRoleUnused .complete) favorableCompleteS30Before [.query 1]) favorableCompleteS30Before [.query 1] = .hydeRetriever 0 := by
  apply visited_choice_from_ordered_certificate _ _ [.query 1] [.hydeRetriever 1] [.hydeRetriever 2] (.hydeRetriever 0) (by decide)
  · intro a ha
    have ho : orderedLegalAvailable [.query 1] = [.hydeRetriever 1,.hydeRetriever 0,.hydeRetriever 2] := by decide
    rw [ho] at ha
    simp only [List.mem_cons,List.not_mem_nil,or_false] at ha
    rcases ha with rfl | rfl | rfl <;> decide
  · intro a ha
    simp only [List.mem_cons,List.not_mem_nil,or_false] at ha
    rcases ha with rfl
    · exact favorableCompleteS30D1Cmp0
  · intro a ha
    simp only [List.mem_cons,List.not_mem_nil,or_false] at ha
    rcases ha with rfl
    · exact favorableCompleteS30D1Cmp2

theorem favorableCompleteS30D2I0 : indexScore (7/5) (controlPenalty savedCref uniformQuoteError unitRoleUnused .complete) favorableCompleteS30Before [.query 1,.hydeRetriever 0] (.selection 1) = treeIndex ((0/1)/2) (7/5) 0 6 2 := by
  have hs : replayBackup favorableCompleteS30Before emptyStatistics ([.query 1,.hydeRetriever 0]++[.selection 1]) = ⟨2,(0/1)⟩ := by
    rw [replayBackup_empty_closed_form]
    simp +decide [backedEvents,favorableCompleteS30Before,favorableCompleteProposal,favorableCompleteEvent1,favorableCompleteEvent2,favorableCompleteEvent3,favorableCompleteEvent4,favorableCompleteEvent5,favorableCompleteEvent6,favorableCompleteEvent7,favorableCompleteEvent8,favorableCompleteEvent9,favorableCompleteEvent10,favorableCompleteEvent11,favorableCompleteEvent12,favorableCompleteEvent13,favorableCompleteEvent14,favorableCompleteEvent15,favorableCompleteEvent16,favorableCompleteEvent17,favorableCompleteEvent18,favorableCompleteEvent19,favorableCompleteEvent20,favorableCompleteEvent21,favorableCompleteEvent22,favorableCompleteEvent23,favorableCompleteEvent24,favorableCompleteEvent25,favorableCompleteEvent26,favorableCompleteEvent27,favorableCompleteEvent28,favorableCompleteEvent29,taskReward]
    <;> norm_num
  have hp : rawVisits favorableCompleteS30Before [.query 1,.hydeRetriever 0] = 6 := by decide
  have hn : rawVisits favorableCompleteS30Before ([.query 1,.hydeRetriever 0]++[.selection 1]) = 2 := by decide
  have hz : (controlPenalty savedCref uniformQuoteError unitRoleUnused .complete) favorableCompleteS30Before [.query 1,.hydeRetriever 0] (.selection 1) = 0 := by
    apply control_penalty_empty_of_prior_terminal .complete savedCref uniformQuoteError favorableCompleteS30Before [.query 1,.hydeRetriever 0] (.selection 1) 16 (by decide)
    · decide
    · decide
  unfold indexScore
  rw [hs,hp,hn,hz]
  simp only [BackupStat.mean]
  norm_num

theorem favorableCompleteS30D2I1 : indexScore (7/5) (controlPenalty savedCref uniformQuoteError unitRoleUnused .complete) favorableCompleteS30Before [.query 1,.hydeRetriever 0] (.selection 2) = treeIndex ((0/1)/1) (7/5) 0 6 1 := by
  have hs : replayBackup favorableCompleteS30Before emptyStatistics ([.query 1,.hydeRetriever 0]++[.selection 2]) = ⟨1,(0/1)⟩ := by
    rw [replayBackup_empty_closed_form]
    simp +decide [backedEvents,favorableCompleteS30Before,favorableCompleteProposal,favorableCompleteEvent1,favorableCompleteEvent2,favorableCompleteEvent3,favorableCompleteEvent4,favorableCompleteEvent5,favorableCompleteEvent6,favorableCompleteEvent7,favorableCompleteEvent8,favorableCompleteEvent9,favorableCompleteEvent10,favorableCompleteEvent11,favorableCompleteEvent12,favorableCompleteEvent13,favorableCompleteEvent14,favorableCompleteEvent15,favorableCompleteEvent16,favorableCompleteEvent17,favorableCompleteEvent18,favorableCompleteEvent19,favorableCompleteEvent20,favorableCompleteEvent21,favorableCompleteEvent22,favorableCompleteEvent23,favorableCompleteEvent24,favorableCompleteEvent25,favorableCompleteEvent26,favorableCompleteEvent27,favorableCompleteEvent28,favorableCompleteEvent29,taskReward]
    <;> norm_num
  have hp : rawVisits favorableCompleteS30Before [.query 1,.hydeRetriever 0] = 6 := by decide
  have hn : rawVisits favorableCompleteS30Before ([.query 1,.hydeRetriever 0]++[.selection 2]) = 1 := by decide
  have hz : (controlPenalty savedCref uniformQuoteError unitRoleUnused .complete) favorableCompleteS30Before [.query 1,.hydeRetriever 0] (.selection 2) = 0 := by
    apply control_penalty_empty_of_prior_terminal .complete savedCref uniformQuoteError favorableCompleteS30Before [.query 1,.hydeRetriever 0] (.selection 2) 19 (by decide)
    · decide
    · decide
  unfold indexScore
  rw [hs,hp,hn,hz]
  simp only [BackupStat.mean]
  norm_num

theorem favorableCompleteS30D2I2 : indexScore (7/5) (controlPenalty savedCref uniformQuoteError unitRoleUnused .complete) favorableCompleteS30Before [.query 1,.hydeRetriever 0] (.selection 3) = treeIndex ((0/1)/1) (7/5) 0 6 1 := by
  have hs : replayBackup favorableCompleteS30Before emptyStatistics ([.query 1,.hydeRetriever 0]++[.selection 3]) = ⟨1,(0/1)⟩ := by
    rw [replayBackup_empty_closed_form]
    simp +decide [backedEvents,favorableCompleteS30Before,favorableCompleteProposal,favorableCompleteEvent1,favorableCompleteEvent2,favorableCompleteEvent3,favorableCompleteEvent4,favorableCompleteEvent5,favorableCompleteEvent6,favorableCompleteEvent7,favorableCompleteEvent8,favorableCompleteEvent9,favorableCompleteEvent10,favorableCompleteEvent11,favorableCompleteEvent12,favorableCompleteEvent13,favorableCompleteEvent14,favorableCompleteEvent15,favorableCompleteEvent16,favorableCompleteEvent17,favorableCompleteEvent18,favorableCompleteEvent19,favorableCompleteEvent20,favorableCompleteEvent21,favorableCompleteEvent22,favorableCompleteEvent23,favorableCompleteEvent24,favorableCompleteEvent25,favorableCompleteEvent26,favorableCompleteEvent27,favorableCompleteEvent28,favorableCompleteEvent29,taskReward]
    <;> norm_num
  have hp : rawVisits favorableCompleteS30Before [.query 1,.hydeRetriever 0] = 6 := by decide
  have hn : rawVisits favorableCompleteS30Before ([.query 1,.hydeRetriever 0]++[.selection 3]) = 1 := by decide
  have hz : (controlPenalty savedCref uniformQuoteError unitRoleUnused .complete) favorableCompleteS30Before [.query 1,.hydeRetriever 0] (.selection 3) = 0 := by
    apply control_penalty_empty_of_prior_terminal .complete savedCref uniformQuoteError favorableCompleteS30Before [.query 1,.hydeRetriever 0] (.selection 3) 23 (by decide)
    · decide
    · decide
  unfold indexScore
  rw [hs,hp,hn,hz]
  simp only [BackupStat.mean]
  norm_num

theorem favorableCompleteS30D2I3 : indexScore (7/5) (controlPenalty savedCref uniformQuoteError unitRoleUnused .complete) favorableCompleteS30Before [.query 1,.hydeRetriever 0] (.selection 0) = treeIndex ((0/1)/1) (7/5) 0 6 1 := by
  have hs : replayBackup favorableCompleteS30Before emptyStatistics ([.query 1,.hydeRetriever 0]++[.selection 0]) = ⟨1,(0/1)⟩ := by
    rw [replayBackup_empty_closed_form]
    simp +decide [backedEvents,favorableCompleteS30Before,favorableCompleteProposal,favorableCompleteEvent1,favorableCompleteEvent2,favorableCompleteEvent3,favorableCompleteEvent4,favorableCompleteEvent5,favorableCompleteEvent6,favorableCompleteEvent7,favorableCompleteEvent8,favorableCompleteEvent9,favorableCompleteEvent10,favorableCompleteEvent11,favorableCompleteEvent12,favorableCompleteEvent13,favorableCompleteEvent14,favorableCompleteEvent15,favorableCompleteEvent16,favorableCompleteEvent17,favorableCompleteEvent18,favorableCompleteEvent19,favorableCompleteEvent20,favorableCompleteEvent21,favorableCompleteEvent22,favorableCompleteEvent23,favorableCompleteEvent24,favorableCompleteEvent25,favorableCompleteEvent26,favorableCompleteEvent27,favorableCompleteEvent28,favorableCompleteEvent29,taskReward]
    <;> norm_num
  have hp : rawVisits favorableCompleteS30Before [.query 1,.hydeRetriever 0] = 6 := by decide
  have hn : rawVisits favorableCompleteS30Before ([.query 1,.hydeRetriever 0]++[.selection 0]) = 1 := by decide
  have hz : (controlPenalty savedCref uniformQuoteError unitRoleUnused .complete) favorableCompleteS30Before [.query 1,.hydeRetriever 0] (.selection 0) = 0 := by
    apply control_penalty_empty_of_prior_terminal .complete savedCref uniformQuoteError favorableCompleteS30Before [.query 1,.hydeRetriever 0] (.selection 0) 1 (by decide)
    · decide
    · decide
  unfold indexScore
  rw [hs,hp,hn,hz]
  simp only [BackupStat.mean]
  norm_num

theorem favorableCompleteS30D2Cmp0 : indexScore (7/5) (controlPenalty savedCref uniformQuoteError unitRoleUnused .complete) favorableCompleteS30Before [.query 1,.hydeRetriever 0] (.selection 1) < indexScore (7/5) (controlPenalty savedCref uniformQuoteError unitRoleUnused .complete) favorableCompleteS30Before [.query 1,.hydeRetriever 0] (.selection 2) := by
  rw [favorableCompleteS30D2I0,favorableCompleteS30D2I1]
  have h := index_strict_order_from_intervals ((0/1)/1) ((0/1)/2) 0 0 (24411779/12500000) (69046943/50000000)
    (treeBonus (7/5) 6 1) (treeBonus (7/5) 6 2)
    (trajectory_bonus_6_1).1 (trajectory_bonus_6_2).2 (by norm_num)
  simpa only [treeIndex,sub_zero] using h

theorem favorableCompleteS30D2Cmp2 : indexScore (7/5) (controlPenalty savedCref uniformQuoteError unitRoleUnused .complete) favorableCompleteS30Before [.query 1,.hydeRetriever 0] (.selection 3) ≤ indexScore (7/5) (controlPenalty savedCref uniformQuoteError unitRoleUnused .complete) favorableCompleteS30Before [.query 1,.hydeRetriever 0] (.selection 2) := by
  rw [favorableCompleteS30D2I2,favorableCompleteS30D2I1]

theorem favorableCompleteS30D2Cmp3 : indexScore (7/5) (controlPenalty savedCref uniformQuoteError unitRoleUnused .complete) favorableCompleteS30Before [.query 1,.hydeRetriever 0] (.selection 0) ≤ indexScore (7/5) (controlPenalty savedCref uniformQuoteError unitRoleUnused .complete) favorableCompleteS30Before [.query 1,.hydeRetriever 0] (.selection 2) := by
  rw [favorableCompleteS30D2I3,favorableCompleteS30D2I1]

theorem favorableCompleteS30Choice2 : nativeFirstChoice (indexScore (7/5) (controlPenalty savedCref uniformQuoteError unitRoleUnused .complete) favorableCompleteS30Before [.query 1,.hydeRetriever 0]) favorableCompleteS30Before [.query 1,.hydeRetriever 0] = .selection 2 := by
  apply visited_choice_from_ordered_certificate _ _ [.query 1,.hydeRetriever 0] [.selection 1] [.selection 3,.selection 0] (.selection 2) (by decide)
  · intro a ha
    have ho : orderedLegalAvailable [.query 1,.hydeRetriever 0] = [.selection 1,.selection 2,.selection 3,.selection 0] := by decide
    rw [ho] at ha
    simp only [List.mem_cons,List.not_mem_nil,or_false] at ha
    rcases ha with rfl | rfl | rfl | rfl <;> decide
  · intro a ha
    simp only [List.mem_cons,List.not_mem_nil,or_false] at ha
    rcases ha with rfl
    · exact favorableCompleteS30D2Cmp0
  · intro a ha
    simp only [List.mem_cons,List.not_mem_nil,or_false] at ha
    rcases ha with rfl | rfl
    · exact favorableCompleteS30D2Cmp2
    · exact favorableCompleteS30D2Cmp3

theorem favorableCompleteS30ActualEvent : nativeEvent budgetTape (7/5) (controlPenalty savedCref uniformQuoteError unitRoleUnused .complete)
    (taskReward false (2/5) (1/2)) favorableCompleteS30Before = favorableCompleteEvent30 := by
  have hs0 := native_select_existing_step budgetTape (7/5) (controlPenalty savedCref uniformQuoteError unitRoleUnused .complete) favorableCompleteS30Before 8 [] (.query 1)
    (by decide) (by decide) favorableCompleteS30Choice0
  have hs1 := native_select_existing_step budgetTape (7/5) (controlPenalty savedCref uniformQuoteError unitRoleUnused .complete) favorableCompleteS30Before 7 [.query 1] (.hydeRetriever 0)
    (by decide) (by decide) favorableCompleteS30Choice1
  have hs2 := native_select_existing_step budgetTape (7/5) (controlPenalty savedCref uniformQuoteError unitRoleUnused .complete) favorableCompleteS30Before 6 [.query 1,.hydeRetriever 0] (.selection 2)
    (by decide) (by decide) favorableCompleteS30Choice2
  have hnew := native_select_new_step budgetTape (7/5) (controlPenalty savedCref uniformQuoteError unitRoleUnused .complete) favorableCompleteS30Before 5 [.query 1,.hydeRetriever 0,.selection 2]
    [.width 3,.width 0,.width 1,.width 2] (.width 0) (by decide) (by decide) (by decide) (by decide)
  have hs : nativeSelect budgetTape (7/5) (controlPenalty savedCref uniformQuoteError unitRoleUnused .complete) favorableCompleteS30Before 9 [] = [.query 1,.hydeRetriever 0,.selection 2,.width 0] := by
    rw [hs0]
    change nativeSelect budgetTape (7/5) (controlPenalty savedCref uniformQuoteError unitRoleUnused .complete) favorableCompleteS30Before 8 [.query 1] = _
    rw [hs1]
    change nativeSelect budgetTape (7/5) (controlPenalty savedCref uniformQuoteError unitRoleUnused .complete) favorableCompleteS30Before 7 [.query 1,.hydeRetriever 0] = _
    rw [hs2]
    change nativeSelect budgetTape (7/5) (controlPenalty savedCref uniformQuoteError unitRoleUnused .complete) favorableCompleteS30Before 6 [.query 1,.hydeRetriever 0,.selection 2] = _
    rw [hnew] <;> rfl
  have hr : repairedRollout budgetTape favorableCompleteS30Before 9 [.query 1,.hydeRetriever 0,.selection 2,.width 0] = [.query 1,.hydeRetriever 0,.selection 2,.width 0,.stop,.reranker 0,.topm 0,.context 0,.answer 0] := by decide
  simp only [nativeEvent,hs,hr]
  rfl

def favorableCompleteS31Before := favorableCompleteProposal.take 30

theorem favorableCompleteS31Choice0 : nativeFirstChoice (indexScore (7/5) (controlPenalty savedCref uniformQuoteError unitRoleUnused .complete) favorableCompleteS31Before []) favorableCompleteS31Before [] = .query 1 := by
  apply complete_root_from_physical_gap favorableCompleteS31Before (favorableComplete_prefix_rewards 30) (by decide)
  · intro q; fin_cases q <;> decide
  · decide
  · intro q hq
    exact AgentUCTNextExact.favorable_complete_normal_root_physical_quote_exact 30 (by omega) q hq

theorem favorableCompleteS31D1I0 : indexScore (7/5) (controlPenalty savedCref uniformQuoteError unitRoleUnused .complete) favorableCompleteS31Before [.query 1] (.hydeRetriever 1) = treeIndex ((3/2)/9) (7/5) 0 23 9 := by
  have hs : replayBackup favorableCompleteS31Before emptyStatistics ([.query 1]++[.hydeRetriever 1]) = ⟨9,(3/2)⟩ := by
    rw [replayBackup_empty_closed_form]
    simp +decide [backedEvents,favorableCompleteS31Before,favorableCompleteProposal,favorableCompleteEvent1,favorableCompleteEvent2,favorableCompleteEvent3,favorableCompleteEvent4,favorableCompleteEvent5,favorableCompleteEvent6,favorableCompleteEvent7,favorableCompleteEvent8,favorableCompleteEvent9,favorableCompleteEvent10,favorableCompleteEvent11,favorableCompleteEvent12,favorableCompleteEvent13,favorableCompleteEvent14,favorableCompleteEvent15,favorableCompleteEvent16,favorableCompleteEvent17,favorableCompleteEvent18,favorableCompleteEvent19,favorableCompleteEvent20,favorableCompleteEvent21,favorableCompleteEvent22,favorableCompleteEvent23,favorableCompleteEvent24,favorableCompleteEvent25,favorableCompleteEvent26,favorableCompleteEvent27,favorableCompleteEvent28,favorableCompleteEvent29,favorableCompleteEvent30,taskReward]
    <;> norm_num
  have hp : rawVisits favorableCompleteS31Before [.query 1] = 23 := by decide
  have hn : rawVisits favorableCompleteS31Before ([.query 1]++[.hydeRetriever 1]) = 9 := by decide
  have hz : (controlPenalty savedCref uniformQuoteError unitRoleUnused .complete) favorableCompleteS31Before [.query 1] (.hydeRetriever 1) = 0 := by
    apply control_penalty_empty_of_prior_terminal .complete savedCref uniformQuoteError favorableCompleteS31Before [.query 1] (.hydeRetriever 1) 8 (by decide)
    · decide
    · decide
  unfold indexScore
  rw [hs,hp,hn,hz]
  simp only [BackupStat.mean]
  norm_num

theorem favorableCompleteS31D1I1 : indexScore (7/5) (controlPenalty savedCref uniformQuoteError unitRoleUnused .complete) favorableCompleteS31Before [.query 1] (.hydeRetriever 0) = treeIndex ((0/1)/7) (7/5) 0 23 7 := by
  have hs : replayBackup favorableCompleteS31Before emptyStatistics ([.query 1]++[.hydeRetriever 0]) = ⟨7,(0/1)⟩ := by
    rw [replayBackup_empty_closed_form]
    simp +decide [backedEvents,favorableCompleteS31Before,favorableCompleteProposal,favorableCompleteEvent1,favorableCompleteEvent2,favorableCompleteEvent3,favorableCompleteEvent4,favorableCompleteEvent5,favorableCompleteEvent6,favorableCompleteEvent7,favorableCompleteEvent8,favorableCompleteEvent9,favorableCompleteEvent10,favorableCompleteEvent11,favorableCompleteEvent12,favorableCompleteEvent13,favorableCompleteEvent14,favorableCompleteEvent15,favorableCompleteEvent16,favorableCompleteEvent17,favorableCompleteEvent18,favorableCompleteEvent19,favorableCompleteEvent20,favorableCompleteEvent21,favorableCompleteEvent22,favorableCompleteEvent23,favorableCompleteEvent24,favorableCompleteEvent25,favorableCompleteEvent26,favorableCompleteEvent27,favorableCompleteEvent28,favorableCompleteEvent29,favorableCompleteEvent30,taskReward]
    <;> norm_num
  have hp : rawVisits favorableCompleteS31Before [.query 1] = 23 := by decide
  have hn : rawVisits favorableCompleteS31Before ([.query 1]++[.hydeRetriever 0]) = 7 := by decide
  have hz : (controlPenalty savedCref uniformQuoteError unitRoleUnused .complete) favorableCompleteS31Before [.query 1] (.hydeRetriever 0) = 0 := by
    apply control_penalty_empty_of_prior_terminal .complete savedCref uniformQuoteError favorableCompleteS31Before [.query 1] (.hydeRetriever 0) 1 (by decide)
    · decide
    · decide
  unfold indexScore
  rw [hs,hp,hn,hz]
  simp only [BackupStat.mean]
  norm_num

theorem favorableCompleteS31D1I2 : indexScore (7/5) (controlPenalty savedCref uniformQuoteError unitRoleUnused .complete) favorableCompleteS31Before [.query 1] (.hydeRetriever 2) = treeIndex ((0/1)/6) (7/5) 0 23 6 := by
  have hs : replayBackup favorableCompleteS31Before emptyStatistics ([.query 1]++[.hydeRetriever 2]) = ⟨6,(0/1)⟩ := by
    rw [replayBackup_empty_closed_form]
    simp +decide [backedEvents,favorableCompleteS31Before,favorableCompleteProposal,favorableCompleteEvent1,favorableCompleteEvent2,favorableCompleteEvent3,favorableCompleteEvent4,favorableCompleteEvent5,favorableCompleteEvent6,favorableCompleteEvent7,favorableCompleteEvent8,favorableCompleteEvent9,favorableCompleteEvent10,favorableCompleteEvent11,favorableCompleteEvent12,favorableCompleteEvent13,favorableCompleteEvent14,favorableCompleteEvent15,favorableCompleteEvent16,favorableCompleteEvent17,favorableCompleteEvent18,favorableCompleteEvent19,favorableCompleteEvent20,favorableCompleteEvent21,favorableCompleteEvent22,favorableCompleteEvent23,favorableCompleteEvent24,favorableCompleteEvent25,favorableCompleteEvent26,favorableCompleteEvent27,favorableCompleteEvent28,favorableCompleteEvent29,favorableCompleteEvent30,taskReward]
    <;> norm_num
  have hp : rawVisits favorableCompleteS31Before [.query 1] = 23 := by decide
  have hn : rawVisits favorableCompleteS31Before ([.query 1]++[.hydeRetriever 2]) = 6 := by decide
  have hz : (controlPenalty savedCref uniformQuoteError unitRoleUnused .complete) favorableCompleteS31Before [.query 1] (.hydeRetriever 2) = 0 := by
    apply control_penalty_empty_of_prior_terminal .complete savedCref uniformQuoteError favorableCompleteS31Before [.query 1] (.hydeRetriever 2) 10 (by decide)
    · decide
    · decide
  unfold indexScore
  rw [hs,hp,hn,hz]
  simp only [BackupStat.mean]
  norm_num

theorem favorableCompleteS31D1Cmp0 : indexScore (7/5) (controlPenalty savedCref uniformQuoteError unitRoleUnused .complete) favorableCompleteS31Before [.query 1] (.hydeRetriever 1) < indexScore (7/5) (controlPenalty savedCref uniformQuoteError unitRoleUnused .complete) favorableCompleteS31Before [.query 1] (.hydeRetriever 2) := by
  rw [favorableCompleteS31D1I0,favorableCompleteS31D1I2]
  have h := index_strict_order_from_intervals ((0/1)/6) ((3/2)/9) 0 0 (50945167/50000000) (20798281/25000000)
    (treeBonus (7/5) 23 6) (treeBonus (7/5) 23 9)
    (trajectory_bonus_23_6).1 (trajectory_bonus_23_9).2 (by norm_num)
  simpa only [treeIndex,sub_zero] using h

theorem favorableCompleteS31D1Cmp1 : indexScore (7/5) (controlPenalty savedCref uniformQuoteError unitRoleUnused .complete) favorableCompleteS31Before [.query 1] (.hydeRetriever 0) < indexScore (7/5) (controlPenalty savedCref uniformQuoteError unitRoleUnused .complete) favorableCompleteS31Before [.query 1] (.hydeRetriever 2) := by
  rw [favorableCompleteS31D1I1,favorableCompleteS31D1I2]
  have h := index_strict_order_from_intervals ((0/1)/6) ((0/1)/7) 0 0 (50945167/50000000) (4716607/5000000)
    (treeBonus (7/5) 23 6) (treeBonus (7/5) 23 7)
    (trajectory_bonus_23_6).1 (trajectory_bonus_23_7).2 (by norm_num)
  simpa only [treeIndex,sub_zero] using h

theorem favorableCompleteS31Choice1 : nativeFirstChoice (indexScore (7/5) (controlPenalty savedCref uniformQuoteError unitRoleUnused .complete) favorableCompleteS31Before [.query 1]) favorableCompleteS31Before [.query 1] = .hydeRetriever 2 := by
  apply visited_choice_from_ordered_certificate _ _ [.query 1] [.hydeRetriever 1,.hydeRetriever 0] [] (.hydeRetriever 2) (by decide)
  · intro a ha
    have ho : orderedLegalAvailable [.query 1] = [.hydeRetriever 1,.hydeRetriever 0,.hydeRetriever 2] := by decide
    rw [ho] at ha
    simp only [List.mem_cons,List.not_mem_nil,or_false] at ha
    rcases ha with rfl | rfl | rfl <;> decide
  · intro a ha
    simp only [List.mem_cons,List.not_mem_nil,or_false] at ha
    rcases ha with rfl | rfl
    · exact favorableCompleteS31D1Cmp0
    · exact favorableCompleteS31D1Cmp1
  · simp

theorem favorableCompleteS31D2I0 : indexScore (7/5) (controlPenalty savedCref uniformQuoteError unitRoleUnused .complete) favorableCompleteS31Before [.query 1,.hydeRetriever 2] (.selection 1) = treeIndex ((0/1)/2) (7/5) 0 6 2 := by
  have hs : replayBackup favorableCompleteS31Before emptyStatistics ([.query 1,.hydeRetriever 2]++[.selection 1]) = ⟨2,(0/1)⟩ := by
    rw [replayBackup_empty_closed_form]
    simp +decide [backedEvents,favorableCompleteS31Before,favorableCompleteProposal,favorableCompleteEvent1,favorableCompleteEvent2,favorableCompleteEvent3,favorableCompleteEvent4,favorableCompleteEvent5,favorableCompleteEvent6,favorableCompleteEvent7,favorableCompleteEvent8,favorableCompleteEvent9,favorableCompleteEvent10,favorableCompleteEvent11,favorableCompleteEvent12,favorableCompleteEvent13,favorableCompleteEvent14,favorableCompleteEvent15,favorableCompleteEvent16,favorableCompleteEvent17,favorableCompleteEvent18,favorableCompleteEvent19,favorableCompleteEvent20,favorableCompleteEvent21,favorableCompleteEvent22,favorableCompleteEvent23,favorableCompleteEvent24,favorableCompleteEvent25,favorableCompleteEvent26,favorableCompleteEvent27,favorableCompleteEvent28,favorableCompleteEvent29,favorableCompleteEvent30,taskReward]
    <;> norm_num
  have hp : rawVisits favorableCompleteS31Before [.query 1,.hydeRetriever 2] = 6 := by decide
  have hn : rawVisits favorableCompleteS31Before ([.query 1,.hydeRetriever 2]++[.selection 1]) = 2 := by decide
  have hz : (controlPenalty savedCref uniformQuoteError unitRoleUnused .complete) favorableCompleteS31Before [.query 1,.hydeRetriever 2] (.selection 1) = 0 := by
    apply control_penalty_empty_of_prior_terminal .complete savedCref uniformQuoteError favorableCompleteS31Before [.query 1,.hydeRetriever 2] (.selection 1) 17 (by decide)
    · decide
    · decide
  unfold indexScore
  rw [hs,hp,hn,hz]
  simp only [BackupStat.mean]
  norm_num

theorem favorableCompleteS31D2I1 : indexScore (7/5) (controlPenalty savedCref uniformQuoteError unitRoleUnused .complete) favorableCompleteS31Before [.query 1,.hydeRetriever 2] (.selection 2) = treeIndex ((0/1)/1) (7/5) 0 6 1 := by
  have hs : replayBackup favorableCompleteS31Before emptyStatistics ([.query 1,.hydeRetriever 2]++[.selection 2]) = ⟨1,(0/1)⟩ := by
    rw [replayBackup_empty_closed_form]
    simp +decide [backedEvents,favorableCompleteS31Before,favorableCompleteProposal,favorableCompleteEvent1,favorableCompleteEvent2,favorableCompleteEvent3,favorableCompleteEvent4,favorableCompleteEvent5,favorableCompleteEvent6,favorableCompleteEvent7,favorableCompleteEvent8,favorableCompleteEvent9,favorableCompleteEvent10,favorableCompleteEvent11,favorableCompleteEvent12,favorableCompleteEvent13,favorableCompleteEvent14,favorableCompleteEvent15,favorableCompleteEvent16,favorableCompleteEvent17,favorableCompleteEvent18,favorableCompleteEvent19,favorableCompleteEvent20,favorableCompleteEvent21,favorableCompleteEvent22,favorableCompleteEvent23,favorableCompleteEvent24,favorableCompleteEvent25,favorableCompleteEvent26,favorableCompleteEvent27,favorableCompleteEvent28,favorableCompleteEvent29,favorableCompleteEvent30,taskReward]
    <;> norm_num
  have hp : rawVisits favorableCompleteS31Before [.query 1,.hydeRetriever 2] = 6 := by decide
  have hn : rawVisits favorableCompleteS31Before ([.query 1,.hydeRetriever 2]++[.selection 2]) = 1 := by decide
  have hz : (controlPenalty savedCref uniformQuoteError unitRoleUnused .complete) favorableCompleteS31Before [.query 1,.hydeRetriever 2] (.selection 2) = 0 := by
    apply control_penalty_empty_of_prior_terminal .complete savedCref uniformQuoteError favorableCompleteS31Before [.query 1,.hydeRetriever 2] (.selection 2) 20 (by decide)
    · decide
    · decide
  unfold indexScore
  rw [hs,hp,hn,hz]
  simp only [BackupStat.mean]
  norm_num

theorem favorableCompleteS31D2I2 : indexScore (7/5) (controlPenalty savedCref uniformQuoteError unitRoleUnused .complete) favorableCompleteS31Before [.query 1,.hydeRetriever 2] (.selection 3) = treeIndex ((0/1)/1) (7/5) 0 6 1 := by
  have hs : replayBackup favorableCompleteS31Before emptyStatistics ([.query 1,.hydeRetriever 2]++[.selection 3]) = ⟨1,(0/1)⟩ := by
    rw [replayBackup_empty_closed_form]
    simp +decide [backedEvents,favorableCompleteS31Before,favorableCompleteProposal,favorableCompleteEvent1,favorableCompleteEvent2,favorableCompleteEvent3,favorableCompleteEvent4,favorableCompleteEvent5,favorableCompleteEvent6,favorableCompleteEvent7,favorableCompleteEvent8,favorableCompleteEvent9,favorableCompleteEvent10,favorableCompleteEvent11,favorableCompleteEvent12,favorableCompleteEvent13,favorableCompleteEvent14,favorableCompleteEvent15,favorableCompleteEvent16,favorableCompleteEvent17,favorableCompleteEvent18,favorableCompleteEvent19,favorableCompleteEvent20,favorableCompleteEvent21,favorableCompleteEvent22,favorableCompleteEvent23,favorableCompleteEvent24,favorableCompleteEvent25,favorableCompleteEvent26,favorableCompleteEvent27,favorableCompleteEvent28,favorableCompleteEvent29,favorableCompleteEvent30,taskReward]
    <;> norm_num
  have hp : rawVisits favorableCompleteS31Before [.query 1,.hydeRetriever 2] = 6 := by decide
  have hn : rawVisits favorableCompleteS31Before ([.query 1,.hydeRetriever 2]++[.selection 3]) = 1 := by decide
  have hz : (controlPenalty savedCref uniformQuoteError unitRoleUnused .complete) favorableCompleteS31Before [.query 1,.hydeRetriever 2] (.selection 3) = 0 := by
    apply control_penalty_empty_of_prior_terminal .complete savedCref uniformQuoteError favorableCompleteS31Before [.query 1,.hydeRetriever 2] (.selection 3) 24 (by decide)
    · decide
    · decide
  unfold indexScore
  rw [hs,hp,hn,hz]
  simp only [BackupStat.mean]
  norm_num

theorem favorableCompleteS31D2I3 : indexScore (7/5) (controlPenalty savedCref uniformQuoteError unitRoleUnused .complete) favorableCompleteS31Before [.query 1,.hydeRetriever 2] (.selection 0) = treeIndex ((0/1)/1) (7/5) 0 6 1 := by
  have hs : replayBackup favorableCompleteS31Before emptyStatistics ([.query 1,.hydeRetriever 2]++[.selection 0]) = ⟨1,(0/1)⟩ := by
    rw [replayBackup_empty_closed_form]
    simp +decide [backedEvents,favorableCompleteS31Before,favorableCompleteProposal,favorableCompleteEvent1,favorableCompleteEvent2,favorableCompleteEvent3,favorableCompleteEvent4,favorableCompleteEvent5,favorableCompleteEvent6,favorableCompleteEvent7,favorableCompleteEvent8,favorableCompleteEvent9,favorableCompleteEvent10,favorableCompleteEvent11,favorableCompleteEvent12,favorableCompleteEvent13,favorableCompleteEvent14,favorableCompleteEvent15,favorableCompleteEvent16,favorableCompleteEvent17,favorableCompleteEvent18,favorableCompleteEvent19,favorableCompleteEvent20,favorableCompleteEvent21,favorableCompleteEvent22,favorableCompleteEvent23,favorableCompleteEvent24,favorableCompleteEvent25,favorableCompleteEvent26,favorableCompleteEvent27,favorableCompleteEvent28,favorableCompleteEvent29,favorableCompleteEvent30,taskReward]
    <;> norm_num
  have hp : rawVisits favorableCompleteS31Before [.query 1,.hydeRetriever 2] = 6 := by decide
  have hn : rawVisits favorableCompleteS31Before ([.query 1,.hydeRetriever 2]++[.selection 0]) = 1 := by decide
  have hz : (controlPenalty savedCref uniformQuoteError unitRoleUnused .complete) favorableCompleteS31Before [.query 1,.hydeRetriever 2] (.selection 0) = 0 := by
    apply control_penalty_empty_of_prior_terminal .complete savedCref uniformQuoteError favorableCompleteS31Before [.query 1,.hydeRetriever 2] (.selection 0) 10 (by decide)
    · decide
    · decide
  unfold indexScore
  rw [hs,hp,hn,hz]
  simp only [BackupStat.mean]
  norm_num

theorem favorableCompleteS31D2Cmp0 : indexScore (7/5) (controlPenalty savedCref uniformQuoteError unitRoleUnused .complete) favorableCompleteS31Before [.query 1,.hydeRetriever 2] (.selection 1) < indexScore (7/5) (controlPenalty savedCref uniformQuoteError unitRoleUnused .complete) favorableCompleteS31Before [.query 1,.hydeRetriever 2] (.selection 2) := by
  rw [favorableCompleteS31D2I0,favorableCompleteS31D2I1]
  have h := index_strict_order_from_intervals ((0/1)/1) ((0/1)/2) 0 0 (24411779/12500000) (69046943/50000000)
    (treeBonus (7/5) 6 1) (treeBonus (7/5) 6 2)
    (trajectory_bonus_6_1).1 (trajectory_bonus_6_2).2 (by norm_num)
  simpa only [treeIndex,sub_zero] using h

theorem favorableCompleteS31D2Cmp2 : indexScore (7/5) (controlPenalty savedCref uniformQuoteError unitRoleUnused .complete) favorableCompleteS31Before [.query 1,.hydeRetriever 2] (.selection 3) ≤ indexScore (7/5) (controlPenalty savedCref uniformQuoteError unitRoleUnused .complete) favorableCompleteS31Before [.query 1,.hydeRetriever 2] (.selection 2) := by
  rw [favorableCompleteS31D2I2,favorableCompleteS31D2I1]

theorem favorableCompleteS31D2Cmp3 : indexScore (7/5) (controlPenalty savedCref uniformQuoteError unitRoleUnused .complete) favorableCompleteS31Before [.query 1,.hydeRetriever 2] (.selection 0) ≤ indexScore (7/5) (controlPenalty savedCref uniformQuoteError unitRoleUnused .complete) favorableCompleteS31Before [.query 1,.hydeRetriever 2] (.selection 2) := by
  rw [favorableCompleteS31D2I3,favorableCompleteS31D2I1]

theorem favorableCompleteS31Choice2 : nativeFirstChoice (indexScore (7/5) (controlPenalty savedCref uniformQuoteError unitRoleUnused .complete) favorableCompleteS31Before [.query 1,.hydeRetriever 2]) favorableCompleteS31Before [.query 1,.hydeRetriever 2] = .selection 2 := by
  apply visited_choice_from_ordered_certificate _ _ [.query 1,.hydeRetriever 2] [.selection 1] [.selection 3,.selection 0] (.selection 2) (by decide)
  · intro a ha
    have ho : orderedLegalAvailable [.query 1,.hydeRetriever 2] = [.selection 1,.selection 2,.selection 3,.selection 0] := by decide
    rw [ho] at ha
    simp only [List.mem_cons,List.not_mem_nil,or_false] at ha
    rcases ha with rfl | rfl | rfl | rfl <;> decide
  · intro a ha
    simp only [List.mem_cons,List.not_mem_nil,or_false] at ha
    rcases ha with rfl
    · exact favorableCompleteS31D2Cmp0
  · intro a ha
    simp only [List.mem_cons,List.not_mem_nil,or_false] at ha
    rcases ha with rfl | rfl
    · exact favorableCompleteS31D2Cmp2
    · exact favorableCompleteS31D2Cmp3

theorem favorableCompleteS31ActualEvent : nativeEvent budgetTape (7/5) (controlPenalty savedCref uniformQuoteError unitRoleUnused .complete)
    (taskReward false (2/5) (1/2)) favorableCompleteS31Before = favorableCompleteEvent31 := by
  have hs0 := native_select_existing_step budgetTape (7/5) (controlPenalty savedCref uniformQuoteError unitRoleUnused .complete) favorableCompleteS31Before 8 [] (.query 1)
    (by decide) (by decide) favorableCompleteS31Choice0
  have hs1 := native_select_existing_step budgetTape (7/5) (controlPenalty savedCref uniformQuoteError unitRoleUnused .complete) favorableCompleteS31Before 7 [.query 1] (.hydeRetriever 2)
    (by decide) (by decide) favorableCompleteS31Choice1
  have hs2 := native_select_existing_step budgetTape (7/5) (controlPenalty savedCref uniformQuoteError unitRoleUnused .complete) favorableCompleteS31Before 6 [.query 1,.hydeRetriever 2] (.selection 2)
    (by decide) (by decide) favorableCompleteS31Choice2
  have hnew := native_select_new_step budgetTape (7/5) (controlPenalty savedCref uniformQuoteError unitRoleUnused .complete) favorableCompleteS31Before 5 [.query 1,.hydeRetriever 2,.selection 2]
    [.width 3,.width 0,.width 1,.width 2] (.width 0) (by decide) (by decide) (by decide) (by decide)
  have hs : nativeSelect budgetTape (7/5) (controlPenalty savedCref uniformQuoteError unitRoleUnused .complete) favorableCompleteS31Before 9 [] = [.query 1,.hydeRetriever 2,.selection 2,.width 0] := by
    rw [hs0]
    change nativeSelect budgetTape (7/5) (controlPenalty savedCref uniformQuoteError unitRoleUnused .complete) favorableCompleteS31Before 8 [.query 1] = _
    rw [hs1]
    change nativeSelect budgetTape (7/5) (controlPenalty savedCref uniformQuoteError unitRoleUnused .complete) favorableCompleteS31Before 7 [.query 1,.hydeRetriever 2] = _
    rw [hs2]
    change nativeSelect budgetTape (7/5) (controlPenalty savedCref uniformQuoteError unitRoleUnused .complete) favorableCompleteS31Before 6 [.query 1,.hydeRetriever 2,.selection 2] = _
    rw [hnew] <;> rfl
  have hr : repairedRollout budgetTape favorableCompleteS31Before 9 [.query 1,.hydeRetriever 2,.selection 2,.width 0] = [.query 1,.hydeRetriever 2,.selection 2,.width 0,.stop,.reranker 0,.topm 0,.context 0,.answer 0] := by decide
  simp only [nativeEvent,hs,hr]
  rfl

def favorableCompleteS32Before := favorableCompleteProposal.take 31

theorem favorableCompleteS32Choice0 : nativeFirstChoice (indexScore (7/5) (controlPenalty savedCref uniformQuoteError unitRoleUnused .complete) favorableCompleteS32Before []) favorableCompleteS32Before [] = .query 1 := by
  apply complete_root_from_physical_gap favorableCompleteS32Before (favorableComplete_prefix_rewards 31) (by decide)
  · intro q; fin_cases q <;> decide
  · decide
  · intro q hq
    exact AgentUCTNextExact.favorable_complete_normal_root_physical_quote_exact 31 (by omega) q hq

theorem favorableCompleteS32D1I0 : indexScore (7/5) (controlPenalty savedCref uniformQuoteError unitRoleUnused .complete) favorableCompleteS32Before [.query 1] (.hydeRetriever 1) = treeIndex ((3/2)/9) (7/5) 0 24 9 := by
  have hs : replayBackup favorableCompleteS32Before emptyStatistics ([.query 1]++[.hydeRetriever 1]) = ⟨9,(3/2)⟩ := by
    rw [replayBackup_empty_closed_form]
    simp +decide [backedEvents,favorableCompleteS32Before,favorableCompleteProposal,favorableCompleteEvent1,favorableCompleteEvent2,favorableCompleteEvent3,favorableCompleteEvent4,favorableCompleteEvent5,favorableCompleteEvent6,favorableCompleteEvent7,favorableCompleteEvent8,favorableCompleteEvent9,favorableCompleteEvent10,favorableCompleteEvent11,favorableCompleteEvent12,favorableCompleteEvent13,favorableCompleteEvent14,favorableCompleteEvent15,favorableCompleteEvent16,favorableCompleteEvent17,favorableCompleteEvent18,favorableCompleteEvent19,favorableCompleteEvent20,favorableCompleteEvent21,favorableCompleteEvent22,favorableCompleteEvent23,favorableCompleteEvent24,favorableCompleteEvent25,favorableCompleteEvent26,favorableCompleteEvent27,favorableCompleteEvent28,favorableCompleteEvent29,favorableCompleteEvent30,favorableCompleteEvent31,taskReward]
    <;> norm_num
  have hp : rawVisits favorableCompleteS32Before [.query 1] = 24 := by decide
  have hn : rawVisits favorableCompleteS32Before ([.query 1]++[.hydeRetriever 1]) = 9 := by decide
  have hz : (controlPenalty savedCref uniformQuoteError unitRoleUnused .complete) favorableCompleteS32Before [.query 1] (.hydeRetriever 1) = 0 := by
    apply control_penalty_empty_of_prior_terminal .complete savedCref uniformQuoteError favorableCompleteS32Before [.query 1] (.hydeRetriever 1) 8 (by decide)
    · decide
    · decide
  unfold indexScore
  rw [hs,hp,hn,hz]
  simp only [BackupStat.mean]
  norm_num

theorem favorableCompleteS32D1I1 : indexScore (7/5) (controlPenalty savedCref uniformQuoteError unitRoleUnused .complete) favorableCompleteS32Before [.query 1] (.hydeRetriever 0) = treeIndex ((0/1)/7) (7/5) 0 24 7 := by
  have hs : replayBackup favorableCompleteS32Before emptyStatistics ([.query 1]++[.hydeRetriever 0]) = ⟨7,(0/1)⟩ := by
    rw [replayBackup_empty_closed_form]
    simp +decide [backedEvents,favorableCompleteS32Before,favorableCompleteProposal,favorableCompleteEvent1,favorableCompleteEvent2,favorableCompleteEvent3,favorableCompleteEvent4,favorableCompleteEvent5,favorableCompleteEvent6,favorableCompleteEvent7,favorableCompleteEvent8,favorableCompleteEvent9,favorableCompleteEvent10,favorableCompleteEvent11,favorableCompleteEvent12,favorableCompleteEvent13,favorableCompleteEvent14,favorableCompleteEvent15,favorableCompleteEvent16,favorableCompleteEvent17,favorableCompleteEvent18,favorableCompleteEvent19,favorableCompleteEvent20,favorableCompleteEvent21,favorableCompleteEvent22,favorableCompleteEvent23,favorableCompleteEvent24,favorableCompleteEvent25,favorableCompleteEvent26,favorableCompleteEvent27,favorableCompleteEvent28,favorableCompleteEvent29,favorableCompleteEvent30,favorableCompleteEvent31,taskReward]
    <;> norm_num
  have hp : rawVisits favorableCompleteS32Before [.query 1] = 24 := by decide
  have hn : rawVisits favorableCompleteS32Before ([.query 1]++[.hydeRetriever 0]) = 7 := by decide
  have hz : (controlPenalty savedCref uniformQuoteError unitRoleUnused .complete) favorableCompleteS32Before [.query 1] (.hydeRetriever 0) = 0 := by
    apply control_penalty_empty_of_prior_terminal .complete savedCref uniformQuoteError favorableCompleteS32Before [.query 1] (.hydeRetriever 0) 1 (by decide)
    · decide
    · decide
  unfold indexScore
  rw [hs,hp,hn,hz]
  simp only [BackupStat.mean]
  norm_num

theorem favorableCompleteS32D1I2 : indexScore (7/5) (controlPenalty savedCref uniformQuoteError unitRoleUnused .complete) favorableCompleteS32Before [.query 1] (.hydeRetriever 2) = treeIndex ((0/1)/7) (7/5) 0 24 7 := by
  have hs : replayBackup favorableCompleteS32Before emptyStatistics ([.query 1]++[.hydeRetriever 2]) = ⟨7,(0/1)⟩ := by
    rw [replayBackup_empty_closed_form]
    simp +decide [backedEvents,favorableCompleteS32Before,favorableCompleteProposal,favorableCompleteEvent1,favorableCompleteEvent2,favorableCompleteEvent3,favorableCompleteEvent4,favorableCompleteEvent5,favorableCompleteEvent6,favorableCompleteEvent7,favorableCompleteEvent8,favorableCompleteEvent9,favorableCompleteEvent10,favorableCompleteEvent11,favorableCompleteEvent12,favorableCompleteEvent13,favorableCompleteEvent14,favorableCompleteEvent15,favorableCompleteEvent16,favorableCompleteEvent17,favorableCompleteEvent18,favorableCompleteEvent19,favorableCompleteEvent20,favorableCompleteEvent21,favorableCompleteEvent22,favorableCompleteEvent23,favorableCompleteEvent24,favorableCompleteEvent25,favorableCompleteEvent26,favorableCompleteEvent27,favorableCompleteEvent28,favorableCompleteEvent29,favorableCompleteEvent30,favorableCompleteEvent31,taskReward]
    <;> norm_num
  have hp : rawVisits favorableCompleteS32Before [.query 1] = 24 := by decide
  have hn : rawVisits favorableCompleteS32Before ([.query 1]++[.hydeRetriever 2]) = 7 := by decide
  have hz : (controlPenalty savedCref uniformQuoteError unitRoleUnused .complete) favorableCompleteS32Before [.query 1] (.hydeRetriever 2) = 0 := by
    apply control_penalty_empty_of_prior_terminal .complete savedCref uniformQuoteError favorableCompleteS32Before [.query 1] (.hydeRetriever 2) 10 (by decide)
    · decide
    · decide
  unfold indexScore
  rw [hs,hp,hn,hz]
  simp only [BackupStat.mean]
  norm_num

theorem favorableCompleteS32D1Cmp1 : indexScore (7/5) (controlPenalty savedCref uniformQuoteError unitRoleUnused .complete) favorableCompleteS32Before [.query 1] (.hydeRetriever 0) ≤ indexScore (7/5) (controlPenalty savedCref uniformQuoteError unitRoleUnused .complete) favorableCompleteS32Before [.query 1] (.hydeRetriever 1) := by
  rw [favorableCompleteS32D1I1,favorableCompleteS32D1I0]
  have h := index_weak_order_from_intervals ((3/2)/9) ((0/1)/7) 0 0 (5232857/6250000) (47468029/50000000)
    (treeBonus (7/5) 24 9) (treeBonus (7/5) 24 7)
    (trajectory_bonus_24_9).1 (trajectory_bonus_24_7).2 (by norm_num)
  simpa only [treeIndex,sub_zero] using h

theorem favorableCompleteS32D1Cmp2 : indexScore (7/5) (controlPenalty savedCref uniformQuoteError unitRoleUnused .complete) favorableCompleteS32Before [.query 1] (.hydeRetriever 2) ≤ indexScore (7/5) (controlPenalty savedCref uniformQuoteError unitRoleUnused .complete) favorableCompleteS32Before [.query 1] (.hydeRetriever 1) := by
  rw [favorableCompleteS32D1I2,favorableCompleteS32D1I0]
  have h := index_weak_order_from_intervals ((3/2)/9) ((0/1)/7) 0 0 (5232857/6250000) (47468029/50000000)
    (treeBonus (7/5) 24 9) (treeBonus (7/5) 24 7)
    (trajectory_bonus_24_9).1 (trajectory_bonus_24_7).2 (by norm_num)
  simpa only [treeIndex,sub_zero] using h

theorem favorableCompleteS32Choice1 : nativeFirstChoice (indexScore (7/5) (controlPenalty savedCref uniformQuoteError unitRoleUnused .complete) favorableCompleteS32Before [.query 1]) favorableCompleteS32Before [.query 1] = .hydeRetriever 1 := by
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
    · exact favorableCompleteS32D1Cmp1
    · exact favorableCompleteS32D1Cmp2

theorem favorableCompleteS32D2I0 : indexScore (7/5) (controlPenalty savedCref uniformQuoteError unitRoleUnused .complete) favorableCompleteS32Before [.query 1,.hydeRetriever 1] (.selection 1) = treeIndex ((0/1)/2) (7/5) 0 9 2 := by
  have hs : replayBackup favorableCompleteS32Before emptyStatistics ([.query 1,.hydeRetriever 1]++[.selection 1]) = ⟨2,(0/1)⟩ := by
    rw [replayBackup_empty_closed_form]
    simp +decide [backedEvents,favorableCompleteS32Before,favorableCompleteProposal,favorableCompleteEvent1,favorableCompleteEvent2,favorableCompleteEvent3,favorableCompleteEvent4,favorableCompleteEvent5,favorableCompleteEvent6,favorableCompleteEvent7,favorableCompleteEvent8,favorableCompleteEvent9,favorableCompleteEvent10,favorableCompleteEvent11,favorableCompleteEvent12,favorableCompleteEvent13,favorableCompleteEvent14,favorableCompleteEvent15,favorableCompleteEvent16,favorableCompleteEvent17,favorableCompleteEvent18,favorableCompleteEvent19,favorableCompleteEvent20,favorableCompleteEvent21,favorableCompleteEvent22,favorableCompleteEvent23,favorableCompleteEvent24,favorableCompleteEvent25,favorableCompleteEvent26,favorableCompleteEvent27,favorableCompleteEvent28,favorableCompleteEvent29,favorableCompleteEvent30,favorableCompleteEvent31,taskReward]
    <;> norm_num
  have hp : rawVisits favorableCompleteS32Before [.query 1,.hydeRetriever 1] = 9 := by decide
  have hn : rawVisits favorableCompleteS32Before ([.query 1,.hydeRetriever 1]++[.selection 1]) = 2 := by decide
  have hz : (controlPenalty savedCref uniformQuoteError unitRoleUnused .complete) favorableCompleteS32Before [.query 1,.hydeRetriever 1] (.selection 1) = 0 := by
    apply control_penalty_empty_of_prior_terminal .complete savedCref uniformQuoteError favorableCompleteS32Before [.query 1,.hydeRetriever 1] (.selection 1) 14 (by decide)
    · decide
    · decide
  unfold indexScore
  rw [hs,hp,hn,hz]
  simp only [BackupStat.mean]
  norm_num

theorem favorableCompleteS32D2I1 : indexScore (7/5) (controlPenalty savedCref uniformQuoteError unitRoleUnused .complete) favorableCompleteS32Before [.query 1,.hydeRetriever 1] (.selection 2) = treeIndex ((0/1)/2) (7/5) 0 9 2 := by
  have hs : replayBackup favorableCompleteS32Before emptyStatistics ([.query 1,.hydeRetriever 1]++[.selection 2]) = ⟨2,(0/1)⟩ := by
    rw [replayBackup_empty_closed_form]
    simp +decide [backedEvents,favorableCompleteS32Before,favorableCompleteProposal,favorableCompleteEvent1,favorableCompleteEvent2,favorableCompleteEvent3,favorableCompleteEvent4,favorableCompleteEvent5,favorableCompleteEvent6,favorableCompleteEvent7,favorableCompleteEvent8,favorableCompleteEvent9,favorableCompleteEvent10,favorableCompleteEvent11,favorableCompleteEvent12,favorableCompleteEvent13,favorableCompleteEvent14,favorableCompleteEvent15,favorableCompleteEvent16,favorableCompleteEvent17,favorableCompleteEvent18,favorableCompleteEvent19,favorableCompleteEvent20,favorableCompleteEvent21,favorableCompleteEvent22,favorableCompleteEvent23,favorableCompleteEvent24,favorableCompleteEvent25,favorableCompleteEvent26,favorableCompleteEvent27,favorableCompleteEvent28,favorableCompleteEvent29,favorableCompleteEvent30,favorableCompleteEvent31,taskReward]
    <;> norm_num
  have hp : rawVisits favorableCompleteS32Before [.query 1,.hydeRetriever 1] = 9 := by decide
  have hn : rawVisits favorableCompleteS32Before ([.query 1,.hydeRetriever 1]++[.selection 2]) = 2 := by decide
  have hz : (controlPenalty savedCref uniformQuoteError unitRoleUnused .complete) favorableCompleteS32Before [.query 1,.hydeRetriever 1] (.selection 2) = 0 := by
    apply control_penalty_empty_of_prior_terminal .complete savedCref uniformQuoteError favorableCompleteS32Before [.query 1,.hydeRetriever 1] (.selection 2) 15 (by decide)
    · decide
    · decide
  unfold indexScore
  rw [hs,hp,hn,hz]
  simp only [BackupStat.mean]
  norm_num

theorem favorableCompleteS32D2I2 : indexScore (7/5) (controlPenalty savedCref uniformQuoteError unitRoleUnused .complete) favorableCompleteS32Before [.query 1,.hydeRetriever 1] (.selection 3) = treeIndex ((0/1)/2) (7/5) 0 9 2 := by
  have hs : replayBackup favorableCompleteS32Before emptyStatistics ([.query 1,.hydeRetriever 1]++[.selection 3]) = ⟨2,(0/1)⟩ := by
    rw [replayBackup_empty_closed_form]
    simp +decide [backedEvents,favorableCompleteS32Before,favorableCompleteProposal,favorableCompleteEvent1,favorableCompleteEvent2,favorableCompleteEvent3,favorableCompleteEvent4,favorableCompleteEvent5,favorableCompleteEvent6,favorableCompleteEvent7,favorableCompleteEvent8,favorableCompleteEvent9,favorableCompleteEvent10,favorableCompleteEvent11,favorableCompleteEvent12,favorableCompleteEvent13,favorableCompleteEvent14,favorableCompleteEvent15,favorableCompleteEvent16,favorableCompleteEvent17,favorableCompleteEvent18,favorableCompleteEvent19,favorableCompleteEvent20,favorableCompleteEvent21,favorableCompleteEvent22,favorableCompleteEvent23,favorableCompleteEvent24,favorableCompleteEvent25,favorableCompleteEvent26,favorableCompleteEvent27,favorableCompleteEvent28,favorableCompleteEvent29,favorableCompleteEvent30,favorableCompleteEvent31,taskReward]
    <;> norm_num
  have hp : rawVisits favorableCompleteS32Before [.query 1,.hydeRetriever 1] = 9 := by decide
  have hn : rawVisits favorableCompleteS32Before ([.query 1,.hydeRetriever 1]++[.selection 3]) = 2 := by decide
  have hz : (controlPenalty savedCref uniformQuoteError unitRoleUnused .complete) favorableCompleteS32Before [.query 1,.hydeRetriever 1] (.selection 3) = 0 := by
    apply control_penalty_empty_of_prior_terminal .complete savedCref uniformQuoteError favorableCompleteS32Before [.query 1,.hydeRetriever 1] (.selection 3) 18 (by decide)
    · decide
    · decide
  unfold indexScore
  rw [hs,hp,hn,hz]
  simp only [BackupStat.mean]
  norm_num

theorem favorableCompleteS32D2I3 : indexScore (7/5) (controlPenalty savedCref uniformQuoteError unitRoleUnused .complete) favorableCompleteS32Before [.query 1,.hydeRetriever 1] (.selection 0) = treeIndex ((1/1)/2) (7/5) 0 9 2 := by
  have hs : replayBackup favorableCompleteS32Before emptyStatistics ([.query 1,.hydeRetriever 1]++[.selection 0]) = ⟨2,(1/1)⟩ := by
    rw [replayBackup_empty_closed_form]
    simp +decide [backedEvents,favorableCompleteS32Before,favorableCompleteProposal,favorableCompleteEvent1,favorableCompleteEvent2,favorableCompleteEvent3,favorableCompleteEvent4,favorableCompleteEvent5,favorableCompleteEvent6,favorableCompleteEvent7,favorableCompleteEvent8,favorableCompleteEvent9,favorableCompleteEvent10,favorableCompleteEvent11,favorableCompleteEvent12,favorableCompleteEvent13,favorableCompleteEvent14,favorableCompleteEvent15,favorableCompleteEvent16,favorableCompleteEvent17,favorableCompleteEvent18,favorableCompleteEvent19,favorableCompleteEvent20,favorableCompleteEvent21,favorableCompleteEvent22,favorableCompleteEvent23,favorableCompleteEvent24,favorableCompleteEvent25,favorableCompleteEvent26,favorableCompleteEvent27,favorableCompleteEvent28,favorableCompleteEvent29,favorableCompleteEvent30,favorableCompleteEvent31,taskReward]
    <;> norm_num
  have hp : rawVisits favorableCompleteS32Before [.query 1,.hydeRetriever 1] = 9 := by decide
  have hn : rawVisits favorableCompleteS32Before ([.query 1,.hydeRetriever 1]++[.selection 0]) = 2 := by decide
  have hz : (controlPenalty savedCref uniformQuoteError unitRoleUnused .complete) favorableCompleteS32Before [.query 1,.hydeRetriever 1] (.selection 0) = 0 := by
    apply control_penalty_empty_of_prior_terminal .complete savedCref uniformQuoteError favorableCompleteS32Before [.query 1,.hydeRetriever 1] (.selection 0) 8 (by decide)
    · decide
    · decide
  unfold indexScore
  rw [hs,hp,hn,hz]
  simp only [BackupStat.mean]
  norm_num

theorem favorableCompleteS32D2Cmp0 : indexScore (7/5) (controlPenalty savedCref uniformQuoteError unitRoleUnused .complete) favorableCompleteS32Before [.query 1,.hydeRetriever 1] (.selection 1) < indexScore (7/5) (controlPenalty savedCref uniformQuoteError unitRoleUnused .complete) favorableCompleteS32Before [.query 1,.hydeRetriever 1] (.selection 0) := by
  rw [favorableCompleteS32D2I0,favorableCompleteS32D2I3]
  have h := index_strict_order_from_intervals ((1/1)/2) ((0/1)/2) 0 0 (75108803/50000000) (75108817/50000000)
    (treeBonus (7/5) 9 2) (treeBonus (7/5) 9 2)
    (trajectory_bonus_9_2).1 (trajectory_bonus_9_2).2 (by norm_num)
  simpa only [treeIndex,sub_zero] using h

theorem favorableCompleteS32D2Cmp1 : indexScore (7/5) (controlPenalty savedCref uniformQuoteError unitRoleUnused .complete) favorableCompleteS32Before [.query 1,.hydeRetriever 1] (.selection 2) < indexScore (7/5) (controlPenalty savedCref uniformQuoteError unitRoleUnused .complete) favorableCompleteS32Before [.query 1,.hydeRetriever 1] (.selection 0) := by
  rw [favorableCompleteS32D2I1,favorableCompleteS32D2I3]
  have h := index_strict_order_from_intervals ((1/1)/2) ((0/1)/2) 0 0 (75108803/50000000) (75108817/50000000)
    (treeBonus (7/5) 9 2) (treeBonus (7/5) 9 2)
    (trajectory_bonus_9_2).1 (trajectory_bonus_9_2).2 (by norm_num)
  simpa only [treeIndex,sub_zero] using h

theorem favorableCompleteS32D2Cmp2 : indexScore (7/5) (controlPenalty savedCref uniformQuoteError unitRoleUnused .complete) favorableCompleteS32Before [.query 1,.hydeRetriever 1] (.selection 3) < indexScore (7/5) (controlPenalty savedCref uniformQuoteError unitRoleUnused .complete) favorableCompleteS32Before [.query 1,.hydeRetriever 1] (.selection 0) := by
  rw [favorableCompleteS32D2I2,favorableCompleteS32D2I3]
  have h := index_strict_order_from_intervals ((1/1)/2) ((0/1)/2) 0 0 (75108803/50000000) (75108817/50000000)
    (treeBonus (7/5) 9 2) (treeBonus (7/5) 9 2)
    (trajectory_bonus_9_2).1 (trajectory_bonus_9_2).2 (by norm_num)
  simpa only [treeIndex,sub_zero] using h

theorem favorableCompleteS32Choice2 : nativeFirstChoice (indexScore (7/5) (controlPenalty savedCref uniformQuoteError unitRoleUnused .complete) favorableCompleteS32Before [.query 1,.hydeRetriever 1]) favorableCompleteS32Before [.query 1,.hydeRetriever 1] = .selection 0 := by
  apply visited_choice_from_ordered_certificate _ _ [.query 1,.hydeRetriever 1] [.selection 1,.selection 2,.selection 3] [] (.selection 0) (by decide)
  · intro a ha
    have ho : orderedLegalAvailable [.query 1,.hydeRetriever 1] = [.selection 1,.selection 2,.selection 3,.selection 0] := by decide
    rw [ho] at ha
    simp only [List.mem_cons,List.not_mem_nil,or_false] at ha
    rcases ha with rfl | rfl | rfl | rfl <;> decide
  · intro a ha
    simp only [List.mem_cons,List.not_mem_nil,or_false] at ha
    rcases ha with rfl | rfl | rfl
    · exact favorableCompleteS32D2Cmp0
    · exact favorableCompleteS32D2Cmp1
    · exact favorableCompleteS32D2Cmp2
  · simp

theorem favorableCompleteS32ActualEvent : nativeEvent budgetTape (7/5) (controlPenalty savedCref uniformQuoteError unitRoleUnused .complete)
    (taskReward false (2/5) (1/2)) favorableCompleteS32Before = favorableCompleteEvent32 := by
  have hs0 := native_select_existing_step budgetTape (7/5) (controlPenalty savedCref uniformQuoteError unitRoleUnused .complete) favorableCompleteS32Before 8 [] (.query 1)
    (by decide) (by decide) favorableCompleteS32Choice0
  have hs1 := native_select_existing_step budgetTape (7/5) (controlPenalty savedCref uniformQuoteError unitRoleUnused .complete) favorableCompleteS32Before 7 [.query 1] (.hydeRetriever 1)
    (by decide) (by decide) favorableCompleteS32Choice1
  have hs2 := native_select_existing_step budgetTape (7/5) (controlPenalty savedCref uniformQuoteError unitRoleUnused .complete) favorableCompleteS32Before 6 [.query 1,.hydeRetriever 1] (.selection 0)
    (by decide) (by decide) favorableCompleteS32Choice2
  have hnew := native_select_new_step budgetTape (7/5) (controlPenalty savedCref uniformQuoteError unitRoleUnused .complete) favorableCompleteS32Before 5 [.query 1,.hydeRetriever 1,.selection 0]
    [.width 3,.width 0,.width 2] (.width 3) (by decide) (by decide) (by decide) (by decide)
  have hs : nativeSelect budgetTape (7/5) (controlPenalty savedCref uniformQuoteError unitRoleUnused .complete) favorableCompleteS32Before 9 [] = [.query 1,.hydeRetriever 1,.selection 0,.width 3] := by
    rw [hs0]
    change nativeSelect budgetTape (7/5) (controlPenalty savedCref uniformQuoteError unitRoleUnused .complete) favorableCompleteS32Before 8 [.query 1] = _
    rw [hs1]
    change nativeSelect budgetTape (7/5) (controlPenalty savedCref uniformQuoteError unitRoleUnused .complete) favorableCompleteS32Before 7 [.query 1,.hydeRetriever 1] = _
    rw [hs2]
    change nativeSelect budgetTape (7/5) (controlPenalty savedCref uniformQuoteError unitRoleUnused .complete) favorableCompleteS32Before 6 [.query 1,.hydeRetriever 1,.selection 0] = _
    rw [hnew] <;> rfl
  have hr : repairedRollout budgetTape favorableCompleteS32Before 9 [.query 1,.hydeRetriever 1,.selection 0,.width 3] = [.query 1,.hydeRetriever 1,.selection 0,.width 3,.stop,.reranker 0,.topm 0,.context 0,.answer 0] := by decide
  simp only [nativeEvent,hs,hr]
  rfl

def favorableCompleteS33Before := favorableCompleteProposal.take 32

theorem favorableCompleteS33Choice0 : nativeFirstChoice (indexScore (7/5) (controlPenalty savedCref uniformQuoteError unitRoleUnused .complete) favorableCompleteS33Before []) favorableCompleteS33Before [] = .query 1 := by
  apply complete_root_from_physical_gap favorableCompleteS33Before (favorableComplete_prefix_rewards 32) (by decide)
  · intro q; fin_cases q <;> decide
  · decide
  · intro q hq
    exact AgentUCTNextExact.favorable_complete_normal_root_physical_quote_exact 32 (by omega) q hq

theorem favorableCompleteS33D1I0 : indexScore (7/5) (controlPenalty savedCref uniformQuoteError unitRoleUnused .complete) favorableCompleteS33Before [.query 1] (.hydeRetriever 1) = treeIndex ((3/2)/10) (7/5) 0 25 10 := by
  have hs : replayBackup favorableCompleteS33Before emptyStatistics ([.query 1]++[.hydeRetriever 1]) = ⟨10,(3/2)⟩ := by
    rw [replayBackup_empty_closed_form]
    simp +decide [backedEvents,favorableCompleteS33Before,favorableCompleteProposal,favorableCompleteEvent1,favorableCompleteEvent2,favorableCompleteEvent3,favorableCompleteEvent4,favorableCompleteEvent5,favorableCompleteEvent6,favorableCompleteEvent7,favorableCompleteEvent8,favorableCompleteEvent9,favorableCompleteEvent10,favorableCompleteEvent11,favorableCompleteEvent12,favorableCompleteEvent13,favorableCompleteEvent14,favorableCompleteEvent15,favorableCompleteEvent16,favorableCompleteEvent17,favorableCompleteEvent18,favorableCompleteEvent19,favorableCompleteEvent20,favorableCompleteEvent21,favorableCompleteEvent22,favorableCompleteEvent23,favorableCompleteEvent24,favorableCompleteEvent25,favorableCompleteEvent26,favorableCompleteEvent27,favorableCompleteEvent28,favorableCompleteEvent29,favorableCompleteEvent30,favorableCompleteEvent31,favorableCompleteEvent32,taskReward]
    <;> norm_num
  have hp : rawVisits favorableCompleteS33Before [.query 1] = 25 := by decide
  have hn : rawVisits favorableCompleteS33Before ([.query 1]++[.hydeRetriever 1]) = 10 := by decide
  have hz : (controlPenalty savedCref uniformQuoteError unitRoleUnused .complete) favorableCompleteS33Before [.query 1] (.hydeRetriever 1) = 0 := by
    apply control_penalty_empty_of_prior_terminal .complete savedCref uniformQuoteError favorableCompleteS33Before [.query 1] (.hydeRetriever 1) 8 (by decide)
    · decide
    · decide
  unfold indexScore
  rw [hs,hp,hn,hz]
  simp only [BackupStat.mean]
  norm_num

theorem favorableCompleteS33D1I1 : indexScore (7/5) (controlPenalty savedCref uniformQuoteError unitRoleUnused .complete) favorableCompleteS33Before [.query 1] (.hydeRetriever 0) = treeIndex ((0/1)/7) (7/5) 0 25 7 := by
  have hs : replayBackup favorableCompleteS33Before emptyStatistics ([.query 1]++[.hydeRetriever 0]) = ⟨7,(0/1)⟩ := by
    rw [replayBackup_empty_closed_form]
    simp +decide [backedEvents,favorableCompleteS33Before,favorableCompleteProposal,favorableCompleteEvent1,favorableCompleteEvent2,favorableCompleteEvent3,favorableCompleteEvent4,favorableCompleteEvent5,favorableCompleteEvent6,favorableCompleteEvent7,favorableCompleteEvent8,favorableCompleteEvent9,favorableCompleteEvent10,favorableCompleteEvent11,favorableCompleteEvent12,favorableCompleteEvent13,favorableCompleteEvent14,favorableCompleteEvent15,favorableCompleteEvent16,favorableCompleteEvent17,favorableCompleteEvent18,favorableCompleteEvent19,favorableCompleteEvent20,favorableCompleteEvent21,favorableCompleteEvent22,favorableCompleteEvent23,favorableCompleteEvent24,favorableCompleteEvent25,favorableCompleteEvent26,favorableCompleteEvent27,favorableCompleteEvent28,favorableCompleteEvent29,favorableCompleteEvent30,favorableCompleteEvent31,favorableCompleteEvent32,taskReward]
    <;> norm_num
  have hp : rawVisits favorableCompleteS33Before [.query 1] = 25 := by decide
  have hn : rawVisits favorableCompleteS33Before ([.query 1]++[.hydeRetriever 0]) = 7 := by decide
  have hz : (controlPenalty savedCref uniformQuoteError unitRoleUnused .complete) favorableCompleteS33Before [.query 1] (.hydeRetriever 0) = 0 := by
    apply control_penalty_empty_of_prior_terminal .complete savedCref uniformQuoteError favorableCompleteS33Before [.query 1] (.hydeRetriever 0) 1 (by decide)
    · decide
    · decide
  unfold indexScore
  rw [hs,hp,hn,hz]
  simp only [BackupStat.mean]
  norm_num

theorem favorableCompleteS33D1I2 : indexScore (7/5) (controlPenalty savedCref uniformQuoteError unitRoleUnused .complete) favorableCompleteS33Before [.query 1] (.hydeRetriever 2) = treeIndex ((0/1)/7) (7/5) 0 25 7 := by
  have hs : replayBackup favorableCompleteS33Before emptyStatistics ([.query 1]++[.hydeRetriever 2]) = ⟨7,(0/1)⟩ := by
    rw [replayBackup_empty_closed_form]
    simp +decide [backedEvents,favorableCompleteS33Before,favorableCompleteProposal,favorableCompleteEvent1,favorableCompleteEvent2,favorableCompleteEvent3,favorableCompleteEvent4,favorableCompleteEvent5,favorableCompleteEvent6,favorableCompleteEvent7,favorableCompleteEvent8,favorableCompleteEvent9,favorableCompleteEvent10,favorableCompleteEvent11,favorableCompleteEvent12,favorableCompleteEvent13,favorableCompleteEvent14,favorableCompleteEvent15,favorableCompleteEvent16,favorableCompleteEvent17,favorableCompleteEvent18,favorableCompleteEvent19,favorableCompleteEvent20,favorableCompleteEvent21,favorableCompleteEvent22,favorableCompleteEvent23,favorableCompleteEvent24,favorableCompleteEvent25,favorableCompleteEvent26,favorableCompleteEvent27,favorableCompleteEvent28,favorableCompleteEvent29,favorableCompleteEvent30,favorableCompleteEvent31,favorableCompleteEvent32,taskReward]
    <;> norm_num
  have hp : rawVisits favorableCompleteS33Before [.query 1] = 25 := by decide
  have hn : rawVisits favorableCompleteS33Before ([.query 1]++[.hydeRetriever 2]) = 7 := by decide
  have hz : (controlPenalty savedCref uniformQuoteError unitRoleUnused .complete) favorableCompleteS33Before [.query 1] (.hydeRetriever 2) = 0 := by
    apply control_penalty_empty_of_prior_terminal .complete savedCref uniformQuoteError favorableCompleteS33Before [.query 1] (.hydeRetriever 2) 10 (by decide)
    · decide
    · decide
  unfold indexScore
  rw [hs,hp,hn,hz]
  simp only [BackupStat.mean]
  norm_num

theorem favorableCompleteS33D1Cmp0 : indexScore (7/5) (controlPenalty savedCref uniformQuoteError unitRoleUnused .complete) favorableCompleteS33Before [.query 1] (.hydeRetriever 1) < indexScore (7/5) (controlPenalty savedCref uniformQuoteError unitRoleUnused .complete) favorableCompleteS33Before [.query 1] (.hydeRetriever 0) := by
  rw [favorableCompleteS33D1I0,favorableCompleteS33D1I1]
  have h := index_strict_order_from_intervals ((0/1)/7) ((3/2)/10) 0 0 (47756331/50000000) (19977909/25000000)
    (treeBonus (7/5) 25 7) (treeBonus (7/5) 25 10)
    (trajectory_bonus_25_7).1 (trajectory_bonus_25_10).2 (by norm_num)
  simpa only [treeIndex,sub_zero] using h

theorem favorableCompleteS33D1Cmp2 : indexScore (7/5) (controlPenalty savedCref uniformQuoteError unitRoleUnused .complete) favorableCompleteS33Before [.query 1] (.hydeRetriever 2) ≤ indexScore (7/5) (controlPenalty savedCref uniformQuoteError unitRoleUnused .complete) favorableCompleteS33Before [.query 1] (.hydeRetriever 0) := by
  rw [favorableCompleteS33D1I2,favorableCompleteS33D1I1]

theorem favorableCompleteS33Choice1 : nativeFirstChoice (indexScore (7/5) (controlPenalty savedCref uniformQuoteError unitRoleUnused .complete) favorableCompleteS33Before [.query 1]) favorableCompleteS33Before [.query 1] = .hydeRetriever 0 := by
  apply visited_choice_from_ordered_certificate _ _ [.query 1] [.hydeRetriever 1] [.hydeRetriever 2] (.hydeRetriever 0) (by decide)
  · intro a ha
    have ho : orderedLegalAvailable [.query 1] = [.hydeRetriever 1,.hydeRetriever 0,.hydeRetriever 2] := by decide
    rw [ho] at ha
    simp only [List.mem_cons,List.not_mem_nil,or_false] at ha
    rcases ha with rfl | rfl | rfl <;> decide
  · intro a ha
    simp only [List.mem_cons,List.not_mem_nil,or_false] at ha
    rcases ha with rfl
    · exact favorableCompleteS33D1Cmp0
  · intro a ha
    simp only [List.mem_cons,List.not_mem_nil,or_false] at ha
    rcases ha with rfl
    · exact favorableCompleteS33D1Cmp2

theorem favorableCompleteS33D2I0 : indexScore (7/5) (controlPenalty savedCref uniformQuoteError unitRoleUnused .complete) favorableCompleteS33Before [.query 1,.hydeRetriever 0] (.selection 1) = treeIndex ((0/1)/2) (7/5) 0 7 2 := by
  have hs : replayBackup favorableCompleteS33Before emptyStatistics ([.query 1,.hydeRetriever 0]++[.selection 1]) = ⟨2,(0/1)⟩ := by
    rw [replayBackup_empty_closed_form]
    simp +decide [backedEvents,favorableCompleteS33Before,favorableCompleteProposal,favorableCompleteEvent1,favorableCompleteEvent2,favorableCompleteEvent3,favorableCompleteEvent4,favorableCompleteEvent5,favorableCompleteEvent6,favorableCompleteEvent7,favorableCompleteEvent8,favorableCompleteEvent9,favorableCompleteEvent10,favorableCompleteEvent11,favorableCompleteEvent12,favorableCompleteEvent13,favorableCompleteEvent14,favorableCompleteEvent15,favorableCompleteEvent16,favorableCompleteEvent17,favorableCompleteEvent18,favorableCompleteEvent19,favorableCompleteEvent20,favorableCompleteEvent21,favorableCompleteEvent22,favorableCompleteEvent23,favorableCompleteEvent24,favorableCompleteEvent25,favorableCompleteEvent26,favorableCompleteEvent27,favorableCompleteEvent28,favorableCompleteEvent29,favorableCompleteEvent30,favorableCompleteEvent31,favorableCompleteEvent32,taskReward]
    <;> norm_num
  have hp : rawVisits favorableCompleteS33Before [.query 1,.hydeRetriever 0] = 7 := by decide
  have hn : rawVisits favorableCompleteS33Before ([.query 1,.hydeRetriever 0]++[.selection 1]) = 2 := by decide
  have hz : (controlPenalty savedCref uniformQuoteError unitRoleUnused .complete) favorableCompleteS33Before [.query 1,.hydeRetriever 0] (.selection 1) = 0 := by
    apply control_penalty_empty_of_prior_terminal .complete savedCref uniformQuoteError favorableCompleteS33Before [.query 1,.hydeRetriever 0] (.selection 1) 16 (by decide)
    · decide
    · decide
  unfold indexScore
  rw [hs,hp,hn,hz]
  simp only [BackupStat.mean]
  norm_num

theorem favorableCompleteS33D2I1 : indexScore (7/5) (controlPenalty savedCref uniformQuoteError unitRoleUnused .complete) favorableCompleteS33Before [.query 1,.hydeRetriever 0] (.selection 2) = treeIndex ((0/1)/2) (7/5) 0 7 2 := by
  have hs : replayBackup favorableCompleteS33Before emptyStatistics ([.query 1,.hydeRetriever 0]++[.selection 2]) = ⟨2,(0/1)⟩ := by
    rw [replayBackup_empty_closed_form]
    simp +decide [backedEvents,favorableCompleteS33Before,favorableCompleteProposal,favorableCompleteEvent1,favorableCompleteEvent2,favorableCompleteEvent3,favorableCompleteEvent4,favorableCompleteEvent5,favorableCompleteEvent6,favorableCompleteEvent7,favorableCompleteEvent8,favorableCompleteEvent9,favorableCompleteEvent10,favorableCompleteEvent11,favorableCompleteEvent12,favorableCompleteEvent13,favorableCompleteEvent14,favorableCompleteEvent15,favorableCompleteEvent16,favorableCompleteEvent17,favorableCompleteEvent18,favorableCompleteEvent19,favorableCompleteEvent20,favorableCompleteEvent21,favorableCompleteEvent22,favorableCompleteEvent23,favorableCompleteEvent24,favorableCompleteEvent25,favorableCompleteEvent26,favorableCompleteEvent27,favorableCompleteEvent28,favorableCompleteEvent29,favorableCompleteEvent30,favorableCompleteEvent31,favorableCompleteEvent32,taskReward]
    <;> norm_num
  have hp : rawVisits favorableCompleteS33Before [.query 1,.hydeRetriever 0] = 7 := by decide
  have hn : rawVisits favorableCompleteS33Before ([.query 1,.hydeRetriever 0]++[.selection 2]) = 2 := by decide
  have hz : (controlPenalty savedCref uniformQuoteError unitRoleUnused .complete) favorableCompleteS33Before [.query 1,.hydeRetriever 0] (.selection 2) = 0 := by
    apply control_penalty_empty_of_prior_terminal .complete savedCref uniformQuoteError favorableCompleteS33Before [.query 1,.hydeRetriever 0] (.selection 2) 19 (by decide)
    · decide
    · decide
  unfold indexScore
  rw [hs,hp,hn,hz]
  simp only [BackupStat.mean]
  norm_num

theorem favorableCompleteS33D2I2 : indexScore (7/5) (controlPenalty savedCref uniformQuoteError unitRoleUnused .complete) favorableCompleteS33Before [.query 1,.hydeRetriever 0] (.selection 3) = treeIndex ((0/1)/1) (7/5) 0 7 1 := by
  have hs : replayBackup favorableCompleteS33Before emptyStatistics ([.query 1,.hydeRetriever 0]++[.selection 3]) = ⟨1,(0/1)⟩ := by
    rw [replayBackup_empty_closed_form]
    simp +decide [backedEvents,favorableCompleteS33Before,favorableCompleteProposal,favorableCompleteEvent1,favorableCompleteEvent2,favorableCompleteEvent3,favorableCompleteEvent4,favorableCompleteEvent5,favorableCompleteEvent6,favorableCompleteEvent7,favorableCompleteEvent8,favorableCompleteEvent9,favorableCompleteEvent10,favorableCompleteEvent11,favorableCompleteEvent12,favorableCompleteEvent13,favorableCompleteEvent14,favorableCompleteEvent15,favorableCompleteEvent16,favorableCompleteEvent17,favorableCompleteEvent18,favorableCompleteEvent19,favorableCompleteEvent20,favorableCompleteEvent21,favorableCompleteEvent22,favorableCompleteEvent23,favorableCompleteEvent24,favorableCompleteEvent25,favorableCompleteEvent26,favorableCompleteEvent27,favorableCompleteEvent28,favorableCompleteEvent29,favorableCompleteEvent30,favorableCompleteEvent31,favorableCompleteEvent32,taskReward]
    <;> norm_num
  have hp : rawVisits favorableCompleteS33Before [.query 1,.hydeRetriever 0] = 7 := by decide
  have hn : rawVisits favorableCompleteS33Before ([.query 1,.hydeRetriever 0]++[.selection 3]) = 1 := by decide
  have hz : (controlPenalty savedCref uniformQuoteError unitRoleUnused .complete) favorableCompleteS33Before [.query 1,.hydeRetriever 0] (.selection 3) = 0 := by
    apply control_penalty_empty_of_prior_terminal .complete savedCref uniformQuoteError favorableCompleteS33Before [.query 1,.hydeRetriever 0] (.selection 3) 23 (by decide)
    · decide
    · decide
  unfold indexScore
  rw [hs,hp,hn,hz]
  simp only [BackupStat.mean]
  norm_num

theorem favorableCompleteS33D2I3 : indexScore (7/5) (controlPenalty savedCref uniformQuoteError unitRoleUnused .complete) favorableCompleteS33Before [.query 1,.hydeRetriever 0] (.selection 0) = treeIndex ((0/1)/1) (7/5) 0 7 1 := by
  have hs : replayBackup favorableCompleteS33Before emptyStatistics ([.query 1,.hydeRetriever 0]++[.selection 0]) = ⟨1,(0/1)⟩ := by
    rw [replayBackup_empty_closed_form]
    simp +decide [backedEvents,favorableCompleteS33Before,favorableCompleteProposal,favorableCompleteEvent1,favorableCompleteEvent2,favorableCompleteEvent3,favorableCompleteEvent4,favorableCompleteEvent5,favorableCompleteEvent6,favorableCompleteEvent7,favorableCompleteEvent8,favorableCompleteEvent9,favorableCompleteEvent10,favorableCompleteEvent11,favorableCompleteEvent12,favorableCompleteEvent13,favorableCompleteEvent14,favorableCompleteEvent15,favorableCompleteEvent16,favorableCompleteEvent17,favorableCompleteEvent18,favorableCompleteEvent19,favorableCompleteEvent20,favorableCompleteEvent21,favorableCompleteEvent22,favorableCompleteEvent23,favorableCompleteEvent24,favorableCompleteEvent25,favorableCompleteEvent26,favorableCompleteEvent27,favorableCompleteEvent28,favorableCompleteEvent29,favorableCompleteEvent30,favorableCompleteEvent31,favorableCompleteEvent32,taskReward]
    <;> norm_num
  have hp : rawVisits favorableCompleteS33Before [.query 1,.hydeRetriever 0] = 7 := by decide
  have hn : rawVisits favorableCompleteS33Before ([.query 1,.hydeRetriever 0]++[.selection 0]) = 1 := by decide
  have hz : (controlPenalty savedCref uniformQuoteError unitRoleUnused .complete) favorableCompleteS33Before [.query 1,.hydeRetriever 0] (.selection 0) = 0 := by
    apply control_penalty_empty_of_prior_terminal .complete savedCref uniformQuoteError favorableCompleteS33Before [.query 1,.hydeRetriever 0] (.selection 0) 1 (by decide)
    · decide
    · decide
  unfold indexScore
  rw [hs,hp,hn,hz]
  simp only [BackupStat.mean]
  norm_num

theorem favorableCompleteS33D2Cmp0 : indexScore (7/5) (controlPenalty savedCref uniformQuoteError unitRoleUnused .complete) favorableCompleteS33Before [.query 1,.hydeRetriever 0] (.selection 1) < indexScore (7/5) (controlPenalty savedCref uniformQuoteError unitRoleUnused .complete) favorableCompleteS33Before [.query 1,.hydeRetriever 0] (.selection 3) := by
  rw [favorableCompleteS33D2I0,favorableCompleteS33D2I2]
  have h := index_strict_order_from_intervals ((0/1)/1) ((0/1)/2) 0 0 (25235469/12500000) (71376697/50000000)
    (treeBonus (7/5) 7 1) (treeBonus (7/5) 7 2)
    (trajectory_bonus_7_1).1 (trajectory_bonus_7_2).2 (by norm_num)
  simpa only [treeIndex,sub_zero] using h

theorem favorableCompleteS33D2Cmp1 : indexScore (7/5) (controlPenalty savedCref uniformQuoteError unitRoleUnused .complete) favorableCompleteS33Before [.query 1,.hydeRetriever 0] (.selection 2) < indexScore (7/5) (controlPenalty savedCref uniformQuoteError unitRoleUnused .complete) favorableCompleteS33Before [.query 1,.hydeRetriever 0] (.selection 3) := by
  rw [favorableCompleteS33D2I1,favorableCompleteS33D2I2]
  have h := index_strict_order_from_intervals ((0/1)/1) ((0/1)/2) 0 0 (25235469/12500000) (71376697/50000000)
    (treeBonus (7/5) 7 1) (treeBonus (7/5) 7 2)
    (trajectory_bonus_7_1).1 (trajectory_bonus_7_2).2 (by norm_num)
  simpa only [treeIndex,sub_zero] using h

theorem favorableCompleteS33D2Cmp3 : indexScore (7/5) (controlPenalty savedCref uniformQuoteError unitRoleUnused .complete) favorableCompleteS33Before [.query 1,.hydeRetriever 0] (.selection 0) ≤ indexScore (7/5) (controlPenalty savedCref uniformQuoteError unitRoleUnused .complete) favorableCompleteS33Before [.query 1,.hydeRetriever 0] (.selection 3) := by
  rw [favorableCompleteS33D2I3,favorableCompleteS33D2I2]

theorem favorableCompleteS33Choice2 : nativeFirstChoice (indexScore (7/5) (controlPenalty savedCref uniformQuoteError unitRoleUnused .complete) favorableCompleteS33Before [.query 1,.hydeRetriever 0]) favorableCompleteS33Before [.query 1,.hydeRetriever 0] = .selection 3 := by
  apply visited_choice_from_ordered_certificate _ _ [.query 1,.hydeRetriever 0] [.selection 1,.selection 2] [.selection 0] (.selection 3) (by decide)
  · intro a ha
    have ho : orderedLegalAvailable [.query 1,.hydeRetriever 0] = [.selection 1,.selection 2,.selection 3,.selection 0] := by decide
    rw [ho] at ha
    simp only [List.mem_cons,List.not_mem_nil,or_false] at ha
    rcases ha with rfl | rfl | rfl | rfl <;> decide
  · intro a ha
    simp only [List.mem_cons,List.not_mem_nil,or_false] at ha
    rcases ha with rfl | rfl
    · exact favorableCompleteS33D2Cmp0
    · exact favorableCompleteS33D2Cmp1
  · intro a ha
    simp only [List.mem_cons,List.not_mem_nil,or_false] at ha
    rcases ha with rfl
    · exact favorableCompleteS33D2Cmp3

theorem favorableCompleteS33ActualEvent : nativeEvent budgetTape (7/5) (controlPenalty savedCref uniformQuoteError unitRoleUnused .complete)
    (taskReward false (2/5) (1/2)) favorableCompleteS33Before = favorableCompleteEvent33 := by
  have hs0 := native_select_existing_step budgetTape (7/5) (controlPenalty savedCref uniformQuoteError unitRoleUnused .complete) favorableCompleteS33Before 8 [] (.query 1)
    (by decide) (by decide) favorableCompleteS33Choice0
  have hs1 := native_select_existing_step budgetTape (7/5) (controlPenalty savedCref uniformQuoteError unitRoleUnused .complete) favorableCompleteS33Before 7 [.query 1] (.hydeRetriever 0)
    (by decide) (by decide) favorableCompleteS33Choice1
  have hs2 := native_select_existing_step budgetTape (7/5) (controlPenalty savedCref uniformQuoteError unitRoleUnused .complete) favorableCompleteS33Before 6 [.query 1,.hydeRetriever 0] (.selection 3)
    (by decide) (by decide) favorableCompleteS33Choice2
  have hnew := native_select_new_step budgetTape (7/5) (controlPenalty savedCref uniformQuoteError unitRoleUnused .complete) favorableCompleteS33Before 5 [.query 1,.hydeRetriever 0,.selection 3]
    [.width 3,.width 0,.width 1,.width 2] (.width 0) (by decide) (by decide) (by decide) (by decide)
  have hs : nativeSelect budgetTape (7/5) (controlPenalty savedCref uniformQuoteError unitRoleUnused .complete) favorableCompleteS33Before 9 [] = [.query 1,.hydeRetriever 0,.selection 3,.width 0] := by
    rw [hs0]
    change nativeSelect budgetTape (7/5) (controlPenalty savedCref uniformQuoteError unitRoleUnused .complete) favorableCompleteS33Before 8 [.query 1] = _
    rw [hs1]
    change nativeSelect budgetTape (7/5) (controlPenalty savedCref uniformQuoteError unitRoleUnused .complete) favorableCompleteS33Before 7 [.query 1,.hydeRetriever 0] = _
    rw [hs2]
    change nativeSelect budgetTape (7/5) (controlPenalty savedCref uniformQuoteError unitRoleUnused .complete) favorableCompleteS33Before 6 [.query 1,.hydeRetriever 0,.selection 3] = _
    rw [hnew] <;> rfl
  have hr : repairedRollout budgetTape favorableCompleteS33Before 9 [.query 1,.hydeRetriever 0,.selection 3,.width 0] = [.query 1,.hydeRetriever 0,.selection 3,.width 0,.stop,.reranker 0,.topm 0,.context 0,.answer 0] := by decide
  simp only [nativeEvent,hs,hr]
  rfl

def favorableCompleteS34Before := favorableCompleteProposal.take 33

theorem favorableCompleteS34Choice0 : nativeFirstChoice (indexScore (7/5) (controlPenalty savedCref uniformQuoteError unitRoleUnused .complete) favorableCompleteS34Before []) favorableCompleteS34Before [] = .query 1 := by
  apply complete_root_from_physical_gap favorableCompleteS34Before (favorableComplete_prefix_rewards 33) (by decide)
  · intro q; fin_cases q <;> decide
  · decide
  · intro q hq
    exact AgentUCTNextExact.favorable_complete_normal_root_physical_quote_exact 33 (by omega) q hq

theorem favorableCompleteS34D1I0 : indexScore (7/5) (controlPenalty savedCref uniformQuoteError unitRoleUnused .complete) favorableCompleteS34Before [.query 1] (.hydeRetriever 1) = treeIndex ((3/2)/10) (7/5) 0 26 10 := by
  have hs : replayBackup favorableCompleteS34Before emptyStatistics ([.query 1]++[.hydeRetriever 1]) = ⟨10,(3/2)⟩ := by
    rw [replayBackup_empty_closed_form]
    simp +decide [backedEvents,favorableCompleteS34Before,favorableCompleteProposal,favorableCompleteEvent1,favorableCompleteEvent2,favorableCompleteEvent3,favorableCompleteEvent4,favorableCompleteEvent5,favorableCompleteEvent6,favorableCompleteEvent7,favorableCompleteEvent8,favorableCompleteEvent9,favorableCompleteEvent10,favorableCompleteEvent11,favorableCompleteEvent12,favorableCompleteEvent13,favorableCompleteEvent14,favorableCompleteEvent15,favorableCompleteEvent16,favorableCompleteEvent17,favorableCompleteEvent18,favorableCompleteEvent19,favorableCompleteEvent20,favorableCompleteEvent21,favorableCompleteEvent22,favorableCompleteEvent23,favorableCompleteEvent24,favorableCompleteEvent25,favorableCompleteEvent26,favorableCompleteEvent27,favorableCompleteEvent28,favorableCompleteEvent29,favorableCompleteEvent30,favorableCompleteEvent31,favorableCompleteEvent32,favorableCompleteEvent33,taskReward]
    <;> norm_num
  have hp : rawVisits favorableCompleteS34Before [.query 1] = 26 := by decide
  have hn : rawVisits favorableCompleteS34Before ([.query 1]++[.hydeRetriever 1]) = 10 := by decide
  have hz : (controlPenalty savedCref uniformQuoteError unitRoleUnused .complete) favorableCompleteS34Before [.query 1] (.hydeRetriever 1) = 0 := by
    apply control_penalty_empty_of_prior_terminal .complete savedCref uniformQuoteError favorableCompleteS34Before [.query 1] (.hydeRetriever 1) 8 (by decide)
    · decide
    · decide
  unfold indexScore
  rw [hs,hp,hn,hz]
  simp only [BackupStat.mean]
  norm_num

theorem favorableCompleteS34D1I1 : indexScore (7/5) (controlPenalty savedCref uniformQuoteError unitRoleUnused .complete) favorableCompleteS34Before [.query 1] (.hydeRetriever 0) = treeIndex ((0/1)/8) (7/5) 0 26 8 := by
  have hs : replayBackup favorableCompleteS34Before emptyStatistics ([.query 1]++[.hydeRetriever 0]) = ⟨8,(0/1)⟩ := by
    rw [replayBackup_empty_closed_form]
    simp +decide [backedEvents,favorableCompleteS34Before,favorableCompleteProposal,favorableCompleteEvent1,favorableCompleteEvent2,favorableCompleteEvent3,favorableCompleteEvent4,favorableCompleteEvent5,favorableCompleteEvent6,favorableCompleteEvent7,favorableCompleteEvent8,favorableCompleteEvent9,favorableCompleteEvent10,favorableCompleteEvent11,favorableCompleteEvent12,favorableCompleteEvent13,favorableCompleteEvent14,favorableCompleteEvent15,favorableCompleteEvent16,favorableCompleteEvent17,favorableCompleteEvent18,favorableCompleteEvent19,favorableCompleteEvent20,favorableCompleteEvent21,favorableCompleteEvent22,favorableCompleteEvent23,favorableCompleteEvent24,favorableCompleteEvent25,favorableCompleteEvent26,favorableCompleteEvent27,favorableCompleteEvent28,favorableCompleteEvent29,favorableCompleteEvent30,favorableCompleteEvent31,favorableCompleteEvent32,favorableCompleteEvent33,taskReward]
    <;> norm_num
  have hp : rawVisits favorableCompleteS34Before [.query 1] = 26 := by decide
  have hn : rawVisits favorableCompleteS34Before ([.query 1]++[.hydeRetriever 0]) = 8 := by decide
  have hz : (controlPenalty savedCref uniformQuoteError unitRoleUnused .complete) favorableCompleteS34Before [.query 1] (.hydeRetriever 0) = 0 := by
    apply control_penalty_empty_of_prior_terminal .complete savedCref uniformQuoteError favorableCompleteS34Before [.query 1] (.hydeRetriever 0) 1 (by decide)
    · decide
    · decide
  unfold indexScore
  rw [hs,hp,hn,hz]
  simp only [BackupStat.mean]
  norm_num

theorem favorableCompleteS34D1I2 : indexScore (7/5) (controlPenalty savedCref uniformQuoteError unitRoleUnused .complete) favorableCompleteS34Before [.query 1] (.hydeRetriever 2) = treeIndex ((0/1)/7) (7/5) 0 26 7 := by
  have hs : replayBackup favorableCompleteS34Before emptyStatistics ([.query 1]++[.hydeRetriever 2]) = ⟨7,(0/1)⟩ := by
    rw [replayBackup_empty_closed_form]
    simp +decide [backedEvents,favorableCompleteS34Before,favorableCompleteProposal,favorableCompleteEvent1,favorableCompleteEvent2,favorableCompleteEvent3,favorableCompleteEvent4,favorableCompleteEvent5,favorableCompleteEvent6,favorableCompleteEvent7,favorableCompleteEvent8,favorableCompleteEvent9,favorableCompleteEvent10,favorableCompleteEvent11,favorableCompleteEvent12,favorableCompleteEvent13,favorableCompleteEvent14,favorableCompleteEvent15,favorableCompleteEvent16,favorableCompleteEvent17,favorableCompleteEvent18,favorableCompleteEvent19,favorableCompleteEvent20,favorableCompleteEvent21,favorableCompleteEvent22,favorableCompleteEvent23,favorableCompleteEvent24,favorableCompleteEvent25,favorableCompleteEvent26,favorableCompleteEvent27,favorableCompleteEvent28,favorableCompleteEvent29,favorableCompleteEvent30,favorableCompleteEvent31,favorableCompleteEvent32,favorableCompleteEvent33,taskReward]
    <;> norm_num
  have hp : rawVisits favorableCompleteS34Before [.query 1] = 26 := by decide
  have hn : rawVisits favorableCompleteS34Before ([.query 1]++[.hydeRetriever 2]) = 7 := by decide
  have hz : (controlPenalty savedCref uniformQuoteError unitRoleUnused .complete) favorableCompleteS34Before [.query 1] (.hydeRetriever 2) = 0 := by
    apply control_penalty_empty_of_prior_terminal .complete savedCref uniformQuoteError favorableCompleteS34Before [.query 1] (.hydeRetriever 2) 10 (by decide)
    · decide
    · decide
  unfold indexScore
  rw [hs,hp,hn,hz]
  simp only [BackupStat.mean]
  norm_num

theorem favorableCompleteS34D1Cmp0 : indexScore (7/5) (controlPenalty savedCref uniformQuoteError unitRoleUnused .complete) favorableCompleteS34Before [.query 1] (.hydeRetriever 1) < indexScore (7/5) (controlPenalty savedCref uniformQuoteError unitRoleUnused .complete) favorableCompleteS34Before [.query 1] (.hydeRetriever 2) := by
  rw [favorableCompleteS34D1I0,favorableCompleteS34D1I2]
  have h := index_strict_order_from_intervals ((0/1)/7) ((3/2)/10) 0 0 (48032131/50000000) (20093283/25000000)
    (treeBonus (7/5) 26 7) (treeBonus (7/5) 26 10)
    (trajectory_bonus_26_7).1 (trajectory_bonus_26_10).2 (by norm_num)
  simpa only [treeIndex,sub_zero] using h

theorem favorableCompleteS34D1Cmp1 : indexScore (7/5) (controlPenalty savedCref uniformQuoteError unitRoleUnused .complete) favorableCompleteS34Before [.query 1] (.hydeRetriever 0) < indexScore (7/5) (controlPenalty savedCref uniformQuoteError unitRoleUnused .complete) favorableCompleteS34Before [.query 1] (.hydeRetriever 2) := by
  rw [favorableCompleteS34D1I1,favorableCompleteS34D1I2]
  have h := index_strict_order_from_intervals ((0/1)/7) ((0/1)/8) 0 0 (48032131/50000000) (11232487/12500000)
    (treeBonus (7/5) 26 7) (treeBonus (7/5) 26 8)
    (trajectory_bonus_26_7).1 (trajectory_bonus_26_8).2 (by norm_num)
  simpa only [treeIndex,sub_zero] using h

theorem favorableCompleteS34Choice1 : nativeFirstChoice (indexScore (7/5) (controlPenalty savedCref uniformQuoteError unitRoleUnused .complete) favorableCompleteS34Before [.query 1]) favorableCompleteS34Before [.query 1] = .hydeRetriever 2 := by
  apply visited_choice_from_ordered_certificate _ _ [.query 1] [.hydeRetriever 1,.hydeRetriever 0] [] (.hydeRetriever 2) (by decide)
  · intro a ha
    have ho : orderedLegalAvailable [.query 1] = [.hydeRetriever 1,.hydeRetriever 0,.hydeRetriever 2] := by decide
    rw [ho] at ha
    simp only [List.mem_cons,List.not_mem_nil,or_false] at ha
    rcases ha with rfl | rfl | rfl <;> decide
  · intro a ha
    simp only [List.mem_cons,List.not_mem_nil,or_false] at ha
    rcases ha with rfl | rfl
    · exact favorableCompleteS34D1Cmp0
    · exact favorableCompleteS34D1Cmp1
  · simp

theorem favorableCompleteS34D2I0 : indexScore (7/5) (controlPenalty savedCref uniformQuoteError unitRoleUnused .complete) favorableCompleteS34Before [.query 1,.hydeRetriever 2] (.selection 1) = treeIndex ((0/1)/2) (7/5) 0 7 2 := by
  have hs : replayBackup favorableCompleteS34Before emptyStatistics ([.query 1,.hydeRetriever 2]++[.selection 1]) = ⟨2,(0/1)⟩ := by
    rw [replayBackup_empty_closed_form]
    simp +decide [backedEvents,favorableCompleteS34Before,favorableCompleteProposal,favorableCompleteEvent1,favorableCompleteEvent2,favorableCompleteEvent3,favorableCompleteEvent4,favorableCompleteEvent5,favorableCompleteEvent6,favorableCompleteEvent7,favorableCompleteEvent8,favorableCompleteEvent9,favorableCompleteEvent10,favorableCompleteEvent11,favorableCompleteEvent12,favorableCompleteEvent13,favorableCompleteEvent14,favorableCompleteEvent15,favorableCompleteEvent16,favorableCompleteEvent17,favorableCompleteEvent18,favorableCompleteEvent19,favorableCompleteEvent20,favorableCompleteEvent21,favorableCompleteEvent22,favorableCompleteEvent23,favorableCompleteEvent24,favorableCompleteEvent25,favorableCompleteEvent26,favorableCompleteEvent27,favorableCompleteEvent28,favorableCompleteEvent29,favorableCompleteEvent30,favorableCompleteEvent31,favorableCompleteEvent32,favorableCompleteEvent33,taskReward]
    <;> norm_num
  have hp : rawVisits favorableCompleteS34Before [.query 1,.hydeRetriever 2] = 7 := by decide
  have hn : rawVisits favorableCompleteS34Before ([.query 1,.hydeRetriever 2]++[.selection 1]) = 2 := by decide
  have hz : (controlPenalty savedCref uniformQuoteError unitRoleUnused .complete) favorableCompleteS34Before [.query 1,.hydeRetriever 2] (.selection 1) = 0 := by
    apply control_penalty_empty_of_prior_terminal .complete savedCref uniformQuoteError favorableCompleteS34Before [.query 1,.hydeRetriever 2] (.selection 1) 17 (by decide)
    · decide
    · decide
  unfold indexScore
  rw [hs,hp,hn,hz]
  simp only [BackupStat.mean]
  norm_num

theorem favorableCompleteS34D2I1 : indexScore (7/5) (controlPenalty savedCref uniformQuoteError unitRoleUnused .complete) favorableCompleteS34Before [.query 1,.hydeRetriever 2] (.selection 2) = treeIndex ((0/1)/2) (7/5) 0 7 2 := by
  have hs : replayBackup favorableCompleteS34Before emptyStatistics ([.query 1,.hydeRetriever 2]++[.selection 2]) = ⟨2,(0/1)⟩ := by
    rw [replayBackup_empty_closed_form]
    simp +decide [backedEvents,favorableCompleteS34Before,favorableCompleteProposal,favorableCompleteEvent1,favorableCompleteEvent2,favorableCompleteEvent3,favorableCompleteEvent4,favorableCompleteEvent5,favorableCompleteEvent6,favorableCompleteEvent7,favorableCompleteEvent8,favorableCompleteEvent9,favorableCompleteEvent10,favorableCompleteEvent11,favorableCompleteEvent12,favorableCompleteEvent13,favorableCompleteEvent14,favorableCompleteEvent15,favorableCompleteEvent16,favorableCompleteEvent17,favorableCompleteEvent18,favorableCompleteEvent19,favorableCompleteEvent20,favorableCompleteEvent21,favorableCompleteEvent22,favorableCompleteEvent23,favorableCompleteEvent24,favorableCompleteEvent25,favorableCompleteEvent26,favorableCompleteEvent27,favorableCompleteEvent28,favorableCompleteEvent29,favorableCompleteEvent30,favorableCompleteEvent31,favorableCompleteEvent32,favorableCompleteEvent33,taskReward]
    <;> norm_num
  have hp : rawVisits favorableCompleteS34Before [.query 1,.hydeRetriever 2] = 7 := by decide
  have hn : rawVisits favorableCompleteS34Before ([.query 1,.hydeRetriever 2]++[.selection 2]) = 2 := by decide
  have hz : (controlPenalty savedCref uniformQuoteError unitRoleUnused .complete) favorableCompleteS34Before [.query 1,.hydeRetriever 2] (.selection 2) = 0 := by
    apply control_penalty_empty_of_prior_terminal .complete savedCref uniformQuoteError favorableCompleteS34Before [.query 1,.hydeRetriever 2] (.selection 2) 20 (by decide)
    · decide
    · decide
  unfold indexScore
  rw [hs,hp,hn,hz]
  simp only [BackupStat.mean]
  norm_num

theorem favorableCompleteS34D2I2 : indexScore (7/5) (controlPenalty savedCref uniformQuoteError unitRoleUnused .complete) favorableCompleteS34Before [.query 1,.hydeRetriever 2] (.selection 3) = treeIndex ((0/1)/1) (7/5) 0 7 1 := by
  have hs : replayBackup favorableCompleteS34Before emptyStatistics ([.query 1,.hydeRetriever 2]++[.selection 3]) = ⟨1,(0/1)⟩ := by
    rw [replayBackup_empty_closed_form]
    simp +decide [backedEvents,favorableCompleteS34Before,favorableCompleteProposal,favorableCompleteEvent1,favorableCompleteEvent2,favorableCompleteEvent3,favorableCompleteEvent4,favorableCompleteEvent5,favorableCompleteEvent6,favorableCompleteEvent7,favorableCompleteEvent8,favorableCompleteEvent9,favorableCompleteEvent10,favorableCompleteEvent11,favorableCompleteEvent12,favorableCompleteEvent13,favorableCompleteEvent14,favorableCompleteEvent15,favorableCompleteEvent16,favorableCompleteEvent17,favorableCompleteEvent18,favorableCompleteEvent19,favorableCompleteEvent20,favorableCompleteEvent21,favorableCompleteEvent22,favorableCompleteEvent23,favorableCompleteEvent24,favorableCompleteEvent25,favorableCompleteEvent26,favorableCompleteEvent27,favorableCompleteEvent28,favorableCompleteEvent29,favorableCompleteEvent30,favorableCompleteEvent31,favorableCompleteEvent32,favorableCompleteEvent33,taskReward]
    <;> norm_num
  have hp : rawVisits favorableCompleteS34Before [.query 1,.hydeRetriever 2] = 7 := by decide
  have hn : rawVisits favorableCompleteS34Before ([.query 1,.hydeRetriever 2]++[.selection 3]) = 1 := by decide
  have hz : (controlPenalty savedCref uniformQuoteError unitRoleUnused .complete) favorableCompleteS34Before [.query 1,.hydeRetriever 2] (.selection 3) = 0 := by
    apply control_penalty_empty_of_prior_terminal .complete savedCref uniformQuoteError favorableCompleteS34Before [.query 1,.hydeRetriever 2] (.selection 3) 24 (by decide)
    · decide
    · decide
  unfold indexScore
  rw [hs,hp,hn,hz]
  simp only [BackupStat.mean]
  norm_num

theorem favorableCompleteS34D2I3 : indexScore (7/5) (controlPenalty savedCref uniformQuoteError unitRoleUnused .complete) favorableCompleteS34Before [.query 1,.hydeRetriever 2] (.selection 0) = treeIndex ((0/1)/1) (7/5) 0 7 1 := by
  have hs : replayBackup favorableCompleteS34Before emptyStatistics ([.query 1,.hydeRetriever 2]++[.selection 0]) = ⟨1,(0/1)⟩ := by
    rw [replayBackup_empty_closed_form]
    simp +decide [backedEvents,favorableCompleteS34Before,favorableCompleteProposal,favorableCompleteEvent1,favorableCompleteEvent2,favorableCompleteEvent3,favorableCompleteEvent4,favorableCompleteEvent5,favorableCompleteEvent6,favorableCompleteEvent7,favorableCompleteEvent8,favorableCompleteEvent9,favorableCompleteEvent10,favorableCompleteEvent11,favorableCompleteEvent12,favorableCompleteEvent13,favorableCompleteEvent14,favorableCompleteEvent15,favorableCompleteEvent16,favorableCompleteEvent17,favorableCompleteEvent18,favorableCompleteEvent19,favorableCompleteEvent20,favorableCompleteEvent21,favorableCompleteEvent22,favorableCompleteEvent23,favorableCompleteEvent24,favorableCompleteEvent25,favorableCompleteEvent26,favorableCompleteEvent27,favorableCompleteEvent28,favorableCompleteEvent29,favorableCompleteEvent30,favorableCompleteEvent31,favorableCompleteEvent32,favorableCompleteEvent33,taskReward]
    <;> norm_num
  have hp : rawVisits favorableCompleteS34Before [.query 1,.hydeRetriever 2] = 7 := by decide
  have hn : rawVisits favorableCompleteS34Before ([.query 1,.hydeRetriever 2]++[.selection 0]) = 1 := by decide
  have hz : (controlPenalty savedCref uniformQuoteError unitRoleUnused .complete) favorableCompleteS34Before [.query 1,.hydeRetriever 2] (.selection 0) = 0 := by
    apply control_penalty_empty_of_prior_terminal .complete savedCref uniformQuoteError favorableCompleteS34Before [.query 1,.hydeRetriever 2] (.selection 0) 10 (by decide)
    · decide
    · decide
  unfold indexScore
  rw [hs,hp,hn,hz]
  simp only [BackupStat.mean]
  norm_num

theorem favorableCompleteS34D2Cmp0 : indexScore (7/5) (controlPenalty savedCref uniformQuoteError unitRoleUnused .complete) favorableCompleteS34Before [.query 1,.hydeRetriever 2] (.selection 1) < indexScore (7/5) (controlPenalty savedCref uniformQuoteError unitRoleUnused .complete) favorableCompleteS34Before [.query 1,.hydeRetriever 2] (.selection 3) := by
  rw [favorableCompleteS34D2I0,favorableCompleteS34D2I2]
  have h := index_strict_order_from_intervals ((0/1)/1) ((0/1)/2) 0 0 (25235469/12500000) (71376697/50000000)
    (treeBonus (7/5) 7 1) (treeBonus (7/5) 7 2)
    (trajectory_bonus_7_1).1 (trajectory_bonus_7_2).2 (by norm_num)
  simpa only [treeIndex,sub_zero] using h

theorem favorableCompleteS34D2Cmp1 : indexScore (7/5) (controlPenalty savedCref uniformQuoteError unitRoleUnused .complete) favorableCompleteS34Before [.query 1,.hydeRetriever 2] (.selection 2) < indexScore (7/5) (controlPenalty savedCref uniformQuoteError unitRoleUnused .complete) favorableCompleteS34Before [.query 1,.hydeRetriever 2] (.selection 3) := by
  rw [favorableCompleteS34D2I1,favorableCompleteS34D2I2]
  have h := index_strict_order_from_intervals ((0/1)/1) ((0/1)/2) 0 0 (25235469/12500000) (71376697/50000000)
    (treeBonus (7/5) 7 1) (treeBonus (7/5) 7 2)
    (trajectory_bonus_7_1).1 (trajectory_bonus_7_2).2 (by norm_num)
  simpa only [treeIndex,sub_zero] using h

theorem favorableCompleteS34D2Cmp3 : indexScore (7/5) (controlPenalty savedCref uniformQuoteError unitRoleUnused .complete) favorableCompleteS34Before [.query 1,.hydeRetriever 2] (.selection 0) ≤ indexScore (7/5) (controlPenalty savedCref uniformQuoteError unitRoleUnused .complete) favorableCompleteS34Before [.query 1,.hydeRetriever 2] (.selection 3) := by
  rw [favorableCompleteS34D2I3,favorableCompleteS34D2I2]

theorem favorableCompleteS34Choice2 : nativeFirstChoice (indexScore (7/5) (controlPenalty savedCref uniformQuoteError unitRoleUnused .complete) favorableCompleteS34Before [.query 1,.hydeRetriever 2]) favorableCompleteS34Before [.query 1,.hydeRetriever 2] = .selection 3 := by
  apply visited_choice_from_ordered_certificate _ _ [.query 1,.hydeRetriever 2] [.selection 1,.selection 2] [.selection 0] (.selection 3) (by decide)
  · intro a ha
    have ho : orderedLegalAvailable [.query 1,.hydeRetriever 2] = [.selection 1,.selection 2,.selection 3,.selection 0] := by decide
    rw [ho] at ha
    simp only [List.mem_cons,List.not_mem_nil,or_false] at ha
    rcases ha with rfl | rfl | rfl | rfl <;> decide
  · intro a ha
    simp only [List.mem_cons,List.not_mem_nil,or_false] at ha
    rcases ha with rfl | rfl
    · exact favorableCompleteS34D2Cmp0
    · exact favorableCompleteS34D2Cmp1
  · intro a ha
    simp only [List.mem_cons,List.not_mem_nil,or_false] at ha
    rcases ha with rfl
    · exact favorableCompleteS34D2Cmp3

theorem favorableCompleteS34ActualEvent : nativeEvent budgetTape (7/5) (controlPenalty savedCref uniformQuoteError unitRoleUnused .complete)
    (taskReward false (2/5) (1/2)) favorableCompleteS34Before = favorableCompleteEvent34 := by
  have hs0 := native_select_existing_step budgetTape (7/5) (controlPenalty savedCref uniformQuoteError unitRoleUnused .complete) favorableCompleteS34Before 8 [] (.query 1)
    (by decide) (by decide) favorableCompleteS34Choice0
  have hs1 := native_select_existing_step budgetTape (7/5) (controlPenalty savedCref uniformQuoteError unitRoleUnused .complete) favorableCompleteS34Before 7 [.query 1] (.hydeRetriever 2)
    (by decide) (by decide) favorableCompleteS34Choice1
  have hs2 := native_select_existing_step budgetTape (7/5) (controlPenalty savedCref uniformQuoteError unitRoleUnused .complete) favorableCompleteS34Before 6 [.query 1,.hydeRetriever 2] (.selection 3)
    (by decide) (by decide) favorableCompleteS34Choice2
  have hnew := native_select_new_step budgetTape (7/5) (controlPenalty savedCref uniformQuoteError unitRoleUnused .complete) favorableCompleteS34Before 5 [.query 1,.hydeRetriever 2,.selection 3]
    [.width 3,.width 0,.width 1,.width 2] (.width 0) (by decide) (by decide) (by decide) (by decide)
  have hs : nativeSelect budgetTape (7/5) (controlPenalty savedCref uniformQuoteError unitRoleUnused .complete) favorableCompleteS34Before 9 [] = [.query 1,.hydeRetriever 2,.selection 3,.width 0] := by
    rw [hs0]
    change nativeSelect budgetTape (7/5) (controlPenalty savedCref uniformQuoteError unitRoleUnused .complete) favorableCompleteS34Before 8 [.query 1] = _
    rw [hs1]
    change nativeSelect budgetTape (7/5) (controlPenalty savedCref uniformQuoteError unitRoleUnused .complete) favorableCompleteS34Before 7 [.query 1,.hydeRetriever 2] = _
    rw [hs2]
    change nativeSelect budgetTape (7/5) (controlPenalty savedCref uniformQuoteError unitRoleUnused .complete) favorableCompleteS34Before 6 [.query 1,.hydeRetriever 2,.selection 3] = _
    rw [hnew] <;> rfl
  have hr : repairedRollout budgetTape favorableCompleteS34Before 9 [.query 1,.hydeRetriever 2,.selection 3,.width 0] = [.query 1,.hydeRetriever 2,.selection 3,.width 0,.stop,.reranker 0,.topm 0,.context 0,.answer 0] := by decide
  simp only [nativeEvent,hs,hr]
  rfl

def favorableCompleteS35Before := favorableCompleteProposal.take 34

theorem favorableCompleteS35Choice0 : nativeFirstChoice (indexScore (7/5) (controlPenalty savedCref uniformQuoteError unitRoleUnused .complete) favorableCompleteS35Before []) favorableCompleteS35Before [] = .query 1 := by
  apply complete_root_from_physical_gap favorableCompleteS35Before (favorableComplete_prefix_rewards 34) (by decide)
  · intro q; fin_cases q <;> decide
  · decide
  · intro q hq
    exact AgentUCTNextExact.favorable_complete_normal_root_physical_quote_exact 34 (by omega) q hq

theorem favorableCompleteS35D1I0 : indexScore (7/5) (controlPenalty savedCref uniformQuoteError unitRoleUnused .complete) favorableCompleteS35Before [.query 1] (.hydeRetriever 1) = treeIndex ((3/2)/10) (7/5) 0 27 10 := by
  have hs : replayBackup favorableCompleteS35Before emptyStatistics ([.query 1]++[.hydeRetriever 1]) = ⟨10,(3/2)⟩ := by
    rw [replayBackup_empty_closed_form]
    simp +decide [backedEvents,favorableCompleteS35Before,favorableCompleteProposal,favorableCompleteEvent1,favorableCompleteEvent2,favorableCompleteEvent3,favorableCompleteEvent4,favorableCompleteEvent5,favorableCompleteEvent6,favorableCompleteEvent7,favorableCompleteEvent8,favorableCompleteEvent9,favorableCompleteEvent10,favorableCompleteEvent11,favorableCompleteEvent12,favorableCompleteEvent13,favorableCompleteEvent14,favorableCompleteEvent15,favorableCompleteEvent16,favorableCompleteEvent17,favorableCompleteEvent18,favorableCompleteEvent19,favorableCompleteEvent20,favorableCompleteEvent21,favorableCompleteEvent22,favorableCompleteEvent23,favorableCompleteEvent24,favorableCompleteEvent25,favorableCompleteEvent26,favorableCompleteEvent27,favorableCompleteEvent28,favorableCompleteEvent29,favorableCompleteEvent30,favorableCompleteEvent31,favorableCompleteEvent32,favorableCompleteEvent33,favorableCompleteEvent34,taskReward]
    <;> norm_num
  have hp : rawVisits favorableCompleteS35Before [.query 1] = 27 := by decide
  have hn : rawVisits favorableCompleteS35Before ([.query 1]++[.hydeRetriever 1]) = 10 := by decide
  have hz : (controlPenalty savedCref uniformQuoteError unitRoleUnused .complete) favorableCompleteS35Before [.query 1] (.hydeRetriever 1) = 0 := by
    apply control_penalty_empty_of_prior_terminal .complete savedCref uniformQuoteError favorableCompleteS35Before [.query 1] (.hydeRetriever 1) 8 (by decide)
    · decide
    · decide
  unfold indexScore
  rw [hs,hp,hn,hz]
  simp only [BackupStat.mean]
  norm_num

theorem favorableCompleteS35D1I1 : indexScore (7/5) (controlPenalty savedCref uniformQuoteError unitRoleUnused .complete) favorableCompleteS35Before [.query 1] (.hydeRetriever 0) = treeIndex ((0/1)/8) (7/5) 0 27 8 := by
  have hs : replayBackup favorableCompleteS35Before emptyStatistics ([.query 1]++[.hydeRetriever 0]) = ⟨8,(0/1)⟩ := by
    rw [replayBackup_empty_closed_form]
    simp +decide [backedEvents,favorableCompleteS35Before,favorableCompleteProposal,favorableCompleteEvent1,favorableCompleteEvent2,favorableCompleteEvent3,favorableCompleteEvent4,favorableCompleteEvent5,favorableCompleteEvent6,favorableCompleteEvent7,favorableCompleteEvent8,favorableCompleteEvent9,favorableCompleteEvent10,favorableCompleteEvent11,favorableCompleteEvent12,favorableCompleteEvent13,favorableCompleteEvent14,favorableCompleteEvent15,favorableCompleteEvent16,favorableCompleteEvent17,favorableCompleteEvent18,favorableCompleteEvent19,favorableCompleteEvent20,favorableCompleteEvent21,favorableCompleteEvent22,favorableCompleteEvent23,favorableCompleteEvent24,favorableCompleteEvent25,favorableCompleteEvent26,favorableCompleteEvent27,favorableCompleteEvent28,favorableCompleteEvent29,favorableCompleteEvent30,favorableCompleteEvent31,favorableCompleteEvent32,favorableCompleteEvent33,favorableCompleteEvent34,taskReward]
    <;> norm_num
  have hp : rawVisits favorableCompleteS35Before [.query 1] = 27 := by decide
  have hn : rawVisits favorableCompleteS35Before ([.query 1]++[.hydeRetriever 0]) = 8 := by decide
  have hz : (controlPenalty savedCref uniformQuoteError unitRoleUnused .complete) favorableCompleteS35Before [.query 1] (.hydeRetriever 0) = 0 := by
    apply control_penalty_empty_of_prior_terminal .complete savedCref uniformQuoteError favorableCompleteS35Before [.query 1] (.hydeRetriever 0) 1 (by decide)
    · decide
    · decide
  unfold indexScore
  rw [hs,hp,hn,hz]
  simp only [BackupStat.mean]
  norm_num

theorem favorableCompleteS35D1I2 : indexScore (7/5) (controlPenalty savedCref uniformQuoteError unitRoleUnused .complete) favorableCompleteS35Before [.query 1] (.hydeRetriever 2) = treeIndex ((0/1)/8) (7/5) 0 27 8 := by
  have hs : replayBackup favorableCompleteS35Before emptyStatistics ([.query 1]++[.hydeRetriever 2]) = ⟨8,(0/1)⟩ := by
    rw [replayBackup_empty_closed_form]
    simp +decide [backedEvents,favorableCompleteS35Before,favorableCompleteProposal,favorableCompleteEvent1,favorableCompleteEvent2,favorableCompleteEvent3,favorableCompleteEvent4,favorableCompleteEvent5,favorableCompleteEvent6,favorableCompleteEvent7,favorableCompleteEvent8,favorableCompleteEvent9,favorableCompleteEvent10,favorableCompleteEvent11,favorableCompleteEvent12,favorableCompleteEvent13,favorableCompleteEvent14,favorableCompleteEvent15,favorableCompleteEvent16,favorableCompleteEvent17,favorableCompleteEvent18,favorableCompleteEvent19,favorableCompleteEvent20,favorableCompleteEvent21,favorableCompleteEvent22,favorableCompleteEvent23,favorableCompleteEvent24,favorableCompleteEvent25,favorableCompleteEvent26,favorableCompleteEvent27,favorableCompleteEvent28,favorableCompleteEvent29,favorableCompleteEvent30,favorableCompleteEvent31,favorableCompleteEvent32,favorableCompleteEvent33,favorableCompleteEvent34,taskReward]
    <;> norm_num
  have hp : rawVisits favorableCompleteS35Before [.query 1] = 27 := by decide
  have hn : rawVisits favorableCompleteS35Before ([.query 1]++[.hydeRetriever 2]) = 8 := by decide
  have hz : (controlPenalty savedCref uniformQuoteError unitRoleUnused .complete) favorableCompleteS35Before [.query 1] (.hydeRetriever 2) = 0 := by
    apply control_penalty_empty_of_prior_terminal .complete savedCref uniformQuoteError favorableCompleteS35Before [.query 1] (.hydeRetriever 2) 10 (by decide)
    · decide
    · decide
  unfold indexScore
  rw [hs,hp,hn,hz]
  simp only [BackupStat.mean]
  norm_num

theorem favorableCompleteS35D1Cmp1 : indexScore (7/5) (controlPenalty savedCref uniformQuoteError unitRoleUnused .complete) favorableCompleteS35Before [.query 1] (.hydeRetriever 0) ≤ indexScore (7/5) (controlPenalty savedCref uniformQuoteError unitRoleUnused .complete) favorableCompleteS35Before [.query 1] (.hydeRetriever 1) := by
  rw [favorableCompleteS35D1I1,favorableCompleteS35D1I0]
  have h := index_weak_order_from_intervals ((3/2)/10) ((0/1)/8) 0 0 (1616307/2000000) (1129429/1250000)
    (treeBonus (7/5) 27 10) (treeBonus (7/5) 27 8)
    (trajectory_bonus_27_10).1 (trajectory_bonus_27_8).2 (by norm_num)
  simpa only [treeIndex,sub_zero] using h

theorem favorableCompleteS35D1Cmp2 : indexScore (7/5) (controlPenalty savedCref uniformQuoteError unitRoleUnused .complete) favorableCompleteS35Before [.query 1] (.hydeRetriever 2) ≤ indexScore (7/5) (controlPenalty savedCref uniformQuoteError unitRoleUnused .complete) favorableCompleteS35Before [.query 1] (.hydeRetriever 1) := by
  rw [favorableCompleteS35D1I2,favorableCompleteS35D1I0]
  have h := index_weak_order_from_intervals ((3/2)/10) ((0/1)/8) 0 0 (1616307/2000000) (1129429/1250000)
    (treeBonus (7/5) 27 10) (treeBonus (7/5) 27 8)
    (trajectory_bonus_27_10).1 (trajectory_bonus_27_8).2 (by norm_num)
  simpa only [treeIndex,sub_zero] using h

theorem favorableCompleteS35Choice1 : nativeFirstChoice (indexScore (7/5) (controlPenalty savedCref uniformQuoteError unitRoleUnused .complete) favorableCompleteS35Before [.query 1]) favorableCompleteS35Before [.query 1] = .hydeRetriever 1 := by
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
    · exact favorableCompleteS35D1Cmp1
    · exact favorableCompleteS35D1Cmp2

theorem favorableCompleteS35D2I0 : indexScore (7/5) (controlPenalty savedCref uniformQuoteError unitRoleUnused .complete) favorableCompleteS35Before [.query 1,.hydeRetriever 1] (.selection 1) = treeIndex ((0/1)/2) (7/5) 0 10 2 := by
  have hs : replayBackup favorableCompleteS35Before emptyStatistics ([.query 1,.hydeRetriever 1]++[.selection 1]) = ⟨2,(0/1)⟩ := by
    rw [replayBackup_empty_closed_form]
    simp +decide [backedEvents,favorableCompleteS35Before,favorableCompleteProposal,favorableCompleteEvent1,favorableCompleteEvent2,favorableCompleteEvent3,favorableCompleteEvent4,favorableCompleteEvent5,favorableCompleteEvent6,favorableCompleteEvent7,favorableCompleteEvent8,favorableCompleteEvent9,favorableCompleteEvent10,favorableCompleteEvent11,favorableCompleteEvent12,favorableCompleteEvent13,favorableCompleteEvent14,favorableCompleteEvent15,favorableCompleteEvent16,favorableCompleteEvent17,favorableCompleteEvent18,favorableCompleteEvent19,favorableCompleteEvent20,favorableCompleteEvent21,favorableCompleteEvent22,favorableCompleteEvent23,favorableCompleteEvent24,favorableCompleteEvent25,favorableCompleteEvent26,favorableCompleteEvent27,favorableCompleteEvent28,favorableCompleteEvent29,favorableCompleteEvent30,favorableCompleteEvent31,favorableCompleteEvent32,favorableCompleteEvent33,favorableCompleteEvent34,taskReward]
    <;> norm_num
  have hp : rawVisits favorableCompleteS35Before [.query 1,.hydeRetriever 1] = 10 := by decide
  have hn : rawVisits favorableCompleteS35Before ([.query 1,.hydeRetriever 1]++[.selection 1]) = 2 := by decide
  have hz : (controlPenalty savedCref uniformQuoteError unitRoleUnused .complete) favorableCompleteS35Before [.query 1,.hydeRetriever 1] (.selection 1) = 0 := by
    apply control_penalty_empty_of_prior_terminal .complete savedCref uniformQuoteError favorableCompleteS35Before [.query 1,.hydeRetriever 1] (.selection 1) 14 (by decide)
    · decide
    · decide
  unfold indexScore
  rw [hs,hp,hn,hz]
  simp only [BackupStat.mean]
  norm_num

theorem favorableCompleteS35D2I1 : indexScore (7/5) (controlPenalty savedCref uniformQuoteError unitRoleUnused .complete) favorableCompleteS35Before [.query 1,.hydeRetriever 1] (.selection 2) = treeIndex ((0/1)/2) (7/5) 0 10 2 := by
  have hs : replayBackup favorableCompleteS35Before emptyStatistics ([.query 1,.hydeRetriever 1]++[.selection 2]) = ⟨2,(0/1)⟩ := by
    rw [replayBackup_empty_closed_form]
    simp +decide [backedEvents,favorableCompleteS35Before,favorableCompleteProposal,favorableCompleteEvent1,favorableCompleteEvent2,favorableCompleteEvent3,favorableCompleteEvent4,favorableCompleteEvent5,favorableCompleteEvent6,favorableCompleteEvent7,favorableCompleteEvent8,favorableCompleteEvent9,favorableCompleteEvent10,favorableCompleteEvent11,favorableCompleteEvent12,favorableCompleteEvent13,favorableCompleteEvent14,favorableCompleteEvent15,favorableCompleteEvent16,favorableCompleteEvent17,favorableCompleteEvent18,favorableCompleteEvent19,favorableCompleteEvent20,favorableCompleteEvent21,favorableCompleteEvent22,favorableCompleteEvent23,favorableCompleteEvent24,favorableCompleteEvent25,favorableCompleteEvent26,favorableCompleteEvent27,favorableCompleteEvent28,favorableCompleteEvent29,favorableCompleteEvent30,favorableCompleteEvent31,favorableCompleteEvent32,favorableCompleteEvent33,favorableCompleteEvent34,taskReward]
    <;> norm_num
  have hp : rawVisits favorableCompleteS35Before [.query 1,.hydeRetriever 1] = 10 := by decide
  have hn : rawVisits favorableCompleteS35Before ([.query 1,.hydeRetriever 1]++[.selection 2]) = 2 := by decide
  have hz : (controlPenalty savedCref uniformQuoteError unitRoleUnused .complete) favorableCompleteS35Before [.query 1,.hydeRetriever 1] (.selection 2) = 0 := by
    apply control_penalty_empty_of_prior_terminal .complete savedCref uniformQuoteError favorableCompleteS35Before [.query 1,.hydeRetriever 1] (.selection 2) 15 (by decide)
    · decide
    · decide
  unfold indexScore
  rw [hs,hp,hn,hz]
  simp only [BackupStat.mean]
  norm_num

theorem favorableCompleteS35D2I2 : indexScore (7/5) (controlPenalty savedCref uniformQuoteError unitRoleUnused .complete) favorableCompleteS35Before [.query 1,.hydeRetriever 1] (.selection 3) = treeIndex ((0/1)/2) (7/5) 0 10 2 := by
  have hs : replayBackup favorableCompleteS35Before emptyStatistics ([.query 1,.hydeRetriever 1]++[.selection 3]) = ⟨2,(0/1)⟩ := by
    rw [replayBackup_empty_closed_form]
    simp +decide [backedEvents,favorableCompleteS35Before,favorableCompleteProposal,favorableCompleteEvent1,favorableCompleteEvent2,favorableCompleteEvent3,favorableCompleteEvent4,favorableCompleteEvent5,favorableCompleteEvent6,favorableCompleteEvent7,favorableCompleteEvent8,favorableCompleteEvent9,favorableCompleteEvent10,favorableCompleteEvent11,favorableCompleteEvent12,favorableCompleteEvent13,favorableCompleteEvent14,favorableCompleteEvent15,favorableCompleteEvent16,favorableCompleteEvent17,favorableCompleteEvent18,favorableCompleteEvent19,favorableCompleteEvent20,favorableCompleteEvent21,favorableCompleteEvent22,favorableCompleteEvent23,favorableCompleteEvent24,favorableCompleteEvent25,favorableCompleteEvent26,favorableCompleteEvent27,favorableCompleteEvent28,favorableCompleteEvent29,favorableCompleteEvent30,favorableCompleteEvent31,favorableCompleteEvent32,favorableCompleteEvent33,favorableCompleteEvent34,taskReward]
    <;> norm_num
  have hp : rawVisits favorableCompleteS35Before [.query 1,.hydeRetriever 1] = 10 := by decide
  have hn : rawVisits favorableCompleteS35Before ([.query 1,.hydeRetriever 1]++[.selection 3]) = 2 := by decide
  have hz : (controlPenalty savedCref uniformQuoteError unitRoleUnused .complete) favorableCompleteS35Before [.query 1,.hydeRetriever 1] (.selection 3) = 0 := by
    apply control_penalty_empty_of_prior_terminal .complete savedCref uniformQuoteError favorableCompleteS35Before [.query 1,.hydeRetriever 1] (.selection 3) 18 (by decide)
    · decide
    · decide
  unfold indexScore
  rw [hs,hp,hn,hz]
  simp only [BackupStat.mean]
  norm_num

theorem favorableCompleteS35D2I3 : indexScore (7/5) (controlPenalty savedCref uniformQuoteError unitRoleUnused .complete) favorableCompleteS35Before [.query 1,.hydeRetriever 1] (.selection 0) = treeIndex ((1/1)/3) (7/5) 0 10 3 := by
  have hs : replayBackup favorableCompleteS35Before emptyStatistics ([.query 1,.hydeRetriever 1]++[.selection 0]) = ⟨3,(1/1)⟩ := by
    rw [replayBackup_empty_closed_form]
    simp +decide [backedEvents,favorableCompleteS35Before,favorableCompleteProposal,favorableCompleteEvent1,favorableCompleteEvent2,favorableCompleteEvent3,favorableCompleteEvent4,favorableCompleteEvent5,favorableCompleteEvent6,favorableCompleteEvent7,favorableCompleteEvent8,favorableCompleteEvent9,favorableCompleteEvent10,favorableCompleteEvent11,favorableCompleteEvent12,favorableCompleteEvent13,favorableCompleteEvent14,favorableCompleteEvent15,favorableCompleteEvent16,favorableCompleteEvent17,favorableCompleteEvent18,favorableCompleteEvent19,favorableCompleteEvent20,favorableCompleteEvent21,favorableCompleteEvent22,favorableCompleteEvent23,favorableCompleteEvent24,favorableCompleteEvent25,favorableCompleteEvent26,favorableCompleteEvent27,favorableCompleteEvent28,favorableCompleteEvent29,favorableCompleteEvent30,favorableCompleteEvent31,favorableCompleteEvent32,favorableCompleteEvent33,favorableCompleteEvent34,taskReward]
    <;> norm_num
  have hp : rawVisits favorableCompleteS35Before [.query 1,.hydeRetriever 1] = 10 := by decide
  have hn : rawVisits favorableCompleteS35Before ([.query 1,.hydeRetriever 1]++[.selection 0]) = 3 := by decide
  have hz : (controlPenalty savedCref uniformQuoteError unitRoleUnused .complete) favorableCompleteS35Before [.query 1,.hydeRetriever 1] (.selection 0) = 0 := by
    apply control_penalty_empty_of_prior_terminal .complete savedCref uniformQuoteError favorableCompleteS35Before [.query 1,.hydeRetriever 1] (.selection 0) 8 (by decide)
    · decide
    · decide
  unfold indexScore
  rw [hs,hp,hn,hz]
  simp only [BackupStat.mean]
  norm_num

theorem favorableCompleteS35D2Cmp0 : indexScore (7/5) (controlPenalty savedCref uniformQuoteError unitRoleUnused .complete) favorableCompleteS35Before [.query 1,.hydeRetriever 1] (.selection 1) < indexScore (7/5) (controlPenalty savedCref uniformQuoteError unitRoleUnused .complete) favorableCompleteS35Before [.query 1,.hydeRetriever 1] (.selection 0) := by
  rw [favorableCompleteS35D2I0,favorableCompleteS35D2I3]
  have h := index_strict_order_from_intervals ((1/1)/3) ((0/1)/2) 0 0 (15645609/12500000) (76647529/50000000)
    (treeBonus (7/5) 10 3) (treeBonus (7/5) 10 2)
    (trajectory_bonus_10_3).1 (trajectory_bonus_10_2).2 (by norm_num)
  simpa only [treeIndex,sub_zero] using h

theorem favorableCompleteS35D2Cmp1 : indexScore (7/5) (controlPenalty savedCref uniformQuoteError unitRoleUnused .complete) favorableCompleteS35Before [.query 1,.hydeRetriever 1] (.selection 2) < indexScore (7/5) (controlPenalty savedCref uniformQuoteError unitRoleUnused .complete) favorableCompleteS35Before [.query 1,.hydeRetriever 1] (.selection 0) := by
  rw [favorableCompleteS35D2I1,favorableCompleteS35D2I3]
  have h := index_strict_order_from_intervals ((1/1)/3) ((0/1)/2) 0 0 (15645609/12500000) (76647529/50000000)
    (treeBonus (7/5) 10 3) (treeBonus (7/5) 10 2)
    (trajectory_bonus_10_3).1 (trajectory_bonus_10_2).2 (by norm_num)
  simpa only [treeIndex,sub_zero] using h

theorem favorableCompleteS35D2Cmp2 : indexScore (7/5) (controlPenalty savedCref uniformQuoteError unitRoleUnused .complete) favorableCompleteS35Before [.query 1,.hydeRetriever 1] (.selection 3) < indexScore (7/5) (controlPenalty savedCref uniformQuoteError unitRoleUnused .complete) favorableCompleteS35Before [.query 1,.hydeRetriever 1] (.selection 0) := by
  rw [favorableCompleteS35D2I2,favorableCompleteS35D2I3]
  have h := index_strict_order_from_intervals ((1/1)/3) ((0/1)/2) 0 0 (15645609/12500000) (76647529/50000000)
    (treeBonus (7/5) 10 3) (treeBonus (7/5) 10 2)
    (trajectory_bonus_10_3).1 (trajectory_bonus_10_2).2 (by norm_num)
  simpa only [treeIndex,sub_zero] using h

theorem favorableCompleteS35Choice2 : nativeFirstChoice (indexScore (7/5) (controlPenalty savedCref uniformQuoteError unitRoleUnused .complete) favorableCompleteS35Before [.query 1,.hydeRetriever 1]) favorableCompleteS35Before [.query 1,.hydeRetriever 1] = .selection 0 := by
  apply visited_choice_from_ordered_certificate _ _ [.query 1,.hydeRetriever 1] [.selection 1,.selection 2,.selection 3] [] (.selection 0) (by decide)
  · intro a ha
    have ho : orderedLegalAvailable [.query 1,.hydeRetriever 1] = [.selection 1,.selection 2,.selection 3,.selection 0] := by decide
    rw [ho] at ha
    simp only [List.mem_cons,List.not_mem_nil,or_false] at ha
    rcases ha with rfl | rfl | rfl | rfl <;> decide
  · intro a ha
    simp only [List.mem_cons,List.not_mem_nil,or_false] at ha
    rcases ha with rfl | rfl | rfl
    · exact favorableCompleteS35D2Cmp0
    · exact favorableCompleteS35D2Cmp1
    · exact favorableCompleteS35D2Cmp2
  · simp

theorem favorableCompleteS35ActualEvent : nativeEvent budgetTape (7/5) (controlPenalty savedCref uniformQuoteError unitRoleUnused .complete)
    (taskReward false (2/5) (1/2)) favorableCompleteS35Before = favorableCompleteEvent35 := by
  have hs0 := native_select_existing_step budgetTape (7/5) (controlPenalty savedCref uniformQuoteError unitRoleUnused .complete) favorableCompleteS35Before 8 [] (.query 1)
    (by decide) (by decide) favorableCompleteS35Choice0
  have hs1 := native_select_existing_step budgetTape (7/5) (controlPenalty savedCref uniformQuoteError unitRoleUnused .complete) favorableCompleteS35Before 7 [.query 1] (.hydeRetriever 1)
    (by decide) (by decide) favorableCompleteS35Choice1
  have hs2 := native_select_existing_step budgetTape (7/5) (controlPenalty savedCref uniformQuoteError unitRoleUnused .complete) favorableCompleteS35Before 6 [.query 1,.hydeRetriever 1] (.selection 0)
    (by decide) (by decide) favorableCompleteS35Choice2
  have hnew := native_select_new_step budgetTape (7/5) (controlPenalty savedCref uniformQuoteError unitRoleUnused .complete) favorableCompleteS35Before 5 [.query 1,.hydeRetriever 1,.selection 0]
    [.width 0,.width 2] (.width 0) (by decide) (by decide) (by decide) (by decide)
  have hs : nativeSelect budgetTape (7/5) (controlPenalty savedCref uniformQuoteError unitRoleUnused .complete) favorableCompleteS35Before 9 [] = [.query 1,.hydeRetriever 1,.selection 0,.width 0] := by
    rw [hs0]
    change nativeSelect budgetTape (7/5) (controlPenalty savedCref uniformQuoteError unitRoleUnused .complete) favorableCompleteS35Before 8 [.query 1] = _
    rw [hs1]
    change nativeSelect budgetTape (7/5) (controlPenalty savedCref uniformQuoteError unitRoleUnused .complete) favorableCompleteS35Before 7 [.query 1,.hydeRetriever 1] = _
    rw [hs2]
    change nativeSelect budgetTape (7/5) (controlPenalty savedCref uniformQuoteError unitRoleUnused .complete) favorableCompleteS35Before 6 [.query 1,.hydeRetriever 1,.selection 0] = _
    rw [hnew] <;> rfl
  have hr : repairedRollout budgetTape favorableCompleteS35Before 9 [.query 1,.hydeRetriever 1,.selection 0,.width 0] = [.query 1,.hydeRetriever 1,.selection 0,.width 0,.stop,.reranker 0,.topm 0,.context 0,.answer 0] := by decide
  simp only [nativeEvent,hs,hr]
  rfl

end AgentUCT32MConcrete
