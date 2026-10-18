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

def favorableCompleteS20Before := favorableCompleteProposal.take 19

theorem favorableCompleteS20Choice0 : nativeFirstChoice (indexScore (7/5) (controlPenalty savedCref uniformQuoteError unitRoleUnused .complete) favorableCompleteS20Before []) favorableCompleteS20Before [] = .query 1 := by
  apply complete_root_from_physical_gap favorableCompleteS20Before (favorableComplete_prefix_rewards 19) (by decide)
  · intro q; fin_cases q <;> decide
  · decide
  · intro q hq
    exact AgentUCTNextExact.favorable_complete_normal_root_physical_quote_exact 19 (by omega) q hq

theorem favorableCompleteS20D1I0 : indexScore (7/5) (controlPenalty savedCref uniformQuoteError unitRoleUnused .complete) favorableCompleteS20Before [.query 1] (.hydeRetriever 1) = treeIndex ((1/1)/5) (7/5) 0 12 5 := by
  have hs : replayBackup favorableCompleteS20Before emptyStatistics ([.query 1]++[.hydeRetriever 1]) = ⟨5,(1/1)⟩ := by
    rw [replayBackup_empty_closed_form]
    simp +decide [backedEvents,favorableCompleteS20Before,favorableCompleteProposal,favorableCompleteEvent1,favorableCompleteEvent2,favorableCompleteEvent3,favorableCompleteEvent4,favorableCompleteEvent5,favorableCompleteEvent6,favorableCompleteEvent7,favorableCompleteEvent8,favorableCompleteEvent9,favorableCompleteEvent10,favorableCompleteEvent11,favorableCompleteEvent12,favorableCompleteEvent13,favorableCompleteEvent14,favorableCompleteEvent15,favorableCompleteEvent16,favorableCompleteEvent17,favorableCompleteEvent18,favorableCompleteEvent19,taskReward]
    <;> norm_num
  have hp : rawVisits favorableCompleteS20Before [.query 1] = 12 := by decide
  have hn : rawVisits favorableCompleteS20Before ([.query 1]++[.hydeRetriever 1]) = 5 := by decide
  have hz : (controlPenalty savedCref uniformQuoteError unitRoleUnused .complete) favorableCompleteS20Before [.query 1] (.hydeRetriever 1) = 0 := by
    apply control_penalty_empty_of_prior_terminal .complete savedCref uniformQuoteError favorableCompleteS20Before [.query 1] (.hydeRetriever 1) 8 (by decide)
    · decide
    · decide
  unfold indexScore
  rw [hs,hp,hn,hz]
  simp only [BackupStat.mean]
  norm_num

theorem favorableCompleteS20D1I1 : indexScore (7/5) (controlPenalty savedCref uniformQuoteError unitRoleUnused .complete) favorableCompleteS20Before [.query 1] (.hydeRetriever 0) = treeIndex ((0/1)/3) (7/5) 0 12 3 := by
  have hs : replayBackup favorableCompleteS20Before emptyStatistics ([.query 1]++[.hydeRetriever 0]) = ⟨3,(0/1)⟩ := by
    rw [replayBackup_empty_closed_form]
    simp +decide [backedEvents,favorableCompleteS20Before,favorableCompleteProposal,favorableCompleteEvent1,favorableCompleteEvent2,favorableCompleteEvent3,favorableCompleteEvent4,favorableCompleteEvent5,favorableCompleteEvent6,favorableCompleteEvent7,favorableCompleteEvent8,favorableCompleteEvent9,favorableCompleteEvent10,favorableCompleteEvent11,favorableCompleteEvent12,favorableCompleteEvent13,favorableCompleteEvent14,favorableCompleteEvent15,favorableCompleteEvent16,favorableCompleteEvent17,favorableCompleteEvent18,favorableCompleteEvent19,taskReward]
    <;> norm_num
  have hp : rawVisits favorableCompleteS20Before [.query 1] = 12 := by decide
  have hn : rawVisits favorableCompleteS20Before ([.query 1]++[.hydeRetriever 0]) = 3 := by decide
  have hz : (controlPenalty savedCref uniformQuoteError unitRoleUnused .complete) favorableCompleteS20Before [.query 1] (.hydeRetriever 0) = 0 := by
    apply control_penalty_empty_of_prior_terminal .complete savedCref uniformQuoteError favorableCompleteS20Before [.query 1] (.hydeRetriever 0) 1 (by decide)
    · decide
    · decide
  unfold indexScore
  rw [hs,hp,hn,hz]
  simp only [BackupStat.mean]
  norm_num

theorem favorableCompleteS20D1I2 : indexScore (7/5) (controlPenalty savedCref uniformQuoteError unitRoleUnused .complete) favorableCompleteS20Before [.query 1] (.hydeRetriever 2) = treeIndex ((0/1)/3) (7/5) 0 12 3 := by
  have hs : replayBackup favorableCompleteS20Before emptyStatistics ([.query 1]++[.hydeRetriever 2]) = ⟨3,(0/1)⟩ := by
    rw [replayBackup_empty_closed_form]
    simp +decide [backedEvents,favorableCompleteS20Before,favorableCompleteProposal,favorableCompleteEvent1,favorableCompleteEvent2,favorableCompleteEvent3,favorableCompleteEvent4,favorableCompleteEvent5,favorableCompleteEvent6,favorableCompleteEvent7,favorableCompleteEvent8,favorableCompleteEvent9,favorableCompleteEvent10,favorableCompleteEvent11,favorableCompleteEvent12,favorableCompleteEvent13,favorableCompleteEvent14,favorableCompleteEvent15,favorableCompleteEvent16,favorableCompleteEvent17,favorableCompleteEvent18,favorableCompleteEvent19,taskReward]
    <;> norm_num
  have hp : rawVisits favorableCompleteS20Before [.query 1] = 12 := by decide
  have hn : rawVisits favorableCompleteS20Before ([.query 1]++[.hydeRetriever 2]) = 3 := by decide
  have hz : (controlPenalty savedCref uniformQuoteError unitRoleUnused .complete) favorableCompleteS20Before [.query 1] (.hydeRetriever 2) = 0 := by
    apply control_penalty_empty_of_prior_terminal .complete savedCref uniformQuoteError favorableCompleteS20Before [.query 1] (.hydeRetriever 2) 10 (by decide)
    · decide
    · decide
  unfold indexScore
  rw [hs,hp,hn,hz]
  simp only [BackupStat.mean]
  norm_num

theorem favorableCompleteS20D1Cmp0 : indexScore (7/5) (controlPenalty savedCref uniformQuoteError unitRoleUnused .complete) favorableCompleteS20Before [.query 1] (.hydeRetriever 1) < indexScore (7/5) (controlPenalty savedCref uniformQuoteError unitRoleUnused .complete) favorableCompleteS20Before [.query 1] (.hydeRetriever 0) := by
  rw [favorableCompleteS20D1I0,favorableCompleteS20D1I1]
  have h := index_strict_order_from_intervals ((0/1)/3) ((1/1)/5) 0 0 (64725703/50000000) (12534081/12500000)
    (treeBonus (7/5) 12 3) (treeBonus (7/5) 12 5)
    (trajectory_bonus_12_3).1 (trajectory_bonus_12_5).2 (by norm_num)
  simpa only [treeIndex,sub_zero] using h

theorem favorableCompleteS20D1Cmp2 : indexScore (7/5) (controlPenalty savedCref uniformQuoteError unitRoleUnused .complete) favorableCompleteS20Before [.query 1] (.hydeRetriever 2) ≤ indexScore (7/5) (controlPenalty savedCref uniformQuoteError unitRoleUnused .complete) favorableCompleteS20Before [.query 1] (.hydeRetriever 0) := by
  rw [favorableCompleteS20D1I2,favorableCompleteS20D1I1]

theorem favorableCompleteS20Choice1 : nativeFirstChoice (indexScore (7/5) (controlPenalty savedCref uniformQuoteError unitRoleUnused .complete) favorableCompleteS20Before [.query 1]) favorableCompleteS20Before [.query 1] = .hydeRetriever 0 := by
  apply visited_choice_from_ordered_certificate _ _ [.query 1] [.hydeRetriever 1] [.hydeRetriever 2] (.hydeRetriever 0) (by decide)
  · intro a ha
    have ho : orderedLegalAvailable [.query 1] = [.hydeRetriever 1,.hydeRetriever 0,.hydeRetriever 2] := by decide
    rw [ho] at ha
    simp only [List.mem_cons,List.not_mem_nil,or_false] at ha
    rcases ha with rfl | rfl | rfl <;> decide
  · intro a ha
    simp only [List.mem_cons,List.not_mem_nil,or_false] at ha
    rcases ha with rfl
    · exact favorableCompleteS20D1Cmp0
  · intro a ha
    simp only [List.mem_cons,List.not_mem_nil,or_false] at ha
    rcases ha with rfl
    · exact favorableCompleteS20D1Cmp2

theorem favorableCompleteS20ActualEvent : nativeEvent budgetTape (7/5) (controlPenalty savedCref uniformQuoteError unitRoleUnused .complete)
    (taskReward false (2/5) (1/2)) favorableCompleteS20Before = favorableCompleteEvent20 := by
  have hs0 := native_select_existing_step budgetTape (7/5) (controlPenalty savedCref uniformQuoteError unitRoleUnused .complete) favorableCompleteS20Before 8 [] (.query 1)
    (by decide) (by decide) favorableCompleteS20Choice0
  have hs1 := native_select_existing_step budgetTape (7/5) (controlPenalty savedCref uniformQuoteError unitRoleUnused .complete) favorableCompleteS20Before 7 [.query 1] (.hydeRetriever 0)
    (by decide) (by decide) favorableCompleteS20Choice1
  have hnew := native_select_new_step budgetTape (7/5) (controlPenalty savedCref uniformQuoteError unitRoleUnused .complete) favorableCompleteS20Before 6 [.query 1,.hydeRetriever 0]
    [.selection 2,.selection 3] (.selection 2) (by decide) (by decide) (by decide) (by decide)
  have hs : nativeSelect budgetTape (7/5) (controlPenalty savedCref uniformQuoteError unitRoleUnused .complete) favorableCompleteS20Before 9 [] = [.query 1,.hydeRetriever 0,.selection 2] := by
    rw [hs0]
    change nativeSelect budgetTape (7/5) (controlPenalty savedCref uniformQuoteError unitRoleUnused .complete) favorableCompleteS20Before 8 [.query 1] = _
    rw [hs1]
    change nativeSelect budgetTape (7/5) (controlPenalty savedCref uniformQuoteError unitRoleUnused .complete) favorableCompleteS20Before 7 [.query 1,.hydeRetriever 0] = _
    rw [hnew] <;> rfl
  have hr : repairedRollout budgetTape favorableCompleteS20Before 9 [.query 1,.hydeRetriever 0,.selection 2] = [.query 1,.hydeRetriever 0,.selection 2,.width 0,.stop,.reranker 0,.topm 0,.context 0,.answer 0] := by decide
  simp only [nativeEvent,hs,hr]
  rfl

def favorableCompleteS21Before := favorableCompleteProposal.take 20

theorem favorableCompleteS21Choice0 : nativeFirstChoice (indexScore (7/5) (controlPenalty savedCref uniformQuoteError unitRoleUnused .complete) favorableCompleteS21Before []) favorableCompleteS21Before [] = .query 1 := by
  apply complete_root_from_physical_gap favorableCompleteS21Before (favorableComplete_prefix_rewards 20) (by decide)
  · intro q; fin_cases q <;> decide
  · decide
  · intro q hq
    exact AgentUCTNextExact.favorable_complete_normal_root_physical_quote_exact 20 (by omega) q hq

theorem favorableCompleteS21D1I0 : indexScore (7/5) (controlPenalty savedCref uniformQuoteError unitRoleUnused .complete) favorableCompleteS21Before [.query 1] (.hydeRetriever 1) = treeIndex ((1/1)/5) (7/5) 0 13 5 := by
  have hs : replayBackup favorableCompleteS21Before emptyStatistics ([.query 1]++[.hydeRetriever 1]) = ⟨5,(1/1)⟩ := by
    rw [replayBackup_empty_closed_form]
    simp +decide [backedEvents,favorableCompleteS21Before,favorableCompleteProposal,favorableCompleteEvent1,favorableCompleteEvent2,favorableCompleteEvent3,favorableCompleteEvent4,favorableCompleteEvent5,favorableCompleteEvent6,favorableCompleteEvent7,favorableCompleteEvent8,favorableCompleteEvent9,favorableCompleteEvent10,favorableCompleteEvent11,favorableCompleteEvent12,favorableCompleteEvent13,favorableCompleteEvent14,favorableCompleteEvent15,favorableCompleteEvent16,favorableCompleteEvent17,favorableCompleteEvent18,favorableCompleteEvent19,favorableCompleteEvent20,taskReward]
    <;> norm_num
  have hp : rawVisits favorableCompleteS21Before [.query 1] = 13 := by decide
  have hn : rawVisits favorableCompleteS21Before ([.query 1]++[.hydeRetriever 1]) = 5 := by decide
  have hz : (controlPenalty savedCref uniformQuoteError unitRoleUnused .complete) favorableCompleteS21Before [.query 1] (.hydeRetriever 1) = 0 := by
    apply control_penalty_empty_of_prior_terminal .complete savedCref uniformQuoteError favorableCompleteS21Before [.query 1] (.hydeRetriever 1) 8 (by decide)
    · decide
    · decide
  unfold indexScore
  rw [hs,hp,hn,hz]
  simp only [BackupStat.mean]
  norm_num

theorem favorableCompleteS21D1I1 : indexScore (7/5) (controlPenalty savedCref uniformQuoteError unitRoleUnused .complete) favorableCompleteS21Before [.query 1] (.hydeRetriever 0) = treeIndex ((0/1)/4) (7/5) 0 13 4 := by
  have hs : replayBackup favorableCompleteS21Before emptyStatistics ([.query 1]++[.hydeRetriever 0]) = ⟨4,(0/1)⟩ := by
    rw [replayBackup_empty_closed_form]
    simp +decide [backedEvents,favorableCompleteS21Before,favorableCompleteProposal,favorableCompleteEvent1,favorableCompleteEvent2,favorableCompleteEvent3,favorableCompleteEvent4,favorableCompleteEvent5,favorableCompleteEvent6,favorableCompleteEvent7,favorableCompleteEvent8,favorableCompleteEvent9,favorableCompleteEvent10,favorableCompleteEvent11,favorableCompleteEvent12,favorableCompleteEvent13,favorableCompleteEvent14,favorableCompleteEvent15,favorableCompleteEvent16,favorableCompleteEvent17,favorableCompleteEvent18,favorableCompleteEvent19,favorableCompleteEvent20,taskReward]
    <;> norm_num
  have hp : rawVisits favorableCompleteS21Before [.query 1] = 13 := by decide
  have hn : rawVisits favorableCompleteS21Before ([.query 1]++[.hydeRetriever 0]) = 4 := by decide
  have hz : (controlPenalty savedCref uniformQuoteError unitRoleUnused .complete) favorableCompleteS21Before [.query 1] (.hydeRetriever 0) = 0 := by
    apply control_penalty_empty_of_prior_terminal .complete savedCref uniformQuoteError favorableCompleteS21Before [.query 1] (.hydeRetriever 0) 1 (by decide)
    · decide
    · decide
  unfold indexScore
  rw [hs,hp,hn,hz]
  simp only [BackupStat.mean]
  norm_num

theorem favorableCompleteS21D1I2 : indexScore (7/5) (controlPenalty savedCref uniformQuoteError unitRoleUnused .complete) favorableCompleteS21Before [.query 1] (.hydeRetriever 2) = treeIndex ((0/1)/3) (7/5) 0 13 3 := by
  have hs : replayBackup favorableCompleteS21Before emptyStatistics ([.query 1]++[.hydeRetriever 2]) = ⟨3,(0/1)⟩ := by
    rw [replayBackup_empty_closed_form]
    simp +decide [backedEvents,favorableCompleteS21Before,favorableCompleteProposal,favorableCompleteEvent1,favorableCompleteEvent2,favorableCompleteEvent3,favorableCompleteEvent4,favorableCompleteEvent5,favorableCompleteEvent6,favorableCompleteEvent7,favorableCompleteEvent8,favorableCompleteEvent9,favorableCompleteEvent10,favorableCompleteEvent11,favorableCompleteEvent12,favorableCompleteEvent13,favorableCompleteEvent14,favorableCompleteEvent15,favorableCompleteEvent16,favorableCompleteEvent17,favorableCompleteEvent18,favorableCompleteEvent19,favorableCompleteEvent20,taskReward]
    <;> norm_num
  have hp : rawVisits favorableCompleteS21Before [.query 1] = 13 := by decide
  have hn : rawVisits favorableCompleteS21Before ([.query 1]++[.hydeRetriever 2]) = 3 := by decide
  have hz : (controlPenalty savedCref uniformQuoteError unitRoleUnused .complete) favorableCompleteS21Before [.query 1] (.hydeRetriever 2) = 0 := by
    apply control_penalty_empty_of_prior_terminal .complete savedCref uniformQuoteError favorableCompleteS21Before [.query 1] (.hydeRetriever 2) 10 (by decide)
    · decide
    · decide
  unfold indexScore
  rw [hs,hp,hn,hz]
  simp only [BackupStat.mean]
  norm_num

theorem favorableCompleteS21D1Cmp0 : indexScore (7/5) (controlPenalty savedCref uniformQuoteError unitRoleUnused .complete) favorableCompleteS21Before [.query 1] (.hydeRetriever 1) < indexScore (7/5) (controlPenalty savedCref uniformQuoteError unitRoleUnused .complete) favorableCompleteS21Before [.query 1] (.hydeRetriever 2) := by
  rw [favorableCompleteS21D1I0,favorableCompleteS21D1I2]
  have h := index_strict_order_from_intervals ((0/1)/3) ((1/1)/5) 0 0 (16413523/12500000) (6356931/6250000)
    (treeBonus (7/5) 13 3) (treeBonus (7/5) 13 5)
    (trajectory_bonus_13_3).1 (trajectory_bonus_13_5).2 (by norm_num)
  simpa only [treeIndex,sub_zero] using h

theorem favorableCompleteS21D1Cmp1 : indexScore (7/5) (controlPenalty savedCref uniformQuoteError unitRoleUnused .complete) favorableCompleteS21Before [.query 1] (.hydeRetriever 0) < indexScore (7/5) (controlPenalty savedCref uniformQuoteError unitRoleUnused .complete) favorableCompleteS21Before [.query 1] (.hydeRetriever 2) := by
  rw [favorableCompleteS21D1I1,favorableCompleteS21D1I2]
  have h := index_strict_order_from_intervals ((0/1)/3) ((0/1)/4) 0 0 (16413523/12500000) (14214529/12500000)
    (treeBonus (7/5) 13 3) (treeBonus (7/5) 13 4)
    (trajectory_bonus_13_3).1 (trajectory_bonus_13_4).2 (by norm_num)
  simpa only [treeIndex,sub_zero] using h

theorem favorableCompleteS21Choice1 : nativeFirstChoice (indexScore (7/5) (controlPenalty savedCref uniformQuoteError unitRoleUnused .complete) favorableCompleteS21Before [.query 1]) favorableCompleteS21Before [.query 1] = .hydeRetriever 2 := by
  apply visited_choice_from_ordered_certificate _ _ [.query 1] [.hydeRetriever 1,.hydeRetriever 0] [] (.hydeRetriever 2) (by decide)
  · intro a ha
    have ho : orderedLegalAvailable [.query 1] = [.hydeRetriever 1,.hydeRetriever 0,.hydeRetriever 2] := by decide
    rw [ho] at ha
    simp only [List.mem_cons,List.not_mem_nil,or_false] at ha
    rcases ha with rfl | rfl | rfl <;> decide
  · intro a ha
    simp only [List.mem_cons,List.not_mem_nil,or_false] at ha
    rcases ha with rfl | rfl
    · exact favorableCompleteS21D1Cmp0
    · exact favorableCompleteS21D1Cmp1
  · simp

theorem favorableCompleteS21ActualEvent : nativeEvent budgetTape (7/5) (controlPenalty savedCref uniformQuoteError unitRoleUnused .complete)
    (taskReward false (2/5) (1/2)) favorableCompleteS21Before = favorableCompleteEvent21 := by
  have hs0 := native_select_existing_step budgetTape (7/5) (controlPenalty savedCref uniformQuoteError unitRoleUnused .complete) favorableCompleteS21Before 8 [] (.query 1)
    (by decide) (by decide) favorableCompleteS21Choice0
  have hs1 := native_select_existing_step budgetTape (7/5) (controlPenalty savedCref uniformQuoteError unitRoleUnused .complete) favorableCompleteS21Before 7 [.query 1] (.hydeRetriever 2)
    (by decide) (by decide) favorableCompleteS21Choice1
  have hnew := native_select_new_step budgetTape (7/5) (controlPenalty savedCref uniformQuoteError unitRoleUnused .complete) favorableCompleteS21Before 6 [.query 1,.hydeRetriever 2]
    [.selection 2,.selection 3] (.selection 2) (by decide) (by decide) (by decide) (by decide)
  have hs : nativeSelect budgetTape (7/5) (controlPenalty savedCref uniformQuoteError unitRoleUnused .complete) favorableCompleteS21Before 9 [] = [.query 1,.hydeRetriever 2,.selection 2] := by
    rw [hs0]
    change nativeSelect budgetTape (7/5) (controlPenalty savedCref uniformQuoteError unitRoleUnused .complete) favorableCompleteS21Before 8 [.query 1] = _
    rw [hs1]
    change nativeSelect budgetTape (7/5) (controlPenalty savedCref uniformQuoteError unitRoleUnused .complete) favorableCompleteS21Before 7 [.query 1,.hydeRetriever 2] = _
    rw [hnew] <;> rfl
  have hr : repairedRollout budgetTape favorableCompleteS21Before 9 [.query 1,.hydeRetriever 2,.selection 2] = [.query 1,.hydeRetriever 2,.selection 2,.width 0,.stop,.reranker 0,.topm 0,.context 0,.answer 0] := by decide
  simp only [nativeEvent,hs,hr]
  rfl

def favorableCompleteS22Before := favorableCompleteProposal.take 21

theorem favorableCompleteS22Choice0 : nativeFirstChoice (indexScore (7/5) (controlPenalty savedCref uniformQuoteError unitRoleUnused .complete) favorableCompleteS22Before []) favorableCompleteS22Before [] = .query 1 := by
  apply complete_root_from_physical_gap favorableCompleteS22Before (favorableComplete_prefix_rewards 21) (by decide)
  · intro q; fin_cases q <;> decide
  · decide
  · intro q hq
    exact AgentUCTNextExact.favorable_complete_normal_root_physical_quote_exact 21 (by omega) q hq

theorem favorableCompleteS22D1I0 : indexScore (7/5) (controlPenalty savedCref uniformQuoteError unitRoleUnused .complete) favorableCompleteS22Before [.query 1] (.hydeRetriever 1) = treeIndex ((1/1)/5) (7/5) 0 14 5 := by
  have hs : replayBackup favorableCompleteS22Before emptyStatistics ([.query 1]++[.hydeRetriever 1]) = ⟨5,(1/1)⟩ := by
    rw [replayBackup_empty_closed_form]
    simp +decide [backedEvents,favorableCompleteS22Before,favorableCompleteProposal,favorableCompleteEvent1,favorableCompleteEvent2,favorableCompleteEvent3,favorableCompleteEvent4,favorableCompleteEvent5,favorableCompleteEvent6,favorableCompleteEvent7,favorableCompleteEvent8,favorableCompleteEvent9,favorableCompleteEvent10,favorableCompleteEvent11,favorableCompleteEvent12,favorableCompleteEvent13,favorableCompleteEvent14,favorableCompleteEvent15,favorableCompleteEvent16,favorableCompleteEvent17,favorableCompleteEvent18,favorableCompleteEvent19,favorableCompleteEvent20,favorableCompleteEvent21,taskReward]
    <;> norm_num
  have hp : rawVisits favorableCompleteS22Before [.query 1] = 14 := by decide
  have hn : rawVisits favorableCompleteS22Before ([.query 1]++[.hydeRetriever 1]) = 5 := by decide
  have hz : (controlPenalty savedCref uniformQuoteError unitRoleUnused .complete) favorableCompleteS22Before [.query 1] (.hydeRetriever 1) = 0 := by
    apply control_penalty_empty_of_prior_terminal .complete savedCref uniformQuoteError favorableCompleteS22Before [.query 1] (.hydeRetriever 1) 8 (by decide)
    · decide
    · decide
  unfold indexScore
  rw [hs,hp,hn,hz]
  simp only [BackupStat.mean]
  norm_num

theorem favorableCompleteS22D1I1 : indexScore (7/5) (controlPenalty savedCref uniformQuoteError unitRoleUnused .complete) favorableCompleteS22Before [.query 1] (.hydeRetriever 0) = treeIndex ((0/1)/4) (7/5) 0 14 4 := by
  have hs : replayBackup favorableCompleteS22Before emptyStatistics ([.query 1]++[.hydeRetriever 0]) = ⟨4,(0/1)⟩ := by
    rw [replayBackup_empty_closed_form]
    simp +decide [backedEvents,favorableCompleteS22Before,favorableCompleteProposal,favorableCompleteEvent1,favorableCompleteEvent2,favorableCompleteEvent3,favorableCompleteEvent4,favorableCompleteEvent5,favorableCompleteEvent6,favorableCompleteEvent7,favorableCompleteEvent8,favorableCompleteEvent9,favorableCompleteEvent10,favorableCompleteEvent11,favorableCompleteEvent12,favorableCompleteEvent13,favorableCompleteEvent14,favorableCompleteEvent15,favorableCompleteEvent16,favorableCompleteEvent17,favorableCompleteEvent18,favorableCompleteEvent19,favorableCompleteEvent20,favorableCompleteEvent21,taskReward]
    <;> norm_num
  have hp : rawVisits favorableCompleteS22Before [.query 1] = 14 := by decide
  have hn : rawVisits favorableCompleteS22Before ([.query 1]++[.hydeRetriever 0]) = 4 := by decide
  have hz : (controlPenalty savedCref uniformQuoteError unitRoleUnused .complete) favorableCompleteS22Before [.query 1] (.hydeRetriever 0) = 0 := by
    apply control_penalty_empty_of_prior_terminal .complete savedCref uniformQuoteError favorableCompleteS22Before [.query 1] (.hydeRetriever 0) 1 (by decide)
    · decide
    · decide
  unfold indexScore
  rw [hs,hp,hn,hz]
  simp only [BackupStat.mean]
  norm_num

theorem favorableCompleteS22D1I2 : indexScore (7/5) (controlPenalty savedCref uniformQuoteError unitRoleUnused .complete) favorableCompleteS22Before [.query 1] (.hydeRetriever 2) = treeIndex ((0/1)/4) (7/5) 0 14 4 := by
  have hs : replayBackup favorableCompleteS22Before emptyStatistics ([.query 1]++[.hydeRetriever 2]) = ⟨4,(0/1)⟩ := by
    rw [replayBackup_empty_closed_form]
    simp +decide [backedEvents,favorableCompleteS22Before,favorableCompleteProposal,favorableCompleteEvent1,favorableCompleteEvent2,favorableCompleteEvent3,favorableCompleteEvent4,favorableCompleteEvent5,favorableCompleteEvent6,favorableCompleteEvent7,favorableCompleteEvent8,favorableCompleteEvent9,favorableCompleteEvent10,favorableCompleteEvent11,favorableCompleteEvent12,favorableCompleteEvent13,favorableCompleteEvent14,favorableCompleteEvent15,favorableCompleteEvent16,favorableCompleteEvent17,favorableCompleteEvent18,favorableCompleteEvent19,favorableCompleteEvent20,favorableCompleteEvent21,taskReward]
    <;> norm_num
  have hp : rawVisits favorableCompleteS22Before [.query 1] = 14 := by decide
  have hn : rawVisits favorableCompleteS22Before ([.query 1]++[.hydeRetriever 2]) = 4 := by decide
  have hz : (controlPenalty savedCref uniformQuoteError unitRoleUnused .complete) favorableCompleteS22Before [.query 1] (.hydeRetriever 2) = 0 := by
    apply control_penalty_empty_of_prior_terminal .complete savedCref uniformQuoteError favorableCompleteS22Before [.query 1] (.hydeRetriever 2) 10 (by decide)
    · decide
    · decide
  unfold indexScore
  rw [hs,hp,hn,hz]
  simp only [BackupStat.mean]
  norm_num

theorem favorableCompleteS22D1Cmp1 : indexScore (7/5) (controlPenalty savedCref uniformQuoteError unitRoleUnused .complete) favorableCompleteS22Before [.query 1] (.hydeRetriever 0) ≤ indexScore (7/5) (controlPenalty savedCref uniformQuoteError unitRoleUnused .complete) favorableCompleteS22Before [.query 1] (.hydeRetriever 1) := by
  rw [favorableCompleteS22D1I1,favorableCompleteS22D1I0]
  have h := index_weak_order_from_intervals ((1/1)/5) ((0/1)/4) 0 0 (6439489/6250000) (28798273/25000000)
    (treeBonus (7/5) 14 5) (treeBonus (7/5) 14 4)
    (trajectory_bonus_14_5).1 (trajectory_bonus_14_4).2 (by norm_num)
  simpa only [treeIndex,sub_zero] using h

theorem favorableCompleteS22D1Cmp2 : indexScore (7/5) (controlPenalty savedCref uniformQuoteError unitRoleUnused .complete) favorableCompleteS22Before [.query 1] (.hydeRetriever 2) ≤ indexScore (7/5) (controlPenalty savedCref uniformQuoteError unitRoleUnused .complete) favorableCompleteS22Before [.query 1] (.hydeRetriever 1) := by
  rw [favorableCompleteS22D1I2,favorableCompleteS22D1I0]
  have h := index_weak_order_from_intervals ((1/1)/5) ((0/1)/4) 0 0 (6439489/6250000) (28798273/25000000)
    (treeBonus (7/5) 14 5) (treeBonus (7/5) 14 4)
    (trajectory_bonus_14_5).1 (trajectory_bonus_14_4).2 (by norm_num)
  simpa only [treeIndex,sub_zero] using h

theorem favorableCompleteS22Choice1 : nativeFirstChoice (indexScore (7/5) (controlPenalty savedCref uniformQuoteError unitRoleUnused .complete) favorableCompleteS22Before [.query 1]) favorableCompleteS22Before [.query 1] = .hydeRetriever 1 := by
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
    · exact favorableCompleteS22D1Cmp1
    · exact favorableCompleteS22D1Cmp2

theorem favorableCompleteS22D2I0 : indexScore (7/5) (controlPenalty savedCref uniformQuoteError unitRoleUnused .complete) favorableCompleteS22Before [.query 1,.hydeRetriever 1] (.selection 1) = treeIndex ((0/1)/1) (7/5) 0 5 1 := by
  have hs : replayBackup favorableCompleteS22Before emptyStatistics ([.query 1,.hydeRetriever 1]++[.selection 1]) = ⟨1,(0/1)⟩ := by
    rw [replayBackup_empty_closed_form]
    simp +decide [backedEvents,favorableCompleteS22Before,favorableCompleteProposal,favorableCompleteEvent1,favorableCompleteEvent2,favorableCompleteEvent3,favorableCompleteEvent4,favorableCompleteEvent5,favorableCompleteEvent6,favorableCompleteEvent7,favorableCompleteEvent8,favorableCompleteEvent9,favorableCompleteEvent10,favorableCompleteEvent11,favorableCompleteEvent12,favorableCompleteEvent13,favorableCompleteEvent14,favorableCompleteEvent15,favorableCompleteEvent16,favorableCompleteEvent17,favorableCompleteEvent18,favorableCompleteEvent19,favorableCompleteEvent20,favorableCompleteEvent21,taskReward]
    <;> norm_num
  have hp : rawVisits favorableCompleteS22Before [.query 1,.hydeRetriever 1] = 5 := by decide
  have hn : rawVisits favorableCompleteS22Before ([.query 1,.hydeRetriever 1]++[.selection 1]) = 1 := by decide
  have hz : (controlPenalty savedCref uniformQuoteError unitRoleUnused .complete) favorableCompleteS22Before [.query 1,.hydeRetriever 1] (.selection 1) = 0 := by
    apply control_penalty_empty_of_prior_terminal .complete savedCref uniformQuoteError favorableCompleteS22Before [.query 1,.hydeRetriever 1] (.selection 1) 14 (by decide)
    · decide
    · decide
  unfold indexScore
  rw [hs,hp,hn,hz]
  simp only [BackupStat.mean]
  norm_num

theorem favorableCompleteS22D2I1 : indexScore (7/5) (controlPenalty savedCref uniformQuoteError unitRoleUnused .complete) favorableCompleteS22Before [.query 1,.hydeRetriever 1] (.selection 2) = treeIndex ((0/1)/1) (7/5) 0 5 1 := by
  have hs : replayBackup favorableCompleteS22Before emptyStatistics ([.query 1,.hydeRetriever 1]++[.selection 2]) = ⟨1,(0/1)⟩ := by
    rw [replayBackup_empty_closed_form]
    simp +decide [backedEvents,favorableCompleteS22Before,favorableCompleteProposal,favorableCompleteEvent1,favorableCompleteEvent2,favorableCompleteEvent3,favorableCompleteEvent4,favorableCompleteEvent5,favorableCompleteEvent6,favorableCompleteEvent7,favorableCompleteEvent8,favorableCompleteEvent9,favorableCompleteEvent10,favorableCompleteEvent11,favorableCompleteEvent12,favorableCompleteEvent13,favorableCompleteEvent14,favorableCompleteEvent15,favorableCompleteEvent16,favorableCompleteEvent17,favorableCompleteEvent18,favorableCompleteEvent19,favorableCompleteEvent20,favorableCompleteEvent21,taskReward]
    <;> norm_num
  have hp : rawVisits favorableCompleteS22Before [.query 1,.hydeRetriever 1] = 5 := by decide
  have hn : rawVisits favorableCompleteS22Before ([.query 1,.hydeRetriever 1]++[.selection 2]) = 1 := by decide
  have hz : (controlPenalty savedCref uniformQuoteError unitRoleUnused .complete) favorableCompleteS22Before [.query 1,.hydeRetriever 1] (.selection 2) = 0 := by
    apply control_penalty_empty_of_prior_terminal .complete savedCref uniformQuoteError favorableCompleteS22Before [.query 1,.hydeRetriever 1] (.selection 2) 15 (by decide)
    · decide
    · decide
  unfold indexScore
  rw [hs,hp,hn,hz]
  simp only [BackupStat.mean]
  norm_num

theorem favorableCompleteS22D2I2 : indexScore (7/5) (controlPenalty savedCref uniformQuoteError unitRoleUnused .complete) favorableCompleteS22Before [.query 1,.hydeRetriever 1] (.selection 3) = treeIndex ((0/1)/1) (7/5) 0 5 1 := by
  have hs : replayBackup favorableCompleteS22Before emptyStatistics ([.query 1,.hydeRetriever 1]++[.selection 3]) = ⟨1,(0/1)⟩ := by
    rw [replayBackup_empty_closed_form]
    simp +decide [backedEvents,favorableCompleteS22Before,favorableCompleteProposal,favorableCompleteEvent1,favorableCompleteEvent2,favorableCompleteEvent3,favorableCompleteEvent4,favorableCompleteEvent5,favorableCompleteEvent6,favorableCompleteEvent7,favorableCompleteEvent8,favorableCompleteEvent9,favorableCompleteEvent10,favorableCompleteEvent11,favorableCompleteEvent12,favorableCompleteEvent13,favorableCompleteEvent14,favorableCompleteEvent15,favorableCompleteEvent16,favorableCompleteEvent17,favorableCompleteEvent18,favorableCompleteEvent19,favorableCompleteEvent20,favorableCompleteEvent21,taskReward]
    <;> norm_num
  have hp : rawVisits favorableCompleteS22Before [.query 1,.hydeRetriever 1] = 5 := by decide
  have hn : rawVisits favorableCompleteS22Before ([.query 1,.hydeRetriever 1]++[.selection 3]) = 1 := by decide
  have hz : (controlPenalty savedCref uniformQuoteError unitRoleUnused .complete) favorableCompleteS22Before [.query 1,.hydeRetriever 1] (.selection 3) = 0 := by
    apply control_penalty_empty_of_prior_terminal .complete savedCref uniformQuoteError favorableCompleteS22Before [.query 1,.hydeRetriever 1] (.selection 3) 18 (by decide)
    · decide
    · decide
  unfold indexScore
  rw [hs,hp,hn,hz]
  simp only [BackupStat.mean]
  norm_num

theorem favorableCompleteS22D2I3 : indexScore (7/5) (controlPenalty savedCref uniformQuoteError unitRoleUnused .complete) favorableCompleteS22Before [.query 1,.hydeRetriever 1] (.selection 0) = treeIndex ((1/2)/1) (7/5) 0 5 1 := by
  have hs : replayBackup favorableCompleteS22Before emptyStatistics ([.query 1,.hydeRetriever 1]++[.selection 0]) = ⟨1,(1/2)⟩ := by
    rw [replayBackup_empty_closed_form]
    simp +decide [backedEvents,favorableCompleteS22Before,favorableCompleteProposal,favorableCompleteEvent1,favorableCompleteEvent2,favorableCompleteEvent3,favorableCompleteEvent4,favorableCompleteEvent5,favorableCompleteEvent6,favorableCompleteEvent7,favorableCompleteEvent8,favorableCompleteEvent9,favorableCompleteEvent10,favorableCompleteEvent11,favorableCompleteEvent12,favorableCompleteEvent13,favorableCompleteEvent14,favorableCompleteEvent15,favorableCompleteEvent16,favorableCompleteEvent17,favorableCompleteEvent18,favorableCompleteEvent19,favorableCompleteEvent20,favorableCompleteEvent21,taskReward]
    <;> norm_num
  have hp : rawVisits favorableCompleteS22Before [.query 1,.hydeRetriever 1] = 5 := by decide
  have hn : rawVisits favorableCompleteS22Before ([.query 1,.hydeRetriever 1]++[.selection 0]) = 1 := by decide
  have hz : (controlPenalty savedCref uniformQuoteError unitRoleUnused .complete) favorableCompleteS22Before [.query 1,.hydeRetriever 1] (.selection 0) = 0 := by
    apply control_penalty_empty_of_prior_terminal .complete savedCref uniformQuoteError favorableCompleteS22Before [.query 1,.hydeRetriever 1] (.selection 0) 8 (by decide)
    · decide
    · decide
  unfold indexScore
  rw [hs,hp,hn,hz]
  simp only [BackupStat.mean]
  norm_num

theorem favorableCompleteS22D2Cmp0 : indexScore (7/5) (controlPenalty savedCref uniformQuoteError unitRoleUnused .complete) favorableCompleteS22Before [.query 1,.hydeRetriever 1] (.selection 1) < indexScore (7/5) (controlPenalty savedCref uniformQuoteError unitRoleUnused .complete) favorableCompleteS22Before [.query 1,.hydeRetriever 1] (.selection 0) := by
  rw [favorableCompleteS22D2I0,favorableCompleteS22D2I3]
  have h := index_strict_order_from_intervals ((1/2)/1) ((0/1)/1) 0 0 (93699627/50000000) (93699641/50000000)
    (treeBonus (7/5) 5 1) (treeBonus (7/5) 5 1)
    (trajectory_bonus_5_1).1 (trajectory_bonus_5_1).2 (by norm_num)
  simpa only [treeIndex,sub_zero] using h

theorem favorableCompleteS22D2Cmp1 : indexScore (7/5) (controlPenalty savedCref uniformQuoteError unitRoleUnused .complete) favorableCompleteS22Before [.query 1,.hydeRetriever 1] (.selection 2) < indexScore (7/5) (controlPenalty savedCref uniformQuoteError unitRoleUnused .complete) favorableCompleteS22Before [.query 1,.hydeRetriever 1] (.selection 0) := by
  rw [favorableCompleteS22D2I1,favorableCompleteS22D2I3]
  have h := index_strict_order_from_intervals ((1/2)/1) ((0/1)/1) 0 0 (93699627/50000000) (93699641/50000000)
    (treeBonus (7/5) 5 1) (treeBonus (7/5) 5 1)
    (trajectory_bonus_5_1).1 (trajectory_bonus_5_1).2 (by norm_num)
  simpa only [treeIndex,sub_zero] using h

theorem favorableCompleteS22D2Cmp2 : indexScore (7/5) (controlPenalty savedCref uniformQuoteError unitRoleUnused .complete) favorableCompleteS22Before [.query 1,.hydeRetriever 1] (.selection 3) < indexScore (7/5) (controlPenalty savedCref uniformQuoteError unitRoleUnused .complete) favorableCompleteS22Before [.query 1,.hydeRetriever 1] (.selection 0) := by
  rw [favorableCompleteS22D2I2,favorableCompleteS22D2I3]
  have h := index_strict_order_from_intervals ((1/2)/1) ((0/1)/1) 0 0 (93699627/50000000) (93699641/50000000)
    (treeBonus (7/5) 5 1) (treeBonus (7/5) 5 1)
    (trajectory_bonus_5_1).1 (trajectory_bonus_5_1).2 (by norm_num)
  simpa only [treeIndex,sub_zero] using h

theorem favorableCompleteS22Choice2 : nativeFirstChoice (indexScore (7/5) (controlPenalty savedCref uniformQuoteError unitRoleUnused .complete) favorableCompleteS22Before [.query 1,.hydeRetriever 1]) favorableCompleteS22Before [.query 1,.hydeRetriever 1] = .selection 0 := by
  apply visited_choice_from_ordered_certificate _ _ [.query 1,.hydeRetriever 1] [.selection 1,.selection 2,.selection 3] [] (.selection 0) (by decide)
  · intro a ha
    have ho : orderedLegalAvailable [.query 1,.hydeRetriever 1] = [.selection 1,.selection 2,.selection 3,.selection 0] := by decide
    rw [ho] at ha
    simp only [List.mem_cons,List.not_mem_nil,or_false] at ha
    rcases ha with rfl | rfl | rfl | rfl <;> decide
  · intro a ha
    simp only [List.mem_cons,List.not_mem_nil,or_false] at ha
    rcases ha with rfl | rfl | rfl
    · exact favorableCompleteS22D2Cmp0
    · exact favorableCompleteS22D2Cmp1
    · exact favorableCompleteS22D2Cmp2
  · simp

theorem favorableCompleteS22ActualEvent : nativeEvent budgetTape (7/5) (controlPenalty savedCref uniformQuoteError unitRoleUnused .complete)
    (taskReward false (2/5) (1/2)) favorableCompleteS22Before = favorableCompleteEvent22 := by
  have hs0 := native_select_existing_step budgetTape (7/5) (controlPenalty savedCref uniformQuoteError unitRoleUnused .complete) favorableCompleteS22Before 8 [] (.query 1)
    (by decide) (by decide) favorableCompleteS22Choice0
  have hs1 := native_select_existing_step budgetTape (7/5) (controlPenalty savedCref uniformQuoteError unitRoleUnused .complete) favorableCompleteS22Before 7 [.query 1] (.hydeRetriever 1)
    (by decide) (by decide) favorableCompleteS22Choice1
  have hs2 := native_select_existing_step budgetTape (7/5) (controlPenalty savedCref uniformQuoteError unitRoleUnused .complete) favorableCompleteS22Before 6 [.query 1,.hydeRetriever 1] (.selection 0)
    (by decide) (by decide) favorableCompleteS22Choice2
  have hnew := native_select_new_step budgetTape (7/5) (controlPenalty savedCref uniformQuoteError unitRoleUnused .complete) favorableCompleteS22Before 5 [.query 1,.hydeRetriever 1,.selection 0]
    [.width 3,.width 0,.width 1,.width 2] (.width 1) (by decide) (by decide) (by decide) (by decide)
  have hs : nativeSelect budgetTape (7/5) (controlPenalty savedCref uniformQuoteError unitRoleUnused .complete) favorableCompleteS22Before 9 [] = [.query 1,.hydeRetriever 1,.selection 0,.width 1] := by
    rw [hs0]
    change nativeSelect budgetTape (7/5) (controlPenalty savedCref uniformQuoteError unitRoleUnused .complete) favorableCompleteS22Before 8 [.query 1] = _
    rw [hs1]
    change nativeSelect budgetTape (7/5) (controlPenalty savedCref uniformQuoteError unitRoleUnused .complete) favorableCompleteS22Before 7 [.query 1,.hydeRetriever 1] = _
    rw [hs2]
    change nativeSelect budgetTape (7/5) (controlPenalty savedCref uniformQuoteError unitRoleUnused .complete) favorableCompleteS22Before 6 [.query 1,.hydeRetriever 1,.selection 0] = _
    rw [hnew] <;> rfl
  have hr : repairedRollout budgetTape favorableCompleteS22Before 9 [.query 1,.hydeRetriever 1,.selection 0,.width 1] = [.query 1,.hydeRetriever 1,.selection 0,.width 1,.stop,.reranker 0,.topm 0,.context 0,.answer 0] := by decide
  simp only [nativeEvent,hs,hr]
  rfl

def favorableCompleteS23Before := favorableCompleteProposal.take 22

theorem favorableCompleteS23Choice0 : nativeFirstChoice (indexScore (7/5) (controlPenalty savedCref uniformQuoteError unitRoleUnused .complete) favorableCompleteS23Before []) favorableCompleteS23Before [] = .query 1 := by
  apply complete_root_from_physical_gap favorableCompleteS23Before (favorableComplete_prefix_rewards 22) (by decide)
  · intro q; fin_cases q <;> decide
  · decide
  · intro q hq
    exact AgentUCTNextExact.favorable_complete_normal_root_physical_quote_exact 22 (by omega) q hq

theorem favorableCompleteS23D1I0 : indexScore (7/5) (controlPenalty savedCref uniformQuoteError unitRoleUnused .complete) favorableCompleteS23Before [.query 1] (.hydeRetriever 1) = treeIndex ((3/2)/6) (7/5) 0 15 6 := by
  have hs : replayBackup favorableCompleteS23Before emptyStatistics ([.query 1]++[.hydeRetriever 1]) = ⟨6,(3/2)⟩ := by
    rw [replayBackup_empty_closed_form]
    simp +decide [backedEvents,favorableCompleteS23Before,favorableCompleteProposal,favorableCompleteEvent1,favorableCompleteEvent2,favorableCompleteEvent3,favorableCompleteEvent4,favorableCompleteEvent5,favorableCompleteEvent6,favorableCompleteEvent7,favorableCompleteEvent8,favorableCompleteEvent9,favorableCompleteEvent10,favorableCompleteEvent11,favorableCompleteEvent12,favorableCompleteEvent13,favorableCompleteEvent14,favorableCompleteEvent15,favorableCompleteEvent16,favorableCompleteEvent17,favorableCompleteEvent18,favorableCompleteEvent19,favorableCompleteEvent20,favorableCompleteEvent21,favorableCompleteEvent22,taskReward]
    <;> norm_num
  have hp : rawVisits favorableCompleteS23Before [.query 1] = 15 := by decide
  have hn : rawVisits favorableCompleteS23Before ([.query 1]++[.hydeRetriever 1]) = 6 := by decide
  have hz : (controlPenalty savedCref uniformQuoteError unitRoleUnused .complete) favorableCompleteS23Before [.query 1] (.hydeRetriever 1) = 0 := by
    apply control_penalty_empty_of_prior_terminal .complete savedCref uniformQuoteError favorableCompleteS23Before [.query 1] (.hydeRetriever 1) 8 (by decide)
    · decide
    · decide
  unfold indexScore
  rw [hs,hp,hn,hz]
  simp only [BackupStat.mean]
  norm_num

theorem favorableCompleteS23D1I1 : indexScore (7/5) (controlPenalty savedCref uniformQuoteError unitRoleUnused .complete) favorableCompleteS23Before [.query 1] (.hydeRetriever 0) = treeIndex ((0/1)/4) (7/5) 0 15 4 := by
  have hs : replayBackup favorableCompleteS23Before emptyStatistics ([.query 1]++[.hydeRetriever 0]) = ⟨4,(0/1)⟩ := by
    rw [replayBackup_empty_closed_form]
    simp +decide [backedEvents,favorableCompleteS23Before,favorableCompleteProposal,favorableCompleteEvent1,favorableCompleteEvent2,favorableCompleteEvent3,favorableCompleteEvent4,favorableCompleteEvent5,favorableCompleteEvent6,favorableCompleteEvent7,favorableCompleteEvent8,favorableCompleteEvent9,favorableCompleteEvent10,favorableCompleteEvent11,favorableCompleteEvent12,favorableCompleteEvent13,favorableCompleteEvent14,favorableCompleteEvent15,favorableCompleteEvent16,favorableCompleteEvent17,favorableCompleteEvent18,favorableCompleteEvent19,favorableCompleteEvent20,favorableCompleteEvent21,favorableCompleteEvent22,taskReward]
    <;> norm_num
  have hp : rawVisits favorableCompleteS23Before [.query 1] = 15 := by decide
  have hn : rawVisits favorableCompleteS23Before ([.query 1]++[.hydeRetriever 0]) = 4 := by decide
  have hz : (controlPenalty savedCref uniformQuoteError unitRoleUnused .complete) favorableCompleteS23Before [.query 1] (.hydeRetriever 0) = 0 := by
    apply control_penalty_empty_of_prior_terminal .complete savedCref uniformQuoteError favorableCompleteS23Before [.query 1] (.hydeRetriever 0) 1 (by decide)
    · decide
    · decide
  unfold indexScore
  rw [hs,hp,hn,hz]
  simp only [BackupStat.mean]
  norm_num

theorem favorableCompleteS23D1I2 : indexScore (7/5) (controlPenalty savedCref uniformQuoteError unitRoleUnused .complete) favorableCompleteS23Before [.query 1] (.hydeRetriever 2) = treeIndex ((0/1)/4) (7/5) 0 15 4 := by
  have hs : replayBackup favorableCompleteS23Before emptyStatistics ([.query 1]++[.hydeRetriever 2]) = ⟨4,(0/1)⟩ := by
    rw [replayBackup_empty_closed_form]
    simp +decide [backedEvents,favorableCompleteS23Before,favorableCompleteProposal,favorableCompleteEvent1,favorableCompleteEvent2,favorableCompleteEvent3,favorableCompleteEvent4,favorableCompleteEvent5,favorableCompleteEvent6,favorableCompleteEvent7,favorableCompleteEvent8,favorableCompleteEvent9,favorableCompleteEvent10,favorableCompleteEvent11,favorableCompleteEvent12,favorableCompleteEvent13,favorableCompleteEvent14,favorableCompleteEvent15,favorableCompleteEvent16,favorableCompleteEvent17,favorableCompleteEvent18,favorableCompleteEvent19,favorableCompleteEvent20,favorableCompleteEvent21,favorableCompleteEvent22,taskReward]
    <;> norm_num
  have hp : rawVisits favorableCompleteS23Before [.query 1] = 15 := by decide
  have hn : rawVisits favorableCompleteS23Before ([.query 1]++[.hydeRetriever 2]) = 4 := by decide
  have hz : (controlPenalty savedCref uniformQuoteError unitRoleUnused .complete) favorableCompleteS23Before [.query 1] (.hydeRetriever 2) = 0 := by
    apply control_penalty_empty_of_prior_terminal .complete savedCref uniformQuoteError favorableCompleteS23Before [.query 1] (.hydeRetriever 2) 10 (by decide)
    · decide
    · decide
  unfold indexScore
  rw [hs,hp,hn,hz]
  simp only [BackupStat.mean]
  norm_num

theorem favorableCompleteS23D1Cmp1 : indexScore (7/5) (controlPenalty savedCref uniformQuoteError unitRoleUnused .complete) favorableCompleteS23Before [.query 1] (.hydeRetriever 0) ≤ indexScore (7/5) (controlPenalty savedCref uniformQuoteError unitRoleUnused .complete) favorableCompleteS23Before [.query 1] (.hydeRetriever 1) := by
  rw [favorableCompleteS23D1I1,favorableCompleteS23D1I0]
  have h := index_weak_order_from_intervals ((3/2)/6) ((0/1)/4) 0 0 (47584453/50000000) (58278829/50000000)
    (treeBonus (7/5) 15 6) (treeBonus (7/5) 15 4)
    (trajectory_bonus_15_6).1 (trajectory_bonus_15_4).2 (by norm_num)
  simpa only [treeIndex,sub_zero] using h

theorem favorableCompleteS23D1Cmp2 : indexScore (7/5) (controlPenalty savedCref uniformQuoteError unitRoleUnused .complete) favorableCompleteS23Before [.query 1] (.hydeRetriever 2) ≤ indexScore (7/5) (controlPenalty savedCref uniformQuoteError unitRoleUnused .complete) favorableCompleteS23Before [.query 1] (.hydeRetriever 1) := by
  rw [favorableCompleteS23D1I2,favorableCompleteS23D1I0]
  have h := index_weak_order_from_intervals ((3/2)/6) ((0/1)/4) 0 0 (47584453/50000000) (58278829/50000000)
    (treeBonus (7/5) 15 6) (treeBonus (7/5) 15 4)
    (trajectory_bonus_15_6).1 (trajectory_bonus_15_4).2 (by norm_num)
  simpa only [treeIndex,sub_zero] using h

theorem favorableCompleteS23Choice1 : nativeFirstChoice (indexScore (7/5) (controlPenalty savedCref uniformQuoteError unitRoleUnused .complete) favorableCompleteS23Before [.query 1]) favorableCompleteS23Before [.query 1] = .hydeRetriever 1 := by
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
    · exact favorableCompleteS23D1Cmp1
    · exact favorableCompleteS23D1Cmp2

theorem favorableCompleteS23D2I0 : indexScore (7/5) (controlPenalty savedCref uniformQuoteError unitRoleUnused .complete) favorableCompleteS23Before [.query 1,.hydeRetriever 1] (.selection 1) = treeIndex ((0/1)/1) (7/5) 0 6 1 := by
  have hs : replayBackup favorableCompleteS23Before emptyStatistics ([.query 1,.hydeRetriever 1]++[.selection 1]) = ⟨1,(0/1)⟩ := by
    rw [replayBackup_empty_closed_form]
    simp +decide [backedEvents,favorableCompleteS23Before,favorableCompleteProposal,favorableCompleteEvent1,favorableCompleteEvent2,favorableCompleteEvent3,favorableCompleteEvent4,favorableCompleteEvent5,favorableCompleteEvent6,favorableCompleteEvent7,favorableCompleteEvent8,favorableCompleteEvent9,favorableCompleteEvent10,favorableCompleteEvent11,favorableCompleteEvent12,favorableCompleteEvent13,favorableCompleteEvent14,favorableCompleteEvent15,favorableCompleteEvent16,favorableCompleteEvent17,favorableCompleteEvent18,favorableCompleteEvent19,favorableCompleteEvent20,favorableCompleteEvent21,favorableCompleteEvent22,taskReward]
    <;> norm_num
  have hp : rawVisits favorableCompleteS23Before [.query 1,.hydeRetriever 1] = 6 := by decide
  have hn : rawVisits favorableCompleteS23Before ([.query 1,.hydeRetriever 1]++[.selection 1]) = 1 := by decide
  have hz : (controlPenalty savedCref uniformQuoteError unitRoleUnused .complete) favorableCompleteS23Before [.query 1,.hydeRetriever 1] (.selection 1) = 0 := by
    apply control_penalty_empty_of_prior_terminal .complete savedCref uniformQuoteError favorableCompleteS23Before [.query 1,.hydeRetriever 1] (.selection 1) 14 (by decide)
    · decide
    · decide
  unfold indexScore
  rw [hs,hp,hn,hz]
  simp only [BackupStat.mean]
  norm_num

theorem favorableCompleteS23D2I1 : indexScore (7/5) (controlPenalty savedCref uniformQuoteError unitRoleUnused .complete) favorableCompleteS23Before [.query 1,.hydeRetriever 1] (.selection 2) = treeIndex ((0/1)/1) (7/5) 0 6 1 := by
  have hs : replayBackup favorableCompleteS23Before emptyStatistics ([.query 1,.hydeRetriever 1]++[.selection 2]) = ⟨1,(0/1)⟩ := by
    rw [replayBackup_empty_closed_form]
    simp +decide [backedEvents,favorableCompleteS23Before,favorableCompleteProposal,favorableCompleteEvent1,favorableCompleteEvent2,favorableCompleteEvent3,favorableCompleteEvent4,favorableCompleteEvent5,favorableCompleteEvent6,favorableCompleteEvent7,favorableCompleteEvent8,favorableCompleteEvent9,favorableCompleteEvent10,favorableCompleteEvent11,favorableCompleteEvent12,favorableCompleteEvent13,favorableCompleteEvent14,favorableCompleteEvent15,favorableCompleteEvent16,favorableCompleteEvent17,favorableCompleteEvent18,favorableCompleteEvent19,favorableCompleteEvent20,favorableCompleteEvent21,favorableCompleteEvent22,taskReward]
    <;> norm_num
  have hp : rawVisits favorableCompleteS23Before [.query 1,.hydeRetriever 1] = 6 := by decide
  have hn : rawVisits favorableCompleteS23Before ([.query 1,.hydeRetriever 1]++[.selection 2]) = 1 := by decide
  have hz : (controlPenalty savedCref uniformQuoteError unitRoleUnused .complete) favorableCompleteS23Before [.query 1,.hydeRetriever 1] (.selection 2) = 0 := by
    apply control_penalty_empty_of_prior_terminal .complete savedCref uniformQuoteError favorableCompleteS23Before [.query 1,.hydeRetriever 1] (.selection 2) 15 (by decide)
    · decide
    · decide
  unfold indexScore
  rw [hs,hp,hn,hz]
  simp only [BackupStat.mean]
  norm_num

theorem favorableCompleteS23D2I2 : indexScore (7/5) (controlPenalty savedCref uniformQuoteError unitRoleUnused .complete) favorableCompleteS23Before [.query 1,.hydeRetriever 1] (.selection 3) = treeIndex ((0/1)/1) (7/5) 0 6 1 := by
  have hs : replayBackup favorableCompleteS23Before emptyStatistics ([.query 1,.hydeRetriever 1]++[.selection 3]) = ⟨1,(0/1)⟩ := by
    rw [replayBackup_empty_closed_form]
    simp +decide [backedEvents,favorableCompleteS23Before,favorableCompleteProposal,favorableCompleteEvent1,favorableCompleteEvent2,favorableCompleteEvent3,favorableCompleteEvent4,favorableCompleteEvent5,favorableCompleteEvent6,favorableCompleteEvent7,favorableCompleteEvent8,favorableCompleteEvent9,favorableCompleteEvent10,favorableCompleteEvent11,favorableCompleteEvent12,favorableCompleteEvent13,favorableCompleteEvent14,favorableCompleteEvent15,favorableCompleteEvent16,favorableCompleteEvent17,favorableCompleteEvent18,favorableCompleteEvent19,favorableCompleteEvent20,favorableCompleteEvent21,favorableCompleteEvent22,taskReward]
    <;> norm_num
  have hp : rawVisits favorableCompleteS23Before [.query 1,.hydeRetriever 1] = 6 := by decide
  have hn : rawVisits favorableCompleteS23Before ([.query 1,.hydeRetriever 1]++[.selection 3]) = 1 := by decide
  have hz : (controlPenalty savedCref uniformQuoteError unitRoleUnused .complete) favorableCompleteS23Before [.query 1,.hydeRetriever 1] (.selection 3) = 0 := by
    apply control_penalty_empty_of_prior_terminal .complete savedCref uniformQuoteError favorableCompleteS23Before [.query 1,.hydeRetriever 1] (.selection 3) 18 (by decide)
    · decide
    · decide
  unfold indexScore
  rw [hs,hp,hn,hz]
  simp only [BackupStat.mean]
  norm_num

theorem favorableCompleteS23D2I3 : indexScore (7/5) (controlPenalty savedCref uniformQuoteError unitRoleUnused .complete) favorableCompleteS23Before [.query 1,.hydeRetriever 1] (.selection 0) = treeIndex ((1/1)/2) (7/5) 0 6 2 := by
  have hs : replayBackup favorableCompleteS23Before emptyStatistics ([.query 1,.hydeRetriever 1]++[.selection 0]) = ⟨2,(1/1)⟩ := by
    rw [replayBackup_empty_closed_form]
    simp +decide [backedEvents,favorableCompleteS23Before,favorableCompleteProposal,favorableCompleteEvent1,favorableCompleteEvent2,favorableCompleteEvent3,favorableCompleteEvent4,favorableCompleteEvent5,favorableCompleteEvent6,favorableCompleteEvent7,favorableCompleteEvent8,favorableCompleteEvent9,favorableCompleteEvent10,favorableCompleteEvent11,favorableCompleteEvent12,favorableCompleteEvent13,favorableCompleteEvent14,favorableCompleteEvent15,favorableCompleteEvent16,favorableCompleteEvent17,favorableCompleteEvent18,favorableCompleteEvent19,favorableCompleteEvent20,favorableCompleteEvent21,favorableCompleteEvent22,taskReward]
    <;> norm_num
  have hp : rawVisits favorableCompleteS23Before [.query 1,.hydeRetriever 1] = 6 := by decide
  have hn : rawVisits favorableCompleteS23Before ([.query 1,.hydeRetriever 1]++[.selection 0]) = 2 := by decide
  have hz : (controlPenalty savedCref uniformQuoteError unitRoleUnused .complete) favorableCompleteS23Before [.query 1,.hydeRetriever 1] (.selection 0) = 0 := by
    apply control_penalty_empty_of_prior_terminal .complete savedCref uniformQuoteError favorableCompleteS23Before [.query 1,.hydeRetriever 1] (.selection 0) 8 (by decide)
    · decide
    · decide
  unfold indexScore
  rw [hs,hp,hn,hz]
  simp only [BackupStat.mean]
  norm_num

theorem favorableCompleteS23D2Cmp1 : indexScore (7/5) (controlPenalty savedCref uniformQuoteError unitRoleUnused .complete) favorableCompleteS23Before [.query 1,.hydeRetriever 1] (.selection 2) ≤ indexScore (7/5) (controlPenalty savedCref uniformQuoteError unitRoleUnused .complete) favorableCompleteS23Before [.query 1,.hydeRetriever 1] (.selection 1) := by
  rw [favorableCompleteS23D2I1,favorableCompleteS23D2I0]

theorem favorableCompleteS23D2Cmp2 : indexScore (7/5) (controlPenalty savedCref uniformQuoteError unitRoleUnused .complete) favorableCompleteS23Before [.query 1,.hydeRetriever 1] (.selection 3) ≤ indexScore (7/5) (controlPenalty savedCref uniformQuoteError unitRoleUnused .complete) favorableCompleteS23Before [.query 1,.hydeRetriever 1] (.selection 1) := by
  rw [favorableCompleteS23D2I2,favorableCompleteS23D2I0]

theorem favorableCompleteS23D2Cmp3 : indexScore (7/5) (controlPenalty savedCref uniformQuoteError unitRoleUnused .complete) favorableCompleteS23Before [.query 1,.hydeRetriever 1] (.selection 0) ≤ indexScore (7/5) (controlPenalty savedCref uniformQuoteError unitRoleUnused .complete) favorableCompleteS23Before [.query 1,.hydeRetriever 1] (.selection 1) := by
  rw [favorableCompleteS23D2I3,favorableCompleteS23D2I0]
  have h := index_weak_order_from_intervals ((0/1)/1) ((1/1)/2) 0 0 (24411779/12500000) (69046943/50000000)
    (treeBonus (7/5) 6 1) (treeBonus (7/5) 6 2)
    (trajectory_bonus_6_1).1 (trajectory_bonus_6_2).2 (by norm_num)
  simpa only [treeIndex,sub_zero] using h

theorem favorableCompleteS23Choice2 : nativeFirstChoice (indexScore (7/5) (controlPenalty savedCref uniformQuoteError unitRoleUnused .complete) favorableCompleteS23Before [.query 1,.hydeRetriever 1]) favorableCompleteS23Before [.query 1,.hydeRetriever 1] = .selection 1 := by
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
    · exact favorableCompleteS23D2Cmp1
    · exact favorableCompleteS23D2Cmp2
    · exact favorableCompleteS23D2Cmp3

theorem favorableCompleteS23ActualEvent : nativeEvent budgetTape (7/5) (controlPenalty savedCref uniformQuoteError unitRoleUnused .complete)
    (taskReward false (2/5) (1/2)) favorableCompleteS23Before = favorableCompleteEvent23 := by
  have hs0 := native_select_existing_step budgetTape (7/5) (controlPenalty savedCref uniformQuoteError unitRoleUnused .complete) favorableCompleteS23Before 8 [] (.query 1)
    (by decide) (by decide) favorableCompleteS23Choice0
  have hs1 := native_select_existing_step budgetTape (7/5) (controlPenalty savedCref uniformQuoteError unitRoleUnused .complete) favorableCompleteS23Before 7 [.query 1] (.hydeRetriever 1)
    (by decide) (by decide) favorableCompleteS23Choice1
  have hs2 := native_select_existing_step budgetTape (7/5) (controlPenalty savedCref uniformQuoteError unitRoleUnused .complete) favorableCompleteS23Before 6 [.query 1,.hydeRetriever 1] (.selection 1)
    (by decide) (by decide) favorableCompleteS23Choice2
  have hnew := native_select_new_step budgetTape (7/5) (controlPenalty savedCref uniformQuoteError unitRoleUnused .complete) favorableCompleteS23Before 5 [.query 1,.hydeRetriever 1,.selection 1]
    [.width 3,.width 0,.width 1,.width 2] (.width 0) (by decide) (by decide) (by decide) (by decide)
  have hs : nativeSelect budgetTape (7/5) (controlPenalty savedCref uniformQuoteError unitRoleUnused .complete) favorableCompleteS23Before 9 [] = [.query 1,.hydeRetriever 1,.selection 1,.width 0] := by
    rw [hs0]
    change nativeSelect budgetTape (7/5) (controlPenalty savedCref uniformQuoteError unitRoleUnused .complete) favorableCompleteS23Before 8 [.query 1] = _
    rw [hs1]
    change nativeSelect budgetTape (7/5) (controlPenalty savedCref uniformQuoteError unitRoleUnused .complete) favorableCompleteS23Before 7 [.query 1,.hydeRetriever 1] = _
    rw [hs2]
    change nativeSelect budgetTape (7/5) (controlPenalty savedCref uniformQuoteError unitRoleUnused .complete) favorableCompleteS23Before 6 [.query 1,.hydeRetriever 1,.selection 1] = _
    rw [hnew] <;> rfl
  have hr : repairedRollout budgetTape favorableCompleteS23Before 9 [.query 1,.hydeRetriever 1,.selection 1,.width 0] = [.query 1,.hydeRetriever 1,.selection 1,.width 0,.stop,.reranker 0,.topm 0,.context 0,.answer 0] := by decide
  simp only [nativeEvent,hs,hr]
  rfl

def favorableCompleteS24Before := favorableCompleteProposal.take 23

theorem favorableCompleteS24Choice0 : nativeFirstChoice (indexScore (7/5) (controlPenalty savedCref uniformQuoteError unitRoleUnused .complete) favorableCompleteS24Before []) favorableCompleteS24Before [] = .query 1 := by
  apply complete_root_from_physical_gap favorableCompleteS24Before (favorableComplete_prefix_rewards 23) (by decide)
  · intro q; fin_cases q <;> decide
  · decide
  · intro q hq
    exact AgentUCTNextExact.favorable_complete_normal_root_physical_quote_exact 23 (by omega) q hq

theorem favorableCompleteS24D1I0 : indexScore (7/5) (controlPenalty savedCref uniformQuoteError unitRoleUnused .complete) favorableCompleteS24Before [.query 1] (.hydeRetriever 1) = treeIndex ((3/2)/7) (7/5) 0 16 7 := by
  have hs : replayBackup favorableCompleteS24Before emptyStatistics ([.query 1]++[.hydeRetriever 1]) = ⟨7,(3/2)⟩ := by
    rw [replayBackup_empty_closed_form]
    simp +decide [backedEvents,favorableCompleteS24Before,favorableCompleteProposal,favorableCompleteEvent1,favorableCompleteEvent2,favorableCompleteEvent3,favorableCompleteEvent4,favorableCompleteEvent5,favorableCompleteEvent6,favorableCompleteEvent7,favorableCompleteEvent8,favorableCompleteEvent9,favorableCompleteEvent10,favorableCompleteEvent11,favorableCompleteEvent12,favorableCompleteEvent13,favorableCompleteEvent14,favorableCompleteEvent15,favorableCompleteEvent16,favorableCompleteEvent17,favorableCompleteEvent18,favorableCompleteEvent19,favorableCompleteEvent20,favorableCompleteEvent21,favorableCompleteEvent22,favorableCompleteEvent23,taskReward]
    <;> norm_num
  have hp : rawVisits favorableCompleteS24Before [.query 1] = 16 := by decide
  have hn : rawVisits favorableCompleteS24Before ([.query 1]++[.hydeRetriever 1]) = 7 := by decide
  have hz : (controlPenalty savedCref uniformQuoteError unitRoleUnused .complete) favorableCompleteS24Before [.query 1] (.hydeRetriever 1) = 0 := by
    apply control_penalty_empty_of_prior_terminal .complete savedCref uniformQuoteError favorableCompleteS24Before [.query 1] (.hydeRetriever 1) 8 (by decide)
    · decide
    · decide
  unfold indexScore
  rw [hs,hp,hn,hz]
  simp only [BackupStat.mean]
  norm_num

theorem favorableCompleteS24D1I1 : indexScore (7/5) (controlPenalty savedCref uniformQuoteError unitRoleUnused .complete) favorableCompleteS24Before [.query 1] (.hydeRetriever 0) = treeIndex ((0/1)/4) (7/5) 0 16 4 := by
  have hs : replayBackup favorableCompleteS24Before emptyStatistics ([.query 1]++[.hydeRetriever 0]) = ⟨4,(0/1)⟩ := by
    rw [replayBackup_empty_closed_form]
    simp +decide [backedEvents,favorableCompleteS24Before,favorableCompleteProposal,favorableCompleteEvent1,favorableCompleteEvent2,favorableCompleteEvent3,favorableCompleteEvent4,favorableCompleteEvent5,favorableCompleteEvent6,favorableCompleteEvent7,favorableCompleteEvent8,favorableCompleteEvent9,favorableCompleteEvent10,favorableCompleteEvent11,favorableCompleteEvent12,favorableCompleteEvent13,favorableCompleteEvent14,favorableCompleteEvent15,favorableCompleteEvent16,favorableCompleteEvent17,favorableCompleteEvent18,favorableCompleteEvent19,favorableCompleteEvent20,favorableCompleteEvent21,favorableCompleteEvent22,favorableCompleteEvent23,taskReward]
    <;> norm_num
  have hp : rawVisits favorableCompleteS24Before [.query 1] = 16 := by decide
  have hn : rawVisits favorableCompleteS24Before ([.query 1]++[.hydeRetriever 0]) = 4 := by decide
  have hz : (controlPenalty savedCref uniformQuoteError unitRoleUnused .complete) favorableCompleteS24Before [.query 1] (.hydeRetriever 0) = 0 := by
    apply control_penalty_empty_of_prior_terminal .complete savedCref uniformQuoteError favorableCompleteS24Before [.query 1] (.hydeRetriever 0) 1 (by decide)
    · decide
    · decide
  unfold indexScore
  rw [hs,hp,hn,hz]
  simp only [BackupStat.mean]
  norm_num

theorem favorableCompleteS24D1I2 : indexScore (7/5) (controlPenalty savedCref uniformQuoteError unitRoleUnused .complete) favorableCompleteS24Before [.query 1] (.hydeRetriever 2) = treeIndex ((0/1)/4) (7/5) 0 16 4 := by
  have hs : replayBackup favorableCompleteS24Before emptyStatistics ([.query 1]++[.hydeRetriever 2]) = ⟨4,(0/1)⟩ := by
    rw [replayBackup_empty_closed_form]
    simp +decide [backedEvents,favorableCompleteS24Before,favorableCompleteProposal,favorableCompleteEvent1,favorableCompleteEvent2,favorableCompleteEvent3,favorableCompleteEvent4,favorableCompleteEvent5,favorableCompleteEvent6,favorableCompleteEvent7,favorableCompleteEvent8,favorableCompleteEvent9,favorableCompleteEvent10,favorableCompleteEvent11,favorableCompleteEvent12,favorableCompleteEvent13,favorableCompleteEvent14,favorableCompleteEvent15,favorableCompleteEvent16,favorableCompleteEvent17,favorableCompleteEvent18,favorableCompleteEvent19,favorableCompleteEvent20,favorableCompleteEvent21,favorableCompleteEvent22,favorableCompleteEvent23,taskReward]
    <;> norm_num
  have hp : rawVisits favorableCompleteS24Before [.query 1] = 16 := by decide
  have hn : rawVisits favorableCompleteS24Before ([.query 1]++[.hydeRetriever 2]) = 4 := by decide
  have hz : (controlPenalty savedCref uniformQuoteError unitRoleUnused .complete) favorableCompleteS24Before [.query 1] (.hydeRetriever 2) = 0 := by
    apply control_penalty_empty_of_prior_terminal .complete savedCref uniformQuoteError favorableCompleteS24Before [.query 1] (.hydeRetriever 2) 10 (by decide)
    · decide
    · decide
  unfold indexScore
  rw [hs,hp,hn,hz]
  simp only [BackupStat.mean]
  norm_num

theorem favorableCompleteS24D1Cmp0 : indexScore (7/5) (controlPenalty savedCref uniformQuoteError unitRoleUnused .complete) favorableCompleteS24Before [.query 1] (.hydeRetriever 1) < indexScore (7/5) (controlPenalty savedCref uniformQuoteError unitRoleUnused .complete) favorableCompleteS24Before [.query 1] (.hydeRetriever 0) := by
  rw [favorableCompleteS24D1I0,favorableCompleteS24D1I1]
  have h := index_strict_order_from_intervals ((0/1)/4) ((3/2)/7) 0 0 (2356501/2000000) (11133423/12500000)
    (treeBonus (7/5) 16 4) (treeBonus (7/5) 16 7)
    (trajectory_bonus_16_4).1 (trajectory_bonus_16_7).2 (by norm_num)
  simpa only [treeIndex,sub_zero] using h

theorem favorableCompleteS24D1Cmp2 : indexScore (7/5) (controlPenalty savedCref uniformQuoteError unitRoleUnused .complete) favorableCompleteS24Before [.query 1] (.hydeRetriever 2) ≤ indexScore (7/5) (controlPenalty savedCref uniformQuoteError unitRoleUnused .complete) favorableCompleteS24Before [.query 1] (.hydeRetriever 0) := by
  rw [favorableCompleteS24D1I2,favorableCompleteS24D1I1]

theorem favorableCompleteS24Choice1 : nativeFirstChoice (indexScore (7/5) (controlPenalty savedCref uniformQuoteError unitRoleUnused .complete) favorableCompleteS24Before [.query 1]) favorableCompleteS24Before [.query 1] = .hydeRetriever 0 := by
  apply visited_choice_from_ordered_certificate _ _ [.query 1] [.hydeRetriever 1] [.hydeRetriever 2] (.hydeRetriever 0) (by decide)
  · intro a ha
    have ho : orderedLegalAvailable [.query 1] = [.hydeRetriever 1,.hydeRetriever 0,.hydeRetriever 2] := by decide
    rw [ho] at ha
    simp only [List.mem_cons,List.not_mem_nil,or_false] at ha
    rcases ha with rfl | rfl | rfl <;> decide
  · intro a ha
    simp only [List.mem_cons,List.not_mem_nil,or_false] at ha
    rcases ha with rfl
    · exact favorableCompleteS24D1Cmp0
  · intro a ha
    simp only [List.mem_cons,List.not_mem_nil,or_false] at ha
    rcases ha with rfl
    · exact favorableCompleteS24D1Cmp2

theorem favorableCompleteS24ActualEvent : nativeEvent budgetTape (7/5) (controlPenalty savedCref uniformQuoteError unitRoleUnused .complete)
    (taskReward false (2/5) (1/2)) favorableCompleteS24Before = favorableCompleteEvent24 := by
  have hs0 := native_select_existing_step budgetTape (7/5) (controlPenalty savedCref uniformQuoteError unitRoleUnused .complete) favorableCompleteS24Before 8 [] (.query 1)
    (by decide) (by decide) favorableCompleteS24Choice0
  have hs1 := native_select_existing_step budgetTape (7/5) (controlPenalty savedCref uniformQuoteError unitRoleUnused .complete) favorableCompleteS24Before 7 [.query 1] (.hydeRetriever 0)
    (by decide) (by decide) favorableCompleteS24Choice1
  have hnew := native_select_new_step budgetTape (7/5) (controlPenalty savedCref uniformQuoteError unitRoleUnused .complete) favorableCompleteS24Before 6 [.query 1,.hydeRetriever 0]
    [.selection 3] (.selection 3) (by decide) (by decide) (by decide) (by decide)
  have hs : nativeSelect budgetTape (7/5) (controlPenalty savedCref uniformQuoteError unitRoleUnused .complete) favorableCompleteS24Before 9 [] = [.query 1,.hydeRetriever 0,.selection 3] := by
    rw [hs0]
    change nativeSelect budgetTape (7/5) (controlPenalty savedCref uniformQuoteError unitRoleUnused .complete) favorableCompleteS24Before 8 [.query 1] = _
    rw [hs1]
    change nativeSelect budgetTape (7/5) (controlPenalty savedCref uniformQuoteError unitRoleUnused .complete) favorableCompleteS24Before 7 [.query 1,.hydeRetriever 0] = _
    rw [hnew] <;> rfl
  have hr : repairedRollout budgetTape favorableCompleteS24Before 9 [.query 1,.hydeRetriever 0,.selection 3] = [.query 1,.hydeRetriever 0,.selection 3,.width 0,.stop,.reranker 0,.topm 0,.context 0,.answer 0] := by decide
  simp only [nativeEvent,hs,hr]
  rfl

def favorableCompleteS25Before := favorableCompleteProposal.take 24

theorem favorableCompleteS25Choice0 : nativeFirstChoice (indexScore (7/5) (controlPenalty savedCref uniformQuoteError unitRoleUnused .complete) favorableCompleteS25Before []) favorableCompleteS25Before [] = .query 1 := by
  apply complete_root_from_physical_gap favorableCompleteS25Before (favorableComplete_prefix_rewards 24) (by decide)
  · intro q; fin_cases q <;> decide
  · decide
  · intro q hq
    exact AgentUCTNextExact.favorable_complete_normal_root_physical_quote_exact 24 (by omega) q hq

theorem favorableCompleteS25D1I0 : indexScore (7/5) (controlPenalty savedCref uniformQuoteError unitRoleUnused .complete) favorableCompleteS25Before [.query 1] (.hydeRetriever 1) = treeIndex ((3/2)/7) (7/5) 0 17 7 := by
  have hs : replayBackup favorableCompleteS25Before emptyStatistics ([.query 1]++[.hydeRetriever 1]) = ⟨7,(3/2)⟩ := by
    rw [replayBackup_empty_closed_form]
    simp +decide [backedEvents,favorableCompleteS25Before,favorableCompleteProposal,favorableCompleteEvent1,favorableCompleteEvent2,favorableCompleteEvent3,favorableCompleteEvent4,favorableCompleteEvent5,favorableCompleteEvent6,favorableCompleteEvent7,favorableCompleteEvent8,favorableCompleteEvent9,favorableCompleteEvent10,favorableCompleteEvent11,favorableCompleteEvent12,favorableCompleteEvent13,favorableCompleteEvent14,favorableCompleteEvent15,favorableCompleteEvent16,favorableCompleteEvent17,favorableCompleteEvent18,favorableCompleteEvent19,favorableCompleteEvent20,favorableCompleteEvent21,favorableCompleteEvent22,favorableCompleteEvent23,favorableCompleteEvent24,taskReward]
    <;> norm_num
  have hp : rawVisits favorableCompleteS25Before [.query 1] = 17 := by decide
  have hn : rawVisits favorableCompleteS25Before ([.query 1]++[.hydeRetriever 1]) = 7 := by decide
  have hz : (controlPenalty savedCref uniformQuoteError unitRoleUnused .complete) favorableCompleteS25Before [.query 1] (.hydeRetriever 1) = 0 := by
    apply control_penalty_empty_of_prior_terminal .complete savedCref uniformQuoteError favorableCompleteS25Before [.query 1] (.hydeRetriever 1) 8 (by decide)
    · decide
    · decide
  unfold indexScore
  rw [hs,hp,hn,hz]
  simp only [BackupStat.mean]
  norm_num

theorem favorableCompleteS25D1I1 : indexScore (7/5) (controlPenalty savedCref uniformQuoteError unitRoleUnused .complete) favorableCompleteS25Before [.query 1] (.hydeRetriever 0) = treeIndex ((0/1)/5) (7/5) 0 17 5 := by
  have hs : replayBackup favorableCompleteS25Before emptyStatistics ([.query 1]++[.hydeRetriever 0]) = ⟨5,(0/1)⟩ := by
    rw [replayBackup_empty_closed_form]
    simp +decide [backedEvents,favorableCompleteS25Before,favorableCompleteProposal,favorableCompleteEvent1,favorableCompleteEvent2,favorableCompleteEvent3,favorableCompleteEvent4,favorableCompleteEvent5,favorableCompleteEvent6,favorableCompleteEvent7,favorableCompleteEvent8,favorableCompleteEvent9,favorableCompleteEvent10,favorableCompleteEvent11,favorableCompleteEvent12,favorableCompleteEvent13,favorableCompleteEvent14,favorableCompleteEvent15,favorableCompleteEvent16,favorableCompleteEvent17,favorableCompleteEvent18,favorableCompleteEvent19,favorableCompleteEvent20,favorableCompleteEvent21,favorableCompleteEvent22,favorableCompleteEvent23,favorableCompleteEvent24,taskReward]
    <;> norm_num
  have hp : rawVisits favorableCompleteS25Before [.query 1] = 17 := by decide
  have hn : rawVisits favorableCompleteS25Before ([.query 1]++[.hydeRetriever 0]) = 5 := by decide
  have hz : (controlPenalty savedCref uniformQuoteError unitRoleUnused .complete) favorableCompleteS25Before [.query 1] (.hydeRetriever 0) = 0 := by
    apply control_penalty_empty_of_prior_terminal .complete savedCref uniformQuoteError favorableCompleteS25Before [.query 1] (.hydeRetriever 0) 1 (by decide)
    · decide
    · decide
  unfold indexScore
  rw [hs,hp,hn,hz]
  simp only [BackupStat.mean]
  norm_num

theorem favorableCompleteS25D1I2 : indexScore (7/5) (controlPenalty savedCref uniformQuoteError unitRoleUnused .complete) favorableCompleteS25Before [.query 1] (.hydeRetriever 2) = treeIndex ((0/1)/4) (7/5) 0 17 4 := by
  have hs : replayBackup favorableCompleteS25Before emptyStatistics ([.query 1]++[.hydeRetriever 2]) = ⟨4,(0/1)⟩ := by
    rw [replayBackup_empty_closed_form]
    simp +decide [backedEvents,favorableCompleteS25Before,favorableCompleteProposal,favorableCompleteEvent1,favorableCompleteEvent2,favorableCompleteEvent3,favorableCompleteEvent4,favorableCompleteEvent5,favorableCompleteEvent6,favorableCompleteEvent7,favorableCompleteEvent8,favorableCompleteEvent9,favorableCompleteEvent10,favorableCompleteEvent11,favorableCompleteEvent12,favorableCompleteEvent13,favorableCompleteEvent14,favorableCompleteEvent15,favorableCompleteEvent16,favorableCompleteEvent17,favorableCompleteEvent18,favorableCompleteEvent19,favorableCompleteEvent20,favorableCompleteEvent21,favorableCompleteEvent22,favorableCompleteEvent23,favorableCompleteEvent24,taskReward]
    <;> norm_num
  have hp : rawVisits favorableCompleteS25Before [.query 1] = 17 := by decide
  have hn : rawVisits favorableCompleteS25Before ([.query 1]++[.hydeRetriever 2]) = 4 := by decide
  have hz : (controlPenalty savedCref uniformQuoteError unitRoleUnused .complete) favorableCompleteS25Before [.query 1] (.hydeRetriever 2) = 0 := by
    apply control_penalty_empty_of_prior_terminal .complete savedCref uniformQuoteError favorableCompleteS25Before [.query 1] (.hydeRetriever 2) 10 (by decide)
    · decide
    · decide
  unfold indexScore
  rw [hs,hp,hn,hz]
  simp only [BackupStat.mean]
  norm_num

theorem favorableCompleteS25D1Cmp0 : indexScore (7/5) (controlPenalty savedCref uniformQuoteError unitRoleUnused .complete) favorableCompleteS25Before [.query 1] (.hydeRetriever 1) < indexScore (7/5) (controlPenalty savedCref uniformQuoteError unitRoleUnused .complete) favorableCompleteS25Before [.query 1] (.hydeRetriever 2) := by
  rw [favorableCompleteS25D1I0,favorableCompleteS25D1I2]
  have h := index_strict_order_from_intervals ((0/1)/4) ((3/2)/7) 0 0 (29751911/25000000) (4498067/5000000)
    (treeBonus (7/5) 17 4) (treeBonus (7/5) 17 7)
    (trajectory_bonus_17_4).1 (trajectory_bonus_17_7).2 (by norm_num)
  simpa only [treeIndex,sub_zero] using h

theorem favorableCompleteS25D1Cmp1 : indexScore (7/5) (controlPenalty savedCref uniformQuoteError unitRoleUnused .complete) favorableCompleteS25Before [.query 1] (.hydeRetriever 0) < indexScore (7/5) (controlPenalty savedCref uniformQuoteError unitRoleUnused .complete) favorableCompleteS25Before [.query 1] (.hydeRetriever 2) := by
  rw [favorableCompleteS25D1I1,favorableCompleteS25D1I2]
  have h := index_strict_order_from_intervals ((0/1)/4) ((0/1)/5) 0 0 (29751911/25000000) (53221847/50000000)
    (treeBonus (7/5) 17 4) (treeBonus (7/5) 17 5)
    (trajectory_bonus_17_4).1 (trajectory_bonus_17_5).2 (by norm_num)
  simpa only [treeIndex,sub_zero] using h

theorem favorableCompleteS25Choice1 : nativeFirstChoice (indexScore (7/5) (controlPenalty savedCref uniformQuoteError unitRoleUnused .complete) favorableCompleteS25Before [.query 1]) favorableCompleteS25Before [.query 1] = .hydeRetriever 2 := by
  apply visited_choice_from_ordered_certificate _ _ [.query 1] [.hydeRetriever 1,.hydeRetriever 0] [] (.hydeRetriever 2) (by decide)
  · intro a ha
    have ho : orderedLegalAvailable [.query 1] = [.hydeRetriever 1,.hydeRetriever 0,.hydeRetriever 2] := by decide
    rw [ho] at ha
    simp only [List.mem_cons,List.not_mem_nil,or_false] at ha
    rcases ha with rfl | rfl | rfl <;> decide
  · intro a ha
    simp only [List.mem_cons,List.not_mem_nil,or_false] at ha
    rcases ha with rfl | rfl
    · exact favorableCompleteS25D1Cmp0
    · exact favorableCompleteS25D1Cmp1
  · simp

theorem favorableCompleteS25ActualEvent : nativeEvent budgetTape (7/5) (controlPenalty savedCref uniformQuoteError unitRoleUnused .complete)
    (taskReward false (2/5) (1/2)) favorableCompleteS25Before = favorableCompleteEvent25 := by
  have hs0 := native_select_existing_step budgetTape (7/5) (controlPenalty savedCref uniformQuoteError unitRoleUnused .complete) favorableCompleteS25Before 8 [] (.query 1)
    (by decide) (by decide) favorableCompleteS25Choice0
  have hs1 := native_select_existing_step budgetTape (7/5) (controlPenalty savedCref uniformQuoteError unitRoleUnused .complete) favorableCompleteS25Before 7 [.query 1] (.hydeRetriever 2)
    (by decide) (by decide) favorableCompleteS25Choice1
  have hnew := native_select_new_step budgetTape (7/5) (controlPenalty savedCref uniformQuoteError unitRoleUnused .complete) favorableCompleteS25Before 6 [.query 1,.hydeRetriever 2]
    [.selection 3] (.selection 3) (by decide) (by decide) (by decide) (by decide)
  have hs : nativeSelect budgetTape (7/5) (controlPenalty savedCref uniformQuoteError unitRoleUnused .complete) favorableCompleteS25Before 9 [] = [.query 1,.hydeRetriever 2,.selection 3] := by
    rw [hs0]
    change nativeSelect budgetTape (7/5) (controlPenalty savedCref uniformQuoteError unitRoleUnused .complete) favorableCompleteS25Before 8 [.query 1] = _
    rw [hs1]
    change nativeSelect budgetTape (7/5) (controlPenalty savedCref uniformQuoteError unitRoleUnused .complete) favorableCompleteS25Before 7 [.query 1,.hydeRetriever 2] = _
    rw [hnew] <;> rfl
  have hr : repairedRollout budgetTape favorableCompleteS25Before 9 [.query 1,.hydeRetriever 2,.selection 3] = [.query 1,.hydeRetriever 2,.selection 3,.width 0,.stop,.reranker 0,.topm 0,.context 0,.answer 0] := by decide
  simp only [nativeEvent,hs,hr]
  rfl

def favorableCompleteS26Before := favorableCompleteProposal.take 25

theorem favorableCompleteS26Choice0 : nativeFirstChoice (indexScore (7/5) (controlPenalty savedCref uniformQuoteError unitRoleUnused .complete) favorableCompleteS26Before []) favorableCompleteS26Before [] = .query 1 := by
  apply complete_root_from_physical_gap favorableCompleteS26Before (favorableComplete_prefix_rewards 25) (by decide)
  · intro q; fin_cases q <;> decide
  · decide
  · intro q hq
    exact AgentUCTNextExact.favorable_complete_normal_root_physical_quote_exact 25 (by omega) q hq

theorem favorableCompleteS26D1I0 : indexScore (7/5) (controlPenalty savedCref uniformQuoteError unitRoleUnused .complete) favorableCompleteS26Before [.query 1] (.hydeRetriever 1) = treeIndex ((3/2)/7) (7/5) 0 18 7 := by
  have hs : replayBackup favorableCompleteS26Before emptyStatistics ([.query 1]++[.hydeRetriever 1]) = ⟨7,(3/2)⟩ := by
    rw [replayBackup_empty_closed_form]
    simp +decide [backedEvents,favorableCompleteS26Before,favorableCompleteProposal,favorableCompleteEvent1,favorableCompleteEvent2,favorableCompleteEvent3,favorableCompleteEvent4,favorableCompleteEvent5,favorableCompleteEvent6,favorableCompleteEvent7,favorableCompleteEvent8,favorableCompleteEvent9,favorableCompleteEvent10,favorableCompleteEvent11,favorableCompleteEvent12,favorableCompleteEvent13,favorableCompleteEvent14,favorableCompleteEvent15,favorableCompleteEvent16,favorableCompleteEvent17,favorableCompleteEvent18,favorableCompleteEvent19,favorableCompleteEvent20,favorableCompleteEvent21,favorableCompleteEvent22,favorableCompleteEvent23,favorableCompleteEvent24,favorableCompleteEvent25,taskReward]
    <;> norm_num
  have hp : rawVisits favorableCompleteS26Before [.query 1] = 18 := by decide
  have hn : rawVisits favorableCompleteS26Before ([.query 1]++[.hydeRetriever 1]) = 7 := by decide
  have hz : (controlPenalty savedCref uniformQuoteError unitRoleUnused .complete) favorableCompleteS26Before [.query 1] (.hydeRetriever 1) = 0 := by
    apply control_penalty_empty_of_prior_terminal .complete savedCref uniformQuoteError favorableCompleteS26Before [.query 1] (.hydeRetriever 1) 8 (by decide)
    · decide
    · decide
  unfold indexScore
  rw [hs,hp,hn,hz]
  simp only [BackupStat.mean]
  norm_num

theorem favorableCompleteS26D1I1 : indexScore (7/5) (controlPenalty savedCref uniformQuoteError unitRoleUnused .complete) favorableCompleteS26Before [.query 1] (.hydeRetriever 0) = treeIndex ((0/1)/5) (7/5) 0 18 5 := by
  have hs : replayBackup favorableCompleteS26Before emptyStatistics ([.query 1]++[.hydeRetriever 0]) = ⟨5,(0/1)⟩ := by
    rw [replayBackup_empty_closed_form]
    simp +decide [backedEvents,favorableCompleteS26Before,favorableCompleteProposal,favorableCompleteEvent1,favorableCompleteEvent2,favorableCompleteEvent3,favorableCompleteEvent4,favorableCompleteEvent5,favorableCompleteEvent6,favorableCompleteEvent7,favorableCompleteEvent8,favorableCompleteEvent9,favorableCompleteEvent10,favorableCompleteEvent11,favorableCompleteEvent12,favorableCompleteEvent13,favorableCompleteEvent14,favorableCompleteEvent15,favorableCompleteEvent16,favorableCompleteEvent17,favorableCompleteEvent18,favorableCompleteEvent19,favorableCompleteEvent20,favorableCompleteEvent21,favorableCompleteEvent22,favorableCompleteEvent23,favorableCompleteEvent24,favorableCompleteEvent25,taskReward]
    <;> norm_num
  have hp : rawVisits favorableCompleteS26Before [.query 1] = 18 := by decide
  have hn : rawVisits favorableCompleteS26Before ([.query 1]++[.hydeRetriever 0]) = 5 := by decide
  have hz : (controlPenalty savedCref uniformQuoteError unitRoleUnused .complete) favorableCompleteS26Before [.query 1] (.hydeRetriever 0) = 0 := by
    apply control_penalty_empty_of_prior_terminal .complete savedCref uniformQuoteError favorableCompleteS26Before [.query 1] (.hydeRetriever 0) 1 (by decide)
    · decide
    · decide
  unfold indexScore
  rw [hs,hp,hn,hz]
  simp only [BackupStat.mean]
  norm_num

theorem favorableCompleteS26D1I2 : indexScore (7/5) (controlPenalty savedCref uniformQuoteError unitRoleUnused .complete) favorableCompleteS26Before [.query 1] (.hydeRetriever 2) = treeIndex ((0/1)/5) (7/5) 0 18 5 := by
  have hs : replayBackup favorableCompleteS26Before emptyStatistics ([.query 1]++[.hydeRetriever 2]) = ⟨5,(0/1)⟩ := by
    rw [replayBackup_empty_closed_form]
    simp +decide [backedEvents,favorableCompleteS26Before,favorableCompleteProposal,favorableCompleteEvent1,favorableCompleteEvent2,favorableCompleteEvent3,favorableCompleteEvent4,favorableCompleteEvent5,favorableCompleteEvent6,favorableCompleteEvent7,favorableCompleteEvent8,favorableCompleteEvent9,favorableCompleteEvent10,favorableCompleteEvent11,favorableCompleteEvent12,favorableCompleteEvent13,favorableCompleteEvent14,favorableCompleteEvent15,favorableCompleteEvent16,favorableCompleteEvent17,favorableCompleteEvent18,favorableCompleteEvent19,favorableCompleteEvent20,favorableCompleteEvent21,favorableCompleteEvent22,favorableCompleteEvent23,favorableCompleteEvent24,favorableCompleteEvent25,taskReward]
    <;> norm_num
  have hp : rawVisits favorableCompleteS26Before [.query 1] = 18 := by decide
  have hn : rawVisits favorableCompleteS26Before ([.query 1]++[.hydeRetriever 2]) = 5 := by decide
  have hz : (controlPenalty savedCref uniformQuoteError unitRoleUnused .complete) favorableCompleteS26Before [.query 1] (.hydeRetriever 2) = 0 := by
    apply control_penalty_empty_of_prior_terminal .complete savedCref uniformQuoteError favorableCompleteS26Before [.query 1] (.hydeRetriever 2) 10 (by decide)
    · decide
    · decide
  unfold indexScore
  rw [hs,hp,hn,hz]
  simp only [BackupStat.mean]
  norm_num

theorem favorableCompleteS26D1Cmp1 : indexScore (7/5) (controlPenalty savedCref uniformQuoteError unitRoleUnused .complete) favorableCompleteS26Before [.query 1] (.hydeRetriever 0) ≤ indexScore (7/5) (controlPenalty savedCref uniformQuoteError unitRoleUnused .complete) favorableCompleteS26Before [.query 1] (.hydeRetriever 1) := by
  rw [favorableCompleteS26D1I1,favorableCompleteS26D1I0]
  have h := index_weak_order_from_intervals ((3/2)/7) ((0/1)/5) 0 0 (45399417/50000000) (53717321/50000000)
    (treeBonus (7/5) 18 7) (treeBonus (7/5) 18 5)
    (trajectory_bonus_18_7).1 (trajectory_bonus_18_5).2 (by norm_num)
  simpa only [treeIndex,sub_zero] using h

theorem favorableCompleteS26D1Cmp2 : indexScore (7/5) (controlPenalty savedCref uniformQuoteError unitRoleUnused .complete) favorableCompleteS26Before [.query 1] (.hydeRetriever 2) ≤ indexScore (7/5) (controlPenalty savedCref uniformQuoteError unitRoleUnused .complete) favorableCompleteS26Before [.query 1] (.hydeRetriever 1) := by
  rw [favorableCompleteS26D1I2,favorableCompleteS26D1I0]
  have h := index_weak_order_from_intervals ((3/2)/7) ((0/1)/5) 0 0 (45399417/50000000) (53717321/50000000)
    (treeBonus (7/5) 18 7) (treeBonus (7/5) 18 5)
    (trajectory_bonus_18_7).1 (trajectory_bonus_18_5).2 (by norm_num)
  simpa only [treeIndex,sub_zero] using h

theorem favorableCompleteS26Choice1 : nativeFirstChoice (indexScore (7/5) (controlPenalty savedCref uniformQuoteError unitRoleUnused .complete) favorableCompleteS26Before [.query 1]) favorableCompleteS26Before [.query 1] = .hydeRetriever 1 := by
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
    · exact favorableCompleteS26D1Cmp1
    · exact favorableCompleteS26D1Cmp2

theorem favorableCompleteS26D2I0 : indexScore (7/5) (controlPenalty savedCref uniformQuoteError unitRoleUnused .complete) favorableCompleteS26Before [.query 1,.hydeRetriever 1] (.selection 1) = treeIndex ((0/1)/2) (7/5) 0 7 2 := by
  have hs : replayBackup favorableCompleteS26Before emptyStatistics ([.query 1,.hydeRetriever 1]++[.selection 1]) = ⟨2,(0/1)⟩ := by
    rw [replayBackup_empty_closed_form]
    simp +decide [backedEvents,favorableCompleteS26Before,favorableCompleteProposal,favorableCompleteEvent1,favorableCompleteEvent2,favorableCompleteEvent3,favorableCompleteEvent4,favorableCompleteEvent5,favorableCompleteEvent6,favorableCompleteEvent7,favorableCompleteEvent8,favorableCompleteEvent9,favorableCompleteEvent10,favorableCompleteEvent11,favorableCompleteEvent12,favorableCompleteEvent13,favorableCompleteEvent14,favorableCompleteEvent15,favorableCompleteEvent16,favorableCompleteEvent17,favorableCompleteEvent18,favorableCompleteEvent19,favorableCompleteEvent20,favorableCompleteEvent21,favorableCompleteEvent22,favorableCompleteEvent23,favorableCompleteEvent24,favorableCompleteEvent25,taskReward]
    <;> norm_num
  have hp : rawVisits favorableCompleteS26Before [.query 1,.hydeRetriever 1] = 7 := by decide
  have hn : rawVisits favorableCompleteS26Before ([.query 1,.hydeRetriever 1]++[.selection 1]) = 2 := by decide
  have hz : (controlPenalty savedCref uniformQuoteError unitRoleUnused .complete) favorableCompleteS26Before [.query 1,.hydeRetriever 1] (.selection 1) = 0 := by
    apply control_penalty_empty_of_prior_terminal .complete savedCref uniformQuoteError favorableCompleteS26Before [.query 1,.hydeRetriever 1] (.selection 1) 14 (by decide)
    · decide
    · decide
  unfold indexScore
  rw [hs,hp,hn,hz]
  simp only [BackupStat.mean]
  norm_num

theorem favorableCompleteS26D2I1 : indexScore (7/5) (controlPenalty savedCref uniformQuoteError unitRoleUnused .complete) favorableCompleteS26Before [.query 1,.hydeRetriever 1] (.selection 2) = treeIndex ((0/1)/1) (7/5) 0 7 1 := by
  have hs : replayBackup favorableCompleteS26Before emptyStatistics ([.query 1,.hydeRetriever 1]++[.selection 2]) = ⟨1,(0/1)⟩ := by
    rw [replayBackup_empty_closed_form]
    simp +decide [backedEvents,favorableCompleteS26Before,favorableCompleteProposal,favorableCompleteEvent1,favorableCompleteEvent2,favorableCompleteEvent3,favorableCompleteEvent4,favorableCompleteEvent5,favorableCompleteEvent6,favorableCompleteEvent7,favorableCompleteEvent8,favorableCompleteEvent9,favorableCompleteEvent10,favorableCompleteEvent11,favorableCompleteEvent12,favorableCompleteEvent13,favorableCompleteEvent14,favorableCompleteEvent15,favorableCompleteEvent16,favorableCompleteEvent17,favorableCompleteEvent18,favorableCompleteEvent19,favorableCompleteEvent20,favorableCompleteEvent21,favorableCompleteEvent22,favorableCompleteEvent23,favorableCompleteEvent24,favorableCompleteEvent25,taskReward]
    <;> norm_num
  have hp : rawVisits favorableCompleteS26Before [.query 1,.hydeRetriever 1] = 7 := by decide
  have hn : rawVisits favorableCompleteS26Before ([.query 1,.hydeRetriever 1]++[.selection 2]) = 1 := by decide
  have hz : (controlPenalty savedCref uniformQuoteError unitRoleUnused .complete) favorableCompleteS26Before [.query 1,.hydeRetriever 1] (.selection 2) = 0 := by
    apply control_penalty_empty_of_prior_terminal .complete savedCref uniformQuoteError favorableCompleteS26Before [.query 1,.hydeRetriever 1] (.selection 2) 15 (by decide)
    · decide
    · decide
  unfold indexScore
  rw [hs,hp,hn,hz]
  simp only [BackupStat.mean]
  norm_num

theorem favorableCompleteS26D2I2 : indexScore (7/5) (controlPenalty savedCref uniformQuoteError unitRoleUnused .complete) favorableCompleteS26Before [.query 1,.hydeRetriever 1] (.selection 3) = treeIndex ((0/1)/1) (7/5) 0 7 1 := by
  have hs : replayBackup favorableCompleteS26Before emptyStatistics ([.query 1,.hydeRetriever 1]++[.selection 3]) = ⟨1,(0/1)⟩ := by
    rw [replayBackup_empty_closed_form]
    simp +decide [backedEvents,favorableCompleteS26Before,favorableCompleteProposal,favorableCompleteEvent1,favorableCompleteEvent2,favorableCompleteEvent3,favorableCompleteEvent4,favorableCompleteEvent5,favorableCompleteEvent6,favorableCompleteEvent7,favorableCompleteEvent8,favorableCompleteEvent9,favorableCompleteEvent10,favorableCompleteEvent11,favorableCompleteEvent12,favorableCompleteEvent13,favorableCompleteEvent14,favorableCompleteEvent15,favorableCompleteEvent16,favorableCompleteEvent17,favorableCompleteEvent18,favorableCompleteEvent19,favorableCompleteEvent20,favorableCompleteEvent21,favorableCompleteEvent22,favorableCompleteEvent23,favorableCompleteEvent24,favorableCompleteEvent25,taskReward]
    <;> norm_num
  have hp : rawVisits favorableCompleteS26Before [.query 1,.hydeRetriever 1] = 7 := by decide
  have hn : rawVisits favorableCompleteS26Before ([.query 1,.hydeRetriever 1]++[.selection 3]) = 1 := by decide
  have hz : (controlPenalty savedCref uniformQuoteError unitRoleUnused .complete) favorableCompleteS26Before [.query 1,.hydeRetriever 1] (.selection 3) = 0 := by
    apply control_penalty_empty_of_prior_terminal .complete savedCref uniformQuoteError favorableCompleteS26Before [.query 1,.hydeRetriever 1] (.selection 3) 18 (by decide)
    · decide
    · decide
  unfold indexScore
  rw [hs,hp,hn,hz]
  simp only [BackupStat.mean]
  norm_num

theorem favorableCompleteS26D2I3 : indexScore (7/5) (controlPenalty savedCref uniformQuoteError unitRoleUnused .complete) favorableCompleteS26Before [.query 1,.hydeRetriever 1] (.selection 0) = treeIndex ((1/1)/2) (7/5) 0 7 2 := by
  have hs : replayBackup favorableCompleteS26Before emptyStatistics ([.query 1,.hydeRetriever 1]++[.selection 0]) = ⟨2,(1/1)⟩ := by
    rw [replayBackup_empty_closed_form]
    simp +decide [backedEvents,favorableCompleteS26Before,favorableCompleteProposal,favorableCompleteEvent1,favorableCompleteEvent2,favorableCompleteEvent3,favorableCompleteEvent4,favorableCompleteEvent5,favorableCompleteEvent6,favorableCompleteEvent7,favorableCompleteEvent8,favorableCompleteEvent9,favorableCompleteEvent10,favorableCompleteEvent11,favorableCompleteEvent12,favorableCompleteEvent13,favorableCompleteEvent14,favorableCompleteEvent15,favorableCompleteEvent16,favorableCompleteEvent17,favorableCompleteEvent18,favorableCompleteEvent19,favorableCompleteEvent20,favorableCompleteEvent21,favorableCompleteEvent22,favorableCompleteEvent23,favorableCompleteEvent24,favorableCompleteEvent25,taskReward]
    <;> norm_num
  have hp : rawVisits favorableCompleteS26Before [.query 1,.hydeRetriever 1] = 7 := by decide
  have hn : rawVisits favorableCompleteS26Before ([.query 1,.hydeRetriever 1]++[.selection 0]) = 2 := by decide
  have hz : (controlPenalty savedCref uniformQuoteError unitRoleUnused .complete) favorableCompleteS26Before [.query 1,.hydeRetriever 1] (.selection 0) = 0 := by
    apply control_penalty_empty_of_prior_terminal .complete savedCref uniformQuoteError favorableCompleteS26Before [.query 1,.hydeRetriever 1] (.selection 0) 8 (by decide)
    · decide
    · decide
  unfold indexScore
  rw [hs,hp,hn,hz]
  simp only [BackupStat.mean]
  norm_num

theorem favorableCompleteS26D2Cmp0 : indexScore (7/5) (controlPenalty savedCref uniformQuoteError unitRoleUnused .complete) favorableCompleteS26Before [.query 1,.hydeRetriever 1] (.selection 1) < indexScore (7/5) (controlPenalty savedCref uniformQuoteError unitRoleUnused .complete) favorableCompleteS26Before [.query 1,.hydeRetriever 1] (.selection 2) := by
  rw [favorableCompleteS26D2I0,favorableCompleteS26D2I1]
  have h := index_strict_order_from_intervals ((0/1)/1) ((0/1)/2) 0 0 (25235469/12500000) (71376697/50000000)
    (treeBonus (7/5) 7 1) (treeBonus (7/5) 7 2)
    (trajectory_bonus_7_1).1 (trajectory_bonus_7_2).2 (by norm_num)
  simpa only [treeIndex,sub_zero] using h

theorem favorableCompleteS26D2Cmp2 : indexScore (7/5) (controlPenalty savedCref uniformQuoteError unitRoleUnused .complete) favorableCompleteS26Before [.query 1,.hydeRetriever 1] (.selection 3) ≤ indexScore (7/5) (controlPenalty savedCref uniformQuoteError unitRoleUnused .complete) favorableCompleteS26Before [.query 1,.hydeRetriever 1] (.selection 2) := by
  rw [favorableCompleteS26D2I2,favorableCompleteS26D2I1]

theorem favorableCompleteS26D2Cmp3 : indexScore (7/5) (controlPenalty savedCref uniformQuoteError unitRoleUnused .complete) favorableCompleteS26Before [.query 1,.hydeRetriever 1] (.selection 0) ≤ indexScore (7/5) (controlPenalty savedCref uniformQuoteError unitRoleUnused .complete) favorableCompleteS26Before [.query 1,.hydeRetriever 1] (.selection 2) := by
  rw [favorableCompleteS26D2I3,favorableCompleteS26D2I1]
  have h := index_weak_order_from_intervals ((0/1)/1) ((1/1)/2) 0 0 (25235469/12500000) (71376697/50000000)
    (treeBonus (7/5) 7 1) (treeBonus (7/5) 7 2)
    (trajectory_bonus_7_1).1 (trajectory_bonus_7_2).2 (by norm_num)
  simpa only [treeIndex,sub_zero] using h

theorem favorableCompleteS26Choice2 : nativeFirstChoice (indexScore (7/5) (controlPenalty savedCref uniformQuoteError unitRoleUnused .complete) favorableCompleteS26Before [.query 1,.hydeRetriever 1]) favorableCompleteS26Before [.query 1,.hydeRetriever 1] = .selection 2 := by
  apply visited_choice_from_ordered_certificate _ _ [.query 1,.hydeRetriever 1] [.selection 1] [.selection 3,.selection 0] (.selection 2) (by decide)
  · intro a ha
    have ho : orderedLegalAvailable [.query 1,.hydeRetriever 1] = [.selection 1,.selection 2,.selection 3,.selection 0] := by decide
    rw [ho] at ha
    simp only [List.mem_cons,List.not_mem_nil,or_false] at ha
    rcases ha with rfl | rfl | rfl | rfl <;> decide
  · intro a ha
    simp only [List.mem_cons,List.not_mem_nil,or_false] at ha
    rcases ha with rfl
    · exact favorableCompleteS26D2Cmp0
  · intro a ha
    simp only [List.mem_cons,List.not_mem_nil,or_false] at ha
    rcases ha with rfl | rfl
    · exact favorableCompleteS26D2Cmp2
    · exact favorableCompleteS26D2Cmp3

theorem favorableCompleteS26ActualEvent : nativeEvent budgetTape (7/5) (controlPenalty savedCref uniformQuoteError unitRoleUnused .complete)
    (taskReward false (2/5) (1/2)) favorableCompleteS26Before = favorableCompleteEvent26 := by
  have hs0 := native_select_existing_step budgetTape (7/5) (controlPenalty savedCref uniformQuoteError unitRoleUnused .complete) favorableCompleteS26Before 8 [] (.query 1)
    (by decide) (by decide) favorableCompleteS26Choice0
  have hs1 := native_select_existing_step budgetTape (7/5) (controlPenalty savedCref uniformQuoteError unitRoleUnused .complete) favorableCompleteS26Before 7 [.query 1] (.hydeRetriever 1)
    (by decide) (by decide) favorableCompleteS26Choice1
  have hs2 := native_select_existing_step budgetTape (7/5) (controlPenalty savedCref uniformQuoteError unitRoleUnused .complete) favorableCompleteS26Before 6 [.query 1,.hydeRetriever 1] (.selection 2)
    (by decide) (by decide) favorableCompleteS26Choice2
  have hnew := native_select_new_step budgetTape (7/5) (controlPenalty savedCref uniformQuoteError unitRoleUnused .complete) favorableCompleteS26Before 5 [.query 1,.hydeRetriever 1,.selection 2]
    [.width 3,.width 0,.width 1,.width 2] (.width 0) (by decide) (by decide) (by decide) (by decide)
  have hs : nativeSelect budgetTape (7/5) (controlPenalty savedCref uniformQuoteError unitRoleUnused .complete) favorableCompleteS26Before 9 [] = [.query 1,.hydeRetriever 1,.selection 2,.width 0] := by
    rw [hs0]
    change nativeSelect budgetTape (7/5) (controlPenalty savedCref uniformQuoteError unitRoleUnused .complete) favorableCompleteS26Before 8 [.query 1] = _
    rw [hs1]
    change nativeSelect budgetTape (7/5) (controlPenalty savedCref uniformQuoteError unitRoleUnused .complete) favorableCompleteS26Before 7 [.query 1,.hydeRetriever 1] = _
    rw [hs2]
    change nativeSelect budgetTape (7/5) (controlPenalty savedCref uniformQuoteError unitRoleUnused .complete) favorableCompleteS26Before 6 [.query 1,.hydeRetriever 1,.selection 2] = _
    rw [hnew] <;> rfl
  have hr : repairedRollout budgetTape favorableCompleteS26Before 9 [.query 1,.hydeRetriever 1,.selection 2,.width 0] = [.query 1,.hydeRetriever 1,.selection 2,.width 0,.stop,.reranker 0,.topm 0,.context 0,.answer 0] := by decide
  simp only [nativeEvent,hs,hr]
  rfl

def favorableCompleteS27Before := favorableCompleteProposal.take 26

theorem favorableCompleteS27Choice0 : nativeFirstChoice (indexScore (7/5) (controlPenalty savedCref uniformQuoteError unitRoleUnused .complete) favorableCompleteS27Before []) favorableCompleteS27Before [] = .query 1 := by
  apply complete_root_from_physical_gap favorableCompleteS27Before (favorableComplete_prefix_rewards 26) (by decide)
  · intro q; fin_cases q <;> decide
  · decide
  · intro q hq
    exact AgentUCTNextExact.favorable_complete_normal_root_physical_quote_exact 26 (by omega) q hq

theorem favorableCompleteS27D1I0 : indexScore (7/5) (controlPenalty savedCref uniformQuoteError unitRoleUnused .complete) favorableCompleteS27Before [.query 1] (.hydeRetriever 1) = treeIndex ((3/2)/8) (7/5) 0 19 8 := by
  have hs : replayBackup favorableCompleteS27Before emptyStatistics ([.query 1]++[.hydeRetriever 1]) = ⟨8,(3/2)⟩ := by
    rw [replayBackup_empty_closed_form]
    simp +decide [backedEvents,favorableCompleteS27Before,favorableCompleteProposal,favorableCompleteEvent1,favorableCompleteEvent2,favorableCompleteEvent3,favorableCompleteEvent4,favorableCompleteEvent5,favorableCompleteEvent6,favorableCompleteEvent7,favorableCompleteEvent8,favorableCompleteEvent9,favorableCompleteEvent10,favorableCompleteEvent11,favorableCompleteEvent12,favorableCompleteEvent13,favorableCompleteEvent14,favorableCompleteEvent15,favorableCompleteEvent16,favorableCompleteEvent17,favorableCompleteEvent18,favorableCompleteEvent19,favorableCompleteEvent20,favorableCompleteEvent21,favorableCompleteEvent22,favorableCompleteEvent23,favorableCompleteEvent24,favorableCompleteEvent25,favorableCompleteEvent26,taskReward]
    <;> norm_num
  have hp : rawVisits favorableCompleteS27Before [.query 1] = 19 := by decide
  have hn : rawVisits favorableCompleteS27Before ([.query 1]++[.hydeRetriever 1]) = 8 := by decide
  have hz : (controlPenalty savedCref uniformQuoteError unitRoleUnused .complete) favorableCompleteS27Before [.query 1] (.hydeRetriever 1) = 0 := by
    apply control_penalty_empty_of_prior_terminal .complete savedCref uniformQuoteError favorableCompleteS27Before [.query 1] (.hydeRetriever 1) 8 (by decide)
    · decide
    · decide
  unfold indexScore
  rw [hs,hp,hn,hz]
  simp only [BackupStat.mean]
  norm_num

theorem favorableCompleteS27D1I1 : indexScore (7/5) (controlPenalty savedCref uniformQuoteError unitRoleUnused .complete) favorableCompleteS27Before [.query 1] (.hydeRetriever 0) = treeIndex ((0/1)/5) (7/5) 0 19 5 := by
  have hs : replayBackup favorableCompleteS27Before emptyStatistics ([.query 1]++[.hydeRetriever 0]) = ⟨5,(0/1)⟩ := by
    rw [replayBackup_empty_closed_form]
    simp +decide [backedEvents,favorableCompleteS27Before,favorableCompleteProposal,favorableCompleteEvent1,favorableCompleteEvent2,favorableCompleteEvent3,favorableCompleteEvent4,favorableCompleteEvent5,favorableCompleteEvent6,favorableCompleteEvent7,favorableCompleteEvent8,favorableCompleteEvent9,favorableCompleteEvent10,favorableCompleteEvent11,favorableCompleteEvent12,favorableCompleteEvent13,favorableCompleteEvent14,favorableCompleteEvent15,favorableCompleteEvent16,favorableCompleteEvent17,favorableCompleteEvent18,favorableCompleteEvent19,favorableCompleteEvent20,favorableCompleteEvent21,favorableCompleteEvent22,favorableCompleteEvent23,favorableCompleteEvent24,favorableCompleteEvent25,favorableCompleteEvent26,taskReward]
    <;> norm_num
  have hp : rawVisits favorableCompleteS27Before [.query 1] = 19 := by decide
  have hn : rawVisits favorableCompleteS27Before ([.query 1]++[.hydeRetriever 0]) = 5 := by decide
  have hz : (controlPenalty savedCref uniformQuoteError unitRoleUnused .complete) favorableCompleteS27Before [.query 1] (.hydeRetriever 0) = 0 := by
    apply control_penalty_empty_of_prior_terminal .complete savedCref uniformQuoteError favorableCompleteS27Before [.query 1] (.hydeRetriever 0) 1 (by decide)
    · decide
    · decide
  unfold indexScore
  rw [hs,hp,hn,hz]
  simp only [BackupStat.mean]
  norm_num

theorem favorableCompleteS27D1I2 : indexScore (7/5) (controlPenalty savedCref uniformQuoteError unitRoleUnused .complete) favorableCompleteS27Before [.query 1] (.hydeRetriever 2) = treeIndex ((0/1)/5) (7/5) 0 19 5 := by
  have hs : replayBackup favorableCompleteS27Before emptyStatistics ([.query 1]++[.hydeRetriever 2]) = ⟨5,(0/1)⟩ := by
    rw [replayBackup_empty_closed_form]
    simp +decide [backedEvents,favorableCompleteS27Before,favorableCompleteProposal,favorableCompleteEvent1,favorableCompleteEvent2,favorableCompleteEvent3,favorableCompleteEvent4,favorableCompleteEvent5,favorableCompleteEvent6,favorableCompleteEvent7,favorableCompleteEvent8,favorableCompleteEvent9,favorableCompleteEvent10,favorableCompleteEvent11,favorableCompleteEvent12,favorableCompleteEvent13,favorableCompleteEvent14,favorableCompleteEvent15,favorableCompleteEvent16,favorableCompleteEvent17,favorableCompleteEvent18,favorableCompleteEvent19,favorableCompleteEvent20,favorableCompleteEvent21,favorableCompleteEvent22,favorableCompleteEvent23,favorableCompleteEvent24,favorableCompleteEvent25,favorableCompleteEvent26,taskReward]
    <;> norm_num
  have hp : rawVisits favorableCompleteS27Before [.query 1] = 19 := by decide
  have hn : rawVisits favorableCompleteS27Before ([.query 1]++[.hydeRetriever 2]) = 5 := by decide
  have hz : (controlPenalty savedCref uniformQuoteError unitRoleUnused .complete) favorableCompleteS27Before [.query 1] (.hydeRetriever 2) = 0 := by
    apply control_penalty_empty_of_prior_terminal .complete savedCref uniformQuoteError favorableCompleteS27Before [.query 1] (.hydeRetriever 2) 10 (by decide)
    · decide
    · decide
  unfold indexScore
  rw [hs,hp,hn,hz]
  simp only [BackupStat.mean]
  norm_num

theorem favorableCompleteS27D1Cmp0 : indexScore (7/5) (controlPenalty savedCref uniformQuoteError unitRoleUnused .complete) favorableCompleteS27Before [.query 1] (.hydeRetriever 1) < indexScore (7/5) (controlPenalty savedCref uniformQuoteError unitRoleUnused .complete) favorableCompleteS27Before [.query 1] (.hydeRetriever 0) := by
  rw [favorableCompleteS27D1I0,favorableCompleteS27D1I1]
  have h := index_strict_order_from_intervals ((0/1)/5) ((3/2)/8) 0 0 (10836637/10000000) (5354447/6250000)
    (treeBonus (7/5) 19 5) (treeBonus (7/5) 19 8)
    (trajectory_bonus_19_5).1 (trajectory_bonus_19_8).2 (by norm_num)
  simpa only [treeIndex,sub_zero] using h

theorem favorableCompleteS27D1Cmp2 : indexScore (7/5) (controlPenalty savedCref uniformQuoteError unitRoleUnused .complete) favorableCompleteS27Before [.query 1] (.hydeRetriever 2) ≤ indexScore (7/5) (controlPenalty savedCref uniformQuoteError unitRoleUnused .complete) favorableCompleteS27Before [.query 1] (.hydeRetriever 0) := by
  rw [favorableCompleteS27D1I2,favorableCompleteS27D1I1]

theorem favorableCompleteS27Choice1 : nativeFirstChoice (indexScore (7/5) (controlPenalty savedCref uniformQuoteError unitRoleUnused .complete) favorableCompleteS27Before [.query 1]) favorableCompleteS27Before [.query 1] = .hydeRetriever 0 := by
  apply visited_choice_from_ordered_certificate _ _ [.query 1] [.hydeRetriever 1] [.hydeRetriever 2] (.hydeRetriever 0) (by decide)
  · intro a ha
    have ho : orderedLegalAvailable [.query 1] = [.hydeRetriever 1,.hydeRetriever 0,.hydeRetriever 2] := by decide
    rw [ho] at ha
    simp only [List.mem_cons,List.not_mem_nil,or_false] at ha
    rcases ha with rfl | rfl | rfl <;> decide
  · intro a ha
    simp only [List.mem_cons,List.not_mem_nil,or_false] at ha
    rcases ha with rfl
    · exact favorableCompleteS27D1Cmp0
  · intro a ha
    simp only [List.mem_cons,List.not_mem_nil,or_false] at ha
    rcases ha with rfl
    · exact favorableCompleteS27D1Cmp2

theorem favorableCompleteS27D2I0 : indexScore (7/5) (controlPenalty savedCref uniformQuoteError unitRoleUnused .complete) favorableCompleteS27Before [.query 1,.hydeRetriever 0] (.selection 1) = treeIndex ((0/1)/1) (7/5) 0 5 1 := by
  have hs : replayBackup favorableCompleteS27Before emptyStatistics ([.query 1,.hydeRetriever 0]++[.selection 1]) = ⟨1,(0/1)⟩ := by
    rw [replayBackup_empty_closed_form]
    simp +decide [backedEvents,favorableCompleteS27Before,favorableCompleteProposal,favorableCompleteEvent1,favorableCompleteEvent2,favorableCompleteEvent3,favorableCompleteEvent4,favorableCompleteEvent5,favorableCompleteEvent6,favorableCompleteEvent7,favorableCompleteEvent8,favorableCompleteEvent9,favorableCompleteEvent10,favorableCompleteEvent11,favorableCompleteEvent12,favorableCompleteEvent13,favorableCompleteEvent14,favorableCompleteEvent15,favorableCompleteEvent16,favorableCompleteEvent17,favorableCompleteEvent18,favorableCompleteEvent19,favorableCompleteEvent20,favorableCompleteEvent21,favorableCompleteEvent22,favorableCompleteEvent23,favorableCompleteEvent24,favorableCompleteEvent25,favorableCompleteEvent26,taskReward]
    <;> norm_num
  have hp : rawVisits favorableCompleteS27Before [.query 1,.hydeRetriever 0] = 5 := by decide
  have hn : rawVisits favorableCompleteS27Before ([.query 1,.hydeRetriever 0]++[.selection 1]) = 1 := by decide
  have hz : (controlPenalty savedCref uniformQuoteError unitRoleUnused .complete) favorableCompleteS27Before [.query 1,.hydeRetriever 0] (.selection 1) = 0 := by
    apply control_penalty_empty_of_prior_terminal .complete savedCref uniformQuoteError favorableCompleteS27Before [.query 1,.hydeRetriever 0] (.selection 1) 16 (by decide)
    · decide
    · decide
  unfold indexScore
  rw [hs,hp,hn,hz]
  simp only [BackupStat.mean]
  norm_num

theorem favorableCompleteS27D2I1 : indexScore (7/5) (controlPenalty savedCref uniformQuoteError unitRoleUnused .complete) favorableCompleteS27Before [.query 1,.hydeRetriever 0] (.selection 2) = treeIndex ((0/1)/1) (7/5) 0 5 1 := by
  have hs : replayBackup favorableCompleteS27Before emptyStatistics ([.query 1,.hydeRetriever 0]++[.selection 2]) = ⟨1,(0/1)⟩ := by
    rw [replayBackup_empty_closed_form]
    simp +decide [backedEvents,favorableCompleteS27Before,favorableCompleteProposal,favorableCompleteEvent1,favorableCompleteEvent2,favorableCompleteEvent3,favorableCompleteEvent4,favorableCompleteEvent5,favorableCompleteEvent6,favorableCompleteEvent7,favorableCompleteEvent8,favorableCompleteEvent9,favorableCompleteEvent10,favorableCompleteEvent11,favorableCompleteEvent12,favorableCompleteEvent13,favorableCompleteEvent14,favorableCompleteEvent15,favorableCompleteEvent16,favorableCompleteEvent17,favorableCompleteEvent18,favorableCompleteEvent19,favorableCompleteEvent20,favorableCompleteEvent21,favorableCompleteEvent22,favorableCompleteEvent23,favorableCompleteEvent24,favorableCompleteEvent25,favorableCompleteEvent26,taskReward]
    <;> norm_num
  have hp : rawVisits favorableCompleteS27Before [.query 1,.hydeRetriever 0] = 5 := by decide
  have hn : rawVisits favorableCompleteS27Before ([.query 1,.hydeRetriever 0]++[.selection 2]) = 1 := by decide
  have hz : (controlPenalty savedCref uniformQuoteError unitRoleUnused .complete) favorableCompleteS27Before [.query 1,.hydeRetriever 0] (.selection 2) = 0 := by
    apply control_penalty_empty_of_prior_terminal .complete savedCref uniformQuoteError favorableCompleteS27Before [.query 1,.hydeRetriever 0] (.selection 2) 19 (by decide)
    · decide
    · decide
  unfold indexScore
  rw [hs,hp,hn,hz]
  simp only [BackupStat.mean]
  norm_num

theorem favorableCompleteS27D2I2 : indexScore (7/5) (controlPenalty savedCref uniformQuoteError unitRoleUnused .complete) favorableCompleteS27Before [.query 1,.hydeRetriever 0] (.selection 3) = treeIndex ((0/1)/1) (7/5) 0 5 1 := by
  have hs : replayBackup favorableCompleteS27Before emptyStatistics ([.query 1,.hydeRetriever 0]++[.selection 3]) = ⟨1,(0/1)⟩ := by
    rw [replayBackup_empty_closed_form]
    simp +decide [backedEvents,favorableCompleteS27Before,favorableCompleteProposal,favorableCompleteEvent1,favorableCompleteEvent2,favorableCompleteEvent3,favorableCompleteEvent4,favorableCompleteEvent5,favorableCompleteEvent6,favorableCompleteEvent7,favorableCompleteEvent8,favorableCompleteEvent9,favorableCompleteEvent10,favorableCompleteEvent11,favorableCompleteEvent12,favorableCompleteEvent13,favorableCompleteEvent14,favorableCompleteEvent15,favorableCompleteEvent16,favorableCompleteEvent17,favorableCompleteEvent18,favorableCompleteEvent19,favorableCompleteEvent20,favorableCompleteEvent21,favorableCompleteEvent22,favorableCompleteEvent23,favorableCompleteEvent24,favorableCompleteEvent25,favorableCompleteEvent26,taskReward]
    <;> norm_num
  have hp : rawVisits favorableCompleteS27Before [.query 1,.hydeRetriever 0] = 5 := by decide
  have hn : rawVisits favorableCompleteS27Before ([.query 1,.hydeRetriever 0]++[.selection 3]) = 1 := by decide
  have hz : (controlPenalty savedCref uniformQuoteError unitRoleUnused .complete) favorableCompleteS27Before [.query 1,.hydeRetriever 0] (.selection 3) = 0 := by
    apply control_penalty_empty_of_prior_terminal .complete savedCref uniformQuoteError favorableCompleteS27Before [.query 1,.hydeRetriever 0] (.selection 3) 23 (by decide)
    · decide
    · decide
  unfold indexScore
  rw [hs,hp,hn,hz]
  simp only [BackupStat.mean]
  norm_num

theorem favorableCompleteS27D2I3 : indexScore (7/5) (controlPenalty savedCref uniformQuoteError unitRoleUnused .complete) favorableCompleteS27Before [.query 1,.hydeRetriever 0] (.selection 0) = treeIndex ((0/1)/1) (7/5) 0 5 1 := by
  have hs : replayBackup favorableCompleteS27Before emptyStatistics ([.query 1,.hydeRetriever 0]++[.selection 0]) = ⟨1,(0/1)⟩ := by
    rw [replayBackup_empty_closed_form]
    simp +decide [backedEvents,favorableCompleteS27Before,favorableCompleteProposal,favorableCompleteEvent1,favorableCompleteEvent2,favorableCompleteEvent3,favorableCompleteEvent4,favorableCompleteEvent5,favorableCompleteEvent6,favorableCompleteEvent7,favorableCompleteEvent8,favorableCompleteEvent9,favorableCompleteEvent10,favorableCompleteEvent11,favorableCompleteEvent12,favorableCompleteEvent13,favorableCompleteEvent14,favorableCompleteEvent15,favorableCompleteEvent16,favorableCompleteEvent17,favorableCompleteEvent18,favorableCompleteEvent19,favorableCompleteEvent20,favorableCompleteEvent21,favorableCompleteEvent22,favorableCompleteEvent23,favorableCompleteEvent24,favorableCompleteEvent25,favorableCompleteEvent26,taskReward]
    <;> norm_num
  have hp : rawVisits favorableCompleteS27Before [.query 1,.hydeRetriever 0] = 5 := by decide
  have hn : rawVisits favorableCompleteS27Before ([.query 1,.hydeRetriever 0]++[.selection 0]) = 1 := by decide
  have hz : (controlPenalty savedCref uniformQuoteError unitRoleUnused .complete) favorableCompleteS27Before [.query 1,.hydeRetriever 0] (.selection 0) = 0 := by
    apply control_penalty_empty_of_prior_terminal .complete savedCref uniformQuoteError favorableCompleteS27Before [.query 1,.hydeRetriever 0] (.selection 0) 1 (by decide)
    · decide
    · decide
  unfold indexScore
  rw [hs,hp,hn,hz]
  simp only [BackupStat.mean]
  norm_num

theorem favorableCompleteS27D2Cmp1 : indexScore (7/5) (controlPenalty savedCref uniformQuoteError unitRoleUnused .complete) favorableCompleteS27Before [.query 1,.hydeRetriever 0] (.selection 2) ≤ indexScore (7/5) (controlPenalty savedCref uniformQuoteError unitRoleUnused .complete) favorableCompleteS27Before [.query 1,.hydeRetriever 0] (.selection 1) := by
  rw [favorableCompleteS27D2I1,favorableCompleteS27D2I0]

theorem favorableCompleteS27D2Cmp2 : indexScore (7/5) (controlPenalty savedCref uniformQuoteError unitRoleUnused .complete) favorableCompleteS27Before [.query 1,.hydeRetriever 0] (.selection 3) ≤ indexScore (7/5) (controlPenalty savedCref uniformQuoteError unitRoleUnused .complete) favorableCompleteS27Before [.query 1,.hydeRetriever 0] (.selection 1) := by
  rw [favorableCompleteS27D2I2,favorableCompleteS27D2I0]

theorem favorableCompleteS27D2Cmp3 : indexScore (7/5) (controlPenalty savedCref uniformQuoteError unitRoleUnused .complete) favorableCompleteS27Before [.query 1,.hydeRetriever 0] (.selection 0) ≤ indexScore (7/5) (controlPenalty savedCref uniformQuoteError unitRoleUnused .complete) favorableCompleteS27Before [.query 1,.hydeRetriever 0] (.selection 1) := by
  rw [favorableCompleteS27D2I3,favorableCompleteS27D2I0]

theorem favorableCompleteS27Choice2 : nativeFirstChoice (indexScore (7/5) (controlPenalty savedCref uniformQuoteError unitRoleUnused .complete) favorableCompleteS27Before [.query 1,.hydeRetriever 0]) favorableCompleteS27Before [.query 1,.hydeRetriever 0] = .selection 1 := by
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
    · exact favorableCompleteS27D2Cmp1
    · exact favorableCompleteS27D2Cmp2
    · exact favorableCompleteS27D2Cmp3

theorem favorableCompleteS27ActualEvent : nativeEvent budgetTape (7/5) (controlPenalty savedCref uniformQuoteError unitRoleUnused .complete)
    (taskReward false (2/5) (1/2)) favorableCompleteS27Before = favorableCompleteEvent27 := by
  have hs0 := native_select_existing_step budgetTape (7/5) (controlPenalty savedCref uniformQuoteError unitRoleUnused .complete) favorableCompleteS27Before 8 [] (.query 1)
    (by decide) (by decide) favorableCompleteS27Choice0
  have hs1 := native_select_existing_step budgetTape (7/5) (controlPenalty savedCref uniformQuoteError unitRoleUnused .complete) favorableCompleteS27Before 7 [.query 1] (.hydeRetriever 0)
    (by decide) (by decide) favorableCompleteS27Choice1
  have hs2 := native_select_existing_step budgetTape (7/5) (controlPenalty savedCref uniformQuoteError unitRoleUnused .complete) favorableCompleteS27Before 6 [.query 1,.hydeRetriever 0] (.selection 1)
    (by decide) (by decide) favorableCompleteS27Choice2
  have hnew := native_select_new_step budgetTape (7/5) (controlPenalty savedCref uniformQuoteError unitRoleUnused .complete) favorableCompleteS27Before 5 [.query 1,.hydeRetriever 0,.selection 1]
    [.width 3,.width 0,.width 1,.width 2] (.width 0) (by decide) (by decide) (by decide) (by decide)
  have hs : nativeSelect budgetTape (7/5) (controlPenalty savedCref uniformQuoteError unitRoleUnused .complete) favorableCompleteS27Before 9 [] = [.query 1,.hydeRetriever 0,.selection 1,.width 0] := by
    rw [hs0]
    change nativeSelect budgetTape (7/5) (controlPenalty savedCref uniformQuoteError unitRoleUnused .complete) favorableCompleteS27Before 8 [.query 1] = _
    rw [hs1]
    change nativeSelect budgetTape (7/5) (controlPenalty savedCref uniformQuoteError unitRoleUnused .complete) favorableCompleteS27Before 7 [.query 1,.hydeRetriever 0] = _
    rw [hs2]
    change nativeSelect budgetTape (7/5) (controlPenalty savedCref uniformQuoteError unitRoleUnused .complete) favorableCompleteS27Before 6 [.query 1,.hydeRetriever 0,.selection 1] = _
    rw [hnew] <;> rfl
  have hr : repairedRollout budgetTape favorableCompleteS27Before 9 [.query 1,.hydeRetriever 0,.selection 1,.width 0] = [.query 1,.hydeRetriever 0,.selection 1,.width 0,.stop,.reranker 0,.topm 0,.context 0,.answer 0] := by decide
  simp only [nativeEvent,hs,hr]
  rfl

end AgentUCT32MConcrete
