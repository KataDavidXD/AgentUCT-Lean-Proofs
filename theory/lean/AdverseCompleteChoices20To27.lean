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

def adverseCompleteS20Before := adverseCompleteProposal.take 19

theorem adverseCompleteS20Choice0 : nativeFirstChoice (indexScore (7/5) (controlPenalty savedCref uniformQuoteError unitRoleUnused .complete) adverseCompleteS20Before []) adverseCompleteS20Before [] = .query 1 := by
  apply complete_root_from_physical_gap adverseCompleteS20Before (adverseComplete_prefix_rewards 19) (by decide)
  · intro q; fin_cases q <;> decide
  · exact AgentUCTNextExact.adverse_complete_hyde_root_suffix_empty 19 (by omega)
  · intro q hq
    exact AgentUCTNextExact.adverse_complete_normal_root_physical_quote_exact 19 (by omega) q hq

theorem adverseCompleteS20D1I0 : indexScore (7/5) (controlPenalty savedCref uniformQuoteError unitRoleUnused .complete) adverseCompleteS20Before [.query 1] (.hydeRetriever 1) = treeIndex ((0/1)/4) (7/5) 0 12 4 := by
  have hs : replayBackup adverseCompleteS20Before emptyStatistics ([.query 1]++[.hydeRetriever 1]) = ⟨4,(0/1)⟩ := by
    rw [replayBackup_empty_closed_form]
    simp +decide [backedEvents,adverseCompleteS20Before,adverseCompleteProposal,adverseCompleteEvent1,adverseCompleteEvent2,adverseCompleteEvent3,adverseCompleteEvent4,adverseCompleteEvent5,adverseCompleteEvent6,adverseCompleteEvent7,adverseCompleteEvent8,adverseCompleteEvent9,adverseCompleteEvent10,adverseCompleteEvent11,adverseCompleteEvent12,adverseCompleteEvent13,adverseCompleteEvent14,adverseCompleteEvent15,adverseCompleteEvent16,adverseCompleteEvent17,adverseCompleteEvent18,adverseCompleteEvent19,taskReward]
    <;> norm_num
  have hp : rawVisits adverseCompleteS20Before [.query 1] = 12 := by decide
  have hn : rawVisits adverseCompleteS20Before ([.query 1]++[.hydeRetriever 1]) = 4 := by decide
  have hz : (controlPenalty savedCref uniformQuoteError unitRoleUnused .complete) adverseCompleteS20Before [.query 1] (.hydeRetriever 1) = 0 := by
    apply control_penalty_empty_of_prior_terminal .complete savedCref uniformQuoteError adverseCompleteS20Before [.query 1] (.hydeRetriever 1) 8 (by decide)
    · decide
    · decide
  unfold indexScore
  rw [hs,hp,hn,hz]
  simp only [BackupStat.mean]
  norm_num

theorem adverseCompleteS20D1I1 : indexScore (7/5) (controlPenalty savedCref uniformQuoteError unitRoleUnused .complete) adverseCompleteS20Before [.query 1] (.hydeRetriever 0) = treeIndex ((0/1)/4) (7/5) 0 12 4 := by
  have hs : replayBackup adverseCompleteS20Before emptyStatistics ([.query 1]++[.hydeRetriever 0]) = ⟨4,(0/1)⟩ := by
    rw [replayBackup_empty_closed_form]
    simp +decide [backedEvents,adverseCompleteS20Before,adverseCompleteProposal,adverseCompleteEvent1,adverseCompleteEvent2,adverseCompleteEvent3,adverseCompleteEvent4,adverseCompleteEvent5,adverseCompleteEvent6,adverseCompleteEvent7,adverseCompleteEvent8,adverseCompleteEvent9,adverseCompleteEvent10,adverseCompleteEvent11,adverseCompleteEvent12,adverseCompleteEvent13,adverseCompleteEvent14,adverseCompleteEvent15,adverseCompleteEvent16,adverseCompleteEvent17,adverseCompleteEvent18,adverseCompleteEvent19,taskReward]
    <;> norm_num
  have hp : rawVisits adverseCompleteS20Before [.query 1] = 12 := by decide
  have hn : rawVisits adverseCompleteS20Before ([.query 1]++[.hydeRetriever 0]) = 4 := by decide
  have hz : (controlPenalty savedCref uniformQuoteError unitRoleUnused .complete) adverseCompleteS20Before [.query 1] (.hydeRetriever 0) = 0 := by
    apply control_penalty_empty_of_prior_terminal .complete savedCref uniformQuoteError adverseCompleteS20Before [.query 1] (.hydeRetriever 0) 1 (by decide)
    · decide
    · decide
  unfold indexScore
  rw [hs,hp,hn,hz]
  simp only [BackupStat.mean]
  norm_num

theorem adverseCompleteS20D1I2 : indexScore (7/5) (controlPenalty savedCref uniformQuoteError unitRoleUnused .complete) adverseCompleteS20Before [.query 1] (.hydeRetriever 2) = treeIndex ((0/1)/3) (7/5) 0 12 3 := by
  have hs : replayBackup adverseCompleteS20Before emptyStatistics ([.query 1]++[.hydeRetriever 2]) = ⟨3,(0/1)⟩ := by
    rw [replayBackup_empty_closed_form]
    simp +decide [backedEvents,adverseCompleteS20Before,adverseCompleteProposal,adverseCompleteEvent1,adverseCompleteEvent2,adverseCompleteEvent3,adverseCompleteEvent4,adverseCompleteEvent5,adverseCompleteEvent6,adverseCompleteEvent7,adverseCompleteEvent8,adverseCompleteEvent9,adverseCompleteEvent10,adverseCompleteEvent11,adverseCompleteEvent12,adverseCompleteEvent13,adverseCompleteEvent14,adverseCompleteEvent15,adverseCompleteEvent16,adverseCompleteEvent17,adverseCompleteEvent18,adverseCompleteEvent19,taskReward]
    <;> norm_num
  have hp : rawVisits adverseCompleteS20Before [.query 1] = 12 := by decide
  have hn : rawVisits adverseCompleteS20Before ([.query 1]++[.hydeRetriever 2]) = 3 := by decide
  have hz : (controlPenalty savedCref uniformQuoteError unitRoleUnused .complete) adverseCompleteS20Before [.query 1] (.hydeRetriever 2) = 0 := by
    apply control_penalty_empty_of_prior_terminal .complete savedCref uniformQuoteError adverseCompleteS20Before [.query 1] (.hydeRetriever 2) 10 (by decide)
    · decide
    · decide
  unfold indexScore
  rw [hs,hp,hn,hz]
  simp only [BackupStat.mean]
  norm_num

theorem adverseCompleteS20D1Cmp0 : indexScore (7/5) (controlPenalty savedCref uniformQuoteError unitRoleUnused .complete) adverseCompleteS20Before [.query 1] (.hydeRetriever 1) < indexScore (7/5) (controlPenalty savedCref uniformQuoteError unitRoleUnused .complete) adverseCompleteS20Before [.query 1] (.hydeRetriever 2) := by
  rw [adverseCompleteS20D1I0,adverseCompleteS20D1I2]
  have h := index_strict_order_from_intervals ((0/1)/3) ((0/1)/4) 0 0 (64725703/50000000) (5605411/5000000)
    (treeBonus (7/5) 12 3) (treeBonus (7/5) 12 4)
    (trajectory_bonus_12_3).1 (trajectory_bonus_12_4).2 (by norm_num)
  simpa only [treeIndex,sub_zero] using h

theorem adverseCompleteS20D1Cmp1 : indexScore (7/5) (controlPenalty savedCref uniformQuoteError unitRoleUnused .complete) adverseCompleteS20Before [.query 1] (.hydeRetriever 0) < indexScore (7/5) (controlPenalty savedCref uniformQuoteError unitRoleUnused .complete) adverseCompleteS20Before [.query 1] (.hydeRetriever 2) := by
  rw [adverseCompleteS20D1I1,adverseCompleteS20D1I2]
  have h := index_strict_order_from_intervals ((0/1)/3) ((0/1)/4) 0 0 (64725703/50000000) (5605411/5000000)
    (treeBonus (7/5) 12 3) (treeBonus (7/5) 12 4)
    (trajectory_bonus_12_3).1 (trajectory_bonus_12_4).2 (by norm_num)
  simpa only [treeIndex,sub_zero] using h

theorem adverseCompleteS20Choice1 : nativeFirstChoice (indexScore (7/5) (controlPenalty savedCref uniformQuoteError unitRoleUnused .complete) adverseCompleteS20Before [.query 1]) adverseCompleteS20Before [.query 1] = .hydeRetriever 2 := by
  apply visited_choice_from_ordered_certificate _ _ [.query 1] [.hydeRetriever 1,.hydeRetriever 0] [] (.hydeRetriever 2) (by decide)
  · intro a ha
    have ho : orderedLegalAvailable [.query 1] = [.hydeRetriever 1,.hydeRetriever 0,.hydeRetriever 2] := by decide
    rw [ho] at ha
    simp only [List.mem_cons,List.not_mem_nil,or_false] at ha
    rcases ha with rfl | rfl | rfl <;> decide
  · intro a ha
    simp only [List.mem_cons,List.not_mem_nil,or_false] at ha
    rcases ha with rfl | rfl
    · exact adverseCompleteS20D1Cmp0
    · exact adverseCompleteS20D1Cmp1
  · simp

theorem adverseCompleteS20ActualEvent : nativeEvent budgetTape (7/5) (controlPenalty savedCref uniformQuoteError unitRoleUnused .complete)
    (taskReward true (2/5) (1/2)) adverseCompleteS20Before = adverseCompleteEvent20 := by
  have hs0 := native_select_existing_step budgetTape (7/5) (controlPenalty savedCref uniformQuoteError unitRoleUnused .complete) adverseCompleteS20Before 8 [] (.query 1)
    (by decide) (by decide) adverseCompleteS20Choice0
  have hs1 := native_select_existing_step budgetTape (7/5) (controlPenalty savedCref uniformQuoteError unitRoleUnused .complete) adverseCompleteS20Before 7 [.query 1] (.hydeRetriever 2)
    (by decide) (by decide) adverseCompleteS20Choice1
  have hnew := native_select_new_step budgetTape (7/5) (controlPenalty savedCref uniformQuoteError unitRoleUnused .complete) adverseCompleteS20Before 6 [.query 1,.hydeRetriever 2]
    [.selection 2,.selection 3] (.selection 2) (by decide) (by decide) (by decide) (by decide)
  have hs : nativeSelect budgetTape (7/5) (controlPenalty savedCref uniformQuoteError unitRoleUnused .complete) adverseCompleteS20Before 9 [] = [.query 1,.hydeRetriever 2,.selection 2] := by
    rw [hs0]
    change nativeSelect budgetTape (7/5) (controlPenalty savedCref uniformQuoteError unitRoleUnused .complete) adverseCompleteS20Before 8 [.query 1] = _
    rw [hs1]
    change nativeSelect budgetTape (7/5) (controlPenalty savedCref uniformQuoteError unitRoleUnused .complete) adverseCompleteS20Before 7 [.query 1,.hydeRetriever 2] = _
    rw [hnew] <;> rfl
  have hr : repairedRollout budgetTape adverseCompleteS20Before 9 [.query 1,.hydeRetriever 2,.selection 2] = [.query 1,.hydeRetriever 2,.selection 2,.width 0,.stop,.reranker 0,.topm 0,.context 0,.answer 0] := by decide
  simp only [nativeEvent,hs,hr]
  rfl

def adverseCompleteS21Before := adverseCompleteProposal.take 20

theorem adverseCompleteS21Choice0 : nativeFirstChoice (indexScore (7/5) (controlPenalty savedCref uniformQuoteError unitRoleUnused .complete) adverseCompleteS21Before []) adverseCompleteS21Before [] = .query 1 := by
  apply complete_root_from_physical_gap adverseCompleteS21Before (adverseComplete_prefix_rewards 20) (by decide)
  · intro q; fin_cases q <;> decide
  · exact AgentUCTNextExact.adverse_complete_hyde_root_suffix_empty 20 (by omega)
  · intro q hq
    exact AgentUCTNextExact.adverse_complete_normal_root_physical_quote_exact 20 (by omega) q hq

theorem adverseCompleteS21D1I0 : indexScore (7/5) (controlPenalty savedCref uniformQuoteError unitRoleUnused .complete) adverseCompleteS21Before [.query 1] (.hydeRetriever 1) = treeIndex ((0/1)/4) (7/5) 0 13 4 := by
  have hs : replayBackup adverseCompleteS21Before emptyStatistics ([.query 1]++[.hydeRetriever 1]) = ⟨4,(0/1)⟩ := by
    rw [replayBackup_empty_closed_form]
    simp +decide [backedEvents,adverseCompleteS21Before,adverseCompleteProposal,adverseCompleteEvent1,adverseCompleteEvent2,adverseCompleteEvent3,adverseCompleteEvent4,adverseCompleteEvent5,adverseCompleteEvent6,adverseCompleteEvent7,adverseCompleteEvent8,adverseCompleteEvent9,adverseCompleteEvent10,adverseCompleteEvent11,adverseCompleteEvent12,adverseCompleteEvent13,adverseCompleteEvent14,adverseCompleteEvent15,adverseCompleteEvent16,adverseCompleteEvent17,adverseCompleteEvent18,adverseCompleteEvent19,adverseCompleteEvent20,taskReward]
    <;> norm_num
  have hp : rawVisits adverseCompleteS21Before [.query 1] = 13 := by decide
  have hn : rawVisits adverseCompleteS21Before ([.query 1]++[.hydeRetriever 1]) = 4 := by decide
  have hz : (controlPenalty savedCref uniformQuoteError unitRoleUnused .complete) adverseCompleteS21Before [.query 1] (.hydeRetriever 1) = 0 := by
    apply control_penalty_empty_of_prior_terminal .complete savedCref uniformQuoteError adverseCompleteS21Before [.query 1] (.hydeRetriever 1) 8 (by decide)
    · decide
    · decide
  unfold indexScore
  rw [hs,hp,hn,hz]
  simp only [BackupStat.mean]
  norm_num

theorem adverseCompleteS21D1I1 : indexScore (7/5) (controlPenalty savedCref uniformQuoteError unitRoleUnused .complete) adverseCompleteS21Before [.query 1] (.hydeRetriever 0) = treeIndex ((0/1)/4) (7/5) 0 13 4 := by
  have hs : replayBackup adverseCompleteS21Before emptyStatistics ([.query 1]++[.hydeRetriever 0]) = ⟨4,(0/1)⟩ := by
    rw [replayBackup_empty_closed_form]
    simp +decide [backedEvents,adverseCompleteS21Before,adverseCompleteProposal,adverseCompleteEvent1,adverseCompleteEvent2,adverseCompleteEvent3,adverseCompleteEvent4,adverseCompleteEvent5,adverseCompleteEvent6,adverseCompleteEvent7,adverseCompleteEvent8,adverseCompleteEvent9,adverseCompleteEvent10,adverseCompleteEvent11,adverseCompleteEvent12,adverseCompleteEvent13,adverseCompleteEvent14,adverseCompleteEvent15,adverseCompleteEvent16,adverseCompleteEvent17,adverseCompleteEvent18,adverseCompleteEvent19,adverseCompleteEvent20,taskReward]
    <;> norm_num
  have hp : rawVisits adverseCompleteS21Before [.query 1] = 13 := by decide
  have hn : rawVisits adverseCompleteS21Before ([.query 1]++[.hydeRetriever 0]) = 4 := by decide
  have hz : (controlPenalty savedCref uniformQuoteError unitRoleUnused .complete) adverseCompleteS21Before [.query 1] (.hydeRetriever 0) = 0 := by
    apply control_penalty_empty_of_prior_terminal .complete savedCref uniformQuoteError adverseCompleteS21Before [.query 1] (.hydeRetriever 0) 1 (by decide)
    · decide
    · decide
  unfold indexScore
  rw [hs,hp,hn,hz]
  simp only [BackupStat.mean]
  norm_num

theorem adverseCompleteS21D1I2 : indexScore (7/5) (controlPenalty savedCref uniformQuoteError unitRoleUnused .complete) adverseCompleteS21Before [.query 1] (.hydeRetriever 2) = treeIndex ((0/1)/4) (7/5) 0 13 4 := by
  have hs : replayBackup adverseCompleteS21Before emptyStatistics ([.query 1]++[.hydeRetriever 2]) = ⟨4,(0/1)⟩ := by
    rw [replayBackup_empty_closed_form]
    simp +decide [backedEvents,adverseCompleteS21Before,adverseCompleteProposal,adverseCompleteEvent1,adverseCompleteEvent2,adverseCompleteEvent3,adverseCompleteEvent4,adverseCompleteEvent5,adverseCompleteEvent6,adverseCompleteEvent7,adverseCompleteEvent8,adverseCompleteEvent9,adverseCompleteEvent10,adverseCompleteEvent11,adverseCompleteEvent12,adverseCompleteEvent13,adverseCompleteEvent14,adverseCompleteEvent15,adverseCompleteEvent16,adverseCompleteEvent17,adverseCompleteEvent18,adverseCompleteEvent19,adverseCompleteEvent20,taskReward]
    <;> norm_num
  have hp : rawVisits adverseCompleteS21Before [.query 1] = 13 := by decide
  have hn : rawVisits adverseCompleteS21Before ([.query 1]++[.hydeRetriever 2]) = 4 := by decide
  have hz : (controlPenalty savedCref uniformQuoteError unitRoleUnused .complete) adverseCompleteS21Before [.query 1] (.hydeRetriever 2) = 0 := by
    apply control_penalty_empty_of_prior_terminal .complete savedCref uniformQuoteError adverseCompleteS21Before [.query 1] (.hydeRetriever 2) 10 (by decide)
    · decide
    · decide
  unfold indexScore
  rw [hs,hp,hn,hz]
  simp only [BackupStat.mean]
  norm_num

theorem adverseCompleteS21D1Cmp1 : indexScore (7/5) (controlPenalty savedCref uniformQuoteError unitRoleUnused .complete) adverseCompleteS21Before [.query 1] (.hydeRetriever 0) ≤ indexScore (7/5) (controlPenalty savedCref uniformQuoteError unitRoleUnused .complete) adverseCompleteS21Before [.query 1] (.hydeRetriever 1) := by
  rw [adverseCompleteS21D1I1,adverseCompleteS21D1I0]

theorem adverseCompleteS21D1Cmp2 : indexScore (7/5) (controlPenalty savedCref uniformQuoteError unitRoleUnused .complete) adverseCompleteS21Before [.query 1] (.hydeRetriever 2) ≤ indexScore (7/5) (controlPenalty savedCref uniformQuoteError unitRoleUnused .complete) adverseCompleteS21Before [.query 1] (.hydeRetriever 1) := by
  rw [adverseCompleteS21D1I2,adverseCompleteS21D1I0]

theorem adverseCompleteS21Choice1 : nativeFirstChoice (indexScore (7/5) (controlPenalty savedCref uniformQuoteError unitRoleUnused .complete) adverseCompleteS21Before [.query 1]) adverseCompleteS21Before [.query 1] = .hydeRetriever 1 := by
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
    · exact adverseCompleteS21D1Cmp1
    · exact adverseCompleteS21D1Cmp2

theorem adverseCompleteS21ActualEvent : nativeEvent budgetTape (7/5) (controlPenalty savedCref uniformQuoteError unitRoleUnused .complete)
    (taskReward true (2/5) (1/2)) adverseCompleteS21Before = adverseCompleteEvent21 := by
  have hs0 := native_select_existing_step budgetTape (7/5) (controlPenalty savedCref uniformQuoteError unitRoleUnused .complete) adverseCompleteS21Before 8 [] (.query 1)
    (by decide) (by decide) adverseCompleteS21Choice0
  have hs1 := native_select_existing_step budgetTape (7/5) (controlPenalty savedCref uniformQuoteError unitRoleUnused .complete) adverseCompleteS21Before 7 [.query 1] (.hydeRetriever 1)
    (by decide) (by decide) adverseCompleteS21Choice1
  have hnew := native_select_new_step budgetTape (7/5) (controlPenalty savedCref uniformQuoteError unitRoleUnused .complete) adverseCompleteS21Before 6 [.query 1,.hydeRetriever 1]
    [.selection 3] (.selection 3) (by decide) (by decide) (by decide) (by decide)
  have hs : nativeSelect budgetTape (7/5) (controlPenalty savedCref uniformQuoteError unitRoleUnused .complete) adverseCompleteS21Before 9 [] = [.query 1,.hydeRetriever 1,.selection 3] := by
    rw [hs0]
    change nativeSelect budgetTape (7/5) (controlPenalty savedCref uniformQuoteError unitRoleUnused .complete) adverseCompleteS21Before 8 [.query 1] = _
    rw [hs1]
    change nativeSelect budgetTape (7/5) (controlPenalty savedCref uniformQuoteError unitRoleUnused .complete) adverseCompleteS21Before 7 [.query 1,.hydeRetriever 1] = _
    rw [hnew] <;> rfl
  have hr : repairedRollout budgetTape adverseCompleteS21Before 9 [.query 1,.hydeRetriever 1,.selection 3] = [.query 1,.hydeRetriever 1,.selection 3,.width 0,.stop,.reranker 0,.topm 0,.context 0,.answer 0] := by decide
  simp only [nativeEvent,hs,hr]
  rfl

def adverseCompleteS22Before := adverseCompleteProposal.take 21

theorem adverseCompleteS22Choice0 : nativeFirstChoice (indexScore (7/5) (controlPenalty savedCref uniformQuoteError unitRoleUnused .complete) adverseCompleteS22Before []) adverseCompleteS22Before [] = .query 1 := by
  apply complete_root_from_physical_gap adverseCompleteS22Before (adverseComplete_prefix_rewards 21) (by decide)
  · intro q; fin_cases q <;> decide
  · exact AgentUCTNextExact.adverse_complete_hyde_root_suffix_empty 21 (by omega)
  · intro q hq
    exact AgentUCTNextExact.adverse_complete_normal_root_physical_quote_exact 21 (by omega) q hq

theorem adverseCompleteS22D1I0 : indexScore (7/5) (controlPenalty savedCref uniformQuoteError unitRoleUnused .complete) adverseCompleteS22Before [.query 1] (.hydeRetriever 1) = treeIndex ((0/1)/5) (7/5) 0 14 5 := by
  have hs : replayBackup adverseCompleteS22Before emptyStatistics ([.query 1]++[.hydeRetriever 1]) = ⟨5,(0/1)⟩ := by
    rw [replayBackup_empty_closed_form]
    simp +decide [backedEvents,adverseCompleteS22Before,adverseCompleteProposal,adverseCompleteEvent1,adverseCompleteEvent2,adverseCompleteEvent3,adverseCompleteEvent4,adverseCompleteEvent5,adverseCompleteEvent6,adverseCompleteEvent7,adverseCompleteEvent8,adverseCompleteEvent9,adverseCompleteEvent10,adverseCompleteEvent11,adverseCompleteEvent12,adverseCompleteEvent13,adverseCompleteEvent14,adverseCompleteEvent15,adverseCompleteEvent16,adverseCompleteEvent17,adverseCompleteEvent18,adverseCompleteEvent19,adverseCompleteEvent20,adverseCompleteEvent21,taskReward]
    <;> norm_num
  have hp : rawVisits adverseCompleteS22Before [.query 1] = 14 := by decide
  have hn : rawVisits adverseCompleteS22Before ([.query 1]++[.hydeRetriever 1]) = 5 := by decide
  have hz : (controlPenalty savedCref uniformQuoteError unitRoleUnused .complete) adverseCompleteS22Before [.query 1] (.hydeRetriever 1) = 0 := by
    apply control_penalty_empty_of_prior_terminal .complete savedCref uniformQuoteError adverseCompleteS22Before [.query 1] (.hydeRetriever 1) 8 (by decide)
    · decide
    · decide
  unfold indexScore
  rw [hs,hp,hn,hz]
  simp only [BackupStat.mean]
  norm_num

theorem adverseCompleteS22D1I1 : indexScore (7/5) (controlPenalty savedCref uniformQuoteError unitRoleUnused .complete) adverseCompleteS22Before [.query 1] (.hydeRetriever 0) = treeIndex ((0/1)/4) (7/5) 0 14 4 := by
  have hs : replayBackup adverseCompleteS22Before emptyStatistics ([.query 1]++[.hydeRetriever 0]) = ⟨4,(0/1)⟩ := by
    rw [replayBackup_empty_closed_form]
    simp +decide [backedEvents,adverseCompleteS22Before,adverseCompleteProposal,adverseCompleteEvent1,adverseCompleteEvent2,adverseCompleteEvent3,adverseCompleteEvent4,adverseCompleteEvent5,adverseCompleteEvent6,adverseCompleteEvent7,adverseCompleteEvent8,adverseCompleteEvent9,adverseCompleteEvent10,adverseCompleteEvent11,adverseCompleteEvent12,adverseCompleteEvent13,adverseCompleteEvent14,adverseCompleteEvent15,adverseCompleteEvent16,adverseCompleteEvent17,adverseCompleteEvent18,adverseCompleteEvent19,adverseCompleteEvent20,adverseCompleteEvent21,taskReward]
    <;> norm_num
  have hp : rawVisits adverseCompleteS22Before [.query 1] = 14 := by decide
  have hn : rawVisits adverseCompleteS22Before ([.query 1]++[.hydeRetriever 0]) = 4 := by decide
  have hz : (controlPenalty savedCref uniformQuoteError unitRoleUnused .complete) adverseCompleteS22Before [.query 1] (.hydeRetriever 0) = 0 := by
    apply control_penalty_empty_of_prior_terminal .complete savedCref uniformQuoteError adverseCompleteS22Before [.query 1] (.hydeRetriever 0) 1 (by decide)
    · decide
    · decide
  unfold indexScore
  rw [hs,hp,hn,hz]
  simp only [BackupStat.mean]
  norm_num

theorem adverseCompleteS22D1I2 : indexScore (7/5) (controlPenalty savedCref uniformQuoteError unitRoleUnused .complete) adverseCompleteS22Before [.query 1] (.hydeRetriever 2) = treeIndex ((0/1)/4) (7/5) 0 14 4 := by
  have hs : replayBackup adverseCompleteS22Before emptyStatistics ([.query 1]++[.hydeRetriever 2]) = ⟨4,(0/1)⟩ := by
    rw [replayBackup_empty_closed_form]
    simp +decide [backedEvents,adverseCompleteS22Before,adverseCompleteProposal,adverseCompleteEvent1,adverseCompleteEvent2,adverseCompleteEvent3,adverseCompleteEvent4,adverseCompleteEvent5,adverseCompleteEvent6,adverseCompleteEvent7,adverseCompleteEvent8,adverseCompleteEvent9,adverseCompleteEvent10,adverseCompleteEvent11,adverseCompleteEvent12,adverseCompleteEvent13,adverseCompleteEvent14,adverseCompleteEvent15,adverseCompleteEvent16,adverseCompleteEvent17,adverseCompleteEvent18,adverseCompleteEvent19,adverseCompleteEvent20,adverseCompleteEvent21,taskReward]
    <;> norm_num
  have hp : rawVisits adverseCompleteS22Before [.query 1] = 14 := by decide
  have hn : rawVisits adverseCompleteS22Before ([.query 1]++[.hydeRetriever 2]) = 4 := by decide
  have hz : (controlPenalty savedCref uniformQuoteError unitRoleUnused .complete) adverseCompleteS22Before [.query 1] (.hydeRetriever 2) = 0 := by
    apply control_penalty_empty_of_prior_terminal .complete savedCref uniformQuoteError adverseCompleteS22Before [.query 1] (.hydeRetriever 2) 10 (by decide)
    · decide
    · decide
  unfold indexScore
  rw [hs,hp,hn,hz]
  simp only [BackupStat.mean]
  norm_num

theorem adverseCompleteS22D1Cmp0 : indexScore (7/5) (controlPenalty savedCref uniformQuoteError unitRoleUnused .complete) adverseCompleteS22Before [.query 1] (.hydeRetriever 1) < indexScore (7/5) (controlPenalty savedCref uniformQuoteError unitRoleUnused .complete) adverseCompleteS22Before [.query 1] (.hydeRetriever 0) := by
  rw [adverseCompleteS22D1I0,adverseCompleteS22D1I1]
  have h := index_strict_order_from_intervals ((0/1)/4) ((0/1)/5) 0 0 (57596539/50000000) (51515919/50000000)
    (treeBonus (7/5) 14 4) (treeBonus (7/5) 14 5)
    (trajectory_bonus_14_4).1 (trajectory_bonus_14_5).2 (by norm_num)
  simpa only [treeIndex,sub_zero] using h

theorem adverseCompleteS22D1Cmp2 : indexScore (7/5) (controlPenalty savedCref uniformQuoteError unitRoleUnused .complete) adverseCompleteS22Before [.query 1] (.hydeRetriever 2) ≤ indexScore (7/5) (controlPenalty savedCref uniformQuoteError unitRoleUnused .complete) adverseCompleteS22Before [.query 1] (.hydeRetriever 0) := by
  rw [adverseCompleteS22D1I2,adverseCompleteS22D1I1]

theorem adverseCompleteS22Choice1 : nativeFirstChoice (indexScore (7/5) (controlPenalty savedCref uniformQuoteError unitRoleUnused .complete) adverseCompleteS22Before [.query 1]) adverseCompleteS22Before [.query 1] = .hydeRetriever 0 := by
  apply visited_choice_from_ordered_certificate _ _ [.query 1] [.hydeRetriever 1] [.hydeRetriever 2] (.hydeRetriever 0) (by decide)
  · intro a ha
    have ho : orderedLegalAvailable [.query 1] = [.hydeRetriever 1,.hydeRetriever 0,.hydeRetriever 2] := by decide
    rw [ho] at ha
    simp only [List.mem_cons,List.not_mem_nil,or_false] at ha
    rcases ha with rfl | rfl | rfl <;> decide
  · intro a ha
    simp only [List.mem_cons,List.not_mem_nil,or_false] at ha
    rcases ha with rfl
    · exact adverseCompleteS22D1Cmp0
  · intro a ha
    simp only [List.mem_cons,List.not_mem_nil,or_false] at ha
    rcases ha with rfl
    · exact adverseCompleteS22D1Cmp2

theorem adverseCompleteS22ActualEvent : nativeEvent budgetTape (7/5) (controlPenalty savedCref uniformQuoteError unitRoleUnused .complete)
    (taskReward true (2/5) (1/2)) adverseCompleteS22Before = adverseCompleteEvent22 := by
  have hs0 := native_select_existing_step budgetTape (7/5) (controlPenalty savedCref uniformQuoteError unitRoleUnused .complete) adverseCompleteS22Before 8 [] (.query 1)
    (by decide) (by decide) adverseCompleteS22Choice0
  have hs1 := native_select_existing_step budgetTape (7/5) (controlPenalty savedCref uniformQuoteError unitRoleUnused .complete) adverseCompleteS22Before 7 [.query 1] (.hydeRetriever 0)
    (by decide) (by decide) adverseCompleteS22Choice1
  have hnew := native_select_new_step budgetTape (7/5) (controlPenalty savedCref uniformQuoteError unitRoleUnused .complete) adverseCompleteS22Before 6 [.query 1,.hydeRetriever 0]
    [.selection 3] (.selection 3) (by decide) (by decide) (by decide) (by decide)
  have hs : nativeSelect budgetTape (7/5) (controlPenalty savedCref uniformQuoteError unitRoleUnused .complete) adverseCompleteS22Before 9 [] = [.query 1,.hydeRetriever 0,.selection 3] := by
    rw [hs0]
    change nativeSelect budgetTape (7/5) (controlPenalty savedCref uniformQuoteError unitRoleUnused .complete) adverseCompleteS22Before 8 [.query 1] = _
    rw [hs1]
    change nativeSelect budgetTape (7/5) (controlPenalty savedCref uniformQuoteError unitRoleUnused .complete) adverseCompleteS22Before 7 [.query 1,.hydeRetriever 0] = _
    rw [hnew] <;> rfl
  have hr : repairedRollout budgetTape adverseCompleteS22Before 9 [.query 1,.hydeRetriever 0,.selection 3] = [.query 1,.hydeRetriever 0,.selection 3,.width 0,.stop,.reranker 0,.topm 0,.context 0,.answer 0] := by decide
  simp only [nativeEvent,hs,hr]
  rfl

def adverseCompleteS23Before := adverseCompleteProposal.take 22

theorem adverseCompleteS23Choice0 : nativeFirstChoice (indexScore (7/5) (controlPenalty savedCref uniformQuoteError unitRoleUnused .complete) adverseCompleteS23Before []) adverseCompleteS23Before [] = .query 1 := by
  apply complete_root_from_physical_gap adverseCompleteS23Before (adverseComplete_prefix_rewards 22) (by decide)
  · intro q; fin_cases q <;> decide
  · exact AgentUCTNextExact.adverse_complete_hyde_root_suffix_empty 22 (by omega)
  · intro q hq
    exact AgentUCTNextExact.adverse_complete_normal_root_physical_quote_exact 22 (by omega) q hq

theorem adverseCompleteS23D1I0 : indexScore (7/5) (controlPenalty savedCref uniformQuoteError unitRoleUnused .complete) adverseCompleteS23Before [.query 1] (.hydeRetriever 1) = treeIndex ((0/1)/5) (7/5) 0 15 5 := by
  have hs : replayBackup adverseCompleteS23Before emptyStatistics ([.query 1]++[.hydeRetriever 1]) = ⟨5,(0/1)⟩ := by
    rw [replayBackup_empty_closed_form]
    simp +decide [backedEvents,adverseCompleteS23Before,adverseCompleteProposal,adverseCompleteEvent1,adverseCompleteEvent2,adverseCompleteEvent3,adverseCompleteEvent4,adverseCompleteEvent5,adverseCompleteEvent6,adverseCompleteEvent7,adverseCompleteEvent8,adverseCompleteEvent9,adverseCompleteEvent10,adverseCompleteEvent11,adverseCompleteEvent12,adverseCompleteEvent13,adverseCompleteEvent14,adverseCompleteEvent15,adverseCompleteEvent16,adverseCompleteEvent17,adverseCompleteEvent18,adverseCompleteEvent19,adverseCompleteEvent20,adverseCompleteEvent21,adverseCompleteEvent22,taskReward]
    <;> norm_num
  have hp : rawVisits adverseCompleteS23Before [.query 1] = 15 := by decide
  have hn : rawVisits adverseCompleteS23Before ([.query 1]++[.hydeRetriever 1]) = 5 := by decide
  have hz : (controlPenalty savedCref uniformQuoteError unitRoleUnused .complete) adverseCompleteS23Before [.query 1] (.hydeRetriever 1) = 0 := by
    apply control_penalty_empty_of_prior_terminal .complete savedCref uniformQuoteError adverseCompleteS23Before [.query 1] (.hydeRetriever 1) 8 (by decide)
    · decide
    · decide
  unfold indexScore
  rw [hs,hp,hn,hz]
  simp only [BackupStat.mean]
  norm_num

theorem adverseCompleteS23D1I1 : indexScore (7/5) (controlPenalty savedCref uniformQuoteError unitRoleUnused .complete) adverseCompleteS23Before [.query 1] (.hydeRetriever 0) = treeIndex ((0/1)/5) (7/5) 0 15 5 := by
  have hs : replayBackup adverseCompleteS23Before emptyStatistics ([.query 1]++[.hydeRetriever 0]) = ⟨5,(0/1)⟩ := by
    rw [replayBackup_empty_closed_form]
    simp +decide [backedEvents,adverseCompleteS23Before,adverseCompleteProposal,adverseCompleteEvent1,adverseCompleteEvent2,adverseCompleteEvent3,adverseCompleteEvent4,adverseCompleteEvent5,adverseCompleteEvent6,adverseCompleteEvent7,adverseCompleteEvent8,adverseCompleteEvent9,adverseCompleteEvent10,adverseCompleteEvent11,adverseCompleteEvent12,adverseCompleteEvent13,adverseCompleteEvent14,adverseCompleteEvent15,adverseCompleteEvent16,adverseCompleteEvent17,adverseCompleteEvent18,adverseCompleteEvent19,adverseCompleteEvent20,adverseCompleteEvent21,adverseCompleteEvent22,taskReward]
    <;> norm_num
  have hp : rawVisits adverseCompleteS23Before [.query 1] = 15 := by decide
  have hn : rawVisits adverseCompleteS23Before ([.query 1]++[.hydeRetriever 0]) = 5 := by decide
  have hz : (controlPenalty savedCref uniformQuoteError unitRoleUnused .complete) adverseCompleteS23Before [.query 1] (.hydeRetriever 0) = 0 := by
    apply control_penalty_empty_of_prior_terminal .complete savedCref uniformQuoteError adverseCompleteS23Before [.query 1] (.hydeRetriever 0) 1 (by decide)
    · decide
    · decide
  unfold indexScore
  rw [hs,hp,hn,hz]
  simp only [BackupStat.mean]
  norm_num

theorem adverseCompleteS23D1I2 : indexScore (7/5) (controlPenalty savedCref uniformQuoteError unitRoleUnused .complete) adverseCompleteS23Before [.query 1] (.hydeRetriever 2) = treeIndex ((0/1)/4) (7/5) 0 15 4 := by
  have hs : replayBackup adverseCompleteS23Before emptyStatistics ([.query 1]++[.hydeRetriever 2]) = ⟨4,(0/1)⟩ := by
    rw [replayBackup_empty_closed_form]
    simp +decide [backedEvents,adverseCompleteS23Before,adverseCompleteProposal,adverseCompleteEvent1,adverseCompleteEvent2,adverseCompleteEvent3,adverseCompleteEvent4,adverseCompleteEvent5,adverseCompleteEvent6,adverseCompleteEvent7,adverseCompleteEvent8,adverseCompleteEvent9,adverseCompleteEvent10,adverseCompleteEvent11,adverseCompleteEvent12,adverseCompleteEvent13,adverseCompleteEvent14,adverseCompleteEvent15,adverseCompleteEvent16,adverseCompleteEvent17,adverseCompleteEvent18,adverseCompleteEvent19,adverseCompleteEvent20,adverseCompleteEvent21,adverseCompleteEvent22,taskReward]
    <;> norm_num
  have hp : rawVisits adverseCompleteS23Before [.query 1] = 15 := by decide
  have hn : rawVisits adverseCompleteS23Before ([.query 1]++[.hydeRetriever 2]) = 4 := by decide
  have hz : (controlPenalty savedCref uniformQuoteError unitRoleUnused .complete) adverseCompleteS23Before [.query 1] (.hydeRetriever 2) = 0 := by
    apply control_penalty_empty_of_prior_terminal .complete savedCref uniformQuoteError adverseCompleteS23Before [.query 1] (.hydeRetriever 2) 10 (by decide)
    · decide
    · decide
  unfold indexScore
  rw [hs,hp,hn,hz]
  simp only [BackupStat.mean]
  norm_num

theorem adverseCompleteS23D1Cmp0 : indexScore (7/5) (controlPenalty savedCref uniformQuoteError unitRoleUnused .complete) adverseCompleteS23Before [.query 1] (.hydeRetriever 1) < indexScore (7/5) (controlPenalty savedCref uniformQuoteError unitRoleUnused .complete) adverseCompleteS23Before [.query 1] (.hydeRetriever 2) := by
  rw [adverseCompleteS23D1I0,adverseCompleteS23D1I2]
  have h := index_strict_order_from_intervals ((0/1)/4) ((0/1)/5) 0 0 (29139411/25000000) (10425233/10000000)
    (treeBonus (7/5) 15 4) (treeBonus (7/5) 15 5)
    (trajectory_bonus_15_4).1 (trajectory_bonus_15_5).2 (by norm_num)
  simpa only [treeIndex,sub_zero] using h

theorem adverseCompleteS23D1Cmp1 : indexScore (7/5) (controlPenalty savedCref uniformQuoteError unitRoleUnused .complete) adverseCompleteS23Before [.query 1] (.hydeRetriever 0) < indexScore (7/5) (controlPenalty savedCref uniformQuoteError unitRoleUnused .complete) adverseCompleteS23Before [.query 1] (.hydeRetriever 2) := by
  rw [adverseCompleteS23D1I1,adverseCompleteS23D1I2]
  have h := index_strict_order_from_intervals ((0/1)/4) ((0/1)/5) 0 0 (29139411/25000000) (10425233/10000000)
    (treeBonus (7/5) 15 4) (treeBonus (7/5) 15 5)
    (trajectory_bonus_15_4).1 (trajectory_bonus_15_5).2 (by norm_num)
  simpa only [treeIndex,sub_zero] using h

theorem adverseCompleteS23Choice1 : nativeFirstChoice (indexScore (7/5) (controlPenalty savedCref uniformQuoteError unitRoleUnused .complete) adverseCompleteS23Before [.query 1]) adverseCompleteS23Before [.query 1] = .hydeRetriever 2 := by
  apply visited_choice_from_ordered_certificate _ _ [.query 1] [.hydeRetriever 1,.hydeRetriever 0] [] (.hydeRetriever 2) (by decide)
  · intro a ha
    have ho : orderedLegalAvailable [.query 1] = [.hydeRetriever 1,.hydeRetriever 0,.hydeRetriever 2] := by decide
    rw [ho] at ha
    simp only [List.mem_cons,List.not_mem_nil,or_false] at ha
    rcases ha with rfl | rfl | rfl <;> decide
  · intro a ha
    simp only [List.mem_cons,List.not_mem_nil,or_false] at ha
    rcases ha with rfl | rfl
    · exact adverseCompleteS23D1Cmp0
    · exact adverseCompleteS23D1Cmp1
  · simp

theorem adverseCompleteS23ActualEvent : nativeEvent budgetTape (7/5) (controlPenalty savedCref uniformQuoteError unitRoleUnused .complete)
    (taskReward true (2/5) (1/2)) adverseCompleteS23Before = adverseCompleteEvent23 := by
  have hs0 := native_select_existing_step budgetTape (7/5) (controlPenalty savedCref uniformQuoteError unitRoleUnused .complete) adverseCompleteS23Before 8 [] (.query 1)
    (by decide) (by decide) adverseCompleteS23Choice0
  have hs1 := native_select_existing_step budgetTape (7/5) (controlPenalty savedCref uniformQuoteError unitRoleUnused .complete) adverseCompleteS23Before 7 [.query 1] (.hydeRetriever 2)
    (by decide) (by decide) adverseCompleteS23Choice1
  have hnew := native_select_new_step budgetTape (7/5) (controlPenalty savedCref uniformQuoteError unitRoleUnused .complete) adverseCompleteS23Before 6 [.query 1,.hydeRetriever 2]
    [.selection 3] (.selection 3) (by decide) (by decide) (by decide) (by decide)
  have hs : nativeSelect budgetTape (7/5) (controlPenalty savedCref uniformQuoteError unitRoleUnused .complete) adverseCompleteS23Before 9 [] = [.query 1,.hydeRetriever 2,.selection 3] := by
    rw [hs0]
    change nativeSelect budgetTape (7/5) (controlPenalty savedCref uniformQuoteError unitRoleUnused .complete) adverseCompleteS23Before 8 [.query 1] = _
    rw [hs1]
    change nativeSelect budgetTape (7/5) (controlPenalty savedCref uniformQuoteError unitRoleUnused .complete) adverseCompleteS23Before 7 [.query 1,.hydeRetriever 2] = _
    rw [hnew] <;> rfl
  have hr : repairedRollout budgetTape adverseCompleteS23Before 9 [.query 1,.hydeRetriever 2,.selection 3] = [.query 1,.hydeRetriever 2,.selection 3,.width 0,.stop,.reranker 0,.topm 0,.context 0,.answer 0] := by decide
  simp only [nativeEvent,hs,hr]
  rfl

def adverseCompleteS24Before := adverseCompleteProposal.take 23

theorem adverseCompleteS24Choice0 : nativeFirstChoice (indexScore (7/5) (controlPenalty savedCref uniformQuoteError unitRoleUnused .complete) adverseCompleteS24Before []) adverseCompleteS24Before [] = .query 1 := by
  apply complete_root_from_physical_gap adverseCompleteS24Before (adverseComplete_prefix_rewards 23) (by decide)
  · intro q; fin_cases q <;> decide
  · exact AgentUCTNextExact.adverse_complete_hyde_root_suffix_empty 23 (by omega)
  · intro q hq
    exact AgentUCTNextExact.adverse_complete_normal_root_physical_quote_exact 23 (by omega) q hq

theorem adverseCompleteS24D1I0 : indexScore (7/5) (controlPenalty savedCref uniformQuoteError unitRoleUnused .complete) adverseCompleteS24Before [.query 1] (.hydeRetriever 1) = treeIndex ((0/1)/5) (7/5) 0 16 5 := by
  have hs : replayBackup adverseCompleteS24Before emptyStatistics ([.query 1]++[.hydeRetriever 1]) = ⟨5,(0/1)⟩ := by
    rw [replayBackup_empty_closed_form]
    simp +decide [backedEvents,adverseCompleteS24Before,adverseCompleteProposal,adverseCompleteEvent1,adverseCompleteEvent2,adverseCompleteEvent3,adverseCompleteEvent4,adverseCompleteEvent5,adverseCompleteEvent6,adverseCompleteEvent7,adverseCompleteEvent8,adverseCompleteEvent9,adverseCompleteEvent10,adverseCompleteEvent11,adverseCompleteEvent12,adverseCompleteEvent13,adverseCompleteEvent14,adverseCompleteEvent15,adverseCompleteEvent16,adverseCompleteEvent17,adverseCompleteEvent18,adverseCompleteEvent19,adverseCompleteEvent20,adverseCompleteEvent21,adverseCompleteEvent22,adverseCompleteEvent23,taskReward]
    <;> norm_num
  have hp : rawVisits adverseCompleteS24Before [.query 1] = 16 := by decide
  have hn : rawVisits adverseCompleteS24Before ([.query 1]++[.hydeRetriever 1]) = 5 := by decide
  have hz : (controlPenalty savedCref uniformQuoteError unitRoleUnused .complete) adverseCompleteS24Before [.query 1] (.hydeRetriever 1) = 0 := by
    apply control_penalty_empty_of_prior_terminal .complete savedCref uniformQuoteError adverseCompleteS24Before [.query 1] (.hydeRetriever 1) 8 (by decide)
    · decide
    · decide
  unfold indexScore
  rw [hs,hp,hn,hz]
  simp only [BackupStat.mean]
  norm_num

theorem adverseCompleteS24D1I1 : indexScore (7/5) (controlPenalty savedCref uniformQuoteError unitRoleUnused .complete) adverseCompleteS24Before [.query 1] (.hydeRetriever 0) = treeIndex ((0/1)/5) (7/5) 0 16 5 := by
  have hs : replayBackup adverseCompleteS24Before emptyStatistics ([.query 1]++[.hydeRetriever 0]) = ⟨5,(0/1)⟩ := by
    rw [replayBackup_empty_closed_form]
    simp +decide [backedEvents,adverseCompleteS24Before,adverseCompleteProposal,adverseCompleteEvent1,adverseCompleteEvent2,adverseCompleteEvent3,adverseCompleteEvent4,adverseCompleteEvent5,adverseCompleteEvent6,adverseCompleteEvent7,adverseCompleteEvent8,adverseCompleteEvent9,adverseCompleteEvent10,adverseCompleteEvent11,adverseCompleteEvent12,adverseCompleteEvent13,adverseCompleteEvent14,adverseCompleteEvent15,adverseCompleteEvent16,adverseCompleteEvent17,adverseCompleteEvent18,adverseCompleteEvent19,adverseCompleteEvent20,adverseCompleteEvent21,adverseCompleteEvent22,adverseCompleteEvent23,taskReward]
    <;> norm_num
  have hp : rawVisits adverseCompleteS24Before [.query 1] = 16 := by decide
  have hn : rawVisits adverseCompleteS24Before ([.query 1]++[.hydeRetriever 0]) = 5 := by decide
  have hz : (controlPenalty savedCref uniformQuoteError unitRoleUnused .complete) adverseCompleteS24Before [.query 1] (.hydeRetriever 0) = 0 := by
    apply control_penalty_empty_of_prior_terminal .complete savedCref uniformQuoteError adverseCompleteS24Before [.query 1] (.hydeRetriever 0) 1 (by decide)
    · decide
    · decide
  unfold indexScore
  rw [hs,hp,hn,hz]
  simp only [BackupStat.mean]
  norm_num

theorem adverseCompleteS24D1I2 : indexScore (7/5) (controlPenalty savedCref uniformQuoteError unitRoleUnused .complete) adverseCompleteS24Before [.query 1] (.hydeRetriever 2) = treeIndex ((0/1)/5) (7/5) 0 16 5 := by
  have hs : replayBackup adverseCompleteS24Before emptyStatistics ([.query 1]++[.hydeRetriever 2]) = ⟨5,(0/1)⟩ := by
    rw [replayBackup_empty_closed_form]
    simp +decide [backedEvents,adverseCompleteS24Before,adverseCompleteProposal,adverseCompleteEvent1,adverseCompleteEvent2,adverseCompleteEvent3,adverseCompleteEvent4,adverseCompleteEvent5,adverseCompleteEvent6,adverseCompleteEvent7,adverseCompleteEvent8,adverseCompleteEvent9,adverseCompleteEvent10,adverseCompleteEvent11,adverseCompleteEvent12,adverseCompleteEvent13,adverseCompleteEvent14,adverseCompleteEvent15,adverseCompleteEvent16,adverseCompleteEvent17,adverseCompleteEvent18,adverseCompleteEvent19,adverseCompleteEvent20,adverseCompleteEvent21,adverseCompleteEvent22,adverseCompleteEvent23,taskReward]
    <;> norm_num
  have hp : rawVisits adverseCompleteS24Before [.query 1] = 16 := by decide
  have hn : rawVisits adverseCompleteS24Before ([.query 1]++[.hydeRetriever 2]) = 5 := by decide
  have hz : (controlPenalty savedCref uniformQuoteError unitRoleUnused .complete) adverseCompleteS24Before [.query 1] (.hydeRetriever 2) = 0 := by
    apply control_penalty_empty_of_prior_terminal .complete savedCref uniformQuoteError adverseCompleteS24Before [.query 1] (.hydeRetriever 2) 10 (by decide)
    · decide
    · decide
  unfold indexScore
  rw [hs,hp,hn,hz]
  simp only [BackupStat.mean]
  norm_num

theorem adverseCompleteS24D1Cmp1 : indexScore (7/5) (controlPenalty savedCref uniformQuoteError unitRoleUnused .complete) adverseCompleteS24Before [.query 1] (.hydeRetriever 0) ≤ indexScore (7/5) (controlPenalty savedCref uniformQuoteError unitRoleUnused .complete) adverseCompleteS24Before [.query 1] (.hydeRetriever 1) := by
  rw [adverseCompleteS24D1I1,adverseCompleteS24D1I0]

theorem adverseCompleteS24D1Cmp2 : indexScore (7/5) (controlPenalty savedCref uniformQuoteError unitRoleUnused .complete) adverseCompleteS24Before [.query 1] (.hydeRetriever 2) ≤ indexScore (7/5) (controlPenalty savedCref uniformQuoteError unitRoleUnused .complete) adverseCompleteS24Before [.query 1] (.hydeRetriever 1) := by
  rw [adverseCompleteS24D1I2,adverseCompleteS24D1I0]

theorem adverseCompleteS24Choice1 : nativeFirstChoice (indexScore (7/5) (controlPenalty savedCref uniformQuoteError unitRoleUnused .complete) adverseCompleteS24Before [.query 1]) adverseCompleteS24Before [.query 1] = .hydeRetriever 1 := by
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
    · exact adverseCompleteS24D1Cmp1
    · exact adverseCompleteS24D1Cmp2

theorem adverseCompleteS24D2I0 : indexScore (7/5) (controlPenalty savedCref uniformQuoteError unitRoleUnused .complete) adverseCompleteS24Before [.query 1,.hydeRetriever 1] (.selection 1) = treeIndex ((0/1)/1) (7/5) 0 5 1 := by
  have hs : replayBackup adverseCompleteS24Before emptyStatistics ([.query 1,.hydeRetriever 1]++[.selection 1]) = ⟨1,(0/1)⟩ := by
    rw [replayBackup_empty_closed_form]
    simp +decide [backedEvents,adverseCompleteS24Before,adverseCompleteProposal,adverseCompleteEvent1,adverseCompleteEvent2,adverseCompleteEvent3,adverseCompleteEvent4,adverseCompleteEvent5,adverseCompleteEvent6,adverseCompleteEvent7,adverseCompleteEvent8,adverseCompleteEvent9,adverseCompleteEvent10,adverseCompleteEvent11,adverseCompleteEvent12,adverseCompleteEvent13,adverseCompleteEvent14,adverseCompleteEvent15,adverseCompleteEvent16,adverseCompleteEvent17,adverseCompleteEvent18,adverseCompleteEvent19,adverseCompleteEvent20,adverseCompleteEvent21,adverseCompleteEvent22,adverseCompleteEvent23,taskReward]
    <;> norm_num
  have hp : rawVisits adverseCompleteS24Before [.query 1,.hydeRetriever 1] = 5 := by decide
  have hn : rawVisits adverseCompleteS24Before ([.query 1,.hydeRetriever 1]++[.selection 1]) = 1 := by decide
  have hz : (controlPenalty savedCref uniformQuoteError unitRoleUnused .complete) adverseCompleteS24Before [.query 1,.hydeRetriever 1] (.selection 1) = 0 := by
    apply control_penalty_empty_of_prior_terminal .complete savedCref uniformQuoteError adverseCompleteS24Before [.query 1,.hydeRetriever 1] (.selection 1) 14 (by decide)
    · decide
    · decide
  unfold indexScore
  rw [hs,hp,hn,hz]
  simp only [BackupStat.mean]
  norm_num

theorem adverseCompleteS24D2I1 : indexScore (7/5) (controlPenalty savedCref uniformQuoteError unitRoleUnused .complete) adverseCompleteS24Before [.query 1,.hydeRetriever 1] (.selection 2) = treeIndex ((0/1)/1) (7/5) 0 5 1 := by
  have hs : replayBackup adverseCompleteS24Before emptyStatistics ([.query 1,.hydeRetriever 1]++[.selection 2]) = ⟨1,(0/1)⟩ := by
    rw [replayBackup_empty_closed_form]
    simp +decide [backedEvents,adverseCompleteS24Before,adverseCompleteProposal,adverseCompleteEvent1,adverseCompleteEvent2,adverseCompleteEvent3,adverseCompleteEvent4,adverseCompleteEvent5,adverseCompleteEvent6,adverseCompleteEvent7,adverseCompleteEvent8,adverseCompleteEvent9,adverseCompleteEvent10,adverseCompleteEvent11,adverseCompleteEvent12,adverseCompleteEvent13,adverseCompleteEvent14,adverseCompleteEvent15,adverseCompleteEvent16,adverseCompleteEvent17,adverseCompleteEvent18,adverseCompleteEvent19,adverseCompleteEvent20,adverseCompleteEvent21,adverseCompleteEvent22,adverseCompleteEvent23,taskReward]
    <;> norm_num
  have hp : rawVisits adverseCompleteS24Before [.query 1,.hydeRetriever 1] = 5 := by decide
  have hn : rawVisits adverseCompleteS24Before ([.query 1,.hydeRetriever 1]++[.selection 2]) = 1 := by decide
  have hz : (controlPenalty savedCref uniformQuoteError unitRoleUnused .complete) adverseCompleteS24Before [.query 1,.hydeRetriever 1] (.selection 2) = 0 := by
    apply control_penalty_empty_of_prior_terminal .complete savedCref uniformQuoteError adverseCompleteS24Before [.query 1,.hydeRetriever 1] (.selection 2) 17 (by decide)
    · decide
    · decide
  unfold indexScore
  rw [hs,hp,hn,hz]
  simp only [BackupStat.mean]
  norm_num

theorem adverseCompleteS24D2I2 : indexScore (7/5) (controlPenalty savedCref uniformQuoteError unitRoleUnused .complete) adverseCompleteS24Before [.query 1,.hydeRetriever 1] (.selection 3) = treeIndex ((0/1)/1) (7/5) 0 5 1 := by
  have hs : replayBackup adverseCompleteS24Before emptyStatistics ([.query 1,.hydeRetriever 1]++[.selection 3]) = ⟨1,(0/1)⟩ := by
    rw [replayBackup_empty_closed_form]
    simp +decide [backedEvents,adverseCompleteS24Before,adverseCompleteProposal,adverseCompleteEvent1,adverseCompleteEvent2,adverseCompleteEvent3,adverseCompleteEvent4,adverseCompleteEvent5,adverseCompleteEvent6,adverseCompleteEvent7,adverseCompleteEvent8,adverseCompleteEvent9,adverseCompleteEvent10,adverseCompleteEvent11,adverseCompleteEvent12,adverseCompleteEvent13,adverseCompleteEvent14,adverseCompleteEvent15,adverseCompleteEvent16,adverseCompleteEvent17,adverseCompleteEvent18,adverseCompleteEvent19,adverseCompleteEvent20,adverseCompleteEvent21,adverseCompleteEvent22,adverseCompleteEvent23,taskReward]
    <;> norm_num
  have hp : rawVisits adverseCompleteS24Before [.query 1,.hydeRetriever 1] = 5 := by decide
  have hn : rawVisits adverseCompleteS24Before ([.query 1,.hydeRetriever 1]++[.selection 3]) = 1 := by decide
  have hz : (controlPenalty savedCref uniformQuoteError unitRoleUnused .complete) adverseCompleteS24Before [.query 1,.hydeRetriever 1] (.selection 3) = 0 := by
    apply control_penalty_empty_of_prior_terminal .complete savedCref uniformQuoteError adverseCompleteS24Before [.query 1,.hydeRetriever 1] (.selection 3) 20 (by decide)
    · decide
    · decide
  unfold indexScore
  rw [hs,hp,hn,hz]
  simp only [BackupStat.mean]
  norm_num

theorem adverseCompleteS24D2I3 : indexScore (7/5) (controlPenalty savedCref uniformQuoteError unitRoleUnused .complete) adverseCompleteS24Before [.query 1,.hydeRetriever 1] (.selection 0) = treeIndex ((0/1)/1) (7/5) 0 5 1 := by
  have hs : replayBackup adverseCompleteS24Before emptyStatistics ([.query 1,.hydeRetriever 1]++[.selection 0]) = ⟨1,(0/1)⟩ := by
    rw [replayBackup_empty_closed_form]
    simp +decide [backedEvents,adverseCompleteS24Before,adverseCompleteProposal,adverseCompleteEvent1,adverseCompleteEvent2,adverseCompleteEvent3,adverseCompleteEvent4,adverseCompleteEvent5,adverseCompleteEvent6,adverseCompleteEvent7,adverseCompleteEvent8,adverseCompleteEvent9,adverseCompleteEvent10,adverseCompleteEvent11,adverseCompleteEvent12,adverseCompleteEvent13,adverseCompleteEvent14,adverseCompleteEvent15,adverseCompleteEvent16,adverseCompleteEvent17,adverseCompleteEvent18,adverseCompleteEvent19,adverseCompleteEvent20,adverseCompleteEvent21,adverseCompleteEvent22,adverseCompleteEvent23,taskReward]
    <;> norm_num
  have hp : rawVisits adverseCompleteS24Before [.query 1,.hydeRetriever 1] = 5 := by decide
  have hn : rawVisits adverseCompleteS24Before ([.query 1,.hydeRetriever 1]++[.selection 0]) = 1 := by decide
  have hz : (controlPenalty savedCref uniformQuoteError unitRoleUnused .complete) adverseCompleteS24Before [.query 1,.hydeRetriever 1] (.selection 0) = 0 := by
    apply control_penalty_empty_of_prior_terminal .complete savedCref uniformQuoteError adverseCompleteS24Before [.query 1,.hydeRetriever 1] (.selection 0) 8 (by decide)
    · decide
    · decide
  unfold indexScore
  rw [hs,hp,hn,hz]
  simp only [BackupStat.mean]
  norm_num

theorem adverseCompleteS24D2Cmp1 : indexScore (7/5) (controlPenalty savedCref uniformQuoteError unitRoleUnused .complete) adverseCompleteS24Before [.query 1,.hydeRetriever 1] (.selection 2) ≤ indexScore (7/5) (controlPenalty savedCref uniformQuoteError unitRoleUnused .complete) adverseCompleteS24Before [.query 1,.hydeRetriever 1] (.selection 1) := by
  rw [adverseCompleteS24D2I1,adverseCompleteS24D2I0]

theorem adverseCompleteS24D2Cmp2 : indexScore (7/5) (controlPenalty savedCref uniformQuoteError unitRoleUnused .complete) adverseCompleteS24Before [.query 1,.hydeRetriever 1] (.selection 3) ≤ indexScore (7/5) (controlPenalty savedCref uniformQuoteError unitRoleUnused .complete) adverseCompleteS24Before [.query 1,.hydeRetriever 1] (.selection 1) := by
  rw [adverseCompleteS24D2I2,adverseCompleteS24D2I0]

theorem adverseCompleteS24D2Cmp3 : indexScore (7/5) (controlPenalty savedCref uniformQuoteError unitRoleUnused .complete) adverseCompleteS24Before [.query 1,.hydeRetriever 1] (.selection 0) ≤ indexScore (7/5) (controlPenalty savedCref uniformQuoteError unitRoleUnused .complete) adverseCompleteS24Before [.query 1,.hydeRetriever 1] (.selection 1) := by
  rw [adverseCompleteS24D2I3,adverseCompleteS24D2I0]

theorem adverseCompleteS24Choice2 : nativeFirstChoice (indexScore (7/5) (controlPenalty savedCref uniformQuoteError unitRoleUnused .complete) adverseCompleteS24Before [.query 1,.hydeRetriever 1]) adverseCompleteS24Before [.query 1,.hydeRetriever 1] = .selection 1 := by
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
    · exact adverseCompleteS24D2Cmp1
    · exact adverseCompleteS24D2Cmp2
    · exact adverseCompleteS24D2Cmp3

theorem adverseCompleteS24ActualEvent : nativeEvent budgetTape (7/5) (controlPenalty savedCref uniformQuoteError unitRoleUnused .complete)
    (taskReward true (2/5) (1/2)) adverseCompleteS24Before = adverseCompleteEvent24 := by
  have hs0 := native_select_existing_step budgetTape (7/5) (controlPenalty savedCref uniformQuoteError unitRoleUnused .complete) adverseCompleteS24Before 8 [] (.query 1)
    (by decide) (by decide) adverseCompleteS24Choice0
  have hs1 := native_select_existing_step budgetTape (7/5) (controlPenalty savedCref uniformQuoteError unitRoleUnused .complete) adverseCompleteS24Before 7 [.query 1] (.hydeRetriever 1)
    (by decide) (by decide) adverseCompleteS24Choice1
  have hs2 := native_select_existing_step budgetTape (7/5) (controlPenalty savedCref uniformQuoteError unitRoleUnused .complete) adverseCompleteS24Before 6 [.query 1,.hydeRetriever 1] (.selection 1)
    (by decide) (by decide) adverseCompleteS24Choice2
  have hnew := native_select_new_step budgetTape (7/5) (controlPenalty savedCref uniformQuoteError unitRoleUnused .complete) adverseCompleteS24Before 5 [.query 1,.hydeRetriever 1,.selection 1]
    [.width 3,.width 0,.width 1,.width 2] (.width 0) (by decide) (by decide) (by decide) (by decide)
  have hs : nativeSelect budgetTape (7/5) (controlPenalty savedCref uniformQuoteError unitRoleUnused .complete) adverseCompleteS24Before 9 [] = [.query 1,.hydeRetriever 1,.selection 1,.width 0] := by
    rw [hs0]
    change nativeSelect budgetTape (7/5) (controlPenalty savedCref uniformQuoteError unitRoleUnused .complete) adverseCompleteS24Before 8 [.query 1] = _
    rw [hs1]
    change nativeSelect budgetTape (7/5) (controlPenalty savedCref uniformQuoteError unitRoleUnused .complete) adverseCompleteS24Before 7 [.query 1,.hydeRetriever 1] = _
    rw [hs2]
    change nativeSelect budgetTape (7/5) (controlPenalty savedCref uniformQuoteError unitRoleUnused .complete) adverseCompleteS24Before 6 [.query 1,.hydeRetriever 1,.selection 1] = _
    rw [hnew] <;> rfl
  have hr : repairedRollout budgetTape adverseCompleteS24Before 9 [.query 1,.hydeRetriever 1,.selection 1,.width 0] = [.query 1,.hydeRetriever 1,.selection 1,.width 0,.stop,.reranker 0,.topm 0,.context 0,.answer 0] := by decide
  simp only [nativeEvent,hs,hr]
  rfl

def adverseCompleteS25Before := adverseCompleteProposal.take 24

theorem adverseCompleteS25Choice0 : nativeFirstChoice (indexScore (7/5) (controlPenalty savedCref uniformQuoteError unitRoleUnused .complete) adverseCompleteS25Before []) adverseCompleteS25Before [] = .query 1 := by
  apply complete_root_from_physical_gap adverseCompleteS25Before (adverseComplete_prefix_rewards 24) (by decide)
  · intro q; fin_cases q <;> decide
  · exact AgentUCTNextExact.adverse_complete_hyde_root_suffix_empty 24 (by omega)
  · intro q hq
    exact AgentUCTNextExact.adverse_complete_normal_root_physical_quote_exact 24 (by omega) q hq

theorem adverseCompleteS25D1I0 : indexScore (7/5) (controlPenalty savedCref uniformQuoteError unitRoleUnused .complete) adverseCompleteS25Before [.query 1] (.hydeRetriever 1) = treeIndex ((0/1)/6) (7/5) 0 17 6 := by
  have hs : replayBackup adverseCompleteS25Before emptyStatistics ([.query 1]++[.hydeRetriever 1]) = ⟨6,(0/1)⟩ := by
    rw [replayBackup_empty_closed_form]
    simp +decide [backedEvents,adverseCompleteS25Before,adverseCompleteProposal,adverseCompleteEvent1,adverseCompleteEvent2,adverseCompleteEvent3,adverseCompleteEvent4,adverseCompleteEvent5,adverseCompleteEvent6,adverseCompleteEvent7,adverseCompleteEvent8,adverseCompleteEvent9,adverseCompleteEvent10,adverseCompleteEvent11,adverseCompleteEvent12,adverseCompleteEvent13,adverseCompleteEvent14,adverseCompleteEvent15,adverseCompleteEvent16,adverseCompleteEvent17,adverseCompleteEvent18,adverseCompleteEvent19,adverseCompleteEvent20,adverseCompleteEvent21,adverseCompleteEvent22,adverseCompleteEvent23,adverseCompleteEvent24,taskReward]
    <;> norm_num
  have hp : rawVisits adverseCompleteS25Before [.query 1] = 17 := by decide
  have hn : rawVisits adverseCompleteS25Before ([.query 1]++[.hydeRetriever 1]) = 6 := by decide
  have hz : (controlPenalty savedCref uniformQuoteError unitRoleUnused .complete) adverseCompleteS25Before [.query 1] (.hydeRetriever 1) = 0 := by
    apply control_penalty_empty_of_prior_terminal .complete savedCref uniformQuoteError adverseCompleteS25Before [.query 1] (.hydeRetriever 1) 8 (by decide)
    · decide
    · decide
  unfold indexScore
  rw [hs,hp,hn,hz]
  simp only [BackupStat.mean]
  norm_num

theorem adverseCompleteS25D1I1 : indexScore (7/5) (controlPenalty savedCref uniformQuoteError unitRoleUnused .complete) adverseCompleteS25Before [.query 1] (.hydeRetriever 0) = treeIndex ((0/1)/5) (7/5) 0 17 5 := by
  have hs : replayBackup adverseCompleteS25Before emptyStatistics ([.query 1]++[.hydeRetriever 0]) = ⟨5,(0/1)⟩ := by
    rw [replayBackup_empty_closed_form]
    simp +decide [backedEvents,adverseCompleteS25Before,adverseCompleteProposal,adverseCompleteEvent1,adverseCompleteEvent2,adverseCompleteEvent3,adverseCompleteEvent4,adverseCompleteEvent5,adverseCompleteEvent6,adverseCompleteEvent7,adverseCompleteEvent8,adverseCompleteEvent9,adverseCompleteEvent10,adverseCompleteEvent11,adverseCompleteEvent12,adverseCompleteEvent13,adverseCompleteEvent14,adverseCompleteEvent15,adverseCompleteEvent16,adverseCompleteEvent17,adverseCompleteEvent18,adverseCompleteEvent19,adverseCompleteEvent20,adverseCompleteEvent21,adverseCompleteEvent22,adverseCompleteEvent23,adverseCompleteEvent24,taskReward]
    <;> norm_num
  have hp : rawVisits adverseCompleteS25Before [.query 1] = 17 := by decide
  have hn : rawVisits adverseCompleteS25Before ([.query 1]++[.hydeRetriever 0]) = 5 := by decide
  have hz : (controlPenalty savedCref uniformQuoteError unitRoleUnused .complete) adverseCompleteS25Before [.query 1] (.hydeRetriever 0) = 0 := by
    apply control_penalty_empty_of_prior_terminal .complete savedCref uniformQuoteError adverseCompleteS25Before [.query 1] (.hydeRetriever 0) 1 (by decide)
    · decide
    · decide
  unfold indexScore
  rw [hs,hp,hn,hz]
  simp only [BackupStat.mean]
  norm_num

theorem adverseCompleteS25D1I2 : indexScore (7/5) (controlPenalty savedCref uniformQuoteError unitRoleUnused .complete) adverseCompleteS25Before [.query 1] (.hydeRetriever 2) = treeIndex ((0/1)/5) (7/5) 0 17 5 := by
  have hs : replayBackup adverseCompleteS25Before emptyStatistics ([.query 1]++[.hydeRetriever 2]) = ⟨5,(0/1)⟩ := by
    rw [replayBackup_empty_closed_form]
    simp +decide [backedEvents,adverseCompleteS25Before,adverseCompleteProposal,adverseCompleteEvent1,adverseCompleteEvent2,adverseCompleteEvent3,adverseCompleteEvent4,adverseCompleteEvent5,adverseCompleteEvent6,adverseCompleteEvent7,adverseCompleteEvent8,adverseCompleteEvent9,adverseCompleteEvent10,adverseCompleteEvent11,adverseCompleteEvent12,adverseCompleteEvent13,adverseCompleteEvent14,adverseCompleteEvent15,adverseCompleteEvent16,adverseCompleteEvent17,adverseCompleteEvent18,adverseCompleteEvent19,adverseCompleteEvent20,adverseCompleteEvent21,adverseCompleteEvent22,adverseCompleteEvent23,adverseCompleteEvent24,taskReward]
    <;> norm_num
  have hp : rawVisits adverseCompleteS25Before [.query 1] = 17 := by decide
  have hn : rawVisits adverseCompleteS25Before ([.query 1]++[.hydeRetriever 2]) = 5 := by decide
  have hz : (controlPenalty savedCref uniformQuoteError unitRoleUnused .complete) adverseCompleteS25Before [.query 1] (.hydeRetriever 2) = 0 := by
    apply control_penalty_empty_of_prior_terminal .complete savedCref uniformQuoteError adverseCompleteS25Before [.query 1] (.hydeRetriever 2) 10 (by decide)
    · decide
    · decide
  unfold indexScore
  rw [hs,hp,hn,hz]
  simp only [BackupStat.mean]
  norm_num

theorem adverseCompleteS25D1Cmp0 : indexScore (7/5) (controlPenalty savedCref uniformQuoteError unitRoleUnused .complete) adverseCompleteS25Before [.query 1] (.hydeRetriever 1) < indexScore (7/5) (controlPenalty savedCref uniformQuoteError unitRoleUnused .complete) adverseCompleteS25Before [.query 1] (.hydeRetriever 0) := by
  rw [adverseCompleteS25D1I0,adverseCompleteS25D1I1]
  have h := index_strict_order_from_intervals ((0/1)/5) ((0/1)/6) 0 0 (665273/625000) (12146169/12500000)
    (treeBonus (7/5) 17 5) (treeBonus (7/5) 17 6)
    (trajectory_bonus_17_5).1 (trajectory_bonus_17_6).2 (by norm_num)
  simpa only [treeIndex,sub_zero] using h

theorem adverseCompleteS25D1Cmp2 : indexScore (7/5) (controlPenalty savedCref uniformQuoteError unitRoleUnused .complete) adverseCompleteS25Before [.query 1] (.hydeRetriever 2) ≤ indexScore (7/5) (controlPenalty savedCref uniformQuoteError unitRoleUnused .complete) adverseCompleteS25Before [.query 1] (.hydeRetriever 0) := by
  rw [adverseCompleteS25D1I2,adverseCompleteS25D1I1]

theorem adverseCompleteS25Choice1 : nativeFirstChoice (indexScore (7/5) (controlPenalty savedCref uniformQuoteError unitRoleUnused .complete) adverseCompleteS25Before [.query 1]) adverseCompleteS25Before [.query 1] = .hydeRetriever 0 := by
  apply visited_choice_from_ordered_certificate _ _ [.query 1] [.hydeRetriever 1] [.hydeRetriever 2] (.hydeRetriever 0) (by decide)
  · intro a ha
    have ho : orderedLegalAvailable [.query 1] = [.hydeRetriever 1,.hydeRetriever 0,.hydeRetriever 2] := by decide
    rw [ho] at ha
    simp only [List.mem_cons,List.not_mem_nil,or_false] at ha
    rcases ha with rfl | rfl | rfl <;> decide
  · intro a ha
    simp only [List.mem_cons,List.not_mem_nil,or_false] at ha
    rcases ha with rfl
    · exact adverseCompleteS25D1Cmp0
  · intro a ha
    simp only [List.mem_cons,List.not_mem_nil,or_false] at ha
    rcases ha with rfl
    · exact adverseCompleteS25D1Cmp2

theorem adverseCompleteS25D2I0 : indexScore (7/5) (controlPenalty savedCref uniformQuoteError unitRoleUnused .complete) adverseCompleteS25Before [.query 1,.hydeRetriever 0] (.selection 1) = treeIndex ((0/1)/1) (7/5) 0 5 1 := by
  have hs : replayBackup adverseCompleteS25Before emptyStatistics ([.query 1,.hydeRetriever 0]++[.selection 1]) = ⟨1,(0/1)⟩ := by
    rw [replayBackup_empty_closed_form]
    simp +decide [backedEvents,adverseCompleteS25Before,adverseCompleteProposal,adverseCompleteEvent1,adverseCompleteEvent2,adverseCompleteEvent3,adverseCompleteEvent4,adverseCompleteEvent5,adverseCompleteEvent6,adverseCompleteEvent7,adverseCompleteEvent8,adverseCompleteEvent9,adverseCompleteEvent10,adverseCompleteEvent11,adverseCompleteEvent12,adverseCompleteEvent13,adverseCompleteEvent14,adverseCompleteEvent15,adverseCompleteEvent16,adverseCompleteEvent17,adverseCompleteEvent18,adverseCompleteEvent19,adverseCompleteEvent20,adverseCompleteEvent21,adverseCompleteEvent22,adverseCompleteEvent23,adverseCompleteEvent24,taskReward]
    <;> norm_num
  have hp : rawVisits adverseCompleteS25Before [.query 1,.hydeRetriever 0] = 5 := by decide
  have hn : rawVisits adverseCompleteS25Before ([.query 1,.hydeRetriever 0]++[.selection 1]) = 1 := by decide
  have hz : (controlPenalty savedCref uniformQuoteError unitRoleUnused .complete) adverseCompleteS25Before [.query 1,.hydeRetriever 0] (.selection 1) = 0 := by
    apply control_penalty_empty_of_prior_terminal .complete savedCref uniformQuoteError adverseCompleteS25Before [.query 1,.hydeRetriever 0] (.selection 1) 15 (by decide)
    · decide
    · decide
  unfold indexScore
  rw [hs,hp,hn,hz]
  simp only [BackupStat.mean]
  norm_num

theorem adverseCompleteS25D2I1 : indexScore (7/5) (controlPenalty savedCref uniformQuoteError unitRoleUnused .complete) adverseCompleteS25Before [.query 1,.hydeRetriever 0] (.selection 2) = treeIndex ((0/1)/1) (7/5) 0 5 1 := by
  have hs : replayBackup adverseCompleteS25Before emptyStatistics ([.query 1,.hydeRetriever 0]++[.selection 2]) = ⟨1,(0/1)⟩ := by
    rw [replayBackup_empty_closed_form]
    simp +decide [backedEvents,adverseCompleteS25Before,adverseCompleteProposal,adverseCompleteEvent1,adverseCompleteEvent2,adverseCompleteEvent3,adverseCompleteEvent4,adverseCompleteEvent5,adverseCompleteEvent6,adverseCompleteEvent7,adverseCompleteEvent8,adverseCompleteEvent9,adverseCompleteEvent10,adverseCompleteEvent11,adverseCompleteEvent12,adverseCompleteEvent13,adverseCompleteEvent14,adverseCompleteEvent15,adverseCompleteEvent16,adverseCompleteEvent17,adverseCompleteEvent18,adverseCompleteEvent19,adverseCompleteEvent20,adverseCompleteEvent21,adverseCompleteEvent22,adverseCompleteEvent23,adverseCompleteEvent24,taskReward]
    <;> norm_num
  have hp : rawVisits adverseCompleteS25Before [.query 1,.hydeRetriever 0] = 5 := by decide
  have hn : rawVisits adverseCompleteS25Before ([.query 1,.hydeRetriever 0]++[.selection 2]) = 1 := by decide
  have hz : (controlPenalty savedCref uniformQuoteError unitRoleUnused .complete) adverseCompleteS25Before [.query 1,.hydeRetriever 0] (.selection 2) = 0 := by
    apply control_penalty_empty_of_prior_terminal .complete savedCref uniformQuoteError adverseCompleteS25Before [.query 1,.hydeRetriever 0] (.selection 2) 18 (by decide)
    · decide
    · decide
  unfold indexScore
  rw [hs,hp,hn,hz]
  simp only [BackupStat.mean]
  norm_num

theorem adverseCompleteS25D2I2 : indexScore (7/5) (controlPenalty savedCref uniformQuoteError unitRoleUnused .complete) adverseCompleteS25Before [.query 1,.hydeRetriever 0] (.selection 3) = treeIndex ((0/1)/1) (7/5) 0 5 1 := by
  have hs : replayBackup adverseCompleteS25Before emptyStatistics ([.query 1,.hydeRetriever 0]++[.selection 3]) = ⟨1,(0/1)⟩ := by
    rw [replayBackup_empty_closed_form]
    simp +decide [backedEvents,adverseCompleteS25Before,adverseCompleteProposal,adverseCompleteEvent1,adverseCompleteEvent2,adverseCompleteEvent3,adverseCompleteEvent4,adverseCompleteEvent5,adverseCompleteEvent6,adverseCompleteEvent7,adverseCompleteEvent8,adverseCompleteEvent9,adverseCompleteEvent10,adverseCompleteEvent11,adverseCompleteEvent12,adverseCompleteEvent13,adverseCompleteEvent14,adverseCompleteEvent15,adverseCompleteEvent16,adverseCompleteEvent17,adverseCompleteEvent18,adverseCompleteEvent19,adverseCompleteEvent20,adverseCompleteEvent21,adverseCompleteEvent22,adverseCompleteEvent23,adverseCompleteEvent24,taskReward]
    <;> norm_num
  have hp : rawVisits adverseCompleteS25Before [.query 1,.hydeRetriever 0] = 5 := by decide
  have hn : rawVisits adverseCompleteS25Before ([.query 1,.hydeRetriever 0]++[.selection 3]) = 1 := by decide
  have hz : (controlPenalty savedCref uniformQuoteError unitRoleUnused .complete) adverseCompleteS25Before [.query 1,.hydeRetriever 0] (.selection 3) = 0 := by
    apply control_penalty_empty_of_prior_terminal .complete savedCref uniformQuoteError adverseCompleteS25Before [.query 1,.hydeRetriever 0] (.selection 3) 21 (by decide)
    · decide
    · decide
  unfold indexScore
  rw [hs,hp,hn,hz]
  simp only [BackupStat.mean]
  norm_num

theorem adverseCompleteS25D2I3 : indexScore (7/5) (controlPenalty savedCref uniformQuoteError unitRoleUnused .complete) adverseCompleteS25Before [.query 1,.hydeRetriever 0] (.selection 0) = treeIndex ((0/1)/1) (7/5) 0 5 1 := by
  have hs : replayBackup adverseCompleteS25Before emptyStatistics ([.query 1,.hydeRetriever 0]++[.selection 0]) = ⟨1,(0/1)⟩ := by
    rw [replayBackup_empty_closed_form]
    simp +decide [backedEvents,adverseCompleteS25Before,adverseCompleteProposal,adverseCompleteEvent1,adverseCompleteEvent2,adverseCompleteEvent3,adverseCompleteEvent4,adverseCompleteEvent5,adverseCompleteEvent6,adverseCompleteEvent7,adverseCompleteEvent8,adverseCompleteEvent9,adverseCompleteEvent10,adverseCompleteEvent11,adverseCompleteEvent12,adverseCompleteEvent13,adverseCompleteEvent14,adverseCompleteEvent15,adverseCompleteEvent16,adverseCompleteEvent17,adverseCompleteEvent18,adverseCompleteEvent19,adverseCompleteEvent20,adverseCompleteEvent21,adverseCompleteEvent22,adverseCompleteEvent23,adverseCompleteEvent24,taskReward]
    <;> norm_num
  have hp : rawVisits adverseCompleteS25Before [.query 1,.hydeRetriever 0] = 5 := by decide
  have hn : rawVisits adverseCompleteS25Before ([.query 1,.hydeRetriever 0]++[.selection 0]) = 1 := by decide
  have hz : (controlPenalty savedCref uniformQuoteError unitRoleUnused .complete) adverseCompleteS25Before [.query 1,.hydeRetriever 0] (.selection 0) = 0 := by
    apply control_penalty_empty_of_prior_terminal .complete savedCref uniformQuoteError adverseCompleteS25Before [.query 1,.hydeRetriever 0] (.selection 0) 1 (by decide)
    · decide
    · decide
  unfold indexScore
  rw [hs,hp,hn,hz]
  simp only [BackupStat.mean]
  norm_num

theorem adverseCompleteS25D2Cmp1 : indexScore (7/5) (controlPenalty savedCref uniformQuoteError unitRoleUnused .complete) adverseCompleteS25Before [.query 1,.hydeRetriever 0] (.selection 2) ≤ indexScore (7/5) (controlPenalty savedCref uniformQuoteError unitRoleUnused .complete) adverseCompleteS25Before [.query 1,.hydeRetriever 0] (.selection 1) := by
  rw [adverseCompleteS25D2I1,adverseCompleteS25D2I0]

theorem adverseCompleteS25D2Cmp2 : indexScore (7/5) (controlPenalty savedCref uniformQuoteError unitRoleUnused .complete) adverseCompleteS25Before [.query 1,.hydeRetriever 0] (.selection 3) ≤ indexScore (7/5) (controlPenalty savedCref uniformQuoteError unitRoleUnused .complete) adverseCompleteS25Before [.query 1,.hydeRetriever 0] (.selection 1) := by
  rw [adverseCompleteS25D2I2,adverseCompleteS25D2I0]

theorem adverseCompleteS25D2Cmp3 : indexScore (7/5) (controlPenalty savedCref uniformQuoteError unitRoleUnused .complete) adverseCompleteS25Before [.query 1,.hydeRetriever 0] (.selection 0) ≤ indexScore (7/5) (controlPenalty savedCref uniformQuoteError unitRoleUnused .complete) adverseCompleteS25Before [.query 1,.hydeRetriever 0] (.selection 1) := by
  rw [adverseCompleteS25D2I3,adverseCompleteS25D2I0]

theorem adverseCompleteS25Choice2 : nativeFirstChoice (indexScore (7/5) (controlPenalty savedCref uniformQuoteError unitRoleUnused .complete) adverseCompleteS25Before [.query 1,.hydeRetriever 0]) adverseCompleteS25Before [.query 1,.hydeRetriever 0] = .selection 1 := by
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
    · exact adverseCompleteS25D2Cmp1
    · exact adverseCompleteS25D2Cmp2
    · exact adverseCompleteS25D2Cmp3

theorem adverseCompleteS25ActualEvent : nativeEvent budgetTape (7/5) (controlPenalty savedCref uniformQuoteError unitRoleUnused .complete)
    (taskReward true (2/5) (1/2)) adverseCompleteS25Before = adverseCompleteEvent25 := by
  have hs0 := native_select_existing_step budgetTape (7/5) (controlPenalty savedCref uniformQuoteError unitRoleUnused .complete) adverseCompleteS25Before 8 [] (.query 1)
    (by decide) (by decide) adverseCompleteS25Choice0
  have hs1 := native_select_existing_step budgetTape (7/5) (controlPenalty savedCref uniformQuoteError unitRoleUnused .complete) adverseCompleteS25Before 7 [.query 1] (.hydeRetriever 0)
    (by decide) (by decide) adverseCompleteS25Choice1
  have hs2 := native_select_existing_step budgetTape (7/5) (controlPenalty savedCref uniformQuoteError unitRoleUnused .complete) adverseCompleteS25Before 6 [.query 1,.hydeRetriever 0] (.selection 1)
    (by decide) (by decide) adverseCompleteS25Choice2
  have hnew := native_select_new_step budgetTape (7/5) (controlPenalty savedCref uniformQuoteError unitRoleUnused .complete) adverseCompleteS25Before 5 [.query 1,.hydeRetriever 0,.selection 1]
    [.width 3,.width 0,.width 1,.width 2] (.width 0) (by decide) (by decide) (by decide) (by decide)
  have hs : nativeSelect budgetTape (7/5) (controlPenalty savedCref uniformQuoteError unitRoleUnused .complete) adverseCompleteS25Before 9 [] = [.query 1,.hydeRetriever 0,.selection 1,.width 0] := by
    rw [hs0]
    change nativeSelect budgetTape (7/5) (controlPenalty savedCref uniformQuoteError unitRoleUnused .complete) adverseCompleteS25Before 8 [.query 1] = _
    rw [hs1]
    change nativeSelect budgetTape (7/5) (controlPenalty savedCref uniformQuoteError unitRoleUnused .complete) adverseCompleteS25Before 7 [.query 1,.hydeRetriever 0] = _
    rw [hs2]
    change nativeSelect budgetTape (7/5) (controlPenalty savedCref uniformQuoteError unitRoleUnused .complete) adverseCompleteS25Before 6 [.query 1,.hydeRetriever 0,.selection 1] = _
    rw [hnew] <;> rfl
  have hr : repairedRollout budgetTape adverseCompleteS25Before 9 [.query 1,.hydeRetriever 0,.selection 1,.width 0] = [.query 1,.hydeRetriever 0,.selection 1,.width 0,.stop,.reranker 0,.topm 0,.context 0,.answer 0] := by decide
  simp only [nativeEvent,hs,hr]
  rfl

def adverseCompleteS26Before := adverseCompleteProposal.take 25

theorem adverseCompleteS26Choice0 : nativeFirstChoice (indexScore (7/5) (controlPenalty savedCref uniformQuoteError unitRoleUnused .complete) adverseCompleteS26Before []) adverseCompleteS26Before [] = .query 1 := by
  apply complete_root_from_physical_gap adverseCompleteS26Before (adverseComplete_prefix_rewards 25) (by decide)
  · intro q; fin_cases q <;> decide
  · exact AgentUCTNextExact.adverse_complete_hyde_root_suffix_empty 25 (by omega)
  · intro q hq
    exact AgentUCTNextExact.adverse_complete_normal_root_physical_quote_exact 25 (by omega) q hq

theorem adverseCompleteS26D1I0 : indexScore (7/5) (controlPenalty savedCref uniformQuoteError unitRoleUnused .complete) adverseCompleteS26Before [.query 1] (.hydeRetriever 1) = treeIndex ((0/1)/6) (7/5) 0 18 6 := by
  have hs : replayBackup adverseCompleteS26Before emptyStatistics ([.query 1]++[.hydeRetriever 1]) = ⟨6,(0/1)⟩ := by
    rw [replayBackup_empty_closed_form]
    simp +decide [backedEvents,adverseCompleteS26Before,adverseCompleteProposal,adverseCompleteEvent1,adverseCompleteEvent2,adverseCompleteEvent3,adverseCompleteEvent4,adverseCompleteEvent5,adverseCompleteEvent6,adverseCompleteEvent7,adverseCompleteEvent8,adverseCompleteEvent9,adverseCompleteEvent10,adverseCompleteEvent11,adverseCompleteEvent12,adverseCompleteEvent13,adverseCompleteEvent14,adverseCompleteEvent15,adverseCompleteEvent16,adverseCompleteEvent17,adverseCompleteEvent18,adverseCompleteEvent19,adverseCompleteEvent20,adverseCompleteEvent21,adverseCompleteEvent22,adverseCompleteEvent23,adverseCompleteEvent24,adverseCompleteEvent25,taskReward]
    <;> norm_num
  have hp : rawVisits adverseCompleteS26Before [.query 1] = 18 := by decide
  have hn : rawVisits adverseCompleteS26Before ([.query 1]++[.hydeRetriever 1]) = 6 := by decide
  have hz : (controlPenalty savedCref uniformQuoteError unitRoleUnused .complete) adverseCompleteS26Before [.query 1] (.hydeRetriever 1) = 0 := by
    apply control_penalty_empty_of_prior_terminal .complete savedCref uniformQuoteError adverseCompleteS26Before [.query 1] (.hydeRetriever 1) 8 (by decide)
    · decide
    · decide
  unfold indexScore
  rw [hs,hp,hn,hz]
  simp only [BackupStat.mean]
  norm_num

theorem adverseCompleteS26D1I1 : indexScore (7/5) (controlPenalty savedCref uniformQuoteError unitRoleUnused .complete) adverseCompleteS26Before [.query 1] (.hydeRetriever 0) = treeIndex ((0/1)/6) (7/5) 0 18 6 := by
  have hs : replayBackup adverseCompleteS26Before emptyStatistics ([.query 1]++[.hydeRetriever 0]) = ⟨6,(0/1)⟩ := by
    rw [replayBackup_empty_closed_form]
    simp +decide [backedEvents,adverseCompleteS26Before,adverseCompleteProposal,adverseCompleteEvent1,adverseCompleteEvent2,adverseCompleteEvent3,adverseCompleteEvent4,adverseCompleteEvent5,adverseCompleteEvent6,adverseCompleteEvent7,adverseCompleteEvent8,adverseCompleteEvent9,adverseCompleteEvent10,adverseCompleteEvent11,adverseCompleteEvent12,adverseCompleteEvent13,adverseCompleteEvent14,adverseCompleteEvent15,adverseCompleteEvent16,adverseCompleteEvent17,adverseCompleteEvent18,adverseCompleteEvent19,adverseCompleteEvent20,adverseCompleteEvent21,adverseCompleteEvent22,adverseCompleteEvent23,adverseCompleteEvent24,adverseCompleteEvent25,taskReward]
    <;> norm_num
  have hp : rawVisits adverseCompleteS26Before [.query 1] = 18 := by decide
  have hn : rawVisits adverseCompleteS26Before ([.query 1]++[.hydeRetriever 0]) = 6 := by decide
  have hz : (controlPenalty savedCref uniformQuoteError unitRoleUnused .complete) adverseCompleteS26Before [.query 1] (.hydeRetriever 0) = 0 := by
    apply control_penalty_empty_of_prior_terminal .complete savedCref uniformQuoteError adverseCompleteS26Before [.query 1] (.hydeRetriever 0) 1 (by decide)
    · decide
    · decide
  unfold indexScore
  rw [hs,hp,hn,hz]
  simp only [BackupStat.mean]
  norm_num

theorem adverseCompleteS26D1I2 : indexScore (7/5) (controlPenalty savedCref uniformQuoteError unitRoleUnused .complete) adverseCompleteS26Before [.query 1] (.hydeRetriever 2) = treeIndex ((0/1)/5) (7/5) 0 18 5 := by
  have hs : replayBackup adverseCompleteS26Before emptyStatistics ([.query 1]++[.hydeRetriever 2]) = ⟨5,(0/1)⟩ := by
    rw [replayBackup_empty_closed_form]
    simp +decide [backedEvents,adverseCompleteS26Before,adverseCompleteProposal,adverseCompleteEvent1,adverseCompleteEvent2,adverseCompleteEvent3,adverseCompleteEvent4,adverseCompleteEvent5,adverseCompleteEvent6,adverseCompleteEvent7,adverseCompleteEvent8,adverseCompleteEvent9,adverseCompleteEvent10,adverseCompleteEvent11,adverseCompleteEvent12,adverseCompleteEvent13,adverseCompleteEvent14,adverseCompleteEvent15,adverseCompleteEvent16,adverseCompleteEvent17,adverseCompleteEvent18,adverseCompleteEvent19,adverseCompleteEvent20,adverseCompleteEvent21,adverseCompleteEvent22,adverseCompleteEvent23,adverseCompleteEvent24,adverseCompleteEvent25,taskReward]
    <;> norm_num
  have hp : rawVisits adverseCompleteS26Before [.query 1] = 18 := by decide
  have hn : rawVisits adverseCompleteS26Before ([.query 1]++[.hydeRetriever 2]) = 5 := by decide
  have hz : (controlPenalty savedCref uniformQuoteError unitRoleUnused .complete) adverseCompleteS26Before [.query 1] (.hydeRetriever 2) = 0 := by
    apply control_penalty_empty_of_prior_terminal .complete savedCref uniformQuoteError adverseCompleteS26Before [.query 1] (.hydeRetriever 2) 10 (by decide)
    · decide
    · decide
  unfold indexScore
  rw [hs,hp,hn,hz]
  simp only [BackupStat.mean]
  norm_num

theorem adverseCompleteS26D1Cmp0 : indexScore (7/5) (controlPenalty savedCref uniformQuoteError unitRoleUnused .complete) adverseCompleteS26Before [.query 1] (.hydeRetriever 1) < indexScore (7/5) (controlPenalty savedCref uniformQuoteError unitRoleUnused .complete) adverseCompleteS26Before [.query 1] (.hydeRetriever 2) := by
  rw [adverseCompleteS26D1I0,adverseCompleteS26D1I2]
  have h := index_strict_order_from_intervals ((0/1)/5) ((0/1)/6) 0 0 (26858657/25000000) (49036981/50000000)
    (treeBonus (7/5) 18 5) (treeBonus (7/5) 18 6)
    (trajectory_bonus_18_5).1 (trajectory_bonus_18_6).2 (by norm_num)
  simpa only [treeIndex,sub_zero] using h

theorem adverseCompleteS26D1Cmp1 : indexScore (7/5) (controlPenalty savedCref uniformQuoteError unitRoleUnused .complete) adverseCompleteS26Before [.query 1] (.hydeRetriever 0) < indexScore (7/5) (controlPenalty savedCref uniformQuoteError unitRoleUnused .complete) adverseCompleteS26Before [.query 1] (.hydeRetriever 2) := by
  rw [adverseCompleteS26D1I1,adverseCompleteS26D1I2]
  have h := index_strict_order_from_intervals ((0/1)/5) ((0/1)/6) 0 0 (26858657/25000000) (49036981/50000000)
    (treeBonus (7/5) 18 5) (treeBonus (7/5) 18 6)
    (trajectory_bonus_18_5).1 (trajectory_bonus_18_6).2 (by norm_num)
  simpa only [treeIndex,sub_zero] using h

theorem adverseCompleteS26Choice1 : nativeFirstChoice (indexScore (7/5) (controlPenalty savedCref uniformQuoteError unitRoleUnused .complete) adverseCompleteS26Before [.query 1]) adverseCompleteS26Before [.query 1] = .hydeRetriever 2 := by
  apply visited_choice_from_ordered_certificate _ _ [.query 1] [.hydeRetriever 1,.hydeRetriever 0] [] (.hydeRetriever 2) (by decide)
  · intro a ha
    have ho : orderedLegalAvailable [.query 1] = [.hydeRetriever 1,.hydeRetriever 0,.hydeRetriever 2] := by decide
    rw [ho] at ha
    simp only [List.mem_cons,List.not_mem_nil,or_false] at ha
    rcases ha with rfl | rfl | rfl <;> decide
  · intro a ha
    simp only [List.mem_cons,List.not_mem_nil,or_false] at ha
    rcases ha with rfl | rfl
    · exact adverseCompleteS26D1Cmp0
    · exact adverseCompleteS26D1Cmp1
  · simp

theorem adverseCompleteS26D2I0 : indexScore (7/5) (controlPenalty savedCref uniformQuoteError unitRoleUnused .complete) adverseCompleteS26Before [.query 1,.hydeRetriever 2] (.selection 1) = treeIndex ((0/1)/1) (7/5) 0 5 1 := by
  have hs : replayBackup adverseCompleteS26Before emptyStatistics ([.query 1,.hydeRetriever 2]++[.selection 1]) = ⟨1,(0/1)⟩ := by
    rw [replayBackup_empty_closed_form]
    simp +decide [backedEvents,adverseCompleteS26Before,adverseCompleteProposal,adverseCompleteEvent1,adverseCompleteEvent2,adverseCompleteEvent3,adverseCompleteEvent4,adverseCompleteEvent5,adverseCompleteEvent6,adverseCompleteEvent7,adverseCompleteEvent8,adverseCompleteEvent9,adverseCompleteEvent10,adverseCompleteEvent11,adverseCompleteEvent12,adverseCompleteEvent13,adverseCompleteEvent14,adverseCompleteEvent15,adverseCompleteEvent16,adverseCompleteEvent17,adverseCompleteEvent18,adverseCompleteEvent19,adverseCompleteEvent20,adverseCompleteEvent21,adverseCompleteEvent22,adverseCompleteEvent23,adverseCompleteEvent24,adverseCompleteEvent25,taskReward]
    <;> norm_num
  have hp : rawVisits adverseCompleteS26Before [.query 1,.hydeRetriever 2] = 5 := by decide
  have hn : rawVisits adverseCompleteS26Before ([.query 1,.hydeRetriever 2]++[.selection 1]) = 1 := by decide
  have hz : (controlPenalty savedCref uniformQuoteError unitRoleUnused .complete) adverseCompleteS26Before [.query 1,.hydeRetriever 2] (.selection 1) = 0 := by
    apply control_penalty_empty_of_prior_terminal .complete savedCref uniformQuoteError adverseCompleteS26Before [.query 1,.hydeRetriever 2] (.selection 1) 16 (by decide)
    · decide
    · decide
  unfold indexScore
  rw [hs,hp,hn,hz]
  simp only [BackupStat.mean]
  norm_num

theorem adverseCompleteS26D2I1 : indexScore (7/5) (controlPenalty savedCref uniformQuoteError unitRoleUnused .complete) adverseCompleteS26Before [.query 1,.hydeRetriever 2] (.selection 2) = treeIndex ((0/1)/1) (7/5) 0 5 1 := by
  have hs : replayBackup adverseCompleteS26Before emptyStatistics ([.query 1,.hydeRetriever 2]++[.selection 2]) = ⟨1,(0/1)⟩ := by
    rw [replayBackup_empty_closed_form]
    simp +decide [backedEvents,adverseCompleteS26Before,adverseCompleteProposal,adverseCompleteEvent1,adverseCompleteEvent2,adverseCompleteEvent3,adverseCompleteEvent4,adverseCompleteEvent5,adverseCompleteEvent6,adverseCompleteEvent7,adverseCompleteEvent8,adverseCompleteEvent9,adverseCompleteEvent10,adverseCompleteEvent11,adverseCompleteEvent12,adverseCompleteEvent13,adverseCompleteEvent14,adverseCompleteEvent15,adverseCompleteEvent16,adverseCompleteEvent17,adverseCompleteEvent18,adverseCompleteEvent19,adverseCompleteEvent20,adverseCompleteEvent21,adverseCompleteEvent22,adverseCompleteEvent23,adverseCompleteEvent24,adverseCompleteEvent25,taskReward]
    <;> norm_num
  have hp : rawVisits adverseCompleteS26Before [.query 1,.hydeRetriever 2] = 5 := by decide
  have hn : rawVisits adverseCompleteS26Before ([.query 1,.hydeRetriever 2]++[.selection 2]) = 1 := by decide
  have hz : (controlPenalty savedCref uniformQuoteError unitRoleUnused .complete) adverseCompleteS26Before [.query 1,.hydeRetriever 2] (.selection 2) = 0 := by
    apply control_penalty_empty_of_prior_terminal .complete savedCref uniformQuoteError adverseCompleteS26Before [.query 1,.hydeRetriever 2] (.selection 2) 19 (by decide)
    · decide
    · decide
  unfold indexScore
  rw [hs,hp,hn,hz]
  simp only [BackupStat.mean]
  norm_num

theorem adverseCompleteS26D2I2 : indexScore (7/5) (controlPenalty savedCref uniformQuoteError unitRoleUnused .complete) adverseCompleteS26Before [.query 1,.hydeRetriever 2] (.selection 3) = treeIndex ((0/1)/1) (7/5) 0 5 1 := by
  have hs : replayBackup adverseCompleteS26Before emptyStatistics ([.query 1,.hydeRetriever 2]++[.selection 3]) = ⟨1,(0/1)⟩ := by
    rw [replayBackup_empty_closed_form]
    simp +decide [backedEvents,adverseCompleteS26Before,adverseCompleteProposal,adverseCompleteEvent1,adverseCompleteEvent2,adverseCompleteEvent3,adverseCompleteEvent4,adverseCompleteEvent5,adverseCompleteEvent6,adverseCompleteEvent7,adverseCompleteEvent8,adverseCompleteEvent9,adverseCompleteEvent10,adverseCompleteEvent11,adverseCompleteEvent12,adverseCompleteEvent13,adverseCompleteEvent14,adverseCompleteEvent15,adverseCompleteEvent16,adverseCompleteEvent17,adverseCompleteEvent18,adverseCompleteEvent19,adverseCompleteEvent20,adverseCompleteEvent21,adverseCompleteEvent22,adverseCompleteEvent23,adverseCompleteEvent24,adverseCompleteEvent25,taskReward]
    <;> norm_num
  have hp : rawVisits adverseCompleteS26Before [.query 1,.hydeRetriever 2] = 5 := by decide
  have hn : rawVisits adverseCompleteS26Before ([.query 1,.hydeRetriever 2]++[.selection 3]) = 1 := by decide
  have hz : (controlPenalty savedCref uniformQuoteError unitRoleUnused .complete) adverseCompleteS26Before [.query 1,.hydeRetriever 2] (.selection 3) = 0 := by
    apply control_penalty_empty_of_prior_terminal .complete savedCref uniformQuoteError adverseCompleteS26Before [.query 1,.hydeRetriever 2] (.selection 3) 22 (by decide)
    · decide
    · decide
  unfold indexScore
  rw [hs,hp,hn,hz]
  simp only [BackupStat.mean]
  norm_num

theorem adverseCompleteS26D2I3 : indexScore (7/5) (controlPenalty savedCref uniformQuoteError unitRoleUnused .complete) adverseCompleteS26Before [.query 1,.hydeRetriever 2] (.selection 0) = treeIndex ((0/1)/1) (7/5) 0 5 1 := by
  have hs : replayBackup adverseCompleteS26Before emptyStatistics ([.query 1,.hydeRetriever 2]++[.selection 0]) = ⟨1,(0/1)⟩ := by
    rw [replayBackup_empty_closed_form]
    simp +decide [backedEvents,adverseCompleteS26Before,adverseCompleteProposal,adverseCompleteEvent1,adverseCompleteEvent2,adverseCompleteEvent3,adverseCompleteEvent4,adverseCompleteEvent5,adverseCompleteEvent6,adverseCompleteEvent7,adverseCompleteEvent8,adverseCompleteEvent9,adverseCompleteEvent10,adverseCompleteEvent11,adverseCompleteEvent12,adverseCompleteEvent13,adverseCompleteEvent14,adverseCompleteEvent15,adverseCompleteEvent16,adverseCompleteEvent17,adverseCompleteEvent18,adverseCompleteEvent19,adverseCompleteEvent20,adverseCompleteEvent21,adverseCompleteEvent22,adverseCompleteEvent23,adverseCompleteEvent24,adverseCompleteEvent25,taskReward]
    <;> norm_num
  have hp : rawVisits adverseCompleteS26Before [.query 1,.hydeRetriever 2] = 5 := by decide
  have hn : rawVisits adverseCompleteS26Before ([.query 1,.hydeRetriever 2]++[.selection 0]) = 1 := by decide
  have hz : (controlPenalty savedCref uniformQuoteError unitRoleUnused .complete) adverseCompleteS26Before [.query 1,.hydeRetriever 2] (.selection 0) = 0 := by
    apply control_penalty_empty_of_prior_terminal .complete savedCref uniformQuoteError adverseCompleteS26Before [.query 1,.hydeRetriever 2] (.selection 0) 10 (by decide)
    · decide
    · decide
  unfold indexScore
  rw [hs,hp,hn,hz]
  simp only [BackupStat.mean]
  norm_num

theorem adverseCompleteS26D2Cmp1 : indexScore (7/5) (controlPenalty savedCref uniformQuoteError unitRoleUnused .complete) adverseCompleteS26Before [.query 1,.hydeRetriever 2] (.selection 2) ≤ indexScore (7/5) (controlPenalty savedCref uniformQuoteError unitRoleUnused .complete) adverseCompleteS26Before [.query 1,.hydeRetriever 2] (.selection 1) := by
  rw [adverseCompleteS26D2I1,adverseCompleteS26D2I0]

theorem adverseCompleteS26D2Cmp2 : indexScore (7/5) (controlPenalty savedCref uniformQuoteError unitRoleUnused .complete) adverseCompleteS26Before [.query 1,.hydeRetriever 2] (.selection 3) ≤ indexScore (7/5) (controlPenalty savedCref uniformQuoteError unitRoleUnused .complete) adverseCompleteS26Before [.query 1,.hydeRetriever 2] (.selection 1) := by
  rw [adverseCompleteS26D2I2,adverseCompleteS26D2I0]

theorem adverseCompleteS26D2Cmp3 : indexScore (7/5) (controlPenalty savedCref uniformQuoteError unitRoleUnused .complete) adverseCompleteS26Before [.query 1,.hydeRetriever 2] (.selection 0) ≤ indexScore (7/5) (controlPenalty savedCref uniformQuoteError unitRoleUnused .complete) adverseCompleteS26Before [.query 1,.hydeRetriever 2] (.selection 1) := by
  rw [adverseCompleteS26D2I3,adverseCompleteS26D2I0]

theorem adverseCompleteS26Choice2 : nativeFirstChoice (indexScore (7/5) (controlPenalty savedCref uniformQuoteError unitRoleUnused .complete) adverseCompleteS26Before [.query 1,.hydeRetriever 2]) adverseCompleteS26Before [.query 1,.hydeRetriever 2] = .selection 1 := by
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
    · exact adverseCompleteS26D2Cmp1
    · exact adverseCompleteS26D2Cmp2
    · exact adverseCompleteS26D2Cmp3

theorem adverseCompleteS26ActualEvent : nativeEvent budgetTape (7/5) (controlPenalty savedCref uniformQuoteError unitRoleUnused .complete)
    (taskReward true (2/5) (1/2)) adverseCompleteS26Before = adverseCompleteEvent26 := by
  have hs0 := native_select_existing_step budgetTape (7/5) (controlPenalty savedCref uniformQuoteError unitRoleUnused .complete) adverseCompleteS26Before 8 [] (.query 1)
    (by decide) (by decide) adverseCompleteS26Choice0
  have hs1 := native_select_existing_step budgetTape (7/5) (controlPenalty savedCref uniformQuoteError unitRoleUnused .complete) adverseCompleteS26Before 7 [.query 1] (.hydeRetriever 2)
    (by decide) (by decide) adverseCompleteS26Choice1
  have hs2 := native_select_existing_step budgetTape (7/5) (controlPenalty savedCref uniformQuoteError unitRoleUnused .complete) adverseCompleteS26Before 6 [.query 1,.hydeRetriever 2] (.selection 1)
    (by decide) (by decide) adverseCompleteS26Choice2
  have hnew := native_select_new_step budgetTape (7/5) (controlPenalty savedCref uniformQuoteError unitRoleUnused .complete) adverseCompleteS26Before 5 [.query 1,.hydeRetriever 2,.selection 1]
    [.width 3,.width 0,.width 1,.width 2] (.width 0) (by decide) (by decide) (by decide) (by decide)
  have hs : nativeSelect budgetTape (7/5) (controlPenalty savedCref uniformQuoteError unitRoleUnused .complete) adverseCompleteS26Before 9 [] = [.query 1,.hydeRetriever 2,.selection 1,.width 0] := by
    rw [hs0]
    change nativeSelect budgetTape (7/5) (controlPenalty savedCref uniformQuoteError unitRoleUnused .complete) adverseCompleteS26Before 8 [.query 1] = _
    rw [hs1]
    change nativeSelect budgetTape (7/5) (controlPenalty savedCref uniformQuoteError unitRoleUnused .complete) adverseCompleteS26Before 7 [.query 1,.hydeRetriever 2] = _
    rw [hs2]
    change nativeSelect budgetTape (7/5) (controlPenalty savedCref uniformQuoteError unitRoleUnused .complete) adverseCompleteS26Before 6 [.query 1,.hydeRetriever 2,.selection 1] = _
    rw [hnew] <;> rfl
  have hr : repairedRollout budgetTape adverseCompleteS26Before 9 [.query 1,.hydeRetriever 2,.selection 1,.width 0] = [.query 1,.hydeRetriever 2,.selection 1,.width 0,.stop,.reranker 0,.topm 0,.context 0,.answer 0] := by decide
  simp only [nativeEvent,hs,hr]
  rfl

def adverseCompleteS27Before := adverseCompleteProposal.take 26

theorem adverseCompleteS27Choice0 : nativeFirstChoice (indexScore (7/5) (controlPenalty savedCref uniformQuoteError unitRoleUnused .complete) adverseCompleteS27Before []) adverseCompleteS27Before [] = .query 1 := by
  apply complete_root_from_physical_gap adverseCompleteS27Before (adverseComplete_prefix_rewards 26) (by decide)
  · intro q; fin_cases q <;> decide
  · exact AgentUCTNextExact.adverse_complete_hyde_root_suffix_empty 26 (by omega)
  · intro q hq
    exact AgentUCTNextExact.adverse_complete_normal_root_physical_quote_exact 26 (by omega) q hq

theorem adverseCompleteS27D1I0 : indexScore (7/5) (controlPenalty savedCref uniformQuoteError unitRoleUnused .complete) adverseCompleteS27Before [.query 1] (.hydeRetriever 1) = treeIndex ((0/1)/6) (7/5) 0 19 6 := by
  have hs : replayBackup adverseCompleteS27Before emptyStatistics ([.query 1]++[.hydeRetriever 1]) = ⟨6,(0/1)⟩ := by
    rw [replayBackup_empty_closed_form]
    simp +decide [backedEvents,adverseCompleteS27Before,adverseCompleteProposal,adverseCompleteEvent1,adverseCompleteEvent2,adverseCompleteEvent3,adverseCompleteEvent4,adverseCompleteEvent5,adverseCompleteEvent6,adverseCompleteEvent7,adverseCompleteEvent8,adverseCompleteEvent9,adverseCompleteEvent10,adverseCompleteEvent11,adverseCompleteEvent12,adverseCompleteEvent13,adverseCompleteEvent14,adverseCompleteEvent15,adverseCompleteEvent16,adverseCompleteEvent17,adverseCompleteEvent18,adverseCompleteEvent19,adverseCompleteEvent20,adverseCompleteEvent21,adverseCompleteEvent22,adverseCompleteEvent23,adverseCompleteEvent24,adverseCompleteEvent25,adverseCompleteEvent26,taskReward]
    <;> norm_num
  have hp : rawVisits adverseCompleteS27Before [.query 1] = 19 := by decide
  have hn : rawVisits adverseCompleteS27Before ([.query 1]++[.hydeRetriever 1]) = 6 := by decide
  have hz : (controlPenalty savedCref uniformQuoteError unitRoleUnused .complete) adverseCompleteS27Before [.query 1] (.hydeRetriever 1) = 0 := by
    apply control_penalty_empty_of_prior_terminal .complete savedCref uniformQuoteError adverseCompleteS27Before [.query 1] (.hydeRetriever 1) 8 (by decide)
    · decide
    · decide
  unfold indexScore
  rw [hs,hp,hn,hz]
  simp only [BackupStat.mean]
  norm_num

theorem adverseCompleteS27D1I1 : indexScore (7/5) (controlPenalty savedCref uniformQuoteError unitRoleUnused .complete) adverseCompleteS27Before [.query 1] (.hydeRetriever 0) = treeIndex ((0/1)/6) (7/5) 0 19 6 := by
  have hs : replayBackup adverseCompleteS27Before emptyStatistics ([.query 1]++[.hydeRetriever 0]) = ⟨6,(0/1)⟩ := by
    rw [replayBackup_empty_closed_form]
    simp +decide [backedEvents,adverseCompleteS27Before,adverseCompleteProposal,adverseCompleteEvent1,adverseCompleteEvent2,adverseCompleteEvent3,adverseCompleteEvent4,adverseCompleteEvent5,adverseCompleteEvent6,adverseCompleteEvent7,adverseCompleteEvent8,adverseCompleteEvent9,adverseCompleteEvent10,adverseCompleteEvent11,adverseCompleteEvent12,adverseCompleteEvent13,adverseCompleteEvent14,adverseCompleteEvent15,adverseCompleteEvent16,adverseCompleteEvent17,adverseCompleteEvent18,adverseCompleteEvent19,adverseCompleteEvent20,adverseCompleteEvent21,adverseCompleteEvent22,adverseCompleteEvent23,adverseCompleteEvent24,adverseCompleteEvent25,adverseCompleteEvent26,taskReward]
    <;> norm_num
  have hp : rawVisits adverseCompleteS27Before [.query 1] = 19 := by decide
  have hn : rawVisits adverseCompleteS27Before ([.query 1]++[.hydeRetriever 0]) = 6 := by decide
  have hz : (controlPenalty savedCref uniformQuoteError unitRoleUnused .complete) adverseCompleteS27Before [.query 1] (.hydeRetriever 0) = 0 := by
    apply control_penalty_empty_of_prior_terminal .complete savedCref uniformQuoteError adverseCompleteS27Before [.query 1] (.hydeRetriever 0) 1 (by decide)
    · decide
    · decide
  unfold indexScore
  rw [hs,hp,hn,hz]
  simp only [BackupStat.mean]
  norm_num

theorem adverseCompleteS27D1I2 : indexScore (7/5) (controlPenalty savedCref uniformQuoteError unitRoleUnused .complete) adverseCompleteS27Before [.query 1] (.hydeRetriever 2) = treeIndex ((0/1)/6) (7/5) 0 19 6 := by
  have hs : replayBackup adverseCompleteS27Before emptyStatistics ([.query 1]++[.hydeRetriever 2]) = ⟨6,(0/1)⟩ := by
    rw [replayBackup_empty_closed_form]
    simp +decide [backedEvents,adverseCompleteS27Before,adverseCompleteProposal,adverseCompleteEvent1,adverseCompleteEvent2,adverseCompleteEvent3,adverseCompleteEvent4,adverseCompleteEvent5,adverseCompleteEvent6,adverseCompleteEvent7,adverseCompleteEvent8,adverseCompleteEvent9,adverseCompleteEvent10,adverseCompleteEvent11,adverseCompleteEvent12,adverseCompleteEvent13,adverseCompleteEvent14,adverseCompleteEvent15,adverseCompleteEvent16,adverseCompleteEvent17,adverseCompleteEvent18,adverseCompleteEvent19,adverseCompleteEvent20,adverseCompleteEvent21,adverseCompleteEvent22,adverseCompleteEvent23,adverseCompleteEvent24,adverseCompleteEvent25,adverseCompleteEvent26,taskReward]
    <;> norm_num
  have hp : rawVisits adverseCompleteS27Before [.query 1] = 19 := by decide
  have hn : rawVisits adverseCompleteS27Before ([.query 1]++[.hydeRetriever 2]) = 6 := by decide
  have hz : (controlPenalty savedCref uniformQuoteError unitRoleUnused .complete) adverseCompleteS27Before [.query 1] (.hydeRetriever 2) = 0 := by
    apply control_penalty_empty_of_prior_terminal .complete savedCref uniformQuoteError adverseCompleteS27Before [.query 1] (.hydeRetriever 2) 10 (by decide)
    · decide
    · decide
  unfold indexScore
  rw [hs,hp,hn,hz]
  simp only [BackupStat.mean]
  norm_num

theorem adverseCompleteS27D1Cmp1 : indexScore (7/5) (controlPenalty savedCref uniformQuoteError unitRoleUnused .complete) adverseCompleteS27Before [.query 1] (.hydeRetriever 0) ≤ indexScore (7/5) (controlPenalty savedCref uniformQuoteError unitRoleUnused .complete) adverseCompleteS27Before [.query 1] (.hydeRetriever 1) := by
  rw [adverseCompleteS27D1I1,adverseCompleteS27D1I0]

theorem adverseCompleteS27D1Cmp2 : indexScore (7/5) (controlPenalty savedCref uniformQuoteError unitRoleUnused .complete) adverseCompleteS27Before [.query 1] (.hydeRetriever 2) ≤ indexScore (7/5) (controlPenalty savedCref uniformQuoteError unitRoleUnused .complete) adverseCompleteS27Before [.query 1] (.hydeRetriever 1) := by
  rw [adverseCompleteS27D1I2,adverseCompleteS27D1I0]

theorem adverseCompleteS27Choice1 : nativeFirstChoice (indexScore (7/5) (controlPenalty savedCref uniformQuoteError unitRoleUnused .complete) adverseCompleteS27Before [.query 1]) adverseCompleteS27Before [.query 1] = .hydeRetriever 1 := by
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
    · exact adverseCompleteS27D1Cmp1
    · exact adverseCompleteS27D1Cmp2

theorem adverseCompleteS27D2I0 : indexScore (7/5) (controlPenalty savedCref uniformQuoteError unitRoleUnused .complete) adverseCompleteS27Before [.query 1,.hydeRetriever 1] (.selection 1) = treeIndex ((0/1)/2) (7/5) 0 6 2 := by
  have hs : replayBackup adverseCompleteS27Before emptyStatistics ([.query 1,.hydeRetriever 1]++[.selection 1]) = ⟨2,(0/1)⟩ := by
    rw [replayBackup_empty_closed_form]
    simp +decide [backedEvents,adverseCompleteS27Before,adverseCompleteProposal,adverseCompleteEvent1,adverseCompleteEvent2,adverseCompleteEvent3,adverseCompleteEvent4,adverseCompleteEvent5,adverseCompleteEvent6,adverseCompleteEvent7,adverseCompleteEvent8,adverseCompleteEvent9,adverseCompleteEvent10,adverseCompleteEvent11,adverseCompleteEvent12,adverseCompleteEvent13,adverseCompleteEvent14,adverseCompleteEvent15,adverseCompleteEvent16,adverseCompleteEvent17,adverseCompleteEvent18,adverseCompleteEvent19,adverseCompleteEvent20,adverseCompleteEvent21,adverseCompleteEvent22,adverseCompleteEvent23,adverseCompleteEvent24,adverseCompleteEvent25,adverseCompleteEvent26,taskReward]
    <;> norm_num
  have hp : rawVisits adverseCompleteS27Before [.query 1,.hydeRetriever 1] = 6 := by decide
  have hn : rawVisits adverseCompleteS27Before ([.query 1,.hydeRetriever 1]++[.selection 1]) = 2 := by decide
  have hz : (controlPenalty savedCref uniformQuoteError unitRoleUnused .complete) adverseCompleteS27Before [.query 1,.hydeRetriever 1] (.selection 1) = 0 := by
    apply control_penalty_empty_of_prior_terminal .complete savedCref uniformQuoteError adverseCompleteS27Before [.query 1,.hydeRetriever 1] (.selection 1) 14 (by decide)
    · decide
    · decide
  unfold indexScore
  rw [hs,hp,hn,hz]
  simp only [BackupStat.mean]
  norm_num

theorem adverseCompleteS27D2I1 : indexScore (7/5) (controlPenalty savedCref uniformQuoteError unitRoleUnused .complete) adverseCompleteS27Before [.query 1,.hydeRetriever 1] (.selection 2) = treeIndex ((0/1)/1) (7/5) 0 6 1 := by
  have hs : replayBackup adverseCompleteS27Before emptyStatistics ([.query 1,.hydeRetriever 1]++[.selection 2]) = ⟨1,(0/1)⟩ := by
    rw [replayBackup_empty_closed_form]
    simp +decide [backedEvents,adverseCompleteS27Before,adverseCompleteProposal,adverseCompleteEvent1,adverseCompleteEvent2,adverseCompleteEvent3,adverseCompleteEvent4,adverseCompleteEvent5,adverseCompleteEvent6,adverseCompleteEvent7,adverseCompleteEvent8,adverseCompleteEvent9,adverseCompleteEvent10,adverseCompleteEvent11,adverseCompleteEvent12,adverseCompleteEvent13,adverseCompleteEvent14,adverseCompleteEvent15,adverseCompleteEvent16,adverseCompleteEvent17,adverseCompleteEvent18,adverseCompleteEvent19,adverseCompleteEvent20,adverseCompleteEvent21,adverseCompleteEvent22,adverseCompleteEvent23,adverseCompleteEvent24,adverseCompleteEvent25,adverseCompleteEvent26,taskReward]
    <;> norm_num
  have hp : rawVisits adverseCompleteS27Before [.query 1,.hydeRetriever 1] = 6 := by decide
  have hn : rawVisits adverseCompleteS27Before ([.query 1,.hydeRetriever 1]++[.selection 2]) = 1 := by decide
  have hz : (controlPenalty savedCref uniformQuoteError unitRoleUnused .complete) adverseCompleteS27Before [.query 1,.hydeRetriever 1] (.selection 2) = 0 := by
    apply control_penalty_empty_of_prior_terminal .complete savedCref uniformQuoteError adverseCompleteS27Before [.query 1,.hydeRetriever 1] (.selection 2) 17 (by decide)
    · decide
    · decide
  unfold indexScore
  rw [hs,hp,hn,hz]
  simp only [BackupStat.mean]
  norm_num

theorem adverseCompleteS27D2I2 : indexScore (7/5) (controlPenalty savedCref uniformQuoteError unitRoleUnused .complete) adverseCompleteS27Before [.query 1,.hydeRetriever 1] (.selection 3) = treeIndex ((0/1)/1) (7/5) 0 6 1 := by
  have hs : replayBackup adverseCompleteS27Before emptyStatistics ([.query 1,.hydeRetriever 1]++[.selection 3]) = ⟨1,(0/1)⟩ := by
    rw [replayBackup_empty_closed_form]
    simp +decide [backedEvents,adverseCompleteS27Before,adverseCompleteProposal,adverseCompleteEvent1,adverseCompleteEvent2,adverseCompleteEvent3,adverseCompleteEvent4,adverseCompleteEvent5,adverseCompleteEvent6,adverseCompleteEvent7,adverseCompleteEvent8,adverseCompleteEvent9,adverseCompleteEvent10,adverseCompleteEvent11,adverseCompleteEvent12,adverseCompleteEvent13,adverseCompleteEvent14,adverseCompleteEvent15,adverseCompleteEvent16,adverseCompleteEvent17,adverseCompleteEvent18,adverseCompleteEvent19,adverseCompleteEvent20,adverseCompleteEvent21,adverseCompleteEvent22,adverseCompleteEvent23,adverseCompleteEvent24,adverseCompleteEvent25,adverseCompleteEvent26,taskReward]
    <;> norm_num
  have hp : rawVisits adverseCompleteS27Before [.query 1,.hydeRetriever 1] = 6 := by decide
  have hn : rawVisits adverseCompleteS27Before ([.query 1,.hydeRetriever 1]++[.selection 3]) = 1 := by decide
  have hz : (controlPenalty savedCref uniformQuoteError unitRoleUnused .complete) adverseCompleteS27Before [.query 1,.hydeRetriever 1] (.selection 3) = 0 := by
    apply control_penalty_empty_of_prior_terminal .complete savedCref uniformQuoteError adverseCompleteS27Before [.query 1,.hydeRetriever 1] (.selection 3) 20 (by decide)
    · decide
    · decide
  unfold indexScore
  rw [hs,hp,hn,hz]
  simp only [BackupStat.mean]
  norm_num

theorem adverseCompleteS27D2I3 : indexScore (7/5) (controlPenalty savedCref uniformQuoteError unitRoleUnused .complete) adverseCompleteS27Before [.query 1,.hydeRetriever 1] (.selection 0) = treeIndex ((0/1)/1) (7/5) 0 6 1 := by
  have hs : replayBackup adverseCompleteS27Before emptyStatistics ([.query 1,.hydeRetriever 1]++[.selection 0]) = ⟨1,(0/1)⟩ := by
    rw [replayBackup_empty_closed_form]
    simp +decide [backedEvents,adverseCompleteS27Before,adverseCompleteProposal,adverseCompleteEvent1,adverseCompleteEvent2,adverseCompleteEvent3,adverseCompleteEvent4,adverseCompleteEvent5,adverseCompleteEvent6,adverseCompleteEvent7,adverseCompleteEvent8,adverseCompleteEvent9,adverseCompleteEvent10,adverseCompleteEvent11,adverseCompleteEvent12,adverseCompleteEvent13,adverseCompleteEvent14,adverseCompleteEvent15,adverseCompleteEvent16,adverseCompleteEvent17,adverseCompleteEvent18,adverseCompleteEvent19,adverseCompleteEvent20,adverseCompleteEvent21,adverseCompleteEvent22,adverseCompleteEvent23,adverseCompleteEvent24,adverseCompleteEvent25,adverseCompleteEvent26,taskReward]
    <;> norm_num
  have hp : rawVisits adverseCompleteS27Before [.query 1,.hydeRetriever 1] = 6 := by decide
  have hn : rawVisits adverseCompleteS27Before ([.query 1,.hydeRetriever 1]++[.selection 0]) = 1 := by decide
  have hz : (controlPenalty savedCref uniformQuoteError unitRoleUnused .complete) adverseCompleteS27Before [.query 1,.hydeRetriever 1] (.selection 0) = 0 := by
    apply control_penalty_empty_of_prior_terminal .complete savedCref uniformQuoteError adverseCompleteS27Before [.query 1,.hydeRetriever 1] (.selection 0) 8 (by decide)
    · decide
    · decide
  unfold indexScore
  rw [hs,hp,hn,hz]
  simp only [BackupStat.mean]
  norm_num

theorem adverseCompleteS27D2Cmp0 : indexScore (7/5) (controlPenalty savedCref uniformQuoteError unitRoleUnused .complete) adverseCompleteS27Before [.query 1,.hydeRetriever 1] (.selection 1) < indexScore (7/5) (controlPenalty savedCref uniformQuoteError unitRoleUnused .complete) adverseCompleteS27Before [.query 1,.hydeRetriever 1] (.selection 2) := by
  rw [adverseCompleteS27D2I0,adverseCompleteS27D2I1]
  have h := index_strict_order_from_intervals ((0/1)/1) ((0/1)/2) 0 0 (24411779/12500000) (69046943/50000000)
    (treeBonus (7/5) 6 1) (treeBonus (7/5) 6 2)
    (trajectory_bonus_6_1).1 (trajectory_bonus_6_2).2 (by norm_num)
  simpa only [treeIndex,sub_zero] using h

theorem adverseCompleteS27D2Cmp2 : indexScore (7/5) (controlPenalty savedCref uniformQuoteError unitRoleUnused .complete) adverseCompleteS27Before [.query 1,.hydeRetriever 1] (.selection 3) ≤ indexScore (7/5) (controlPenalty savedCref uniformQuoteError unitRoleUnused .complete) adverseCompleteS27Before [.query 1,.hydeRetriever 1] (.selection 2) := by
  rw [adverseCompleteS27D2I2,adverseCompleteS27D2I1]

theorem adverseCompleteS27D2Cmp3 : indexScore (7/5) (controlPenalty savedCref uniformQuoteError unitRoleUnused .complete) adverseCompleteS27Before [.query 1,.hydeRetriever 1] (.selection 0) ≤ indexScore (7/5) (controlPenalty savedCref uniformQuoteError unitRoleUnused .complete) adverseCompleteS27Before [.query 1,.hydeRetriever 1] (.selection 2) := by
  rw [adverseCompleteS27D2I3,adverseCompleteS27D2I1]

theorem adverseCompleteS27Choice2 : nativeFirstChoice (indexScore (7/5) (controlPenalty savedCref uniformQuoteError unitRoleUnused .complete) adverseCompleteS27Before [.query 1,.hydeRetriever 1]) adverseCompleteS27Before [.query 1,.hydeRetriever 1] = .selection 2 := by
  apply visited_choice_from_ordered_certificate _ _ [.query 1,.hydeRetriever 1] [.selection 1] [.selection 3,.selection 0] (.selection 2) (by decide)
  · intro a ha
    have ho : orderedLegalAvailable [.query 1,.hydeRetriever 1] = [.selection 1,.selection 2,.selection 3,.selection 0] := by decide
    rw [ho] at ha
    simp only [List.mem_cons,List.not_mem_nil,or_false] at ha
    rcases ha with rfl | rfl | rfl | rfl <;> decide
  · intro a ha
    simp only [List.mem_cons,List.not_mem_nil,or_false] at ha
    rcases ha with rfl
    · exact adverseCompleteS27D2Cmp0
  · intro a ha
    simp only [List.mem_cons,List.not_mem_nil,or_false] at ha
    rcases ha with rfl | rfl
    · exact adverseCompleteS27D2Cmp2
    · exact adverseCompleteS27D2Cmp3

theorem adverseCompleteS27ActualEvent : nativeEvent budgetTape (7/5) (controlPenalty savedCref uniformQuoteError unitRoleUnused .complete)
    (taskReward true (2/5) (1/2)) adverseCompleteS27Before = adverseCompleteEvent27 := by
  have hs0 := native_select_existing_step budgetTape (7/5) (controlPenalty savedCref uniformQuoteError unitRoleUnused .complete) adverseCompleteS27Before 8 [] (.query 1)
    (by decide) (by decide) adverseCompleteS27Choice0
  have hs1 := native_select_existing_step budgetTape (7/5) (controlPenalty savedCref uniformQuoteError unitRoleUnused .complete) adverseCompleteS27Before 7 [.query 1] (.hydeRetriever 1)
    (by decide) (by decide) adverseCompleteS27Choice1
  have hs2 := native_select_existing_step budgetTape (7/5) (controlPenalty savedCref uniformQuoteError unitRoleUnused .complete) adverseCompleteS27Before 6 [.query 1,.hydeRetriever 1] (.selection 2)
    (by decide) (by decide) adverseCompleteS27Choice2
  have hnew := native_select_new_step budgetTape (7/5) (controlPenalty savedCref uniformQuoteError unitRoleUnused .complete) adverseCompleteS27Before 5 [.query 1,.hydeRetriever 1,.selection 2]
    [.width 3,.width 0,.width 1,.width 2] (.width 0) (by decide) (by decide) (by decide) (by decide)
  have hs : nativeSelect budgetTape (7/5) (controlPenalty savedCref uniformQuoteError unitRoleUnused .complete) adverseCompleteS27Before 9 [] = [.query 1,.hydeRetriever 1,.selection 2,.width 0] := by
    rw [hs0]
    change nativeSelect budgetTape (7/5) (controlPenalty savedCref uniformQuoteError unitRoleUnused .complete) adverseCompleteS27Before 8 [.query 1] = _
    rw [hs1]
    change nativeSelect budgetTape (7/5) (controlPenalty savedCref uniformQuoteError unitRoleUnused .complete) adverseCompleteS27Before 7 [.query 1,.hydeRetriever 1] = _
    rw [hs2]
    change nativeSelect budgetTape (7/5) (controlPenalty savedCref uniformQuoteError unitRoleUnused .complete) adverseCompleteS27Before 6 [.query 1,.hydeRetriever 1,.selection 2] = _
    rw [hnew] <;> rfl
  have hr : repairedRollout budgetTape adverseCompleteS27Before 9 [.query 1,.hydeRetriever 1,.selection 2,.width 0] = [.query 1,.hydeRetriever 1,.selection 2,.width 0,.stop,.reranker 0,.topm 0,.context 0,.answer 0] := by decide
  simp only [nativeEvent,hs,hr]
  rfl

end AgentUCT32MConcrete
