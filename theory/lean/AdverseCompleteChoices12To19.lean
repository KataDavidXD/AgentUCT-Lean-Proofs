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

def adverseCompleteS12Before := adverseCompleteProposal.take 11

theorem adverseCompleteS12Choice0 : nativeFirstChoice (indexScore (7/5) (controlPenalty savedCref uniformQuoteError unitRoleUnused .complete) adverseCompleteS12Before []) adverseCompleteS12Before [] = .query 1 := by
  apply complete_root_from_physical_gap adverseCompleteS12Before (adverseComplete_prefix_rewards 11) (by decide)
  · intro q; fin_cases q <;> decide
  · exact AgentUCTNextExact.adverse_complete_hyde_root_suffix_empty 11 (by omega)
  · intro q hq
    exact AgentUCTNextExact.adverse_complete_normal_root_physical_quote_exact 11 (by omega) q hq

theorem adverseCompleteS12D1I0 : indexScore (7/5) (controlPenalty savedCref uniformQuoteError unitRoleUnused .complete) adverseCompleteS12Before [.query 1] (.hydeRetriever 1) = treeIndex ((0/1)/1) (7/5) 0 4 1 := by
  have hs : replayBackup adverseCompleteS12Before emptyStatistics ([.query 1]++[.hydeRetriever 1]) = ⟨1,(0/1)⟩ := by
    rw [replayBackup_empty_closed_form]
    simp +decide [backedEvents,adverseCompleteS12Before,adverseCompleteProposal,adverseCompleteEvent1,adverseCompleteEvent2,adverseCompleteEvent3,adverseCompleteEvent4,adverseCompleteEvent5,adverseCompleteEvent6,adverseCompleteEvent7,adverseCompleteEvent8,adverseCompleteEvent9,adverseCompleteEvent10,adverseCompleteEvent11,taskReward]
    <;> norm_num
  have hp : rawVisits adverseCompleteS12Before [.query 1] = 4 := by decide
  have hn : rawVisits adverseCompleteS12Before ([.query 1]++[.hydeRetriever 1]) = 1 := by decide
  have hz : (controlPenalty savedCref uniformQuoteError unitRoleUnused .complete) adverseCompleteS12Before [.query 1] (.hydeRetriever 1) = 0 := by
    apply control_penalty_empty_of_prior_terminal .complete savedCref uniformQuoteError adverseCompleteS12Before [.query 1] (.hydeRetriever 1) 8 (by decide)
    · decide
    · decide
  unfold indexScore
  rw [hs,hp,hn,hz]
  simp only [BackupStat.mean]
  norm_num

theorem adverseCompleteS12D1I1 : indexScore (7/5) (controlPenalty savedCref uniformQuoteError unitRoleUnused .complete) adverseCompleteS12Before [.query 1] (.hydeRetriever 0) = treeIndex ((0/1)/1) (7/5) 0 4 1 := by
  have hs : replayBackup adverseCompleteS12Before emptyStatistics ([.query 1]++[.hydeRetriever 0]) = ⟨1,(0/1)⟩ := by
    rw [replayBackup_empty_closed_form]
    simp +decide [backedEvents,adverseCompleteS12Before,adverseCompleteProposal,adverseCompleteEvent1,adverseCompleteEvent2,adverseCompleteEvent3,adverseCompleteEvent4,adverseCompleteEvent5,adverseCompleteEvent6,adverseCompleteEvent7,adverseCompleteEvent8,adverseCompleteEvent9,adverseCompleteEvent10,adverseCompleteEvent11,taskReward]
    <;> norm_num
  have hp : rawVisits adverseCompleteS12Before [.query 1] = 4 := by decide
  have hn : rawVisits adverseCompleteS12Before ([.query 1]++[.hydeRetriever 0]) = 1 := by decide
  have hz : (controlPenalty savedCref uniformQuoteError unitRoleUnused .complete) adverseCompleteS12Before [.query 1] (.hydeRetriever 0) = 0 := by
    apply control_penalty_empty_of_prior_terminal .complete savedCref uniformQuoteError adverseCompleteS12Before [.query 1] (.hydeRetriever 0) 1 (by decide)
    · decide
    · decide
  unfold indexScore
  rw [hs,hp,hn,hz]
  simp only [BackupStat.mean]
  norm_num

theorem adverseCompleteS12D1I2 : indexScore (7/5) (controlPenalty savedCref uniformQuoteError unitRoleUnused .complete) adverseCompleteS12Before [.query 1] (.hydeRetriever 2) = treeIndex ((0/1)/1) (7/5) 0 4 1 := by
  have hs : replayBackup adverseCompleteS12Before emptyStatistics ([.query 1]++[.hydeRetriever 2]) = ⟨1,(0/1)⟩ := by
    rw [replayBackup_empty_closed_form]
    simp +decide [backedEvents,adverseCompleteS12Before,adverseCompleteProposal,adverseCompleteEvent1,adverseCompleteEvent2,adverseCompleteEvent3,adverseCompleteEvent4,adverseCompleteEvent5,adverseCompleteEvent6,adverseCompleteEvent7,adverseCompleteEvent8,adverseCompleteEvent9,adverseCompleteEvent10,adverseCompleteEvent11,taskReward]
    <;> norm_num
  have hp : rawVisits adverseCompleteS12Before [.query 1] = 4 := by decide
  have hn : rawVisits adverseCompleteS12Before ([.query 1]++[.hydeRetriever 2]) = 1 := by decide
  have hz : (controlPenalty savedCref uniformQuoteError unitRoleUnused .complete) adverseCompleteS12Before [.query 1] (.hydeRetriever 2) = 0 := by
    apply control_penalty_empty_of_prior_terminal .complete savedCref uniformQuoteError adverseCompleteS12Before [.query 1] (.hydeRetriever 2) 10 (by decide)
    · decide
    · decide
  unfold indexScore
  rw [hs,hp,hn,hz]
  simp only [BackupStat.mean]
  norm_num

theorem adverseCompleteS12D1Cmp1 : indexScore (7/5) (controlPenalty savedCref uniformQuoteError unitRoleUnused .complete) adverseCompleteS12Before [.query 1] (.hydeRetriever 0) ≤ indexScore (7/5) (controlPenalty savedCref uniformQuoteError unitRoleUnused .complete) adverseCompleteS12Before [.query 1] (.hydeRetriever 1) := by
  rw [adverseCompleteS12D1I1,adverseCompleteS12D1I0]

theorem adverseCompleteS12D1Cmp2 : indexScore (7/5) (controlPenalty savedCref uniformQuoteError unitRoleUnused .complete) adverseCompleteS12Before [.query 1] (.hydeRetriever 2) ≤ indexScore (7/5) (controlPenalty savedCref uniformQuoteError unitRoleUnused .complete) adverseCompleteS12Before [.query 1] (.hydeRetriever 1) := by
  rw [adverseCompleteS12D1I2,adverseCompleteS12D1I0]

theorem adverseCompleteS12Choice1 : nativeFirstChoice (indexScore (7/5) (controlPenalty savedCref uniformQuoteError unitRoleUnused .complete) adverseCompleteS12Before [.query 1]) adverseCompleteS12Before [.query 1] = .hydeRetriever 1 := by
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
    · exact adverseCompleteS12D1Cmp1
    · exact adverseCompleteS12D1Cmp2

theorem adverseCompleteS12ActualEvent : nativeEvent budgetTape (7/5) (controlPenalty savedCref uniformQuoteError unitRoleUnused .complete)
    (taskReward true (2/5) (1/2)) adverseCompleteS12Before = adverseCompleteEvent12 := by
  have hs0 := native_select_existing_step budgetTape (7/5) (controlPenalty savedCref uniformQuoteError unitRoleUnused .complete) adverseCompleteS12Before 8 [] (.query 1)
    (by decide) (by decide) adverseCompleteS12Choice0
  have hs1 := native_select_existing_step budgetTape (7/5) (controlPenalty savedCref uniformQuoteError unitRoleUnused .complete) adverseCompleteS12Before 7 [.query 1] (.hydeRetriever 1)
    (by decide) (by decide) adverseCompleteS12Choice1
  have hnew := native_select_new_step budgetTape (7/5) (controlPenalty savedCref uniformQuoteError unitRoleUnused .complete) adverseCompleteS12Before 6 [.query 1,.hydeRetriever 1]
    [.selection 1,.selection 2,.selection 3,.selection 0] (.selection 0) (by decide) (by decide) (by decide) (by decide)
  have hs : nativeSelect budgetTape (7/5) (controlPenalty savedCref uniformQuoteError unitRoleUnused .complete) adverseCompleteS12Before 9 [] = [.query 1,.hydeRetriever 1,.selection 0] := by
    rw [hs0]
    change nativeSelect budgetTape (7/5) (controlPenalty savedCref uniformQuoteError unitRoleUnused .complete) adverseCompleteS12Before 8 [.query 1] = _
    rw [hs1]
    change nativeSelect budgetTape (7/5) (controlPenalty savedCref uniformQuoteError unitRoleUnused .complete) adverseCompleteS12Before 7 [.query 1,.hydeRetriever 1] = _
    rw [hnew] <;> rfl
  have hr : repairedRollout budgetTape adverseCompleteS12Before 9 [.query 1,.hydeRetriever 1,.selection 0] = [.query 1,.hydeRetriever 1,.selection 0,.width 1,.stop,.reranker 0,.topm 0,.context 0,.answer 0] := by decide
  simp only [nativeEvent,hs,hr]
  rfl

def adverseCompleteS13Before := adverseCompleteProposal.take 12

theorem adverseCompleteS13Choice0 : nativeFirstChoice (indexScore (7/5) (controlPenalty savedCref uniformQuoteError unitRoleUnused .complete) adverseCompleteS13Before []) adverseCompleteS13Before [] = .query 1 := by
  apply complete_root_from_physical_gap adverseCompleteS13Before (adverseComplete_prefix_rewards 12) (by decide)
  · intro q; fin_cases q <;> decide
  · exact AgentUCTNextExact.adverse_complete_hyde_root_suffix_empty 12 (by omega)
  · intro q hq
    exact AgentUCTNextExact.adverse_complete_normal_root_physical_quote_exact 12 (by omega) q hq

theorem adverseCompleteS13D1I0 : indexScore (7/5) (controlPenalty savedCref uniformQuoteError unitRoleUnused .complete) adverseCompleteS13Before [.query 1] (.hydeRetriever 1) = treeIndex ((0/1)/2) (7/5) 0 5 2 := by
  have hs : replayBackup adverseCompleteS13Before emptyStatistics ([.query 1]++[.hydeRetriever 1]) = ⟨2,(0/1)⟩ := by
    rw [replayBackup_empty_closed_form]
    simp +decide [backedEvents,adverseCompleteS13Before,adverseCompleteProposal,adverseCompleteEvent1,adverseCompleteEvent2,adverseCompleteEvent3,adverseCompleteEvent4,adverseCompleteEvent5,adverseCompleteEvent6,adverseCompleteEvent7,adverseCompleteEvent8,adverseCompleteEvent9,adverseCompleteEvent10,adverseCompleteEvent11,adverseCompleteEvent12,taskReward]
    <;> norm_num
  have hp : rawVisits adverseCompleteS13Before [.query 1] = 5 := by decide
  have hn : rawVisits adverseCompleteS13Before ([.query 1]++[.hydeRetriever 1]) = 2 := by decide
  have hz : (controlPenalty savedCref uniformQuoteError unitRoleUnused .complete) adverseCompleteS13Before [.query 1] (.hydeRetriever 1) = 0 := by
    apply control_penalty_empty_of_prior_terminal .complete savedCref uniformQuoteError adverseCompleteS13Before [.query 1] (.hydeRetriever 1) 8 (by decide)
    · decide
    · decide
  unfold indexScore
  rw [hs,hp,hn,hz]
  simp only [BackupStat.mean]
  norm_num

theorem adverseCompleteS13D1I1 : indexScore (7/5) (controlPenalty savedCref uniformQuoteError unitRoleUnused .complete) adverseCompleteS13Before [.query 1] (.hydeRetriever 0) = treeIndex ((0/1)/1) (7/5) 0 5 1 := by
  have hs : replayBackup adverseCompleteS13Before emptyStatistics ([.query 1]++[.hydeRetriever 0]) = ⟨1,(0/1)⟩ := by
    rw [replayBackup_empty_closed_form]
    simp +decide [backedEvents,adverseCompleteS13Before,adverseCompleteProposal,adverseCompleteEvent1,adverseCompleteEvent2,adverseCompleteEvent3,adverseCompleteEvent4,adverseCompleteEvent5,adverseCompleteEvent6,adverseCompleteEvent7,adverseCompleteEvent8,adverseCompleteEvent9,adverseCompleteEvent10,adverseCompleteEvent11,adverseCompleteEvent12,taskReward]
    <;> norm_num
  have hp : rawVisits adverseCompleteS13Before [.query 1] = 5 := by decide
  have hn : rawVisits adverseCompleteS13Before ([.query 1]++[.hydeRetriever 0]) = 1 := by decide
  have hz : (controlPenalty savedCref uniformQuoteError unitRoleUnused .complete) adverseCompleteS13Before [.query 1] (.hydeRetriever 0) = 0 := by
    apply control_penalty_empty_of_prior_terminal .complete savedCref uniformQuoteError adverseCompleteS13Before [.query 1] (.hydeRetriever 0) 1 (by decide)
    · decide
    · decide
  unfold indexScore
  rw [hs,hp,hn,hz]
  simp only [BackupStat.mean]
  norm_num

theorem adverseCompleteS13D1I2 : indexScore (7/5) (controlPenalty savedCref uniformQuoteError unitRoleUnused .complete) adverseCompleteS13Before [.query 1] (.hydeRetriever 2) = treeIndex ((0/1)/1) (7/5) 0 5 1 := by
  have hs : replayBackup adverseCompleteS13Before emptyStatistics ([.query 1]++[.hydeRetriever 2]) = ⟨1,(0/1)⟩ := by
    rw [replayBackup_empty_closed_form]
    simp +decide [backedEvents,adverseCompleteS13Before,adverseCompleteProposal,adverseCompleteEvent1,adverseCompleteEvent2,adverseCompleteEvent3,adverseCompleteEvent4,adverseCompleteEvent5,adverseCompleteEvent6,adverseCompleteEvent7,adverseCompleteEvent8,adverseCompleteEvent9,adverseCompleteEvent10,adverseCompleteEvent11,adverseCompleteEvent12,taskReward]
    <;> norm_num
  have hp : rawVisits adverseCompleteS13Before [.query 1] = 5 := by decide
  have hn : rawVisits adverseCompleteS13Before ([.query 1]++[.hydeRetriever 2]) = 1 := by decide
  have hz : (controlPenalty savedCref uniformQuoteError unitRoleUnused .complete) adverseCompleteS13Before [.query 1] (.hydeRetriever 2) = 0 := by
    apply control_penalty_empty_of_prior_terminal .complete savedCref uniformQuoteError adverseCompleteS13Before [.query 1] (.hydeRetriever 2) 10 (by decide)
    · decide
    · decide
  unfold indexScore
  rw [hs,hp,hn,hz]
  simp only [BackupStat.mean]
  norm_num

theorem adverseCompleteS13D1Cmp0 : indexScore (7/5) (controlPenalty savedCref uniformQuoteError unitRoleUnused .complete) adverseCompleteS13Before [.query 1] (.hydeRetriever 1) < indexScore (7/5) (controlPenalty savedCref uniformQuoteError unitRoleUnused .complete) adverseCompleteS13Before [.query 1] (.hydeRetriever 0) := by
  rw [adverseCompleteS13D1I0,adverseCompleteS13D1I1]
  have h := index_strict_order_from_intervals ((0/1)/1) ((0/1)/2) 0 0 (93699627/50000000) (66255651/50000000)
    (treeBonus (7/5) 5 1) (treeBonus (7/5) 5 2)
    (trajectory_bonus_5_1).1 (trajectory_bonus_5_2).2 (by norm_num)
  simpa only [treeIndex,sub_zero] using h

theorem adverseCompleteS13D1Cmp2 : indexScore (7/5) (controlPenalty savedCref uniformQuoteError unitRoleUnused .complete) adverseCompleteS13Before [.query 1] (.hydeRetriever 2) ≤ indexScore (7/5) (controlPenalty savedCref uniformQuoteError unitRoleUnused .complete) adverseCompleteS13Before [.query 1] (.hydeRetriever 0) := by
  rw [adverseCompleteS13D1I2,adverseCompleteS13D1I1]

theorem adverseCompleteS13Choice1 : nativeFirstChoice (indexScore (7/5) (controlPenalty savedCref uniformQuoteError unitRoleUnused .complete) adverseCompleteS13Before [.query 1]) adverseCompleteS13Before [.query 1] = .hydeRetriever 0 := by
  apply visited_choice_from_ordered_certificate _ _ [.query 1] [.hydeRetriever 1] [.hydeRetriever 2] (.hydeRetriever 0) (by decide)
  · intro a ha
    have ho : orderedLegalAvailable [.query 1] = [.hydeRetriever 1,.hydeRetriever 0,.hydeRetriever 2] := by decide
    rw [ho] at ha
    simp only [List.mem_cons,List.not_mem_nil,or_false] at ha
    rcases ha with rfl | rfl | rfl <;> decide
  · intro a ha
    simp only [List.mem_cons,List.not_mem_nil,or_false] at ha
    rcases ha with rfl
    · exact adverseCompleteS13D1Cmp0
  · intro a ha
    simp only [List.mem_cons,List.not_mem_nil,or_false] at ha
    rcases ha with rfl
    · exact adverseCompleteS13D1Cmp2

theorem adverseCompleteS13ActualEvent : nativeEvent budgetTape (7/5) (controlPenalty savedCref uniformQuoteError unitRoleUnused .complete)
    (taskReward true (2/5) (1/2)) adverseCompleteS13Before = adverseCompleteEvent13 := by
  have hs0 := native_select_existing_step budgetTape (7/5) (controlPenalty savedCref uniformQuoteError unitRoleUnused .complete) adverseCompleteS13Before 8 [] (.query 1)
    (by decide) (by decide) adverseCompleteS13Choice0
  have hs1 := native_select_existing_step budgetTape (7/5) (controlPenalty savedCref uniformQuoteError unitRoleUnused .complete) adverseCompleteS13Before 7 [.query 1] (.hydeRetriever 0)
    (by decide) (by decide) adverseCompleteS13Choice1
  have hnew := native_select_new_step budgetTape (7/5) (controlPenalty savedCref uniformQuoteError unitRoleUnused .complete) adverseCompleteS13Before 6 [.query 1,.hydeRetriever 0]
    [.selection 1,.selection 2,.selection 3,.selection 0] (.selection 0) (by decide) (by decide) (by decide) (by decide)
  have hs : nativeSelect budgetTape (7/5) (controlPenalty savedCref uniformQuoteError unitRoleUnused .complete) adverseCompleteS13Before 9 [] = [.query 1,.hydeRetriever 0,.selection 0] := by
    rw [hs0]
    change nativeSelect budgetTape (7/5) (controlPenalty savedCref uniformQuoteError unitRoleUnused .complete) adverseCompleteS13Before 8 [.query 1] = _
    rw [hs1]
    change nativeSelect budgetTape (7/5) (controlPenalty savedCref uniformQuoteError unitRoleUnused .complete) adverseCompleteS13Before 7 [.query 1,.hydeRetriever 0] = _
    rw [hnew] <;> rfl
  have hr : repairedRollout budgetTape adverseCompleteS13Before 9 [.query 1,.hydeRetriever 0,.selection 0] = [.query 1,.hydeRetriever 0,.selection 0,.width 0,.stop,.reranker 0,.topm 0,.context 0,.answer 0] := by decide
  simp only [nativeEvent,hs,hr]
  rfl

def adverseCompleteS14Before := adverseCompleteProposal.take 13

theorem adverseCompleteS14Choice0 : nativeFirstChoice (indexScore (7/5) (controlPenalty savedCref uniformQuoteError unitRoleUnused .complete) adverseCompleteS14Before []) adverseCompleteS14Before [] = .query 1 := by
  apply complete_root_from_physical_gap adverseCompleteS14Before (adverseComplete_prefix_rewards 13) (by decide)
  · intro q; fin_cases q <;> decide
  · exact AgentUCTNextExact.adverse_complete_hyde_root_suffix_empty 13 (by omega)
  · intro q hq
    exact AgentUCTNextExact.adverse_complete_normal_root_physical_quote_exact 13 (by omega) q hq

theorem adverseCompleteS14D1I0 : indexScore (7/5) (controlPenalty savedCref uniformQuoteError unitRoleUnused .complete) adverseCompleteS14Before [.query 1] (.hydeRetriever 1) = treeIndex ((0/1)/2) (7/5) 0 6 2 := by
  have hs : replayBackup adverseCompleteS14Before emptyStatistics ([.query 1]++[.hydeRetriever 1]) = ⟨2,(0/1)⟩ := by
    rw [replayBackup_empty_closed_form]
    simp +decide [backedEvents,adverseCompleteS14Before,adverseCompleteProposal,adverseCompleteEvent1,adverseCompleteEvent2,adverseCompleteEvent3,adverseCompleteEvent4,adverseCompleteEvent5,adverseCompleteEvent6,adverseCompleteEvent7,adverseCompleteEvent8,adverseCompleteEvent9,adverseCompleteEvent10,adverseCompleteEvent11,adverseCompleteEvent12,adverseCompleteEvent13,taskReward]
    <;> norm_num
  have hp : rawVisits adverseCompleteS14Before [.query 1] = 6 := by decide
  have hn : rawVisits adverseCompleteS14Before ([.query 1]++[.hydeRetriever 1]) = 2 := by decide
  have hz : (controlPenalty savedCref uniformQuoteError unitRoleUnused .complete) adverseCompleteS14Before [.query 1] (.hydeRetriever 1) = 0 := by
    apply control_penalty_empty_of_prior_terminal .complete savedCref uniformQuoteError adverseCompleteS14Before [.query 1] (.hydeRetriever 1) 8 (by decide)
    · decide
    · decide
  unfold indexScore
  rw [hs,hp,hn,hz]
  simp only [BackupStat.mean]
  norm_num

theorem adverseCompleteS14D1I1 : indexScore (7/5) (controlPenalty savedCref uniformQuoteError unitRoleUnused .complete) adverseCompleteS14Before [.query 1] (.hydeRetriever 0) = treeIndex ((0/1)/2) (7/5) 0 6 2 := by
  have hs : replayBackup adverseCompleteS14Before emptyStatistics ([.query 1]++[.hydeRetriever 0]) = ⟨2,(0/1)⟩ := by
    rw [replayBackup_empty_closed_form]
    simp +decide [backedEvents,adverseCompleteS14Before,adverseCompleteProposal,adverseCompleteEvent1,adverseCompleteEvent2,adverseCompleteEvent3,adverseCompleteEvent4,adverseCompleteEvent5,adverseCompleteEvent6,adverseCompleteEvent7,adverseCompleteEvent8,adverseCompleteEvent9,adverseCompleteEvent10,adverseCompleteEvent11,adverseCompleteEvent12,adverseCompleteEvent13,taskReward]
    <;> norm_num
  have hp : rawVisits adverseCompleteS14Before [.query 1] = 6 := by decide
  have hn : rawVisits adverseCompleteS14Before ([.query 1]++[.hydeRetriever 0]) = 2 := by decide
  have hz : (controlPenalty savedCref uniformQuoteError unitRoleUnused .complete) adverseCompleteS14Before [.query 1] (.hydeRetriever 0) = 0 := by
    apply control_penalty_empty_of_prior_terminal .complete savedCref uniformQuoteError adverseCompleteS14Before [.query 1] (.hydeRetriever 0) 1 (by decide)
    · decide
    · decide
  unfold indexScore
  rw [hs,hp,hn,hz]
  simp only [BackupStat.mean]
  norm_num

theorem adverseCompleteS14D1I2 : indexScore (7/5) (controlPenalty savedCref uniformQuoteError unitRoleUnused .complete) adverseCompleteS14Before [.query 1] (.hydeRetriever 2) = treeIndex ((0/1)/1) (7/5) 0 6 1 := by
  have hs : replayBackup adverseCompleteS14Before emptyStatistics ([.query 1]++[.hydeRetriever 2]) = ⟨1,(0/1)⟩ := by
    rw [replayBackup_empty_closed_form]
    simp +decide [backedEvents,adverseCompleteS14Before,adverseCompleteProposal,adverseCompleteEvent1,adverseCompleteEvent2,adverseCompleteEvent3,adverseCompleteEvent4,adverseCompleteEvent5,adverseCompleteEvent6,adverseCompleteEvent7,adverseCompleteEvent8,adverseCompleteEvent9,adverseCompleteEvent10,adverseCompleteEvent11,adverseCompleteEvent12,adverseCompleteEvent13,taskReward]
    <;> norm_num
  have hp : rawVisits adverseCompleteS14Before [.query 1] = 6 := by decide
  have hn : rawVisits adverseCompleteS14Before ([.query 1]++[.hydeRetriever 2]) = 1 := by decide
  have hz : (controlPenalty savedCref uniformQuoteError unitRoleUnused .complete) adverseCompleteS14Before [.query 1] (.hydeRetriever 2) = 0 := by
    apply control_penalty_empty_of_prior_terminal .complete savedCref uniformQuoteError adverseCompleteS14Before [.query 1] (.hydeRetriever 2) 10 (by decide)
    · decide
    · decide
  unfold indexScore
  rw [hs,hp,hn,hz]
  simp only [BackupStat.mean]
  norm_num

theorem adverseCompleteS14D1Cmp0 : indexScore (7/5) (controlPenalty savedCref uniformQuoteError unitRoleUnused .complete) adverseCompleteS14Before [.query 1] (.hydeRetriever 1) < indexScore (7/5) (controlPenalty savedCref uniformQuoteError unitRoleUnused .complete) adverseCompleteS14Before [.query 1] (.hydeRetriever 2) := by
  rw [adverseCompleteS14D1I0,adverseCompleteS14D1I2]
  have h := index_strict_order_from_intervals ((0/1)/1) ((0/1)/2) 0 0 (24411779/12500000) (69046943/50000000)
    (treeBonus (7/5) 6 1) (treeBonus (7/5) 6 2)
    (trajectory_bonus_6_1).1 (trajectory_bonus_6_2).2 (by norm_num)
  simpa only [treeIndex,sub_zero] using h

theorem adverseCompleteS14D1Cmp1 : indexScore (7/5) (controlPenalty savedCref uniformQuoteError unitRoleUnused .complete) adverseCompleteS14Before [.query 1] (.hydeRetriever 0) < indexScore (7/5) (controlPenalty savedCref uniformQuoteError unitRoleUnused .complete) adverseCompleteS14Before [.query 1] (.hydeRetriever 2) := by
  rw [adverseCompleteS14D1I1,adverseCompleteS14D1I2]
  have h := index_strict_order_from_intervals ((0/1)/1) ((0/1)/2) 0 0 (24411779/12500000) (69046943/50000000)
    (treeBonus (7/5) 6 1) (treeBonus (7/5) 6 2)
    (trajectory_bonus_6_1).1 (trajectory_bonus_6_2).2 (by norm_num)
  simpa only [treeIndex,sub_zero] using h

theorem adverseCompleteS14Choice1 : nativeFirstChoice (indexScore (7/5) (controlPenalty savedCref uniformQuoteError unitRoleUnused .complete) adverseCompleteS14Before [.query 1]) adverseCompleteS14Before [.query 1] = .hydeRetriever 2 := by
  apply visited_choice_from_ordered_certificate _ _ [.query 1] [.hydeRetriever 1,.hydeRetriever 0] [] (.hydeRetriever 2) (by decide)
  · intro a ha
    have ho : orderedLegalAvailable [.query 1] = [.hydeRetriever 1,.hydeRetriever 0,.hydeRetriever 2] := by decide
    rw [ho] at ha
    simp only [List.mem_cons,List.not_mem_nil,or_false] at ha
    rcases ha with rfl | rfl | rfl <;> decide
  · intro a ha
    simp only [List.mem_cons,List.not_mem_nil,or_false] at ha
    rcases ha with rfl | rfl
    · exact adverseCompleteS14D1Cmp0
    · exact adverseCompleteS14D1Cmp1
  · simp

theorem adverseCompleteS14ActualEvent : nativeEvent budgetTape (7/5) (controlPenalty savedCref uniformQuoteError unitRoleUnused .complete)
    (taskReward true (2/5) (1/2)) adverseCompleteS14Before = adverseCompleteEvent14 := by
  have hs0 := native_select_existing_step budgetTape (7/5) (controlPenalty savedCref uniformQuoteError unitRoleUnused .complete) adverseCompleteS14Before 8 [] (.query 1)
    (by decide) (by decide) adverseCompleteS14Choice0
  have hs1 := native_select_existing_step budgetTape (7/5) (controlPenalty savedCref uniformQuoteError unitRoleUnused .complete) adverseCompleteS14Before 7 [.query 1] (.hydeRetriever 2)
    (by decide) (by decide) adverseCompleteS14Choice1
  have hnew := native_select_new_step budgetTape (7/5) (controlPenalty savedCref uniformQuoteError unitRoleUnused .complete) adverseCompleteS14Before 6 [.query 1,.hydeRetriever 2]
    [.selection 1,.selection 2,.selection 3,.selection 0] (.selection 0) (by decide) (by decide) (by decide) (by decide)
  have hs : nativeSelect budgetTape (7/5) (controlPenalty savedCref uniformQuoteError unitRoleUnused .complete) adverseCompleteS14Before 9 [] = [.query 1,.hydeRetriever 2,.selection 0] := by
    rw [hs0]
    change nativeSelect budgetTape (7/5) (controlPenalty savedCref uniformQuoteError unitRoleUnused .complete) adverseCompleteS14Before 8 [.query 1] = _
    rw [hs1]
    change nativeSelect budgetTape (7/5) (controlPenalty savedCref uniformQuoteError unitRoleUnused .complete) adverseCompleteS14Before 7 [.query 1,.hydeRetriever 2] = _
    rw [hnew] <;> rfl
  have hr : repairedRollout budgetTape adverseCompleteS14Before 9 [.query 1,.hydeRetriever 2,.selection 0] = [.query 1,.hydeRetriever 2,.selection 0,.width 0,.stop,.reranker 0,.topm 2,.context 0,.answer 2] := by decide
  simp only [nativeEvent,hs,hr]
  rfl

def adverseCompleteS15Before := adverseCompleteProposal.take 14

theorem adverseCompleteS15Choice0 : nativeFirstChoice (indexScore (7/5) (controlPenalty savedCref uniformQuoteError unitRoleUnused .complete) adverseCompleteS15Before []) adverseCompleteS15Before [] = .query 1 := by
  apply complete_root_from_physical_gap adverseCompleteS15Before (adverseComplete_prefix_rewards 14) (by decide)
  · intro q; fin_cases q <;> decide
  · exact AgentUCTNextExact.adverse_complete_hyde_root_suffix_empty 14 (by omega)
  · intro q hq
    exact AgentUCTNextExact.adverse_complete_normal_root_physical_quote_exact 14 (by omega) q hq

theorem adverseCompleteS15D1I0 : indexScore (7/5) (controlPenalty savedCref uniformQuoteError unitRoleUnused .complete) adverseCompleteS15Before [.query 1] (.hydeRetriever 1) = treeIndex ((0/1)/2) (7/5) 0 7 2 := by
  have hs : replayBackup adverseCompleteS15Before emptyStatistics ([.query 1]++[.hydeRetriever 1]) = ⟨2,(0/1)⟩ := by
    rw [replayBackup_empty_closed_form]
    simp +decide [backedEvents,adverseCompleteS15Before,adverseCompleteProposal,adverseCompleteEvent1,adverseCompleteEvent2,adverseCompleteEvent3,adverseCompleteEvent4,adverseCompleteEvent5,adverseCompleteEvent6,adverseCompleteEvent7,adverseCompleteEvent8,adverseCompleteEvent9,adverseCompleteEvent10,adverseCompleteEvent11,adverseCompleteEvent12,adverseCompleteEvent13,adverseCompleteEvent14,taskReward]
    <;> norm_num
  have hp : rawVisits adverseCompleteS15Before [.query 1] = 7 := by decide
  have hn : rawVisits adverseCompleteS15Before ([.query 1]++[.hydeRetriever 1]) = 2 := by decide
  have hz : (controlPenalty savedCref uniformQuoteError unitRoleUnused .complete) adverseCompleteS15Before [.query 1] (.hydeRetriever 1) = 0 := by
    apply control_penalty_empty_of_prior_terminal .complete savedCref uniformQuoteError adverseCompleteS15Before [.query 1] (.hydeRetriever 1) 8 (by decide)
    · decide
    · decide
  unfold indexScore
  rw [hs,hp,hn,hz]
  simp only [BackupStat.mean]
  norm_num

theorem adverseCompleteS15D1I1 : indexScore (7/5) (controlPenalty savedCref uniformQuoteError unitRoleUnused .complete) adverseCompleteS15Before [.query 1] (.hydeRetriever 0) = treeIndex ((0/1)/2) (7/5) 0 7 2 := by
  have hs : replayBackup adverseCompleteS15Before emptyStatistics ([.query 1]++[.hydeRetriever 0]) = ⟨2,(0/1)⟩ := by
    rw [replayBackup_empty_closed_form]
    simp +decide [backedEvents,adverseCompleteS15Before,adverseCompleteProposal,adverseCompleteEvent1,adverseCompleteEvent2,adverseCompleteEvent3,adverseCompleteEvent4,adverseCompleteEvent5,adverseCompleteEvent6,adverseCompleteEvent7,adverseCompleteEvent8,adverseCompleteEvent9,adverseCompleteEvent10,adverseCompleteEvent11,adverseCompleteEvent12,adverseCompleteEvent13,adverseCompleteEvent14,taskReward]
    <;> norm_num
  have hp : rawVisits adverseCompleteS15Before [.query 1] = 7 := by decide
  have hn : rawVisits adverseCompleteS15Before ([.query 1]++[.hydeRetriever 0]) = 2 := by decide
  have hz : (controlPenalty savedCref uniformQuoteError unitRoleUnused .complete) adverseCompleteS15Before [.query 1] (.hydeRetriever 0) = 0 := by
    apply control_penalty_empty_of_prior_terminal .complete savedCref uniformQuoteError adverseCompleteS15Before [.query 1] (.hydeRetriever 0) 1 (by decide)
    · decide
    · decide
  unfold indexScore
  rw [hs,hp,hn,hz]
  simp only [BackupStat.mean]
  norm_num

theorem adverseCompleteS15D1I2 : indexScore (7/5) (controlPenalty savedCref uniformQuoteError unitRoleUnused .complete) adverseCompleteS15Before [.query 1] (.hydeRetriever 2) = treeIndex ((0/1)/2) (7/5) 0 7 2 := by
  have hs : replayBackup adverseCompleteS15Before emptyStatistics ([.query 1]++[.hydeRetriever 2]) = ⟨2,(0/1)⟩ := by
    rw [replayBackup_empty_closed_form]
    simp +decide [backedEvents,adverseCompleteS15Before,adverseCompleteProposal,adverseCompleteEvent1,adverseCompleteEvent2,adverseCompleteEvent3,adverseCompleteEvent4,adverseCompleteEvent5,adverseCompleteEvent6,adverseCompleteEvent7,adverseCompleteEvent8,adverseCompleteEvent9,adverseCompleteEvent10,adverseCompleteEvent11,adverseCompleteEvent12,adverseCompleteEvent13,adverseCompleteEvent14,taskReward]
    <;> norm_num
  have hp : rawVisits adverseCompleteS15Before [.query 1] = 7 := by decide
  have hn : rawVisits adverseCompleteS15Before ([.query 1]++[.hydeRetriever 2]) = 2 := by decide
  have hz : (controlPenalty savedCref uniformQuoteError unitRoleUnused .complete) adverseCompleteS15Before [.query 1] (.hydeRetriever 2) = 0 := by
    apply control_penalty_empty_of_prior_terminal .complete savedCref uniformQuoteError adverseCompleteS15Before [.query 1] (.hydeRetriever 2) 10 (by decide)
    · decide
    · decide
  unfold indexScore
  rw [hs,hp,hn,hz]
  simp only [BackupStat.mean]
  norm_num

theorem adverseCompleteS15D1Cmp1 : indexScore (7/5) (controlPenalty savedCref uniformQuoteError unitRoleUnused .complete) adverseCompleteS15Before [.query 1] (.hydeRetriever 0) ≤ indexScore (7/5) (controlPenalty savedCref uniformQuoteError unitRoleUnused .complete) adverseCompleteS15Before [.query 1] (.hydeRetriever 1) := by
  rw [adverseCompleteS15D1I1,adverseCompleteS15D1I0]

theorem adverseCompleteS15D1Cmp2 : indexScore (7/5) (controlPenalty savedCref uniformQuoteError unitRoleUnused .complete) adverseCompleteS15Before [.query 1] (.hydeRetriever 2) ≤ indexScore (7/5) (controlPenalty savedCref uniformQuoteError unitRoleUnused .complete) adverseCompleteS15Before [.query 1] (.hydeRetriever 1) := by
  rw [adverseCompleteS15D1I2,adverseCompleteS15D1I0]

theorem adverseCompleteS15Choice1 : nativeFirstChoice (indexScore (7/5) (controlPenalty savedCref uniformQuoteError unitRoleUnused .complete) adverseCompleteS15Before [.query 1]) adverseCompleteS15Before [.query 1] = .hydeRetriever 1 := by
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
    · exact adverseCompleteS15D1Cmp1
    · exact adverseCompleteS15D1Cmp2

theorem adverseCompleteS15ActualEvent : nativeEvent budgetTape (7/5) (controlPenalty savedCref uniformQuoteError unitRoleUnused .complete)
    (taskReward true (2/5) (1/2)) adverseCompleteS15Before = adverseCompleteEvent15 := by
  have hs0 := native_select_existing_step budgetTape (7/5) (controlPenalty savedCref uniformQuoteError unitRoleUnused .complete) adverseCompleteS15Before 8 [] (.query 1)
    (by decide) (by decide) adverseCompleteS15Choice0
  have hs1 := native_select_existing_step budgetTape (7/5) (controlPenalty savedCref uniformQuoteError unitRoleUnused .complete) adverseCompleteS15Before 7 [.query 1] (.hydeRetriever 1)
    (by decide) (by decide) adverseCompleteS15Choice1
  have hnew := native_select_new_step budgetTape (7/5) (controlPenalty savedCref uniformQuoteError unitRoleUnused .complete) adverseCompleteS15Before 6 [.query 1,.hydeRetriever 1]
    [.selection 1,.selection 2,.selection 3] (.selection 1) (by decide) (by decide) (by decide) (by decide)
  have hs : nativeSelect budgetTape (7/5) (controlPenalty savedCref uniformQuoteError unitRoleUnused .complete) adverseCompleteS15Before 9 [] = [.query 1,.hydeRetriever 1,.selection 1] := by
    rw [hs0]
    change nativeSelect budgetTape (7/5) (controlPenalty savedCref uniformQuoteError unitRoleUnused .complete) adverseCompleteS15Before 8 [.query 1] = _
    rw [hs1]
    change nativeSelect budgetTape (7/5) (controlPenalty savedCref uniformQuoteError unitRoleUnused .complete) adverseCompleteS15Before 7 [.query 1,.hydeRetriever 1] = _
    rw [hnew] <;> rfl
  have hr : repairedRollout budgetTape adverseCompleteS15Before 9 [.query 1,.hydeRetriever 1,.selection 1] = [.query 1,.hydeRetriever 1,.selection 1,.width 0,.stop,.reranker 0,.topm 0,.context 0,.answer 0] := by decide
  simp only [nativeEvent,hs,hr]
  rfl

def adverseCompleteS16Before := adverseCompleteProposal.take 15

theorem adverseCompleteS16Choice0 : nativeFirstChoice (indexScore (7/5) (controlPenalty savedCref uniformQuoteError unitRoleUnused .complete) adverseCompleteS16Before []) adverseCompleteS16Before [] = .query 1 := by
  apply complete_root_from_physical_gap adverseCompleteS16Before (adverseComplete_prefix_rewards 15) (by decide)
  · intro q; fin_cases q <;> decide
  · exact AgentUCTNextExact.adverse_complete_hyde_root_suffix_empty 15 (by omega)
  · intro q hq
    exact AgentUCTNextExact.adverse_complete_normal_root_physical_quote_exact 15 (by omega) q hq

theorem adverseCompleteS16D1I0 : indexScore (7/5) (controlPenalty savedCref uniformQuoteError unitRoleUnused .complete) adverseCompleteS16Before [.query 1] (.hydeRetriever 1) = treeIndex ((0/1)/3) (7/5) 0 8 3 := by
  have hs : replayBackup adverseCompleteS16Before emptyStatistics ([.query 1]++[.hydeRetriever 1]) = ⟨3,(0/1)⟩ := by
    rw [replayBackup_empty_closed_form]
    simp +decide [backedEvents,adverseCompleteS16Before,adverseCompleteProposal,adverseCompleteEvent1,adverseCompleteEvent2,adverseCompleteEvent3,adverseCompleteEvent4,adverseCompleteEvent5,adverseCompleteEvent6,adverseCompleteEvent7,adverseCompleteEvent8,adverseCompleteEvent9,adverseCompleteEvent10,adverseCompleteEvent11,adverseCompleteEvent12,adverseCompleteEvent13,adverseCompleteEvent14,adverseCompleteEvent15,taskReward]
    <;> norm_num
  have hp : rawVisits adverseCompleteS16Before [.query 1] = 8 := by decide
  have hn : rawVisits adverseCompleteS16Before ([.query 1]++[.hydeRetriever 1]) = 3 := by decide
  have hz : (controlPenalty savedCref uniformQuoteError unitRoleUnused .complete) adverseCompleteS16Before [.query 1] (.hydeRetriever 1) = 0 := by
    apply control_penalty_empty_of_prior_terminal .complete savedCref uniformQuoteError adverseCompleteS16Before [.query 1] (.hydeRetriever 1) 8 (by decide)
    · decide
    · decide
  unfold indexScore
  rw [hs,hp,hn,hz]
  simp only [BackupStat.mean]
  norm_num

theorem adverseCompleteS16D1I1 : indexScore (7/5) (controlPenalty savedCref uniformQuoteError unitRoleUnused .complete) adverseCompleteS16Before [.query 1] (.hydeRetriever 0) = treeIndex ((0/1)/2) (7/5) 0 8 2 := by
  have hs : replayBackup adverseCompleteS16Before emptyStatistics ([.query 1]++[.hydeRetriever 0]) = ⟨2,(0/1)⟩ := by
    rw [replayBackup_empty_closed_form]
    simp +decide [backedEvents,adverseCompleteS16Before,adverseCompleteProposal,adverseCompleteEvent1,adverseCompleteEvent2,adverseCompleteEvent3,adverseCompleteEvent4,adverseCompleteEvent5,adverseCompleteEvent6,adverseCompleteEvent7,adverseCompleteEvent8,adverseCompleteEvent9,adverseCompleteEvent10,adverseCompleteEvent11,adverseCompleteEvent12,adverseCompleteEvent13,adverseCompleteEvent14,adverseCompleteEvent15,taskReward]
    <;> norm_num
  have hp : rawVisits adverseCompleteS16Before [.query 1] = 8 := by decide
  have hn : rawVisits adverseCompleteS16Before ([.query 1]++[.hydeRetriever 0]) = 2 := by decide
  have hz : (controlPenalty savedCref uniformQuoteError unitRoleUnused .complete) adverseCompleteS16Before [.query 1] (.hydeRetriever 0) = 0 := by
    apply control_penalty_empty_of_prior_terminal .complete savedCref uniformQuoteError adverseCompleteS16Before [.query 1] (.hydeRetriever 0) 1 (by decide)
    · decide
    · decide
  unfold indexScore
  rw [hs,hp,hn,hz]
  simp only [BackupStat.mean]
  norm_num

theorem adverseCompleteS16D1I2 : indexScore (7/5) (controlPenalty savedCref uniformQuoteError unitRoleUnused .complete) adverseCompleteS16Before [.query 1] (.hydeRetriever 2) = treeIndex ((0/1)/2) (7/5) 0 8 2 := by
  have hs : replayBackup adverseCompleteS16Before emptyStatistics ([.query 1]++[.hydeRetriever 2]) = ⟨2,(0/1)⟩ := by
    rw [replayBackup_empty_closed_form]
    simp +decide [backedEvents,adverseCompleteS16Before,adverseCompleteProposal,adverseCompleteEvent1,adverseCompleteEvent2,adverseCompleteEvent3,adverseCompleteEvent4,adverseCompleteEvent5,adverseCompleteEvent6,adverseCompleteEvent7,adverseCompleteEvent8,adverseCompleteEvent9,adverseCompleteEvent10,adverseCompleteEvent11,adverseCompleteEvent12,adverseCompleteEvent13,adverseCompleteEvent14,adverseCompleteEvent15,taskReward]
    <;> norm_num
  have hp : rawVisits adverseCompleteS16Before [.query 1] = 8 := by decide
  have hn : rawVisits adverseCompleteS16Before ([.query 1]++[.hydeRetriever 2]) = 2 := by decide
  have hz : (controlPenalty savedCref uniformQuoteError unitRoleUnused .complete) adverseCompleteS16Before [.query 1] (.hydeRetriever 2) = 0 := by
    apply control_penalty_empty_of_prior_terminal .complete savedCref uniformQuoteError adverseCompleteS16Before [.query 1] (.hydeRetriever 2) 10 (by decide)
    · decide
    · decide
  unfold indexScore
  rw [hs,hp,hn,hz]
  simp only [BackupStat.mean]
  norm_num

theorem adverseCompleteS16D1Cmp0 : indexScore (7/5) (controlPenalty savedCref uniformQuoteError unitRoleUnused .complete) adverseCompleteS16Before [.query 1] (.hydeRetriever 1) < indexScore (7/5) (controlPenalty savedCref uniformQuoteError unitRoleUnused .complete) adverseCompleteS16Before [.query 1] (.hydeRetriever 0) := by
  rw [adverseCompleteS16D1I0,adverseCompleteS16D1I1]
  have h := index_strict_order_from_intervals ((0/1)/2) ((0/1)/3) 0 0 (7337029/5000000) (29953301/25000000)
    (treeBonus (7/5) 8 2) (treeBonus (7/5) 8 3)
    (trajectory_bonus_8_2).1 (trajectory_bonus_8_3).2 (by norm_num)
  simpa only [treeIndex,sub_zero] using h

theorem adverseCompleteS16D1Cmp2 : indexScore (7/5) (controlPenalty savedCref uniformQuoteError unitRoleUnused .complete) adverseCompleteS16Before [.query 1] (.hydeRetriever 2) ≤ indexScore (7/5) (controlPenalty savedCref uniformQuoteError unitRoleUnused .complete) adverseCompleteS16Before [.query 1] (.hydeRetriever 0) := by
  rw [adverseCompleteS16D1I2,adverseCompleteS16D1I1]

theorem adverseCompleteS16Choice1 : nativeFirstChoice (indexScore (7/5) (controlPenalty savedCref uniformQuoteError unitRoleUnused .complete) adverseCompleteS16Before [.query 1]) adverseCompleteS16Before [.query 1] = .hydeRetriever 0 := by
  apply visited_choice_from_ordered_certificate _ _ [.query 1] [.hydeRetriever 1] [.hydeRetriever 2] (.hydeRetriever 0) (by decide)
  · intro a ha
    have ho : orderedLegalAvailable [.query 1] = [.hydeRetriever 1,.hydeRetriever 0,.hydeRetriever 2] := by decide
    rw [ho] at ha
    simp only [List.mem_cons,List.not_mem_nil,or_false] at ha
    rcases ha with rfl | rfl | rfl <;> decide
  · intro a ha
    simp only [List.mem_cons,List.not_mem_nil,or_false] at ha
    rcases ha with rfl
    · exact adverseCompleteS16D1Cmp0
  · intro a ha
    simp only [List.mem_cons,List.not_mem_nil,or_false] at ha
    rcases ha with rfl
    · exact adverseCompleteS16D1Cmp2

theorem adverseCompleteS16ActualEvent : nativeEvent budgetTape (7/5) (controlPenalty savedCref uniformQuoteError unitRoleUnused .complete)
    (taskReward true (2/5) (1/2)) adverseCompleteS16Before = adverseCompleteEvent16 := by
  have hs0 := native_select_existing_step budgetTape (7/5) (controlPenalty savedCref uniformQuoteError unitRoleUnused .complete) adverseCompleteS16Before 8 [] (.query 1)
    (by decide) (by decide) adverseCompleteS16Choice0
  have hs1 := native_select_existing_step budgetTape (7/5) (controlPenalty savedCref uniformQuoteError unitRoleUnused .complete) adverseCompleteS16Before 7 [.query 1] (.hydeRetriever 0)
    (by decide) (by decide) adverseCompleteS16Choice1
  have hnew := native_select_new_step budgetTape (7/5) (controlPenalty savedCref uniformQuoteError unitRoleUnused .complete) adverseCompleteS16Before 6 [.query 1,.hydeRetriever 0]
    [.selection 1,.selection 2,.selection 3] (.selection 1) (by decide) (by decide) (by decide) (by decide)
  have hs : nativeSelect budgetTape (7/5) (controlPenalty savedCref uniformQuoteError unitRoleUnused .complete) adverseCompleteS16Before 9 [] = [.query 1,.hydeRetriever 0,.selection 1] := by
    rw [hs0]
    change nativeSelect budgetTape (7/5) (controlPenalty savedCref uniformQuoteError unitRoleUnused .complete) adverseCompleteS16Before 8 [.query 1] = _
    rw [hs1]
    change nativeSelect budgetTape (7/5) (controlPenalty savedCref uniformQuoteError unitRoleUnused .complete) adverseCompleteS16Before 7 [.query 1,.hydeRetriever 0] = _
    rw [hnew] <;> rfl
  have hr : repairedRollout budgetTape adverseCompleteS16Before 9 [.query 1,.hydeRetriever 0,.selection 1] = [.query 1,.hydeRetriever 0,.selection 1,.width 0,.stop,.reranker 0,.topm 0,.context 0,.answer 0] := by decide
  simp only [nativeEvent,hs,hr]
  rfl

def adverseCompleteS17Before := adverseCompleteProposal.take 16

theorem adverseCompleteS17Choice0 : nativeFirstChoice (indexScore (7/5) (controlPenalty savedCref uniformQuoteError unitRoleUnused .complete) adverseCompleteS17Before []) adverseCompleteS17Before [] = .query 1 := by
  apply complete_root_from_physical_gap adverseCompleteS17Before (adverseComplete_prefix_rewards 16) (by decide)
  · intro q; fin_cases q <;> decide
  · exact AgentUCTNextExact.adverse_complete_hyde_root_suffix_empty 16 (by omega)
  · intro q hq
    exact AgentUCTNextExact.adverse_complete_normal_root_physical_quote_exact 16 (by omega) q hq

theorem adverseCompleteS17D1I0 : indexScore (7/5) (controlPenalty savedCref uniformQuoteError unitRoleUnused .complete) adverseCompleteS17Before [.query 1] (.hydeRetriever 1) = treeIndex ((0/1)/3) (7/5) 0 9 3 := by
  have hs : replayBackup adverseCompleteS17Before emptyStatistics ([.query 1]++[.hydeRetriever 1]) = ⟨3,(0/1)⟩ := by
    rw [replayBackup_empty_closed_form]
    simp +decide [backedEvents,adverseCompleteS17Before,adverseCompleteProposal,adverseCompleteEvent1,adverseCompleteEvent2,adverseCompleteEvent3,adverseCompleteEvent4,adverseCompleteEvent5,adverseCompleteEvent6,adverseCompleteEvent7,adverseCompleteEvent8,adverseCompleteEvent9,adverseCompleteEvent10,adverseCompleteEvent11,adverseCompleteEvent12,adverseCompleteEvent13,adverseCompleteEvent14,adverseCompleteEvent15,adverseCompleteEvent16,taskReward]
    <;> norm_num
  have hp : rawVisits adverseCompleteS17Before [.query 1] = 9 := by decide
  have hn : rawVisits adverseCompleteS17Before ([.query 1]++[.hydeRetriever 1]) = 3 := by decide
  have hz : (controlPenalty savedCref uniformQuoteError unitRoleUnused .complete) adverseCompleteS17Before [.query 1] (.hydeRetriever 1) = 0 := by
    apply control_penalty_empty_of_prior_terminal .complete savedCref uniformQuoteError adverseCompleteS17Before [.query 1] (.hydeRetriever 1) 8 (by decide)
    · decide
    · decide
  unfold indexScore
  rw [hs,hp,hn,hz]
  simp only [BackupStat.mean]
  norm_num

theorem adverseCompleteS17D1I1 : indexScore (7/5) (controlPenalty savedCref uniformQuoteError unitRoleUnused .complete) adverseCompleteS17Before [.query 1] (.hydeRetriever 0) = treeIndex ((0/1)/3) (7/5) 0 9 3 := by
  have hs : replayBackup adverseCompleteS17Before emptyStatistics ([.query 1]++[.hydeRetriever 0]) = ⟨3,(0/1)⟩ := by
    rw [replayBackup_empty_closed_form]
    simp +decide [backedEvents,adverseCompleteS17Before,adverseCompleteProposal,adverseCompleteEvent1,adverseCompleteEvent2,adverseCompleteEvent3,adverseCompleteEvent4,adverseCompleteEvent5,adverseCompleteEvent6,adverseCompleteEvent7,adverseCompleteEvent8,adverseCompleteEvent9,adverseCompleteEvent10,adverseCompleteEvent11,adverseCompleteEvent12,adverseCompleteEvent13,adverseCompleteEvent14,adverseCompleteEvent15,adverseCompleteEvent16,taskReward]
    <;> norm_num
  have hp : rawVisits adverseCompleteS17Before [.query 1] = 9 := by decide
  have hn : rawVisits adverseCompleteS17Before ([.query 1]++[.hydeRetriever 0]) = 3 := by decide
  have hz : (controlPenalty savedCref uniformQuoteError unitRoleUnused .complete) adverseCompleteS17Before [.query 1] (.hydeRetriever 0) = 0 := by
    apply control_penalty_empty_of_prior_terminal .complete savedCref uniformQuoteError adverseCompleteS17Before [.query 1] (.hydeRetriever 0) 1 (by decide)
    · decide
    · decide
  unfold indexScore
  rw [hs,hp,hn,hz]
  simp only [BackupStat.mean]
  norm_num

theorem adverseCompleteS17D1I2 : indexScore (7/5) (controlPenalty savedCref uniformQuoteError unitRoleUnused .complete) adverseCompleteS17Before [.query 1] (.hydeRetriever 2) = treeIndex ((0/1)/2) (7/5) 0 9 2 := by
  have hs : replayBackup adverseCompleteS17Before emptyStatistics ([.query 1]++[.hydeRetriever 2]) = ⟨2,(0/1)⟩ := by
    rw [replayBackup_empty_closed_form]
    simp +decide [backedEvents,adverseCompleteS17Before,adverseCompleteProposal,adverseCompleteEvent1,adverseCompleteEvent2,adverseCompleteEvent3,adverseCompleteEvent4,adverseCompleteEvent5,adverseCompleteEvent6,adverseCompleteEvent7,adverseCompleteEvent8,adverseCompleteEvent9,adverseCompleteEvent10,adverseCompleteEvent11,adverseCompleteEvent12,adverseCompleteEvent13,adverseCompleteEvent14,adverseCompleteEvent15,adverseCompleteEvent16,taskReward]
    <;> norm_num
  have hp : rawVisits adverseCompleteS17Before [.query 1] = 9 := by decide
  have hn : rawVisits adverseCompleteS17Before ([.query 1]++[.hydeRetriever 2]) = 2 := by decide
  have hz : (controlPenalty savedCref uniformQuoteError unitRoleUnused .complete) adverseCompleteS17Before [.query 1] (.hydeRetriever 2) = 0 := by
    apply control_penalty_empty_of_prior_terminal .complete savedCref uniformQuoteError adverseCompleteS17Before [.query 1] (.hydeRetriever 2) 10 (by decide)
    · decide
    · decide
  unfold indexScore
  rw [hs,hp,hn,hz]
  simp only [BackupStat.mean]
  norm_num

theorem adverseCompleteS17D1Cmp0 : indexScore (7/5) (controlPenalty savedCref uniformQuoteError unitRoleUnused .complete) adverseCompleteS17Before [.query 1] (.hydeRetriever 1) < indexScore (7/5) (controlPenalty savedCref uniformQuoteError unitRoleUnused .complete) adverseCompleteS17Before [.query 1] (.hydeRetriever 2) := by
  rw [adverseCompleteS17D1I0,adverseCompleteS17D1I2]
  have h := index_strict_order_from_intervals ((0/1)/2) ((0/1)/3) 0 0 (75108803/50000000) (6132609/5000000)
    (treeBonus (7/5) 9 2) (treeBonus (7/5) 9 3)
    (trajectory_bonus_9_2).1 (trajectory_bonus_9_3).2 (by norm_num)
  simpa only [treeIndex,sub_zero] using h

theorem adverseCompleteS17D1Cmp1 : indexScore (7/5) (controlPenalty savedCref uniformQuoteError unitRoleUnused .complete) adverseCompleteS17Before [.query 1] (.hydeRetriever 0) < indexScore (7/5) (controlPenalty savedCref uniformQuoteError unitRoleUnused .complete) adverseCompleteS17Before [.query 1] (.hydeRetriever 2) := by
  rw [adverseCompleteS17D1I1,adverseCompleteS17D1I2]
  have h := index_strict_order_from_intervals ((0/1)/2) ((0/1)/3) 0 0 (75108803/50000000) (6132609/5000000)
    (treeBonus (7/5) 9 2) (treeBonus (7/5) 9 3)
    (trajectory_bonus_9_2).1 (trajectory_bonus_9_3).2 (by norm_num)
  simpa only [treeIndex,sub_zero] using h

theorem adverseCompleteS17Choice1 : nativeFirstChoice (indexScore (7/5) (controlPenalty savedCref uniformQuoteError unitRoleUnused .complete) adverseCompleteS17Before [.query 1]) adverseCompleteS17Before [.query 1] = .hydeRetriever 2 := by
  apply visited_choice_from_ordered_certificate _ _ [.query 1] [.hydeRetriever 1,.hydeRetriever 0] [] (.hydeRetriever 2) (by decide)
  · intro a ha
    have ho : orderedLegalAvailable [.query 1] = [.hydeRetriever 1,.hydeRetriever 0,.hydeRetriever 2] := by decide
    rw [ho] at ha
    simp only [List.mem_cons,List.not_mem_nil,or_false] at ha
    rcases ha with rfl | rfl | rfl <;> decide
  · intro a ha
    simp only [List.mem_cons,List.not_mem_nil,or_false] at ha
    rcases ha with rfl | rfl
    · exact adverseCompleteS17D1Cmp0
    · exact adverseCompleteS17D1Cmp1
  · simp

theorem adverseCompleteS17ActualEvent : nativeEvent budgetTape (7/5) (controlPenalty savedCref uniformQuoteError unitRoleUnused .complete)
    (taskReward true (2/5) (1/2)) adverseCompleteS17Before = adverseCompleteEvent17 := by
  have hs0 := native_select_existing_step budgetTape (7/5) (controlPenalty savedCref uniformQuoteError unitRoleUnused .complete) adverseCompleteS17Before 8 [] (.query 1)
    (by decide) (by decide) adverseCompleteS17Choice0
  have hs1 := native_select_existing_step budgetTape (7/5) (controlPenalty savedCref uniformQuoteError unitRoleUnused .complete) adverseCompleteS17Before 7 [.query 1] (.hydeRetriever 2)
    (by decide) (by decide) adverseCompleteS17Choice1
  have hnew := native_select_new_step budgetTape (7/5) (controlPenalty savedCref uniformQuoteError unitRoleUnused .complete) adverseCompleteS17Before 6 [.query 1,.hydeRetriever 2]
    [.selection 1,.selection 2,.selection 3] (.selection 1) (by decide) (by decide) (by decide) (by decide)
  have hs : nativeSelect budgetTape (7/5) (controlPenalty savedCref uniformQuoteError unitRoleUnused .complete) adverseCompleteS17Before 9 [] = [.query 1,.hydeRetriever 2,.selection 1] := by
    rw [hs0]
    change nativeSelect budgetTape (7/5) (controlPenalty savedCref uniformQuoteError unitRoleUnused .complete) adverseCompleteS17Before 8 [.query 1] = _
    rw [hs1]
    change nativeSelect budgetTape (7/5) (controlPenalty savedCref uniformQuoteError unitRoleUnused .complete) adverseCompleteS17Before 7 [.query 1,.hydeRetriever 2] = _
    rw [hnew] <;> rfl
  have hr : repairedRollout budgetTape adverseCompleteS17Before 9 [.query 1,.hydeRetriever 2,.selection 1] = [.query 1,.hydeRetriever 2,.selection 1,.width 0,.stop,.reranker 0,.topm 0,.context 0,.answer 0] := by decide
  simp only [nativeEvent,hs,hr]
  rfl

def adverseCompleteS18Before := adverseCompleteProposal.take 17

theorem adverseCompleteS18Choice0 : nativeFirstChoice (indexScore (7/5) (controlPenalty savedCref uniformQuoteError unitRoleUnused .complete) adverseCompleteS18Before []) adverseCompleteS18Before [] = .query 1 := by
  apply complete_root_from_physical_gap adverseCompleteS18Before (adverseComplete_prefix_rewards 17) (by decide)
  · intro q; fin_cases q <;> decide
  · exact AgentUCTNextExact.adverse_complete_hyde_root_suffix_empty 17 (by omega)
  · intro q hq
    exact AgentUCTNextExact.adverse_complete_normal_root_physical_quote_exact 17 (by omega) q hq

theorem adverseCompleteS18D1I0 : indexScore (7/5) (controlPenalty savedCref uniformQuoteError unitRoleUnused .complete) adverseCompleteS18Before [.query 1] (.hydeRetriever 1) = treeIndex ((0/1)/3) (7/5) 0 10 3 := by
  have hs : replayBackup adverseCompleteS18Before emptyStatistics ([.query 1]++[.hydeRetriever 1]) = ⟨3,(0/1)⟩ := by
    rw [replayBackup_empty_closed_form]
    simp +decide [backedEvents,adverseCompleteS18Before,adverseCompleteProposal,adverseCompleteEvent1,adverseCompleteEvent2,adverseCompleteEvent3,adverseCompleteEvent4,adverseCompleteEvent5,adverseCompleteEvent6,adverseCompleteEvent7,adverseCompleteEvent8,adverseCompleteEvent9,adverseCompleteEvent10,adverseCompleteEvent11,adverseCompleteEvent12,adverseCompleteEvent13,adverseCompleteEvent14,adverseCompleteEvent15,adverseCompleteEvent16,adverseCompleteEvent17,taskReward]
    <;> norm_num
  have hp : rawVisits adverseCompleteS18Before [.query 1] = 10 := by decide
  have hn : rawVisits adverseCompleteS18Before ([.query 1]++[.hydeRetriever 1]) = 3 := by decide
  have hz : (controlPenalty savedCref uniformQuoteError unitRoleUnused .complete) adverseCompleteS18Before [.query 1] (.hydeRetriever 1) = 0 := by
    apply control_penalty_empty_of_prior_terminal .complete savedCref uniformQuoteError adverseCompleteS18Before [.query 1] (.hydeRetriever 1) 8 (by decide)
    · decide
    · decide
  unfold indexScore
  rw [hs,hp,hn,hz]
  simp only [BackupStat.mean]
  norm_num

theorem adverseCompleteS18D1I1 : indexScore (7/5) (controlPenalty savedCref uniformQuoteError unitRoleUnused .complete) adverseCompleteS18Before [.query 1] (.hydeRetriever 0) = treeIndex ((0/1)/3) (7/5) 0 10 3 := by
  have hs : replayBackup adverseCompleteS18Before emptyStatistics ([.query 1]++[.hydeRetriever 0]) = ⟨3,(0/1)⟩ := by
    rw [replayBackup_empty_closed_form]
    simp +decide [backedEvents,adverseCompleteS18Before,adverseCompleteProposal,adverseCompleteEvent1,adverseCompleteEvent2,adverseCompleteEvent3,adverseCompleteEvent4,adverseCompleteEvent5,adverseCompleteEvent6,adverseCompleteEvent7,adverseCompleteEvent8,adverseCompleteEvent9,adverseCompleteEvent10,adverseCompleteEvent11,adverseCompleteEvent12,adverseCompleteEvent13,adverseCompleteEvent14,adverseCompleteEvent15,adverseCompleteEvent16,adverseCompleteEvent17,taskReward]
    <;> norm_num
  have hp : rawVisits adverseCompleteS18Before [.query 1] = 10 := by decide
  have hn : rawVisits adverseCompleteS18Before ([.query 1]++[.hydeRetriever 0]) = 3 := by decide
  have hz : (controlPenalty savedCref uniformQuoteError unitRoleUnused .complete) adverseCompleteS18Before [.query 1] (.hydeRetriever 0) = 0 := by
    apply control_penalty_empty_of_prior_terminal .complete savedCref uniformQuoteError adverseCompleteS18Before [.query 1] (.hydeRetriever 0) 1 (by decide)
    · decide
    · decide
  unfold indexScore
  rw [hs,hp,hn,hz]
  simp only [BackupStat.mean]
  norm_num

theorem adverseCompleteS18D1I2 : indexScore (7/5) (controlPenalty savedCref uniformQuoteError unitRoleUnused .complete) adverseCompleteS18Before [.query 1] (.hydeRetriever 2) = treeIndex ((0/1)/3) (7/5) 0 10 3 := by
  have hs : replayBackup adverseCompleteS18Before emptyStatistics ([.query 1]++[.hydeRetriever 2]) = ⟨3,(0/1)⟩ := by
    rw [replayBackup_empty_closed_form]
    simp +decide [backedEvents,adverseCompleteS18Before,adverseCompleteProposal,adverseCompleteEvent1,adverseCompleteEvent2,adverseCompleteEvent3,adverseCompleteEvent4,adverseCompleteEvent5,adverseCompleteEvent6,adverseCompleteEvent7,adverseCompleteEvent8,adverseCompleteEvent9,adverseCompleteEvent10,adverseCompleteEvent11,adverseCompleteEvent12,adverseCompleteEvent13,adverseCompleteEvent14,adverseCompleteEvent15,adverseCompleteEvent16,adverseCompleteEvent17,taskReward]
    <;> norm_num
  have hp : rawVisits adverseCompleteS18Before [.query 1] = 10 := by decide
  have hn : rawVisits adverseCompleteS18Before ([.query 1]++[.hydeRetriever 2]) = 3 := by decide
  have hz : (controlPenalty savedCref uniformQuoteError unitRoleUnused .complete) adverseCompleteS18Before [.query 1] (.hydeRetriever 2) = 0 := by
    apply control_penalty_empty_of_prior_terminal .complete savedCref uniformQuoteError adverseCompleteS18Before [.query 1] (.hydeRetriever 2) 10 (by decide)
    · decide
    · decide
  unfold indexScore
  rw [hs,hp,hn,hz]
  simp only [BackupStat.mean]
  norm_num

theorem adverseCompleteS18D1Cmp1 : indexScore (7/5) (controlPenalty savedCref uniformQuoteError unitRoleUnused .complete) adverseCompleteS18Before [.query 1] (.hydeRetriever 0) ≤ indexScore (7/5) (controlPenalty savedCref uniformQuoteError unitRoleUnused .complete) adverseCompleteS18Before [.query 1] (.hydeRetriever 1) := by
  rw [adverseCompleteS18D1I1,adverseCompleteS18D1I0]

theorem adverseCompleteS18D1Cmp2 : indexScore (7/5) (controlPenalty savedCref uniformQuoteError unitRoleUnused .complete) adverseCompleteS18Before [.query 1] (.hydeRetriever 2) ≤ indexScore (7/5) (controlPenalty savedCref uniformQuoteError unitRoleUnused .complete) adverseCompleteS18Before [.query 1] (.hydeRetriever 1) := by
  rw [adverseCompleteS18D1I2,adverseCompleteS18D1I0]

theorem adverseCompleteS18Choice1 : nativeFirstChoice (indexScore (7/5) (controlPenalty savedCref uniformQuoteError unitRoleUnused .complete) adverseCompleteS18Before [.query 1]) adverseCompleteS18Before [.query 1] = .hydeRetriever 1 := by
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
    · exact adverseCompleteS18D1Cmp1
    · exact adverseCompleteS18D1Cmp2

theorem adverseCompleteS18ActualEvent : nativeEvent budgetTape (7/5) (controlPenalty savedCref uniformQuoteError unitRoleUnused .complete)
    (taskReward true (2/5) (1/2)) adverseCompleteS18Before = adverseCompleteEvent18 := by
  have hs0 := native_select_existing_step budgetTape (7/5) (controlPenalty savedCref uniformQuoteError unitRoleUnused .complete) adverseCompleteS18Before 8 [] (.query 1)
    (by decide) (by decide) adverseCompleteS18Choice0
  have hs1 := native_select_existing_step budgetTape (7/5) (controlPenalty savedCref uniformQuoteError unitRoleUnused .complete) adverseCompleteS18Before 7 [.query 1] (.hydeRetriever 1)
    (by decide) (by decide) adverseCompleteS18Choice1
  have hnew := native_select_new_step budgetTape (7/5) (controlPenalty savedCref uniformQuoteError unitRoleUnused .complete) adverseCompleteS18Before 6 [.query 1,.hydeRetriever 1]
    [.selection 2,.selection 3] (.selection 2) (by decide) (by decide) (by decide) (by decide)
  have hs : nativeSelect budgetTape (7/5) (controlPenalty savedCref uniformQuoteError unitRoleUnused .complete) adverseCompleteS18Before 9 [] = [.query 1,.hydeRetriever 1,.selection 2] := by
    rw [hs0]
    change nativeSelect budgetTape (7/5) (controlPenalty savedCref uniformQuoteError unitRoleUnused .complete) adverseCompleteS18Before 8 [.query 1] = _
    rw [hs1]
    change nativeSelect budgetTape (7/5) (controlPenalty savedCref uniformQuoteError unitRoleUnused .complete) adverseCompleteS18Before 7 [.query 1,.hydeRetriever 1] = _
    rw [hnew] <;> rfl
  have hr : repairedRollout budgetTape adverseCompleteS18Before 9 [.query 1,.hydeRetriever 1,.selection 2] = [.query 1,.hydeRetriever 1,.selection 2,.width 0,.stop,.reranker 0,.topm 0,.context 0,.answer 0] := by decide
  simp only [nativeEvent,hs,hr]
  rfl

def adverseCompleteS19Before := adverseCompleteProposal.take 18

theorem adverseCompleteS19Choice0 : nativeFirstChoice (indexScore (7/5) (controlPenalty savedCref uniformQuoteError unitRoleUnused .complete) adverseCompleteS19Before []) adverseCompleteS19Before [] = .query 1 := by
  apply complete_root_from_physical_gap adverseCompleteS19Before (adverseComplete_prefix_rewards 18) (by decide)
  · intro q; fin_cases q <;> decide
  · exact AgentUCTNextExact.adverse_complete_hyde_root_suffix_empty 18 (by omega)
  · intro q hq
    exact AgentUCTNextExact.adverse_complete_normal_root_physical_quote_exact 18 (by omega) q hq

theorem adverseCompleteS19D1I0 : indexScore (7/5) (controlPenalty savedCref uniformQuoteError unitRoleUnused .complete) adverseCompleteS19Before [.query 1] (.hydeRetriever 1) = treeIndex ((0/1)/4) (7/5) 0 11 4 := by
  have hs : replayBackup adverseCompleteS19Before emptyStatistics ([.query 1]++[.hydeRetriever 1]) = ⟨4,(0/1)⟩ := by
    rw [replayBackup_empty_closed_form]
    simp +decide [backedEvents,adverseCompleteS19Before,adverseCompleteProposal,adverseCompleteEvent1,adverseCompleteEvent2,adverseCompleteEvent3,adverseCompleteEvent4,adverseCompleteEvent5,adverseCompleteEvent6,adverseCompleteEvent7,adverseCompleteEvent8,adverseCompleteEvent9,adverseCompleteEvent10,adverseCompleteEvent11,adverseCompleteEvent12,adverseCompleteEvent13,adverseCompleteEvent14,adverseCompleteEvent15,adverseCompleteEvent16,adverseCompleteEvent17,adverseCompleteEvent18,taskReward]
    <;> norm_num
  have hp : rawVisits adverseCompleteS19Before [.query 1] = 11 := by decide
  have hn : rawVisits adverseCompleteS19Before ([.query 1]++[.hydeRetriever 1]) = 4 := by decide
  have hz : (controlPenalty savedCref uniformQuoteError unitRoleUnused .complete) adverseCompleteS19Before [.query 1] (.hydeRetriever 1) = 0 := by
    apply control_penalty_empty_of_prior_terminal .complete savedCref uniformQuoteError adverseCompleteS19Before [.query 1] (.hydeRetriever 1) 8 (by decide)
    · decide
    · decide
  unfold indexScore
  rw [hs,hp,hn,hz]
  simp only [BackupStat.mean]
  norm_num

theorem adverseCompleteS19D1I1 : indexScore (7/5) (controlPenalty savedCref uniformQuoteError unitRoleUnused .complete) adverseCompleteS19Before [.query 1] (.hydeRetriever 0) = treeIndex ((0/1)/3) (7/5) 0 11 3 := by
  have hs : replayBackup adverseCompleteS19Before emptyStatistics ([.query 1]++[.hydeRetriever 0]) = ⟨3,(0/1)⟩ := by
    rw [replayBackup_empty_closed_form]
    simp +decide [backedEvents,adverseCompleteS19Before,adverseCompleteProposal,adverseCompleteEvent1,adverseCompleteEvent2,adverseCompleteEvent3,adverseCompleteEvent4,adverseCompleteEvent5,adverseCompleteEvent6,adverseCompleteEvent7,adverseCompleteEvent8,adverseCompleteEvent9,adverseCompleteEvent10,adverseCompleteEvent11,adverseCompleteEvent12,adverseCompleteEvent13,adverseCompleteEvent14,adverseCompleteEvent15,adverseCompleteEvent16,adverseCompleteEvent17,adverseCompleteEvent18,taskReward]
    <;> norm_num
  have hp : rawVisits adverseCompleteS19Before [.query 1] = 11 := by decide
  have hn : rawVisits adverseCompleteS19Before ([.query 1]++[.hydeRetriever 0]) = 3 := by decide
  have hz : (controlPenalty savedCref uniformQuoteError unitRoleUnused .complete) adverseCompleteS19Before [.query 1] (.hydeRetriever 0) = 0 := by
    apply control_penalty_empty_of_prior_terminal .complete savedCref uniformQuoteError adverseCompleteS19Before [.query 1] (.hydeRetriever 0) 1 (by decide)
    · decide
    · decide
  unfold indexScore
  rw [hs,hp,hn,hz]
  simp only [BackupStat.mean]
  norm_num

theorem adverseCompleteS19D1I2 : indexScore (7/5) (controlPenalty savedCref uniformQuoteError unitRoleUnused .complete) adverseCompleteS19Before [.query 1] (.hydeRetriever 2) = treeIndex ((0/1)/3) (7/5) 0 11 3 := by
  have hs : replayBackup adverseCompleteS19Before emptyStatistics ([.query 1]++[.hydeRetriever 2]) = ⟨3,(0/1)⟩ := by
    rw [replayBackup_empty_closed_form]
    simp +decide [backedEvents,adverseCompleteS19Before,adverseCompleteProposal,adverseCompleteEvent1,adverseCompleteEvent2,adverseCompleteEvent3,adverseCompleteEvent4,adverseCompleteEvent5,adverseCompleteEvent6,adverseCompleteEvent7,adverseCompleteEvent8,adverseCompleteEvent9,adverseCompleteEvent10,adverseCompleteEvent11,adverseCompleteEvent12,adverseCompleteEvent13,adverseCompleteEvent14,adverseCompleteEvent15,adverseCompleteEvent16,adverseCompleteEvent17,adverseCompleteEvent18,taskReward]
    <;> norm_num
  have hp : rawVisits adverseCompleteS19Before [.query 1] = 11 := by decide
  have hn : rawVisits adverseCompleteS19Before ([.query 1]++[.hydeRetriever 2]) = 3 := by decide
  have hz : (controlPenalty savedCref uniformQuoteError unitRoleUnused .complete) adverseCompleteS19Before [.query 1] (.hydeRetriever 2) = 0 := by
    apply control_penalty_empty_of_prior_terminal .complete savedCref uniformQuoteError adverseCompleteS19Before [.query 1] (.hydeRetriever 2) 10 (by decide)
    · decide
    · decide
  unfold indexScore
  rw [hs,hp,hn,hz]
  simp only [BackupStat.mean]
  norm_num

theorem adverseCompleteS19D1Cmp0 : indexScore (7/5) (controlPenalty savedCref uniformQuoteError unitRoleUnused .complete) adverseCompleteS19Before [.query 1] (.hydeRetriever 1) < indexScore (7/5) (controlPenalty savedCref uniformQuoteError unitRoleUnused .complete) adverseCompleteS19Before [.query 1] (.hydeRetriever 0) := by
  rw [adverseCompleteS19D1I0,adverseCompleteS19D1I1]
  have h := index_strict_order_from_intervals ((0/1)/3) ((0/1)/4) 0 0 (6370777/5000000) (27586279/25000000)
    (treeBonus (7/5) 11 3) (treeBonus (7/5) 11 4)
    (trajectory_bonus_11_3).1 (trajectory_bonus_11_4).2 (by norm_num)
  simpa only [treeIndex,sub_zero] using h

theorem adverseCompleteS19D1Cmp2 : indexScore (7/5) (controlPenalty savedCref uniformQuoteError unitRoleUnused .complete) adverseCompleteS19Before [.query 1] (.hydeRetriever 2) ≤ indexScore (7/5) (controlPenalty savedCref uniformQuoteError unitRoleUnused .complete) adverseCompleteS19Before [.query 1] (.hydeRetriever 0) := by
  rw [adverseCompleteS19D1I2,adverseCompleteS19D1I1]

theorem adverseCompleteS19Choice1 : nativeFirstChoice (indexScore (7/5) (controlPenalty savedCref uniformQuoteError unitRoleUnused .complete) adverseCompleteS19Before [.query 1]) adverseCompleteS19Before [.query 1] = .hydeRetriever 0 := by
  apply visited_choice_from_ordered_certificate _ _ [.query 1] [.hydeRetriever 1] [.hydeRetriever 2] (.hydeRetriever 0) (by decide)
  · intro a ha
    have ho : orderedLegalAvailable [.query 1] = [.hydeRetriever 1,.hydeRetriever 0,.hydeRetriever 2] := by decide
    rw [ho] at ha
    simp only [List.mem_cons,List.not_mem_nil,or_false] at ha
    rcases ha with rfl | rfl | rfl <;> decide
  · intro a ha
    simp only [List.mem_cons,List.not_mem_nil,or_false] at ha
    rcases ha with rfl
    · exact adverseCompleteS19D1Cmp0
  · intro a ha
    simp only [List.mem_cons,List.not_mem_nil,or_false] at ha
    rcases ha with rfl
    · exact adverseCompleteS19D1Cmp2

theorem adverseCompleteS19ActualEvent : nativeEvent budgetTape (7/5) (controlPenalty savedCref uniformQuoteError unitRoleUnused .complete)
    (taskReward true (2/5) (1/2)) adverseCompleteS19Before = adverseCompleteEvent19 := by
  have hs0 := native_select_existing_step budgetTape (7/5) (controlPenalty savedCref uniformQuoteError unitRoleUnused .complete) adverseCompleteS19Before 8 [] (.query 1)
    (by decide) (by decide) adverseCompleteS19Choice0
  have hs1 := native_select_existing_step budgetTape (7/5) (controlPenalty savedCref uniformQuoteError unitRoleUnused .complete) adverseCompleteS19Before 7 [.query 1] (.hydeRetriever 0)
    (by decide) (by decide) adverseCompleteS19Choice1
  have hnew := native_select_new_step budgetTape (7/5) (controlPenalty savedCref uniformQuoteError unitRoleUnused .complete) adverseCompleteS19Before 6 [.query 1,.hydeRetriever 0]
    [.selection 2,.selection 3] (.selection 2) (by decide) (by decide) (by decide) (by decide)
  have hs : nativeSelect budgetTape (7/5) (controlPenalty savedCref uniformQuoteError unitRoleUnused .complete) adverseCompleteS19Before 9 [] = [.query 1,.hydeRetriever 0,.selection 2] := by
    rw [hs0]
    change nativeSelect budgetTape (7/5) (controlPenalty savedCref uniformQuoteError unitRoleUnused .complete) adverseCompleteS19Before 8 [.query 1] = _
    rw [hs1]
    change nativeSelect budgetTape (7/5) (controlPenalty savedCref uniformQuoteError unitRoleUnused .complete) adverseCompleteS19Before 7 [.query 1,.hydeRetriever 0] = _
    rw [hnew] <;> rfl
  have hr : repairedRollout budgetTape adverseCompleteS19Before 9 [.query 1,.hydeRetriever 0,.selection 2] = [.query 1,.hydeRetriever 0,.selection 2,.width 0,.stop,.reranker 0,.topm 0,.context 0,.answer 0] := by decide
  simp only [nativeEvent,hs,hr]
  rfl

end AgentUCT32MConcrete
