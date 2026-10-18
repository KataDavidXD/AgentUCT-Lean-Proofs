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

def adverseCompleteS28Before := adverseCompleteProposal.take 27

theorem adverseCompleteS28Choice0 : nativeFirstChoice (indexScore (7/5) (controlPenalty savedCref uniformQuoteError unitRoleUnused .complete) adverseCompleteS28Before []) adverseCompleteS28Before [] = .query 1 := by
  apply complete_root_from_physical_gap adverseCompleteS28Before (adverseComplete_prefix_rewards 27) (by decide)
  · intro q; fin_cases q <;> decide
  · exact AgentUCTNextExact.adverse_complete_hyde_root_suffix_empty 27 (by omega)
  · intro q hq
    exact AgentUCTNextExact.adverse_complete_normal_root_physical_quote_exact 27 (by omega) q hq

theorem adverseCompleteS28D1I0 : indexScore (7/5) (controlPenalty savedCref uniformQuoteError unitRoleUnused .complete) adverseCompleteS28Before [.query 1] (.hydeRetriever 1) = treeIndex ((0/1)/7) (7/5) 0 20 7 := by
  have hs : replayBackup adverseCompleteS28Before emptyStatistics ([.query 1]++[.hydeRetriever 1]) = ⟨7,(0/1)⟩ := by
    rw [replayBackup_empty_closed_form]
    simp +decide [backedEvents,adverseCompleteS28Before,adverseCompleteProposal,adverseCompleteEvent1,adverseCompleteEvent2,adverseCompleteEvent3,adverseCompleteEvent4,adverseCompleteEvent5,adverseCompleteEvent6,adverseCompleteEvent7,adverseCompleteEvent8,adverseCompleteEvent9,adverseCompleteEvent10,adverseCompleteEvent11,adverseCompleteEvent12,adverseCompleteEvent13,adverseCompleteEvent14,adverseCompleteEvent15,adverseCompleteEvent16,adverseCompleteEvent17,adverseCompleteEvent18,adverseCompleteEvent19,adverseCompleteEvent20,adverseCompleteEvent21,adverseCompleteEvent22,adverseCompleteEvent23,adverseCompleteEvent24,adverseCompleteEvent25,adverseCompleteEvent26,adverseCompleteEvent27,taskReward]
    <;> norm_num
  have hp : rawVisits adverseCompleteS28Before [.query 1] = 20 := by decide
  have hn : rawVisits adverseCompleteS28Before ([.query 1]++[.hydeRetriever 1]) = 7 := by decide
  have hz : (controlPenalty savedCref uniformQuoteError unitRoleUnused .complete) adverseCompleteS28Before [.query 1] (.hydeRetriever 1) = 0 := by
    apply control_penalty_empty_of_prior_terminal .complete savedCref uniformQuoteError adverseCompleteS28Before [.query 1] (.hydeRetriever 1) 8 (by decide)
    · decide
    · decide
  unfold indexScore
  rw [hs,hp,hn,hz]
  simp only [BackupStat.mean]
  norm_num

theorem adverseCompleteS28D1I1 : indexScore (7/5) (controlPenalty savedCref uniformQuoteError unitRoleUnused .complete) adverseCompleteS28Before [.query 1] (.hydeRetriever 0) = treeIndex ((0/1)/6) (7/5) 0 20 6 := by
  have hs : replayBackup adverseCompleteS28Before emptyStatistics ([.query 1]++[.hydeRetriever 0]) = ⟨6,(0/1)⟩ := by
    rw [replayBackup_empty_closed_form]
    simp +decide [backedEvents,adverseCompleteS28Before,adverseCompleteProposal,adverseCompleteEvent1,adverseCompleteEvent2,adverseCompleteEvent3,adverseCompleteEvent4,adverseCompleteEvent5,adverseCompleteEvent6,adverseCompleteEvent7,adverseCompleteEvent8,adverseCompleteEvent9,adverseCompleteEvent10,adverseCompleteEvent11,adverseCompleteEvent12,adverseCompleteEvent13,adverseCompleteEvent14,adverseCompleteEvent15,adverseCompleteEvent16,adverseCompleteEvent17,adverseCompleteEvent18,adverseCompleteEvent19,adverseCompleteEvent20,adverseCompleteEvent21,adverseCompleteEvent22,adverseCompleteEvent23,adverseCompleteEvent24,adverseCompleteEvent25,adverseCompleteEvent26,adverseCompleteEvent27,taskReward]
    <;> norm_num
  have hp : rawVisits adverseCompleteS28Before [.query 1] = 20 := by decide
  have hn : rawVisits adverseCompleteS28Before ([.query 1]++[.hydeRetriever 0]) = 6 := by decide
  have hz : (controlPenalty savedCref uniformQuoteError unitRoleUnused .complete) adverseCompleteS28Before [.query 1] (.hydeRetriever 0) = 0 := by
    apply control_penalty_empty_of_prior_terminal .complete savedCref uniformQuoteError adverseCompleteS28Before [.query 1] (.hydeRetriever 0) 1 (by decide)
    · decide
    · decide
  unfold indexScore
  rw [hs,hp,hn,hz]
  simp only [BackupStat.mean]
  norm_num

theorem adverseCompleteS28D1I2 : indexScore (7/5) (controlPenalty savedCref uniformQuoteError unitRoleUnused .complete) adverseCompleteS28Before [.query 1] (.hydeRetriever 2) = treeIndex ((0/1)/6) (7/5) 0 20 6 := by
  have hs : replayBackup adverseCompleteS28Before emptyStatistics ([.query 1]++[.hydeRetriever 2]) = ⟨6,(0/1)⟩ := by
    rw [replayBackup_empty_closed_form]
    simp +decide [backedEvents,adverseCompleteS28Before,adverseCompleteProposal,adverseCompleteEvent1,adverseCompleteEvent2,adverseCompleteEvent3,adverseCompleteEvent4,adverseCompleteEvent5,adverseCompleteEvent6,adverseCompleteEvent7,adverseCompleteEvent8,adverseCompleteEvent9,adverseCompleteEvent10,adverseCompleteEvent11,adverseCompleteEvent12,adverseCompleteEvent13,adverseCompleteEvent14,adverseCompleteEvent15,adverseCompleteEvent16,adverseCompleteEvent17,adverseCompleteEvent18,adverseCompleteEvent19,adverseCompleteEvent20,adverseCompleteEvent21,adverseCompleteEvent22,adverseCompleteEvent23,adverseCompleteEvent24,adverseCompleteEvent25,adverseCompleteEvent26,adverseCompleteEvent27,taskReward]
    <;> norm_num
  have hp : rawVisits adverseCompleteS28Before [.query 1] = 20 := by decide
  have hn : rawVisits adverseCompleteS28Before ([.query 1]++[.hydeRetriever 2]) = 6 := by decide
  have hz : (controlPenalty savedCref uniformQuoteError unitRoleUnused .complete) adverseCompleteS28Before [.query 1] (.hydeRetriever 2) = 0 := by
    apply control_penalty_empty_of_prior_terminal .complete savedCref uniformQuoteError adverseCompleteS28Before [.query 1] (.hydeRetriever 2) 10 (by decide)
    · decide
    · decide
  unfold indexScore
  rw [hs,hp,hn,hz]
  simp only [BackupStat.mean]
  norm_num

theorem adverseCompleteS28D1Cmp0 : indexScore (7/5) (controlPenalty savedCref uniformQuoteError unitRoleUnused .complete) adverseCompleteS28Before [.query 1] (.hydeRetriever 1) < indexScore (7/5) (controlPenalty savedCref uniformQuoteError unitRoleUnused .complete) adverseCompleteS28Before [.query 1] (.hydeRetriever 0) := by
  rw [adverseCompleteS28D1I0,adverseCompleteS28D1I1]
  have h := index_strict_order_from_intervals ((0/1)/6) ((0/1)/7) 0 0 (3116463/3125000) (5770569/6250000)
    (treeBonus (7/5) 20 6) (treeBonus (7/5) 20 7)
    (trajectory_bonus_20_6).1 (trajectory_bonus_20_7).2 (by norm_num)
  simpa only [treeIndex,sub_zero] using h

theorem adverseCompleteS28D1Cmp2 : indexScore (7/5) (controlPenalty savedCref uniformQuoteError unitRoleUnused .complete) adverseCompleteS28Before [.query 1] (.hydeRetriever 2) ≤ indexScore (7/5) (controlPenalty savedCref uniformQuoteError unitRoleUnused .complete) adverseCompleteS28Before [.query 1] (.hydeRetriever 0) := by
  rw [adverseCompleteS28D1I2,adverseCompleteS28D1I1]

theorem adverseCompleteS28Choice1 : nativeFirstChoice (indexScore (7/5) (controlPenalty savedCref uniformQuoteError unitRoleUnused .complete) adverseCompleteS28Before [.query 1]) adverseCompleteS28Before [.query 1] = .hydeRetriever 0 := by
  apply visited_choice_from_ordered_certificate _ _ [.query 1] [.hydeRetriever 1] [.hydeRetriever 2] (.hydeRetriever 0) (by decide)
  · intro a ha
    have ho : orderedLegalAvailable [.query 1] = [.hydeRetriever 1,.hydeRetriever 0,.hydeRetriever 2] := by decide
    rw [ho] at ha
    simp only [List.mem_cons,List.not_mem_nil,or_false] at ha
    rcases ha with rfl | rfl | rfl <;> decide
  · intro a ha
    simp only [List.mem_cons,List.not_mem_nil,or_false] at ha
    rcases ha with rfl
    · exact adverseCompleteS28D1Cmp0
  · intro a ha
    simp only [List.mem_cons,List.not_mem_nil,or_false] at ha
    rcases ha with rfl
    · exact adverseCompleteS28D1Cmp2

theorem adverseCompleteS28D2I0 : indexScore (7/5) (controlPenalty savedCref uniformQuoteError unitRoleUnused .complete) adverseCompleteS28Before [.query 1,.hydeRetriever 0] (.selection 1) = treeIndex ((0/1)/2) (7/5) 0 6 2 := by
  have hs : replayBackup adverseCompleteS28Before emptyStatistics ([.query 1,.hydeRetriever 0]++[.selection 1]) = ⟨2,(0/1)⟩ := by
    rw [replayBackup_empty_closed_form]
    simp +decide [backedEvents,adverseCompleteS28Before,adverseCompleteProposal,adverseCompleteEvent1,adverseCompleteEvent2,adverseCompleteEvent3,adverseCompleteEvent4,adverseCompleteEvent5,adverseCompleteEvent6,adverseCompleteEvent7,adverseCompleteEvent8,adverseCompleteEvent9,adverseCompleteEvent10,adverseCompleteEvent11,adverseCompleteEvent12,adverseCompleteEvent13,adverseCompleteEvent14,adverseCompleteEvent15,adverseCompleteEvent16,adverseCompleteEvent17,adverseCompleteEvent18,adverseCompleteEvent19,adverseCompleteEvent20,adverseCompleteEvent21,adverseCompleteEvent22,adverseCompleteEvent23,adverseCompleteEvent24,adverseCompleteEvent25,adverseCompleteEvent26,adverseCompleteEvent27,taskReward]
    <;> norm_num
  have hp : rawVisits adverseCompleteS28Before [.query 1,.hydeRetriever 0] = 6 := by decide
  have hn : rawVisits adverseCompleteS28Before ([.query 1,.hydeRetriever 0]++[.selection 1]) = 2 := by decide
  have hz : (controlPenalty savedCref uniformQuoteError unitRoleUnused .complete) adverseCompleteS28Before [.query 1,.hydeRetriever 0] (.selection 1) = 0 := by
    apply control_penalty_empty_of_prior_terminal .complete savedCref uniformQuoteError adverseCompleteS28Before [.query 1,.hydeRetriever 0] (.selection 1) 15 (by decide)
    · decide
    · decide
  unfold indexScore
  rw [hs,hp,hn,hz]
  simp only [BackupStat.mean]
  norm_num

theorem adverseCompleteS28D2I1 : indexScore (7/5) (controlPenalty savedCref uniformQuoteError unitRoleUnused .complete) adverseCompleteS28Before [.query 1,.hydeRetriever 0] (.selection 2) = treeIndex ((0/1)/1) (7/5) 0 6 1 := by
  have hs : replayBackup adverseCompleteS28Before emptyStatistics ([.query 1,.hydeRetriever 0]++[.selection 2]) = ⟨1,(0/1)⟩ := by
    rw [replayBackup_empty_closed_form]
    simp +decide [backedEvents,adverseCompleteS28Before,adverseCompleteProposal,adverseCompleteEvent1,adverseCompleteEvent2,adverseCompleteEvent3,adverseCompleteEvent4,adverseCompleteEvent5,adverseCompleteEvent6,adverseCompleteEvent7,adverseCompleteEvent8,adverseCompleteEvent9,adverseCompleteEvent10,adverseCompleteEvent11,adverseCompleteEvent12,adverseCompleteEvent13,adverseCompleteEvent14,adverseCompleteEvent15,adverseCompleteEvent16,adverseCompleteEvent17,adverseCompleteEvent18,adverseCompleteEvent19,adverseCompleteEvent20,adverseCompleteEvent21,adverseCompleteEvent22,adverseCompleteEvent23,adverseCompleteEvent24,adverseCompleteEvent25,adverseCompleteEvent26,adverseCompleteEvent27,taskReward]
    <;> norm_num
  have hp : rawVisits adverseCompleteS28Before [.query 1,.hydeRetriever 0] = 6 := by decide
  have hn : rawVisits adverseCompleteS28Before ([.query 1,.hydeRetriever 0]++[.selection 2]) = 1 := by decide
  have hz : (controlPenalty savedCref uniformQuoteError unitRoleUnused .complete) adverseCompleteS28Before [.query 1,.hydeRetriever 0] (.selection 2) = 0 := by
    apply control_penalty_empty_of_prior_terminal .complete savedCref uniformQuoteError adverseCompleteS28Before [.query 1,.hydeRetriever 0] (.selection 2) 18 (by decide)
    · decide
    · decide
  unfold indexScore
  rw [hs,hp,hn,hz]
  simp only [BackupStat.mean]
  norm_num

theorem adverseCompleteS28D2I2 : indexScore (7/5) (controlPenalty savedCref uniformQuoteError unitRoleUnused .complete) adverseCompleteS28Before [.query 1,.hydeRetriever 0] (.selection 3) = treeIndex ((0/1)/1) (7/5) 0 6 1 := by
  have hs : replayBackup adverseCompleteS28Before emptyStatistics ([.query 1,.hydeRetriever 0]++[.selection 3]) = ⟨1,(0/1)⟩ := by
    rw [replayBackup_empty_closed_form]
    simp +decide [backedEvents,adverseCompleteS28Before,adverseCompleteProposal,adverseCompleteEvent1,adverseCompleteEvent2,adverseCompleteEvent3,adverseCompleteEvent4,adverseCompleteEvent5,adverseCompleteEvent6,adverseCompleteEvent7,adverseCompleteEvent8,adverseCompleteEvent9,adverseCompleteEvent10,adverseCompleteEvent11,adverseCompleteEvent12,adverseCompleteEvent13,adverseCompleteEvent14,adverseCompleteEvent15,adverseCompleteEvent16,adverseCompleteEvent17,adverseCompleteEvent18,adverseCompleteEvent19,adverseCompleteEvent20,adverseCompleteEvent21,adverseCompleteEvent22,adverseCompleteEvent23,adverseCompleteEvent24,adverseCompleteEvent25,adverseCompleteEvent26,adverseCompleteEvent27,taskReward]
    <;> norm_num
  have hp : rawVisits adverseCompleteS28Before [.query 1,.hydeRetriever 0] = 6 := by decide
  have hn : rawVisits adverseCompleteS28Before ([.query 1,.hydeRetriever 0]++[.selection 3]) = 1 := by decide
  have hz : (controlPenalty savedCref uniformQuoteError unitRoleUnused .complete) adverseCompleteS28Before [.query 1,.hydeRetriever 0] (.selection 3) = 0 := by
    apply control_penalty_empty_of_prior_terminal .complete savedCref uniformQuoteError adverseCompleteS28Before [.query 1,.hydeRetriever 0] (.selection 3) 21 (by decide)
    · decide
    · decide
  unfold indexScore
  rw [hs,hp,hn,hz]
  simp only [BackupStat.mean]
  norm_num

theorem adverseCompleteS28D2I3 : indexScore (7/5) (controlPenalty savedCref uniformQuoteError unitRoleUnused .complete) adverseCompleteS28Before [.query 1,.hydeRetriever 0] (.selection 0) = treeIndex ((0/1)/1) (7/5) 0 6 1 := by
  have hs : replayBackup adverseCompleteS28Before emptyStatistics ([.query 1,.hydeRetriever 0]++[.selection 0]) = ⟨1,(0/1)⟩ := by
    rw [replayBackup_empty_closed_form]
    simp +decide [backedEvents,adverseCompleteS28Before,adverseCompleteProposal,adverseCompleteEvent1,adverseCompleteEvent2,adverseCompleteEvent3,adverseCompleteEvent4,adverseCompleteEvent5,adverseCompleteEvent6,adverseCompleteEvent7,adverseCompleteEvent8,adverseCompleteEvent9,adverseCompleteEvent10,adverseCompleteEvent11,adverseCompleteEvent12,adverseCompleteEvent13,adverseCompleteEvent14,adverseCompleteEvent15,adverseCompleteEvent16,adverseCompleteEvent17,adverseCompleteEvent18,adverseCompleteEvent19,adverseCompleteEvent20,adverseCompleteEvent21,adverseCompleteEvent22,adverseCompleteEvent23,adverseCompleteEvent24,adverseCompleteEvent25,adverseCompleteEvent26,adverseCompleteEvent27,taskReward]
    <;> norm_num
  have hp : rawVisits adverseCompleteS28Before [.query 1,.hydeRetriever 0] = 6 := by decide
  have hn : rawVisits adverseCompleteS28Before ([.query 1,.hydeRetriever 0]++[.selection 0]) = 1 := by decide
  have hz : (controlPenalty savedCref uniformQuoteError unitRoleUnused .complete) adverseCompleteS28Before [.query 1,.hydeRetriever 0] (.selection 0) = 0 := by
    apply control_penalty_empty_of_prior_terminal .complete savedCref uniformQuoteError adverseCompleteS28Before [.query 1,.hydeRetriever 0] (.selection 0) 1 (by decide)
    · decide
    · decide
  unfold indexScore
  rw [hs,hp,hn,hz]
  simp only [BackupStat.mean]
  norm_num

theorem adverseCompleteS28D2Cmp0 : indexScore (7/5) (controlPenalty savedCref uniformQuoteError unitRoleUnused .complete) adverseCompleteS28Before [.query 1,.hydeRetriever 0] (.selection 1) < indexScore (7/5) (controlPenalty savedCref uniformQuoteError unitRoleUnused .complete) adverseCompleteS28Before [.query 1,.hydeRetriever 0] (.selection 2) := by
  rw [adverseCompleteS28D2I0,adverseCompleteS28D2I1]
  have h := index_strict_order_from_intervals ((0/1)/1) ((0/1)/2) 0 0 (24411779/12500000) (69046943/50000000)
    (treeBonus (7/5) 6 1) (treeBonus (7/5) 6 2)
    (trajectory_bonus_6_1).1 (trajectory_bonus_6_2).2 (by norm_num)
  simpa only [treeIndex,sub_zero] using h

theorem adverseCompleteS28D2Cmp2 : indexScore (7/5) (controlPenalty savedCref uniformQuoteError unitRoleUnused .complete) adverseCompleteS28Before [.query 1,.hydeRetriever 0] (.selection 3) ≤ indexScore (7/5) (controlPenalty savedCref uniformQuoteError unitRoleUnused .complete) adverseCompleteS28Before [.query 1,.hydeRetriever 0] (.selection 2) := by
  rw [adverseCompleteS28D2I2,adverseCompleteS28D2I1]

theorem adverseCompleteS28D2Cmp3 : indexScore (7/5) (controlPenalty savedCref uniformQuoteError unitRoleUnused .complete) adverseCompleteS28Before [.query 1,.hydeRetriever 0] (.selection 0) ≤ indexScore (7/5) (controlPenalty savedCref uniformQuoteError unitRoleUnused .complete) adverseCompleteS28Before [.query 1,.hydeRetriever 0] (.selection 2) := by
  rw [adverseCompleteS28D2I3,adverseCompleteS28D2I1]

theorem adverseCompleteS28Choice2 : nativeFirstChoice (indexScore (7/5) (controlPenalty savedCref uniformQuoteError unitRoleUnused .complete) adverseCompleteS28Before [.query 1,.hydeRetriever 0]) adverseCompleteS28Before [.query 1,.hydeRetriever 0] = .selection 2 := by
  apply visited_choice_from_ordered_certificate _ _ [.query 1,.hydeRetriever 0] [.selection 1] [.selection 3,.selection 0] (.selection 2) (by decide)
  · intro a ha
    have ho : orderedLegalAvailable [.query 1,.hydeRetriever 0] = [.selection 1,.selection 2,.selection 3,.selection 0] := by decide
    rw [ho] at ha
    simp only [List.mem_cons,List.not_mem_nil,or_false] at ha
    rcases ha with rfl | rfl | rfl | rfl <;> decide
  · intro a ha
    simp only [List.mem_cons,List.not_mem_nil,or_false] at ha
    rcases ha with rfl
    · exact adverseCompleteS28D2Cmp0
  · intro a ha
    simp only [List.mem_cons,List.not_mem_nil,or_false] at ha
    rcases ha with rfl | rfl
    · exact adverseCompleteS28D2Cmp2
    · exact adverseCompleteS28D2Cmp3

theorem adverseCompleteS28ActualEvent : nativeEvent budgetTape (7/5) (controlPenalty savedCref uniformQuoteError unitRoleUnused .complete)
    (taskReward true (2/5) (1/2)) adverseCompleteS28Before = adverseCompleteEvent28 := by
  have hs0 := native_select_existing_step budgetTape (7/5) (controlPenalty savedCref uniformQuoteError unitRoleUnused .complete) adverseCompleteS28Before 8 [] (.query 1)
    (by decide) (by decide) adverseCompleteS28Choice0
  have hs1 := native_select_existing_step budgetTape (7/5) (controlPenalty savedCref uniformQuoteError unitRoleUnused .complete) adverseCompleteS28Before 7 [.query 1] (.hydeRetriever 0)
    (by decide) (by decide) adverseCompleteS28Choice1
  have hs2 := native_select_existing_step budgetTape (7/5) (controlPenalty savedCref uniformQuoteError unitRoleUnused .complete) adverseCompleteS28Before 6 [.query 1,.hydeRetriever 0] (.selection 2)
    (by decide) (by decide) adverseCompleteS28Choice2
  have hnew := native_select_new_step budgetTape (7/5) (controlPenalty savedCref uniformQuoteError unitRoleUnused .complete) adverseCompleteS28Before 5 [.query 1,.hydeRetriever 0,.selection 2]
    [.width 3,.width 0,.width 1,.width 2] (.width 0) (by decide) (by decide) (by decide) (by decide)
  have hs : nativeSelect budgetTape (7/5) (controlPenalty savedCref uniformQuoteError unitRoleUnused .complete) adverseCompleteS28Before 9 [] = [.query 1,.hydeRetriever 0,.selection 2,.width 0] := by
    rw [hs0]
    change nativeSelect budgetTape (7/5) (controlPenalty savedCref uniformQuoteError unitRoleUnused .complete) adverseCompleteS28Before 8 [.query 1] = _
    rw [hs1]
    change nativeSelect budgetTape (7/5) (controlPenalty savedCref uniformQuoteError unitRoleUnused .complete) adverseCompleteS28Before 7 [.query 1,.hydeRetriever 0] = _
    rw [hs2]
    change nativeSelect budgetTape (7/5) (controlPenalty savedCref uniformQuoteError unitRoleUnused .complete) adverseCompleteS28Before 6 [.query 1,.hydeRetriever 0,.selection 2] = _
    rw [hnew] <;> rfl
  have hr : repairedRollout budgetTape adverseCompleteS28Before 9 [.query 1,.hydeRetriever 0,.selection 2,.width 0] = [.query 1,.hydeRetriever 0,.selection 2,.width 0,.stop,.reranker 0,.topm 0,.context 0,.answer 0] := by decide
  simp only [nativeEvent,hs,hr]
  rfl

def adverseCompleteS29Before := adverseCompleteProposal.take 28

theorem adverseCompleteS29Choice0 : nativeFirstChoice (indexScore (7/5) (controlPenalty savedCref uniformQuoteError unitRoleUnused .complete) adverseCompleteS29Before []) adverseCompleteS29Before [] = .query 1 := by
  apply complete_root_from_physical_gap adverseCompleteS29Before (adverseComplete_prefix_rewards 28) (by decide)
  · intro q; fin_cases q <;> decide
  · exact AgentUCTNextExact.adverse_complete_hyde_root_suffix_empty 28 (by omega)
  · intro q hq
    exact AgentUCTNextExact.adverse_complete_normal_root_physical_quote_exact 28 (by omega) q hq

theorem adverseCompleteS29D1I0 : indexScore (7/5) (controlPenalty savedCref uniformQuoteError unitRoleUnused .complete) adverseCompleteS29Before [.query 1] (.hydeRetriever 1) = treeIndex ((0/1)/7) (7/5) 0 21 7 := by
  have hs : replayBackup adverseCompleteS29Before emptyStatistics ([.query 1]++[.hydeRetriever 1]) = ⟨7,(0/1)⟩ := by
    rw [replayBackup_empty_closed_form]
    simp +decide [backedEvents,adverseCompleteS29Before,adverseCompleteProposal,adverseCompleteEvent1,adverseCompleteEvent2,adverseCompleteEvent3,adverseCompleteEvent4,adverseCompleteEvent5,adverseCompleteEvent6,adverseCompleteEvent7,adverseCompleteEvent8,adverseCompleteEvent9,adverseCompleteEvent10,adverseCompleteEvent11,adverseCompleteEvent12,adverseCompleteEvent13,adverseCompleteEvent14,adverseCompleteEvent15,adverseCompleteEvent16,adverseCompleteEvent17,adverseCompleteEvent18,adverseCompleteEvent19,adverseCompleteEvent20,adverseCompleteEvent21,adverseCompleteEvent22,adverseCompleteEvent23,adverseCompleteEvent24,adverseCompleteEvent25,adverseCompleteEvent26,adverseCompleteEvent27,adverseCompleteEvent28,taskReward]
    <;> norm_num
  have hp : rawVisits adverseCompleteS29Before [.query 1] = 21 := by decide
  have hn : rawVisits adverseCompleteS29Before ([.query 1]++[.hydeRetriever 1]) = 7 := by decide
  have hz : (controlPenalty savedCref uniformQuoteError unitRoleUnused .complete) adverseCompleteS29Before [.query 1] (.hydeRetriever 1) = 0 := by
    apply control_penalty_empty_of_prior_terminal .complete savedCref uniformQuoteError adverseCompleteS29Before [.query 1] (.hydeRetriever 1) 8 (by decide)
    · decide
    · decide
  unfold indexScore
  rw [hs,hp,hn,hz]
  simp only [BackupStat.mean]
  norm_num

theorem adverseCompleteS29D1I1 : indexScore (7/5) (controlPenalty savedCref uniformQuoteError unitRoleUnused .complete) adverseCompleteS29Before [.query 1] (.hydeRetriever 0) = treeIndex ((0/1)/7) (7/5) 0 21 7 := by
  have hs : replayBackup adverseCompleteS29Before emptyStatistics ([.query 1]++[.hydeRetriever 0]) = ⟨7,(0/1)⟩ := by
    rw [replayBackup_empty_closed_form]
    simp +decide [backedEvents,adverseCompleteS29Before,adverseCompleteProposal,adverseCompleteEvent1,adverseCompleteEvent2,adverseCompleteEvent3,adverseCompleteEvent4,adverseCompleteEvent5,adverseCompleteEvent6,adverseCompleteEvent7,adverseCompleteEvent8,adverseCompleteEvent9,adverseCompleteEvent10,adverseCompleteEvent11,adverseCompleteEvent12,adverseCompleteEvent13,adverseCompleteEvent14,adverseCompleteEvent15,adverseCompleteEvent16,adverseCompleteEvent17,adverseCompleteEvent18,adverseCompleteEvent19,adverseCompleteEvent20,adverseCompleteEvent21,adverseCompleteEvent22,adverseCompleteEvent23,adverseCompleteEvent24,adverseCompleteEvent25,adverseCompleteEvent26,adverseCompleteEvent27,adverseCompleteEvent28,taskReward]
    <;> norm_num
  have hp : rawVisits adverseCompleteS29Before [.query 1] = 21 := by decide
  have hn : rawVisits adverseCompleteS29Before ([.query 1]++[.hydeRetriever 0]) = 7 := by decide
  have hz : (controlPenalty savedCref uniformQuoteError unitRoleUnused .complete) adverseCompleteS29Before [.query 1] (.hydeRetriever 0) = 0 := by
    apply control_penalty_empty_of_prior_terminal .complete savedCref uniformQuoteError adverseCompleteS29Before [.query 1] (.hydeRetriever 0) 1 (by decide)
    · decide
    · decide
  unfold indexScore
  rw [hs,hp,hn,hz]
  simp only [BackupStat.mean]
  norm_num

theorem adverseCompleteS29D1I2 : indexScore (7/5) (controlPenalty savedCref uniformQuoteError unitRoleUnused .complete) adverseCompleteS29Before [.query 1] (.hydeRetriever 2) = treeIndex ((0/1)/6) (7/5) 0 21 6 := by
  have hs : replayBackup adverseCompleteS29Before emptyStatistics ([.query 1]++[.hydeRetriever 2]) = ⟨6,(0/1)⟩ := by
    rw [replayBackup_empty_closed_form]
    simp +decide [backedEvents,adverseCompleteS29Before,adverseCompleteProposal,adverseCompleteEvent1,adverseCompleteEvent2,adverseCompleteEvent3,adverseCompleteEvent4,adverseCompleteEvent5,adverseCompleteEvent6,adverseCompleteEvent7,adverseCompleteEvent8,adverseCompleteEvent9,adverseCompleteEvent10,adverseCompleteEvent11,adverseCompleteEvent12,adverseCompleteEvent13,adverseCompleteEvent14,adverseCompleteEvent15,adverseCompleteEvent16,adverseCompleteEvent17,adverseCompleteEvent18,adverseCompleteEvent19,adverseCompleteEvent20,adverseCompleteEvent21,adverseCompleteEvent22,adverseCompleteEvent23,adverseCompleteEvent24,adverseCompleteEvent25,adverseCompleteEvent26,adverseCompleteEvent27,adverseCompleteEvent28,taskReward]
    <;> norm_num
  have hp : rawVisits adverseCompleteS29Before [.query 1] = 21 := by decide
  have hn : rawVisits adverseCompleteS29Before ([.query 1]++[.hydeRetriever 2]) = 6 := by decide
  have hz : (controlPenalty savedCref uniformQuoteError unitRoleUnused .complete) adverseCompleteS29Before [.query 1] (.hydeRetriever 2) = 0 := by
    apply control_penalty_empty_of_prior_terminal .complete savedCref uniformQuoteError adverseCompleteS29Before [.query 1] (.hydeRetriever 2) 10 (by decide)
    · decide
    · decide
  unfold indexScore
  rw [hs,hp,hn,hz]
  simp only [BackupStat.mean]
  norm_num

theorem adverseCompleteS29D1Cmp0 : indexScore (7/5) (controlPenalty savedCref uniformQuoteError unitRoleUnused .complete) adverseCompleteS29Before [.query 1] (.hydeRetriever 1) < indexScore (7/5) (controlPenalty savedCref uniformQuoteError unitRoleUnused .complete) adverseCompleteS29Before [.query 1] (.hydeRetriever 2) := by
  rw [adverseCompleteS29D1I0,adverseCompleteS29D1I2]
  have h := index_strict_order_from_intervals ((0/1)/6) ((0/1)/7) 0 0 (1256073/1250000) (4651591/5000000)
    (treeBonus (7/5) 21 6) (treeBonus (7/5) 21 7)
    (trajectory_bonus_21_6).1 (trajectory_bonus_21_7).2 (by norm_num)
  simpa only [treeIndex,sub_zero] using h

theorem adverseCompleteS29D1Cmp1 : indexScore (7/5) (controlPenalty savedCref uniformQuoteError unitRoleUnused .complete) adverseCompleteS29Before [.query 1] (.hydeRetriever 0) < indexScore (7/5) (controlPenalty savedCref uniformQuoteError unitRoleUnused .complete) adverseCompleteS29Before [.query 1] (.hydeRetriever 2) := by
  rw [adverseCompleteS29D1I1,adverseCompleteS29D1I2]
  have h := index_strict_order_from_intervals ((0/1)/6) ((0/1)/7) 0 0 (1256073/1250000) (4651591/5000000)
    (treeBonus (7/5) 21 6) (treeBonus (7/5) 21 7)
    (trajectory_bonus_21_6).1 (trajectory_bonus_21_7).2 (by norm_num)
  simpa only [treeIndex,sub_zero] using h

theorem adverseCompleteS29Choice1 : nativeFirstChoice (indexScore (7/5) (controlPenalty savedCref uniformQuoteError unitRoleUnused .complete) adverseCompleteS29Before [.query 1]) adverseCompleteS29Before [.query 1] = .hydeRetriever 2 := by
  apply visited_choice_from_ordered_certificate _ _ [.query 1] [.hydeRetriever 1,.hydeRetriever 0] [] (.hydeRetriever 2) (by decide)
  · intro a ha
    have ho : orderedLegalAvailable [.query 1] = [.hydeRetriever 1,.hydeRetriever 0,.hydeRetriever 2] := by decide
    rw [ho] at ha
    simp only [List.mem_cons,List.not_mem_nil,or_false] at ha
    rcases ha with rfl | rfl | rfl <;> decide
  · intro a ha
    simp only [List.mem_cons,List.not_mem_nil,or_false] at ha
    rcases ha with rfl | rfl
    · exact adverseCompleteS29D1Cmp0
    · exact adverseCompleteS29D1Cmp1
  · simp

theorem adverseCompleteS29D2I0 : indexScore (7/5) (controlPenalty savedCref uniformQuoteError unitRoleUnused .complete) adverseCompleteS29Before [.query 1,.hydeRetriever 2] (.selection 1) = treeIndex ((0/1)/2) (7/5) 0 6 2 := by
  have hs : replayBackup adverseCompleteS29Before emptyStatistics ([.query 1,.hydeRetriever 2]++[.selection 1]) = ⟨2,(0/1)⟩ := by
    rw [replayBackup_empty_closed_form]
    simp +decide [backedEvents,adverseCompleteS29Before,adverseCompleteProposal,adverseCompleteEvent1,adverseCompleteEvent2,adverseCompleteEvent3,adverseCompleteEvent4,adverseCompleteEvent5,adverseCompleteEvent6,adverseCompleteEvent7,adverseCompleteEvent8,adverseCompleteEvent9,adverseCompleteEvent10,adverseCompleteEvent11,adverseCompleteEvent12,adverseCompleteEvent13,adverseCompleteEvent14,adverseCompleteEvent15,adverseCompleteEvent16,adverseCompleteEvent17,adverseCompleteEvent18,adverseCompleteEvent19,adverseCompleteEvent20,adverseCompleteEvent21,adverseCompleteEvent22,adverseCompleteEvent23,adverseCompleteEvent24,adverseCompleteEvent25,adverseCompleteEvent26,adverseCompleteEvent27,adverseCompleteEvent28,taskReward]
    <;> norm_num
  have hp : rawVisits adverseCompleteS29Before [.query 1,.hydeRetriever 2] = 6 := by decide
  have hn : rawVisits adverseCompleteS29Before ([.query 1,.hydeRetriever 2]++[.selection 1]) = 2 := by decide
  have hz : (controlPenalty savedCref uniformQuoteError unitRoleUnused .complete) adverseCompleteS29Before [.query 1,.hydeRetriever 2] (.selection 1) = 0 := by
    apply control_penalty_empty_of_prior_terminal .complete savedCref uniformQuoteError adverseCompleteS29Before [.query 1,.hydeRetriever 2] (.selection 1) 16 (by decide)
    · decide
    · decide
  unfold indexScore
  rw [hs,hp,hn,hz]
  simp only [BackupStat.mean]
  norm_num

theorem adverseCompleteS29D2I1 : indexScore (7/5) (controlPenalty savedCref uniformQuoteError unitRoleUnused .complete) adverseCompleteS29Before [.query 1,.hydeRetriever 2] (.selection 2) = treeIndex ((0/1)/1) (7/5) 0 6 1 := by
  have hs : replayBackup adverseCompleteS29Before emptyStatistics ([.query 1,.hydeRetriever 2]++[.selection 2]) = ⟨1,(0/1)⟩ := by
    rw [replayBackup_empty_closed_form]
    simp +decide [backedEvents,adverseCompleteS29Before,adverseCompleteProposal,adverseCompleteEvent1,adverseCompleteEvent2,adverseCompleteEvent3,adverseCompleteEvent4,adverseCompleteEvent5,adverseCompleteEvent6,adverseCompleteEvent7,adverseCompleteEvent8,adverseCompleteEvent9,adverseCompleteEvent10,adverseCompleteEvent11,adverseCompleteEvent12,adverseCompleteEvent13,adverseCompleteEvent14,adverseCompleteEvent15,adverseCompleteEvent16,adverseCompleteEvent17,adverseCompleteEvent18,adverseCompleteEvent19,adverseCompleteEvent20,adverseCompleteEvent21,adverseCompleteEvent22,adverseCompleteEvent23,adverseCompleteEvent24,adverseCompleteEvent25,adverseCompleteEvent26,adverseCompleteEvent27,adverseCompleteEvent28,taskReward]
    <;> norm_num
  have hp : rawVisits adverseCompleteS29Before [.query 1,.hydeRetriever 2] = 6 := by decide
  have hn : rawVisits adverseCompleteS29Before ([.query 1,.hydeRetriever 2]++[.selection 2]) = 1 := by decide
  have hz : (controlPenalty savedCref uniformQuoteError unitRoleUnused .complete) adverseCompleteS29Before [.query 1,.hydeRetriever 2] (.selection 2) = 0 := by
    apply control_penalty_empty_of_prior_terminal .complete savedCref uniformQuoteError adverseCompleteS29Before [.query 1,.hydeRetriever 2] (.selection 2) 19 (by decide)
    · decide
    · decide
  unfold indexScore
  rw [hs,hp,hn,hz]
  simp only [BackupStat.mean]
  norm_num

theorem adverseCompleteS29D2I2 : indexScore (7/5) (controlPenalty savedCref uniformQuoteError unitRoleUnused .complete) adverseCompleteS29Before [.query 1,.hydeRetriever 2] (.selection 3) = treeIndex ((0/1)/1) (7/5) 0 6 1 := by
  have hs : replayBackup adverseCompleteS29Before emptyStatistics ([.query 1,.hydeRetriever 2]++[.selection 3]) = ⟨1,(0/1)⟩ := by
    rw [replayBackup_empty_closed_form]
    simp +decide [backedEvents,adverseCompleteS29Before,adverseCompleteProposal,adverseCompleteEvent1,adverseCompleteEvent2,adverseCompleteEvent3,adverseCompleteEvent4,adverseCompleteEvent5,adverseCompleteEvent6,adverseCompleteEvent7,adverseCompleteEvent8,adverseCompleteEvent9,adverseCompleteEvent10,adverseCompleteEvent11,adverseCompleteEvent12,adverseCompleteEvent13,adverseCompleteEvent14,adverseCompleteEvent15,adverseCompleteEvent16,adverseCompleteEvent17,adverseCompleteEvent18,adverseCompleteEvent19,adverseCompleteEvent20,adverseCompleteEvent21,adverseCompleteEvent22,adverseCompleteEvent23,adverseCompleteEvent24,adverseCompleteEvent25,adverseCompleteEvent26,adverseCompleteEvent27,adverseCompleteEvent28,taskReward]
    <;> norm_num
  have hp : rawVisits adverseCompleteS29Before [.query 1,.hydeRetriever 2] = 6 := by decide
  have hn : rawVisits adverseCompleteS29Before ([.query 1,.hydeRetriever 2]++[.selection 3]) = 1 := by decide
  have hz : (controlPenalty savedCref uniformQuoteError unitRoleUnused .complete) adverseCompleteS29Before [.query 1,.hydeRetriever 2] (.selection 3) = 0 := by
    apply control_penalty_empty_of_prior_terminal .complete savedCref uniformQuoteError adverseCompleteS29Before [.query 1,.hydeRetriever 2] (.selection 3) 22 (by decide)
    · decide
    · decide
  unfold indexScore
  rw [hs,hp,hn,hz]
  simp only [BackupStat.mean]
  norm_num

theorem adverseCompleteS29D2I3 : indexScore (7/5) (controlPenalty savedCref uniformQuoteError unitRoleUnused .complete) adverseCompleteS29Before [.query 1,.hydeRetriever 2] (.selection 0) = treeIndex ((0/1)/1) (7/5) 0 6 1 := by
  have hs : replayBackup adverseCompleteS29Before emptyStatistics ([.query 1,.hydeRetriever 2]++[.selection 0]) = ⟨1,(0/1)⟩ := by
    rw [replayBackup_empty_closed_form]
    simp +decide [backedEvents,adverseCompleteS29Before,adverseCompleteProposal,adverseCompleteEvent1,adverseCompleteEvent2,adverseCompleteEvent3,adverseCompleteEvent4,adverseCompleteEvent5,adverseCompleteEvent6,adverseCompleteEvent7,adverseCompleteEvent8,adverseCompleteEvent9,adverseCompleteEvent10,adverseCompleteEvent11,adverseCompleteEvent12,adverseCompleteEvent13,adverseCompleteEvent14,adverseCompleteEvent15,adverseCompleteEvent16,adverseCompleteEvent17,adverseCompleteEvent18,adverseCompleteEvent19,adverseCompleteEvent20,adverseCompleteEvent21,adverseCompleteEvent22,adverseCompleteEvent23,adverseCompleteEvent24,adverseCompleteEvent25,adverseCompleteEvent26,adverseCompleteEvent27,adverseCompleteEvent28,taskReward]
    <;> norm_num
  have hp : rawVisits adverseCompleteS29Before [.query 1,.hydeRetriever 2] = 6 := by decide
  have hn : rawVisits adverseCompleteS29Before ([.query 1,.hydeRetriever 2]++[.selection 0]) = 1 := by decide
  have hz : (controlPenalty savedCref uniformQuoteError unitRoleUnused .complete) adverseCompleteS29Before [.query 1,.hydeRetriever 2] (.selection 0) = 0 := by
    apply control_penalty_empty_of_prior_terminal .complete savedCref uniformQuoteError adverseCompleteS29Before [.query 1,.hydeRetriever 2] (.selection 0) 10 (by decide)
    · decide
    · decide
  unfold indexScore
  rw [hs,hp,hn,hz]
  simp only [BackupStat.mean]
  norm_num

theorem adverseCompleteS29D2Cmp0 : indexScore (7/5) (controlPenalty savedCref uniformQuoteError unitRoleUnused .complete) adverseCompleteS29Before [.query 1,.hydeRetriever 2] (.selection 1) < indexScore (7/5) (controlPenalty savedCref uniformQuoteError unitRoleUnused .complete) adverseCompleteS29Before [.query 1,.hydeRetriever 2] (.selection 2) := by
  rw [adverseCompleteS29D2I0,adverseCompleteS29D2I1]
  have h := index_strict_order_from_intervals ((0/1)/1) ((0/1)/2) 0 0 (24411779/12500000) (69046943/50000000)
    (treeBonus (7/5) 6 1) (treeBonus (7/5) 6 2)
    (trajectory_bonus_6_1).1 (trajectory_bonus_6_2).2 (by norm_num)
  simpa only [treeIndex,sub_zero] using h

theorem adverseCompleteS29D2Cmp2 : indexScore (7/5) (controlPenalty savedCref uniformQuoteError unitRoleUnused .complete) adverseCompleteS29Before [.query 1,.hydeRetriever 2] (.selection 3) ≤ indexScore (7/5) (controlPenalty savedCref uniformQuoteError unitRoleUnused .complete) adverseCompleteS29Before [.query 1,.hydeRetriever 2] (.selection 2) := by
  rw [adverseCompleteS29D2I2,adverseCompleteS29D2I1]

theorem adverseCompleteS29D2Cmp3 : indexScore (7/5) (controlPenalty savedCref uniformQuoteError unitRoleUnused .complete) adverseCompleteS29Before [.query 1,.hydeRetriever 2] (.selection 0) ≤ indexScore (7/5) (controlPenalty savedCref uniformQuoteError unitRoleUnused .complete) adverseCompleteS29Before [.query 1,.hydeRetriever 2] (.selection 2) := by
  rw [adverseCompleteS29D2I3,adverseCompleteS29D2I1]

theorem adverseCompleteS29Choice2 : nativeFirstChoice (indexScore (7/5) (controlPenalty savedCref uniformQuoteError unitRoleUnused .complete) adverseCompleteS29Before [.query 1,.hydeRetriever 2]) adverseCompleteS29Before [.query 1,.hydeRetriever 2] = .selection 2 := by
  apply visited_choice_from_ordered_certificate _ _ [.query 1,.hydeRetriever 2] [.selection 1] [.selection 3,.selection 0] (.selection 2) (by decide)
  · intro a ha
    have ho : orderedLegalAvailable [.query 1,.hydeRetriever 2] = [.selection 1,.selection 2,.selection 3,.selection 0] := by decide
    rw [ho] at ha
    simp only [List.mem_cons,List.not_mem_nil,or_false] at ha
    rcases ha with rfl | rfl | rfl | rfl <;> decide
  · intro a ha
    simp only [List.mem_cons,List.not_mem_nil,or_false] at ha
    rcases ha with rfl
    · exact adverseCompleteS29D2Cmp0
  · intro a ha
    simp only [List.mem_cons,List.not_mem_nil,or_false] at ha
    rcases ha with rfl | rfl
    · exact adverseCompleteS29D2Cmp2
    · exact adverseCompleteS29D2Cmp3

theorem adverseCompleteS29ActualEvent : nativeEvent budgetTape (7/5) (controlPenalty savedCref uniformQuoteError unitRoleUnused .complete)
    (taskReward true (2/5) (1/2)) adverseCompleteS29Before = adverseCompleteEvent29 := by
  have hs0 := native_select_existing_step budgetTape (7/5) (controlPenalty savedCref uniformQuoteError unitRoleUnused .complete) adverseCompleteS29Before 8 [] (.query 1)
    (by decide) (by decide) adverseCompleteS29Choice0
  have hs1 := native_select_existing_step budgetTape (7/5) (controlPenalty savedCref uniformQuoteError unitRoleUnused .complete) adverseCompleteS29Before 7 [.query 1] (.hydeRetriever 2)
    (by decide) (by decide) adverseCompleteS29Choice1
  have hs2 := native_select_existing_step budgetTape (7/5) (controlPenalty savedCref uniformQuoteError unitRoleUnused .complete) adverseCompleteS29Before 6 [.query 1,.hydeRetriever 2] (.selection 2)
    (by decide) (by decide) adverseCompleteS29Choice2
  have hnew := native_select_new_step budgetTape (7/5) (controlPenalty savedCref uniformQuoteError unitRoleUnused .complete) adverseCompleteS29Before 5 [.query 1,.hydeRetriever 2,.selection 2]
    [.width 3,.width 0,.width 1,.width 2] (.width 0) (by decide) (by decide) (by decide) (by decide)
  have hs : nativeSelect budgetTape (7/5) (controlPenalty savedCref uniformQuoteError unitRoleUnused .complete) adverseCompleteS29Before 9 [] = [.query 1,.hydeRetriever 2,.selection 2,.width 0] := by
    rw [hs0]
    change nativeSelect budgetTape (7/5) (controlPenalty savedCref uniformQuoteError unitRoleUnused .complete) adverseCompleteS29Before 8 [.query 1] = _
    rw [hs1]
    change nativeSelect budgetTape (7/5) (controlPenalty savedCref uniformQuoteError unitRoleUnused .complete) adverseCompleteS29Before 7 [.query 1,.hydeRetriever 2] = _
    rw [hs2]
    change nativeSelect budgetTape (7/5) (controlPenalty savedCref uniformQuoteError unitRoleUnused .complete) adverseCompleteS29Before 6 [.query 1,.hydeRetriever 2,.selection 2] = _
    rw [hnew] <;> rfl
  have hr : repairedRollout budgetTape adverseCompleteS29Before 9 [.query 1,.hydeRetriever 2,.selection 2,.width 0] = [.query 1,.hydeRetriever 2,.selection 2,.width 0,.stop,.reranker 0,.topm 0,.context 0,.answer 0] := by decide
  simp only [nativeEvent,hs,hr]
  rfl

def adverseCompleteS30Before := adverseCompleteProposal.take 29

theorem adverseCompleteS30Choice0 : nativeFirstChoice (indexScore (7/5) (controlPenalty savedCref uniformQuoteError unitRoleUnused .complete) adverseCompleteS30Before []) adverseCompleteS30Before [] = .query 1 := by
  apply complete_root_from_physical_gap adverseCompleteS30Before (adverseComplete_prefix_rewards 29) (by decide)
  · intro q; fin_cases q <;> decide
  · exact AgentUCTNextExact.adverse_complete_hyde_root_suffix_empty 29 (by omega)
  · intro q hq
    exact AgentUCTNextExact.adverse_complete_normal_root_physical_quote_exact 29 (by omega) q hq

theorem adverseCompleteS30D1I0 : indexScore (7/5) (controlPenalty savedCref uniformQuoteError unitRoleUnused .complete) adverseCompleteS30Before [.query 1] (.hydeRetriever 1) = treeIndex ((0/1)/7) (7/5) 0 22 7 := by
  have hs : replayBackup adverseCompleteS30Before emptyStatistics ([.query 1]++[.hydeRetriever 1]) = ⟨7,(0/1)⟩ := by
    rw [replayBackup_empty_closed_form]
    simp +decide [backedEvents,adverseCompleteS30Before,adverseCompleteProposal,adverseCompleteEvent1,adverseCompleteEvent2,adverseCompleteEvent3,adverseCompleteEvent4,adverseCompleteEvent5,adverseCompleteEvent6,adverseCompleteEvent7,adverseCompleteEvent8,adverseCompleteEvent9,adverseCompleteEvent10,adverseCompleteEvent11,adverseCompleteEvent12,adverseCompleteEvent13,adverseCompleteEvent14,adverseCompleteEvent15,adverseCompleteEvent16,adverseCompleteEvent17,adverseCompleteEvent18,adverseCompleteEvent19,adverseCompleteEvent20,adverseCompleteEvent21,adverseCompleteEvent22,adverseCompleteEvent23,adverseCompleteEvent24,adverseCompleteEvent25,adverseCompleteEvent26,adverseCompleteEvent27,adverseCompleteEvent28,adverseCompleteEvent29,taskReward]
    <;> norm_num
  have hp : rawVisits adverseCompleteS30Before [.query 1] = 22 := by decide
  have hn : rawVisits adverseCompleteS30Before ([.query 1]++[.hydeRetriever 1]) = 7 := by decide
  have hz : (controlPenalty savedCref uniformQuoteError unitRoleUnused .complete) adverseCompleteS30Before [.query 1] (.hydeRetriever 1) = 0 := by
    apply control_penalty_empty_of_prior_terminal .complete savedCref uniformQuoteError adverseCompleteS30Before [.query 1] (.hydeRetriever 1) 8 (by decide)
    · decide
    · decide
  unfold indexScore
  rw [hs,hp,hn,hz]
  simp only [BackupStat.mean]
  norm_num

theorem adverseCompleteS30D1I1 : indexScore (7/5) (controlPenalty savedCref uniformQuoteError unitRoleUnused .complete) adverseCompleteS30Before [.query 1] (.hydeRetriever 0) = treeIndex ((0/1)/7) (7/5) 0 22 7 := by
  have hs : replayBackup adverseCompleteS30Before emptyStatistics ([.query 1]++[.hydeRetriever 0]) = ⟨7,(0/1)⟩ := by
    rw [replayBackup_empty_closed_form]
    simp +decide [backedEvents,adverseCompleteS30Before,adverseCompleteProposal,adverseCompleteEvent1,adverseCompleteEvent2,adverseCompleteEvent3,adverseCompleteEvent4,adverseCompleteEvent5,adverseCompleteEvent6,adverseCompleteEvent7,adverseCompleteEvent8,adverseCompleteEvent9,adverseCompleteEvent10,adverseCompleteEvent11,adverseCompleteEvent12,adverseCompleteEvent13,adverseCompleteEvent14,adverseCompleteEvent15,adverseCompleteEvent16,adverseCompleteEvent17,adverseCompleteEvent18,adverseCompleteEvent19,adverseCompleteEvent20,adverseCompleteEvent21,adverseCompleteEvent22,adverseCompleteEvent23,adverseCompleteEvent24,adverseCompleteEvent25,adverseCompleteEvent26,adverseCompleteEvent27,adverseCompleteEvent28,adverseCompleteEvent29,taskReward]
    <;> norm_num
  have hp : rawVisits adverseCompleteS30Before [.query 1] = 22 := by decide
  have hn : rawVisits adverseCompleteS30Before ([.query 1]++[.hydeRetriever 0]) = 7 := by decide
  have hz : (controlPenalty savedCref uniformQuoteError unitRoleUnused .complete) adverseCompleteS30Before [.query 1] (.hydeRetriever 0) = 0 := by
    apply control_penalty_empty_of_prior_terminal .complete savedCref uniformQuoteError adverseCompleteS30Before [.query 1] (.hydeRetriever 0) 1 (by decide)
    · decide
    · decide
  unfold indexScore
  rw [hs,hp,hn,hz]
  simp only [BackupStat.mean]
  norm_num

theorem adverseCompleteS30D1I2 : indexScore (7/5) (controlPenalty savedCref uniformQuoteError unitRoleUnused .complete) adverseCompleteS30Before [.query 1] (.hydeRetriever 2) = treeIndex ((0/1)/7) (7/5) 0 22 7 := by
  have hs : replayBackup adverseCompleteS30Before emptyStatistics ([.query 1]++[.hydeRetriever 2]) = ⟨7,(0/1)⟩ := by
    rw [replayBackup_empty_closed_form]
    simp +decide [backedEvents,adverseCompleteS30Before,adverseCompleteProposal,adverseCompleteEvent1,adverseCompleteEvent2,adverseCompleteEvent3,adverseCompleteEvent4,adverseCompleteEvent5,adverseCompleteEvent6,adverseCompleteEvent7,adverseCompleteEvent8,adverseCompleteEvent9,adverseCompleteEvent10,adverseCompleteEvent11,adverseCompleteEvent12,adverseCompleteEvent13,adverseCompleteEvent14,adverseCompleteEvent15,adverseCompleteEvent16,adverseCompleteEvent17,adverseCompleteEvent18,adverseCompleteEvent19,adverseCompleteEvent20,adverseCompleteEvent21,adverseCompleteEvent22,adverseCompleteEvent23,adverseCompleteEvent24,adverseCompleteEvent25,adverseCompleteEvent26,adverseCompleteEvent27,adverseCompleteEvent28,adverseCompleteEvent29,taskReward]
    <;> norm_num
  have hp : rawVisits adverseCompleteS30Before [.query 1] = 22 := by decide
  have hn : rawVisits adverseCompleteS30Before ([.query 1]++[.hydeRetriever 2]) = 7 := by decide
  have hz : (controlPenalty savedCref uniformQuoteError unitRoleUnused .complete) adverseCompleteS30Before [.query 1] (.hydeRetriever 2) = 0 := by
    apply control_penalty_empty_of_prior_terminal .complete savedCref uniformQuoteError adverseCompleteS30Before [.query 1] (.hydeRetriever 2) 10 (by decide)
    · decide
    · decide
  unfold indexScore
  rw [hs,hp,hn,hz]
  simp only [BackupStat.mean]
  norm_num

theorem adverseCompleteS30D1Cmp1 : indexScore (7/5) (controlPenalty savedCref uniformQuoteError unitRoleUnused .complete) adverseCompleteS30Before [.query 1] (.hydeRetriever 0) ≤ indexScore (7/5) (controlPenalty savedCref uniformQuoteError unitRoleUnused .complete) adverseCompleteS30Before [.query 1] (.hydeRetriever 1) := by
  rw [adverseCompleteS30D1I1,adverseCompleteS30D1I0]

theorem adverseCompleteS30D1Cmp2 : indexScore (7/5) (controlPenalty savedCref uniformQuoteError unitRoleUnused .complete) adverseCompleteS30Before [.query 1] (.hydeRetriever 2) ≤ indexScore (7/5) (controlPenalty savedCref uniformQuoteError unitRoleUnused .complete) adverseCompleteS30Before [.query 1] (.hydeRetriever 1) := by
  rw [adverseCompleteS30D1I2,adverseCompleteS30D1I0]

theorem adverseCompleteS30Choice1 : nativeFirstChoice (indexScore (7/5) (controlPenalty savedCref uniformQuoteError unitRoleUnused .complete) adverseCompleteS30Before [.query 1]) adverseCompleteS30Before [.query 1] = .hydeRetriever 1 := by
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
    · exact adverseCompleteS30D1Cmp1
    · exact adverseCompleteS30D1Cmp2

theorem adverseCompleteS30D2I0 : indexScore (7/5) (controlPenalty savedCref uniformQuoteError unitRoleUnused .complete) adverseCompleteS30Before [.query 1,.hydeRetriever 1] (.selection 1) = treeIndex ((0/1)/2) (7/5) 0 7 2 := by
  have hs : replayBackup adverseCompleteS30Before emptyStatistics ([.query 1,.hydeRetriever 1]++[.selection 1]) = ⟨2,(0/1)⟩ := by
    rw [replayBackup_empty_closed_form]
    simp +decide [backedEvents,adverseCompleteS30Before,adverseCompleteProposal,adverseCompleteEvent1,adverseCompleteEvent2,adverseCompleteEvent3,adverseCompleteEvent4,adverseCompleteEvent5,adverseCompleteEvent6,adverseCompleteEvent7,adverseCompleteEvent8,adverseCompleteEvent9,adverseCompleteEvent10,adverseCompleteEvent11,adverseCompleteEvent12,adverseCompleteEvent13,adverseCompleteEvent14,adverseCompleteEvent15,adverseCompleteEvent16,adverseCompleteEvent17,adverseCompleteEvent18,adverseCompleteEvent19,adverseCompleteEvent20,adverseCompleteEvent21,adverseCompleteEvent22,adverseCompleteEvent23,adverseCompleteEvent24,adverseCompleteEvent25,adverseCompleteEvent26,adverseCompleteEvent27,adverseCompleteEvent28,adverseCompleteEvent29,taskReward]
    <;> norm_num
  have hp : rawVisits adverseCompleteS30Before [.query 1,.hydeRetriever 1] = 7 := by decide
  have hn : rawVisits adverseCompleteS30Before ([.query 1,.hydeRetriever 1]++[.selection 1]) = 2 := by decide
  have hz : (controlPenalty savedCref uniformQuoteError unitRoleUnused .complete) adverseCompleteS30Before [.query 1,.hydeRetriever 1] (.selection 1) = 0 := by
    apply control_penalty_empty_of_prior_terminal .complete savedCref uniformQuoteError adverseCompleteS30Before [.query 1,.hydeRetriever 1] (.selection 1) 14 (by decide)
    · decide
    · decide
  unfold indexScore
  rw [hs,hp,hn,hz]
  simp only [BackupStat.mean]
  norm_num

theorem adverseCompleteS30D2I1 : indexScore (7/5) (controlPenalty savedCref uniformQuoteError unitRoleUnused .complete) adverseCompleteS30Before [.query 1,.hydeRetriever 1] (.selection 2) = treeIndex ((0/1)/2) (7/5) 0 7 2 := by
  have hs : replayBackup adverseCompleteS30Before emptyStatistics ([.query 1,.hydeRetriever 1]++[.selection 2]) = ⟨2,(0/1)⟩ := by
    rw [replayBackup_empty_closed_form]
    simp +decide [backedEvents,adverseCompleteS30Before,adverseCompleteProposal,adverseCompleteEvent1,adverseCompleteEvent2,adverseCompleteEvent3,adverseCompleteEvent4,adverseCompleteEvent5,adverseCompleteEvent6,adverseCompleteEvent7,adverseCompleteEvent8,adverseCompleteEvent9,adverseCompleteEvent10,adverseCompleteEvent11,adverseCompleteEvent12,adverseCompleteEvent13,adverseCompleteEvent14,adverseCompleteEvent15,adverseCompleteEvent16,adverseCompleteEvent17,adverseCompleteEvent18,adverseCompleteEvent19,adverseCompleteEvent20,adverseCompleteEvent21,adverseCompleteEvent22,adverseCompleteEvent23,adverseCompleteEvent24,adverseCompleteEvent25,adverseCompleteEvent26,adverseCompleteEvent27,adverseCompleteEvent28,adverseCompleteEvent29,taskReward]
    <;> norm_num
  have hp : rawVisits adverseCompleteS30Before [.query 1,.hydeRetriever 1] = 7 := by decide
  have hn : rawVisits adverseCompleteS30Before ([.query 1,.hydeRetriever 1]++[.selection 2]) = 2 := by decide
  have hz : (controlPenalty savedCref uniformQuoteError unitRoleUnused .complete) adverseCompleteS30Before [.query 1,.hydeRetriever 1] (.selection 2) = 0 := by
    apply control_penalty_empty_of_prior_terminal .complete savedCref uniformQuoteError adverseCompleteS30Before [.query 1,.hydeRetriever 1] (.selection 2) 17 (by decide)
    · decide
    · decide
  unfold indexScore
  rw [hs,hp,hn,hz]
  simp only [BackupStat.mean]
  norm_num

theorem adverseCompleteS30D2I2 : indexScore (7/5) (controlPenalty savedCref uniformQuoteError unitRoleUnused .complete) adverseCompleteS30Before [.query 1,.hydeRetriever 1] (.selection 3) = treeIndex ((0/1)/1) (7/5) 0 7 1 := by
  have hs : replayBackup adverseCompleteS30Before emptyStatistics ([.query 1,.hydeRetriever 1]++[.selection 3]) = ⟨1,(0/1)⟩ := by
    rw [replayBackup_empty_closed_form]
    simp +decide [backedEvents,adverseCompleteS30Before,adverseCompleteProposal,adverseCompleteEvent1,adverseCompleteEvent2,adverseCompleteEvent3,adverseCompleteEvent4,adverseCompleteEvent5,adverseCompleteEvent6,adverseCompleteEvent7,adverseCompleteEvent8,adverseCompleteEvent9,adverseCompleteEvent10,adverseCompleteEvent11,adverseCompleteEvent12,adverseCompleteEvent13,adverseCompleteEvent14,adverseCompleteEvent15,adverseCompleteEvent16,adverseCompleteEvent17,adverseCompleteEvent18,adverseCompleteEvent19,adverseCompleteEvent20,adverseCompleteEvent21,adverseCompleteEvent22,adverseCompleteEvent23,adverseCompleteEvent24,adverseCompleteEvent25,adverseCompleteEvent26,adverseCompleteEvent27,adverseCompleteEvent28,adverseCompleteEvent29,taskReward]
    <;> norm_num
  have hp : rawVisits adverseCompleteS30Before [.query 1,.hydeRetriever 1] = 7 := by decide
  have hn : rawVisits adverseCompleteS30Before ([.query 1,.hydeRetriever 1]++[.selection 3]) = 1 := by decide
  have hz : (controlPenalty savedCref uniformQuoteError unitRoleUnused .complete) adverseCompleteS30Before [.query 1,.hydeRetriever 1] (.selection 3) = 0 := by
    apply control_penalty_empty_of_prior_terminal .complete savedCref uniformQuoteError adverseCompleteS30Before [.query 1,.hydeRetriever 1] (.selection 3) 20 (by decide)
    · decide
    · decide
  unfold indexScore
  rw [hs,hp,hn,hz]
  simp only [BackupStat.mean]
  norm_num

theorem adverseCompleteS30D2I3 : indexScore (7/5) (controlPenalty savedCref uniformQuoteError unitRoleUnused .complete) adverseCompleteS30Before [.query 1,.hydeRetriever 1] (.selection 0) = treeIndex ((0/1)/1) (7/5) 0 7 1 := by
  have hs : replayBackup adverseCompleteS30Before emptyStatistics ([.query 1,.hydeRetriever 1]++[.selection 0]) = ⟨1,(0/1)⟩ := by
    rw [replayBackup_empty_closed_form]
    simp +decide [backedEvents,adverseCompleteS30Before,adverseCompleteProposal,adverseCompleteEvent1,adverseCompleteEvent2,adverseCompleteEvent3,adverseCompleteEvent4,adverseCompleteEvent5,adverseCompleteEvent6,adverseCompleteEvent7,adverseCompleteEvent8,adverseCompleteEvent9,adverseCompleteEvent10,adverseCompleteEvent11,adverseCompleteEvent12,adverseCompleteEvent13,adverseCompleteEvent14,adverseCompleteEvent15,adverseCompleteEvent16,adverseCompleteEvent17,adverseCompleteEvent18,adverseCompleteEvent19,adverseCompleteEvent20,adverseCompleteEvent21,adverseCompleteEvent22,adverseCompleteEvent23,adverseCompleteEvent24,adverseCompleteEvent25,adverseCompleteEvent26,adverseCompleteEvent27,adverseCompleteEvent28,adverseCompleteEvent29,taskReward]
    <;> norm_num
  have hp : rawVisits adverseCompleteS30Before [.query 1,.hydeRetriever 1] = 7 := by decide
  have hn : rawVisits adverseCompleteS30Before ([.query 1,.hydeRetriever 1]++[.selection 0]) = 1 := by decide
  have hz : (controlPenalty savedCref uniformQuoteError unitRoleUnused .complete) adverseCompleteS30Before [.query 1,.hydeRetriever 1] (.selection 0) = 0 := by
    apply control_penalty_empty_of_prior_terminal .complete savedCref uniformQuoteError adverseCompleteS30Before [.query 1,.hydeRetriever 1] (.selection 0) 8 (by decide)
    · decide
    · decide
  unfold indexScore
  rw [hs,hp,hn,hz]
  simp only [BackupStat.mean]
  norm_num

theorem adverseCompleteS30D2Cmp0 : indexScore (7/5) (controlPenalty savedCref uniformQuoteError unitRoleUnused .complete) adverseCompleteS30Before [.query 1,.hydeRetriever 1] (.selection 1) < indexScore (7/5) (controlPenalty savedCref uniformQuoteError unitRoleUnused .complete) adverseCompleteS30Before [.query 1,.hydeRetriever 1] (.selection 3) := by
  rw [adverseCompleteS30D2I0,adverseCompleteS30D2I2]
  have h := index_strict_order_from_intervals ((0/1)/1) ((0/1)/2) 0 0 (25235469/12500000) (71376697/50000000)
    (treeBonus (7/5) 7 1) (treeBonus (7/5) 7 2)
    (trajectory_bonus_7_1).1 (trajectory_bonus_7_2).2 (by norm_num)
  simpa only [treeIndex,sub_zero] using h

theorem adverseCompleteS30D2Cmp1 : indexScore (7/5) (controlPenalty savedCref uniformQuoteError unitRoleUnused .complete) adverseCompleteS30Before [.query 1,.hydeRetriever 1] (.selection 2) < indexScore (7/5) (controlPenalty savedCref uniformQuoteError unitRoleUnused .complete) adverseCompleteS30Before [.query 1,.hydeRetriever 1] (.selection 3) := by
  rw [adverseCompleteS30D2I1,adverseCompleteS30D2I2]
  have h := index_strict_order_from_intervals ((0/1)/1) ((0/1)/2) 0 0 (25235469/12500000) (71376697/50000000)
    (treeBonus (7/5) 7 1) (treeBonus (7/5) 7 2)
    (trajectory_bonus_7_1).1 (trajectory_bonus_7_2).2 (by norm_num)
  simpa only [treeIndex,sub_zero] using h

theorem adverseCompleteS30D2Cmp3 : indexScore (7/5) (controlPenalty savedCref uniformQuoteError unitRoleUnused .complete) adverseCompleteS30Before [.query 1,.hydeRetriever 1] (.selection 0) ≤ indexScore (7/5) (controlPenalty savedCref uniformQuoteError unitRoleUnused .complete) adverseCompleteS30Before [.query 1,.hydeRetriever 1] (.selection 3) := by
  rw [adverseCompleteS30D2I3,adverseCompleteS30D2I2]

theorem adverseCompleteS30Choice2 : nativeFirstChoice (indexScore (7/5) (controlPenalty savedCref uniformQuoteError unitRoleUnused .complete) adverseCompleteS30Before [.query 1,.hydeRetriever 1]) adverseCompleteS30Before [.query 1,.hydeRetriever 1] = .selection 3 := by
  apply visited_choice_from_ordered_certificate _ _ [.query 1,.hydeRetriever 1] [.selection 1,.selection 2] [.selection 0] (.selection 3) (by decide)
  · intro a ha
    have ho : orderedLegalAvailable [.query 1,.hydeRetriever 1] = [.selection 1,.selection 2,.selection 3,.selection 0] := by decide
    rw [ho] at ha
    simp only [List.mem_cons,List.not_mem_nil,or_false] at ha
    rcases ha with rfl | rfl | rfl | rfl <;> decide
  · intro a ha
    simp only [List.mem_cons,List.not_mem_nil,or_false] at ha
    rcases ha with rfl | rfl
    · exact adverseCompleteS30D2Cmp0
    · exact adverseCompleteS30D2Cmp1
  · intro a ha
    simp only [List.mem_cons,List.not_mem_nil,or_false] at ha
    rcases ha with rfl
    · exact adverseCompleteS30D2Cmp3

theorem adverseCompleteS30ActualEvent : nativeEvent budgetTape (7/5) (controlPenalty savedCref uniformQuoteError unitRoleUnused .complete)
    (taskReward true (2/5) (1/2)) adverseCompleteS30Before = adverseCompleteEvent30 := by
  have hs0 := native_select_existing_step budgetTape (7/5) (controlPenalty savedCref uniformQuoteError unitRoleUnused .complete) adverseCompleteS30Before 8 [] (.query 1)
    (by decide) (by decide) adverseCompleteS30Choice0
  have hs1 := native_select_existing_step budgetTape (7/5) (controlPenalty savedCref uniformQuoteError unitRoleUnused .complete) adverseCompleteS30Before 7 [.query 1] (.hydeRetriever 1)
    (by decide) (by decide) adverseCompleteS30Choice1
  have hs2 := native_select_existing_step budgetTape (7/5) (controlPenalty savedCref uniformQuoteError unitRoleUnused .complete) adverseCompleteS30Before 6 [.query 1,.hydeRetriever 1] (.selection 3)
    (by decide) (by decide) adverseCompleteS30Choice2
  have hnew := native_select_new_step budgetTape (7/5) (controlPenalty savedCref uniformQuoteError unitRoleUnused .complete) adverseCompleteS30Before 5 [.query 1,.hydeRetriever 1,.selection 3]
    [.width 3,.width 0,.width 1,.width 2] (.width 0) (by decide) (by decide) (by decide) (by decide)
  have hs : nativeSelect budgetTape (7/5) (controlPenalty savedCref uniformQuoteError unitRoleUnused .complete) adverseCompleteS30Before 9 [] = [.query 1,.hydeRetriever 1,.selection 3,.width 0] := by
    rw [hs0]
    change nativeSelect budgetTape (7/5) (controlPenalty savedCref uniformQuoteError unitRoleUnused .complete) adverseCompleteS30Before 8 [.query 1] = _
    rw [hs1]
    change nativeSelect budgetTape (7/5) (controlPenalty savedCref uniformQuoteError unitRoleUnused .complete) adverseCompleteS30Before 7 [.query 1,.hydeRetriever 1] = _
    rw [hs2]
    change nativeSelect budgetTape (7/5) (controlPenalty savedCref uniformQuoteError unitRoleUnused .complete) adverseCompleteS30Before 6 [.query 1,.hydeRetriever 1,.selection 3] = _
    rw [hnew] <;> rfl
  have hr : repairedRollout budgetTape adverseCompleteS30Before 9 [.query 1,.hydeRetriever 1,.selection 3,.width 0] = [.query 1,.hydeRetriever 1,.selection 3,.width 0,.stop,.reranker 0,.topm 0,.context 0,.answer 0] := by decide
  simp only [nativeEvent,hs,hr]
  rfl

def adverseCompleteS31Before := adverseCompleteProposal.take 30

theorem adverseCompleteS31Choice0 : nativeFirstChoice (indexScore (7/5) (controlPenalty savedCref uniformQuoteError unitRoleUnused .complete) adverseCompleteS31Before []) adverseCompleteS31Before [] = .query 1 := by
  apply complete_root_from_physical_gap adverseCompleteS31Before (adverseComplete_prefix_rewards 30) (by decide)
  · intro q; fin_cases q <;> decide
  · exact AgentUCTNextExact.adverse_complete_hyde_root_suffix_empty 30 (by omega)
  · intro q hq
    exact AgentUCTNextExact.adverse_complete_normal_root_physical_quote_exact 30 (by omega) q hq

theorem adverseCompleteS31D1I0 : indexScore (7/5) (controlPenalty savedCref uniformQuoteError unitRoleUnused .complete) adverseCompleteS31Before [.query 1] (.hydeRetriever 1) = treeIndex ((0/1)/8) (7/5) 0 23 8 := by
  have hs : replayBackup adverseCompleteS31Before emptyStatistics ([.query 1]++[.hydeRetriever 1]) = ⟨8,(0/1)⟩ := by
    rw [replayBackup_empty_closed_form]
    simp +decide [backedEvents,adverseCompleteS31Before,adverseCompleteProposal,adverseCompleteEvent1,adverseCompleteEvent2,adverseCompleteEvent3,adverseCompleteEvent4,adverseCompleteEvent5,adverseCompleteEvent6,adverseCompleteEvent7,adverseCompleteEvent8,adverseCompleteEvent9,adverseCompleteEvent10,adverseCompleteEvent11,adverseCompleteEvent12,adverseCompleteEvent13,adverseCompleteEvent14,adverseCompleteEvent15,adverseCompleteEvent16,adverseCompleteEvent17,adverseCompleteEvent18,adverseCompleteEvent19,adverseCompleteEvent20,adverseCompleteEvent21,adverseCompleteEvent22,adverseCompleteEvent23,adverseCompleteEvent24,adverseCompleteEvent25,adverseCompleteEvent26,adverseCompleteEvent27,adverseCompleteEvent28,adverseCompleteEvent29,adverseCompleteEvent30,taskReward]
    <;> norm_num
  have hp : rawVisits adverseCompleteS31Before [.query 1] = 23 := by decide
  have hn : rawVisits adverseCompleteS31Before ([.query 1]++[.hydeRetriever 1]) = 8 := by decide
  have hz : (controlPenalty savedCref uniformQuoteError unitRoleUnused .complete) adverseCompleteS31Before [.query 1] (.hydeRetriever 1) = 0 := by
    apply control_penalty_empty_of_prior_terminal .complete savedCref uniformQuoteError adverseCompleteS31Before [.query 1] (.hydeRetriever 1) 8 (by decide)
    · decide
    · decide
  unfold indexScore
  rw [hs,hp,hn,hz]
  simp only [BackupStat.mean]
  norm_num

theorem adverseCompleteS31D1I1 : indexScore (7/5) (controlPenalty savedCref uniformQuoteError unitRoleUnused .complete) adverseCompleteS31Before [.query 1] (.hydeRetriever 0) = treeIndex ((0/1)/7) (7/5) 0 23 7 := by
  have hs : replayBackup adverseCompleteS31Before emptyStatistics ([.query 1]++[.hydeRetriever 0]) = ⟨7,(0/1)⟩ := by
    rw [replayBackup_empty_closed_form]
    simp +decide [backedEvents,adverseCompleteS31Before,adverseCompleteProposal,adverseCompleteEvent1,adverseCompleteEvent2,adverseCompleteEvent3,adverseCompleteEvent4,adverseCompleteEvent5,adverseCompleteEvent6,adverseCompleteEvent7,adverseCompleteEvent8,adverseCompleteEvent9,adverseCompleteEvent10,adverseCompleteEvent11,adverseCompleteEvent12,adverseCompleteEvent13,adverseCompleteEvent14,adverseCompleteEvent15,adverseCompleteEvent16,adverseCompleteEvent17,adverseCompleteEvent18,adverseCompleteEvent19,adverseCompleteEvent20,adverseCompleteEvent21,adverseCompleteEvent22,adverseCompleteEvent23,adverseCompleteEvent24,adverseCompleteEvent25,adverseCompleteEvent26,adverseCompleteEvent27,adverseCompleteEvent28,adverseCompleteEvent29,adverseCompleteEvent30,taskReward]
    <;> norm_num
  have hp : rawVisits adverseCompleteS31Before [.query 1] = 23 := by decide
  have hn : rawVisits adverseCompleteS31Before ([.query 1]++[.hydeRetriever 0]) = 7 := by decide
  have hz : (controlPenalty savedCref uniformQuoteError unitRoleUnused .complete) adverseCompleteS31Before [.query 1] (.hydeRetriever 0) = 0 := by
    apply control_penalty_empty_of_prior_terminal .complete savedCref uniformQuoteError adverseCompleteS31Before [.query 1] (.hydeRetriever 0) 1 (by decide)
    · decide
    · decide
  unfold indexScore
  rw [hs,hp,hn,hz]
  simp only [BackupStat.mean]
  norm_num

theorem adverseCompleteS31D1I2 : indexScore (7/5) (controlPenalty savedCref uniformQuoteError unitRoleUnused .complete) adverseCompleteS31Before [.query 1] (.hydeRetriever 2) = treeIndex ((0/1)/7) (7/5) 0 23 7 := by
  have hs : replayBackup adverseCompleteS31Before emptyStatistics ([.query 1]++[.hydeRetriever 2]) = ⟨7,(0/1)⟩ := by
    rw [replayBackup_empty_closed_form]
    simp +decide [backedEvents,adverseCompleteS31Before,adverseCompleteProposal,adverseCompleteEvent1,adverseCompleteEvent2,adverseCompleteEvent3,adverseCompleteEvent4,adverseCompleteEvent5,adverseCompleteEvent6,adverseCompleteEvent7,adverseCompleteEvent8,adverseCompleteEvent9,adverseCompleteEvent10,adverseCompleteEvent11,adverseCompleteEvent12,adverseCompleteEvent13,adverseCompleteEvent14,adverseCompleteEvent15,adverseCompleteEvent16,adverseCompleteEvent17,adverseCompleteEvent18,adverseCompleteEvent19,adverseCompleteEvent20,adverseCompleteEvent21,adverseCompleteEvent22,adverseCompleteEvent23,adverseCompleteEvent24,adverseCompleteEvent25,adverseCompleteEvent26,adverseCompleteEvent27,adverseCompleteEvent28,adverseCompleteEvent29,adverseCompleteEvent30,taskReward]
    <;> norm_num
  have hp : rawVisits adverseCompleteS31Before [.query 1] = 23 := by decide
  have hn : rawVisits adverseCompleteS31Before ([.query 1]++[.hydeRetriever 2]) = 7 := by decide
  have hz : (controlPenalty savedCref uniformQuoteError unitRoleUnused .complete) adverseCompleteS31Before [.query 1] (.hydeRetriever 2) = 0 := by
    apply control_penalty_empty_of_prior_terminal .complete savedCref uniformQuoteError adverseCompleteS31Before [.query 1] (.hydeRetriever 2) 10 (by decide)
    · decide
    · decide
  unfold indexScore
  rw [hs,hp,hn,hz]
  simp only [BackupStat.mean]
  norm_num

theorem adverseCompleteS31D1Cmp0 : indexScore (7/5) (controlPenalty savedCref uniformQuoteError unitRoleUnused .complete) adverseCompleteS31Before [.query 1] (.hydeRetriever 1) < indexScore (7/5) (controlPenalty savedCref uniformQuoteError unitRoleUnused .complete) adverseCompleteS31Before [.query 1] (.hydeRetriever 0) := by
  rw [adverseCompleteS31D1I0,adverseCompleteS31D1I1]
  have h := index_strict_order_from_intervals ((0/1)/7) ((0/1)/8) 0 0 (47166063/50000000) (44119817/50000000)
    (treeBonus (7/5) 23 7) (treeBonus (7/5) 23 8)
    (trajectory_bonus_23_7).1 (trajectory_bonus_23_8).2 (by norm_num)
  simpa only [treeIndex,sub_zero] using h

theorem adverseCompleteS31D1Cmp2 : indexScore (7/5) (controlPenalty savedCref uniformQuoteError unitRoleUnused .complete) adverseCompleteS31Before [.query 1] (.hydeRetriever 2) ≤ indexScore (7/5) (controlPenalty savedCref uniformQuoteError unitRoleUnused .complete) adverseCompleteS31Before [.query 1] (.hydeRetriever 0) := by
  rw [adverseCompleteS31D1I2,adverseCompleteS31D1I1]

theorem adverseCompleteS31Choice1 : nativeFirstChoice (indexScore (7/5) (controlPenalty savedCref uniformQuoteError unitRoleUnused .complete) adverseCompleteS31Before [.query 1]) adverseCompleteS31Before [.query 1] = .hydeRetriever 0 := by
  apply visited_choice_from_ordered_certificate _ _ [.query 1] [.hydeRetriever 1] [.hydeRetriever 2] (.hydeRetriever 0) (by decide)
  · intro a ha
    have ho : orderedLegalAvailable [.query 1] = [.hydeRetriever 1,.hydeRetriever 0,.hydeRetriever 2] := by decide
    rw [ho] at ha
    simp only [List.mem_cons,List.not_mem_nil,or_false] at ha
    rcases ha with rfl | rfl | rfl <;> decide
  · intro a ha
    simp only [List.mem_cons,List.not_mem_nil,or_false] at ha
    rcases ha with rfl
    · exact adverseCompleteS31D1Cmp0
  · intro a ha
    simp only [List.mem_cons,List.not_mem_nil,or_false] at ha
    rcases ha with rfl
    · exact adverseCompleteS31D1Cmp2

theorem adverseCompleteS31D2I0 : indexScore (7/5) (controlPenalty savedCref uniformQuoteError unitRoleUnused .complete) adverseCompleteS31Before [.query 1,.hydeRetriever 0] (.selection 1) = treeIndex ((0/1)/2) (7/5) 0 7 2 := by
  have hs : replayBackup adverseCompleteS31Before emptyStatistics ([.query 1,.hydeRetriever 0]++[.selection 1]) = ⟨2,(0/1)⟩ := by
    rw [replayBackup_empty_closed_form]
    simp +decide [backedEvents,adverseCompleteS31Before,adverseCompleteProposal,adverseCompleteEvent1,adverseCompleteEvent2,adverseCompleteEvent3,adverseCompleteEvent4,adverseCompleteEvent5,adverseCompleteEvent6,adverseCompleteEvent7,adverseCompleteEvent8,adverseCompleteEvent9,adverseCompleteEvent10,adverseCompleteEvent11,adverseCompleteEvent12,adverseCompleteEvent13,adverseCompleteEvent14,adverseCompleteEvent15,adverseCompleteEvent16,adverseCompleteEvent17,adverseCompleteEvent18,adverseCompleteEvent19,adverseCompleteEvent20,adverseCompleteEvent21,adverseCompleteEvent22,adverseCompleteEvent23,adverseCompleteEvent24,adverseCompleteEvent25,adverseCompleteEvent26,adverseCompleteEvent27,adverseCompleteEvent28,adverseCompleteEvent29,adverseCompleteEvent30,taskReward]
    <;> norm_num
  have hp : rawVisits adverseCompleteS31Before [.query 1,.hydeRetriever 0] = 7 := by decide
  have hn : rawVisits adverseCompleteS31Before ([.query 1,.hydeRetriever 0]++[.selection 1]) = 2 := by decide
  have hz : (controlPenalty savedCref uniformQuoteError unitRoleUnused .complete) adverseCompleteS31Before [.query 1,.hydeRetriever 0] (.selection 1) = 0 := by
    apply control_penalty_empty_of_prior_terminal .complete savedCref uniformQuoteError adverseCompleteS31Before [.query 1,.hydeRetriever 0] (.selection 1) 15 (by decide)
    · decide
    · decide
  unfold indexScore
  rw [hs,hp,hn,hz]
  simp only [BackupStat.mean]
  norm_num

theorem adverseCompleteS31D2I1 : indexScore (7/5) (controlPenalty savedCref uniformQuoteError unitRoleUnused .complete) adverseCompleteS31Before [.query 1,.hydeRetriever 0] (.selection 2) = treeIndex ((0/1)/2) (7/5) 0 7 2 := by
  have hs : replayBackup adverseCompleteS31Before emptyStatistics ([.query 1,.hydeRetriever 0]++[.selection 2]) = ⟨2,(0/1)⟩ := by
    rw [replayBackup_empty_closed_form]
    simp +decide [backedEvents,adverseCompleteS31Before,adverseCompleteProposal,adverseCompleteEvent1,adverseCompleteEvent2,adverseCompleteEvent3,adverseCompleteEvent4,adverseCompleteEvent5,adverseCompleteEvent6,adverseCompleteEvent7,adverseCompleteEvent8,adverseCompleteEvent9,adverseCompleteEvent10,adverseCompleteEvent11,adverseCompleteEvent12,adverseCompleteEvent13,adverseCompleteEvent14,adverseCompleteEvent15,adverseCompleteEvent16,adverseCompleteEvent17,adverseCompleteEvent18,adverseCompleteEvent19,adverseCompleteEvent20,adverseCompleteEvent21,adverseCompleteEvent22,adverseCompleteEvent23,adverseCompleteEvent24,adverseCompleteEvent25,adverseCompleteEvent26,adverseCompleteEvent27,adverseCompleteEvent28,adverseCompleteEvent29,adverseCompleteEvent30,taskReward]
    <;> norm_num
  have hp : rawVisits adverseCompleteS31Before [.query 1,.hydeRetriever 0] = 7 := by decide
  have hn : rawVisits adverseCompleteS31Before ([.query 1,.hydeRetriever 0]++[.selection 2]) = 2 := by decide
  have hz : (controlPenalty savedCref uniformQuoteError unitRoleUnused .complete) adverseCompleteS31Before [.query 1,.hydeRetriever 0] (.selection 2) = 0 := by
    apply control_penalty_empty_of_prior_terminal .complete savedCref uniformQuoteError adverseCompleteS31Before [.query 1,.hydeRetriever 0] (.selection 2) 18 (by decide)
    · decide
    · decide
  unfold indexScore
  rw [hs,hp,hn,hz]
  simp only [BackupStat.mean]
  norm_num

theorem adverseCompleteS31D2I2 : indexScore (7/5) (controlPenalty savedCref uniformQuoteError unitRoleUnused .complete) adverseCompleteS31Before [.query 1,.hydeRetriever 0] (.selection 3) = treeIndex ((0/1)/1) (7/5) 0 7 1 := by
  have hs : replayBackup adverseCompleteS31Before emptyStatistics ([.query 1,.hydeRetriever 0]++[.selection 3]) = ⟨1,(0/1)⟩ := by
    rw [replayBackup_empty_closed_form]
    simp +decide [backedEvents,adverseCompleteS31Before,adverseCompleteProposal,adverseCompleteEvent1,adverseCompleteEvent2,adverseCompleteEvent3,adverseCompleteEvent4,adverseCompleteEvent5,adverseCompleteEvent6,adverseCompleteEvent7,adverseCompleteEvent8,adverseCompleteEvent9,adverseCompleteEvent10,adverseCompleteEvent11,adverseCompleteEvent12,adverseCompleteEvent13,adverseCompleteEvent14,adverseCompleteEvent15,adverseCompleteEvent16,adverseCompleteEvent17,adverseCompleteEvent18,adverseCompleteEvent19,adverseCompleteEvent20,adverseCompleteEvent21,adverseCompleteEvent22,adverseCompleteEvent23,adverseCompleteEvent24,adverseCompleteEvent25,adverseCompleteEvent26,adverseCompleteEvent27,adverseCompleteEvent28,adverseCompleteEvent29,adverseCompleteEvent30,taskReward]
    <;> norm_num
  have hp : rawVisits adverseCompleteS31Before [.query 1,.hydeRetriever 0] = 7 := by decide
  have hn : rawVisits adverseCompleteS31Before ([.query 1,.hydeRetriever 0]++[.selection 3]) = 1 := by decide
  have hz : (controlPenalty savedCref uniformQuoteError unitRoleUnused .complete) adverseCompleteS31Before [.query 1,.hydeRetriever 0] (.selection 3) = 0 := by
    apply control_penalty_empty_of_prior_terminal .complete savedCref uniformQuoteError adverseCompleteS31Before [.query 1,.hydeRetriever 0] (.selection 3) 21 (by decide)
    · decide
    · decide
  unfold indexScore
  rw [hs,hp,hn,hz]
  simp only [BackupStat.mean]
  norm_num

theorem adverseCompleteS31D2I3 : indexScore (7/5) (controlPenalty savedCref uniformQuoteError unitRoleUnused .complete) adverseCompleteS31Before [.query 1,.hydeRetriever 0] (.selection 0) = treeIndex ((0/1)/1) (7/5) 0 7 1 := by
  have hs : replayBackup adverseCompleteS31Before emptyStatistics ([.query 1,.hydeRetriever 0]++[.selection 0]) = ⟨1,(0/1)⟩ := by
    rw [replayBackup_empty_closed_form]
    simp +decide [backedEvents,adverseCompleteS31Before,adverseCompleteProposal,adverseCompleteEvent1,adverseCompleteEvent2,adverseCompleteEvent3,adverseCompleteEvent4,adverseCompleteEvent5,adverseCompleteEvent6,adverseCompleteEvent7,adverseCompleteEvent8,adverseCompleteEvent9,adverseCompleteEvent10,adverseCompleteEvent11,adverseCompleteEvent12,adverseCompleteEvent13,adverseCompleteEvent14,adverseCompleteEvent15,adverseCompleteEvent16,adverseCompleteEvent17,adverseCompleteEvent18,adverseCompleteEvent19,adverseCompleteEvent20,adverseCompleteEvent21,adverseCompleteEvent22,adverseCompleteEvent23,adverseCompleteEvent24,adverseCompleteEvent25,adverseCompleteEvent26,adverseCompleteEvent27,adverseCompleteEvent28,adverseCompleteEvent29,adverseCompleteEvent30,taskReward]
    <;> norm_num
  have hp : rawVisits adverseCompleteS31Before [.query 1,.hydeRetriever 0] = 7 := by decide
  have hn : rawVisits adverseCompleteS31Before ([.query 1,.hydeRetriever 0]++[.selection 0]) = 1 := by decide
  have hz : (controlPenalty savedCref uniformQuoteError unitRoleUnused .complete) adverseCompleteS31Before [.query 1,.hydeRetriever 0] (.selection 0) = 0 := by
    apply control_penalty_empty_of_prior_terminal .complete savedCref uniformQuoteError adverseCompleteS31Before [.query 1,.hydeRetriever 0] (.selection 0) 1 (by decide)
    · decide
    · decide
  unfold indexScore
  rw [hs,hp,hn,hz]
  simp only [BackupStat.mean]
  norm_num

theorem adverseCompleteS31D2Cmp0 : indexScore (7/5) (controlPenalty savedCref uniformQuoteError unitRoleUnused .complete) adverseCompleteS31Before [.query 1,.hydeRetriever 0] (.selection 1) < indexScore (7/5) (controlPenalty savedCref uniformQuoteError unitRoleUnused .complete) adverseCompleteS31Before [.query 1,.hydeRetriever 0] (.selection 3) := by
  rw [adverseCompleteS31D2I0,adverseCompleteS31D2I2]
  have h := index_strict_order_from_intervals ((0/1)/1) ((0/1)/2) 0 0 (25235469/12500000) (71376697/50000000)
    (treeBonus (7/5) 7 1) (treeBonus (7/5) 7 2)
    (trajectory_bonus_7_1).1 (trajectory_bonus_7_2).2 (by norm_num)
  simpa only [treeIndex,sub_zero] using h

theorem adverseCompleteS31D2Cmp1 : indexScore (7/5) (controlPenalty savedCref uniformQuoteError unitRoleUnused .complete) adverseCompleteS31Before [.query 1,.hydeRetriever 0] (.selection 2) < indexScore (7/5) (controlPenalty savedCref uniformQuoteError unitRoleUnused .complete) adverseCompleteS31Before [.query 1,.hydeRetriever 0] (.selection 3) := by
  rw [adverseCompleteS31D2I1,adverseCompleteS31D2I2]
  have h := index_strict_order_from_intervals ((0/1)/1) ((0/1)/2) 0 0 (25235469/12500000) (71376697/50000000)
    (treeBonus (7/5) 7 1) (treeBonus (7/5) 7 2)
    (trajectory_bonus_7_1).1 (trajectory_bonus_7_2).2 (by norm_num)
  simpa only [treeIndex,sub_zero] using h

theorem adverseCompleteS31D2Cmp3 : indexScore (7/5) (controlPenalty savedCref uniformQuoteError unitRoleUnused .complete) adverseCompleteS31Before [.query 1,.hydeRetriever 0] (.selection 0) ≤ indexScore (7/5) (controlPenalty savedCref uniformQuoteError unitRoleUnused .complete) adverseCompleteS31Before [.query 1,.hydeRetriever 0] (.selection 3) := by
  rw [adverseCompleteS31D2I3,adverseCompleteS31D2I2]

theorem adverseCompleteS31Choice2 : nativeFirstChoice (indexScore (7/5) (controlPenalty savedCref uniformQuoteError unitRoleUnused .complete) adverseCompleteS31Before [.query 1,.hydeRetriever 0]) adverseCompleteS31Before [.query 1,.hydeRetriever 0] = .selection 3 := by
  apply visited_choice_from_ordered_certificate _ _ [.query 1,.hydeRetriever 0] [.selection 1,.selection 2] [.selection 0] (.selection 3) (by decide)
  · intro a ha
    have ho : orderedLegalAvailable [.query 1,.hydeRetriever 0] = [.selection 1,.selection 2,.selection 3,.selection 0] := by decide
    rw [ho] at ha
    simp only [List.mem_cons,List.not_mem_nil,or_false] at ha
    rcases ha with rfl | rfl | rfl | rfl <;> decide
  · intro a ha
    simp only [List.mem_cons,List.not_mem_nil,or_false] at ha
    rcases ha with rfl | rfl
    · exact adverseCompleteS31D2Cmp0
    · exact adverseCompleteS31D2Cmp1
  · intro a ha
    simp only [List.mem_cons,List.not_mem_nil,or_false] at ha
    rcases ha with rfl
    · exact adverseCompleteS31D2Cmp3

theorem adverseCompleteS31ActualEvent : nativeEvent budgetTape (7/5) (controlPenalty savedCref uniformQuoteError unitRoleUnused .complete)
    (taskReward true (2/5) (1/2)) adverseCompleteS31Before = adverseCompleteEvent31 := by
  have hs0 := native_select_existing_step budgetTape (7/5) (controlPenalty savedCref uniformQuoteError unitRoleUnused .complete) adverseCompleteS31Before 8 [] (.query 1)
    (by decide) (by decide) adverseCompleteS31Choice0
  have hs1 := native_select_existing_step budgetTape (7/5) (controlPenalty savedCref uniformQuoteError unitRoleUnused .complete) adverseCompleteS31Before 7 [.query 1] (.hydeRetriever 0)
    (by decide) (by decide) adverseCompleteS31Choice1
  have hs2 := native_select_existing_step budgetTape (7/5) (controlPenalty savedCref uniformQuoteError unitRoleUnused .complete) adverseCompleteS31Before 6 [.query 1,.hydeRetriever 0] (.selection 3)
    (by decide) (by decide) adverseCompleteS31Choice2
  have hnew := native_select_new_step budgetTape (7/5) (controlPenalty savedCref uniformQuoteError unitRoleUnused .complete) adverseCompleteS31Before 5 [.query 1,.hydeRetriever 0,.selection 3]
    [.width 3,.width 0,.width 1,.width 2] (.width 0) (by decide) (by decide) (by decide) (by decide)
  have hs : nativeSelect budgetTape (7/5) (controlPenalty savedCref uniformQuoteError unitRoleUnused .complete) adverseCompleteS31Before 9 [] = [.query 1,.hydeRetriever 0,.selection 3,.width 0] := by
    rw [hs0]
    change nativeSelect budgetTape (7/5) (controlPenalty savedCref uniformQuoteError unitRoleUnused .complete) adverseCompleteS31Before 8 [.query 1] = _
    rw [hs1]
    change nativeSelect budgetTape (7/5) (controlPenalty savedCref uniformQuoteError unitRoleUnused .complete) adverseCompleteS31Before 7 [.query 1,.hydeRetriever 0] = _
    rw [hs2]
    change nativeSelect budgetTape (7/5) (controlPenalty savedCref uniformQuoteError unitRoleUnused .complete) adverseCompleteS31Before 6 [.query 1,.hydeRetriever 0,.selection 3] = _
    rw [hnew] <;> rfl
  have hr : repairedRollout budgetTape adverseCompleteS31Before 9 [.query 1,.hydeRetriever 0,.selection 3,.width 0] = [.query 1,.hydeRetriever 0,.selection 3,.width 0,.stop,.reranker 0,.topm 0,.context 0,.answer 0] := by decide
  simp only [nativeEvent,hs,hr]
  rfl

def adverseCompleteS32Before := adverseCompleteProposal.take 31

theorem adverseCompleteS32Choice0 : nativeFirstChoice (indexScore (7/5) (controlPenalty savedCref uniformQuoteError unitRoleUnused .complete) adverseCompleteS32Before []) adverseCompleteS32Before [] = .query 1 := by
  apply complete_root_from_physical_gap adverseCompleteS32Before (adverseComplete_prefix_rewards 31) (by decide)
  · intro q; fin_cases q <;> decide
  · exact AgentUCTNextExact.adverse_complete_hyde_root_suffix_empty 31 (by omega)
  · intro q hq
    exact AgentUCTNextExact.adverse_complete_normal_root_physical_quote_exact 31 (by omega) q hq

theorem adverseCompleteS32D1I0 : indexScore (7/5) (controlPenalty savedCref uniformQuoteError unitRoleUnused .complete) adverseCompleteS32Before [.query 1] (.hydeRetriever 1) = treeIndex ((0/1)/8) (7/5) 0 24 8 := by
  have hs : replayBackup adverseCompleteS32Before emptyStatistics ([.query 1]++[.hydeRetriever 1]) = ⟨8,(0/1)⟩ := by
    rw [replayBackup_empty_closed_form]
    simp +decide [backedEvents,adverseCompleteS32Before,adverseCompleteProposal,adverseCompleteEvent1,adverseCompleteEvent2,adverseCompleteEvent3,adverseCompleteEvent4,adverseCompleteEvent5,adverseCompleteEvent6,adverseCompleteEvent7,adverseCompleteEvent8,adverseCompleteEvent9,adverseCompleteEvent10,adverseCompleteEvent11,adverseCompleteEvent12,adverseCompleteEvent13,adverseCompleteEvent14,adverseCompleteEvent15,adverseCompleteEvent16,adverseCompleteEvent17,adverseCompleteEvent18,adverseCompleteEvent19,adverseCompleteEvent20,adverseCompleteEvent21,adverseCompleteEvent22,adverseCompleteEvent23,adverseCompleteEvent24,adverseCompleteEvent25,adverseCompleteEvent26,adverseCompleteEvent27,adverseCompleteEvent28,adverseCompleteEvent29,adverseCompleteEvent30,adverseCompleteEvent31,taskReward]
    <;> norm_num
  have hp : rawVisits adverseCompleteS32Before [.query 1] = 24 := by decide
  have hn : rawVisits adverseCompleteS32Before ([.query 1]++[.hydeRetriever 1]) = 8 := by decide
  have hz : (controlPenalty savedCref uniformQuoteError unitRoleUnused .complete) adverseCompleteS32Before [.query 1] (.hydeRetriever 1) = 0 := by
    apply control_penalty_empty_of_prior_terminal .complete savedCref uniformQuoteError adverseCompleteS32Before [.query 1] (.hydeRetriever 1) 8 (by decide)
    · decide
    · decide
  unfold indexScore
  rw [hs,hp,hn,hz]
  simp only [BackupStat.mean]
  norm_num

theorem adverseCompleteS32D1I1 : indexScore (7/5) (controlPenalty savedCref uniformQuoteError unitRoleUnused .complete) adverseCompleteS32Before [.query 1] (.hydeRetriever 0) = treeIndex ((0/1)/8) (7/5) 0 24 8 := by
  have hs : replayBackup adverseCompleteS32Before emptyStatistics ([.query 1]++[.hydeRetriever 0]) = ⟨8,(0/1)⟩ := by
    rw [replayBackup_empty_closed_form]
    simp +decide [backedEvents,adverseCompleteS32Before,adverseCompleteProposal,adverseCompleteEvent1,adverseCompleteEvent2,adverseCompleteEvent3,adverseCompleteEvent4,adverseCompleteEvent5,adverseCompleteEvent6,adverseCompleteEvent7,adverseCompleteEvent8,adverseCompleteEvent9,adverseCompleteEvent10,adverseCompleteEvent11,adverseCompleteEvent12,adverseCompleteEvent13,adverseCompleteEvent14,adverseCompleteEvent15,adverseCompleteEvent16,adverseCompleteEvent17,adverseCompleteEvent18,adverseCompleteEvent19,adverseCompleteEvent20,adverseCompleteEvent21,adverseCompleteEvent22,adverseCompleteEvent23,adverseCompleteEvent24,adverseCompleteEvent25,adverseCompleteEvent26,adverseCompleteEvent27,adverseCompleteEvent28,adverseCompleteEvent29,adverseCompleteEvent30,adverseCompleteEvent31,taskReward]
    <;> norm_num
  have hp : rawVisits adverseCompleteS32Before [.query 1] = 24 := by decide
  have hn : rawVisits adverseCompleteS32Before ([.query 1]++[.hydeRetriever 0]) = 8 := by decide
  have hz : (controlPenalty savedCref uniformQuoteError unitRoleUnused .complete) adverseCompleteS32Before [.query 1] (.hydeRetriever 0) = 0 := by
    apply control_penalty_empty_of_prior_terminal .complete savedCref uniformQuoteError adverseCompleteS32Before [.query 1] (.hydeRetriever 0) 1 (by decide)
    · decide
    · decide
  unfold indexScore
  rw [hs,hp,hn,hz]
  simp only [BackupStat.mean]
  norm_num

theorem adverseCompleteS32D1I2 : indexScore (7/5) (controlPenalty savedCref uniformQuoteError unitRoleUnused .complete) adverseCompleteS32Before [.query 1] (.hydeRetriever 2) = treeIndex ((0/1)/7) (7/5) 0 24 7 := by
  have hs : replayBackup adverseCompleteS32Before emptyStatistics ([.query 1]++[.hydeRetriever 2]) = ⟨7,(0/1)⟩ := by
    rw [replayBackup_empty_closed_form]
    simp +decide [backedEvents,adverseCompleteS32Before,adverseCompleteProposal,adverseCompleteEvent1,adverseCompleteEvent2,adverseCompleteEvent3,adverseCompleteEvent4,adverseCompleteEvent5,adverseCompleteEvent6,adverseCompleteEvent7,adverseCompleteEvent8,adverseCompleteEvent9,adverseCompleteEvent10,adverseCompleteEvent11,adverseCompleteEvent12,adverseCompleteEvent13,adverseCompleteEvent14,adverseCompleteEvent15,adverseCompleteEvent16,adverseCompleteEvent17,adverseCompleteEvent18,adverseCompleteEvent19,adverseCompleteEvent20,adverseCompleteEvent21,adverseCompleteEvent22,adverseCompleteEvent23,adverseCompleteEvent24,adverseCompleteEvent25,adverseCompleteEvent26,adverseCompleteEvent27,adverseCompleteEvent28,adverseCompleteEvent29,adverseCompleteEvent30,adverseCompleteEvent31,taskReward]
    <;> norm_num
  have hp : rawVisits adverseCompleteS32Before [.query 1] = 24 := by decide
  have hn : rawVisits adverseCompleteS32Before ([.query 1]++[.hydeRetriever 2]) = 7 := by decide
  have hz : (controlPenalty savedCref uniformQuoteError unitRoleUnused .complete) adverseCompleteS32Before [.query 1] (.hydeRetriever 2) = 0 := by
    apply control_penalty_empty_of_prior_terminal .complete savedCref uniformQuoteError adverseCompleteS32Before [.query 1] (.hydeRetriever 2) 10 (by decide)
    · decide
    · decide
  unfold indexScore
  rw [hs,hp,hn,hz]
  simp only [BackupStat.mean]
  norm_num

theorem adverseCompleteS32D1Cmp0 : indexScore (7/5) (controlPenalty savedCref uniformQuoteError unitRoleUnused .complete) adverseCompleteS32Before [.query 1] (.hydeRetriever 1) < indexScore (7/5) (controlPenalty savedCref uniformQuoteError unitRoleUnused .complete) adverseCompleteS32Before [.query 1] (.hydeRetriever 2) := by
  rw [adverseCompleteS32D1I0,adverseCompleteS32D1I2]
  have h := index_strict_order_from_intervals ((0/1)/7) ((0/1)/8) 0 0 (9493603/10000000) (22201137/25000000)
    (treeBonus (7/5) 24 7) (treeBonus (7/5) 24 8)
    (trajectory_bonus_24_7).1 (trajectory_bonus_24_8).2 (by norm_num)
  simpa only [treeIndex,sub_zero] using h

theorem adverseCompleteS32D1Cmp1 : indexScore (7/5) (controlPenalty savedCref uniformQuoteError unitRoleUnused .complete) adverseCompleteS32Before [.query 1] (.hydeRetriever 0) < indexScore (7/5) (controlPenalty savedCref uniformQuoteError unitRoleUnused .complete) adverseCompleteS32Before [.query 1] (.hydeRetriever 2) := by
  rw [adverseCompleteS32D1I1,adverseCompleteS32D1I2]
  have h := index_strict_order_from_intervals ((0/1)/7) ((0/1)/8) 0 0 (9493603/10000000) (22201137/25000000)
    (treeBonus (7/5) 24 7) (treeBonus (7/5) 24 8)
    (trajectory_bonus_24_7).1 (trajectory_bonus_24_8).2 (by norm_num)
  simpa only [treeIndex,sub_zero] using h

theorem adverseCompleteS32Choice1 : nativeFirstChoice (indexScore (7/5) (controlPenalty savedCref uniformQuoteError unitRoleUnused .complete) adverseCompleteS32Before [.query 1]) adverseCompleteS32Before [.query 1] = .hydeRetriever 2 := by
  apply visited_choice_from_ordered_certificate _ _ [.query 1] [.hydeRetriever 1,.hydeRetriever 0] [] (.hydeRetriever 2) (by decide)
  · intro a ha
    have ho : orderedLegalAvailable [.query 1] = [.hydeRetriever 1,.hydeRetriever 0,.hydeRetriever 2] := by decide
    rw [ho] at ha
    simp only [List.mem_cons,List.not_mem_nil,or_false] at ha
    rcases ha with rfl | rfl | rfl <;> decide
  · intro a ha
    simp only [List.mem_cons,List.not_mem_nil,or_false] at ha
    rcases ha with rfl | rfl
    · exact adverseCompleteS32D1Cmp0
    · exact adverseCompleteS32D1Cmp1
  · simp

theorem adverseCompleteS32D2I0 : indexScore (7/5) (controlPenalty savedCref uniformQuoteError unitRoleUnused .complete) adverseCompleteS32Before [.query 1,.hydeRetriever 2] (.selection 1) = treeIndex ((0/1)/2) (7/5) 0 7 2 := by
  have hs : replayBackup adverseCompleteS32Before emptyStatistics ([.query 1,.hydeRetriever 2]++[.selection 1]) = ⟨2,(0/1)⟩ := by
    rw [replayBackup_empty_closed_form]
    simp +decide [backedEvents,adverseCompleteS32Before,adverseCompleteProposal,adverseCompleteEvent1,adverseCompleteEvent2,adverseCompleteEvent3,adverseCompleteEvent4,adverseCompleteEvent5,adverseCompleteEvent6,adverseCompleteEvent7,adverseCompleteEvent8,adverseCompleteEvent9,adverseCompleteEvent10,adverseCompleteEvent11,adverseCompleteEvent12,adverseCompleteEvent13,adverseCompleteEvent14,adverseCompleteEvent15,adverseCompleteEvent16,adverseCompleteEvent17,adverseCompleteEvent18,adverseCompleteEvent19,adverseCompleteEvent20,adverseCompleteEvent21,adverseCompleteEvent22,adverseCompleteEvent23,adverseCompleteEvent24,adverseCompleteEvent25,adverseCompleteEvent26,adverseCompleteEvent27,adverseCompleteEvent28,adverseCompleteEvent29,adverseCompleteEvent30,adverseCompleteEvent31,taskReward]
    <;> norm_num
  have hp : rawVisits adverseCompleteS32Before [.query 1,.hydeRetriever 2] = 7 := by decide
  have hn : rawVisits adverseCompleteS32Before ([.query 1,.hydeRetriever 2]++[.selection 1]) = 2 := by decide
  have hz : (controlPenalty savedCref uniformQuoteError unitRoleUnused .complete) adverseCompleteS32Before [.query 1,.hydeRetriever 2] (.selection 1) = 0 := by
    apply control_penalty_empty_of_prior_terminal .complete savedCref uniformQuoteError adverseCompleteS32Before [.query 1,.hydeRetriever 2] (.selection 1) 16 (by decide)
    · decide
    · decide
  unfold indexScore
  rw [hs,hp,hn,hz]
  simp only [BackupStat.mean]
  norm_num

theorem adverseCompleteS32D2I1 : indexScore (7/5) (controlPenalty savedCref uniformQuoteError unitRoleUnused .complete) adverseCompleteS32Before [.query 1,.hydeRetriever 2] (.selection 2) = treeIndex ((0/1)/2) (7/5) 0 7 2 := by
  have hs : replayBackup adverseCompleteS32Before emptyStatistics ([.query 1,.hydeRetriever 2]++[.selection 2]) = ⟨2,(0/1)⟩ := by
    rw [replayBackup_empty_closed_form]
    simp +decide [backedEvents,adverseCompleteS32Before,adverseCompleteProposal,adverseCompleteEvent1,adverseCompleteEvent2,adverseCompleteEvent3,adverseCompleteEvent4,adverseCompleteEvent5,adverseCompleteEvent6,adverseCompleteEvent7,adverseCompleteEvent8,adverseCompleteEvent9,adverseCompleteEvent10,adverseCompleteEvent11,adverseCompleteEvent12,adverseCompleteEvent13,adverseCompleteEvent14,adverseCompleteEvent15,adverseCompleteEvent16,adverseCompleteEvent17,adverseCompleteEvent18,adverseCompleteEvent19,adverseCompleteEvent20,adverseCompleteEvent21,adverseCompleteEvent22,adverseCompleteEvent23,adverseCompleteEvent24,adverseCompleteEvent25,adverseCompleteEvent26,adverseCompleteEvent27,adverseCompleteEvent28,adverseCompleteEvent29,adverseCompleteEvent30,adverseCompleteEvent31,taskReward]
    <;> norm_num
  have hp : rawVisits adverseCompleteS32Before [.query 1,.hydeRetriever 2] = 7 := by decide
  have hn : rawVisits adverseCompleteS32Before ([.query 1,.hydeRetriever 2]++[.selection 2]) = 2 := by decide
  have hz : (controlPenalty savedCref uniformQuoteError unitRoleUnused .complete) adverseCompleteS32Before [.query 1,.hydeRetriever 2] (.selection 2) = 0 := by
    apply control_penalty_empty_of_prior_terminal .complete savedCref uniformQuoteError adverseCompleteS32Before [.query 1,.hydeRetriever 2] (.selection 2) 19 (by decide)
    · decide
    · decide
  unfold indexScore
  rw [hs,hp,hn,hz]
  simp only [BackupStat.mean]
  norm_num

theorem adverseCompleteS32D2I2 : indexScore (7/5) (controlPenalty savedCref uniformQuoteError unitRoleUnused .complete) adverseCompleteS32Before [.query 1,.hydeRetriever 2] (.selection 3) = treeIndex ((0/1)/1) (7/5) 0 7 1 := by
  have hs : replayBackup adverseCompleteS32Before emptyStatistics ([.query 1,.hydeRetriever 2]++[.selection 3]) = ⟨1,(0/1)⟩ := by
    rw [replayBackup_empty_closed_form]
    simp +decide [backedEvents,adverseCompleteS32Before,adverseCompleteProposal,adverseCompleteEvent1,adverseCompleteEvent2,adverseCompleteEvent3,adverseCompleteEvent4,adverseCompleteEvent5,adverseCompleteEvent6,adverseCompleteEvent7,adverseCompleteEvent8,adverseCompleteEvent9,adverseCompleteEvent10,adverseCompleteEvent11,adverseCompleteEvent12,adverseCompleteEvent13,adverseCompleteEvent14,adverseCompleteEvent15,adverseCompleteEvent16,adverseCompleteEvent17,adverseCompleteEvent18,adverseCompleteEvent19,adverseCompleteEvent20,adverseCompleteEvent21,adverseCompleteEvent22,adverseCompleteEvent23,adverseCompleteEvent24,adverseCompleteEvent25,adverseCompleteEvent26,adverseCompleteEvent27,adverseCompleteEvent28,adverseCompleteEvent29,adverseCompleteEvent30,adverseCompleteEvent31,taskReward]
    <;> norm_num
  have hp : rawVisits adverseCompleteS32Before [.query 1,.hydeRetriever 2] = 7 := by decide
  have hn : rawVisits adverseCompleteS32Before ([.query 1,.hydeRetriever 2]++[.selection 3]) = 1 := by decide
  have hz : (controlPenalty savedCref uniformQuoteError unitRoleUnused .complete) adverseCompleteS32Before [.query 1,.hydeRetriever 2] (.selection 3) = 0 := by
    apply control_penalty_empty_of_prior_terminal .complete savedCref uniformQuoteError adverseCompleteS32Before [.query 1,.hydeRetriever 2] (.selection 3) 22 (by decide)
    · decide
    · decide
  unfold indexScore
  rw [hs,hp,hn,hz]
  simp only [BackupStat.mean]
  norm_num

theorem adverseCompleteS32D2I3 : indexScore (7/5) (controlPenalty savedCref uniformQuoteError unitRoleUnused .complete) adverseCompleteS32Before [.query 1,.hydeRetriever 2] (.selection 0) = treeIndex ((0/1)/1) (7/5) 0 7 1 := by
  have hs : replayBackup adverseCompleteS32Before emptyStatistics ([.query 1,.hydeRetriever 2]++[.selection 0]) = ⟨1,(0/1)⟩ := by
    rw [replayBackup_empty_closed_form]
    simp +decide [backedEvents,adverseCompleteS32Before,adverseCompleteProposal,adverseCompleteEvent1,adverseCompleteEvent2,adverseCompleteEvent3,adverseCompleteEvent4,adverseCompleteEvent5,adverseCompleteEvent6,adverseCompleteEvent7,adverseCompleteEvent8,adverseCompleteEvent9,adverseCompleteEvent10,adverseCompleteEvent11,adverseCompleteEvent12,adverseCompleteEvent13,adverseCompleteEvent14,adverseCompleteEvent15,adverseCompleteEvent16,adverseCompleteEvent17,adverseCompleteEvent18,adverseCompleteEvent19,adverseCompleteEvent20,adverseCompleteEvent21,adverseCompleteEvent22,adverseCompleteEvent23,adverseCompleteEvent24,adverseCompleteEvent25,adverseCompleteEvent26,adverseCompleteEvent27,adverseCompleteEvent28,adverseCompleteEvent29,adverseCompleteEvent30,adverseCompleteEvent31,taskReward]
    <;> norm_num
  have hp : rawVisits adverseCompleteS32Before [.query 1,.hydeRetriever 2] = 7 := by decide
  have hn : rawVisits adverseCompleteS32Before ([.query 1,.hydeRetriever 2]++[.selection 0]) = 1 := by decide
  have hz : (controlPenalty savedCref uniformQuoteError unitRoleUnused .complete) adverseCompleteS32Before [.query 1,.hydeRetriever 2] (.selection 0) = 0 := by
    apply control_penalty_empty_of_prior_terminal .complete savedCref uniformQuoteError adverseCompleteS32Before [.query 1,.hydeRetriever 2] (.selection 0) 10 (by decide)
    · decide
    · decide
  unfold indexScore
  rw [hs,hp,hn,hz]
  simp only [BackupStat.mean]
  norm_num

theorem adverseCompleteS32D2Cmp0 : indexScore (7/5) (controlPenalty savedCref uniformQuoteError unitRoleUnused .complete) adverseCompleteS32Before [.query 1,.hydeRetriever 2] (.selection 1) < indexScore (7/5) (controlPenalty savedCref uniformQuoteError unitRoleUnused .complete) adverseCompleteS32Before [.query 1,.hydeRetriever 2] (.selection 3) := by
  rw [adverseCompleteS32D2I0,adverseCompleteS32D2I2]
  have h := index_strict_order_from_intervals ((0/1)/1) ((0/1)/2) 0 0 (25235469/12500000) (71376697/50000000)
    (treeBonus (7/5) 7 1) (treeBonus (7/5) 7 2)
    (trajectory_bonus_7_1).1 (trajectory_bonus_7_2).2 (by norm_num)
  simpa only [treeIndex,sub_zero] using h

theorem adverseCompleteS32D2Cmp1 : indexScore (7/5) (controlPenalty savedCref uniformQuoteError unitRoleUnused .complete) adverseCompleteS32Before [.query 1,.hydeRetriever 2] (.selection 2) < indexScore (7/5) (controlPenalty savedCref uniformQuoteError unitRoleUnused .complete) adverseCompleteS32Before [.query 1,.hydeRetriever 2] (.selection 3) := by
  rw [adverseCompleteS32D2I1,adverseCompleteS32D2I2]
  have h := index_strict_order_from_intervals ((0/1)/1) ((0/1)/2) 0 0 (25235469/12500000) (71376697/50000000)
    (treeBonus (7/5) 7 1) (treeBonus (7/5) 7 2)
    (trajectory_bonus_7_1).1 (trajectory_bonus_7_2).2 (by norm_num)
  simpa only [treeIndex,sub_zero] using h

theorem adverseCompleteS32D2Cmp3 : indexScore (7/5) (controlPenalty savedCref uniformQuoteError unitRoleUnused .complete) adverseCompleteS32Before [.query 1,.hydeRetriever 2] (.selection 0) ≤ indexScore (7/5) (controlPenalty savedCref uniformQuoteError unitRoleUnused .complete) adverseCompleteS32Before [.query 1,.hydeRetriever 2] (.selection 3) := by
  rw [adverseCompleteS32D2I3,adverseCompleteS32D2I2]

theorem adverseCompleteS32Choice2 : nativeFirstChoice (indexScore (7/5) (controlPenalty savedCref uniformQuoteError unitRoleUnused .complete) adverseCompleteS32Before [.query 1,.hydeRetriever 2]) adverseCompleteS32Before [.query 1,.hydeRetriever 2] = .selection 3 := by
  apply visited_choice_from_ordered_certificate _ _ [.query 1,.hydeRetriever 2] [.selection 1,.selection 2] [.selection 0] (.selection 3) (by decide)
  · intro a ha
    have ho : orderedLegalAvailable [.query 1,.hydeRetriever 2] = [.selection 1,.selection 2,.selection 3,.selection 0] := by decide
    rw [ho] at ha
    simp only [List.mem_cons,List.not_mem_nil,or_false] at ha
    rcases ha with rfl | rfl | rfl | rfl <;> decide
  · intro a ha
    simp only [List.mem_cons,List.not_mem_nil,or_false] at ha
    rcases ha with rfl | rfl
    · exact adverseCompleteS32D2Cmp0
    · exact adverseCompleteS32D2Cmp1
  · intro a ha
    simp only [List.mem_cons,List.not_mem_nil,or_false] at ha
    rcases ha with rfl
    · exact adverseCompleteS32D2Cmp3

theorem adverseCompleteS32ActualEvent : nativeEvent budgetTape (7/5) (controlPenalty savedCref uniformQuoteError unitRoleUnused .complete)
    (taskReward true (2/5) (1/2)) adverseCompleteS32Before = adverseCompleteEvent32 := by
  have hs0 := native_select_existing_step budgetTape (7/5) (controlPenalty savedCref uniformQuoteError unitRoleUnused .complete) adverseCompleteS32Before 8 [] (.query 1)
    (by decide) (by decide) adverseCompleteS32Choice0
  have hs1 := native_select_existing_step budgetTape (7/5) (controlPenalty savedCref uniformQuoteError unitRoleUnused .complete) adverseCompleteS32Before 7 [.query 1] (.hydeRetriever 2)
    (by decide) (by decide) adverseCompleteS32Choice1
  have hs2 := native_select_existing_step budgetTape (7/5) (controlPenalty savedCref uniformQuoteError unitRoleUnused .complete) adverseCompleteS32Before 6 [.query 1,.hydeRetriever 2] (.selection 3)
    (by decide) (by decide) adverseCompleteS32Choice2
  have hnew := native_select_new_step budgetTape (7/5) (controlPenalty savedCref uniformQuoteError unitRoleUnused .complete) adverseCompleteS32Before 5 [.query 1,.hydeRetriever 2,.selection 3]
    [.width 3,.width 0,.width 1,.width 2] (.width 0) (by decide) (by decide) (by decide) (by decide)
  have hs : nativeSelect budgetTape (7/5) (controlPenalty savedCref uniformQuoteError unitRoleUnused .complete) adverseCompleteS32Before 9 [] = [.query 1,.hydeRetriever 2,.selection 3,.width 0] := by
    rw [hs0]
    change nativeSelect budgetTape (7/5) (controlPenalty savedCref uniformQuoteError unitRoleUnused .complete) adverseCompleteS32Before 8 [.query 1] = _
    rw [hs1]
    change nativeSelect budgetTape (7/5) (controlPenalty savedCref uniformQuoteError unitRoleUnused .complete) adverseCompleteS32Before 7 [.query 1,.hydeRetriever 2] = _
    rw [hs2]
    change nativeSelect budgetTape (7/5) (controlPenalty savedCref uniformQuoteError unitRoleUnused .complete) adverseCompleteS32Before 6 [.query 1,.hydeRetriever 2,.selection 3] = _
    rw [hnew] <;> rfl
  have hr : repairedRollout budgetTape adverseCompleteS32Before 9 [.query 1,.hydeRetriever 2,.selection 3,.width 0] = [.query 1,.hydeRetriever 2,.selection 3,.width 0,.stop,.reranker 0,.topm 0,.context 0,.answer 0] := by decide
  simp only [nativeEvent,hs,hr]
  rfl

def adverseCompleteS33Before := adverseCompleteProposal.take 32

theorem adverseCompleteS33Choice0 : nativeFirstChoice (indexScore (7/5) (controlPenalty savedCref uniformQuoteError unitRoleUnused .complete) adverseCompleteS33Before []) adverseCompleteS33Before [] = .query 1 := by
  apply complete_root_from_physical_gap adverseCompleteS33Before (adverseComplete_prefix_rewards 32) (by decide)
  · intro q; fin_cases q <;> decide
  · exact AgentUCTNextExact.adverse_complete_hyde_root_suffix_empty 32 (by omega)
  · intro q hq
    exact AgentUCTNextExact.adverse_complete_normal_root_physical_quote_exact 32 (by omega) q hq

theorem adverseCompleteS33D1I0 : indexScore (7/5) (controlPenalty savedCref uniformQuoteError unitRoleUnused .complete) adverseCompleteS33Before [.query 1] (.hydeRetriever 1) = treeIndex ((0/1)/8) (7/5) 0 25 8 := by
  have hs : replayBackup adverseCompleteS33Before emptyStatistics ([.query 1]++[.hydeRetriever 1]) = ⟨8,(0/1)⟩ := by
    rw [replayBackup_empty_closed_form]
    simp +decide [backedEvents,adverseCompleteS33Before,adverseCompleteProposal,adverseCompleteEvent1,adverseCompleteEvent2,adverseCompleteEvent3,adverseCompleteEvent4,adverseCompleteEvent5,adverseCompleteEvent6,adverseCompleteEvent7,adverseCompleteEvent8,adverseCompleteEvent9,adverseCompleteEvent10,adverseCompleteEvent11,adverseCompleteEvent12,adverseCompleteEvent13,adverseCompleteEvent14,adverseCompleteEvent15,adverseCompleteEvent16,adverseCompleteEvent17,adverseCompleteEvent18,adverseCompleteEvent19,adverseCompleteEvent20,adverseCompleteEvent21,adverseCompleteEvent22,adverseCompleteEvent23,adverseCompleteEvent24,adverseCompleteEvent25,adverseCompleteEvent26,adverseCompleteEvent27,adverseCompleteEvent28,adverseCompleteEvent29,adverseCompleteEvent30,adverseCompleteEvent31,adverseCompleteEvent32,taskReward]
    <;> norm_num
  have hp : rawVisits adverseCompleteS33Before [.query 1] = 25 := by decide
  have hn : rawVisits adverseCompleteS33Before ([.query 1]++[.hydeRetriever 1]) = 8 := by decide
  have hz : (controlPenalty savedCref uniformQuoteError unitRoleUnused .complete) adverseCompleteS33Before [.query 1] (.hydeRetriever 1) = 0 := by
    apply control_penalty_empty_of_prior_terminal .complete savedCref uniformQuoteError adverseCompleteS33Before [.query 1] (.hydeRetriever 1) 8 (by decide)
    · decide
    · decide
  unfold indexScore
  rw [hs,hp,hn,hz]
  simp only [BackupStat.mean]
  norm_num

theorem adverseCompleteS33D1I1 : indexScore (7/5) (controlPenalty savedCref uniformQuoteError unitRoleUnused .complete) adverseCompleteS33Before [.query 1] (.hydeRetriever 0) = treeIndex ((0/1)/8) (7/5) 0 25 8 := by
  have hs : replayBackup adverseCompleteS33Before emptyStatistics ([.query 1]++[.hydeRetriever 0]) = ⟨8,(0/1)⟩ := by
    rw [replayBackup_empty_closed_form]
    simp +decide [backedEvents,adverseCompleteS33Before,adverseCompleteProposal,adverseCompleteEvent1,adverseCompleteEvent2,adverseCompleteEvent3,adverseCompleteEvent4,adverseCompleteEvent5,adverseCompleteEvent6,adverseCompleteEvent7,adverseCompleteEvent8,adverseCompleteEvent9,adverseCompleteEvent10,adverseCompleteEvent11,adverseCompleteEvent12,adverseCompleteEvent13,adverseCompleteEvent14,adverseCompleteEvent15,adverseCompleteEvent16,adverseCompleteEvent17,adverseCompleteEvent18,adverseCompleteEvent19,adverseCompleteEvent20,adverseCompleteEvent21,adverseCompleteEvent22,adverseCompleteEvent23,adverseCompleteEvent24,adverseCompleteEvent25,adverseCompleteEvent26,adverseCompleteEvent27,adverseCompleteEvent28,adverseCompleteEvent29,adverseCompleteEvent30,adverseCompleteEvent31,adverseCompleteEvent32,taskReward]
    <;> norm_num
  have hp : rawVisits adverseCompleteS33Before [.query 1] = 25 := by decide
  have hn : rawVisits adverseCompleteS33Before ([.query 1]++[.hydeRetriever 0]) = 8 := by decide
  have hz : (controlPenalty savedCref uniformQuoteError unitRoleUnused .complete) adverseCompleteS33Before [.query 1] (.hydeRetriever 0) = 0 := by
    apply control_penalty_empty_of_prior_terminal .complete savedCref uniformQuoteError adverseCompleteS33Before [.query 1] (.hydeRetriever 0) 1 (by decide)
    · decide
    · decide
  unfold indexScore
  rw [hs,hp,hn,hz]
  simp only [BackupStat.mean]
  norm_num

theorem adverseCompleteS33D1I2 : indexScore (7/5) (controlPenalty savedCref uniformQuoteError unitRoleUnused .complete) adverseCompleteS33Before [.query 1] (.hydeRetriever 2) = treeIndex ((0/1)/8) (7/5) 0 25 8 := by
  have hs : replayBackup adverseCompleteS33Before emptyStatistics ([.query 1]++[.hydeRetriever 2]) = ⟨8,(0/1)⟩ := by
    rw [replayBackup_empty_closed_form]
    simp +decide [backedEvents,adverseCompleteS33Before,adverseCompleteProposal,adverseCompleteEvent1,adverseCompleteEvent2,adverseCompleteEvent3,adverseCompleteEvent4,adverseCompleteEvent5,adverseCompleteEvent6,adverseCompleteEvent7,adverseCompleteEvent8,adverseCompleteEvent9,adverseCompleteEvent10,adverseCompleteEvent11,adverseCompleteEvent12,adverseCompleteEvent13,adverseCompleteEvent14,adverseCompleteEvent15,adverseCompleteEvent16,adverseCompleteEvent17,adverseCompleteEvent18,adverseCompleteEvent19,adverseCompleteEvent20,adverseCompleteEvent21,adverseCompleteEvent22,adverseCompleteEvent23,adverseCompleteEvent24,adverseCompleteEvent25,adverseCompleteEvent26,adverseCompleteEvent27,adverseCompleteEvent28,adverseCompleteEvent29,adverseCompleteEvent30,adverseCompleteEvent31,adverseCompleteEvent32,taskReward]
    <;> norm_num
  have hp : rawVisits adverseCompleteS33Before [.query 1] = 25 := by decide
  have hn : rawVisits adverseCompleteS33Before ([.query 1]++[.hydeRetriever 2]) = 8 := by decide
  have hz : (controlPenalty savedCref uniformQuoteError unitRoleUnused .complete) adverseCompleteS33Before [.query 1] (.hydeRetriever 2) = 0 := by
    apply control_penalty_empty_of_prior_terminal .complete savedCref uniformQuoteError adverseCompleteS33Before [.query 1] (.hydeRetriever 2) 10 (by decide)
    · decide
    · decide
  unfold indexScore
  rw [hs,hp,hn,hz]
  simp only [BackupStat.mean]
  norm_num

theorem adverseCompleteS33D1Cmp1 : indexScore (7/5) (controlPenalty savedCref uniformQuoteError unitRoleUnused .complete) adverseCompleteS33Before [.query 1] (.hydeRetriever 0) ≤ indexScore (7/5) (controlPenalty savedCref uniformQuoteError unitRoleUnused .complete) adverseCompleteS33Before [.query 1] (.hydeRetriever 1) := by
  rw [adverseCompleteS33D1I1,adverseCompleteS33D1I0]

theorem adverseCompleteS33D1Cmp2 : indexScore (7/5) (controlPenalty savedCref uniformQuoteError unitRoleUnused .complete) adverseCompleteS33Before [.query 1] (.hydeRetriever 2) ≤ indexScore (7/5) (controlPenalty savedCref uniformQuoteError unitRoleUnused .complete) adverseCompleteS33Before [.query 1] (.hydeRetriever 1) := by
  rw [adverseCompleteS33D1I2,adverseCompleteS33D1I0]

theorem adverseCompleteS33Choice1 : nativeFirstChoice (indexScore (7/5) (controlPenalty savedCref uniformQuoteError unitRoleUnused .complete) adverseCompleteS33Before [.query 1]) adverseCompleteS33Before [.query 1] = .hydeRetriever 1 := by
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
    · exact adverseCompleteS33D1Cmp1
    · exact adverseCompleteS33D1Cmp2

theorem adverseCompleteS33D2I0 : indexScore (7/5) (controlPenalty savedCref uniformQuoteError unitRoleUnused .complete) adverseCompleteS33Before [.query 1,.hydeRetriever 1] (.selection 1) = treeIndex ((0/1)/2) (7/5) 0 8 2 := by
  have hs : replayBackup adverseCompleteS33Before emptyStatistics ([.query 1,.hydeRetriever 1]++[.selection 1]) = ⟨2,(0/1)⟩ := by
    rw [replayBackup_empty_closed_form]
    simp +decide [backedEvents,adverseCompleteS33Before,adverseCompleteProposal,adverseCompleteEvent1,adverseCompleteEvent2,adverseCompleteEvent3,adverseCompleteEvent4,adverseCompleteEvent5,adverseCompleteEvent6,adverseCompleteEvent7,adverseCompleteEvent8,adverseCompleteEvent9,adverseCompleteEvent10,adverseCompleteEvent11,adverseCompleteEvent12,adverseCompleteEvent13,adverseCompleteEvent14,adverseCompleteEvent15,adverseCompleteEvent16,adverseCompleteEvent17,adverseCompleteEvent18,adverseCompleteEvent19,adverseCompleteEvent20,adverseCompleteEvent21,adverseCompleteEvent22,adverseCompleteEvent23,adverseCompleteEvent24,adverseCompleteEvent25,adverseCompleteEvent26,adverseCompleteEvent27,adverseCompleteEvent28,adverseCompleteEvent29,adverseCompleteEvent30,adverseCompleteEvent31,adverseCompleteEvent32,taskReward]
    <;> norm_num
  have hp : rawVisits adverseCompleteS33Before [.query 1,.hydeRetriever 1] = 8 := by decide
  have hn : rawVisits adverseCompleteS33Before ([.query 1,.hydeRetriever 1]++[.selection 1]) = 2 := by decide
  have hz : (controlPenalty savedCref uniformQuoteError unitRoleUnused .complete) adverseCompleteS33Before [.query 1,.hydeRetriever 1] (.selection 1) = 0 := by
    apply control_penalty_empty_of_prior_terminal .complete savedCref uniformQuoteError adverseCompleteS33Before [.query 1,.hydeRetriever 1] (.selection 1) 14 (by decide)
    · decide
    · decide
  unfold indexScore
  rw [hs,hp,hn,hz]
  simp only [BackupStat.mean]
  norm_num

theorem adverseCompleteS33D2I1 : indexScore (7/5) (controlPenalty savedCref uniformQuoteError unitRoleUnused .complete) adverseCompleteS33Before [.query 1,.hydeRetriever 1] (.selection 2) = treeIndex ((0/1)/2) (7/5) 0 8 2 := by
  have hs : replayBackup adverseCompleteS33Before emptyStatistics ([.query 1,.hydeRetriever 1]++[.selection 2]) = ⟨2,(0/1)⟩ := by
    rw [replayBackup_empty_closed_form]
    simp +decide [backedEvents,adverseCompleteS33Before,adverseCompleteProposal,adverseCompleteEvent1,adverseCompleteEvent2,adverseCompleteEvent3,adverseCompleteEvent4,adverseCompleteEvent5,adverseCompleteEvent6,adverseCompleteEvent7,adverseCompleteEvent8,adverseCompleteEvent9,adverseCompleteEvent10,adverseCompleteEvent11,adverseCompleteEvent12,adverseCompleteEvent13,adverseCompleteEvent14,adverseCompleteEvent15,adverseCompleteEvent16,adverseCompleteEvent17,adverseCompleteEvent18,adverseCompleteEvent19,adverseCompleteEvent20,adverseCompleteEvent21,adverseCompleteEvent22,adverseCompleteEvent23,adverseCompleteEvent24,adverseCompleteEvent25,adverseCompleteEvent26,adverseCompleteEvent27,adverseCompleteEvent28,adverseCompleteEvent29,adverseCompleteEvent30,adverseCompleteEvent31,adverseCompleteEvent32,taskReward]
    <;> norm_num
  have hp : rawVisits adverseCompleteS33Before [.query 1,.hydeRetriever 1] = 8 := by decide
  have hn : rawVisits adverseCompleteS33Before ([.query 1,.hydeRetriever 1]++[.selection 2]) = 2 := by decide
  have hz : (controlPenalty savedCref uniformQuoteError unitRoleUnused .complete) adverseCompleteS33Before [.query 1,.hydeRetriever 1] (.selection 2) = 0 := by
    apply control_penalty_empty_of_prior_terminal .complete savedCref uniformQuoteError adverseCompleteS33Before [.query 1,.hydeRetriever 1] (.selection 2) 17 (by decide)
    · decide
    · decide
  unfold indexScore
  rw [hs,hp,hn,hz]
  simp only [BackupStat.mean]
  norm_num

theorem adverseCompleteS33D2I2 : indexScore (7/5) (controlPenalty savedCref uniformQuoteError unitRoleUnused .complete) adverseCompleteS33Before [.query 1,.hydeRetriever 1] (.selection 3) = treeIndex ((0/1)/2) (7/5) 0 8 2 := by
  have hs : replayBackup adverseCompleteS33Before emptyStatistics ([.query 1,.hydeRetriever 1]++[.selection 3]) = ⟨2,(0/1)⟩ := by
    rw [replayBackup_empty_closed_form]
    simp +decide [backedEvents,adverseCompleteS33Before,adverseCompleteProposal,adverseCompleteEvent1,adverseCompleteEvent2,adverseCompleteEvent3,adverseCompleteEvent4,adverseCompleteEvent5,adverseCompleteEvent6,adverseCompleteEvent7,adverseCompleteEvent8,adverseCompleteEvent9,adverseCompleteEvent10,adverseCompleteEvent11,adverseCompleteEvent12,adverseCompleteEvent13,adverseCompleteEvent14,adverseCompleteEvent15,adverseCompleteEvent16,adverseCompleteEvent17,adverseCompleteEvent18,adverseCompleteEvent19,adverseCompleteEvent20,adverseCompleteEvent21,adverseCompleteEvent22,adverseCompleteEvent23,adverseCompleteEvent24,adverseCompleteEvent25,adverseCompleteEvent26,adverseCompleteEvent27,adverseCompleteEvent28,adverseCompleteEvent29,adverseCompleteEvent30,adverseCompleteEvent31,adverseCompleteEvent32,taskReward]
    <;> norm_num
  have hp : rawVisits adverseCompleteS33Before [.query 1,.hydeRetriever 1] = 8 := by decide
  have hn : rawVisits adverseCompleteS33Before ([.query 1,.hydeRetriever 1]++[.selection 3]) = 2 := by decide
  have hz : (controlPenalty savedCref uniformQuoteError unitRoleUnused .complete) adverseCompleteS33Before [.query 1,.hydeRetriever 1] (.selection 3) = 0 := by
    apply control_penalty_empty_of_prior_terminal .complete savedCref uniformQuoteError adverseCompleteS33Before [.query 1,.hydeRetriever 1] (.selection 3) 20 (by decide)
    · decide
    · decide
  unfold indexScore
  rw [hs,hp,hn,hz]
  simp only [BackupStat.mean]
  norm_num

theorem adverseCompleteS33D2I3 : indexScore (7/5) (controlPenalty savedCref uniformQuoteError unitRoleUnused .complete) adverseCompleteS33Before [.query 1,.hydeRetriever 1] (.selection 0) = treeIndex ((0/1)/1) (7/5) 0 8 1 := by
  have hs : replayBackup adverseCompleteS33Before emptyStatistics ([.query 1,.hydeRetriever 1]++[.selection 0]) = ⟨1,(0/1)⟩ := by
    rw [replayBackup_empty_closed_form]
    simp +decide [backedEvents,adverseCompleteS33Before,adverseCompleteProposal,adverseCompleteEvent1,adverseCompleteEvent2,adverseCompleteEvent3,adverseCompleteEvent4,adverseCompleteEvent5,adverseCompleteEvent6,adverseCompleteEvent7,adverseCompleteEvent8,adverseCompleteEvent9,adverseCompleteEvent10,adverseCompleteEvent11,adverseCompleteEvent12,adverseCompleteEvent13,adverseCompleteEvent14,adverseCompleteEvent15,adverseCompleteEvent16,adverseCompleteEvent17,adverseCompleteEvent18,adverseCompleteEvent19,adverseCompleteEvent20,adverseCompleteEvent21,adverseCompleteEvent22,adverseCompleteEvent23,adverseCompleteEvent24,adverseCompleteEvent25,adverseCompleteEvent26,adverseCompleteEvent27,adverseCompleteEvent28,adverseCompleteEvent29,adverseCompleteEvent30,adverseCompleteEvent31,adverseCompleteEvent32,taskReward]
    <;> norm_num
  have hp : rawVisits adverseCompleteS33Before [.query 1,.hydeRetriever 1] = 8 := by decide
  have hn : rawVisits adverseCompleteS33Before ([.query 1,.hydeRetriever 1]++[.selection 0]) = 1 := by decide
  have hz : (controlPenalty savedCref uniformQuoteError unitRoleUnused .complete) adverseCompleteS33Before [.query 1,.hydeRetriever 1] (.selection 0) = 0 := by
    apply control_penalty_empty_of_prior_terminal .complete savedCref uniformQuoteError adverseCompleteS33Before [.query 1,.hydeRetriever 1] (.selection 0) 8 (by decide)
    · decide
    · decide
  unfold indexScore
  rw [hs,hp,hn,hz]
  simp only [BackupStat.mean]
  norm_num

theorem adverseCompleteS33D2Cmp0 : indexScore (7/5) (controlPenalty savedCref uniformQuoteError unitRoleUnused .complete) adverseCompleteS33Before [.query 1,.hydeRetriever 1] (.selection 1) < indexScore (7/5) (controlPenalty savedCref uniformQuoteError unitRoleUnused .complete) adverseCompleteS33Before [.query 1,.hydeRetriever 1] (.selection 0) := by
  rw [adverseCompleteS33D2I0,adverseCompleteS33D2I3]
  have h := index_strict_order_from_intervals ((0/1)/1) ((0/1)/2) 0 0 (103761259/50000000) (1146411/781250)
    (treeBonus (7/5) 8 1) (treeBonus (7/5) 8 2)
    (trajectory_bonus_8_1).1 (trajectory_bonus_8_2).2 (by norm_num)
  simpa only [treeIndex,sub_zero] using h

theorem adverseCompleteS33D2Cmp1 : indexScore (7/5) (controlPenalty savedCref uniformQuoteError unitRoleUnused .complete) adverseCompleteS33Before [.query 1,.hydeRetriever 1] (.selection 2) < indexScore (7/5) (controlPenalty savedCref uniformQuoteError unitRoleUnused .complete) adverseCompleteS33Before [.query 1,.hydeRetriever 1] (.selection 0) := by
  rw [adverseCompleteS33D2I1,adverseCompleteS33D2I3]
  have h := index_strict_order_from_intervals ((0/1)/1) ((0/1)/2) 0 0 (103761259/50000000) (1146411/781250)
    (treeBonus (7/5) 8 1) (treeBonus (7/5) 8 2)
    (trajectory_bonus_8_1).1 (trajectory_bonus_8_2).2 (by norm_num)
  simpa only [treeIndex,sub_zero] using h

theorem adverseCompleteS33D2Cmp2 : indexScore (7/5) (controlPenalty savedCref uniformQuoteError unitRoleUnused .complete) adverseCompleteS33Before [.query 1,.hydeRetriever 1] (.selection 3) < indexScore (7/5) (controlPenalty savedCref uniformQuoteError unitRoleUnused .complete) adverseCompleteS33Before [.query 1,.hydeRetriever 1] (.selection 0) := by
  rw [adverseCompleteS33D2I2,adverseCompleteS33D2I3]
  have h := index_strict_order_from_intervals ((0/1)/1) ((0/1)/2) 0 0 (103761259/50000000) (1146411/781250)
    (treeBonus (7/5) 8 1) (treeBonus (7/5) 8 2)
    (trajectory_bonus_8_1).1 (trajectory_bonus_8_2).2 (by norm_num)
  simpa only [treeIndex,sub_zero] using h

theorem adverseCompleteS33Choice2 : nativeFirstChoice (indexScore (7/5) (controlPenalty savedCref uniformQuoteError unitRoleUnused .complete) adverseCompleteS33Before [.query 1,.hydeRetriever 1]) adverseCompleteS33Before [.query 1,.hydeRetriever 1] = .selection 0 := by
  apply visited_choice_from_ordered_certificate _ _ [.query 1,.hydeRetriever 1] [.selection 1,.selection 2,.selection 3] [] (.selection 0) (by decide)
  · intro a ha
    have ho : orderedLegalAvailable [.query 1,.hydeRetriever 1] = [.selection 1,.selection 2,.selection 3,.selection 0] := by decide
    rw [ho] at ha
    simp only [List.mem_cons,List.not_mem_nil,or_false] at ha
    rcases ha with rfl | rfl | rfl | rfl <;> decide
  · intro a ha
    simp only [List.mem_cons,List.not_mem_nil,or_false] at ha
    rcases ha with rfl | rfl | rfl
    · exact adverseCompleteS33D2Cmp0
    · exact adverseCompleteS33D2Cmp1
    · exact adverseCompleteS33D2Cmp2
  · simp

theorem adverseCompleteS33ActualEvent : nativeEvent budgetTape (7/5) (controlPenalty savedCref uniformQuoteError unitRoleUnused .complete)
    (taskReward true (2/5) (1/2)) adverseCompleteS33Before = adverseCompleteEvent33 := by
  have hs0 := native_select_existing_step budgetTape (7/5) (controlPenalty savedCref uniformQuoteError unitRoleUnused .complete) adverseCompleteS33Before 8 [] (.query 1)
    (by decide) (by decide) adverseCompleteS33Choice0
  have hs1 := native_select_existing_step budgetTape (7/5) (controlPenalty savedCref uniformQuoteError unitRoleUnused .complete) adverseCompleteS33Before 7 [.query 1] (.hydeRetriever 1)
    (by decide) (by decide) adverseCompleteS33Choice1
  have hs2 := native_select_existing_step budgetTape (7/5) (controlPenalty savedCref uniformQuoteError unitRoleUnused .complete) adverseCompleteS33Before 6 [.query 1,.hydeRetriever 1] (.selection 0)
    (by decide) (by decide) adverseCompleteS33Choice2
  have hnew := native_select_new_step budgetTape (7/5) (controlPenalty savedCref uniformQuoteError unitRoleUnused .complete) adverseCompleteS33Before 5 [.query 1,.hydeRetriever 1,.selection 0]
    [.width 3,.width 0,.width 1,.width 2] (.width 1) (by decide) (by decide) (by decide) (by decide)
  have hs : nativeSelect budgetTape (7/5) (controlPenalty savedCref uniformQuoteError unitRoleUnused .complete) adverseCompleteS33Before 9 [] = [.query 1,.hydeRetriever 1,.selection 0,.width 1] := by
    rw [hs0]
    change nativeSelect budgetTape (7/5) (controlPenalty savedCref uniformQuoteError unitRoleUnused .complete) adverseCompleteS33Before 8 [.query 1] = _
    rw [hs1]
    change nativeSelect budgetTape (7/5) (controlPenalty savedCref uniformQuoteError unitRoleUnused .complete) adverseCompleteS33Before 7 [.query 1,.hydeRetriever 1] = _
    rw [hs2]
    change nativeSelect budgetTape (7/5) (controlPenalty savedCref uniformQuoteError unitRoleUnused .complete) adverseCompleteS33Before 6 [.query 1,.hydeRetriever 1,.selection 0] = _
    rw [hnew] <;> rfl
  have hr : repairedRollout budgetTape adverseCompleteS33Before 9 [.query 1,.hydeRetriever 1,.selection 0,.width 1] = [.query 1,.hydeRetriever 1,.selection 0,.width 1,.stop,.reranker 0,.topm 0,.context 0,.answer 0] := by decide
  simp only [nativeEvent,hs,hr]
  rfl

def adverseCompleteS34Before := adverseCompleteProposal.take 33

theorem adverseCompleteS34Choice0 : nativeFirstChoice (indexScore (7/5) (controlPenalty savedCref uniformQuoteError unitRoleUnused .complete) adverseCompleteS34Before []) adverseCompleteS34Before [] = .query 1 := by
  apply complete_root_from_physical_gap adverseCompleteS34Before (adverseComplete_prefix_rewards 33) (by decide)
  · intro q; fin_cases q <;> decide
  · exact AgentUCTNextExact.adverse_complete_hyde_root_suffix_empty 33 (by omega)
  · intro q hq
    exact AgentUCTNextExact.adverse_complete_normal_root_physical_quote_exact 33 (by omega) q hq

theorem adverseCompleteS34D1I0 : indexScore (7/5) (controlPenalty savedCref uniformQuoteError unitRoleUnused .complete) adverseCompleteS34Before [.query 1] (.hydeRetriever 1) = treeIndex ((0/1)/9) (7/5) 0 26 9 := by
  have hs : replayBackup adverseCompleteS34Before emptyStatistics ([.query 1]++[.hydeRetriever 1]) = ⟨9,(0/1)⟩ := by
    rw [replayBackup_empty_closed_form]
    simp +decide [backedEvents,adverseCompleteS34Before,adverseCompleteProposal,adverseCompleteEvent1,adverseCompleteEvent2,adverseCompleteEvent3,adverseCompleteEvent4,adverseCompleteEvent5,adverseCompleteEvent6,adverseCompleteEvent7,adverseCompleteEvent8,adverseCompleteEvent9,adverseCompleteEvent10,adverseCompleteEvent11,adverseCompleteEvent12,adverseCompleteEvent13,adverseCompleteEvent14,adverseCompleteEvent15,adverseCompleteEvent16,adverseCompleteEvent17,adverseCompleteEvent18,adverseCompleteEvent19,adverseCompleteEvent20,adverseCompleteEvent21,adverseCompleteEvent22,adverseCompleteEvent23,adverseCompleteEvent24,adverseCompleteEvent25,adverseCompleteEvent26,adverseCompleteEvent27,adverseCompleteEvent28,adverseCompleteEvent29,adverseCompleteEvent30,adverseCompleteEvent31,adverseCompleteEvent32,adverseCompleteEvent33,taskReward]
    <;> norm_num
  have hp : rawVisits adverseCompleteS34Before [.query 1] = 26 := by decide
  have hn : rawVisits adverseCompleteS34Before ([.query 1]++[.hydeRetriever 1]) = 9 := by decide
  have hz : (controlPenalty savedCref uniformQuoteError unitRoleUnused .complete) adverseCompleteS34Before [.query 1] (.hydeRetriever 1) = 0 := by
    apply control_penalty_empty_of_prior_terminal .complete savedCref uniformQuoteError adverseCompleteS34Before [.query 1] (.hydeRetriever 1) 8 (by decide)
    · decide
    · decide
  unfold indexScore
  rw [hs,hp,hn,hz]
  simp only [BackupStat.mean]
  norm_num

theorem adverseCompleteS34D1I1 : indexScore (7/5) (controlPenalty savedCref uniformQuoteError unitRoleUnused .complete) adverseCompleteS34Before [.query 1] (.hydeRetriever 0) = treeIndex ((0/1)/8) (7/5) 0 26 8 := by
  have hs : replayBackup adverseCompleteS34Before emptyStatistics ([.query 1]++[.hydeRetriever 0]) = ⟨8,(0/1)⟩ := by
    rw [replayBackup_empty_closed_form]
    simp +decide [backedEvents,adverseCompleteS34Before,adverseCompleteProposal,adverseCompleteEvent1,adverseCompleteEvent2,adverseCompleteEvent3,adverseCompleteEvent4,adverseCompleteEvent5,adverseCompleteEvent6,adverseCompleteEvent7,adverseCompleteEvent8,adverseCompleteEvent9,adverseCompleteEvent10,adverseCompleteEvent11,adverseCompleteEvent12,adverseCompleteEvent13,adverseCompleteEvent14,adverseCompleteEvent15,adverseCompleteEvent16,adverseCompleteEvent17,adverseCompleteEvent18,adverseCompleteEvent19,adverseCompleteEvent20,adverseCompleteEvent21,adverseCompleteEvent22,adverseCompleteEvent23,adverseCompleteEvent24,adverseCompleteEvent25,adverseCompleteEvent26,adverseCompleteEvent27,adverseCompleteEvent28,adverseCompleteEvent29,adverseCompleteEvent30,adverseCompleteEvent31,adverseCompleteEvent32,adverseCompleteEvent33,taskReward]
    <;> norm_num
  have hp : rawVisits adverseCompleteS34Before [.query 1] = 26 := by decide
  have hn : rawVisits adverseCompleteS34Before ([.query 1]++[.hydeRetriever 0]) = 8 := by decide
  have hz : (controlPenalty savedCref uniformQuoteError unitRoleUnused .complete) adverseCompleteS34Before [.query 1] (.hydeRetriever 0) = 0 := by
    apply control_penalty_empty_of_prior_terminal .complete savedCref uniformQuoteError adverseCompleteS34Before [.query 1] (.hydeRetriever 0) 1 (by decide)
    · decide
    · decide
  unfold indexScore
  rw [hs,hp,hn,hz]
  simp only [BackupStat.mean]
  norm_num

theorem adverseCompleteS34D1I2 : indexScore (7/5) (controlPenalty savedCref uniformQuoteError unitRoleUnused .complete) adverseCompleteS34Before [.query 1] (.hydeRetriever 2) = treeIndex ((0/1)/8) (7/5) 0 26 8 := by
  have hs : replayBackup adverseCompleteS34Before emptyStatistics ([.query 1]++[.hydeRetriever 2]) = ⟨8,(0/1)⟩ := by
    rw [replayBackup_empty_closed_form]
    simp +decide [backedEvents,adverseCompleteS34Before,adverseCompleteProposal,adverseCompleteEvent1,adverseCompleteEvent2,adverseCompleteEvent3,adverseCompleteEvent4,adverseCompleteEvent5,adverseCompleteEvent6,adverseCompleteEvent7,adverseCompleteEvent8,adverseCompleteEvent9,adverseCompleteEvent10,adverseCompleteEvent11,adverseCompleteEvent12,adverseCompleteEvent13,adverseCompleteEvent14,adverseCompleteEvent15,adverseCompleteEvent16,adverseCompleteEvent17,adverseCompleteEvent18,adverseCompleteEvent19,adverseCompleteEvent20,adverseCompleteEvent21,adverseCompleteEvent22,adverseCompleteEvent23,adverseCompleteEvent24,adverseCompleteEvent25,adverseCompleteEvent26,adverseCompleteEvent27,adverseCompleteEvent28,adverseCompleteEvent29,adverseCompleteEvent30,adverseCompleteEvent31,adverseCompleteEvent32,adverseCompleteEvent33,taskReward]
    <;> norm_num
  have hp : rawVisits adverseCompleteS34Before [.query 1] = 26 := by decide
  have hn : rawVisits adverseCompleteS34Before ([.query 1]++[.hydeRetriever 2]) = 8 := by decide
  have hz : (controlPenalty savedCref uniformQuoteError unitRoleUnused .complete) adverseCompleteS34Before [.query 1] (.hydeRetriever 2) = 0 := by
    apply control_penalty_empty_of_prior_terminal .complete savedCref uniformQuoteError adverseCompleteS34Before [.query 1] (.hydeRetriever 2) 10 (by decide)
    · decide
    · decide
  unfold indexScore
  rw [hs,hp,hn,hz]
  simp only [BackupStat.mean]
  norm_num

theorem adverseCompleteS34D1Cmp0 : indexScore (7/5) (controlPenalty savedCref uniformQuoteError unitRoleUnused .complete) adverseCompleteS34Before [.query 1] (.hydeRetriever 1) < indexScore (7/5) (controlPenalty savedCref uniformQuoteError unitRoleUnused .complete) adverseCompleteS34Before [.query 1] (.hydeRetriever 0) := by
  rw [adverseCompleteS34D1I0,adverseCompleteS34D1I1]
  have h := index_strict_order_from_intervals ((0/1)/8) ((0/1)/9) 0 0 (44929941/50000000) (1059009/1250000)
    (treeBonus (7/5) 26 8) (treeBonus (7/5) 26 9)
    (trajectory_bonus_26_8).1 (trajectory_bonus_26_9).2 (by norm_num)
  simpa only [treeIndex,sub_zero] using h

theorem adverseCompleteS34D1Cmp2 : indexScore (7/5) (controlPenalty savedCref uniformQuoteError unitRoleUnused .complete) adverseCompleteS34Before [.query 1] (.hydeRetriever 2) ≤ indexScore (7/5) (controlPenalty savedCref uniformQuoteError unitRoleUnused .complete) adverseCompleteS34Before [.query 1] (.hydeRetriever 0) := by
  rw [adverseCompleteS34D1I2,adverseCompleteS34D1I1]

theorem adverseCompleteS34Choice1 : nativeFirstChoice (indexScore (7/5) (controlPenalty savedCref uniformQuoteError unitRoleUnused .complete) adverseCompleteS34Before [.query 1]) adverseCompleteS34Before [.query 1] = .hydeRetriever 0 := by
  apply visited_choice_from_ordered_certificate _ _ [.query 1] [.hydeRetriever 1] [.hydeRetriever 2] (.hydeRetriever 0) (by decide)
  · intro a ha
    have ho : orderedLegalAvailable [.query 1] = [.hydeRetriever 1,.hydeRetriever 0,.hydeRetriever 2] := by decide
    rw [ho] at ha
    simp only [List.mem_cons,List.not_mem_nil,or_false] at ha
    rcases ha with rfl | rfl | rfl <;> decide
  · intro a ha
    simp only [List.mem_cons,List.not_mem_nil,or_false] at ha
    rcases ha with rfl
    · exact adverseCompleteS34D1Cmp0
  · intro a ha
    simp only [List.mem_cons,List.not_mem_nil,or_false] at ha
    rcases ha with rfl
    · exact adverseCompleteS34D1Cmp2

theorem adverseCompleteS34D2I0 : indexScore (7/5) (controlPenalty savedCref uniformQuoteError unitRoleUnused .complete) adverseCompleteS34Before [.query 1,.hydeRetriever 0] (.selection 1) = treeIndex ((0/1)/2) (7/5) 0 8 2 := by
  have hs : replayBackup adverseCompleteS34Before emptyStatistics ([.query 1,.hydeRetriever 0]++[.selection 1]) = ⟨2,(0/1)⟩ := by
    rw [replayBackup_empty_closed_form]
    simp +decide [backedEvents,adverseCompleteS34Before,adverseCompleteProposal,adverseCompleteEvent1,adverseCompleteEvent2,adverseCompleteEvent3,adverseCompleteEvent4,adverseCompleteEvent5,adverseCompleteEvent6,adverseCompleteEvent7,adverseCompleteEvent8,adverseCompleteEvent9,adverseCompleteEvent10,adverseCompleteEvent11,adverseCompleteEvent12,adverseCompleteEvent13,adverseCompleteEvent14,adverseCompleteEvent15,adverseCompleteEvent16,adverseCompleteEvent17,adverseCompleteEvent18,adverseCompleteEvent19,adverseCompleteEvent20,adverseCompleteEvent21,adverseCompleteEvent22,adverseCompleteEvent23,adverseCompleteEvent24,adverseCompleteEvent25,adverseCompleteEvent26,adverseCompleteEvent27,adverseCompleteEvent28,adverseCompleteEvent29,adverseCompleteEvent30,adverseCompleteEvent31,adverseCompleteEvent32,adverseCompleteEvent33,taskReward]
    <;> norm_num
  have hp : rawVisits adverseCompleteS34Before [.query 1,.hydeRetriever 0] = 8 := by decide
  have hn : rawVisits adverseCompleteS34Before ([.query 1,.hydeRetriever 0]++[.selection 1]) = 2 := by decide
  have hz : (controlPenalty savedCref uniformQuoteError unitRoleUnused .complete) adverseCompleteS34Before [.query 1,.hydeRetriever 0] (.selection 1) = 0 := by
    apply control_penalty_empty_of_prior_terminal .complete savedCref uniformQuoteError adverseCompleteS34Before [.query 1,.hydeRetriever 0] (.selection 1) 15 (by decide)
    · decide
    · decide
  unfold indexScore
  rw [hs,hp,hn,hz]
  simp only [BackupStat.mean]
  norm_num

theorem adverseCompleteS34D2I1 : indexScore (7/5) (controlPenalty savedCref uniformQuoteError unitRoleUnused .complete) adverseCompleteS34Before [.query 1,.hydeRetriever 0] (.selection 2) = treeIndex ((0/1)/2) (7/5) 0 8 2 := by
  have hs : replayBackup adverseCompleteS34Before emptyStatistics ([.query 1,.hydeRetriever 0]++[.selection 2]) = ⟨2,(0/1)⟩ := by
    rw [replayBackup_empty_closed_form]
    simp +decide [backedEvents,adverseCompleteS34Before,adverseCompleteProposal,adverseCompleteEvent1,adverseCompleteEvent2,adverseCompleteEvent3,adverseCompleteEvent4,adverseCompleteEvent5,adverseCompleteEvent6,adverseCompleteEvent7,adverseCompleteEvent8,adverseCompleteEvent9,adverseCompleteEvent10,adverseCompleteEvent11,adverseCompleteEvent12,adverseCompleteEvent13,adverseCompleteEvent14,adverseCompleteEvent15,adverseCompleteEvent16,adverseCompleteEvent17,adverseCompleteEvent18,adverseCompleteEvent19,adverseCompleteEvent20,adverseCompleteEvent21,adverseCompleteEvent22,adverseCompleteEvent23,adverseCompleteEvent24,adverseCompleteEvent25,adverseCompleteEvent26,adverseCompleteEvent27,adverseCompleteEvent28,adverseCompleteEvent29,adverseCompleteEvent30,adverseCompleteEvent31,adverseCompleteEvent32,adverseCompleteEvent33,taskReward]
    <;> norm_num
  have hp : rawVisits adverseCompleteS34Before [.query 1,.hydeRetriever 0] = 8 := by decide
  have hn : rawVisits adverseCompleteS34Before ([.query 1,.hydeRetriever 0]++[.selection 2]) = 2 := by decide
  have hz : (controlPenalty savedCref uniformQuoteError unitRoleUnused .complete) adverseCompleteS34Before [.query 1,.hydeRetriever 0] (.selection 2) = 0 := by
    apply control_penalty_empty_of_prior_terminal .complete savedCref uniformQuoteError adverseCompleteS34Before [.query 1,.hydeRetriever 0] (.selection 2) 18 (by decide)
    · decide
    · decide
  unfold indexScore
  rw [hs,hp,hn,hz]
  simp only [BackupStat.mean]
  norm_num

theorem adverseCompleteS34D2I2 : indexScore (7/5) (controlPenalty savedCref uniformQuoteError unitRoleUnused .complete) adverseCompleteS34Before [.query 1,.hydeRetriever 0] (.selection 3) = treeIndex ((0/1)/2) (7/5) 0 8 2 := by
  have hs : replayBackup adverseCompleteS34Before emptyStatistics ([.query 1,.hydeRetriever 0]++[.selection 3]) = ⟨2,(0/1)⟩ := by
    rw [replayBackup_empty_closed_form]
    simp +decide [backedEvents,adverseCompleteS34Before,adverseCompleteProposal,adverseCompleteEvent1,adverseCompleteEvent2,adverseCompleteEvent3,adverseCompleteEvent4,adverseCompleteEvent5,adverseCompleteEvent6,adverseCompleteEvent7,adverseCompleteEvent8,adverseCompleteEvent9,adverseCompleteEvent10,adverseCompleteEvent11,adverseCompleteEvent12,adverseCompleteEvent13,adverseCompleteEvent14,adverseCompleteEvent15,adverseCompleteEvent16,adverseCompleteEvent17,adverseCompleteEvent18,adverseCompleteEvent19,adverseCompleteEvent20,adverseCompleteEvent21,adverseCompleteEvent22,adverseCompleteEvent23,adverseCompleteEvent24,adverseCompleteEvent25,adverseCompleteEvent26,adverseCompleteEvent27,adverseCompleteEvent28,adverseCompleteEvent29,adverseCompleteEvent30,adverseCompleteEvent31,adverseCompleteEvent32,adverseCompleteEvent33,taskReward]
    <;> norm_num
  have hp : rawVisits adverseCompleteS34Before [.query 1,.hydeRetriever 0] = 8 := by decide
  have hn : rawVisits adverseCompleteS34Before ([.query 1,.hydeRetriever 0]++[.selection 3]) = 2 := by decide
  have hz : (controlPenalty savedCref uniformQuoteError unitRoleUnused .complete) adverseCompleteS34Before [.query 1,.hydeRetriever 0] (.selection 3) = 0 := by
    apply control_penalty_empty_of_prior_terminal .complete savedCref uniformQuoteError adverseCompleteS34Before [.query 1,.hydeRetriever 0] (.selection 3) 21 (by decide)
    · decide
    · decide
  unfold indexScore
  rw [hs,hp,hn,hz]
  simp only [BackupStat.mean]
  norm_num

theorem adverseCompleteS34D2I3 : indexScore (7/5) (controlPenalty savedCref uniformQuoteError unitRoleUnused .complete) adverseCompleteS34Before [.query 1,.hydeRetriever 0] (.selection 0) = treeIndex ((0/1)/1) (7/5) 0 8 1 := by
  have hs : replayBackup adverseCompleteS34Before emptyStatistics ([.query 1,.hydeRetriever 0]++[.selection 0]) = ⟨1,(0/1)⟩ := by
    rw [replayBackup_empty_closed_form]
    simp +decide [backedEvents,adverseCompleteS34Before,adverseCompleteProposal,adverseCompleteEvent1,adverseCompleteEvent2,adverseCompleteEvent3,adverseCompleteEvent4,adverseCompleteEvent5,adverseCompleteEvent6,adverseCompleteEvent7,adverseCompleteEvent8,adverseCompleteEvent9,adverseCompleteEvent10,adverseCompleteEvent11,adverseCompleteEvent12,adverseCompleteEvent13,adverseCompleteEvent14,adverseCompleteEvent15,adverseCompleteEvent16,adverseCompleteEvent17,adverseCompleteEvent18,adverseCompleteEvent19,adverseCompleteEvent20,adverseCompleteEvent21,adverseCompleteEvent22,adverseCompleteEvent23,adverseCompleteEvent24,adverseCompleteEvent25,adverseCompleteEvent26,adverseCompleteEvent27,adverseCompleteEvent28,adverseCompleteEvent29,adverseCompleteEvent30,adverseCompleteEvent31,adverseCompleteEvent32,adverseCompleteEvent33,taskReward]
    <;> norm_num
  have hp : rawVisits adverseCompleteS34Before [.query 1,.hydeRetriever 0] = 8 := by decide
  have hn : rawVisits adverseCompleteS34Before ([.query 1,.hydeRetriever 0]++[.selection 0]) = 1 := by decide
  have hz : (controlPenalty savedCref uniformQuoteError unitRoleUnused .complete) adverseCompleteS34Before [.query 1,.hydeRetriever 0] (.selection 0) = 0 := by
    apply control_penalty_empty_of_prior_terminal .complete savedCref uniformQuoteError adverseCompleteS34Before [.query 1,.hydeRetriever 0] (.selection 0) 1 (by decide)
    · decide
    · decide
  unfold indexScore
  rw [hs,hp,hn,hz]
  simp only [BackupStat.mean]
  norm_num

theorem adverseCompleteS34D2Cmp0 : indexScore (7/5) (controlPenalty savedCref uniformQuoteError unitRoleUnused .complete) adverseCompleteS34Before [.query 1,.hydeRetriever 0] (.selection 1) < indexScore (7/5) (controlPenalty savedCref uniformQuoteError unitRoleUnused .complete) adverseCompleteS34Before [.query 1,.hydeRetriever 0] (.selection 0) := by
  rw [adverseCompleteS34D2I0,adverseCompleteS34D2I3]
  have h := index_strict_order_from_intervals ((0/1)/1) ((0/1)/2) 0 0 (103761259/50000000) (1146411/781250)
    (treeBonus (7/5) 8 1) (treeBonus (7/5) 8 2)
    (trajectory_bonus_8_1).1 (trajectory_bonus_8_2).2 (by norm_num)
  simpa only [treeIndex,sub_zero] using h

theorem adverseCompleteS34D2Cmp1 : indexScore (7/5) (controlPenalty savedCref uniformQuoteError unitRoleUnused .complete) adverseCompleteS34Before [.query 1,.hydeRetriever 0] (.selection 2) < indexScore (7/5) (controlPenalty savedCref uniformQuoteError unitRoleUnused .complete) adverseCompleteS34Before [.query 1,.hydeRetriever 0] (.selection 0) := by
  rw [adverseCompleteS34D2I1,adverseCompleteS34D2I3]
  have h := index_strict_order_from_intervals ((0/1)/1) ((0/1)/2) 0 0 (103761259/50000000) (1146411/781250)
    (treeBonus (7/5) 8 1) (treeBonus (7/5) 8 2)
    (trajectory_bonus_8_1).1 (trajectory_bonus_8_2).2 (by norm_num)
  simpa only [treeIndex,sub_zero] using h

theorem adverseCompleteS34D2Cmp2 : indexScore (7/5) (controlPenalty savedCref uniformQuoteError unitRoleUnused .complete) adverseCompleteS34Before [.query 1,.hydeRetriever 0] (.selection 3) < indexScore (7/5) (controlPenalty savedCref uniformQuoteError unitRoleUnused .complete) adverseCompleteS34Before [.query 1,.hydeRetriever 0] (.selection 0) := by
  rw [adverseCompleteS34D2I2,adverseCompleteS34D2I3]
  have h := index_strict_order_from_intervals ((0/1)/1) ((0/1)/2) 0 0 (103761259/50000000) (1146411/781250)
    (treeBonus (7/5) 8 1) (treeBonus (7/5) 8 2)
    (trajectory_bonus_8_1).1 (trajectory_bonus_8_2).2 (by norm_num)
  simpa only [treeIndex,sub_zero] using h

theorem adverseCompleteS34Choice2 : nativeFirstChoice (indexScore (7/5) (controlPenalty savedCref uniformQuoteError unitRoleUnused .complete) adverseCompleteS34Before [.query 1,.hydeRetriever 0]) adverseCompleteS34Before [.query 1,.hydeRetriever 0] = .selection 0 := by
  apply visited_choice_from_ordered_certificate _ _ [.query 1,.hydeRetriever 0] [.selection 1,.selection 2,.selection 3] [] (.selection 0) (by decide)
  · intro a ha
    have ho : orderedLegalAvailable [.query 1,.hydeRetriever 0] = [.selection 1,.selection 2,.selection 3,.selection 0] := by decide
    rw [ho] at ha
    simp only [List.mem_cons,List.not_mem_nil,or_false] at ha
    rcases ha with rfl | rfl | rfl | rfl <;> decide
  · intro a ha
    simp only [List.mem_cons,List.not_mem_nil,or_false] at ha
    rcases ha with rfl | rfl | rfl
    · exact adverseCompleteS34D2Cmp0
    · exact adverseCompleteS34D2Cmp1
    · exact adverseCompleteS34D2Cmp2
  · simp

theorem adverseCompleteS34ActualEvent : nativeEvent budgetTape (7/5) (controlPenalty savedCref uniformQuoteError unitRoleUnused .complete)
    (taskReward true (2/5) (1/2)) adverseCompleteS34Before = adverseCompleteEvent34 := by
  have hs0 := native_select_existing_step budgetTape (7/5) (controlPenalty savedCref uniformQuoteError unitRoleUnused .complete) adverseCompleteS34Before 8 [] (.query 1)
    (by decide) (by decide) adverseCompleteS34Choice0
  have hs1 := native_select_existing_step budgetTape (7/5) (controlPenalty savedCref uniformQuoteError unitRoleUnused .complete) adverseCompleteS34Before 7 [.query 1] (.hydeRetriever 0)
    (by decide) (by decide) adverseCompleteS34Choice1
  have hs2 := native_select_existing_step budgetTape (7/5) (controlPenalty savedCref uniformQuoteError unitRoleUnused .complete) adverseCompleteS34Before 6 [.query 1,.hydeRetriever 0] (.selection 0)
    (by decide) (by decide) adverseCompleteS34Choice2
  have hnew := native_select_new_step budgetTape (7/5) (controlPenalty savedCref uniformQuoteError unitRoleUnused .complete) adverseCompleteS34Before 5 [.query 1,.hydeRetriever 0,.selection 0]
    [.width 3,.width 0,.width 1,.width 2] (.width 0) (by decide) (by decide) (by decide) (by decide)
  have hs : nativeSelect budgetTape (7/5) (controlPenalty savedCref uniformQuoteError unitRoleUnused .complete) adverseCompleteS34Before 9 [] = [.query 1,.hydeRetriever 0,.selection 0,.width 0] := by
    rw [hs0]
    change nativeSelect budgetTape (7/5) (controlPenalty savedCref uniformQuoteError unitRoleUnused .complete) adverseCompleteS34Before 8 [.query 1] = _
    rw [hs1]
    change nativeSelect budgetTape (7/5) (controlPenalty savedCref uniformQuoteError unitRoleUnused .complete) adverseCompleteS34Before 7 [.query 1,.hydeRetriever 0] = _
    rw [hs2]
    change nativeSelect budgetTape (7/5) (controlPenalty savedCref uniformQuoteError unitRoleUnused .complete) adverseCompleteS34Before 6 [.query 1,.hydeRetriever 0,.selection 0] = _
    rw [hnew] <;> rfl
  have hr : repairedRollout budgetTape adverseCompleteS34Before 9 [.query 1,.hydeRetriever 0,.selection 0,.width 0] = [.query 1,.hydeRetriever 0,.selection 0,.width 0,.stop,.reranker 0,.topm 0,.context 0,.answer 0] := by decide
  simp only [nativeEvent,hs,hr]
  rfl

def adverseCompleteS35Before := adverseCompleteProposal.take 34

theorem adverseCompleteS35Choice0 : nativeFirstChoice (indexScore (7/5) (controlPenalty savedCref uniformQuoteError unitRoleUnused .complete) adverseCompleteS35Before []) adverseCompleteS35Before [] = .query 1 := by
  apply complete_root_from_physical_gap adverseCompleteS35Before (adverseComplete_prefix_rewards 34) (by decide)
  · intro q; fin_cases q <;> decide
  · exact AgentUCTNextExact.adverse_complete_hyde_root_suffix_empty 34 (by omega)
  · intro q hq
    exact AgentUCTNextExact.adverse_complete_normal_root_physical_quote_exact 34 (by omega) q hq

theorem adverseCompleteS35D1I0 : indexScore (7/5) (controlPenalty savedCref uniformQuoteError unitRoleUnused .complete) adverseCompleteS35Before [.query 1] (.hydeRetriever 1) = treeIndex ((0/1)/9) (7/5) 0 27 9 := by
  have hs : replayBackup adverseCompleteS35Before emptyStatistics ([.query 1]++[.hydeRetriever 1]) = ⟨9,(0/1)⟩ := by
    rw [replayBackup_empty_closed_form]
    simp +decide [backedEvents,adverseCompleteS35Before,adverseCompleteProposal,adverseCompleteEvent1,adverseCompleteEvent2,adverseCompleteEvent3,adverseCompleteEvent4,adverseCompleteEvent5,adverseCompleteEvent6,adverseCompleteEvent7,adverseCompleteEvent8,adverseCompleteEvent9,adverseCompleteEvent10,adverseCompleteEvent11,adverseCompleteEvent12,adverseCompleteEvent13,adverseCompleteEvent14,adverseCompleteEvent15,adverseCompleteEvent16,adverseCompleteEvent17,adverseCompleteEvent18,adverseCompleteEvent19,adverseCompleteEvent20,adverseCompleteEvent21,adverseCompleteEvent22,adverseCompleteEvent23,adverseCompleteEvent24,adverseCompleteEvent25,adverseCompleteEvent26,adverseCompleteEvent27,adverseCompleteEvent28,adverseCompleteEvent29,adverseCompleteEvent30,adverseCompleteEvent31,adverseCompleteEvent32,adverseCompleteEvent33,adverseCompleteEvent34,taskReward]
    <;> norm_num
  have hp : rawVisits adverseCompleteS35Before [.query 1] = 27 := by decide
  have hn : rawVisits adverseCompleteS35Before ([.query 1]++[.hydeRetriever 1]) = 9 := by decide
  have hz : (controlPenalty savedCref uniformQuoteError unitRoleUnused .complete) adverseCompleteS35Before [.query 1] (.hydeRetriever 1) = 0 := by
    apply control_penalty_empty_of_prior_terminal .complete savedCref uniformQuoteError adverseCompleteS35Before [.query 1] (.hydeRetriever 1) 8 (by decide)
    · decide
    · decide
  unfold indexScore
  rw [hs,hp,hn,hz]
  simp only [BackupStat.mean]
  norm_num

theorem adverseCompleteS35D1I1 : indexScore (7/5) (controlPenalty savedCref uniformQuoteError unitRoleUnused .complete) adverseCompleteS35Before [.query 1] (.hydeRetriever 0) = treeIndex ((0/1)/9) (7/5) 0 27 9 := by
  have hs : replayBackup adverseCompleteS35Before emptyStatistics ([.query 1]++[.hydeRetriever 0]) = ⟨9,(0/1)⟩ := by
    rw [replayBackup_empty_closed_form]
    simp +decide [backedEvents,adverseCompleteS35Before,adverseCompleteProposal,adverseCompleteEvent1,adverseCompleteEvent2,adverseCompleteEvent3,adverseCompleteEvent4,adverseCompleteEvent5,adverseCompleteEvent6,adverseCompleteEvent7,adverseCompleteEvent8,adverseCompleteEvent9,adverseCompleteEvent10,adverseCompleteEvent11,adverseCompleteEvent12,adverseCompleteEvent13,adverseCompleteEvent14,adverseCompleteEvent15,adverseCompleteEvent16,adverseCompleteEvent17,adverseCompleteEvent18,adverseCompleteEvent19,adverseCompleteEvent20,adverseCompleteEvent21,adverseCompleteEvent22,adverseCompleteEvent23,adverseCompleteEvent24,adverseCompleteEvent25,adverseCompleteEvent26,adverseCompleteEvent27,adverseCompleteEvent28,adverseCompleteEvent29,adverseCompleteEvent30,adverseCompleteEvent31,adverseCompleteEvent32,adverseCompleteEvent33,adverseCompleteEvent34,taskReward]
    <;> norm_num
  have hp : rawVisits adverseCompleteS35Before [.query 1] = 27 := by decide
  have hn : rawVisits adverseCompleteS35Before ([.query 1]++[.hydeRetriever 0]) = 9 := by decide
  have hz : (controlPenalty savedCref uniformQuoteError unitRoleUnused .complete) adverseCompleteS35Before [.query 1] (.hydeRetriever 0) = 0 := by
    apply control_penalty_empty_of_prior_terminal .complete savedCref uniformQuoteError adverseCompleteS35Before [.query 1] (.hydeRetriever 0) 1 (by decide)
    · decide
    · decide
  unfold indexScore
  rw [hs,hp,hn,hz]
  simp only [BackupStat.mean]
  norm_num

theorem adverseCompleteS35D1I2 : indexScore (7/5) (controlPenalty savedCref uniformQuoteError unitRoleUnused .complete) adverseCompleteS35Before [.query 1] (.hydeRetriever 2) = treeIndex ((0/1)/8) (7/5) 0 27 8 := by
  have hs : replayBackup adverseCompleteS35Before emptyStatistics ([.query 1]++[.hydeRetriever 2]) = ⟨8,(0/1)⟩ := by
    rw [replayBackup_empty_closed_form]
    simp +decide [backedEvents,adverseCompleteS35Before,adverseCompleteProposal,adverseCompleteEvent1,adverseCompleteEvent2,adverseCompleteEvent3,adverseCompleteEvent4,adverseCompleteEvent5,adverseCompleteEvent6,adverseCompleteEvent7,adverseCompleteEvent8,adverseCompleteEvent9,adverseCompleteEvent10,adverseCompleteEvent11,adverseCompleteEvent12,adverseCompleteEvent13,adverseCompleteEvent14,adverseCompleteEvent15,adverseCompleteEvent16,adverseCompleteEvent17,adverseCompleteEvent18,adverseCompleteEvent19,adverseCompleteEvent20,adverseCompleteEvent21,adverseCompleteEvent22,adverseCompleteEvent23,adverseCompleteEvent24,adverseCompleteEvent25,adverseCompleteEvent26,adverseCompleteEvent27,adverseCompleteEvent28,adverseCompleteEvent29,adverseCompleteEvent30,adverseCompleteEvent31,adverseCompleteEvent32,adverseCompleteEvent33,adverseCompleteEvent34,taskReward]
    <;> norm_num
  have hp : rawVisits adverseCompleteS35Before [.query 1] = 27 := by decide
  have hn : rawVisits adverseCompleteS35Before ([.query 1]++[.hydeRetriever 2]) = 8 := by decide
  have hz : (controlPenalty savedCref uniformQuoteError unitRoleUnused .complete) adverseCompleteS35Before [.query 1] (.hydeRetriever 2) = 0 := by
    apply control_penalty_empty_of_prior_terminal .complete savedCref uniformQuoteError adverseCompleteS35Before [.query 1] (.hydeRetriever 2) 10 (by decide)
    · decide
    · decide
  unfold indexScore
  rw [hs,hp,hn,hz]
  simp only [BackupStat.mean]
  norm_num

theorem adverseCompleteS35D1Cmp0 : indexScore (7/5) (controlPenalty savedCref uniformQuoteError unitRoleUnused .complete) adverseCompleteS35Before [.query 1] (.hydeRetriever 1) < indexScore (7/5) (controlPenalty savedCref uniformQuoteError unitRoleUnused .complete) adverseCompleteS35Before [.query 1] (.hydeRetriever 2) := by
  rw [adverseCompleteS35D1I0,adverseCompleteS35D1I2]
  have h := index_strict_order_from_intervals ((0/1)/8) ((0/1)/9) 0 0 (45177153/50000000) (5324179/6250000)
    (treeBonus (7/5) 27 8) (treeBonus (7/5) 27 9)
    (trajectory_bonus_27_8).1 (trajectory_bonus_27_9).2 (by norm_num)
  simpa only [treeIndex,sub_zero] using h

theorem adverseCompleteS35D1Cmp1 : indexScore (7/5) (controlPenalty savedCref uniformQuoteError unitRoleUnused .complete) adverseCompleteS35Before [.query 1] (.hydeRetriever 0) < indexScore (7/5) (controlPenalty savedCref uniformQuoteError unitRoleUnused .complete) adverseCompleteS35Before [.query 1] (.hydeRetriever 2) := by
  rw [adverseCompleteS35D1I1,adverseCompleteS35D1I2]
  have h := index_strict_order_from_intervals ((0/1)/8) ((0/1)/9) 0 0 (45177153/50000000) (5324179/6250000)
    (treeBonus (7/5) 27 8) (treeBonus (7/5) 27 9)
    (trajectory_bonus_27_8).1 (trajectory_bonus_27_9).2 (by norm_num)
  simpa only [treeIndex,sub_zero] using h

theorem adverseCompleteS35Choice1 : nativeFirstChoice (indexScore (7/5) (controlPenalty savedCref uniformQuoteError unitRoleUnused .complete) adverseCompleteS35Before [.query 1]) adverseCompleteS35Before [.query 1] = .hydeRetriever 2 := by
  apply visited_choice_from_ordered_certificate _ _ [.query 1] [.hydeRetriever 1,.hydeRetriever 0] [] (.hydeRetriever 2) (by decide)
  · intro a ha
    have ho : orderedLegalAvailable [.query 1] = [.hydeRetriever 1,.hydeRetriever 0,.hydeRetriever 2] := by decide
    rw [ho] at ha
    simp only [List.mem_cons,List.not_mem_nil,or_false] at ha
    rcases ha with rfl | rfl | rfl <;> decide
  · intro a ha
    simp only [List.mem_cons,List.not_mem_nil,or_false] at ha
    rcases ha with rfl | rfl
    · exact adverseCompleteS35D1Cmp0
    · exact adverseCompleteS35D1Cmp1
  · simp

theorem adverseCompleteS35D2I0 : indexScore (7/5) (controlPenalty savedCref uniformQuoteError unitRoleUnused .complete) adverseCompleteS35Before [.query 1,.hydeRetriever 2] (.selection 1) = treeIndex ((0/1)/2) (7/5) 0 8 2 := by
  have hs : replayBackup adverseCompleteS35Before emptyStatistics ([.query 1,.hydeRetriever 2]++[.selection 1]) = ⟨2,(0/1)⟩ := by
    rw [replayBackup_empty_closed_form]
    simp +decide [backedEvents,adverseCompleteS35Before,adverseCompleteProposal,adverseCompleteEvent1,adverseCompleteEvent2,adverseCompleteEvent3,adverseCompleteEvent4,adverseCompleteEvent5,adverseCompleteEvent6,adverseCompleteEvent7,adverseCompleteEvent8,adverseCompleteEvent9,adverseCompleteEvent10,adverseCompleteEvent11,adverseCompleteEvent12,adverseCompleteEvent13,adverseCompleteEvent14,adverseCompleteEvent15,adverseCompleteEvent16,adverseCompleteEvent17,adverseCompleteEvent18,adverseCompleteEvent19,adverseCompleteEvent20,adverseCompleteEvent21,adverseCompleteEvent22,adverseCompleteEvent23,adverseCompleteEvent24,adverseCompleteEvent25,adverseCompleteEvent26,adverseCompleteEvent27,adverseCompleteEvent28,adverseCompleteEvent29,adverseCompleteEvent30,adverseCompleteEvent31,adverseCompleteEvent32,adverseCompleteEvent33,adverseCompleteEvent34,taskReward]
    <;> norm_num
  have hp : rawVisits adverseCompleteS35Before [.query 1,.hydeRetriever 2] = 8 := by decide
  have hn : rawVisits adverseCompleteS35Before ([.query 1,.hydeRetriever 2]++[.selection 1]) = 2 := by decide
  have hz : (controlPenalty savedCref uniformQuoteError unitRoleUnused .complete) adverseCompleteS35Before [.query 1,.hydeRetriever 2] (.selection 1) = 0 := by
    apply control_penalty_empty_of_prior_terminal .complete savedCref uniformQuoteError adverseCompleteS35Before [.query 1,.hydeRetriever 2] (.selection 1) 16 (by decide)
    · decide
    · decide
  unfold indexScore
  rw [hs,hp,hn,hz]
  simp only [BackupStat.mean]
  norm_num

theorem adverseCompleteS35D2I1 : indexScore (7/5) (controlPenalty savedCref uniformQuoteError unitRoleUnused .complete) adverseCompleteS35Before [.query 1,.hydeRetriever 2] (.selection 2) = treeIndex ((0/1)/2) (7/5) 0 8 2 := by
  have hs : replayBackup adverseCompleteS35Before emptyStatistics ([.query 1,.hydeRetriever 2]++[.selection 2]) = ⟨2,(0/1)⟩ := by
    rw [replayBackup_empty_closed_form]
    simp +decide [backedEvents,adverseCompleteS35Before,adverseCompleteProposal,adverseCompleteEvent1,adverseCompleteEvent2,adverseCompleteEvent3,adverseCompleteEvent4,adverseCompleteEvent5,adverseCompleteEvent6,adverseCompleteEvent7,adverseCompleteEvent8,adverseCompleteEvent9,adverseCompleteEvent10,adverseCompleteEvent11,adverseCompleteEvent12,adverseCompleteEvent13,adverseCompleteEvent14,adverseCompleteEvent15,adverseCompleteEvent16,adverseCompleteEvent17,adverseCompleteEvent18,adverseCompleteEvent19,adverseCompleteEvent20,adverseCompleteEvent21,adverseCompleteEvent22,adverseCompleteEvent23,adverseCompleteEvent24,adverseCompleteEvent25,adverseCompleteEvent26,adverseCompleteEvent27,adverseCompleteEvent28,adverseCompleteEvent29,adverseCompleteEvent30,adverseCompleteEvent31,adverseCompleteEvent32,adverseCompleteEvent33,adverseCompleteEvent34,taskReward]
    <;> norm_num
  have hp : rawVisits adverseCompleteS35Before [.query 1,.hydeRetriever 2] = 8 := by decide
  have hn : rawVisits adverseCompleteS35Before ([.query 1,.hydeRetriever 2]++[.selection 2]) = 2 := by decide
  have hz : (controlPenalty savedCref uniformQuoteError unitRoleUnused .complete) adverseCompleteS35Before [.query 1,.hydeRetriever 2] (.selection 2) = 0 := by
    apply control_penalty_empty_of_prior_terminal .complete savedCref uniformQuoteError adverseCompleteS35Before [.query 1,.hydeRetriever 2] (.selection 2) 19 (by decide)
    · decide
    · decide
  unfold indexScore
  rw [hs,hp,hn,hz]
  simp only [BackupStat.mean]
  norm_num

theorem adverseCompleteS35D2I2 : indexScore (7/5) (controlPenalty savedCref uniformQuoteError unitRoleUnused .complete) adverseCompleteS35Before [.query 1,.hydeRetriever 2] (.selection 3) = treeIndex ((0/1)/2) (7/5) 0 8 2 := by
  have hs : replayBackup adverseCompleteS35Before emptyStatistics ([.query 1,.hydeRetriever 2]++[.selection 3]) = ⟨2,(0/1)⟩ := by
    rw [replayBackup_empty_closed_form]
    simp +decide [backedEvents,adverseCompleteS35Before,adverseCompleteProposal,adverseCompleteEvent1,adverseCompleteEvent2,adverseCompleteEvent3,adverseCompleteEvent4,adverseCompleteEvent5,adverseCompleteEvent6,adverseCompleteEvent7,adverseCompleteEvent8,adverseCompleteEvent9,adverseCompleteEvent10,adverseCompleteEvent11,adverseCompleteEvent12,adverseCompleteEvent13,adverseCompleteEvent14,adverseCompleteEvent15,adverseCompleteEvent16,adverseCompleteEvent17,adverseCompleteEvent18,adverseCompleteEvent19,adverseCompleteEvent20,adverseCompleteEvent21,adverseCompleteEvent22,adverseCompleteEvent23,adverseCompleteEvent24,adverseCompleteEvent25,adverseCompleteEvent26,adverseCompleteEvent27,adverseCompleteEvent28,adverseCompleteEvent29,adverseCompleteEvent30,adverseCompleteEvent31,adverseCompleteEvent32,adverseCompleteEvent33,adverseCompleteEvent34,taskReward]
    <;> norm_num
  have hp : rawVisits adverseCompleteS35Before [.query 1,.hydeRetriever 2] = 8 := by decide
  have hn : rawVisits adverseCompleteS35Before ([.query 1,.hydeRetriever 2]++[.selection 3]) = 2 := by decide
  have hz : (controlPenalty savedCref uniformQuoteError unitRoleUnused .complete) adverseCompleteS35Before [.query 1,.hydeRetriever 2] (.selection 3) = 0 := by
    apply control_penalty_empty_of_prior_terminal .complete savedCref uniformQuoteError adverseCompleteS35Before [.query 1,.hydeRetriever 2] (.selection 3) 22 (by decide)
    · decide
    · decide
  unfold indexScore
  rw [hs,hp,hn,hz]
  simp only [BackupStat.mean]
  norm_num

theorem adverseCompleteS35D2I3 : indexScore (7/5) (controlPenalty savedCref uniformQuoteError unitRoleUnused .complete) adverseCompleteS35Before [.query 1,.hydeRetriever 2] (.selection 0) = treeIndex ((0/1)/1) (7/5) 0 8 1 := by
  have hs : replayBackup adverseCompleteS35Before emptyStatistics ([.query 1,.hydeRetriever 2]++[.selection 0]) = ⟨1,(0/1)⟩ := by
    rw [replayBackup_empty_closed_form]
    simp +decide [backedEvents,adverseCompleteS35Before,adverseCompleteProposal,adverseCompleteEvent1,adverseCompleteEvent2,adverseCompleteEvent3,adverseCompleteEvent4,adverseCompleteEvent5,adverseCompleteEvent6,adverseCompleteEvent7,adverseCompleteEvent8,adverseCompleteEvent9,adverseCompleteEvent10,adverseCompleteEvent11,adverseCompleteEvent12,adverseCompleteEvent13,adverseCompleteEvent14,adverseCompleteEvent15,adverseCompleteEvent16,adverseCompleteEvent17,adverseCompleteEvent18,adverseCompleteEvent19,adverseCompleteEvent20,adverseCompleteEvent21,adverseCompleteEvent22,adverseCompleteEvent23,adverseCompleteEvent24,adverseCompleteEvent25,adverseCompleteEvent26,adverseCompleteEvent27,adverseCompleteEvent28,adverseCompleteEvent29,adverseCompleteEvent30,adverseCompleteEvent31,adverseCompleteEvent32,adverseCompleteEvent33,adverseCompleteEvent34,taskReward]
    <;> norm_num
  have hp : rawVisits adverseCompleteS35Before [.query 1,.hydeRetriever 2] = 8 := by decide
  have hn : rawVisits adverseCompleteS35Before ([.query 1,.hydeRetriever 2]++[.selection 0]) = 1 := by decide
  have hz : (controlPenalty savedCref uniformQuoteError unitRoleUnused .complete) adverseCompleteS35Before [.query 1,.hydeRetriever 2] (.selection 0) = 0 := by
    apply control_penalty_empty_of_prior_terminal .complete savedCref uniformQuoteError adverseCompleteS35Before [.query 1,.hydeRetriever 2] (.selection 0) 10 (by decide)
    · decide
    · decide
  unfold indexScore
  rw [hs,hp,hn,hz]
  simp only [BackupStat.mean]
  norm_num

theorem adverseCompleteS35D2Cmp0 : indexScore (7/5) (controlPenalty savedCref uniformQuoteError unitRoleUnused .complete) adverseCompleteS35Before [.query 1,.hydeRetriever 2] (.selection 1) < indexScore (7/5) (controlPenalty savedCref uniformQuoteError unitRoleUnused .complete) adverseCompleteS35Before [.query 1,.hydeRetriever 2] (.selection 0) := by
  rw [adverseCompleteS35D2I0,adverseCompleteS35D2I3]
  have h := index_strict_order_from_intervals ((0/1)/1) ((0/1)/2) 0 0 (103761259/50000000) (1146411/781250)
    (treeBonus (7/5) 8 1) (treeBonus (7/5) 8 2)
    (trajectory_bonus_8_1).1 (trajectory_bonus_8_2).2 (by norm_num)
  simpa only [treeIndex,sub_zero] using h

theorem adverseCompleteS35D2Cmp1 : indexScore (7/5) (controlPenalty savedCref uniformQuoteError unitRoleUnused .complete) adverseCompleteS35Before [.query 1,.hydeRetriever 2] (.selection 2) < indexScore (7/5) (controlPenalty savedCref uniformQuoteError unitRoleUnused .complete) adverseCompleteS35Before [.query 1,.hydeRetriever 2] (.selection 0) := by
  rw [adverseCompleteS35D2I1,adverseCompleteS35D2I3]
  have h := index_strict_order_from_intervals ((0/1)/1) ((0/1)/2) 0 0 (103761259/50000000) (1146411/781250)
    (treeBonus (7/5) 8 1) (treeBonus (7/5) 8 2)
    (trajectory_bonus_8_1).1 (trajectory_bonus_8_2).2 (by norm_num)
  simpa only [treeIndex,sub_zero] using h

theorem adverseCompleteS35D2Cmp2 : indexScore (7/5) (controlPenalty savedCref uniformQuoteError unitRoleUnused .complete) adverseCompleteS35Before [.query 1,.hydeRetriever 2] (.selection 3) < indexScore (7/5) (controlPenalty savedCref uniformQuoteError unitRoleUnused .complete) adverseCompleteS35Before [.query 1,.hydeRetriever 2] (.selection 0) := by
  rw [adverseCompleteS35D2I2,adverseCompleteS35D2I3]
  have h := index_strict_order_from_intervals ((0/1)/1) ((0/1)/2) 0 0 (103761259/50000000) (1146411/781250)
    (treeBonus (7/5) 8 1) (treeBonus (7/5) 8 2)
    (trajectory_bonus_8_1).1 (trajectory_bonus_8_2).2 (by norm_num)
  simpa only [treeIndex,sub_zero] using h

theorem adverseCompleteS35Choice2 : nativeFirstChoice (indexScore (7/5) (controlPenalty savedCref uniformQuoteError unitRoleUnused .complete) adverseCompleteS35Before [.query 1,.hydeRetriever 2]) adverseCompleteS35Before [.query 1,.hydeRetriever 2] = .selection 0 := by
  apply visited_choice_from_ordered_certificate _ _ [.query 1,.hydeRetriever 2] [.selection 1,.selection 2,.selection 3] [] (.selection 0) (by decide)
  · intro a ha
    have ho : orderedLegalAvailable [.query 1,.hydeRetriever 2] = [.selection 1,.selection 2,.selection 3,.selection 0] := by decide
    rw [ho] at ha
    simp only [List.mem_cons,List.not_mem_nil,or_false] at ha
    rcases ha with rfl | rfl | rfl | rfl <;> decide
  · intro a ha
    simp only [List.mem_cons,List.not_mem_nil,or_false] at ha
    rcases ha with rfl | rfl | rfl
    · exact adverseCompleteS35D2Cmp0
    · exact adverseCompleteS35D2Cmp1
    · exact adverseCompleteS35D2Cmp2
  · simp

theorem adverseCompleteS35ActualEvent : nativeEvent budgetTape (7/5) (controlPenalty savedCref uniformQuoteError unitRoleUnused .complete)
    (taskReward true (2/5) (1/2)) adverseCompleteS35Before = adverseCompleteEvent35 := by
  have hs0 := native_select_existing_step budgetTape (7/5) (controlPenalty savedCref uniformQuoteError unitRoleUnused .complete) adverseCompleteS35Before 8 [] (.query 1)
    (by decide) (by decide) adverseCompleteS35Choice0
  have hs1 := native_select_existing_step budgetTape (7/5) (controlPenalty savedCref uniformQuoteError unitRoleUnused .complete) adverseCompleteS35Before 7 [.query 1] (.hydeRetriever 2)
    (by decide) (by decide) adverseCompleteS35Choice1
  have hs2 := native_select_existing_step budgetTape (7/5) (controlPenalty savedCref uniformQuoteError unitRoleUnused .complete) adverseCompleteS35Before 6 [.query 1,.hydeRetriever 2] (.selection 0)
    (by decide) (by decide) adverseCompleteS35Choice2
  have hnew := native_select_new_step budgetTape (7/5) (controlPenalty savedCref uniformQuoteError unitRoleUnused .complete) adverseCompleteS35Before 5 [.query 1,.hydeRetriever 2,.selection 0]
    [.width 3,.width 0,.width 1,.width 2] (.width 0) (by decide) (by decide) (by decide) (by decide)
  have hs : nativeSelect budgetTape (7/5) (controlPenalty savedCref uniformQuoteError unitRoleUnused .complete) adverseCompleteS35Before 9 [] = [.query 1,.hydeRetriever 2,.selection 0,.width 0] := by
    rw [hs0]
    change nativeSelect budgetTape (7/5) (controlPenalty savedCref uniformQuoteError unitRoleUnused .complete) adverseCompleteS35Before 8 [.query 1] = _
    rw [hs1]
    change nativeSelect budgetTape (7/5) (controlPenalty savedCref uniformQuoteError unitRoleUnused .complete) adverseCompleteS35Before 7 [.query 1,.hydeRetriever 2] = _
    rw [hs2]
    change nativeSelect budgetTape (7/5) (controlPenalty savedCref uniformQuoteError unitRoleUnused .complete) adverseCompleteS35Before 6 [.query 1,.hydeRetriever 2,.selection 0] = _
    rw [hnew] <;> rfl
  have hr : repairedRollout budgetTape adverseCompleteS35Before 9 [.query 1,.hydeRetriever 2,.selection 0,.width 0] = [.query 1,.hydeRetriever 2,.selection 0,.width 0,.stop,.reranker 0,.topm 2,.context 0,.answer 2] := by decide
  simp only [nativeEvent,hs,hr]
  rfl

end AgentUCT32MConcrete
