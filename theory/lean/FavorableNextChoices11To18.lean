import ProposalRewards
import TrajectoryBonus
import InitialConcreteBridge
import NextRootIndexBridge
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

def favorableNextS11Before := favorableNextProposal.take 10

theorem favorableNextS11D0I0 : indexScore (7/5) (controlPenalty savedCref uniformQuoteError unitRoleUnused .next) favorableNextS11Before [] (.query 0) = treeIndex ((0/1)/1) (7/5) (nextNormalPenalty favorableNextS11Before) 10 1 := by
  have hs : replayBackup favorableNextS11Before emptyStatistics ([]++[.query 0]) = ⟨1,(0/1)⟩ := by
    rw [replayBackup_empty_closed_form]
    simp +decide [backedEvents,favorableNextS11Before,favorableNextProposal,favorableNextEvent1,favorableNextEvent2,favorableNextEvent3,favorableNextEvent4,favorableNextEvent5,favorableNextEvent6,favorableNextEvent7,favorableNextEvent8,favorableNextEvent9,favorableNextEvent10,taskReward]
    <;> norm_num
  have hp : rawVisits favorableNextS11Before [] = 10 := by decide
  have hn : rawVisits favorableNextS11Before ([]++[.query 0]) = 1 := by decide
  have hz : (controlPenalty savedCref uniformQuoteError unitRoleUnused .next) favorableNextS11Before [] (.query 0) = (nextNormalPenalty favorableNextS11Before) := by
    simpa only [favorableNextS11Before,nextNormalPenalty] using AgentUCTNextExact.favorable_next_normal_root_quotes_exact 10 (by omega) 0 (by decide)
  unfold indexScore
  rw [hs,hp,hn,hz]
  simp only [BackupStat.mean]
  norm_num

theorem favorableNextS11D0I1 : indexScore (7/5) (controlPenalty savedCref uniformQuoteError unitRoleUnused .next) favorableNextS11Before [] (.query 1) = treeIndex ((1/2)/2) (7/5) 0 10 2 := by
  have hs : replayBackup favorableNextS11Before emptyStatistics ([]++[.query 1]) = ⟨2,(1/2)⟩ := by
    rw [replayBackup_empty_closed_form]
    simp +decide [backedEvents,favorableNextS11Before,favorableNextProposal,favorableNextEvent1,favorableNextEvent2,favorableNextEvent3,favorableNextEvent4,favorableNextEvent5,favorableNextEvent6,favorableNextEvent7,favorableNextEvent8,favorableNextEvent9,favorableNextEvent10,taskReward]
    <;> norm_num
  have hp : rawVisits favorableNextS11Before [] = 10 := by decide
  have hn : rawVisits favorableNextS11Before ([]++[.query 1]) = 2 := by decide
  have hz : (controlPenalty savedCref uniformQuoteError unitRoleUnused .next) favorableNextS11Before [] (.query 1) = 0 := by
    apply control_penalty_empty_suffix
    decide
  unfold indexScore
  rw [hs,hp,hn,hz]
  simp only [BackupStat.mean]
  norm_num

theorem favorableNextS11D0I2 : indexScore (7/5) (controlPenalty savedCref uniformQuoteError unitRoleUnused .next) favorableNextS11Before [] (.query 2) = treeIndex ((0/1)/1) (7/5) (nextNormalPenalty favorableNextS11Before) 10 1 := by
  have hs : replayBackup favorableNextS11Before emptyStatistics ([]++[.query 2]) = ⟨1,(0/1)⟩ := by
    rw [replayBackup_empty_closed_form]
    simp +decide [backedEvents,favorableNextS11Before,favorableNextProposal,favorableNextEvent1,favorableNextEvent2,favorableNextEvent3,favorableNextEvent4,favorableNextEvent5,favorableNextEvent6,favorableNextEvent7,favorableNextEvent8,favorableNextEvent9,favorableNextEvent10,taskReward]
    <;> norm_num
  have hp : rawVisits favorableNextS11Before [] = 10 := by decide
  have hn : rawVisits favorableNextS11Before ([]++[.query 2]) = 1 := by decide
  have hz : (controlPenalty savedCref uniformQuoteError unitRoleUnused .next) favorableNextS11Before [] (.query 2) = (nextNormalPenalty favorableNextS11Before) := by
    simpa only [favorableNextS11Before,nextNormalPenalty] using AgentUCTNextExact.favorable_next_normal_root_quotes_exact 10 (by omega) 2 (by decide)
  unfold indexScore
  rw [hs,hp,hn,hz]
  simp only [BackupStat.mean]
  norm_num

theorem favorableNextS11D0I3 : indexScore (7/5) (controlPenalty savedCref uniformQuoteError unitRoleUnused .next) favorableNextS11Before [] (.query 3) = treeIndex ((0/1)/1) (7/5) (nextNormalPenalty favorableNextS11Before) 10 1 := by
  have hs : replayBackup favorableNextS11Before emptyStatistics ([]++[.query 3]) = ⟨1,(0/1)⟩ := by
    rw [replayBackup_empty_closed_form]
    simp +decide [backedEvents,favorableNextS11Before,favorableNextProposal,favorableNextEvent1,favorableNextEvent2,favorableNextEvent3,favorableNextEvent4,favorableNextEvent5,favorableNextEvent6,favorableNextEvent7,favorableNextEvent8,favorableNextEvent9,favorableNextEvent10,taskReward]
    <;> norm_num
  have hp : rawVisits favorableNextS11Before [] = 10 := by decide
  have hn : rawVisits favorableNextS11Before ([]++[.query 3]) = 1 := by decide
  have hz : (controlPenalty savedCref uniformQuoteError unitRoleUnused .next) favorableNextS11Before [] (.query 3) = (nextNormalPenalty favorableNextS11Before) := by
    simpa only [favorableNextS11Before,nextNormalPenalty] using AgentUCTNextExact.favorable_next_normal_root_quotes_exact 10 (by omega) 3 (by decide)
  unfold indexScore
  rw [hs,hp,hn,hz]
  simp only [BackupStat.mean]
  norm_num

theorem favorableNextS11D0I4 : indexScore (7/5) (controlPenalty savedCref uniformQuoteError unitRoleUnused .next) favorableNextS11Before [] (.query 4) = treeIndex ((0/1)/1) (7/5) (nextNormalPenalty favorableNextS11Before) 10 1 := by
  have hs : replayBackup favorableNextS11Before emptyStatistics ([]++[.query 4]) = ⟨1,(0/1)⟩ := by
    rw [replayBackup_empty_closed_form]
    simp +decide [backedEvents,favorableNextS11Before,favorableNextProposal,favorableNextEvent1,favorableNextEvent2,favorableNextEvent3,favorableNextEvent4,favorableNextEvent5,favorableNextEvent6,favorableNextEvent7,favorableNextEvent8,favorableNextEvent9,favorableNextEvent10,taskReward]
    <;> norm_num
  have hp : rawVisits favorableNextS11Before [] = 10 := by decide
  have hn : rawVisits favorableNextS11Before ([]++[.query 4]) = 1 := by decide
  have hz : (controlPenalty savedCref uniformQuoteError unitRoleUnused .next) favorableNextS11Before [] (.query 4) = (nextNormalPenalty favorableNextS11Before) := by
    simpa only [favorableNextS11Before,nextNormalPenalty] using AgentUCTNextExact.favorable_next_normal_root_quotes_exact 10 (by omega) 4 (by decide)
  unfold indexScore
  rw [hs,hp,hn,hz]
  simp only [BackupStat.mean]
  norm_num

theorem favorableNextS11D0I5 : indexScore (7/5) (controlPenalty savedCref uniformQuoteError unitRoleUnused .next) favorableNextS11Before [] (.query 5) = treeIndex ((4/5)/2) (7/5) (nextNormalPenalty favorableNextS11Before) 10 2 := by
  have hs : replayBackup favorableNextS11Before emptyStatistics ([]++[.query 5]) = ⟨2,(4/5)⟩ := by
    rw [replayBackup_empty_closed_form]
    simp +decide [backedEvents,favorableNextS11Before,favorableNextProposal,favorableNextEvent1,favorableNextEvent2,favorableNextEvent3,favorableNextEvent4,favorableNextEvent5,favorableNextEvent6,favorableNextEvent7,favorableNextEvent8,favorableNextEvent9,favorableNextEvent10,taskReward]
    <;> norm_num
  have hp : rawVisits favorableNextS11Before [] = 10 := by decide
  have hn : rawVisits favorableNextS11Before ([]++[.query 5]) = 2 := by decide
  have hz : (controlPenalty savedCref uniformQuoteError unitRoleUnused .next) favorableNextS11Before [] (.query 5) = (nextNormalPenalty favorableNextS11Before) := by
    simpa only [favorableNextS11Before,nextNormalPenalty] using AgentUCTNextExact.favorable_next_normal_root_quotes_exact 10 (by omega) 5 (by decide)
  unfold indexScore
  rw [hs,hp,hn,hz]
  simp only [BackupStat.mean]
  norm_num

theorem favorableNextS11D0I6 : indexScore (7/5) (controlPenalty savedCref uniformQuoteError unitRoleUnused .next) favorableNextS11Before [] (.query 6) = treeIndex ((0/1)/1) (7/5) (nextNormalPenalty favorableNextS11Before) 10 1 := by
  have hs : replayBackup favorableNextS11Before emptyStatistics ([]++[.query 6]) = ⟨1,(0/1)⟩ := by
    rw [replayBackup_empty_closed_form]
    simp +decide [backedEvents,favorableNextS11Before,favorableNextProposal,favorableNextEvent1,favorableNextEvent2,favorableNextEvent3,favorableNextEvent4,favorableNextEvent5,favorableNextEvent6,favorableNextEvent7,favorableNextEvent8,favorableNextEvent9,favorableNextEvent10,taskReward]
    <;> norm_num
  have hp : rawVisits favorableNextS11Before [] = 10 := by decide
  have hn : rawVisits favorableNextS11Before ([]++[.query 6]) = 1 := by decide
  have hz : (controlPenalty savedCref uniformQuoteError unitRoleUnused .next) favorableNextS11Before [] (.query 6) = (nextNormalPenalty favorableNextS11Before) := by
    simpa only [favorableNextS11Before,nextNormalPenalty] using AgentUCTNextExact.favorable_next_normal_root_quotes_exact 10 (by omega) 6 (by decide)
  unfold indexScore
  rw [hs,hp,hn,hz]
  simp only [BackupStat.mean]
  norm_num

theorem favorableNextS11D0I7 : indexScore (7/5) (controlPenalty savedCref uniformQuoteError unitRoleUnused .next) favorableNextS11Before [] (.query 7) = treeIndex ((0/1)/1) (7/5) (nextNormalPenalty favorableNextS11Before) 10 1 := by
  have hs : replayBackup favorableNextS11Before emptyStatistics ([]++[.query 7]) = ⟨1,(0/1)⟩ := by
    rw [replayBackup_empty_closed_form]
    simp +decide [backedEvents,favorableNextS11Before,favorableNextProposal,favorableNextEvent1,favorableNextEvent2,favorableNextEvent3,favorableNextEvent4,favorableNextEvent5,favorableNextEvent6,favorableNextEvent7,favorableNextEvent8,favorableNextEvent9,favorableNextEvent10,taskReward]
    <;> norm_num
  have hp : rawVisits favorableNextS11Before [] = 10 := by decide
  have hn : rawVisits favorableNextS11Before ([]++[.query 7]) = 1 := by decide
  have hz : (controlPenalty savedCref uniformQuoteError unitRoleUnused .next) favorableNextS11Before [] (.query 7) = (nextNormalPenalty favorableNextS11Before) := by
    simpa only [favorableNextS11Before,nextNormalPenalty] using AgentUCTNextExact.favorable_next_normal_root_quotes_exact 10 (by omega) 7 (by decide)
  unfold indexScore
  rw [hs,hp,hn,hz]
  simp only [BackupStat.mean]
  norm_num

theorem favorableNextS11D0Cmp1 : indexScore (7/5) (controlPenalty savedCref uniformQuoteError unitRoleUnused .next) favorableNextS11Before [] (.query 1) ≤ indexScore (7/5) (controlPenalty savedCref uniformQuoteError unitRoleUnused .next) favorableNextS11Before [] (.query 0) := by
  rw [favorableNextS11D0I1,favorableNextS11D0I0]
  have hk := favorable_next_penalty_interval 10 (by omega)
  change nextNormalPenaltyLower ≤ nextNormalPenalty favorableNextS11Before ∧ nextNormalPenalty favorableNextS11Before ≤ nextNormalPenaltyUpper at hk
  have hm : ((1/2)/2)+(76647529/50000000)-0 < ((0/1)/1)+(54197983/25000000)-(nextNormalPenalty favorableNextS11Before) := by
    have h : ((1/2)/2)+(76647529/50000000) < ((0/1)/1)+(54197983/25000000)-nextNormalPenaltyUpper := by norm_num [nextNormalPenaltyUpper,savedCref,uniformQuoteError]
    linarith [hk.2]
  have h := index_weak_order_from_intervals ((0/1)/1) ((1/2)/2) (nextNormalPenalty favorableNextS11Before) 0 (54197983/25000000) (76647529/50000000)
    (treeBonus (7/5) 10 1) (treeBonus (7/5) 10 2)
    (trajectory_bonus_10_1).1 (trajectory_bonus_10_2).2 hm.le
  simpa only [treeIndex] using h

theorem favorableNextS11D0Cmp2 : indexScore (7/5) (controlPenalty savedCref uniformQuoteError unitRoleUnused .next) favorableNextS11Before [] (.query 2) ≤ indexScore (7/5) (controlPenalty savedCref uniformQuoteError unitRoleUnused .next) favorableNextS11Before [] (.query 0) := by
  rw [favorableNextS11D0I2,favorableNextS11D0I0]

theorem favorableNextS11D0Cmp3 : indexScore (7/5) (controlPenalty savedCref uniformQuoteError unitRoleUnused .next) favorableNextS11Before [] (.query 3) ≤ indexScore (7/5) (controlPenalty savedCref uniformQuoteError unitRoleUnused .next) favorableNextS11Before [] (.query 0) := by
  rw [favorableNextS11D0I3,favorableNextS11D0I0]

theorem favorableNextS11D0Cmp4 : indexScore (7/5) (controlPenalty savedCref uniformQuoteError unitRoleUnused .next) favorableNextS11Before [] (.query 4) ≤ indexScore (7/5) (controlPenalty savedCref uniformQuoteError unitRoleUnused .next) favorableNextS11Before [] (.query 0) := by
  rw [favorableNextS11D0I4,favorableNextS11D0I0]

theorem favorableNextS11D0Cmp5 : indexScore (7/5) (controlPenalty savedCref uniformQuoteError unitRoleUnused .next) favorableNextS11Before [] (.query 5) ≤ indexScore (7/5) (controlPenalty savedCref uniformQuoteError unitRoleUnused .next) favorableNextS11Before [] (.query 0) := by
  rw [favorableNextS11D0I5,favorableNextS11D0I0]
  have hk := favorable_next_penalty_interval 10 (by omega)
  change nextNormalPenaltyLower ≤ nextNormalPenalty favorableNextS11Before ∧ nextNormalPenalty favorableNextS11Before ≤ nextNormalPenaltyUpper at hk
  have hm : ((4/5)/2)+(76647529/50000000)-(nextNormalPenalty favorableNextS11Before) < ((0/1)/1)+(54197983/25000000)-(nextNormalPenalty favorableNextS11Before) := by
    have h : (((4/5)/2)+(76647529/50000000) : ℝ) < ((0/1)/1)+(54197983/25000000) := by norm_num
    linarith
  have h := index_weak_order_from_intervals ((0/1)/1) ((4/5)/2) (nextNormalPenalty favorableNextS11Before) (nextNormalPenalty favorableNextS11Before) (54197983/25000000) (76647529/50000000)
    (treeBonus (7/5) 10 1) (treeBonus (7/5) 10 2)
    (trajectory_bonus_10_1).1 (trajectory_bonus_10_2).2 hm.le
  simpa only [treeIndex] using h

theorem favorableNextS11D0Cmp6 : indexScore (7/5) (controlPenalty savedCref uniformQuoteError unitRoleUnused .next) favorableNextS11Before [] (.query 6) ≤ indexScore (7/5) (controlPenalty savedCref uniformQuoteError unitRoleUnused .next) favorableNextS11Before [] (.query 0) := by
  rw [favorableNextS11D0I6,favorableNextS11D0I0]

theorem favorableNextS11D0Cmp7 : indexScore (7/5) (controlPenalty savedCref uniformQuoteError unitRoleUnused .next) favorableNextS11Before [] (.query 7) ≤ indexScore (7/5) (controlPenalty savedCref uniformQuoteError unitRoleUnused .next) favorableNextS11Before [] (.query 0) := by
  rw [favorableNextS11D0I7,favorableNextS11D0I0]

theorem favorableNextS11Choice0 : nativeFirstChoice (indexScore (7/5) (controlPenalty savedCref uniformQuoteError unitRoleUnused .next) favorableNextS11Before []) favorableNextS11Before [] = .query 0 := by
  apply visited_choice_from_ordered_certificate _ _ [] [] [.query 1,.query 2,.query 3,.query 4,.query 5,.query 6,.query 7] (.query 0) (by decide)
  · intro a ha
    have ho : orderedLegalAvailable [] = [.query 0,.query 1,.query 2,.query 3,.query 4,.query 5,.query 6,.query 7] := by decide
    rw [ho] at ha
    simp only [List.mem_cons,List.not_mem_nil,or_false] at ha
    rcases ha with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> decide
  · simp
  · intro a ha
    simp only [List.mem_cons,List.not_mem_nil,or_false] at ha
    rcases ha with rfl | rfl | rfl | rfl | rfl | rfl | rfl
    · exact favorableNextS11D0Cmp1
    · exact favorableNextS11D0Cmp2
    · exact favorableNextS11D0Cmp3
    · exact favorableNextS11D0Cmp4
    · exact favorableNextS11D0Cmp5
    · exact favorableNextS11D0Cmp6
    · exact favorableNextS11D0Cmp7

theorem favorableNextS11ActualEvent : nativeEvent budgetTape (7/5) (controlPenalty savedCref uniformQuoteError unitRoleUnused .next)
    (taskReward false (2/5) (1/2)) favorableNextS11Before = favorableNextEvent11 := by
  have hs0 := native_select_existing_step budgetTape (7/5) (controlPenalty savedCref uniformQuoteError unitRoleUnused .next) favorableNextS11Before 8 [] (.query 0)
    (by decide) (by decide) favorableNextS11Choice0
  have hnew := native_select_new_step budgetTape (7/5) (controlPenalty savedCref uniformQuoteError unitRoleUnused .next) favorableNextS11Before 7 [.query 0]
    [.normalRetriever 4,.normalRetriever 6,.normalRetriever 7,.normalRetriever 8,.normalRetriever 5,.normalRetriever 0,.normalRetriever 1,.normalRetriever 2,.normalRetriever 3,.normalRetriever 12,.normalRetriever 14,.normalRetriever 13,.normalRetriever 21,.normalRetriever 23,.normalRetriever 22,.normalRetriever 9,.normalRetriever 11,.normalRetriever 10,.normalRetriever 15,.normalRetriever 17,.normalRetriever 16,.normalRetriever 18,.normalRetriever 20,.normalRetriever 19,.normalRetriever 24,.normalRetriever 25,.normalRetriever 26,.normalRetriever 27,.normalRetriever 28,.normalRetriever 29] (.normalRetriever 0) (by decide) (by decide) (by decide) (by decide)
  have hs : nativeSelect budgetTape (7/5) (controlPenalty savedCref uniformQuoteError unitRoleUnused .next) favorableNextS11Before 9 [] = [.query 0,.normalRetriever 0] := by
    rw [hs0]
    change nativeSelect budgetTape (7/5) (controlPenalty savedCref uniformQuoteError unitRoleUnused .next) favorableNextS11Before 8 [.query 0] = _
    rw [hnew] <;> rfl
  have hr : repairedRollout budgetTape favorableNextS11Before 9 [.query 0,.normalRetriever 0] = [.query 0,.normalRetriever 0,.selection 0,.width 0,.stop,.reranker 0,.topm 0,.context 0,.answer 0] := by decide
  simp only [nativeEvent,hs,hr]
  rfl

def favorableNextS12Before := favorableNextProposal.take 11

theorem favorableNextS12D0I0 : indexScore (7/5) (controlPenalty savedCref uniformQuoteError unitRoleUnused .next) favorableNextS12Before [] (.query 0) = treeIndex ((0/1)/2) (7/5) (nextNormalPenalty favorableNextS12Before) 11 2 := by
  have hs : replayBackup favorableNextS12Before emptyStatistics ([]++[.query 0]) = ⟨2,(0/1)⟩ := by
    rw [replayBackup_empty_closed_form]
    simp +decide [backedEvents,favorableNextS12Before,favorableNextProposal,favorableNextEvent1,favorableNextEvent2,favorableNextEvent3,favorableNextEvent4,favorableNextEvent5,favorableNextEvent6,favorableNextEvent7,favorableNextEvent8,favorableNextEvent9,favorableNextEvent10,favorableNextEvent11,taskReward]
    <;> norm_num
  have hp : rawVisits favorableNextS12Before [] = 11 := by decide
  have hn : rawVisits favorableNextS12Before ([]++[.query 0]) = 2 := by decide
  have hz : (controlPenalty savedCref uniformQuoteError unitRoleUnused .next) favorableNextS12Before [] (.query 0) = (nextNormalPenalty favorableNextS12Before) := by
    simpa only [favorableNextS12Before,nextNormalPenalty] using AgentUCTNextExact.favorable_next_normal_root_quotes_exact 11 (by omega) 0 (by decide)
  unfold indexScore
  rw [hs,hp,hn,hz]
  simp only [BackupStat.mean]
  norm_num

theorem favorableNextS12D0I1 : indexScore (7/5) (controlPenalty savedCref uniformQuoteError unitRoleUnused .next) favorableNextS12Before [] (.query 1) = treeIndex ((1/2)/2) (7/5) 0 11 2 := by
  have hs : replayBackup favorableNextS12Before emptyStatistics ([]++[.query 1]) = ⟨2,(1/2)⟩ := by
    rw [replayBackup_empty_closed_form]
    simp +decide [backedEvents,favorableNextS12Before,favorableNextProposal,favorableNextEvent1,favorableNextEvent2,favorableNextEvent3,favorableNextEvent4,favorableNextEvent5,favorableNextEvent6,favorableNextEvent7,favorableNextEvent8,favorableNextEvent9,favorableNextEvent10,favorableNextEvent11,taskReward]
    <;> norm_num
  have hp : rawVisits favorableNextS12Before [] = 11 := by decide
  have hn : rawVisits favorableNextS12Before ([]++[.query 1]) = 2 := by decide
  have hz : (controlPenalty savedCref uniformQuoteError unitRoleUnused .next) favorableNextS12Before [] (.query 1) = 0 := by
    apply control_penalty_empty_suffix
    decide
  unfold indexScore
  rw [hs,hp,hn,hz]
  simp only [BackupStat.mean]
  norm_num

theorem favorableNextS12D0I2 : indexScore (7/5) (controlPenalty savedCref uniformQuoteError unitRoleUnused .next) favorableNextS12Before [] (.query 2) = treeIndex ((0/1)/1) (7/5) (nextNormalPenalty favorableNextS12Before) 11 1 := by
  have hs : replayBackup favorableNextS12Before emptyStatistics ([]++[.query 2]) = ⟨1,(0/1)⟩ := by
    rw [replayBackup_empty_closed_form]
    simp +decide [backedEvents,favorableNextS12Before,favorableNextProposal,favorableNextEvent1,favorableNextEvent2,favorableNextEvent3,favorableNextEvent4,favorableNextEvent5,favorableNextEvent6,favorableNextEvent7,favorableNextEvent8,favorableNextEvent9,favorableNextEvent10,favorableNextEvent11,taskReward]
    <;> norm_num
  have hp : rawVisits favorableNextS12Before [] = 11 := by decide
  have hn : rawVisits favorableNextS12Before ([]++[.query 2]) = 1 := by decide
  have hz : (controlPenalty savedCref uniformQuoteError unitRoleUnused .next) favorableNextS12Before [] (.query 2) = (nextNormalPenalty favorableNextS12Before) := by
    simpa only [favorableNextS12Before,nextNormalPenalty] using AgentUCTNextExact.favorable_next_normal_root_quotes_exact 11 (by omega) 2 (by decide)
  unfold indexScore
  rw [hs,hp,hn,hz]
  simp only [BackupStat.mean]
  norm_num

theorem favorableNextS12D0I3 : indexScore (7/5) (controlPenalty savedCref uniformQuoteError unitRoleUnused .next) favorableNextS12Before [] (.query 3) = treeIndex ((0/1)/1) (7/5) (nextNormalPenalty favorableNextS12Before) 11 1 := by
  have hs : replayBackup favorableNextS12Before emptyStatistics ([]++[.query 3]) = ⟨1,(0/1)⟩ := by
    rw [replayBackup_empty_closed_form]
    simp +decide [backedEvents,favorableNextS12Before,favorableNextProposal,favorableNextEvent1,favorableNextEvent2,favorableNextEvent3,favorableNextEvent4,favorableNextEvent5,favorableNextEvent6,favorableNextEvent7,favorableNextEvent8,favorableNextEvent9,favorableNextEvent10,favorableNextEvent11,taskReward]
    <;> norm_num
  have hp : rawVisits favorableNextS12Before [] = 11 := by decide
  have hn : rawVisits favorableNextS12Before ([]++[.query 3]) = 1 := by decide
  have hz : (controlPenalty savedCref uniformQuoteError unitRoleUnused .next) favorableNextS12Before [] (.query 3) = (nextNormalPenalty favorableNextS12Before) := by
    simpa only [favorableNextS12Before,nextNormalPenalty] using AgentUCTNextExact.favorable_next_normal_root_quotes_exact 11 (by omega) 3 (by decide)
  unfold indexScore
  rw [hs,hp,hn,hz]
  simp only [BackupStat.mean]
  norm_num

theorem favorableNextS12D0I4 : indexScore (7/5) (controlPenalty savedCref uniformQuoteError unitRoleUnused .next) favorableNextS12Before [] (.query 4) = treeIndex ((0/1)/1) (7/5) (nextNormalPenalty favorableNextS12Before) 11 1 := by
  have hs : replayBackup favorableNextS12Before emptyStatistics ([]++[.query 4]) = ⟨1,(0/1)⟩ := by
    rw [replayBackup_empty_closed_form]
    simp +decide [backedEvents,favorableNextS12Before,favorableNextProposal,favorableNextEvent1,favorableNextEvent2,favorableNextEvent3,favorableNextEvent4,favorableNextEvent5,favorableNextEvent6,favorableNextEvent7,favorableNextEvent8,favorableNextEvent9,favorableNextEvent10,favorableNextEvent11,taskReward]
    <;> norm_num
  have hp : rawVisits favorableNextS12Before [] = 11 := by decide
  have hn : rawVisits favorableNextS12Before ([]++[.query 4]) = 1 := by decide
  have hz : (controlPenalty savedCref uniformQuoteError unitRoleUnused .next) favorableNextS12Before [] (.query 4) = (nextNormalPenalty favorableNextS12Before) := by
    simpa only [favorableNextS12Before,nextNormalPenalty] using AgentUCTNextExact.favorable_next_normal_root_quotes_exact 11 (by omega) 4 (by decide)
  unfold indexScore
  rw [hs,hp,hn,hz]
  simp only [BackupStat.mean]
  norm_num

theorem favorableNextS12D0I5 : indexScore (7/5) (controlPenalty savedCref uniformQuoteError unitRoleUnused .next) favorableNextS12Before [] (.query 5) = treeIndex ((4/5)/2) (7/5) (nextNormalPenalty favorableNextS12Before) 11 2 := by
  have hs : replayBackup favorableNextS12Before emptyStatistics ([]++[.query 5]) = ⟨2,(4/5)⟩ := by
    rw [replayBackup_empty_closed_form]
    simp +decide [backedEvents,favorableNextS12Before,favorableNextProposal,favorableNextEvent1,favorableNextEvent2,favorableNextEvent3,favorableNextEvent4,favorableNextEvent5,favorableNextEvent6,favorableNextEvent7,favorableNextEvent8,favorableNextEvent9,favorableNextEvent10,favorableNextEvent11,taskReward]
    <;> norm_num
  have hp : rawVisits favorableNextS12Before [] = 11 := by decide
  have hn : rawVisits favorableNextS12Before ([]++[.query 5]) = 2 := by decide
  have hz : (controlPenalty savedCref uniformQuoteError unitRoleUnused .next) favorableNextS12Before [] (.query 5) = (nextNormalPenalty favorableNextS12Before) := by
    simpa only [favorableNextS12Before,nextNormalPenalty] using AgentUCTNextExact.favorable_next_normal_root_quotes_exact 11 (by omega) 5 (by decide)
  unfold indexScore
  rw [hs,hp,hn,hz]
  simp only [BackupStat.mean]
  norm_num

theorem favorableNextS12D0I6 : indexScore (7/5) (controlPenalty savedCref uniformQuoteError unitRoleUnused .next) favorableNextS12Before [] (.query 6) = treeIndex ((0/1)/1) (7/5) (nextNormalPenalty favorableNextS12Before) 11 1 := by
  have hs : replayBackup favorableNextS12Before emptyStatistics ([]++[.query 6]) = ⟨1,(0/1)⟩ := by
    rw [replayBackup_empty_closed_form]
    simp +decide [backedEvents,favorableNextS12Before,favorableNextProposal,favorableNextEvent1,favorableNextEvent2,favorableNextEvent3,favorableNextEvent4,favorableNextEvent5,favorableNextEvent6,favorableNextEvent7,favorableNextEvent8,favorableNextEvent9,favorableNextEvent10,favorableNextEvent11,taskReward]
    <;> norm_num
  have hp : rawVisits favorableNextS12Before [] = 11 := by decide
  have hn : rawVisits favorableNextS12Before ([]++[.query 6]) = 1 := by decide
  have hz : (controlPenalty savedCref uniformQuoteError unitRoleUnused .next) favorableNextS12Before [] (.query 6) = (nextNormalPenalty favorableNextS12Before) := by
    simpa only [favorableNextS12Before,nextNormalPenalty] using AgentUCTNextExact.favorable_next_normal_root_quotes_exact 11 (by omega) 6 (by decide)
  unfold indexScore
  rw [hs,hp,hn,hz]
  simp only [BackupStat.mean]
  norm_num

theorem favorableNextS12D0I7 : indexScore (7/5) (controlPenalty savedCref uniformQuoteError unitRoleUnused .next) favorableNextS12Before [] (.query 7) = treeIndex ((0/1)/1) (7/5) (nextNormalPenalty favorableNextS12Before) 11 1 := by
  have hs : replayBackup favorableNextS12Before emptyStatistics ([]++[.query 7]) = ⟨1,(0/1)⟩ := by
    rw [replayBackup_empty_closed_form]
    simp +decide [backedEvents,favorableNextS12Before,favorableNextProposal,favorableNextEvent1,favorableNextEvent2,favorableNextEvent3,favorableNextEvent4,favorableNextEvent5,favorableNextEvent6,favorableNextEvent7,favorableNextEvent8,favorableNextEvent9,favorableNextEvent10,favorableNextEvent11,taskReward]
    <;> norm_num
  have hp : rawVisits favorableNextS12Before [] = 11 := by decide
  have hn : rawVisits favorableNextS12Before ([]++[.query 7]) = 1 := by decide
  have hz : (controlPenalty savedCref uniformQuoteError unitRoleUnused .next) favorableNextS12Before [] (.query 7) = (nextNormalPenalty favorableNextS12Before) := by
    simpa only [favorableNextS12Before,nextNormalPenalty] using AgentUCTNextExact.favorable_next_normal_root_quotes_exact 11 (by omega) 7 (by decide)
  unfold indexScore
  rw [hs,hp,hn,hz]
  simp only [BackupStat.mean]
  norm_num

theorem favorableNextS12D0Cmp0 : indexScore (7/5) (controlPenalty savedCref uniformQuoteError unitRoleUnused .next) favorableNextS12Before [] (.query 0) < indexScore (7/5) (controlPenalty savedCref uniformQuoteError unitRoleUnused .next) favorableNextS12Before [] (.query 2) := by
  rw [favorableNextS12D0I0,favorableNextS12D0I2]
  have hk := favorable_next_penalty_interval 11 (by omega)
  change nextNormalPenaltyLower ≤ nextNormalPenalty favorableNextS12Before ∧ nextNormalPenalty favorableNextS12Before ≤ nextNormalPenaltyUpper at hk
  have hm : ((0/1)/2)+(3901289/2500000)-(nextNormalPenalty favorableNextS12Before) < ((0/1)/1)+(55172551/25000000)-(nextNormalPenalty favorableNextS12Before) := by
    have h : (((0/1)/2)+(3901289/2500000) : ℝ) < ((0/1)/1)+(55172551/25000000) := by norm_num
    linarith
  have h := index_strict_order_from_intervals ((0/1)/1) ((0/1)/2) (nextNormalPenalty favorableNextS12Before) (nextNormalPenalty favorableNextS12Before) (55172551/25000000) (3901289/2500000)
    (treeBonus (7/5) 11 1) (treeBonus (7/5) 11 2)
    (trajectory_bonus_11_1).1 (trajectory_bonus_11_2).2 hm
  simpa only [treeIndex] using h

theorem favorableNextS12D0Cmp1 : indexScore (7/5) (controlPenalty savedCref uniformQuoteError unitRoleUnused .next) favorableNextS12Before [] (.query 1) < indexScore (7/5) (controlPenalty savedCref uniformQuoteError unitRoleUnused .next) favorableNextS12Before [] (.query 2) := by
  rw [favorableNextS12D0I1,favorableNextS12D0I2]
  have hk := favorable_next_penalty_interval 11 (by omega)
  change nextNormalPenaltyLower ≤ nextNormalPenalty favorableNextS12Before ∧ nextNormalPenalty favorableNextS12Before ≤ nextNormalPenaltyUpper at hk
  have hm : ((1/2)/2)+(3901289/2500000)-0 < ((0/1)/1)+(55172551/25000000)-(nextNormalPenalty favorableNextS12Before) := by
    have h : ((1/2)/2)+(3901289/2500000) < ((0/1)/1)+(55172551/25000000)-nextNormalPenaltyUpper := by norm_num [nextNormalPenaltyUpper,savedCref,uniformQuoteError]
    linarith [hk.2]
  have h := index_strict_order_from_intervals ((0/1)/1) ((1/2)/2) (nextNormalPenalty favorableNextS12Before) 0 (55172551/25000000) (3901289/2500000)
    (treeBonus (7/5) 11 1) (treeBonus (7/5) 11 2)
    (trajectory_bonus_11_1).1 (trajectory_bonus_11_2).2 hm
  simpa only [treeIndex] using h

theorem favorableNextS12D0Cmp3 : indexScore (7/5) (controlPenalty savedCref uniformQuoteError unitRoleUnused .next) favorableNextS12Before [] (.query 3) ≤ indexScore (7/5) (controlPenalty savedCref uniformQuoteError unitRoleUnused .next) favorableNextS12Before [] (.query 2) := by
  rw [favorableNextS12D0I3,favorableNextS12D0I2]

theorem favorableNextS12D0Cmp4 : indexScore (7/5) (controlPenalty savedCref uniformQuoteError unitRoleUnused .next) favorableNextS12Before [] (.query 4) ≤ indexScore (7/5) (controlPenalty savedCref uniformQuoteError unitRoleUnused .next) favorableNextS12Before [] (.query 2) := by
  rw [favorableNextS12D0I4,favorableNextS12D0I2]

theorem favorableNextS12D0Cmp5 : indexScore (7/5) (controlPenalty savedCref uniformQuoteError unitRoleUnused .next) favorableNextS12Before [] (.query 5) ≤ indexScore (7/5) (controlPenalty savedCref uniformQuoteError unitRoleUnused .next) favorableNextS12Before [] (.query 2) := by
  rw [favorableNextS12D0I5,favorableNextS12D0I2]
  have hk := favorable_next_penalty_interval 11 (by omega)
  change nextNormalPenaltyLower ≤ nextNormalPenalty favorableNextS12Before ∧ nextNormalPenalty favorableNextS12Before ≤ nextNormalPenaltyUpper at hk
  have hm : ((4/5)/2)+(3901289/2500000)-(nextNormalPenalty favorableNextS12Before) < ((0/1)/1)+(55172551/25000000)-(nextNormalPenalty favorableNextS12Before) := by
    have h : (((4/5)/2)+(3901289/2500000) : ℝ) < ((0/1)/1)+(55172551/25000000) := by norm_num
    linarith
  have h := index_weak_order_from_intervals ((0/1)/1) ((4/5)/2) (nextNormalPenalty favorableNextS12Before) (nextNormalPenalty favorableNextS12Before) (55172551/25000000) (3901289/2500000)
    (treeBonus (7/5) 11 1) (treeBonus (7/5) 11 2)
    (trajectory_bonus_11_1).1 (trajectory_bonus_11_2).2 hm.le
  simpa only [treeIndex] using h

theorem favorableNextS12D0Cmp6 : indexScore (7/5) (controlPenalty savedCref uniformQuoteError unitRoleUnused .next) favorableNextS12Before [] (.query 6) ≤ indexScore (7/5) (controlPenalty savedCref uniformQuoteError unitRoleUnused .next) favorableNextS12Before [] (.query 2) := by
  rw [favorableNextS12D0I6,favorableNextS12D0I2]

theorem favorableNextS12D0Cmp7 : indexScore (7/5) (controlPenalty savedCref uniformQuoteError unitRoleUnused .next) favorableNextS12Before [] (.query 7) ≤ indexScore (7/5) (controlPenalty savedCref uniformQuoteError unitRoleUnused .next) favorableNextS12Before [] (.query 2) := by
  rw [favorableNextS12D0I7,favorableNextS12D0I2]

theorem favorableNextS12Choice0 : nativeFirstChoice (indexScore (7/5) (controlPenalty savedCref uniformQuoteError unitRoleUnused .next) favorableNextS12Before []) favorableNextS12Before [] = .query 2 := by
  apply visited_choice_from_ordered_certificate _ _ [] [.query 0,.query 1] [.query 3,.query 4,.query 5,.query 6,.query 7] (.query 2) (by decide)
  · intro a ha
    have ho : orderedLegalAvailable [] = [.query 0,.query 1,.query 2,.query 3,.query 4,.query 5,.query 6,.query 7] := by decide
    rw [ho] at ha
    simp only [List.mem_cons,List.not_mem_nil,or_false] at ha
    rcases ha with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> decide
  · intro a ha
    simp only [List.mem_cons,List.not_mem_nil,or_false] at ha
    rcases ha with rfl | rfl
    · exact favorableNextS12D0Cmp0
    · exact favorableNextS12D0Cmp1
  · intro a ha
    simp only [List.mem_cons,List.not_mem_nil,or_false] at ha
    rcases ha with rfl | rfl | rfl | rfl | rfl
    · exact favorableNextS12D0Cmp3
    · exact favorableNextS12D0Cmp4
    · exact favorableNextS12D0Cmp5
    · exact favorableNextS12D0Cmp6
    · exact favorableNextS12D0Cmp7

theorem favorableNextS12ActualEvent : nativeEvent budgetTape (7/5) (controlPenalty savedCref uniformQuoteError unitRoleUnused .next)
    (taskReward false (2/5) (1/2)) favorableNextS12Before = favorableNextEvent12 := by
  have hs0 := native_select_existing_step budgetTape (7/5) (controlPenalty savedCref uniformQuoteError unitRoleUnused .next) favorableNextS12Before 8 [] (.query 2)
    (by decide) (by decide) favorableNextS12Choice0
  have hnew := native_select_new_step budgetTape (7/5) (controlPenalty savedCref uniformQuoteError unitRoleUnused .next) favorableNextS12Before 7 [.query 2]
    [.normalRetriever 4,.normalRetriever 6,.normalRetriever 7,.normalRetriever 8,.normalRetriever 5,.normalRetriever 0,.normalRetriever 1,.normalRetriever 2,.normalRetriever 3,.normalRetriever 12,.normalRetriever 14,.normalRetriever 13,.normalRetriever 21,.normalRetriever 23,.normalRetriever 22,.normalRetriever 9,.normalRetriever 11,.normalRetriever 10,.normalRetriever 15,.normalRetriever 17,.normalRetriever 16,.normalRetriever 18,.normalRetriever 20,.normalRetriever 19,.normalRetriever 24,.normalRetriever 25,.normalRetriever 26,.normalRetriever 27,.normalRetriever 28,.normalRetriever 29] (.normalRetriever 0) (by decide) (by decide) (by decide) (by decide)
  have hs : nativeSelect budgetTape (7/5) (controlPenalty savedCref uniformQuoteError unitRoleUnused .next) favorableNextS12Before 9 [] = [.query 2,.normalRetriever 0] := by
    rw [hs0]
    change nativeSelect budgetTape (7/5) (controlPenalty savedCref uniformQuoteError unitRoleUnused .next) favorableNextS12Before 8 [.query 2] = _
    rw [hnew] <;> rfl
  have hr : repairedRollout budgetTape favorableNextS12Before 9 [.query 2,.normalRetriever 0] = [.query 2,.normalRetriever 0,.selection 0,.width 0,.stop,.reranker 0,.topm 0,.context 0,.answer 0] := by decide
  simp only [nativeEvent,hs,hr]
  rfl

def favorableNextS13Before := favorableNextProposal.take 12

theorem favorableNextS13D0I0 : indexScore (7/5) (controlPenalty savedCref uniformQuoteError unitRoleUnused .next) favorableNextS13Before [] (.query 0) = treeIndex ((0/1)/2) (7/5) (nextNormalPenalty favorableNextS13Before) 12 2 := by
  have hs : replayBackup favorableNextS13Before emptyStatistics ([]++[.query 0]) = ⟨2,(0/1)⟩ := by
    rw [replayBackup_empty_closed_form]
    simp +decide [backedEvents,favorableNextS13Before,favorableNextProposal,favorableNextEvent1,favorableNextEvent2,favorableNextEvent3,favorableNextEvent4,favorableNextEvent5,favorableNextEvent6,favorableNextEvent7,favorableNextEvent8,favorableNextEvent9,favorableNextEvent10,favorableNextEvent11,favorableNextEvent12,taskReward]
    <;> norm_num
  have hp : rawVisits favorableNextS13Before [] = 12 := by decide
  have hn : rawVisits favorableNextS13Before ([]++[.query 0]) = 2 := by decide
  have hz : (controlPenalty savedCref uniformQuoteError unitRoleUnused .next) favorableNextS13Before [] (.query 0) = (nextNormalPenalty favorableNextS13Before) := by
    simpa only [favorableNextS13Before,nextNormalPenalty] using AgentUCTNextExact.favorable_next_normal_root_quotes_exact 12 (by omega) 0 (by decide)
  unfold indexScore
  rw [hs,hp,hn,hz]
  simp only [BackupStat.mean]
  norm_num

theorem favorableNextS13D0I1 : indexScore (7/5) (controlPenalty savedCref uniformQuoteError unitRoleUnused .next) favorableNextS13Before [] (.query 1) = treeIndex ((1/2)/2) (7/5) 0 12 2 := by
  have hs : replayBackup favorableNextS13Before emptyStatistics ([]++[.query 1]) = ⟨2,(1/2)⟩ := by
    rw [replayBackup_empty_closed_form]
    simp +decide [backedEvents,favorableNextS13Before,favorableNextProposal,favorableNextEvent1,favorableNextEvent2,favorableNextEvent3,favorableNextEvent4,favorableNextEvent5,favorableNextEvent6,favorableNextEvent7,favorableNextEvent8,favorableNextEvent9,favorableNextEvent10,favorableNextEvent11,favorableNextEvent12,taskReward]
    <;> norm_num
  have hp : rawVisits favorableNextS13Before [] = 12 := by decide
  have hn : rawVisits favorableNextS13Before ([]++[.query 1]) = 2 := by decide
  have hz : (controlPenalty savedCref uniformQuoteError unitRoleUnused .next) favorableNextS13Before [] (.query 1) = 0 := by
    apply control_penalty_empty_suffix
    decide
  unfold indexScore
  rw [hs,hp,hn,hz]
  simp only [BackupStat.mean]
  norm_num

theorem favorableNextS13D0I2 : indexScore (7/5) (controlPenalty savedCref uniformQuoteError unitRoleUnused .next) favorableNextS13Before [] (.query 2) = treeIndex ((0/1)/2) (7/5) (nextNormalPenalty favorableNextS13Before) 12 2 := by
  have hs : replayBackup favorableNextS13Before emptyStatistics ([]++[.query 2]) = ⟨2,(0/1)⟩ := by
    rw [replayBackup_empty_closed_form]
    simp +decide [backedEvents,favorableNextS13Before,favorableNextProposal,favorableNextEvent1,favorableNextEvent2,favorableNextEvent3,favorableNextEvent4,favorableNextEvent5,favorableNextEvent6,favorableNextEvent7,favorableNextEvent8,favorableNextEvent9,favorableNextEvent10,favorableNextEvent11,favorableNextEvent12,taskReward]
    <;> norm_num
  have hp : rawVisits favorableNextS13Before [] = 12 := by decide
  have hn : rawVisits favorableNextS13Before ([]++[.query 2]) = 2 := by decide
  have hz : (controlPenalty savedCref uniformQuoteError unitRoleUnused .next) favorableNextS13Before [] (.query 2) = (nextNormalPenalty favorableNextS13Before) := by
    simpa only [favorableNextS13Before,nextNormalPenalty] using AgentUCTNextExact.favorable_next_normal_root_quotes_exact 12 (by omega) 2 (by decide)
  unfold indexScore
  rw [hs,hp,hn,hz]
  simp only [BackupStat.mean]
  norm_num

theorem favorableNextS13D0I3 : indexScore (7/5) (controlPenalty savedCref uniformQuoteError unitRoleUnused .next) favorableNextS13Before [] (.query 3) = treeIndex ((0/1)/1) (7/5) (nextNormalPenalty favorableNextS13Before) 12 1 := by
  have hs : replayBackup favorableNextS13Before emptyStatistics ([]++[.query 3]) = ⟨1,(0/1)⟩ := by
    rw [replayBackup_empty_closed_form]
    simp +decide [backedEvents,favorableNextS13Before,favorableNextProposal,favorableNextEvent1,favorableNextEvent2,favorableNextEvent3,favorableNextEvent4,favorableNextEvent5,favorableNextEvent6,favorableNextEvent7,favorableNextEvent8,favorableNextEvent9,favorableNextEvent10,favorableNextEvent11,favorableNextEvent12,taskReward]
    <;> norm_num
  have hp : rawVisits favorableNextS13Before [] = 12 := by decide
  have hn : rawVisits favorableNextS13Before ([]++[.query 3]) = 1 := by decide
  have hz : (controlPenalty savedCref uniformQuoteError unitRoleUnused .next) favorableNextS13Before [] (.query 3) = (nextNormalPenalty favorableNextS13Before) := by
    simpa only [favorableNextS13Before,nextNormalPenalty] using AgentUCTNextExact.favorable_next_normal_root_quotes_exact 12 (by omega) 3 (by decide)
  unfold indexScore
  rw [hs,hp,hn,hz]
  simp only [BackupStat.mean]
  norm_num

theorem favorableNextS13D0I4 : indexScore (7/5) (controlPenalty savedCref uniformQuoteError unitRoleUnused .next) favorableNextS13Before [] (.query 4) = treeIndex ((0/1)/1) (7/5) (nextNormalPenalty favorableNextS13Before) 12 1 := by
  have hs : replayBackup favorableNextS13Before emptyStatistics ([]++[.query 4]) = ⟨1,(0/1)⟩ := by
    rw [replayBackup_empty_closed_form]
    simp +decide [backedEvents,favorableNextS13Before,favorableNextProposal,favorableNextEvent1,favorableNextEvent2,favorableNextEvent3,favorableNextEvent4,favorableNextEvent5,favorableNextEvent6,favorableNextEvent7,favorableNextEvent8,favorableNextEvent9,favorableNextEvent10,favorableNextEvent11,favorableNextEvent12,taskReward]
    <;> norm_num
  have hp : rawVisits favorableNextS13Before [] = 12 := by decide
  have hn : rawVisits favorableNextS13Before ([]++[.query 4]) = 1 := by decide
  have hz : (controlPenalty savedCref uniformQuoteError unitRoleUnused .next) favorableNextS13Before [] (.query 4) = (nextNormalPenalty favorableNextS13Before) := by
    simpa only [favorableNextS13Before,nextNormalPenalty] using AgentUCTNextExact.favorable_next_normal_root_quotes_exact 12 (by omega) 4 (by decide)
  unfold indexScore
  rw [hs,hp,hn,hz]
  simp only [BackupStat.mean]
  norm_num

theorem favorableNextS13D0I5 : indexScore (7/5) (controlPenalty savedCref uniformQuoteError unitRoleUnused .next) favorableNextS13Before [] (.query 5) = treeIndex ((4/5)/2) (7/5) (nextNormalPenalty favorableNextS13Before) 12 2 := by
  have hs : replayBackup favorableNextS13Before emptyStatistics ([]++[.query 5]) = ⟨2,(4/5)⟩ := by
    rw [replayBackup_empty_closed_form]
    simp +decide [backedEvents,favorableNextS13Before,favorableNextProposal,favorableNextEvent1,favorableNextEvent2,favorableNextEvent3,favorableNextEvent4,favorableNextEvent5,favorableNextEvent6,favorableNextEvent7,favorableNextEvent8,favorableNextEvent9,favorableNextEvent10,favorableNextEvent11,favorableNextEvent12,taskReward]
    <;> norm_num
  have hp : rawVisits favorableNextS13Before [] = 12 := by decide
  have hn : rawVisits favorableNextS13Before ([]++[.query 5]) = 2 := by decide
  have hz : (controlPenalty savedCref uniformQuoteError unitRoleUnused .next) favorableNextS13Before [] (.query 5) = (nextNormalPenalty favorableNextS13Before) := by
    simpa only [favorableNextS13Before,nextNormalPenalty] using AgentUCTNextExact.favorable_next_normal_root_quotes_exact 12 (by omega) 5 (by decide)
  unfold indexScore
  rw [hs,hp,hn,hz]
  simp only [BackupStat.mean]
  norm_num

theorem favorableNextS13D0I6 : indexScore (7/5) (controlPenalty savedCref uniformQuoteError unitRoleUnused .next) favorableNextS13Before [] (.query 6) = treeIndex ((0/1)/1) (7/5) (nextNormalPenalty favorableNextS13Before) 12 1 := by
  have hs : replayBackup favorableNextS13Before emptyStatistics ([]++[.query 6]) = ⟨1,(0/1)⟩ := by
    rw [replayBackup_empty_closed_form]
    simp +decide [backedEvents,favorableNextS13Before,favorableNextProposal,favorableNextEvent1,favorableNextEvent2,favorableNextEvent3,favorableNextEvent4,favorableNextEvent5,favorableNextEvent6,favorableNextEvent7,favorableNextEvent8,favorableNextEvent9,favorableNextEvent10,favorableNextEvent11,favorableNextEvent12,taskReward]
    <;> norm_num
  have hp : rawVisits favorableNextS13Before [] = 12 := by decide
  have hn : rawVisits favorableNextS13Before ([]++[.query 6]) = 1 := by decide
  have hz : (controlPenalty savedCref uniformQuoteError unitRoleUnused .next) favorableNextS13Before [] (.query 6) = (nextNormalPenalty favorableNextS13Before) := by
    simpa only [favorableNextS13Before,nextNormalPenalty] using AgentUCTNextExact.favorable_next_normal_root_quotes_exact 12 (by omega) 6 (by decide)
  unfold indexScore
  rw [hs,hp,hn,hz]
  simp only [BackupStat.mean]
  norm_num

theorem favorableNextS13D0I7 : indexScore (7/5) (controlPenalty savedCref uniformQuoteError unitRoleUnused .next) favorableNextS13Before [] (.query 7) = treeIndex ((0/1)/1) (7/5) (nextNormalPenalty favorableNextS13Before) 12 1 := by
  have hs : replayBackup favorableNextS13Before emptyStatistics ([]++[.query 7]) = ⟨1,(0/1)⟩ := by
    rw [replayBackup_empty_closed_form]
    simp +decide [backedEvents,favorableNextS13Before,favorableNextProposal,favorableNextEvent1,favorableNextEvent2,favorableNextEvent3,favorableNextEvent4,favorableNextEvent5,favorableNextEvent6,favorableNextEvent7,favorableNextEvent8,favorableNextEvent9,favorableNextEvent10,favorableNextEvent11,favorableNextEvent12,taskReward]
    <;> norm_num
  have hp : rawVisits favorableNextS13Before [] = 12 := by decide
  have hn : rawVisits favorableNextS13Before ([]++[.query 7]) = 1 := by decide
  have hz : (controlPenalty savedCref uniformQuoteError unitRoleUnused .next) favorableNextS13Before [] (.query 7) = (nextNormalPenalty favorableNextS13Before) := by
    simpa only [favorableNextS13Before,nextNormalPenalty] using AgentUCTNextExact.favorable_next_normal_root_quotes_exact 12 (by omega) 7 (by decide)
  unfold indexScore
  rw [hs,hp,hn,hz]
  simp only [BackupStat.mean]
  norm_num

theorem favorableNextS13D0Cmp0 : indexScore (7/5) (controlPenalty savedCref uniformQuoteError unitRoleUnused .next) favorableNextS13Before [] (.query 0) < indexScore (7/5) (controlPenalty savedCref uniformQuoteError unitRoleUnused .next) favorableNextS13Before [] (.query 3) := by
  rw [favorableNextS13D0I0,favorableNextS13D0I3]
  have hk := favorable_next_penalty_interval 12 (by omega)
  change nextNormalPenaltyLower ≤ nextNormalPenalty favorableNextS13Before ∧ nextNormalPenalty favorableNextS13Before ≤ nextNormalPenaltyUpper at hk
  have hm : ((0/1)/2)+(495453/312500)-(nextNormalPenalty favorableNextS13Before) < ((0/1)/1)+(112108213/50000000)-(nextNormalPenalty favorableNextS13Before) := by
    have h : (((0/1)/2)+(495453/312500) : ℝ) < ((0/1)/1)+(112108213/50000000) := by norm_num
    linarith
  have h := index_strict_order_from_intervals ((0/1)/1) ((0/1)/2) (nextNormalPenalty favorableNextS13Before) (nextNormalPenalty favorableNextS13Before) (112108213/50000000) (495453/312500)
    (treeBonus (7/5) 12 1) (treeBonus (7/5) 12 2)
    (trajectory_bonus_12_1).1 (trajectory_bonus_12_2).2 hm
  simpa only [treeIndex] using h

theorem favorableNextS13D0Cmp1 : indexScore (7/5) (controlPenalty savedCref uniformQuoteError unitRoleUnused .next) favorableNextS13Before [] (.query 1) < indexScore (7/5) (controlPenalty savedCref uniformQuoteError unitRoleUnused .next) favorableNextS13Before [] (.query 3) := by
  rw [favorableNextS13D0I1,favorableNextS13D0I3]
  have hk := favorable_next_penalty_interval 12 (by omega)
  change nextNormalPenaltyLower ≤ nextNormalPenalty favorableNextS13Before ∧ nextNormalPenalty favorableNextS13Before ≤ nextNormalPenaltyUpper at hk
  have hm : ((1/2)/2)+(495453/312500)-0 < ((0/1)/1)+(112108213/50000000)-(nextNormalPenalty favorableNextS13Before) := by
    have h : ((1/2)/2)+(495453/312500) < ((0/1)/1)+(112108213/50000000)-nextNormalPenaltyUpper := by norm_num [nextNormalPenaltyUpper,savedCref,uniformQuoteError]
    linarith [hk.2]
  have h := index_strict_order_from_intervals ((0/1)/1) ((1/2)/2) (nextNormalPenalty favorableNextS13Before) 0 (112108213/50000000) (495453/312500)
    (treeBonus (7/5) 12 1) (treeBonus (7/5) 12 2)
    (trajectory_bonus_12_1).1 (trajectory_bonus_12_2).2 hm
  simpa only [treeIndex] using h

theorem favorableNextS13D0Cmp2 : indexScore (7/5) (controlPenalty savedCref uniformQuoteError unitRoleUnused .next) favorableNextS13Before [] (.query 2) < indexScore (7/5) (controlPenalty savedCref uniformQuoteError unitRoleUnused .next) favorableNextS13Before [] (.query 3) := by
  rw [favorableNextS13D0I2,favorableNextS13D0I3]
  have hk := favorable_next_penalty_interval 12 (by omega)
  change nextNormalPenaltyLower ≤ nextNormalPenalty favorableNextS13Before ∧ nextNormalPenalty favorableNextS13Before ≤ nextNormalPenaltyUpper at hk
  have hm : ((0/1)/2)+(495453/312500)-(nextNormalPenalty favorableNextS13Before) < ((0/1)/1)+(112108213/50000000)-(nextNormalPenalty favorableNextS13Before) := by
    have h : (((0/1)/2)+(495453/312500) : ℝ) < ((0/1)/1)+(112108213/50000000) := by norm_num
    linarith
  have h := index_strict_order_from_intervals ((0/1)/1) ((0/1)/2) (nextNormalPenalty favorableNextS13Before) (nextNormalPenalty favorableNextS13Before) (112108213/50000000) (495453/312500)
    (treeBonus (7/5) 12 1) (treeBonus (7/5) 12 2)
    (trajectory_bonus_12_1).1 (trajectory_bonus_12_2).2 hm
  simpa only [treeIndex] using h

theorem favorableNextS13D0Cmp4 : indexScore (7/5) (controlPenalty savedCref uniformQuoteError unitRoleUnused .next) favorableNextS13Before [] (.query 4) ≤ indexScore (7/5) (controlPenalty savedCref uniformQuoteError unitRoleUnused .next) favorableNextS13Before [] (.query 3) := by
  rw [favorableNextS13D0I4,favorableNextS13D0I3]

theorem favorableNextS13D0Cmp5 : indexScore (7/5) (controlPenalty savedCref uniformQuoteError unitRoleUnused .next) favorableNextS13Before [] (.query 5) ≤ indexScore (7/5) (controlPenalty savedCref uniformQuoteError unitRoleUnused .next) favorableNextS13Before [] (.query 3) := by
  rw [favorableNextS13D0I5,favorableNextS13D0I3]
  have hk := favorable_next_penalty_interval 12 (by omega)
  change nextNormalPenaltyLower ≤ nextNormalPenalty favorableNextS13Before ∧ nextNormalPenalty favorableNextS13Before ≤ nextNormalPenaltyUpper at hk
  have hm : ((4/5)/2)+(495453/312500)-(nextNormalPenalty favorableNextS13Before) < ((0/1)/1)+(112108213/50000000)-(nextNormalPenalty favorableNextS13Before) := by
    have h : (((4/5)/2)+(495453/312500) : ℝ) < ((0/1)/1)+(112108213/50000000) := by norm_num
    linarith
  have h := index_weak_order_from_intervals ((0/1)/1) ((4/5)/2) (nextNormalPenalty favorableNextS13Before) (nextNormalPenalty favorableNextS13Before) (112108213/50000000) (495453/312500)
    (treeBonus (7/5) 12 1) (treeBonus (7/5) 12 2)
    (trajectory_bonus_12_1).1 (trajectory_bonus_12_2).2 hm.le
  simpa only [treeIndex] using h

theorem favorableNextS13D0Cmp6 : indexScore (7/5) (controlPenalty savedCref uniformQuoteError unitRoleUnused .next) favorableNextS13Before [] (.query 6) ≤ indexScore (7/5) (controlPenalty savedCref uniformQuoteError unitRoleUnused .next) favorableNextS13Before [] (.query 3) := by
  rw [favorableNextS13D0I6,favorableNextS13D0I3]

theorem favorableNextS13D0Cmp7 : indexScore (7/5) (controlPenalty savedCref uniformQuoteError unitRoleUnused .next) favorableNextS13Before [] (.query 7) ≤ indexScore (7/5) (controlPenalty savedCref uniformQuoteError unitRoleUnused .next) favorableNextS13Before [] (.query 3) := by
  rw [favorableNextS13D0I7,favorableNextS13D0I3]

theorem favorableNextS13Choice0 : nativeFirstChoice (indexScore (7/5) (controlPenalty savedCref uniformQuoteError unitRoleUnused .next) favorableNextS13Before []) favorableNextS13Before [] = .query 3 := by
  apply visited_choice_from_ordered_certificate _ _ [] [.query 0,.query 1,.query 2] [.query 4,.query 5,.query 6,.query 7] (.query 3) (by decide)
  · intro a ha
    have ho : orderedLegalAvailable [] = [.query 0,.query 1,.query 2,.query 3,.query 4,.query 5,.query 6,.query 7] := by decide
    rw [ho] at ha
    simp only [List.mem_cons,List.not_mem_nil,or_false] at ha
    rcases ha with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> decide
  · intro a ha
    simp only [List.mem_cons,List.not_mem_nil,or_false] at ha
    rcases ha with rfl | rfl | rfl
    · exact favorableNextS13D0Cmp0
    · exact favorableNextS13D0Cmp1
    · exact favorableNextS13D0Cmp2
  · intro a ha
    simp only [List.mem_cons,List.not_mem_nil,or_false] at ha
    rcases ha with rfl | rfl | rfl | rfl
    · exact favorableNextS13D0Cmp4
    · exact favorableNextS13D0Cmp5
    · exact favorableNextS13D0Cmp6
    · exact favorableNextS13D0Cmp7

theorem favorableNextS13ActualEvent : nativeEvent budgetTape (7/5) (controlPenalty savedCref uniformQuoteError unitRoleUnused .next)
    (taskReward false (2/5) (1/2)) favorableNextS13Before = favorableNextEvent13 := by
  have hs0 := native_select_existing_step budgetTape (7/5) (controlPenalty savedCref uniformQuoteError unitRoleUnused .next) favorableNextS13Before 8 [] (.query 3)
    (by decide) (by decide) favorableNextS13Choice0
  have hnew := native_select_new_step budgetTape (7/5) (controlPenalty savedCref uniformQuoteError unitRoleUnused .next) favorableNextS13Before 7 [.query 3]
    [.normalRetriever 4,.normalRetriever 6,.normalRetriever 7,.normalRetriever 8,.normalRetriever 5,.normalRetriever 0,.normalRetriever 1,.normalRetriever 2,.normalRetriever 3,.normalRetriever 12,.normalRetriever 14,.normalRetriever 13,.normalRetriever 21,.normalRetriever 23,.normalRetriever 22,.normalRetriever 9,.normalRetriever 11,.normalRetriever 10,.normalRetriever 15,.normalRetriever 17,.normalRetriever 16,.normalRetriever 18,.normalRetriever 20,.normalRetriever 19,.normalRetriever 24,.normalRetriever 25,.normalRetriever 26,.normalRetriever 27,.normalRetriever 28,.normalRetriever 29] (.normalRetriever 0) (by decide) (by decide) (by decide) (by decide)
  have hs : nativeSelect budgetTape (7/5) (controlPenalty savedCref uniformQuoteError unitRoleUnused .next) favorableNextS13Before 9 [] = [.query 3,.normalRetriever 0] := by
    rw [hs0]
    change nativeSelect budgetTape (7/5) (controlPenalty savedCref uniformQuoteError unitRoleUnused .next) favorableNextS13Before 8 [.query 3] = _
    rw [hnew] <;> rfl
  have hr : repairedRollout budgetTape favorableNextS13Before 9 [.query 3,.normalRetriever 0] = [.query 3,.normalRetriever 0,.selection 0,.width 0,.stop,.reranker 0,.topm 0,.context 0,.answer 0] := by decide
  simp only [nativeEvent,hs,hr]
  rfl

def favorableNextS14Before := favorableNextProposal.take 13

theorem favorableNextS14D0I0 : indexScore (7/5) (controlPenalty savedCref uniformQuoteError unitRoleUnused .next) favorableNextS14Before [] (.query 0) = treeIndex ((0/1)/2) (7/5) (nextNormalPenalty favorableNextS14Before) 13 2 := by
  have hs : replayBackup favorableNextS14Before emptyStatistics ([]++[.query 0]) = ⟨2,(0/1)⟩ := by
    rw [replayBackup_empty_closed_form]
    simp +decide [backedEvents,favorableNextS14Before,favorableNextProposal,favorableNextEvent1,favorableNextEvent2,favorableNextEvent3,favorableNextEvent4,favorableNextEvent5,favorableNextEvent6,favorableNextEvent7,favorableNextEvent8,favorableNextEvent9,favorableNextEvent10,favorableNextEvent11,favorableNextEvent12,favorableNextEvent13,taskReward]
    <;> norm_num
  have hp : rawVisits favorableNextS14Before [] = 13 := by decide
  have hn : rawVisits favorableNextS14Before ([]++[.query 0]) = 2 := by decide
  have hz : (controlPenalty savedCref uniformQuoteError unitRoleUnused .next) favorableNextS14Before [] (.query 0) = (nextNormalPenalty favorableNextS14Before) := by
    simpa only [favorableNextS14Before,nextNormalPenalty] using AgentUCTNextExact.favorable_next_normal_root_quotes_exact 13 (by omega) 0 (by decide)
  unfold indexScore
  rw [hs,hp,hn,hz]
  simp only [BackupStat.mean]
  norm_num

theorem favorableNextS14D0I1 : indexScore (7/5) (controlPenalty savedCref uniformQuoteError unitRoleUnused .next) favorableNextS14Before [] (.query 1) = treeIndex ((1/2)/2) (7/5) 0 13 2 := by
  have hs : replayBackup favorableNextS14Before emptyStatistics ([]++[.query 1]) = ⟨2,(1/2)⟩ := by
    rw [replayBackup_empty_closed_form]
    simp +decide [backedEvents,favorableNextS14Before,favorableNextProposal,favorableNextEvent1,favorableNextEvent2,favorableNextEvent3,favorableNextEvent4,favorableNextEvent5,favorableNextEvent6,favorableNextEvent7,favorableNextEvent8,favorableNextEvent9,favorableNextEvent10,favorableNextEvent11,favorableNextEvent12,favorableNextEvent13,taskReward]
    <;> norm_num
  have hp : rawVisits favorableNextS14Before [] = 13 := by decide
  have hn : rawVisits favorableNextS14Before ([]++[.query 1]) = 2 := by decide
  have hz : (controlPenalty savedCref uniformQuoteError unitRoleUnused .next) favorableNextS14Before [] (.query 1) = 0 := by
    apply control_penalty_empty_suffix
    decide
  unfold indexScore
  rw [hs,hp,hn,hz]
  simp only [BackupStat.mean]
  norm_num

theorem favorableNextS14D0I2 : indexScore (7/5) (controlPenalty savedCref uniformQuoteError unitRoleUnused .next) favorableNextS14Before [] (.query 2) = treeIndex ((0/1)/2) (7/5) (nextNormalPenalty favorableNextS14Before) 13 2 := by
  have hs : replayBackup favorableNextS14Before emptyStatistics ([]++[.query 2]) = ⟨2,(0/1)⟩ := by
    rw [replayBackup_empty_closed_form]
    simp +decide [backedEvents,favorableNextS14Before,favorableNextProposal,favorableNextEvent1,favorableNextEvent2,favorableNextEvent3,favorableNextEvent4,favorableNextEvent5,favorableNextEvent6,favorableNextEvent7,favorableNextEvent8,favorableNextEvent9,favorableNextEvent10,favorableNextEvent11,favorableNextEvent12,favorableNextEvent13,taskReward]
    <;> norm_num
  have hp : rawVisits favorableNextS14Before [] = 13 := by decide
  have hn : rawVisits favorableNextS14Before ([]++[.query 2]) = 2 := by decide
  have hz : (controlPenalty savedCref uniformQuoteError unitRoleUnused .next) favorableNextS14Before [] (.query 2) = (nextNormalPenalty favorableNextS14Before) := by
    simpa only [favorableNextS14Before,nextNormalPenalty] using AgentUCTNextExact.favorable_next_normal_root_quotes_exact 13 (by omega) 2 (by decide)
  unfold indexScore
  rw [hs,hp,hn,hz]
  simp only [BackupStat.mean]
  norm_num

theorem favorableNextS14D0I3 : indexScore (7/5) (controlPenalty savedCref uniformQuoteError unitRoleUnused .next) favorableNextS14Before [] (.query 3) = treeIndex ((0/1)/2) (7/5) (nextNormalPenalty favorableNextS14Before) 13 2 := by
  have hs : replayBackup favorableNextS14Before emptyStatistics ([]++[.query 3]) = ⟨2,(0/1)⟩ := by
    rw [replayBackup_empty_closed_form]
    simp +decide [backedEvents,favorableNextS14Before,favorableNextProposal,favorableNextEvent1,favorableNextEvent2,favorableNextEvent3,favorableNextEvent4,favorableNextEvent5,favorableNextEvent6,favorableNextEvent7,favorableNextEvent8,favorableNextEvent9,favorableNextEvent10,favorableNextEvent11,favorableNextEvent12,favorableNextEvent13,taskReward]
    <;> norm_num
  have hp : rawVisits favorableNextS14Before [] = 13 := by decide
  have hn : rawVisits favorableNextS14Before ([]++[.query 3]) = 2 := by decide
  have hz : (controlPenalty savedCref uniformQuoteError unitRoleUnused .next) favorableNextS14Before [] (.query 3) = (nextNormalPenalty favorableNextS14Before) := by
    simpa only [favorableNextS14Before,nextNormalPenalty] using AgentUCTNextExact.favorable_next_normal_root_quotes_exact 13 (by omega) 3 (by decide)
  unfold indexScore
  rw [hs,hp,hn,hz]
  simp only [BackupStat.mean]
  norm_num

theorem favorableNextS14D0I4 : indexScore (7/5) (controlPenalty savedCref uniformQuoteError unitRoleUnused .next) favorableNextS14Before [] (.query 4) = treeIndex ((0/1)/1) (7/5) (nextNormalPenalty favorableNextS14Before) 13 1 := by
  have hs : replayBackup favorableNextS14Before emptyStatistics ([]++[.query 4]) = ⟨1,(0/1)⟩ := by
    rw [replayBackup_empty_closed_form]
    simp +decide [backedEvents,favorableNextS14Before,favorableNextProposal,favorableNextEvent1,favorableNextEvent2,favorableNextEvent3,favorableNextEvent4,favorableNextEvent5,favorableNextEvent6,favorableNextEvent7,favorableNextEvent8,favorableNextEvent9,favorableNextEvent10,favorableNextEvent11,favorableNextEvent12,favorableNextEvent13,taskReward]
    <;> norm_num
  have hp : rawVisits favorableNextS14Before [] = 13 := by decide
  have hn : rawVisits favorableNextS14Before ([]++[.query 4]) = 1 := by decide
  have hz : (controlPenalty savedCref uniformQuoteError unitRoleUnused .next) favorableNextS14Before [] (.query 4) = (nextNormalPenalty favorableNextS14Before) := by
    simpa only [favorableNextS14Before,nextNormalPenalty] using AgentUCTNextExact.favorable_next_normal_root_quotes_exact 13 (by omega) 4 (by decide)
  unfold indexScore
  rw [hs,hp,hn,hz]
  simp only [BackupStat.mean]
  norm_num

theorem favorableNextS14D0I5 : indexScore (7/5) (controlPenalty savedCref uniformQuoteError unitRoleUnused .next) favorableNextS14Before [] (.query 5) = treeIndex ((4/5)/2) (7/5) (nextNormalPenalty favorableNextS14Before) 13 2 := by
  have hs : replayBackup favorableNextS14Before emptyStatistics ([]++[.query 5]) = ⟨2,(4/5)⟩ := by
    rw [replayBackup_empty_closed_form]
    simp +decide [backedEvents,favorableNextS14Before,favorableNextProposal,favorableNextEvent1,favorableNextEvent2,favorableNextEvent3,favorableNextEvent4,favorableNextEvent5,favorableNextEvent6,favorableNextEvent7,favorableNextEvent8,favorableNextEvent9,favorableNextEvent10,favorableNextEvent11,favorableNextEvent12,favorableNextEvent13,taskReward]
    <;> norm_num
  have hp : rawVisits favorableNextS14Before [] = 13 := by decide
  have hn : rawVisits favorableNextS14Before ([]++[.query 5]) = 2 := by decide
  have hz : (controlPenalty savedCref uniformQuoteError unitRoleUnused .next) favorableNextS14Before [] (.query 5) = (nextNormalPenalty favorableNextS14Before) := by
    simpa only [favorableNextS14Before,nextNormalPenalty] using AgentUCTNextExact.favorable_next_normal_root_quotes_exact 13 (by omega) 5 (by decide)
  unfold indexScore
  rw [hs,hp,hn,hz]
  simp only [BackupStat.mean]
  norm_num

theorem favorableNextS14D0I6 : indexScore (7/5) (controlPenalty savedCref uniformQuoteError unitRoleUnused .next) favorableNextS14Before [] (.query 6) = treeIndex ((0/1)/1) (7/5) (nextNormalPenalty favorableNextS14Before) 13 1 := by
  have hs : replayBackup favorableNextS14Before emptyStatistics ([]++[.query 6]) = ⟨1,(0/1)⟩ := by
    rw [replayBackup_empty_closed_form]
    simp +decide [backedEvents,favorableNextS14Before,favorableNextProposal,favorableNextEvent1,favorableNextEvent2,favorableNextEvent3,favorableNextEvent4,favorableNextEvent5,favorableNextEvent6,favorableNextEvent7,favorableNextEvent8,favorableNextEvent9,favorableNextEvent10,favorableNextEvent11,favorableNextEvent12,favorableNextEvent13,taskReward]
    <;> norm_num
  have hp : rawVisits favorableNextS14Before [] = 13 := by decide
  have hn : rawVisits favorableNextS14Before ([]++[.query 6]) = 1 := by decide
  have hz : (controlPenalty savedCref uniformQuoteError unitRoleUnused .next) favorableNextS14Before [] (.query 6) = (nextNormalPenalty favorableNextS14Before) := by
    simpa only [favorableNextS14Before,nextNormalPenalty] using AgentUCTNextExact.favorable_next_normal_root_quotes_exact 13 (by omega) 6 (by decide)
  unfold indexScore
  rw [hs,hp,hn,hz]
  simp only [BackupStat.mean]
  norm_num

theorem favorableNextS14D0I7 : indexScore (7/5) (controlPenalty savedCref uniformQuoteError unitRoleUnused .next) favorableNextS14Before [] (.query 7) = treeIndex ((0/1)/1) (7/5) (nextNormalPenalty favorableNextS14Before) 13 1 := by
  have hs : replayBackup favorableNextS14Before emptyStatistics ([]++[.query 7]) = ⟨1,(0/1)⟩ := by
    rw [replayBackup_empty_closed_form]
    simp +decide [backedEvents,favorableNextS14Before,favorableNextProposal,favorableNextEvent1,favorableNextEvent2,favorableNextEvent3,favorableNextEvent4,favorableNextEvent5,favorableNextEvent6,favorableNextEvent7,favorableNextEvent8,favorableNextEvent9,favorableNextEvent10,favorableNextEvent11,favorableNextEvent12,favorableNextEvent13,taskReward]
    <;> norm_num
  have hp : rawVisits favorableNextS14Before [] = 13 := by decide
  have hn : rawVisits favorableNextS14Before ([]++[.query 7]) = 1 := by decide
  have hz : (controlPenalty savedCref uniformQuoteError unitRoleUnused .next) favorableNextS14Before [] (.query 7) = (nextNormalPenalty favorableNextS14Before) := by
    simpa only [favorableNextS14Before,nextNormalPenalty] using AgentUCTNextExact.favorable_next_normal_root_quotes_exact 13 (by omega) 7 (by decide)
  unfold indexScore
  rw [hs,hp,hn,hz]
  simp only [BackupStat.mean]
  norm_num

theorem favorableNextS14D0Cmp0 : indexScore (7/5) (controlPenalty savedCref uniformQuoteError unitRoleUnused .next) favorableNextS14Before [] (.query 0) < indexScore (7/5) (controlPenalty savedCref uniformQuoteError unitRoleUnused .next) favorableNextS14Before [] (.query 4) := by
  rw [favorableNextS14D0I0,favorableNextS14D0I4]
  have hk := favorable_next_penalty_interval 13 (by omega)
  change nextNormalPenaltyLower ≤ nextNormalPenalty favorableNextS14Before ∧ nextNormalPenalty favorableNextS14Before ≤ nextNormalPenaltyUpper at hk
  have hm : ((0/1)/2)+(3216381/2000000)-(nextNormalPenalty favorableNextS14Before) < ((0/1)/1)+(4548649/2000000)-(nextNormalPenalty favorableNextS14Before) := by
    have h : (((0/1)/2)+(3216381/2000000) : ℝ) < ((0/1)/1)+(4548649/2000000) := by norm_num
    linarith
  have h := index_strict_order_from_intervals ((0/1)/1) ((0/1)/2) (nextNormalPenalty favorableNextS14Before) (nextNormalPenalty favorableNextS14Before) (4548649/2000000) (3216381/2000000)
    (treeBonus (7/5) 13 1) (treeBonus (7/5) 13 2)
    (trajectory_bonus_13_1).1 (trajectory_bonus_13_2).2 hm
  simpa only [treeIndex] using h

theorem favorableNextS14D0Cmp1 : indexScore (7/5) (controlPenalty savedCref uniformQuoteError unitRoleUnused .next) favorableNextS14Before [] (.query 1) < indexScore (7/5) (controlPenalty savedCref uniformQuoteError unitRoleUnused .next) favorableNextS14Before [] (.query 4) := by
  rw [favorableNextS14D0I1,favorableNextS14D0I4]
  have hk := favorable_next_penalty_interval 13 (by omega)
  change nextNormalPenaltyLower ≤ nextNormalPenalty favorableNextS14Before ∧ nextNormalPenalty favorableNextS14Before ≤ nextNormalPenaltyUpper at hk
  have hm : ((1/2)/2)+(3216381/2000000)-0 < ((0/1)/1)+(4548649/2000000)-(nextNormalPenalty favorableNextS14Before) := by
    have h : ((1/2)/2)+(3216381/2000000) < ((0/1)/1)+(4548649/2000000)-nextNormalPenaltyUpper := by norm_num [nextNormalPenaltyUpper,savedCref,uniformQuoteError]
    linarith [hk.2]
  have h := index_strict_order_from_intervals ((0/1)/1) ((1/2)/2) (nextNormalPenalty favorableNextS14Before) 0 (4548649/2000000) (3216381/2000000)
    (treeBonus (7/5) 13 1) (treeBonus (7/5) 13 2)
    (trajectory_bonus_13_1).1 (trajectory_bonus_13_2).2 hm
  simpa only [treeIndex] using h

theorem favorableNextS14D0Cmp2 : indexScore (7/5) (controlPenalty savedCref uniformQuoteError unitRoleUnused .next) favorableNextS14Before [] (.query 2) < indexScore (7/5) (controlPenalty savedCref uniformQuoteError unitRoleUnused .next) favorableNextS14Before [] (.query 4) := by
  rw [favorableNextS14D0I2,favorableNextS14D0I4]
  have hk := favorable_next_penalty_interval 13 (by omega)
  change nextNormalPenaltyLower ≤ nextNormalPenalty favorableNextS14Before ∧ nextNormalPenalty favorableNextS14Before ≤ nextNormalPenaltyUpper at hk
  have hm : ((0/1)/2)+(3216381/2000000)-(nextNormalPenalty favorableNextS14Before) < ((0/1)/1)+(4548649/2000000)-(nextNormalPenalty favorableNextS14Before) := by
    have h : (((0/1)/2)+(3216381/2000000) : ℝ) < ((0/1)/1)+(4548649/2000000) := by norm_num
    linarith
  have h := index_strict_order_from_intervals ((0/1)/1) ((0/1)/2) (nextNormalPenalty favorableNextS14Before) (nextNormalPenalty favorableNextS14Before) (4548649/2000000) (3216381/2000000)
    (treeBonus (7/5) 13 1) (treeBonus (7/5) 13 2)
    (trajectory_bonus_13_1).1 (trajectory_bonus_13_2).2 hm
  simpa only [treeIndex] using h

theorem favorableNextS14D0Cmp3 : indexScore (7/5) (controlPenalty savedCref uniformQuoteError unitRoleUnused .next) favorableNextS14Before [] (.query 3) < indexScore (7/5) (controlPenalty savedCref uniformQuoteError unitRoleUnused .next) favorableNextS14Before [] (.query 4) := by
  rw [favorableNextS14D0I3,favorableNextS14D0I4]
  have hk := favorable_next_penalty_interval 13 (by omega)
  change nextNormalPenaltyLower ≤ nextNormalPenalty favorableNextS14Before ∧ nextNormalPenalty favorableNextS14Before ≤ nextNormalPenaltyUpper at hk
  have hm : ((0/1)/2)+(3216381/2000000)-(nextNormalPenalty favorableNextS14Before) < ((0/1)/1)+(4548649/2000000)-(nextNormalPenalty favorableNextS14Before) := by
    have h : (((0/1)/2)+(3216381/2000000) : ℝ) < ((0/1)/1)+(4548649/2000000) := by norm_num
    linarith
  have h := index_strict_order_from_intervals ((0/1)/1) ((0/1)/2) (nextNormalPenalty favorableNextS14Before) (nextNormalPenalty favorableNextS14Before) (4548649/2000000) (3216381/2000000)
    (treeBonus (7/5) 13 1) (treeBonus (7/5) 13 2)
    (trajectory_bonus_13_1).1 (trajectory_bonus_13_2).2 hm
  simpa only [treeIndex] using h

theorem favorableNextS14D0Cmp5 : indexScore (7/5) (controlPenalty savedCref uniformQuoteError unitRoleUnused .next) favorableNextS14Before [] (.query 5) ≤ indexScore (7/5) (controlPenalty savedCref uniformQuoteError unitRoleUnused .next) favorableNextS14Before [] (.query 4) := by
  rw [favorableNextS14D0I5,favorableNextS14D0I4]
  have hk := favorable_next_penalty_interval 13 (by omega)
  change nextNormalPenaltyLower ≤ nextNormalPenalty favorableNextS14Before ∧ nextNormalPenalty favorableNextS14Before ≤ nextNormalPenaltyUpper at hk
  have hm : ((4/5)/2)+(3216381/2000000)-(nextNormalPenalty favorableNextS14Before) < ((0/1)/1)+(4548649/2000000)-(nextNormalPenalty favorableNextS14Before) := by
    have h : (((4/5)/2)+(3216381/2000000) : ℝ) < ((0/1)/1)+(4548649/2000000) := by norm_num
    linarith
  have h := index_weak_order_from_intervals ((0/1)/1) ((4/5)/2) (nextNormalPenalty favorableNextS14Before) (nextNormalPenalty favorableNextS14Before) (4548649/2000000) (3216381/2000000)
    (treeBonus (7/5) 13 1) (treeBonus (7/5) 13 2)
    (trajectory_bonus_13_1).1 (trajectory_bonus_13_2).2 hm.le
  simpa only [treeIndex] using h

theorem favorableNextS14D0Cmp6 : indexScore (7/5) (controlPenalty savedCref uniformQuoteError unitRoleUnused .next) favorableNextS14Before [] (.query 6) ≤ indexScore (7/5) (controlPenalty savedCref uniformQuoteError unitRoleUnused .next) favorableNextS14Before [] (.query 4) := by
  rw [favorableNextS14D0I6,favorableNextS14D0I4]

theorem favorableNextS14D0Cmp7 : indexScore (7/5) (controlPenalty savedCref uniformQuoteError unitRoleUnused .next) favorableNextS14Before [] (.query 7) ≤ indexScore (7/5) (controlPenalty savedCref uniformQuoteError unitRoleUnused .next) favorableNextS14Before [] (.query 4) := by
  rw [favorableNextS14D0I7,favorableNextS14D0I4]

theorem favorableNextS14Choice0 : nativeFirstChoice (indexScore (7/5) (controlPenalty savedCref uniformQuoteError unitRoleUnused .next) favorableNextS14Before []) favorableNextS14Before [] = .query 4 := by
  apply visited_choice_from_ordered_certificate _ _ [] [.query 0,.query 1,.query 2,.query 3] [.query 5,.query 6,.query 7] (.query 4) (by decide)
  · intro a ha
    have ho : orderedLegalAvailable [] = [.query 0,.query 1,.query 2,.query 3,.query 4,.query 5,.query 6,.query 7] := by decide
    rw [ho] at ha
    simp only [List.mem_cons,List.not_mem_nil,or_false] at ha
    rcases ha with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> decide
  · intro a ha
    simp only [List.mem_cons,List.not_mem_nil,or_false] at ha
    rcases ha with rfl | rfl | rfl | rfl
    · exact favorableNextS14D0Cmp0
    · exact favorableNextS14D0Cmp1
    · exact favorableNextS14D0Cmp2
    · exact favorableNextS14D0Cmp3
  · intro a ha
    simp only [List.mem_cons,List.not_mem_nil,or_false] at ha
    rcases ha with rfl | rfl | rfl
    · exact favorableNextS14D0Cmp5
    · exact favorableNextS14D0Cmp6
    · exact favorableNextS14D0Cmp7

theorem favorableNextS14ActualEvent : nativeEvent budgetTape (7/5) (controlPenalty savedCref uniformQuoteError unitRoleUnused .next)
    (taskReward false (2/5) (1/2)) favorableNextS14Before = favorableNextEvent14 := by
  have hs0 := native_select_existing_step budgetTape (7/5) (controlPenalty savedCref uniformQuoteError unitRoleUnused .next) favorableNextS14Before 8 [] (.query 4)
    (by decide) (by decide) favorableNextS14Choice0
  have hnew := native_select_new_step budgetTape (7/5) (controlPenalty savedCref uniformQuoteError unitRoleUnused .next) favorableNextS14Before 7 [.query 4]
    [.normalRetriever 4,.normalRetriever 6,.normalRetriever 7,.normalRetriever 8,.normalRetriever 5,.normalRetriever 0,.normalRetriever 1,.normalRetriever 2,.normalRetriever 3,.normalRetriever 12,.normalRetriever 14,.normalRetriever 13,.normalRetriever 21,.normalRetriever 23,.normalRetriever 22,.normalRetriever 9,.normalRetriever 11,.normalRetriever 10,.normalRetriever 15,.normalRetriever 17,.normalRetriever 16,.normalRetriever 18,.normalRetriever 20,.normalRetriever 19,.normalRetriever 24,.normalRetriever 25,.normalRetriever 26,.normalRetriever 27,.normalRetriever 28,.normalRetriever 29] (.normalRetriever 0) (by decide) (by decide) (by decide) (by decide)
  have hs : nativeSelect budgetTape (7/5) (controlPenalty savedCref uniformQuoteError unitRoleUnused .next) favorableNextS14Before 9 [] = [.query 4,.normalRetriever 0] := by
    rw [hs0]
    change nativeSelect budgetTape (7/5) (controlPenalty savedCref uniformQuoteError unitRoleUnused .next) favorableNextS14Before 8 [.query 4] = _
    rw [hnew] <;> rfl
  have hr : repairedRollout budgetTape favorableNextS14Before 9 [.query 4,.normalRetriever 0] = [.query 4,.normalRetriever 0,.selection 0,.width 0,.stop,.reranker 0,.topm 0,.context 0,.answer 0] := by decide
  simp only [nativeEvent,hs,hr]
  rfl

def favorableNextS15Before := favorableNextProposal.take 14

theorem favorableNextS15D0I0 : indexScore (7/5) (controlPenalty savedCref uniformQuoteError unitRoleUnused .next) favorableNextS15Before [] (.query 0) = treeIndex ((0/1)/2) (7/5) (nextNormalPenalty favorableNextS15Before) 14 2 := by
  have hs : replayBackup favorableNextS15Before emptyStatistics ([]++[.query 0]) = ⟨2,(0/1)⟩ := by
    rw [replayBackup_empty_closed_form]
    simp +decide [backedEvents,favorableNextS15Before,favorableNextProposal,favorableNextEvent1,favorableNextEvent2,favorableNextEvent3,favorableNextEvent4,favorableNextEvent5,favorableNextEvent6,favorableNextEvent7,favorableNextEvent8,favorableNextEvent9,favorableNextEvent10,favorableNextEvent11,favorableNextEvent12,favorableNextEvent13,favorableNextEvent14,taskReward]
    <;> norm_num
  have hp : rawVisits favorableNextS15Before [] = 14 := by decide
  have hn : rawVisits favorableNextS15Before ([]++[.query 0]) = 2 := by decide
  have hz : (controlPenalty savedCref uniformQuoteError unitRoleUnused .next) favorableNextS15Before [] (.query 0) = (nextNormalPenalty favorableNextS15Before) := by
    simpa only [favorableNextS15Before,nextNormalPenalty] using AgentUCTNextExact.favorable_next_normal_root_quotes_exact 14 (by omega) 0 (by decide)
  unfold indexScore
  rw [hs,hp,hn,hz]
  simp only [BackupStat.mean]
  norm_num

theorem favorableNextS15D0I1 : indexScore (7/5) (controlPenalty savedCref uniformQuoteError unitRoleUnused .next) favorableNextS15Before [] (.query 1) = treeIndex ((1/2)/2) (7/5) 0 14 2 := by
  have hs : replayBackup favorableNextS15Before emptyStatistics ([]++[.query 1]) = ⟨2,(1/2)⟩ := by
    rw [replayBackup_empty_closed_form]
    simp +decide [backedEvents,favorableNextS15Before,favorableNextProposal,favorableNextEvent1,favorableNextEvent2,favorableNextEvent3,favorableNextEvent4,favorableNextEvent5,favorableNextEvent6,favorableNextEvent7,favorableNextEvent8,favorableNextEvent9,favorableNextEvent10,favorableNextEvent11,favorableNextEvent12,favorableNextEvent13,favorableNextEvent14,taskReward]
    <;> norm_num
  have hp : rawVisits favorableNextS15Before [] = 14 := by decide
  have hn : rawVisits favorableNextS15Before ([]++[.query 1]) = 2 := by decide
  have hz : (controlPenalty savedCref uniformQuoteError unitRoleUnused .next) favorableNextS15Before [] (.query 1) = 0 := by
    apply control_penalty_empty_suffix
    decide
  unfold indexScore
  rw [hs,hp,hn,hz]
  simp only [BackupStat.mean]
  norm_num

theorem favorableNextS15D0I2 : indexScore (7/5) (controlPenalty savedCref uniformQuoteError unitRoleUnused .next) favorableNextS15Before [] (.query 2) = treeIndex ((0/1)/2) (7/5) (nextNormalPenalty favorableNextS15Before) 14 2 := by
  have hs : replayBackup favorableNextS15Before emptyStatistics ([]++[.query 2]) = ⟨2,(0/1)⟩ := by
    rw [replayBackup_empty_closed_form]
    simp +decide [backedEvents,favorableNextS15Before,favorableNextProposal,favorableNextEvent1,favorableNextEvent2,favorableNextEvent3,favorableNextEvent4,favorableNextEvent5,favorableNextEvent6,favorableNextEvent7,favorableNextEvent8,favorableNextEvent9,favorableNextEvent10,favorableNextEvent11,favorableNextEvent12,favorableNextEvent13,favorableNextEvent14,taskReward]
    <;> norm_num
  have hp : rawVisits favorableNextS15Before [] = 14 := by decide
  have hn : rawVisits favorableNextS15Before ([]++[.query 2]) = 2 := by decide
  have hz : (controlPenalty savedCref uniformQuoteError unitRoleUnused .next) favorableNextS15Before [] (.query 2) = (nextNormalPenalty favorableNextS15Before) := by
    simpa only [favorableNextS15Before,nextNormalPenalty] using AgentUCTNextExact.favorable_next_normal_root_quotes_exact 14 (by omega) 2 (by decide)
  unfold indexScore
  rw [hs,hp,hn,hz]
  simp only [BackupStat.mean]
  norm_num

theorem favorableNextS15D0I3 : indexScore (7/5) (controlPenalty savedCref uniformQuoteError unitRoleUnused .next) favorableNextS15Before [] (.query 3) = treeIndex ((0/1)/2) (7/5) (nextNormalPenalty favorableNextS15Before) 14 2 := by
  have hs : replayBackup favorableNextS15Before emptyStatistics ([]++[.query 3]) = ⟨2,(0/1)⟩ := by
    rw [replayBackup_empty_closed_form]
    simp +decide [backedEvents,favorableNextS15Before,favorableNextProposal,favorableNextEvent1,favorableNextEvent2,favorableNextEvent3,favorableNextEvent4,favorableNextEvent5,favorableNextEvent6,favorableNextEvent7,favorableNextEvent8,favorableNextEvent9,favorableNextEvent10,favorableNextEvent11,favorableNextEvent12,favorableNextEvent13,favorableNextEvent14,taskReward]
    <;> norm_num
  have hp : rawVisits favorableNextS15Before [] = 14 := by decide
  have hn : rawVisits favorableNextS15Before ([]++[.query 3]) = 2 := by decide
  have hz : (controlPenalty savedCref uniformQuoteError unitRoleUnused .next) favorableNextS15Before [] (.query 3) = (nextNormalPenalty favorableNextS15Before) := by
    simpa only [favorableNextS15Before,nextNormalPenalty] using AgentUCTNextExact.favorable_next_normal_root_quotes_exact 14 (by omega) 3 (by decide)
  unfold indexScore
  rw [hs,hp,hn,hz]
  simp only [BackupStat.mean]
  norm_num

theorem favorableNextS15D0I4 : indexScore (7/5) (controlPenalty savedCref uniformQuoteError unitRoleUnused .next) favorableNextS15Before [] (.query 4) = treeIndex ((0/1)/2) (7/5) (nextNormalPenalty favorableNextS15Before) 14 2 := by
  have hs : replayBackup favorableNextS15Before emptyStatistics ([]++[.query 4]) = ⟨2,(0/1)⟩ := by
    rw [replayBackup_empty_closed_form]
    simp +decide [backedEvents,favorableNextS15Before,favorableNextProposal,favorableNextEvent1,favorableNextEvent2,favorableNextEvent3,favorableNextEvent4,favorableNextEvent5,favorableNextEvent6,favorableNextEvent7,favorableNextEvent8,favorableNextEvent9,favorableNextEvent10,favorableNextEvent11,favorableNextEvent12,favorableNextEvent13,favorableNextEvent14,taskReward]
    <;> norm_num
  have hp : rawVisits favorableNextS15Before [] = 14 := by decide
  have hn : rawVisits favorableNextS15Before ([]++[.query 4]) = 2 := by decide
  have hz : (controlPenalty savedCref uniformQuoteError unitRoleUnused .next) favorableNextS15Before [] (.query 4) = (nextNormalPenalty favorableNextS15Before) := by
    simpa only [favorableNextS15Before,nextNormalPenalty] using AgentUCTNextExact.favorable_next_normal_root_quotes_exact 14 (by omega) 4 (by decide)
  unfold indexScore
  rw [hs,hp,hn,hz]
  simp only [BackupStat.mean]
  norm_num

theorem favorableNextS15D0I5 : indexScore (7/5) (controlPenalty savedCref uniformQuoteError unitRoleUnused .next) favorableNextS15Before [] (.query 5) = treeIndex ((4/5)/2) (7/5) (nextNormalPenalty favorableNextS15Before) 14 2 := by
  have hs : replayBackup favorableNextS15Before emptyStatistics ([]++[.query 5]) = ⟨2,(4/5)⟩ := by
    rw [replayBackup_empty_closed_form]
    simp +decide [backedEvents,favorableNextS15Before,favorableNextProposal,favorableNextEvent1,favorableNextEvent2,favorableNextEvent3,favorableNextEvent4,favorableNextEvent5,favorableNextEvent6,favorableNextEvent7,favorableNextEvent8,favorableNextEvent9,favorableNextEvent10,favorableNextEvent11,favorableNextEvent12,favorableNextEvent13,favorableNextEvent14,taskReward]
    <;> norm_num
  have hp : rawVisits favorableNextS15Before [] = 14 := by decide
  have hn : rawVisits favorableNextS15Before ([]++[.query 5]) = 2 := by decide
  have hz : (controlPenalty savedCref uniformQuoteError unitRoleUnused .next) favorableNextS15Before [] (.query 5) = (nextNormalPenalty favorableNextS15Before) := by
    simpa only [favorableNextS15Before,nextNormalPenalty] using AgentUCTNextExact.favorable_next_normal_root_quotes_exact 14 (by omega) 5 (by decide)
  unfold indexScore
  rw [hs,hp,hn,hz]
  simp only [BackupStat.mean]
  norm_num

theorem favorableNextS15D0I6 : indexScore (7/5) (controlPenalty savedCref uniformQuoteError unitRoleUnused .next) favorableNextS15Before [] (.query 6) = treeIndex ((0/1)/1) (7/5) (nextNormalPenalty favorableNextS15Before) 14 1 := by
  have hs : replayBackup favorableNextS15Before emptyStatistics ([]++[.query 6]) = ⟨1,(0/1)⟩ := by
    rw [replayBackup_empty_closed_form]
    simp +decide [backedEvents,favorableNextS15Before,favorableNextProposal,favorableNextEvent1,favorableNextEvent2,favorableNextEvent3,favorableNextEvent4,favorableNextEvent5,favorableNextEvent6,favorableNextEvent7,favorableNextEvent8,favorableNextEvent9,favorableNextEvent10,favorableNextEvent11,favorableNextEvent12,favorableNextEvent13,favorableNextEvent14,taskReward]
    <;> norm_num
  have hp : rawVisits favorableNextS15Before [] = 14 := by decide
  have hn : rawVisits favorableNextS15Before ([]++[.query 6]) = 1 := by decide
  have hz : (controlPenalty savedCref uniformQuoteError unitRoleUnused .next) favorableNextS15Before [] (.query 6) = (nextNormalPenalty favorableNextS15Before) := by
    simpa only [favorableNextS15Before,nextNormalPenalty] using AgentUCTNextExact.favorable_next_normal_root_quotes_exact 14 (by omega) 6 (by decide)
  unfold indexScore
  rw [hs,hp,hn,hz]
  simp only [BackupStat.mean]
  norm_num

theorem favorableNextS15D0I7 : indexScore (7/5) (controlPenalty savedCref uniformQuoteError unitRoleUnused .next) favorableNextS15Before [] (.query 7) = treeIndex ((0/1)/1) (7/5) (nextNormalPenalty favorableNextS15Before) 14 1 := by
  have hs : replayBackup favorableNextS15Before emptyStatistics ([]++[.query 7]) = ⟨1,(0/1)⟩ := by
    rw [replayBackup_empty_closed_form]
    simp +decide [backedEvents,favorableNextS15Before,favorableNextProposal,favorableNextEvent1,favorableNextEvent2,favorableNextEvent3,favorableNextEvent4,favorableNextEvent5,favorableNextEvent6,favorableNextEvent7,favorableNextEvent8,favorableNextEvent9,favorableNextEvent10,favorableNextEvent11,favorableNextEvent12,favorableNextEvent13,favorableNextEvent14,taskReward]
    <;> norm_num
  have hp : rawVisits favorableNextS15Before [] = 14 := by decide
  have hn : rawVisits favorableNextS15Before ([]++[.query 7]) = 1 := by decide
  have hz : (controlPenalty savedCref uniformQuoteError unitRoleUnused .next) favorableNextS15Before [] (.query 7) = (nextNormalPenalty favorableNextS15Before) := by
    simpa only [favorableNextS15Before,nextNormalPenalty] using AgentUCTNextExact.favorable_next_normal_root_quotes_exact 14 (by omega) 7 (by decide)
  unfold indexScore
  rw [hs,hp,hn,hz]
  simp only [BackupStat.mean]
  norm_num

theorem favorableNextS15D0Cmp0 : indexScore (7/5) (controlPenalty savedCref uniformQuoteError unitRoleUnused .next) favorableNextS15Before [] (.query 0) < indexScore (7/5) (controlPenalty savedCref uniformQuoteError unitRoleUnused .next) favorableNextS15Before [] (.query 6) := by
  rw [favorableNextS15D0I0,favorableNextS15D0I6]
  have hk := favorable_next_penalty_interval 14 (by omega)
  change nextNormalPenaltyLower ≤ nextNormalPenalty favorableNextS15Before ∧ nextNormalPenalty favorableNextS15Before ≤ nextNormalPenaltyUpper at hk
  have hm : ((0/1)/2)+(81453813/50000000)-(nextNormalPenalty favorableNextS15Before) < ((0/1)/1)+(57596539/25000000)-(nextNormalPenalty favorableNextS15Before) := by
    have h : (((0/1)/2)+(81453813/50000000) : ℝ) < ((0/1)/1)+(57596539/25000000) := by norm_num
    linarith
  have h := index_strict_order_from_intervals ((0/1)/1) ((0/1)/2) (nextNormalPenalty favorableNextS15Before) (nextNormalPenalty favorableNextS15Before) (57596539/25000000) (81453813/50000000)
    (treeBonus (7/5) 14 1) (treeBonus (7/5) 14 2)
    (trajectory_bonus_14_1).1 (trajectory_bonus_14_2).2 hm
  simpa only [treeIndex] using h

theorem favorableNextS15D0Cmp1 : indexScore (7/5) (controlPenalty savedCref uniformQuoteError unitRoleUnused .next) favorableNextS15Before [] (.query 1) < indexScore (7/5) (controlPenalty savedCref uniformQuoteError unitRoleUnused .next) favorableNextS15Before [] (.query 6) := by
  rw [favorableNextS15D0I1,favorableNextS15D0I6]
  have hk := favorable_next_penalty_interval 14 (by omega)
  change nextNormalPenaltyLower ≤ nextNormalPenalty favorableNextS15Before ∧ nextNormalPenalty favorableNextS15Before ≤ nextNormalPenaltyUpper at hk
  have hm : ((1/2)/2)+(81453813/50000000)-0 < ((0/1)/1)+(57596539/25000000)-(nextNormalPenalty favorableNextS15Before) := by
    have h : ((1/2)/2)+(81453813/50000000) < ((0/1)/1)+(57596539/25000000)-nextNormalPenaltyUpper := by norm_num [nextNormalPenaltyUpper,savedCref,uniformQuoteError]
    linarith [hk.2]
  have h := index_strict_order_from_intervals ((0/1)/1) ((1/2)/2) (nextNormalPenalty favorableNextS15Before) 0 (57596539/25000000) (81453813/50000000)
    (treeBonus (7/5) 14 1) (treeBonus (7/5) 14 2)
    (trajectory_bonus_14_1).1 (trajectory_bonus_14_2).2 hm
  simpa only [treeIndex] using h

theorem favorableNextS15D0Cmp2 : indexScore (7/5) (controlPenalty savedCref uniformQuoteError unitRoleUnused .next) favorableNextS15Before [] (.query 2) < indexScore (7/5) (controlPenalty savedCref uniformQuoteError unitRoleUnused .next) favorableNextS15Before [] (.query 6) := by
  rw [favorableNextS15D0I2,favorableNextS15D0I6]
  have hk := favorable_next_penalty_interval 14 (by omega)
  change nextNormalPenaltyLower ≤ nextNormalPenalty favorableNextS15Before ∧ nextNormalPenalty favorableNextS15Before ≤ nextNormalPenaltyUpper at hk
  have hm : ((0/1)/2)+(81453813/50000000)-(nextNormalPenalty favorableNextS15Before) < ((0/1)/1)+(57596539/25000000)-(nextNormalPenalty favorableNextS15Before) := by
    have h : (((0/1)/2)+(81453813/50000000) : ℝ) < ((0/1)/1)+(57596539/25000000) := by norm_num
    linarith
  have h := index_strict_order_from_intervals ((0/1)/1) ((0/1)/2) (nextNormalPenalty favorableNextS15Before) (nextNormalPenalty favorableNextS15Before) (57596539/25000000) (81453813/50000000)
    (treeBonus (7/5) 14 1) (treeBonus (7/5) 14 2)
    (trajectory_bonus_14_1).1 (trajectory_bonus_14_2).2 hm
  simpa only [treeIndex] using h

theorem favorableNextS15D0Cmp3 : indexScore (7/5) (controlPenalty savedCref uniformQuoteError unitRoleUnused .next) favorableNextS15Before [] (.query 3) < indexScore (7/5) (controlPenalty savedCref uniformQuoteError unitRoleUnused .next) favorableNextS15Before [] (.query 6) := by
  rw [favorableNextS15D0I3,favorableNextS15D0I6]
  have hk := favorable_next_penalty_interval 14 (by omega)
  change nextNormalPenaltyLower ≤ nextNormalPenalty favorableNextS15Before ∧ nextNormalPenalty favorableNextS15Before ≤ nextNormalPenaltyUpper at hk
  have hm : ((0/1)/2)+(81453813/50000000)-(nextNormalPenalty favorableNextS15Before) < ((0/1)/1)+(57596539/25000000)-(nextNormalPenalty favorableNextS15Before) := by
    have h : (((0/1)/2)+(81453813/50000000) : ℝ) < ((0/1)/1)+(57596539/25000000) := by norm_num
    linarith
  have h := index_strict_order_from_intervals ((0/1)/1) ((0/1)/2) (nextNormalPenalty favorableNextS15Before) (nextNormalPenalty favorableNextS15Before) (57596539/25000000) (81453813/50000000)
    (treeBonus (7/5) 14 1) (treeBonus (7/5) 14 2)
    (trajectory_bonus_14_1).1 (trajectory_bonus_14_2).2 hm
  simpa only [treeIndex] using h

theorem favorableNextS15D0Cmp4 : indexScore (7/5) (controlPenalty savedCref uniformQuoteError unitRoleUnused .next) favorableNextS15Before [] (.query 4) < indexScore (7/5) (controlPenalty savedCref uniformQuoteError unitRoleUnused .next) favorableNextS15Before [] (.query 6) := by
  rw [favorableNextS15D0I4,favorableNextS15D0I6]
  have hk := favorable_next_penalty_interval 14 (by omega)
  change nextNormalPenaltyLower ≤ nextNormalPenalty favorableNextS15Before ∧ nextNormalPenalty favorableNextS15Before ≤ nextNormalPenaltyUpper at hk
  have hm : ((0/1)/2)+(81453813/50000000)-(nextNormalPenalty favorableNextS15Before) < ((0/1)/1)+(57596539/25000000)-(nextNormalPenalty favorableNextS15Before) := by
    have h : (((0/1)/2)+(81453813/50000000) : ℝ) < ((0/1)/1)+(57596539/25000000) := by norm_num
    linarith
  have h := index_strict_order_from_intervals ((0/1)/1) ((0/1)/2) (nextNormalPenalty favorableNextS15Before) (nextNormalPenalty favorableNextS15Before) (57596539/25000000) (81453813/50000000)
    (treeBonus (7/5) 14 1) (treeBonus (7/5) 14 2)
    (trajectory_bonus_14_1).1 (trajectory_bonus_14_2).2 hm
  simpa only [treeIndex] using h

theorem favorableNextS15D0Cmp5 : indexScore (7/5) (controlPenalty savedCref uniformQuoteError unitRoleUnused .next) favorableNextS15Before [] (.query 5) < indexScore (7/5) (controlPenalty savedCref uniformQuoteError unitRoleUnused .next) favorableNextS15Before [] (.query 6) := by
  rw [favorableNextS15D0I5,favorableNextS15D0I6]
  have hk := favorable_next_penalty_interval 14 (by omega)
  change nextNormalPenaltyLower ≤ nextNormalPenalty favorableNextS15Before ∧ nextNormalPenalty favorableNextS15Before ≤ nextNormalPenaltyUpper at hk
  have hm : ((4/5)/2)+(81453813/50000000)-(nextNormalPenalty favorableNextS15Before) < ((0/1)/1)+(57596539/25000000)-(nextNormalPenalty favorableNextS15Before) := by
    have h : (((4/5)/2)+(81453813/50000000) : ℝ) < ((0/1)/1)+(57596539/25000000) := by norm_num
    linarith
  have h := index_strict_order_from_intervals ((0/1)/1) ((4/5)/2) (nextNormalPenalty favorableNextS15Before) (nextNormalPenalty favorableNextS15Before) (57596539/25000000) (81453813/50000000)
    (treeBonus (7/5) 14 1) (treeBonus (7/5) 14 2)
    (trajectory_bonus_14_1).1 (trajectory_bonus_14_2).2 hm
  simpa only [treeIndex] using h

theorem favorableNextS15D0Cmp7 : indexScore (7/5) (controlPenalty savedCref uniformQuoteError unitRoleUnused .next) favorableNextS15Before [] (.query 7) ≤ indexScore (7/5) (controlPenalty savedCref uniformQuoteError unitRoleUnused .next) favorableNextS15Before [] (.query 6) := by
  rw [favorableNextS15D0I7,favorableNextS15D0I6]

theorem favorableNextS15Choice0 : nativeFirstChoice (indexScore (7/5) (controlPenalty savedCref uniformQuoteError unitRoleUnused .next) favorableNextS15Before []) favorableNextS15Before [] = .query 6 := by
  apply visited_choice_from_ordered_certificate _ _ [] [.query 0,.query 1,.query 2,.query 3,.query 4,.query 5] [.query 7] (.query 6) (by decide)
  · intro a ha
    have ho : orderedLegalAvailable [] = [.query 0,.query 1,.query 2,.query 3,.query 4,.query 5,.query 6,.query 7] := by decide
    rw [ho] at ha
    simp only [List.mem_cons,List.not_mem_nil,or_false] at ha
    rcases ha with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> decide
  · intro a ha
    simp only [List.mem_cons,List.not_mem_nil,or_false] at ha
    rcases ha with rfl | rfl | rfl | rfl | rfl | rfl
    · exact favorableNextS15D0Cmp0
    · exact favorableNextS15D0Cmp1
    · exact favorableNextS15D0Cmp2
    · exact favorableNextS15D0Cmp3
    · exact favorableNextS15D0Cmp4
    · exact favorableNextS15D0Cmp5
  · intro a ha
    simp only [List.mem_cons,List.not_mem_nil,or_false] at ha
    rcases ha with rfl
    · exact favorableNextS15D0Cmp7

theorem favorableNextS15ActualEvent : nativeEvent budgetTape (7/5) (controlPenalty savedCref uniformQuoteError unitRoleUnused .next)
    (taskReward false (2/5) (1/2)) favorableNextS15Before = favorableNextEvent15 := by
  have hs0 := native_select_existing_step budgetTape (7/5) (controlPenalty savedCref uniformQuoteError unitRoleUnused .next) favorableNextS15Before 8 [] (.query 6)
    (by decide) (by decide) favorableNextS15Choice0
  have hnew := native_select_new_step budgetTape (7/5) (controlPenalty savedCref uniformQuoteError unitRoleUnused .next) favorableNextS15Before 7 [.query 6]
    [.normalRetriever 4,.normalRetriever 6,.normalRetriever 7,.normalRetriever 8,.normalRetriever 5,.normalRetriever 0,.normalRetriever 1,.normalRetriever 2,.normalRetriever 3,.normalRetriever 12,.normalRetriever 14,.normalRetriever 13,.normalRetriever 21,.normalRetriever 23,.normalRetriever 22,.normalRetriever 9,.normalRetriever 11,.normalRetriever 10,.normalRetriever 15,.normalRetriever 17,.normalRetriever 16,.normalRetriever 18,.normalRetriever 20,.normalRetriever 19,.normalRetriever 24,.normalRetriever 25,.normalRetriever 26,.normalRetriever 27,.normalRetriever 28,.normalRetriever 29] (.normalRetriever 0) (by decide) (by decide) (by decide) (by decide)
  have hs : nativeSelect budgetTape (7/5) (controlPenalty savedCref uniformQuoteError unitRoleUnused .next) favorableNextS15Before 9 [] = [.query 6,.normalRetriever 0] := by
    rw [hs0]
    change nativeSelect budgetTape (7/5) (controlPenalty savedCref uniformQuoteError unitRoleUnused .next) favorableNextS15Before 8 [.query 6] = _
    rw [hnew] <;> rfl
  have hr : repairedRollout budgetTape favorableNextS15Before 9 [.query 6,.normalRetriever 0] = [.query 6,.normalRetriever 0,.selection 0,.width 0,.stop,.reranker 0,.topm 0,.context 0,.answer 0] := by decide
  simp only [nativeEvent,hs,hr]
  rfl

def favorableNextS16Before := favorableNextProposal.take 15

theorem favorableNextS16D0I0 : indexScore (7/5) (controlPenalty savedCref uniformQuoteError unitRoleUnused .next) favorableNextS16Before [] (.query 0) = treeIndex ((0/1)/2) (7/5) (nextNormalPenalty favorableNextS16Before) 15 2 := by
  have hs : replayBackup favorableNextS16Before emptyStatistics ([]++[.query 0]) = ⟨2,(0/1)⟩ := by
    rw [replayBackup_empty_closed_form]
    simp +decide [backedEvents,favorableNextS16Before,favorableNextProposal,favorableNextEvent1,favorableNextEvent2,favorableNextEvent3,favorableNextEvent4,favorableNextEvent5,favorableNextEvent6,favorableNextEvent7,favorableNextEvent8,favorableNextEvent9,favorableNextEvent10,favorableNextEvent11,favorableNextEvent12,favorableNextEvent13,favorableNextEvent14,favorableNextEvent15,taskReward]
    <;> norm_num
  have hp : rawVisits favorableNextS16Before [] = 15 := by decide
  have hn : rawVisits favorableNextS16Before ([]++[.query 0]) = 2 := by decide
  have hz : (controlPenalty savedCref uniformQuoteError unitRoleUnused .next) favorableNextS16Before [] (.query 0) = (nextNormalPenalty favorableNextS16Before) := by
    simpa only [favorableNextS16Before,nextNormalPenalty] using AgentUCTNextExact.favorable_next_normal_root_quotes_exact 15 (by omega) 0 (by decide)
  unfold indexScore
  rw [hs,hp,hn,hz]
  simp only [BackupStat.mean]
  norm_num

theorem favorableNextS16D0I1 : indexScore (7/5) (controlPenalty savedCref uniformQuoteError unitRoleUnused .next) favorableNextS16Before [] (.query 1) = treeIndex ((1/2)/2) (7/5) 0 15 2 := by
  have hs : replayBackup favorableNextS16Before emptyStatistics ([]++[.query 1]) = ⟨2,(1/2)⟩ := by
    rw [replayBackup_empty_closed_form]
    simp +decide [backedEvents,favorableNextS16Before,favorableNextProposal,favorableNextEvent1,favorableNextEvent2,favorableNextEvent3,favorableNextEvent4,favorableNextEvent5,favorableNextEvent6,favorableNextEvent7,favorableNextEvent8,favorableNextEvent9,favorableNextEvent10,favorableNextEvent11,favorableNextEvent12,favorableNextEvent13,favorableNextEvent14,favorableNextEvent15,taskReward]
    <;> norm_num
  have hp : rawVisits favorableNextS16Before [] = 15 := by decide
  have hn : rawVisits favorableNextS16Before ([]++[.query 1]) = 2 := by decide
  have hz : (controlPenalty savedCref uniformQuoteError unitRoleUnused .next) favorableNextS16Before [] (.query 1) = 0 := by
    apply control_penalty_empty_suffix
    decide
  unfold indexScore
  rw [hs,hp,hn,hz]
  simp only [BackupStat.mean]
  norm_num

theorem favorableNextS16D0I2 : indexScore (7/5) (controlPenalty savedCref uniformQuoteError unitRoleUnused .next) favorableNextS16Before [] (.query 2) = treeIndex ((0/1)/2) (7/5) (nextNormalPenalty favorableNextS16Before) 15 2 := by
  have hs : replayBackup favorableNextS16Before emptyStatistics ([]++[.query 2]) = ⟨2,(0/1)⟩ := by
    rw [replayBackup_empty_closed_form]
    simp +decide [backedEvents,favorableNextS16Before,favorableNextProposal,favorableNextEvent1,favorableNextEvent2,favorableNextEvent3,favorableNextEvent4,favorableNextEvent5,favorableNextEvent6,favorableNextEvent7,favorableNextEvent8,favorableNextEvent9,favorableNextEvent10,favorableNextEvent11,favorableNextEvent12,favorableNextEvent13,favorableNextEvent14,favorableNextEvent15,taskReward]
    <;> norm_num
  have hp : rawVisits favorableNextS16Before [] = 15 := by decide
  have hn : rawVisits favorableNextS16Before ([]++[.query 2]) = 2 := by decide
  have hz : (controlPenalty savedCref uniformQuoteError unitRoleUnused .next) favorableNextS16Before [] (.query 2) = (nextNormalPenalty favorableNextS16Before) := by
    simpa only [favorableNextS16Before,nextNormalPenalty] using AgentUCTNextExact.favorable_next_normal_root_quotes_exact 15 (by omega) 2 (by decide)
  unfold indexScore
  rw [hs,hp,hn,hz]
  simp only [BackupStat.mean]
  norm_num

theorem favorableNextS16D0I3 : indexScore (7/5) (controlPenalty savedCref uniformQuoteError unitRoleUnused .next) favorableNextS16Before [] (.query 3) = treeIndex ((0/1)/2) (7/5) (nextNormalPenalty favorableNextS16Before) 15 2 := by
  have hs : replayBackup favorableNextS16Before emptyStatistics ([]++[.query 3]) = ⟨2,(0/1)⟩ := by
    rw [replayBackup_empty_closed_form]
    simp +decide [backedEvents,favorableNextS16Before,favorableNextProposal,favorableNextEvent1,favorableNextEvent2,favorableNextEvent3,favorableNextEvent4,favorableNextEvent5,favorableNextEvent6,favorableNextEvent7,favorableNextEvent8,favorableNextEvent9,favorableNextEvent10,favorableNextEvent11,favorableNextEvent12,favorableNextEvent13,favorableNextEvent14,favorableNextEvent15,taskReward]
    <;> norm_num
  have hp : rawVisits favorableNextS16Before [] = 15 := by decide
  have hn : rawVisits favorableNextS16Before ([]++[.query 3]) = 2 := by decide
  have hz : (controlPenalty savedCref uniformQuoteError unitRoleUnused .next) favorableNextS16Before [] (.query 3) = (nextNormalPenalty favorableNextS16Before) := by
    simpa only [favorableNextS16Before,nextNormalPenalty] using AgentUCTNextExact.favorable_next_normal_root_quotes_exact 15 (by omega) 3 (by decide)
  unfold indexScore
  rw [hs,hp,hn,hz]
  simp only [BackupStat.mean]
  norm_num

theorem favorableNextS16D0I4 : indexScore (7/5) (controlPenalty savedCref uniformQuoteError unitRoleUnused .next) favorableNextS16Before [] (.query 4) = treeIndex ((0/1)/2) (7/5) (nextNormalPenalty favorableNextS16Before) 15 2 := by
  have hs : replayBackup favorableNextS16Before emptyStatistics ([]++[.query 4]) = ⟨2,(0/1)⟩ := by
    rw [replayBackup_empty_closed_form]
    simp +decide [backedEvents,favorableNextS16Before,favorableNextProposal,favorableNextEvent1,favorableNextEvent2,favorableNextEvent3,favorableNextEvent4,favorableNextEvent5,favorableNextEvent6,favorableNextEvent7,favorableNextEvent8,favorableNextEvent9,favorableNextEvent10,favorableNextEvent11,favorableNextEvent12,favorableNextEvent13,favorableNextEvent14,favorableNextEvent15,taskReward]
    <;> norm_num
  have hp : rawVisits favorableNextS16Before [] = 15 := by decide
  have hn : rawVisits favorableNextS16Before ([]++[.query 4]) = 2 := by decide
  have hz : (controlPenalty savedCref uniformQuoteError unitRoleUnused .next) favorableNextS16Before [] (.query 4) = (nextNormalPenalty favorableNextS16Before) := by
    simpa only [favorableNextS16Before,nextNormalPenalty] using AgentUCTNextExact.favorable_next_normal_root_quotes_exact 15 (by omega) 4 (by decide)
  unfold indexScore
  rw [hs,hp,hn,hz]
  simp only [BackupStat.mean]
  norm_num

theorem favorableNextS16D0I5 : indexScore (7/5) (controlPenalty savedCref uniformQuoteError unitRoleUnused .next) favorableNextS16Before [] (.query 5) = treeIndex ((4/5)/2) (7/5) (nextNormalPenalty favorableNextS16Before) 15 2 := by
  have hs : replayBackup favorableNextS16Before emptyStatistics ([]++[.query 5]) = ⟨2,(4/5)⟩ := by
    rw [replayBackup_empty_closed_form]
    simp +decide [backedEvents,favorableNextS16Before,favorableNextProposal,favorableNextEvent1,favorableNextEvent2,favorableNextEvent3,favorableNextEvent4,favorableNextEvent5,favorableNextEvent6,favorableNextEvent7,favorableNextEvent8,favorableNextEvent9,favorableNextEvent10,favorableNextEvent11,favorableNextEvent12,favorableNextEvent13,favorableNextEvent14,favorableNextEvent15,taskReward]
    <;> norm_num
  have hp : rawVisits favorableNextS16Before [] = 15 := by decide
  have hn : rawVisits favorableNextS16Before ([]++[.query 5]) = 2 := by decide
  have hz : (controlPenalty savedCref uniformQuoteError unitRoleUnused .next) favorableNextS16Before [] (.query 5) = (nextNormalPenalty favorableNextS16Before) := by
    simpa only [favorableNextS16Before,nextNormalPenalty] using AgentUCTNextExact.favorable_next_normal_root_quotes_exact 15 (by omega) 5 (by decide)
  unfold indexScore
  rw [hs,hp,hn,hz]
  simp only [BackupStat.mean]
  norm_num

theorem favorableNextS16D0I6 : indexScore (7/5) (controlPenalty savedCref uniformQuoteError unitRoleUnused .next) favorableNextS16Before [] (.query 6) = treeIndex ((0/1)/2) (7/5) (nextNormalPenalty favorableNextS16Before) 15 2 := by
  have hs : replayBackup favorableNextS16Before emptyStatistics ([]++[.query 6]) = ⟨2,(0/1)⟩ := by
    rw [replayBackup_empty_closed_form]
    simp +decide [backedEvents,favorableNextS16Before,favorableNextProposal,favorableNextEvent1,favorableNextEvent2,favorableNextEvent3,favorableNextEvent4,favorableNextEvent5,favorableNextEvent6,favorableNextEvent7,favorableNextEvent8,favorableNextEvent9,favorableNextEvent10,favorableNextEvent11,favorableNextEvent12,favorableNextEvent13,favorableNextEvent14,favorableNextEvent15,taskReward]
    <;> norm_num
  have hp : rawVisits favorableNextS16Before [] = 15 := by decide
  have hn : rawVisits favorableNextS16Before ([]++[.query 6]) = 2 := by decide
  have hz : (controlPenalty savedCref uniformQuoteError unitRoleUnused .next) favorableNextS16Before [] (.query 6) = (nextNormalPenalty favorableNextS16Before) := by
    simpa only [favorableNextS16Before,nextNormalPenalty] using AgentUCTNextExact.favorable_next_normal_root_quotes_exact 15 (by omega) 6 (by decide)
  unfold indexScore
  rw [hs,hp,hn,hz]
  simp only [BackupStat.mean]
  norm_num

theorem favorableNextS16D0I7 : indexScore (7/5) (controlPenalty savedCref uniformQuoteError unitRoleUnused .next) favorableNextS16Before [] (.query 7) = treeIndex ((0/1)/1) (7/5) (nextNormalPenalty favorableNextS16Before) 15 1 := by
  have hs : replayBackup favorableNextS16Before emptyStatistics ([]++[.query 7]) = ⟨1,(0/1)⟩ := by
    rw [replayBackup_empty_closed_form]
    simp +decide [backedEvents,favorableNextS16Before,favorableNextProposal,favorableNextEvent1,favorableNextEvent2,favorableNextEvent3,favorableNextEvent4,favorableNextEvent5,favorableNextEvent6,favorableNextEvent7,favorableNextEvent8,favorableNextEvent9,favorableNextEvent10,favorableNextEvent11,favorableNextEvent12,favorableNextEvent13,favorableNextEvent14,favorableNextEvent15,taskReward]
    <;> norm_num
  have hp : rawVisits favorableNextS16Before [] = 15 := by decide
  have hn : rawVisits favorableNextS16Before ([]++[.query 7]) = 1 := by decide
  have hz : (controlPenalty savedCref uniformQuoteError unitRoleUnused .next) favorableNextS16Before [] (.query 7) = (nextNormalPenalty favorableNextS16Before) := by
    simpa only [favorableNextS16Before,nextNormalPenalty] using AgentUCTNextExact.favorable_next_normal_root_quotes_exact 15 (by omega) 7 (by decide)
  unfold indexScore
  rw [hs,hp,hn,hz]
  simp only [BackupStat.mean]
  norm_num

theorem favorableNextS16D0Cmp0 : indexScore (7/5) (controlPenalty savedCref uniformQuoteError unitRoleUnused .next) favorableNextS16Before [] (.query 0) < indexScore (7/5) (controlPenalty savedCref uniformQuoteError unitRoleUnused .next) favorableNextS16Before [] (.query 7) := by
  rw [favorableNextS16D0I0,favorableNextS16D0I7]
  have hk := favorable_next_penalty_interval 15 (by omega)
  change nextNormalPenaltyLower ≤ nextNormalPenalty favorableNextS16Before ∧ nextNormalPenalty favorableNextS16Before ≤ nextNormalPenaltyUpper at hk
  have hm : ((0/1)/2)+(82418707/50000000)-(nextNormalPenalty favorableNextS16Before) < ((0/1)/1)+(29139411/12500000)-(nextNormalPenalty favorableNextS16Before) := by
    have h : (((0/1)/2)+(82418707/50000000) : ℝ) < ((0/1)/1)+(29139411/12500000) := by norm_num
    linarith
  have h := index_strict_order_from_intervals ((0/1)/1) ((0/1)/2) (nextNormalPenalty favorableNextS16Before) (nextNormalPenalty favorableNextS16Before) (29139411/12500000) (82418707/50000000)
    (treeBonus (7/5) 15 1) (treeBonus (7/5) 15 2)
    (trajectory_bonus_15_1).1 (trajectory_bonus_15_2).2 hm
  simpa only [treeIndex] using h

theorem favorableNextS16D0Cmp1 : indexScore (7/5) (controlPenalty savedCref uniformQuoteError unitRoleUnused .next) favorableNextS16Before [] (.query 1) < indexScore (7/5) (controlPenalty savedCref uniformQuoteError unitRoleUnused .next) favorableNextS16Before [] (.query 7) := by
  rw [favorableNextS16D0I1,favorableNextS16D0I7]
  have hk := favorable_next_penalty_interval 15 (by omega)
  change nextNormalPenaltyLower ≤ nextNormalPenalty favorableNextS16Before ∧ nextNormalPenalty favorableNextS16Before ≤ nextNormalPenaltyUpper at hk
  have hm : ((1/2)/2)+(82418707/50000000)-0 < ((0/1)/1)+(29139411/12500000)-(nextNormalPenalty favorableNextS16Before) := by
    have h : ((1/2)/2)+(82418707/50000000) < ((0/1)/1)+(29139411/12500000)-nextNormalPenaltyUpper := by norm_num [nextNormalPenaltyUpper,savedCref,uniformQuoteError]
    linarith [hk.2]
  have h := index_strict_order_from_intervals ((0/1)/1) ((1/2)/2) (nextNormalPenalty favorableNextS16Before) 0 (29139411/12500000) (82418707/50000000)
    (treeBonus (7/5) 15 1) (treeBonus (7/5) 15 2)
    (trajectory_bonus_15_1).1 (trajectory_bonus_15_2).2 hm
  simpa only [treeIndex] using h

theorem favorableNextS16D0Cmp2 : indexScore (7/5) (controlPenalty savedCref uniformQuoteError unitRoleUnused .next) favorableNextS16Before [] (.query 2) < indexScore (7/5) (controlPenalty savedCref uniformQuoteError unitRoleUnused .next) favorableNextS16Before [] (.query 7) := by
  rw [favorableNextS16D0I2,favorableNextS16D0I7]
  have hk := favorable_next_penalty_interval 15 (by omega)
  change nextNormalPenaltyLower ≤ nextNormalPenalty favorableNextS16Before ∧ nextNormalPenalty favorableNextS16Before ≤ nextNormalPenaltyUpper at hk
  have hm : ((0/1)/2)+(82418707/50000000)-(nextNormalPenalty favorableNextS16Before) < ((0/1)/1)+(29139411/12500000)-(nextNormalPenalty favorableNextS16Before) := by
    have h : (((0/1)/2)+(82418707/50000000) : ℝ) < ((0/1)/1)+(29139411/12500000) := by norm_num
    linarith
  have h := index_strict_order_from_intervals ((0/1)/1) ((0/1)/2) (nextNormalPenalty favorableNextS16Before) (nextNormalPenalty favorableNextS16Before) (29139411/12500000) (82418707/50000000)
    (treeBonus (7/5) 15 1) (treeBonus (7/5) 15 2)
    (trajectory_bonus_15_1).1 (trajectory_bonus_15_2).2 hm
  simpa only [treeIndex] using h

theorem favorableNextS16D0Cmp3 : indexScore (7/5) (controlPenalty savedCref uniformQuoteError unitRoleUnused .next) favorableNextS16Before [] (.query 3) < indexScore (7/5) (controlPenalty savedCref uniformQuoteError unitRoleUnused .next) favorableNextS16Before [] (.query 7) := by
  rw [favorableNextS16D0I3,favorableNextS16D0I7]
  have hk := favorable_next_penalty_interval 15 (by omega)
  change nextNormalPenaltyLower ≤ nextNormalPenalty favorableNextS16Before ∧ nextNormalPenalty favorableNextS16Before ≤ nextNormalPenaltyUpper at hk
  have hm : ((0/1)/2)+(82418707/50000000)-(nextNormalPenalty favorableNextS16Before) < ((0/1)/1)+(29139411/12500000)-(nextNormalPenalty favorableNextS16Before) := by
    have h : (((0/1)/2)+(82418707/50000000) : ℝ) < ((0/1)/1)+(29139411/12500000) := by norm_num
    linarith
  have h := index_strict_order_from_intervals ((0/1)/1) ((0/1)/2) (nextNormalPenalty favorableNextS16Before) (nextNormalPenalty favorableNextS16Before) (29139411/12500000) (82418707/50000000)
    (treeBonus (7/5) 15 1) (treeBonus (7/5) 15 2)
    (trajectory_bonus_15_1).1 (trajectory_bonus_15_2).2 hm
  simpa only [treeIndex] using h

theorem favorableNextS16D0Cmp4 : indexScore (7/5) (controlPenalty savedCref uniformQuoteError unitRoleUnused .next) favorableNextS16Before [] (.query 4) < indexScore (7/5) (controlPenalty savedCref uniformQuoteError unitRoleUnused .next) favorableNextS16Before [] (.query 7) := by
  rw [favorableNextS16D0I4,favorableNextS16D0I7]
  have hk := favorable_next_penalty_interval 15 (by omega)
  change nextNormalPenaltyLower ≤ nextNormalPenalty favorableNextS16Before ∧ nextNormalPenalty favorableNextS16Before ≤ nextNormalPenaltyUpper at hk
  have hm : ((0/1)/2)+(82418707/50000000)-(nextNormalPenalty favorableNextS16Before) < ((0/1)/1)+(29139411/12500000)-(nextNormalPenalty favorableNextS16Before) := by
    have h : (((0/1)/2)+(82418707/50000000) : ℝ) < ((0/1)/1)+(29139411/12500000) := by norm_num
    linarith
  have h := index_strict_order_from_intervals ((0/1)/1) ((0/1)/2) (nextNormalPenalty favorableNextS16Before) (nextNormalPenalty favorableNextS16Before) (29139411/12500000) (82418707/50000000)
    (treeBonus (7/5) 15 1) (treeBonus (7/5) 15 2)
    (trajectory_bonus_15_1).1 (trajectory_bonus_15_2).2 hm
  simpa only [treeIndex] using h

theorem favorableNextS16D0Cmp5 : indexScore (7/5) (controlPenalty savedCref uniformQuoteError unitRoleUnused .next) favorableNextS16Before [] (.query 5) < indexScore (7/5) (controlPenalty savedCref uniformQuoteError unitRoleUnused .next) favorableNextS16Before [] (.query 7) := by
  rw [favorableNextS16D0I5,favorableNextS16D0I7]
  have hk := favorable_next_penalty_interval 15 (by omega)
  change nextNormalPenaltyLower ≤ nextNormalPenalty favorableNextS16Before ∧ nextNormalPenalty favorableNextS16Before ≤ nextNormalPenaltyUpper at hk
  have hm : ((4/5)/2)+(82418707/50000000)-(nextNormalPenalty favorableNextS16Before) < ((0/1)/1)+(29139411/12500000)-(nextNormalPenalty favorableNextS16Before) := by
    have h : (((4/5)/2)+(82418707/50000000) : ℝ) < ((0/1)/1)+(29139411/12500000) := by norm_num
    linarith
  have h := index_strict_order_from_intervals ((0/1)/1) ((4/5)/2) (nextNormalPenalty favorableNextS16Before) (nextNormalPenalty favorableNextS16Before) (29139411/12500000) (82418707/50000000)
    (treeBonus (7/5) 15 1) (treeBonus (7/5) 15 2)
    (trajectory_bonus_15_1).1 (trajectory_bonus_15_2).2 hm
  simpa only [treeIndex] using h

theorem favorableNextS16D0Cmp6 : indexScore (7/5) (controlPenalty savedCref uniformQuoteError unitRoleUnused .next) favorableNextS16Before [] (.query 6) < indexScore (7/5) (controlPenalty savedCref uniformQuoteError unitRoleUnused .next) favorableNextS16Before [] (.query 7) := by
  rw [favorableNextS16D0I6,favorableNextS16D0I7]
  have hk := favorable_next_penalty_interval 15 (by omega)
  change nextNormalPenaltyLower ≤ nextNormalPenalty favorableNextS16Before ∧ nextNormalPenalty favorableNextS16Before ≤ nextNormalPenaltyUpper at hk
  have hm : ((0/1)/2)+(82418707/50000000)-(nextNormalPenalty favorableNextS16Before) < ((0/1)/1)+(29139411/12500000)-(nextNormalPenalty favorableNextS16Before) := by
    have h : (((0/1)/2)+(82418707/50000000) : ℝ) < ((0/1)/1)+(29139411/12500000) := by norm_num
    linarith
  have h := index_strict_order_from_intervals ((0/1)/1) ((0/1)/2) (nextNormalPenalty favorableNextS16Before) (nextNormalPenalty favorableNextS16Before) (29139411/12500000) (82418707/50000000)
    (treeBonus (7/5) 15 1) (treeBonus (7/5) 15 2)
    (trajectory_bonus_15_1).1 (trajectory_bonus_15_2).2 hm
  simpa only [treeIndex] using h

theorem favorableNextS16Choice0 : nativeFirstChoice (indexScore (7/5) (controlPenalty savedCref uniformQuoteError unitRoleUnused .next) favorableNextS16Before []) favorableNextS16Before [] = .query 7 := by
  apply visited_choice_from_ordered_certificate _ _ [] [.query 0,.query 1,.query 2,.query 3,.query 4,.query 5,.query 6] [] (.query 7) (by decide)
  · intro a ha
    have ho : orderedLegalAvailable [] = [.query 0,.query 1,.query 2,.query 3,.query 4,.query 5,.query 6,.query 7] := by decide
    rw [ho] at ha
    simp only [List.mem_cons,List.not_mem_nil,or_false] at ha
    rcases ha with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> decide
  · intro a ha
    simp only [List.mem_cons,List.not_mem_nil,or_false] at ha
    rcases ha with rfl | rfl | rfl | rfl | rfl | rfl | rfl
    · exact favorableNextS16D0Cmp0
    · exact favorableNextS16D0Cmp1
    · exact favorableNextS16D0Cmp2
    · exact favorableNextS16D0Cmp3
    · exact favorableNextS16D0Cmp4
    · exact favorableNextS16D0Cmp5
    · exact favorableNextS16D0Cmp6
  · simp

theorem favorableNextS16ActualEvent : nativeEvent budgetTape (7/5) (controlPenalty savedCref uniformQuoteError unitRoleUnused .next)
    (taskReward false (2/5) (1/2)) favorableNextS16Before = favorableNextEvent16 := by
  have hs0 := native_select_existing_step budgetTape (7/5) (controlPenalty savedCref uniformQuoteError unitRoleUnused .next) favorableNextS16Before 8 [] (.query 7)
    (by decide) (by decide) favorableNextS16Choice0
  have hnew := native_select_new_step budgetTape (7/5) (controlPenalty savedCref uniformQuoteError unitRoleUnused .next) favorableNextS16Before 7 [.query 7]
    [.normalRetriever 4,.normalRetriever 6,.normalRetriever 7,.normalRetriever 8,.normalRetriever 5,.normalRetriever 0,.normalRetriever 1,.normalRetriever 2,.normalRetriever 3,.normalRetriever 12,.normalRetriever 14,.normalRetriever 13,.normalRetriever 21,.normalRetriever 23,.normalRetriever 22,.normalRetriever 9,.normalRetriever 11,.normalRetriever 10,.normalRetriever 15,.normalRetriever 17,.normalRetriever 16,.normalRetriever 18,.normalRetriever 20,.normalRetriever 19,.normalRetriever 24,.normalRetriever 25,.normalRetriever 26,.normalRetriever 27,.normalRetriever 28,.normalRetriever 29] (.normalRetriever 0) (by decide) (by decide) (by decide) (by decide)
  have hs : nativeSelect budgetTape (7/5) (controlPenalty savedCref uniformQuoteError unitRoleUnused .next) favorableNextS16Before 9 [] = [.query 7,.normalRetriever 0] := by
    rw [hs0]
    change nativeSelect budgetTape (7/5) (controlPenalty savedCref uniformQuoteError unitRoleUnused .next) favorableNextS16Before 8 [.query 7] = _
    rw [hnew] <;> rfl
  have hr : repairedRollout budgetTape favorableNextS16Before 9 [.query 7,.normalRetriever 0] = [.query 7,.normalRetriever 0,.selection 0,.width 0,.stop,.reranker 0,.topm 0,.context 0,.answer 0] := by decide
  simp only [nativeEvent,hs,hr]
  rfl

def favorableNextS17Before := favorableNextProposal.take 16

theorem favorableNextS17D0I0 : indexScore (7/5) (controlPenalty savedCref uniformQuoteError unitRoleUnused .next) favorableNextS17Before [] (.query 0) = treeIndex ((0/1)/2) (7/5) (nextNormalPenalty favorableNextS17Before) 16 2 := by
  have hs : replayBackup favorableNextS17Before emptyStatistics ([]++[.query 0]) = ⟨2,(0/1)⟩ := by
    rw [replayBackup_empty_closed_form]
    simp +decide [backedEvents,favorableNextS17Before,favorableNextProposal,favorableNextEvent1,favorableNextEvent2,favorableNextEvent3,favorableNextEvent4,favorableNextEvent5,favorableNextEvent6,favorableNextEvent7,favorableNextEvent8,favorableNextEvent9,favorableNextEvent10,favorableNextEvent11,favorableNextEvent12,favorableNextEvent13,favorableNextEvent14,favorableNextEvent15,favorableNextEvent16,taskReward]
    <;> norm_num
  have hp : rawVisits favorableNextS17Before [] = 16 := by decide
  have hn : rawVisits favorableNextS17Before ([]++[.query 0]) = 2 := by decide
  have hz : (controlPenalty savedCref uniformQuoteError unitRoleUnused .next) favorableNextS17Before [] (.query 0) = (nextNormalPenalty favorableNextS17Before) := by
    simpa only [favorableNextS17Before,nextNormalPenalty] using AgentUCTNextExact.favorable_next_normal_root_quotes_exact 16 (by omega) 0 (by decide)
  unfold indexScore
  rw [hs,hp,hn,hz]
  simp only [BackupStat.mean]
  norm_num

theorem favorableNextS17D0I1 : indexScore (7/5) (controlPenalty savedCref uniformQuoteError unitRoleUnused .next) favorableNextS17Before [] (.query 1) = treeIndex ((1/2)/2) (7/5) 0 16 2 := by
  have hs : replayBackup favorableNextS17Before emptyStatistics ([]++[.query 1]) = ⟨2,(1/2)⟩ := by
    rw [replayBackup_empty_closed_form]
    simp +decide [backedEvents,favorableNextS17Before,favorableNextProposal,favorableNextEvent1,favorableNextEvent2,favorableNextEvent3,favorableNextEvent4,favorableNextEvent5,favorableNextEvent6,favorableNextEvent7,favorableNextEvent8,favorableNextEvent9,favorableNextEvent10,favorableNextEvent11,favorableNextEvent12,favorableNextEvent13,favorableNextEvent14,favorableNextEvent15,favorableNextEvent16,taskReward]
    <;> norm_num
  have hp : rawVisits favorableNextS17Before [] = 16 := by decide
  have hn : rawVisits favorableNextS17Before ([]++[.query 1]) = 2 := by decide
  have hz : (controlPenalty savedCref uniformQuoteError unitRoleUnused .next) favorableNextS17Before [] (.query 1) = 0 := by
    apply control_penalty_empty_suffix
    decide
  unfold indexScore
  rw [hs,hp,hn,hz]
  simp only [BackupStat.mean]
  norm_num

theorem favorableNextS17D0I2 : indexScore (7/5) (controlPenalty savedCref uniformQuoteError unitRoleUnused .next) favorableNextS17Before [] (.query 2) = treeIndex ((0/1)/2) (7/5) (nextNormalPenalty favorableNextS17Before) 16 2 := by
  have hs : replayBackup favorableNextS17Before emptyStatistics ([]++[.query 2]) = ⟨2,(0/1)⟩ := by
    rw [replayBackup_empty_closed_form]
    simp +decide [backedEvents,favorableNextS17Before,favorableNextProposal,favorableNextEvent1,favorableNextEvent2,favorableNextEvent3,favorableNextEvent4,favorableNextEvent5,favorableNextEvent6,favorableNextEvent7,favorableNextEvent8,favorableNextEvent9,favorableNextEvent10,favorableNextEvent11,favorableNextEvent12,favorableNextEvent13,favorableNextEvent14,favorableNextEvent15,favorableNextEvent16,taskReward]
    <;> norm_num
  have hp : rawVisits favorableNextS17Before [] = 16 := by decide
  have hn : rawVisits favorableNextS17Before ([]++[.query 2]) = 2 := by decide
  have hz : (controlPenalty savedCref uniformQuoteError unitRoleUnused .next) favorableNextS17Before [] (.query 2) = (nextNormalPenalty favorableNextS17Before) := by
    simpa only [favorableNextS17Before,nextNormalPenalty] using AgentUCTNextExact.favorable_next_normal_root_quotes_exact 16 (by omega) 2 (by decide)
  unfold indexScore
  rw [hs,hp,hn,hz]
  simp only [BackupStat.mean]
  norm_num

theorem favorableNextS17D0I3 : indexScore (7/5) (controlPenalty savedCref uniformQuoteError unitRoleUnused .next) favorableNextS17Before [] (.query 3) = treeIndex ((0/1)/2) (7/5) (nextNormalPenalty favorableNextS17Before) 16 2 := by
  have hs : replayBackup favorableNextS17Before emptyStatistics ([]++[.query 3]) = ⟨2,(0/1)⟩ := by
    rw [replayBackup_empty_closed_form]
    simp +decide [backedEvents,favorableNextS17Before,favorableNextProposal,favorableNextEvent1,favorableNextEvent2,favorableNextEvent3,favorableNextEvent4,favorableNextEvent5,favorableNextEvent6,favorableNextEvent7,favorableNextEvent8,favorableNextEvent9,favorableNextEvent10,favorableNextEvent11,favorableNextEvent12,favorableNextEvent13,favorableNextEvent14,favorableNextEvent15,favorableNextEvent16,taskReward]
    <;> norm_num
  have hp : rawVisits favorableNextS17Before [] = 16 := by decide
  have hn : rawVisits favorableNextS17Before ([]++[.query 3]) = 2 := by decide
  have hz : (controlPenalty savedCref uniformQuoteError unitRoleUnused .next) favorableNextS17Before [] (.query 3) = (nextNormalPenalty favorableNextS17Before) := by
    simpa only [favorableNextS17Before,nextNormalPenalty] using AgentUCTNextExact.favorable_next_normal_root_quotes_exact 16 (by omega) 3 (by decide)
  unfold indexScore
  rw [hs,hp,hn,hz]
  simp only [BackupStat.mean]
  norm_num

theorem favorableNextS17D0I4 : indexScore (7/5) (controlPenalty savedCref uniformQuoteError unitRoleUnused .next) favorableNextS17Before [] (.query 4) = treeIndex ((0/1)/2) (7/5) (nextNormalPenalty favorableNextS17Before) 16 2 := by
  have hs : replayBackup favorableNextS17Before emptyStatistics ([]++[.query 4]) = ⟨2,(0/1)⟩ := by
    rw [replayBackup_empty_closed_form]
    simp +decide [backedEvents,favorableNextS17Before,favorableNextProposal,favorableNextEvent1,favorableNextEvent2,favorableNextEvent3,favorableNextEvent4,favorableNextEvent5,favorableNextEvent6,favorableNextEvent7,favorableNextEvent8,favorableNextEvent9,favorableNextEvent10,favorableNextEvent11,favorableNextEvent12,favorableNextEvent13,favorableNextEvent14,favorableNextEvent15,favorableNextEvent16,taskReward]
    <;> norm_num
  have hp : rawVisits favorableNextS17Before [] = 16 := by decide
  have hn : rawVisits favorableNextS17Before ([]++[.query 4]) = 2 := by decide
  have hz : (controlPenalty savedCref uniformQuoteError unitRoleUnused .next) favorableNextS17Before [] (.query 4) = (nextNormalPenalty favorableNextS17Before) := by
    simpa only [favorableNextS17Before,nextNormalPenalty] using AgentUCTNextExact.favorable_next_normal_root_quotes_exact 16 (by omega) 4 (by decide)
  unfold indexScore
  rw [hs,hp,hn,hz]
  simp only [BackupStat.mean]
  norm_num

theorem favorableNextS17D0I5 : indexScore (7/5) (controlPenalty savedCref uniformQuoteError unitRoleUnused .next) favorableNextS17Before [] (.query 5) = treeIndex ((4/5)/2) (7/5) (nextNormalPenalty favorableNextS17Before) 16 2 := by
  have hs : replayBackup favorableNextS17Before emptyStatistics ([]++[.query 5]) = ⟨2,(4/5)⟩ := by
    rw [replayBackup_empty_closed_form]
    simp +decide [backedEvents,favorableNextS17Before,favorableNextProposal,favorableNextEvent1,favorableNextEvent2,favorableNextEvent3,favorableNextEvent4,favorableNextEvent5,favorableNextEvent6,favorableNextEvent7,favorableNextEvent8,favorableNextEvent9,favorableNextEvent10,favorableNextEvent11,favorableNextEvent12,favorableNextEvent13,favorableNextEvent14,favorableNextEvent15,favorableNextEvent16,taskReward]
    <;> norm_num
  have hp : rawVisits favorableNextS17Before [] = 16 := by decide
  have hn : rawVisits favorableNextS17Before ([]++[.query 5]) = 2 := by decide
  have hz : (controlPenalty savedCref uniformQuoteError unitRoleUnused .next) favorableNextS17Before [] (.query 5) = (nextNormalPenalty favorableNextS17Before) := by
    simpa only [favorableNextS17Before,nextNormalPenalty] using AgentUCTNextExact.favorable_next_normal_root_quotes_exact 16 (by omega) 5 (by decide)
  unfold indexScore
  rw [hs,hp,hn,hz]
  simp only [BackupStat.mean]
  norm_num

theorem favorableNextS17D0I6 : indexScore (7/5) (controlPenalty savedCref uniformQuoteError unitRoleUnused .next) favorableNextS17Before [] (.query 6) = treeIndex ((0/1)/2) (7/5) (nextNormalPenalty favorableNextS17Before) 16 2 := by
  have hs : replayBackup favorableNextS17Before emptyStatistics ([]++[.query 6]) = ⟨2,(0/1)⟩ := by
    rw [replayBackup_empty_closed_form]
    simp +decide [backedEvents,favorableNextS17Before,favorableNextProposal,favorableNextEvent1,favorableNextEvent2,favorableNextEvent3,favorableNextEvent4,favorableNextEvent5,favorableNextEvent6,favorableNextEvent7,favorableNextEvent8,favorableNextEvent9,favorableNextEvent10,favorableNextEvent11,favorableNextEvent12,favorableNextEvent13,favorableNextEvent14,favorableNextEvent15,favorableNextEvent16,taskReward]
    <;> norm_num
  have hp : rawVisits favorableNextS17Before [] = 16 := by decide
  have hn : rawVisits favorableNextS17Before ([]++[.query 6]) = 2 := by decide
  have hz : (controlPenalty savedCref uniformQuoteError unitRoleUnused .next) favorableNextS17Before [] (.query 6) = (nextNormalPenalty favorableNextS17Before) := by
    simpa only [favorableNextS17Before,nextNormalPenalty] using AgentUCTNextExact.favorable_next_normal_root_quotes_exact 16 (by omega) 6 (by decide)
  unfold indexScore
  rw [hs,hp,hn,hz]
  simp only [BackupStat.mean]
  norm_num

theorem favorableNextS17D0I7 : indexScore (7/5) (controlPenalty savedCref uniformQuoteError unitRoleUnused .next) favorableNextS17Before [] (.query 7) = treeIndex ((0/1)/2) (7/5) (nextNormalPenalty favorableNextS17Before) 16 2 := by
  have hs : replayBackup favorableNextS17Before emptyStatistics ([]++[.query 7]) = ⟨2,(0/1)⟩ := by
    rw [replayBackup_empty_closed_form]
    simp +decide [backedEvents,favorableNextS17Before,favorableNextProposal,favorableNextEvent1,favorableNextEvent2,favorableNextEvent3,favorableNextEvent4,favorableNextEvent5,favorableNextEvent6,favorableNextEvent7,favorableNextEvent8,favorableNextEvent9,favorableNextEvent10,favorableNextEvent11,favorableNextEvent12,favorableNextEvent13,favorableNextEvent14,favorableNextEvent15,favorableNextEvent16,taskReward]
    <;> norm_num
  have hp : rawVisits favorableNextS17Before [] = 16 := by decide
  have hn : rawVisits favorableNextS17Before ([]++[.query 7]) = 2 := by decide
  have hz : (controlPenalty savedCref uniformQuoteError unitRoleUnused .next) favorableNextS17Before [] (.query 7) = (nextNormalPenalty favorableNextS17Before) := by
    simpa only [favorableNextS17Before,nextNormalPenalty] using AgentUCTNextExact.favorable_next_normal_root_quotes_exact 16 (by omega) 7 (by decide)
  unfold indexScore
  rw [hs,hp,hn,hz]
  simp only [BackupStat.mean]
  norm_num

theorem favorableNextS17D0Cmp0 : indexScore (7/5) (controlPenalty savedCref uniformQuoteError unitRoleUnused .next) favorableNextS17Before [] (.query 0) < indexScore (7/5) (controlPenalty savedCref uniformQuoteError unitRoleUnused .next) favorableNextS17Before [] (.query 1) := by
  rw [favorableNextS17D0I0,favorableNextS17D0I1]
  have hk := favorable_next_penalty_interval 16 (by omega)
  change nextNormalPenaltyLower ≤ nextNormalPenalty favorableNextS17Before ∧ nextNormalPenalty favorableNextS17Before ≤ nextNormalPenaltyUpper at hk
  have hm : ((0/1)/2)+(8331491/5000000)-(nextNormalPenalty favorableNextS17Before) < ((1/2)/2)+(5207181/3125000)-0 := by
    have h : ((0/1)/2)+(8331491/5000000)-nextNormalPenaltyLower < ((1/2)/2)+(5207181/3125000) := by norm_num [nextNormalPenaltyLower,savedCref,uniformQuoteError]
    linarith [hk.1]
  have h := index_strict_order_from_intervals ((1/2)/2) ((0/1)/2) 0 (nextNormalPenalty favorableNextS17Before) (5207181/3125000) (8331491/5000000)
    (treeBonus (7/5) 16 2) (treeBonus (7/5) 16 2)
    (trajectory_bonus_16_2).1 (trajectory_bonus_16_2).2 hm
  simpa only [treeIndex] using h

theorem favorableNextS17D0Cmp2 : indexScore (7/5) (controlPenalty savedCref uniformQuoteError unitRoleUnused .next) favorableNextS17Before [] (.query 2) ≤ indexScore (7/5) (controlPenalty savedCref uniformQuoteError unitRoleUnused .next) favorableNextS17Before [] (.query 1) := by
  rw [favorableNextS17D0I2,favorableNextS17D0I1]
  have hk := favorable_next_penalty_interval 16 (by omega)
  change nextNormalPenaltyLower ≤ nextNormalPenalty favorableNextS17Before ∧ nextNormalPenalty favorableNextS17Before ≤ nextNormalPenaltyUpper at hk
  have hm : ((0/1)/2)+(8331491/5000000)-(nextNormalPenalty favorableNextS17Before) < ((1/2)/2)+(5207181/3125000)-0 := by
    have h : ((0/1)/2)+(8331491/5000000)-nextNormalPenaltyLower < ((1/2)/2)+(5207181/3125000) := by norm_num [nextNormalPenaltyLower,savedCref,uniformQuoteError]
    linarith [hk.1]
  have h := index_weak_order_from_intervals ((1/2)/2) ((0/1)/2) 0 (nextNormalPenalty favorableNextS17Before) (5207181/3125000) (8331491/5000000)
    (treeBonus (7/5) 16 2) (treeBonus (7/5) 16 2)
    (trajectory_bonus_16_2).1 (trajectory_bonus_16_2).2 hm.le
  simpa only [treeIndex] using h

theorem favorableNextS17D0Cmp3 : indexScore (7/5) (controlPenalty savedCref uniformQuoteError unitRoleUnused .next) favorableNextS17Before [] (.query 3) ≤ indexScore (7/5) (controlPenalty savedCref uniformQuoteError unitRoleUnused .next) favorableNextS17Before [] (.query 1) := by
  rw [favorableNextS17D0I3,favorableNextS17D0I1]
  have hk := favorable_next_penalty_interval 16 (by omega)
  change nextNormalPenaltyLower ≤ nextNormalPenalty favorableNextS17Before ∧ nextNormalPenalty favorableNextS17Before ≤ nextNormalPenaltyUpper at hk
  have hm : ((0/1)/2)+(8331491/5000000)-(nextNormalPenalty favorableNextS17Before) < ((1/2)/2)+(5207181/3125000)-0 := by
    have h : ((0/1)/2)+(8331491/5000000)-nextNormalPenaltyLower < ((1/2)/2)+(5207181/3125000) := by norm_num [nextNormalPenaltyLower,savedCref,uniformQuoteError]
    linarith [hk.1]
  have h := index_weak_order_from_intervals ((1/2)/2) ((0/1)/2) 0 (nextNormalPenalty favorableNextS17Before) (5207181/3125000) (8331491/5000000)
    (treeBonus (7/5) 16 2) (treeBonus (7/5) 16 2)
    (trajectory_bonus_16_2).1 (trajectory_bonus_16_2).2 hm.le
  simpa only [treeIndex] using h

theorem favorableNextS17D0Cmp4 : indexScore (7/5) (controlPenalty savedCref uniformQuoteError unitRoleUnused .next) favorableNextS17Before [] (.query 4) ≤ indexScore (7/5) (controlPenalty savedCref uniformQuoteError unitRoleUnused .next) favorableNextS17Before [] (.query 1) := by
  rw [favorableNextS17D0I4,favorableNextS17D0I1]
  have hk := favorable_next_penalty_interval 16 (by omega)
  change nextNormalPenaltyLower ≤ nextNormalPenalty favorableNextS17Before ∧ nextNormalPenalty favorableNextS17Before ≤ nextNormalPenaltyUpper at hk
  have hm : ((0/1)/2)+(8331491/5000000)-(nextNormalPenalty favorableNextS17Before) < ((1/2)/2)+(5207181/3125000)-0 := by
    have h : ((0/1)/2)+(8331491/5000000)-nextNormalPenaltyLower < ((1/2)/2)+(5207181/3125000) := by norm_num [nextNormalPenaltyLower,savedCref,uniformQuoteError]
    linarith [hk.1]
  have h := index_weak_order_from_intervals ((1/2)/2) ((0/1)/2) 0 (nextNormalPenalty favorableNextS17Before) (5207181/3125000) (8331491/5000000)
    (treeBonus (7/5) 16 2) (treeBonus (7/5) 16 2)
    (trajectory_bonus_16_2).1 (trajectory_bonus_16_2).2 hm.le
  simpa only [treeIndex] using h

theorem favorableNextS17D0Cmp5 : indexScore (7/5) (controlPenalty savedCref uniformQuoteError unitRoleUnused .next) favorableNextS17Before [] (.query 5) ≤ indexScore (7/5) (controlPenalty savedCref uniformQuoteError unitRoleUnused .next) favorableNextS17Before [] (.query 1) := by
  rw [favorableNextS17D0I5,favorableNextS17D0I1]
  have hk := favorable_next_penalty_interval 16 (by omega)
  change nextNormalPenaltyLower ≤ nextNormalPenalty favorableNextS17Before ∧ nextNormalPenalty favorableNextS17Before ≤ nextNormalPenaltyUpper at hk
  have hm : ((4/5)/2)+(8331491/5000000)-(nextNormalPenalty favorableNextS17Before) < ((1/2)/2)+(5207181/3125000)-0 := by
    have h : ((4/5)/2)+(8331491/5000000)-nextNormalPenaltyLower < ((1/2)/2)+(5207181/3125000) := by norm_num [nextNormalPenaltyLower,savedCref,uniformQuoteError]
    linarith [hk.1]
  have h := index_weak_order_from_intervals ((1/2)/2) ((4/5)/2) 0 (nextNormalPenalty favorableNextS17Before) (5207181/3125000) (8331491/5000000)
    (treeBonus (7/5) 16 2) (treeBonus (7/5) 16 2)
    (trajectory_bonus_16_2).1 (trajectory_bonus_16_2).2 hm.le
  simpa only [treeIndex] using h

theorem favorableNextS17D0Cmp6 : indexScore (7/5) (controlPenalty savedCref uniformQuoteError unitRoleUnused .next) favorableNextS17Before [] (.query 6) ≤ indexScore (7/5) (controlPenalty savedCref uniformQuoteError unitRoleUnused .next) favorableNextS17Before [] (.query 1) := by
  rw [favorableNextS17D0I6,favorableNextS17D0I1]
  have hk := favorable_next_penalty_interval 16 (by omega)
  change nextNormalPenaltyLower ≤ nextNormalPenalty favorableNextS17Before ∧ nextNormalPenalty favorableNextS17Before ≤ nextNormalPenaltyUpper at hk
  have hm : ((0/1)/2)+(8331491/5000000)-(nextNormalPenalty favorableNextS17Before) < ((1/2)/2)+(5207181/3125000)-0 := by
    have h : ((0/1)/2)+(8331491/5000000)-nextNormalPenaltyLower < ((1/2)/2)+(5207181/3125000) := by norm_num [nextNormalPenaltyLower,savedCref,uniformQuoteError]
    linarith [hk.1]
  have h := index_weak_order_from_intervals ((1/2)/2) ((0/1)/2) 0 (nextNormalPenalty favorableNextS17Before) (5207181/3125000) (8331491/5000000)
    (treeBonus (7/5) 16 2) (treeBonus (7/5) 16 2)
    (trajectory_bonus_16_2).1 (trajectory_bonus_16_2).2 hm.le
  simpa only [treeIndex] using h

theorem favorableNextS17D0Cmp7 : indexScore (7/5) (controlPenalty savedCref uniformQuoteError unitRoleUnused .next) favorableNextS17Before [] (.query 7) ≤ indexScore (7/5) (controlPenalty savedCref uniformQuoteError unitRoleUnused .next) favorableNextS17Before [] (.query 1) := by
  rw [favorableNextS17D0I7,favorableNextS17D0I1]
  have hk := favorable_next_penalty_interval 16 (by omega)
  change nextNormalPenaltyLower ≤ nextNormalPenalty favorableNextS17Before ∧ nextNormalPenalty favorableNextS17Before ≤ nextNormalPenaltyUpper at hk
  have hm : ((0/1)/2)+(8331491/5000000)-(nextNormalPenalty favorableNextS17Before) < ((1/2)/2)+(5207181/3125000)-0 := by
    have h : ((0/1)/2)+(8331491/5000000)-nextNormalPenaltyLower < ((1/2)/2)+(5207181/3125000) := by norm_num [nextNormalPenaltyLower,savedCref,uniformQuoteError]
    linarith [hk.1]
  have h := index_weak_order_from_intervals ((1/2)/2) ((0/1)/2) 0 (nextNormalPenalty favorableNextS17Before) (5207181/3125000) (8331491/5000000)
    (treeBonus (7/5) 16 2) (treeBonus (7/5) 16 2)
    (trajectory_bonus_16_2).1 (trajectory_bonus_16_2).2 hm.le
  simpa only [treeIndex] using h

theorem favorableNextS17Choice0 : nativeFirstChoice (indexScore (7/5) (controlPenalty savedCref uniformQuoteError unitRoleUnused .next) favorableNextS17Before []) favorableNextS17Before [] = .query 1 := by
  apply visited_choice_from_ordered_certificate _ _ [] [.query 0] [.query 2,.query 3,.query 4,.query 5,.query 6,.query 7] (.query 1) (by decide)
  · intro a ha
    have ho : orderedLegalAvailable [] = [.query 0,.query 1,.query 2,.query 3,.query 4,.query 5,.query 6,.query 7] := by decide
    rw [ho] at ha
    simp only [List.mem_cons,List.not_mem_nil,or_false] at ha
    rcases ha with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> decide
  · intro a ha
    simp only [List.mem_cons,List.not_mem_nil,or_false] at ha
    rcases ha with rfl
    · exact favorableNextS17D0Cmp0
  · intro a ha
    simp only [List.mem_cons,List.not_mem_nil,or_false] at ha
    rcases ha with rfl | rfl | rfl | rfl | rfl | rfl
    · exact favorableNextS17D0Cmp2
    · exact favorableNextS17D0Cmp3
    · exact favorableNextS17D0Cmp4
    · exact favorableNextS17D0Cmp5
    · exact favorableNextS17D0Cmp6
    · exact favorableNextS17D0Cmp7

theorem favorableNextS17ActualEvent : nativeEvent budgetTape (7/5) (controlPenalty savedCref uniformQuoteError unitRoleUnused .next)
    (taskReward false (2/5) (1/2)) favorableNextS17Before = favorableNextEvent17 := by
  have hs0 := native_select_existing_step budgetTape (7/5) (controlPenalty savedCref uniformQuoteError unitRoleUnused .next) favorableNextS17Before 8 [] (.query 1)
    (by decide) (by decide) favorableNextS17Choice0
  have hnew := native_select_new_step budgetTape (7/5) (controlPenalty savedCref uniformQuoteError unitRoleUnused .next) favorableNextS17Before 7 [.query 1]
    [.hydeRetriever 0,.hydeRetriever 2] (.hydeRetriever 0) (by decide) (by decide) (by decide) (by decide)
  have hs : nativeSelect budgetTape (7/5) (controlPenalty savedCref uniformQuoteError unitRoleUnused .next) favorableNextS17Before 9 [] = [.query 1,.hydeRetriever 0] := by
    rw [hs0]
    change nativeSelect budgetTape (7/5) (controlPenalty savedCref uniformQuoteError unitRoleUnused .next) favorableNextS17Before 8 [.query 1] = _
    rw [hnew] <;> rfl
  have hr : repairedRollout budgetTape favorableNextS17Before 9 [.query 1,.hydeRetriever 0] = [.query 1,.hydeRetriever 0,.selection 0,.width 0,.stop,.reranker 0,.topm 0,.context 0,.answer 0] := by decide
  simp only [nativeEvent,hs,hr]
  rfl

def favorableNextS18Before := favorableNextProposal.take 17

theorem favorableNextS18D0I0 : indexScore (7/5) (controlPenalty savedCref uniformQuoteError unitRoleUnused .next) favorableNextS18Before [] (.query 0) = treeIndex ((0/1)/2) (7/5) (nextNormalPenalty favorableNextS18Before) 17 2 := by
  have hs : replayBackup favorableNextS18Before emptyStatistics ([]++[.query 0]) = ⟨2,(0/1)⟩ := by
    rw [replayBackup_empty_closed_form]
    simp +decide [backedEvents,favorableNextS18Before,favorableNextProposal,favorableNextEvent1,favorableNextEvent2,favorableNextEvent3,favorableNextEvent4,favorableNextEvent5,favorableNextEvent6,favorableNextEvent7,favorableNextEvent8,favorableNextEvent9,favorableNextEvent10,favorableNextEvent11,favorableNextEvent12,favorableNextEvent13,favorableNextEvent14,favorableNextEvent15,favorableNextEvent16,favorableNextEvent17,taskReward]
    <;> norm_num
  have hp : rawVisits favorableNextS18Before [] = 17 := by decide
  have hn : rawVisits favorableNextS18Before ([]++[.query 0]) = 2 := by decide
  have hz : (controlPenalty savedCref uniformQuoteError unitRoleUnused .next) favorableNextS18Before [] (.query 0) = (nextNormalPenalty favorableNextS18Before) := by
    simpa only [favorableNextS18Before,nextNormalPenalty] using AgentUCTNextExact.favorable_next_normal_root_quotes_exact 17 (by omega) 0 (by decide)
  unfold indexScore
  rw [hs,hp,hn,hz]
  simp only [BackupStat.mean]
  norm_num

theorem favorableNextS18D0I1 : indexScore (7/5) (controlPenalty savedCref uniformQuoteError unitRoleUnused .next) favorableNextS18Before [] (.query 1) = treeIndex ((1/2)/3) (7/5) 0 17 3 := by
  have hs : replayBackup favorableNextS18Before emptyStatistics ([]++[.query 1]) = ⟨3,(1/2)⟩ := by
    rw [replayBackup_empty_closed_form]
    simp +decide [backedEvents,favorableNextS18Before,favorableNextProposal,favorableNextEvent1,favorableNextEvent2,favorableNextEvent3,favorableNextEvent4,favorableNextEvent5,favorableNextEvent6,favorableNextEvent7,favorableNextEvent8,favorableNextEvent9,favorableNextEvent10,favorableNextEvent11,favorableNextEvent12,favorableNextEvent13,favorableNextEvent14,favorableNextEvent15,favorableNextEvent16,favorableNextEvent17,taskReward]
    <;> norm_num
  have hp : rawVisits favorableNextS18Before [] = 17 := by decide
  have hn : rawVisits favorableNextS18Before ([]++[.query 1]) = 3 := by decide
  have hz : (controlPenalty savedCref uniformQuoteError unitRoleUnused .next) favorableNextS18Before [] (.query 1) = 0 := by
    apply control_penalty_empty_suffix
    decide
  unfold indexScore
  rw [hs,hp,hn,hz]
  simp only [BackupStat.mean]
  norm_num

theorem favorableNextS18D0I2 : indexScore (7/5) (controlPenalty savedCref uniformQuoteError unitRoleUnused .next) favorableNextS18Before [] (.query 2) = treeIndex ((0/1)/2) (7/5) (nextNormalPenalty favorableNextS18Before) 17 2 := by
  have hs : replayBackup favorableNextS18Before emptyStatistics ([]++[.query 2]) = ⟨2,(0/1)⟩ := by
    rw [replayBackup_empty_closed_form]
    simp +decide [backedEvents,favorableNextS18Before,favorableNextProposal,favorableNextEvent1,favorableNextEvent2,favorableNextEvent3,favorableNextEvent4,favorableNextEvent5,favorableNextEvent6,favorableNextEvent7,favorableNextEvent8,favorableNextEvent9,favorableNextEvent10,favorableNextEvent11,favorableNextEvent12,favorableNextEvent13,favorableNextEvent14,favorableNextEvent15,favorableNextEvent16,favorableNextEvent17,taskReward]
    <;> norm_num
  have hp : rawVisits favorableNextS18Before [] = 17 := by decide
  have hn : rawVisits favorableNextS18Before ([]++[.query 2]) = 2 := by decide
  have hz : (controlPenalty savedCref uniformQuoteError unitRoleUnused .next) favorableNextS18Before [] (.query 2) = (nextNormalPenalty favorableNextS18Before) := by
    simpa only [favorableNextS18Before,nextNormalPenalty] using AgentUCTNextExact.favorable_next_normal_root_quotes_exact 17 (by omega) 2 (by decide)
  unfold indexScore
  rw [hs,hp,hn,hz]
  simp only [BackupStat.mean]
  norm_num

theorem favorableNextS18D0I3 : indexScore (7/5) (controlPenalty savedCref uniformQuoteError unitRoleUnused .next) favorableNextS18Before [] (.query 3) = treeIndex ((0/1)/2) (7/5) (nextNormalPenalty favorableNextS18Before) 17 2 := by
  have hs : replayBackup favorableNextS18Before emptyStatistics ([]++[.query 3]) = ⟨2,(0/1)⟩ := by
    rw [replayBackup_empty_closed_form]
    simp +decide [backedEvents,favorableNextS18Before,favorableNextProposal,favorableNextEvent1,favorableNextEvent2,favorableNextEvent3,favorableNextEvent4,favorableNextEvent5,favorableNextEvent6,favorableNextEvent7,favorableNextEvent8,favorableNextEvent9,favorableNextEvent10,favorableNextEvent11,favorableNextEvent12,favorableNextEvent13,favorableNextEvent14,favorableNextEvent15,favorableNextEvent16,favorableNextEvent17,taskReward]
    <;> norm_num
  have hp : rawVisits favorableNextS18Before [] = 17 := by decide
  have hn : rawVisits favorableNextS18Before ([]++[.query 3]) = 2 := by decide
  have hz : (controlPenalty savedCref uniformQuoteError unitRoleUnused .next) favorableNextS18Before [] (.query 3) = (nextNormalPenalty favorableNextS18Before) := by
    simpa only [favorableNextS18Before,nextNormalPenalty] using AgentUCTNextExact.favorable_next_normal_root_quotes_exact 17 (by omega) 3 (by decide)
  unfold indexScore
  rw [hs,hp,hn,hz]
  simp only [BackupStat.mean]
  norm_num

theorem favorableNextS18D0I4 : indexScore (7/5) (controlPenalty savedCref uniformQuoteError unitRoleUnused .next) favorableNextS18Before [] (.query 4) = treeIndex ((0/1)/2) (7/5) (nextNormalPenalty favorableNextS18Before) 17 2 := by
  have hs : replayBackup favorableNextS18Before emptyStatistics ([]++[.query 4]) = ⟨2,(0/1)⟩ := by
    rw [replayBackup_empty_closed_form]
    simp +decide [backedEvents,favorableNextS18Before,favorableNextProposal,favorableNextEvent1,favorableNextEvent2,favorableNextEvent3,favorableNextEvent4,favorableNextEvent5,favorableNextEvent6,favorableNextEvent7,favorableNextEvent8,favorableNextEvent9,favorableNextEvent10,favorableNextEvent11,favorableNextEvent12,favorableNextEvent13,favorableNextEvent14,favorableNextEvent15,favorableNextEvent16,favorableNextEvent17,taskReward]
    <;> norm_num
  have hp : rawVisits favorableNextS18Before [] = 17 := by decide
  have hn : rawVisits favorableNextS18Before ([]++[.query 4]) = 2 := by decide
  have hz : (controlPenalty savedCref uniformQuoteError unitRoleUnused .next) favorableNextS18Before [] (.query 4) = (nextNormalPenalty favorableNextS18Before) := by
    simpa only [favorableNextS18Before,nextNormalPenalty] using AgentUCTNextExact.favorable_next_normal_root_quotes_exact 17 (by omega) 4 (by decide)
  unfold indexScore
  rw [hs,hp,hn,hz]
  simp only [BackupStat.mean]
  norm_num

theorem favorableNextS18D0I5 : indexScore (7/5) (controlPenalty savedCref uniformQuoteError unitRoleUnused .next) favorableNextS18Before [] (.query 5) = treeIndex ((4/5)/2) (7/5) (nextNormalPenalty favorableNextS18Before) 17 2 := by
  have hs : replayBackup favorableNextS18Before emptyStatistics ([]++[.query 5]) = ⟨2,(4/5)⟩ := by
    rw [replayBackup_empty_closed_form]
    simp +decide [backedEvents,favorableNextS18Before,favorableNextProposal,favorableNextEvent1,favorableNextEvent2,favorableNextEvent3,favorableNextEvent4,favorableNextEvent5,favorableNextEvent6,favorableNextEvent7,favorableNextEvent8,favorableNextEvent9,favorableNextEvent10,favorableNextEvent11,favorableNextEvent12,favorableNextEvent13,favorableNextEvent14,favorableNextEvent15,favorableNextEvent16,favorableNextEvent17,taskReward]
    <;> norm_num
  have hp : rawVisits favorableNextS18Before [] = 17 := by decide
  have hn : rawVisits favorableNextS18Before ([]++[.query 5]) = 2 := by decide
  have hz : (controlPenalty savedCref uniformQuoteError unitRoleUnused .next) favorableNextS18Before [] (.query 5) = (nextNormalPenalty favorableNextS18Before) := by
    simpa only [favorableNextS18Before,nextNormalPenalty] using AgentUCTNextExact.favorable_next_normal_root_quotes_exact 17 (by omega) 5 (by decide)
  unfold indexScore
  rw [hs,hp,hn,hz]
  simp only [BackupStat.mean]
  norm_num

theorem favorableNextS18D0I6 : indexScore (7/5) (controlPenalty savedCref uniformQuoteError unitRoleUnused .next) favorableNextS18Before [] (.query 6) = treeIndex ((0/1)/2) (7/5) (nextNormalPenalty favorableNextS18Before) 17 2 := by
  have hs : replayBackup favorableNextS18Before emptyStatistics ([]++[.query 6]) = ⟨2,(0/1)⟩ := by
    rw [replayBackup_empty_closed_form]
    simp +decide [backedEvents,favorableNextS18Before,favorableNextProposal,favorableNextEvent1,favorableNextEvent2,favorableNextEvent3,favorableNextEvent4,favorableNextEvent5,favorableNextEvent6,favorableNextEvent7,favorableNextEvent8,favorableNextEvent9,favorableNextEvent10,favorableNextEvent11,favorableNextEvent12,favorableNextEvent13,favorableNextEvent14,favorableNextEvent15,favorableNextEvent16,favorableNextEvent17,taskReward]
    <;> norm_num
  have hp : rawVisits favorableNextS18Before [] = 17 := by decide
  have hn : rawVisits favorableNextS18Before ([]++[.query 6]) = 2 := by decide
  have hz : (controlPenalty savedCref uniformQuoteError unitRoleUnused .next) favorableNextS18Before [] (.query 6) = (nextNormalPenalty favorableNextS18Before) := by
    simpa only [favorableNextS18Before,nextNormalPenalty] using AgentUCTNextExact.favorable_next_normal_root_quotes_exact 17 (by omega) 6 (by decide)
  unfold indexScore
  rw [hs,hp,hn,hz]
  simp only [BackupStat.mean]
  norm_num

theorem favorableNextS18D0I7 : indexScore (7/5) (controlPenalty savedCref uniformQuoteError unitRoleUnused .next) favorableNextS18Before [] (.query 7) = treeIndex ((0/1)/2) (7/5) (nextNormalPenalty favorableNextS18Before) 17 2 := by
  have hs : replayBackup favorableNextS18Before emptyStatistics ([]++[.query 7]) = ⟨2,(0/1)⟩ := by
    rw [replayBackup_empty_closed_form]
    simp +decide [backedEvents,favorableNextS18Before,favorableNextProposal,favorableNextEvent1,favorableNextEvent2,favorableNextEvent3,favorableNextEvent4,favorableNextEvent5,favorableNextEvent6,favorableNextEvent7,favorableNextEvent8,favorableNextEvent9,favorableNextEvent10,favorableNextEvent11,favorableNextEvent12,favorableNextEvent13,favorableNextEvent14,favorableNextEvent15,favorableNextEvent16,favorableNextEvent17,taskReward]
    <;> norm_num
  have hp : rawVisits favorableNextS18Before [] = 17 := by decide
  have hn : rawVisits favorableNextS18Before ([]++[.query 7]) = 2 := by decide
  have hz : (controlPenalty savedCref uniformQuoteError unitRoleUnused .next) favorableNextS18Before [] (.query 7) = (nextNormalPenalty favorableNextS18Before) := by
    simpa only [favorableNextS18Before,nextNormalPenalty] using AgentUCTNextExact.favorable_next_normal_root_quotes_exact 17 (by omega) 7 (by decide)
  unfold indexScore
  rw [hs,hp,hn,hz]
  simp only [BackupStat.mean]
  norm_num

theorem favorableNextS18D0Cmp0 : indexScore (7/5) (controlPenalty savedCref uniformQuoteError unitRoleUnused .next) favorableNextS18Before [] (.query 0) < indexScore (7/5) (controlPenalty savedCref uniformQuoteError unitRoleUnused .next) favorableNextS18Before [] (.query 5) := by
  rw [favorableNextS18D0I0,favorableNextS18D0I5]
  have hk := favorable_next_penalty_interval 17 (by omega)
  change nextNormalPenaltyLower ≤ nextNormalPenalty favorableNextS18Before ∧ nextNormalPenalty favorableNextS18Before ≤ nextNormalPenaltyUpper at hk
  have hm : ((0/1)/2)+(84151123/50000000)-(nextNormalPenalty favorableNextS18Before) < ((4/5)/2)+(21037779/12500000)-(nextNormalPenalty favorableNextS18Before) := by
    have h : (((0/1)/2)+(84151123/50000000) : ℝ) < ((4/5)/2)+(21037779/12500000) := by norm_num
    linarith
  have h := index_strict_order_from_intervals ((4/5)/2) ((0/1)/2) (nextNormalPenalty favorableNextS18Before) (nextNormalPenalty favorableNextS18Before) (21037779/12500000) (84151123/50000000)
    (treeBonus (7/5) 17 2) (treeBonus (7/5) 17 2)
    (trajectory_bonus_17_2).1 (trajectory_bonus_17_2).2 hm
  simpa only [treeIndex] using h

theorem favorableNextS18D0Cmp1 : indexScore (7/5) (controlPenalty savedCref uniformQuoteError unitRoleUnused .next) favorableNextS18Before [] (.query 1) < indexScore (7/5) (controlPenalty savedCref uniformQuoteError unitRoleUnused .next) favorableNextS18Before [] (.query 5) := by
  rw [favorableNextS18D0I1,favorableNextS18D0I5]
  have hk := favorable_next_penalty_interval 17 (by omega)
  change nextNormalPenaltyLower ≤ nextNormalPenalty favorableNextS18Before ∧ nextNormalPenalty favorableNextS18Before ≤ nextNormalPenaltyUpper at hk
  have hm : ((1/2)/3)+(68709109/50000000)-0 < ((4/5)/2)+(21037779/12500000)-(nextNormalPenalty favorableNextS18Before) := by
    have h : ((1/2)/3)+(68709109/50000000) < ((4/5)/2)+(21037779/12500000)-nextNormalPenaltyUpper := by norm_num [nextNormalPenaltyUpper,savedCref,uniformQuoteError]
    linarith [hk.2]
  have h := index_strict_order_from_intervals ((4/5)/2) ((1/2)/3) (nextNormalPenalty favorableNextS18Before) 0 (21037779/12500000) (68709109/50000000)
    (treeBonus (7/5) 17 2) (treeBonus (7/5) 17 3)
    (trajectory_bonus_17_2).1 (trajectory_bonus_17_3).2 hm
  simpa only [treeIndex] using h

theorem favorableNextS18D0Cmp2 : indexScore (7/5) (controlPenalty savedCref uniformQuoteError unitRoleUnused .next) favorableNextS18Before [] (.query 2) < indexScore (7/5) (controlPenalty savedCref uniformQuoteError unitRoleUnused .next) favorableNextS18Before [] (.query 5) := by
  rw [favorableNextS18D0I2,favorableNextS18D0I5]
  have hk := favorable_next_penalty_interval 17 (by omega)
  change nextNormalPenaltyLower ≤ nextNormalPenalty favorableNextS18Before ∧ nextNormalPenalty favorableNextS18Before ≤ nextNormalPenaltyUpper at hk
  have hm : ((0/1)/2)+(84151123/50000000)-(nextNormalPenalty favorableNextS18Before) < ((4/5)/2)+(21037779/12500000)-(nextNormalPenalty favorableNextS18Before) := by
    have h : (((0/1)/2)+(84151123/50000000) : ℝ) < ((4/5)/2)+(21037779/12500000) := by norm_num
    linarith
  have h := index_strict_order_from_intervals ((4/5)/2) ((0/1)/2) (nextNormalPenalty favorableNextS18Before) (nextNormalPenalty favorableNextS18Before) (21037779/12500000) (84151123/50000000)
    (treeBonus (7/5) 17 2) (treeBonus (7/5) 17 2)
    (trajectory_bonus_17_2).1 (trajectory_bonus_17_2).2 hm
  simpa only [treeIndex] using h

theorem favorableNextS18D0Cmp3 : indexScore (7/5) (controlPenalty savedCref uniformQuoteError unitRoleUnused .next) favorableNextS18Before [] (.query 3) < indexScore (7/5) (controlPenalty savedCref uniformQuoteError unitRoleUnused .next) favorableNextS18Before [] (.query 5) := by
  rw [favorableNextS18D0I3,favorableNextS18D0I5]
  have hk := favorable_next_penalty_interval 17 (by omega)
  change nextNormalPenaltyLower ≤ nextNormalPenalty favorableNextS18Before ∧ nextNormalPenalty favorableNextS18Before ≤ nextNormalPenaltyUpper at hk
  have hm : ((0/1)/2)+(84151123/50000000)-(nextNormalPenalty favorableNextS18Before) < ((4/5)/2)+(21037779/12500000)-(nextNormalPenalty favorableNextS18Before) := by
    have h : (((0/1)/2)+(84151123/50000000) : ℝ) < ((4/5)/2)+(21037779/12500000) := by norm_num
    linarith
  have h := index_strict_order_from_intervals ((4/5)/2) ((0/1)/2) (nextNormalPenalty favorableNextS18Before) (nextNormalPenalty favorableNextS18Before) (21037779/12500000) (84151123/50000000)
    (treeBonus (7/5) 17 2) (treeBonus (7/5) 17 2)
    (trajectory_bonus_17_2).1 (trajectory_bonus_17_2).2 hm
  simpa only [treeIndex] using h

theorem favorableNextS18D0Cmp4 : indexScore (7/5) (controlPenalty savedCref uniformQuoteError unitRoleUnused .next) favorableNextS18Before [] (.query 4) < indexScore (7/5) (controlPenalty savedCref uniformQuoteError unitRoleUnused .next) favorableNextS18Before [] (.query 5) := by
  rw [favorableNextS18D0I4,favorableNextS18D0I5]
  have hk := favorable_next_penalty_interval 17 (by omega)
  change nextNormalPenaltyLower ≤ nextNormalPenalty favorableNextS18Before ∧ nextNormalPenalty favorableNextS18Before ≤ nextNormalPenaltyUpper at hk
  have hm : ((0/1)/2)+(84151123/50000000)-(nextNormalPenalty favorableNextS18Before) < ((4/5)/2)+(21037779/12500000)-(nextNormalPenalty favorableNextS18Before) := by
    have h : (((0/1)/2)+(84151123/50000000) : ℝ) < ((4/5)/2)+(21037779/12500000) := by norm_num
    linarith
  have h := index_strict_order_from_intervals ((4/5)/2) ((0/1)/2) (nextNormalPenalty favorableNextS18Before) (nextNormalPenalty favorableNextS18Before) (21037779/12500000) (84151123/50000000)
    (treeBonus (7/5) 17 2) (treeBonus (7/5) 17 2)
    (trajectory_bonus_17_2).1 (trajectory_bonus_17_2).2 hm
  simpa only [treeIndex] using h

theorem favorableNextS18D0Cmp6 : indexScore (7/5) (controlPenalty savedCref uniformQuoteError unitRoleUnused .next) favorableNextS18Before [] (.query 6) ≤ indexScore (7/5) (controlPenalty savedCref uniformQuoteError unitRoleUnused .next) favorableNextS18Before [] (.query 5) := by
  rw [favorableNextS18D0I6,favorableNextS18D0I5]
  have hk := favorable_next_penalty_interval 17 (by omega)
  change nextNormalPenaltyLower ≤ nextNormalPenalty favorableNextS18Before ∧ nextNormalPenalty favorableNextS18Before ≤ nextNormalPenaltyUpper at hk
  have hm : ((0/1)/2)+(84151123/50000000)-(nextNormalPenalty favorableNextS18Before) < ((4/5)/2)+(21037779/12500000)-(nextNormalPenalty favorableNextS18Before) := by
    have h : (((0/1)/2)+(84151123/50000000) : ℝ) < ((4/5)/2)+(21037779/12500000) := by norm_num
    linarith
  have h := index_weak_order_from_intervals ((4/5)/2) ((0/1)/2) (nextNormalPenalty favorableNextS18Before) (nextNormalPenalty favorableNextS18Before) (21037779/12500000) (84151123/50000000)
    (treeBonus (7/5) 17 2) (treeBonus (7/5) 17 2)
    (trajectory_bonus_17_2).1 (trajectory_bonus_17_2).2 hm.le
  simpa only [treeIndex] using h

theorem favorableNextS18D0Cmp7 : indexScore (7/5) (controlPenalty savedCref uniformQuoteError unitRoleUnused .next) favorableNextS18Before [] (.query 7) ≤ indexScore (7/5) (controlPenalty savedCref uniformQuoteError unitRoleUnused .next) favorableNextS18Before [] (.query 5) := by
  rw [favorableNextS18D0I7,favorableNextS18D0I5]
  have hk := favorable_next_penalty_interval 17 (by omega)
  change nextNormalPenaltyLower ≤ nextNormalPenalty favorableNextS18Before ∧ nextNormalPenalty favorableNextS18Before ≤ nextNormalPenaltyUpper at hk
  have hm : ((0/1)/2)+(84151123/50000000)-(nextNormalPenalty favorableNextS18Before) < ((4/5)/2)+(21037779/12500000)-(nextNormalPenalty favorableNextS18Before) := by
    have h : (((0/1)/2)+(84151123/50000000) : ℝ) < ((4/5)/2)+(21037779/12500000) := by norm_num
    linarith
  have h := index_weak_order_from_intervals ((4/5)/2) ((0/1)/2) (nextNormalPenalty favorableNextS18Before) (nextNormalPenalty favorableNextS18Before) (21037779/12500000) (84151123/50000000)
    (treeBonus (7/5) 17 2) (treeBonus (7/5) 17 2)
    (trajectory_bonus_17_2).1 (trajectory_bonus_17_2).2 hm.le
  simpa only [treeIndex] using h

theorem favorableNextS18Choice0 : nativeFirstChoice (indexScore (7/5) (controlPenalty savedCref uniformQuoteError unitRoleUnused .next) favorableNextS18Before []) favorableNextS18Before [] = .query 5 := by
  apply visited_choice_from_ordered_certificate _ _ [] [.query 0,.query 1,.query 2,.query 3,.query 4] [.query 6,.query 7] (.query 5) (by decide)
  · intro a ha
    have ho : orderedLegalAvailable [] = [.query 0,.query 1,.query 2,.query 3,.query 4,.query 5,.query 6,.query 7] := by decide
    rw [ho] at ha
    simp only [List.mem_cons,List.not_mem_nil,or_false] at ha
    rcases ha with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> decide
  · intro a ha
    simp only [List.mem_cons,List.not_mem_nil,or_false] at ha
    rcases ha with rfl | rfl | rfl | rfl | rfl
    · exact favorableNextS18D0Cmp0
    · exact favorableNextS18D0Cmp1
    · exact favorableNextS18D0Cmp2
    · exact favorableNextS18D0Cmp3
    · exact favorableNextS18D0Cmp4
  · intro a ha
    simp only [List.mem_cons,List.not_mem_nil,or_false] at ha
    rcases ha with rfl | rfl
    · exact favorableNextS18D0Cmp6
    · exact favorableNextS18D0Cmp7

theorem favorableNextS18ActualEvent : nativeEvent budgetTape (7/5) (controlPenalty savedCref uniformQuoteError unitRoleUnused .next)
    (taskReward false (2/5) (1/2)) favorableNextS18Before = favorableNextEvent18 := by
  have hs0 := native_select_existing_step budgetTape (7/5) (controlPenalty savedCref uniformQuoteError unitRoleUnused .next) favorableNextS18Before 8 [] (.query 5)
    (by decide) (by decide) favorableNextS18Choice0
  have hnew := native_select_new_step budgetTape (7/5) (controlPenalty savedCref uniformQuoteError unitRoleUnused .next) favorableNextS18Before 7 [.query 5]
    [.normalRetriever 4,.normalRetriever 6,.normalRetriever 7,.normalRetriever 8,.normalRetriever 5,.normalRetriever 0,.normalRetriever 2,.normalRetriever 3,.normalRetriever 12,.normalRetriever 14,.normalRetriever 13,.normalRetriever 21,.normalRetriever 23,.normalRetriever 22,.normalRetriever 9,.normalRetriever 11,.normalRetriever 10,.normalRetriever 15,.normalRetriever 17,.normalRetriever 16,.normalRetriever 18,.normalRetriever 20,.normalRetriever 19,.normalRetriever 24,.normalRetriever 25,.normalRetriever 26,.normalRetriever 27,.normalRetriever 28,.normalRetriever 29] (.normalRetriever 0) (by decide) (by decide) (by decide) (by decide)
  have hs : nativeSelect budgetTape (7/5) (controlPenalty savedCref uniformQuoteError unitRoleUnused .next) favorableNextS18Before 9 [] = [.query 5,.normalRetriever 0] := by
    rw [hs0]
    change nativeSelect budgetTape (7/5) (controlPenalty savedCref uniformQuoteError unitRoleUnused .next) favorableNextS18Before 8 [.query 5] = _
    rw [hnew] <;> rfl
  have hr : repairedRollout budgetTape favorableNextS18Before 9 [.query 5,.normalRetriever 0] = [.query 5,.normalRetriever 0,.selection 0,.width 0,.stop,.reranker 0,.topm 0,.context 0,.answer 0] := by decide
  simp only [nativeEvent,hs,hr]
  rfl

end AgentUCT32MConcrete
