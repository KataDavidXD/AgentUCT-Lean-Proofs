import ProposalRewards
import TrajectoryBonus
import InitialConcreteBridge
import NextRootIndexBridge
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

def adverseNextS11Before := adverseNextProposal.take 10

theorem adverseNextS11D0I0 : indexScore (7/5) (controlPenalty savedCref uniformQuoteError unitRoleUnused .next) adverseNextS11Before [] (.query 0) = treeIndex ((0/1)/1) (7/5) (nextNormalPenalty adverseNextS11Before) 10 1 := by
  have hs : replayBackup adverseNextS11Before emptyStatistics ([]++[.query 0]) = ⟨1,(0/1)⟩ := by
    rw [replayBackup_empty_closed_form]
    simp +decide [backedEvents,adverseNextS11Before,adverseNextProposal,adverseNextEvent1,adverseNextEvent2,adverseNextEvent3,adverseNextEvent4,adverseNextEvent5,adverseNextEvent6,adverseNextEvent7,adverseNextEvent8,adverseNextEvent9,adverseNextEvent10,taskReward]
    <;> norm_num
  have hp : rawVisits adverseNextS11Before [] = 10 := by decide
  have hn : rawVisits adverseNextS11Before ([]++[.query 0]) = 1 := by decide
  have hz : (controlPenalty savedCref uniformQuoteError unitRoleUnused .next) adverseNextS11Before [] (.query 0) = (nextNormalPenalty adverseNextS11Before) := by
    simpa only [adverseNextS11Before,nextNormalPenalty] using AgentUCTNextExact.adverse_next_normal_root_quotes_exact 10 (by omega) 0 (by decide)
  unfold indexScore
  rw [hs,hp,hn,hz]
  simp only [BackupStat.mean]
  norm_num

theorem adverseNextS11D0I1 : indexScore (7/5) (controlPenalty savedCref uniformQuoteError unitRoleUnused .next) adverseNextS11Before [] (.query 1) = treeIndex ((0/1)/2) (7/5) 0 10 2 := by
  have hs : replayBackup adverseNextS11Before emptyStatistics ([]++[.query 1]) = ⟨2,(0/1)⟩ := by
    rw [replayBackup_empty_closed_form]
    simp +decide [backedEvents,adverseNextS11Before,adverseNextProposal,adverseNextEvent1,adverseNextEvent2,adverseNextEvent3,adverseNextEvent4,adverseNextEvent5,adverseNextEvent6,adverseNextEvent7,adverseNextEvent8,adverseNextEvent9,adverseNextEvent10,taskReward]
    <;> norm_num
  have hp : rawVisits adverseNextS11Before [] = 10 := by decide
  have hn : rawVisits adverseNextS11Before ([]++[.query 1]) = 2 := by decide
  have hz : (controlPenalty savedCref uniformQuoteError unitRoleUnused .next) adverseNextS11Before [] (.query 1) = 0 := by
    apply control_penalty_empty_suffix
    exact AgentUCTNextExact.adverse_next_hyde_root_suffix_empty 10 (by omega)
  unfold indexScore
  rw [hs,hp,hn,hz]
  simp only [BackupStat.mean]
  norm_num

theorem adverseNextS11D0I2 : indexScore (7/5) (controlPenalty savedCref uniformQuoteError unitRoleUnused .next) adverseNextS11Before [] (.query 2) = treeIndex ((0/1)/1) (7/5) (nextNormalPenalty adverseNextS11Before) 10 1 := by
  have hs : replayBackup adverseNextS11Before emptyStatistics ([]++[.query 2]) = ⟨1,(0/1)⟩ := by
    rw [replayBackup_empty_closed_form]
    simp +decide [backedEvents,adverseNextS11Before,adverseNextProposal,adverseNextEvent1,adverseNextEvent2,adverseNextEvent3,adverseNextEvent4,adverseNextEvent5,adverseNextEvent6,adverseNextEvent7,adverseNextEvent8,adverseNextEvent9,adverseNextEvent10,taskReward]
    <;> norm_num
  have hp : rawVisits adverseNextS11Before [] = 10 := by decide
  have hn : rawVisits adverseNextS11Before ([]++[.query 2]) = 1 := by decide
  have hz : (controlPenalty savedCref uniformQuoteError unitRoleUnused .next) adverseNextS11Before [] (.query 2) = (nextNormalPenalty adverseNextS11Before) := by
    simpa only [adverseNextS11Before,nextNormalPenalty] using AgentUCTNextExact.adverse_next_normal_root_quotes_exact 10 (by omega) 2 (by decide)
  unfold indexScore
  rw [hs,hp,hn,hz]
  simp only [BackupStat.mean]
  norm_num

theorem adverseNextS11D0I3 : indexScore (7/5) (controlPenalty savedCref uniformQuoteError unitRoleUnused .next) adverseNextS11Before [] (.query 3) = treeIndex ((0/1)/1) (7/5) (nextNormalPenalty adverseNextS11Before) 10 1 := by
  have hs : replayBackup adverseNextS11Before emptyStatistics ([]++[.query 3]) = ⟨1,(0/1)⟩ := by
    rw [replayBackup_empty_closed_form]
    simp +decide [backedEvents,adverseNextS11Before,adverseNextProposal,adverseNextEvent1,adverseNextEvent2,adverseNextEvent3,adverseNextEvent4,adverseNextEvent5,adverseNextEvent6,adverseNextEvent7,adverseNextEvent8,adverseNextEvent9,adverseNextEvent10,taskReward]
    <;> norm_num
  have hp : rawVisits adverseNextS11Before [] = 10 := by decide
  have hn : rawVisits adverseNextS11Before ([]++[.query 3]) = 1 := by decide
  have hz : (controlPenalty savedCref uniformQuoteError unitRoleUnused .next) adverseNextS11Before [] (.query 3) = (nextNormalPenalty adverseNextS11Before) := by
    simpa only [adverseNextS11Before,nextNormalPenalty] using AgentUCTNextExact.adverse_next_normal_root_quotes_exact 10 (by omega) 3 (by decide)
  unfold indexScore
  rw [hs,hp,hn,hz]
  simp only [BackupStat.mean]
  norm_num

theorem adverseNextS11D0I4 : indexScore (7/5) (controlPenalty savedCref uniformQuoteError unitRoleUnused .next) adverseNextS11Before [] (.query 4) = treeIndex ((0/1)/1) (7/5) (nextNormalPenalty adverseNextS11Before) 10 1 := by
  have hs : replayBackup adverseNextS11Before emptyStatistics ([]++[.query 4]) = ⟨1,(0/1)⟩ := by
    rw [replayBackup_empty_closed_form]
    simp +decide [backedEvents,adverseNextS11Before,adverseNextProposal,adverseNextEvent1,adverseNextEvent2,adverseNextEvent3,adverseNextEvent4,adverseNextEvent5,adverseNextEvent6,adverseNextEvent7,adverseNextEvent8,adverseNextEvent9,adverseNextEvent10,taskReward]
    <;> norm_num
  have hp : rawVisits adverseNextS11Before [] = 10 := by decide
  have hn : rawVisits adverseNextS11Before ([]++[.query 4]) = 1 := by decide
  have hz : (controlPenalty savedCref uniformQuoteError unitRoleUnused .next) adverseNextS11Before [] (.query 4) = (nextNormalPenalty adverseNextS11Before) := by
    simpa only [adverseNextS11Before,nextNormalPenalty] using AgentUCTNextExact.adverse_next_normal_root_quotes_exact 10 (by omega) 4 (by decide)
  unfold indexScore
  rw [hs,hp,hn,hz]
  simp only [BackupStat.mean]
  norm_num

theorem adverseNextS11D0I5 : indexScore (7/5) (controlPenalty savedCref uniformQuoteError unitRoleUnused .next) adverseNextS11Before [] (.query 5) = treeIndex ((9/10)/2) (7/5) (nextNormalPenalty adverseNextS11Before) 10 2 := by
  have hs : replayBackup adverseNextS11Before emptyStatistics ([]++[.query 5]) = ⟨2,(9/10)⟩ := by
    rw [replayBackup_empty_closed_form]
    simp +decide [backedEvents,adverseNextS11Before,adverseNextProposal,adverseNextEvent1,adverseNextEvent2,adverseNextEvent3,adverseNextEvent4,adverseNextEvent5,adverseNextEvent6,adverseNextEvent7,adverseNextEvent8,adverseNextEvent9,adverseNextEvent10,taskReward]
    <;> norm_num
  have hp : rawVisits adverseNextS11Before [] = 10 := by decide
  have hn : rawVisits adverseNextS11Before ([]++[.query 5]) = 2 := by decide
  have hz : (controlPenalty savedCref uniformQuoteError unitRoleUnused .next) adverseNextS11Before [] (.query 5) = (nextNormalPenalty adverseNextS11Before) := by
    simpa only [adverseNextS11Before,nextNormalPenalty] using AgentUCTNextExact.adverse_next_normal_root_quotes_exact 10 (by omega) 5 (by decide)
  unfold indexScore
  rw [hs,hp,hn,hz]
  simp only [BackupStat.mean]
  norm_num

theorem adverseNextS11D0I6 : indexScore (7/5) (controlPenalty savedCref uniformQuoteError unitRoleUnused .next) adverseNextS11Before [] (.query 6) = treeIndex ((0/1)/1) (7/5) (nextNormalPenalty adverseNextS11Before) 10 1 := by
  have hs : replayBackup adverseNextS11Before emptyStatistics ([]++[.query 6]) = ⟨1,(0/1)⟩ := by
    rw [replayBackup_empty_closed_form]
    simp +decide [backedEvents,adverseNextS11Before,adverseNextProposal,adverseNextEvent1,adverseNextEvent2,adverseNextEvent3,adverseNextEvent4,adverseNextEvent5,adverseNextEvent6,adverseNextEvent7,adverseNextEvent8,adverseNextEvent9,adverseNextEvent10,taskReward]
    <;> norm_num
  have hp : rawVisits adverseNextS11Before [] = 10 := by decide
  have hn : rawVisits adverseNextS11Before ([]++[.query 6]) = 1 := by decide
  have hz : (controlPenalty savedCref uniformQuoteError unitRoleUnused .next) adverseNextS11Before [] (.query 6) = (nextNormalPenalty adverseNextS11Before) := by
    simpa only [adverseNextS11Before,nextNormalPenalty] using AgentUCTNextExact.adverse_next_normal_root_quotes_exact 10 (by omega) 6 (by decide)
  unfold indexScore
  rw [hs,hp,hn,hz]
  simp only [BackupStat.mean]
  norm_num

theorem adverseNextS11D0I7 : indexScore (7/5) (controlPenalty savedCref uniformQuoteError unitRoleUnused .next) adverseNextS11Before [] (.query 7) = treeIndex ((0/1)/1) (7/5) (nextNormalPenalty adverseNextS11Before) 10 1 := by
  have hs : replayBackup adverseNextS11Before emptyStatistics ([]++[.query 7]) = ⟨1,(0/1)⟩ := by
    rw [replayBackup_empty_closed_form]
    simp +decide [backedEvents,adverseNextS11Before,adverseNextProposal,adverseNextEvent1,adverseNextEvent2,adverseNextEvent3,adverseNextEvent4,adverseNextEvent5,adverseNextEvent6,adverseNextEvent7,adverseNextEvent8,adverseNextEvent9,adverseNextEvent10,taskReward]
    <;> norm_num
  have hp : rawVisits adverseNextS11Before [] = 10 := by decide
  have hn : rawVisits adverseNextS11Before ([]++[.query 7]) = 1 := by decide
  have hz : (controlPenalty savedCref uniformQuoteError unitRoleUnused .next) adverseNextS11Before [] (.query 7) = (nextNormalPenalty adverseNextS11Before) := by
    simpa only [adverseNextS11Before,nextNormalPenalty] using AgentUCTNextExact.adverse_next_normal_root_quotes_exact 10 (by omega) 7 (by decide)
  unfold indexScore
  rw [hs,hp,hn,hz]
  simp only [BackupStat.mean]
  norm_num

theorem adverseNextS11D0Cmp1 : indexScore (7/5) (controlPenalty savedCref uniformQuoteError unitRoleUnused .next) adverseNextS11Before [] (.query 1) ≤ indexScore (7/5) (controlPenalty savedCref uniformQuoteError unitRoleUnused .next) adverseNextS11Before [] (.query 0) := by
  rw [adverseNextS11D0I1,adverseNextS11D0I0]
  have hk := adverse_next_penalty_interval 10 (by omega)
  change nextNormalPenaltyLower ≤ nextNormalPenalty adverseNextS11Before ∧ nextNormalPenalty adverseNextS11Before ≤ nextNormalPenaltyUpper at hk
  have hm : ((0/1)/2)+(76647529/50000000)-0 < ((0/1)/1)+(54197983/25000000)-(nextNormalPenalty adverseNextS11Before) := by
    have h : ((0/1)/2)+(76647529/50000000) < ((0/1)/1)+(54197983/25000000)-nextNormalPenaltyUpper := by norm_num [nextNormalPenaltyUpper,savedCref,uniformQuoteError]
    linarith [hk.2]
  have h := index_weak_order_from_intervals ((0/1)/1) ((0/1)/2) (nextNormalPenalty adverseNextS11Before) 0 (54197983/25000000) (76647529/50000000)
    (treeBonus (7/5) 10 1) (treeBonus (7/5) 10 2)
    (trajectory_bonus_10_1).1 (trajectory_bonus_10_2).2 hm.le
  simpa only [treeIndex] using h

theorem adverseNextS11D0Cmp2 : indexScore (7/5) (controlPenalty savedCref uniformQuoteError unitRoleUnused .next) adverseNextS11Before [] (.query 2) ≤ indexScore (7/5) (controlPenalty savedCref uniformQuoteError unitRoleUnused .next) adverseNextS11Before [] (.query 0) := by
  rw [adverseNextS11D0I2,adverseNextS11D0I0]

theorem adverseNextS11D0Cmp3 : indexScore (7/5) (controlPenalty savedCref uniformQuoteError unitRoleUnused .next) adverseNextS11Before [] (.query 3) ≤ indexScore (7/5) (controlPenalty savedCref uniformQuoteError unitRoleUnused .next) adverseNextS11Before [] (.query 0) := by
  rw [adverseNextS11D0I3,adverseNextS11D0I0]

theorem adverseNextS11D0Cmp4 : indexScore (7/5) (controlPenalty savedCref uniformQuoteError unitRoleUnused .next) adverseNextS11Before [] (.query 4) ≤ indexScore (7/5) (controlPenalty savedCref uniformQuoteError unitRoleUnused .next) adverseNextS11Before [] (.query 0) := by
  rw [adverseNextS11D0I4,adverseNextS11D0I0]

theorem adverseNextS11D0Cmp5 : indexScore (7/5) (controlPenalty savedCref uniformQuoteError unitRoleUnused .next) adverseNextS11Before [] (.query 5) ≤ indexScore (7/5) (controlPenalty savedCref uniformQuoteError unitRoleUnused .next) adverseNextS11Before [] (.query 0) := by
  rw [adverseNextS11D0I5,adverseNextS11D0I0]
  have hk := adverse_next_penalty_interval 10 (by omega)
  change nextNormalPenaltyLower ≤ nextNormalPenalty adverseNextS11Before ∧ nextNormalPenalty adverseNextS11Before ≤ nextNormalPenaltyUpper at hk
  have hm : ((9/10)/2)+(76647529/50000000)-(nextNormalPenalty adverseNextS11Before) < ((0/1)/1)+(54197983/25000000)-(nextNormalPenalty adverseNextS11Before) := by
    have h : (((9/10)/2)+(76647529/50000000) : ℝ) < ((0/1)/1)+(54197983/25000000) := by norm_num
    linarith
  have h := index_weak_order_from_intervals ((0/1)/1) ((9/10)/2) (nextNormalPenalty adverseNextS11Before) (nextNormalPenalty adverseNextS11Before) (54197983/25000000) (76647529/50000000)
    (treeBonus (7/5) 10 1) (treeBonus (7/5) 10 2)
    (trajectory_bonus_10_1).1 (trajectory_bonus_10_2).2 hm.le
  simpa only [treeIndex] using h

theorem adverseNextS11D0Cmp6 : indexScore (7/5) (controlPenalty savedCref uniformQuoteError unitRoleUnused .next) adverseNextS11Before [] (.query 6) ≤ indexScore (7/5) (controlPenalty savedCref uniformQuoteError unitRoleUnused .next) adverseNextS11Before [] (.query 0) := by
  rw [adverseNextS11D0I6,adverseNextS11D0I0]

theorem adverseNextS11D0Cmp7 : indexScore (7/5) (controlPenalty savedCref uniformQuoteError unitRoleUnused .next) adverseNextS11Before [] (.query 7) ≤ indexScore (7/5) (controlPenalty savedCref uniformQuoteError unitRoleUnused .next) adverseNextS11Before [] (.query 0) := by
  rw [adverseNextS11D0I7,adverseNextS11D0I0]

theorem adverseNextS11Choice0 : nativeFirstChoice (indexScore (7/5) (controlPenalty savedCref uniformQuoteError unitRoleUnused .next) adverseNextS11Before []) adverseNextS11Before [] = .query 0 := by
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
    · exact adverseNextS11D0Cmp1
    · exact adverseNextS11D0Cmp2
    · exact adverseNextS11D0Cmp3
    · exact adverseNextS11D0Cmp4
    · exact adverseNextS11D0Cmp5
    · exact adverseNextS11D0Cmp6
    · exact adverseNextS11D0Cmp7

theorem adverseNextS11ActualEvent : nativeEvent budgetTape (7/5) (controlPenalty savedCref uniformQuoteError unitRoleUnused .next)
    (taskReward true (2/5) (1/2)) adverseNextS11Before = adverseNextEvent11 := by
  have hs0 := native_select_existing_step budgetTape (7/5) (controlPenalty savedCref uniformQuoteError unitRoleUnused .next) adverseNextS11Before 8 [] (.query 0)
    (by decide) (by decide) adverseNextS11Choice0
  have hnew := native_select_new_step budgetTape (7/5) (controlPenalty savedCref uniformQuoteError unitRoleUnused .next) adverseNextS11Before 7 [.query 0]
    [.normalRetriever 4,.normalRetriever 6,.normalRetriever 7,.normalRetriever 8,.normalRetriever 5,.normalRetriever 0,.normalRetriever 1,.normalRetriever 2,.normalRetriever 3,.normalRetriever 12,.normalRetriever 14,.normalRetriever 13,.normalRetriever 21,.normalRetriever 23,.normalRetriever 22,.normalRetriever 9,.normalRetriever 11,.normalRetriever 10,.normalRetriever 15,.normalRetriever 17,.normalRetriever 16,.normalRetriever 18,.normalRetriever 20,.normalRetriever 19,.normalRetriever 24,.normalRetriever 25,.normalRetriever 26,.normalRetriever 27,.normalRetriever 28,.normalRetriever 29] (.normalRetriever 0) (by decide) (by decide) (by decide) (by decide)
  have hs : nativeSelect budgetTape (7/5) (controlPenalty savedCref uniformQuoteError unitRoleUnused .next) adverseNextS11Before 9 [] = [.query 0,.normalRetriever 0] := by
    rw [hs0]
    change nativeSelect budgetTape (7/5) (controlPenalty savedCref uniformQuoteError unitRoleUnused .next) adverseNextS11Before 8 [.query 0] = _
    rw [hnew] <;> rfl
  have hr : repairedRollout budgetTape adverseNextS11Before 9 [.query 0,.normalRetriever 0] = [.query 0,.normalRetriever 0,.selection 0,.width 0,.stop,.reranker 0,.topm 0,.context 0,.answer 0] := by decide
  simp only [nativeEvent,hs,hr]
  rfl

def adverseNextS12Before := adverseNextProposal.take 11

theorem adverseNextS12D0I0 : indexScore (7/5) (controlPenalty savedCref uniformQuoteError unitRoleUnused .next) adverseNextS12Before [] (.query 0) = treeIndex ((0/1)/2) (7/5) (nextNormalPenalty adverseNextS12Before) 11 2 := by
  have hs : replayBackup adverseNextS12Before emptyStatistics ([]++[.query 0]) = ⟨2,(0/1)⟩ := by
    rw [replayBackup_empty_closed_form]
    simp +decide [backedEvents,adverseNextS12Before,adverseNextProposal,adverseNextEvent1,adverseNextEvent2,adverseNextEvent3,adverseNextEvent4,adverseNextEvent5,adverseNextEvent6,adverseNextEvent7,adverseNextEvent8,adverseNextEvent9,adverseNextEvent10,adverseNextEvent11,taskReward]
    <;> norm_num
  have hp : rawVisits adverseNextS12Before [] = 11 := by decide
  have hn : rawVisits adverseNextS12Before ([]++[.query 0]) = 2 := by decide
  have hz : (controlPenalty savedCref uniformQuoteError unitRoleUnused .next) adverseNextS12Before [] (.query 0) = (nextNormalPenalty adverseNextS12Before) := by
    simpa only [adverseNextS12Before,nextNormalPenalty] using AgentUCTNextExact.adverse_next_normal_root_quotes_exact 11 (by omega) 0 (by decide)
  unfold indexScore
  rw [hs,hp,hn,hz]
  simp only [BackupStat.mean]
  norm_num

theorem adverseNextS12D0I1 : indexScore (7/5) (controlPenalty savedCref uniformQuoteError unitRoleUnused .next) adverseNextS12Before [] (.query 1) = treeIndex ((0/1)/2) (7/5) 0 11 2 := by
  have hs : replayBackup adverseNextS12Before emptyStatistics ([]++[.query 1]) = ⟨2,(0/1)⟩ := by
    rw [replayBackup_empty_closed_form]
    simp +decide [backedEvents,adverseNextS12Before,adverseNextProposal,adverseNextEvent1,adverseNextEvent2,adverseNextEvent3,adverseNextEvent4,adverseNextEvent5,adverseNextEvent6,adverseNextEvent7,adverseNextEvent8,adverseNextEvent9,adverseNextEvent10,adverseNextEvent11,taskReward]
    <;> norm_num
  have hp : rawVisits adverseNextS12Before [] = 11 := by decide
  have hn : rawVisits adverseNextS12Before ([]++[.query 1]) = 2 := by decide
  have hz : (controlPenalty savedCref uniformQuoteError unitRoleUnused .next) adverseNextS12Before [] (.query 1) = 0 := by
    apply control_penalty_empty_suffix
    exact AgentUCTNextExact.adverse_next_hyde_root_suffix_empty 11 (by omega)
  unfold indexScore
  rw [hs,hp,hn,hz]
  simp only [BackupStat.mean]
  norm_num

theorem adverseNextS12D0I2 : indexScore (7/5) (controlPenalty savedCref uniformQuoteError unitRoleUnused .next) adverseNextS12Before [] (.query 2) = treeIndex ((0/1)/1) (7/5) (nextNormalPenalty adverseNextS12Before) 11 1 := by
  have hs : replayBackup adverseNextS12Before emptyStatistics ([]++[.query 2]) = ⟨1,(0/1)⟩ := by
    rw [replayBackup_empty_closed_form]
    simp +decide [backedEvents,adverseNextS12Before,adverseNextProposal,adverseNextEvent1,adverseNextEvent2,adverseNextEvent3,adverseNextEvent4,adverseNextEvent5,adverseNextEvent6,adverseNextEvent7,adverseNextEvent8,adverseNextEvent9,adverseNextEvent10,adverseNextEvent11,taskReward]
    <;> norm_num
  have hp : rawVisits adverseNextS12Before [] = 11 := by decide
  have hn : rawVisits adverseNextS12Before ([]++[.query 2]) = 1 := by decide
  have hz : (controlPenalty savedCref uniformQuoteError unitRoleUnused .next) adverseNextS12Before [] (.query 2) = (nextNormalPenalty adverseNextS12Before) := by
    simpa only [adverseNextS12Before,nextNormalPenalty] using AgentUCTNextExact.adverse_next_normal_root_quotes_exact 11 (by omega) 2 (by decide)
  unfold indexScore
  rw [hs,hp,hn,hz]
  simp only [BackupStat.mean]
  norm_num

theorem adverseNextS12D0I3 : indexScore (7/5) (controlPenalty savedCref uniformQuoteError unitRoleUnused .next) adverseNextS12Before [] (.query 3) = treeIndex ((0/1)/1) (7/5) (nextNormalPenalty adverseNextS12Before) 11 1 := by
  have hs : replayBackup adverseNextS12Before emptyStatistics ([]++[.query 3]) = ⟨1,(0/1)⟩ := by
    rw [replayBackup_empty_closed_form]
    simp +decide [backedEvents,adverseNextS12Before,adverseNextProposal,adverseNextEvent1,adverseNextEvent2,adverseNextEvent3,adverseNextEvent4,adverseNextEvent5,adverseNextEvent6,adverseNextEvent7,adverseNextEvent8,adverseNextEvent9,adverseNextEvent10,adverseNextEvent11,taskReward]
    <;> norm_num
  have hp : rawVisits adverseNextS12Before [] = 11 := by decide
  have hn : rawVisits adverseNextS12Before ([]++[.query 3]) = 1 := by decide
  have hz : (controlPenalty savedCref uniformQuoteError unitRoleUnused .next) adverseNextS12Before [] (.query 3) = (nextNormalPenalty adverseNextS12Before) := by
    simpa only [adverseNextS12Before,nextNormalPenalty] using AgentUCTNextExact.adverse_next_normal_root_quotes_exact 11 (by omega) 3 (by decide)
  unfold indexScore
  rw [hs,hp,hn,hz]
  simp only [BackupStat.mean]
  norm_num

theorem adverseNextS12D0I4 : indexScore (7/5) (controlPenalty savedCref uniformQuoteError unitRoleUnused .next) adverseNextS12Before [] (.query 4) = treeIndex ((0/1)/1) (7/5) (nextNormalPenalty adverseNextS12Before) 11 1 := by
  have hs : replayBackup adverseNextS12Before emptyStatistics ([]++[.query 4]) = ⟨1,(0/1)⟩ := by
    rw [replayBackup_empty_closed_form]
    simp +decide [backedEvents,adverseNextS12Before,adverseNextProposal,adverseNextEvent1,adverseNextEvent2,adverseNextEvent3,adverseNextEvent4,adverseNextEvent5,adverseNextEvent6,adverseNextEvent7,adverseNextEvent8,adverseNextEvent9,adverseNextEvent10,adverseNextEvent11,taskReward]
    <;> norm_num
  have hp : rawVisits adverseNextS12Before [] = 11 := by decide
  have hn : rawVisits adverseNextS12Before ([]++[.query 4]) = 1 := by decide
  have hz : (controlPenalty savedCref uniformQuoteError unitRoleUnused .next) adverseNextS12Before [] (.query 4) = (nextNormalPenalty adverseNextS12Before) := by
    simpa only [adverseNextS12Before,nextNormalPenalty] using AgentUCTNextExact.adverse_next_normal_root_quotes_exact 11 (by omega) 4 (by decide)
  unfold indexScore
  rw [hs,hp,hn,hz]
  simp only [BackupStat.mean]
  norm_num

theorem adverseNextS12D0I5 : indexScore (7/5) (controlPenalty savedCref uniformQuoteError unitRoleUnused .next) adverseNextS12Before [] (.query 5) = treeIndex ((9/10)/2) (7/5) (nextNormalPenalty adverseNextS12Before) 11 2 := by
  have hs : replayBackup adverseNextS12Before emptyStatistics ([]++[.query 5]) = ⟨2,(9/10)⟩ := by
    rw [replayBackup_empty_closed_form]
    simp +decide [backedEvents,adverseNextS12Before,adverseNextProposal,adverseNextEvent1,adverseNextEvent2,adverseNextEvent3,adverseNextEvent4,adverseNextEvent5,adverseNextEvent6,adverseNextEvent7,adverseNextEvent8,adverseNextEvent9,adverseNextEvent10,adverseNextEvent11,taskReward]
    <;> norm_num
  have hp : rawVisits adverseNextS12Before [] = 11 := by decide
  have hn : rawVisits adverseNextS12Before ([]++[.query 5]) = 2 := by decide
  have hz : (controlPenalty savedCref uniformQuoteError unitRoleUnused .next) adverseNextS12Before [] (.query 5) = (nextNormalPenalty adverseNextS12Before) := by
    simpa only [adverseNextS12Before,nextNormalPenalty] using AgentUCTNextExact.adverse_next_normal_root_quotes_exact 11 (by omega) 5 (by decide)
  unfold indexScore
  rw [hs,hp,hn,hz]
  simp only [BackupStat.mean]
  norm_num

theorem adverseNextS12D0I6 : indexScore (7/5) (controlPenalty savedCref uniformQuoteError unitRoleUnused .next) adverseNextS12Before [] (.query 6) = treeIndex ((0/1)/1) (7/5) (nextNormalPenalty adverseNextS12Before) 11 1 := by
  have hs : replayBackup adverseNextS12Before emptyStatistics ([]++[.query 6]) = ⟨1,(0/1)⟩ := by
    rw [replayBackup_empty_closed_form]
    simp +decide [backedEvents,adverseNextS12Before,adverseNextProposal,adverseNextEvent1,adverseNextEvent2,adverseNextEvent3,adverseNextEvent4,adverseNextEvent5,adverseNextEvent6,adverseNextEvent7,adverseNextEvent8,adverseNextEvent9,adverseNextEvent10,adverseNextEvent11,taskReward]
    <;> norm_num
  have hp : rawVisits adverseNextS12Before [] = 11 := by decide
  have hn : rawVisits adverseNextS12Before ([]++[.query 6]) = 1 := by decide
  have hz : (controlPenalty savedCref uniformQuoteError unitRoleUnused .next) adverseNextS12Before [] (.query 6) = (nextNormalPenalty adverseNextS12Before) := by
    simpa only [adverseNextS12Before,nextNormalPenalty] using AgentUCTNextExact.adverse_next_normal_root_quotes_exact 11 (by omega) 6 (by decide)
  unfold indexScore
  rw [hs,hp,hn,hz]
  simp only [BackupStat.mean]
  norm_num

theorem adverseNextS12D0I7 : indexScore (7/5) (controlPenalty savedCref uniformQuoteError unitRoleUnused .next) adverseNextS12Before [] (.query 7) = treeIndex ((0/1)/1) (7/5) (nextNormalPenalty adverseNextS12Before) 11 1 := by
  have hs : replayBackup adverseNextS12Before emptyStatistics ([]++[.query 7]) = ⟨1,(0/1)⟩ := by
    rw [replayBackup_empty_closed_form]
    simp +decide [backedEvents,adverseNextS12Before,adverseNextProposal,adverseNextEvent1,adverseNextEvent2,adverseNextEvent3,adverseNextEvent4,adverseNextEvent5,adverseNextEvent6,adverseNextEvent7,adverseNextEvent8,adverseNextEvent9,adverseNextEvent10,adverseNextEvent11,taskReward]
    <;> norm_num
  have hp : rawVisits adverseNextS12Before [] = 11 := by decide
  have hn : rawVisits adverseNextS12Before ([]++[.query 7]) = 1 := by decide
  have hz : (controlPenalty savedCref uniformQuoteError unitRoleUnused .next) adverseNextS12Before [] (.query 7) = (nextNormalPenalty adverseNextS12Before) := by
    simpa only [adverseNextS12Before,nextNormalPenalty] using AgentUCTNextExact.adverse_next_normal_root_quotes_exact 11 (by omega) 7 (by decide)
  unfold indexScore
  rw [hs,hp,hn,hz]
  simp only [BackupStat.mean]
  norm_num

theorem adverseNextS12D0Cmp0 : indexScore (7/5) (controlPenalty savedCref uniformQuoteError unitRoleUnused .next) adverseNextS12Before [] (.query 0) < indexScore (7/5) (controlPenalty savedCref uniformQuoteError unitRoleUnused .next) adverseNextS12Before [] (.query 2) := by
  rw [adverseNextS12D0I0,adverseNextS12D0I2]
  have hk := adverse_next_penalty_interval 11 (by omega)
  change nextNormalPenaltyLower ≤ nextNormalPenalty adverseNextS12Before ∧ nextNormalPenalty adverseNextS12Before ≤ nextNormalPenaltyUpper at hk
  have hm : ((0/1)/2)+(3901289/2500000)-(nextNormalPenalty adverseNextS12Before) < ((0/1)/1)+(55172551/25000000)-(nextNormalPenalty adverseNextS12Before) := by
    have h : (((0/1)/2)+(3901289/2500000) : ℝ) < ((0/1)/1)+(55172551/25000000) := by norm_num
    linarith
  have h := index_strict_order_from_intervals ((0/1)/1) ((0/1)/2) (nextNormalPenalty adverseNextS12Before) (nextNormalPenalty adverseNextS12Before) (55172551/25000000) (3901289/2500000)
    (treeBonus (7/5) 11 1) (treeBonus (7/5) 11 2)
    (trajectory_bonus_11_1).1 (trajectory_bonus_11_2).2 hm
  simpa only [treeIndex] using h

theorem adverseNextS12D0Cmp1 : indexScore (7/5) (controlPenalty savedCref uniformQuoteError unitRoleUnused .next) adverseNextS12Before [] (.query 1) < indexScore (7/5) (controlPenalty savedCref uniformQuoteError unitRoleUnused .next) adverseNextS12Before [] (.query 2) := by
  rw [adverseNextS12D0I1,adverseNextS12D0I2]
  have hk := adverse_next_penalty_interval 11 (by omega)
  change nextNormalPenaltyLower ≤ nextNormalPenalty adverseNextS12Before ∧ nextNormalPenalty adverseNextS12Before ≤ nextNormalPenaltyUpper at hk
  have hm : ((0/1)/2)+(3901289/2500000)-0 < ((0/1)/1)+(55172551/25000000)-(nextNormalPenalty adverseNextS12Before) := by
    have h : ((0/1)/2)+(3901289/2500000) < ((0/1)/1)+(55172551/25000000)-nextNormalPenaltyUpper := by norm_num [nextNormalPenaltyUpper,savedCref,uniformQuoteError]
    linarith [hk.2]
  have h := index_strict_order_from_intervals ((0/1)/1) ((0/1)/2) (nextNormalPenalty adverseNextS12Before) 0 (55172551/25000000) (3901289/2500000)
    (treeBonus (7/5) 11 1) (treeBonus (7/5) 11 2)
    (trajectory_bonus_11_1).1 (trajectory_bonus_11_2).2 hm
  simpa only [treeIndex] using h

theorem adverseNextS12D0Cmp3 : indexScore (7/5) (controlPenalty savedCref uniformQuoteError unitRoleUnused .next) adverseNextS12Before [] (.query 3) ≤ indexScore (7/5) (controlPenalty savedCref uniformQuoteError unitRoleUnused .next) adverseNextS12Before [] (.query 2) := by
  rw [adverseNextS12D0I3,adverseNextS12D0I2]

theorem adverseNextS12D0Cmp4 : indexScore (7/5) (controlPenalty savedCref uniformQuoteError unitRoleUnused .next) adverseNextS12Before [] (.query 4) ≤ indexScore (7/5) (controlPenalty savedCref uniformQuoteError unitRoleUnused .next) adverseNextS12Before [] (.query 2) := by
  rw [adverseNextS12D0I4,adverseNextS12D0I2]

theorem adverseNextS12D0Cmp5 : indexScore (7/5) (controlPenalty savedCref uniformQuoteError unitRoleUnused .next) adverseNextS12Before [] (.query 5) ≤ indexScore (7/5) (controlPenalty savedCref uniformQuoteError unitRoleUnused .next) adverseNextS12Before [] (.query 2) := by
  rw [adverseNextS12D0I5,adverseNextS12D0I2]
  have hk := adverse_next_penalty_interval 11 (by omega)
  change nextNormalPenaltyLower ≤ nextNormalPenalty adverseNextS12Before ∧ nextNormalPenalty adverseNextS12Before ≤ nextNormalPenaltyUpper at hk
  have hm : ((9/10)/2)+(3901289/2500000)-(nextNormalPenalty adverseNextS12Before) < ((0/1)/1)+(55172551/25000000)-(nextNormalPenalty adverseNextS12Before) := by
    have h : (((9/10)/2)+(3901289/2500000) : ℝ) < ((0/1)/1)+(55172551/25000000) := by norm_num
    linarith
  have h := index_weak_order_from_intervals ((0/1)/1) ((9/10)/2) (nextNormalPenalty adverseNextS12Before) (nextNormalPenalty adverseNextS12Before) (55172551/25000000) (3901289/2500000)
    (treeBonus (7/5) 11 1) (treeBonus (7/5) 11 2)
    (trajectory_bonus_11_1).1 (trajectory_bonus_11_2).2 hm.le
  simpa only [treeIndex] using h

theorem adverseNextS12D0Cmp6 : indexScore (7/5) (controlPenalty savedCref uniformQuoteError unitRoleUnused .next) adverseNextS12Before [] (.query 6) ≤ indexScore (7/5) (controlPenalty savedCref uniformQuoteError unitRoleUnused .next) adverseNextS12Before [] (.query 2) := by
  rw [adverseNextS12D0I6,adverseNextS12D0I2]

theorem adverseNextS12D0Cmp7 : indexScore (7/5) (controlPenalty savedCref uniformQuoteError unitRoleUnused .next) adverseNextS12Before [] (.query 7) ≤ indexScore (7/5) (controlPenalty savedCref uniformQuoteError unitRoleUnused .next) adverseNextS12Before [] (.query 2) := by
  rw [adverseNextS12D0I7,adverseNextS12D0I2]

theorem adverseNextS12Choice0 : nativeFirstChoice (indexScore (7/5) (controlPenalty savedCref uniformQuoteError unitRoleUnused .next) adverseNextS12Before []) adverseNextS12Before [] = .query 2 := by
  apply visited_choice_from_ordered_certificate _ _ [] [.query 0,.query 1] [.query 3,.query 4,.query 5,.query 6,.query 7] (.query 2) (by decide)
  · intro a ha
    have ho : orderedLegalAvailable [] = [.query 0,.query 1,.query 2,.query 3,.query 4,.query 5,.query 6,.query 7] := by decide
    rw [ho] at ha
    simp only [List.mem_cons,List.not_mem_nil,or_false] at ha
    rcases ha with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> decide
  · intro a ha
    simp only [List.mem_cons,List.not_mem_nil,or_false] at ha
    rcases ha with rfl | rfl
    · exact adverseNextS12D0Cmp0
    · exact adverseNextS12D0Cmp1
  · intro a ha
    simp only [List.mem_cons,List.not_mem_nil,or_false] at ha
    rcases ha with rfl | rfl | rfl | rfl | rfl
    · exact adverseNextS12D0Cmp3
    · exact adverseNextS12D0Cmp4
    · exact adverseNextS12D0Cmp5
    · exact adverseNextS12D0Cmp6
    · exact adverseNextS12D0Cmp7

theorem adverseNextS12ActualEvent : nativeEvent budgetTape (7/5) (controlPenalty savedCref uniformQuoteError unitRoleUnused .next)
    (taskReward true (2/5) (1/2)) adverseNextS12Before = adverseNextEvent12 := by
  have hs0 := native_select_existing_step budgetTape (7/5) (controlPenalty savedCref uniformQuoteError unitRoleUnused .next) adverseNextS12Before 8 [] (.query 2)
    (by decide) (by decide) adverseNextS12Choice0
  have hnew := native_select_new_step budgetTape (7/5) (controlPenalty savedCref uniformQuoteError unitRoleUnused .next) adverseNextS12Before 7 [.query 2]
    [.normalRetriever 4,.normalRetriever 6,.normalRetriever 7,.normalRetriever 8,.normalRetriever 5,.normalRetriever 0,.normalRetriever 1,.normalRetriever 2,.normalRetriever 3,.normalRetriever 12,.normalRetriever 14,.normalRetriever 13,.normalRetriever 21,.normalRetriever 23,.normalRetriever 22,.normalRetriever 9,.normalRetriever 11,.normalRetriever 10,.normalRetriever 15,.normalRetriever 17,.normalRetriever 16,.normalRetriever 18,.normalRetriever 20,.normalRetriever 19,.normalRetriever 24,.normalRetriever 25,.normalRetriever 26,.normalRetriever 27,.normalRetriever 28,.normalRetriever 29] (.normalRetriever 0) (by decide) (by decide) (by decide) (by decide)
  have hs : nativeSelect budgetTape (7/5) (controlPenalty savedCref uniformQuoteError unitRoleUnused .next) adverseNextS12Before 9 [] = [.query 2,.normalRetriever 0] := by
    rw [hs0]
    change nativeSelect budgetTape (7/5) (controlPenalty savedCref uniformQuoteError unitRoleUnused .next) adverseNextS12Before 8 [.query 2] = _
    rw [hnew] <;> rfl
  have hr : repairedRollout budgetTape adverseNextS12Before 9 [.query 2,.normalRetriever 0] = [.query 2,.normalRetriever 0,.selection 0,.width 0,.stop,.reranker 0,.topm 0,.context 0,.answer 0] := by decide
  simp only [nativeEvent,hs,hr]
  rfl

def adverseNextS13Before := adverseNextProposal.take 12

theorem adverseNextS13D0I0 : indexScore (7/5) (controlPenalty savedCref uniformQuoteError unitRoleUnused .next) adverseNextS13Before [] (.query 0) = treeIndex ((0/1)/2) (7/5) (nextNormalPenalty adverseNextS13Before) 12 2 := by
  have hs : replayBackup adverseNextS13Before emptyStatistics ([]++[.query 0]) = ⟨2,(0/1)⟩ := by
    rw [replayBackup_empty_closed_form]
    simp +decide [backedEvents,adverseNextS13Before,adverseNextProposal,adverseNextEvent1,adverseNextEvent2,adverseNextEvent3,adverseNextEvent4,adverseNextEvent5,adverseNextEvent6,adverseNextEvent7,adverseNextEvent8,adverseNextEvent9,adverseNextEvent10,adverseNextEvent11,adverseNextEvent12,taskReward]
    <;> norm_num
  have hp : rawVisits adverseNextS13Before [] = 12 := by decide
  have hn : rawVisits adverseNextS13Before ([]++[.query 0]) = 2 := by decide
  have hz : (controlPenalty savedCref uniformQuoteError unitRoleUnused .next) adverseNextS13Before [] (.query 0) = (nextNormalPenalty adverseNextS13Before) := by
    simpa only [adverseNextS13Before,nextNormalPenalty] using AgentUCTNextExact.adverse_next_normal_root_quotes_exact 12 (by omega) 0 (by decide)
  unfold indexScore
  rw [hs,hp,hn,hz]
  simp only [BackupStat.mean]
  norm_num

theorem adverseNextS13D0I1 : indexScore (7/5) (controlPenalty savedCref uniformQuoteError unitRoleUnused .next) adverseNextS13Before [] (.query 1) = treeIndex ((0/1)/2) (7/5) 0 12 2 := by
  have hs : replayBackup adverseNextS13Before emptyStatistics ([]++[.query 1]) = ⟨2,(0/1)⟩ := by
    rw [replayBackup_empty_closed_form]
    simp +decide [backedEvents,adverseNextS13Before,adverseNextProposal,adverseNextEvent1,adverseNextEvent2,adverseNextEvent3,adverseNextEvent4,adverseNextEvent5,adverseNextEvent6,adverseNextEvent7,adverseNextEvent8,adverseNextEvent9,adverseNextEvent10,adverseNextEvent11,adverseNextEvent12,taskReward]
    <;> norm_num
  have hp : rawVisits adverseNextS13Before [] = 12 := by decide
  have hn : rawVisits adverseNextS13Before ([]++[.query 1]) = 2 := by decide
  have hz : (controlPenalty savedCref uniformQuoteError unitRoleUnused .next) adverseNextS13Before [] (.query 1) = 0 := by
    apply control_penalty_empty_suffix
    exact AgentUCTNextExact.adverse_next_hyde_root_suffix_empty 12 (by omega)
  unfold indexScore
  rw [hs,hp,hn,hz]
  simp only [BackupStat.mean]
  norm_num

theorem adverseNextS13D0I2 : indexScore (7/5) (controlPenalty savedCref uniformQuoteError unitRoleUnused .next) adverseNextS13Before [] (.query 2) = treeIndex ((0/1)/2) (7/5) (nextNormalPenalty adverseNextS13Before) 12 2 := by
  have hs : replayBackup adverseNextS13Before emptyStatistics ([]++[.query 2]) = ⟨2,(0/1)⟩ := by
    rw [replayBackup_empty_closed_form]
    simp +decide [backedEvents,adverseNextS13Before,adverseNextProposal,adverseNextEvent1,adverseNextEvent2,adverseNextEvent3,adverseNextEvent4,adverseNextEvent5,adverseNextEvent6,adverseNextEvent7,adverseNextEvent8,adverseNextEvent9,adverseNextEvent10,adverseNextEvent11,adverseNextEvent12,taskReward]
    <;> norm_num
  have hp : rawVisits adverseNextS13Before [] = 12 := by decide
  have hn : rawVisits adverseNextS13Before ([]++[.query 2]) = 2 := by decide
  have hz : (controlPenalty savedCref uniformQuoteError unitRoleUnused .next) adverseNextS13Before [] (.query 2) = (nextNormalPenalty adverseNextS13Before) := by
    simpa only [adverseNextS13Before,nextNormalPenalty] using AgentUCTNextExact.adverse_next_normal_root_quotes_exact 12 (by omega) 2 (by decide)
  unfold indexScore
  rw [hs,hp,hn,hz]
  simp only [BackupStat.mean]
  norm_num

theorem adverseNextS13D0I3 : indexScore (7/5) (controlPenalty savedCref uniformQuoteError unitRoleUnused .next) adverseNextS13Before [] (.query 3) = treeIndex ((0/1)/1) (7/5) (nextNormalPenalty adverseNextS13Before) 12 1 := by
  have hs : replayBackup adverseNextS13Before emptyStatistics ([]++[.query 3]) = ⟨1,(0/1)⟩ := by
    rw [replayBackup_empty_closed_form]
    simp +decide [backedEvents,adverseNextS13Before,adverseNextProposal,adverseNextEvent1,adverseNextEvent2,adverseNextEvent3,adverseNextEvent4,adverseNextEvent5,adverseNextEvent6,adverseNextEvent7,adverseNextEvent8,adverseNextEvent9,adverseNextEvent10,adverseNextEvent11,adverseNextEvent12,taskReward]
    <;> norm_num
  have hp : rawVisits adverseNextS13Before [] = 12 := by decide
  have hn : rawVisits adverseNextS13Before ([]++[.query 3]) = 1 := by decide
  have hz : (controlPenalty savedCref uniformQuoteError unitRoleUnused .next) adverseNextS13Before [] (.query 3) = (nextNormalPenalty adverseNextS13Before) := by
    simpa only [adverseNextS13Before,nextNormalPenalty] using AgentUCTNextExact.adverse_next_normal_root_quotes_exact 12 (by omega) 3 (by decide)
  unfold indexScore
  rw [hs,hp,hn,hz]
  simp only [BackupStat.mean]
  norm_num

theorem adverseNextS13D0I4 : indexScore (7/5) (controlPenalty savedCref uniformQuoteError unitRoleUnused .next) adverseNextS13Before [] (.query 4) = treeIndex ((0/1)/1) (7/5) (nextNormalPenalty adverseNextS13Before) 12 1 := by
  have hs : replayBackup adverseNextS13Before emptyStatistics ([]++[.query 4]) = ⟨1,(0/1)⟩ := by
    rw [replayBackup_empty_closed_form]
    simp +decide [backedEvents,adverseNextS13Before,adverseNextProposal,adverseNextEvent1,adverseNextEvent2,adverseNextEvent3,adverseNextEvent4,adverseNextEvent5,adverseNextEvent6,adverseNextEvent7,adverseNextEvent8,adverseNextEvent9,adverseNextEvent10,adverseNextEvent11,adverseNextEvent12,taskReward]
    <;> norm_num
  have hp : rawVisits adverseNextS13Before [] = 12 := by decide
  have hn : rawVisits adverseNextS13Before ([]++[.query 4]) = 1 := by decide
  have hz : (controlPenalty savedCref uniformQuoteError unitRoleUnused .next) adverseNextS13Before [] (.query 4) = (nextNormalPenalty adverseNextS13Before) := by
    simpa only [adverseNextS13Before,nextNormalPenalty] using AgentUCTNextExact.adverse_next_normal_root_quotes_exact 12 (by omega) 4 (by decide)
  unfold indexScore
  rw [hs,hp,hn,hz]
  simp only [BackupStat.mean]
  norm_num

theorem adverseNextS13D0I5 : indexScore (7/5) (controlPenalty savedCref uniformQuoteError unitRoleUnused .next) adverseNextS13Before [] (.query 5) = treeIndex ((9/10)/2) (7/5) (nextNormalPenalty adverseNextS13Before) 12 2 := by
  have hs : replayBackup adverseNextS13Before emptyStatistics ([]++[.query 5]) = ⟨2,(9/10)⟩ := by
    rw [replayBackup_empty_closed_form]
    simp +decide [backedEvents,adverseNextS13Before,adverseNextProposal,adverseNextEvent1,adverseNextEvent2,adverseNextEvent3,adverseNextEvent4,adverseNextEvent5,adverseNextEvent6,adverseNextEvent7,adverseNextEvent8,adverseNextEvent9,adverseNextEvent10,adverseNextEvent11,adverseNextEvent12,taskReward]
    <;> norm_num
  have hp : rawVisits adverseNextS13Before [] = 12 := by decide
  have hn : rawVisits adverseNextS13Before ([]++[.query 5]) = 2 := by decide
  have hz : (controlPenalty savedCref uniformQuoteError unitRoleUnused .next) adverseNextS13Before [] (.query 5) = (nextNormalPenalty adverseNextS13Before) := by
    simpa only [adverseNextS13Before,nextNormalPenalty] using AgentUCTNextExact.adverse_next_normal_root_quotes_exact 12 (by omega) 5 (by decide)
  unfold indexScore
  rw [hs,hp,hn,hz]
  simp only [BackupStat.mean]
  norm_num

theorem adverseNextS13D0I6 : indexScore (7/5) (controlPenalty savedCref uniformQuoteError unitRoleUnused .next) adverseNextS13Before [] (.query 6) = treeIndex ((0/1)/1) (7/5) (nextNormalPenalty adverseNextS13Before) 12 1 := by
  have hs : replayBackup adverseNextS13Before emptyStatistics ([]++[.query 6]) = ⟨1,(0/1)⟩ := by
    rw [replayBackup_empty_closed_form]
    simp +decide [backedEvents,adverseNextS13Before,adverseNextProposal,adverseNextEvent1,adverseNextEvent2,adverseNextEvent3,adverseNextEvent4,adverseNextEvent5,adverseNextEvent6,adverseNextEvent7,adverseNextEvent8,adverseNextEvent9,adverseNextEvent10,adverseNextEvent11,adverseNextEvent12,taskReward]
    <;> norm_num
  have hp : rawVisits adverseNextS13Before [] = 12 := by decide
  have hn : rawVisits adverseNextS13Before ([]++[.query 6]) = 1 := by decide
  have hz : (controlPenalty savedCref uniformQuoteError unitRoleUnused .next) adverseNextS13Before [] (.query 6) = (nextNormalPenalty adverseNextS13Before) := by
    simpa only [adverseNextS13Before,nextNormalPenalty] using AgentUCTNextExact.adverse_next_normal_root_quotes_exact 12 (by omega) 6 (by decide)
  unfold indexScore
  rw [hs,hp,hn,hz]
  simp only [BackupStat.mean]
  norm_num

theorem adverseNextS13D0I7 : indexScore (7/5) (controlPenalty savedCref uniformQuoteError unitRoleUnused .next) adverseNextS13Before [] (.query 7) = treeIndex ((0/1)/1) (7/5) (nextNormalPenalty adverseNextS13Before) 12 1 := by
  have hs : replayBackup adverseNextS13Before emptyStatistics ([]++[.query 7]) = ⟨1,(0/1)⟩ := by
    rw [replayBackup_empty_closed_form]
    simp +decide [backedEvents,adverseNextS13Before,adverseNextProposal,adverseNextEvent1,adverseNextEvent2,adverseNextEvent3,adverseNextEvent4,adverseNextEvent5,adverseNextEvent6,adverseNextEvent7,adverseNextEvent8,adverseNextEvent9,adverseNextEvent10,adverseNextEvent11,adverseNextEvent12,taskReward]
    <;> norm_num
  have hp : rawVisits adverseNextS13Before [] = 12 := by decide
  have hn : rawVisits adverseNextS13Before ([]++[.query 7]) = 1 := by decide
  have hz : (controlPenalty savedCref uniformQuoteError unitRoleUnused .next) adverseNextS13Before [] (.query 7) = (nextNormalPenalty adverseNextS13Before) := by
    simpa only [adverseNextS13Before,nextNormalPenalty] using AgentUCTNextExact.adverse_next_normal_root_quotes_exact 12 (by omega) 7 (by decide)
  unfold indexScore
  rw [hs,hp,hn,hz]
  simp only [BackupStat.mean]
  norm_num

theorem adverseNextS13D0Cmp0 : indexScore (7/5) (controlPenalty savedCref uniformQuoteError unitRoleUnused .next) adverseNextS13Before [] (.query 0) < indexScore (7/5) (controlPenalty savedCref uniformQuoteError unitRoleUnused .next) adverseNextS13Before [] (.query 3) := by
  rw [adverseNextS13D0I0,adverseNextS13D0I3]
  have hk := adverse_next_penalty_interval 12 (by omega)
  change nextNormalPenaltyLower ≤ nextNormalPenalty adverseNextS13Before ∧ nextNormalPenalty adverseNextS13Before ≤ nextNormalPenaltyUpper at hk
  have hm : ((0/1)/2)+(495453/312500)-(nextNormalPenalty adverseNextS13Before) < ((0/1)/1)+(112108213/50000000)-(nextNormalPenalty adverseNextS13Before) := by
    have h : (((0/1)/2)+(495453/312500) : ℝ) < ((0/1)/1)+(112108213/50000000) := by norm_num
    linarith
  have h := index_strict_order_from_intervals ((0/1)/1) ((0/1)/2) (nextNormalPenalty adverseNextS13Before) (nextNormalPenalty adverseNextS13Before) (112108213/50000000) (495453/312500)
    (treeBonus (7/5) 12 1) (treeBonus (7/5) 12 2)
    (trajectory_bonus_12_1).1 (trajectory_bonus_12_2).2 hm
  simpa only [treeIndex] using h

theorem adverseNextS13D0Cmp1 : indexScore (7/5) (controlPenalty savedCref uniformQuoteError unitRoleUnused .next) adverseNextS13Before [] (.query 1) < indexScore (7/5) (controlPenalty savedCref uniformQuoteError unitRoleUnused .next) adverseNextS13Before [] (.query 3) := by
  rw [adverseNextS13D0I1,adverseNextS13D0I3]
  have hk := adverse_next_penalty_interval 12 (by omega)
  change nextNormalPenaltyLower ≤ nextNormalPenalty adverseNextS13Before ∧ nextNormalPenalty adverseNextS13Before ≤ nextNormalPenaltyUpper at hk
  have hm : ((0/1)/2)+(495453/312500)-0 < ((0/1)/1)+(112108213/50000000)-(nextNormalPenalty adverseNextS13Before) := by
    have h : ((0/1)/2)+(495453/312500) < ((0/1)/1)+(112108213/50000000)-nextNormalPenaltyUpper := by norm_num [nextNormalPenaltyUpper,savedCref,uniformQuoteError]
    linarith [hk.2]
  have h := index_strict_order_from_intervals ((0/1)/1) ((0/1)/2) (nextNormalPenalty adverseNextS13Before) 0 (112108213/50000000) (495453/312500)
    (treeBonus (7/5) 12 1) (treeBonus (7/5) 12 2)
    (trajectory_bonus_12_1).1 (trajectory_bonus_12_2).2 hm
  simpa only [treeIndex] using h

theorem adverseNextS13D0Cmp2 : indexScore (7/5) (controlPenalty savedCref uniformQuoteError unitRoleUnused .next) adverseNextS13Before [] (.query 2) < indexScore (7/5) (controlPenalty savedCref uniformQuoteError unitRoleUnused .next) adverseNextS13Before [] (.query 3) := by
  rw [adverseNextS13D0I2,adverseNextS13D0I3]
  have hk := adverse_next_penalty_interval 12 (by omega)
  change nextNormalPenaltyLower ≤ nextNormalPenalty adverseNextS13Before ∧ nextNormalPenalty adverseNextS13Before ≤ nextNormalPenaltyUpper at hk
  have hm : ((0/1)/2)+(495453/312500)-(nextNormalPenalty adverseNextS13Before) < ((0/1)/1)+(112108213/50000000)-(nextNormalPenalty adverseNextS13Before) := by
    have h : (((0/1)/2)+(495453/312500) : ℝ) < ((0/1)/1)+(112108213/50000000) := by norm_num
    linarith
  have h := index_strict_order_from_intervals ((0/1)/1) ((0/1)/2) (nextNormalPenalty adverseNextS13Before) (nextNormalPenalty adverseNextS13Before) (112108213/50000000) (495453/312500)
    (treeBonus (7/5) 12 1) (treeBonus (7/5) 12 2)
    (trajectory_bonus_12_1).1 (trajectory_bonus_12_2).2 hm
  simpa only [treeIndex] using h

theorem adverseNextS13D0Cmp4 : indexScore (7/5) (controlPenalty savedCref uniformQuoteError unitRoleUnused .next) adverseNextS13Before [] (.query 4) ≤ indexScore (7/5) (controlPenalty savedCref uniformQuoteError unitRoleUnused .next) adverseNextS13Before [] (.query 3) := by
  rw [adverseNextS13D0I4,adverseNextS13D0I3]

theorem adverseNextS13D0Cmp5 : indexScore (7/5) (controlPenalty savedCref uniformQuoteError unitRoleUnused .next) adverseNextS13Before [] (.query 5) ≤ indexScore (7/5) (controlPenalty savedCref uniformQuoteError unitRoleUnused .next) adverseNextS13Before [] (.query 3) := by
  rw [adverseNextS13D0I5,adverseNextS13D0I3]
  have hk := adverse_next_penalty_interval 12 (by omega)
  change nextNormalPenaltyLower ≤ nextNormalPenalty adverseNextS13Before ∧ nextNormalPenalty adverseNextS13Before ≤ nextNormalPenaltyUpper at hk
  have hm : ((9/10)/2)+(495453/312500)-(nextNormalPenalty adverseNextS13Before) < ((0/1)/1)+(112108213/50000000)-(nextNormalPenalty adverseNextS13Before) := by
    have h : (((9/10)/2)+(495453/312500) : ℝ) < ((0/1)/1)+(112108213/50000000) := by norm_num
    linarith
  have h := index_weak_order_from_intervals ((0/1)/1) ((9/10)/2) (nextNormalPenalty adverseNextS13Before) (nextNormalPenalty adverseNextS13Before) (112108213/50000000) (495453/312500)
    (treeBonus (7/5) 12 1) (treeBonus (7/5) 12 2)
    (trajectory_bonus_12_1).1 (trajectory_bonus_12_2).2 hm.le
  simpa only [treeIndex] using h

theorem adverseNextS13D0Cmp6 : indexScore (7/5) (controlPenalty savedCref uniformQuoteError unitRoleUnused .next) adverseNextS13Before [] (.query 6) ≤ indexScore (7/5) (controlPenalty savedCref uniformQuoteError unitRoleUnused .next) adverseNextS13Before [] (.query 3) := by
  rw [adverseNextS13D0I6,adverseNextS13D0I3]

theorem adverseNextS13D0Cmp7 : indexScore (7/5) (controlPenalty savedCref uniformQuoteError unitRoleUnused .next) adverseNextS13Before [] (.query 7) ≤ indexScore (7/5) (controlPenalty savedCref uniformQuoteError unitRoleUnused .next) adverseNextS13Before [] (.query 3) := by
  rw [adverseNextS13D0I7,adverseNextS13D0I3]

theorem adverseNextS13Choice0 : nativeFirstChoice (indexScore (7/5) (controlPenalty savedCref uniformQuoteError unitRoleUnused .next) adverseNextS13Before []) adverseNextS13Before [] = .query 3 := by
  apply visited_choice_from_ordered_certificate _ _ [] [.query 0,.query 1,.query 2] [.query 4,.query 5,.query 6,.query 7] (.query 3) (by decide)
  · intro a ha
    have ho : orderedLegalAvailable [] = [.query 0,.query 1,.query 2,.query 3,.query 4,.query 5,.query 6,.query 7] := by decide
    rw [ho] at ha
    simp only [List.mem_cons,List.not_mem_nil,or_false] at ha
    rcases ha with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> decide
  · intro a ha
    simp only [List.mem_cons,List.not_mem_nil,or_false] at ha
    rcases ha with rfl | rfl | rfl
    · exact adverseNextS13D0Cmp0
    · exact adverseNextS13D0Cmp1
    · exact adverseNextS13D0Cmp2
  · intro a ha
    simp only [List.mem_cons,List.not_mem_nil,or_false] at ha
    rcases ha with rfl | rfl | rfl | rfl
    · exact adverseNextS13D0Cmp4
    · exact adverseNextS13D0Cmp5
    · exact adverseNextS13D0Cmp6
    · exact adverseNextS13D0Cmp7

theorem adverseNextS13ActualEvent : nativeEvent budgetTape (7/5) (controlPenalty savedCref uniformQuoteError unitRoleUnused .next)
    (taskReward true (2/5) (1/2)) adverseNextS13Before = adverseNextEvent13 := by
  have hs0 := native_select_existing_step budgetTape (7/5) (controlPenalty savedCref uniformQuoteError unitRoleUnused .next) adverseNextS13Before 8 [] (.query 3)
    (by decide) (by decide) adverseNextS13Choice0
  have hnew := native_select_new_step budgetTape (7/5) (controlPenalty savedCref uniformQuoteError unitRoleUnused .next) adverseNextS13Before 7 [.query 3]
    [.normalRetriever 4,.normalRetriever 6,.normalRetriever 7,.normalRetriever 8,.normalRetriever 5,.normalRetriever 0,.normalRetriever 1,.normalRetriever 2,.normalRetriever 3,.normalRetriever 12,.normalRetriever 14,.normalRetriever 13,.normalRetriever 21,.normalRetriever 23,.normalRetriever 22,.normalRetriever 9,.normalRetriever 11,.normalRetriever 10,.normalRetriever 15,.normalRetriever 17,.normalRetriever 16,.normalRetriever 18,.normalRetriever 20,.normalRetriever 19,.normalRetriever 24,.normalRetriever 25,.normalRetriever 26,.normalRetriever 27,.normalRetriever 28,.normalRetriever 29] (.normalRetriever 0) (by decide) (by decide) (by decide) (by decide)
  have hs : nativeSelect budgetTape (7/5) (controlPenalty savedCref uniformQuoteError unitRoleUnused .next) adverseNextS13Before 9 [] = [.query 3,.normalRetriever 0] := by
    rw [hs0]
    change nativeSelect budgetTape (7/5) (controlPenalty savedCref uniformQuoteError unitRoleUnused .next) adverseNextS13Before 8 [.query 3] = _
    rw [hnew] <;> rfl
  have hr : repairedRollout budgetTape adverseNextS13Before 9 [.query 3,.normalRetriever 0] = [.query 3,.normalRetriever 0,.selection 0,.width 0,.stop,.reranker 0,.topm 0,.context 0,.answer 0] := by decide
  simp only [nativeEvent,hs,hr]
  rfl

def adverseNextS14Before := adverseNextProposal.take 13

theorem adverseNextS14D0I0 : indexScore (7/5) (controlPenalty savedCref uniformQuoteError unitRoleUnused .next) adverseNextS14Before [] (.query 0) = treeIndex ((0/1)/2) (7/5) (nextNormalPenalty adverseNextS14Before) 13 2 := by
  have hs : replayBackup adverseNextS14Before emptyStatistics ([]++[.query 0]) = ⟨2,(0/1)⟩ := by
    rw [replayBackup_empty_closed_form]
    simp +decide [backedEvents,adverseNextS14Before,adverseNextProposal,adverseNextEvent1,adverseNextEvent2,adverseNextEvent3,adverseNextEvent4,adverseNextEvent5,adverseNextEvent6,adverseNextEvent7,adverseNextEvent8,adverseNextEvent9,adverseNextEvent10,adverseNextEvent11,adverseNextEvent12,adverseNextEvent13,taskReward]
    <;> norm_num
  have hp : rawVisits adverseNextS14Before [] = 13 := by decide
  have hn : rawVisits adverseNextS14Before ([]++[.query 0]) = 2 := by decide
  have hz : (controlPenalty savedCref uniformQuoteError unitRoleUnused .next) adverseNextS14Before [] (.query 0) = (nextNormalPenalty adverseNextS14Before) := by
    simpa only [adverseNextS14Before,nextNormalPenalty] using AgentUCTNextExact.adverse_next_normal_root_quotes_exact 13 (by omega) 0 (by decide)
  unfold indexScore
  rw [hs,hp,hn,hz]
  simp only [BackupStat.mean]
  norm_num

theorem adverseNextS14D0I1 : indexScore (7/5) (controlPenalty savedCref uniformQuoteError unitRoleUnused .next) adverseNextS14Before [] (.query 1) = treeIndex ((0/1)/2) (7/5) 0 13 2 := by
  have hs : replayBackup adverseNextS14Before emptyStatistics ([]++[.query 1]) = ⟨2,(0/1)⟩ := by
    rw [replayBackup_empty_closed_form]
    simp +decide [backedEvents,adverseNextS14Before,adverseNextProposal,adverseNextEvent1,adverseNextEvent2,adverseNextEvent3,adverseNextEvent4,adverseNextEvent5,adverseNextEvent6,adverseNextEvent7,adverseNextEvent8,adverseNextEvent9,adverseNextEvent10,adverseNextEvent11,adverseNextEvent12,adverseNextEvent13,taskReward]
    <;> norm_num
  have hp : rawVisits adverseNextS14Before [] = 13 := by decide
  have hn : rawVisits adverseNextS14Before ([]++[.query 1]) = 2 := by decide
  have hz : (controlPenalty savedCref uniformQuoteError unitRoleUnused .next) adverseNextS14Before [] (.query 1) = 0 := by
    apply control_penalty_empty_suffix
    exact AgentUCTNextExact.adverse_next_hyde_root_suffix_empty 13 (by omega)
  unfold indexScore
  rw [hs,hp,hn,hz]
  simp only [BackupStat.mean]
  norm_num

theorem adverseNextS14D0I2 : indexScore (7/5) (controlPenalty savedCref uniformQuoteError unitRoleUnused .next) adverseNextS14Before [] (.query 2) = treeIndex ((0/1)/2) (7/5) (nextNormalPenalty adverseNextS14Before) 13 2 := by
  have hs : replayBackup adverseNextS14Before emptyStatistics ([]++[.query 2]) = ⟨2,(0/1)⟩ := by
    rw [replayBackup_empty_closed_form]
    simp +decide [backedEvents,adverseNextS14Before,adverseNextProposal,adverseNextEvent1,adverseNextEvent2,adverseNextEvent3,adverseNextEvent4,adverseNextEvent5,adverseNextEvent6,adverseNextEvent7,adverseNextEvent8,adverseNextEvent9,adverseNextEvent10,adverseNextEvent11,adverseNextEvent12,adverseNextEvent13,taskReward]
    <;> norm_num
  have hp : rawVisits adverseNextS14Before [] = 13 := by decide
  have hn : rawVisits adverseNextS14Before ([]++[.query 2]) = 2 := by decide
  have hz : (controlPenalty savedCref uniformQuoteError unitRoleUnused .next) adverseNextS14Before [] (.query 2) = (nextNormalPenalty adverseNextS14Before) := by
    simpa only [adverseNextS14Before,nextNormalPenalty] using AgentUCTNextExact.adverse_next_normal_root_quotes_exact 13 (by omega) 2 (by decide)
  unfold indexScore
  rw [hs,hp,hn,hz]
  simp only [BackupStat.mean]
  norm_num

theorem adverseNextS14D0I3 : indexScore (7/5) (controlPenalty savedCref uniformQuoteError unitRoleUnused .next) adverseNextS14Before [] (.query 3) = treeIndex ((0/1)/2) (7/5) (nextNormalPenalty adverseNextS14Before) 13 2 := by
  have hs : replayBackup adverseNextS14Before emptyStatistics ([]++[.query 3]) = ⟨2,(0/1)⟩ := by
    rw [replayBackup_empty_closed_form]
    simp +decide [backedEvents,adverseNextS14Before,adverseNextProposal,adverseNextEvent1,adverseNextEvent2,adverseNextEvent3,adverseNextEvent4,adverseNextEvent5,adverseNextEvent6,adverseNextEvent7,adverseNextEvent8,adverseNextEvent9,adverseNextEvent10,adverseNextEvent11,adverseNextEvent12,adverseNextEvent13,taskReward]
    <;> norm_num
  have hp : rawVisits adverseNextS14Before [] = 13 := by decide
  have hn : rawVisits adverseNextS14Before ([]++[.query 3]) = 2 := by decide
  have hz : (controlPenalty savedCref uniformQuoteError unitRoleUnused .next) adverseNextS14Before [] (.query 3) = (nextNormalPenalty adverseNextS14Before) := by
    simpa only [adverseNextS14Before,nextNormalPenalty] using AgentUCTNextExact.adverse_next_normal_root_quotes_exact 13 (by omega) 3 (by decide)
  unfold indexScore
  rw [hs,hp,hn,hz]
  simp only [BackupStat.mean]
  norm_num

theorem adverseNextS14D0I4 : indexScore (7/5) (controlPenalty savedCref uniformQuoteError unitRoleUnused .next) adverseNextS14Before [] (.query 4) = treeIndex ((0/1)/1) (7/5) (nextNormalPenalty adverseNextS14Before) 13 1 := by
  have hs : replayBackup adverseNextS14Before emptyStatistics ([]++[.query 4]) = ⟨1,(0/1)⟩ := by
    rw [replayBackup_empty_closed_form]
    simp +decide [backedEvents,adverseNextS14Before,adverseNextProposal,adverseNextEvent1,adverseNextEvent2,adverseNextEvent3,adverseNextEvent4,adverseNextEvent5,adverseNextEvent6,adverseNextEvent7,adverseNextEvent8,adverseNextEvent9,adverseNextEvent10,adverseNextEvent11,adverseNextEvent12,adverseNextEvent13,taskReward]
    <;> norm_num
  have hp : rawVisits adverseNextS14Before [] = 13 := by decide
  have hn : rawVisits adverseNextS14Before ([]++[.query 4]) = 1 := by decide
  have hz : (controlPenalty savedCref uniformQuoteError unitRoleUnused .next) adverseNextS14Before [] (.query 4) = (nextNormalPenalty adverseNextS14Before) := by
    simpa only [adverseNextS14Before,nextNormalPenalty] using AgentUCTNextExact.adverse_next_normal_root_quotes_exact 13 (by omega) 4 (by decide)
  unfold indexScore
  rw [hs,hp,hn,hz]
  simp only [BackupStat.mean]
  norm_num

theorem adverseNextS14D0I5 : indexScore (7/5) (controlPenalty savedCref uniformQuoteError unitRoleUnused .next) adverseNextS14Before [] (.query 5) = treeIndex ((9/10)/2) (7/5) (nextNormalPenalty adverseNextS14Before) 13 2 := by
  have hs : replayBackup adverseNextS14Before emptyStatistics ([]++[.query 5]) = ⟨2,(9/10)⟩ := by
    rw [replayBackup_empty_closed_form]
    simp +decide [backedEvents,adverseNextS14Before,adverseNextProposal,adverseNextEvent1,adverseNextEvent2,adverseNextEvent3,adverseNextEvent4,adverseNextEvent5,adverseNextEvent6,adverseNextEvent7,adverseNextEvent8,adverseNextEvent9,adverseNextEvent10,adverseNextEvent11,adverseNextEvent12,adverseNextEvent13,taskReward]
    <;> norm_num
  have hp : rawVisits adverseNextS14Before [] = 13 := by decide
  have hn : rawVisits adverseNextS14Before ([]++[.query 5]) = 2 := by decide
  have hz : (controlPenalty savedCref uniformQuoteError unitRoleUnused .next) adverseNextS14Before [] (.query 5) = (nextNormalPenalty adverseNextS14Before) := by
    simpa only [adverseNextS14Before,nextNormalPenalty] using AgentUCTNextExact.adverse_next_normal_root_quotes_exact 13 (by omega) 5 (by decide)
  unfold indexScore
  rw [hs,hp,hn,hz]
  simp only [BackupStat.mean]
  norm_num

theorem adverseNextS14D0I6 : indexScore (7/5) (controlPenalty savedCref uniformQuoteError unitRoleUnused .next) adverseNextS14Before [] (.query 6) = treeIndex ((0/1)/1) (7/5) (nextNormalPenalty adverseNextS14Before) 13 1 := by
  have hs : replayBackup adverseNextS14Before emptyStatistics ([]++[.query 6]) = ⟨1,(0/1)⟩ := by
    rw [replayBackup_empty_closed_form]
    simp +decide [backedEvents,adverseNextS14Before,adverseNextProposal,adverseNextEvent1,adverseNextEvent2,adverseNextEvent3,adverseNextEvent4,adverseNextEvent5,adverseNextEvent6,adverseNextEvent7,adverseNextEvent8,adverseNextEvent9,adverseNextEvent10,adverseNextEvent11,adverseNextEvent12,adverseNextEvent13,taskReward]
    <;> norm_num
  have hp : rawVisits adverseNextS14Before [] = 13 := by decide
  have hn : rawVisits adverseNextS14Before ([]++[.query 6]) = 1 := by decide
  have hz : (controlPenalty savedCref uniformQuoteError unitRoleUnused .next) adverseNextS14Before [] (.query 6) = (nextNormalPenalty adverseNextS14Before) := by
    simpa only [adverseNextS14Before,nextNormalPenalty] using AgentUCTNextExact.adverse_next_normal_root_quotes_exact 13 (by omega) 6 (by decide)
  unfold indexScore
  rw [hs,hp,hn,hz]
  simp only [BackupStat.mean]
  norm_num

theorem adverseNextS14D0I7 : indexScore (7/5) (controlPenalty savedCref uniformQuoteError unitRoleUnused .next) adverseNextS14Before [] (.query 7) = treeIndex ((0/1)/1) (7/5) (nextNormalPenalty adverseNextS14Before) 13 1 := by
  have hs : replayBackup adverseNextS14Before emptyStatistics ([]++[.query 7]) = ⟨1,(0/1)⟩ := by
    rw [replayBackup_empty_closed_form]
    simp +decide [backedEvents,adverseNextS14Before,adverseNextProposal,adverseNextEvent1,adverseNextEvent2,adverseNextEvent3,adverseNextEvent4,adverseNextEvent5,adverseNextEvent6,adverseNextEvent7,adverseNextEvent8,adverseNextEvent9,adverseNextEvent10,adverseNextEvent11,adverseNextEvent12,adverseNextEvent13,taskReward]
    <;> norm_num
  have hp : rawVisits adverseNextS14Before [] = 13 := by decide
  have hn : rawVisits adverseNextS14Before ([]++[.query 7]) = 1 := by decide
  have hz : (controlPenalty savedCref uniformQuoteError unitRoleUnused .next) adverseNextS14Before [] (.query 7) = (nextNormalPenalty adverseNextS14Before) := by
    simpa only [adverseNextS14Before,nextNormalPenalty] using AgentUCTNextExact.adverse_next_normal_root_quotes_exact 13 (by omega) 7 (by decide)
  unfold indexScore
  rw [hs,hp,hn,hz]
  simp only [BackupStat.mean]
  norm_num

theorem adverseNextS14D0Cmp0 : indexScore (7/5) (controlPenalty savedCref uniformQuoteError unitRoleUnused .next) adverseNextS14Before [] (.query 0) < indexScore (7/5) (controlPenalty savedCref uniformQuoteError unitRoleUnused .next) adverseNextS14Before [] (.query 4) := by
  rw [adverseNextS14D0I0,adverseNextS14D0I4]
  have hk := adverse_next_penalty_interval 13 (by omega)
  change nextNormalPenaltyLower ≤ nextNormalPenalty adverseNextS14Before ∧ nextNormalPenalty adverseNextS14Before ≤ nextNormalPenaltyUpper at hk
  have hm : ((0/1)/2)+(3216381/2000000)-(nextNormalPenalty adverseNextS14Before) < ((0/1)/1)+(4548649/2000000)-(nextNormalPenalty adverseNextS14Before) := by
    have h : (((0/1)/2)+(3216381/2000000) : ℝ) < ((0/1)/1)+(4548649/2000000) := by norm_num
    linarith
  have h := index_strict_order_from_intervals ((0/1)/1) ((0/1)/2) (nextNormalPenalty adverseNextS14Before) (nextNormalPenalty adverseNextS14Before) (4548649/2000000) (3216381/2000000)
    (treeBonus (7/5) 13 1) (treeBonus (7/5) 13 2)
    (trajectory_bonus_13_1).1 (trajectory_bonus_13_2).2 hm
  simpa only [treeIndex] using h

theorem adverseNextS14D0Cmp1 : indexScore (7/5) (controlPenalty savedCref uniformQuoteError unitRoleUnused .next) adverseNextS14Before [] (.query 1) < indexScore (7/5) (controlPenalty savedCref uniformQuoteError unitRoleUnused .next) adverseNextS14Before [] (.query 4) := by
  rw [adverseNextS14D0I1,adverseNextS14D0I4]
  have hk := adverse_next_penalty_interval 13 (by omega)
  change nextNormalPenaltyLower ≤ nextNormalPenalty adverseNextS14Before ∧ nextNormalPenalty adverseNextS14Before ≤ nextNormalPenaltyUpper at hk
  have hm : ((0/1)/2)+(3216381/2000000)-0 < ((0/1)/1)+(4548649/2000000)-(nextNormalPenalty adverseNextS14Before) := by
    have h : ((0/1)/2)+(3216381/2000000) < ((0/1)/1)+(4548649/2000000)-nextNormalPenaltyUpper := by norm_num [nextNormalPenaltyUpper,savedCref,uniformQuoteError]
    linarith [hk.2]
  have h := index_strict_order_from_intervals ((0/1)/1) ((0/1)/2) (nextNormalPenalty adverseNextS14Before) 0 (4548649/2000000) (3216381/2000000)
    (treeBonus (7/5) 13 1) (treeBonus (7/5) 13 2)
    (trajectory_bonus_13_1).1 (trajectory_bonus_13_2).2 hm
  simpa only [treeIndex] using h

theorem adverseNextS14D0Cmp2 : indexScore (7/5) (controlPenalty savedCref uniformQuoteError unitRoleUnused .next) adverseNextS14Before [] (.query 2) < indexScore (7/5) (controlPenalty savedCref uniformQuoteError unitRoleUnused .next) adverseNextS14Before [] (.query 4) := by
  rw [adverseNextS14D0I2,adverseNextS14D0I4]
  have hk := adverse_next_penalty_interval 13 (by omega)
  change nextNormalPenaltyLower ≤ nextNormalPenalty adverseNextS14Before ∧ nextNormalPenalty adverseNextS14Before ≤ nextNormalPenaltyUpper at hk
  have hm : ((0/1)/2)+(3216381/2000000)-(nextNormalPenalty adverseNextS14Before) < ((0/1)/1)+(4548649/2000000)-(nextNormalPenalty adverseNextS14Before) := by
    have h : (((0/1)/2)+(3216381/2000000) : ℝ) < ((0/1)/1)+(4548649/2000000) := by norm_num
    linarith
  have h := index_strict_order_from_intervals ((0/1)/1) ((0/1)/2) (nextNormalPenalty adverseNextS14Before) (nextNormalPenalty adverseNextS14Before) (4548649/2000000) (3216381/2000000)
    (treeBonus (7/5) 13 1) (treeBonus (7/5) 13 2)
    (trajectory_bonus_13_1).1 (trajectory_bonus_13_2).2 hm
  simpa only [treeIndex] using h

theorem adverseNextS14D0Cmp3 : indexScore (7/5) (controlPenalty savedCref uniformQuoteError unitRoleUnused .next) adverseNextS14Before [] (.query 3) < indexScore (7/5) (controlPenalty savedCref uniformQuoteError unitRoleUnused .next) adverseNextS14Before [] (.query 4) := by
  rw [adverseNextS14D0I3,adverseNextS14D0I4]
  have hk := adverse_next_penalty_interval 13 (by omega)
  change nextNormalPenaltyLower ≤ nextNormalPenalty adverseNextS14Before ∧ nextNormalPenalty adverseNextS14Before ≤ nextNormalPenaltyUpper at hk
  have hm : ((0/1)/2)+(3216381/2000000)-(nextNormalPenalty adverseNextS14Before) < ((0/1)/1)+(4548649/2000000)-(nextNormalPenalty adverseNextS14Before) := by
    have h : (((0/1)/2)+(3216381/2000000) : ℝ) < ((0/1)/1)+(4548649/2000000) := by norm_num
    linarith
  have h := index_strict_order_from_intervals ((0/1)/1) ((0/1)/2) (nextNormalPenalty adverseNextS14Before) (nextNormalPenalty adverseNextS14Before) (4548649/2000000) (3216381/2000000)
    (treeBonus (7/5) 13 1) (treeBonus (7/5) 13 2)
    (trajectory_bonus_13_1).1 (trajectory_bonus_13_2).2 hm
  simpa only [treeIndex] using h

theorem adverseNextS14D0Cmp5 : indexScore (7/5) (controlPenalty savedCref uniformQuoteError unitRoleUnused .next) adverseNextS14Before [] (.query 5) ≤ indexScore (7/5) (controlPenalty savedCref uniformQuoteError unitRoleUnused .next) adverseNextS14Before [] (.query 4) := by
  rw [adverseNextS14D0I5,adverseNextS14D0I4]
  have hk := adverse_next_penalty_interval 13 (by omega)
  change nextNormalPenaltyLower ≤ nextNormalPenalty adverseNextS14Before ∧ nextNormalPenalty adverseNextS14Before ≤ nextNormalPenaltyUpper at hk
  have hm : ((9/10)/2)+(3216381/2000000)-(nextNormalPenalty adverseNextS14Before) < ((0/1)/1)+(4548649/2000000)-(nextNormalPenalty adverseNextS14Before) := by
    have h : (((9/10)/2)+(3216381/2000000) : ℝ) < ((0/1)/1)+(4548649/2000000) := by norm_num
    linarith
  have h := index_weak_order_from_intervals ((0/1)/1) ((9/10)/2) (nextNormalPenalty adverseNextS14Before) (nextNormalPenalty adverseNextS14Before) (4548649/2000000) (3216381/2000000)
    (treeBonus (7/5) 13 1) (treeBonus (7/5) 13 2)
    (trajectory_bonus_13_1).1 (trajectory_bonus_13_2).2 hm.le
  simpa only [treeIndex] using h

theorem adverseNextS14D0Cmp6 : indexScore (7/5) (controlPenalty savedCref uniformQuoteError unitRoleUnused .next) adverseNextS14Before [] (.query 6) ≤ indexScore (7/5) (controlPenalty savedCref uniformQuoteError unitRoleUnused .next) adverseNextS14Before [] (.query 4) := by
  rw [adverseNextS14D0I6,adverseNextS14D0I4]

theorem adverseNextS14D0Cmp7 : indexScore (7/5) (controlPenalty savedCref uniformQuoteError unitRoleUnused .next) adverseNextS14Before [] (.query 7) ≤ indexScore (7/5) (controlPenalty savedCref uniformQuoteError unitRoleUnused .next) adverseNextS14Before [] (.query 4) := by
  rw [adverseNextS14D0I7,adverseNextS14D0I4]

theorem adverseNextS14Choice0 : nativeFirstChoice (indexScore (7/5) (controlPenalty savedCref uniformQuoteError unitRoleUnused .next) adverseNextS14Before []) adverseNextS14Before [] = .query 4 := by
  apply visited_choice_from_ordered_certificate _ _ [] [.query 0,.query 1,.query 2,.query 3] [.query 5,.query 6,.query 7] (.query 4) (by decide)
  · intro a ha
    have ho : orderedLegalAvailable [] = [.query 0,.query 1,.query 2,.query 3,.query 4,.query 5,.query 6,.query 7] := by decide
    rw [ho] at ha
    simp only [List.mem_cons,List.not_mem_nil,or_false] at ha
    rcases ha with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> decide
  · intro a ha
    simp only [List.mem_cons,List.not_mem_nil,or_false] at ha
    rcases ha with rfl | rfl | rfl | rfl
    · exact adverseNextS14D0Cmp0
    · exact adverseNextS14D0Cmp1
    · exact adverseNextS14D0Cmp2
    · exact adverseNextS14D0Cmp3
  · intro a ha
    simp only [List.mem_cons,List.not_mem_nil,or_false] at ha
    rcases ha with rfl | rfl | rfl
    · exact adverseNextS14D0Cmp5
    · exact adverseNextS14D0Cmp6
    · exact adverseNextS14D0Cmp7

theorem adverseNextS14ActualEvent : nativeEvent budgetTape (7/5) (controlPenalty savedCref uniformQuoteError unitRoleUnused .next)
    (taskReward true (2/5) (1/2)) adverseNextS14Before = adverseNextEvent14 := by
  have hs0 := native_select_existing_step budgetTape (7/5) (controlPenalty savedCref uniformQuoteError unitRoleUnused .next) adverseNextS14Before 8 [] (.query 4)
    (by decide) (by decide) adverseNextS14Choice0
  have hnew := native_select_new_step budgetTape (7/5) (controlPenalty savedCref uniformQuoteError unitRoleUnused .next) adverseNextS14Before 7 [.query 4]
    [.normalRetriever 4,.normalRetriever 6,.normalRetriever 7,.normalRetriever 8,.normalRetriever 5,.normalRetriever 0,.normalRetriever 1,.normalRetriever 2,.normalRetriever 3,.normalRetriever 12,.normalRetriever 14,.normalRetriever 13,.normalRetriever 21,.normalRetriever 23,.normalRetriever 22,.normalRetriever 9,.normalRetriever 11,.normalRetriever 10,.normalRetriever 15,.normalRetriever 17,.normalRetriever 16,.normalRetriever 18,.normalRetriever 20,.normalRetriever 19,.normalRetriever 24,.normalRetriever 25,.normalRetriever 26,.normalRetriever 27,.normalRetriever 28,.normalRetriever 29] (.normalRetriever 0) (by decide) (by decide) (by decide) (by decide)
  have hs : nativeSelect budgetTape (7/5) (controlPenalty savedCref uniformQuoteError unitRoleUnused .next) adverseNextS14Before 9 [] = [.query 4,.normalRetriever 0] := by
    rw [hs0]
    change nativeSelect budgetTape (7/5) (controlPenalty savedCref uniformQuoteError unitRoleUnused .next) adverseNextS14Before 8 [.query 4] = _
    rw [hnew] <;> rfl
  have hr : repairedRollout budgetTape adverseNextS14Before 9 [.query 4,.normalRetriever 0] = [.query 4,.normalRetriever 0,.selection 0,.width 0,.stop,.reranker 0,.topm 0,.context 0,.answer 0] := by decide
  simp only [nativeEvent,hs,hr]
  rfl

def adverseNextS15Before := adverseNextProposal.take 14

theorem adverseNextS15D0I0 : indexScore (7/5) (controlPenalty savedCref uniformQuoteError unitRoleUnused .next) adverseNextS15Before [] (.query 0) = treeIndex ((0/1)/2) (7/5) (nextNormalPenalty adverseNextS15Before) 14 2 := by
  have hs : replayBackup adverseNextS15Before emptyStatistics ([]++[.query 0]) = ⟨2,(0/1)⟩ := by
    rw [replayBackup_empty_closed_form]
    simp +decide [backedEvents,adverseNextS15Before,adverseNextProposal,adverseNextEvent1,adverseNextEvent2,adverseNextEvent3,adverseNextEvent4,adverseNextEvent5,adverseNextEvent6,adverseNextEvent7,adverseNextEvent8,adverseNextEvent9,adverseNextEvent10,adverseNextEvent11,adverseNextEvent12,adverseNextEvent13,adverseNextEvent14,taskReward]
    <;> norm_num
  have hp : rawVisits adverseNextS15Before [] = 14 := by decide
  have hn : rawVisits adverseNextS15Before ([]++[.query 0]) = 2 := by decide
  have hz : (controlPenalty savedCref uniformQuoteError unitRoleUnused .next) adverseNextS15Before [] (.query 0) = (nextNormalPenalty adverseNextS15Before) := by
    simpa only [adverseNextS15Before,nextNormalPenalty] using AgentUCTNextExact.adverse_next_normal_root_quotes_exact 14 (by omega) 0 (by decide)
  unfold indexScore
  rw [hs,hp,hn,hz]
  simp only [BackupStat.mean]
  norm_num

theorem adverseNextS15D0I1 : indexScore (7/5) (controlPenalty savedCref uniformQuoteError unitRoleUnused .next) adverseNextS15Before [] (.query 1) = treeIndex ((0/1)/2) (7/5) 0 14 2 := by
  have hs : replayBackup adverseNextS15Before emptyStatistics ([]++[.query 1]) = ⟨2,(0/1)⟩ := by
    rw [replayBackup_empty_closed_form]
    simp +decide [backedEvents,adverseNextS15Before,adverseNextProposal,adverseNextEvent1,adverseNextEvent2,adverseNextEvent3,adverseNextEvent4,adverseNextEvent5,adverseNextEvent6,adverseNextEvent7,adverseNextEvent8,adverseNextEvent9,adverseNextEvent10,adverseNextEvent11,adverseNextEvent12,adverseNextEvent13,adverseNextEvent14,taskReward]
    <;> norm_num
  have hp : rawVisits adverseNextS15Before [] = 14 := by decide
  have hn : rawVisits adverseNextS15Before ([]++[.query 1]) = 2 := by decide
  have hz : (controlPenalty savedCref uniformQuoteError unitRoleUnused .next) adverseNextS15Before [] (.query 1) = 0 := by
    apply control_penalty_empty_suffix
    exact AgentUCTNextExact.adverse_next_hyde_root_suffix_empty 14 (by omega)
  unfold indexScore
  rw [hs,hp,hn,hz]
  simp only [BackupStat.mean]
  norm_num

theorem adverseNextS15D0I2 : indexScore (7/5) (controlPenalty savedCref uniformQuoteError unitRoleUnused .next) adverseNextS15Before [] (.query 2) = treeIndex ((0/1)/2) (7/5) (nextNormalPenalty adverseNextS15Before) 14 2 := by
  have hs : replayBackup adverseNextS15Before emptyStatistics ([]++[.query 2]) = ⟨2,(0/1)⟩ := by
    rw [replayBackup_empty_closed_form]
    simp +decide [backedEvents,adverseNextS15Before,adverseNextProposal,adverseNextEvent1,adverseNextEvent2,adverseNextEvent3,adverseNextEvent4,adverseNextEvent5,adverseNextEvent6,adverseNextEvent7,adverseNextEvent8,adverseNextEvent9,adverseNextEvent10,adverseNextEvent11,adverseNextEvent12,adverseNextEvent13,adverseNextEvent14,taskReward]
    <;> norm_num
  have hp : rawVisits adverseNextS15Before [] = 14 := by decide
  have hn : rawVisits adverseNextS15Before ([]++[.query 2]) = 2 := by decide
  have hz : (controlPenalty savedCref uniformQuoteError unitRoleUnused .next) adverseNextS15Before [] (.query 2) = (nextNormalPenalty adverseNextS15Before) := by
    simpa only [adverseNextS15Before,nextNormalPenalty] using AgentUCTNextExact.adverse_next_normal_root_quotes_exact 14 (by omega) 2 (by decide)
  unfold indexScore
  rw [hs,hp,hn,hz]
  simp only [BackupStat.mean]
  norm_num

theorem adverseNextS15D0I3 : indexScore (7/5) (controlPenalty savedCref uniformQuoteError unitRoleUnused .next) adverseNextS15Before [] (.query 3) = treeIndex ((0/1)/2) (7/5) (nextNormalPenalty adverseNextS15Before) 14 2 := by
  have hs : replayBackup adverseNextS15Before emptyStatistics ([]++[.query 3]) = ⟨2,(0/1)⟩ := by
    rw [replayBackup_empty_closed_form]
    simp +decide [backedEvents,adverseNextS15Before,adverseNextProposal,adverseNextEvent1,adverseNextEvent2,adverseNextEvent3,adverseNextEvent4,adverseNextEvent5,adverseNextEvent6,adverseNextEvent7,adverseNextEvent8,adverseNextEvent9,adverseNextEvent10,adverseNextEvent11,adverseNextEvent12,adverseNextEvent13,adverseNextEvent14,taskReward]
    <;> norm_num
  have hp : rawVisits adverseNextS15Before [] = 14 := by decide
  have hn : rawVisits adverseNextS15Before ([]++[.query 3]) = 2 := by decide
  have hz : (controlPenalty savedCref uniformQuoteError unitRoleUnused .next) adverseNextS15Before [] (.query 3) = (nextNormalPenalty adverseNextS15Before) := by
    simpa only [adverseNextS15Before,nextNormalPenalty] using AgentUCTNextExact.adverse_next_normal_root_quotes_exact 14 (by omega) 3 (by decide)
  unfold indexScore
  rw [hs,hp,hn,hz]
  simp only [BackupStat.mean]
  norm_num

theorem adverseNextS15D0I4 : indexScore (7/5) (controlPenalty savedCref uniformQuoteError unitRoleUnused .next) adverseNextS15Before [] (.query 4) = treeIndex ((0/1)/2) (7/5) (nextNormalPenalty adverseNextS15Before) 14 2 := by
  have hs : replayBackup adverseNextS15Before emptyStatistics ([]++[.query 4]) = ⟨2,(0/1)⟩ := by
    rw [replayBackup_empty_closed_form]
    simp +decide [backedEvents,adverseNextS15Before,adverseNextProposal,adverseNextEvent1,adverseNextEvent2,adverseNextEvent3,adverseNextEvent4,adverseNextEvent5,adverseNextEvent6,adverseNextEvent7,adverseNextEvent8,adverseNextEvent9,adverseNextEvent10,adverseNextEvent11,adverseNextEvent12,adverseNextEvent13,adverseNextEvent14,taskReward]
    <;> norm_num
  have hp : rawVisits adverseNextS15Before [] = 14 := by decide
  have hn : rawVisits adverseNextS15Before ([]++[.query 4]) = 2 := by decide
  have hz : (controlPenalty savedCref uniformQuoteError unitRoleUnused .next) adverseNextS15Before [] (.query 4) = (nextNormalPenalty adverseNextS15Before) := by
    simpa only [adverseNextS15Before,nextNormalPenalty] using AgentUCTNextExact.adverse_next_normal_root_quotes_exact 14 (by omega) 4 (by decide)
  unfold indexScore
  rw [hs,hp,hn,hz]
  simp only [BackupStat.mean]
  norm_num

theorem adverseNextS15D0I5 : indexScore (7/5) (controlPenalty savedCref uniformQuoteError unitRoleUnused .next) adverseNextS15Before [] (.query 5) = treeIndex ((9/10)/2) (7/5) (nextNormalPenalty adverseNextS15Before) 14 2 := by
  have hs : replayBackup adverseNextS15Before emptyStatistics ([]++[.query 5]) = ⟨2,(9/10)⟩ := by
    rw [replayBackup_empty_closed_form]
    simp +decide [backedEvents,adverseNextS15Before,adverseNextProposal,adverseNextEvent1,adverseNextEvent2,adverseNextEvent3,adverseNextEvent4,adverseNextEvent5,adverseNextEvent6,adverseNextEvent7,adverseNextEvent8,adverseNextEvent9,adverseNextEvent10,adverseNextEvent11,adverseNextEvent12,adverseNextEvent13,adverseNextEvent14,taskReward]
    <;> norm_num
  have hp : rawVisits adverseNextS15Before [] = 14 := by decide
  have hn : rawVisits adverseNextS15Before ([]++[.query 5]) = 2 := by decide
  have hz : (controlPenalty savedCref uniformQuoteError unitRoleUnused .next) adverseNextS15Before [] (.query 5) = (nextNormalPenalty adverseNextS15Before) := by
    simpa only [adverseNextS15Before,nextNormalPenalty] using AgentUCTNextExact.adverse_next_normal_root_quotes_exact 14 (by omega) 5 (by decide)
  unfold indexScore
  rw [hs,hp,hn,hz]
  simp only [BackupStat.mean]
  norm_num

theorem adverseNextS15D0I6 : indexScore (7/5) (controlPenalty savedCref uniformQuoteError unitRoleUnused .next) adverseNextS15Before [] (.query 6) = treeIndex ((0/1)/1) (7/5) (nextNormalPenalty adverseNextS15Before) 14 1 := by
  have hs : replayBackup adverseNextS15Before emptyStatistics ([]++[.query 6]) = ⟨1,(0/1)⟩ := by
    rw [replayBackup_empty_closed_form]
    simp +decide [backedEvents,adverseNextS15Before,adverseNextProposal,adverseNextEvent1,adverseNextEvent2,adverseNextEvent3,adverseNextEvent4,adverseNextEvent5,adverseNextEvent6,adverseNextEvent7,adverseNextEvent8,adverseNextEvent9,adverseNextEvent10,adverseNextEvent11,adverseNextEvent12,adverseNextEvent13,adverseNextEvent14,taskReward]
    <;> norm_num
  have hp : rawVisits adverseNextS15Before [] = 14 := by decide
  have hn : rawVisits adverseNextS15Before ([]++[.query 6]) = 1 := by decide
  have hz : (controlPenalty savedCref uniformQuoteError unitRoleUnused .next) adverseNextS15Before [] (.query 6) = (nextNormalPenalty adverseNextS15Before) := by
    simpa only [adverseNextS15Before,nextNormalPenalty] using AgentUCTNextExact.adverse_next_normal_root_quotes_exact 14 (by omega) 6 (by decide)
  unfold indexScore
  rw [hs,hp,hn,hz]
  simp only [BackupStat.mean]
  norm_num

theorem adverseNextS15D0I7 : indexScore (7/5) (controlPenalty savedCref uniformQuoteError unitRoleUnused .next) adverseNextS15Before [] (.query 7) = treeIndex ((0/1)/1) (7/5) (nextNormalPenalty adverseNextS15Before) 14 1 := by
  have hs : replayBackup adverseNextS15Before emptyStatistics ([]++[.query 7]) = ⟨1,(0/1)⟩ := by
    rw [replayBackup_empty_closed_form]
    simp +decide [backedEvents,adverseNextS15Before,adverseNextProposal,adverseNextEvent1,adverseNextEvent2,adverseNextEvent3,adverseNextEvent4,adverseNextEvent5,adverseNextEvent6,adverseNextEvent7,adverseNextEvent8,adverseNextEvent9,adverseNextEvent10,adverseNextEvent11,adverseNextEvent12,adverseNextEvent13,adverseNextEvent14,taskReward]
    <;> norm_num
  have hp : rawVisits adverseNextS15Before [] = 14 := by decide
  have hn : rawVisits adverseNextS15Before ([]++[.query 7]) = 1 := by decide
  have hz : (controlPenalty savedCref uniformQuoteError unitRoleUnused .next) adverseNextS15Before [] (.query 7) = (nextNormalPenalty adverseNextS15Before) := by
    simpa only [adverseNextS15Before,nextNormalPenalty] using AgentUCTNextExact.adverse_next_normal_root_quotes_exact 14 (by omega) 7 (by decide)
  unfold indexScore
  rw [hs,hp,hn,hz]
  simp only [BackupStat.mean]
  norm_num

theorem adverseNextS15D0Cmp0 : indexScore (7/5) (controlPenalty savedCref uniformQuoteError unitRoleUnused .next) adverseNextS15Before [] (.query 0) < indexScore (7/5) (controlPenalty savedCref uniformQuoteError unitRoleUnused .next) adverseNextS15Before [] (.query 6) := by
  rw [adverseNextS15D0I0,adverseNextS15D0I6]
  have hk := adverse_next_penalty_interval 14 (by omega)
  change nextNormalPenaltyLower ≤ nextNormalPenalty adverseNextS15Before ∧ nextNormalPenalty adverseNextS15Before ≤ nextNormalPenaltyUpper at hk
  have hm : ((0/1)/2)+(81453813/50000000)-(nextNormalPenalty adverseNextS15Before) < ((0/1)/1)+(57596539/25000000)-(nextNormalPenalty adverseNextS15Before) := by
    have h : (((0/1)/2)+(81453813/50000000) : ℝ) < ((0/1)/1)+(57596539/25000000) := by norm_num
    linarith
  have h := index_strict_order_from_intervals ((0/1)/1) ((0/1)/2) (nextNormalPenalty adverseNextS15Before) (nextNormalPenalty adverseNextS15Before) (57596539/25000000) (81453813/50000000)
    (treeBonus (7/5) 14 1) (treeBonus (7/5) 14 2)
    (trajectory_bonus_14_1).1 (trajectory_bonus_14_2).2 hm
  simpa only [treeIndex] using h

theorem adverseNextS15D0Cmp1 : indexScore (7/5) (controlPenalty savedCref uniformQuoteError unitRoleUnused .next) adverseNextS15Before [] (.query 1) < indexScore (7/5) (controlPenalty savedCref uniformQuoteError unitRoleUnused .next) adverseNextS15Before [] (.query 6) := by
  rw [adverseNextS15D0I1,adverseNextS15D0I6]
  have hk := adverse_next_penalty_interval 14 (by omega)
  change nextNormalPenaltyLower ≤ nextNormalPenalty adverseNextS15Before ∧ nextNormalPenalty adverseNextS15Before ≤ nextNormalPenaltyUpper at hk
  have hm : ((0/1)/2)+(81453813/50000000)-0 < ((0/1)/1)+(57596539/25000000)-(nextNormalPenalty adverseNextS15Before) := by
    have h : ((0/1)/2)+(81453813/50000000) < ((0/1)/1)+(57596539/25000000)-nextNormalPenaltyUpper := by norm_num [nextNormalPenaltyUpper,savedCref,uniformQuoteError]
    linarith [hk.2]
  have h := index_strict_order_from_intervals ((0/1)/1) ((0/1)/2) (nextNormalPenalty adverseNextS15Before) 0 (57596539/25000000) (81453813/50000000)
    (treeBonus (7/5) 14 1) (treeBonus (7/5) 14 2)
    (trajectory_bonus_14_1).1 (trajectory_bonus_14_2).2 hm
  simpa only [treeIndex] using h

theorem adverseNextS15D0Cmp2 : indexScore (7/5) (controlPenalty savedCref uniformQuoteError unitRoleUnused .next) adverseNextS15Before [] (.query 2) < indexScore (7/5) (controlPenalty savedCref uniformQuoteError unitRoleUnused .next) adverseNextS15Before [] (.query 6) := by
  rw [adverseNextS15D0I2,adverseNextS15D0I6]
  have hk := adverse_next_penalty_interval 14 (by omega)
  change nextNormalPenaltyLower ≤ nextNormalPenalty adverseNextS15Before ∧ nextNormalPenalty adverseNextS15Before ≤ nextNormalPenaltyUpper at hk
  have hm : ((0/1)/2)+(81453813/50000000)-(nextNormalPenalty adverseNextS15Before) < ((0/1)/1)+(57596539/25000000)-(nextNormalPenalty adverseNextS15Before) := by
    have h : (((0/1)/2)+(81453813/50000000) : ℝ) < ((0/1)/1)+(57596539/25000000) := by norm_num
    linarith
  have h := index_strict_order_from_intervals ((0/1)/1) ((0/1)/2) (nextNormalPenalty adverseNextS15Before) (nextNormalPenalty adverseNextS15Before) (57596539/25000000) (81453813/50000000)
    (treeBonus (7/5) 14 1) (treeBonus (7/5) 14 2)
    (trajectory_bonus_14_1).1 (trajectory_bonus_14_2).2 hm
  simpa only [treeIndex] using h

theorem adverseNextS15D0Cmp3 : indexScore (7/5) (controlPenalty savedCref uniformQuoteError unitRoleUnused .next) adverseNextS15Before [] (.query 3) < indexScore (7/5) (controlPenalty savedCref uniformQuoteError unitRoleUnused .next) adverseNextS15Before [] (.query 6) := by
  rw [adverseNextS15D0I3,adverseNextS15D0I6]
  have hk := adverse_next_penalty_interval 14 (by omega)
  change nextNormalPenaltyLower ≤ nextNormalPenalty adverseNextS15Before ∧ nextNormalPenalty adverseNextS15Before ≤ nextNormalPenaltyUpper at hk
  have hm : ((0/1)/2)+(81453813/50000000)-(nextNormalPenalty adverseNextS15Before) < ((0/1)/1)+(57596539/25000000)-(nextNormalPenalty adverseNextS15Before) := by
    have h : (((0/1)/2)+(81453813/50000000) : ℝ) < ((0/1)/1)+(57596539/25000000) := by norm_num
    linarith
  have h := index_strict_order_from_intervals ((0/1)/1) ((0/1)/2) (nextNormalPenalty adverseNextS15Before) (nextNormalPenalty adverseNextS15Before) (57596539/25000000) (81453813/50000000)
    (treeBonus (7/5) 14 1) (treeBonus (7/5) 14 2)
    (trajectory_bonus_14_1).1 (trajectory_bonus_14_2).2 hm
  simpa only [treeIndex] using h

theorem adverseNextS15D0Cmp4 : indexScore (7/5) (controlPenalty savedCref uniformQuoteError unitRoleUnused .next) adverseNextS15Before [] (.query 4) < indexScore (7/5) (controlPenalty savedCref uniformQuoteError unitRoleUnused .next) adverseNextS15Before [] (.query 6) := by
  rw [adverseNextS15D0I4,adverseNextS15D0I6]
  have hk := adverse_next_penalty_interval 14 (by omega)
  change nextNormalPenaltyLower ≤ nextNormalPenalty adverseNextS15Before ∧ nextNormalPenalty adverseNextS15Before ≤ nextNormalPenaltyUpper at hk
  have hm : ((0/1)/2)+(81453813/50000000)-(nextNormalPenalty adverseNextS15Before) < ((0/1)/1)+(57596539/25000000)-(nextNormalPenalty adverseNextS15Before) := by
    have h : (((0/1)/2)+(81453813/50000000) : ℝ) < ((0/1)/1)+(57596539/25000000) := by norm_num
    linarith
  have h := index_strict_order_from_intervals ((0/1)/1) ((0/1)/2) (nextNormalPenalty adverseNextS15Before) (nextNormalPenalty adverseNextS15Before) (57596539/25000000) (81453813/50000000)
    (treeBonus (7/5) 14 1) (treeBonus (7/5) 14 2)
    (trajectory_bonus_14_1).1 (trajectory_bonus_14_2).2 hm
  simpa only [treeIndex] using h

theorem adverseNextS15D0Cmp5 : indexScore (7/5) (controlPenalty savedCref uniformQuoteError unitRoleUnused .next) adverseNextS15Before [] (.query 5) < indexScore (7/5) (controlPenalty savedCref uniformQuoteError unitRoleUnused .next) adverseNextS15Before [] (.query 6) := by
  rw [adverseNextS15D0I5,adverseNextS15D0I6]
  have hk := adverse_next_penalty_interval 14 (by omega)
  change nextNormalPenaltyLower ≤ nextNormalPenalty adverseNextS15Before ∧ nextNormalPenalty adverseNextS15Before ≤ nextNormalPenaltyUpper at hk
  have hm : ((9/10)/2)+(81453813/50000000)-(nextNormalPenalty adverseNextS15Before) < ((0/1)/1)+(57596539/25000000)-(nextNormalPenalty adverseNextS15Before) := by
    have h : (((9/10)/2)+(81453813/50000000) : ℝ) < ((0/1)/1)+(57596539/25000000) := by norm_num
    linarith
  have h := index_strict_order_from_intervals ((0/1)/1) ((9/10)/2) (nextNormalPenalty adverseNextS15Before) (nextNormalPenalty adverseNextS15Before) (57596539/25000000) (81453813/50000000)
    (treeBonus (7/5) 14 1) (treeBonus (7/5) 14 2)
    (trajectory_bonus_14_1).1 (trajectory_bonus_14_2).2 hm
  simpa only [treeIndex] using h

theorem adverseNextS15D0Cmp7 : indexScore (7/5) (controlPenalty savedCref uniformQuoteError unitRoleUnused .next) adverseNextS15Before [] (.query 7) ≤ indexScore (7/5) (controlPenalty savedCref uniformQuoteError unitRoleUnused .next) adverseNextS15Before [] (.query 6) := by
  rw [adverseNextS15D0I7,adverseNextS15D0I6]

theorem adverseNextS15Choice0 : nativeFirstChoice (indexScore (7/5) (controlPenalty savedCref uniformQuoteError unitRoleUnused .next) adverseNextS15Before []) adverseNextS15Before [] = .query 6 := by
  apply visited_choice_from_ordered_certificate _ _ [] [.query 0,.query 1,.query 2,.query 3,.query 4,.query 5] [.query 7] (.query 6) (by decide)
  · intro a ha
    have ho : orderedLegalAvailable [] = [.query 0,.query 1,.query 2,.query 3,.query 4,.query 5,.query 6,.query 7] := by decide
    rw [ho] at ha
    simp only [List.mem_cons,List.not_mem_nil,or_false] at ha
    rcases ha with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> decide
  · intro a ha
    simp only [List.mem_cons,List.not_mem_nil,or_false] at ha
    rcases ha with rfl | rfl | rfl | rfl | rfl | rfl
    · exact adverseNextS15D0Cmp0
    · exact adverseNextS15D0Cmp1
    · exact adverseNextS15D0Cmp2
    · exact adverseNextS15D0Cmp3
    · exact adverseNextS15D0Cmp4
    · exact adverseNextS15D0Cmp5
  · intro a ha
    simp only [List.mem_cons,List.not_mem_nil,or_false] at ha
    rcases ha with rfl
    · exact adverseNextS15D0Cmp7

theorem adverseNextS15ActualEvent : nativeEvent budgetTape (7/5) (controlPenalty savedCref uniformQuoteError unitRoleUnused .next)
    (taskReward true (2/5) (1/2)) adverseNextS15Before = adverseNextEvent15 := by
  have hs0 := native_select_existing_step budgetTape (7/5) (controlPenalty savedCref uniformQuoteError unitRoleUnused .next) adverseNextS15Before 8 [] (.query 6)
    (by decide) (by decide) adverseNextS15Choice0
  have hnew := native_select_new_step budgetTape (7/5) (controlPenalty savedCref uniformQuoteError unitRoleUnused .next) adverseNextS15Before 7 [.query 6]
    [.normalRetriever 4,.normalRetriever 6,.normalRetriever 7,.normalRetriever 8,.normalRetriever 5,.normalRetriever 0,.normalRetriever 1,.normalRetriever 2,.normalRetriever 3,.normalRetriever 12,.normalRetriever 14,.normalRetriever 13,.normalRetriever 21,.normalRetriever 23,.normalRetriever 22,.normalRetriever 9,.normalRetriever 11,.normalRetriever 10,.normalRetriever 15,.normalRetriever 17,.normalRetriever 16,.normalRetriever 18,.normalRetriever 20,.normalRetriever 19,.normalRetriever 24,.normalRetriever 25,.normalRetriever 26,.normalRetriever 27,.normalRetriever 28,.normalRetriever 29] (.normalRetriever 0) (by decide) (by decide) (by decide) (by decide)
  have hs : nativeSelect budgetTape (7/5) (controlPenalty savedCref uniformQuoteError unitRoleUnused .next) adverseNextS15Before 9 [] = [.query 6,.normalRetriever 0] := by
    rw [hs0]
    change nativeSelect budgetTape (7/5) (controlPenalty savedCref uniformQuoteError unitRoleUnused .next) adverseNextS15Before 8 [.query 6] = _
    rw [hnew] <;> rfl
  have hr : repairedRollout budgetTape adverseNextS15Before 9 [.query 6,.normalRetriever 0] = [.query 6,.normalRetriever 0,.selection 0,.width 0,.stop,.reranker 0,.topm 0,.context 0,.answer 0] := by decide
  simp only [nativeEvent,hs,hr]
  rfl

def adverseNextS16Before := adverseNextProposal.take 15

theorem adverseNextS16D0I0 : indexScore (7/5) (controlPenalty savedCref uniformQuoteError unitRoleUnused .next) adverseNextS16Before [] (.query 0) = treeIndex ((0/1)/2) (7/5) (nextNormalPenalty adverseNextS16Before) 15 2 := by
  have hs : replayBackup adverseNextS16Before emptyStatistics ([]++[.query 0]) = ⟨2,(0/1)⟩ := by
    rw [replayBackup_empty_closed_form]
    simp +decide [backedEvents,adverseNextS16Before,adverseNextProposal,adverseNextEvent1,adverseNextEvent2,adverseNextEvent3,adverseNextEvent4,adverseNextEvent5,adverseNextEvent6,adverseNextEvent7,adverseNextEvent8,adverseNextEvent9,adverseNextEvent10,adverseNextEvent11,adverseNextEvent12,adverseNextEvent13,adverseNextEvent14,adverseNextEvent15,taskReward]
    <;> norm_num
  have hp : rawVisits adverseNextS16Before [] = 15 := by decide
  have hn : rawVisits adverseNextS16Before ([]++[.query 0]) = 2 := by decide
  have hz : (controlPenalty savedCref uniformQuoteError unitRoleUnused .next) adverseNextS16Before [] (.query 0) = (nextNormalPenalty adverseNextS16Before) := by
    simpa only [adverseNextS16Before,nextNormalPenalty] using AgentUCTNextExact.adverse_next_normal_root_quotes_exact 15 (by omega) 0 (by decide)
  unfold indexScore
  rw [hs,hp,hn,hz]
  simp only [BackupStat.mean]
  norm_num

theorem adverseNextS16D0I1 : indexScore (7/5) (controlPenalty savedCref uniformQuoteError unitRoleUnused .next) adverseNextS16Before [] (.query 1) = treeIndex ((0/1)/2) (7/5) 0 15 2 := by
  have hs : replayBackup adverseNextS16Before emptyStatistics ([]++[.query 1]) = ⟨2,(0/1)⟩ := by
    rw [replayBackup_empty_closed_form]
    simp +decide [backedEvents,adverseNextS16Before,adverseNextProposal,adverseNextEvent1,adverseNextEvent2,adverseNextEvent3,adverseNextEvent4,adverseNextEvent5,adverseNextEvent6,adverseNextEvent7,adverseNextEvent8,adverseNextEvent9,adverseNextEvent10,adverseNextEvent11,adverseNextEvent12,adverseNextEvent13,adverseNextEvent14,adverseNextEvent15,taskReward]
    <;> norm_num
  have hp : rawVisits adverseNextS16Before [] = 15 := by decide
  have hn : rawVisits adverseNextS16Before ([]++[.query 1]) = 2 := by decide
  have hz : (controlPenalty savedCref uniformQuoteError unitRoleUnused .next) adverseNextS16Before [] (.query 1) = 0 := by
    apply control_penalty_empty_suffix
    exact AgentUCTNextExact.adverse_next_hyde_root_suffix_empty 15 (by omega)
  unfold indexScore
  rw [hs,hp,hn,hz]
  simp only [BackupStat.mean]
  norm_num

theorem adverseNextS16D0I2 : indexScore (7/5) (controlPenalty savedCref uniformQuoteError unitRoleUnused .next) adverseNextS16Before [] (.query 2) = treeIndex ((0/1)/2) (7/5) (nextNormalPenalty adverseNextS16Before) 15 2 := by
  have hs : replayBackup adverseNextS16Before emptyStatistics ([]++[.query 2]) = ⟨2,(0/1)⟩ := by
    rw [replayBackup_empty_closed_form]
    simp +decide [backedEvents,adverseNextS16Before,adverseNextProposal,adverseNextEvent1,adverseNextEvent2,adverseNextEvent3,adverseNextEvent4,adverseNextEvent5,adverseNextEvent6,adverseNextEvent7,adverseNextEvent8,adverseNextEvent9,adverseNextEvent10,adverseNextEvent11,adverseNextEvent12,adverseNextEvent13,adverseNextEvent14,adverseNextEvent15,taskReward]
    <;> norm_num
  have hp : rawVisits adverseNextS16Before [] = 15 := by decide
  have hn : rawVisits adverseNextS16Before ([]++[.query 2]) = 2 := by decide
  have hz : (controlPenalty savedCref uniformQuoteError unitRoleUnused .next) adverseNextS16Before [] (.query 2) = (nextNormalPenalty adverseNextS16Before) := by
    simpa only [adverseNextS16Before,nextNormalPenalty] using AgentUCTNextExact.adverse_next_normal_root_quotes_exact 15 (by omega) 2 (by decide)
  unfold indexScore
  rw [hs,hp,hn,hz]
  simp only [BackupStat.mean]
  norm_num

theorem adverseNextS16D0I3 : indexScore (7/5) (controlPenalty savedCref uniformQuoteError unitRoleUnused .next) adverseNextS16Before [] (.query 3) = treeIndex ((0/1)/2) (7/5) (nextNormalPenalty adverseNextS16Before) 15 2 := by
  have hs : replayBackup adverseNextS16Before emptyStatistics ([]++[.query 3]) = ⟨2,(0/1)⟩ := by
    rw [replayBackup_empty_closed_form]
    simp +decide [backedEvents,adverseNextS16Before,adverseNextProposal,adverseNextEvent1,adverseNextEvent2,adverseNextEvent3,adverseNextEvent4,adverseNextEvent5,adverseNextEvent6,adverseNextEvent7,adverseNextEvent8,adverseNextEvent9,adverseNextEvent10,adverseNextEvent11,adverseNextEvent12,adverseNextEvent13,adverseNextEvent14,adverseNextEvent15,taskReward]
    <;> norm_num
  have hp : rawVisits adverseNextS16Before [] = 15 := by decide
  have hn : rawVisits adverseNextS16Before ([]++[.query 3]) = 2 := by decide
  have hz : (controlPenalty savedCref uniformQuoteError unitRoleUnused .next) adverseNextS16Before [] (.query 3) = (nextNormalPenalty adverseNextS16Before) := by
    simpa only [adverseNextS16Before,nextNormalPenalty] using AgentUCTNextExact.adverse_next_normal_root_quotes_exact 15 (by omega) 3 (by decide)
  unfold indexScore
  rw [hs,hp,hn,hz]
  simp only [BackupStat.mean]
  norm_num

theorem adverseNextS16D0I4 : indexScore (7/5) (controlPenalty savedCref uniformQuoteError unitRoleUnused .next) adverseNextS16Before [] (.query 4) = treeIndex ((0/1)/2) (7/5) (nextNormalPenalty adverseNextS16Before) 15 2 := by
  have hs : replayBackup adverseNextS16Before emptyStatistics ([]++[.query 4]) = ⟨2,(0/1)⟩ := by
    rw [replayBackup_empty_closed_form]
    simp +decide [backedEvents,adverseNextS16Before,adverseNextProposal,adverseNextEvent1,adverseNextEvent2,adverseNextEvent3,adverseNextEvent4,adverseNextEvent5,adverseNextEvent6,adverseNextEvent7,adverseNextEvent8,adverseNextEvent9,adverseNextEvent10,adverseNextEvent11,adverseNextEvent12,adverseNextEvent13,adverseNextEvent14,adverseNextEvent15,taskReward]
    <;> norm_num
  have hp : rawVisits adverseNextS16Before [] = 15 := by decide
  have hn : rawVisits adverseNextS16Before ([]++[.query 4]) = 2 := by decide
  have hz : (controlPenalty savedCref uniformQuoteError unitRoleUnused .next) adverseNextS16Before [] (.query 4) = (nextNormalPenalty adverseNextS16Before) := by
    simpa only [adverseNextS16Before,nextNormalPenalty] using AgentUCTNextExact.adverse_next_normal_root_quotes_exact 15 (by omega) 4 (by decide)
  unfold indexScore
  rw [hs,hp,hn,hz]
  simp only [BackupStat.mean]
  norm_num

theorem adverseNextS16D0I5 : indexScore (7/5) (controlPenalty savedCref uniformQuoteError unitRoleUnused .next) adverseNextS16Before [] (.query 5) = treeIndex ((9/10)/2) (7/5) (nextNormalPenalty adverseNextS16Before) 15 2 := by
  have hs : replayBackup adverseNextS16Before emptyStatistics ([]++[.query 5]) = ⟨2,(9/10)⟩ := by
    rw [replayBackup_empty_closed_form]
    simp +decide [backedEvents,adverseNextS16Before,adverseNextProposal,adverseNextEvent1,adverseNextEvent2,adverseNextEvent3,adverseNextEvent4,adverseNextEvent5,adverseNextEvent6,adverseNextEvent7,adverseNextEvent8,adverseNextEvent9,adverseNextEvent10,adverseNextEvent11,adverseNextEvent12,adverseNextEvent13,adverseNextEvent14,adverseNextEvent15,taskReward]
    <;> norm_num
  have hp : rawVisits adverseNextS16Before [] = 15 := by decide
  have hn : rawVisits adverseNextS16Before ([]++[.query 5]) = 2 := by decide
  have hz : (controlPenalty savedCref uniformQuoteError unitRoleUnused .next) adverseNextS16Before [] (.query 5) = (nextNormalPenalty adverseNextS16Before) := by
    simpa only [adverseNextS16Before,nextNormalPenalty] using AgentUCTNextExact.adverse_next_normal_root_quotes_exact 15 (by omega) 5 (by decide)
  unfold indexScore
  rw [hs,hp,hn,hz]
  simp only [BackupStat.mean]
  norm_num

theorem adverseNextS16D0I6 : indexScore (7/5) (controlPenalty savedCref uniformQuoteError unitRoleUnused .next) adverseNextS16Before [] (.query 6) = treeIndex ((0/1)/2) (7/5) (nextNormalPenalty adverseNextS16Before) 15 2 := by
  have hs : replayBackup adverseNextS16Before emptyStatistics ([]++[.query 6]) = ⟨2,(0/1)⟩ := by
    rw [replayBackup_empty_closed_form]
    simp +decide [backedEvents,adverseNextS16Before,adverseNextProposal,adverseNextEvent1,adverseNextEvent2,adverseNextEvent3,adverseNextEvent4,adverseNextEvent5,adverseNextEvent6,adverseNextEvent7,adverseNextEvent8,adverseNextEvent9,adverseNextEvent10,adverseNextEvent11,adverseNextEvent12,adverseNextEvent13,adverseNextEvent14,adverseNextEvent15,taskReward]
    <;> norm_num
  have hp : rawVisits adverseNextS16Before [] = 15 := by decide
  have hn : rawVisits adverseNextS16Before ([]++[.query 6]) = 2 := by decide
  have hz : (controlPenalty savedCref uniformQuoteError unitRoleUnused .next) adverseNextS16Before [] (.query 6) = (nextNormalPenalty adverseNextS16Before) := by
    simpa only [adverseNextS16Before,nextNormalPenalty] using AgentUCTNextExact.adverse_next_normal_root_quotes_exact 15 (by omega) 6 (by decide)
  unfold indexScore
  rw [hs,hp,hn,hz]
  simp only [BackupStat.mean]
  norm_num

theorem adverseNextS16D0I7 : indexScore (7/5) (controlPenalty savedCref uniformQuoteError unitRoleUnused .next) adverseNextS16Before [] (.query 7) = treeIndex ((0/1)/1) (7/5) (nextNormalPenalty adverseNextS16Before) 15 1 := by
  have hs : replayBackup adverseNextS16Before emptyStatistics ([]++[.query 7]) = ⟨1,(0/1)⟩ := by
    rw [replayBackup_empty_closed_form]
    simp +decide [backedEvents,adverseNextS16Before,adverseNextProposal,adverseNextEvent1,adverseNextEvent2,adverseNextEvent3,adverseNextEvent4,adverseNextEvent5,adverseNextEvent6,adverseNextEvent7,adverseNextEvent8,adverseNextEvent9,adverseNextEvent10,adverseNextEvent11,adverseNextEvent12,adverseNextEvent13,adverseNextEvent14,adverseNextEvent15,taskReward]
    <;> norm_num
  have hp : rawVisits adverseNextS16Before [] = 15 := by decide
  have hn : rawVisits adverseNextS16Before ([]++[.query 7]) = 1 := by decide
  have hz : (controlPenalty savedCref uniformQuoteError unitRoleUnused .next) adverseNextS16Before [] (.query 7) = (nextNormalPenalty adverseNextS16Before) := by
    simpa only [adverseNextS16Before,nextNormalPenalty] using AgentUCTNextExact.adverse_next_normal_root_quotes_exact 15 (by omega) 7 (by decide)
  unfold indexScore
  rw [hs,hp,hn,hz]
  simp only [BackupStat.mean]
  norm_num

theorem adverseNextS16D0Cmp0 : indexScore (7/5) (controlPenalty savedCref uniformQuoteError unitRoleUnused .next) adverseNextS16Before [] (.query 0) < indexScore (7/5) (controlPenalty savedCref uniformQuoteError unitRoleUnused .next) adverseNextS16Before [] (.query 7) := by
  rw [adverseNextS16D0I0,adverseNextS16D0I7]
  have hk := adverse_next_penalty_interval 15 (by omega)
  change nextNormalPenaltyLower ≤ nextNormalPenalty adverseNextS16Before ∧ nextNormalPenalty adverseNextS16Before ≤ nextNormalPenaltyUpper at hk
  have hm : ((0/1)/2)+(82418707/50000000)-(nextNormalPenalty adverseNextS16Before) < ((0/1)/1)+(29139411/12500000)-(nextNormalPenalty adverseNextS16Before) := by
    have h : (((0/1)/2)+(82418707/50000000) : ℝ) < ((0/1)/1)+(29139411/12500000) := by norm_num
    linarith
  have h := index_strict_order_from_intervals ((0/1)/1) ((0/1)/2) (nextNormalPenalty adverseNextS16Before) (nextNormalPenalty adverseNextS16Before) (29139411/12500000) (82418707/50000000)
    (treeBonus (7/5) 15 1) (treeBonus (7/5) 15 2)
    (trajectory_bonus_15_1).1 (trajectory_bonus_15_2).2 hm
  simpa only [treeIndex] using h

theorem adverseNextS16D0Cmp1 : indexScore (7/5) (controlPenalty savedCref uniformQuoteError unitRoleUnused .next) adverseNextS16Before [] (.query 1) < indexScore (7/5) (controlPenalty savedCref uniformQuoteError unitRoleUnused .next) adverseNextS16Before [] (.query 7) := by
  rw [adverseNextS16D0I1,adverseNextS16D0I7]
  have hk := adverse_next_penalty_interval 15 (by omega)
  change nextNormalPenaltyLower ≤ nextNormalPenalty adverseNextS16Before ∧ nextNormalPenalty adverseNextS16Before ≤ nextNormalPenaltyUpper at hk
  have hm : ((0/1)/2)+(82418707/50000000)-0 < ((0/1)/1)+(29139411/12500000)-(nextNormalPenalty adverseNextS16Before) := by
    have h : ((0/1)/2)+(82418707/50000000) < ((0/1)/1)+(29139411/12500000)-nextNormalPenaltyUpper := by norm_num [nextNormalPenaltyUpper,savedCref,uniformQuoteError]
    linarith [hk.2]
  have h := index_strict_order_from_intervals ((0/1)/1) ((0/1)/2) (nextNormalPenalty adverseNextS16Before) 0 (29139411/12500000) (82418707/50000000)
    (treeBonus (7/5) 15 1) (treeBonus (7/5) 15 2)
    (trajectory_bonus_15_1).1 (trajectory_bonus_15_2).2 hm
  simpa only [treeIndex] using h

theorem adverseNextS16D0Cmp2 : indexScore (7/5) (controlPenalty savedCref uniformQuoteError unitRoleUnused .next) adverseNextS16Before [] (.query 2) < indexScore (7/5) (controlPenalty savedCref uniformQuoteError unitRoleUnused .next) adverseNextS16Before [] (.query 7) := by
  rw [adverseNextS16D0I2,adverseNextS16D0I7]
  have hk := adverse_next_penalty_interval 15 (by omega)
  change nextNormalPenaltyLower ≤ nextNormalPenalty adverseNextS16Before ∧ nextNormalPenalty adverseNextS16Before ≤ nextNormalPenaltyUpper at hk
  have hm : ((0/1)/2)+(82418707/50000000)-(nextNormalPenalty adverseNextS16Before) < ((0/1)/1)+(29139411/12500000)-(nextNormalPenalty adverseNextS16Before) := by
    have h : (((0/1)/2)+(82418707/50000000) : ℝ) < ((0/1)/1)+(29139411/12500000) := by norm_num
    linarith
  have h := index_strict_order_from_intervals ((0/1)/1) ((0/1)/2) (nextNormalPenalty adverseNextS16Before) (nextNormalPenalty adverseNextS16Before) (29139411/12500000) (82418707/50000000)
    (treeBonus (7/5) 15 1) (treeBonus (7/5) 15 2)
    (trajectory_bonus_15_1).1 (trajectory_bonus_15_2).2 hm
  simpa only [treeIndex] using h

theorem adverseNextS16D0Cmp3 : indexScore (7/5) (controlPenalty savedCref uniformQuoteError unitRoleUnused .next) adverseNextS16Before [] (.query 3) < indexScore (7/5) (controlPenalty savedCref uniformQuoteError unitRoleUnused .next) adverseNextS16Before [] (.query 7) := by
  rw [adverseNextS16D0I3,adverseNextS16D0I7]
  have hk := adverse_next_penalty_interval 15 (by omega)
  change nextNormalPenaltyLower ≤ nextNormalPenalty adverseNextS16Before ∧ nextNormalPenalty adverseNextS16Before ≤ nextNormalPenaltyUpper at hk
  have hm : ((0/1)/2)+(82418707/50000000)-(nextNormalPenalty adverseNextS16Before) < ((0/1)/1)+(29139411/12500000)-(nextNormalPenalty adverseNextS16Before) := by
    have h : (((0/1)/2)+(82418707/50000000) : ℝ) < ((0/1)/1)+(29139411/12500000) := by norm_num
    linarith
  have h := index_strict_order_from_intervals ((0/1)/1) ((0/1)/2) (nextNormalPenalty adverseNextS16Before) (nextNormalPenalty adverseNextS16Before) (29139411/12500000) (82418707/50000000)
    (treeBonus (7/5) 15 1) (treeBonus (7/5) 15 2)
    (trajectory_bonus_15_1).1 (trajectory_bonus_15_2).2 hm
  simpa only [treeIndex] using h

theorem adverseNextS16D0Cmp4 : indexScore (7/5) (controlPenalty savedCref uniformQuoteError unitRoleUnused .next) adverseNextS16Before [] (.query 4) < indexScore (7/5) (controlPenalty savedCref uniformQuoteError unitRoleUnused .next) adverseNextS16Before [] (.query 7) := by
  rw [adverseNextS16D0I4,adverseNextS16D0I7]
  have hk := adverse_next_penalty_interval 15 (by omega)
  change nextNormalPenaltyLower ≤ nextNormalPenalty adverseNextS16Before ∧ nextNormalPenalty adverseNextS16Before ≤ nextNormalPenaltyUpper at hk
  have hm : ((0/1)/2)+(82418707/50000000)-(nextNormalPenalty adverseNextS16Before) < ((0/1)/1)+(29139411/12500000)-(nextNormalPenalty adverseNextS16Before) := by
    have h : (((0/1)/2)+(82418707/50000000) : ℝ) < ((0/1)/1)+(29139411/12500000) := by norm_num
    linarith
  have h := index_strict_order_from_intervals ((0/1)/1) ((0/1)/2) (nextNormalPenalty adverseNextS16Before) (nextNormalPenalty adverseNextS16Before) (29139411/12500000) (82418707/50000000)
    (treeBonus (7/5) 15 1) (treeBonus (7/5) 15 2)
    (trajectory_bonus_15_1).1 (trajectory_bonus_15_2).2 hm
  simpa only [treeIndex] using h

theorem adverseNextS16D0Cmp5 : indexScore (7/5) (controlPenalty savedCref uniformQuoteError unitRoleUnused .next) adverseNextS16Before [] (.query 5) < indexScore (7/5) (controlPenalty savedCref uniformQuoteError unitRoleUnused .next) adverseNextS16Before [] (.query 7) := by
  rw [adverseNextS16D0I5,adverseNextS16D0I7]
  have hk := adverse_next_penalty_interval 15 (by omega)
  change nextNormalPenaltyLower ≤ nextNormalPenalty adverseNextS16Before ∧ nextNormalPenalty adverseNextS16Before ≤ nextNormalPenaltyUpper at hk
  have hm : ((9/10)/2)+(82418707/50000000)-(nextNormalPenalty adverseNextS16Before) < ((0/1)/1)+(29139411/12500000)-(nextNormalPenalty adverseNextS16Before) := by
    have h : (((9/10)/2)+(82418707/50000000) : ℝ) < ((0/1)/1)+(29139411/12500000) := by norm_num
    linarith
  have h := index_strict_order_from_intervals ((0/1)/1) ((9/10)/2) (nextNormalPenalty adverseNextS16Before) (nextNormalPenalty adverseNextS16Before) (29139411/12500000) (82418707/50000000)
    (treeBonus (7/5) 15 1) (treeBonus (7/5) 15 2)
    (trajectory_bonus_15_1).1 (trajectory_bonus_15_2).2 hm
  simpa only [treeIndex] using h

theorem adverseNextS16D0Cmp6 : indexScore (7/5) (controlPenalty savedCref uniformQuoteError unitRoleUnused .next) adverseNextS16Before [] (.query 6) < indexScore (7/5) (controlPenalty savedCref uniformQuoteError unitRoleUnused .next) adverseNextS16Before [] (.query 7) := by
  rw [adverseNextS16D0I6,adverseNextS16D0I7]
  have hk := adverse_next_penalty_interval 15 (by omega)
  change nextNormalPenaltyLower ≤ nextNormalPenalty adverseNextS16Before ∧ nextNormalPenalty adverseNextS16Before ≤ nextNormalPenaltyUpper at hk
  have hm : ((0/1)/2)+(82418707/50000000)-(nextNormalPenalty adverseNextS16Before) < ((0/1)/1)+(29139411/12500000)-(nextNormalPenalty adverseNextS16Before) := by
    have h : (((0/1)/2)+(82418707/50000000) : ℝ) < ((0/1)/1)+(29139411/12500000) := by norm_num
    linarith
  have h := index_strict_order_from_intervals ((0/1)/1) ((0/1)/2) (nextNormalPenalty adverseNextS16Before) (nextNormalPenalty adverseNextS16Before) (29139411/12500000) (82418707/50000000)
    (treeBonus (7/5) 15 1) (treeBonus (7/5) 15 2)
    (trajectory_bonus_15_1).1 (trajectory_bonus_15_2).2 hm
  simpa only [treeIndex] using h

theorem adverseNextS16Choice0 : nativeFirstChoice (indexScore (7/5) (controlPenalty savedCref uniformQuoteError unitRoleUnused .next) adverseNextS16Before []) adverseNextS16Before [] = .query 7 := by
  apply visited_choice_from_ordered_certificate _ _ [] [.query 0,.query 1,.query 2,.query 3,.query 4,.query 5,.query 6] [] (.query 7) (by decide)
  · intro a ha
    have ho : orderedLegalAvailable [] = [.query 0,.query 1,.query 2,.query 3,.query 4,.query 5,.query 6,.query 7] := by decide
    rw [ho] at ha
    simp only [List.mem_cons,List.not_mem_nil,or_false] at ha
    rcases ha with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> decide
  · intro a ha
    simp only [List.mem_cons,List.not_mem_nil,or_false] at ha
    rcases ha with rfl | rfl | rfl | rfl | rfl | rfl | rfl
    · exact adverseNextS16D0Cmp0
    · exact adverseNextS16D0Cmp1
    · exact adverseNextS16D0Cmp2
    · exact adverseNextS16D0Cmp3
    · exact adverseNextS16D0Cmp4
    · exact adverseNextS16D0Cmp5
    · exact adverseNextS16D0Cmp6
  · simp

theorem adverseNextS16ActualEvent : nativeEvent budgetTape (7/5) (controlPenalty savedCref uniformQuoteError unitRoleUnused .next)
    (taskReward true (2/5) (1/2)) adverseNextS16Before = adverseNextEvent16 := by
  have hs0 := native_select_existing_step budgetTape (7/5) (controlPenalty savedCref uniformQuoteError unitRoleUnused .next) adverseNextS16Before 8 [] (.query 7)
    (by decide) (by decide) adverseNextS16Choice0
  have hnew := native_select_new_step budgetTape (7/5) (controlPenalty savedCref uniformQuoteError unitRoleUnused .next) adverseNextS16Before 7 [.query 7]
    [.normalRetriever 4,.normalRetriever 6,.normalRetriever 7,.normalRetriever 8,.normalRetriever 5,.normalRetriever 0,.normalRetriever 1,.normalRetriever 2,.normalRetriever 3,.normalRetriever 12,.normalRetriever 14,.normalRetriever 13,.normalRetriever 21,.normalRetriever 23,.normalRetriever 22,.normalRetriever 9,.normalRetriever 11,.normalRetriever 10,.normalRetriever 15,.normalRetriever 17,.normalRetriever 16,.normalRetriever 18,.normalRetriever 20,.normalRetriever 19,.normalRetriever 24,.normalRetriever 25,.normalRetriever 26,.normalRetriever 27,.normalRetriever 28,.normalRetriever 29] (.normalRetriever 0) (by decide) (by decide) (by decide) (by decide)
  have hs : nativeSelect budgetTape (7/5) (controlPenalty savedCref uniformQuoteError unitRoleUnused .next) adverseNextS16Before 9 [] = [.query 7,.normalRetriever 0] := by
    rw [hs0]
    change nativeSelect budgetTape (7/5) (controlPenalty savedCref uniformQuoteError unitRoleUnused .next) adverseNextS16Before 8 [.query 7] = _
    rw [hnew] <;> rfl
  have hr : repairedRollout budgetTape adverseNextS16Before 9 [.query 7,.normalRetriever 0] = [.query 7,.normalRetriever 0,.selection 0,.width 0,.stop,.reranker 0,.topm 0,.context 0,.answer 0] := by decide
  simp only [nativeEvent,hs,hr]
  rfl

def adverseNextS17Before := adverseNextProposal.take 16

theorem adverseNextS17D0I0 : indexScore (7/5) (controlPenalty savedCref uniformQuoteError unitRoleUnused .next) adverseNextS17Before [] (.query 0) = treeIndex ((0/1)/2) (7/5) (nextNormalPenalty adverseNextS17Before) 16 2 := by
  have hs : replayBackup adverseNextS17Before emptyStatistics ([]++[.query 0]) = ⟨2,(0/1)⟩ := by
    rw [replayBackup_empty_closed_form]
    simp +decide [backedEvents,adverseNextS17Before,adverseNextProposal,adverseNextEvent1,adverseNextEvent2,adverseNextEvent3,adverseNextEvent4,adverseNextEvent5,adverseNextEvent6,adverseNextEvent7,adverseNextEvent8,adverseNextEvent9,adverseNextEvent10,adverseNextEvent11,adverseNextEvent12,adverseNextEvent13,adverseNextEvent14,adverseNextEvent15,adverseNextEvent16,taskReward]
    <;> norm_num
  have hp : rawVisits adverseNextS17Before [] = 16 := by decide
  have hn : rawVisits adverseNextS17Before ([]++[.query 0]) = 2 := by decide
  have hz : (controlPenalty savedCref uniformQuoteError unitRoleUnused .next) adverseNextS17Before [] (.query 0) = (nextNormalPenalty adverseNextS17Before) := by
    simpa only [adverseNextS17Before,nextNormalPenalty] using AgentUCTNextExact.adverse_next_normal_root_quotes_exact 16 (by omega) 0 (by decide)
  unfold indexScore
  rw [hs,hp,hn,hz]
  simp only [BackupStat.mean]
  norm_num

theorem adverseNextS17D0I1 : indexScore (7/5) (controlPenalty savedCref uniformQuoteError unitRoleUnused .next) adverseNextS17Before [] (.query 1) = treeIndex ((0/1)/2) (7/5) 0 16 2 := by
  have hs : replayBackup adverseNextS17Before emptyStatistics ([]++[.query 1]) = ⟨2,(0/1)⟩ := by
    rw [replayBackup_empty_closed_form]
    simp +decide [backedEvents,adverseNextS17Before,adverseNextProposal,adverseNextEvent1,adverseNextEvent2,adverseNextEvent3,adverseNextEvent4,adverseNextEvent5,adverseNextEvent6,adverseNextEvent7,adverseNextEvent8,adverseNextEvent9,adverseNextEvent10,adverseNextEvent11,adverseNextEvent12,adverseNextEvent13,adverseNextEvent14,adverseNextEvent15,adverseNextEvent16,taskReward]
    <;> norm_num
  have hp : rawVisits adverseNextS17Before [] = 16 := by decide
  have hn : rawVisits adverseNextS17Before ([]++[.query 1]) = 2 := by decide
  have hz : (controlPenalty savedCref uniformQuoteError unitRoleUnused .next) adverseNextS17Before [] (.query 1) = 0 := by
    apply control_penalty_empty_suffix
    exact AgentUCTNextExact.adverse_next_hyde_root_suffix_empty 16 (by omega)
  unfold indexScore
  rw [hs,hp,hn,hz]
  simp only [BackupStat.mean]
  norm_num

theorem adverseNextS17D0I2 : indexScore (7/5) (controlPenalty savedCref uniformQuoteError unitRoleUnused .next) adverseNextS17Before [] (.query 2) = treeIndex ((0/1)/2) (7/5) (nextNormalPenalty adverseNextS17Before) 16 2 := by
  have hs : replayBackup adverseNextS17Before emptyStatistics ([]++[.query 2]) = ⟨2,(0/1)⟩ := by
    rw [replayBackup_empty_closed_form]
    simp +decide [backedEvents,adverseNextS17Before,adverseNextProposal,adverseNextEvent1,adverseNextEvent2,adverseNextEvent3,adverseNextEvent4,adverseNextEvent5,adverseNextEvent6,adverseNextEvent7,adverseNextEvent8,adverseNextEvent9,adverseNextEvent10,adverseNextEvent11,adverseNextEvent12,adverseNextEvent13,adverseNextEvent14,adverseNextEvent15,adverseNextEvent16,taskReward]
    <;> norm_num
  have hp : rawVisits adverseNextS17Before [] = 16 := by decide
  have hn : rawVisits adverseNextS17Before ([]++[.query 2]) = 2 := by decide
  have hz : (controlPenalty savedCref uniformQuoteError unitRoleUnused .next) adverseNextS17Before [] (.query 2) = (nextNormalPenalty adverseNextS17Before) := by
    simpa only [adverseNextS17Before,nextNormalPenalty] using AgentUCTNextExact.adverse_next_normal_root_quotes_exact 16 (by omega) 2 (by decide)
  unfold indexScore
  rw [hs,hp,hn,hz]
  simp only [BackupStat.mean]
  norm_num

theorem adverseNextS17D0I3 : indexScore (7/5) (controlPenalty savedCref uniformQuoteError unitRoleUnused .next) adverseNextS17Before [] (.query 3) = treeIndex ((0/1)/2) (7/5) (nextNormalPenalty adverseNextS17Before) 16 2 := by
  have hs : replayBackup adverseNextS17Before emptyStatistics ([]++[.query 3]) = ⟨2,(0/1)⟩ := by
    rw [replayBackup_empty_closed_form]
    simp +decide [backedEvents,adverseNextS17Before,adverseNextProposal,adverseNextEvent1,adverseNextEvent2,adverseNextEvent3,adverseNextEvent4,adverseNextEvent5,adverseNextEvent6,adverseNextEvent7,adverseNextEvent8,adverseNextEvent9,adverseNextEvent10,adverseNextEvent11,adverseNextEvent12,adverseNextEvent13,adverseNextEvent14,adverseNextEvent15,adverseNextEvent16,taskReward]
    <;> norm_num
  have hp : rawVisits adverseNextS17Before [] = 16 := by decide
  have hn : rawVisits adverseNextS17Before ([]++[.query 3]) = 2 := by decide
  have hz : (controlPenalty savedCref uniformQuoteError unitRoleUnused .next) adverseNextS17Before [] (.query 3) = (nextNormalPenalty adverseNextS17Before) := by
    simpa only [adverseNextS17Before,nextNormalPenalty] using AgentUCTNextExact.adverse_next_normal_root_quotes_exact 16 (by omega) 3 (by decide)
  unfold indexScore
  rw [hs,hp,hn,hz]
  simp only [BackupStat.mean]
  norm_num

theorem adverseNextS17D0I4 : indexScore (7/5) (controlPenalty savedCref uniformQuoteError unitRoleUnused .next) adverseNextS17Before [] (.query 4) = treeIndex ((0/1)/2) (7/5) (nextNormalPenalty adverseNextS17Before) 16 2 := by
  have hs : replayBackup adverseNextS17Before emptyStatistics ([]++[.query 4]) = ⟨2,(0/1)⟩ := by
    rw [replayBackup_empty_closed_form]
    simp +decide [backedEvents,adverseNextS17Before,adverseNextProposal,adverseNextEvent1,adverseNextEvent2,adverseNextEvent3,adverseNextEvent4,adverseNextEvent5,adverseNextEvent6,adverseNextEvent7,adverseNextEvent8,adverseNextEvent9,adverseNextEvent10,adverseNextEvent11,adverseNextEvent12,adverseNextEvent13,adverseNextEvent14,adverseNextEvent15,adverseNextEvent16,taskReward]
    <;> norm_num
  have hp : rawVisits adverseNextS17Before [] = 16 := by decide
  have hn : rawVisits adverseNextS17Before ([]++[.query 4]) = 2 := by decide
  have hz : (controlPenalty savedCref uniformQuoteError unitRoleUnused .next) adverseNextS17Before [] (.query 4) = (nextNormalPenalty adverseNextS17Before) := by
    simpa only [adverseNextS17Before,nextNormalPenalty] using AgentUCTNextExact.adverse_next_normal_root_quotes_exact 16 (by omega) 4 (by decide)
  unfold indexScore
  rw [hs,hp,hn,hz]
  simp only [BackupStat.mean]
  norm_num

theorem adverseNextS17D0I5 : indexScore (7/5) (controlPenalty savedCref uniformQuoteError unitRoleUnused .next) adverseNextS17Before [] (.query 5) = treeIndex ((9/10)/2) (7/5) (nextNormalPenalty adverseNextS17Before) 16 2 := by
  have hs : replayBackup adverseNextS17Before emptyStatistics ([]++[.query 5]) = ⟨2,(9/10)⟩ := by
    rw [replayBackup_empty_closed_form]
    simp +decide [backedEvents,adverseNextS17Before,adverseNextProposal,adverseNextEvent1,adverseNextEvent2,adverseNextEvent3,adverseNextEvent4,adverseNextEvent5,adverseNextEvent6,adverseNextEvent7,adverseNextEvent8,adverseNextEvent9,adverseNextEvent10,adverseNextEvent11,adverseNextEvent12,adverseNextEvent13,adverseNextEvent14,adverseNextEvent15,adverseNextEvent16,taskReward]
    <;> norm_num
  have hp : rawVisits adverseNextS17Before [] = 16 := by decide
  have hn : rawVisits adverseNextS17Before ([]++[.query 5]) = 2 := by decide
  have hz : (controlPenalty savedCref uniformQuoteError unitRoleUnused .next) adverseNextS17Before [] (.query 5) = (nextNormalPenalty adverseNextS17Before) := by
    simpa only [adverseNextS17Before,nextNormalPenalty] using AgentUCTNextExact.adverse_next_normal_root_quotes_exact 16 (by omega) 5 (by decide)
  unfold indexScore
  rw [hs,hp,hn,hz]
  simp only [BackupStat.mean]
  norm_num

theorem adverseNextS17D0I6 : indexScore (7/5) (controlPenalty savedCref uniformQuoteError unitRoleUnused .next) adverseNextS17Before [] (.query 6) = treeIndex ((0/1)/2) (7/5) (nextNormalPenalty adverseNextS17Before) 16 2 := by
  have hs : replayBackup adverseNextS17Before emptyStatistics ([]++[.query 6]) = ⟨2,(0/1)⟩ := by
    rw [replayBackup_empty_closed_form]
    simp +decide [backedEvents,adverseNextS17Before,adverseNextProposal,adverseNextEvent1,adverseNextEvent2,adverseNextEvent3,adverseNextEvent4,adverseNextEvent5,adverseNextEvent6,adverseNextEvent7,adverseNextEvent8,adverseNextEvent9,adverseNextEvent10,adverseNextEvent11,adverseNextEvent12,adverseNextEvent13,adverseNextEvent14,adverseNextEvent15,adverseNextEvent16,taskReward]
    <;> norm_num
  have hp : rawVisits adverseNextS17Before [] = 16 := by decide
  have hn : rawVisits adverseNextS17Before ([]++[.query 6]) = 2 := by decide
  have hz : (controlPenalty savedCref uniformQuoteError unitRoleUnused .next) adverseNextS17Before [] (.query 6) = (nextNormalPenalty adverseNextS17Before) := by
    simpa only [adverseNextS17Before,nextNormalPenalty] using AgentUCTNextExact.adverse_next_normal_root_quotes_exact 16 (by omega) 6 (by decide)
  unfold indexScore
  rw [hs,hp,hn,hz]
  simp only [BackupStat.mean]
  norm_num

theorem adverseNextS17D0I7 : indexScore (7/5) (controlPenalty savedCref uniformQuoteError unitRoleUnused .next) adverseNextS17Before [] (.query 7) = treeIndex ((0/1)/2) (7/5) (nextNormalPenalty adverseNextS17Before) 16 2 := by
  have hs : replayBackup adverseNextS17Before emptyStatistics ([]++[.query 7]) = ⟨2,(0/1)⟩ := by
    rw [replayBackup_empty_closed_form]
    simp +decide [backedEvents,adverseNextS17Before,adverseNextProposal,adverseNextEvent1,adverseNextEvent2,adverseNextEvent3,adverseNextEvent4,adverseNextEvent5,adverseNextEvent6,adverseNextEvent7,adverseNextEvent8,adverseNextEvent9,adverseNextEvent10,adverseNextEvent11,adverseNextEvent12,adverseNextEvent13,adverseNextEvent14,adverseNextEvent15,adverseNextEvent16,taskReward]
    <;> norm_num
  have hp : rawVisits adverseNextS17Before [] = 16 := by decide
  have hn : rawVisits adverseNextS17Before ([]++[.query 7]) = 2 := by decide
  have hz : (controlPenalty savedCref uniformQuoteError unitRoleUnused .next) adverseNextS17Before [] (.query 7) = (nextNormalPenalty adverseNextS17Before) := by
    simpa only [adverseNextS17Before,nextNormalPenalty] using AgentUCTNextExact.adverse_next_normal_root_quotes_exact 16 (by omega) 7 (by decide)
  unfold indexScore
  rw [hs,hp,hn,hz]
  simp only [BackupStat.mean]
  norm_num

theorem adverseNextS17D0Cmp0 : indexScore (7/5) (controlPenalty savedCref uniformQuoteError unitRoleUnused .next) adverseNextS17Before [] (.query 0) < indexScore (7/5) (controlPenalty savedCref uniformQuoteError unitRoleUnused .next) adverseNextS17Before [] (.query 5) := by
  rw [adverseNextS17D0I0,adverseNextS17D0I5]
  have hk := adverse_next_penalty_interval 16 (by omega)
  change nextNormalPenaltyLower ≤ nextNormalPenalty adverseNextS17Before ∧ nextNormalPenalty adverseNextS17Before ≤ nextNormalPenaltyUpper at hk
  have hm : ((0/1)/2)+(8331491/5000000)-(nextNormalPenalty adverseNextS17Before) < ((9/10)/2)+(5207181/3125000)-(nextNormalPenalty adverseNextS17Before) := by
    have h : (((0/1)/2)+(8331491/5000000) : ℝ) < ((9/10)/2)+(5207181/3125000) := by norm_num
    linarith
  have h := index_strict_order_from_intervals ((9/10)/2) ((0/1)/2) (nextNormalPenalty adverseNextS17Before) (nextNormalPenalty adverseNextS17Before) (5207181/3125000) (8331491/5000000)
    (treeBonus (7/5) 16 2) (treeBonus (7/5) 16 2)
    (trajectory_bonus_16_2).1 (trajectory_bonus_16_2).2 hm
  simpa only [treeIndex] using h

theorem adverseNextS17D0Cmp1 : indexScore (7/5) (controlPenalty savedCref uniformQuoteError unitRoleUnused .next) adverseNextS17Before [] (.query 1) < indexScore (7/5) (controlPenalty savedCref uniformQuoteError unitRoleUnused .next) adverseNextS17Before [] (.query 5) := by
  rw [adverseNextS17D0I1,adverseNextS17D0I5]
  have hk := adverse_next_penalty_interval 16 (by omega)
  change nextNormalPenaltyLower ≤ nextNormalPenalty adverseNextS17Before ∧ nextNormalPenalty adverseNextS17Before ≤ nextNormalPenaltyUpper at hk
  have hm : ((0/1)/2)+(8331491/5000000)-0 < ((9/10)/2)+(5207181/3125000)-(nextNormalPenalty adverseNextS17Before) := by
    have h : ((0/1)/2)+(8331491/5000000) < ((9/10)/2)+(5207181/3125000)-nextNormalPenaltyUpper := by norm_num [nextNormalPenaltyUpper,savedCref,uniformQuoteError]
    linarith [hk.2]
  have h := index_strict_order_from_intervals ((9/10)/2) ((0/1)/2) (nextNormalPenalty adverseNextS17Before) 0 (5207181/3125000) (8331491/5000000)
    (treeBonus (7/5) 16 2) (treeBonus (7/5) 16 2)
    (trajectory_bonus_16_2).1 (trajectory_bonus_16_2).2 hm
  simpa only [treeIndex] using h

theorem adverseNextS17D0Cmp2 : indexScore (7/5) (controlPenalty savedCref uniformQuoteError unitRoleUnused .next) adverseNextS17Before [] (.query 2) < indexScore (7/5) (controlPenalty savedCref uniformQuoteError unitRoleUnused .next) adverseNextS17Before [] (.query 5) := by
  rw [adverseNextS17D0I2,adverseNextS17D0I5]
  have hk := adverse_next_penalty_interval 16 (by omega)
  change nextNormalPenaltyLower ≤ nextNormalPenalty adverseNextS17Before ∧ nextNormalPenalty adverseNextS17Before ≤ nextNormalPenaltyUpper at hk
  have hm : ((0/1)/2)+(8331491/5000000)-(nextNormalPenalty adverseNextS17Before) < ((9/10)/2)+(5207181/3125000)-(nextNormalPenalty adverseNextS17Before) := by
    have h : (((0/1)/2)+(8331491/5000000) : ℝ) < ((9/10)/2)+(5207181/3125000) := by norm_num
    linarith
  have h := index_strict_order_from_intervals ((9/10)/2) ((0/1)/2) (nextNormalPenalty adverseNextS17Before) (nextNormalPenalty adverseNextS17Before) (5207181/3125000) (8331491/5000000)
    (treeBonus (7/5) 16 2) (treeBonus (7/5) 16 2)
    (trajectory_bonus_16_2).1 (trajectory_bonus_16_2).2 hm
  simpa only [treeIndex] using h

theorem adverseNextS17D0Cmp3 : indexScore (7/5) (controlPenalty savedCref uniformQuoteError unitRoleUnused .next) adverseNextS17Before [] (.query 3) < indexScore (7/5) (controlPenalty savedCref uniformQuoteError unitRoleUnused .next) adverseNextS17Before [] (.query 5) := by
  rw [adverseNextS17D0I3,adverseNextS17D0I5]
  have hk := adverse_next_penalty_interval 16 (by omega)
  change nextNormalPenaltyLower ≤ nextNormalPenalty adverseNextS17Before ∧ nextNormalPenalty adverseNextS17Before ≤ nextNormalPenaltyUpper at hk
  have hm : ((0/1)/2)+(8331491/5000000)-(nextNormalPenalty adverseNextS17Before) < ((9/10)/2)+(5207181/3125000)-(nextNormalPenalty adverseNextS17Before) := by
    have h : (((0/1)/2)+(8331491/5000000) : ℝ) < ((9/10)/2)+(5207181/3125000) := by norm_num
    linarith
  have h := index_strict_order_from_intervals ((9/10)/2) ((0/1)/2) (nextNormalPenalty adverseNextS17Before) (nextNormalPenalty adverseNextS17Before) (5207181/3125000) (8331491/5000000)
    (treeBonus (7/5) 16 2) (treeBonus (7/5) 16 2)
    (trajectory_bonus_16_2).1 (trajectory_bonus_16_2).2 hm
  simpa only [treeIndex] using h

theorem adverseNextS17D0Cmp4 : indexScore (7/5) (controlPenalty savedCref uniformQuoteError unitRoleUnused .next) adverseNextS17Before [] (.query 4) < indexScore (7/5) (controlPenalty savedCref uniformQuoteError unitRoleUnused .next) adverseNextS17Before [] (.query 5) := by
  rw [adverseNextS17D0I4,adverseNextS17D0I5]
  have hk := adverse_next_penalty_interval 16 (by omega)
  change nextNormalPenaltyLower ≤ nextNormalPenalty adverseNextS17Before ∧ nextNormalPenalty adverseNextS17Before ≤ nextNormalPenaltyUpper at hk
  have hm : ((0/1)/2)+(8331491/5000000)-(nextNormalPenalty adverseNextS17Before) < ((9/10)/2)+(5207181/3125000)-(nextNormalPenalty adverseNextS17Before) := by
    have h : (((0/1)/2)+(8331491/5000000) : ℝ) < ((9/10)/2)+(5207181/3125000) := by norm_num
    linarith
  have h := index_strict_order_from_intervals ((9/10)/2) ((0/1)/2) (nextNormalPenalty adverseNextS17Before) (nextNormalPenalty adverseNextS17Before) (5207181/3125000) (8331491/5000000)
    (treeBonus (7/5) 16 2) (treeBonus (7/5) 16 2)
    (trajectory_bonus_16_2).1 (trajectory_bonus_16_2).2 hm
  simpa only [treeIndex] using h

theorem adverseNextS17D0Cmp6 : indexScore (7/5) (controlPenalty savedCref uniformQuoteError unitRoleUnused .next) adverseNextS17Before [] (.query 6) ≤ indexScore (7/5) (controlPenalty savedCref uniformQuoteError unitRoleUnused .next) adverseNextS17Before [] (.query 5) := by
  rw [adverseNextS17D0I6,adverseNextS17D0I5]
  have hk := adverse_next_penalty_interval 16 (by omega)
  change nextNormalPenaltyLower ≤ nextNormalPenalty adverseNextS17Before ∧ nextNormalPenalty adverseNextS17Before ≤ nextNormalPenaltyUpper at hk
  have hm : ((0/1)/2)+(8331491/5000000)-(nextNormalPenalty adverseNextS17Before) < ((9/10)/2)+(5207181/3125000)-(nextNormalPenalty adverseNextS17Before) := by
    have h : (((0/1)/2)+(8331491/5000000) : ℝ) < ((9/10)/2)+(5207181/3125000) := by norm_num
    linarith
  have h := index_weak_order_from_intervals ((9/10)/2) ((0/1)/2) (nextNormalPenalty adverseNextS17Before) (nextNormalPenalty adverseNextS17Before) (5207181/3125000) (8331491/5000000)
    (treeBonus (7/5) 16 2) (treeBonus (7/5) 16 2)
    (trajectory_bonus_16_2).1 (trajectory_bonus_16_2).2 hm.le
  simpa only [treeIndex] using h

theorem adverseNextS17D0Cmp7 : indexScore (7/5) (controlPenalty savedCref uniformQuoteError unitRoleUnused .next) adverseNextS17Before [] (.query 7) ≤ indexScore (7/5) (controlPenalty savedCref uniformQuoteError unitRoleUnused .next) adverseNextS17Before [] (.query 5) := by
  rw [adverseNextS17D0I7,adverseNextS17D0I5]
  have hk := adverse_next_penalty_interval 16 (by omega)
  change nextNormalPenaltyLower ≤ nextNormalPenalty adverseNextS17Before ∧ nextNormalPenalty adverseNextS17Before ≤ nextNormalPenaltyUpper at hk
  have hm : ((0/1)/2)+(8331491/5000000)-(nextNormalPenalty adverseNextS17Before) < ((9/10)/2)+(5207181/3125000)-(nextNormalPenalty adverseNextS17Before) := by
    have h : (((0/1)/2)+(8331491/5000000) : ℝ) < ((9/10)/2)+(5207181/3125000) := by norm_num
    linarith
  have h := index_weak_order_from_intervals ((9/10)/2) ((0/1)/2) (nextNormalPenalty adverseNextS17Before) (nextNormalPenalty adverseNextS17Before) (5207181/3125000) (8331491/5000000)
    (treeBonus (7/5) 16 2) (treeBonus (7/5) 16 2)
    (trajectory_bonus_16_2).1 (trajectory_bonus_16_2).2 hm.le
  simpa only [treeIndex] using h

theorem adverseNextS17Choice0 : nativeFirstChoice (indexScore (7/5) (controlPenalty savedCref uniformQuoteError unitRoleUnused .next) adverseNextS17Before []) adverseNextS17Before [] = .query 5 := by
  apply visited_choice_from_ordered_certificate _ _ [] [.query 0,.query 1,.query 2,.query 3,.query 4] [.query 6,.query 7] (.query 5) (by decide)
  · intro a ha
    have ho : orderedLegalAvailable [] = [.query 0,.query 1,.query 2,.query 3,.query 4,.query 5,.query 6,.query 7] := by decide
    rw [ho] at ha
    simp only [List.mem_cons,List.not_mem_nil,or_false] at ha
    rcases ha with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> decide
  · intro a ha
    simp only [List.mem_cons,List.not_mem_nil,or_false] at ha
    rcases ha with rfl | rfl | rfl | rfl | rfl
    · exact adverseNextS17D0Cmp0
    · exact adverseNextS17D0Cmp1
    · exact adverseNextS17D0Cmp2
    · exact adverseNextS17D0Cmp3
    · exact adverseNextS17D0Cmp4
  · intro a ha
    simp only [List.mem_cons,List.not_mem_nil,or_false] at ha
    rcases ha with rfl | rfl
    · exact adverseNextS17D0Cmp6
    · exact adverseNextS17D0Cmp7

theorem adverseNextS17ActualEvent : nativeEvent budgetTape (7/5) (controlPenalty savedCref uniformQuoteError unitRoleUnused .next)
    (taskReward true (2/5) (1/2)) adverseNextS17Before = adverseNextEvent17 := by
  have hs0 := native_select_existing_step budgetTape (7/5) (controlPenalty savedCref uniformQuoteError unitRoleUnused .next) adverseNextS17Before 8 [] (.query 5)
    (by decide) (by decide) adverseNextS17Choice0
  have hnew := native_select_new_step budgetTape (7/5) (controlPenalty savedCref uniformQuoteError unitRoleUnused .next) adverseNextS17Before 7 [.query 5]
    [.normalRetriever 4,.normalRetriever 6,.normalRetriever 7,.normalRetriever 8,.normalRetriever 5,.normalRetriever 0,.normalRetriever 2,.normalRetriever 3,.normalRetriever 12,.normalRetriever 14,.normalRetriever 13,.normalRetriever 21,.normalRetriever 23,.normalRetriever 22,.normalRetriever 9,.normalRetriever 11,.normalRetriever 10,.normalRetriever 15,.normalRetriever 17,.normalRetriever 16,.normalRetriever 18,.normalRetriever 20,.normalRetriever 19,.normalRetriever 24,.normalRetriever 25,.normalRetriever 26,.normalRetriever 27,.normalRetriever 28,.normalRetriever 29] (.normalRetriever 0) (by decide) (by decide) (by decide) (by decide)
  have hs : nativeSelect budgetTape (7/5) (controlPenalty savedCref uniformQuoteError unitRoleUnused .next) adverseNextS17Before 9 [] = [.query 5,.normalRetriever 0] := by
    rw [hs0]
    change nativeSelect budgetTape (7/5) (controlPenalty savedCref uniformQuoteError unitRoleUnused .next) adverseNextS17Before 8 [.query 5] = _
    rw [hnew] <;> rfl
  have hr : repairedRollout budgetTape adverseNextS17Before 9 [.query 5,.normalRetriever 0] = [.query 5,.normalRetriever 0,.selection 0,.width 0,.stop,.reranker 0,.topm 0,.context 0,.answer 0] := by decide
  simp only [nativeEvent,hs,hr]
  rfl

def adverseNextS18Before := adverseNextProposal.take 17

theorem adverseNextS18D0I0 : indexScore (7/5) (controlPenalty savedCref uniformQuoteError unitRoleUnused .next) adverseNextS18Before [] (.query 0) = treeIndex ((0/1)/2) (7/5) (nextNormalPenalty adverseNextS18Before) 17 2 := by
  have hs : replayBackup adverseNextS18Before emptyStatistics ([]++[.query 0]) = ⟨2,(0/1)⟩ := by
    rw [replayBackup_empty_closed_form]
    simp +decide [backedEvents,adverseNextS18Before,adverseNextProposal,adverseNextEvent1,adverseNextEvent2,adverseNextEvent3,adverseNextEvent4,adverseNextEvent5,adverseNextEvent6,adverseNextEvent7,adverseNextEvent8,adverseNextEvent9,adverseNextEvent10,adverseNextEvent11,adverseNextEvent12,adverseNextEvent13,adverseNextEvent14,adverseNextEvent15,adverseNextEvent16,adverseNextEvent17,taskReward]
    <;> norm_num
  have hp : rawVisits adverseNextS18Before [] = 17 := by decide
  have hn : rawVisits adverseNextS18Before ([]++[.query 0]) = 2 := by decide
  have hz : (controlPenalty savedCref uniformQuoteError unitRoleUnused .next) adverseNextS18Before [] (.query 0) = (nextNormalPenalty adverseNextS18Before) := by
    simpa only [adverseNextS18Before,nextNormalPenalty] using AgentUCTNextExact.adverse_next_normal_root_quotes_exact 17 (by omega) 0 (by decide)
  unfold indexScore
  rw [hs,hp,hn,hz]
  simp only [BackupStat.mean]
  norm_num

theorem adverseNextS18D0I1 : indexScore (7/5) (controlPenalty savedCref uniformQuoteError unitRoleUnused .next) adverseNextS18Before [] (.query 1) = treeIndex ((0/1)/2) (7/5) 0 17 2 := by
  have hs : replayBackup adverseNextS18Before emptyStatistics ([]++[.query 1]) = ⟨2,(0/1)⟩ := by
    rw [replayBackup_empty_closed_form]
    simp +decide [backedEvents,adverseNextS18Before,adverseNextProposal,adverseNextEvent1,adverseNextEvent2,adverseNextEvent3,adverseNextEvent4,adverseNextEvent5,adverseNextEvent6,adverseNextEvent7,adverseNextEvent8,adverseNextEvent9,adverseNextEvent10,adverseNextEvent11,adverseNextEvent12,adverseNextEvent13,adverseNextEvent14,adverseNextEvent15,adverseNextEvent16,adverseNextEvent17,taskReward]
    <;> norm_num
  have hp : rawVisits adverseNextS18Before [] = 17 := by decide
  have hn : rawVisits adverseNextS18Before ([]++[.query 1]) = 2 := by decide
  have hz : (controlPenalty savedCref uniformQuoteError unitRoleUnused .next) adverseNextS18Before [] (.query 1) = 0 := by
    apply control_penalty_empty_suffix
    exact AgentUCTNextExact.adverse_next_hyde_root_suffix_empty 17 (by omega)
  unfold indexScore
  rw [hs,hp,hn,hz]
  simp only [BackupStat.mean]
  norm_num

theorem adverseNextS18D0I2 : indexScore (7/5) (controlPenalty savedCref uniformQuoteError unitRoleUnused .next) adverseNextS18Before [] (.query 2) = treeIndex ((0/1)/2) (7/5) (nextNormalPenalty adverseNextS18Before) 17 2 := by
  have hs : replayBackup adverseNextS18Before emptyStatistics ([]++[.query 2]) = ⟨2,(0/1)⟩ := by
    rw [replayBackup_empty_closed_form]
    simp +decide [backedEvents,adverseNextS18Before,adverseNextProposal,adverseNextEvent1,adverseNextEvent2,adverseNextEvent3,adverseNextEvent4,adverseNextEvent5,adverseNextEvent6,adverseNextEvent7,adverseNextEvent8,adverseNextEvent9,adverseNextEvent10,adverseNextEvent11,adverseNextEvent12,adverseNextEvent13,adverseNextEvent14,adverseNextEvent15,adverseNextEvent16,adverseNextEvent17,taskReward]
    <;> norm_num
  have hp : rawVisits adverseNextS18Before [] = 17 := by decide
  have hn : rawVisits adverseNextS18Before ([]++[.query 2]) = 2 := by decide
  have hz : (controlPenalty savedCref uniformQuoteError unitRoleUnused .next) adverseNextS18Before [] (.query 2) = (nextNormalPenalty adverseNextS18Before) := by
    simpa only [adverseNextS18Before,nextNormalPenalty] using AgentUCTNextExact.adverse_next_normal_root_quotes_exact 17 (by omega) 2 (by decide)
  unfold indexScore
  rw [hs,hp,hn,hz]
  simp only [BackupStat.mean]
  norm_num

theorem adverseNextS18D0I3 : indexScore (7/5) (controlPenalty savedCref uniformQuoteError unitRoleUnused .next) adverseNextS18Before [] (.query 3) = treeIndex ((0/1)/2) (7/5) (nextNormalPenalty adverseNextS18Before) 17 2 := by
  have hs : replayBackup adverseNextS18Before emptyStatistics ([]++[.query 3]) = ⟨2,(0/1)⟩ := by
    rw [replayBackup_empty_closed_form]
    simp +decide [backedEvents,adverseNextS18Before,adverseNextProposal,adverseNextEvent1,adverseNextEvent2,adverseNextEvent3,adverseNextEvent4,adverseNextEvent5,adverseNextEvent6,adverseNextEvent7,adverseNextEvent8,adverseNextEvent9,adverseNextEvent10,adverseNextEvent11,adverseNextEvent12,adverseNextEvent13,adverseNextEvent14,adverseNextEvent15,adverseNextEvent16,adverseNextEvent17,taskReward]
    <;> norm_num
  have hp : rawVisits adverseNextS18Before [] = 17 := by decide
  have hn : rawVisits adverseNextS18Before ([]++[.query 3]) = 2 := by decide
  have hz : (controlPenalty savedCref uniformQuoteError unitRoleUnused .next) adverseNextS18Before [] (.query 3) = (nextNormalPenalty adverseNextS18Before) := by
    simpa only [adverseNextS18Before,nextNormalPenalty] using AgentUCTNextExact.adverse_next_normal_root_quotes_exact 17 (by omega) 3 (by decide)
  unfold indexScore
  rw [hs,hp,hn,hz]
  simp only [BackupStat.mean]
  norm_num

theorem adverseNextS18D0I4 : indexScore (7/5) (controlPenalty savedCref uniformQuoteError unitRoleUnused .next) adverseNextS18Before [] (.query 4) = treeIndex ((0/1)/2) (7/5) (nextNormalPenalty adverseNextS18Before) 17 2 := by
  have hs : replayBackup adverseNextS18Before emptyStatistics ([]++[.query 4]) = ⟨2,(0/1)⟩ := by
    rw [replayBackup_empty_closed_form]
    simp +decide [backedEvents,adverseNextS18Before,adverseNextProposal,adverseNextEvent1,adverseNextEvent2,adverseNextEvent3,adverseNextEvent4,adverseNextEvent5,adverseNextEvent6,adverseNextEvent7,adverseNextEvent8,adverseNextEvent9,adverseNextEvent10,adverseNextEvent11,adverseNextEvent12,adverseNextEvent13,adverseNextEvent14,adverseNextEvent15,adverseNextEvent16,adverseNextEvent17,taskReward]
    <;> norm_num
  have hp : rawVisits adverseNextS18Before [] = 17 := by decide
  have hn : rawVisits adverseNextS18Before ([]++[.query 4]) = 2 := by decide
  have hz : (controlPenalty savedCref uniformQuoteError unitRoleUnused .next) adverseNextS18Before [] (.query 4) = (nextNormalPenalty adverseNextS18Before) := by
    simpa only [adverseNextS18Before,nextNormalPenalty] using AgentUCTNextExact.adverse_next_normal_root_quotes_exact 17 (by omega) 4 (by decide)
  unfold indexScore
  rw [hs,hp,hn,hz]
  simp only [BackupStat.mean]
  norm_num

theorem adverseNextS18D0I5 : indexScore (7/5) (controlPenalty savedCref uniformQuoteError unitRoleUnused .next) adverseNextS18Before [] (.query 5) = treeIndex ((13/10)/3) (7/5) (nextNormalPenalty adverseNextS18Before) 17 3 := by
  have hs : replayBackup adverseNextS18Before emptyStatistics ([]++[.query 5]) = ⟨3,(13/10)⟩ := by
    rw [replayBackup_empty_closed_form]
    simp +decide [backedEvents,adverseNextS18Before,adverseNextProposal,adverseNextEvent1,adverseNextEvent2,adverseNextEvent3,adverseNextEvent4,adverseNextEvent5,adverseNextEvent6,adverseNextEvent7,adverseNextEvent8,adverseNextEvent9,adverseNextEvent10,adverseNextEvent11,adverseNextEvent12,adverseNextEvent13,adverseNextEvent14,adverseNextEvent15,adverseNextEvent16,adverseNextEvent17,taskReward]
    <;> norm_num
  have hp : rawVisits adverseNextS18Before [] = 17 := by decide
  have hn : rawVisits adverseNextS18Before ([]++[.query 5]) = 3 := by decide
  have hz : (controlPenalty savedCref uniformQuoteError unitRoleUnused .next) adverseNextS18Before [] (.query 5) = (nextNormalPenalty adverseNextS18Before) := by
    simpa only [adverseNextS18Before,nextNormalPenalty] using AgentUCTNextExact.adverse_next_normal_root_quotes_exact 17 (by omega) 5 (by decide)
  unfold indexScore
  rw [hs,hp,hn,hz]
  simp only [BackupStat.mean]
  norm_num

theorem adverseNextS18D0I6 : indexScore (7/5) (controlPenalty savedCref uniformQuoteError unitRoleUnused .next) adverseNextS18Before [] (.query 6) = treeIndex ((0/1)/2) (7/5) (nextNormalPenalty adverseNextS18Before) 17 2 := by
  have hs : replayBackup adverseNextS18Before emptyStatistics ([]++[.query 6]) = ⟨2,(0/1)⟩ := by
    rw [replayBackup_empty_closed_form]
    simp +decide [backedEvents,adverseNextS18Before,adverseNextProposal,adverseNextEvent1,adverseNextEvent2,adverseNextEvent3,adverseNextEvent4,adverseNextEvent5,adverseNextEvent6,adverseNextEvent7,adverseNextEvent8,adverseNextEvent9,adverseNextEvent10,adverseNextEvent11,adverseNextEvent12,adverseNextEvent13,adverseNextEvent14,adverseNextEvent15,adverseNextEvent16,adverseNextEvent17,taskReward]
    <;> norm_num
  have hp : rawVisits adverseNextS18Before [] = 17 := by decide
  have hn : rawVisits adverseNextS18Before ([]++[.query 6]) = 2 := by decide
  have hz : (controlPenalty savedCref uniformQuoteError unitRoleUnused .next) adverseNextS18Before [] (.query 6) = (nextNormalPenalty adverseNextS18Before) := by
    simpa only [adverseNextS18Before,nextNormalPenalty] using AgentUCTNextExact.adverse_next_normal_root_quotes_exact 17 (by omega) 6 (by decide)
  unfold indexScore
  rw [hs,hp,hn,hz]
  simp only [BackupStat.mean]
  norm_num

theorem adverseNextS18D0I7 : indexScore (7/5) (controlPenalty savedCref uniformQuoteError unitRoleUnused .next) adverseNextS18Before [] (.query 7) = treeIndex ((0/1)/2) (7/5) (nextNormalPenalty adverseNextS18Before) 17 2 := by
  have hs : replayBackup adverseNextS18Before emptyStatistics ([]++[.query 7]) = ⟨2,(0/1)⟩ := by
    rw [replayBackup_empty_closed_form]
    simp +decide [backedEvents,adverseNextS18Before,adverseNextProposal,adverseNextEvent1,adverseNextEvent2,adverseNextEvent3,adverseNextEvent4,adverseNextEvent5,adverseNextEvent6,adverseNextEvent7,adverseNextEvent8,adverseNextEvent9,adverseNextEvent10,adverseNextEvent11,adverseNextEvent12,adverseNextEvent13,adverseNextEvent14,adverseNextEvent15,adverseNextEvent16,adverseNextEvent17,taskReward]
    <;> norm_num
  have hp : rawVisits adverseNextS18Before [] = 17 := by decide
  have hn : rawVisits adverseNextS18Before ([]++[.query 7]) = 2 := by decide
  have hz : (controlPenalty savedCref uniformQuoteError unitRoleUnused .next) adverseNextS18Before [] (.query 7) = (nextNormalPenalty adverseNextS18Before) := by
    simpa only [adverseNextS18Before,nextNormalPenalty] using AgentUCTNextExact.adverse_next_normal_root_quotes_exact 17 (by omega) 7 (by decide)
  unfold indexScore
  rw [hs,hp,hn,hz]
  simp only [BackupStat.mean]
  norm_num

theorem adverseNextS18D0Cmp0 : indexScore (7/5) (controlPenalty savedCref uniformQuoteError unitRoleUnused .next) adverseNextS18Before [] (.query 0) < indexScore (7/5) (controlPenalty savedCref uniformQuoteError unitRoleUnused .next) adverseNextS18Before [] (.query 1) := by
  rw [adverseNextS18D0I0,adverseNextS18D0I1]
  have hk := adverse_next_penalty_interval 17 (by omega)
  change nextNormalPenaltyLower ≤ nextNormalPenalty adverseNextS18Before ∧ nextNormalPenalty adverseNextS18Before ≤ nextNormalPenaltyUpper at hk
  have hm : ((0/1)/2)+(84151123/50000000)-(nextNormalPenalty adverseNextS18Before) < ((0/1)/2)+(21037779/12500000)-0 := by
    have h : ((0/1)/2)+(84151123/50000000)-nextNormalPenaltyLower < ((0/1)/2)+(21037779/12500000) := by norm_num [nextNormalPenaltyLower,savedCref,uniformQuoteError]
    linarith [hk.1]
  have h := index_strict_order_from_intervals ((0/1)/2) ((0/1)/2) 0 (nextNormalPenalty adverseNextS18Before) (21037779/12500000) (84151123/50000000)
    (treeBonus (7/5) 17 2) (treeBonus (7/5) 17 2)
    (trajectory_bonus_17_2).1 (trajectory_bonus_17_2).2 hm
  simpa only [treeIndex] using h

theorem adverseNextS18D0Cmp2 : indexScore (7/5) (controlPenalty savedCref uniformQuoteError unitRoleUnused .next) adverseNextS18Before [] (.query 2) ≤ indexScore (7/5) (controlPenalty savedCref uniformQuoteError unitRoleUnused .next) adverseNextS18Before [] (.query 1) := by
  rw [adverseNextS18D0I2,adverseNextS18D0I1]
  have hk := adverse_next_penalty_interval 17 (by omega)
  change nextNormalPenaltyLower ≤ nextNormalPenalty adverseNextS18Before ∧ nextNormalPenalty adverseNextS18Before ≤ nextNormalPenaltyUpper at hk
  have hm : ((0/1)/2)+(84151123/50000000)-(nextNormalPenalty adverseNextS18Before) < ((0/1)/2)+(21037779/12500000)-0 := by
    have h : ((0/1)/2)+(84151123/50000000)-nextNormalPenaltyLower < ((0/1)/2)+(21037779/12500000) := by norm_num [nextNormalPenaltyLower,savedCref,uniformQuoteError]
    linarith [hk.1]
  have h := index_weak_order_from_intervals ((0/1)/2) ((0/1)/2) 0 (nextNormalPenalty adverseNextS18Before) (21037779/12500000) (84151123/50000000)
    (treeBonus (7/5) 17 2) (treeBonus (7/5) 17 2)
    (trajectory_bonus_17_2).1 (trajectory_bonus_17_2).2 hm.le
  simpa only [treeIndex] using h

theorem adverseNextS18D0Cmp3 : indexScore (7/5) (controlPenalty savedCref uniformQuoteError unitRoleUnused .next) adverseNextS18Before [] (.query 3) ≤ indexScore (7/5) (controlPenalty savedCref uniformQuoteError unitRoleUnused .next) adverseNextS18Before [] (.query 1) := by
  rw [adverseNextS18D0I3,adverseNextS18D0I1]
  have hk := adverse_next_penalty_interval 17 (by omega)
  change nextNormalPenaltyLower ≤ nextNormalPenalty adverseNextS18Before ∧ nextNormalPenalty adverseNextS18Before ≤ nextNormalPenaltyUpper at hk
  have hm : ((0/1)/2)+(84151123/50000000)-(nextNormalPenalty adverseNextS18Before) < ((0/1)/2)+(21037779/12500000)-0 := by
    have h : ((0/1)/2)+(84151123/50000000)-nextNormalPenaltyLower < ((0/1)/2)+(21037779/12500000) := by norm_num [nextNormalPenaltyLower,savedCref,uniformQuoteError]
    linarith [hk.1]
  have h := index_weak_order_from_intervals ((0/1)/2) ((0/1)/2) 0 (nextNormalPenalty adverseNextS18Before) (21037779/12500000) (84151123/50000000)
    (treeBonus (7/5) 17 2) (treeBonus (7/5) 17 2)
    (trajectory_bonus_17_2).1 (trajectory_bonus_17_2).2 hm.le
  simpa only [treeIndex] using h

theorem adverseNextS18D0Cmp4 : indexScore (7/5) (controlPenalty savedCref uniformQuoteError unitRoleUnused .next) adverseNextS18Before [] (.query 4) ≤ indexScore (7/5) (controlPenalty savedCref uniformQuoteError unitRoleUnused .next) adverseNextS18Before [] (.query 1) := by
  rw [adverseNextS18D0I4,adverseNextS18D0I1]
  have hk := adverse_next_penalty_interval 17 (by omega)
  change nextNormalPenaltyLower ≤ nextNormalPenalty adverseNextS18Before ∧ nextNormalPenalty adverseNextS18Before ≤ nextNormalPenaltyUpper at hk
  have hm : ((0/1)/2)+(84151123/50000000)-(nextNormalPenalty adverseNextS18Before) < ((0/1)/2)+(21037779/12500000)-0 := by
    have h : ((0/1)/2)+(84151123/50000000)-nextNormalPenaltyLower < ((0/1)/2)+(21037779/12500000) := by norm_num [nextNormalPenaltyLower,savedCref,uniformQuoteError]
    linarith [hk.1]
  have h := index_weak_order_from_intervals ((0/1)/2) ((0/1)/2) 0 (nextNormalPenalty adverseNextS18Before) (21037779/12500000) (84151123/50000000)
    (treeBonus (7/5) 17 2) (treeBonus (7/5) 17 2)
    (trajectory_bonus_17_2).1 (trajectory_bonus_17_2).2 hm.le
  simpa only [treeIndex] using h

theorem adverseNextS18D0Cmp5 : indexScore (7/5) (controlPenalty savedCref uniformQuoteError unitRoleUnused .next) adverseNextS18Before [] (.query 5) ≤ indexScore (7/5) (controlPenalty savedCref uniformQuoteError unitRoleUnused .next) adverseNextS18Before [] (.query 1) := by
  rw [adverseNextS18D0I5,adverseNextS18D0I1]
  have hk := adverse_next_penalty_interval 17 (by omega)
  change nextNormalPenaltyLower ≤ nextNormalPenalty adverseNextS18Before ∧ nextNormalPenalty adverseNextS18Before ≤ nextNormalPenaltyUpper at hk
  have hm : ((13/10)/3)+(68709109/50000000)-(nextNormalPenalty adverseNextS18Before) < ((0/1)/2)+(21037779/12500000)-0 := by
    have h : ((13/10)/3)+(68709109/50000000)-nextNormalPenaltyLower < ((0/1)/2)+(21037779/12500000) := by norm_num [nextNormalPenaltyLower,savedCref,uniformQuoteError]
    linarith [hk.1]
  have h := index_weak_order_from_intervals ((0/1)/2) ((13/10)/3) 0 (nextNormalPenalty adverseNextS18Before) (21037779/12500000) (68709109/50000000)
    (treeBonus (7/5) 17 2) (treeBonus (7/5) 17 3)
    (trajectory_bonus_17_2).1 (trajectory_bonus_17_3).2 hm.le
  simpa only [treeIndex] using h

theorem adverseNextS18D0Cmp6 : indexScore (7/5) (controlPenalty savedCref uniformQuoteError unitRoleUnused .next) adverseNextS18Before [] (.query 6) ≤ indexScore (7/5) (controlPenalty savedCref uniformQuoteError unitRoleUnused .next) adverseNextS18Before [] (.query 1) := by
  rw [adverseNextS18D0I6,adverseNextS18D0I1]
  have hk := adverse_next_penalty_interval 17 (by omega)
  change nextNormalPenaltyLower ≤ nextNormalPenalty adverseNextS18Before ∧ nextNormalPenalty adverseNextS18Before ≤ nextNormalPenaltyUpper at hk
  have hm : ((0/1)/2)+(84151123/50000000)-(nextNormalPenalty adverseNextS18Before) < ((0/1)/2)+(21037779/12500000)-0 := by
    have h : ((0/1)/2)+(84151123/50000000)-nextNormalPenaltyLower < ((0/1)/2)+(21037779/12500000) := by norm_num [nextNormalPenaltyLower,savedCref,uniformQuoteError]
    linarith [hk.1]
  have h := index_weak_order_from_intervals ((0/1)/2) ((0/1)/2) 0 (nextNormalPenalty adverseNextS18Before) (21037779/12500000) (84151123/50000000)
    (treeBonus (7/5) 17 2) (treeBonus (7/5) 17 2)
    (trajectory_bonus_17_2).1 (trajectory_bonus_17_2).2 hm.le
  simpa only [treeIndex] using h

theorem adverseNextS18D0Cmp7 : indexScore (7/5) (controlPenalty savedCref uniformQuoteError unitRoleUnused .next) adverseNextS18Before [] (.query 7) ≤ indexScore (7/5) (controlPenalty savedCref uniformQuoteError unitRoleUnused .next) adverseNextS18Before [] (.query 1) := by
  rw [adverseNextS18D0I7,adverseNextS18D0I1]
  have hk := adverse_next_penalty_interval 17 (by omega)
  change nextNormalPenaltyLower ≤ nextNormalPenalty adverseNextS18Before ∧ nextNormalPenalty adverseNextS18Before ≤ nextNormalPenaltyUpper at hk
  have hm : ((0/1)/2)+(84151123/50000000)-(nextNormalPenalty adverseNextS18Before) < ((0/1)/2)+(21037779/12500000)-0 := by
    have h : ((0/1)/2)+(84151123/50000000)-nextNormalPenaltyLower < ((0/1)/2)+(21037779/12500000) := by norm_num [nextNormalPenaltyLower,savedCref,uniformQuoteError]
    linarith [hk.1]
  have h := index_weak_order_from_intervals ((0/1)/2) ((0/1)/2) 0 (nextNormalPenalty adverseNextS18Before) (21037779/12500000) (84151123/50000000)
    (treeBonus (7/5) 17 2) (treeBonus (7/5) 17 2)
    (trajectory_bonus_17_2).1 (trajectory_bonus_17_2).2 hm.le
  simpa only [treeIndex] using h

theorem adverseNextS18Choice0 : nativeFirstChoice (indexScore (7/5) (controlPenalty savedCref uniformQuoteError unitRoleUnused .next) adverseNextS18Before []) adverseNextS18Before [] = .query 1 := by
  apply visited_choice_from_ordered_certificate _ _ [] [.query 0] [.query 2,.query 3,.query 4,.query 5,.query 6,.query 7] (.query 1) (by decide)
  · intro a ha
    have ho : orderedLegalAvailable [] = [.query 0,.query 1,.query 2,.query 3,.query 4,.query 5,.query 6,.query 7] := by decide
    rw [ho] at ha
    simp only [List.mem_cons,List.not_mem_nil,or_false] at ha
    rcases ha with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> decide
  · intro a ha
    simp only [List.mem_cons,List.not_mem_nil,or_false] at ha
    rcases ha with rfl
    · exact adverseNextS18D0Cmp0
  · intro a ha
    simp only [List.mem_cons,List.not_mem_nil,or_false] at ha
    rcases ha with rfl | rfl | rfl | rfl | rfl | rfl
    · exact adverseNextS18D0Cmp2
    · exact adverseNextS18D0Cmp3
    · exact adverseNextS18D0Cmp4
    · exact adverseNextS18D0Cmp5
    · exact adverseNextS18D0Cmp6
    · exact adverseNextS18D0Cmp7

theorem adverseNextS18ActualEvent : nativeEvent budgetTape (7/5) (controlPenalty savedCref uniformQuoteError unitRoleUnused .next)
    (taskReward true (2/5) (1/2)) adverseNextS18Before = adverseNextEvent18 := by
  have hs0 := native_select_existing_step budgetTape (7/5) (controlPenalty savedCref uniformQuoteError unitRoleUnused .next) adverseNextS18Before 8 [] (.query 1)
    (by decide) (by decide) adverseNextS18Choice0
  have hnew := native_select_new_step budgetTape (7/5) (controlPenalty savedCref uniformQuoteError unitRoleUnused .next) adverseNextS18Before 7 [.query 1]
    [.hydeRetriever 0,.hydeRetriever 2] (.hydeRetriever 0) (by decide) (by decide) (by decide) (by decide)
  have hs : nativeSelect budgetTape (7/5) (controlPenalty savedCref uniformQuoteError unitRoleUnused .next) adverseNextS18Before 9 [] = [.query 1,.hydeRetriever 0] := by
    rw [hs0]
    change nativeSelect budgetTape (7/5) (controlPenalty savedCref uniformQuoteError unitRoleUnused .next) adverseNextS18Before 8 [.query 1] = _
    rw [hnew] <;> rfl
  have hr : repairedRollout budgetTape adverseNextS18Before 9 [.query 1,.hydeRetriever 0] = [.query 1,.hydeRetriever 0,.selection 0,.width 0,.stop,.reranker 0,.topm 0,.context 0,.answer 0] := by decide
  simp only [nativeEvent,hs,hr]
  rfl

end AgentUCT32MConcrete
