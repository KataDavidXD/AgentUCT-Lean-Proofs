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

def favorableNextS19Before := favorableNextProposal.take 18

theorem favorableNextS19D0I0 : indexScore (7/5) (controlPenalty savedCref uniformQuoteError unitRoleUnused .next) favorableNextS19Before [] (.query 0) = treeIndex ((0/1)/2) (7/5) (nextNormalPenalty favorableNextS19Before) 18 2 := by
  have hs : replayBackup favorableNextS19Before emptyStatistics ([]++[.query 0]) = ⟨2,(0/1)⟩ := by
    rw [replayBackup_empty_closed_form]
    simp +decide [backedEvents,favorableNextS19Before,favorableNextProposal,favorableNextEvent1,favorableNextEvent2,favorableNextEvent3,favorableNextEvent4,favorableNextEvent5,favorableNextEvent6,favorableNextEvent7,favorableNextEvent8,favorableNextEvent9,favorableNextEvent10,favorableNextEvent11,favorableNextEvent12,favorableNextEvent13,favorableNextEvent14,favorableNextEvent15,favorableNextEvent16,favorableNextEvent17,favorableNextEvent18,taskReward]
    <;> norm_num
  have hp : rawVisits favorableNextS19Before [] = 18 := by decide
  have hn : rawVisits favorableNextS19Before ([]++[.query 0]) = 2 := by decide
  have hz : (controlPenalty savedCref uniformQuoteError unitRoleUnused .next) favorableNextS19Before [] (.query 0) = (nextNormalPenalty favorableNextS19Before) := by
    simpa only [favorableNextS19Before,nextNormalPenalty] using AgentUCTNextExact.favorable_next_normal_root_quotes_exact 18 (by omega) 0 (by decide)
  unfold indexScore
  rw [hs,hp,hn,hz]
  simp only [BackupStat.mean]
  norm_num

theorem favorableNextS19D0I1 : indexScore (7/5) (controlPenalty savedCref uniformQuoteError unitRoleUnused .next) favorableNextS19Before [] (.query 1) = treeIndex ((1/2)/3) (7/5) 0 18 3 := by
  have hs : replayBackup favorableNextS19Before emptyStatistics ([]++[.query 1]) = ⟨3,(1/2)⟩ := by
    rw [replayBackup_empty_closed_form]
    simp +decide [backedEvents,favorableNextS19Before,favorableNextProposal,favorableNextEvent1,favorableNextEvent2,favorableNextEvent3,favorableNextEvent4,favorableNextEvent5,favorableNextEvent6,favorableNextEvent7,favorableNextEvent8,favorableNextEvent9,favorableNextEvent10,favorableNextEvent11,favorableNextEvent12,favorableNextEvent13,favorableNextEvent14,favorableNextEvent15,favorableNextEvent16,favorableNextEvent17,favorableNextEvent18,taskReward]
    <;> norm_num
  have hp : rawVisits favorableNextS19Before [] = 18 := by decide
  have hn : rawVisits favorableNextS19Before ([]++[.query 1]) = 3 := by decide
  have hz : (controlPenalty savedCref uniformQuoteError unitRoleUnused .next) favorableNextS19Before [] (.query 1) = 0 := by
    apply control_penalty_empty_suffix
    decide
  unfold indexScore
  rw [hs,hp,hn,hz]
  simp only [BackupStat.mean]
  norm_num

theorem favorableNextS19D0I2 : indexScore (7/5) (controlPenalty savedCref uniformQuoteError unitRoleUnused .next) favorableNextS19Before [] (.query 2) = treeIndex ((0/1)/2) (7/5) (nextNormalPenalty favorableNextS19Before) 18 2 := by
  have hs : replayBackup favorableNextS19Before emptyStatistics ([]++[.query 2]) = ⟨2,(0/1)⟩ := by
    rw [replayBackup_empty_closed_form]
    simp +decide [backedEvents,favorableNextS19Before,favorableNextProposal,favorableNextEvent1,favorableNextEvent2,favorableNextEvent3,favorableNextEvent4,favorableNextEvent5,favorableNextEvent6,favorableNextEvent7,favorableNextEvent8,favorableNextEvent9,favorableNextEvent10,favorableNextEvent11,favorableNextEvent12,favorableNextEvent13,favorableNextEvent14,favorableNextEvent15,favorableNextEvent16,favorableNextEvent17,favorableNextEvent18,taskReward]
    <;> norm_num
  have hp : rawVisits favorableNextS19Before [] = 18 := by decide
  have hn : rawVisits favorableNextS19Before ([]++[.query 2]) = 2 := by decide
  have hz : (controlPenalty savedCref uniformQuoteError unitRoleUnused .next) favorableNextS19Before [] (.query 2) = (nextNormalPenalty favorableNextS19Before) := by
    simpa only [favorableNextS19Before,nextNormalPenalty] using AgentUCTNextExact.favorable_next_normal_root_quotes_exact 18 (by omega) 2 (by decide)
  unfold indexScore
  rw [hs,hp,hn,hz]
  simp only [BackupStat.mean]
  norm_num

theorem favorableNextS19D0I3 : indexScore (7/5) (controlPenalty savedCref uniformQuoteError unitRoleUnused .next) favorableNextS19Before [] (.query 3) = treeIndex ((0/1)/2) (7/5) (nextNormalPenalty favorableNextS19Before) 18 2 := by
  have hs : replayBackup favorableNextS19Before emptyStatistics ([]++[.query 3]) = ⟨2,(0/1)⟩ := by
    rw [replayBackup_empty_closed_form]
    simp +decide [backedEvents,favorableNextS19Before,favorableNextProposal,favorableNextEvent1,favorableNextEvent2,favorableNextEvent3,favorableNextEvent4,favorableNextEvent5,favorableNextEvent6,favorableNextEvent7,favorableNextEvent8,favorableNextEvent9,favorableNextEvent10,favorableNextEvent11,favorableNextEvent12,favorableNextEvent13,favorableNextEvent14,favorableNextEvent15,favorableNextEvent16,favorableNextEvent17,favorableNextEvent18,taskReward]
    <;> norm_num
  have hp : rawVisits favorableNextS19Before [] = 18 := by decide
  have hn : rawVisits favorableNextS19Before ([]++[.query 3]) = 2 := by decide
  have hz : (controlPenalty savedCref uniformQuoteError unitRoleUnused .next) favorableNextS19Before [] (.query 3) = (nextNormalPenalty favorableNextS19Before) := by
    simpa only [favorableNextS19Before,nextNormalPenalty] using AgentUCTNextExact.favorable_next_normal_root_quotes_exact 18 (by omega) 3 (by decide)
  unfold indexScore
  rw [hs,hp,hn,hz]
  simp only [BackupStat.mean]
  norm_num

theorem favorableNextS19D0I4 : indexScore (7/5) (controlPenalty savedCref uniformQuoteError unitRoleUnused .next) favorableNextS19Before [] (.query 4) = treeIndex ((0/1)/2) (7/5) (nextNormalPenalty favorableNextS19Before) 18 2 := by
  have hs : replayBackup favorableNextS19Before emptyStatistics ([]++[.query 4]) = ⟨2,(0/1)⟩ := by
    rw [replayBackup_empty_closed_form]
    simp +decide [backedEvents,favorableNextS19Before,favorableNextProposal,favorableNextEvent1,favorableNextEvent2,favorableNextEvent3,favorableNextEvent4,favorableNextEvent5,favorableNextEvent6,favorableNextEvent7,favorableNextEvent8,favorableNextEvent9,favorableNextEvent10,favorableNextEvent11,favorableNextEvent12,favorableNextEvent13,favorableNextEvent14,favorableNextEvent15,favorableNextEvent16,favorableNextEvent17,favorableNextEvent18,taskReward]
    <;> norm_num
  have hp : rawVisits favorableNextS19Before [] = 18 := by decide
  have hn : rawVisits favorableNextS19Before ([]++[.query 4]) = 2 := by decide
  have hz : (controlPenalty savedCref uniformQuoteError unitRoleUnused .next) favorableNextS19Before [] (.query 4) = (nextNormalPenalty favorableNextS19Before) := by
    simpa only [favorableNextS19Before,nextNormalPenalty] using AgentUCTNextExact.favorable_next_normal_root_quotes_exact 18 (by omega) 4 (by decide)
  unfold indexScore
  rw [hs,hp,hn,hz]
  simp only [BackupStat.mean]
  norm_num

theorem favorableNextS19D0I5 : indexScore (7/5) (controlPenalty savedCref uniformQuoteError unitRoleUnused .next) favorableNextS19Before [] (.query 5) = treeIndex ((6/5)/3) (7/5) (nextNormalPenalty favorableNextS19Before) 18 3 := by
  have hs : replayBackup favorableNextS19Before emptyStatistics ([]++[.query 5]) = ⟨3,(6/5)⟩ := by
    rw [replayBackup_empty_closed_form]
    simp +decide [backedEvents,favorableNextS19Before,favorableNextProposal,favorableNextEvent1,favorableNextEvent2,favorableNextEvent3,favorableNextEvent4,favorableNextEvent5,favorableNextEvent6,favorableNextEvent7,favorableNextEvent8,favorableNextEvent9,favorableNextEvent10,favorableNextEvent11,favorableNextEvent12,favorableNextEvent13,favorableNextEvent14,favorableNextEvent15,favorableNextEvent16,favorableNextEvent17,favorableNextEvent18,taskReward]
    <;> norm_num
  have hp : rawVisits favorableNextS19Before [] = 18 := by decide
  have hn : rawVisits favorableNextS19Before ([]++[.query 5]) = 3 := by decide
  have hz : (controlPenalty savedCref uniformQuoteError unitRoleUnused .next) favorableNextS19Before [] (.query 5) = (nextNormalPenalty favorableNextS19Before) := by
    simpa only [favorableNextS19Before,nextNormalPenalty] using AgentUCTNextExact.favorable_next_normal_root_quotes_exact 18 (by omega) 5 (by decide)
  unfold indexScore
  rw [hs,hp,hn,hz]
  simp only [BackupStat.mean]
  norm_num

theorem favorableNextS19D0I6 : indexScore (7/5) (controlPenalty savedCref uniformQuoteError unitRoleUnused .next) favorableNextS19Before [] (.query 6) = treeIndex ((0/1)/2) (7/5) (nextNormalPenalty favorableNextS19Before) 18 2 := by
  have hs : replayBackup favorableNextS19Before emptyStatistics ([]++[.query 6]) = ⟨2,(0/1)⟩ := by
    rw [replayBackup_empty_closed_form]
    simp +decide [backedEvents,favorableNextS19Before,favorableNextProposal,favorableNextEvent1,favorableNextEvent2,favorableNextEvent3,favorableNextEvent4,favorableNextEvent5,favorableNextEvent6,favorableNextEvent7,favorableNextEvent8,favorableNextEvent9,favorableNextEvent10,favorableNextEvent11,favorableNextEvent12,favorableNextEvent13,favorableNextEvent14,favorableNextEvent15,favorableNextEvent16,favorableNextEvent17,favorableNextEvent18,taskReward]
    <;> norm_num
  have hp : rawVisits favorableNextS19Before [] = 18 := by decide
  have hn : rawVisits favorableNextS19Before ([]++[.query 6]) = 2 := by decide
  have hz : (controlPenalty savedCref uniformQuoteError unitRoleUnused .next) favorableNextS19Before [] (.query 6) = (nextNormalPenalty favorableNextS19Before) := by
    simpa only [favorableNextS19Before,nextNormalPenalty] using AgentUCTNextExact.favorable_next_normal_root_quotes_exact 18 (by omega) 6 (by decide)
  unfold indexScore
  rw [hs,hp,hn,hz]
  simp only [BackupStat.mean]
  norm_num

theorem favorableNextS19D0I7 : indexScore (7/5) (controlPenalty savedCref uniformQuoteError unitRoleUnused .next) favorableNextS19Before [] (.query 7) = treeIndex ((0/1)/2) (7/5) (nextNormalPenalty favorableNextS19Before) 18 2 := by
  have hs : replayBackup favorableNextS19Before emptyStatistics ([]++[.query 7]) = ⟨2,(0/1)⟩ := by
    rw [replayBackup_empty_closed_form]
    simp +decide [backedEvents,favorableNextS19Before,favorableNextProposal,favorableNextEvent1,favorableNextEvent2,favorableNextEvent3,favorableNextEvent4,favorableNextEvent5,favorableNextEvent6,favorableNextEvent7,favorableNextEvent8,favorableNextEvent9,favorableNextEvent10,favorableNextEvent11,favorableNextEvent12,favorableNextEvent13,favorableNextEvent14,favorableNextEvent15,favorableNextEvent16,favorableNextEvent17,favorableNextEvent18,taskReward]
    <;> norm_num
  have hp : rawVisits favorableNextS19Before [] = 18 := by decide
  have hn : rawVisits favorableNextS19Before ([]++[.query 7]) = 2 := by decide
  have hz : (controlPenalty savedCref uniformQuoteError unitRoleUnused .next) favorableNextS19Before [] (.query 7) = (nextNormalPenalty favorableNextS19Before) := by
    simpa only [favorableNextS19Before,nextNormalPenalty] using AgentUCTNextExact.favorable_next_normal_root_quotes_exact 18 (by omega) 7 (by decide)
  unfold indexScore
  rw [hs,hp,hn,hz]
  simp only [BackupStat.mean]
  norm_num

theorem favorableNextS19D0Cmp0 : indexScore (7/5) (controlPenalty savedCref uniformQuoteError unitRoleUnused .next) favorableNextS19Before [] (.query 0) < indexScore (7/5) (controlPenalty savedCref uniformQuoteError unitRoleUnused .next) favorableNextS19Before [] (.query 1) := by
  rw [favorableNextS19D0I0,favorableNextS19D0I1]
  have hk := favorable_next_penalty_interval 18 (by omega)
  change nextNormalPenaltyLower ≤ nextNormalPenalty favorableNextS19Before ∧ nextNormalPenalty favorableNextS19Before ≤ nextNormalPenaltyUpper at hk
  have hm : ((0/1)/2)+(42467271/25000000)-(nextNormalPenalty favorableNextS19Before) < ((1/2)/3)+(13869751/10000000)-0 := by
    have h : ((0/1)/2)+(42467271/25000000)-nextNormalPenaltyLower < ((1/2)/3)+(13869751/10000000) := by norm_num [nextNormalPenaltyLower,savedCref,uniformQuoteError]
    linarith [hk.1]
  have h := index_strict_order_from_intervals ((1/2)/3) ((0/1)/2) 0 (nextNormalPenalty favorableNextS19Before) (13869751/10000000) (42467271/25000000)
    (treeBonus (7/5) 18 3) (treeBonus (7/5) 18 2)
    (trajectory_bonus_18_3).1 (trajectory_bonus_18_2).2 hm
  simpa only [treeIndex] using h

theorem favorableNextS19D0Cmp2 : indexScore (7/5) (controlPenalty savedCref uniformQuoteError unitRoleUnused .next) favorableNextS19Before [] (.query 2) ≤ indexScore (7/5) (controlPenalty savedCref uniformQuoteError unitRoleUnused .next) favorableNextS19Before [] (.query 1) := by
  rw [favorableNextS19D0I2,favorableNextS19D0I1]
  have hk := favorable_next_penalty_interval 18 (by omega)
  change nextNormalPenaltyLower ≤ nextNormalPenalty favorableNextS19Before ∧ nextNormalPenalty favorableNextS19Before ≤ nextNormalPenaltyUpper at hk
  have hm : ((0/1)/2)+(42467271/25000000)-(nextNormalPenalty favorableNextS19Before) < ((1/2)/3)+(13869751/10000000)-0 := by
    have h : ((0/1)/2)+(42467271/25000000)-nextNormalPenaltyLower < ((1/2)/3)+(13869751/10000000) := by norm_num [nextNormalPenaltyLower,savedCref,uniformQuoteError]
    linarith [hk.1]
  have h := index_weak_order_from_intervals ((1/2)/3) ((0/1)/2) 0 (nextNormalPenalty favorableNextS19Before) (13869751/10000000) (42467271/25000000)
    (treeBonus (7/5) 18 3) (treeBonus (7/5) 18 2)
    (trajectory_bonus_18_3).1 (trajectory_bonus_18_2).2 hm.le
  simpa only [treeIndex] using h

theorem favorableNextS19D0Cmp3 : indexScore (7/5) (controlPenalty savedCref uniformQuoteError unitRoleUnused .next) favorableNextS19Before [] (.query 3) ≤ indexScore (7/5) (controlPenalty savedCref uniformQuoteError unitRoleUnused .next) favorableNextS19Before [] (.query 1) := by
  rw [favorableNextS19D0I3,favorableNextS19D0I1]
  have hk := favorable_next_penalty_interval 18 (by omega)
  change nextNormalPenaltyLower ≤ nextNormalPenalty favorableNextS19Before ∧ nextNormalPenalty favorableNextS19Before ≤ nextNormalPenaltyUpper at hk
  have hm : ((0/1)/2)+(42467271/25000000)-(nextNormalPenalty favorableNextS19Before) < ((1/2)/3)+(13869751/10000000)-0 := by
    have h : ((0/1)/2)+(42467271/25000000)-nextNormalPenaltyLower < ((1/2)/3)+(13869751/10000000) := by norm_num [nextNormalPenaltyLower,savedCref,uniformQuoteError]
    linarith [hk.1]
  have h := index_weak_order_from_intervals ((1/2)/3) ((0/1)/2) 0 (nextNormalPenalty favorableNextS19Before) (13869751/10000000) (42467271/25000000)
    (treeBonus (7/5) 18 3) (treeBonus (7/5) 18 2)
    (trajectory_bonus_18_3).1 (trajectory_bonus_18_2).2 hm.le
  simpa only [treeIndex] using h

theorem favorableNextS19D0Cmp4 : indexScore (7/5) (controlPenalty savedCref uniformQuoteError unitRoleUnused .next) favorableNextS19Before [] (.query 4) ≤ indexScore (7/5) (controlPenalty savedCref uniformQuoteError unitRoleUnused .next) favorableNextS19Before [] (.query 1) := by
  rw [favorableNextS19D0I4,favorableNextS19D0I1]
  have hk := favorable_next_penalty_interval 18 (by omega)
  change nextNormalPenaltyLower ≤ nextNormalPenalty favorableNextS19Before ∧ nextNormalPenalty favorableNextS19Before ≤ nextNormalPenaltyUpper at hk
  have hm : ((0/1)/2)+(42467271/25000000)-(nextNormalPenalty favorableNextS19Before) < ((1/2)/3)+(13869751/10000000)-0 := by
    have h : ((0/1)/2)+(42467271/25000000)-nextNormalPenaltyLower < ((1/2)/3)+(13869751/10000000) := by norm_num [nextNormalPenaltyLower,savedCref,uniformQuoteError]
    linarith [hk.1]
  have h := index_weak_order_from_intervals ((1/2)/3) ((0/1)/2) 0 (nextNormalPenalty favorableNextS19Before) (13869751/10000000) (42467271/25000000)
    (treeBonus (7/5) 18 3) (treeBonus (7/5) 18 2)
    (trajectory_bonus_18_3).1 (trajectory_bonus_18_2).2 hm.le
  simpa only [treeIndex] using h

theorem favorableNextS19D0Cmp5 : indexScore (7/5) (controlPenalty savedCref uniformQuoteError unitRoleUnused .next) favorableNextS19Before [] (.query 5) ≤ indexScore (7/5) (controlPenalty savedCref uniformQuoteError unitRoleUnused .next) favorableNextS19Before [] (.query 1) := by
  rw [favorableNextS19D0I5,favorableNextS19D0I1]
  have hk := favorable_next_penalty_interval 18 (by omega)
  change nextNormalPenaltyLower ≤ nextNormalPenalty favorableNextS19Before ∧ nextNormalPenalty favorableNextS19Before ≤ nextNormalPenaltyUpper at hk
  have hm : ((6/5)/3)+(34674381/25000000)-(nextNormalPenalty favorableNextS19Before) < ((1/2)/3)+(13869751/10000000)-0 := by
    have h : ((6/5)/3)+(34674381/25000000)-nextNormalPenaltyLower < ((1/2)/3)+(13869751/10000000) := by norm_num [nextNormalPenaltyLower,savedCref,uniformQuoteError]
    linarith [hk.1]
  have h := index_weak_order_from_intervals ((1/2)/3) ((6/5)/3) 0 (nextNormalPenalty favorableNextS19Before) (13869751/10000000) (34674381/25000000)
    (treeBonus (7/5) 18 3) (treeBonus (7/5) 18 3)
    (trajectory_bonus_18_3).1 (trajectory_bonus_18_3).2 hm.le
  simpa only [treeIndex] using h

theorem favorableNextS19D0Cmp6 : indexScore (7/5) (controlPenalty savedCref uniformQuoteError unitRoleUnused .next) favorableNextS19Before [] (.query 6) ≤ indexScore (7/5) (controlPenalty savedCref uniformQuoteError unitRoleUnused .next) favorableNextS19Before [] (.query 1) := by
  rw [favorableNextS19D0I6,favorableNextS19D0I1]
  have hk := favorable_next_penalty_interval 18 (by omega)
  change nextNormalPenaltyLower ≤ nextNormalPenalty favorableNextS19Before ∧ nextNormalPenalty favorableNextS19Before ≤ nextNormalPenaltyUpper at hk
  have hm : ((0/1)/2)+(42467271/25000000)-(nextNormalPenalty favorableNextS19Before) < ((1/2)/3)+(13869751/10000000)-0 := by
    have h : ((0/1)/2)+(42467271/25000000)-nextNormalPenaltyLower < ((1/2)/3)+(13869751/10000000) := by norm_num [nextNormalPenaltyLower,savedCref,uniformQuoteError]
    linarith [hk.1]
  have h := index_weak_order_from_intervals ((1/2)/3) ((0/1)/2) 0 (nextNormalPenalty favorableNextS19Before) (13869751/10000000) (42467271/25000000)
    (treeBonus (7/5) 18 3) (treeBonus (7/5) 18 2)
    (trajectory_bonus_18_3).1 (trajectory_bonus_18_2).2 hm.le
  simpa only [treeIndex] using h

theorem favorableNextS19D0Cmp7 : indexScore (7/5) (controlPenalty savedCref uniformQuoteError unitRoleUnused .next) favorableNextS19Before [] (.query 7) ≤ indexScore (7/5) (controlPenalty savedCref uniformQuoteError unitRoleUnused .next) favorableNextS19Before [] (.query 1) := by
  rw [favorableNextS19D0I7,favorableNextS19D0I1]
  have hk := favorable_next_penalty_interval 18 (by omega)
  change nextNormalPenaltyLower ≤ nextNormalPenalty favorableNextS19Before ∧ nextNormalPenalty favorableNextS19Before ≤ nextNormalPenaltyUpper at hk
  have hm : ((0/1)/2)+(42467271/25000000)-(nextNormalPenalty favorableNextS19Before) < ((1/2)/3)+(13869751/10000000)-0 := by
    have h : ((0/1)/2)+(42467271/25000000)-nextNormalPenaltyLower < ((1/2)/3)+(13869751/10000000) := by norm_num [nextNormalPenaltyLower,savedCref,uniformQuoteError]
    linarith [hk.1]
  have h := index_weak_order_from_intervals ((1/2)/3) ((0/1)/2) 0 (nextNormalPenalty favorableNextS19Before) (13869751/10000000) (42467271/25000000)
    (treeBonus (7/5) 18 3) (treeBonus (7/5) 18 2)
    (trajectory_bonus_18_3).1 (trajectory_bonus_18_2).2 hm.le
  simpa only [treeIndex] using h

theorem favorableNextS19Choice0 : nativeFirstChoice (indexScore (7/5) (controlPenalty savedCref uniformQuoteError unitRoleUnused .next) favorableNextS19Before []) favorableNextS19Before [] = .query 1 := by
  apply visited_choice_from_ordered_certificate _ _ [] [.query 0] [.query 2,.query 3,.query 4,.query 5,.query 6,.query 7] (.query 1) (by decide)
  · intro a ha
    have ho : orderedLegalAvailable [] = [.query 0,.query 1,.query 2,.query 3,.query 4,.query 5,.query 6,.query 7] := by decide
    rw [ho] at ha
    simp only [List.mem_cons,List.not_mem_nil,or_false] at ha
    rcases ha with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> decide
  · intro a ha
    simp only [List.mem_cons,List.not_mem_nil,or_false] at ha
    rcases ha with rfl
    · exact favorableNextS19D0Cmp0
  · intro a ha
    simp only [List.mem_cons,List.not_mem_nil,or_false] at ha
    rcases ha with rfl | rfl | rfl | rfl | rfl | rfl
    · exact favorableNextS19D0Cmp2
    · exact favorableNextS19D0Cmp3
    · exact favorableNextS19D0Cmp4
    · exact favorableNextS19D0Cmp5
    · exact favorableNextS19D0Cmp6
    · exact favorableNextS19D0Cmp7

theorem favorableNextS19ActualEvent : nativeEvent budgetTape (7/5) (controlPenalty savedCref uniformQuoteError unitRoleUnused .next)
    (taskReward false (2/5) (1/2)) favorableNextS19Before = favorableNextEvent19 := by
  have hs0 := native_select_existing_step budgetTape (7/5) (controlPenalty savedCref uniformQuoteError unitRoleUnused .next) favorableNextS19Before 8 [] (.query 1)
    (by decide) (by decide) favorableNextS19Choice0
  have hnew := native_select_new_step budgetTape (7/5) (controlPenalty savedCref uniformQuoteError unitRoleUnused .next) favorableNextS19Before 7 [.query 1]
    [.hydeRetriever 2] (.hydeRetriever 2) (by decide) (by decide) (by decide) (by decide)
  have hs : nativeSelect budgetTape (7/5) (controlPenalty savedCref uniformQuoteError unitRoleUnused .next) favorableNextS19Before 9 [] = [.query 1,.hydeRetriever 2] := by
    rw [hs0]
    change nativeSelect budgetTape (7/5) (controlPenalty savedCref uniformQuoteError unitRoleUnused .next) favorableNextS19Before 8 [.query 1] = _
    rw [hnew] <;> rfl
  have hr : repairedRollout budgetTape favorableNextS19Before 9 [.query 1,.hydeRetriever 2] = [.query 1,.hydeRetriever 2,.selection 0,.width 0,.stop,.reranker 0,.topm 2,.context 0,.answer 2] := by decide
  simp only [nativeEvent,hs,hr]
  rfl

def favorableNextS20Before := favorableNextProposal.take 19

theorem favorableNextS20D0I0 : indexScore (7/5) (controlPenalty savedCref uniformQuoteError unitRoleUnused .next) favorableNextS20Before [] (.query 0) = treeIndex ((0/1)/2) (7/5) (nextNormalPenalty favorableNextS20Before) 19 2 := by
  have hs : replayBackup favorableNextS20Before emptyStatistics ([]++[.query 0]) = ⟨2,(0/1)⟩ := by
    rw [replayBackup_empty_closed_form]
    simp +decide [backedEvents,favorableNextS20Before,favorableNextProposal,favorableNextEvent1,favorableNextEvent2,favorableNextEvent3,favorableNextEvent4,favorableNextEvent5,favorableNextEvent6,favorableNextEvent7,favorableNextEvent8,favorableNextEvent9,favorableNextEvent10,favorableNextEvent11,favorableNextEvent12,favorableNextEvent13,favorableNextEvent14,favorableNextEvent15,favorableNextEvent16,favorableNextEvent17,favorableNextEvent18,favorableNextEvent19,taskReward]
    <;> norm_num
  have hp : rawVisits favorableNextS20Before [] = 19 := by decide
  have hn : rawVisits favorableNextS20Before ([]++[.query 0]) = 2 := by decide
  have hz : (controlPenalty savedCref uniformQuoteError unitRoleUnused .next) favorableNextS20Before [] (.query 0) = (nextNormalPenalty favorableNextS20Before) := by
    simpa only [favorableNextS20Before,nextNormalPenalty] using AgentUCTNextExact.favorable_next_normal_root_quotes_exact 19 (by omega) 0 (by decide)
  unfold indexScore
  rw [hs,hp,hn,hz]
  simp only [BackupStat.mean]
  norm_num

theorem favorableNextS20D0I1 : indexScore (7/5) (controlPenalty savedCref uniformQuoteError unitRoleUnused .next) favorableNextS20Before [] (.query 1) = treeIndex ((1/2)/4) (7/5) 0 19 4 := by
  have hs : replayBackup favorableNextS20Before emptyStatistics ([]++[.query 1]) = ⟨4,(1/2)⟩ := by
    rw [replayBackup_empty_closed_form]
    simp +decide [backedEvents,favorableNextS20Before,favorableNextProposal,favorableNextEvent1,favorableNextEvent2,favorableNextEvent3,favorableNextEvent4,favorableNextEvent5,favorableNextEvent6,favorableNextEvent7,favorableNextEvent8,favorableNextEvent9,favorableNextEvent10,favorableNextEvent11,favorableNextEvent12,favorableNextEvent13,favorableNextEvent14,favorableNextEvent15,favorableNextEvent16,favorableNextEvent17,favorableNextEvent18,favorableNextEvent19,taskReward]
    <;> norm_num
  have hp : rawVisits favorableNextS20Before [] = 19 := by decide
  have hn : rawVisits favorableNextS20Before ([]++[.query 1]) = 4 := by decide
  have hz : (controlPenalty savedCref uniformQuoteError unitRoleUnused .next) favorableNextS20Before [] (.query 1) = 0 := by
    apply control_penalty_empty_suffix
    decide
  unfold indexScore
  rw [hs,hp,hn,hz]
  simp only [BackupStat.mean]
  norm_num

theorem favorableNextS20D0I2 : indexScore (7/5) (controlPenalty savedCref uniformQuoteError unitRoleUnused .next) favorableNextS20Before [] (.query 2) = treeIndex ((0/1)/2) (7/5) (nextNormalPenalty favorableNextS20Before) 19 2 := by
  have hs : replayBackup favorableNextS20Before emptyStatistics ([]++[.query 2]) = ⟨2,(0/1)⟩ := by
    rw [replayBackup_empty_closed_form]
    simp +decide [backedEvents,favorableNextS20Before,favorableNextProposal,favorableNextEvent1,favorableNextEvent2,favorableNextEvent3,favorableNextEvent4,favorableNextEvent5,favorableNextEvent6,favorableNextEvent7,favorableNextEvent8,favorableNextEvent9,favorableNextEvent10,favorableNextEvent11,favorableNextEvent12,favorableNextEvent13,favorableNextEvent14,favorableNextEvent15,favorableNextEvent16,favorableNextEvent17,favorableNextEvent18,favorableNextEvent19,taskReward]
    <;> norm_num
  have hp : rawVisits favorableNextS20Before [] = 19 := by decide
  have hn : rawVisits favorableNextS20Before ([]++[.query 2]) = 2 := by decide
  have hz : (controlPenalty savedCref uniformQuoteError unitRoleUnused .next) favorableNextS20Before [] (.query 2) = (nextNormalPenalty favorableNextS20Before) := by
    simpa only [favorableNextS20Before,nextNormalPenalty] using AgentUCTNextExact.favorable_next_normal_root_quotes_exact 19 (by omega) 2 (by decide)
  unfold indexScore
  rw [hs,hp,hn,hz]
  simp only [BackupStat.mean]
  norm_num

theorem favorableNextS20D0I3 : indexScore (7/5) (controlPenalty savedCref uniformQuoteError unitRoleUnused .next) favorableNextS20Before [] (.query 3) = treeIndex ((0/1)/2) (7/5) (nextNormalPenalty favorableNextS20Before) 19 2 := by
  have hs : replayBackup favorableNextS20Before emptyStatistics ([]++[.query 3]) = ⟨2,(0/1)⟩ := by
    rw [replayBackup_empty_closed_form]
    simp +decide [backedEvents,favorableNextS20Before,favorableNextProposal,favorableNextEvent1,favorableNextEvent2,favorableNextEvent3,favorableNextEvent4,favorableNextEvent5,favorableNextEvent6,favorableNextEvent7,favorableNextEvent8,favorableNextEvent9,favorableNextEvent10,favorableNextEvent11,favorableNextEvent12,favorableNextEvent13,favorableNextEvent14,favorableNextEvent15,favorableNextEvent16,favorableNextEvent17,favorableNextEvent18,favorableNextEvent19,taskReward]
    <;> norm_num
  have hp : rawVisits favorableNextS20Before [] = 19 := by decide
  have hn : rawVisits favorableNextS20Before ([]++[.query 3]) = 2 := by decide
  have hz : (controlPenalty savedCref uniformQuoteError unitRoleUnused .next) favorableNextS20Before [] (.query 3) = (nextNormalPenalty favorableNextS20Before) := by
    simpa only [favorableNextS20Before,nextNormalPenalty] using AgentUCTNextExact.favorable_next_normal_root_quotes_exact 19 (by omega) 3 (by decide)
  unfold indexScore
  rw [hs,hp,hn,hz]
  simp only [BackupStat.mean]
  norm_num

theorem favorableNextS20D0I4 : indexScore (7/5) (controlPenalty savedCref uniformQuoteError unitRoleUnused .next) favorableNextS20Before [] (.query 4) = treeIndex ((0/1)/2) (7/5) (nextNormalPenalty favorableNextS20Before) 19 2 := by
  have hs : replayBackup favorableNextS20Before emptyStatistics ([]++[.query 4]) = ⟨2,(0/1)⟩ := by
    rw [replayBackup_empty_closed_form]
    simp +decide [backedEvents,favorableNextS20Before,favorableNextProposal,favorableNextEvent1,favorableNextEvent2,favorableNextEvent3,favorableNextEvent4,favorableNextEvent5,favorableNextEvent6,favorableNextEvent7,favorableNextEvent8,favorableNextEvent9,favorableNextEvent10,favorableNextEvent11,favorableNextEvent12,favorableNextEvent13,favorableNextEvent14,favorableNextEvent15,favorableNextEvent16,favorableNextEvent17,favorableNextEvent18,favorableNextEvent19,taskReward]
    <;> norm_num
  have hp : rawVisits favorableNextS20Before [] = 19 := by decide
  have hn : rawVisits favorableNextS20Before ([]++[.query 4]) = 2 := by decide
  have hz : (controlPenalty savedCref uniformQuoteError unitRoleUnused .next) favorableNextS20Before [] (.query 4) = (nextNormalPenalty favorableNextS20Before) := by
    simpa only [favorableNextS20Before,nextNormalPenalty] using AgentUCTNextExact.favorable_next_normal_root_quotes_exact 19 (by omega) 4 (by decide)
  unfold indexScore
  rw [hs,hp,hn,hz]
  simp only [BackupStat.mean]
  norm_num

theorem favorableNextS20D0I5 : indexScore (7/5) (controlPenalty savedCref uniformQuoteError unitRoleUnused .next) favorableNextS20Before [] (.query 5) = treeIndex ((6/5)/3) (7/5) (nextNormalPenalty favorableNextS20Before) 19 3 := by
  have hs : replayBackup favorableNextS20Before emptyStatistics ([]++[.query 5]) = ⟨3,(6/5)⟩ := by
    rw [replayBackup_empty_closed_form]
    simp +decide [backedEvents,favorableNextS20Before,favorableNextProposal,favorableNextEvent1,favorableNextEvent2,favorableNextEvent3,favorableNextEvent4,favorableNextEvent5,favorableNextEvent6,favorableNextEvent7,favorableNextEvent8,favorableNextEvent9,favorableNextEvent10,favorableNextEvent11,favorableNextEvent12,favorableNextEvent13,favorableNextEvent14,favorableNextEvent15,favorableNextEvent16,favorableNextEvent17,favorableNextEvent18,favorableNextEvent19,taskReward]
    <;> norm_num
  have hp : rawVisits favorableNextS20Before [] = 19 := by decide
  have hn : rawVisits favorableNextS20Before ([]++[.query 5]) = 3 := by decide
  have hz : (controlPenalty savedCref uniformQuoteError unitRoleUnused .next) favorableNextS20Before [] (.query 5) = (nextNormalPenalty favorableNextS20Before) := by
    simpa only [favorableNextS20Before,nextNormalPenalty] using AgentUCTNextExact.favorable_next_normal_root_quotes_exact 19 (by omega) 5 (by decide)
  unfold indexScore
  rw [hs,hp,hn,hz]
  simp only [BackupStat.mean]
  norm_num

theorem favorableNextS20D0I6 : indexScore (7/5) (controlPenalty savedCref uniformQuoteError unitRoleUnused .next) favorableNextS20Before [] (.query 6) = treeIndex ((0/1)/2) (7/5) (nextNormalPenalty favorableNextS20Before) 19 2 := by
  have hs : replayBackup favorableNextS20Before emptyStatistics ([]++[.query 6]) = ⟨2,(0/1)⟩ := by
    rw [replayBackup_empty_closed_form]
    simp +decide [backedEvents,favorableNextS20Before,favorableNextProposal,favorableNextEvent1,favorableNextEvent2,favorableNextEvent3,favorableNextEvent4,favorableNextEvent5,favorableNextEvent6,favorableNextEvent7,favorableNextEvent8,favorableNextEvent9,favorableNextEvent10,favorableNextEvent11,favorableNextEvent12,favorableNextEvent13,favorableNextEvent14,favorableNextEvent15,favorableNextEvent16,favorableNextEvent17,favorableNextEvent18,favorableNextEvent19,taskReward]
    <;> norm_num
  have hp : rawVisits favorableNextS20Before [] = 19 := by decide
  have hn : rawVisits favorableNextS20Before ([]++[.query 6]) = 2 := by decide
  have hz : (controlPenalty savedCref uniformQuoteError unitRoleUnused .next) favorableNextS20Before [] (.query 6) = (nextNormalPenalty favorableNextS20Before) := by
    simpa only [favorableNextS20Before,nextNormalPenalty] using AgentUCTNextExact.favorable_next_normal_root_quotes_exact 19 (by omega) 6 (by decide)
  unfold indexScore
  rw [hs,hp,hn,hz]
  simp only [BackupStat.mean]
  norm_num

theorem favorableNextS20D0I7 : indexScore (7/5) (controlPenalty savedCref uniformQuoteError unitRoleUnused .next) favorableNextS20Before [] (.query 7) = treeIndex ((0/1)/2) (7/5) (nextNormalPenalty favorableNextS20Before) 19 2 := by
  have hs : replayBackup favorableNextS20Before emptyStatistics ([]++[.query 7]) = ⟨2,(0/1)⟩ := by
    rw [replayBackup_empty_closed_form]
    simp +decide [backedEvents,favorableNextS20Before,favorableNextProposal,favorableNextEvent1,favorableNextEvent2,favorableNextEvent3,favorableNextEvent4,favorableNextEvent5,favorableNextEvent6,favorableNextEvent7,favorableNextEvent8,favorableNextEvent9,favorableNextEvent10,favorableNextEvent11,favorableNextEvent12,favorableNextEvent13,favorableNextEvent14,favorableNextEvent15,favorableNextEvent16,favorableNextEvent17,favorableNextEvent18,favorableNextEvent19,taskReward]
    <;> norm_num
  have hp : rawVisits favorableNextS20Before [] = 19 := by decide
  have hn : rawVisits favorableNextS20Before ([]++[.query 7]) = 2 := by decide
  have hz : (controlPenalty savedCref uniformQuoteError unitRoleUnused .next) favorableNextS20Before [] (.query 7) = (nextNormalPenalty favorableNextS20Before) := by
    simpa only [favorableNextS20Before,nextNormalPenalty] using AgentUCTNextExact.favorable_next_normal_root_quotes_exact 19 (by omega) 7 (by decide)
  unfold indexScore
  rw [hs,hp,hn,hz]
  simp only [BackupStat.mean]
  norm_num

theorem favorableNextS20D0Cmp0 : indexScore (7/5) (controlPenalty savedCref uniformQuoteError unitRoleUnused .next) favorableNextS20Before [] (.query 0) < indexScore (7/5) (controlPenalty savedCref uniformQuoteError unitRoleUnused .next) favorableNextS20Before [] (.query 5) := by
  rw [favorableNextS20D0I0,favorableNextS20D0I5]
  have hk := favorable_next_penalty_interval 19 (by omega)
  change nextNormalPenaltyLower ≤ nextNormalPenalty favorableNextS20Before ∧ nextNormalPenalty favorableNextS20Before ≤ nextNormalPenaltyUpper at hk
  have hm : ((0/1)/2)+(17134229/10000000)-(nextNormalPenalty favorableNextS20Before) < ((6/5)/3)+(17487547/12500000)-(nextNormalPenalty favorableNextS20Before) := by
    have h : (((0/1)/2)+(17134229/10000000) : ℝ) < ((6/5)/3)+(17487547/12500000) := by norm_num
    linarith
  have h := index_strict_order_from_intervals ((6/5)/3) ((0/1)/2) (nextNormalPenalty favorableNextS20Before) (nextNormalPenalty favorableNextS20Before) (17487547/12500000) (17134229/10000000)
    (treeBonus (7/5) 19 3) (treeBonus (7/5) 19 2)
    (trajectory_bonus_19_3).1 (trajectory_bonus_19_2).2 hm
  simpa only [treeIndex] using h

theorem favorableNextS20D0Cmp1 : indexScore (7/5) (controlPenalty savedCref uniformQuoteError unitRoleUnused .next) favorableNextS20Before [] (.query 1) < indexScore (7/5) (controlPenalty savedCref uniformQuoteError unitRoleUnused .next) favorableNextS20Before [] (.query 5) := by
  rw [favorableNextS20D0I1,favorableNextS20D0I5]
  have hk := favorable_next_penalty_interval 19 (by omega)
  change nextNormalPenaltyLower ≤ nextNormalPenalty favorableNextS20Before ∧ nextNormalPenalty favorableNextS20Before ≤ nextNormalPenaltyUpper at hk
  have hm : ((1/2)/4)+(15144661/12500000)-0 < ((6/5)/3)+(17487547/12500000)-(nextNormalPenalty favorableNextS20Before) := by
    have h : ((1/2)/4)+(15144661/12500000) < ((6/5)/3)+(17487547/12500000)-nextNormalPenaltyUpper := by norm_num [nextNormalPenaltyUpper,savedCref,uniformQuoteError]
    linarith [hk.2]
  have h := index_strict_order_from_intervals ((6/5)/3) ((1/2)/4) (nextNormalPenalty favorableNextS20Before) 0 (17487547/12500000) (15144661/12500000)
    (treeBonus (7/5) 19 3) (treeBonus (7/5) 19 4)
    (trajectory_bonus_19_3).1 (trajectory_bonus_19_4).2 hm
  simpa only [treeIndex] using h

theorem favorableNextS20D0Cmp2 : indexScore (7/5) (controlPenalty savedCref uniformQuoteError unitRoleUnused .next) favorableNextS20Before [] (.query 2) < indexScore (7/5) (controlPenalty savedCref uniformQuoteError unitRoleUnused .next) favorableNextS20Before [] (.query 5) := by
  rw [favorableNextS20D0I2,favorableNextS20D0I5]
  have hk := favorable_next_penalty_interval 19 (by omega)
  change nextNormalPenaltyLower ≤ nextNormalPenalty favorableNextS20Before ∧ nextNormalPenalty favorableNextS20Before ≤ nextNormalPenaltyUpper at hk
  have hm : ((0/1)/2)+(17134229/10000000)-(nextNormalPenalty favorableNextS20Before) < ((6/5)/3)+(17487547/12500000)-(nextNormalPenalty favorableNextS20Before) := by
    have h : (((0/1)/2)+(17134229/10000000) : ℝ) < ((6/5)/3)+(17487547/12500000) := by norm_num
    linarith
  have h := index_strict_order_from_intervals ((6/5)/3) ((0/1)/2) (nextNormalPenalty favorableNextS20Before) (nextNormalPenalty favorableNextS20Before) (17487547/12500000) (17134229/10000000)
    (treeBonus (7/5) 19 3) (treeBonus (7/5) 19 2)
    (trajectory_bonus_19_3).1 (trajectory_bonus_19_2).2 hm
  simpa only [treeIndex] using h

theorem favorableNextS20D0Cmp3 : indexScore (7/5) (controlPenalty savedCref uniformQuoteError unitRoleUnused .next) favorableNextS20Before [] (.query 3) < indexScore (7/5) (controlPenalty savedCref uniformQuoteError unitRoleUnused .next) favorableNextS20Before [] (.query 5) := by
  rw [favorableNextS20D0I3,favorableNextS20D0I5]
  have hk := favorable_next_penalty_interval 19 (by omega)
  change nextNormalPenaltyLower ≤ nextNormalPenalty favorableNextS20Before ∧ nextNormalPenalty favorableNextS20Before ≤ nextNormalPenaltyUpper at hk
  have hm : ((0/1)/2)+(17134229/10000000)-(nextNormalPenalty favorableNextS20Before) < ((6/5)/3)+(17487547/12500000)-(nextNormalPenalty favorableNextS20Before) := by
    have h : (((0/1)/2)+(17134229/10000000) : ℝ) < ((6/5)/3)+(17487547/12500000) := by norm_num
    linarith
  have h := index_strict_order_from_intervals ((6/5)/3) ((0/1)/2) (nextNormalPenalty favorableNextS20Before) (nextNormalPenalty favorableNextS20Before) (17487547/12500000) (17134229/10000000)
    (treeBonus (7/5) 19 3) (treeBonus (7/5) 19 2)
    (trajectory_bonus_19_3).1 (trajectory_bonus_19_2).2 hm
  simpa only [treeIndex] using h

theorem favorableNextS20D0Cmp4 : indexScore (7/5) (controlPenalty savedCref uniformQuoteError unitRoleUnused .next) favorableNextS20Before [] (.query 4) < indexScore (7/5) (controlPenalty savedCref uniformQuoteError unitRoleUnused .next) favorableNextS20Before [] (.query 5) := by
  rw [favorableNextS20D0I4,favorableNextS20D0I5]
  have hk := favorable_next_penalty_interval 19 (by omega)
  change nextNormalPenaltyLower ≤ nextNormalPenalty favorableNextS20Before ∧ nextNormalPenalty favorableNextS20Before ≤ nextNormalPenaltyUpper at hk
  have hm : ((0/1)/2)+(17134229/10000000)-(nextNormalPenalty favorableNextS20Before) < ((6/5)/3)+(17487547/12500000)-(nextNormalPenalty favorableNextS20Before) := by
    have h : (((0/1)/2)+(17134229/10000000) : ℝ) < ((6/5)/3)+(17487547/12500000) := by norm_num
    linarith
  have h := index_strict_order_from_intervals ((6/5)/3) ((0/1)/2) (nextNormalPenalty favorableNextS20Before) (nextNormalPenalty favorableNextS20Before) (17487547/12500000) (17134229/10000000)
    (treeBonus (7/5) 19 3) (treeBonus (7/5) 19 2)
    (trajectory_bonus_19_3).1 (trajectory_bonus_19_2).2 hm
  simpa only [treeIndex] using h

theorem favorableNextS20D0Cmp6 : indexScore (7/5) (controlPenalty savedCref uniformQuoteError unitRoleUnused .next) favorableNextS20Before [] (.query 6) ≤ indexScore (7/5) (controlPenalty savedCref uniformQuoteError unitRoleUnused .next) favorableNextS20Before [] (.query 5) := by
  rw [favorableNextS20D0I6,favorableNextS20D0I5]
  have hk := favorable_next_penalty_interval 19 (by omega)
  change nextNormalPenaltyLower ≤ nextNormalPenalty favorableNextS20Before ∧ nextNormalPenalty favorableNextS20Before ≤ nextNormalPenaltyUpper at hk
  have hm : ((0/1)/2)+(17134229/10000000)-(nextNormalPenalty favorableNextS20Before) < ((6/5)/3)+(17487547/12500000)-(nextNormalPenalty favorableNextS20Before) := by
    have h : (((0/1)/2)+(17134229/10000000) : ℝ) < ((6/5)/3)+(17487547/12500000) := by norm_num
    linarith
  have h := index_weak_order_from_intervals ((6/5)/3) ((0/1)/2) (nextNormalPenalty favorableNextS20Before) (nextNormalPenalty favorableNextS20Before) (17487547/12500000) (17134229/10000000)
    (treeBonus (7/5) 19 3) (treeBonus (7/5) 19 2)
    (trajectory_bonus_19_3).1 (trajectory_bonus_19_2).2 hm.le
  simpa only [treeIndex] using h

theorem favorableNextS20D0Cmp7 : indexScore (7/5) (controlPenalty savedCref uniformQuoteError unitRoleUnused .next) favorableNextS20Before [] (.query 7) ≤ indexScore (7/5) (controlPenalty savedCref uniformQuoteError unitRoleUnused .next) favorableNextS20Before [] (.query 5) := by
  rw [favorableNextS20D0I7,favorableNextS20D0I5]
  have hk := favorable_next_penalty_interval 19 (by omega)
  change nextNormalPenaltyLower ≤ nextNormalPenalty favorableNextS20Before ∧ nextNormalPenalty favorableNextS20Before ≤ nextNormalPenaltyUpper at hk
  have hm : ((0/1)/2)+(17134229/10000000)-(nextNormalPenalty favorableNextS20Before) < ((6/5)/3)+(17487547/12500000)-(nextNormalPenalty favorableNextS20Before) := by
    have h : (((0/1)/2)+(17134229/10000000) : ℝ) < ((6/5)/3)+(17487547/12500000) := by norm_num
    linarith
  have h := index_weak_order_from_intervals ((6/5)/3) ((0/1)/2) (nextNormalPenalty favorableNextS20Before) (nextNormalPenalty favorableNextS20Before) (17487547/12500000) (17134229/10000000)
    (treeBonus (7/5) 19 3) (treeBonus (7/5) 19 2)
    (trajectory_bonus_19_3).1 (trajectory_bonus_19_2).2 hm.le
  simpa only [treeIndex] using h

theorem favorableNextS20Choice0 : nativeFirstChoice (indexScore (7/5) (controlPenalty savedCref uniformQuoteError unitRoleUnused .next) favorableNextS20Before []) favorableNextS20Before [] = .query 5 := by
  apply visited_choice_from_ordered_certificate _ _ [] [.query 0,.query 1,.query 2,.query 3,.query 4] [.query 6,.query 7] (.query 5) (by decide)
  · intro a ha
    have ho : orderedLegalAvailable [] = [.query 0,.query 1,.query 2,.query 3,.query 4,.query 5,.query 6,.query 7] := by decide
    rw [ho] at ha
    simp only [List.mem_cons,List.not_mem_nil,or_false] at ha
    rcases ha with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> decide
  · intro a ha
    simp only [List.mem_cons,List.not_mem_nil,or_false] at ha
    rcases ha with rfl | rfl | rfl | rfl | rfl
    · exact favorableNextS20D0Cmp0
    · exact favorableNextS20D0Cmp1
    · exact favorableNextS20D0Cmp2
    · exact favorableNextS20D0Cmp3
    · exact favorableNextS20D0Cmp4
  · intro a ha
    simp only [List.mem_cons,List.not_mem_nil,or_false] at ha
    rcases ha with rfl | rfl
    · exact favorableNextS20D0Cmp6
    · exact favorableNextS20D0Cmp7

theorem favorableNextS20ActualEvent : nativeEvent budgetTape (7/5) (controlPenalty savedCref uniformQuoteError unitRoleUnused .next)
    (taskReward false (2/5) (1/2)) favorableNextS20Before = favorableNextEvent20 := by
  have hs0 := native_select_existing_step budgetTape (7/5) (controlPenalty savedCref uniformQuoteError unitRoleUnused .next) favorableNextS20Before 8 [] (.query 5)
    (by decide) (by decide) favorableNextS20Choice0
  have hnew := native_select_new_step budgetTape (7/5) (controlPenalty savedCref uniformQuoteError unitRoleUnused .next) favorableNextS20Before 7 [.query 5]
    [.normalRetriever 4,.normalRetriever 6,.normalRetriever 7,.normalRetriever 8,.normalRetriever 5,.normalRetriever 2,.normalRetriever 3,.normalRetriever 12,.normalRetriever 14,.normalRetriever 13,.normalRetriever 21,.normalRetriever 23,.normalRetriever 22,.normalRetriever 9,.normalRetriever 11,.normalRetriever 10,.normalRetriever 15,.normalRetriever 17,.normalRetriever 16,.normalRetriever 18,.normalRetriever 20,.normalRetriever 19,.normalRetriever 24,.normalRetriever 25,.normalRetriever 26,.normalRetriever 27,.normalRetriever 28,.normalRetriever 29] (.normalRetriever 4) (by decide) (by decide) (by decide) (by decide)
  have hs : nativeSelect budgetTape (7/5) (controlPenalty savedCref uniformQuoteError unitRoleUnused .next) favorableNextS20Before 9 [] = [.query 5,.normalRetriever 4] := by
    rw [hs0]
    change nativeSelect budgetTape (7/5) (controlPenalty savedCref uniformQuoteError unitRoleUnused .next) favorableNextS20Before 8 [.query 5] = _
    rw [hnew] <;> rfl
  have hr : repairedRollout budgetTape favorableNextS20Before 9 [.query 5,.normalRetriever 4] = [.query 5,.normalRetriever 4,.selection 0,.width 0,.stop,.reranker 0,.topm 0,.context 0,.answer 0] := by decide
  simp only [nativeEvent,hs,hr]
  rfl

def favorableNextS21Before := favorableNextProposal.take 20

theorem favorableNextS21D0I0 : indexScore (7/5) (controlPenalty savedCref uniformQuoteError unitRoleUnused .next) favorableNextS21Before [] (.query 0) = treeIndex ((0/1)/2) (7/5) (nextNormalPenalty favorableNextS21Before) 20 2 := by
  have hs : replayBackup favorableNextS21Before emptyStatistics ([]++[.query 0]) = ⟨2,(0/1)⟩ := by
    rw [replayBackup_empty_closed_form]
    simp +decide [backedEvents,favorableNextS21Before,favorableNextProposal,favorableNextEvent1,favorableNextEvent2,favorableNextEvent3,favorableNextEvent4,favorableNextEvent5,favorableNextEvent6,favorableNextEvent7,favorableNextEvent8,favorableNextEvent9,favorableNextEvent10,favorableNextEvent11,favorableNextEvent12,favorableNextEvent13,favorableNextEvent14,favorableNextEvent15,favorableNextEvent16,favorableNextEvent17,favorableNextEvent18,favorableNextEvent19,favorableNextEvent20,taskReward]
    <;> norm_num
  have hp : rawVisits favorableNextS21Before [] = 20 := by decide
  have hn : rawVisits favorableNextS21Before ([]++[.query 0]) = 2 := by decide
  have hz : (controlPenalty savedCref uniformQuoteError unitRoleUnused .next) favorableNextS21Before [] (.query 0) = (nextNormalPenalty favorableNextS21Before) := by
    simpa only [favorableNextS21Before,nextNormalPenalty] using AgentUCTNextExact.favorable_next_normal_root_quotes_exact 20 (by omega) 0 (by decide)
  unfold indexScore
  rw [hs,hp,hn,hz]
  simp only [BackupStat.mean]
  norm_num

theorem favorableNextS21D0I1 : indexScore (7/5) (controlPenalty savedCref uniformQuoteError unitRoleUnused .next) favorableNextS21Before [] (.query 1) = treeIndex ((1/2)/4) (7/5) 0 20 4 := by
  have hs : replayBackup favorableNextS21Before emptyStatistics ([]++[.query 1]) = ⟨4,(1/2)⟩ := by
    rw [replayBackup_empty_closed_form]
    simp +decide [backedEvents,favorableNextS21Before,favorableNextProposal,favorableNextEvent1,favorableNextEvent2,favorableNextEvent3,favorableNextEvent4,favorableNextEvent5,favorableNextEvent6,favorableNextEvent7,favorableNextEvent8,favorableNextEvent9,favorableNextEvent10,favorableNextEvent11,favorableNextEvent12,favorableNextEvent13,favorableNextEvent14,favorableNextEvent15,favorableNextEvent16,favorableNextEvent17,favorableNextEvent18,favorableNextEvent19,favorableNextEvent20,taskReward]
    <;> norm_num
  have hp : rawVisits favorableNextS21Before [] = 20 := by decide
  have hn : rawVisits favorableNextS21Before ([]++[.query 1]) = 4 := by decide
  have hz : (controlPenalty savedCref uniformQuoteError unitRoleUnused .next) favorableNextS21Before [] (.query 1) = 0 := by
    apply control_penalty_empty_suffix
    decide
  unfold indexScore
  rw [hs,hp,hn,hz]
  simp only [BackupStat.mean]
  norm_num

theorem favorableNextS21D0I2 : indexScore (7/5) (controlPenalty savedCref uniformQuoteError unitRoleUnused .next) favorableNextS21Before [] (.query 2) = treeIndex ((0/1)/2) (7/5) (nextNormalPenalty favorableNextS21Before) 20 2 := by
  have hs : replayBackup favorableNextS21Before emptyStatistics ([]++[.query 2]) = ⟨2,(0/1)⟩ := by
    rw [replayBackup_empty_closed_form]
    simp +decide [backedEvents,favorableNextS21Before,favorableNextProposal,favorableNextEvent1,favorableNextEvent2,favorableNextEvent3,favorableNextEvent4,favorableNextEvent5,favorableNextEvent6,favorableNextEvent7,favorableNextEvent8,favorableNextEvent9,favorableNextEvent10,favorableNextEvent11,favorableNextEvent12,favorableNextEvent13,favorableNextEvent14,favorableNextEvent15,favorableNextEvent16,favorableNextEvent17,favorableNextEvent18,favorableNextEvent19,favorableNextEvent20,taskReward]
    <;> norm_num
  have hp : rawVisits favorableNextS21Before [] = 20 := by decide
  have hn : rawVisits favorableNextS21Before ([]++[.query 2]) = 2 := by decide
  have hz : (controlPenalty savedCref uniformQuoteError unitRoleUnused .next) favorableNextS21Before [] (.query 2) = (nextNormalPenalty favorableNextS21Before) := by
    simpa only [favorableNextS21Before,nextNormalPenalty] using AgentUCTNextExact.favorable_next_normal_root_quotes_exact 20 (by omega) 2 (by decide)
  unfold indexScore
  rw [hs,hp,hn,hz]
  simp only [BackupStat.mean]
  norm_num

theorem favorableNextS21D0I3 : indexScore (7/5) (controlPenalty savedCref uniformQuoteError unitRoleUnused .next) favorableNextS21Before [] (.query 3) = treeIndex ((0/1)/2) (7/5) (nextNormalPenalty favorableNextS21Before) 20 2 := by
  have hs : replayBackup favorableNextS21Before emptyStatistics ([]++[.query 3]) = ⟨2,(0/1)⟩ := by
    rw [replayBackup_empty_closed_form]
    simp +decide [backedEvents,favorableNextS21Before,favorableNextProposal,favorableNextEvent1,favorableNextEvent2,favorableNextEvent3,favorableNextEvent4,favorableNextEvent5,favorableNextEvent6,favorableNextEvent7,favorableNextEvent8,favorableNextEvent9,favorableNextEvent10,favorableNextEvent11,favorableNextEvent12,favorableNextEvent13,favorableNextEvent14,favorableNextEvent15,favorableNextEvent16,favorableNextEvent17,favorableNextEvent18,favorableNextEvent19,favorableNextEvent20,taskReward]
    <;> norm_num
  have hp : rawVisits favorableNextS21Before [] = 20 := by decide
  have hn : rawVisits favorableNextS21Before ([]++[.query 3]) = 2 := by decide
  have hz : (controlPenalty savedCref uniformQuoteError unitRoleUnused .next) favorableNextS21Before [] (.query 3) = (nextNormalPenalty favorableNextS21Before) := by
    simpa only [favorableNextS21Before,nextNormalPenalty] using AgentUCTNextExact.favorable_next_normal_root_quotes_exact 20 (by omega) 3 (by decide)
  unfold indexScore
  rw [hs,hp,hn,hz]
  simp only [BackupStat.mean]
  norm_num

theorem favorableNextS21D0I4 : indexScore (7/5) (controlPenalty savedCref uniformQuoteError unitRoleUnused .next) favorableNextS21Before [] (.query 4) = treeIndex ((0/1)/2) (7/5) (nextNormalPenalty favorableNextS21Before) 20 2 := by
  have hs : replayBackup favorableNextS21Before emptyStatistics ([]++[.query 4]) = ⟨2,(0/1)⟩ := by
    rw [replayBackup_empty_closed_form]
    simp +decide [backedEvents,favorableNextS21Before,favorableNextProposal,favorableNextEvent1,favorableNextEvent2,favorableNextEvent3,favorableNextEvent4,favorableNextEvent5,favorableNextEvent6,favorableNextEvent7,favorableNextEvent8,favorableNextEvent9,favorableNextEvent10,favorableNextEvent11,favorableNextEvent12,favorableNextEvent13,favorableNextEvent14,favorableNextEvent15,favorableNextEvent16,favorableNextEvent17,favorableNextEvent18,favorableNextEvent19,favorableNextEvent20,taskReward]
    <;> norm_num
  have hp : rawVisits favorableNextS21Before [] = 20 := by decide
  have hn : rawVisits favorableNextS21Before ([]++[.query 4]) = 2 := by decide
  have hz : (controlPenalty savedCref uniformQuoteError unitRoleUnused .next) favorableNextS21Before [] (.query 4) = (nextNormalPenalty favorableNextS21Before) := by
    simpa only [favorableNextS21Before,nextNormalPenalty] using AgentUCTNextExact.favorable_next_normal_root_quotes_exact 20 (by omega) 4 (by decide)
  unfold indexScore
  rw [hs,hp,hn,hz]
  simp only [BackupStat.mean]
  norm_num

theorem favorableNextS21D0I5 : indexScore (7/5) (controlPenalty savedCref uniformQuoteError unitRoleUnused .next) favorableNextS21Before [] (.query 5) = treeIndex ((6/5)/4) (7/5) (nextNormalPenalty favorableNextS21Before) 20 4 := by
  have hs : replayBackup favorableNextS21Before emptyStatistics ([]++[.query 5]) = ⟨4,(6/5)⟩ := by
    rw [replayBackup_empty_closed_form]
    simp +decide [backedEvents,favorableNextS21Before,favorableNextProposal,favorableNextEvent1,favorableNextEvent2,favorableNextEvent3,favorableNextEvent4,favorableNextEvent5,favorableNextEvent6,favorableNextEvent7,favorableNextEvent8,favorableNextEvent9,favorableNextEvent10,favorableNextEvent11,favorableNextEvent12,favorableNextEvent13,favorableNextEvent14,favorableNextEvent15,favorableNextEvent16,favorableNextEvent17,favorableNextEvent18,favorableNextEvent19,favorableNextEvent20,taskReward]
    <;> norm_num
  have hp : rawVisits favorableNextS21Before [] = 20 := by decide
  have hn : rawVisits favorableNextS21Before ([]++[.query 5]) = 4 := by decide
  have hz : (controlPenalty savedCref uniformQuoteError unitRoleUnused .next) favorableNextS21Before [] (.query 5) = (nextNormalPenalty favorableNextS21Before) := by
    simpa only [favorableNextS21Before,nextNormalPenalty] using AgentUCTNextExact.favorable_next_normal_root_quotes_exact 20 (by omega) 5 (by decide)
  unfold indexScore
  rw [hs,hp,hn,hz]
  simp only [BackupStat.mean]
  norm_num

theorem favorableNextS21D0I6 : indexScore (7/5) (controlPenalty savedCref uniformQuoteError unitRoleUnused .next) favorableNextS21Before [] (.query 6) = treeIndex ((0/1)/2) (7/5) (nextNormalPenalty favorableNextS21Before) 20 2 := by
  have hs : replayBackup favorableNextS21Before emptyStatistics ([]++[.query 6]) = ⟨2,(0/1)⟩ := by
    rw [replayBackup_empty_closed_form]
    simp +decide [backedEvents,favorableNextS21Before,favorableNextProposal,favorableNextEvent1,favorableNextEvent2,favorableNextEvent3,favorableNextEvent4,favorableNextEvent5,favorableNextEvent6,favorableNextEvent7,favorableNextEvent8,favorableNextEvent9,favorableNextEvent10,favorableNextEvent11,favorableNextEvent12,favorableNextEvent13,favorableNextEvent14,favorableNextEvent15,favorableNextEvent16,favorableNextEvent17,favorableNextEvent18,favorableNextEvent19,favorableNextEvent20,taskReward]
    <;> norm_num
  have hp : rawVisits favorableNextS21Before [] = 20 := by decide
  have hn : rawVisits favorableNextS21Before ([]++[.query 6]) = 2 := by decide
  have hz : (controlPenalty savedCref uniformQuoteError unitRoleUnused .next) favorableNextS21Before [] (.query 6) = (nextNormalPenalty favorableNextS21Before) := by
    simpa only [favorableNextS21Before,nextNormalPenalty] using AgentUCTNextExact.favorable_next_normal_root_quotes_exact 20 (by omega) 6 (by decide)
  unfold indexScore
  rw [hs,hp,hn,hz]
  simp only [BackupStat.mean]
  norm_num

theorem favorableNextS21D0I7 : indexScore (7/5) (controlPenalty savedCref uniformQuoteError unitRoleUnused .next) favorableNextS21Before [] (.query 7) = treeIndex ((0/1)/2) (7/5) (nextNormalPenalty favorableNextS21Before) 20 2 := by
  have hs : replayBackup favorableNextS21Before emptyStatistics ([]++[.query 7]) = ⟨2,(0/1)⟩ := by
    rw [replayBackup_empty_closed_form]
    simp +decide [backedEvents,favorableNextS21Before,favorableNextProposal,favorableNextEvent1,favorableNextEvent2,favorableNextEvent3,favorableNextEvent4,favorableNextEvent5,favorableNextEvent6,favorableNextEvent7,favorableNextEvent8,favorableNextEvent9,favorableNextEvent10,favorableNextEvent11,favorableNextEvent12,favorableNextEvent13,favorableNextEvent14,favorableNextEvent15,favorableNextEvent16,favorableNextEvent17,favorableNextEvent18,favorableNextEvent19,favorableNextEvent20,taskReward]
    <;> norm_num
  have hp : rawVisits favorableNextS21Before [] = 20 := by decide
  have hn : rawVisits favorableNextS21Before ([]++[.query 7]) = 2 := by decide
  have hz : (controlPenalty savedCref uniformQuoteError unitRoleUnused .next) favorableNextS21Before [] (.query 7) = (nextNormalPenalty favorableNextS21Before) := by
    simpa only [favorableNextS21Before,nextNormalPenalty] using AgentUCTNextExact.favorable_next_normal_root_quotes_exact 20 (by omega) 7 (by decide)
  unfold indexScore
  rw [hs,hp,hn,hz]
  simp only [BackupStat.mean]
  norm_num

theorem favorableNextS21D0Cmp1 : indexScore (7/5) (controlPenalty savedCref uniformQuoteError unitRoleUnused .next) favorableNextS21Before [] (.query 1) ≤ indexScore (7/5) (controlPenalty savedCref uniformQuoteError unitRoleUnused .next) favorableNextS21Before [] (.query 0) := by
  rw [favorableNextS21D0I1,favorableNextS21D0I0]
  have hk := favorable_next_penalty_interval 20 (by omega)
  change nextNormalPenaltyLower ≤ nextNormalPenalty favorableNextS21Before ∧ nextNormalPenalty favorableNextS21Before ≤ nextNormalPenaltyUpper at hk
  have hm : ((1/2)/4)+(61069967/50000000)-0 < ((0/1)/2)+(43182979/25000000)-(nextNormalPenalty favorableNextS21Before) := by
    have h : ((1/2)/4)+(61069967/50000000) < ((0/1)/2)+(43182979/25000000)-nextNormalPenaltyUpper := by norm_num [nextNormalPenaltyUpper,savedCref,uniformQuoteError]
    linarith [hk.2]
  have h := index_weak_order_from_intervals ((0/1)/2) ((1/2)/4) (nextNormalPenalty favorableNextS21Before) 0 (43182979/25000000) (61069967/50000000)
    (treeBonus (7/5) 20 2) (treeBonus (7/5) 20 4)
    (trajectory_bonus_20_2).1 (trajectory_bonus_20_4).2 hm.le
  simpa only [treeIndex] using h

theorem favorableNextS21D0Cmp2 : indexScore (7/5) (controlPenalty savedCref uniformQuoteError unitRoleUnused .next) favorableNextS21Before [] (.query 2) ≤ indexScore (7/5) (controlPenalty savedCref uniformQuoteError unitRoleUnused .next) favorableNextS21Before [] (.query 0) := by
  rw [favorableNextS21D0I2,favorableNextS21D0I0]

theorem favorableNextS21D0Cmp3 : indexScore (7/5) (controlPenalty savedCref uniformQuoteError unitRoleUnused .next) favorableNextS21Before [] (.query 3) ≤ indexScore (7/5) (controlPenalty savedCref uniformQuoteError unitRoleUnused .next) favorableNextS21Before [] (.query 0) := by
  rw [favorableNextS21D0I3,favorableNextS21D0I0]

theorem favorableNextS21D0Cmp4 : indexScore (7/5) (controlPenalty savedCref uniformQuoteError unitRoleUnused .next) favorableNextS21Before [] (.query 4) ≤ indexScore (7/5) (controlPenalty savedCref uniformQuoteError unitRoleUnused .next) favorableNextS21Before [] (.query 0) := by
  rw [favorableNextS21D0I4,favorableNextS21D0I0]

theorem favorableNextS21D0Cmp5 : indexScore (7/5) (controlPenalty savedCref uniformQuoteError unitRoleUnused .next) favorableNextS21Before [] (.query 5) ≤ indexScore (7/5) (controlPenalty savedCref uniformQuoteError unitRoleUnused .next) favorableNextS21Before [] (.query 0) := by
  rw [favorableNextS21D0I5,favorableNextS21D0I0]
  have hk := favorable_next_penalty_interval 20 (by omega)
  change nextNormalPenaltyLower ≤ nextNormalPenalty favorableNextS21Before ∧ nextNormalPenalty favorableNextS21Before ≤ nextNormalPenaltyUpper at hk
  have hm : ((6/5)/4)+(61069967/50000000)-(nextNormalPenalty favorableNextS21Before) < ((0/1)/2)+(43182979/25000000)-(nextNormalPenalty favorableNextS21Before) := by
    have h : (((6/5)/4)+(61069967/50000000) : ℝ) < ((0/1)/2)+(43182979/25000000) := by norm_num
    linarith
  have h := index_weak_order_from_intervals ((0/1)/2) ((6/5)/4) (nextNormalPenalty favorableNextS21Before) (nextNormalPenalty favorableNextS21Before) (43182979/25000000) (61069967/50000000)
    (treeBonus (7/5) 20 2) (treeBonus (7/5) 20 4)
    (trajectory_bonus_20_2).1 (trajectory_bonus_20_4).2 hm.le
  simpa only [treeIndex] using h

theorem favorableNextS21D0Cmp6 : indexScore (7/5) (controlPenalty savedCref uniformQuoteError unitRoleUnused .next) favorableNextS21Before [] (.query 6) ≤ indexScore (7/5) (controlPenalty savedCref uniformQuoteError unitRoleUnused .next) favorableNextS21Before [] (.query 0) := by
  rw [favorableNextS21D0I6,favorableNextS21D0I0]

theorem favorableNextS21D0Cmp7 : indexScore (7/5) (controlPenalty savedCref uniformQuoteError unitRoleUnused .next) favorableNextS21Before [] (.query 7) ≤ indexScore (7/5) (controlPenalty savedCref uniformQuoteError unitRoleUnused .next) favorableNextS21Before [] (.query 0) := by
  rw [favorableNextS21D0I7,favorableNextS21D0I0]

theorem favorableNextS21Choice0 : nativeFirstChoice (indexScore (7/5) (controlPenalty savedCref uniformQuoteError unitRoleUnused .next) favorableNextS21Before []) favorableNextS21Before [] = .query 0 := by
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
    · exact favorableNextS21D0Cmp1
    · exact favorableNextS21D0Cmp2
    · exact favorableNextS21D0Cmp3
    · exact favorableNextS21D0Cmp4
    · exact favorableNextS21D0Cmp5
    · exact favorableNextS21D0Cmp6
    · exact favorableNextS21D0Cmp7

theorem favorableNextS21ActualEvent : nativeEvent budgetTape (7/5) (controlPenalty savedCref uniformQuoteError unitRoleUnused .next)
    (taskReward false (2/5) (1/2)) favorableNextS21Before = favorableNextEvent21 := by
  have hs0 := native_select_existing_step budgetTape (7/5) (controlPenalty savedCref uniformQuoteError unitRoleUnused .next) favorableNextS21Before 8 [] (.query 0)
    (by decide) (by decide) favorableNextS21Choice0
  have hnew := native_select_new_step budgetTape (7/5) (controlPenalty savedCref uniformQuoteError unitRoleUnused .next) favorableNextS21Before 7 [.query 0]
    [.normalRetriever 4,.normalRetriever 6,.normalRetriever 7,.normalRetriever 8,.normalRetriever 5,.normalRetriever 1,.normalRetriever 2,.normalRetriever 3,.normalRetriever 12,.normalRetriever 14,.normalRetriever 13,.normalRetriever 21,.normalRetriever 23,.normalRetriever 22,.normalRetriever 9,.normalRetriever 11,.normalRetriever 10,.normalRetriever 15,.normalRetriever 17,.normalRetriever 16,.normalRetriever 18,.normalRetriever 20,.normalRetriever 19,.normalRetriever 24,.normalRetriever 25,.normalRetriever 26,.normalRetriever 27,.normalRetriever 28,.normalRetriever 29] (.normalRetriever 4) (by decide) (by decide) (by decide) (by decide)
  have hs : nativeSelect budgetTape (7/5) (controlPenalty savedCref uniformQuoteError unitRoleUnused .next) favorableNextS21Before 9 [] = [.query 0,.normalRetriever 4] := by
    rw [hs0]
    change nativeSelect budgetTape (7/5) (controlPenalty savedCref uniformQuoteError unitRoleUnused .next) favorableNextS21Before 8 [.query 0] = _
    rw [hnew] <;> rfl
  have hr : repairedRollout budgetTape favorableNextS21Before 9 [.query 0,.normalRetriever 4] = [.query 0,.normalRetriever 4,.selection 0,.width 0,.stop,.reranker 0,.topm 0,.context 0,.answer 0] := by decide
  simp only [nativeEvent,hs,hr]
  rfl

def favorableNextS22Before := favorableNextProposal.take 21

theorem favorableNextS22D0I0 : indexScore (7/5) (controlPenalty savedCref uniformQuoteError unitRoleUnused .next) favorableNextS22Before [] (.query 0) = treeIndex ((0/1)/3) (7/5) (nextNormalPenalty favorableNextS22Before) 21 3 := by
  have hs : replayBackup favorableNextS22Before emptyStatistics ([]++[.query 0]) = ⟨3,(0/1)⟩ := by
    rw [replayBackup_empty_closed_form]
    simp +decide [backedEvents,favorableNextS22Before,favorableNextProposal,favorableNextEvent1,favorableNextEvent2,favorableNextEvent3,favorableNextEvent4,favorableNextEvent5,favorableNextEvent6,favorableNextEvent7,favorableNextEvent8,favorableNextEvent9,favorableNextEvent10,favorableNextEvent11,favorableNextEvent12,favorableNextEvent13,favorableNextEvent14,favorableNextEvent15,favorableNextEvent16,favorableNextEvent17,favorableNextEvent18,favorableNextEvent19,favorableNextEvent20,favorableNextEvent21,taskReward]
    <;> norm_num
  have hp : rawVisits favorableNextS22Before [] = 21 := by decide
  have hn : rawVisits favorableNextS22Before ([]++[.query 0]) = 3 := by decide
  have hz : (controlPenalty savedCref uniformQuoteError unitRoleUnused .next) favorableNextS22Before [] (.query 0) = (nextNormalPenalty favorableNextS22Before) := by
    simpa only [favorableNextS22Before,nextNormalPenalty] using AgentUCTNextExact.favorable_next_normal_root_quotes_exact 21 (by omega) 0 (by decide)
  unfold indexScore
  rw [hs,hp,hn,hz]
  simp only [BackupStat.mean]
  norm_num

theorem favorableNextS22D0I1 : indexScore (7/5) (controlPenalty savedCref uniformQuoteError unitRoleUnused .next) favorableNextS22Before [] (.query 1) = treeIndex ((1/2)/4) (7/5) 0 21 4 := by
  have hs : replayBackup favorableNextS22Before emptyStatistics ([]++[.query 1]) = ⟨4,(1/2)⟩ := by
    rw [replayBackup_empty_closed_form]
    simp +decide [backedEvents,favorableNextS22Before,favorableNextProposal,favorableNextEvent1,favorableNextEvent2,favorableNextEvent3,favorableNextEvent4,favorableNextEvent5,favorableNextEvent6,favorableNextEvent7,favorableNextEvent8,favorableNextEvent9,favorableNextEvent10,favorableNextEvent11,favorableNextEvent12,favorableNextEvent13,favorableNextEvent14,favorableNextEvent15,favorableNextEvent16,favorableNextEvent17,favorableNextEvent18,favorableNextEvent19,favorableNextEvent20,favorableNextEvent21,taskReward]
    <;> norm_num
  have hp : rawVisits favorableNextS22Before [] = 21 := by decide
  have hn : rawVisits favorableNextS22Before ([]++[.query 1]) = 4 := by decide
  have hz : (controlPenalty savedCref uniformQuoteError unitRoleUnused .next) favorableNextS22Before [] (.query 1) = 0 := by
    apply control_penalty_empty_suffix
    decide
  unfold indexScore
  rw [hs,hp,hn,hz]
  simp only [BackupStat.mean]
  norm_num

theorem favorableNextS22D0I2 : indexScore (7/5) (controlPenalty savedCref uniformQuoteError unitRoleUnused .next) favorableNextS22Before [] (.query 2) = treeIndex ((0/1)/2) (7/5) (nextNormalPenalty favorableNextS22Before) 21 2 := by
  have hs : replayBackup favorableNextS22Before emptyStatistics ([]++[.query 2]) = ⟨2,(0/1)⟩ := by
    rw [replayBackup_empty_closed_form]
    simp +decide [backedEvents,favorableNextS22Before,favorableNextProposal,favorableNextEvent1,favorableNextEvent2,favorableNextEvent3,favorableNextEvent4,favorableNextEvent5,favorableNextEvent6,favorableNextEvent7,favorableNextEvent8,favorableNextEvent9,favorableNextEvent10,favorableNextEvent11,favorableNextEvent12,favorableNextEvent13,favorableNextEvent14,favorableNextEvent15,favorableNextEvent16,favorableNextEvent17,favorableNextEvent18,favorableNextEvent19,favorableNextEvent20,favorableNextEvent21,taskReward]
    <;> norm_num
  have hp : rawVisits favorableNextS22Before [] = 21 := by decide
  have hn : rawVisits favorableNextS22Before ([]++[.query 2]) = 2 := by decide
  have hz : (controlPenalty savedCref uniformQuoteError unitRoleUnused .next) favorableNextS22Before [] (.query 2) = (nextNormalPenalty favorableNextS22Before) := by
    simpa only [favorableNextS22Before,nextNormalPenalty] using AgentUCTNextExact.favorable_next_normal_root_quotes_exact 21 (by omega) 2 (by decide)
  unfold indexScore
  rw [hs,hp,hn,hz]
  simp only [BackupStat.mean]
  norm_num

theorem favorableNextS22D0I3 : indexScore (7/5) (controlPenalty savedCref uniformQuoteError unitRoleUnused .next) favorableNextS22Before [] (.query 3) = treeIndex ((0/1)/2) (7/5) (nextNormalPenalty favorableNextS22Before) 21 2 := by
  have hs : replayBackup favorableNextS22Before emptyStatistics ([]++[.query 3]) = ⟨2,(0/1)⟩ := by
    rw [replayBackup_empty_closed_form]
    simp +decide [backedEvents,favorableNextS22Before,favorableNextProposal,favorableNextEvent1,favorableNextEvent2,favorableNextEvent3,favorableNextEvent4,favorableNextEvent5,favorableNextEvent6,favorableNextEvent7,favorableNextEvent8,favorableNextEvent9,favorableNextEvent10,favorableNextEvent11,favorableNextEvent12,favorableNextEvent13,favorableNextEvent14,favorableNextEvent15,favorableNextEvent16,favorableNextEvent17,favorableNextEvent18,favorableNextEvent19,favorableNextEvent20,favorableNextEvent21,taskReward]
    <;> norm_num
  have hp : rawVisits favorableNextS22Before [] = 21 := by decide
  have hn : rawVisits favorableNextS22Before ([]++[.query 3]) = 2 := by decide
  have hz : (controlPenalty savedCref uniformQuoteError unitRoleUnused .next) favorableNextS22Before [] (.query 3) = (nextNormalPenalty favorableNextS22Before) := by
    simpa only [favorableNextS22Before,nextNormalPenalty] using AgentUCTNextExact.favorable_next_normal_root_quotes_exact 21 (by omega) 3 (by decide)
  unfold indexScore
  rw [hs,hp,hn,hz]
  simp only [BackupStat.mean]
  norm_num

theorem favorableNextS22D0I4 : indexScore (7/5) (controlPenalty savedCref uniformQuoteError unitRoleUnused .next) favorableNextS22Before [] (.query 4) = treeIndex ((0/1)/2) (7/5) (nextNormalPenalty favorableNextS22Before) 21 2 := by
  have hs : replayBackup favorableNextS22Before emptyStatistics ([]++[.query 4]) = ⟨2,(0/1)⟩ := by
    rw [replayBackup_empty_closed_form]
    simp +decide [backedEvents,favorableNextS22Before,favorableNextProposal,favorableNextEvent1,favorableNextEvent2,favorableNextEvent3,favorableNextEvent4,favorableNextEvent5,favorableNextEvent6,favorableNextEvent7,favorableNextEvent8,favorableNextEvent9,favorableNextEvent10,favorableNextEvent11,favorableNextEvent12,favorableNextEvent13,favorableNextEvent14,favorableNextEvent15,favorableNextEvent16,favorableNextEvent17,favorableNextEvent18,favorableNextEvent19,favorableNextEvent20,favorableNextEvent21,taskReward]
    <;> norm_num
  have hp : rawVisits favorableNextS22Before [] = 21 := by decide
  have hn : rawVisits favorableNextS22Before ([]++[.query 4]) = 2 := by decide
  have hz : (controlPenalty savedCref uniformQuoteError unitRoleUnused .next) favorableNextS22Before [] (.query 4) = (nextNormalPenalty favorableNextS22Before) := by
    simpa only [favorableNextS22Before,nextNormalPenalty] using AgentUCTNextExact.favorable_next_normal_root_quotes_exact 21 (by omega) 4 (by decide)
  unfold indexScore
  rw [hs,hp,hn,hz]
  simp only [BackupStat.mean]
  norm_num

theorem favorableNextS22D0I5 : indexScore (7/5) (controlPenalty savedCref uniformQuoteError unitRoleUnused .next) favorableNextS22Before [] (.query 5) = treeIndex ((6/5)/4) (7/5) (nextNormalPenalty favorableNextS22Before) 21 4 := by
  have hs : replayBackup favorableNextS22Before emptyStatistics ([]++[.query 5]) = ⟨4,(6/5)⟩ := by
    rw [replayBackup_empty_closed_form]
    simp +decide [backedEvents,favorableNextS22Before,favorableNextProposal,favorableNextEvent1,favorableNextEvent2,favorableNextEvent3,favorableNextEvent4,favorableNextEvent5,favorableNextEvent6,favorableNextEvent7,favorableNextEvent8,favorableNextEvent9,favorableNextEvent10,favorableNextEvent11,favorableNextEvent12,favorableNextEvent13,favorableNextEvent14,favorableNextEvent15,favorableNextEvent16,favorableNextEvent17,favorableNextEvent18,favorableNextEvent19,favorableNextEvent20,favorableNextEvent21,taskReward]
    <;> norm_num
  have hp : rawVisits favorableNextS22Before [] = 21 := by decide
  have hn : rawVisits favorableNextS22Before ([]++[.query 5]) = 4 := by decide
  have hz : (controlPenalty savedCref uniformQuoteError unitRoleUnused .next) favorableNextS22Before [] (.query 5) = (nextNormalPenalty favorableNextS22Before) := by
    simpa only [favorableNextS22Before,nextNormalPenalty] using AgentUCTNextExact.favorable_next_normal_root_quotes_exact 21 (by omega) 5 (by decide)
  unfold indexScore
  rw [hs,hp,hn,hz]
  simp only [BackupStat.mean]
  norm_num

theorem favorableNextS22D0I6 : indexScore (7/5) (controlPenalty savedCref uniformQuoteError unitRoleUnused .next) favorableNextS22Before [] (.query 6) = treeIndex ((0/1)/2) (7/5) (nextNormalPenalty favorableNextS22Before) 21 2 := by
  have hs : replayBackup favorableNextS22Before emptyStatistics ([]++[.query 6]) = ⟨2,(0/1)⟩ := by
    rw [replayBackup_empty_closed_form]
    simp +decide [backedEvents,favorableNextS22Before,favorableNextProposal,favorableNextEvent1,favorableNextEvent2,favorableNextEvent3,favorableNextEvent4,favorableNextEvent5,favorableNextEvent6,favorableNextEvent7,favorableNextEvent8,favorableNextEvent9,favorableNextEvent10,favorableNextEvent11,favorableNextEvent12,favorableNextEvent13,favorableNextEvent14,favorableNextEvent15,favorableNextEvent16,favorableNextEvent17,favorableNextEvent18,favorableNextEvent19,favorableNextEvent20,favorableNextEvent21,taskReward]
    <;> norm_num
  have hp : rawVisits favorableNextS22Before [] = 21 := by decide
  have hn : rawVisits favorableNextS22Before ([]++[.query 6]) = 2 := by decide
  have hz : (controlPenalty savedCref uniformQuoteError unitRoleUnused .next) favorableNextS22Before [] (.query 6) = (nextNormalPenalty favorableNextS22Before) := by
    simpa only [favorableNextS22Before,nextNormalPenalty] using AgentUCTNextExact.favorable_next_normal_root_quotes_exact 21 (by omega) 6 (by decide)
  unfold indexScore
  rw [hs,hp,hn,hz]
  simp only [BackupStat.mean]
  norm_num

theorem favorableNextS22D0I7 : indexScore (7/5) (controlPenalty savedCref uniformQuoteError unitRoleUnused .next) favorableNextS22Before [] (.query 7) = treeIndex ((0/1)/2) (7/5) (nextNormalPenalty favorableNextS22Before) 21 2 := by
  have hs : replayBackup favorableNextS22Before emptyStatistics ([]++[.query 7]) = ⟨2,(0/1)⟩ := by
    rw [replayBackup_empty_closed_form]
    simp +decide [backedEvents,favorableNextS22Before,favorableNextProposal,favorableNextEvent1,favorableNextEvent2,favorableNextEvent3,favorableNextEvent4,favorableNextEvent5,favorableNextEvent6,favorableNextEvent7,favorableNextEvent8,favorableNextEvent9,favorableNextEvent10,favorableNextEvent11,favorableNextEvent12,favorableNextEvent13,favorableNextEvent14,favorableNextEvent15,favorableNextEvent16,favorableNextEvent17,favorableNextEvent18,favorableNextEvent19,favorableNextEvent20,favorableNextEvent21,taskReward]
    <;> norm_num
  have hp : rawVisits favorableNextS22Before [] = 21 := by decide
  have hn : rawVisits favorableNextS22Before ([]++[.query 7]) = 2 := by decide
  have hz : (controlPenalty savedCref uniformQuoteError unitRoleUnused .next) favorableNextS22Before [] (.query 7) = (nextNormalPenalty favorableNextS22Before) := by
    simpa only [favorableNextS22Before,nextNormalPenalty] using AgentUCTNextExact.favorable_next_normal_root_quotes_exact 21 (by omega) 7 (by decide)
  unfold indexScore
  rw [hs,hp,hn,hz]
  simp only [BackupStat.mean]
  norm_num

theorem favorableNextS22D0Cmp0 : indexScore (7/5) (controlPenalty savedCref uniformQuoteError unitRoleUnused .next) favorableNextS22Before [] (.query 0) < indexScore (7/5) (controlPenalty savedCref uniformQuoteError unitRoleUnused .next) favorableNextS22Before [] (.query 2) := by
  rw [favorableNextS22D0I0,favorableNextS22D0I2]
  have hk := favorable_next_penalty_interval 21 (by omega)
  change nextNormalPenaltyLower ≤ nextNormalPenalty favorableNextS22Before ∧ nextNormalPenalty favorableNextS22Before ≤ nextNormalPenaltyUpper at hk
  have hm : ((0/1)/3)+(17763557/12500000)-(nextNormalPenalty favorableNextS22Before) < ((0/1)/2)+(87023293/50000000)-(nextNormalPenalty favorableNextS22Before) := by
    have h : (((0/1)/3)+(17763557/12500000) : ℝ) < ((0/1)/2)+(87023293/50000000) := by norm_num
    linarith
  have h := index_strict_order_from_intervals ((0/1)/2) ((0/1)/3) (nextNormalPenalty favorableNextS22Before) (nextNormalPenalty favorableNextS22Before) (87023293/50000000) (17763557/12500000)
    (treeBonus (7/5) 21 2) (treeBonus (7/5) 21 3)
    (trajectory_bonus_21_2).1 (trajectory_bonus_21_3).2 hm
  simpa only [treeIndex] using h

theorem favorableNextS22D0Cmp1 : indexScore (7/5) (controlPenalty savedCref uniformQuoteError unitRoleUnused .next) favorableNextS22Before [] (.query 1) < indexScore (7/5) (controlPenalty savedCref uniformQuoteError unitRoleUnused .next) favorableNextS22Before [] (.query 2) := by
  rw [favorableNextS22D0I1,favorableNextS22D0I2]
  have hk := favorable_next_penalty_interval 21 (by omega)
  change nextNormalPenaltyLower ≤ nextNormalPenalty favorableNextS22Before ∧ nextNormalPenalty favorableNextS22Before ≤ nextNormalPenaltyUpper at hk
  have hm : ((1/2)/4)+(61534767/50000000)-0 < ((0/1)/2)+(87023293/50000000)-(nextNormalPenalty favorableNextS22Before) := by
    have h : ((1/2)/4)+(61534767/50000000) < ((0/1)/2)+(87023293/50000000)-nextNormalPenaltyUpper := by norm_num [nextNormalPenaltyUpper,savedCref,uniformQuoteError]
    linarith [hk.2]
  have h := index_strict_order_from_intervals ((0/1)/2) ((1/2)/4) (nextNormalPenalty favorableNextS22Before) 0 (87023293/50000000) (61534767/50000000)
    (treeBonus (7/5) 21 2) (treeBonus (7/5) 21 4)
    (trajectory_bonus_21_2).1 (trajectory_bonus_21_4).2 hm
  simpa only [treeIndex] using h

theorem favorableNextS22D0Cmp3 : indexScore (7/5) (controlPenalty savedCref uniformQuoteError unitRoleUnused .next) favorableNextS22Before [] (.query 3) ≤ indexScore (7/5) (controlPenalty savedCref uniformQuoteError unitRoleUnused .next) favorableNextS22Before [] (.query 2) := by
  rw [favorableNextS22D0I3,favorableNextS22D0I2]

theorem favorableNextS22D0Cmp4 : indexScore (7/5) (controlPenalty savedCref uniformQuoteError unitRoleUnused .next) favorableNextS22Before [] (.query 4) ≤ indexScore (7/5) (controlPenalty savedCref uniformQuoteError unitRoleUnused .next) favorableNextS22Before [] (.query 2) := by
  rw [favorableNextS22D0I4,favorableNextS22D0I2]

theorem favorableNextS22D0Cmp5 : indexScore (7/5) (controlPenalty savedCref uniformQuoteError unitRoleUnused .next) favorableNextS22Before [] (.query 5) ≤ indexScore (7/5) (controlPenalty savedCref uniformQuoteError unitRoleUnused .next) favorableNextS22Before [] (.query 2) := by
  rw [favorableNextS22D0I5,favorableNextS22D0I2]
  have hk := favorable_next_penalty_interval 21 (by omega)
  change nextNormalPenaltyLower ≤ nextNormalPenalty favorableNextS22Before ∧ nextNormalPenalty favorableNextS22Before ≤ nextNormalPenaltyUpper at hk
  have hm : ((6/5)/4)+(61534767/50000000)-(nextNormalPenalty favorableNextS22Before) < ((0/1)/2)+(87023293/50000000)-(nextNormalPenalty favorableNextS22Before) := by
    have h : (((6/5)/4)+(61534767/50000000) : ℝ) < ((0/1)/2)+(87023293/50000000) := by norm_num
    linarith
  have h := index_weak_order_from_intervals ((0/1)/2) ((6/5)/4) (nextNormalPenalty favorableNextS22Before) (nextNormalPenalty favorableNextS22Before) (87023293/50000000) (61534767/50000000)
    (treeBonus (7/5) 21 2) (treeBonus (7/5) 21 4)
    (trajectory_bonus_21_2).1 (trajectory_bonus_21_4).2 hm.le
  simpa only [treeIndex] using h

theorem favorableNextS22D0Cmp6 : indexScore (7/5) (controlPenalty savedCref uniformQuoteError unitRoleUnused .next) favorableNextS22Before [] (.query 6) ≤ indexScore (7/5) (controlPenalty savedCref uniformQuoteError unitRoleUnused .next) favorableNextS22Before [] (.query 2) := by
  rw [favorableNextS22D0I6,favorableNextS22D0I2]

theorem favorableNextS22D0Cmp7 : indexScore (7/5) (controlPenalty savedCref uniformQuoteError unitRoleUnused .next) favorableNextS22Before [] (.query 7) ≤ indexScore (7/5) (controlPenalty savedCref uniformQuoteError unitRoleUnused .next) favorableNextS22Before [] (.query 2) := by
  rw [favorableNextS22D0I7,favorableNextS22D0I2]

theorem favorableNextS22Choice0 : nativeFirstChoice (indexScore (7/5) (controlPenalty savedCref uniformQuoteError unitRoleUnused .next) favorableNextS22Before []) favorableNextS22Before [] = .query 2 := by
  apply visited_choice_from_ordered_certificate _ _ [] [.query 0,.query 1] [.query 3,.query 4,.query 5,.query 6,.query 7] (.query 2) (by decide)
  · intro a ha
    have ho : orderedLegalAvailable [] = [.query 0,.query 1,.query 2,.query 3,.query 4,.query 5,.query 6,.query 7] := by decide
    rw [ho] at ha
    simp only [List.mem_cons,List.not_mem_nil,or_false] at ha
    rcases ha with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> decide
  · intro a ha
    simp only [List.mem_cons,List.not_mem_nil,or_false] at ha
    rcases ha with rfl | rfl
    · exact favorableNextS22D0Cmp0
    · exact favorableNextS22D0Cmp1
  · intro a ha
    simp only [List.mem_cons,List.not_mem_nil,or_false] at ha
    rcases ha with rfl | rfl | rfl | rfl | rfl
    · exact favorableNextS22D0Cmp3
    · exact favorableNextS22D0Cmp4
    · exact favorableNextS22D0Cmp5
    · exact favorableNextS22D0Cmp6
    · exact favorableNextS22D0Cmp7

theorem favorableNextS22ActualEvent : nativeEvent budgetTape (7/5) (controlPenalty savedCref uniformQuoteError unitRoleUnused .next)
    (taskReward false (2/5) (1/2)) favorableNextS22Before = favorableNextEvent22 := by
  have hs0 := native_select_existing_step budgetTape (7/5) (controlPenalty savedCref uniformQuoteError unitRoleUnused .next) favorableNextS22Before 8 [] (.query 2)
    (by decide) (by decide) favorableNextS22Choice0
  have hnew := native_select_new_step budgetTape (7/5) (controlPenalty savedCref uniformQuoteError unitRoleUnused .next) favorableNextS22Before 7 [.query 2]
    [.normalRetriever 4,.normalRetriever 6,.normalRetriever 7,.normalRetriever 8,.normalRetriever 5,.normalRetriever 1,.normalRetriever 2,.normalRetriever 3,.normalRetriever 12,.normalRetriever 14,.normalRetriever 13,.normalRetriever 21,.normalRetriever 23,.normalRetriever 22,.normalRetriever 9,.normalRetriever 11,.normalRetriever 10,.normalRetriever 15,.normalRetriever 17,.normalRetriever 16,.normalRetriever 18,.normalRetriever 20,.normalRetriever 19,.normalRetriever 24,.normalRetriever 25,.normalRetriever 26,.normalRetriever 27,.normalRetriever 28,.normalRetriever 29] (.normalRetriever 4) (by decide) (by decide) (by decide) (by decide)
  have hs : nativeSelect budgetTape (7/5) (controlPenalty savedCref uniformQuoteError unitRoleUnused .next) favorableNextS22Before 9 [] = [.query 2,.normalRetriever 4] := by
    rw [hs0]
    change nativeSelect budgetTape (7/5) (controlPenalty savedCref uniformQuoteError unitRoleUnused .next) favorableNextS22Before 8 [.query 2] = _
    rw [hnew] <;> rfl
  have hr : repairedRollout budgetTape favorableNextS22Before 9 [.query 2,.normalRetriever 4] = [.query 2,.normalRetriever 4,.selection 0,.width 0,.stop,.reranker 0,.topm 0,.context 0,.answer 0] := by decide
  simp only [nativeEvent,hs,hr]
  rfl

def favorableNextS23Before := favorableNextProposal.take 22

theorem favorableNextS23D0I0 : indexScore (7/5) (controlPenalty savedCref uniformQuoteError unitRoleUnused .next) favorableNextS23Before [] (.query 0) = treeIndex ((0/1)/3) (7/5) (nextNormalPenalty favorableNextS23Before) 22 3 := by
  have hs : replayBackup favorableNextS23Before emptyStatistics ([]++[.query 0]) = ⟨3,(0/1)⟩ := by
    rw [replayBackup_empty_closed_form]
    simp +decide [backedEvents,favorableNextS23Before,favorableNextProposal,favorableNextEvent1,favorableNextEvent2,favorableNextEvent3,favorableNextEvent4,favorableNextEvent5,favorableNextEvent6,favorableNextEvent7,favorableNextEvent8,favorableNextEvent9,favorableNextEvent10,favorableNextEvent11,favorableNextEvent12,favorableNextEvent13,favorableNextEvent14,favorableNextEvent15,favorableNextEvent16,favorableNextEvent17,favorableNextEvent18,favorableNextEvent19,favorableNextEvent20,favorableNextEvent21,favorableNextEvent22,taskReward]
    <;> norm_num
  have hp : rawVisits favorableNextS23Before [] = 22 := by decide
  have hn : rawVisits favorableNextS23Before ([]++[.query 0]) = 3 := by decide
  have hz : (controlPenalty savedCref uniformQuoteError unitRoleUnused .next) favorableNextS23Before [] (.query 0) = (nextNormalPenalty favorableNextS23Before) := by
    simpa only [favorableNextS23Before,nextNormalPenalty] using AgentUCTNextExact.favorable_next_normal_root_quotes_exact 22 (by omega) 0 (by decide)
  unfold indexScore
  rw [hs,hp,hn,hz]
  simp only [BackupStat.mean]
  norm_num

theorem favorableNextS23D0I1 : indexScore (7/5) (controlPenalty savedCref uniformQuoteError unitRoleUnused .next) favorableNextS23Before [] (.query 1) = treeIndex ((1/2)/4) (7/5) 0 22 4 := by
  have hs : replayBackup favorableNextS23Before emptyStatistics ([]++[.query 1]) = ⟨4,(1/2)⟩ := by
    rw [replayBackup_empty_closed_form]
    simp +decide [backedEvents,favorableNextS23Before,favorableNextProposal,favorableNextEvent1,favorableNextEvent2,favorableNextEvent3,favorableNextEvent4,favorableNextEvent5,favorableNextEvent6,favorableNextEvent7,favorableNextEvent8,favorableNextEvent9,favorableNextEvent10,favorableNextEvent11,favorableNextEvent12,favorableNextEvent13,favorableNextEvent14,favorableNextEvent15,favorableNextEvent16,favorableNextEvent17,favorableNextEvent18,favorableNextEvent19,favorableNextEvent20,favorableNextEvent21,favorableNextEvent22,taskReward]
    <;> norm_num
  have hp : rawVisits favorableNextS23Before [] = 22 := by decide
  have hn : rawVisits favorableNextS23Before ([]++[.query 1]) = 4 := by decide
  have hz : (controlPenalty savedCref uniformQuoteError unitRoleUnused .next) favorableNextS23Before [] (.query 1) = 0 := by
    apply control_penalty_empty_suffix
    decide
  unfold indexScore
  rw [hs,hp,hn,hz]
  simp only [BackupStat.mean]
  norm_num

theorem favorableNextS23D0I2 : indexScore (7/5) (controlPenalty savedCref uniformQuoteError unitRoleUnused .next) favorableNextS23Before [] (.query 2) = treeIndex ((0/1)/3) (7/5) (nextNormalPenalty favorableNextS23Before) 22 3 := by
  have hs : replayBackup favorableNextS23Before emptyStatistics ([]++[.query 2]) = ⟨3,(0/1)⟩ := by
    rw [replayBackup_empty_closed_form]
    simp +decide [backedEvents,favorableNextS23Before,favorableNextProposal,favorableNextEvent1,favorableNextEvent2,favorableNextEvent3,favorableNextEvent4,favorableNextEvent5,favorableNextEvent6,favorableNextEvent7,favorableNextEvent8,favorableNextEvent9,favorableNextEvent10,favorableNextEvent11,favorableNextEvent12,favorableNextEvent13,favorableNextEvent14,favorableNextEvent15,favorableNextEvent16,favorableNextEvent17,favorableNextEvent18,favorableNextEvent19,favorableNextEvent20,favorableNextEvent21,favorableNextEvent22,taskReward]
    <;> norm_num
  have hp : rawVisits favorableNextS23Before [] = 22 := by decide
  have hn : rawVisits favorableNextS23Before ([]++[.query 2]) = 3 := by decide
  have hz : (controlPenalty savedCref uniformQuoteError unitRoleUnused .next) favorableNextS23Before [] (.query 2) = (nextNormalPenalty favorableNextS23Before) := by
    simpa only [favorableNextS23Before,nextNormalPenalty] using AgentUCTNextExact.favorable_next_normal_root_quotes_exact 22 (by omega) 2 (by decide)
  unfold indexScore
  rw [hs,hp,hn,hz]
  simp only [BackupStat.mean]
  norm_num

theorem favorableNextS23D0I3 : indexScore (7/5) (controlPenalty savedCref uniformQuoteError unitRoleUnused .next) favorableNextS23Before [] (.query 3) = treeIndex ((0/1)/2) (7/5) (nextNormalPenalty favorableNextS23Before) 22 2 := by
  have hs : replayBackup favorableNextS23Before emptyStatistics ([]++[.query 3]) = ⟨2,(0/1)⟩ := by
    rw [replayBackup_empty_closed_form]
    simp +decide [backedEvents,favorableNextS23Before,favorableNextProposal,favorableNextEvent1,favorableNextEvent2,favorableNextEvent3,favorableNextEvent4,favorableNextEvent5,favorableNextEvent6,favorableNextEvent7,favorableNextEvent8,favorableNextEvent9,favorableNextEvent10,favorableNextEvent11,favorableNextEvent12,favorableNextEvent13,favorableNextEvent14,favorableNextEvent15,favorableNextEvent16,favorableNextEvent17,favorableNextEvent18,favorableNextEvent19,favorableNextEvent20,favorableNextEvent21,favorableNextEvent22,taskReward]
    <;> norm_num
  have hp : rawVisits favorableNextS23Before [] = 22 := by decide
  have hn : rawVisits favorableNextS23Before ([]++[.query 3]) = 2 := by decide
  have hz : (controlPenalty savedCref uniformQuoteError unitRoleUnused .next) favorableNextS23Before [] (.query 3) = (nextNormalPenalty favorableNextS23Before) := by
    simpa only [favorableNextS23Before,nextNormalPenalty] using AgentUCTNextExact.favorable_next_normal_root_quotes_exact 22 (by omega) 3 (by decide)
  unfold indexScore
  rw [hs,hp,hn,hz]
  simp only [BackupStat.mean]
  norm_num

theorem favorableNextS23D0I4 : indexScore (7/5) (controlPenalty savedCref uniformQuoteError unitRoleUnused .next) favorableNextS23Before [] (.query 4) = treeIndex ((0/1)/2) (7/5) (nextNormalPenalty favorableNextS23Before) 22 2 := by
  have hs : replayBackup favorableNextS23Before emptyStatistics ([]++[.query 4]) = ⟨2,(0/1)⟩ := by
    rw [replayBackup_empty_closed_form]
    simp +decide [backedEvents,favorableNextS23Before,favorableNextProposal,favorableNextEvent1,favorableNextEvent2,favorableNextEvent3,favorableNextEvent4,favorableNextEvent5,favorableNextEvent6,favorableNextEvent7,favorableNextEvent8,favorableNextEvent9,favorableNextEvent10,favorableNextEvent11,favorableNextEvent12,favorableNextEvent13,favorableNextEvent14,favorableNextEvent15,favorableNextEvent16,favorableNextEvent17,favorableNextEvent18,favorableNextEvent19,favorableNextEvent20,favorableNextEvent21,favorableNextEvent22,taskReward]
    <;> norm_num
  have hp : rawVisits favorableNextS23Before [] = 22 := by decide
  have hn : rawVisits favorableNextS23Before ([]++[.query 4]) = 2 := by decide
  have hz : (controlPenalty savedCref uniformQuoteError unitRoleUnused .next) favorableNextS23Before [] (.query 4) = (nextNormalPenalty favorableNextS23Before) := by
    simpa only [favorableNextS23Before,nextNormalPenalty] using AgentUCTNextExact.favorable_next_normal_root_quotes_exact 22 (by omega) 4 (by decide)
  unfold indexScore
  rw [hs,hp,hn,hz]
  simp only [BackupStat.mean]
  norm_num

theorem favorableNextS23D0I5 : indexScore (7/5) (controlPenalty savedCref uniformQuoteError unitRoleUnused .next) favorableNextS23Before [] (.query 5) = treeIndex ((6/5)/4) (7/5) (nextNormalPenalty favorableNextS23Before) 22 4 := by
  have hs : replayBackup favorableNextS23Before emptyStatistics ([]++[.query 5]) = ⟨4,(6/5)⟩ := by
    rw [replayBackup_empty_closed_form]
    simp +decide [backedEvents,favorableNextS23Before,favorableNextProposal,favorableNextEvent1,favorableNextEvent2,favorableNextEvent3,favorableNextEvent4,favorableNextEvent5,favorableNextEvent6,favorableNextEvent7,favorableNextEvent8,favorableNextEvent9,favorableNextEvent10,favorableNextEvent11,favorableNextEvent12,favorableNextEvent13,favorableNextEvent14,favorableNextEvent15,favorableNextEvent16,favorableNextEvent17,favorableNextEvent18,favorableNextEvent19,favorableNextEvent20,favorableNextEvent21,favorableNextEvent22,taskReward]
    <;> norm_num
  have hp : rawVisits favorableNextS23Before [] = 22 := by decide
  have hn : rawVisits favorableNextS23Before ([]++[.query 5]) = 4 := by decide
  have hz : (controlPenalty savedCref uniformQuoteError unitRoleUnused .next) favorableNextS23Before [] (.query 5) = (nextNormalPenalty favorableNextS23Before) := by
    simpa only [favorableNextS23Before,nextNormalPenalty] using AgentUCTNextExact.favorable_next_normal_root_quotes_exact 22 (by omega) 5 (by decide)
  unfold indexScore
  rw [hs,hp,hn,hz]
  simp only [BackupStat.mean]
  norm_num

theorem favorableNextS23D0I6 : indexScore (7/5) (controlPenalty savedCref uniformQuoteError unitRoleUnused .next) favorableNextS23Before [] (.query 6) = treeIndex ((0/1)/2) (7/5) (nextNormalPenalty favorableNextS23Before) 22 2 := by
  have hs : replayBackup favorableNextS23Before emptyStatistics ([]++[.query 6]) = ⟨2,(0/1)⟩ := by
    rw [replayBackup_empty_closed_form]
    simp +decide [backedEvents,favorableNextS23Before,favorableNextProposal,favorableNextEvent1,favorableNextEvent2,favorableNextEvent3,favorableNextEvent4,favorableNextEvent5,favorableNextEvent6,favorableNextEvent7,favorableNextEvent8,favorableNextEvent9,favorableNextEvent10,favorableNextEvent11,favorableNextEvent12,favorableNextEvent13,favorableNextEvent14,favorableNextEvent15,favorableNextEvent16,favorableNextEvent17,favorableNextEvent18,favorableNextEvent19,favorableNextEvent20,favorableNextEvent21,favorableNextEvent22,taskReward]
    <;> norm_num
  have hp : rawVisits favorableNextS23Before [] = 22 := by decide
  have hn : rawVisits favorableNextS23Before ([]++[.query 6]) = 2 := by decide
  have hz : (controlPenalty savedCref uniformQuoteError unitRoleUnused .next) favorableNextS23Before [] (.query 6) = (nextNormalPenalty favorableNextS23Before) := by
    simpa only [favorableNextS23Before,nextNormalPenalty] using AgentUCTNextExact.favorable_next_normal_root_quotes_exact 22 (by omega) 6 (by decide)
  unfold indexScore
  rw [hs,hp,hn,hz]
  simp only [BackupStat.mean]
  norm_num

theorem favorableNextS23D0I7 : indexScore (7/5) (controlPenalty savedCref uniformQuoteError unitRoleUnused .next) favorableNextS23Before [] (.query 7) = treeIndex ((0/1)/2) (7/5) (nextNormalPenalty favorableNextS23Before) 22 2 := by
  have hs : replayBackup favorableNextS23Before emptyStatistics ([]++[.query 7]) = ⟨2,(0/1)⟩ := by
    rw [replayBackup_empty_closed_form]
    simp +decide [backedEvents,favorableNextS23Before,favorableNextProposal,favorableNextEvent1,favorableNextEvent2,favorableNextEvent3,favorableNextEvent4,favorableNextEvent5,favorableNextEvent6,favorableNextEvent7,favorableNextEvent8,favorableNextEvent9,favorableNextEvent10,favorableNextEvent11,favorableNextEvent12,favorableNextEvent13,favorableNextEvent14,favorableNextEvent15,favorableNextEvent16,favorableNextEvent17,favorableNextEvent18,favorableNextEvent19,favorableNextEvent20,favorableNextEvent21,favorableNextEvent22,taskReward]
    <;> norm_num
  have hp : rawVisits favorableNextS23Before [] = 22 := by decide
  have hn : rawVisits favorableNextS23Before ([]++[.query 7]) = 2 := by decide
  have hz : (controlPenalty savedCref uniformQuoteError unitRoleUnused .next) favorableNextS23Before [] (.query 7) = (nextNormalPenalty favorableNextS23Before) := by
    simpa only [favorableNextS23Before,nextNormalPenalty] using AgentUCTNextExact.favorable_next_normal_root_quotes_exact 22 (by omega) 7 (by decide)
  unfold indexScore
  rw [hs,hp,hn,hz]
  simp only [BackupStat.mean]
  norm_num

theorem favorableNextS23D0Cmp0 : indexScore (7/5) (controlPenalty savedCref uniformQuoteError unitRoleUnused .next) favorableNextS23Before [] (.query 0) < indexScore (7/5) (controlPenalty savedCref uniformQuoteError unitRoleUnused .next) favorableNextS23Before [] (.query 3) := by
  rw [favorableNextS23D0I0,favorableNextS23D0I3]
  have hk := favorable_next_penalty_interval 22 (by omega)
  change nextNormalPenaltyLower ≤ nextNormalPenalty favorableNextS23Before ∧ nextNormalPenalty favorableNextS23Before ≤ nextNormalPenaltyUpper at hk
  have hm : ((0/1)/3)+(71563317/50000000)-(nextNormalPenalty favorableNextS23Before) < ((0/1)/2)+(8764679/5000000)-(nextNormalPenalty favorableNextS23Before) := by
    have h : (((0/1)/3)+(71563317/50000000) : ℝ) < ((0/1)/2)+(8764679/5000000) := by norm_num
    linarith
  have h := index_strict_order_from_intervals ((0/1)/2) ((0/1)/3) (nextNormalPenalty favorableNextS23Before) (nextNormalPenalty favorableNextS23Before) (8764679/5000000) (71563317/50000000)
    (treeBonus (7/5) 22 2) (treeBonus (7/5) 22 3)
    (trajectory_bonus_22_2).1 (trajectory_bonus_22_3).2 hm
  simpa only [treeIndex] using h

theorem favorableNextS23D0Cmp1 : indexScore (7/5) (controlPenalty savedCref uniformQuoteError unitRoleUnused .next) favorableNextS23Before [] (.query 1) < indexScore (7/5) (controlPenalty savedCref uniformQuoteError unitRoleUnused .next) favorableNextS23Before [] (.query 3) := by
  rw [favorableNextS23D0I1,favorableNextS23D0I3]
  have hk := favorable_next_penalty_interval 22 (by omega)
  change nextNormalPenaltyLower ≤ nextNormalPenalty favorableNextS23Before ∧ nextNormalPenalty favorableNextS23Before ≤ nextNormalPenaltyUpper at hk
  have hm : ((1/2)/4)+(1936739/1562500)-0 < ((0/1)/2)+(8764679/5000000)-(nextNormalPenalty favorableNextS23Before) := by
    have h : ((1/2)/4)+(1936739/1562500) < ((0/1)/2)+(8764679/5000000)-nextNormalPenaltyUpper := by norm_num [nextNormalPenaltyUpper,savedCref,uniformQuoteError]
    linarith [hk.2]
  have h := index_strict_order_from_intervals ((0/1)/2) ((1/2)/4) (nextNormalPenalty favorableNextS23Before) 0 (8764679/5000000) (1936739/1562500)
    (treeBonus (7/5) 22 2) (treeBonus (7/5) 22 4)
    (trajectory_bonus_22_2).1 (trajectory_bonus_22_4).2 hm
  simpa only [treeIndex] using h

theorem favorableNextS23D0Cmp2 : indexScore (7/5) (controlPenalty savedCref uniformQuoteError unitRoleUnused .next) favorableNextS23Before [] (.query 2) < indexScore (7/5) (controlPenalty savedCref uniformQuoteError unitRoleUnused .next) favorableNextS23Before [] (.query 3) := by
  rw [favorableNextS23D0I2,favorableNextS23D0I3]
  have hk := favorable_next_penalty_interval 22 (by omega)
  change nextNormalPenaltyLower ≤ nextNormalPenalty favorableNextS23Before ∧ nextNormalPenalty favorableNextS23Before ≤ nextNormalPenaltyUpper at hk
  have hm : ((0/1)/3)+(71563317/50000000)-(nextNormalPenalty favorableNextS23Before) < ((0/1)/2)+(8764679/5000000)-(nextNormalPenalty favorableNextS23Before) := by
    have h : (((0/1)/3)+(71563317/50000000) : ℝ) < ((0/1)/2)+(8764679/5000000) := by norm_num
    linarith
  have h := index_strict_order_from_intervals ((0/1)/2) ((0/1)/3) (nextNormalPenalty favorableNextS23Before) (nextNormalPenalty favorableNextS23Before) (8764679/5000000) (71563317/50000000)
    (treeBonus (7/5) 22 2) (treeBonus (7/5) 22 3)
    (trajectory_bonus_22_2).1 (trajectory_bonus_22_3).2 hm
  simpa only [treeIndex] using h

theorem favorableNextS23D0Cmp4 : indexScore (7/5) (controlPenalty savedCref uniformQuoteError unitRoleUnused .next) favorableNextS23Before [] (.query 4) ≤ indexScore (7/5) (controlPenalty savedCref uniformQuoteError unitRoleUnused .next) favorableNextS23Before [] (.query 3) := by
  rw [favorableNextS23D0I4,favorableNextS23D0I3]

theorem favorableNextS23D0Cmp5 : indexScore (7/5) (controlPenalty savedCref uniformQuoteError unitRoleUnused .next) favorableNextS23Before [] (.query 5) ≤ indexScore (7/5) (controlPenalty savedCref uniformQuoteError unitRoleUnused .next) favorableNextS23Before [] (.query 3) := by
  rw [favorableNextS23D0I5,favorableNextS23D0I3]
  have hk := favorable_next_penalty_interval 22 (by omega)
  change nextNormalPenaltyLower ≤ nextNormalPenalty favorableNextS23Before ∧ nextNormalPenalty favorableNextS23Before ≤ nextNormalPenaltyUpper at hk
  have hm : ((6/5)/4)+(1936739/1562500)-(nextNormalPenalty favorableNextS23Before) < ((0/1)/2)+(8764679/5000000)-(nextNormalPenalty favorableNextS23Before) := by
    have h : (((6/5)/4)+(1936739/1562500) : ℝ) < ((0/1)/2)+(8764679/5000000) := by norm_num
    linarith
  have h := index_weak_order_from_intervals ((0/1)/2) ((6/5)/4) (nextNormalPenalty favorableNextS23Before) (nextNormalPenalty favorableNextS23Before) (8764679/5000000) (1936739/1562500)
    (treeBonus (7/5) 22 2) (treeBonus (7/5) 22 4)
    (trajectory_bonus_22_2).1 (trajectory_bonus_22_4).2 hm.le
  simpa only [treeIndex] using h

theorem favorableNextS23D0Cmp6 : indexScore (7/5) (controlPenalty savedCref uniformQuoteError unitRoleUnused .next) favorableNextS23Before [] (.query 6) ≤ indexScore (7/5) (controlPenalty savedCref uniformQuoteError unitRoleUnused .next) favorableNextS23Before [] (.query 3) := by
  rw [favorableNextS23D0I6,favorableNextS23D0I3]

theorem favorableNextS23D0Cmp7 : indexScore (7/5) (controlPenalty savedCref uniformQuoteError unitRoleUnused .next) favorableNextS23Before [] (.query 7) ≤ indexScore (7/5) (controlPenalty savedCref uniformQuoteError unitRoleUnused .next) favorableNextS23Before [] (.query 3) := by
  rw [favorableNextS23D0I7,favorableNextS23D0I3]

theorem favorableNextS23Choice0 : nativeFirstChoice (indexScore (7/5) (controlPenalty savedCref uniformQuoteError unitRoleUnused .next) favorableNextS23Before []) favorableNextS23Before [] = .query 3 := by
  apply visited_choice_from_ordered_certificate _ _ [] [.query 0,.query 1,.query 2] [.query 4,.query 5,.query 6,.query 7] (.query 3) (by decide)
  · intro a ha
    have ho : orderedLegalAvailable [] = [.query 0,.query 1,.query 2,.query 3,.query 4,.query 5,.query 6,.query 7] := by decide
    rw [ho] at ha
    simp only [List.mem_cons,List.not_mem_nil,or_false] at ha
    rcases ha with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> decide
  · intro a ha
    simp only [List.mem_cons,List.not_mem_nil,or_false] at ha
    rcases ha with rfl | rfl | rfl
    · exact favorableNextS23D0Cmp0
    · exact favorableNextS23D0Cmp1
    · exact favorableNextS23D0Cmp2
  · intro a ha
    simp only [List.mem_cons,List.not_mem_nil,or_false] at ha
    rcases ha with rfl | rfl | rfl | rfl
    · exact favorableNextS23D0Cmp4
    · exact favorableNextS23D0Cmp5
    · exact favorableNextS23D0Cmp6
    · exact favorableNextS23D0Cmp7

theorem favorableNextS23ActualEvent : nativeEvent budgetTape (7/5) (controlPenalty savedCref uniformQuoteError unitRoleUnused .next)
    (taskReward false (2/5) (1/2)) favorableNextS23Before = favorableNextEvent23 := by
  have hs0 := native_select_existing_step budgetTape (7/5) (controlPenalty savedCref uniformQuoteError unitRoleUnused .next) favorableNextS23Before 8 [] (.query 3)
    (by decide) (by decide) favorableNextS23Choice0
  have hnew := native_select_new_step budgetTape (7/5) (controlPenalty savedCref uniformQuoteError unitRoleUnused .next) favorableNextS23Before 7 [.query 3]
    [.normalRetriever 4,.normalRetriever 6,.normalRetriever 7,.normalRetriever 8,.normalRetriever 5,.normalRetriever 1,.normalRetriever 2,.normalRetriever 3,.normalRetriever 12,.normalRetriever 14,.normalRetriever 13,.normalRetriever 21,.normalRetriever 23,.normalRetriever 22,.normalRetriever 9,.normalRetriever 11,.normalRetriever 10,.normalRetriever 15,.normalRetriever 17,.normalRetriever 16,.normalRetriever 18,.normalRetriever 20,.normalRetriever 19,.normalRetriever 24,.normalRetriever 25,.normalRetriever 26,.normalRetriever 27,.normalRetriever 28,.normalRetriever 29] (.normalRetriever 4) (by decide) (by decide) (by decide) (by decide)
  have hs : nativeSelect budgetTape (7/5) (controlPenalty savedCref uniformQuoteError unitRoleUnused .next) favorableNextS23Before 9 [] = [.query 3,.normalRetriever 4] := by
    rw [hs0]
    change nativeSelect budgetTape (7/5) (controlPenalty savedCref uniformQuoteError unitRoleUnused .next) favorableNextS23Before 8 [.query 3] = _
    rw [hnew] <;> rfl
  have hr : repairedRollout budgetTape favorableNextS23Before 9 [.query 3,.normalRetriever 4] = [.query 3,.normalRetriever 4,.selection 0,.width 0,.stop,.reranker 0,.topm 0,.context 0,.answer 0] := by decide
  simp only [nativeEvent,hs,hr]
  rfl

def favorableNextS24Before := favorableNextProposal.take 23

theorem favorableNextS24D0I0 : indexScore (7/5) (controlPenalty savedCref uniformQuoteError unitRoleUnused .next) favorableNextS24Before [] (.query 0) = treeIndex ((0/1)/3) (7/5) (nextNormalPenalty favorableNextS24Before) 23 3 := by
  have hs : replayBackup favorableNextS24Before emptyStatistics ([]++[.query 0]) = ⟨3,(0/1)⟩ := by
    rw [replayBackup_empty_closed_form]
    simp +decide [backedEvents,favorableNextS24Before,favorableNextProposal,favorableNextEvent1,favorableNextEvent2,favorableNextEvent3,favorableNextEvent4,favorableNextEvent5,favorableNextEvent6,favorableNextEvent7,favorableNextEvent8,favorableNextEvent9,favorableNextEvent10,favorableNextEvent11,favorableNextEvent12,favorableNextEvent13,favorableNextEvent14,favorableNextEvent15,favorableNextEvent16,favorableNextEvent17,favorableNextEvent18,favorableNextEvent19,favorableNextEvent20,favorableNextEvent21,favorableNextEvent22,favorableNextEvent23,taskReward]
    <;> norm_num
  have hp : rawVisits favorableNextS24Before [] = 23 := by decide
  have hn : rawVisits favorableNextS24Before ([]++[.query 0]) = 3 := by decide
  have hz : (controlPenalty savedCref uniformQuoteError unitRoleUnused .next) favorableNextS24Before [] (.query 0) = (nextNormalPenalty favorableNextS24Before) := by
    simpa only [favorableNextS24Before,nextNormalPenalty] using AgentUCTNextExact.favorable_next_normal_root_quotes_exact 23 (by omega) 0 (by decide)
  unfold indexScore
  rw [hs,hp,hn,hz]
  simp only [BackupStat.mean]
  norm_num

theorem favorableNextS24D0I1 : indexScore (7/5) (controlPenalty savedCref uniformQuoteError unitRoleUnused .next) favorableNextS24Before [] (.query 1) = treeIndex ((1/2)/4) (7/5) 0 23 4 := by
  have hs : replayBackup favorableNextS24Before emptyStatistics ([]++[.query 1]) = ⟨4,(1/2)⟩ := by
    rw [replayBackup_empty_closed_form]
    simp +decide [backedEvents,favorableNextS24Before,favorableNextProposal,favorableNextEvent1,favorableNextEvent2,favorableNextEvent3,favorableNextEvent4,favorableNextEvent5,favorableNextEvent6,favorableNextEvent7,favorableNextEvent8,favorableNextEvent9,favorableNextEvent10,favorableNextEvent11,favorableNextEvent12,favorableNextEvent13,favorableNextEvent14,favorableNextEvent15,favorableNextEvent16,favorableNextEvent17,favorableNextEvent18,favorableNextEvent19,favorableNextEvent20,favorableNextEvent21,favorableNextEvent22,favorableNextEvent23,taskReward]
    <;> norm_num
  have hp : rawVisits favorableNextS24Before [] = 23 := by decide
  have hn : rawVisits favorableNextS24Before ([]++[.query 1]) = 4 := by decide
  have hz : (controlPenalty savedCref uniformQuoteError unitRoleUnused .next) favorableNextS24Before [] (.query 1) = 0 := by
    apply control_penalty_empty_suffix
    decide
  unfold indexScore
  rw [hs,hp,hn,hz]
  simp only [BackupStat.mean]
  norm_num

theorem favorableNextS24D0I2 : indexScore (7/5) (controlPenalty savedCref uniformQuoteError unitRoleUnused .next) favorableNextS24Before [] (.query 2) = treeIndex ((0/1)/3) (7/5) (nextNormalPenalty favorableNextS24Before) 23 3 := by
  have hs : replayBackup favorableNextS24Before emptyStatistics ([]++[.query 2]) = ⟨3,(0/1)⟩ := by
    rw [replayBackup_empty_closed_form]
    simp +decide [backedEvents,favorableNextS24Before,favorableNextProposal,favorableNextEvent1,favorableNextEvent2,favorableNextEvent3,favorableNextEvent4,favorableNextEvent5,favorableNextEvent6,favorableNextEvent7,favorableNextEvent8,favorableNextEvent9,favorableNextEvent10,favorableNextEvent11,favorableNextEvent12,favorableNextEvent13,favorableNextEvent14,favorableNextEvent15,favorableNextEvent16,favorableNextEvent17,favorableNextEvent18,favorableNextEvent19,favorableNextEvent20,favorableNextEvent21,favorableNextEvent22,favorableNextEvent23,taskReward]
    <;> norm_num
  have hp : rawVisits favorableNextS24Before [] = 23 := by decide
  have hn : rawVisits favorableNextS24Before ([]++[.query 2]) = 3 := by decide
  have hz : (controlPenalty savedCref uniformQuoteError unitRoleUnused .next) favorableNextS24Before [] (.query 2) = (nextNormalPenalty favorableNextS24Before) := by
    simpa only [favorableNextS24Before,nextNormalPenalty] using AgentUCTNextExact.favorable_next_normal_root_quotes_exact 23 (by omega) 2 (by decide)
  unfold indexScore
  rw [hs,hp,hn,hz]
  simp only [BackupStat.mean]
  norm_num

theorem favorableNextS24D0I3 : indexScore (7/5) (controlPenalty savedCref uniformQuoteError unitRoleUnused .next) favorableNextS24Before [] (.query 3) = treeIndex ((0/1)/3) (7/5) (nextNormalPenalty favorableNextS24Before) 23 3 := by
  have hs : replayBackup favorableNextS24Before emptyStatistics ([]++[.query 3]) = ⟨3,(0/1)⟩ := by
    rw [replayBackup_empty_closed_form]
    simp +decide [backedEvents,favorableNextS24Before,favorableNextProposal,favorableNextEvent1,favorableNextEvent2,favorableNextEvent3,favorableNextEvent4,favorableNextEvent5,favorableNextEvent6,favorableNextEvent7,favorableNextEvent8,favorableNextEvent9,favorableNextEvent10,favorableNextEvent11,favorableNextEvent12,favorableNextEvent13,favorableNextEvent14,favorableNextEvent15,favorableNextEvent16,favorableNextEvent17,favorableNextEvent18,favorableNextEvent19,favorableNextEvent20,favorableNextEvent21,favorableNextEvent22,favorableNextEvent23,taskReward]
    <;> norm_num
  have hp : rawVisits favorableNextS24Before [] = 23 := by decide
  have hn : rawVisits favorableNextS24Before ([]++[.query 3]) = 3 := by decide
  have hz : (controlPenalty savedCref uniformQuoteError unitRoleUnused .next) favorableNextS24Before [] (.query 3) = (nextNormalPenalty favorableNextS24Before) := by
    simpa only [favorableNextS24Before,nextNormalPenalty] using AgentUCTNextExact.favorable_next_normal_root_quotes_exact 23 (by omega) 3 (by decide)
  unfold indexScore
  rw [hs,hp,hn,hz]
  simp only [BackupStat.mean]
  norm_num

theorem favorableNextS24D0I4 : indexScore (7/5) (controlPenalty savedCref uniformQuoteError unitRoleUnused .next) favorableNextS24Before [] (.query 4) = treeIndex ((0/1)/2) (7/5) (nextNormalPenalty favorableNextS24Before) 23 2 := by
  have hs : replayBackup favorableNextS24Before emptyStatistics ([]++[.query 4]) = ⟨2,(0/1)⟩ := by
    rw [replayBackup_empty_closed_form]
    simp +decide [backedEvents,favorableNextS24Before,favorableNextProposal,favorableNextEvent1,favorableNextEvent2,favorableNextEvent3,favorableNextEvent4,favorableNextEvent5,favorableNextEvent6,favorableNextEvent7,favorableNextEvent8,favorableNextEvent9,favorableNextEvent10,favorableNextEvent11,favorableNextEvent12,favorableNextEvent13,favorableNextEvent14,favorableNextEvent15,favorableNextEvent16,favorableNextEvent17,favorableNextEvent18,favorableNextEvent19,favorableNextEvent20,favorableNextEvent21,favorableNextEvent22,favorableNextEvent23,taskReward]
    <;> norm_num
  have hp : rawVisits favorableNextS24Before [] = 23 := by decide
  have hn : rawVisits favorableNextS24Before ([]++[.query 4]) = 2 := by decide
  have hz : (controlPenalty savedCref uniformQuoteError unitRoleUnused .next) favorableNextS24Before [] (.query 4) = (nextNormalPenalty favorableNextS24Before) := by
    simpa only [favorableNextS24Before,nextNormalPenalty] using AgentUCTNextExact.favorable_next_normal_root_quotes_exact 23 (by omega) 4 (by decide)
  unfold indexScore
  rw [hs,hp,hn,hz]
  simp only [BackupStat.mean]
  norm_num

theorem favorableNextS24D0I5 : indexScore (7/5) (controlPenalty savedCref uniformQuoteError unitRoleUnused .next) favorableNextS24Before [] (.query 5) = treeIndex ((6/5)/4) (7/5) (nextNormalPenalty favorableNextS24Before) 23 4 := by
  have hs : replayBackup favorableNextS24Before emptyStatistics ([]++[.query 5]) = ⟨4,(6/5)⟩ := by
    rw [replayBackup_empty_closed_form]
    simp +decide [backedEvents,favorableNextS24Before,favorableNextProposal,favorableNextEvent1,favorableNextEvent2,favorableNextEvent3,favorableNextEvent4,favorableNextEvent5,favorableNextEvent6,favorableNextEvent7,favorableNextEvent8,favorableNextEvent9,favorableNextEvent10,favorableNextEvent11,favorableNextEvent12,favorableNextEvent13,favorableNextEvent14,favorableNextEvent15,favorableNextEvent16,favorableNextEvent17,favorableNextEvent18,favorableNextEvent19,favorableNextEvent20,favorableNextEvent21,favorableNextEvent22,favorableNextEvent23,taskReward]
    <;> norm_num
  have hp : rawVisits favorableNextS24Before [] = 23 := by decide
  have hn : rawVisits favorableNextS24Before ([]++[.query 5]) = 4 := by decide
  have hz : (controlPenalty savedCref uniformQuoteError unitRoleUnused .next) favorableNextS24Before [] (.query 5) = (nextNormalPenalty favorableNextS24Before) := by
    simpa only [favorableNextS24Before,nextNormalPenalty] using AgentUCTNextExact.favorable_next_normal_root_quotes_exact 23 (by omega) 5 (by decide)
  unfold indexScore
  rw [hs,hp,hn,hz]
  simp only [BackupStat.mean]
  norm_num

theorem favorableNextS24D0I6 : indexScore (7/5) (controlPenalty savedCref uniformQuoteError unitRoleUnused .next) favorableNextS24Before [] (.query 6) = treeIndex ((0/1)/2) (7/5) (nextNormalPenalty favorableNextS24Before) 23 2 := by
  have hs : replayBackup favorableNextS24Before emptyStatistics ([]++[.query 6]) = ⟨2,(0/1)⟩ := by
    rw [replayBackup_empty_closed_form]
    simp +decide [backedEvents,favorableNextS24Before,favorableNextProposal,favorableNextEvent1,favorableNextEvent2,favorableNextEvent3,favorableNextEvent4,favorableNextEvent5,favorableNextEvent6,favorableNextEvent7,favorableNextEvent8,favorableNextEvent9,favorableNextEvent10,favorableNextEvent11,favorableNextEvent12,favorableNextEvent13,favorableNextEvent14,favorableNextEvent15,favorableNextEvent16,favorableNextEvent17,favorableNextEvent18,favorableNextEvent19,favorableNextEvent20,favorableNextEvent21,favorableNextEvent22,favorableNextEvent23,taskReward]
    <;> norm_num
  have hp : rawVisits favorableNextS24Before [] = 23 := by decide
  have hn : rawVisits favorableNextS24Before ([]++[.query 6]) = 2 := by decide
  have hz : (controlPenalty savedCref uniformQuoteError unitRoleUnused .next) favorableNextS24Before [] (.query 6) = (nextNormalPenalty favorableNextS24Before) := by
    simpa only [favorableNextS24Before,nextNormalPenalty] using AgentUCTNextExact.favorable_next_normal_root_quotes_exact 23 (by omega) 6 (by decide)
  unfold indexScore
  rw [hs,hp,hn,hz]
  simp only [BackupStat.mean]
  norm_num

theorem favorableNextS24D0I7 : indexScore (7/5) (controlPenalty savedCref uniformQuoteError unitRoleUnused .next) favorableNextS24Before [] (.query 7) = treeIndex ((0/1)/2) (7/5) (nextNormalPenalty favorableNextS24Before) 23 2 := by
  have hs : replayBackup favorableNextS24Before emptyStatistics ([]++[.query 7]) = ⟨2,(0/1)⟩ := by
    rw [replayBackup_empty_closed_form]
    simp +decide [backedEvents,favorableNextS24Before,favorableNextProposal,favorableNextEvent1,favorableNextEvent2,favorableNextEvent3,favorableNextEvent4,favorableNextEvent5,favorableNextEvent6,favorableNextEvent7,favorableNextEvent8,favorableNextEvent9,favorableNextEvent10,favorableNextEvent11,favorableNextEvent12,favorableNextEvent13,favorableNextEvent14,favorableNextEvent15,favorableNextEvent16,favorableNextEvent17,favorableNextEvent18,favorableNextEvent19,favorableNextEvent20,favorableNextEvent21,favorableNextEvent22,favorableNextEvent23,taskReward]
    <;> norm_num
  have hp : rawVisits favorableNextS24Before [] = 23 := by decide
  have hn : rawVisits favorableNextS24Before ([]++[.query 7]) = 2 := by decide
  have hz : (controlPenalty savedCref uniformQuoteError unitRoleUnused .next) favorableNextS24Before [] (.query 7) = (nextNormalPenalty favorableNextS24Before) := by
    simpa only [favorableNextS24Before,nextNormalPenalty] using AgentUCTNextExact.favorable_next_normal_root_quotes_exact 23 (by omega) 7 (by decide)
  unfold indexScore
  rw [hs,hp,hn,hz]
  simp only [BackupStat.mean]
  norm_num

theorem favorableNextS24D0Cmp0 : indexScore (7/5) (controlPenalty savedCref uniformQuoteError unitRoleUnused .next) favorableNextS24Before [] (.query 0) < indexScore (7/5) (controlPenalty savedCref uniformQuoteError unitRoleUnused .next) favorableNextS24Before [] (.query 4) := by
  rw [favorableNextS24D0I0,favorableNextS24D0I4]
  have hk := favorable_next_penalty_interval 23 (by omega)
  change nextNormalPenaltyLower ≤ nextNormalPenalty favorableNextS24Before ∧ nextNormalPenalty favorableNextS24Before ≤ nextNormalPenaltyUpper at hk
  have hm : ((0/1)/3)+(112574/78125)-(nextNormalPenalty favorableNextS24Before) < ((0/1)/2)+(88239627/50000000)-(nextNormalPenalty favorableNextS24Before) := by
    have h : (((0/1)/3)+(112574/78125) : ℝ) < ((0/1)/2)+(88239627/50000000) := by norm_num
    linarith
  have h := index_strict_order_from_intervals ((0/1)/2) ((0/1)/3) (nextNormalPenalty favorableNextS24Before) (nextNormalPenalty favorableNextS24Before) (88239627/50000000) (112574/78125)
    (treeBonus (7/5) 23 2) (treeBonus (7/5) 23 3)
    (trajectory_bonus_23_2).1 (trajectory_bonus_23_3).2 hm
  simpa only [treeIndex] using h

theorem favorableNextS24D0Cmp1 : indexScore (7/5) (controlPenalty savedCref uniformQuoteError unitRoleUnused .next) favorableNextS24Before [] (.query 1) < indexScore (7/5) (controlPenalty savedCref uniformQuoteError unitRoleUnused .next) favorableNextS24Before [] (.query 4) := by
  rw [favorableNextS24D0I1,favorableNextS24D0I4]
  have hk := favorable_next_penalty_interval 23 (by omega)
  change nextNormalPenaltyLower ≤ nextNormalPenalty favorableNextS24Before ∧ nextNormalPenalty favorableNextS24Before ≤ nextNormalPenaltyUpper at hk
  have hm : ((1/2)/4)+(62394843/50000000)-0 < ((0/1)/2)+(88239627/50000000)-(nextNormalPenalty favorableNextS24Before) := by
    have h : ((1/2)/4)+(62394843/50000000) < ((0/1)/2)+(88239627/50000000)-nextNormalPenaltyUpper := by norm_num [nextNormalPenaltyUpper,savedCref,uniformQuoteError]
    linarith [hk.2]
  have h := index_strict_order_from_intervals ((0/1)/2) ((1/2)/4) (nextNormalPenalty favorableNextS24Before) 0 (88239627/50000000) (62394843/50000000)
    (treeBonus (7/5) 23 2) (treeBonus (7/5) 23 4)
    (trajectory_bonus_23_2).1 (trajectory_bonus_23_4).2 hm
  simpa only [treeIndex] using h

theorem favorableNextS24D0Cmp2 : indexScore (7/5) (controlPenalty savedCref uniformQuoteError unitRoleUnused .next) favorableNextS24Before [] (.query 2) < indexScore (7/5) (controlPenalty savedCref uniformQuoteError unitRoleUnused .next) favorableNextS24Before [] (.query 4) := by
  rw [favorableNextS24D0I2,favorableNextS24D0I4]
  have hk := favorable_next_penalty_interval 23 (by omega)
  change nextNormalPenaltyLower ≤ nextNormalPenalty favorableNextS24Before ∧ nextNormalPenalty favorableNextS24Before ≤ nextNormalPenaltyUpper at hk
  have hm : ((0/1)/3)+(112574/78125)-(nextNormalPenalty favorableNextS24Before) < ((0/1)/2)+(88239627/50000000)-(nextNormalPenalty favorableNextS24Before) := by
    have h : (((0/1)/3)+(112574/78125) : ℝ) < ((0/1)/2)+(88239627/50000000) := by norm_num
    linarith
  have h := index_strict_order_from_intervals ((0/1)/2) ((0/1)/3) (nextNormalPenalty favorableNextS24Before) (nextNormalPenalty favorableNextS24Before) (88239627/50000000) (112574/78125)
    (treeBonus (7/5) 23 2) (treeBonus (7/5) 23 3)
    (trajectory_bonus_23_2).1 (trajectory_bonus_23_3).2 hm
  simpa only [treeIndex] using h

theorem favorableNextS24D0Cmp3 : indexScore (7/5) (controlPenalty savedCref uniformQuoteError unitRoleUnused .next) favorableNextS24Before [] (.query 3) < indexScore (7/5) (controlPenalty savedCref uniformQuoteError unitRoleUnused .next) favorableNextS24Before [] (.query 4) := by
  rw [favorableNextS24D0I3,favorableNextS24D0I4]
  have hk := favorable_next_penalty_interval 23 (by omega)
  change nextNormalPenaltyLower ≤ nextNormalPenalty favorableNextS24Before ∧ nextNormalPenalty favorableNextS24Before ≤ nextNormalPenaltyUpper at hk
  have hm : ((0/1)/3)+(112574/78125)-(nextNormalPenalty favorableNextS24Before) < ((0/1)/2)+(88239627/50000000)-(nextNormalPenalty favorableNextS24Before) := by
    have h : (((0/1)/3)+(112574/78125) : ℝ) < ((0/1)/2)+(88239627/50000000) := by norm_num
    linarith
  have h := index_strict_order_from_intervals ((0/1)/2) ((0/1)/3) (nextNormalPenalty favorableNextS24Before) (nextNormalPenalty favorableNextS24Before) (88239627/50000000) (112574/78125)
    (treeBonus (7/5) 23 2) (treeBonus (7/5) 23 3)
    (trajectory_bonus_23_2).1 (trajectory_bonus_23_3).2 hm
  simpa only [treeIndex] using h

theorem favorableNextS24D0Cmp5 : indexScore (7/5) (controlPenalty savedCref uniformQuoteError unitRoleUnused .next) favorableNextS24Before [] (.query 5) ≤ indexScore (7/5) (controlPenalty savedCref uniformQuoteError unitRoleUnused .next) favorableNextS24Before [] (.query 4) := by
  rw [favorableNextS24D0I5,favorableNextS24D0I4]
  have hk := favorable_next_penalty_interval 23 (by omega)
  change nextNormalPenaltyLower ≤ nextNormalPenalty favorableNextS24Before ∧ nextNormalPenalty favorableNextS24Before ≤ nextNormalPenaltyUpper at hk
  have hm : ((6/5)/4)+(62394843/50000000)-(nextNormalPenalty favorableNextS24Before) < ((0/1)/2)+(88239627/50000000)-(nextNormalPenalty favorableNextS24Before) := by
    have h : (((6/5)/4)+(62394843/50000000) : ℝ) < ((0/1)/2)+(88239627/50000000) := by norm_num
    linarith
  have h := index_weak_order_from_intervals ((0/1)/2) ((6/5)/4) (nextNormalPenalty favorableNextS24Before) (nextNormalPenalty favorableNextS24Before) (88239627/50000000) (62394843/50000000)
    (treeBonus (7/5) 23 2) (treeBonus (7/5) 23 4)
    (trajectory_bonus_23_2).1 (trajectory_bonus_23_4).2 hm.le
  simpa only [treeIndex] using h

theorem favorableNextS24D0Cmp6 : indexScore (7/5) (controlPenalty savedCref uniformQuoteError unitRoleUnused .next) favorableNextS24Before [] (.query 6) ≤ indexScore (7/5) (controlPenalty savedCref uniformQuoteError unitRoleUnused .next) favorableNextS24Before [] (.query 4) := by
  rw [favorableNextS24D0I6,favorableNextS24D0I4]

theorem favorableNextS24D0Cmp7 : indexScore (7/5) (controlPenalty savedCref uniformQuoteError unitRoleUnused .next) favorableNextS24Before [] (.query 7) ≤ indexScore (7/5) (controlPenalty savedCref uniformQuoteError unitRoleUnused .next) favorableNextS24Before [] (.query 4) := by
  rw [favorableNextS24D0I7,favorableNextS24D0I4]

theorem favorableNextS24Choice0 : nativeFirstChoice (indexScore (7/5) (controlPenalty savedCref uniformQuoteError unitRoleUnused .next) favorableNextS24Before []) favorableNextS24Before [] = .query 4 := by
  apply visited_choice_from_ordered_certificate _ _ [] [.query 0,.query 1,.query 2,.query 3] [.query 5,.query 6,.query 7] (.query 4) (by decide)
  · intro a ha
    have ho : orderedLegalAvailable [] = [.query 0,.query 1,.query 2,.query 3,.query 4,.query 5,.query 6,.query 7] := by decide
    rw [ho] at ha
    simp only [List.mem_cons,List.not_mem_nil,or_false] at ha
    rcases ha with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> decide
  · intro a ha
    simp only [List.mem_cons,List.not_mem_nil,or_false] at ha
    rcases ha with rfl | rfl | rfl | rfl
    · exact favorableNextS24D0Cmp0
    · exact favorableNextS24D0Cmp1
    · exact favorableNextS24D0Cmp2
    · exact favorableNextS24D0Cmp3
  · intro a ha
    simp only [List.mem_cons,List.not_mem_nil,or_false] at ha
    rcases ha with rfl | rfl | rfl
    · exact favorableNextS24D0Cmp5
    · exact favorableNextS24D0Cmp6
    · exact favorableNextS24D0Cmp7

theorem favorableNextS24ActualEvent : nativeEvent budgetTape (7/5) (controlPenalty savedCref uniformQuoteError unitRoleUnused .next)
    (taskReward false (2/5) (1/2)) favorableNextS24Before = favorableNextEvent24 := by
  have hs0 := native_select_existing_step budgetTape (7/5) (controlPenalty savedCref uniformQuoteError unitRoleUnused .next) favorableNextS24Before 8 [] (.query 4)
    (by decide) (by decide) favorableNextS24Choice0
  have hnew := native_select_new_step budgetTape (7/5) (controlPenalty savedCref uniformQuoteError unitRoleUnused .next) favorableNextS24Before 7 [.query 4]
    [.normalRetriever 4,.normalRetriever 6,.normalRetriever 7,.normalRetriever 8,.normalRetriever 5,.normalRetriever 1,.normalRetriever 2,.normalRetriever 3,.normalRetriever 12,.normalRetriever 14,.normalRetriever 13,.normalRetriever 21,.normalRetriever 23,.normalRetriever 22,.normalRetriever 9,.normalRetriever 11,.normalRetriever 10,.normalRetriever 15,.normalRetriever 17,.normalRetriever 16,.normalRetriever 18,.normalRetriever 20,.normalRetriever 19,.normalRetriever 24,.normalRetriever 25,.normalRetriever 26,.normalRetriever 27,.normalRetriever 28,.normalRetriever 29] (.normalRetriever 4) (by decide) (by decide) (by decide) (by decide)
  have hs : nativeSelect budgetTape (7/5) (controlPenalty savedCref uniformQuoteError unitRoleUnused .next) favorableNextS24Before 9 [] = [.query 4,.normalRetriever 4] := by
    rw [hs0]
    change nativeSelect budgetTape (7/5) (controlPenalty savedCref uniformQuoteError unitRoleUnused .next) favorableNextS24Before 8 [.query 4] = _
    rw [hnew] <;> rfl
  have hr : repairedRollout budgetTape favorableNextS24Before 9 [.query 4,.normalRetriever 4] = [.query 4,.normalRetriever 4,.selection 0,.width 0,.stop,.reranker 0,.topm 0,.context 0,.answer 0] := by decide
  simp only [nativeEvent,hs,hr]
  rfl

def favorableNextS25Before := favorableNextProposal.take 24

theorem favorableNextS25D0I0 : indexScore (7/5) (controlPenalty savedCref uniformQuoteError unitRoleUnused .next) favorableNextS25Before [] (.query 0) = treeIndex ((0/1)/3) (7/5) (nextNormalPenalty favorableNextS25Before) 24 3 := by
  have hs : replayBackup favorableNextS25Before emptyStatistics ([]++[.query 0]) = ⟨3,(0/1)⟩ := by
    rw [replayBackup_empty_closed_form]
    simp +decide [backedEvents,favorableNextS25Before,favorableNextProposal,favorableNextEvent1,favorableNextEvent2,favorableNextEvent3,favorableNextEvent4,favorableNextEvent5,favorableNextEvent6,favorableNextEvent7,favorableNextEvent8,favorableNextEvent9,favorableNextEvent10,favorableNextEvent11,favorableNextEvent12,favorableNextEvent13,favorableNextEvent14,favorableNextEvent15,favorableNextEvent16,favorableNextEvent17,favorableNextEvent18,favorableNextEvent19,favorableNextEvent20,favorableNextEvent21,favorableNextEvent22,favorableNextEvent23,favorableNextEvent24,taskReward]
    <;> norm_num
  have hp : rawVisits favorableNextS25Before [] = 24 := by decide
  have hn : rawVisits favorableNextS25Before ([]++[.query 0]) = 3 := by decide
  have hz : (controlPenalty savedCref uniformQuoteError unitRoleUnused .next) favorableNextS25Before [] (.query 0) = (nextNormalPenalty favorableNextS25Before) := by
    simpa only [favorableNextS25Before,nextNormalPenalty] using AgentUCTNextExact.favorable_next_normal_root_quotes_exact 24 (by omega) 0 (by decide)
  unfold indexScore
  rw [hs,hp,hn,hz]
  simp only [BackupStat.mean]
  norm_num

theorem favorableNextS25D0I1 : indexScore (7/5) (controlPenalty savedCref uniformQuoteError unitRoleUnused .next) favorableNextS25Before [] (.query 1) = treeIndex ((1/2)/4) (7/5) 0 24 4 := by
  have hs : replayBackup favorableNextS25Before emptyStatistics ([]++[.query 1]) = ⟨4,(1/2)⟩ := by
    rw [replayBackup_empty_closed_form]
    simp +decide [backedEvents,favorableNextS25Before,favorableNextProposal,favorableNextEvent1,favorableNextEvent2,favorableNextEvent3,favorableNextEvent4,favorableNextEvent5,favorableNextEvent6,favorableNextEvent7,favorableNextEvent8,favorableNextEvent9,favorableNextEvent10,favorableNextEvent11,favorableNextEvent12,favorableNextEvent13,favorableNextEvent14,favorableNextEvent15,favorableNextEvent16,favorableNextEvent17,favorableNextEvent18,favorableNextEvent19,favorableNextEvent20,favorableNextEvent21,favorableNextEvent22,favorableNextEvent23,favorableNextEvent24,taskReward]
    <;> norm_num
  have hp : rawVisits favorableNextS25Before [] = 24 := by decide
  have hn : rawVisits favorableNextS25Before ([]++[.query 1]) = 4 := by decide
  have hz : (controlPenalty savedCref uniformQuoteError unitRoleUnused .next) favorableNextS25Before [] (.query 1) = 0 := by
    apply control_penalty_empty_suffix
    decide
  unfold indexScore
  rw [hs,hp,hn,hz]
  simp only [BackupStat.mean]
  norm_num

theorem favorableNextS25D0I2 : indexScore (7/5) (controlPenalty savedCref uniformQuoteError unitRoleUnused .next) favorableNextS25Before [] (.query 2) = treeIndex ((0/1)/3) (7/5) (nextNormalPenalty favorableNextS25Before) 24 3 := by
  have hs : replayBackup favorableNextS25Before emptyStatistics ([]++[.query 2]) = ⟨3,(0/1)⟩ := by
    rw [replayBackup_empty_closed_form]
    simp +decide [backedEvents,favorableNextS25Before,favorableNextProposal,favorableNextEvent1,favorableNextEvent2,favorableNextEvent3,favorableNextEvent4,favorableNextEvent5,favorableNextEvent6,favorableNextEvent7,favorableNextEvent8,favorableNextEvent9,favorableNextEvent10,favorableNextEvent11,favorableNextEvent12,favorableNextEvent13,favorableNextEvent14,favorableNextEvent15,favorableNextEvent16,favorableNextEvent17,favorableNextEvent18,favorableNextEvent19,favorableNextEvent20,favorableNextEvent21,favorableNextEvent22,favorableNextEvent23,favorableNextEvent24,taskReward]
    <;> norm_num
  have hp : rawVisits favorableNextS25Before [] = 24 := by decide
  have hn : rawVisits favorableNextS25Before ([]++[.query 2]) = 3 := by decide
  have hz : (controlPenalty savedCref uniformQuoteError unitRoleUnused .next) favorableNextS25Before [] (.query 2) = (nextNormalPenalty favorableNextS25Before) := by
    simpa only [favorableNextS25Before,nextNormalPenalty] using AgentUCTNextExact.favorable_next_normal_root_quotes_exact 24 (by omega) 2 (by decide)
  unfold indexScore
  rw [hs,hp,hn,hz]
  simp only [BackupStat.mean]
  norm_num

theorem favorableNextS25D0I3 : indexScore (7/5) (controlPenalty savedCref uniformQuoteError unitRoleUnused .next) favorableNextS25Before [] (.query 3) = treeIndex ((0/1)/3) (7/5) (nextNormalPenalty favorableNextS25Before) 24 3 := by
  have hs : replayBackup favorableNextS25Before emptyStatistics ([]++[.query 3]) = ⟨3,(0/1)⟩ := by
    rw [replayBackup_empty_closed_form]
    simp +decide [backedEvents,favorableNextS25Before,favorableNextProposal,favorableNextEvent1,favorableNextEvent2,favorableNextEvent3,favorableNextEvent4,favorableNextEvent5,favorableNextEvent6,favorableNextEvent7,favorableNextEvent8,favorableNextEvent9,favorableNextEvent10,favorableNextEvent11,favorableNextEvent12,favorableNextEvent13,favorableNextEvent14,favorableNextEvent15,favorableNextEvent16,favorableNextEvent17,favorableNextEvent18,favorableNextEvent19,favorableNextEvent20,favorableNextEvent21,favorableNextEvent22,favorableNextEvent23,favorableNextEvent24,taskReward]
    <;> norm_num
  have hp : rawVisits favorableNextS25Before [] = 24 := by decide
  have hn : rawVisits favorableNextS25Before ([]++[.query 3]) = 3 := by decide
  have hz : (controlPenalty savedCref uniformQuoteError unitRoleUnused .next) favorableNextS25Before [] (.query 3) = (nextNormalPenalty favorableNextS25Before) := by
    simpa only [favorableNextS25Before,nextNormalPenalty] using AgentUCTNextExact.favorable_next_normal_root_quotes_exact 24 (by omega) 3 (by decide)
  unfold indexScore
  rw [hs,hp,hn,hz]
  simp only [BackupStat.mean]
  norm_num

theorem favorableNextS25D0I4 : indexScore (7/5) (controlPenalty savedCref uniformQuoteError unitRoleUnused .next) favorableNextS25Before [] (.query 4) = treeIndex ((0/1)/3) (7/5) (nextNormalPenalty favorableNextS25Before) 24 3 := by
  have hs : replayBackup favorableNextS25Before emptyStatistics ([]++[.query 4]) = ⟨3,(0/1)⟩ := by
    rw [replayBackup_empty_closed_form]
    simp +decide [backedEvents,favorableNextS25Before,favorableNextProposal,favorableNextEvent1,favorableNextEvent2,favorableNextEvent3,favorableNextEvent4,favorableNextEvent5,favorableNextEvent6,favorableNextEvent7,favorableNextEvent8,favorableNextEvent9,favorableNextEvent10,favorableNextEvent11,favorableNextEvent12,favorableNextEvent13,favorableNextEvent14,favorableNextEvent15,favorableNextEvent16,favorableNextEvent17,favorableNextEvent18,favorableNextEvent19,favorableNextEvent20,favorableNextEvent21,favorableNextEvent22,favorableNextEvent23,favorableNextEvent24,taskReward]
    <;> norm_num
  have hp : rawVisits favorableNextS25Before [] = 24 := by decide
  have hn : rawVisits favorableNextS25Before ([]++[.query 4]) = 3 := by decide
  have hz : (controlPenalty savedCref uniformQuoteError unitRoleUnused .next) favorableNextS25Before [] (.query 4) = (nextNormalPenalty favorableNextS25Before) := by
    simpa only [favorableNextS25Before,nextNormalPenalty] using AgentUCTNextExact.favorable_next_normal_root_quotes_exact 24 (by omega) 4 (by decide)
  unfold indexScore
  rw [hs,hp,hn,hz]
  simp only [BackupStat.mean]
  norm_num

theorem favorableNextS25D0I5 : indexScore (7/5) (controlPenalty savedCref uniformQuoteError unitRoleUnused .next) favorableNextS25Before [] (.query 5) = treeIndex ((6/5)/4) (7/5) (nextNormalPenalty favorableNextS25Before) 24 4 := by
  have hs : replayBackup favorableNextS25Before emptyStatistics ([]++[.query 5]) = ⟨4,(6/5)⟩ := by
    rw [replayBackup_empty_closed_form]
    simp +decide [backedEvents,favorableNextS25Before,favorableNextProposal,favorableNextEvent1,favorableNextEvent2,favorableNextEvent3,favorableNextEvent4,favorableNextEvent5,favorableNextEvent6,favorableNextEvent7,favorableNextEvent8,favorableNextEvent9,favorableNextEvent10,favorableNextEvent11,favorableNextEvent12,favorableNextEvent13,favorableNextEvent14,favorableNextEvent15,favorableNextEvent16,favorableNextEvent17,favorableNextEvent18,favorableNextEvent19,favorableNextEvent20,favorableNextEvent21,favorableNextEvent22,favorableNextEvent23,favorableNextEvent24,taskReward]
    <;> norm_num
  have hp : rawVisits favorableNextS25Before [] = 24 := by decide
  have hn : rawVisits favorableNextS25Before ([]++[.query 5]) = 4 := by decide
  have hz : (controlPenalty savedCref uniformQuoteError unitRoleUnused .next) favorableNextS25Before [] (.query 5) = (nextNormalPenalty favorableNextS25Before) := by
    simpa only [favorableNextS25Before,nextNormalPenalty] using AgentUCTNextExact.favorable_next_normal_root_quotes_exact 24 (by omega) 5 (by decide)
  unfold indexScore
  rw [hs,hp,hn,hz]
  simp only [BackupStat.mean]
  norm_num

theorem favorableNextS25D0I6 : indexScore (7/5) (controlPenalty savedCref uniformQuoteError unitRoleUnused .next) favorableNextS25Before [] (.query 6) = treeIndex ((0/1)/2) (7/5) (nextNormalPenalty favorableNextS25Before) 24 2 := by
  have hs : replayBackup favorableNextS25Before emptyStatistics ([]++[.query 6]) = ⟨2,(0/1)⟩ := by
    rw [replayBackup_empty_closed_form]
    simp +decide [backedEvents,favorableNextS25Before,favorableNextProposal,favorableNextEvent1,favorableNextEvent2,favorableNextEvent3,favorableNextEvent4,favorableNextEvent5,favorableNextEvent6,favorableNextEvent7,favorableNextEvent8,favorableNextEvent9,favorableNextEvent10,favorableNextEvent11,favorableNextEvent12,favorableNextEvent13,favorableNextEvent14,favorableNextEvent15,favorableNextEvent16,favorableNextEvent17,favorableNextEvent18,favorableNextEvent19,favorableNextEvent20,favorableNextEvent21,favorableNextEvent22,favorableNextEvent23,favorableNextEvent24,taskReward]
    <;> norm_num
  have hp : rawVisits favorableNextS25Before [] = 24 := by decide
  have hn : rawVisits favorableNextS25Before ([]++[.query 6]) = 2 := by decide
  have hz : (controlPenalty savedCref uniformQuoteError unitRoleUnused .next) favorableNextS25Before [] (.query 6) = (nextNormalPenalty favorableNextS25Before) := by
    simpa only [favorableNextS25Before,nextNormalPenalty] using AgentUCTNextExact.favorable_next_normal_root_quotes_exact 24 (by omega) 6 (by decide)
  unfold indexScore
  rw [hs,hp,hn,hz]
  simp only [BackupStat.mean]
  norm_num

theorem favorableNextS25D0I7 : indexScore (7/5) (controlPenalty savedCref uniformQuoteError unitRoleUnused .next) favorableNextS25Before [] (.query 7) = treeIndex ((0/1)/2) (7/5) (nextNormalPenalty favorableNextS25Before) 24 2 := by
  have hs : replayBackup favorableNextS25Before emptyStatistics ([]++[.query 7]) = ⟨2,(0/1)⟩ := by
    rw [replayBackup_empty_closed_form]
    simp +decide [backedEvents,favorableNextS25Before,favorableNextProposal,favorableNextEvent1,favorableNextEvent2,favorableNextEvent3,favorableNextEvent4,favorableNextEvent5,favorableNextEvent6,favorableNextEvent7,favorableNextEvent8,favorableNextEvent9,favorableNextEvent10,favorableNextEvent11,favorableNextEvent12,favorableNextEvent13,favorableNextEvent14,favorableNextEvent15,favorableNextEvent16,favorableNextEvent17,favorableNextEvent18,favorableNextEvent19,favorableNextEvent20,favorableNextEvent21,favorableNextEvent22,favorableNextEvent23,favorableNextEvent24,taskReward]
    <;> norm_num
  have hp : rawVisits favorableNextS25Before [] = 24 := by decide
  have hn : rawVisits favorableNextS25Before ([]++[.query 7]) = 2 := by decide
  have hz : (controlPenalty savedCref uniformQuoteError unitRoleUnused .next) favorableNextS25Before [] (.query 7) = (nextNormalPenalty favorableNextS25Before) := by
    simpa only [favorableNextS25Before,nextNormalPenalty] using AgentUCTNextExact.favorable_next_normal_root_quotes_exact 24 (by omega) 7 (by decide)
  unfold indexScore
  rw [hs,hp,hn,hz]
  simp only [BackupStat.mean]
  norm_num

theorem favorableNextS25D0Cmp0 : indexScore (7/5) (controlPenalty savedCref uniformQuoteError unitRoleUnused .next) favorableNextS25Before [] (.query 0) < indexScore (7/5) (controlPenalty savedCref uniformQuoteError unitRoleUnused .next) favorableNextS25Before [] (.query 6) := by
  rw [favorableNextS25D0I0,favorableNextS25D0I6]
  have hk := favorable_next_penalty_interval 24 (by omega)
  change nextNormalPenaltyLower ≤ nextNormalPenalty favorableNextS25Before ∧ nextNormalPenalty favorableNextS25Before ≤ nextNormalPenaltyUpper at hk
  have hm : ((0/1)/3)+(18127151/12500000)-(nextNormalPenalty favorableNextS25Before) < ((0/1)/2)+(44402267/25000000)-(nextNormalPenalty favorableNextS25Before) := by
    have h : (((0/1)/3)+(18127151/12500000) : ℝ) < ((0/1)/2)+(44402267/25000000) := by norm_num
    linarith
  have h := index_strict_order_from_intervals ((0/1)/2) ((0/1)/3) (nextNormalPenalty favorableNextS25Before) (nextNormalPenalty favorableNextS25Before) (44402267/25000000) (18127151/12500000)
    (treeBonus (7/5) 24 2) (treeBonus (7/5) 24 3)
    (trajectory_bonus_24_2).1 (trajectory_bonus_24_3).2 hm
  simpa only [treeIndex] using h

theorem favorableNextS25D0Cmp1 : indexScore (7/5) (controlPenalty savedCref uniformQuoteError unitRoleUnused .next) favorableNextS25Before [] (.query 1) < indexScore (7/5) (controlPenalty savedCref uniformQuoteError unitRoleUnused .next) favorableNextS25Before [] (.query 6) := by
  rw [favorableNextS25D0I1,favorableNextS25D0I6]
  have hk := favorable_next_penalty_interval 24 (by omega)
  change nextNormalPenaltyLower ≤ nextNormalPenalty favorableNextS25Before ∧ nextNormalPenalty favorableNextS25Before ≤ nextNormalPenaltyUpper at hk
  have hm : ((1/2)/4)+(62794291/50000000)-0 < ((0/1)/2)+(44402267/25000000)-(nextNormalPenalty favorableNextS25Before) := by
    have h : ((1/2)/4)+(62794291/50000000) < ((0/1)/2)+(44402267/25000000)-nextNormalPenaltyUpper := by norm_num [nextNormalPenaltyUpper,savedCref,uniformQuoteError]
    linarith [hk.2]
  have h := index_strict_order_from_intervals ((0/1)/2) ((1/2)/4) (nextNormalPenalty favorableNextS25Before) 0 (44402267/25000000) (62794291/50000000)
    (treeBonus (7/5) 24 2) (treeBonus (7/5) 24 4)
    (trajectory_bonus_24_2).1 (trajectory_bonus_24_4).2 hm
  simpa only [treeIndex] using h

theorem favorableNextS25D0Cmp2 : indexScore (7/5) (controlPenalty savedCref uniformQuoteError unitRoleUnused .next) favorableNextS25Before [] (.query 2) < indexScore (7/5) (controlPenalty savedCref uniformQuoteError unitRoleUnused .next) favorableNextS25Before [] (.query 6) := by
  rw [favorableNextS25D0I2,favorableNextS25D0I6]
  have hk := favorable_next_penalty_interval 24 (by omega)
  change nextNormalPenaltyLower ≤ nextNormalPenalty favorableNextS25Before ∧ nextNormalPenalty favorableNextS25Before ≤ nextNormalPenaltyUpper at hk
  have hm : ((0/1)/3)+(18127151/12500000)-(nextNormalPenalty favorableNextS25Before) < ((0/1)/2)+(44402267/25000000)-(nextNormalPenalty favorableNextS25Before) := by
    have h : (((0/1)/3)+(18127151/12500000) : ℝ) < ((0/1)/2)+(44402267/25000000) := by norm_num
    linarith
  have h := index_strict_order_from_intervals ((0/1)/2) ((0/1)/3) (nextNormalPenalty favorableNextS25Before) (nextNormalPenalty favorableNextS25Before) (44402267/25000000) (18127151/12500000)
    (treeBonus (7/5) 24 2) (treeBonus (7/5) 24 3)
    (trajectory_bonus_24_2).1 (trajectory_bonus_24_3).2 hm
  simpa only [treeIndex] using h

theorem favorableNextS25D0Cmp3 : indexScore (7/5) (controlPenalty savedCref uniformQuoteError unitRoleUnused .next) favorableNextS25Before [] (.query 3) < indexScore (7/5) (controlPenalty savedCref uniformQuoteError unitRoleUnused .next) favorableNextS25Before [] (.query 6) := by
  rw [favorableNextS25D0I3,favorableNextS25D0I6]
  have hk := favorable_next_penalty_interval 24 (by omega)
  change nextNormalPenaltyLower ≤ nextNormalPenalty favorableNextS25Before ∧ nextNormalPenalty favorableNextS25Before ≤ nextNormalPenaltyUpper at hk
  have hm : ((0/1)/3)+(18127151/12500000)-(nextNormalPenalty favorableNextS25Before) < ((0/1)/2)+(44402267/25000000)-(nextNormalPenalty favorableNextS25Before) := by
    have h : (((0/1)/3)+(18127151/12500000) : ℝ) < ((0/1)/2)+(44402267/25000000) := by norm_num
    linarith
  have h := index_strict_order_from_intervals ((0/1)/2) ((0/1)/3) (nextNormalPenalty favorableNextS25Before) (nextNormalPenalty favorableNextS25Before) (44402267/25000000) (18127151/12500000)
    (treeBonus (7/5) 24 2) (treeBonus (7/5) 24 3)
    (trajectory_bonus_24_2).1 (trajectory_bonus_24_3).2 hm
  simpa only [treeIndex] using h

theorem favorableNextS25D0Cmp4 : indexScore (7/5) (controlPenalty savedCref uniformQuoteError unitRoleUnused .next) favorableNextS25Before [] (.query 4) < indexScore (7/5) (controlPenalty savedCref uniformQuoteError unitRoleUnused .next) favorableNextS25Before [] (.query 6) := by
  rw [favorableNextS25D0I4,favorableNextS25D0I6]
  have hk := favorable_next_penalty_interval 24 (by omega)
  change nextNormalPenaltyLower ≤ nextNormalPenalty favorableNextS25Before ∧ nextNormalPenalty favorableNextS25Before ≤ nextNormalPenaltyUpper at hk
  have hm : ((0/1)/3)+(18127151/12500000)-(nextNormalPenalty favorableNextS25Before) < ((0/1)/2)+(44402267/25000000)-(nextNormalPenalty favorableNextS25Before) := by
    have h : (((0/1)/3)+(18127151/12500000) : ℝ) < ((0/1)/2)+(44402267/25000000) := by norm_num
    linarith
  have h := index_strict_order_from_intervals ((0/1)/2) ((0/1)/3) (nextNormalPenalty favorableNextS25Before) (nextNormalPenalty favorableNextS25Before) (44402267/25000000) (18127151/12500000)
    (treeBonus (7/5) 24 2) (treeBonus (7/5) 24 3)
    (trajectory_bonus_24_2).1 (trajectory_bonus_24_3).2 hm
  simpa only [treeIndex] using h

theorem favorableNextS25D0Cmp5 : indexScore (7/5) (controlPenalty savedCref uniformQuoteError unitRoleUnused .next) favorableNextS25Before [] (.query 5) < indexScore (7/5) (controlPenalty savedCref uniformQuoteError unitRoleUnused .next) favorableNextS25Before [] (.query 6) := by
  rw [favorableNextS25D0I5,favorableNextS25D0I6]
  have hk := favorable_next_penalty_interval 24 (by omega)
  change nextNormalPenaltyLower ≤ nextNormalPenalty favorableNextS25Before ∧ nextNormalPenalty favorableNextS25Before ≤ nextNormalPenaltyUpper at hk
  have hm : ((6/5)/4)+(62794291/50000000)-(nextNormalPenalty favorableNextS25Before) < ((0/1)/2)+(44402267/25000000)-(nextNormalPenalty favorableNextS25Before) := by
    have h : (((6/5)/4)+(62794291/50000000) : ℝ) < ((0/1)/2)+(44402267/25000000) := by norm_num
    linarith
  have h := index_strict_order_from_intervals ((0/1)/2) ((6/5)/4) (nextNormalPenalty favorableNextS25Before) (nextNormalPenalty favorableNextS25Before) (44402267/25000000) (62794291/50000000)
    (treeBonus (7/5) 24 2) (treeBonus (7/5) 24 4)
    (trajectory_bonus_24_2).1 (trajectory_bonus_24_4).2 hm
  simpa only [treeIndex] using h

theorem favorableNextS25D0Cmp7 : indexScore (7/5) (controlPenalty savedCref uniformQuoteError unitRoleUnused .next) favorableNextS25Before [] (.query 7) ≤ indexScore (7/5) (controlPenalty savedCref uniformQuoteError unitRoleUnused .next) favorableNextS25Before [] (.query 6) := by
  rw [favorableNextS25D0I7,favorableNextS25D0I6]

theorem favorableNextS25Choice0 : nativeFirstChoice (indexScore (7/5) (controlPenalty savedCref uniformQuoteError unitRoleUnused .next) favorableNextS25Before []) favorableNextS25Before [] = .query 6 := by
  apply visited_choice_from_ordered_certificate _ _ [] [.query 0,.query 1,.query 2,.query 3,.query 4,.query 5] [.query 7] (.query 6) (by decide)
  · intro a ha
    have ho : orderedLegalAvailable [] = [.query 0,.query 1,.query 2,.query 3,.query 4,.query 5,.query 6,.query 7] := by decide
    rw [ho] at ha
    simp only [List.mem_cons,List.not_mem_nil,or_false] at ha
    rcases ha with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> decide
  · intro a ha
    simp only [List.mem_cons,List.not_mem_nil,or_false] at ha
    rcases ha with rfl | rfl | rfl | rfl | rfl | rfl
    · exact favorableNextS25D0Cmp0
    · exact favorableNextS25D0Cmp1
    · exact favorableNextS25D0Cmp2
    · exact favorableNextS25D0Cmp3
    · exact favorableNextS25D0Cmp4
    · exact favorableNextS25D0Cmp5
  · intro a ha
    simp only [List.mem_cons,List.not_mem_nil,or_false] at ha
    rcases ha with rfl
    · exact favorableNextS25D0Cmp7

theorem favorableNextS25ActualEvent : nativeEvent budgetTape (7/5) (controlPenalty savedCref uniformQuoteError unitRoleUnused .next)
    (taskReward false (2/5) (1/2)) favorableNextS25Before = favorableNextEvent25 := by
  have hs0 := native_select_existing_step budgetTape (7/5) (controlPenalty savedCref uniformQuoteError unitRoleUnused .next) favorableNextS25Before 8 [] (.query 6)
    (by decide) (by decide) favorableNextS25Choice0
  have hnew := native_select_new_step budgetTape (7/5) (controlPenalty savedCref uniformQuoteError unitRoleUnused .next) favorableNextS25Before 7 [.query 6]
    [.normalRetriever 4,.normalRetriever 6,.normalRetriever 7,.normalRetriever 8,.normalRetriever 5,.normalRetriever 1,.normalRetriever 2,.normalRetriever 3,.normalRetriever 12,.normalRetriever 14,.normalRetriever 13,.normalRetriever 21,.normalRetriever 23,.normalRetriever 22,.normalRetriever 9,.normalRetriever 11,.normalRetriever 10,.normalRetriever 15,.normalRetriever 17,.normalRetriever 16,.normalRetriever 18,.normalRetriever 20,.normalRetriever 19,.normalRetriever 24,.normalRetriever 25,.normalRetriever 26,.normalRetriever 27,.normalRetriever 28,.normalRetriever 29] (.normalRetriever 4) (by decide) (by decide) (by decide) (by decide)
  have hs : nativeSelect budgetTape (7/5) (controlPenalty savedCref uniformQuoteError unitRoleUnused .next) favorableNextS25Before 9 [] = [.query 6,.normalRetriever 4] := by
    rw [hs0]
    change nativeSelect budgetTape (7/5) (controlPenalty savedCref uniformQuoteError unitRoleUnused .next) favorableNextS25Before 8 [.query 6] = _
    rw [hnew] <;> rfl
  have hr : repairedRollout budgetTape favorableNextS25Before 9 [.query 6,.normalRetriever 4] = [.query 6,.normalRetriever 4,.selection 0,.width 0,.stop,.reranker 0,.topm 0,.context 0,.answer 0] := by decide
  simp only [nativeEvent,hs,hr]
  rfl

def favorableNextS26Before := favorableNextProposal.take 25

theorem favorableNextS26D0I0 : indexScore (7/5) (controlPenalty savedCref uniformQuoteError unitRoleUnused .next) favorableNextS26Before [] (.query 0) = treeIndex ((0/1)/3) (7/5) (nextNormalPenalty favorableNextS26Before) 25 3 := by
  have hs : replayBackup favorableNextS26Before emptyStatistics ([]++[.query 0]) = ⟨3,(0/1)⟩ := by
    rw [replayBackup_empty_closed_form]
    simp +decide [backedEvents,favorableNextS26Before,favorableNextProposal,favorableNextEvent1,favorableNextEvent2,favorableNextEvent3,favorableNextEvent4,favorableNextEvent5,favorableNextEvent6,favorableNextEvent7,favorableNextEvent8,favorableNextEvent9,favorableNextEvent10,favorableNextEvent11,favorableNextEvent12,favorableNextEvent13,favorableNextEvent14,favorableNextEvent15,favorableNextEvent16,favorableNextEvent17,favorableNextEvent18,favorableNextEvent19,favorableNextEvent20,favorableNextEvent21,favorableNextEvent22,favorableNextEvent23,favorableNextEvent24,favorableNextEvent25,taskReward]
    <;> norm_num
  have hp : rawVisits favorableNextS26Before [] = 25 := by decide
  have hn : rawVisits favorableNextS26Before ([]++[.query 0]) = 3 := by decide
  have hz : (controlPenalty savedCref uniformQuoteError unitRoleUnused .next) favorableNextS26Before [] (.query 0) = (nextNormalPenalty favorableNextS26Before) := by
    simpa only [favorableNextS26Before,nextNormalPenalty] using AgentUCTNextExact.favorable_next_normal_root_quotes_exact 25 (by omega) 0 (by decide)
  unfold indexScore
  rw [hs,hp,hn,hz]
  simp only [BackupStat.mean]
  norm_num

theorem favorableNextS26D0I1 : indexScore (7/5) (controlPenalty savedCref uniformQuoteError unitRoleUnused .next) favorableNextS26Before [] (.query 1) = treeIndex ((1/2)/4) (7/5) 0 25 4 := by
  have hs : replayBackup favorableNextS26Before emptyStatistics ([]++[.query 1]) = ⟨4,(1/2)⟩ := by
    rw [replayBackup_empty_closed_form]
    simp +decide [backedEvents,favorableNextS26Before,favorableNextProposal,favorableNextEvent1,favorableNextEvent2,favorableNextEvent3,favorableNextEvent4,favorableNextEvent5,favorableNextEvent6,favorableNextEvent7,favorableNextEvent8,favorableNextEvent9,favorableNextEvent10,favorableNextEvent11,favorableNextEvent12,favorableNextEvent13,favorableNextEvent14,favorableNextEvent15,favorableNextEvent16,favorableNextEvent17,favorableNextEvent18,favorableNextEvent19,favorableNextEvent20,favorableNextEvent21,favorableNextEvent22,favorableNextEvent23,favorableNextEvent24,favorableNextEvent25,taskReward]
    <;> norm_num
  have hp : rawVisits favorableNextS26Before [] = 25 := by decide
  have hn : rawVisits favorableNextS26Before ([]++[.query 1]) = 4 := by decide
  have hz : (controlPenalty savedCref uniformQuoteError unitRoleUnused .next) favorableNextS26Before [] (.query 1) = 0 := by
    apply control_penalty_empty_suffix
    decide
  unfold indexScore
  rw [hs,hp,hn,hz]
  simp only [BackupStat.mean]
  norm_num

theorem favorableNextS26D0I2 : indexScore (7/5) (controlPenalty savedCref uniformQuoteError unitRoleUnused .next) favorableNextS26Before [] (.query 2) = treeIndex ((0/1)/3) (7/5) (nextNormalPenalty favorableNextS26Before) 25 3 := by
  have hs : replayBackup favorableNextS26Before emptyStatistics ([]++[.query 2]) = ⟨3,(0/1)⟩ := by
    rw [replayBackup_empty_closed_form]
    simp +decide [backedEvents,favorableNextS26Before,favorableNextProposal,favorableNextEvent1,favorableNextEvent2,favorableNextEvent3,favorableNextEvent4,favorableNextEvent5,favorableNextEvent6,favorableNextEvent7,favorableNextEvent8,favorableNextEvent9,favorableNextEvent10,favorableNextEvent11,favorableNextEvent12,favorableNextEvent13,favorableNextEvent14,favorableNextEvent15,favorableNextEvent16,favorableNextEvent17,favorableNextEvent18,favorableNextEvent19,favorableNextEvent20,favorableNextEvent21,favorableNextEvent22,favorableNextEvent23,favorableNextEvent24,favorableNextEvent25,taskReward]
    <;> norm_num
  have hp : rawVisits favorableNextS26Before [] = 25 := by decide
  have hn : rawVisits favorableNextS26Before ([]++[.query 2]) = 3 := by decide
  have hz : (controlPenalty savedCref uniformQuoteError unitRoleUnused .next) favorableNextS26Before [] (.query 2) = (nextNormalPenalty favorableNextS26Before) := by
    simpa only [favorableNextS26Before,nextNormalPenalty] using AgentUCTNextExact.favorable_next_normal_root_quotes_exact 25 (by omega) 2 (by decide)
  unfold indexScore
  rw [hs,hp,hn,hz]
  simp only [BackupStat.mean]
  norm_num

theorem favorableNextS26D0I3 : indexScore (7/5) (controlPenalty savedCref uniformQuoteError unitRoleUnused .next) favorableNextS26Before [] (.query 3) = treeIndex ((0/1)/3) (7/5) (nextNormalPenalty favorableNextS26Before) 25 3 := by
  have hs : replayBackup favorableNextS26Before emptyStatistics ([]++[.query 3]) = ⟨3,(0/1)⟩ := by
    rw [replayBackup_empty_closed_form]
    simp +decide [backedEvents,favorableNextS26Before,favorableNextProposal,favorableNextEvent1,favorableNextEvent2,favorableNextEvent3,favorableNextEvent4,favorableNextEvent5,favorableNextEvent6,favorableNextEvent7,favorableNextEvent8,favorableNextEvent9,favorableNextEvent10,favorableNextEvent11,favorableNextEvent12,favorableNextEvent13,favorableNextEvent14,favorableNextEvent15,favorableNextEvent16,favorableNextEvent17,favorableNextEvent18,favorableNextEvent19,favorableNextEvent20,favorableNextEvent21,favorableNextEvent22,favorableNextEvent23,favorableNextEvent24,favorableNextEvent25,taskReward]
    <;> norm_num
  have hp : rawVisits favorableNextS26Before [] = 25 := by decide
  have hn : rawVisits favorableNextS26Before ([]++[.query 3]) = 3 := by decide
  have hz : (controlPenalty savedCref uniformQuoteError unitRoleUnused .next) favorableNextS26Before [] (.query 3) = (nextNormalPenalty favorableNextS26Before) := by
    simpa only [favorableNextS26Before,nextNormalPenalty] using AgentUCTNextExact.favorable_next_normal_root_quotes_exact 25 (by omega) 3 (by decide)
  unfold indexScore
  rw [hs,hp,hn,hz]
  simp only [BackupStat.mean]
  norm_num

theorem favorableNextS26D0I4 : indexScore (7/5) (controlPenalty savedCref uniformQuoteError unitRoleUnused .next) favorableNextS26Before [] (.query 4) = treeIndex ((0/1)/3) (7/5) (nextNormalPenalty favorableNextS26Before) 25 3 := by
  have hs : replayBackup favorableNextS26Before emptyStatistics ([]++[.query 4]) = ⟨3,(0/1)⟩ := by
    rw [replayBackup_empty_closed_form]
    simp +decide [backedEvents,favorableNextS26Before,favorableNextProposal,favorableNextEvent1,favorableNextEvent2,favorableNextEvent3,favorableNextEvent4,favorableNextEvent5,favorableNextEvent6,favorableNextEvent7,favorableNextEvent8,favorableNextEvent9,favorableNextEvent10,favorableNextEvent11,favorableNextEvent12,favorableNextEvent13,favorableNextEvent14,favorableNextEvent15,favorableNextEvent16,favorableNextEvent17,favorableNextEvent18,favorableNextEvent19,favorableNextEvent20,favorableNextEvent21,favorableNextEvent22,favorableNextEvent23,favorableNextEvent24,favorableNextEvent25,taskReward]
    <;> norm_num
  have hp : rawVisits favorableNextS26Before [] = 25 := by decide
  have hn : rawVisits favorableNextS26Before ([]++[.query 4]) = 3 := by decide
  have hz : (controlPenalty savedCref uniformQuoteError unitRoleUnused .next) favorableNextS26Before [] (.query 4) = (nextNormalPenalty favorableNextS26Before) := by
    simpa only [favorableNextS26Before,nextNormalPenalty] using AgentUCTNextExact.favorable_next_normal_root_quotes_exact 25 (by omega) 4 (by decide)
  unfold indexScore
  rw [hs,hp,hn,hz]
  simp only [BackupStat.mean]
  norm_num

theorem favorableNextS26D0I5 : indexScore (7/5) (controlPenalty savedCref uniformQuoteError unitRoleUnused .next) favorableNextS26Before [] (.query 5) = treeIndex ((6/5)/4) (7/5) (nextNormalPenalty favorableNextS26Before) 25 4 := by
  have hs : replayBackup favorableNextS26Before emptyStatistics ([]++[.query 5]) = ⟨4,(6/5)⟩ := by
    rw [replayBackup_empty_closed_form]
    simp +decide [backedEvents,favorableNextS26Before,favorableNextProposal,favorableNextEvent1,favorableNextEvent2,favorableNextEvent3,favorableNextEvent4,favorableNextEvent5,favorableNextEvent6,favorableNextEvent7,favorableNextEvent8,favorableNextEvent9,favorableNextEvent10,favorableNextEvent11,favorableNextEvent12,favorableNextEvent13,favorableNextEvent14,favorableNextEvent15,favorableNextEvent16,favorableNextEvent17,favorableNextEvent18,favorableNextEvent19,favorableNextEvent20,favorableNextEvent21,favorableNextEvent22,favorableNextEvent23,favorableNextEvent24,favorableNextEvent25,taskReward]
    <;> norm_num
  have hp : rawVisits favorableNextS26Before [] = 25 := by decide
  have hn : rawVisits favorableNextS26Before ([]++[.query 5]) = 4 := by decide
  have hz : (controlPenalty savedCref uniformQuoteError unitRoleUnused .next) favorableNextS26Before [] (.query 5) = (nextNormalPenalty favorableNextS26Before) := by
    simpa only [favorableNextS26Before,nextNormalPenalty] using AgentUCTNextExact.favorable_next_normal_root_quotes_exact 25 (by omega) 5 (by decide)
  unfold indexScore
  rw [hs,hp,hn,hz]
  simp only [BackupStat.mean]
  norm_num

theorem favorableNextS26D0I6 : indexScore (7/5) (controlPenalty savedCref uniformQuoteError unitRoleUnused .next) favorableNextS26Before [] (.query 6) = treeIndex ((0/1)/3) (7/5) (nextNormalPenalty favorableNextS26Before) 25 3 := by
  have hs : replayBackup favorableNextS26Before emptyStatistics ([]++[.query 6]) = ⟨3,(0/1)⟩ := by
    rw [replayBackup_empty_closed_form]
    simp +decide [backedEvents,favorableNextS26Before,favorableNextProposal,favorableNextEvent1,favorableNextEvent2,favorableNextEvent3,favorableNextEvent4,favorableNextEvent5,favorableNextEvent6,favorableNextEvent7,favorableNextEvent8,favorableNextEvent9,favorableNextEvent10,favorableNextEvent11,favorableNextEvent12,favorableNextEvent13,favorableNextEvent14,favorableNextEvent15,favorableNextEvent16,favorableNextEvent17,favorableNextEvent18,favorableNextEvent19,favorableNextEvent20,favorableNextEvent21,favorableNextEvent22,favorableNextEvent23,favorableNextEvent24,favorableNextEvent25,taskReward]
    <;> norm_num
  have hp : rawVisits favorableNextS26Before [] = 25 := by decide
  have hn : rawVisits favorableNextS26Before ([]++[.query 6]) = 3 := by decide
  have hz : (controlPenalty savedCref uniformQuoteError unitRoleUnused .next) favorableNextS26Before [] (.query 6) = (nextNormalPenalty favorableNextS26Before) := by
    simpa only [favorableNextS26Before,nextNormalPenalty] using AgentUCTNextExact.favorable_next_normal_root_quotes_exact 25 (by omega) 6 (by decide)
  unfold indexScore
  rw [hs,hp,hn,hz]
  simp only [BackupStat.mean]
  norm_num

theorem favorableNextS26D0I7 : indexScore (7/5) (controlPenalty savedCref uniformQuoteError unitRoleUnused .next) favorableNextS26Before [] (.query 7) = treeIndex ((0/1)/2) (7/5) (nextNormalPenalty favorableNextS26Before) 25 2 := by
  have hs : replayBackup favorableNextS26Before emptyStatistics ([]++[.query 7]) = ⟨2,(0/1)⟩ := by
    rw [replayBackup_empty_closed_form]
    simp +decide [backedEvents,favorableNextS26Before,favorableNextProposal,favorableNextEvent1,favorableNextEvent2,favorableNextEvent3,favorableNextEvent4,favorableNextEvent5,favorableNextEvent6,favorableNextEvent7,favorableNextEvent8,favorableNextEvent9,favorableNextEvent10,favorableNextEvent11,favorableNextEvent12,favorableNextEvent13,favorableNextEvent14,favorableNextEvent15,favorableNextEvent16,favorableNextEvent17,favorableNextEvent18,favorableNextEvent19,favorableNextEvent20,favorableNextEvent21,favorableNextEvent22,favorableNextEvent23,favorableNextEvent24,favorableNextEvent25,taskReward]
    <;> norm_num
  have hp : rawVisits favorableNextS26Before [] = 25 := by decide
  have hn : rawVisits favorableNextS26Before ([]++[.query 7]) = 2 := by decide
  have hz : (controlPenalty savedCref uniformQuoteError unitRoleUnused .next) favorableNextS26Before [] (.query 7) = (nextNormalPenalty favorableNextS26Before) := by
    simpa only [favorableNextS26Before,nextNormalPenalty] using AgentUCTNextExact.favorable_next_normal_root_quotes_exact 25 (by omega) 7 (by decide)
  unfold indexScore
  rw [hs,hp,hn,hz]
  simp only [BackupStat.mean]
  norm_num

theorem favorableNextS26D0Cmp0 : indexScore (7/5) (controlPenalty savedCref uniformQuoteError unitRoleUnused .next) favorableNextS26Before [] (.query 0) < indexScore (7/5) (controlPenalty savedCref uniformQuoteError unitRoleUnused .next) favorableNextS26Before [] (.query 7) := by
  rw [favorableNextS26D0I0,favorableNextS26D0I7]
  have hk := favorable_next_penalty_interval 25 (by omega)
  change nextNormalPenaltyLower ≤ nextNormalPenalty favorableNextS26Before ∧ nextNormalPenalty favorableNextS26Before ≤ nextNormalPenaltyUpper at hk
  have hm : ((0/1)/3)+(72949009/50000000)-(nextNormalPenalty favorableNextS26Before) < ((0/1)/2)+(89343919/50000000)-(nextNormalPenalty favorableNextS26Before) := by
    have h : (((0/1)/3)+(72949009/50000000) : ℝ) < ((0/1)/2)+(89343919/50000000) := by norm_num
    linarith
  have h := index_strict_order_from_intervals ((0/1)/2) ((0/1)/3) (nextNormalPenalty favorableNextS26Before) (nextNormalPenalty favorableNextS26Before) (89343919/50000000) (72949009/50000000)
    (treeBonus (7/5) 25 2) (treeBonus (7/5) 25 3)
    (trajectory_bonus_25_2).1 (trajectory_bonus_25_3).2 hm
  simpa only [treeIndex] using h

theorem favorableNextS26D0Cmp1 : indexScore (7/5) (controlPenalty savedCref uniformQuoteError unitRoleUnused .next) favorableNextS26Before [] (.query 1) < indexScore (7/5) (controlPenalty savedCref uniformQuoteError unitRoleUnused .next) favorableNextS26Before [] (.query 7) := by
  rw [favorableNextS26D0I1,favorableNextS26D0I7]
  have hk := favorable_next_penalty_interval 25 (by omega)
  change nextNormalPenaltyLower ≤ nextNormalPenalty favorableNextS26Before ∧ nextNormalPenalty favorableNextS26Before ≤ nextNormalPenaltyUpper at hk
  have hm : ((1/2)/4)+(631757/500000)-0 < ((0/1)/2)+(89343919/50000000)-(nextNormalPenalty favorableNextS26Before) := by
    have h : ((1/2)/4)+(631757/500000) < ((0/1)/2)+(89343919/50000000)-nextNormalPenaltyUpper := by norm_num [nextNormalPenaltyUpper,savedCref,uniformQuoteError]
    linarith [hk.2]
  have h := index_strict_order_from_intervals ((0/1)/2) ((1/2)/4) (nextNormalPenalty favorableNextS26Before) 0 (89343919/50000000) (631757/500000)
    (treeBonus (7/5) 25 2) (treeBonus (7/5) 25 4)
    (trajectory_bonus_25_2).1 (trajectory_bonus_25_4).2 hm
  simpa only [treeIndex] using h

theorem favorableNextS26D0Cmp2 : indexScore (7/5) (controlPenalty savedCref uniformQuoteError unitRoleUnused .next) favorableNextS26Before [] (.query 2) < indexScore (7/5) (controlPenalty savedCref uniformQuoteError unitRoleUnused .next) favorableNextS26Before [] (.query 7) := by
  rw [favorableNextS26D0I2,favorableNextS26D0I7]
  have hk := favorable_next_penalty_interval 25 (by omega)
  change nextNormalPenaltyLower ≤ nextNormalPenalty favorableNextS26Before ∧ nextNormalPenalty favorableNextS26Before ≤ nextNormalPenaltyUpper at hk
  have hm : ((0/1)/3)+(72949009/50000000)-(nextNormalPenalty favorableNextS26Before) < ((0/1)/2)+(89343919/50000000)-(nextNormalPenalty favorableNextS26Before) := by
    have h : (((0/1)/3)+(72949009/50000000) : ℝ) < ((0/1)/2)+(89343919/50000000) := by norm_num
    linarith
  have h := index_strict_order_from_intervals ((0/1)/2) ((0/1)/3) (nextNormalPenalty favorableNextS26Before) (nextNormalPenalty favorableNextS26Before) (89343919/50000000) (72949009/50000000)
    (treeBonus (7/5) 25 2) (treeBonus (7/5) 25 3)
    (trajectory_bonus_25_2).1 (trajectory_bonus_25_3).2 hm
  simpa only [treeIndex] using h

theorem favorableNextS26D0Cmp3 : indexScore (7/5) (controlPenalty savedCref uniformQuoteError unitRoleUnused .next) favorableNextS26Before [] (.query 3) < indexScore (7/5) (controlPenalty savedCref uniformQuoteError unitRoleUnused .next) favorableNextS26Before [] (.query 7) := by
  rw [favorableNextS26D0I3,favorableNextS26D0I7]
  have hk := favorable_next_penalty_interval 25 (by omega)
  change nextNormalPenaltyLower ≤ nextNormalPenalty favorableNextS26Before ∧ nextNormalPenalty favorableNextS26Before ≤ nextNormalPenaltyUpper at hk
  have hm : ((0/1)/3)+(72949009/50000000)-(nextNormalPenalty favorableNextS26Before) < ((0/1)/2)+(89343919/50000000)-(nextNormalPenalty favorableNextS26Before) := by
    have h : (((0/1)/3)+(72949009/50000000) : ℝ) < ((0/1)/2)+(89343919/50000000) := by norm_num
    linarith
  have h := index_strict_order_from_intervals ((0/1)/2) ((0/1)/3) (nextNormalPenalty favorableNextS26Before) (nextNormalPenalty favorableNextS26Before) (89343919/50000000) (72949009/50000000)
    (treeBonus (7/5) 25 2) (treeBonus (7/5) 25 3)
    (trajectory_bonus_25_2).1 (trajectory_bonus_25_3).2 hm
  simpa only [treeIndex] using h

theorem favorableNextS26D0Cmp4 : indexScore (7/5) (controlPenalty savedCref uniformQuoteError unitRoleUnused .next) favorableNextS26Before [] (.query 4) < indexScore (7/5) (controlPenalty savedCref uniformQuoteError unitRoleUnused .next) favorableNextS26Before [] (.query 7) := by
  rw [favorableNextS26D0I4,favorableNextS26D0I7]
  have hk := favorable_next_penalty_interval 25 (by omega)
  change nextNormalPenaltyLower ≤ nextNormalPenalty favorableNextS26Before ∧ nextNormalPenalty favorableNextS26Before ≤ nextNormalPenaltyUpper at hk
  have hm : ((0/1)/3)+(72949009/50000000)-(nextNormalPenalty favorableNextS26Before) < ((0/1)/2)+(89343919/50000000)-(nextNormalPenalty favorableNextS26Before) := by
    have h : (((0/1)/3)+(72949009/50000000) : ℝ) < ((0/1)/2)+(89343919/50000000) := by norm_num
    linarith
  have h := index_strict_order_from_intervals ((0/1)/2) ((0/1)/3) (nextNormalPenalty favorableNextS26Before) (nextNormalPenalty favorableNextS26Before) (89343919/50000000) (72949009/50000000)
    (treeBonus (7/5) 25 2) (treeBonus (7/5) 25 3)
    (trajectory_bonus_25_2).1 (trajectory_bonus_25_3).2 hm
  simpa only [treeIndex] using h

theorem favorableNextS26D0Cmp5 : indexScore (7/5) (controlPenalty savedCref uniformQuoteError unitRoleUnused .next) favorableNextS26Before [] (.query 5) < indexScore (7/5) (controlPenalty savedCref uniformQuoteError unitRoleUnused .next) favorableNextS26Before [] (.query 7) := by
  rw [favorableNextS26D0I5,favorableNextS26D0I7]
  have hk := favorable_next_penalty_interval 25 (by omega)
  change nextNormalPenaltyLower ≤ nextNormalPenalty favorableNextS26Before ∧ nextNormalPenalty favorableNextS26Before ≤ nextNormalPenaltyUpper at hk
  have hm : ((6/5)/4)+(631757/500000)-(nextNormalPenalty favorableNextS26Before) < ((0/1)/2)+(89343919/50000000)-(nextNormalPenalty favorableNextS26Before) := by
    have h : (((6/5)/4)+(631757/500000) : ℝ) < ((0/1)/2)+(89343919/50000000) := by norm_num
    linarith
  have h := index_strict_order_from_intervals ((0/1)/2) ((6/5)/4) (nextNormalPenalty favorableNextS26Before) (nextNormalPenalty favorableNextS26Before) (89343919/50000000) (631757/500000)
    (treeBonus (7/5) 25 2) (treeBonus (7/5) 25 4)
    (trajectory_bonus_25_2).1 (trajectory_bonus_25_4).2 hm
  simpa only [treeIndex] using h

theorem favorableNextS26D0Cmp6 : indexScore (7/5) (controlPenalty savedCref uniformQuoteError unitRoleUnused .next) favorableNextS26Before [] (.query 6) < indexScore (7/5) (controlPenalty savedCref uniformQuoteError unitRoleUnused .next) favorableNextS26Before [] (.query 7) := by
  rw [favorableNextS26D0I6,favorableNextS26D0I7]
  have hk := favorable_next_penalty_interval 25 (by omega)
  change nextNormalPenaltyLower ≤ nextNormalPenalty favorableNextS26Before ∧ nextNormalPenalty favorableNextS26Before ≤ nextNormalPenaltyUpper at hk
  have hm : ((0/1)/3)+(72949009/50000000)-(nextNormalPenalty favorableNextS26Before) < ((0/1)/2)+(89343919/50000000)-(nextNormalPenalty favorableNextS26Before) := by
    have h : (((0/1)/3)+(72949009/50000000) : ℝ) < ((0/1)/2)+(89343919/50000000) := by norm_num
    linarith
  have h := index_strict_order_from_intervals ((0/1)/2) ((0/1)/3) (nextNormalPenalty favorableNextS26Before) (nextNormalPenalty favorableNextS26Before) (89343919/50000000) (72949009/50000000)
    (treeBonus (7/5) 25 2) (treeBonus (7/5) 25 3)
    (trajectory_bonus_25_2).1 (trajectory_bonus_25_3).2 hm
  simpa only [treeIndex] using h

theorem favorableNextS26Choice0 : nativeFirstChoice (indexScore (7/5) (controlPenalty savedCref uniformQuoteError unitRoleUnused .next) favorableNextS26Before []) favorableNextS26Before [] = .query 7 := by
  apply visited_choice_from_ordered_certificate _ _ [] [.query 0,.query 1,.query 2,.query 3,.query 4,.query 5,.query 6] [] (.query 7) (by decide)
  · intro a ha
    have ho : orderedLegalAvailable [] = [.query 0,.query 1,.query 2,.query 3,.query 4,.query 5,.query 6,.query 7] := by decide
    rw [ho] at ha
    simp only [List.mem_cons,List.not_mem_nil,or_false] at ha
    rcases ha with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> decide
  · intro a ha
    simp only [List.mem_cons,List.not_mem_nil,or_false] at ha
    rcases ha with rfl | rfl | rfl | rfl | rfl | rfl | rfl
    · exact favorableNextS26D0Cmp0
    · exact favorableNextS26D0Cmp1
    · exact favorableNextS26D0Cmp2
    · exact favorableNextS26D0Cmp3
    · exact favorableNextS26D0Cmp4
    · exact favorableNextS26D0Cmp5
    · exact favorableNextS26D0Cmp6
  · simp

theorem favorableNextS26ActualEvent : nativeEvent budgetTape (7/5) (controlPenalty savedCref uniformQuoteError unitRoleUnused .next)
    (taskReward false (2/5) (1/2)) favorableNextS26Before = favorableNextEvent26 := by
  have hs0 := native_select_existing_step budgetTape (7/5) (controlPenalty savedCref uniformQuoteError unitRoleUnused .next) favorableNextS26Before 8 [] (.query 7)
    (by decide) (by decide) favorableNextS26Choice0
  have hnew := native_select_new_step budgetTape (7/5) (controlPenalty savedCref uniformQuoteError unitRoleUnused .next) favorableNextS26Before 7 [.query 7]
    [.normalRetriever 4,.normalRetriever 6,.normalRetriever 7,.normalRetriever 8,.normalRetriever 5,.normalRetriever 1,.normalRetriever 2,.normalRetriever 3,.normalRetriever 12,.normalRetriever 14,.normalRetriever 13,.normalRetriever 21,.normalRetriever 23,.normalRetriever 22,.normalRetriever 9,.normalRetriever 11,.normalRetriever 10,.normalRetriever 15,.normalRetriever 17,.normalRetriever 16,.normalRetriever 18,.normalRetriever 20,.normalRetriever 19,.normalRetriever 24,.normalRetriever 25,.normalRetriever 26,.normalRetriever 27,.normalRetriever 28,.normalRetriever 29] (.normalRetriever 4) (by decide) (by decide) (by decide) (by decide)
  have hs : nativeSelect budgetTape (7/5) (controlPenalty savedCref uniformQuoteError unitRoleUnused .next) favorableNextS26Before 9 [] = [.query 7,.normalRetriever 4] := by
    rw [hs0]
    change nativeSelect budgetTape (7/5) (controlPenalty savedCref uniformQuoteError unitRoleUnused .next) favorableNextS26Before 8 [.query 7] = _
    rw [hnew] <;> rfl
  have hr : repairedRollout budgetTape favorableNextS26Before 9 [.query 7,.normalRetriever 4] = [.query 7,.normalRetriever 4,.selection 0,.width 0,.stop,.reranker 0,.topm 0,.context 0,.answer 0] := by decide
  simp only [nativeEvent,hs,hr]
  rfl

end AgentUCT32MConcrete
