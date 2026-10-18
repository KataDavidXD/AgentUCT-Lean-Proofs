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

def favorableNextS27Before := favorableNextProposal.take 26

theorem favorableNextS27D0I0 : indexScore (7/5) (controlPenalty savedCref uniformQuoteError unitRoleUnused .next) favorableNextS27Before [] (.query 0) = treeIndex ((0/1)/3) (7/5) (nextNormalPenalty favorableNextS27Before) 26 3 := by
  have hs : replayBackup favorableNextS27Before emptyStatistics ([]++[.query 0]) = ⟨3,(0/1)⟩ := by
    rw [replayBackup_empty_closed_form]
    simp +decide [backedEvents,favorableNextS27Before,favorableNextProposal,favorableNextEvent1,favorableNextEvent2,favorableNextEvent3,favorableNextEvent4,favorableNextEvent5,favorableNextEvent6,favorableNextEvent7,favorableNextEvent8,favorableNextEvent9,favorableNextEvent10,favorableNextEvent11,favorableNextEvent12,favorableNextEvent13,favorableNextEvent14,favorableNextEvent15,favorableNextEvent16,favorableNextEvent17,favorableNextEvent18,favorableNextEvent19,favorableNextEvent20,favorableNextEvent21,favorableNextEvent22,favorableNextEvent23,favorableNextEvent24,favorableNextEvent25,favorableNextEvent26,taskReward]
    <;> norm_num
  have hp : rawVisits favorableNextS27Before [] = 26 := by decide
  have hn : rawVisits favorableNextS27Before ([]++[.query 0]) = 3 := by decide
  have hz : (controlPenalty savedCref uniformQuoteError unitRoleUnused .next) favorableNextS27Before [] (.query 0) = (nextNormalPenalty favorableNextS27Before) := by
    simpa only [favorableNextS27Before,nextNormalPenalty] using AgentUCTNextExact.favorable_next_normal_root_quotes_exact 26 (by omega) 0 (by decide)
  unfold indexScore
  rw [hs,hp,hn,hz]
  simp only [BackupStat.mean]
  norm_num

theorem favorableNextS27D0I1 : indexScore (7/5) (controlPenalty savedCref uniformQuoteError unitRoleUnused .next) favorableNextS27Before [] (.query 1) = treeIndex ((1/2)/4) (7/5) 0 26 4 := by
  have hs : replayBackup favorableNextS27Before emptyStatistics ([]++[.query 1]) = ⟨4,(1/2)⟩ := by
    rw [replayBackup_empty_closed_form]
    simp +decide [backedEvents,favorableNextS27Before,favorableNextProposal,favorableNextEvent1,favorableNextEvent2,favorableNextEvent3,favorableNextEvent4,favorableNextEvent5,favorableNextEvent6,favorableNextEvent7,favorableNextEvent8,favorableNextEvent9,favorableNextEvent10,favorableNextEvent11,favorableNextEvent12,favorableNextEvent13,favorableNextEvent14,favorableNextEvent15,favorableNextEvent16,favorableNextEvent17,favorableNextEvent18,favorableNextEvent19,favorableNextEvent20,favorableNextEvent21,favorableNextEvent22,favorableNextEvent23,favorableNextEvent24,favorableNextEvent25,favorableNextEvent26,taskReward]
    <;> norm_num
  have hp : rawVisits favorableNextS27Before [] = 26 := by decide
  have hn : rawVisits favorableNextS27Before ([]++[.query 1]) = 4 := by decide
  have hz : (controlPenalty savedCref uniformQuoteError unitRoleUnused .next) favorableNextS27Before [] (.query 1) = 0 := by
    apply control_penalty_empty_suffix
    exact AgentUCTNextExact.favorable_next_hyde_root_suffix_empty 26 (by omega)
  unfold indexScore
  rw [hs,hp,hn,hz]
  simp only [BackupStat.mean]
  norm_num

theorem favorableNextS27D0I2 : indexScore (7/5) (controlPenalty savedCref uniformQuoteError unitRoleUnused .next) favorableNextS27Before [] (.query 2) = treeIndex ((0/1)/3) (7/5) (nextNormalPenalty favorableNextS27Before) 26 3 := by
  have hs : replayBackup favorableNextS27Before emptyStatistics ([]++[.query 2]) = ⟨3,(0/1)⟩ := by
    rw [replayBackup_empty_closed_form]
    simp +decide [backedEvents,favorableNextS27Before,favorableNextProposal,favorableNextEvent1,favorableNextEvent2,favorableNextEvent3,favorableNextEvent4,favorableNextEvent5,favorableNextEvent6,favorableNextEvent7,favorableNextEvent8,favorableNextEvent9,favorableNextEvent10,favorableNextEvent11,favorableNextEvent12,favorableNextEvent13,favorableNextEvent14,favorableNextEvent15,favorableNextEvent16,favorableNextEvent17,favorableNextEvent18,favorableNextEvent19,favorableNextEvent20,favorableNextEvent21,favorableNextEvent22,favorableNextEvent23,favorableNextEvent24,favorableNextEvent25,favorableNextEvent26,taskReward]
    <;> norm_num
  have hp : rawVisits favorableNextS27Before [] = 26 := by decide
  have hn : rawVisits favorableNextS27Before ([]++[.query 2]) = 3 := by decide
  have hz : (controlPenalty savedCref uniformQuoteError unitRoleUnused .next) favorableNextS27Before [] (.query 2) = (nextNormalPenalty favorableNextS27Before) := by
    simpa only [favorableNextS27Before,nextNormalPenalty] using AgentUCTNextExact.favorable_next_normal_root_quotes_exact 26 (by omega) 2 (by decide)
  unfold indexScore
  rw [hs,hp,hn,hz]
  simp only [BackupStat.mean]
  norm_num

theorem favorableNextS27D0I3 : indexScore (7/5) (controlPenalty savedCref uniformQuoteError unitRoleUnused .next) favorableNextS27Before [] (.query 3) = treeIndex ((0/1)/3) (7/5) (nextNormalPenalty favorableNextS27Before) 26 3 := by
  have hs : replayBackup favorableNextS27Before emptyStatistics ([]++[.query 3]) = ⟨3,(0/1)⟩ := by
    rw [replayBackup_empty_closed_form]
    simp +decide [backedEvents,favorableNextS27Before,favorableNextProposal,favorableNextEvent1,favorableNextEvent2,favorableNextEvent3,favorableNextEvent4,favorableNextEvent5,favorableNextEvent6,favorableNextEvent7,favorableNextEvent8,favorableNextEvent9,favorableNextEvent10,favorableNextEvent11,favorableNextEvent12,favorableNextEvent13,favorableNextEvent14,favorableNextEvent15,favorableNextEvent16,favorableNextEvent17,favorableNextEvent18,favorableNextEvent19,favorableNextEvent20,favorableNextEvent21,favorableNextEvent22,favorableNextEvent23,favorableNextEvent24,favorableNextEvent25,favorableNextEvent26,taskReward]
    <;> norm_num
  have hp : rawVisits favorableNextS27Before [] = 26 := by decide
  have hn : rawVisits favorableNextS27Before ([]++[.query 3]) = 3 := by decide
  have hz : (controlPenalty savedCref uniformQuoteError unitRoleUnused .next) favorableNextS27Before [] (.query 3) = (nextNormalPenalty favorableNextS27Before) := by
    simpa only [favorableNextS27Before,nextNormalPenalty] using AgentUCTNextExact.favorable_next_normal_root_quotes_exact 26 (by omega) 3 (by decide)
  unfold indexScore
  rw [hs,hp,hn,hz]
  simp only [BackupStat.mean]
  norm_num

theorem favorableNextS27D0I4 : indexScore (7/5) (controlPenalty savedCref uniformQuoteError unitRoleUnused .next) favorableNextS27Before [] (.query 4) = treeIndex ((0/1)/3) (7/5) (nextNormalPenalty favorableNextS27Before) 26 3 := by
  have hs : replayBackup favorableNextS27Before emptyStatistics ([]++[.query 4]) = ⟨3,(0/1)⟩ := by
    rw [replayBackup_empty_closed_form]
    simp +decide [backedEvents,favorableNextS27Before,favorableNextProposal,favorableNextEvent1,favorableNextEvent2,favorableNextEvent3,favorableNextEvent4,favorableNextEvent5,favorableNextEvent6,favorableNextEvent7,favorableNextEvent8,favorableNextEvent9,favorableNextEvent10,favorableNextEvent11,favorableNextEvent12,favorableNextEvent13,favorableNextEvent14,favorableNextEvent15,favorableNextEvent16,favorableNextEvent17,favorableNextEvent18,favorableNextEvent19,favorableNextEvent20,favorableNextEvent21,favorableNextEvent22,favorableNextEvent23,favorableNextEvent24,favorableNextEvent25,favorableNextEvent26,taskReward]
    <;> norm_num
  have hp : rawVisits favorableNextS27Before [] = 26 := by decide
  have hn : rawVisits favorableNextS27Before ([]++[.query 4]) = 3 := by decide
  have hz : (controlPenalty savedCref uniformQuoteError unitRoleUnused .next) favorableNextS27Before [] (.query 4) = (nextNormalPenalty favorableNextS27Before) := by
    simpa only [favorableNextS27Before,nextNormalPenalty] using AgentUCTNextExact.favorable_next_normal_root_quotes_exact 26 (by omega) 4 (by decide)
  unfold indexScore
  rw [hs,hp,hn,hz]
  simp only [BackupStat.mean]
  norm_num

theorem favorableNextS27D0I5 : indexScore (7/5) (controlPenalty savedCref uniformQuoteError unitRoleUnused .next) favorableNextS27Before [] (.query 5) = treeIndex ((6/5)/4) (7/5) (nextNormalPenalty favorableNextS27Before) 26 4 := by
  have hs : replayBackup favorableNextS27Before emptyStatistics ([]++[.query 5]) = ⟨4,(6/5)⟩ := by
    rw [replayBackup_empty_closed_form]
    simp +decide [backedEvents,favorableNextS27Before,favorableNextProposal,favorableNextEvent1,favorableNextEvent2,favorableNextEvent3,favorableNextEvent4,favorableNextEvent5,favorableNextEvent6,favorableNextEvent7,favorableNextEvent8,favorableNextEvent9,favorableNextEvent10,favorableNextEvent11,favorableNextEvent12,favorableNextEvent13,favorableNextEvent14,favorableNextEvent15,favorableNextEvent16,favorableNextEvent17,favorableNextEvent18,favorableNextEvent19,favorableNextEvent20,favorableNextEvent21,favorableNextEvent22,favorableNextEvent23,favorableNextEvent24,favorableNextEvent25,favorableNextEvent26,taskReward]
    <;> norm_num
  have hp : rawVisits favorableNextS27Before [] = 26 := by decide
  have hn : rawVisits favorableNextS27Before ([]++[.query 5]) = 4 := by decide
  have hz : (controlPenalty savedCref uniformQuoteError unitRoleUnused .next) favorableNextS27Before [] (.query 5) = (nextNormalPenalty favorableNextS27Before) := by
    simpa only [favorableNextS27Before,nextNormalPenalty] using AgentUCTNextExact.favorable_next_normal_root_quotes_exact 26 (by omega) 5 (by decide)
  unfold indexScore
  rw [hs,hp,hn,hz]
  simp only [BackupStat.mean]
  norm_num

theorem favorableNextS27D0I6 : indexScore (7/5) (controlPenalty savedCref uniformQuoteError unitRoleUnused .next) favorableNextS27Before [] (.query 6) = treeIndex ((0/1)/3) (7/5) (nextNormalPenalty favorableNextS27Before) 26 3 := by
  have hs : replayBackup favorableNextS27Before emptyStatistics ([]++[.query 6]) = ⟨3,(0/1)⟩ := by
    rw [replayBackup_empty_closed_form]
    simp +decide [backedEvents,favorableNextS27Before,favorableNextProposal,favorableNextEvent1,favorableNextEvent2,favorableNextEvent3,favorableNextEvent4,favorableNextEvent5,favorableNextEvent6,favorableNextEvent7,favorableNextEvent8,favorableNextEvent9,favorableNextEvent10,favorableNextEvent11,favorableNextEvent12,favorableNextEvent13,favorableNextEvent14,favorableNextEvent15,favorableNextEvent16,favorableNextEvent17,favorableNextEvent18,favorableNextEvent19,favorableNextEvent20,favorableNextEvent21,favorableNextEvent22,favorableNextEvent23,favorableNextEvent24,favorableNextEvent25,favorableNextEvent26,taskReward]
    <;> norm_num
  have hp : rawVisits favorableNextS27Before [] = 26 := by decide
  have hn : rawVisits favorableNextS27Before ([]++[.query 6]) = 3 := by decide
  have hz : (controlPenalty savedCref uniformQuoteError unitRoleUnused .next) favorableNextS27Before [] (.query 6) = (nextNormalPenalty favorableNextS27Before) := by
    simpa only [favorableNextS27Before,nextNormalPenalty] using AgentUCTNextExact.favorable_next_normal_root_quotes_exact 26 (by omega) 6 (by decide)
  unfold indexScore
  rw [hs,hp,hn,hz]
  simp only [BackupStat.mean]
  norm_num

theorem favorableNextS27D0I7 : indexScore (7/5) (controlPenalty savedCref uniformQuoteError unitRoleUnused .next) favorableNextS27Before [] (.query 7) = treeIndex ((0/1)/3) (7/5) (nextNormalPenalty favorableNextS27Before) 26 3 := by
  have hs : replayBackup favorableNextS27Before emptyStatistics ([]++[.query 7]) = ⟨3,(0/1)⟩ := by
    rw [replayBackup_empty_closed_form]
    simp +decide [backedEvents,favorableNextS27Before,favorableNextProposal,favorableNextEvent1,favorableNextEvent2,favorableNextEvent3,favorableNextEvent4,favorableNextEvent5,favorableNextEvent6,favorableNextEvent7,favorableNextEvent8,favorableNextEvent9,favorableNextEvent10,favorableNextEvent11,favorableNextEvent12,favorableNextEvent13,favorableNextEvent14,favorableNextEvent15,favorableNextEvent16,favorableNextEvent17,favorableNextEvent18,favorableNextEvent19,favorableNextEvent20,favorableNextEvent21,favorableNextEvent22,favorableNextEvent23,favorableNextEvent24,favorableNextEvent25,favorableNextEvent26,taskReward]
    <;> norm_num
  have hp : rawVisits favorableNextS27Before [] = 26 := by decide
  have hn : rawVisits favorableNextS27Before ([]++[.query 7]) = 3 := by decide
  have hz : (controlPenalty savedCref uniformQuoteError unitRoleUnused .next) favorableNextS27Before [] (.query 7) = (nextNormalPenalty favorableNextS27Before) := by
    simpa only [favorableNextS27Before,nextNormalPenalty] using AgentUCTNextExact.favorable_next_normal_root_quotes_exact 26 (by omega) 7 (by decide)
  unfold indexScore
  rw [hs,hp,hn,hz]
  simp only [BackupStat.mean]
  norm_num

theorem favorableNextS27D0Cmp0 : indexScore (7/5) (controlPenalty savedCref uniformQuoteError unitRoleUnused .next) favorableNextS27Before [] (.query 0) < indexScore (7/5) (controlPenalty savedCref uniformQuoteError unitRoleUnused .next) favorableNextS27Before [] (.query 1) := by
  rw [favorableNextS27D0I0,favorableNextS27D0I1]
  have hk := favorable_next_penalty_interval 26 (by omega)
  change nextNormalPenaltyLower ≤ nextNormalPenalty favorableNextS27Before ∧ nextNormalPenalty favorableNextS27Before ≤ nextNormalPenaltyUpper at hk
  have hm : ((0/1)/3)+(73370297/50000000)-(nextNormalPenalty favorableNextS27Before) < ((1/2)/4)+(63540533/50000000)-0 := by
    have h : ((0/1)/3)+(73370297/50000000)-nextNormalPenaltyLower < ((1/2)/4)+(63540533/50000000) := by norm_num [nextNormalPenaltyLower,savedCref,uniformQuoteError]
    linarith [hk.1]
  have h := index_strict_order_from_intervals ((1/2)/4) ((0/1)/3) 0 (nextNormalPenalty favorableNextS27Before) (63540533/50000000) (73370297/50000000)
    (treeBonus (7/5) 26 4) (treeBonus (7/5) 26 3)
    (trajectory_bonus_26_4).1 (trajectory_bonus_26_3).2 hm
  simpa only [treeIndex] using h

theorem favorableNextS27D0Cmp2 : indexScore (7/5) (controlPenalty savedCref uniformQuoteError unitRoleUnused .next) favorableNextS27Before [] (.query 2) ≤ indexScore (7/5) (controlPenalty savedCref uniformQuoteError unitRoleUnused .next) favorableNextS27Before [] (.query 1) := by
  rw [favorableNextS27D0I2,favorableNextS27D0I1]
  have hk := favorable_next_penalty_interval 26 (by omega)
  change nextNormalPenaltyLower ≤ nextNormalPenalty favorableNextS27Before ∧ nextNormalPenalty favorableNextS27Before ≤ nextNormalPenaltyUpper at hk
  have hm : ((0/1)/3)+(73370297/50000000)-(nextNormalPenalty favorableNextS27Before) < ((1/2)/4)+(63540533/50000000)-0 := by
    have h : ((0/1)/3)+(73370297/50000000)-nextNormalPenaltyLower < ((1/2)/4)+(63540533/50000000) := by norm_num [nextNormalPenaltyLower,savedCref,uniformQuoteError]
    linarith [hk.1]
  have h := index_weak_order_from_intervals ((1/2)/4) ((0/1)/3) 0 (nextNormalPenalty favorableNextS27Before) (63540533/50000000) (73370297/50000000)
    (treeBonus (7/5) 26 4) (treeBonus (7/5) 26 3)
    (trajectory_bonus_26_4).1 (trajectory_bonus_26_3).2 hm.le
  simpa only [treeIndex] using h

theorem favorableNextS27D0Cmp3 : indexScore (7/5) (controlPenalty savedCref uniformQuoteError unitRoleUnused .next) favorableNextS27Before [] (.query 3) ≤ indexScore (7/5) (controlPenalty savedCref uniformQuoteError unitRoleUnused .next) favorableNextS27Before [] (.query 1) := by
  rw [favorableNextS27D0I3,favorableNextS27D0I1]
  have hk := favorable_next_penalty_interval 26 (by omega)
  change nextNormalPenaltyLower ≤ nextNormalPenalty favorableNextS27Before ∧ nextNormalPenalty favorableNextS27Before ≤ nextNormalPenaltyUpper at hk
  have hm : ((0/1)/3)+(73370297/50000000)-(nextNormalPenalty favorableNextS27Before) < ((1/2)/4)+(63540533/50000000)-0 := by
    have h : ((0/1)/3)+(73370297/50000000)-nextNormalPenaltyLower < ((1/2)/4)+(63540533/50000000) := by norm_num [nextNormalPenaltyLower,savedCref,uniformQuoteError]
    linarith [hk.1]
  have h := index_weak_order_from_intervals ((1/2)/4) ((0/1)/3) 0 (nextNormalPenalty favorableNextS27Before) (63540533/50000000) (73370297/50000000)
    (treeBonus (7/5) 26 4) (treeBonus (7/5) 26 3)
    (trajectory_bonus_26_4).1 (trajectory_bonus_26_3).2 hm.le
  simpa only [treeIndex] using h

theorem favorableNextS27D0Cmp4 : indexScore (7/5) (controlPenalty savedCref uniformQuoteError unitRoleUnused .next) favorableNextS27Before [] (.query 4) ≤ indexScore (7/5) (controlPenalty savedCref uniformQuoteError unitRoleUnused .next) favorableNextS27Before [] (.query 1) := by
  rw [favorableNextS27D0I4,favorableNextS27D0I1]
  have hk := favorable_next_penalty_interval 26 (by omega)
  change nextNormalPenaltyLower ≤ nextNormalPenalty favorableNextS27Before ∧ nextNormalPenalty favorableNextS27Before ≤ nextNormalPenaltyUpper at hk
  have hm : ((0/1)/3)+(73370297/50000000)-(nextNormalPenalty favorableNextS27Before) < ((1/2)/4)+(63540533/50000000)-0 := by
    have h : ((0/1)/3)+(73370297/50000000)-nextNormalPenaltyLower < ((1/2)/4)+(63540533/50000000) := by norm_num [nextNormalPenaltyLower,savedCref,uniformQuoteError]
    linarith [hk.1]
  have h := index_weak_order_from_intervals ((1/2)/4) ((0/1)/3) 0 (nextNormalPenalty favorableNextS27Before) (63540533/50000000) (73370297/50000000)
    (treeBonus (7/5) 26 4) (treeBonus (7/5) 26 3)
    (trajectory_bonus_26_4).1 (trajectory_bonus_26_3).2 hm.le
  simpa only [treeIndex] using h

theorem favorableNextS27D0Cmp5 : indexScore (7/5) (controlPenalty savedCref uniformQuoteError unitRoleUnused .next) favorableNextS27Before [] (.query 5) ≤ indexScore (7/5) (controlPenalty savedCref uniformQuoteError unitRoleUnused .next) favorableNextS27Before [] (.query 1) := by
  rw [favorableNextS27D0I5,favorableNextS27D0I1]
  have hk := favorable_next_penalty_interval 26 (by omega)
  change nextNormalPenaltyLower ≤ nextNormalPenalty favorableNextS27Before ∧ nextNormalPenalty favorableNextS27Before ≤ nextNormalPenaltyUpper at hk
  have hm : ((6/5)/4)+(3177027/2500000)-(nextNormalPenalty favorableNextS27Before) < ((1/2)/4)+(63540533/50000000)-0 := by
    have h : ((6/5)/4)+(3177027/2500000)-nextNormalPenaltyLower < ((1/2)/4)+(63540533/50000000) := by norm_num [nextNormalPenaltyLower,savedCref,uniformQuoteError]
    linarith [hk.1]
  have h := index_weak_order_from_intervals ((1/2)/4) ((6/5)/4) 0 (nextNormalPenalty favorableNextS27Before) (63540533/50000000) (3177027/2500000)
    (treeBonus (7/5) 26 4) (treeBonus (7/5) 26 4)
    (trajectory_bonus_26_4).1 (trajectory_bonus_26_4).2 hm.le
  simpa only [treeIndex] using h

theorem favorableNextS27D0Cmp6 : indexScore (7/5) (controlPenalty savedCref uniformQuoteError unitRoleUnused .next) favorableNextS27Before [] (.query 6) ≤ indexScore (7/5) (controlPenalty savedCref uniformQuoteError unitRoleUnused .next) favorableNextS27Before [] (.query 1) := by
  rw [favorableNextS27D0I6,favorableNextS27D0I1]
  have hk := favorable_next_penalty_interval 26 (by omega)
  change nextNormalPenaltyLower ≤ nextNormalPenalty favorableNextS27Before ∧ nextNormalPenalty favorableNextS27Before ≤ nextNormalPenaltyUpper at hk
  have hm : ((0/1)/3)+(73370297/50000000)-(nextNormalPenalty favorableNextS27Before) < ((1/2)/4)+(63540533/50000000)-0 := by
    have h : ((0/1)/3)+(73370297/50000000)-nextNormalPenaltyLower < ((1/2)/4)+(63540533/50000000) := by norm_num [nextNormalPenaltyLower,savedCref,uniformQuoteError]
    linarith [hk.1]
  have h := index_weak_order_from_intervals ((1/2)/4) ((0/1)/3) 0 (nextNormalPenalty favorableNextS27Before) (63540533/50000000) (73370297/50000000)
    (treeBonus (7/5) 26 4) (treeBonus (7/5) 26 3)
    (trajectory_bonus_26_4).1 (trajectory_bonus_26_3).2 hm.le
  simpa only [treeIndex] using h

theorem favorableNextS27D0Cmp7 : indexScore (7/5) (controlPenalty savedCref uniformQuoteError unitRoleUnused .next) favorableNextS27Before [] (.query 7) ≤ indexScore (7/5) (controlPenalty savedCref uniformQuoteError unitRoleUnused .next) favorableNextS27Before [] (.query 1) := by
  rw [favorableNextS27D0I7,favorableNextS27D0I1]
  have hk := favorable_next_penalty_interval 26 (by omega)
  change nextNormalPenaltyLower ≤ nextNormalPenalty favorableNextS27Before ∧ nextNormalPenalty favorableNextS27Before ≤ nextNormalPenaltyUpper at hk
  have hm : ((0/1)/3)+(73370297/50000000)-(nextNormalPenalty favorableNextS27Before) < ((1/2)/4)+(63540533/50000000)-0 := by
    have h : ((0/1)/3)+(73370297/50000000)-nextNormalPenaltyLower < ((1/2)/4)+(63540533/50000000) := by norm_num [nextNormalPenaltyLower,savedCref,uniformQuoteError]
    linarith [hk.1]
  have h := index_weak_order_from_intervals ((1/2)/4) ((0/1)/3) 0 (nextNormalPenalty favorableNextS27Before) (63540533/50000000) (73370297/50000000)
    (treeBonus (7/5) 26 4) (treeBonus (7/5) 26 3)
    (trajectory_bonus_26_4).1 (trajectory_bonus_26_3).2 hm.le
  simpa only [treeIndex] using h

theorem favorableNextS27Choice0 : nativeFirstChoice (indexScore (7/5) (controlPenalty savedCref uniformQuoteError unitRoleUnused .next) favorableNextS27Before []) favorableNextS27Before [] = .query 1 := by
  apply visited_choice_from_ordered_certificate _ _ [] [.query 0] [.query 2,.query 3,.query 4,.query 5,.query 6,.query 7] (.query 1) (by decide)
  · intro a ha
    have ho : orderedLegalAvailable [] = [.query 0,.query 1,.query 2,.query 3,.query 4,.query 5,.query 6,.query 7] := by decide
    rw [ho] at ha
    simp only [List.mem_cons,List.not_mem_nil,or_false] at ha
    rcases ha with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> decide
  · intro a ha
    simp only [List.mem_cons,List.not_mem_nil,or_false] at ha
    rcases ha with rfl
    · exact favorableNextS27D0Cmp0
  · intro a ha
    simp only [List.mem_cons,List.not_mem_nil,or_false] at ha
    rcases ha with rfl | rfl | rfl | rfl | rfl | rfl
    · exact favorableNextS27D0Cmp2
    · exact favorableNextS27D0Cmp3
    · exact favorableNextS27D0Cmp4
    · exact favorableNextS27D0Cmp5
    · exact favorableNextS27D0Cmp6
    · exact favorableNextS27D0Cmp7

theorem favorableNextS27D1I0 : indexScore (7/5) (controlPenalty savedCref uniformQuoteError unitRoleUnused .next) favorableNextS27Before [.query 1] (.hydeRetriever 1) = treeIndex ((1/2)/1) (7/5) 0 4 1 := by
  have hs : replayBackup favorableNextS27Before emptyStatistics ([.query 1]++[.hydeRetriever 1]) = ⟨1,(1/2)⟩ := by
    rw [replayBackup_empty_closed_form]
    simp +decide [backedEvents,favorableNextS27Before,favorableNextProposal,favorableNextEvent1,favorableNextEvent2,favorableNextEvent3,favorableNextEvent4,favorableNextEvent5,favorableNextEvent6,favorableNextEvent7,favorableNextEvent8,favorableNextEvent9,favorableNextEvent10,favorableNextEvent11,favorableNextEvent12,favorableNextEvent13,favorableNextEvent14,favorableNextEvent15,favorableNextEvent16,favorableNextEvent17,favorableNextEvent18,favorableNextEvent19,favorableNextEvent20,favorableNextEvent21,favorableNextEvent22,favorableNextEvent23,favorableNextEvent24,favorableNextEvent25,favorableNextEvent26,taskReward]
    <;> norm_num
  have hp : rawVisits favorableNextS27Before [.query 1] = 4 := by decide
  have hn : rawVisits favorableNextS27Before ([.query 1]++[.hydeRetriever 1]) = 1 := by decide
  have hz : (controlPenalty savedCref uniformQuoteError unitRoleUnused .next) favorableNextS27Before [.query 1] (.hydeRetriever 1) = 0 := by
    apply control_penalty_empty_of_prior_terminal .next savedCref uniformQuoteError favorableNextS27Before [.query 1] (.hydeRetriever 1) 9 (by decide)
    · decide
    · decide
  unfold indexScore
  rw [hs,hp,hn,hz]
  simp only [BackupStat.mean]
  norm_num

theorem favorableNextS27D1I1 : indexScore (7/5) (controlPenalty savedCref uniformQuoteError unitRoleUnused .next) favorableNextS27Before [.query 1] (.hydeRetriever 0) = treeIndex ((0/1)/1) (7/5) 0 4 1 := by
  have hs : replayBackup favorableNextS27Before emptyStatistics ([.query 1]++[.hydeRetriever 0]) = ⟨1,(0/1)⟩ := by
    rw [replayBackup_empty_closed_form]
    simp +decide [backedEvents,favorableNextS27Before,favorableNextProposal,favorableNextEvent1,favorableNextEvent2,favorableNextEvent3,favorableNextEvent4,favorableNextEvent5,favorableNextEvent6,favorableNextEvent7,favorableNextEvent8,favorableNextEvent9,favorableNextEvent10,favorableNextEvent11,favorableNextEvent12,favorableNextEvent13,favorableNextEvent14,favorableNextEvent15,favorableNextEvent16,favorableNextEvent17,favorableNextEvent18,favorableNextEvent19,favorableNextEvent20,favorableNextEvent21,favorableNextEvent22,favorableNextEvent23,favorableNextEvent24,favorableNextEvent25,favorableNextEvent26,taskReward]
    <;> norm_num
  have hp : rawVisits favorableNextS27Before [.query 1] = 4 := by decide
  have hn : rawVisits favorableNextS27Before ([.query 1]++[.hydeRetriever 0]) = 1 := by decide
  have hz : (controlPenalty savedCref uniformQuoteError unitRoleUnused .next) favorableNextS27Before [.query 1] (.hydeRetriever 0) = 0 := by
    apply control_penalty_empty_of_prior_terminal .next savedCref uniformQuoteError favorableNextS27Before [.query 1] (.hydeRetriever 0) 1 (by decide)
    · decide
    · decide
  unfold indexScore
  rw [hs,hp,hn,hz]
  simp only [BackupStat.mean]
  norm_num

theorem favorableNextS27D1I2 : indexScore (7/5) (controlPenalty savedCref uniformQuoteError unitRoleUnused .next) favorableNextS27Before [.query 1] (.hydeRetriever 2) = treeIndex ((0/1)/1) (7/5) 0 4 1 := by
  have hs : replayBackup favorableNextS27Before emptyStatistics ([.query 1]++[.hydeRetriever 2]) = ⟨1,(0/1)⟩ := by
    rw [replayBackup_empty_closed_form]
    simp +decide [backedEvents,favorableNextS27Before,favorableNextProposal,favorableNextEvent1,favorableNextEvent2,favorableNextEvent3,favorableNextEvent4,favorableNextEvent5,favorableNextEvent6,favorableNextEvent7,favorableNextEvent8,favorableNextEvent9,favorableNextEvent10,favorableNextEvent11,favorableNextEvent12,favorableNextEvent13,favorableNextEvent14,favorableNextEvent15,favorableNextEvent16,favorableNextEvent17,favorableNextEvent18,favorableNextEvent19,favorableNextEvent20,favorableNextEvent21,favorableNextEvent22,favorableNextEvent23,favorableNextEvent24,favorableNextEvent25,favorableNextEvent26,taskReward]
    <;> norm_num
  have hp : rawVisits favorableNextS27Before [.query 1] = 4 := by decide
  have hn : rawVisits favorableNextS27Before ([.query 1]++[.hydeRetriever 2]) = 1 := by decide
  have hz : (controlPenalty savedCref uniformQuoteError unitRoleUnused .next) favorableNextS27Before [.query 1] (.hydeRetriever 2) = 0 := by
    apply control_penalty_empty_of_prior_terminal .next savedCref uniformQuoteError favorableNextS27Before [.query 1] (.hydeRetriever 2) 18 (by decide)
    · decide
    · decide
  unfold indexScore
  rw [hs,hp,hn,hz]
  simp only [BackupStat.mean]
  norm_num

theorem favorableNextS27D1Cmp1 : indexScore (7/5) (controlPenalty savedCref uniformQuoteError unitRoleUnused .next) favorableNextS27Before [.query 1] (.hydeRetriever 0) ≤ indexScore (7/5) (controlPenalty savedCref uniformQuoteError unitRoleUnused .next) favorableNextS27Before [.query 1] (.hydeRetriever 1) := by
  rw [favorableNextS27D1I1,favorableNextS27D1I0]
  have h := index_weak_order_from_intervals ((1/2)/1) ((0/1)/1) 0 0 (44402267/25000000) (88804541/50000000)
    (treeBonus (7/5) 4 1) (treeBonus (7/5) 4 1)
    (trajectory_bonus_4_1).1 (trajectory_bonus_4_1).2 (by norm_num)
  simpa only [treeIndex,sub_zero] using h

theorem favorableNextS27D1Cmp2 : indexScore (7/5) (controlPenalty savedCref uniformQuoteError unitRoleUnused .next) favorableNextS27Before [.query 1] (.hydeRetriever 2) ≤ indexScore (7/5) (controlPenalty savedCref uniformQuoteError unitRoleUnused .next) favorableNextS27Before [.query 1] (.hydeRetriever 1) := by
  rw [favorableNextS27D1I2,favorableNextS27D1I0]
  have h := index_weak_order_from_intervals ((1/2)/1) ((0/1)/1) 0 0 (44402267/25000000) (88804541/50000000)
    (treeBonus (7/5) 4 1) (treeBonus (7/5) 4 1)
    (trajectory_bonus_4_1).1 (trajectory_bonus_4_1).2 (by norm_num)
  simpa only [treeIndex,sub_zero] using h

theorem favorableNextS27Choice1 : nativeFirstChoice (indexScore (7/5) (controlPenalty savedCref uniformQuoteError unitRoleUnused .next) favorableNextS27Before [.query 1]) favorableNextS27Before [.query 1] = .hydeRetriever 1 := by
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
    · exact favorableNextS27D1Cmp1
    · exact favorableNextS27D1Cmp2

theorem favorableNextS27ActualEvent : nativeEvent budgetTape (7/5) (controlPenalty savedCref uniformQuoteError unitRoleUnused .next)
    (taskReward false (2/5) (1/2)) favorableNextS27Before = favorableNextEvent27 := by
  have hs0 := native_select_existing_step budgetTape (7/5) (controlPenalty savedCref uniformQuoteError unitRoleUnused .next) favorableNextS27Before 8 [] (.query 1)
    (by decide) (by decide) favorableNextS27Choice0
  have hs1 := native_select_existing_step budgetTape (7/5) (controlPenalty savedCref uniformQuoteError unitRoleUnused .next) favorableNextS27Before 7 [.query 1] (.hydeRetriever 1)
    (by decide) (by decide) favorableNextS27Choice1
  have hnew := native_select_new_step budgetTape (7/5) (controlPenalty savedCref uniformQuoteError unitRoleUnused .next) favorableNextS27Before 6 [.query 1,.hydeRetriever 1]
    [.selection 1,.selection 2,.selection 3,.selection 0] (.selection 0) (by decide) (by decide) (by decide) (by decide)
  have hs : nativeSelect budgetTape (7/5) (controlPenalty savedCref uniformQuoteError unitRoleUnused .next) favorableNextS27Before 9 [] = [.query 1,.hydeRetriever 1,.selection 0] := by
    rw [hs0]
    change nativeSelect budgetTape (7/5) (controlPenalty savedCref uniformQuoteError unitRoleUnused .next) favorableNextS27Before 8 [.query 1] = _
    rw [hs1]
    change nativeSelect budgetTape (7/5) (controlPenalty savedCref uniformQuoteError unitRoleUnused .next) favorableNextS27Before 7 [.query 1,.hydeRetriever 1] = _
    rw [hnew] <;> rfl
  have hr : repairedRollout budgetTape favorableNextS27Before 9 [.query 1,.hydeRetriever 1,.selection 0] = [.query 1,.hydeRetriever 1,.selection 0,.width 1,.stop,.reranker 0,.topm 0,.context 0,.answer 0] := by decide
  simp only [nativeEvent,hs,hr]
  rfl

def favorableNextS28Before := favorableNextProposal.take 27

theorem favorableNextS28D0I0 : indexScore (7/5) (controlPenalty savedCref uniformQuoteError unitRoleUnused .next) favorableNextS28Before [] (.query 0) = treeIndex ((0/1)/3) (7/5) (nextNormalPenalty favorableNextS28Before) 27 3 := by
  have hs : replayBackup favorableNextS28Before emptyStatistics ([]++[.query 0]) = ⟨3,(0/1)⟩ := by
    rw [replayBackup_empty_closed_form]
    simp +decide [backedEvents,favorableNextS28Before,favorableNextProposal,favorableNextEvent1,favorableNextEvent2,favorableNextEvent3,favorableNextEvent4,favorableNextEvent5,favorableNextEvent6,favorableNextEvent7,favorableNextEvent8,favorableNextEvent9,favorableNextEvent10,favorableNextEvent11,favorableNextEvent12,favorableNextEvent13,favorableNextEvent14,favorableNextEvent15,favorableNextEvent16,favorableNextEvent17,favorableNextEvent18,favorableNextEvent19,favorableNextEvent20,favorableNextEvent21,favorableNextEvent22,favorableNextEvent23,favorableNextEvent24,favorableNextEvent25,favorableNextEvent26,favorableNextEvent27,taskReward]
    <;> norm_num
  have hp : rawVisits favorableNextS28Before [] = 27 := by decide
  have hn : rawVisits favorableNextS28Before ([]++[.query 0]) = 3 := by decide
  have hz : (controlPenalty savedCref uniformQuoteError unitRoleUnused .next) favorableNextS28Before [] (.query 0) = (nextNormalPenalty favorableNextS28Before) := by
    simpa only [favorableNextS28Before,nextNormalPenalty] using AgentUCTNextExact.favorable_next_normal_root_quotes_exact 27 (by omega) 0 (by decide)
  unfold indexScore
  rw [hs,hp,hn,hz]
  simp only [BackupStat.mean]
  norm_num

theorem favorableNextS28D0I1 : indexScore (7/5) (controlPenalty savedCref uniformQuoteError unitRoleUnused .next) favorableNextS28Before [] (.query 1) = treeIndex ((1/1)/5) (7/5) 0 27 5 := by
  have hs : replayBackup favorableNextS28Before emptyStatistics ([]++[.query 1]) = ⟨5,(1/1)⟩ := by
    rw [replayBackup_empty_closed_form]
    simp +decide [backedEvents,favorableNextS28Before,favorableNextProposal,favorableNextEvent1,favorableNextEvent2,favorableNextEvent3,favorableNextEvent4,favorableNextEvent5,favorableNextEvent6,favorableNextEvent7,favorableNextEvent8,favorableNextEvent9,favorableNextEvent10,favorableNextEvent11,favorableNextEvent12,favorableNextEvent13,favorableNextEvent14,favorableNextEvent15,favorableNextEvent16,favorableNextEvent17,favorableNextEvent18,favorableNextEvent19,favorableNextEvent20,favorableNextEvent21,favorableNextEvent22,favorableNextEvent23,favorableNextEvent24,favorableNextEvent25,favorableNextEvent26,favorableNextEvent27,taskReward]
    <;> norm_num
  have hp : rawVisits favorableNextS28Before [] = 27 := by decide
  have hn : rawVisits favorableNextS28Before ([]++[.query 1]) = 5 := by decide
  have hz : (controlPenalty savedCref uniformQuoteError unitRoleUnused .next) favorableNextS28Before [] (.query 1) = 0 := by
    apply control_penalty_empty_suffix
    exact AgentUCTNextExact.favorable_next_hyde_root_suffix_empty 27 (by omega)
  unfold indexScore
  rw [hs,hp,hn,hz]
  simp only [BackupStat.mean]
  norm_num

theorem favorableNextS28D0I2 : indexScore (7/5) (controlPenalty savedCref uniformQuoteError unitRoleUnused .next) favorableNextS28Before [] (.query 2) = treeIndex ((0/1)/3) (7/5) (nextNormalPenalty favorableNextS28Before) 27 3 := by
  have hs : replayBackup favorableNextS28Before emptyStatistics ([]++[.query 2]) = ⟨3,(0/1)⟩ := by
    rw [replayBackup_empty_closed_form]
    simp +decide [backedEvents,favorableNextS28Before,favorableNextProposal,favorableNextEvent1,favorableNextEvent2,favorableNextEvent3,favorableNextEvent4,favorableNextEvent5,favorableNextEvent6,favorableNextEvent7,favorableNextEvent8,favorableNextEvent9,favorableNextEvent10,favorableNextEvent11,favorableNextEvent12,favorableNextEvent13,favorableNextEvent14,favorableNextEvent15,favorableNextEvent16,favorableNextEvent17,favorableNextEvent18,favorableNextEvent19,favorableNextEvent20,favorableNextEvent21,favorableNextEvent22,favorableNextEvent23,favorableNextEvent24,favorableNextEvent25,favorableNextEvent26,favorableNextEvent27,taskReward]
    <;> norm_num
  have hp : rawVisits favorableNextS28Before [] = 27 := by decide
  have hn : rawVisits favorableNextS28Before ([]++[.query 2]) = 3 := by decide
  have hz : (controlPenalty savedCref uniformQuoteError unitRoleUnused .next) favorableNextS28Before [] (.query 2) = (nextNormalPenalty favorableNextS28Before) := by
    simpa only [favorableNextS28Before,nextNormalPenalty] using AgentUCTNextExact.favorable_next_normal_root_quotes_exact 27 (by omega) 2 (by decide)
  unfold indexScore
  rw [hs,hp,hn,hz]
  simp only [BackupStat.mean]
  norm_num

theorem favorableNextS28D0I3 : indexScore (7/5) (controlPenalty savedCref uniformQuoteError unitRoleUnused .next) favorableNextS28Before [] (.query 3) = treeIndex ((0/1)/3) (7/5) (nextNormalPenalty favorableNextS28Before) 27 3 := by
  have hs : replayBackup favorableNextS28Before emptyStatistics ([]++[.query 3]) = ⟨3,(0/1)⟩ := by
    rw [replayBackup_empty_closed_form]
    simp +decide [backedEvents,favorableNextS28Before,favorableNextProposal,favorableNextEvent1,favorableNextEvent2,favorableNextEvent3,favorableNextEvent4,favorableNextEvent5,favorableNextEvent6,favorableNextEvent7,favorableNextEvent8,favorableNextEvent9,favorableNextEvent10,favorableNextEvent11,favorableNextEvent12,favorableNextEvent13,favorableNextEvent14,favorableNextEvent15,favorableNextEvent16,favorableNextEvent17,favorableNextEvent18,favorableNextEvent19,favorableNextEvent20,favorableNextEvent21,favorableNextEvent22,favorableNextEvent23,favorableNextEvent24,favorableNextEvent25,favorableNextEvent26,favorableNextEvent27,taskReward]
    <;> norm_num
  have hp : rawVisits favorableNextS28Before [] = 27 := by decide
  have hn : rawVisits favorableNextS28Before ([]++[.query 3]) = 3 := by decide
  have hz : (controlPenalty savedCref uniformQuoteError unitRoleUnused .next) favorableNextS28Before [] (.query 3) = (nextNormalPenalty favorableNextS28Before) := by
    simpa only [favorableNextS28Before,nextNormalPenalty] using AgentUCTNextExact.favorable_next_normal_root_quotes_exact 27 (by omega) 3 (by decide)
  unfold indexScore
  rw [hs,hp,hn,hz]
  simp only [BackupStat.mean]
  norm_num

theorem favorableNextS28D0I4 : indexScore (7/5) (controlPenalty savedCref uniformQuoteError unitRoleUnused .next) favorableNextS28Before [] (.query 4) = treeIndex ((0/1)/3) (7/5) (nextNormalPenalty favorableNextS28Before) 27 3 := by
  have hs : replayBackup favorableNextS28Before emptyStatistics ([]++[.query 4]) = ⟨3,(0/1)⟩ := by
    rw [replayBackup_empty_closed_form]
    simp +decide [backedEvents,favorableNextS28Before,favorableNextProposal,favorableNextEvent1,favorableNextEvent2,favorableNextEvent3,favorableNextEvent4,favorableNextEvent5,favorableNextEvent6,favorableNextEvent7,favorableNextEvent8,favorableNextEvent9,favorableNextEvent10,favorableNextEvent11,favorableNextEvent12,favorableNextEvent13,favorableNextEvent14,favorableNextEvent15,favorableNextEvent16,favorableNextEvent17,favorableNextEvent18,favorableNextEvent19,favorableNextEvent20,favorableNextEvent21,favorableNextEvent22,favorableNextEvent23,favorableNextEvent24,favorableNextEvent25,favorableNextEvent26,favorableNextEvent27,taskReward]
    <;> norm_num
  have hp : rawVisits favorableNextS28Before [] = 27 := by decide
  have hn : rawVisits favorableNextS28Before ([]++[.query 4]) = 3 := by decide
  have hz : (controlPenalty savedCref uniformQuoteError unitRoleUnused .next) favorableNextS28Before [] (.query 4) = (nextNormalPenalty favorableNextS28Before) := by
    simpa only [favorableNextS28Before,nextNormalPenalty] using AgentUCTNextExact.favorable_next_normal_root_quotes_exact 27 (by omega) 4 (by decide)
  unfold indexScore
  rw [hs,hp,hn,hz]
  simp only [BackupStat.mean]
  norm_num

theorem favorableNextS28D0I5 : indexScore (7/5) (controlPenalty savedCref uniformQuoteError unitRoleUnused .next) favorableNextS28Before [] (.query 5) = treeIndex ((6/5)/4) (7/5) (nextNormalPenalty favorableNextS28Before) 27 4 := by
  have hs : replayBackup favorableNextS28Before emptyStatistics ([]++[.query 5]) = ⟨4,(6/5)⟩ := by
    rw [replayBackup_empty_closed_form]
    simp +decide [backedEvents,favorableNextS28Before,favorableNextProposal,favorableNextEvent1,favorableNextEvent2,favorableNextEvent3,favorableNextEvent4,favorableNextEvent5,favorableNextEvent6,favorableNextEvent7,favorableNextEvent8,favorableNextEvent9,favorableNextEvent10,favorableNextEvent11,favorableNextEvent12,favorableNextEvent13,favorableNextEvent14,favorableNextEvent15,favorableNextEvent16,favorableNextEvent17,favorableNextEvent18,favorableNextEvent19,favorableNextEvent20,favorableNextEvent21,favorableNextEvent22,favorableNextEvent23,favorableNextEvent24,favorableNextEvent25,favorableNextEvent26,favorableNextEvent27,taskReward]
    <;> norm_num
  have hp : rawVisits favorableNextS28Before [] = 27 := by decide
  have hn : rawVisits favorableNextS28Before ([]++[.query 5]) = 4 := by decide
  have hz : (controlPenalty savedCref uniformQuoteError unitRoleUnused .next) favorableNextS28Before [] (.query 5) = (nextNormalPenalty favorableNextS28Before) := by
    simpa only [favorableNextS28Before,nextNormalPenalty] using AgentUCTNextExact.favorable_next_normal_root_quotes_exact 27 (by omega) 5 (by decide)
  unfold indexScore
  rw [hs,hp,hn,hz]
  simp only [BackupStat.mean]
  norm_num

theorem favorableNextS28D0I6 : indexScore (7/5) (controlPenalty savedCref uniformQuoteError unitRoleUnused .next) favorableNextS28Before [] (.query 6) = treeIndex ((0/1)/3) (7/5) (nextNormalPenalty favorableNextS28Before) 27 3 := by
  have hs : replayBackup favorableNextS28Before emptyStatistics ([]++[.query 6]) = ⟨3,(0/1)⟩ := by
    rw [replayBackup_empty_closed_form]
    simp +decide [backedEvents,favorableNextS28Before,favorableNextProposal,favorableNextEvent1,favorableNextEvent2,favorableNextEvent3,favorableNextEvent4,favorableNextEvent5,favorableNextEvent6,favorableNextEvent7,favorableNextEvent8,favorableNextEvent9,favorableNextEvent10,favorableNextEvent11,favorableNextEvent12,favorableNextEvent13,favorableNextEvent14,favorableNextEvent15,favorableNextEvent16,favorableNextEvent17,favorableNextEvent18,favorableNextEvent19,favorableNextEvent20,favorableNextEvent21,favorableNextEvent22,favorableNextEvent23,favorableNextEvent24,favorableNextEvent25,favorableNextEvent26,favorableNextEvent27,taskReward]
    <;> norm_num
  have hp : rawVisits favorableNextS28Before [] = 27 := by decide
  have hn : rawVisits favorableNextS28Before ([]++[.query 6]) = 3 := by decide
  have hz : (controlPenalty savedCref uniformQuoteError unitRoleUnused .next) favorableNextS28Before [] (.query 6) = (nextNormalPenalty favorableNextS28Before) := by
    simpa only [favorableNextS28Before,nextNormalPenalty] using AgentUCTNextExact.favorable_next_normal_root_quotes_exact 27 (by omega) 6 (by decide)
  unfold indexScore
  rw [hs,hp,hn,hz]
  simp only [BackupStat.mean]
  norm_num

theorem favorableNextS28D0I7 : indexScore (7/5) (controlPenalty savedCref uniformQuoteError unitRoleUnused .next) favorableNextS28Before [] (.query 7) = treeIndex ((0/1)/3) (7/5) (nextNormalPenalty favorableNextS28Before) 27 3 := by
  have hs : replayBackup favorableNextS28Before emptyStatistics ([]++[.query 7]) = ⟨3,(0/1)⟩ := by
    rw [replayBackup_empty_closed_form]
    simp +decide [backedEvents,favorableNextS28Before,favorableNextProposal,favorableNextEvent1,favorableNextEvent2,favorableNextEvent3,favorableNextEvent4,favorableNextEvent5,favorableNextEvent6,favorableNextEvent7,favorableNextEvent8,favorableNextEvent9,favorableNextEvent10,favorableNextEvent11,favorableNextEvent12,favorableNextEvent13,favorableNextEvent14,favorableNextEvent15,favorableNextEvent16,favorableNextEvent17,favorableNextEvent18,favorableNextEvent19,favorableNextEvent20,favorableNextEvent21,favorableNextEvent22,favorableNextEvent23,favorableNextEvent24,favorableNextEvent25,favorableNextEvent26,favorableNextEvent27,taskReward]
    <;> norm_num
  have hp : rawVisits favorableNextS28Before [] = 27 := by decide
  have hn : rawVisits favorableNextS28Before ([]++[.query 7]) = 3 := by decide
  have hz : (controlPenalty savedCref uniformQuoteError unitRoleUnused .next) favorableNextS28Before [] (.query 7) = (nextNormalPenalty favorableNextS28Before) := by
    simpa only [favorableNextS28Before,nextNormalPenalty] using AgentUCTNextExact.favorable_next_normal_root_quotes_exact 27 (by omega) 7 (by decide)
  unfold indexScore
  rw [hs,hp,hn,hz]
  simp only [BackupStat.mean]
  norm_num

theorem favorableNextS28D0Cmp0 : indexScore (7/5) (controlPenalty savedCref uniformQuoteError unitRoleUnused .next) favorableNextS28Before [] (.query 0) < indexScore (7/5) (controlPenalty savedCref uniformQuoteError unitRoleUnused .next) favorableNextS28Before [] (.query 1) := by
  rw [favorableNextS28D0I0,favorableNextS28D0I1]
  have hk := favorable_next_penalty_interval 27 (by omega)
  change nextNormalPenaltyLower ≤ nextNormalPenalty favorableNextS28Before ∧ nextNormalPenalty favorableNextS28Before ≤ nextNormalPenaltyUpper at hk
  have hm : ((0/1)/3)+(73773987/50000000)-(nextNormalPenalty favorableNextS28Before) < ((1/1)/5)+(57145081/50000000)-0 := by
    have h : ((0/1)/3)+(73773987/50000000)-nextNormalPenaltyLower < ((1/1)/5)+(57145081/50000000) := by norm_num [nextNormalPenaltyLower,savedCref,uniformQuoteError]
    linarith [hk.1]
  have h := index_strict_order_from_intervals ((1/1)/5) ((0/1)/3) 0 (nextNormalPenalty favorableNextS28Before) (57145081/50000000) (73773987/50000000)
    (treeBonus (7/5) 27 5) (treeBonus (7/5) 27 3)
    (trajectory_bonus_27_5).1 (trajectory_bonus_27_3).2 hm
  simpa only [treeIndex] using h

theorem favorableNextS28D0Cmp2 : indexScore (7/5) (controlPenalty savedCref uniformQuoteError unitRoleUnused .next) favorableNextS28Before [] (.query 2) ≤ indexScore (7/5) (controlPenalty savedCref uniformQuoteError unitRoleUnused .next) favorableNextS28Before [] (.query 1) := by
  rw [favorableNextS28D0I2,favorableNextS28D0I1]
  have hk := favorable_next_penalty_interval 27 (by omega)
  change nextNormalPenaltyLower ≤ nextNormalPenalty favorableNextS28Before ∧ nextNormalPenalty favorableNextS28Before ≤ nextNormalPenaltyUpper at hk
  have hm : ((0/1)/3)+(73773987/50000000)-(nextNormalPenalty favorableNextS28Before) < ((1/1)/5)+(57145081/50000000)-0 := by
    have h : ((0/1)/3)+(73773987/50000000)-nextNormalPenaltyLower < ((1/1)/5)+(57145081/50000000) := by norm_num [nextNormalPenaltyLower,savedCref,uniformQuoteError]
    linarith [hk.1]
  have h := index_weak_order_from_intervals ((1/1)/5) ((0/1)/3) 0 (nextNormalPenalty favorableNextS28Before) (57145081/50000000) (73773987/50000000)
    (treeBonus (7/5) 27 5) (treeBonus (7/5) 27 3)
    (trajectory_bonus_27_5).1 (trajectory_bonus_27_3).2 hm.le
  simpa only [treeIndex] using h

theorem favorableNextS28D0Cmp3 : indexScore (7/5) (controlPenalty savedCref uniformQuoteError unitRoleUnused .next) favorableNextS28Before [] (.query 3) ≤ indexScore (7/5) (controlPenalty savedCref uniformQuoteError unitRoleUnused .next) favorableNextS28Before [] (.query 1) := by
  rw [favorableNextS28D0I3,favorableNextS28D0I1]
  have hk := favorable_next_penalty_interval 27 (by omega)
  change nextNormalPenaltyLower ≤ nextNormalPenalty favorableNextS28Before ∧ nextNormalPenalty favorableNextS28Before ≤ nextNormalPenaltyUpper at hk
  have hm : ((0/1)/3)+(73773987/50000000)-(nextNormalPenalty favorableNextS28Before) < ((1/1)/5)+(57145081/50000000)-0 := by
    have h : ((0/1)/3)+(73773987/50000000)-nextNormalPenaltyLower < ((1/1)/5)+(57145081/50000000) := by norm_num [nextNormalPenaltyLower,savedCref,uniformQuoteError]
    linarith [hk.1]
  have h := index_weak_order_from_intervals ((1/1)/5) ((0/1)/3) 0 (nextNormalPenalty favorableNextS28Before) (57145081/50000000) (73773987/50000000)
    (treeBonus (7/5) 27 5) (treeBonus (7/5) 27 3)
    (trajectory_bonus_27_5).1 (trajectory_bonus_27_3).2 hm.le
  simpa only [treeIndex] using h

theorem favorableNextS28D0Cmp4 : indexScore (7/5) (controlPenalty savedCref uniformQuoteError unitRoleUnused .next) favorableNextS28Before [] (.query 4) ≤ indexScore (7/5) (controlPenalty savedCref uniformQuoteError unitRoleUnused .next) favorableNextS28Before [] (.query 1) := by
  rw [favorableNextS28D0I4,favorableNextS28D0I1]
  have hk := favorable_next_penalty_interval 27 (by omega)
  change nextNormalPenaltyLower ≤ nextNormalPenalty favorableNextS28Before ∧ nextNormalPenalty favorableNextS28Before ≤ nextNormalPenaltyUpper at hk
  have hm : ((0/1)/3)+(73773987/50000000)-(nextNormalPenalty favorableNextS28Before) < ((1/1)/5)+(57145081/50000000)-0 := by
    have h : ((0/1)/3)+(73773987/50000000)-nextNormalPenaltyLower < ((1/1)/5)+(57145081/50000000) := by norm_num [nextNormalPenaltyLower,savedCref,uniformQuoteError]
    linarith [hk.1]
  have h := index_weak_order_from_intervals ((1/1)/5) ((0/1)/3) 0 (nextNormalPenalty favorableNextS28Before) (57145081/50000000) (73773987/50000000)
    (treeBonus (7/5) 27 5) (treeBonus (7/5) 27 3)
    (trajectory_bonus_27_5).1 (trajectory_bonus_27_3).2 hm.le
  simpa only [treeIndex] using h

theorem favorableNextS28D0Cmp5 : indexScore (7/5) (controlPenalty savedCref uniformQuoteError unitRoleUnused .next) favorableNextS28Before [] (.query 5) ≤ indexScore (7/5) (controlPenalty savedCref uniformQuoteError unitRoleUnused .next) favorableNextS28Before [] (.query 1) := by
  rw [favorableNextS28D0I5,favorableNextS28D0I1]
  have hk := favorable_next_penalty_interval 27 (by omega)
  change nextNormalPenaltyLower ≤ nextNormalPenalty favorableNextS28Before ∧ nextNormalPenalty favorableNextS28Before ≤ nextNormalPenaltyUpper at hk
  have hm : ((6/5)/4)+(15972537/12500000)-(nextNormalPenalty favorableNextS28Before) < ((1/1)/5)+(57145081/50000000)-0 := by
    have h : ((6/5)/4)+(15972537/12500000)-nextNormalPenaltyLower < ((1/1)/5)+(57145081/50000000) := by norm_num [nextNormalPenaltyLower,savedCref,uniformQuoteError]
    linarith [hk.1]
  have h := index_weak_order_from_intervals ((1/1)/5) ((6/5)/4) 0 (nextNormalPenalty favorableNextS28Before) (57145081/50000000) (15972537/12500000)
    (treeBonus (7/5) 27 5) (treeBonus (7/5) 27 4)
    (trajectory_bonus_27_5).1 (trajectory_bonus_27_4).2 hm.le
  simpa only [treeIndex] using h

theorem favorableNextS28D0Cmp6 : indexScore (7/5) (controlPenalty savedCref uniformQuoteError unitRoleUnused .next) favorableNextS28Before [] (.query 6) ≤ indexScore (7/5) (controlPenalty savedCref uniformQuoteError unitRoleUnused .next) favorableNextS28Before [] (.query 1) := by
  rw [favorableNextS28D0I6,favorableNextS28D0I1]
  have hk := favorable_next_penalty_interval 27 (by omega)
  change nextNormalPenaltyLower ≤ nextNormalPenalty favorableNextS28Before ∧ nextNormalPenalty favorableNextS28Before ≤ nextNormalPenaltyUpper at hk
  have hm : ((0/1)/3)+(73773987/50000000)-(nextNormalPenalty favorableNextS28Before) < ((1/1)/5)+(57145081/50000000)-0 := by
    have h : ((0/1)/3)+(73773987/50000000)-nextNormalPenaltyLower < ((1/1)/5)+(57145081/50000000) := by norm_num [nextNormalPenaltyLower,savedCref,uniformQuoteError]
    linarith [hk.1]
  have h := index_weak_order_from_intervals ((1/1)/5) ((0/1)/3) 0 (nextNormalPenalty favorableNextS28Before) (57145081/50000000) (73773987/50000000)
    (treeBonus (7/5) 27 5) (treeBonus (7/5) 27 3)
    (trajectory_bonus_27_5).1 (trajectory_bonus_27_3).2 hm.le
  simpa only [treeIndex] using h

theorem favorableNextS28D0Cmp7 : indexScore (7/5) (controlPenalty savedCref uniformQuoteError unitRoleUnused .next) favorableNextS28Before [] (.query 7) ≤ indexScore (7/5) (controlPenalty savedCref uniformQuoteError unitRoleUnused .next) favorableNextS28Before [] (.query 1) := by
  rw [favorableNextS28D0I7,favorableNextS28D0I1]
  have hk := favorable_next_penalty_interval 27 (by omega)
  change nextNormalPenaltyLower ≤ nextNormalPenalty favorableNextS28Before ∧ nextNormalPenalty favorableNextS28Before ≤ nextNormalPenaltyUpper at hk
  have hm : ((0/1)/3)+(73773987/50000000)-(nextNormalPenalty favorableNextS28Before) < ((1/1)/5)+(57145081/50000000)-0 := by
    have h : ((0/1)/3)+(73773987/50000000)-nextNormalPenaltyLower < ((1/1)/5)+(57145081/50000000) := by norm_num [nextNormalPenaltyLower,savedCref,uniformQuoteError]
    linarith [hk.1]
  have h := index_weak_order_from_intervals ((1/1)/5) ((0/1)/3) 0 (nextNormalPenalty favorableNextS28Before) (57145081/50000000) (73773987/50000000)
    (treeBonus (7/5) 27 5) (treeBonus (7/5) 27 3)
    (trajectory_bonus_27_5).1 (trajectory_bonus_27_3).2 hm.le
  simpa only [treeIndex] using h

theorem favorableNextS28Choice0 : nativeFirstChoice (indexScore (7/5) (controlPenalty savedCref uniformQuoteError unitRoleUnused .next) favorableNextS28Before []) favorableNextS28Before [] = .query 1 := by
  apply visited_choice_from_ordered_certificate _ _ [] [.query 0] [.query 2,.query 3,.query 4,.query 5,.query 6,.query 7] (.query 1) (by decide)
  · intro a ha
    have ho : orderedLegalAvailable [] = [.query 0,.query 1,.query 2,.query 3,.query 4,.query 5,.query 6,.query 7] := by decide
    rw [ho] at ha
    simp only [List.mem_cons,List.not_mem_nil,or_false] at ha
    rcases ha with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> decide
  · intro a ha
    simp only [List.mem_cons,List.not_mem_nil,or_false] at ha
    rcases ha with rfl
    · exact favorableNextS28D0Cmp0
  · intro a ha
    simp only [List.mem_cons,List.not_mem_nil,or_false] at ha
    rcases ha with rfl | rfl | rfl | rfl | rfl | rfl
    · exact favorableNextS28D0Cmp2
    · exact favorableNextS28D0Cmp3
    · exact favorableNextS28D0Cmp4
    · exact favorableNextS28D0Cmp5
    · exact favorableNextS28D0Cmp6
    · exact favorableNextS28D0Cmp7

theorem favorableNextS28D1I0 : indexScore (7/5) (controlPenalty savedCref uniformQuoteError unitRoleUnused .next) favorableNextS28Before [.query 1] (.hydeRetriever 1) = treeIndex ((1/1)/2) (7/5) 0 5 2 := by
  have hs : replayBackup favorableNextS28Before emptyStatistics ([.query 1]++[.hydeRetriever 1]) = ⟨2,(1/1)⟩ := by
    rw [replayBackup_empty_closed_form]
    simp +decide [backedEvents,favorableNextS28Before,favorableNextProposal,favorableNextEvent1,favorableNextEvent2,favorableNextEvent3,favorableNextEvent4,favorableNextEvent5,favorableNextEvent6,favorableNextEvent7,favorableNextEvent8,favorableNextEvent9,favorableNextEvent10,favorableNextEvent11,favorableNextEvent12,favorableNextEvent13,favorableNextEvent14,favorableNextEvent15,favorableNextEvent16,favorableNextEvent17,favorableNextEvent18,favorableNextEvent19,favorableNextEvent20,favorableNextEvent21,favorableNextEvent22,favorableNextEvent23,favorableNextEvent24,favorableNextEvent25,favorableNextEvent26,favorableNextEvent27,taskReward]
    <;> norm_num
  have hp : rawVisits favorableNextS28Before [.query 1] = 5 := by decide
  have hn : rawVisits favorableNextS28Before ([.query 1]++[.hydeRetriever 1]) = 2 := by decide
  have hz : (controlPenalty savedCref uniformQuoteError unitRoleUnused .next) favorableNextS28Before [.query 1] (.hydeRetriever 1) = 0 := by
    apply control_penalty_empty_of_prior_terminal .next savedCref uniformQuoteError favorableNextS28Before [.query 1] (.hydeRetriever 1) 9 (by decide)
    · decide
    · decide
  unfold indexScore
  rw [hs,hp,hn,hz]
  simp only [BackupStat.mean]
  norm_num

theorem favorableNextS28D1I1 : indexScore (7/5) (controlPenalty savedCref uniformQuoteError unitRoleUnused .next) favorableNextS28Before [.query 1] (.hydeRetriever 0) = treeIndex ((0/1)/1) (7/5) 0 5 1 := by
  have hs : replayBackup favorableNextS28Before emptyStatistics ([.query 1]++[.hydeRetriever 0]) = ⟨1,(0/1)⟩ := by
    rw [replayBackup_empty_closed_form]
    simp +decide [backedEvents,favorableNextS28Before,favorableNextProposal,favorableNextEvent1,favorableNextEvent2,favorableNextEvent3,favorableNextEvent4,favorableNextEvent5,favorableNextEvent6,favorableNextEvent7,favorableNextEvent8,favorableNextEvent9,favorableNextEvent10,favorableNextEvent11,favorableNextEvent12,favorableNextEvent13,favorableNextEvent14,favorableNextEvent15,favorableNextEvent16,favorableNextEvent17,favorableNextEvent18,favorableNextEvent19,favorableNextEvent20,favorableNextEvent21,favorableNextEvent22,favorableNextEvent23,favorableNextEvent24,favorableNextEvent25,favorableNextEvent26,favorableNextEvent27,taskReward]
    <;> norm_num
  have hp : rawVisits favorableNextS28Before [.query 1] = 5 := by decide
  have hn : rawVisits favorableNextS28Before ([.query 1]++[.hydeRetriever 0]) = 1 := by decide
  have hz : (controlPenalty savedCref uniformQuoteError unitRoleUnused .next) favorableNextS28Before [.query 1] (.hydeRetriever 0) = 0 := by
    apply control_penalty_empty_of_prior_terminal .next savedCref uniformQuoteError favorableNextS28Before [.query 1] (.hydeRetriever 0) 1 (by decide)
    · decide
    · decide
  unfold indexScore
  rw [hs,hp,hn,hz]
  simp only [BackupStat.mean]
  norm_num

theorem favorableNextS28D1I2 : indexScore (7/5) (controlPenalty savedCref uniformQuoteError unitRoleUnused .next) favorableNextS28Before [.query 1] (.hydeRetriever 2) = treeIndex ((0/1)/1) (7/5) 0 5 1 := by
  have hs : replayBackup favorableNextS28Before emptyStatistics ([.query 1]++[.hydeRetriever 2]) = ⟨1,(0/1)⟩ := by
    rw [replayBackup_empty_closed_form]
    simp +decide [backedEvents,favorableNextS28Before,favorableNextProposal,favorableNextEvent1,favorableNextEvent2,favorableNextEvent3,favorableNextEvent4,favorableNextEvent5,favorableNextEvent6,favorableNextEvent7,favorableNextEvent8,favorableNextEvent9,favorableNextEvent10,favorableNextEvent11,favorableNextEvent12,favorableNextEvent13,favorableNextEvent14,favorableNextEvent15,favorableNextEvent16,favorableNextEvent17,favorableNextEvent18,favorableNextEvent19,favorableNextEvent20,favorableNextEvent21,favorableNextEvent22,favorableNextEvent23,favorableNextEvent24,favorableNextEvent25,favorableNextEvent26,favorableNextEvent27,taskReward]
    <;> norm_num
  have hp : rawVisits favorableNextS28Before [.query 1] = 5 := by decide
  have hn : rawVisits favorableNextS28Before ([.query 1]++[.hydeRetriever 2]) = 1 := by decide
  have hz : (controlPenalty savedCref uniformQuoteError unitRoleUnused .next) favorableNextS28Before [.query 1] (.hydeRetriever 2) = 0 := by
    apply control_penalty_empty_of_prior_terminal .next savedCref uniformQuoteError favorableNextS28Before [.query 1] (.hydeRetriever 2) 18 (by decide)
    · decide
    · decide
  unfold indexScore
  rw [hs,hp,hn,hz]
  simp only [BackupStat.mean]
  norm_num

theorem favorableNextS28D1Cmp0 : indexScore (7/5) (controlPenalty savedCref uniformQuoteError unitRoleUnused .next) favorableNextS28Before [.query 1] (.hydeRetriever 1) < indexScore (7/5) (controlPenalty savedCref uniformQuoteError unitRoleUnused .next) favorableNextS28Before [.query 1] (.hydeRetriever 0) := by
  rw [favorableNextS28D1I0,favorableNextS28D1I1]
  have h := index_strict_order_from_intervals ((0/1)/1) ((1/1)/2) 0 0 (93699627/50000000) (66255651/50000000)
    (treeBonus (7/5) 5 1) (treeBonus (7/5) 5 2)
    (trajectory_bonus_5_1).1 (trajectory_bonus_5_2).2 (by norm_num)
  simpa only [treeIndex,sub_zero] using h

theorem favorableNextS28D1Cmp2 : indexScore (7/5) (controlPenalty savedCref uniformQuoteError unitRoleUnused .next) favorableNextS28Before [.query 1] (.hydeRetriever 2) ≤ indexScore (7/5) (controlPenalty savedCref uniformQuoteError unitRoleUnused .next) favorableNextS28Before [.query 1] (.hydeRetriever 0) := by
  rw [favorableNextS28D1I2,favorableNextS28D1I1]

theorem favorableNextS28Choice1 : nativeFirstChoice (indexScore (7/5) (controlPenalty savedCref uniformQuoteError unitRoleUnused .next) favorableNextS28Before [.query 1]) favorableNextS28Before [.query 1] = .hydeRetriever 0 := by
  apply visited_choice_from_ordered_certificate _ _ [.query 1] [.hydeRetriever 1] [.hydeRetriever 2] (.hydeRetriever 0) (by decide)
  · intro a ha
    have ho : orderedLegalAvailable [.query 1] = [.hydeRetriever 1,.hydeRetriever 0,.hydeRetriever 2] := by decide
    rw [ho] at ha
    simp only [List.mem_cons,List.not_mem_nil,or_false] at ha
    rcases ha with rfl | rfl | rfl <;> decide
  · intro a ha
    simp only [List.mem_cons,List.not_mem_nil,or_false] at ha
    rcases ha with rfl
    · exact favorableNextS28D1Cmp0
  · intro a ha
    simp only [List.mem_cons,List.not_mem_nil,or_false] at ha
    rcases ha with rfl
    · exact favorableNextS28D1Cmp2

theorem favorableNextS28ActualEvent : nativeEvent budgetTape (7/5) (controlPenalty savedCref uniformQuoteError unitRoleUnused .next)
    (taskReward false (2/5) (1/2)) favorableNextS28Before = favorableNextEvent28 := by
  have hs0 := native_select_existing_step budgetTape (7/5) (controlPenalty savedCref uniformQuoteError unitRoleUnused .next) favorableNextS28Before 8 [] (.query 1)
    (by decide) (by decide) favorableNextS28Choice0
  have hs1 := native_select_existing_step budgetTape (7/5) (controlPenalty savedCref uniformQuoteError unitRoleUnused .next) favorableNextS28Before 7 [.query 1] (.hydeRetriever 0)
    (by decide) (by decide) favorableNextS28Choice1
  have hnew := native_select_new_step budgetTape (7/5) (controlPenalty savedCref uniformQuoteError unitRoleUnused .next) favorableNextS28Before 6 [.query 1,.hydeRetriever 0]
    [.selection 1,.selection 2,.selection 3,.selection 0] (.selection 0) (by decide) (by decide) (by decide) (by decide)
  have hs : nativeSelect budgetTape (7/5) (controlPenalty savedCref uniformQuoteError unitRoleUnused .next) favorableNextS28Before 9 [] = [.query 1,.hydeRetriever 0,.selection 0] := by
    rw [hs0]
    change nativeSelect budgetTape (7/5) (controlPenalty savedCref uniformQuoteError unitRoleUnused .next) favorableNextS28Before 8 [.query 1] = _
    rw [hs1]
    change nativeSelect budgetTape (7/5) (controlPenalty savedCref uniformQuoteError unitRoleUnused .next) favorableNextS28Before 7 [.query 1,.hydeRetriever 0] = _
    rw [hnew] <;> rfl
  have hr : repairedRollout budgetTape favorableNextS28Before 9 [.query 1,.hydeRetriever 0,.selection 0] = [.query 1,.hydeRetriever 0,.selection 0,.width 0,.stop,.reranker 0,.topm 0,.context 0,.answer 0] := by decide
  simp only [nativeEvent,hs,hr]
  rfl

def favorableNextS29Before := favorableNextProposal.take 28

theorem favorableNextS29D0I0 : indexScore (7/5) (controlPenalty savedCref uniformQuoteError unitRoleUnused .next) favorableNextS29Before [] (.query 0) = treeIndex ((0/1)/3) (7/5) (nextNormalPenalty favorableNextS29Before) 28 3 := by
  have hs : replayBackup favorableNextS29Before emptyStatistics ([]++[.query 0]) = ⟨3,(0/1)⟩ := by
    rw [replayBackup_empty_closed_form]
    simp +decide [backedEvents,favorableNextS29Before,favorableNextProposal,favorableNextEvent1,favorableNextEvent2,favorableNextEvent3,favorableNextEvent4,favorableNextEvent5,favorableNextEvent6,favorableNextEvent7,favorableNextEvent8,favorableNextEvent9,favorableNextEvent10,favorableNextEvent11,favorableNextEvent12,favorableNextEvent13,favorableNextEvent14,favorableNextEvent15,favorableNextEvent16,favorableNextEvent17,favorableNextEvent18,favorableNextEvent19,favorableNextEvent20,favorableNextEvent21,favorableNextEvent22,favorableNextEvent23,favorableNextEvent24,favorableNextEvent25,favorableNextEvent26,favorableNextEvent27,favorableNextEvent28,taskReward]
    <;> norm_num
  have hp : rawVisits favorableNextS29Before [] = 28 := by decide
  have hn : rawVisits favorableNextS29Before ([]++[.query 0]) = 3 := by decide
  have hz : (controlPenalty savedCref uniformQuoteError unitRoleUnused .next) favorableNextS29Before [] (.query 0) = (nextNormalPenalty favorableNextS29Before) := by
    simpa only [favorableNextS29Before,nextNormalPenalty] using AgentUCTNextExact.favorable_next_normal_root_quotes_exact 28 (by omega) 0 (by decide)
  unfold indexScore
  rw [hs,hp,hn,hz]
  simp only [BackupStat.mean]
  norm_num

theorem favorableNextS29D0I1 : indexScore (7/5) (controlPenalty savedCref uniformQuoteError unitRoleUnused .next) favorableNextS29Before [] (.query 1) = treeIndex ((1/1)/6) (7/5) 0 28 6 := by
  have hs : replayBackup favorableNextS29Before emptyStatistics ([]++[.query 1]) = ⟨6,(1/1)⟩ := by
    rw [replayBackup_empty_closed_form]
    simp +decide [backedEvents,favorableNextS29Before,favorableNextProposal,favorableNextEvent1,favorableNextEvent2,favorableNextEvent3,favorableNextEvent4,favorableNextEvent5,favorableNextEvent6,favorableNextEvent7,favorableNextEvent8,favorableNextEvent9,favorableNextEvent10,favorableNextEvent11,favorableNextEvent12,favorableNextEvent13,favorableNextEvent14,favorableNextEvent15,favorableNextEvent16,favorableNextEvent17,favorableNextEvent18,favorableNextEvent19,favorableNextEvent20,favorableNextEvent21,favorableNextEvent22,favorableNextEvent23,favorableNextEvent24,favorableNextEvent25,favorableNextEvent26,favorableNextEvent27,favorableNextEvent28,taskReward]
    <;> norm_num
  have hp : rawVisits favorableNextS29Before [] = 28 := by decide
  have hn : rawVisits favorableNextS29Before ([]++[.query 1]) = 6 := by decide
  have hz : (controlPenalty savedCref uniformQuoteError unitRoleUnused .next) favorableNextS29Before [] (.query 1) = 0 := by
    apply control_penalty_empty_suffix
    exact AgentUCTNextExact.favorable_next_hyde_root_suffix_empty 28 (by omega)
  unfold indexScore
  rw [hs,hp,hn,hz]
  simp only [BackupStat.mean]
  norm_num

theorem favorableNextS29D0I2 : indexScore (7/5) (controlPenalty savedCref uniformQuoteError unitRoleUnused .next) favorableNextS29Before [] (.query 2) = treeIndex ((0/1)/3) (7/5) (nextNormalPenalty favorableNextS29Before) 28 3 := by
  have hs : replayBackup favorableNextS29Before emptyStatistics ([]++[.query 2]) = ⟨3,(0/1)⟩ := by
    rw [replayBackup_empty_closed_form]
    simp +decide [backedEvents,favorableNextS29Before,favorableNextProposal,favorableNextEvent1,favorableNextEvent2,favorableNextEvent3,favorableNextEvent4,favorableNextEvent5,favorableNextEvent6,favorableNextEvent7,favorableNextEvent8,favorableNextEvent9,favorableNextEvent10,favorableNextEvent11,favorableNextEvent12,favorableNextEvent13,favorableNextEvent14,favorableNextEvent15,favorableNextEvent16,favorableNextEvent17,favorableNextEvent18,favorableNextEvent19,favorableNextEvent20,favorableNextEvent21,favorableNextEvent22,favorableNextEvent23,favorableNextEvent24,favorableNextEvent25,favorableNextEvent26,favorableNextEvent27,favorableNextEvent28,taskReward]
    <;> norm_num
  have hp : rawVisits favorableNextS29Before [] = 28 := by decide
  have hn : rawVisits favorableNextS29Before ([]++[.query 2]) = 3 := by decide
  have hz : (controlPenalty savedCref uniformQuoteError unitRoleUnused .next) favorableNextS29Before [] (.query 2) = (nextNormalPenalty favorableNextS29Before) := by
    simpa only [favorableNextS29Before,nextNormalPenalty] using AgentUCTNextExact.favorable_next_normal_root_quotes_exact 28 (by omega) 2 (by decide)
  unfold indexScore
  rw [hs,hp,hn,hz]
  simp only [BackupStat.mean]
  norm_num

theorem favorableNextS29D0I3 : indexScore (7/5) (controlPenalty savedCref uniformQuoteError unitRoleUnused .next) favorableNextS29Before [] (.query 3) = treeIndex ((0/1)/3) (7/5) (nextNormalPenalty favorableNextS29Before) 28 3 := by
  have hs : replayBackup favorableNextS29Before emptyStatistics ([]++[.query 3]) = ⟨3,(0/1)⟩ := by
    rw [replayBackup_empty_closed_form]
    simp +decide [backedEvents,favorableNextS29Before,favorableNextProposal,favorableNextEvent1,favorableNextEvent2,favorableNextEvent3,favorableNextEvent4,favorableNextEvent5,favorableNextEvent6,favorableNextEvent7,favorableNextEvent8,favorableNextEvent9,favorableNextEvent10,favorableNextEvent11,favorableNextEvent12,favorableNextEvent13,favorableNextEvent14,favorableNextEvent15,favorableNextEvent16,favorableNextEvent17,favorableNextEvent18,favorableNextEvent19,favorableNextEvent20,favorableNextEvent21,favorableNextEvent22,favorableNextEvent23,favorableNextEvent24,favorableNextEvent25,favorableNextEvent26,favorableNextEvent27,favorableNextEvent28,taskReward]
    <;> norm_num
  have hp : rawVisits favorableNextS29Before [] = 28 := by decide
  have hn : rawVisits favorableNextS29Before ([]++[.query 3]) = 3 := by decide
  have hz : (controlPenalty savedCref uniformQuoteError unitRoleUnused .next) favorableNextS29Before [] (.query 3) = (nextNormalPenalty favorableNextS29Before) := by
    simpa only [favorableNextS29Before,nextNormalPenalty] using AgentUCTNextExact.favorable_next_normal_root_quotes_exact 28 (by omega) 3 (by decide)
  unfold indexScore
  rw [hs,hp,hn,hz]
  simp only [BackupStat.mean]
  norm_num

theorem favorableNextS29D0I4 : indexScore (7/5) (controlPenalty savedCref uniformQuoteError unitRoleUnused .next) favorableNextS29Before [] (.query 4) = treeIndex ((0/1)/3) (7/5) (nextNormalPenalty favorableNextS29Before) 28 3 := by
  have hs : replayBackup favorableNextS29Before emptyStatistics ([]++[.query 4]) = ⟨3,(0/1)⟩ := by
    rw [replayBackup_empty_closed_form]
    simp +decide [backedEvents,favorableNextS29Before,favorableNextProposal,favorableNextEvent1,favorableNextEvent2,favorableNextEvent3,favorableNextEvent4,favorableNextEvent5,favorableNextEvent6,favorableNextEvent7,favorableNextEvent8,favorableNextEvent9,favorableNextEvent10,favorableNextEvent11,favorableNextEvent12,favorableNextEvent13,favorableNextEvent14,favorableNextEvent15,favorableNextEvent16,favorableNextEvent17,favorableNextEvent18,favorableNextEvent19,favorableNextEvent20,favorableNextEvent21,favorableNextEvent22,favorableNextEvent23,favorableNextEvent24,favorableNextEvent25,favorableNextEvent26,favorableNextEvent27,favorableNextEvent28,taskReward]
    <;> norm_num
  have hp : rawVisits favorableNextS29Before [] = 28 := by decide
  have hn : rawVisits favorableNextS29Before ([]++[.query 4]) = 3 := by decide
  have hz : (controlPenalty savedCref uniformQuoteError unitRoleUnused .next) favorableNextS29Before [] (.query 4) = (nextNormalPenalty favorableNextS29Before) := by
    simpa only [favorableNextS29Before,nextNormalPenalty] using AgentUCTNextExact.favorable_next_normal_root_quotes_exact 28 (by omega) 4 (by decide)
  unfold indexScore
  rw [hs,hp,hn,hz]
  simp only [BackupStat.mean]
  norm_num

theorem favorableNextS29D0I5 : indexScore (7/5) (controlPenalty savedCref uniformQuoteError unitRoleUnused .next) favorableNextS29Before [] (.query 5) = treeIndex ((6/5)/4) (7/5) (nextNormalPenalty favorableNextS29Before) 28 4 := by
  have hs : replayBackup favorableNextS29Before emptyStatistics ([]++[.query 5]) = ⟨4,(6/5)⟩ := by
    rw [replayBackup_empty_closed_form]
    simp +decide [backedEvents,favorableNextS29Before,favorableNextProposal,favorableNextEvent1,favorableNextEvent2,favorableNextEvent3,favorableNextEvent4,favorableNextEvent5,favorableNextEvent6,favorableNextEvent7,favorableNextEvent8,favorableNextEvent9,favorableNextEvent10,favorableNextEvent11,favorableNextEvent12,favorableNextEvent13,favorableNextEvent14,favorableNextEvent15,favorableNextEvent16,favorableNextEvent17,favorableNextEvent18,favorableNextEvent19,favorableNextEvent20,favorableNextEvent21,favorableNextEvent22,favorableNextEvent23,favorableNextEvent24,favorableNextEvent25,favorableNextEvent26,favorableNextEvent27,favorableNextEvent28,taskReward]
    <;> norm_num
  have hp : rawVisits favorableNextS29Before [] = 28 := by decide
  have hn : rawVisits favorableNextS29Before ([]++[.query 5]) = 4 := by decide
  have hz : (controlPenalty savedCref uniformQuoteError unitRoleUnused .next) favorableNextS29Before [] (.query 5) = (nextNormalPenalty favorableNextS29Before) := by
    simpa only [favorableNextS29Before,nextNormalPenalty] using AgentUCTNextExact.favorable_next_normal_root_quotes_exact 28 (by omega) 5 (by decide)
  unfold indexScore
  rw [hs,hp,hn,hz]
  simp only [BackupStat.mean]
  norm_num

theorem favorableNextS29D0I6 : indexScore (7/5) (controlPenalty savedCref uniformQuoteError unitRoleUnused .next) favorableNextS29Before [] (.query 6) = treeIndex ((0/1)/3) (7/5) (nextNormalPenalty favorableNextS29Before) 28 3 := by
  have hs : replayBackup favorableNextS29Before emptyStatistics ([]++[.query 6]) = ⟨3,(0/1)⟩ := by
    rw [replayBackup_empty_closed_form]
    simp +decide [backedEvents,favorableNextS29Before,favorableNextProposal,favorableNextEvent1,favorableNextEvent2,favorableNextEvent3,favorableNextEvent4,favorableNextEvent5,favorableNextEvent6,favorableNextEvent7,favorableNextEvent8,favorableNextEvent9,favorableNextEvent10,favorableNextEvent11,favorableNextEvent12,favorableNextEvent13,favorableNextEvent14,favorableNextEvent15,favorableNextEvent16,favorableNextEvent17,favorableNextEvent18,favorableNextEvent19,favorableNextEvent20,favorableNextEvent21,favorableNextEvent22,favorableNextEvent23,favorableNextEvent24,favorableNextEvent25,favorableNextEvent26,favorableNextEvent27,favorableNextEvent28,taskReward]
    <;> norm_num
  have hp : rawVisits favorableNextS29Before [] = 28 := by decide
  have hn : rawVisits favorableNextS29Before ([]++[.query 6]) = 3 := by decide
  have hz : (controlPenalty savedCref uniformQuoteError unitRoleUnused .next) favorableNextS29Before [] (.query 6) = (nextNormalPenalty favorableNextS29Before) := by
    simpa only [favorableNextS29Before,nextNormalPenalty] using AgentUCTNextExact.favorable_next_normal_root_quotes_exact 28 (by omega) 6 (by decide)
  unfold indexScore
  rw [hs,hp,hn,hz]
  simp only [BackupStat.mean]
  norm_num

theorem favorableNextS29D0I7 : indexScore (7/5) (controlPenalty savedCref uniformQuoteError unitRoleUnused .next) favorableNextS29Before [] (.query 7) = treeIndex ((0/1)/3) (7/5) (nextNormalPenalty favorableNextS29Before) 28 3 := by
  have hs : replayBackup favorableNextS29Before emptyStatistics ([]++[.query 7]) = ⟨3,(0/1)⟩ := by
    rw [replayBackup_empty_closed_form]
    simp +decide [backedEvents,favorableNextS29Before,favorableNextProposal,favorableNextEvent1,favorableNextEvent2,favorableNextEvent3,favorableNextEvent4,favorableNextEvent5,favorableNextEvent6,favorableNextEvent7,favorableNextEvent8,favorableNextEvent9,favorableNextEvent10,favorableNextEvent11,favorableNextEvent12,favorableNextEvent13,favorableNextEvent14,favorableNextEvent15,favorableNextEvent16,favorableNextEvent17,favorableNextEvent18,favorableNextEvent19,favorableNextEvent20,favorableNextEvent21,favorableNextEvent22,favorableNextEvent23,favorableNextEvent24,favorableNextEvent25,favorableNextEvent26,favorableNextEvent27,favorableNextEvent28,taskReward]
    <;> norm_num
  have hp : rawVisits favorableNextS29Before [] = 28 := by decide
  have hn : rawVisits favorableNextS29Before ([]++[.query 7]) = 3 := by decide
  have hz : (controlPenalty savedCref uniformQuoteError unitRoleUnused .next) favorableNextS29Before [] (.query 7) = (nextNormalPenalty favorableNextS29Before) := by
    simpa only [favorableNextS29Before,nextNormalPenalty] using AgentUCTNextExact.favorable_next_normal_root_quotes_exact 28 (by omega) 7 (by decide)
  unfold indexScore
  rw [hs,hp,hn,hz]
  simp only [BackupStat.mean]
  norm_num

theorem favorableNextS29D0Cmp0 : indexScore (7/5) (controlPenalty savedCref uniformQuoteError unitRoleUnused .next) favorableNextS29Before [] (.query 0) < indexScore (7/5) (controlPenalty savedCref uniformQuoteError unitRoleUnused .next) favorableNextS29Before [] (.query 5) := by
  rw [favorableNextS29D0I0,favorableNextS29D0I5]
  have hk := favorable_next_penalty_interval 28 (by omega)
  change nextNormalPenaltyLower ≤ nextNormalPenalty favorableNextS29Before ∧ nextNormalPenalty favorableNextS29Before ≤ nextNormalPenaltyUpper at hk
  have hm : ((0/1)/3)+(74161423/50000000)-(nextNormalPenalty favorableNextS29Before) < ((6/5)/4)+(8028209/6250000)-(nextNormalPenalty favorableNextS29Before) := by
    have h : (((0/1)/3)+(74161423/50000000) : ℝ) < ((6/5)/4)+(8028209/6250000) := by norm_num
    linarith
  have h := index_strict_order_from_intervals ((6/5)/4) ((0/1)/3) (nextNormalPenalty favorableNextS29Before) (nextNormalPenalty favorableNextS29Before) (8028209/6250000) (74161423/50000000)
    (treeBonus (7/5) 28 4) (treeBonus (7/5) 28 3)
    (trajectory_bonus_28_4).1 (trajectory_bonus_28_3).2 hm
  simpa only [treeIndex] using h

theorem favorableNextS29D0Cmp1 : indexScore (7/5) (controlPenalty savedCref uniformQuoteError unitRoleUnused .next) favorableNextS29Before [] (.query 1) < indexScore (7/5) (controlPenalty savedCref uniformQuoteError unitRoleUnused .next) favorableNextS29Before [] (.query 5) := by
  rw [favorableNextS29D0I1,favorableNextS29D0I5]
  have hk := favorable_next_penalty_interval 28 (by omega)
  change nextNormalPenaltyLower ≤ nextNormalPenalty favorableNextS29Before ∧ nextNormalPenalty favorableNextS29Before ≤ nextNormalPenaltyUpper at hk
  have hm : ((1/1)/6)+(10488009/10000000)-0 < ((6/5)/4)+(8028209/6250000)-(nextNormalPenalty favorableNextS29Before) := by
    have h : ((1/1)/6)+(10488009/10000000) < ((6/5)/4)+(8028209/6250000)-nextNormalPenaltyUpper := by norm_num [nextNormalPenaltyUpper,savedCref,uniformQuoteError]
    linarith [hk.2]
  have h := index_strict_order_from_intervals ((6/5)/4) ((1/1)/6) (nextNormalPenalty favorableNextS29Before) 0 (8028209/6250000) (10488009/10000000)
    (treeBonus (7/5) 28 4) (treeBonus (7/5) 28 6)
    (trajectory_bonus_28_4).1 (trajectory_bonus_28_6).2 hm
  simpa only [treeIndex] using h

theorem favorableNextS29D0Cmp2 : indexScore (7/5) (controlPenalty savedCref uniformQuoteError unitRoleUnused .next) favorableNextS29Before [] (.query 2) < indexScore (7/5) (controlPenalty savedCref uniformQuoteError unitRoleUnused .next) favorableNextS29Before [] (.query 5) := by
  rw [favorableNextS29D0I2,favorableNextS29D0I5]
  have hk := favorable_next_penalty_interval 28 (by omega)
  change nextNormalPenaltyLower ≤ nextNormalPenalty favorableNextS29Before ∧ nextNormalPenalty favorableNextS29Before ≤ nextNormalPenaltyUpper at hk
  have hm : ((0/1)/3)+(74161423/50000000)-(nextNormalPenalty favorableNextS29Before) < ((6/5)/4)+(8028209/6250000)-(nextNormalPenalty favorableNextS29Before) := by
    have h : (((0/1)/3)+(74161423/50000000) : ℝ) < ((6/5)/4)+(8028209/6250000) := by norm_num
    linarith
  have h := index_strict_order_from_intervals ((6/5)/4) ((0/1)/3) (nextNormalPenalty favorableNextS29Before) (nextNormalPenalty favorableNextS29Before) (8028209/6250000) (74161423/50000000)
    (treeBonus (7/5) 28 4) (treeBonus (7/5) 28 3)
    (trajectory_bonus_28_4).1 (trajectory_bonus_28_3).2 hm
  simpa only [treeIndex] using h

theorem favorableNextS29D0Cmp3 : indexScore (7/5) (controlPenalty savedCref uniformQuoteError unitRoleUnused .next) favorableNextS29Before [] (.query 3) < indexScore (7/5) (controlPenalty savedCref uniformQuoteError unitRoleUnused .next) favorableNextS29Before [] (.query 5) := by
  rw [favorableNextS29D0I3,favorableNextS29D0I5]
  have hk := favorable_next_penalty_interval 28 (by omega)
  change nextNormalPenaltyLower ≤ nextNormalPenalty favorableNextS29Before ∧ nextNormalPenalty favorableNextS29Before ≤ nextNormalPenaltyUpper at hk
  have hm : ((0/1)/3)+(74161423/50000000)-(nextNormalPenalty favorableNextS29Before) < ((6/5)/4)+(8028209/6250000)-(nextNormalPenalty favorableNextS29Before) := by
    have h : (((0/1)/3)+(74161423/50000000) : ℝ) < ((6/5)/4)+(8028209/6250000) := by norm_num
    linarith
  have h := index_strict_order_from_intervals ((6/5)/4) ((0/1)/3) (nextNormalPenalty favorableNextS29Before) (nextNormalPenalty favorableNextS29Before) (8028209/6250000) (74161423/50000000)
    (treeBonus (7/5) 28 4) (treeBonus (7/5) 28 3)
    (trajectory_bonus_28_4).1 (trajectory_bonus_28_3).2 hm
  simpa only [treeIndex] using h

theorem favorableNextS29D0Cmp4 : indexScore (7/5) (controlPenalty savedCref uniformQuoteError unitRoleUnused .next) favorableNextS29Before [] (.query 4) < indexScore (7/5) (controlPenalty savedCref uniformQuoteError unitRoleUnused .next) favorableNextS29Before [] (.query 5) := by
  rw [favorableNextS29D0I4,favorableNextS29D0I5]
  have hk := favorable_next_penalty_interval 28 (by omega)
  change nextNormalPenaltyLower ≤ nextNormalPenalty favorableNextS29Before ∧ nextNormalPenalty favorableNextS29Before ≤ nextNormalPenaltyUpper at hk
  have hm : ((0/1)/3)+(74161423/50000000)-(nextNormalPenalty favorableNextS29Before) < ((6/5)/4)+(8028209/6250000)-(nextNormalPenalty favorableNextS29Before) := by
    have h : (((0/1)/3)+(74161423/50000000) : ℝ) < ((6/5)/4)+(8028209/6250000) := by norm_num
    linarith
  have h := index_strict_order_from_intervals ((6/5)/4) ((0/1)/3) (nextNormalPenalty favorableNextS29Before) (nextNormalPenalty favorableNextS29Before) (8028209/6250000) (74161423/50000000)
    (treeBonus (7/5) 28 4) (treeBonus (7/5) 28 3)
    (trajectory_bonus_28_4).1 (trajectory_bonus_28_3).2 hm
  simpa only [treeIndex] using h

theorem favorableNextS29D0Cmp6 : indexScore (7/5) (controlPenalty savedCref uniformQuoteError unitRoleUnused .next) favorableNextS29Before [] (.query 6) ≤ indexScore (7/5) (controlPenalty savedCref uniformQuoteError unitRoleUnused .next) favorableNextS29Before [] (.query 5) := by
  rw [favorableNextS29D0I6,favorableNextS29D0I5]
  have hk := favorable_next_penalty_interval 28 (by omega)
  change nextNormalPenaltyLower ≤ nextNormalPenalty favorableNextS29Before ∧ nextNormalPenalty favorableNextS29Before ≤ nextNormalPenaltyUpper at hk
  have hm : ((0/1)/3)+(74161423/50000000)-(nextNormalPenalty favorableNextS29Before) < ((6/5)/4)+(8028209/6250000)-(nextNormalPenalty favorableNextS29Before) := by
    have h : (((0/1)/3)+(74161423/50000000) : ℝ) < ((6/5)/4)+(8028209/6250000) := by norm_num
    linarith
  have h := index_weak_order_from_intervals ((6/5)/4) ((0/1)/3) (nextNormalPenalty favorableNextS29Before) (nextNormalPenalty favorableNextS29Before) (8028209/6250000) (74161423/50000000)
    (treeBonus (7/5) 28 4) (treeBonus (7/5) 28 3)
    (trajectory_bonus_28_4).1 (trajectory_bonus_28_3).2 hm.le
  simpa only [treeIndex] using h

theorem favorableNextS29D0Cmp7 : indexScore (7/5) (controlPenalty savedCref uniformQuoteError unitRoleUnused .next) favorableNextS29Before [] (.query 7) ≤ indexScore (7/5) (controlPenalty savedCref uniformQuoteError unitRoleUnused .next) favorableNextS29Before [] (.query 5) := by
  rw [favorableNextS29D0I7,favorableNextS29D0I5]
  have hk := favorable_next_penalty_interval 28 (by omega)
  change nextNormalPenaltyLower ≤ nextNormalPenalty favorableNextS29Before ∧ nextNormalPenalty favorableNextS29Before ≤ nextNormalPenaltyUpper at hk
  have hm : ((0/1)/3)+(74161423/50000000)-(nextNormalPenalty favorableNextS29Before) < ((6/5)/4)+(8028209/6250000)-(nextNormalPenalty favorableNextS29Before) := by
    have h : (((0/1)/3)+(74161423/50000000) : ℝ) < ((6/5)/4)+(8028209/6250000) := by norm_num
    linarith
  have h := index_weak_order_from_intervals ((6/5)/4) ((0/1)/3) (nextNormalPenalty favorableNextS29Before) (nextNormalPenalty favorableNextS29Before) (8028209/6250000) (74161423/50000000)
    (treeBonus (7/5) 28 4) (treeBonus (7/5) 28 3)
    (trajectory_bonus_28_4).1 (trajectory_bonus_28_3).2 hm.le
  simpa only [treeIndex] using h

theorem favorableNextS29Choice0 : nativeFirstChoice (indexScore (7/5) (controlPenalty savedCref uniformQuoteError unitRoleUnused .next) favorableNextS29Before []) favorableNextS29Before [] = .query 5 := by
  apply visited_choice_from_ordered_certificate _ _ [] [.query 0,.query 1,.query 2,.query 3,.query 4] [.query 6,.query 7] (.query 5) (by decide)
  · intro a ha
    have ho : orderedLegalAvailable [] = [.query 0,.query 1,.query 2,.query 3,.query 4,.query 5,.query 6,.query 7] := by decide
    rw [ho] at ha
    simp only [List.mem_cons,List.not_mem_nil,or_false] at ha
    rcases ha with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> decide
  · intro a ha
    simp only [List.mem_cons,List.not_mem_nil,or_false] at ha
    rcases ha with rfl | rfl | rfl | rfl | rfl
    · exact favorableNextS29D0Cmp0
    · exact favorableNextS29D0Cmp1
    · exact favorableNextS29D0Cmp2
    · exact favorableNextS29D0Cmp3
    · exact favorableNextS29D0Cmp4
  · intro a ha
    simp only [List.mem_cons,List.not_mem_nil,or_false] at ha
    rcases ha with rfl | rfl
    · exact favorableNextS29D0Cmp6
    · exact favorableNextS29D0Cmp7

theorem favorableNextS29ActualEvent : nativeEvent budgetTape (7/5) (controlPenalty savedCref uniformQuoteError unitRoleUnused .next)
    (taskReward false (2/5) (1/2)) favorableNextS29Before = favorableNextEvent29 := by
  have hs0 := native_select_existing_step budgetTape (7/5) (controlPenalty savedCref uniformQuoteError unitRoleUnused .next) favorableNextS29Before 8 [] (.query 5)
    (by decide) (by decide) favorableNextS29Choice0
  have hnew := native_select_new_step budgetTape (7/5) (controlPenalty savedCref uniformQuoteError unitRoleUnused .next) favorableNextS29Before 7 [.query 5]
    [.normalRetriever 6,.normalRetriever 7,.normalRetriever 8,.normalRetriever 5,.normalRetriever 2,.normalRetriever 3,.normalRetriever 12,.normalRetriever 14,.normalRetriever 13,.normalRetriever 21,.normalRetriever 23,.normalRetriever 22,.normalRetriever 9,.normalRetriever 11,.normalRetriever 10,.normalRetriever 15,.normalRetriever 17,.normalRetriever 16,.normalRetriever 18,.normalRetriever 20,.normalRetriever 19,.normalRetriever 24,.normalRetriever 25,.normalRetriever 26,.normalRetriever 27,.normalRetriever 28,.normalRetriever 29] (.normalRetriever 6) (by decide) (by decide) (by decide) (by decide)
  have hs : nativeSelect budgetTape (7/5) (controlPenalty savedCref uniformQuoteError unitRoleUnused .next) favorableNextS29Before 9 [] = [.query 5,.normalRetriever 6] := by
    rw [hs0]
    change nativeSelect budgetTape (7/5) (controlPenalty savedCref uniformQuoteError unitRoleUnused .next) favorableNextS29Before 8 [.query 5] = _
    rw [hnew] <;> rfl
  have hr : repairedRollout budgetTape favorableNextS29Before 9 [.query 5,.normalRetriever 6] = [.query 5,.normalRetriever 6,.selection 0,.width 0,.stop,.reranker 0,.topm 0,.context 0,.answer 0] := by decide
  simp only [nativeEvent,hs,hr]
  rfl

def favorableNextS30Before := favorableNextProposal.take 29

theorem favorableNextS30D0I0 : indexScore (7/5) (controlPenalty savedCref uniformQuoteError unitRoleUnused .next) favorableNextS30Before [] (.query 0) = treeIndex ((0/1)/3) (7/5) (nextNormalPenalty favorableNextS30Before) 29 3 := by
  have hs : replayBackup favorableNextS30Before emptyStatistics ([]++[.query 0]) = ⟨3,(0/1)⟩ := by
    rw [replayBackup_empty_closed_form]
    simp +decide [backedEvents,favorableNextS30Before,favorableNextProposal,favorableNextEvent1,favorableNextEvent2,favorableNextEvent3,favorableNextEvent4,favorableNextEvent5,favorableNextEvent6,favorableNextEvent7,favorableNextEvent8,favorableNextEvent9,favorableNextEvent10,favorableNextEvent11,favorableNextEvent12,favorableNextEvent13,favorableNextEvent14,favorableNextEvent15,favorableNextEvent16,favorableNextEvent17,favorableNextEvent18,favorableNextEvent19,favorableNextEvent20,favorableNextEvent21,favorableNextEvent22,favorableNextEvent23,favorableNextEvent24,favorableNextEvent25,favorableNextEvent26,favorableNextEvent27,favorableNextEvent28,favorableNextEvent29,taskReward]
    <;> norm_num
  have hp : rawVisits favorableNextS30Before [] = 29 := by decide
  have hn : rawVisits favorableNextS30Before ([]++[.query 0]) = 3 := by decide
  have hz : (controlPenalty savedCref uniformQuoteError unitRoleUnused .next) favorableNextS30Before [] (.query 0) = (nextNormalPenalty favorableNextS30Before) := by
    simpa only [favorableNextS30Before,nextNormalPenalty] using AgentUCTNextExact.favorable_next_normal_root_quotes_exact 29 (by omega) 0 (by decide)
  unfold indexScore
  rw [hs,hp,hn,hz]
  simp only [BackupStat.mean]
  norm_num

theorem favorableNextS30D0I1 : indexScore (7/5) (controlPenalty savedCref uniformQuoteError unitRoleUnused .next) favorableNextS30Before [] (.query 1) = treeIndex ((1/1)/6) (7/5) 0 29 6 := by
  have hs : replayBackup favorableNextS30Before emptyStatistics ([]++[.query 1]) = ⟨6,(1/1)⟩ := by
    rw [replayBackup_empty_closed_form]
    simp +decide [backedEvents,favorableNextS30Before,favorableNextProposal,favorableNextEvent1,favorableNextEvent2,favorableNextEvent3,favorableNextEvent4,favorableNextEvent5,favorableNextEvent6,favorableNextEvent7,favorableNextEvent8,favorableNextEvent9,favorableNextEvent10,favorableNextEvent11,favorableNextEvent12,favorableNextEvent13,favorableNextEvent14,favorableNextEvent15,favorableNextEvent16,favorableNextEvent17,favorableNextEvent18,favorableNextEvent19,favorableNextEvent20,favorableNextEvent21,favorableNextEvent22,favorableNextEvent23,favorableNextEvent24,favorableNextEvent25,favorableNextEvent26,favorableNextEvent27,favorableNextEvent28,favorableNextEvent29,taskReward]
    <;> norm_num
  have hp : rawVisits favorableNextS30Before [] = 29 := by decide
  have hn : rawVisits favorableNextS30Before ([]++[.query 1]) = 6 := by decide
  have hz : (controlPenalty savedCref uniformQuoteError unitRoleUnused .next) favorableNextS30Before [] (.query 1) = 0 := by
    apply control_penalty_empty_suffix
    exact AgentUCTNextExact.favorable_next_hyde_root_suffix_empty 29 (by omega)
  unfold indexScore
  rw [hs,hp,hn,hz]
  simp only [BackupStat.mean]
  norm_num

theorem favorableNextS30D0I2 : indexScore (7/5) (controlPenalty savedCref uniformQuoteError unitRoleUnused .next) favorableNextS30Before [] (.query 2) = treeIndex ((0/1)/3) (7/5) (nextNormalPenalty favorableNextS30Before) 29 3 := by
  have hs : replayBackup favorableNextS30Before emptyStatistics ([]++[.query 2]) = ⟨3,(0/1)⟩ := by
    rw [replayBackup_empty_closed_form]
    simp +decide [backedEvents,favorableNextS30Before,favorableNextProposal,favorableNextEvent1,favorableNextEvent2,favorableNextEvent3,favorableNextEvent4,favorableNextEvent5,favorableNextEvent6,favorableNextEvent7,favorableNextEvent8,favorableNextEvent9,favorableNextEvent10,favorableNextEvent11,favorableNextEvent12,favorableNextEvent13,favorableNextEvent14,favorableNextEvent15,favorableNextEvent16,favorableNextEvent17,favorableNextEvent18,favorableNextEvent19,favorableNextEvent20,favorableNextEvent21,favorableNextEvent22,favorableNextEvent23,favorableNextEvent24,favorableNextEvent25,favorableNextEvent26,favorableNextEvent27,favorableNextEvent28,favorableNextEvent29,taskReward]
    <;> norm_num
  have hp : rawVisits favorableNextS30Before [] = 29 := by decide
  have hn : rawVisits favorableNextS30Before ([]++[.query 2]) = 3 := by decide
  have hz : (controlPenalty savedCref uniformQuoteError unitRoleUnused .next) favorableNextS30Before [] (.query 2) = (nextNormalPenalty favorableNextS30Before) := by
    simpa only [favorableNextS30Before,nextNormalPenalty] using AgentUCTNextExact.favorable_next_normal_root_quotes_exact 29 (by omega) 2 (by decide)
  unfold indexScore
  rw [hs,hp,hn,hz]
  simp only [BackupStat.mean]
  norm_num

theorem favorableNextS30D0I3 : indexScore (7/5) (controlPenalty savedCref uniformQuoteError unitRoleUnused .next) favorableNextS30Before [] (.query 3) = treeIndex ((0/1)/3) (7/5) (nextNormalPenalty favorableNextS30Before) 29 3 := by
  have hs : replayBackup favorableNextS30Before emptyStatistics ([]++[.query 3]) = ⟨3,(0/1)⟩ := by
    rw [replayBackup_empty_closed_form]
    simp +decide [backedEvents,favorableNextS30Before,favorableNextProposal,favorableNextEvent1,favorableNextEvent2,favorableNextEvent3,favorableNextEvent4,favorableNextEvent5,favorableNextEvent6,favorableNextEvent7,favorableNextEvent8,favorableNextEvent9,favorableNextEvent10,favorableNextEvent11,favorableNextEvent12,favorableNextEvent13,favorableNextEvent14,favorableNextEvent15,favorableNextEvent16,favorableNextEvent17,favorableNextEvent18,favorableNextEvent19,favorableNextEvent20,favorableNextEvent21,favorableNextEvent22,favorableNextEvent23,favorableNextEvent24,favorableNextEvent25,favorableNextEvent26,favorableNextEvent27,favorableNextEvent28,favorableNextEvent29,taskReward]
    <;> norm_num
  have hp : rawVisits favorableNextS30Before [] = 29 := by decide
  have hn : rawVisits favorableNextS30Before ([]++[.query 3]) = 3 := by decide
  have hz : (controlPenalty savedCref uniformQuoteError unitRoleUnused .next) favorableNextS30Before [] (.query 3) = (nextNormalPenalty favorableNextS30Before) := by
    simpa only [favorableNextS30Before,nextNormalPenalty] using AgentUCTNextExact.favorable_next_normal_root_quotes_exact 29 (by omega) 3 (by decide)
  unfold indexScore
  rw [hs,hp,hn,hz]
  simp only [BackupStat.mean]
  norm_num

theorem favorableNextS30D0I4 : indexScore (7/5) (controlPenalty savedCref uniformQuoteError unitRoleUnused .next) favorableNextS30Before [] (.query 4) = treeIndex ((0/1)/3) (7/5) (nextNormalPenalty favorableNextS30Before) 29 3 := by
  have hs : replayBackup favorableNextS30Before emptyStatistics ([]++[.query 4]) = ⟨3,(0/1)⟩ := by
    rw [replayBackup_empty_closed_form]
    simp +decide [backedEvents,favorableNextS30Before,favorableNextProposal,favorableNextEvent1,favorableNextEvent2,favorableNextEvent3,favorableNextEvent4,favorableNextEvent5,favorableNextEvent6,favorableNextEvent7,favorableNextEvent8,favorableNextEvent9,favorableNextEvent10,favorableNextEvent11,favorableNextEvent12,favorableNextEvent13,favorableNextEvent14,favorableNextEvent15,favorableNextEvent16,favorableNextEvent17,favorableNextEvent18,favorableNextEvent19,favorableNextEvent20,favorableNextEvent21,favorableNextEvent22,favorableNextEvent23,favorableNextEvent24,favorableNextEvent25,favorableNextEvent26,favorableNextEvent27,favorableNextEvent28,favorableNextEvent29,taskReward]
    <;> norm_num
  have hp : rawVisits favorableNextS30Before [] = 29 := by decide
  have hn : rawVisits favorableNextS30Before ([]++[.query 4]) = 3 := by decide
  have hz : (controlPenalty savedCref uniformQuoteError unitRoleUnused .next) favorableNextS30Before [] (.query 4) = (nextNormalPenalty favorableNextS30Before) := by
    simpa only [favorableNextS30Before,nextNormalPenalty] using AgentUCTNextExact.favorable_next_normal_root_quotes_exact 29 (by omega) 4 (by decide)
  unfold indexScore
  rw [hs,hp,hn,hz]
  simp only [BackupStat.mean]
  norm_num

theorem favorableNextS30D0I5 : indexScore (7/5) (controlPenalty savedCref uniformQuoteError unitRoleUnused .next) favorableNextS30Before [] (.query 5) = treeIndex ((6/5)/5) (7/5) (nextNormalPenalty favorableNextS30Before) 29 5 := by
  have hs : replayBackup favorableNextS30Before emptyStatistics ([]++[.query 5]) = ⟨5,(6/5)⟩ := by
    rw [replayBackup_empty_closed_form]
    simp +decide [backedEvents,favorableNextS30Before,favorableNextProposal,favorableNextEvent1,favorableNextEvent2,favorableNextEvent3,favorableNextEvent4,favorableNextEvent5,favorableNextEvent6,favorableNextEvent7,favorableNextEvent8,favorableNextEvent9,favorableNextEvent10,favorableNextEvent11,favorableNextEvent12,favorableNextEvent13,favorableNextEvent14,favorableNextEvent15,favorableNextEvent16,favorableNextEvent17,favorableNextEvent18,favorableNextEvent19,favorableNextEvent20,favorableNextEvent21,favorableNextEvent22,favorableNextEvent23,favorableNextEvent24,favorableNextEvent25,favorableNextEvent26,favorableNextEvent27,favorableNextEvent28,favorableNextEvent29,taskReward]
    <;> norm_num
  have hp : rawVisits favorableNextS30Before [] = 29 := by decide
  have hn : rawVisits favorableNextS30Before ([]++[.query 5]) = 5 := by decide
  have hz : (controlPenalty savedCref uniformQuoteError unitRoleUnused .next) favorableNextS30Before [] (.query 5) = (nextNormalPenalty favorableNextS30Before) := by
    simpa only [favorableNextS30Before,nextNormalPenalty] using AgentUCTNextExact.favorable_next_normal_root_quotes_exact 29 (by omega) 5 (by decide)
  unfold indexScore
  rw [hs,hp,hn,hz]
  simp only [BackupStat.mean]
  norm_num

theorem favorableNextS30D0I6 : indexScore (7/5) (controlPenalty savedCref uniformQuoteError unitRoleUnused .next) favorableNextS30Before [] (.query 6) = treeIndex ((0/1)/3) (7/5) (nextNormalPenalty favorableNextS30Before) 29 3 := by
  have hs : replayBackup favorableNextS30Before emptyStatistics ([]++[.query 6]) = ⟨3,(0/1)⟩ := by
    rw [replayBackup_empty_closed_form]
    simp +decide [backedEvents,favorableNextS30Before,favorableNextProposal,favorableNextEvent1,favorableNextEvent2,favorableNextEvent3,favorableNextEvent4,favorableNextEvent5,favorableNextEvent6,favorableNextEvent7,favorableNextEvent8,favorableNextEvent9,favorableNextEvent10,favorableNextEvent11,favorableNextEvent12,favorableNextEvent13,favorableNextEvent14,favorableNextEvent15,favorableNextEvent16,favorableNextEvent17,favorableNextEvent18,favorableNextEvent19,favorableNextEvent20,favorableNextEvent21,favorableNextEvent22,favorableNextEvent23,favorableNextEvent24,favorableNextEvent25,favorableNextEvent26,favorableNextEvent27,favorableNextEvent28,favorableNextEvent29,taskReward]
    <;> norm_num
  have hp : rawVisits favorableNextS30Before [] = 29 := by decide
  have hn : rawVisits favorableNextS30Before ([]++[.query 6]) = 3 := by decide
  have hz : (controlPenalty savedCref uniformQuoteError unitRoleUnused .next) favorableNextS30Before [] (.query 6) = (nextNormalPenalty favorableNextS30Before) := by
    simpa only [favorableNextS30Before,nextNormalPenalty] using AgentUCTNextExact.favorable_next_normal_root_quotes_exact 29 (by omega) 6 (by decide)
  unfold indexScore
  rw [hs,hp,hn,hz]
  simp only [BackupStat.mean]
  norm_num

theorem favorableNextS30D0I7 : indexScore (7/5) (controlPenalty savedCref uniformQuoteError unitRoleUnused .next) favorableNextS30Before [] (.query 7) = treeIndex ((0/1)/3) (7/5) (nextNormalPenalty favorableNextS30Before) 29 3 := by
  have hs : replayBackup favorableNextS30Before emptyStatistics ([]++[.query 7]) = ⟨3,(0/1)⟩ := by
    rw [replayBackup_empty_closed_form]
    simp +decide [backedEvents,favorableNextS30Before,favorableNextProposal,favorableNextEvent1,favorableNextEvent2,favorableNextEvent3,favorableNextEvent4,favorableNextEvent5,favorableNextEvent6,favorableNextEvent7,favorableNextEvent8,favorableNextEvent9,favorableNextEvent10,favorableNextEvent11,favorableNextEvent12,favorableNextEvent13,favorableNextEvent14,favorableNextEvent15,favorableNextEvent16,favorableNextEvent17,favorableNextEvent18,favorableNextEvent19,favorableNextEvent20,favorableNextEvent21,favorableNextEvent22,favorableNextEvent23,favorableNextEvent24,favorableNextEvent25,favorableNextEvent26,favorableNextEvent27,favorableNextEvent28,favorableNextEvent29,taskReward]
    <;> norm_num
  have hp : rawVisits favorableNextS30Before [] = 29 := by decide
  have hn : rawVisits favorableNextS30Before ([]++[.query 7]) = 3 := by decide
  have hz : (controlPenalty savedCref uniformQuoteError unitRoleUnused .next) favorableNextS30Before [] (.query 7) = (nextNormalPenalty favorableNextS30Before) := by
    simpa only [favorableNextS30Before,nextNormalPenalty] using AgentUCTNextExact.favorable_next_normal_root_quotes_exact 29 (by omega) 7 (by decide)
  unfold indexScore
  rw [hs,hp,hn,hz]
  simp only [BackupStat.mean]
  norm_num

theorem favorableNextS30D0Cmp0 : indexScore (7/5) (controlPenalty savedCref uniformQuoteError unitRoleUnused .next) favorableNextS30Before [] (.query 0) < indexScore (7/5) (controlPenalty savedCref uniformQuoteError unitRoleUnused .next) favorableNextS30Before [] (.query 1) := by
  rw [favorableNextS30D0I0,favorableNextS30D0I1]
  have hk := favorable_next_penalty_interval 29 (by omega)
  change nextNormalPenaltyLower ≤ nextNormalPenalty favorableNextS30Before ∧ nextNormalPenalty favorableNextS30Before ≤ nextNormalPenaltyUpper at hk
  have hm : ((0/1)/3)+(9316727/6250000)-(nextNormalPenalty favorableNextS30Before) < ((1/1)/6)+(52703357/50000000)-0 := by
    have h : ((0/1)/3)+(9316727/6250000)-nextNormalPenaltyLower < ((1/1)/6)+(52703357/50000000) := by norm_num [nextNormalPenaltyLower,savedCref,uniformQuoteError]
    linarith [hk.1]
  have h := index_strict_order_from_intervals ((1/1)/6) ((0/1)/3) 0 (nextNormalPenalty favorableNextS30Before) (52703357/50000000) (9316727/6250000)
    (treeBonus (7/5) 29 6) (treeBonus (7/5) 29 3)
    (trajectory_bonus_29_6).1 (trajectory_bonus_29_3).2 hm
  simpa only [treeIndex] using h

theorem favorableNextS30D0Cmp2 : indexScore (7/5) (controlPenalty savedCref uniformQuoteError unitRoleUnused .next) favorableNextS30Before [] (.query 2) ≤ indexScore (7/5) (controlPenalty savedCref uniformQuoteError unitRoleUnused .next) favorableNextS30Before [] (.query 1) := by
  rw [favorableNextS30D0I2,favorableNextS30D0I1]
  have hk := favorable_next_penalty_interval 29 (by omega)
  change nextNormalPenaltyLower ≤ nextNormalPenalty favorableNextS30Before ∧ nextNormalPenalty favorableNextS30Before ≤ nextNormalPenaltyUpper at hk
  have hm : ((0/1)/3)+(9316727/6250000)-(nextNormalPenalty favorableNextS30Before) < ((1/1)/6)+(52703357/50000000)-0 := by
    have h : ((0/1)/3)+(9316727/6250000)-nextNormalPenaltyLower < ((1/1)/6)+(52703357/50000000) := by norm_num [nextNormalPenaltyLower,savedCref,uniformQuoteError]
    linarith [hk.1]
  have h := index_weak_order_from_intervals ((1/1)/6) ((0/1)/3) 0 (nextNormalPenalty favorableNextS30Before) (52703357/50000000) (9316727/6250000)
    (treeBonus (7/5) 29 6) (treeBonus (7/5) 29 3)
    (trajectory_bonus_29_6).1 (trajectory_bonus_29_3).2 hm.le
  simpa only [treeIndex] using h

theorem favorableNextS30D0Cmp3 : indexScore (7/5) (controlPenalty savedCref uniformQuoteError unitRoleUnused .next) favorableNextS30Before [] (.query 3) ≤ indexScore (7/5) (controlPenalty savedCref uniformQuoteError unitRoleUnused .next) favorableNextS30Before [] (.query 1) := by
  rw [favorableNextS30D0I3,favorableNextS30D0I1]
  have hk := favorable_next_penalty_interval 29 (by omega)
  change nextNormalPenaltyLower ≤ nextNormalPenalty favorableNextS30Before ∧ nextNormalPenalty favorableNextS30Before ≤ nextNormalPenaltyUpper at hk
  have hm : ((0/1)/3)+(9316727/6250000)-(nextNormalPenalty favorableNextS30Before) < ((1/1)/6)+(52703357/50000000)-0 := by
    have h : ((0/1)/3)+(9316727/6250000)-nextNormalPenaltyLower < ((1/1)/6)+(52703357/50000000) := by norm_num [nextNormalPenaltyLower,savedCref,uniformQuoteError]
    linarith [hk.1]
  have h := index_weak_order_from_intervals ((1/1)/6) ((0/1)/3) 0 (nextNormalPenalty favorableNextS30Before) (52703357/50000000) (9316727/6250000)
    (treeBonus (7/5) 29 6) (treeBonus (7/5) 29 3)
    (trajectory_bonus_29_6).1 (trajectory_bonus_29_3).2 hm.le
  simpa only [treeIndex] using h

theorem favorableNextS30D0Cmp4 : indexScore (7/5) (controlPenalty savedCref uniformQuoteError unitRoleUnused .next) favorableNextS30Before [] (.query 4) ≤ indexScore (7/5) (controlPenalty savedCref uniformQuoteError unitRoleUnused .next) favorableNextS30Before [] (.query 1) := by
  rw [favorableNextS30D0I4,favorableNextS30D0I1]
  have hk := favorable_next_penalty_interval 29 (by omega)
  change nextNormalPenaltyLower ≤ nextNormalPenalty favorableNextS30Before ∧ nextNormalPenalty favorableNextS30Before ≤ nextNormalPenaltyUpper at hk
  have hm : ((0/1)/3)+(9316727/6250000)-(nextNormalPenalty favorableNextS30Before) < ((1/1)/6)+(52703357/50000000)-0 := by
    have h : ((0/1)/3)+(9316727/6250000)-nextNormalPenaltyLower < ((1/1)/6)+(52703357/50000000) := by norm_num [nextNormalPenaltyLower,savedCref,uniformQuoteError]
    linarith [hk.1]
  have h := index_weak_order_from_intervals ((1/1)/6) ((0/1)/3) 0 (nextNormalPenalty favorableNextS30Before) (52703357/50000000) (9316727/6250000)
    (treeBonus (7/5) 29 6) (treeBonus (7/5) 29 3)
    (trajectory_bonus_29_6).1 (trajectory_bonus_29_3).2 hm.le
  simpa only [treeIndex] using h

theorem favorableNextS30D0Cmp5 : indexScore (7/5) (controlPenalty savedCref uniformQuoteError unitRoleUnused .next) favorableNextS30Before [] (.query 5) ≤ indexScore (7/5) (controlPenalty savedCref uniformQuoteError unitRoleUnused .next) favorableNextS30Before [] (.query 1) := by
  rw [favorableNextS30D0I5,favorableNextS30D0I1]
  have hk := favorable_next_penalty_interval 29 (by omega)
  change nextNormalPenaltyLower ≤ nextNormalPenalty favorableNextS30Before ∧ nextNormalPenalty favorableNextS30Before ≤ nextNormalPenaltyUpper at hk
  have hm : ((6/5)/5)+(3608353/3125000)-(nextNormalPenalty favorableNextS30Before) < ((1/1)/6)+(52703357/50000000)-0 := by
    have h : ((6/5)/5)+(3608353/3125000)-nextNormalPenaltyLower < ((1/1)/6)+(52703357/50000000) := by norm_num [nextNormalPenaltyLower,savedCref,uniformQuoteError]
    linarith [hk.1]
  have h := index_weak_order_from_intervals ((1/1)/6) ((6/5)/5) 0 (nextNormalPenalty favorableNextS30Before) (52703357/50000000) (3608353/3125000)
    (treeBonus (7/5) 29 6) (treeBonus (7/5) 29 5)
    (trajectory_bonus_29_6).1 (trajectory_bonus_29_5).2 hm.le
  simpa only [treeIndex] using h

theorem favorableNextS30D0Cmp6 : indexScore (7/5) (controlPenalty savedCref uniformQuoteError unitRoleUnused .next) favorableNextS30Before [] (.query 6) ≤ indexScore (7/5) (controlPenalty savedCref uniformQuoteError unitRoleUnused .next) favorableNextS30Before [] (.query 1) := by
  rw [favorableNextS30D0I6,favorableNextS30D0I1]
  have hk := favorable_next_penalty_interval 29 (by omega)
  change nextNormalPenaltyLower ≤ nextNormalPenalty favorableNextS30Before ∧ nextNormalPenalty favorableNextS30Before ≤ nextNormalPenaltyUpper at hk
  have hm : ((0/1)/3)+(9316727/6250000)-(nextNormalPenalty favorableNextS30Before) < ((1/1)/6)+(52703357/50000000)-0 := by
    have h : ((0/1)/3)+(9316727/6250000)-nextNormalPenaltyLower < ((1/1)/6)+(52703357/50000000) := by norm_num [nextNormalPenaltyLower,savedCref,uniformQuoteError]
    linarith [hk.1]
  have h := index_weak_order_from_intervals ((1/1)/6) ((0/1)/3) 0 (nextNormalPenalty favorableNextS30Before) (52703357/50000000) (9316727/6250000)
    (treeBonus (7/5) 29 6) (treeBonus (7/5) 29 3)
    (trajectory_bonus_29_6).1 (trajectory_bonus_29_3).2 hm.le
  simpa only [treeIndex] using h

theorem favorableNextS30D0Cmp7 : indexScore (7/5) (controlPenalty savedCref uniformQuoteError unitRoleUnused .next) favorableNextS30Before [] (.query 7) ≤ indexScore (7/5) (controlPenalty savedCref uniformQuoteError unitRoleUnused .next) favorableNextS30Before [] (.query 1) := by
  rw [favorableNextS30D0I7,favorableNextS30D0I1]
  have hk := favorable_next_penalty_interval 29 (by omega)
  change nextNormalPenaltyLower ≤ nextNormalPenalty favorableNextS30Before ∧ nextNormalPenalty favorableNextS30Before ≤ nextNormalPenaltyUpper at hk
  have hm : ((0/1)/3)+(9316727/6250000)-(nextNormalPenalty favorableNextS30Before) < ((1/1)/6)+(52703357/50000000)-0 := by
    have h : ((0/1)/3)+(9316727/6250000)-nextNormalPenaltyLower < ((1/1)/6)+(52703357/50000000) := by norm_num [nextNormalPenaltyLower,savedCref,uniformQuoteError]
    linarith [hk.1]
  have h := index_weak_order_from_intervals ((1/1)/6) ((0/1)/3) 0 (nextNormalPenalty favorableNextS30Before) (52703357/50000000) (9316727/6250000)
    (treeBonus (7/5) 29 6) (treeBonus (7/5) 29 3)
    (trajectory_bonus_29_6).1 (trajectory_bonus_29_3).2 hm.le
  simpa only [treeIndex] using h

theorem favorableNextS30Choice0 : nativeFirstChoice (indexScore (7/5) (controlPenalty savedCref uniformQuoteError unitRoleUnused .next) favorableNextS30Before []) favorableNextS30Before [] = .query 1 := by
  apply visited_choice_from_ordered_certificate _ _ [] [.query 0] [.query 2,.query 3,.query 4,.query 5,.query 6,.query 7] (.query 1) (by decide)
  · intro a ha
    have ho : orderedLegalAvailable [] = [.query 0,.query 1,.query 2,.query 3,.query 4,.query 5,.query 6,.query 7] := by decide
    rw [ho] at ha
    simp only [List.mem_cons,List.not_mem_nil,or_false] at ha
    rcases ha with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> decide
  · intro a ha
    simp only [List.mem_cons,List.not_mem_nil,or_false] at ha
    rcases ha with rfl
    · exact favorableNextS30D0Cmp0
  · intro a ha
    simp only [List.mem_cons,List.not_mem_nil,or_false] at ha
    rcases ha with rfl | rfl | rfl | rfl | rfl | rfl
    · exact favorableNextS30D0Cmp2
    · exact favorableNextS30D0Cmp3
    · exact favorableNextS30D0Cmp4
    · exact favorableNextS30D0Cmp5
    · exact favorableNextS30D0Cmp6
    · exact favorableNextS30D0Cmp7

theorem favorableNextS30D1I0 : indexScore (7/5) (controlPenalty savedCref uniformQuoteError unitRoleUnused .next) favorableNextS30Before [.query 1] (.hydeRetriever 1) = treeIndex ((1/1)/2) (7/5) 0 6 2 := by
  have hs : replayBackup favorableNextS30Before emptyStatistics ([.query 1]++[.hydeRetriever 1]) = ⟨2,(1/1)⟩ := by
    rw [replayBackup_empty_closed_form]
    simp +decide [backedEvents,favorableNextS30Before,favorableNextProposal,favorableNextEvent1,favorableNextEvent2,favorableNextEvent3,favorableNextEvent4,favorableNextEvent5,favorableNextEvent6,favorableNextEvent7,favorableNextEvent8,favorableNextEvent9,favorableNextEvent10,favorableNextEvent11,favorableNextEvent12,favorableNextEvent13,favorableNextEvent14,favorableNextEvent15,favorableNextEvent16,favorableNextEvent17,favorableNextEvent18,favorableNextEvent19,favorableNextEvent20,favorableNextEvent21,favorableNextEvent22,favorableNextEvent23,favorableNextEvent24,favorableNextEvent25,favorableNextEvent26,favorableNextEvent27,favorableNextEvent28,favorableNextEvent29,taskReward]
    <;> norm_num
  have hp : rawVisits favorableNextS30Before [.query 1] = 6 := by decide
  have hn : rawVisits favorableNextS30Before ([.query 1]++[.hydeRetriever 1]) = 2 := by decide
  have hz : (controlPenalty savedCref uniformQuoteError unitRoleUnused .next) favorableNextS30Before [.query 1] (.hydeRetriever 1) = 0 := by
    apply control_penalty_empty_of_prior_terminal .next savedCref uniformQuoteError favorableNextS30Before [.query 1] (.hydeRetriever 1) 9 (by decide)
    · decide
    · decide
  unfold indexScore
  rw [hs,hp,hn,hz]
  simp only [BackupStat.mean]
  norm_num

theorem favorableNextS30D1I1 : indexScore (7/5) (controlPenalty savedCref uniformQuoteError unitRoleUnused .next) favorableNextS30Before [.query 1] (.hydeRetriever 0) = treeIndex ((0/1)/2) (7/5) 0 6 2 := by
  have hs : replayBackup favorableNextS30Before emptyStatistics ([.query 1]++[.hydeRetriever 0]) = ⟨2,(0/1)⟩ := by
    rw [replayBackup_empty_closed_form]
    simp +decide [backedEvents,favorableNextS30Before,favorableNextProposal,favorableNextEvent1,favorableNextEvent2,favorableNextEvent3,favorableNextEvent4,favorableNextEvent5,favorableNextEvent6,favorableNextEvent7,favorableNextEvent8,favorableNextEvent9,favorableNextEvent10,favorableNextEvent11,favorableNextEvent12,favorableNextEvent13,favorableNextEvent14,favorableNextEvent15,favorableNextEvent16,favorableNextEvent17,favorableNextEvent18,favorableNextEvent19,favorableNextEvent20,favorableNextEvent21,favorableNextEvent22,favorableNextEvent23,favorableNextEvent24,favorableNextEvent25,favorableNextEvent26,favorableNextEvent27,favorableNextEvent28,favorableNextEvent29,taskReward]
    <;> norm_num
  have hp : rawVisits favorableNextS30Before [.query 1] = 6 := by decide
  have hn : rawVisits favorableNextS30Before ([.query 1]++[.hydeRetriever 0]) = 2 := by decide
  have hz : (controlPenalty savedCref uniformQuoteError unitRoleUnused .next) favorableNextS30Before [.query 1] (.hydeRetriever 0) = 0 := by
    apply control_penalty_empty_of_prior_terminal .next savedCref uniformQuoteError favorableNextS30Before [.query 1] (.hydeRetriever 0) 1 (by decide)
    · decide
    · decide
  unfold indexScore
  rw [hs,hp,hn,hz]
  simp only [BackupStat.mean]
  norm_num

theorem favorableNextS30D1I2 : indexScore (7/5) (controlPenalty savedCref uniformQuoteError unitRoleUnused .next) favorableNextS30Before [.query 1] (.hydeRetriever 2) = treeIndex ((0/1)/1) (7/5) 0 6 1 := by
  have hs : replayBackup favorableNextS30Before emptyStatistics ([.query 1]++[.hydeRetriever 2]) = ⟨1,(0/1)⟩ := by
    rw [replayBackup_empty_closed_form]
    simp +decide [backedEvents,favorableNextS30Before,favorableNextProposal,favorableNextEvent1,favorableNextEvent2,favorableNextEvent3,favorableNextEvent4,favorableNextEvent5,favorableNextEvent6,favorableNextEvent7,favorableNextEvent8,favorableNextEvent9,favorableNextEvent10,favorableNextEvent11,favorableNextEvent12,favorableNextEvent13,favorableNextEvent14,favorableNextEvent15,favorableNextEvent16,favorableNextEvent17,favorableNextEvent18,favorableNextEvent19,favorableNextEvent20,favorableNextEvent21,favorableNextEvent22,favorableNextEvent23,favorableNextEvent24,favorableNextEvent25,favorableNextEvent26,favorableNextEvent27,favorableNextEvent28,favorableNextEvent29,taskReward]
    <;> norm_num
  have hp : rawVisits favorableNextS30Before [.query 1] = 6 := by decide
  have hn : rawVisits favorableNextS30Before ([.query 1]++[.hydeRetriever 2]) = 1 := by decide
  have hz : (controlPenalty savedCref uniformQuoteError unitRoleUnused .next) favorableNextS30Before [.query 1] (.hydeRetriever 2) = 0 := by
    apply control_penalty_empty_of_prior_terminal .next savedCref uniformQuoteError favorableNextS30Before [.query 1] (.hydeRetriever 2) 18 (by decide)
    · decide
    · decide
  unfold indexScore
  rw [hs,hp,hn,hz]
  simp only [BackupStat.mean]
  norm_num

theorem favorableNextS30D1Cmp0 : indexScore (7/5) (controlPenalty savedCref uniformQuoteError unitRoleUnused .next) favorableNextS30Before [.query 1] (.hydeRetriever 1) < indexScore (7/5) (controlPenalty savedCref uniformQuoteError unitRoleUnused .next) favorableNextS30Before [.query 1] (.hydeRetriever 2) := by
  rw [favorableNextS30D1I0,favorableNextS30D1I2]
  have h := index_strict_order_from_intervals ((0/1)/1) ((1/1)/2) 0 0 (24411779/12500000) (69046943/50000000)
    (treeBonus (7/5) 6 1) (treeBonus (7/5) 6 2)
    (trajectory_bonus_6_1).1 (trajectory_bonus_6_2).2 (by norm_num)
  simpa only [treeIndex,sub_zero] using h

theorem favorableNextS30D1Cmp1 : indexScore (7/5) (controlPenalty savedCref uniformQuoteError unitRoleUnused .next) favorableNextS30Before [.query 1] (.hydeRetriever 0) < indexScore (7/5) (controlPenalty savedCref uniformQuoteError unitRoleUnused .next) favorableNextS30Before [.query 1] (.hydeRetriever 2) := by
  rw [favorableNextS30D1I1,favorableNextS30D1I2]
  have h := index_strict_order_from_intervals ((0/1)/1) ((0/1)/2) 0 0 (24411779/12500000) (69046943/50000000)
    (treeBonus (7/5) 6 1) (treeBonus (7/5) 6 2)
    (trajectory_bonus_6_1).1 (trajectory_bonus_6_2).2 (by norm_num)
  simpa only [treeIndex,sub_zero] using h

theorem favorableNextS30Choice1 : nativeFirstChoice (indexScore (7/5) (controlPenalty savedCref uniformQuoteError unitRoleUnused .next) favorableNextS30Before [.query 1]) favorableNextS30Before [.query 1] = .hydeRetriever 2 := by
  apply visited_choice_from_ordered_certificate _ _ [.query 1] [.hydeRetriever 1,.hydeRetriever 0] [] (.hydeRetriever 2) (by decide)
  · intro a ha
    have ho : orderedLegalAvailable [.query 1] = [.hydeRetriever 1,.hydeRetriever 0,.hydeRetriever 2] := by decide
    rw [ho] at ha
    simp only [List.mem_cons,List.not_mem_nil,or_false] at ha
    rcases ha with rfl | rfl | rfl <;> decide
  · intro a ha
    simp only [List.mem_cons,List.not_mem_nil,or_false] at ha
    rcases ha with rfl | rfl
    · exact favorableNextS30D1Cmp0
    · exact favorableNextS30D1Cmp1
  · simp

theorem favorableNextS30ActualEvent : nativeEvent budgetTape (7/5) (controlPenalty savedCref uniformQuoteError unitRoleUnused .next)
    (taskReward false (2/5) (1/2)) favorableNextS30Before = favorableNextEvent30 := by
  have hs0 := native_select_existing_step budgetTape (7/5) (controlPenalty savedCref uniformQuoteError unitRoleUnused .next) favorableNextS30Before 8 [] (.query 1)
    (by decide) (by decide) favorableNextS30Choice0
  have hs1 := native_select_existing_step budgetTape (7/5) (controlPenalty savedCref uniformQuoteError unitRoleUnused .next) favorableNextS30Before 7 [.query 1] (.hydeRetriever 2)
    (by decide) (by decide) favorableNextS30Choice1
  have hnew := native_select_new_step budgetTape (7/5) (controlPenalty savedCref uniformQuoteError unitRoleUnused .next) favorableNextS30Before 6 [.query 1,.hydeRetriever 2]
    [.selection 1,.selection 2,.selection 3,.selection 0] (.selection 0) (by decide) (by decide) (by decide) (by decide)
  have hs : nativeSelect budgetTape (7/5) (controlPenalty savedCref uniformQuoteError unitRoleUnused .next) favorableNextS30Before 9 [] = [.query 1,.hydeRetriever 2,.selection 0] := by
    rw [hs0]
    change nativeSelect budgetTape (7/5) (controlPenalty savedCref uniformQuoteError unitRoleUnused .next) favorableNextS30Before 8 [.query 1] = _
    rw [hs1]
    change nativeSelect budgetTape (7/5) (controlPenalty savedCref uniformQuoteError unitRoleUnused .next) favorableNextS30Before 7 [.query 1,.hydeRetriever 2] = _
    rw [hnew] <;> rfl
  have hr : repairedRollout budgetTape favorableNextS30Before 9 [.query 1,.hydeRetriever 2,.selection 0] = [.query 1,.hydeRetriever 2,.selection 0,.width 0,.stop,.reranker 0,.topm 2,.context 0,.answer 2] := by decide
  simp only [nativeEvent,hs,hr]
  rfl

def favorableNextS31Before := favorableNextProposal.take 30

theorem favorableNextS31D0I0 : indexScore (7/5) (controlPenalty savedCref uniformQuoteError unitRoleUnused .next) favorableNextS31Before [] (.query 0) = treeIndex ((0/1)/3) (7/5) (nextNormalPenalty favorableNextS31Before) 30 3 := by
  have hs : replayBackup favorableNextS31Before emptyStatistics ([]++[.query 0]) = ⟨3,(0/1)⟩ := by
    rw [replayBackup_empty_closed_form]
    simp +decide [backedEvents,favorableNextS31Before,favorableNextProposal,favorableNextEvent1,favorableNextEvent2,favorableNextEvent3,favorableNextEvent4,favorableNextEvent5,favorableNextEvent6,favorableNextEvent7,favorableNextEvent8,favorableNextEvent9,favorableNextEvent10,favorableNextEvent11,favorableNextEvent12,favorableNextEvent13,favorableNextEvent14,favorableNextEvent15,favorableNextEvent16,favorableNextEvent17,favorableNextEvent18,favorableNextEvent19,favorableNextEvent20,favorableNextEvent21,favorableNextEvent22,favorableNextEvent23,favorableNextEvent24,favorableNextEvent25,favorableNextEvent26,favorableNextEvent27,favorableNextEvent28,favorableNextEvent29,favorableNextEvent30,taskReward]
    <;> norm_num
  have hp : rawVisits favorableNextS31Before [] = 30 := by decide
  have hn : rawVisits favorableNextS31Before ([]++[.query 0]) = 3 := by decide
  have hz : (controlPenalty savedCref uniformQuoteError unitRoleUnused .next) favorableNextS31Before [] (.query 0) = (nextNormalPenalty favorableNextS31Before) := by
    simpa only [favorableNextS31Before,nextNormalPenalty] using AgentUCTNextExact.favorable_next_normal_root_quotes_exact 30 (by omega) 0 (by decide)
  unfold indexScore
  rw [hs,hp,hn,hz]
  simp only [BackupStat.mean]
  norm_num

theorem favorableNextS31D0I1 : indexScore (7/5) (controlPenalty savedCref uniformQuoteError unitRoleUnused .next) favorableNextS31Before [] (.query 1) = treeIndex ((1/1)/7) (7/5) 0 30 7 := by
  have hs : replayBackup favorableNextS31Before emptyStatistics ([]++[.query 1]) = ⟨7,(1/1)⟩ := by
    rw [replayBackup_empty_closed_form]
    simp +decide [backedEvents,favorableNextS31Before,favorableNextProposal,favorableNextEvent1,favorableNextEvent2,favorableNextEvent3,favorableNextEvent4,favorableNextEvent5,favorableNextEvent6,favorableNextEvent7,favorableNextEvent8,favorableNextEvent9,favorableNextEvent10,favorableNextEvent11,favorableNextEvent12,favorableNextEvent13,favorableNextEvent14,favorableNextEvent15,favorableNextEvent16,favorableNextEvent17,favorableNextEvent18,favorableNextEvent19,favorableNextEvent20,favorableNextEvent21,favorableNextEvent22,favorableNextEvent23,favorableNextEvent24,favorableNextEvent25,favorableNextEvent26,favorableNextEvent27,favorableNextEvent28,favorableNextEvent29,favorableNextEvent30,taskReward]
    <;> norm_num
  have hp : rawVisits favorableNextS31Before [] = 30 := by decide
  have hn : rawVisits favorableNextS31Before ([]++[.query 1]) = 7 := by decide
  have hz : (controlPenalty savedCref uniformQuoteError unitRoleUnused .next) favorableNextS31Before [] (.query 1) = 0 := by
    apply control_penalty_empty_suffix
    exact AgentUCTNextExact.favorable_next_hyde_root_suffix_empty 30 (by omega)
  unfold indexScore
  rw [hs,hp,hn,hz]
  simp only [BackupStat.mean]
  norm_num

theorem favorableNextS31D0I2 : indexScore (7/5) (controlPenalty savedCref uniformQuoteError unitRoleUnused .next) favorableNextS31Before [] (.query 2) = treeIndex ((0/1)/3) (7/5) (nextNormalPenalty favorableNextS31Before) 30 3 := by
  have hs : replayBackup favorableNextS31Before emptyStatistics ([]++[.query 2]) = ⟨3,(0/1)⟩ := by
    rw [replayBackup_empty_closed_form]
    simp +decide [backedEvents,favorableNextS31Before,favorableNextProposal,favorableNextEvent1,favorableNextEvent2,favorableNextEvent3,favorableNextEvent4,favorableNextEvent5,favorableNextEvent6,favorableNextEvent7,favorableNextEvent8,favorableNextEvent9,favorableNextEvent10,favorableNextEvent11,favorableNextEvent12,favorableNextEvent13,favorableNextEvent14,favorableNextEvent15,favorableNextEvent16,favorableNextEvent17,favorableNextEvent18,favorableNextEvent19,favorableNextEvent20,favorableNextEvent21,favorableNextEvent22,favorableNextEvent23,favorableNextEvent24,favorableNextEvent25,favorableNextEvent26,favorableNextEvent27,favorableNextEvent28,favorableNextEvent29,favorableNextEvent30,taskReward]
    <;> norm_num
  have hp : rawVisits favorableNextS31Before [] = 30 := by decide
  have hn : rawVisits favorableNextS31Before ([]++[.query 2]) = 3 := by decide
  have hz : (controlPenalty savedCref uniformQuoteError unitRoleUnused .next) favorableNextS31Before [] (.query 2) = (nextNormalPenalty favorableNextS31Before) := by
    simpa only [favorableNextS31Before,nextNormalPenalty] using AgentUCTNextExact.favorable_next_normal_root_quotes_exact 30 (by omega) 2 (by decide)
  unfold indexScore
  rw [hs,hp,hn,hz]
  simp only [BackupStat.mean]
  norm_num

theorem favorableNextS31D0I3 : indexScore (7/5) (controlPenalty savedCref uniformQuoteError unitRoleUnused .next) favorableNextS31Before [] (.query 3) = treeIndex ((0/1)/3) (7/5) (nextNormalPenalty favorableNextS31Before) 30 3 := by
  have hs : replayBackup favorableNextS31Before emptyStatistics ([]++[.query 3]) = ⟨3,(0/1)⟩ := by
    rw [replayBackup_empty_closed_form]
    simp +decide [backedEvents,favorableNextS31Before,favorableNextProposal,favorableNextEvent1,favorableNextEvent2,favorableNextEvent3,favorableNextEvent4,favorableNextEvent5,favorableNextEvent6,favorableNextEvent7,favorableNextEvent8,favorableNextEvent9,favorableNextEvent10,favorableNextEvent11,favorableNextEvent12,favorableNextEvent13,favorableNextEvent14,favorableNextEvent15,favorableNextEvent16,favorableNextEvent17,favorableNextEvent18,favorableNextEvent19,favorableNextEvent20,favorableNextEvent21,favorableNextEvent22,favorableNextEvent23,favorableNextEvent24,favorableNextEvent25,favorableNextEvent26,favorableNextEvent27,favorableNextEvent28,favorableNextEvent29,favorableNextEvent30,taskReward]
    <;> norm_num
  have hp : rawVisits favorableNextS31Before [] = 30 := by decide
  have hn : rawVisits favorableNextS31Before ([]++[.query 3]) = 3 := by decide
  have hz : (controlPenalty savedCref uniformQuoteError unitRoleUnused .next) favorableNextS31Before [] (.query 3) = (nextNormalPenalty favorableNextS31Before) := by
    simpa only [favorableNextS31Before,nextNormalPenalty] using AgentUCTNextExact.favorable_next_normal_root_quotes_exact 30 (by omega) 3 (by decide)
  unfold indexScore
  rw [hs,hp,hn,hz]
  simp only [BackupStat.mean]
  norm_num

theorem favorableNextS31D0I4 : indexScore (7/5) (controlPenalty savedCref uniformQuoteError unitRoleUnused .next) favorableNextS31Before [] (.query 4) = treeIndex ((0/1)/3) (7/5) (nextNormalPenalty favorableNextS31Before) 30 3 := by
  have hs : replayBackup favorableNextS31Before emptyStatistics ([]++[.query 4]) = ⟨3,(0/1)⟩ := by
    rw [replayBackup_empty_closed_form]
    simp +decide [backedEvents,favorableNextS31Before,favorableNextProposal,favorableNextEvent1,favorableNextEvent2,favorableNextEvent3,favorableNextEvent4,favorableNextEvent5,favorableNextEvent6,favorableNextEvent7,favorableNextEvent8,favorableNextEvent9,favorableNextEvent10,favorableNextEvent11,favorableNextEvent12,favorableNextEvent13,favorableNextEvent14,favorableNextEvent15,favorableNextEvent16,favorableNextEvent17,favorableNextEvent18,favorableNextEvent19,favorableNextEvent20,favorableNextEvent21,favorableNextEvent22,favorableNextEvent23,favorableNextEvent24,favorableNextEvent25,favorableNextEvent26,favorableNextEvent27,favorableNextEvent28,favorableNextEvent29,favorableNextEvent30,taskReward]
    <;> norm_num
  have hp : rawVisits favorableNextS31Before [] = 30 := by decide
  have hn : rawVisits favorableNextS31Before ([]++[.query 4]) = 3 := by decide
  have hz : (controlPenalty savedCref uniformQuoteError unitRoleUnused .next) favorableNextS31Before [] (.query 4) = (nextNormalPenalty favorableNextS31Before) := by
    simpa only [favorableNextS31Before,nextNormalPenalty] using AgentUCTNextExact.favorable_next_normal_root_quotes_exact 30 (by omega) 4 (by decide)
  unfold indexScore
  rw [hs,hp,hn,hz]
  simp only [BackupStat.mean]
  norm_num

theorem favorableNextS31D0I5 : indexScore (7/5) (controlPenalty savedCref uniformQuoteError unitRoleUnused .next) favorableNextS31Before [] (.query 5) = treeIndex ((6/5)/5) (7/5) (nextNormalPenalty favorableNextS31Before) 30 5 := by
  have hs : replayBackup favorableNextS31Before emptyStatistics ([]++[.query 5]) = ⟨5,(6/5)⟩ := by
    rw [replayBackup_empty_closed_form]
    simp +decide [backedEvents,favorableNextS31Before,favorableNextProposal,favorableNextEvent1,favorableNextEvent2,favorableNextEvent3,favorableNextEvent4,favorableNextEvent5,favorableNextEvent6,favorableNextEvent7,favorableNextEvent8,favorableNextEvent9,favorableNextEvent10,favorableNextEvent11,favorableNextEvent12,favorableNextEvent13,favorableNextEvent14,favorableNextEvent15,favorableNextEvent16,favorableNextEvent17,favorableNextEvent18,favorableNextEvent19,favorableNextEvent20,favorableNextEvent21,favorableNextEvent22,favorableNextEvent23,favorableNextEvent24,favorableNextEvent25,favorableNextEvent26,favorableNextEvent27,favorableNextEvent28,favorableNextEvent29,favorableNextEvent30,taskReward]
    <;> norm_num
  have hp : rawVisits favorableNextS31Before [] = 30 := by decide
  have hn : rawVisits favorableNextS31Before ([]++[.query 5]) = 5 := by decide
  have hz : (controlPenalty savedCref uniformQuoteError unitRoleUnused .next) favorableNextS31Before [] (.query 5) = (nextNormalPenalty favorableNextS31Before) := by
    simpa only [favorableNextS31Before,nextNormalPenalty] using AgentUCTNextExact.favorable_next_normal_root_quotes_exact 30 (by omega) 5 (by decide)
  unfold indexScore
  rw [hs,hp,hn,hz]
  simp only [BackupStat.mean]
  norm_num

theorem favorableNextS31D0I6 : indexScore (7/5) (controlPenalty savedCref uniformQuoteError unitRoleUnused .next) favorableNextS31Before [] (.query 6) = treeIndex ((0/1)/3) (7/5) (nextNormalPenalty favorableNextS31Before) 30 3 := by
  have hs : replayBackup favorableNextS31Before emptyStatistics ([]++[.query 6]) = ⟨3,(0/1)⟩ := by
    rw [replayBackup_empty_closed_form]
    simp +decide [backedEvents,favorableNextS31Before,favorableNextProposal,favorableNextEvent1,favorableNextEvent2,favorableNextEvent3,favorableNextEvent4,favorableNextEvent5,favorableNextEvent6,favorableNextEvent7,favorableNextEvent8,favorableNextEvent9,favorableNextEvent10,favorableNextEvent11,favorableNextEvent12,favorableNextEvent13,favorableNextEvent14,favorableNextEvent15,favorableNextEvent16,favorableNextEvent17,favorableNextEvent18,favorableNextEvent19,favorableNextEvent20,favorableNextEvent21,favorableNextEvent22,favorableNextEvent23,favorableNextEvent24,favorableNextEvent25,favorableNextEvent26,favorableNextEvent27,favorableNextEvent28,favorableNextEvent29,favorableNextEvent30,taskReward]
    <;> norm_num
  have hp : rawVisits favorableNextS31Before [] = 30 := by decide
  have hn : rawVisits favorableNextS31Before ([]++[.query 6]) = 3 := by decide
  have hz : (controlPenalty savedCref uniformQuoteError unitRoleUnused .next) favorableNextS31Before [] (.query 6) = (nextNormalPenalty favorableNextS31Before) := by
    simpa only [favorableNextS31Before,nextNormalPenalty] using AgentUCTNextExact.favorable_next_normal_root_quotes_exact 30 (by omega) 6 (by decide)
  unfold indexScore
  rw [hs,hp,hn,hz]
  simp only [BackupStat.mean]
  norm_num

theorem favorableNextS31D0I7 : indexScore (7/5) (controlPenalty savedCref uniformQuoteError unitRoleUnused .next) favorableNextS31Before [] (.query 7) = treeIndex ((0/1)/3) (7/5) (nextNormalPenalty favorableNextS31Before) 30 3 := by
  have hs : replayBackup favorableNextS31Before emptyStatistics ([]++[.query 7]) = ⟨3,(0/1)⟩ := by
    rw [replayBackup_empty_closed_form]
    simp +decide [backedEvents,favorableNextS31Before,favorableNextProposal,favorableNextEvent1,favorableNextEvent2,favorableNextEvent3,favorableNextEvent4,favorableNextEvent5,favorableNextEvent6,favorableNextEvent7,favorableNextEvent8,favorableNextEvent9,favorableNextEvent10,favorableNextEvent11,favorableNextEvent12,favorableNextEvent13,favorableNextEvent14,favorableNextEvent15,favorableNextEvent16,favorableNextEvent17,favorableNextEvent18,favorableNextEvent19,favorableNextEvent20,favorableNextEvent21,favorableNextEvent22,favorableNextEvent23,favorableNextEvent24,favorableNextEvent25,favorableNextEvent26,favorableNextEvent27,favorableNextEvent28,favorableNextEvent29,favorableNextEvent30,taskReward]
    <;> norm_num
  have hp : rawVisits favorableNextS31Before [] = 30 := by decide
  have hn : rawVisits favorableNextS31Before ([]++[.query 7]) = 3 := by decide
  have hz : (controlPenalty savedCref uniformQuoteError unitRoleUnused .next) favorableNextS31Before [] (.query 7) = (nextNormalPenalty favorableNextS31Before) := by
    simpa only [favorableNextS31Before,nextNormalPenalty] using AgentUCTNextExact.favorable_next_normal_root_quotes_exact 30 (by omega) 7 (by decide)
  unfold indexScore
  rw [hs,hp,hn,hz]
  simp only [BackupStat.mean]
  norm_num

theorem favorableNextS31D0Cmp1 : indexScore (7/5) (controlPenalty savedCref uniformQuoteError unitRoleUnused .next) favorableNextS31Before [] (.query 1) ≤ indexScore (7/5) (controlPenalty savedCref uniformQuoteError unitRoleUnused .next) favorableNextS31Before [] (.query 0) := by
  rw [favorableNextS31D0I1,favorableNextS31D0I0]
  have hk := favorable_next_penalty_interval 30 (by omega)
  change nextNormalPenaltyLower ≤ nextNormalPenalty favorableNextS31Before ∧ nextNormalPenalty favorableNextS31Before ≤ nextNormalPenaltyUpper at hk
  have hm : ((1/1)/7)+(12257119/12500000)-0 < ((0/1)/3)+(74892223/50000000)-(nextNormalPenalty favorableNextS31Before) := by
    have h : ((1/1)/7)+(12257119/12500000) < ((0/1)/3)+(74892223/50000000)-nextNormalPenaltyUpper := by norm_num [nextNormalPenaltyUpper,savedCref,uniformQuoteError]
    linarith [hk.2]
  have h := index_weak_order_from_intervals ((0/1)/3) ((1/1)/7) (nextNormalPenalty favorableNextS31Before) 0 (74892223/50000000) (12257119/12500000)
    (treeBonus (7/5) 30 3) (treeBonus (7/5) 30 7)
    (trajectory_bonus_30_3).1 (trajectory_bonus_30_7).2 hm.le
  simpa only [treeIndex] using h

theorem favorableNextS31D0Cmp2 : indexScore (7/5) (controlPenalty savedCref uniformQuoteError unitRoleUnused .next) favorableNextS31Before [] (.query 2) ≤ indexScore (7/5) (controlPenalty savedCref uniformQuoteError unitRoleUnused .next) favorableNextS31Before [] (.query 0) := by
  rw [favorableNextS31D0I2,favorableNextS31D0I0]

theorem favorableNextS31D0Cmp3 : indexScore (7/5) (controlPenalty savedCref uniformQuoteError unitRoleUnused .next) favorableNextS31Before [] (.query 3) ≤ indexScore (7/5) (controlPenalty savedCref uniformQuoteError unitRoleUnused .next) favorableNextS31Before [] (.query 0) := by
  rw [favorableNextS31D0I3,favorableNextS31D0I0]

theorem favorableNextS31D0Cmp4 : indexScore (7/5) (controlPenalty savedCref uniformQuoteError unitRoleUnused .next) favorableNextS31Before [] (.query 4) ≤ indexScore (7/5) (controlPenalty savedCref uniformQuoteError unitRoleUnused .next) favorableNextS31Before [] (.query 0) := by
  rw [favorableNextS31D0I4,favorableNextS31D0I0]

theorem favorableNextS31D0Cmp5 : indexScore (7/5) (controlPenalty savedCref uniformQuoteError unitRoleUnused .next) favorableNextS31Before [] (.query 5) ≤ indexScore (7/5) (controlPenalty savedCref uniformQuoteError unitRoleUnused .next) favorableNextS31Before [] (.query 0) := by
  rw [favorableNextS31D0I5,favorableNextS31D0I0]
  have hk := favorable_next_penalty_interval 30 (by omega)
  change nextNormalPenaltyLower ≤ nextNormalPenalty favorableNextS31Before ∧ nextNormalPenalty favorableNextS31Before ≤ nextNormalPenaltyUpper at hk
  have hm : ((6/5)/5)+(2320451/2000000)-(nextNormalPenalty favorableNextS31Before) < ((0/1)/3)+(74892223/50000000)-(nextNormalPenalty favorableNextS31Before) := by
    have h : (((6/5)/5)+(2320451/2000000) : ℝ) < ((0/1)/3)+(74892223/50000000) := by norm_num
    linarith
  have h := index_weak_order_from_intervals ((0/1)/3) ((6/5)/5) (nextNormalPenalty favorableNextS31Before) (nextNormalPenalty favorableNextS31Before) (74892223/50000000) (2320451/2000000)
    (treeBonus (7/5) 30 3) (treeBonus (7/5) 30 5)
    (trajectory_bonus_30_3).1 (trajectory_bonus_30_5).2 hm.le
  simpa only [treeIndex] using h

theorem favorableNextS31D0Cmp6 : indexScore (7/5) (controlPenalty savedCref uniformQuoteError unitRoleUnused .next) favorableNextS31Before [] (.query 6) ≤ indexScore (7/5) (controlPenalty savedCref uniformQuoteError unitRoleUnused .next) favorableNextS31Before [] (.query 0) := by
  rw [favorableNextS31D0I6,favorableNextS31D0I0]

theorem favorableNextS31D0Cmp7 : indexScore (7/5) (controlPenalty savedCref uniformQuoteError unitRoleUnused .next) favorableNextS31Before [] (.query 7) ≤ indexScore (7/5) (controlPenalty savedCref uniformQuoteError unitRoleUnused .next) favorableNextS31Before [] (.query 0) := by
  rw [favorableNextS31D0I7,favorableNextS31D0I0]

theorem favorableNextS31Choice0 : nativeFirstChoice (indexScore (7/5) (controlPenalty savedCref uniformQuoteError unitRoleUnused .next) favorableNextS31Before []) favorableNextS31Before [] = .query 0 := by
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
    · exact favorableNextS31D0Cmp1
    · exact favorableNextS31D0Cmp2
    · exact favorableNextS31D0Cmp3
    · exact favorableNextS31D0Cmp4
    · exact favorableNextS31D0Cmp5
    · exact favorableNextS31D0Cmp6
    · exact favorableNextS31D0Cmp7

theorem favorableNextS31ActualEvent : nativeEvent budgetTape (7/5) (controlPenalty savedCref uniformQuoteError unitRoleUnused .next)
    (taskReward false (2/5) (1/2)) favorableNextS31Before = favorableNextEvent31 := by
  have hs0 := native_select_existing_step budgetTape (7/5) (controlPenalty savedCref uniformQuoteError unitRoleUnused .next) favorableNextS31Before 8 [] (.query 0)
    (by decide) (by decide) favorableNextS31Choice0
  have hnew := native_select_new_step budgetTape (7/5) (controlPenalty savedCref uniformQuoteError unitRoleUnused .next) favorableNextS31Before 7 [.query 0]
    [.normalRetriever 6,.normalRetriever 7,.normalRetriever 8,.normalRetriever 5,.normalRetriever 1,.normalRetriever 2,.normalRetriever 3,.normalRetriever 12,.normalRetriever 14,.normalRetriever 13,.normalRetriever 21,.normalRetriever 23,.normalRetriever 22,.normalRetriever 9,.normalRetriever 11,.normalRetriever 10,.normalRetriever 15,.normalRetriever 17,.normalRetriever 16,.normalRetriever 18,.normalRetriever 20,.normalRetriever 19,.normalRetriever 24,.normalRetriever 25,.normalRetriever 26,.normalRetriever 27,.normalRetriever 28,.normalRetriever 29] (.normalRetriever 6) (by decide) (by decide) (by decide) (by decide)
  have hs : nativeSelect budgetTape (7/5) (controlPenalty savedCref uniformQuoteError unitRoleUnused .next) favorableNextS31Before 9 [] = [.query 0,.normalRetriever 6] := by
    rw [hs0]
    change nativeSelect budgetTape (7/5) (controlPenalty savedCref uniformQuoteError unitRoleUnused .next) favorableNextS31Before 8 [.query 0] = _
    rw [hnew] <;> rfl
  have hr : repairedRollout budgetTape favorableNextS31Before 9 [.query 0,.normalRetriever 6] = [.query 0,.normalRetriever 6,.selection 0,.width 0,.stop,.reranker 0,.topm 0,.context 0,.answer 0] := by decide
  simp only [nativeEvent,hs,hr]
  rfl

def favorableNextS32Before := favorableNextProposal.take 31

theorem favorableNextS32D0I0 : indexScore (7/5) (controlPenalty savedCref uniformQuoteError unitRoleUnused .next) favorableNextS32Before [] (.query 0) = treeIndex ((0/1)/4) (7/5) (nextNormalPenalty favorableNextS32Before) 31 4 := by
  have hs : replayBackup favorableNextS32Before emptyStatistics ([]++[.query 0]) = ⟨4,(0/1)⟩ := by
    rw [replayBackup_empty_closed_form]
    simp +decide [backedEvents,favorableNextS32Before,favorableNextProposal,favorableNextEvent1,favorableNextEvent2,favorableNextEvent3,favorableNextEvent4,favorableNextEvent5,favorableNextEvent6,favorableNextEvent7,favorableNextEvent8,favorableNextEvent9,favorableNextEvent10,favorableNextEvent11,favorableNextEvent12,favorableNextEvent13,favorableNextEvent14,favorableNextEvent15,favorableNextEvent16,favorableNextEvent17,favorableNextEvent18,favorableNextEvent19,favorableNextEvent20,favorableNextEvent21,favorableNextEvent22,favorableNextEvent23,favorableNextEvent24,favorableNextEvent25,favorableNextEvent26,favorableNextEvent27,favorableNextEvent28,favorableNextEvent29,favorableNextEvent30,favorableNextEvent31,taskReward]
    <;> norm_num
  have hp : rawVisits favorableNextS32Before [] = 31 := by decide
  have hn : rawVisits favorableNextS32Before ([]++[.query 0]) = 4 := by decide
  have hz : (controlPenalty savedCref uniformQuoteError unitRoleUnused .next) favorableNextS32Before [] (.query 0) = (nextNormalPenalty favorableNextS32Before) := by
    simpa only [favorableNextS32Before,nextNormalPenalty] using AgentUCTNextExact.favorable_next_normal_root_quotes_exact 31 (by omega) 0 (by decide)
  unfold indexScore
  rw [hs,hp,hn,hz]
  simp only [BackupStat.mean]
  norm_num

theorem favorableNextS32D0I1 : indexScore (7/5) (controlPenalty savedCref uniformQuoteError unitRoleUnused .next) favorableNextS32Before [] (.query 1) = treeIndex ((1/1)/7) (7/5) 0 31 7 := by
  have hs : replayBackup favorableNextS32Before emptyStatistics ([]++[.query 1]) = ⟨7,(1/1)⟩ := by
    rw [replayBackup_empty_closed_form]
    simp +decide [backedEvents,favorableNextS32Before,favorableNextProposal,favorableNextEvent1,favorableNextEvent2,favorableNextEvent3,favorableNextEvent4,favorableNextEvent5,favorableNextEvent6,favorableNextEvent7,favorableNextEvent8,favorableNextEvent9,favorableNextEvent10,favorableNextEvent11,favorableNextEvent12,favorableNextEvent13,favorableNextEvent14,favorableNextEvent15,favorableNextEvent16,favorableNextEvent17,favorableNextEvent18,favorableNextEvent19,favorableNextEvent20,favorableNextEvent21,favorableNextEvent22,favorableNextEvent23,favorableNextEvent24,favorableNextEvent25,favorableNextEvent26,favorableNextEvent27,favorableNextEvent28,favorableNextEvent29,favorableNextEvent30,favorableNextEvent31,taskReward]
    <;> norm_num
  have hp : rawVisits favorableNextS32Before [] = 31 := by decide
  have hn : rawVisits favorableNextS32Before ([]++[.query 1]) = 7 := by decide
  have hz : (controlPenalty savedCref uniformQuoteError unitRoleUnused .next) favorableNextS32Before [] (.query 1) = 0 := by
    apply control_penalty_empty_suffix
    exact AgentUCTNextExact.favorable_next_hyde_root_suffix_empty 31 (by omega)
  unfold indexScore
  rw [hs,hp,hn,hz]
  simp only [BackupStat.mean]
  norm_num

theorem favorableNextS32D0I2 : indexScore (7/5) (controlPenalty savedCref uniformQuoteError unitRoleUnused .next) favorableNextS32Before [] (.query 2) = treeIndex ((0/1)/3) (7/5) (nextNormalPenalty favorableNextS32Before) 31 3 := by
  have hs : replayBackup favorableNextS32Before emptyStatistics ([]++[.query 2]) = ⟨3,(0/1)⟩ := by
    rw [replayBackup_empty_closed_form]
    simp +decide [backedEvents,favorableNextS32Before,favorableNextProposal,favorableNextEvent1,favorableNextEvent2,favorableNextEvent3,favorableNextEvent4,favorableNextEvent5,favorableNextEvent6,favorableNextEvent7,favorableNextEvent8,favorableNextEvent9,favorableNextEvent10,favorableNextEvent11,favorableNextEvent12,favorableNextEvent13,favorableNextEvent14,favorableNextEvent15,favorableNextEvent16,favorableNextEvent17,favorableNextEvent18,favorableNextEvent19,favorableNextEvent20,favorableNextEvent21,favorableNextEvent22,favorableNextEvent23,favorableNextEvent24,favorableNextEvent25,favorableNextEvent26,favorableNextEvent27,favorableNextEvent28,favorableNextEvent29,favorableNextEvent30,favorableNextEvent31,taskReward]
    <;> norm_num
  have hp : rawVisits favorableNextS32Before [] = 31 := by decide
  have hn : rawVisits favorableNextS32Before ([]++[.query 2]) = 3 := by decide
  have hz : (controlPenalty savedCref uniformQuoteError unitRoleUnused .next) favorableNextS32Before [] (.query 2) = (nextNormalPenalty favorableNextS32Before) := by
    simpa only [favorableNextS32Before,nextNormalPenalty] using AgentUCTNextExact.favorable_next_normal_root_quotes_exact 31 (by omega) 2 (by decide)
  unfold indexScore
  rw [hs,hp,hn,hz]
  simp only [BackupStat.mean]
  norm_num

theorem favorableNextS32D0I3 : indexScore (7/5) (controlPenalty savedCref uniformQuoteError unitRoleUnused .next) favorableNextS32Before [] (.query 3) = treeIndex ((0/1)/3) (7/5) (nextNormalPenalty favorableNextS32Before) 31 3 := by
  have hs : replayBackup favorableNextS32Before emptyStatistics ([]++[.query 3]) = ⟨3,(0/1)⟩ := by
    rw [replayBackup_empty_closed_form]
    simp +decide [backedEvents,favorableNextS32Before,favorableNextProposal,favorableNextEvent1,favorableNextEvent2,favorableNextEvent3,favorableNextEvent4,favorableNextEvent5,favorableNextEvent6,favorableNextEvent7,favorableNextEvent8,favorableNextEvent9,favorableNextEvent10,favorableNextEvent11,favorableNextEvent12,favorableNextEvent13,favorableNextEvent14,favorableNextEvent15,favorableNextEvent16,favorableNextEvent17,favorableNextEvent18,favorableNextEvent19,favorableNextEvent20,favorableNextEvent21,favorableNextEvent22,favorableNextEvent23,favorableNextEvent24,favorableNextEvent25,favorableNextEvent26,favorableNextEvent27,favorableNextEvent28,favorableNextEvent29,favorableNextEvent30,favorableNextEvent31,taskReward]
    <;> norm_num
  have hp : rawVisits favorableNextS32Before [] = 31 := by decide
  have hn : rawVisits favorableNextS32Before ([]++[.query 3]) = 3 := by decide
  have hz : (controlPenalty savedCref uniformQuoteError unitRoleUnused .next) favorableNextS32Before [] (.query 3) = (nextNormalPenalty favorableNextS32Before) := by
    simpa only [favorableNextS32Before,nextNormalPenalty] using AgentUCTNextExact.favorable_next_normal_root_quotes_exact 31 (by omega) 3 (by decide)
  unfold indexScore
  rw [hs,hp,hn,hz]
  simp only [BackupStat.mean]
  norm_num

theorem favorableNextS32D0I4 : indexScore (7/5) (controlPenalty savedCref uniformQuoteError unitRoleUnused .next) favorableNextS32Before [] (.query 4) = treeIndex ((0/1)/3) (7/5) (nextNormalPenalty favorableNextS32Before) 31 3 := by
  have hs : replayBackup favorableNextS32Before emptyStatistics ([]++[.query 4]) = ⟨3,(0/1)⟩ := by
    rw [replayBackup_empty_closed_form]
    simp +decide [backedEvents,favorableNextS32Before,favorableNextProposal,favorableNextEvent1,favorableNextEvent2,favorableNextEvent3,favorableNextEvent4,favorableNextEvent5,favorableNextEvent6,favorableNextEvent7,favorableNextEvent8,favorableNextEvent9,favorableNextEvent10,favorableNextEvent11,favorableNextEvent12,favorableNextEvent13,favorableNextEvent14,favorableNextEvent15,favorableNextEvent16,favorableNextEvent17,favorableNextEvent18,favorableNextEvent19,favorableNextEvent20,favorableNextEvent21,favorableNextEvent22,favorableNextEvent23,favorableNextEvent24,favorableNextEvent25,favorableNextEvent26,favorableNextEvent27,favorableNextEvent28,favorableNextEvent29,favorableNextEvent30,favorableNextEvent31,taskReward]
    <;> norm_num
  have hp : rawVisits favorableNextS32Before [] = 31 := by decide
  have hn : rawVisits favorableNextS32Before ([]++[.query 4]) = 3 := by decide
  have hz : (controlPenalty savedCref uniformQuoteError unitRoleUnused .next) favorableNextS32Before [] (.query 4) = (nextNormalPenalty favorableNextS32Before) := by
    simpa only [favorableNextS32Before,nextNormalPenalty] using AgentUCTNextExact.favorable_next_normal_root_quotes_exact 31 (by omega) 4 (by decide)
  unfold indexScore
  rw [hs,hp,hn,hz]
  simp only [BackupStat.mean]
  norm_num

theorem favorableNextS32D0I5 : indexScore (7/5) (controlPenalty savedCref uniformQuoteError unitRoleUnused .next) favorableNextS32Before [] (.query 5) = treeIndex ((6/5)/5) (7/5) (nextNormalPenalty favorableNextS32Before) 31 5 := by
  have hs : replayBackup favorableNextS32Before emptyStatistics ([]++[.query 5]) = ⟨5,(6/5)⟩ := by
    rw [replayBackup_empty_closed_form]
    simp +decide [backedEvents,favorableNextS32Before,favorableNextProposal,favorableNextEvent1,favorableNextEvent2,favorableNextEvent3,favorableNextEvent4,favorableNextEvent5,favorableNextEvent6,favorableNextEvent7,favorableNextEvent8,favorableNextEvent9,favorableNextEvent10,favorableNextEvent11,favorableNextEvent12,favorableNextEvent13,favorableNextEvent14,favorableNextEvent15,favorableNextEvent16,favorableNextEvent17,favorableNextEvent18,favorableNextEvent19,favorableNextEvent20,favorableNextEvent21,favorableNextEvent22,favorableNextEvent23,favorableNextEvent24,favorableNextEvent25,favorableNextEvent26,favorableNextEvent27,favorableNextEvent28,favorableNextEvent29,favorableNextEvent30,favorableNextEvent31,taskReward]
    <;> norm_num
  have hp : rawVisits favorableNextS32Before [] = 31 := by decide
  have hn : rawVisits favorableNextS32Before ([]++[.query 5]) = 5 := by decide
  have hz : (controlPenalty savedCref uniformQuoteError unitRoleUnused .next) favorableNextS32Before [] (.query 5) = (nextNormalPenalty favorableNextS32Before) := by
    simpa only [favorableNextS32Before,nextNormalPenalty] using AgentUCTNextExact.favorable_next_normal_root_quotes_exact 31 (by omega) 5 (by decide)
  unfold indexScore
  rw [hs,hp,hn,hz]
  simp only [BackupStat.mean]
  norm_num

theorem favorableNextS32D0I6 : indexScore (7/5) (controlPenalty savedCref uniformQuoteError unitRoleUnused .next) favorableNextS32Before [] (.query 6) = treeIndex ((0/1)/3) (7/5) (nextNormalPenalty favorableNextS32Before) 31 3 := by
  have hs : replayBackup favorableNextS32Before emptyStatistics ([]++[.query 6]) = ⟨3,(0/1)⟩ := by
    rw [replayBackup_empty_closed_form]
    simp +decide [backedEvents,favorableNextS32Before,favorableNextProposal,favorableNextEvent1,favorableNextEvent2,favorableNextEvent3,favorableNextEvent4,favorableNextEvent5,favorableNextEvent6,favorableNextEvent7,favorableNextEvent8,favorableNextEvent9,favorableNextEvent10,favorableNextEvent11,favorableNextEvent12,favorableNextEvent13,favorableNextEvent14,favorableNextEvent15,favorableNextEvent16,favorableNextEvent17,favorableNextEvent18,favorableNextEvent19,favorableNextEvent20,favorableNextEvent21,favorableNextEvent22,favorableNextEvent23,favorableNextEvent24,favorableNextEvent25,favorableNextEvent26,favorableNextEvent27,favorableNextEvent28,favorableNextEvent29,favorableNextEvent30,favorableNextEvent31,taskReward]
    <;> norm_num
  have hp : rawVisits favorableNextS32Before [] = 31 := by decide
  have hn : rawVisits favorableNextS32Before ([]++[.query 6]) = 3 := by decide
  have hz : (controlPenalty savedCref uniformQuoteError unitRoleUnused .next) favorableNextS32Before [] (.query 6) = (nextNormalPenalty favorableNextS32Before) := by
    simpa only [favorableNextS32Before,nextNormalPenalty] using AgentUCTNextExact.favorable_next_normal_root_quotes_exact 31 (by omega) 6 (by decide)
  unfold indexScore
  rw [hs,hp,hn,hz]
  simp only [BackupStat.mean]
  norm_num

theorem favorableNextS32D0I7 : indexScore (7/5) (controlPenalty savedCref uniformQuoteError unitRoleUnused .next) favorableNextS32Before [] (.query 7) = treeIndex ((0/1)/3) (7/5) (nextNormalPenalty favorableNextS32Before) 31 3 := by
  have hs : replayBackup favorableNextS32Before emptyStatistics ([]++[.query 7]) = ⟨3,(0/1)⟩ := by
    rw [replayBackup_empty_closed_form]
    simp +decide [backedEvents,favorableNextS32Before,favorableNextProposal,favorableNextEvent1,favorableNextEvent2,favorableNextEvent3,favorableNextEvent4,favorableNextEvent5,favorableNextEvent6,favorableNextEvent7,favorableNextEvent8,favorableNextEvent9,favorableNextEvent10,favorableNextEvent11,favorableNextEvent12,favorableNextEvent13,favorableNextEvent14,favorableNextEvent15,favorableNextEvent16,favorableNextEvent17,favorableNextEvent18,favorableNextEvent19,favorableNextEvent20,favorableNextEvent21,favorableNextEvent22,favorableNextEvent23,favorableNextEvent24,favorableNextEvent25,favorableNextEvent26,favorableNextEvent27,favorableNextEvent28,favorableNextEvent29,favorableNextEvent30,favorableNextEvent31,taskReward]
    <;> norm_num
  have hp : rawVisits favorableNextS32Before [] = 31 := by decide
  have hn : rawVisits favorableNextS32Before ([]++[.query 7]) = 3 := by decide
  have hz : (controlPenalty savedCref uniformQuoteError unitRoleUnused .next) favorableNextS32Before [] (.query 7) = (nextNormalPenalty favorableNextS32Before) := by
    simpa only [favorableNextS32Before,nextNormalPenalty] using AgentUCTNextExact.favorable_next_normal_root_quotes_exact 31 (by omega) 7 (by decide)
  unfold indexScore
  rw [hs,hp,hn,hz]
  simp only [BackupStat.mean]
  norm_num

theorem favorableNextS32D0Cmp0 : indexScore (7/5) (controlPenalty savedCref uniformQuoteError unitRoleUnused .next) favorableNextS32Before [] (.query 0) < indexScore (7/5) (controlPenalty savedCref uniformQuoteError unitRoleUnused .next) favorableNextS32Before [] (.query 2) := by
  rw [favorableNextS32D0I0,favorableNextS32D0I2]
  have hk := favorable_next_penalty_interval 31 (by omega)
  change nextNormalPenaltyLower ≤ nextNormalPenalty favorableNextS32Before ∧ nextNormalPenalty favorableNextS32Before ≤ nextNormalPenaltyUpper at hk
  have hm : ((0/1)/4)+(16289427/12500000)-(nextNormalPenalty favorableNextS32Before) < ((0/1)/3)+(75237631/50000000)-(nextNormalPenalty favorableNextS32Before) := by
    have h : (((0/1)/4)+(16289427/12500000) : ℝ) < ((0/1)/3)+(75237631/50000000) := by norm_num
    linarith
  have h := index_strict_order_from_intervals ((0/1)/3) ((0/1)/4) (nextNormalPenalty favorableNextS32Before) (nextNormalPenalty favorableNextS32Before) (75237631/50000000) (16289427/12500000)
    (treeBonus (7/5) 31 3) (treeBonus (7/5) 31 4)
    (trajectory_bonus_31_3).1 (trajectory_bonus_31_4).2 hm
  simpa only [treeIndex] using h

theorem favorableNextS32D0Cmp1 : indexScore (7/5) (controlPenalty savedCref uniformQuoteError unitRoleUnused .next) favorableNextS32Before [] (.query 1) < indexScore (7/5) (controlPenalty savedCref uniformQuoteError unitRoleUnused .next) favorableNextS32Before [] (.query 2) := by
  rw [favorableNextS32D0I1,favorableNextS32D0I2]
  have hk := favorable_next_penalty_interval 31 (by omega)
  change nextNormalPenaltyLower ≤ nextNormalPenalty favorableNextS32Before ∧ nextNormalPenalty favorableNextS32Before ≤ nextNormalPenaltyUpper at hk
  have hm : ((1/1)/7)+(49254597/50000000)-0 < ((0/1)/3)+(75237631/50000000)-(nextNormalPenalty favorableNextS32Before) := by
    have h : ((1/1)/7)+(49254597/50000000) < ((0/1)/3)+(75237631/50000000)-nextNormalPenaltyUpper := by norm_num [nextNormalPenaltyUpper,savedCref,uniformQuoteError]
    linarith [hk.2]
  have h := index_strict_order_from_intervals ((0/1)/3) ((1/1)/7) (nextNormalPenalty favorableNextS32Before) 0 (75237631/50000000) (49254597/50000000)
    (treeBonus (7/5) 31 3) (treeBonus (7/5) 31 7)
    (trajectory_bonus_31_3).1 (trajectory_bonus_31_7).2 hm
  simpa only [treeIndex] using h

theorem favorableNextS32D0Cmp3 : indexScore (7/5) (controlPenalty savedCref uniformQuoteError unitRoleUnused .next) favorableNextS32Before [] (.query 3) ≤ indexScore (7/5) (controlPenalty savedCref uniformQuoteError unitRoleUnused .next) favorableNextS32Before [] (.query 2) := by
  rw [favorableNextS32D0I3,favorableNextS32D0I2]

theorem favorableNextS32D0Cmp4 : indexScore (7/5) (controlPenalty savedCref uniformQuoteError unitRoleUnused .next) favorableNextS32Before [] (.query 4) ≤ indexScore (7/5) (controlPenalty savedCref uniformQuoteError unitRoleUnused .next) favorableNextS32Before [] (.query 2) := by
  rw [favorableNextS32D0I4,favorableNextS32D0I2]

theorem favorableNextS32D0Cmp5 : indexScore (7/5) (controlPenalty savedCref uniformQuoteError unitRoleUnused .next) favorableNextS32Before [] (.query 5) ≤ indexScore (7/5) (controlPenalty savedCref uniformQuoteError unitRoleUnused .next) favorableNextS32Before [] (.query 2) := by
  rw [favorableNextS32D0I5,favorableNextS32D0I2]
  have hk := favorable_next_penalty_interval 31 (by omega)
  change nextNormalPenaltyLower ≤ nextNormalPenalty favorableNextS32Before ∧ nextNormalPenalty favorableNextS32Before ≤ nextNormalPenaltyUpper at hk
  have hm : ((6/5)/5)+(58278829/50000000)-(nextNormalPenalty favorableNextS32Before) < ((0/1)/3)+(75237631/50000000)-(nextNormalPenalty favorableNextS32Before) := by
    have h : (((6/5)/5)+(58278829/50000000) : ℝ) < ((0/1)/3)+(75237631/50000000) := by norm_num
    linarith
  have h := index_weak_order_from_intervals ((0/1)/3) ((6/5)/5) (nextNormalPenalty favorableNextS32Before) (nextNormalPenalty favorableNextS32Before) (75237631/50000000) (58278829/50000000)
    (treeBonus (7/5) 31 3) (treeBonus (7/5) 31 5)
    (trajectory_bonus_31_3).1 (trajectory_bonus_31_5).2 hm.le
  simpa only [treeIndex] using h

theorem favorableNextS32D0Cmp6 : indexScore (7/5) (controlPenalty savedCref uniformQuoteError unitRoleUnused .next) favorableNextS32Before [] (.query 6) ≤ indexScore (7/5) (controlPenalty savedCref uniformQuoteError unitRoleUnused .next) favorableNextS32Before [] (.query 2) := by
  rw [favorableNextS32D0I6,favorableNextS32D0I2]

theorem favorableNextS32D0Cmp7 : indexScore (7/5) (controlPenalty savedCref uniformQuoteError unitRoleUnused .next) favorableNextS32Before [] (.query 7) ≤ indexScore (7/5) (controlPenalty savedCref uniformQuoteError unitRoleUnused .next) favorableNextS32Before [] (.query 2) := by
  rw [favorableNextS32D0I7,favorableNextS32D0I2]

theorem favorableNextS32Choice0 : nativeFirstChoice (indexScore (7/5) (controlPenalty savedCref uniformQuoteError unitRoleUnused .next) favorableNextS32Before []) favorableNextS32Before [] = .query 2 := by
  apply visited_choice_from_ordered_certificate _ _ [] [.query 0,.query 1] [.query 3,.query 4,.query 5,.query 6,.query 7] (.query 2) (by decide)
  · intro a ha
    have ho : orderedLegalAvailable [] = [.query 0,.query 1,.query 2,.query 3,.query 4,.query 5,.query 6,.query 7] := by decide
    rw [ho] at ha
    simp only [List.mem_cons,List.not_mem_nil,or_false] at ha
    rcases ha with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> decide
  · intro a ha
    simp only [List.mem_cons,List.not_mem_nil,or_false] at ha
    rcases ha with rfl | rfl
    · exact favorableNextS32D0Cmp0
    · exact favorableNextS32D0Cmp1
  · intro a ha
    simp only [List.mem_cons,List.not_mem_nil,or_false] at ha
    rcases ha with rfl | rfl | rfl | rfl | rfl
    · exact favorableNextS32D0Cmp3
    · exact favorableNextS32D0Cmp4
    · exact favorableNextS32D0Cmp5
    · exact favorableNextS32D0Cmp6
    · exact favorableNextS32D0Cmp7

theorem favorableNextS32ActualEvent : nativeEvent budgetTape (7/5) (controlPenalty savedCref uniformQuoteError unitRoleUnused .next)
    (taskReward false (2/5) (1/2)) favorableNextS32Before = favorableNextEvent32 := by
  have hs0 := native_select_existing_step budgetTape (7/5) (controlPenalty savedCref uniformQuoteError unitRoleUnused .next) favorableNextS32Before 8 [] (.query 2)
    (by decide) (by decide) favorableNextS32Choice0
  have hnew := native_select_new_step budgetTape (7/5) (controlPenalty savedCref uniformQuoteError unitRoleUnused .next) favorableNextS32Before 7 [.query 2]
    [.normalRetriever 6,.normalRetriever 7,.normalRetriever 8,.normalRetriever 5,.normalRetriever 1,.normalRetriever 2,.normalRetriever 3,.normalRetriever 12,.normalRetriever 14,.normalRetriever 13,.normalRetriever 21,.normalRetriever 23,.normalRetriever 22,.normalRetriever 9,.normalRetriever 11,.normalRetriever 10,.normalRetriever 15,.normalRetriever 17,.normalRetriever 16,.normalRetriever 18,.normalRetriever 20,.normalRetriever 19,.normalRetriever 24,.normalRetriever 25,.normalRetriever 26,.normalRetriever 27,.normalRetriever 28,.normalRetriever 29] (.normalRetriever 6) (by decide) (by decide) (by decide) (by decide)
  have hs : nativeSelect budgetTape (7/5) (controlPenalty savedCref uniformQuoteError unitRoleUnused .next) favorableNextS32Before 9 [] = [.query 2,.normalRetriever 6] := by
    rw [hs0]
    change nativeSelect budgetTape (7/5) (controlPenalty savedCref uniformQuoteError unitRoleUnused .next) favorableNextS32Before 8 [.query 2] = _
    rw [hnew] <;> rfl
  have hr : repairedRollout budgetTape favorableNextS32Before 9 [.query 2,.normalRetriever 6] = [.query 2,.normalRetriever 6,.selection 0,.width 0,.stop,.reranker 0,.topm 0,.context 0,.answer 0] := by decide
  simp only [nativeEvent,hs,hr]
  rfl

def favorableNextS33Before := favorableNextProposal.take 32

theorem favorableNextS33D0I0 : indexScore (7/5) (controlPenalty savedCref uniformQuoteError unitRoleUnused .next) favorableNextS33Before [] (.query 0) = treeIndex ((0/1)/4) (7/5) (nextNormalPenalty favorableNextS33Before) 32 4 := by
  have hs : replayBackup favorableNextS33Before emptyStatistics ([]++[.query 0]) = ⟨4,(0/1)⟩ := by
    rw [replayBackup_empty_closed_form]
    simp +decide [backedEvents,favorableNextS33Before,favorableNextProposal,favorableNextEvent1,favorableNextEvent2,favorableNextEvent3,favorableNextEvent4,favorableNextEvent5,favorableNextEvent6,favorableNextEvent7,favorableNextEvent8,favorableNextEvent9,favorableNextEvent10,favorableNextEvent11,favorableNextEvent12,favorableNextEvent13,favorableNextEvent14,favorableNextEvent15,favorableNextEvent16,favorableNextEvent17,favorableNextEvent18,favorableNextEvent19,favorableNextEvent20,favorableNextEvent21,favorableNextEvent22,favorableNextEvent23,favorableNextEvent24,favorableNextEvent25,favorableNextEvent26,favorableNextEvent27,favorableNextEvent28,favorableNextEvent29,favorableNextEvent30,favorableNextEvent31,favorableNextEvent32,taskReward]
    <;> norm_num
  have hp : rawVisits favorableNextS33Before [] = 32 := by decide
  have hn : rawVisits favorableNextS33Before ([]++[.query 0]) = 4 := by decide
  have hz : (controlPenalty savedCref uniformQuoteError unitRoleUnused .next) favorableNextS33Before [] (.query 0) = (nextNormalPenalty favorableNextS33Before) := by
    simpa only [favorableNextS33Before,nextNormalPenalty] using AgentUCTNextExact.favorable_next_normal_root_quotes_exact 32 (by omega) 0 (by decide)
  unfold indexScore
  rw [hs,hp,hn,hz]
  simp only [BackupStat.mean]
  norm_num

theorem favorableNextS33D0I1 : indexScore (7/5) (controlPenalty savedCref uniformQuoteError unitRoleUnused .next) favorableNextS33Before [] (.query 1) = treeIndex ((1/1)/7) (7/5) 0 32 7 := by
  have hs : replayBackup favorableNextS33Before emptyStatistics ([]++[.query 1]) = ⟨7,(1/1)⟩ := by
    rw [replayBackup_empty_closed_form]
    simp +decide [backedEvents,favorableNextS33Before,favorableNextProposal,favorableNextEvent1,favorableNextEvent2,favorableNextEvent3,favorableNextEvent4,favorableNextEvent5,favorableNextEvent6,favorableNextEvent7,favorableNextEvent8,favorableNextEvent9,favorableNextEvent10,favorableNextEvent11,favorableNextEvent12,favorableNextEvent13,favorableNextEvent14,favorableNextEvent15,favorableNextEvent16,favorableNextEvent17,favorableNextEvent18,favorableNextEvent19,favorableNextEvent20,favorableNextEvent21,favorableNextEvent22,favorableNextEvent23,favorableNextEvent24,favorableNextEvent25,favorableNextEvent26,favorableNextEvent27,favorableNextEvent28,favorableNextEvent29,favorableNextEvent30,favorableNextEvent31,favorableNextEvent32,taskReward]
    <;> norm_num
  have hp : rawVisits favorableNextS33Before [] = 32 := by decide
  have hn : rawVisits favorableNextS33Before ([]++[.query 1]) = 7 := by decide
  have hz : (controlPenalty savedCref uniformQuoteError unitRoleUnused .next) favorableNextS33Before [] (.query 1) = 0 := by
    apply control_penalty_empty_suffix
    exact AgentUCTNextExact.favorable_next_hyde_root_suffix_empty 32 (by omega)
  unfold indexScore
  rw [hs,hp,hn,hz]
  simp only [BackupStat.mean]
  norm_num

theorem favorableNextS33D0I2 : indexScore (7/5) (controlPenalty savedCref uniformQuoteError unitRoleUnused .next) favorableNextS33Before [] (.query 2) = treeIndex ((0/1)/4) (7/5) (nextNormalPenalty favorableNextS33Before) 32 4 := by
  have hs : replayBackup favorableNextS33Before emptyStatistics ([]++[.query 2]) = ⟨4,(0/1)⟩ := by
    rw [replayBackup_empty_closed_form]
    simp +decide [backedEvents,favorableNextS33Before,favorableNextProposal,favorableNextEvent1,favorableNextEvent2,favorableNextEvent3,favorableNextEvent4,favorableNextEvent5,favorableNextEvent6,favorableNextEvent7,favorableNextEvent8,favorableNextEvent9,favorableNextEvent10,favorableNextEvent11,favorableNextEvent12,favorableNextEvent13,favorableNextEvent14,favorableNextEvent15,favorableNextEvent16,favorableNextEvent17,favorableNextEvent18,favorableNextEvent19,favorableNextEvent20,favorableNextEvent21,favorableNextEvent22,favorableNextEvent23,favorableNextEvent24,favorableNextEvent25,favorableNextEvent26,favorableNextEvent27,favorableNextEvent28,favorableNextEvent29,favorableNextEvent30,favorableNextEvent31,favorableNextEvent32,taskReward]
    <;> norm_num
  have hp : rawVisits favorableNextS33Before [] = 32 := by decide
  have hn : rawVisits favorableNextS33Before ([]++[.query 2]) = 4 := by decide
  have hz : (controlPenalty savedCref uniformQuoteError unitRoleUnused .next) favorableNextS33Before [] (.query 2) = (nextNormalPenalty favorableNextS33Before) := by
    simpa only [favorableNextS33Before,nextNormalPenalty] using AgentUCTNextExact.favorable_next_normal_root_quotes_exact 32 (by omega) 2 (by decide)
  unfold indexScore
  rw [hs,hp,hn,hz]
  simp only [BackupStat.mean]
  norm_num

theorem favorableNextS33D0I3 : indexScore (7/5) (controlPenalty savedCref uniformQuoteError unitRoleUnused .next) favorableNextS33Before [] (.query 3) = treeIndex ((0/1)/3) (7/5) (nextNormalPenalty favorableNextS33Before) 32 3 := by
  have hs : replayBackup favorableNextS33Before emptyStatistics ([]++[.query 3]) = ⟨3,(0/1)⟩ := by
    rw [replayBackup_empty_closed_form]
    simp +decide [backedEvents,favorableNextS33Before,favorableNextProposal,favorableNextEvent1,favorableNextEvent2,favorableNextEvent3,favorableNextEvent4,favorableNextEvent5,favorableNextEvent6,favorableNextEvent7,favorableNextEvent8,favorableNextEvent9,favorableNextEvent10,favorableNextEvent11,favorableNextEvent12,favorableNextEvent13,favorableNextEvent14,favorableNextEvent15,favorableNextEvent16,favorableNextEvent17,favorableNextEvent18,favorableNextEvent19,favorableNextEvent20,favorableNextEvent21,favorableNextEvent22,favorableNextEvent23,favorableNextEvent24,favorableNextEvent25,favorableNextEvent26,favorableNextEvent27,favorableNextEvent28,favorableNextEvent29,favorableNextEvent30,favorableNextEvent31,favorableNextEvent32,taskReward]
    <;> norm_num
  have hp : rawVisits favorableNextS33Before [] = 32 := by decide
  have hn : rawVisits favorableNextS33Before ([]++[.query 3]) = 3 := by decide
  have hz : (controlPenalty savedCref uniformQuoteError unitRoleUnused .next) favorableNextS33Before [] (.query 3) = (nextNormalPenalty favorableNextS33Before) := by
    simpa only [favorableNextS33Before,nextNormalPenalty] using AgentUCTNextExact.favorable_next_normal_root_quotes_exact 32 (by omega) 3 (by decide)
  unfold indexScore
  rw [hs,hp,hn,hz]
  simp only [BackupStat.mean]
  norm_num

theorem favorableNextS33D0I4 : indexScore (7/5) (controlPenalty savedCref uniformQuoteError unitRoleUnused .next) favorableNextS33Before [] (.query 4) = treeIndex ((0/1)/3) (7/5) (nextNormalPenalty favorableNextS33Before) 32 3 := by
  have hs : replayBackup favorableNextS33Before emptyStatistics ([]++[.query 4]) = ⟨3,(0/1)⟩ := by
    rw [replayBackup_empty_closed_form]
    simp +decide [backedEvents,favorableNextS33Before,favorableNextProposal,favorableNextEvent1,favorableNextEvent2,favorableNextEvent3,favorableNextEvent4,favorableNextEvent5,favorableNextEvent6,favorableNextEvent7,favorableNextEvent8,favorableNextEvent9,favorableNextEvent10,favorableNextEvent11,favorableNextEvent12,favorableNextEvent13,favorableNextEvent14,favorableNextEvent15,favorableNextEvent16,favorableNextEvent17,favorableNextEvent18,favorableNextEvent19,favorableNextEvent20,favorableNextEvent21,favorableNextEvent22,favorableNextEvent23,favorableNextEvent24,favorableNextEvent25,favorableNextEvent26,favorableNextEvent27,favorableNextEvent28,favorableNextEvent29,favorableNextEvent30,favorableNextEvent31,favorableNextEvent32,taskReward]
    <;> norm_num
  have hp : rawVisits favorableNextS33Before [] = 32 := by decide
  have hn : rawVisits favorableNextS33Before ([]++[.query 4]) = 3 := by decide
  have hz : (controlPenalty savedCref uniformQuoteError unitRoleUnused .next) favorableNextS33Before [] (.query 4) = (nextNormalPenalty favorableNextS33Before) := by
    simpa only [favorableNextS33Before,nextNormalPenalty] using AgentUCTNextExact.favorable_next_normal_root_quotes_exact 32 (by omega) 4 (by decide)
  unfold indexScore
  rw [hs,hp,hn,hz]
  simp only [BackupStat.mean]
  norm_num

theorem favorableNextS33D0I5 : indexScore (7/5) (controlPenalty savedCref uniformQuoteError unitRoleUnused .next) favorableNextS33Before [] (.query 5) = treeIndex ((6/5)/5) (7/5) (nextNormalPenalty favorableNextS33Before) 32 5 := by
  have hs : replayBackup favorableNextS33Before emptyStatistics ([]++[.query 5]) = ⟨5,(6/5)⟩ := by
    rw [replayBackup_empty_closed_form]
    simp +decide [backedEvents,favorableNextS33Before,favorableNextProposal,favorableNextEvent1,favorableNextEvent2,favorableNextEvent3,favorableNextEvent4,favorableNextEvent5,favorableNextEvent6,favorableNextEvent7,favorableNextEvent8,favorableNextEvent9,favorableNextEvent10,favorableNextEvent11,favorableNextEvent12,favorableNextEvent13,favorableNextEvent14,favorableNextEvent15,favorableNextEvent16,favorableNextEvent17,favorableNextEvent18,favorableNextEvent19,favorableNextEvent20,favorableNextEvent21,favorableNextEvent22,favorableNextEvent23,favorableNextEvent24,favorableNextEvent25,favorableNextEvent26,favorableNextEvent27,favorableNextEvent28,favorableNextEvent29,favorableNextEvent30,favorableNextEvent31,favorableNextEvent32,taskReward]
    <;> norm_num
  have hp : rawVisits favorableNextS33Before [] = 32 := by decide
  have hn : rawVisits favorableNextS33Before ([]++[.query 5]) = 5 := by decide
  have hz : (controlPenalty savedCref uniformQuoteError unitRoleUnused .next) favorableNextS33Before [] (.query 5) = (nextNormalPenalty favorableNextS33Before) := by
    simpa only [favorableNextS33Before,nextNormalPenalty] using AgentUCTNextExact.favorable_next_normal_root_quotes_exact 32 (by omega) 5 (by decide)
  unfold indexScore
  rw [hs,hp,hn,hz]
  simp only [BackupStat.mean]
  norm_num

theorem favorableNextS33D0I6 : indexScore (7/5) (controlPenalty savedCref uniformQuoteError unitRoleUnused .next) favorableNextS33Before [] (.query 6) = treeIndex ((0/1)/3) (7/5) (nextNormalPenalty favorableNextS33Before) 32 3 := by
  have hs : replayBackup favorableNextS33Before emptyStatistics ([]++[.query 6]) = ⟨3,(0/1)⟩ := by
    rw [replayBackup_empty_closed_form]
    simp +decide [backedEvents,favorableNextS33Before,favorableNextProposal,favorableNextEvent1,favorableNextEvent2,favorableNextEvent3,favorableNextEvent4,favorableNextEvent5,favorableNextEvent6,favorableNextEvent7,favorableNextEvent8,favorableNextEvent9,favorableNextEvent10,favorableNextEvent11,favorableNextEvent12,favorableNextEvent13,favorableNextEvent14,favorableNextEvent15,favorableNextEvent16,favorableNextEvent17,favorableNextEvent18,favorableNextEvent19,favorableNextEvent20,favorableNextEvent21,favorableNextEvent22,favorableNextEvent23,favorableNextEvent24,favorableNextEvent25,favorableNextEvent26,favorableNextEvent27,favorableNextEvent28,favorableNextEvent29,favorableNextEvent30,favorableNextEvent31,favorableNextEvent32,taskReward]
    <;> norm_num
  have hp : rawVisits favorableNextS33Before [] = 32 := by decide
  have hn : rawVisits favorableNextS33Before ([]++[.query 6]) = 3 := by decide
  have hz : (controlPenalty savedCref uniformQuoteError unitRoleUnused .next) favorableNextS33Before [] (.query 6) = (nextNormalPenalty favorableNextS33Before) := by
    simpa only [favorableNextS33Before,nextNormalPenalty] using AgentUCTNextExact.favorable_next_normal_root_quotes_exact 32 (by omega) 6 (by decide)
  unfold indexScore
  rw [hs,hp,hn,hz]
  simp only [BackupStat.mean]
  norm_num

theorem favorableNextS33D0I7 : indexScore (7/5) (controlPenalty savedCref uniformQuoteError unitRoleUnused .next) favorableNextS33Before [] (.query 7) = treeIndex ((0/1)/3) (7/5) (nextNormalPenalty favorableNextS33Before) 32 3 := by
  have hs : replayBackup favorableNextS33Before emptyStatistics ([]++[.query 7]) = ⟨3,(0/1)⟩ := by
    rw [replayBackup_empty_closed_form]
    simp +decide [backedEvents,favorableNextS33Before,favorableNextProposal,favorableNextEvent1,favorableNextEvent2,favorableNextEvent3,favorableNextEvent4,favorableNextEvent5,favorableNextEvent6,favorableNextEvent7,favorableNextEvent8,favorableNextEvent9,favorableNextEvent10,favorableNextEvent11,favorableNextEvent12,favorableNextEvent13,favorableNextEvent14,favorableNextEvent15,favorableNextEvent16,favorableNextEvent17,favorableNextEvent18,favorableNextEvent19,favorableNextEvent20,favorableNextEvent21,favorableNextEvent22,favorableNextEvent23,favorableNextEvent24,favorableNextEvent25,favorableNextEvent26,favorableNextEvent27,favorableNextEvent28,favorableNextEvent29,favorableNextEvent30,favorableNextEvent31,favorableNextEvent32,taskReward]
    <;> norm_num
  have hp : rawVisits favorableNextS33Before [] = 32 := by decide
  have hn : rawVisits favorableNextS33Before ([]++[.query 7]) = 3 := by decide
  have hz : (controlPenalty savedCref uniformQuoteError unitRoleUnused .next) favorableNextS33Before [] (.query 7) = (nextNormalPenalty favorableNextS33Before) := by
    simpa only [favorableNextS33Before,nextNormalPenalty] using AgentUCTNextExact.favorable_next_normal_root_quotes_exact 32 (by omega) 7 (by decide)
  unfold indexScore
  rw [hs,hp,hn,hz]
  simp only [BackupStat.mean]
  norm_num

theorem favorableNextS33D0Cmp0 : indexScore (7/5) (controlPenalty savedCref uniformQuoteError unitRoleUnused .next) favorableNextS33Before [] (.query 0) < indexScore (7/5) (controlPenalty savedCref uniformQuoteError unitRoleUnused .next) favorableNextS33Before [] (.query 3) := by
  rw [favorableNextS33D0I0,favorableNextS33D0I3]
  have hk := favorable_next_penalty_interval 32 (by omega)
  change nextNormalPenaltyLower ≤ nextNormalPenalty favorableNextS33Before ∧ nextNormalPenalty favorableNextS33Before ≤ nextNormalPenaltyUpper at hk
  have hm : ((0/1)/4)+(65446339/50000000)-(nextNormalPenalty favorableNextS33Before) < ((0/1)/3)+(75570901/50000000)-(nextNormalPenalty favorableNextS33Before) := by
    have h : (((0/1)/4)+(65446339/50000000) : ℝ) < ((0/1)/3)+(75570901/50000000) := by norm_num
    linarith
  have h := index_strict_order_from_intervals ((0/1)/3) ((0/1)/4) (nextNormalPenalty favorableNextS33Before) (nextNormalPenalty favorableNextS33Before) (75570901/50000000) (65446339/50000000)
    (treeBonus (7/5) 32 3) (treeBonus (7/5) 32 4)
    (trajectory_bonus_32_3).1 (trajectory_bonus_32_4).2 hm
  simpa only [treeIndex] using h

theorem favorableNextS33D0Cmp1 : indexScore (7/5) (controlPenalty savedCref uniformQuoteError unitRoleUnused .next) favorableNextS33Before [] (.query 1) < indexScore (7/5) (controlPenalty savedCref uniformQuoteError unitRoleUnused .next) favorableNextS33Before [] (.query 3) := by
  rw [favorableNextS33D0I1,favorableNextS33D0I3]
  have hk := favorable_next_penalty_interval 32 (by omega)
  change nextNormalPenaltyLower ≤ nextNormalPenalty favorableNextS33Before ∧ nextNormalPenalty favorableNextS33Before ≤ nextNormalPenaltyUpper at hk
  have hm : ((1/1)/7)+(2473639/2500000)-0 < ((0/1)/3)+(75570901/50000000)-(nextNormalPenalty favorableNextS33Before) := by
    have h : ((1/1)/7)+(2473639/2500000) < ((0/1)/3)+(75570901/50000000)-nextNormalPenaltyUpper := by norm_num [nextNormalPenaltyUpper,savedCref,uniformQuoteError]
    linarith [hk.2]
  have h := index_strict_order_from_intervals ((0/1)/3) ((1/1)/7) (nextNormalPenalty favorableNextS33Before) 0 (75570901/50000000) (2473639/2500000)
    (treeBonus (7/5) 32 3) (treeBonus (7/5) 32 7)
    (trajectory_bonus_32_3).1 (trajectory_bonus_32_7).2 hm
  simpa only [treeIndex] using h

theorem favorableNextS33D0Cmp2 : indexScore (7/5) (controlPenalty savedCref uniformQuoteError unitRoleUnused .next) favorableNextS33Before [] (.query 2) < indexScore (7/5) (controlPenalty savedCref uniformQuoteError unitRoleUnused .next) favorableNextS33Before [] (.query 3) := by
  rw [favorableNextS33D0I2,favorableNextS33D0I3]
  have hk := favorable_next_penalty_interval 32 (by omega)
  change nextNormalPenaltyLower ≤ nextNormalPenalty favorableNextS33Before ∧ nextNormalPenalty favorableNextS33Before ≤ nextNormalPenaltyUpper at hk
  have hm : ((0/1)/4)+(65446339/50000000)-(nextNormalPenalty favorableNextS33Before) < ((0/1)/3)+(75570901/50000000)-(nextNormalPenalty favorableNextS33Before) := by
    have h : (((0/1)/4)+(65446339/50000000) : ℝ) < ((0/1)/3)+(75570901/50000000) := by norm_num
    linarith
  have h := index_strict_order_from_intervals ((0/1)/3) ((0/1)/4) (nextNormalPenalty favorableNextS33Before) (nextNormalPenalty favorableNextS33Before) (75570901/50000000) (65446339/50000000)
    (treeBonus (7/5) 32 3) (treeBonus (7/5) 32 4)
    (trajectory_bonus_32_3).1 (trajectory_bonus_32_4).2 hm
  simpa only [treeIndex] using h

theorem favorableNextS33D0Cmp4 : indexScore (7/5) (controlPenalty savedCref uniformQuoteError unitRoleUnused .next) favorableNextS33Before [] (.query 4) ≤ indexScore (7/5) (controlPenalty savedCref uniformQuoteError unitRoleUnused .next) favorableNextS33Before [] (.query 3) := by
  rw [favorableNextS33D0I4,favorableNextS33D0I3]

theorem favorableNextS33D0Cmp5 : indexScore (7/5) (controlPenalty savedCref uniformQuoteError unitRoleUnused .next) favorableNextS33Before [] (.query 5) ≤ indexScore (7/5) (controlPenalty savedCref uniformQuoteError unitRoleUnused .next) favorableNextS33Before [] (.query 3) := by
  rw [favorableNextS33D0I5,favorableNextS33D0I3]
  have hk := favorable_next_penalty_interval 32 (by omega)
  change nextNormalPenaltyLower ≤ nextNormalPenalty favorableNextS33Before ∧ nextNormalPenalty favorableNextS33Before ≤ nextNormalPenaltyUpper at hk
  have hm : ((6/5)/5)+(29268491/25000000)-(nextNormalPenalty favorableNextS33Before) < ((0/1)/3)+(75570901/50000000)-(nextNormalPenalty favorableNextS33Before) := by
    have h : (((6/5)/5)+(29268491/25000000) : ℝ) < ((0/1)/3)+(75570901/50000000) := by norm_num
    linarith
  have h := index_weak_order_from_intervals ((0/1)/3) ((6/5)/5) (nextNormalPenalty favorableNextS33Before) (nextNormalPenalty favorableNextS33Before) (75570901/50000000) (29268491/25000000)
    (treeBonus (7/5) 32 3) (treeBonus (7/5) 32 5)
    (trajectory_bonus_32_3).1 (trajectory_bonus_32_5).2 hm.le
  simpa only [treeIndex] using h

theorem favorableNextS33D0Cmp6 : indexScore (7/5) (controlPenalty savedCref uniformQuoteError unitRoleUnused .next) favorableNextS33Before [] (.query 6) ≤ indexScore (7/5) (controlPenalty savedCref uniformQuoteError unitRoleUnused .next) favorableNextS33Before [] (.query 3) := by
  rw [favorableNextS33D0I6,favorableNextS33D0I3]

theorem favorableNextS33D0Cmp7 : indexScore (7/5) (controlPenalty savedCref uniformQuoteError unitRoleUnused .next) favorableNextS33Before [] (.query 7) ≤ indexScore (7/5) (controlPenalty savedCref uniformQuoteError unitRoleUnused .next) favorableNextS33Before [] (.query 3) := by
  rw [favorableNextS33D0I7,favorableNextS33D0I3]

theorem favorableNextS33Choice0 : nativeFirstChoice (indexScore (7/5) (controlPenalty savedCref uniformQuoteError unitRoleUnused .next) favorableNextS33Before []) favorableNextS33Before [] = .query 3 := by
  apply visited_choice_from_ordered_certificate _ _ [] [.query 0,.query 1,.query 2] [.query 4,.query 5,.query 6,.query 7] (.query 3) (by decide)
  · intro a ha
    have ho : orderedLegalAvailable [] = [.query 0,.query 1,.query 2,.query 3,.query 4,.query 5,.query 6,.query 7] := by decide
    rw [ho] at ha
    simp only [List.mem_cons,List.not_mem_nil,or_false] at ha
    rcases ha with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> decide
  · intro a ha
    simp only [List.mem_cons,List.not_mem_nil,or_false] at ha
    rcases ha with rfl | rfl | rfl
    · exact favorableNextS33D0Cmp0
    · exact favorableNextS33D0Cmp1
    · exact favorableNextS33D0Cmp2
  · intro a ha
    simp only [List.mem_cons,List.not_mem_nil,or_false] at ha
    rcases ha with rfl | rfl | rfl | rfl
    · exact favorableNextS33D0Cmp4
    · exact favorableNextS33D0Cmp5
    · exact favorableNextS33D0Cmp6
    · exact favorableNextS33D0Cmp7

theorem favorableNextS33ActualEvent : nativeEvent budgetTape (7/5) (controlPenalty savedCref uniformQuoteError unitRoleUnused .next)
    (taskReward false (2/5) (1/2)) favorableNextS33Before = favorableNextEvent33 := by
  have hs0 := native_select_existing_step budgetTape (7/5) (controlPenalty savedCref uniformQuoteError unitRoleUnused .next) favorableNextS33Before 8 [] (.query 3)
    (by decide) (by decide) favorableNextS33Choice0
  have hnew := native_select_new_step budgetTape (7/5) (controlPenalty savedCref uniformQuoteError unitRoleUnused .next) favorableNextS33Before 7 [.query 3]
    [.normalRetriever 6,.normalRetriever 7,.normalRetriever 8,.normalRetriever 5,.normalRetriever 1,.normalRetriever 2,.normalRetriever 3,.normalRetriever 12,.normalRetriever 14,.normalRetriever 13,.normalRetriever 21,.normalRetriever 23,.normalRetriever 22,.normalRetriever 9,.normalRetriever 11,.normalRetriever 10,.normalRetriever 15,.normalRetriever 17,.normalRetriever 16,.normalRetriever 18,.normalRetriever 20,.normalRetriever 19,.normalRetriever 24,.normalRetriever 25,.normalRetriever 26,.normalRetriever 27,.normalRetriever 28,.normalRetriever 29] (.normalRetriever 6) (by decide) (by decide) (by decide) (by decide)
  have hs : nativeSelect budgetTape (7/5) (controlPenalty savedCref uniformQuoteError unitRoleUnused .next) favorableNextS33Before 9 [] = [.query 3,.normalRetriever 6] := by
    rw [hs0]
    change nativeSelect budgetTape (7/5) (controlPenalty savedCref uniformQuoteError unitRoleUnused .next) favorableNextS33Before 8 [.query 3] = _
    rw [hnew] <;> rfl
  have hr : repairedRollout budgetTape favorableNextS33Before 9 [.query 3,.normalRetriever 6] = [.query 3,.normalRetriever 6,.selection 0,.width 0,.stop,.reranker 0,.topm 0,.context 0,.answer 0] := by decide
  simp only [nativeEvent,hs,hr]
  rfl

def favorableNextS34Before := favorableNextProposal.take 33

theorem favorableNextS34D0I0 : indexScore (7/5) (controlPenalty savedCref uniformQuoteError unitRoleUnused .next) favorableNextS34Before [] (.query 0) = treeIndex ((0/1)/4) (7/5) (nextNormalPenalty favorableNextS34Before) 33 4 := by
  have hs : replayBackup favorableNextS34Before emptyStatistics ([]++[.query 0]) = ⟨4,(0/1)⟩ := by
    rw [replayBackup_empty_closed_form]
    simp +decide [backedEvents,favorableNextS34Before,favorableNextProposal,favorableNextEvent1,favorableNextEvent2,favorableNextEvent3,favorableNextEvent4,favorableNextEvent5,favorableNextEvent6,favorableNextEvent7,favorableNextEvent8,favorableNextEvent9,favorableNextEvent10,favorableNextEvent11,favorableNextEvent12,favorableNextEvent13,favorableNextEvent14,favorableNextEvent15,favorableNextEvent16,favorableNextEvent17,favorableNextEvent18,favorableNextEvent19,favorableNextEvent20,favorableNextEvent21,favorableNextEvent22,favorableNextEvent23,favorableNextEvent24,favorableNextEvent25,favorableNextEvent26,favorableNextEvent27,favorableNextEvent28,favorableNextEvent29,favorableNextEvent30,favorableNextEvent31,favorableNextEvent32,favorableNextEvent33,taskReward]
    <;> norm_num
  have hp : rawVisits favorableNextS34Before [] = 33 := by decide
  have hn : rawVisits favorableNextS34Before ([]++[.query 0]) = 4 := by decide
  have hz : (controlPenalty savedCref uniformQuoteError unitRoleUnused .next) favorableNextS34Before [] (.query 0) = (nextNormalPenalty favorableNextS34Before) := by
    simpa only [favorableNextS34Before,nextNormalPenalty] using AgentUCTNextExact.favorable_next_normal_root_quotes_exact 33 (by omega) 0 (by decide)
  unfold indexScore
  rw [hs,hp,hn,hz]
  simp only [BackupStat.mean]
  norm_num

theorem favorableNextS34D0I1 : indexScore (7/5) (controlPenalty savedCref uniformQuoteError unitRoleUnused .next) favorableNextS34Before [] (.query 1) = treeIndex ((1/1)/7) (7/5) 0 33 7 := by
  have hs : replayBackup favorableNextS34Before emptyStatistics ([]++[.query 1]) = ⟨7,(1/1)⟩ := by
    rw [replayBackup_empty_closed_form]
    simp +decide [backedEvents,favorableNextS34Before,favorableNextProposal,favorableNextEvent1,favorableNextEvent2,favorableNextEvent3,favorableNextEvent4,favorableNextEvent5,favorableNextEvent6,favorableNextEvent7,favorableNextEvent8,favorableNextEvent9,favorableNextEvent10,favorableNextEvent11,favorableNextEvent12,favorableNextEvent13,favorableNextEvent14,favorableNextEvent15,favorableNextEvent16,favorableNextEvent17,favorableNextEvent18,favorableNextEvent19,favorableNextEvent20,favorableNextEvent21,favorableNextEvent22,favorableNextEvent23,favorableNextEvent24,favorableNextEvent25,favorableNextEvent26,favorableNextEvent27,favorableNextEvent28,favorableNextEvent29,favorableNextEvent30,favorableNextEvent31,favorableNextEvent32,favorableNextEvent33,taskReward]
    <;> norm_num
  have hp : rawVisits favorableNextS34Before [] = 33 := by decide
  have hn : rawVisits favorableNextS34Before ([]++[.query 1]) = 7 := by decide
  have hz : (controlPenalty savedCref uniformQuoteError unitRoleUnused .next) favorableNextS34Before [] (.query 1) = 0 := by
    apply control_penalty_empty_suffix
    exact AgentUCTNextExact.favorable_next_hyde_root_suffix_empty 33 (by omega)
  unfold indexScore
  rw [hs,hp,hn,hz]
  simp only [BackupStat.mean]
  norm_num

theorem favorableNextS34D0I2 : indexScore (7/5) (controlPenalty savedCref uniformQuoteError unitRoleUnused .next) favorableNextS34Before [] (.query 2) = treeIndex ((0/1)/4) (7/5) (nextNormalPenalty favorableNextS34Before) 33 4 := by
  have hs : replayBackup favorableNextS34Before emptyStatistics ([]++[.query 2]) = ⟨4,(0/1)⟩ := by
    rw [replayBackup_empty_closed_form]
    simp +decide [backedEvents,favorableNextS34Before,favorableNextProposal,favorableNextEvent1,favorableNextEvent2,favorableNextEvent3,favorableNextEvent4,favorableNextEvent5,favorableNextEvent6,favorableNextEvent7,favorableNextEvent8,favorableNextEvent9,favorableNextEvent10,favorableNextEvent11,favorableNextEvent12,favorableNextEvent13,favorableNextEvent14,favorableNextEvent15,favorableNextEvent16,favorableNextEvent17,favorableNextEvent18,favorableNextEvent19,favorableNextEvent20,favorableNextEvent21,favorableNextEvent22,favorableNextEvent23,favorableNextEvent24,favorableNextEvent25,favorableNextEvent26,favorableNextEvent27,favorableNextEvent28,favorableNextEvent29,favorableNextEvent30,favorableNextEvent31,favorableNextEvent32,favorableNextEvent33,taskReward]
    <;> norm_num
  have hp : rawVisits favorableNextS34Before [] = 33 := by decide
  have hn : rawVisits favorableNextS34Before ([]++[.query 2]) = 4 := by decide
  have hz : (controlPenalty savedCref uniformQuoteError unitRoleUnused .next) favorableNextS34Before [] (.query 2) = (nextNormalPenalty favorableNextS34Before) := by
    simpa only [favorableNextS34Before,nextNormalPenalty] using AgentUCTNextExact.favorable_next_normal_root_quotes_exact 33 (by omega) 2 (by decide)
  unfold indexScore
  rw [hs,hp,hn,hz]
  simp only [BackupStat.mean]
  norm_num

theorem favorableNextS34D0I3 : indexScore (7/5) (controlPenalty savedCref uniformQuoteError unitRoleUnused .next) favorableNextS34Before [] (.query 3) = treeIndex ((0/1)/4) (7/5) (nextNormalPenalty favorableNextS34Before) 33 4 := by
  have hs : replayBackup favorableNextS34Before emptyStatistics ([]++[.query 3]) = ⟨4,(0/1)⟩ := by
    rw [replayBackup_empty_closed_form]
    simp +decide [backedEvents,favorableNextS34Before,favorableNextProposal,favorableNextEvent1,favorableNextEvent2,favorableNextEvent3,favorableNextEvent4,favorableNextEvent5,favorableNextEvent6,favorableNextEvent7,favorableNextEvent8,favorableNextEvent9,favorableNextEvent10,favorableNextEvent11,favorableNextEvent12,favorableNextEvent13,favorableNextEvent14,favorableNextEvent15,favorableNextEvent16,favorableNextEvent17,favorableNextEvent18,favorableNextEvent19,favorableNextEvent20,favorableNextEvent21,favorableNextEvent22,favorableNextEvent23,favorableNextEvent24,favorableNextEvent25,favorableNextEvent26,favorableNextEvent27,favorableNextEvent28,favorableNextEvent29,favorableNextEvent30,favorableNextEvent31,favorableNextEvent32,favorableNextEvent33,taskReward]
    <;> norm_num
  have hp : rawVisits favorableNextS34Before [] = 33 := by decide
  have hn : rawVisits favorableNextS34Before ([]++[.query 3]) = 4 := by decide
  have hz : (controlPenalty savedCref uniformQuoteError unitRoleUnused .next) favorableNextS34Before [] (.query 3) = (nextNormalPenalty favorableNextS34Before) := by
    simpa only [favorableNextS34Before,nextNormalPenalty] using AgentUCTNextExact.favorable_next_normal_root_quotes_exact 33 (by omega) 3 (by decide)
  unfold indexScore
  rw [hs,hp,hn,hz]
  simp only [BackupStat.mean]
  norm_num

theorem favorableNextS34D0I4 : indexScore (7/5) (controlPenalty savedCref uniformQuoteError unitRoleUnused .next) favorableNextS34Before [] (.query 4) = treeIndex ((0/1)/3) (7/5) (nextNormalPenalty favorableNextS34Before) 33 3 := by
  have hs : replayBackup favorableNextS34Before emptyStatistics ([]++[.query 4]) = ⟨3,(0/1)⟩ := by
    rw [replayBackup_empty_closed_form]
    simp +decide [backedEvents,favorableNextS34Before,favorableNextProposal,favorableNextEvent1,favorableNextEvent2,favorableNextEvent3,favorableNextEvent4,favorableNextEvent5,favorableNextEvent6,favorableNextEvent7,favorableNextEvent8,favorableNextEvent9,favorableNextEvent10,favorableNextEvent11,favorableNextEvent12,favorableNextEvent13,favorableNextEvent14,favorableNextEvent15,favorableNextEvent16,favorableNextEvent17,favorableNextEvent18,favorableNextEvent19,favorableNextEvent20,favorableNextEvent21,favorableNextEvent22,favorableNextEvent23,favorableNextEvent24,favorableNextEvent25,favorableNextEvent26,favorableNextEvent27,favorableNextEvent28,favorableNextEvent29,favorableNextEvent30,favorableNextEvent31,favorableNextEvent32,favorableNextEvent33,taskReward]
    <;> norm_num
  have hp : rawVisits favorableNextS34Before [] = 33 := by decide
  have hn : rawVisits favorableNextS34Before ([]++[.query 4]) = 3 := by decide
  have hz : (controlPenalty savedCref uniformQuoteError unitRoleUnused .next) favorableNextS34Before [] (.query 4) = (nextNormalPenalty favorableNextS34Before) := by
    simpa only [favorableNextS34Before,nextNormalPenalty] using AgentUCTNextExact.favorable_next_normal_root_quotes_exact 33 (by omega) 4 (by decide)
  unfold indexScore
  rw [hs,hp,hn,hz]
  simp only [BackupStat.mean]
  norm_num

theorem favorableNextS34D0I5 : indexScore (7/5) (controlPenalty savedCref uniformQuoteError unitRoleUnused .next) favorableNextS34Before [] (.query 5) = treeIndex ((6/5)/5) (7/5) (nextNormalPenalty favorableNextS34Before) 33 5 := by
  have hs : replayBackup favorableNextS34Before emptyStatistics ([]++[.query 5]) = ⟨5,(6/5)⟩ := by
    rw [replayBackup_empty_closed_form]
    simp +decide [backedEvents,favorableNextS34Before,favorableNextProposal,favorableNextEvent1,favorableNextEvent2,favorableNextEvent3,favorableNextEvent4,favorableNextEvent5,favorableNextEvent6,favorableNextEvent7,favorableNextEvent8,favorableNextEvent9,favorableNextEvent10,favorableNextEvent11,favorableNextEvent12,favorableNextEvent13,favorableNextEvent14,favorableNextEvent15,favorableNextEvent16,favorableNextEvent17,favorableNextEvent18,favorableNextEvent19,favorableNextEvent20,favorableNextEvent21,favorableNextEvent22,favorableNextEvent23,favorableNextEvent24,favorableNextEvent25,favorableNextEvent26,favorableNextEvent27,favorableNextEvent28,favorableNextEvent29,favorableNextEvent30,favorableNextEvent31,favorableNextEvent32,favorableNextEvent33,taskReward]
    <;> norm_num
  have hp : rawVisits favorableNextS34Before [] = 33 := by decide
  have hn : rawVisits favorableNextS34Before ([]++[.query 5]) = 5 := by decide
  have hz : (controlPenalty savedCref uniformQuoteError unitRoleUnused .next) favorableNextS34Before [] (.query 5) = (nextNormalPenalty favorableNextS34Before) := by
    simpa only [favorableNextS34Before,nextNormalPenalty] using AgentUCTNextExact.favorable_next_normal_root_quotes_exact 33 (by omega) 5 (by decide)
  unfold indexScore
  rw [hs,hp,hn,hz]
  simp only [BackupStat.mean]
  norm_num

theorem favorableNextS34D0I6 : indexScore (7/5) (controlPenalty savedCref uniformQuoteError unitRoleUnused .next) favorableNextS34Before [] (.query 6) = treeIndex ((0/1)/3) (7/5) (nextNormalPenalty favorableNextS34Before) 33 3 := by
  have hs : replayBackup favorableNextS34Before emptyStatistics ([]++[.query 6]) = ⟨3,(0/1)⟩ := by
    rw [replayBackup_empty_closed_form]
    simp +decide [backedEvents,favorableNextS34Before,favorableNextProposal,favorableNextEvent1,favorableNextEvent2,favorableNextEvent3,favorableNextEvent4,favorableNextEvent5,favorableNextEvent6,favorableNextEvent7,favorableNextEvent8,favorableNextEvent9,favorableNextEvent10,favorableNextEvent11,favorableNextEvent12,favorableNextEvent13,favorableNextEvent14,favorableNextEvent15,favorableNextEvent16,favorableNextEvent17,favorableNextEvent18,favorableNextEvent19,favorableNextEvent20,favorableNextEvent21,favorableNextEvent22,favorableNextEvent23,favorableNextEvent24,favorableNextEvent25,favorableNextEvent26,favorableNextEvent27,favorableNextEvent28,favorableNextEvent29,favorableNextEvent30,favorableNextEvent31,favorableNextEvent32,favorableNextEvent33,taskReward]
    <;> norm_num
  have hp : rawVisits favorableNextS34Before [] = 33 := by decide
  have hn : rawVisits favorableNextS34Before ([]++[.query 6]) = 3 := by decide
  have hz : (controlPenalty savedCref uniformQuoteError unitRoleUnused .next) favorableNextS34Before [] (.query 6) = (nextNormalPenalty favorableNextS34Before) := by
    simpa only [favorableNextS34Before,nextNormalPenalty] using AgentUCTNextExact.favorable_next_normal_root_quotes_exact 33 (by omega) 6 (by decide)
  unfold indexScore
  rw [hs,hp,hn,hz]
  simp only [BackupStat.mean]
  norm_num

theorem favorableNextS34D0I7 : indexScore (7/5) (controlPenalty savedCref uniformQuoteError unitRoleUnused .next) favorableNextS34Before [] (.query 7) = treeIndex ((0/1)/3) (7/5) (nextNormalPenalty favorableNextS34Before) 33 3 := by
  have hs : replayBackup favorableNextS34Before emptyStatistics ([]++[.query 7]) = ⟨3,(0/1)⟩ := by
    rw [replayBackup_empty_closed_form]
    simp +decide [backedEvents,favorableNextS34Before,favorableNextProposal,favorableNextEvent1,favorableNextEvent2,favorableNextEvent3,favorableNextEvent4,favorableNextEvent5,favorableNextEvent6,favorableNextEvent7,favorableNextEvent8,favorableNextEvent9,favorableNextEvent10,favorableNextEvent11,favorableNextEvent12,favorableNextEvent13,favorableNextEvent14,favorableNextEvent15,favorableNextEvent16,favorableNextEvent17,favorableNextEvent18,favorableNextEvent19,favorableNextEvent20,favorableNextEvent21,favorableNextEvent22,favorableNextEvent23,favorableNextEvent24,favorableNextEvent25,favorableNextEvent26,favorableNextEvent27,favorableNextEvent28,favorableNextEvent29,favorableNextEvent30,favorableNextEvent31,favorableNextEvent32,favorableNextEvent33,taskReward]
    <;> norm_num
  have hp : rawVisits favorableNextS34Before [] = 33 := by decide
  have hn : rawVisits favorableNextS34Before ([]++[.query 7]) = 3 := by decide
  have hz : (controlPenalty savedCref uniformQuoteError unitRoleUnused .next) favorableNextS34Before [] (.query 7) = (nextNormalPenalty favorableNextS34Before) := by
    simpa only [favorableNextS34Before,nextNormalPenalty] using AgentUCTNextExact.favorable_next_normal_root_quotes_exact 33 (by omega) 7 (by decide)
  unfold indexScore
  rw [hs,hp,hn,hz]
  simp only [BackupStat.mean]
  norm_num

theorem favorableNextS34D0Cmp0 : indexScore (7/5) (controlPenalty savedCref uniformQuoteError unitRoleUnused .next) favorableNextS34Before [] (.query 0) < indexScore (7/5) (controlPenalty savedCref uniformQuoteError unitRoleUnused .next) favorableNextS34Before [] (.query 4) := by
  rw [favorableNextS34D0I0,favorableNextS34D0I4]
  have hk := favorable_next_penalty_interval 33 (by omega)
  change nextNormalPenaltyLower ≤ nextNormalPenalty favorableNextS34Before ∧ nextNormalPenalty favorableNextS34Before ≤ nextNormalPenaltyUpper at hk
  have hm : ((0/1)/4)+(8215641/6250000)-(nextNormalPenalty favorableNextS34Before) < ((0/1)/3)+(75892831/50000000)-(nextNormalPenalty favorableNextS34Before) := by
    have h : (((0/1)/4)+(8215641/6250000) : ℝ) < ((0/1)/3)+(75892831/50000000) := by norm_num
    linarith
  have h := index_strict_order_from_intervals ((0/1)/3) ((0/1)/4) (nextNormalPenalty favorableNextS34Before) (nextNormalPenalty favorableNextS34Before) (75892831/50000000) (8215641/6250000)
    (treeBonus (7/5) 33 3) (treeBonus (7/5) 33 4)
    (trajectory_bonus_33_3).1 (trajectory_bonus_33_4).2 hm
  simpa only [treeIndex] using h

theorem favorableNextS34D0Cmp1 : indexScore (7/5) (controlPenalty savedCref uniformQuoteError unitRoleUnused .next) favorableNextS34Before [] (.query 1) < indexScore (7/5) (controlPenalty savedCref uniformQuoteError unitRoleUnused .next) favorableNextS34Before [] (.query 4) := by
  rw [favorableNextS34D0I1,favorableNextS34D0I4]
  have hk := favorable_next_penalty_interval 33 (by omega)
  change nextNormalPenaltyLower ≤ nextNormalPenalty favorableNextS34Before ∧ nextNormalPenalty favorableNextS34Before ≤ nextNormalPenaltyUpper at hk
  have hm : ((1/1)/7)+(49683529/50000000)-0 < ((0/1)/3)+(75892831/50000000)-(nextNormalPenalty favorableNextS34Before) := by
    have h : ((1/1)/7)+(49683529/50000000) < ((0/1)/3)+(75892831/50000000)-nextNormalPenaltyUpper := by norm_num [nextNormalPenaltyUpper,savedCref,uniformQuoteError]
    linarith [hk.2]
  have h := index_strict_order_from_intervals ((0/1)/3) ((1/1)/7) (nextNormalPenalty favorableNextS34Before) 0 (75892831/50000000) (49683529/50000000)
    (treeBonus (7/5) 33 3) (treeBonus (7/5) 33 7)
    (trajectory_bonus_33_3).1 (trajectory_bonus_33_7).2 hm
  simpa only [treeIndex] using h

theorem favorableNextS34D0Cmp2 : indexScore (7/5) (controlPenalty savedCref uniformQuoteError unitRoleUnused .next) favorableNextS34Before [] (.query 2) < indexScore (7/5) (controlPenalty savedCref uniformQuoteError unitRoleUnused .next) favorableNextS34Before [] (.query 4) := by
  rw [favorableNextS34D0I2,favorableNextS34D0I4]
  have hk := favorable_next_penalty_interval 33 (by omega)
  change nextNormalPenaltyLower ≤ nextNormalPenalty favorableNextS34Before ∧ nextNormalPenalty favorableNextS34Before ≤ nextNormalPenaltyUpper at hk
  have hm : ((0/1)/4)+(8215641/6250000)-(nextNormalPenalty favorableNextS34Before) < ((0/1)/3)+(75892831/50000000)-(nextNormalPenalty favorableNextS34Before) := by
    have h : (((0/1)/4)+(8215641/6250000) : ℝ) < ((0/1)/3)+(75892831/50000000) := by norm_num
    linarith
  have h := index_strict_order_from_intervals ((0/1)/3) ((0/1)/4) (nextNormalPenalty favorableNextS34Before) (nextNormalPenalty favorableNextS34Before) (75892831/50000000) (8215641/6250000)
    (treeBonus (7/5) 33 3) (treeBonus (7/5) 33 4)
    (trajectory_bonus_33_3).1 (trajectory_bonus_33_4).2 hm
  simpa only [treeIndex] using h

theorem favorableNextS34D0Cmp3 : indexScore (7/5) (controlPenalty savedCref uniformQuoteError unitRoleUnused .next) favorableNextS34Before [] (.query 3) < indexScore (7/5) (controlPenalty savedCref uniformQuoteError unitRoleUnused .next) favorableNextS34Before [] (.query 4) := by
  rw [favorableNextS34D0I3,favorableNextS34D0I4]
  have hk := favorable_next_penalty_interval 33 (by omega)
  change nextNormalPenaltyLower ≤ nextNormalPenalty favorableNextS34Before ∧ nextNormalPenalty favorableNextS34Before ≤ nextNormalPenaltyUpper at hk
  have hm : ((0/1)/4)+(8215641/6250000)-(nextNormalPenalty favorableNextS34Before) < ((0/1)/3)+(75892831/50000000)-(nextNormalPenalty favorableNextS34Before) := by
    have h : (((0/1)/4)+(8215641/6250000) : ℝ) < ((0/1)/3)+(75892831/50000000) := by norm_num
    linarith
  have h := index_strict_order_from_intervals ((0/1)/3) ((0/1)/4) (nextNormalPenalty favorableNextS34Before) (nextNormalPenalty favorableNextS34Before) (75892831/50000000) (8215641/6250000)
    (treeBonus (7/5) 33 3) (treeBonus (7/5) 33 4)
    (trajectory_bonus_33_3).1 (trajectory_bonus_33_4).2 hm
  simpa only [treeIndex] using h

theorem favorableNextS34D0Cmp5 : indexScore (7/5) (controlPenalty savedCref uniformQuoteError unitRoleUnused .next) favorableNextS34Before [] (.query 5) ≤ indexScore (7/5) (controlPenalty savedCref uniformQuoteError unitRoleUnused .next) favorableNextS34Before [] (.query 4) := by
  rw [favorableNextS34D0I5,favorableNextS34D0I4]
  have hk := favorable_next_penalty_interval 33 (by omega)
  change nextNormalPenaltyLower ≤ nextNormalPenalty favorableNextS34Before ∧ nextNormalPenalty favorableNextS34Before ≤ nextNormalPenaltyUpper at hk
  have hm : ((6/5)/5)+(58786343/50000000)-(nextNormalPenalty favorableNextS34Before) < ((0/1)/3)+(75892831/50000000)-(nextNormalPenalty favorableNextS34Before) := by
    have h : (((6/5)/5)+(58786343/50000000) : ℝ) < ((0/1)/3)+(75892831/50000000) := by norm_num
    linarith
  have h := index_weak_order_from_intervals ((0/1)/3) ((6/5)/5) (nextNormalPenalty favorableNextS34Before) (nextNormalPenalty favorableNextS34Before) (75892831/50000000) (58786343/50000000)
    (treeBonus (7/5) 33 3) (treeBonus (7/5) 33 5)
    (trajectory_bonus_33_3).1 (trajectory_bonus_33_5).2 hm.le
  simpa only [treeIndex] using h

theorem favorableNextS34D0Cmp6 : indexScore (7/5) (controlPenalty savedCref uniformQuoteError unitRoleUnused .next) favorableNextS34Before [] (.query 6) ≤ indexScore (7/5) (controlPenalty savedCref uniformQuoteError unitRoleUnused .next) favorableNextS34Before [] (.query 4) := by
  rw [favorableNextS34D0I6,favorableNextS34D0I4]

theorem favorableNextS34D0Cmp7 : indexScore (7/5) (controlPenalty savedCref uniformQuoteError unitRoleUnused .next) favorableNextS34Before [] (.query 7) ≤ indexScore (7/5) (controlPenalty savedCref uniformQuoteError unitRoleUnused .next) favorableNextS34Before [] (.query 4) := by
  rw [favorableNextS34D0I7,favorableNextS34D0I4]

theorem favorableNextS34Choice0 : nativeFirstChoice (indexScore (7/5) (controlPenalty savedCref uniformQuoteError unitRoleUnused .next) favorableNextS34Before []) favorableNextS34Before [] = .query 4 := by
  apply visited_choice_from_ordered_certificate _ _ [] [.query 0,.query 1,.query 2,.query 3] [.query 5,.query 6,.query 7] (.query 4) (by decide)
  · intro a ha
    have ho : orderedLegalAvailable [] = [.query 0,.query 1,.query 2,.query 3,.query 4,.query 5,.query 6,.query 7] := by decide
    rw [ho] at ha
    simp only [List.mem_cons,List.not_mem_nil,or_false] at ha
    rcases ha with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> decide
  · intro a ha
    simp only [List.mem_cons,List.not_mem_nil,or_false] at ha
    rcases ha with rfl | rfl | rfl | rfl
    · exact favorableNextS34D0Cmp0
    · exact favorableNextS34D0Cmp1
    · exact favorableNextS34D0Cmp2
    · exact favorableNextS34D0Cmp3
  · intro a ha
    simp only [List.mem_cons,List.not_mem_nil,or_false] at ha
    rcases ha with rfl | rfl | rfl
    · exact favorableNextS34D0Cmp5
    · exact favorableNextS34D0Cmp6
    · exact favorableNextS34D0Cmp7

theorem favorableNextS34ActualEvent : nativeEvent budgetTape (7/5) (controlPenalty savedCref uniformQuoteError unitRoleUnused .next)
    (taskReward false (2/5) (1/2)) favorableNextS34Before = favorableNextEvent34 := by
  have hs0 := native_select_existing_step budgetTape (7/5) (controlPenalty savedCref uniformQuoteError unitRoleUnused .next) favorableNextS34Before 8 [] (.query 4)
    (by decide) (by decide) favorableNextS34Choice0
  have hnew := native_select_new_step budgetTape (7/5) (controlPenalty savedCref uniformQuoteError unitRoleUnused .next) favorableNextS34Before 7 [.query 4]
    [.normalRetriever 6,.normalRetriever 7,.normalRetriever 8,.normalRetriever 5,.normalRetriever 1,.normalRetriever 2,.normalRetriever 3,.normalRetriever 12,.normalRetriever 14,.normalRetriever 13,.normalRetriever 21,.normalRetriever 23,.normalRetriever 22,.normalRetriever 9,.normalRetriever 11,.normalRetriever 10,.normalRetriever 15,.normalRetriever 17,.normalRetriever 16,.normalRetriever 18,.normalRetriever 20,.normalRetriever 19,.normalRetriever 24,.normalRetriever 25,.normalRetriever 26,.normalRetriever 27,.normalRetriever 28,.normalRetriever 29] (.normalRetriever 6) (by decide) (by decide) (by decide) (by decide)
  have hs : nativeSelect budgetTape (7/5) (controlPenalty savedCref uniformQuoteError unitRoleUnused .next) favorableNextS34Before 9 [] = [.query 4,.normalRetriever 6] := by
    rw [hs0]
    change nativeSelect budgetTape (7/5) (controlPenalty savedCref uniformQuoteError unitRoleUnused .next) favorableNextS34Before 8 [.query 4] = _
    rw [hnew] <;> rfl
  have hr : repairedRollout budgetTape favorableNextS34Before 9 [.query 4,.normalRetriever 6] = [.query 4,.normalRetriever 6,.selection 0,.width 0,.stop,.reranker 0,.topm 0,.context 0,.answer 0] := by decide
  simp only [nativeEvent,hs,hr]
  rfl

def favorableNextS35Before := favorableNextProposal.take 34

theorem favorableNextS35D0I0 : indexScore (7/5) (controlPenalty savedCref uniformQuoteError unitRoleUnused .next) favorableNextS35Before [] (.query 0) = treeIndex ((0/1)/4) (7/5) (nextNormalPenalty favorableNextS35Before) 34 4 := by
  have hs : replayBackup favorableNextS35Before emptyStatistics ([]++[.query 0]) = ⟨4,(0/1)⟩ := by
    rw [replayBackup_empty_closed_form]
    simp +decide [backedEvents,favorableNextS35Before,favorableNextProposal,favorableNextEvent1,favorableNextEvent2,favorableNextEvent3,favorableNextEvent4,favorableNextEvent5,favorableNextEvent6,favorableNextEvent7,favorableNextEvent8,favorableNextEvent9,favorableNextEvent10,favorableNextEvent11,favorableNextEvent12,favorableNextEvent13,favorableNextEvent14,favorableNextEvent15,favorableNextEvent16,favorableNextEvent17,favorableNextEvent18,favorableNextEvent19,favorableNextEvent20,favorableNextEvent21,favorableNextEvent22,favorableNextEvent23,favorableNextEvent24,favorableNextEvent25,favorableNextEvent26,favorableNextEvent27,favorableNextEvent28,favorableNextEvent29,favorableNextEvent30,favorableNextEvent31,favorableNextEvent32,favorableNextEvent33,favorableNextEvent34,taskReward]
    <;> norm_num
  have hp : rawVisits favorableNextS35Before [] = 34 := by decide
  have hn : rawVisits favorableNextS35Before ([]++[.query 0]) = 4 := by decide
  have hz : (controlPenalty savedCref uniformQuoteError unitRoleUnused .next) favorableNextS35Before [] (.query 0) = (nextNormalPenalty favorableNextS35Before) := by
    simpa only [favorableNextS35Before,nextNormalPenalty] using AgentUCTNextExact.favorable_next_normal_root_quotes_exact 34 (by omega) 0 (by decide)
  unfold indexScore
  rw [hs,hp,hn,hz]
  simp only [BackupStat.mean]
  norm_num

theorem favorableNextS35D0I1 : indexScore (7/5) (controlPenalty savedCref uniformQuoteError unitRoleUnused .next) favorableNextS35Before [] (.query 1) = treeIndex ((1/1)/7) (7/5) 0 34 7 := by
  have hs : replayBackup favorableNextS35Before emptyStatistics ([]++[.query 1]) = ⟨7,(1/1)⟩ := by
    rw [replayBackup_empty_closed_form]
    simp +decide [backedEvents,favorableNextS35Before,favorableNextProposal,favorableNextEvent1,favorableNextEvent2,favorableNextEvent3,favorableNextEvent4,favorableNextEvent5,favorableNextEvent6,favorableNextEvent7,favorableNextEvent8,favorableNextEvent9,favorableNextEvent10,favorableNextEvent11,favorableNextEvent12,favorableNextEvent13,favorableNextEvent14,favorableNextEvent15,favorableNextEvent16,favorableNextEvent17,favorableNextEvent18,favorableNextEvent19,favorableNextEvent20,favorableNextEvent21,favorableNextEvent22,favorableNextEvent23,favorableNextEvent24,favorableNextEvent25,favorableNextEvent26,favorableNextEvent27,favorableNextEvent28,favorableNextEvent29,favorableNextEvent30,favorableNextEvent31,favorableNextEvent32,favorableNextEvent33,favorableNextEvent34,taskReward]
    <;> norm_num
  have hp : rawVisits favorableNextS35Before [] = 34 := by decide
  have hn : rawVisits favorableNextS35Before ([]++[.query 1]) = 7 := by decide
  have hz : (controlPenalty savedCref uniformQuoteError unitRoleUnused .next) favorableNextS35Before [] (.query 1) = 0 := by
    apply control_penalty_empty_suffix
    exact AgentUCTNextExact.favorable_next_hyde_root_suffix_empty 34 (by omega)
  unfold indexScore
  rw [hs,hp,hn,hz]
  simp only [BackupStat.mean]
  norm_num

theorem favorableNextS35D0I2 : indexScore (7/5) (controlPenalty savedCref uniformQuoteError unitRoleUnused .next) favorableNextS35Before [] (.query 2) = treeIndex ((0/1)/4) (7/5) (nextNormalPenalty favorableNextS35Before) 34 4 := by
  have hs : replayBackup favorableNextS35Before emptyStatistics ([]++[.query 2]) = ⟨4,(0/1)⟩ := by
    rw [replayBackup_empty_closed_form]
    simp +decide [backedEvents,favorableNextS35Before,favorableNextProposal,favorableNextEvent1,favorableNextEvent2,favorableNextEvent3,favorableNextEvent4,favorableNextEvent5,favorableNextEvent6,favorableNextEvent7,favorableNextEvent8,favorableNextEvent9,favorableNextEvent10,favorableNextEvent11,favorableNextEvent12,favorableNextEvent13,favorableNextEvent14,favorableNextEvent15,favorableNextEvent16,favorableNextEvent17,favorableNextEvent18,favorableNextEvent19,favorableNextEvent20,favorableNextEvent21,favorableNextEvent22,favorableNextEvent23,favorableNextEvent24,favorableNextEvent25,favorableNextEvent26,favorableNextEvent27,favorableNextEvent28,favorableNextEvent29,favorableNextEvent30,favorableNextEvent31,favorableNextEvent32,favorableNextEvent33,favorableNextEvent34,taskReward]
    <;> norm_num
  have hp : rawVisits favorableNextS35Before [] = 34 := by decide
  have hn : rawVisits favorableNextS35Before ([]++[.query 2]) = 4 := by decide
  have hz : (controlPenalty savedCref uniformQuoteError unitRoleUnused .next) favorableNextS35Before [] (.query 2) = (nextNormalPenalty favorableNextS35Before) := by
    simpa only [favorableNextS35Before,nextNormalPenalty] using AgentUCTNextExact.favorable_next_normal_root_quotes_exact 34 (by omega) 2 (by decide)
  unfold indexScore
  rw [hs,hp,hn,hz]
  simp only [BackupStat.mean]
  norm_num

theorem favorableNextS35D0I3 : indexScore (7/5) (controlPenalty savedCref uniformQuoteError unitRoleUnused .next) favorableNextS35Before [] (.query 3) = treeIndex ((0/1)/4) (7/5) (nextNormalPenalty favorableNextS35Before) 34 4 := by
  have hs : replayBackup favorableNextS35Before emptyStatistics ([]++[.query 3]) = ⟨4,(0/1)⟩ := by
    rw [replayBackup_empty_closed_form]
    simp +decide [backedEvents,favorableNextS35Before,favorableNextProposal,favorableNextEvent1,favorableNextEvent2,favorableNextEvent3,favorableNextEvent4,favorableNextEvent5,favorableNextEvent6,favorableNextEvent7,favorableNextEvent8,favorableNextEvent9,favorableNextEvent10,favorableNextEvent11,favorableNextEvent12,favorableNextEvent13,favorableNextEvent14,favorableNextEvent15,favorableNextEvent16,favorableNextEvent17,favorableNextEvent18,favorableNextEvent19,favorableNextEvent20,favorableNextEvent21,favorableNextEvent22,favorableNextEvent23,favorableNextEvent24,favorableNextEvent25,favorableNextEvent26,favorableNextEvent27,favorableNextEvent28,favorableNextEvent29,favorableNextEvent30,favorableNextEvent31,favorableNextEvent32,favorableNextEvent33,favorableNextEvent34,taskReward]
    <;> norm_num
  have hp : rawVisits favorableNextS35Before [] = 34 := by decide
  have hn : rawVisits favorableNextS35Before ([]++[.query 3]) = 4 := by decide
  have hz : (controlPenalty savedCref uniformQuoteError unitRoleUnused .next) favorableNextS35Before [] (.query 3) = (nextNormalPenalty favorableNextS35Before) := by
    simpa only [favorableNextS35Before,nextNormalPenalty] using AgentUCTNextExact.favorable_next_normal_root_quotes_exact 34 (by omega) 3 (by decide)
  unfold indexScore
  rw [hs,hp,hn,hz]
  simp only [BackupStat.mean]
  norm_num

theorem favorableNextS35D0I4 : indexScore (7/5) (controlPenalty savedCref uniformQuoteError unitRoleUnused .next) favorableNextS35Before [] (.query 4) = treeIndex ((0/1)/4) (7/5) (nextNormalPenalty favorableNextS35Before) 34 4 := by
  have hs : replayBackup favorableNextS35Before emptyStatistics ([]++[.query 4]) = ⟨4,(0/1)⟩ := by
    rw [replayBackup_empty_closed_form]
    simp +decide [backedEvents,favorableNextS35Before,favorableNextProposal,favorableNextEvent1,favorableNextEvent2,favorableNextEvent3,favorableNextEvent4,favorableNextEvent5,favorableNextEvent6,favorableNextEvent7,favorableNextEvent8,favorableNextEvent9,favorableNextEvent10,favorableNextEvent11,favorableNextEvent12,favorableNextEvent13,favorableNextEvent14,favorableNextEvent15,favorableNextEvent16,favorableNextEvent17,favorableNextEvent18,favorableNextEvent19,favorableNextEvent20,favorableNextEvent21,favorableNextEvent22,favorableNextEvent23,favorableNextEvent24,favorableNextEvent25,favorableNextEvent26,favorableNextEvent27,favorableNextEvent28,favorableNextEvent29,favorableNextEvent30,favorableNextEvent31,favorableNextEvent32,favorableNextEvent33,favorableNextEvent34,taskReward]
    <;> norm_num
  have hp : rawVisits favorableNextS35Before [] = 34 := by decide
  have hn : rawVisits favorableNextS35Before ([]++[.query 4]) = 4 := by decide
  have hz : (controlPenalty savedCref uniformQuoteError unitRoleUnused .next) favorableNextS35Before [] (.query 4) = (nextNormalPenalty favorableNextS35Before) := by
    simpa only [favorableNextS35Before,nextNormalPenalty] using AgentUCTNextExact.favorable_next_normal_root_quotes_exact 34 (by omega) 4 (by decide)
  unfold indexScore
  rw [hs,hp,hn,hz]
  simp only [BackupStat.mean]
  norm_num

theorem favorableNextS35D0I5 : indexScore (7/5) (controlPenalty savedCref uniformQuoteError unitRoleUnused .next) favorableNextS35Before [] (.query 5) = treeIndex ((6/5)/5) (7/5) (nextNormalPenalty favorableNextS35Before) 34 5 := by
  have hs : replayBackup favorableNextS35Before emptyStatistics ([]++[.query 5]) = ⟨5,(6/5)⟩ := by
    rw [replayBackup_empty_closed_form]
    simp +decide [backedEvents,favorableNextS35Before,favorableNextProposal,favorableNextEvent1,favorableNextEvent2,favorableNextEvent3,favorableNextEvent4,favorableNextEvent5,favorableNextEvent6,favorableNextEvent7,favorableNextEvent8,favorableNextEvent9,favorableNextEvent10,favorableNextEvent11,favorableNextEvent12,favorableNextEvent13,favorableNextEvent14,favorableNextEvent15,favorableNextEvent16,favorableNextEvent17,favorableNextEvent18,favorableNextEvent19,favorableNextEvent20,favorableNextEvent21,favorableNextEvent22,favorableNextEvent23,favorableNextEvent24,favorableNextEvent25,favorableNextEvent26,favorableNextEvent27,favorableNextEvent28,favorableNextEvent29,favorableNextEvent30,favorableNextEvent31,favorableNextEvent32,favorableNextEvent33,favorableNextEvent34,taskReward]
    <;> norm_num
  have hp : rawVisits favorableNextS35Before [] = 34 := by decide
  have hn : rawVisits favorableNextS35Before ([]++[.query 5]) = 5 := by decide
  have hz : (controlPenalty savedCref uniformQuoteError unitRoleUnused .next) favorableNextS35Before [] (.query 5) = (nextNormalPenalty favorableNextS35Before) := by
    simpa only [favorableNextS35Before,nextNormalPenalty] using AgentUCTNextExact.favorable_next_normal_root_quotes_exact 34 (by omega) 5 (by decide)
  unfold indexScore
  rw [hs,hp,hn,hz]
  simp only [BackupStat.mean]
  norm_num

theorem favorableNextS35D0I6 : indexScore (7/5) (controlPenalty savedCref uniformQuoteError unitRoleUnused .next) favorableNextS35Before [] (.query 6) = treeIndex ((0/1)/3) (7/5) (nextNormalPenalty favorableNextS35Before) 34 3 := by
  have hs : replayBackup favorableNextS35Before emptyStatistics ([]++[.query 6]) = ⟨3,(0/1)⟩ := by
    rw [replayBackup_empty_closed_form]
    simp +decide [backedEvents,favorableNextS35Before,favorableNextProposal,favorableNextEvent1,favorableNextEvent2,favorableNextEvent3,favorableNextEvent4,favorableNextEvent5,favorableNextEvent6,favorableNextEvent7,favorableNextEvent8,favorableNextEvent9,favorableNextEvent10,favorableNextEvent11,favorableNextEvent12,favorableNextEvent13,favorableNextEvent14,favorableNextEvent15,favorableNextEvent16,favorableNextEvent17,favorableNextEvent18,favorableNextEvent19,favorableNextEvent20,favorableNextEvent21,favorableNextEvent22,favorableNextEvent23,favorableNextEvent24,favorableNextEvent25,favorableNextEvent26,favorableNextEvent27,favorableNextEvent28,favorableNextEvent29,favorableNextEvent30,favorableNextEvent31,favorableNextEvent32,favorableNextEvent33,favorableNextEvent34,taskReward]
    <;> norm_num
  have hp : rawVisits favorableNextS35Before [] = 34 := by decide
  have hn : rawVisits favorableNextS35Before ([]++[.query 6]) = 3 := by decide
  have hz : (controlPenalty savedCref uniformQuoteError unitRoleUnused .next) favorableNextS35Before [] (.query 6) = (nextNormalPenalty favorableNextS35Before) := by
    simpa only [favorableNextS35Before,nextNormalPenalty] using AgentUCTNextExact.favorable_next_normal_root_quotes_exact 34 (by omega) 6 (by decide)
  unfold indexScore
  rw [hs,hp,hn,hz]
  simp only [BackupStat.mean]
  norm_num

theorem favorableNextS35D0I7 : indexScore (7/5) (controlPenalty savedCref uniformQuoteError unitRoleUnused .next) favorableNextS35Before [] (.query 7) = treeIndex ((0/1)/3) (7/5) (nextNormalPenalty favorableNextS35Before) 34 3 := by
  have hs : replayBackup favorableNextS35Before emptyStatistics ([]++[.query 7]) = ⟨3,(0/1)⟩ := by
    rw [replayBackup_empty_closed_form]
    simp +decide [backedEvents,favorableNextS35Before,favorableNextProposal,favorableNextEvent1,favorableNextEvent2,favorableNextEvent3,favorableNextEvent4,favorableNextEvent5,favorableNextEvent6,favorableNextEvent7,favorableNextEvent8,favorableNextEvent9,favorableNextEvent10,favorableNextEvent11,favorableNextEvent12,favorableNextEvent13,favorableNextEvent14,favorableNextEvent15,favorableNextEvent16,favorableNextEvent17,favorableNextEvent18,favorableNextEvent19,favorableNextEvent20,favorableNextEvent21,favorableNextEvent22,favorableNextEvent23,favorableNextEvent24,favorableNextEvent25,favorableNextEvent26,favorableNextEvent27,favorableNextEvent28,favorableNextEvent29,favorableNextEvent30,favorableNextEvent31,favorableNextEvent32,favorableNextEvent33,favorableNextEvent34,taskReward]
    <;> norm_num
  have hp : rawVisits favorableNextS35Before [] = 34 := by decide
  have hn : rawVisits favorableNextS35Before ([]++[.query 7]) = 3 := by decide
  have hz : (controlPenalty savedCref uniformQuoteError unitRoleUnused .next) favorableNextS35Before [] (.query 7) = (nextNormalPenalty favorableNextS35Before) := by
    simpa only [favorableNextS35Before,nextNormalPenalty] using AgentUCTNextExact.favorable_next_normal_root_quotes_exact 34 (by omega) 7 (by decide)
  unfold indexScore
  rw [hs,hp,hn,hz]
  simp only [BackupStat.mean]
  norm_num

theorem favorableNextS35D0Cmp0 : indexScore (7/5) (controlPenalty savedCref uniformQuoteError unitRoleUnused .next) favorableNextS35Before [] (.query 0) < indexScore (7/5) (controlPenalty savedCref uniformQuoteError unitRoleUnused .next) favorableNextS35Before [] (.query 6) := by
  rw [favorableNextS35D0I0,favorableNextS35D0I6]
  have hk := favorable_next_penalty_interval 34 (by omega)
  change nextNormalPenaltyLower ≤ nextNormalPenalty favorableNextS35Before ∧ nextNormalPenalty favorableNextS35Before ≤ nextNormalPenaltyUpper at hk
  have hm : ((0/1)/4)+(8249339/6250000)-(nextNormalPenalty favorableNextS35Before) < ((0/1)/3)+(76204121/50000000)-(nextNormalPenalty favorableNextS35Before) := by
    have h : (((0/1)/4)+(8249339/6250000) : ℝ) < ((0/1)/3)+(76204121/50000000) := by norm_num
    linarith
  have h := index_strict_order_from_intervals ((0/1)/3) ((0/1)/4) (nextNormalPenalty favorableNextS35Before) (nextNormalPenalty favorableNextS35Before) (76204121/50000000) (8249339/6250000)
    (treeBonus (7/5) 34 3) (treeBonus (7/5) 34 4)
    (trajectory_bonus_34_3).1 (trajectory_bonus_34_4).2 hm
  simpa only [treeIndex] using h

theorem favorableNextS35D0Cmp1 : indexScore (7/5) (controlPenalty savedCref uniformQuoteError unitRoleUnused .next) favorableNextS35Before [] (.query 1) < indexScore (7/5) (controlPenalty savedCref uniformQuoteError unitRoleUnused .next) favorableNextS35Before [] (.query 6) := by
  rw [favorableNextS35D0I1,favorableNextS35D0I6]
  have hk := favorable_next_penalty_interval 34 (by omega)
  change nextNormalPenaltyLower ≤ nextNormalPenalty favorableNextS35Before ∧ nextNormalPenalty favorableNextS35Before ≤ nextNormalPenaltyUpper at hk
  have hm : ((1/1)/7)+(49887313/50000000)-0 < ((0/1)/3)+(76204121/50000000)-(nextNormalPenalty favorableNextS35Before) := by
    have h : ((1/1)/7)+(49887313/50000000) < ((0/1)/3)+(76204121/50000000)-nextNormalPenaltyUpper := by norm_num [nextNormalPenaltyUpper,savedCref,uniformQuoteError]
    linarith [hk.2]
  have h := index_strict_order_from_intervals ((0/1)/3) ((1/1)/7) (nextNormalPenalty favorableNextS35Before) 0 (76204121/50000000) (49887313/50000000)
    (treeBonus (7/5) 34 3) (treeBonus (7/5) 34 7)
    (trajectory_bonus_34_3).1 (trajectory_bonus_34_7).2 hm
  simpa only [treeIndex] using h

theorem favorableNextS35D0Cmp2 : indexScore (7/5) (controlPenalty savedCref uniformQuoteError unitRoleUnused .next) favorableNextS35Before [] (.query 2) < indexScore (7/5) (controlPenalty savedCref uniformQuoteError unitRoleUnused .next) favorableNextS35Before [] (.query 6) := by
  rw [favorableNextS35D0I2,favorableNextS35D0I6]
  have hk := favorable_next_penalty_interval 34 (by omega)
  change nextNormalPenaltyLower ≤ nextNormalPenalty favorableNextS35Before ∧ nextNormalPenalty favorableNextS35Before ≤ nextNormalPenaltyUpper at hk
  have hm : ((0/1)/4)+(8249339/6250000)-(nextNormalPenalty favorableNextS35Before) < ((0/1)/3)+(76204121/50000000)-(nextNormalPenalty favorableNextS35Before) := by
    have h : (((0/1)/4)+(8249339/6250000) : ℝ) < ((0/1)/3)+(76204121/50000000) := by norm_num
    linarith
  have h := index_strict_order_from_intervals ((0/1)/3) ((0/1)/4) (nextNormalPenalty favorableNextS35Before) (nextNormalPenalty favorableNextS35Before) (76204121/50000000) (8249339/6250000)
    (treeBonus (7/5) 34 3) (treeBonus (7/5) 34 4)
    (trajectory_bonus_34_3).1 (trajectory_bonus_34_4).2 hm
  simpa only [treeIndex] using h

theorem favorableNextS35D0Cmp3 : indexScore (7/5) (controlPenalty savedCref uniformQuoteError unitRoleUnused .next) favorableNextS35Before [] (.query 3) < indexScore (7/5) (controlPenalty savedCref uniformQuoteError unitRoleUnused .next) favorableNextS35Before [] (.query 6) := by
  rw [favorableNextS35D0I3,favorableNextS35D0I6]
  have hk := favorable_next_penalty_interval 34 (by omega)
  change nextNormalPenaltyLower ≤ nextNormalPenalty favorableNextS35Before ∧ nextNormalPenalty favorableNextS35Before ≤ nextNormalPenaltyUpper at hk
  have hm : ((0/1)/4)+(8249339/6250000)-(nextNormalPenalty favorableNextS35Before) < ((0/1)/3)+(76204121/50000000)-(nextNormalPenalty favorableNextS35Before) := by
    have h : (((0/1)/4)+(8249339/6250000) : ℝ) < ((0/1)/3)+(76204121/50000000) := by norm_num
    linarith
  have h := index_strict_order_from_intervals ((0/1)/3) ((0/1)/4) (nextNormalPenalty favorableNextS35Before) (nextNormalPenalty favorableNextS35Before) (76204121/50000000) (8249339/6250000)
    (treeBonus (7/5) 34 3) (treeBonus (7/5) 34 4)
    (trajectory_bonus_34_3).1 (trajectory_bonus_34_4).2 hm
  simpa only [treeIndex] using h

theorem favorableNextS35D0Cmp4 : indexScore (7/5) (controlPenalty savedCref uniformQuoteError unitRoleUnused .next) favorableNextS35Before [] (.query 4) < indexScore (7/5) (controlPenalty savedCref uniformQuoteError unitRoleUnused .next) favorableNextS35Before [] (.query 6) := by
  rw [favorableNextS35D0I4,favorableNextS35D0I6]
  have hk := favorable_next_penalty_interval 34 (by omega)
  change nextNormalPenaltyLower ≤ nextNormalPenalty favorableNextS35Before ∧ nextNormalPenalty favorableNextS35Before ≤ nextNormalPenaltyUpper at hk
  have hm : ((0/1)/4)+(8249339/6250000)-(nextNormalPenalty favorableNextS35Before) < ((0/1)/3)+(76204121/50000000)-(nextNormalPenalty favorableNextS35Before) := by
    have h : (((0/1)/4)+(8249339/6250000) : ℝ) < ((0/1)/3)+(76204121/50000000) := by norm_num
    linarith
  have h := index_strict_order_from_intervals ((0/1)/3) ((0/1)/4) (nextNormalPenalty favorableNextS35Before) (nextNormalPenalty favorableNextS35Before) (76204121/50000000) (8249339/6250000)
    (treeBonus (7/5) 34 3) (treeBonus (7/5) 34 4)
    (trajectory_bonus_34_3).1 (trajectory_bonus_34_4).2 hm
  simpa only [treeIndex] using h

theorem favorableNextS35D0Cmp5 : indexScore (7/5) (controlPenalty savedCref uniformQuoteError unitRoleUnused .next) favorableNextS35Before [] (.query 5) < indexScore (7/5) (controlPenalty savedCref uniformQuoteError unitRoleUnused .next) favorableNextS35Before [] (.query 6) := by
  rw [favorableNextS35D0I5,favorableNextS35D0I6]
  have hk := favorable_next_penalty_interval 34 (by omega)
  change nextNormalPenaltyLower ≤ nextNormalPenalty favorableNextS35Before ∧ nextNormalPenalty favorableNextS35Before ≤ nextNormalPenaltyUpper at hk
  have hm : ((6/5)/5)+(11805493/10000000)-(nextNormalPenalty favorableNextS35Before) < ((0/1)/3)+(76204121/50000000)-(nextNormalPenalty favorableNextS35Before) := by
    have h : (((6/5)/5)+(11805493/10000000) : ℝ) < ((0/1)/3)+(76204121/50000000) := by norm_num
    linarith
  have h := index_strict_order_from_intervals ((0/1)/3) ((6/5)/5) (nextNormalPenalty favorableNextS35Before) (nextNormalPenalty favorableNextS35Before) (76204121/50000000) (11805493/10000000)
    (treeBonus (7/5) 34 3) (treeBonus (7/5) 34 5)
    (trajectory_bonus_34_3).1 (trajectory_bonus_34_5).2 hm
  simpa only [treeIndex] using h

theorem favorableNextS35D0Cmp7 : indexScore (7/5) (controlPenalty savedCref uniformQuoteError unitRoleUnused .next) favorableNextS35Before [] (.query 7) ≤ indexScore (7/5) (controlPenalty savedCref uniformQuoteError unitRoleUnused .next) favorableNextS35Before [] (.query 6) := by
  rw [favorableNextS35D0I7,favorableNextS35D0I6]

theorem favorableNextS35Choice0 : nativeFirstChoice (indexScore (7/5) (controlPenalty savedCref uniformQuoteError unitRoleUnused .next) favorableNextS35Before []) favorableNextS35Before [] = .query 6 := by
  apply visited_choice_from_ordered_certificate _ _ [] [.query 0,.query 1,.query 2,.query 3,.query 4,.query 5] [.query 7] (.query 6) (by decide)
  · intro a ha
    have ho : orderedLegalAvailable [] = [.query 0,.query 1,.query 2,.query 3,.query 4,.query 5,.query 6,.query 7] := by decide
    rw [ho] at ha
    simp only [List.mem_cons,List.not_mem_nil,or_false] at ha
    rcases ha with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> decide
  · intro a ha
    simp only [List.mem_cons,List.not_mem_nil,or_false] at ha
    rcases ha with rfl | rfl | rfl | rfl | rfl | rfl
    · exact favorableNextS35D0Cmp0
    · exact favorableNextS35D0Cmp1
    · exact favorableNextS35D0Cmp2
    · exact favorableNextS35D0Cmp3
    · exact favorableNextS35D0Cmp4
    · exact favorableNextS35D0Cmp5
  · intro a ha
    simp only [List.mem_cons,List.not_mem_nil,or_false] at ha
    rcases ha with rfl
    · exact favorableNextS35D0Cmp7

theorem favorableNextS35ActualEvent : nativeEvent budgetTape (7/5) (controlPenalty savedCref uniformQuoteError unitRoleUnused .next)
    (taskReward false (2/5) (1/2)) favorableNextS35Before = favorableNextEvent35 := by
  have hs0 := native_select_existing_step budgetTape (7/5) (controlPenalty savedCref uniformQuoteError unitRoleUnused .next) favorableNextS35Before 8 [] (.query 6)
    (by decide) (by decide) favorableNextS35Choice0
  have hnew := native_select_new_step budgetTape (7/5) (controlPenalty savedCref uniformQuoteError unitRoleUnused .next) favorableNextS35Before 7 [.query 6]
    [.normalRetriever 6,.normalRetriever 7,.normalRetriever 8,.normalRetriever 5,.normalRetriever 1,.normalRetriever 2,.normalRetriever 3,.normalRetriever 12,.normalRetriever 14,.normalRetriever 13,.normalRetriever 21,.normalRetriever 23,.normalRetriever 22,.normalRetriever 9,.normalRetriever 11,.normalRetriever 10,.normalRetriever 15,.normalRetriever 17,.normalRetriever 16,.normalRetriever 18,.normalRetriever 20,.normalRetriever 19,.normalRetriever 24,.normalRetriever 25,.normalRetriever 26,.normalRetriever 27,.normalRetriever 28,.normalRetriever 29] (.normalRetriever 6) (by decide) (by decide) (by decide) (by decide)
  have hs : nativeSelect budgetTape (7/5) (controlPenalty savedCref uniformQuoteError unitRoleUnused .next) favorableNextS35Before 9 [] = [.query 6,.normalRetriever 6] := by
    rw [hs0]
    change nativeSelect budgetTape (7/5) (controlPenalty savedCref uniformQuoteError unitRoleUnused .next) favorableNextS35Before 8 [.query 6] = _
    rw [hnew] <;> rfl
  have hr : repairedRollout budgetTape favorableNextS35Before 9 [.query 6,.normalRetriever 6] = [.query 6,.normalRetriever 6,.selection 0,.width 0,.stop,.reranker 0,.topm 0,.context 0,.answer 0] := by decide
  simp only [nativeEvent,hs,hr]
  rfl

def favorableNextS36Before := favorableNextProposal.take 35

theorem favorableNextS36D0I0 : indexScore (7/5) (controlPenalty savedCref uniformQuoteError unitRoleUnused .next) favorableNextS36Before [] (.query 0) = treeIndex ((0/1)/4) (7/5) (nextNormalPenalty favorableNextS36Before) 35 4 := by
  have hs : replayBackup favorableNextS36Before emptyStatistics ([]++[.query 0]) = ⟨4,(0/1)⟩ := by
    rw [replayBackup_empty_closed_form]
    simp +decide [backedEvents,favorableNextS36Before,favorableNextProposal,favorableNextEvent1,favorableNextEvent2,favorableNextEvent3,favorableNextEvent4,favorableNextEvent5,favorableNextEvent6,favorableNextEvent7,favorableNextEvent8,favorableNextEvent9,favorableNextEvent10,favorableNextEvent11,favorableNextEvent12,favorableNextEvent13,favorableNextEvent14,favorableNextEvent15,favorableNextEvent16,favorableNextEvent17,favorableNextEvent18,favorableNextEvent19,favorableNextEvent20,favorableNextEvent21,favorableNextEvent22,favorableNextEvent23,favorableNextEvent24,favorableNextEvent25,favorableNextEvent26,favorableNextEvent27,favorableNextEvent28,favorableNextEvent29,favorableNextEvent30,favorableNextEvent31,favorableNextEvent32,favorableNextEvent33,favorableNextEvent34,favorableNextEvent35,taskReward]
    <;> norm_num
  have hp : rawVisits favorableNextS36Before [] = 35 := by decide
  have hn : rawVisits favorableNextS36Before ([]++[.query 0]) = 4 := by decide
  have hz : (controlPenalty savedCref uniformQuoteError unitRoleUnused .next) favorableNextS36Before [] (.query 0) = (nextNormalPenalty favorableNextS36Before) := by
    simpa only [favorableNextS36Before,nextNormalPenalty] using AgentUCTNextExact.favorable_next_normal_root_quotes_exact 35 (by omega) 0 (by decide)
  unfold indexScore
  rw [hs,hp,hn,hz]
  simp only [BackupStat.mean]
  norm_num

theorem favorableNextS36D0I1 : indexScore (7/5) (controlPenalty savedCref uniformQuoteError unitRoleUnused .next) favorableNextS36Before [] (.query 1) = treeIndex ((1/1)/7) (7/5) 0 35 7 := by
  have hs : replayBackup favorableNextS36Before emptyStatistics ([]++[.query 1]) = ⟨7,(1/1)⟩ := by
    rw [replayBackup_empty_closed_form]
    simp +decide [backedEvents,favorableNextS36Before,favorableNextProposal,favorableNextEvent1,favorableNextEvent2,favorableNextEvent3,favorableNextEvent4,favorableNextEvent5,favorableNextEvent6,favorableNextEvent7,favorableNextEvent8,favorableNextEvent9,favorableNextEvent10,favorableNextEvent11,favorableNextEvent12,favorableNextEvent13,favorableNextEvent14,favorableNextEvent15,favorableNextEvent16,favorableNextEvent17,favorableNextEvent18,favorableNextEvent19,favorableNextEvent20,favorableNextEvent21,favorableNextEvent22,favorableNextEvent23,favorableNextEvent24,favorableNextEvent25,favorableNextEvent26,favorableNextEvent27,favorableNextEvent28,favorableNextEvent29,favorableNextEvent30,favorableNextEvent31,favorableNextEvent32,favorableNextEvent33,favorableNextEvent34,favorableNextEvent35,taskReward]
    <;> norm_num
  have hp : rawVisits favorableNextS36Before [] = 35 := by decide
  have hn : rawVisits favorableNextS36Before ([]++[.query 1]) = 7 := by decide
  have hz : (controlPenalty savedCref uniformQuoteError unitRoleUnused .next) favorableNextS36Before [] (.query 1) = 0 := by
    apply control_penalty_empty_suffix
    exact AgentUCTNextExact.favorable_next_hyde_root_suffix_empty 35 (by omega)
  unfold indexScore
  rw [hs,hp,hn,hz]
  simp only [BackupStat.mean]
  norm_num

theorem favorableNextS36D0I2 : indexScore (7/5) (controlPenalty savedCref uniformQuoteError unitRoleUnused .next) favorableNextS36Before [] (.query 2) = treeIndex ((0/1)/4) (7/5) (nextNormalPenalty favorableNextS36Before) 35 4 := by
  have hs : replayBackup favorableNextS36Before emptyStatistics ([]++[.query 2]) = ⟨4,(0/1)⟩ := by
    rw [replayBackup_empty_closed_form]
    simp +decide [backedEvents,favorableNextS36Before,favorableNextProposal,favorableNextEvent1,favorableNextEvent2,favorableNextEvent3,favorableNextEvent4,favorableNextEvent5,favorableNextEvent6,favorableNextEvent7,favorableNextEvent8,favorableNextEvent9,favorableNextEvent10,favorableNextEvent11,favorableNextEvent12,favorableNextEvent13,favorableNextEvent14,favorableNextEvent15,favorableNextEvent16,favorableNextEvent17,favorableNextEvent18,favorableNextEvent19,favorableNextEvent20,favorableNextEvent21,favorableNextEvent22,favorableNextEvent23,favorableNextEvent24,favorableNextEvent25,favorableNextEvent26,favorableNextEvent27,favorableNextEvent28,favorableNextEvent29,favorableNextEvent30,favorableNextEvent31,favorableNextEvent32,favorableNextEvent33,favorableNextEvent34,favorableNextEvent35,taskReward]
    <;> norm_num
  have hp : rawVisits favorableNextS36Before [] = 35 := by decide
  have hn : rawVisits favorableNextS36Before ([]++[.query 2]) = 4 := by decide
  have hz : (controlPenalty savedCref uniformQuoteError unitRoleUnused .next) favorableNextS36Before [] (.query 2) = (nextNormalPenalty favorableNextS36Before) := by
    simpa only [favorableNextS36Before,nextNormalPenalty] using AgentUCTNextExact.favorable_next_normal_root_quotes_exact 35 (by omega) 2 (by decide)
  unfold indexScore
  rw [hs,hp,hn,hz]
  simp only [BackupStat.mean]
  norm_num

theorem favorableNextS36D0I3 : indexScore (7/5) (controlPenalty savedCref uniformQuoteError unitRoleUnused .next) favorableNextS36Before [] (.query 3) = treeIndex ((0/1)/4) (7/5) (nextNormalPenalty favorableNextS36Before) 35 4 := by
  have hs : replayBackup favorableNextS36Before emptyStatistics ([]++[.query 3]) = ⟨4,(0/1)⟩ := by
    rw [replayBackup_empty_closed_form]
    simp +decide [backedEvents,favorableNextS36Before,favorableNextProposal,favorableNextEvent1,favorableNextEvent2,favorableNextEvent3,favorableNextEvent4,favorableNextEvent5,favorableNextEvent6,favorableNextEvent7,favorableNextEvent8,favorableNextEvent9,favorableNextEvent10,favorableNextEvent11,favorableNextEvent12,favorableNextEvent13,favorableNextEvent14,favorableNextEvent15,favorableNextEvent16,favorableNextEvent17,favorableNextEvent18,favorableNextEvent19,favorableNextEvent20,favorableNextEvent21,favorableNextEvent22,favorableNextEvent23,favorableNextEvent24,favorableNextEvent25,favorableNextEvent26,favorableNextEvent27,favorableNextEvent28,favorableNextEvent29,favorableNextEvent30,favorableNextEvent31,favorableNextEvent32,favorableNextEvent33,favorableNextEvent34,favorableNextEvent35,taskReward]
    <;> norm_num
  have hp : rawVisits favorableNextS36Before [] = 35 := by decide
  have hn : rawVisits favorableNextS36Before ([]++[.query 3]) = 4 := by decide
  have hz : (controlPenalty savedCref uniformQuoteError unitRoleUnused .next) favorableNextS36Before [] (.query 3) = (nextNormalPenalty favorableNextS36Before) := by
    simpa only [favorableNextS36Before,nextNormalPenalty] using AgentUCTNextExact.favorable_next_normal_root_quotes_exact 35 (by omega) 3 (by decide)
  unfold indexScore
  rw [hs,hp,hn,hz]
  simp only [BackupStat.mean]
  norm_num

theorem favorableNextS36D0I4 : indexScore (7/5) (controlPenalty savedCref uniformQuoteError unitRoleUnused .next) favorableNextS36Before [] (.query 4) = treeIndex ((0/1)/4) (7/5) (nextNormalPenalty favorableNextS36Before) 35 4 := by
  have hs : replayBackup favorableNextS36Before emptyStatistics ([]++[.query 4]) = ⟨4,(0/1)⟩ := by
    rw [replayBackup_empty_closed_form]
    simp +decide [backedEvents,favorableNextS36Before,favorableNextProposal,favorableNextEvent1,favorableNextEvent2,favorableNextEvent3,favorableNextEvent4,favorableNextEvent5,favorableNextEvent6,favorableNextEvent7,favorableNextEvent8,favorableNextEvent9,favorableNextEvent10,favorableNextEvent11,favorableNextEvent12,favorableNextEvent13,favorableNextEvent14,favorableNextEvent15,favorableNextEvent16,favorableNextEvent17,favorableNextEvent18,favorableNextEvent19,favorableNextEvent20,favorableNextEvent21,favorableNextEvent22,favorableNextEvent23,favorableNextEvent24,favorableNextEvent25,favorableNextEvent26,favorableNextEvent27,favorableNextEvent28,favorableNextEvent29,favorableNextEvent30,favorableNextEvent31,favorableNextEvent32,favorableNextEvent33,favorableNextEvent34,favorableNextEvent35,taskReward]
    <;> norm_num
  have hp : rawVisits favorableNextS36Before [] = 35 := by decide
  have hn : rawVisits favorableNextS36Before ([]++[.query 4]) = 4 := by decide
  have hz : (controlPenalty savedCref uniformQuoteError unitRoleUnused .next) favorableNextS36Before [] (.query 4) = (nextNormalPenalty favorableNextS36Before) := by
    simpa only [favorableNextS36Before,nextNormalPenalty] using AgentUCTNextExact.favorable_next_normal_root_quotes_exact 35 (by omega) 4 (by decide)
  unfold indexScore
  rw [hs,hp,hn,hz]
  simp only [BackupStat.mean]
  norm_num

theorem favorableNextS36D0I5 : indexScore (7/5) (controlPenalty savedCref uniformQuoteError unitRoleUnused .next) favorableNextS36Before [] (.query 5) = treeIndex ((6/5)/5) (7/5) (nextNormalPenalty favorableNextS36Before) 35 5 := by
  have hs : replayBackup favorableNextS36Before emptyStatistics ([]++[.query 5]) = ⟨5,(6/5)⟩ := by
    rw [replayBackup_empty_closed_form]
    simp +decide [backedEvents,favorableNextS36Before,favorableNextProposal,favorableNextEvent1,favorableNextEvent2,favorableNextEvent3,favorableNextEvent4,favorableNextEvent5,favorableNextEvent6,favorableNextEvent7,favorableNextEvent8,favorableNextEvent9,favorableNextEvent10,favorableNextEvent11,favorableNextEvent12,favorableNextEvent13,favorableNextEvent14,favorableNextEvent15,favorableNextEvent16,favorableNextEvent17,favorableNextEvent18,favorableNextEvent19,favorableNextEvent20,favorableNextEvent21,favorableNextEvent22,favorableNextEvent23,favorableNextEvent24,favorableNextEvent25,favorableNextEvent26,favorableNextEvent27,favorableNextEvent28,favorableNextEvent29,favorableNextEvent30,favorableNextEvent31,favorableNextEvent32,favorableNextEvent33,favorableNextEvent34,favorableNextEvent35,taskReward]
    <;> norm_num
  have hp : rawVisits favorableNextS36Before [] = 35 := by decide
  have hn : rawVisits favorableNextS36Before ([]++[.query 5]) = 5 := by decide
  have hz : (controlPenalty savedCref uniformQuoteError unitRoleUnused .next) favorableNextS36Before [] (.query 5) = (nextNormalPenalty favorableNextS36Before) := by
    simpa only [favorableNextS36Before,nextNormalPenalty] using AgentUCTNextExact.favorable_next_normal_root_quotes_exact 35 (by omega) 5 (by decide)
  unfold indexScore
  rw [hs,hp,hn,hz]
  simp only [BackupStat.mean]
  norm_num

theorem favorableNextS36D0I6 : indexScore (7/5) (controlPenalty savedCref uniformQuoteError unitRoleUnused .next) favorableNextS36Before [] (.query 6) = treeIndex ((0/1)/4) (7/5) (nextNormalPenalty favorableNextS36Before) 35 4 := by
  have hs : replayBackup favorableNextS36Before emptyStatistics ([]++[.query 6]) = ⟨4,(0/1)⟩ := by
    rw [replayBackup_empty_closed_form]
    simp +decide [backedEvents,favorableNextS36Before,favorableNextProposal,favorableNextEvent1,favorableNextEvent2,favorableNextEvent3,favorableNextEvent4,favorableNextEvent5,favorableNextEvent6,favorableNextEvent7,favorableNextEvent8,favorableNextEvent9,favorableNextEvent10,favorableNextEvent11,favorableNextEvent12,favorableNextEvent13,favorableNextEvent14,favorableNextEvent15,favorableNextEvent16,favorableNextEvent17,favorableNextEvent18,favorableNextEvent19,favorableNextEvent20,favorableNextEvent21,favorableNextEvent22,favorableNextEvent23,favorableNextEvent24,favorableNextEvent25,favorableNextEvent26,favorableNextEvent27,favorableNextEvent28,favorableNextEvent29,favorableNextEvent30,favorableNextEvent31,favorableNextEvent32,favorableNextEvent33,favorableNextEvent34,favorableNextEvent35,taskReward]
    <;> norm_num
  have hp : rawVisits favorableNextS36Before [] = 35 := by decide
  have hn : rawVisits favorableNextS36Before ([]++[.query 6]) = 4 := by decide
  have hz : (controlPenalty savedCref uniformQuoteError unitRoleUnused .next) favorableNextS36Before [] (.query 6) = (nextNormalPenalty favorableNextS36Before) := by
    simpa only [favorableNextS36Before,nextNormalPenalty] using AgentUCTNextExact.favorable_next_normal_root_quotes_exact 35 (by omega) 6 (by decide)
  unfold indexScore
  rw [hs,hp,hn,hz]
  simp only [BackupStat.mean]
  norm_num

theorem favorableNextS36D0I7 : indexScore (7/5) (controlPenalty savedCref uniformQuoteError unitRoleUnused .next) favorableNextS36Before [] (.query 7) = treeIndex ((0/1)/3) (7/5) (nextNormalPenalty favorableNextS36Before) 35 3 := by
  have hs : replayBackup favorableNextS36Before emptyStatistics ([]++[.query 7]) = ⟨3,(0/1)⟩ := by
    rw [replayBackup_empty_closed_form]
    simp +decide [backedEvents,favorableNextS36Before,favorableNextProposal,favorableNextEvent1,favorableNextEvent2,favorableNextEvent3,favorableNextEvent4,favorableNextEvent5,favorableNextEvent6,favorableNextEvent7,favorableNextEvent8,favorableNextEvent9,favorableNextEvent10,favorableNextEvent11,favorableNextEvent12,favorableNextEvent13,favorableNextEvent14,favorableNextEvent15,favorableNextEvent16,favorableNextEvent17,favorableNextEvent18,favorableNextEvent19,favorableNextEvent20,favorableNextEvent21,favorableNextEvent22,favorableNextEvent23,favorableNextEvent24,favorableNextEvent25,favorableNextEvent26,favorableNextEvent27,favorableNextEvent28,favorableNextEvent29,favorableNextEvent30,favorableNextEvent31,favorableNextEvent32,favorableNextEvent33,favorableNextEvent34,favorableNextEvent35,taskReward]
    <;> norm_num
  have hp : rawVisits favorableNextS36Before [] = 35 := by decide
  have hn : rawVisits favorableNextS36Before ([]++[.query 7]) = 3 := by decide
  have hz : (controlPenalty savedCref uniformQuoteError unitRoleUnused .next) favorableNextS36Before [] (.query 7) = (nextNormalPenalty favorableNextS36Before) := by
    simpa only [favorableNextS36Before,nextNormalPenalty] using AgentUCTNextExact.favorable_next_normal_root_quotes_exact 35 (by omega) 7 (by decide)
  unfold indexScore
  rw [hs,hp,hn,hz]
  simp only [BackupStat.mean]
  norm_num

theorem favorableNextS36D0Cmp0 : indexScore (7/5) (controlPenalty savedCref uniformQuoteError unitRoleUnused .next) favorableNextS36Before [] (.query 0) < indexScore (7/5) (controlPenalty savedCref uniformQuoteError unitRoleUnused .next) favorableNextS36Before [] (.query 7) := by
  rw [favorableNextS36D0I0,favorableNextS36D0I7]
  have hk := favorable_next_penalty_interval 35 (by omega)
  change nextNormalPenaltyLower ≤ nextNormalPenalty favorableNextS36Before ∧ nextNormalPenalty favorableNextS36Before ≤ nextNormalPenaltyUpper at hk
  have hm : ((0/1)/4)+(66255651/50000000)-(nextNormalPenalty favorableNextS36Before) < ((0/1)/3)+(76505429/50000000)-(nextNormalPenalty favorableNextS36Before) := by
    have h : (((0/1)/4)+(66255651/50000000) : ℝ) < ((0/1)/3)+(76505429/50000000) := by norm_num
    linarith
  have h := index_strict_order_from_intervals ((0/1)/3) ((0/1)/4) (nextNormalPenalty favorableNextS36Before) (nextNormalPenalty favorableNextS36Before) (76505429/50000000) (66255651/50000000)
    (treeBonus (7/5) 35 3) (treeBonus (7/5) 35 4)
    (trajectory_bonus_35_3).1 (trajectory_bonus_35_4).2 hm
  simpa only [treeIndex] using h

theorem favorableNextS36D0Cmp1 : indexScore (7/5) (controlPenalty savedCref uniformQuoteError unitRoleUnused .next) favorableNextS36Before [] (.query 1) < indexScore (7/5) (controlPenalty savedCref uniformQuoteError unitRoleUnused .next) favorableNextS36Before [] (.query 7) := by
  rw [favorableNextS36D0I1,favorableNextS36D0I7]
  have hk := favorable_next_penalty_interval 35 (by omega)
  change nextNormalPenaltyLower ≤ nextNormalPenalty favorableNextS36Before ∧ nextNormalPenalty favorableNextS36Before ≤ nextNormalPenaltyUpper at hk
  have hm : ((1/1)/7)+(25042283/25000000)-0 < ((0/1)/3)+(76505429/50000000)-(nextNormalPenalty favorableNextS36Before) := by
    have h : ((1/1)/7)+(25042283/25000000) < ((0/1)/3)+(76505429/50000000)-nextNormalPenaltyUpper := by norm_num [nextNormalPenaltyUpper,savedCref,uniformQuoteError]
    linarith [hk.2]
  have h := index_strict_order_from_intervals ((0/1)/3) ((1/1)/7) (nextNormalPenalty favorableNextS36Before) 0 (76505429/50000000) (25042283/25000000)
    (treeBonus (7/5) 35 3) (treeBonus (7/5) 35 7)
    (trajectory_bonus_35_3).1 (trajectory_bonus_35_7).2 hm
  simpa only [treeIndex] using h

theorem favorableNextS36D0Cmp2 : indexScore (7/5) (controlPenalty savedCref uniformQuoteError unitRoleUnused .next) favorableNextS36Before [] (.query 2) < indexScore (7/5) (controlPenalty savedCref uniformQuoteError unitRoleUnused .next) favorableNextS36Before [] (.query 7) := by
  rw [favorableNextS36D0I2,favorableNextS36D0I7]
  have hk := favorable_next_penalty_interval 35 (by omega)
  change nextNormalPenaltyLower ≤ nextNormalPenalty favorableNextS36Before ∧ nextNormalPenalty favorableNextS36Before ≤ nextNormalPenaltyUpper at hk
  have hm : ((0/1)/4)+(66255651/50000000)-(nextNormalPenalty favorableNextS36Before) < ((0/1)/3)+(76505429/50000000)-(nextNormalPenalty favorableNextS36Before) := by
    have h : (((0/1)/4)+(66255651/50000000) : ℝ) < ((0/1)/3)+(76505429/50000000) := by norm_num
    linarith
  have h := index_strict_order_from_intervals ((0/1)/3) ((0/1)/4) (nextNormalPenalty favorableNextS36Before) (nextNormalPenalty favorableNextS36Before) (76505429/50000000) (66255651/50000000)
    (treeBonus (7/5) 35 3) (treeBonus (7/5) 35 4)
    (trajectory_bonus_35_3).1 (trajectory_bonus_35_4).2 hm
  simpa only [treeIndex] using h

theorem favorableNextS36D0Cmp3 : indexScore (7/5) (controlPenalty savedCref uniformQuoteError unitRoleUnused .next) favorableNextS36Before [] (.query 3) < indexScore (7/5) (controlPenalty savedCref uniformQuoteError unitRoleUnused .next) favorableNextS36Before [] (.query 7) := by
  rw [favorableNextS36D0I3,favorableNextS36D0I7]
  have hk := favorable_next_penalty_interval 35 (by omega)
  change nextNormalPenaltyLower ≤ nextNormalPenalty favorableNextS36Before ∧ nextNormalPenalty favorableNextS36Before ≤ nextNormalPenaltyUpper at hk
  have hm : ((0/1)/4)+(66255651/50000000)-(nextNormalPenalty favorableNextS36Before) < ((0/1)/3)+(76505429/50000000)-(nextNormalPenalty favorableNextS36Before) := by
    have h : (((0/1)/4)+(66255651/50000000) : ℝ) < ((0/1)/3)+(76505429/50000000) := by norm_num
    linarith
  have h := index_strict_order_from_intervals ((0/1)/3) ((0/1)/4) (nextNormalPenalty favorableNextS36Before) (nextNormalPenalty favorableNextS36Before) (76505429/50000000) (66255651/50000000)
    (treeBonus (7/5) 35 3) (treeBonus (7/5) 35 4)
    (trajectory_bonus_35_3).1 (trajectory_bonus_35_4).2 hm
  simpa only [treeIndex] using h

theorem favorableNextS36D0Cmp4 : indexScore (7/5) (controlPenalty savedCref uniformQuoteError unitRoleUnused .next) favorableNextS36Before [] (.query 4) < indexScore (7/5) (controlPenalty savedCref uniformQuoteError unitRoleUnused .next) favorableNextS36Before [] (.query 7) := by
  rw [favorableNextS36D0I4,favorableNextS36D0I7]
  have hk := favorable_next_penalty_interval 35 (by omega)
  change nextNormalPenaltyLower ≤ nextNormalPenalty favorableNextS36Before ∧ nextNormalPenalty favorableNextS36Before ≤ nextNormalPenaltyUpper at hk
  have hm : ((0/1)/4)+(66255651/50000000)-(nextNormalPenalty favorableNextS36Before) < ((0/1)/3)+(76505429/50000000)-(nextNormalPenalty favorableNextS36Before) := by
    have h : (((0/1)/4)+(66255651/50000000) : ℝ) < ((0/1)/3)+(76505429/50000000) := by norm_num
    linarith
  have h := index_strict_order_from_intervals ((0/1)/3) ((0/1)/4) (nextNormalPenalty favorableNextS36Before) (nextNormalPenalty favorableNextS36Before) (76505429/50000000) (66255651/50000000)
    (treeBonus (7/5) 35 3) (treeBonus (7/5) 35 4)
    (trajectory_bonus_35_3).1 (trajectory_bonus_35_4).2 hm
  simpa only [treeIndex] using h

theorem favorableNextS36D0Cmp5 : indexScore (7/5) (controlPenalty savedCref uniformQuoteError unitRoleUnused .next) favorableNextS36Before [] (.query 5) < indexScore (7/5) (controlPenalty savedCref uniformQuoteError unitRoleUnused .next) favorableNextS36Before [] (.query 7) := by
  rw [favorableNextS36D0I5,favorableNextS36D0I7]
  have hk := favorable_next_penalty_interval 35 (by omega)
  change nextNormalPenaltyLower ≤ nextNormalPenalty favorableNextS36Before ∧ nextNormalPenalty favorableNextS36Before ≤ nextNormalPenaltyUpper at hk
  have hm : ((6/5)/5)+(59260859/50000000)-(nextNormalPenalty favorableNextS36Before) < ((0/1)/3)+(76505429/50000000)-(nextNormalPenalty favorableNextS36Before) := by
    have h : (((6/5)/5)+(59260859/50000000) : ℝ) < ((0/1)/3)+(76505429/50000000) := by norm_num
    linarith
  have h := index_strict_order_from_intervals ((0/1)/3) ((6/5)/5) (nextNormalPenalty favorableNextS36Before) (nextNormalPenalty favorableNextS36Before) (76505429/50000000) (59260859/50000000)
    (treeBonus (7/5) 35 3) (treeBonus (7/5) 35 5)
    (trajectory_bonus_35_3).1 (trajectory_bonus_35_5).2 hm
  simpa only [treeIndex] using h

theorem favorableNextS36D0Cmp6 : indexScore (7/5) (controlPenalty savedCref uniformQuoteError unitRoleUnused .next) favorableNextS36Before [] (.query 6) < indexScore (7/5) (controlPenalty savedCref uniformQuoteError unitRoleUnused .next) favorableNextS36Before [] (.query 7) := by
  rw [favorableNextS36D0I6,favorableNextS36D0I7]
  have hk := favorable_next_penalty_interval 35 (by omega)
  change nextNormalPenaltyLower ≤ nextNormalPenalty favorableNextS36Before ∧ nextNormalPenalty favorableNextS36Before ≤ nextNormalPenaltyUpper at hk
  have hm : ((0/1)/4)+(66255651/50000000)-(nextNormalPenalty favorableNextS36Before) < ((0/1)/3)+(76505429/50000000)-(nextNormalPenalty favorableNextS36Before) := by
    have h : (((0/1)/4)+(66255651/50000000) : ℝ) < ((0/1)/3)+(76505429/50000000) := by norm_num
    linarith
  have h := index_strict_order_from_intervals ((0/1)/3) ((0/1)/4) (nextNormalPenalty favorableNextS36Before) (nextNormalPenalty favorableNextS36Before) (76505429/50000000) (66255651/50000000)
    (treeBonus (7/5) 35 3) (treeBonus (7/5) 35 4)
    (trajectory_bonus_35_3).1 (trajectory_bonus_35_4).2 hm
  simpa only [treeIndex] using h

theorem favorableNextS36Choice0 : nativeFirstChoice (indexScore (7/5) (controlPenalty savedCref uniformQuoteError unitRoleUnused .next) favorableNextS36Before []) favorableNextS36Before [] = .query 7 := by
  apply visited_choice_from_ordered_certificate _ _ [] [.query 0,.query 1,.query 2,.query 3,.query 4,.query 5,.query 6] [] (.query 7) (by decide)
  · intro a ha
    have ho : orderedLegalAvailable [] = [.query 0,.query 1,.query 2,.query 3,.query 4,.query 5,.query 6,.query 7] := by decide
    rw [ho] at ha
    simp only [List.mem_cons,List.not_mem_nil,or_false] at ha
    rcases ha with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> decide
  · intro a ha
    simp only [List.mem_cons,List.not_mem_nil,or_false] at ha
    rcases ha with rfl | rfl | rfl | rfl | rfl | rfl | rfl
    · exact favorableNextS36D0Cmp0
    · exact favorableNextS36D0Cmp1
    · exact favorableNextS36D0Cmp2
    · exact favorableNextS36D0Cmp3
    · exact favorableNextS36D0Cmp4
    · exact favorableNextS36D0Cmp5
    · exact favorableNextS36D0Cmp6
  · simp

theorem favorableNextS36ActualEvent : nativeEvent budgetTape (7/5) (controlPenalty savedCref uniformQuoteError unitRoleUnused .next)
    (taskReward false (2/5) (1/2)) favorableNextS36Before = favorableNextEvent36 := by
  have hs0 := native_select_existing_step budgetTape (7/5) (controlPenalty savedCref uniformQuoteError unitRoleUnused .next) favorableNextS36Before 8 [] (.query 7)
    (by decide) (by decide) favorableNextS36Choice0
  have hnew := native_select_new_step budgetTape (7/5) (controlPenalty savedCref uniformQuoteError unitRoleUnused .next) favorableNextS36Before 7 [.query 7]
    [.normalRetriever 6,.normalRetriever 7,.normalRetriever 8,.normalRetriever 5,.normalRetriever 1,.normalRetriever 2,.normalRetriever 3,.normalRetriever 12,.normalRetriever 14,.normalRetriever 13,.normalRetriever 21,.normalRetriever 23,.normalRetriever 22,.normalRetriever 9,.normalRetriever 11,.normalRetriever 10,.normalRetriever 15,.normalRetriever 17,.normalRetriever 16,.normalRetriever 18,.normalRetriever 20,.normalRetriever 19,.normalRetriever 24,.normalRetriever 25,.normalRetriever 26,.normalRetriever 27,.normalRetriever 28,.normalRetriever 29] (.normalRetriever 6) (by decide) (by decide) (by decide) (by decide)
  have hs : nativeSelect budgetTape (7/5) (controlPenalty savedCref uniformQuoteError unitRoleUnused .next) favorableNextS36Before 9 [] = [.query 7,.normalRetriever 6] := by
    rw [hs0]
    change nativeSelect budgetTape (7/5) (controlPenalty savedCref uniformQuoteError unitRoleUnused .next) favorableNextS36Before 8 [.query 7] = _
    rw [hnew] <;> rfl
  have hr : repairedRollout budgetTape favorableNextS36Before 9 [.query 7,.normalRetriever 6] = [.query 7,.normalRetriever 6,.selection 0,.width 0,.stop,.reranker 0,.topm 0,.context 0,.answer 0] := by decide
  simp only [nativeEvent,hs,hr]
  rfl

def favorableNextS37Before := favorableNextProposal.take 36

theorem favorableNextS37D0I0 : indexScore (7/5) (controlPenalty savedCref uniformQuoteError unitRoleUnused .next) favorableNextS37Before [] (.query 0) = treeIndex ((0/1)/4) (7/5) (nextNormalPenalty favorableNextS37Before) 36 4 := by
  have hs : replayBackup favorableNextS37Before emptyStatistics ([]++[.query 0]) = ⟨4,(0/1)⟩ := by
    rw [replayBackup_empty_closed_form]
    simp +decide [backedEvents,favorableNextS37Before,favorableNextProposal,favorableNextEvent1,favorableNextEvent2,favorableNextEvent3,favorableNextEvent4,favorableNextEvent5,favorableNextEvent6,favorableNextEvent7,favorableNextEvent8,favorableNextEvent9,favorableNextEvent10,favorableNextEvent11,favorableNextEvent12,favorableNextEvent13,favorableNextEvent14,favorableNextEvent15,favorableNextEvent16,favorableNextEvent17,favorableNextEvent18,favorableNextEvent19,favorableNextEvent20,favorableNextEvent21,favorableNextEvent22,favorableNextEvent23,favorableNextEvent24,favorableNextEvent25,favorableNextEvent26,favorableNextEvent27,favorableNextEvent28,favorableNextEvent29,favorableNextEvent30,favorableNextEvent31,favorableNextEvent32,favorableNextEvent33,favorableNextEvent34,favorableNextEvent35,favorableNextEvent36,taskReward]
    <;> norm_num
  have hp : rawVisits favorableNextS37Before [] = 36 := by decide
  have hn : rawVisits favorableNextS37Before ([]++[.query 0]) = 4 := by decide
  have hz : (controlPenalty savedCref uniformQuoteError unitRoleUnused .next) favorableNextS37Before [] (.query 0) = (nextNormalPenalty favorableNextS37Before) := by
    simpa only [favorableNextS37Before,nextNormalPenalty] using AgentUCTNextExact.favorable_next_normal_root_quotes_exact 36 (by omega) 0 (by decide)
  unfold indexScore
  rw [hs,hp,hn,hz]
  simp only [BackupStat.mean]
  norm_num

theorem favorableNextS37D0I1 : indexScore (7/5) (controlPenalty savedCref uniformQuoteError unitRoleUnused .next) favorableNextS37Before [] (.query 1) = treeIndex ((1/1)/7) (7/5) 0 36 7 := by
  have hs : replayBackup favorableNextS37Before emptyStatistics ([]++[.query 1]) = ⟨7,(1/1)⟩ := by
    rw [replayBackup_empty_closed_form]
    simp +decide [backedEvents,favorableNextS37Before,favorableNextProposal,favorableNextEvent1,favorableNextEvent2,favorableNextEvent3,favorableNextEvent4,favorableNextEvent5,favorableNextEvent6,favorableNextEvent7,favorableNextEvent8,favorableNextEvent9,favorableNextEvent10,favorableNextEvent11,favorableNextEvent12,favorableNextEvent13,favorableNextEvent14,favorableNextEvent15,favorableNextEvent16,favorableNextEvent17,favorableNextEvent18,favorableNextEvent19,favorableNextEvent20,favorableNextEvent21,favorableNextEvent22,favorableNextEvent23,favorableNextEvent24,favorableNextEvent25,favorableNextEvent26,favorableNextEvent27,favorableNextEvent28,favorableNextEvent29,favorableNextEvent30,favorableNextEvent31,favorableNextEvent32,favorableNextEvent33,favorableNextEvent34,favorableNextEvent35,favorableNextEvent36,taskReward]
    <;> norm_num
  have hp : rawVisits favorableNextS37Before [] = 36 := by decide
  have hn : rawVisits favorableNextS37Before ([]++[.query 1]) = 7 := by decide
  have hz : (controlPenalty savedCref uniformQuoteError unitRoleUnused .next) favorableNextS37Before [] (.query 1) = 0 := by
    apply control_penalty_empty_suffix
    exact AgentUCTNextExact.favorable_next_hyde_root_suffix_empty 36 (by omega)
  unfold indexScore
  rw [hs,hp,hn,hz]
  simp only [BackupStat.mean]
  norm_num

theorem favorableNextS37D0I2 : indexScore (7/5) (controlPenalty savedCref uniformQuoteError unitRoleUnused .next) favorableNextS37Before [] (.query 2) = treeIndex ((0/1)/4) (7/5) (nextNormalPenalty favorableNextS37Before) 36 4 := by
  have hs : replayBackup favorableNextS37Before emptyStatistics ([]++[.query 2]) = ⟨4,(0/1)⟩ := by
    rw [replayBackup_empty_closed_form]
    simp +decide [backedEvents,favorableNextS37Before,favorableNextProposal,favorableNextEvent1,favorableNextEvent2,favorableNextEvent3,favorableNextEvent4,favorableNextEvent5,favorableNextEvent6,favorableNextEvent7,favorableNextEvent8,favorableNextEvent9,favorableNextEvent10,favorableNextEvent11,favorableNextEvent12,favorableNextEvent13,favorableNextEvent14,favorableNextEvent15,favorableNextEvent16,favorableNextEvent17,favorableNextEvent18,favorableNextEvent19,favorableNextEvent20,favorableNextEvent21,favorableNextEvent22,favorableNextEvent23,favorableNextEvent24,favorableNextEvent25,favorableNextEvent26,favorableNextEvent27,favorableNextEvent28,favorableNextEvent29,favorableNextEvent30,favorableNextEvent31,favorableNextEvent32,favorableNextEvent33,favorableNextEvent34,favorableNextEvent35,favorableNextEvent36,taskReward]
    <;> norm_num
  have hp : rawVisits favorableNextS37Before [] = 36 := by decide
  have hn : rawVisits favorableNextS37Before ([]++[.query 2]) = 4 := by decide
  have hz : (controlPenalty savedCref uniformQuoteError unitRoleUnused .next) favorableNextS37Before [] (.query 2) = (nextNormalPenalty favorableNextS37Before) := by
    simpa only [favorableNextS37Before,nextNormalPenalty] using AgentUCTNextExact.favorable_next_normal_root_quotes_exact 36 (by omega) 2 (by decide)
  unfold indexScore
  rw [hs,hp,hn,hz]
  simp only [BackupStat.mean]
  norm_num

theorem favorableNextS37D0I3 : indexScore (7/5) (controlPenalty savedCref uniformQuoteError unitRoleUnused .next) favorableNextS37Before [] (.query 3) = treeIndex ((0/1)/4) (7/5) (nextNormalPenalty favorableNextS37Before) 36 4 := by
  have hs : replayBackup favorableNextS37Before emptyStatistics ([]++[.query 3]) = ⟨4,(0/1)⟩ := by
    rw [replayBackup_empty_closed_form]
    simp +decide [backedEvents,favorableNextS37Before,favorableNextProposal,favorableNextEvent1,favorableNextEvent2,favorableNextEvent3,favorableNextEvent4,favorableNextEvent5,favorableNextEvent6,favorableNextEvent7,favorableNextEvent8,favorableNextEvent9,favorableNextEvent10,favorableNextEvent11,favorableNextEvent12,favorableNextEvent13,favorableNextEvent14,favorableNextEvent15,favorableNextEvent16,favorableNextEvent17,favorableNextEvent18,favorableNextEvent19,favorableNextEvent20,favorableNextEvent21,favorableNextEvent22,favorableNextEvent23,favorableNextEvent24,favorableNextEvent25,favorableNextEvent26,favorableNextEvent27,favorableNextEvent28,favorableNextEvent29,favorableNextEvent30,favorableNextEvent31,favorableNextEvent32,favorableNextEvent33,favorableNextEvent34,favorableNextEvent35,favorableNextEvent36,taskReward]
    <;> norm_num
  have hp : rawVisits favorableNextS37Before [] = 36 := by decide
  have hn : rawVisits favorableNextS37Before ([]++[.query 3]) = 4 := by decide
  have hz : (controlPenalty savedCref uniformQuoteError unitRoleUnused .next) favorableNextS37Before [] (.query 3) = (nextNormalPenalty favorableNextS37Before) := by
    simpa only [favorableNextS37Before,nextNormalPenalty] using AgentUCTNextExact.favorable_next_normal_root_quotes_exact 36 (by omega) 3 (by decide)
  unfold indexScore
  rw [hs,hp,hn,hz]
  simp only [BackupStat.mean]
  norm_num

theorem favorableNextS37D0I4 : indexScore (7/5) (controlPenalty savedCref uniformQuoteError unitRoleUnused .next) favorableNextS37Before [] (.query 4) = treeIndex ((0/1)/4) (7/5) (nextNormalPenalty favorableNextS37Before) 36 4 := by
  have hs : replayBackup favorableNextS37Before emptyStatistics ([]++[.query 4]) = ⟨4,(0/1)⟩ := by
    rw [replayBackup_empty_closed_form]
    simp +decide [backedEvents,favorableNextS37Before,favorableNextProposal,favorableNextEvent1,favorableNextEvent2,favorableNextEvent3,favorableNextEvent4,favorableNextEvent5,favorableNextEvent6,favorableNextEvent7,favorableNextEvent8,favorableNextEvent9,favorableNextEvent10,favorableNextEvent11,favorableNextEvent12,favorableNextEvent13,favorableNextEvent14,favorableNextEvent15,favorableNextEvent16,favorableNextEvent17,favorableNextEvent18,favorableNextEvent19,favorableNextEvent20,favorableNextEvent21,favorableNextEvent22,favorableNextEvent23,favorableNextEvent24,favorableNextEvent25,favorableNextEvent26,favorableNextEvent27,favorableNextEvent28,favorableNextEvent29,favorableNextEvent30,favorableNextEvent31,favorableNextEvent32,favorableNextEvent33,favorableNextEvent34,favorableNextEvent35,favorableNextEvent36,taskReward]
    <;> norm_num
  have hp : rawVisits favorableNextS37Before [] = 36 := by decide
  have hn : rawVisits favorableNextS37Before ([]++[.query 4]) = 4 := by decide
  have hz : (controlPenalty savedCref uniformQuoteError unitRoleUnused .next) favorableNextS37Before [] (.query 4) = (nextNormalPenalty favorableNextS37Before) := by
    simpa only [favorableNextS37Before,nextNormalPenalty] using AgentUCTNextExact.favorable_next_normal_root_quotes_exact 36 (by omega) 4 (by decide)
  unfold indexScore
  rw [hs,hp,hn,hz]
  simp only [BackupStat.mean]
  norm_num

theorem favorableNextS37D0I5 : indexScore (7/5) (controlPenalty savedCref uniformQuoteError unitRoleUnused .next) favorableNextS37Before [] (.query 5) = treeIndex ((6/5)/5) (7/5) (nextNormalPenalty favorableNextS37Before) 36 5 := by
  have hs : replayBackup favorableNextS37Before emptyStatistics ([]++[.query 5]) = ⟨5,(6/5)⟩ := by
    rw [replayBackup_empty_closed_form]
    simp +decide [backedEvents,favorableNextS37Before,favorableNextProposal,favorableNextEvent1,favorableNextEvent2,favorableNextEvent3,favorableNextEvent4,favorableNextEvent5,favorableNextEvent6,favorableNextEvent7,favorableNextEvent8,favorableNextEvent9,favorableNextEvent10,favorableNextEvent11,favorableNextEvent12,favorableNextEvent13,favorableNextEvent14,favorableNextEvent15,favorableNextEvent16,favorableNextEvent17,favorableNextEvent18,favorableNextEvent19,favorableNextEvent20,favorableNextEvent21,favorableNextEvent22,favorableNextEvent23,favorableNextEvent24,favorableNextEvent25,favorableNextEvent26,favorableNextEvent27,favorableNextEvent28,favorableNextEvent29,favorableNextEvent30,favorableNextEvent31,favorableNextEvent32,favorableNextEvent33,favorableNextEvent34,favorableNextEvent35,favorableNextEvent36,taskReward]
    <;> norm_num
  have hp : rawVisits favorableNextS37Before [] = 36 := by decide
  have hn : rawVisits favorableNextS37Before ([]++[.query 5]) = 5 := by decide
  have hz : (controlPenalty savedCref uniformQuoteError unitRoleUnused .next) favorableNextS37Before [] (.query 5) = (nextNormalPenalty favorableNextS37Before) := by
    simpa only [favorableNextS37Before,nextNormalPenalty] using AgentUCTNextExact.favorable_next_normal_root_quotes_exact 36 (by omega) 5 (by decide)
  unfold indexScore
  rw [hs,hp,hn,hz]
  simp only [BackupStat.mean]
  norm_num

theorem favorableNextS37D0I6 : indexScore (7/5) (controlPenalty savedCref uniformQuoteError unitRoleUnused .next) favorableNextS37Before [] (.query 6) = treeIndex ((0/1)/4) (7/5) (nextNormalPenalty favorableNextS37Before) 36 4 := by
  have hs : replayBackup favorableNextS37Before emptyStatistics ([]++[.query 6]) = ⟨4,(0/1)⟩ := by
    rw [replayBackup_empty_closed_form]
    simp +decide [backedEvents,favorableNextS37Before,favorableNextProposal,favorableNextEvent1,favorableNextEvent2,favorableNextEvent3,favorableNextEvent4,favorableNextEvent5,favorableNextEvent6,favorableNextEvent7,favorableNextEvent8,favorableNextEvent9,favorableNextEvent10,favorableNextEvent11,favorableNextEvent12,favorableNextEvent13,favorableNextEvent14,favorableNextEvent15,favorableNextEvent16,favorableNextEvent17,favorableNextEvent18,favorableNextEvent19,favorableNextEvent20,favorableNextEvent21,favorableNextEvent22,favorableNextEvent23,favorableNextEvent24,favorableNextEvent25,favorableNextEvent26,favorableNextEvent27,favorableNextEvent28,favorableNextEvent29,favorableNextEvent30,favorableNextEvent31,favorableNextEvent32,favorableNextEvent33,favorableNextEvent34,favorableNextEvent35,favorableNextEvent36,taskReward]
    <;> norm_num
  have hp : rawVisits favorableNextS37Before [] = 36 := by decide
  have hn : rawVisits favorableNextS37Before ([]++[.query 6]) = 4 := by decide
  have hz : (controlPenalty savedCref uniformQuoteError unitRoleUnused .next) favorableNextS37Before [] (.query 6) = (nextNormalPenalty favorableNextS37Before) := by
    simpa only [favorableNextS37Before,nextNormalPenalty] using AgentUCTNextExact.favorable_next_normal_root_quotes_exact 36 (by omega) 6 (by decide)
  unfold indexScore
  rw [hs,hp,hn,hz]
  simp only [BackupStat.mean]
  norm_num

theorem favorableNextS37D0I7 : indexScore (7/5) (controlPenalty savedCref uniformQuoteError unitRoleUnused .next) favorableNextS37Before [] (.query 7) = treeIndex ((0/1)/4) (7/5) (nextNormalPenalty favorableNextS37Before) 36 4 := by
  have hs : replayBackup favorableNextS37Before emptyStatistics ([]++[.query 7]) = ⟨4,(0/1)⟩ := by
    rw [replayBackup_empty_closed_form]
    simp +decide [backedEvents,favorableNextS37Before,favorableNextProposal,favorableNextEvent1,favorableNextEvent2,favorableNextEvent3,favorableNextEvent4,favorableNextEvent5,favorableNextEvent6,favorableNextEvent7,favorableNextEvent8,favorableNextEvent9,favorableNextEvent10,favorableNextEvent11,favorableNextEvent12,favorableNextEvent13,favorableNextEvent14,favorableNextEvent15,favorableNextEvent16,favorableNextEvent17,favorableNextEvent18,favorableNextEvent19,favorableNextEvent20,favorableNextEvent21,favorableNextEvent22,favorableNextEvent23,favorableNextEvent24,favorableNextEvent25,favorableNextEvent26,favorableNextEvent27,favorableNextEvent28,favorableNextEvent29,favorableNextEvent30,favorableNextEvent31,favorableNextEvent32,favorableNextEvent33,favorableNextEvent34,favorableNextEvent35,favorableNextEvent36,taskReward]
    <;> norm_num
  have hp : rawVisits favorableNextS37Before [] = 36 := by decide
  have hn : rawVisits favorableNextS37Before ([]++[.query 7]) = 4 := by decide
  have hz : (controlPenalty savedCref uniformQuoteError unitRoleUnused .next) favorableNextS37Before [] (.query 7) = (nextNormalPenalty favorableNextS37Before) := by
    simpa only [favorableNextS37Before,nextNormalPenalty] using AgentUCTNextExact.favorable_next_normal_root_quotes_exact 36 (by omega) 7 (by decide)
  unfold indexScore
  rw [hs,hp,hn,hz]
  simp only [BackupStat.mean]
  norm_num

theorem favorableNextS37D0Cmp0 : indexScore (7/5) (controlPenalty savedCref uniformQuoteError unitRoleUnused .next) favorableNextS37Before [] (.query 0) < indexScore (7/5) (controlPenalty savedCref uniformQuoteError unitRoleUnused .next) favorableNextS37Before [] (.query 5) := by
  rw [favorableNextS37D0I0,favorableNextS37D0I5]
  have hk := favorable_next_penalty_interval 36 (by omega)
  change nextNormalPenaltyLower ≤ nextNormalPenalty favorableNextS37Before ∧ nextNormalPenalty favorableNextS37Before ≤ nextNormalPenaltyUpper at hk
  have hm : ((0/1)/4)+(8313557/6250000)-(nextNormalPenalty favorableNextS37Before) < ((6/5)/5)+(29743483/25000000)-(nextNormalPenalty favorableNextS37Before) := by
    have h : (((0/1)/4)+(8313557/6250000) : ℝ) < ((6/5)/5)+(29743483/25000000) := by norm_num
    linarith
  have h := index_strict_order_from_intervals ((6/5)/5) ((0/1)/4) (nextNormalPenalty favorableNextS37Before) (nextNormalPenalty favorableNextS37Before) (29743483/25000000) (8313557/6250000)
    (treeBonus (7/5) 36 5) (treeBonus (7/5) 36 4)
    (trajectory_bonus_36_5).1 (trajectory_bonus_36_4).2 hm
  simpa only [treeIndex] using h

theorem favorableNextS37D0Cmp1 : indexScore (7/5) (controlPenalty savedCref uniformQuoteError unitRoleUnused .next) favorableNextS37Before [] (.query 1) < indexScore (7/5) (controlPenalty savedCref uniformQuoteError unitRoleUnused .next) favorableNextS37Before [] (.query 5) := by
  rw [favorableNextS37D0I1,favorableNextS37D0I5]
  have hk := favorable_next_penalty_interval 36 (by omega)
  change nextNormalPenaltyLower ≤ nextNormalPenalty favorableNextS37Before ∧ nextNormalPenalty favorableNextS37Before ≤ nextNormalPenaltyUpper at hk
  have hm : ((1/1)/7)+(50275673/50000000)-0 < ((6/5)/5)+(29743483/25000000)-(nextNormalPenalty favorableNextS37Before) := by
    have h : ((1/1)/7)+(50275673/50000000) < ((6/5)/5)+(29743483/25000000)-nextNormalPenaltyUpper := by norm_num [nextNormalPenaltyUpper,savedCref,uniformQuoteError]
    linarith [hk.2]
  have h := index_strict_order_from_intervals ((6/5)/5) ((1/1)/7) (nextNormalPenalty favorableNextS37Before) 0 (29743483/25000000) (50275673/50000000)
    (treeBonus (7/5) 36 5) (treeBonus (7/5) 36 7)
    (trajectory_bonus_36_5).1 (trajectory_bonus_36_7).2 hm
  simpa only [treeIndex] using h

theorem favorableNextS37D0Cmp2 : indexScore (7/5) (controlPenalty savedCref uniformQuoteError unitRoleUnused .next) favorableNextS37Before [] (.query 2) < indexScore (7/5) (controlPenalty savedCref uniformQuoteError unitRoleUnused .next) favorableNextS37Before [] (.query 5) := by
  rw [favorableNextS37D0I2,favorableNextS37D0I5]
  have hk := favorable_next_penalty_interval 36 (by omega)
  change nextNormalPenaltyLower ≤ nextNormalPenalty favorableNextS37Before ∧ nextNormalPenalty favorableNextS37Before ≤ nextNormalPenaltyUpper at hk
  have hm : ((0/1)/4)+(8313557/6250000)-(nextNormalPenalty favorableNextS37Before) < ((6/5)/5)+(29743483/25000000)-(nextNormalPenalty favorableNextS37Before) := by
    have h : (((0/1)/4)+(8313557/6250000) : ℝ) < ((6/5)/5)+(29743483/25000000) := by norm_num
    linarith
  have h := index_strict_order_from_intervals ((6/5)/5) ((0/1)/4) (nextNormalPenalty favorableNextS37Before) (nextNormalPenalty favorableNextS37Before) (29743483/25000000) (8313557/6250000)
    (treeBonus (7/5) 36 5) (treeBonus (7/5) 36 4)
    (trajectory_bonus_36_5).1 (trajectory_bonus_36_4).2 hm
  simpa only [treeIndex] using h

theorem favorableNextS37D0Cmp3 : indexScore (7/5) (controlPenalty savedCref uniformQuoteError unitRoleUnused .next) favorableNextS37Before [] (.query 3) < indexScore (7/5) (controlPenalty savedCref uniformQuoteError unitRoleUnused .next) favorableNextS37Before [] (.query 5) := by
  rw [favorableNextS37D0I3,favorableNextS37D0I5]
  have hk := favorable_next_penalty_interval 36 (by omega)
  change nextNormalPenaltyLower ≤ nextNormalPenalty favorableNextS37Before ∧ nextNormalPenalty favorableNextS37Before ≤ nextNormalPenaltyUpper at hk
  have hm : ((0/1)/4)+(8313557/6250000)-(nextNormalPenalty favorableNextS37Before) < ((6/5)/5)+(29743483/25000000)-(nextNormalPenalty favorableNextS37Before) := by
    have h : (((0/1)/4)+(8313557/6250000) : ℝ) < ((6/5)/5)+(29743483/25000000) := by norm_num
    linarith
  have h := index_strict_order_from_intervals ((6/5)/5) ((0/1)/4) (nextNormalPenalty favorableNextS37Before) (nextNormalPenalty favorableNextS37Before) (29743483/25000000) (8313557/6250000)
    (treeBonus (7/5) 36 5) (treeBonus (7/5) 36 4)
    (trajectory_bonus_36_5).1 (trajectory_bonus_36_4).2 hm
  simpa only [treeIndex] using h

theorem favorableNextS37D0Cmp4 : indexScore (7/5) (controlPenalty savedCref uniformQuoteError unitRoleUnused .next) favorableNextS37Before [] (.query 4) < indexScore (7/5) (controlPenalty savedCref uniformQuoteError unitRoleUnused .next) favorableNextS37Before [] (.query 5) := by
  rw [favorableNextS37D0I4,favorableNextS37D0I5]
  have hk := favorable_next_penalty_interval 36 (by omega)
  change nextNormalPenaltyLower ≤ nextNormalPenalty favorableNextS37Before ∧ nextNormalPenalty favorableNextS37Before ≤ nextNormalPenaltyUpper at hk
  have hm : ((0/1)/4)+(8313557/6250000)-(nextNormalPenalty favorableNextS37Before) < ((6/5)/5)+(29743483/25000000)-(nextNormalPenalty favorableNextS37Before) := by
    have h : (((0/1)/4)+(8313557/6250000) : ℝ) < ((6/5)/5)+(29743483/25000000) := by norm_num
    linarith
  have h := index_strict_order_from_intervals ((6/5)/5) ((0/1)/4) (nextNormalPenalty favorableNextS37Before) (nextNormalPenalty favorableNextS37Before) (29743483/25000000) (8313557/6250000)
    (treeBonus (7/5) 36 5) (treeBonus (7/5) 36 4)
    (trajectory_bonus_36_5).1 (trajectory_bonus_36_4).2 hm
  simpa only [treeIndex] using h

theorem favorableNextS37D0Cmp6 : indexScore (7/5) (controlPenalty savedCref uniformQuoteError unitRoleUnused .next) favorableNextS37Before [] (.query 6) ≤ indexScore (7/5) (controlPenalty savedCref uniformQuoteError unitRoleUnused .next) favorableNextS37Before [] (.query 5) := by
  rw [favorableNextS37D0I6,favorableNextS37D0I5]
  have hk := favorable_next_penalty_interval 36 (by omega)
  change nextNormalPenaltyLower ≤ nextNormalPenalty favorableNextS37Before ∧ nextNormalPenalty favorableNextS37Before ≤ nextNormalPenaltyUpper at hk
  have hm : ((0/1)/4)+(8313557/6250000)-(nextNormalPenalty favorableNextS37Before) < ((6/5)/5)+(29743483/25000000)-(nextNormalPenalty favorableNextS37Before) := by
    have h : (((0/1)/4)+(8313557/6250000) : ℝ) < ((6/5)/5)+(29743483/25000000) := by norm_num
    linarith
  have h := index_weak_order_from_intervals ((6/5)/5) ((0/1)/4) (nextNormalPenalty favorableNextS37Before) (nextNormalPenalty favorableNextS37Before) (29743483/25000000) (8313557/6250000)
    (treeBonus (7/5) 36 5) (treeBonus (7/5) 36 4)
    (trajectory_bonus_36_5).1 (trajectory_bonus_36_4).2 hm.le
  simpa only [treeIndex] using h

theorem favorableNextS37D0Cmp7 : indexScore (7/5) (controlPenalty savedCref uniformQuoteError unitRoleUnused .next) favorableNextS37Before [] (.query 7) ≤ indexScore (7/5) (controlPenalty savedCref uniformQuoteError unitRoleUnused .next) favorableNextS37Before [] (.query 5) := by
  rw [favorableNextS37D0I7,favorableNextS37D0I5]
  have hk := favorable_next_penalty_interval 36 (by omega)
  change nextNormalPenaltyLower ≤ nextNormalPenalty favorableNextS37Before ∧ nextNormalPenalty favorableNextS37Before ≤ nextNormalPenaltyUpper at hk
  have hm : ((0/1)/4)+(8313557/6250000)-(nextNormalPenalty favorableNextS37Before) < ((6/5)/5)+(29743483/25000000)-(nextNormalPenalty favorableNextS37Before) := by
    have h : (((0/1)/4)+(8313557/6250000) : ℝ) < ((6/5)/5)+(29743483/25000000) := by norm_num
    linarith
  have h := index_weak_order_from_intervals ((6/5)/5) ((0/1)/4) (nextNormalPenalty favorableNextS37Before) (nextNormalPenalty favorableNextS37Before) (29743483/25000000) (8313557/6250000)
    (treeBonus (7/5) 36 5) (treeBonus (7/5) 36 4)
    (trajectory_bonus_36_5).1 (trajectory_bonus_36_4).2 hm.le
  simpa only [treeIndex] using h

theorem favorableNextS37Choice0 : nativeFirstChoice (indexScore (7/5) (controlPenalty savedCref uniformQuoteError unitRoleUnused .next) favorableNextS37Before []) favorableNextS37Before [] = .query 5 := by
  apply visited_choice_from_ordered_certificate _ _ [] [.query 0,.query 1,.query 2,.query 3,.query 4] [.query 6,.query 7] (.query 5) (by decide)
  · intro a ha
    have ho : orderedLegalAvailable [] = [.query 0,.query 1,.query 2,.query 3,.query 4,.query 5,.query 6,.query 7] := by decide
    rw [ho] at ha
    simp only [List.mem_cons,List.not_mem_nil,or_false] at ha
    rcases ha with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> decide
  · intro a ha
    simp only [List.mem_cons,List.not_mem_nil,or_false] at ha
    rcases ha with rfl | rfl | rfl | rfl | rfl
    · exact favorableNextS37D0Cmp0
    · exact favorableNextS37D0Cmp1
    · exact favorableNextS37D0Cmp2
    · exact favorableNextS37D0Cmp3
    · exact favorableNextS37D0Cmp4
  · intro a ha
    simp only [List.mem_cons,List.not_mem_nil,or_false] at ha
    rcases ha with rfl | rfl
    · exact favorableNextS37D0Cmp6
    · exact favorableNextS37D0Cmp7

theorem favorableNextS37ActualEvent : nativeEvent budgetTape (7/5) (controlPenalty savedCref uniformQuoteError unitRoleUnused .next)
    (taskReward false (2/5) (1/2)) favorableNextS37Before = favorableNextEvent37 := by
  have hs0 := native_select_existing_step budgetTape (7/5) (controlPenalty savedCref uniformQuoteError unitRoleUnused .next) favorableNextS37Before 8 [] (.query 5)
    (by decide) (by decide) favorableNextS37Choice0
  have hnew := native_select_new_step budgetTape (7/5) (controlPenalty savedCref uniformQuoteError unitRoleUnused .next) favorableNextS37Before 7 [.query 5]
    [.normalRetriever 7,.normalRetriever 8,.normalRetriever 5,.normalRetriever 2,.normalRetriever 3,.normalRetriever 12,.normalRetriever 14,.normalRetriever 13,.normalRetriever 21,.normalRetriever 23,.normalRetriever 22,.normalRetriever 9,.normalRetriever 11,.normalRetriever 10,.normalRetriever 15,.normalRetriever 17,.normalRetriever 16,.normalRetriever 18,.normalRetriever 20,.normalRetriever 19,.normalRetriever 24,.normalRetriever 25,.normalRetriever 26,.normalRetriever 27,.normalRetriever 28,.normalRetriever 29] (.normalRetriever 7) (by decide) (by decide) (by decide) (by decide)
  have hs : nativeSelect budgetTape (7/5) (controlPenalty savedCref uniformQuoteError unitRoleUnused .next) favorableNextS37Before 9 [] = [.query 5,.normalRetriever 7] := by
    rw [hs0]
    change nativeSelect budgetTape (7/5) (controlPenalty savedCref uniformQuoteError unitRoleUnused .next) favorableNextS37Before 8 [.query 5] = _
    rw [hnew] <;> rfl
  have hr : repairedRollout budgetTape favorableNextS37Before 9 [.query 5,.normalRetriever 7] = [.query 5,.normalRetriever 7,.selection 0,.width 0,.stop,.reranker 0,.topm 0,.context 0,.answer 0] := by decide
  simp only [nativeEvent,hs,hr]
  rfl

end AgentUCT32MConcrete
