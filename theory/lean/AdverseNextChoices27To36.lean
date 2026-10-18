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

def adverseNextS27Before := adverseNextProposal.take 26

theorem adverseNextS27D0I0 : indexScore (7/5) (controlPenalty savedCref uniformQuoteError unitRoleUnused .next) adverseNextS27Before [] (.query 0) = treeIndex ((0/1)/3) (7/5) (nextNormalPenalty adverseNextS27Before) 26 3 := by
  have hs : replayBackup adverseNextS27Before emptyStatistics ([]++[.query 0]) = ⟨3,(0/1)⟩ := by
    rw [replayBackup_empty_closed_form]
    simp +decide [backedEvents,adverseNextS27Before,adverseNextProposal,adverseNextEvent1,adverseNextEvent2,adverseNextEvent3,adverseNextEvent4,adverseNextEvent5,adverseNextEvent6,adverseNextEvent7,adverseNextEvent8,adverseNextEvent9,adverseNextEvent10,adverseNextEvent11,adverseNextEvent12,adverseNextEvent13,adverseNextEvent14,adverseNextEvent15,adverseNextEvent16,adverseNextEvent17,adverseNextEvent18,adverseNextEvent19,adverseNextEvent20,adverseNextEvent21,adverseNextEvent22,adverseNextEvent23,adverseNextEvent24,adverseNextEvent25,adverseNextEvent26,taskReward]
    <;> norm_num
  have hp : rawVisits adverseNextS27Before [] = 26 := by decide
  have hn : rawVisits adverseNextS27Before ([]++[.query 0]) = 3 := by decide
  have hz : (controlPenalty savedCref uniformQuoteError unitRoleUnused .next) adverseNextS27Before [] (.query 0) = (nextNormalPenalty adverseNextS27Before) := by
    simpa only [adverseNextS27Before,nextNormalPenalty] using AgentUCTNextExact.adverse_next_normal_root_quotes_exact 26 (by omega) 0 (by decide)
  unfold indexScore
  rw [hs,hp,hn,hz]
  simp only [BackupStat.mean]
  norm_num

theorem adverseNextS27D0I1 : indexScore (7/5) (controlPenalty savedCref uniformQuoteError unitRoleUnused .next) adverseNextS27Before [] (.query 1) = treeIndex ((0/1)/4) (7/5) 0 26 4 := by
  have hs : replayBackup adverseNextS27Before emptyStatistics ([]++[.query 1]) = ⟨4,(0/1)⟩ := by
    rw [replayBackup_empty_closed_form]
    simp +decide [backedEvents,adverseNextS27Before,adverseNextProposal,adverseNextEvent1,adverseNextEvent2,adverseNextEvent3,adverseNextEvent4,adverseNextEvent5,adverseNextEvent6,adverseNextEvent7,adverseNextEvent8,adverseNextEvent9,adverseNextEvent10,adverseNextEvent11,adverseNextEvent12,adverseNextEvent13,adverseNextEvent14,adverseNextEvent15,adverseNextEvent16,adverseNextEvent17,adverseNextEvent18,adverseNextEvent19,adverseNextEvent20,adverseNextEvent21,adverseNextEvent22,adverseNextEvent23,adverseNextEvent24,adverseNextEvent25,adverseNextEvent26,taskReward]
    <;> norm_num
  have hp : rawVisits adverseNextS27Before [] = 26 := by decide
  have hn : rawVisits adverseNextS27Before ([]++[.query 1]) = 4 := by decide
  have hz : (controlPenalty savedCref uniformQuoteError unitRoleUnused .next) adverseNextS27Before [] (.query 1) = 0 := by
    apply control_penalty_empty_suffix
    exact AgentUCTNextExact.adverse_next_hyde_root_suffix_empty 26 (by omega)
  unfold indexScore
  rw [hs,hp,hn,hz]
  simp only [BackupStat.mean]
  norm_num

theorem adverseNextS27D0I2 : indexScore (7/5) (controlPenalty savedCref uniformQuoteError unitRoleUnused .next) adverseNextS27Before [] (.query 2) = treeIndex ((0/1)/3) (7/5) (nextNormalPenalty adverseNextS27Before) 26 3 := by
  have hs : replayBackup adverseNextS27Before emptyStatistics ([]++[.query 2]) = ⟨3,(0/1)⟩ := by
    rw [replayBackup_empty_closed_form]
    simp +decide [backedEvents,adverseNextS27Before,adverseNextProposal,adverseNextEvent1,adverseNextEvent2,adverseNextEvent3,adverseNextEvent4,adverseNextEvent5,adverseNextEvent6,adverseNextEvent7,adverseNextEvent8,adverseNextEvent9,adverseNextEvent10,adverseNextEvent11,adverseNextEvent12,adverseNextEvent13,adverseNextEvent14,adverseNextEvent15,adverseNextEvent16,adverseNextEvent17,adverseNextEvent18,adverseNextEvent19,adverseNextEvent20,adverseNextEvent21,adverseNextEvent22,adverseNextEvent23,adverseNextEvent24,adverseNextEvent25,adverseNextEvent26,taskReward]
    <;> norm_num
  have hp : rawVisits adverseNextS27Before [] = 26 := by decide
  have hn : rawVisits adverseNextS27Before ([]++[.query 2]) = 3 := by decide
  have hz : (controlPenalty savedCref uniformQuoteError unitRoleUnused .next) adverseNextS27Before [] (.query 2) = (nextNormalPenalty adverseNextS27Before) := by
    simpa only [adverseNextS27Before,nextNormalPenalty] using AgentUCTNextExact.adverse_next_normal_root_quotes_exact 26 (by omega) 2 (by decide)
  unfold indexScore
  rw [hs,hp,hn,hz]
  simp only [BackupStat.mean]
  norm_num

theorem adverseNextS27D0I3 : indexScore (7/5) (controlPenalty savedCref uniformQuoteError unitRoleUnused .next) adverseNextS27Before [] (.query 3) = treeIndex ((0/1)/3) (7/5) (nextNormalPenalty adverseNextS27Before) 26 3 := by
  have hs : replayBackup adverseNextS27Before emptyStatistics ([]++[.query 3]) = ⟨3,(0/1)⟩ := by
    rw [replayBackup_empty_closed_form]
    simp +decide [backedEvents,adverseNextS27Before,adverseNextProposal,adverseNextEvent1,adverseNextEvent2,adverseNextEvent3,adverseNextEvent4,adverseNextEvent5,adverseNextEvent6,adverseNextEvent7,adverseNextEvent8,adverseNextEvent9,adverseNextEvent10,adverseNextEvent11,adverseNextEvent12,adverseNextEvent13,adverseNextEvent14,adverseNextEvent15,adverseNextEvent16,adverseNextEvent17,adverseNextEvent18,adverseNextEvent19,adverseNextEvent20,adverseNextEvent21,adverseNextEvent22,adverseNextEvent23,adverseNextEvent24,adverseNextEvent25,adverseNextEvent26,taskReward]
    <;> norm_num
  have hp : rawVisits adverseNextS27Before [] = 26 := by decide
  have hn : rawVisits adverseNextS27Before ([]++[.query 3]) = 3 := by decide
  have hz : (controlPenalty savedCref uniformQuoteError unitRoleUnused .next) adverseNextS27Before [] (.query 3) = (nextNormalPenalty adverseNextS27Before) := by
    simpa only [adverseNextS27Before,nextNormalPenalty] using AgentUCTNextExact.adverse_next_normal_root_quotes_exact 26 (by omega) 3 (by decide)
  unfold indexScore
  rw [hs,hp,hn,hz]
  simp only [BackupStat.mean]
  norm_num

theorem adverseNextS27D0I4 : indexScore (7/5) (controlPenalty savedCref uniformQuoteError unitRoleUnused .next) adverseNextS27Before [] (.query 4) = treeIndex ((0/1)/3) (7/5) (nextNormalPenalty adverseNextS27Before) 26 3 := by
  have hs : replayBackup adverseNextS27Before emptyStatistics ([]++[.query 4]) = ⟨3,(0/1)⟩ := by
    rw [replayBackup_empty_closed_form]
    simp +decide [backedEvents,adverseNextS27Before,adverseNextProposal,adverseNextEvent1,adverseNextEvent2,adverseNextEvent3,adverseNextEvent4,adverseNextEvent5,adverseNextEvent6,adverseNextEvent7,adverseNextEvent8,adverseNextEvent9,adverseNextEvent10,adverseNextEvent11,adverseNextEvent12,adverseNextEvent13,adverseNextEvent14,adverseNextEvent15,adverseNextEvent16,adverseNextEvent17,adverseNextEvent18,adverseNextEvent19,adverseNextEvent20,adverseNextEvent21,adverseNextEvent22,adverseNextEvent23,adverseNextEvent24,adverseNextEvent25,adverseNextEvent26,taskReward]
    <;> norm_num
  have hp : rawVisits adverseNextS27Before [] = 26 := by decide
  have hn : rawVisits adverseNextS27Before ([]++[.query 4]) = 3 := by decide
  have hz : (controlPenalty savedCref uniformQuoteError unitRoleUnused .next) adverseNextS27Before [] (.query 4) = (nextNormalPenalty adverseNextS27Before) := by
    simpa only [adverseNextS27Before,nextNormalPenalty] using AgentUCTNextExact.adverse_next_normal_root_quotes_exact 26 (by omega) 4 (by decide)
  unfold indexScore
  rw [hs,hp,hn,hz]
  simp only [BackupStat.mean]
  norm_num

theorem adverseNextS27D0I5 : indexScore (7/5) (controlPenalty savedCref uniformQuoteError unitRoleUnused .next) adverseNextS27Before [] (.query 5) = treeIndex ((13/10)/4) (7/5) (nextNormalPenalty adverseNextS27Before) 26 4 := by
  have hs : replayBackup adverseNextS27Before emptyStatistics ([]++[.query 5]) = ⟨4,(13/10)⟩ := by
    rw [replayBackup_empty_closed_form]
    simp +decide [backedEvents,adverseNextS27Before,adverseNextProposal,adverseNextEvent1,adverseNextEvent2,adverseNextEvent3,adverseNextEvent4,adverseNextEvent5,adverseNextEvent6,adverseNextEvent7,adverseNextEvent8,adverseNextEvent9,adverseNextEvent10,adverseNextEvent11,adverseNextEvent12,adverseNextEvent13,adverseNextEvent14,adverseNextEvent15,adverseNextEvent16,adverseNextEvent17,adverseNextEvent18,adverseNextEvent19,adverseNextEvent20,adverseNextEvent21,adverseNextEvent22,adverseNextEvent23,adverseNextEvent24,adverseNextEvent25,adverseNextEvent26,taskReward]
    <;> norm_num
  have hp : rawVisits adverseNextS27Before [] = 26 := by decide
  have hn : rawVisits adverseNextS27Before ([]++[.query 5]) = 4 := by decide
  have hz : (controlPenalty savedCref uniformQuoteError unitRoleUnused .next) adverseNextS27Before [] (.query 5) = (nextNormalPenalty adverseNextS27Before) := by
    simpa only [adverseNextS27Before,nextNormalPenalty] using AgentUCTNextExact.adverse_next_normal_root_quotes_exact 26 (by omega) 5 (by decide)
  unfold indexScore
  rw [hs,hp,hn,hz]
  simp only [BackupStat.mean]
  norm_num

theorem adverseNextS27D0I6 : indexScore (7/5) (controlPenalty savedCref uniformQuoteError unitRoleUnused .next) adverseNextS27Before [] (.query 6) = treeIndex ((0/1)/3) (7/5) (nextNormalPenalty adverseNextS27Before) 26 3 := by
  have hs : replayBackup adverseNextS27Before emptyStatistics ([]++[.query 6]) = ⟨3,(0/1)⟩ := by
    rw [replayBackup_empty_closed_form]
    simp +decide [backedEvents,adverseNextS27Before,adverseNextProposal,adverseNextEvent1,adverseNextEvent2,adverseNextEvent3,adverseNextEvent4,adverseNextEvent5,adverseNextEvent6,adverseNextEvent7,adverseNextEvent8,adverseNextEvent9,adverseNextEvent10,adverseNextEvent11,adverseNextEvent12,adverseNextEvent13,adverseNextEvent14,adverseNextEvent15,adverseNextEvent16,adverseNextEvent17,adverseNextEvent18,adverseNextEvent19,adverseNextEvent20,adverseNextEvent21,adverseNextEvent22,adverseNextEvent23,adverseNextEvent24,adverseNextEvent25,adverseNextEvent26,taskReward]
    <;> norm_num
  have hp : rawVisits adverseNextS27Before [] = 26 := by decide
  have hn : rawVisits adverseNextS27Before ([]++[.query 6]) = 3 := by decide
  have hz : (controlPenalty savedCref uniformQuoteError unitRoleUnused .next) adverseNextS27Before [] (.query 6) = (nextNormalPenalty adverseNextS27Before) := by
    simpa only [adverseNextS27Before,nextNormalPenalty] using AgentUCTNextExact.adverse_next_normal_root_quotes_exact 26 (by omega) 6 (by decide)
  unfold indexScore
  rw [hs,hp,hn,hz]
  simp only [BackupStat.mean]
  norm_num

theorem adverseNextS27D0I7 : indexScore (7/5) (controlPenalty savedCref uniformQuoteError unitRoleUnused .next) adverseNextS27Before [] (.query 7) = treeIndex ((0/1)/3) (7/5) (nextNormalPenalty adverseNextS27Before) 26 3 := by
  have hs : replayBackup adverseNextS27Before emptyStatistics ([]++[.query 7]) = ⟨3,(0/1)⟩ := by
    rw [replayBackup_empty_closed_form]
    simp +decide [backedEvents,adverseNextS27Before,adverseNextProposal,adverseNextEvent1,adverseNextEvent2,adverseNextEvent3,adverseNextEvent4,adverseNextEvent5,adverseNextEvent6,adverseNextEvent7,adverseNextEvent8,adverseNextEvent9,adverseNextEvent10,adverseNextEvent11,adverseNextEvent12,adverseNextEvent13,adverseNextEvent14,adverseNextEvent15,adverseNextEvent16,adverseNextEvent17,adverseNextEvent18,adverseNextEvent19,adverseNextEvent20,adverseNextEvent21,adverseNextEvent22,adverseNextEvent23,adverseNextEvent24,adverseNextEvent25,adverseNextEvent26,taskReward]
    <;> norm_num
  have hp : rawVisits adverseNextS27Before [] = 26 := by decide
  have hn : rawVisits adverseNextS27Before ([]++[.query 7]) = 3 := by decide
  have hz : (controlPenalty savedCref uniformQuoteError unitRoleUnused .next) adverseNextS27Before [] (.query 7) = (nextNormalPenalty adverseNextS27Before) := by
    simpa only [adverseNextS27Before,nextNormalPenalty] using AgentUCTNextExact.adverse_next_normal_root_quotes_exact 26 (by omega) 7 (by decide)
  unfold indexScore
  rw [hs,hp,hn,hz]
  simp only [BackupStat.mean]
  norm_num

theorem adverseNextS27D0Cmp0 : indexScore (7/5) (controlPenalty savedCref uniformQuoteError unitRoleUnused .next) adverseNextS27Before [] (.query 0) < indexScore (7/5) (controlPenalty savedCref uniformQuoteError unitRoleUnused .next) adverseNextS27Before [] (.query 5) := by
  rw [adverseNextS27D0I0,adverseNextS27D0I5]
  have hk := adverse_next_penalty_interval 26 (by omega)
  change nextNormalPenaltyLower ≤ nextNormalPenalty adverseNextS27Before ∧ nextNormalPenalty adverseNextS27Before ≤ nextNormalPenaltyUpper at hk
  have hm : ((0/1)/3)+(73370297/50000000)-(nextNormalPenalty adverseNextS27Before) < ((13/10)/4)+(63540533/50000000)-(nextNormalPenalty adverseNextS27Before) := by
    have h : (((0/1)/3)+(73370297/50000000) : ℝ) < ((13/10)/4)+(63540533/50000000) := by norm_num
    linarith
  have h := index_strict_order_from_intervals ((13/10)/4) ((0/1)/3) (nextNormalPenalty adverseNextS27Before) (nextNormalPenalty adverseNextS27Before) (63540533/50000000) (73370297/50000000)
    (treeBonus (7/5) 26 4) (treeBonus (7/5) 26 3)
    (trajectory_bonus_26_4).1 (trajectory_bonus_26_3).2 hm
  simpa only [treeIndex] using h

theorem adverseNextS27D0Cmp1 : indexScore (7/5) (controlPenalty savedCref uniformQuoteError unitRoleUnused .next) adverseNextS27Before [] (.query 1) < indexScore (7/5) (controlPenalty savedCref uniformQuoteError unitRoleUnused .next) adverseNextS27Before [] (.query 5) := by
  rw [adverseNextS27D0I1,adverseNextS27D0I5]
  have hk := adverse_next_penalty_interval 26 (by omega)
  change nextNormalPenaltyLower ≤ nextNormalPenalty adverseNextS27Before ∧ nextNormalPenalty adverseNextS27Before ≤ nextNormalPenaltyUpper at hk
  have hm : ((0/1)/4)+(3177027/2500000)-0 < ((13/10)/4)+(63540533/50000000)-(nextNormalPenalty adverseNextS27Before) := by
    have h : ((0/1)/4)+(3177027/2500000) < ((13/10)/4)+(63540533/50000000)-nextNormalPenaltyUpper := by norm_num [nextNormalPenaltyUpper,savedCref,uniformQuoteError]
    linarith [hk.2]
  have h := index_strict_order_from_intervals ((13/10)/4) ((0/1)/4) (nextNormalPenalty adverseNextS27Before) 0 (63540533/50000000) (3177027/2500000)
    (treeBonus (7/5) 26 4) (treeBonus (7/5) 26 4)
    (trajectory_bonus_26_4).1 (trajectory_bonus_26_4).2 hm
  simpa only [treeIndex] using h

theorem adverseNextS27D0Cmp2 : indexScore (7/5) (controlPenalty savedCref uniformQuoteError unitRoleUnused .next) adverseNextS27Before [] (.query 2) < indexScore (7/5) (controlPenalty savedCref uniformQuoteError unitRoleUnused .next) adverseNextS27Before [] (.query 5) := by
  rw [adverseNextS27D0I2,adverseNextS27D0I5]
  have hk := adverse_next_penalty_interval 26 (by omega)
  change nextNormalPenaltyLower ≤ nextNormalPenalty adverseNextS27Before ∧ nextNormalPenalty adverseNextS27Before ≤ nextNormalPenaltyUpper at hk
  have hm : ((0/1)/3)+(73370297/50000000)-(nextNormalPenalty adverseNextS27Before) < ((13/10)/4)+(63540533/50000000)-(nextNormalPenalty adverseNextS27Before) := by
    have h : (((0/1)/3)+(73370297/50000000) : ℝ) < ((13/10)/4)+(63540533/50000000) := by norm_num
    linarith
  have h := index_strict_order_from_intervals ((13/10)/4) ((0/1)/3) (nextNormalPenalty adverseNextS27Before) (nextNormalPenalty adverseNextS27Before) (63540533/50000000) (73370297/50000000)
    (treeBonus (7/5) 26 4) (treeBonus (7/5) 26 3)
    (trajectory_bonus_26_4).1 (trajectory_bonus_26_3).2 hm
  simpa only [treeIndex] using h

theorem adverseNextS27D0Cmp3 : indexScore (7/5) (controlPenalty savedCref uniformQuoteError unitRoleUnused .next) adverseNextS27Before [] (.query 3) < indexScore (7/5) (controlPenalty savedCref uniformQuoteError unitRoleUnused .next) adverseNextS27Before [] (.query 5) := by
  rw [adverseNextS27D0I3,adverseNextS27D0I5]
  have hk := adverse_next_penalty_interval 26 (by omega)
  change nextNormalPenaltyLower ≤ nextNormalPenalty adverseNextS27Before ∧ nextNormalPenalty adverseNextS27Before ≤ nextNormalPenaltyUpper at hk
  have hm : ((0/1)/3)+(73370297/50000000)-(nextNormalPenalty adverseNextS27Before) < ((13/10)/4)+(63540533/50000000)-(nextNormalPenalty adverseNextS27Before) := by
    have h : (((0/1)/3)+(73370297/50000000) : ℝ) < ((13/10)/4)+(63540533/50000000) := by norm_num
    linarith
  have h := index_strict_order_from_intervals ((13/10)/4) ((0/1)/3) (nextNormalPenalty adverseNextS27Before) (nextNormalPenalty adverseNextS27Before) (63540533/50000000) (73370297/50000000)
    (treeBonus (7/5) 26 4) (treeBonus (7/5) 26 3)
    (trajectory_bonus_26_4).1 (trajectory_bonus_26_3).2 hm
  simpa only [treeIndex] using h

theorem adverseNextS27D0Cmp4 : indexScore (7/5) (controlPenalty savedCref uniformQuoteError unitRoleUnused .next) adverseNextS27Before [] (.query 4) < indexScore (7/5) (controlPenalty savedCref uniformQuoteError unitRoleUnused .next) adverseNextS27Before [] (.query 5) := by
  rw [adverseNextS27D0I4,adverseNextS27D0I5]
  have hk := adverse_next_penalty_interval 26 (by omega)
  change nextNormalPenaltyLower ≤ nextNormalPenalty adverseNextS27Before ∧ nextNormalPenalty adverseNextS27Before ≤ nextNormalPenaltyUpper at hk
  have hm : ((0/1)/3)+(73370297/50000000)-(nextNormalPenalty adverseNextS27Before) < ((13/10)/4)+(63540533/50000000)-(nextNormalPenalty adverseNextS27Before) := by
    have h : (((0/1)/3)+(73370297/50000000) : ℝ) < ((13/10)/4)+(63540533/50000000) := by norm_num
    linarith
  have h := index_strict_order_from_intervals ((13/10)/4) ((0/1)/3) (nextNormalPenalty adverseNextS27Before) (nextNormalPenalty adverseNextS27Before) (63540533/50000000) (73370297/50000000)
    (treeBonus (7/5) 26 4) (treeBonus (7/5) 26 3)
    (trajectory_bonus_26_4).1 (trajectory_bonus_26_3).2 hm
  simpa only [treeIndex] using h

theorem adverseNextS27D0Cmp6 : indexScore (7/5) (controlPenalty savedCref uniformQuoteError unitRoleUnused .next) adverseNextS27Before [] (.query 6) ≤ indexScore (7/5) (controlPenalty savedCref uniformQuoteError unitRoleUnused .next) adverseNextS27Before [] (.query 5) := by
  rw [adverseNextS27D0I6,adverseNextS27D0I5]
  have hk := adverse_next_penalty_interval 26 (by omega)
  change nextNormalPenaltyLower ≤ nextNormalPenalty adverseNextS27Before ∧ nextNormalPenalty adverseNextS27Before ≤ nextNormalPenaltyUpper at hk
  have hm : ((0/1)/3)+(73370297/50000000)-(nextNormalPenalty adverseNextS27Before) < ((13/10)/4)+(63540533/50000000)-(nextNormalPenalty adverseNextS27Before) := by
    have h : (((0/1)/3)+(73370297/50000000) : ℝ) < ((13/10)/4)+(63540533/50000000) := by norm_num
    linarith
  have h := index_weak_order_from_intervals ((13/10)/4) ((0/1)/3) (nextNormalPenalty adverseNextS27Before) (nextNormalPenalty adverseNextS27Before) (63540533/50000000) (73370297/50000000)
    (treeBonus (7/5) 26 4) (treeBonus (7/5) 26 3)
    (trajectory_bonus_26_4).1 (trajectory_bonus_26_3).2 hm.le
  simpa only [treeIndex] using h

theorem adverseNextS27D0Cmp7 : indexScore (7/5) (controlPenalty savedCref uniformQuoteError unitRoleUnused .next) adverseNextS27Before [] (.query 7) ≤ indexScore (7/5) (controlPenalty savedCref uniformQuoteError unitRoleUnused .next) adverseNextS27Before [] (.query 5) := by
  rw [adverseNextS27D0I7,adverseNextS27D0I5]
  have hk := adverse_next_penalty_interval 26 (by omega)
  change nextNormalPenaltyLower ≤ nextNormalPenalty adverseNextS27Before ∧ nextNormalPenalty adverseNextS27Before ≤ nextNormalPenaltyUpper at hk
  have hm : ((0/1)/3)+(73370297/50000000)-(nextNormalPenalty adverseNextS27Before) < ((13/10)/4)+(63540533/50000000)-(nextNormalPenalty adverseNextS27Before) := by
    have h : (((0/1)/3)+(73370297/50000000) : ℝ) < ((13/10)/4)+(63540533/50000000) := by norm_num
    linarith
  have h := index_weak_order_from_intervals ((13/10)/4) ((0/1)/3) (nextNormalPenalty adverseNextS27Before) (nextNormalPenalty adverseNextS27Before) (63540533/50000000) (73370297/50000000)
    (treeBonus (7/5) 26 4) (treeBonus (7/5) 26 3)
    (trajectory_bonus_26_4).1 (trajectory_bonus_26_3).2 hm.le
  simpa only [treeIndex] using h

theorem adverseNextS27Choice0 : nativeFirstChoice (indexScore (7/5) (controlPenalty savedCref uniformQuoteError unitRoleUnused .next) adverseNextS27Before []) adverseNextS27Before [] = .query 5 := by
  apply visited_choice_from_ordered_certificate _ _ [] [.query 0,.query 1,.query 2,.query 3,.query 4] [.query 6,.query 7] (.query 5) (by decide)
  · intro a ha
    have ho : orderedLegalAvailable [] = [.query 0,.query 1,.query 2,.query 3,.query 4,.query 5,.query 6,.query 7] := by decide
    rw [ho] at ha
    simp only [List.mem_cons,List.not_mem_nil,or_false] at ha
    rcases ha with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> decide
  · intro a ha
    simp only [List.mem_cons,List.not_mem_nil,or_false] at ha
    rcases ha with rfl | rfl | rfl | rfl | rfl
    · exact adverseNextS27D0Cmp0
    · exact adverseNextS27D0Cmp1
    · exact adverseNextS27D0Cmp2
    · exact adverseNextS27D0Cmp3
    · exact adverseNextS27D0Cmp4
  · intro a ha
    simp only [List.mem_cons,List.not_mem_nil,or_false] at ha
    rcases ha with rfl | rfl
    · exact adverseNextS27D0Cmp6
    · exact adverseNextS27D0Cmp7

theorem adverseNextS27ActualEvent : nativeEvent budgetTape (7/5) (controlPenalty savedCref uniformQuoteError unitRoleUnused .next)
    (taskReward true (2/5) (1/2)) adverseNextS27Before = adverseNextEvent27 := by
  have hs0 := native_select_existing_step budgetTape (7/5) (controlPenalty savedCref uniformQuoteError unitRoleUnused .next) adverseNextS27Before 8 [] (.query 5)
    (by decide) (by decide) adverseNextS27Choice0
  have hnew := native_select_new_step budgetTape (7/5) (controlPenalty savedCref uniformQuoteError unitRoleUnused .next) adverseNextS27Before 7 [.query 5]
    [.normalRetriever 6,.normalRetriever 7,.normalRetriever 8,.normalRetriever 5,.normalRetriever 2,.normalRetriever 3,.normalRetriever 12,.normalRetriever 14,.normalRetriever 13,.normalRetriever 21,.normalRetriever 23,.normalRetriever 22,.normalRetriever 9,.normalRetriever 11,.normalRetriever 10,.normalRetriever 15,.normalRetriever 17,.normalRetriever 16,.normalRetriever 18,.normalRetriever 20,.normalRetriever 19,.normalRetriever 24,.normalRetriever 25,.normalRetriever 26,.normalRetriever 27,.normalRetriever 28,.normalRetriever 29] (.normalRetriever 6) (by decide) (by decide) (by decide) (by decide)
  have hs : nativeSelect budgetTape (7/5) (controlPenalty savedCref uniformQuoteError unitRoleUnused .next) adverseNextS27Before 9 [] = [.query 5,.normalRetriever 6] := by
    rw [hs0]
    change nativeSelect budgetTape (7/5) (controlPenalty savedCref uniformQuoteError unitRoleUnused .next) adverseNextS27Before 8 [.query 5] = _
    rw [hnew] <;> rfl
  have hr : repairedRollout budgetTape adverseNextS27Before 9 [.query 5,.normalRetriever 6] = [.query 5,.normalRetriever 6,.selection 0,.width 0,.stop,.reranker 0,.topm 0,.context 0,.answer 0] := by decide
  simp only [nativeEvent,hs,hr]
  rfl

def adverseNextS28Before := adverseNextProposal.take 27

theorem adverseNextS28D0I0 : indexScore (7/5) (controlPenalty savedCref uniformQuoteError unitRoleUnused .next) adverseNextS28Before [] (.query 0) = treeIndex ((0/1)/3) (7/5) (nextNormalPenalty adverseNextS28Before) 27 3 := by
  have hs : replayBackup adverseNextS28Before emptyStatistics ([]++[.query 0]) = ⟨3,(0/1)⟩ := by
    rw [replayBackup_empty_closed_form]
    simp +decide [backedEvents,adverseNextS28Before,adverseNextProposal,adverseNextEvent1,adverseNextEvent2,adverseNextEvent3,adverseNextEvent4,adverseNextEvent5,adverseNextEvent6,adverseNextEvent7,adverseNextEvent8,adverseNextEvent9,adverseNextEvent10,adverseNextEvent11,adverseNextEvent12,adverseNextEvent13,adverseNextEvent14,adverseNextEvent15,adverseNextEvent16,adverseNextEvent17,adverseNextEvent18,adverseNextEvent19,adverseNextEvent20,adverseNextEvent21,adverseNextEvent22,adverseNextEvent23,adverseNextEvent24,adverseNextEvent25,adverseNextEvent26,adverseNextEvent27,taskReward]
    <;> norm_num
  have hp : rawVisits adverseNextS28Before [] = 27 := by decide
  have hn : rawVisits adverseNextS28Before ([]++[.query 0]) = 3 := by decide
  have hz : (controlPenalty savedCref uniformQuoteError unitRoleUnused .next) adverseNextS28Before [] (.query 0) = (nextNormalPenalty adverseNextS28Before) := by
    simpa only [adverseNextS28Before,nextNormalPenalty] using AgentUCTNextExact.adverse_next_normal_root_quotes_exact 27 (by omega) 0 (by decide)
  unfold indexScore
  rw [hs,hp,hn,hz]
  simp only [BackupStat.mean]
  norm_num

theorem adverseNextS28D0I1 : indexScore (7/5) (controlPenalty savedCref uniformQuoteError unitRoleUnused .next) adverseNextS28Before [] (.query 1) = treeIndex ((0/1)/4) (7/5) 0 27 4 := by
  have hs : replayBackup adverseNextS28Before emptyStatistics ([]++[.query 1]) = ⟨4,(0/1)⟩ := by
    rw [replayBackup_empty_closed_form]
    simp +decide [backedEvents,adverseNextS28Before,adverseNextProposal,adverseNextEvent1,adverseNextEvent2,adverseNextEvent3,adverseNextEvent4,adverseNextEvent5,adverseNextEvent6,adverseNextEvent7,adverseNextEvent8,adverseNextEvent9,adverseNextEvent10,adverseNextEvent11,adverseNextEvent12,adverseNextEvent13,adverseNextEvent14,adverseNextEvent15,adverseNextEvent16,adverseNextEvent17,adverseNextEvent18,adverseNextEvent19,adverseNextEvent20,adverseNextEvent21,adverseNextEvent22,adverseNextEvent23,adverseNextEvent24,adverseNextEvent25,adverseNextEvent26,adverseNextEvent27,taskReward]
    <;> norm_num
  have hp : rawVisits adverseNextS28Before [] = 27 := by decide
  have hn : rawVisits adverseNextS28Before ([]++[.query 1]) = 4 := by decide
  have hz : (controlPenalty savedCref uniformQuoteError unitRoleUnused .next) adverseNextS28Before [] (.query 1) = 0 := by
    apply control_penalty_empty_suffix
    exact AgentUCTNextExact.adverse_next_hyde_root_suffix_empty 27 (by omega)
  unfold indexScore
  rw [hs,hp,hn,hz]
  simp only [BackupStat.mean]
  norm_num

theorem adverseNextS28D0I2 : indexScore (7/5) (controlPenalty savedCref uniformQuoteError unitRoleUnused .next) adverseNextS28Before [] (.query 2) = treeIndex ((0/1)/3) (7/5) (nextNormalPenalty adverseNextS28Before) 27 3 := by
  have hs : replayBackup adverseNextS28Before emptyStatistics ([]++[.query 2]) = ⟨3,(0/1)⟩ := by
    rw [replayBackup_empty_closed_form]
    simp +decide [backedEvents,adverseNextS28Before,adverseNextProposal,adverseNextEvent1,adverseNextEvent2,adverseNextEvent3,adverseNextEvent4,adverseNextEvent5,adverseNextEvent6,adverseNextEvent7,adverseNextEvent8,adverseNextEvent9,adverseNextEvent10,adverseNextEvent11,adverseNextEvent12,adverseNextEvent13,adverseNextEvent14,adverseNextEvent15,adverseNextEvent16,adverseNextEvent17,adverseNextEvent18,adverseNextEvent19,adverseNextEvent20,adverseNextEvent21,adverseNextEvent22,adverseNextEvent23,adverseNextEvent24,adverseNextEvent25,adverseNextEvent26,adverseNextEvent27,taskReward]
    <;> norm_num
  have hp : rawVisits adverseNextS28Before [] = 27 := by decide
  have hn : rawVisits adverseNextS28Before ([]++[.query 2]) = 3 := by decide
  have hz : (controlPenalty savedCref uniformQuoteError unitRoleUnused .next) adverseNextS28Before [] (.query 2) = (nextNormalPenalty adverseNextS28Before) := by
    simpa only [adverseNextS28Before,nextNormalPenalty] using AgentUCTNextExact.adverse_next_normal_root_quotes_exact 27 (by omega) 2 (by decide)
  unfold indexScore
  rw [hs,hp,hn,hz]
  simp only [BackupStat.mean]
  norm_num

theorem adverseNextS28D0I3 : indexScore (7/5) (controlPenalty savedCref uniformQuoteError unitRoleUnused .next) adverseNextS28Before [] (.query 3) = treeIndex ((0/1)/3) (7/5) (nextNormalPenalty adverseNextS28Before) 27 3 := by
  have hs : replayBackup adverseNextS28Before emptyStatistics ([]++[.query 3]) = ⟨3,(0/1)⟩ := by
    rw [replayBackup_empty_closed_form]
    simp +decide [backedEvents,adverseNextS28Before,adverseNextProposal,adverseNextEvent1,adverseNextEvent2,adverseNextEvent3,adverseNextEvent4,adverseNextEvent5,adverseNextEvent6,adverseNextEvent7,adverseNextEvent8,adverseNextEvent9,adverseNextEvent10,adverseNextEvent11,adverseNextEvent12,adverseNextEvent13,adverseNextEvent14,adverseNextEvent15,adverseNextEvent16,adverseNextEvent17,adverseNextEvent18,adverseNextEvent19,adverseNextEvent20,adverseNextEvent21,adverseNextEvent22,adverseNextEvent23,adverseNextEvent24,adverseNextEvent25,adverseNextEvent26,adverseNextEvent27,taskReward]
    <;> norm_num
  have hp : rawVisits adverseNextS28Before [] = 27 := by decide
  have hn : rawVisits adverseNextS28Before ([]++[.query 3]) = 3 := by decide
  have hz : (controlPenalty savedCref uniformQuoteError unitRoleUnused .next) adverseNextS28Before [] (.query 3) = (nextNormalPenalty adverseNextS28Before) := by
    simpa only [adverseNextS28Before,nextNormalPenalty] using AgentUCTNextExact.adverse_next_normal_root_quotes_exact 27 (by omega) 3 (by decide)
  unfold indexScore
  rw [hs,hp,hn,hz]
  simp only [BackupStat.mean]
  norm_num

theorem adverseNextS28D0I4 : indexScore (7/5) (controlPenalty savedCref uniformQuoteError unitRoleUnused .next) adverseNextS28Before [] (.query 4) = treeIndex ((0/1)/3) (7/5) (nextNormalPenalty adverseNextS28Before) 27 3 := by
  have hs : replayBackup adverseNextS28Before emptyStatistics ([]++[.query 4]) = ⟨3,(0/1)⟩ := by
    rw [replayBackup_empty_closed_form]
    simp +decide [backedEvents,adverseNextS28Before,adverseNextProposal,adverseNextEvent1,adverseNextEvent2,adverseNextEvent3,adverseNextEvent4,adverseNextEvent5,adverseNextEvent6,adverseNextEvent7,adverseNextEvent8,adverseNextEvent9,adverseNextEvent10,adverseNextEvent11,adverseNextEvent12,adverseNextEvent13,adverseNextEvent14,adverseNextEvent15,adverseNextEvent16,adverseNextEvent17,adverseNextEvent18,adverseNextEvent19,adverseNextEvent20,adverseNextEvent21,adverseNextEvent22,adverseNextEvent23,adverseNextEvent24,adverseNextEvent25,adverseNextEvent26,adverseNextEvent27,taskReward]
    <;> norm_num
  have hp : rawVisits adverseNextS28Before [] = 27 := by decide
  have hn : rawVisits adverseNextS28Before ([]++[.query 4]) = 3 := by decide
  have hz : (controlPenalty savedCref uniformQuoteError unitRoleUnused .next) adverseNextS28Before [] (.query 4) = (nextNormalPenalty adverseNextS28Before) := by
    simpa only [adverseNextS28Before,nextNormalPenalty] using AgentUCTNextExact.adverse_next_normal_root_quotes_exact 27 (by omega) 4 (by decide)
  unfold indexScore
  rw [hs,hp,hn,hz]
  simp only [BackupStat.mean]
  norm_num

theorem adverseNextS28D0I5 : indexScore (7/5) (controlPenalty savedCref uniformQuoteError unitRoleUnused .next) adverseNextS28Before [] (.query 5) = treeIndex ((13/10)/5) (7/5) (nextNormalPenalty adverseNextS28Before) 27 5 := by
  have hs : replayBackup adverseNextS28Before emptyStatistics ([]++[.query 5]) = ⟨5,(13/10)⟩ := by
    rw [replayBackup_empty_closed_form]
    simp +decide [backedEvents,adverseNextS28Before,adverseNextProposal,adverseNextEvent1,adverseNextEvent2,adverseNextEvent3,adverseNextEvent4,adverseNextEvent5,adverseNextEvent6,adverseNextEvent7,adverseNextEvent8,adverseNextEvent9,adverseNextEvent10,adverseNextEvent11,adverseNextEvent12,adverseNextEvent13,adverseNextEvent14,adverseNextEvent15,adverseNextEvent16,adverseNextEvent17,adverseNextEvent18,adverseNextEvent19,adverseNextEvent20,adverseNextEvent21,adverseNextEvent22,adverseNextEvent23,adverseNextEvent24,adverseNextEvent25,adverseNextEvent26,adverseNextEvent27,taskReward]
    <;> norm_num
  have hp : rawVisits adverseNextS28Before [] = 27 := by decide
  have hn : rawVisits adverseNextS28Before ([]++[.query 5]) = 5 := by decide
  have hz : (controlPenalty savedCref uniformQuoteError unitRoleUnused .next) adverseNextS28Before [] (.query 5) = (nextNormalPenalty adverseNextS28Before) := by
    simpa only [adverseNextS28Before,nextNormalPenalty] using AgentUCTNextExact.adverse_next_normal_root_quotes_exact 27 (by omega) 5 (by decide)
  unfold indexScore
  rw [hs,hp,hn,hz]
  simp only [BackupStat.mean]
  norm_num

theorem adverseNextS28D0I6 : indexScore (7/5) (controlPenalty savedCref uniformQuoteError unitRoleUnused .next) adverseNextS28Before [] (.query 6) = treeIndex ((0/1)/3) (7/5) (nextNormalPenalty adverseNextS28Before) 27 3 := by
  have hs : replayBackup adverseNextS28Before emptyStatistics ([]++[.query 6]) = ⟨3,(0/1)⟩ := by
    rw [replayBackup_empty_closed_form]
    simp +decide [backedEvents,adverseNextS28Before,adverseNextProposal,adverseNextEvent1,adverseNextEvent2,adverseNextEvent3,adverseNextEvent4,adverseNextEvent5,adverseNextEvent6,adverseNextEvent7,adverseNextEvent8,adverseNextEvent9,adverseNextEvent10,adverseNextEvent11,adverseNextEvent12,adverseNextEvent13,adverseNextEvent14,adverseNextEvent15,adverseNextEvent16,adverseNextEvent17,adverseNextEvent18,adverseNextEvent19,adverseNextEvent20,adverseNextEvent21,adverseNextEvent22,adverseNextEvent23,adverseNextEvent24,adverseNextEvent25,adverseNextEvent26,adverseNextEvent27,taskReward]
    <;> norm_num
  have hp : rawVisits adverseNextS28Before [] = 27 := by decide
  have hn : rawVisits adverseNextS28Before ([]++[.query 6]) = 3 := by decide
  have hz : (controlPenalty savedCref uniformQuoteError unitRoleUnused .next) adverseNextS28Before [] (.query 6) = (nextNormalPenalty adverseNextS28Before) := by
    simpa only [adverseNextS28Before,nextNormalPenalty] using AgentUCTNextExact.adverse_next_normal_root_quotes_exact 27 (by omega) 6 (by decide)
  unfold indexScore
  rw [hs,hp,hn,hz]
  simp only [BackupStat.mean]
  norm_num

theorem adverseNextS28D0I7 : indexScore (7/5) (controlPenalty savedCref uniformQuoteError unitRoleUnused .next) adverseNextS28Before [] (.query 7) = treeIndex ((0/1)/3) (7/5) (nextNormalPenalty adverseNextS28Before) 27 3 := by
  have hs : replayBackup adverseNextS28Before emptyStatistics ([]++[.query 7]) = ⟨3,(0/1)⟩ := by
    rw [replayBackup_empty_closed_form]
    simp +decide [backedEvents,adverseNextS28Before,adverseNextProposal,adverseNextEvent1,adverseNextEvent2,adverseNextEvent3,adverseNextEvent4,adverseNextEvent5,adverseNextEvent6,adverseNextEvent7,adverseNextEvent8,adverseNextEvent9,adverseNextEvent10,adverseNextEvent11,adverseNextEvent12,adverseNextEvent13,adverseNextEvent14,adverseNextEvent15,adverseNextEvent16,adverseNextEvent17,adverseNextEvent18,adverseNextEvent19,adverseNextEvent20,adverseNextEvent21,adverseNextEvent22,adverseNextEvent23,adverseNextEvent24,adverseNextEvent25,adverseNextEvent26,adverseNextEvent27,taskReward]
    <;> norm_num
  have hp : rawVisits adverseNextS28Before [] = 27 := by decide
  have hn : rawVisits adverseNextS28Before ([]++[.query 7]) = 3 := by decide
  have hz : (controlPenalty savedCref uniformQuoteError unitRoleUnused .next) adverseNextS28Before [] (.query 7) = (nextNormalPenalty adverseNextS28Before) := by
    simpa only [adverseNextS28Before,nextNormalPenalty] using AgentUCTNextExact.adverse_next_normal_root_quotes_exact 27 (by omega) 7 (by decide)
  unfold indexScore
  rw [hs,hp,hn,hz]
  simp only [BackupStat.mean]
  norm_num

theorem adverseNextS28D0Cmp0 : indexScore (7/5) (controlPenalty savedCref uniformQuoteError unitRoleUnused .next) adverseNextS28Before [] (.query 0) < indexScore (7/5) (controlPenalty savedCref uniformQuoteError unitRoleUnused .next) adverseNextS28Before [] (.query 1) := by
  rw [adverseNextS28D0I0,adverseNextS28D0I1]
  have hk := adverse_next_penalty_interval 27 (by omega)
  change nextNormalPenaltyLower ≤ nextNormalPenalty adverseNextS28Before ∧ nextNormalPenalty adverseNextS28Before ≤ nextNormalPenaltyUpper at hk
  have hm : ((0/1)/3)+(73773987/50000000)-(nextNormalPenalty adverseNextS28Before) < ((0/1)/4)+(63890141/50000000)-0 := by
    have h : ((0/1)/3)+(73773987/50000000)-nextNormalPenaltyLower < ((0/1)/4)+(63890141/50000000) := by norm_num [nextNormalPenaltyLower,savedCref,uniformQuoteError]
    linarith [hk.1]
  have h := index_strict_order_from_intervals ((0/1)/4) ((0/1)/3) 0 (nextNormalPenalty adverseNextS28Before) (63890141/50000000) (73773987/50000000)
    (treeBonus (7/5) 27 4) (treeBonus (7/5) 27 3)
    (trajectory_bonus_27_4).1 (trajectory_bonus_27_3).2 hm
  simpa only [treeIndex] using h

theorem adverseNextS28D0Cmp2 : indexScore (7/5) (controlPenalty savedCref uniformQuoteError unitRoleUnused .next) adverseNextS28Before [] (.query 2) ≤ indexScore (7/5) (controlPenalty savedCref uniformQuoteError unitRoleUnused .next) adverseNextS28Before [] (.query 1) := by
  rw [adverseNextS28D0I2,adverseNextS28D0I1]
  have hk := adverse_next_penalty_interval 27 (by omega)
  change nextNormalPenaltyLower ≤ nextNormalPenalty adverseNextS28Before ∧ nextNormalPenalty adverseNextS28Before ≤ nextNormalPenaltyUpper at hk
  have hm : ((0/1)/3)+(73773987/50000000)-(nextNormalPenalty adverseNextS28Before) < ((0/1)/4)+(63890141/50000000)-0 := by
    have h : ((0/1)/3)+(73773987/50000000)-nextNormalPenaltyLower < ((0/1)/4)+(63890141/50000000) := by norm_num [nextNormalPenaltyLower,savedCref,uniformQuoteError]
    linarith [hk.1]
  have h := index_weak_order_from_intervals ((0/1)/4) ((0/1)/3) 0 (nextNormalPenalty adverseNextS28Before) (63890141/50000000) (73773987/50000000)
    (treeBonus (7/5) 27 4) (treeBonus (7/5) 27 3)
    (trajectory_bonus_27_4).1 (trajectory_bonus_27_3).2 hm.le
  simpa only [treeIndex] using h

theorem adverseNextS28D0Cmp3 : indexScore (7/5) (controlPenalty savedCref uniformQuoteError unitRoleUnused .next) adverseNextS28Before [] (.query 3) ≤ indexScore (7/5) (controlPenalty savedCref uniformQuoteError unitRoleUnused .next) adverseNextS28Before [] (.query 1) := by
  rw [adverseNextS28D0I3,adverseNextS28D0I1]
  have hk := adverse_next_penalty_interval 27 (by omega)
  change nextNormalPenaltyLower ≤ nextNormalPenalty adverseNextS28Before ∧ nextNormalPenalty adverseNextS28Before ≤ nextNormalPenaltyUpper at hk
  have hm : ((0/1)/3)+(73773987/50000000)-(nextNormalPenalty adverseNextS28Before) < ((0/1)/4)+(63890141/50000000)-0 := by
    have h : ((0/1)/3)+(73773987/50000000)-nextNormalPenaltyLower < ((0/1)/4)+(63890141/50000000) := by norm_num [nextNormalPenaltyLower,savedCref,uniformQuoteError]
    linarith [hk.1]
  have h := index_weak_order_from_intervals ((0/1)/4) ((0/1)/3) 0 (nextNormalPenalty adverseNextS28Before) (63890141/50000000) (73773987/50000000)
    (treeBonus (7/5) 27 4) (treeBonus (7/5) 27 3)
    (trajectory_bonus_27_4).1 (trajectory_bonus_27_3).2 hm.le
  simpa only [treeIndex] using h

theorem adverseNextS28D0Cmp4 : indexScore (7/5) (controlPenalty savedCref uniformQuoteError unitRoleUnused .next) adverseNextS28Before [] (.query 4) ≤ indexScore (7/5) (controlPenalty savedCref uniformQuoteError unitRoleUnused .next) adverseNextS28Before [] (.query 1) := by
  rw [adverseNextS28D0I4,adverseNextS28D0I1]
  have hk := adverse_next_penalty_interval 27 (by omega)
  change nextNormalPenaltyLower ≤ nextNormalPenalty adverseNextS28Before ∧ nextNormalPenalty adverseNextS28Before ≤ nextNormalPenaltyUpper at hk
  have hm : ((0/1)/3)+(73773987/50000000)-(nextNormalPenalty adverseNextS28Before) < ((0/1)/4)+(63890141/50000000)-0 := by
    have h : ((0/1)/3)+(73773987/50000000)-nextNormalPenaltyLower < ((0/1)/4)+(63890141/50000000) := by norm_num [nextNormalPenaltyLower,savedCref,uniformQuoteError]
    linarith [hk.1]
  have h := index_weak_order_from_intervals ((0/1)/4) ((0/1)/3) 0 (nextNormalPenalty adverseNextS28Before) (63890141/50000000) (73773987/50000000)
    (treeBonus (7/5) 27 4) (treeBonus (7/5) 27 3)
    (trajectory_bonus_27_4).1 (trajectory_bonus_27_3).2 hm.le
  simpa only [treeIndex] using h

theorem adverseNextS28D0Cmp5 : indexScore (7/5) (controlPenalty savedCref uniformQuoteError unitRoleUnused .next) adverseNextS28Before [] (.query 5) ≤ indexScore (7/5) (controlPenalty savedCref uniformQuoteError unitRoleUnused .next) adverseNextS28Before [] (.query 1) := by
  rw [adverseNextS28D0I5,adverseNextS28D0I1]
  have hk := adverse_next_penalty_interval 27 (by omega)
  change nextNormalPenaltyLower ≤ nextNormalPenalty adverseNextS28Before ∧ nextNormalPenalty adverseNextS28Before ≤ nextNormalPenaltyUpper at hk
  have hm : ((13/10)/5)+(446446/390625)-(nextNormalPenalty adverseNextS28Before) < ((0/1)/4)+(63890141/50000000)-0 := by
    have h : ((13/10)/5)+(446446/390625)-nextNormalPenaltyLower < ((0/1)/4)+(63890141/50000000) := by norm_num [nextNormalPenaltyLower,savedCref,uniformQuoteError]
    linarith [hk.1]
  have h := index_weak_order_from_intervals ((0/1)/4) ((13/10)/5) 0 (nextNormalPenalty adverseNextS28Before) (63890141/50000000) (446446/390625)
    (treeBonus (7/5) 27 4) (treeBonus (7/5) 27 5)
    (trajectory_bonus_27_4).1 (trajectory_bonus_27_5).2 hm.le
  simpa only [treeIndex] using h

theorem adverseNextS28D0Cmp6 : indexScore (7/5) (controlPenalty savedCref uniformQuoteError unitRoleUnused .next) adverseNextS28Before [] (.query 6) ≤ indexScore (7/5) (controlPenalty savedCref uniformQuoteError unitRoleUnused .next) adverseNextS28Before [] (.query 1) := by
  rw [adverseNextS28D0I6,adverseNextS28D0I1]
  have hk := adverse_next_penalty_interval 27 (by omega)
  change nextNormalPenaltyLower ≤ nextNormalPenalty adverseNextS28Before ∧ nextNormalPenalty adverseNextS28Before ≤ nextNormalPenaltyUpper at hk
  have hm : ((0/1)/3)+(73773987/50000000)-(nextNormalPenalty adverseNextS28Before) < ((0/1)/4)+(63890141/50000000)-0 := by
    have h : ((0/1)/3)+(73773987/50000000)-nextNormalPenaltyLower < ((0/1)/4)+(63890141/50000000) := by norm_num [nextNormalPenaltyLower,savedCref,uniformQuoteError]
    linarith [hk.1]
  have h := index_weak_order_from_intervals ((0/1)/4) ((0/1)/3) 0 (nextNormalPenalty adverseNextS28Before) (63890141/50000000) (73773987/50000000)
    (treeBonus (7/5) 27 4) (treeBonus (7/5) 27 3)
    (trajectory_bonus_27_4).1 (trajectory_bonus_27_3).2 hm.le
  simpa only [treeIndex] using h

theorem adverseNextS28D0Cmp7 : indexScore (7/5) (controlPenalty savedCref uniformQuoteError unitRoleUnused .next) adverseNextS28Before [] (.query 7) ≤ indexScore (7/5) (controlPenalty savedCref uniformQuoteError unitRoleUnused .next) adverseNextS28Before [] (.query 1) := by
  rw [adverseNextS28D0I7,adverseNextS28D0I1]
  have hk := adverse_next_penalty_interval 27 (by omega)
  change nextNormalPenaltyLower ≤ nextNormalPenalty adverseNextS28Before ∧ nextNormalPenalty adverseNextS28Before ≤ nextNormalPenaltyUpper at hk
  have hm : ((0/1)/3)+(73773987/50000000)-(nextNormalPenalty adverseNextS28Before) < ((0/1)/4)+(63890141/50000000)-0 := by
    have h : ((0/1)/3)+(73773987/50000000)-nextNormalPenaltyLower < ((0/1)/4)+(63890141/50000000) := by norm_num [nextNormalPenaltyLower,savedCref,uniformQuoteError]
    linarith [hk.1]
  have h := index_weak_order_from_intervals ((0/1)/4) ((0/1)/3) 0 (nextNormalPenalty adverseNextS28Before) (63890141/50000000) (73773987/50000000)
    (treeBonus (7/5) 27 4) (treeBonus (7/5) 27 3)
    (trajectory_bonus_27_4).1 (trajectory_bonus_27_3).2 hm.le
  simpa only [treeIndex] using h

theorem adverseNextS28Choice0 : nativeFirstChoice (indexScore (7/5) (controlPenalty savedCref uniformQuoteError unitRoleUnused .next) adverseNextS28Before []) adverseNextS28Before [] = .query 1 := by
  apply visited_choice_from_ordered_certificate _ _ [] [.query 0] [.query 2,.query 3,.query 4,.query 5,.query 6,.query 7] (.query 1) (by decide)
  · intro a ha
    have ho : orderedLegalAvailable [] = [.query 0,.query 1,.query 2,.query 3,.query 4,.query 5,.query 6,.query 7] := by decide
    rw [ho] at ha
    simp only [List.mem_cons,List.not_mem_nil,or_false] at ha
    rcases ha with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> decide
  · intro a ha
    simp only [List.mem_cons,List.not_mem_nil,or_false] at ha
    rcases ha with rfl
    · exact adverseNextS28D0Cmp0
  · intro a ha
    simp only [List.mem_cons,List.not_mem_nil,or_false] at ha
    rcases ha with rfl | rfl | rfl | rfl | rfl | rfl
    · exact adverseNextS28D0Cmp2
    · exact adverseNextS28D0Cmp3
    · exact adverseNextS28D0Cmp4
    · exact adverseNextS28D0Cmp5
    · exact adverseNextS28D0Cmp6
    · exact adverseNextS28D0Cmp7

theorem adverseNextS28D1I0 : indexScore (7/5) (controlPenalty savedCref uniformQuoteError unitRoleUnused .next) adverseNextS28Before [.query 1] (.hydeRetriever 1) = treeIndex ((0/1)/1) (7/5) 0 4 1 := by
  have hs : replayBackup adverseNextS28Before emptyStatistics ([.query 1]++[.hydeRetriever 1]) = ⟨1,(0/1)⟩ := by
    rw [replayBackup_empty_closed_form]
    simp +decide [backedEvents,adverseNextS28Before,adverseNextProposal,adverseNextEvent1,adverseNextEvent2,adverseNextEvent3,adverseNextEvent4,adverseNextEvent5,adverseNextEvent6,adverseNextEvent7,adverseNextEvent8,adverseNextEvent9,adverseNextEvent10,adverseNextEvent11,adverseNextEvent12,adverseNextEvent13,adverseNextEvent14,adverseNextEvent15,adverseNextEvent16,adverseNextEvent17,adverseNextEvent18,adverseNextEvent19,adverseNextEvent20,adverseNextEvent21,adverseNextEvent22,adverseNextEvent23,adverseNextEvent24,adverseNextEvent25,adverseNextEvent26,adverseNextEvent27,taskReward]
    <;> norm_num
  have hp : rawVisits adverseNextS28Before [.query 1] = 4 := by decide
  have hn : rawVisits adverseNextS28Before ([.query 1]++[.hydeRetriever 1]) = 1 := by decide
  have hz : (controlPenalty savedCref uniformQuoteError unitRoleUnused .next) adverseNextS28Before [.query 1] (.hydeRetriever 1) = 0 := by
    apply control_penalty_empty_of_prior_terminal .next savedCref uniformQuoteError adverseNextS28Before [.query 1] (.hydeRetriever 1) 9 (by decide)
    · decide
    · decide
  unfold indexScore
  rw [hs,hp,hn,hz]
  simp only [BackupStat.mean]
  norm_num

theorem adverseNextS28D1I1 : indexScore (7/5) (controlPenalty savedCref uniformQuoteError unitRoleUnused .next) adverseNextS28Before [.query 1] (.hydeRetriever 0) = treeIndex ((0/1)/1) (7/5) 0 4 1 := by
  have hs : replayBackup adverseNextS28Before emptyStatistics ([.query 1]++[.hydeRetriever 0]) = ⟨1,(0/1)⟩ := by
    rw [replayBackup_empty_closed_form]
    simp +decide [backedEvents,adverseNextS28Before,adverseNextProposal,adverseNextEvent1,adverseNextEvent2,adverseNextEvent3,adverseNextEvent4,adverseNextEvent5,adverseNextEvent6,adverseNextEvent7,adverseNextEvent8,adverseNextEvent9,adverseNextEvent10,adverseNextEvent11,adverseNextEvent12,adverseNextEvent13,adverseNextEvent14,adverseNextEvent15,adverseNextEvent16,adverseNextEvent17,adverseNextEvent18,adverseNextEvent19,adverseNextEvent20,adverseNextEvent21,adverseNextEvent22,adverseNextEvent23,adverseNextEvent24,adverseNextEvent25,adverseNextEvent26,adverseNextEvent27,taskReward]
    <;> norm_num
  have hp : rawVisits adverseNextS28Before [.query 1] = 4 := by decide
  have hn : rawVisits adverseNextS28Before ([.query 1]++[.hydeRetriever 0]) = 1 := by decide
  have hz : (controlPenalty savedCref uniformQuoteError unitRoleUnused .next) adverseNextS28Before [.query 1] (.hydeRetriever 0) = 0 := by
    apply control_penalty_empty_of_prior_terminal .next savedCref uniformQuoteError adverseNextS28Before [.query 1] (.hydeRetriever 0) 1 (by decide)
    · decide
    · decide
  unfold indexScore
  rw [hs,hp,hn,hz]
  simp only [BackupStat.mean]
  norm_num

theorem adverseNextS28D1I2 : indexScore (7/5) (controlPenalty savedCref uniformQuoteError unitRoleUnused .next) adverseNextS28Before [.query 1] (.hydeRetriever 2) = treeIndex ((0/1)/1) (7/5) 0 4 1 := by
  have hs : replayBackup adverseNextS28Before emptyStatistics ([.query 1]++[.hydeRetriever 2]) = ⟨1,(0/1)⟩ := by
    rw [replayBackup_empty_closed_form]
    simp +decide [backedEvents,adverseNextS28Before,adverseNextProposal,adverseNextEvent1,adverseNextEvent2,adverseNextEvent3,adverseNextEvent4,adverseNextEvent5,adverseNextEvent6,adverseNextEvent7,adverseNextEvent8,adverseNextEvent9,adverseNextEvent10,adverseNextEvent11,adverseNextEvent12,adverseNextEvent13,adverseNextEvent14,adverseNextEvent15,adverseNextEvent16,adverseNextEvent17,adverseNextEvent18,adverseNextEvent19,adverseNextEvent20,adverseNextEvent21,adverseNextEvent22,adverseNextEvent23,adverseNextEvent24,adverseNextEvent25,adverseNextEvent26,adverseNextEvent27,taskReward]
    <;> norm_num
  have hp : rawVisits adverseNextS28Before [.query 1] = 4 := by decide
  have hn : rawVisits adverseNextS28Before ([.query 1]++[.hydeRetriever 2]) = 1 := by decide
  have hz : (controlPenalty savedCref uniformQuoteError unitRoleUnused .next) adverseNextS28Before [.query 1] (.hydeRetriever 2) = 0 := by
    apply control_penalty_empty_of_prior_terminal .next savedCref uniformQuoteError adverseNextS28Before [.query 1] (.hydeRetriever 2) 25 (by decide)
    · decide
    · decide
  unfold indexScore
  rw [hs,hp,hn,hz]
  simp only [BackupStat.mean]
  norm_num

theorem adverseNextS28D1Cmp1 : indexScore (7/5) (controlPenalty savedCref uniformQuoteError unitRoleUnused .next) adverseNextS28Before [.query 1] (.hydeRetriever 0) ≤ indexScore (7/5) (controlPenalty savedCref uniformQuoteError unitRoleUnused .next) adverseNextS28Before [.query 1] (.hydeRetriever 1) := by
  rw [adverseNextS28D1I1,adverseNextS28D1I0]

theorem adverseNextS28D1Cmp2 : indexScore (7/5) (controlPenalty savedCref uniformQuoteError unitRoleUnused .next) adverseNextS28Before [.query 1] (.hydeRetriever 2) ≤ indexScore (7/5) (controlPenalty savedCref uniformQuoteError unitRoleUnused .next) adverseNextS28Before [.query 1] (.hydeRetriever 1) := by
  rw [adverseNextS28D1I2,adverseNextS28D1I0]

theorem adverseNextS28Choice1 : nativeFirstChoice (indexScore (7/5) (controlPenalty savedCref uniformQuoteError unitRoleUnused .next) adverseNextS28Before [.query 1]) adverseNextS28Before [.query 1] = .hydeRetriever 1 := by
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
    · exact adverseNextS28D1Cmp1
    · exact adverseNextS28D1Cmp2

theorem adverseNextS28ActualEvent : nativeEvent budgetTape (7/5) (controlPenalty savedCref uniformQuoteError unitRoleUnused .next)
    (taskReward true (2/5) (1/2)) adverseNextS28Before = adverseNextEvent28 := by
  have hs0 := native_select_existing_step budgetTape (7/5) (controlPenalty savedCref uniformQuoteError unitRoleUnused .next) adverseNextS28Before 8 [] (.query 1)
    (by decide) (by decide) adverseNextS28Choice0
  have hs1 := native_select_existing_step budgetTape (7/5) (controlPenalty savedCref uniformQuoteError unitRoleUnused .next) adverseNextS28Before 7 [.query 1] (.hydeRetriever 1)
    (by decide) (by decide) adverseNextS28Choice1
  have hnew := native_select_new_step budgetTape (7/5) (controlPenalty savedCref uniformQuoteError unitRoleUnused .next) adverseNextS28Before 6 [.query 1,.hydeRetriever 1]
    [.selection 1,.selection 2,.selection 3,.selection 0] (.selection 0) (by decide) (by decide) (by decide) (by decide)
  have hs : nativeSelect budgetTape (7/5) (controlPenalty savedCref uniformQuoteError unitRoleUnused .next) adverseNextS28Before 9 [] = [.query 1,.hydeRetriever 1,.selection 0] := by
    rw [hs0]
    change nativeSelect budgetTape (7/5) (controlPenalty savedCref uniformQuoteError unitRoleUnused .next) adverseNextS28Before 8 [.query 1] = _
    rw [hs1]
    change nativeSelect budgetTape (7/5) (controlPenalty savedCref uniformQuoteError unitRoleUnused .next) adverseNextS28Before 7 [.query 1,.hydeRetriever 1] = _
    rw [hnew] <;> rfl
  have hr : repairedRollout budgetTape adverseNextS28Before 9 [.query 1,.hydeRetriever 1,.selection 0] = [.query 1,.hydeRetriever 1,.selection 0,.width 1,.stop,.reranker 0,.topm 0,.context 0,.answer 0] := by decide
  simp only [nativeEvent,hs,hr]
  rfl

def adverseNextS29Before := adverseNextProposal.take 28

theorem adverseNextS29D0I0 : indexScore (7/5) (controlPenalty savedCref uniformQuoteError unitRoleUnused .next) adverseNextS29Before [] (.query 0) = treeIndex ((0/1)/3) (7/5) (nextNormalPenalty adverseNextS29Before) 28 3 := by
  have hs : replayBackup adverseNextS29Before emptyStatistics ([]++[.query 0]) = ⟨3,(0/1)⟩ := by
    rw [replayBackup_empty_closed_form]
    simp +decide [backedEvents,adverseNextS29Before,adverseNextProposal,adverseNextEvent1,adverseNextEvent2,adverseNextEvent3,adverseNextEvent4,adverseNextEvent5,adverseNextEvent6,adverseNextEvent7,adverseNextEvent8,adverseNextEvent9,adverseNextEvent10,adverseNextEvent11,adverseNextEvent12,adverseNextEvent13,adverseNextEvent14,adverseNextEvent15,adverseNextEvent16,adverseNextEvent17,adverseNextEvent18,adverseNextEvent19,adverseNextEvent20,adverseNextEvent21,adverseNextEvent22,adverseNextEvent23,adverseNextEvent24,adverseNextEvent25,adverseNextEvent26,adverseNextEvent27,adverseNextEvent28,taskReward]
    <;> norm_num
  have hp : rawVisits adverseNextS29Before [] = 28 := by decide
  have hn : rawVisits adverseNextS29Before ([]++[.query 0]) = 3 := by decide
  have hz : (controlPenalty savedCref uniformQuoteError unitRoleUnused .next) adverseNextS29Before [] (.query 0) = (nextNormalPenalty adverseNextS29Before) := by
    simpa only [adverseNextS29Before,nextNormalPenalty] using AgentUCTNextExact.adverse_next_normal_root_quotes_exact 28 (by omega) 0 (by decide)
  unfold indexScore
  rw [hs,hp,hn,hz]
  simp only [BackupStat.mean]
  norm_num

theorem adverseNextS29D0I1 : indexScore (7/5) (controlPenalty savedCref uniformQuoteError unitRoleUnused .next) adverseNextS29Before [] (.query 1) = treeIndex ((0/1)/5) (7/5) 0 28 5 := by
  have hs : replayBackup adverseNextS29Before emptyStatistics ([]++[.query 1]) = ⟨5,(0/1)⟩ := by
    rw [replayBackup_empty_closed_form]
    simp +decide [backedEvents,adverseNextS29Before,adverseNextProposal,adverseNextEvent1,adverseNextEvent2,adverseNextEvent3,adverseNextEvent4,adverseNextEvent5,adverseNextEvent6,adverseNextEvent7,adverseNextEvent8,adverseNextEvent9,adverseNextEvent10,adverseNextEvent11,adverseNextEvent12,adverseNextEvent13,adverseNextEvent14,adverseNextEvent15,adverseNextEvent16,adverseNextEvent17,adverseNextEvent18,adverseNextEvent19,adverseNextEvent20,adverseNextEvent21,adverseNextEvent22,adverseNextEvent23,adverseNextEvent24,adverseNextEvent25,adverseNextEvent26,adverseNextEvent27,adverseNextEvent28,taskReward]
    <;> norm_num
  have hp : rawVisits adverseNextS29Before [] = 28 := by decide
  have hn : rawVisits adverseNextS29Before ([]++[.query 1]) = 5 := by decide
  have hz : (controlPenalty savedCref uniformQuoteError unitRoleUnused .next) adverseNextS29Before [] (.query 1) = 0 := by
    apply control_penalty_empty_suffix
    exact AgentUCTNextExact.adverse_next_hyde_root_suffix_empty 28 (by omega)
  unfold indexScore
  rw [hs,hp,hn,hz]
  simp only [BackupStat.mean]
  norm_num

theorem adverseNextS29D0I2 : indexScore (7/5) (controlPenalty savedCref uniformQuoteError unitRoleUnused .next) adverseNextS29Before [] (.query 2) = treeIndex ((0/1)/3) (7/5) (nextNormalPenalty adverseNextS29Before) 28 3 := by
  have hs : replayBackup adverseNextS29Before emptyStatistics ([]++[.query 2]) = ⟨3,(0/1)⟩ := by
    rw [replayBackup_empty_closed_form]
    simp +decide [backedEvents,adverseNextS29Before,adverseNextProposal,adverseNextEvent1,adverseNextEvent2,adverseNextEvent3,adverseNextEvent4,adverseNextEvent5,adverseNextEvent6,adverseNextEvent7,adverseNextEvent8,adverseNextEvent9,adverseNextEvent10,adverseNextEvent11,adverseNextEvent12,adverseNextEvent13,adverseNextEvent14,adverseNextEvent15,adverseNextEvent16,adverseNextEvent17,adverseNextEvent18,adverseNextEvent19,adverseNextEvent20,adverseNextEvent21,adverseNextEvent22,adverseNextEvent23,adverseNextEvent24,adverseNextEvent25,adverseNextEvent26,adverseNextEvent27,adverseNextEvent28,taskReward]
    <;> norm_num
  have hp : rawVisits adverseNextS29Before [] = 28 := by decide
  have hn : rawVisits adverseNextS29Before ([]++[.query 2]) = 3 := by decide
  have hz : (controlPenalty savedCref uniformQuoteError unitRoleUnused .next) adverseNextS29Before [] (.query 2) = (nextNormalPenalty adverseNextS29Before) := by
    simpa only [adverseNextS29Before,nextNormalPenalty] using AgentUCTNextExact.adverse_next_normal_root_quotes_exact 28 (by omega) 2 (by decide)
  unfold indexScore
  rw [hs,hp,hn,hz]
  simp only [BackupStat.mean]
  norm_num

theorem adverseNextS29D0I3 : indexScore (7/5) (controlPenalty savedCref uniformQuoteError unitRoleUnused .next) adverseNextS29Before [] (.query 3) = treeIndex ((0/1)/3) (7/5) (nextNormalPenalty adverseNextS29Before) 28 3 := by
  have hs : replayBackup adverseNextS29Before emptyStatistics ([]++[.query 3]) = ⟨3,(0/1)⟩ := by
    rw [replayBackup_empty_closed_form]
    simp +decide [backedEvents,adverseNextS29Before,adverseNextProposal,adverseNextEvent1,adverseNextEvent2,adverseNextEvent3,adverseNextEvent4,adverseNextEvent5,adverseNextEvent6,adverseNextEvent7,adverseNextEvent8,adverseNextEvent9,adverseNextEvent10,adverseNextEvent11,adverseNextEvent12,adverseNextEvent13,adverseNextEvent14,adverseNextEvent15,adverseNextEvent16,adverseNextEvent17,adverseNextEvent18,adverseNextEvent19,adverseNextEvent20,adverseNextEvent21,adverseNextEvent22,adverseNextEvent23,adverseNextEvent24,adverseNextEvent25,adverseNextEvent26,adverseNextEvent27,adverseNextEvent28,taskReward]
    <;> norm_num
  have hp : rawVisits adverseNextS29Before [] = 28 := by decide
  have hn : rawVisits adverseNextS29Before ([]++[.query 3]) = 3 := by decide
  have hz : (controlPenalty savedCref uniformQuoteError unitRoleUnused .next) adverseNextS29Before [] (.query 3) = (nextNormalPenalty adverseNextS29Before) := by
    simpa only [adverseNextS29Before,nextNormalPenalty] using AgentUCTNextExact.adverse_next_normal_root_quotes_exact 28 (by omega) 3 (by decide)
  unfold indexScore
  rw [hs,hp,hn,hz]
  simp only [BackupStat.mean]
  norm_num

theorem adverseNextS29D0I4 : indexScore (7/5) (controlPenalty savedCref uniformQuoteError unitRoleUnused .next) adverseNextS29Before [] (.query 4) = treeIndex ((0/1)/3) (7/5) (nextNormalPenalty adverseNextS29Before) 28 3 := by
  have hs : replayBackup adverseNextS29Before emptyStatistics ([]++[.query 4]) = ⟨3,(0/1)⟩ := by
    rw [replayBackup_empty_closed_form]
    simp +decide [backedEvents,adverseNextS29Before,adverseNextProposal,adverseNextEvent1,adverseNextEvent2,adverseNextEvent3,adverseNextEvent4,adverseNextEvent5,adverseNextEvent6,adverseNextEvent7,adverseNextEvent8,adverseNextEvent9,adverseNextEvent10,adverseNextEvent11,adverseNextEvent12,adverseNextEvent13,adverseNextEvent14,adverseNextEvent15,adverseNextEvent16,adverseNextEvent17,adverseNextEvent18,adverseNextEvent19,adverseNextEvent20,adverseNextEvent21,adverseNextEvent22,adverseNextEvent23,adverseNextEvent24,adverseNextEvent25,adverseNextEvent26,adverseNextEvent27,adverseNextEvent28,taskReward]
    <;> norm_num
  have hp : rawVisits adverseNextS29Before [] = 28 := by decide
  have hn : rawVisits adverseNextS29Before ([]++[.query 4]) = 3 := by decide
  have hz : (controlPenalty savedCref uniformQuoteError unitRoleUnused .next) adverseNextS29Before [] (.query 4) = (nextNormalPenalty adverseNextS29Before) := by
    simpa only [adverseNextS29Before,nextNormalPenalty] using AgentUCTNextExact.adverse_next_normal_root_quotes_exact 28 (by omega) 4 (by decide)
  unfold indexScore
  rw [hs,hp,hn,hz]
  simp only [BackupStat.mean]
  norm_num

theorem adverseNextS29D0I5 : indexScore (7/5) (controlPenalty savedCref uniformQuoteError unitRoleUnused .next) adverseNextS29Before [] (.query 5) = treeIndex ((13/10)/5) (7/5) (nextNormalPenalty adverseNextS29Before) 28 5 := by
  have hs : replayBackup adverseNextS29Before emptyStatistics ([]++[.query 5]) = ⟨5,(13/10)⟩ := by
    rw [replayBackup_empty_closed_form]
    simp +decide [backedEvents,adverseNextS29Before,adverseNextProposal,adverseNextEvent1,adverseNextEvent2,adverseNextEvent3,adverseNextEvent4,adverseNextEvent5,adverseNextEvent6,adverseNextEvent7,adverseNextEvent8,adverseNextEvent9,adverseNextEvent10,adverseNextEvent11,adverseNextEvent12,adverseNextEvent13,adverseNextEvent14,adverseNextEvent15,adverseNextEvent16,adverseNextEvent17,adverseNextEvent18,adverseNextEvent19,adverseNextEvent20,adverseNextEvent21,adverseNextEvent22,adverseNextEvent23,adverseNextEvent24,adverseNextEvent25,adverseNextEvent26,adverseNextEvent27,adverseNextEvent28,taskReward]
    <;> norm_num
  have hp : rawVisits adverseNextS29Before [] = 28 := by decide
  have hn : rawVisits adverseNextS29Before ([]++[.query 5]) = 5 := by decide
  have hz : (controlPenalty savedCref uniformQuoteError unitRoleUnused .next) adverseNextS29Before [] (.query 5) = (nextNormalPenalty adverseNextS29Before) := by
    simpa only [adverseNextS29Before,nextNormalPenalty] using AgentUCTNextExact.adverse_next_normal_root_quotes_exact 28 (by omega) 5 (by decide)
  unfold indexScore
  rw [hs,hp,hn,hz]
  simp only [BackupStat.mean]
  norm_num

theorem adverseNextS29D0I6 : indexScore (7/5) (controlPenalty savedCref uniformQuoteError unitRoleUnused .next) adverseNextS29Before [] (.query 6) = treeIndex ((0/1)/3) (7/5) (nextNormalPenalty adverseNextS29Before) 28 3 := by
  have hs : replayBackup adverseNextS29Before emptyStatistics ([]++[.query 6]) = ⟨3,(0/1)⟩ := by
    rw [replayBackup_empty_closed_form]
    simp +decide [backedEvents,adverseNextS29Before,adverseNextProposal,adverseNextEvent1,adverseNextEvent2,adverseNextEvent3,adverseNextEvent4,adverseNextEvent5,adverseNextEvent6,adverseNextEvent7,adverseNextEvent8,adverseNextEvent9,adverseNextEvent10,adverseNextEvent11,adverseNextEvent12,adverseNextEvent13,adverseNextEvent14,adverseNextEvent15,adverseNextEvent16,adverseNextEvent17,adverseNextEvent18,adverseNextEvent19,adverseNextEvent20,adverseNextEvent21,adverseNextEvent22,adverseNextEvent23,adverseNextEvent24,adverseNextEvent25,adverseNextEvent26,adverseNextEvent27,adverseNextEvent28,taskReward]
    <;> norm_num
  have hp : rawVisits adverseNextS29Before [] = 28 := by decide
  have hn : rawVisits adverseNextS29Before ([]++[.query 6]) = 3 := by decide
  have hz : (controlPenalty savedCref uniformQuoteError unitRoleUnused .next) adverseNextS29Before [] (.query 6) = (nextNormalPenalty adverseNextS29Before) := by
    simpa only [adverseNextS29Before,nextNormalPenalty] using AgentUCTNextExact.adverse_next_normal_root_quotes_exact 28 (by omega) 6 (by decide)
  unfold indexScore
  rw [hs,hp,hn,hz]
  simp only [BackupStat.mean]
  norm_num

theorem adverseNextS29D0I7 : indexScore (7/5) (controlPenalty savedCref uniformQuoteError unitRoleUnused .next) adverseNextS29Before [] (.query 7) = treeIndex ((0/1)/3) (7/5) (nextNormalPenalty adverseNextS29Before) 28 3 := by
  have hs : replayBackup adverseNextS29Before emptyStatistics ([]++[.query 7]) = ⟨3,(0/1)⟩ := by
    rw [replayBackup_empty_closed_form]
    simp +decide [backedEvents,adverseNextS29Before,adverseNextProposal,adverseNextEvent1,adverseNextEvent2,adverseNextEvent3,adverseNextEvent4,adverseNextEvent5,adverseNextEvent6,adverseNextEvent7,adverseNextEvent8,adverseNextEvent9,adverseNextEvent10,adverseNextEvent11,adverseNextEvent12,adverseNextEvent13,adverseNextEvent14,adverseNextEvent15,adverseNextEvent16,adverseNextEvent17,adverseNextEvent18,adverseNextEvent19,adverseNextEvent20,adverseNextEvent21,adverseNextEvent22,adverseNextEvent23,adverseNextEvent24,adverseNextEvent25,adverseNextEvent26,adverseNextEvent27,adverseNextEvent28,taskReward]
    <;> norm_num
  have hp : rawVisits adverseNextS29Before [] = 28 := by decide
  have hn : rawVisits adverseNextS29Before ([]++[.query 7]) = 3 := by decide
  have hz : (controlPenalty savedCref uniformQuoteError unitRoleUnused .next) adverseNextS29Before [] (.query 7) = (nextNormalPenalty adverseNextS29Before) := by
    simpa only [adverseNextS29Before,nextNormalPenalty] using AgentUCTNextExact.adverse_next_normal_root_quotes_exact 28 (by omega) 7 (by decide)
  unfold indexScore
  rw [hs,hp,hn,hz]
  simp only [BackupStat.mean]
  norm_num

theorem adverseNextS29D0Cmp1 : indexScore (7/5) (controlPenalty savedCref uniformQuoteError unitRoleUnused .next) adverseNextS29Before [] (.query 1) ≤ indexScore (7/5) (controlPenalty savedCref uniformQuoteError unitRoleUnused .next) adverseNextS29Before [] (.query 0) := by
  rw [adverseNextS29D0I1,adverseNextS29D0I0]
  have hk := adverse_next_penalty_interval 28 (by omega)
  change nextNormalPenaltyLower ≤ nextNormalPenalty adverseNextS29Before ∧ nextNormalPenalty adverseNextS29Before ≤ nextNormalPenaltyUpper at hk
  have hm : ((0/1)/5)+(7180649/6250000)-0 < ((0/1)/3)+(9270177/6250000)-(nextNormalPenalty adverseNextS29Before) := by
    have h : ((0/1)/5)+(7180649/6250000) < ((0/1)/3)+(9270177/6250000)-nextNormalPenaltyUpper := by norm_num [nextNormalPenaltyUpper,savedCref,uniformQuoteError]
    linarith [hk.2]
  have h := index_weak_order_from_intervals ((0/1)/3) ((0/1)/5) (nextNormalPenalty adverseNextS29Before) 0 (9270177/6250000) (7180649/6250000)
    (treeBonus (7/5) 28 3) (treeBonus (7/5) 28 5)
    (trajectory_bonus_28_3).1 (trajectory_bonus_28_5).2 hm.le
  simpa only [treeIndex] using h

theorem adverseNextS29D0Cmp2 : indexScore (7/5) (controlPenalty savedCref uniformQuoteError unitRoleUnused .next) adverseNextS29Before [] (.query 2) ≤ indexScore (7/5) (controlPenalty savedCref uniformQuoteError unitRoleUnused .next) adverseNextS29Before [] (.query 0) := by
  rw [adverseNextS29D0I2,adverseNextS29D0I0]

theorem adverseNextS29D0Cmp3 : indexScore (7/5) (controlPenalty savedCref uniformQuoteError unitRoleUnused .next) adverseNextS29Before [] (.query 3) ≤ indexScore (7/5) (controlPenalty savedCref uniformQuoteError unitRoleUnused .next) adverseNextS29Before [] (.query 0) := by
  rw [adverseNextS29D0I3,adverseNextS29D0I0]

theorem adverseNextS29D0Cmp4 : indexScore (7/5) (controlPenalty savedCref uniformQuoteError unitRoleUnused .next) adverseNextS29Before [] (.query 4) ≤ indexScore (7/5) (controlPenalty savedCref uniformQuoteError unitRoleUnused .next) adverseNextS29Before [] (.query 0) := by
  rw [adverseNextS29D0I4,adverseNextS29D0I0]

theorem adverseNextS29D0Cmp5 : indexScore (7/5) (controlPenalty savedCref uniformQuoteError unitRoleUnused .next) adverseNextS29Before [] (.query 5) ≤ indexScore (7/5) (controlPenalty savedCref uniformQuoteError unitRoleUnused .next) adverseNextS29Before [] (.query 0) := by
  rw [adverseNextS29D0I5,adverseNextS29D0I0]
  have hk := adverse_next_penalty_interval 28 (by omega)
  change nextNormalPenaltyLower ≤ nextNormalPenalty adverseNextS29Before ∧ nextNormalPenalty adverseNextS29Before ≤ nextNormalPenaltyUpper at hk
  have hm : ((13/10)/5)+(7180649/6250000)-(nextNormalPenalty adverseNextS29Before) < ((0/1)/3)+(9270177/6250000)-(nextNormalPenalty adverseNextS29Before) := by
    have h : (((13/10)/5)+(7180649/6250000) : ℝ) < ((0/1)/3)+(9270177/6250000) := by norm_num
    linarith
  have h := index_weak_order_from_intervals ((0/1)/3) ((13/10)/5) (nextNormalPenalty adverseNextS29Before) (nextNormalPenalty adverseNextS29Before) (9270177/6250000) (7180649/6250000)
    (treeBonus (7/5) 28 3) (treeBonus (7/5) 28 5)
    (trajectory_bonus_28_3).1 (trajectory_bonus_28_5).2 hm.le
  simpa only [treeIndex] using h

theorem adverseNextS29D0Cmp6 : indexScore (7/5) (controlPenalty savedCref uniformQuoteError unitRoleUnused .next) adverseNextS29Before [] (.query 6) ≤ indexScore (7/5) (controlPenalty savedCref uniformQuoteError unitRoleUnused .next) adverseNextS29Before [] (.query 0) := by
  rw [adverseNextS29D0I6,adverseNextS29D0I0]

theorem adverseNextS29D0Cmp7 : indexScore (7/5) (controlPenalty savedCref uniformQuoteError unitRoleUnused .next) adverseNextS29Before [] (.query 7) ≤ indexScore (7/5) (controlPenalty savedCref uniformQuoteError unitRoleUnused .next) adverseNextS29Before [] (.query 0) := by
  rw [adverseNextS29D0I7,adverseNextS29D0I0]

theorem adverseNextS29Choice0 : nativeFirstChoice (indexScore (7/5) (controlPenalty savedCref uniformQuoteError unitRoleUnused .next) adverseNextS29Before []) adverseNextS29Before [] = .query 0 := by
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
    · exact adverseNextS29D0Cmp1
    · exact adverseNextS29D0Cmp2
    · exact adverseNextS29D0Cmp3
    · exact adverseNextS29D0Cmp4
    · exact adverseNextS29D0Cmp5
    · exact adverseNextS29D0Cmp6
    · exact adverseNextS29D0Cmp7

theorem adverseNextS29ActualEvent : nativeEvent budgetTape (7/5) (controlPenalty savedCref uniformQuoteError unitRoleUnused .next)
    (taskReward true (2/5) (1/2)) adverseNextS29Before = adverseNextEvent29 := by
  have hs0 := native_select_existing_step budgetTape (7/5) (controlPenalty savedCref uniformQuoteError unitRoleUnused .next) adverseNextS29Before 8 [] (.query 0)
    (by decide) (by decide) adverseNextS29Choice0
  have hnew := native_select_new_step budgetTape (7/5) (controlPenalty savedCref uniformQuoteError unitRoleUnused .next) adverseNextS29Before 7 [.query 0]
    [.normalRetriever 6,.normalRetriever 7,.normalRetriever 8,.normalRetriever 5,.normalRetriever 1,.normalRetriever 2,.normalRetriever 3,.normalRetriever 12,.normalRetriever 14,.normalRetriever 13,.normalRetriever 21,.normalRetriever 23,.normalRetriever 22,.normalRetriever 9,.normalRetriever 11,.normalRetriever 10,.normalRetriever 15,.normalRetriever 17,.normalRetriever 16,.normalRetriever 18,.normalRetriever 20,.normalRetriever 19,.normalRetriever 24,.normalRetriever 25,.normalRetriever 26,.normalRetriever 27,.normalRetriever 28,.normalRetriever 29] (.normalRetriever 6) (by decide) (by decide) (by decide) (by decide)
  have hs : nativeSelect budgetTape (7/5) (controlPenalty savedCref uniformQuoteError unitRoleUnused .next) adverseNextS29Before 9 [] = [.query 0,.normalRetriever 6] := by
    rw [hs0]
    change nativeSelect budgetTape (7/5) (controlPenalty savedCref uniformQuoteError unitRoleUnused .next) adverseNextS29Before 8 [.query 0] = _
    rw [hnew] <;> rfl
  have hr : repairedRollout budgetTape adverseNextS29Before 9 [.query 0,.normalRetriever 6] = [.query 0,.normalRetriever 6,.selection 0,.width 0,.stop,.reranker 0,.topm 0,.context 0,.answer 0] := by decide
  simp only [nativeEvent,hs,hr]
  rfl

def adverseNextS30Before := adverseNextProposal.take 29

theorem adverseNextS30D0I0 : indexScore (7/5) (controlPenalty savedCref uniformQuoteError unitRoleUnused .next) adverseNextS30Before [] (.query 0) = treeIndex ((0/1)/4) (7/5) (nextNormalPenalty adverseNextS30Before) 29 4 := by
  have hs : replayBackup adverseNextS30Before emptyStatistics ([]++[.query 0]) = ⟨4,(0/1)⟩ := by
    rw [replayBackup_empty_closed_form]
    simp +decide [backedEvents,adverseNextS30Before,adverseNextProposal,adverseNextEvent1,adverseNextEvent2,adverseNextEvent3,adverseNextEvent4,adverseNextEvent5,adverseNextEvent6,adverseNextEvent7,adverseNextEvent8,adverseNextEvent9,adverseNextEvent10,adverseNextEvent11,adverseNextEvent12,adverseNextEvent13,adverseNextEvent14,adverseNextEvent15,adverseNextEvent16,adverseNextEvent17,adverseNextEvent18,adverseNextEvent19,adverseNextEvent20,adverseNextEvent21,adverseNextEvent22,adverseNextEvent23,adverseNextEvent24,adverseNextEvent25,adverseNextEvent26,adverseNextEvent27,adverseNextEvent28,adverseNextEvent29,taskReward]
    <;> norm_num
  have hp : rawVisits adverseNextS30Before [] = 29 := by decide
  have hn : rawVisits adverseNextS30Before ([]++[.query 0]) = 4 := by decide
  have hz : (controlPenalty savedCref uniformQuoteError unitRoleUnused .next) adverseNextS30Before [] (.query 0) = (nextNormalPenalty adverseNextS30Before) := by
    simpa only [adverseNextS30Before,nextNormalPenalty] using AgentUCTNextExact.adverse_next_normal_root_quotes_exact 29 (by omega) 0 (by decide)
  unfold indexScore
  rw [hs,hp,hn,hz]
  simp only [BackupStat.mean]
  norm_num

theorem adverseNextS30D0I1 : indexScore (7/5) (controlPenalty savedCref uniformQuoteError unitRoleUnused .next) adverseNextS30Before [] (.query 1) = treeIndex ((0/1)/5) (7/5) 0 29 5 := by
  have hs : replayBackup adverseNextS30Before emptyStatistics ([]++[.query 1]) = ⟨5,(0/1)⟩ := by
    rw [replayBackup_empty_closed_form]
    simp +decide [backedEvents,adverseNextS30Before,adverseNextProposal,adverseNextEvent1,adverseNextEvent2,adverseNextEvent3,adverseNextEvent4,adverseNextEvent5,adverseNextEvent6,adverseNextEvent7,adverseNextEvent8,adverseNextEvent9,adverseNextEvent10,adverseNextEvent11,adverseNextEvent12,adverseNextEvent13,adverseNextEvent14,adverseNextEvent15,adverseNextEvent16,adverseNextEvent17,adverseNextEvent18,adverseNextEvent19,adverseNextEvent20,adverseNextEvent21,adverseNextEvent22,adverseNextEvent23,adverseNextEvent24,adverseNextEvent25,adverseNextEvent26,adverseNextEvent27,adverseNextEvent28,adverseNextEvent29,taskReward]
    <;> norm_num
  have hp : rawVisits adverseNextS30Before [] = 29 := by decide
  have hn : rawVisits adverseNextS30Before ([]++[.query 1]) = 5 := by decide
  have hz : (controlPenalty savedCref uniformQuoteError unitRoleUnused .next) adverseNextS30Before [] (.query 1) = 0 := by
    apply control_penalty_empty_suffix
    exact AgentUCTNextExact.adverse_next_hyde_root_suffix_empty 29 (by omega)
  unfold indexScore
  rw [hs,hp,hn,hz]
  simp only [BackupStat.mean]
  norm_num

theorem adverseNextS30D0I2 : indexScore (7/5) (controlPenalty savedCref uniformQuoteError unitRoleUnused .next) adverseNextS30Before [] (.query 2) = treeIndex ((0/1)/3) (7/5) (nextNormalPenalty adverseNextS30Before) 29 3 := by
  have hs : replayBackup adverseNextS30Before emptyStatistics ([]++[.query 2]) = ⟨3,(0/1)⟩ := by
    rw [replayBackup_empty_closed_form]
    simp +decide [backedEvents,adverseNextS30Before,adverseNextProposal,adverseNextEvent1,adverseNextEvent2,adverseNextEvent3,adverseNextEvent4,adverseNextEvent5,adverseNextEvent6,adverseNextEvent7,adverseNextEvent8,adverseNextEvent9,adverseNextEvent10,adverseNextEvent11,adverseNextEvent12,adverseNextEvent13,adverseNextEvent14,adverseNextEvent15,adverseNextEvent16,adverseNextEvent17,adverseNextEvent18,adverseNextEvent19,adverseNextEvent20,adverseNextEvent21,adverseNextEvent22,adverseNextEvent23,adverseNextEvent24,adverseNextEvent25,adverseNextEvent26,adverseNextEvent27,adverseNextEvent28,adverseNextEvent29,taskReward]
    <;> norm_num
  have hp : rawVisits adverseNextS30Before [] = 29 := by decide
  have hn : rawVisits adverseNextS30Before ([]++[.query 2]) = 3 := by decide
  have hz : (controlPenalty savedCref uniformQuoteError unitRoleUnused .next) adverseNextS30Before [] (.query 2) = (nextNormalPenalty adverseNextS30Before) := by
    simpa only [adverseNextS30Before,nextNormalPenalty] using AgentUCTNextExact.adverse_next_normal_root_quotes_exact 29 (by omega) 2 (by decide)
  unfold indexScore
  rw [hs,hp,hn,hz]
  simp only [BackupStat.mean]
  norm_num

theorem adverseNextS30D0I3 : indexScore (7/5) (controlPenalty savedCref uniformQuoteError unitRoleUnused .next) adverseNextS30Before [] (.query 3) = treeIndex ((0/1)/3) (7/5) (nextNormalPenalty adverseNextS30Before) 29 3 := by
  have hs : replayBackup adverseNextS30Before emptyStatistics ([]++[.query 3]) = ⟨3,(0/1)⟩ := by
    rw [replayBackup_empty_closed_form]
    simp +decide [backedEvents,adverseNextS30Before,adverseNextProposal,adverseNextEvent1,adverseNextEvent2,adverseNextEvent3,adverseNextEvent4,adverseNextEvent5,adverseNextEvent6,adverseNextEvent7,adverseNextEvent8,adverseNextEvent9,adverseNextEvent10,adverseNextEvent11,adverseNextEvent12,adverseNextEvent13,adverseNextEvent14,adverseNextEvent15,adverseNextEvent16,adverseNextEvent17,adverseNextEvent18,adverseNextEvent19,adverseNextEvent20,adverseNextEvent21,adverseNextEvent22,adverseNextEvent23,adverseNextEvent24,adverseNextEvent25,adverseNextEvent26,adverseNextEvent27,adverseNextEvent28,adverseNextEvent29,taskReward]
    <;> norm_num
  have hp : rawVisits adverseNextS30Before [] = 29 := by decide
  have hn : rawVisits adverseNextS30Before ([]++[.query 3]) = 3 := by decide
  have hz : (controlPenalty savedCref uniformQuoteError unitRoleUnused .next) adverseNextS30Before [] (.query 3) = (nextNormalPenalty adverseNextS30Before) := by
    simpa only [adverseNextS30Before,nextNormalPenalty] using AgentUCTNextExact.adverse_next_normal_root_quotes_exact 29 (by omega) 3 (by decide)
  unfold indexScore
  rw [hs,hp,hn,hz]
  simp only [BackupStat.mean]
  norm_num

theorem adverseNextS30D0I4 : indexScore (7/5) (controlPenalty savedCref uniformQuoteError unitRoleUnused .next) adverseNextS30Before [] (.query 4) = treeIndex ((0/1)/3) (7/5) (nextNormalPenalty adverseNextS30Before) 29 3 := by
  have hs : replayBackup adverseNextS30Before emptyStatistics ([]++[.query 4]) = ⟨3,(0/1)⟩ := by
    rw [replayBackup_empty_closed_form]
    simp +decide [backedEvents,adverseNextS30Before,adverseNextProposal,adverseNextEvent1,adverseNextEvent2,adverseNextEvent3,adverseNextEvent4,adverseNextEvent5,adverseNextEvent6,adverseNextEvent7,adverseNextEvent8,adverseNextEvent9,adverseNextEvent10,adverseNextEvent11,adverseNextEvent12,adverseNextEvent13,adverseNextEvent14,adverseNextEvent15,adverseNextEvent16,adverseNextEvent17,adverseNextEvent18,adverseNextEvent19,adverseNextEvent20,adverseNextEvent21,adverseNextEvent22,adverseNextEvent23,adverseNextEvent24,adverseNextEvent25,adverseNextEvent26,adverseNextEvent27,adverseNextEvent28,adverseNextEvent29,taskReward]
    <;> norm_num
  have hp : rawVisits adverseNextS30Before [] = 29 := by decide
  have hn : rawVisits adverseNextS30Before ([]++[.query 4]) = 3 := by decide
  have hz : (controlPenalty savedCref uniformQuoteError unitRoleUnused .next) adverseNextS30Before [] (.query 4) = (nextNormalPenalty adverseNextS30Before) := by
    simpa only [adverseNextS30Before,nextNormalPenalty] using AgentUCTNextExact.adverse_next_normal_root_quotes_exact 29 (by omega) 4 (by decide)
  unfold indexScore
  rw [hs,hp,hn,hz]
  simp only [BackupStat.mean]
  norm_num

theorem adverseNextS30D0I5 : indexScore (7/5) (controlPenalty savedCref uniformQuoteError unitRoleUnused .next) adverseNextS30Before [] (.query 5) = treeIndex ((13/10)/5) (7/5) (nextNormalPenalty adverseNextS30Before) 29 5 := by
  have hs : replayBackup adverseNextS30Before emptyStatistics ([]++[.query 5]) = ⟨5,(13/10)⟩ := by
    rw [replayBackup_empty_closed_form]
    simp +decide [backedEvents,adverseNextS30Before,adverseNextProposal,adverseNextEvent1,adverseNextEvent2,adverseNextEvent3,adverseNextEvent4,adverseNextEvent5,adverseNextEvent6,adverseNextEvent7,adverseNextEvent8,adverseNextEvent9,adverseNextEvent10,adverseNextEvent11,adverseNextEvent12,adverseNextEvent13,adverseNextEvent14,adverseNextEvent15,adverseNextEvent16,adverseNextEvent17,adverseNextEvent18,adverseNextEvent19,adverseNextEvent20,adverseNextEvent21,adverseNextEvent22,adverseNextEvent23,adverseNextEvent24,adverseNextEvent25,adverseNextEvent26,adverseNextEvent27,adverseNextEvent28,adverseNextEvent29,taskReward]
    <;> norm_num
  have hp : rawVisits adverseNextS30Before [] = 29 := by decide
  have hn : rawVisits adverseNextS30Before ([]++[.query 5]) = 5 := by decide
  have hz : (controlPenalty savedCref uniformQuoteError unitRoleUnused .next) adverseNextS30Before [] (.query 5) = (nextNormalPenalty adverseNextS30Before) := by
    simpa only [adverseNextS30Before,nextNormalPenalty] using AgentUCTNextExact.adverse_next_normal_root_quotes_exact 29 (by omega) 5 (by decide)
  unfold indexScore
  rw [hs,hp,hn,hz]
  simp only [BackupStat.mean]
  norm_num

theorem adverseNextS30D0I6 : indexScore (7/5) (controlPenalty savedCref uniformQuoteError unitRoleUnused .next) adverseNextS30Before [] (.query 6) = treeIndex ((0/1)/3) (7/5) (nextNormalPenalty adverseNextS30Before) 29 3 := by
  have hs : replayBackup adverseNextS30Before emptyStatistics ([]++[.query 6]) = ⟨3,(0/1)⟩ := by
    rw [replayBackup_empty_closed_form]
    simp +decide [backedEvents,adverseNextS30Before,adverseNextProposal,adverseNextEvent1,adverseNextEvent2,adverseNextEvent3,adverseNextEvent4,adverseNextEvent5,adverseNextEvent6,adverseNextEvent7,adverseNextEvent8,adverseNextEvent9,adverseNextEvent10,adverseNextEvent11,adverseNextEvent12,adverseNextEvent13,adverseNextEvent14,adverseNextEvent15,adverseNextEvent16,adverseNextEvent17,adverseNextEvent18,adverseNextEvent19,adverseNextEvent20,adverseNextEvent21,adverseNextEvent22,adverseNextEvent23,adverseNextEvent24,adverseNextEvent25,adverseNextEvent26,adverseNextEvent27,adverseNextEvent28,adverseNextEvent29,taskReward]
    <;> norm_num
  have hp : rawVisits adverseNextS30Before [] = 29 := by decide
  have hn : rawVisits adverseNextS30Before ([]++[.query 6]) = 3 := by decide
  have hz : (controlPenalty savedCref uniformQuoteError unitRoleUnused .next) adverseNextS30Before [] (.query 6) = (nextNormalPenalty adverseNextS30Before) := by
    simpa only [adverseNextS30Before,nextNormalPenalty] using AgentUCTNextExact.adverse_next_normal_root_quotes_exact 29 (by omega) 6 (by decide)
  unfold indexScore
  rw [hs,hp,hn,hz]
  simp only [BackupStat.mean]
  norm_num

theorem adverseNextS30D0I7 : indexScore (7/5) (controlPenalty savedCref uniformQuoteError unitRoleUnused .next) adverseNextS30Before [] (.query 7) = treeIndex ((0/1)/3) (7/5) (nextNormalPenalty adverseNextS30Before) 29 3 := by
  have hs : replayBackup adverseNextS30Before emptyStatistics ([]++[.query 7]) = ⟨3,(0/1)⟩ := by
    rw [replayBackup_empty_closed_form]
    simp +decide [backedEvents,adverseNextS30Before,adverseNextProposal,adverseNextEvent1,adverseNextEvent2,adverseNextEvent3,adverseNextEvent4,adverseNextEvent5,adverseNextEvent6,adverseNextEvent7,adverseNextEvent8,adverseNextEvent9,adverseNextEvent10,adverseNextEvent11,adverseNextEvent12,adverseNextEvent13,adverseNextEvent14,adverseNextEvent15,adverseNextEvent16,adverseNextEvent17,adverseNextEvent18,adverseNextEvent19,adverseNextEvent20,adverseNextEvent21,adverseNextEvent22,adverseNextEvent23,adverseNextEvent24,adverseNextEvent25,adverseNextEvent26,adverseNextEvent27,adverseNextEvent28,adverseNextEvent29,taskReward]
    <;> norm_num
  have hp : rawVisits adverseNextS30Before [] = 29 := by decide
  have hn : rawVisits adverseNextS30Before ([]++[.query 7]) = 3 := by decide
  have hz : (controlPenalty savedCref uniformQuoteError unitRoleUnused .next) adverseNextS30Before [] (.query 7) = (nextNormalPenalty adverseNextS30Before) := by
    simpa only [adverseNextS30Before,nextNormalPenalty] using AgentUCTNextExact.adverse_next_normal_root_quotes_exact 29 (by omega) 7 (by decide)
  unfold indexScore
  rw [hs,hp,hn,hz]
  simp only [BackupStat.mean]
  norm_num

theorem adverseNextS30D0Cmp0 : indexScore (7/5) (controlPenalty savedCref uniformQuoteError unitRoleUnused .next) adverseNextS30Before [] (.query 0) < indexScore (7/5) (controlPenalty savedCref uniformQuoteError unitRoleUnused .next) adverseNextS30Before [] (.query 2) := by
  rw [adverseNextS30D0I0,adverseNextS30D0I2]
  have hk := adverse_next_penalty_interval 29 (by omega)
  change nextNormalPenaltyLower ≤ nextNormalPenalty adverseNextS30Before ∧ nextNormalPenalty adverseNextS30Before ≤ nextNormalPenaltyUpper at hk
  have hm : ((0/1)/4)+(4034261/3125000)-(nextNormalPenalty adverseNextS30Before) < ((0/1)/3)+(74533809/50000000)-(nextNormalPenalty adverseNextS30Before) := by
    have h : (((0/1)/4)+(4034261/3125000) : ℝ) < ((0/1)/3)+(74533809/50000000) := by norm_num
    linarith
  have h := index_strict_order_from_intervals ((0/1)/3) ((0/1)/4) (nextNormalPenalty adverseNextS30Before) (nextNormalPenalty adverseNextS30Before) (74533809/50000000) (4034261/3125000)
    (treeBonus (7/5) 29 3) (treeBonus (7/5) 29 4)
    (trajectory_bonus_29_3).1 (trajectory_bonus_29_4).2 hm
  simpa only [treeIndex] using h

theorem adverseNextS30D0Cmp1 : indexScore (7/5) (controlPenalty savedCref uniformQuoteError unitRoleUnused .next) adverseNextS30Before [] (.query 1) < indexScore (7/5) (controlPenalty savedCref uniformQuoteError unitRoleUnused .next) adverseNextS30Before [] (.query 2) := by
  rw [adverseNextS30D0I1,adverseNextS30D0I2]
  have hk := adverse_next_penalty_interval 29 (by omega)
  change nextNormalPenaltyLower ≤ nextNormalPenalty adverseNextS30Before ∧ nextNormalPenalty adverseNextS30Before ≤ nextNormalPenaltyUpper at hk
  have hm : ((0/1)/5)+(3608353/3125000)-0 < ((0/1)/3)+(74533809/50000000)-(nextNormalPenalty adverseNextS30Before) := by
    have h : ((0/1)/5)+(3608353/3125000) < ((0/1)/3)+(74533809/50000000)-nextNormalPenaltyUpper := by norm_num [nextNormalPenaltyUpper,savedCref,uniformQuoteError]
    linarith [hk.2]
  have h := index_strict_order_from_intervals ((0/1)/3) ((0/1)/5) (nextNormalPenalty adverseNextS30Before) 0 (74533809/50000000) (3608353/3125000)
    (treeBonus (7/5) 29 3) (treeBonus (7/5) 29 5)
    (trajectory_bonus_29_3).1 (trajectory_bonus_29_5).2 hm
  simpa only [treeIndex] using h

theorem adverseNextS30D0Cmp3 : indexScore (7/5) (controlPenalty savedCref uniformQuoteError unitRoleUnused .next) adverseNextS30Before [] (.query 3) ≤ indexScore (7/5) (controlPenalty savedCref uniformQuoteError unitRoleUnused .next) adverseNextS30Before [] (.query 2) := by
  rw [adverseNextS30D0I3,adverseNextS30D0I2]

theorem adverseNextS30D0Cmp4 : indexScore (7/5) (controlPenalty savedCref uniformQuoteError unitRoleUnused .next) adverseNextS30Before [] (.query 4) ≤ indexScore (7/5) (controlPenalty savedCref uniformQuoteError unitRoleUnused .next) adverseNextS30Before [] (.query 2) := by
  rw [adverseNextS30D0I4,adverseNextS30D0I2]

theorem adverseNextS30D0Cmp5 : indexScore (7/5) (controlPenalty savedCref uniformQuoteError unitRoleUnused .next) adverseNextS30Before [] (.query 5) ≤ indexScore (7/5) (controlPenalty savedCref uniformQuoteError unitRoleUnused .next) adverseNextS30Before [] (.query 2) := by
  rw [adverseNextS30D0I5,adverseNextS30D0I2]
  have hk := adverse_next_penalty_interval 29 (by omega)
  change nextNormalPenaltyLower ≤ nextNormalPenalty adverseNextS30Before ∧ nextNormalPenalty adverseNextS30Before ≤ nextNormalPenaltyUpper at hk
  have hm : ((13/10)/5)+(3608353/3125000)-(nextNormalPenalty adverseNextS30Before) < ((0/1)/3)+(74533809/50000000)-(nextNormalPenalty adverseNextS30Before) := by
    have h : (((13/10)/5)+(3608353/3125000) : ℝ) < ((0/1)/3)+(74533809/50000000) := by norm_num
    linarith
  have h := index_weak_order_from_intervals ((0/1)/3) ((13/10)/5) (nextNormalPenalty adverseNextS30Before) (nextNormalPenalty adverseNextS30Before) (74533809/50000000) (3608353/3125000)
    (treeBonus (7/5) 29 3) (treeBonus (7/5) 29 5)
    (trajectory_bonus_29_3).1 (trajectory_bonus_29_5).2 hm.le
  simpa only [treeIndex] using h

theorem adverseNextS30D0Cmp6 : indexScore (7/5) (controlPenalty savedCref uniformQuoteError unitRoleUnused .next) adverseNextS30Before [] (.query 6) ≤ indexScore (7/5) (controlPenalty savedCref uniformQuoteError unitRoleUnused .next) adverseNextS30Before [] (.query 2) := by
  rw [adverseNextS30D0I6,adverseNextS30D0I2]

theorem adverseNextS30D0Cmp7 : indexScore (7/5) (controlPenalty savedCref uniformQuoteError unitRoleUnused .next) adverseNextS30Before [] (.query 7) ≤ indexScore (7/5) (controlPenalty savedCref uniformQuoteError unitRoleUnused .next) adverseNextS30Before [] (.query 2) := by
  rw [adverseNextS30D0I7,adverseNextS30D0I2]

theorem adverseNextS30Choice0 : nativeFirstChoice (indexScore (7/5) (controlPenalty savedCref uniformQuoteError unitRoleUnused .next) adverseNextS30Before []) adverseNextS30Before [] = .query 2 := by
  apply visited_choice_from_ordered_certificate _ _ [] [.query 0,.query 1] [.query 3,.query 4,.query 5,.query 6,.query 7] (.query 2) (by decide)
  · intro a ha
    have ho : orderedLegalAvailable [] = [.query 0,.query 1,.query 2,.query 3,.query 4,.query 5,.query 6,.query 7] := by decide
    rw [ho] at ha
    simp only [List.mem_cons,List.not_mem_nil,or_false] at ha
    rcases ha with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> decide
  · intro a ha
    simp only [List.mem_cons,List.not_mem_nil,or_false] at ha
    rcases ha with rfl | rfl
    · exact adverseNextS30D0Cmp0
    · exact adverseNextS30D0Cmp1
  · intro a ha
    simp only [List.mem_cons,List.not_mem_nil,or_false] at ha
    rcases ha with rfl | rfl | rfl | rfl | rfl
    · exact adverseNextS30D0Cmp3
    · exact adverseNextS30D0Cmp4
    · exact adverseNextS30D0Cmp5
    · exact adverseNextS30D0Cmp6
    · exact adverseNextS30D0Cmp7

theorem adverseNextS30ActualEvent : nativeEvent budgetTape (7/5) (controlPenalty savedCref uniformQuoteError unitRoleUnused .next)
    (taskReward true (2/5) (1/2)) adverseNextS30Before = adverseNextEvent30 := by
  have hs0 := native_select_existing_step budgetTape (7/5) (controlPenalty savedCref uniformQuoteError unitRoleUnused .next) adverseNextS30Before 8 [] (.query 2)
    (by decide) (by decide) adverseNextS30Choice0
  have hnew := native_select_new_step budgetTape (7/5) (controlPenalty savedCref uniformQuoteError unitRoleUnused .next) adverseNextS30Before 7 [.query 2]
    [.normalRetriever 6,.normalRetriever 7,.normalRetriever 8,.normalRetriever 5,.normalRetriever 1,.normalRetriever 2,.normalRetriever 3,.normalRetriever 12,.normalRetriever 14,.normalRetriever 13,.normalRetriever 21,.normalRetriever 23,.normalRetriever 22,.normalRetriever 9,.normalRetriever 11,.normalRetriever 10,.normalRetriever 15,.normalRetriever 17,.normalRetriever 16,.normalRetriever 18,.normalRetriever 20,.normalRetriever 19,.normalRetriever 24,.normalRetriever 25,.normalRetriever 26,.normalRetriever 27,.normalRetriever 28,.normalRetriever 29] (.normalRetriever 6) (by decide) (by decide) (by decide) (by decide)
  have hs : nativeSelect budgetTape (7/5) (controlPenalty savedCref uniformQuoteError unitRoleUnused .next) adverseNextS30Before 9 [] = [.query 2,.normalRetriever 6] := by
    rw [hs0]
    change nativeSelect budgetTape (7/5) (controlPenalty savedCref uniformQuoteError unitRoleUnused .next) adverseNextS30Before 8 [.query 2] = _
    rw [hnew] <;> rfl
  have hr : repairedRollout budgetTape adverseNextS30Before 9 [.query 2,.normalRetriever 6] = [.query 2,.normalRetriever 6,.selection 0,.width 0,.stop,.reranker 0,.topm 0,.context 0,.answer 0] := by decide
  simp only [nativeEvent,hs,hr]
  rfl

def adverseNextS31Before := adverseNextProposal.take 30

theorem adverseNextS31D0I0 : indexScore (7/5) (controlPenalty savedCref uniformQuoteError unitRoleUnused .next) adverseNextS31Before [] (.query 0) = treeIndex ((0/1)/4) (7/5) (nextNormalPenalty adverseNextS31Before) 30 4 := by
  have hs : replayBackup adverseNextS31Before emptyStatistics ([]++[.query 0]) = ⟨4,(0/1)⟩ := by
    rw [replayBackup_empty_closed_form]
    simp +decide [backedEvents,adverseNextS31Before,adverseNextProposal,adverseNextEvent1,adverseNextEvent2,adverseNextEvent3,adverseNextEvent4,adverseNextEvent5,adverseNextEvent6,adverseNextEvent7,adverseNextEvent8,adverseNextEvent9,adverseNextEvent10,adverseNextEvent11,adverseNextEvent12,adverseNextEvent13,adverseNextEvent14,adverseNextEvent15,adverseNextEvent16,adverseNextEvent17,adverseNextEvent18,adverseNextEvent19,adverseNextEvent20,adverseNextEvent21,adverseNextEvent22,adverseNextEvent23,adverseNextEvent24,adverseNextEvent25,adverseNextEvent26,adverseNextEvent27,adverseNextEvent28,adverseNextEvent29,adverseNextEvent30,taskReward]
    <;> norm_num
  have hp : rawVisits adverseNextS31Before [] = 30 := by decide
  have hn : rawVisits adverseNextS31Before ([]++[.query 0]) = 4 := by decide
  have hz : (controlPenalty savedCref uniformQuoteError unitRoleUnused .next) adverseNextS31Before [] (.query 0) = (nextNormalPenalty adverseNextS31Before) := by
    simpa only [adverseNextS31Before,nextNormalPenalty] using AgentUCTNextExact.adverse_next_normal_root_quotes_exact 30 (by omega) 0 (by decide)
  unfold indexScore
  rw [hs,hp,hn,hz]
  simp only [BackupStat.mean]
  norm_num

theorem adverseNextS31D0I1 : indexScore (7/5) (controlPenalty savedCref uniformQuoteError unitRoleUnused .next) adverseNextS31Before [] (.query 1) = treeIndex ((0/1)/5) (7/5) 0 30 5 := by
  have hs : replayBackup adverseNextS31Before emptyStatistics ([]++[.query 1]) = ⟨5,(0/1)⟩ := by
    rw [replayBackup_empty_closed_form]
    simp +decide [backedEvents,adverseNextS31Before,adverseNextProposal,adverseNextEvent1,adverseNextEvent2,adverseNextEvent3,adverseNextEvent4,adverseNextEvent5,adverseNextEvent6,adverseNextEvent7,adverseNextEvent8,adverseNextEvent9,adverseNextEvent10,adverseNextEvent11,adverseNextEvent12,adverseNextEvent13,adverseNextEvent14,adverseNextEvent15,adverseNextEvent16,adverseNextEvent17,adverseNextEvent18,adverseNextEvent19,adverseNextEvent20,adverseNextEvent21,adverseNextEvent22,adverseNextEvent23,adverseNextEvent24,adverseNextEvent25,adverseNextEvent26,adverseNextEvent27,adverseNextEvent28,adverseNextEvent29,adverseNextEvent30,taskReward]
    <;> norm_num
  have hp : rawVisits adverseNextS31Before [] = 30 := by decide
  have hn : rawVisits adverseNextS31Before ([]++[.query 1]) = 5 := by decide
  have hz : (controlPenalty savedCref uniformQuoteError unitRoleUnused .next) adverseNextS31Before [] (.query 1) = 0 := by
    apply control_penalty_empty_suffix
    exact AgentUCTNextExact.adverse_next_hyde_root_suffix_empty 30 (by omega)
  unfold indexScore
  rw [hs,hp,hn,hz]
  simp only [BackupStat.mean]
  norm_num

theorem adverseNextS31D0I2 : indexScore (7/5) (controlPenalty savedCref uniformQuoteError unitRoleUnused .next) adverseNextS31Before [] (.query 2) = treeIndex ((0/1)/4) (7/5) (nextNormalPenalty adverseNextS31Before) 30 4 := by
  have hs : replayBackup adverseNextS31Before emptyStatistics ([]++[.query 2]) = ⟨4,(0/1)⟩ := by
    rw [replayBackup_empty_closed_form]
    simp +decide [backedEvents,adverseNextS31Before,adverseNextProposal,adverseNextEvent1,adverseNextEvent2,adverseNextEvent3,adverseNextEvent4,adverseNextEvent5,adverseNextEvent6,adverseNextEvent7,adverseNextEvent8,adverseNextEvent9,adverseNextEvent10,adverseNextEvent11,adverseNextEvent12,adverseNextEvent13,adverseNextEvent14,adverseNextEvent15,adverseNextEvent16,adverseNextEvent17,adverseNextEvent18,adverseNextEvent19,adverseNextEvent20,adverseNextEvent21,adverseNextEvent22,adverseNextEvent23,adverseNextEvent24,adverseNextEvent25,adverseNextEvent26,adverseNextEvent27,adverseNextEvent28,adverseNextEvent29,adverseNextEvent30,taskReward]
    <;> norm_num
  have hp : rawVisits adverseNextS31Before [] = 30 := by decide
  have hn : rawVisits adverseNextS31Before ([]++[.query 2]) = 4 := by decide
  have hz : (controlPenalty savedCref uniformQuoteError unitRoleUnused .next) adverseNextS31Before [] (.query 2) = (nextNormalPenalty adverseNextS31Before) := by
    simpa only [adverseNextS31Before,nextNormalPenalty] using AgentUCTNextExact.adverse_next_normal_root_quotes_exact 30 (by omega) 2 (by decide)
  unfold indexScore
  rw [hs,hp,hn,hz]
  simp only [BackupStat.mean]
  norm_num

theorem adverseNextS31D0I3 : indexScore (7/5) (controlPenalty savedCref uniformQuoteError unitRoleUnused .next) adverseNextS31Before [] (.query 3) = treeIndex ((0/1)/3) (7/5) (nextNormalPenalty adverseNextS31Before) 30 3 := by
  have hs : replayBackup adverseNextS31Before emptyStatistics ([]++[.query 3]) = ⟨3,(0/1)⟩ := by
    rw [replayBackup_empty_closed_form]
    simp +decide [backedEvents,adverseNextS31Before,adverseNextProposal,adverseNextEvent1,adverseNextEvent2,adverseNextEvent3,adverseNextEvent4,adverseNextEvent5,adverseNextEvent6,adverseNextEvent7,adverseNextEvent8,adverseNextEvent9,adverseNextEvent10,adverseNextEvent11,adverseNextEvent12,adverseNextEvent13,adverseNextEvent14,adverseNextEvent15,adverseNextEvent16,adverseNextEvent17,adverseNextEvent18,adverseNextEvent19,adverseNextEvent20,adverseNextEvent21,adverseNextEvent22,adverseNextEvent23,adverseNextEvent24,adverseNextEvent25,adverseNextEvent26,adverseNextEvent27,adverseNextEvent28,adverseNextEvent29,adverseNextEvent30,taskReward]
    <;> norm_num
  have hp : rawVisits adverseNextS31Before [] = 30 := by decide
  have hn : rawVisits adverseNextS31Before ([]++[.query 3]) = 3 := by decide
  have hz : (controlPenalty savedCref uniformQuoteError unitRoleUnused .next) adverseNextS31Before [] (.query 3) = (nextNormalPenalty adverseNextS31Before) := by
    simpa only [adverseNextS31Before,nextNormalPenalty] using AgentUCTNextExact.adverse_next_normal_root_quotes_exact 30 (by omega) 3 (by decide)
  unfold indexScore
  rw [hs,hp,hn,hz]
  simp only [BackupStat.mean]
  norm_num

theorem adverseNextS31D0I4 : indexScore (7/5) (controlPenalty savedCref uniformQuoteError unitRoleUnused .next) adverseNextS31Before [] (.query 4) = treeIndex ((0/1)/3) (7/5) (nextNormalPenalty adverseNextS31Before) 30 3 := by
  have hs : replayBackup adverseNextS31Before emptyStatistics ([]++[.query 4]) = ⟨3,(0/1)⟩ := by
    rw [replayBackup_empty_closed_form]
    simp +decide [backedEvents,adverseNextS31Before,adverseNextProposal,adverseNextEvent1,adverseNextEvent2,adverseNextEvent3,adverseNextEvent4,adverseNextEvent5,adverseNextEvent6,adverseNextEvent7,adverseNextEvent8,adverseNextEvent9,adverseNextEvent10,adverseNextEvent11,adverseNextEvent12,adverseNextEvent13,adverseNextEvent14,adverseNextEvent15,adverseNextEvent16,adverseNextEvent17,adverseNextEvent18,adverseNextEvent19,adverseNextEvent20,adverseNextEvent21,adverseNextEvent22,adverseNextEvent23,adverseNextEvent24,adverseNextEvent25,adverseNextEvent26,adverseNextEvent27,adverseNextEvent28,adverseNextEvent29,adverseNextEvent30,taskReward]
    <;> norm_num
  have hp : rawVisits adverseNextS31Before [] = 30 := by decide
  have hn : rawVisits adverseNextS31Before ([]++[.query 4]) = 3 := by decide
  have hz : (controlPenalty savedCref uniformQuoteError unitRoleUnused .next) adverseNextS31Before [] (.query 4) = (nextNormalPenalty adverseNextS31Before) := by
    simpa only [adverseNextS31Before,nextNormalPenalty] using AgentUCTNextExact.adverse_next_normal_root_quotes_exact 30 (by omega) 4 (by decide)
  unfold indexScore
  rw [hs,hp,hn,hz]
  simp only [BackupStat.mean]
  norm_num

theorem adverseNextS31D0I5 : indexScore (7/5) (controlPenalty savedCref uniformQuoteError unitRoleUnused .next) adverseNextS31Before [] (.query 5) = treeIndex ((13/10)/5) (7/5) (nextNormalPenalty adverseNextS31Before) 30 5 := by
  have hs : replayBackup adverseNextS31Before emptyStatistics ([]++[.query 5]) = ⟨5,(13/10)⟩ := by
    rw [replayBackup_empty_closed_form]
    simp +decide [backedEvents,adverseNextS31Before,adverseNextProposal,adverseNextEvent1,adverseNextEvent2,adverseNextEvent3,adverseNextEvent4,adverseNextEvent5,adverseNextEvent6,adverseNextEvent7,adverseNextEvent8,adverseNextEvent9,adverseNextEvent10,adverseNextEvent11,adverseNextEvent12,adverseNextEvent13,adverseNextEvent14,adverseNextEvent15,adverseNextEvent16,adverseNextEvent17,adverseNextEvent18,adverseNextEvent19,adverseNextEvent20,adverseNextEvent21,adverseNextEvent22,adverseNextEvent23,adverseNextEvent24,adverseNextEvent25,adverseNextEvent26,adverseNextEvent27,adverseNextEvent28,adverseNextEvent29,adverseNextEvent30,taskReward]
    <;> norm_num
  have hp : rawVisits adverseNextS31Before [] = 30 := by decide
  have hn : rawVisits adverseNextS31Before ([]++[.query 5]) = 5 := by decide
  have hz : (controlPenalty savedCref uniformQuoteError unitRoleUnused .next) adverseNextS31Before [] (.query 5) = (nextNormalPenalty adverseNextS31Before) := by
    simpa only [adverseNextS31Before,nextNormalPenalty] using AgentUCTNextExact.adverse_next_normal_root_quotes_exact 30 (by omega) 5 (by decide)
  unfold indexScore
  rw [hs,hp,hn,hz]
  simp only [BackupStat.mean]
  norm_num

theorem adverseNextS31D0I6 : indexScore (7/5) (controlPenalty savedCref uniformQuoteError unitRoleUnused .next) adverseNextS31Before [] (.query 6) = treeIndex ((0/1)/3) (7/5) (nextNormalPenalty adverseNextS31Before) 30 3 := by
  have hs : replayBackup adverseNextS31Before emptyStatistics ([]++[.query 6]) = ⟨3,(0/1)⟩ := by
    rw [replayBackup_empty_closed_form]
    simp +decide [backedEvents,adverseNextS31Before,adverseNextProposal,adverseNextEvent1,adverseNextEvent2,adverseNextEvent3,adverseNextEvent4,adverseNextEvent5,adverseNextEvent6,adverseNextEvent7,adverseNextEvent8,adverseNextEvent9,adverseNextEvent10,adverseNextEvent11,adverseNextEvent12,adverseNextEvent13,adverseNextEvent14,adverseNextEvent15,adverseNextEvent16,adverseNextEvent17,adverseNextEvent18,adverseNextEvent19,adverseNextEvent20,adverseNextEvent21,adverseNextEvent22,adverseNextEvent23,adverseNextEvent24,adverseNextEvent25,adverseNextEvent26,adverseNextEvent27,adverseNextEvent28,adverseNextEvent29,adverseNextEvent30,taskReward]
    <;> norm_num
  have hp : rawVisits adverseNextS31Before [] = 30 := by decide
  have hn : rawVisits adverseNextS31Before ([]++[.query 6]) = 3 := by decide
  have hz : (controlPenalty savedCref uniformQuoteError unitRoleUnused .next) adverseNextS31Before [] (.query 6) = (nextNormalPenalty adverseNextS31Before) := by
    simpa only [adverseNextS31Before,nextNormalPenalty] using AgentUCTNextExact.adverse_next_normal_root_quotes_exact 30 (by omega) 6 (by decide)
  unfold indexScore
  rw [hs,hp,hn,hz]
  simp only [BackupStat.mean]
  norm_num

theorem adverseNextS31D0I7 : indexScore (7/5) (controlPenalty savedCref uniformQuoteError unitRoleUnused .next) adverseNextS31Before [] (.query 7) = treeIndex ((0/1)/3) (7/5) (nextNormalPenalty adverseNextS31Before) 30 3 := by
  have hs : replayBackup adverseNextS31Before emptyStatistics ([]++[.query 7]) = ⟨3,(0/1)⟩ := by
    rw [replayBackup_empty_closed_form]
    simp +decide [backedEvents,adverseNextS31Before,adverseNextProposal,adverseNextEvent1,adverseNextEvent2,adverseNextEvent3,adverseNextEvent4,adverseNextEvent5,adverseNextEvent6,adverseNextEvent7,adverseNextEvent8,adverseNextEvent9,adverseNextEvent10,adverseNextEvent11,adverseNextEvent12,adverseNextEvent13,adverseNextEvent14,adverseNextEvent15,adverseNextEvent16,adverseNextEvent17,adverseNextEvent18,adverseNextEvent19,adverseNextEvent20,adverseNextEvent21,adverseNextEvent22,adverseNextEvent23,adverseNextEvent24,adverseNextEvent25,adverseNextEvent26,adverseNextEvent27,adverseNextEvent28,adverseNextEvent29,adverseNextEvent30,taskReward]
    <;> norm_num
  have hp : rawVisits adverseNextS31Before [] = 30 := by decide
  have hn : rawVisits adverseNextS31Before ([]++[.query 7]) = 3 := by decide
  have hz : (controlPenalty savedCref uniformQuoteError unitRoleUnused .next) adverseNextS31Before [] (.query 7) = (nextNormalPenalty adverseNextS31Before) := by
    simpa only [adverseNextS31Before,nextNormalPenalty] using AgentUCTNextExact.adverse_next_normal_root_quotes_exact 30 (by omega) 7 (by decide)
  unfold indexScore
  rw [hs,hp,hn,hz]
  simp only [BackupStat.mean]
  norm_num

theorem adverseNextS31D0Cmp0 : indexScore (7/5) (controlPenalty savedCref uniformQuoteError unitRoleUnused .next) adverseNextS31Before [] (.query 0) < indexScore (7/5) (controlPenalty savedCref uniformQuoteError unitRoleUnused .next) adverseNextS31Before [] (.query 3) := by
  rw [adverseNextS31D0I0,adverseNextS31D0I3]
  have hk := adverse_next_penalty_interval 30 (by omega)
  change nextNormalPenaltyLower ≤ nextNormalPenalty adverseNextS31Before ∧ nextNormalPenalty adverseNextS31Before ≤ nextNormalPenaltyUpper at hk
  have hm : ((0/1)/4)+(64858577/50000000)-(nextNormalPenalty adverseNextS31Before) < ((0/1)/3)+(74892223/50000000)-(nextNormalPenalty adverseNextS31Before) := by
    have h : (((0/1)/4)+(64858577/50000000) : ℝ) < ((0/1)/3)+(74892223/50000000) := by norm_num
    linarith
  have h := index_strict_order_from_intervals ((0/1)/3) ((0/1)/4) (nextNormalPenalty adverseNextS31Before) (nextNormalPenalty adverseNextS31Before) (74892223/50000000) (64858577/50000000)
    (treeBonus (7/5) 30 3) (treeBonus (7/5) 30 4)
    (trajectory_bonus_30_3).1 (trajectory_bonus_30_4).2 hm
  simpa only [treeIndex] using h

theorem adverseNextS31D0Cmp1 : indexScore (7/5) (controlPenalty savedCref uniformQuoteError unitRoleUnused .next) adverseNextS31Before [] (.query 1) < indexScore (7/5) (controlPenalty savedCref uniformQuoteError unitRoleUnused .next) adverseNextS31Before [] (.query 3) := by
  rw [adverseNextS31D0I1,adverseNextS31D0I3]
  have hk := adverse_next_penalty_interval 30 (by omega)
  change nextNormalPenaltyLower ≤ nextNormalPenalty adverseNextS31Before ∧ nextNormalPenalty adverseNextS31Before ≤ nextNormalPenaltyUpper at hk
  have hm : ((0/1)/5)+(2320451/2000000)-0 < ((0/1)/3)+(74892223/50000000)-(nextNormalPenalty adverseNextS31Before) := by
    have h : ((0/1)/5)+(2320451/2000000) < ((0/1)/3)+(74892223/50000000)-nextNormalPenaltyUpper := by norm_num [nextNormalPenaltyUpper,savedCref,uniformQuoteError]
    linarith [hk.2]
  have h := index_strict_order_from_intervals ((0/1)/3) ((0/1)/5) (nextNormalPenalty adverseNextS31Before) 0 (74892223/50000000) (2320451/2000000)
    (treeBonus (7/5) 30 3) (treeBonus (7/5) 30 5)
    (trajectory_bonus_30_3).1 (trajectory_bonus_30_5).2 hm
  simpa only [treeIndex] using h

theorem adverseNextS31D0Cmp2 : indexScore (7/5) (controlPenalty savedCref uniformQuoteError unitRoleUnused .next) adverseNextS31Before [] (.query 2) < indexScore (7/5) (controlPenalty savedCref uniformQuoteError unitRoleUnused .next) adverseNextS31Before [] (.query 3) := by
  rw [adverseNextS31D0I2,adverseNextS31D0I3]
  have hk := adverse_next_penalty_interval 30 (by omega)
  change nextNormalPenaltyLower ≤ nextNormalPenalty adverseNextS31Before ∧ nextNormalPenalty adverseNextS31Before ≤ nextNormalPenaltyUpper at hk
  have hm : ((0/1)/4)+(64858577/50000000)-(nextNormalPenalty adverseNextS31Before) < ((0/1)/3)+(74892223/50000000)-(nextNormalPenalty adverseNextS31Before) := by
    have h : (((0/1)/4)+(64858577/50000000) : ℝ) < ((0/1)/3)+(74892223/50000000) := by norm_num
    linarith
  have h := index_strict_order_from_intervals ((0/1)/3) ((0/1)/4) (nextNormalPenalty adverseNextS31Before) (nextNormalPenalty adverseNextS31Before) (74892223/50000000) (64858577/50000000)
    (treeBonus (7/5) 30 3) (treeBonus (7/5) 30 4)
    (trajectory_bonus_30_3).1 (trajectory_bonus_30_4).2 hm
  simpa only [treeIndex] using h

theorem adverseNextS31D0Cmp4 : indexScore (7/5) (controlPenalty savedCref uniformQuoteError unitRoleUnused .next) adverseNextS31Before [] (.query 4) ≤ indexScore (7/5) (controlPenalty savedCref uniformQuoteError unitRoleUnused .next) adverseNextS31Before [] (.query 3) := by
  rw [adverseNextS31D0I4,adverseNextS31D0I3]

theorem adverseNextS31D0Cmp5 : indexScore (7/5) (controlPenalty savedCref uniformQuoteError unitRoleUnused .next) adverseNextS31Before [] (.query 5) ≤ indexScore (7/5) (controlPenalty savedCref uniformQuoteError unitRoleUnused .next) adverseNextS31Before [] (.query 3) := by
  rw [adverseNextS31D0I5,adverseNextS31D0I3]
  have hk := adverse_next_penalty_interval 30 (by omega)
  change nextNormalPenaltyLower ≤ nextNormalPenalty adverseNextS31Before ∧ nextNormalPenalty adverseNextS31Before ≤ nextNormalPenaltyUpper at hk
  have hm : ((13/10)/5)+(2320451/2000000)-(nextNormalPenalty adverseNextS31Before) < ((0/1)/3)+(74892223/50000000)-(nextNormalPenalty adverseNextS31Before) := by
    have h : (((13/10)/5)+(2320451/2000000) : ℝ) < ((0/1)/3)+(74892223/50000000) := by norm_num
    linarith
  have h := index_weak_order_from_intervals ((0/1)/3) ((13/10)/5) (nextNormalPenalty adverseNextS31Before) (nextNormalPenalty adverseNextS31Before) (74892223/50000000) (2320451/2000000)
    (treeBonus (7/5) 30 3) (treeBonus (7/5) 30 5)
    (trajectory_bonus_30_3).1 (trajectory_bonus_30_5).2 hm.le
  simpa only [treeIndex] using h

theorem adverseNextS31D0Cmp6 : indexScore (7/5) (controlPenalty savedCref uniformQuoteError unitRoleUnused .next) adverseNextS31Before [] (.query 6) ≤ indexScore (7/5) (controlPenalty savedCref uniformQuoteError unitRoleUnused .next) adverseNextS31Before [] (.query 3) := by
  rw [adverseNextS31D0I6,adverseNextS31D0I3]

theorem adverseNextS31D0Cmp7 : indexScore (7/5) (controlPenalty savedCref uniformQuoteError unitRoleUnused .next) adverseNextS31Before [] (.query 7) ≤ indexScore (7/5) (controlPenalty savedCref uniformQuoteError unitRoleUnused .next) adverseNextS31Before [] (.query 3) := by
  rw [adverseNextS31D0I7,adverseNextS31D0I3]

theorem adverseNextS31Choice0 : nativeFirstChoice (indexScore (7/5) (controlPenalty savedCref uniformQuoteError unitRoleUnused .next) adverseNextS31Before []) adverseNextS31Before [] = .query 3 := by
  apply visited_choice_from_ordered_certificate _ _ [] [.query 0,.query 1,.query 2] [.query 4,.query 5,.query 6,.query 7] (.query 3) (by decide)
  · intro a ha
    have ho : orderedLegalAvailable [] = [.query 0,.query 1,.query 2,.query 3,.query 4,.query 5,.query 6,.query 7] := by decide
    rw [ho] at ha
    simp only [List.mem_cons,List.not_mem_nil,or_false] at ha
    rcases ha with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> decide
  · intro a ha
    simp only [List.mem_cons,List.not_mem_nil,or_false] at ha
    rcases ha with rfl | rfl | rfl
    · exact adverseNextS31D0Cmp0
    · exact adverseNextS31D0Cmp1
    · exact adverseNextS31D0Cmp2
  · intro a ha
    simp only [List.mem_cons,List.not_mem_nil,or_false] at ha
    rcases ha with rfl | rfl | rfl | rfl
    · exact adverseNextS31D0Cmp4
    · exact adverseNextS31D0Cmp5
    · exact adverseNextS31D0Cmp6
    · exact adverseNextS31D0Cmp7

theorem adverseNextS31ActualEvent : nativeEvent budgetTape (7/5) (controlPenalty savedCref uniformQuoteError unitRoleUnused .next)
    (taskReward true (2/5) (1/2)) adverseNextS31Before = adverseNextEvent31 := by
  have hs0 := native_select_existing_step budgetTape (7/5) (controlPenalty savedCref uniformQuoteError unitRoleUnused .next) adverseNextS31Before 8 [] (.query 3)
    (by decide) (by decide) adverseNextS31Choice0
  have hnew := native_select_new_step budgetTape (7/5) (controlPenalty savedCref uniformQuoteError unitRoleUnused .next) adverseNextS31Before 7 [.query 3]
    [.normalRetriever 6,.normalRetriever 7,.normalRetriever 8,.normalRetriever 5,.normalRetriever 1,.normalRetriever 2,.normalRetriever 3,.normalRetriever 12,.normalRetriever 14,.normalRetriever 13,.normalRetriever 21,.normalRetriever 23,.normalRetriever 22,.normalRetriever 9,.normalRetriever 11,.normalRetriever 10,.normalRetriever 15,.normalRetriever 17,.normalRetriever 16,.normalRetriever 18,.normalRetriever 20,.normalRetriever 19,.normalRetriever 24,.normalRetriever 25,.normalRetriever 26,.normalRetriever 27,.normalRetriever 28,.normalRetriever 29] (.normalRetriever 6) (by decide) (by decide) (by decide) (by decide)
  have hs : nativeSelect budgetTape (7/5) (controlPenalty savedCref uniformQuoteError unitRoleUnused .next) adverseNextS31Before 9 [] = [.query 3,.normalRetriever 6] := by
    rw [hs0]
    change nativeSelect budgetTape (7/5) (controlPenalty savedCref uniformQuoteError unitRoleUnused .next) adverseNextS31Before 8 [.query 3] = _
    rw [hnew] <;> rfl
  have hr : repairedRollout budgetTape adverseNextS31Before 9 [.query 3,.normalRetriever 6] = [.query 3,.normalRetriever 6,.selection 0,.width 0,.stop,.reranker 0,.topm 0,.context 0,.answer 0] := by decide
  simp only [nativeEvent,hs,hr]
  rfl

def adverseNextS32Before := adverseNextProposal.take 31

theorem adverseNextS32D0I0 : indexScore (7/5) (controlPenalty savedCref uniformQuoteError unitRoleUnused .next) adverseNextS32Before [] (.query 0) = treeIndex ((0/1)/4) (7/5) (nextNormalPenalty adverseNextS32Before) 31 4 := by
  have hs : replayBackup adverseNextS32Before emptyStatistics ([]++[.query 0]) = ⟨4,(0/1)⟩ := by
    rw [replayBackup_empty_closed_form]
    simp +decide [backedEvents,adverseNextS32Before,adverseNextProposal,adverseNextEvent1,adverseNextEvent2,adverseNextEvent3,adverseNextEvent4,adverseNextEvent5,adverseNextEvent6,adverseNextEvent7,adverseNextEvent8,adverseNextEvent9,adverseNextEvent10,adverseNextEvent11,adverseNextEvent12,adverseNextEvent13,adverseNextEvent14,adverseNextEvent15,adverseNextEvent16,adverseNextEvent17,adverseNextEvent18,adverseNextEvent19,adverseNextEvent20,adverseNextEvent21,adverseNextEvent22,adverseNextEvent23,adverseNextEvent24,adverseNextEvent25,adverseNextEvent26,adverseNextEvent27,adverseNextEvent28,adverseNextEvent29,adverseNextEvent30,adverseNextEvent31,taskReward]
    <;> norm_num
  have hp : rawVisits adverseNextS32Before [] = 31 := by decide
  have hn : rawVisits adverseNextS32Before ([]++[.query 0]) = 4 := by decide
  have hz : (controlPenalty savedCref uniformQuoteError unitRoleUnused .next) adverseNextS32Before [] (.query 0) = (nextNormalPenalty adverseNextS32Before) := by
    simpa only [adverseNextS32Before,nextNormalPenalty] using AgentUCTNextExact.adverse_next_normal_root_quotes_exact 31 (by omega) 0 (by decide)
  unfold indexScore
  rw [hs,hp,hn,hz]
  simp only [BackupStat.mean]
  norm_num

theorem adverseNextS32D0I1 : indexScore (7/5) (controlPenalty savedCref uniformQuoteError unitRoleUnused .next) adverseNextS32Before [] (.query 1) = treeIndex ((0/1)/5) (7/5) 0 31 5 := by
  have hs : replayBackup adverseNextS32Before emptyStatistics ([]++[.query 1]) = ⟨5,(0/1)⟩ := by
    rw [replayBackup_empty_closed_form]
    simp +decide [backedEvents,adverseNextS32Before,adverseNextProposal,adverseNextEvent1,adverseNextEvent2,adverseNextEvent3,adverseNextEvent4,adverseNextEvent5,adverseNextEvent6,adverseNextEvent7,adverseNextEvent8,adverseNextEvent9,adverseNextEvent10,adverseNextEvent11,adverseNextEvent12,adverseNextEvent13,adverseNextEvent14,adverseNextEvent15,adverseNextEvent16,adverseNextEvent17,adverseNextEvent18,adverseNextEvent19,adverseNextEvent20,adverseNextEvent21,adverseNextEvent22,adverseNextEvent23,adverseNextEvent24,adverseNextEvent25,adverseNextEvent26,adverseNextEvent27,adverseNextEvent28,adverseNextEvent29,adverseNextEvent30,adverseNextEvent31,taskReward]
    <;> norm_num
  have hp : rawVisits adverseNextS32Before [] = 31 := by decide
  have hn : rawVisits adverseNextS32Before ([]++[.query 1]) = 5 := by decide
  have hz : (controlPenalty savedCref uniformQuoteError unitRoleUnused .next) adverseNextS32Before [] (.query 1) = 0 := by
    apply control_penalty_empty_suffix
    exact AgentUCTNextExact.adverse_next_hyde_root_suffix_empty 31 (by omega)
  unfold indexScore
  rw [hs,hp,hn,hz]
  simp only [BackupStat.mean]
  norm_num

theorem adverseNextS32D0I2 : indexScore (7/5) (controlPenalty savedCref uniformQuoteError unitRoleUnused .next) adverseNextS32Before [] (.query 2) = treeIndex ((0/1)/4) (7/5) (nextNormalPenalty adverseNextS32Before) 31 4 := by
  have hs : replayBackup adverseNextS32Before emptyStatistics ([]++[.query 2]) = ⟨4,(0/1)⟩ := by
    rw [replayBackup_empty_closed_form]
    simp +decide [backedEvents,adverseNextS32Before,adverseNextProposal,adverseNextEvent1,adverseNextEvent2,adverseNextEvent3,adverseNextEvent4,adverseNextEvent5,adverseNextEvent6,adverseNextEvent7,adverseNextEvent8,adverseNextEvent9,adverseNextEvent10,adverseNextEvent11,adverseNextEvent12,adverseNextEvent13,adverseNextEvent14,adverseNextEvent15,adverseNextEvent16,adverseNextEvent17,adverseNextEvent18,adverseNextEvent19,adverseNextEvent20,adverseNextEvent21,adverseNextEvent22,adverseNextEvent23,adverseNextEvent24,adverseNextEvent25,adverseNextEvent26,adverseNextEvent27,adverseNextEvent28,adverseNextEvent29,adverseNextEvent30,adverseNextEvent31,taskReward]
    <;> norm_num
  have hp : rawVisits adverseNextS32Before [] = 31 := by decide
  have hn : rawVisits adverseNextS32Before ([]++[.query 2]) = 4 := by decide
  have hz : (controlPenalty savedCref uniformQuoteError unitRoleUnused .next) adverseNextS32Before [] (.query 2) = (nextNormalPenalty adverseNextS32Before) := by
    simpa only [adverseNextS32Before,nextNormalPenalty] using AgentUCTNextExact.adverse_next_normal_root_quotes_exact 31 (by omega) 2 (by decide)
  unfold indexScore
  rw [hs,hp,hn,hz]
  simp only [BackupStat.mean]
  norm_num

theorem adverseNextS32D0I3 : indexScore (7/5) (controlPenalty savedCref uniformQuoteError unitRoleUnused .next) adverseNextS32Before [] (.query 3) = treeIndex ((0/1)/4) (7/5) (nextNormalPenalty adverseNextS32Before) 31 4 := by
  have hs : replayBackup adverseNextS32Before emptyStatistics ([]++[.query 3]) = ⟨4,(0/1)⟩ := by
    rw [replayBackup_empty_closed_form]
    simp +decide [backedEvents,adverseNextS32Before,adverseNextProposal,adverseNextEvent1,adverseNextEvent2,adverseNextEvent3,adverseNextEvent4,adverseNextEvent5,adverseNextEvent6,adverseNextEvent7,adverseNextEvent8,adverseNextEvent9,adverseNextEvent10,adverseNextEvent11,adverseNextEvent12,adverseNextEvent13,adverseNextEvent14,adverseNextEvent15,adverseNextEvent16,adverseNextEvent17,adverseNextEvent18,adverseNextEvent19,adverseNextEvent20,adverseNextEvent21,adverseNextEvent22,adverseNextEvent23,adverseNextEvent24,adverseNextEvent25,adverseNextEvent26,adverseNextEvent27,adverseNextEvent28,adverseNextEvent29,adverseNextEvent30,adverseNextEvent31,taskReward]
    <;> norm_num
  have hp : rawVisits adverseNextS32Before [] = 31 := by decide
  have hn : rawVisits adverseNextS32Before ([]++[.query 3]) = 4 := by decide
  have hz : (controlPenalty savedCref uniformQuoteError unitRoleUnused .next) adverseNextS32Before [] (.query 3) = (nextNormalPenalty adverseNextS32Before) := by
    simpa only [adverseNextS32Before,nextNormalPenalty] using AgentUCTNextExact.adverse_next_normal_root_quotes_exact 31 (by omega) 3 (by decide)
  unfold indexScore
  rw [hs,hp,hn,hz]
  simp only [BackupStat.mean]
  norm_num

theorem adverseNextS32D0I4 : indexScore (7/5) (controlPenalty savedCref uniformQuoteError unitRoleUnused .next) adverseNextS32Before [] (.query 4) = treeIndex ((0/1)/3) (7/5) (nextNormalPenalty adverseNextS32Before) 31 3 := by
  have hs : replayBackup adverseNextS32Before emptyStatistics ([]++[.query 4]) = ⟨3,(0/1)⟩ := by
    rw [replayBackup_empty_closed_form]
    simp +decide [backedEvents,adverseNextS32Before,adverseNextProposal,adverseNextEvent1,adverseNextEvent2,adverseNextEvent3,adverseNextEvent4,adverseNextEvent5,adverseNextEvent6,adverseNextEvent7,adverseNextEvent8,adverseNextEvent9,adverseNextEvent10,adverseNextEvent11,adverseNextEvent12,adverseNextEvent13,adverseNextEvent14,adverseNextEvent15,adverseNextEvent16,adverseNextEvent17,adverseNextEvent18,adverseNextEvent19,adverseNextEvent20,adverseNextEvent21,adverseNextEvent22,adverseNextEvent23,adverseNextEvent24,adverseNextEvent25,adverseNextEvent26,adverseNextEvent27,adverseNextEvent28,adverseNextEvent29,adverseNextEvent30,adverseNextEvent31,taskReward]
    <;> norm_num
  have hp : rawVisits adverseNextS32Before [] = 31 := by decide
  have hn : rawVisits adverseNextS32Before ([]++[.query 4]) = 3 := by decide
  have hz : (controlPenalty savedCref uniformQuoteError unitRoleUnused .next) adverseNextS32Before [] (.query 4) = (nextNormalPenalty adverseNextS32Before) := by
    simpa only [adverseNextS32Before,nextNormalPenalty] using AgentUCTNextExact.adverse_next_normal_root_quotes_exact 31 (by omega) 4 (by decide)
  unfold indexScore
  rw [hs,hp,hn,hz]
  simp only [BackupStat.mean]
  norm_num

theorem adverseNextS32D0I5 : indexScore (7/5) (controlPenalty savedCref uniformQuoteError unitRoleUnused .next) adverseNextS32Before [] (.query 5) = treeIndex ((13/10)/5) (7/5) (nextNormalPenalty adverseNextS32Before) 31 5 := by
  have hs : replayBackup adverseNextS32Before emptyStatistics ([]++[.query 5]) = ⟨5,(13/10)⟩ := by
    rw [replayBackup_empty_closed_form]
    simp +decide [backedEvents,adverseNextS32Before,adverseNextProposal,adverseNextEvent1,adverseNextEvent2,adverseNextEvent3,adverseNextEvent4,adverseNextEvent5,adverseNextEvent6,adverseNextEvent7,adverseNextEvent8,adverseNextEvent9,adverseNextEvent10,adverseNextEvent11,adverseNextEvent12,adverseNextEvent13,adverseNextEvent14,adverseNextEvent15,adverseNextEvent16,adverseNextEvent17,adverseNextEvent18,adverseNextEvent19,adverseNextEvent20,adverseNextEvent21,adverseNextEvent22,adverseNextEvent23,adverseNextEvent24,adverseNextEvent25,adverseNextEvent26,adverseNextEvent27,adverseNextEvent28,adverseNextEvent29,adverseNextEvent30,adverseNextEvent31,taskReward]
    <;> norm_num
  have hp : rawVisits adverseNextS32Before [] = 31 := by decide
  have hn : rawVisits adverseNextS32Before ([]++[.query 5]) = 5 := by decide
  have hz : (controlPenalty savedCref uniformQuoteError unitRoleUnused .next) adverseNextS32Before [] (.query 5) = (nextNormalPenalty adverseNextS32Before) := by
    simpa only [adverseNextS32Before,nextNormalPenalty] using AgentUCTNextExact.adverse_next_normal_root_quotes_exact 31 (by omega) 5 (by decide)
  unfold indexScore
  rw [hs,hp,hn,hz]
  simp only [BackupStat.mean]
  norm_num

theorem adverseNextS32D0I6 : indexScore (7/5) (controlPenalty savedCref uniformQuoteError unitRoleUnused .next) adverseNextS32Before [] (.query 6) = treeIndex ((0/1)/3) (7/5) (nextNormalPenalty adverseNextS32Before) 31 3 := by
  have hs : replayBackup adverseNextS32Before emptyStatistics ([]++[.query 6]) = ⟨3,(0/1)⟩ := by
    rw [replayBackup_empty_closed_form]
    simp +decide [backedEvents,adverseNextS32Before,adverseNextProposal,adverseNextEvent1,adverseNextEvent2,adverseNextEvent3,adverseNextEvent4,adverseNextEvent5,adverseNextEvent6,adverseNextEvent7,adverseNextEvent8,adverseNextEvent9,adverseNextEvent10,adverseNextEvent11,adverseNextEvent12,adverseNextEvent13,adverseNextEvent14,adverseNextEvent15,adverseNextEvent16,adverseNextEvent17,adverseNextEvent18,adverseNextEvent19,adverseNextEvent20,adverseNextEvent21,adverseNextEvent22,adverseNextEvent23,adverseNextEvent24,adverseNextEvent25,adverseNextEvent26,adverseNextEvent27,adverseNextEvent28,adverseNextEvent29,adverseNextEvent30,adverseNextEvent31,taskReward]
    <;> norm_num
  have hp : rawVisits adverseNextS32Before [] = 31 := by decide
  have hn : rawVisits adverseNextS32Before ([]++[.query 6]) = 3 := by decide
  have hz : (controlPenalty savedCref uniformQuoteError unitRoleUnused .next) adverseNextS32Before [] (.query 6) = (nextNormalPenalty adverseNextS32Before) := by
    simpa only [adverseNextS32Before,nextNormalPenalty] using AgentUCTNextExact.adverse_next_normal_root_quotes_exact 31 (by omega) 6 (by decide)
  unfold indexScore
  rw [hs,hp,hn,hz]
  simp only [BackupStat.mean]
  norm_num

theorem adverseNextS32D0I7 : indexScore (7/5) (controlPenalty savedCref uniformQuoteError unitRoleUnused .next) adverseNextS32Before [] (.query 7) = treeIndex ((0/1)/3) (7/5) (nextNormalPenalty adverseNextS32Before) 31 3 := by
  have hs : replayBackup adverseNextS32Before emptyStatistics ([]++[.query 7]) = ⟨3,(0/1)⟩ := by
    rw [replayBackup_empty_closed_form]
    simp +decide [backedEvents,adverseNextS32Before,adverseNextProposal,adverseNextEvent1,adverseNextEvent2,adverseNextEvent3,adverseNextEvent4,adverseNextEvent5,adverseNextEvent6,adverseNextEvent7,adverseNextEvent8,adverseNextEvent9,adverseNextEvent10,adverseNextEvent11,adverseNextEvent12,adverseNextEvent13,adverseNextEvent14,adverseNextEvent15,adverseNextEvent16,adverseNextEvent17,adverseNextEvent18,adverseNextEvent19,adverseNextEvent20,adverseNextEvent21,adverseNextEvent22,adverseNextEvent23,adverseNextEvent24,adverseNextEvent25,adverseNextEvent26,adverseNextEvent27,adverseNextEvent28,adverseNextEvent29,adverseNextEvent30,adverseNextEvent31,taskReward]
    <;> norm_num
  have hp : rawVisits adverseNextS32Before [] = 31 := by decide
  have hn : rawVisits adverseNextS32Before ([]++[.query 7]) = 3 := by decide
  have hz : (controlPenalty savedCref uniformQuoteError unitRoleUnused .next) adverseNextS32Before [] (.query 7) = (nextNormalPenalty adverseNextS32Before) := by
    simpa only [adverseNextS32Before,nextNormalPenalty] using AgentUCTNextExact.adverse_next_normal_root_quotes_exact 31 (by omega) 7 (by decide)
  unfold indexScore
  rw [hs,hp,hn,hz]
  simp only [BackupStat.mean]
  norm_num

theorem adverseNextS32D0Cmp0 : indexScore (7/5) (controlPenalty savedCref uniformQuoteError unitRoleUnused .next) adverseNextS32Before [] (.query 0) < indexScore (7/5) (controlPenalty savedCref uniformQuoteError unitRoleUnused .next) adverseNextS32Before [] (.query 4) := by
  rw [adverseNextS32D0I0,adverseNextS32D0I4]
  have hk := adverse_next_penalty_interval 31 (by omega)
  change nextNormalPenaltyLower ≤ nextNormalPenalty adverseNextS32Before ∧ nextNormalPenalty adverseNextS32Before ≤ nextNormalPenaltyUpper at hk
  have hm : ((0/1)/4)+(16289427/12500000)-(nextNormalPenalty adverseNextS32Before) < ((0/1)/3)+(75237631/50000000)-(nextNormalPenalty adverseNextS32Before) := by
    have h : (((0/1)/4)+(16289427/12500000) : ℝ) < ((0/1)/3)+(75237631/50000000) := by norm_num
    linarith
  have h := index_strict_order_from_intervals ((0/1)/3) ((0/1)/4) (nextNormalPenalty adverseNextS32Before) (nextNormalPenalty adverseNextS32Before) (75237631/50000000) (16289427/12500000)
    (treeBonus (7/5) 31 3) (treeBonus (7/5) 31 4)
    (trajectory_bonus_31_3).1 (trajectory_bonus_31_4).2 hm
  simpa only [treeIndex] using h

theorem adverseNextS32D0Cmp1 : indexScore (7/5) (controlPenalty savedCref uniformQuoteError unitRoleUnused .next) adverseNextS32Before [] (.query 1) < indexScore (7/5) (controlPenalty savedCref uniformQuoteError unitRoleUnused .next) adverseNextS32Before [] (.query 4) := by
  rw [adverseNextS32D0I1,adverseNextS32D0I4]
  have hk := adverse_next_penalty_interval 31 (by omega)
  change nextNormalPenaltyLower ≤ nextNormalPenalty adverseNextS32Before ∧ nextNormalPenalty adverseNextS32Before ≤ nextNormalPenaltyUpper at hk
  have hm : ((0/1)/5)+(58278829/50000000)-0 < ((0/1)/3)+(75237631/50000000)-(nextNormalPenalty adverseNextS32Before) := by
    have h : ((0/1)/5)+(58278829/50000000) < ((0/1)/3)+(75237631/50000000)-nextNormalPenaltyUpper := by norm_num [nextNormalPenaltyUpper,savedCref,uniformQuoteError]
    linarith [hk.2]
  have h := index_strict_order_from_intervals ((0/1)/3) ((0/1)/5) (nextNormalPenalty adverseNextS32Before) 0 (75237631/50000000) (58278829/50000000)
    (treeBonus (7/5) 31 3) (treeBonus (7/5) 31 5)
    (trajectory_bonus_31_3).1 (trajectory_bonus_31_5).2 hm
  simpa only [treeIndex] using h

theorem adverseNextS32D0Cmp2 : indexScore (7/5) (controlPenalty savedCref uniformQuoteError unitRoleUnused .next) adverseNextS32Before [] (.query 2) < indexScore (7/5) (controlPenalty savedCref uniformQuoteError unitRoleUnused .next) adverseNextS32Before [] (.query 4) := by
  rw [adverseNextS32D0I2,adverseNextS32D0I4]
  have hk := adverse_next_penalty_interval 31 (by omega)
  change nextNormalPenaltyLower ≤ nextNormalPenalty adverseNextS32Before ∧ nextNormalPenalty adverseNextS32Before ≤ nextNormalPenaltyUpper at hk
  have hm : ((0/1)/4)+(16289427/12500000)-(nextNormalPenalty adverseNextS32Before) < ((0/1)/3)+(75237631/50000000)-(nextNormalPenalty adverseNextS32Before) := by
    have h : (((0/1)/4)+(16289427/12500000) : ℝ) < ((0/1)/3)+(75237631/50000000) := by norm_num
    linarith
  have h := index_strict_order_from_intervals ((0/1)/3) ((0/1)/4) (nextNormalPenalty adverseNextS32Before) (nextNormalPenalty adverseNextS32Before) (75237631/50000000) (16289427/12500000)
    (treeBonus (7/5) 31 3) (treeBonus (7/5) 31 4)
    (trajectory_bonus_31_3).1 (trajectory_bonus_31_4).2 hm
  simpa only [treeIndex] using h

theorem adverseNextS32D0Cmp3 : indexScore (7/5) (controlPenalty savedCref uniformQuoteError unitRoleUnused .next) adverseNextS32Before [] (.query 3) < indexScore (7/5) (controlPenalty savedCref uniformQuoteError unitRoleUnused .next) adverseNextS32Before [] (.query 4) := by
  rw [adverseNextS32D0I3,adverseNextS32D0I4]
  have hk := adverse_next_penalty_interval 31 (by omega)
  change nextNormalPenaltyLower ≤ nextNormalPenalty adverseNextS32Before ∧ nextNormalPenalty adverseNextS32Before ≤ nextNormalPenaltyUpper at hk
  have hm : ((0/1)/4)+(16289427/12500000)-(nextNormalPenalty adverseNextS32Before) < ((0/1)/3)+(75237631/50000000)-(nextNormalPenalty adverseNextS32Before) := by
    have h : (((0/1)/4)+(16289427/12500000) : ℝ) < ((0/1)/3)+(75237631/50000000) := by norm_num
    linarith
  have h := index_strict_order_from_intervals ((0/1)/3) ((0/1)/4) (nextNormalPenalty adverseNextS32Before) (nextNormalPenalty adverseNextS32Before) (75237631/50000000) (16289427/12500000)
    (treeBonus (7/5) 31 3) (treeBonus (7/5) 31 4)
    (trajectory_bonus_31_3).1 (trajectory_bonus_31_4).2 hm
  simpa only [treeIndex] using h

theorem adverseNextS32D0Cmp5 : indexScore (7/5) (controlPenalty savedCref uniformQuoteError unitRoleUnused .next) adverseNextS32Before [] (.query 5) ≤ indexScore (7/5) (controlPenalty savedCref uniformQuoteError unitRoleUnused .next) adverseNextS32Before [] (.query 4) := by
  rw [adverseNextS32D0I5,adverseNextS32D0I4]
  have hk := adverse_next_penalty_interval 31 (by omega)
  change nextNormalPenaltyLower ≤ nextNormalPenalty adverseNextS32Before ∧ nextNormalPenalty adverseNextS32Before ≤ nextNormalPenaltyUpper at hk
  have hm : ((13/10)/5)+(58278829/50000000)-(nextNormalPenalty adverseNextS32Before) < ((0/1)/3)+(75237631/50000000)-(nextNormalPenalty adverseNextS32Before) := by
    have h : (((13/10)/5)+(58278829/50000000) : ℝ) < ((0/1)/3)+(75237631/50000000) := by norm_num
    linarith
  have h := index_weak_order_from_intervals ((0/1)/3) ((13/10)/5) (nextNormalPenalty adverseNextS32Before) (nextNormalPenalty adverseNextS32Before) (75237631/50000000) (58278829/50000000)
    (treeBonus (7/5) 31 3) (treeBonus (7/5) 31 5)
    (trajectory_bonus_31_3).1 (trajectory_bonus_31_5).2 hm.le
  simpa only [treeIndex] using h

theorem adverseNextS32D0Cmp6 : indexScore (7/5) (controlPenalty savedCref uniformQuoteError unitRoleUnused .next) adverseNextS32Before [] (.query 6) ≤ indexScore (7/5) (controlPenalty savedCref uniformQuoteError unitRoleUnused .next) adverseNextS32Before [] (.query 4) := by
  rw [adverseNextS32D0I6,adverseNextS32D0I4]

theorem adverseNextS32D0Cmp7 : indexScore (7/5) (controlPenalty savedCref uniformQuoteError unitRoleUnused .next) adverseNextS32Before [] (.query 7) ≤ indexScore (7/5) (controlPenalty savedCref uniformQuoteError unitRoleUnused .next) adverseNextS32Before [] (.query 4) := by
  rw [adverseNextS32D0I7,adverseNextS32D0I4]

theorem adverseNextS32Choice0 : nativeFirstChoice (indexScore (7/5) (controlPenalty savedCref uniformQuoteError unitRoleUnused .next) adverseNextS32Before []) adverseNextS32Before [] = .query 4 := by
  apply visited_choice_from_ordered_certificate _ _ [] [.query 0,.query 1,.query 2,.query 3] [.query 5,.query 6,.query 7] (.query 4) (by decide)
  · intro a ha
    have ho : orderedLegalAvailable [] = [.query 0,.query 1,.query 2,.query 3,.query 4,.query 5,.query 6,.query 7] := by decide
    rw [ho] at ha
    simp only [List.mem_cons,List.not_mem_nil,or_false] at ha
    rcases ha with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> decide
  · intro a ha
    simp only [List.mem_cons,List.not_mem_nil,or_false] at ha
    rcases ha with rfl | rfl | rfl | rfl
    · exact adverseNextS32D0Cmp0
    · exact adverseNextS32D0Cmp1
    · exact adverseNextS32D0Cmp2
    · exact adverseNextS32D0Cmp3
  · intro a ha
    simp only [List.mem_cons,List.not_mem_nil,or_false] at ha
    rcases ha with rfl | rfl | rfl
    · exact adverseNextS32D0Cmp5
    · exact adverseNextS32D0Cmp6
    · exact adverseNextS32D0Cmp7

theorem adverseNextS32ActualEvent : nativeEvent budgetTape (7/5) (controlPenalty savedCref uniformQuoteError unitRoleUnused .next)
    (taskReward true (2/5) (1/2)) adverseNextS32Before = adverseNextEvent32 := by
  have hs0 := native_select_existing_step budgetTape (7/5) (controlPenalty savedCref uniformQuoteError unitRoleUnused .next) adverseNextS32Before 8 [] (.query 4)
    (by decide) (by decide) adverseNextS32Choice0
  have hnew := native_select_new_step budgetTape (7/5) (controlPenalty savedCref uniformQuoteError unitRoleUnused .next) adverseNextS32Before 7 [.query 4]
    [.normalRetriever 6,.normalRetriever 7,.normalRetriever 8,.normalRetriever 5,.normalRetriever 1,.normalRetriever 2,.normalRetriever 3,.normalRetriever 12,.normalRetriever 14,.normalRetriever 13,.normalRetriever 21,.normalRetriever 23,.normalRetriever 22,.normalRetriever 9,.normalRetriever 11,.normalRetriever 10,.normalRetriever 15,.normalRetriever 17,.normalRetriever 16,.normalRetriever 18,.normalRetriever 20,.normalRetriever 19,.normalRetriever 24,.normalRetriever 25,.normalRetriever 26,.normalRetriever 27,.normalRetriever 28,.normalRetriever 29] (.normalRetriever 6) (by decide) (by decide) (by decide) (by decide)
  have hs : nativeSelect budgetTape (7/5) (controlPenalty savedCref uniformQuoteError unitRoleUnused .next) adverseNextS32Before 9 [] = [.query 4,.normalRetriever 6] := by
    rw [hs0]
    change nativeSelect budgetTape (7/5) (controlPenalty savedCref uniformQuoteError unitRoleUnused .next) adverseNextS32Before 8 [.query 4] = _
    rw [hnew] <;> rfl
  have hr : repairedRollout budgetTape adverseNextS32Before 9 [.query 4,.normalRetriever 6] = [.query 4,.normalRetriever 6,.selection 0,.width 0,.stop,.reranker 0,.topm 0,.context 0,.answer 0] := by decide
  simp only [nativeEvent,hs,hr]
  rfl

def adverseNextS33Before := adverseNextProposal.take 32

theorem adverseNextS33D0I0 : indexScore (7/5) (controlPenalty savedCref uniformQuoteError unitRoleUnused .next) adverseNextS33Before [] (.query 0) = treeIndex ((0/1)/4) (7/5) (nextNormalPenalty adverseNextS33Before) 32 4 := by
  have hs : replayBackup adverseNextS33Before emptyStatistics ([]++[.query 0]) = ⟨4,(0/1)⟩ := by
    rw [replayBackup_empty_closed_form]
    simp +decide [backedEvents,adverseNextS33Before,adverseNextProposal,adverseNextEvent1,adverseNextEvent2,adverseNextEvent3,adverseNextEvent4,adverseNextEvent5,adverseNextEvent6,adverseNextEvent7,adverseNextEvent8,adverseNextEvent9,adverseNextEvent10,adverseNextEvent11,adverseNextEvent12,adverseNextEvent13,adverseNextEvent14,adverseNextEvent15,adverseNextEvent16,adverseNextEvent17,adverseNextEvent18,adverseNextEvent19,adverseNextEvent20,adverseNextEvent21,adverseNextEvent22,adverseNextEvent23,adverseNextEvent24,adverseNextEvent25,adverseNextEvent26,adverseNextEvent27,adverseNextEvent28,adverseNextEvent29,adverseNextEvent30,adverseNextEvent31,adverseNextEvent32,taskReward]
    <;> norm_num
  have hp : rawVisits adverseNextS33Before [] = 32 := by decide
  have hn : rawVisits adverseNextS33Before ([]++[.query 0]) = 4 := by decide
  have hz : (controlPenalty savedCref uniformQuoteError unitRoleUnused .next) adverseNextS33Before [] (.query 0) = (nextNormalPenalty adverseNextS33Before) := by
    simpa only [adverseNextS33Before,nextNormalPenalty] using AgentUCTNextExact.adverse_next_normal_root_quotes_exact 32 (by omega) 0 (by decide)
  unfold indexScore
  rw [hs,hp,hn,hz]
  simp only [BackupStat.mean]
  norm_num

theorem adverseNextS33D0I1 : indexScore (7/5) (controlPenalty savedCref uniformQuoteError unitRoleUnused .next) adverseNextS33Before [] (.query 1) = treeIndex ((0/1)/5) (7/5) 0 32 5 := by
  have hs : replayBackup adverseNextS33Before emptyStatistics ([]++[.query 1]) = ⟨5,(0/1)⟩ := by
    rw [replayBackup_empty_closed_form]
    simp +decide [backedEvents,adverseNextS33Before,adverseNextProposal,adverseNextEvent1,adverseNextEvent2,adverseNextEvent3,adverseNextEvent4,adverseNextEvent5,adverseNextEvent6,adverseNextEvent7,adverseNextEvent8,adverseNextEvent9,adverseNextEvent10,adverseNextEvent11,adverseNextEvent12,adverseNextEvent13,adverseNextEvent14,adverseNextEvent15,adverseNextEvent16,adverseNextEvent17,adverseNextEvent18,adverseNextEvent19,adverseNextEvent20,adverseNextEvent21,adverseNextEvent22,adverseNextEvent23,adverseNextEvent24,adverseNextEvent25,adverseNextEvent26,adverseNextEvent27,adverseNextEvent28,adverseNextEvent29,adverseNextEvent30,adverseNextEvent31,adverseNextEvent32,taskReward]
    <;> norm_num
  have hp : rawVisits adverseNextS33Before [] = 32 := by decide
  have hn : rawVisits adverseNextS33Before ([]++[.query 1]) = 5 := by decide
  have hz : (controlPenalty savedCref uniformQuoteError unitRoleUnused .next) adverseNextS33Before [] (.query 1) = 0 := by
    apply control_penalty_empty_suffix
    exact AgentUCTNextExact.adverse_next_hyde_root_suffix_empty 32 (by omega)
  unfold indexScore
  rw [hs,hp,hn,hz]
  simp only [BackupStat.mean]
  norm_num

theorem adverseNextS33D0I2 : indexScore (7/5) (controlPenalty savedCref uniformQuoteError unitRoleUnused .next) adverseNextS33Before [] (.query 2) = treeIndex ((0/1)/4) (7/5) (nextNormalPenalty adverseNextS33Before) 32 4 := by
  have hs : replayBackup adverseNextS33Before emptyStatistics ([]++[.query 2]) = ⟨4,(0/1)⟩ := by
    rw [replayBackup_empty_closed_form]
    simp +decide [backedEvents,adverseNextS33Before,adverseNextProposal,adverseNextEvent1,adverseNextEvent2,adverseNextEvent3,adverseNextEvent4,adverseNextEvent5,adverseNextEvent6,adverseNextEvent7,adverseNextEvent8,adverseNextEvent9,adverseNextEvent10,adverseNextEvent11,adverseNextEvent12,adverseNextEvent13,adverseNextEvent14,adverseNextEvent15,adverseNextEvent16,adverseNextEvent17,adverseNextEvent18,adverseNextEvent19,adverseNextEvent20,adverseNextEvent21,adverseNextEvent22,adverseNextEvent23,adverseNextEvent24,adverseNextEvent25,adverseNextEvent26,adverseNextEvent27,adverseNextEvent28,adverseNextEvent29,adverseNextEvent30,adverseNextEvent31,adverseNextEvent32,taskReward]
    <;> norm_num
  have hp : rawVisits adverseNextS33Before [] = 32 := by decide
  have hn : rawVisits adverseNextS33Before ([]++[.query 2]) = 4 := by decide
  have hz : (controlPenalty savedCref uniformQuoteError unitRoleUnused .next) adverseNextS33Before [] (.query 2) = (nextNormalPenalty adverseNextS33Before) := by
    simpa only [adverseNextS33Before,nextNormalPenalty] using AgentUCTNextExact.adverse_next_normal_root_quotes_exact 32 (by omega) 2 (by decide)
  unfold indexScore
  rw [hs,hp,hn,hz]
  simp only [BackupStat.mean]
  norm_num

theorem adverseNextS33D0I3 : indexScore (7/5) (controlPenalty savedCref uniformQuoteError unitRoleUnused .next) adverseNextS33Before [] (.query 3) = treeIndex ((0/1)/4) (7/5) (nextNormalPenalty adverseNextS33Before) 32 4 := by
  have hs : replayBackup adverseNextS33Before emptyStatistics ([]++[.query 3]) = ⟨4,(0/1)⟩ := by
    rw [replayBackup_empty_closed_form]
    simp +decide [backedEvents,adverseNextS33Before,adverseNextProposal,adverseNextEvent1,adverseNextEvent2,adverseNextEvent3,adverseNextEvent4,adverseNextEvent5,adverseNextEvent6,adverseNextEvent7,adverseNextEvent8,adverseNextEvent9,adverseNextEvent10,adverseNextEvent11,adverseNextEvent12,adverseNextEvent13,adverseNextEvent14,adverseNextEvent15,adverseNextEvent16,adverseNextEvent17,adverseNextEvent18,adverseNextEvent19,adverseNextEvent20,adverseNextEvent21,adverseNextEvent22,adverseNextEvent23,adverseNextEvent24,adverseNextEvent25,adverseNextEvent26,adverseNextEvent27,adverseNextEvent28,adverseNextEvent29,adverseNextEvent30,adverseNextEvent31,adverseNextEvent32,taskReward]
    <;> norm_num
  have hp : rawVisits adverseNextS33Before [] = 32 := by decide
  have hn : rawVisits adverseNextS33Before ([]++[.query 3]) = 4 := by decide
  have hz : (controlPenalty savedCref uniformQuoteError unitRoleUnused .next) adverseNextS33Before [] (.query 3) = (nextNormalPenalty adverseNextS33Before) := by
    simpa only [adverseNextS33Before,nextNormalPenalty] using AgentUCTNextExact.adverse_next_normal_root_quotes_exact 32 (by omega) 3 (by decide)
  unfold indexScore
  rw [hs,hp,hn,hz]
  simp only [BackupStat.mean]
  norm_num

theorem adverseNextS33D0I4 : indexScore (7/5) (controlPenalty savedCref uniformQuoteError unitRoleUnused .next) adverseNextS33Before [] (.query 4) = treeIndex ((0/1)/4) (7/5) (nextNormalPenalty adverseNextS33Before) 32 4 := by
  have hs : replayBackup adverseNextS33Before emptyStatistics ([]++[.query 4]) = ⟨4,(0/1)⟩ := by
    rw [replayBackup_empty_closed_form]
    simp +decide [backedEvents,adverseNextS33Before,adverseNextProposal,adverseNextEvent1,adverseNextEvent2,adverseNextEvent3,adverseNextEvent4,adverseNextEvent5,adverseNextEvent6,adverseNextEvent7,adverseNextEvent8,adverseNextEvent9,adverseNextEvent10,adverseNextEvent11,adverseNextEvent12,adverseNextEvent13,adverseNextEvent14,adverseNextEvent15,adverseNextEvent16,adverseNextEvent17,adverseNextEvent18,adverseNextEvent19,adverseNextEvent20,adverseNextEvent21,adverseNextEvent22,adverseNextEvent23,adverseNextEvent24,adverseNextEvent25,adverseNextEvent26,adverseNextEvent27,adverseNextEvent28,adverseNextEvent29,adverseNextEvent30,adverseNextEvent31,adverseNextEvent32,taskReward]
    <;> norm_num
  have hp : rawVisits adverseNextS33Before [] = 32 := by decide
  have hn : rawVisits adverseNextS33Before ([]++[.query 4]) = 4 := by decide
  have hz : (controlPenalty savedCref uniformQuoteError unitRoleUnused .next) adverseNextS33Before [] (.query 4) = (nextNormalPenalty adverseNextS33Before) := by
    simpa only [adverseNextS33Before,nextNormalPenalty] using AgentUCTNextExact.adverse_next_normal_root_quotes_exact 32 (by omega) 4 (by decide)
  unfold indexScore
  rw [hs,hp,hn,hz]
  simp only [BackupStat.mean]
  norm_num

theorem adverseNextS33D0I5 : indexScore (7/5) (controlPenalty savedCref uniformQuoteError unitRoleUnused .next) adverseNextS33Before [] (.query 5) = treeIndex ((13/10)/5) (7/5) (nextNormalPenalty adverseNextS33Before) 32 5 := by
  have hs : replayBackup adverseNextS33Before emptyStatistics ([]++[.query 5]) = ⟨5,(13/10)⟩ := by
    rw [replayBackup_empty_closed_form]
    simp +decide [backedEvents,adverseNextS33Before,adverseNextProposal,adverseNextEvent1,adverseNextEvent2,adverseNextEvent3,adverseNextEvent4,adverseNextEvent5,adverseNextEvent6,adverseNextEvent7,adverseNextEvent8,adverseNextEvent9,adverseNextEvent10,adverseNextEvent11,adverseNextEvent12,adverseNextEvent13,adverseNextEvent14,adverseNextEvent15,adverseNextEvent16,adverseNextEvent17,adverseNextEvent18,adverseNextEvent19,adverseNextEvent20,adverseNextEvent21,adverseNextEvent22,adverseNextEvent23,adverseNextEvent24,adverseNextEvent25,adverseNextEvent26,adverseNextEvent27,adverseNextEvent28,adverseNextEvent29,adverseNextEvent30,adverseNextEvent31,adverseNextEvent32,taskReward]
    <;> norm_num
  have hp : rawVisits adverseNextS33Before [] = 32 := by decide
  have hn : rawVisits adverseNextS33Before ([]++[.query 5]) = 5 := by decide
  have hz : (controlPenalty savedCref uniformQuoteError unitRoleUnused .next) adverseNextS33Before [] (.query 5) = (nextNormalPenalty adverseNextS33Before) := by
    simpa only [adverseNextS33Before,nextNormalPenalty] using AgentUCTNextExact.adverse_next_normal_root_quotes_exact 32 (by omega) 5 (by decide)
  unfold indexScore
  rw [hs,hp,hn,hz]
  simp only [BackupStat.mean]
  norm_num

theorem adverseNextS33D0I6 : indexScore (7/5) (controlPenalty savedCref uniformQuoteError unitRoleUnused .next) adverseNextS33Before [] (.query 6) = treeIndex ((0/1)/3) (7/5) (nextNormalPenalty adverseNextS33Before) 32 3 := by
  have hs : replayBackup adverseNextS33Before emptyStatistics ([]++[.query 6]) = ⟨3,(0/1)⟩ := by
    rw [replayBackup_empty_closed_form]
    simp +decide [backedEvents,adverseNextS33Before,adverseNextProposal,adverseNextEvent1,adverseNextEvent2,adverseNextEvent3,adverseNextEvent4,adverseNextEvent5,adverseNextEvent6,adverseNextEvent7,adverseNextEvent8,adverseNextEvent9,adverseNextEvent10,adverseNextEvent11,adverseNextEvent12,adverseNextEvent13,adverseNextEvent14,adverseNextEvent15,adverseNextEvent16,adverseNextEvent17,adverseNextEvent18,adverseNextEvent19,adverseNextEvent20,adverseNextEvent21,adverseNextEvent22,adverseNextEvent23,adverseNextEvent24,adverseNextEvent25,adverseNextEvent26,adverseNextEvent27,adverseNextEvent28,adverseNextEvent29,adverseNextEvent30,adverseNextEvent31,adverseNextEvent32,taskReward]
    <;> norm_num
  have hp : rawVisits adverseNextS33Before [] = 32 := by decide
  have hn : rawVisits adverseNextS33Before ([]++[.query 6]) = 3 := by decide
  have hz : (controlPenalty savedCref uniformQuoteError unitRoleUnused .next) adverseNextS33Before [] (.query 6) = (nextNormalPenalty adverseNextS33Before) := by
    simpa only [adverseNextS33Before,nextNormalPenalty] using AgentUCTNextExact.adverse_next_normal_root_quotes_exact 32 (by omega) 6 (by decide)
  unfold indexScore
  rw [hs,hp,hn,hz]
  simp only [BackupStat.mean]
  norm_num

theorem adverseNextS33D0I7 : indexScore (7/5) (controlPenalty savedCref uniformQuoteError unitRoleUnused .next) adverseNextS33Before [] (.query 7) = treeIndex ((0/1)/3) (7/5) (nextNormalPenalty adverseNextS33Before) 32 3 := by
  have hs : replayBackup adverseNextS33Before emptyStatistics ([]++[.query 7]) = ⟨3,(0/1)⟩ := by
    rw [replayBackup_empty_closed_form]
    simp +decide [backedEvents,adverseNextS33Before,adverseNextProposal,adverseNextEvent1,adverseNextEvent2,adverseNextEvent3,adverseNextEvent4,adverseNextEvent5,adverseNextEvent6,adverseNextEvent7,adverseNextEvent8,adverseNextEvent9,adverseNextEvent10,adverseNextEvent11,adverseNextEvent12,adverseNextEvent13,adverseNextEvent14,adverseNextEvent15,adverseNextEvent16,adverseNextEvent17,adverseNextEvent18,adverseNextEvent19,adverseNextEvent20,adverseNextEvent21,adverseNextEvent22,adverseNextEvent23,adverseNextEvent24,adverseNextEvent25,adverseNextEvent26,adverseNextEvent27,adverseNextEvent28,adverseNextEvent29,adverseNextEvent30,adverseNextEvent31,adverseNextEvent32,taskReward]
    <;> norm_num
  have hp : rawVisits adverseNextS33Before [] = 32 := by decide
  have hn : rawVisits adverseNextS33Before ([]++[.query 7]) = 3 := by decide
  have hz : (controlPenalty savedCref uniformQuoteError unitRoleUnused .next) adverseNextS33Before [] (.query 7) = (nextNormalPenalty adverseNextS33Before) := by
    simpa only [adverseNextS33Before,nextNormalPenalty] using AgentUCTNextExact.adverse_next_normal_root_quotes_exact 32 (by omega) 7 (by decide)
  unfold indexScore
  rw [hs,hp,hn,hz]
  simp only [BackupStat.mean]
  norm_num

theorem adverseNextS33D0Cmp0 : indexScore (7/5) (controlPenalty savedCref uniformQuoteError unitRoleUnused .next) adverseNextS33Before [] (.query 0) < indexScore (7/5) (controlPenalty savedCref uniformQuoteError unitRoleUnused .next) adverseNextS33Before [] (.query 6) := by
  rw [adverseNextS33D0I0,adverseNextS33D0I6]
  have hk := adverse_next_penalty_interval 32 (by omega)
  change nextNormalPenaltyLower ≤ nextNormalPenalty adverseNextS33Before ∧ nextNormalPenalty adverseNextS33Before ≤ nextNormalPenaltyUpper at hk
  have hm : ((0/1)/4)+(65446339/50000000)-(nextNormalPenalty adverseNextS33Before) < ((0/1)/3)+(75570901/50000000)-(nextNormalPenalty adverseNextS33Before) := by
    have h : (((0/1)/4)+(65446339/50000000) : ℝ) < ((0/1)/3)+(75570901/50000000) := by norm_num
    linarith
  have h := index_strict_order_from_intervals ((0/1)/3) ((0/1)/4) (nextNormalPenalty adverseNextS33Before) (nextNormalPenalty adverseNextS33Before) (75570901/50000000) (65446339/50000000)
    (treeBonus (7/5) 32 3) (treeBonus (7/5) 32 4)
    (trajectory_bonus_32_3).1 (trajectory_bonus_32_4).2 hm
  simpa only [treeIndex] using h

theorem adverseNextS33D0Cmp1 : indexScore (7/5) (controlPenalty savedCref uniformQuoteError unitRoleUnused .next) adverseNextS33Before [] (.query 1) < indexScore (7/5) (controlPenalty savedCref uniformQuoteError unitRoleUnused .next) adverseNextS33Before [] (.query 6) := by
  rw [adverseNextS33D0I1,adverseNextS33D0I6]
  have hk := adverse_next_penalty_interval 32 (by omega)
  change nextNormalPenaltyLower ≤ nextNormalPenalty adverseNextS33Before ∧ nextNormalPenalty adverseNextS33Before ≤ nextNormalPenaltyUpper at hk
  have hm : ((0/1)/5)+(29268491/25000000)-0 < ((0/1)/3)+(75570901/50000000)-(nextNormalPenalty adverseNextS33Before) := by
    have h : ((0/1)/5)+(29268491/25000000) < ((0/1)/3)+(75570901/50000000)-nextNormalPenaltyUpper := by norm_num [nextNormalPenaltyUpper,savedCref,uniformQuoteError]
    linarith [hk.2]
  have h := index_strict_order_from_intervals ((0/1)/3) ((0/1)/5) (nextNormalPenalty adverseNextS33Before) 0 (75570901/50000000) (29268491/25000000)
    (treeBonus (7/5) 32 3) (treeBonus (7/5) 32 5)
    (trajectory_bonus_32_3).1 (trajectory_bonus_32_5).2 hm
  simpa only [treeIndex] using h

theorem adverseNextS33D0Cmp2 : indexScore (7/5) (controlPenalty savedCref uniformQuoteError unitRoleUnused .next) adverseNextS33Before [] (.query 2) < indexScore (7/5) (controlPenalty savedCref uniformQuoteError unitRoleUnused .next) adverseNextS33Before [] (.query 6) := by
  rw [adverseNextS33D0I2,adverseNextS33D0I6]
  have hk := adverse_next_penalty_interval 32 (by omega)
  change nextNormalPenaltyLower ≤ nextNormalPenalty adverseNextS33Before ∧ nextNormalPenalty adverseNextS33Before ≤ nextNormalPenaltyUpper at hk
  have hm : ((0/1)/4)+(65446339/50000000)-(nextNormalPenalty adverseNextS33Before) < ((0/1)/3)+(75570901/50000000)-(nextNormalPenalty adverseNextS33Before) := by
    have h : (((0/1)/4)+(65446339/50000000) : ℝ) < ((0/1)/3)+(75570901/50000000) := by norm_num
    linarith
  have h := index_strict_order_from_intervals ((0/1)/3) ((0/1)/4) (nextNormalPenalty adverseNextS33Before) (nextNormalPenalty adverseNextS33Before) (75570901/50000000) (65446339/50000000)
    (treeBonus (7/5) 32 3) (treeBonus (7/5) 32 4)
    (trajectory_bonus_32_3).1 (trajectory_bonus_32_4).2 hm
  simpa only [treeIndex] using h

theorem adverseNextS33D0Cmp3 : indexScore (7/5) (controlPenalty savedCref uniformQuoteError unitRoleUnused .next) adverseNextS33Before [] (.query 3) < indexScore (7/5) (controlPenalty savedCref uniformQuoteError unitRoleUnused .next) adverseNextS33Before [] (.query 6) := by
  rw [adverseNextS33D0I3,adverseNextS33D0I6]
  have hk := adverse_next_penalty_interval 32 (by omega)
  change nextNormalPenaltyLower ≤ nextNormalPenalty adverseNextS33Before ∧ nextNormalPenalty adverseNextS33Before ≤ nextNormalPenaltyUpper at hk
  have hm : ((0/1)/4)+(65446339/50000000)-(nextNormalPenalty adverseNextS33Before) < ((0/1)/3)+(75570901/50000000)-(nextNormalPenalty adverseNextS33Before) := by
    have h : (((0/1)/4)+(65446339/50000000) : ℝ) < ((0/1)/3)+(75570901/50000000) := by norm_num
    linarith
  have h := index_strict_order_from_intervals ((0/1)/3) ((0/1)/4) (nextNormalPenalty adverseNextS33Before) (nextNormalPenalty adverseNextS33Before) (75570901/50000000) (65446339/50000000)
    (treeBonus (7/5) 32 3) (treeBonus (7/5) 32 4)
    (trajectory_bonus_32_3).1 (trajectory_bonus_32_4).2 hm
  simpa only [treeIndex] using h

theorem adverseNextS33D0Cmp4 : indexScore (7/5) (controlPenalty savedCref uniformQuoteError unitRoleUnused .next) adverseNextS33Before [] (.query 4) < indexScore (7/5) (controlPenalty savedCref uniformQuoteError unitRoleUnused .next) adverseNextS33Before [] (.query 6) := by
  rw [adverseNextS33D0I4,adverseNextS33D0I6]
  have hk := adverse_next_penalty_interval 32 (by omega)
  change nextNormalPenaltyLower ≤ nextNormalPenalty adverseNextS33Before ∧ nextNormalPenalty adverseNextS33Before ≤ nextNormalPenaltyUpper at hk
  have hm : ((0/1)/4)+(65446339/50000000)-(nextNormalPenalty adverseNextS33Before) < ((0/1)/3)+(75570901/50000000)-(nextNormalPenalty adverseNextS33Before) := by
    have h : (((0/1)/4)+(65446339/50000000) : ℝ) < ((0/1)/3)+(75570901/50000000) := by norm_num
    linarith
  have h := index_strict_order_from_intervals ((0/1)/3) ((0/1)/4) (nextNormalPenalty adverseNextS33Before) (nextNormalPenalty adverseNextS33Before) (75570901/50000000) (65446339/50000000)
    (treeBonus (7/5) 32 3) (treeBonus (7/5) 32 4)
    (trajectory_bonus_32_3).1 (trajectory_bonus_32_4).2 hm
  simpa only [treeIndex] using h

theorem adverseNextS33D0Cmp5 : indexScore (7/5) (controlPenalty savedCref uniformQuoteError unitRoleUnused .next) adverseNextS33Before [] (.query 5) < indexScore (7/5) (controlPenalty savedCref uniformQuoteError unitRoleUnused .next) adverseNextS33Before [] (.query 6) := by
  rw [adverseNextS33D0I5,adverseNextS33D0I6]
  have hk := adverse_next_penalty_interval 32 (by omega)
  change nextNormalPenaltyLower ≤ nextNormalPenalty adverseNextS33Before ∧ nextNormalPenalty adverseNextS33Before ≤ nextNormalPenaltyUpper at hk
  have hm : ((13/10)/5)+(29268491/25000000)-(nextNormalPenalty adverseNextS33Before) < ((0/1)/3)+(75570901/50000000)-(nextNormalPenalty adverseNextS33Before) := by
    have h : (((13/10)/5)+(29268491/25000000) : ℝ) < ((0/1)/3)+(75570901/50000000) := by norm_num
    linarith
  have h := index_strict_order_from_intervals ((0/1)/3) ((13/10)/5) (nextNormalPenalty adverseNextS33Before) (nextNormalPenalty adverseNextS33Before) (75570901/50000000) (29268491/25000000)
    (treeBonus (7/5) 32 3) (treeBonus (7/5) 32 5)
    (trajectory_bonus_32_3).1 (trajectory_bonus_32_5).2 hm
  simpa only [treeIndex] using h

theorem adverseNextS33D0Cmp7 : indexScore (7/5) (controlPenalty savedCref uniformQuoteError unitRoleUnused .next) adverseNextS33Before [] (.query 7) ≤ indexScore (7/5) (controlPenalty savedCref uniformQuoteError unitRoleUnused .next) adverseNextS33Before [] (.query 6) := by
  rw [adverseNextS33D0I7,adverseNextS33D0I6]

theorem adverseNextS33Choice0 : nativeFirstChoice (indexScore (7/5) (controlPenalty savedCref uniformQuoteError unitRoleUnused .next) adverseNextS33Before []) adverseNextS33Before [] = .query 6 := by
  apply visited_choice_from_ordered_certificate _ _ [] [.query 0,.query 1,.query 2,.query 3,.query 4,.query 5] [.query 7] (.query 6) (by decide)
  · intro a ha
    have ho : orderedLegalAvailable [] = [.query 0,.query 1,.query 2,.query 3,.query 4,.query 5,.query 6,.query 7] := by decide
    rw [ho] at ha
    simp only [List.mem_cons,List.not_mem_nil,or_false] at ha
    rcases ha with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> decide
  · intro a ha
    simp only [List.mem_cons,List.not_mem_nil,or_false] at ha
    rcases ha with rfl | rfl | rfl | rfl | rfl | rfl
    · exact adverseNextS33D0Cmp0
    · exact adverseNextS33D0Cmp1
    · exact adverseNextS33D0Cmp2
    · exact adverseNextS33D0Cmp3
    · exact adverseNextS33D0Cmp4
    · exact adverseNextS33D0Cmp5
  · intro a ha
    simp only [List.mem_cons,List.not_mem_nil,or_false] at ha
    rcases ha with rfl
    · exact adverseNextS33D0Cmp7

theorem adverseNextS33ActualEvent : nativeEvent budgetTape (7/5) (controlPenalty savedCref uniformQuoteError unitRoleUnused .next)
    (taskReward true (2/5) (1/2)) adverseNextS33Before = adverseNextEvent33 := by
  have hs0 := native_select_existing_step budgetTape (7/5) (controlPenalty savedCref uniformQuoteError unitRoleUnused .next) adverseNextS33Before 8 [] (.query 6)
    (by decide) (by decide) adverseNextS33Choice0
  have hnew := native_select_new_step budgetTape (7/5) (controlPenalty savedCref uniformQuoteError unitRoleUnused .next) adverseNextS33Before 7 [.query 6]
    [.normalRetriever 6,.normalRetriever 7,.normalRetriever 8,.normalRetriever 5,.normalRetriever 1,.normalRetriever 2,.normalRetriever 3,.normalRetriever 12,.normalRetriever 14,.normalRetriever 13,.normalRetriever 21,.normalRetriever 23,.normalRetriever 22,.normalRetriever 9,.normalRetriever 11,.normalRetriever 10,.normalRetriever 15,.normalRetriever 17,.normalRetriever 16,.normalRetriever 18,.normalRetriever 20,.normalRetriever 19,.normalRetriever 24,.normalRetriever 25,.normalRetriever 26,.normalRetriever 27,.normalRetriever 28,.normalRetriever 29] (.normalRetriever 6) (by decide) (by decide) (by decide) (by decide)
  have hs : nativeSelect budgetTape (7/5) (controlPenalty savedCref uniformQuoteError unitRoleUnused .next) adverseNextS33Before 9 [] = [.query 6,.normalRetriever 6] := by
    rw [hs0]
    change nativeSelect budgetTape (7/5) (controlPenalty savedCref uniformQuoteError unitRoleUnused .next) adverseNextS33Before 8 [.query 6] = _
    rw [hnew] <;> rfl
  have hr : repairedRollout budgetTape adverseNextS33Before 9 [.query 6,.normalRetriever 6] = [.query 6,.normalRetriever 6,.selection 0,.width 0,.stop,.reranker 0,.topm 0,.context 0,.answer 0] := by decide
  simp only [nativeEvent,hs,hr]
  rfl

def adverseNextS34Before := adverseNextProposal.take 33

theorem adverseNextS34D0I0 : indexScore (7/5) (controlPenalty savedCref uniformQuoteError unitRoleUnused .next) adverseNextS34Before [] (.query 0) = treeIndex ((0/1)/4) (7/5) (nextNormalPenalty adverseNextS34Before) 33 4 := by
  have hs : replayBackup adverseNextS34Before emptyStatistics ([]++[.query 0]) = ⟨4,(0/1)⟩ := by
    rw [replayBackup_empty_closed_form]
    simp +decide [backedEvents,adverseNextS34Before,adverseNextProposal,adverseNextEvent1,adverseNextEvent2,adverseNextEvent3,adverseNextEvent4,adverseNextEvent5,adverseNextEvent6,adverseNextEvent7,adverseNextEvent8,adverseNextEvent9,adverseNextEvent10,adverseNextEvent11,adverseNextEvent12,adverseNextEvent13,adverseNextEvent14,adverseNextEvent15,adverseNextEvent16,adverseNextEvent17,adverseNextEvent18,adverseNextEvent19,adverseNextEvent20,adverseNextEvent21,adverseNextEvent22,adverseNextEvent23,adverseNextEvent24,adverseNextEvent25,adverseNextEvent26,adverseNextEvent27,adverseNextEvent28,adverseNextEvent29,adverseNextEvent30,adverseNextEvent31,adverseNextEvent32,adverseNextEvent33,taskReward]
    <;> norm_num
  have hp : rawVisits adverseNextS34Before [] = 33 := by decide
  have hn : rawVisits adverseNextS34Before ([]++[.query 0]) = 4 := by decide
  have hz : (controlPenalty savedCref uniformQuoteError unitRoleUnused .next) adverseNextS34Before [] (.query 0) = (nextNormalPenalty adverseNextS34Before) := by
    simpa only [adverseNextS34Before,nextNormalPenalty] using AgentUCTNextExact.adverse_next_normal_root_quotes_exact 33 (by omega) 0 (by decide)
  unfold indexScore
  rw [hs,hp,hn,hz]
  simp only [BackupStat.mean]
  norm_num

theorem adverseNextS34D0I1 : indexScore (7/5) (controlPenalty savedCref uniformQuoteError unitRoleUnused .next) adverseNextS34Before [] (.query 1) = treeIndex ((0/1)/5) (7/5) 0 33 5 := by
  have hs : replayBackup adverseNextS34Before emptyStatistics ([]++[.query 1]) = ⟨5,(0/1)⟩ := by
    rw [replayBackup_empty_closed_form]
    simp +decide [backedEvents,adverseNextS34Before,adverseNextProposal,adverseNextEvent1,adverseNextEvent2,adverseNextEvent3,adverseNextEvent4,adverseNextEvent5,adverseNextEvent6,adverseNextEvent7,adverseNextEvent8,adverseNextEvent9,adverseNextEvent10,adverseNextEvent11,adverseNextEvent12,adverseNextEvent13,adverseNextEvent14,adverseNextEvent15,adverseNextEvent16,adverseNextEvent17,adverseNextEvent18,adverseNextEvent19,adverseNextEvent20,adverseNextEvent21,adverseNextEvent22,adverseNextEvent23,adverseNextEvent24,adverseNextEvent25,adverseNextEvent26,adverseNextEvent27,adverseNextEvent28,adverseNextEvent29,adverseNextEvent30,adverseNextEvent31,adverseNextEvent32,adverseNextEvent33,taskReward]
    <;> norm_num
  have hp : rawVisits adverseNextS34Before [] = 33 := by decide
  have hn : rawVisits adverseNextS34Before ([]++[.query 1]) = 5 := by decide
  have hz : (controlPenalty savedCref uniformQuoteError unitRoleUnused .next) adverseNextS34Before [] (.query 1) = 0 := by
    apply control_penalty_empty_suffix
    exact AgentUCTNextExact.adverse_next_hyde_root_suffix_empty 33 (by omega)
  unfold indexScore
  rw [hs,hp,hn,hz]
  simp only [BackupStat.mean]
  norm_num

theorem adverseNextS34D0I2 : indexScore (7/5) (controlPenalty savedCref uniformQuoteError unitRoleUnused .next) adverseNextS34Before [] (.query 2) = treeIndex ((0/1)/4) (7/5) (nextNormalPenalty adverseNextS34Before) 33 4 := by
  have hs : replayBackup adverseNextS34Before emptyStatistics ([]++[.query 2]) = ⟨4,(0/1)⟩ := by
    rw [replayBackup_empty_closed_form]
    simp +decide [backedEvents,adverseNextS34Before,adverseNextProposal,adverseNextEvent1,adverseNextEvent2,adverseNextEvent3,adverseNextEvent4,adverseNextEvent5,adverseNextEvent6,adverseNextEvent7,adverseNextEvent8,adverseNextEvent9,adverseNextEvent10,adverseNextEvent11,adverseNextEvent12,adverseNextEvent13,adverseNextEvent14,adverseNextEvent15,adverseNextEvent16,adverseNextEvent17,adverseNextEvent18,adverseNextEvent19,adverseNextEvent20,adverseNextEvent21,adverseNextEvent22,adverseNextEvent23,adverseNextEvent24,adverseNextEvent25,adverseNextEvent26,adverseNextEvent27,adverseNextEvent28,adverseNextEvent29,adverseNextEvent30,adverseNextEvent31,adverseNextEvent32,adverseNextEvent33,taskReward]
    <;> norm_num
  have hp : rawVisits adverseNextS34Before [] = 33 := by decide
  have hn : rawVisits adverseNextS34Before ([]++[.query 2]) = 4 := by decide
  have hz : (controlPenalty savedCref uniformQuoteError unitRoleUnused .next) adverseNextS34Before [] (.query 2) = (nextNormalPenalty adverseNextS34Before) := by
    simpa only [adverseNextS34Before,nextNormalPenalty] using AgentUCTNextExact.adverse_next_normal_root_quotes_exact 33 (by omega) 2 (by decide)
  unfold indexScore
  rw [hs,hp,hn,hz]
  simp only [BackupStat.mean]
  norm_num

theorem adverseNextS34D0I3 : indexScore (7/5) (controlPenalty savedCref uniformQuoteError unitRoleUnused .next) adverseNextS34Before [] (.query 3) = treeIndex ((0/1)/4) (7/5) (nextNormalPenalty adverseNextS34Before) 33 4 := by
  have hs : replayBackup adverseNextS34Before emptyStatistics ([]++[.query 3]) = ⟨4,(0/1)⟩ := by
    rw [replayBackup_empty_closed_form]
    simp +decide [backedEvents,adverseNextS34Before,adverseNextProposal,adverseNextEvent1,adverseNextEvent2,adverseNextEvent3,adverseNextEvent4,adverseNextEvent5,adverseNextEvent6,adverseNextEvent7,adverseNextEvent8,adverseNextEvent9,adverseNextEvent10,adverseNextEvent11,adverseNextEvent12,adverseNextEvent13,adverseNextEvent14,adverseNextEvent15,adverseNextEvent16,adverseNextEvent17,adverseNextEvent18,adverseNextEvent19,adverseNextEvent20,adverseNextEvent21,adverseNextEvent22,adverseNextEvent23,adverseNextEvent24,adverseNextEvent25,adverseNextEvent26,adverseNextEvent27,adverseNextEvent28,adverseNextEvent29,adverseNextEvent30,adverseNextEvent31,adverseNextEvent32,adverseNextEvent33,taskReward]
    <;> norm_num
  have hp : rawVisits adverseNextS34Before [] = 33 := by decide
  have hn : rawVisits adverseNextS34Before ([]++[.query 3]) = 4 := by decide
  have hz : (controlPenalty savedCref uniformQuoteError unitRoleUnused .next) adverseNextS34Before [] (.query 3) = (nextNormalPenalty adverseNextS34Before) := by
    simpa only [adverseNextS34Before,nextNormalPenalty] using AgentUCTNextExact.adverse_next_normal_root_quotes_exact 33 (by omega) 3 (by decide)
  unfold indexScore
  rw [hs,hp,hn,hz]
  simp only [BackupStat.mean]
  norm_num

theorem adverseNextS34D0I4 : indexScore (7/5) (controlPenalty savedCref uniformQuoteError unitRoleUnused .next) adverseNextS34Before [] (.query 4) = treeIndex ((0/1)/4) (7/5) (nextNormalPenalty adverseNextS34Before) 33 4 := by
  have hs : replayBackup adverseNextS34Before emptyStatistics ([]++[.query 4]) = ⟨4,(0/1)⟩ := by
    rw [replayBackup_empty_closed_form]
    simp +decide [backedEvents,adverseNextS34Before,adverseNextProposal,adverseNextEvent1,adverseNextEvent2,adverseNextEvent3,adverseNextEvent4,adverseNextEvent5,adverseNextEvent6,adverseNextEvent7,adverseNextEvent8,adverseNextEvent9,adverseNextEvent10,adverseNextEvent11,adverseNextEvent12,adverseNextEvent13,adverseNextEvent14,adverseNextEvent15,adverseNextEvent16,adverseNextEvent17,adverseNextEvent18,adverseNextEvent19,adverseNextEvent20,adverseNextEvent21,adverseNextEvent22,adverseNextEvent23,adverseNextEvent24,adverseNextEvent25,adverseNextEvent26,adverseNextEvent27,adverseNextEvent28,adverseNextEvent29,adverseNextEvent30,adverseNextEvent31,adverseNextEvent32,adverseNextEvent33,taskReward]
    <;> norm_num
  have hp : rawVisits adverseNextS34Before [] = 33 := by decide
  have hn : rawVisits adverseNextS34Before ([]++[.query 4]) = 4 := by decide
  have hz : (controlPenalty savedCref uniformQuoteError unitRoleUnused .next) adverseNextS34Before [] (.query 4) = (nextNormalPenalty adverseNextS34Before) := by
    simpa only [adverseNextS34Before,nextNormalPenalty] using AgentUCTNextExact.adverse_next_normal_root_quotes_exact 33 (by omega) 4 (by decide)
  unfold indexScore
  rw [hs,hp,hn,hz]
  simp only [BackupStat.mean]
  norm_num

theorem adverseNextS34D0I5 : indexScore (7/5) (controlPenalty savedCref uniformQuoteError unitRoleUnused .next) adverseNextS34Before [] (.query 5) = treeIndex ((13/10)/5) (7/5) (nextNormalPenalty adverseNextS34Before) 33 5 := by
  have hs : replayBackup adverseNextS34Before emptyStatistics ([]++[.query 5]) = ⟨5,(13/10)⟩ := by
    rw [replayBackup_empty_closed_form]
    simp +decide [backedEvents,adverseNextS34Before,adverseNextProposal,adverseNextEvent1,adverseNextEvent2,adverseNextEvent3,adverseNextEvent4,adverseNextEvent5,adverseNextEvent6,adverseNextEvent7,adverseNextEvent8,adverseNextEvent9,adverseNextEvent10,adverseNextEvent11,adverseNextEvent12,adverseNextEvent13,adverseNextEvent14,adverseNextEvent15,adverseNextEvent16,adverseNextEvent17,adverseNextEvent18,adverseNextEvent19,adverseNextEvent20,adverseNextEvent21,adverseNextEvent22,adverseNextEvent23,adverseNextEvent24,adverseNextEvent25,adverseNextEvent26,adverseNextEvent27,adverseNextEvent28,adverseNextEvent29,adverseNextEvent30,adverseNextEvent31,adverseNextEvent32,adverseNextEvent33,taskReward]
    <;> norm_num
  have hp : rawVisits adverseNextS34Before [] = 33 := by decide
  have hn : rawVisits adverseNextS34Before ([]++[.query 5]) = 5 := by decide
  have hz : (controlPenalty savedCref uniformQuoteError unitRoleUnused .next) adverseNextS34Before [] (.query 5) = (nextNormalPenalty adverseNextS34Before) := by
    simpa only [adverseNextS34Before,nextNormalPenalty] using AgentUCTNextExact.adverse_next_normal_root_quotes_exact 33 (by omega) 5 (by decide)
  unfold indexScore
  rw [hs,hp,hn,hz]
  simp only [BackupStat.mean]
  norm_num

theorem adverseNextS34D0I6 : indexScore (7/5) (controlPenalty savedCref uniformQuoteError unitRoleUnused .next) adverseNextS34Before [] (.query 6) = treeIndex ((0/1)/4) (7/5) (nextNormalPenalty adverseNextS34Before) 33 4 := by
  have hs : replayBackup adverseNextS34Before emptyStatistics ([]++[.query 6]) = ⟨4,(0/1)⟩ := by
    rw [replayBackup_empty_closed_form]
    simp +decide [backedEvents,adverseNextS34Before,adverseNextProposal,adverseNextEvent1,adverseNextEvent2,adverseNextEvent3,adverseNextEvent4,adverseNextEvent5,adverseNextEvent6,adverseNextEvent7,adverseNextEvent8,adverseNextEvent9,adverseNextEvent10,adverseNextEvent11,adverseNextEvent12,adverseNextEvent13,adverseNextEvent14,adverseNextEvent15,adverseNextEvent16,adverseNextEvent17,adverseNextEvent18,adverseNextEvent19,adverseNextEvent20,adverseNextEvent21,adverseNextEvent22,adverseNextEvent23,adverseNextEvent24,adverseNextEvent25,adverseNextEvent26,adverseNextEvent27,adverseNextEvent28,adverseNextEvent29,adverseNextEvent30,adverseNextEvent31,adverseNextEvent32,adverseNextEvent33,taskReward]
    <;> norm_num
  have hp : rawVisits adverseNextS34Before [] = 33 := by decide
  have hn : rawVisits adverseNextS34Before ([]++[.query 6]) = 4 := by decide
  have hz : (controlPenalty savedCref uniformQuoteError unitRoleUnused .next) adverseNextS34Before [] (.query 6) = (nextNormalPenalty adverseNextS34Before) := by
    simpa only [adverseNextS34Before,nextNormalPenalty] using AgentUCTNextExact.adverse_next_normal_root_quotes_exact 33 (by omega) 6 (by decide)
  unfold indexScore
  rw [hs,hp,hn,hz]
  simp only [BackupStat.mean]
  norm_num

theorem adverseNextS34D0I7 : indexScore (7/5) (controlPenalty savedCref uniformQuoteError unitRoleUnused .next) adverseNextS34Before [] (.query 7) = treeIndex ((0/1)/3) (7/5) (nextNormalPenalty adverseNextS34Before) 33 3 := by
  have hs : replayBackup adverseNextS34Before emptyStatistics ([]++[.query 7]) = ⟨3,(0/1)⟩ := by
    rw [replayBackup_empty_closed_form]
    simp +decide [backedEvents,adverseNextS34Before,adverseNextProposal,adverseNextEvent1,adverseNextEvent2,adverseNextEvent3,adverseNextEvent4,adverseNextEvent5,adverseNextEvent6,adverseNextEvent7,adverseNextEvent8,adverseNextEvent9,adverseNextEvent10,adverseNextEvent11,adverseNextEvent12,adverseNextEvent13,adverseNextEvent14,adverseNextEvent15,adverseNextEvent16,adverseNextEvent17,adverseNextEvent18,adverseNextEvent19,adverseNextEvent20,adverseNextEvent21,adverseNextEvent22,adverseNextEvent23,adverseNextEvent24,adverseNextEvent25,adverseNextEvent26,adverseNextEvent27,adverseNextEvent28,adverseNextEvent29,adverseNextEvent30,adverseNextEvent31,adverseNextEvent32,adverseNextEvent33,taskReward]
    <;> norm_num
  have hp : rawVisits adverseNextS34Before [] = 33 := by decide
  have hn : rawVisits adverseNextS34Before ([]++[.query 7]) = 3 := by decide
  have hz : (controlPenalty savedCref uniformQuoteError unitRoleUnused .next) adverseNextS34Before [] (.query 7) = (nextNormalPenalty adverseNextS34Before) := by
    simpa only [adverseNextS34Before,nextNormalPenalty] using AgentUCTNextExact.adverse_next_normal_root_quotes_exact 33 (by omega) 7 (by decide)
  unfold indexScore
  rw [hs,hp,hn,hz]
  simp only [BackupStat.mean]
  norm_num

theorem adverseNextS34D0Cmp0 : indexScore (7/5) (controlPenalty savedCref uniformQuoteError unitRoleUnused .next) adverseNextS34Before [] (.query 0) < indexScore (7/5) (controlPenalty savedCref uniformQuoteError unitRoleUnused .next) adverseNextS34Before [] (.query 7) := by
  rw [adverseNextS34D0I0,adverseNextS34D0I7]
  have hk := adverse_next_penalty_interval 33 (by omega)
  change nextNormalPenaltyLower ≤ nextNormalPenalty adverseNextS34Before ∧ nextNormalPenalty adverseNextS34Before ≤ nextNormalPenaltyUpper at hk
  have hm : ((0/1)/4)+(8215641/6250000)-(nextNormalPenalty adverseNextS34Before) < ((0/1)/3)+(75892831/50000000)-(nextNormalPenalty adverseNextS34Before) := by
    have h : (((0/1)/4)+(8215641/6250000) : ℝ) < ((0/1)/3)+(75892831/50000000) := by norm_num
    linarith
  have h := index_strict_order_from_intervals ((0/1)/3) ((0/1)/4) (nextNormalPenalty adverseNextS34Before) (nextNormalPenalty adverseNextS34Before) (75892831/50000000) (8215641/6250000)
    (treeBonus (7/5) 33 3) (treeBonus (7/5) 33 4)
    (trajectory_bonus_33_3).1 (trajectory_bonus_33_4).2 hm
  simpa only [treeIndex] using h

theorem adverseNextS34D0Cmp1 : indexScore (7/5) (controlPenalty savedCref uniformQuoteError unitRoleUnused .next) adverseNextS34Before [] (.query 1) < indexScore (7/5) (controlPenalty savedCref uniformQuoteError unitRoleUnused .next) adverseNextS34Before [] (.query 7) := by
  rw [adverseNextS34D0I1,adverseNextS34D0I7]
  have hk := adverse_next_penalty_interval 33 (by omega)
  change nextNormalPenaltyLower ≤ nextNormalPenalty adverseNextS34Before ∧ nextNormalPenalty adverseNextS34Before ≤ nextNormalPenaltyUpper at hk
  have hm : ((0/1)/5)+(58786343/50000000)-0 < ((0/1)/3)+(75892831/50000000)-(nextNormalPenalty adverseNextS34Before) := by
    have h : ((0/1)/5)+(58786343/50000000) < ((0/1)/3)+(75892831/50000000)-nextNormalPenaltyUpper := by norm_num [nextNormalPenaltyUpper,savedCref,uniformQuoteError]
    linarith [hk.2]
  have h := index_strict_order_from_intervals ((0/1)/3) ((0/1)/5) (nextNormalPenalty adverseNextS34Before) 0 (75892831/50000000) (58786343/50000000)
    (treeBonus (7/5) 33 3) (treeBonus (7/5) 33 5)
    (trajectory_bonus_33_3).1 (trajectory_bonus_33_5).2 hm
  simpa only [treeIndex] using h

theorem adverseNextS34D0Cmp2 : indexScore (7/5) (controlPenalty savedCref uniformQuoteError unitRoleUnused .next) adverseNextS34Before [] (.query 2) < indexScore (7/5) (controlPenalty savedCref uniformQuoteError unitRoleUnused .next) adverseNextS34Before [] (.query 7) := by
  rw [adverseNextS34D0I2,adverseNextS34D0I7]
  have hk := adverse_next_penalty_interval 33 (by omega)
  change nextNormalPenaltyLower ≤ nextNormalPenalty adverseNextS34Before ∧ nextNormalPenalty adverseNextS34Before ≤ nextNormalPenaltyUpper at hk
  have hm : ((0/1)/4)+(8215641/6250000)-(nextNormalPenalty adverseNextS34Before) < ((0/1)/3)+(75892831/50000000)-(nextNormalPenalty adverseNextS34Before) := by
    have h : (((0/1)/4)+(8215641/6250000) : ℝ) < ((0/1)/3)+(75892831/50000000) := by norm_num
    linarith
  have h := index_strict_order_from_intervals ((0/1)/3) ((0/1)/4) (nextNormalPenalty adverseNextS34Before) (nextNormalPenalty adverseNextS34Before) (75892831/50000000) (8215641/6250000)
    (treeBonus (7/5) 33 3) (treeBonus (7/5) 33 4)
    (trajectory_bonus_33_3).1 (trajectory_bonus_33_4).2 hm
  simpa only [treeIndex] using h

theorem adverseNextS34D0Cmp3 : indexScore (7/5) (controlPenalty savedCref uniformQuoteError unitRoleUnused .next) adverseNextS34Before [] (.query 3) < indexScore (7/5) (controlPenalty savedCref uniformQuoteError unitRoleUnused .next) adverseNextS34Before [] (.query 7) := by
  rw [adverseNextS34D0I3,adverseNextS34D0I7]
  have hk := adverse_next_penalty_interval 33 (by omega)
  change nextNormalPenaltyLower ≤ nextNormalPenalty adverseNextS34Before ∧ nextNormalPenalty adverseNextS34Before ≤ nextNormalPenaltyUpper at hk
  have hm : ((0/1)/4)+(8215641/6250000)-(nextNormalPenalty adverseNextS34Before) < ((0/1)/3)+(75892831/50000000)-(nextNormalPenalty adverseNextS34Before) := by
    have h : (((0/1)/4)+(8215641/6250000) : ℝ) < ((0/1)/3)+(75892831/50000000) := by norm_num
    linarith
  have h := index_strict_order_from_intervals ((0/1)/3) ((0/1)/4) (nextNormalPenalty adverseNextS34Before) (nextNormalPenalty adverseNextS34Before) (75892831/50000000) (8215641/6250000)
    (treeBonus (7/5) 33 3) (treeBonus (7/5) 33 4)
    (trajectory_bonus_33_3).1 (trajectory_bonus_33_4).2 hm
  simpa only [treeIndex] using h

theorem adverseNextS34D0Cmp4 : indexScore (7/5) (controlPenalty savedCref uniformQuoteError unitRoleUnused .next) adverseNextS34Before [] (.query 4) < indexScore (7/5) (controlPenalty savedCref uniformQuoteError unitRoleUnused .next) adverseNextS34Before [] (.query 7) := by
  rw [adverseNextS34D0I4,adverseNextS34D0I7]
  have hk := adverse_next_penalty_interval 33 (by omega)
  change nextNormalPenaltyLower ≤ nextNormalPenalty adverseNextS34Before ∧ nextNormalPenalty adverseNextS34Before ≤ nextNormalPenaltyUpper at hk
  have hm : ((0/1)/4)+(8215641/6250000)-(nextNormalPenalty adverseNextS34Before) < ((0/1)/3)+(75892831/50000000)-(nextNormalPenalty adverseNextS34Before) := by
    have h : (((0/1)/4)+(8215641/6250000) : ℝ) < ((0/1)/3)+(75892831/50000000) := by norm_num
    linarith
  have h := index_strict_order_from_intervals ((0/1)/3) ((0/1)/4) (nextNormalPenalty adverseNextS34Before) (nextNormalPenalty adverseNextS34Before) (75892831/50000000) (8215641/6250000)
    (treeBonus (7/5) 33 3) (treeBonus (7/5) 33 4)
    (trajectory_bonus_33_3).1 (trajectory_bonus_33_4).2 hm
  simpa only [treeIndex] using h

theorem adverseNextS34D0Cmp5 : indexScore (7/5) (controlPenalty savedCref uniformQuoteError unitRoleUnused .next) adverseNextS34Before [] (.query 5) < indexScore (7/5) (controlPenalty savedCref uniformQuoteError unitRoleUnused .next) adverseNextS34Before [] (.query 7) := by
  rw [adverseNextS34D0I5,adverseNextS34D0I7]
  have hk := adverse_next_penalty_interval 33 (by omega)
  change nextNormalPenaltyLower ≤ nextNormalPenalty adverseNextS34Before ∧ nextNormalPenalty adverseNextS34Before ≤ nextNormalPenaltyUpper at hk
  have hm : ((13/10)/5)+(58786343/50000000)-(nextNormalPenalty adverseNextS34Before) < ((0/1)/3)+(75892831/50000000)-(nextNormalPenalty adverseNextS34Before) := by
    have h : (((13/10)/5)+(58786343/50000000) : ℝ) < ((0/1)/3)+(75892831/50000000) := by norm_num
    linarith
  have h := index_strict_order_from_intervals ((0/1)/3) ((13/10)/5) (nextNormalPenalty adverseNextS34Before) (nextNormalPenalty adverseNextS34Before) (75892831/50000000) (58786343/50000000)
    (treeBonus (7/5) 33 3) (treeBonus (7/5) 33 5)
    (trajectory_bonus_33_3).1 (trajectory_bonus_33_5).2 hm
  simpa only [treeIndex] using h

theorem adverseNextS34D0Cmp6 : indexScore (7/5) (controlPenalty savedCref uniformQuoteError unitRoleUnused .next) adverseNextS34Before [] (.query 6) < indexScore (7/5) (controlPenalty savedCref uniformQuoteError unitRoleUnused .next) adverseNextS34Before [] (.query 7) := by
  rw [adverseNextS34D0I6,adverseNextS34D0I7]
  have hk := adverse_next_penalty_interval 33 (by omega)
  change nextNormalPenaltyLower ≤ nextNormalPenalty adverseNextS34Before ∧ nextNormalPenalty adverseNextS34Before ≤ nextNormalPenaltyUpper at hk
  have hm : ((0/1)/4)+(8215641/6250000)-(nextNormalPenalty adverseNextS34Before) < ((0/1)/3)+(75892831/50000000)-(nextNormalPenalty adverseNextS34Before) := by
    have h : (((0/1)/4)+(8215641/6250000) : ℝ) < ((0/1)/3)+(75892831/50000000) := by norm_num
    linarith
  have h := index_strict_order_from_intervals ((0/1)/3) ((0/1)/4) (nextNormalPenalty adverseNextS34Before) (nextNormalPenalty adverseNextS34Before) (75892831/50000000) (8215641/6250000)
    (treeBonus (7/5) 33 3) (treeBonus (7/5) 33 4)
    (trajectory_bonus_33_3).1 (trajectory_bonus_33_4).2 hm
  simpa only [treeIndex] using h

theorem adverseNextS34Choice0 : nativeFirstChoice (indexScore (7/5) (controlPenalty savedCref uniformQuoteError unitRoleUnused .next) adverseNextS34Before []) adverseNextS34Before [] = .query 7 := by
  apply visited_choice_from_ordered_certificate _ _ [] [.query 0,.query 1,.query 2,.query 3,.query 4,.query 5,.query 6] [] (.query 7) (by decide)
  · intro a ha
    have ho : orderedLegalAvailable [] = [.query 0,.query 1,.query 2,.query 3,.query 4,.query 5,.query 6,.query 7] := by decide
    rw [ho] at ha
    simp only [List.mem_cons,List.not_mem_nil,or_false] at ha
    rcases ha with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> decide
  · intro a ha
    simp only [List.mem_cons,List.not_mem_nil,or_false] at ha
    rcases ha with rfl | rfl | rfl | rfl | rfl | rfl | rfl
    · exact adverseNextS34D0Cmp0
    · exact adverseNextS34D0Cmp1
    · exact adverseNextS34D0Cmp2
    · exact adverseNextS34D0Cmp3
    · exact adverseNextS34D0Cmp4
    · exact adverseNextS34D0Cmp5
    · exact adverseNextS34D0Cmp6
  · simp

theorem adverseNextS34ActualEvent : nativeEvent budgetTape (7/5) (controlPenalty savedCref uniformQuoteError unitRoleUnused .next)
    (taskReward true (2/5) (1/2)) adverseNextS34Before = adverseNextEvent34 := by
  have hs0 := native_select_existing_step budgetTape (7/5) (controlPenalty savedCref uniformQuoteError unitRoleUnused .next) adverseNextS34Before 8 [] (.query 7)
    (by decide) (by decide) adverseNextS34Choice0
  have hnew := native_select_new_step budgetTape (7/5) (controlPenalty savedCref uniformQuoteError unitRoleUnused .next) adverseNextS34Before 7 [.query 7]
    [.normalRetriever 6,.normalRetriever 7,.normalRetriever 8,.normalRetriever 5,.normalRetriever 1,.normalRetriever 2,.normalRetriever 3,.normalRetriever 12,.normalRetriever 14,.normalRetriever 13,.normalRetriever 21,.normalRetriever 23,.normalRetriever 22,.normalRetriever 9,.normalRetriever 11,.normalRetriever 10,.normalRetriever 15,.normalRetriever 17,.normalRetriever 16,.normalRetriever 18,.normalRetriever 20,.normalRetriever 19,.normalRetriever 24,.normalRetriever 25,.normalRetriever 26,.normalRetriever 27,.normalRetriever 28,.normalRetriever 29] (.normalRetriever 6) (by decide) (by decide) (by decide) (by decide)
  have hs : nativeSelect budgetTape (7/5) (controlPenalty savedCref uniformQuoteError unitRoleUnused .next) adverseNextS34Before 9 [] = [.query 7,.normalRetriever 6] := by
    rw [hs0]
    change nativeSelect budgetTape (7/5) (controlPenalty savedCref uniformQuoteError unitRoleUnused .next) adverseNextS34Before 8 [.query 7] = _
    rw [hnew] <;> rfl
  have hr : repairedRollout budgetTape adverseNextS34Before 9 [.query 7,.normalRetriever 6] = [.query 7,.normalRetriever 6,.selection 0,.width 0,.stop,.reranker 0,.topm 0,.context 0,.answer 0] := by decide
  simp only [nativeEvent,hs,hr]
  rfl

def adverseNextS35Before := adverseNextProposal.take 34

theorem adverseNextS35D0I0 : indexScore (7/5) (controlPenalty savedCref uniformQuoteError unitRoleUnused .next) adverseNextS35Before [] (.query 0) = treeIndex ((0/1)/4) (7/5) (nextNormalPenalty adverseNextS35Before) 34 4 := by
  have hs : replayBackup adverseNextS35Before emptyStatistics ([]++[.query 0]) = ⟨4,(0/1)⟩ := by
    rw [replayBackup_empty_closed_form]
    simp +decide [backedEvents,adverseNextS35Before,adverseNextProposal,adverseNextEvent1,adverseNextEvent2,adverseNextEvent3,adverseNextEvent4,adverseNextEvent5,adverseNextEvent6,adverseNextEvent7,adverseNextEvent8,adverseNextEvent9,adverseNextEvent10,adverseNextEvent11,adverseNextEvent12,adverseNextEvent13,adverseNextEvent14,adverseNextEvent15,adverseNextEvent16,adverseNextEvent17,adverseNextEvent18,adverseNextEvent19,adverseNextEvent20,adverseNextEvent21,adverseNextEvent22,adverseNextEvent23,adverseNextEvent24,adverseNextEvent25,adverseNextEvent26,adverseNextEvent27,adverseNextEvent28,adverseNextEvent29,adverseNextEvent30,adverseNextEvent31,adverseNextEvent32,adverseNextEvent33,adverseNextEvent34,taskReward]
    <;> norm_num
  have hp : rawVisits adverseNextS35Before [] = 34 := by decide
  have hn : rawVisits adverseNextS35Before ([]++[.query 0]) = 4 := by decide
  have hz : (controlPenalty savedCref uniformQuoteError unitRoleUnused .next) adverseNextS35Before [] (.query 0) = (nextNormalPenalty adverseNextS35Before) := by
    simpa only [adverseNextS35Before,nextNormalPenalty] using AgentUCTNextExact.adverse_next_normal_root_quotes_exact 34 (by omega) 0 (by decide)
  unfold indexScore
  rw [hs,hp,hn,hz]
  simp only [BackupStat.mean]
  norm_num

theorem adverseNextS35D0I1 : indexScore (7/5) (controlPenalty savedCref uniformQuoteError unitRoleUnused .next) adverseNextS35Before [] (.query 1) = treeIndex ((0/1)/5) (7/5) 0 34 5 := by
  have hs : replayBackup adverseNextS35Before emptyStatistics ([]++[.query 1]) = ⟨5,(0/1)⟩ := by
    rw [replayBackup_empty_closed_form]
    simp +decide [backedEvents,adverseNextS35Before,adverseNextProposal,adverseNextEvent1,adverseNextEvent2,adverseNextEvent3,adverseNextEvent4,adverseNextEvent5,adverseNextEvent6,adverseNextEvent7,adverseNextEvent8,adverseNextEvent9,adverseNextEvent10,adverseNextEvent11,adverseNextEvent12,adverseNextEvent13,adverseNextEvent14,adverseNextEvent15,adverseNextEvent16,adverseNextEvent17,adverseNextEvent18,adverseNextEvent19,adverseNextEvent20,adverseNextEvent21,adverseNextEvent22,adverseNextEvent23,adverseNextEvent24,adverseNextEvent25,adverseNextEvent26,adverseNextEvent27,adverseNextEvent28,adverseNextEvent29,adverseNextEvent30,adverseNextEvent31,adverseNextEvent32,adverseNextEvent33,adverseNextEvent34,taskReward]
    <;> norm_num
  have hp : rawVisits adverseNextS35Before [] = 34 := by decide
  have hn : rawVisits adverseNextS35Before ([]++[.query 1]) = 5 := by decide
  have hz : (controlPenalty savedCref uniformQuoteError unitRoleUnused .next) adverseNextS35Before [] (.query 1) = 0 := by
    apply control_penalty_empty_suffix
    exact AgentUCTNextExact.adverse_next_hyde_root_suffix_empty 34 (by omega)
  unfold indexScore
  rw [hs,hp,hn,hz]
  simp only [BackupStat.mean]
  norm_num

theorem adverseNextS35D0I2 : indexScore (7/5) (controlPenalty savedCref uniformQuoteError unitRoleUnused .next) adverseNextS35Before [] (.query 2) = treeIndex ((0/1)/4) (7/5) (nextNormalPenalty adverseNextS35Before) 34 4 := by
  have hs : replayBackup adverseNextS35Before emptyStatistics ([]++[.query 2]) = ⟨4,(0/1)⟩ := by
    rw [replayBackup_empty_closed_form]
    simp +decide [backedEvents,adverseNextS35Before,adverseNextProposal,adverseNextEvent1,adverseNextEvent2,adverseNextEvent3,adverseNextEvent4,adverseNextEvent5,adverseNextEvent6,adverseNextEvent7,adverseNextEvent8,adverseNextEvent9,adverseNextEvent10,adverseNextEvent11,adverseNextEvent12,adverseNextEvent13,adverseNextEvent14,adverseNextEvent15,adverseNextEvent16,adverseNextEvent17,adverseNextEvent18,adverseNextEvent19,adverseNextEvent20,adverseNextEvent21,adverseNextEvent22,adverseNextEvent23,adverseNextEvent24,adverseNextEvent25,adverseNextEvent26,adverseNextEvent27,adverseNextEvent28,adverseNextEvent29,adverseNextEvent30,adverseNextEvent31,adverseNextEvent32,adverseNextEvent33,adverseNextEvent34,taskReward]
    <;> norm_num
  have hp : rawVisits adverseNextS35Before [] = 34 := by decide
  have hn : rawVisits adverseNextS35Before ([]++[.query 2]) = 4 := by decide
  have hz : (controlPenalty savedCref uniformQuoteError unitRoleUnused .next) adverseNextS35Before [] (.query 2) = (nextNormalPenalty adverseNextS35Before) := by
    simpa only [adverseNextS35Before,nextNormalPenalty] using AgentUCTNextExact.adverse_next_normal_root_quotes_exact 34 (by omega) 2 (by decide)
  unfold indexScore
  rw [hs,hp,hn,hz]
  simp only [BackupStat.mean]
  norm_num

theorem adverseNextS35D0I3 : indexScore (7/5) (controlPenalty savedCref uniformQuoteError unitRoleUnused .next) adverseNextS35Before [] (.query 3) = treeIndex ((0/1)/4) (7/5) (nextNormalPenalty adverseNextS35Before) 34 4 := by
  have hs : replayBackup adverseNextS35Before emptyStatistics ([]++[.query 3]) = ⟨4,(0/1)⟩ := by
    rw [replayBackup_empty_closed_form]
    simp +decide [backedEvents,adverseNextS35Before,adverseNextProposal,adverseNextEvent1,adverseNextEvent2,adverseNextEvent3,adverseNextEvent4,adverseNextEvent5,adverseNextEvent6,adverseNextEvent7,adverseNextEvent8,adverseNextEvent9,adverseNextEvent10,adverseNextEvent11,adverseNextEvent12,adverseNextEvent13,adverseNextEvent14,adverseNextEvent15,adverseNextEvent16,adverseNextEvent17,adverseNextEvent18,adverseNextEvent19,adverseNextEvent20,adverseNextEvent21,adverseNextEvent22,adverseNextEvent23,adverseNextEvent24,adverseNextEvent25,adverseNextEvent26,adverseNextEvent27,adverseNextEvent28,adverseNextEvent29,adverseNextEvent30,adverseNextEvent31,adverseNextEvent32,adverseNextEvent33,adverseNextEvent34,taskReward]
    <;> norm_num
  have hp : rawVisits adverseNextS35Before [] = 34 := by decide
  have hn : rawVisits adverseNextS35Before ([]++[.query 3]) = 4 := by decide
  have hz : (controlPenalty savedCref uniformQuoteError unitRoleUnused .next) adverseNextS35Before [] (.query 3) = (nextNormalPenalty adverseNextS35Before) := by
    simpa only [adverseNextS35Before,nextNormalPenalty] using AgentUCTNextExact.adverse_next_normal_root_quotes_exact 34 (by omega) 3 (by decide)
  unfold indexScore
  rw [hs,hp,hn,hz]
  simp only [BackupStat.mean]
  norm_num

theorem adverseNextS35D0I4 : indexScore (7/5) (controlPenalty savedCref uniformQuoteError unitRoleUnused .next) adverseNextS35Before [] (.query 4) = treeIndex ((0/1)/4) (7/5) (nextNormalPenalty adverseNextS35Before) 34 4 := by
  have hs : replayBackup adverseNextS35Before emptyStatistics ([]++[.query 4]) = ⟨4,(0/1)⟩ := by
    rw [replayBackup_empty_closed_form]
    simp +decide [backedEvents,adverseNextS35Before,adverseNextProposal,adverseNextEvent1,adverseNextEvent2,adverseNextEvent3,adverseNextEvent4,adverseNextEvent5,adverseNextEvent6,adverseNextEvent7,adverseNextEvent8,adverseNextEvent9,adverseNextEvent10,adverseNextEvent11,adverseNextEvent12,adverseNextEvent13,adverseNextEvent14,adverseNextEvent15,adverseNextEvent16,adverseNextEvent17,adverseNextEvent18,adverseNextEvent19,adverseNextEvent20,adverseNextEvent21,adverseNextEvent22,adverseNextEvent23,adverseNextEvent24,adverseNextEvent25,adverseNextEvent26,adverseNextEvent27,adverseNextEvent28,adverseNextEvent29,adverseNextEvent30,adverseNextEvent31,adverseNextEvent32,adverseNextEvent33,adverseNextEvent34,taskReward]
    <;> norm_num
  have hp : rawVisits adverseNextS35Before [] = 34 := by decide
  have hn : rawVisits adverseNextS35Before ([]++[.query 4]) = 4 := by decide
  have hz : (controlPenalty savedCref uniformQuoteError unitRoleUnused .next) adverseNextS35Before [] (.query 4) = (nextNormalPenalty adverseNextS35Before) := by
    simpa only [adverseNextS35Before,nextNormalPenalty] using AgentUCTNextExact.adverse_next_normal_root_quotes_exact 34 (by omega) 4 (by decide)
  unfold indexScore
  rw [hs,hp,hn,hz]
  simp only [BackupStat.mean]
  norm_num

theorem adverseNextS35D0I5 : indexScore (7/5) (controlPenalty savedCref uniformQuoteError unitRoleUnused .next) adverseNextS35Before [] (.query 5) = treeIndex ((13/10)/5) (7/5) (nextNormalPenalty adverseNextS35Before) 34 5 := by
  have hs : replayBackup adverseNextS35Before emptyStatistics ([]++[.query 5]) = ⟨5,(13/10)⟩ := by
    rw [replayBackup_empty_closed_form]
    simp +decide [backedEvents,adverseNextS35Before,adverseNextProposal,adverseNextEvent1,adverseNextEvent2,adverseNextEvent3,adverseNextEvent4,adverseNextEvent5,adverseNextEvent6,adverseNextEvent7,adverseNextEvent8,adverseNextEvent9,adverseNextEvent10,adverseNextEvent11,adverseNextEvent12,adverseNextEvent13,adverseNextEvent14,adverseNextEvent15,adverseNextEvent16,adverseNextEvent17,adverseNextEvent18,adverseNextEvent19,adverseNextEvent20,adverseNextEvent21,adverseNextEvent22,adverseNextEvent23,adverseNextEvent24,adverseNextEvent25,adverseNextEvent26,adverseNextEvent27,adverseNextEvent28,adverseNextEvent29,adverseNextEvent30,adverseNextEvent31,adverseNextEvent32,adverseNextEvent33,adverseNextEvent34,taskReward]
    <;> norm_num
  have hp : rawVisits adverseNextS35Before [] = 34 := by decide
  have hn : rawVisits adverseNextS35Before ([]++[.query 5]) = 5 := by decide
  have hz : (controlPenalty savedCref uniformQuoteError unitRoleUnused .next) adverseNextS35Before [] (.query 5) = (nextNormalPenalty adverseNextS35Before) := by
    simpa only [adverseNextS35Before,nextNormalPenalty] using AgentUCTNextExact.adverse_next_normal_root_quotes_exact 34 (by omega) 5 (by decide)
  unfold indexScore
  rw [hs,hp,hn,hz]
  simp only [BackupStat.mean]
  norm_num

theorem adverseNextS35D0I6 : indexScore (7/5) (controlPenalty savedCref uniformQuoteError unitRoleUnused .next) adverseNextS35Before [] (.query 6) = treeIndex ((0/1)/4) (7/5) (nextNormalPenalty adverseNextS35Before) 34 4 := by
  have hs : replayBackup adverseNextS35Before emptyStatistics ([]++[.query 6]) = ⟨4,(0/1)⟩ := by
    rw [replayBackup_empty_closed_form]
    simp +decide [backedEvents,adverseNextS35Before,adverseNextProposal,adverseNextEvent1,adverseNextEvent2,adverseNextEvent3,adverseNextEvent4,adverseNextEvent5,adverseNextEvent6,adverseNextEvent7,adverseNextEvent8,adverseNextEvent9,adverseNextEvent10,adverseNextEvent11,adverseNextEvent12,adverseNextEvent13,adverseNextEvent14,adverseNextEvent15,adverseNextEvent16,adverseNextEvent17,adverseNextEvent18,adverseNextEvent19,adverseNextEvent20,adverseNextEvent21,adverseNextEvent22,adverseNextEvent23,adverseNextEvent24,adverseNextEvent25,adverseNextEvent26,adverseNextEvent27,adverseNextEvent28,adverseNextEvent29,adverseNextEvent30,adverseNextEvent31,adverseNextEvent32,adverseNextEvent33,adverseNextEvent34,taskReward]
    <;> norm_num
  have hp : rawVisits adverseNextS35Before [] = 34 := by decide
  have hn : rawVisits adverseNextS35Before ([]++[.query 6]) = 4 := by decide
  have hz : (controlPenalty savedCref uniformQuoteError unitRoleUnused .next) adverseNextS35Before [] (.query 6) = (nextNormalPenalty adverseNextS35Before) := by
    simpa only [adverseNextS35Before,nextNormalPenalty] using AgentUCTNextExact.adverse_next_normal_root_quotes_exact 34 (by omega) 6 (by decide)
  unfold indexScore
  rw [hs,hp,hn,hz]
  simp only [BackupStat.mean]
  norm_num

theorem adverseNextS35D0I7 : indexScore (7/5) (controlPenalty savedCref uniformQuoteError unitRoleUnused .next) adverseNextS35Before [] (.query 7) = treeIndex ((0/1)/4) (7/5) (nextNormalPenalty adverseNextS35Before) 34 4 := by
  have hs : replayBackup adverseNextS35Before emptyStatistics ([]++[.query 7]) = ⟨4,(0/1)⟩ := by
    rw [replayBackup_empty_closed_form]
    simp +decide [backedEvents,adverseNextS35Before,adverseNextProposal,adverseNextEvent1,adverseNextEvent2,adverseNextEvent3,adverseNextEvent4,adverseNextEvent5,adverseNextEvent6,adverseNextEvent7,adverseNextEvent8,adverseNextEvent9,adverseNextEvent10,adverseNextEvent11,adverseNextEvent12,adverseNextEvent13,adverseNextEvent14,adverseNextEvent15,adverseNextEvent16,adverseNextEvent17,adverseNextEvent18,adverseNextEvent19,adverseNextEvent20,adverseNextEvent21,adverseNextEvent22,adverseNextEvent23,adverseNextEvent24,adverseNextEvent25,adverseNextEvent26,adverseNextEvent27,adverseNextEvent28,adverseNextEvent29,adverseNextEvent30,adverseNextEvent31,adverseNextEvent32,adverseNextEvent33,adverseNextEvent34,taskReward]
    <;> norm_num
  have hp : rawVisits adverseNextS35Before [] = 34 := by decide
  have hn : rawVisits adverseNextS35Before ([]++[.query 7]) = 4 := by decide
  have hz : (controlPenalty savedCref uniformQuoteError unitRoleUnused .next) adverseNextS35Before [] (.query 7) = (nextNormalPenalty adverseNextS35Before) := by
    simpa only [adverseNextS35Before,nextNormalPenalty] using AgentUCTNextExact.adverse_next_normal_root_quotes_exact 34 (by omega) 7 (by decide)
  unfold indexScore
  rw [hs,hp,hn,hz]
  simp only [BackupStat.mean]
  norm_num

theorem adverseNextS35D0Cmp0 : indexScore (7/5) (controlPenalty savedCref uniformQuoteError unitRoleUnused .next) adverseNextS35Before [] (.query 0) < indexScore (7/5) (controlPenalty savedCref uniformQuoteError unitRoleUnused .next) adverseNextS35Before [] (.query 1) := by
  rw [adverseNextS35D0I0,adverseNextS35D0I1]
  have hk := adverse_next_penalty_interval 34 (by omega)
  change nextNormalPenaltyLower ≤ nextNormalPenalty adverseNextS35Before ∧ nextNormalPenalty adverseNextS35Before ≤ nextNormalPenaltyUpper at hk
  have hm : ((0/1)/4)+(8249339/6250000)-(nextNormalPenalty adverseNextS35Before) < ((0/1)/5)+(29513729/25000000)-0 := by
    have h : ((0/1)/4)+(8249339/6250000)-nextNormalPenaltyLower < ((0/1)/5)+(29513729/25000000) := by norm_num [nextNormalPenaltyLower,savedCref,uniformQuoteError]
    linarith [hk.1]
  have h := index_strict_order_from_intervals ((0/1)/5) ((0/1)/4) 0 (nextNormalPenalty adverseNextS35Before) (29513729/25000000) (8249339/6250000)
    (treeBonus (7/5) 34 5) (treeBonus (7/5) 34 4)
    (trajectory_bonus_34_5).1 (trajectory_bonus_34_4).2 hm
  simpa only [treeIndex] using h

theorem adverseNextS35D0Cmp2 : indexScore (7/5) (controlPenalty savedCref uniformQuoteError unitRoleUnused .next) adverseNextS35Before [] (.query 2) ≤ indexScore (7/5) (controlPenalty savedCref uniformQuoteError unitRoleUnused .next) adverseNextS35Before [] (.query 1) := by
  rw [adverseNextS35D0I2,adverseNextS35D0I1]
  have hk := adverse_next_penalty_interval 34 (by omega)
  change nextNormalPenaltyLower ≤ nextNormalPenalty adverseNextS35Before ∧ nextNormalPenalty adverseNextS35Before ≤ nextNormalPenaltyUpper at hk
  have hm : ((0/1)/4)+(8249339/6250000)-(nextNormalPenalty adverseNextS35Before) < ((0/1)/5)+(29513729/25000000)-0 := by
    have h : ((0/1)/4)+(8249339/6250000)-nextNormalPenaltyLower < ((0/1)/5)+(29513729/25000000) := by norm_num [nextNormalPenaltyLower,savedCref,uniformQuoteError]
    linarith [hk.1]
  have h := index_weak_order_from_intervals ((0/1)/5) ((0/1)/4) 0 (nextNormalPenalty adverseNextS35Before) (29513729/25000000) (8249339/6250000)
    (treeBonus (7/5) 34 5) (treeBonus (7/5) 34 4)
    (trajectory_bonus_34_5).1 (trajectory_bonus_34_4).2 hm.le
  simpa only [treeIndex] using h

theorem adverseNextS35D0Cmp3 : indexScore (7/5) (controlPenalty savedCref uniformQuoteError unitRoleUnused .next) adverseNextS35Before [] (.query 3) ≤ indexScore (7/5) (controlPenalty savedCref uniformQuoteError unitRoleUnused .next) adverseNextS35Before [] (.query 1) := by
  rw [adverseNextS35D0I3,adverseNextS35D0I1]
  have hk := adverse_next_penalty_interval 34 (by omega)
  change nextNormalPenaltyLower ≤ nextNormalPenalty adverseNextS35Before ∧ nextNormalPenalty adverseNextS35Before ≤ nextNormalPenaltyUpper at hk
  have hm : ((0/1)/4)+(8249339/6250000)-(nextNormalPenalty adverseNextS35Before) < ((0/1)/5)+(29513729/25000000)-0 := by
    have h : ((0/1)/4)+(8249339/6250000)-nextNormalPenaltyLower < ((0/1)/5)+(29513729/25000000) := by norm_num [nextNormalPenaltyLower,savedCref,uniformQuoteError]
    linarith [hk.1]
  have h := index_weak_order_from_intervals ((0/1)/5) ((0/1)/4) 0 (nextNormalPenalty adverseNextS35Before) (29513729/25000000) (8249339/6250000)
    (treeBonus (7/5) 34 5) (treeBonus (7/5) 34 4)
    (trajectory_bonus_34_5).1 (trajectory_bonus_34_4).2 hm.le
  simpa only [treeIndex] using h

theorem adverseNextS35D0Cmp4 : indexScore (7/5) (controlPenalty savedCref uniformQuoteError unitRoleUnused .next) adverseNextS35Before [] (.query 4) ≤ indexScore (7/5) (controlPenalty savedCref uniformQuoteError unitRoleUnused .next) adverseNextS35Before [] (.query 1) := by
  rw [adverseNextS35D0I4,adverseNextS35D0I1]
  have hk := adverse_next_penalty_interval 34 (by omega)
  change nextNormalPenaltyLower ≤ nextNormalPenalty adverseNextS35Before ∧ nextNormalPenalty adverseNextS35Before ≤ nextNormalPenaltyUpper at hk
  have hm : ((0/1)/4)+(8249339/6250000)-(nextNormalPenalty adverseNextS35Before) < ((0/1)/5)+(29513729/25000000)-0 := by
    have h : ((0/1)/4)+(8249339/6250000)-nextNormalPenaltyLower < ((0/1)/5)+(29513729/25000000) := by norm_num [nextNormalPenaltyLower,savedCref,uniformQuoteError]
    linarith [hk.1]
  have h := index_weak_order_from_intervals ((0/1)/5) ((0/1)/4) 0 (nextNormalPenalty adverseNextS35Before) (29513729/25000000) (8249339/6250000)
    (treeBonus (7/5) 34 5) (treeBonus (7/5) 34 4)
    (trajectory_bonus_34_5).1 (trajectory_bonus_34_4).2 hm.le
  simpa only [treeIndex] using h

theorem adverseNextS35D0Cmp5 : indexScore (7/5) (controlPenalty savedCref uniformQuoteError unitRoleUnused .next) adverseNextS35Before [] (.query 5) ≤ indexScore (7/5) (controlPenalty savedCref uniformQuoteError unitRoleUnused .next) adverseNextS35Before [] (.query 1) := by
  rw [adverseNextS35D0I5,adverseNextS35D0I1]
  have hk := adverse_next_penalty_interval 34 (by omega)
  change nextNormalPenaltyLower ≤ nextNormalPenalty adverseNextS35Before ∧ nextNormalPenalty adverseNextS35Before ≤ nextNormalPenaltyUpper at hk
  have hm : ((13/10)/5)+(11805493/10000000)-(nextNormalPenalty adverseNextS35Before) < ((0/1)/5)+(29513729/25000000)-0 := by
    have h : ((13/10)/5)+(11805493/10000000)-nextNormalPenaltyLower < ((0/1)/5)+(29513729/25000000) := by norm_num [nextNormalPenaltyLower,savedCref,uniformQuoteError]
    linarith [hk.1]
  have h := index_weak_order_from_intervals ((0/1)/5) ((13/10)/5) 0 (nextNormalPenalty adverseNextS35Before) (29513729/25000000) (11805493/10000000)
    (treeBonus (7/5) 34 5) (treeBonus (7/5) 34 5)
    (trajectory_bonus_34_5).1 (trajectory_bonus_34_5).2 hm.le
  simpa only [treeIndex] using h

theorem adverseNextS35D0Cmp6 : indexScore (7/5) (controlPenalty savedCref uniformQuoteError unitRoleUnused .next) adverseNextS35Before [] (.query 6) ≤ indexScore (7/5) (controlPenalty savedCref uniformQuoteError unitRoleUnused .next) adverseNextS35Before [] (.query 1) := by
  rw [adverseNextS35D0I6,adverseNextS35D0I1]
  have hk := adverse_next_penalty_interval 34 (by omega)
  change nextNormalPenaltyLower ≤ nextNormalPenalty adverseNextS35Before ∧ nextNormalPenalty adverseNextS35Before ≤ nextNormalPenaltyUpper at hk
  have hm : ((0/1)/4)+(8249339/6250000)-(nextNormalPenalty adverseNextS35Before) < ((0/1)/5)+(29513729/25000000)-0 := by
    have h : ((0/1)/4)+(8249339/6250000)-nextNormalPenaltyLower < ((0/1)/5)+(29513729/25000000) := by norm_num [nextNormalPenaltyLower,savedCref,uniformQuoteError]
    linarith [hk.1]
  have h := index_weak_order_from_intervals ((0/1)/5) ((0/1)/4) 0 (nextNormalPenalty adverseNextS35Before) (29513729/25000000) (8249339/6250000)
    (treeBonus (7/5) 34 5) (treeBonus (7/5) 34 4)
    (trajectory_bonus_34_5).1 (trajectory_bonus_34_4).2 hm.le
  simpa only [treeIndex] using h

theorem adverseNextS35D0Cmp7 : indexScore (7/5) (controlPenalty savedCref uniformQuoteError unitRoleUnused .next) adverseNextS35Before [] (.query 7) ≤ indexScore (7/5) (controlPenalty savedCref uniformQuoteError unitRoleUnused .next) adverseNextS35Before [] (.query 1) := by
  rw [adverseNextS35D0I7,adverseNextS35D0I1]
  have hk := adverse_next_penalty_interval 34 (by omega)
  change nextNormalPenaltyLower ≤ nextNormalPenalty adverseNextS35Before ∧ nextNormalPenalty adverseNextS35Before ≤ nextNormalPenaltyUpper at hk
  have hm : ((0/1)/4)+(8249339/6250000)-(nextNormalPenalty adverseNextS35Before) < ((0/1)/5)+(29513729/25000000)-0 := by
    have h : ((0/1)/4)+(8249339/6250000)-nextNormalPenaltyLower < ((0/1)/5)+(29513729/25000000) := by norm_num [nextNormalPenaltyLower,savedCref,uniformQuoteError]
    linarith [hk.1]
  have h := index_weak_order_from_intervals ((0/1)/5) ((0/1)/4) 0 (nextNormalPenalty adverseNextS35Before) (29513729/25000000) (8249339/6250000)
    (treeBonus (7/5) 34 5) (treeBonus (7/5) 34 4)
    (trajectory_bonus_34_5).1 (trajectory_bonus_34_4).2 hm.le
  simpa only [treeIndex] using h

theorem adverseNextS35Choice0 : nativeFirstChoice (indexScore (7/5) (controlPenalty savedCref uniformQuoteError unitRoleUnused .next) adverseNextS35Before []) adverseNextS35Before [] = .query 1 := by
  apply visited_choice_from_ordered_certificate _ _ [] [.query 0] [.query 2,.query 3,.query 4,.query 5,.query 6,.query 7] (.query 1) (by decide)
  · intro a ha
    have ho : orderedLegalAvailable [] = [.query 0,.query 1,.query 2,.query 3,.query 4,.query 5,.query 6,.query 7] := by decide
    rw [ho] at ha
    simp only [List.mem_cons,List.not_mem_nil,or_false] at ha
    rcases ha with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> decide
  · intro a ha
    simp only [List.mem_cons,List.not_mem_nil,or_false] at ha
    rcases ha with rfl
    · exact adverseNextS35D0Cmp0
  · intro a ha
    simp only [List.mem_cons,List.not_mem_nil,or_false] at ha
    rcases ha with rfl | rfl | rfl | rfl | rfl | rfl
    · exact adverseNextS35D0Cmp2
    · exact adverseNextS35D0Cmp3
    · exact adverseNextS35D0Cmp4
    · exact adverseNextS35D0Cmp5
    · exact adverseNextS35D0Cmp6
    · exact adverseNextS35D0Cmp7

theorem adverseNextS35D1I0 : indexScore (7/5) (controlPenalty savedCref uniformQuoteError unitRoleUnused .next) adverseNextS35Before [.query 1] (.hydeRetriever 1) = treeIndex ((0/1)/2) (7/5) 0 5 2 := by
  have hs : replayBackup adverseNextS35Before emptyStatistics ([.query 1]++[.hydeRetriever 1]) = ⟨2,(0/1)⟩ := by
    rw [replayBackup_empty_closed_form]
    simp +decide [backedEvents,adverseNextS35Before,adverseNextProposal,adverseNextEvent1,adverseNextEvent2,adverseNextEvent3,adverseNextEvent4,adverseNextEvent5,adverseNextEvent6,adverseNextEvent7,adverseNextEvent8,adverseNextEvent9,adverseNextEvent10,adverseNextEvent11,adverseNextEvent12,adverseNextEvent13,adverseNextEvent14,adverseNextEvent15,adverseNextEvent16,adverseNextEvent17,adverseNextEvent18,adverseNextEvent19,adverseNextEvent20,adverseNextEvent21,adverseNextEvent22,adverseNextEvent23,adverseNextEvent24,adverseNextEvent25,adverseNextEvent26,adverseNextEvent27,adverseNextEvent28,adverseNextEvent29,adverseNextEvent30,adverseNextEvent31,adverseNextEvent32,adverseNextEvent33,adverseNextEvent34,taskReward]
    <;> norm_num
  have hp : rawVisits adverseNextS35Before [.query 1] = 5 := by decide
  have hn : rawVisits adverseNextS35Before ([.query 1]++[.hydeRetriever 1]) = 2 := by decide
  have hz : (controlPenalty savedCref uniformQuoteError unitRoleUnused .next) adverseNextS35Before [.query 1] (.hydeRetriever 1) = 0 := by
    apply control_penalty_empty_of_prior_terminal .next savedCref uniformQuoteError adverseNextS35Before [.query 1] (.hydeRetriever 1) 9 (by decide)
    · decide
    · decide
  unfold indexScore
  rw [hs,hp,hn,hz]
  simp only [BackupStat.mean]
  norm_num

theorem adverseNextS35D1I1 : indexScore (7/5) (controlPenalty savedCref uniformQuoteError unitRoleUnused .next) adverseNextS35Before [.query 1] (.hydeRetriever 0) = treeIndex ((0/1)/1) (7/5) 0 5 1 := by
  have hs : replayBackup adverseNextS35Before emptyStatistics ([.query 1]++[.hydeRetriever 0]) = ⟨1,(0/1)⟩ := by
    rw [replayBackup_empty_closed_form]
    simp +decide [backedEvents,adverseNextS35Before,adverseNextProposal,adverseNextEvent1,adverseNextEvent2,adverseNextEvent3,adverseNextEvent4,adverseNextEvent5,adverseNextEvent6,adverseNextEvent7,adverseNextEvent8,adverseNextEvent9,adverseNextEvent10,adverseNextEvent11,adverseNextEvent12,adverseNextEvent13,adverseNextEvent14,adverseNextEvent15,adverseNextEvent16,adverseNextEvent17,adverseNextEvent18,adverseNextEvent19,adverseNextEvent20,adverseNextEvent21,adverseNextEvent22,adverseNextEvent23,adverseNextEvent24,adverseNextEvent25,adverseNextEvent26,adverseNextEvent27,adverseNextEvent28,adverseNextEvent29,adverseNextEvent30,adverseNextEvent31,adverseNextEvent32,adverseNextEvent33,adverseNextEvent34,taskReward]
    <;> norm_num
  have hp : rawVisits adverseNextS35Before [.query 1] = 5 := by decide
  have hn : rawVisits adverseNextS35Before ([.query 1]++[.hydeRetriever 0]) = 1 := by decide
  have hz : (controlPenalty savedCref uniformQuoteError unitRoleUnused .next) adverseNextS35Before [.query 1] (.hydeRetriever 0) = 0 := by
    apply control_penalty_empty_of_prior_terminal .next savedCref uniformQuoteError adverseNextS35Before [.query 1] (.hydeRetriever 0) 1 (by decide)
    · decide
    · decide
  unfold indexScore
  rw [hs,hp,hn,hz]
  simp only [BackupStat.mean]
  norm_num

theorem adverseNextS35D1I2 : indexScore (7/5) (controlPenalty savedCref uniformQuoteError unitRoleUnused .next) adverseNextS35Before [.query 1] (.hydeRetriever 2) = treeIndex ((0/1)/1) (7/5) 0 5 1 := by
  have hs : replayBackup adverseNextS35Before emptyStatistics ([.query 1]++[.hydeRetriever 2]) = ⟨1,(0/1)⟩ := by
    rw [replayBackup_empty_closed_form]
    simp +decide [backedEvents,adverseNextS35Before,adverseNextProposal,adverseNextEvent1,adverseNextEvent2,adverseNextEvent3,adverseNextEvent4,adverseNextEvent5,adverseNextEvent6,adverseNextEvent7,adverseNextEvent8,adverseNextEvent9,adverseNextEvent10,adverseNextEvent11,adverseNextEvent12,adverseNextEvent13,adverseNextEvent14,adverseNextEvent15,adverseNextEvent16,adverseNextEvent17,adverseNextEvent18,adverseNextEvent19,adverseNextEvent20,adverseNextEvent21,adverseNextEvent22,adverseNextEvent23,adverseNextEvent24,adverseNextEvent25,adverseNextEvent26,adverseNextEvent27,adverseNextEvent28,adverseNextEvent29,adverseNextEvent30,adverseNextEvent31,adverseNextEvent32,adverseNextEvent33,adverseNextEvent34,taskReward]
    <;> norm_num
  have hp : rawVisits adverseNextS35Before [.query 1] = 5 := by decide
  have hn : rawVisits adverseNextS35Before ([.query 1]++[.hydeRetriever 2]) = 1 := by decide
  have hz : (controlPenalty savedCref uniformQuoteError unitRoleUnused .next) adverseNextS35Before [.query 1] (.hydeRetriever 2) = 0 := by
    apply control_penalty_empty_of_prior_terminal .next savedCref uniformQuoteError adverseNextS35Before [.query 1] (.hydeRetriever 2) 25 (by decide)
    · decide
    · decide
  unfold indexScore
  rw [hs,hp,hn,hz]
  simp only [BackupStat.mean]
  norm_num

theorem adverseNextS35D1Cmp0 : indexScore (7/5) (controlPenalty savedCref uniformQuoteError unitRoleUnused .next) adverseNextS35Before [.query 1] (.hydeRetriever 1) < indexScore (7/5) (controlPenalty savedCref uniformQuoteError unitRoleUnused .next) adverseNextS35Before [.query 1] (.hydeRetriever 0) := by
  rw [adverseNextS35D1I0,adverseNextS35D1I1]
  have h := index_strict_order_from_intervals ((0/1)/1) ((0/1)/2) 0 0 (93699627/50000000) (66255651/50000000)
    (treeBonus (7/5) 5 1) (treeBonus (7/5) 5 2)
    (trajectory_bonus_5_1).1 (trajectory_bonus_5_2).2 (by norm_num)
  simpa only [treeIndex,sub_zero] using h

theorem adverseNextS35D1Cmp2 : indexScore (7/5) (controlPenalty savedCref uniformQuoteError unitRoleUnused .next) adverseNextS35Before [.query 1] (.hydeRetriever 2) ≤ indexScore (7/5) (controlPenalty savedCref uniformQuoteError unitRoleUnused .next) adverseNextS35Before [.query 1] (.hydeRetriever 0) := by
  rw [adverseNextS35D1I2,adverseNextS35D1I1]

theorem adverseNextS35Choice1 : nativeFirstChoice (indexScore (7/5) (controlPenalty savedCref uniformQuoteError unitRoleUnused .next) adverseNextS35Before [.query 1]) adverseNextS35Before [.query 1] = .hydeRetriever 0 := by
  apply visited_choice_from_ordered_certificate _ _ [.query 1] [.hydeRetriever 1] [.hydeRetriever 2] (.hydeRetriever 0) (by decide)
  · intro a ha
    have ho : orderedLegalAvailable [.query 1] = [.hydeRetriever 1,.hydeRetriever 0,.hydeRetriever 2] := by decide
    rw [ho] at ha
    simp only [List.mem_cons,List.not_mem_nil,or_false] at ha
    rcases ha with rfl | rfl | rfl <;> decide
  · intro a ha
    simp only [List.mem_cons,List.not_mem_nil,or_false] at ha
    rcases ha with rfl
    · exact adverseNextS35D1Cmp0
  · intro a ha
    simp only [List.mem_cons,List.not_mem_nil,or_false] at ha
    rcases ha with rfl
    · exact adverseNextS35D1Cmp2

theorem adverseNextS35ActualEvent : nativeEvent budgetTape (7/5) (controlPenalty savedCref uniformQuoteError unitRoleUnused .next)
    (taskReward true (2/5) (1/2)) adverseNextS35Before = adverseNextEvent35 := by
  have hs0 := native_select_existing_step budgetTape (7/5) (controlPenalty savedCref uniformQuoteError unitRoleUnused .next) adverseNextS35Before 8 [] (.query 1)
    (by decide) (by decide) adverseNextS35Choice0
  have hs1 := native_select_existing_step budgetTape (7/5) (controlPenalty savedCref uniformQuoteError unitRoleUnused .next) adverseNextS35Before 7 [.query 1] (.hydeRetriever 0)
    (by decide) (by decide) adverseNextS35Choice1
  have hnew := native_select_new_step budgetTape (7/5) (controlPenalty savedCref uniformQuoteError unitRoleUnused .next) adverseNextS35Before 6 [.query 1,.hydeRetriever 0]
    [.selection 1,.selection 2,.selection 3,.selection 0] (.selection 0) (by decide) (by decide) (by decide) (by decide)
  have hs : nativeSelect budgetTape (7/5) (controlPenalty savedCref uniformQuoteError unitRoleUnused .next) adverseNextS35Before 9 [] = [.query 1,.hydeRetriever 0,.selection 0] := by
    rw [hs0]
    change nativeSelect budgetTape (7/5) (controlPenalty savedCref uniformQuoteError unitRoleUnused .next) adverseNextS35Before 8 [.query 1] = _
    rw [hs1]
    change nativeSelect budgetTape (7/5) (controlPenalty savedCref uniformQuoteError unitRoleUnused .next) adverseNextS35Before 7 [.query 1,.hydeRetriever 0] = _
    rw [hnew] <;> rfl
  have hr : repairedRollout budgetTape adverseNextS35Before 9 [.query 1,.hydeRetriever 0,.selection 0] = [.query 1,.hydeRetriever 0,.selection 0,.width 0,.stop,.reranker 0,.topm 0,.context 0,.answer 0] := by decide
  simp only [nativeEvent,hs,hr]
  rfl

def adverseNextS36Before := adverseNextProposal.take 35

theorem adverseNextS36D0I0 : indexScore (7/5) (controlPenalty savedCref uniformQuoteError unitRoleUnused .next) adverseNextS36Before [] (.query 0) = treeIndex ((0/1)/4) (7/5) (nextNormalPenalty adverseNextS36Before) 35 4 := by
  have hs : replayBackup adverseNextS36Before emptyStatistics ([]++[.query 0]) = ⟨4,(0/1)⟩ := by
    rw [replayBackup_empty_closed_form]
    simp +decide [backedEvents,adverseNextS36Before,adverseNextProposal,adverseNextEvent1,adverseNextEvent2,adverseNextEvent3,adverseNextEvent4,adverseNextEvent5,adverseNextEvent6,adverseNextEvent7,adverseNextEvent8,adverseNextEvent9,adverseNextEvent10,adverseNextEvent11,adverseNextEvent12,adverseNextEvent13,adverseNextEvent14,adverseNextEvent15,adverseNextEvent16,adverseNextEvent17,adverseNextEvent18,adverseNextEvent19,adverseNextEvent20,adverseNextEvent21,adverseNextEvent22,adverseNextEvent23,adverseNextEvent24,adverseNextEvent25,adverseNextEvent26,adverseNextEvent27,adverseNextEvent28,adverseNextEvent29,adverseNextEvent30,adverseNextEvent31,adverseNextEvent32,adverseNextEvent33,adverseNextEvent34,adverseNextEvent35,taskReward]
    <;> norm_num
  have hp : rawVisits adverseNextS36Before [] = 35 := by decide
  have hn : rawVisits adverseNextS36Before ([]++[.query 0]) = 4 := by decide
  have hz : (controlPenalty savedCref uniformQuoteError unitRoleUnused .next) adverseNextS36Before [] (.query 0) = (nextNormalPenalty adverseNextS36Before) := by
    simpa only [adverseNextS36Before,nextNormalPenalty] using AgentUCTNextExact.adverse_next_normal_root_quotes_exact 35 (by omega) 0 (by decide)
  unfold indexScore
  rw [hs,hp,hn,hz]
  simp only [BackupStat.mean]
  norm_num

theorem adverseNextS36D0I1 : indexScore (7/5) (controlPenalty savedCref uniformQuoteError unitRoleUnused .next) adverseNextS36Before [] (.query 1) = treeIndex ((0/1)/6) (7/5) 0 35 6 := by
  have hs : replayBackup adverseNextS36Before emptyStatistics ([]++[.query 1]) = ⟨6,(0/1)⟩ := by
    rw [replayBackup_empty_closed_form]
    simp +decide [backedEvents,adverseNextS36Before,adverseNextProposal,adverseNextEvent1,adverseNextEvent2,adverseNextEvent3,adverseNextEvent4,adverseNextEvent5,adverseNextEvent6,adverseNextEvent7,adverseNextEvent8,adverseNextEvent9,adverseNextEvent10,adverseNextEvent11,adverseNextEvent12,adverseNextEvent13,adverseNextEvent14,adverseNextEvent15,adverseNextEvent16,adverseNextEvent17,adverseNextEvent18,adverseNextEvent19,adverseNextEvent20,adverseNextEvent21,adverseNextEvent22,adverseNextEvent23,adverseNextEvent24,adverseNextEvent25,adverseNextEvent26,adverseNextEvent27,adverseNextEvent28,adverseNextEvent29,adverseNextEvent30,adverseNextEvent31,adverseNextEvent32,adverseNextEvent33,adverseNextEvent34,adverseNextEvent35,taskReward]
    <;> norm_num
  have hp : rawVisits adverseNextS36Before [] = 35 := by decide
  have hn : rawVisits adverseNextS36Before ([]++[.query 1]) = 6 := by decide
  have hz : (controlPenalty savedCref uniformQuoteError unitRoleUnused .next) adverseNextS36Before [] (.query 1) = 0 := by
    apply control_penalty_empty_suffix
    exact AgentUCTNextExact.adverse_next_hyde_root_suffix_empty 35 (by omega)
  unfold indexScore
  rw [hs,hp,hn,hz]
  simp only [BackupStat.mean]
  norm_num

theorem adverseNextS36D0I2 : indexScore (7/5) (controlPenalty savedCref uniformQuoteError unitRoleUnused .next) adverseNextS36Before [] (.query 2) = treeIndex ((0/1)/4) (7/5) (nextNormalPenalty adverseNextS36Before) 35 4 := by
  have hs : replayBackup adverseNextS36Before emptyStatistics ([]++[.query 2]) = ⟨4,(0/1)⟩ := by
    rw [replayBackup_empty_closed_form]
    simp +decide [backedEvents,adverseNextS36Before,adverseNextProposal,adverseNextEvent1,adverseNextEvent2,adverseNextEvent3,adverseNextEvent4,adverseNextEvent5,adverseNextEvent6,adverseNextEvent7,adverseNextEvent8,adverseNextEvent9,adverseNextEvent10,adverseNextEvent11,adverseNextEvent12,adverseNextEvent13,adverseNextEvent14,adverseNextEvent15,adverseNextEvent16,adverseNextEvent17,adverseNextEvent18,adverseNextEvent19,adverseNextEvent20,adverseNextEvent21,adverseNextEvent22,adverseNextEvent23,adverseNextEvent24,adverseNextEvent25,adverseNextEvent26,adverseNextEvent27,adverseNextEvent28,adverseNextEvent29,adverseNextEvent30,adverseNextEvent31,adverseNextEvent32,adverseNextEvent33,adverseNextEvent34,adverseNextEvent35,taskReward]
    <;> norm_num
  have hp : rawVisits adverseNextS36Before [] = 35 := by decide
  have hn : rawVisits adverseNextS36Before ([]++[.query 2]) = 4 := by decide
  have hz : (controlPenalty savedCref uniformQuoteError unitRoleUnused .next) adverseNextS36Before [] (.query 2) = (nextNormalPenalty adverseNextS36Before) := by
    simpa only [adverseNextS36Before,nextNormalPenalty] using AgentUCTNextExact.adverse_next_normal_root_quotes_exact 35 (by omega) 2 (by decide)
  unfold indexScore
  rw [hs,hp,hn,hz]
  simp only [BackupStat.mean]
  norm_num

theorem adverseNextS36D0I3 : indexScore (7/5) (controlPenalty savedCref uniformQuoteError unitRoleUnused .next) adverseNextS36Before [] (.query 3) = treeIndex ((0/1)/4) (7/5) (nextNormalPenalty adverseNextS36Before) 35 4 := by
  have hs : replayBackup adverseNextS36Before emptyStatistics ([]++[.query 3]) = ⟨4,(0/1)⟩ := by
    rw [replayBackup_empty_closed_form]
    simp +decide [backedEvents,adverseNextS36Before,adverseNextProposal,adverseNextEvent1,adverseNextEvent2,adverseNextEvent3,adverseNextEvent4,adverseNextEvent5,adverseNextEvent6,adverseNextEvent7,adverseNextEvent8,adverseNextEvent9,adverseNextEvent10,adverseNextEvent11,adverseNextEvent12,adverseNextEvent13,adverseNextEvent14,adverseNextEvent15,adverseNextEvent16,adverseNextEvent17,adverseNextEvent18,adverseNextEvent19,adverseNextEvent20,adverseNextEvent21,adverseNextEvent22,adverseNextEvent23,adverseNextEvent24,adverseNextEvent25,adverseNextEvent26,adverseNextEvent27,adverseNextEvent28,adverseNextEvent29,adverseNextEvent30,adverseNextEvent31,adverseNextEvent32,adverseNextEvent33,adverseNextEvent34,adverseNextEvent35,taskReward]
    <;> norm_num
  have hp : rawVisits adverseNextS36Before [] = 35 := by decide
  have hn : rawVisits adverseNextS36Before ([]++[.query 3]) = 4 := by decide
  have hz : (controlPenalty savedCref uniformQuoteError unitRoleUnused .next) adverseNextS36Before [] (.query 3) = (nextNormalPenalty adverseNextS36Before) := by
    simpa only [adverseNextS36Before,nextNormalPenalty] using AgentUCTNextExact.adverse_next_normal_root_quotes_exact 35 (by omega) 3 (by decide)
  unfold indexScore
  rw [hs,hp,hn,hz]
  simp only [BackupStat.mean]
  norm_num

theorem adverseNextS36D0I4 : indexScore (7/5) (controlPenalty savedCref uniformQuoteError unitRoleUnused .next) adverseNextS36Before [] (.query 4) = treeIndex ((0/1)/4) (7/5) (nextNormalPenalty adverseNextS36Before) 35 4 := by
  have hs : replayBackup adverseNextS36Before emptyStatistics ([]++[.query 4]) = ⟨4,(0/1)⟩ := by
    rw [replayBackup_empty_closed_form]
    simp +decide [backedEvents,adverseNextS36Before,adverseNextProposal,adverseNextEvent1,adverseNextEvent2,adverseNextEvent3,adverseNextEvent4,adverseNextEvent5,adverseNextEvent6,adverseNextEvent7,adverseNextEvent8,adverseNextEvent9,adverseNextEvent10,adverseNextEvent11,adverseNextEvent12,adverseNextEvent13,adverseNextEvent14,adverseNextEvent15,adverseNextEvent16,adverseNextEvent17,adverseNextEvent18,adverseNextEvent19,adverseNextEvent20,adverseNextEvent21,adverseNextEvent22,adverseNextEvent23,adverseNextEvent24,adverseNextEvent25,adverseNextEvent26,adverseNextEvent27,adverseNextEvent28,adverseNextEvent29,adverseNextEvent30,adverseNextEvent31,adverseNextEvent32,adverseNextEvent33,adverseNextEvent34,adverseNextEvent35,taskReward]
    <;> norm_num
  have hp : rawVisits adverseNextS36Before [] = 35 := by decide
  have hn : rawVisits adverseNextS36Before ([]++[.query 4]) = 4 := by decide
  have hz : (controlPenalty savedCref uniformQuoteError unitRoleUnused .next) adverseNextS36Before [] (.query 4) = (nextNormalPenalty adverseNextS36Before) := by
    simpa only [adverseNextS36Before,nextNormalPenalty] using AgentUCTNextExact.adverse_next_normal_root_quotes_exact 35 (by omega) 4 (by decide)
  unfold indexScore
  rw [hs,hp,hn,hz]
  simp only [BackupStat.mean]
  norm_num

theorem adverseNextS36D0I5 : indexScore (7/5) (controlPenalty savedCref uniformQuoteError unitRoleUnused .next) adverseNextS36Before [] (.query 5) = treeIndex ((13/10)/5) (7/5) (nextNormalPenalty adverseNextS36Before) 35 5 := by
  have hs : replayBackup adverseNextS36Before emptyStatistics ([]++[.query 5]) = ⟨5,(13/10)⟩ := by
    rw [replayBackup_empty_closed_form]
    simp +decide [backedEvents,adverseNextS36Before,adverseNextProposal,adverseNextEvent1,adverseNextEvent2,adverseNextEvent3,adverseNextEvent4,adverseNextEvent5,adverseNextEvent6,adverseNextEvent7,adverseNextEvent8,adverseNextEvent9,adverseNextEvent10,adverseNextEvent11,adverseNextEvent12,adverseNextEvent13,adverseNextEvent14,adverseNextEvent15,adverseNextEvent16,adverseNextEvent17,adverseNextEvent18,adverseNextEvent19,adverseNextEvent20,adverseNextEvent21,adverseNextEvent22,adverseNextEvent23,adverseNextEvent24,adverseNextEvent25,adverseNextEvent26,adverseNextEvent27,adverseNextEvent28,adverseNextEvent29,adverseNextEvent30,adverseNextEvent31,adverseNextEvent32,adverseNextEvent33,adverseNextEvent34,adverseNextEvent35,taskReward]
    <;> norm_num
  have hp : rawVisits adverseNextS36Before [] = 35 := by decide
  have hn : rawVisits adverseNextS36Before ([]++[.query 5]) = 5 := by decide
  have hz : (controlPenalty savedCref uniformQuoteError unitRoleUnused .next) adverseNextS36Before [] (.query 5) = (nextNormalPenalty adverseNextS36Before) := by
    simpa only [adverseNextS36Before,nextNormalPenalty] using AgentUCTNextExact.adverse_next_normal_root_quotes_exact 35 (by omega) 5 (by decide)
  unfold indexScore
  rw [hs,hp,hn,hz]
  simp only [BackupStat.mean]
  norm_num

theorem adverseNextS36D0I6 : indexScore (7/5) (controlPenalty savedCref uniformQuoteError unitRoleUnused .next) adverseNextS36Before [] (.query 6) = treeIndex ((0/1)/4) (7/5) (nextNormalPenalty adverseNextS36Before) 35 4 := by
  have hs : replayBackup adverseNextS36Before emptyStatistics ([]++[.query 6]) = ⟨4,(0/1)⟩ := by
    rw [replayBackup_empty_closed_form]
    simp +decide [backedEvents,adverseNextS36Before,adverseNextProposal,adverseNextEvent1,adverseNextEvent2,adverseNextEvent3,adverseNextEvent4,adverseNextEvent5,adverseNextEvent6,adverseNextEvent7,adverseNextEvent8,adverseNextEvent9,adverseNextEvent10,adverseNextEvent11,adverseNextEvent12,adverseNextEvent13,adverseNextEvent14,adverseNextEvent15,adverseNextEvent16,adverseNextEvent17,adverseNextEvent18,adverseNextEvent19,adverseNextEvent20,adverseNextEvent21,adverseNextEvent22,adverseNextEvent23,adverseNextEvent24,adverseNextEvent25,adverseNextEvent26,adverseNextEvent27,adverseNextEvent28,adverseNextEvent29,adverseNextEvent30,adverseNextEvent31,adverseNextEvent32,adverseNextEvent33,adverseNextEvent34,adverseNextEvent35,taskReward]
    <;> norm_num
  have hp : rawVisits adverseNextS36Before [] = 35 := by decide
  have hn : rawVisits adverseNextS36Before ([]++[.query 6]) = 4 := by decide
  have hz : (controlPenalty savedCref uniformQuoteError unitRoleUnused .next) adverseNextS36Before [] (.query 6) = (nextNormalPenalty adverseNextS36Before) := by
    simpa only [adverseNextS36Before,nextNormalPenalty] using AgentUCTNextExact.adverse_next_normal_root_quotes_exact 35 (by omega) 6 (by decide)
  unfold indexScore
  rw [hs,hp,hn,hz]
  simp only [BackupStat.mean]
  norm_num

theorem adverseNextS36D0I7 : indexScore (7/5) (controlPenalty savedCref uniformQuoteError unitRoleUnused .next) adverseNextS36Before [] (.query 7) = treeIndex ((0/1)/4) (7/5) (nextNormalPenalty adverseNextS36Before) 35 4 := by
  have hs : replayBackup adverseNextS36Before emptyStatistics ([]++[.query 7]) = ⟨4,(0/1)⟩ := by
    rw [replayBackup_empty_closed_form]
    simp +decide [backedEvents,adverseNextS36Before,adverseNextProposal,adverseNextEvent1,adverseNextEvent2,adverseNextEvent3,adverseNextEvent4,adverseNextEvent5,adverseNextEvent6,adverseNextEvent7,adverseNextEvent8,adverseNextEvent9,adverseNextEvent10,adverseNextEvent11,adverseNextEvent12,adverseNextEvent13,adverseNextEvent14,adverseNextEvent15,adverseNextEvent16,adverseNextEvent17,adverseNextEvent18,adverseNextEvent19,adverseNextEvent20,adverseNextEvent21,adverseNextEvent22,adverseNextEvent23,adverseNextEvent24,adverseNextEvent25,adverseNextEvent26,adverseNextEvent27,adverseNextEvent28,adverseNextEvent29,adverseNextEvent30,adverseNextEvent31,adverseNextEvent32,adverseNextEvent33,adverseNextEvent34,adverseNextEvent35,taskReward]
    <;> norm_num
  have hp : rawVisits adverseNextS36Before [] = 35 := by decide
  have hn : rawVisits adverseNextS36Before ([]++[.query 7]) = 4 := by decide
  have hz : (controlPenalty savedCref uniformQuoteError unitRoleUnused .next) adverseNextS36Before [] (.query 7) = (nextNormalPenalty adverseNextS36Before) := by
    simpa only [adverseNextS36Before,nextNormalPenalty] using AgentUCTNextExact.adverse_next_normal_root_quotes_exact 35 (by omega) 7 (by decide)
  unfold indexScore
  rw [hs,hp,hn,hz]
  simp only [BackupStat.mean]
  norm_num

theorem adverseNextS36D0Cmp0 : indexScore (7/5) (controlPenalty savedCref uniformQuoteError unitRoleUnused .next) adverseNextS36Before [] (.query 0) < indexScore (7/5) (controlPenalty savedCref uniformQuoteError unitRoleUnused .next) adverseNextS36Before [] (.query 5) := by
  rw [adverseNextS36D0I0,adverseNextS36D0I5]
  have hk := adverse_next_penalty_interval 35 (by omega)
  change nextNormalPenaltyLower ≤ nextNormalPenalty adverseNextS36Before ∧ nextNormalPenalty adverseNextS36Before ≤ nextNormalPenaltyUpper at hk
  have hm : ((0/1)/4)+(66255651/50000000)-(nextNormalPenalty adverseNextS36Before) < ((13/10)/5)+(11852169/10000000)-(nextNormalPenalty adverseNextS36Before) := by
    have h : (((0/1)/4)+(66255651/50000000) : ℝ) < ((13/10)/5)+(11852169/10000000) := by norm_num
    linarith
  have h := index_strict_order_from_intervals ((13/10)/5) ((0/1)/4) (nextNormalPenalty adverseNextS36Before) (nextNormalPenalty adverseNextS36Before) (11852169/10000000) (66255651/50000000)
    (treeBonus (7/5) 35 5) (treeBonus (7/5) 35 4)
    (trajectory_bonus_35_5).1 (trajectory_bonus_35_4).2 hm
  simpa only [treeIndex] using h

theorem adverseNextS36D0Cmp1 : indexScore (7/5) (controlPenalty savedCref uniformQuoteError unitRoleUnused .next) adverseNextS36Before [] (.query 1) < indexScore (7/5) (controlPenalty savedCref uniformQuoteError unitRoleUnused .next) adverseNextS36Before [] (.query 5) := by
  rw [adverseNextS36D0I1,adverseNextS36D0I5]
  have hk := adverse_next_penalty_interval 35 (by omega)
  change nextNormalPenaltyLower ≤ nextNormalPenalty adverseNextS36Before ∧ nextNormalPenalty adverseNextS36Before ≤ nextNormalPenaltyUpper at hk
  have hm : ((0/1)/6)+(6762189/6250000)-0 < ((13/10)/5)+(11852169/10000000)-(nextNormalPenalty adverseNextS36Before) := by
    have h : ((0/1)/6)+(6762189/6250000) < ((13/10)/5)+(11852169/10000000)-nextNormalPenaltyUpper := by norm_num [nextNormalPenaltyUpper,savedCref,uniformQuoteError]
    linarith [hk.2]
  have h := index_strict_order_from_intervals ((13/10)/5) ((0/1)/6) (nextNormalPenalty adverseNextS36Before) 0 (11852169/10000000) (6762189/6250000)
    (treeBonus (7/5) 35 5) (treeBonus (7/5) 35 6)
    (trajectory_bonus_35_5).1 (trajectory_bonus_35_6).2 hm
  simpa only [treeIndex] using h

theorem adverseNextS36D0Cmp2 : indexScore (7/5) (controlPenalty savedCref uniformQuoteError unitRoleUnused .next) adverseNextS36Before [] (.query 2) < indexScore (7/5) (controlPenalty savedCref uniformQuoteError unitRoleUnused .next) adverseNextS36Before [] (.query 5) := by
  rw [adverseNextS36D0I2,adverseNextS36D0I5]
  have hk := adverse_next_penalty_interval 35 (by omega)
  change nextNormalPenaltyLower ≤ nextNormalPenalty adverseNextS36Before ∧ nextNormalPenalty adverseNextS36Before ≤ nextNormalPenaltyUpper at hk
  have hm : ((0/1)/4)+(66255651/50000000)-(nextNormalPenalty adverseNextS36Before) < ((13/10)/5)+(11852169/10000000)-(nextNormalPenalty adverseNextS36Before) := by
    have h : (((0/1)/4)+(66255651/50000000) : ℝ) < ((13/10)/5)+(11852169/10000000) := by norm_num
    linarith
  have h := index_strict_order_from_intervals ((13/10)/5) ((0/1)/4) (nextNormalPenalty adverseNextS36Before) (nextNormalPenalty adverseNextS36Before) (11852169/10000000) (66255651/50000000)
    (treeBonus (7/5) 35 5) (treeBonus (7/5) 35 4)
    (trajectory_bonus_35_5).1 (trajectory_bonus_35_4).2 hm
  simpa only [treeIndex] using h

theorem adverseNextS36D0Cmp3 : indexScore (7/5) (controlPenalty savedCref uniformQuoteError unitRoleUnused .next) adverseNextS36Before [] (.query 3) < indexScore (7/5) (controlPenalty savedCref uniformQuoteError unitRoleUnused .next) adverseNextS36Before [] (.query 5) := by
  rw [adverseNextS36D0I3,adverseNextS36D0I5]
  have hk := adverse_next_penalty_interval 35 (by omega)
  change nextNormalPenaltyLower ≤ nextNormalPenalty adverseNextS36Before ∧ nextNormalPenalty adverseNextS36Before ≤ nextNormalPenaltyUpper at hk
  have hm : ((0/1)/4)+(66255651/50000000)-(nextNormalPenalty adverseNextS36Before) < ((13/10)/5)+(11852169/10000000)-(nextNormalPenalty adverseNextS36Before) := by
    have h : (((0/1)/4)+(66255651/50000000) : ℝ) < ((13/10)/5)+(11852169/10000000) := by norm_num
    linarith
  have h := index_strict_order_from_intervals ((13/10)/5) ((0/1)/4) (nextNormalPenalty adverseNextS36Before) (nextNormalPenalty adverseNextS36Before) (11852169/10000000) (66255651/50000000)
    (treeBonus (7/5) 35 5) (treeBonus (7/5) 35 4)
    (trajectory_bonus_35_5).1 (trajectory_bonus_35_4).2 hm
  simpa only [treeIndex] using h

theorem adverseNextS36D0Cmp4 : indexScore (7/5) (controlPenalty savedCref uniformQuoteError unitRoleUnused .next) adverseNextS36Before [] (.query 4) < indexScore (7/5) (controlPenalty savedCref uniformQuoteError unitRoleUnused .next) adverseNextS36Before [] (.query 5) := by
  rw [adverseNextS36D0I4,adverseNextS36D0I5]
  have hk := adverse_next_penalty_interval 35 (by omega)
  change nextNormalPenaltyLower ≤ nextNormalPenalty adverseNextS36Before ∧ nextNormalPenalty adverseNextS36Before ≤ nextNormalPenaltyUpper at hk
  have hm : ((0/1)/4)+(66255651/50000000)-(nextNormalPenalty adverseNextS36Before) < ((13/10)/5)+(11852169/10000000)-(nextNormalPenalty adverseNextS36Before) := by
    have h : (((0/1)/4)+(66255651/50000000) : ℝ) < ((13/10)/5)+(11852169/10000000) := by norm_num
    linarith
  have h := index_strict_order_from_intervals ((13/10)/5) ((0/1)/4) (nextNormalPenalty adverseNextS36Before) (nextNormalPenalty adverseNextS36Before) (11852169/10000000) (66255651/50000000)
    (treeBonus (7/5) 35 5) (treeBonus (7/5) 35 4)
    (trajectory_bonus_35_5).1 (trajectory_bonus_35_4).2 hm
  simpa only [treeIndex] using h

theorem adverseNextS36D0Cmp6 : indexScore (7/5) (controlPenalty savedCref uniformQuoteError unitRoleUnused .next) adverseNextS36Before [] (.query 6) ≤ indexScore (7/5) (controlPenalty savedCref uniformQuoteError unitRoleUnused .next) adverseNextS36Before [] (.query 5) := by
  rw [adverseNextS36D0I6,adverseNextS36D0I5]
  have hk := adverse_next_penalty_interval 35 (by omega)
  change nextNormalPenaltyLower ≤ nextNormalPenalty adverseNextS36Before ∧ nextNormalPenalty adverseNextS36Before ≤ nextNormalPenaltyUpper at hk
  have hm : ((0/1)/4)+(66255651/50000000)-(nextNormalPenalty adverseNextS36Before) < ((13/10)/5)+(11852169/10000000)-(nextNormalPenalty adverseNextS36Before) := by
    have h : (((0/1)/4)+(66255651/50000000) : ℝ) < ((13/10)/5)+(11852169/10000000) := by norm_num
    linarith
  have h := index_weak_order_from_intervals ((13/10)/5) ((0/1)/4) (nextNormalPenalty adverseNextS36Before) (nextNormalPenalty adverseNextS36Before) (11852169/10000000) (66255651/50000000)
    (treeBonus (7/5) 35 5) (treeBonus (7/5) 35 4)
    (trajectory_bonus_35_5).1 (trajectory_bonus_35_4).2 hm.le
  simpa only [treeIndex] using h

theorem adverseNextS36D0Cmp7 : indexScore (7/5) (controlPenalty savedCref uniformQuoteError unitRoleUnused .next) adverseNextS36Before [] (.query 7) ≤ indexScore (7/5) (controlPenalty savedCref uniformQuoteError unitRoleUnused .next) adverseNextS36Before [] (.query 5) := by
  rw [adverseNextS36D0I7,adverseNextS36D0I5]
  have hk := adverse_next_penalty_interval 35 (by omega)
  change nextNormalPenaltyLower ≤ nextNormalPenalty adverseNextS36Before ∧ nextNormalPenalty adverseNextS36Before ≤ nextNormalPenaltyUpper at hk
  have hm : ((0/1)/4)+(66255651/50000000)-(nextNormalPenalty adverseNextS36Before) < ((13/10)/5)+(11852169/10000000)-(nextNormalPenalty adverseNextS36Before) := by
    have h : (((0/1)/4)+(66255651/50000000) : ℝ) < ((13/10)/5)+(11852169/10000000) := by norm_num
    linarith
  have h := index_weak_order_from_intervals ((13/10)/5) ((0/1)/4) (nextNormalPenalty adverseNextS36Before) (nextNormalPenalty adverseNextS36Before) (11852169/10000000) (66255651/50000000)
    (treeBonus (7/5) 35 5) (treeBonus (7/5) 35 4)
    (trajectory_bonus_35_5).1 (trajectory_bonus_35_4).2 hm.le
  simpa only [treeIndex] using h

theorem adverseNextS36Choice0 : nativeFirstChoice (indexScore (7/5) (controlPenalty savedCref uniformQuoteError unitRoleUnused .next) adverseNextS36Before []) adverseNextS36Before [] = .query 5 := by
  apply visited_choice_from_ordered_certificate _ _ [] [.query 0,.query 1,.query 2,.query 3,.query 4] [.query 6,.query 7] (.query 5) (by decide)
  · intro a ha
    have ho : orderedLegalAvailable [] = [.query 0,.query 1,.query 2,.query 3,.query 4,.query 5,.query 6,.query 7] := by decide
    rw [ho] at ha
    simp only [List.mem_cons,List.not_mem_nil,or_false] at ha
    rcases ha with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> decide
  · intro a ha
    simp only [List.mem_cons,List.not_mem_nil,or_false] at ha
    rcases ha with rfl | rfl | rfl | rfl | rfl
    · exact adverseNextS36D0Cmp0
    · exact adverseNextS36D0Cmp1
    · exact adverseNextS36D0Cmp2
    · exact adverseNextS36D0Cmp3
    · exact adverseNextS36D0Cmp4
  · intro a ha
    simp only [List.mem_cons,List.not_mem_nil,or_false] at ha
    rcases ha with rfl | rfl
    · exact adverseNextS36D0Cmp6
    · exact adverseNextS36D0Cmp7

theorem adverseNextS36ActualEvent : nativeEvent budgetTape (7/5) (controlPenalty savedCref uniformQuoteError unitRoleUnused .next)
    (taskReward true (2/5) (1/2)) adverseNextS36Before = adverseNextEvent36 := by
  have hs0 := native_select_existing_step budgetTape (7/5) (controlPenalty savedCref uniformQuoteError unitRoleUnused .next) adverseNextS36Before 8 [] (.query 5)
    (by decide) (by decide) adverseNextS36Choice0
  have hnew := native_select_new_step budgetTape (7/5) (controlPenalty savedCref uniformQuoteError unitRoleUnused .next) adverseNextS36Before 7 [.query 5]
    [.normalRetriever 7,.normalRetriever 8,.normalRetriever 5,.normalRetriever 2,.normalRetriever 3,.normalRetriever 12,.normalRetriever 14,.normalRetriever 13,.normalRetriever 21,.normalRetriever 23,.normalRetriever 22,.normalRetriever 9,.normalRetriever 11,.normalRetriever 10,.normalRetriever 15,.normalRetriever 17,.normalRetriever 16,.normalRetriever 18,.normalRetriever 20,.normalRetriever 19,.normalRetriever 24,.normalRetriever 25,.normalRetriever 26,.normalRetriever 27,.normalRetriever 28,.normalRetriever 29] (.normalRetriever 7) (by decide) (by decide) (by decide) (by decide)
  have hs : nativeSelect budgetTape (7/5) (controlPenalty savedCref uniformQuoteError unitRoleUnused .next) adverseNextS36Before 9 [] = [.query 5,.normalRetriever 7] := by
    rw [hs0]
    change nativeSelect budgetTape (7/5) (controlPenalty savedCref uniformQuoteError unitRoleUnused .next) adverseNextS36Before 8 [.query 5] = _
    rw [hnew] <;> rfl
  have hr : repairedRollout budgetTape adverseNextS36Before 9 [.query 5,.normalRetriever 7] = [.query 5,.normalRetriever 7,.selection 0,.width 0,.stop,.reranker 0,.topm 0,.context 0,.answer 0] := by decide
  simp only [nativeEvent,hs,hr]
  rfl

end AgentUCT32MConcrete
