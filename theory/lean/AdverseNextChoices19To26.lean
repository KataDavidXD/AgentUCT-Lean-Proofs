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

def adverseNextS19Before := adverseNextProposal.take 18

theorem adverseNextS19D0I0 : indexScore (7/5) (controlPenalty savedCref uniformQuoteError unitRoleUnused .next) adverseNextS19Before [] (.query 0) = treeIndex ((0/1)/2) (7/5) (nextNormalPenalty adverseNextS19Before) 18 2 := by
  have hs : replayBackup adverseNextS19Before emptyStatistics ([]++[.query 0]) = ⟨2,(0/1)⟩ := by
    rw [replayBackup_empty_closed_form]
    simp +decide [backedEvents,adverseNextS19Before,adverseNextProposal,adverseNextEvent1,adverseNextEvent2,adverseNextEvent3,adverseNextEvent4,adverseNextEvent5,adverseNextEvent6,adverseNextEvent7,adverseNextEvent8,adverseNextEvent9,adverseNextEvent10,adverseNextEvent11,adverseNextEvent12,adverseNextEvent13,adverseNextEvent14,adverseNextEvent15,adverseNextEvent16,adverseNextEvent17,adverseNextEvent18,taskReward]
    <;> norm_num
  have hp : rawVisits adverseNextS19Before [] = 18 := by decide
  have hn : rawVisits adverseNextS19Before ([]++[.query 0]) = 2 := by decide
  have hz : (controlPenalty savedCref uniformQuoteError unitRoleUnused .next) adverseNextS19Before [] (.query 0) = (nextNormalPenalty adverseNextS19Before) := by
    simpa only [adverseNextS19Before,nextNormalPenalty] using AgentUCTNextExact.adverse_next_normal_root_quotes_exact 18 (by omega) 0 (by decide)
  unfold indexScore
  rw [hs,hp,hn,hz]
  simp only [BackupStat.mean]
  norm_num

theorem adverseNextS19D0I1 : indexScore (7/5) (controlPenalty savedCref uniformQuoteError unitRoleUnused .next) adverseNextS19Before [] (.query 1) = treeIndex ((0/1)/3) (7/5) 0 18 3 := by
  have hs : replayBackup adverseNextS19Before emptyStatistics ([]++[.query 1]) = ⟨3,(0/1)⟩ := by
    rw [replayBackup_empty_closed_form]
    simp +decide [backedEvents,adverseNextS19Before,adverseNextProposal,adverseNextEvent1,adverseNextEvent2,adverseNextEvent3,adverseNextEvent4,adverseNextEvent5,adverseNextEvent6,adverseNextEvent7,adverseNextEvent8,adverseNextEvent9,adverseNextEvent10,adverseNextEvent11,adverseNextEvent12,adverseNextEvent13,adverseNextEvent14,adverseNextEvent15,adverseNextEvent16,adverseNextEvent17,adverseNextEvent18,taskReward]
    <;> norm_num
  have hp : rawVisits adverseNextS19Before [] = 18 := by decide
  have hn : rawVisits adverseNextS19Before ([]++[.query 1]) = 3 := by decide
  have hz : (controlPenalty savedCref uniformQuoteError unitRoleUnused .next) adverseNextS19Before [] (.query 1) = 0 := by
    apply control_penalty_empty_suffix
    exact AgentUCTNextExact.adverse_next_hyde_root_suffix_empty 18 (by omega)
  unfold indexScore
  rw [hs,hp,hn,hz]
  simp only [BackupStat.mean]
  norm_num

theorem adverseNextS19D0I2 : indexScore (7/5) (controlPenalty savedCref uniformQuoteError unitRoleUnused .next) adverseNextS19Before [] (.query 2) = treeIndex ((0/1)/2) (7/5) (nextNormalPenalty adverseNextS19Before) 18 2 := by
  have hs : replayBackup adverseNextS19Before emptyStatistics ([]++[.query 2]) = ⟨2,(0/1)⟩ := by
    rw [replayBackup_empty_closed_form]
    simp +decide [backedEvents,adverseNextS19Before,adverseNextProposal,adverseNextEvent1,adverseNextEvent2,adverseNextEvent3,adverseNextEvent4,adverseNextEvent5,adverseNextEvent6,adverseNextEvent7,adverseNextEvent8,adverseNextEvent9,adverseNextEvent10,adverseNextEvent11,adverseNextEvent12,adverseNextEvent13,adverseNextEvent14,adverseNextEvent15,adverseNextEvent16,adverseNextEvent17,adverseNextEvent18,taskReward]
    <;> norm_num
  have hp : rawVisits adverseNextS19Before [] = 18 := by decide
  have hn : rawVisits adverseNextS19Before ([]++[.query 2]) = 2 := by decide
  have hz : (controlPenalty savedCref uniformQuoteError unitRoleUnused .next) adverseNextS19Before [] (.query 2) = (nextNormalPenalty adverseNextS19Before) := by
    simpa only [adverseNextS19Before,nextNormalPenalty] using AgentUCTNextExact.adverse_next_normal_root_quotes_exact 18 (by omega) 2 (by decide)
  unfold indexScore
  rw [hs,hp,hn,hz]
  simp only [BackupStat.mean]
  norm_num

theorem adverseNextS19D0I3 : indexScore (7/5) (controlPenalty savedCref uniformQuoteError unitRoleUnused .next) adverseNextS19Before [] (.query 3) = treeIndex ((0/1)/2) (7/5) (nextNormalPenalty adverseNextS19Before) 18 2 := by
  have hs : replayBackup adverseNextS19Before emptyStatistics ([]++[.query 3]) = ⟨2,(0/1)⟩ := by
    rw [replayBackup_empty_closed_form]
    simp +decide [backedEvents,adverseNextS19Before,adverseNextProposal,adverseNextEvent1,adverseNextEvent2,adverseNextEvent3,adverseNextEvent4,adverseNextEvent5,adverseNextEvent6,adverseNextEvent7,adverseNextEvent8,adverseNextEvent9,adverseNextEvent10,adverseNextEvent11,adverseNextEvent12,adverseNextEvent13,adverseNextEvent14,adverseNextEvent15,adverseNextEvent16,adverseNextEvent17,adverseNextEvent18,taskReward]
    <;> norm_num
  have hp : rawVisits adverseNextS19Before [] = 18 := by decide
  have hn : rawVisits adverseNextS19Before ([]++[.query 3]) = 2 := by decide
  have hz : (controlPenalty savedCref uniformQuoteError unitRoleUnused .next) adverseNextS19Before [] (.query 3) = (nextNormalPenalty adverseNextS19Before) := by
    simpa only [adverseNextS19Before,nextNormalPenalty] using AgentUCTNextExact.adverse_next_normal_root_quotes_exact 18 (by omega) 3 (by decide)
  unfold indexScore
  rw [hs,hp,hn,hz]
  simp only [BackupStat.mean]
  norm_num

theorem adverseNextS19D0I4 : indexScore (7/5) (controlPenalty savedCref uniformQuoteError unitRoleUnused .next) adverseNextS19Before [] (.query 4) = treeIndex ((0/1)/2) (7/5) (nextNormalPenalty adverseNextS19Before) 18 2 := by
  have hs : replayBackup adverseNextS19Before emptyStatistics ([]++[.query 4]) = ⟨2,(0/1)⟩ := by
    rw [replayBackup_empty_closed_form]
    simp +decide [backedEvents,adverseNextS19Before,adverseNextProposal,adverseNextEvent1,adverseNextEvent2,adverseNextEvent3,adverseNextEvent4,adverseNextEvent5,adverseNextEvent6,adverseNextEvent7,adverseNextEvent8,adverseNextEvent9,adverseNextEvent10,adverseNextEvent11,adverseNextEvent12,adverseNextEvent13,adverseNextEvent14,adverseNextEvent15,adverseNextEvent16,adverseNextEvent17,adverseNextEvent18,taskReward]
    <;> norm_num
  have hp : rawVisits adverseNextS19Before [] = 18 := by decide
  have hn : rawVisits adverseNextS19Before ([]++[.query 4]) = 2 := by decide
  have hz : (controlPenalty savedCref uniformQuoteError unitRoleUnused .next) adverseNextS19Before [] (.query 4) = (nextNormalPenalty adverseNextS19Before) := by
    simpa only [adverseNextS19Before,nextNormalPenalty] using AgentUCTNextExact.adverse_next_normal_root_quotes_exact 18 (by omega) 4 (by decide)
  unfold indexScore
  rw [hs,hp,hn,hz]
  simp only [BackupStat.mean]
  norm_num

theorem adverseNextS19D0I5 : indexScore (7/5) (controlPenalty savedCref uniformQuoteError unitRoleUnused .next) adverseNextS19Before [] (.query 5) = treeIndex ((13/10)/3) (7/5) (nextNormalPenalty adverseNextS19Before) 18 3 := by
  have hs : replayBackup adverseNextS19Before emptyStatistics ([]++[.query 5]) = ⟨3,(13/10)⟩ := by
    rw [replayBackup_empty_closed_form]
    simp +decide [backedEvents,adverseNextS19Before,adverseNextProposal,adverseNextEvent1,adverseNextEvent2,adverseNextEvent3,adverseNextEvent4,adverseNextEvent5,adverseNextEvent6,adverseNextEvent7,adverseNextEvent8,adverseNextEvent9,adverseNextEvent10,adverseNextEvent11,adverseNextEvent12,adverseNextEvent13,adverseNextEvent14,adverseNextEvent15,adverseNextEvent16,adverseNextEvent17,adverseNextEvent18,taskReward]
    <;> norm_num
  have hp : rawVisits adverseNextS19Before [] = 18 := by decide
  have hn : rawVisits adverseNextS19Before ([]++[.query 5]) = 3 := by decide
  have hz : (controlPenalty savedCref uniformQuoteError unitRoleUnused .next) adverseNextS19Before [] (.query 5) = (nextNormalPenalty adverseNextS19Before) := by
    simpa only [adverseNextS19Before,nextNormalPenalty] using AgentUCTNextExact.adverse_next_normal_root_quotes_exact 18 (by omega) 5 (by decide)
  unfold indexScore
  rw [hs,hp,hn,hz]
  simp only [BackupStat.mean]
  norm_num

theorem adverseNextS19D0I6 : indexScore (7/5) (controlPenalty savedCref uniformQuoteError unitRoleUnused .next) adverseNextS19Before [] (.query 6) = treeIndex ((0/1)/2) (7/5) (nextNormalPenalty adverseNextS19Before) 18 2 := by
  have hs : replayBackup adverseNextS19Before emptyStatistics ([]++[.query 6]) = ⟨2,(0/1)⟩ := by
    rw [replayBackup_empty_closed_form]
    simp +decide [backedEvents,adverseNextS19Before,adverseNextProposal,adverseNextEvent1,adverseNextEvent2,adverseNextEvent3,adverseNextEvent4,adverseNextEvent5,adverseNextEvent6,adverseNextEvent7,adverseNextEvent8,adverseNextEvent9,adverseNextEvent10,adverseNextEvent11,adverseNextEvent12,adverseNextEvent13,adverseNextEvent14,adverseNextEvent15,adverseNextEvent16,adverseNextEvent17,adverseNextEvent18,taskReward]
    <;> norm_num
  have hp : rawVisits adverseNextS19Before [] = 18 := by decide
  have hn : rawVisits adverseNextS19Before ([]++[.query 6]) = 2 := by decide
  have hz : (controlPenalty savedCref uniformQuoteError unitRoleUnused .next) adverseNextS19Before [] (.query 6) = (nextNormalPenalty adverseNextS19Before) := by
    simpa only [adverseNextS19Before,nextNormalPenalty] using AgentUCTNextExact.adverse_next_normal_root_quotes_exact 18 (by omega) 6 (by decide)
  unfold indexScore
  rw [hs,hp,hn,hz]
  simp only [BackupStat.mean]
  norm_num

theorem adverseNextS19D0I7 : indexScore (7/5) (controlPenalty savedCref uniformQuoteError unitRoleUnused .next) adverseNextS19Before [] (.query 7) = treeIndex ((0/1)/2) (7/5) (nextNormalPenalty adverseNextS19Before) 18 2 := by
  have hs : replayBackup adverseNextS19Before emptyStatistics ([]++[.query 7]) = ⟨2,(0/1)⟩ := by
    rw [replayBackup_empty_closed_form]
    simp +decide [backedEvents,adverseNextS19Before,adverseNextProposal,adverseNextEvent1,adverseNextEvent2,adverseNextEvent3,adverseNextEvent4,adverseNextEvent5,adverseNextEvent6,adverseNextEvent7,adverseNextEvent8,adverseNextEvent9,adverseNextEvent10,adverseNextEvent11,adverseNextEvent12,adverseNextEvent13,adverseNextEvent14,adverseNextEvent15,adverseNextEvent16,adverseNextEvent17,adverseNextEvent18,taskReward]
    <;> norm_num
  have hp : rawVisits adverseNextS19Before [] = 18 := by decide
  have hn : rawVisits adverseNextS19Before ([]++[.query 7]) = 2 := by decide
  have hz : (controlPenalty savedCref uniformQuoteError unitRoleUnused .next) adverseNextS19Before [] (.query 7) = (nextNormalPenalty adverseNextS19Before) := by
    simpa only [adverseNextS19Before,nextNormalPenalty] using AgentUCTNextExact.adverse_next_normal_root_quotes_exact 18 (by omega) 7 (by decide)
  unfold indexScore
  rw [hs,hp,hn,hz]
  simp only [BackupStat.mean]
  norm_num

theorem adverseNextS19D0Cmp0 : indexScore (7/5) (controlPenalty savedCref uniformQuoteError unitRoleUnused .next) adverseNextS19Before [] (.query 0) < indexScore (7/5) (controlPenalty savedCref uniformQuoteError unitRoleUnused .next) adverseNextS19Before [] (.query 5) := by
  rw [adverseNextS19D0I0,adverseNextS19D0I5]
  have hk := adverse_next_penalty_interval 18 (by omega)
  change nextNormalPenaltyLower ≤ nextNormalPenalty adverseNextS19Before ∧ nextNormalPenalty adverseNextS19Before ≤ nextNormalPenaltyUpper at hk
  have hm : ((0/1)/2)+(42467271/25000000)-(nextNormalPenalty adverseNextS19Before) < ((13/10)/3)+(13869751/10000000)-(nextNormalPenalty adverseNextS19Before) := by
    have h : (((0/1)/2)+(42467271/25000000) : ℝ) < ((13/10)/3)+(13869751/10000000) := by norm_num
    linarith
  have h := index_strict_order_from_intervals ((13/10)/3) ((0/1)/2) (nextNormalPenalty adverseNextS19Before) (nextNormalPenalty adverseNextS19Before) (13869751/10000000) (42467271/25000000)
    (treeBonus (7/5) 18 3) (treeBonus (7/5) 18 2)
    (trajectory_bonus_18_3).1 (trajectory_bonus_18_2).2 hm
  simpa only [treeIndex] using h

theorem adverseNextS19D0Cmp1 : indexScore (7/5) (controlPenalty savedCref uniformQuoteError unitRoleUnused .next) adverseNextS19Before [] (.query 1) < indexScore (7/5) (controlPenalty savedCref uniformQuoteError unitRoleUnused .next) adverseNextS19Before [] (.query 5) := by
  rw [adverseNextS19D0I1,adverseNextS19D0I5]
  have hk := adverse_next_penalty_interval 18 (by omega)
  change nextNormalPenaltyLower ≤ nextNormalPenalty adverseNextS19Before ∧ nextNormalPenalty adverseNextS19Before ≤ nextNormalPenaltyUpper at hk
  have hm : ((0/1)/3)+(34674381/25000000)-0 < ((13/10)/3)+(13869751/10000000)-(nextNormalPenalty adverseNextS19Before) := by
    have h : ((0/1)/3)+(34674381/25000000) < ((13/10)/3)+(13869751/10000000)-nextNormalPenaltyUpper := by norm_num [nextNormalPenaltyUpper,savedCref,uniformQuoteError]
    linarith [hk.2]
  have h := index_strict_order_from_intervals ((13/10)/3) ((0/1)/3) (nextNormalPenalty adverseNextS19Before) 0 (13869751/10000000) (34674381/25000000)
    (treeBonus (7/5) 18 3) (treeBonus (7/5) 18 3)
    (trajectory_bonus_18_3).1 (trajectory_bonus_18_3).2 hm
  simpa only [treeIndex] using h

theorem adverseNextS19D0Cmp2 : indexScore (7/5) (controlPenalty savedCref uniformQuoteError unitRoleUnused .next) adverseNextS19Before [] (.query 2) < indexScore (7/5) (controlPenalty savedCref uniformQuoteError unitRoleUnused .next) adverseNextS19Before [] (.query 5) := by
  rw [adverseNextS19D0I2,adverseNextS19D0I5]
  have hk := adverse_next_penalty_interval 18 (by omega)
  change nextNormalPenaltyLower ≤ nextNormalPenalty adverseNextS19Before ∧ nextNormalPenalty adverseNextS19Before ≤ nextNormalPenaltyUpper at hk
  have hm : ((0/1)/2)+(42467271/25000000)-(nextNormalPenalty adverseNextS19Before) < ((13/10)/3)+(13869751/10000000)-(nextNormalPenalty adverseNextS19Before) := by
    have h : (((0/1)/2)+(42467271/25000000) : ℝ) < ((13/10)/3)+(13869751/10000000) := by norm_num
    linarith
  have h := index_strict_order_from_intervals ((13/10)/3) ((0/1)/2) (nextNormalPenalty adverseNextS19Before) (nextNormalPenalty adverseNextS19Before) (13869751/10000000) (42467271/25000000)
    (treeBonus (7/5) 18 3) (treeBonus (7/5) 18 2)
    (trajectory_bonus_18_3).1 (trajectory_bonus_18_2).2 hm
  simpa only [treeIndex] using h

theorem adverseNextS19D0Cmp3 : indexScore (7/5) (controlPenalty savedCref uniformQuoteError unitRoleUnused .next) adverseNextS19Before [] (.query 3) < indexScore (7/5) (controlPenalty savedCref uniformQuoteError unitRoleUnused .next) adverseNextS19Before [] (.query 5) := by
  rw [adverseNextS19D0I3,adverseNextS19D0I5]
  have hk := adverse_next_penalty_interval 18 (by omega)
  change nextNormalPenaltyLower ≤ nextNormalPenalty adverseNextS19Before ∧ nextNormalPenalty adverseNextS19Before ≤ nextNormalPenaltyUpper at hk
  have hm : ((0/1)/2)+(42467271/25000000)-(nextNormalPenalty adverseNextS19Before) < ((13/10)/3)+(13869751/10000000)-(nextNormalPenalty adverseNextS19Before) := by
    have h : (((0/1)/2)+(42467271/25000000) : ℝ) < ((13/10)/3)+(13869751/10000000) := by norm_num
    linarith
  have h := index_strict_order_from_intervals ((13/10)/3) ((0/1)/2) (nextNormalPenalty adverseNextS19Before) (nextNormalPenalty adverseNextS19Before) (13869751/10000000) (42467271/25000000)
    (treeBonus (7/5) 18 3) (treeBonus (7/5) 18 2)
    (trajectory_bonus_18_3).1 (trajectory_bonus_18_2).2 hm
  simpa only [treeIndex] using h

theorem adverseNextS19D0Cmp4 : indexScore (7/5) (controlPenalty savedCref uniformQuoteError unitRoleUnused .next) adverseNextS19Before [] (.query 4) < indexScore (7/5) (controlPenalty savedCref uniformQuoteError unitRoleUnused .next) adverseNextS19Before [] (.query 5) := by
  rw [adverseNextS19D0I4,adverseNextS19D0I5]
  have hk := adverse_next_penalty_interval 18 (by omega)
  change nextNormalPenaltyLower ≤ nextNormalPenalty adverseNextS19Before ∧ nextNormalPenalty adverseNextS19Before ≤ nextNormalPenaltyUpper at hk
  have hm : ((0/1)/2)+(42467271/25000000)-(nextNormalPenalty adverseNextS19Before) < ((13/10)/3)+(13869751/10000000)-(nextNormalPenalty adverseNextS19Before) := by
    have h : (((0/1)/2)+(42467271/25000000) : ℝ) < ((13/10)/3)+(13869751/10000000) := by norm_num
    linarith
  have h := index_strict_order_from_intervals ((13/10)/3) ((0/1)/2) (nextNormalPenalty adverseNextS19Before) (nextNormalPenalty adverseNextS19Before) (13869751/10000000) (42467271/25000000)
    (treeBonus (7/5) 18 3) (treeBonus (7/5) 18 2)
    (trajectory_bonus_18_3).1 (trajectory_bonus_18_2).2 hm
  simpa only [treeIndex] using h

theorem adverseNextS19D0Cmp6 : indexScore (7/5) (controlPenalty savedCref uniformQuoteError unitRoleUnused .next) adverseNextS19Before [] (.query 6) ≤ indexScore (7/5) (controlPenalty savedCref uniformQuoteError unitRoleUnused .next) adverseNextS19Before [] (.query 5) := by
  rw [adverseNextS19D0I6,adverseNextS19D0I5]
  have hk := adverse_next_penalty_interval 18 (by omega)
  change nextNormalPenaltyLower ≤ nextNormalPenalty adverseNextS19Before ∧ nextNormalPenalty adverseNextS19Before ≤ nextNormalPenaltyUpper at hk
  have hm : ((0/1)/2)+(42467271/25000000)-(nextNormalPenalty adverseNextS19Before) < ((13/10)/3)+(13869751/10000000)-(nextNormalPenalty adverseNextS19Before) := by
    have h : (((0/1)/2)+(42467271/25000000) : ℝ) < ((13/10)/3)+(13869751/10000000) := by norm_num
    linarith
  have h := index_weak_order_from_intervals ((13/10)/3) ((0/1)/2) (nextNormalPenalty adverseNextS19Before) (nextNormalPenalty adverseNextS19Before) (13869751/10000000) (42467271/25000000)
    (treeBonus (7/5) 18 3) (treeBonus (7/5) 18 2)
    (trajectory_bonus_18_3).1 (trajectory_bonus_18_2).2 hm.le
  simpa only [treeIndex] using h

theorem adverseNextS19D0Cmp7 : indexScore (7/5) (controlPenalty savedCref uniformQuoteError unitRoleUnused .next) adverseNextS19Before [] (.query 7) ≤ indexScore (7/5) (controlPenalty savedCref uniformQuoteError unitRoleUnused .next) adverseNextS19Before [] (.query 5) := by
  rw [adverseNextS19D0I7,adverseNextS19D0I5]
  have hk := adverse_next_penalty_interval 18 (by omega)
  change nextNormalPenaltyLower ≤ nextNormalPenalty adverseNextS19Before ∧ nextNormalPenalty adverseNextS19Before ≤ nextNormalPenaltyUpper at hk
  have hm : ((0/1)/2)+(42467271/25000000)-(nextNormalPenalty adverseNextS19Before) < ((13/10)/3)+(13869751/10000000)-(nextNormalPenalty adverseNextS19Before) := by
    have h : (((0/1)/2)+(42467271/25000000) : ℝ) < ((13/10)/3)+(13869751/10000000) := by norm_num
    linarith
  have h := index_weak_order_from_intervals ((13/10)/3) ((0/1)/2) (nextNormalPenalty adverseNextS19Before) (nextNormalPenalty adverseNextS19Before) (13869751/10000000) (42467271/25000000)
    (treeBonus (7/5) 18 3) (treeBonus (7/5) 18 2)
    (trajectory_bonus_18_3).1 (trajectory_bonus_18_2).2 hm.le
  simpa only [treeIndex] using h

theorem adverseNextS19Choice0 : nativeFirstChoice (indexScore (7/5) (controlPenalty savedCref uniformQuoteError unitRoleUnused .next) adverseNextS19Before []) adverseNextS19Before [] = .query 5 := by
  apply visited_choice_from_ordered_certificate _ _ [] [.query 0,.query 1,.query 2,.query 3,.query 4] [.query 6,.query 7] (.query 5) (by decide)
  · intro a ha
    have ho : orderedLegalAvailable [] = [.query 0,.query 1,.query 2,.query 3,.query 4,.query 5,.query 6,.query 7] := by decide
    rw [ho] at ha
    simp only [List.mem_cons,List.not_mem_nil,or_false] at ha
    rcases ha with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> decide
  · intro a ha
    simp only [List.mem_cons,List.not_mem_nil,or_false] at ha
    rcases ha with rfl | rfl | rfl | rfl | rfl
    · exact adverseNextS19D0Cmp0
    · exact adverseNextS19D0Cmp1
    · exact adverseNextS19D0Cmp2
    · exact adverseNextS19D0Cmp3
    · exact adverseNextS19D0Cmp4
  · intro a ha
    simp only [List.mem_cons,List.not_mem_nil,or_false] at ha
    rcases ha with rfl | rfl
    · exact adverseNextS19D0Cmp6
    · exact adverseNextS19D0Cmp7

theorem adverseNextS19ActualEvent : nativeEvent budgetTape (7/5) (controlPenalty savedCref uniformQuoteError unitRoleUnused .next)
    (taskReward true (2/5) (1/2)) adverseNextS19Before = adverseNextEvent19 := by
  have hs0 := native_select_existing_step budgetTape (7/5) (controlPenalty savedCref uniformQuoteError unitRoleUnused .next) adverseNextS19Before 8 [] (.query 5)
    (by decide) (by decide) adverseNextS19Choice0
  have hnew := native_select_new_step budgetTape (7/5) (controlPenalty savedCref uniformQuoteError unitRoleUnused .next) adverseNextS19Before 7 [.query 5]
    [.normalRetriever 4,.normalRetriever 6,.normalRetriever 7,.normalRetriever 8,.normalRetriever 5,.normalRetriever 2,.normalRetriever 3,.normalRetriever 12,.normalRetriever 14,.normalRetriever 13,.normalRetriever 21,.normalRetriever 23,.normalRetriever 22,.normalRetriever 9,.normalRetriever 11,.normalRetriever 10,.normalRetriever 15,.normalRetriever 17,.normalRetriever 16,.normalRetriever 18,.normalRetriever 20,.normalRetriever 19,.normalRetriever 24,.normalRetriever 25,.normalRetriever 26,.normalRetriever 27,.normalRetriever 28,.normalRetriever 29] (.normalRetriever 4) (by decide) (by decide) (by decide) (by decide)
  have hs : nativeSelect budgetTape (7/5) (controlPenalty savedCref uniformQuoteError unitRoleUnused .next) adverseNextS19Before 9 [] = [.query 5,.normalRetriever 4] := by
    rw [hs0]
    change nativeSelect budgetTape (7/5) (controlPenalty savedCref uniformQuoteError unitRoleUnused .next) adverseNextS19Before 8 [.query 5] = _
    rw [hnew] <;> rfl
  have hr : repairedRollout budgetTape adverseNextS19Before 9 [.query 5,.normalRetriever 4] = [.query 5,.normalRetriever 4,.selection 0,.width 0,.stop,.reranker 0,.topm 0,.context 0,.answer 0] := by decide
  simp only [nativeEvent,hs,hr]
  rfl

def adverseNextS20Before := adverseNextProposal.take 19

theorem adverseNextS20D0I0 : indexScore (7/5) (controlPenalty savedCref uniformQuoteError unitRoleUnused .next) adverseNextS20Before [] (.query 0) = treeIndex ((0/1)/2) (7/5) (nextNormalPenalty adverseNextS20Before) 19 2 := by
  have hs : replayBackup adverseNextS20Before emptyStatistics ([]++[.query 0]) = ⟨2,(0/1)⟩ := by
    rw [replayBackup_empty_closed_form]
    simp +decide [backedEvents,adverseNextS20Before,adverseNextProposal,adverseNextEvent1,adverseNextEvent2,adverseNextEvent3,adverseNextEvent4,adverseNextEvent5,adverseNextEvent6,adverseNextEvent7,adverseNextEvent8,adverseNextEvent9,adverseNextEvent10,adverseNextEvent11,adverseNextEvent12,adverseNextEvent13,adverseNextEvent14,adverseNextEvent15,adverseNextEvent16,adverseNextEvent17,adverseNextEvent18,adverseNextEvent19,taskReward]
    <;> norm_num
  have hp : rawVisits adverseNextS20Before [] = 19 := by decide
  have hn : rawVisits adverseNextS20Before ([]++[.query 0]) = 2 := by decide
  have hz : (controlPenalty savedCref uniformQuoteError unitRoleUnused .next) adverseNextS20Before [] (.query 0) = (nextNormalPenalty adverseNextS20Before) := by
    simpa only [adverseNextS20Before,nextNormalPenalty] using AgentUCTNextExact.adverse_next_normal_root_quotes_exact 19 (by omega) 0 (by decide)
  unfold indexScore
  rw [hs,hp,hn,hz]
  simp only [BackupStat.mean]
  norm_num

theorem adverseNextS20D0I1 : indexScore (7/5) (controlPenalty savedCref uniformQuoteError unitRoleUnused .next) adverseNextS20Before [] (.query 1) = treeIndex ((0/1)/3) (7/5) 0 19 3 := by
  have hs : replayBackup adverseNextS20Before emptyStatistics ([]++[.query 1]) = ⟨3,(0/1)⟩ := by
    rw [replayBackup_empty_closed_form]
    simp +decide [backedEvents,adverseNextS20Before,adverseNextProposal,adverseNextEvent1,adverseNextEvent2,adverseNextEvent3,adverseNextEvent4,adverseNextEvent5,adverseNextEvent6,adverseNextEvent7,adverseNextEvent8,adverseNextEvent9,adverseNextEvent10,adverseNextEvent11,adverseNextEvent12,adverseNextEvent13,adverseNextEvent14,adverseNextEvent15,adverseNextEvent16,adverseNextEvent17,adverseNextEvent18,adverseNextEvent19,taskReward]
    <;> norm_num
  have hp : rawVisits adverseNextS20Before [] = 19 := by decide
  have hn : rawVisits adverseNextS20Before ([]++[.query 1]) = 3 := by decide
  have hz : (controlPenalty savedCref uniformQuoteError unitRoleUnused .next) adverseNextS20Before [] (.query 1) = 0 := by
    apply control_penalty_empty_suffix
    exact AgentUCTNextExact.adverse_next_hyde_root_suffix_empty 19 (by omega)
  unfold indexScore
  rw [hs,hp,hn,hz]
  simp only [BackupStat.mean]
  norm_num

theorem adverseNextS20D0I2 : indexScore (7/5) (controlPenalty savedCref uniformQuoteError unitRoleUnused .next) adverseNextS20Before [] (.query 2) = treeIndex ((0/1)/2) (7/5) (nextNormalPenalty adverseNextS20Before) 19 2 := by
  have hs : replayBackup adverseNextS20Before emptyStatistics ([]++[.query 2]) = ⟨2,(0/1)⟩ := by
    rw [replayBackup_empty_closed_form]
    simp +decide [backedEvents,adverseNextS20Before,adverseNextProposal,adverseNextEvent1,adverseNextEvent2,adverseNextEvent3,adverseNextEvent4,adverseNextEvent5,adverseNextEvent6,adverseNextEvent7,adverseNextEvent8,adverseNextEvent9,adverseNextEvent10,adverseNextEvent11,adverseNextEvent12,adverseNextEvent13,adverseNextEvent14,adverseNextEvent15,adverseNextEvent16,adverseNextEvent17,adverseNextEvent18,adverseNextEvent19,taskReward]
    <;> norm_num
  have hp : rawVisits adverseNextS20Before [] = 19 := by decide
  have hn : rawVisits adverseNextS20Before ([]++[.query 2]) = 2 := by decide
  have hz : (controlPenalty savedCref uniformQuoteError unitRoleUnused .next) adverseNextS20Before [] (.query 2) = (nextNormalPenalty adverseNextS20Before) := by
    simpa only [adverseNextS20Before,nextNormalPenalty] using AgentUCTNextExact.adverse_next_normal_root_quotes_exact 19 (by omega) 2 (by decide)
  unfold indexScore
  rw [hs,hp,hn,hz]
  simp only [BackupStat.mean]
  norm_num

theorem adverseNextS20D0I3 : indexScore (7/5) (controlPenalty savedCref uniformQuoteError unitRoleUnused .next) adverseNextS20Before [] (.query 3) = treeIndex ((0/1)/2) (7/5) (nextNormalPenalty adverseNextS20Before) 19 2 := by
  have hs : replayBackup adverseNextS20Before emptyStatistics ([]++[.query 3]) = ⟨2,(0/1)⟩ := by
    rw [replayBackup_empty_closed_form]
    simp +decide [backedEvents,adverseNextS20Before,adverseNextProposal,adverseNextEvent1,adverseNextEvent2,adverseNextEvent3,adverseNextEvent4,adverseNextEvent5,adverseNextEvent6,adverseNextEvent7,adverseNextEvent8,adverseNextEvent9,adverseNextEvent10,adverseNextEvent11,adverseNextEvent12,adverseNextEvent13,adverseNextEvent14,adverseNextEvent15,adverseNextEvent16,adverseNextEvent17,adverseNextEvent18,adverseNextEvent19,taskReward]
    <;> norm_num
  have hp : rawVisits adverseNextS20Before [] = 19 := by decide
  have hn : rawVisits adverseNextS20Before ([]++[.query 3]) = 2 := by decide
  have hz : (controlPenalty savedCref uniformQuoteError unitRoleUnused .next) adverseNextS20Before [] (.query 3) = (nextNormalPenalty adverseNextS20Before) := by
    simpa only [adverseNextS20Before,nextNormalPenalty] using AgentUCTNextExact.adverse_next_normal_root_quotes_exact 19 (by omega) 3 (by decide)
  unfold indexScore
  rw [hs,hp,hn,hz]
  simp only [BackupStat.mean]
  norm_num

theorem adverseNextS20D0I4 : indexScore (7/5) (controlPenalty savedCref uniformQuoteError unitRoleUnused .next) adverseNextS20Before [] (.query 4) = treeIndex ((0/1)/2) (7/5) (nextNormalPenalty adverseNextS20Before) 19 2 := by
  have hs : replayBackup adverseNextS20Before emptyStatistics ([]++[.query 4]) = ⟨2,(0/1)⟩ := by
    rw [replayBackup_empty_closed_form]
    simp +decide [backedEvents,adverseNextS20Before,adverseNextProposal,adverseNextEvent1,adverseNextEvent2,adverseNextEvent3,adverseNextEvent4,adverseNextEvent5,adverseNextEvent6,adverseNextEvent7,adverseNextEvent8,adverseNextEvent9,adverseNextEvent10,adverseNextEvent11,adverseNextEvent12,adverseNextEvent13,adverseNextEvent14,adverseNextEvent15,adverseNextEvent16,adverseNextEvent17,adverseNextEvent18,adverseNextEvent19,taskReward]
    <;> norm_num
  have hp : rawVisits adverseNextS20Before [] = 19 := by decide
  have hn : rawVisits adverseNextS20Before ([]++[.query 4]) = 2 := by decide
  have hz : (controlPenalty savedCref uniformQuoteError unitRoleUnused .next) adverseNextS20Before [] (.query 4) = (nextNormalPenalty adverseNextS20Before) := by
    simpa only [adverseNextS20Before,nextNormalPenalty] using AgentUCTNextExact.adverse_next_normal_root_quotes_exact 19 (by omega) 4 (by decide)
  unfold indexScore
  rw [hs,hp,hn,hz]
  simp only [BackupStat.mean]
  norm_num

theorem adverseNextS20D0I5 : indexScore (7/5) (controlPenalty savedCref uniformQuoteError unitRoleUnused .next) adverseNextS20Before [] (.query 5) = treeIndex ((13/10)/4) (7/5) (nextNormalPenalty adverseNextS20Before) 19 4 := by
  have hs : replayBackup adverseNextS20Before emptyStatistics ([]++[.query 5]) = ⟨4,(13/10)⟩ := by
    rw [replayBackup_empty_closed_form]
    simp +decide [backedEvents,adverseNextS20Before,adverseNextProposal,adverseNextEvent1,adverseNextEvent2,adverseNextEvent3,adverseNextEvent4,adverseNextEvent5,adverseNextEvent6,adverseNextEvent7,adverseNextEvent8,adverseNextEvent9,adverseNextEvent10,adverseNextEvent11,adverseNextEvent12,adverseNextEvent13,adverseNextEvent14,adverseNextEvent15,adverseNextEvent16,adverseNextEvent17,adverseNextEvent18,adverseNextEvent19,taskReward]
    <;> norm_num
  have hp : rawVisits adverseNextS20Before [] = 19 := by decide
  have hn : rawVisits adverseNextS20Before ([]++[.query 5]) = 4 := by decide
  have hz : (controlPenalty savedCref uniformQuoteError unitRoleUnused .next) adverseNextS20Before [] (.query 5) = (nextNormalPenalty adverseNextS20Before) := by
    simpa only [adverseNextS20Before,nextNormalPenalty] using AgentUCTNextExact.adverse_next_normal_root_quotes_exact 19 (by omega) 5 (by decide)
  unfold indexScore
  rw [hs,hp,hn,hz]
  simp only [BackupStat.mean]
  norm_num

theorem adverseNextS20D0I6 : indexScore (7/5) (controlPenalty savedCref uniformQuoteError unitRoleUnused .next) adverseNextS20Before [] (.query 6) = treeIndex ((0/1)/2) (7/5) (nextNormalPenalty adverseNextS20Before) 19 2 := by
  have hs : replayBackup adverseNextS20Before emptyStatistics ([]++[.query 6]) = ⟨2,(0/1)⟩ := by
    rw [replayBackup_empty_closed_form]
    simp +decide [backedEvents,adverseNextS20Before,adverseNextProposal,adverseNextEvent1,adverseNextEvent2,adverseNextEvent3,adverseNextEvent4,adverseNextEvent5,adverseNextEvent6,adverseNextEvent7,adverseNextEvent8,adverseNextEvent9,adverseNextEvent10,adverseNextEvent11,adverseNextEvent12,adverseNextEvent13,adverseNextEvent14,adverseNextEvent15,adverseNextEvent16,adverseNextEvent17,adverseNextEvent18,adverseNextEvent19,taskReward]
    <;> norm_num
  have hp : rawVisits adverseNextS20Before [] = 19 := by decide
  have hn : rawVisits adverseNextS20Before ([]++[.query 6]) = 2 := by decide
  have hz : (controlPenalty savedCref uniformQuoteError unitRoleUnused .next) adverseNextS20Before [] (.query 6) = (nextNormalPenalty adverseNextS20Before) := by
    simpa only [adverseNextS20Before,nextNormalPenalty] using AgentUCTNextExact.adverse_next_normal_root_quotes_exact 19 (by omega) 6 (by decide)
  unfold indexScore
  rw [hs,hp,hn,hz]
  simp only [BackupStat.mean]
  norm_num

theorem adverseNextS20D0I7 : indexScore (7/5) (controlPenalty savedCref uniformQuoteError unitRoleUnused .next) adverseNextS20Before [] (.query 7) = treeIndex ((0/1)/2) (7/5) (nextNormalPenalty adverseNextS20Before) 19 2 := by
  have hs : replayBackup adverseNextS20Before emptyStatistics ([]++[.query 7]) = ⟨2,(0/1)⟩ := by
    rw [replayBackup_empty_closed_form]
    simp +decide [backedEvents,adverseNextS20Before,adverseNextProposal,adverseNextEvent1,adverseNextEvent2,adverseNextEvent3,adverseNextEvent4,adverseNextEvent5,adverseNextEvent6,adverseNextEvent7,adverseNextEvent8,adverseNextEvent9,adverseNextEvent10,adverseNextEvent11,adverseNextEvent12,adverseNextEvent13,adverseNextEvent14,adverseNextEvent15,adverseNextEvent16,adverseNextEvent17,adverseNextEvent18,adverseNextEvent19,taskReward]
    <;> norm_num
  have hp : rawVisits adverseNextS20Before [] = 19 := by decide
  have hn : rawVisits adverseNextS20Before ([]++[.query 7]) = 2 := by decide
  have hz : (controlPenalty savedCref uniformQuoteError unitRoleUnused .next) adverseNextS20Before [] (.query 7) = (nextNormalPenalty adverseNextS20Before) := by
    simpa only [adverseNextS20Before,nextNormalPenalty] using AgentUCTNextExact.adverse_next_normal_root_quotes_exact 19 (by omega) 7 (by decide)
  unfold indexScore
  rw [hs,hp,hn,hz]
  simp only [BackupStat.mean]
  norm_num

theorem adverseNextS20D0Cmp1 : indexScore (7/5) (controlPenalty savedCref uniformQuoteError unitRoleUnused .next) adverseNextS20Before [] (.query 1) ≤ indexScore (7/5) (controlPenalty savedCref uniformQuoteError unitRoleUnused .next) adverseNextS20Before [] (.query 0) := by
  rw [adverseNextS20D0I1,adverseNextS20D0I0]
  have hk := adverse_next_penalty_interval 19 (by omega)
  change nextNormalPenaltyLower ≤ nextNormalPenalty adverseNextS20Before ∧ nextNormalPenalty adverseNextS20Before ≤ nextNormalPenaltyUpper at hk
  have hm : ((0/1)/3)+(13990039/10000000)-0 < ((0/1)/2)+(42835569/25000000)-(nextNormalPenalty adverseNextS20Before) := by
    have h : ((0/1)/3)+(13990039/10000000) < ((0/1)/2)+(42835569/25000000)-nextNormalPenaltyUpper := by norm_num [nextNormalPenaltyUpper,savedCref,uniformQuoteError]
    linarith [hk.2]
  have h := index_weak_order_from_intervals ((0/1)/2) ((0/1)/3) (nextNormalPenalty adverseNextS20Before) 0 (42835569/25000000) (13990039/10000000)
    (treeBonus (7/5) 19 2) (treeBonus (7/5) 19 3)
    (trajectory_bonus_19_2).1 (trajectory_bonus_19_3).2 hm.le
  simpa only [treeIndex] using h

theorem adverseNextS20D0Cmp2 : indexScore (7/5) (controlPenalty savedCref uniformQuoteError unitRoleUnused .next) adverseNextS20Before [] (.query 2) ≤ indexScore (7/5) (controlPenalty savedCref uniformQuoteError unitRoleUnused .next) adverseNextS20Before [] (.query 0) := by
  rw [adverseNextS20D0I2,adverseNextS20D0I0]

theorem adverseNextS20D0Cmp3 : indexScore (7/5) (controlPenalty savedCref uniformQuoteError unitRoleUnused .next) adverseNextS20Before [] (.query 3) ≤ indexScore (7/5) (controlPenalty savedCref uniformQuoteError unitRoleUnused .next) adverseNextS20Before [] (.query 0) := by
  rw [adverseNextS20D0I3,adverseNextS20D0I0]

theorem adverseNextS20D0Cmp4 : indexScore (7/5) (controlPenalty savedCref uniformQuoteError unitRoleUnused .next) adverseNextS20Before [] (.query 4) ≤ indexScore (7/5) (controlPenalty savedCref uniformQuoteError unitRoleUnused .next) adverseNextS20Before [] (.query 0) := by
  rw [adverseNextS20D0I4,adverseNextS20D0I0]

theorem adverseNextS20D0Cmp5 : indexScore (7/5) (controlPenalty savedCref uniformQuoteError unitRoleUnused .next) adverseNextS20Before [] (.query 5) ≤ indexScore (7/5) (controlPenalty savedCref uniformQuoteError unitRoleUnused .next) adverseNextS20Before [] (.query 0) := by
  rw [adverseNextS20D0I5,adverseNextS20D0I0]
  have hk := adverse_next_penalty_interval 19 (by omega)
  change nextNormalPenaltyLower ≤ nextNormalPenalty adverseNextS20Before ∧ nextNormalPenalty adverseNextS20Before ≤ nextNormalPenaltyUpper at hk
  have hm : ((13/10)/4)+(15144661/12500000)-(nextNormalPenalty adverseNextS20Before) < ((0/1)/2)+(42835569/25000000)-(nextNormalPenalty adverseNextS20Before) := by
    have h : (((13/10)/4)+(15144661/12500000) : ℝ) < ((0/1)/2)+(42835569/25000000) := by norm_num
    linarith
  have h := index_weak_order_from_intervals ((0/1)/2) ((13/10)/4) (nextNormalPenalty adverseNextS20Before) (nextNormalPenalty adverseNextS20Before) (42835569/25000000) (15144661/12500000)
    (treeBonus (7/5) 19 2) (treeBonus (7/5) 19 4)
    (trajectory_bonus_19_2).1 (trajectory_bonus_19_4).2 hm.le
  simpa only [treeIndex] using h

theorem adverseNextS20D0Cmp6 : indexScore (7/5) (controlPenalty savedCref uniformQuoteError unitRoleUnused .next) adverseNextS20Before [] (.query 6) ≤ indexScore (7/5) (controlPenalty savedCref uniformQuoteError unitRoleUnused .next) adverseNextS20Before [] (.query 0) := by
  rw [adverseNextS20D0I6,adverseNextS20D0I0]

theorem adverseNextS20D0Cmp7 : indexScore (7/5) (controlPenalty savedCref uniformQuoteError unitRoleUnused .next) adverseNextS20Before [] (.query 7) ≤ indexScore (7/5) (controlPenalty savedCref uniformQuoteError unitRoleUnused .next) adverseNextS20Before [] (.query 0) := by
  rw [adverseNextS20D0I7,adverseNextS20D0I0]

theorem adverseNextS20Choice0 : nativeFirstChoice (indexScore (7/5) (controlPenalty savedCref uniformQuoteError unitRoleUnused .next) adverseNextS20Before []) adverseNextS20Before [] = .query 0 := by
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
    · exact adverseNextS20D0Cmp1
    · exact adverseNextS20D0Cmp2
    · exact adverseNextS20D0Cmp3
    · exact adverseNextS20D0Cmp4
    · exact adverseNextS20D0Cmp5
    · exact adverseNextS20D0Cmp6
    · exact adverseNextS20D0Cmp7

theorem adverseNextS20ActualEvent : nativeEvent budgetTape (7/5) (controlPenalty savedCref uniformQuoteError unitRoleUnused .next)
    (taskReward true (2/5) (1/2)) adverseNextS20Before = adverseNextEvent20 := by
  have hs0 := native_select_existing_step budgetTape (7/5) (controlPenalty savedCref uniformQuoteError unitRoleUnused .next) adverseNextS20Before 8 [] (.query 0)
    (by decide) (by decide) adverseNextS20Choice0
  have hnew := native_select_new_step budgetTape (7/5) (controlPenalty savedCref uniformQuoteError unitRoleUnused .next) adverseNextS20Before 7 [.query 0]
    [.normalRetriever 4,.normalRetriever 6,.normalRetriever 7,.normalRetriever 8,.normalRetriever 5,.normalRetriever 1,.normalRetriever 2,.normalRetriever 3,.normalRetriever 12,.normalRetriever 14,.normalRetriever 13,.normalRetriever 21,.normalRetriever 23,.normalRetriever 22,.normalRetriever 9,.normalRetriever 11,.normalRetriever 10,.normalRetriever 15,.normalRetriever 17,.normalRetriever 16,.normalRetriever 18,.normalRetriever 20,.normalRetriever 19,.normalRetriever 24,.normalRetriever 25,.normalRetriever 26,.normalRetriever 27,.normalRetriever 28,.normalRetriever 29] (.normalRetriever 4) (by decide) (by decide) (by decide) (by decide)
  have hs : nativeSelect budgetTape (7/5) (controlPenalty savedCref uniformQuoteError unitRoleUnused .next) adverseNextS20Before 9 [] = [.query 0,.normalRetriever 4] := by
    rw [hs0]
    change nativeSelect budgetTape (7/5) (controlPenalty savedCref uniformQuoteError unitRoleUnused .next) adverseNextS20Before 8 [.query 0] = _
    rw [hnew] <;> rfl
  have hr : repairedRollout budgetTape adverseNextS20Before 9 [.query 0,.normalRetriever 4] = [.query 0,.normalRetriever 4,.selection 0,.width 0,.stop,.reranker 0,.topm 0,.context 0,.answer 0] := by decide
  simp only [nativeEvent,hs,hr]
  rfl

def adverseNextS21Before := adverseNextProposal.take 20

theorem adverseNextS21D0I0 : indexScore (7/5) (controlPenalty savedCref uniformQuoteError unitRoleUnused .next) adverseNextS21Before [] (.query 0) = treeIndex ((0/1)/3) (7/5) (nextNormalPenalty adverseNextS21Before) 20 3 := by
  have hs : replayBackup adverseNextS21Before emptyStatistics ([]++[.query 0]) = ⟨3,(0/1)⟩ := by
    rw [replayBackup_empty_closed_form]
    simp +decide [backedEvents,adverseNextS21Before,adverseNextProposal,adverseNextEvent1,adverseNextEvent2,adverseNextEvent3,adverseNextEvent4,adverseNextEvent5,adverseNextEvent6,adverseNextEvent7,adverseNextEvent8,adverseNextEvent9,adverseNextEvent10,adverseNextEvent11,adverseNextEvent12,adverseNextEvent13,adverseNextEvent14,adverseNextEvent15,adverseNextEvent16,adverseNextEvent17,adverseNextEvent18,adverseNextEvent19,adverseNextEvent20,taskReward]
    <;> norm_num
  have hp : rawVisits adverseNextS21Before [] = 20 := by decide
  have hn : rawVisits adverseNextS21Before ([]++[.query 0]) = 3 := by decide
  have hz : (controlPenalty savedCref uniformQuoteError unitRoleUnused .next) adverseNextS21Before [] (.query 0) = (nextNormalPenalty adverseNextS21Before) := by
    simpa only [adverseNextS21Before,nextNormalPenalty] using AgentUCTNextExact.adverse_next_normal_root_quotes_exact 20 (by omega) 0 (by decide)
  unfold indexScore
  rw [hs,hp,hn,hz]
  simp only [BackupStat.mean]
  norm_num

theorem adverseNextS21D0I1 : indexScore (7/5) (controlPenalty savedCref uniformQuoteError unitRoleUnused .next) adverseNextS21Before [] (.query 1) = treeIndex ((0/1)/3) (7/5) 0 20 3 := by
  have hs : replayBackup adverseNextS21Before emptyStatistics ([]++[.query 1]) = ⟨3,(0/1)⟩ := by
    rw [replayBackup_empty_closed_form]
    simp +decide [backedEvents,adverseNextS21Before,adverseNextProposal,adverseNextEvent1,adverseNextEvent2,adverseNextEvent3,adverseNextEvent4,adverseNextEvent5,adverseNextEvent6,adverseNextEvent7,adverseNextEvent8,adverseNextEvent9,adverseNextEvent10,adverseNextEvent11,adverseNextEvent12,adverseNextEvent13,adverseNextEvent14,adverseNextEvent15,adverseNextEvent16,adverseNextEvent17,adverseNextEvent18,adverseNextEvent19,adverseNextEvent20,taskReward]
    <;> norm_num
  have hp : rawVisits adverseNextS21Before [] = 20 := by decide
  have hn : rawVisits adverseNextS21Before ([]++[.query 1]) = 3 := by decide
  have hz : (controlPenalty savedCref uniformQuoteError unitRoleUnused .next) adverseNextS21Before [] (.query 1) = 0 := by
    apply control_penalty_empty_suffix
    exact AgentUCTNextExact.adverse_next_hyde_root_suffix_empty 20 (by omega)
  unfold indexScore
  rw [hs,hp,hn,hz]
  simp only [BackupStat.mean]
  norm_num

theorem adverseNextS21D0I2 : indexScore (7/5) (controlPenalty savedCref uniformQuoteError unitRoleUnused .next) adverseNextS21Before [] (.query 2) = treeIndex ((0/1)/2) (7/5) (nextNormalPenalty adverseNextS21Before) 20 2 := by
  have hs : replayBackup adverseNextS21Before emptyStatistics ([]++[.query 2]) = ⟨2,(0/1)⟩ := by
    rw [replayBackup_empty_closed_form]
    simp +decide [backedEvents,adverseNextS21Before,adverseNextProposal,adverseNextEvent1,adverseNextEvent2,adverseNextEvent3,adverseNextEvent4,adverseNextEvent5,adverseNextEvent6,adverseNextEvent7,adverseNextEvent8,adverseNextEvent9,adverseNextEvent10,adverseNextEvent11,adverseNextEvent12,adverseNextEvent13,adverseNextEvent14,adverseNextEvent15,adverseNextEvent16,adverseNextEvent17,adverseNextEvent18,adverseNextEvent19,adverseNextEvent20,taskReward]
    <;> norm_num
  have hp : rawVisits adverseNextS21Before [] = 20 := by decide
  have hn : rawVisits adverseNextS21Before ([]++[.query 2]) = 2 := by decide
  have hz : (controlPenalty savedCref uniformQuoteError unitRoleUnused .next) adverseNextS21Before [] (.query 2) = (nextNormalPenalty adverseNextS21Before) := by
    simpa only [adverseNextS21Before,nextNormalPenalty] using AgentUCTNextExact.adverse_next_normal_root_quotes_exact 20 (by omega) 2 (by decide)
  unfold indexScore
  rw [hs,hp,hn,hz]
  simp only [BackupStat.mean]
  norm_num

theorem adverseNextS21D0I3 : indexScore (7/5) (controlPenalty savedCref uniformQuoteError unitRoleUnused .next) adverseNextS21Before [] (.query 3) = treeIndex ((0/1)/2) (7/5) (nextNormalPenalty adverseNextS21Before) 20 2 := by
  have hs : replayBackup adverseNextS21Before emptyStatistics ([]++[.query 3]) = ⟨2,(0/1)⟩ := by
    rw [replayBackup_empty_closed_form]
    simp +decide [backedEvents,adverseNextS21Before,adverseNextProposal,adverseNextEvent1,adverseNextEvent2,adverseNextEvent3,adverseNextEvent4,adverseNextEvent5,adverseNextEvent6,adverseNextEvent7,adverseNextEvent8,adverseNextEvent9,adverseNextEvent10,adverseNextEvent11,adverseNextEvent12,adverseNextEvent13,adverseNextEvent14,adverseNextEvent15,adverseNextEvent16,adverseNextEvent17,adverseNextEvent18,adverseNextEvent19,adverseNextEvent20,taskReward]
    <;> norm_num
  have hp : rawVisits adverseNextS21Before [] = 20 := by decide
  have hn : rawVisits adverseNextS21Before ([]++[.query 3]) = 2 := by decide
  have hz : (controlPenalty savedCref uniformQuoteError unitRoleUnused .next) adverseNextS21Before [] (.query 3) = (nextNormalPenalty adverseNextS21Before) := by
    simpa only [adverseNextS21Before,nextNormalPenalty] using AgentUCTNextExact.adverse_next_normal_root_quotes_exact 20 (by omega) 3 (by decide)
  unfold indexScore
  rw [hs,hp,hn,hz]
  simp only [BackupStat.mean]
  norm_num

theorem adverseNextS21D0I4 : indexScore (7/5) (controlPenalty savedCref uniformQuoteError unitRoleUnused .next) adverseNextS21Before [] (.query 4) = treeIndex ((0/1)/2) (7/5) (nextNormalPenalty adverseNextS21Before) 20 2 := by
  have hs : replayBackup adverseNextS21Before emptyStatistics ([]++[.query 4]) = ⟨2,(0/1)⟩ := by
    rw [replayBackup_empty_closed_form]
    simp +decide [backedEvents,adverseNextS21Before,adverseNextProposal,adverseNextEvent1,adverseNextEvent2,adverseNextEvent3,adverseNextEvent4,adverseNextEvent5,adverseNextEvent6,adverseNextEvent7,adverseNextEvent8,adverseNextEvent9,adverseNextEvent10,adverseNextEvent11,adverseNextEvent12,adverseNextEvent13,adverseNextEvent14,adverseNextEvent15,adverseNextEvent16,adverseNextEvent17,adverseNextEvent18,adverseNextEvent19,adverseNextEvent20,taskReward]
    <;> norm_num
  have hp : rawVisits adverseNextS21Before [] = 20 := by decide
  have hn : rawVisits adverseNextS21Before ([]++[.query 4]) = 2 := by decide
  have hz : (controlPenalty savedCref uniformQuoteError unitRoleUnused .next) adverseNextS21Before [] (.query 4) = (nextNormalPenalty adverseNextS21Before) := by
    simpa only [adverseNextS21Before,nextNormalPenalty] using AgentUCTNextExact.adverse_next_normal_root_quotes_exact 20 (by omega) 4 (by decide)
  unfold indexScore
  rw [hs,hp,hn,hz]
  simp only [BackupStat.mean]
  norm_num

theorem adverseNextS21D0I5 : indexScore (7/5) (controlPenalty savedCref uniformQuoteError unitRoleUnused .next) adverseNextS21Before [] (.query 5) = treeIndex ((13/10)/4) (7/5) (nextNormalPenalty adverseNextS21Before) 20 4 := by
  have hs : replayBackup adverseNextS21Before emptyStatistics ([]++[.query 5]) = ⟨4,(13/10)⟩ := by
    rw [replayBackup_empty_closed_form]
    simp +decide [backedEvents,adverseNextS21Before,adverseNextProposal,adverseNextEvent1,adverseNextEvent2,adverseNextEvent3,adverseNextEvent4,adverseNextEvent5,adverseNextEvent6,adverseNextEvent7,adverseNextEvent8,adverseNextEvent9,adverseNextEvent10,adverseNextEvent11,adverseNextEvent12,adverseNextEvent13,adverseNextEvent14,adverseNextEvent15,adverseNextEvent16,adverseNextEvent17,adverseNextEvent18,adverseNextEvent19,adverseNextEvent20,taskReward]
    <;> norm_num
  have hp : rawVisits adverseNextS21Before [] = 20 := by decide
  have hn : rawVisits adverseNextS21Before ([]++[.query 5]) = 4 := by decide
  have hz : (controlPenalty savedCref uniformQuoteError unitRoleUnused .next) adverseNextS21Before [] (.query 5) = (nextNormalPenalty adverseNextS21Before) := by
    simpa only [adverseNextS21Before,nextNormalPenalty] using AgentUCTNextExact.adverse_next_normal_root_quotes_exact 20 (by omega) 5 (by decide)
  unfold indexScore
  rw [hs,hp,hn,hz]
  simp only [BackupStat.mean]
  norm_num

theorem adverseNextS21D0I6 : indexScore (7/5) (controlPenalty savedCref uniformQuoteError unitRoleUnused .next) adverseNextS21Before [] (.query 6) = treeIndex ((0/1)/2) (7/5) (nextNormalPenalty adverseNextS21Before) 20 2 := by
  have hs : replayBackup adverseNextS21Before emptyStatistics ([]++[.query 6]) = ⟨2,(0/1)⟩ := by
    rw [replayBackup_empty_closed_form]
    simp +decide [backedEvents,adverseNextS21Before,adverseNextProposal,adverseNextEvent1,adverseNextEvent2,adverseNextEvent3,adverseNextEvent4,adverseNextEvent5,adverseNextEvent6,adverseNextEvent7,adverseNextEvent8,adverseNextEvent9,adverseNextEvent10,adverseNextEvent11,adverseNextEvent12,adverseNextEvent13,adverseNextEvent14,adverseNextEvent15,adverseNextEvent16,adverseNextEvent17,adverseNextEvent18,adverseNextEvent19,adverseNextEvent20,taskReward]
    <;> norm_num
  have hp : rawVisits adverseNextS21Before [] = 20 := by decide
  have hn : rawVisits adverseNextS21Before ([]++[.query 6]) = 2 := by decide
  have hz : (controlPenalty savedCref uniformQuoteError unitRoleUnused .next) adverseNextS21Before [] (.query 6) = (nextNormalPenalty adverseNextS21Before) := by
    simpa only [adverseNextS21Before,nextNormalPenalty] using AgentUCTNextExact.adverse_next_normal_root_quotes_exact 20 (by omega) 6 (by decide)
  unfold indexScore
  rw [hs,hp,hn,hz]
  simp only [BackupStat.mean]
  norm_num

theorem adverseNextS21D0I7 : indexScore (7/5) (controlPenalty savedCref uniformQuoteError unitRoleUnused .next) adverseNextS21Before [] (.query 7) = treeIndex ((0/1)/2) (7/5) (nextNormalPenalty adverseNextS21Before) 20 2 := by
  have hs : replayBackup adverseNextS21Before emptyStatistics ([]++[.query 7]) = ⟨2,(0/1)⟩ := by
    rw [replayBackup_empty_closed_form]
    simp +decide [backedEvents,adverseNextS21Before,adverseNextProposal,adverseNextEvent1,adverseNextEvent2,adverseNextEvent3,adverseNextEvent4,adverseNextEvent5,adverseNextEvent6,adverseNextEvent7,adverseNextEvent8,adverseNextEvent9,adverseNextEvent10,adverseNextEvent11,adverseNextEvent12,adverseNextEvent13,adverseNextEvent14,adverseNextEvent15,adverseNextEvent16,adverseNextEvent17,adverseNextEvent18,adverseNextEvent19,adverseNextEvent20,taskReward]
    <;> norm_num
  have hp : rawVisits adverseNextS21Before [] = 20 := by decide
  have hn : rawVisits adverseNextS21Before ([]++[.query 7]) = 2 := by decide
  have hz : (controlPenalty savedCref uniformQuoteError unitRoleUnused .next) adverseNextS21Before [] (.query 7) = (nextNormalPenalty adverseNextS21Before) := by
    simpa only [adverseNextS21Before,nextNormalPenalty] using AgentUCTNextExact.adverse_next_normal_root_quotes_exact 20 (by omega) 7 (by decide)
  unfold indexScore
  rw [hs,hp,hn,hz]
  simp only [BackupStat.mean]
  norm_num

theorem adverseNextS21D0Cmp0 : indexScore (7/5) (controlPenalty savedCref uniformQuoteError unitRoleUnused .next) adverseNextS21Before [] (.query 0) < indexScore (7/5) (controlPenalty savedCref uniformQuoteError unitRoleUnused .next) adverseNextS21Before [] (.query 2) := by
  rw [adverseNextS21D0I0,adverseNextS21D0I2]
  have hk := adverse_next_penalty_interval 20 (by omega)
  change nextNormalPenaltyLower ≤ nextNormalPenalty adverseNextS21Before ∧ nextNormalPenalty adverseNextS21Before ≤ nextNormalPenaltyUpper at hk
  have hm : ((0/1)/3)+(70517517/50000000)-(nextNormalPenalty adverseNextS21Before) < ((0/1)/2)+(43182979/25000000)-(nextNormalPenalty adverseNextS21Before) := by
    have h : (((0/1)/3)+(70517517/50000000) : ℝ) < ((0/1)/2)+(43182979/25000000) := by norm_num
    linarith
  have h := index_strict_order_from_intervals ((0/1)/2) ((0/1)/3) (nextNormalPenalty adverseNextS21Before) (nextNormalPenalty adverseNextS21Before) (43182979/25000000) (70517517/50000000)
    (treeBonus (7/5) 20 2) (treeBonus (7/5) 20 3)
    (trajectory_bonus_20_2).1 (trajectory_bonus_20_3).2 hm
  simpa only [treeIndex] using h

theorem adverseNextS21D0Cmp1 : indexScore (7/5) (controlPenalty savedCref uniformQuoteError unitRoleUnused .next) adverseNextS21Before [] (.query 1) < indexScore (7/5) (controlPenalty savedCref uniformQuoteError unitRoleUnused .next) adverseNextS21Before [] (.query 2) := by
  rw [adverseNextS21D0I1,adverseNextS21D0I2]
  have hk := adverse_next_penalty_interval 20 (by omega)
  change nextNormalPenaltyLower ≤ nextNormalPenalty adverseNextS21Before ∧ nextNormalPenalty adverseNextS21Before ≤ nextNormalPenaltyUpper at hk
  have hm : ((0/1)/3)+(70517517/50000000)-0 < ((0/1)/2)+(43182979/25000000)-(nextNormalPenalty adverseNextS21Before) := by
    have h : ((0/1)/3)+(70517517/50000000) < ((0/1)/2)+(43182979/25000000)-nextNormalPenaltyUpper := by norm_num [nextNormalPenaltyUpper,savedCref,uniformQuoteError]
    linarith [hk.2]
  have h := index_strict_order_from_intervals ((0/1)/2) ((0/1)/3) (nextNormalPenalty adverseNextS21Before) 0 (43182979/25000000) (70517517/50000000)
    (treeBonus (7/5) 20 2) (treeBonus (7/5) 20 3)
    (trajectory_bonus_20_2).1 (trajectory_bonus_20_3).2 hm
  simpa only [treeIndex] using h

theorem adverseNextS21D0Cmp3 : indexScore (7/5) (controlPenalty savedCref uniformQuoteError unitRoleUnused .next) adverseNextS21Before [] (.query 3) ≤ indexScore (7/5) (controlPenalty savedCref uniformQuoteError unitRoleUnused .next) adverseNextS21Before [] (.query 2) := by
  rw [adverseNextS21D0I3,adverseNextS21D0I2]

theorem adverseNextS21D0Cmp4 : indexScore (7/5) (controlPenalty savedCref uniformQuoteError unitRoleUnused .next) adverseNextS21Before [] (.query 4) ≤ indexScore (7/5) (controlPenalty savedCref uniformQuoteError unitRoleUnused .next) adverseNextS21Before [] (.query 2) := by
  rw [adverseNextS21D0I4,adverseNextS21D0I2]

theorem adverseNextS21D0Cmp5 : indexScore (7/5) (controlPenalty savedCref uniformQuoteError unitRoleUnused .next) adverseNextS21Before [] (.query 5) ≤ indexScore (7/5) (controlPenalty savedCref uniformQuoteError unitRoleUnused .next) adverseNextS21Before [] (.query 2) := by
  rw [adverseNextS21D0I5,adverseNextS21D0I2]
  have hk := adverse_next_penalty_interval 20 (by omega)
  change nextNormalPenaltyLower ≤ nextNormalPenalty adverseNextS21Before ∧ nextNormalPenalty adverseNextS21Before ≤ nextNormalPenaltyUpper at hk
  have hm : ((13/10)/4)+(61069967/50000000)-(nextNormalPenalty adverseNextS21Before) < ((0/1)/2)+(43182979/25000000)-(nextNormalPenalty adverseNextS21Before) := by
    have h : (((13/10)/4)+(61069967/50000000) : ℝ) < ((0/1)/2)+(43182979/25000000) := by norm_num
    linarith
  have h := index_weak_order_from_intervals ((0/1)/2) ((13/10)/4) (nextNormalPenalty adverseNextS21Before) (nextNormalPenalty adverseNextS21Before) (43182979/25000000) (61069967/50000000)
    (treeBonus (7/5) 20 2) (treeBonus (7/5) 20 4)
    (trajectory_bonus_20_2).1 (trajectory_bonus_20_4).2 hm.le
  simpa only [treeIndex] using h

theorem adverseNextS21D0Cmp6 : indexScore (7/5) (controlPenalty savedCref uniformQuoteError unitRoleUnused .next) adverseNextS21Before [] (.query 6) ≤ indexScore (7/5) (controlPenalty savedCref uniformQuoteError unitRoleUnused .next) adverseNextS21Before [] (.query 2) := by
  rw [adverseNextS21D0I6,adverseNextS21D0I2]

theorem adverseNextS21D0Cmp7 : indexScore (7/5) (controlPenalty savedCref uniformQuoteError unitRoleUnused .next) adverseNextS21Before [] (.query 7) ≤ indexScore (7/5) (controlPenalty savedCref uniformQuoteError unitRoleUnused .next) adverseNextS21Before [] (.query 2) := by
  rw [adverseNextS21D0I7,adverseNextS21D0I2]

theorem adverseNextS21Choice0 : nativeFirstChoice (indexScore (7/5) (controlPenalty savedCref uniformQuoteError unitRoleUnused .next) adverseNextS21Before []) adverseNextS21Before [] = .query 2 := by
  apply visited_choice_from_ordered_certificate _ _ [] [.query 0,.query 1] [.query 3,.query 4,.query 5,.query 6,.query 7] (.query 2) (by decide)
  · intro a ha
    have ho : orderedLegalAvailable [] = [.query 0,.query 1,.query 2,.query 3,.query 4,.query 5,.query 6,.query 7] := by decide
    rw [ho] at ha
    simp only [List.mem_cons,List.not_mem_nil,or_false] at ha
    rcases ha with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> decide
  · intro a ha
    simp only [List.mem_cons,List.not_mem_nil,or_false] at ha
    rcases ha with rfl | rfl
    · exact adverseNextS21D0Cmp0
    · exact adverseNextS21D0Cmp1
  · intro a ha
    simp only [List.mem_cons,List.not_mem_nil,or_false] at ha
    rcases ha with rfl | rfl | rfl | rfl | rfl
    · exact adverseNextS21D0Cmp3
    · exact adverseNextS21D0Cmp4
    · exact adverseNextS21D0Cmp5
    · exact adverseNextS21D0Cmp6
    · exact adverseNextS21D0Cmp7

theorem adverseNextS21ActualEvent : nativeEvent budgetTape (7/5) (controlPenalty savedCref uniformQuoteError unitRoleUnused .next)
    (taskReward true (2/5) (1/2)) adverseNextS21Before = adverseNextEvent21 := by
  have hs0 := native_select_existing_step budgetTape (7/5) (controlPenalty savedCref uniformQuoteError unitRoleUnused .next) adverseNextS21Before 8 [] (.query 2)
    (by decide) (by decide) adverseNextS21Choice0
  have hnew := native_select_new_step budgetTape (7/5) (controlPenalty savedCref uniformQuoteError unitRoleUnused .next) adverseNextS21Before 7 [.query 2]
    [.normalRetriever 4,.normalRetriever 6,.normalRetriever 7,.normalRetriever 8,.normalRetriever 5,.normalRetriever 1,.normalRetriever 2,.normalRetriever 3,.normalRetriever 12,.normalRetriever 14,.normalRetriever 13,.normalRetriever 21,.normalRetriever 23,.normalRetriever 22,.normalRetriever 9,.normalRetriever 11,.normalRetriever 10,.normalRetriever 15,.normalRetriever 17,.normalRetriever 16,.normalRetriever 18,.normalRetriever 20,.normalRetriever 19,.normalRetriever 24,.normalRetriever 25,.normalRetriever 26,.normalRetriever 27,.normalRetriever 28,.normalRetriever 29] (.normalRetriever 4) (by decide) (by decide) (by decide) (by decide)
  have hs : nativeSelect budgetTape (7/5) (controlPenalty savedCref uniformQuoteError unitRoleUnused .next) adverseNextS21Before 9 [] = [.query 2,.normalRetriever 4] := by
    rw [hs0]
    change nativeSelect budgetTape (7/5) (controlPenalty savedCref uniformQuoteError unitRoleUnused .next) adverseNextS21Before 8 [.query 2] = _
    rw [hnew] <;> rfl
  have hr : repairedRollout budgetTape adverseNextS21Before 9 [.query 2,.normalRetriever 4] = [.query 2,.normalRetriever 4,.selection 0,.width 0,.stop,.reranker 0,.topm 0,.context 0,.answer 0] := by decide
  simp only [nativeEvent,hs,hr]
  rfl

def adverseNextS22Before := adverseNextProposal.take 21

theorem adverseNextS22D0I0 : indexScore (7/5) (controlPenalty savedCref uniformQuoteError unitRoleUnused .next) adverseNextS22Before [] (.query 0) = treeIndex ((0/1)/3) (7/5) (nextNormalPenalty adverseNextS22Before) 21 3 := by
  have hs : replayBackup adverseNextS22Before emptyStatistics ([]++[.query 0]) = ⟨3,(0/1)⟩ := by
    rw [replayBackup_empty_closed_form]
    simp +decide [backedEvents,adverseNextS22Before,adverseNextProposal,adverseNextEvent1,adverseNextEvent2,adverseNextEvent3,adverseNextEvent4,adverseNextEvent5,adverseNextEvent6,adverseNextEvent7,adverseNextEvent8,adverseNextEvent9,adverseNextEvent10,adverseNextEvent11,adverseNextEvent12,adverseNextEvent13,adverseNextEvent14,adverseNextEvent15,adverseNextEvent16,adverseNextEvent17,adverseNextEvent18,adverseNextEvent19,adverseNextEvent20,adverseNextEvent21,taskReward]
    <;> norm_num
  have hp : rawVisits adverseNextS22Before [] = 21 := by decide
  have hn : rawVisits adverseNextS22Before ([]++[.query 0]) = 3 := by decide
  have hz : (controlPenalty savedCref uniformQuoteError unitRoleUnused .next) adverseNextS22Before [] (.query 0) = (nextNormalPenalty adverseNextS22Before) := by
    simpa only [adverseNextS22Before,nextNormalPenalty] using AgentUCTNextExact.adverse_next_normal_root_quotes_exact 21 (by omega) 0 (by decide)
  unfold indexScore
  rw [hs,hp,hn,hz]
  simp only [BackupStat.mean]
  norm_num

theorem adverseNextS22D0I1 : indexScore (7/5) (controlPenalty savedCref uniformQuoteError unitRoleUnused .next) adverseNextS22Before [] (.query 1) = treeIndex ((0/1)/3) (7/5) 0 21 3 := by
  have hs : replayBackup adverseNextS22Before emptyStatistics ([]++[.query 1]) = ⟨3,(0/1)⟩ := by
    rw [replayBackup_empty_closed_form]
    simp +decide [backedEvents,adverseNextS22Before,adverseNextProposal,adverseNextEvent1,adverseNextEvent2,adverseNextEvent3,adverseNextEvent4,adverseNextEvent5,adverseNextEvent6,adverseNextEvent7,adverseNextEvent8,adverseNextEvent9,adverseNextEvent10,adverseNextEvent11,adverseNextEvent12,adverseNextEvent13,adverseNextEvent14,adverseNextEvent15,adverseNextEvent16,adverseNextEvent17,adverseNextEvent18,adverseNextEvent19,adverseNextEvent20,adverseNextEvent21,taskReward]
    <;> norm_num
  have hp : rawVisits adverseNextS22Before [] = 21 := by decide
  have hn : rawVisits adverseNextS22Before ([]++[.query 1]) = 3 := by decide
  have hz : (controlPenalty savedCref uniformQuoteError unitRoleUnused .next) adverseNextS22Before [] (.query 1) = 0 := by
    apply control_penalty_empty_suffix
    exact AgentUCTNextExact.adverse_next_hyde_root_suffix_empty 21 (by omega)
  unfold indexScore
  rw [hs,hp,hn,hz]
  simp only [BackupStat.mean]
  norm_num

theorem adverseNextS22D0I2 : indexScore (7/5) (controlPenalty savedCref uniformQuoteError unitRoleUnused .next) adverseNextS22Before [] (.query 2) = treeIndex ((0/1)/3) (7/5) (nextNormalPenalty adverseNextS22Before) 21 3 := by
  have hs : replayBackup adverseNextS22Before emptyStatistics ([]++[.query 2]) = ⟨3,(0/1)⟩ := by
    rw [replayBackup_empty_closed_form]
    simp +decide [backedEvents,adverseNextS22Before,adverseNextProposal,adverseNextEvent1,adverseNextEvent2,adverseNextEvent3,adverseNextEvent4,adverseNextEvent5,adverseNextEvent6,adverseNextEvent7,adverseNextEvent8,adverseNextEvent9,adverseNextEvent10,adverseNextEvent11,adverseNextEvent12,adverseNextEvent13,adverseNextEvent14,adverseNextEvent15,adverseNextEvent16,adverseNextEvent17,adverseNextEvent18,adverseNextEvent19,adverseNextEvent20,adverseNextEvent21,taskReward]
    <;> norm_num
  have hp : rawVisits adverseNextS22Before [] = 21 := by decide
  have hn : rawVisits adverseNextS22Before ([]++[.query 2]) = 3 := by decide
  have hz : (controlPenalty savedCref uniformQuoteError unitRoleUnused .next) adverseNextS22Before [] (.query 2) = (nextNormalPenalty adverseNextS22Before) := by
    simpa only [adverseNextS22Before,nextNormalPenalty] using AgentUCTNextExact.adverse_next_normal_root_quotes_exact 21 (by omega) 2 (by decide)
  unfold indexScore
  rw [hs,hp,hn,hz]
  simp only [BackupStat.mean]
  norm_num

theorem adverseNextS22D0I3 : indexScore (7/5) (controlPenalty savedCref uniformQuoteError unitRoleUnused .next) adverseNextS22Before [] (.query 3) = treeIndex ((0/1)/2) (7/5) (nextNormalPenalty adverseNextS22Before) 21 2 := by
  have hs : replayBackup adverseNextS22Before emptyStatistics ([]++[.query 3]) = ⟨2,(0/1)⟩ := by
    rw [replayBackup_empty_closed_form]
    simp +decide [backedEvents,adverseNextS22Before,adverseNextProposal,adverseNextEvent1,adverseNextEvent2,adverseNextEvent3,adverseNextEvent4,adverseNextEvent5,adverseNextEvent6,adverseNextEvent7,adverseNextEvent8,adverseNextEvent9,adverseNextEvent10,adverseNextEvent11,adverseNextEvent12,adverseNextEvent13,adverseNextEvent14,adverseNextEvent15,adverseNextEvent16,adverseNextEvent17,adverseNextEvent18,adverseNextEvent19,adverseNextEvent20,adverseNextEvent21,taskReward]
    <;> norm_num
  have hp : rawVisits adverseNextS22Before [] = 21 := by decide
  have hn : rawVisits adverseNextS22Before ([]++[.query 3]) = 2 := by decide
  have hz : (controlPenalty savedCref uniformQuoteError unitRoleUnused .next) adverseNextS22Before [] (.query 3) = (nextNormalPenalty adverseNextS22Before) := by
    simpa only [adverseNextS22Before,nextNormalPenalty] using AgentUCTNextExact.adverse_next_normal_root_quotes_exact 21 (by omega) 3 (by decide)
  unfold indexScore
  rw [hs,hp,hn,hz]
  simp only [BackupStat.mean]
  norm_num

theorem adverseNextS22D0I4 : indexScore (7/5) (controlPenalty savedCref uniformQuoteError unitRoleUnused .next) adverseNextS22Before [] (.query 4) = treeIndex ((0/1)/2) (7/5) (nextNormalPenalty adverseNextS22Before) 21 2 := by
  have hs : replayBackup adverseNextS22Before emptyStatistics ([]++[.query 4]) = ⟨2,(0/1)⟩ := by
    rw [replayBackup_empty_closed_form]
    simp +decide [backedEvents,adverseNextS22Before,adverseNextProposal,adverseNextEvent1,adverseNextEvent2,adverseNextEvent3,adverseNextEvent4,adverseNextEvent5,adverseNextEvent6,adverseNextEvent7,adverseNextEvent8,adverseNextEvent9,adverseNextEvent10,adverseNextEvent11,adverseNextEvent12,adverseNextEvent13,adverseNextEvent14,adverseNextEvent15,adverseNextEvent16,adverseNextEvent17,adverseNextEvent18,adverseNextEvent19,adverseNextEvent20,adverseNextEvent21,taskReward]
    <;> norm_num
  have hp : rawVisits adverseNextS22Before [] = 21 := by decide
  have hn : rawVisits adverseNextS22Before ([]++[.query 4]) = 2 := by decide
  have hz : (controlPenalty savedCref uniformQuoteError unitRoleUnused .next) adverseNextS22Before [] (.query 4) = (nextNormalPenalty adverseNextS22Before) := by
    simpa only [adverseNextS22Before,nextNormalPenalty] using AgentUCTNextExact.adverse_next_normal_root_quotes_exact 21 (by omega) 4 (by decide)
  unfold indexScore
  rw [hs,hp,hn,hz]
  simp only [BackupStat.mean]
  norm_num

theorem adverseNextS22D0I5 : indexScore (7/5) (controlPenalty savedCref uniformQuoteError unitRoleUnused .next) adverseNextS22Before [] (.query 5) = treeIndex ((13/10)/4) (7/5) (nextNormalPenalty adverseNextS22Before) 21 4 := by
  have hs : replayBackup adverseNextS22Before emptyStatistics ([]++[.query 5]) = ⟨4,(13/10)⟩ := by
    rw [replayBackup_empty_closed_form]
    simp +decide [backedEvents,adverseNextS22Before,adverseNextProposal,adverseNextEvent1,adverseNextEvent2,adverseNextEvent3,adverseNextEvent4,adverseNextEvent5,adverseNextEvent6,adverseNextEvent7,adverseNextEvent8,adverseNextEvent9,adverseNextEvent10,adverseNextEvent11,adverseNextEvent12,adverseNextEvent13,adverseNextEvent14,adverseNextEvent15,adverseNextEvent16,adverseNextEvent17,adverseNextEvent18,adverseNextEvent19,adverseNextEvent20,adverseNextEvent21,taskReward]
    <;> norm_num
  have hp : rawVisits adverseNextS22Before [] = 21 := by decide
  have hn : rawVisits adverseNextS22Before ([]++[.query 5]) = 4 := by decide
  have hz : (controlPenalty savedCref uniformQuoteError unitRoleUnused .next) adverseNextS22Before [] (.query 5) = (nextNormalPenalty adverseNextS22Before) := by
    simpa only [adverseNextS22Before,nextNormalPenalty] using AgentUCTNextExact.adverse_next_normal_root_quotes_exact 21 (by omega) 5 (by decide)
  unfold indexScore
  rw [hs,hp,hn,hz]
  simp only [BackupStat.mean]
  norm_num

theorem adverseNextS22D0I6 : indexScore (7/5) (controlPenalty savedCref uniformQuoteError unitRoleUnused .next) adverseNextS22Before [] (.query 6) = treeIndex ((0/1)/2) (7/5) (nextNormalPenalty adverseNextS22Before) 21 2 := by
  have hs : replayBackup adverseNextS22Before emptyStatistics ([]++[.query 6]) = ⟨2,(0/1)⟩ := by
    rw [replayBackup_empty_closed_form]
    simp +decide [backedEvents,adverseNextS22Before,adverseNextProposal,adverseNextEvent1,adverseNextEvent2,adverseNextEvent3,adverseNextEvent4,adverseNextEvent5,adverseNextEvent6,adverseNextEvent7,adverseNextEvent8,adverseNextEvent9,adverseNextEvent10,adverseNextEvent11,adverseNextEvent12,adverseNextEvent13,adverseNextEvent14,adverseNextEvent15,adverseNextEvent16,adverseNextEvent17,adverseNextEvent18,adverseNextEvent19,adverseNextEvent20,adverseNextEvent21,taskReward]
    <;> norm_num
  have hp : rawVisits adverseNextS22Before [] = 21 := by decide
  have hn : rawVisits adverseNextS22Before ([]++[.query 6]) = 2 := by decide
  have hz : (controlPenalty savedCref uniformQuoteError unitRoleUnused .next) adverseNextS22Before [] (.query 6) = (nextNormalPenalty adverseNextS22Before) := by
    simpa only [adverseNextS22Before,nextNormalPenalty] using AgentUCTNextExact.adverse_next_normal_root_quotes_exact 21 (by omega) 6 (by decide)
  unfold indexScore
  rw [hs,hp,hn,hz]
  simp only [BackupStat.mean]
  norm_num

theorem adverseNextS22D0I7 : indexScore (7/5) (controlPenalty savedCref uniformQuoteError unitRoleUnused .next) adverseNextS22Before [] (.query 7) = treeIndex ((0/1)/2) (7/5) (nextNormalPenalty adverseNextS22Before) 21 2 := by
  have hs : replayBackup adverseNextS22Before emptyStatistics ([]++[.query 7]) = ⟨2,(0/1)⟩ := by
    rw [replayBackup_empty_closed_form]
    simp +decide [backedEvents,adverseNextS22Before,adverseNextProposal,adverseNextEvent1,adverseNextEvent2,adverseNextEvent3,adverseNextEvent4,adverseNextEvent5,adverseNextEvent6,adverseNextEvent7,adverseNextEvent8,adverseNextEvent9,adverseNextEvent10,adverseNextEvent11,adverseNextEvent12,adverseNextEvent13,adverseNextEvent14,adverseNextEvent15,adverseNextEvent16,adverseNextEvent17,adverseNextEvent18,adverseNextEvent19,adverseNextEvent20,adverseNextEvent21,taskReward]
    <;> norm_num
  have hp : rawVisits adverseNextS22Before [] = 21 := by decide
  have hn : rawVisits adverseNextS22Before ([]++[.query 7]) = 2 := by decide
  have hz : (controlPenalty savedCref uniformQuoteError unitRoleUnused .next) adverseNextS22Before [] (.query 7) = (nextNormalPenalty adverseNextS22Before) := by
    simpa only [adverseNextS22Before,nextNormalPenalty] using AgentUCTNextExact.adverse_next_normal_root_quotes_exact 21 (by omega) 7 (by decide)
  unfold indexScore
  rw [hs,hp,hn,hz]
  simp only [BackupStat.mean]
  norm_num

theorem adverseNextS22D0Cmp0 : indexScore (7/5) (controlPenalty savedCref uniformQuoteError unitRoleUnused .next) adverseNextS22Before [] (.query 0) < indexScore (7/5) (controlPenalty savedCref uniformQuoteError unitRoleUnused .next) adverseNextS22Before [] (.query 3) := by
  rw [adverseNextS22D0I0,adverseNextS22D0I3]
  have hk := adverse_next_penalty_interval 21 (by omega)
  change nextNormalPenaltyLower ≤ nextNormalPenalty adverseNextS22Before ∧ nextNormalPenalty adverseNextS22Before ≤ nextNormalPenaltyUpper at hk
  have hm : ((0/1)/3)+(17763557/12500000)-(nextNormalPenalty adverseNextS22Before) < ((0/1)/2)+(87023293/50000000)-(nextNormalPenalty adverseNextS22Before) := by
    have h : (((0/1)/3)+(17763557/12500000) : ℝ) < ((0/1)/2)+(87023293/50000000) := by norm_num
    linarith
  have h := index_strict_order_from_intervals ((0/1)/2) ((0/1)/3) (nextNormalPenalty adverseNextS22Before) (nextNormalPenalty adverseNextS22Before) (87023293/50000000) (17763557/12500000)
    (treeBonus (7/5) 21 2) (treeBonus (7/5) 21 3)
    (trajectory_bonus_21_2).1 (trajectory_bonus_21_3).2 hm
  simpa only [treeIndex] using h

theorem adverseNextS22D0Cmp1 : indexScore (7/5) (controlPenalty savedCref uniformQuoteError unitRoleUnused .next) adverseNextS22Before [] (.query 1) < indexScore (7/5) (controlPenalty savedCref uniformQuoteError unitRoleUnused .next) adverseNextS22Before [] (.query 3) := by
  rw [adverseNextS22D0I1,adverseNextS22D0I3]
  have hk := adverse_next_penalty_interval 21 (by omega)
  change nextNormalPenaltyLower ≤ nextNormalPenalty adverseNextS22Before ∧ nextNormalPenalty adverseNextS22Before ≤ nextNormalPenaltyUpper at hk
  have hm : ((0/1)/3)+(17763557/12500000)-0 < ((0/1)/2)+(87023293/50000000)-(nextNormalPenalty adverseNextS22Before) := by
    have h : ((0/1)/3)+(17763557/12500000) < ((0/1)/2)+(87023293/50000000)-nextNormalPenaltyUpper := by norm_num [nextNormalPenaltyUpper,savedCref,uniformQuoteError]
    linarith [hk.2]
  have h := index_strict_order_from_intervals ((0/1)/2) ((0/1)/3) (nextNormalPenalty adverseNextS22Before) 0 (87023293/50000000) (17763557/12500000)
    (treeBonus (7/5) 21 2) (treeBonus (7/5) 21 3)
    (trajectory_bonus_21_2).1 (trajectory_bonus_21_3).2 hm
  simpa only [treeIndex] using h

theorem adverseNextS22D0Cmp2 : indexScore (7/5) (controlPenalty savedCref uniformQuoteError unitRoleUnused .next) adverseNextS22Before [] (.query 2) < indexScore (7/5) (controlPenalty savedCref uniformQuoteError unitRoleUnused .next) adverseNextS22Before [] (.query 3) := by
  rw [adverseNextS22D0I2,adverseNextS22D0I3]
  have hk := adverse_next_penalty_interval 21 (by omega)
  change nextNormalPenaltyLower ≤ nextNormalPenalty adverseNextS22Before ∧ nextNormalPenalty adverseNextS22Before ≤ nextNormalPenaltyUpper at hk
  have hm : ((0/1)/3)+(17763557/12500000)-(nextNormalPenalty adverseNextS22Before) < ((0/1)/2)+(87023293/50000000)-(nextNormalPenalty adverseNextS22Before) := by
    have h : (((0/1)/3)+(17763557/12500000) : ℝ) < ((0/1)/2)+(87023293/50000000) := by norm_num
    linarith
  have h := index_strict_order_from_intervals ((0/1)/2) ((0/1)/3) (nextNormalPenalty adverseNextS22Before) (nextNormalPenalty adverseNextS22Before) (87023293/50000000) (17763557/12500000)
    (treeBonus (7/5) 21 2) (treeBonus (7/5) 21 3)
    (trajectory_bonus_21_2).1 (trajectory_bonus_21_3).2 hm
  simpa only [treeIndex] using h

theorem adverseNextS22D0Cmp4 : indexScore (7/5) (controlPenalty savedCref uniformQuoteError unitRoleUnused .next) adverseNextS22Before [] (.query 4) ≤ indexScore (7/5) (controlPenalty savedCref uniformQuoteError unitRoleUnused .next) adverseNextS22Before [] (.query 3) := by
  rw [adverseNextS22D0I4,adverseNextS22D0I3]

theorem adverseNextS22D0Cmp5 : indexScore (7/5) (controlPenalty savedCref uniformQuoteError unitRoleUnused .next) adverseNextS22Before [] (.query 5) ≤ indexScore (7/5) (controlPenalty savedCref uniformQuoteError unitRoleUnused .next) adverseNextS22Before [] (.query 3) := by
  rw [adverseNextS22D0I5,adverseNextS22D0I3]
  have hk := adverse_next_penalty_interval 21 (by omega)
  change nextNormalPenaltyLower ≤ nextNormalPenalty adverseNextS22Before ∧ nextNormalPenalty adverseNextS22Before ≤ nextNormalPenaltyUpper at hk
  have hm : ((13/10)/4)+(61534767/50000000)-(nextNormalPenalty adverseNextS22Before) < ((0/1)/2)+(87023293/50000000)-(nextNormalPenalty adverseNextS22Before) := by
    have h : (((13/10)/4)+(61534767/50000000) : ℝ) < ((0/1)/2)+(87023293/50000000) := by norm_num
    linarith
  have h := index_weak_order_from_intervals ((0/1)/2) ((13/10)/4) (nextNormalPenalty adverseNextS22Before) (nextNormalPenalty adverseNextS22Before) (87023293/50000000) (61534767/50000000)
    (treeBonus (7/5) 21 2) (treeBonus (7/5) 21 4)
    (trajectory_bonus_21_2).1 (trajectory_bonus_21_4).2 hm.le
  simpa only [treeIndex] using h

theorem adverseNextS22D0Cmp6 : indexScore (7/5) (controlPenalty savedCref uniformQuoteError unitRoleUnused .next) adverseNextS22Before [] (.query 6) ≤ indexScore (7/5) (controlPenalty savedCref uniformQuoteError unitRoleUnused .next) adverseNextS22Before [] (.query 3) := by
  rw [adverseNextS22D0I6,adverseNextS22D0I3]

theorem adverseNextS22D0Cmp7 : indexScore (7/5) (controlPenalty savedCref uniformQuoteError unitRoleUnused .next) adverseNextS22Before [] (.query 7) ≤ indexScore (7/5) (controlPenalty savedCref uniformQuoteError unitRoleUnused .next) adverseNextS22Before [] (.query 3) := by
  rw [adverseNextS22D0I7,adverseNextS22D0I3]

theorem adverseNextS22Choice0 : nativeFirstChoice (indexScore (7/5) (controlPenalty savedCref uniformQuoteError unitRoleUnused .next) adverseNextS22Before []) adverseNextS22Before [] = .query 3 := by
  apply visited_choice_from_ordered_certificate _ _ [] [.query 0,.query 1,.query 2] [.query 4,.query 5,.query 6,.query 7] (.query 3) (by decide)
  · intro a ha
    have ho : orderedLegalAvailable [] = [.query 0,.query 1,.query 2,.query 3,.query 4,.query 5,.query 6,.query 7] := by decide
    rw [ho] at ha
    simp only [List.mem_cons,List.not_mem_nil,or_false] at ha
    rcases ha with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> decide
  · intro a ha
    simp only [List.mem_cons,List.not_mem_nil,or_false] at ha
    rcases ha with rfl | rfl | rfl
    · exact adverseNextS22D0Cmp0
    · exact adverseNextS22D0Cmp1
    · exact adverseNextS22D0Cmp2
  · intro a ha
    simp only [List.mem_cons,List.not_mem_nil,or_false] at ha
    rcases ha with rfl | rfl | rfl | rfl
    · exact adverseNextS22D0Cmp4
    · exact adverseNextS22D0Cmp5
    · exact adverseNextS22D0Cmp6
    · exact adverseNextS22D0Cmp7

theorem adverseNextS22ActualEvent : nativeEvent budgetTape (7/5) (controlPenalty savedCref uniformQuoteError unitRoleUnused .next)
    (taskReward true (2/5) (1/2)) adverseNextS22Before = adverseNextEvent22 := by
  have hs0 := native_select_existing_step budgetTape (7/5) (controlPenalty savedCref uniformQuoteError unitRoleUnused .next) adverseNextS22Before 8 [] (.query 3)
    (by decide) (by decide) adverseNextS22Choice0
  have hnew := native_select_new_step budgetTape (7/5) (controlPenalty savedCref uniformQuoteError unitRoleUnused .next) adverseNextS22Before 7 [.query 3]
    [.normalRetriever 4,.normalRetriever 6,.normalRetriever 7,.normalRetriever 8,.normalRetriever 5,.normalRetriever 1,.normalRetriever 2,.normalRetriever 3,.normalRetriever 12,.normalRetriever 14,.normalRetriever 13,.normalRetriever 21,.normalRetriever 23,.normalRetriever 22,.normalRetriever 9,.normalRetriever 11,.normalRetriever 10,.normalRetriever 15,.normalRetriever 17,.normalRetriever 16,.normalRetriever 18,.normalRetriever 20,.normalRetriever 19,.normalRetriever 24,.normalRetriever 25,.normalRetriever 26,.normalRetriever 27,.normalRetriever 28,.normalRetriever 29] (.normalRetriever 4) (by decide) (by decide) (by decide) (by decide)
  have hs : nativeSelect budgetTape (7/5) (controlPenalty savedCref uniformQuoteError unitRoleUnused .next) adverseNextS22Before 9 [] = [.query 3,.normalRetriever 4] := by
    rw [hs0]
    change nativeSelect budgetTape (7/5) (controlPenalty savedCref uniformQuoteError unitRoleUnused .next) adverseNextS22Before 8 [.query 3] = _
    rw [hnew] <;> rfl
  have hr : repairedRollout budgetTape adverseNextS22Before 9 [.query 3,.normalRetriever 4] = [.query 3,.normalRetriever 4,.selection 0,.width 0,.stop,.reranker 0,.topm 0,.context 0,.answer 0] := by decide
  simp only [nativeEvent,hs,hr]
  rfl

def adverseNextS23Before := adverseNextProposal.take 22

theorem adverseNextS23D0I0 : indexScore (7/5) (controlPenalty savedCref uniformQuoteError unitRoleUnused .next) adverseNextS23Before [] (.query 0) = treeIndex ((0/1)/3) (7/5) (nextNormalPenalty adverseNextS23Before) 22 3 := by
  have hs : replayBackup adverseNextS23Before emptyStatistics ([]++[.query 0]) = ⟨3,(0/1)⟩ := by
    rw [replayBackup_empty_closed_form]
    simp +decide [backedEvents,adverseNextS23Before,adverseNextProposal,adverseNextEvent1,adverseNextEvent2,adverseNextEvent3,adverseNextEvent4,adverseNextEvent5,adverseNextEvent6,adverseNextEvent7,adverseNextEvent8,adverseNextEvent9,adverseNextEvent10,adverseNextEvent11,adverseNextEvent12,adverseNextEvent13,adverseNextEvent14,adverseNextEvent15,adverseNextEvent16,adverseNextEvent17,adverseNextEvent18,adverseNextEvent19,adverseNextEvent20,adverseNextEvent21,adverseNextEvent22,taskReward]
    <;> norm_num
  have hp : rawVisits adverseNextS23Before [] = 22 := by decide
  have hn : rawVisits adverseNextS23Before ([]++[.query 0]) = 3 := by decide
  have hz : (controlPenalty savedCref uniformQuoteError unitRoleUnused .next) adverseNextS23Before [] (.query 0) = (nextNormalPenalty adverseNextS23Before) := by
    simpa only [adverseNextS23Before,nextNormalPenalty] using AgentUCTNextExact.adverse_next_normal_root_quotes_exact 22 (by omega) 0 (by decide)
  unfold indexScore
  rw [hs,hp,hn,hz]
  simp only [BackupStat.mean]
  norm_num

theorem adverseNextS23D0I1 : indexScore (7/5) (controlPenalty savedCref uniformQuoteError unitRoleUnused .next) adverseNextS23Before [] (.query 1) = treeIndex ((0/1)/3) (7/5) 0 22 3 := by
  have hs : replayBackup adverseNextS23Before emptyStatistics ([]++[.query 1]) = ⟨3,(0/1)⟩ := by
    rw [replayBackup_empty_closed_form]
    simp +decide [backedEvents,adverseNextS23Before,adverseNextProposal,adverseNextEvent1,adverseNextEvent2,adverseNextEvent3,adverseNextEvent4,adverseNextEvent5,adverseNextEvent6,adverseNextEvent7,adverseNextEvent8,adverseNextEvent9,adverseNextEvent10,adverseNextEvent11,adverseNextEvent12,adverseNextEvent13,adverseNextEvent14,adverseNextEvent15,adverseNextEvent16,adverseNextEvent17,adverseNextEvent18,adverseNextEvent19,adverseNextEvent20,adverseNextEvent21,adverseNextEvent22,taskReward]
    <;> norm_num
  have hp : rawVisits adverseNextS23Before [] = 22 := by decide
  have hn : rawVisits adverseNextS23Before ([]++[.query 1]) = 3 := by decide
  have hz : (controlPenalty savedCref uniformQuoteError unitRoleUnused .next) adverseNextS23Before [] (.query 1) = 0 := by
    apply control_penalty_empty_suffix
    exact AgentUCTNextExact.adverse_next_hyde_root_suffix_empty 22 (by omega)
  unfold indexScore
  rw [hs,hp,hn,hz]
  simp only [BackupStat.mean]
  norm_num

theorem adverseNextS23D0I2 : indexScore (7/5) (controlPenalty savedCref uniformQuoteError unitRoleUnused .next) adverseNextS23Before [] (.query 2) = treeIndex ((0/1)/3) (7/5) (nextNormalPenalty adverseNextS23Before) 22 3 := by
  have hs : replayBackup adverseNextS23Before emptyStatistics ([]++[.query 2]) = ⟨3,(0/1)⟩ := by
    rw [replayBackup_empty_closed_form]
    simp +decide [backedEvents,adverseNextS23Before,adverseNextProposal,adverseNextEvent1,adverseNextEvent2,adverseNextEvent3,adverseNextEvent4,adverseNextEvent5,adverseNextEvent6,adverseNextEvent7,adverseNextEvent8,adverseNextEvent9,adverseNextEvent10,adverseNextEvent11,adverseNextEvent12,adverseNextEvent13,adverseNextEvent14,adverseNextEvent15,adverseNextEvent16,adverseNextEvent17,adverseNextEvent18,adverseNextEvent19,adverseNextEvent20,adverseNextEvent21,adverseNextEvent22,taskReward]
    <;> norm_num
  have hp : rawVisits adverseNextS23Before [] = 22 := by decide
  have hn : rawVisits adverseNextS23Before ([]++[.query 2]) = 3 := by decide
  have hz : (controlPenalty savedCref uniformQuoteError unitRoleUnused .next) adverseNextS23Before [] (.query 2) = (nextNormalPenalty adverseNextS23Before) := by
    simpa only [adverseNextS23Before,nextNormalPenalty] using AgentUCTNextExact.adverse_next_normal_root_quotes_exact 22 (by omega) 2 (by decide)
  unfold indexScore
  rw [hs,hp,hn,hz]
  simp only [BackupStat.mean]
  norm_num

theorem adverseNextS23D0I3 : indexScore (7/5) (controlPenalty savedCref uniformQuoteError unitRoleUnused .next) adverseNextS23Before [] (.query 3) = treeIndex ((0/1)/3) (7/5) (nextNormalPenalty adverseNextS23Before) 22 3 := by
  have hs : replayBackup adverseNextS23Before emptyStatistics ([]++[.query 3]) = ⟨3,(0/1)⟩ := by
    rw [replayBackup_empty_closed_form]
    simp +decide [backedEvents,adverseNextS23Before,adverseNextProposal,adverseNextEvent1,adverseNextEvent2,adverseNextEvent3,adverseNextEvent4,adverseNextEvent5,adverseNextEvent6,adverseNextEvent7,adverseNextEvent8,adverseNextEvent9,adverseNextEvent10,adverseNextEvent11,adverseNextEvent12,adverseNextEvent13,adverseNextEvent14,adverseNextEvent15,adverseNextEvent16,adverseNextEvent17,adverseNextEvent18,adverseNextEvent19,adverseNextEvent20,adverseNextEvent21,adverseNextEvent22,taskReward]
    <;> norm_num
  have hp : rawVisits adverseNextS23Before [] = 22 := by decide
  have hn : rawVisits adverseNextS23Before ([]++[.query 3]) = 3 := by decide
  have hz : (controlPenalty savedCref uniformQuoteError unitRoleUnused .next) adverseNextS23Before [] (.query 3) = (nextNormalPenalty adverseNextS23Before) := by
    simpa only [adverseNextS23Before,nextNormalPenalty] using AgentUCTNextExact.adverse_next_normal_root_quotes_exact 22 (by omega) 3 (by decide)
  unfold indexScore
  rw [hs,hp,hn,hz]
  simp only [BackupStat.mean]
  norm_num

theorem adverseNextS23D0I4 : indexScore (7/5) (controlPenalty savedCref uniformQuoteError unitRoleUnused .next) adverseNextS23Before [] (.query 4) = treeIndex ((0/1)/2) (7/5) (nextNormalPenalty adverseNextS23Before) 22 2 := by
  have hs : replayBackup adverseNextS23Before emptyStatistics ([]++[.query 4]) = ⟨2,(0/1)⟩ := by
    rw [replayBackup_empty_closed_form]
    simp +decide [backedEvents,adverseNextS23Before,adverseNextProposal,adverseNextEvent1,adverseNextEvent2,adverseNextEvent3,adverseNextEvent4,adverseNextEvent5,adverseNextEvent6,adverseNextEvent7,adverseNextEvent8,adverseNextEvent9,adverseNextEvent10,adverseNextEvent11,adverseNextEvent12,adverseNextEvent13,adverseNextEvent14,adverseNextEvent15,adverseNextEvent16,adverseNextEvent17,adverseNextEvent18,adverseNextEvent19,adverseNextEvent20,adverseNextEvent21,adverseNextEvent22,taskReward]
    <;> norm_num
  have hp : rawVisits adverseNextS23Before [] = 22 := by decide
  have hn : rawVisits adverseNextS23Before ([]++[.query 4]) = 2 := by decide
  have hz : (controlPenalty savedCref uniformQuoteError unitRoleUnused .next) adverseNextS23Before [] (.query 4) = (nextNormalPenalty adverseNextS23Before) := by
    simpa only [adverseNextS23Before,nextNormalPenalty] using AgentUCTNextExact.adverse_next_normal_root_quotes_exact 22 (by omega) 4 (by decide)
  unfold indexScore
  rw [hs,hp,hn,hz]
  simp only [BackupStat.mean]
  norm_num

theorem adverseNextS23D0I5 : indexScore (7/5) (controlPenalty savedCref uniformQuoteError unitRoleUnused .next) adverseNextS23Before [] (.query 5) = treeIndex ((13/10)/4) (7/5) (nextNormalPenalty adverseNextS23Before) 22 4 := by
  have hs : replayBackup adverseNextS23Before emptyStatistics ([]++[.query 5]) = ⟨4,(13/10)⟩ := by
    rw [replayBackup_empty_closed_form]
    simp +decide [backedEvents,adverseNextS23Before,adverseNextProposal,adverseNextEvent1,adverseNextEvent2,adverseNextEvent3,adverseNextEvent4,adverseNextEvent5,adverseNextEvent6,adverseNextEvent7,adverseNextEvent8,adverseNextEvent9,adverseNextEvent10,adverseNextEvent11,adverseNextEvent12,adverseNextEvent13,adverseNextEvent14,adverseNextEvent15,adverseNextEvent16,adverseNextEvent17,adverseNextEvent18,adverseNextEvent19,adverseNextEvent20,adverseNextEvent21,adverseNextEvent22,taskReward]
    <;> norm_num
  have hp : rawVisits adverseNextS23Before [] = 22 := by decide
  have hn : rawVisits adverseNextS23Before ([]++[.query 5]) = 4 := by decide
  have hz : (controlPenalty savedCref uniformQuoteError unitRoleUnused .next) adverseNextS23Before [] (.query 5) = (nextNormalPenalty adverseNextS23Before) := by
    simpa only [adverseNextS23Before,nextNormalPenalty] using AgentUCTNextExact.adverse_next_normal_root_quotes_exact 22 (by omega) 5 (by decide)
  unfold indexScore
  rw [hs,hp,hn,hz]
  simp only [BackupStat.mean]
  norm_num

theorem adverseNextS23D0I6 : indexScore (7/5) (controlPenalty savedCref uniformQuoteError unitRoleUnused .next) adverseNextS23Before [] (.query 6) = treeIndex ((0/1)/2) (7/5) (nextNormalPenalty adverseNextS23Before) 22 2 := by
  have hs : replayBackup adverseNextS23Before emptyStatistics ([]++[.query 6]) = ⟨2,(0/1)⟩ := by
    rw [replayBackup_empty_closed_form]
    simp +decide [backedEvents,adverseNextS23Before,adverseNextProposal,adverseNextEvent1,adverseNextEvent2,adverseNextEvent3,adverseNextEvent4,adverseNextEvent5,adverseNextEvent6,adverseNextEvent7,adverseNextEvent8,adverseNextEvent9,adverseNextEvent10,adverseNextEvent11,adverseNextEvent12,adverseNextEvent13,adverseNextEvent14,adverseNextEvent15,adverseNextEvent16,adverseNextEvent17,adverseNextEvent18,adverseNextEvent19,adverseNextEvent20,adverseNextEvent21,adverseNextEvent22,taskReward]
    <;> norm_num
  have hp : rawVisits adverseNextS23Before [] = 22 := by decide
  have hn : rawVisits adverseNextS23Before ([]++[.query 6]) = 2 := by decide
  have hz : (controlPenalty savedCref uniformQuoteError unitRoleUnused .next) adverseNextS23Before [] (.query 6) = (nextNormalPenalty adverseNextS23Before) := by
    simpa only [adverseNextS23Before,nextNormalPenalty] using AgentUCTNextExact.adverse_next_normal_root_quotes_exact 22 (by omega) 6 (by decide)
  unfold indexScore
  rw [hs,hp,hn,hz]
  simp only [BackupStat.mean]
  norm_num

theorem adverseNextS23D0I7 : indexScore (7/5) (controlPenalty savedCref uniformQuoteError unitRoleUnused .next) adverseNextS23Before [] (.query 7) = treeIndex ((0/1)/2) (7/5) (nextNormalPenalty adverseNextS23Before) 22 2 := by
  have hs : replayBackup adverseNextS23Before emptyStatistics ([]++[.query 7]) = ⟨2,(0/1)⟩ := by
    rw [replayBackup_empty_closed_form]
    simp +decide [backedEvents,adverseNextS23Before,adverseNextProposal,adverseNextEvent1,adverseNextEvent2,adverseNextEvent3,adverseNextEvent4,adverseNextEvent5,adverseNextEvent6,adverseNextEvent7,adverseNextEvent8,adverseNextEvent9,adverseNextEvent10,adverseNextEvent11,adverseNextEvent12,adverseNextEvent13,adverseNextEvent14,adverseNextEvent15,adverseNextEvent16,adverseNextEvent17,adverseNextEvent18,adverseNextEvent19,adverseNextEvent20,adverseNextEvent21,adverseNextEvent22,taskReward]
    <;> norm_num
  have hp : rawVisits adverseNextS23Before [] = 22 := by decide
  have hn : rawVisits adverseNextS23Before ([]++[.query 7]) = 2 := by decide
  have hz : (controlPenalty savedCref uniformQuoteError unitRoleUnused .next) adverseNextS23Before [] (.query 7) = (nextNormalPenalty adverseNextS23Before) := by
    simpa only [adverseNextS23Before,nextNormalPenalty] using AgentUCTNextExact.adverse_next_normal_root_quotes_exact 22 (by omega) 7 (by decide)
  unfold indexScore
  rw [hs,hp,hn,hz]
  simp only [BackupStat.mean]
  norm_num

theorem adverseNextS23D0Cmp0 : indexScore (7/5) (controlPenalty savedCref uniformQuoteError unitRoleUnused .next) adverseNextS23Before [] (.query 0) < indexScore (7/5) (controlPenalty savedCref uniformQuoteError unitRoleUnused .next) adverseNextS23Before [] (.query 4) := by
  rw [adverseNextS23D0I0,adverseNextS23D0I4]
  have hk := adverse_next_penalty_interval 22 (by omega)
  change nextNormalPenaltyLower ≤ nextNormalPenalty adverseNextS23Before ∧ nextNormalPenalty adverseNextS23Before ≤ nextNormalPenaltyUpper at hk
  have hm : ((0/1)/3)+(71563317/50000000)-(nextNormalPenalty adverseNextS23Before) < ((0/1)/2)+(8764679/5000000)-(nextNormalPenalty adverseNextS23Before) := by
    have h : (((0/1)/3)+(71563317/50000000) : ℝ) < ((0/1)/2)+(8764679/5000000) := by norm_num
    linarith
  have h := index_strict_order_from_intervals ((0/1)/2) ((0/1)/3) (nextNormalPenalty adverseNextS23Before) (nextNormalPenalty adverseNextS23Before) (8764679/5000000) (71563317/50000000)
    (treeBonus (7/5) 22 2) (treeBonus (7/5) 22 3)
    (trajectory_bonus_22_2).1 (trajectory_bonus_22_3).2 hm
  simpa only [treeIndex] using h

theorem adverseNextS23D0Cmp1 : indexScore (7/5) (controlPenalty savedCref uniformQuoteError unitRoleUnused .next) adverseNextS23Before [] (.query 1) < indexScore (7/5) (controlPenalty savedCref uniformQuoteError unitRoleUnused .next) adverseNextS23Before [] (.query 4) := by
  rw [adverseNextS23D0I1,adverseNextS23D0I4]
  have hk := adverse_next_penalty_interval 22 (by omega)
  change nextNormalPenaltyLower ≤ nextNormalPenalty adverseNextS23Before ∧ nextNormalPenalty adverseNextS23Before ≤ nextNormalPenaltyUpper at hk
  have hm : ((0/1)/3)+(71563317/50000000)-0 < ((0/1)/2)+(8764679/5000000)-(nextNormalPenalty adverseNextS23Before) := by
    have h : ((0/1)/3)+(71563317/50000000) < ((0/1)/2)+(8764679/5000000)-nextNormalPenaltyUpper := by norm_num [nextNormalPenaltyUpper,savedCref,uniformQuoteError]
    linarith [hk.2]
  have h := index_strict_order_from_intervals ((0/1)/2) ((0/1)/3) (nextNormalPenalty adverseNextS23Before) 0 (8764679/5000000) (71563317/50000000)
    (treeBonus (7/5) 22 2) (treeBonus (7/5) 22 3)
    (trajectory_bonus_22_2).1 (trajectory_bonus_22_3).2 hm
  simpa only [treeIndex] using h

theorem adverseNextS23D0Cmp2 : indexScore (7/5) (controlPenalty savedCref uniformQuoteError unitRoleUnused .next) adverseNextS23Before [] (.query 2) < indexScore (7/5) (controlPenalty savedCref uniformQuoteError unitRoleUnused .next) adverseNextS23Before [] (.query 4) := by
  rw [adverseNextS23D0I2,adverseNextS23D0I4]
  have hk := adverse_next_penalty_interval 22 (by omega)
  change nextNormalPenaltyLower ≤ nextNormalPenalty adverseNextS23Before ∧ nextNormalPenalty adverseNextS23Before ≤ nextNormalPenaltyUpper at hk
  have hm : ((0/1)/3)+(71563317/50000000)-(nextNormalPenalty adverseNextS23Before) < ((0/1)/2)+(8764679/5000000)-(nextNormalPenalty adverseNextS23Before) := by
    have h : (((0/1)/3)+(71563317/50000000) : ℝ) < ((0/1)/2)+(8764679/5000000) := by norm_num
    linarith
  have h := index_strict_order_from_intervals ((0/1)/2) ((0/1)/3) (nextNormalPenalty adverseNextS23Before) (nextNormalPenalty adverseNextS23Before) (8764679/5000000) (71563317/50000000)
    (treeBonus (7/5) 22 2) (treeBonus (7/5) 22 3)
    (trajectory_bonus_22_2).1 (trajectory_bonus_22_3).2 hm
  simpa only [treeIndex] using h

theorem adverseNextS23D0Cmp3 : indexScore (7/5) (controlPenalty savedCref uniformQuoteError unitRoleUnused .next) adverseNextS23Before [] (.query 3) < indexScore (7/5) (controlPenalty savedCref uniformQuoteError unitRoleUnused .next) adverseNextS23Before [] (.query 4) := by
  rw [adverseNextS23D0I3,adverseNextS23D0I4]
  have hk := adverse_next_penalty_interval 22 (by omega)
  change nextNormalPenaltyLower ≤ nextNormalPenalty adverseNextS23Before ∧ nextNormalPenalty adverseNextS23Before ≤ nextNormalPenaltyUpper at hk
  have hm : ((0/1)/3)+(71563317/50000000)-(nextNormalPenalty adverseNextS23Before) < ((0/1)/2)+(8764679/5000000)-(nextNormalPenalty adverseNextS23Before) := by
    have h : (((0/1)/3)+(71563317/50000000) : ℝ) < ((0/1)/2)+(8764679/5000000) := by norm_num
    linarith
  have h := index_strict_order_from_intervals ((0/1)/2) ((0/1)/3) (nextNormalPenalty adverseNextS23Before) (nextNormalPenalty adverseNextS23Before) (8764679/5000000) (71563317/50000000)
    (treeBonus (7/5) 22 2) (treeBonus (7/5) 22 3)
    (trajectory_bonus_22_2).1 (trajectory_bonus_22_3).2 hm
  simpa only [treeIndex] using h

theorem adverseNextS23D0Cmp5 : indexScore (7/5) (controlPenalty savedCref uniformQuoteError unitRoleUnused .next) adverseNextS23Before [] (.query 5) ≤ indexScore (7/5) (controlPenalty savedCref uniformQuoteError unitRoleUnused .next) adverseNextS23Before [] (.query 4) := by
  rw [adverseNextS23D0I5,adverseNextS23D0I4]
  have hk := adverse_next_penalty_interval 22 (by omega)
  change nextNormalPenaltyLower ≤ nextNormalPenalty adverseNextS23Before ∧ nextNormalPenalty adverseNextS23Before ≤ nextNormalPenaltyUpper at hk
  have hm : ((13/10)/4)+(1936739/1562500)-(nextNormalPenalty adverseNextS23Before) < ((0/1)/2)+(8764679/5000000)-(nextNormalPenalty adverseNextS23Before) := by
    have h : (((13/10)/4)+(1936739/1562500) : ℝ) < ((0/1)/2)+(8764679/5000000) := by norm_num
    linarith
  have h := index_weak_order_from_intervals ((0/1)/2) ((13/10)/4) (nextNormalPenalty adverseNextS23Before) (nextNormalPenalty adverseNextS23Before) (8764679/5000000) (1936739/1562500)
    (treeBonus (7/5) 22 2) (treeBonus (7/5) 22 4)
    (trajectory_bonus_22_2).1 (trajectory_bonus_22_4).2 hm.le
  simpa only [treeIndex] using h

theorem adverseNextS23D0Cmp6 : indexScore (7/5) (controlPenalty savedCref uniformQuoteError unitRoleUnused .next) adverseNextS23Before [] (.query 6) ≤ indexScore (7/5) (controlPenalty savedCref uniformQuoteError unitRoleUnused .next) adverseNextS23Before [] (.query 4) := by
  rw [adverseNextS23D0I6,adverseNextS23D0I4]

theorem adverseNextS23D0Cmp7 : indexScore (7/5) (controlPenalty savedCref uniformQuoteError unitRoleUnused .next) adverseNextS23Before [] (.query 7) ≤ indexScore (7/5) (controlPenalty savedCref uniformQuoteError unitRoleUnused .next) adverseNextS23Before [] (.query 4) := by
  rw [adverseNextS23D0I7,adverseNextS23D0I4]

theorem adverseNextS23Choice0 : nativeFirstChoice (indexScore (7/5) (controlPenalty savedCref uniformQuoteError unitRoleUnused .next) adverseNextS23Before []) adverseNextS23Before [] = .query 4 := by
  apply visited_choice_from_ordered_certificate _ _ [] [.query 0,.query 1,.query 2,.query 3] [.query 5,.query 6,.query 7] (.query 4) (by decide)
  · intro a ha
    have ho : orderedLegalAvailable [] = [.query 0,.query 1,.query 2,.query 3,.query 4,.query 5,.query 6,.query 7] := by decide
    rw [ho] at ha
    simp only [List.mem_cons,List.not_mem_nil,or_false] at ha
    rcases ha with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> decide
  · intro a ha
    simp only [List.mem_cons,List.not_mem_nil,or_false] at ha
    rcases ha with rfl | rfl | rfl | rfl
    · exact adverseNextS23D0Cmp0
    · exact adverseNextS23D0Cmp1
    · exact adverseNextS23D0Cmp2
    · exact adverseNextS23D0Cmp3
  · intro a ha
    simp only [List.mem_cons,List.not_mem_nil,or_false] at ha
    rcases ha with rfl | rfl | rfl
    · exact adverseNextS23D0Cmp5
    · exact adverseNextS23D0Cmp6
    · exact adverseNextS23D0Cmp7

theorem adverseNextS23ActualEvent : nativeEvent budgetTape (7/5) (controlPenalty savedCref uniformQuoteError unitRoleUnused .next)
    (taskReward true (2/5) (1/2)) adverseNextS23Before = adverseNextEvent23 := by
  have hs0 := native_select_existing_step budgetTape (7/5) (controlPenalty savedCref uniformQuoteError unitRoleUnused .next) adverseNextS23Before 8 [] (.query 4)
    (by decide) (by decide) adverseNextS23Choice0
  have hnew := native_select_new_step budgetTape (7/5) (controlPenalty savedCref uniformQuoteError unitRoleUnused .next) adverseNextS23Before 7 [.query 4]
    [.normalRetriever 4,.normalRetriever 6,.normalRetriever 7,.normalRetriever 8,.normalRetriever 5,.normalRetriever 1,.normalRetriever 2,.normalRetriever 3,.normalRetriever 12,.normalRetriever 14,.normalRetriever 13,.normalRetriever 21,.normalRetriever 23,.normalRetriever 22,.normalRetriever 9,.normalRetriever 11,.normalRetriever 10,.normalRetriever 15,.normalRetriever 17,.normalRetriever 16,.normalRetriever 18,.normalRetriever 20,.normalRetriever 19,.normalRetriever 24,.normalRetriever 25,.normalRetriever 26,.normalRetriever 27,.normalRetriever 28,.normalRetriever 29] (.normalRetriever 4) (by decide) (by decide) (by decide) (by decide)
  have hs : nativeSelect budgetTape (7/5) (controlPenalty savedCref uniformQuoteError unitRoleUnused .next) adverseNextS23Before 9 [] = [.query 4,.normalRetriever 4] := by
    rw [hs0]
    change nativeSelect budgetTape (7/5) (controlPenalty savedCref uniformQuoteError unitRoleUnused .next) adverseNextS23Before 8 [.query 4] = _
    rw [hnew] <;> rfl
  have hr : repairedRollout budgetTape adverseNextS23Before 9 [.query 4,.normalRetriever 4] = [.query 4,.normalRetriever 4,.selection 0,.width 0,.stop,.reranker 0,.topm 0,.context 0,.answer 0] := by decide
  simp only [nativeEvent,hs,hr]
  rfl

def adverseNextS24Before := adverseNextProposal.take 23

theorem adverseNextS24D0I0 : indexScore (7/5) (controlPenalty savedCref uniformQuoteError unitRoleUnused .next) adverseNextS24Before [] (.query 0) = treeIndex ((0/1)/3) (7/5) (nextNormalPenalty adverseNextS24Before) 23 3 := by
  have hs : replayBackup adverseNextS24Before emptyStatistics ([]++[.query 0]) = ⟨3,(0/1)⟩ := by
    rw [replayBackup_empty_closed_form]
    simp +decide [backedEvents,adverseNextS24Before,adverseNextProposal,adverseNextEvent1,adverseNextEvent2,adverseNextEvent3,adverseNextEvent4,adverseNextEvent5,adverseNextEvent6,adverseNextEvent7,adverseNextEvent8,adverseNextEvent9,adverseNextEvent10,adverseNextEvent11,adverseNextEvent12,adverseNextEvent13,adverseNextEvent14,adverseNextEvent15,adverseNextEvent16,adverseNextEvent17,adverseNextEvent18,adverseNextEvent19,adverseNextEvent20,adverseNextEvent21,adverseNextEvent22,adverseNextEvent23,taskReward]
    <;> norm_num
  have hp : rawVisits adverseNextS24Before [] = 23 := by decide
  have hn : rawVisits adverseNextS24Before ([]++[.query 0]) = 3 := by decide
  have hz : (controlPenalty savedCref uniformQuoteError unitRoleUnused .next) adverseNextS24Before [] (.query 0) = (nextNormalPenalty adverseNextS24Before) := by
    simpa only [adverseNextS24Before,nextNormalPenalty] using AgentUCTNextExact.adverse_next_normal_root_quotes_exact 23 (by omega) 0 (by decide)
  unfold indexScore
  rw [hs,hp,hn,hz]
  simp only [BackupStat.mean]
  norm_num

theorem adverseNextS24D0I1 : indexScore (7/5) (controlPenalty savedCref uniformQuoteError unitRoleUnused .next) adverseNextS24Before [] (.query 1) = treeIndex ((0/1)/3) (7/5) 0 23 3 := by
  have hs : replayBackup adverseNextS24Before emptyStatistics ([]++[.query 1]) = ⟨3,(0/1)⟩ := by
    rw [replayBackup_empty_closed_form]
    simp +decide [backedEvents,adverseNextS24Before,adverseNextProposal,adverseNextEvent1,adverseNextEvent2,adverseNextEvent3,adverseNextEvent4,adverseNextEvent5,adverseNextEvent6,adverseNextEvent7,adverseNextEvent8,adverseNextEvent9,adverseNextEvent10,adverseNextEvent11,adverseNextEvent12,adverseNextEvent13,adverseNextEvent14,adverseNextEvent15,adverseNextEvent16,adverseNextEvent17,adverseNextEvent18,adverseNextEvent19,adverseNextEvent20,adverseNextEvent21,adverseNextEvent22,adverseNextEvent23,taskReward]
    <;> norm_num
  have hp : rawVisits adverseNextS24Before [] = 23 := by decide
  have hn : rawVisits adverseNextS24Before ([]++[.query 1]) = 3 := by decide
  have hz : (controlPenalty savedCref uniformQuoteError unitRoleUnused .next) adverseNextS24Before [] (.query 1) = 0 := by
    apply control_penalty_empty_suffix
    exact AgentUCTNextExact.adverse_next_hyde_root_suffix_empty 23 (by omega)
  unfold indexScore
  rw [hs,hp,hn,hz]
  simp only [BackupStat.mean]
  norm_num

theorem adverseNextS24D0I2 : indexScore (7/5) (controlPenalty savedCref uniformQuoteError unitRoleUnused .next) adverseNextS24Before [] (.query 2) = treeIndex ((0/1)/3) (7/5) (nextNormalPenalty adverseNextS24Before) 23 3 := by
  have hs : replayBackup adverseNextS24Before emptyStatistics ([]++[.query 2]) = ⟨3,(0/1)⟩ := by
    rw [replayBackup_empty_closed_form]
    simp +decide [backedEvents,adverseNextS24Before,adverseNextProposal,adverseNextEvent1,adverseNextEvent2,adverseNextEvent3,adverseNextEvent4,adverseNextEvent5,adverseNextEvent6,adverseNextEvent7,adverseNextEvent8,adverseNextEvent9,adverseNextEvent10,adverseNextEvent11,adverseNextEvent12,adverseNextEvent13,adverseNextEvent14,adverseNextEvent15,adverseNextEvent16,adverseNextEvent17,adverseNextEvent18,adverseNextEvent19,adverseNextEvent20,adverseNextEvent21,adverseNextEvent22,adverseNextEvent23,taskReward]
    <;> norm_num
  have hp : rawVisits adverseNextS24Before [] = 23 := by decide
  have hn : rawVisits adverseNextS24Before ([]++[.query 2]) = 3 := by decide
  have hz : (controlPenalty savedCref uniformQuoteError unitRoleUnused .next) adverseNextS24Before [] (.query 2) = (nextNormalPenalty adverseNextS24Before) := by
    simpa only [adverseNextS24Before,nextNormalPenalty] using AgentUCTNextExact.adverse_next_normal_root_quotes_exact 23 (by omega) 2 (by decide)
  unfold indexScore
  rw [hs,hp,hn,hz]
  simp only [BackupStat.mean]
  norm_num

theorem adverseNextS24D0I3 : indexScore (7/5) (controlPenalty savedCref uniformQuoteError unitRoleUnused .next) adverseNextS24Before [] (.query 3) = treeIndex ((0/1)/3) (7/5) (nextNormalPenalty adverseNextS24Before) 23 3 := by
  have hs : replayBackup adverseNextS24Before emptyStatistics ([]++[.query 3]) = ⟨3,(0/1)⟩ := by
    rw [replayBackup_empty_closed_form]
    simp +decide [backedEvents,adverseNextS24Before,adverseNextProposal,adverseNextEvent1,adverseNextEvent2,adverseNextEvent3,adverseNextEvent4,adverseNextEvent5,adverseNextEvent6,adverseNextEvent7,adverseNextEvent8,adverseNextEvent9,adverseNextEvent10,adverseNextEvent11,adverseNextEvent12,adverseNextEvent13,adverseNextEvent14,adverseNextEvent15,adverseNextEvent16,adverseNextEvent17,adverseNextEvent18,adverseNextEvent19,adverseNextEvent20,adverseNextEvent21,adverseNextEvent22,adverseNextEvent23,taskReward]
    <;> norm_num
  have hp : rawVisits adverseNextS24Before [] = 23 := by decide
  have hn : rawVisits adverseNextS24Before ([]++[.query 3]) = 3 := by decide
  have hz : (controlPenalty savedCref uniformQuoteError unitRoleUnused .next) adverseNextS24Before [] (.query 3) = (nextNormalPenalty adverseNextS24Before) := by
    simpa only [adverseNextS24Before,nextNormalPenalty] using AgentUCTNextExact.adverse_next_normal_root_quotes_exact 23 (by omega) 3 (by decide)
  unfold indexScore
  rw [hs,hp,hn,hz]
  simp only [BackupStat.mean]
  norm_num

theorem adverseNextS24D0I4 : indexScore (7/5) (controlPenalty savedCref uniformQuoteError unitRoleUnused .next) adverseNextS24Before [] (.query 4) = treeIndex ((0/1)/3) (7/5) (nextNormalPenalty adverseNextS24Before) 23 3 := by
  have hs : replayBackup adverseNextS24Before emptyStatistics ([]++[.query 4]) = ⟨3,(0/1)⟩ := by
    rw [replayBackup_empty_closed_form]
    simp +decide [backedEvents,adverseNextS24Before,adverseNextProposal,adverseNextEvent1,adverseNextEvent2,adverseNextEvent3,adverseNextEvent4,adverseNextEvent5,adverseNextEvent6,adverseNextEvent7,adverseNextEvent8,adverseNextEvent9,adverseNextEvent10,adverseNextEvent11,adverseNextEvent12,adverseNextEvent13,adverseNextEvent14,adverseNextEvent15,adverseNextEvent16,adverseNextEvent17,adverseNextEvent18,adverseNextEvent19,adverseNextEvent20,adverseNextEvent21,adverseNextEvent22,adverseNextEvent23,taskReward]
    <;> norm_num
  have hp : rawVisits adverseNextS24Before [] = 23 := by decide
  have hn : rawVisits adverseNextS24Before ([]++[.query 4]) = 3 := by decide
  have hz : (controlPenalty savedCref uniformQuoteError unitRoleUnused .next) adverseNextS24Before [] (.query 4) = (nextNormalPenalty adverseNextS24Before) := by
    simpa only [adverseNextS24Before,nextNormalPenalty] using AgentUCTNextExact.adverse_next_normal_root_quotes_exact 23 (by omega) 4 (by decide)
  unfold indexScore
  rw [hs,hp,hn,hz]
  simp only [BackupStat.mean]
  norm_num

theorem adverseNextS24D0I5 : indexScore (7/5) (controlPenalty savedCref uniformQuoteError unitRoleUnused .next) adverseNextS24Before [] (.query 5) = treeIndex ((13/10)/4) (7/5) (nextNormalPenalty adverseNextS24Before) 23 4 := by
  have hs : replayBackup adverseNextS24Before emptyStatistics ([]++[.query 5]) = ⟨4,(13/10)⟩ := by
    rw [replayBackup_empty_closed_form]
    simp +decide [backedEvents,adverseNextS24Before,adverseNextProposal,adverseNextEvent1,adverseNextEvent2,adverseNextEvent3,adverseNextEvent4,adverseNextEvent5,adverseNextEvent6,adverseNextEvent7,adverseNextEvent8,adverseNextEvent9,adverseNextEvent10,adverseNextEvent11,adverseNextEvent12,adverseNextEvent13,adverseNextEvent14,adverseNextEvent15,adverseNextEvent16,adverseNextEvent17,adverseNextEvent18,adverseNextEvent19,adverseNextEvent20,adverseNextEvent21,adverseNextEvent22,adverseNextEvent23,taskReward]
    <;> norm_num
  have hp : rawVisits adverseNextS24Before [] = 23 := by decide
  have hn : rawVisits adverseNextS24Before ([]++[.query 5]) = 4 := by decide
  have hz : (controlPenalty savedCref uniformQuoteError unitRoleUnused .next) adverseNextS24Before [] (.query 5) = (nextNormalPenalty adverseNextS24Before) := by
    simpa only [adverseNextS24Before,nextNormalPenalty] using AgentUCTNextExact.adverse_next_normal_root_quotes_exact 23 (by omega) 5 (by decide)
  unfold indexScore
  rw [hs,hp,hn,hz]
  simp only [BackupStat.mean]
  norm_num

theorem adverseNextS24D0I6 : indexScore (7/5) (controlPenalty savedCref uniformQuoteError unitRoleUnused .next) adverseNextS24Before [] (.query 6) = treeIndex ((0/1)/2) (7/5) (nextNormalPenalty adverseNextS24Before) 23 2 := by
  have hs : replayBackup adverseNextS24Before emptyStatistics ([]++[.query 6]) = ⟨2,(0/1)⟩ := by
    rw [replayBackup_empty_closed_form]
    simp +decide [backedEvents,adverseNextS24Before,adverseNextProposal,adverseNextEvent1,adverseNextEvent2,adverseNextEvent3,adverseNextEvent4,adverseNextEvent5,adverseNextEvent6,adverseNextEvent7,adverseNextEvent8,adverseNextEvent9,adverseNextEvent10,adverseNextEvent11,adverseNextEvent12,adverseNextEvent13,adverseNextEvent14,adverseNextEvent15,adverseNextEvent16,adverseNextEvent17,adverseNextEvent18,adverseNextEvent19,adverseNextEvent20,adverseNextEvent21,adverseNextEvent22,adverseNextEvent23,taskReward]
    <;> norm_num
  have hp : rawVisits adverseNextS24Before [] = 23 := by decide
  have hn : rawVisits adverseNextS24Before ([]++[.query 6]) = 2 := by decide
  have hz : (controlPenalty savedCref uniformQuoteError unitRoleUnused .next) adverseNextS24Before [] (.query 6) = (nextNormalPenalty adverseNextS24Before) := by
    simpa only [adverseNextS24Before,nextNormalPenalty] using AgentUCTNextExact.adverse_next_normal_root_quotes_exact 23 (by omega) 6 (by decide)
  unfold indexScore
  rw [hs,hp,hn,hz]
  simp only [BackupStat.mean]
  norm_num

theorem adverseNextS24D0I7 : indexScore (7/5) (controlPenalty savedCref uniformQuoteError unitRoleUnused .next) adverseNextS24Before [] (.query 7) = treeIndex ((0/1)/2) (7/5) (nextNormalPenalty adverseNextS24Before) 23 2 := by
  have hs : replayBackup adverseNextS24Before emptyStatistics ([]++[.query 7]) = ⟨2,(0/1)⟩ := by
    rw [replayBackup_empty_closed_form]
    simp +decide [backedEvents,adverseNextS24Before,adverseNextProposal,adverseNextEvent1,adverseNextEvent2,adverseNextEvent3,adverseNextEvent4,adverseNextEvent5,adverseNextEvent6,adverseNextEvent7,adverseNextEvent8,adverseNextEvent9,adverseNextEvent10,adverseNextEvent11,adverseNextEvent12,adverseNextEvent13,adverseNextEvent14,adverseNextEvent15,adverseNextEvent16,adverseNextEvent17,adverseNextEvent18,adverseNextEvent19,adverseNextEvent20,adverseNextEvent21,adverseNextEvent22,adverseNextEvent23,taskReward]
    <;> norm_num
  have hp : rawVisits adverseNextS24Before [] = 23 := by decide
  have hn : rawVisits adverseNextS24Before ([]++[.query 7]) = 2 := by decide
  have hz : (controlPenalty savedCref uniformQuoteError unitRoleUnused .next) adverseNextS24Before [] (.query 7) = (nextNormalPenalty adverseNextS24Before) := by
    simpa only [adverseNextS24Before,nextNormalPenalty] using AgentUCTNextExact.adverse_next_normal_root_quotes_exact 23 (by omega) 7 (by decide)
  unfold indexScore
  rw [hs,hp,hn,hz]
  simp only [BackupStat.mean]
  norm_num

theorem adverseNextS24D0Cmp0 : indexScore (7/5) (controlPenalty savedCref uniformQuoteError unitRoleUnused .next) adverseNextS24Before [] (.query 0) < indexScore (7/5) (controlPenalty savedCref uniformQuoteError unitRoleUnused .next) adverseNextS24Before [] (.query 6) := by
  rw [adverseNextS24D0I0,adverseNextS24D0I6]
  have hk := adverse_next_penalty_interval 23 (by omega)
  change nextNormalPenaltyLower ≤ nextNormalPenalty adverseNextS24Before ∧ nextNormalPenalty adverseNextS24Before ≤ nextNormalPenaltyUpper at hk
  have hm : ((0/1)/3)+(112574/78125)-(nextNormalPenalty adverseNextS24Before) < ((0/1)/2)+(88239627/50000000)-(nextNormalPenalty adverseNextS24Before) := by
    have h : (((0/1)/3)+(112574/78125) : ℝ) < ((0/1)/2)+(88239627/50000000) := by norm_num
    linarith
  have h := index_strict_order_from_intervals ((0/1)/2) ((0/1)/3) (nextNormalPenalty adverseNextS24Before) (nextNormalPenalty adverseNextS24Before) (88239627/50000000) (112574/78125)
    (treeBonus (7/5) 23 2) (treeBonus (7/5) 23 3)
    (trajectory_bonus_23_2).1 (trajectory_bonus_23_3).2 hm
  simpa only [treeIndex] using h

theorem adverseNextS24D0Cmp1 : indexScore (7/5) (controlPenalty savedCref uniformQuoteError unitRoleUnused .next) adverseNextS24Before [] (.query 1) < indexScore (7/5) (controlPenalty savedCref uniformQuoteError unitRoleUnused .next) adverseNextS24Before [] (.query 6) := by
  rw [adverseNextS24D0I1,adverseNextS24D0I6]
  have hk := adverse_next_penalty_interval 23 (by omega)
  change nextNormalPenaltyLower ≤ nextNormalPenalty adverseNextS24Before ∧ nextNormalPenalty adverseNextS24Before ≤ nextNormalPenaltyUpper at hk
  have hm : ((0/1)/3)+(112574/78125)-0 < ((0/1)/2)+(88239627/50000000)-(nextNormalPenalty adverseNextS24Before) := by
    have h : ((0/1)/3)+(112574/78125) < ((0/1)/2)+(88239627/50000000)-nextNormalPenaltyUpper := by norm_num [nextNormalPenaltyUpper,savedCref,uniformQuoteError]
    linarith [hk.2]
  have h := index_strict_order_from_intervals ((0/1)/2) ((0/1)/3) (nextNormalPenalty adverseNextS24Before) 0 (88239627/50000000) (112574/78125)
    (treeBonus (7/5) 23 2) (treeBonus (7/5) 23 3)
    (trajectory_bonus_23_2).1 (trajectory_bonus_23_3).2 hm
  simpa only [treeIndex] using h

theorem adverseNextS24D0Cmp2 : indexScore (7/5) (controlPenalty savedCref uniformQuoteError unitRoleUnused .next) adverseNextS24Before [] (.query 2) < indexScore (7/5) (controlPenalty savedCref uniformQuoteError unitRoleUnused .next) adverseNextS24Before [] (.query 6) := by
  rw [adverseNextS24D0I2,adverseNextS24D0I6]
  have hk := adverse_next_penalty_interval 23 (by omega)
  change nextNormalPenaltyLower ≤ nextNormalPenalty adverseNextS24Before ∧ nextNormalPenalty adverseNextS24Before ≤ nextNormalPenaltyUpper at hk
  have hm : ((0/1)/3)+(112574/78125)-(nextNormalPenalty adverseNextS24Before) < ((0/1)/2)+(88239627/50000000)-(nextNormalPenalty adverseNextS24Before) := by
    have h : (((0/1)/3)+(112574/78125) : ℝ) < ((0/1)/2)+(88239627/50000000) := by norm_num
    linarith
  have h := index_strict_order_from_intervals ((0/1)/2) ((0/1)/3) (nextNormalPenalty adverseNextS24Before) (nextNormalPenalty adverseNextS24Before) (88239627/50000000) (112574/78125)
    (treeBonus (7/5) 23 2) (treeBonus (7/5) 23 3)
    (trajectory_bonus_23_2).1 (trajectory_bonus_23_3).2 hm
  simpa only [treeIndex] using h

theorem adverseNextS24D0Cmp3 : indexScore (7/5) (controlPenalty savedCref uniformQuoteError unitRoleUnused .next) adverseNextS24Before [] (.query 3) < indexScore (7/5) (controlPenalty savedCref uniformQuoteError unitRoleUnused .next) adverseNextS24Before [] (.query 6) := by
  rw [adverseNextS24D0I3,adverseNextS24D0I6]
  have hk := adverse_next_penalty_interval 23 (by omega)
  change nextNormalPenaltyLower ≤ nextNormalPenalty adverseNextS24Before ∧ nextNormalPenalty adverseNextS24Before ≤ nextNormalPenaltyUpper at hk
  have hm : ((0/1)/3)+(112574/78125)-(nextNormalPenalty adverseNextS24Before) < ((0/1)/2)+(88239627/50000000)-(nextNormalPenalty adverseNextS24Before) := by
    have h : (((0/1)/3)+(112574/78125) : ℝ) < ((0/1)/2)+(88239627/50000000) := by norm_num
    linarith
  have h := index_strict_order_from_intervals ((0/1)/2) ((0/1)/3) (nextNormalPenalty adverseNextS24Before) (nextNormalPenalty adverseNextS24Before) (88239627/50000000) (112574/78125)
    (treeBonus (7/5) 23 2) (treeBonus (7/5) 23 3)
    (trajectory_bonus_23_2).1 (trajectory_bonus_23_3).2 hm
  simpa only [treeIndex] using h

theorem adverseNextS24D0Cmp4 : indexScore (7/5) (controlPenalty savedCref uniformQuoteError unitRoleUnused .next) adverseNextS24Before [] (.query 4) < indexScore (7/5) (controlPenalty savedCref uniformQuoteError unitRoleUnused .next) adverseNextS24Before [] (.query 6) := by
  rw [adverseNextS24D0I4,adverseNextS24D0I6]
  have hk := adverse_next_penalty_interval 23 (by omega)
  change nextNormalPenaltyLower ≤ nextNormalPenalty adverseNextS24Before ∧ nextNormalPenalty adverseNextS24Before ≤ nextNormalPenaltyUpper at hk
  have hm : ((0/1)/3)+(112574/78125)-(nextNormalPenalty adverseNextS24Before) < ((0/1)/2)+(88239627/50000000)-(nextNormalPenalty adverseNextS24Before) := by
    have h : (((0/1)/3)+(112574/78125) : ℝ) < ((0/1)/2)+(88239627/50000000) := by norm_num
    linarith
  have h := index_strict_order_from_intervals ((0/1)/2) ((0/1)/3) (nextNormalPenalty adverseNextS24Before) (nextNormalPenalty adverseNextS24Before) (88239627/50000000) (112574/78125)
    (treeBonus (7/5) 23 2) (treeBonus (7/5) 23 3)
    (trajectory_bonus_23_2).1 (trajectory_bonus_23_3).2 hm
  simpa only [treeIndex] using h

theorem adverseNextS24D0Cmp5 : indexScore (7/5) (controlPenalty savedCref uniformQuoteError unitRoleUnused .next) adverseNextS24Before [] (.query 5) < indexScore (7/5) (controlPenalty savedCref uniformQuoteError unitRoleUnused .next) adverseNextS24Before [] (.query 6) := by
  rw [adverseNextS24D0I5,adverseNextS24D0I6]
  have hk := adverse_next_penalty_interval 23 (by omega)
  change nextNormalPenaltyLower ≤ nextNormalPenalty adverseNextS24Before ∧ nextNormalPenalty adverseNextS24Before ≤ nextNormalPenaltyUpper at hk
  have hm : ((13/10)/4)+(62394843/50000000)-(nextNormalPenalty adverseNextS24Before) < ((0/1)/2)+(88239627/50000000)-(nextNormalPenalty adverseNextS24Before) := by
    have h : (((13/10)/4)+(62394843/50000000) : ℝ) < ((0/1)/2)+(88239627/50000000) := by norm_num
    linarith
  have h := index_strict_order_from_intervals ((0/1)/2) ((13/10)/4) (nextNormalPenalty adverseNextS24Before) (nextNormalPenalty adverseNextS24Before) (88239627/50000000) (62394843/50000000)
    (treeBonus (7/5) 23 2) (treeBonus (7/5) 23 4)
    (trajectory_bonus_23_2).1 (trajectory_bonus_23_4).2 hm
  simpa only [treeIndex] using h

theorem adverseNextS24D0Cmp7 : indexScore (7/5) (controlPenalty savedCref uniformQuoteError unitRoleUnused .next) adverseNextS24Before [] (.query 7) ≤ indexScore (7/5) (controlPenalty savedCref uniformQuoteError unitRoleUnused .next) adverseNextS24Before [] (.query 6) := by
  rw [adverseNextS24D0I7,adverseNextS24D0I6]

theorem adverseNextS24Choice0 : nativeFirstChoice (indexScore (7/5) (controlPenalty savedCref uniformQuoteError unitRoleUnused .next) adverseNextS24Before []) adverseNextS24Before [] = .query 6 := by
  apply visited_choice_from_ordered_certificate _ _ [] [.query 0,.query 1,.query 2,.query 3,.query 4,.query 5] [.query 7] (.query 6) (by decide)
  · intro a ha
    have ho : orderedLegalAvailable [] = [.query 0,.query 1,.query 2,.query 3,.query 4,.query 5,.query 6,.query 7] := by decide
    rw [ho] at ha
    simp only [List.mem_cons,List.not_mem_nil,or_false] at ha
    rcases ha with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> decide
  · intro a ha
    simp only [List.mem_cons,List.not_mem_nil,or_false] at ha
    rcases ha with rfl | rfl | rfl | rfl | rfl | rfl
    · exact adverseNextS24D0Cmp0
    · exact adverseNextS24D0Cmp1
    · exact adverseNextS24D0Cmp2
    · exact adverseNextS24D0Cmp3
    · exact adverseNextS24D0Cmp4
    · exact adverseNextS24D0Cmp5
  · intro a ha
    simp only [List.mem_cons,List.not_mem_nil,or_false] at ha
    rcases ha with rfl
    · exact adverseNextS24D0Cmp7

theorem adverseNextS24ActualEvent : nativeEvent budgetTape (7/5) (controlPenalty savedCref uniformQuoteError unitRoleUnused .next)
    (taskReward true (2/5) (1/2)) adverseNextS24Before = adverseNextEvent24 := by
  have hs0 := native_select_existing_step budgetTape (7/5) (controlPenalty savedCref uniformQuoteError unitRoleUnused .next) adverseNextS24Before 8 [] (.query 6)
    (by decide) (by decide) adverseNextS24Choice0
  have hnew := native_select_new_step budgetTape (7/5) (controlPenalty savedCref uniformQuoteError unitRoleUnused .next) adverseNextS24Before 7 [.query 6]
    [.normalRetriever 4,.normalRetriever 6,.normalRetriever 7,.normalRetriever 8,.normalRetriever 5,.normalRetriever 1,.normalRetriever 2,.normalRetriever 3,.normalRetriever 12,.normalRetriever 14,.normalRetriever 13,.normalRetriever 21,.normalRetriever 23,.normalRetriever 22,.normalRetriever 9,.normalRetriever 11,.normalRetriever 10,.normalRetriever 15,.normalRetriever 17,.normalRetriever 16,.normalRetriever 18,.normalRetriever 20,.normalRetriever 19,.normalRetriever 24,.normalRetriever 25,.normalRetriever 26,.normalRetriever 27,.normalRetriever 28,.normalRetriever 29] (.normalRetriever 4) (by decide) (by decide) (by decide) (by decide)
  have hs : nativeSelect budgetTape (7/5) (controlPenalty savedCref uniformQuoteError unitRoleUnused .next) adverseNextS24Before 9 [] = [.query 6,.normalRetriever 4] := by
    rw [hs0]
    change nativeSelect budgetTape (7/5) (controlPenalty savedCref uniformQuoteError unitRoleUnused .next) adverseNextS24Before 8 [.query 6] = _
    rw [hnew] <;> rfl
  have hr : repairedRollout budgetTape adverseNextS24Before 9 [.query 6,.normalRetriever 4] = [.query 6,.normalRetriever 4,.selection 0,.width 0,.stop,.reranker 0,.topm 0,.context 0,.answer 0] := by decide
  simp only [nativeEvent,hs,hr]
  rfl

def adverseNextS25Before := adverseNextProposal.take 24

theorem adverseNextS25D0I0 : indexScore (7/5) (controlPenalty savedCref uniformQuoteError unitRoleUnused .next) adverseNextS25Before [] (.query 0) = treeIndex ((0/1)/3) (7/5) (nextNormalPenalty adverseNextS25Before) 24 3 := by
  have hs : replayBackup adverseNextS25Before emptyStatistics ([]++[.query 0]) = ⟨3,(0/1)⟩ := by
    rw [replayBackup_empty_closed_form]
    simp +decide [backedEvents,adverseNextS25Before,adverseNextProposal,adverseNextEvent1,adverseNextEvent2,adverseNextEvent3,adverseNextEvent4,adverseNextEvent5,adverseNextEvent6,adverseNextEvent7,adverseNextEvent8,adverseNextEvent9,adverseNextEvent10,adverseNextEvent11,adverseNextEvent12,adverseNextEvent13,adverseNextEvent14,adverseNextEvent15,adverseNextEvent16,adverseNextEvent17,adverseNextEvent18,adverseNextEvent19,adverseNextEvent20,adverseNextEvent21,adverseNextEvent22,adverseNextEvent23,adverseNextEvent24,taskReward]
    <;> norm_num
  have hp : rawVisits adverseNextS25Before [] = 24 := by decide
  have hn : rawVisits adverseNextS25Before ([]++[.query 0]) = 3 := by decide
  have hz : (controlPenalty savedCref uniformQuoteError unitRoleUnused .next) adverseNextS25Before [] (.query 0) = (nextNormalPenalty adverseNextS25Before) := by
    simpa only [adverseNextS25Before,nextNormalPenalty] using AgentUCTNextExact.adverse_next_normal_root_quotes_exact 24 (by omega) 0 (by decide)
  unfold indexScore
  rw [hs,hp,hn,hz]
  simp only [BackupStat.mean]
  norm_num

theorem adverseNextS25D0I1 : indexScore (7/5) (controlPenalty savedCref uniformQuoteError unitRoleUnused .next) adverseNextS25Before [] (.query 1) = treeIndex ((0/1)/3) (7/5) 0 24 3 := by
  have hs : replayBackup adverseNextS25Before emptyStatistics ([]++[.query 1]) = ⟨3,(0/1)⟩ := by
    rw [replayBackup_empty_closed_form]
    simp +decide [backedEvents,adverseNextS25Before,adverseNextProposal,adverseNextEvent1,adverseNextEvent2,adverseNextEvent3,adverseNextEvent4,adverseNextEvent5,adverseNextEvent6,adverseNextEvent7,adverseNextEvent8,adverseNextEvent9,adverseNextEvent10,adverseNextEvent11,adverseNextEvent12,adverseNextEvent13,adverseNextEvent14,adverseNextEvent15,adverseNextEvent16,adverseNextEvent17,adverseNextEvent18,adverseNextEvent19,adverseNextEvent20,adverseNextEvent21,adverseNextEvent22,adverseNextEvent23,adverseNextEvent24,taskReward]
    <;> norm_num
  have hp : rawVisits adverseNextS25Before [] = 24 := by decide
  have hn : rawVisits adverseNextS25Before ([]++[.query 1]) = 3 := by decide
  have hz : (controlPenalty savedCref uniformQuoteError unitRoleUnused .next) adverseNextS25Before [] (.query 1) = 0 := by
    apply control_penalty_empty_suffix
    exact AgentUCTNextExact.adverse_next_hyde_root_suffix_empty 24 (by omega)
  unfold indexScore
  rw [hs,hp,hn,hz]
  simp only [BackupStat.mean]
  norm_num

theorem adverseNextS25D0I2 : indexScore (7/5) (controlPenalty savedCref uniformQuoteError unitRoleUnused .next) adverseNextS25Before [] (.query 2) = treeIndex ((0/1)/3) (7/5) (nextNormalPenalty adverseNextS25Before) 24 3 := by
  have hs : replayBackup adverseNextS25Before emptyStatistics ([]++[.query 2]) = ⟨3,(0/1)⟩ := by
    rw [replayBackup_empty_closed_form]
    simp +decide [backedEvents,adverseNextS25Before,adverseNextProposal,adverseNextEvent1,adverseNextEvent2,adverseNextEvent3,adverseNextEvent4,adverseNextEvent5,adverseNextEvent6,adverseNextEvent7,adverseNextEvent8,adverseNextEvent9,adverseNextEvent10,adverseNextEvent11,adverseNextEvent12,adverseNextEvent13,adverseNextEvent14,adverseNextEvent15,adverseNextEvent16,adverseNextEvent17,adverseNextEvent18,adverseNextEvent19,adverseNextEvent20,adverseNextEvent21,adverseNextEvent22,adverseNextEvent23,adverseNextEvent24,taskReward]
    <;> norm_num
  have hp : rawVisits adverseNextS25Before [] = 24 := by decide
  have hn : rawVisits adverseNextS25Before ([]++[.query 2]) = 3 := by decide
  have hz : (controlPenalty savedCref uniformQuoteError unitRoleUnused .next) adverseNextS25Before [] (.query 2) = (nextNormalPenalty adverseNextS25Before) := by
    simpa only [adverseNextS25Before,nextNormalPenalty] using AgentUCTNextExact.adverse_next_normal_root_quotes_exact 24 (by omega) 2 (by decide)
  unfold indexScore
  rw [hs,hp,hn,hz]
  simp only [BackupStat.mean]
  norm_num

theorem adverseNextS25D0I3 : indexScore (7/5) (controlPenalty savedCref uniformQuoteError unitRoleUnused .next) adverseNextS25Before [] (.query 3) = treeIndex ((0/1)/3) (7/5) (nextNormalPenalty adverseNextS25Before) 24 3 := by
  have hs : replayBackup adverseNextS25Before emptyStatistics ([]++[.query 3]) = ⟨3,(0/1)⟩ := by
    rw [replayBackup_empty_closed_form]
    simp +decide [backedEvents,adverseNextS25Before,adverseNextProposal,adverseNextEvent1,adverseNextEvent2,adverseNextEvent3,adverseNextEvent4,adverseNextEvent5,adverseNextEvent6,adverseNextEvent7,adverseNextEvent8,adverseNextEvent9,adverseNextEvent10,adverseNextEvent11,adverseNextEvent12,adverseNextEvent13,adverseNextEvent14,adverseNextEvent15,adverseNextEvent16,adverseNextEvent17,adverseNextEvent18,adverseNextEvent19,adverseNextEvent20,adverseNextEvent21,adverseNextEvent22,adverseNextEvent23,adverseNextEvent24,taskReward]
    <;> norm_num
  have hp : rawVisits adverseNextS25Before [] = 24 := by decide
  have hn : rawVisits adverseNextS25Before ([]++[.query 3]) = 3 := by decide
  have hz : (controlPenalty savedCref uniformQuoteError unitRoleUnused .next) adverseNextS25Before [] (.query 3) = (nextNormalPenalty adverseNextS25Before) := by
    simpa only [adverseNextS25Before,nextNormalPenalty] using AgentUCTNextExact.adverse_next_normal_root_quotes_exact 24 (by omega) 3 (by decide)
  unfold indexScore
  rw [hs,hp,hn,hz]
  simp only [BackupStat.mean]
  norm_num

theorem adverseNextS25D0I4 : indexScore (7/5) (controlPenalty savedCref uniformQuoteError unitRoleUnused .next) adverseNextS25Before [] (.query 4) = treeIndex ((0/1)/3) (7/5) (nextNormalPenalty adverseNextS25Before) 24 3 := by
  have hs : replayBackup adverseNextS25Before emptyStatistics ([]++[.query 4]) = ⟨3,(0/1)⟩ := by
    rw [replayBackup_empty_closed_form]
    simp +decide [backedEvents,adverseNextS25Before,adverseNextProposal,adverseNextEvent1,adverseNextEvent2,adverseNextEvent3,adverseNextEvent4,adverseNextEvent5,adverseNextEvent6,adverseNextEvent7,adverseNextEvent8,adverseNextEvent9,adverseNextEvent10,adverseNextEvent11,adverseNextEvent12,adverseNextEvent13,adverseNextEvent14,adverseNextEvent15,adverseNextEvent16,adverseNextEvent17,adverseNextEvent18,adverseNextEvent19,adverseNextEvent20,adverseNextEvent21,adverseNextEvent22,adverseNextEvent23,adverseNextEvent24,taskReward]
    <;> norm_num
  have hp : rawVisits adverseNextS25Before [] = 24 := by decide
  have hn : rawVisits adverseNextS25Before ([]++[.query 4]) = 3 := by decide
  have hz : (controlPenalty savedCref uniformQuoteError unitRoleUnused .next) adverseNextS25Before [] (.query 4) = (nextNormalPenalty adverseNextS25Before) := by
    simpa only [adverseNextS25Before,nextNormalPenalty] using AgentUCTNextExact.adverse_next_normal_root_quotes_exact 24 (by omega) 4 (by decide)
  unfold indexScore
  rw [hs,hp,hn,hz]
  simp only [BackupStat.mean]
  norm_num

theorem adverseNextS25D0I5 : indexScore (7/5) (controlPenalty savedCref uniformQuoteError unitRoleUnused .next) adverseNextS25Before [] (.query 5) = treeIndex ((13/10)/4) (7/5) (nextNormalPenalty adverseNextS25Before) 24 4 := by
  have hs : replayBackup adverseNextS25Before emptyStatistics ([]++[.query 5]) = ⟨4,(13/10)⟩ := by
    rw [replayBackup_empty_closed_form]
    simp +decide [backedEvents,adverseNextS25Before,adverseNextProposal,adverseNextEvent1,adverseNextEvent2,adverseNextEvent3,adverseNextEvent4,adverseNextEvent5,adverseNextEvent6,adverseNextEvent7,adverseNextEvent8,adverseNextEvent9,adverseNextEvent10,adverseNextEvent11,adverseNextEvent12,adverseNextEvent13,adverseNextEvent14,adverseNextEvent15,adverseNextEvent16,adverseNextEvent17,adverseNextEvent18,adverseNextEvent19,adverseNextEvent20,adverseNextEvent21,adverseNextEvent22,adverseNextEvent23,adverseNextEvent24,taskReward]
    <;> norm_num
  have hp : rawVisits adverseNextS25Before [] = 24 := by decide
  have hn : rawVisits adverseNextS25Before ([]++[.query 5]) = 4 := by decide
  have hz : (controlPenalty savedCref uniformQuoteError unitRoleUnused .next) adverseNextS25Before [] (.query 5) = (nextNormalPenalty adverseNextS25Before) := by
    simpa only [adverseNextS25Before,nextNormalPenalty] using AgentUCTNextExact.adverse_next_normal_root_quotes_exact 24 (by omega) 5 (by decide)
  unfold indexScore
  rw [hs,hp,hn,hz]
  simp only [BackupStat.mean]
  norm_num

theorem adverseNextS25D0I6 : indexScore (7/5) (controlPenalty savedCref uniformQuoteError unitRoleUnused .next) adverseNextS25Before [] (.query 6) = treeIndex ((0/1)/3) (7/5) (nextNormalPenalty adverseNextS25Before) 24 3 := by
  have hs : replayBackup adverseNextS25Before emptyStatistics ([]++[.query 6]) = ⟨3,(0/1)⟩ := by
    rw [replayBackup_empty_closed_form]
    simp +decide [backedEvents,adverseNextS25Before,adverseNextProposal,adverseNextEvent1,adverseNextEvent2,adverseNextEvent3,adverseNextEvent4,adverseNextEvent5,adverseNextEvent6,adverseNextEvent7,adverseNextEvent8,adverseNextEvent9,adverseNextEvent10,adverseNextEvent11,adverseNextEvent12,adverseNextEvent13,adverseNextEvent14,adverseNextEvent15,adverseNextEvent16,adverseNextEvent17,adverseNextEvent18,adverseNextEvent19,adverseNextEvent20,adverseNextEvent21,adverseNextEvent22,adverseNextEvent23,adverseNextEvent24,taskReward]
    <;> norm_num
  have hp : rawVisits adverseNextS25Before [] = 24 := by decide
  have hn : rawVisits adverseNextS25Before ([]++[.query 6]) = 3 := by decide
  have hz : (controlPenalty savedCref uniformQuoteError unitRoleUnused .next) adverseNextS25Before [] (.query 6) = (nextNormalPenalty adverseNextS25Before) := by
    simpa only [adverseNextS25Before,nextNormalPenalty] using AgentUCTNextExact.adverse_next_normal_root_quotes_exact 24 (by omega) 6 (by decide)
  unfold indexScore
  rw [hs,hp,hn,hz]
  simp only [BackupStat.mean]
  norm_num

theorem adverseNextS25D0I7 : indexScore (7/5) (controlPenalty savedCref uniformQuoteError unitRoleUnused .next) adverseNextS25Before [] (.query 7) = treeIndex ((0/1)/2) (7/5) (nextNormalPenalty adverseNextS25Before) 24 2 := by
  have hs : replayBackup adverseNextS25Before emptyStatistics ([]++[.query 7]) = ⟨2,(0/1)⟩ := by
    rw [replayBackup_empty_closed_form]
    simp +decide [backedEvents,adverseNextS25Before,adverseNextProposal,adverseNextEvent1,adverseNextEvent2,adverseNextEvent3,adverseNextEvent4,adverseNextEvent5,adverseNextEvent6,adverseNextEvent7,adverseNextEvent8,adverseNextEvent9,adverseNextEvent10,adverseNextEvent11,adverseNextEvent12,adverseNextEvent13,adverseNextEvent14,adverseNextEvent15,adverseNextEvent16,adverseNextEvent17,adverseNextEvent18,adverseNextEvent19,adverseNextEvent20,adverseNextEvent21,adverseNextEvent22,adverseNextEvent23,adverseNextEvent24,taskReward]
    <;> norm_num
  have hp : rawVisits adverseNextS25Before [] = 24 := by decide
  have hn : rawVisits adverseNextS25Before ([]++[.query 7]) = 2 := by decide
  have hz : (controlPenalty savedCref uniformQuoteError unitRoleUnused .next) adverseNextS25Before [] (.query 7) = (nextNormalPenalty adverseNextS25Before) := by
    simpa only [adverseNextS25Before,nextNormalPenalty] using AgentUCTNextExact.adverse_next_normal_root_quotes_exact 24 (by omega) 7 (by decide)
  unfold indexScore
  rw [hs,hp,hn,hz]
  simp only [BackupStat.mean]
  norm_num

theorem adverseNextS25D0Cmp0 : indexScore (7/5) (controlPenalty savedCref uniformQuoteError unitRoleUnused .next) adverseNextS25Before [] (.query 0) < indexScore (7/5) (controlPenalty savedCref uniformQuoteError unitRoleUnused .next) adverseNextS25Before [] (.query 7) := by
  rw [adverseNextS25D0I0,adverseNextS25D0I7]
  have hk := adverse_next_penalty_interval 24 (by omega)
  change nextNormalPenaltyLower ≤ nextNormalPenalty adverseNextS25Before ∧ nextNormalPenalty adverseNextS25Before ≤ nextNormalPenaltyUpper at hk
  have hm : ((0/1)/3)+(18127151/12500000)-(nextNormalPenalty adverseNextS25Before) < ((0/1)/2)+(44402267/25000000)-(nextNormalPenalty adverseNextS25Before) := by
    have h : (((0/1)/3)+(18127151/12500000) : ℝ) < ((0/1)/2)+(44402267/25000000) := by norm_num
    linarith
  have h := index_strict_order_from_intervals ((0/1)/2) ((0/1)/3) (nextNormalPenalty adverseNextS25Before) (nextNormalPenalty adverseNextS25Before) (44402267/25000000) (18127151/12500000)
    (treeBonus (7/5) 24 2) (treeBonus (7/5) 24 3)
    (trajectory_bonus_24_2).1 (trajectory_bonus_24_3).2 hm
  simpa only [treeIndex] using h

theorem adverseNextS25D0Cmp1 : indexScore (7/5) (controlPenalty savedCref uniformQuoteError unitRoleUnused .next) adverseNextS25Before [] (.query 1) < indexScore (7/5) (controlPenalty savedCref uniformQuoteError unitRoleUnused .next) adverseNextS25Before [] (.query 7) := by
  rw [adverseNextS25D0I1,adverseNextS25D0I7]
  have hk := adverse_next_penalty_interval 24 (by omega)
  change nextNormalPenaltyLower ≤ nextNormalPenalty adverseNextS25Before ∧ nextNormalPenalty adverseNextS25Before ≤ nextNormalPenaltyUpper at hk
  have hm : ((0/1)/3)+(18127151/12500000)-0 < ((0/1)/2)+(44402267/25000000)-(nextNormalPenalty adverseNextS25Before) := by
    have h : ((0/1)/3)+(18127151/12500000) < ((0/1)/2)+(44402267/25000000)-nextNormalPenaltyUpper := by norm_num [nextNormalPenaltyUpper,savedCref,uniformQuoteError]
    linarith [hk.2]
  have h := index_strict_order_from_intervals ((0/1)/2) ((0/1)/3) (nextNormalPenalty adverseNextS25Before) 0 (44402267/25000000) (18127151/12500000)
    (treeBonus (7/5) 24 2) (treeBonus (7/5) 24 3)
    (trajectory_bonus_24_2).1 (trajectory_bonus_24_3).2 hm
  simpa only [treeIndex] using h

theorem adverseNextS25D0Cmp2 : indexScore (7/5) (controlPenalty savedCref uniformQuoteError unitRoleUnused .next) adverseNextS25Before [] (.query 2) < indexScore (7/5) (controlPenalty savedCref uniformQuoteError unitRoleUnused .next) adverseNextS25Before [] (.query 7) := by
  rw [adverseNextS25D0I2,adverseNextS25D0I7]
  have hk := adverse_next_penalty_interval 24 (by omega)
  change nextNormalPenaltyLower ≤ nextNormalPenalty adverseNextS25Before ∧ nextNormalPenalty adverseNextS25Before ≤ nextNormalPenaltyUpper at hk
  have hm : ((0/1)/3)+(18127151/12500000)-(nextNormalPenalty adverseNextS25Before) < ((0/1)/2)+(44402267/25000000)-(nextNormalPenalty adverseNextS25Before) := by
    have h : (((0/1)/3)+(18127151/12500000) : ℝ) < ((0/1)/2)+(44402267/25000000) := by norm_num
    linarith
  have h := index_strict_order_from_intervals ((0/1)/2) ((0/1)/3) (nextNormalPenalty adverseNextS25Before) (nextNormalPenalty adverseNextS25Before) (44402267/25000000) (18127151/12500000)
    (treeBonus (7/5) 24 2) (treeBonus (7/5) 24 3)
    (trajectory_bonus_24_2).1 (trajectory_bonus_24_3).2 hm
  simpa only [treeIndex] using h

theorem adverseNextS25D0Cmp3 : indexScore (7/5) (controlPenalty savedCref uniformQuoteError unitRoleUnused .next) adverseNextS25Before [] (.query 3) < indexScore (7/5) (controlPenalty savedCref uniformQuoteError unitRoleUnused .next) adverseNextS25Before [] (.query 7) := by
  rw [adverseNextS25D0I3,adverseNextS25D0I7]
  have hk := adverse_next_penalty_interval 24 (by omega)
  change nextNormalPenaltyLower ≤ nextNormalPenalty adverseNextS25Before ∧ nextNormalPenalty adverseNextS25Before ≤ nextNormalPenaltyUpper at hk
  have hm : ((0/1)/3)+(18127151/12500000)-(nextNormalPenalty adverseNextS25Before) < ((0/1)/2)+(44402267/25000000)-(nextNormalPenalty adverseNextS25Before) := by
    have h : (((0/1)/3)+(18127151/12500000) : ℝ) < ((0/1)/2)+(44402267/25000000) := by norm_num
    linarith
  have h := index_strict_order_from_intervals ((0/1)/2) ((0/1)/3) (nextNormalPenalty adverseNextS25Before) (nextNormalPenalty adverseNextS25Before) (44402267/25000000) (18127151/12500000)
    (treeBonus (7/5) 24 2) (treeBonus (7/5) 24 3)
    (trajectory_bonus_24_2).1 (trajectory_bonus_24_3).2 hm
  simpa only [treeIndex] using h

theorem adverseNextS25D0Cmp4 : indexScore (7/5) (controlPenalty savedCref uniformQuoteError unitRoleUnused .next) adverseNextS25Before [] (.query 4) < indexScore (7/5) (controlPenalty savedCref uniformQuoteError unitRoleUnused .next) adverseNextS25Before [] (.query 7) := by
  rw [adverseNextS25D0I4,adverseNextS25D0I7]
  have hk := adverse_next_penalty_interval 24 (by omega)
  change nextNormalPenaltyLower ≤ nextNormalPenalty adverseNextS25Before ∧ nextNormalPenalty adverseNextS25Before ≤ nextNormalPenaltyUpper at hk
  have hm : ((0/1)/3)+(18127151/12500000)-(nextNormalPenalty adverseNextS25Before) < ((0/1)/2)+(44402267/25000000)-(nextNormalPenalty adverseNextS25Before) := by
    have h : (((0/1)/3)+(18127151/12500000) : ℝ) < ((0/1)/2)+(44402267/25000000) := by norm_num
    linarith
  have h := index_strict_order_from_intervals ((0/1)/2) ((0/1)/3) (nextNormalPenalty adverseNextS25Before) (nextNormalPenalty adverseNextS25Before) (44402267/25000000) (18127151/12500000)
    (treeBonus (7/5) 24 2) (treeBonus (7/5) 24 3)
    (trajectory_bonus_24_2).1 (trajectory_bonus_24_3).2 hm
  simpa only [treeIndex] using h

theorem adverseNextS25D0Cmp5 : indexScore (7/5) (controlPenalty savedCref uniformQuoteError unitRoleUnused .next) adverseNextS25Before [] (.query 5) < indexScore (7/5) (controlPenalty savedCref uniformQuoteError unitRoleUnused .next) adverseNextS25Before [] (.query 7) := by
  rw [adverseNextS25D0I5,adverseNextS25D0I7]
  have hk := adverse_next_penalty_interval 24 (by omega)
  change nextNormalPenaltyLower ≤ nextNormalPenalty adverseNextS25Before ∧ nextNormalPenalty adverseNextS25Before ≤ nextNormalPenaltyUpper at hk
  have hm : ((13/10)/4)+(62794291/50000000)-(nextNormalPenalty adverseNextS25Before) < ((0/1)/2)+(44402267/25000000)-(nextNormalPenalty adverseNextS25Before) := by
    have h : (((13/10)/4)+(62794291/50000000) : ℝ) < ((0/1)/2)+(44402267/25000000) := by norm_num
    linarith
  have h := index_strict_order_from_intervals ((0/1)/2) ((13/10)/4) (nextNormalPenalty adverseNextS25Before) (nextNormalPenalty adverseNextS25Before) (44402267/25000000) (62794291/50000000)
    (treeBonus (7/5) 24 2) (treeBonus (7/5) 24 4)
    (trajectory_bonus_24_2).1 (trajectory_bonus_24_4).2 hm
  simpa only [treeIndex] using h

theorem adverseNextS25D0Cmp6 : indexScore (7/5) (controlPenalty savedCref uniformQuoteError unitRoleUnused .next) adverseNextS25Before [] (.query 6) < indexScore (7/5) (controlPenalty savedCref uniformQuoteError unitRoleUnused .next) adverseNextS25Before [] (.query 7) := by
  rw [adverseNextS25D0I6,adverseNextS25D0I7]
  have hk := adverse_next_penalty_interval 24 (by omega)
  change nextNormalPenaltyLower ≤ nextNormalPenalty adverseNextS25Before ∧ nextNormalPenalty adverseNextS25Before ≤ nextNormalPenaltyUpper at hk
  have hm : ((0/1)/3)+(18127151/12500000)-(nextNormalPenalty adverseNextS25Before) < ((0/1)/2)+(44402267/25000000)-(nextNormalPenalty adverseNextS25Before) := by
    have h : (((0/1)/3)+(18127151/12500000) : ℝ) < ((0/1)/2)+(44402267/25000000) := by norm_num
    linarith
  have h := index_strict_order_from_intervals ((0/1)/2) ((0/1)/3) (nextNormalPenalty adverseNextS25Before) (nextNormalPenalty adverseNextS25Before) (44402267/25000000) (18127151/12500000)
    (treeBonus (7/5) 24 2) (treeBonus (7/5) 24 3)
    (trajectory_bonus_24_2).1 (trajectory_bonus_24_3).2 hm
  simpa only [treeIndex] using h

theorem adverseNextS25Choice0 : nativeFirstChoice (indexScore (7/5) (controlPenalty savedCref uniformQuoteError unitRoleUnused .next) adverseNextS25Before []) adverseNextS25Before [] = .query 7 := by
  apply visited_choice_from_ordered_certificate _ _ [] [.query 0,.query 1,.query 2,.query 3,.query 4,.query 5,.query 6] [] (.query 7) (by decide)
  · intro a ha
    have ho : orderedLegalAvailable [] = [.query 0,.query 1,.query 2,.query 3,.query 4,.query 5,.query 6,.query 7] := by decide
    rw [ho] at ha
    simp only [List.mem_cons,List.not_mem_nil,or_false] at ha
    rcases ha with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> decide
  · intro a ha
    simp only [List.mem_cons,List.not_mem_nil,or_false] at ha
    rcases ha with rfl | rfl | rfl | rfl | rfl | rfl | rfl
    · exact adverseNextS25D0Cmp0
    · exact adverseNextS25D0Cmp1
    · exact adverseNextS25D0Cmp2
    · exact adverseNextS25D0Cmp3
    · exact adverseNextS25D0Cmp4
    · exact adverseNextS25D0Cmp5
    · exact adverseNextS25D0Cmp6
  · simp

theorem adverseNextS25ActualEvent : nativeEvent budgetTape (7/5) (controlPenalty savedCref uniformQuoteError unitRoleUnused .next)
    (taskReward true (2/5) (1/2)) adverseNextS25Before = adverseNextEvent25 := by
  have hs0 := native_select_existing_step budgetTape (7/5) (controlPenalty savedCref uniformQuoteError unitRoleUnused .next) adverseNextS25Before 8 [] (.query 7)
    (by decide) (by decide) adverseNextS25Choice0
  have hnew := native_select_new_step budgetTape (7/5) (controlPenalty savedCref uniformQuoteError unitRoleUnused .next) adverseNextS25Before 7 [.query 7]
    [.normalRetriever 4,.normalRetriever 6,.normalRetriever 7,.normalRetriever 8,.normalRetriever 5,.normalRetriever 1,.normalRetriever 2,.normalRetriever 3,.normalRetriever 12,.normalRetriever 14,.normalRetriever 13,.normalRetriever 21,.normalRetriever 23,.normalRetriever 22,.normalRetriever 9,.normalRetriever 11,.normalRetriever 10,.normalRetriever 15,.normalRetriever 17,.normalRetriever 16,.normalRetriever 18,.normalRetriever 20,.normalRetriever 19,.normalRetriever 24,.normalRetriever 25,.normalRetriever 26,.normalRetriever 27,.normalRetriever 28,.normalRetriever 29] (.normalRetriever 4) (by decide) (by decide) (by decide) (by decide)
  have hs : nativeSelect budgetTape (7/5) (controlPenalty savedCref uniformQuoteError unitRoleUnused .next) adverseNextS25Before 9 [] = [.query 7,.normalRetriever 4] := by
    rw [hs0]
    change nativeSelect budgetTape (7/5) (controlPenalty savedCref uniformQuoteError unitRoleUnused .next) adverseNextS25Before 8 [.query 7] = _
    rw [hnew] <;> rfl
  have hr : repairedRollout budgetTape adverseNextS25Before 9 [.query 7,.normalRetriever 4] = [.query 7,.normalRetriever 4,.selection 0,.width 0,.stop,.reranker 0,.topm 0,.context 0,.answer 0] := by decide
  simp only [nativeEvent,hs,hr]
  rfl

def adverseNextS26Before := adverseNextProposal.take 25

theorem adverseNextS26D0I0 : indexScore (7/5) (controlPenalty savedCref uniformQuoteError unitRoleUnused .next) adverseNextS26Before [] (.query 0) = treeIndex ((0/1)/3) (7/5) (nextNormalPenalty adverseNextS26Before) 25 3 := by
  have hs : replayBackup adverseNextS26Before emptyStatistics ([]++[.query 0]) = ⟨3,(0/1)⟩ := by
    rw [replayBackup_empty_closed_form]
    simp +decide [backedEvents,adverseNextS26Before,adverseNextProposal,adverseNextEvent1,adverseNextEvent2,adverseNextEvent3,adverseNextEvent4,adverseNextEvent5,adverseNextEvent6,adverseNextEvent7,adverseNextEvent8,adverseNextEvent9,adverseNextEvent10,adverseNextEvent11,adverseNextEvent12,adverseNextEvent13,adverseNextEvent14,adverseNextEvent15,adverseNextEvent16,adverseNextEvent17,adverseNextEvent18,adverseNextEvent19,adverseNextEvent20,adverseNextEvent21,adverseNextEvent22,adverseNextEvent23,adverseNextEvent24,adverseNextEvent25,taskReward]
    <;> norm_num
  have hp : rawVisits adverseNextS26Before [] = 25 := by decide
  have hn : rawVisits adverseNextS26Before ([]++[.query 0]) = 3 := by decide
  have hz : (controlPenalty savedCref uniformQuoteError unitRoleUnused .next) adverseNextS26Before [] (.query 0) = (nextNormalPenalty adverseNextS26Before) := by
    simpa only [adverseNextS26Before,nextNormalPenalty] using AgentUCTNextExact.adverse_next_normal_root_quotes_exact 25 (by omega) 0 (by decide)
  unfold indexScore
  rw [hs,hp,hn,hz]
  simp only [BackupStat.mean]
  norm_num

theorem adverseNextS26D0I1 : indexScore (7/5) (controlPenalty savedCref uniformQuoteError unitRoleUnused .next) adverseNextS26Before [] (.query 1) = treeIndex ((0/1)/3) (7/5) 0 25 3 := by
  have hs : replayBackup adverseNextS26Before emptyStatistics ([]++[.query 1]) = ⟨3,(0/1)⟩ := by
    rw [replayBackup_empty_closed_form]
    simp +decide [backedEvents,adverseNextS26Before,adverseNextProposal,adverseNextEvent1,adverseNextEvent2,adverseNextEvent3,adverseNextEvent4,adverseNextEvent5,adverseNextEvent6,adverseNextEvent7,adverseNextEvent8,adverseNextEvent9,adverseNextEvent10,adverseNextEvent11,adverseNextEvent12,adverseNextEvent13,adverseNextEvent14,adverseNextEvent15,adverseNextEvent16,adverseNextEvent17,adverseNextEvent18,adverseNextEvent19,adverseNextEvent20,adverseNextEvent21,adverseNextEvent22,adverseNextEvent23,adverseNextEvent24,adverseNextEvent25,taskReward]
    <;> norm_num
  have hp : rawVisits adverseNextS26Before [] = 25 := by decide
  have hn : rawVisits adverseNextS26Before ([]++[.query 1]) = 3 := by decide
  have hz : (controlPenalty savedCref uniformQuoteError unitRoleUnused .next) adverseNextS26Before [] (.query 1) = 0 := by
    apply control_penalty_empty_suffix
    exact AgentUCTNextExact.adverse_next_hyde_root_suffix_empty 25 (by omega)
  unfold indexScore
  rw [hs,hp,hn,hz]
  simp only [BackupStat.mean]
  norm_num

theorem adverseNextS26D0I2 : indexScore (7/5) (controlPenalty savedCref uniformQuoteError unitRoleUnused .next) adverseNextS26Before [] (.query 2) = treeIndex ((0/1)/3) (7/5) (nextNormalPenalty adverseNextS26Before) 25 3 := by
  have hs : replayBackup adverseNextS26Before emptyStatistics ([]++[.query 2]) = ⟨3,(0/1)⟩ := by
    rw [replayBackup_empty_closed_form]
    simp +decide [backedEvents,adverseNextS26Before,adverseNextProposal,adverseNextEvent1,adverseNextEvent2,adverseNextEvent3,adverseNextEvent4,adverseNextEvent5,adverseNextEvent6,adverseNextEvent7,adverseNextEvent8,adverseNextEvent9,adverseNextEvent10,adverseNextEvent11,adverseNextEvent12,adverseNextEvent13,adverseNextEvent14,adverseNextEvent15,adverseNextEvent16,adverseNextEvent17,adverseNextEvent18,adverseNextEvent19,adverseNextEvent20,adverseNextEvent21,adverseNextEvent22,adverseNextEvent23,adverseNextEvent24,adverseNextEvent25,taskReward]
    <;> norm_num
  have hp : rawVisits adverseNextS26Before [] = 25 := by decide
  have hn : rawVisits adverseNextS26Before ([]++[.query 2]) = 3 := by decide
  have hz : (controlPenalty savedCref uniformQuoteError unitRoleUnused .next) adverseNextS26Before [] (.query 2) = (nextNormalPenalty adverseNextS26Before) := by
    simpa only [adverseNextS26Before,nextNormalPenalty] using AgentUCTNextExact.adverse_next_normal_root_quotes_exact 25 (by omega) 2 (by decide)
  unfold indexScore
  rw [hs,hp,hn,hz]
  simp only [BackupStat.mean]
  norm_num

theorem adverseNextS26D0I3 : indexScore (7/5) (controlPenalty savedCref uniformQuoteError unitRoleUnused .next) adverseNextS26Before [] (.query 3) = treeIndex ((0/1)/3) (7/5) (nextNormalPenalty adverseNextS26Before) 25 3 := by
  have hs : replayBackup adverseNextS26Before emptyStatistics ([]++[.query 3]) = ⟨3,(0/1)⟩ := by
    rw [replayBackup_empty_closed_form]
    simp +decide [backedEvents,adverseNextS26Before,adverseNextProposal,adverseNextEvent1,adverseNextEvent2,adverseNextEvent3,adverseNextEvent4,adverseNextEvent5,adverseNextEvent6,adverseNextEvent7,adverseNextEvent8,adverseNextEvent9,adverseNextEvent10,adverseNextEvent11,adverseNextEvent12,adverseNextEvent13,adverseNextEvent14,adverseNextEvent15,adverseNextEvent16,adverseNextEvent17,adverseNextEvent18,adverseNextEvent19,adverseNextEvent20,adverseNextEvent21,adverseNextEvent22,adverseNextEvent23,adverseNextEvent24,adverseNextEvent25,taskReward]
    <;> norm_num
  have hp : rawVisits adverseNextS26Before [] = 25 := by decide
  have hn : rawVisits adverseNextS26Before ([]++[.query 3]) = 3 := by decide
  have hz : (controlPenalty savedCref uniformQuoteError unitRoleUnused .next) adverseNextS26Before [] (.query 3) = (nextNormalPenalty adverseNextS26Before) := by
    simpa only [adverseNextS26Before,nextNormalPenalty] using AgentUCTNextExact.adverse_next_normal_root_quotes_exact 25 (by omega) 3 (by decide)
  unfold indexScore
  rw [hs,hp,hn,hz]
  simp only [BackupStat.mean]
  norm_num

theorem adverseNextS26D0I4 : indexScore (7/5) (controlPenalty savedCref uniformQuoteError unitRoleUnused .next) adverseNextS26Before [] (.query 4) = treeIndex ((0/1)/3) (7/5) (nextNormalPenalty adverseNextS26Before) 25 3 := by
  have hs : replayBackup adverseNextS26Before emptyStatistics ([]++[.query 4]) = ⟨3,(0/1)⟩ := by
    rw [replayBackup_empty_closed_form]
    simp +decide [backedEvents,adverseNextS26Before,adverseNextProposal,adverseNextEvent1,adverseNextEvent2,adverseNextEvent3,adverseNextEvent4,adverseNextEvent5,adverseNextEvent6,adverseNextEvent7,adverseNextEvent8,adverseNextEvent9,adverseNextEvent10,adverseNextEvent11,adverseNextEvent12,adverseNextEvent13,adverseNextEvent14,adverseNextEvent15,adverseNextEvent16,adverseNextEvent17,adverseNextEvent18,adverseNextEvent19,adverseNextEvent20,adverseNextEvent21,adverseNextEvent22,adverseNextEvent23,adverseNextEvent24,adverseNextEvent25,taskReward]
    <;> norm_num
  have hp : rawVisits adverseNextS26Before [] = 25 := by decide
  have hn : rawVisits adverseNextS26Before ([]++[.query 4]) = 3 := by decide
  have hz : (controlPenalty savedCref uniformQuoteError unitRoleUnused .next) adverseNextS26Before [] (.query 4) = (nextNormalPenalty adverseNextS26Before) := by
    simpa only [adverseNextS26Before,nextNormalPenalty] using AgentUCTNextExact.adverse_next_normal_root_quotes_exact 25 (by omega) 4 (by decide)
  unfold indexScore
  rw [hs,hp,hn,hz]
  simp only [BackupStat.mean]
  norm_num

theorem adverseNextS26D0I5 : indexScore (7/5) (controlPenalty savedCref uniformQuoteError unitRoleUnused .next) adverseNextS26Before [] (.query 5) = treeIndex ((13/10)/4) (7/5) (nextNormalPenalty adverseNextS26Before) 25 4 := by
  have hs : replayBackup adverseNextS26Before emptyStatistics ([]++[.query 5]) = ⟨4,(13/10)⟩ := by
    rw [replayBackup_empty_closed_form]
    simp +decide [backedEvents,adverseNextS26Before,adverseNextProposal,adverseNextEvent1,adverseNextEvent2,adverseNextEvent3,adverseNextEvent4,adverseNextEvent5,adverseNextEvent6,adverseNextEvent7,adverseNextEvent8,adverseNextEvent9,adverseNextEvent10,adverseNextEvent11,adverseNextEvent12,adverseNextEvent13,adverseNextEvent14,adverseNextEvent15,adverseNextEvent16,adverseNextEvent17,adverseNextEvent18,adverseNextEvent19,adverseNextEvent20,adverseNextEvent21,adverseNextEvent22,adverseNextEvent23,adverseNextEvent24,adverseNextEvent25,taskReward]
    <;> norm_num
  have hp : rawVisits adverseNextS26Before [] = 25 := by decide
  have hn : rawVisits adverseNextS26Before ([]++[.query 5]) = 4 := by decide
  have hz : (controlPenalty savedCref uniformQuoteError unitRoleUnused .next) adverseNextS26Before [] (.query 5) = (nextNormalPenalty adverseNextS26Before) := by
    simpa only [adverseNextS26Before,nextNormalPenalty] using AgentUCTNextExact.adverse_next_normal_root_quotes_exact 25 (by omega) 5 (by decide)
  unfold indexScore
  rw [hs,hp,hn,hz]
  simp only [BackupStat.mean]
  norm_num

theorem adverseNextS26D0I6 : indexScore (7/5) (controlPenalty savedCref uniformQuoteError unitRoleUnused .next) adverseNextS26Before [] (.query 6) = treeIndex ((0/1)/3) (7/5) (nextNormalPenalty adverseNextS26Before) 25 3 := by
  have hs : replayBackup adverseNextS26Before emptyStatistics ([]++[.query 6]) = ⟨3,(0/1)⟩ := by
    rw [replayBackup_empty_closed_form]
    simp +decide [backedEvents,adverseNextS26Before,adverseNextProposal,adverseNextEvent1,adverseNextEvent2,adverseNextEvent3,adverseNextEvent4,adverseNextEvent5,adverseNextEvent6,adverseNextEvent7,adverseNextEvent8,adverseNextEvent9,adverseNextEvent10,adverseNextEvent11,adverseNextEvent12,adverseNextEvent13,adverseNextEvent14,adverseNextEvent15,adverseNextEvent16,adverseNextEvent17,adverseNextEvent18,adverseNextEvent19,adverseNextEvent20,adverseNextEvent21,adverseNextEvent22,adverseNextEvent23,adverseNextEvent24,adverseNextEvent25,taskReward]
    <;> norm_num
  have hp : rawVisits adverseNextS26Before [] = 25 := by decide
  have hn : rawVisits adverseNextS26Before ([]++[.query 6]) = 3 := by decide
  have hz : (controlPenalty savedCref uniformQuoteError unitRoleUnused .next) adverseNextS26Before [] (.query 6) = (nextNormalPenalty adverseNextS26Before) := by
    simpa only [adverseNextS26Before,nextNormalPenalty] using AgentUCTNextExact.adverse_next_normal_root_quotes_exact 25 (by omega) 6 (by decide)
  unfold indexScore
  rw [hs,hp,hn,hz]
  simp only [BackupStat.mean]
  norm_num

theorem adverseNextS26D0I7 : indexScore (7/5) (controlPenalty savedCref uniformQuoteError unitRoleUnused .next) adverseNextS26Before [] (.query 7) = treeIndex ((0/1)/3) (7/5) (nextNormalPenalty adverseNextS26Before) 25 3 := by
  have hs : replayBackup adverseNextS26Before emptyStatistics ([]++[.query 7]) = ⟨3,(0/1)⟩ := by
    rw [replayBackup_empty_closed_form]
    simp +decide [backedEvents,adverseNextS26Before,adverseNextProposal,adverseNextEvent1,adverseNextEvent2,adverseNextEvent3,adverseNextEvent4,adverseNextEvent5,adverseNextEvent6,adverseNextEvent7,adverseNextEvent8,adverseNextEvent9,adverseNextEvent10,adverseNextEvent11,adverseNextEvent12,adverseNextEvent13,adverseNextEvent14,adverseNextEvent15,adverseNextEvent16,adverseNextEvent17,adverseNextEvent18,adverseNextEvent19,adverseNextEvent20,adverseNextEvent21,adverseNextEvent22,adverseNextEvent23,adverseNextEvent24,adverseNextEvent25,taskReward]
    <;> norm_num
  have hp : rawVisits adverseNextS26Before [] = 25 := by decide
  have hn : rawVisits adverseNextS26Before ([]++[.query 7]) = 3 := by decide
  have hz : (controlPenalty savedCref uniformQuoteError unitRoleUnused .next) adverseNextS26Before [] (.query 7) = (nextNormalPenalty adverseNextS26Before) := by
    simpa only [adverseNextS26Before,nextNormalPenalty] using AgentUCTNextExact.adverse_next_normal_root_quotes_exact 25 (by omega) 7 (by decide)
  unfold indexScore
  rw [hs,hp,hn,hz]
  simp only [BackupStat.mean]
  norm_num

theorem adverseNextS26D0Cmp0 : indexScore (7/5) (controlPenalty savedCref uniformQuoteError unitRoleUnused .next) adverseNextS26Before [] (.query 0) < indexScore (7/5) (controlPenalty savedCref uniformQuoteError unitRoleUnused .next) adverseNextS26Before [] (.query 1) := by
  rw [adverseNextS26D0I0,adverseNextS26D0I1]
  have hk := adverse_next_penalty_interval 25 (by omega)
  change nextNormalPenaltyLower ≤ nextNormalPenalty adverseNextS26Before ∧ nextNormalPenalty adverseNextS26Before ≤ nextNormalPenaltyUpper at hk
  have hm : ((0/1)/3)+(72949009/50000000)-(nextNormalPenalty adverseNextS26Before) < ((0/1)/3)+(36474501/25000000)-0 := by
    have h : ((0/1)/3)+(72949009/50000000)-nextNormalPenaltyLower < ((0/1)/3)+(36474501/25000000) := by norm_num [nextNormalPenaltyLower,savedCref,uniformQuoteError]
    linarith [hk.1]
  have h := index_strict_order_from_intervals ((0/1)/3) ((0/1)/3) 0 (nextNormalPenalty adverseNextS26Before) (36474501/25000000) (72949009/50000000)
    (treeBonus (7/5) 25 3) (treeBonus (7/5) 25 3)
    (trajectory_bonus_25_3).1 (trajectory_bonus_25_3).2 hm
  simpa only [treeIndex] using h

theorem adverseNextS26D0Cmp2 : indexScore (7/5) (controlPenalty savedCref uniformQuoteError unitRoleUnused .next) adverseNextS26Before [] (.query 2) ≤ indexScore (7/5) (controlPenalty savedCref uniformQuoteError unitRoleUnused .next) adverseNextS26Before [] (.query 1) := by
  rw [adverseNextS26D0I2,adverseNextS26D0I1]
  have hk := adverse_next_penalty_interval 25 (by omega)
  change nextNormalPenaltyLower ≤ nextNormalPenalty adverseNextS26Before ∧ nextNormalPenalty adverseNextS26Before ≤ nextNormalPenaltyUpper at hk
  have hm : ((0/1)/3)+(72949009/50000000)-(nextNormalPenalty adverseNextS26Before) < ((0/1)/3)+(36474501/25000000)-0 := by
    have h : ((0/1)/3)+(72949009/50000000)-nextNormalPenaltyLower < ((0/1)/3)+(36474501/25000000) := by norm_num [nextNormalPenaltyLower,savedCref,uniformQuoteError]
    linarith [hk.1]
  have h := index_weak_order_from_intervals ((0/1)/3) ((0/1)/3) 0 (nextNormalPenalty adverseNextS26Before) (36474501/25000000) (72949009/50000000)
    (treeBonus (7/5) 25 3) (treeBonus (7/5) 25 3)
    (trajectory_bonus_25_3).1 (trajectory_bonus_25_3).2 hm.le
  simpa only [treeIndex] using h

theorem adverseNextS26D0Cmp3 : indexScore (7/5) (controlPenalty savedCref uniformQuoteError unitRoleUnused .next) adverseNextS26Before [] (.query 3) ≤ indexScore (7/5) (controlPenalty savedCref uniformQuoteError unitRoleUnused .next) adverseNextS26Before [] (.query 1) := by
  rw [adverseNextS26D0I3,adverseNextS26D0I1]
  have hk := adverse_next_penalty_interval 25 (by omega)
  change nextNormalPenaltyLower ≤ nextNormalPenalty adverseNextS26Before ∧ nextNormalPenalty adverseNextS26Before ≤ nextNormalPenaltyUpper at hk
  have hm : ((0/1)/3)+(72949009/50000000)-(nextNormalPenalty adverseNextS26Before) < ((0/1)/3)+(36474501/25000000)-0 := by
    have h : ((0/1)/3)+(72949009/50000000)-nextNormalPenaltyLower < ((0/1)/3)+(36474501/25000000) := by norm_num [nextNormalPenaltyLower,savedCref,uniformQuoteError]
    linarith [hk.1]
  have h := index_weak_order_from_intervals ((0/1)/3) ((0/1)/3) 0 (nextNormalPenalty adverseNextS26Before) (36474501/25000000) (72949009/50000000)
    (treeBonus (7/5) 25 3) (treeBonus (7/5) 25 3)
    (trajectory_bonus_25_3).1 (trajectory_bonus_25_3).2 hm.le
  simpa only [treeIndex] using h

theorem adverseNextS26D0Cmp4 : indexScore (7/5) (controlPenalty savedCref uniformQuoteError unitRoleUnused .next) adverseNextS26Before [] (.query 4) ≤ indexScore (7/5) (controlPenalty savedCref uniformQuoteError unitRoleUnused .next) adverseNextS26Before [] (.query 1) := by
  rw [adverseNextS26D0I4,adverseNextS26D0I1]
  have hk := adverse_next_penalty_interval 25 (by omega)
  change nextNormalPenaltyLower ≤ nextNormalPenalty adverseNextS26Before ∧ nextNormalPenalty adverseNextS26Before ≤ nextNormalPenaltyUpper at hk
  have hm : ((0/1)/3)+(72949009/50000000)-(nextNormalPenalty adverseNextS26Before) < ((0/1)/3)+(36474501/25000000)-0 := by
    have h : ((0/1)/3)+(72949009/50000000)-nextNormalPenaltyLower < ((0/1)/3)+(36474501/25000000) := by norm_num [nextNormalPenaltyLower,savedCref,uniformQuoteError]
    linarith [hk.1]
  have h := index_weak_order_from_intervals ((0/1)/3) ((0/1)/3) 0 (nextNormalPenalty adverseNextS26Before) (36474501/25000000) (72949009/50000000)
    (treeBonus (7/5) 25 3) (treeBonus (7/5) 25 3)
    (trajectory_bonus_25_3).1 (trajectory_bonus_25_3).2 hm.le
  simpa only [treeIndex] using h

theorem adverseNextS26D0Cmp5 : indexScore (7/5) (controlPenalty savedCref uniformQuoteError unitRoleUnused .next) adverseNextS26Before [] (.query 5) ≤ indexScore (7/5) (controlPenalty savedCref uniformQuoteError unitRoleUnused .next) adverseNextS26Before [] (.query 1) := by
  rw [adverseNextS26D0I5,adverseNextS26D0I1]
  have hk := adverse_next_penalty_interval 25 (by omega)
  change nextNormalPenaltyLower ≤ nextNormalPenalty adverseNextS26Before ∧ nextNormalPenalty adverseNextS26Before ≤ nextNormalPenaltyUpper at hk
  have hm : ((13/10)/4)+(631757/500000)-(nextNormalPenalty adverseNextS26Before) < ((0/1)/3)+(36474501/25000000)-0 := by
    have h : ((13/10)/4)+(631757/500000)-nextNormalPenaltyLower < ((0/1)/3)+(36474501/25000000) := by norm_num [nextNormalPenaltyLower,savedCref,uniformQuoteError]
    linarith [hk.1]
  have h := index_weak_order_from_intervals ((0/1)/3) ((13/10)/4) 0 (nextNormalPenalty adverseNextS26Before) (36474501/25000000) (631757/500000)
    (treeBonus (7/5) 25 3) (treeBonus (7/5) 25 4)
    (trajectory_bonus_25_3).1 (trajectory_bonus_25_4).2 hm.le
  simpa only [treeIndex] using h

theorem adverseNextS26D0Cmp6 : indexScore (7/5) (controlPenalty savedCref uniformQuoteError unitRoleUnused .next) adverseNextS26Before [] (.query 6) ≤ indexScore (7/5) (controlPenalty savedCref uniformQuoteError unitRoleUnused .next) adverseNextS26Before [] (.query 1) := by
  rw [adverseNextS26D0I6,adverseNextS26D0I1]
  have hk := adverse_next_penalty_interval 25 (by omega)
  change nextNormalPenaltyLower ≤ nextNormalPenalty adverseNextS26Before ∧ nextNormalPenalty adverseNextS26Before ≤ nextNormalPenaltyUpper at hk
  have hm : ((0/1)/3)+(72949009/50000000)-(nextNormalPenalty adverseNextS26Before) < ((0/1)/3)+(36474501/25000000)-0 := by
    have h : ((0/1)/3)+(72949009/50000000)-nextNormalPenaltyLower < ((0/1)/3)+(36474501/25000000) := by norm_num [nextNormalPenaltyLower,savedCref,uniformQuoteError]
    linarith [hk.1]
  have h := index_weak_order_from_intervals ((0/1)/3) ((0/1)/3) 0 (nextNormalPenalty adverseNextS26Before) (36474501/25000000) (72949009/50000000)
    (treeBonus (7/5) 25 3) (treeBonus (7/5) 25 3)
    (trajectory_bonus_25_3).1 (trajectory_bonus_25_3).2 hm.le
  simpa only [treeIndex] using h

theorem adverseNextS26D0Cmp7 : indexScore (7/5) (controlPenalty savedCref uniformQuoteError unitRoleUnused .next) adverseNextS26Before [] (.query 7) ≤ indexScore (7/5) (controlPenalty savedCref uniformQuoteError unitRoleUnused .next) adverseNextS26Before [] (.query 1) := by
  rw [adverseNextS26D0I7,adverseNextS26D0I1]
  have hk := adverse_next_penalty_interval 25 (by omega)
  change nextNormalPenaltyLower ≤ nextNormalPenalty adverseNextS26Before ∧ nextNormalPenalty adverseNextS26Before ≤ nextNormalPenaltyUpper at hk
  have hm : ((0/1)/3)+(72949009/50000000)-(nextNormalPenalty adverseNextS26Before) < ((0/1)/3)+(36474501/25000000)-0 := by
    have h : ((0/1)/3)+(72949009/50000000)-nextNormalPenaltyLower < ((0/1)/3)+(36474501/25000000) := by norm_num [nextNormalPenaltyLower,savedCref,uniformQuoteError]
    linarith [hk.1]
  have h := index_weak_order_from_intervals ((0/1)/3) ((0/1)/3) 0 (nextNormalPenalty adverseNextS26Before) (36474501/25000000) (72949009/50000000)
    (treeBonus (7/5) 25 3) (treeBonus (7/5) 25 3)
    (trajectory_bonus_25_3).1 (trajectory_bonus_25_3).2 hm.le
  simpa only [treeIndex] using h

theorem adverseNextS26Choice0 : nativeFirstChoice (indexScore (7/5) (controlPenalty savedCref uniformQuoteError unitRoleUnused .next) adverseNextS26Before []) adverseNextS26Before [] = .query 1 := by
  apply visited_choice_from_ordered_certificate _ _ [] [.query 0] [.query 2,.query 3,.query 4,.query 5,.query 6,.query 7] (.query 1) (by decide)
  · intro a ha
    have ho : orderedLegalAvailable [] = [.query 0,.query 1,.query 2,.query 3,.query 4,.query 5,.query 6,.query 7] := by decide
    rw [ho] at ha
    simp only [List.mem_cons,List.not_mem_nil,or_false] at ha
    rcases ha with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> decide
  · intro a ha
    simp only [List.mem_cons,List.not_mem_nil,or_false] at ha
    rcases ha with rfl
    · exact adverseNextS26D0Cmp0
  · intro a ha
    simp only [List.mem_cons,List.not_mem_nil,or_false] at ha
    rcases ha with rfl | rfl | rfl | rfl | rfl | rfl
    · exact adverseNextS26D0Cmp2
    · exact adverseNextS26D0Cmp3
    · exact adverseNextS26D0Cmp4
    · exact adverseNextS26D0Cmp5
    · exact adverseNextS26D0Cmp6
    · exact adverseNextS26D0Cmp7

theorem adverseNextS26ActualEvent : nativeEvent budgetTape (7/5) (controlPenalty savedCref uniformQuoteError unitRoleUnused .next)
    (taskReward true (2/5) (1/2)) adverseNextS26Before = adverseNextEvent26 := by
  have hs0 := native_select_existing_step budgetTape (7/5) (controlPenalty savedCref uniformQuoteError unitRoleUnused .next) adverseNextS26Before 8 [] (.query 1)
    (by decide) (by decide) adverseNextS26Choice0
  have hnew := native_select_new_step budgetTape (7/5) (controlPenalty savedCref uniformQuoteError unitRoleUnused .next) adverseNextS26Before 7 [.query 1]
    [.hydeRetriever 2] (.hydeRetriever 2) (by decide) (by decide) (by decide) (by decide)
  have hs : nativeSelect budgetTape (7/5) (controlPenalty savedCref uniformQuoteError unitRoleUnused .next) adverseNextS26Before 9 [] = [.query 1,.hydeRetriever 2] := by
    rw [hs0]
    change nativeSelect budgetTape (7/5) (controlPenalty savedCref uniformQuoteError unitRoleUnused .next) adverseNextS26Before 8 [.query 1] = _
    rw [hnew] <;> rfl
  have hr : repairedRollout budgetTape adverseNextS26Before 9 [.query 1,.hydeRetriever 2] = [.query 1,.hydeRetriever 2,.selection 0,.width 0,.stop,.reranker 0,.topm 2,.context 0,.answer 2] := by decide
  simp only [nativeEvent,hs,hr]
  rfl

end AgentUCT32MConcrete
