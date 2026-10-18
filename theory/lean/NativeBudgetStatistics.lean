import NativeBudgetResolver




set_option autoImplicit false
set_option maxRecDepth 16384
set_option maxHeartbeats 4000000
set_option linter.constructorNameAsVariable false
noncomputable section
namespace AgentUCTNativeBudget
open AgentUCTPanelAllocation AgentUCTNativeRepair AgentUCTNativeRefinement AgentUCTPaper

theorem initial_root_stat_exact (reward : List Act → ℝ) (q : Fin 8) :
    replayBackup (initialization reward) emptyStatistics [.query q] = ⟨1,reward (seedPath q)⟩ := by
  obtain ⟨hn,hm⟩ := initialization_child_stats reward q
  have hs : (replayBackup (initialization reward) emptyStatistics [.query q]).rewardSum = reward (seedPath q) := by
    simpa only [BackupStat.mean,hn,Nat.cast_one,div_one] using hm
  change BackupStat.mk (replayBackup (initialization reward) emptyStatistics [.query q]).visits
    (replayBackup (initialization reward) emptyStatistics [.query q]).rewardSum = _
  rw [hn,hs]

theorem a9_root_child_statistics (reward : List Act → ℝ) (q : Fin 8) :
    replayBackup (aNine reward) emptyStatistics [.query q] =
      if q = hyde then ⟨2,reward (seedPath q)+reward aCold⟩ else ⟨1,reward (seedPath q)⟩ := by
  rw [aNine,replayBackup_append_one]
  fin_cases q <;> simp +decide [backupEvent,initial_root_stat_exact,aColdEvent,routeEvent,aCold,hyde]

theorem a10_root_child_statistics (reward : List Act → ℝ) (q : Fin 8) :
    replayBackup (aTen reward) emptyStatistics [.query q] =
      if q = hyde then ⟨3,2*reward (seedPath q)+reward aCold⟩ else ⟨1,reward (seedPath q)⟩ := by
  rw [aTen,replayBackup_append_one]
  fin_cases q <;> simp +decide [backupEvent,a9_root_child_statistics,aWarmEvent,routeEvent,aCold,hyde,seedPath,seedRetriever]
  ring

theorem a11_root_child_statistics (reward : List Act → ℝ) (q : Fin 8) :
    replayBackup (aEleven reward) emptyStatistics [.query q] =
      if q = hyde then ⟨4,2*reward (seedPath q)+reward aCold+reward aCross⟩ else ⟨1,reward (seedPath q)⟩ := by
  rw [aEleven,replayBackup_append_one]
  fin_cases q <;> simp +decide [backupEvent,a10_root_child_statistics,aCrossEvent,routeEvent,aCross,hyde]

theorem b9_root_child_statistics (reward : List Act → ℝ) (q : Fin 8) :
    replayBackup (bNine reward) emptyStatistics [.query q] =
      if q = branchB then ⟨2,reward (seedPath q)+reward bCold⟩ else ⟨1,reward (seedPath q)⟩ := by
  rw [bNine,replayBackup_append_one]
  fin_cases q <;> simp +decide [backupEvent,initial_root_stat_exact,bColdEvent,routeEvent,bCold,branchB]

theorem b10_root_child_statistics (reward : List Act → ℝ) (q : Fin 8) :
    replayBackup (bTen reward) emptyStatistics [.query q] =
      if q = hyde then ⟨2,reward (seedPath q)+reward aCold⟩ else
      if q = branchB then ⟨2,reward (seedPath q)+reward bCold⟩ else ⟨1,reward (seedPath q)⟩ := by
  rw [bTen,replayBackup_append_one]
  fin_cases q <;> simp +decide [backupEvent,b9_root_child_statistics,aColdEvent,routeEvent,aCold,hyde,branchB]

theorem warm10_raw_visit_mean (reward : List Act → ℝ) :
    rawVisits (aTen reward) [.query hyde] = 3 ∧
    (replayBackup (aTen reward) emptyStatistics [.query hyde]).mean =
      (2*reward aWarm+reward aCold)/3 ∧
    rawVisits (aTen reward) [.query hyde,.hydeRetriever 0] = 1 ∧
    (replayBackup (aTen reward) emptyStatistics [.query hyde,.hydeRetriever 0]).mean = reward aWarm := by
  simp +decide [rawVisits,a10_root_child_statistics,BackupStat.mean,aWarm,aTen,aNine,
    initialization,finRange8_explicit,seedEvent,replayBackup,backupEvent,emptyStatistics,
    aColdEvent,aWarmEvent,routeEvent,hyde,seedPath,seedRetriever,aCold]
  ring

theorem warm10_tree_child_is_new (reward : List Act → ℝ) :
    [.query hyde,.hydeRetriever 0] ∉ expandedNodes (aNine reward) := by
  simp +decide [expandedNodes,aNine,initialization,seedEvent,finRange8_explicit,aColdEvent,routeEvent,hyde]

theorem warm10_child_inserted_after_replay (reward : List Act → ℝ) :
    [.query hyde,.hydeRetriever 0] ∈ expandedNodes (aTen reward) := by
  rw [aTen,expanded_nodes_append]
  simp [aWarmEvent,routeEvent]

theorem actual_resource_histories_root_counts (reward : List Act → ℝ) :
    rawVisits (aNine reward) [] = 9 ∧ rawVisits (aTen reward) [] = 10 ∧
    rawVisits (aEleven reward) [] = 11 ∧ rawVisits (bNine reward) [] = 9 ∧ rawVisits (bTen reward) [] = 10 := by
  simp only [rawVisits,replayBackup_root_visits]
  exact resource_history_lengths reward

end AgentUCTNativeBudget
