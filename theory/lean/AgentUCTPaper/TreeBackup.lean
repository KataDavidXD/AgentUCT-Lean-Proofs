import AgentUCT

/-! # Operational reward backup

An event backs up its terminal Score through the prefixes of the actual expanded tree node.
The terminal rollout may be deeper. Replay is an operational left fold of these updates.
No statistical independence, concentration, or regret assumption enters this module.
-/

set_option autoImplicit false

noncomputable section

namespace AgentUCTPaper

structure BackupStat where
  visits : ℕ
  rewardSum : ℝ
  deriving DecidableEq

structure TreeEvaluation (Action : Type*) where
  expanded : List Action
  terminal : List Action
  reward : ℝ
  bill : ℝ
  expanded_is_prefix : expanded <+: terminal

abbrev TreeStatistics (Action : Type*) := List Action → BackupStat

def emptyStatistics {Action : Type*} : TreeStatistics Action := fun _ ↦ ⟨0, 0⟩

def BackupStat.mean (stat : BackupStat) : ℝ := stat.rewardSum / stat.visits

variable {Action : Type*} [DecidableEq Action]

/-- The loop visits precisely the expanded node and its existing ancestors, once each. -/
def backupEvent (stats : TreeStatistics Action) (event : TreeEvaluation Action) :
    TreeStatistics Action := fun p ↦
  if p <+: event.expanded then
    ⟨(stats p).visits + 1, (stats p).rewardSum + event.reward⟩
  else stats p

def replayBackup (events : List (TreeEvaluation Action))
    (initial : TreeStatistics Action := emptyStatistics) : TreeStatistics Action :=
  events.foldl backupEvent initial

def backedCount (events : List (TreeEvaluation Action)) (p : List Action) : ℕ :=
  (events.filter fun event ↦ decide (p <+: event.expanded)).length

def backedReturn (events : List (TreeEvaluation Action)) (p : List Action) : ℝ :=
  (events.map fun event ↦ if p <+: event.expanded then event.reward else 0).sum

/-- Committing the next complete result is the same update used by the search loop. -/
theorem replayBackup_append_one (events : List (TreeEvaluation Action))
    (event : TreeEvaluation Action) (initial : TreeStatistics Action) :
    replayBackup (events ++ [event]) initial = backupEvent (replayBackup events initial) event := by
  simp [replayBackup, List.foldl_append]

/-- Counts are derived from repeated updates, rather than postulated observation counts. -/
theorem replayBackup_visits (events : List (TreeEvaluation Action))
    (initial : TreeStatistics Action) (p : List Action) :
    (replayBackup events initial p).visits = (initial p).visits + backedCount events p := by
  induction events generalizing initial with
  | nil => simp [replayBackup, backedCount]
  | cons event events ih =>
    change (replayBackup events (backupEvent initial event) p).visits = _
    rw [ih]
    by_cases h : p <+: event.expanded
    · simp [backupEvent, backedCount, h]
      omega
    · simp [backupEvent, backedCount, h]

/-- The operational reward sum is exactly the sum of terminal Scores passing through the node. -/
theorem replayBackup_rewardSum (events : List (TreeEvaluation Action))
    (initial : TreeStatistics Action) (p : List Action) :
    (replayBackup events initial p).rewardSum = (initial p).rewardSum + backedReturn events p := by
  induction events generalizing initial with
  | nil => simp [replayBackup, backedReturn]
  | cons event events ih =>
    change (replayBackup events (backupEvent initial event) p).rewardSum = _
    rw [ih]
    by_cases h : p <+: event.expanded
    · simp [backupEvent, backedReturn, h]
      ring
    · simp [backupEvent, backedReturn, h]

/-- Starting from zero, Q is the actual selected-return mean, including Q=0 when unvisited. -/
theorem replayBackup_mean (events : List (TreeEvaluation Action)) (p : List Action) :
    (replayBackup events emptyStatistics p).mean =
      backedReturn events p / backedCount events p := by
  simp [BackupStat.mean, replayBackup_visits, replayBackup_rewardSum, emptyStatistics]

/-- Every complete evaluation contributes once to the root, including a cache hit. -/
theorem replayBackup_root_visits (events : List (TreeEvaluation Action)) :
    (replayBackup events emptyStatistics []).visits = events.length := by
  simp [replayBackup_visits, emptyStatistics, backedCount]

/-- A node outside the expanded path receives no reward or visit update. -/
theorem backupEvent_off_path (stats : TreeStatistics Action) (event : TreeEvaluation Action)
    (p : List Action) (h : ¬ p <+: event.expanded) : backupEvent stats event p = stats p := by
  simp [backupEvent, h]

/-- Changing only the physical bill cannot change raw reward backup. -/
theorem backupEvent_bill_irrelevant (stats : TreeStatistics Action) (event : TreeEvaluation Action)
    (bill : ℝ) : backupEvent stats { event with bill := bill } = backupEvent stats event := by
  rfl

/-- A node reward sum stays between zero and its visit count. -/
theorem backupEvent_bounded (stats : TreeStatistics Action) (event : TreeEvaluation Action)
    (hStats : ∀ p, 0 ≤ (stats p).rewardSum ∧ (stats p).rewardSum ≤ (stats p).visits)
    (hReward : 0 ≤ event.reward ∧ event.reward ≤ 1) :
    ∀ p, 0 ≤ (backupEvent stats event p).rewardSum ∧
      (backupEvent stats event p).rewardSum ≤ (backupEvent stats event p).visits := by
  intro p
  by_cases h : p <+: event.expanded
  · simp only [backupEvent, if_pos h, Nat.cast_add, Nat.cast_one]
    obtain ⟨h0, h1⟩ := hStats p
    constructor <;> linarith [hReward.1, hReward.2]
  · simpa [backupEvent, h] using hStats p

theorem replayBackup_bounded (events : List (TreeEvaluation Action))
    (initial : TreeStatistics Action)
    (hStats : ∀ p, 0 ≤ (initial p).rewardSum ∧ (initial p).rewardSum ≤ (initial p).visits)
    (hRewards : ∀ event ∈ events, 0 ≤ event.reward ∧ event.reward ≤ 1) :
    ∀ p, 0 ≤ (replayBackup events initial p).rewardSum ∧
      (replayBackup events initial p).rewardSum ≤ (replayBackup events initial p).visits := by
  induction events generalizing initial with
  | nil => simpa [replayBackup] using hStats
  | cons event events ih =>
    exact ih (backupEvent initial event)
      (backupEvent_bounded initial event hStats (hRewards event (by simp)))
      (fun e he ↦ hRewards e (by simp [he]))

theorem replayBackup_mean_mem_unit (events : List (TreeEvaluation Action))
    (hRewards : ∀ event ∈ events, 0 ≤ event.reward ∧ event.reward ≤ 1) (p : List Action) :
    (replayBackup events emptyStatistics p).mean ∈ Set.Icc (0 : ℝ) 1 := by
  obtain ⟨h0, h1⟩ := replayBackup_bounded events emptyStatistics
    (fun _ ↦ by simp [emptyStatistics]) hRewards p
  change 0 ≤ _ / _ ∧ _ / _ ≤ 1
  constructor
  · exact div_nonneg h0 (Nat.cast_nonneg _)
  · by_cases hN : (replayBackup events emptyStatistics p).visits = 0
    · simp [hN]
    · exact (div_le_one (Nat.cast_pos.mpr (Nat.pos_of_ne_zero hN))).mpr h1

end AgentUCTPaper
