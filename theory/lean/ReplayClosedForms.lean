import PanelUnits





set_option autoImplicit false
set_option maxRecDepth 16384
noncomputable section
namespace AgentUCTRealIndex
open AgentUCTPaper AgentUCTNativeRepair AgentUCTNativeRefinement Finset

variable {Action : Type*} [DecidableEq Action]

def backedEvents (events : List (TreeEvaluation Action)) (p : List Action) :
    List (TreeEvaluation Action) :=
  events.filter fun e => decide (p <+: e.expanded)

theorem backedReturn_filtered_sum (events : List (TreeEvaluation Action)) (p : List Action) :
    backedReturn events p = ((backedEvents events p).map TreeEvaluation.reward).sum := by
  induction events with
  | nil => simp [backedReturn, backedEvents]
  | cons e es ih =>
      by_cases h : p <+: e.expanded
      · simp [backedReturn, backedEvents, h] at ih ⊢
        exact ih
      · simpa [backedReturn, backedEvents, h] using ih

theorem replayBackup_closed_form (events : List (TreeEvaluation Action))
    (initial : TreeStatistics Action) (p : List Action) :
    replayBackup events initial p =
      ⟨(initial p).visits + (backedEvents events p).length,
        (initial p).rewardSum + ((backedEvents events p).map TreeEvaluation.reward).sum⟩ := by
  change BackupStat.mk (replayBackup events initial p).visits
    (replayBackup events initial p).rewardSum = _
  rw [replayBackup_visits, replayBackup_rewardSum, backedReturn_filtered_sum]
  rfl

theorem replayBackup_empty_closed_form (events : List (TreeEvaluation Action))
    (p : List Action) :
    replayBackup events emptyStatistics p =
      ⟨(backedEvents events p).length, ((backedEvents events p).map TreeEvaluation.reward).sum⟩ := by
  simpa [emptyStatistics] using replayBackup_closed_form events emptyStatistics p

theorem replayBackup_filtered_mean (events : List (TreeEvaluation Action)) (p : List Action) :
    (replayBackup events emptyStatistics p).mean =
      ((backedEvents events p).map TreeEvaluation.reward).sum / (backedEvents events p).length := by
  rw [replayBackup_empty_closed_form]
  rfl

theorem backedEvents_append (left right : List (TreeEvaluation Action)) (p : List Action) :
    backedEvents (left ++ right) p = backedEvents left p ++ backedEvents right p := by
  simp [backedEvents]

theorem pathHistoryCache_mem (events : List (TreeEvaluation Act)) (p : List Act) :
    p ∈ pathHistoryCache events ↔ ∃ e ∈ events, p ∈ executionPrefixes e.terminal := by
  induction events using List.reverseRecOn with
  | nil => simp [pathHistoryCache]
  | append_singleton es e ih =>
      simp only [pathHistoryCache, List.foldl_append, List.foldl_cons, List.foldl_nil]
      change p ∈ pathHistoryCache es ∪ executionPrefixes e.terminal ↔ _
      simp only [Finset.mem_union, ih, List.mem_append, List.mem_singleton]
      aesop

theorem pathHistoryCache_biUnion (events : List (TreeEvaluation Act)) :
    pathHistoryCache events =
      (events.map TreeEvaluation.terminal).toFinset.biUnion executionPrefixes := by
  ext p
  simp [pathHistoryCache_mem]

theorem pathHistoryCache_append (left right : List (TreeEvaluation Act)) :
    pathHistoryCache (left ++ right) = pathHistoryCache left ∪ pathHistoryCache right := by
  ext p
  simp only [pathHistoryCache_mem, List.mem_append, Finset.mem_union]
  aesop

theorem panel_actual_bill_terminal_union {Qid : Type*} [DecidableEq Qid]
    (qids : Finset Qid) (prices : Qid × List Act → ℝ)
    (events : List (TreeEvaluation Act)) :
    (replayPanel qids prices events).totalPaid =
      ∑ qid ∈ qids,
        ∑ p ∈ (events.map TreeEvaluation.terminal).toFinset.biUnion executionPrefixes,
          prices (qid,p) := by
  rw [replay_panel_actual_bill_sum, pathHistoryCache_biUnion]

theorem replayPanel_statistics_filtered {Qid : Type*} [DecidableEq Qid]
    (qids : Finset Qid) (prices : Qid × List Act → ℝ)
    (events : List (TreeEvaluation Act)) (p : List Act) :
    (replayPanel qids prices events).stats p =
      ⟨(backedEvents events p).length, ((backedEvents events p).map TreeEvaluation.reward).sum⟩ := by
  rw [replayPanel, replayMetered_stats]
  exact replayBackup_empty_closed_form events p

end AgentUCTRealIndex
