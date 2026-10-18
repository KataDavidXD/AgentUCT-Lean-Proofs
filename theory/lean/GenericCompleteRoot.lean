import NativeChoiceTools
set_option autoImplicit false
set_option maxRecDepth 16384
set_option maxHeartbeats 16000000
noncomputable section
namespace AgentUCT32MConcrete
open AgentUCT32MContinuation AgentUCTSavedBudget AgentUCTObservability
  AgentUCTPhysicalDiagnostic AgentUCTNativeBudget AgentUCTPanelAllocation
  AgentUCTNativeRepair AgentUCTNativeRefinement AgentUCTPaper AgentUCTRealIndex

theorem task_reward_in_unit (adverse : Bool) (terminal : List Act) :
    0 ≤ taskReward adverse (2/5) (1/2) terminal ∧ taskReward adverse (2/5) (1/2) terminal ≤ 1 := by
  unfold taskReward
  split_ifs <;> cases adverse <;> norm_num

theorem complete_root_from_physical_gap (before : List (TreeEvaluation Act))
    (hRewards : ∀ e ∈ before,0 ≤ e.reward ∧ e.reward ≤ 1)
    (hparent : rawVisits before [] ≤ 256)
    (hvisits : ∀ q : Fin 8,1 ≤ rawVisits before [.query q])
    (hchosen : pathSuffix (pathHistoryCache before) (safeCompletion [.query 1]) = [])
    (hother : ∀ q : Fin 8,q ≠ 1 →
      pathQuote .complete (pathHistoryCache before) (completedPrice unitRoleUnused)
        (safeCompletion [.query q]) = (154035641216/1953125:ℝ)) :
    nativeFirstChoice (indexScore (7/5) (controlPenalty savedCref uniformQuoteError unitRoleUnused .complete)
      before []) before [] = .query 1 := by
  let score := indexScore (7/5) (controlPenalty savedCref uniformQuoteError unitRoleUnused .complete) before []
  have hzero : controlPenalty savedCref uniformQuoteError unitRoleUnused .complete before [] (.query 1) = 0 :=
    control_penalty_empty_suffix _ _ _ _ _ _ (by simpa using hchosen)
  have hneg (q : Fin 8) (hq : q ≠ 1) : score (.query q) < score (.query 1) := by
    have hh := completed_control_penalty_error .complete savedCref uniformQuoteError
      (by norm_num [savedCref]) (by norm_num [uniformQuoteError]) (by norm_num [uniformQuoteError])
      before [] (.query q) (by decide) (by simp [available,rootOrder])
    rw [List.nil_append,hother q hq] at hh
    have hgap : (0:ℝ)+5 < controlPenalty savedCref uniformQuoteError unitRoleUnused .complete before [] (.query q) := by
      have hlo := (abs_le.mp hh).1
      have hc : (5:ℝ) < (300/savedCref)*(154035641216/1953125)-(3000/savedCref)*uniformQuoteError := by
        norm_num [savedCref,uniformQuoteError]
      linarith
    have hqa := (replayBackup_mean_mem_unit before hRewards [.query 1]).1
    have hqb := (replayBackup_mean_mem_unit before hRewards [.query q]).2
    have hi := uniform_strict_dominance_from_penalty_gap _ _ 0
      (controlPenalty savedCref uniformQuoteError unitRoleUnused .complete before [] (.query q))
      (rawVisits before []) (rawVisits before [.query 1]) (rawVisits before [.query q])
      hqa hqb hparent (hvisits q) hgap
    simpa only [score,indexScore,List.nil_append,hzero] using hi
  apply visited_choice_from_ordered_certificate score before [] [.query 0]
    [.query 2,.query 3,.query 4,.query 5,.query 6,.query 7] (.query 1) (by decide)
  · intro a ha
    have ho : orderedLegalAvailable [] = [.query 0,.query 1,.query 2,.query 3,.query 4,.query 5,.query 6,.query 7] := by decide
    rw [ho] at ha
    simp only [List.mem_cons,List.not_mem_nil,or_false] at ha
    rcases ha with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> simpa using hvisits _
  · intro a ha
    have ha : a = .query 0 := by simpa using ha
    subst a
    exact hneg 0 (by decide)
  · intro a ha
    simp only [List.mem_cons,List.not_mem_nil,or_false] at ha
    rcases ha with rfl | rfl | rfl | rfl | rfl | rfl <;> exact (hneg _ (by decide)).le

theorem zero_quote_index_interval (mode : ForecastMode) (before : List (TreeEvaluation Act))
    (p : List Act) (a : Act) (parent count : ℕ) (total blo bhi : ℝ)
    (hstat : replayBackup before emptyStatistics (p++[a]) = ⟨count,total⟩)
    (hparent : rawVisits before p = parent)
    (hs : pathSuffix (pathHistoryCache before) (safeCompletion (p++[a])) = [])
    (hb : blo ≤ treeBonus (7/5) parent count ∧ treeBonus (7/5) parent count ≤ bhi) :
    total/count+blo ≤ indexScore (7/5) (controlPenalty savedCref uniformQuoteError unitRoleUnused mode) before p a ∧
    indexScore (7/5) (controlPenalty savedCref uniformQuoteError unitRoleUnused mode) before p a ≤ total/count+bhi := by
  have hn : rawVisits before (p++[a]) = count := by unfold rawVisits; rw [hstat]
  have hp := control_penalty_empty_suffix mode savedCref uniformQuoteError before p a hs
  simp only [indexScore,hstat,hparent,hn,hp,BackupStat.mean,treeIndex,sub_zero]
  exact ⟨add_le_add_left hb.1 _,add_le_add_left hb.2 _⟩

end AgentUCT32MConcrete
