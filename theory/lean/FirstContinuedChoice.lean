import ConcreteProposals
import ReplayClosedForms
import OrderedIndexCertificate
import UniformIndexDominance
import EqualBonusCancellation
import NativeChoiceTools
set_option autoImplicit false
set_option maxRecDepth 16384
set_option maxHeartbeats 16000000
noncomputable section
namespace AgentUCT32MConcrete
open AgentUCT32MContinuation AgentUCTSavedBudget AgentUCTObservability
  AgentUCTPhysicalDiagnostic AgentUCTNativeBudget AgentUCTPanelAllocation
  AgentUCTNativeRepair AgentUCTNativeRefinement AgentUCTPaper AgentUCTRealIndex

def favorableCompleteH11 := favorableCompleteProposal.take 11

theorem favorable_complete_11_root_stats (q : Fin 8) :
    replayBackup favorableCompleteH11 emptyStatistics [.query q] =
      ⟨if q = 1 then 4 else 1,if q = 1 then (1/2:ℝ) else if q = 5 then 2/5 else 0⟩ := by
  rw [replayBackup_empty_closed_form]
  fin_cases q <;> simp +decide [backedEvents,favorableCompleteH11,favorableCompleteProposal,favorableCompleteEvent1,favorableCompleteEvent2,favorableCompleteEvent3,favorableCompleteEvent4,favorableCompleteEvent5,favorableCompleteEvent6,favorableCompleteEvent7,favorableCompleteEvent8,favorableCompleteEvent9,favorableCompleteEvent10,favorableCompleteEvent11,taskReward,aCold,bCold,aWarm,aCross,
    leaf,fullLeaf,seedPath,hyde,branchB]

theorem favorable_complete_11_root_parent_visits :
    rawVisits favorableCompleteH11 [] = 11 := by decide

theorem favorable_complete_11_quote_0 :
    pathQuote .complete (pathHistoryCache favorableCompleteH11) (completedPrice unitRoleUnused)
      (safeCompletion [.query 0]) = (154035641216/1953125:ℝ) := by
  have hs : pathSuffix (pathHistoryCache favorableCompleteH11) (safeCompletion [.query 0]) =
    [[.query 0,.normalRetriever 0,.selection 0,.width 1],[.query 0,.normalRetriever 0,.selection 0,.width 1,.stop],[.query 0,.normalRetriever 0,.selection 0,.width 1,.stop,.reranker 1],[.query 0,.normalRetriever 0,.selection 0,.width 1,.stop,.reranker 1,.topm 2],[.query 0,.normalRetriever 0,.selection 0,.width 1,.stop,.reranker 1,.topm 2,.context 0],[.query 0,.normalRetriever 0,.selection 0,.width 1,.stop,.reranker 1,.topm 2,.context 0,.answer 2]] := by decide
  simp only [pathQuote,hs,List.map_cons,List.map_nil,List.sum_cons,List.sum_nil,completed_price_rational_projection]
  norm_num [rationalActionPrice]

theorem favorable_complete_11_quote_1 :
    pathQuote .complete (pathHistoryCache favorableCompleteH11) (completedPrice unitRoleUnused)
      (safeCompletion [.query 1]) = (0/1:ℝ) := by
  have hs : pathSuffix (pathHistoryCache favorableCompleteH11) (safeCompletion [.query 1]) =
    [] := by decide
  simp only [pathQuote,hs,List.map_cons,List.map_nil,List.sum_cons,List.sum_nil,completed_price_rational_projection]
  norm_num [rationalActionPrice]

theorem favorable_complete_11_quote_2 :
    pathQuote .complete (pathHistoryCache favorableCompleteH11) (completedPrice unitRoleUnused)
      (safeCompletion [.query 2]) = (154035641216/1953125:ℝ) := by
  have hs : pathSuffix (pathHistoryCache favorableCompleteH11) (safeCompletion [.query 2]) =
    [[.query 2,.normalRetriever 0,.selection 0,.width 1],[.query 2,.normalRetriever 0,.selection 0,.width 1,.stop],[.query 2,.normalRetriever 0,.selection 0,.width 1,.stop,.reranker 1],[.query 2,.normalRetriever 0,.selection 0,.width 1,.stop,.reranker 1,.topm 2],[.query 2,.normalRetriever 0,.selection 0,.width 1,.stop,.reranker 1,.topm 2,.context 0],[.query 2,.normalRetriever 0,.selection 0,.width 1,.stop,.reranker 1,.topm 2,.context 0,.answer 2]] := by decide
  simp only [pathQuote,hs,List.map_cons,List.map_nil,List.sum_cons,List.sum_nil,completed_price_rational_projection]
  norm_num [rationalActionPrice]

theorem favorable_complete_11_quote_3 :
    pathQuote .complete (pathHistoryCache favorableCompleteH11) (completedPrice unitRoleUnused)
      (safeCompletion [.query 3]) = (154035641216/1953125:ℝ) := by
  have hs : pathSuffix (pathHistoryCache favorableCompleteH11) (safeCompletion [.query 3]) =
    [[.query 3,.normalRetriever 0,.selection 0,.width 1],[.query 3,.normalRetriever 0,.selection 0,.width 1,.stop],[.query 3,.normalRetriever 0,.selection 0,.width 1,.stop,.reranker 1],[.query 3,.normalRetriever 0,.selection 0,.width 1,.stop,.reranker 1,.topm 2],[.query 3,.normalRetriever 0,.selection 0,.width 1,.stop,.reranker 1,.topm 2,.context 0],[.query 3,.normalRetriever 0,.selection 0,.width 1,.stop,.reranker 1,.topm 2,.context 0,.answer 2]] := by decide
  simp only [pathQuote,hs,List.map_cons,List.map_nil,List.sum_cons,List.sum_nil,completed_price_rational_projection]
  norm_num [rationalActionPrice]

theorem favorable_complete_11_quote_4 :
    pathQuote .complete (pathHistoryCache favorableCompleteH11) (completedPrice unitRoleUnused)
      (safeCompletion [.query 4]) = (154035641216/1953125:ℝ) := by
  have hs : pathSuffix (pathHistoryCache favorableCompleteH11) (safeCompletion [.query 4]) =
    [[.query 4,.normalRetriever 0,.selection 0,.width 1],[.query 4,.normalRetriever 0,.selection 0,.width 1,.stop],[.query 4,.normalRetriever 0,.selection 0,.width 1,.stop,.reranker 1],[.query 4,.normalRetriever 0,.selection 0,.width 1,.stop,.reranker 1,.topm 2],[.query 4,.normalRetriever 0,.selection 0,.width 1,.stop,.reranker 1,.topm 2,.context 0],[.query 4,.normalRetriever 0,.selection 0,.width 1,.stop,.reranker 1,.topm 2,.context 0,.answer 2]] := by decide
  simp only [pathQuote,hs,List.map_cons,List.map_nil,List.sum_cons,List.sum_nil,completed_price_rational_projection]
  norm_num [rationalActionPrice]

theorem favorable_complete_11_quote_5 :
    pathQuote .complete (pathHistoryCache favorableCompleteH11) (completedPrice unitRoleUnused)
      (safeCompletion [.query 5]) = (154035641216/1953125:ℝ) := by
  have hs : pathSuffix (pathHistoryCache favorableCompleteH11) (safeCompletion [.query 5]) =
    [[.query 5,.normalRetriever 0,.selection 0,.width 1],[.query 5,.normalRetriever 0,.selection 0,.width 1,.stop],[.query 5,.normalRetriever 0,.selection 0,.width 1,.stop,.reranker 1],[.query 5,.normalRetriever 0,.selection 0,.width 1,.stop,.reranker 1,.topm 2],[.query 5,.normalRetriever 0,.selection 0,.width 1,.stop,.reranker 1,.topm 2,.context 0],[.query 5,.normalRetriever 0,.selection 0,.width 1,.stop,.reranker 1,.topm 2,.context 0,.answer 2]] := by decide
  simp only [pathQuote,hs,List.map_cons,List.map_nil,List.sum_cons,List.sum_nil,completed_price_rational_projection]
  norm_num [rationalActionPrice]

theorem favorable_complete_11_quote_6 :
    pathQuote .complete (pathHistoryCache favorableCompleteH11) (completedPrice unitRoleUnused)
      (safeCompletion [.query 6]) = (154035641216/1953125:ℝ) := by
  have hs : pathSuffix (pathHistoryCache favorableCompleteH11) (safeCompletion [.query 6]) =
    [[.query 6,.normalRetriever 0,.selection 0,.width 1],[.query 6,.normalRetriever 0,.selection 0,.width 1,.stop],[.query 6,.normalRetriever 0,.selection 0,.width 1,.stop,.reranker 1],[.query 6,.normalRetriever 0,.selection 0,.width 1,.stop,.reranker 1,.topm 2],[.query 6,.normalRetriever 0,.selection 0,.width 1,.stop,.reranker 1,.topm 2,.context 0],[.query 6,.normalRetriever 0,.selection 0,.width 1,.stop,.reranker 1,.topm 2,.context 0,.answer 2]] := by decide
  simp only [pathQuote,hs,List.map_cons,List.map_nil,List.sum_cons,List.sum_nil,completed_price_rational_projection]
  norm_num [rationalActionPrice]

theorem favorable_complete_11_quote_7 :
    pathQuote .complete (pathHistoryCache favorableCompleteH11) (completedPrice unitRoleUnused)
      (safeCompletion [.query 7]) = (154035641216/1953125:ℝ) := by
  have hs : pathSuffix (pathHistoryCache favorableCompleteH11) (safeCompletion [.query 7]) =
    [[.query 7,.normalRetriever 0,.selection 0,.width 1],[.query 7,.normalRetriever 0,.selection 0,.width 1,.stop],[.query 7,.normalRetriever 0,.selection 0,.width 1,.stop,.reranker 1],[.query 7,.normalRetriever 0,.selection 0,.width 1,.stop,.reranker 1,.topm 2],[.query 7,.normalRetriever 0,.selection 0,.width 1,.stop,.reranker 1,.topm 2,.context 0],[.query 7,.normalRetriever 0,.selection 0,.width 1,.stop,.reranker 1,.topm 2,.context 0,.answer 2]] := by decide
  simp only [pathQuote,hs,List.map_cons,List.map_nil,List.sum_cons,List.sum_nil,completed_price_rational_projection]
  norm_num [rationalActionPrice]


theorem favorable_complete_12_root_selected :
    nativeFirstChoice (indexScore (7/5) (controlPenalty savedCref uniformQuoteError unitRoleUnused .complete)
      favorableCompleteH11 []) favorableCompleteH11 [] = .query 1 := by
  have h1 := actual_index_interval .complete savedCref uniformQuoteError
    (by norm_num [savedCref]) (by norm_num [uniformQuoteError]) (by norm_num [uniformQuoteError])
    favorableCompleteH11 [] (.query 1) (by decide) (by decide) 11 4 (1/2) 0 0 4
    (by simpa using favorable_complete_11_root_stats 1) favorable_complete_11_root_parent_visits
    (by simpa using favorable_complete_11_quote_1) (bonus_7_5_bound4 11 4 (by norm_num) (by norm_num))
  have h1pos : 0 ≤ indexScore (7/5) (controlPenalty savedCref uniformQuoteError unitRoleUnused .complete)
      favorableCompleteH11 [] (.query 1) := by
    exact le_trans (by norm_num [savedCref,uniformQuoteError]) h1.1
  have hneg (q : Fin 8) (hq : q ≠ 1) :
      indexScore (7/5) (controlPenalty savedCref uniformQuoteError unitRoleUnused .complete)
        favorableCompleteH11 [] (.query q) < 0 := by
    fin_cases q
    · have hh := actual_index_interval .complete savedCref uniformQuoteError
        (by norm_num [savedCref]) (by norm_num [uniformQuoteError]) (by norm_num [uniformQuoteError])
        favorableCompleteH11 [] (.query 0) (by decide) (by decide) 11 1 0 (154035641216/1953125) 0 4
        (by simpa using favorable_complete_11_root_stats 0) favorable_complete_11_root_parent_visits
        favorable_complete_11_quote_0 (bonus_7_5_bound4 11 1 (by norm_num) (by norm_num))
      exact lt_of_le_of_lt hh.2 (by norm_num [savedCref,uniformQuoteError])
    · exact (hq rfl).elim
    · have hh := actual_index_interval .complete savedCref uniformQuoteError
        (by norm_num [savedCref]) (by norm_num [uniformQuoteError]) (by norm_num [uniformQuoteError])
        favorableCompleteH11 [] (.query 2) (by decide) (by decide) 11 1 0 (154035641216/1953125) 0 4
        (by simpa using favorable_complete_11_root_stats 2) favorable_complete_11_root_parent_visits
        favorable_complete_11_quote_2 (bonus_7_5_bound4 11 1 (by norm_num) (by norm_num))
      exact lt_of_le_of_lt hh.2 (by norm_num [savedCref,uniformQuoteError])
    · have hh := actual_index_interval .complete savedCref uniformQuoteError
        (by norm_num [savedCref]) (by norm_num [uniformQuoteError]) (by norm_num [uniformQuoteError])
        favorableCompleteH11 [] (.query 3) (by decide) (by decide) 11 1 0 (154035641216/1953125) 0 4
        (by simpa using favorable_complete_11_root_stats 3) favorable_complete_11_root_parent_visits
        favorable_complete_11_quote_3 (bonus_7_5_bound4 11 1 (by norm_num) (by norm_num))
      exact lt_of_le_of_lt hh.2 (by norm_num [savedCref,uniformQuoteError])
    · have hh := actual_index_interval .complete savedCref uniformQuoteError
        (by norm_num [savedCref]) (by norm_num [uniformQuoteError]) (by norm_num [uniformQuoteError])
        favorableCompleteH11 [] (.query 4) (by decide) (by decide) 11 1 0 (154035641216/1953125) 0 4
        (by simpa using favorable_complete_11_root_stats 4) favorable_complete_11_root_parent_visits
        favorable_complete_11_quote_4 (bonus_7_5_bound4 11 1 (by norm_num) (by norm_num))
      exact lt_of_le_of_lt hh.2 (by norm_num [savedCref,uniformQuoteError])
    · have hh := actual_index_interval .complete savedCref uniformQuoteError
        (by norm_num [savedCref]) (by norm_num [uniformQuoteError]) (by norm_num [uniformQuoteError])
        favorableCompleteH11 [] (.query 5) (by decide) (by decide) 11 1 (2/5) (154035641216/1953125) 0 4
        (by simpa using favorable_complete_11_root_stats 5) favorable_complete_11_root_parent_visits
        favorable_complete_11_quote_5 (bonus_7_5_bound4 11 1 (by norm_num) (by norm_num))
      exact lt_of_le_of_lt hh.2 (by norm_num [savedCref,uniformQuoteError])
    · have hh := actual_index_interval .complete savedCref uniformQuoteError
        (by norm_num [savedCref]) (by norm_num [uniformQuoteError]) (by norm_num [uniformQuoteError])
        favorableCompleteH11 [] (.query 6) (by decide) (by decide) 11 1 0 (154035641216/1953125) 0 4
        (by simpa using favorable_complete_11_root_stats 6) favorable_complete_11_root_parent_visits
        favorable_complete_11_quote_6 (bonus_7_5_bound4 11 1 (by norm_num) (by norm_num))
      exact lt_of_le_of_lt hh.2 (by norm_num [savedCref,uniformQuoteError])
    · have hh := actual_index_interval .complete savedCref uniformQuoteError
        (by norm_num [savedCref]) (by norm_num [uniformQuoteError]) (by norm_num [uniformQuoteError])
        favorableCompleteH11 [] (.query 7) (by decide) (by decide) 11 1 0 (154035641216/1953125) 0 4
        (by simpa using favorable_complete_11_root_stats 7) favorable_complete_11_root_parent_visits
        favorable_complete_11_quote_7 (bonus_7_5_bound4 11 1 (by norm_num) (by norm_num))
      exact lt_of_le_of_lt hh.2 (by norm_num [savedCref,uniformQuoteError])

  apply visited_choice_from_ordered_certificate _ _ [] [.query 0]
    [.query 2,.query 3,.query 4,.query 5,.query 6,.query 7] (.query 1) (by decide)
  · intro a ha
    have ho : orderedLegalAvailable [] = [.query 0,.query 1,.query 2,.query 3,.query 4,.query 5,.query 6,.query 7] := by decide
    rw [ho] at ha
    simp only [List.mem_cons,List.not_mem_nil,or_false] at ha
    rcases ha with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> decide
  · intro a ha
    simp only [List.mem_singleton] at ha
    subst a
    exact lt_of_lt_of_le (hneg 0 (by decide)) h1pos
  · intro a ha
    simp only [List.mem_cons,List.not_mem_nil,or_false] at ha
    rcases ha with rfl | rfl | rfl | rfl | rfl | rfl <;>
      exact (lt_of_lt_of_le (hneg _ (by decide)) h1pos).le

theorem favorable_complete_11_hyde_stats (r : Fin 3) :
    replayBackup favorableCompleteH11 emptyStatistics [.query 1,.hydeRetriever r] =
      ⟨1,if r = 1 then (1/2:ℝ) else 0⟩ := by
  rw [replayBackup_empty_closed_form]
  fin_cases r <;> simp +decide [backedEvents,favorableCompleteH11,favorableCompleteProposal,
    favorableCompleteEvent1,favorableCompleteEvent2,favorableCompleteEvent3,favorableCompleteEvent4,
    favorableCompleteEvent5,favorableCompleteEvent6,favorableCompleteEvent7,favorableCompleteEvent8,
    favorableCompleteEvent9,favorableCompleteEvent10,favorableCompleteEvent11,taskReward]

theorem favorable_complete_11_hyde_penalty_zero (r : Fin 3) :
    controlPenalty savedCref uniformQuoteError unitRoleUnused .complete favorableCompleteH11
      [.query 1] (.hydeRetriever r) = 0 := by
  apply control_penalty_empty_suffix
  fin_cases r <;> decide

theorem favorable_complete_12_hyde_selected :
    nativeFirstChoice (indexScore (7/5) (controlPenalty savedCref uniformQuoteError unitRoleUnused .complete)
      favorableCompleteH11 [.query 1]) favorableCompleteH11 [.query 1] = .hydeRetriever 1 := by
  have hh (r : Fin 3) : indexScore (7/5) (controlPenalty savedCref uniformQuoteError unitRoleUnused .complete)
      favorableCompleteH11 [.query 1] (.hydeRetriever r) =
      treeIndex (if r = 1 then (1/2:ℝ) else 0) (7/5) 0 4 1 := by
    have hp : rawVisits favorableCompleteH11 [.query 1] = 4 := by decide
    have hn : rawVisits favorableCompleteH11 ([.query 1]++[.hydeRetriever r]) = 1 := by
      unfold rawVisits
      simpa using congrArg BackupStat.visits (favorable_complete_11_hyde_stats r)
    simp only [indexScore,hp,hn,List.singleton_append,favorable_complete_11_hyde_stats,
      favorable_complete_11_hyde_penalty_zero,BackupStat.mean,div_one]
    have hn2 : rawVisits favorableCompleteH11 [.query 1,.hydeRetriever r] = 1 := by simpa using hn
    rw [hn2]
    norm_num
  apply visited_choice_from_ordered_certificate _ _ [.query 1] [] [.hydeRetriever 0,.hydeRetriever 2]
    (.hydeRetriever 1) (by decide)
  · intro a ha
    have ho : orderedLegalAvailable [.query 1] = [.hydeRetriever 1,.hydeRetriever 0,.hydeRetriever 2] := by decide
    rw [ho] at ha
    simp only [List.mem_cons,List.not_mem_nil,or_false] at ha
    rcases ha with rfl | rfl | rfl <;> decide
  · simp
  · intro a ha
    simp only [List.mem_cons,List.not_mem_nil,or_false] at ha
    rcases ha with rfl | rfl <;> rw [hh,hh] <;>
      apply (same_visits_index_weak_iff _ _ _ _ _ _ _).mpr <;> simp +decide <;> norm_num

theorem favorable_complete_12_actual_event :
    nativeEvent budgetTape (7/5) (controlPenalty savedCref uniformQuoteError unitRoleUnused .complete)
      (taskReward false (2/5) (1/2)) favorableCompleteH11 = favorableCompleteEvent12 := by
  have hroot := native_select_existing_step budgetTape (7/5)
    (controlPenalty savedCref uniformQuoteError unitRoleUnused .complete) favorableCompleteH11 8 [] (.query 1)
    (by decide) (by decide) favorable_complete_12_root_selected
  have hhyde := native_select_existing_step budgetTape (7/5)
    (controlPenalty savedCref uniformQuoteError unitRoleUnused .complete) favorableCompleteH11 7 [.query 1] (.hydeRetriever 1)
    (by decide) (by decide) favorable_complete_12_hyde_selected
  have hnew := native_select_new_step budgetTape (7/5)
    (controlPenalty savedCref uniformQuoteError unitRoleUnused .complete) favorableCompleteH11 6 [.query 1,.hydeRetriever 1]
    [.selection 1,.selection 2,.selection 3,.selection 0] (.selection 0)
    (by decide) (by decide) (by decide) (by decide)
  have hs : nativeSelect budgetTape (7/5)
      (controlPenalty savedCref uniformQuoteError unitRoleUnused .complete) favorableCompleteH11 9 [] =
      [.query 1,.hydeRetriever 1,.selection 0] := by
    rw [hroot]; simp only [List.nil_append]; rw [hhyde]; simp only [List.singleton_append]; rw [hnew]; rfl
  have hr : repairedRollout budgetTape favorableCompleteH11 9 [.query 1,.hydeRetriever 1,.selection 0] =
      [.query 1,.hydeRetriever 1,.selection 0,.width 1,.stop,.reranker 0,.topm 0,.context 0,.answer 0] := by decide
  simp only [nativeEvent,hs,hr]
  rfl

end AgentUCT32MConcrete
