import ProposalRewards
import TrajectoryBonus
import InitialConcreteBridge
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

def favorableCompleteS12Before := favorableCompleteProposal.take 11

theorem favorableCompleteS12Choice0 : nativeFirstChoice (indexScore (7/5) (controlPenalty savedCref uniformQuoteError unitRoleUnused .complete) favorableCompleteS12Before []) favorableCompleteS12Before [] = .query 1 := by
  apply complete_root_from_physical_gap favorableCompleteS12Before (favorableComplete_prefix_rewards 11) (by decide)
  · intro q; fin_cases q <;> decide
  · decide
  · intro q hq
    fin_cases q
    · change pathQuote .complete (pathHistoryCache favorableCompleteS12Before) (completedPrice unitRoleUnused) (safeCompletion [.query 0]) = _
      have hs : pathSuffix (pathHistoryCache favorableCompleteS12Before) (safeCompletion [.query 0]) = [[.query 0,.normalRetriever 0,.selection 0,.width 1],[.query 0,.normalRetriever 0,.selection 0,.width 1,.stop],[.query 0,.normalRetriever 0,.selection 0,.width 1,.stop,.reranker 1],[.query 0,.normalRetriever 0,.selection 0,.width 1,.stop,.reranker 1,.topm 2],[.query 0,.normalRetriever 0,.selection 0,.width 1,.stop,.reranker 1,.topm 2,.context 0],[.query 0,.normalRetriever 0,.selection 0,.width 1,.stop,.reranker 1,.topm 2,.context 0,.answer 2]] := by decide
      unfold pathQuote
      rw [hs]
      norm_num [completed_price_rational_projection,rationalActionPrice]
    · exact (hq rfl).elim
    · change pathQuote .complete (pathHistoryCache favorableCompleteS12Before) (completedPrice unitRoleUnused) (safeCompletion [.query 2]) = _
      have hs : pathSuffix (pathHistoryCache favorableCompleteS12Before) (safeCompletion [.query 2]) = [[.query 2,.normalRetriever 0,.selection 0,.width 1],[.query 2,.normalRetriever 0,.selection 0,.width 1,.stop],[.query 2,.normalRetriever 0,.selection 0,.width 1,.stop,.reranker 1],[.query 2,.normalRetriever 0,.selection 0,.width 1,.stop,.reranker 1,.topm 2],[.query 2,.normalRetriever 0,.selection 0,.width 1,.stop,.reranker 1,.topm 2,.context 0],[.query 2,.normalRetriever 0,.selection 0,.width 1,.stop,.reranker 1,.topm 2,.context 0,.answer 2]] := by decide
      unfold pathQuote
      rw [hs]
      norm_num [completed_price_rational_projection,rationalActionPrice]
    · change pathQuote .complete (pathHistoryCache favorableCompleteS12Before) (completedPrice unitRoleUnused) (safeCompletion [.query 3]) = _
      have hs : pathSuffix (pathHistoryCache favorableCompleteS12Before) (safeCompletion [.query 3]) = [[.query 3,.normalRetriever 0,.selection 0,.width 1],[.query 3,.normalRetriever 0,.selection 0,.width 1,.stop],[.query 3,.normalRetriever 0,.selection 0,.width 1,.stop,.reranker 1],[.query 3,.normalRetriever 0,.selection 0,.width 1,.stop,.reranker 1,.topm 2],[.query 3,.normalRetriever 0,.selection 0,.width 1,.stop,.reranker 1,.topm 2,.context 0],[.query 3,.normalRetriever 0,.selection 0,.width 1,.stop,.reranker 1,.topm 2,.context 0,.answer 2]] := by decide
      unfold pathQuote
      rw [hs]
      norm_num [completed_price_rational_projection,rationalActionPrice]
    · change pathQuote .complete (pathHistoryCache favorableCompleteS12Before) (completedPrice unitRoleUnused) (safeCompletion [.query 4]) = _
      have hs : pathSuffix (pathHistoryCache favorableCompleteS12Before) (safeCompletion [.query 4]) = [[.query 4,.normalRetriever 0,.selection 0,.width 1],[.query 4,.normalRetriever 0,.selection 0,.width 1,.stop],[.query 4,.normalRetriever 0,.selection 0,.width 1,.stop,.reranker 1],[.query 4,.normalRetriever 0,.selection 0,.width 1,.stop,.reranker 1,.topm 2],[.query 4,.normalRetriever 0,.selection 0,.width 1,.stop,.reranker 1,.topm 2,.context 0],[.query 4,.normalRetriever 0,.selection 0,.width 1,.stop,.reranker 1,.topm 2,.context 0,.answer 2]] := by decide
      unfold pathQuote
      rw [hs]
      norm_num [completed_price_rational_projection,rationalActionPrice]
    · change pathQuote .complete (pathHistoryCache favorableCompleteS12Before) (completedPrice unitRoleUnused) (safeCompletion [.query 5]) = _
      have hs : pathSuffix (pathHistoryCache favorableCompleteS12Before) (safeCompletion [.query 5]) = [[.query 5,.normalRetriever 0,.selection 0,.width 1],[.query 5,.normalRetriever 0,.selection 0,.width 1,.stop],[.query 5,.normalRetriever 0,.selection 0,.width 1,.stop,.reranker 1],[.query 5,.normalRetriever 0,.selection 0,.width 1,.stop,.reranker 1,.topm 2],[.query 5,.normalRetriever 0,.selection 0,.width 1,.stop,.reranker 1,.topm 2,.context 0],[.query 5,.normalRetriever 0,.selection 0,.width 1,.stop,.reranker 1,.topm 2,.context 0,.answer 2]] := by decide
      unfold pathQuote
      rw [hs]
      norm_num [completed_price_rational_projection,rationalActionPrice]
    · change pathQuote .complete (pathHistoryCache favorableCompleteS12Before) (completedPrice unitRoleUnused) (safeCompletion [.query 6]) = _
      have hs : pathSuffix (pathHistoryCache favorableCompleteS12Before) (safeCompletion [.query 6]) = [[.query 6,.normalRetriever 0,.selection 0,.width 1],[.query 6,.normalRetriever 0,.selection 0,.width 1,.stop],[.query 6,.normalRetriever 0,.selection 0,.width 1,.stop,.reranker 1],[.query 6,.normalRetriever 0,.selection 0,.width 1,.stop,.reranker 1,.topm 2],[.query 6,.normalRetriever 0,.selection 0,.width 1,.stop,.reranker 1,.topm 2,.context 0],[.query 6,.normalRetriever 0,.selection 0,.width 1,.stop,.reranker 1,.topm 2,.context 0,.answer 2]] := by decide
      unfold pathQuote
      rw [hs]
      norm_num [completed_price_rational_projection,rationalActionPrice]
    · change pathQuote .complete (pathHistoryCache favorableCompleteS12Before) (completedPrice unitRoleUnused) (safeCompletion [.query 7]) = _
      have hs : pathSuffix (pathHistoryCache favorableCompleteS12Before) (safeCompletion [.query 7]) = [[.query 7,.normalRetriever 0,.selection 0,.width 1],[.query 7,.normalRetriever 0,.selection 0,.width 1,.stop],[.query 7,.normalRetriever 0,.selection 0,.width 1,.stop,.reranker 1],[.query 7,.normalRetriever 0,.selection 0,.width 1,.stop,.reranker 1,.topm 2],[.query 7,.normalRetriever 0,.selection 0,.width 1,.stop,.reranker 1,.topm 2,.context 0],[.query 7,.normalRetriever 0,.selection 0,.width 1,.stop,.reranker 1,.topm 2,.context 0,.answer 2]] := by decide
      unfold pathQuote
      rw [hs]
      norm_num [completed_price_rational_projection,rationalActionPrice]

theorem favorableCompleteS12D1I0 : indexScore (7/5) (controlPenalty savedCref uniformQuoteError unitRoleUnused .complete) favorableCompleteS12Before [.query 1] (.hydeRetriever 1) = treeIndex ((1/2)/1) (7/5) 0 4 1 := by
  have hs : replayBackup favorableCompleteS12Before emptyStatistics ([.query 1]++[.hydeRetriever 1]) = ⟨1,(1/2)⟩ := by
    rw [replayBackup_empty_closed_form]
    simp +decide [backedEvents,favorableCompleteS12Before,favorableCompleteProposal,favorableCompleteEvent1,favorableCompleteEvent2,favorableCompleteEvent3,favorableCompleteEvent4,favorableCompleteEvent5,favorableCompleteEvent6,favorableCompleteEvent7,favorableCompleteEvent8,favorableCompleteEvent9,favorableCompleteEvent10,favorableCompleteEvent11,taskReward]
    <;> norm_num
  have hp : rawVisits favorableCompleteS12Before [.query 1] = 4 := by decide
  have hn : rawVisits favorableCompleteS12Before ([.query 1]++[.hydeRetriever 1]) = 1 := by decide
  have hz : (controlPenalty savedCref uniformQuoteError unitRoleUnused .complete) favorableCompleteS12Before [.query 1] (.hydeRetriever 1) = 0 := control_penalty_empty_suffix _ _ _ _ _ _ (by decide)
  unfold indexScore
  rw [hs,hp,hn,hz]
  simp only [BackupStat.mean]
  norm_num

theorem favorableCompleteS12D1I1 : indexScore (7/5) (controlPenalty savedCref uniformQuoteError unitRoleUnused .complete) favorableCompleteS12Before [.query 1] (.hydeRetriever 0) = treeIndex ((0/1)/1) (7/5) 0 4 1 := by
  have hs : replayBackup favorableCompleteS12Before emptyStatistics ([.query 1]++[.hydeRetriever 0]) = ⟨1,(0/1)⟩ := by
    rw [replayBackup_empty_closed_form]
    simp +decide [backedEvents,favorableCompleteS12Before,favorableCompleteProposal,favorableCompleteEvent1,favorableCompleteEvent2,favorableCompleteEvent3,favorableCompleteEvent4,favorableCompleteEvent5,favorableCompleteEvent6,favorableCompleteEvent7,favorableCompleteEvent8,favorableCompleteEvent9,favorableCompleteEvent10,favorableCompleteEvent11,taskReward]
    <;> norm_num
  have hp : rawVisits favorableCompleteS12Before [.query 1] = 4 := by decide
  have hn : rawVisits favorableCompleteS12Before ([.query 1]++[.hydeRetriever 0]) = 1 := by decide
  have hz : (controlPenalty savedCref uniformQuoteError unitRoleUnused .complete) favorableCompleteS12Before [.query 1] (.hydeRetriever 0) = 0 := control_penalty_empty_suffix _ _ _ _ _ _ (by decide)
  unfold indexScore
  rw [hs,hp,hn,hz]
  simp only [BackupStat.mean]
  norm_num

theorem favorableCompleteS12D1I2 : indexScore (7/5) (controlPenalty savedCref uniformQuoteError unitRoleUnused .complete) favorableCompleteS12Before [.query 1] (.hydeRetriever 2) = treeIndex ((0/1)/1) (7/5) 0 4 1 := by
  have hs : replayBackup favorableCompleteS12Before emptyStatistics ([.query 1]++[.hydeRetriever 2]) = ⟨1,(0/1)⟩ := by
    rw [replayBackup_empty_closed_form]
    simp +decide [backedEvents,favorableCompleteS12Before,favorableCompleteProposal,favorableCompleteEvent1,favorableCompleteEvent2,favorableCompleteEvent3,favorableCompleteEvent4,favorableCompleteEvent5,favorableCompleteEvent6,favorableCompleteEvent7,favorableCompleteEvent8,favorableCompleteEvent9,favorableCompleteEvent10,favorableCompleteEvent11,taskReward]
    <;> norm_num
  have hp : rawVisits favorableCompleteS12Before [.query 1] = 4 := by decide
  have hn : rawVisits favorableCompleteS12Before ([.query 1]++[.hydeRetriever 2]) = 1 := by decide
  have hz : (controlPenalty savedCref uniformQuoteError unitRoleUnused .complete) favorableCompleteS12Before [.query 1] (.hydeRetriever 2) = 0 := control_penalty_empty_suffix _ _ _ _ _ _ (by decide)
  unfold indexScore
  rw [hs,hp,hn,hz]
  simp only [BackupStat.mean]
  norm_num

theorem favorableCompleteS12D1Cmp1 : indexScore (7/5) (controlPenalty savedCref uniformQuoteError unitRoleUnused .complete) favorableCompleteS12Before [.query 1] (.hydeRetriever 0) ≤ indexScore (7/5) (controlPenalty savedCref uniformQuoteError unitRoleUnused .complete) favorableCompleteS12Before [.query 1] (.hydeRetriever 1) := by
  rw [favorableCompleteS12D1I1,favorableCompleteS12D1I0]
  have h := index_weak_order_from_intervals ((1/2)/1) ((0/1)/1) 0 0 (44402267/25000000) (88804541/50000000)
    (treeBonus (7/5) 4 1) (treeBonus (7/5) 4 1)
    (trajectory_bonus_4_1).1 (trajectory_bonus_4_1).2 (by norm_num)
  simpa only [treeIndex,sub_zero] using h

theorem favorableCompleteS12D1Cmp2 : indexScore (7/5) (controlPenalty savedCref uniformQuoteError unitRoleUnused .complete) favorableCompleteS12Before [.query 1] (.hydeRetriever 2) ≤ indexScore (7/5) (controlPenalty savedCref uniformQuoteError unitRoleUnused .complete) favorableCompleteS12Before [.query 1] (.hydeRetriever 1) := by
  rw [favorableCompleteS12D1I2,favorableCompleteS12D1I0]
  have h := index_weak_order_from_intervals ((1/2)/1) ((0/1)/1) 0 0 (44402267/25000000) (88804541/50000000)
    (treeBonus (7/5) 4 1) (treeBonus (7/5) 4 1)
    (trajectory_bonus_4_1).1 (trajectory_bonus_4_1).2 (by norm_num)
  simpa only [treeIndex,sub_zero] using h

theorem favorableCompleteS12Choice1 : nativeFirstChoice (indexScore (7/5) (controlPenalty savedCref uniformQuoteError unitRoleUnused .complete) favorableCompleteS12Before [.query 1]) favorableCompleteS12Before [.query 1] = .hydeRetriever 1 := by
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
    · exact favorableCompleteS12D1Cmp1
    · exact favorableCompleteS12D1Cmp2

theorem favorableCompleteS12ActualEvent : nativeEvent budgetTape (7/5) (controlPenalty savedCref uniformQuoteError unitRoleUnused .complete)
    (taskReward false (2/5) (1/2)) favorableCompleteS12Before = favorableCompleteEvent12 := by
  have hs0 := native_select_existing_step budgetTape (7/5) (controlPenalty savedCref uniformQuoteError unitRoleUnused .complete) favorableCompleteS12Before 8 [] (.query 1)
    (by decide) (by decide) favorableCompleteS12Choice0
  have hs1 := native_select_existing_step budgetTape (7/5) (controlPenalty savedCref uniformQuoteError unitRoleUnused .complete) favorableCompleteS12Before 7 [.query 1] (.hydeRetriever 1)
    (by decide) (by decide) favorableCompleteS12Choice1
  have hnew := native_select_new_step budgetTape (7/5) (controlPenalty savedCref uniformQuoteError unitRoleUnused .complete) favorableCompleteS12Before 6 [.query 1,.hydeRetriever 1]
    [.selection 1,.selection 2,.selection 3,.selection 0] (.selection 0) (by decide) (by decide) (by decide) (by decide)
  have hs : nativeSelect budgetTape (7/5) (controlPenalty savedCref uniformQuoteError unitRoleUnused .complete) favorableCompleteS12Before 9 [] = [.query 1,.hydeRetriever 1,.selection 0] := by
    rw [hs0]
    change nativeSelect budgetTape (7/5) (controlPenalty savedCref uniformQuoteError unitRoleUnused .complete) favorableCompleteS12Before 8 [.query 1] = _
    rw [hs1]
    change nativeSelect budgetTape (7/5) (controlPenalty savedCref uniformQuoteError unitRoleUnused .complete) favorableCompleteS12Before 7 [.query 1,.hydeRetriever 1] = _
    rw [hnew] <;> rfl
  have hr : repairedRollout budgetTape favorableCompleteS12Before 9 [.query 1,.hydeRetriever 1,.selection 0] = [.query 1,.hydeRetriever 1,.selection 0,.width 1,.stop,.reranker 0,.topm 0,.context 0,.answer 0] := by decide
  simp only [nativeEvent,hs,hr]
  rfl

def favorableCompleteS13Before := favorableCompleteProposal.take 12

theorem favorableCompleteS13Choice0 : nativeFirstChoice (indexScore (7/5) (controlPenalty savedCref uniformQuoteError unitRoleUnused .complete) favorableCompleteS13Before []) favorableCompleteS13Before [] = .query 1 := by
  apply complete_root_from_physical_gap favorableCompleteS13Before (favorableComplete_prefix_rewards 12) (by decide)
  · intro q; fin_cases q <;> decide
  · decide
  · intro q hq
    fin_cases q
    · change pathQuote .complete (pathHistoryCache favorableCompleteS13Before) (completedPrice unitRoleUnused) (safeCompletion [.query 0]) = _
      have hs : pathSuffix (pathHistoryCache favorableCompleteS13Before) (safeCompletion [.query 0]) = [[.query 0,.normalRetriever 0,.selection 0,.width 1],[.query 0,.normalRetriever 0,.selection 0,.width 1,.stop],[.query 0,.normalRetriever 0,.selection 0,.width 1,.stop,.reranker 1],[.query 0,.normalRetriever 0,.selection 0,.width 1,.stop,.reranker 1,.topm 2],[.query 0,.normalRetriever 0,.selection 0,.width 1,.stop,.reranker 1,.topm 2,.context 0],[.query 0,.normalRetriever 0,.selection 0,.width 1,.stop,.reranker 1,.topm 2,.context 0,.answer 2]] := by decide
      unfold pathQuote
      rw [hs]
      norm_num [completed_price_rational_projection,rationalActionPrice]
    · exact (hq rfl).elim
    · change pathQuote .complete (pathHistoryCache favorableCompleteS13Before) (completedPrice unitRoleUnused) (safeCompletion [.query 2]) = _
      have hs : pathSuffix (pathHistoryCache favorableCompleteS13Before) (safeCompletion [.query 2]) = [[.query 2,.normalRetriever 0,.selection 0,.width 1],[.query 2,.normalRetriever 0,.selection 0,.width 1,.stop],[.query 2,.normalRetriever 0,.selection 0,.width 1,.stop,.reranker 1],[.query 2,.normalRetriever 0,.selection 0,.width 1,.stop,.reranker 1,.topm 2],[.query 2,.normalRetriever 0,.selection 0,.width 1,.stop,.reranker 1,.topm 2,.context 0],[.query 2,.normalRetriever 0,.selection 0,.width 1,.stop,.reranker 1,.topm 2,.context 0,.answer 2]] := by decide
      unfold pathQuote
      rw [hs]
      norm_num [completed_price_rational_projection,rationalActionPrice]
    · change pathQuote .complete (pathHistoryCache favorableCompleteS13Before) (completedPrice unitRoleUnused) (safeCompletion [.query 3]) = _
      have hs : pathSuffix (pathHistoryCache favorableCompleteS13Before) (safeCompletion [.query 3]) = [[.query 3,.normalRetriever 0,.selection 0,.width 1],[.query 3,.normalRetriever 0,.selection 0,.width 1,.stop],[.query 3,.normalRetriever 0,.selection 0,.width 1,.stop,.reranker 1],[.query 3,.normalRetriever 0,.selection 0,.width 1,.stop,.reranker 1,.topm 2],[.query 3,.normalRetriever 0,.selection 0,.width 1,.stop,.reranker 1,.topm 2,.context 0],[.query 3,.normalRetriever 0,.selection 0,.width 1,.stop,.reranker 1,.topm 2,.context 0,.answer 2]] := by decide
      unfold pathQuote
      rw [hs]
      norm_num [completed_price_rational_projection,rationalActionPrice]
    · change pathQuote .complete (pathHistoryCache favorableCompleteS13Before) (completedPrice unitRoleUnused) (safeCompletion [.query 4]) = _
      have hs : pathSuffix (pathHistoryCache favorableCompleteS13Before) (safeCompletion [.query 4]) = [[.query 4,.normalRetriever 0,.selection 0,.width 1],[.query 4,.normalRetriever 0,.selection 0,.width 1,.stop],[.query 4,.normalRetriever 0,.selection 0,.width 1,.stop,.reranker 1],[.query 4,.normalRetriever 0,.selection 0,.width 1,.stop,.reranker 1,.topm 2],[.query 4,.normalRetriever 0,.selection 0,.width 1,.stop,.reranker 1,.topm 2,.context 0],[.query 4,.normalRetriever 0,.selection 0,.width 1,.stop,.reranker 1,.topm 2,.context 0,.answer 2]] := by decide
      unfold pathQuote
      rw [hs]
      norm_num [completed_price_rational_projection,rationalActionPrice]
    · change pathQuote .complete (pathHistoryCache favorableCompleteS13Before) (completedPrice unitRoleUnused) (safeCompletion [.query 5]) = _
      have hs : pathSuffix (pathHistoryCache favorableCompleteS13Before) (safeCompletion [.query 5]) = [[.query 5,.normalRetriever 0,.selection 0,.width 1],[.query 5,.normalRetriever 0,.selection 0,.width 1,.stop],[.query 5,.normalRetriever 0,.selection 0,.width 1,.stop,.reranker 1],[.query 5,.normalRetriever 0,.selection 0,.width 1,.stop,.reranker 1,.topm 2],[.query 5,.normalRetriever 0,.selection 0,.width 1,.stop,.reranker 1,.topm 2,.context 0],[.query 5,.normalRetriever 0,.selection 0,.width 1,.stop,.reranker 1,.topm 2,.context 0,.answer 2]] := by decide
      unfold pathQuote
      rw [hs]
      norm_num [completed_price_rational_projection,rationalActionPrice]
    · change pathQuote .complete (pathHistoryCache favorableCompleteS13Before) (completedPrice unitRoleUnused) (safeCompletion [.query 6]) = _
      have hs : pathSuffix (pathHistoryCache favorableCompleteS13Before) (safeCompletion [.query 6]) = [[.query 6,.normalRetriever 0,.selection 0,.width 1],[.query 6,.normalRetriever 0,.selection 0,.width 1,.stop],[.query 6,.normalRetriever 0,.selection 0,.width 1,.stop,.reranker 1],[.query 6,.normalRetriever 0,.selection 0,.width 1,.stop,.reranker 1,.topm 2],[.query 6,.normalRetriever 0,.selection 0,.width 1,.stop,.reranker 1,.topm 2,.context 0],[.query 6,.normalRetriever 0,.selection 0,.width 1,.stop,.reranker 1,.topm 2,.context 0,.answer 2]] := by decide
      unfold pathQuote
      rw [hs]
      norm_num [completed_price_rational_projection,rationalActionPrice]
    · change pathQuote .complete (pathHistoryCache favorableCompleteS13Before) (completedPrice unitRoleUnused) (safeCompletion [.query 7]) = _
      have hs : pathSuffix (pathHistoryCache favorableCompleteS13Before) (safeCompletion [.query 7]) = [[.query 7,.normalRetriever 0,.selection 0,.width 1],[.query 7,.normalRetriever 0,.selection 0,.width 1,.stop],[.query 7,.normalRetriever 0,.selection 0,.width 1,.stop,.reranker 1],[.query 7,.normalRetriever 0,.selection 0,.width 1,.stop,.reranker 1,.topm 2],[.query 7,.normalRetriever 0,.selection 0,.width 1,.stop,.reranker 1,.topm 2,.context 0],[.query 7,.normalRetriever 0,.selection 0,.width 1,.stop,.reranker 1,.topm 2,.context 0,.answer 2]] := by decide
      unfold pathQuote
      rw [hs]
      norm_num [completed_price_rational_projection,rationalActionPrice]

theorem favorableCompleteS13D1I0 : indexScore (7/5) (controlPenalty savedCref uniformQuoteError unitRoleUnused .complete) favorableCompleteS13Before [.query 1] (.hydeRetriever 1) = treeIndex ((1/1)/2) (7/5) 0 5 2 := by
  have hs : replayBackup favorableCompleteS13Before emptyStatistics ([.query 1]++[.hydeRetriever 1]) = ⟨2,(1/1)⟩ := by
    rw [replayBackup_empty_closed_form]
    simp +decide [backedEvents,favorableCompleteS13Before,favorableCompleteProposal,favorableCompleteEvent1,favorableCompleteEvent2,favorableCompleteEvent3,favorableCompleteEvent4,favorableCompleteEvent5,favorableCompleteEvent6,favorableCompleteEvent7,favorableCompleteEvent8,favorableCompleteEvent9,favorableCompleteEvent10,favorableCompleteEvent11,favorableCompleteEvent12,taskReward]
    <;> norm_num
  have hp : rawVisits favorableCompleteS13Before [.query 1] = 5 := by decide
  have hn : rawVisits favorableCompleteS13Before ([.query 1]++[.hydeRetriever 1]) = 2 := by decide
  have hz : (controlPenalty savedCref uniformQuoteError unitRoleUnused .complete) favorableCompleteS13Before [.query 1] (.hydeRetriever 1) = 0 := control_penalty_empty_suffix _ _ _ _ _ _ (by decide)
  unfold indexScore
  rw [hs,hp,hn,hz]
  simp only [BackupStat.mean]
  norm_num

theorem favorableCompleteS13D1I1 : indexScore (7/5) (controlPenalty savedCref uniformQuoteError unitRoleUnused .complete) favorableCompleteS13Before [.query 1] (.hydeRetriever 0) = treeIndex ((0/1)/1) (7/5) 0 5 1 := by
  have hs : replayBackup favorableCompleteS13Before emptyStatistics ([.query 1]++[.hydeRetriever 0]) = ⟨1,(0/1)⟩ := by
    rw [replayBackup_empty_closed_form]
    simp +decide [backedEvents,favorableCompleteS13Before,favorableCompleteProposal,favorableCompleteEvent1,favorableCompleteEvent2,favorableCompleteEvent3,favorableCompleteEvent4,favorableCompleteEvent5,favorableCompleteEvent6,favorableCompleteEvent7,favorableCompleteEvent8,favorableCompleteEvent9,favorableCompleteEvent10,favorableCompleteEvent11,favorableCompleteEvent12,taskReward]
    <;> norm_num
  have hp : rawVisits favorableCompleteS13Before [.query 1] = 5 := by decide
  have hn : rawVisits favorableCompleteS13Before ([.query 1]++[.hydeRetriever 0]) = 1 := by decide
  have hz : (controlPenalty savedCref uniformQuoteError unitRoleUnused .complete) favorableCompleteS13Before [.query 1] (.hydeRetriever 0) = 0 := control_penalty_empty_suffix _ _ _ _ _ _ (by decide)
  unfold indexScore
  rw [hs,hp,hn,hz]
  simp only [BackupStat.mean]
  norm_num

theorem favorableCompleteS13D1I2 : indexScore (7/5) (controlPenalty savedCref uniformQuoteError unitRoleUnused .complete) favorableCompleteS13Before [.query 1] (.hydeRetriever 2) = treeIndex ((0/1)/1) (7/5) 0 5 1 := by
  have hs : replayBackup favorableCompleteS13Before emptyStatistics ([.query 1]++[.hydeRetriever 2]) = ⟨1,(0/1)⟩ := by
    rw [replayBackup_empty_closed_form]
    simp +decide [backedEvents,favorableCompleteS13Before,favorableCompleteProposal,favorableCompleteEvent1,favorableCompleteEvent2,favorableCompleteEvent3,favorableCompleteEvent4,favorableCompleteEvent5,favorableCompleteEvent6,favorableCompleteEvent7,favorableCompleteEvent8,favorableCompleteEvent9,favorableCompleteEvent10,favorableCompleteEvent11,favorableCompleteEvent12,taskReward]
    <;> norm_num
  have hp : rawVisits favorableCompleteS13Before [.query 1] = 5 := by decide
  have hn : rawVisits favorableCompleteS13Before ([.query 1]++[.hydeRetriever 2]) = 1 := by decide
  have hz : (controlPenalty savedCref uniformQuoteError unitRoleUnused .complete) favorableCompleteS13Before [.query 1] (.hydeRetriever 2) = 0 := control_penalty_empty_suffix _ _ _ _ _ _ (by decide)
  unfold indexScore
  rw [hs,hp,hn,hz]
  simp only [BackupStat.mean]
  norm_num

theorem favorableCompleteS13D1Cmp0 : indexScore (7/5) (controlPenalty savedCref uniformQuoteError unitRoleUnused .complete) favorableCompleteS13Before [.query 1] (.hydeRetriever 1) < indexScore (7/5) (controlPenalty savedCref uniformQuoteError unitRoleUnused .complete) favorableCompleteS13Before [.query 1] (.hydeRetriever 0) := by
  rw [favorableCompleteS13D1I0,favorableCompleteS13D1I1]
  have h := index_strict_order_from_intervals ((0/1)/1) ((1/1)/2) 0 0 (93699627/50000000) (66255651/50000000)
    (treeBonus (7/5) 5 1) (treeBonus (7/5) 5 2)
    (trajectory_bonus_5_1).1 (trajectory_bonus_5_2).2 (by norm_num)
  simpa only [treeIndex,sub_zero] using h

theorem favorableCompleteS13D1Cmp2 : indexScore (7/5) (controlPenalty savedCref uniformQuoteError unitRoleUnused .complete) favorableCompleteS13Before [.query 1] (.hydeRetriever 2) ≤ indexScore (7/5) (controlPenalty savedCref uniformQuoteError unitRoleUnused .complete) favorableCompleteS13Before [.query 1] (.hydeRetriever 0) := by
  rw [favorableCompleteS13D1I2,favorableCompleteS13D1I1]

theorem favorableCompleteS13Choice1 : nativeFirstChoice (indexScore (7/5) (controlPenalty savedCref uniformQuoteError unitRoleUnused .complete) favorableCompleteS13Before [.query 1]) favorableCompleteS13Before [.query 1] = .hydeRetriever 0 := by
  apply visited_choice_from_ordered_certificate _ _ [.query 1] [.hydeRetriever 1] [.hydeRetriever 2] (.hydeRetriever 0) (by decide)
  · intro a ha
    have ho : orderedLegalAvailable [.query 1] = [.hydeRetriever 1,.hydeRetriever 0,.hydeRetriever 2] := by decide
    rw [ho] at ha
    simp only [List.mem_cons,List.not_mem_nil,or_false] at ha
    rcases ha with rfl | rfl | rfl <;> decide
  · intro a ha
    simp only [List.mem_cons,List.not_mem_nil,or_false] at ha
    rcases ha with rfl
    · exact favorableCompleteS13D1Cmp0
  · intro a ha
    simp only [List.mem_cons,List.not_mem_nil,or_false] at ha
    rcases ha with rfl
    · exact favorableCompleteS13D1Cmp2

theorem favorableCompleteS13ActualEvent : nativeEvent budgetTape (7/5) (controlPenalty savedCref uniformQuoteError unitRoleUnused .complete)
    (taskReward false (2/5) (1/2)) favorableCompleteS13Before = favorableCompleteEvent13 := by
  have hs0 := native_select_existing_step budgetTape (7/5) (controlPenalty savedCref uniformQuoteError unitRoleUnused .complete) favorableCompleteS13Before 8 [] (.query 1)
    (by decide) (by decide) favorableCompleteS13Choice0
  have hs1 := native_select_existing_step budgetTape (7/5) (controlPenalty savedCref uniformQuoteError unitRoleUnused .complete) favorableCompleteS13Before 7 [.query 1] (.hydeRetriever 0)
    (by decide) (by decide) favorableCompleteS13Choice1
  have hnew := native_select_new_step budgetTape (7/5) (controlPenalty savedCref uniformQuoteError unitRoleUnused .complete) favorableCompleteS13Before 6 [.query 1,.hydeRetriever 0]
    [.selection 1,.selection 2,.selection 3,.selection 0] (.selection 0) (by decide) (by decide) (by decide) (by decide)
  have hs : nativeSelect budgetTape (7/5) (controlPenalty savedCref uniformQuoteError unitRoleUnused .complete) favorableCompleteS13Before 9 [] = [.query 1,.hydeRetriever 0,.selection 0] := by
    rw [hs0]
    change nativeSelect budgetTape (7/5) (controlPenalty savedCref uniformQuoteError unitRoleUnused .complete) favorableCompleteS13Before 8 [.query 1] = _
    rw [hs1]
    change nativeSelect budgetTape (7/5) (controlPenalty savedCref uniformQuoteError unitRoleUnused .complete) favorableCompleteS13Before 7 [.query 1,.hydeRetriever 0] = _
    rw [hnew] <;> rfl
  have hr : repairedRollout budgetTape favorableCompleteS13Before 9 [.query 1,.hydeRetriever 0,.selection 0] = [.query 1,.hydeRetriever 0,.selection 0,.width 0,.stop,.reranker 0,.topm 0,.context 0,.answer 0] := by decide
  simp only [nativeEvent,hs,hr]
  rfl

def favorableCompleteS14Before := favorableCompleteProposal.take 13

theorem favorableCompleteS14Choice0 : nativeFirstChoice (indexScore (7/5) (controlPenalty savedCref uniformQuoteError unitRoleUnused .complete) favorableCompleteS14Before []) favorableCompleteS14Before [] = .query 1 := by
  apply complete_root_from_physical_gap favorableCompleteS14Before (favorableComplete_prefix_rewards 13) (by decide)
  · intro q; fin_cases q <;> decide
  · decide
  · intro q hq
    fin_cases q
    · change pathQuote .complete (pathHistoryCache favorableCompleteS14Before) (completedPrice unitRoleUnused) (safeCompletion [.query 0]) = _
      have hs : pathSuffix (pathHistoryCache favorableCompleteS14Before) (safeCompletion [.query 0]) = [[.query 0,.normalRetriever 0,.selection 0,.width 1],[.query 0,.normalRetriever 0,.selection 0,.width 1,.stop],[.query 0,.normalRetriever 0,.selection 0,.width 1,.stop,.reranker 1],[.query 0,.normalRetriever 0,.selection 0,.width 1,.stop,.reranker 1,.topm 2],[.query 0,.normalRetriever 0,.selection 0,.width 1,.stop,.reranker 1,.topm 2,.context 0],[.query 0,.normalRetriever 0,.selection 0,.width 1,.stop,.reranker 1,.topm 2,.context 0,.answer 2]] := by decide
      unfold pathQuote
      rw [hs]
      norm_num [completed_price_rational_projection,rationalActionPrice]
    · exact (hq rfl).elim
    · change pathQuote .complete (pathHistoryCache favorableCompleteS14Before) (completedPrice unitRoleUnused) (safeCompletion [.query 2]) = _
      have hs : pathSuffix (pathHistoryCache favorableCompleteS14Before) (safeCompletion [.query 2]) = [[.query 2,.normalRetriever 0,.selection 0,.width 1],[.query 2,.normalRetriever 0,.selection 0,.width 1,.stop],[.query 2,.normalRetriever 0,.selection 0,.width 1,.stop,.reranker 1],[.query 2,.normalRetriever 0,.selection 0,.width 1,.stop,.reranker 1,.topm 2],[.query 2,.normalRetriever 0,.selection 0,.width 1,.stop,.reranker 1,.topm 2,.context 0],[.query 2,.normalRetriever 0,.selection 0,.width 1,.stop,.reranker 1,.topm 2,.context 0,.answer 2]] := by decide
      unfold pathQuote
      rw [hs]
      norm_num [completed_price_rational_projection,rationalActionPrice]
    · change pathQuote .complete (pathHistoryCache favorableCompleteS14Before) (completedPrice unitRoleUnused) (safeCompletion [.query 3]) = _
      have hs : pathSuffix (pathHistoryCache favorableCompleteS14Before) (safeCompletion [.query 3]) = [[.query 3,.normalRetriever 0,.selection 0,.width 1],[.query 3,.normalRetriever 0,.selection 0,.width 1,.stop],[.query 3,.normalRetriever 0,.selection 0,.width 1,.stop,.reranker 1],[.query 3,.normalRetriever 0,.selection 0,.width 1,.stop,.reranker 1,.topm 2],[.query 3,.normalRetriever 0,.selection 0,.width 1,.stop,.reranker 1,.topm 2,.context 0],[.query 3,.normalRetriever 0,.selection 0,.width 1,.stop,.reranker 1,.topm 2,.context 0,.answer 2]] := by decide
      unfold pathQuote
      rw [hs]
      norm_num [completed_price_rational_projection,rationalActionPrice]
    · change pathQuote .complete (pathHistoryCache favorableCompleteS14Before) (completedPrice unitRoleUnused) (safeCompletion [.query 4]) = _
      have hs : pathSuffix (pathHistoryCache favorableCompleteS14Before) (safeCompletion [.query 4]) = [[.query 4,.normalRetriever 0,.selection 0,.width 1],[.query 4,.normalRetriever 0,.selection 0,.width 1,.stop],[.query 4,.normalRetriever 0,.selection 0,.width 1,.stop,.reranker 1],[.query 4,.normalRetriever 0,.selection 0,.width 1,.stop,.reranker 1,.topm 2],[.query 4,.normalRetriever 0,.selection 0,.width 1,.stop,.reranker 1,.topm 2,.context 0],[.query 4,.normalRetriever 0,.selection 0,.width 1,.stop,.reranker 1,.topm 2,.context 0,.answer 2]] := by decide
      unfold pathQuote
      rw [hs]
      norm_num [completed_price_rational_projection,rationalActionPrice]
    · change pathQuote .complete (pathHistoryCache favorableCompleteS14Before) (completedPrice unitRoleUnused) (safeCompletion [.query 5]) = _
      have hs : pathSuffix (pathHistoryCache favorableCompleteS14Before) (safeCompletion [.query 5]) = [[.query 5,.normalRetriever 0,.selection 0,.width 1],[.query 5,.normalRetriever 0,.selection 0,.width 1,.stop],[.query 5,.normalRetriever 0,.selection 0,.width 1,.stop,.reranker 1],[.query 5,.normalRetriever 0,.selection 0,.width 1,.stop,.reranker 1,.topm 2],[.query 5,.normalRetriever 0,.selection 0,.width 1,.stop,.reranker 1,.topm 2,.context 0],[.query 5,.normalRetriever 0,.selection 0,.width 1,.stop,.reranker 1,.topm 2,.context 0,.answer 2]] := by decide
      unfold pathQuote
      rw [hs]
      norm_num [completed_price_rational_projection,rationalActionPrice]
    · change pathQuote .complete (pathHistoryCache favorableCompleteS14Before) (completedPrice unitRoleUnused) (safeCompletion [.query 6]) = _
      have hs : pathSuffix (pathHistoryCache favorableCompleteS14Before) (safeCompletion [.query 6]) = [[.query 6,.normalRetriever 0,.selection 0,.width 1],[.query 6,.normalRetriever 0,.selection 0,.width 1,.stop],[.query 6,.normalRetriever 0,.selection 0,.width 1,.stop,.reranker 1],[.query 6,.normalRetriever 0,.selection 0,.width 1,.stop,.reranker 1,.topm 2],[.query 6,.normalRetriever 0,.selection 0,.width 1,.stop,.reranker 1,.topm 2,.context 0],[.query 6,.normalRetriever 0,.selection 0,.width 1,.stop,.reranker 1,.topm 2,.context 0,.answer 2]] := by decide
      unfold pathQuote
      rw [hs]
      norm_num [completed_price_rational_projection,rationalActionPrice]
    · change pathQuote .complete (pathHistoryCache favorableCompleteS14Before) (completedPrice unitRoleUnused) (safeCompletion [.query 7]) = _
      have hs : pathSuffix (pathHistoryCache favorableCompleteS14Before) (safeCompletion [.query 7]) = [[.query 7,.normalRetriever 0,.selection 0,.width 1],[.query 7,.normalRetriever 0,.selection 0,.width 1,.stop],[.query 7,.normalRetriever 0,.selection 0,.width 1,.stop,.reranker 1],[.query 7,.normalRetriever 0,.selection 0,.width 1,.stop,.reranker 1,.topm 2],[.query 7,.normalRetriever 0,.selection 0,.width 1,.stop,.reranker 1,.topm 2,.context 0],[.query 7,.normalRetriever 0,.selection 0,.width 1,.stop,.reranker 1,.topm 2,.context 0,.answer 2]] := by decide
      unfold pathQuote
      rw [hs]
      norm_num [completed_price_rational_projection,rationalActionPrice]

theorem favorableCompleteS14D1I0 : indexScore (7/5) (controlPenalty savedCref uniformQuoteError unitRoleUnused .complete) favorableCompleteS14Before [.query 1] (.hydeRetriever 1) = treeIndex ((1/1)/2) (7/5) 0 6 2 := by
  have hs : replayBackup favorableCompleteS14Before emptyStatistics ([.query 1]++[.hydeRetriever 1]) = ⟨2,(1/1)⟩ := by
    rw [replayBackup_empty_closed_form]
    simp +decide [backedEvents,favorableCompleteS14Before,favorableCompleteProposal,favorableCompleteEvent1,favorableCompleteEvent2,favorableCompleteEvent3,favorableCompleteEvent4,favorableCompleteEvent5,favorableCompleteEvent6,favorableCompleteEvent7,favorableCompleteEvent8,favorableCompleteEvent9,favorableCompleteEvent10,favorableCompleteEvent11,favorableCompleteEvent12,favorableCompleteEvent13,taskReward]
    <;> norm_num
  have hp : rawVisits favorableCompleteS14Before [.query 1] = 6 := by decide
  have hn : rawVisits favorableCompleteS14Before ([.query 1]++[.hydeRetriever 1]) = 2 := by decide
  have hz : (controlPenalty savedCref uniformQuoteError unitRoleUnused .complete) favorableCompleteS14Before [.query 1] (.hydeRetriever 1) = 0 := control_penalty_empty_suffix _ _ _ _ _ _ (by decide)
  unfold indexScore
  rw [hs,hp,hn,hz]
  simp only [BackupStat.mean]
  norm_num

theorem favorableCompleteS14D1I1 : indexScore (7/5) (controlPenalty savedCref uniformQuoteError unitRoleUnused .complete) favorableCompleteS14Before [.query 1] (.hydeRetriever 0) = treeIndex ((0/1)/2) (7/5) 0 6 2 := by
  have hs : replayBackup favorableCompleteS14Before emptyStatistics ([.query 1]++[.hydeRetriever 0]) = ⟨2,(0/1)⟩ := by
    rw [replayBackup_empty_closed_form]
    simp +decide [backedEvents,favorableCompleteS14Before,favorableCompleteProposal,favorableCompleteEvent1,favorableCompleteEvent2,favorableCompleteEvent3,favorableCompleteEvent4,favorableCompleteEvent5,favorableCompleteEvent6,favorableCompleteEvent7,favorableCompleteEvent8,favorableCompleteEvent9,favorableCompleteEvent10,favorableCompleteEvent11,favorableCompleteEvent12,favorableCompleteEvent13,taskReward]
    <;> norm_num
  have hp : rawVisits favorableCompleteS14Before [.query 1] = 6 := by decide
  have hn : rawVisits favorableCompleteS14Before ([.query 1]++[.hydeRetriever 0]) = 2 := by decide
  have hz : (controlPenalty savedCref uniformQuoteError unitRoleUnused .complete) favorableCompleteS14Before [.query 1] (.hydeRetriever 0) = 0 := control_penalty_empty_suffix _ _ _ _ _ _ (by decide)
  unfold indexScore
  rw [hs,hp,hn,hz]
  simp only [BackupStat.mean]
  norm_num

theorem favorableCompleteS14D1I2 : indexScore (7/5) (controlPenalty savedCref uniformQuoteError unitRoleUnused .complete) favorableCompleteS14Before [.query 1] (.hydeRetriever 2) = treeIndex ((0/1)/1) (7/5) 0 6 1 := by
  have hs : replayBackup favorableCompleteS14Before emptyStatistics ([.query 1]++[.hydeRetriever 2]) = ⟨1,(0/1)⟩ := by
    rw [replayBackup_empty_closed_form]
    simp +decide [backedEvents,favorableCompleteS14Before,favorableCompleteProposal,favorableCompleteEvent1,favorableCompleteEvent2,favorableCompleteEvent3,favorableCompleteEvent4,favorableCompleteEvent5,favorableCompleteEvent6,favorableCompleteEvent7,favorableCompleteEvent8,favorableCompleteEvent9,favorableCompleteEvent10,favorableCompleteEvent11,favorableCompleteEvent12,favorableCompleteEvent13,taskReward]
    <;> norm_num
  have hp : rawVisits favorableCompleteS14Before [.query 1] = 6 := by decide
  have hn : rawVisits favorableCompleteS14Before ([.query 1]++[.hydeRetriever 2]) = 1 := by decide
  have hz : (controlPenalty savedCref uniformQuoteError unitRoleUnused .complete) favorableCompleteS14Before [.query 1] (.hydeRetriever 2) = 0 := control_penalty_empty_suffix _ _ _ _ _ _ (by decide)
  unfold indexScore
  rw [hs,hp,hn,hz]
  simp only [BackupStat.mean]
  norm_num

theorem favorableCompleteS14D1Cmp0 : indexScore (7/5) (controlPenalty savedCref uniformQuoteError unitRoleUnused .complete) favorableCompleteS14Before [.query 1] (.hydeRetriever 1) < indexScore (7/5) (controlPenalty savedCref uniformQuoteError unitRoleUnused .complete) favorableCompleteS14Before [.query 1] (.hydeRetriever 2) := by
  rw [favorableCompleteS14D1I0,favorableCompleteS14D1I2]
  have h := index_strict_order_from_intervals ((0/1)/1) ((1/1)/2) 0 0 (24411779/12500000) (69046943/50000000)
    (treeBonus (7/5) 6 1) (treeBonus (7/5) 6 2)
    (trajectory_bonus_6_1).1 (trajectory_bonus_6_2).2 (by norm_num)
  simpa only [treeIndex,sub_zero] using h

theorem favorableCompleteS14D1Cmp1 : indexScore (7/5) (controlPenalty savedCref uniformQuoteError unitRoleUnused .complete) favorableCompleteS14Before [.query 1] (.hydeRetriever 0) < indexScore (7/5) (controlPenalty savedCref uniformQuoteError unitRoleUnused .complete) favorableCompleteS14Before [.query 1] (.hydeRetriever 2) := by
  rw [favorableCompleteS14D1I1,favorableCompleteS14D1I2]
  have h := index_strict_order_from_intervals ((0/1)/1) ((0/1)/2) 0 0 (24411779/12500000) (69046943/50000000)
    (treeBonus (7/5) 6 1) (treeBonus (7/5) 6 2)
    (trajectory_bonus_6_1).1 (trajectory_bonus_6_2).2 (by norm_num)
  simpa only [treeIndex,sub_zero] using h

theorem favorableCompleteS14Choice1 : nativeFirstChoice (indexScore (7/5) (controlPenalty savedCref uniformQuoteError unitRoleUnused .complete) favorableCompleteS14Before [.query 1]) favorableCompleteS14Before [.query 1] = .hydeRetriever 2 := by
  apply visited_choice_from_ordered_certificate _ _ [.query 1] [.hydeRetriever 1,.hydeRetriever 0] [] (.hydeRetriever 2) (by decide)
  · intro a ha
    have ho : orderedLegalAvailable [.query 1] = [.hydeRetriever 1,.hydeRetriever 0,.hydeRetriever 2] := by decide
    rw [ho] at ha
    simp only [List.mem_cons,List.not_mem_nil,or_false] at ha
    rcases ha with rfl | rfl | rfl <;> decide
  · intro a ha
    simp only [List.mem_cons,List.not_mem_nil,or_false] at ha
    rcases ha with rfl | rfl
    · exact favorableCompleteS14D1Cmp0
    · exact favorableCompleteS14D1Cmp1
  · simp

theorem favorableCompleteS14ActualEvent : nativeEvent budgetTape (7/5) (controlPenalty savedCref uniformQuoteError unitRoleUnused .complete)
    (taskReward false (2/5) (1/2)) favorableCompleteS14Before = favorableCompleteEvent14 := by
  have hs0 := native_select_existing_step budgetTape (7/5) (controlPenalty savedCref uniformQuoteError unitRoleUnused .complete) favorableCompleteS14Before 8 [] (.query 1)
    (by decide) (by decide) favorableCompleteS14Choice0
  have hs1 := native_select_existing_step budgetTape (7/5) (controlPenalty savedCref uniformQuoteError unitRoleUnused .complete) favorableCompleteS14Before 7 [.query 1] (.hydeRetriever 2)
    (by decide) (by decide) favorableCompleteS14Choice1
  have hnew := native_select_new_step budgetTape (7/5) (controlPenalty savedCref uniformQuoteError unitRoleUnused .complete) favorableCompleteS14Before 6 [.query 1,.hydeRetriever 2]
    [.selection 1,.selection 2,.selection 3,.selection 0] (.selection 0) (by decide) (by decide) (by decide) (by decide)
  have hs : nativeSelect budgetTape (7/5) (controlPenalty savedCref uniformQuoteError unitRoleUnused .complete) favorableCompleteS14Before 9 [] = [.query 1,.hydeRetriever 2,.selection 0] := by
    rw [hs0]
    change nativeSelect budgetTape (7/5) (controlPenalty savedCref uniformQuoteError unitRoleUnused .complete) favorableCompleteS14Before 8 [.query 1] = _
    rw [hs1]
    change nativeSelect budgetTape (7/5) (controlPenalty savedCref uniformQuoteError unitRoleUnused .complete) favorableCompleteS14Before 7 [.query 1,.hydeRetriever 2] = _
    rw [hnew] <;> rfl
  have hr : repairedRollout budgetTape favorableCompleteS14Before 9 [.query 1,.hydeRetriever 2,.selection 0] = [.query 1,.hydeRetriever 2,.selection 0,.width 0,.stop,.reranker 0,.topm 2,.context 0,.answer 2] := by decide
  simp only [nativeEvent,hs,hr]
  rfl

def favorableCompleteS15Before := favorableCompleteProposal.take 14

theorem favorableCompleteS15Choice0 : nativeFirstChoice (indexScore (7/5) (controlPenalty savedCref uniformQuoteError unitRoleUnused .complete) favorableCompleteS15Before []) favorableCompleteS15Before [] = .query 1 := by
  apply complete_root_from_physical_gap favorableCompleteS15Before (favorableComplete_prefix_rewards 14) (by decide)
  · intro q; fin_cases q <;> decide
  · decide
  · intro q hq
    fin_cases q
    · change pathQuote .complete (pathHistoryCache favorableCompleteS15Before) (completedPrice unitRoleUnused) (safeCompletion [.query 0]) = _
      have hs : pathSuffix (pathHistoryCache favorableCompleteS15Before) (safeCompletion [.query 0]) = [[.query 0,.normalRetriever 0,.selection 0,.width 1],[.query 0,.normalRetriever 0,.selection 0,.width 1,.stop],[.query 0,.normalRetriever 0,.selection 0,.width 1,.stop,.reranker 1],[.query 0,.normalRetriever 0,.selection 0,.width 1,.stop,.reranker 1,.topm 2],[.query 0,.normalRetriever 0,.selection 0,.width 1,.stop,.reranker 1,.topm 2,.context 0],[.query 0,.normalRetriever 0,.selection 0,.width 1,.stop,.reranker 1,.topm 2,.context 0,.answer 2]] := by decide
      unfold pathQuote
      rw [hs]
      norm_num [completed_price_rational_projection,rationalActionPrice]
    · exact (hq rfl).elim
    · change pathQuote .complete (pathHistoryCache favorableCompleteS15Before) (completedPrice unitRoleUnused) (safeCompletion [.query 2]) = _
      have hs : pathSuffix (pathHistoryCache favorableCompleteS15Before) (safeCompletion [.query 2]) = [[.query 2,.normalRetriever 0,.selection 0,.width 1],[.query 2,.normalRetriever 0,.selection 0,.width 1,.stop],[.query 2,.normalRetriever 0,.selection 0,.width 1,.stop,.reranker 1],[.query 2,.normalRetriever 0,.selection 0,.width 1,.stop,.reranker 1,.topm 2],[.query 2,.normalRetriever 0,.selection 0,.width 1,.stop,.reranker 1,.topm 2,.context 0],[.query 2,.normalRetriever 0,.selection 0,.width 1,.stop,.reranker 1,.topm 2,.context 0,.answer 2]] := by decide
      unfold pathQuote
      rw [hs]
      norm_num [completed_price_rational_projection,rationalActionPrice]
    · change pathQuote .complete (pathHistoryCache favorableCompleteS15Before) (completedPrice unitRoleUnused) (safeCompletion [.query 3]) = _
      have hs : pathSuffix (pathHistoryCache favorableCompleteS15Before) (safeCompletion [.query 3]) = [[.query 3,.normalRetriever 0,.selection 0,.width 1],[.query 3,.normalRetriever 0,.selection 0,.width 1,.stop],[.query 3,.normalRetriever 0,.selection 0,.width 1,.stop,.reranker 1],[.query 3,.normalRetriever 0,.selection 0,.width 1,.stop,.reranker 1,.topm 2],[.query 3,.normalRetriever 0,.selection 0,.width 1,.stop,.reranker 1,.topm 2,.context 0],[.query 3,.normalRetriever 0,.selection 0,.width 1,.stop,.reranker 1,.topm 2,.context 0,.answer 2]] := by decide
      unfold pathQuote
      rw [hs]
      norm_num [completed_price_rational_projection,rationalActionPrice]
    · change pathQuote .complete (pathHistoryCache favorableCompleteS15Before) (completedPrice unitRoleUnused) (safeCompletion [.query 4]) = _
      have hs : pathSuffix (pathHistoryCache favorableCompleteS15Before) (safeCompletion [.query 4]) = [[.query 4,.normalRetriever 0,.selection 0,.width 1],[.query 4,.normalRetriever 0,.selection 0,.width 1,.stop],[.query 4,.normalRetriever 0,.selection 0,.width 1,.stop,.reranker 1],[.query 4,.normalRetriever 0,.selection 0,.width 1,.stop,.reranker 1,.topm 2],[.query 4,.normalRetriever 0,.selection 0,.width 1,.stop,.reranker 1,.topm 2,.context 0],[.query 4,.normalRetriever 0,.selection 0,.width 1,.stop,.reranker 1,.topm 2,.context 0,.answer 2]] := by decide
      unfold pathQuote
      rw [hs]
      norm_num [completed_price_rational_projection,rationalActionPrice]
    · change pathQuote .complete (pathHistoryCache favorableCompleteS15Before) (completedPrice unitRoleUnused) (safeCompletion [.query 5]) = _
      have hs : pathSuffix (pathHistoryCache favorableCompleteS15Before) (safeCompletion [.query 5]) = [[.query 5,.normalRetriever 0,.selection 0,.width 1],[.query 5,.normalRetriever 0,.selection 0,.width 1,.stop],[.query 5,.normalRetriever 0,.selection 0,.width 1,.stop,.reranker 1],[.query 5,.normalRetriever 0,.selection 0,.width 1,.stop,.reranker 1,.topm 2],[.query 5,.normalRetriever 0,.selection 0,.width 1,.stop,.reranker 1,.topm 2,.context 0],[.query 5,.normalRetriever 0,.selection 0,.width 1,.stop,.reranker 1,.topm 2,.context 0,.answer 2]] := by decide
      unfold pathQuote
      rw [hs]
      norm_num [completed_price_rational_projection,rationalActionPrice]
    · change pathQuote .complete (pathHistoryCache favorableCompleteS15Before) (completedPrice unitRoleUnused) (safeCompletion [.query 6]) = _
      have hs : pathSuffix (pathHistoryCache favorableCompleteS15Before) (safeCompletion [.query 6]) = [[.query 6,.normalRetriever 0,.selection 0,.width 1],[.query 6,.normalRetriever 0,.selection 0,.width 1,.stop],[.query 6,.normalRetriever 0,.selection 0,.width 1,.stop,.reranker 1],[.query 6,.normalRetriever 0,.selection 0,.width 1,.stop,.reranker 1,.topm 2],[.query 6,.normalRetriever 0,.selection 0,.width 1,.stop,.reranker 1,.topm 2,.context 0],[.query 6,.normalRetriever 0,.selection 0,.width 1,.stop,.reranker 1,.topm 2,.context 0,.answer 2]] := by decide
      unfold pathQuote
      rw [hs]
      norm_num [completed_price_rational_projection,rationalActionPrice]
    · change pathQuote .complete (pathHistoryCache favorableCompleteS15Before) (completedPrice unitRoleUnused) (safeCompletion [.query 7]) = _
      have hs : pathSuffix (pathHistoryCache favorableCompleteS15Before) (safeCompletion [.query 7]) = [[.query 7,.normalRetriever 0,.selection 0,.width 1],[.query 7,.normalRetriever 0,.selection 0,.width 1,.stop],[.query 7,.normalRetriever 0,.selection 0,.width 1,.stop,.reranker 1],[.query 7,.normalRetriever 0,.selection 0,.width 1,.stop,.reranker 1,.topm 2],[.query 7,.normalRetriever 0,.selection 0,.width 1,.stop,.reranker 1,.topm 2,.context 0],[.query 7,.normalRetriever 0,.selection 0,.width 1,.stop,.reranker 1,.topm 2,.context 0,.answer 2]] := by decide
      unfold pathQuote
      rw [hs]
      norm_num [completed_price_rational_projection,rationalActionPrice]

theorem favorableCompleteS15D1I0 : indexScore (7/5) (controlPenalty savedCref uniformQuoteError unitRoleUnused .complete) favorableCompleteS15Before [.query 1] (.hydeRetriever 1) = treeIndex ((1/1)/2) (7/5) 0 7 2 := by
  have hs : replayBackup favorableCompleteS15Before emptyStatistics ([.query 1]++[.hydeRetriever 1]) = ⟨2,(1/1)⟩ := by
    rw [replayBackup_empty_closed_form]
    simp +decide [backedEvents,favorableCompleteS15Before,favorableCompleteProposal,favorableCompleteEvent1,favorableCompleteEvent2,favorableCompleteEvent3,favorableCompleteEvent4,favorableCompleteEvent5,favorableCompleteEvent6,favorableCompleteEvent7,favorableCompleteEvent8,favorableCompleteEvent9,favorableCompleteEvent10,favorableCompleteEvent11,favorableCompleteEvent12,favorableCompleteEvent13,favorableCompleteEvent14,taskReward]
    <;> norm_num
  have hp : rawVisits favorableCompleteS15Before [.query 1] = 7 := by decide
  have hn : rawVisits favorableCompleteS15Before ([.query 1]++[.hydeRetriever 1]) = 2 := by decide
  have hz : (controlPenalty savedCref uniformQuoteError unitRoleUnused .complete) favorableCompleteS15Before [.query 1] (.hydeRetriever 1) = 0 := control_penalty_empty_suffix _ _ _ _ _ _ (by decide)
  unfold indexScore
  rw [hs,hp,hn,hz]
  simp only [BackupStat.mean]
  norm_num

theorem favorableCompleteS15D1I1 : indexScore (7/5) (controlPenalty savedCref uniformQuoteError unitRoleUnused .complete) favorableCompleteS15Before [.query 1] (.hydeRetriever 0) = treeIndex ((0/1)/2) (7/5) 0 7 2 := by
  have hs : replayBackup favorableCompleteS15Before emptyStatistics ([.query 1]++[.hydeRetriever 0]) = ⟨2,(0/1)⟩ := by
    rw [replayBackup_empty_closed_form]
    simp +decide [backedEvents,favorableCompleteS15Before,favorableCompleteProposal,favorableCompleteEvent1,favorableCompleteEvent2,favorableCompleteEvent3,favorableCompleteEvent4,favorableCompleteEvent5,favorableCompleteEvent6,favorableCompleteEvent7,favorableCompleteEvent8,favorableCompleteEvent9,favorableCompleteEvent10,favorableCompleteEvent11,favorableCompleteEvent12,favorableCompleteEvent13,favorableCompleteEvent14,taskReward]
    <;> norm_num
  have hp : rawVisits favorableCompleteS15Before [.query 1] = 7 := by decide
  have hn : rawVisits favorableCompleteS15Before ([.query 1]++[.hydeRetriever 0]) = 2 := by decide
  have hz : (controlPenalty savedCref uniformQuoteError unitRoleUnused .complete) favorableCompleteS15Before [.query 1] (.hydeRetriever 0) = 0 := control_penalty_empty_suffix _ _ _ _ _ _ (by decide)
  unfold indexScore
  rw [hs,hp,hn,hz]
  simp only [BackupStat.mean]
  norm_num

theorem favorableCompleteS15D1I2 : indexScore (7/5) (controlPenalty savedCref uniformQuoteError unitRoleUnused .complete) favorableCompleteS15Before [.query 1] (.hydeRetriever 2) = treeIndex ((0/1)/2) (7/5) 0 7 2 := by
  have hs : replayBackup favorableCompleteS15Before emptyStatistics ([.query 1]++[.hydeRetriever 2]) = ⟨2,(0/1)⟩ := by
    rw [replayBackup_empty_closed_form]
    simp +decide [backedEvents,favorableCompleteS15Before,favorableCompleteProposal,favorableCompleteEvent1,favorableCompleteEvent2,favorableCompleteEvent3,favorableCompleteEvent4,favorableCompleteEvent5,favorableCompleteEvent6,favorableCompleteEvent7,favorableCompleteEvent8,favorableCompleteEvent9,favorableCompleteEvent10,favorableCompleteEvent11,favorableCompleteEvent12,favorableCompleteEvent13,favorableCompleteEvent14,taskReward]
    <;> norm_num
  have hp : rawVisits favorableCompleteS15Before [.query 1] = 7 := by decide
  have hn : rawVisits favorableCompleteS15Before ([.query 1]++[.hydeRetriever 2]) = 2 := by decide
  have hz : (controlPenalty savedCref uniformQuoteError unitRoleUnused .complete) favorableCompleteS15Before [.query 1] (.hydeRetriever 2) = 0 := control_penalty_empty_suffix _ _ _ _ _ _ (by decide)
  unfold indexScore
  rw [hs,hp,hn,hz]
  simp only [BackupStat.mean]
  norm_num

theorem favorableCompleteS15D1Cmp1 : indexScore (7/5) (controlPenalty savedCref uniformQuoteError unitRoleUnused .complete) favorableCompleteS15Before [.query 1] (.hydeRetriever 0) ≤ indexScore (7/5) (controlPenalty savedCref uniformQuoteError unitRoleUnused .complete) favorableCompleteS15Before [.query 1] (.hydeRetriever 1) := by
  rw [favorableCompleteS15D1I1,favorableCompleteS15D1I0]
  have h := index_weak_order_from_intervals ((1/1)/2) ((0/1)/2) 0 0 (71376683/50000000) (71376697/50000000)
    (treeBonus (7/5) 7 2) (treeBonus (7/5) 7 2)
    (trajectory_bonus_7_2).1 (trajectory_bonus_7_2).2 (by norm_num)
  simpa only [treeIndex,sub_zero] using h

theorem favorableCompleteS15D1Cmp2 : indexScore (7/5) (controlPenalty savedCref uniformQuoteError unitRoleUnused .complete) favorableCompleteS15Before [.query 1] (.hydeRetriever 2) ≤ indexScore (7/5) (controlPenalty savedCref uniformQuoteError unitRoleUnused .complete) favorableCompleteS15Before [.query 1] (.hydeRetriever 1) := by
  rw [favorableCompleteS15D1I2,favorableCompleteS15D1I0]
  have h := index_weak_order_from_intervals ((1/1)/2) ((0/1)/2) 0 0 (71376683/50000000) (71376697/50000000)
    (treeBonus (7/5) 7 2) (treeBonus (7/5) 7 2)
    (trajectory_bonus_7_2).1 (trajectory_bonus_7_2).2 (by norm_num)
  simpa only [treeIndex,sub_zero] using h

theorem favorableCompleteS15Choice1 : nativeFirstChoice (indexScore (7/5) (controlPenalty savedCref uniformQuoteError unitRoleUnused .complete) favorableCompleteS15Before [.query 1]) favorableCompleteS15Before [.query 1] = .hydeRetriever 1 := by
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
    · exact favorableCompleteS15D1Cmp1
    · exact favorableCompleteS15D1Cmp2

theorem favorableCompleteS15ActualEvent : nativeEvent budgetTape (7/5) (controlPenalty savedCref uniformQuoteError unitRoleUnused .complete)
    (taskReward false (2/5) (1/2)) favorableCompleteS15Before = favorableCompleteEvent15 := by
  have hs0 := native_select_existing_step budgetTape (7/5) (controlPenalty savedCref uniformQuoteError unitRoleUnused .complete) favorableCompleteS15Before 8 [] (.query 1)
    (by decide) (by decide) favorableCompleteS15Choice0
  have hs1 := native_select_existing_step budgetTape (7/5) (controlPenalty savedCref uniformQuoteError unitRoleUnused .complete) favorableCompleteS15Before 7 [.query 1] (.hydeRetriever 1)
    (by decide) (by decide) favorableCompleteS15Choice1
  have hnew := native_select_new_step budgetTape (7/5) (controlPenalty savedCref uniformQuoteError unitRoleUnused .complete) favorableCompleteS15Before 6 [.query 1,.hydeRetriever 1]
    [.selection 1,.selection 2,.selection 3] (.selection 1) (by decide) (by decide) (by decide) (by decide)
  have hs : nativeSelect budgetTape (7/5) (controlPenalty savedCref uniformQuoteError unitRoleUnused .complete) favorableCompleteS15Before 9 [] = [.query 1,.hydeRetriever 1,.selection 1] := by
    rw [hs0]
    change nativeSelect budgetTape (7/5) (controlPenalty savedCref uniformQuoteError unitRoleUnused .complete) favorableCompleteS15Before 8 [.query 1] = _
    rw [hs1]
    change nativeSelect budgetTape (7/5) (controlPenalty savedCref uniformQuoteError unitRoleUnused .complete) favorableCompleteS15Before 7 [.query 1,.hydeRetriever 1] = _
    rw [hnew] <;> rfl
  have hr : repairedRollout budgetTape favorableCompleteS15Before 9 [.query 1,.hydeRetriever 1,.selection 1] = [.query 1,.hydeRetriever 1,.selection 1,.width 0,.stop,.reranker 0,.topm 0,.context 0,.answer 0] := by decide
  simp only [nativeEvent,hs,hr]
  rfl

def favorableCompleteS16Before := favorableCompleteProposal.take 15

theorem favorableCompleteS16Choice0 : nativeFirstChoice (indexScore (7/5) (controlPenalty savedCref uniformQuoteError unitRoleUnused .complete) favorableCompleteS16Before []) favorableCompleteS16Before [] = .query 1 := by
  apply complete_root_from_physical_gap favorableCompleteS16Before (favorableComplete_prefix_rewards 15) (by decide)
  · intro q; fin_cases q <;> decide
  · decide
  · intro q hq
    fin_cases q
    · change pathQuote .complete (pathHistoryCache favorableCompleteS16Before) (completedPrice unitRoleUnused) (safeCompletion [.query 0]) = _
      have hs : pathSuffix (pathHistoryCache favorableCompleteS16Before) (safeCompletion [.query 0]) = [[.query 0,.normalRetriever 0,.selection 0,.width 1],[.query 0,.normalRetriever 0,.selection 0,.width 1,.stop],[.query 0,.normalRetriever 0,.selection 0,.width 1,.stop,.reranker 1],[.query 0,.normalRetriever 0,.selection 0,.width 1,.stop,.reranker 1,.topm 2],[.query 0,.normalRetriever 0,.selection 0,.width 1,.stop,.reranker 1,.topm 2,.context 0],[.query 0,.normalRetriever 0,.selection 0,.width 1,.stop,.reranker 1,.topm 2,.context 0,.answer 2]] := by decide
      unfold pathQuote
      rw [hs]
      norm_num [completed_price_rational_projection,rationalActionPrice]
    · exact (hq rfl).elim
    · change pathQuote .complete (pathHistoryCache favorableCompleteS16Before) (completedPrice unitRoleUnused) (safeCompletion [.query 2]) = _
      have hs : pathSuffix (pathHistoryCache favorableCompleteS16Before) (safeCompletion [.query 2]) = [[.query 2,.normalRetriever 0,.selection 0,.width 1],[.query 2,.normalRetriever 0,.selection 0,.width 1,.stop],[.query 2,.normalRetriever 0,.selection 0,.width 1,.stop,.reranker 1],[.query 2,.normalRetriever 0,.selection 0,.width 1,.stop,.reranker 1,.topm 2],[.query 2,.normalRetriever 0,.selection 0,.width 1,.stop,.reranker 1,.topm 2,.context 0],[.query 2,.normalRetriever 0,.selection 0,.width 1,.stop,.reranker 1,.topm 2,.context 0,.answer 2]] := by decide
      unfold pathQuote
      rw [hs]
      norm_num [completed_price_rational_projection,rationalActionPrice]
    · change pathQuote .complete (pathHistoryCache favorableCompleteS16Before) (completedPrice unitRoleUnused) (safeCompletion [.query 3]) = _
      have hs : pathSuffix (pathHistoryCache favorableCompleteS16Before) (safeCompletion [.query 3]) = [[.query 3,.normalRetriever 0,.selection 0,.width 1],[.query 3,.normalRetriever 0,.selection 0,.width 1,.stop],[.query 3,.normalRetriever 0,.selection 0,.width 1,.stop,.reranker 1],[.query 3,.normalRetriever 0,.selection 0,.width 1,.stop,.reranker 1,.topm 2],[.query 3,.normalRetriever 0,.selection 0,.width 1,.stop,.reranker 1,.topm 2,.context 0],[.query 3,.normalRetriever 0,.selection 0,.width 1,.stop,.reranker 1,.topm 2,.context 0,.answer 2]] := by decide
      unfold pathQuote
      rw [hs]
      norm_num [completed_price_rational_projection,rationalActionPrice]
    · change pathQuote .complete (pathHistoryCache favorableCompleteS16Before) (completedPrice unitRoleUnused) (safeCompletion [.query 4]) = _
      have hs : pathSuffix (pathHistoryCache favorableCompleteS16Before) (safeCompletion [.query 4]) = [[.query 4,.normalRetriever 0,.selection 0,.width 1],[.query 4,.normalRetriever 0,.selection 0,.width 1,.stop],[.query 4,.normalRetriever 0,.selection 0,.width 1,.stop,.reranker 1],[.query 4,.normalRetriever 0,.selection 0,.width 1,.stop,.reranker 1,.topm 2],[.query 4,.normalRetriever 0,.selection 0,.width 1,.stop,.reranker 1,.topm 2,.context 0],[.query 4,.normalRetriever 0,.selection 0,.width 1,.stop,.reranker 1,.topm 2,.context 0,.answer 2]] := by decide
      unfold pathQuote
      rw [hs]
      norm_num [completed_price_rational_projection,rationalActionPrice]
    · change pathQuote .complete (pathHistoryCache favorableCompleteS16Before) (completedPrice unitRoleUnused) (safeCompletion [.query 5]) = _
      have hs : pathSuffix (pathHistoryCache favorableCompleteS16Before) (safeCompletion [.query 5]) = [[.query 5,.normalRetriever 0,.selection 0,.width 1],[.query 5,.normalRetriever 0,.selection 0,.width 1,.stop],[.query 5,.normalRetriever 0,.selection 0,.width 1,.stop,.reranker 1],[.query 5,.normalRetriever 0,.selection 0,.width 1,.stop,.reranker 1,.topm 2],[.query 5,.normalRetriever 0,.selection 0,.width 1,.stop,.reranker 1,.topm 2,.context 0],[.query 5,.normalRetriever 0,.selection 0,.width 1,.stop,.reranker 1,.topm 2,.context 0,.answer 2]] := by decide
      unfold pathQuote
      rw [hs]
      norm_num [completed_price_rational_projection,rationalActionPrice]
    · change pathQuote .complete (pathHistoryCache favorableCompleteS16Before) (completedPrice unitRoleUnused) (safeCompletion [.query 6]) = _
      have hs : pathSuffix (pathHistoryCache favorableCompleteS16Before) (safeCompletion [.query 6]) = [[.query 6,.normalRetriever 0,.selection 0,.width 1],[.query 6,.normalRetriever 0,.selection 0,.width 1,.stop],[.query 6,.normalRetriever 0,.selection 0,.width 1,.stop,.reranker 1],[.query 6,.normalRetriever 0,.selection 0,.width 1,.stop,.reranker 1,.topm 2],[.query 6,.normalRetriever 0,.selection 0,.width 1,.stop,.reranker 1,.topm 2,.context 0],[.query 6,.normalRetriever 0,.selection 0,.width 1,.stop,.reranker 1,.topm 2,.context 0,.answer 2]] := by decide
      unfold pathQuote
      rw [hs]
      norm_num [completed_price_rational_projection,rationalActionPrice]
    · change pathQuote .complete (pathHistoryCache favorableCompleteS16Before) (completedPrice unitRoleUnused) (safeCompletion [.query 7]) = _
      have hs : pathSuffix (pathHistoryCache favorableCompleteS16Before) (safeCompletion [.query 7]) = [[.query 7,.normalRetriever 0,.selection 0,.width 1],[.query 7,.normalRetriever 0,.selection 0,.width 1,.stop],[.query 7,.normalRetriever 0,.selection 0,.width 1,.stop,.reranker 1],[.query 7,.normalRetriever 0,.selection 0,.width 1,.stop,.reranker 1,.topm 2],[.query 7,.normalRetriever 0,.selection 0,.width 1,.stop,.reranker 1,.topm 2,.context 0],[.query 7,.normalRetriever 0,.selection 0,.width 1,.stop,.reranker 1,.topm 2,.context 0,.answer 2]] := by decide
      unfold pathQuote
      rw [hs]
      norm_num [completed_price_rational_projection,rationalActionPrice]

theorem favorableCompleteS16D1I0 : indexScore (7/5) (controlPenalty savedCref uniformQuoteError unitRoleUnused .complete) favorableCompleteS16Before [.query 1] (.hydeRetriever 1) = treeIndex ((1/1)/3) (7/5) 0 8 3 := by
  have hs : replayBackup favorableCompleteS16Before emptyStatistics ([.query 1]++[.hydeRetriever 1]) = ⟨3,(1/1)⟩ := by
    rw [replayBackup_empty_closed_form]
    simp +decide [backedEvents,favorableCompleteS16Before,favorableCompleteProposal,favorableCompleteEvent1,favorableCompleteEvent2,favorableCompleteEvent3,favorableCompleteEvent4,favorableCompleteEvent5,favorableCompleteEvent6,favorableCompleteEvent7,favorableCompleteEvent8,favorableCompleteEvent9,favorableCompleteEvent10,favorableCompleteEvent11,favorableCompleteEvent12,favorableCompleteEvent13,favorableCompleteEvent14,favorableCompleteEvent15,taskReward]
    <;> norm_num
  have hp : rawVisits favorableCompleteS16Before [.query 1] = 8 := by decide
  have hn : rawVisits favorableCompleteS16Before ([.query 1]++[.hydeRetriever 1]) = 3 := by decide
  have hz : (controlPenalty savedCref uniformQuoteError unitRoleUnused .complete) favorableCompleteS16Before [.query 1] (.hydeRetriever 1) = 0 := control_penalty_empty_suffix _ _ _ _ _ _ (by decide)
  unfold indexScore
  rw [hs,hp,hn,hz]
  simp only [BackupStat.mean]
  norm_num

theorem favorableCompleteS16D1I1 : indexScore (7/5) (controlPenalty savedCref uniformQuoteError unitRoleUnused .complete) favorableCompleteS16Before [.query 1] (.hydeRetriever 0) = treeIndex ((0/1)/2) (7/5) 0 8 2 := by
  have hs : replayBackup favorableCompleteS16Before emptyStatistics ([.query 1]++[.hydeRetriever 0]) = ⟨2,(0/1)⟩ := by
    rw [replayBackup_empty_closed_form]
    simp +decide [backedEvents,favorableCompleteS16Before,favorableCompleteProposal,favorableCompleteEvent1,favorableCompleteEvent2,favorableCompleteEvent3,favorableCompleteEvent4,favorableCompleteEvent5,favorableCompleteEvent6,favorableCompleteEvent7,favorableCompleteEvent8,favorableCompleteEvent9,favorableCompleteEvent10,favorableCompleteEvent11,favorableCompleteEvent12,favorableCompleteEvent13,favorableCompleteEvent14,favorableCompleteEvent15,taskReward]
    <;> norm_num
  have hp : rawVisits favorableCompleteS16Before [.query 1] = 8 := by decide
  have hn : rawVisits favorableCompleteS16Before ([.query 1]++[.hydeRetriever 0]) = 2 := by decide
  have hz : (controlPenalty savedCref uniformQuoteError unitRoleUnused .complete) favorableCompleteS16Before [.query 1] (.hydeRetriever 0) = 0 := control_penalty_empty_suffix _ _ _ _ _ _ (by decide)
  unfold indexScore
  rw [hs,hp,hn,hz]
  simp only [BackupStat.mean]
  norm_num

theorem favorableCompleteS16D1I2 : indexScore (7/5) (controlPenalty savedCref uniformQuoteError unitRoleUnused .complete) favorableCompleteS16Before [.query 1] (.hydeRetriever 2) = treeIndex ((0/1)/2) (7/5) 0 8 2 := by
  have hs : replayBackup favorableCompleteS16Before emptyStatistics ([.query 1]++[.hydeRetriever 2]) = ⟨2,(0/1)⟩ := by
    rw [replayBackup_empty_closed_form]
    simp +decide [backedEvents,favorableCompleteS16Before,favorableCompleteProposal,favorableCompleteEvent1,favorableCompleteEvent2,favorableCompleteEvent3,favorableCompleteEvent4,favorableCompleteEvent5,favorableCompleteEvent6,favorableCompleteEvent7,favorableCompleteEvent8,favorableCompleteEvent9,favorableCompleteEvent10,favorableCompleteEvent11,favorableCompleteEvent12,favorableCompleteEvent13,favorableCompleteEvent14,favorableCompleteEvent15,taskReward]
    <;> norm_num
  have hp : rawVisits favorableCompleteS16Before [.query 1] = 8 := by decide
  have hn : rawVisits favorableCompleteS16Before ([.query 1]++[.hydeRetriever 2]) = 2 := by decide
  have hz : (controlPenalty savedCref uniformQuoteError unitRoleUnused .complete) favorableCompleteS16Before [.query 1] (.hydeRetriever 2) = 0 := control_penalty_empty_suffix _ _ _ _ _ _ (by decide)
  unfold indexScore
  rw [hs,hp,hn,hz]
  simp only [BackupStat.mean]
  norm_num

theorem favorableCompleteS16D1Cmp1 : indexScore (7/5) (controlPenalty savedCref uniformQuoteError unitRoleUnused .complete) favorableCompleteS16Before [.query 1] (.hydeRetriever 0) ≤ indexScore (7/5) (controlPenalty savedCref uniformQuoteError unitRoleUnused .complete) favorableCompleteS16Before [.query 1] (.hydeRetriever 1) := by
  rw [favorableCompleteS16D1I1,favorableCompleteS16D1I0]
  have h := index_weak_order_from_intervals ((1/1)/3) ((0/1)/2) 0 0 (14976647/12500000) (1146411/781250)
    (treeBonus (7/5) 8 3) (treeBonus (7/5) 8 2)
    (trajectory_bonus_8_3).1 (trajectory_bonus_8_2).2 (by norm_num)
  simpa only [treeIndex,sub_zero] using h

theorem favorableCompleteS16D1Cmp2 : indexScore (7/5) (controlPenalty savedCref uniformQuoteError unitRoleUnused .complete) favorableCompleteS16Before [.query 1] (.hydeRetriever 2) ≤ indexScore (7/5) (controlPenalty savedCref uniformQuoteError unitRoleUnused .complete) favorableCompleteS16Before [.query 1] (.hydeRetriever 1) := by
  rw [favorableCompleteS16D1I2,favorableCompleteS16D1I0]
  have h := index_weak_order_from_intervals ((1/1)/3) ((0/1)/2) 0 0 (14976647/12500000) (1146411/781250)
    (treeBonus (7/5) 8 3) (treeBonus (7/5) 8 2)
    (trajectory_bonus_8_3).1 (trajectory_bonus_8_2).2 (by norm_num)
  simpa only [treeIndex,sub_zero] using h

theorem favorableCompleteS16Choice1 : nativeFirstChoice (indexScore (7/5) (controlPenalty savedCref uniformQuoteError unitRoleUnused .complete) favorableCompleteS16Before [.query 1]) favorableCompleteS16Before [.query 1] = .hydeRetriever 1 := by
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
    · exact favorableCompleteS16D1Cmp1
    · exact favorableCompleteS16D1Cmp2

theorem favorableCompleteS16ActualEvent : nativeEvent budgetTape (7/5) (controlPenalty savedCref uniformQuoteError unitRoleUnused .complete)
    (taskReward false (2/5) (1/2)) favorableCompleteS16Before = favorableCompleteEvent16 := by
  have hs0 := native_select_existing_step budgetTape (7/5) (controlPenalty savedCref uniformQuoteError unitRoleUnused .complete) favorableCompleteS16Before 8 [] (.query 1)
    (by decide) (by decide) favorableCompleteS16Choice0
  have hs1 := native_select_existing_step budgetTape (7/5) (controlPenalty savedCref uniformQuoteError unitRoleUnused .complete) favorableCompleteS16Before 7 [.query 1] (.hydeRetriever 1)
    (by decide) (by decide) favorableCompleteS16Choice1
  have hnew := native_select_new_step budgetTape (7/5) (controlPenalty savedCref uniformQuoteError unitRoleUnused .complete) favorableCompleteS16Before 6 [.query 1,.hydeRetriever 1]
    [.selection 2,.selection 3] (.selection 2) (by decide) (by decide) (by decide) (by decide)
  have hs : nativeSelect budgetTape (7/5) (controlPenalty savedCref uniformQuoteError unitRoleUnused .complete) favorableCompleteS16Before 9 [] = [.query 1,.hydeRetriever 1,.selection 2] := by
    rw [hs0]
    change nativeSelect budgetTape (7/5) (controlPenalty savedCref uniformQuoteError unitRoleUnused .complete) favorableCompleteS16Before 8 [.query 1] = _
    rw [hs1]
    change nativeSelect budgetTape (7/5) (controlPenalty savedCref uniformQuoteError unitRoleUnused .complete) favorableCompleteS16Before 7 [.query 1,.hydeRetriever 1] = _
    rw [hnew] <;> rfl
  have hr : repairedRollout budgetTape favorableCompleteS16Before 9 [.query 1,.hydeRetriever 1,.selection 2] = [.query 1,.hydeRetriever 1,.selection 2,.width 0,.stop,.reranker 0,.topm 0,.context 0,.answer 0] := by decide
  simp only [nativeEvent,hs,hr]
  rfl

def favorableCompleteS17Before := favorableCompleteProposal.take 16

theorem favorableCompleteS17Choice0 : nativeFirstChoice (indexScore (7/5) (controlPenalty savedCref uniformQuoteError unitRoleUnused .complete) favorableCompleteS17Before []) favorableCompleteS17Before [] = .query 1 := by
  apply complete_root_from_physical_gap favorableCompleteS17Before (favorableComplete_prefix_rewards 16) (by decide)
  · intro q; fin_cases q <;> decide
  · decide
  · intro q hq
    fin_cases q
    · change pathQuote .complete (pathHistoryCache favorableCompleteS17Before) (completedPrice unitRoleUnused) (safeCompletion [.query 0]) = _
      have hs : pathSuffix (pathHistoryCache favorableCompleteS17Before) (safeCompletion [.query 0]) = [[.query 0,.normalRetriever 0,.selection 0,.width 1],[.query 0,.normalRetriever 0,.selection 0,.width 1,.stop],[.query 0,.normalRetriever 0,.selection 0,.width 1,.stop,.reranker 1],[.query 0,.normalRetriever 0,.selection 0,.width 1,.stop,.reranker 1,.topm 2],[.query 0,.normalRetriever 0,.selection 0,.width 1,.stop,.reranker 1,.topm 2,.context 0],[.query 0,.normalRetriever 0,.selection 0,.width 1,.stop,.reranker 1,.topm 2,.context 0,.answer 2]] := by decide
      unfold pathQuote
      rw [hs]
      norm_num [completed_price_rational_projection,rationalActionPrice]
    · exact (hq rfl).elim
    · change pathQuote .complete (pathHistoryCache favorableCompleteS17Before) (completedPrice unitRoleUnused) (safeCompletion [.query 2]) = _
      have hs : pathSuffix (pathHistoryCache favorableCompleteS17Before) (safeCompletion [.query 2]) = [[.query 2,.normalRetriever 0,.selection 0,.width 1],[.query 2,.normalRetriever 0,.selection 0,.width 1,.stop],[.query 2,.normalRetriever 0,.selection 0,.width 1,.stop,.reranker 1],[.query 2,.normalRetriever 0,.selection 0,.width 1,.stop,.reranker 1,.topm 2],[.query 2,.normalRetriever 0,.selection 0,.width 1,.stop,.reranker 1,.topm 2,.context 0],[.query 2,.normalRetriever 0,.selection 0,.width 1,.stop,.reranker 1,.topm 2,.context 0,.answer 2]] := by decide
      unfold pathQuote
      rw [hs]
      norm_num [completed_price_rational_projection,rationalActionPrice]
    · change pathQuote .complete (pathHistoryCache favorableCompleteS17Before) (completedPrice unitRoleUnused) (safeCompletion [.query 3]) = _
      have hs : pathSuffix (pathHistoryCache favorableCompleteS17Before) (safeCompletion [.query 3]) = [[.query 3,.normalRetriever 0,.selection 0,.width 1],[.query 3,.normalRetriever 0,.selection 0,.width 1,.stop],[.query 3,.normalRetriever 0,.selection 0,.width 1,.stop,.reranker 1],[.query 3,.normalRetriever 0,.selection 0,.width 1,.stop,.reranker 1,.topm 2],[.query 3,.normalRetriever 0,.selection 0,.width 1,.stop,.reranker 1,.topm 2,.context 0],[.query 3,.normalRetriever 0,.selection 0,.width 1,.stop,.reranker 1,.topm 2,.context 0,.answer 2]] := by decide
      unfold pathQuote
      rw [hs]
      norm_num [completed_price_rational_projection,rationalActionPrice]
    · change pathQuote .complete (pathHistoryCache favorableCompleteS17Before) (completedPrice unitRoleUnused) (safeCompletion [.query 4]) = _
      have hs : pathSuffix (pathHistoryCache favorableCompleteS17Before) (safeCompletion [.query 4]) = [[.query 4,.normalRetriever 0,.selection 0,.width 1],[.query 4,.normalRetriever 0,.selection 0,.width 1,.stop],[.query 4,.normalRetriever 0,.selection 0,.width 1,.stop,.reranker 1],[.query 4,.normalRetriever 0,.selection 0,.width 1,.stop,.reranker 1,.topm 2],[.query 4,.normalRetriever 0,.selection 0,.width 1,.stop,.reranker 1,.topm 2,.context 0],[.query 4,.normalRetriever 0,.selection 0,.width 1,.stop,.reranker 1,.topm 2,.context 0,.answer 2]] := by decide
      unfold pathQuote
      rw [hs]
      norm_num [completed_price_rational_projection,rationalActionPrice]
    · change pathQuote .complete (pathHistoryCache favorableCompleteS17Before) (completedPrice unitRoleUnused) (safeCompletion [.query 5]) = _
      have hs : pathSuffix (pathHistoryCache favorableCompleteS17Before) (safeCompletion [.query 5]) = [[.query 5,.normalRetriever 0,.selection 0,.width 1],[.query 5,.normalRetriever 0,.selection 0,.width 1,.stop],[.query 5,.normalRetriever 0,.selection 0,.width 1,.stop,.reranker 1],[.query 5,.normalRetriever 0,.selection 0,.width 1,.stop,.reranker 1,.topm 2],[.query 5,.normalRetriever 0,.selection 0,.width 1,.stop,.reranker 1,.topm 2,.context 0],[.query 5,.normalRetriever 0,.selection 0,.width 1,.stop,.reranker 1,.topm 2,.context 0,.answer 2]] := by decide
      unfold pathQuote
      rw [hs]
      norm_num [completed_price_rational_projection,rationalActionPrice]
    · change pathQuote .complete (pathHistoryCache favorableCompleteS17Before) (completedPrice unitRoleUnused) (safeCompletion [.query 6]) = _
      have hs : pathSuffix (pathHistoryCache favorableCompleteS17Before) (safeCompletion [.query 6]) = [[.query 6,.normalRetriever 0,.selection 0,.width 1],[.query 6,.normalRetriever 0,.selection 0,.width 1,.stop],[.query 6,.normalRetriever 0,.selection 0,.width 1,.stop,.reranker 1],[.query 6,.normalRetriever 0,.selection 0,.width 1,.stop,.reranker 1,.topm 2],[.query 6,.normalRetriever 0,.selection 0,.width 1,.stop,.reranker 1,.topm 2,.context 0],[.query 6,.normalRetriever 0,.selection 0,.width 1,.stop,.reranker 1,.topm 2,.context 0,.answer 2]] := by decide
      unfold pathQuote
      rw [hs]
      norm_num [completed_price_rational_projection,rationalActionPrice]
    · change pathQuote .complete (pathHistoryCache favorableCompleteS17Before) (completedPrice unitRoleUnused) (safeCompletion [.query 7]) = _
      have hs : pathSuffix (pathHistoryCache favorableCompleteS17Before) (safeCompletion [.query 7]) = [[.query 7,.normalRetriever 0,.selection 0,.width 1],[.query 7,.normalRetriever 0,.selection 0,.width 1,.stop],[.query 7,.normalRetriever 0,.selection 0,.width 1,.stop,.reranker 1],[.query 7,.normalRetriever 0,.selection 0,.width 1,.stop,.reranker 1,.topm 2],[.query 7,.normalRetriever 0,.selection 0,.width 1,.stop,.reranker 1,.topm 2,.context 0],[.query 7,.normalRetriever 0,.selection 0,.width 1,.stop,.reranker 1,.topm 2,.context 0,.answer 2]] := by decide
      unfold pathQuote
      rw [hs]
      norm_num [completed_price_rational_projection,rationalActionPrice]

theorem favorableCompleteS17D1I0 : indexScore (7/5) (controlPenalty savedCref uniformQuoteError unitRoleUnused .complete) favorableCompleteS17Before [.query 1] (.hydeRetriever 1) = treeIndex ((1/1)/4) (7/5) 0 9 4 := by
  have hs : replayBackup favorableCompleteS17Before emptyStatistics ([.query 1]++[.hydeRetriever 1]) = ⟨4,(1/1)⟩ := by
    rw [replayBackup_empty_closed_form]
    simp +decide [backedEvents,favorableCompleteS17Before,favorableCompleteProposal,favorableCompleteEvent1,favorableCompleteEvent2,favorableCompleteEvent3,favorableCompleteEvent4,favorableCompleteEvent5,favorableCompleteEvent6,favorableCompleteEvent7,favorableCompleteEvent8,favorableCompleteEvent9,favorableCompleteEvent10,favorableCompleteEvent11,favorableCompleteEvent12,favorableCompleteEvent13,favorableCompleteEvent14,favorableCompleteEvent15,favorableCompleteEvent16,taskReward]
    <;> norm_num
  have hp : rawVisits favorableCompleteS17Before [.query 1] = 9 := by decide
  have hn : rawVisits favorableCompleteS17Before ([.query 1]++[.hydeRetriever 1]) = 4 := by decide
  have hz : (controlPenalty savedCref uniformQuoteError unitRoleUnused .complete) favorableCompleteS17Before [.query 1] (.hydeRetriever 1) = 0 := control_penalty_empty_suffix _ _ _ _ _ _ (by decide)
  unfold indexScore
  rw [hs,hp,hn,hz]
  simp only [BackupStat.mean]
  norm_num

theorem favorableCompleteS17D1I1 : indexScore (7/5) (controlPenalty savedCref uniformQuoteError unitRoleUnused .complete) favorableCompleteS17Before [.query 1] (.hydeRetriever 0) = treeIndex ((0/1)/2) (7/5) 0 9 2 := by
  have hs : replayBackup favorableCompleteS17Before emptyStatistics ([.query 1]++[.hydeRetriever 0]) = ⟨2,(0/1)⟩ := by
    rw [replayBackup_empty_closed_form]
    simp +decide [backedEvents,favorableCompleteS17Before,favorableCompleteProposal,favorableCompleteEvent1,favorableCompleteEvent2,favorableCompleteEvent3,favorableCompleteEvent4,favorableCompleteEvent5,favorableCompleteEvent6,favorableCompleteEvent7,favorableCompleteEvent8,favorableCompleteEvent9,favorableCompleteEvent10,favorableCompleteEvent11,favorableCompleteEvent12,favorableCompleteEvent13,favorableCompleteEvent14,favorableCompleteEvent15,favorableCompleteEvent16,taskReward]
    <;> norm_num
  have hp : rawVisits favorableCompleteS17Before [.query 1] = 9 := by decide
  have hn : rawVisits favorableCompleteS17Before ([.query 1]++[.hydeRetriever 0]) = 2 := by decide
  have hz : (controlPenalty savedCref uniformQuoteError unitRoleUnused .complete) favorableCompleteS17Before [.query 1] (.hydeRetriever 0) = 0 := control_penalty_empty_suffix _ _ _ _ _ _ (by decide)
  unfold indexScore
  rw [hs,hp,hn,hz]
  simp only [BackupStat.mean]
  norm_num

theorem favorableCompleteS17D1I2 : indexScore (7/5) (controlPenalty savedCref uniformQuoteError unitRoleUnused .complete) favorableCompleteS17Before [.query 1] (.hydeRetriever 2) = treeIndex ((0/1)/2) (7/5) 0 9 2 := by
  have hs : replayBackup favorableCompleteS17Before emptyStatistics ([.query 1]++[.hydeRetriever 2]) = ⟨2,(0/1)⟩ := by
    rw [replayBackup_empty_closed_form]
    simp +decide [backedEvents,favorableCompleteS17Before,favorableCompleteProposal,favorableCompleteEvent1,favorableCompleteEvent2,favorableCompleteEvent3,favorableCompleteEvent4,favorableCompleteEvent5,favorableCompleteEvent6,favorableCompleteEvent7,favorableCompleteEvent8,favorableCompleteEvent9,favorableCompleteEvent10,favorableCompleteEvent11,favorableCompleteEvent12,favorableCompleteEvent13,favorableCompleteEvent14,favorableCompleteEvent15,favorableCompleteEvent16,taskReward]
    <;> norm_num
  have hp : rawVisits favorableCompleteS17Before [.query 1] = 9 := by decide
  have hn : rawVisits favorableCompleteS17Before ([.query 1]++[.hydeRetriever 2]) = 2 := by decide
  have hz : (controlPenalty savedCref uniformQuoteError unitRoleUnused .complete) favorableCompleteS17Before [.query 1] (.hydeRetriever 2) = 0 := control_penalty_empty_suffix _ _ _ _ _ _ (by decide)
  unfold indexScore
  rw [hs,hp,hn,hz]
  simp only [BackupStat.mean]
  norm_num

theorem favorableCompleteS17D1Cmp0 : indexScore (7/5) (controlPenalty savedCref uniformQuoteError unitRoleUnused .complete) favorableCompleteS17Before [.query 1] (.hydeRetriever 1) < indexScore (7/5) (controlPenalty savedCref uniformQuoteError unitRoleUnused .complete) favorableCompleteS17Before [.query 1] (.hydeRetriever 0) := by
  rw [favorableCompleteS17D1I0,favorableCompleteS17D1I1]
  have h := index_strict_order_from_intervals ((0/1)/2) ((1/1)/4) 0 0 (75108803/50000000) (829843/781250)
    (treeBonus (7/5) 9 2) (treeBonus (7/5) 9 4)
    (trajectory_bonus_9_2).1 (trajectory_bonus_9_4).2 (by norm_num)
  simpa only [treeIndex,sub_zero] using h

theorem favorableCompleteS17D1Cmp2 : indexScore (7/5) (controlPenalty savedCref uniformQuoteError unitRoleUnused .complete) favorableCompleteS17Before [.query 1] (.hydeRetriever 2) ≤ indexScore (7/5) (controlPenalty savedCref uniformQuoteError unitRoleUnused .complete) favorableCompleteS17Before [.query 1] (.hydeRetriever 0) := by
  rw [favorableCompleteS17D1I2,favorableCompleteS17D1I1]

theorem favorableCompleteS17Choice1 : nativeFirstChoice (indexScore (7/5) (controlPenalty savedCref uniformQuoteError unitRoleUnused .complete) favorableCompleteS17Before [.query 1]) favorableCompleteS17Before [.query 1] = .hydeRetriever 0 := by
  apply visited_choice_from_ordered_certificate _ _ [.query 1] [.hydeRetriever 1] [.hydeRetriever 2] (.hydeRetriever 0) (by decide)
  · intro a ha
    have ho : orderedLegalAvailable [.query 1] = [.hydeRetriever 1,.hydeRetriever 0,.hydeRetriever 2] := by decide
    rw [ho] at ha
    simp only [List.mem_cons,List.not_mem_nil,or_false] at ha
    rcases ha with rfl | rfl | rfl <;> decide
  · intro a ha
    simp only [List.mem_cons,List.not_mem_nil,or_false] at ha
    rcases ha with rfl
    · exact favorableCompleteS17D1Cmp0
  · intro a ha
    simp only [List.mem_cons,List.not_mem_nil,or_false] at ha
    rcases ha with rfl
    · exact favorableCompleteS17D1Cmp2

theorem favorableCompleteS17ActualEvent : nativeEvent budgetTape (7/5) (controlPenalty savedCref uniformQuoteError unitRoleUnused .complete)
    (taskReward false (2/5) (1/2)) favorableCompleteS17Before = favorableCompleteEvent17 := by
  have hs0 := native_select_existing_step budgetTape (7/5) (controlPenalty savedCref uniformQuoteError unitRoleUnused .complete) favorableCompleteS17Before 8 [] (.query 1)
    (by decide) (by decide) favorableCompleteS17Choice0
  have hs1 := native_select_existing_step budgetTape (7/5) (controlPenalty savedCref uniformQuoteError unitRoleUnused .complete) favorableCompleteS17Before 7 [.query 1] (.hydeRetriever 0)
    (by decide) (by decide) favorableCompleteS17Choice1
  have hnew := native_select_new_step budgetTape (7/5) (controlPenalty savedCref uniformQuoteError unitRoleUnused .complete) favorableCompleteS17Before 6 [.query 1,.hydeRetriever 0]
    [.selection 1,.selection 2,.selection 3] (.selection 1) (by decide) (by decide) (by decide) (by decide)
  have hs : nativeSelect budgetTape (7/5) (controlPenalty savedCref uniformQuoteError unitRoleUnused .complete) favorableCompleteS17Before 9 [] = [.query 1,.hydeRetriever 0,.selection 1] := by
    rw [hs0]
    change nativeSelect budgetTape (7/5) (controlPenalty savedCref uniformQuoteError unitRoleUnused .complete) favorableCompleteS17Before 8 [.query 1] = _
    rw [hs1]
    change nativeSelect budgetTape (7/5) (controlPenalty savedCref uniformQuoteError unitRoleUnused .complete) favorableCompleteS17Before 7 [.query 1,.hydeRetriever 0] = _
    rw [hnew] <;> rfl
  have hr : repairedRollout budgetTape favorableCompleteS17Before 9 [.query 1,.hydeRetriever 0,.selection 1] = [.query 1,.hydeRetriever 0,.selection 1,.width 0,.stop,.reranker 0,.topm 0,.context 0,.answer 0] := by decide
  simp only [nativeEvent,hs,hr]
  rfl

def favorableCompleteS18Before := favorableCompleteProposal.take 17

theorem favorableCompleteS18Choice0 : nativeFirstChoice (indexScore (7/5) (controlPenalty savedCref uniformQuoteError unitRoleUnused .complete) favorableCompleteS18Before []) favorableCompleteS18Before [] = .query 1 := by
  apply complete_root_from_physical_gap favorableCompleteS18Before (favorableComplete_prefix_rewards 17) (by decide)
  · intro q; fin_cases q <;> decide
  · decide
  · intro q hq
    fin_cases q
    · change pathQuote .complete (pathHistoryCache favorableCompleteS18Before) (completedPrice unitRoleUnused) (safeCompletion [.query 0]) = _
      have hs : pathSuffix (pathHistoryCache favorableCompleteS18Before) (safeCompletion [.query 0]) = [[.query 0,.normalRetriever 0,.selection 0,.width 1],[.query 0,.normalRetriever 0,.selection 0,.width 1,.stop],[.query 0,.normalRetriever 0,.selection 0,.width 1,.stop,.reranker 1],[.query 0,.normalRetriever 0,.selection 0,.width 1,.stop,.reranker 1,.topm 2],[.query 0,.normalRetriever 0,.selection 0,.width 1,.stop,.reranker 1,.topm 2,.context 0],[.query 0,.normalRetriever 0,.selection 0,.width 1,.stop,.reranker 1,.topm 2,.context 0,.answer 2]] := by decide
      unfold pathQuote
      rw [hs]
      norm_num [completed_price_rational_projection,rationalActionPrice]
    · exact (hq rfl).elim
    · change pathQuote .complete (pathHistoryCache favorableCompleteS18Before) (completedPrice unitRoleUnused) (safeCompletion [.query 2]) = _
      have hs : pathSuffix (pathHistoryCache favorableCompleteS18Before) (safeCompletion [.query 2]) = [[.query 2,.normalRetriever 0,.selection 0,.width 1],[.query 2,.normalRetriever 0,.selection 0,.width 1,.stop],[.query 2,.normalRetriever 0,.selection 0,.width 1,.stop,.reranker 1],[.query 2,.normalRetriever 0,.selection 0,.width 1,.stop,.reranker 1,.topm 2],[.query 2,.normalRetriever 0,.selection 0,.width 1,.stop,.reranker 1,.topm 2,.context 0],[.query 2,.normalRetriever 0,.selection 0,.width 1,.stop,.reranker 1,.topm 2,.context 0,.answer 2]] := by decide
      unfold pathQuote
      rw [hs]
      norm_num [completed_price_rational_projection,rationalActionPrice]
    · change pathQuote .complete (pathHistoryCache favorableCompleteS18Before) (completedPrice unitRoleUnused) (safeCompletion [.query 3]) = _
      have hs : pathSuffix (pathHistoryCache favorableCompleteS18Before) (safeCompletion [.query 3]) = [[.query 3,.normalRetriever 0,.selection 0,.width 1],[.query 3,.normalRetriever 0,.selection 0,.width 1,.stop],[.query 3,.normalRetriever 0,.selection 0,.width 1,.stop,.reranker 1],[.query 3,.normalRetriever 0,.selection 0,.width 1,.stop,.reranker 1,.topm 2],[.query 3,.normalRetriever 0,.selection 0,.width 1,.stop,.reranker 1,.topm 2,.context 0],[.query 3,.normalRetriever 0,.selection 0,.width 1,.stop,.reranker 1,.topm 2,.context 0,.answer 2]] := by decide
      unfold pathQuote
      rw [hs]
      norm_num [completed_price_rational_projection,rationalActionPrice]
    · change pathQuote .complete (pathHistoryCache favorableCompleteS18Before) (completedPrice unitRoleUnused) (safeCompletion [.query 4]) = _
      have hs : pathSuffix (pathHistoryCache favorableCompleteS18Before) (safeCompletion [.query 4]) = [[.query 4,.normalRetriever 0,.selection 0,.width 1],[.query 4,.normalRetriever 0,.selection 0,.width 1,.stop],[.query 4,.normalRetriever 0,.selection 0,.width 1,.stop,.reranker 1],[.query 4,.normalRetriever 0,.selection 0,.width 1,.stop,.reranker 1,.topm 2],[.query 4,.normalRetriever 0,.selection 0,.width 1,.stop,.reranker 1,.topm 2,.context 0],[.query 4,.normalRetriever 0,.selection 0,.width 1,.stop,.reranker 1,.topm 2,.context 0,.answer 2]] := by decide
      unfold pathQuote
      rw [hs]
      norm_num [completed_price_rational_projection,rationalActionPrice]
    · change pathQuote .complete (pathHistoryCache favorableCompleteS18Before) (completedPrice unitRoleUnused) (safeCompletion [.query 5]) = _
      have hs : pathSuffix (pathHistoryCache favorableCompleteS18Before) (safeCompletion [.query 5]) = [[.query 5,.normalRetriever 0,.selection 0,.width 1],[.query 5,.normalRetriever 0,.selection 0,.width 1,.stop],[.query 5,.normalRetriever 0,.selection 0,.width 1,.stop,.reranker 1],[.query 5,.normalRetriever 0,.selection 0,.width 1,.stop,.reranker 1,.topm 2],[.query 5,.normalRetriever 0,.selection 0,.width 1,.stop,.reranker 1,.topm 2,.context 0],[.query 5,.normalRetriever 0,.selection 0,.width 1,.stop,.reranker 1,.topm 2,.context 0,.answer 2]] := by decide
      unfold pathQuote
      rw [hs]
      norm_num [completed_price_rational_projection,rationalActionPrice]
    · change pathQuote .complete (pathHistoryCache favorableCompleteS18Before) (completedPrice unitRoleUnused) (safeCompletion [.query 6]) = _
      have hs : pathSuffix (pathHistoryCache favorableCompleteS18Before) (safeCompletion [.query 6]) = [[.query 6,.normalRetriever 0,.selection 0,.width 1],[.query 6,.normalRetriever 0,.selection 0,.width 1,.stop],[.query 6,.normalRetriever 0,.selection 0,.width 1,.stop,.reranker 1],[.query 6,.normalRetriever 0,.selection 0,.width 1,.stop,.reranker 1,.topm 2],[.query 6,.normalRetriever 0,.selection 0,.width 1,.stop,.reranker 1,.topm 2,.context 0],[.query 6,.normalRetriever 0,.selection 0,.width 1,.stop,.reranker 1,.topm 2,.context 0,.answer 2]] := by decide
      unfold pathQuote
      rw [hs]
      norm_num [completed_price_rational_projection,rationalActionPrice]
    · change pathQuote .complete (pathHistoryCache favorableCompleteS18Before) (completedPrice unitRoleUnused) (safeCompletion [.query 7]) = _
      have hs : pathSuffix (pathHistoryCache favorableCompleteS18Before) (safeCompletion [.query 7]) = [[.query 7,.normalRetriever 0,.selection 0,.width 1],[.query 7,.normalRetriever 0,.selection 0,.width 1,.stop],[.query 7,.normalRetriever 0,.selection 0,.width 1,.stop,.reranker 1],[.query 7,.normalRetriever 0,.selection 0,.width 1,.stop,.reranker 1,.topm 2],[.query 7,.normalRetriever 0,.selection 0,.width 1,.stop,.reranker 1,.topm 2,.context 0],[.query 7,.normalRetriever 0,.selection 0,.width 1,.stop,.reranker 1,.topm 2,.context 0,.answer 2]] := by decide
      unfold pathQuote
      rw [hs]
      norm_num [completed_price_rational_projection,rationalActionPrice]

theorem favorableCompleteS18D1I0 : indexScore (7/5) (controlPenalty savedCref uniformQuoteError unitRoleUnused .complete) favorableCompleteS18Before [.query 1] (.hydeRetriever 1) = treeIndex ((1/1)/4) (7/5) 0 10 4 := by
  have hs : replayBackup favorableCompleteS18Before emptyStatistics ([.query 1]++[.hydeRetriever 1]) = ⟨4,(1/1)⟩ := by
    rw [replayBackup_empty_closed_form]
    simp +decide [backedEvents,favorableCompleteS18Before,favorableCompleteProposal,favorableCompleteEvent1,favorableCompleteEvent2,favorableCompleteEvent3,favorableCompleteEvent4,favorableCompleteEvent5,favorableCompleteEvent6,favorableCompleteEvent7,favorableCompleteEvent8,favorableCompleteEvent9,favorableCompleteEvent10,favorableCompleteEvent11,favorableCompleteEvent12,favorableCompleteEvent13,favorableCompleteEvent14,favorableCompleteEvent15,favorableCompleteEvent16,favorableCompleteEvent17,taskReward]
    <;> norm_num
  have hp : rawVisits favorableCompleteS18Before [.query 1] = 10 := by decide
  have hn : rawVisits favorableCompleteS18Before ([.query 1]++[.hydeRetriever 1]) = 4 := by decide
  have hz : (controlPenalty savedCref uniformQuoteError unitRoleUnused .complete) favorableCompleteS18Before [.query 1] (.hydeRetriever 1) = 0 := control_penalty_empty_suffix _ _ _ _ _ _ (by decide)
  unfold indexScore
  rw [hs,hp,hn,hz]
  simp only [BackupStat.mean]
  norm_num

theorem favorableCompleteS18D1I1 : indexScore (7/5) (controlPenalty savedCref uniformQuoteError unitRoleUnused .complete) favorableCompleteS18Before [.query 1] (.hydeRetriever 0) = treeIndex ((0/1)/3) (7/5) 0 10 3 := by
  have hs : replayBackup favorableCompleteS18Before emptyStatistics ([.query 1]++[.hydeRetriever 0]) = ⟨3,(0/1)⟩ := by
    rw [replayBackup_empty_closed_form]
    simp +decide [backedEvents,favorableCompleteS18Before,favorableCompleteProposal,favorableCompleteEvent1,favorableCompleteEvent2,favorableCompleteEvent3,favorableCompleteEvent4,favorableCompleteEvent5,favorableCompleteEvent6,favorableCompleteEvent7,favorableCompleteEvent8,favorableCompleteEvent9,favorableCompleteEvent10,favorableCompleteEvent11,favorableCompleteEvent12,favorableCompleteEvent13,favorableCompleteEvent14,favorableCompleteEvent15,favorableCompleteEvent16,favorableCompleteEvent17,taskReward]
    <;> norm_num
  have hp : rawVisits favorableCompleteS18Before [.query 1] = 10 := by decide
  have hn : rawVisits favorableCompleteS18Before ([.query 1]++[.hydeRetriever 0]) = 3 := by decide
  have hz : (controlPenalty savedCref uniformQuoteError unitRoleUnused .complete) favorableCompleteS18Before [.query 1] (.hydeRetriever 0) = 0 := control_penalty_empty_suffix _ _ _ _ _ _ (by decide)
  unfold indexScore
  rw [hs,hp,hn,hz]
  simp only [BackupStat.mean]
  norm_num

theorem favorableCompleteS18D1I2 : indexScore (7/5) (controlPenalty savedCref uniformQuoteError unitRoleUnused .complete) favorableCompleteS18Before [.query 1] (.hydeRetriever 2) = treeIndex ((0/1)/2) (7/5) 0 10 2 := by
  have hs : replayBackup favorableCompleteS18Before emptyStatistics ([.query 1]++[.hydeRetriever 2]) = ⟨2,(0/1)⟩ := by
    rw [replayBackup_empty_closed_form]
    simp +decide [backedEvents,favorableCompleteS18Before,favorableCompleteProposal,favorableCompleteEvent1,favorableCompleteEvent2,favorableCompleteEvent3,favorableCompleteEvent4,favorableCompleteEvent5,favorableCompleteEvent6,favorableCompleteEvent7,favorableCompleteEvent8,favorableCompleteEvent9,favorableCompleteEvent10,favorableCompleteEvent11,favorableCompleteEvent12,favorableCompleteEvent13,favorableCompleteEvent14,favorableCompleteEvent15,favorableCompleteEvent16,favorableCompleteEvent17,taskReward]
    <;> norm_num
  have hp : rawVisits favorableCompleteS18Before [.query 1] = 10 := by decide
  have hn : rawVisits favorableCompleteS18Before ([.query 1]++[.hydeRetriever 2]) = 2 := by decide
  have hz : (controlPenalty savedCref uniformQuoteError unitRoleUnused .complete) favorableCompleteS18Before [.query 1] (.hydeRetriever 2) = 0 := control_penalty_empty_suffix _ _ _ _ _ _ (by decide)
  unfold indexScore
  rw [hs,hp,hn,hz]
  simp only [BackupStat.mean]
  norm_num

theorem favorableCompleteS18D1Cmp0 : indexScore (7/5) (controlPenalty savedCref uniformQuoteError unitRoleUnused .complete) favorableCompleteS18Before [.query 1] (.hydeRetriever 1) < indexScore (7/5) (controlPenalty savedCref uniformQuoteError unitRoleUnused .complete) favorableCompleteS18Before [.query 1] (.hydeRetriever 2) := by
  rw [favorableCompleteS18D1I0,favorableCompleteS18D1I2]
  have h := index_strict_order_from_intervals ((0/1)/2) ((1/1)/4) 0 0 (38323761/25000000) (5419799/5000000)
    (treeBonus (7/5) 10 2) (treeBonus (7/5) 10 4)
    (trajectory_bonus_10_2).1 (trajectory_bonus_10_4).2 (by norm_num)
  simpa only [treeIndex,sub_zero] using h

theorem favorableCompleteS18D1Cmp1 : indexScore (7/5) (controlPenalty savedCref uniformQuoteError unitRoleUnused .complete) favorableCompleteS18Before [.query 1] (.hydeRetriever 0) < indexScore (7/5) (controlPenalty savedCref uniformQuoteError unitRoleUnused .complete) favorableCompleteS18Before [.query 1] (.hydeRetriever 2) := by
  rw [favorableCompleteS18D1I1,favorableCompleteS18D1I2]
  have h := index_strict_order_from_intervals ((0/1)/2) ((0/1)/3) 0 0 (38323761/25000000) (1251649/1000000)
    (treeBonus (7/5) 10 2) (treeBonus (7/5) 10 3)
    (trajectory_bonus_10_2).1 (trajectory_bonus_10_3).2 (by norm_num)
  simpa only [treeIndex,sub_zero] using h

theorem favorableCompleteS18Choice1 : nativeFirstChoice (indexScore (7/5) (controlPenalty savedCref uniformQuoteError unitRoleUnused .complete) favorableCompleteS18Before [.query 1]) favorableCompleteS18Before [.query 1] = .hydeRetriever 2 := by
  apply visited_choice_from_ordered_certificate _ _ [.query 1] [.hydeRetriever 1,.hydeRetriever 0] [] (.hydeRetriever 2) (by decide)
  · intro a ha
    have ho : orderedLegalAvailable [.query 1] = [.hydeRetriever 1,.hydeRetriever 0,.hydeRetriever 2] := by decide
    rw [ho] at ha
    simp only [List.mem_cons,List.not_mem_nil,or_false] at ha
    rcases ha with rfl | rfl | rfl <;> decide
  · intro a ha
    simp only [List.mem_cons,List.not_mem_nil,or_false] at ha
    rcases ha with rfl | rfl
    · exact favorableCompleteS18D1Cmp0
    · exact favorableCompleteS18D1Cmp1
  · simp

theorem favorableCompleteS18ActualEvent : nativeEvent budgetTape (7/5) (controlPenalty savedCref uniformQuoteError unitRoleUnused .complete)
    (taskReward false (2/5) (1/2)) favorableCompleteS18Before = favorableCompleteEvent18 := by
  have hs0 := native_select_existing_step budgetTape (7/5) (controlPenalty savedCref uniformQuoteError unitRoleUnused .complete) favorableCompleteS18Before 8 [] (.query 1)
    (by decide) (by decide) favorableCompleteS18Choice0
  have hs1 := native_select_existing_step budgetTape (7/5) (controlPenalty savedCref uniformQuoteError unitRoleUnused .complete) favorableCompleteS18Before 7 [.query 1] (.hydeRetriever 2)
    (by decide) (by decide) favorableCompleteS18Choice1
  have hnew := native_select_new_step budgetTape (7/5) (controlPenalty savedCref uniformQuoteError unitRoleUnused .complete) favorableCompleteS18Before 6 [.query 1,.hydeRetriever 2]
    [.selection 1,.selection 2,.selection 3] (.selection 1) (by decide) (by decide) (by decide) (by decide)
  have hs : nativeSelect budgetTape (7/5) (controlPenalty savedCref uniformQuoteError unitRoleUnused .complete) favorableCompleteS18Before 9 [] = [.query 1,.hydeRetriever 2,.selection 1] := by
    rw [hs0]
    change nativeSelect budgetTape (7/5) (controlPenalty savedCref uniformQuoteError unitRoleUnused .complete) favorableCompleteS18Before 8 [.query 1] = _
    rw [hs1]
    change nativeSelect budgetTape (7/5) (controlPenalty savedCref uniformQuoteError unitRoleUnused .complete) favorableCompleteS18Before 7 [.query 1,.hydeRetriever 2] = _
    rw [hnew] <;> rfl
  have hr : repairedRollout budgetTape favorableCompleteS18Before 9 [.query 1,.hydeRetriever 2,.selection 1] = [.query 1,.hydeRetriever 2,.selection 1,.width 0,.stop,.reranker 0,.topm 0,.context 0,.answer 0] := by decide
  simp only [nativeEvent,hs,hr]
  rfl

def favorableCompleteS19Before := favorableCompleteProposal.take 18

theorem favorableCompleteS19Choice0 : nativeFirstChoice (indexScore (7/5) (controlPenalty savedCref uniformQuoteError unitRoleUnused .complete) favorableCompleteS19Before []) favorableCompleteS19Before [] = .query 1 := by
  apply complete_root_from_physical_gap favorableCompleteS19Before (favorableComplete_prefix_rewards 18) (by decide)
  · intro q; fin_cases q <;> decide
  · decide
  · intro q hq
    fin_cases q
    · change pathQuote .complete (pathHistoryCache favorableCompleteS19Before) (completedPrice unitRoleUnused) (safeCompletion [.query 0]) = _
      have hs : pathSuffix (pathHistoryCache favorableCompleteS19Before) (safeCompletion [.query 0]) = [[.query 0,.normalRetriever 0,.selection 0,.width 1],[.query 0,.normalRetriever 0,.selection 0,.width 1,.stop],[.query 0,.normalRetriever 0,.selection 0,.width 1,.stop,.reranker 1],[.query 0,.normalRetriever 0,.selection 0,.width 1,.stop,.reranker 1,.topm 2],[.query 0,.normalRetriever 0,.selection 0,.width 1,.stop,.reranker 1,.topm 2,.context 0],[.query 0,.normalRetriever 0,.selection 0,.width 1,.stop,.reranker 1,.topm 2,.context 0,.answer 2]] := by decide
      unfold pathQuote
      rw [hs]
      norm_num [completed_price_rational_projection,rationalActionPrice]
    · exact (hq rfl).elim
    · change pathQuote .complete (pathHistoryCache favorableCompleteS19Before) (completedPrice unitRoleUnused) (safeCompletion [.query 2]) = _
      have hs : pathSuffix (pathHistoryCache favorableCompleteS19Before) (safeCompletion [.query 2]) = [[.query 2,.normalRetriever 0,.selection 0,.width 1],[.query 2,.normalRetriever 0,.selection 0,.width 1,.stop],[.query 2,.normalRetriever 0,.selection 0,.width 1,.stop,.reranker 1],[.query 2,.normalRetriever 0,.selection 0,.width 1,.stop,.reranker 1,.topm 2],[.query 2,.normalRetriever 0,.selection 0,.width 1,.stop,.reranker 1,.topm 2,.context 0],[.query 2,.normalRetriever 0,.selection 0,.width 1,.stop,.reranker 1,.topm 2,.context 0,.answer 2]] := by decide
      unfold pathQuote
      rw [hs]
      norm_num [completed_price_rational_projection,rationalActionPrice]
    · change pathQuote .complete (pathHistoryCache favorableCompleteS19Before) (completedPrice unitRoleUnused) (safeCompletion [.query 3]) = _
      have hs : pathSuffix (pathHistoryCache favorableCompleteS19Before) (safeCompletion [.query 3]) = [[.query 3,.normalRetriever 0,.selection 0,.width 1],[.query 3,.normalRetriever 0,.selection 0,.width 1,.stop],[.query 3,.normalRetriever 0,.selection 0,.width 1,.stop,.reranker 1],[.query 3,.normalRetriever 0,.selection 0,.width 1,.stop,.reranker 1,.topm 2],[.query 3,.normalRetriever 0,.selection 0,.width 1,.stop,.reranker 1,.topm 2,.context 0],[.query 3,.normalRetriever 0,.selection 0,.width 1,.stop,.reranker 1,.topm 2,.context 0,.answer 2]] := by decide
      unfold pathQuote
      rw [hs]
      norm_num [completed_price_rational_projection,rationalActionPrice]
    · change pathQuote .complete (pathHistoryCache favorableCompleteS19Before) (completedPrice unitRoleUnused) (safeCompletion [.query 4]) = _
      have hs : pathSuffix (pathHistoryCache favorableCompleteS19Before) (safeCompletion [.query 4]) = [[.query 4,.normalRetriever 0,.selection 0,.width 1],[.query 4,.normalRetriever 0,.selection 0,.width 1,.stop],[.query 4,.normalRetriever 0,.selection 0,.width 1,.stop,.reranker 1],[.query 4,.normalRetriever 0,.selection 0,.width 1,.stop,.reranker 1,.topm 2],[.query 4,.normalRetriever 0,.selection 0,.width 1,.stop,.reranker 1,.topm 2,.context 0],[.query 4,.normalRetriever 0,.selection 0,.width 1,.stop,.reranker 1,.topm 2,.context 0,.answer 2]] := by decide
      unfold pathQuote
      rw [hs]
      norm_num [completed_price_rational_projection,rationalActionPrice]
    · change pathQuote .complete (pathHistoryCache favorableCompleteS19Before) (completedPrice unitRoleUnused) (safeCompletion [.query 5]) = _
      have hs : pathSuffix (pathHistoryCache favorableCompleteS19Before) (safeCompletion [.query 5]) = [[.query 5,.normalRetriever 0,.selection 0,.width 1],[.query 5,.normalRetriever 0,.selection 0,.width 1,.stop],[.query 5,.normalRetriever 0,.selection 0,.width 1,.stop,.reranker 1],[.query 5,.normalRetriever 0,.selection 0,.width 1,.stop,.reranker 1,.topm 2],[.query 5,.normalRetriever 0,.selection 0,.width 1,.stop,.reranker 1,.topm 2,.context 0],[.query 5,.normalRetriever 0,.selection 0,.width 1,.stop,.reranker 1,.topm 2,.context 0,.answer 2]] := by decide
      unfold pathQuote
      rw [hs]
      norm_num [completed_price_rational_projection,rationalActionPrice]
    · change pathQuote .complete (pathHistoryCache favorableCompleteS19Before) (completedPrice unitRoleUnused) (safeCompletion [.query 6]) = _
      have hs : pathSuffix (pathHistoryCache favorableCompleteS19Before) (safeCompletion [.query 6]) = [[.query 6,.normalRetriever 0,.selection 0,.width 1],[.query 6,.normalRetriever 0,.selection 0,.width 1,.stop],[.query 6,.normalRetriever 0,.selection 0,.width 1,.stop,.reranker 1],[.query 6,.normalRetriever 0,.selection 0,.width 1,.stop,.reranker 1,.topm 2],[.query 6,.normalRetriever 0,.selection 0,.width 1,.stop,.reranker 1,.topm 2,.context 0],[.query 6,.normalRetriever 0,.selection 0,.width 1,.stop,.reranker 1,.topm 2,.context 0,.answer 2]] := by decide
      unfold pathQuote
      rw [hs]
      norm_num [completed_price_rational_projection,rationalActionPrice]
    · change pathQuote .complete (pathHistoryCache favorableCompleteS19Before) (completedPrice unitRoleUnused) (safeCompletion [.query 7]) = _
      have hs : pathSuffix (pathHistoryCache favorableCompleteS19Before) (safeCompletion [.query 7]) = [[.query 7,.normalRetriever 0,.selection 0,.width 1],[.query 7,.normalRetriever 0,.selection 0,.width 1,.stop],[.query 7,.normalRetriever 0,.selection 0,.width 1,.stop,.reranker 1],[.query 7,.normalRetriever 0,.selection 0,.width 1,.stop,.reranker 1,.topm 2],[.query 7,.normalRetriever 0,.selection 0,.width 1,.stop,.reranker 1,.topm 2,.context 0],[.query 7,.normalRetriever 0,.selection 0,.width 1,.stop,.reranker 1,.topm 2,.context 0,.answer 2]] := by decide
      unfold pathQuote
      rw [hs]
      norm_num [completed_price_rational_projection,rationalActionPrice]

theorem favorableCompleteS19D1I0 : indexScore (7/5) (controlPenalty savedCref uniformQuoteError unitRoleUnused .complete) favorableCompleteS19Before [.query 1] (.hydeRetriever 1) = treeIndex ((1/1)/4) (7/5) 0 11 4 := by
  have hs : replayBackup favorableCompleteS19Before emptyStatistics ([.query 1]++[.hydeRetriever 1]) = ⟨4,(1/1)⟩ := by
    rw [replayBackup_empty_closed_form]
    simp +decide [backedEvents,favorableCompleteS19Before,favorableCompleteProposal,favorableCompleteEvent1,favorableCompleteEvent2,favorableCompleteEvent3,favorableCompleteEvent4,favorableCompleteEvent5,favorableCompleteEvent6,favorableCompleteEvent7,favorableCompleteEvent8,favorableCompleteEvent9,favorableCompleteEvent10,favorableCompleteEvent11,favorableCompleteEvent12,favorableCompleteEvent13,favorableCompleteEvent14,favorableCompleteEvent15,favorableCompleteEvent16,favorableCompleteEvent17,favorableCompleteEvent18,taskReward]
    <;> norm_num
  have hp : rawVisits favorableCompleteS19Before [.query 1] = 11 := by decide
  have hn : rawVisits favorableCompleteS19Before ([.query 1]++[.hydeRetriever 1]) = 4 := by decide
  have hz : (controlPenalty savedCref uniformQuoteError unitRoleUnused .complete) favorableCompleteS19Before [.query 1] (.hydeRetriever 1) = 0 := control_penalty_empty_suffix _ _ _ _ _ _ (by decide)
  unfold indexScore
  rw [hs,hp,hn,hz]
  simp only [BackupStat.mean]
  norm_num

theorem favorableCompleteS19D1I1 : indexScore (7/5) (controlPenalty savedCref uniformQuoteError unitRoleUnused .complete) favorableCompleteS19Before [.query 1] (.hydeRetriever 0) = treeIndex ((0/1)/3) (7/5) 0 11 3 := by
  have hs : replayBackup favorableCompleteS19Before emptyStatistics ([.query 1]++[.hydeRetriever 0]) = ⟨3,(0/1)⟩ := by
    rw [replayBackup_empty_closed_form]
    simp +decide [backedEvents,favorableCompleteS19Before,favorableCompleteProposal,favorableCompleteEvent1,favorableCompleteEvent2,favorableCompleteEvent3,favorableCompleteEvent4,favorableCompleteEvent5,favorableCompleteEvent6,favorableCompleteEvent7,favorableCompleteEvent8,favorableCompleteEvent9,favorableCompleteEvent10,favorableCompleteEvent11,favorableCompleteEvent12,favorableCompleteEvent13,favorableCompleteEvent14,favorableCompleteEvent15,favorableCompleteEvent16,favorableCompleteEvent17,favorableCompleteEvent18,taskReward]
    <;> norm_num
  have hp : rawVisits favorableCompleteS19Before [.query 1] = 11 := by decide
  have hn : rawVisits favorableCompleteS19Before ([.query 1]++[.hydeRetriever 0]) = 3 := by decide
  have hz : (controlPenalty savedCref uniformQuoteError unitRoleUnused .complete) favorableCompleteS19Before [.query 1] (.hydeRetriever 0) = 0 := control_penalty_empty_suffix _ _ _ _ _ _ (by decide)
  unfold indexScore
  rw [hs,hp,hn,hz]
  simp only [BackupStat.mean]
  norm_num

theorem favorableCompleteS19D1I2 : indexScore (7/5) (controlPenalty savedCref uniformQuoteError unitRoleUnused .complete) favorableCompleteS19Before [.query 1] (.hydeRetriever 2) = treeIndex ((0/1)/3) (7/5) 0 11 3 := by
  have hs : replayBackup favorableCompleteS19Before emptyStatistics ([.query 1]++[.hydeRetriever 2]) = ⟨3,(0/1)⟩ := by
    rw [replayBackup_empty_closed_form]
    simp +decide [backedEvents,favorableCompleteS19Before,favorableCompleteProposal,favorableCompleteEvent1,favorableCompleteEvent2,favorableCompleteEvent3,favorableCompleteEvent4,favorableCompleteEvent5,favorableCompleteEvent6,favorableCompleteEvent7,favorableCompleteEvent8,favorableCompleteEvent9,favorableCompleteEvent10,favorableCompleteEvent11,favorableCompleteEvent12,favorableCompleteEvent13,favorableCompleteEvent14,favorableCompleteEvent15,favorableCompleteEvent16,favorableCompleteEvent17,favorableCompleteEvent18,taskReward]
    <;> norm_num
  have hp : rawVisits favorableCompleteS19Before [.query 1] = 11 := by decide
  have hn : rawVisits favorableCompleteS19Before ([.query 1]++[.hydeRetriever 2]) = 3 := by decide
  have hz : (controlPenalty savedCref uniformQuoteError unitRoleUnused .complete) favorableCompleteS19Before [.query 1] (.hydeRetriever 2) = 0 := control_penalty_empty_suffix _ _ _ _ _ _ (by decide)
  unfold indexScore
  rw [hs,hp,hn,hz]
  simp only [BackupStat.mean]
  norm_num

theorem favorableCompleteS19D1Cmp1 : indexScore (7/5) (controlPenalty savedCref uniformQuoteError unitRoleUnused .complete) favorableCompleteS19Before [.query 1] (.hydeRetriever 0) ≤ indexScore (7/5) (controlPenalty savedCref uniformQuoteError unitRoleUnused .complete) favorableCompleteS19Before [.query 1] (.hydeRetriever 1) := by
  rw [favorableCompleteS19D1I1,favorableCompleteS19D1I0]
  have h := index_weak_order_from_intervals ((1/1)/4) ((0/1)/3) 0 0 (55172551/50000000) (7963473/6250000)
    (treeBonus (7/5) 11 4) (treeBonus (7/5) 11 3)
    (trajectory_bonus_11_4).1 (trajectory_bonus_11_3).2 (by norm_num)
  simpa only [treeIndex,sub_zero] using h

theorem favorableCompleteS19D1Cmp2 : indexScore (7/5) (controlPenalty savedCref uniformQuoteError unitRoleUnused .complete) favorableCompleteS19Before [.query 1] (.hydeRetriever 2) ≤ indexScore (7/5) (controlPenalty savedCref uniformQuoteError unitRoleUnused .complete) favorableCompleteS19Before [.query 1] (.hydeRetriever 1) := by
  rw [favorableCompleteS19D1I2,favorableCompleteS19D1I0]
  have h := index_weak_order_from_intervals ((1/1)/4) ((0/1)/3) 0 0 (55172551/50000000) (7963473/6250000)
    (treeBonus (7/5) 11 4) (treeBonus (7/5) 11 3)
    (trajectory_bonus_11_4).1 (trajectory_bonus_11_3).2 (by norm_num)
  simpa only [treeIndex,sub_zero] using h

theorem favorableCompleteS19Choice1 : nativeFirstChoice (indexScore (7/5) (controlPenalty savedCref uniformQuoteError unitRoleUnused .complete) favorableCompleteS19Before [.query 1]) favorableCompleteS19Before [.query 1] = .hydeRetriever 1 := by
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
    · exact favorableCompleteS19D1Cmp1
    · exact favorableCompleteS19D1Cmp2

theorem favorableCompleteS19ActualEvent : nativeEvent budgetTape (7/5) (controlPenalty savedCref uniformQuoteError unitRoleUnused .complete)
    (taskReward false (2/5) (1/2)) favorableCompleteS19Before = favorableCompleteEvent19 := by
  have hs0 := native_select_existing_step budgetTape (7/5) (controlPenalty savedCref uniformQuoteError unitRoleUnused .complete) favorableCompleteS19Before 8 [] (.query 1)
    (by decide) (by decide) favorableCompleteS19Choice0
  have hs1 := native_select_existing_step budgetTape (7/5) (controlPenalty savedCref uniformQuoteError unitRoleUnused .complete) favorableCompleteS19Before 7 [.query 1] (.hydeRetriever 1)
    (by decide) (by decide) favorableCompleteS19Choice1
  have hnew := native_select_new_step budgetTape (7/5) (controlPenalty savedCref uniformQuoteError unitRoleUnused .complete) favorableCompleteS19Before 6 [.query 1,.hydeRetriever 1]
    [.selection 3] (.selection 3) (by decide) (by decide) (by decide) (by decide)
  have hs : nativeSelect budgetTape (7/5) (controlPenalty savedCref uniformQuoteError unitRoleUnused .complete) favorableCompleteS19Before 9 [] = [.query 1,.hydeRetriever 1,.selection 3] := by
    rw [hs0]
    change nativeSelect budgetTape (7/5) (controlPenalty savedCref uniformQuoteError unitRoleUnused .complete) favorableCompleteS19Before 8 [.query 1] = _
    rw [hs1]
    change nativeSelect budgetTape (7/5) (controlPenalty savedCref uniformQuoteError unitRoleUnused .complete) favorableCompleteS19Before 7 [.query 1,.hydeRetriever 1] = _
    rw [hnew] <;> rfl
  have hr : repairedRollout budgetTape favorableCompleteS19Before 9 [.query 1,.hydeRetriever 1,.selection 3] = [.query 1,.hydeRetriever 1,.selection 3,.width 0,.stop,.reranker 0,.topm 0,.context 0,.answer 0] := by decide
  simp only [nativeEvent,hs,hr]
  rfl

end AgentUCT32MConcrete
