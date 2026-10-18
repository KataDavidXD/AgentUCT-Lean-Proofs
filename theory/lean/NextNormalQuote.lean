import NextNormalCache
set_option autoImplicit false
set_option maxRecDepth 16384
set_option maxHeartbeats 16000000
noncomputable section
namespace AgentUCTNextExact
open AgentUCT32MConcrete AgentUCT32MContinuation AgentUCTSavedBudget AgentUCTObservability
  AgentUCTPhysicalDiagnostic AgentUCTNativeBudget AgentUCTPanelAllocation
  AgentUCTNativeRepair AgentUCTNativeRefinement AgentUCTPaper

def concretePrice (before : List (TreeEvaluation Act)) : Fin 150 × List Act → ℝ :=
  liveReceiptPrice (completedPriors uniformQuoteError unitRoleUnused) (completedCaps uniformQuoteError)
    (observedMeans panel150 (completedPrice unitRoleUnused) (completedCaps uniformQuoteError) 0 before)

theorem normal_suffix_after_three (before : List (TreeEvaluation Act)) (q : Fin 8) (hq : q ≠ hyde)
    (hs : normalWarmStages before q = {1,2,3}) :
    pathSuffix (pathHistoryCache before) (normalMCPath q) =
      [(normalMCPath q).take 4,(normalMCPath q).take 5,(normalMCPath q).take 6,
       (normalMCPath q).take 7,(normalMCPath q).take 8,(normalMCPath q).take 9] := by
  rw [pathSuffix,normal_warm_depth_three before q hs,normal_mc_path q hq]
  fin_cases q <;> decide

theorem normal_first_resource_action (q : Fin 8) (hq : q ≠ hyde) (qid : Fin 150) :
    resourceAction (qid,(normalMCPath q).take 4) = .width 1 := by
  rw [normal_mc_path q hq]
  simp [resourceAction,fullLeaf]

theorem normal_first_quote_positive (before : List (TreeEvaluation Act)) (q : Fin 8)
    (hq : q ≠ hyde) (qid : Fin 150) :
    0 < concretePrice before (qid,(normalMCPath q).take 4) := by
  have hs := completed_live_price_support_stable uniformQuoteError
    (by norm_num [uniformQuoteError]) (by norm_num [uniformQuoteError]) before (qid,(normalMCPath q).take 4)
  have ht : 0 < completedPrice unitRoleUnused (resourceAction (qid,(normalMCPath q).take 4)) := by
    rw [normal_first_resource_action q hq qid,completed_price_rational_projection]
    norm_num [rationalActionPrice]
  exact lt_of_not_ge (fun h => not_le.mpr ht (hs.mp h))

theorem normal_qid_next_exact (before : List (TreeEvaluation Act)) (q : Fin 8) (hq : q ≠ hyde)
    (hs : normalWarmStages before q = {1,2,3}) (qid : Fin 150) :
    sourceQidQuote .next (ownPanelCache panel150 before) (fun _ _ => false) (concretePrice before)
      qid (normalMCPath q) = concretePrice before (qid,(normalMCPath q).take 4) := by
  simp only [sourceQidQuote]
  rw [own_panel_cache_product]
  change nextUnpaidBill ∅ (concretePrice before)
    (sourceSuffix ((Finset.univ : Finset (Fin 150)) ×ˢ pathHistoryCache before) (fun _ _ => false)
      qid (normalMCPath q)) = _
  rw [source_suffix_full_panel_projection,normal_suffix_after_three before q hq hs]
  simp only [List.map_cons,nextUnpaidBill,Finset.notMem_empty,false_or]
  rw [if_neg (not_le.mpr (normal_first_quote_positive before q hq qid))]

theorem normal_first_quotes_equal (before : List (TreeEvaluation Act)) (q : Fin 8) (hq : q ≠ hyde)
    (hs : normalWarmStages before q = {1,2,3}) (hzero : normalWarmStages before 0 = {1,2,3})
    (qid : Fin 150) :
    concretePrice before (qid,(normalMCPath q).take 4) =
      concretePrice before (0,(normalMCPath 0).take 4) := by
  apply equal_action_unmaterialized_prefix_prices_exact
  · intro query; exact normal_first_unpaid_absent before q hq hs query
  · intro query; exact normal_first_unpaid_absent before 0 (by decide) hzero query
  · rw [normal_first_resource_action q hq qid,normal_first_resource_action 0 (by decide) 0]

theorem normal_panel_mc16_exact (before : List (TreeEvaluation Act)) (q : Fin 8) (hq : q ≠ hyde)
    (hs : normalWarmStages before q = {1,2,3}) (hzero : normalWarmStages before 0 = {1,2,3}) :
    sourcePanelMC16 panel150 .next (ownPanelCache panel150 before) (fun _ _ => false)
      (concretePrice before) (budgetTape.completion before [] (.query q)) =
      150*concretePrice before (0,(normalMCPath 0).take 4) := by
  simp only [sourcePanelMC16,sourcePanelSample,budgetTape,List.nil_append]
  change (∑ i : Fin 16,∑ qid ∈ panel150,sourceQidQuote .next (ownPanelCache panel150 before)
      (fun _ _ => false) (concretePrice before) qid (normalMCPath q))/16 = _
  simp_rw [normal_qid_next_exact before q hq hs,normal_first_quotes_equal before q hq hs hzero]
  norm_num [panel150]

theorem normal_penalty_exact (Cref : ℝ) (before : List (TreeEvaluation Act)) (q : Fin 8) (hq : q ≠ hyde)
    (hs : normalWarmStages before q = {1,2,3}) (hzero : normalWarmStages before 0 = {1,2,3}) :
    controlPenalty Cref uniformQuoteError unitRoleUnused .next before [] (.query q) =
      (300/Cref)*concretePrice before (0,(normalMCPath 0).take 4) := by
  simp only [controlPenalty,observedPenalty,livePanelPenalty,livePanelForecast,
    true_or,if_true,add_zero]
  change (2/Cref)*sourcePanelMC16 panel150 .next (ownPanelCache panel150 before) (fun _ _ => false)
    (concretePrice before) (budgetTape.completion before [] (.query q)) = _
  rw [normal_panel_mc16_exact before q hq hs hzero]
  ring

theorem favorable_next_normal_root_quotes_exact (k : ℕ) (hk : 8 ≤ k) (q : Fin 8) (hq : q ≠ hyde) :
    controlPenalty savedCref uniformQuoteError unitRoleUnused .next (favorableNextProposal.take k) [] (.query q) =
      controlPenalty savedCref uniformQuoteError unitRoleUnused .next (favorableNextProposal.take k) [] (.query 0) := by
  rw [normal_penalty_exact _ _ q hq (favorable_normal_stages k hk q hq)
      (favorable_normal_stages k hk 0 (by decide)),
    normal_penalty_exact _ _ 0 (by decide) (favorable_normal_stages k hk 0 (by decide))
      (favorable_normal_stages k hk 0 (by decide))]

theorem adverse_next_normal_root_quotes_exact (k : ℕ) (hk : 8 ≤ k) (q : Fin 8) (hq : q ≠ hyde) :
    controlPenalty savedCref uniformQuoteError unitRoleUnused .next (adverseNextProposal.take k) [] (.query q) =
      controlPenalty savedCref uniformQuoteError unitRoleUnused .next (adverseNextProposal.take k) [] (.query 0) := by
  rw [normal_penalty_exact _ _ q hq (adverse_normal_stages k hk q hq)
      (adverse_normal_stages k hk 0 (by decide)),
    normal_penalty_exact _ _ 0 (by decide) (adverse_normal_stages k hk 0 (by decide))
      (adverse_normal_stages k hk 0 (by decide))]

end AgentUCTNextExact
