import ActualIndexCertificate
set_option autoImplicit false
set_option maxRecDepth 16384
set_option maxHeartbeats 12000000
noncomputable section
namespace AgentUCT32MConcrete
open AgentUCT32MContinuation AgentUCTSavedBudget AgentUCTObservability
  AgentUCTPhysicalDiagnostic AgentUCTNativeBudget AgentUCTPanelAllocation
  AgentUCTNativeRepair AgentUCTNativeRefinement AgentUCTPaper AgentUCTRealIndex

theorem native_select_existing_step (tape : SharedTape) (c : ℝ)
    (penalty : List (TreeEvaluation Act) → List Act → Act → ℝ)
    (before : List (TreeEvaluation Act)) (fuel : ℕ) (p : List Act) (a : Act)
    (hne : orderedLegalAvailable p ≠ [])
    (hex : (orderedLegalAvailable p).filter (fun a => p++[a] ∉ expandedNodes before) = [])
    (hchoice : nativeFirstChoice (indexScore c penalty before p) before p = a) :
    nativeSelect tape c penalty before (fuel+1) p =
      nativeSelect tape c penalty before fuel (p++[a]) := by
  simp only [nativeSelect,if_neg hne,hex,if_true,hchoice]

theorem native_select_new_step (tape : SharedTape) (c : ℝ)
    (penalty : List (TreeEvaluation Act) → List Act → Act → ℝ)
    (before : List (TreeEvaluation Act)) (fuel : ℕ) (p : List Act)
    (candidates : List Act) (a : Act)
    (hne : orderedLegalAvailable p ≠ []) (hcn : candidates ≠ [])
    (hex : (orderedLegalAvailable p).filter (fun a => p++[a] ∉ expandedNodes before) = candidates)
    (htape : tape.action before .expansion p candidates = a) :
    nativeSelect tape c penalty before (fuel+1) p = p++[a] := by
  simp only [nativeSelect,if_neg hne,hex,if_neg hcn,htape]

theorem control_penalty_empty_suffix (mode : ForecastMode) (Cref epsilon : ℝ)
    (before : List (TreeEvaluation Act)) (p : List Act) (a : Act)
    (hs : pathSuffix (pathHistoryCache before) (safeCompletion (p++[a])) = []) :
    controlPenalty Cref epsilon unitRoleUnused mode before p a = 0 := by
  have hz : ∀ q : Fin 150,sourceSuffix (ownPanelCache panel150 before) (fun _ _ => false)
      q (safeCompletion (p++[a])) = [] := by
    intro q
    rw [own_panel_cache_product,panel150,source_suffix_full_panel_projection,hs]
    rfl
  unfold controlPenalty observedPenalty livePanelPenalty livePanelForecast sourcePanelMC16 sourcePanelSample
  simp only [budgetTape]
  cases mode <;> simp [sourceQidQuote,hz,nextUnpaidBill]

end AgentUCT32MConcrete
