import CompletedQuoteEnvelope
set_option autoImplicit false
set_option maxRecDepth 16384
set_option maxHeartbeats 6000000
noncomputable section
namespace AgentUCT32MConcrete
open AgentUCT32MContinuation AgentUCTSavedBudget AgentUCTObservability
  AgentUCTPhysicalDiagnostic AgentUCTNativeBudget AgentUCTPanelAllocation
  AgentUCTNativeRepair AgentUCTNativeRefinement AgentUCTPaper
theorem completed_panel_mc16_error (mode : ForecastMode) (epsilon : ℝ)
    (he : 0 < epsilon) (hesmall : epsilon < 1/10)
    (before : List (TreeEvaluation Act)) (p : List Act) (a : Act)
    (hl : Legal p) (ha : a ∈ available p) :
    |sourcePanelMC16 panel150 mode (ownPanelCache panel150 before) (fun _ _ => false)
       (liveReceiptPrice (completedPriors epsilon unitRoleUnused) (completedCaps epsilon) (observedMeans panel150 (completedPrice unitRoleUnused) (completedCaps epsilon) 0 before)) (budgetTape.completion before p a)-
     sourcePanelMC16 panel150 mode (ownPanelCache panel150 before) (fun _ _ => false)
       (fun r => completedPrice unitRoleUnused (resourceAction r)) (budgetTape.completion before p a)| ≤
      (panel150.card : ℝ)*(10*epsilon) := by
  have hh : ∀ i : Fin 16, ∀ q ∈ panel150,
      |sourceQidQuote mode (ownPanelCache panel150 before) (fun _ _ => false)
         (liveReceiptPrice (completedPriors epsilon unitRoleUnused) (completedCaps epsilon) (observedMeans panel150 (completedPrice unitRoleUnused) (completedCaps epsilon) 0 before)) q (budgetTape.completion before p a i)-
       sourceQidQuote mode (ownPanelCache panel150 before) (fun _ _ => false)
         (fun r => completedPrice unitRoleUnused (resourceAction r)) q (budgetTape.completion before p a i)| ≤ 10*epsilon := by
    intro i q hq
    exact source_terminal_quote_error mode _ _ _ _ epsilon he.le
      (completed_live_receipt_error_all_histories epsilon he (by linarith) before)
      (completed_live_price_support_stable epsilon he hesmall before) q _
      (budget_tape_supported.2 before p a i hl ha).1.2
  have hs : ∀ i : Fin 16,
      |sourcePanelSample panel150 mode (ownPanelCache panel150 before) (fun _ _ => false)
         (liveReceiptPrice (completedPriors epsilon unitRoleUnused) (completedCaps epsilon) (observedMeans panel150 (completedPrice unitRoleUnused) (completedCaps epsilon) 0 before)) (budgetTape.completion before p a i)-
       sourcePanelSample panel150 mode (ownPanelCache panel150 before) (fun _ _ => false)
         (fun r => completedPrice unitRoleUnused (resourceAction r)) (budgetTape.completion before p a i)| ≤ (panel150.card : ℝ)*(10*epsilon) := by
    intro i
    simp only [sourcePanelSample,← Finset.sum_sub_distrib]
    exact (Finset.abs_sum_le_sum_abs _ _).trans (by simpa using Finset.sum_le_sum (fun q hq => hh i q hq))
  unfold sourcePanelMC16
  rw [← sub_div,abs_div,show |(16:ℝ)| = 16 by norm_num]
  apply (div_le_iff₀ (by norm_num : (0:ℝ) < 16)).mpr
  rw [← Finset.sum_sub_distrib]
  have hsum := Finset.sum_le_sum (s := (Finset.univ : Finset (Fin 16))) (fun i _ => hs i)
  exact (Finset.abs_sum_le_sum_abs _ _).trans (by simpa [mul_comm] using hsum)


theorem completed_control_penalty_error (mode : ForecastMode) (Cref epsilon : ℝ)
    (hC : 0 < Cref) (he : 0 < epsilon) (hesmall : epsilon < 1/10)
    (before : List (TreeEvaluation Act)) (p : List Act) (a : Act)
    (hl : Legal p) (ha : a ∈ available p) :
    |controlPenalty Cref epsilon unitRoleUnused mode before p a -
      (300/Cref)*pathQuote mode (pathHistoryCache before) (completedPrice unitRoleUnused)
        (safeCompletion (p++[a]))| ≤ (3000/Cref)*epsilon := by
  have hh := completed_panel_mc16_error mode epsilon he hesmall before p a hl ha
  have hs : 0 ≤ (2:ℝ)/Cref := by positivity
  have ho : (if mode = .next ∨ mode = .unpriced then 0 else (0:ℝ)) = 0 := by split_ifs <;> rfl
  have hp := physical_reference_penalty_full_panel_projection mode Cref before p a
  rw [← hp]
  simp only [controlPenalty,observedPenalty,livePanelPenalty,livePanelForecast,ho,add_zero,
    ← mul_sub,abs_mul,abs_of_nonneg hs]
  exact (mul_le_mul_of_nonneg_left hh hs).trans_eq (by norm_num [panel150]; ring)

end AgentUCT32MConcrete
