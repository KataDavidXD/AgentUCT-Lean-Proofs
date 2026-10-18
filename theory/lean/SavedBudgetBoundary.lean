import ObservedPhysicalWitness




set_option autoImplicit false
set_option maxRecDepth 16384
set_option maxHeartbeats 4000000
noncomputable section
namespace AgentUCTObservabilityBoundary
open AgentUCTObservability AgentUCTPhysicalDiagnostic AgentUCTNativeBudget
  AgentUCTPanelAllocation AgentUCTNativeRepair AgentUCTNativeRefinement AgentUCTPaper

theorem companion_whole_bills_below_saved_target (unused : Act → Fin 8 → ℕ)
    (reward : List Act → ℝ) :
    panelActualBill panel150 (fun r => completedPrice unused (resourceAction r)) (aEleven reward) < (32000000:ℝ) ∧
    panelActualBill panel150 (fun r => completedPrice unused (resourceAction r)) (bTen reward) < (32000000:ℝ) := by
  have hb := completed_raw_and_retained_bills unused reward
  rw [hb.1,hb.2.1]
  simp +decide [baseBill,eightBill,integerTariffs,tailBill,crossBill,
    finUniv8_explicit,identityQuery]
  norm_num [generatorRate,e5Rate,bgeRate,embeddingRate]

theorem companion_whole_bills_do_not_reach_saved_target (unused : Act → Fin 8 → ℕ)
    (reward : List Act → ℝ) :
    ¬ targetReached (panelActualBill panel150 (fun r => completedPrice unused (resourceAction r)) (aEleven reward)) (32000000:ℝ) ∧
    ¬ targetReached (panelActualBill panel150 (fun r => completedPrice unused (resourceAction r)) (bTen reward)) (32000000:ℝ) := by
  have hb := companion_whole_bills_below_saved_target unused reward
  exact ⟨not_le.mpr hb.1,not_le.mpr hb.2⟩

#print axioms companion_whole_bills_below_saved_target
#print axioms companion_whole_bills_do_not_reach_saved_target
end AgentUCTObservabilityBoundary
