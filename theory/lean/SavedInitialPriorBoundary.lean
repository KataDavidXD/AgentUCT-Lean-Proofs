import SavedControlMargins




set_option autoImplicit false
set_option maxRecDepth 16384
set_option maxHeartbeats 4000000
noncomputable section
namespace AgentUCTSavedPriorDiagnostic
open AgentUCTSavedBudget AgentUCTObservability AgentUCTPhysicalDiagnostic
  AgentUCTNativeBudget AgentUCTPanelAllocation AgentUCTNativeRepair AgentUCTNativeRefinement AgentUCTPaper

def savedWidthFourPrior : ℝ := 4201.545544703999
def savedWidthFourCap : ℝ := 86133.78654208

theorem initial_resource_cache_no_width_four :
    ∀ r ∈ initialCache,resourceAction r ≠ .width 1 := by decide

theorem initial_own_width_four_pool_empty (caps : Act → ℝ) (reward : List Act → ℝ)
    (r : Fin 150 × List Act) (ha : resourceAction r = .width 1) :
    selectedCallPool (taskMeans panel150 integerTariffs caps (0:Fin 150) (initialization reward)) r = ∅ := by
  apply Finset.eq_empty_iff_forall_notMem.mpr
  intro i hi
  obtain ⟨hseen,hact⟩ := selected_call_pool_valid _ r i hi
  obtain ⟨hs,hp,hm⟩ := task_means_full_cache_metadata_and_bill panel150 integerTariffs caps
    (0:Fin 150) (initialization reward)
  rw [hs] at hseen
  obtain ⟨s,hs,hid⟩ := Finset.mem_image.mp hseen
  rw [← hid,(hm s hs).1,ha] at hact
  have hu : ((),s.2) ∈ initialCache := by
    have hprod := hs
    rw [own_panel_cache_product] at hprod
    have hpath := (Finset.mem_product.mp hprod).2
    rw [← initialization_cache_exact reward,← unit_panel_cache_is_own,own_panel_cache_product]
    exact Finset.mem_product.mpr ⟨by simp,hpath⟩
  exact initial_resource_cache_no_width_four _ hu (by simpa [resourceAction] using hact)

theorem initial_saved_width_four_quote (priors caps : Act → ℝ) (reward : List Act → ℝ)
    (hp : priors (.width 1) = savedWidthFourPrior) (hc : caps (.width 1) = savedWidthFourCap) :
    liveReceiptPrice priors caps
      (taskMeans panel150 integerTariffs caps (0:Fin 150) (initialization reward))
      ((0:Fin 150),aCold.take 4) = savedWidthFourPrior := by
  have ha : resourceAction ((0:Fin 150),aCold.take 4) = .width 1 := by simp [resourceAction,aCold,leaf]
  unfold liveReceiptPrice
  rw [initial_own_width_four_pool_empty caps reward _ ha]
  simp only [onlineMean,Finset.card_empty,Finset.sum_empty,Nat.cast_zero,zero_add,add_zero,div_one,ha,hp,hc]
  norm_num [savedWidthFourCap,savedWidthFourPrior]

theorem initial_saved_width_four_error_exceeds_uniform (priors caps : Act → ℝ) (reward : List Act → ℝ)
    (hp : priors (.width 1) = savedWidthFourPrior) (hc : caps (.width 1) = savedWidthFourCap) :
    uniformQuoteError < |liveReceiptPrice priors caps
      (taskMeans panel150 integerTariffs caps (0:Fin 150) (initialization reward))
      ((0:Fin 150),aCold.take 4)-integerTariffs.w4| := by
  rw [initial_saved_width_four_quote priors caps reward hp hc]
  norm_num [uniformQuoteError,savedWidthFourPrior,integerTariffs,generatorRate]

theorem saved_width_four_prior_not_uniform_admissible (priors caps : Act → ℝ)
    (hp : priors (.width 1) = savedWidthFourPrior) (hc : caps (.width 1) = savedWidthFourCap) :
    ¬ AdmissibleInitialPrices integerTariffs priors caps uniformQuoteError := by
  intro hadm
  have hb := hadm.2.2.1 (.width 1)
  rw [hp,hc] at hb
  norm_num [savedWidthFourPrior,savedWidthFourCap,uniformQuoteError,tariff,taskTariff,integerTariffs,generatorRate] at hb

#print axioms savedWidthFourPrior
#print axioms savedWidthFourCap
#print axioms initial_resource_cache_no_width_four
#print axioms initial_own_width_four_pool_empty
#print axioms initial_saved_width_four_quote
#print axioms initial_saved_width_four_error_exceeds_uniform
#print axioms saved_width_four_prior_not_uniform_admissible
end AgentUCTSavedPriorDiagnostic
