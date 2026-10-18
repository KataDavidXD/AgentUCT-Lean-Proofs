import NativeCausalEndpoints





set_option autoImplicit false
set_option maxRecDepth 16384
set_option maxHeartbeats 4000000
set_option linter.constructorNameAsVariable false
noncomputable section
namespace AgentUCTNativeBudget
open AgentUCTPanelAllocation AgentUCTNativeRepair AgentUCTNativeRefinement AgentUCTPaper

def panel150 : Finset (Fin 150) := Finset.univ

theorem panel150_cardinality : panel150.card = 150 := by simp [panel150]

theorem panel150_reference_cref (c : ℝ) : classCref panel150 (feasibleTariffs c) = 450 := by
  rw [feasible_class_independent_cref,panel150_cardinality]
  norm_num

theorem panel150_calibrated_penalty_scale (c : ℝ) :
    penaltyScale panel150 3 (classCref panel150 (feasibleTariffs c)) = 1 := by
  rw [panel150_reference_cref]
  norm_num [penaltyScale,panel150_cardinality]

theorem panel150_complete_causal_class_nonempty (c : ℝ) (hc : 0 < c) (cap : ℕ) (hcap : 11 ≤ cap) :
    ∃ epsilon : ℝ,0 < epsilon ∧
      (∀ adverse : Bool,
        causalTaskRun panel150 .complete (feasibleTariffs c) (perturbedPriors (feasibleTariffs c) epsilon)
          (perturbedCaps (feasibleTariffs c) epsilon) 0 adverse (feasibleDelta c) (feasibleGood c) c 3
          (classCref panel150 (feasibleTariffs c)) cap = aEleven (taskReward adverse (feasibleDelta c) (feasibleGood c)) ∧
        causalTaskRun panel150 .next (feasibleTariffs c) (perturbedPriors (feasibleTariffs c) epsilon)
          (perturbedCaps (feasibleTariffs c) epsilon) 0 adverse (feasibleDelta c) (feasibleGood c) c 3
          (classCref panel150 (feasibleTariffs c)) cap = bTen (taskReward adverse (feasibleDelta c) (feasibleGood c))) ∧
      0 < |liveReceiptPrice (perturbedPriors (feasibleTariffs c) epsilon) (perturbedCaps (feasibleTariffs c) epsilon)
        (taskMeans panel150 (feasibleTariffs c) (perturbedCaps (feasibleTariffs c) epsilon) 0
          (initialization (taskReward false (feasibleDelta c) (feasibleGood c)))) (0,aCold.take 2)-1| ∧
      causalRetainedNet panel150 .next (feasibleTariffs c) (perturbedPriors (feasibleTariffs c) epsilon)
        (perturbedCaps (feasibleTariffs c) epsilon) 0 false (feasibleDelta c) (feasibleGood c) c 3
        (classCref panel150 (feasibleTariffs c)) 0 (feasibleGood c-feasibleDelta c) cap <
      causalRetainedNet panel150 .complete (feasibleTariffs c) (perturbedPriors (feasibleTariffs c) epsilon)
        (perturbedCaps (feasibleTariffs c) epsilon) 0 false (feasibleDelta c) (feasibleGood c) c 3
        (classCref panel150 (feasibleTariffs c)) 0 (feasibleGood c-feasibleDelta c) cap ∧
      causalRetainedNet panel150 .complete (feasibleTariffs c) (perturbedPriors (feasibleTariffs c) epsilon)
        (perturbedCaps (feasibleTariffs c) epsilon) 0 true (feasibleDelta c) (feasibleGood c) c 3
        (classCref panel150 (feasibleTariffs c)) 0 (feasibleGood c-feasibleDelta c) cap <
      causalRetainedNet panel150 .next (feasibleTariffs c) (perturbedPriors (feasibleTariffs c) epsilon)
        (perturbedCaps (feasibleTariffs c) epsilon) 0 true (feasibleDelta c) (feasibleGood c) c 3
        (classCref panel150 (feasibleTariffs c)) 0 (feasibleGood c-feasibleDelta c) cap := by
  obtain ⟨epsilon,he,hp,hm,herr⟩ := causal_error_class_nonempty c hc
  have hscale : 0 ≤ (3:ℝ)/classCref panel150 (feasibleTariffs c) := by rw [panel150_reference_cref]; norm_num
  have hroot : RootMargins (feasibleTariffs c) c
      (penaltyScale panel150 3 (classCref panel150 (feasibleTariffs c))) (feasibleDelta c) (feasibleGood c) := by
    rw [panel150_calibrated_penalty_scale]; exact root_structural_conditions_nonempty c hc
  have hmargin : ErrorMargins (feasibleTariffs c) c
      (penaltyScale panel150 3 (classCref panel150 (feasibleTariffs c))) (feasibleDelta c) (feasibleGood c)
      (10*(penaltyScale panel150 3 (classCref panel150 (feasibleTariffs c)))*epsilon) := by
    simpa only [panel150_calibrated_penalty_scale,mul_one] using hm
  have hwindow : StrictResourceWindow (panel150.card : ℝ) (feasibleTariffs c) 0 := by
    rw [panel150_cardinality]; exact resource_window_same_nonempty_class c hc
  have htariff := same_class_nonnegative_tariffs c hc
  have hg := positive_bounded_feasible_good c hc
  have hgap : 0 < feasibleGood c-feasibleDelta c := by unfold feasibleDelta; nlinarith [hg.1]
  have hcost : (feasibleGood c-feasibleDelta c)*(panel150.card : ℝ)*
      ((feasibleTariffs c).bge-(feasibleTariffs c).normalE5)/classCref panel150 (feasibleTariffs c) =
      (feasibleGood c-feasibleDelta c)/6 := by
    rw [panel150_reference_cref,panel150_cardinality]
    dsimp only [feasibleTariffs]
    ring
  have hsep := causal_positive_and_adverse_separation_same_controls panel150 (feasibleTariffs c)
    _ _ (0 : Fin 150) (feasibleDelta c) (feasibleGood c) c 3 _ epsilon 0
    (feasibleGood c-feasibleDelta c) cap hcap hscale hp hroot hmargin hwindow htariff
    (by rw [hcost]; constructor <;> linarith)
  refine ⟨epsilon,he,?_,?_,hsep.1,hsep.2⟩
  · intro adverse
    exact causal_both_task_histories_generated panel150 (feasibleTariffs c) _ _ 0 adverse
      (feasibleDelta c) (feasibleGood c) c 3 _ epsilon 0 cap hcap hscale hp hroot hmargin hwindow htariff
  · exact common_initial_bge_actual_nonzero_error panel150 (feasibleTariffs c) 0
      (taskReward false (feasibleDelta c) (feasibleGood c)) epsilon he (by simp [feasibleTariffs])

end AgentUCTNativeBudget
