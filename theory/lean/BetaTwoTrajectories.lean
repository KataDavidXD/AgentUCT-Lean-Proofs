import BetaTwoMargins




set_option autoImplicit false
set_option maxRecDepth 16384
set_option maxHeartbeats 4000000
noncomputable section
namespace AgentUCTPhysicalDiagnostic
open AgentUCTNativeBudget AgentUCTPanelAllocation AgentUCTNativeRepair AgentUCTNativeRefinement AgentUCTPaper

def diagnosticRun (epsilon : ℝ) (mode : ForecastMode) (adverse : Bool) (cap : ℕ) :=
  causalTaskRun panel150 mode integerTariffs (perturbedPriors integerTariffs epsilon)
    (perturbedCaps integerTariffs epsilon) 0 adverse (2/5) (1/2) (7/5) 2 (classCref panel150 integerTariffs) cap

def diagnosticNet (epsilon : ℝ) (mode : ForecastMode) (adverse : Bool) (cap : ℕ) : ℝ :=
  causalRetainedNet panel150 mode integerTariffs (perturbedPriors integerTariffs epsilon)
    (perturbedCaps integerTariffs epsilon) 0 adverse (2/5) (1/2) (7/5) 2 (classCref panel150 integerTariffs)
    (1/10000000) (1/20) cap

theorem beta2_complete_causal_class_nonempty (cap : ℕ) (hcap : 11 ≤ cap) :
    ∃ epsilon : ℝ,0 < epsilon ∧
      (∀ adverse : Bool,
        diagnosticRun epsilon .complete adverse cap = aEleven (taskReward adverse (2/5) (1/2)) ∧
        diagnosticRun epsilon .next adverse cap = bTen (taskReward adverse (2/5) (1/2))) ∧
      diagnosticNet epsilon .next false cap < diagnosticNet epsilon .complete false cap ∧
      diagnosticNet epsilon .complete true cap < diagnosticNet epsilon .next true cap ∧
      0 < |liveReceiptPrice (perturbedPriors integerTariffs epsilon) (perturbedCaps integerTariffs epsilon)
        (taskMeans panel150 integerTariffs (perturbedCaps integerTariffs epsilon) 0
          (initialization (taskReward false (2/5) (1/2)))) (0,aCold.take 2)-integerTariffs.bge| := by
  obtain ⟨epsilon,he,hp,hm⟩ := beta2_causal_error_inputs_inhabited
  have hs : 0 ≤ (2:ℝ)/classCref panel150 integerTariffs := by
    rw [panel150_integer_cref]; norm_num [generatorRate]
  have hr : RootMargins integerTariffs (7/5) (penaltyScale panel150 2 (classCref panel150 integerTariffs)) (2/5) (1/2) := by
    rw [beta2_integer_penalty_scale]; exact beta2_root_margins
  have herr : ErrorMargins integerTariffs (7/5) (penaltyScale panel150 2 (classCref panel150 integerTariffs)) (2/5) (1/2)
      (10*(penaltyScale panel150 2 (classCref panel150 integerTariffs))*epsilon) := by
    simpa only [beta2_integer_penalty_scale] using hm
  have hw : StrictResourceWindow (panel150.card : ℝ) integerTariffs (1/10000000) := by
    rw [AgentUCTNativeBudget.panel150_cardinality]; exact beta2_resource_window
  have hsep := causal_positive_and_adverse_separation_same_controls panel150 integerTariffs _ _ (0 : Fin 150)
    (2/5) (1/2) (7/5) 2 _ epsilon (1/10000000) (1/20) cap hcap hs hp hr herr hw
    integer_tariffs_nonnegative beta2_retained_gap_bracket
  refine ⟨epsilon,he,?_,hsep.1,hsep.2,?_⟩
  · intro adverse
    exact causal_both_task_histories_generated panel150 integerTariffs _ _ 0 adverse (2/5) (1/2)
      (7/5) 2 _ epsilon (1/10000000) cap hcap hs hp hr herr hw integer_tariffs_nonnegative
  · exact common_initial_bge_actual_nonzero_error panel150 integerTariffs 0 _ epsilon he
      (by norm_num [integerTariffs,bgeRate])

theorem beta2_reward_bounds_and_true_optimum (adverse : Bool) :
    (∀ path,0 ≤ taskReward adverse (2/5) (1/2) path ∧ taskReward adverse (2/5) (1/2) path ≤ 1) ∧
    (∀ path,Terminal path → taskReward adverse (2/5) (1/2) path ≤ 1/2) ∧
    (∃ path,Terminal path ∧ taskReward adverse (2/5) (1/2) path = 1/2) := by
  constructor
  · intro path
    exact task_reward_unit_interval adverse (2/5) (1/2) (by norm_num) (by norm_num) path
  · exact task_true_terminal_optimum adverse (2/5) (1/2) (by norm_num) (by norm_num)

end AgentUCTPhysicalDiagnostic
