import PhysicalTariffInputs
import Mathlib.Analysis.Complex.ExponentialBounds



set_option autoImplicit false
set_option maxRecDepth 16384
set_option maxHeartbeats 4000000
noncomputable section
namespace AgentUCTPhysicalDiagnostic
open AgentUCTNativeBudget AgentUCTPanelAllocation AgentUCTNativeRepair AgentUCTNativeRefinement AgentUCTPaper

theorem log_ten_gt_one : (1:ℝ) < Real.log 10 := by
  have he : Real.exp 1 < (10:ℝ) := lt_trans Real.exp_one_lt_d9 (by norm_num)
  have hh := Real.log_lt_log (Real.exp_pos 1) he
  simpa using hh

theorem fixed_exploration_bounds :
    (7/25:ℝ) < bonusGap2 (7/5) ∧ bonusGap2 (7/5) < 6 ∧ bonusGap3 (7/5) < 6 := by
  have hl : 0 < Real.log (10:ℝ) := lt_trans (by norm_num) log_ten_gt_one
  have hr := Real.sqrt_nonneg (Real.log (10:ℝ))
  have hs := Real.sqrt_nonneg (Real.log (10:ℝ)/2)
  have hr2 := Real.sq_sqrt hl.le
  have hs2 := Real.sq_sqrt (show 0 ≤ Real.log (10:ℝ)/2 by positivity)
  have hR : (1:ℝ) ≤ Real.sqrt (Real.log 10) := by
    have hh := Real.sqrt_le_sqrt log_ten_gt_one.le
    simpa using hh
  have hS : Real.sqrt (Real.log (10:ℝ)/2) < (4/5)*Real.sqrt (Real.log 10) := by
    by_contra hn
    have hle : (4/5)*Real.sqrt (Real.log (10:ℝ)) ≤ Real.sqrt (Real.log (10:ℝ)/2) := not_lt.mp hn
    have hh := mul_nonneg (sub_nonneg.mpr hle)
      (show 0 ≤ Real.sqrt (Real.log (10:ℝ)/2)+(4/5)*Real.sqrt (Real.log 10) by positivity)
    nlinarith
  have hlog10 := Real.log_le_sub_one_of_pos (by norm_num : (0:ℝ) < 10)
  have hlog11 := Real.log_le_sub_one_of_pos (by norm_num : (0:ℝ) < 11)
  have hten := Real.sqrt_le_sqrt (show Real.log (10:ℝ) ≤ 16 by linarith)
  have heleven := Real.sqrt_le_sqrt (show Real.log (11:ℝ) ≤ 16 by linarith)
  norm_num at hten heleven
  have hs11 := Real.sqrt_nonneg (Real.log (11:ℝ)/3)
  dsimp only [bonusGap2,bonusGap3]
  constructor
  · nlinarith
  constructor <;> nlinarith

theorem beta2_root_margins :
    RootMargins integerTariffs (7/5) (2/(generatorRate*2331)) (2/5) (1/2) := by
  obtain ⟨hlo,hhi,h3⟩ := fixed_exploration_bounds
  constructor <;>
    norm_num [integerTariffs,generatorRate,e5Rate,bgeRate,embeddingRate,normalForecastBill,tailBill] <;> linarith

theorem beta2_resource_window : StrictResourceWindow 150 integerTariffs (1/10000000) := by
  norm_num [StrictResourceWindow,integerTariffs,tailBill,crossBill,generatorRate,e5Rate,bgeRate,embeddingRate]

theorem beta2_retained_gap_bracket :
    (2/5:ℝ)-1/2 < (1/20)*(panel150.card : ℝ)*(integerTariffs.bge-integerTariffs.normalE5)/classCref panel150 integerTariffs ∧
    (1/20)*(panel150.card : ℝ)*(integerTariffs.bge-integerTariffs.normalE5)/classCref panel150 integerTariffs < (1/2:ℝ)-2/5 := by
  rw [panel150_integer_cref,AgentUCTNativeBudget.panel150_cardinality]
  norm_num [integerTariffs,generatorRate,e5Rate,bgeRate]

theorem beta2_causal_error_inputs_inhabited :
    ∃ epsilon : ℝ,0 < epsilon ∧
      AdmissibleInitialPrices integerTariffs (perturbedPriors integerTariffs epsilon)
        (perturbedCaps integerTariffs epsilon) epsilon ∧
      ErrorMargins integerTariffs (7/5) (2/(generatorRate*2331)) (2/5) (1/2)
        (10*(2/(generatorRate*2331))*epsilon) := by
  obtain ⟨epsilon,he,hh,hm⟩ := root_margin_positive_error_exists integerTariffs _ _ _ _ beta2_root_margins
  exact ⟨epsilon,he,perturbed_initial_prices_admissible _ _ he hh integer_tariffs_positive_floor,hm⟩

end AgentUCTPhysicalDiagnostic
