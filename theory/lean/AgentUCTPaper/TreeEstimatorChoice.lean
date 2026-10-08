import AgentUCTPaper.TreeCostEstimation

/-! # A full conditional cost predictor and a cost-confidence allocation index -/

set_option autoImplicit false

noncomputable section

namespace AgentUCTPaper

open Finset

def finiteCostMean {Completion : Type*} (completions : Finset Completion)
    (law bill : Completion → ℝ) : ℝ := ∑ x ∈ completions, law x * bill x

def finiteCostMSE {Completion : Type*} (completions : Finset Completion)
    (law bill : Completion → ℝ) (estimate : ℝ) : ℝ :=
  ∑ x ∈ completions, law x * (bill x - estimate) ^ 2

theorem finite_cost_mse_decomposition {Completion : Type*} (completions : Finset Completion)
    (law bill : Completion → ℝ) (hMass : ∑ x ∈ completions, law x = 1) (estimate : ℝ) :
    finiteCostMSE completions law bill estimate =
      finiteCostMSE completions law bill (finiteCostMean completions law bill) +
        (estimate - finiteCostMean completions law bill) ^ 2 := by
  let mean := finiteCostMean completions law bill
  have hPoint (x : Completion) : law x * (bill x - estimate) ^ 2 =
      law x * (bill x - mean) ^ 2 + law x * (estimate - mean) ^ 2 +
        2 * (mean - estimate) * (law x * bill x - law x * mean) := by ring
  unfold finiteCostMSE
  simp_rw [hPoint]
  rw [sum_add_distrib, sum_add_distrib, ← sum_mul, hMass, one_mul, ← mul_sum,
    sum_sub_distrib, ← sum_mul, hMass, one_mul]
  change _ + _ + 2 * (mean - estimate) * (mean - mean) = _
  ring

theorem full_cost_mean_unique_mse_minimizer {Completion : Type*}
    (completions : Finset Completion) (law bill : Completion → ℝ)
    (hMass : ∑ x ∈ completions, law x = 1) (estimate : ℝ) :
    finiteCostMSE completions law bill (finiteCostMean completions law bill) ≤
      finiteCostMSE completions law bill estimate ∧
    (finiteCostMSE completions law bill estimate =
      finiteCostMSE completions law bill (finiteCostMean completions law bill) ↔
        estimate = finiteCostMean completions law bill) := by
  rw [finite_cost_mse_decomposition completions law bill hMass estimate]
  constructor
  · exact le_add_of_nonneg_right (sq_nonneg _)
  · constructor
    · intro h
      have hs : (estimate - finiteCostMean completions law bill) ^ 2 = 0 := by linarith
      exact sub_eq_zero.mp (sq_eq_zero_iff.mp hs)
    · intro h
      simp [h]

variable {Qid Action : Type*} [DecidableEq Qid] [DecidableEq Action]

theorem referenceFullCost_is_conditional_mean (qids : Finset Qid) (root : List Action)
    (terminals : Finset (List Action)) (weight : Qid × List Action → ℝ)
    (overhead law : List Action → ℝ) (cached : Finset (Qid × List Action)) (p : List Action) :
    referenceFullCost qids root terminals weight overhead law cached p =
      finiteCostMean (subtreeTerminals terminals p) law
        (fun leaf ↦ coldWork weight cached (panelDemand qids (root ++ leaf)) + overhead leaf) := rfl

def costLowerBound (estimate radius : ℝ) : ℝ := max 0 (estimate - radius)

theorem costLowerBound_valid {actual estimate radius : ℝ}
    (hActual : 0 ≤ actual) (hError : |estimate - actual| ≤ radius) :
    0 ≤ costLowerBound estimate radius ∧ costLowerBound estimate radius ≤ actual ∧
      actual - costLowerBound estimate radius ≤ 2 * radius := by
  obtain ⟨hLower, hUpper⟩ := abs_le.mp hError
  refine ⟨le_max_left _ _, max_le hActual (by linarith), ?_⟩
  have h := le_max_right 0 (estimate - radius)
  change actual - max 0 (estimate - radius) ≤ 2 * radius
  linarith

theorem costLowerBound_below_point {estimate radius : ℝ}
    (hEstimate : 0 ≤ estimate) (hRadius : 0 ≤ radius) :
    costLowerBound estimate radius ≤ estimate := max_le hEstimate (by linarith)

theorem costLowerBound_cached_zero {radius : ℝ} (hRadius : 0 ≤ radius) :
    costLowerBound 0 radius = 0 := by simp [costLowerBound, hRadius]

theorem net_optimism_from_cost_radius {mu q rewardRadius actualCost estimateCost costRadius beta : ℝ}
    (hBeta : 0 ≤ beta) (hReward : mu ≤ q + rewardRadius) (hCost : 0 ≤ actualCost)
    (hCostError : |estimateCost - actualCost| ≤ costRadius) :
    AgentUCT.net mu actualCost beta ≤
      q + rewardRadius - beta * costLowerBound estimateCost costRadius := by
  have hLower := (costLowerBound_valid hCost hCostError).2.1
  have hMul := mul_le_mul_of_nonneg_left hLower hBeta
  unfold AgentUCT.net
  linarith

theorem selected_net_gap_from_cost_radii
    {muBest muChosen qBest qChosen rBest rChosen actualBest actualChosen
      estimatedBest estimatedChosen errorBest errorChosen beta : ℝ}
    (hBeta : 0 ≤ beta) (hBest : muBest ≤ qBest + rBest)
    (hChosen : qChosen ≤ muChosen + rChosen) (hActualBest : 0 ≤ actualBest)
    (hActualChosen : 0 ≤ actualChosen)
    (hBestError : |estimatedBest - actualBest| ≤ errorBest)
    (hChosenError : |estimatedChosen - actualChosen| ≤ errorChosen)
    (hSelect : qBest + rBest - beta * costLowerBound estimatedBest errorBest ≤
      qChosen + rChosen - beta * costLowerBound estimatedChosen errorChosen) :
    AgentUCT.net muBest actualBest beta - AgentUCT.net muChosen actualChosen beta ≤
      2 * rChosen + 2 * beta * errorChosen := by
  exact AgentUCT.optimistic_cost_gap_bound hBeta hBest hChosen
    (costLowerBound_valid hActualBest hBestError).2.1
    (costLowerBound_valid hActualChosen hChosenError).2.2 hSelect

end AgentUCTPaper
