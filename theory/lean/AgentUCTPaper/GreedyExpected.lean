import AgentUCTPaper.Expected
import AgentUCTPaper.Greedy
import AgentUCTPaper.CacheExpectation

/-! # Expected full-cost regret of next-edge UCB

Only the chosen omitted cost is charged. This one-sided comparison allows
persistent cache accounting to bound the approximation term later.
-/

noncomputable section

open MeasureTheory ProbabilityTheory Finset
open scoped NNReal

namespace AgentUCTPaper

/-- The implemented clipped difference is zero when the child checkpoint is
already present and the parent's missing-cost baseline is nonnegative. -/
theorem cached_child_next_penalty_zero {baseline : ℝ} (h : 0 ≤ baseline) :
    max 0 (0 - baseline) = 0 := by
  exact max_eq_left (by linarith)

/-- If every candidate's next-edge penalty is zero, selection is ordinary UCB,
including its entire set of tied maximizers. -/
theorem zero_next_penalty_recovers_ucb {Arm : Type*}
    (q radius edge : Arm → ℝ) (lambda : ℝ) (chosen : Arm)
    (hZero : ∀ a, edge a = 0) :
    (∀ a, q a + radius a - lambda * edge a ≤
      q chosen + radius chosen - lambda * edge chosen) ↔
    (∀ a, q a + radius a ≤ q chosen + radius chosen) := by
  simp only [hZero, mul_zero, sub_zero]

variable {Ω Arm : Type*} [MeasurableSpace Ω] {P : Measure Ω}
  [IsProbabilityMeasure P] [Fintype Arm] [DecidableEq Arm]

/-- The next-edge rule has a full-cost expected regret bound with a one-sided
omitted-tail budget, rather than a sum of both arms' absolute cost errors. -/
theorem expected_next_edge_regret
    (S : Arm → ℕ → Ω → ℝ) (action best : Ω → ℕ → Arm)
    (mu : Arm → ℝ) (q cost edge tail : Ω → ℕ → Arm → ℝ) (lambda : ℝ)
    {T : ℕ} {delta D : ℝ}
    (hLambda : 0 ≤ lambda) (hT : 1 ≤ T) (hDelta : 0 < delta) (hD : 0 ≤ D)
    (hMeas : ∀ a n, Measurable (S a n))
    (hMGF : ∀ a n, 0 < n → HasSubgaussianMGF (S a n) ((n : ℝ≥0) / 4) P)
    (hQ : ∀ ω t, t < T → Fintype.card Arm ≤ t → ∀ a,
      q ω t a = mu a + S a (AgentUCT.pullCount (action ω) a t) ω /
        (AgentUCT.pullCount (action ω) a t : ℝ))
    (hCount : ∀ ω t, t < T → Fintype.card Arm ≤ t → ∀ a,
      0 < AgentUCT.pullCount (action ω) a t)
    (hDecomp : ∀ ω t, t < T → ∀ a, cost ω t a = edge ω t a + tail ω t a)
    (hTail : ∀ ω t, t < T → ∀ a, 0 ≤ tail ω t a)
    (hGapNonneg : ∀ ω t, t < T →
      0 ≤ localGap mu (cost ω) lambda (action ω) (best ω) t)
    (hGapUpper : ∀ ω t, t < T →
      localGap mu (cost ω) lambda (action ω) (best ω) t ≤ D)
    (hSeparated : ∀ ω t, t < T →
      0 < localGap mu (cost ω) lambda (action ω) (best ω) t →
      delta ≤ localGap mu (cost ω) lambda (action ω) (best ω) t)
    (hSelect : ∀ ω t, t < T → Fintype.card Arm ≤ t →
      q ω t (best ω t) + localRadius (action ω) (best ω t) t -
        lambda * edge ω t (best ω t) ≤
      q ω t (action ω t) + localRadius (action ω) (action ω t) t -
        lambda * edge ω t (action ω t))
    (hRegretInt : Integrable (fun ω ↦ ∑ t ∈ range T,
      localGap mu (cost ω) lambda (action ω) (best ω) t) P)
    (hTailInt : Integrable (fun ω ↦ ∑ t ∈ range T, tail ω t (action ω t)) P) :
    (∫ ω, (∑ t ∈ range T,
      localGap mu (cost ω) lambda (action ω) (best ω) t) ∂P) ≤
      (Fintype.card Arm : ℝ) * D * (32 * Real.log (T : ℝ) / delta ^ 2 + 6) +
      2 * lambda * (∫ ω, (∑ t ∈ range T, tail ω t (action ω t)) ∂P) := by
  have hErrInt : Integrable
      (fun ω ↦ ∑ t ∈ range T, lambda * tail ω t (action ω t)) P := by
    simpa only [← Finset.mul_sum] using hTailInt.const_mul lambda
  have h := expected_regret_with_error_budget S action
    (fun ω t ↦ localGap mu (cost ω) lambda (action ω) (best ω) t)
    (fun ω t ↦ lambda * tail ω t (action ω t)) hT hDelta hD hMeas hMGF
    hGapNonneg hGapUpper (fun ω t ht ↦ mul_nonneg hLambda (hTail ω t ht _))
    hSeparated (fun ω t ht hk ↦ hCount ω t ht hk _) ?_ hRegretInt hErrInt
  · simpa only [← Finset.mul_sum, integral_const_mul, mul_assoc] using h
  · intro ω t ht hk hGood
    have hc (a : Arm) := sample_mean_confidence S action mu q
      (hCount ω t ht hk a) (hQ ω t ht hk a) hGood
    have hp := nonnegative_tail_gap_bound (tailChosen := tail ω t (action ω t))
      hLambda (hTail ω t ht (best ω t))
      (by linarith [(abs_le.mp (hc (best ω t))).1] :
        mu (best ω t) ≤ q ω t (best ω t) + localRadius (action ω) (best ω t) t)
      (by linarith [(abs_le.mp (hc (action ω t))).2] :
        q ω t (action ω t) ≤ mu (action ω t) + localRadius (action ω) (action ω t) t)
      (hSelect ω t ht hk)
    simpa only [localGap, hDecomp ω t ht] using hp

/-- Persistent materialization converts omitted cold work into a finite additive
regret term. Conditional calibration is explicit; no cumulative error bound is assumed. -/
theorem expected_next_edge_regret_with_cache
    {Resource : Type*} [DecidableEq Resource]
    (S : Arm → ℕ → Ω → ℝ) (action best : Ω → ℕ → Arm)
    (mu : Arm → ℝ) (q cost edge tail : Ω → ℕ → Arm → ℝ) (lambda : ℝ)
    {T : ℕ} {delta D : ℝ}
    (hLambda : 0 ≤ lambda) (hT : 1 ≤ T) (hDelta : 0 < delta) (hD : 0 ≤ D)
    (hMeas : ∀ a n, Measurable (S a n))
    (hMGF : ∀ a n, 0 < n → HasSubgaussianMGF (S a n) ((n : ℝ≥0) / 4) P)
    (hQ : ∀ ω t, t < T → Fintype.card Arm ≤ t → ∀ a,
      q ω t a = mu a + S a (AgentUCT.pullCount (action ω) a t) ω /
        (AgentUCT.pullCount (action ω) a t : ℝ))
    (hCount : ∀ ω t, t < T → Fintype.card Arm ≤ t → ∀ a,
      0 < AgentUCT.pullCount (action ω) a t)
    (hDecomp : ∀ ω t, t < T → ∀ a, cost ω t a = edge ω t a + tail ω t a)
    (hTail : ∀ ω t, t < T → ∀ a, 0 ≤ tail ω t a)
    (hGapNonneg : ∀ ω t, t < T →
      0 ≤ localGap mu (cost ω) lambda (action ω) (best ω) t)
    (hGapUpper : ∀ ω t, t < T →
      localGap mu (cost ω) lambda (action ω) (best ω) t ≤ D)
    (hSeparated : ∀ ω t, t < T →
      0 < localGap mu (cost ω) lambda (action ω) (best ω) t →
      delta ≤ localGap mu (cost ω) lambda (action ω) (best ω) t)
    (hSelect : ∀ ω t, t < T → Fintype.card Arm ≤ t →
      q ω t (best ω t) + localRadius (action ω) (best ω t) t -
        lambda * edge ω t (best ω t) ≤
      q ω t (action ω t) + localRadius (action ω) (action ω t) t -
        lambda * edge ω t (action ω t))
    (hRegretInt : Integrable (fun ω ↦ ∑ t ∈ range T,
      localGap mu (cost ω) lambda (action ω) (best ω) t) P)
    (weight : Resource → ℝ) (hWeight : ∀ r, 0 ≤ weight r)
    (cached demand : Ω → ℕ → Finset Resource) (initial resourceSet : Finset Resource)
    (hInitial : ∀ ω, cached ω 0 = initial)
    (hStep : ∀ ω t, cached ω (t + 1) = cached ω t ∪ demand ω t)
    (hUniverse : ∀ ω, cached ω T ⊆ resourceSet)
    (actual : Ω → ℕ → ℝ)
    (hActual : ∀ ω t, t ∈ range T →
      0 ≤ actual ω t ∧ actual ω t ≤ coldWork weight (cached ω t) (demand ω t))
    (hActualInt : ∀ t ∈ range T, Integrable (fun ω ↦ actual ω t) P)
    (info : ℕ → MeasurableSpace Ω) (hInfo : ∀ t, info t ≤ ‹MeasurableSpace Ω›)
    (hForecast : ∀ t ∈ range T, (fun ω ↦ tail ω t (action ω t)) =ᵐ[P]
      (fun ω ↦ conditionalColdForecast P info actual ω t)) :
    (∫ ω, (∑ t ∈ range T,
      localGap mu (cost ω) lambda (action ω) (best ω) t) ∂P) ≤
      (Fintype.card Arm : ℝ) * D * (32 * Real.log (T : ℝ) / delta ^ 2 + 6) +
      2 * lambda * (cacheWeight weight resourceSet - cacheWeight weight initial) := by
  have hTailInt : Integrable (fun ω ↦ ∑ t ∈ range T, tail ω t (action ω t)) P := by
    apply integrable_finset_sum
    intro t ht
    exact integrable_condExp.congr (hForecast t ht).symm
  have h := expected_next_edge_regret S action best mu q cost edge tail lambda
    hLambda hT hDelta hD hMeas hMGF hQ hCount hDecomp hTail
    hGapNonneg hGapUpper hSeparated hSelect hRegretInt hTailInt
  have hBudget := expected_forecast_cold_budget P weight hWeight cached demand initial
    resourceSet T hInitial hStep hUniverse actual (fun ω t ↦ tail ω t (action ω t))
    hActual hActualInt info hInfo hForecast
  exact h.trans (add_le_add_left
    (mul_le_mul_of_nonneg_left hBudget (mul_nonneg (by norm_num) hLambda)) _)

#print axioms expected_next_edge_regret_with_cache

#print axioms expected_next_edge_regret

end AgentUCTPaper
