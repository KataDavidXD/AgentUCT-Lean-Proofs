import AgentUCTPaper.Probability
import AgentUCTPaper.Regret

/-! # Expected regret derived from reward concentration

This file composes the all-round deterministic bound with the independently
proved concentration and union bounds. No successful confidence event is an
assumption. Costs may be arbitrary functions of the outcome and local time.
-/

noncomputable section

open MeasureTheory ProbabilityTheory Finset
open scoped NNReal

namespace AgentUCTPaper

variable {Ω Arm : Type*} [MeasurableSpace Ω] {P : Measure Ω}
  [IsProbabilityMeasure P] [Fintype Arm] [DecidableEq Arm]

omit [Fintype Arm] in
theorem pullCount_le_time (action : ℕ → Arm) (arm : Arm) (t : ℕ) :
    AgentUCT.pullCount action arm t ≤ t := by
  unfold AgentUCT.pullCount
  have h := Finset.card_le_card (Finset.filter_subset
    (s := Finset.range t) (p := fun s ↦ action s = arm))
  simpa only [Finset.card_range] using h

omit [MeasurableSpace Ω] in
/-- Confidence at an adaptively chosen count is derived by a union over all
possible counts, with no independence requirement on the random count itself. -/
theorem sample_mean_confidence
    (S : Arm → ℕ → Ω → ℝ) (action : Ω → ℕ → Arm)
    (mu : Arm → ℝ) (q : Ω → ℕ → Arm → ℝ)
    {ω : Ω} {t : ℕ} {arm : Arm}
    (hCount : 0 < AgentUCT.pullCount (action ω) arm t)
    (hQ : q ω t arm = mu arm +
      S arm (AgentUCT.pullCount (action ω) arm t) ω /
        (AgentUCT.pullCount (action ω) arm t : ℝ))
    (hGood : ω ∉ badAt Finset.univ S t) :
    |q ω t arm - mu arm| ≤ localRadius (action ω) arm t := by
  rw [hQ]
  simp only [add_sub_cancel_left]
  exact not_badAt_error Finset.univ S (Finset.mem_univ arm) hCount
    (pullCount_le_time (action ω) arm t) hGood

/-- A complete expected bound for a local node and the same-cache comparator.
The centered-sum MGF assumption is constructed from independent [0,1] reward
streams in `Probability.lean`. The estimator identity links those streams to Q.
All arms have at least one observation after the initialization period.
-/
theorem expected_local_regret
    (S : Arm → ℕ → Ω → ℝ) (action best : Ω → ℕ → Arm)
    (mu : Arm → ℝ) (q cost : Ω → ℕ → Arm → ℝ) (lambda : ℝ)
    {T : ℕ} {delta D : ℝ}
    (hT : 1 ≤ T) (hDelta : 0 < delta) (hD : 0 ≤ D)
    (hMeas : ∀ a n, Measurable (S a n))
    (hMGF : ∀ a n, 0 < n → HasSubgaussianMGF (S a n) ((n : ℝ≥0) / 4) P)
    (hQ : ∀ ω t, t < T → Fintype.card Arm ≤ t → ∀ a,
      q ω t a = mu a + S a (AgentUCT.pullCount (action ω) a t) ω /
        (AgentUCT.pullCount (action ω) a t : ℝ))
    (hCount : ∀ ω t, t < T → Fintype.card Arm ≤ t → ∀ a,
      0 < AgentUCT.pullCount (action ω) a t)
    (hGapNonneg : ∀ ω t, t < T →
      0 ≤ localGap mu (cost ω) lambda (action ω) (best ω) t)
    (hGapUpper : ∀ ω t, t < T →
      localGap mu (cost ω) lambda (action ω) (best ω) t ≤ D)
    (hSeparated : ∀ ω t, t < T →
      0 < localGap mu (cost ω) lambda (action ω) (best ω) t →
      delta ≤ localGap mu (cost ω) lambda (action ω) (best ω) t)
    (hSelect : ∀ ω t, t < T → Fintype.card Arm ≤ t →
      q ω t (best ω t) + localRadius (action ω) (best ω t) t -
        lambda * cost ω t (best ω t) ≤
      q ω t (action ω t) + localRadius (action ω) (action ω t) t -
        lambda * cost ω t (action ω t))
    (hIntegrable : Integrable (fun ω ↦ ∑ t ∈ Finset.range T,
      localGap mu (cost ω) lambda (action ω) (best ω) t) P) :
    (∫ ω, (∑ t ∈ Finset.range T,
      localGap mu (cost ω) lambda (action ω) (best ω) t) ∂P) ≤
      (Fintype.card Arm : ℝ) * D * (8 * Real.log (T : ℝ) / delta ^ 2 + 6) := by
  classical
  let B := (Fintype.card Arm : ℝ) * D * (8 * Real.log (T : ℝ) / delta ^ 2 + 2)
  have hPath (ω : Ω) : (∑ t ∈ Finset.range T,
      localGap mu (cost ω) lambda (action ω) (best ω) t) ≤
      B + D * badCount Finset.univ S T ω := by
    apply local_regret_all_rounds (action ω) (best ω) mu (q ω) (cost ω) lambda
      (fun t ↦ ω ∈ badAt Finset.univ S t) hT hDelta hD
      (hGapNonneg ω) (hGapUpper ω) (hSeparated ω)
    · intro t ht hk
      exact hCount ω t ht hk (action ω t)
    · intro t ht hk hg
      have hc := sample_mean_confidence S action mu q (hCount ω t ht hk (best ω t))
        (hQ ω t ht hk (best ω t)) hg
      have := (abs_le.mp hc).1
      linarith
    · intro t ht hk hg
      have hc := sample_mean_confidence S action mu q (hCount ω t ht hk (action ω t))
        (hQ ω t ht hk (action ω t)) hg
      have := (abs_le.mp hc).2
      linarith
    · exact hSelect ω
  have hBadInt := badCount_integrable (μ := P) Finset.univ S hMeas T
  have hBInt : Integrable (fun ω ↦ B + D * badCount Finset.univ S T ω) P :=
    (integrable_const B).add (hBadInt.const_mul D)
  have hInt := integral_mono hIntegrable hBInt hPath
  have hBad := expected_badCount (μ := P) Finset.univ S hMeas
    (fun a _ n hn ↦ hMGF a n hn) T
  rw [integral_add (integrable_const B) (hBadInt.const_mul D)] at hInt
  simp only [integral_const_mul, integral_const, measureReal_univ_eq_one, one_smul,
    Finset.card_univ] at hInt hBad
  dsimp only [B] at hInt
  nlinarith

/-- Expected error-budget composition. The probability of a confidence failure
is derived from the centered streams. `hOptimism` is the structural gap inequality
supplied by `drift_plugin_gap_bound`, not an assumed probability bound. -/
theorem expected_regret_with_error_budget
    (S : Arm → ℕ → Ω → ℝ) (action : Ω → ℕ → Arm)
    (gap error : Ω → ℕ → ℝ)
    {T : ℕ} {delta D : ℝ}
    (hT : 1 ≤ T) (hDelta : 0 < delta) (hD : 0 ≤ D)
    (hMeas : ∀ a n, Measurable (S a n))
    (hMGF : ∀ a n, 0 < n → HasSubgaussianMGF (S a n) ((n : ℝ≥0) / 4) P)
    (hGapNonneg : ∀ ω t, t < T → 0 ≤ gap ω t)
    (hGapUpper : ∀ ω t, t < T → gap ω t ≤ D)
    (hErrorNonneg : ∀ ω t, t < T → 0 ≤ error ω t)
    (hSeparated : ∀ ω t, t < T → 0 < gap ω t → delta ≤ gap ω t)
    (hCount : ∀ ω t, t < T → Fintype.card Arm ≤ t →
      0 < AgentUCT.pullCount (action ω) (action ω t) t)
    (hOptimism : ∀ ω t, t < T → Fintype.card Arm ≤ t →
      ω ∉ badAt Finset.univ S t →
      gap ω t ≤ 2 * localRadius (action ω) (action ω t) t + error ω t)
    (hRegretInt : Integrable (fun ω ↦ ∑ t ∈ Finset.range T, gap ω t) P)
    (hErrorInt : Integrable (fun ω ↦ ∑ t ∈ Finset.range T, error ω t) P) :
    (∫ ω, (∑ t ∈ Finset.range T, gap ω t) ∂P) ≤
      (Fintype.card Arm : ℝ) * D * (32 * Real.log (T : ℝ) / delta ^ 2 + 6) +
      2 * (∫ ω, (∑ t ∈ Finset.range T, error ω t) ∂P) := by
  classical
  let B := (Fintype.card Arm : ℝ) * D * (32 * Real.log (T : ℝ) / delta ^ 2 + 2)
  have hPath (ω : Ω) : (∑ t ∈ Finset.range T, gap ω t) ≤
      B + 2 * (∑ t ∈ Finset.range T, error ω t) + D * badCount Finset.univ S T ω :=
    local_regret_with_error_budget (action ω) (gap ω) (error ω)
      (fun t ↦ ω ∈ badAt Finset.univ S t) hT hDelta hD
      (hGapNonneg ω) (hGapUpper ω) (hErrorNonneg ω) (hSeparated ω)
      (hCount ω) (hOptimism ω)
  have hBadInt := badCount_integrable (μ := P) Finset.univ S hMeas T
  have hBaseInt : Integrable (fun ω ↦ B + 2 * ∑ t ∈ Finset.range T, error ω t) P :=
    (integrable_const B).add (hErrorInt.const_mul 2)
  have hInt := integral_mono hRegretInt (hBaseInt.add (hBadInt.const_mul D)) hPath
  change (∫ ω, (∑ t ∈ Finset.range T, gap ω t) ∂P) ≤
    (∫ ω, (B + 2 * (∑ t ∈ Finset.range T, error ω t) +
      D * badCount Finset.univ S T ω) ∂P) at hInt
  have hBad := expected_badCount (μ := P) Finset.univ S hMeas
    (fun a _ n hn ↦ hMGF a n hn) T
  rw [integral_add hBaseInt (hBadInt.const_mul D),
    integral_add (integrable_const B) (hErrorInt.const_mul 2)] at hInt
  simp only [integral_const_mul, integral_const, measureReal_univ_eq_one, one_smul,
    Finset.card_univ, B] at hInt hBad
  nlinarith

/-- Current value gaps allow the comparator's reward value to change with search. -/
def currentGap (current cost : Ω → ℕ → Arm → ℝ) (lambda : ℝ)
    (action best : Ω → ℕ → Arm) (ω : Ω) (t : ℕ) : ℝ :=
  AgentUCT.net (current ω t (best ω t)) (cost ω t (best ω t)) lambda -
    AgentUCT.net (current ω t (action ω t)) (cost ω t (action ω t)) lambda

/-- Sum of comparator and chosen-action reward drift and cost prediction errors. -/
def currentError (drift costError : Ω → ℕ → Arm → ℝ) (lambda : ℝ)
    (action best : Ω → ℕ → Arm) (ω : Ω) (t : ℕ) : ℝ :=
  drift ω t (best ω t) + drift ω t (action ω t) +
    lambda * (costError ω t (best ω t) + costError ω t (action ω t))

/-- Full expected bound with dynamic reward centers, true current values, and
plug-in predicted costs. Statistical concentration, reward drift, and prediction
error are separate hypotheses. In particular, no stationarity of tree returns
or successful confidence event is smuggled into the regret conclusion. -/
theorem expected_current_regret_with_errors
    (S : Arm → ℕ → Ω → ℝ) (action best : Ω → ℕ → Arm)
    (center current q cost estimate drift costError : Ω → ℕ → Arm → ℝ)
    (lambda : ℝ) {T : ℕ} {delta D : ℝ}
    (hLambda : 0 ≤ lambda)
    (hT : 1 ≤ T) (hDelta : 0 < delta) (hD : 0 ≤ D)
    (hMeas : ∀ a n, Measurable (S a n))
    (hMGF : ∀ a n, 0 < n → HasSubgaussianMGF (S a n) ((n : ℝ≥0) / 4) P)
    (hQ : ∀ ω t, t < T → Fintype.card Arm ≤ t → ∀ a,
      q ω t a = center ω t a + S a (AgentUCT.pullCount (action ω) a t) ω /
        (AgentUCT.pullCount (action ω) a t : ℝ))
    (hCount : ∀ ω t, t < T → Fintype.card Arm ≤ t → ∀ a,
      0 < AgentUCT.pullCount (action ω) a t)
    (hDrift : ∀ ω t, t < T → ∀ a, |current ω t a - center ω t a| ≤ drift ω t a)
    (hCostError : ∀ ω t, t < T → ∀ a, |estimate ω t a - cost ω t a| ≤ costError ω t a)
    (hGapNonneg : ∀ ω t, t < T → 0 ≤ currentGap current cost lambda action best ω t)
    (hGapUpper : ∀ ω t, t < T → currentGap current cost lambda action best ω t ≤ D)
    (hSeparated : ∀ ω t, t < T → 0 < currentGap current cost lambda action best ω t →
      delta ≤ currentGap current cost lambda action best ω t)
    (hSelect : ∀ ω t, t < T → Fintype.card Arm ≤ t →
      q ω t (best ω t) + localRadius (action ω) (best ω t) t -
        lambda * estimate ω t (best ω t) ≤
      q ω t (action ω t) + localRadius (action ω) (action ω t) t -
        lambda * estimate ω t (action ω t))
    (hRegretInt : Integrable (fun ω ↦ ∑ t ∈ Finset.range T,
      currentGap current cost lambda action best ω t) P)
    (hErrorInt : Integrable (fun ω ↦ ∑ t ∈ Finset.range T,
      currentError drift costError lambda action best ω t) P) :
    (∫ ω, (∑ t ∈ Finset.range T, currentGap current cost lambda action best ω t) ∂P) ≤
      (Fintype.card Arm : ℝ) * D * (32 * Real.log (T : ℝ) / delta ^ 2 + 6) +
      2 * (∫ ω, (∑ t ∈ Finset.range T, currentError drift costError lambda action best ω t) ∂P) := by
  apply expected_regret_with_error_budget S action (currentGap current cost lambda action best)
    (currentError drift costError lambda action best) hT hDelta hD hMeas hMGF
    hGapNonneg hGapUpper _ hSeparated _ _ hRegretInt hErrorInt
  · intro ω t ht
    have hd (a : Arm) : 0 ≤ drift ω t a := (abs_nonneg _).trans (hDrift ω t ht a)
    have he (a : Arm) : 0 ≤ costError ω t a := (abs_nonneg _).trans (hCostError ω t ht a)
    exact add_nonneg (add_nonneg (hd _) (hd _))
      (mul_nonneg hLambda (add_nonneg (he _) (he _)))
  · intro ω t ht hk
    exact hCount ω t ht hk (action ω t)
  · intro ω t ht hk hGood
    have hc (a : Arm) : |q ω t a - center ω t a| ≤ localRadius (action ω) a t := by
      rw [hQ ω t ht hk a]
      simp only [add_sub_cancel_left]
      exact not_badAt_error Finset.univ S (Finset.mem_univ a) (hCount ω t ht hk a)
        (pullCount_le_time (action ω) a t) hGood
    have hb := (abs_le.mp (hc (best ω t))).1
    have ha := (abs_le.mp (hc (action ω t))).2
    have hdb := (abs_le.mp (hDrift ω t ht (best ω t))).2
    have hda := (abs_le.mp (hDrift ω t ht (action ω t))).1
    have heb := (abs_le.mp (hCostError ω t ht (best ω t))).2
    have hea := (abs_le.mp (hCostError ω t ht (action ω t))).1
    have h := drift_plugin_gap_bound hLambda (by linarith :
        center ω t (best ω t) ≤ q ω t (best ω t) + localRadius (action ω) (best ω t) t)
      (by linarith : q ω t (action ω t) ≤
        center ω t (action ω t) + localRadius (action ω) (action ω t) t)
      hdb (by linarith : center ω t (action ω t) - current ω t (action ω t) ≤
        drift ω t (action ω t)) heb
      (by linarith : cost ω t (action ω t) - estimate ω t (action ω t) ≤
        costError ω t (action ω t)) (hSelect ω t ht hk)
    simpa only [currentGap, currentError, add_assoc] using h

#print axioms sample_mean_confidence
#print axioms expected_local_regret
#print axioms expected_regret_with_error_budget
#print axioms expected_current_regret_with_errors

end AgentUCTPaper
