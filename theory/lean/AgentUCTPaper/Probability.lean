import AgentUCT
import Mathlib.Probability.Moments.SubGaussian
import Mathlib.MeasureTheory.Measure.Real

/-! Probability lemmas for the paper. Concentration is derived from a stated MGF
model, with a bounded independent observation construction, rather than assumed
as a successful confidence event. -/

noncomputable section
open MeasureTheory ProbabilityTheory Finset Real
open scoped NNReal

namespace AgentUCTPaper

variable {Ω : Type*} [MeasurableSpace Ω] {μ : Measure Ω} [IsProbabilityMeasure μ]

theorem subgaussian_abs_tail {X : Ω → ℝ} {v : ℝ≥0}
    (hX : HasSubgaussianMGF X v μ) {r : ℝ} (hr : 0 ≤ r) :
    μ.real {ω | r ≤ |X ω|} ≤ 2 * exp (-r ^ 2 / (2 * v)) := by
  have hset : {ω | r ≤ |X ω|} ⊆ {ω | r ≤ X ω} ∪ {ω | r ≤ -X ω} := by
    intro ω h
    by_cases hx : 0 ≤ X ω
    · exact Or.inl (by simpa [abs_of_nonneg hx] using h)
    · exact Or.inr (by simpa [abs_of_neg (lt_of_not_ge hx)] using h)
  calc
    _ ≤ μ.real ({ω | r ≤ X ω} ∪ {ω | r ≤ -X ω}) := measureReal_mono hset
    _ ≤ μ.real {ω | r ≤ X ω} + μ.real {ω | r ≤ -X ω} := measureReal_union_le _ _
    _ ≤ exp (-r ^ 2 / (2 * v)) + exp (-r ^ 2 / (2 * v)) :=
      add_le_add (hX.measure_ge_le hr) (hX.neg.measure_ge_le hr)
    _ = _ := by ring

/-- Centering independent bounded observations produces the required MGF model.
Independence is required only along the observation stream of a single arm. -/
theorem bounded_centered_subgaussian {X : ℕ → Ω → ℝ}
    (hX : ∀ j, AEMeasurable (X j) μ)
    (hBound : ∀ j, ∀ᵐ ω ∂μ, X j ω ∈ Set.Icc (0 : ℝ) 1)
    (j : ℕ) : HasSubgaussianMGF (fun ω ↦ X j ω - ∫ w, X j w ∂μ) (1 / 4) μ := by
  have h := hasSubgaussianMGF_of_mem_Icc (hX j) (hBound j)
  norm_num at h ⊢
  exact h

theorem independent_centered_sum {X : ℕ → Ω → ℝ}
    (hX : ∀ j, AEMeasurable (X j) μ)
    (hBound : ∀ j, ∀ᵐ ω ∂μ, X j ω ∈ Set.Icc (0 : ℝ) 1)
    (hIndep : iIndepFun X μ) (n : ℕ) :
    HasSubgaussianMGF
      (fun ω ↦ ∑ j ∈ range n, (X j ω - ∫ w, X j w ∂μ)) ((n : ℝ≥0) / 4) μ := by
  have hInd : iIndepFun (fun j ω ↦ X j ω - ∫ w, X j w ∂μ) μ :=
    hIndep.comp (fun j x ↦ x - ∫ w, X j w ∂μ) (fun _ ↦ measurable_id.sub_const _)
  have h := HasSubgaussianMGF.sum_of_iIndepFun hInd
    (s := range n) (c := fun _ ↦ (1 / 4 : ℝ≥0))
    (fun j _ ↦ bounded_centered_subgaussian hX hBound j)
  simpa [nsmul_eq_mul, div_eq_mul_inv] using h

/-- A fixed-mean bounded independent observation stream supplies both measurable
residual sums and the MGF assumption used by the expected-regret theorem. -/
theorem bounded_observation_stream {X : ℕ → Ω → ℝ} {mean : ℝ}
    (hX : ∀ j, Measurable (X j))
    (hBound : ∀ j, ∀ᵐ ω ∂μ, X j ω ∈ Set.Icc (0 : ℝ) 1)
    (hIndep : iIndepFun X μ) (hMean : ∀ j, (∫ ω, X j ω ∂μ) = mean)
    (n : ℕ) :
    Measurable (fun ω ↦ ∑ j ∈ range n, (X j ω - mean)) ∧
      HasSubgaussianMGF (fun ω ↦ ∑ j ∈ range n, (X j ω - mean))
        ((n : ℝ≥0) / 4) μ := by
  constructor
  · exact Finset.measurable_sum _ (fun j _ ↦ (hX j).sub measurable_const)
  · simpa only [hMean] using
      independent_centered_sum (fun j ↦ (hX j).aemeasurable) hBound hIndep n

omit [MeasurableSpace Ω] in
/-- The residual model is exactly the ordinary sample average, not a separate
assumed confidence estimator. -/
theorem sample_average_eq_mean_add_residual (X : ℕ → Ω → ℝ) (mean : ℝ)
    {n : ℕ} (hn : 0 < n) (ω : Ω) :
    (∑ j ∈ range n, X j ω) / (n : ℝ) =
      mean + (∑ j ∈ range n, (X j ω - mean)) / (n : ℝ) := by
  have hne : (n : ℝ) ≠ 0 := by exact_mod_cast (Nat.ne_of_gt hn)
  simp only [sum_sub_distrib, sum_const, card_range, nsmul_eq_mul]
  field_simp
  ring

/-- A two-sided average-error bound, including all probability steps in Lean. -/
theorem mean_error_tail {S : Ω → ℝ} {n : ℕ} (hn : 0 < n)
    (hS : HasSubgaussianMGF S ((n : ℝ≥0) / 4) μ)
    {L : ℝ} (hL : 0 ≤ L) :
    μ.real {ω | Real.sqrt (2 * L / n) ≤ |S ω / n|} ≤ 2 * exp (-4 * L) := by
  have hnR : (0 : ℝ) < n := by exact_mod_cast hn
  let r := Real.sqrt (2 * L / n)
  have hr : 0 ≤ r := sqrt_nonneg _
  have hrsq : r ^ 2 = 2 * L / n := Real.sq_sqrt (by positivity)
  have hset : {ω | r ≤ |S ω / n|} = {ω | (n : ℝ) * r ≤ |S ω|} := by
    ext ω
    simp only [Set.mem_setOf_eq]
    rw [abs_div, abs_of_pos hnR, le_div_iff₀ hnR]
    simp [mul_comm]
  change μ.real {ω | r ≤ |S ω / n|} ≤ _
  rw [hset]
  have ht := subgaussian_abs_tail hS (mul_nonneg (le_of_lt hnR) hr)
  have he : -((n : ℝ) * r) ^ 2 / (2 * (((n : ℝ≥0) / 4 : ℝ≥0) : ℝ)) = -4 * L := by
    push_cast
    rw [mul_pow, hrsq]
    field_simp
  rwa [he] at ht

theorem mean_error_tail_at_time {S : Ω → ℝ} {n : ℕ} (hn : 0 < n)
    (hS : HasSubgaussianMGF S ((n : ℝ≥0) / 4) μ) (t : ℕ) :
    μ.real {ω | Real.sqrt (2 * log (t + 1 : ℕ) / n) ≤ |S ω / n|} ≤
      2 / (t + 1 : ℝ) ^ 4 := by
  have ht : (0 : ℝ) < t + 1 := by positivity
  have hL : 0 ≤ log (t + 1 : ℕ) := log_nonneg (by exact_mod_cast Nat.le_add_left 1 t)
  have h := mean_error_tail hn hS hL
  have he : exp (-4 * log (t + 1 : ℕ)) = 1 / (t + 1 : ℝ) ^ 4 := by
    rw [show -4 * log (t + 1 : ℕ) = -(4 * log (t + 1 : ℕ)) by ring,
      exp_neg, show (4 : ℝ) = ((4 : ℕ) : ℝ) from rfl, exp_nat_mul]
    simp [Nat.cast_add, Nat.cast_one, exp_log ht]
  rw [he] at h
  simpa [div_eq_mul_inv] using h

/-- Union over every possible adaptive observation count; counts need not be independent. -/
def badAt {Arm : Type*} (arms : Finset Arm) (S : Arm → ℕ → Ω → ℝ) (t : ℕ) : Set Ω :=
  ⋃ a ∈ arms, ⋃ n ∈ range (t + 1),
    {ω | 0 < n ∧ sqrt (2 * log (t + 1 : ℕ) / n) ≤ |S a n ω / n|}

theorem badAt_probability {Arm : Type*} (arms : Finset Arm) (S : Arm → ℕ → Ω → ℝ)
    (hS : ∀ a ∈ arms, ∀ n, 0 < n → HasSubgaussianMGF (S a n) ((n : ℝ≥0) / 4) μ)
    (t : ℕ) : μ.real (badAt arms S t) ≤
      (arms.card : ℝ) * ((t + 1 : ℝ) * (2 / (t + 1 : ℝ) ^ 4)) := by
  classical
  unfold badAt
  apply (measureReal_biUnion_finset_le arms _).trans
  calc
    _ ≤ ∑ a ∈ arms, ∑ n ∈ range (t + 1), (2 / (t + 1 : ℝ) ^ 4) := by
      apply Finset.sum_le_sum
      intro a ha
      apply (measureReal_biUnion_finset_le (range (t + 1)) _).trans
      apply Finset.sum_le_sum
      intro n _
      by_cases hn : 0 < n
      · exact (measureReal_mono (fun ω h ↦ h.2)).trans
          (mean_error_tail_at_time hn (hS a ha n hn) t)
      · simp only [hn, false_and, Set.setOf_false, measureReal_empty]
        positivity
    _ = _ := by simp [nsmul_eq_mul, Nat.cast_add, Nat.cast_one]

theorem reciprocal_telescope (T : ℕ) :
    (∑ t ∈ range T, ((1 : ℝ) / (t + 1) - 1 / (t + 2))) = 1 - 1 / (T + 1) := by
  induction T with
  | zero => norm_num
  | succ T ih => rw [sum_range_succ, ih]; push_cast; ring

theorem badAt_probability_telescope {Arm : Type*} (arms : Finset Arm)
    (S : Arm → ℕ → Ω → ℝ)
    (hS : ∀ a ∈ arms, ∀ n, 0 < n → HasSubgaussianMGF (S a n) ((n : ℝ≥0) / 4) μ)
    (t : ℕ) : μ.real (badAt arms S t) ≤
      4 * (arms.card : ℝ) * (1 / (t + 1 : ℝ) - 1 / (t + 2 : ℝ)) := by
  have hu : (0 : ℝ) < t + 1 := by positivity
  have hv : (0 : ℝ) < t + 2 := by positivity
  have hd : (1 : ℝ) / (t + 1) - 1 / (t + 2) = 1 / ((t + 1) * (t + 2)) := by
    field_simp
    ring
  have hf : (t + 1 : ℝ) * (2 / (t + 1 : ℝ) ^ 4) ≤
      4 / ((t + 1 : ℝ) * (t + 2 : ℝ)) := by
    rw [← mul_div_assoc]
    apply (div_le_div_iff₀ (pow_pos hu _) (mul_pos hu hv)).mpr
    have hx : (t + 2 : ℝ) ≤ 2 * (t + 1 : ℝ) ^ 2 := by
      have := Nat.cast_nonneg (α := ℝ) t
      nlinarith
    have hm := mul_le_mul_of_nonneg_left hx (by positivity : 0 ≤ 2 * (t + 1 : ℝ) ^ 2)
    nlinarith
  calc
    _ ≤ (arms.card : ℝ) * ((t + 1 : ℝ) * (2 / (t + 1 : ℝ) ^ 4)) :=
      badAt_probability arms S hS t
    _ ≤ (arms.card : ℝ) * (4 / ((t + 1 : ℝ) * (t + 2 : ℝ))) :=
      mul_le_mul_of_nonneg_left hf (Nat.cast_nonneg _)
    _ = _ := by rw [hd]; ring

theorem total_failure_probability {Arm : Type*} (arms : Finset Arm)
    (S : Arm → ℕ → Ω → ℝ)
    (hS : ∀ a ∈ arms, ∀ n, 0 < n → HasSubgaussianMGF (S a n) ((n : ℝ≥0) / 4) μ)
    (T : ℕ) : (∑ t ∈ range T, μ.real (badAt arms S t)) ≤ 4 * arms.card := by
  calc
    _ ≤ ∑ t ∈ range T, 4 * (arms.card : ℝ) *
        (1 / (t + 1 : ℝ) - 1 / (t + 2 : ℝ)) :=
      Finset.sum_le_sum (fun t _ ↦ badAt_probability_telescope arms S hS t)
    _ = 4 * (arms.card : ℝ) * (1 - 1 / (T + 1 : ℝ)) := by
      rw [← Finset.mul_sum, reciprocal_telescope]
    _ ≤ 4 * arms.card := by
      have hp : (0 : ℝ) ≤ 1 / (T + 1 : ℝ) := by positivity
      nlinarith [Nat.cast_nonneg (α := ℝ) arms.card]

theorem measurableSet_badAt {Arm : Type*} (arms : Finset Arm)
    (S : Arm → ℕ → Ω → ℝ) (hS : ∀ a n, Measurable (S a n)) (t : ℕ) :
    MeasurableSet (badAt arms S t) := by
  classical
  unfold badAt
  apply MeasurableSet.biUnion arms.countable_toSet
  intro a _
  apply MeasurableSet.biUnion (range (t + 1)).countable_toSet
  intro n _
  by_cases hn : 0 < n
  · simp only [hn, true_and]
    exact measurableSet_le measurable_const ((hS a n).div_const _).abs
  · simp [hn]

omit [MeasurableSpace Ω] in
theorem not_badAt_error {Arm : Type*} (arms : Finset Arm) (S : Arm → ℕ → Ω → ℝ)
    {t n : ℕ} {a : Arm} {ω : Ω} (ha : a ∈ arms) (hn : 0 < n) (hnt : n ≤ t)
    (hgood : ω ∉ badAt arms S t) :
    |S a n ω / n| ≤ sqrt (2 * log (t + 1 : ℕ) / n) := by
  by_contra h
  apply hgood
  simp only [badAt, Set.mem_iUnion, Set.mem_setOf_eq]
  exact ⟨a, ha, n, Finset.mem_range.mpr (by omega), hn, le_of_lt (lt_of_not_ge h)⟩

def badCount {Arm : Type*} (arms : Finset Arm) (S : Arm → ℕ → Ω → ℝ)
    (T : ℕ) (ω : Ω) : ℝ := by
  classical
  exact ∑ t ∈ range T, if ω ∈ badAt arms S t then 1 else 0

theorem badCount_integrable {Arm : Type*} (arms : Finset Arm) (S : Arm → ℕ → Ω → ℝ)
    (hS : ∀ a n, Measurable (S a n)) (T : ℕ) : Integrable (badCount arms S T) μ := by
  classical
  unfold badCount
  apply integrable_finset_sum
  intro t _
  exact (integrable_const (1 : ℝ) (μ := μ)).indicator (measurableSet_badAt arms S hS t)

theorem expected_badCount {Arm : Type*} (arms : Finset Arm) (S : Arm → ℕ → Ω → ℝ)
    (hMeas : ∀ a n, Measurable (S a n))
    (hS : ∀ a ∈ arms, ∀ n, 0 < n → HasSubgaussianMGF (S a n) ((n : ℝ≥0) / 4) μ)
    (T : ℕ) : (∫ ω, badCount arms S T ω ∂μ) ≤ 4 * arms.card := by
  classical
  have hi (t : ℕ) : Integrable (fun ω ↦ if ω ∈ badAt arms S t then (1 : ℝ) else 0) μ :=
    (integrable_const (1 : ℝ) (μ := μ)).indicator (measurableSet_badAt arms S hMeas t)
  unfold badCount
  rw [integral_finset_sum _ (fun t _ ↦ hi t)]
  have he (t : ℕ) : (∫ ω, (if ω ∈ badAt arms S t then (1 : ℝ) else 0) ∂μ) =
      μ.real (badAt arms S t) := integral_indicator_one (measurableSet_badAt arms S hMeas t)
  simp_rw [he]
  exact total_failure_probability arms S hS T

end AgentUCTPaper
