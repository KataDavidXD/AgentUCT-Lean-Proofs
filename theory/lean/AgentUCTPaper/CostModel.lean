import AgentUCT

/-! # Reference-law error and deepest-checkpoint suffix costs

Cost forecasts can err through both a per-completion bill and the probability law
used to average those bills. The first theorem separates these errors. The suffix
results describe one fixed qid and one fixed completion path; summing over a panel
preserves the inequalities. No probabilistic confidence interval is postulated.
-/

noncomputable section

open Finset

namespace AgentUCTPaper

/-- Reference-law cost error splits into bill prediction error and law mismatch.
The completion bills may include qid-prefix cold work and future overhead. The bound
does not assume independent resource demands. Normalization is unnecessary for the
inequality; if both laws are probabilities, their L1 distance is twice total variation. -/
theorem reference_law_cost_error {Completion : Type*} (completions : Finset Completion)
    (predictedLaw actualLaw predictedBill actualBill : Completion → ℝ) (billBound : ℝ)
    (hpredicted : ∀ x ∈ completions, 0 ≤ predictedLaw x)
    (hbounded : ∀ x ∈ completions, |actualBill x| ≤ billBound) :
    |(∑ x ∈ completions, predictedLaw x * predictedBill x) -
        ∑ x ∈ completions, actualLaw x * actualBill x| ≤
      (∑ x ∈ completions, predictedLaw x * |predictedBill x - actualBill x|) +
        billBound * ∑ x ∈ completions, |predictedLaw x - actualLaw x| := by
  have hpoint : ∀ x ∈ completions,
      |predictedLaw x * predictedBill x - actualLaw x * actualBill x| ≤
        predictedLaw x * |predictedBill x - actualBill x| +
          billBound * |predictedLaw x - actualLaw x| := by
    intro x hx
    have hsplit : predictedLaw x * predictedBill x - actualLaw x * actualBill x =
        predictedLaw x * (predictedBill x - actualBill x) +
          (predictedLaw x - actualLaw x) * actualBill x := by ring
    rw [hsplit]
    calc
      |predictedLaw x * (predictedBill x - actualBill x) +
          (predictedLaw x - actualLaw x) * actualBill x| ≤
          |predictedLaw x * (predictedBill x - actualBill x)| +
            |(predictedLaw x - actualLaw x) * actualBill x| := abs_add_le _ _
      _ = predictedLaw x * |predictedBill x - actualBill x| +
          |predictedLaw x - actualLaw x| * |actualBill x| := by
        rw [abs_mul, abs_mul, abs_of_nonneg (hpredicted x hx)]
      _ ≤ predictedLaw x * |predictedBill x - actualBill x| +
          billBound * |predictedLaw x - actualLaw x| := by
        have hmul := mul_le_mul_of_nonneg_left (hbounded x hx)
          (abs_nonneg (predictedLaw x - actualLaw x))
        nlinarith
  rw [← sum_sub_distrib]
  calc
    |∑ x ∈ completions, (predictedLaw x * predictedBill x - actualLaw x * actualBill x)| ≤
        ∑ x ∈ completions, |predictedLaw x * predictedBill x - actualLaw x * actualBill x| :=
      abs_sum_le_sum_abs _ _
    _ ≤ ∑ x ∈ completions,
        (predictedLaw x * |predictedBill x - actualBill x| +
          billBound * |predictedLaw x - actualLaw x|) := sum_le_sum hpoint
    _ = (∑ x ∈ completions, predictedLaw x * |predictedBill x - actualBill x|) +
        billBound * ∑ x ∈ completions, |predictedLaw x - actualLaw x| := by
      rw [sum_add_distrib, mul_sum]

/-- Certified bill radii can be substituted directly into the reference-law bound.
Such radii may be obtained from `total_search_cost_forecast_error`; their statistical
coverage, if desired, must be proved separately. -/
theorem reference_law_cost_error_of_radius {Completion : Type*}
    (completions : Finset Completion)
    (predictedLaw actualLaw predictedBill actualBill billRadius : Completion → ℝ)
    (billBound : ℝ)
    (hpredicted : ∀ x ∈ completions, 0 ≤ predictedLaw x)
    (hbounded : ∀ x ∈ completions, |actualBill x| ≤ billBound)
    (hradius : ∀ x ∈ completions, |predictedBill x - actualBill x| ≤ billRadius x) :
    |(∑ x ∈ completions, predictedLaw x * predictedBill x) -
        ∑ x ∈ completions, actualLaw x * actualBill x| ≤
      (∑ x ∈ completions, predictedLaw x * billRadius x) +
        billBound * ∑ x ∈ completions, |predictedLaw x - actualLaw x| := by
  refine (reference_law_cost_error completions predictedLaw actualLaw predictedBill
    actualBill billBound hpredicted hbounded).trans ?_
  apply add_le_add_right
  exact sum_le_sum fun x hx =>
    mul_le_mul_of_nonneg_left (hradius x hx) (hpredicted x hx)

/-- For a fixed qid and path of length `depth`, only stages strictly after the deepest
restorable checkpoint need execution. Stage indices are one-based. -/
def checkpointSuffixBill (stageCost : ℕ → ℝ) (checkpoint depth : ℕ) : ℝ :=
  ∑ stage ∈ Ioc checkpoint depth, stageCost stage

/-- Restoring a deeper checkpoint cannot increase the required suffix bill when stage
costs are nonnegative. It need not imply that all ancestors are stored as objects. -/
theorem checkpointSuffixBill_antitone (stageCost : ℕ → ℝ)
    (hnonneg : ∀ stage, 0 ≤ stageCost stage) {oldCheckpoint newCheckpoint depth : ℕ}
    (hdeeper : oldCheckpoint ≤ newCheckpoint) :
    checkpointSuffixBill stageCost newCheckpoint depth ≤
      checkpointSuffixBill stageCost oldCheckpoint depth := by
  exact sum_le_sum_of_subset_of_nonneg (Ioc_subset_Ioc_left hdeeper)
    (fun stage _ _ => hnonneg stage)

/-- A checkpoint at the terminal stage eliminates the execution suffix, while any
future overhead remains separately chargeable. -/
theorem terminal_checkpoint_zero (stageCost : ℕ → ℝ) (depth : ℕ) :
    checkpointSuffixBill stageCost depth depth = 0 := by
  simp [checkpointSuffixBill]

end AgentUCTPaper
