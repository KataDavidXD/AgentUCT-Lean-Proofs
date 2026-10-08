import AgentUCTPaper.TreeGraphInformation

/-! # Completion-cost decisions and finite-budget coverage

The index results compare candidates at the same observed state. The coverage
result uses separate realized cost sequences, so it does not identify two
policies' caches. No reward improvement follows from evaluation count alone.
-/

set_option autoImplicit false
noncomputable section

namespace AgentUCTPaper

/-- The quality advantage needed to justify a more expensive completion. -/
theorem completion_index_threshold (ua ub ca cb gamma : ℝ) :
    ua - gamma * ca ≤ ub - gamma * cb ↔ ua - ub ≤ gamma * (ca - cb) := by
  constructor <;> intro h <;> nlinarith

/-- At equal optimistic quality, the completion-cost index orders by cost. -/
theorem equal_priority_minimizes_completion (u ca cb gamma : ℝ) (hg : 0 < gamma) :
    u - gamma * ca ≤ u - gamma * cb ↔ cb ≤ ca := by
  constructor <;> intro h <;> nlinarith

/-- Forecast error controls the loss in the true same-state completion index. -/
theorem completion_index_error (ua ub ca cb ea eb ra rb gamma : ℝ)
    (hg : 0 ≤ gamma) (ha : |ea - ca| ≤ ra) (hb : |eb - cb| ≤ rb)
    (hChoose : ub - gamma * eb ≤ ua - gamma * ea) :
    (ub - gamma * cb) - (ua - gamma * ca) ≤ gamma * (ra + rb) := by
  obtain ⟨hal, har⟩ := abs_le.mp ha
  obtain ⟨hbl, hbr⟩ := abs_le.mp hb
  have h1 := mul_le_mul_of_nonneg_left (show ca - ea ≤ ra by linarith) hg
  have h2 := mul_le_mul_of_nonneg_left hbr hg
  nlinarith

/-- Error accumulation is explicit; sublinear loss requires control of this sum. -/
theorem completion_index_cumulative_error (ua ub ca cb ea eb ra rb : ℕ → ℝ)
    (gamma : ℝ) (hg : 0 ≤ gamma) (T : ℕ)
    (ha : ∀ t ∈ Finset.range T, |ea t - ca t| ≤ ra t)
    (hb : ∀ t ∈ Finset.range T, |eb t - cb t| ≤ rb t)
    (hChoose : ∀ t ∈ Finset.range T, ub t - gamma * eb t ≤ ua t - gamma * ea t) :
    (∑ t ∈ Finset.range T, ((ub t - gamma * cb t) - (ua t - gamma * ca t))) ≤
      gamma * (∑ t ∈ Finset.range T, (ra t + rb t)) := by
  rw [Finset.mul_sum]
  apply Finset.sum_le_sum
  intro t ht
  exact completion_index_error _ _ _ _ _ _ _ _ _ hg (ha t ht) (hb t ht) (hChoose t ht)

/-- A prefix of a nonnegative cost trace cannot exceed the complete trace. -/
theorem prefix_spend_le (cost : ℕ → ℝ) (hc : ∀ t, 0 ≤ cost t)
    (k m : ℕ) (hkm : k ≤ m) :
    ∑ t ∈ Finset.range k, cost t ≤ ∑ t ∈ Finset.range m, cost t := by
  exact Finset.sum_le_sum_of_subset_of_nonneg (Finset.range_mono hkm)
    (fun t _ _ ↦ hc t)

/-- Own-trajectory cost bounds imply a strict finite-budget coverage separation.
The first conjunct covers every retrospectively affordable completed prefix.
These are realized bills; the theorem does not prescribe pre-call admission. -/
theorem own_cache_budget_coverage (cheap expensive : ℕ → ℝ)
    (hc : ∀ t, 0 ≤ cheap t) (low high B : ℝ) (m k : ℕ)
    (hLow : ∀ t ∈ Finset.range m, cheap t ≤ low)
    (hHigh : ∀ t ∈ Finset.range k, high ≤ expensive t)
    (hFit : (m : ℝ) * low ≤ B) (hMiss : B < (k : ℝ) * high) :
    (∀ j ≤ m, ∑ t ∈ Finset.range j, cheap t ≤ B) ∧
      B < ∑ t ∈ Finset.range k, expensive t := by
  have hl : (∑ t ∈ Finset.range m, cheap t) ≤ (m : ℝ) * low := by
    calc
      _ ≤ ∑ _t ∈ Finset.range m, low := Finset.sum_le_sum hLow
      _ = _ := by simp
  have hh : (k : ℝ) * high ≤ ∑ t ∈ Finset.range k, expensive t := by
    calc
      _ = ∑ _t ∈ Finset.range k, high := by simp
      _ ≤ _ := Finset.sum_le_sum hHigh
  exact ⟨fun j hj ↦ (prefix_spend_le cheap hc j m hj).trans (hl.trans hFit),
    hMiss.trans_le hh⟩

/-- A cached next edge has no information about a still-cold completion suffix. -/
theorem next_edge_ranking_reversal (ua ub edge taila tailb gamma : ℝ)
    (hQuality : ua < ub) (hTail : ub - ua < gamma * (tailb - taila)) :
    ua - gamma * edge < ub - gamma * edge ∧
      ub - gamma * (edge + tailb) < ua - gamma * (edge + taila) := by
  constructor <;> nlinarith

/-- Omitting a nonnegative suffix loses its entire bill, regardless of edge cost. -/
theorem next_edge_omitted_error (edge tail : ℝ) (ht : 0 ≤ tail) :
    |edge - (edge + tail)| = tail := by
  rw [show edge - (edge + tail) = -tail by ring, abs_neg, abs_of_nonneg ht]

/-- Scale the graph witness: an aggregate-blind allocation loses H/2 somewhere. -/
theorem GraphWitness.scaled_randomized_excess (p H : ℝ) :
    H / 2 ≤ max (H * (1 - p)) (H * p) := by
  have h1 := le_max_left (H * (1 - p)) (H * p)
  have h2 := le_max_right (H * (1 - p)) (H * p)
  nlinarith

end AgentUCTPaper
