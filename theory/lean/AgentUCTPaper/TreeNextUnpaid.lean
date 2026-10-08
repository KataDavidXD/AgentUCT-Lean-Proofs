import AgentUCTPaper.TreeFiniteBudget

/-! # First unpaid execution cost versus the immediate tree edge

An ordered execution demand skips cached resources and zero-priced routing
steps. This estimator charges the first remaining positive-price resource.
For a panel, apply it separately to each qid's path and sum, then average under
the declared continuation law. It is a truncation of the complete cold bill.
-/

set_option autoImplicit false
noncomputable section

namespace AgentUCTPaper

variable {Resource : Type*} [DecidableEq Resource]

/-- Price of the next positive-price resource that actually needs execution. -/
def nextUnpaidBill (cache : Finset Resource) (price : Resource → ℝ) : List Resource → ℝ
  | [] => 0
  | r :: rs => if r ∈ cache ∨ price r ≤ 0 then nextUnpaidBill cache price rs else price r

/-- Complete cold bill in execution order. -/
def orderedColdBill (cache : Finset Resource) (price : Resource → ℝ) : List Resource → ℝ
  | [] => 0
  | r :: rs => (if r ∈ cache then 0 else price r) + orderedColdBill cache price rs

theorem nextUnpaidBill_nonneg (cache : Finset Resource) (price : Resource → ℝ)
    (rs : List Resource) : 0 ≤ nextUnpaidBill cache price rs := by
  induction rs with
  | nil => simp [nextUnpaidBill]
  | cons r rs ih =>
    simp only [nextUnpaidBill]
    split_ifs with h
    · exact ih
    · exact le_of_lt (lt_of_not_ge (fun h0 ↦ h (Or.inr h0)))

theorem orderedColdBill_nonneg (cache : Finset Resource) (price : Resource → ℝ)
    (hp : ∀ r, 0 ≤ price r) (rs : List Resource) : 0 ≤ orderedColdBill cache price rs := by
  induction rs with
  | nil => simp [orderedColdBill]
  | cons r rs ih =>
    simp only [orderedColdBill]
    exact add_nonneg (by split_ifs <;> simp_all) ih

theorem nextUnpaidBill_le_complete (cache : Finset Resource) (price : Resource → ℝ)
    (hp : ∀ r, 0 ≤ price r) (rs : List Resource) :
    nextUnpaidBill cache price rs ≤ orderedColdBill cache price rs := by
  induction rs with
  | nil => simp [nextUnpaidBill, orderedColdBill]
  | cons r rs ih =>
    by_cases hc : r ∈ cache
    · simpa [nextUnpaidBill, orderedColdBill, hc] using ih
    · by_cases hz : price r ≤ 0
      · have he : price r = 0 := le_antisymm hz (hp r)
        simpa [nextUnpaidBill, orderedColdBill, hc, he] using ih
      · simp only [nextUnpaidBill, hc, hz, or_self, ↓reduceIte, orderedColdBill]
        exact le_add_of_nonneg_right (orderedColdBill_nonneg cache price hp rs)

theorem nextUnpaidBill_skip_cached (cache : Finset Resource) (price : Resource → ℝ)
    (r : Resource) (rs : List Resource) (hc : r ∈ cache) :
    nextUnpaidBill cache price (r :: rs) = nextUnpaidBill cache price rs := by
  simp [nextUnpaidBill, hc]

theorem nextUnpaidBill_zero_of_covered (cache : Finset Resource) (price : Resource → ℝ)
    (rs : List Resource) (h : ∀ r ∈ rs, r ∈ cache) : nextUnpaidBill cache price rs = 0 := by
  induction rs with
  | nil => simp [nextUnpaidBill]
  | cons r rs ih =>
    rw [nextUnpaidBill_skip_cached cache price r rs (h r (by simp))]
    exact ih (fun x hx ↦ h x (by simp [hx]))

/-- A saved immediate resource does not zero the next unpaid execution bill. -/
theorem nextUnpaidBill_cached_edge_counterexample :
    nextUnpaidBill ({0} : Finset ℕ) (fun _ ↦ (4 : ℝ)) [0, 1] = 4 := by
  norm_num [nextUnpaidBill]

end AgentUCTPaper
