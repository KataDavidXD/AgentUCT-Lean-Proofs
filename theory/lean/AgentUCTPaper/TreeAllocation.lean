import AgentUCTPaper.TreeReturns

/-! # Progress of the actual cost-perturbed UCT index

Q is allowed to be any adaptive number in [0,1]. Costs are arbitrary bounded
nonnegative penalties. This module uses no confidence or drift hypothesis.
-/

set_option autoImplicit false

noncomputable section

namespace AgentUCTPaper

open Finset

def treeBonus (c : ℝ) (parentCount childCount : ℕ) : ℝ :=
  c * Real.sqrt (Real.log (parentCount + 1 : ℕ) / (childCount : ℝ))

def treeIndex (q c penalty : ℝ) (parentCount childCount : ℕ) : ℝ :=
  q + treeBonus c parentCount childCount - penalty

theorem treeBonus_nonnegative {c : ℝ} (hc : 0 ≤ c) (parentCount childCount : ℕ) :
    0 ≤ treeBonus c parentCount childCount := mul_nonneg hc (Real.sqrt_nonneg _)

theorem treeBonus_square (c : ℝ) (parentCount childCount : ℕ) (hCount : 0 < childCount) :
    treeBonus c parentCount childCount ^ 2 * (childCount : ℝ) =
      c ^ 2 * Real.log (parentCount + 1 : ℕ) := by
  have hLog : 0 ≤ Real.log (parentCount + 1 : ℕ) :=
    Real.log_nonneg (by exact_mod_cast Nat.le_add_left 1 parentCount)
  have hN : (0 : ℝ) < childCount := Nat.cast_pos.mpr hCount
  unfold treeBonus
  rw [mul_pow, Real.sq_sqrt (div_nonneg hLog hN.le)]
  field_simp

/-- An under-visited competitor forces the selected action to have a small prior count. -/
theorem selected_count_under_pressure {qBest qChosen c H penaltyBest penaltyChosen : ℝ}
    {parentCount bestCount chosenCount : ℕ} (hc : 0 ≤ c) (hH : 0 ≤ H)
    (hBestCount : 0 < bestCount) (hChosenCount : 0 < chosenCount)
    (hBestQ : 0 ≤ qBest) (hChosenQ : qChosen ≤ 1)
    (hBestPenalty : penaltyBest ≤ H) (hChosenPenalty : 0 ≤ penaltyChosen)
    (hPressure : (H + 2) ^ 2 * (bestCount : ℝ) < c ^ 2 * Real.log (parentCount + 1 : ℕ))
    (hSelect : treeIndex qBest c penaltyBest parentCount bestCount ≤
      treeIndex qChosen c penaltyChosen parentCount chosenCount) :
    (chosenCount : ℝ) < c ^ 2 * Real.log (parentCount + 1 : ℕ) := by
  -- Q2.2：低次数child的bonus>H+2；结合Q≥0、罚项≤H得到index>2。
  have hBestR := treeBonus_nonnegative hc parentCount bestCount
  have hChosenR := treeBonus_nonnegative hc parentCount chosenCount
  have hBestSq := treeBonus_square c parentCount bestCount hBestCount
  have hChosenSq := treeBonus_square c parentCount chosenCount hChosenCount
  have hBig : H + 2 < treeBonus c parentCount bestCount := by
    by_contra h
    have hu : treeBonus c parentCount bestCount ≤ H + 2 := le_of_not_gt h
    have hs : treeBonus c parentCount bestCount ^ 2 ≤ (H + 2) ^ 2 := by nlinarith
    have hm := mul_le_mul_of_nonneg_right hs (Nat.cast_nonneg bestCount : (0 : ℝ) ≤ _)
    linarith
  have hChosenBig : 1 < treeBonus c parentCount chosenCount := by
    -- Q2.3：被选child的Q≤1、罚项≥0，要达到该index，其bonus必须>1。
    unfold treeIndex at hSelect
    linarith
  have hn : (0 : ℝ) < chosenCount := Nat.cast_pos.mpr hChosenCount
  have hs : 1 < treeBonus c parentCount chosenCount ^ 2 := by nlinarith
  have hm := mul_lt_mul_of_pos_right hs hn
  nlinarith

section Counts

variable {Arm : Type*} [DecidableEq Arm]

theorem pullCount_monotone (action : ℕ → Arm) (arm : Arm) {s t : ℕ} (hst : s ≤ t) :
    AgentUCT.pullCount action arm s ≤ AgentUCT.pullCount action arm t := by
  apply Finset.card_le_card
  intro x hx
  simp only [mem_filter, mem_range] at hx ⊢
  exact ⟨lt_of_lt_of_le hx.1 hst, hx.2⟩

theorem initialized_after_distinct_actions [Fintype Arm] (action : ℕ → Arm)
    (hDistinct : Set.InjOn action (Finset.range (Fintype.card Arm) : Set ℕ)) :
    ∀ arm, 0 < AgentUCT.pullCount action arm (Fintype.card Arm) := by
  have hImage : (Finset.range (Fintype.card Arm)).image action = Finset.univ := by
    apply Finset.eq_univ_of_card
    rw [Finset.card_image_of_injOn hDistinct, Finset.card_range]
  intro arm
  have hm : arm ∈ (Finset.range (Fintype.card Arm)).image action := by
    rw [hImage]
    exact Finset.mem_univ _
  obtain ⟨t, ht, ha⟩ := Finset.mem_image.mp hm
  exact Finset.card_pos.mpr ⟨t, Finset.mem_filter.mpr ⟨ht, ha⟩⟩

/-- Expanding an unvisited child whenever one remains completes initialization after K visits. -/
theorem initialized_after_unvisited_first [Fintype Arm] (action : ℕ → Arm)
    (hUnvisited : ∀ t < Fintype.card Arm, ∀ arm,
      AgentUCT.pullCount action arm t = 0 → AgentUCT.pullCount action (action t) t = 0) :
    ∀ arm, 0 < AgentUCT.pullCount action arm (Fintype.card Arm) := by
  intro arm
  by_contra h
  have hZero : AgentUCT.pullCount action arm (Fintype.card Arm) = 0 := by omega
  have hChosenZero : ∀ t < Fintype.card Arm, AgentUCT.pullCount action (action t) t = 0 := by
    intro t ht
    apply hUnvisited t ht arm
    have hm := pullCount_monotone action arm ht.le
    omega
  have hDistinct : Set.InjOn action (Finset.range (Fintype.card Arm) : Set ℕ) := by
    intro s hs t ht heq
    have hsK := Finset.mem_range.mp hs
    have htK := Finset.mem_range.mp ht
    rcases lt_trichotomy s t with hst | hst | hts
    · have hCount := AgentUCT.pullCount_strict hst (show action s = action t from heq)
      have hz := hChosenZero t htK
      omega
    · exact hst
    · have hCount := AgentUCT.pullCount_strict hts (show action t = action s from heq.symm)
      have hz := hChosenZero s hsK
      omega
  have hp := initialized_after_distinct_actions action hDistinct arm
  omega

/-- A finite collection of low-prior-count selections has a finite cardinality. -/
theorem small_count_window_bound [Fintype Arm] (action : ℕ → Arm) (times : Finset ℕ)
    {cap : ℝ} (hCap : 0 ≤ cap)
    (hCount : ∀ t ∈ times, (AgentUCT.pullCount action (action t) t : ℝ) ≤ cap) :
    (times.card : ℝ) ≤ (Fintype.card Arm : ℝ) * (cap + 1) := by
  have hPerArm (arm : Arm) : (∑ t ∈ times.filter (fun t ↦ action t = arm), (1 : ℝ)) ≤ cap + 1 := by
    have h := AgentUCT.selected_count_bound action arm
      (times.filter (fun t ↦ action t = arm)) hCap
      (fun t ht ↦ (mem_filter.mp ht).2) (by
        intro t ht
        obtain ⟨ht, ha⟩ := mem_filter.mp ht
        simpa [ha] using hCount t ht)
    simpa using h
  have hPartition :
      (∑ arm : Arm, ∑ t ∈ times.filter (fun t ↦ action t = arm), (1 : ℝ)) = times.card := by
    simp_rw [sum_filter]
    rw [sum_comm]
    simp
  rw [← hPartition]
  calc
    _ ≤ ∑ _arm : Arm, (cap + 1) := sum_le_sum (fun arm _ ↦ hPerArm arm)
    _ = _ := by simp [mul_add]

/-- Explicit finite-window exploration, valid for arbitrary bounded adaptive backup means. -/
theorem finite_window_explores [Fintype Arm] (action : ℕ → Arm)
    (q penalty : ℕ → Arm → ℝ) (c H : ℝ) (offset L U m : ℕ) (arm : Arm)
    (hc : 0 ≤ c) (hH : 0 ≤ H)
    (hInitialized : ∀ a, 0 < AgentUCT.pullCount action a L)
    (hQ : ∀ t ∈ Ico L U, ∀ a, 0 ≤ q t a ∧ q t a ≤ 1)
    (hPenalty : ∀ t ∈ Ico L U, ∀ a, 0 ≤ penalty t a ∧ penalty t a ≤ H)
    (hSelect : ∀ t ∈ Ico L U, ∀ a,
      treeIndex (q t a) c (penalty t a) (t + offset) (AgentUCT.pullCount action a t) ≤
        treeIndex (q t (action t)) c (penalty t (action t)) (t + offset)
          (AgentUCT.pullCount action (action t) t))
    (hPressure : (H + 2) ^ 2 * (m : ℝ) < c ^ 2 * Real.log (L + offset + 1 : ℕ))
    (hWindow : (Fintype.card Arm : ℝ) * (c ^ 2 * Real.log (U + offset + 1 : ℕ) + 1) <
      (U - L : ℕ)) :
    m < AgentUCT.pullCount action arm U := by
  -- Q2.4：反设目标child到U仍≤m，则整个窗口内所有被选child次数受log界。
  by_contra h
  have hEnd : AgentUCT.pullCount action arm U ≤ m := Nat.le_of_not_gt h
  have hLogUpper : 0 ≤ Real.log (U + offset + 1 : ℕ) :=
    Real.log_nonneg (by exact_mod_cast Nat.le_add_left 1 (U + offset))
  have hBound : ∀ t ∈ Ico L U,
      (AgentUCT.pullCount action (action t) t : ℝ) ≤
        c ^ 2 * Real.log (U + offset + 1 : ℕ) := by
    intro t ht
    obtain ⟨hLt, htU⟩ := mem_Ico.mp ht
    have hBestN : 0 < AgentUCT.pullCount action arm t :=
      lt_of_lt_of_le (hInitialized arm) (pullCount_monotone action arm hLt)
    have hChosenN : 0 < AgentUCT.pullCount action (action t) t :=
      lt_of_lt_of_le (hInitialized (action t)) (pullCount_monotone action (action t) hLt)
    have hCountM : (AgentUCT.pullCount action arm t : ℝ) ≤ m := by
      exact_mod_cast (pullCount_monotone action arm htU.le).trans hEnd
    have hLogLo : Real.log (L + offset + 1 : ℕ) ≤ Real.log (t + offset + 1 : ℕ) :=
      Real.log_le_log (by positivity)
        (by exact_mod_cast (show L + offset + 1 ≤ t + offset + 1 by omega))
    have hLogHi : Real.log (t + offset + 1 : ℕ) ≤ Real.log (U + offset + 1 : ℕ) :=
      Real.log_le_log (by positivity)
        (by exact_mod_cast (show t + offset + 1 ≤ U + offset + 1 by omega))
    have hp : (H + 2) ^ 2 * (AgentUCT.pullCount action arm t : ℝ) <
        c ^ 2 * Real.log (t + offset + 1 : ℕ) :=
      lt_of_le_of_lt (mul_le_mul_of_nonneg_left hCountM (sq_nonneg _))
        (lt_of_lt_of_le hPressure (mul_le_mul_of_nonneg_left hLogLo (sq_nonneg _)))
    exact (selected_count_under_pressure hc hH hBestN hChosenN
      (hQ t ht arm).1 (hQ t ht (action t)).2
      (hPenalty t ht arm).2 (hPenalty t ht (action t)).1 hp (hSelect t ht arm)).le.trans
        (mul_le_mul_of_nonneg_left hLogHi (sq_nonneg _))
  have hSize := small_count_window_bound action (Ico L U)
    (mul_nonneg (sq_nonneg _) hLogUpper) hBound
  -- Q2.5：按child汇总可选择次数，小于窗口长度U-L，得到矛盾。
  simp only [Nat.card_Ico] at hSize
  linarith

end Counts

end AgentUCTPaper
