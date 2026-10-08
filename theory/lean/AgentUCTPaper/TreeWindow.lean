import AgentUCTPaper.TreeAllocation

/-! # Explicit cost-dependent exploration windows

The exponential window is a worst-case progress bound, not a practical sample budget.
All dependence on the target count, penalty bound, branching factor and c is displayed.
-/

set_option autoImplicit false

noncomputable section

namespace AgentUCTPaper

open Finset

def explorationWindowStart (c H : ℝ) (K m : ℕ) : ℕ :=
  ⌈max (K + 1 : ℝ)
    (max (Real.exp (((H + 2) ^ 2 * (m : ℝ) + 1) / c ^ 2))
      ((8 * (K : ℝ) * max 1 (c ^ 2) + 2) ^ 2))⌉₊

theorem explorationWindow_bounds (c H : ℝ) (K m : ℕ) :
    (K + 1 : ℝ) ≤ explorationWindowStart c H K m ∧
      Real.exp (((H + 2) ^ 2 * (m : ℝ) + 1) / c ^ 2) ≤
        explorationWindowStart c H K m ∧
      (8 * (K : ℝ) * max 1 (c ^ 2) + 2) ^ 2 ≤ explorationWindowStart c H K m := by
  have h := Nat.le_ceil (max (K + 1 : ℝ)
    (max (Real.exp (((H + 2) ^ 2 * (m : ℝ) + 1) / c ^ 2))
      ((8 * (K : ℝ) * max 1 (c ^ 2) + 2) ^ 2)))
  exact ⟨(le_max_left _ _).trans h,
    (le_max_left _ _).trans ((le_max_right _ _).trans h),
    (le_max_right _ _).trans ((le_max_right _ _).trans h)⟩

theorem explorationWindow_pressure (c H : ℝ) (K m offset : ℕ) (hc : 0 < c) :
    (H + 2) ^ 2 * (m : ℝ) <
      c ^ 2 * Real.log (explorationWindowStart c H K m + offset + 1 : ℕ) := by
  let L := explorationWindowStart c H K m
  have hb := explorationWindow_bounds c H K m
  have hL : (0 : ℝ) < L := by
    dsimp [L]
    nlinarith [(Nat.cast_nonneg K : (0 : ℝ) ≤ K)]
  have he := Real.log_le_log (Real.exp_pos _) hb.2.1
  rw [Real.log_exp] at he
  have hm := (div_le_iff₀ (sq_pos_of_pos hc)).mp he
  have hlog : Real.log (L : ℝ) ≤ Real.log (L + offset + 1 : ℕ) :=
    Real.log_le_log hL (by exact_mod_cast (show L ≤ L + offset + 1 by omega))
  have hmul := mul_le_mul_of_nonneg_left hlog (sq_nonneg c)
  change (H + 2) ^ 2 * (m : ℝ) < c ^ 2 * Real.log (L + offset + 1 : ℕ)
  dsimp [L] at hmul
  nlinarith

theorem log_le_two_sqrt {x : ℝ} (hx : 0 < x) : Real.log x ≤ 2 * Real.sqrt x := by
  have h := Real.log_le_sub_one_of_pos (Real.sqrt_pos.mpr hx)
  rw [Real.log_sqrt hx.le] at h
  linarith

theorem explorationWindow_long_enough (c H : ℝ) (K m offset : ℕ) (hOffset : offset ≤ 1) :
    (K : ℝ) * (c ^ 2 * Real.log (2 * explorationWindowStart c H K m + offset + 1 : ℕ) + 1) <
      explorationWindowStart c H K m := by
  let L := explorationWindowStart c H K m
  let A := max 1 (c ^ 2)
  have hb := explorationWindow_bounds c H K m
  have hK : (0 : ℝ) ≤ K := Nat.cast_nonneg K
  have hA : 1 ≤ A := le_max_left _ _
  have hcA : c ^ 2 ≤ A := le_max_right _ _
  have hL1 : (1 : ℝ) ≤ L := by dsimp [L]; linarith [hb.1]
  have hLNat : 1 ≤ L := by exact_mod_cast hL1
  have hL0 : (0 : ℝ) ≤ L := hL1.trans' (by norm_num)
  have hRoot : 8 * (K : ℝ) * A + 2 ≤ Real.sqrt (L : ℝ) :=
    Real.le_sqrt_of_sq_le hb.2.2
  have hSqrt1 : 1 ≤ Real.sqrt (L : ℝ) := Real.le_sqrt_of_sq_le (by simpa using hL1)
  have hSqrtPos : 0 < Real.sqrt (L : ℝ) := by linarith
  have hxPos : (0 : ℝ) < (2 * L + offset + 1 : ℕ) := by positivity
  have hxLe : ((2 * L + offset + 1 : ℕ) : ℝ) ≤ 4 * L := by
    exact_mod_cast (show 2 * L + offset + 1 ≤ 4 * L by omega)
  have hSqrtBound : Real.sqrt (2 * L + offset + 1 : ℕ) ≤ 2 * Real.sqrt (L : ℝ) := by
    have hs1 := Real.sq_sqrt hxPos.le
    have hs2 := Real.sq_sqrt hL0
    have hn1 := Real.sqrt_nonneg ((2 * L + offset + 1 : ℕ) : ℝ)
    nlinarith
  have hLog : Real.log (2 * L + offset + 1 : ℕ) ≤ 4 * Real.sqrt (L : ℝ) :=
    (log_le_two_sqrt hxPos).trans (by linarith)
  have hLog0 : 0 ≤ Real.log (2 * L + offset + 1 : ℕ) :=
    Real.log_nonneg (by exact_mod_cast Nat.le_add_left 1 (2 * L + offset))
  have hProd := mul_le_mul hcA hLog hLog0 (by linarith : 0 ≤ A)
  have hTerm : c ^ 2 * Real.log (2 * L + offset + 1 : ℕ) + 1 ≤
      4 * A * Real.sqrt (L : ℝ) + Real.sqrt (L : ℝ) := by nlinarith
  have hUpper : (K : ℝ) * (c ^ 2 * Real.log (2 * L + offset + 1 : ℕ) + 1) ≤
      (4 * (K : ℝ) * A + K) * Real.sqrt (L : ℝ) := by
    calc
      _ ≤ (K : ℝ) * (4 * A * Real.sqrt (L : ℝ) + Real.sqrt (L : ℝ)) :=
        mul_le_mul_of_nonneg_left hTerm hK
      _ = _ := by ring
  have hKA : (K : ℝ) ≤ (K : ℝ) * A := by nlinarith
  have hCoef : 4 * (K : ℝ) * A + K < Real.sqrt (L : ℝ) := by nlinarith
  have hStrict := mul_lt_mul_of_pos_right hCoef hSqrtPos
  rw [Real.mul_self_sqrt hL0] at hStrict
  exact hUpper.trans_lt hStrict

theorem explicit_window_explores {Arm : Type*} [Fintype Arm] [DecidableEq Arm]
    (action : ℕ → Arm) (q penalty : ℕ → Arm → ℝ) (c H : ℝ) (offset m : ℕ) (arm : Arm)
    (hc : 0 < c) (hH : 0 ≤ H) (hOffset : offset ≤ 1)
    (hInitialized : ∀ a, 0 < AgentUCT.pullCount action a (Fintype.card Arm))
    (hQ : ∀ t, ∀ a, 0 ≤ q t a ∧ q t a ≤ 1)
    (hPenalty : ∀ t, ∀ a, 0 ≤ penalty t a ∧ penalty t a ≤ H)
    (hSelect : ∀ t, Fintype.card Arm ≤ t → ∀ a,
      treeIndex (q t a) c (penalty t a) (t + offset) (AgentUCT.pullCount action a t) ≤
        treeIndex (q t (action t)) c (penalty t (action t)) (t + offset)
          (AgentUCT.pullCount action (action t) t)) :
    m < AgentUCT.pullCount action arm (2 * explorationWindowStart c H (Fintype.card Arm) m) := by
  let L := explorationWindowStart c H (Fintype.card Arm) m
  have hKL : Fintype.card Arm ≤ L := by
    have h := (explorationWindow_bounds c H (Fintype.card Arm) m).1
    have hn : (Fintype.card Arm : ℝ) ≤ L := by dsimp [L]; linarith
    exact_mod_cast hn
  apply finite_window_explores action q penalty c H offset L (2 * L) m arm hc.le hH
  · exact fun a ↦ lt_of_lt_of_le (hInitialized a) (pullCount_monotone action a hKL)
  · exact fun t _ a ↦ hQ t a
  · exact fun t _ a ↦ hPenalty t a
  · exact fun t ht a ↦ hSelect t (hKL.trans (mem_Ico.mp ht).1) a
  · exact explorationWindow_pressure c H (Fintype.card Arm) m offset hc
  · have h := explorationWindow_long_enough c H (Fintype.card Arm) m offset hOffset
    have he : 2 * L - L = L := by omega
    simpa only [he] using h

/-- A finite observed history suffices; its arbitrary extension has no policy obligations. -/
theorem finite_explicit_window_explores {Arm : Type*} [Fintype Arm] [DecidableEq Arm]
    (action : ℕ → Arm) (q penalty : ℕ → Arm → ℝ) (c H : ℝ)
    (offset m horizon : ℕ) (arm : Arm)
    (hc : 0 < c) (hH : 0 ≤ H) (hOffset : offset ≤ 1)
    (hEnd : 2 * explorationWindowStart c H (Fintype.card Arm) m ≤ horizon)
    (hInitialized : ∀ a, 0 < AgentUCT.pullCount action a (Fintype.card Arm))
    (hQ : ∀ t < horizon, ∀ a, 0 ≤ q t a ∧ q t a ≤ 1)
    (hPenalty : ∀ t < horizon, ∀ a, 0 ≤ penalty t a ∧ penalty t a ≤ H)
    (hSelect : ∀ t < horizon, Fintype.card Arm ≤ t → ∀ a,
      treeIndex (q t a) c (penalty t a) (t + offset) (AgentUCT.pullCount action a t) ≤
        treeIndex (q t (action t)) c (penalty t (action t)) (t + offset)
          (AgentUCT.pullCount action (action t) t)) :
    m < AgentUCT.pullCount action arm horizon := by
  let L := explorationWindowStart c H (Fintype.card Arm) m
  have hKL : Fintype.card Arm ≤ L := by
    have h := (explorationWindow_bounds c H (Fintype.card Arm) m).1
    have hn : (Fintype.card Arm : ℝ) ≤ L := by dsimp [L]; linarith
    exact_mod_cast hn
  have hWindow : m < AgentUCT.pullCount action arm (2 * L) := by
    apply finite_window_explores action q penalty c H offset L (2 * L) m arm hc.le hH
    · exact fun a ↦ lt_of_lt_of_le (hInitialized a) (pullCount_monotone action a hKL)
    · exact fun t ht a ↦ hQ t (lt_of_lt_of_le (mem_Ico.mp ht).2 hEnd) a
    · exact fun t ht a ↦ hPenalty t (lt_of_lt_of_le (mem_Ico.mp ht).2 hEnd) a
    · exact fun t ht a ↦ hSelect t (lt_of_lt_of_le (mem_Ico.mp ht).2 hEnd)
        (hKL.trans (mem_Ico.mp ht).1) a
    · exact explorationWindow_pressure c H (Fintype.card Arm) m offset hc
    · have h := explorationWindow_long_enough c H (Fintype.card Arm) m offset hOffset
      have he : 2 * L - L = L := by omega
      simpa only [he] using h
  exact hWindow.trans_le (pullCount_monotone action arm hEnd)

end AgentUCTPaper
