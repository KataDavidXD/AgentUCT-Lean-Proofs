import AgentUCTPaper.TreeWindow

/-! # Explicit numerical thresholds and counting for the subtree induction -/

set_option autoImplicit false

noncomputable section

namespace AgentUCTPaper

open Finset

theorem log_nat_succ_le_four_sqrt (n : ℕ) (hn : 0 < n) :
    Real.log (n + 1 : ℕ) ≤ 4 * Real.sqrt (n : ℝ) := by
  have hN : (1 : ℝ) ≤ n := by exact_mod_cast hn
  have hs := Real.sq_sqrt (Nat.cast_nonneg n : (0 : ℝ) ≤ n)
  have hs' := Real.sq_sqrt (Nat.cast_nonneg (n + 1) : (0 : ℝ) ≤ (n + 1 : ℕ))
  have hNonneg := Real.sqrt_nonneg (n : ℝ)
  have hNonneg' := Real.sqrt_nonneg ((n + 1 : ℕ) : ℝ)
  have hBound : Real.sqrt (n + 1 : ℕ) ≤ 2 * Real.sqrt (n : ℝ) := by
    have hCast : ((n + 1 : ℕ) : ℝ) = (n : ℝ) + 1 := by push_cast; rfl
    nlinarith
  exact (log_le_two_sqrt (by positivity : (0 : ℝ) < (n + 1 : ℕ))).trans (by linarith)

def biasVisitTarget (A B delta : ℝ) : ℕ :=
  ⌈max 1 (max ((32 * A / delta) ^ 2) (8 * B / delta))⌉₊

theorem biasVisitTarget_bounds (A B delta : ℝ) :
    (1 : ℝ) ≤ biasVisitTarget A B delta ∧
      (32 * A / delta) ^ 2 ≤ biasVisitTarget A B delta ∧
      8 * B / delta ≤ biasVisitTarget A B delta := by
  have h := Nat.le_ceil (max 1 (max ((32 * A / delta) ^ 2) (8 * B / delta)))
  exact ⟨(le_max_left _ _).trans h,
    (le_max_left _ _).trans ((le_max_right _ _).trans h),
    (le_max_right _ _).trans ((le_max_right _ _).trans h)⟩

theorem logarithmic_deficit_small {A B delta D : ℝ} (n : ℕ)
    (hA : 0 ≤ A) (hDelta : 0 < delta) (hN : biasVisitTarget A B delta ≤ n)
    (hDeficit : D ≤ A * Real.log (n + 1 : ℕ) + B) : D / n ≤ delta / 4 := by
  -- Q5.1：m的三项分别确保正分母、A*log/n≤delta/8、B/n≤delta/8。
  obtain ⟨hOne, hSquare, hB⟩ := biasVisitTarget_bounds A B delta
  have hn : (biasVisitTarget A B delta : ℝ) ≤ n := by exact_mod_cast hN
  have hNat : 0 < n := by
    have h : (1 : ℝ) ≤ n := hOne.trans hn
    exact_mod_cast h
  have hPos : (0 : ℝ) < n := Nat.cast_pos.mpr hNat
  have hRoot : 32 * A / delta ≤ Real.sqrt (n : ℝ) :=
    Real.le_sqrt_of_sq_le (hSquare.trans hn)
  have hA' := (div_le_iff₀ hDelta).mp hRoot
  have hB' := (div_le_iff₀ hDelta).mp (hB.trans hn)
  have hMul := mul_le_mul_of_nonneg_right hA' (Real.sqrt_nonneg (n : ℝ))
  have hSq := Real.sq_sqrt hPos.le
  have hLog := mul_le_mul_of_nonneg_left (log_nat_succ_le_four_sqrt n hNat) hA
  -- Q5.2：log(n+1)≤4*sqrt(n)，乘除均保留所需非负/正条件。
  apply (div_le_iff₀ hPos).mpr
  nlinarith

theorem selected_count_from_subtree_bias {qBest qChosen vBest vChosen c delta : ℝ}
    {parent bestCount chosenCount : ℕ} (hc : 0 ≤ c) (hDelta : 0 < delta)
    (hChosen : 0 < chosenCount) (hBestQ : vBest - delta / 4 ≤ qBest)
    (hChosenQ : qChosen ≤ vChosen) (hGap : delta ≤ vBest - vChosen)
    (hSelect : treeIndex qBest c 0 parent bestCount ≤ treeIndex qChosen c 0 parent chosenCount) :
    (chosenCount : ℝ) ≤ 4 * c ^ 2 * Real.log (parent + 1 : ℕ) / delta ^ 2 := by
  -- Q6.2：次优值gap≥delta，最优均值损失≤delta/4，最大性迫使所选bonus大。
  have hBestRadius := treeBonus_nonnegative hc parent bestCount
  have hChosenRadius := treeBonus_nonnegative hc parent chosenCount
  have hSquare := treeBonus_square c parent chosenCount hChosen
  have hGapBonus : delta ≤ 2 * treeBonus c parent chosenCount := by
    unfold treeIndex at hSelect
    linarith
  -- Q6.3：两边非负才平方，乘正次数，用bonus平方恒等式消去根号。
  have hSq : delta ^ 2 ≤ 4 * treeBonus c parent chosenCount ^ 2 := by nlinarith
  have hMul := mul_le_mul_of_nonneg_right hSq (Nat.cast_nonneg chosenCount : (0 : ℝ) ≤ _)
  apply (le_div_iff₀ (sq_pos_of_pos hDelta)).mpr
  nlinarith

theorem count_le_burnin_add_cap {Arm : Type*} [DecidableEq Arm]
    (action : ℕ → Arm) (arm : Arm) (burnin horizon : ℕ) (cap : ℝ) (hCap : 0 ≤ cap)
    (hLate : ∀ t, burnin ≤ t → t < horizon → action t = arm →
      (AgentUCT.pullCount action arm t : ℝ) ≤ cap) :
    (AgentUCT.pullCount action arm horizon : ℝ) ≤ burnin + cap + 1 := by
  -- Q6.4：按早/晚选择分组；晚期每次选择前次数≤cap，末次更新额外+1。
  let late := (range horizon).filter (fun t ↦ burnin ≤ t ∧ action t = arm)
  have hLateBound : (late.card : ℝ) ≤ cap + 1 :=
    AgentUCT.selected_count_bound action arm late hCap
      (fun t ht ↦ (mem_filter.mp ht).2.2)
      (fun t ht ↦ hLate t (mem_filter.mp ht).2.1
        (mem_range.mp (mem_filter.mp ht).1) (mem_filter.mp ht).2.2)
  have hSubset : (range horizon).filter (fun t ↦ action t = arm) ⊆ range burnin ∪ late := by
    intro t ht
    obtain ⟨ht, ha⟩ := mem_filter.mp ht
    by_cases hb : t < burnin
    · exact mem_union_left _ (mem_range.mpr hb)
    · exact mem_union_right _ (mem_filter.mpr ⟨ht, Nat.le_of_not_gt hb, ha⟩)
  have hCount : AgentUCT.pullCount action arm horizon ≤ burnin + late.card := by
    exact (card_le_card hSubset).trans (by simpa using card_union_le (range burnin) late)
  have hr : (AgentUCT.pullCount action arm horizon : ℝ) ≤ burnin + (late.card : ℝ) := by
    exact_mod_cast hCount
  linarith

end AgentUCTPaper
