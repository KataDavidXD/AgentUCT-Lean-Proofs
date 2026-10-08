import AgentUCT

/-! # Local UCT regret with changing execution costs

The all-round theorem includes initialization and arbitrary failed confidence rounds.
It is deterministic: concentration of the supplied reward estimates is proved separately.
The drift lemma makes the extra errors of adaptive tree returns explicit.
-/

noncomputable section

open Finset

namespace AgentUCTPaper

/-- The true-current gap includes current execution cost, not past paid costs. -/
def localGap {Arm : Type*} (mu : Arm → ℝ) (cost : ℕ → Arm → ℝ)
    (lambda : ℝ) (action best : ℕ → Arm) (t : ℕ) : ℝ :=
  AgentUCT.net (mu (best t)) (cost t (best t)) lambda -
    AgentUCT.net (mu (action t)) (cost t (action t)) lambda

/-- Radius based on the number of observations before the current local visit. -/
def localRadius {Arm : Type*} [DecidableEq Arm]
    (action : ℕ → Arm) (arm : Arm) (t : ℕ) : ℝ :=
  Real.sqrt (2 * Real.log (t + 1 : ℕ) / (AgentUCT.pullCount action arm t : ℝ))

/-- Adaptive reward drift and cost prediction error are separate error terms.
`center` is the reward mean around which the estimate concentrates; `current` is
the reward value used by the current comparator. No stationarity is hidden here. -/
theorem drift_plugin_gap_bound
    {currentBest currentChosen centerBest centerChosen qBest qChosen
      rBest rChosen cBest cChosen cHatBest cHatChosen
      zBest zChosen eBest eChosen lambda : ℝ}
    (hLambda : 0 ≤ lambda)
    (hBestConfidence : centerBest ≤ qBest + rBest)
    (hChosenConfidence : qChosen ≤ centerChosen + rChosen)
    (hBestDrift : currentBest - centerBest ≤ zBest)
    (hChosenDrift : centerChosen - currentChosen ≤ zChosen)
    (hBestCost : cHatBest - cBest ≤ eBest)
    (hChosenCost : cChosen - cHatChosen ≤ eChosen)
    (hSelect : qBest + rBest - lambda * cHatBest ≤
      qChosen + rChosen - lambda * cHatChosen) :
    AgentUCT.net currentBest cBest lambda -
      AgentUCT.net currentChosen cChosen lambda ≤
      2 * rChosen + zBest + zChosen + lambda * (eBest + eChosen) := by
  have h := AgentUCT.plugin_gap_bound hLambda hBestConfidence hChosenConfidence
    hBestCost hChosenCost hSelect
  unfold AgentUCT.net at h ⊢
  linarith

/-- If total drift and cost error consume at most a fraction of the gap,
the ordinary UCB counting argument still applies with the remaining gap. -/
theorem count_threshold_with_errors {gap radius count logHorizon error delta eta : ℝ}
    (hDelta : 0 < delta) (hEta : eta < 1)
    (hRadius : 0 ≤ radius) (hCount : 0 ≤ count)
    (hGapLower : delta ≤ gap)
    (hGapBound : gap ≤ 2 * radius + error)
    (hError : error ≤ eta * delta)
    (hVariance : radius ^ 2 * count ≤ 2 * logHorizon) :
    count ≤ 8 * logHorizon / ((1 - eta) * delta) ^ 2 := by
  apply AgentUCT.exploration_count_threshold (mul_pos (by linarith) hDelta)
    hRadius hCount _ hVariance
  nlinarith

section LocalRegret

variable {Arm : Type*} [Fintype Arm] [DecidableEq Arm]

/-- An all-round bound for the same-cache comparator at a single bandit node.
The first `card Arm` rounds initialize the arms. Remaining failed confidence
rounds are charged at the maximum per-round gap, while good positive-gap rounds
are counted by their genuine observation counts. Costs may vary at every round.
-/
theorem local_regret_all_rounds
    (action best : ℕ → Arm) (mu : Arm → ℝ) (q cost : ℕ → Arm → ℝ)
    (lambda : ℝ) (bad : ℕ → Prop) [DecidablePred bad]
    {T : ℕ} {delta D : ℝ}
    (hT : 1 ≤ T) (hDelta : 0 < delta) (hD : 0 ≤ D)
    (hGapNonneg : ∀ t < T, 0 ≤ localGap mu cost lambda action best t)
    (hGapUpper : ∀ t < T, localGap mu cost lambda action best t ≤ D)
    (hSeparated : ∀ t < T, 0 < localGap mu cost lambda action best t →
      delta ≤ localGap mu cost lambda action best t)
    (hCount : ∀ t < T, Fintype.card Arm ≤ t →
      0 < AgentUCT.pullCount action (action t) t)
    (hBest : ∀ t < T, Fintype.card Arm ≤ t → ¬ bad t →
      mu (best t) ≤ q t (best t) + localRadius action (best t) t)
    (hChosen : ∀ t < T, Fintype.card Arm ≤ t → ¬ bad t →
      q t (action t) ≤ mu (action t) + localRadius action (action t) t)
    (hSelect : ∀ t < T, Fintype.card Arm ≤ t →
      q t (best t) + localRadius action (best t) t - lambda * cost t (best t) ≤
      q t (action t) + localRadius action (action t) t - lambda * cost t (action t)) :
    (∑ t ∈ Finset.range T, localGap mu cost lambda action best t) ≤
      (Fintype.card Arm : ℝ) * D * (8 * Real.log (T : ℝ) / delta ^ 2 + 2) +
      D * ∑ t ∈ Finset.range T, if bad t then (1 : ℝ) else 0 := by
  classical
  let K := Fintype.card Arm
  let gap := localGap mu cost lambda action best
  let good := (Finset.range T).filter
    (fun t ↦ K ≤ t ∧ ¬ bad t ∧ 0 < gap t)
  have hGoodMem (t : ℕ) : t ∈ good ↔
      t < T ∧ K ≤ t ∧ ¬ bad t ∧ 0 < gap t := by
    simp only [good, Finset.mem_filter, Finset.mem_range]
  have hGood : (∑ t ∈ good, gap t) ≤
      (K : ℝ) * D * (8 * Real.log (T : ℝ) / delta ^ 2 + 1) := by
    apply AgentUCT.dynamic_local_good_regret Finset.univ good action best mu q cost
      lambda hT hDelta hD
    · intro t _
      exact Finset.mem_univ _
    · intro t ht
      have := ((hGoodMem t).mp ht).1
      omega
    · intro t ht
      obtain ⟨ht, hk, _, _⟩ := (hGoodMem t).mp ht
      exact hCount t ht hk
    · intro t ht
      obtain ⟨ht, hk, hb, _⟩ := (hGoodMem t).mp ht
      exact hBest t ht hk hb
    · intro t ht
      obtain ⟨ht, hk, hb, _⟩ := (hGoodMem t).mp ht
      exact hChosen t ht hk hb
    · intro t ht
      obtain ⟨ht, hk, _, _⟩ := (hGoodMem t).mp ht
      exact hSelect t ht hk
    · intro t ht
      obtain ⟨ht, _, _, hg⟩ := (hGoodMem t).mp ht
      exact hSeparated t ht hg
    · intro t ht
      exact hGapUpper t ((hGoodMem t).mp ht).1
  have hPoint (t : ℕ) (ht : t ∈ Finset.range T) :
      gap t ≤ (if t < K then D else 0) +
        (if bad t then D else 0) + (if t ∈ good then gap t else 0) := by
    have ht' := Finset.mem_range.mp ht
    have hgu := hGapUpper t ht'
    have hgn := hGapNonneg t ht'
    by_cases hk : t < K
    · have hng : t ∉ good := by
        intro hg
        have := ((hGoodMem t).mp hg).2.1
        omega
      by_cases hb : bad t <;> simp only [hk, hb, hng, if_true, if_false]
      · linarith
      · simpa only [add_zero] using hgu
    · by_cases hb : bad t
      · have hng : t ∉ good := by
          intro hg
          exact ((hGoodMem t).mp hg).2.2.1 hb
        simpa only [hk, hb, hng, if_true, if_false, zero_add, add_zero] using hgu
      · by_cases hg : 0 < gap t
        · have hmem : t ∈ good := (hGoodMem t).mpr ⟨ht', by omega, hb, hg⟩
          simp only [hk, hb, hmem, if_true, if_false, zero_add, le_refl]
        · have heq : gap t = 0 := by dsimp [gap] at hg ⊢; linarith
          simp [hk, hb, heq]
  have hInit : (∑ t ∈ Finset.range T, if t < K then D else 0) ≤ (K : ℝ) * D := by
    calc
      _ = ∑ _t ∈ (Finset.range T).filter (fun t ↦ t < K), D := by
        rw [Finset.sum_filter]
      _ = (((Finset.range T).filter (fun t ↦ t < K)).card : ℝ) * D := by simp
      _ ≤ (K : ℝ) * D := by
        apply mul_le_mul_of_nonneg_right _ hD
        have hc := Finset.card_le_card (show
          (Finset.range T).filter (fun t ↦ t < K) ⊆ Finset.range K from
          fun t ht ↦ Finset.mem_range.mpr (Finset.mem_filter.mp ht).2)
        simp only [Finset.card_range] at hc
        exact_mod_cast hc
  have hGoodSum : (∑ t ∈ Finset.range T, if t ∈ good then gap t else 0) =
      ∑ t ∈ good, gap t := by
    rw [← Finset.sum_filter]
    congr 1
    ext t
    simp only [Finset.mem_filter]
    exact ⟨And.right, fun ht ↦ ⟨Finset.mem_range.mpr ((hGoodMem t).mp ht).1, ht⟩⟩
  have hBadSum : (∑ t ∈ Finset.range T, if bad t then D else 0) =
      D * ∑ t ∈ Finset.range T, if bad t then (1 : ℝ) else 0 := by
    rw [Finset.mul_sum]
    apply Finset.sum_congr rfl
    intro t _
    by_cases hb : bad t <;> simp [hb]
  have hSum := Finset.sum_le_sum hPoint
  simp only [Finset.sum_add_distrib, hGoodSum, hBadSum] at hSum
  change (∑ t ∈ Finset.range T, gap t) ≤ _
  change _ ≤ (K : ℝ) * D * _ + _
  nlinarith

/-- A complete deterministic regret bound with an explicit cumulative error budget.
`error` can contain both adaptive reward drift and plug-in cost prediction error.
No stationarity of `gap` is assumed. On rounds where the error exceeds half the
gap, regret is charged to twice the error; the remaining rounds admit UCB counting.
-/
theorem local_regret_with_error_budget
    (action : ℕ → Arm) (gap error : ℕ → ℝ)
    (bad : ℕ → Prop) [DecidablePred bad]
    {T : ℕ} {delta D : ℝ}
    (hT : 1 ≤ T) (hDelta : 0 < delta) (hD : 0 ≤ D)
    (hGapNonneg : ∀ t < T, 0 ≤ gap t)
    (hGapUpper : ∀ t < T, gap t ≤ D)
    (hErrorNonneg : ∀ t < T, 0 ≤ error t)
    (hSeparated : ∀ t < T, 0 < gap t → delta ≤ gap t)
    (hCount : ∀ t < T, Fintype.card Arm ≤ t →
      0 < AgentUCT.pullCount action (action t) t)
    (hOptimism : ∀ t < T, Fintype.card Arm ≤ t → ¬ bad t →
      gap t ≤ 2 * localRadius action (action t) t + error t) :
    (∑ t ∈ Finset.range T, gap t) ≤
      (Fintype.card Arm : ℝ) * D * (32 * Real.log (T : ℝ) / delta ^ 2 + 2) +
      2 * (∑ t ∈ Finset.range T, error t) +
      D * ∑ t ∈ Finset.range T, if bad t then (1 : ℝ) else 0 := by
  classical
  let K := Fintype.card Arm
  let good := (Finset.range T).filter
    (fun t ↦ K ≤ t ∧ ¬ bad t ∧ 0 < gap t ∧ 2 * error t ≤ gap t)
  have hGoodMem (t : ℕ) : t ∈ good ↔
      t < T ∧ K ≤ t ∧ ¬ bad t ∧ 0 < gap t ∧ 2 * error t ≤ gap t := by
    simp only [good, Finset.mem_filter, Finset.mem_range]
  have hPerArm (arm : Arm) :
      (∑ t ∈ good.filter (fun t ↦ action t = arm), gap t) ≤
      D * (32 * Real.log (T : ℝ) / delta ^ 2 + 1) := by
    have hb := AgentUCT.good_arm_regret_bound action arm
      (good.filter (fun t ↦ action t = arm)) gap
      (fun t ↦ 2 * localRadius action arm t)
      (delta := delta) (maxGap := D) (logHorizon := 4 * Real.log (T : ℝ))
      hDelta hD (mul_nonneg (by norm_num)
        (Real.log_nonneg (by exact_mod_cast hT)))
    have hBound := hb (fun t ht ↦ (Finset.mem_filter.mp ht).2)
      (fun t ht ↦ hSeparated t ((hGoodMem t).mp (Finset.mem_filter.mp ht).1).1
        ((hGoodMem t).mp (Finset.mem_filter.mp ht).1).2.2.2.1)
      (fun t ht ↦ hGapUpper t ((hGoodMem t).mp (Finset.mem_filter.mp ht).1).1)
      (fun t _ ↦ mul_nonneg (by norm_num) (Real.sqrt_nonneg _))
      (by
        intro t ht
        obtain ⟨hmem, ha⟩ := Finset.mem_filter.mp ht
        obtain ⟨ht, hk, hbad, _, herr⟩ := (hGoodMem t).mp hmem
        have hop := hOptimism t ht hk hbad
        rw [ha] at hop
        linarith)
      (by
        intro t ht
        obtain ⟨hmem, ha⟩ := Finset.mem_filter.mp ht
        obtain ⟨ht, hk, _, _, _⟩ := (hGoodMem t).mp hmem
        have hct := hCount t ht hk
        rw [ha] at hct
        have hv := AgentUCT.radius_at_horizon action arm (by omega : t + 1 ≤ T) hct
        change (2 * localRadius action arm t) ^ 2 *
          (AgentUCT.pullCount action arm t : ℝ) ≤ _
        change (localRadius action arm t) ^ 2 *
          (AgentUCT.pullCount action arm t : ℝ) ≤ _ at hv
        nlinarith)
    convert hBound using 1
    ring
  have hGood : (∑ t ∈ good, gap t) ≤
      (K : ℝ) * D * (32 * Real.log (T : ℝ) / delta ^ 2 + 1) := by
    have hPartition : (∑ arm : Arm, ∑ t ∈ good.filter (fun t ↦ action t = arm),
        gap t) = ∑ t ∈ good, gap t := by
      simp_rw [Finset.sum_filter]
      rw [Finset.sum_comm]
      apply Finset.sum_congr rfl
      intro t _
      simp
    rw [← hPartition]
    calc
      _ ≤ ∑ _arm : Arm, D * (32 * Real.log (T : ℝ) / delta ^ 2 + 1) :=
        Finset.sum_le_sum (fun arm _ ↦ hPerArm arm)
      _ = _ := by simp [K, mul_assoc]
  have hPoint (t : ℕ) (ht : t ∈ Finset.range T) :
      gap t ≤ (if t < K then D else 0) +
        (if bad t then D else 0) + (if t ∈ good then gap t else 0) + 2 * error t := by
    have ht' := Finset.mem_range.mp ht
    have hgu := hGapUpper t ht'
    have hgn := hGapNonneg t ht'
    have hen := hErrorNonneg t ht'
    have hterm : 0 ≤ (if t ∈ good then gap t else 0) := by
      split_ifs <;> linarith
    by_cases hk : t < K
    · by_cases hb : bad t <;> simp only [hk, hb, if_true, if_false] <;> linarith
    · by_cases hb : bad t
      · simp only [hk, hb, if_true, if_false]
        linarith
      · by_cases hg : 0 < gap t
        · by_cases he : 2 * error t ≤ gap t
          · have hmem : t ∈ good := (hGoodMem t).mpr ⟨ht', by omega, hb, hg, he⟩
            simp only [hk, hb, hmem, if_true, if_false]
            linarith
          · simp only [hk, hb, if_false]
            linarith
        · simp only [hk, hb, if_false]
          linarith
  have hInit : (∑ t ∈ Finset.range T, if t < K then D else 0) ≤ (K : ℝ) * D := by
    calc
      _ = ∑ _t ∈ (Finset.range T).filter (fun t ↦ t < K), D := by
        rw [Finset.sum_filter]
      _ = (((Finset.range T).filter (fun t ↦ t < K)).card : ℝ) * D := by simp
      _ ≤ (K : ℝ) * D := by
        apply mul_le_mul_of_nonneg_right _ hD
        have hc := Finset.card_le_card (show
          (Finset.range T).filter (fun t ↦ t < K) ⊆ Finset.range K from
          fun t ht ↦ Finset.mem_range.mpr (Finset.mem_filter.mp ht).2)
        simp only [Finset.card_range] at hc
        exact_mod_cast hc
  have hGoodSum : (∑ t ∈ Finset.range T, if t ∈ good then gap t else 0) =
      ∑ t ∈ good, gap t := by
    rw [← Finset.sum_filter]
    congr 1
    ext t
    simp only [Finset.mem_filter]
    exact ⟨And.right, fun ht ↦ ⟨Finset.mem_range.mpr ((hGoodMem t).mp ht).1, ht⟩⟩
  have hBadSum : (∑ t ∈ Finset.range T, if bad t then D else 0) =
      D * ∑ t ∈ Finset.range T, if bad t then (1 : ℝ) else 0 := by
    rw [Finset.mul_sum]
    apply Finset.sum_congr rfl
    intro t _
    by_cases hb : bad t <;> simp [hb]
  have hSum := Finset.sum_le_sum hPoint
  simp only [Finset.sum_add_distrib, hGoodSum, hBadSum, ← Finset.mul_sum] at hSum
  change _ ≤ (K : ℝ) * D * _ + _ + _
  nlinarith

end LocalRegret

/-- Sum of local comparator regrets over finitely many visited tree nodes.
Each node may have its own action type, horizon, gap separation, and gap bound.
This measures the sum of local selection gaps: it is not simple regret of the
terminal recommendation, nor regret against an alternative cache trajectory.
-/
theorem tree_local_regret_with_error_budget
    {Node : Type*} (nodes : Finset Node) (Arm : Node → Type*)
    [∀ v, Fintype (Arm v)] [∀ v, DecidableEq (Arm v)]
    (action : (v : Node) → ℕ → Arm v) (gap error : Node → ℕ → ℝ)
    (bad : Node → ℕ → Prop) [∀ v, DecidablePred (bad v)]
    (T : Node → ℕ) (delta D : Node → ℝ)
    (hT : ∀ v ∈ nodes, 1 ≤ T v)
    (hDelta : ∀ v ∈ nodes, 0 < delta v)
    (hD : ∀ v ∈ nodes, 0 ≤ D v)
    (hGapNonneg : ∀ v ∈ nodes, ∀ t < T v, 0 ≤ gap v t)
    (hGapUpper : ∀ v ∈ nodes, ∀ t < T v, gap v t ≤ D v)
    (hErrorNonneg : ∀ v ∈ nodes, ∀ t < T v, 0 ≤ error v t)
    (hSeparated : ∀ v ∈ nodes, ∀ t < T v, 0 < gap v t → delta v ≤ gap v t)
    (hCount : ∀ v ∈ nodes, ∀ t < T v, Fintype.card (Arm v) ≤ t →
      0 < AgentUCT.pullCount (action v) (action v t) t)
    (hOptimism : ∀ v ∈ nodes, ∀ t < T v, Fintype.card (Arm v) ≤ t → ¬ bad v t →
      gap v t ≤ 2 * localRadius (action v) (action v t) t + error v t) :
    (∑ v ∈ nodes, ∑ t ∈ Finset.range (T v), gap v t) ≤
      (∑ v ∈ nodes, (Fintype.card (Arm v) : ℝ) * D v *
        (32 * Real.log (T v : ℝ) / delta v ^ 2 + 2)) +
      2 * (∑ v ∈ nodes, ∑ t ∈ Finset.range (T v), error v t) +
      ∑ v ∈ nodes, D v * ∑ t ∈ Finset.range (T v), if bad v t then (1 : ℝ) else 0 := by
  calc
    _ ≤ ∑ v ∈ nodes, ((Fintype.card (Arm v) : ℝ) * D v *
          (32 * Real.log (T v : ℝ) / delta v ^ 2 + 2) +
        2 * (∑ t ∈ Finset.range (T v), error v t) +
        D v * ∑ t ∈ Finset.range (T v), if bad v t then (1 : ℝ) else 0) := by
      apply Finset.sum_le_sum
      intro v hv
      exact local_regret_with_error_budget (action v) (gap v) (error v) (bad v)
        (hT v hv) (hDelta v hv) (hD v hv) (hGapNonneg v hv) (hGapUpper v hv)
        (hErrorNonneg v hv) (hSeparated v hv) (hCount v hv) (hOptimism v hv)
    _ = _ := by simp only [Finset.sum_add_distrib, ← Finset.mul_sum]

#print axioms drift_plugin_gap_bound
#print axioms count_threshold_with_errors
#print axioms local_regret_all_rounds
#print axioms local_regret_with_error_budget
#print axioms tree_local_regret_with_error_budget

end AgentUCTPaper
