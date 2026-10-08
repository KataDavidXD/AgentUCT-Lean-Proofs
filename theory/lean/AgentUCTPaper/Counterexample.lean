import AgentUCTPaper.Regret

/-! # Persistent cost bias causes linear true regret

The two arms have deterministic rewards. The cost-aware UCB rule receives exact
reward means and uses a persistently biased cost forecast. Every trajectory of
that rule, after one initialization pull per arm, satisfies a linear-minus-log
lower bound on regret for true net values. This is stronger than a ranking-only
counterexample and requires no probabilistic approximation.
-/

noncomputable section

open Finset

namespace AgentUCTPaper

def biasedReward : Bool → ℝ
  | true => 4 / 5
  | false => 7 / 10

def biasedTrueCost (_ : Bool) : ℝ := 1 / 10

def biasedCostEstimate : Bool → ℝ
  | true => 4 / 10
  | false => 1 / 10

def biasedTrueGap (action : ℕ → Bool) (t : ℕ) : ℝ :=
  localGap biasedReward (fun _ ↦ biasedTrueCost) 1 action (fun _ ↦ true) t

def biasedProxyGap (action : ℕ → Bool) (t : ℕ) : ℝ :=
  localGap biasedReward (fun _ ↦ biasedCostEstimate) 1 action (fun _ ↦ false) t

theorem biased_gap_identity (action : ℕ → Bool) (t : ℕ) :
    biasedTrueGap action t = 1 / 10 - (1 / 2) * biasedProxyGap action t := by
  cases h : action t <;>
    norm_num [biasedTrueGap, biasedProxyGap, localGap, AgentUCT.net,
      biasedReward, biasedTrueCost, biasedCostEstimate, h]

theorem biased_regret_identity (action : ℕ → Bool) (T : ℕ) :
    (∑ t ∈ Finset.range T, biasedTrueGap action t) =
      (T : ℝ) / 10 - (1 / 2) * ∑ t ∈ Finset.range T, biasedProxyGap action t := by
  simp_rw [biased_gap_identity, Finset.sum_sub_distrib, ← Finset.mul_sum]
  simp [div_eq_mul_inv]

theorem bool_initialized_count (action : ℕ → Bool)
    (hInitA : action 0 = true) (hInitB : action 1 = false)
    {t : ℕ} (ht : 2 ≤ t) (arm : Bool) :
    0 < AgentUCT.pullCount action arm t := by
  unfold AgentUCT.pullCount
  apply Finset.card_pos.mpr
  cases arm with
  | false => exact ⟨1, by simp [hInitB]; omega⟩
  | true => exact ⟨0, by simp [hInitA]; omega⟩

/-- The proxy UCB rule selects a truly inferior arm on all but logarithmically
many visits. The conclusion holds for every tie-breaking rule satisfying index
maximization. The count `T` includes the two initialization pulls. -/
theorem biased_cost_linear_regret
    (action : ℕ → Bool) {T : ℕ} (hT : 1 ≤ T)
    (hInitA : action 0 = true) (hInitB : action 1 = false)
    (hSelect : ∀ t < T, 2 ≤ t → ∀ arm : Bool,
      biasedReward arm + localRadius action arm t - biasedCostEstimate arm ≤
      biasedReward (action t) + localRadius action (action t) t -
        biasedCostEstimate (action t)) :
    (T : ℝ) / 10 - 40 * Real.log (T : ℝ) - 2 / 5 ≤
      ∑ t ∈ Finset.range T, biasedTrueGap action t := by
  classical
  have hp := local_regret_all_rounds action (fun _ ↦ false) biasedReward
    (fun _ ↦ biasedReward) (fun _ ↦ biasedCostEstimate) 1 (fun _ ↦ False)
    (T := T) (delta := 1 / 5) (D := 1 / 5) hT (by norm_num) (by norm_num)
    (by
      intro t _
      cases h : action t <;>
        norm_num [localGap, AgentUCT.net, biasedReward, biasedCostEstimate, h])
    (by
      intro t _
      cases h : action t <;>
        norm_num [localGap, AgentUCT.net, biasedReward, biasedCostEstimate, h])
    (by
      intro t _ hg
      cases h : action t with
      | false => norm_num [localGap, AgentUCT.net, biasedReward, biasedCostEstimate, h] at hg
      | true => norm_num [localGap, AgentUCT.net, biasedReward, biasedCostEstimate, h])
    (by
      intro t _ ht
      exact bool_initialized_count action hInitA hInitB (by simpa using ht) (action t))
    (by
      intro t _ _ _
      have := Real.sqrt_nonneg (2 * Real.log (t + 1 : ℕ) /
        (AgentUCT.pullCount action false t : ℝ))
      change biasedReward false ≤ biasedReward false + localRadius action false t
      exact le_add_of_nonneg_right this)
    (by
      intro t _ _ _
      have := Real.sqrt_nonneg (2 * Real.log (t + 1 : ℕ) /
        (AgentUCT.pullCount action (action t) t : ℝ))
      exact le_add_of_nonneg_right this)
    (by
      intro t ht hk
      simpa using hSelect t ht (by simpa using hk) false)
  have hProxy : (∑ t ∈ Finset.range T, biasedProxyGap action t) ≤
      80 * Real.log (T : ℝ) + 4 / 5 := by
    convert hp using 1
    norm_num
    ring
  rw [biased_regret_identity]
  linarith

#print axioms biased_gap_identity
#print axioms biased_regret_identity
#print axioms bool_initialized_count
#print axioms biased_cost_linear_regret

end AgentUCTPaper
