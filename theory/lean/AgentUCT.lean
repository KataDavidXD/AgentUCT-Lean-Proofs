import Mathlib.Analysis.SpecialFunctions.Log.Basic
import Mathlib.Data.Real.Sqrt
import Mathlib.Algebra.Order.Floor.Semiring
import Mathlib.Tactic

/-! # AgentUCT: cost shifts, cache accounting, and conditional logarithmic regret

This file proves deterministic inequalities and counting results. Confidence events and their
probabilities must be justified by the sampling model; this file does not silently assume that
adaptive UCT backups or repeated cached evaluations are independent bandit observations.
See the accompanying report for the separate probabilistic argument and its assumptions.
-/

noncomputable section

open Finset

namespace AgentUCT

/-- The cost coefficient includes the fixed normalization: lambda = beta / C_ref. -/
def net (reward cost lambda : ℝ) : ℝ := reward - lambda * cost

/-- The production score is a UCB after translating its reward center by current cost. -/
theorem index_is_shifted_ucb (q radius cost lambda : ℝ) :
    q + radius - lambda * cost = net q cost lambda + radius := by
  unfold net
  ring

/-- A known cost translation does not change the reward estimation error. -/
theorem known_cost_preserves_error (q mu cost lambda : ℝ) :
    |net q cost lambda - net mu cost lambda| = |q - mu| := by
  congr 1
  unfold net
  ring

/-- A candidate-independent baseline changes every index by the same amount. -/
theorem common_baseline_shift (q radius cost baseline lambda : ℝ) :
    q + radius - lambda * (cost - baseline) =
      q + radius - lambda * cost + lambda * baseline := by
  ring

/-- The max-clipped subtraction is exact only when the subtracted baseline is no larger. -/
theorem baseline_clipping_inactive {cost baseline : ℝ} (h : baseline ≤ cost) :
    max 0 (cost - baseline) = cost - baseline := max_eq_right (sub_nonneg.mpr h)

/-- Fixed-cost sample averages can be formed by subtracting the cost after averaging. -/
theorem shifted_sum {Sample : Type*} (samples : Finset Sample) (reward : Sample → ℝ)
    (cost lambda : ℝ) :
    (∑ s ∈ samples, net (reward s) cost lambda) =
      (∑ s ∈ samples, reward s) - samples.card * (lambda * cost) := by
  simp [net, Finset.sum_sub_distrib]

/-- Optimism yields a gap bound even for a history-dependent known cost vector. -/
theorem chosen_gap_le_two_radius
    {muBest muChosen qBest qChosen rBest rChosen cBest cChosen lambda : ℝ}
    (hBest : muBest ≤ qBest + rBest)
    (hChosen : qChosen ≤ muChosen + rChosen)
    (hSelect : qBest + rBest - lambda * cBest ≤
      qChosen + rChosen - lambda * cChosen) :
    net muBest cBest lambda - net muChosen cChosen lambda ≤ 2 * rChosen := by
  unfold net
  linarith

/-- Point-estimate costs add errors for both the chosen option and its comparator. -/
theorem plugin_gap_bound
    {muBest muChosen qBest qChosen rBest rChosen cBest cChosen
      cHatBest cHatChosen eBest eChosen lambda : ℝ}
    (hLambda : 0 ≤ lambda)
    (hBest : muBest ≤ qBest + rBest)
    (hChosen : qChosen ≤ muChosen + rChosen)
    (hCostBest : cHatBest - cBest ≤ eBest)
    (hCostChosen : cChosen - cHatChosen ≤ eChosen)
    (hSelect : qBest + rBest - lambda * cHatBest ≤
      qChosen + rChosen - lambda * cHatChosen) :
    net muBest cBest lambda - net muChosen cChosen lambda ≤
      2 * rChosen + lambda * (eBest + eChosen) := by
  have h1 := mul_le_mul_of_nonneg_left hCostBest hLambda
  have h2 := mul_le_mul_of_nonneg_left hCostChosen hLambda
  unfold net
  nlinarith

/-- A lower confidence bound on nonnegative cost yields an optimistic net-value index. -/
theorem cost_lcb_is_valid {cost estimate error : ℝ}
    (hNonneg : 0 ≤ cost) (hError : |estimate - cost| ≤ error) :
    max 0 (estimate - error) ≤ cost ∧
      cost - max 0 (estimate - error) ≤ 2 * error := by
  have h := abs_le.mp hError
  constructor
  · exact max_le hNonneg (by linarith)
  · have hm := le_max_right (0 : ℝ) (estimate - error)
    linarith

/-- With cost lower bounds, only the selected option's uncertainty remains in the gap. -/
theorem optimistic_cost_gap_bound
    {muBest muChosen qBest qChosen rBest rChosen cBest cChosen
      lBest lChosen eChosen lambda : ℝ}
    (hLambda : 0 ≤ lambda)
    (hBest : muBest ≤ qBest + rBest)
    (hChosen : qChosen ≤ muChosen + rChosen)
    (hLCBBest : lBest ≤ cBest)
    (hLCBChosen : cChosen - lChosen ≤ 2 * eChosen)
    (hSelect : qBest + rBest - lambda * lBest ≤
      qChosen + rChosen - lambda * lChosen) :
    net muBest cBest lambda - net muChosen cChosen lambda ≤
      2 * rChosen + 2 * lambda * eChosen := by
  have h1 := mul_le_mul_of_nonneg_left hLCBBest hLambda
  have h2 := mul_le_mul_of_nonneg_left hLCBChosen hLambda
  unfold net
  nlinarith

section Cache

variable {Resource Path : Type*} [DecidableEq Resource]

/-- A physical resource is paid once, regardless of how many logical paths reference it. -/
def missingCost (required cached : Finset Resource) (unitCost : Resource → ℝ) : ℝ :=
  ∑ r ∈ required \ cached, unitCost r

theorem missingCost_nonnegative (required cached : Finset Resource)
    (unitCost : Resource → ℝ) (h : ∀ r, 0 ≤ unitCost r) :
    0 ≤ missingCost required cached unitCost :=
  Finset.sum_nonneg (fun r _ ↦ h r)

theorem full_cache_zero (required cached : Finset Resource) (unitCost : Resource → ℝ)
    (h : required ⊆ cached) : missingCost required cached unitCost = 0 := by
  simp [missingCost, Finset.sdiff_eq_empty_iff_subset.mpr h]

/-- Enlarging the valid cache cannot increase missing physical work. -/
theorem cache_cost_antitone (required oldCache newCache : Finset Resource)
    (unitCost : Resource → ℝ) (hCache : oldCache ⊆ newCache)
    (hCost : ∀ r, 0 ≤ unitCost r) :
    missingCost required newCache unitCost ≤ missingCost required oldCache unitCost := by
  apply Finset.sum_le_sum_of_subset_of_nonneg
  · intro r hr
    simp only [Finset.mem_sdiff] at hr ⊢
    exact ⟨hr.1, fun ho ↦ hr.2 (hCache ho)⟩
  · intro r _ _
    exact hCost r

/-- Bipartite path-resource accounting equals inclusion probability times cold resource cost.
No independence between resource demands is needed for this finite-sum identity. -/
theorem bipartite_expectation
    (paths : Finset Path) (resources cached : Finset Resource)
    (demand : Path → Resource → Prop) [DecidableRel demand]
    (weight : Path → ℝ) (unitCost : Resource → ℝ) :
    (∑ p ∈ paths, weight p *
      (∑ r ∈ resources, if demand p r ∧ r ∉ cached then unitCost r else 0)) =
    ∑ r ∈ resources, (∑ p ∈ paths, if demand p r then weight p else 0) *
      (if r ∈ cached then 0 else unitCost r) := by
  simp_rw [Finset.mul_sum]
  rw [Finset.sum_comm]
  apply Finset.sum_congr rfl
  intro r _
  rw [Finset.sum_mul]
  apply Finset.sum_congr rfl
  intro p _
  by_cases hc : r ∈ cached <;> by_cases hd : demand p r <;> simp [hc, hd]

end Cache

/-- The actual graph has qid and prefix vertices. `execute` means this edge lies
after that qid's deepest valid checkpoint on the drawn completion, not merely
that an entry is absent from a dictionary. Thus sparse deep checkpoints are allowed.
Weights describe the joint completion / evaluation-panel distribution. -/
theorem qid_prefix_expected_cost {Completion Qid Prefix : Type*}
    (completions : Finset Completion) (qids : Finset Qid) (prefixes : Finset Prefix)
    (execute : Completion → Qid → Prefix → Prop)
    [∀ x q p, Decidable (execute x q p)]
    (weight : Completion → ℝ) (edgeCost : Qid → Prefix → ℝ) :
    (∑ x ∈ completions, weight x *
      (∑ q ∈ qids, ∑ p ∈ prefixes, if execute x q p then edgeCost q p else 0)) =
    ∑ q ∈ qids, ∑ p ∈ prefixes,
      (∑ x ∈ completions, if execute x q p then weight x else 0) * edgeCost q p := by
  simp_rw [Finset.mul_sum]
  rw [Finset.sum_comm]
  apply Finset.sum_congr rfl
  intro q _
  rw [Finset.sum_comm]
  apply Finset.sum_congr rfl
  intro p _
  rw [Finset.sum_mul]
  apply Finset.sum_congr rfl
  intro x _
  by_cases h : execute x q p <;> simp [h]

/-- A positive gap and a Hoeffding-sized radius limit the number of prior observations. -/
theorem exploration_count_threshold {delta radius count logHorizon : ℝ}
    (hDelta : 0 < delta) (hRadius : 0 ≤ radius) (hCount : 0 ≤ count)
    (hGap : delta ≤ 2 * radius)
    (hVariance : radius ^ 2 * count ≤ 2 * logHorizon) :
    count ≤ 8 * logHorizon / delta ^ 2 := by
  have hSquare : delta ^ 2 ≤ 4 * radius ^ 2 := by nlinarith
  have hProduct := mul_le_mul_of_nonneg_right hSquare hCount
  apply (le_div_iff₀ (sq_pos_of_pos hDelta)).mpr
  nlinarith

theorem ucb_radius_variance {logHorizon count : ℝ}
    (hLog : 0 ≤ logHorizon) (hCount : 0 < count) :
    (Real.sqrt (2 * logHorizon / count)) ^ 2 * count = 2 * logHorizon := by
  rw [Real.sq_sqrt (by positivity)]
  exact div_mul_cancel₀ _ (ne_of_gt hCount)

section Counts

variable {Arm : Type*} [DecidableEq Arm]

/-- Number of genuine observations before time t in the bandit abstraction. -/
def pullCount (action : ℕ → Arm) (arm : Arm) (t : ℕ) : ℕ :=
  ((Finset.range t).filter (fun s ↦ action s = arm)).card

theorem pullCount_strict {action : ℕ → Arm} {arm : Arm} {s t : ℕ}
    (hst : s < t) (hs : action s = arm) :
    pullCount action arm s < pullCount action arm t := by
  unfold pullCount
  apply Finset.card_lt_card
  refine Finset.ssubset_iff_subset_ne.mpr ⟨?_, ?_⟩
  · intro x hx
    simp only [Finset.mem_filter, Finset.mem_range] at hx ⊢
    exact ⟨lt_trans hx.1 hst, hx.2⟩
  · intro heq
    have hmem : s ∈ (Finset.range t).filter (fun x ↦ action x = arm) := by
      simp [hst, hs]
    rw [← heq] at hmem
    simp at hmem

theorem pullCount_injective (action : ℕ → Arm) (arm : Arm) (times : Finset ℕ)
    (hSelected : ∀ t ∈ times, action t = arm) :
    Set.InjOn (pullCount action arm) (times : Set ℕ) := by
  intro s hs t ht heq
  by_contra hne
  rcases lt_or_gt_of_ne hne with hst | hts
  · have := pullCount_strict hst (hSelected s hs)
    omega
  · have := pullCount_strict hts (hSelected t ht)
    omega

/-- Distinct selection times have distinct prior counts; at most floor(cap)+1 fit below cap. -/
theorem selected_count_bound (action : ℕ → Arm) (arm : Arm) (times : Finset ℕ)
    {cap : ℝ} (hCap : 0 ≤ cap)
    (hSelected : ∀ t ∈ times, action t = arm)
    (hBound : ∀ t ∈ times, (pullCount action arm t : ℝ) ≤ cap) :
    (times.card : ℝ) ≤ cap + 1 := by
  have hc : times.card ≤ (Finset.range (⌊cap⌋₊ + 1)).card := by
    apply Finset.card_le_card_of_injOn (pullCount action arm)
    · intro t ht
      simp only [Finset.mem_coe, Finset.mem_range]
      have hn : pullCount action arm t ≤ ⌊cap⌋₊ := Nat.le_floor (hBound t ht)
      omega
    · exact pullCount_injective action arm times hSelected
  simp only [Finset.card_range] at hc
  have hcr : (times.card : ℝ) ≤ (⌊cap⌋₊ : ℝ) + 1 := by exact_mod_cast hc
  exact hcr.trans (add_le_add_right (Nat.floor_le hCap) 1)

/-- Conditional per-arm O(log T) regret. The supplied set contains good suboptimal rounds.
The assumptions explicitly connect confidence radius, gap, and genuine observation count. -/
theorem good_arm_regret_bound
    (action : ℕ → Arm) (arm : Arm) (times : Finset ℕ) (gap radius : ℕ → ℝ)
    {delta maxGap logHorizon : ℝ}
    (hDelta : 0 < delta) (hMaxGap : 0 ≤ maxGap) (hLog : 0 ≤ logHorizon)
    (hSelected : ∀ t ∈ times, action t = arm)
    (hGapLower : ∀ t ∈ times, delta ≤ gap t)
    (hGapUpper : ∀ t ∈ times, gap t ≤ maxGap)
    (hRadius : ∀ t ∈ times, 0 ≤ radius t)
    (hOptimism : ∀ t ∈ times, gap t ≤ 2 * radius t)
    (hVariance : ∀ t ∈ times,
      radius t ^ 2 * (pullCount action arm t : ℝ) ≤ 2 * logHorizon) :
    (∑ t ∈ times, gap t) ≤ maxGap * (8 * logHorizon / delta ^ 2 + 1) := by
  have hn : (times.card : ℝ) ≤ 8 * logHorizon / delta ^ 2 + 1 := by
    apply selected_count_bound action arm times (by positivity) hSelected
    intro t ht
    exact exploration_count_threshold hDelta (hRadius t ht) (Nat.cast_nonneg _)
      ((hGapLower t ht).trans (hOptimism t ht)) (hVariance t ht)
  calc
    (∑ t ∈ times, gap t) ≤ ∑ _t ∈ times, maxGap :=
      Finset.sum_le_sum hGapUpper
    _ = maxGap * (times.card : ℝ) := by simp [mul_comm]
    _ ≤ maxGap * (8 * logHorizon / delta ^ 2 + 1) :=
      mul_le_mul_of_nonneg_left hn hMaxGap

/-- In a stationary bandit the per-round gap is constant, recovering 8 log T / delta. -/
theorem stationary_good_regret_bound
    (action : ℕ → Arm) (arm : Arm) (times : Finset ℕ) (radius : ℕ → ℝ)
    {delta logHorizon : ℝ} (hDelta : 0 < delta) (hLog : 0 ≤ logHorizon)
    (hSelected : ∀ t ∈ times, action t = arm)
    (hRadius : ∀ t ∈ times, 0 ≤ radius t)
    (hOptimism : ∀ t ∈ times, delta ≤ 2 * radius t)
    (hVariance : ∀ t ∈ times,
      radius t ^ 2 * (pullCount action arm t : ℝ) ≤ 2 * logHorizon) :
    (times.card : ℝ) * delta ≤ 8 * logHorizon / delta + delta := by
  have h := good_arm_regret_bound action arm times (fun _ ↦ delta) radius hDelta
    (le_of_lt hDelta) hLog hSelected (fun _ _ ↦ le_rfl) (fun _ _ ↦ le_rfl)
    hRadius hOptimism hVariance
  simp only [Finset.sum_const, nsmul_eq_mul] at h
  convert h using 1
  field_simp

/-- The actual UCB1 radius at time t is bounded using any later horizon. -/
theorem radius_at_horizon (action : ℕ → Arm) (arm : Arm) {t horizon : ℕ}
    (hTime : t + 1 ≤ horizon) (hCount : 0 < pullCount action arm t) :
    (Real.sqrt (2 * Real.log (t + 1 : ℕ) / (pullCount action arm t : ℝ))) ^ 2 *
      (pullCount action arm t : ℝ) ≤ 2 * Real.log (horizon : ℝ) := by
  have ht : (1 : ℝ) ≤ (t + 1 : ℕ) := by exact_mod_cast Nat.le_add_left 1 t
  have hlog : 0 ≤ Real.log (t + 1 : ℕ) := Real.log_nonneg ht
  rw [ucb_radius_variance hlog (by exact_mod_cast hCount)]
  apply mul_le_mul_of_nonneg_left _ (by norm_num)
  exact Real.log_le_log (by positivity) (by exact_mod_cast hTime)

/-- Dynamic same-state regret on all good positive-gap rounds at one bandit node.
Costs may change with the cache. The confidence and fixed-mean assumptions remain explicit.
Initialization, zero-gap rounds, and confidence failures are handled separately in the report. -/
theorem dynamic_local_good_regret
    (arms : Finset Arm) (times : Finset ℕ) (action best : ℕ → Arm)
    (mu : Arm → ℝ) (q cost : ℕ → Arm → ℝ) (lambda : ℝ)
    {delta maxGap : ℝ} {horizon : ℕ}
    (hHorizon : 1 ≤ horizon) (hDelta : 0 < delta) (hMaxGap : 0 ≤ maxGap)
    (hIn : ∀ t ∈ times, action t ∈ arms)
    (hTime : ∀ t ∈ times, t + 1 ≤ horizon)
    (hCount : ∀ t ∈ times, 0 < pullCount action (action t) t)
    (hBest : ∀ t ∈ times, mu (best t) ≤ q t (best t) +
      Real.sqrt (2 * Real.log (t + 1 : ℕ) / (pullCount action (best t) t : ℝ)))
    (hChosen : ∀ t ∈ times, q t (action t) ≤ mu (action t) +
      Real.sqrt (2 * Real.log (t + 1 : ℕ) / (pullCount action (action t) t : ℝ)))
    (hSelect : ∀ t ∈ times,
      q t (best t) + Real.sqrt (2 * Real.log (t + 1 : ℕ) /
        (pullCount action (best t) t : ℝ)) - lambda * cost t (best t) ≤
      q t (action t) + Real.sqrt (2 * Real.log (t + 1 : ℕ) /
        (pullCount action (action t) t : ℝ)) - lambda * cost t (action t))
    (hGapLower : ∀ t ∈ times, delta ≤
      net (mu (best t)) (cost t (best t)) lambda -
        net (mu (action t)) (cost t (action t)) lambda)
    (hGapUpper : ∀ t ∈ times,
      net (mu (best t)) (cost t (best t)) lambda -
        net (mu (action t)) (cost t (action t)) lambda ≤ maxGap) :
    (∑ t ∈ times, (net (mu (best t)) (cost t (best t)) lambda -
      net (mu (action t)) (cost t (action t)) lambda)) ≤
    (arms.card : ℝ) * maxGap * (8 * Real.log (horizon : ℝ) / delta ^ 2 + 1) := by
  let gap : ℕ → ℝ := fun t ↦ net (mu (best t)) (cost t (best t)) lambda -
    net (mu (action t)) (cost t (action t)) lambda
  have hPerArm (arm : Arm) :
      (∑ t ∈ times.filter (fun t ↦ action t = arm), gap t) ≤
      maxGap * (8 * Real.log (horizon : ℝ) / delta ^ 2 + 1) := by
    apply good_arm_regret_bound action arm _ gap
      (fun t ↦ Real.sqrt (2 * Real.log (t + 1 : ℕ) / (pullCount action arm t : ℝ)))
      hDelta hMaxGap (Real.log_nonneg (by exact_mod_cast hHorizon))
    · intro t ht
      exact (Finset.mem_filter.mp ht).2
    · intro t ht
      exact hGapLower t (Finset.mem_filter.mp ht).1
    · intro t ht
      exact hGapUpper t (Finset.mem_filter.mp ht).1
    · intro t _
      exact Real.sqrt_nonneg _
    · intro t ht
      rcases Finset.mem_filter.mp ht with ⟨ht, ha⟩
      have h := chosen_gap_le_two_radius (hBest t ht) (hChosen t ht) (hSelect t ht)
      simpa only [gap, ha] using h
    · intro t ht
      rcases Finset.mem_filter.mp ht with ⟨ht, ha⟩
      apply radius_at_horizon action arm (hTime t ht)
      simpa only [ha] using hCount t ht
  have hPartition : (∑ arm ∈ arms, ∑ t ∈ times.filter (fun t ↦ action t = arm),
      gap t) = ∑ t ∈ times, gap t := by
    simp_rw [Finset.sum_filter]
    rw [Finset.sum_comm]
    apply Finset.sum_congr rfl
    intro t ht
    simp [hIn t ht]
  change (∑ t ∈ times, gap t) ≤ _
  rw [← hPartition]
  calc
    _ ≤ ∑ _arm ∈ arms, maxGap * (8 * Real.log (horizon : ℝ) / delta ^ 2 + 1) :=
      Finset.sum_le_sum (fun arm _ ↦ hPerArm arm)
    _ = _ := by simp [mul_assoc]

end Counts

/-- A finite probability-space bridge: pathwise regret plus expected failure count.
No concentration inequality is encoded as an axiom; the failure estimate is an explicit input. -/
theorem expected_regret_from_pathwise {Outcome : Type*}
    (outcomes : Finset Outcome) (weight regret badCount : Outcome → ℝ)
    {goodBound maxGap badExpectation : ℝ}
    (hWeight : ∀ w ∈ outcomes, 0 ≤ weight w)
    (hMass : (∑ w ∈ outcomes, weight w) = 1)
    (hGap : 0 ≤ maxGap)
    (hPathwise : ∀ w ∈ outcomes, regret w ≤ goodBound + maxGap * badCount w)
    (hBad : (∑ w ∈ outcomes, weight w * badCount w) ≤ badExpectation) :
    (∑ w ∈ outcomes, weight w * regret w) ≤ goodBound + maxGap * badExpectation := by
  calc
    _ ≤ ∑ w ∈ outcomes, weight w * (goodBound + maxGap * badCount w) :=
      Finset.sum_le_sum (fun w hw ↦ mul_le_mul_of_nonneg_left (hPathwise w hw)
        (hWeight w hw))
    _ = goodBound + maxGap * (∑ w ∈ outcomes, weight w * badCount w) := by
      simp_rw [mul_add, Finset.sum_add_distrib]
      rw [← Finset.sum_mul, hMass, one_mul]
      congr 1
      rw [Finset.mul_sum]
      apply Finset.sum_congr rfl
      intro w _
      ring
    _ ≤ goodBound + maxGap * badExpectation :=
      add_le_add_left (mul_le_mul_of_nonneg_left hBad hGap) _

/-- Formal counterexample: current-cost rebasing differs from averaging historical net rewards. -/
theorem historical_cost_average_is_not_current_cost :
    ((net (4 / 5 : ℝ) 1 1 + net (4 / 5) 0 1) / 2) ≠ net (4 / 5) 0 1 := by
  norm_num [net]

/-- Formal counterexample: a biased cost estimate reverses a strictly better net-value arm. -/
theorem biased_cost_reverses_ranking :
    net (4 / 5 : ℝ) (1 / 10) 1 > net (7 / 10) (1 / 10) 1 ∧
    net (4 / 5 : ℝ) (4 / 10) 1 < net (7 / 10) (1 / 10) 1 := by
  norm_num [net]

/-- A cache investment can beat a zero-cost myopic choice over a sufficiently long horizon. -/
theorem cache_investment_beats_myopic {horizon : ℝ} (h : 5 / 2 < horizon) :
    horizon * (3 / 5) < horizon - 1 := by
  linarith

#print axioms index_is_shifted_ucb
#print axioms chosen_gap_le_two_radius
#print axioms plugin_gap_bound
#print axioms optimistic_cost_gap_bound
#print axioms bipartite_expectation
#print axioms good_arm_regret_bound
#print axioms stationary_good_regret_bound
#print axioms dynamic_local_good_regret
#print axioms expected_regret_from_pathwise
#print axioms biased_cost_reverses_ranking

end AgentUCT
