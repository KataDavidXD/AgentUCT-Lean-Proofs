import Mathlib.Analysis.SpecialFunctions.Log.Basic
import Mathlib.Data.Real.Sqrt
import Mathlib.Algebra.Order.Floor.Semiring
import Mathlib.Tactic
import Mathlib.Probability.Moments.SubGaussian
import Mathlib.MeasureTheory.Measure.Real
import Mathlib.MeasureTheory.Function.ConditionalExpectation.Basic
import Mathlib.Data.Finset.Option

/-!
# AgentUCT: complete formal proofs, English reading edition

All mathematical declarations and proof bodies from the project's 45 source
modules follow in dependency order. The only edits are import consolidation,
file-local section boundaries, and translation of explanatory comments.
Canonical edits belong in AgentUCT.lean and AgentUCTPaper/*.lean; regenerate
this reading edition with theory/scripts/build_english_proof_bundle.py.

Read AgentUCTProofGuideEN.lean first for assumptions, conclusions, and open
questions. Each SOURCE banner below identifies the original editable module.
This edition imports Mathlib only. Import this edition OR AgentUCTPaper in
a downstream module: they define the same public project declarations.
Compiler verification establishes the stated conditional mathematics; the
guide records which empirical and implementation guarantees remain open.
-/

/-!
## SOURCE 01: AgentUCT.lean
Original definitions, theorem statements, and complete proof bodies.
-/
section CompleteProofSource01

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
end
end CompleteProofSource01

/-!
## SOURCE 02: AgentUCTPaper/Cache.lean
Original definitions, theorem statements, and complete proof bodies.
-/
section CompleteProofSource02

/-! # Exact accounting for persistent qid-prefix materialization

A resource can be a qid-prefix pair with any additional execution-identity fields.
The cache is a finite set of materialized resources.  These results concern the
fixed physical cost attached to each resource, not a changing cost forecast.
-/

noncomputable section

open Finset

namespace AgentUCTPaper

variable {Resource : Type*} [DecidableEq Resource]

/-- Total physical work represented by a set of materialized resources. -/
def cacheWeight (weight : Resource → ℝ) (cached : Finset Resource) : ℝ :=
  ∑ resource ∈ cached, weight resource

/-- Work needed to materialize the demanded resources absent from the cache. -/
def coldWork (weight : Resource → ℝ) (cached demand : Finset Resource) : ℝ :=
  ∑ resource ∈ demand \ cached, weight resource

/-- Materializing a union adds exactly the work of its previously absent resources. -/
theorem cache_union_accounting (weight : Resource → ℝ) (cached demand : Finset Resource) :
    cacheWeight weight (cached ∪ demand) =
      cacheWeight weight cached + coldWork weight cached demand := by
  unfold cacheWeight coldWork
  have hdisj : Disjoint cached (demand \ cached) := by
    exact disjoint_left.mpr fun _ hcached hcold => (mem_sdiff.mp hcold).2 hcached
  have hunion : cached ∪ demand = cached ∪ (demand \ cached) := by
    ext resource
    simp only [mem_union, mem_sdiff]
    tauto
  rw [hunion, sum_union hdisj]

/-- Replaying a demand already represented by materialized resources incurs no cold work.
This says nothing about fresh per-evaluation search or scoring overhead. -/
theorem cached_demand_is_free (weight : Resource → ℝ) (cached demand : Finset Resource)
    (halready : demand ⊆ cached) : coldWork weight cached demand = 0 := by
  simp [coldWork, sdiff_eq_empty_iff_subset.mpr halready]

omit [DecidableEq Resource] in
/-- Nonnegative resource weights make cache weight monotone under inclusion. -/
theorem cacheWeight_mono (weight : Resource → ℝ) (hnonneg : ∀ resource, 0 ≤ weight resource)
    {cached larger : Finset Resource} (hsub : cached ⊆ larger) :
    cacheWeight weight cached ≤ cacheWeight weight larger := by
  exact sum_le_sum_of_subset_of_nonneg hsub (fun resource _ _ => hnonneg resource)

/-- The incremental work is nonnegative when physical resource costs are nonnegative. -/
theorem coldWork_nonnegative (weight : Resource → ℝ)
    (hnonneg : ∀ resource, 0 ≤ weight resource) (cached demand : Finset Resource) :
    0 ≤ coldWork weight cached demand := by
  exact sum_nonneg fun resource _ => hnonneg resource

/-- A cache cannot increase the physical work for a fixed demand. -/
theorem coldWork_le_fullWork (weight : Resource → ℝ)
    (hnonneg : ∀ resource, 0 ≤ weight resource) (cached demand : Finset Resource) :
    coldWork weight cached demand ≤ cacheWeight weight demand := by
  exact sum_le_sum_of_subset_of_nonneg sdiff_subset (fun resource _ _ => hnonneg resource)

/-- Pathwise conservation of successful materialization work. The transition assumes
persistence, no eviction, and that every newly demanded resource is materialized.
It allows arbitrary adaptive demands and needs no stochastic independence. -/
theorem cumulative_coldWork_eq (weight : Resource → ℝ)
    (cached demand : ℕ → Finset Resource)
    (hstep : ∀ t, cached (t + 1) = cached t ∪ demand t) (horizon : ℕ) :
    (∑ t ∈ range horizon, coldWork weight (cached t) (demand t)) =
      cacheWeight weight (cached horizon) - cacheWeight weight (cached 0) := by
  induction horizon with
  | zero => simp
  | succ horizon ih =>
    rw [sum_range_succ, ih, hstep, cache_union_accounting]
    ring

/-- A finite materializable resource universe bounds all cold work, independent of
how many evaluations replay already materialized qid-prefix resources. -/
theorem cumulative_coldWork_le_universe (weight : Resource → ℝ)
    (hnonneg : ∀ resource, 0 ≤ weight resource)
    (cached demand : ℕ → Finset Resource)
    (hstep : ∀ t, cached (t + 1) = cached t ∪ demand t)
    (horizon : ℕ) (resourceSet : Finset Resource) (hfinite : cached horizon ⊆ resourceSet) :
    (∑ t ∈ range horizon, coldWork weight (cached t) (demand t)) ≤
      cacheWeight weight resourceSet - cacheWeight weight (cached 0) := by
  rw [cumulative_coldWork_eq weight cached demand hstep horizon]
  exact sub_le_sub_right (cacheWeight_mono weight hnonneg hfinite) _

/-- Unshared per-evaluation overhead is charged at every evaluation. Cache conservation
applies only to the materialized-resource portion of total search cost. -/
theorem total_search_cost_accounting (weight : Resource → ℝ)
    (cached demand : ℕ → Finset Resource) (overhead : ℕ → ℝ)
    (hstep : ∀ t, cached (t + 1) = cached t ∪ demand t) (horizon : ℕ) :
    (∑ t ∈ range horizon, (coldWork weight (cached t) (demand t) + overhead t)) =
      cacheWeight weight (cached horizon) - cacheWeight weight (cached 0) +
        ∑ t ∈ range horizon, overhead t := by
  rw [sum_add_distrib, cumulative_coldWork_eq weight cached demand hstep horizon]

omit [DecidableEq Resource] in
/-- Per-resource forecast errors propagate through nonnegative execution probabilities.
Use the cold qid-prefix resources as `resources`; `inclusion` gives the marginal
probability that the completion evaluates each resource.  These probabilities need
not sum to one, and dependencies among resource demands require no extra assumption. -/
theorem weighted_resource_forecast_error (resources : Finset Resource)
    (inclusion predicted actual radius : Resource → ℝ)
    (hprob : ∀ resource ∈ resources, 0 ≤ inclusion resource)
    (herror : ∀ resource ∈ resources, |predicted resource - actual resource| ≤ radius resource) :
    |(∑ resource ∈ resources, inclusion resource * predicted resource) -
        ∑ resource ∈ resources, inclusion resource * actual resource| ≤
      ∑ resource ∈ resources, inclusion resource * radius resource := by
  rw [← sum_sub_distrib]
  calc
    |∑ resource ∈ resources,
        (inclusion resource * predicted resource - inclusion resource * actual resource)| ≤
        ∑ resource ∈ resources,
          |inclusion resource * predicted resource - inclusion resource * actual resource| :=
      abs_sum_le_sum_abs _ _
    _ = ∑ resource ∈ resources,
        inclusion resource * |predicted resource - actual resource| := by
      apply sum_congr rfl
      intro resource hresource
      rw [← mul_sub, abs_mul, abs_of_nonneg (hprob resource hresource)]
    _ ≤ ∑ resource ∈ resources, inclusion resource * radius resource := by
      exact sum_le_sum fun resource hresource =>
        mul_le_mul_of_nonneg_left (herror resource hresource) (hprob resource hresource)

omit [DecidableEq Resource] in
/-- The uncertainty radius of future evaluation overhead adds to the resource radius.
This is a deterministic coverage statement; calibration of all input error bounds
is a separate statistical obligation. -/
theorem total_search_cost_forecast_error (resources : Finset Resource)
    (inclusion predicted actual radius : Resource → ℝ)
    (predictedOverhead actualOverhead overheadRadius : ℝ)
    (hprob : ∀ resource ∈ resources, 0 ≤ inclusion resource)
    (herror : ∀ resource ∈ resources, |predicted resource - actual resource| ≤ radius resource)
    (hoverhead : |predictedOverhead - actualOverhead| ≤ overheadRadius) :
    |((∑ resource ∈ resources, inclusion resource * predicted resource) + predictedOverhead) -
        ((∑ resource ∈ resources, inclusion resource * actual resource) + actualOverhead)| ≤
      (∑ resource ∈ resources, inclusion resource * radius resource) + overheadRadius := by
  have hsplit :
      ((∑ resource ∈ resources, inclusion resource * predicted resource) + predictedOverhead) -
          ((∑ resource ∈ resources, inclusion resource * actual resource) + actualOverhead) =
        ((∑ resource ∈ resources, inclusion resource * predicted resource) -
          ∑ resource ∈ resources, inclusion resource * actual resource) +
            (predictedOverhead - actualOverhead) := by ring
  rw [hsplit]
  exact (abs_add_le _ _).trans
    (add_le_add
      (weighted_resource_forecast_error resources inclusion predicted actual radius hprob herror)
      hoverhead)

end AgentUCTPaper
end
end CompleteProofSource02

/-!
## SOURCE 03: AgentUCTPaper/CostModel.lean
Original definitions, theorem statements, and complete proof bodies.
-/
section CompleteProofSource03

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
end
end CompleteProofSource03

/-!
## SOURCE 04: AgentUCTPaper/FiniteModel.lean
Original definitions, theorem statements, and complete proof bodies.
-/
section CompleteProofSource04

/-! Finite cache-state models have a positive separation for every nonzero gap.
This is an instance-dependent separation; no uniform numerical lower bound is asserted. -/

noncomputable section
open Finset
namespace AgentUCTPaper

theorem finite_positive_gap (values : Finset ℝ) :
    ∃ delta : ℝ, 0 < delta ∧ ∀ g ∈ values, 0 < g → delta ≤ g := by
  classical
  induction values using Finset.induction_on with
  | empty => exact ⟨1, by norm_num, by simp⟩
  | @insert a s ha ih =>
    obtain ⟨delta, hd, hb⟩ := ih
    by_cases hp : 0 < a
    · refine ⟨min a delta, lt_min hp hd, ?_⟩
      intro g hg hgp
      rcases Finset.mem_insert.mp hg with hga | hgs
      · subst g
        exact min_le_left a delta
      · exact (min_le_right a delta).trans (hb g hgs hgp)
    · refine ⟨delta, hd, ?_⟩
      intro g hg hgp
      rcases Finset.mem_insert.mp hg with hga | hgs
      · exact (hp (hga ▸ hgp)).elim
      · exact hb g hgs hgp

/-- Apply `State = Finset Resource` for a finite qid-prefix materialization universe.
The net values must be fixed functions of this state: changing forecasters or
rollout distributions introduce further state and do not satisfy that model automatically. -/
theorem finite_state_gap_separation {State Arm : Type*} [Fintype State] [Fintype Arm]
    (value : State → Arm → ℝ) :
    ∃ delta : ℝ, 0 < delta ∧ ∀ s a b,
      0 < value s a - value s b → delta ≤ value s a - value s b := by
  classical
  let gaps := (Finset.univ : Finset (State × Arm × Arm)).image
    (fun x ↦ value x.1 x.2.1 - value x.1 x.2.2)
  obtain ⟨delta, hd, hb⟩ := finite_positive_gap gaps
  refine ⟨delta, hd, ?_⟩
  intro s a b hp
  apply hb _ _ hp
  exact Finset.mem_image.mpr ⟨(s, a, b), Finset.mem_univ _, rfl⟩

/-- Clipping a common baseline is not generally a common shift. Deep checkpoints
can make complete-path cold cost smaller than an uncached partial-prefix baseline. -/
theorem clipped_baseline_can_reverse_order :
    ((4 / 10 : ℝ) - 2 / 10 > 8 / 10 - 8 / 10) ∧
      ((4 / 10 : ℝ) - max 0 (2 / 10 - 1) < 8 / 10 - max 0 (8 / 10 - 1)) := by
  norm_num

end AgentUCTPaper
end
end CompleteProofSource04

/-!
## SOURCE 05: AgentUCTPaper/Probability.lean
Original definitions, theorem statements, and complete proof bodies.
-/
section CompleteProofSource05

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
end
end CompleteProofSource05

/-!
## SOURCE 06: AgentUCTPaper/Regret.lean
Original definitions, theorem statements, and complete proof bodies.
-/
section CompleteProofSource06

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
end
end CompleteProofSource06

/-!
## SOURCE 07: AgentUCTPaper/Expected.lean
Original definitions, theorem statements, and complete proof bodies.
-/
section CompleteProofSource07

/-! # Expected regret derived from reward concentration

This file composes the all-round deterministic bound with the independently
proved concentration and union bounds. No successful confidence event is an
assumption. Costs may be arbitrary functions of the outcome and local time.
-/

noncomputable section

open MeasureTheory ProbabilityTheory Finset
open scoped NNReal

namespace AgentUCTPaper

variable {Ω Arm : Type*} [MeasurableSpace Ω] {P : Measure Ω}
  [IsProbabilityMeasure P] [Fintype Arm] [DecidableEq Arm]

omit [Fintype Arm] in
theorem pullCount_le_time (action : ℕ → Arm) (arm : Arm) (t : ℕ) :
    AgentUCT.pullCount action arm t ≤ t := by
  unfold AgentUCT.pullCount
  have h := Finset.card_le_card (Finset.filter_subset
    (s := Finset.range t) (p := fun s ↦ action s = arm))
  simpa only [Finset.card_range] using h

omit [MeasurableSpace Ω] in
/-- Confidence at an adaptively chosen count is derived by a union over all
possible counts, with no independence requirement on the random count itself. -/
theorem sample_mean_confidence
    (S : Arm → ℕ → Ω → ℝ) (action : Ω → ℕ → Arm)
    (mu : Arm → ℝ) (q : Ω → ℕ → Arm → ℝ)
    {ω : Ω} {t : ℕ} {arm : Arm}
    (hCount : 0 < AgentUCT.pullCount (action ω) arm t)
    (hQ : q ω t arm = mu arm +
      S arm (AgentUCT.pullCount (action ω) arm t) ω /
        (AgentUCT.pullCount (action ω) arm t : ℝ))
    (hGood : ω ∉ badAt Finset.univ S t) :
    |q ω t arm - mu arm| ≤ localRadius (action ω) arm t := by
  rw [hQ]
  simp only [add_sub_cancel_left]
  exact not_badAt_error Finset.univ S (Finset.mem_univ arm) hCount
    (pullCount_le_time (action ω) arm t) hGood

/-- A complete expected bound for a local node and the same-cache comparator.
The centered-sum MGF assumption is constructed from independent [0,1] reward
streams in `Probability.lean`. The estimator identity links those streams to Q.
All arms have at least one observation after the initialization period.
-/
theorem expected_local_regret
    (S : Arm → ℕ → Ω → ℝ) (action best : Ω → ℕ → Arm)
    (mu : Arm → ℝ) (q cost : Ω → ℕ → Arm → ℝ) (lambda : ℝ)
    {T : ℕ} {delta D : ℝ}
    (hT : 1 ≤ T) (hDelta : 0 < delta) (hD : 0 ≤ D)
    (hMeas : ∀ a n, Measurable (S a n))
    (hMGF : ∀ a n, 0 < n → HasSubgaussianMGF (S a n) ((n : ℝ≥0) / 4) P)
    (hQ : ∀ ω t, t < T → Fintype.card Arm ≤ t → ∀ a,
      q ω t a = mu a + S a (AgentUCT.pullCount (action ω) a t) ω /
        (AgentUCT.pullCount (action ω) a t : ℝ))
    (hCount : ∀ ω t, t < T → Fintype.card Arm ≤ t → ∀ a,
      0 < AgentUCT.pullCount (action ω) a t)
    (hGapNonneg : ∀ ω t, t < T →
      0 ≤ localGap mu (cost ω) lambda (action ω) (best ω) t)
    (hGapUpper : ∀ ω t, t < T →
      localGap mu (cost ω) lambda (action ω) (best ω) t ≤ D)
    (hSeparated : ∀ ω t, t < T →
      0 < localGap mu (cost ω) lambda (action ω) (best ω) t →
      delta ≤ localGap mu (cost ω) lambda (action ω) (best ω) t)
    (hSelect : ∀ ω t, t < T → Fintype.card Arm ≤ t →
      q ω t (best ω t) + localRadius (action ω) (best ω t) t -
        lambda * cost ω t (best ω t) ≤
      q ω t (action ω t) + localRadius (action ω) (action ω t) t -
        lambda * cost ω t (action ω t))
    (hIntegrable : Integrable (fun ω ↦ ∑ t ∈ Finset.range T,
      localGap mu (cost ω) lambda (action ω) (best ω) t) P) :
    (∫ ω, (∑ t ∈ Finset.range T,
      localGap mu (cost ω) lambda (action ω) (best ω) t) ∂P) ≤
      (Fintype.card Arm : ℝ) * D * (8 * Real.log (T : ℝ) / delta ^ 2 + 6) := by
  classical
  let B := (Fintype.card Arm : ℝ) * D * (8 * Real.log (T : ℝ) / delta ^ 2 + 2)
  have hPath (ω : Ω) : (∑ t ∈ Finset.range T,
      localGap mu (cost ω) lambda (action ω) (best ω) t) ≤
      B + D * badCount Finset.univ S T ω := by
    apply local_regret_all_rounds (action ω) (best ω) mu (q ω) (cost ω) lambda
      (fun t ↦ ω ∈ badAt Finset.univ S t) hT hDelta hD
      (hGapNonneg ω) (hGapUpper ω) (hSeparated ω)
    · intro t ht hk
      exact hCount ω t ht hk (action ω t)
    · intro t ht hk hg
      have hc := sample_mean_confidence S action mu q (hCount ω t ht hk (best ω t))
        (hQ ω t ht hk (best ω t)) hg
      have := (abs_le.mp hc).1
      linarith
    · intro t ht hk hg
      have hc := sample_mean_confidence S action mu q (hCount ω t ht hk (action ω t))
        (hQ ω t ht hk (action ω t)) hg
      have := (abs_le.mp hc).2
      linarith
    · exact hSelect ω
  have hBadInt := badCount_integrable (μ := P) Finset.univ S hMeas T
  have hBInt : Integrable (fun ω ↦ B + D * badCount Finset.univ S T ω) P :=
    (integrable_const B).add (hBadInt.const_mul D)
  have hInt := integral_mono hIntegrable hBInt hPath
  have hBad := expected_badCount (μ := P) Finset.univ S hMeas
    (fun a _ n hn ↦ hMGF a n hn) T
  rw [integral_add (integrable_const B) (hBadInt.const_mul D)] at hInt
  simp only [integral_const_mul, integral_const, measureReal_univ_eq_one, one_smul,
    Finset.card_univ] at hInt hBad
  dsimp only [B] at hInt
  nlinarith

/-- Expected error-budget composition. The probability of a confidence failure
is derived from the centered streams. `hOptimism` is the structural gap inequality
supplied by `drift_plugin_gap_bound`, not an assumed probability bound. -/
theorem expected_regret_with_error_budget
    (S : Arm → ℕ → Ω → ℝ) (action : Ω → ℕ → Arm)
    (gap error : Ω → ℕ → ℝ)
    {T : ℕ} {delta D : ℝ}
    (hT : 1 ≤ T) (hDelta : 0 < delta) (hD : 0 ≤ D)
    (hMeas : ∀ a n, Measurable (S a n))
    (hMGF : ∀ a n, 0 < n → HasSubgaussianMGF (S a n) ((n : ℝ≥0) / 4) P)
    (hGapNonneg : ∀ ω t, t < T → 0 ≤ gap ω t)
    (hGapUpper : ∀ ω t, t < T → gap ω t ≤ D)
    (hErrorNonneg : ∀ ω t, t < T → 0 ≤ error ω t)
    (hSeparated : ∀ ω t, t < T → 0 < gap ω t → delta ≤ gap ω t)
    (hCount : ∀ ω t, t < T → Fintype.card Arm ≤ t →
      0 < AgentUCT.pullCount (action ω) (action ω t) t)
    (hOptimism : ∀ ω t, t < T → Fintype.card Arm ≤ t →
      ω ∉ badAt Finset.univ S t →
      gap ω t ≤ 2 * localRadius (action ω) (action ω t) t + error ω t)
    (hRegretInt : Integrable (fun ω ↦ ∑ t ∈ Finset.range T, gap ω t) P)
    (hErrorInt : Integrable (fun ω ↦ ∑ t ∈ Finset.range T, error ω t) P) :
    (∫ ω, (∑ t ∈ Finset.range T, gap ω t) ∂P) ≤
      (Fintype.card Arm : ℝ) * D * (32 * Real.log (T : ℝ) / delta ^ 2 + 6) +
      2 * (∫ ω, (∑ t ∈ Finset.range T, error ω t) ∂P) := by
  classical
  let B := (Fintype.card Arm : ℝ) * D * (32 * Real.log (T : ℝ) / delta ^ 2 + 2)
  have hPath (ω : Ω) : (∑ t ∈ Finset.range T, gap ω t) ≤
      B + 2 * (∑ t ∈ Finset.range T, error ω t) + D * badCount Finset.univ S T ω :=
    local_regret_with_error_budget (action ω) (gap ω) (error ω)
      (fun t ↦ ω ∈ badAt Finset.univ S t) hT hDelta hD
      (hGapNonneg ω) (hGapUpper ω) (hErrorNonneg ω) (hSeparated ω)
      (hCount ω) (hOptimism ω)
  have hBadInt := badCount_integrable (μ := P) Finset.univ S hMeas T
  have hBaseInt : Integrable (fun ω ↦ B + 2 * ∑ t ∈ Finset.range T, error ω t) P :=
    (integrable_const B).add (hErrorInt.const_mul 2)
  have hInt := integral_mono hRegretInt (hBaseInt.add (hBadInt.const_mul D)) hPath
  change (∫ ω, (∑ t ∈ Finset.range T, gap ω t) ∂P) ≤
    (∫ ω, (B + 2 * (∑ t ∈ Finset.range T, error ω t) +
      D * badCount Finset.univ S T ω) ∂P) at hInt
  have hBad := expected_badCount (μ := P) Finset.univ S hMeas
    (fun a _ n hn ↦ hMGF a n hn) T
  rw [integral_add hBaseInt (hBadInt.const_mul D),
    integral_add (integrable_const B) (hErrorInt.const_mul 2)] at hInt
  simp only [integral_const_mul, integral_const, measureReal_univ_eq_one, one_smul,
    Finset.card_univ, B] at hInt hBad
  nlinarith

/-- Current value gaps allow the comparator's reward value to change with search. -/
def currentGap (current cost : Ω → ℕ → Arm → ℝ) (lambda : ℝ)
    (action best : Ω → ℕ → Arm) (ω : Ω) (t : ℕ) : ℝ :=
  AgentUCT.net (current ω t (best ω t)) (cost ω t (best ω t)) lambda -
    AgentUCT.net (current ω t (action ω t)) (cost ω t (action ω t)) lambda

/-- Sum of comparator and chosen-action reward drift and cost prediction errors. -/
def currentError (drift costError : Ω → ℕ → Arm → ℝ) (lambda : ℝ)
    (action best : Ω → ℕ → Arm) (ω : Ω) (t : ℕ) : ℝ :=
  drift ω t (best ω t) + drift ω t (action ω t) +
    lambda * (costError ω t (best ω t) + costError ω t (action ω t))

/-- Full expected bound with dynamic reward centers, true current values, and
plug-in predicted costs. Statistical concentration, reward drift, and prediction
error are separate hypotheses. In particular, no stationarity of tree returns
or successful confidence event is smuggled into the regret conclusion. -/
theorem expected_current_regret_with_errors
    (S : Arm → ℕ → Ω → ℝ) (action best : Ω → ℕ → Arm)
    (center current q cost estimate drift costError : Ω → ℕ → Arm → ℝ)
    (lambda : ℝ) {T : ℕ} {delta D : ℝ}
    (hLambda : 0 ≤ lambda)
    (hT : 1 ≤ T) (hDelta : 0 < delta) (hD : 0 ≤ D)
    (hMeas : ∀ a n, Measurable (S a n))
    (hMGF : ∀ a n, 0 < n → HasSubgaussianMGF (S a n) ((n : ℝ≥0) / 4) P)
    (hQ : ∀ ω t, t < T → Fintype.card Arm ≤ t → ∀ a,
      q ω t a = center ω t a + S a (AgentUCT.pullCount (action ω) a t) ω /
        (AgentUCT.pullCount (action ω) a t : ℝ))
    (hCount : ∀ ω t, t < T → Fintype.card Arm ≤ t → ∀ a,
      0 < AgentUCT.pullCount (action ω) a t)
    (hDrift : ∀ ω t, t < T → ∀ a, |current ω t a - center ω t a| ≤ drift ω t a)
    (hCostError : ∀ ω t, t < T → ∀ a, |estimate ω t a - cost ω t a| ≤ costError ω t a)
    (hGapNonneg : ∀ ω t, t < T → 0 ≤ currentGap current cost lambda action best ω t)
    (hGapUpper : ∀ ω t, t < T → currentGap current cost lambda action best ω t ≤ D)
    (hSeparated : ∀ ω t, t < T → 0 < currentGap current cost lambda action best ω t →
      delta ≤ currentGap current cost lambda action best ω t)
    (hSelect : ∀ ω t, t < T → Fintype.card Arm ≤ t →
      q ω t (best ω t) + localRadius (action ω) (best ω t) t -
        lambda * estimate ω t (best ω t) ≤
      q ω t (action ω t) + localRadius (action ω) (action ω t) t -
        lambda * estimate ω t (action ω t))
    (hRegretInt : Integrable (fun ω ↦ ∑ t ∈ Finset.range T,
      currentGap current cost lambda action best ω t) P)
    (hErrorInt : Integrable (fun ω ↦ ∑ t ∈ Finset.range T,
      currentError drift costError lambda action best ω t) P) :
    (∫ ω, (∑ t ∈ Finset.range T, currentGap current cost lambda action best ω t) ∂P) ≤
      (Fintype.card Arm : ℝ) * D * (32 * Real.log (T : ℝ) / delta ^ 2 + 6) +
      2 * (∫ ω, (∑ t ∈ Finset.range T, currentError drift costError lambda action best ω t) ∂P) := by
  apply expected_regret_with_error_budget S action (currentGap current cost lambda action best)
    (currentError drift costError lambda action best) hT hDelta hD hMeas hMGF
    hGapNonneg hGapUpper _ hSeparated _ _ hRegretInt hErrorInt
  · intro ω t ht
    have hd (a : Arm) : 0 ≤ drift ω t a := (abs_nonneg _).trans (hDrift ω t ht a)
    have he (a : Arm) : 0 ≤ costError ω t a := (abs_nonneg _).trans (hCostError ω t ht a)
    exact add_nonneg (add_nonneg (hd _) (hd _))
      (mul_nonneg hLambda (add_nonneg (he _) (he _)))
  · intro ω t ht hk
    exact hCount ω t ht hk (action ω t)
  · intro ω t ht hk hGood
    have hc (a : Arm) : |q ω t a - center ω t a| ≤ localRadius (action ω) a t := by
      rw [hQ ω t ht hk a]
      simp only [add_sub_cancel_left]
      exact not_badAt_error Finset.univ S (Finset.mem_univ a) (hCount ω t ht hk a)
        (pullCount_le_time (action ω) a t) hGood
    have hb := (abs_le.mp (hc (best ω t))).1
    have ha := (abs_le.mp (hc (action ω t))).2
    have hdb := (abs_le.mp (hDrift ω t ht (best ω t))).2
    have hda := (abs_le.mp (hDrift ω t ht (action ω t))).1
    have heb := (abs_le.mp (hCostError ω t ht (best ω t))).2
    have hea := (abs_le.mp (hCostError ω t ht (action ω t))).1
    have h := drift_plugin_gap_bound hLambda (by linarith :
        center ω t (best ω t) ≤ q ω t (best ω t) + localRadius (action ω) (best ω t) t)
      (by linarith : q ω t (action ω t) ≤
        center ω t (action ω t) + localRadius (action ω) (action ω t) t)
      hdb (by linarith : center ω t (action ω t) - current ω t (action ω t) ≤
        drift ω t (action ω t)) heb
      (by linarith : cost ω t (action ω t) - estimate ω t (action ω t) ≤
        costError ω t (action ω t)) (hSelect ω t ht hk)
    simpa only [currentGap, currentError, add_assoc] using h

#print axioms sample_mean_confidence
#print axioms expected_local_regret
#print axioms expected_regret_with_error_budget
#print axioms expected_current_regret_with_errors

end AgentUCTPaper
end
end CompleteProofSource07

/-!
## SOURCE 08: AgentUCTPaper/Counterexample.lean
Original definitions, theorem statements, and complete proof bodies.
-/
section CompleteProofSource08

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
end
end CompleteProofSource08

/-!
## SOURCE 09: AgentUCTPaper/Greedy.lean
Original definitions, theorem statements, and complete proof bodies.
-/
section CompleteProofSource09

/-! # Immediate-cost reduction and omitted-tail error

An immediate-edge penalty is an exact ranking reduction when every action has
the same remaining tail cost. For differing tails, the selected-action gap has
a signed residual determined by chosen tail minus comparator tail.
-/

noncomputable section

namespace AgentUCTPaper

/-- A common tail subtracts the same constant from every action index. -/
theorem common_tail_index_identity (q radius edge tail lambda : ℝ) :
    q + radius - lambda * (edge + tail) =
      (q + radius - lambda * edge) - lambda * tail := by
  ring

/-- Pairwise rankings, including ties, are exactly preserved by a common tail. -/
theorem common_tail_preserves_order
    (qA qB rA rB edgeA edgeB tail lambda : ℝ) :
    (qA + rA - lambda * (edgeA + tail) ≤
      qB + rB - lambda * (edgeB + tail)) ↔
    (qA + rA - lambda * edgeA ≤ qB + rB - lambda * edgeB) := by
  rw [common_tail_index_identity, common_tail_index_identity]
  exact sub_le_sub_iff_right _

/-- Immediate-index maximization is full-index maximization for a common tail. -/
theorem common_tail_argmax_iff {Arm : Type*}
    (q radius edge : Arm → ℝ) (tail lambda : ℝ) (chosen : Arm) :
    (∀ a, q a + radius a - lambda * (edge a + tail) ≤
      q chosen + radius chosen - lambda * (edge chosen + tail)) ↔
    (∀ a, q a + radius a - lambda * edge a ≤
      q chosen + radius chosen - lambda * edge chosen) := by
  apply forall_congr'
  intro a
  exact common_tail_preserves_order _ _ _ _ _ _ _ _

/-- The omitted-tail penalty is signed: only a larger chosen tail hurts this
comparison. This identity-based bound holds for any real cost coefficient. -/
theorem signed_tail_gap_bound
    {muBest muChosen qBest qChosen rBest rChosen
      edgeBest edgeChosen tailBest tailChosen lambda : ℝ}
    (hBest : muBest ≤ qBest + rBest)
    (hChosen : qChosen ≤ muChosen + rChosen)
    (hSelect : qBest + rBest - lambda * edgeBest ≤
      qChosen + rChosen - lambda * edgeChosen) :
    AgentUCT.net muBest (edgeBest + tailBest) lambda -
      AgentUCT.net muChosen (edgeChosen + tailChosen) lambda ≤
      2 * rChosen + lambda * (tailChosen - tailBest) := by
  have h := AgentUCT.chosen_gap_le_two_radius hBest hChosen hSelect
  unfold AgentUCT.net at h ⊢
  linarith

/-- With a nonnegative comparator tail, its subtraction can be dropped to obtain
an upper bound depending only on the chosen action's omitted cost. -/
theorem nonnegative_tail_gap_bound
    {muBest muChosen qBest qChosen rBest rChosen
      edgeBest edgeChosen tailBest tailChosen lambda : ℝ}
    (hLambda : 0 ≤ lambda) (hTailBest : 0 ≤ tailBest)
    (hBest : muBest ≤ qBest + rBest)
    (hChosen : qChosen ≤ muChosen + rChosen)
    (hSelect : qBest + rBest - lambda * edgeBest ≤
      qChosen + rChosen - lambda * edgeChosen) :
    AgentUCT.net muBest (edgeBest + tailBest) lambda -
      AgentUCT.net muChosen (edgeChosen + tailChosen) lambda ≤
      2 * rChosen + lambda * tailChosen := by
  have h := signed_tail_gap_bound (tailBest := tailBest) (tailChosen := tailChosen)
    hBest hChosen hSelect
  have hn := mul_nonneg hLambda hTailBest
  nlinarith

/-- Exact next-edge costs in the omitted-tail counterexample. -/
def nextImmediateCost : Bool → ℝ := biasedCostEstimate

/-- Every evaluation costs 0.4 in total, including its recurring tail. -/
def nextFullCost (_ : Bool) : ℝ := 2 / 5

/-- The second arm has a positive recurring tail that an edge-only index omits. -/
def nextTailCost : Bool → ℝ
  | true => 0
  | false => 3 / 10

theorem next_cost_decomposition (arm : Bool) :
    nextFullCost arm = nextImmediateCost arm + nextTailCost arm := by
  cases arm <;> norm_num [nextFullCost, nextImmediateCost, nextTailCost, biasedCostEstimate]

theorem next_tail_nonnegative (arm : Bool) : 0 ≤ nextTailCost arm := by
  cases arm <;> norm_num [nextTailCost]

/-- True regret compares the deterministic reward minus full recurring cost. -/
def nextFullGap (action : ℕ → Bool) (t : ℕ) : ℝ :=
  localGap biasedReward (fun _ ↦ nextFullCost) 1 action (fun _ ↦ true) t

/-- Raising both true costs by the same amount preserves the true regret gap. -/
theorem next_full_gap_identity (action : ℕ → Bool) (t : ℕ) :
    nextFullGap action t = biasedTrueGap action t := by
  dsimp [nextFullGap, biasedTrueGap, localGap, AgentUCT.net, nextFullCost, biasedTrueCost]
  ring

/-- Even exact next-edge estimates do not guarantee logarithmic regret for full
evaluation costs. With a recurring omitted tail, every initialized greedy-next
UCB trajectory has a linear-minus-log lower bound. No predictor bias is needed.
-/
theorem next_edge_linear_regret
    (action : ℕ → Bool) {T : ℕ} (hT : 1 ≤ T)
    (hInitA : action 0 = true) (hInitB : action 1 = false)
    (hSelect : ∀ t < T, 2 ≤ t → ∀ arm : Bool,
      biasedReward arm + localRadius action arm t - nextImmediateCost arm ≤
      biasedReward (action t) + localRadius action (action t) t -
        nextImmediateCost (action t)) :
    (T : ℝ) / 10 - 40 * Real.log (T : ℝ) - 2 / 5 ≤
      ∑ t ∈ Finset.range T, nextFullGap action t := by
  simp_rw [next_full_gap_identity]
  exact biased_cost_linear_regret action hT hInitA hInitB hSelect

#print axioms common_tail_index_identity
#print axioms common_tail_preserves_order
#print axioms common_tail_argmax_iff
#print axioms signed_tail_gap_bound
#print axioms nonnegative_tail_gap_bound
#print axioms next_cost_decomposition
#print axioms next_tail_nonnegative
#print axioms next_full_gap_identity
#print axioms next_edge_linear_regret

end AgentUCTPaper
end
end CompleteProofSource09

/-!
## SOURCE 10: AgentUCTPaper/CacheExpectation.lean
Original definitions, theorem statements, and complete proof bodies.
-/
section CompleteProofSource10

/-! # Expected cold-cost forecasts inherit the persistent-cache budget

The pathwise bound comes from actual successful materialization, not an assumed
bound on forecasts. The expectation step uses genuine conditional expectation.
Conditioning sigma-fields should contain the decision whose cost is forecast;
the algebra needs only that they are sub-sigma-fields of the ambient space.
-/

noncomputable section

open Finset MeasureTheory

namespace AgentUCTPaper

variable {Resource Ω : Type*} [DecidableEq Resource]

/-- Omitted actual cold work is charged against the same persistent materialization
ledger. It cannot exceed the weight of all newly materialized resources. -/
theorem omitted_cold_sum_bounds (weight : Resource → ℝ)
    (hnonneg : ∀ resource, 0 ≤ weight resource)
    (cached demand : Ω → ℕ → Finset Resource) (initial resourceSet : Finset Resource)
    (horizon : ℕ)
    (hinitial : ∀ ω, cached ω 0 = initial)
    (hstep : ∀ ω t, cached ω (t + 1) = cached ω t ∪ demand ω t)
    (hfinite : ∀ ω, cached ω horizon ⊆ resourceSet)
    (actual : Ω → ℕ → ℝ)
    (hactual : ∀ ω t, t ∈ range horizon →
      0 ≤ actual ω t ∧ actual ω t ≤ coldWork weight (cached ω t) (demand ω t))
    (ω : Ω) :
    0 ≤ ∑ t ∈ range horizon, actual ω t ∧
      (∑ t ∈ range horizon, actual ω t) ≤
        cacheWeight weight resourceSet - cacheWeight weight initial := by
  constructor
  · exact sum_nonneg fun t ht => (hactual ω t ht).1
  · calc
      (∑ t ∈ range horizon, actual ω t) ≤
          ∑ t ∈ range horizon, coldWork weight (cached ω t) (demand ω t) :=
        sum_le_sum fun t ht => (hactual ω t ht).2
      _ ≤ cacheWeight weight resourceSet - cacheWeight weight initial := by
        simpa only [hinitial ω] using cumulative_coldWork_le_universe weight hnonneg
          (cached ω) (demand ω) (hstep ω) horizon resourceSet (hfinite ω)

variable [mΩ : MeasurableSpace Ω]

/-- Integrating the actual pathwise materialization bound gives the expected budget.
Integrability is an explicit interface; no measurability of the random ledger is
silently inferred from its finite-set representation. -/
theorem expected_omitted_cold_budget (P : Measure Ω) [IsProbabilityMeasure P]
    (weight : Resource → ℝ) (hnonneg : ∀ resource, 0 ≤ weight resource)
    (cached demand : Ω → ℕ → Finset Resource) (initial resourceSet : Finset Resource)
    (horizon : ℕ)
    (hinitial : ∀ ω, cached ω 0 = initial)
    (hstep : ∀ ω t, cached ω (t + 1) = cached ω t ∪ demand ω t)
    (hfinite : ∀ ω, cached ω horizon ⊆ resourceSet)
    (actual : Ω → ℕ → ℝ)
    (hactual : ∀ ω t, t ∈ range horizon →
      0 ≤ actual ω t ∧ actual ω t ≤ coldWork weight (cached ω t) (demand ω t))
    (hintegrable : Integrable (fun ω => ∑ t ∈ range horizon, actual ω t) P) :
    (∫ ω, ∑ t ∈ range horizon, actual ω t ∂P) ≤
      cacheWeight weight resourceSet - cacheWeight weight initial := by
  calc
    (∫ ω, ∑ t ∈ range horizon, actual ω t ∂P) ≤
        ∫ _, (cacheWeight weight resourceSet - cacheWeight weight initial) ∂P :=
      integral_mono_ae hintegrable (integrable_const _) (Filter.Eventually.of_forall
        fun ω => (omitted_cold_sum_bounds weight hnonneg cached demand initial resourceSet
          horizon hinitial hstep hfinite actual hactual ω).2)
    _ = cacheWeight weight resourceSet - cacheWeight weight initial := by simp

omit [DecidableEq Resource] in
/-- The conditional expectation of the selected actual cold bill. Its conditioning
information is supplied explicitly and can include the already chosen action. -/
def conditionalColdForecast (P : Measure Ω) (info : ℕ → MeasurableSpace Ω)
    (actual : Ω → ℕ → ℝ) (ω : Ω) (t : ℕ) : ℝ :=
  (P[fun x => actual x t | info t]) ω

omit [DecidableEq Resource] in
/-- Every finite sum of canonical conditional-expectation forecasts is integrable. -/
theorem integrable_conditionalColdForecast_sum (P : Measure Ω)
    (info : ℕ → MeasurableSpace Ω) (actual : Ω → ℕ → ℝ) (horizon : ℕ) :
    Integrable (fun ω => ∑ t ∈ range horizon,
      conditionalColdForecast P info actual ω t) P := by
  exact integrable_finset_sum _ fun _ _ => integrable_condExp

omit [DecidableEq Resource] in
/-- Conditional unbiasedness conserves total expected cost. This is proved from
`integral_condExp`, not supplied as a hypothesis on the cumulative forecasts. -/
theorem integral_forecast_sum_eq_actual (P : Measure Ω) [IsProbabilityMeasure P]
    (info : ℕ → MeasurableSpace Ω) (hinfo : ∀ t, info t ≤ mΩ)
    (actual forecast : Ω → ℕ → ℝ) (horizon : ℕ)
    (hintegrable : ∀ t ∈ range horizon, Integrable (fun ω => actual ω t) P)
    (hforecast : ∀ t ∈ range horizon,
      (fun ω => forecast ω t) =ᵐ[P] (fun ω => conditionalColdForecast P info actual ω t)) :
    (∫ ω, ∑ t ∈ range horizon, forecast ω t ∂P) =
      ∫ ω, ∑ t ∈ range horizon, actual ω t ∂P := by
  have hforecastInt : ∀ t ∈ range horizon, Integrable (fun ω => forecast ω t) P := by
    intro t ht
    exact integrable_condExp.congr (hforecast t ht).symm
  rw [integral_finset_sum _ hforecastInt, integral_finset_sum _ hintegrable]
  apply sum_congr rfl
  intro t ht
  calc
    (∫ ω, forecast ω t ∂P) = ∫ ω, conditionalColdForecast P info actual ω t ∂P :=
      integral_congr_ae (hforecast t ht)
    _ = ∫ ω, actual ω t ∂P := integral_condExp (hinfo t)

/-- The finite qid-prefix materialization budget also bounds the expected sum of
conditionally unbiased omitted-cold-cost forecasts, even for adaptive cache demands.
Only the actual cold component is covered; repeatedly incurred overhead is separate. -/
theorem expected_forecast_cold_budget (P : Measure Ω) [IsProbabilityMeasure P]
    (weight : Resource → ℝ) (hnonneg : ∀ resource, 0 ≤ weight resource)
    (cached demand : Ω → ℕ → Finset Resource) (initial resourceSet : Finset Resource)
    (horizon : ℕ)
    (hinitial : ∀ ω, cached ω 0 = initial)
    (hstep : ∀ ω t, cached ω (t + 1) = cached ω t ∪ demand ω t)
    (hfinite : ∀ ω, cached ω horizon ⊆ resourceSet)
    (actual forecast : Ω → ℕ → ℝ)
    (hactual : ∀ ω t, t ∈ range horizon →
      0 ≤ actual ω t ∧ actual ω t ≤ coldWork weight (cached ω t) (demand ω t))
    (hintegrable : ∀ t ∈ range horizon, Integrable (fun ω => actual ω t) P)
    (info : ℕ → MeasurableSpace Ω) (hinfo : ∀ t, info t ≤ mΩ)
    (hforecast : ∀ t ∈ range horizon,
      (fun ω => forecast ω t) =ᵐ[P] (fun ω => conditionalColdForecast P info actual ω t)) :
    (∫ ω, ∑ t ∈ range horizon, forecast ω t ∂P) ≤
      cacheWeight weight resourceSet - cacheWeight weight initial := by
  rw [integral_forecast_sum_eq_actual P info hinfo actual forecast horizon hintegrable hforecast]
  exact expected_omitted_cold_budget P weight hnonneg cached demand initial resourceSet horizon
    hinitial hstep hfinite actual hactual (integrable_finset_sum _ hintegrable)

end AgentUCTPaper
end
end CompleteProofSource10

/-!
## SOURCE 11: AgentUCTPaper/GreedyExpected.lean
Original definitions, theorem statements, and complete proof bodies.
-/
section CompleteProofSource11

/-! # Expected full-cost regret of next-edge UCB

Only the chosen omitted cost is charged. This one-sided comparison allows
persistent cache accounting to bound the approximation term later.
-/

noncomputable section

open MeasureTheory ProbabilityTheory Finset
open scoped NNReal

namespace AgentUCTPaper

/-- The implemented clipped difference is zero when the child checkpoint is
already present and the parent's missing-cost baseline is nonnegative. -/
theorem cached_child_next_penalty_zero {baseline : ℝ} (h : 0 ≤ baseline) :
    max 0 (0 - baseline) = 0 := by
  exact max_eq_left (by linarith)

/-- If every candidate's next-edge penalty is zero, selection is ordinary UCB,
including its entire set of tied maximizers. -/
theorem zero_next_penalty_recovers_ucb {Arm : Type*}
    (q radius edge : Arm → ℝ) (lambda : ℝ) (chosen : Arm)
    (hZero : ∀ a, edge a = 0) :
    (∀ a, q a + radius a - lambda * edge a ≤
      q chosen + radius chosen - lambda * edge chosen) ↔
    (∀ a, q a + radius a ≤ q chosen + radius chosen) := by
  simp only [hZero, mul_zero, sub_zero]

variable {Ω Arm : Type*} [MeasurableSpace Ω] {P : Measure Ω}
  [IsProbabilityMeasure P] [Fintype Arm] [DecidableEq Arm]

/-- The next-edge rule has a full-cost expected regret bound with a one-sided
omitted-tail budget, rather than a sum of both arms' absolute cost errors. -/
theorem expected_next_edge_regret
    (S : Arm → ℕ → Ω → ℝ) (action best : Ω → ℕ → Arm)
    (mu : Arm → ℝ) (q cost edge tail : Ω → ℕ → Arm → ℝ) (lambda : ℝ)
    {T : ℕ} {delta D : ℝ}
    (hLambda : 0 ≤ lambda) (hT : 1 ≤ T) (hDelta : 0 < delta) (hD : 0 ≤ D)
    (hMeas : ∀ a n, Measurable (S a n))
    (hMGF : ∀ a n, 0 < n → HasSubgaussianMGF (S a n) ((n : ℝ≥0) / 4) P)
    (hQ : ∀ ω t, t < T → Fintype.card Arm ≤ t → ∀ a,
      q ω t a = mu a + S a (AgentUCT.pullCount (action ω) a t) ω /
        (AgentUCT.pullCount (action ω) a t : ℝ))
    (hCount : ∀ ω t, t < T → Fintype.card Arm ≤ t → ∀ a,
      0 < AgentUCT.pullCount (action ω) a t)
    (hDecomp : ∀ ω t, t < T → ∀ a, cost ω t a = edge ω t a + tail ω t a)
    (hTail : ∀ ω t, t < T → ∀ a, 0 ≤ tail ω t a)
    (hGapNonneg : ∀ ω t, t < T →
      0 ≤ localGap mu (cost ω) lambda (action ω) (best ω) t)
    (hGapUpper : ∀ ω t, t < T →
      localGap mu (cost ω) lambda (action ω) (best ω) t ≤ D)
    (hSeparated : ∀ ω t, t < T →
      0 < localGap mu (cost ω) lambda (action ω) (best ω) t →
      delta ≤ localGap mu (cost ω) lambda (action ω) (best ω) t)
    (hSelect : ∀ ω t, t < T → Fintype.card Arm ≤ t →
      q ω t (best ω t) + localRadius (action ω) (best ω t) t -
        lambda * edge ω t (best ω t) ≤
      q ω t (action ω t) + localRadius (action ω) (action ω t) t -
        lambda * edge ω t (action ω t))
    (hRegretInt : Integrable (fun ω ↦ ∑ t ∈ range T,
      localGap mu (cost ω) lambda (action ω) (best ω) t) P)
    (hTailInt : Integrable (fun ω ↦ ∑ t ∈ range T, tail ω t (action ω t)) P) :
    (∫ ω, (∑ t ∈ range T,
      localGap mu (cost ω) lambda (action ω) (best ω) t) ∂P) ≤
      (Fintype.card Arm : ℝ) * D * (32 * Real.log (T : ℝ) / delta ^ 2 + 6) +
      2 * lambda * (∫ ω, (∑ t ∈ range T, tail ω t (action ω t)) ∂P) := by
  have hErrInt : Integrable
      (fun ω ↦ ∑ t ∈ range T, lambda * tail ω t (action ω t)) P := by
    simpa only [← Finset.mul_sum] using hTailInt.const_mul lambda
  have h := expected_regret_with_error_budget S action
    (fun ω t ↦ localGap mu (cost ω) lambda (action ω) (best ω) t)
    (fun ω t ↦ lambda * tail ω t (action ω t)) hT hDelta hD hMeas hMGF
    hGapNonneg hGapUpper (fun ω t ht ↦ mul_nonneg hLambda (hTail ω t ht _))
    hSeparated (fun ω t ht hk ↦ hCount ω t ht hk _) ?_ hRegretInt hErrInt
  · simpa only [← Finset.mul_sum, integral_const_mul, mul_assoc] using h
  · intro ω t ht hk hGood
    have hc (a : Arm) := sample_mean_confidence S action mu q
      (hCount ω t ht hk a) (hQ ω t ht hk a) hGood
    have hp := nonnegative_tail_gap_bound (tailChosen := tail ω t (action ω t))
      hLambda (hTail ω t ht (best ω t))
      (by linarith [(abs_le.mp (hc (best ω t))).1] :
        mu (best ω t) ≤ q ω t (best ω t) + localRadius (action ω) (best ω t) t)
      (by linarith [(abs_le.mp (hc (action ω t))).2] :
        q ω t (action ω t) ≤ mu (action ω t) + localRadius (action ω) (action ω t) t)
      (hSelect ω t ht hk)
    simpa only [localGap, hDecomp ω t ht] using hp

/-- Persistent materialization converts omitted cold work into a finite additive
regret term. Conditional calibration is explicit; no cumulative error bound is assumed. -/
theorem expected_next_edge_regret_with_cache
    {Resource : Type*} [DecidableEq Resource]
    (S : Arm → ℕ → Ω → ℝ) (action best : Ω → ℕ → Arm)
    (mu : Arm → ℝ) (q cost edge tail : Ω → ℕ → Arm → ℝ) (lambda : ℝ)
    {T : ℕ} {delta D : ℝ}
    (hLambda : 0 ≤ lambda) (hT : 1 ≤ T) (hDelta : 0 < delta) (hD : 0 ≤ D)
    (hMeas : ∀ a n, Measurable (S a n))
    (hMGF : ∀ a n, 0 < n → HasSubgaussianMGF (S a n) ((n : ℝ≥0) / 4) P)
    (hQ : ∀ ω t, t < T → Fintype.card Arm ≤ t → ∀ a,
      q ω t a = mu a + S a (AgentUCT.pullCount (action ω) a t) ω /
        (AgentUCT.pullCount (action ω) a t : ℝ))
    (hCount : ∀ ω t, t < T → Fintype.card Arm ≤ t → ∀ a,
      0 < AgentUCT.pullCount (action ω) a t)
    (hDecomp : ∀ ω t, t < T → ∀ a, cost ω t a = edge ω t a + tail ω t a)
    (hTail : ∀ ω t, t < T → ∀ a, 0 ≤ tail ω t a)
    (hGapNonneg : ∀ ω t, t < T →
      0 ≤ localGap mu (cost ω) lambda (action ω) (best ω) t)
    (hGapUpper : ∀ ω t, t < T →
      localGap mu (cost ω) lambda (action ω) (best ω) t ≤ D)
    (hSeparated : ∀ ω t, t < T →
      0 < localGap mu (cost ω) lambda (action ω) (best ω) t →
      delta ≤ localGap mu (cost ω) lambda (action ω) (best ω) t)
    (hSelect : ∀ ω t, t < T → Fintype.card Arm ≤ t →
      q ω t (best ω t) + localRadius (action ω) (best ω t) t -
        lambda * edge ω t (best ω t) ≤
      q ω t (action ω t) + localRadius (action ω) (action ω t) t -
        lambda * edge ω t (action ω t))
    (hRegretInt : Integrable (fun ω ↦ ∑ t ∈ range T,
      localGap mu (cost ω) lambda (action ω) (best ω) t) P)
    (weight : Resource → ℝ) (hWeight : ∀ r, 0 ≤ weight r)
    (cached demand : Ω → ℕ → Finset Resource) (initial resourceSet : Finset Resource)
    (hInitial : ∀ ω, cached ω 0 = initial)
    (hStep : ∀ ω t, cached ω (t + 1) = cached ω t ∪ demand ω t)
    (hUniverse : ∀ ω, cached ω T ⊆ resourceSet)
    (actual : Ω → ℕ → ℝ)
    (hActual : ∀ ω t, t ∈ range T →
      0 ≤ actual ω t ∧ actual ω t ≤ coldWork weight (cached ω t) (demand ω t))
    (hActualInt : ∀ t ∈ range T, Integrable (fun ω ↦ actual ω t) P)
    (info : ℕ → MeasurableSpace Ω) (hInfo : ∀ t, info t ≤ ‹MeasurableSpace Ω›)
    (hForecast : ∀ t ∈ range T, (fun ω ↦ tail ω t (action ω t)) =ᵐ[P]
      (fun ω ↦ conditionalColdForecast P info actual ω t)) :
    (∫ ω, (∑ t ∈ range T,
      localGap mu (cost ω) lambda (action ω) (best ω) t) ∂P) ≤
      (Fintype.card Arm : ℝ) * D * (32 * Real.log (T : ℝ) / delta ^ 2 + 6) +
      2 * lambda * (cacheWeight weight resourceSet - cacheWeight weight initial) := by
  have hTailInt : Integrable (fun ω ↦ ∑ t ∈ range T, tail ω t (action ω t)) P := by
    apply integrable_finset_sum
    intro t ht
    exact integrable_condExp.congr (hForecast t ht).symm
  have h := expected_next_edge_regret S action best mu q cost edge tail lambda
    hLambda hT hDelta hD hMeas hMGF hQ hCount hDecomp hTail
    hGapNonneg hGapUpper hSeparated hSelect hRegretInt hTailInt
  have hBudget := expected_forecast_cold_budget P weight hWeight cached demand initial
    resourceSet T hInitial hStep hUniverse actual (fun ω t ↦ tail ω t (action ω t))
    hActual hActualInt info hInfo hForecast
  exact h.trans (add_le_add_left
    (mul_le_mul_of_nonneg_left hBudget (mul_nonneg (by norm_num) hLambda)) _)

#print axioms expected_next_edge_regret_with_cache

#print axioms expected_next_edge_regret

end AgentUCTPaper
end
end CompleteProofSource11

/-!
## SOURCE 12: AgentUCTPaper/TreeBackup.lean
Original definitions, theorem statements, and complete proof bodies.
-/
section CompleteProofSource12

/-! # Operational reward backup

An event backs up its terminal Score through the prefixes of the actual expanded tree node.
The terminal rollout may be deeper. Replay is an operational left fold of these updates.
No statistical independence, concentration, or regret assumption enters this module.
-/

set_option autoImplicit false

noncomputable section

namespace AgentUCTPaper

structure BackupStat where
  visits : ℕ
  rewardSum : ℝ
  deriving DecidableEq

structure TreeEvaluation (Action : Type*) where
  expanded : List Action
  terminal : List Action
  reward : ℝ
  bill : ℝ
  expanded_is_prefix : expanded <+: terminal

abbrev TreeStatistics (Action : Type*) := List Action → BackupStat

def emptyStatistics {Action : Type*} : TreeStatistics Action := fun _ ↦ ⟨0, 0⟩

def BackupStat.mean (stat : BackupStat) : ℝ := stat.rewardSum / stat.visits

variable {Action : Type*} [DecidableEq Action]

/-- The loop visits precisely the expanded node and its existing ancestors, once each. -/
def backupEvent (stats : TreeStatistics Action) (event : TreeEvaluation Action) :
    TreeStatistics Action := fun p ↦
  if p <+: event.expanded then
    ⟨(stats p).visits + 1, (stats p).rewardSum + event.reward⟩
  else stats p

def replayBackup (events : List (TreeEvaluation Action))
    (initial : TreeStatistics Action := emptyStatistics) : TreeStatistics Action :=
  events.foldl backupEvent initial

def backedCount (events : List (TreeEvaluation Action)) (p : List Action) : ℕ :=
  (events.filter fun event ↦ decide (p <+: event.expanded)).length

def backedReturn (events : List (TreeEvaluation Action)) (p : List Action) : ℝ :=
  (events.map fun event ↦ if p <+: event.expanded then event.reward else 0).sum

/-- Committing the next complete result is the same update used by the search loop. -/
theorem replayBackup_append_one (events : List (TreeEvaluation Action))
    (event : TreeEvaluation Action) (initial : TreeStatistics Action) :
    replayBackup (events ++ [event]) initial = backupEvent (replayBackup events initial) event := by
  simp [replayBackup, List.foldl_append]

/-- Counts are derived from repeated updates, rather than postulated observation counts. -/
theorem replayBackup_visits (events : List (TreeEvaluation Action))
    (initial : TreeStatistics Action) (p : List Action) :
    (replayBackup events initial p).visits = (initial p).visits + backedCount events p := by
  induction events generalizing initial with
  | nil => simp [replayBackup, backedCount]
  | cons event events ih =>
    change (replayBackup events (backupEvent initial event) p).visits = _
    rw [ih]
    by_cases h : p <+: event.expanded
    · simp [backupEvent, backedCount, h]
      omega
    · simp [backupEvent, backedCount, h]

/-- The operational reward sum is exactly the sum of terminal Scores passing through the node. -/
theorem replayBackup_rewardSum (events : List (TreeEvaluation Action))
    (initial : TreeStatistics Action) (p : List Action) :
    (replayBackup events initial p).rewardSum = (initial p).rewardSum + backedReturn events p := by
  induction events generalizing initial with
  | nil => simp [replayBackup, backedReturn]
  | cons event events ih =>
    change (replayBackup events (backupEvent initial event) p).rewardSum = _
    rw [ih]
    by_cases h : p <+: event.expanded
    · simp [backupEvent, backedReturn, h]
      ring
    · simp [backupEvent, backedReturn, h]

/-- Starting from zero, Q is the actual selected-return mean, including Q=0 when unvisited. -/
theorem replayBackup_mean (events : List (TreeEvaluation Action)) (p : List Action) :
    (replayBackup events emptyStatistics p).mean =
      backedReturn events p / backedCount events p := by
  simp [BackupStat.mean, replayBackup_visits, replayBackup_rewardSum, emptyStatistics]

/-- Every complete evaluation contributes once to the root, including a cache hit. -/
theorem replayBackup_root_visits (events : List (TreeEvaluation Action)) :
    (replayBackup events emptyStatistics []).visits = events.length := by
  simp [replayBackup_visits, emptyStatistics, backedCount]

/-- A node outside the expanded path receives no reward or visit update. -/
theorem backupEvent_off_path (stats : TreeStatistics Action) (event : TreeEvaluation Action)
    (p : List Action) (h : ¬ p <+: event.expanded) : backupEvent stats event p = stats p := by
  simp [backupEvent, h]

/-- Changing only the physical bill cannot change raw reward backup. -/
theorem backupEvent_bill_irrelevant (stats : TreeStatistics Action) (event : TreeEvaluation Action)
    (bill : ℝ) : backupEvent stats { event with bill := bill } = backupEvent stats event := by
  rfl

/-- A node reward sum stays between zero and its visit count. -/
theorem backupEvent_bounded (stats : TreeStatistics Action) (event : TreeEvaluation Action)
    (hStats : ∀ p, 0 ≤ (stats p).rewardSum ∧ (stats p).rewardSum ≤ (stats p).visits)
    (hReward : 0 ≤ event.reward ∧ event.reward ≤ 1) :
    ∀ p, 0 ≤ (backupEvent stats event p).rewardSum ∧
      (backupEvent stats event p).rewardSum ≤ (backupEvent stats event p).visits := by
  intro p
  by_cases h : p <+: event.expanded
  · simp only [backupEvent, if_pos h, Nat.cast_add, Nat.cast_one]
    obtain ⟨h0, h1⟩ := hStats p
    constructor <;> linarith [hReward.1, hReward.2]
  · simpa [backupEvent, h] using hStats p

theorem replayBackup_bounded (events : List (TreeEvaluation Action))
    (initial : TreeStatistics Action)
    (hStats : ∀ p, 0 ≤ (initial p).rewardSum ∧ (initial p).rewardSum ≤ (initial p).visits)
    (hRewards : ∀ event ∈ events, 0 ≤ event.reward ∧ event.reward ≤ 1) :
    ∀ p, 0 ≤ (replayBackup events initial p).rewardSum ∧
      (replayBackup events initial p).rewardSum ≤ (replayBackup events initial p).visits := by
  induction events generalizing initial with
  | nil => simpa [replayBackup] using hStats
  | cons event events ih =>
    exact ih (backupEvent initial event)
      (backupEvent_bounded initial event hStats (hRewards event (by simp)))
      (fun e he ↦ hRewards e (by simp [he]))

theorem replayBackup_mean_mem_unit (events : List (TreeEvaluation Action))
    (hRewards : ∀ event ∈ events, 0 ≤ event.reward ∧ event.reward ≤ 1) (p : List Action) :
    (replayBackup events emptyStatistics p).mean ∈ Set.Icc (0 : ℝ) 1 := by
  obtain ⟨h0, h1⟩ := replayBackup_bounded events emptyStatistics
    (fun _ ↦ by simp [emptyStatistics]) hRewards p
  change 0 ≤ _ / _ ∧ _ / _ ≤ 1
  constructor
  · exact div_nonneg h0 (Nat.cast_nonneg _)
  · by_cases hN : (replayBackup events emptyStatistics p).visits = 0
    · simp [hN]
    · exact (div_le_one (Nat.cast_pos.mpr (Nat.pos_of_ne_zero hN))).mpr h1

end AgentUCTPaper
end
end CompleteProofSource12

/-!
## SOURCE 13: AgentUCTPaper/TreeProtocol.lean
Original definitions, theorem statements, and complete proof bodies.
-/
section CompleteProofSource13

/-! # Expansion, commit, and training recommendation

All paths are relative to the fixed caller-owned root. A complete evaluation inserts at most
one child; its rollout can be deeper. Selection-index conditions are imposed separately.
-/

set_option autoImplicit false

noncomputable section

namespace AgentUCTPaper

variable {Action : Type*} [DecidableEq Action]

def PrefixClosed (nodes : Finset (List Action)) : Prop :=
  ∀ p ∈ nodes, ∀ q, q <+: p → q ∈ nodes

def LegalTreeEvent (terminal : List Action → Prop) (nodes : Finset (List Action))
    (event : TreeEvaluation Action) : Prop :=
  terminal event.terminal ∧
    ((event.expanded ∈ nodes ∧ terminal event.expanded) ∨
      ∃ p ∈ nodes, ∃ a, event.expanded = p ++ [a] ∧ event.expanded ∉ nodes)

def growTree (nodes : Finset (List Action)) (event : TreeEvaluation Action) :
    Finset (List Action) := insert event.expanded nodes

def replayTree (events : List (TreeEvaluation Action))
    (initial : Finset (List Action) := {[]}) : Finset (List Action) :=
  events.foldl growTree initial

def LegalTreeRun (terminal : List Action → Prop) :
    Finset (List Action) → List (TreeEvaluation Action) → Prop
  | _, [] => True
  | nodes, event :: events =>
      LegalTreeEvent terminal nodes event ∧ LegalTreeRun terminal (growTree nodes event) events

omit [DecidableEq Action] in
theorem root_prefixClosed : PrefixClosed ({[]} : Finset (List Action)) := by
  intro p hp q hq
  simp only [Finset.mem_singleton] at hp ⊢
  subst p
  simpa using hq

theorem insert_child_prefixClosed (nodes : Finset (List Action)) (p : List Action)
    (a : Action) (hClosed : PrefixClosed nodes) (hp : p ∈ nodes) :
    PrefixClosed (insert (p ++ [a]) nodes) := by
  intro x hx q hq
  rcases Finset.mem_insert.mp hx with rfl | hx
  · by_cases hlen : q.length ≤ p.length
    · exact Finset.mem_insert_of_mem
        (hClosed p hp q (List.prefix_of_prefix_length_le hq (List.prefix_append p [a]) hlen))
    · have heq : q = p ++ [a] := hq.eq_of_length_le
        (by simp only [List.length_append, List.length_singleton]; omega)
      rw [heq]
      exact Finset.mem_insert_self _ _
  · exact Finset.mem_insert_of_mem (hClosed x hx q hq)

theorem growTree_prefixClosed (terminal : List Action → Prop)
    (nodes : Finset (List Action)) (event : TreeEvaluation Action)
    (hClosed : PrefixClosed nodes) (hLegal : LegalTreeEvent terminal nodes event) :
    PrefixClosed (growTree nodes event) := by
  rcases hLegal.2 with hOld | ⟨p, hp, a, he, _⟩
  · simpa [growTree, Finset.insert_eq_of_mem hOld.1] using hClosed
  · simpa [growTree, he] using insert_child_prefixClosed nodes p a hClosed hp

theorem replayTree_prefixClosed (terminal : List Action → Prop)
    (events : List (TreeEvaluation Action)) (initial : Finset (List Action))
    (hClosed : PrefixClosed initial) (hLegal : LegalTreeRun terminal initial events) :
    PrefixClosed (replayTree events initial) := by
  induction events generalizing initial with
  | nil => exact hClosed
  | cons event events ih =>
    exact ih _ (growTree_prefixClosed terminal initial event hClosed hLegal.1) hLegal.2

theorem replayTree_card (events : List (TreeEvaluation Action))
    (initial : Finset (List Action)) :
    (replayTree events initial).card ≤ initial.card + events.length := by
  induction events generalizing initial with
  | nil => simp [replayTree]
  | cons event events ih =>
    have h := ih (growTree initial event)
    have hc : (growTree initial event).card ≤ initial.card + 1 :=
      Finset.card_insert_le event.expanded initial
    change (replayTree events (growTree initial event)).card ≤ initial.card + (events.length + 1)
    omega

/-- Membership records expanded paths only, even when the terminal completion is longer. -/
theorem replayTree_mem (events : List (TreeEvaluation Action))
    (initial : Finset (List Action)) (p : List Action) :
    p ∈ replayTree events initial ↔ p ∈ initial ∨ ∃ event ∈ events, p = event.expanded := by
  induction events generalizing initial with
  | nil => simp [replayTree]
  | cons event events ih =>
    change p ∈ replayTree events (growTree initial event) ↔ _
    rw [ih]
    simp only [growTree, Finset.mem_insert, List.mem_cons]
    aesop

/-- A node absent from the expanded tree has received no earlier ancestor update. -/
theorem replayBackup_nonnode_zero (terminal : List Action → Prop)
    (events : List (TreeEvaluation Action)) (p : List Action)
    (hLegal : LegalTreeRun terminal {[]} events) (hAbsent : p ∉ replayTree events {[]}) :
    (replayBackup events emptyStatistics p).visits = 0 ∧
      (replayBackup events emptyStatistics p).rewardSum = 0 := by
  have hClosed := replayTree_prefixClosed terminal events {[]} root_prefixClosed hLegal
  have hMiss : ∀ e ∈ events, ¬ p <+: e.expanded := by
    intro e he hp
    exact hAbsent (hClosed e.expanded ((replayTree_mem events {[]} e.expanded).mpr
      (Or.inr ⟨e, he, rfl⟩)) p hp)
  have hCount : backedCount events p = 0 := by
    simpa [backedCount, List.filter_eq_nil_iff] using hMiss
  have hReturn : backedReturn events p = 0 := by
    apply List.sum_eq_zero
    intro x hx
    obtain ⟨e, he, rfl⟩ := List.mem_map.mp hx
    simp [hMiss e he]
  simp [replayBackup_visits, replayBackup_rewardSum, emptyStatistics, hCount, hReturn]

theorem inserted_node_first_visit (terminal : List Action → Prop)
    (events : List (TreeEvaluation Action)) (event : TreeEvaluation Action)
    (hLegal : LegalTreeRun terminal {[]} events)
    (hNew : event.expanded ∉ replayTree events {[]}) :
    (replayBackup (events ++ [event]) emptyStatistics event.expanded).visits = 1 := by
  have h0 := (replayBackup_nonnode_zero terminal events event.expanded hLegal hNew).1
  rw [replayBackup_append_one]
  simp [backupEvent, h0]

/-- A failed or partial evaluator result is not a completed reward observation. -/
def commitComplete (stats : TreeStatistics Action) (outcome : Option (TreeEvaluation Action)) :
    TreeStatistics Action :=
  match outcome with
  | none => stats
  | some event => backupEvent stats event

theorem incomplete_does_not_backup (stats : TreeStatistics Action) :
    commitComplete stats none = stats := rfl

def keepBest (best event : TreeEvaluation Action) : TreeEvaluation Action :=
  if best.reward < event.reward then event else best

def bestFrom (initial : TreeEvaluation Action) (events : List (TreeEvaluation Action)) :
    TreeEvaluation Action := events.foldl keepBest initial

def bestCompleted : List (TreeEvaluation Action) → Option (TreeEvaluation Action)
  | [] => none
  | event :: events => some (bestFrom event events)

omit [DecidableEq Action] in
theorem bestFrom_mem (initial : TreeEvaluation Action) (events : List (TreeEvaluation Action)) :
    bestFrom initial events ∈ initial :: events := by
  induction events generalizing initial with
  | nil => simp [bestFrom]
  | cons event events ih =>
    change bestFrom (keepBest initial event) events ∈ initial :: event :: events
    rcases List.mem_cons.mp (ih (keepBest initial event)) with h | h
    · rw [h]
      unfold keepBest
      split_ifs <;> simp
    · simp [h]

omit [DecidableEq Action] in
theorem keepBest_left_le (initial event : TreeEvaluation Action) :
    initial.reward ≤ (keepBest initial event).reward := by
  unfold keepBest
  split_ifs with h
  · exact h.le
  · exact le_rfl

omit [DecidableEq Action] in
theorem keepBest_right_le (initial event : TreeEvaluation Action) :
    event.reward ≤ (keepBest initial event).reward := by
  unfold keepBest
  split_ifs with h
  · exact le_rfl
  · exact le_of_not_gt h

omit [DecidableEq Action] in
theorem bestFrom_initial_le (initial : TreeEvaluation Action)
    (events : List (TreeEvaluation Action)) :
    initial.reward ≤ (bestFrom initial events).reward := by
  induction events generalizing initial with
  | nil => exact le_rfl
  | cons event events ih =>
    exact (keepBest_left_le initial event).trans (ih (keepBest initial event))

omit [DecidableEq Action] in
theorem bestFrom_all_le (initial : TreeEvaluation Action)
    (events : List (TreeEvaluation Action)) (event : TreeEvaluation Action) (he : event ∈ events) :
    event.reward ≤ (bestFrom initial events).reward := by
  induction events generalizing initial with
  | nil => simp at he
  | cons head events ih =>
    rcases List.mem_cons.mp he with rfl | he
    · exact (keepBest_right_le initial event).trans (bestFrom_initial_le _ _)
    · exact ih _ he

omit [DecidableEq Action] in
theorem bestCompleted_spec (events : List (TreeEvaluation Action))
    (best : TreeEvaluation Action) (hBest : bestCompleted events = some best) :
    best ∈ events ∧ ∀ event ∈ events, event.reward ≤ best.reward := by
  cases events with
  | nil => simp [bestCompleted] at hBest
  | cons head events =>
    simp only [bestCompleted, Option.some.injEq] at hBest
    subst best
    refine ⟨bestFrom_mem head events, ?_⟩
    intro event he
    rcases List.mem_cons.mp he with rfl | he
    · exact bestFrom_initial_le event events
    · exact bestFrom_all_le head events event he

omit [DecidableEq Action] in
theorem keepBest_tie_keeps_first (initial event : TreeEvaluation Action)
    (hTie : initial.reward = event.reward) : keepBest initial event = initial := by
  simp [keepBest, hTie]

end AgentUCTPaper
end
end CompleteProofSource13

/-!
## SOURCE 14: AgentUCTPaper/TreeExecution.lean
Original definitions, theorem statements, and complete proof bodies.
-/
section CompleteProofSource14

/-! # A shared operational trace for backup and physical materialization

Resource identities are qid and full execution prefix within a fixed namespace.
`executionPath` embeds relative tree paths under the caller's execution root.
Successful execution persists every demanded prefix; nonreusable overhead is separate.
-/

set_option autoImplicit false

noncomputable section

namespace AgentUCTPaper

open Finset

variable {Qid Action : Type*} [DecidableEq Qid] [DecidableEq Action]

def executionPrefixes (path : List Action) : Finset (List Action) :=
  (Icc 1 path.length).image (fun stage ↦ path.take stage)

def panelDemand (qids : Finset Qid) (path : List Action) : Finset (Qid × List Action) :=
  qids ×ˢ executionPrefixes path

omit [DecidableEq Qid] in
theorem panelDemand_mem (qids : Finset Qid) (path p : List Action) (qid : Qid) :
    (qid, p) ∈ panelDemand qids path ↔ qid ∈ qids ∧ p ∈ executionPrefixes path := by
  simp [panelDemand]

omit [DecidableEq Qid] in
theorem different_qids_disjoint (q1 q2 : Qid) (path1 path2 : List Action) (h : q1 ≠ q2) :
    Disjoint (panelDemand {q1} path1) (panelDemand {q2} path2) := by
  apply Finset.disjoint_left.mpr
  intro resource h1 h2
  simp only [panelDemand, mem_product, mem_singleton] at h1 h2
  exact h (h1.1.symm.trans h2.1)

theorem other_qid_cache_cannot_pay (weight : Qid × List Action → ℝ)
    (q1 q2 : Qid) (path1 path2 : List Action) (h : q1 ≠ q2) :
    coldWork weight (panelDemand {q1} path1) (panelDemand {q2} path2) =
      cacheWeight weight (panelDemand {q2} path2) := by
  unfold coldWork cacheWeight
  rw [Finset.sdiff_eq_self_of_disjoint (different_qids_disjoint q1 q2 path1 path2 h).symm]

/-- Full-panel physical work sums the separate qid bills; it is not a panel average. -/
theorem coldWork_panel_sum (weight : Qid × List Action → ℝ)
    (cached : Finset (Qid × List Action)) (qids : Finset Qid) (path : List Action) :
    coldWork weight cached (panelDemand qids path) =
      ∑ qid ∈ qids, coldWork weight cached (panelDemand {qid} path) := by
  simp [coldWork, panelDemand, Finset.sdiff_eq_filter, Finset.sum_filter, Finset.sum_product]

def panelScore (qids : Finset Qid) (score : Qid → ℝ) : ℝ :=
  (∑ qid ∈ qids, score qid) / qids.card

omit [DecidableEq Qid] [DecidableEq Action] in
theorem panelScore_bounded (qids : Finset Qid) (score : Qid → ℝ)
    (hScore : ∀ qid ∈ qids, 0 ≤ score qid ∧ score qid ≤ 1) :
    panelScore qids score ∈ Set.Icc (0 : ℝ) 1 := by
  have h0 : 0 ≤ ∑ qid ∈ qids, score qid := sum_nonneg (fun q hq ↦ (hScore q hq).1)
  have h1 : (∑ qid ∈ qids, score qid) ≤ (qids.card : ℝ) := by
    simpa using sum_le_sum (fun q hq ↦ (hScore q hq).2)
  unfold panelScore
  constructor
  · exact div_nonneg h0 (Nat.cast_nonneg _)
  · by_cases hCard : qids.card = 0
    · simp [hCard]
    · exact (div_le_one (Nat.cast_pos.mpr (Nat.pos_of_ne_zero hCard))).mpr h1

structure MeteredTreeState (Qid Action : Type*) where
  stats : TreeStatistics Action
  materialized : Finset (Qid × List Action)
  coldPaid : ℝ
  overheadPaid : ℝ

def MeteredTreeState.totalPaid (state : MeteredTreeState Qid Action) : ℝ :=
  state.coldPaid + state.overheadPaid

def meterStep (qids : Finset Qid) (executionPath : List Action → List Action)
    (weight : Qid × List Action → ℝ) (overhead : TreeEvaluation Action → ℝ)
    (state : MeteredTreeState Qid Action) (event : TreeEvaluation Action) :
    MeteredTreeState Qid Action :=
  let demand := panelDemand qids (executionPath event.terminal)
  let cold := coldWork weight state.materialized demand
  let billed := { event with bill := cold + overhead event }
  { stats := backupEvent state.stats billed
    materialized := state.materialized ∪ demand
    coldPaid := state.coldPaid + cold
    overheadPaid := state.overheadPaid + overhead event }

def replayMetered (qids : Finset Qid) (executionPath : List Action → List Action)
    (weight : Qid × List Action → ℝ) (overhead : TreeEvaluation Action → ℝ)
    (events : List (TreeEvaluation Action)) (initial : MeteredTreeState Qid Action) :
    MeteredTreeState Qid Action :=
  events.foldl (meterStep qids executionPath weight overhead) initial

/-- Cache objects and historical work are distinct state components, even in the persistent case. -/
structure PersistentCaches (Qid Action : Type*) where
  restorable : Finset (Qid × List Action)
  everMaterialized : Finset (Qid × List Action)

def publishComplete (qids : Finset Qid) (executionPath : List Action → List Action)
    (caches : PersistentCaches Qid Action) (event : TreeEvaluation Action) :
    PersistentCaches Qid Action :=
  let demand := panelDemand qids (executionPath event.terminal)
  ⟨caches.restorable ∪ demand, caches.everMaterialized ∪ demand⟩

def replayPublished (qids : Finset Qid) (executionPath : List Action → List Action)
    (events : List (TreeEvaluation Action)) (initial : PersistentCaches Qid Action) :
    PersistentCaches Qid Action := events.foldl (publishComplete qids executionPath) initial

/-- Equality follows from the initial state and successful persistence.
Eviction is a different transition and is not covered by this result. -/
theorem replayPublished_cache_equals_ledger (qids : Finset Qid)
    (executionPath : List Action → List Action) (events : List (TreeEvaluation Action))
    (initial : PersistentCaches Qid Action)
    (hInitial : initial.restorable = initial.everMaterialized) :
    (replayPublished qids executionPath events initial).restorable =
      (replayPublished qids executionPath events initial).everMaterialized := by
  induction events generalizing initial with
  | nil => exact hInitial
  | cons event events ih =>
    exact ih (publishComplete qids executionPath initial event)
      (by simp [publishComplete, hInitial])

theorem replayPublished_ledger_matches_metered (qids : Finset Qid)
    (executionPath : List Action → List Action) (weight : Qid × List Action → ℝ)
    (overhead : TreeEvaluation Action → ℝ) (events : List (TreeEvaluation Action))
    (caches : PersistentCaches Qid Action) (initial : MeteredTreeState Qid Action)
    (hInitial : caches.everMaterialized = initial.materialized) :
    (replayPublished qids executionPath events caches).everMaterialized =
      (replayMetered qids executionPath weight overhead events initial).materialized := by
  induction events generalizing caches initial with
  | nil => exact hInitial
  | cons event events ih =>
    exact ih (publishComplete qids executionPath caches event)
      (meterStep qids executionPath weight overhead initial event)
      (by simp [publishComplete, meterStep, hInitial])

theorem replayPublished_cache_matches_metered (qids : Finset Qid)
    (executionPath : List Action → List Action) (weight : Qid × List Action → ℝ)
    (overhead : TreeEvaluation Action → ℝ) (events : List (TreeEvaluation Action))
    (caches : PersistentCaches Qid Action) (initial : MeteredTreeState Qid Action)
    (hCache : caches.restorable = caches.everMaterialized)
    (hLedger : caches.everMaterialized = initial.materialized) :
    (replayPublished qids executionPath events caches).restorable =
      (replayMetered qids executionPath weight overhead events initial).materialized := by
  exact (replayPublished_cache_equals_ledger qids executionPath events caches hCache).trans
    (replayPublished_ledger_matches_metered qids executionPath weight overhead events caches
      initial hLedger)

theorem meterStep_stats (qids : Finset Qid) (executionPath : List Action → List Action)
    (weight : Qid × List Action → ℝ) (overhead : TreeEvaluation Action → ℝ)
    (state : MeteredTreeState Qid Action) (event : TreeEvaluation Action) :
    (meterStep qids executionPath weight overhead state event).stats =
      backupEvent state.stats event := rfl

theorem replayMetered_stats (qids : Finset Qid) (executionPath : List Action → List Action)
    (weight : Qid × List Action → ℝ) (overhead : TreeEvaluation Action → ℝ)
    (events : List (TreeEvaluation Action)) (initial : MeteredTreeState Qid Action) :
    (replayMetered qids executionPath weight overhead events initial).stats =
      replayBackup events initial.stats := by
  induction events generalizing initial with
  | nil => rfl
  | cons event events ih =>
    exact ih (meterStep qids executionPath weight overhead initial event)

theorem meterStep_cold_conservation (qids : Finset Qid)
    (executionPath : List Action → List Action) (weight : Qid × List Action → ℝ)
    (overhead : TreeEvaluation Action → ℝ) (state : MeteredTreeState Qid Action)
    (event : TreeEvaluation Action) :
    (meterStep qids executionPath weight overhead state event).coldPaid - state.coldPaid =
      cacheWeight weight (meterStep qids executionPath weight overhead state event).materialized -
        cacheWeight weight state.materialized := by
  simp only [meterStep, cache_union_accounting]
  ring

theorem replayMetered_cold_conservation (qids : Finset Qid)
    (executionPath : List Action → List Action) (weight : Qid × List Action → ℝ)
    (overhead : TreeEvaluation Action → ℝ) (events : List (TreeEvaluation Action))
    (initial : MeteredTreeState Qid Action) :
    (replayMetered qids executionPath weight overhead events initial).coldPaid - initial.coldPaid =
      cacheWeight weight
          (replayMetered qids executionPath weight overhead events initial).materialized -
        cacheWeight weight initial.materialized := by
  induction events generalizing initial with
  | nil => simp [replayMetered]
  | cons event events ih =>
    have h := ih (meterStep qids executionPath weight overhead initial event)
    have hstep := meterStep_cold_conservation qids executionPath weight overhead initial event
    change (replayMetered qids executionPath weight overhead events
      (meterStep qids executionPath weight overhead initial event)).coldPaid - initial.coldPaid =
      cacheWeight weight (replayMetered qids executionPath weight overhead events
        (meterStep qids executionPath weight overhead initial event)).materialized -
          cacheWeight weight initial.materialized
    linarith

theorem replayMetered_overhead (qids : Finset Qid) (executionPath : List Action → List Action)
    (weight : Qid × List Action → ℝ) (overhead : TreeEvaluation Action → ℝ)
    (events : List (TreeEvaluation Action)) (initial : MeteredTreeState Qid Action) :
    (replayMetered qids executionPath weight overhead events initial).overheadPaid =
      initial.overheadPaid + (events.map overhead).sum := by
  induction events generalizing initial with
  | nil => simp [replayMetered]
  | cons event events ih =>
    change (replayMetered qids executionPath weight overhead events
      (meterStep qids executionPath weight overhead initial event)).overheadPaid = _
    rw [ih]
    simp [meterStep, add_assoc]

theorem replayMetered_total (qids : Finset Qid) (executionPath : List Action → List Action)
    (weight : Qid × List Action → ℝ) (overhead : TreeEvaluation Action → ℝ)
    (events : List (TreeEvaluation Action)) (initial : MeteredTreeState Qid Action) :
    (replayMetered qids executionPath weight overhead events initial).totalPaid -
        initial.totalPaid =
      cacheWeight weight
          (replayMetered qids executionPath weight overhead events initial).materialized -
        cacheWeight weight initial.materialized + (events.map overhead).sum := by
  have hc := replayMetered_cold_conservation qids executionPath weight overhead events initial
  have ho := replayMetered_overhead qids executionPath weight overhead events initial
  unfold MeteredTreeState.totalPaid
  linarith

theorem replayMetered_cache_subset (qids : Finset Qid)
    (executionPath : List Action → List Action) (weight : Qid × List Action → ℝ)
    (overhead : TreeEvaluation Action → ℝ) (events : List (TreeEvaluation Action))
    (initial : MeteredTreeState Qid Action) (resources : Finset (Qid × List Action))
    (hInitial : initial.materialized ⊆ resources)
    (hDemand : ∀ e ∈ events, panelDemand qids (executionPath e.terminal) ⊆ resources) :
    (replayMetered qids executionPath weight overhead events initial).materialized ⊆ resources := by
  induction events generalizing initial with
  | nil => exact hInitial
  | cons event events ih =>
    apply ih (meterStep qids executionPath weight overhead initial event)
    · exact union_subset hInitial (hDemand event (by simp))
    · exact fun e he ↦ hDemand e (by simp [he])

theorem replayMetered_cold_budget (qids : Finset Qid)
    (executionPath : List Action → List Action) (weight : Qid × List Action → ℝ)
    (overhead : TreeEvaluation Action → ℝ) (events : List (TreeEvaluation Action))
    (initial : MeteredTreeState Qid Action) (resources : Finset (Qid × List Action))
    (hWeight : ∀ resource, 0 ≤ weight resource) (hInitial : initial.materialized ⊆ resources)
    (hDemand : ∀ e ∈ events, panelDemand qids (executionPath e.terminal) ⊆ resources) :
    (replayMetered qids executionPath weight overhead events initial).coldPaid - initial.coldPaid ≤
      cacheWeight weight resources - cacheWeight weight initial.materialized := by
  rw [replayMetered_cold_conservation]
  exact sub_le_sub_right (cacheWeight_mono weight hWeight
    (replayMetered_cache_subset qids executionPath weight overhead events initial resources
      hInitial hDemand)) _

/-- A cached completion still contributes a visit and reward, but no new cold work. -/
theorem meterStep_cached_visit (qids : Finset Qid) (executionPath : List Action → List Action)
    (weight : Qid × List Action → ℝ) (overhead : TreeEvaluation Action → ℝ)
    (state : MeteredTreeState Qid Action) (event : TreeEvaluation Action)
    (hCached : panelDemand qids (executionPath event.terminal) ⊆ state.materialized) :
    (meterStep qids executionPath weight overhead state event).coldPaid = state.coldPaid ∧
      ((meterStep qids executionPath weight overhead state event).stats []).visits =
        (state.stats []).visits + 1 ∧
      (meterStep qids executionPath weight overhead state event).overheadPaid =
        state.overheadPaid + overhead event := by
  simp [meterStep, cached_demand_is_free weight _ _ hCached, backupEvent]

end AgentUCTPaper
end
end CompleteProofSource14

/-!
## SOURCE 15: AgentUCTPaper/TreeCheckpoint.lean
Original definitions, theorem statements, and complete proof bodies.
-/
section CompleteProofSource15

/-! # Deriving deepest-checkpoint execution from a prefix-complete ledger -/

set_option autoImplicit false

noncomputable section

namespace AgentUCTPaper

open Finset

variable {Qid Action : Type*} [DecidableEq Qid] [DecidableEq Action]

def savedStages (cached : Finset (Qid × List Action)) (qid : Qid) (path : List Action) :
    Finset ℕ := insert 0 ((Icc 1 path.length).filter (fun i ↦ (qid, path.take i) ∈ cached))

def deepestSaved (cached : Finset (Qid × List Action)) (qid : Qid) (path : List Action) : ℕ :=
  (savedStages cached qid path).max' ⟨0, by simp [savedStages]⟩

def PrefixCompleteCache (cached : Finset (Qid × List Action)) : Prop :=
  ∀ q p, (q, p) ∈ cached → ∀ i, 1 ≤ i → i ≤ p.length → (q, p.take i) ∈ cached

theorem deepestSaved_mem (cached : Finset (Qid × List Action)) (qid : Qid) (path : List Action) :
    deepestSaved cached qid path ∈ savedStages cached qid path := Finset.max'_mem _ _

theorem deepestSaved_le_length (cached : Finset (Qid × List Action))
    (qid : Qid) (path : List Action) : deepestSaved cached qid path ≤ path.length := by
  rcases mem_insert.mp (deepestSaved_mem cached qid path) with h | h
  · omega
  · exact (mem_Icc.mp (mem_filter.mp h).1).2

theorem cached_stage_le_deepest (cached : Finset (Qid × List Action))
    (qid : Qid) (path : List Action) (i : ℕ)
    (hi : i ∈ Icc 1 path.length) (hCached : (qid, path.take i) ∈ cached) :
    i ≤ deepestSaved cached qid path := by
  apply Finset.le_max'
  simp [savedStages, hi, hCached]

theorem cached_stage_iff_le_deepest (cached : Finset (Qid × List Action))
    (hClosed : PrefixCompleteCache cached) (qid : Qid) (path : List Action) (i : ℕ)
    (hi : i ∈ Icc 1 path.length) :
    (qid, path.take i) ∈ cached ↔ i ≤ deepestSaved cached qid path := by
  constructor
  · exact cached_stage_le_deepest cached qid path i hi
  · intro hle
    have hi1 := (mem_Icc.mp hi).1
    rcases mem_insert.mp (deepestSaved_mem cached qid path) with hz | hc
    · omega
    · have hd := deepestSaved_le_length cached qid path
      have h := hClosed qid (path.take (deepestSaved cached qid path))
        (mem_filter.mp hc).2 i hi1 (by simp [List.length_take, Nat.min_eq_left hd, hle])
      simpa [List.take_take, Nat.min_eq_left hle] using h

theorem missing_stage_iff_after_checkpoint (cached : Finset (Qid × List Action))
    (hClosed : PrefixCompleteCache cached) (qid : Qid) (path : List Action) (i : ℕ)
    (hi : i ∈ Icc 1 path.length) :
    (qid, path.take i) ∉ cached ↔ deepestSaved cached qid path < i := by
  rw [cached_stage_iff_le_deepest cached hClosed qid path i hi, not_le]

theorem singleton_panel_stage_image (qid : Qid) (path : List Action) :
    panelDemand {qid} path = (Icc 1 path.length).image (fun i ↦ (qid, path.take i)) := by
  ext ⟨q, p⟩
  simp only [panelDemand, executionPrefixes, mem_product, mem_singleton, mem_image, Prod.mk.injEq]
  aesop

theorem panel_missing_is_checkpoint_suffix (cached : Finset (Qid × List Action))
    (hClosed : PrefixCompleteCache cached) (qid : Qid) (path : List Action) :
    panelDemand {qid} path \ cached =
      (Ioc (deepestSaved cached qid path) path.length).image (fun i ↦ (qid, path.take i)) := by
  rw [singleton_panel_stage_image]
  ext resource
  constructor
  · intro h
    obtain ⟨i, hi, rfl⟩ := mem_image.mp (mem_sdiff.mp h).1
    exact mem_image.mpr ⟨i, mem_Ioc.mpr
      ⟨(missing_stage_iff_after_checkpoint cached hClosed qid path i hi).mp (mem_sdiff.mp h).2,
        (mem_Icc.mp hi).2⟩, rfl⟩
  · intro h
    obtain ⟨i, hi, rfl⟩ := mem_image.mp h
    have hrange : i ∈ Icc 1 path.length := mem_Icc.mpr
      ⟨by have := (mem_Ioc.mp hi).1; omega, (mem_Ioc.mp hi).2⟩
    exact mem_sdiff.mpr ⟨mem_image.mpr ⟨i, hrange, rfl⟩,
      (missing_stage_iff_after_checkpoint cached hClosed qid path i hrange).mpr
        (mem_Ioc.mp hi).1⟩

omit [DecidableEq Qid] [DecidableEq Action] in
theorem prefix_keys_injective (qid : Qid) (path : List Action) {i j : ℕ}
    (hi : i ≤ path.length) (hj : j ≤ path.length)
    (heq : (qid, path.take i) = (qid, path.take j)) : i = j := by
  have hlen := congrArg (fun r : Qid × List Action ↦ r.2.length) heq
  simpa [List.length_take, Nat.min_eq_left hi, Nat.min_eq_left hj] using hlen

theorem coldWork_eq_deepest_suffix (weight : Qid × List Action → ℝ)
    (cached : Finset (Qid × List Action)) (hClosed : PrefixCompleteCache cached)
    (qid : Qid) (path : List Action) :
    coldWork weight cached (panelDemand {qid} path) =
      checkpointSuffixBill (fun i ↦ weight (qid, path.take i))
        (deepestSaved cached qid path) path.length := by
  unfold coldWork checkpointSuffixBill
  rw [panel_missing_is_checkpoint_suffix cached hClosed qid path, Finset.sum_image]
  intro i hi j hj heq
  exact prefix_keys_injective qid path (mem_Ioc.mp hi).2 (mem_Ioc.mp hj).2 heq

omit [DecidableEq Qid] [DecidableEq Action] in
theorem empty_prefixComplete : PrefixCompleteCache (∅ : Finset (Qid × List Action)) := by
  simp [PrefixCompleteCache]

omit [DecidableEq Qid] in
theorem panelDemand_prefixComplete (qids : Finset Qid) (path : List Action) :
    PrefixCompleteCache (panelDemand qids path) := by
  intro q p hp i hi hlen
  obtain ⟨hq, hp⟩ := (panelDemand_mem qids path p q).mp hp
  obtain ⟨j, hj, rfl⟩ := mem_image.mp hp
  have hjlen := (mem_Icc.mp hj).2
  have hij : i ≤ j := by simpa [List.length_take, Nat.min_eq_left hjlen] using hlen
  apply (panelDemand_mem qids path ((path.take j).take i) q).mpr
  refine ⟨hq, mem_image.mpr ⟨i, mem_Icc.mpr ⟨hi, hij.trans hjlen⟩, ?_⟩⟩
  simp [List.take_take, Nat.min_eq_left hij]

theorem prefixComplete_union {left right : Finset (Qid × List Action)}
    (hLeft : PrefixCompleteCache left) (hRight : PrefixCompleteCache right) :
    PrefixCompleteCache (left ∪ right) := by
  intro q p hp i hi hlen
  rcases mem_union.mp hp with hp | hp
  · exact mem_union_left _ (hLeft q p hp i hi hlen)
  · exact mem_union_right _ (hRight q p hp i hi hlen)

theorem replayMetered_prefixComplete (qids : Finset Qid)
    (executionPath : List Action → List Action) (weight : Qid × List Action → ℝ)
    (overhead : TreeEvaluation Action → ℝ) (events : List (TreeEvaluation Action))
    (initial : MeteredTreeState Qid Action) (hInitial : PrefixCompleteCache initial.materialized) :
    PrefixCompleteCache
      (replayMetered qids executionPath weight overhead events initial).materialized := by
  induction events generalizing initial with
  | nil => exact hInitial
  | cons event events ih =>
    exact ih (meterStep qids executionPath weight overhead initial event)
      (prefixComplete_union hInitial
        (panelDemand_prefixComplete qids (executionPath event.terminal)))

end AgentUCTPaper
end
end CompleteProofSource15

/-!
## SOURCE 16: AgentUCTPaper/TreeReturns.lean
Original definitions, theorem statements, and complete proof bodies.
-/
section CompleteProofSource16

/-! # Exact adaptive backup deficit for a fixed finite terminal table

There is no sampling or independence assumption. The missing rate problem is made explicit:
Q at an internal node differs from its best terminal value by its actual cumulative
descendant deficit divided by the number of backed-up evaluations.
-/

set_option autoImplicit false

noncomputable section

namespace AgentUCTPaper

open Finset

variable {Action : Type*} [DecidableEq Action]

def subtreeTerminals (terminals : Finset (List Action)) (p : List Action) :
    Finset (List Action) := terminals.filter (fun leaf ↦ p <+: leaf)

def subtreeValue (terminals : Finset (List Action)) (reward : List Action → ℝ)
    (p : List Action) : ℝ :=
  if h : (subtreeTerminals terminals p).Nonempty then
    (subtreeTerminals terminals p).sup' h reward
  else 0

def FixedTableEvents (terminals : Finset (List Action)) (reward : List Action → ℝ)
    (events : List (TreeEvaluation Action)) : Prop :=
  ∀ event ∈ events, event.terminal ∈ terminals ∧ event.reward = reward event.terminal

theorem subtreeValue_upper (terminals : Finset (List Action)) (reward : List Action → ℝ)
    (p leaf : List Action) (hLeaf : leaf ∈ terminals) (hPath : p <+: leaf) :
    reward leaf ≤ subtreeValue terminals reward p := by
  have hm : leaf ∈ subtreeTerminals terminals p := mem_filter.mpr ⟨hLeaf, hPath⟩
  have hn : (subtreeTerminals terminals p).Nonempty := ⟨leaf, hm⟩
  simp only [subtreeValue, dif_pos hn]
  exact Finset.le_sup' reward hm

theorem subtreeValue_attained (terminals : Finset (List Action)) (reward : List Action → ℝ)
    (p : List Action) (h : (subtreeTerminals terminals p).Nonempty) :
    ∃ leaf ∈ terminals, p <+: leaf ∧ subtreeValue terminals reward p = reward leaf := by
  obtain ⟨leaf, hm, he⟩ := Finset.exists_mem_eq_sup' h reward
  exact ⟨leaf, (mem_filter.mp hm).1, (mem_filter.mp hm).2, by simp [subtreeValue, h, he]⟩

theorem subtreeValue_at_terminal (terminals : Finset (List Action)) (reward : List Action → ℝ)
    (hAntichain : ∀ p ∈ terminals, ∀ q ∈ terminals, p <+: q → p = q)
    (leaf : List Action) (hLeaf : leaf ∈ terminals) :
    subtreeValue terminals reward leaf = reward leaf := by
  have h : (subtreeTerminals terminals leaf).Nonempty :=
    ⟨leaf, mem_filter.mpr ⟨hLeaf, List.prefix_refl _⟩⟩
  obtain ⟨other, ho, hp, hv⟩ := subtreeValue_attained terminals reward leaf h
  have he := hAntichain leaf hLeaf other ho hp
  simpa [← he] using hv

def backedDeficit (value : ℝ) (events : List (TreeEvaluation Action)) (p : List Action) : ℝ :=
  (events.map (fun event ↦ if p <+: event.expanded then value - event.reward else 0)).sum

theorem backedDeficit_identity (value : ℝ) (events : List (TreeEvaluation Action))
    (p : List Action) :
    backedDeficit value events p = (backedCount events p : ℝ) * value - backedReturn events p := by
  induction events with
  | nil => simp [backedDeficit, backedCount, backedReturn]
  | cons event events ih =>
    by_cases h : p <+: event.expanded
    · simp [backedDeficit, backedCount, backedReturn, h] at ih ⊢
      linarith
    · simpa [backedDeficit, backedCount, backedReturn, h] using ih

theorem operational_mean_deficit (value : ℝ) (events : List (TreeEvaluation Action))
    (p : List Action) (hCount : 0 < backedCount events p) :
    (replayBackup events emptyStatistics p).mean =
      value - backedDeficit value events p / backedCount events p := by
  rw [replayBackup_mean, backedDeficit_identity]
  have hn : (backedCount events p : ℝ) ≠ 0 := Nat.cast_ne_zero.mpr (Nat.ne_of_gt hCount)
  field_simp
  ring

theorem subtree_backedDeficit_nonnegative (terminals : Finset (List Action))
    (reward : List Action → ℝ) (events : List (TreeEvaluation Action))
    (hTable : FixedTableEvents terminals reward events) (p : List Action) :
    0 ≤ backedDeficit (subtreeValue terminals reward p) events p := by
  apply List.sum_nonneg
  intro x hx
  obtain ⟨event, he, rfl⟩ := List.mem_map.mp hx
  split_ifs with hp
  · rw [(hTable event he).2]
    exact sub_nonneg.mpr (subtreeValue_upper terminals reward p event.terminal
      (hTable event he).1 (hp.trans event.expanded_is_prefix))
  · exact le_rfl

theorem operational_mean_le_subtreeValue (terminals : Finset (List Action))
    (reward : List Action → ℝ) (events : List (TreeEvaluation Action))
    (hTable : FixedTableEvents terminals reward events) (p : List Action)
    (hCount : 0 < backedCount events p) :
    (replayBackup events emptyStatistics p).mean ≤ subtreeValue terminals reward p := by
  rw [operational_mean_deficit _ events p hCount]
  exact sub_le_self _ (div_nonneg
    (subtree_backedDeficit_nonnegative terminals reward events hTable p) (Nat.cast_nonneg _))

theorem terminal_backedDeficit_zero (terminals : Finset (List Action))
    (reward : List Action → ℝ) (events : List (TreeEvaluation Action))
    (hTable : FixedTableEvents terminals reward events)
    (hAntichain : ∀ p ∈ terminals, ∀ q ∈ terminals, p <+: q → p = q)
    (leaf : List Action) (hLeaf : leaf ∈ terminals) :
    backedDeficit (reward leaf) events leaf = 0 := by
  apply List.sum_eq_zero
  intro x hx
  obtain ⟨event, he, rfl⟩ := List.mem_map.mp hx
  split_ifs with hp
  · have hEq := hAntichain leaf hLeaf event.terminal (hTable event he).1
      (hp.trans event.expanded_is_prefix)
    simp [(hTable event he).2, hEq]
  · rfl

theorem operational_terminal_mean_exact (terminals : Finset (List Action))
    (reward : List Action → ℝ) (events : List (TreeEvaluation Action))
    (hTable : FixedTableEvents terminals reward events)
    (hAntichain : ∀ p ∈ terminals, ∀ q ∈ terminals, p <+: q → p = q)
    (leaf : List Action) (hLeaf : leaf ∈ terminals) (hCount : 0 < backedCount events leaf) :
    (replayBackup events emptyStatistics leaf).mean = reward leaf := by
  rw [operational_mean_deficit _ events leaf hCount,
    terminal_backedDeficit_zero terminals reward events hTable hAntichain leaf hLeaf]
  simp

theorem root_deficit_is_terminal_quality_regret (value : ℝ)
    (events : List (TreeEvaluation Action)) :
    backedDeficit value events [] = (events.map (fun event ↦ value - event.reward)).sum := by
  simp [backedDeficit]

omit [DecidableEq Action] in
theorem sum_returns_le_best (value : ℝ) (events : List (TreeEvaluation Action))
    (hBound : ∀ event ∈ events, event.reward ≤ value) :
    (events.map TreeEvaluation.reward).sum ≤ events.length * value := by
  induction events with
  | nil => simp
  | cons event events ih =>
    have hTail := ih (fun e he ↦ hBound e (by simp [he]))
    have hHead := hBound event (by simp)
    simp only [List.map_cons, List.sum_cons, List.length_cons, Nat.cast_add, Nat.cast_one]
    nlinarith

/-- This connects an actual root quality-regret bound to the training endpoint only. -/
theorem best_training_simple_gap (value : ℝ) (events : List (TreeEvaluation Action))
    (best : TreeEvaluation Action) (hBest : bestCompleted events = some best) :
    value - best.reward ≤ backedDeficit value events [] / events.length := by
  have hSpec := bestCompleted_spec events best hBest
  have hLen : 0 < events.length := List.length_pos_iff.mpr (by
    intro hNil
    simp [hNil, bestCompleted] at hBest)
  have hSum := sum_returns_le_best best.reward events hSpec.2
  rw [le_div_iff₀ (Nat.cast_pos.mpr hLen), backedDeficit_identity]
  simp only [backedCount, List.nil_prefix, decide_true, List.filter_true,
    backedReturn, if_true] at *
  nlinarith

end AgentUCTPaper
end
end CompleteProofSource16

/-!
## SOURCE 17: AgentUCTPaper/TreeAllocation.lean
Original definitions, theorem statements, and complete proof bodies.
-/
section CompleteProofSource17

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
  -- Q2.2: The low-count child's bonus exceeds H + 2; Q >= 0 and penalty <= H make its index exceed 2.
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
    -- Q2.3: The selected child has Q <= 1 and a nonnegative penalty; its bonus must exceed 1 to reach that index.
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
  -- Q2.4: If the target still has count <= m at U, every selected child in the window has a logarithmic count bound.
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
  -- Q2.5: Sum the possible selections over children; the result is smaller than U - L, a contradiction.
  simp only [Nat.card_Ico] at hSize
  linarith

end Counts

end AgentUCTPaper
end
end CompleteProofSource17

/-!
## SOURCE 18: AgentUCTPaper/TreeWindow.lean
Original definitions, theorem statements, and complete proof bodies.
-/
section CompleteProofSource18

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
end
end CompleteProofSource18

/-!
## SOURCE 19: AgentUCTPaper/TreeCacheVisit.lean
Original definitions, theorem statements, and complete proof bodies.
-/
section CompleteProofSource19

/-! # Why next-edge cost vanishes at visited children

This derives the degeneracy from the actual shared event history, instead of assuming
zero penalties. Complete descendant evaluation can still require uncached resources.
-/

set_option autoImplicit false

noncomputable section

namespace AgentUCTPaper

open Finset

variable {Qid Action : Type*} [DecidableEq Qid] [DecidableEq Action]

omit [DecidableEq Qid] in
theorem executionPrefixes_mem_iff (path p : List Action) :
    p ∈ executionPrefixes path ↔ p ≠ [] ∧ p <+: path := by
  constructor
  · intro hp
    obtain ⟨i, hi, rfl⟩ := mem_image.mp hp
    obtain ⟨hi1, hiLen⟩ := mem_Icc.mp hi
    refine ⟨?_, List.take_prefix i path⟩
    intro hNil
    have hlen := congrArg List.length hNil
    simp only [List.length_take, Nat.min_eq_left hiLen, List.length_nil] at hlen
    omega
  · rintro ⟨hne, hp⟩
    have hpos := List.length_pos_iff.mpr hne
    exact mem_image.mpr ⟨p.length, mem_Icc.mpr ⟨hpos, hp.length_le⟩,
      (List.prefix_iff_eq_take.mp hp).symm⟩

omit [DecidableEq Qid] in
theorem panelDemand_prefix_mono (qids : Finset Qid) (short long : List Action)
    (hPath : short <+: long) : panelDemand qids short ⊆ panelDemand qids long := by
  intro ⟨q, p⟩ hp
  obtain ⟨hq, hp⟩ := (panelDemand_mem qids short p q).mp hp
  obtain ⟨hne, hpre⟩ := (executionPrefixes_mem_iff short p).mp hp
  exact (panelDemand_mem qids long p q).mpr
    ⟨hq, (executionPrefixes_mem_iff long p).mpr ⟨hne, hpre.trans hPath⟩⟩

theorem replayMetered_initial_cache_subset (qids : Finset Qid)
    (executionPath : List Action → List Action) (weight : Qid × List Action → ℝ)
    (overhead : TreeEvaluation Action → ℝ) (events : List (TreeEvaluation Action))
    (initial : MeteredTreeState Qid Action) :
    initial.materialized ⊆
      (replayMetered qids executionPath weight overhead events initial).materialized := by
  induction events generalizing initial with
  | nil => exact subset_rfl
  | cons event events ih =>
    exact (subset_union_left : initial.materialized ⊆
      (meterStep qids executionPath weight overhead initial event).materialized).trans
        (ih (meterStep qids executionPath weight overhead initial event))

theorem replayMetered_event_demand_subset (qids : Finset Qid)
    (executionPath : List Action → List Action) (weight : Qid × List Action → ℝ)
    (overhead : TreeEvaluation Action → ℝ) (events : List (TreeEvaluation Action))
    (initial : MeteredTreeState Qid Action) (event : TreeEvaluation Action) (he : event ∈ events) :
    panelDemand qids (executionPath event.terminal) ⊆
      (replayMetered qids executionPath weight overhead events initial).materialized := by
  induction events generalizing initial with
  | nil => simp at he
  | cons head events ih =>
    rcases List.mem_cons.mp he with rfl | he
    · exact (subset_union_right : panelDemand qids (executionPath event.terminal) ⊆
        (meterStep qids executionPath weight overhead initial event).materialized).trans
          (replayMetered_initial_cache_subset qids executionPath weight overhead events
            (meterStep qids executionPath weight overhead initial event))
    · exact ih (meterStep qids executionPath weight overhead initial head) he

theorem visited_prefix_demand_cached (qids : Finset Qid) (root : List Action)
    (weight : Qid × List Action → ℝ) (overhead : TreeEvaluation Action → ℝ)
    (events : List (TreeEvaluation Action)) (initial : MeteredTreeState Qid Action)
    (p : List Action) (hVisited : 0 < backedCount events p) :
    panelDemand qids (root ++ p) ⊆
      (replayMetered qids (fun x ↦ root ++ x) weight overhead events initial).materialized := by
  have hSome : ∃ e ∈ events, p <+: e.expanded := by
    by_contra! hMiss
    have hZero : backedCount events p = 0 := by
      simpa [backedCount, List.filter_eq_nil_iff] using hMiss
    omega
  obtain ⟨event, he, hp⟩ := hSome
  have hFull : root ++ p <+: root ++ event.terminal :=
    (List.prefix_append_right_inj root).mpr (hp.trans event.expanded_is_prefix)
  exact (panelDemand_prefix_mono qids _ _ hFull).trans
    (replayMetered_event_demand_subset qids (fun x ↦ root ++ x) weight overhead events initial
      event he)

theorem visited_prefix_no_cold_cost (qids : Finset Qid) (root : List Action)
    (weight : Qid × List Action → ℝ) (overhead : TreeEvaluation Action → ℝ)
    (events : List (TreeEvaluation Action)) (initial : MeteredTreeState Qid Action)
    (p : List Action) (hVisited : 0 < backedCount events p) :
    coldWork weight
      (replayMetered qids (fun x ↦ root ++ x) weight overhead events initial).materialized
      (panelDemand qids (root ++ p)) = 0 :=
  cached_demand_is_free weight _ _
    (visited_prefix_demand_cached qids root weight overhead events initial p hVisited)

/-- Exact production next-edge formula; this statement does not include future overhead. -/
theorem visited_child_next_edge_zero (qids : Finset Qid) (root : List Action)
    (weight : Qid × List Action → ℝ) (overhead : TreeEvaluation Action → ℝ)
    (events : List (TreeEvaluation Action)) (initial : MeteredTreeState Qid Action)
    (p : List Action) (a : Action) (hWeight : ∀ r, 0 ≤ weight r)
    (hVisited : 0 < backedCount events (p ++ [a])) :
    let cached :=
      (replayMetered qids (fun x ↦ root ++ x) weight overhead events initial).materialized
    max 0 (coldWork weight cached (panelDemand qids (root ++ (p ++ [a]))) -
      coldWork weight cached (panelDemand qids (root ++ p))) = 0 := by
  dsimp only
  rw [visited_prefix_no_cold_cost qids root weight overhead events initial _ hVisited]
  have hNonneg := coldWork_nonnegative weight hWeight
    (replayMetered qids (fun x ↦ root ++ x) weight overhead events initial).materialized
    (panelDemand qids (root ++ p))
  exact max_eq_left (by linarith)

/-- This does not require calibrated predictions or equality of physical and predicted weights. -/
theorem visited_child_any_forecast_next_edge_zero (qids : Finset Qid) (root : List Action)
    (physicalWeight forecastWeight : Qid × List Action → ℝ)
    (overhead : TreeEvaluation Action → ℝ) (events : List (TreeEvaluation Action))
    (initial : MeteredTreeState Qid Action) (p : List Action) (a : Action)
    (hForecast : ∀ r, 0 ≤ forecastWeight r) (hVisited : 0 < backedCount events (p ++ [a])) :
    let cached :=
      (replayMetered qids (fun x ↦ root ++ x) physicalWeight overhead events initial).materialized
    max 0 (coldWork forecastWeight cached (panelDemand qids (root ++ (p ++ [a]))) -
      coldWork forecastWeight cached (panelDemand qids (root ++ p))) = 0 := by
  dsimp only
  have hFree := cached_demand_is_free forecastWeight _ _
    (visited_prefix_demand_cached qids root physicalWeight overhead events initial _ hVisited)
  rw [hFree]
  have hNonneg := coldWork_nonnegative forecastWeight hForecast
    (replayMetered qids (fun x ↦ root ++ x) physicalWeight overhead events initial).materialized
    (panelDemand qids (root ++ p))
  exact max_eq_left (by linarith)

/-- Actual backed-up visits and actual restorable-cache state supply the premises above. -/
theorem actual_visited_child_next_edge_zero (qids : Finset Qid) (root : List Action)
    (physicalWeight forecastWeight : Qid × List Action → ℝ)
    (overhead : TreeEvaluation Action → ℝ) (events : List (TreeEvaluation Action))
    (initial : MeteredTreeState Qid Action) (caches : PersistentCaches Qid Action)
    (p : List Action) (a : Action) (hStats : initial.stats = emptyStatistics)
    (hCache : caches.restorable = caches.everMaterialized)
    (hLedger : caches.everMaterialized = initial.materialized)
    (hForecast : ∀ r, 0 ≤ forecastWeight r)
    (hVisited : 0 < ((replayMetered qids (fun x ↦ root ++ x) physicalWeight overhead events
      initial).stats (p ++ [a])).visits) :
    let cached := (replayPublished qids (fun x ↦ root ++ x) events caches).restorable
    max 0 (coldWork forecastWeight cached (panelDemand qids (root ++ (p ++ [a]))) -
      coldWork forecastWeight cached (panelDemand qids (root ++ p))) = 0 := by
  dsimp only
  rw [replayPublished_cache_matches_metered qids (fun x ↦ root ++ x) physicalWeight overhead
    events caches initial hCache hLedger]
  have hCount : 0 < backedCount events (p ++ [a]) := by
    rw [replayMetered_stats, replayBackup_visits, hStats] at hVisited
    simpa [emptyStatistics] using hVisited
  exact visited_child_any_forecast_next_edge_zero qids root physicalWeight forecastWeight overhead
    events initial p a hForecast hCount

end AgentUCTPaper
end
end CompleteProofSource19

/-!
## SOURCE 20: AgentUCTPaper/TreeHistory.lean
Original definitions, theorem statements, and complete proof bodies.
-/
section CompleteProofSource20

/-! # Deriving local child histories from whole-tree events -/

set_option autoImplicit false

noncomputable section

namespace AgentUCTPaper

variable {Action : Type*} [DecidableEq Action]

def childAfter (p path : List Action) : Option Action :=
  if p <+: path then (path.drop p.length).head? else none

theorem childAfter_self (p : List Action) : childAfter p p = none := by
  simp [childAfter]

theorem childAfter_append (p : List Action) (a : Action) (tail : List Action) :
    childAfter p (p ++ a :: tail) = some a := by
  simp [childAfter]

theorem childAfter_some_iff (p path : List Action) (a : Action) :
    childAfter p path = some a ↔ p ++ [a] <+: path := by
  constructor
  · intro h
    unfold childAfter at h
    split_ifs at h with hp
    · obtain ⟨tail, ht⟩ := List.head?_eq_some_iff.mp h
      have hPath := (List.prefix_iff_eq_append.mp hp).symm
      rw [ht] at hPath
      rw [hPath]
      exact ⟨tail, by simp⟩
  · intro h
    obtain ⟨tail, rfl⟩ := h
    simpa [List.append_assoc] using childAfter_append p a tail

theorem prefix_eq_or_childAfter (p path : List Action) (h : p <+: path) :
    path = p ∨ ∃ a, childAfter p path = some a := by
  obtain ⟨tail, rfl⟩ := h
  cases tail with
  | nil => simp
  | cons a tail => exact Or.inr ⟨a, childAfter_append p a tail⟩

def localActions (events : List (TreeEvaluation Action)) (p : List Action) : List Action :=
  events.filterMap (fun event ↦ childAfter p event.expanded)

def actionOccurrences (actions : List Action) (a : Action) : ℕ :=
  (actions.filter (fun x ↦ decide (x = a))).length

def birthCount (events : List (TreeEvaluation Action)) (p : List Action) : ℕ :=
  (events.filter (fun event ↦ decide (event.expanded = p))).length

theorem localActions_append (before after : List (TreeEvaluation Action)) (p : List Action) :
    localActions (before ++ after) p = localActions before p ++ localActions after p := by
  simp [localActions]

theorem localActions_child_count (events : List (TreeEvaluation Action))
    (p : List Action) (a : Action) :
    actionOccurrences (localActions events p) a = backedCount events (p ++ [a]) := by
  induction events with
  | nil => simp [localActions, actionOccurrences, backedCount]
  | cons event events ih =>
    cases h : childAfter p event.expanded with
    | none =>
      have hn : ¬ p ++ [a] <+: event.expanded := by
        intro hp
        have hs := (childAfter_some_iff p event.expanded a).mpr hp
        simp [h] at hs
      simpa [localActions, actionOccurrences, backedCount, h, hn] using ih
    | some b =>
      have hChild : p ++ [a] <+: event.expanded ↔ b = a := by
        rw [← childAfter_some_iff, h, Option.some.injEq]
      by_cases hb : b = a
      · simp [localActions, actionOccurrences, backedCount, h, hChild, hb] at ih ⊢
        omega
      · simpa [localActions, actionOccurrences, backedCount, h, hChild, hb] using ih

/-- Child observations are the same terminal evaluations selected through that local action. -/
theorem child_event_subsequence (events : List (TreeEvaluation Action))
    (p : List Action) (a : Action) :
    events.filter (fun e ↦ decide (childAfter p e.expanded = some a)) =
      events.filter (fun e ↦ decide (p ++ [a] <+: e.expanded)) := by
  simp only [childAfter_some_iff]

theorem parent_count_decomposition (events : List (TreeEvaluation Action)) (p : List Action) :
    backedCount events p = (localActions events p).length + birthCount events p := by
  induction events with
  | nil => simp [backedCount, localActions, birthCount]
  | cons event events ih =>
    by_cases hp : p <+: event.expanded
    · rcases prefix_eq_or_childAfter p event.expanded hp with he | ⟨a, ha⟩
      · simp [backedCount, localActions, birthCount, he, childAfter_self] at ih ⊢
        omega
      · have hne : event.expanded ≠ p := by
          intro he
          simp [he, childAfter_self] at ha
        simp [backedCount, localActions, birthCount, hp, ha, hne] at ih ⊢
        omega
    · have hne : event.expanded ≠ p := by
        intro he
        exact hp (he ▸ List.prefix_refl _)
      have hn : childAfter p event.expanded = none := by simp [childAfter, hp]
      simpa [backedCount, localActions, birthCount, hp, hn, hne] using ih

/-- An internal node contributes a birth rollout at most once, and never after it already exists. -/
theorem nonterminal_birth_count (terminal : List Action → Prop)
    (events : List (TreeEvaluation Action)) (initial : Finset (List Action))
    (p : List Action) (hNonterminal : ¬ terminal p) (hLegal : LegalTreeRun terminal initial events) :
    birthCount events p ≤ if p ∈ initial then 0 else 1 := by
  induction events generalizing initial with
  | nil => simp [birthCount]
  | cons event events ih =>
    have ht := ih (growTree initial event) hLegal.2
    by_cases he : event.expanded = p
    · have hAbsent : p ∉ initial := by
        rcases hLegal.1.2 with hOld | ⟨q, hq, a, ha, hNew⟩
        · exact (hNonterminal (he ▸ hOld.2)).elim
        · simpa [he] using hNew
      simp [growTree, he] at ht
      simp [birthCount, he, hAbsent]
      simpa [birthCount] using ht
    · have he' : p ≠ event.expanded := Ne.symm he
      simpa [birthCount, growTree, he, he'] using ht

theorem parent_count_birth_offset (terminal : List Action → Prop)
    (events : List (TreeEvaluation Action)) (initial : Finset (List Action))
    (p : List Action) (hNonterminal : ¬ terminal p) (hLegal : LegalTreeRun terminal initial events) :
    ∃ offset : ℕ, offset ≤ 1 ∧
      backedCount events p = (localActions events p).length + offset := by
  refine ⟨birthCount events p, ?_, parent_count_decomposition events p⟩
  have h := nonterminal_birth_count terminal events initial p hNonterminal hLegal
  split_ifs at h <;> omega

theorem root_count_has_zero_offset (terminal : List Action → Prop)
    (events : List (TreeEvaluation Action)) (hRoot : ¬ terminal [])
    (hLegal : LegalTreeRun terminal {[]} events) :
    backedCount events [] = (localActions events []).length := by
  have h := nonterminal_birth_count terminal events {[]} [] hRoot hLegal
  simp at h
  simpa [h] using parent_count_decomposition events []

def historyOf (action : ℕ → Action) (n : ℕ) : List Action := (List.range n).map action

theorem pullCount_historyOf (action : ℕ → Action) (a : Action) (n : ℕ) :
    AgentUCT.pullCount action a n = actionOccurrences (historyOf action n) a := by
  induction n with
  | zero => simp [AgentUCT.pullCount, actionOccurrences, historyOf]
  | succ n ih =>
    by_cases h : action n = a
    · simp [AgentUCT.pullCount, Finset.range_add_one, Finset.filter_insert,
        actionOccurrences, historyOf,
        List.range_succ, h] at ih ⊢
      exact ih
    · simp [AgentUCT.pullCount, Finset.range_add_one, Finset.filter_insert,
        actionOccurrences, historyOf,
        List.range_succ, h] at ih ⊢
      exact ih

/-- No auxiliary count process: any stream extending the projected history has the same counts. -/
theorem operational_child_visits_eq_pullCount (events : List (TreeEvaluation Action))
    (p : List Action) (a : Action) (action : ℕ → Action) (n : ℕ)
    (hHistory : localActions events p = historyOf action n) :
    (replayBackup events emptyStatistics (p ++ [a])).visits = AgentUCT.pullCount action a n := by
  rw [replayBackup_visits, pullCount_historyOf, ← hHistory, localActions_child_count]
  simp [emptyStatistics]

def extendHistory (history : List Action) (fallback : Action) (n : ℕ) : Action :=
  history[n]?.getD fallback

omit [DecidableEq Action] in
theorem historyOf_extendHistory_take (history : List Action) (fallback : Action)
    (n : ℕ) (hn : n ≤ history.length) :
    historyOf (extendHistory history fallback) n = history.take n := by
  apply List.ext_getElem
  · simp [historyOf, List.length_take, Nat.min_eq_left hn]
  · intro i hi hj
    have hin : i < n := by simpa [historyOf] using hi
    have hix : i < history.length := lt_of_lt_of_le hin hn
    simp [historyOf, extendHistory, List.getElem?_eq_getElem hix]

omit [DecidableEq Action] in
theorem historyOf_extendHistory (history : List Action) (fallback : Action) :
    historyOf (extendHistory history fallback) history.length = history := by
  simpa using historyOf_extendHistory_take history fallback history.length le_rfl

theorem localActions_prefix (before all : List (TreeEvaluation Action)) (p : List Action)
    (hPrefix : before <+: all) : localActions before p <+: localActions all p :=
  List.IsPrefix.filterMap (fun event : TreeEvaluation Action ↦ childAfter p event.expanded) hPrefix

/-- The local stream is constructed from this tree history, not supplied independently. -/
theorem local_history_before_global_prefix (events : List (TreeEvaluation Action))
    (p : List Action) (fallback : Action) (t : ℕ) :
    localActions (events.take t) p =
      historyOf (extendHistory (localActions events p) fallback)
        (localActions (events.take t) p).length := by
  have hp := localActions_prefix (events.take t) events p (List.take_prefix t events)
  rw [historyOf_extendHistory_take _ _ _ hp.length_le]
  exact List.prefix_iff_eq_take.mp hp

theorem child_visits_at_global_time (events : List (TreeEvaluation Action))
    (p : List Action) (a fallback : Action) (t : ℕ) :
    (replayBackup (events.take t) emptyStatistics (p ++ [a])).visits =
      AgentUCT.pullCount (extendHistory (localActions events p) fallback) a
        (localActions (events.take t) p).length :=
  operational_child_visits_eq_pullCount _ p a _ _
    (local_history_before_global_prefix events p fallback t)

omit [DecidableEq Action] in
theorem extendHistory_append_next (before after : List Action) (a fallback : Action) :
    extendHistory (before ++ a :: after) fallback before.length = a := by
  simp [extendHistory]

theorem local_chosen_action (before after : List (TreeEvaluation Action))
    (event : TreeEvaluation Action) (p : List Action) (a fallback : Action)
    (hChild : childAfter p event.expanded = some a) :
    extendHistory (localActions (before ++ event :: after) p) fallback
      (localActions before p).length = a := by
  simp [localActions, hChild, extendHistory]

theorem exists_backed_event_of_count_pos (events : List (TreeEvaluation Action))
    (p : List Action) (hCount : 0 < backedCount events p) :
    ∃ event ∈ events, p <+: event.expanded := by
  by_contra! hMiss
  have hZero : backedCount events p = 0 := by
    simpa [backedCount, List.filter_eq_nil_iff] using hMiss
  omega

theorem backed_node_in_replayTree (terminal : List Action → Prop)
    (events : List (TreeEvaluation Action)) (p : List Action)
    (hLegal : LegalTreeRun terminal {[]} events) (hCount : 0 < backedCount events p) :
    p ∈ replayTree events {[]} := by
  obtain ⟨event, he, hp⟩ := exists_backed_event_of_count_pos events p hCount
  exact replayTree_prefixClosed terminal events {[]} root_prefixClosed hLegal event.expanded
    ((replayTree_mem events {[]} event.expanded).mpr (Or.inr ⟨event, he, rfl⟩)) p hp

theorem visited_nonroot_birth_count_one (terminal : List Action → Prop)
    (events : List (TreeEvaluation Action)) (p : List Action)
    (hLegal : LegalTreeRun terminal {[]} events) (hNonterminal : ¬ terminal p)
    (hNonroot : p ≠ []) (hCount : 0 < backedCount events p) : birthCount events p = 1 := by
  have hNode := backed_node_in_replayTree terminal events p hLegal hCount
  obtain ⟨event, he, hp⟩ : ∃ event ∈ events, p = event.expanded := by
    have h := (replayTree_mem events {[]} p).mp hNode
    simpa [hNonroot] using h
  have hBirth : 0 < birthCount events p := by
    apply List.length_pos_iff.mpr
    intro hNil
    have hm : event ∈ events.filter (fun e ↦ decide (e.expanded = p)) := by
      simp [he, hp]
    simp [hNil] at hm
  have hUpper := nonterminal_birth_count terminal events {[]} p hNonterminal hLegal
  simp [hNonroot] at hUpper
  omega

/-- After a non-root internal node is born, the offset is exactly one, not a changing bias. -/
theorem visited_parent_count_exact_offset (terminal : List Action → Prop)
    (events : List (TreeEvaluation Action)) (p : List Action)
    (hLegal : LegalTreeRun terminal {[]} events) (hNonterminal : ¬ terminal p)
    (hCount : 0 < backedCount events p) :
    backedCount events p = (localActions events p).length + if p = [] then 0 else 1 := by
  by_cases hRoot : p = []
  · subst p
    simpa using root_count_has_zero_offset terminal events hNonterminal hLegal
  · rw [parent_count_decomposition,
      visited_nonroot_birth_count_one terminal events p hLegal hNonterminal hRoot hCount]
    simp [hRoot]

end AgentUCTPaper
end
end CompleteProofSource20

/-!
## SOURCE 21: AgentUCTPaper/TreeTopology.lean
Original definitions, theorem statements, and complete proof bodies.
-/
section CompleteProofSource21

/-! # Finite workflow topology, legal local arms, and descendant maxima -/

set_option autoImplicit false

noncomputable section

namespace AgentUCTPaper

open Finset

variable {Action : Type*} [DecidableEq Action]

def workflowNodes (terminals : Finset (List Action)) : Finset (List Action) :=
  terminals.biUnion (fun leaf ↦ insert [] (executionPrefixes leaf))

def availableChildren (terminals : Finset (List Action)) (p : List Action) : Finset Action :=
  terminals.biUnion (fun leaf ↦ (childAfter p leaf).toFinset)

abbrev ChildArm (terminals : Finset (List Action)) (p : List Action) :=
  ↥(availableChildren terminals p)

theorem workflowNodes_mem (terminals : Finset (List Action)) (p : List Action) :
    p ∈ workflowNodes terminals ↔ ∃ leaf ∈ terminals, p <+: leaf := by
  simp only [workflowNodes, mem_biUnion, mem_insert, executionPrefixes_mem_iff]
  constructor
  · rintro ⟨leaf, hl, hp | hp⟩
    · subst p
      exact ⟨leaf, hl, List.nil_prefix⟩
    · exact ⟨leaf, hl, hp.2⟩
  · rintro ⟨leaf, hl, hp⟩
    refine ⟨leaf, hl, ?_⟩
    by_cases h : p = []
    · exact Or.inl h
    · exact Or.inr ⟨h, hp⟩

theorem availableChildren_mem (terminals : Finset (List Action)) (p : List Action) (a : Action) :
    a ∈ availableChildren terminals p ↔ ∃ leaf ∈ terminals, p ++ [a] <+: leaf := by
  simp [availableChildren, Option.mem_def, childAfter_some_iff]

theorem legal_child_is_node (terminals : Finset (List Action)) (p : List Action) (a : Action)
    (ha : a ∈ availableChildren terminals p) : p ++ [a] ∈ workflowNodes terminals := by
  rw [workflowNodes_mem]
  exact (availableChildren_mem terminals p a).mp ha

theorem legal_child_has_terminals (terminals : Finset (List Action)) (p : List Action) (a : Action)
    (ha : a ∈ availableChildren terminals p) : (subtreeTerminals terminals (p ++ [a])).Nonempty := by
  obtain ⟨leaf, hl, hp⟩ := (availableChildren_mem terminals p a).mp ha
  exact ⟨leaf, mem_filter.mpr ⟨hl, hp⟩⟩

theorem internal_has_child (terminals : Finset (List Action)) (p : List Action)
    (hNode : p ∈ workflowNodes terminals) (hInternal : p ∉ terminals) :
    (availableChildren terminals p).Nonempty := by
  obtain ⟨leaf, hl, hp⟩ := (workflowNodes_mem terminals p).mp hNode
  rcases prefix_eq_or_childAfter p leaf hp with he | ⟨a, ha⟩
  · exact (hInternal (he ▸ hl)).elim
  · exact ⟨a, (availableChildren_mem terminals p a).mpr
      ⟨leaf, hl, (childAfter_some_iff p leaf a).mp ha⟩⟩

theorem terminal_has_no_child (terminals : Finset (List Action))
    (hAntichain : ∀ p ∈ terminals, ∀ q ∈ terminals, p <+: q → p = q)
    (p : List Action) (hp : p ∈ terminals) : availableChildren terminals p = ∅ := by
  apply Finset.eq_empty_iff_forall_notMem.mpr
  intro a ha
  obtain ⟨leaf, hl, hpre⟩ := (availableChildren_mem terminals p a).mp ha
  have he := hAntichain p hp leaf hl ((List.prefix_append p [a]).trans hpre)
  have hlen := hpre.length_le
  simp [← he] at hlen

theorem subtreeValue_bounded (terminals : Finset (List Action)) (reward : List Action → ℝ)
    (hReward : ∀ leaf ∈ terminals, 0 ≤ reward leaf ∧ reward leaf ≤ 1) (p : List Action) :
    0 ≤ subtreeValue terminals reward p ∧ subtreeValue terminals reward p ≤ 1 := by
  by_cases h : (subtreeTerminals terminals p).Nonempty
  · obtain ⟨leaf, hl, _, he⟩ := subtreeValue_attained terminals reward p h
    rw [he]
    exact hReward leaf hl
  · simp [subtreeValue, h]

theorem subtreeValue_child_le (terminals : Finset (List Action)) (reward : List Action → ℝ)
    (p : List Action) (a : Action) (ha : a ∈ availableChildren terminals p) :
    subtreeValue terminals reward (p ++ [a]) ≤ subtreeValue terminals reward p := by
  obtain ⟨leaf, hl, hp, he⟩ := subtreeValue_attained terminals reward (p ++ [a])
    (legal_child_has_terminals terminals p a ha)
  rw [he]
  exact subtreeValue_upper terminals reward p leaf hl ((List.prefix_append p [a]).trans hp)

theorem internal_has_optimal_child (terminals : Finset (List Action)) (reward : List Action → ℝ)
    (p : List Action) (hNode : p ∈ workflowNodes terminals) (hInternal : p ∉ terminals) :
    ∃ a ∈ availableChildren terminals p,
      subtreeValue terminals reward (p ++ [a]) = subtreeValue terminals reward p := by
  obtain ⟨someLeaf, hs, hp⟩ := (workflowNodes_mem terminals p).mp hNode
  have hn : (subtreeTerminals terminals p).Nonempty := ⟨someLeaf, mem_filter.mpr ⟨hs, hp⟩⟩
  obtain ⟨leaf, hl, hp, he⟩ := subtreeValue_attained terminals reward p hn
  rcases prefix_eq_or_childAfter p leaf hp with hEq | ⟨a, ha⟩
  · exact (hInternal (hEq ▸ hl)).elim
  · have hpre := (childAfter_some_iff p leaf a).mp ha
    have hLegal := (availableChildren_mem terminals p a).mpr ⟨leaf, hl, hpre⟩
    refine ⟨a, hLegal, le_antisymm (subtreeValue_child_le terminals reward p a hLegal) ?_⟩
    rw [he]
    exact subtreeValue_upper terminals reward (p ++ [a]) leaf hl hpre

def edgeGap (terminals : Finset (List Action)) (reward : List Action → ℝ)
    (p : List Action) (a : Action) : ℝ :=
  subtreeValue terminals reward p - subtreeValue terminals reward (p ++ [a])

theorem edgeGap_nonnegative (terminals : Finset (List Action)) (reward : List Action → ℝ)
    (p : List Action) (a : Action) (ha : a ∈ availableChildren terminals p) :
    0 ≤ edgeGap terminals reward p a :=
  sub_nonneg.mpr (subtreeValue_child_le terminals reward p a ha)

theorem edgeGap_le_one (terminals : Finset (List Action)) (reward : List Action → ℝ)
    (hReward : ∀ leaf ∈ terminals, 0 ≤ reward leaf ∧ reward leaf ≤ 1)
    (p : List Action) (a : Action) : edgeGap terminals reward p a ≤ 1 := by
  have hp := subtreeValue_bounded terminals reward hReward p
  have hc := subtreeValue_bounded terminals reward hReward (p ++ [a])
  unfold edgeGap
  linarith

theorem finite_tree_positive_edge_gap (terminals : Finset (List Action))
    (reward : List Action → ℝ) :
    ∃ delta : ℝ, 0 < delta ∧ ∀ p ∈ workflowNodes terminals, ∀ a ∈ availableChildren terminals p,
      0 < edgeGap terminals reward p a → delta ≤ edgeGap terminals reward p a := by
  classical
  let gaps := (workflowNodes terminals).biUnion
    (fun p ↦ (availableChildren terminals p).image (edgeGap terminals reward p))
  obtain ⟨delta, hd, hBound⟩ := finite_positive_gap gaps
  refine ⟨delta, hd, ?_⟩
  intro p hp a ha hpos
  exact hBound _ (mem_biUnion.mpr ⟨p, hp, mem_image.mpr ⟨a, ha, rfl⟩⟩) hpos

def topologyDepth (terminals : Finset (List Action)) : ℕ := terminals.sup List.length

theorem node_length_le_depth (terminals : Finset (List Action)) (p : List Action)
    (hp : p ∈ workflowNodes terminals) : p.length ≤ topologyDepth terminals := by
  obtain ⟨leaf, hl, hpre⟩ := (workflowNodes_mem terminals p).mp hp
  exact hpre.length_le.trans (Finset.le_sup hl)

theorem child_remaining_depth_lt (terminals : Finset (List Action)) (p : List Action) (a : Action)
    (ha : a ∈ availableChildren terminals p) :
    topologyDepth terminals - (p ++ [a]).length < topologyDepth terminals - p.length := by
  have h := node_length_le_depth terminals (p ++ [a]) (legal_child_is_node terminals p a ha)
  simp only [List.length_append, List.length_singleton] at h ⊢
  omega

theorem projected_action_is_legal (terminals : Finset (List Action))
    (events : List (TreeEvaluation Action))
    (hTerminal : ∀ event ∈ events, event.terminal ∈ terminals) (p : List Action)
    (a : Action) (ha : a ∈ localActions events p) : a ∈ availableChildren terminals p := by
  obtain ⟨event, he, hAction⟩ := List.mem_filterMap.mp ha
  have hp := (childAfter_some_iff p event.expanded a).mp hAction
  exact (availableChildren_mem terminals p a).mpr
    ⟨event.terminal, hTerminal event he, hp.trans event.expanded_is_prefix⟩

theorem childArm_card (terminals : Finset (List Action)) (p : List Action) :
    Fintype.card (ChildArm terminals p) = (availableChildren terminals p).card := by
  simp [ChildArm]

end AgentUCTPaper
end
end CompleteProofSource21

/-!
## SOURCE 22: AgentUCTPaper/TreeDecomposition.lean
Original definitions, theorem statements, and complete proof bodies.
-/
section CompleteProofSource22

/-! # Exact recursive decomposition of backed-up terminal-quality loss -/

set_option autoImplicit false

noncomputable section

namespace AgentUCTPaper

open Finset

variable {Action : Type*} [DecidableEq Action]

def birthDeficit (value : ℝ) (events : List (TreeEvaluation Action)) (p : List Action) : ℝ :=
  (events.map (fun event ↦ if event.expanded = p then value - event.reward else 0)).sum

theorem backedDeficit_cons (value : ℝ) (event : TreeEvaluation Action)
    (events : List (TreeEvaluation Action)) (p : List Action) :
    backedDeficit value (event :: events) p =
      (if p <+: event.expanded then value - event.reward else 0) + backedDeficit value events p := rfl

theorem birthDeficit_cons (value : ℝ) (event : TreeEvaluation Action)
    (events : List (TreeEvaluation Action)) (p : List Action) :
    birthDeficit value (event :: events) p =
      (if event.expanded = p then value - event.reward else 0) + birthDeficit value events p := rfl

theorem event_child_partition (terminals : Finset (List Action))
    (event : TreeEvaluation Action) (hTerminal : event.terminal ∈ terminals)
    (p : List Action) (value : ℝ) :
    (if p <+: event.expanded then value - event.reward else 0) =
      (if event.expanded = p then value - event.reward else 0) +
        ∑ a ∈ availableChildren terminals p,
          if p ++ [a] <+: event.expanded then value - event.reward else 0 := by
  by_cases hp : p <+: event.expanded
  · rcases prefix_eq_or_childAfter p event.expanded hp with he | ⟨a, ha⟩
    · have hNoChild : ∀ a : Action, ¬ p ++ [a] <+: p := by
        intro a hpre
        have hlen := hpre.length_le
        simp at hlen
      simp [he, hNoChild]
    · have hNe : event.expanded ≠ p := by
        intro he
        simp [he, childAfter_self] at ha
      have hLegal : a ∈ availableChildren terminals p :=
        (availableChildren_mem terminals p a).mpr ⟨event.terminal, hTerminal,
          ((childAfter_some_iff p event.expanded a).mp ha).trans event.expanded_is_prefix⟩
      have hOnly : ∀ b : Action, p ++ [b] <+: event.expanded ↔ b = a := by
        intro b
        rw [← childAfter_some_iff, ha, Option.some.injEq, eq_comm]
      simp [hp, hNe, hOnly, hLegal]
  · have hNe : event.expanded ≠ p := by
      intro he
      exact hp (he ▸ List.prefix_refl _)
    have hNoChild : ∀ a : Action, ¬ p ++ [a] <+: event.expanded := by
      exact fun a hpre ↦ hp ((List.prefix_append p [a]).trans hpre)
    simp [hp, hNe, hNoChild]

theorem parent_deficit_partition (terminals : Finset (List Action))
    (events : List (TreeEvaluation Action))
    (hTerminal : ∀ event ∈ events, event.terminal ∈ terminals) (p : List Action) (value : ℝ) :
    backedDeficit value events p = birthDeficit value events p +
      ∑ a ∈ availableChildren terminals p, backedDeficit value events (p ++ [a]) := by
  induction events with
  | nil => simp [backedDeficit, birthDeficit]
  | cons event events ih =>
    have hTail := ih (fun e he ↦ hTerminal e (by simp [he]))
    have hHead := event_child_partition terminals event (hTerminal event (by simp)) p value
    simp_rw [backedDeficit_cons, birthDeficit_cons]
    rw [Finset.sum_add_distrib]
    linarith

/-- Parent and children use the same global history and operational visit counts. -/
theorem operational_subtree_deficit_decomposition (terminals : Finset (List Action))
    (reward : List Action → ℝ) (events : List (TreeEvaluation Action))
    (hTerminal : ∀ event ∈ events, event.terminal ∈ terminals) (p : List Action) :
    backedDeficit (subtreeValue terminals reward p) events p =
      birthDeficit (subtreeValue terminals reward p) events p +
        ∑ a ∈ availableChildren terminals p,
          ((backedCount events (p ++ [a]) : ℝ) * edgeGap terminals reward p a +
            backedDeficit (subtreeValue terminals reward (p ++ [a])) events (p ++ [a])) := by
  rw [parent_deficit_partition terminals events hTerminal p]
  congr 1
  apply Finset.sum_congr rfl
  intro a _
  rw [backedDeficit_identity, backedDeficit_identity]
  unfold edgeGap
  ring

theorem birthDeficit_le_birthCount (value : ℝ) (hValue : value ≤ 1)
    (events : List (TreeEvaluation Action)) (hReward : ∀ e ∈ events, 0 ≤ e.reward)
    (p : List Action) : birthDeficit value events p ≤ birthCount events p := by
  induction events with
  | nil => simp [birthDeficit, birthCount]
  | cons event events ih =>
    have hTail := ih (fun e he ↦ hReward e (by simp [he]))
    have hHead := hReward event (by simp)
    by_cases he : event.expanded = p
    · simp [birthDeficit, birthCount, he] at hTail ⊢
      linarith
    · simpa [birthDeficit, birthCount, he] using hTail

theorem subtree_birthDeficit_nonnegative (terminals : Finset (List Action))
    (reward : List Action → ℝ) (events : List (TreeEvaluation Action))
    (hTable : FixedTableEvents terminals reward events) (p : List Action) :
    0 ≤ birthDeficit (subtreeValue terminals reward p) events p := by
  apply List.sum_nonneg
  intro x hx
  obtain ⟨event, he, rfl⟩ := List.mem_map.mp hx
  split_ifs with hp
  · rw [(hTable event he).2]
    exact sub_nonneg.mpr (subtreeValue_upper terminals reward p event.terminal
      (hTable event he).1 (hp ▸ event.expanded_is_prefix))
  · exact le_rfl

theorem internal_birthDeficit_le_one (terminals : Finset (List Action))
    (reward : List Action → ℝ)
    (hReward : ∀ leaf ∈ terminals, 0 ≤ reward leaf ∧ reward leaf ≤ 1)
    (events : List (TreeEvaluation Action)) (hTable : FixedTableEvents terminals reward events)
    (hLegal : LegalTreeRun (fun p ↦ p ∈ terminals) {[]} events)
    (p : List Action) (hInternal : p ∉ terminals) :
    birthDeficit (subtreeValue terminals reward p) events p ≤ 1 := by
  have hScores : ∀ e ∈ events, 0 ≤ e.reward := by
    intro e he
    rw [(hTable e he).2]
    exact (hReward e.terminal (hTable e he).1).1
  have hb := birthDeficit_le_birthCount _
    (subtreeValue_bounded terminals reward hReward p).2 events hScores p
  have hc := nonterminal_birth_count (fun p ↦ p ∈ terminals) events {[]} p hInternal hLegal
  have hc1 : birthCount events p ≤ 1 := by split_ifs at hc <;> omega
  exact hb.trans (by exact_mod_cast hc1)

theorem root_birthDeficit_zero (terminals : Finset (List Action)) (reward : List Action → ℝ)
    (hReward : ∀ leaf ∈ terminals, 0 ≤ reward leaf ∧ reward leaf ≤ 1)
    (events : List (TreeEvaluation Action)) (hTable : FixedTableEvents terminals reward events)
    (hLegal : LegalTreeRun (fun p ↦ p ∈ terminals) {[]} events) (hRoot : [] ∉ terminals) :
    birthDeficit (subtreeValue terminals reward []) events [] = 0 := by
  have hScores : ∀ e ∈ events, 0 ≤ e.reward := by
    intro e he
    rw [(hTable e he).2]
    exact (hReward e.terminal (hTable e he).1).1
  have hb := birthDeficit_le_birthCount _
    (subtreeValue_bounded terminals reward hReward []).2 events hScores []
  have hc := nonterminal_birth_count (fun p ↦ p ∈ terminals) events {[]} [] hRoot hLegal
  simp at hc
  rw [hc] at hb
  norm_num at hb
  have hn := subtree_birthDeficit_nonnegative terminals reward events hTable []
  exact le_antisymm hb hn

end AgentUCTPaper
end
end CompleteProofSource22

/-!
## SOURCE 23: AgentUCTPaper/TreePolicy.lean
Original definitions, theorem statements, and complete proof bodies.
-/
section CompleteProofSource23

/-! # The observed UCT decisions projected to a finite local action stream -/

set_option autoImplicit false

noncomputable section

namespace AgentUCTPaper

variable {Action : Type*} [DecidableEq Action]

omit [DecidableEq Action] in
theorem filterMap_step_exists {Item : Type*} (items : List Item) (f : Item → Option Action)
    (n : ℕ) (hn : n < (items.filterMap f).length) :
    ∃ before event after a, items = before ++ event :: after ∧
      (before.filterMap f).length = n ∧ f event = some a := by
  induction items generalizing n with
  | nil => simp at hn
  | cons event items ih =>
    cases h : f event with
    | none =>
      have ht : n < (items.filterMap f).length := by simpa [h] using hn
      obtain ⟨before, next, after, a, hs, ht, ha⟩ := ih n ht
      exact ⟨event :: before, next, after, a, by simp [hs], by simp [h, ht], ha⟩
    | some a =>
      cases n with
      | zero => exact ⟨[], event, items, a, by simp, by simp, h⟩
      | succ n =>
        have ht : n < (items.filterMap f).length := by simpa [h] using hn
        obtain ⟨before, next, after, b, hs, ht, hb⟩ := ih n ht
        exact ⟨event :: before, next, after, b, by simp [hs], by simp [h, ht], hb⟩

structure LocalStep (events : List (TreeEvaluation Action)) (p : List Action) (n : ℕ) where
  before : List (TreeEvaluation Action)
  event : TreeEvaluation Action
  after : List (TreeEvaluation Action)
  chosen : Action
  split : events = before ++ event :: after
  time : (localActions before p).length = n
  child : childAfter p event.expanded = some chosen

theorem localStep_nonempty (events : List (TreeEvaluation Action)) (p : List Action) (n : ℕ)
    (hn : n < (localActions events p).length) : Nonempty (LocalStep events p n) := by
  obtain ⟨before, event, after, a, hs, ht, ha⟩ :=
    filterMap_step_exists events (fun e ↦ childAfter p e.expanded) n hn
  exact ⟨⟨before, event, after, a, hs, ht, ha⟩⟩

def observedLocalStep (events : List (TreeEvaluation Action)) (p : List Action) (n : ℕ)
    (hn : n < (localActions events p).length) : LocalStep events p n :=
  Classical.choice (localStep_nonempty events p n hn)

def localBefore (events : List (TreeEvaluation Action)) (p : List Action) (n : ℕ) :
    List (TreeEvaluation Action) :=
  if hn : n < (localActions events p).length then (observedLocalStep events p n hn).before
  else events

theorem localBefore_prefix (events : List (TreeEvaluation Action)) (p : List Action) (n : ℕ) :
    localBefore events p n <+: events := by
  unfold localBefore
  split_ifs with hn
  · exact ⟨_, (observedLocalStep events p n hn).split.symm⟩
  · exact List.prefix_refl _

theorem localBefore_time (events : List (TreeEvaluation Action)) (p : List Action) (n : ℕ)
    (hn : n < (localActions events p).length) :
    (localActions (localBefore events p n) p).length = n := by
  simpa [localBefore, hn] using (observedLocalStep events p n hn).time

theorem localBefore_history (events : List (TreeEvaluation Action)) (p : List Action)
    (fallback : Action) (n : ℕ) (hn : n < (localActions events p).length) :
    localActions (localBefore events p n) p =
      historyOf (extendHistory (localActions events p) fallback) n := by
  have hp := localActions_prefix _ _ p (localBefore_prefix events p n)
  have ht := localBefore_time events p n hn
  rw [historyOf_extendHistory_take _ _ _ hn.le]
  simpa only [ht] using List.prefix_iff_eq_take.mp hp

theorem localBefore_child_count (events : List (TreeEvaluation Action)) (p : List Action)
    (a fallback : Action) (n : ℕ) (hn : n < (localActions events p).length) :
    (replayBackup (localBefore events p n) emptyStatistics (p ++ [a])).visits =
      AgentUCT.pullCount (extendHistory (localActions events p) fallback) a n :=
  operational_child_visits_eq_pullCount _ p a _ n
    (localBefore_history events p fallback n hn)

theorem legalTreeRun_append (terminal : List Action → Prop)
    (before after : List (TreeEvaluation Action)) (initial : Finset (List Action)) :
    LegalTreeRun terminal initial (before ++ after) ↔
      LegalTreeRun terminal initial before ∧
        LegalTreeRun terminal (replayTree before initial) after := by
  induction before generalizing initial with
  | nil => simp [LegalTreeRun, replayTree]
  | cons event before ih =>
    simp [LegalTreeRun, replayTree, ih, and_assoc]

theorem legalTreeRun_prefix (terminal : List Action → Prop)
    (before events : List (TreeEvaluation Action)) (initial : Finset (List Action))
    (hp : before <+: events) (hLegal : LegalTreeRun terminal initial events) :
    LegalTreeRun terminal initial before := by
  obtain ⟨after, rfl⟩ := hp
  exact (legalTreeRun_append terminal before after initial).mp hLegal |>.1

theorem localBefore_parent_count (terminals : Finset (List Action))
    (events : List (TreeEvaluation Action)) (p : List Action) (n : ℕ)
    (hLegal : LegalTreeRun (fun p ↦ p ∈ terminals) {[]} events)
    (hInternal : p ∉ terminals) (hPos : 0 < n) (hn : n < (localActions events p).length) :
    (replayBackup (localBefore events p n) emptyStatistics p).visits =
      n + if p = [] then 0 else 1 := by
  have hPrefix := legalTreeRun_prefix _ _ _ _ (localBefore_prefix events p n) hLegal
  have ht := localBefore_time events p n hn
  have hCount : 0 < backedCount (localBefore events p n) p := by
    rw [parent_count_decomposition, ht]
    omega
  simpa [replayBackup_visits, emptyStatistics, ht] using
    visited_parent_count_exact_offset _ _ p hPrefix hInternal hCount

omit [DecidableEq Action] in
theorem extendHistory_mem (arms : Finset Action) (history : List Action) (fallback : Action)
    (hHistory : ∀ a ∈ history, a ∈ arms) (hFallback : fallback ∈ arms) (n : ℕ) :
    extendHistory history fallback n ∈ arms := by
  unfold extendHistory
  cases h : history[n]? with
  | none => simpa [h] using hFallback
  | some a => simpa [h] using hHistory a (List.mem_of_getElem? h)

def restrictActions (arms : Finset Action) (action : ℕ → Action)
    (hAction : ∀ n, action n ∈ arms) : ℕ → ↥arms := fun n ↦ ⟨action n, hAction n⟩

theorem restrictActions_count (arms : Finset Action) (action : ℕ → Action)
    (hAction : ∀ n, action n ∈ arms) (a : ↥arms) (n : ℕ) :
    AgentUCT.pullCount (restrictActions arms action hAction) a n =
      AgentUCT.pullCount action a.val n := by
  unfold AgentUCT.pullCount
  congr 1
  ext t
  simp [restrictActions, Subtype.ext_iff]

/-- Exactly the selection conditions, with observed backup statistics and a predictable bill. -/
def TreeAllocationRule (terminals : Finset (List Action)) (c : ℝ)
    (penalty : List (TreeEvaluation Action) → List Action → Action → ℝ)
    (events : List (TreeEvaluation Action)) : Prop :=
  ∀ before event after, events = before ++ event :: after →
    ∀ p a, childAfter p event.expanded = some a →
      (∀ b ∈ availableChildren terminals p,
        (replayBackup before emptyStatistics (p ++ [b])).visits = 0 →
          (replayBackup before emptyStatistics (p ++ [a])).visits = 0) ∧
      ((∀ b ∈ availableChildren terminals p,
          0 < (replayBackup before emptyStatistics (p ++ [b])).visits) →
        ∀ b ∈ availableChildren terminals p,
          treeIndex (replayBackup before emptyStatistics (p ++ [b])).mean c
            (penalty before p b) (replayBackup before emptyStatistics p).visits
            (replayBackup before emptyStatistics (p ++ [b])).visits ≤
          treeIndex (replayBackup before emptyStatistics (p ++ [a])).mean c
            (penalty before p a) (replayBackup before emptyStatistics p).visits
            (replayBackup before emptyStatistics (p ++ [a])).visits)

theorem projected_unvisited_first (terminals : Finset (List Action)) (c : ℝ)
    (penalty : List (TreeEvaluation Action) → List Action → Action → ℝ)
    (events : List (TreeEvaluation Action)) (p : List Action) (fallback : Action)
    (hRule : TreeAllocationRule terminals c penalty events) (n : ℕ)
    (hn : n < (localActions events p).length) (b : Action)
    (hb : b ∈ availableChildren terminals p)
    (hZero : AgentUCT.pullCount (extendHistory (localActions events p) fallback) b n = 0) :
    AgentUCT.pullCount (extendHistory (localActions events p) fallback)
      (extendHistory (localActions events p) fallback n) n = 0 := by
  let step := observedLocalStep events p n hn
  have hChosen : extendHistory (localActions events p) fallback n = step.chosen := by
    have hs := local_chosen_action step.before step.after step.event p
      step.chosen fallback step.child
    simpa only [step.time, ← step.split] using hs
  have hBefore : localBefore events p n = step.before := by simp [localBefore, hn, step]
  have hCounts := localBefore_child_count events p b fallback n hn
  rw [hBefore, hZero] at hCounts
  have hDecision := (hRule step.before step.event step.after step.split
    p step.chosen step.child).1 b hb hCounts
  rw [← hChosen, ← hBefore, localBefore_child_count events p _ fallback n hn] at hDecision
  exact hDecision

theorem projected_index_max (terminals : Finset (List Action)) (c : ℝ)
    (penalty : List (TreeEvaluation Action) → List Action → Action → ℝ)
    (events : List (TreeEvaluation Action)) (p : List Action) (fallback : Action)
    (hRule : TreeAllocationRule terminals c penalty events)
    (hLegal : LegalTreeRun (fun p ↦ p ∈ terminals) {[]} events)
    (hInternal : p ∉ terminals) (n : ℕ) (hPos : 0 < n)
    (hn : n < (localActions events p).length)
    (hInitialized : ∀ a ∈ availableChildren terminals p,
      0 < AgentUCT.pullCount (extendHistory (localActions events p) fallback) a n)
    (b : Action) (hb : b ∈ availableChildren terminals p) :
    let action := extendHistory (localActions events p) fallback
    let before := localBefore events p n
    treeIndex (replayBackup before emptyStatistics (p ++ [b])).mean c (penalty before p b)
      (n + if p = [] then 0 else 1) (AgentUCT.pullCount action b n) ≤
    treeIndex (replayBackup before emptyStatistics (p ++ [action n])).mean c
      (penalty before p (action n)) (n + if p = [] then 0 else 1)
      (AgentUCT.pullCount action (action n) n) := by
  dsimp only
  let step := observedLocalStep events p n hn
  have hChosen : extendHistory (localActions events p) fallback n = step.chosen := by
    have hs := local_chosen_action step.before step.after step.event p
      step.chosen fallback step.child
    simpa only [step.time, ← step.split] using hs
  have hBefore : localBefore events p n = step.before := by simp [localBefore, hn, step]
  have hInit : ∀ a ∈ availableChildren terminals p,
      0 < (replayBackup step.before emptyStatistics (p ++ [a])).visits := by
    intro a ha
    rw [← hBefore, localBefore_child_count events p a fallback n hn]
    exact hInitialized a ha
  have hDecision := (hRule step.before step.event step.after step.split
    p step.chosen step.child).2 hInit b hb
  rw [← hChosen, ← hBefore,
    localBefore_parent_count terminals events p n hLegal hInternal hPos hn,
    localBefore_child_count events p b fallback n hn,
    localBefore_child_count events p _ fallback n hn] at hDecision
  exact hDecision

end AgentUCTPaper
end
end CompleteProofSource23

/-!
## SOURCE 24: AgentUCTPaper/TreeExploration.lean
Original definitions, theorem statements, and complete proof bodies.
-/
section CompleteProofSource24

/-! # Exploration derived from the actual finite tree run -/

set_option autoImplicit false

noncomputable section

namespace AgentUCTPaper

variable {Action : Type*} [DecidableEq Action]

structure BoundedTreeRun (terminals : Finset (List Action)) (c H : ℝ)
    (penalty : List (TreeEvaluation Action) → List Action → Action → ℝ)
    (events : List (TreeEvaluation Action)) : Prop where
  terminal : ∀ event ∈ events, event.terminal ∈ terminals
  reward : ∀ event ∈ events, 0 ≤ event.reward ∧ event.reward ≤ 1
  legal : LegalTreeRun (fun p ↦ p ∈ terminals) {[]} events
  rule : TreeAllocationRule terminals c penalty events
  penalty_bounded : ∀ before, before <+: events → ∀ p, ∀ a ∈ availableChildren terminals p,
    0 ≤ penalty before p a ∧ penalty before p a ≤ H

theorem treeAllocationRule_prefix (terminals : Finset (List Action)) (c : ℝ)
    (penalty : List (TreeEvaluation Action) → List Action → Action → ℝ)
    (before events : List (TreeEvaluation Action)) (hp : before <+: events)
    (hRule : TreeAllocationRule terminals c penalty events) :
    TreeAllocationRule terminals c penalty before := by
  obtain ⟨tail, rfl⟩ := hp
  intro past event after hs p a ha
  apply hRule past event (after ++ tail) _ p a ha
  simp [hs, List.append_assoc]

theorem BoundedTreeRun.prefix {terminals : Finset (List Action)} {c H : ℝ}
    {penalty : List (TreeEvaluation Action) → List Action → Action → ℝ}
    {events before : List (TreeEvaluation Action)}
    (run : BoundedTreeRun terminals c H penalty events) (hp : before <+: events) :
    BoundedTreeRun terminals c H penalty before where
  terminal e he := run.terminal e (hp.subset he)
  reward e he := run.reward e (hp.subset he)
  legal := legalTreeRun_prefix _ _ _ _ hp run.legal
  rule := treeAllocationRule_prefix terminals c penalty before events hp run.rule
  penalty_bounded past ht := run.penalty_bounded past (ht.trans hp)

def legalLocalStream (terminals : Finset (List Action))
    (events : List (TreeEvaluation Action)) (p : List Action) (fallback : ChildArm terminals p)
    (hTerminal : ∀ event ∈ events, event.terminal ∈ terminals) : ℕ → ChildArm terminals p :=
  restrictActions (availableChildren terminals p)
    (extendHistory (localActions events p) fallback.val)
    (extendHistory_mem _ _ _ (projected_action_is_legal terminals events hTerminal p)
      fallback.property)

theorem legalLocalStream_count (terminals : Finset (List Action))
    (events : List (TreeEvaluation Action)) (p : List Action) (fallback : ChildArm terminals p)
    (hTerminal : ∀ event ∈ events, event.terminal ∈ terminals)
    (a : ChildArm terminals p) (n : ℕ) :
    AgentUCT.pullCount (legalLocalStream terminals events p fallback hTerminal) a n =
      AgentUCT.pullCount (extendHistory (localActions events p) fallback.val) a.val n :=
  restrictActions_count _ _ _ a n

theorem operational_local_initialized (terminals : Finset (List Action)) (c H : ℝ)
    (penalty : List (TreeEvaluation Action) → List Action → Action → ℝ)
    (events : List (TreeEvaluation Action)) (run : BoundedTreeRun terminals c H penalty events)
    (p : List Action) (fallback : ChildArm terminals p)
    (hEnough : Fintype.card (ChildArm terminals p) ≤ (localActions events p).length) :
    ∀ a, 0 < AgentUCT.pullCount (legalLocalStream terminals events p fallback run.terminal)
      a (Fintype.card (ChildArm terminals p)) := by
  apply initialized_after_unvisited_first
  intro t ht a ha
  rw [legalLocalStream_count] at ha ⊢
  exact projected_unvisited_first terminals c penalty events p fallback.val run.rule t
    (ht.trans_le hEnough) a.val a.property ha

/-- This is an actual child-visitation theorem, not an independently assumed bandit process. -/
theorem actual_children_explored (terminals : Finset (List Action)) (c H : ℝ)
    (penalty : List (TreeEvaluation Action) → List Action → Action → ℝ)
    (events : List (TreeEvaluation Action)) (run : BoundedTreeRun terminals c H penalty events)
    (hc : 0 < c) (hH : 0 ≤ H) (p : List Action) (hInternal : p ∉ terminals)
    (m : ℕ) (hEnough : 2 * explorationWindowStart c H
      (Fintype.card (ChildArm terminals p)) m ≤ (localActions events p).length)
    (a : Action) (ha : a ∈ availableChildren terminals p) :
    m < backedCount events (p ++ [a]) := by
  let fallback : ChildArm terminals p := ⟨a, ha⟩
  let action := legalLocalStream terminals events p fallback run.terminal
  let horizon := (localActions events p).length
  let K := Fintype.card (ChildArm terminals p)
  let q : ℕ → ChildArm terminals p → ℝ := fun n b ↦
    (replayBackup (localBefore events p n) emptyStatistics (p ++ [b.val])).mean
  let costs : ℕ → ChildArm terminals p → ℝ := fun n b ↦ penalty (localBefore events p n) p b.val
  have hKPos : 0 < K := Fintype.card_pos_iff.mpr ⟨fallback⟩
  have hKEnough : K ≤ horizon := by
    have h := (explorationWindow_bounds c H K m).1
    have hKL : K ≤ explorationWindowStart c H K m := by
      have hr : (K : ℝ) ≤ explorationWindowStart c H K m := by linarith
      exact_mod_cast hr
    change 2 * explorationWindowStart c H K m ≤ horizon at hEnough
    omega
  have hInit := operational_local_initialized terminals c H penalty events run p fallback hKEnough
  have hResult := finite_explicit_window_explores action q costs c H
    (if p = [] then 0 else 1) m horizon fallback hc hH (by split_ifs <;> omega) hEnough hInit
    (by
      intro t ht b
      exact replayBackup_mean_mem_unit _
        (fun e he ↦ run.reward e ((localBefore_prefix events p t).subset he)) _)
    (by
      intro t ht b
      exact run.penalty_bounded _ (localBefore_prefix events p t) p b.val b.property)
    (by
      intro t ht hKt b
      have hCounts : ∀ b ∈ availableChildren terminals p,
          0 < AgentUCT.pullCount (extendHistory (localActions events p) fallback.val) b t := by
        intro b hb
        have hi := (hInit ⟨b, hb⟩).trans_le (pullCount_monotone action ⟨b, hb⟩ hKt)
        simpa only [action, legalLocalStream_count] using hi
      have hMax := projected_index_max terminals c penalty events p fallback.val run.rule
        run.legal hInternal t (lt_of_lt_of_le hKPos hKt) ht hCounts b.val b.property
      simpa only [action, q, costs, legalLocalStream_count] using hMax)
  have hCount : AgentUCT.pullCount action fallback horizon = backedCount events (p ++ [a]) := by
    rw [legalLocalStream_count, pullCount_historyOf, historyOf_extendHistory]
    exact localActions_child_count events p a
  rwa [hCount] at hResult

end AgentUCTPaper
end
end CompleteProofSource24

/-!
## SOURCE 25: AgentUCTPaper/TreeCoverage.lean
Original definitions, theorem statements, and complete proof bodies.
-/
section CompleteProofSource25

/-! # Explicit recursive coverage and cache saturation of the actual run -/

set_option autoImplicit false

noncomputable section

namespace AgentUCTPaper

open Finset

variable {Action : Type*} [DecidableEq Action]

def coverageVisits (terminals : Finset (List Action)) (c H : ℝ) : ℕ → ℕ
  | 0 => 1
  | depth + 1 => 1 + (workflowNodes terminals).sup (fun p ↦
      2 * explorationWindowStart c H (Fintype.card (ChildArm terminals p))
        (coverageVisits terminals c H depth))

theorem coverageVisits_positive (terminals : Finset (List Action)) (c H : ℝ) (depth : ℕ) :
    0 < coverageVisits terminals c H depth := by
  cases depth <;> simp only [coverageVisits] <;> omega

theorem actual_subtree_coverage (terminals : Finset (List Action)) (c H : ℝ)
    (penalty : List (TreeEvaluation Action) → List Action → Action → ℝ)
    (events : List (TreeEvaluation Action)) (run : BoundedTreeRun terminals c H penalty events)
    (hc : 0 < c) (hH : 0 ≤ H)
    (hAntichain : ∀ p ∈ terminals, ∀ q ∈ terminals, p <+: q → p = q)
    (depth : ℕ) (p : List Action) (hNode : p ∈ workflowNodes terminals)
    (hDepth : topologyDepth terminals - p.length ≤ depth)
    (hCount : coverageVisits terminals c H depth ≤ backedCount events p) :
    ∀ leaf ∈ terminals, p <+: leaf → 0 < backedCount events leaf := by
  induction depth generalizing p with
  -- Q3.1: Induct on remaining depth; the terminal antichain forces a terminal observation to be that terminal itself.
  | zero =>
    intro leaf hl hp
    have hlen := node_length_le_depth terminals leaf
      ((workflowNodes_mem terminals leaf).mpr ⟨leaf, hl, List.prefix_refl _⟩)
    have he : p = leaf := hp.eq_of_length_le (by omega)
    subst leaf
    exact (coverageVisits_positive terminals c H 0).trans_le hCount
  | succ depth ih =>
    intro leaf hl hp
    by_cases hTerminal : p ∈ terminals
    · have he := hAntichain p hTerminal leaf hl hp
      subst leaf
      exact (coverageVisits_positive terminals c H (depth + 1)).trans_le hCount
    · rcases prefix_eq_or_childAfter p leaf hp with he | ⟨a, ha⟩
      · exact (hTerminal (he ▸ hl)).elim
      · have hChildPath := (childAfter_some_iff p leaf a).mp ha
        have hChild := (availableChildren_mem terminals p a).mpr ⟨leaf, hl, hChildPath⟩
        have hWindow : 2 * explorationWindowStart c H (Fintype.card (ChildArm terminals p))
            (coverageVisits terminals c H depth) ≤
            (workflowNodes terminals).sup (fun q ↦
              2 * explorationWindowStart c H (Fintype.card (ChildArm terminals q))
                (coverageVisits terminals c H depth)) :=
          Finset.le_sup (f := fun q ↦
            2 * explorationWindowStart c H (Fintype.card (ChildArm terminals q))
              (coverageVisits terminals c H depth)) hNode
        have hBirth := nonterminal_birth_count (fun p ↦ p ∈ terminals) events {[]} p
          hTerminal run.legal
        -- Q3.2: Remove the parent's at-most-one birth event; enough visits remain for the entire exploration window.
        have hDecomp := parent_count_decomposition events p
        have hEnough : 2 * explorationWindowStart c H (Fintype.card (ChildArm terminals p))
            (coverageVisits terminals c H depth) ≤ (localActions events p).length := by
          simp only [coverageVisits] at hCount
          split_ifs at hBirth <;> omega
        have hChildN := actual_children_explored terminals c H penalty events run hc hH p
          hTerminal (coverageVisits terminals c H depth) hEnough a hChild
        have hChildDepth := child_remaining_depth_lt terminals p a hChild
        -- Q3.3: Each child exceeds the recursive coverage threshold; apply induction at its smaller remaining depth.
        exact ih (p ++ [a]) (legal_child_is_node terminals p a hChild) (by omega)
          hChildN.le leaf hl hChildPath

theorem root_count_eq_length (events : List (TreeEvaluation Action)) :
    backedCount events [] = events.length := by simp [backedCount]

theorem actual_terminal_coverage (terminals : Finset (List Action)) (c H : ℝ)
    (penalty : List (TreeEvaluation Action) → List Action → Action → ℝ)
    (events : List (TreeEvaluation Action)) (run : BoundedTreeRun terminals c H penalty events)
    (hc : 0 < c) (hH : 0 ≤ H)
    (hAntichain : ∀ p ∈ terminals, ∀ q ∈ terminals, p <+: q → p = q)
    (hCount : coverageVisits terminals c H (topologyDepth terminals) ≤ events.length) :
    ∀ leaf ∈ terminals, 0 < backedCount events leaf := by
  intro leaf hl
  apply actual_subtree_coverage terminals c H penalty events run hc hH hAntichain
    (topologyDepth terminals) []
    ((workflowNodes_mem terminals []).mpr ⟨leaf, hl, List.nil_prefix⟩)
    (by simp) (by simpa [root_count_eq_length] using hCount) leaf hl List.nil_prefix

theorem visited_terminal_observed (terminals : Finset (List Action))
    (events : List (TreeEvaluation Action))
    (hTerminal : ∀ event ∈ events, event.terminal ∈ terminals)
    (hAntichain : ∀ p ∈ terminals, ∀ q ∈ terminals, p <+: q → p = q)
    (leaf : List Action) (hl : leaf ∈ terminals) (hCount : 0 < backedCount events leaf) :
    ∃ event ∈ events, event.terminal = leaf := by
  obtain ⟨event, he, hp⟩ := exists_backed_event_of_count_pos events leaf hCount
  exact ⟨event, he, (hAntichain leaf hl event.terminal (hTerminal event he)
    (hp.trans event.expanded_is_prefix)).symm⟩

variable {Qid : Type*} [DecidableEq Qid]

def workflowResources (qids : Finset Qid) (root : List Action)
    (terminals : Finset (List Action)) : Finset (Qid × List Action) :=
  terminals.biUnion (fun leaf ↦ panelDemand qids (root ++ leaf))

theorem actual_cache_coverage (qids : Finset Qid) (root : List Action)
    (terminals : Finset (List Action)) (c H : ℝ)
    (penalty : List (TreeEvaluation Action) → List Action → Action → ℝ)
    (physicalWeight : Qid × List Action → ℝ) (overhead : TreeEvaluation Action → ℝ)
    (events : List (TreeEvaluation Action)) (initial : MeteredTreeState Qid Action)
    (run : BoundedTreeRun terminals c H penalty events) (hc : 0 < c) (hH : 0 ≤ H)
    (hAntichain : ∀ p ∈ terminals, ∀ q ∈ terminals, p <+: q → p = q)
    (hCount : coverageVisits terminals c H (topologyDepth terminals) ≤ events.length) :
    workflowResources qids root terminals ⊆
      (replayMetered qids (fun x ↦ root ++ x) physicalWeight overhead events initial).materialized := by
  intro resource hr
  obtain ⟨leaf, hl, hd⟩ := mem_biUnion.mp hr
  exact visited_prefix_demand_cached qids root physicalWeight overhead events initial leaf
    (actual_terminal_coverage terminals c H penalty events run hc hH hAntichain hCount leaf hl) hd

theorem actual_restorable_coverage (qids : Finset Qid) (root : List Action)
    (terminals : Finset (List Action)) (c H : ℝ)
    (penalty : List (TreeEvaluation Action) → List Action → Action → ℝ)
    (physicalWeight : Qid × List Action → ℝ) (overhead : TreeEvaluation Action → ℝ)
    (events : List (TreeEvaluation Action)) (initial : MeteredTreeState Qid Action)
    (caches : PersistentCaches Qid Action)
    (hCache : caches.restorable = caches.everMaterialized)
    (hLedger : caches.everMaterialized = initial.materialized)
    (run : BoundedTreeRun terminals c H penalty events) (hc : 0 < c) (hH : 0 ≤ H)
    (hAntichain : ∀ p ∈ terminals, ∀ q ∈ terminals, p <+: q → p = q)
    (hCount : coverageVisits terminals c H (topologyDepth terminals) ≤ events.length) :
    workflowResources qids root terminals ⊆
      (replayPublished qids (fun x ↦ root ++ x) events caches).restorable := by
  -- Q4.1: Persistent caches identify published resources with restorable resources, turning publication coverage into restoration coverage.
  rw [replayPublished_cache_matches_metered qids (fun x ↦ root ++ x) physicalWeight overhead
    events caches initial hCache hLedger]
  exact actual_cache_coverage qids root terminals c H penalty physicalWeight overhead events
    initial run hc hH hAntichain hCount

end AgentUCTPaper
end
end CompleteProofSource25

/-!
## SOURCE 26: AgentUCTPaper/TreeForecast.lean
Original definitions, theorem statements, and complete proof bodies.
-/
section CompleteProofSource26

/-! # Reference completion costs attached to the actual persistent cache -/

set_option autoImplicit false

noncomputable section

namespace AgentUCTPaper

open Finset

variable {Qid Action : Type*} [DecidableEq Qid] [DecidableEq Action]

def referenceColdCost (qids : Finset Qid) (root : List Action)
    (terminals : Finset (List Action)) (prediction : Qid × List Action → ℝ)
    (law : List Action → ℝ) (cached : Finset (Qid × List Action)) (p : List Action) : ℝ :=
  ∑ leaf ∈ subtreeTerminals terminals p,
    law leaf * coldWork prediction cached (panelDemand qids (root ++ leaf))

theorem terminal_demand_subset_resources (qids : Finset Qid) (root : List Action)
    (terminals : Finset (List Action)) (leaf : List Action) (hl : leaf ∈ terminals) :
    panelDemand qids (root ++ leaf) ⊆ workflowResources qids root terminals := by
  intro r hr
  exact mem_biUnion.mpr ⟨leaf, hl, hr⟩

theorem referenceColdCost_bounded (qids : Finset Qid) (root : List Action)
    (terminals : Finset (List Action)) (prediction : Qid × List Action → ℝ)
    (hPrediction : ∀ r, 0 ≤ prediction r) (law : List Action → ℝ)
    (cached : Finset (Qid × List Action)) (p : List Action)
    (hLaw : ∀ leaf ∈ subtreeTerminals terminals p, 0 ≤ law leaf)
    (hMass : ∑ leaf ∈ subtreeTerminals terminals p, law leaf = 1) :
    0 ≤ referenceColdCost qids root terminals prediction law cached p ∧
      referenceColdCost qids root terminals prediction law cached p ≤
        cacheWeight prediction (workflowResources qids root terminals) := by
  constructor
  · exact sum_nonneg (fun leaf hl ↦ mul_nonneg (hLaw leaf hl)
      (coldWork_nonnegative prediction hPrediction _ _))
  · unfold referenceColdCost
    calc
      _ ≤ ∑ leaf ∈ subtreeTerminals terminals p,
          law leaf * cacheWeight prediction (workflowResources qids root terminals) := by
        apply sum_le_sum
        intro leaf hl
        apply mul_le_mul_of_nonneg_left _ (hLaw leaf hl)
        exact (coldWork_le_fullWork prediction hPrediction _ _).trans
          (cacheWeight_mono prediction hPrediction
            (terminal_demand_subset_resources qids root terminals leaf (mem_filter.mp hl).1))
      _ = _ := by rw [← sum_mul, hMass, one_mul]

theorem referenceColdCost_zero (qids : Finset Qid) (root : List Action)
    (terminals : Finset (List Action)) (prediction : Qid × List Action → ℝ)
    (law : List Action → ℝ) (cached : Finset (Qid × List Action)) (p : List Action)
    (hCache : workflowResources qids root terminals ⊆ cached) :
    referenceColdCost qids root terminals prediction law cached p = 0 := by
  apply sum_eq_zero
  intro leaf hl
  rw [cached_demand_is_free prediction cached _
    ((terminal_demand_subset_resources qids root terminals leaf (mem_filter.mp hl).1).trans hCache)]
  exact mul_zero _

def coldForecastPenalty (qids : Finset Qid) (root : List Action)
    (terminals : Finset (List Action)) (prediction : Qid × List Action → ℝ) (gamma : ℝ)
    (law : List (TreeEvaluation Action) → List Action → Action → List Action → ℝ)
    (initial : PersistentCaches Qid Action) (before : List (TreeEvaluation Action))
    (p : List Action) (a : Action) : ℝ :=
  gamma * referenceColdCost qids root terminals prediction (law before p a)
    (replayPublished qids (fun x ↦ root ++ x) before initial).restorable (p ++ [a])

theorem coldForecastPenalty_bounded (qids : Finset Qid) (root : List Action)
    (terminals : Finset (List Action)) (prediction : Qid × List Action → ℝ)
    (hPrediction : ∀ r, 0 ≤ prediction r) (gamma : ℝ) (hGamma : 0 ≤ gamma)
    (law : List (TreeEvaluation Action) → List Action → Action → List Action → ℝ)
    (initial : PersistentCaches Qid Action) (before : List (TreeEvaluation Action))
    (p : List Action) (a : Action)
    (hLaw : ∀ leaf ∈ subtreeTerminals terminals (p ++ [a]), 0 ≤ law before p a leaf)
    (hMass : ∑ leaf ∈ subtreeTerminals terminals (p ++ [a]), law before p a leaf = 1) :
    0 ≤ coldForecastPenalty qids root terminals prediction gamma law initial before p a ∧
      coldForecastPenalty qids root terminals prediction gamma law initial before p a ≤
        gamma * cacheWeight prediction (workflowResources qids root terminals) := by
  obtain ⟨h0, h1⟩ := referenceColdCost_bounded qids root terminals prediction hPrediction
    (law before p a) _ (p ++ [a]) hLaw hMass
  exact ⟨mul_nonneg hGamma h0, mul_le_mul_of_nonneg_left h1 hGamma⟩

/-- Zero follows from proved operational coverage, independently of forecast calibration. -/
theorem coldForecastPenalty_after_coverage (qids : Finset Qid) (root : List Action)
    (terminals : Finset (List Action)) (prediction : Qid × List Action → ℝ) (gamma c H : ℝ)
    (law : List (TreeEvaluation Action) → List Action → Action → List Action → ℝ)
    (initial : PersistentCaches Qid Action)
    (hCache : initial.restorable = initial.everMaterialized)
    (events : List (TreeEvaluation Action))
    (run : BoundedTreeRun terminals c H
      (coldForecastPenalty qids root terminals prediction gamma law initial) events)
    (hc : 0 < c) (hH : 0 ≤ H)
    (hAntichain : ∀ p ∈ terminals, ∀ q ∈ terminals, p <+: q → p = q)
    (hCount : coverageVisits terminals c H (topologyDepth terminals) ≤ events.length)
    (p : List Action) (a : Action) :
    coldForecastPenalty qids root terminals prediction gamma law initial events p a = 0 := by
  -- Q4.2: All terminal demands are restorable after coverage, so every legal completion has an empty missing set.
  have hCovered := actual_restorable_coverage qids root terminals c H
    (coldForecastPenalty qids root terminals prediction gamma law initial)
    (fun _ ↦ 0) (fun _ ↦ 0) events
    ⟨emptyStatistics, initial.everMaterialized, 0, 0⟩ initial hCache rfl run hc hH hAntichain hCount
  unfold coldForecastPenalty
  -- Q4.3: The empty finite sum is zero, and gamma times zero is zero; no forecast accuracy is needed for this step.
  rw [referenceColdCost_zero qids root terminals prediction _ _ _ hCovered, mul_zero]

end AgentUCTPaper
end
end CompleteProofSource26

/-!
## SOURCE 27: AgentUCTPaper/TreeRateAlgebra.lean
Original definitions, theorem statements, and complete proof bodies.
-/
section CompleteProofSource27

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
  -- Q5.1: The three terms in m ensure a positive denominator, A * log / n <= delta / 8, and B / n <= delta / 8.
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
  -- Q5.2: Use log(n + 1) <= 4 * sqrt(n), retaining all sign conditions when multiplying and dividing.
  apply (div_le_iff₀ hPos).mpr
  nlinarith

theorem selected_count_from_subtree_bias {qBest qChosen vBest vChosen c delta : ℝ}
    {parent bestCount chosenCount : ℕ} (hc : 0 ≤ c) (hDelta : 0 < delta)
    (hChosen : 0 < chosenCount) (hBestQ : vBest - delta / 4 ≤ qBest)
    (hChosenQ : qChosen ≤ vChosen) (hGap : delta ≤ vBest - vChosen)
    (hSelect : treeIndex qBest c 0 parent bestCount ≤ treeIndex qChosen c 0 parent chosenCount) :
    (chosenCount : ℝ) ≤ 4 * c ^ 2 * Real.log (parent + 1 : ℕ) / delta ^ 2 := by
  -- Q6.2: Gap >= delta and optimal mean loss <= delta / 4 force a large bonus for the selected suboptimal child.
  have hBestRadius := treeBonus_nonnegative hc parent bestCount
  have hChosenRadius := treeBonus_nonnegative hc parent chosenCount
  have hSquare := treeBonus_square c parent chosenCount hChosen
  have hGapBonus : delta ≤ 2 * treeBonus c parent chosenCount := by
    unfold treeIndex at hSelect
    linarith
  -- Q6.3: Check nonnegative sides before squaring, multiply by the positive count, and eliminate the square root using bonus_sq.
  have hSq : delta ^ 2 ≤ 4 * treeBonus c parent chosenCount ^ 2 := by nlinarith
  have hMul := mul_le_mul_of_nonneg_right hSq (Nat.cast_nonneg chosenCount : (0 : ℝ) ≤ _)
  apply (le_div_iff₀ (sq_pos_of_pos hDelta)).mpr
  nlinarith

theorem count_le_burnin_add_cap {Arm : Type*} [DecidableEq Arm]
    (action : ℕ → Arm) (arm : Arm) (burnin horizon : ℕ) (cap : ℝ) (hCap : 0 ≤ cap)
    (hLate : ∀ t, burnin ≤ t → t < horizon → action t = arm →
      (AgentUCT.pullCount action arm t : ℝ) ≤ cap) :
    (AgentUCT.pullCount action arm horizon : ℝ) ≤ burnin + cap + 1 := by
  -- Q6.4: Split early and late selections; late pre-selection counts are <= cap, with +1 for the final update.
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
end
end CompleteProofSource27

/-!
## SOURCE 28: AgentUCTPaper/TreeRateStep.lean
Original definitions, theorem statements, and complete proof bodies.
-/
section CompleteProofSource28

/-! # Operational induction step for a positive-gap child -/

set_option autoImplicit false

noncomputable section

namespace AgentUCTPaper

variable {Action : Type*} [DecidableEq Action]

omit [DecidableEq Action] in
theorem FixedTableEvents.prefix {terminals : Finset (List Action)} {reward : List Action → ℝ}
    {before events : List (TreeEvaluation Action)} (hTable : FixedTableEvents terminals reward events)
    (hp : before <+: events) : FixedTableEvents terminals reward before :=
  fun event he ↦ hTable event (hp.subset he)

theorem backedCount_prefix_mono (before events : List (TreeEvaluation Action)) (p : List Action)
    (hp : before <+: events) : backedCount before p ≤ backedCount events p := by
  obtain ⟨after, rfl⟩ := hp
  simp [backedCount, List.filter_append]

theorem backedCount_path_mono (events : List (TreeEvaluation Action)) (p q : List Action)
    (hp : p <+: q) : backedCount events q ≤ backedCount events p := by
  induction events with
  | nil => simp [backedCount]
  | cons event events ih =>
    by_cases hq : q <+: event.expanded
    · have hp' := hp.trans hq
      simpa [backedCount, hq, hp'] using ih
    · by_cases hp' : p <+: event.expanded
      · simp [backedCount, hq, hp'] at ih ⊢
        omega
      · simpa [backedCount, hq, hp'] using ih

theorem localBefore_global_time (events : List (TreeEvaluation Action)) (p : List Action)
    (n : ℕ) (hn : n < (localActions events p).length) : n ≤ (localBefore events p n).length := by
  calc
    n = (localActions (localBefore events p n) p).length :=
      (localBefore_time events p n hn).symm
    _ ≤ _ := List.length_filterMap_le _ _

def nodeRateBurnin (terminals : Finset (List Action)) (c H A B delta : ℝ)
    (cacheTime : ℕ) (p : List Action) : ℕ :=
  max cacheTime (2 * explorationWindowStart c H (Fintype.card (ChildArm terminals p))
    (biasVisitTarget A B delta))

theorem actual_suboptimal_child_count (terminals : Finset (List Action))
    (reward : List Action → ℝ) (c H A B delta : ℝ) (cacheTime : ℕ)
    (penalty : List (TreeEvaluation Action) → List Action → Action → ℝ)
    (events : List (TreeEvaluation Action)) (run : BoundedTreeRun terminals c H penalty events)
    (hTable : FixedTableEvents terminals reward events) (hc : 0 < c) (hH : 0 ≤ H)
    (hA : 0 ≤ A) (hDelta : 0 < delta) (p : List Action)
    (hNode : p ∈ workflowNodes terminals) (hInternal : p ∉ terminals)
    (hChildren : ∀ before, before <+: events → ∀ b ∈ availableChildren terminals p,
      backedDeficit (subtreeValue terminals reward (p ++ [b])) before (p ++ [b]) ≤
        A * Real.log (backedCount before (p ++ [b]) + 1 : ℕ) + B)
    (hZero : ∀ before, before <+: events → cacheTime ≤ before.length →
      ∀ b ∈ availableChildren terminals p, penalty before p b = 0)
    (a : Action) (ha : a ∈ availableChildren terminals p)
    (hGap : delta ≤ edgeGap terminals reward p a) :
    (backedCount events (p ++ [a]) : ℝ) ≤ nodeRateBurnin terminals c H A B delta cacheTime p +
      4 * c ^ 2 * Real.log (backedCount events p + 1 : ℕ) / delta ^ 2 + 1 := by
  -- Q6.1: The local action stream preserves actual child choices; burn-in covers cache coverage and mean-bias phases.
  let action := extendHistory (localActions events p) a
  let burnin := nodeRateBurnin terminals c H A B delta cacheTime p
  let cap := 4 * c ^ 2 * Real.log (backedCount events p + 1 : ℕ) / delta ^ 2
  have hCap : 0 ≤ cap := by
    dsimp [cap]
    apply div_nonneg
    · exact mul_nonneg (by positivity) (Real.log_nonneg (by
        exact_mod_cast Nat.le_add_left 1 (backedCount events p)))
    · positivity
  have hBound := count_le_burnin_add_cap action a burnin (localActions events p).length cap hCap
    (by
      intro t hBurn ht hSelected
      let before := localBefore events p t
      have hp : before <+: events := localBefore_prefix events p t
      have hTime : (localActions before p).length = t := localBefore_time events p t ht
      have hCacheTime : cacheTime ≤ before.length :=
        (le_max_left _ _).trans (hBurn.trans (localBefore_global_time events p t ht))
      have hEnough : 2 * explorationWindowStart c H (Fintype.card (ChildArm terminals p))
          (biasVisitTarget A B delta) ≤ (localActions before p).length := by
        rw [hTime]
        exact (le_max_right _ _).trans hBurn
      have hVisits : ∀ b ∈ availableChildren terminals p,
          biasVisitTarget A B delta < backedCount before (p ++ [b]) :=
        actual_children_explored terminals c H penalty before (run.prefix hp) hc hH p
          hInternal (biasVisitTarget A B delta) hEnough
      -- Q5: The finite exploration window makes every child exceed the bias threshold; local and backed counts agree.
      have hCounts : ∀ b, backedCount before (p ++ [b]) = AgentUCT.pullCount action b t := by
        intro b
        simpa [before, action, replayBackup_visits, emptyStatistics] using
          localBefore_child_count events p b a t ht
      have hInit : ∀ b ∈ availableChildren terminals p, 0 < AgentUCT.pullCount action b t := by
        intro b hb
        rw [← hCounts b]
        exact lt_of_le_of_lt (Nat.zero_le _) (hVisits b hb)
      have hTPos : 0 < t := by
        have hWindow := (explorationWindow_bounds c H (Fintype.card (ChildArm terminals p))
          (biasVisitTarget A B delta)).1
        have hWPos : 0 < explorationWindowStart c H (Fintype.card (ChildArm terminals p))
            (biasVisitTarget A B delta) := by
          have hReal : (0 : ℝ) < explorationWindowStart c H
              (Fintype.card (ChildArm terminals p)) (biasVisitTarget A B delta) := by
            linarith [(Nat.cast_nonneg (Fintype.card (ChildArm terminals p)) :
              (0 : ℝ) ≤ Fintype.card (ChildArm terminals p))]
          exact_mod_cast hReal
        omega
      obtain ⟨best, hBest, hOptimal⟩ := internal_has_optimal_child terminals reward p hNode hInternal
      have hBestN : 0 < backedCount before (p ++ [best]) :=
        lt_of_le_of_lt (Nat.zero_le _) (hVisits best hBest)
      have hRatio := logarithmic_deficit_small (backedCount before (p ++ [best])) hA hDelta
        (hVisits best hBest).le (hChildren before hp best hBest)
      -- The optimal child's D / N <= delta / 4 gives Q >= V(parent) - delta / 4 by the actual mean identity.
      have hBestQ : subtreeValue terminals reward p - delta / 4 ≤
          (replayBackup before emptyStatistics (p ++ [best])).mean := by
        rw [operational_mean_deficit (subtreeValue terminals reward (p ++ [best]))
          before _ hBestN]
        linarith
      have hChosenQ := operational_mean_le_subtreeValue terminals reward before (hTable.prefix hp)
        (p ++ [a]) (lt_of_le_of_lt (Nat.zero_le _) (hVisits a ha))
      have hMax := projected_index_max terminals c penalty events p a run.rule run.legal hInternal
        t hTPos ht hInit best hBest
      change treeIndex (replayBackup before emptyStatistics (p ++ [best])).mean c
        (penalty before p best) (t + if p = [] then 0 else 1) (AgentUCT.pullCount action best t) ≤
        treeIndex (replayBackup before emptyStatistics (p ++ [action t])).mean c
          (penalty before p (action t)) (t + if p = [] then 0 else 1)
          (AgentUCT.pullCount action (action t) t) at hMax
      -- Q6.2: Use actual index maximality; both completion cold penalties are zero after coverage.
      rw [hSelected, hZero before hp hCacheTime best hBest,
        hZero before hp hCacheTime a ha] at hMax
      have hCapLocal := selected_count_from_subtree_bias hc.le hDelta (hInit a ha)
        hBestQ hChosenQ hGap hMax
      -- Q6.3: The squared-bonus identity bounds the current count; the final parent logarithm dominates earlier prefixes.
      have hParent : t + (if p = [] then 0 else 1) ≤ backedCount events p := by
        have hEq := localBefore_parent_count terminals events p t run.legal hInternal hTPos ht
        have hEq' : backedCount before p = t + if p = [] then 0 else 1 := by
          simpa [replayBackup_visits, emptyStatistics, before] using hEq
        have hMono := backedCount_prefix_mono before events p hp
        rwa [hEq'] at hMono
      have hLog : Real.log (t + (if p = [] then 0 else 1) + 1 : ℕ) ≤
          Real.log (backedCount events p + 1 : ℕ) :=
        Real.log_le_log (by positivity) (by exact_mod_cast Nat.add_le_add_right hParent 1)
      exact hCapLocal.trans (div_le_div_of_nonneg_right
        (mul_le_mul_of_nonneg_left hLog (by positivity)) (sq_nonneg delta)))
  have hCount : AgentUCT.pullCount action a (localActions events p).length =
      backedCount events (p ++ [a]) := by
    rw [pullCount_historyOf, historyOf_extendHistory]
    exact localActions_child_count events p a
  -- Q6.4: Return to actual global counts; the counting lemma already includes early burn-in and the final increment +1.
  rwa [hCount] at hBound

end AgentUCTPaper
end
end CompleteProofSource28

/-!
## SOURCE 29: AgentUCTPaper/TreeRate.lean
Original definitions, theorem statements, and complete proof bodies.
-/
section CompleteProofSource29

/-! # Closing the deterministic finite-tree deficit induction -/

set_option autoImplicit false

noncomputable section

namespace AgentUCTPaper

open Finset

variable {Action : Type*} [DecidableEq Action]

theorem parent_deficit_log_bound (terminals : Finset (List Action))
    (reward : List Action → ℝ) (c H A B delta : ℝ) (cacheTime burnin : ℕ)
    (penalty : List (TreeEvaluation Action) → List Action → Action → ℝ)
    (events : List (TreeEvaluation Action)) (run : BoundedTreeRun terminals c H penalty events)
    (hTable : FixedTableEvents terminals reward events)
    (hReward : ∀ leaf ∈ terminals, 0 ≤ reward leaf ∧ reward leaf ≤ 1)
    (hc : 0 < c) (hH : 0 ≤ H) (hA : 0 ≤ A) (hDelta : 0 < delta)
    (p : List Action) (hNode : p ∈ workflowNodes terminals) (hInternal : p ∉ terminals)
    (hBurn : nodeRateBurnin terminals c H A B delta cacheTime p ≤ burnin)
    (hChildren : ∀ before, before <+: events → ∀ b ∈ availableChildren terminals p,
      backedDeficit (subtreeValue terminals reward (p ++ [b])) before (p ++ [b]) ≤
        A * Real.log (backedCount before (p ++ [b]) + 1 : ℕ) + B)
    (hZero : ∀ before, before <+: events → cacheTime ≤ before.length →
      ∀ b ∈ availableChildren terminals p, penalty before p b = 0)
    (hGaps : ∀ a ∈ availableChildren terminals p,
      0 < edgeGap terminals reward p a → delta ≤ edgeGap terminals reward p a) :
    backedDeficit (subtreeValue terminals reward p) events p ≤
      ((availableChildren terminals p).card : ℝ) * (A + 4 * c ^ 2 / delta ^ 2) *
        Real.log (backedCount events p + 1 : ℕ) +
      (1 + ((availableChildren terminals p).card : ℝ) * (B + burnin + 1)) := by
  -- Q7.1: Use the final parent count to fix the common logarithm and the suboptimal-child count bounds.
  let L := Real.log (backedCount events p + 1 : ℕ)
  let cap := 4 * c ^ 2 * L / delta ^ 2
  have hL : 0 ≤ L := Real.log_nonneg (by
    exact_mod_cast Nat.le_add_left 1 (backedCount events p))
  have hCap : 0 ≤ cap := by dsimp [cap]; positivity
  have hTerm : ∀ a ∈ availableChildren terminals p,
      (backedCount events (p ++ [a]) : ℝ) * edgeGap terminals reward p a +
        backedDeficit (subtreeValue terminals reward (p ++ [a])) events (p ++ [a]) ≤
      (burnin + cap + 1) + (A * L + B) := by
    intro a ha
    -- Q7.2: Each child count is at most the parent count, so the same parent logarithm bounds its induction term.
    have hN : backedCount events (p ++ [a]) ≤ backedCount events p :=
      backedCount_path_mono events p (p ++ [a]) (List.prefix_append _ _)
    have hLog : Real.log (backedCount events (p ++ [a]) + 1 : ℕ) ≤ L :=
      Real.log_le_log (by positivity) (by exact_mod_cast Nat.add_le_add_right hN 1)
    have hChild := (hChildren events (List.prefix_refl _) a ha).trans
      (add_le_add_right (mul_le_mul_of_nonneg_left hLog hA) B)
    have hEdge : (backedCount events (p ++ [a]) : ℝ) * edgeGap terminals reward p a ≤
        burnin + cap + 1 := by
      by_cases hPos : 0 < edgeGap terminals reward p a
      -- Q7.3: A positive gap uses Q6 and gap <= 1; a zero gap contributes exactly zero to N * gap.
      · have hCount := actual_suboptimal_child_count terminals reward c H A B delta cacheTime
          penalty events run hTable hc hH hA hDelta p hNode hInternal hChildren hZero a ha
          (hGaps a ha hPos)
        have hBurn' : (nodeRateBurnin terminals c H A B delta cacheTime p : ℝ) ≤ burnin := by
          exact_mod_cast hBurn
        have hMul := mul_le_mul_of_nonneg_left (edgeGap_le_one terminals reward hReward p a)
          (Nat.cast_nonneg (backedCount events (p ++ [a])) : (0 : ℝ) ≤ _)
        dsimp [cap, L]
        linarith
      · have hEq := le_antisymm (le_of_not_gt hPos) (edgeGap_nonnegative terminals reward p a ha)
        rw [hEq, mul_zero]
        positivity
    exact add_le_add hEdge hChild
  rw [operational_subtree_deficit_decomposition terminals reward events run.terminal p]
  -- Q7.4: Retain birth deficit <= 1 in the actual parent decomposition; sum over the finite children and collect coefficients.
  calc
    _ ≤ 1 + ∑ _a ∈ availableChildren terminals p, ((burnin + cap + 1) + (A * L + B)) :=
      add_le_add (internal_birthDeficit_le_one terminals reward hReward events hTable
        run.legal p hInternal) (sum_le_sum hTerm)
    _ = _ := by simp only [sum_const, nsmul_eq_mul]; dsimp [cap, L]; ring

def treeBranching (terminals : Finset (List Action)) : ℕ :=
  (workflowNodes terminals).sup (fun p ↦ (availableChildren terminals p).card)

def treeRateConstants (terminals : Finset (List Action)) (c H delta : ℝ) (cacheTime : ℕ) :
    ℕ → ℝ × ℝ
  | 0 => (0, 0)
  | depth + 1 =>
      let previous := treeRateConstants terminals c H delta cacheTime depth
      let burnin := (workflowNodes terminals).sup
        (nodeRateBurnin terminals c H previous.1 previous.2 delta cacheTime)
      (treeBranching terminals * (previous.1 + 4 * c ^ 2 / delta ^ 2),
        1 + treeBranching terminals * (previous.2 + burnin + 1))

theorem treeRateConstants_nonnegative (terminals : Finset (List Action))
    (c H delta : ℝ) (cacheTime depth : ℕ) :
    0 ≤ (treeRateConstants terminals c H delta cacheTime depth).1 ∧
      0 ≤ (treeRateConstants terminals c H delta cacheTime depth).2 := by
  induction depth with
  | zero => simp [treeRateConstants]
  | succ depth ih =>
    obtain ⟨hA, hB⟩ := ih
    simp only [treeRateConstants]
    constructor <;> positivity

theorem actual_subtree_log_deficit (terminals : Finset (List Action))
    (reward : List Action → ℝ) (c H delta : ℝ) (cacheTime : ℕ)
    (penalty : List (TreeEvaluation Action) → List Action → Action → ℝ)
    (hReward : ∀ leaf ∈ terminals, 0 ≤ reward leaf ∧ reward leaf ≤ 1)
    (hc : 0 < c) (hH : 0 ≤ H) (hDelta : 0 < delta)
    (hAntichain : ∀ p ∈ terminals, ∀ q ∈ terminals, p <+: q → p = q)
    (hGaps : ∀ p ∈ workflowNodes terminals, ∀ a ∈ availableChildren terminals p,
      0 < edgeGap terminals reward p a → delta ≤ edgeGap terminals reward p a)
    (depth : ℕ) (events : List (TreeEvaluation Action))
    (run : BoundedTreeRun terminals c H penalty events)
    (hTable : FixedTableEvents terminals reward events)
    (hZero : ∀ before, before <+: events → cacheTime ≤ before.length →
      ∀ p ∈ workflowNodes terminals, ∀ a ∈ availableChildren terminals p, penalty before p a = 0)
    (p : List Action) (hNode : p ∈ workflowNodes terminals)
    (hDepth : topologyDepth terminals - p.length ≤ depth) :
    backedDeficit (subtreeValue terminals reward p) events p ≤
      (treeRateConstants terminals c H delta cacheTime depth).1 *
        Real.log (backedCount events p + 1 : ℕ) +
      (treeRateConstants terminals c H delta cacheTime depth).2 := by
  induction depth generalizing events p with
  -- Q7.5: Quantify over all histories and nodes during induction, so the hypothesis applies to every pre-selection prefix.
  | zero =>
    -- Base case: Remaining depth zero forces a terminal; the antichain and fixed rewards give deficit zero.
    obtain ⟨leaf, hl, hp⟩ := (workflowNodes_mem terminals p).mp hNode
    have hlen := node_length_le_depth terminals leaf
      ((workflowNodes_mem terminals leaf).mpr ⟨leaf, hl, List.prefix_refl _⟩)
    have he : p = leaf := hp.eq_of_length_le (by omega)
    subst leaf
    rw [subtreeValue_at_terminal terminals reward hAntichain p hl,
      terminal_backedDeficit_zero terminals reward events hTable hAntichain p hl]
    simp [treeRateConstants]
  | succ depth ih =>
    have hNonneg := treeRateConstants_nonnegative terminals c H delta cacheTime (depth + 1)
    have hLog : 0 ≤ Real.log (backedCount events p + 1 : ℕ) :=
      Real.log_nonneg (by exact_mod_cast Nat.le_add_left 1 (backedCount events p))
    by_cases hTerminal : p ∈ terminals
    · rw [subtreeValue_at_terminal terminals reward hAntichain p hTerminal,
        terminal_backedDeficit_zero terminals reward events hTable hAntichain p hTerminal]
      exact add_nonneg (mul_nonneg hNonneg.1 hLog) hNonneg.2
    · let previous := treeRateConstants terminals c H delta cacheTime depth
      -- Induction step: Every legal child has smaller remaining depth; restrict run, reward table, and zero penalties to history prefixes.
      let burnin := (workflowNodes terminals).sup
        (nodeRateBurnin terminals c H previous.1 previous.2 delta cacheTime)
      have hPrevious := treeRateConstants_nonnegative terminals c H delta cacheTime depth
      have hChildren : ∀ before, before <+: events → ∀ a ∈ availableChildren terminals p,
          backedDeficit (subtreeValue terminals reward (p ++ [a])) before (p ++ [a]) ≤
            previous.1 * Real.log (backedCount before (p ++ [a]) + 1 : ℕ) + previous.2 := by
        intro before hp a ha
        have hChildDepth := child_remaining_depth_lt terminals p a ha
        exact ih (events := before) (p := p ++ [a]) (run.prefix hp) (hTable.prefix hp)
          (fun past ht hTime q hq b hb ↦ hZero past (ht.trans hp) hTime q hq b hb)
          (legal_child_is_node terminals p a ha) (by omega)
      have hStep := parent_deficit_log_bound terminals reward c H previous.1 previous.2 delta
        cacheTime burnin penalty events run hTable hReward hc hH hPrevious.1 hDelta p hNode
        hTerminal (Finset.le_sup (f := nodeRateBurnin terminals c H previous.1 previous.2
          delta cacheTime) hNode) hChildren
        (fun before hp ht a ha ↦ hZero before hp ht p hNode a ha) (hGaps p hNode)
      have hK : ((availableChildren terminals p).card : ℝ) ≤ treeBranching terminals := by
        -- Use the tree-wide maximum branching factor for constants independent of the particular history and horizon T.
        exact_mod_cast (Finset.le_sup (f := fun q ↦ (availableChildren terminals q).card) hNode)
      have hCoef : 0 ≤ previous.1 + 4 * c ^ 2 / delta ^ 2 :=
        add_nonneg hPrevious.1 (by positivity)
      have hConst : 0 ≤ previous.2 + burnin + 1 := by
        have hB : 0 ≤ previous.2 := hPrevious.2
        positivity
      have hLeading := mul_le_mul_of_nonneg_right
        (mul_le_mul_of_nonneg_right hK hCoef) hLog
      have hTrailing := mul_le_mul_of_nonneg_right hK hConst
      change _ ≤ (treeBranching terminals * (previous.1 + 4 * c ^ 2 / delta ^ 2)) *
        Real.log (backedCount events p + 1 : ℕ) +
        (1 + treeBranching terminals * (previous.2 + burnin + 1))
      linarith

variable {Qid : Type*} [DecidableEq Qid]

/-- A single gap and explicit constants work for every finite valid run, independently of T. -/
theorem cold_forecast_uniform_root_log_bound (qids : Finset Qid) (root : List Action)
    (terminals : Finset (List Action)) (hTerminals : terminals.Nonempty)
    (reward : List Action → ℝ)
    (hReward : ∀ leaf ∈ terminals, 0 ≤ reward leaf ∧ reward leaf ≤ 1)
    (hAntichain : ∀ p ∈ terminals, ∀ q ∈ terminals, p <+: q → p = q)
    (prediction : Qid × List Action → ℝ) (hPrediction : ∀ r, 0 ≤ prediction r)
    (gamma c : ℝ) (hGamma : 0 ≤ gamma) (hc : 0 < c)
    (law : List (TreeEvaluation Action) → List Action → Action → List Action → ℝ)
    (hLaw : ∀ before p a, a ∈ availableChildren terminals p →
      ∀ leaf ∈ subtreeTerminals terminals (p ++ [a]), 0 ≤ law before p a leaf)
    (hMass : ∀ before p a, a ∈ availableChildren terminals p →
      ∑ leaf ∈ subtreeTerminals terminals (p ++ [a]), law before p a leaf = 1)
    (initial : PersistentCaches Qid Action)
    (hInitial : initial.restorable = initial.everMaterialized) :
    ∃ delta : ℝ, 0 < delta ∧ ∀ events : List (TreeEvaluation Action),
      FixedTableEvents terminals reward events →
      LegalTreeRun (fun p ↦ p ∈ terminals) {[]} events →
      TreeAllocationRule terminals c
        (coldForecastPenalty qids root terminals prediction gamma law initial) events →
      let H := gamma * cacheWeight prediction (workflowResources qids root terminals)
      let cacheTime := coverageVisits terminals c H (topologyDepth terminals)
      let constants := treeRateConstants terminals c H delta cacheTime (topologyDepth terminals)
      backedDeficit (subtreeValue terminals reward []) events [] ≤
        constants.1 * Real.log (events.length + 1 : ℕ) + constants.2 := by
  -- Q8.1: Fix an instance-level positive delta before quantifying over events; it cannot be chosen again for each history or T.
  obtain ⟨delta, hDelta, hGaps⟩ := finite_tree_positive_edge_gap terminals reward
  refine ⟨delta, hDelta, ?_⟩
  intro events hTable hLegal hRule
  let H := gamma * cacheWeight prediction (workflowResources qids root terminals)
  let penalty := coldForecastPenalty qids root terminals prediction gamma law initial
  let cacheTime := coverageVisits terminals c H (topologyDepth terminals)
  have hH : 0 ≤ H := mul_nonneg hGamma (sum_nonneg (fun r _ ↦ hPrediction r))
  have run : BoundedTreeRun terminals c H penalty events := {
    -- Q1: Combine the fixed table, legal execution, actual allocation rule, and common penalty envelope into a bounded run.
    terminal := fun event he ↦ (hTable event he).1
    reward := by
      intro event he
      rw [(hTable event he).2]
      exact hReward event.terminal (hTable event he).1
    legal := hLegal
    rule := hRule
    penalty_bounded := by
      intro before _ p a ha
      exact coldForecastPenalty_bounded qids root terminals prediction hPrediction gamma hGamma
        law initial before p a (hLaw before p a ha) (hMass before p a ha) }
  have hZero : ∀ before, before <+: events → cacheTime ≤ before.length →
      ∀ p ∈ workflowNodes terminals, ∀ a ∈ availableChildren terminals p, penalty before p a = 0 := by
    intro before hp ht p _ a _
    -- Q3/Q4: Obtain zero penalties from successful persistent publication and coverage, using more than penalty boundedness.
    exact coldForecastPenalty_after_coverage qids root terminals prediction gamma c H law initial
      hInitial before (run.prefix hp) hc hH hAntichain ht p a
  obtain ⟨leaf, hl⟩ := hTerminals
  have hRoot : [] ∈ workflowNodes terminals :=
    (workflowNodes_mem terminals []).mpr ⟨leaf, hl, List.nil_prefix⟩
  have hResult := actual_subtree_log_deficit terminals reward c H delta cacheTime penalty
    hReward hc hH hDelta hAntichain hGaps (topologyDepth terminals) events run hTable hZero
    [] hRoot (by simp)
  -- Q8.2: Every complete event backs up the root once; root count is T and root deficit is training-quality regret.
  simpa only [root_count_eq_length] using hResult

end AgentUCTPaper
end
end CompleteProofSource29

/-!
## SOURCE 30: AgentUCTPaper/TreeObjectives.lean
Original definitions, theorem statements, and complete proof bodies.
-/
section CompleteProofSource30

/-! # From tree quality regret to training recommendation and own-cache policy costs -/

set_option autoImplicit false

noncomputable section

namespace AgentUCTPaper

open Finset

variable {Action Qid : Type*} [DecidableEq Action] [DecidableEq Qid]

omit [DecidableEq Qid] in
theorem best_training_after_coverage (terminals : Finset (List Action))
    (reward : List Action → ℝ) (c H : ℝ)
    (penalty : List (TreeEvaluation Action) → List Action → Action → ℝ)
    (events : List (TreeEvaluation Action)) (run : BoundedTreeRun terminals c H penalty events)
    (hTable : FixedTableEvents terminals reward events) (hc : 0 < c) (hH : 0 ≤ H)
    (hAntichain : ∀ p ∈ terminals, ∀ q ∈ terminals, p <+: q → p = q)
    (hCount : coverageVisits terminals c H (topologyDepth terminals) ≤ events.length)
    (best : TreeEvaluation Action) (hBest : bestCompleted events = some best) :
    best.reward = subtreeValue terminals reward [] := by
  have hSpec := bestCompleted_spec events best hBest
  have hBestTable := hTable best hSpec.1
  have hNonempty : (subtreeTerminals terminals []).Nonempty :=
    ⟨best.terminal, mem_filter.mpr ⟨hBestTable.1, List.nil_prefix⟩⟩
  obtain ⟨leaf, hl, _, hValue⟩ := subtreeValue_attained terminals reward [] hNonempty
  obtain ⟨event, he, hTerminal⟩ := visited_terminal_observed terminals events run.terminal hAntichain
    leaf hl (actual_terminal_coverage terminals c H penalty events run hc hH hAntichain hCount leaf hl)
  have hLower := hSpec.2 event he
  rw [(hTable event he).2, hTerminal, ← hValue] at hLower
  have hUpper := subtreeValue_upper terminals reward [] best.terminal hBestTable.1 List.nil_prefix
  rw [← hBestTable.2] at hUpper
  exact le_antisymm hUpper hLower

def meteredSearchCost (qids : Finset Qid) (root : List Action)
    (weight : Qid × List Action → ℝ) (overhead : TreeEvaluation Action → ℝ)
    (events : List (TreeEvaluation Action)) (initial : MeteredTreeState Qid Action) : ℝ :=
  (replayMetered qids (fun p ↦ root ++ p) weight overhead events initial).totalPaid - initial.totalPaid

theorem meteredSearchCost_nonnegative (qids : Finset Qid) (root : List Action)
    (weight : Qid × List Action → ℝ) (hWeight : ∀ r, 0 ≤ weight r)
    (overhead : TreeEvaluation Action → ℝ) (events : List (TreeEvaluation Action))
    (hOverhead : ∀ e ∈ events, 0 ≤ overhead e) (initial : MeteredTreeState Qid Action) :
    0 ≤ meteredSearchCost qids root weight overhead events initial := by
  unfold meteredSearchCost
  rw [replayMetered_total]
  apply add_nonneg
  · exact sub_nonneg.mpr (cacheWeight_mono weight hWeight
      (replayMetered_initial_cache_subset qids (fun p ↦ root ++ p) weight overhead events initial))
  · exact List.sum_nonneg (by
      intro x hx
      obtain ⟨e, he, rfl⟩ := List.mem_map.mp hx
      exact hOverhead e he)

theorem meteredSearchCost_upper (qids : Finset Qid) (root : List Action)
    (terminals : Finset (List Action)) (weight : Qid × List Action → ℝ)
    (hWeight : ∀ r, 0 ≤ weight r) (overhead : TreeEvaluation Action → ℝ)
    (events : List (TreeEvaluation Action)) (initial : MeteredTreeState Qid Action)
    (hInitial : initial.materialized ⊆ workflowResources qids root terminals)
    (hTerminal : ∀ e ∈ events, e.terminal ∈ terminals) :
    meteredSearchCost qids root weight overhead events initial ≤
      cacheWeight weight (workflowResources qids root terminals) -
        cacheWeight weight initial.materialized + (events.map overhead).sum := by
  unfold meteredSearchCost
  rw [replayMetered_total]
  apply add_le_add_right
  apply sub_le_sub_right
  exact cacheWeight_mono weight hWeight
    (replayMetered_cache_subset qids (fun p ↦ root ++ p) weight overhead events initial
      (workflowResources qids root terminals) hInitial
      (fun e he ↦ terminal_demand_subset_resources qids root terminals e.terminal (hTerminal e he)))

def cumulativePolicyNetRegret (lambda : ℝ) (actual comparator : List (TreeEvaluation Action))
    (actualCost comparatorCost : ℝ) : ℝ :=
  (comparator.map TreeEvaluation.reward).sum - (actual.map TreeEvaluation.reward).sum +
    lambda * (actualCost - comparatorCost)

omit [DecidableEq Qid] in
theorem policy_net_regret_from_quality (value lambda actualCost comparatorCost budget : ℝ)
    (actual comparator : List (TreeEvaluation Action)) (hLambda : 0 ≤ lambda)
    (hLength : actual.length = comparator.length)
    (hComparator : ∀ e ∈ comparator, e.reward ≤ value)
    (hCost : actualCost - comparatorCost ≤ budget) :
    cumulativePolicyNetRegret lambda actual comparator actualCost comparatorCost ≤
      backedDeficit value actual [] + lambda * budget := by
  have hSum := sum_returns_le_best value comparator hComparator
  have hWeighted := mul_le_mul_of_nonneg_left hCost hLambda
  rw [backedDeficit_identity, root_count_eq_length]
  have hReturn : backedReturn actual [] = (actual.map TreeEvaluation.reward).sum := by
    simp [backedReturn]
  rw [hReturn, hLength]
  unfold cumulativePolicyNetRegret
  linarith

/-- The two trajectories pay against their own caches; comparator cost is not evaluated in K_t. -/
theorem own_cache_policy_regret_bound (qids : Finset Qid) (root : List Action)
    (terminals : Finset (List Action)) (reward : List Action → ℝ) (lambda : ℝ)
    (weight : Qid × List Action → ℝ) (hWeight : ∀ r, 0 ≤ weight r)
    (actualOverhead comparatorOverhead : TreeEvaluation Action → ℝ)
    (actual comparator : List (TreeEvaluation Action))
    (actualInitial comparatorInitial : MeteredTreeState Qid Action)
    (hLambda : 0 ≤ lambda) (hLength : actual.length = comparator.length)
    (hActual : ∀ e ∈ actual, e.terminal ∈ terminals)
    (hComparator : FixedTableEvents terminals reward comparator)
    (hInitial : actualInitial.materialized ⊆ workflowResources qids root terminals)
    (hComparatorOverhead : ∀ e ∈ comparator, 0 ≤ comparatorOverhead e) :
    cumulativePolicyNetRegret lambda actual comparator
      (meteredSearchCost qids root weight actualOverhead actual actualInitial)
      (meteredSearchCost qids root weight comparatorOverhead comparator comparatorInitial) ≤
    backedDeficit (subtreeValue terminals reward []) actual [] + lambda *
      (cacheWeight weight (workflowResources qids root terminals) -
        cacheWeight weight actualInitial.materialized + (actual.map actualOverhead).sum) := by
  apply policy_net_regret_from_quality _ _ _ _ _ actual comparator hLambda hLength
  · intro e he
    rw [(hComparator e he).2]
    exact subtreeValue_upper terminals reward [] e.terminal (hComparator e he).1 List.nil_prefix
  · have hUpper := meteredSearchCost_upper qids root terminals weight hWeight actualOverhead
      actual actualInitial hInitial hActual
    have hLower := meteredSearchCost_nonnegative qids root weight hWeight comparatorOverhead
      comparator hComparatorOverhead comparatorInitial
    linarith

theorem own_cache_cost_difference_common_overhead (qids : Finset Qid) (root : List Action)
    (terminals : Finset (List Action)) (weight : Qid × List Action → ℝ)
    (hWeight : ∀ r, 0 ≤ weight r) (actualOverhead comparatorOverhead : TreeEvaluation Action → ℝ)
    (actual comparator : List (TreeEvaluation Action))
    (actualInitial comparatorInitial : MeteredTreeState Qid Action)
    (hActual : ∀ e ∈ actual, e.terminal ∈ terminals)
    (hInitial : actualInitial.materialized ⊆ workflowResources qids root terminals)
    (hSameOverhead : (actual.map actualOverhead).sum = (comparator.map comparatorOverhead).sum) :
    meteredSearchCost qids root weight actualOverhead actual actualInitial -
      meteredSearchCost qids root weight comparatorOverhead comparator comparatorInitial ≤
    cacheWeight weight (workflowResources qids root terminals) -
      cacheWeight weight actualInitial.materialized := by
  have hUpper := meteredSearchCost_upper qids root terminals weight hWeight actualOverhead
    actual actualInitial hInitial hActual
  have hLower := cacheWeight_mono weight hWeight (replayMetered_initial_cache_subset qids
    (fun p ↦ root ++ p) weight comparatorOverhead comparator comparatorInitial)
  unfold meteredSearchCost at hUpper ⊢
  rw [replayMetered_total] at hUpper ⊢
  rw [replayMetered_total, hSameOverhead]
  linarith

end AgentUCTPaper
end
end CompleteProofSource30

/-!
## SOURCE 31: AgentUCTPaper/TreeRecommendation.lean
Original definitions, theorem statements, and complete proof bodies.
-/
section CompleteProofSource31

/-! # Training shortlist, validation transfer, and the distinct endpoint objective -/

set_option autoImplicit false

noncomputable section

namespace AgentUCTPaper

variable {Action : Type*} [DecidableEq Action]

omit [DecidableEq Action] in
theorem ranked_head_dominates (reward : List Action → ℝ) (head : List Action)
    (tail : List (List Action))
    (hRank : (head :: tail).Pairwise (fun p q ↦ reward q ≤ reward p)) :
    ∀ p ∈ head :: tail, reward p ≤ reward head := by
  intro p hp
  rcases List.mem_cons.mp hp with rfl | hp
  · exact le_rfl
  · exact (List.pairwise_cons.mp hRank).1 p hp

omit [DecidableEq Action] in
theorem ranked_head_in_shortlist (head : List Action) (tail : List (List Action))
    (k : ℕ) (hk : 0 < k) : head ∈ (head :: tail).take k := by
  cases k with
  | zero => omega
  | succ k => simp

theorem ranked_training_head_gap (terminals : Finset (List Action)) (reward : List Action → ℝ)
    (events : List (TreeEvaluation Action)) (hTable : FixedTableEvents terminals reward events)
    (head : List Action) (tail : List (List Action))
    (hRank : (head :: tail).Pairwise (fun p q ↦ reward q ≤ reward p))
    (hComplete : ∀ event ∈ events, event.terminal ∈ head :: tail)
    (hNonempty : events ≠ []) :
    subtreeValue terminals reward [] - reward head ≤
      backedDeficit (subtreeValue terminals reward []) events [] / events.length := by
  have hSum := sum_returns_le_best (reward head) events (by
    intro event he
    rw [(hTable event he).2]
    exact ranked_head_dominates reward head tail hRank _ (hComplete event he))
  have hLen : 0 < events.length := List.length_pos_iff.mpr hNonempty
  rw [le_div_iff₀ (Nat.cast_pos.mpr hLen), backedDeficit_identity, root_count_eq_length]
  have hReturn : backedReturn events [] = (events.map TreeEvaluation.reward).sum := by
    simp [backedReturn]
  rw [hReturn]
  nlinarith

theorem validation_shortlist_gap (terminals : Finset (List Action))
    (train valid : List Action → ℝ) (epsilon : ℝ)
    (events : List (TreeEvaluation Action)) (hTable : FixedTableEvents terminals train events)
    (head : List Action) (tail : List (List Action)) (chosen : List Action) (k : ℕ) (hk : 0 < k)
    (hRank : (head :: tail).Pairwise (fun p q ↦ train q ≤ train p))
    (hComplete : ∀ event ∈ events, event.terminal ∈ head :: tail)
    (hSound : ∀ p ∈ head :: tail, p ∈ terminals) (hNonempty : events ≠ [])
    (hSelected : ∀ p ∈ (head :: tail).take k, valid p ≤ valid chosen)
    (hDifference : ∀ p ∈ terminals, |valid p - train p| ≤ epsilon) :
    subtreeValue terminals valid [] - valid chosen ≤
      backedDeficit (subtreeValue terminals train []) events [] / events.length + 2 * epsilon := by
  have hHead := hSound head (by simp)
  have hHas : (subtreeTerminals terminals []).Nonempty :=
    ⟨head, Finset.mem_filter.mpr ⟨hHead, List.nil_prefix⟩⟩
  obtain ⟨opt, hOpt, _, hValue⟩ := subtreeValue_attained terminals valid [] hHas
  have hOptDiff := (abs_le.mp (hDifference opt hOpt)).2
  have hTrainOpt := subtreeValue_upper terminals train [] opt hOpt List.nil_prefix
  have hHeadDiff := (abs_le.mp (hDifference head hHead)).1
  have hChoose := hSelected head (ranked_head_in_shortlist head tail k hk)
  have hGap := ranked_training_head_gap terminals train events hTable head tail hRank
    hComplete hNonempty
  rw [hValue]
  linarith

/-- All workflows may be observed and yet training top-1 can exclude the validation optimum. -/
theorem validation_top_one_counterexample :
    let ranked := [true, false]
    let train := fun b : Bool ↦ if b then (1 : ℝ) else 0
    let valid := fun b : Bool ↦ if b then (0 : ℝ) else 1
    ranked.Pairwise (fun a b ↦ train b ≤ train a) ∧
      true ∈ ranked.take 1 ∧ false ∉ ranked.take 1 ∧ valid false - valid true = 1 := by
  norm_num

def endpointJ (quality cost lambda reference : ℝ) : ℝ := quality - lambda * cost / reference

theorem endpointJ_gap_identity (actualQuality comparatorQuality actualCost comparatorCost
    lambda reference : ℝ) :
    endpointJ comparatorQuality comparatorCost lambda reference -
      endpointJ actualQuality actualCost lambda reference =
    (comparatorQuality - actualQuality) + lambda * (actualCost - comparatorCost) / reference := by
  unfold endpointJ
  ring

/-- Quality optimality alone does not remove the already-paid optimization-cost gap. -/
theorem equal_quality_positive_endpoint_gap (quality actualCost comparatorCost lambda reference : ℝ)
    (hCost : comparatorCost < actualCost) (hLambda : 0 < lambda) (hReference : 0 < reference) :
    0 < endpointJ quality comparatorCost lambda reference -
      endpointJ quality actualCost lambda reference := by
  rw [endpointJ_gap_identity, sub_self, zero_add]
  exact div_pos (mul_pos hLambda (sub_pos.mpr hCost)) hReference

end AgentUCTPaper
end
end CompleteProofSource31

/-!
## SOURCE 32: AgentUCTPaper/TreeReduced.lean
Original definitions, theorem statements, and complete proof bodies.
-/
section CompleteProofSource32

/-! # The operational next-edge reduction and its actual quality-regret corollary -/

set_option autoImplicit false

noncomputable section

namespace AgentUCTPaper

variable {Qid Action : Type*} [DecidableEq Qid] [DecidableEq Action]

def nextEdgePenalty (qids : Finset Qid) (root : List Action)
    (prediction : Qid × List Action → ℝ) (gamma : ℝ) (initial : PersistentCaches Qid Action)
    (events : List (TreeEvaluation Action)) (p : List Action) (a : Action) : ℝ :=
  let cached := (replayPublished qids (fun x ↦ root ++ x) events initial).restorable
  gamma * max 0 (coldWork prediction cached (panelDemand qids (root ++ (p ++ [a]))) -
    coldWork prediction cached (panelDemand qids (root ++ p)))

theorem nextEdgePenalty_visited_zero (qids : Finset Qid) (root : List Action)
    (prediction : Qid × List Action → ℝ) (gamma : ℝ) (initial : PersistentCaches Qid Action)
    (hInitial : initial.restorable = initial.everMaterialized)
    (hPrediction : ∀ r, 0 ≤ prediction r) (events : List (TreeEvaluation Action))
    (p : List Action) (a : Action)
    (hVisited : 0 < (replayBackup events emptyStatistics (p ++ [a])).visits) :
    nextEdgePenalty qids root prediction gamma initial events p a = 0 := by
  have hZero := actual_visited_child_next_edge_zero qids root (fun _ ↦ 0) prediction
    (fun _ ↦ 0) events ⟨emptyStatistics, initial.everMaterialized, 0, 0⟩ initial p a
    rfl hInitial rfl hPrediction (by simpa only [replayMetered_stats] using hVisited)
  dsimp only [nextEdgePenalty]
  rw [hZero, mul_zero]

theorem next_edge_allocation_iff_uct (qids : Finset Qid) (root : List Action)
    (terminals : Finset (List Action)) (prediction : Qid × List Action → ℝ)
    (gamma c : ℝ) (initial : PersistentCaches Qid Action)
    (hInitial : initial.restorable = initial.everMaterialized)
    (hPrediction : ∀ r, 0 ≤ prediction r) (events : List (TreeEvaluation Action))
    (hTerminal : ∀ event ∈ events, event.terminal ∈ terminals) :
    TreeAllocationRule terminals c (nextEdgePenalty qids root prediction gamma initial) events ↔
      TreeAllocationRule terminals c (fun _ _ _ ↦ 0) events := by
  have hEquiv (before : List (TreeEvaluation Action)) (event : TreeEvaluation Action)
      (after : List (TreeEvaluation Action)) (hs : events = before ++ event :: after)
      (p : List Action) (a : Action) (hChild : childAfter p event.expanded = some a)
      (hInit : ∀ b ∈ availableChildren terminals p,
        0 < (replayBackup before emptyStatistics (p ++ [b])).visits) :
      ∀ b ∈ availableChildren terminals p,
        nextEdgePenalty qids root prediction gamma initial before p b = 0 ∧
          nextEdgePenalty qids root prediction gamma initial before p a = 0 := by
    have he : event ∈ events := by simp [hs]
    have ha := (availableChildren_mem terminals p a).mpr
      ⟨event.terminal, hTerminal event he,
        ((childAfter_some_iff p event.expanded a).mp hChild).trans event.expanded_is_prefix⟩
    intro b hb
    exact ⟨nextEdgePenalty_visited_zero qids root prediction gamma initial hInitial hPrediction
      before p b (hInit b hb),
      nextEdgePenalty_visited_zero qids root prediction gamma initial hInitial hPrediction
        before p a (hInit a ha)⟩
  constructor <;> intro hRule before event after hs p a ha
  · refine ⟨(hRule before event after hs p a ha).1, ?_⟩
    intro hInit b hb
    have hIndex := (hRule before event after hs p a ha).2 hInit b hb
    obtain ⟨hB, hA⟩ := hEquiv before event after hs p a ha hInit b hb
    simpa only [hB, hA] using hIndex
  · refine ⟨(hRule before event after hs p a ha).1, ?_⟩
    intro hInit b hb
    obtain ⟨hB, hA⟩ := hEquiv before event after hs p a ha hInit b hb
    rw [hB, hA]
    exact (hRule before event after hs p a ha).2 hInit b hb

omit [DecidableEq Qid] in
theorem ordinary_uct_uniform_root_log_bound (terminals : Finset (List Action))
    (hTerminals : terminals.Nonempty) (reward : List Action → ℝ)
    (hReward : ∀ leaf ∈ terminals, 0 ≤ reward leaf ∧ reward leaf ≤ 1)
    (hAntichain : ∀ p ∈ terminals, ∀ q ∈ terminals, p <+: q → p = q)
    (c : ℝ) (hc : 0 < c) :
    ∃ delta : ℝ, 0 < delta ∧ ∀ events : List (TreeEvaluation Action),
      FixedTableEvents terminals reward events →
      LegalTreeRun (fun p ↦ p ∈ terminals) {[]} events →
      TreeAllocationRule terminals c (fun _ _ _ ↦ 0) events →
      let constants := treeRateConstants terminals c 0 delta 0 (topologyDepth terminals)
      backedDeficit (subtreeValue terminals reward []) events [] ≤
        constants.1 * Real.log (events.length + 1 : ℕ) + constants.2 := by
  obtain ⟨delta, hDelta, hGaps⟩ := finite_tree_positive_edge_gap terminals reward
  refine ⟨delta, hDelta, ?_⟩
  intro events hTable hLegal hRule
  have run : BoundedTreeRun terminals c 0 (fun _ _ _ ↦ 0) events := {
    terminal := fun e he ↦ (hTable e he).1
    reward := by
      intro e he
      rw [(hTable e he).2]
      exact hReward e.terminal (hTable e he).1
    legal := hLegal
    rule := hRule
    penalty_bounded := by intros; constructor <;> rfl }
  obtain ⟨leaf, hl⟩ := hTerminals
  have hRoot : [] ∈ workflowNodes terminals :=
    (workflowNodes_mem terminals []).mpr ⟨leaf, hl, List.nil_prefix⟩
  have hResult := actual_subtree_log_deficit terminals reward c 0 delta 0 (fun _ _ _ ↦ 0)
    hReward hc le_rfl hDelta hAntichain hGaps (topologyDepth terminals) events run hTable
    (by intros; rfl) [] hRoot (by simp)
  simpa only [root_count_eq_length] using hResult

theorem next_edge_uniform_root_log_bound (qids : Finset Qid) (root : List Action)
    (terminals : Finset (List Action)) (hTerminals : terminals.Nonempty)
    (reward : List Action → ℝ)
    (hReward : ∀ leaf ∈ terminals, 0 ≤ reward leaf ∧ reward leaf ≤ 1)
    (hAntichain : ∀ p ∈ terminals, ∀ q ∈ terminals, p <+: q → p = q)
    (prediction : Qid × List Action → ℝ) (hPrediction : ∀ r, 0 ≤ prediction r)
    (gamma c : ℝ) (hc : 0 < c) (initial : PersistentCaches Qid Action)
    (hInitial : initial.restorable = initial.everMaterialized) :
    ∃ delta : ℝ, 0 < delta ∧ ∀ events : List (TreeEvaluation Action),
      FixedTableEvents terminals reward events →
      LegalTreeRun (fun p ↦ p ∈ terminals) {[]} events →
      TreeAllocationRule terminals c (nextEdgePenalty qids root prediction gamma initial) events →
      let constants := treeRateConstants terminals c 0 delta 0 (topologyDepth terminals)
      backedDeficit (subtreeValue terminals reward []) events [] ≤
        constants.1 * Real.log (events.length + 1 : ℕ) + constants.2 := by
  obtain ⟨delta, hd, hBound⟩ := ordinary_uct_uniform_root_log_bound terminals hTerminals reward
    hReward hAntichain c hc
  refine ⟨delta, hd, ?_⟩
  intro events hTable hLegal hRule
  exact hBound events hTable hLegal ((next_edge_allocation_iff_uct qids root terminals prediction
    gamma c initial hInitial hPrediction events (fun e he ↦ (hTable e he).1)).mp hRule)

/-- Complete event histories satisfying the fixed table, expansion, and allocation rules. -/
def AllocatedTreeHistory (terminals : Finset (List Action)) (reward : List Action → ℝ)
    (c : ℝ) (penalty : List (TreeEvaluation Action) → List Action → Action → ℝ)
    (events : List (TreeEvaluation Action)) : Prop :=
  FixedTableEvents terminals reward events ∧
    LegalTreeRun (fun p ↦ p ∈ terminals) {[]} events ∧
    TreeAllocationRule terminals c penalty events

/-- Admissible complete next events, including rollout terminals and observed rewards. -/
def admissibleTreeEvents (terminals : Finset (List Action)) (reward : List Action → ℝ)
    (c : ℝ) (penalty : List (TreeEvaluation Action) → List Action → Action → ℝ)
    (before : List (TreeEvaluation Action)) : Set (TreeEvaluation Action) :=
  {event | AllocatedTreeHistory terminals reward c penalty (before ++ [event])}

/-- A shared resolver fixes all remaining choices: expansion, rollout, evaluation receipts,
ties, and stopping. A fixed common random tape can be included in this deterministic function.
Equality of allocation rules alone does not supply such a resolver. -/
def resolvedTreeHistory
    (candidates : List (TreeEvaluation Action) → Set (TreeEvaluation Action))
    (resolve : List (TreeEvaluation Action) → Set (TreeEvaluation Action) →
      Option (TreeEvaluation Action)) : ℕ → List (TreeEvaluation Action)
  | 0 => []
  | n + 1 =>
      let before := resolvedTreeHistory candidates resolve n
      match resolve before (candidates before) with
      | none => before
      | some event => before ++ [event]

theorem admissibleTreeEvents_next_edge_eq_uct (qids : Finset Qid) (root : List Action)
    (terminals : Finset (List Action)) (reward : List Action → ℝ)
    (prediction : Qid × List Action → ℝ) (gamma c : ℝ)
    (initial : PersistentCaches Qid Action)
    (hInitial : initial.restorable = initial.everMaterialized)
    (hPrediction : ∀ r, 0 ≤ prediction r) (before : List (TreeEvaluation Action)) :
    admissibleTreeEvents terminals reward c
        (nextEdgePenalty qids root prediction gamma initial) before =
      admissibleTreeEvents terminals reward c (fun _ _ _ ↦ 0) before := by
  ext event
  change (_ ∧ _ ∧ _) ↔ (_ ∧ _ ∧ _)
  constructor <;> intro ⟨hTable, hLegal, hRule⟩
  · exact ⟨hTable, hLegal, (next_edge_allocation_iff_uct qids root terminals prediction
      gamma c initial hInitial hPrediction _ (fun e he ↦ (hTable e he).1)).mp hRule⟩
  · exact ⟨hTable, hLegal, (next_edge_allocation_iff_uct qids root terminals prediction
      gamma c initial hInitial hPrediction _ (fun e he ↦ (hTable e he).1)).mpr hRule⟩

omit [DecidableEq Qid] in
/-- A resolver that returns admissible events generates a valid allocated history. -/
theorem resolvedTreeHistory_valid (terminals : Finset (List Action)) (reward : List Action → ℝ)
    (c : ℝ) (penalty : List (TreeEvaluation Action) → List Action → Action → ℝ)
    (resolve : List (TreeEvaluation Action) → Set (TreeEvaluation Action) →
      Option (TreeEvaluation Action))
    (hResolve : ∀ before event,
      resolve before (admissibleTreeEvents terminals reward c penalty before) = some event →
        event ∈ admissibleTreeEvents terminals reward c penalty before) (n : ℕ) :
    AllocatedTreeHistory terminals reward c penalty
      (resolvedTreeHistory (admissibleTreeEvents terminals reward c penalty) resolve n) := by
  induction n with
  | zero =>
    refine ⟨by simp [resolvedTreeHistory, FixedTableEvents], trivial, ?_⟩
    intro before event after hs
    have hLength := congrArg List.length hs
    simp [resolvedTreeHistory] at hLength
    omega
  | succ n ih =>
    let before := resolvedTreeHistory (admissibleTreeEvents terminals reward c penalty) resolve n
    change AllocatedTreeHistory terminals reward c penalty
      (match resolve before (admissibleTreeEvents terminals reward c penalty before) with
      | none => before
      | some event => before ++ [event])
    cases h : resolve before (admissibleTreeEvents terminals reward c penalty before) with
    | none => exact ih
    | some event => exact hResolve before event h

/-- Next-edge and ordinary UCT have identical histories under one shared complete-event
resolver. This couples rollout and evaluation as well as expansion, ties, and stopping. -/
theorem next_edge_coupled_history_eq_uct (qids : Finset Qid) (root : List Action)
    (terminals : Finset (List Action)) (reward : List Action → ℝ)
    (prediction : Qid × List Action → ℝ) (gamma c : ℝ)
    (initial : PersistentCaches Qid Action)
    (hInitial : initial.restorable = initial.everMaterialized)
    (hPrediction : ∀ r, 0 ≤ prediction r)
    (resolve : List (TreeEvaluation Action) → Set (TreeEvaluation Action) →
      Option (TreeEvaluation Action)) (n : ℕ) :
    resolvedTreeHistory (admissibleTreeEvents terminals reward c
        (nextEdgePenalty qids root prediction gamma initial)) resolve n =
      resolvedTreeHistory (admissibleTreeEvents terminals reward c (fun _ _ _ ↦ 0)) resolve n := by
  have hCandidates := funext (admissibleTreeEvents_next_edge_eq_uct qids root terminals reward
    prediction gamma c initial hInitial hPrediction)
  rw [hCandidates]

/-- Equal coupled event histories give equal raw backups, expanded trees, and cache graphs. -/
theorem next_edge_coupled_state_eq_uct (qids : Finset Qid) (root : List Action)
    (terminals : Finset (List Action)) (reward : List Action → ℝ)
    (prediction : Qid × List Action → ℝ) (gamma c : ℝ)
    (initial : PersistentCaches Qid Action)
    (hInitial : initial.restorable = initial.everMaterialized)
    (hPrediction : ∀ r, 0 ≤ prediction r)
    (resolve : List (TreeEvaluation Action) → Set (TreeEvaluation Action) →
      Option (TreeEvaluation Action)) (n : ℕ) :
    let next := resolvedTreeHistory (admissibleTreeEvents terminals reward c
      (nextEdgePenalty qids root prediction gamma initial)) resolve n
    let ordinary := resolvedTreeHistory
      (admissibleTreeEvents terminals reward c (fun _ _ _ ↦ 0)) resolve n
    replayBackup next emptyStatistics = replayBackup ordinary emptyStatistics ∧
      replayTree next = replayTree ordinary ∧
      replayPublished qids (fun x ↦ root ++ x) next initial =
        replayPublished qids (fun x ↦ root ++ x) ordinary initial := by
  dsimp only
  rw [next_edge_coupled_history_eq_uct qids root terminals reward prediction gamma c initial
    hInitial hPrediction resolve n]
  exact ⟨rfl, rfl, rfl⟩

end AgentUCTPaper
end
end CompleteProofSource32

/-!
## SOURCE 33: AgentUCTPaper/TreeCostEstimation.lean
Original definitions, theorem statements, and complete proof bodies.
-/
section CompleteProofSource33

/-! # Executable reference costs, legacy reduction, and explicit error components -/

set_option autoImplicit false

noncomputable section

namespace AgentUCTPaper

open Finset

variable {Qid Action : Type*} [DecidableEq Qid] [DecidableEq Action]

def uniformTerminalLaw (terminals : Finset (List Action)) (p : List Action) (_leaf : List Action) :
    ℝ := 1 / (subtreeTerminals terminals p).card

omit [DecidableEq Qid] in
theorem uniformTerminalLaw_probability (terminals : Finset (List Action)) (p : List Action)
    (hNonempty : (subtreeTerminals terminals p).Nonempty) :
    (∀ leaf, 0 ≤ uniformTerminalLaw terminals p leaf) ∧
      (∑ leaf ∈ subtreeTerminals terminals p, uniformTerminalLaw terminals p leaf) = 1 := by
  have hCard : ((subtreeTerminals terminals p).card : ℝ) ≠ 0 := by
    exact_mod_cast (card_ne_zero.mpr hNonempty)
  constructor
  · intro leaf
    unfold uniformTerminalLaw
    positivity
  · simp [uniformTerminalLaw, hCard]

def coldResourceInclusion (qids : Finset Qid) (root : List Action)
    (terminals : Finset (List Action)) (law : List Action → ℝ)
    (cached : Finset (Qid × List Action)) (p : List Action) (r : Qid × List Action) : ℝ :=
  ∑ leaf ∈ subtreeTerminals terminals p,
    if r ∈ panelDemand qids (root ++ leaf) \ cached then law leaf else 0

theorem referenceColdCost_resource_form (qids : Finset Qid) (root : List Action)
    (terminals : Finset (List Action)) (prediction : Qid × List Action → ℝ)
    (law : List Action → ℝ) (cached : Finset (Qid × List Action)) (p : List Action) :
    referenceColdCost qids root terminals prediction law cached p =
      ∑ r ∈ workflowResources qids root terminals,
        coldResourceInclusion qids root terminals law cached p r * prediction r := by
  have hBill (leaf : List Action) (hl : leaf ∈ subtreeTerminals terminals p) :
      coldWork prediction cached (panelDemand qids (root ++ leaf)) =
        ∑ r ∈ workflowResources qids root terminals,
          if r ∈ panelDemand qids (root ++ leaf) \ cached then prediction r else 0 := by
    have hSubset : panelDemand qids (root ++ leaf) \ cached ⊆
        workflowResources qids root terminals := sdiff_subset.trans
      (terminal_demand_subset_resources qids root terminals leaf (mem_filter.mp hl).1)
    have hFilter : (workflowResources qids root terminals).filter
        (fun r ↦ r ∈ panelDemand qids (root ++ leaf) \ cached) =
        panelDemand qids (root ++ leaf) \ cached := by
      ext r
      simp only [mem_filter]
      exact ⟨fun h ↦ h.2, fun h ↦ ⟨hSubset h, h⟩⟩
    rw [← sum_filter, hFilter]
    rfl
  unfold referenceColdCost
  calc
    _ = ∑ leaf ∈ subtreeTerminals terminals p, law leaf *
        ∑ r ∈ workflowResources qids root terminals,
          if r ∈ panelDemand qids (root ++ leaf) \ cached then prediction r else 0 := by
      apply sum_congr rfl
      intro leaf hl
      rw [hBill leaf hl]
    _ = _ := by
      simp_rw [mul_sum]
      rw [sum_comm]
      apply sum_congr rfl
      intro r _
      rw [coldResourceInclusion, sum_mul]
      apply sum_congr rfl
      intro leaf _
      split_ifs <;> simp

theorem coldWork_demand_mono (weight : Qid × List Action → ℝ)
    (hWeight : ∀ r, 0 ≤ weight r) (cached small large : Finset (Qid × List Action))
    (hSubset : small ⊆ large) : coldWork weight cached small ≤ coldWork weight cached large := by
  exact sum_le_sum_of_subset_of_nonneg (sdiff_subset_sdiff hSubset subset_rfl)
    (fun r _ _ ↦ hWeight r)

def legacyContinuationCold (qids : Finset Qid) (root : List Action)
    (terminals : Finset (List Action)) (prediction : Qid × List Action → ℝ)
    (law : List Action → ℝ) (cached : Finset (Qid × List Action)) (p : List Action) (a : Action) : ℝ :=
  ∑ leaf ∈ subtreeTerminals terminals (p ++ [a]), law leaf * max 0
    (coldWork prediction cached (panelDemand qids (root ++ leaf)) -
      coldWork prediction cached (panelDemand qids (root ++ p)))

/-- Under ledger/set-difference semantics clipping is inactive; suffix equivalence additionally
requires the prefix-complete invariant proved in TreeCheckpoint. -/
theorem legacyContinuationCold_common_shift (qids : Finset Qid) (root : List Action)
    (terminals : Finset (List Action)) (prediction : Qid × List Action → ℝ)
    (hPrediction : ∀ r, 0 ≤ prediction r) (law : List Action → ℝ)
    (cached : Finset (Qid × List Action)) (p : List Action) (a : Action)
    (hMass : ∑ leaf ∈ subtreeTerminals terminals (p ++ [a]), law leaf = 1) :
    legacyContinuationCold qids root terminals prediction law cached p a =
      referenceColdCost qids root terminals prediction law cached (p ++ [a]) -
        coldWork prediction cached (panelDemand qids (root ++ p)) := by
  have hCold (leaf : List Action) (hl : leaf ∈ subtreeTerminals terminals (p ++ [a])) :
      0 ≤ coldWork prediction cached (panelDemand qids (root ++ leaf)) -
        coldWork prediction cached (panelDemand qids (root ++ p)) := by
    apply sub_nonneg.mpr
    apply coldWork_demand_mono prediction hPrediction
    apply panelDemand_prefix_mono
    exact (List.prefix_append_right_inj root).mpr
      ((List.prefix_append p [a]).trans (mem_filter.mp hl).2)
  unfold legacyContinuationCold referenceColdCost
  calc
    _ = ∑ leaf ∈ subtreeTerminals terminals (p ++ [a]), law leaf *
        (coldWork prediction cached (panelDemand qids (root ++ leaf)) -
          coldWork prediction cached (panelDemand qids (root ++ p))) := by
      apply sum_congr rfl
      intro leaf hl
      rw [max_eq_right (hCold leaf hl)]
    _ = _ := by simp_rw [mul_sub]; rw [sum_sub_distrib, ← sum_mul, hMass, one_mul]

def referenceFullCost (qids : Finset Qid) (root : List Action)
    (terminals : Finset (List Action)) (weight : Qid × List Action → ℝ)
    (overhead law : List Action → ℝ) (cached : Finset (Qid × List Action)) (p : List Action) : ℝ :=
  ∑ leaf ∈ subtreeTerminals terminals p,
    law leaf * (coldWork weight cached (panelDemand qids (root ++ leaf)) + overhead leaf)

theorem full_reference_cost_error (qids : Finset Qid) (root : List Action)
    (terminals : Finset (List Action)) (predicted actual radius : Qid × List Action → ℝ)
    (predictedOverhead actualOverhead overheadRadius predictedLaw actualLaw : List Action → ℝ)
    (cached : Finset (Qid × List Action)) (p : List Action) (billBound : ℝ)
    (hLaw : ∀ leaf ∈ subtreeTerminals terminals p, 0 ≤ predictedLaw leaf)
    (hError : ∀ r ∈ workflowResources qids root terminals, |predicted r - actual r| ≤ radius r)
    (hOverhead : ∀ leaf ∈ subtreeTerminals terminals p,
      |predictedOverhead leaf - actualOverhead leaf| ≤ overheadRadius leaf)
    (hBill : ∀ leaf ∈ subtreeTerminals terminals p,
      |coldWork actual cached (panelDemand qids (root ++ leaf)) + actualOverhead leaf| ≤ billBound) :
    |referenceFullCost qids root terminals predicted predictedOverhead predictedLaw cached p -
      referenceFullCost qids root terminals actual actualOverhead actualLaw cached p| ≤
      (∑ leaf ∈ subtreeTerminals terminals p, predictedLaw leaf *
        ((∑ r ∈ panelDemand qids (root ++ leaf) \ cached, radius r) + overheadRadius leaf)) +
      billBound * ∑ leaf ∈ subtreeTerminals terminals p, |predictedLaw leaf - actualLaw leaf| := by
  apply reference_law_cost_error_of_radius _ _ _ _ _ _ billBound hLaw hBill
  intro leaf hl
  have hSubset := terminal_demand_subset_resources qids root terminals leaf (mem_filter.mp hl).1
  have h := total_search_cost_forecast_error (panelDemand qids (root ++ leaf) \ cached)
    (fun _ ↦ 1) predicted actual radius (predictedOverhead leaf) (actualOverhead leaf)
    (overheadRadius leaf) (by intros; norm_num)
    (fun r hr ↦ hError r (hSubset (mem_sdiff.mp hr).1)) (hOverhead leaf hl)
  simpa only [one_mul, coldWork] using h

omit [DecidableEq Qid] in
theorem tree_allocation_common_overhead_iff (terminals : Finset (List Action)) (c : ℝ)
    (penalty : List (TreeEvaluation Action) → List Action → Action → ℝ)
    (common : List (TreeEvaluation Action) → List Action → ℝ)
    (events : List (TreeEvaluation Action)) :
    TreeAllocationRule terminals c (fun before p a ↦ penalty before p a + common before p) events ↔
      TreeAllocationRule terminals c penalty events := by
  unfold TreeAllocationRule treeIndex
  simp only [sub_add_eq_sub_sub, sub_le_sub_iff_right]

end AgentUCTPaper
end
end CompleteProofSource33

/-!
## SOURCE 34: AgentUCTPaper/TreeEstimatorChoice.lean
Original definitions, theorem statements, and complete proof bodies.
-/
section CompleteProofSource34

/-! # A full conditional cost predictor and a cost-confidence allocation index -/

set_option autoImplicit false

noncomputable section

namespace AgentUCTPaper

open Finset

def finiteCostMean {Completion : Type*} (completions : Finset Completion)
    (law bill : Completion → ℝ) : ℝ := ∑ x ∈ completions, law x * bill x

def finiteCostMSE {Completion : Type*} (completions : Finset Completion)
    (law bill : Completion → ℝ) (estimate : ℝ) : ℝ :=
  ∑ x ∈ completions, law x * (bill x - estimate) ^ 2

theorem finite_cost_mse_decomposition {Completion : Type*} (completions : Finset Completion)
    (law bill : Completion → ℝ) (hMass : ∑ x ∈ completions, law x = 1) (estimate : ℝ) :
    finiteCostMSE completions law bill estimate =
      finiteCostMSE completions law bill (finiteCostMean completions law bill) +
        (estimate - finiteCostMean completions law bill) ^ 2 := by
  let mean := finiteCostMean completions law bill
  have hPoint (x : Completion) : law x * (bill x - estimate) ^ 2 =
      law x * (bill x - mean) ^ 2 + law x * (estimate - mean) ^ 2 +
        2 * (mean - estimate) * (law x * bill x - law x * mean) := by ring
  unfold finiteCostMSE
  simp_rw [hPoint]
  rw [sum_add_distrib, sum_add_distrib, ← sum_mul, hMass, one_mul, ← mul_sum,
    sum_sub_distrib, ← sum_mul, hMass, one_mul]
  change _ + _ + 2 * (mean - estimate) * (mean - mean) = _
  ring

theorem full_cost_mean_unique_mse_minimizer {Completion : Type*}
    (completions : Finset Completion) (law bill : Completion → ℝ)
    (hMass : ∑ x ∈ completions, law x = 1) (estimate : ℝ) :
    finiteCostMSE completions law bill (finiteCostMean completions law bill) ≤
      finiteCostMSE completions law bill estimate ∧
    (finiteCostMSE completions law bill estimate =
      finiteCostMSE completions law bill (finiteCostMean completions law bill) ↔
        estimate = finiteCostMean completions law bill) := by
  rw [finite_cost_mse_decomposition completions law bill hMass estimate]
  constructor
  · exact le_add_of_nonneg_right (sq_nonneg _)
  · constructor
    · intro h
      have hs : (estimate - finiteCostMean completions law bill) ^ 2 = 0 := by linarith
      exact sub_eq_zero.mp (sq_eq_zero_iff.mp hs)
    · intro h
      simp [h]

variable {Qid Action : Type*} [DecidableEq Qid] [DecidableEq Action]

theorem referenceFullCost_is_conditional_mean (qids : Finset Qid) (root : List Action)
    (terminals : Finset (List Action)) (weight : Qid × List Action → ℝ)
    (overhead law : List Action → ℝ) (cached : Finset (Qid × List Action)) (p : List Action) :
    referenceFullCost qids root terminals weight overhead law cached p =
      finiteCostMean (subtreeTerminals terminals p) law
        (fun leaf ↦ coldWork weight cached (panelDemand qids (root ++ leaf)) + overhead leaf) := rfl

def costLowerBound (estimate radius : ℝ) : ℝ := max 0 (estimate - radius)

theorem costLowerBound_valid {actual estimate radius : ℝ}
    (hActual : 0 ≤ actual) (hError : |estimate - actual| ≤ radius) :
    0 ≤ costLowerBound estimate radius ∧ costLowerBound estimate radius ≤ actual ∧
      actual - costLowerBound estimate radius ≤ 2 * radius := by
  obtain ⟨hLower, hUpper⟩ := abs_le.mp hError
  refine ⟨le_max_left _ _, max_le hActual (by linarith), ?_⟩
  have h := le_max_right 0 (estimate - radius)
  change actual - max 0 (estimate - radius) ≤ 2 * radius
  linarith

theorem costLowerBound_below_point {estimate radius : ℝ}
    (hEstimate : 0 ≤ estimate) (hRadius : 0 ≤ radius) :
    costLowerBound estimate radius ≤ estimate := max_le hEstimate (by linarith)

theorem costLowerBound_cached_zero {radius : ℝ} (hRadius : 0 ≤ radius) :
    costLowerBound 0 radius = 0 := by simp [costLowerBound, hRadius]

theorem net_optimism_from_cost_radius {mu q rewardRadius actualCost estimateCost costRadius beta : ℝ}
    (hBeta : 0 ≤ beta) (hReward : mu ≤ q + rewardRadius) (hCost : 0 ≤ actualCost)
    (hCostError : |estimateCost - actualCost| ≤ costRadius) :
    AgentUCT.net mu actualCost beta ≤
      q + rewardRadius - beta * costLowerBound estimateCost costRadius := by
  have hLower := (costLowerBound_valid hCost hCostError).2.1
  have hMul := mul_le_mul_of_nonneg_left hLower hBeta
  unfold AgentUCT.net
  linarith

theorem selected_net_gap_from_cost_radii
    {muBest muChosen qBest qChosen rBest rChosen actualBest actualChosen
      estimatedBest estimatedChosen errorBest errorChosen beta : ℝ}
    (hBeta : 0 ≤ beta) (hBest : muBest ≤ qBest + rBest)
    (hChosen : qChosen ≤ muChosen + rChosen) (hActualBest : 0 ≤ actualBest)
    (hActualChosen : 0 ≤ actualChosen)
    (hBestError : |estimatedBest - actualBest| ≤ errorBest)
    (hChosenError : |estimatedChosen - actualChosen| ≤ errorChosen)
    (hSelect : qBest + rBest - beta * costLowerBound estimatedBest errorBest ≤
      qChosen + rChosen - beta * costLowerBound estimatedChosen errorChosen) :
    AgentUCT.net muBest actualBest beta - AgentUCT.net muChosen actualChosen beta ≤
      2 * rChosen + 2 * beta * errorChosen := by
  exact AgentUCT.optimistic_cost_gap_bound hBeta hBest hChosen
    (costLowerBound_valid hActualBest hBestError).2.1
    (costLowerBound_valid hActualChosen hChosenError).2.2 hSelect

end AgentUCTPaper
end
end CompleteProofSource34

/-!
## SOURCE 35: AgentUCTPaper/TreeEstimatorDynamics.lean
Original definitions, theorem statements, and complete proof bodies.
-/
section CompleteProofSource35

/-! # Cache accumulation, prediction savings, and next-edge net regret

Physical publication and counterfactual cost forecasts are separate operations.
Savings compare a fixed demand law and fixed weights before and after publication.
The net-regret corollary compares policies running against their own caches.
-/

set_option autoImplicit false

noncomputable section

namespace AgentUCTPaper

open Finset

variable {Resource : Type*} [DecidableEq Resource]

/-- More saved resources reduce a fixed bill; no estimator is involved. -/
theorem coldWork_cache_antitone (weight : Resource → ℝ) (hWeight : ∀ r, 0 ≤ weight r)
    (cached larger demand : Finset Resource) (hCache : cached ⊆ larger) :
    coldWork weight larger demand ≤ coldWork weight cached demand := by
  exact sum_le_sum_of_subset_of_nonneg (sdiff_subset_sdiff subset_rfl hCache)
    (fun r _ _ ↦ hWeight r)

/-- A bill computed at the initial snapshot already accounts for sequential cache growth. -/
theorem coldWork_sequential_union (weight : Resource → ℝ)
    (cached first later : Finset Resource) :
    coldWork weight cached (first ∪ later) =
      coldWork weight cached first + coldWork weight (cached ∪ first) later := by
  have h := cache_union_accounting weight cached (first ∪ later)
  rw [← union_assoc, cache_union_accounting, cache_union_accounting] at h
  linarith

/-- Exactly the newly published resources shared with the later demand become free. -/
theorem coldWork_publication_savings (weight : Resource → ℝ)
    (cached published demand : Finset Resource) :
    coldWork weight cached demand - coldWork weight (cached ∪ published) demand =
      coldWork weight cached (demand ∩ published) := by
  have hSplit : demand \ cached =
      (demand \ (cached ∪ published)) ∪ ((demand ∩ published) \ cached) := by
    ext r
    simp only [mem_sdiff, mem_union, mem_inter]
    tauto
  have hDisjoint : Disjoint (demand \ (cached ∪ published))
      ((demand ∩ published) \ cached) := by
    apply disjoint_left.mpr
    intro r ha hb
    exact (mem_sdiff.mp ha).2 (mem_union_right cached (mem_inter.mp (mem_sdiff.mp hb).1).2)
  unfold coldWork
  rw [hSplit, sum_union hDisjoint]
  ring

variable {Qid Action : Type*} [DecidableEq Qid] [DecidableEq Action]

/-- A rollout-only prefix is published even though it receives no tree-statistics update. -/
theorem rollout_publication_without_backup (qids : Finset Qid)
    (weight : Qid × List Action → ℝ) (overhead : TreeEvaluation Action → ℝ)
    (state : MeteredTreeState Qid Action) (event : TreeEvaluation Action)
    (qid : Qid) (p : List Action) (hQid : qid ∈ qids)
    (hPrefix : p ∈ executionPrefixes event.terminal) (hOffTree : ¬ p <+: event.expanded) :
    (qid, p) ∈ (meterStep qids id weight overhead state event).materialized ∧
      (meterStep qids id weight overhead state event).stats p = state.stats p := by
  constructor
  · exact mem_union_right _ ((panelDemand_mem qids event.terminal p qid).mpr ⟨hQid, hPrefix⟩)
  · rw [meterStep_stats]
    exact backupEvent_off_path state.stats event p hOffTree

/-- Frozen-law prediction change isolates the effect of newly published cache objects. -/
theorem referenceColdCost_publication_savings (qids : Finset Qid) (root : List Action)
    (terminals : Finset (List Action)) (prediction : Qid × List Action → ℝ)
    (law : List Action → ℝ) (cached published : Finset (Qid × List Action)) (p : List Action) :
    referenceColdCost qids root terminals prediction law cached p -
      referenceColdCost qids root terminals prediction law (cached ∪ published) p =
    ∑ leaf ∈ subtreeTerminals terminals p, law leaf *
      coldWork prediction cached (panelDemand qids (root ++ leaf) ∩ published) := by
  unfold referenceColdCost
  rw [← sum_sub_distrib]
  apply sum_congr rfl
  intro leaf _
  rw [← mul_sub, coldWork_publication_savings]

/-- Monotonicity holds with the continuation law and predictor held fixed. -/
theorem referenceColdCost_cache_antitone (qids : Finset Qid) (root : List Action)
    (terminals : Finset (List Action)) (prediction : Qid × List Action → ℝ)
    (hPrediction : ∀ r, 0 ≤ prediction r) (law : List Action → ℝ)
    (cached larger : Finset (Qid × List Action)) (p : List Action)
    (hLaw : ∀ leaf ∈ subtreeTerminals terminals p, 0 ≤ law leaf)
    (hCache : cached ⊆ larger) :
    referenceColdCost qids root terminals prediction law larger p ≤
      referenceColdCost qids root terminals prediction law cached p := by
  apply sum_le_sum
  intro leaf hl
  exact mul_le_mul_of_nonneg_left
    (coldWork_cache_antitone prediction hPrediction cached larger _ hCache) (hLaw leaf hl)

/-- A local same-state comparison accumulates omitted-tail variation explicitly.
An own-cache policy comparison needs the separate accounting theorem below. -/
theorem next_edge_tail_regret_transfer {Arm : Type*}
    (reward edge tail : ℕ → Arm → ℝ) (chosen comparator : ℕ → Arm)
    (eta : ℝ) (hEta : 0 ≤ eta) (variation : ℕ → ℝ) (T : ℕ)
    (hVariation : ∀ t ∈ range T, tail t (chosen t) - tail t (comparator t) ≤ variation t) :
    (∑ t ∈ range T,
      (AgentUCT.net (reward t (comparator t))
          (edge t (comparator t) + tail t (comparator t)) eta -
        AgentUCT.net (reward t (chosen t)) (edge t (chosen t) + tail t (chosen t)) eta)) ≤
    (∑ t ∈ range T,
      (AgentUCT.net (reward t (comparator t)) (edge t (comparator t)) eta -
        AgentUCT.net (reward t (chosen t)) (edge t (chosen t)) eta)) +
      eta * ∑ t ∈ range T, variation t := by
  rw [mul_sum, ← sum_add_distrib]
  apply sum_le_sum
  intro t ht
  have h := mul_le_mul_of_nonneg_left (hVariation t ht) hEta
  unfold AgentUCT.net
  nlinarith

/-- Next-edge has logarithmic own-cache net regret for cold work or equal total overhead.
This is an upper bound, not an improvement over UCT or an endpoint-utility guarantee. -/
theorem next_edge_own_cache_log_bound (qids : Finset Qid) (root : List Action)
    (terminals : Finset (List Action)) (hTerminals : terminals.Nonempty)
    (reward : List Action → ℝ)
    (hReward : ∀ leaf ∈ terminals, 0 ≤ reward leaf ∧ reward leaf ≤ 1)
    (hAntichain : ∀ p ∈ terminals, ∀ q ∈ terminals, p <+: q → p = q)
    (prediction : Qid × List Action → ℝ) (hPrediction : ∀ r, 0 ≤ prediction r)
    (weight : Qid × List Action → ℝ) (hWeight : ∀ r, 0 ≤ weight r)
    (gamma c eta : ℝ) (hc : 0 < c) (hEta : 0 ≤ eta)
    (initial : PersistentCaches Qid Action)
    (hInitial : initial.restorable = initial.everMaterialized)
    (hResources : initial.everMaterialized ⊆ workflowResources qids root terminals) :
    ∃ delta : ℝ, 0 < delta ∧ ∀ actual comparator : List (TreeEvaluation Action),
      FixedTableEvents terminals reward actual →
      LegalTreeRun (fun p ↦ p ∈ terminals) {[]} actual →
      TreeAllocationRule terminals c (nextEdgePenalty qids root prediction gamma initial) actual →
      FixedTableEvents terminals reward comparator → actual.length = comparator.length →
      ∀ (actualOverhead comparatorOverhead : TreeEvaluation Action → ℝ)
        (comparatorInitial : MeteredTreeState Qid Action),
      (actual.map actualOverhead).sum = (comparator.map comparatorOverhead).sum →
      let constants := treeRateConstants terminals c 0 delta 0 (topologyDepth terminals)
      cumulativePolicyNetRegret eta actual comparator
        (meteredSearchCost qids root weight actualOverhead actual
          ⟨emptyStatistics, initial.everMaterialized, 0, 0⟩)
        (meteredSearchCost qids root weight comparatorOverhead comparator comparatorInitial) ≤
      constants.1 * Real.log (actual.length + 1 : ℕ) + constants.2 +
        eta * (cacheWeight weight (workflowResources qids root terminals) -
          cacheWeight weight initial.everMaterialized) := by
  obtain ⟨delta, hd, hQuality⟩ := next_edge_uniform_root_log_bound qids root terminals hTerminals
    reward hReward hAntichain prediction hPrediction gamma c hc initial hInitial
  refine ⟨delta, hd, ?_⟩
  intro actual comparator hActual hLegal hRule hComparator hLength actualOverhead
    comparatorOverhead comparatorInitial hSame
  have hCost := own_cache_cost_difference_common_overhead qids root terminals weight hWeight
    actualOverhead comparatorOverhead actual comparator
    ⟨emptyStatistics, initial.everMaterialized, 0, 0⟩ comparatorInitial
    (fun e he ↦ (hActual e he).1) hResources hSame
  have hNet := policy_net_regret_from_quality (subtreeValue terminals reward []) eta _ _ _
    actual comparator hEta hLength (by
      intro e he
      rw [(hComparator e he).2]
      exact subtreeValue_upper terminals reward [] e.terminal (hComparator e he).1 List.nil_prefix)
    hCost
  exact hNet.trans (add_le_add_right (hQuality actual hActual hLegal hRule) _)

end AgentUCTPaper
end
end CompleteProofSource35

/-!
## SOURCE 36: AgentUCTPaper/TreeGraphInformation.lean
Original definitions, theorem statements, and complete proof bodies.
-/
section CompleteProofSource36

/-! # Information retained by a qid-prefix cache

Full-panel execution admits a prefix-level quotient, even for a nonrectangular cache
when fixed resource weights are aggregated as residual bills. Query-selective demands
can distinguish caches with identical per-prefix hit counts and residual bills.
The counterexample uses two one-step terminal prefixes, so prefix completeness holds.
-/

set_option autoImplicit false
noncomputable section

namespace AgentUCTPaper
open Finset

variable {Q P : Type*} [DecidableEq Q] [DecidableEq P]

/-- A fixed full panel only needs the residual bill of each prefix for its next bill. -/
theorem full_panel_residual_quotient (weight : Q × P → ℝ)
    (cached : Finset (Q × P)) (qids : Finset Q) (prefixes : Finset P) :
    coldWork weight cached (qids ×ˢ prefixes) =
      ∑ p ∈ prefixes, ∑ q ∈ qids, if (q, p) ∈ cached then 0 else weight (q, p) := by
  simp only [coldWork, sdiff_eq_filter, sum_filter, sum_product]
  rw [sum_comm]
  apply sum_congr rfl
  intro p _
  apply sum_congr rfl
  intro q _
  split_ifs <;> rfl

/-- Rectangular caches reduce exactly to a weighted prefix cache. -/
theorem rectangular_cache_cost_quotient (weight : Q × P → ℝ)
    (qids : Finset Q) (saved demanded : Finset P) :
    coldWork weight (qids ×ˢ saved) (qids ×ˢ demanded) =
      coldWork (fun p ↦ ∑ q ∈ qids, weight (q, p)) saved demanded := by
  rw [full_panel_residual_quotient]
  simp only [coldWork, sdiff_eq_filter, sum_filter]
  apply sum_congr rfl
  intro p _
  by_cases hp : p ∈ saved
  · simp only [mem_product, hp, and_true, not_true_eq_false, if_false]
    exact sum_eq_zero (fun q hq ↦ if_pos hq)
  · simp only [mem_product, hp, and_false, if_false, not_false_eq_true, if_true]

/-- A complete-panel publication preserves rectangularity. -/
theorem full_panel_publication_rectangular (qids : Finset Q) (saved demanded : Finset P) :
    (qids ×ˢ saved) ∪ (qids ×ˢ demanded) = qids ×ˢ (saved ∪ demanded) := by
  exact product_union.symm

/-- The quotient is preserved along every finite full-panel publication history. -/
theorem full_panel_history_rectangular (qids : Finset Q) (saved : Finset P)
    (demands : List (Finset P)) :
    demands.foldl (fun cached demand ↦ cached ∪ (qids ×ˢ demand)) (qids ×ˢ saved) =
      qids ×ˢ demands.foldl (fun cached demand ↦ cached ∪ demand) saved := by
  induction demands generalizing saved with
  | nil => rfl
  | cons demand rest ih =>
    simpa only [List.foldl_cons, full_panel_publication_rectangular] using ih (saved ∪ demand)

/-- Full-panel publication also updates residual prefix bills without qid identities. -/
theorem full_panel_residual_update (weight : Q × P → ℝ) (cached : Finset (Q × P))
    (qids : Finset Q) (published : Finset P) (p : P) :
    (∑ q ∈ qids, if (q, p) ∈ cached ∪ (qids ×ˢ published) then 0 else weight (q, p)) =
      if p ∈ published then 0 else
        ∑ q ∈ qids, if (q, p) ∈ cached then 0 else weight (q, p) := by
  by_cases hp : p ∈ published
  · simp only [hp, if_true]
    apply sum_eq_zero
    intro q hq
    simp [hq, hp]
  · simp [hp]

namespace GraphWitness

def leftCache : Finset (Bool × Bool) := {(false, false), (true, true)}
def rightCache : Finset (Bool × Bool) := {(true, false), (false, true)}
def hitCount (cached : Finset (Bool × Bool)) (p : Bool) : ℕ :=
  ((univ : Finset Bool).filter (fun q ↦ (q, p) ∈ cached)).card
def bill (cached : Finset (Bool × Bool)) (action : Bool) : ℝ :=
  coldWork (fun _ ↦ 1) cached {(false, action)}

end GraphWitness

open GraphWitness

/-- Prefix counts discard exactly the query identity needed by the next partial panel. -/
theorem GraphWitness.counts_equal : hitCount leftCache = hitCount rightCache := by
  funext p
  cases p <;> decide

/-- Even the exact residual full-panel bill is identical in both states. -/
theorem GraphWitness.residual_bills_equal (p : Bool) :
    coldWork (fun _ ↦ (1 : ℝ)) leftCache (univ ×ˢ {p}) =
      coldWork (fun _ ↦ (1 : ℝ)) rightCache (univ ×ˢ {p}) := by
  cases p <;> norm_num [coldWork, leftCache, rightCache] <;> decide

/-- For the same active qid, the two prefixes exchange their cold bills. -/
theorem GraphWitness.bills_reverse :
    bill leftCache false = 0 ∧ bill leftCache true = 1 ∧
      bill rightCache false = 1 ∧ bill rightCache true = 0 := by
  norm_num [bill, coldWork, leftCache, rightCache]
  decide

/-- No deterministic count-only policy minimizes the next bill in both states. -/
theorem GraphWitness.no_count_only_optimal_policy :
    ¬ ∃ choose : (Bool → ℕ) → Bool,
      (∀ a, bill leftCache (choose (hitCount leftCache)) ≤ bill leftCache a) ∧
      (∀ a, bill rightCache (choose (hitCount rightCache)) ≤ bill rightCache a) := by
  rintro ⟨choose, hl, hr⟩
  have hl' := hl false
  have hr' := hr true
  rw [← counts_equal] at hr'
  rcases bills_reverse with ⟨h00, h01, h10, h11⟩
  cases h : choose (hitCount leftCache)
  · rw [h, h10, h11] at hr'
    norm_num at hr'
  · rw [h, h01, h00] at hl'
    norm_num at hl'

/-- An identity-blind randomized choice incurs at least half a unit in one state.
Here p is its probability of choosing the first action in either indistinguishable state. -/
theorem GraphWitness.randomized_excess_lower_bound (p : ℝ) :
    (1 / 2 : ℝ) ≤ max (1 - p) p := by
  have h1 := le_max_left (1 - p) p
  have h2 := le_max_right (1 - p) p
  linarith

/-- A single predicted bill for indistinguishable zero/one bills has irreducible error. -/
theorem GraphWitness.common_estimate_error_lower_bound (estimate : ℝ) :
    (1 / 2 : ℝ) ≤ max |estimate| |estimate - 1| := by
  have h1 := le_abs_self estimate
  have h2 := neg_le_abs (estimate - 1)
  have h3 := le_max_left |estimate| |estimate - 1|
  have h4 := le_max_right |estimate| |estimate - 1|
  linarith

/-- With a unit recurring bill and a unit remaining budget, feasibility reverses. -/
theorem GraphWitness.budget_feasibility_reverses :
    (1 + bill leftCache false ≤ 1 ∧ ¬ 1 + bill leftCache true ≤ 1) ∧
      (1 + bill rightCache true ≤ 1 ∧ ¬ 1 + bill rightCache false ≤ 1) := by
  rcases bills_reverse with ⟨h00, h01, h10, h11⟩
  rw [h00, h01, h10, h11]
  norm_num

end AgentUCTPaper
end
end CompleteProofSource36

/-!
## SOURCE 37: AgentUCTPaper/TreeFiniteBudget.lean
Original definitions, theorem statements, and complete proof bodies.
-/
section CompleteProofSource37

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
end
end CompleteProofSource37

/-!
## SOURCE 38: AgentUCTPaper/TreeSharedCache.lean
Original definitions, theorem statements, and complete proof bodies.
-/
section CompleteProofSource38

/-! # Fixed reward panels sharing qid-prefix materializations

Each panel owns its tree and raw-reward statistics. Other panels may publish
additional restorable resources between its visits. Their observations are not
backed up into this panel. Thus its reward table remains fixed, while its bill
depends on the full bipartite cache. The theorem allows arbitrary extra cache
contents: own successful publications are always retained.
-/

set_option autoImplicit false
noncomputable section

namespace AgentUCTPaper

variable {Qid Action : Type*} [DecidableEq Qid] [DecidableEq Action]

/-- A panel's own publication history plus materializations from other panels. -/
def sharedColdPenalty (qids : Finset Qid) (root : List Action)
    (terminals : Finset (List Action)) (prediction : Qid × List Action → ℝ) (gamma : ℝ)
    (law : List (TreeEvaluation Action) → List Action → Action → List Action → ℝ)
    (initial : PersistentCaches Qid Action)
    (extra : List (TreeEvaluation Action) → Finset (Qid × List Action))
    (before : List (TreeEvaluation Action)) (p : List Action) (a : Action) : ℝ :=
  gamma * referenceColdCost qids root terminals prediction (law before p a)
    ((replayPublished qids (fun x ↦ root ++ x) before initial).restorable ∪ extra before)
    (p ++ [a])

/-- Sharing saved prefixes preserves the whole-tree logarithmic quality bound.
The extra cache may depend on the entire external schedule, encoded along the
local history. Rewards and tree statistics still belong to this fixed panel. -/
theorem shared_cache_uniform_root_log_bound (qids : Finset Qid) (root : List Action)
    (terminals : Finset (List Action)) (hTerminals : terminals.Nonempty)
    (reward : List Action → ℝ)
    (hReward : ∀ leaf ∈ terminals, 0 ≤ reward leaf ∧ reward leaf ≤ 1)
    (hAntichain : ∀ p ∈ terminals, ∀ q ∈ terminals, p <+: q → p = q)
    (prediction : Qid × List Action → ℝ) (hPrediction : ∀ r, 0 ≤ prediction r)
    (gamma c : ℝ) (hGamma : 0 ≤ gamma) (hc : 0 < c)
    (law : List (TreeEvaluation Action) → List Action → Action → List Action → ℝ)
    (hLaw : ∀ before p a, a ∈ availableChildren terminals p →
      ∀ leaf ∈ subtreeTerminals terminals (p ++ [a]), 0 ≤ law before p a leaf)
    (hMass : ∀ before p a, a ∈ availableChildren terminals p →
      ∑ leaf ∈ subtreeTerminals terminals (p ++ [a]), law before p a leaf = 1)
    (initial : PersistentCaches Qid Action)
    (hInitial : initial.restorable = initial.everMaterialized)
    (extra : List (TreeEvaluation Action) → Finset (Qid × List Action)) :
    ∃ delta : ℝ, 0 < delta ∧ ∀ events : List (TreeEvaluation Action),
      FixedTableEvents terminals reward events →
      LegalTreeRun (fun p ↦ p ∈ terminals) {[]} events →
      TreeAllocationRule terminals c
        (sharedColdPenalty qids root terminals prediction gamma law initial extra) events →
      let H := gamma * cacheWeight prediction (workflowResources qids root terminals)
      let cacheTime := coverageVisits terminals c H (topologyDepth terminals)
      let constants := treeRateConstants terminals c H delta cacheTime
        (topologyDepth terminals)
      backedDeficit (subtreeValue terminals reward []) events [] ≤
        constants.1 * Real.log (events.length + 1 : ℕ) + constants.2 := by
  obtain ⟨delta, hDelta, hGaps⟩ := finite_tree_positive_edge_gap terminals reward
  refine ⟨delta, hDelta, ?_⟩
  intro events hTable hLegal hRule
  let H := gamma * cacheWeight prediction (workflowResources qids root terminals)
  let penalty := sharedColdPenalty qids root terminals prediction gamma law initial extra
  let cacheTime := coverageVisits terminals c H (topologyDepth terminals)
  have hH : 0 ≤ H := mul_nonneg hGamma (Finset.sum_nonneg (fun r _ ↦ hPrediction r))
  have run : BoundedTreeRun terminals c H penalty events := {
    terminal := fun event he ↦ (hTable event he).1
    reward := by
      intro event he
      rw [(hTable event he).2]
      exact hReward event.terminal (hTable event he).1
    legal := hLegal
    rule := hRule
    penalty_bounded := by
      intro before _ p a ha
      obtain ⟨h0, h1⟩ := referenceColdCost_bounded qids root terminals prediction hPrediction
        (law before p a) _ (p ++ [a]) (hLaw before p a ha) (hMass before p a ha)
      exact ⟨mul_nonneg hGamma h0, mul_le_mul_of_nonneg_left h1 hGamma⟩ }
  have hZero : ∀ before, before <+: events → cacheTime ≤ before.length →
      ∀ p ∈ workflowNodes terminals, ∀ a ∈ availableChildren terminals p,
        penalty before p a = 0 := by
    intro before hp ht p _ a _
    have hCovered := actual_restorable_coverage qids root terminals c H penalty
      (fun _ ↦ 0) (fun _ ↦ 0) before
      ⟨emptyStatistics, initial.everMaterialized, 0, 0⟩ initial hInitial rfl
      (run.prefix hp) hc hH hAntichain ht
    change gamma * referenceColdCost qids root terminals prediction _ _ _ = 0
    rw [referenceColdCost_zero qids root terminals prediction _ _ _
      (hCovered.trans Finset.subset_union_left), mul_zero]
  obtain ⟨leaf, hl⟩ := hTerminals
  have hRoot : [] ∈ workflowNodes terminals :=
    (workflowNodes_mem terminals []).mpr ⟨leaf, hl, List.nil_prefix⟩
  have hResult := actual_subtree_log_deficit terminals reward c H delta cacheTime
    penalty hReward hc hH hDelta hAntichain hGaps (topologyDepth terminals) events run
    hTable hZero [] hRoot (by simp)
  simpa only [root_count_eq_length] using hResult

/-- A fixed finite family of panel bounds gives a logarithmic scheduled bound. -/
theorem fixed_panel_family_log_bound {Context : Type*} (contexts : Finset Context)
    (regret A B : Context → ℝ) (visits : Context → ℕ) (T : ℕ)
    (hA : ∀ j ∈ contexts, 0 ≤ A j)
    (hVisits : ∀ j ∈ contexts, visits j ≤ T)
    (hBound : ∀ j ∈ contexts,
      regret j ≤ A j * Real.log (visits j + 1 : ℕ) + B j) :
    (∑ j ∈ contexts, regret j) ≤
      (∑ j ∈ contexts, A j) * Real.log (T + 1 : ℕ) + ∑ j ∈ contexts, B j := by
  rw [Finset.sum_mul, ← Finset.sum_add_distrib]
  apply Finset.sum_le_sum
  intro j hj
  have hLog : Real.log (visits j + 1 : ℕ) ≤ Real.log (T + 1 : ℕ) :=
    Real.log_le_log (by positivity) (by exact_mod_cast Nat.add_le_add_right (hVisits j hj) 1)
  exact (hBound j hj).trans (add_le_add_right (mul_le_mul_of_nonneg_left hLog (hA j hj)) _)

end AgentUCTPaper

namespace AgentUCTPaper

variable {Qid Action : Type*} [DecidableEq Qid] [DecidableEq Action]

/-- Nonnegative cold-cost truncations inherit the shared-panel quality rate.
This covers a first-unpaid estimate once its pointwise domination by the
complete forecast is established. Equality with ordinary UCT is not assumed. -/
theorem dominated_cold_shared_root_log_bound (qids : Finset Qid) (root : List Action)
    (terminals : Finset (List Action)) (hTerminals : terminals.Nonempty)
    (reward : List Action → ℝ)
    (hReward : ∀ leaf ∈ terminals, 0 ≤ reward leaf ∧ reward leaf ≤ 1)
    (hAntichain : ∀ p ∈ terminals, ∀ q ∈ terminals, p <+: q → p = q)
    (prediction : Qid × List Action → ℝ) (hPrediction : ∀ r, 0 ≤ prediction r)
    (gamma c : ℝ) (hGamma : 0 ≤ gamma) (hc : 0 < c)
    (law : List (TreeEvaluation Action) → List Action → Action → List Action → ℝ)
    (hLaw : ∀ before p a, a ∈ availableChildren terminals p →
      ∀ leaf ∈ subtreeTerminals terminals (p ++ [a]), 0 ≤ law before p a leaf)
    (hMass : ∀ before p a, a ∈ availableChildren terminals p →
      ∑ leaf ∈ subtreeTerminals terminals (p ++ [a]), law before p a leaf = 1)
    (initial : PersistentCaches Qid Action)
    (hInitial : initial.restorable = initial.everMaterialized)
    (extra : List (TreeEvaluation Action) → Finset (Qid × List Action))
    (penalty : List (TreeEvaluation Action) → List Action → Action → ℝ)
    (hNonneg : ∀ before p a, a ∈ availableChildren terminals p → 0 ≤ penalty before p a)
    (hDominated : ∀ before p a, a ∈ availableChildren terminals p →
      penalty before p a ≤ sharedColdPenalty qids root terminals prediction gamma law initial extra before p a) :
    ∃ delta : ℝ, 0 < delta ∧ ∀ events : List (TreeEvaluation Action),
      FixedTableEvents terminals reward events →
      LegalTreeRun (fun p ↦ p ∈ terminals) {[]} events →
      TreeAllocationRule terminals c penalty events →
      let H := gamma * cacheWeight prediction (workflowResources qids root terminals)
      let cacheTime := coverageVisits terminals c H (topologyDepth terminals)
      let constants := treeRateConstants terminals c H delta cacheTime (topologyDepth terminals)
      backedDeficit (subtreeValue terminals reward []) events [] ≤
        constants.1 * Real.log (events.length + 1 : ℕ) + constants.2 := by
  -- Q8 domination 1: Fix delta before every history; dominate the actual penalty by a common nonnegative completion cold bill.
  obtain ⟨delta, hDelta, hGaps⟩ := finite_tree_positive_edge_gap terminals reward
  refine ⟨delta, hDelta, ?_⟩
  intro events hTable hLegal hRule
  let H := gamma * cacheWeight prediction (workflowResources qids root terminals)
  let cacheTime := coverageVisits terminals c H (topologyDepth terminals)
  have hH : 0 ≤ H := mul_nonneg hGamma (Finset.sum_nonneg (fun r _ ↦ hPrediction r))
  have run : BoundedTreeRun terminals c H penalty events := {
    terminal := fun event he ↦ (hTable event he).1
    reward := by
      intro event he
      rw [(hTable event he).2]
      exact hReward event.terminal (hTable event he).1
    legal := hLegal
    rule := hRule
    penalty_bounded := by
      intro before _ p a ha
      obtain ⟨_, h1⟩ := referenceColdCost_bounded qids root terminals prediction hPrediction
        (law before p a) _ (p ++ [a]) (hLaw before p a ha) (hMass before p a ha)
      exact ⟨hNonneg before p a ha,
        (hDominated before p a ha).trans (mul_le_mul_of_nonneg_left h1 hGamma)⟩ }
  have hZero : ∀ before, before <+: events → cacheTime ≤ before.length →
      ∀ p ∈ workflowNodes terminals, ∀ a ∈ availableChildren terminals p,
        penalty before p a = 0 := by
    intro before hp ht p _ a ha
    have hCovered := actual_restorable_coverage qids root terminals c H penalty
      (fun _ ↦ 0) (fun _ ↦ 0) before
      ⟨emptyStatistics, initial.everMaterialized, 0, 0⟩ initial hInitial rfl
      (run.prefix hp) hc hH hAntichain ht
    have hFull : sharedColdPenalty qids root terminals prediction gamma law initial extra before p a = 0 := by
      -- Q4 domination 2: This tree's persistent publications cover all resources; union with extra shared resources preserves coverage.
      change gamma * referenceColdCost qids root terminals prediction _ _ _ = 0
      rw [referenceColdCost_zero qids root terminals prediction _ _ _
        (hCovered.trans Finset.subset_union_left), mul_zero]
    exact le_antisymm ((hDominated before p a ha).trans_eq hFull) (hNonneg before p a ha)
    -- Actual penalty lies between zero and a zero complete cold penalty; antisymmetry gives zero, then apply Q7 induction.
  obtain ⟨leaf, hl⟩ := hTerminals
  have hRoot : [] ∈ workflowNodes terminals :=
    (workflowNodes_mem terminals []).mpr ⟨leaf, hl, List.nil_prefix⟩
  have hResult := actual_subtree_log_deficit terminals reward c H delta cacheTime
    penalty hReward hc hH hDelta hAntichain hGaps (topologyDepth terminals) events run
    hTable hZero [] hRoot (by simp)
  simpa only [root_count_eq_length] using hResult

end AgentUCTPaper
end
end CompleteProofSource38

/-!
## SOURCE 39: AgentUCTPaper/TreeNextUnpaid.lean
Original definitions, theorem statements, and complete proof bodies.
-/
section CompleteProofSource39

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
end
end CompleteProofSource39

/-!
## SOURCE 40: AgentUCTPaper/TreeDemandQuotient.lean
Original definitions, theorem statements, and complete proof bodies.
-/
section CompleteProofSource40

/-! # Exact cache compression for a fixed family of query demands

Queries may be grouped when every allowed panel treats all members of a group
identically. Weighted residual bills per group and prefix are sufficient both
for billing and for publication updates. Merging queries that a panel separates
loses information, even with unit prices and binary missing-resource vectors.
This is a statement about information; no particular storage layout is required.
-/

set_option autoImplicit false
noncomputable section
namespace AgentUCTPaper
open Finset

variable {Q C P : Type*} [Fintype Q] [DecidableEq Q] [DecidableEq C] [DecidableEq P]

def groupedQuantity (group : Q → C) (quantity : Q → ℝ) (c : C) : ℝ :=
  ∑ q : Q, if group q = c then quantity q else 0

def groupedResidual (group : Q → C) (weight : Q × P → ℝ)
    (cached : Finset (Q × P)) (c : C) (p : P) : ℝ :=
  groupedQuantity group (fun q ↦ if (q, p) ∈ cached then 0 else weight (q, p)) c

omit [DecidableEq Q] in
/-- Group totals recover every panel that is a union of groups. -/
theorem grouped_panel_sum (group : Q → C) (quantity : Q → ℝ) (selected : Finset C) :
    (∑ q ∈ univ.filter (fun q ↦ group q ∈ selected), quantity q) =
      ∑ c ∈ selected, groupedQuantity group quantity c := by
  unfold groupedQuantity
  rw [sum_comm]
  simp [sum_filter]

/-- Group residuals give exactly the physical bill of every allowed completion. -/
theorem demand_group_cost_quotient (group : Q → C) (weight : Q × P → ℝ)
    (cached : Finset (Q × P)) (selected : Finset C) (prefixes : Finset P) :
    coldWork weight cached ((univ.filter (fun q ↦ group q ∈ selected)) ×ˢ prefixes) =
      ∑ p ∈ prefixes, ∑ c ∈ selected, groupedResidual group weight cached c p := by
  rw [full_panel_residual_quotient]
  apply sum_congr rfl
  intro p _
  exact grouped_panel_sum group _ selected

/-- Publication is closed on the same summary: affected group-prefix cells become zero. -/
theorem demand_group_publication (group : Q → C) (weight : Q × P → ℝ)
    (cached : Finset (Q × P)) (selected : Finset C) (prefixes : Finset P)
    (c : C) (p : P) :
    groupedResidual group weight
      (cached ∪ ((univ.filter (fun q ↦ group q ∈ selected)) ×ˢ prefixes)) c p =
      if c ∈ selected ∧ p ∈ prefixes then 0 else groupedResidual group weight cached c p := by
  unfold groupedResidual groupedQuantity
  by_cases hc : c ∈ selected <;> by_cases hp : p ∈ prefixes
  · simp only [hc, hp, and_self, if_true]
    apply sum_eq_zero
    intro q _
    by_cases hq : group q = c <;> simp [hq, hc, hp]
  · simp [hp]
  · simp only [hc, false_and, if_false]
    apply sum_congr rfl
    intro q _
    by_cases hq : group q = c <;> simp [hq, hc, hp]
  · simp [hp]

/-- The canonical grouping is the vector of memberships in the allowed panels. -/
def panelProfile {J : Type*} (panels : J → Finset Q) (q : Q) : J → Prop :=
  fun j ↦ q ∈ panels j

omit [Fintype Q] [DecidableEq Q] [DecidableEq C] in
/-- A grouping respects every panel exactly when equal groups have equal profiles. -/
theorem grouping_respects_profiles {J : Type*} (panels : J → Finset Q) (group : Q → C) :
    (∀ q r, group q = group r → panelProfile panels q = panelProfile panels r) ↔
      ∀ j q r, group q = group r → (q ∈ panels j ↔ r ∈ panels j) := by
  constructor
  · intro h j q r hqr
    exact Iff.of_eq (congrFun (h q r hqr) j)
  · intro h q r hqr
    funext j
    exact propext (h j q r hqr)

private theorem grouped_singleton (group : Q → C) (q : Q) (c : C) :
    groupedQuantity group (fun r ↦ if r = q then 1 else 0) c =
      if group q = c then 1 else 0 := by
  unfold groupedQuantity
  rw [sum_eq_single q]
  · simp
  · intro r _ hr
    simp [hr]
  · simp

/-- A group that merges two differently demanded queries cannot determine every bill.
The witness quantities are realizable binary residuals with unit physical prices. -/
theorem demand_separating_merge_loses_information (group : Q → C) (panel : Finset Q)
    (q r : Q) (hGroup : group q = group r) (hq : q ∈ panel) (hr : r ∉ panel) :
    ¬ ∃ decode : (C → ℝ) → ℝ, ∀ quantity : Q → ℝ,
      (∀ x, quantity x = 0 ∨ quantity x = 1) →
      decode (groupedQuantity group quantity) = ∑ x ∈ panel, quantity x := by
  rintro ⟨decode, hDecode⟩
  have hb (a : Q) (x : Q) : (if x = a then (1 : ℝ) else 0) = 0 ∨
      (if x = a then (1 : ℝ) else 0) = 1 := by split_ifs <;> simp
  have hLeft := hDecode (fun x ↦ if x = q then 1 else 0) (hb q)
  have hRight := hDecode (fun x ↦ if x = r then 1 else 0) (hb r)
  have hSame : groupedQuantity group (fun x ↦ if x = q then 1 else 0) =
      groupedQuantity group (fun x ↦ if x = r then 1 else 0) := by
    funext c
    simp only [grouped_singleton, hGroup]
  rw [hSame] at hLeft
  simp [hq] at hLeft
  simp [hr] at hRight
  linarith

end AgentUCTPaper
end
end CompleteProofSource40

/-!
## SOURCE 41: AgentUCTPaper/TreeDecisionValue.lean
Original definitions, theorem statements, and complete proof bodies.
-/
section CompleteProofSource41

/-! # Finite-decision value and its own-cache limit

Compare ordinary UCT and the priced rule at an identical state. The priced rule
always chooses a weakly cheaper predicted completion and bounds the sacrifice
in the unpriced index. Cost prediction error gives a robust physical saving
certificate. Whole-policy expenditure depends on the distinct resources each
policy discovers; local savings do not imply global or endpoint dominance.
-/

set_option autoImplicit false
noncomputable section
namespace AgentUCTPaper

/-- Pricing gives a bounded exchange of optimistic quality for predicted completion cost. -/
theorem priced_choice_tradeoff (ua ub ca cb gamma : ℝ) (hg : 0 < gamma)
    (hUCT : ua ≤ ub) (hPriced : ub - gamma * cb ≤ ua - gamma * ca) :
    ca ≤ cb ∧ 0 ≤ ub - ua ∧ ub - ua ≤ gamma * (cb - ca) := by
  -- L1: Ordinary index maximality gives a nonnegative index loss; U includes a bonus and is not a quality estimate alone.
  have hLossNonneg : 0 ≤ ub - ua := sub_nonneg.mpr hUCT
  -- L2: Rearrange priced-index maximality to bound this loss by gamma times predicted cost saving.
  have hLossUpper : ub - ua ≤ gamma * (cb - ca) := by nlinarith
  -- L3: With gamma > 0, ca > cb would make the upper bound negative, contradicting L1 and L2.
  have hCheaper : ca ≤ cb := by
    by_contra h
    have hCostOrder : cb < ca := lt_of_not_ge h
    nlinarith
  -- L4: Assemble the three named intermediate conclusions.
  exact ⟨hCheaper, hLossNonneg, hLossUpper⟩

/-- A predicted saving exceeding both cost errors certifies a physical mean-bill saving. -/
theorem physical_saving_certificate (ca cb ea eb ra rb : ℝ)
    (ha : |ea - ca| ≤ ra) (hb : |eb - cb| ≤ rb) :
    eb - ea - (ra + rb) ≤ cb - ca := by
  -- L5: Expand both absolute-error bounds; subtract their radii from predicted saving to bound physical saving.
  obtain ⟨hal, har⟩ := abs_le.mp ha
  obtain ⟨hbl, hbr⟩ := abs_le.mp hb
  linarith

/-- Approximate costs weaken same-state savings only by the two prediction errors. -/
theorem priced_choice_physical_cost (ua ub ca cb ea eb ra rb gamma : ℝ)
    (hg : 0 < gamma) (hUCT : ua ≤ ub)
    (hPriced : ub - gamma * eb ≤ ua - gamma * ea)
    (ha : |ea - ca| ≤ ra) (hb : |eb - cb| ≤ rb) :
    ca ≤ cb + ra + rb := by
  have hOrder := (priced_choice_tradeoff ua ub ea eb gamma hg hUCT hPriced).1
  have hSaving := physical_saving_certificate ca cb ea eb ra rb ha hb
  linarith

/-- The observed index margin certifies actual net gain when reward and bill errors are bounded. -/
theorem actual_net_gain_certificate (ua ub qa qb ca cb ea eb ra rb sa sb gamma : ℝ)
    (hg : 0 ≤ gamma) (hqa : |ua - qa| ≤ sa) (hqb : |ub - qb| ≤ sb)
    (hca : |ea - ca| ≤ ra) (hcb : |eb - cb| ≤ rb) :
    (ua - gamma * ea) - (ub - gamma * eb) - (sa + sb) - gamma * (ra + rb) ≤
      (qa - gamma * ca) - (qb - gamma * cb) := by
  -- L6: Also control quality errors; weight cost errors by nonnegative gamma and rearrange the net-value bound.
  obtain ⟨hqal, hqar⟩ := abs_le.mp hqa
  obtain ⟨hqbl, hqbr⟩ := abs_le.mp hqb
  have hCost := physical_saving_certificate ca cb ea eb ra rb hca hcb
  have hWeighted := mul_le_mul_of_nonneg_left hCost hg
  nlinarith

/-- Independent cache histories differ exactly by their exclusive new materializations. -/
theorem own_cache_cost_difference {R : Type*} [DecidableEq R] (weight : R → ℝ)
    (cached first second : Finset R) :
    coldWork weight cached first - coldWork weight cached second =
      coldWork weight (cached ∪ second) first - coldWork weight (cached ∪ first) second := by
  have h1 := coldWork_sequential_union weight cached first second
  have h2 := coldWork_sequential_union weight cached second first
  rw [Finset.union_comm second first] at h2
  linarith

/-- A scalar price can select either a better or a worse next terminal in two
indistinguishable pre-evaluation states. Both completions fit the same budget. -/
theorem priced_choice_no_universal_quality_dominance :
    (6 / 10 : ℝ) < 7 / 10 ∧
    (7 / 10 : ℝ) - 1 / 2 * 2 < 6 / 10 - 1 / 2 * 1 ∧
    (1 : ℝ) ≤ 2 ∧ (2 : ℝ) ≤ 2 ∧
    (0 - (1 / 2 : ℝ) * 1 < 1 - 1 / 2 * 2) ∧
    (0 - (1 / 2 : ℝ) * 2 < 1 - 1 / 2 * 1) := by
  norm_num

end AgentUCTPaper
end
end CompleteProofSource41

/-!
## SOURCE 42: AgentUCTPaper/DynamicCompletion.lean
Original definitions, theorem statements, and complete proof bodies.
-/
section CompleteProofSource42

/-! # Dynamic execution costs and optimistic allocation

Each realized execution has a finite resource demand. The resource type and the
sequence of future programs need not be known or finite in advance. Resource
prices are fixed for a realized key; recurring proposal/repair work is overhead.
Finite conditional scenario laws give the pre-proposal/post-proposal identity.
These statements do not assert a fixed-tree rate for an evolving edit tree.
-/

set_option autoImplicit false
noncomputable section
namespace AgentUCTPaper
open Finset

variable {R : Type*} [DecidableEq R]

def dynamicDemand : List (Finset R) → Finset R
  | [] => ∅
  | demand :: rest => demand ∪ dynamicDemand rest

def dynamicSpend (weight : R → ℝ) (cached : Finset R) : List (Finset R) → ℝ
  | [] => 0
  | demand :: rest => coldWork weight cached demand +
      dynamicSpend weight (cached ∪ demand) rest

/-- Realized finite traces admit exact accounting without a predeclared resource universe. -/
theorem dynamic_spend_union (weight : R → ℝ) (cached : Finset R)
    (demands : List (Finset R)) :
    dynamicSpend weight cached demands = coldWork weight cached (dynamicDemand demands) := by
  induction demands generalizing cached with
  | nil => simp [dynamicSpend, dynamicDemand, coldWork]
  | cons demand rest ih =>
    simp only [dynamicSpend, dynamicDemand, ih]
    exact (coldWork_sequential_union weight cached demand (dynamicDemand rest)).symm

/-- Stopped logical slots may publish checkpoints while incurring zero model work. -/
theorem zero_weight_padding (weight : R → ℝ) (cached demand padding : Finset R)
    (hZero : ∀ r ∈ padding, weight r = 0) :
    coldWork weight cached (demand ∪ padding) = coldWork weight cached demand := by
  rw [coldWork_sequential_union]
  suffices coldWork weight (cached ∪ demand) padding = 0 by linarith
  apply sum_eq_zero
  intro r hr
  exact hZero r (mem_sdiff.mp hr).1

/-- Growing caches never amortize recurring work: the overhead sum remains in full. -/
theorem dynamic_spend_with_overhead (weight : R → ℝ) (cached : Finset R)
    (demands : List (Finset R)) (overhead : List ℝ) :
    dynamicSpend weight cached demands + overhead.sum =
      coldWork weight cached (dynamicDemand demands) + overhead.sum := by
  rw [dynamic_spend_union]

/-- Pre-proposal expectation equals conditioning on each generated child and execution.
The execution law may depend on the child; no independence is assumed. -/
theorem generated_completion_two_stage {G E : Type*}
    (children : Finset G) (traces : G → Finset E) (proposalLaw : G → ℝ)
    (executionLaw : G → E → ℝ) (proposalCost : G → ℝ) (bill : G → E → ℝ)
    (hMass : ∀ g ∈ children, ∑ e ∈ traces g, executionLaw g e = 1) :
    (∑ g ∈ children, proposalLaw g *
      (proposalCost g + ∑ e ∈ traces g, executionLaw g e * bill g e)) =
    ∑ g ∈ children, ∑ e ∈ traces g,
      proposalLaw g * executionLaw g e * (proposalCost g + bill g e) := by
  apply sum_congr rfl
  intro g hg
  simp_rw [mul_add, sum_add_distrib]
  rw [← sum_mul, ← mul_sum, hMass g hg, mul_one, mul_sum]
  congr 1
  apply sum_congr rfl
  intro e _
  ring

/-- The optimistic net rule has a one-step guarantee against the current conditional oracle.
Only the chosen arm's uncertainty widths appear in the bound. -/
theorem dynamic_optimistic_net_loss (qa qb ua ub ca cb la lb rq rc gamma : ℝ)
    (hg : 0 ≤ gamma) (hRewardB : qb ≤ ub) (hRewardA : ua - qa ≤ rq)
    (hCostB : lb ≤ cb) (hCostA : ca - la ≤ rc)
    (hSelect : ub - gamma * lb ≤ ua - gamma * la) :
    (qb - gamma * cb) - (qa - gamma * ca) ≤ rq + gamma * rc := by
  have hb := mul_le_mul_of_nonneg_left hCostB hg
  have ha := mul_le_mul_of_nonneg_left hCostA hg
  nlinarith

/-- The dynamic bound accumulates widths at each actual history, including cache state.
The comparator is the one-step conditional oracle at those same histories. -/
theorem dynamic_optimistic_cumulative (qa qb ua ub ca cb la lb rq rc : ℕ → ℝ)
    (gamma : ℝ) (hg : 0 ≤ gamma) (T : ℕ)
    (hRewardB : ∀ t ∈ range T, qb t ≤ ub t)
    (hRewardA : ∀ t ∈ range T, ua t - qa t ≤ rq t)
    (hCostB : ∀ t ∈ range T, lb t ≤ cb t)
    (hCostA : ∀ t ∈ range T, ca t - la t ≤ rc t)
    (hSelect : ∀ t ∈ range T, ub t - gamma * lb t ≤ ua t - gamma * la t) :
    (∑ t ∈ range T, ((qb t - gamma * cb t) - (qa t - gamma * ca t))) ≤
      (∑ t ∈ range T, rq t) + gamma * ∑ t ∈ range T, rc t := by
  rw [mul_sum, ← sum_add_distrib]
  apply sum_le_sum
  intro t ht
  exact dynamic_optimistic_net_loss _ _ _ _ _ _ _ _ _ _ _ hg
    (hRewardB t ht) (hRewardA t ht) (hCostB t ht) (hCostA t ht) (hSelect t ht)

/-- A fresh key remains chargeable despite persistent caching of every older key. -/
theorem fresh_dynamic_resource_cost (t : ℕ) :
    coldWork (fun _ : ℕ ↦ (1 : ℝ)) (range t) {t} = 1 := by
  have h : ({t} : Finset ℕ) \ range t = {t} := by
    ext r
    simp only [mem_sdiff, mem_singleton, mem_range]
    omega
  simp [coldWork, h]

/-- With fresh resources, an omitted suffix can recur at every step. This exact
ledger witness prevents using finite total cold work for an unbounded edit space. -/
theorem recurring_omitted_suffix (T : ℕ) :
    (∑ t ∈ range T, coldWork (fun _ : ℕ ↦ (1 : ℝ)) (range t) {t}) = (T : ℝ) := by
  simp [fresh_dynamic_resource_cost]

/-- History-conditioned resource predictions may decrease within a fixed envelope. -/
theorem cold_prediction_envelope (base prediction : R → ℝ) (cached demand : Finset R)
    (hNonneg : ∀ r, 0 ≤ prediction r) (hUpper : ∀ r, prediction r ≤ base r) :
    0 ≤ coldWork prediction cached demand ∧
      coldWork prediction cached demand ≤ coldWork base cached demand := by
  constructor
  · exact sum_nonneg (fun r _ ↦ hNonneg r)
  · exact sum_le_sum (fun r _ ↦ hUpper r)

/-- A checkpoint may certify zero execution work in part of its future subtree. -/
theorem checkpoint_zero_prediction_envelope (base : R → ℝ) (hBase : ∀ r, 0 ≤ base r)
    (knownZero : R → Prop) [DecidablePred knownZero] (cached demand : Finset R) :
    0 ≤ coldWork (fun r ↦ if knownZero r then 0 else base r) cached demand ∧
      coldWork (fun r ↦ if knownZero r then 0 else base r) cached demand ≤
        coldWork base cached demand := by
  apply cold_prediction_envelope
  · intro r
    split_ifs <;> simp_all
  · intro r
    split_ifs <;> simp_all

/-- Any nonnegative continuation law preserves the envelope, even if the live
prediction and law both depend on the current checkpoint history. This discharges
the domination premise of dominated_cold_shared_root_log_bound at each history. -/
theorem completion_prediction_envelope {G : Type*} (outcomes : Finset G)
    (law : G → ℝ) (hLaw : ∀ g ∈ outcomes, 0 ≤ law g)
    (demands : G → Finset R) (base prediction : R → ℝ) (cached : Finset R)
    (hNonneg : ∀ r, 0 ≤ prediction r) (hUpper : ∀ r, prediction r ≤ base r) :
    0 ≤ ∑ g ∈ outcomes, law g * coldWork prediction cached (demands g) ∧
      (∑ g ∈ outcomes, law g * coldWork prediction cached (demands g)) ≤
      ∑ g ∈ outcomes, law g * coldWork base cached (demands g) := by
  constructor
  · apply sum_nonneg
    intro g hg
    exact mul_nonneg (hLaw g hg)
      (cold_prediction_envelope base prediction cached (demands g) hNonneg hUpper).1
  · apply sum_le_sum
    intro g hg
    exact mul_le_mul_of_nonneg_left
      (cold_prediction_envelope base prediction cached (demands g) hNonneg hUpper).2
      (hLaw g hg)

variable {Qid Action : Type*} [DecidableEq Qid] [DecidableEq Action]

/-- Causal checkpoint-conditioned prices inherit the fixed-panel logarithmic quality
rate when each live price stays between zero and a fixed finite envelope. -/
theorem checkpoint_conditioned_shared_root_log_bound
    (qids : Finset Qid) (root : List Action)
    (terminals : Finset (List Action)) (hTerminals : terminals.Nonempty)
    (reward : List Action → ℝ)
    (hReward : ∀ leaf ∈ terminals, 0 ≤ reward leaf ∧ reward leaf ≤ 1)
    (hAntichain : ∀ p ∈ terminals, ∀ q ∈ terminals, p <+: q → p = q)
    (base : Qid × List Action → ℝ) (hBase : ∀ r, 0 ≤ base r)
    (live : List (TreeEvaluation Action) → Qid × List Action → ℝ)
    (hLive : ∀ before r, 0 ≤ live before r)
    (hUpper : ∀ before r, live before r ≤ base r)
    (gamma c : ℝ) (hGamma : 0 ≤ gamma) (hc : 0 < c)
    (law : List (TreeEvaluation Action) → List Action → Action → List Action → ℝ)
    (hLaw : ∀ before p a, a ∈ availableChildren terminals p →
      ∀ leaf ∈ subtreeTerminals terminals (p ++ [a]), 0 ≤ law before p a leaf)
    (hMass : ∀ before p a, a ∈ availableChildren terminals p →
      ∑ leaf ∈ subtreeTerminals terminals (p ++ [a]), law before p a leaf = 1)
    (initial : PersistentCaches Qid Action)
    (hInitial : initial.restorable = initial.everMaterialized)
    (extra : List (TreeEvaluation Action) → Finset (Qid × List Action)) :
    ∃ delta : ℝ, 0 < delta ∧ ∀ events : List (TreeEvaluation Action),
      FixedTableEvents terminals reward events →
      LegalTreeRun (fun p ↦ p ∈ terminals) {[]} events →
      TreeAllocationRule terminals c (fun before p a ↦
        sharedColdPenalty qids root terminals (live before) gamma law initial extra before p a) events →
      let H := gamma * cacheWeight base (workflowResources qids root terminals)
      let cacheTime := coverageVisits terminals c H (topologyDepth terminals)
      let constants := treeRateConstants terminals c H delta cacheTime (topologyDepth terminals)
      backedDeficit (subtreeValue terminals reward []) events [] ≤
        constants.1 * Real.log (events.length + 1 : ℕ) + constants.2 := by
  -- Q9 extension 1: Reduce history-dependent live prices to domination by fixed base completion cold costs.
  apply dominated_cold_shared_root_log_bound qids root terminals hTerminals reward
    hReward hAntichain base hBase gamma c hGamma hc law hLaw hMass initial hInitial extra
  · intro before p a ha
    -- Extension 2: Nonnegative live prices, law weights, and gamma give a nonnegative actual penalty.
    obtain ⟨h0, _⟩ := referenceColdCost_bounded qids root terminals (live before)
      (hLive before) (law before p a) _ (p ++ [a])
      (hLaw before p a ha) (hMass before p a ha)
    exact mul_nonneg hGamma h0
  · intro before p a ha
    -- Extension 3: Sum the resourcewise live <= base bounds in the same cache and law, then multiply by nonnegative gamma.
    apply mul_le_mul_of_nonneg_left _ hGamma
    exact (completion_prediction_envelope
      (subtreeTerminals terminals (p ++ [a])) (law before p a) (hLaw before p a ha)
      (fun leaf ↦ panelDemand qids (root ++ leaf)) base (live before) _
      (hLive before) (hUpper before)).2

end AgentUCTPaper
end
end CompleteProofSource42

/-!
## SOURCE 43: AgentUCTPaper/ReachableDemandSeparation.lean
Original definitions, theorem statements, and complete proof bodies.
-/
section CompleteProofSource43

/-! # A separation reachable by overlapping-pair evaluations from an empty cache

Both histories use the same panel order, publish complete two-query panels,
and pay the same cold bill.
Every branch total agrees. The active pair's bills and budget-feasible action
are reversed. Thus the witness does not require arbitrary warm-cache entries.
-/

set_option autoImplicit false
noncomputable section
namespace AgentUCTPaper.ReachablePairs
open Finset

def firstPanel : Finset ℕ := {0, 1}
def secondPanel : Finset ℕ := {1, 2}
def allQueries : Finset ℕ := {0, 1, 2}
def demand (panel : Finset ℕ) (branch : Bool) : Finset (ℕ × Bool) :=
  panel ×ˢ {branch}
def leftCache := demand firstPanel false ∪ demand secondPanel true
def rightCache := demand secondPanel false ∪ demand firstPanel true
def price (_ : ℕ × Bool) : ℝ := 1

/-- The two cache states are the unions of actual complete overlapping-panel demands. -/
theorem reachable_from_empty :
    dynamicDemand [demand firstPanel false, demand secondPanel true] = leftCache ∧
    dynamicDemand [demand firstPanel true, demand secondPanel false] = rightCache := by
  simp [dynamicDemand, leftCache, rightCache, union_comm]

/-- Materializing either two-evaluation history consumes four unit-price resources. -/
theorem equal_warmup_cost :
    dynamicSpend price ∅ [demand firstPanel false, demand secondPanel true] = 4 ∧
    dynamicSpend price ∅ [demand firstPanel true, demand secondPanel false] = 4 := by
  simp [dynamicSpend, demand, firstPanel, secondPanel, coldWork, price]
  norm_cast

/-- Counts and weighted residuals per branch are identical in the two histories. -/
theorem equal_full_panel_residuals (branch : Bool) :
    coldWork price leftCache (demand allQueries branch) = 1 ∧
    coldWork price rightCache (demand allQueries branch) = 1 := by
  cases branch <;>
    norm_num [coldWork, demand, allQueries, leftCache, rightCache,
      firstPanel, secondPanel, price] <;> norm_cast

/-- At the same active panel, exact completion bills have opposite rankings. -/
theorem active_pair_ranking_reverses :
    coldWork price leftCache (demand firstPanel false) = 0 ∧
    coldWork price leftCache (demand firstPanel true) = 1 ∧
    coldWork price rightCache (demand firstPanel false) = 1 ∧
    coldWork price rightCache (demand firstPanel true) = 0 := by
  norm_num [coldWork, demand, leftCache, rightCache, firstPanel, secondPanel, price]
  norm_cast

/-- Adding one unit of common recurring work yields opposite budget-feasible choices. -/
theorem affordable_action_reverses :
    1 + coldWork price leftCache (demand firstPanel false) ≤ 1 ∧
    ¬ 1 + coldWork price leftCache (demand firstPanel true) ≤ 1 ∧
    ¬ 1 + coldWork price rightCache (demand firstPanel false) ≤ 1 ∧
    1 + coldWork price rightCache (demand firstPanel true) ≤ 1 := by
  obtain ⟨h1, h2, h3, h4⟩ := active_pair_ranking_reverses
  rw [h1, h2, h3, h4]
  norm_num

end AgentUCTPaper.ReachablePairs
end
end CompleteProofSource43

/-!
## SOURCE 44: AgentUCTPaper/FullPanelLivePrices.lean
Original definitions, theorem statements, and complete proof bodies.
-/
section CompleteProofSource44

/-! # Full-panel accounting when checkpoint observations change predicted prices

At one decision, summing residual prices over queries is exact. Across decisions,
publication and price revision are distinct updates. A fixed-price residual table
alone does not describe how a predictor derives its new prices from saved state.
-/

set_option autoImplicit false
noncomputable section

namespace AgentUCTPaper
open Finset

variable {Q P X : Type*} [DecidableEq Q] [DecidableEq P]

/-- A supplied full-panel completion law can use residual prefix sums exactly,
including query-dependent prices inferred from the current checkpoint state. -/
theorem full_panel_live_completion_quotient (weight : Q × P → ℝ)
    (cached : Finset (Q × P)) (qids : Finset Q) (outcomes : Finset X)
    (law : X → ℝ) (prefixes : X → Finset P) :
    (∑ x ∈ outcomes, law x * coldWork weight cached (qids ×ˢ prefixes x)) =
      ∑ x ∈ outcomes, law x *
        ∑ p ∈ prefixes x, ∑ q ∈ qids, if (q, p) ∈ cached then 0 else weight (q, p) := by
  apply sum_congr rfl
  intro x _
  rw [full_panel_residual_quotient]

/-- Publication zeros its prefixes; all other residual totals also receive the
sum of the new-minus-old prices over the still-uncached query resources. -/
theorem full_panel_live_price_update (old next : Q × P → ℝ)
    (cached : Finset (Q × P)) (qids : Finset Q) (published : Finset P) (p : P) :
    (∑ q ∈ qids, if (q, p) ∈ cached ∪ (qids ×ˢ published) then 0 else next (q, p)) =
      if p ∈ published then 0 else
        (∑ q ∈ qids, if (q, p) ∈ cached then 0 else old (q, p)) +
        ∑ q ∈ qids, if (q, p) ∈ cached then 0 else next (q, p) - old (q, p) := by
  rw [full_panel_residual_update]
  split_ifs
  · rfl
  · rw [← sum_add_distrib]
    apply sum_congr rfl
    intro q _
    split_ifs <;> ring

/-- Even without publication, a scalar residual can change when a predictor learns
a zero-work guard. The price update cannot be replaced by cache publication alone. -/
theorem unpublished_price_revision_changes_residual :
    (∑ q ∈ ({()} : Finset Unit),
      if (q, ()) ∈ (∅ : Finset (Unit × Unit)) then 0 else (1 : ℝ)) = 1 ∧
    (∑ q ∈ ({()} : Finset Unit),
      if (q, ()) ∈ (∅ : Finset (Unit × Unit)) then 0 else (0 : ℝ)) = 0 := by
  simp

end AgentUCTPaper
end
end CompleteProofSource44

/-!
## SOURCE 45: AgentUCTPaper/OnlineMean.lean
Original definitions, theorem statements, and complete proof bodies.
-/
section CompleteProofSource45

set_option autoImplicit false
noncomputable section
namespace AgentUCTPaper
open Finset

/-- One calibration pseudo-observation and physical observations only. -/
def onlineMean {I : Type*} (prior : ℝ) (samples : Finset I) (value : I → ℝ) : ℝ :=
  (prior + ∑ i ∈ samples, value i) / (samples.card + 1 : ℝ)

theorem onlineMean_envelope {I : Type*} (prior cap : ℝ)
    (samples : Finset I) (value : I → ℝ)
    (hp : 0 ≤ prior) (hpc : prior ≤ cap)
    (hv : ∀ i ∈ samples, 0 ≤ value i ∧ value i ≤ cap) :
    0 ≤ onlineMean prior samples value ∧ onlineMean prior samples value ≤ cap := by
  -- Q9.1: card + 1 is positive; the prior and every physical prediction sample lie in [0, cap].
  have hd : (0 : ℝ) < samples.card + 1 := by positivity
  have hs0 : 0 ≤ ∑ i ∈ samples, value i := sum_nonneg (fun i hi ↦ (hv i hi).1)
  have hsc : (∑ i ∈ samples, value i) ≤ samples.card * cap := by
    calc
      _ ≤ ∑ _i ∈ samples, cap := sum_le_sum (fun i hi ↦ (hv i hi).2)
      _ = _ := by simp
  constructor
  · exact div_nonneg (add_nonneg hp hs0) (le_of_lt hd)
  · apply (div_le_iff₀ hd).2
    nlinarith

/-- Samples retain multiplicity; their indices, not distinct outcomes, carry mass. -/
def sampledLaw {G : Type*} [DecidableEq G] (n : ℕ) (sample : Fin n → G) (g : G) : ℝ :=
  ∑ i : Fin n, if sample i = g then (1 : ℝ) / n else 0

theorem sampledLaw_nonneg {G : Type*} [DecidableEq G]
    (n : ℕ) (sample : Fin n → G) (g : G) : 0 ≤ sampledLaw n sample g := by
  apply sum_nonneg
  intro i _
  split_ifs <;> positivity

theorem sampledLaw_expectation {G : Type*} [DecidableEq G]
    (outcomes : Finset G) (n : ℕ) (sample : Fin n → G)
    (hSample : ∀ i, sample i ∈ outcomes) (bill : G → ℝ) :
    (∑ g ∈ outcomes, sampledLaw n sample g * bill g) =
      (∑ i : Fin n, bill (sample i)) / n := by
  -- Q9.2a: Expand the index-based sample law, then exchange the two finite sums.
  simp only [sampledLaw, sum_mul]
  rw [sum_comm]
  calc
    _ = ∑ i : Fin n, bill (sample i) / n := by
      apply sum_congr rfl
      intro i _
      simp only [ite_mul, zero_mul]
      rw [sum_ite_eq outcomes (sample i)]
      -- Q9.2b: Each valid sample matches exactly one completion; repeated completions keep their separate indices.
      simp [hSample i, div_eq_mul_inv, mul_comm]
    _ = _ := by rw [sum_div]

theorem sampledLaw_mass {G : Type*} [DecidableEq G]
    (outcomes : Finset G) (n : ℕ) (hn : 0 < n) (sample : Fin n → G)
    (hSample : ∀ i, sample i ∈ outcomes) :
    (∑ g ∈ outcomes, sampledLaw n sample g) = 1 := by
  -- Q9.2: Apply the expectation identity to the constant bill 1; positive sample size gives total mass 1.
  have h := sampledLaw_expectation outcomes n sample hSample (fun _ ↦ 1)
  simpa [Nat.ne_of_gt hn] using h

/-- Concrete online prices discharge the live-price premise of the shared-cache
quality theorem. The empirical law above discharges its law/mass premises;
coverage and eventual zero penalties remain the theorem's essential mechanism. -/
theorem onlineMean_completion_envelope {I R G : Type*} [DecidableEq R]
    (outcomes : Finset G) (law : G → ℝ) (hLaw : ∀ g ∈ outcomes, 0 ≤ law g)
    (demands : G → Finset R) (base prior : R → ℝ) (cached : Finset R)
    (samples : R → Finset I) (value : R → I → ℝ)
    (hPrior : ∀ r, 0 ≤ prior r ∧ prior r ≤ base r)
    (hValue : ∀ r i, i ∈ samples r → 0 ≤ value r i ∧ value r i ≤ base r) :
    0 ≤ ∑ g ∈ outcomes, law g * coldWork
      (fun r ↦ onlineMean (prior r) (samples r) (value r)) cached (demands g) ∧
    (∑ g ∈ outcomes, law g * coldWork
      (fun r ↦ onlineMean (prior r) (samples r) (value r)) cached (demands g)) ≤
      ∑ g ∈ outcomes, law g * coldWork base cached (demands g) := by
  apply completion_prediction_envelope outcomes law hLaw demands base _ cached
  · intro r
    exact (onlineMean_envelope _ _ _ _ (hPrior r).1 (hPrior r).2 (hValue r)).1
  · intro r
    exact (onlineMean_envelope _ _ _ _ (hPrior r).1 (hPrior r).2 (hValue r)).2

theorem online_mean_shared_root_log_bound
    {I Qid Action : Type*} [DecidableEq Qid] [DecidableEq Action]
    (qids : Finset Qid) (root : List Action)
    (terminals : Finset (List Action)) (hTerminals : terminals.Nonempty)
    (reward : List Action → ℝ)
    (hReward : ∀ leaf ∈ terminals, 0 ≤ reward leaf ∧ reward leaf ≤ 1)
    (hAntichain : ∀ p ∈ terminals, ∀ q ∈ terminals, p <+: q → p = q)
    (base prior : Qid × List Action → ℝ)
    (hPrior : ∀ r, 0 ≤ prior r ∧ prior r ≤ base r)
    (samples : List (TreeEvaluation Action) → Qid × List Action → Finset I)
    (value : List (TreeEvaluation Action) → Qid × List Action → I → ℝ)
    (hValue : ∀ before r i, i ∈ samples before r →
      0 ≤ value before r i ∧ value before r i ≤ base r)
    (gamma c : ℝ) (hGamma : 0 ≤ gamma) (hc : 0 < c)
    (law : List (TreeEvaluation Action) → List Action → Action → List Action → ℝ)
    (hLaw : ∀ before p a, a ∈ availableChildren terminals p →
      ∀ leaf ∈ subtreeTerminals terminals (p ++ [a]), 0 ≤ law before p a leaf)
    (hMass : ∀ before p a, a ∈ availableChildren terminals p →
      ∑ leaf ∈ subtreeTerminals terminals (p ++ [a]), law before p a leaf = 1)
    (initial : PersistentCaches Qid Action)
    (hInitial : initial.restorable = initial.everMaterialized)
    (extra : List (TreeEvaluation Action) → Finset (Qid × List Action)) :
    ∃ delta : ℝ, 0 < delta ∧ ∀ events : List (TreeEvaluation Action),
      FixedTableEvents terminals reward events →
      LegalTreeRun (fun p ↦ p ∈ terminals) {[]} events →
      TreeAllocationRule terminals c (fun before p a ↦
        sharedColdPenalty qids root terminals
          (fun r ↦ onlineMean (prior r) (samples before r) (value before r))
          gamma law initial extra before p a) events →
      let H := gamma * cacheWeight base (workflowResources qids root terminals)
      let cacheTime := coverageVisits terminals c H (topologyDepth terminals)
      let constants := treeRateConstants terminals c H delta cacheTime (topologyDepth terminals)
      backedDeficit (subtreeValue terminals reward []) events [] ≤
        constants.1 * Real.log (events.length + 1 : ℕ) + constants.2 := by
  -- Q9.3: Supply nonnegative history-dependent prices and their fixed envelope; pass the other hypotheses unchanged.
  apply checkpoint_conditioned_shared_root_log_bound qids root terminals hTerminals reward
    hReward hAntichain base (fun r ↦ le_trans (hPrior r).1 (hPrior r).2)
    (fun before r ↦ onlineMean (prior r) (samples before r) (value before r))
    _ _ gamma c hGamma hc law hLaw hMass initial hInitial extra
  · intro before r
    exact (onlineMean_envelope _ _ _ _ (hPrior r).1 (hPrior r).2 (hValue before r)).1
  · intro before r
    exact (onlineMean_envelope _ _ _ _ (hPrior r).1 (hPrior r).2 (hValue before r)).2

end AgentUCTPaper
end
end CompleteProofSource45

