import AgentUCTPaper.TreeDecisionValue
import AgentUCTPaper.TreeSharedCache

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
  -- Q9扩展1：把任意历史live价格的实际罚项，接到固定base完成冷费用的支配定理。
  apply dominated_cold_shared_root_log_bound qids root terminals hTerminals reward
    hReward hAntichain base hBase gamma c hGamma hc law hLaw hMass initial hInitial extra
  · intro before p a ha
    -- 扩展2：live≥0、law≥0、gamma≥0，使实际罚项非负。
    obtain ⟨h0, _⟩ := referenceColdCost_bounded qids root terminals (live before)
      (hLive before) (law before p a) _ (p ++ [a])
      (hLaw before p a ha) (hMass before p a ha)
    exact mul_nonneg hGamma h0
  · intro before p a ha
    -- 扩展3：live≤base逐资源成立；同一cache/law下求和并乘gamma保留上界。
    apply mul_le_mul_of_nonneg_left _ hGamma
    exact (completion_prediction_envelope
      (subtreeTerminals terminals (p ++ [a])) (law before p a) (hLaw before p a ha)
      (fun leaf ↦ panelDemand qids (root ++ leaf)) base (live before) _
      (hLive before) (hUpper before)).2

end AgentUCTPaper
