import AgentUCTPaper.TreeFiniteBudget

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
  -- L1：普通最大性给非负指数损失；U含bonus，尚不是真实质量。
  have hLossNonneg : 0 ≤ ub - ua := sub_nonneg.mpr hUCT
  -- L2：定价最大性移项，损失不超过gamma倍预测费用节省。
  have hLossUpper : ub - ua ≤ gamma * (cb - ca) := by nlinarith
  -- L3：gamma>0；若ca>cb，右侧负，与L1、L2矛盾。
  have hCheaper : ca ≤ cb := by
    by_contra h
    have hCostOrder : cb < ca := lt_of_not_ge h
    nlinarith
  -- L4：合并已经命名的三个结论。
  exact ⟨hCheaper, hLossNonneg, hLossUpper⟩

/-- A predicted saving exceeding both cost errors certifies a physical mean-bill saving. -/
theorem physical_saving_certificate (ca cb ea eb ra rb : ℝ)
    (ha : |ea - ca| ≤ ra) (hb : |eb - cb| ≤ rb) :
    eb - ea - (ra + rb) ≤ cb - ca := by
  -- L5：拆两候选abs误差，实际费用节省下界减去两误差半径之和。
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
  -- L6：质量误差也须控制；费用误差按非负gamma加权后一起移项。
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
