import Mathlib.Analysis.Complex.ExponentialBounds
import Mathlib.Analysis.SpecialFunctions.Pow.Real



set_option autoImplicit false
noncomputable section
namespace AgentUCTRealIndex
open Finset

def logSeries (x : ℝ) (terms : ℕ) : ℝ :=
  ∑ i ∈ Finset.range terms, x^(i+1)/(i+1)

def logRemainder (x : ℝ) (terms : ℕ) : ℝ :=
  x^(terms+1)/(1-x)

theorem dyadic_log_interval (y x lower upper : ℝ) (k terms : ℕ)
    (hx0 : 0 ≤ x) (hx1 : x < 1) (hy : y = 2^k*(1-x))
    (hlo : lower ≤ (k:ℝ)*(6931471803/10000000000)-logSeries x terms-logRemainder x terms)
    (hhi : (k:ℝ)*(6931471808/10000000000)-logSeries x terms+logRemainder x terms ≤ upper) :
    lower ≤ Real.log y ∧ Real.log y ≤ upper := by
  have hs := Real.abs_log_sub_add_sum_range_le (x:=x) (by simpa [abs_of_nonneg hx0] using hx1) terms
  rw [abs_of_nonneg hx0] at hs
  have hh : -logRemainder x terms ≤ logSeries x terms + Real.log (1-x) ∧
      logSeries x terms + Real.log (1-x) ≤ logRemainder x terms := by
    exact abs_le.mp hs
  have heq : Real.log y = (k:ℝ)*Real.log 2+Real.log (1-x) := by
    rw [hy,Real.log_mul (by positivity) (by linarith : 1-x ≠ 0),Real.log_pow]
  have hk : (0:ℝ) ≤ k := Nat.cast_nonneg k
  have hl2 := mul_le_mul_of_nonneg_left Real.log_two_gt_d9.le hk
  have hu2 := mul_le_mul_of_nonneg_left Real.log_two_lt_d9.le hk
  rw [heq]
  constructor <;> linarith

theorem sqrt_rational_interval (z lower upper : ℝ) (hlo : 0 ≤ lower)
    (hhi : 0 ≤ upper) (hlower : lower^2 ≤ z) (hupper : z ≤ upper^2) :
    lower ≤ Real.sqrt z ∧ Real.sqrt z ≤ upper := by
  constructor
  · exact (Real.le_sqrt hlo ((sq_nonneg lower).trans hlower)).mpr hlower
  · exact (Real.sqrt_le_iff).mpr ⟨hhi,hupper⟩

theorem uct_bonus_interval (c logLower logUpper sqrtLower sqrtUpper : ℝ)
    (parentCount childCount : ℕ) (hc : 0 ≤ c) (hchild : 0 < childCount)
    (hlog : logLower ≤ Real.log (parentCount+1:ℕ) ∧ Real.log (parentCount+1:ℕ) ≤ logUpper)
    (hl0 : 0 ≤ sqrtLower) (hu0 : 0 ≤ sqrtUpper)
    (hl : sqrtLower^2*(childCount:ℝ) ≤ logLower)
    (hu : logUpper ≤ sqrtUpper^2*(childCount:ℝ)) :
    c*sqrtLower ≤ c*Real.sqrt (Real.log (parentCount+1:ℕ)/(childCount:ℝ)) ∧
      c*Real.sqrt (Real.log (parentCount+1:ℕ)/(childCount:ℝ)) ≤ c*sqrtUpper := by
  have hd : (0:ℝ) < childCount := Nat.cast_pos.mpr hchild
  have hs := sqrt_rational_interval (Real.log (parentCount+1:ℕ)/(childCount:ℝ)) sqrtLower sqrtUpper
    hl0 hu0 ((le_div_iff₀ hd).mpr (hl.trans hlog.1)) ((div_le_iff₀ hd).mpr (hlog.2.trans hu))
  exact ⟨mul_le_mul_of_nonneg_left hs.1 hc,mul_le_mul_of_nonneg_left hs.2 hc⟩

theorem index_strict_order_from_intervals (qa qb ca cb bonusLower bonusUpper : ℝ)
    (bonusA bonusB : ℝ) (ha : bonusLower ≤ bonusA) (hb : bonusB ≤ bonusUpper)
    (hmargin : qb+bonusUpper-cb < qa+bonusLower-ca) :
    qb+bonusB-cb < qa+bonusA-ca := by linarith

end AgentUCTRealIndex
