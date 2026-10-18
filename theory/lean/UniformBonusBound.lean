import ExtendedLogBounds
import AgentUCTPaper.TreeAllocation

set_option autoImplicit false
noncomputable section
namespace AgentUCTRealIndex
open AgentUCTPaper

theorem log_nat_upto257_lt6 (n : ℕ) (hn : 1 ≤ n) (hu : n ≤ 257) : Real.log (n:ℝ) < 6 := by
  have hmon : Real.log (n:ℝ) ≤ Real.log 257 :=
    Real.log_le_log (by exact_mod_cast hn) (by exact_mod_cast hu)
  have hb := log_257_interval.2
  linarith

theorem bonus_7_5_bound4 (parent child : ℕ) (hparent : parent ≤ 256) (hchild : 1 ≤ child) :
    0 ≤ treeBonus (7/5) parent child ∧ treeBonus (7/5) parent child ≤ 4 := by
  have hn : (0:ℝ) < child := by exact_mod_cast (by omega : 0 < child)
  have hn1 : (1:ℝ) ≤ child := by exact_mod_cast hchild
  have hlog := log_nat_upto257_lt6 (parent+1) (by omega) (by omega)
  have hz : Real.log (parent+1:ℕ)/(child:ℝ) ≤ 6 := by
    apply (div_le_iff₀ hn).mpr
    nlinarith
  have hs : Real.sqrt (Real.log (parent+1:ℕ)/(child:ℝ)) ≤ (20/7:ℝ) := by
    apply Real.sqrt_le_iff.mpr
    constructor
    · norm_num
    · nlinarith
  constructor
  · exact treeBonus_nonnegative (by norm_num) _ _
  · unfold treeBonus
    have hm := mul_le_mul_of_nonneg_left hs (by norm_num : (0:ℝ) ≤ 7/5)
    calc
      _ ≤ (7/5:ℝ)*(20/7) := hm
      _ = 4 := by norm_num

end AgentUCTRealIndex
