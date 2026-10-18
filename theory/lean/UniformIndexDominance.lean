import UniformBonusBound
import OrderedIndexCertificate

set_option autoImplicit false
noncomputable section
namespace AgentUCTRealIndex
open AgentUCTPaper

theorem tree_index_upper5 (q penalty : ℝ) (parent child : ℕ)
    (hq : q ≤ 1) (hp : parent ≤ 256) (hn : 1 ≤ child) :
    treeIndex q (7/5) penalty parent child ≤ 5-penalty := by
  have hb := (bonus_7_5_bound4 parent child hp hn).2
  unfold treeIndex
  linarith

theorem tree_index_lower_minus_penalty (q penalty : ℝ) (parent child : ℕ)
    (hq : 0 ≤ q) : -penalty ≤ treeIndex q (7/5) penalty parent child := by
  have hb := treeBonus_nonnegative (by norm_num : (0:ℝ) ≤ 7/5) parent child
  unfold treeIndex
  linarith

theorem uniform_strict_dominance_from_penalty_gap (qa qb ca cb : ℝ)
    (parent na nb : ℕ) (hqa : 0 ≤ qa) (hqb : qb ≤ 1)
    (hp : parent ≤ 256) (hnb : 1 ≤ nb) (hgap : ca+5 < cb) :
    treeIndex qb (7/5) cb parent nb < treeIndex qa (7/5) ca parent na := by
  have hupper := tree_index_upper5 qb cb parent nb hqb hp hnb
  have hlower := tree_index_lower_minus_penalty qa ca parent na hqa
  linarith

theorem uniform_weak_dominance_from_penalty_gap (qa qb ca cb : ℝ)
    (parent na nb : ℕ) (hqa : 0 ≤ qa) (hqb : qb ≤ 1)
    (hp : parent ≤ 256) (hnb : 1 ≤ nb) (hgap : ca+5 ≤ cb) :
    treeIndex qb (7/5) cb parent nb ≤ treeIndex qa (7/5) ca parent na := by
  have hupper := tree_index_upper5 qb cb parent nb hqb hp hnb
  have hlower := tree_index_lower_minus_penalty qa ca parent na hqa
  linarith

end AgentUCTRealIndex
