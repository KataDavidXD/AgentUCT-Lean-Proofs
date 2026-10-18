import OrderedIndexCertificate
import AgentUCTPaper.TreeAllocation

set_option autoImplicit false
noncomputable section
namespace AgentUCTRealIndex
open AgentUCTPaper

theorem same_visits_index_strict_iff (qa qb c ca cb : ℝ) (parent child : ℕ) :
    treeIndex qb c cb parent child < treeIndex qa c ca parent child ↔ qb-cb < qa-ca := by
  unfold treeIndex
  constructor <;> intro h <;> linarith

theorem same_visits_index_weak_iff (qa qb c ca cb : ℝ) (parent child : ℕ) :
    treeIndex qb c cb parent child ≤ treeIndex qa c ca parent child ↔ qb-cb ≤ qa-ca := by
  unfold treeIndex
  constructor <;> intro h <;> linarith

theorem same_visits_index_equal_iff (qa qb c ca cb : ℝ) (parent child : ℕ) :
    treeIndex qb c cb parent child = treeIndex qa c ca parent child ↔ qb-cb = qa-ca := by
  unfold treeIndex
  constructor <;> intro h <;> linarith

theorem same_mean_penalty_fewer_visits_strict (q c penalty : ℝ)
    (parent na nb : ℕ) (hparent : 0 < parent) (hc : 0 < c) (ha : 0 < na) (hab : na < nb) :
    treeIndex q c penalty parent nb < treeIndex q c penalty parent na := by
  have hp : (1:ℝ) < (parent+1:ℕ) := by exact_mod_cast (by omega : 1 < parent+1)
  have hlog : 0 < Real.log (parent+1:ℕ) := Real.log_pos hp
  have han : (0:ℝ) < na := Nat.cast_pos.mpr ha
  have hbn : (na:ℝ) < nb := by exact_mod_cast hab
  have hdiv : Real.log (parent+1:ℕ)/(nb:ℝ) < Real.log (parent+1:ℕ)/(na:ℝ) := by
    exact div_lt_div_of_pos_left hlog han hbn
  have hs : Real.sqrt (Real.log (parent+1:ℕ)/(nb:ℝ)) < Real.sqrt (Real.log (parent+1:ℕ)/(na:ℝ)) :=
    Real.sqrt_lt_sqrt (by positivity) hdiv
  have hm := mul_lt_mul_of_pos_left hs hc
  unfold treeIndex treeBonus
  linarith

end AgentUCTRealIndex
