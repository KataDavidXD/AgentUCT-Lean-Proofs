import AgentUCTPaper.Regret
import AgentUCTPaper.Counterexample

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
