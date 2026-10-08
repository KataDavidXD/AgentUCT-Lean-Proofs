import AgentUCTPaper.TreeRateStep

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
  -- Q7.1：用最终父计数固定log项与次优child次数上界。
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
    -- Q7.2：孩子计数≤父计数，因此孩子归纳log界可由同一父log支配。
    have hN : backedCount events (p ++ [a]) ≤ backedCount events p :=
      backedCount_path_mono events p (p ++ [a]) (List.prefix_append _ _)
    have hLog : Real.log (backedCount events (p ++ [a]) + 1 : ℕ) ≤ L :=
      Real.log_le_log (by positivity) (by exact_mod_cast Nat.add_le_add_right hN 1)
    have hChild := (hChildren events (List.prefix_refl _) a ha).trans
      (add_le_add_right (mul_le_mul_of_nonneg_left hLog hA) B)
    have hEdge : (backedCount events (p ++ [a]) : ℝ) * edgeGap terminals reward p a ≤
        burnin + cap + 1 := by
      by_cases hPos : 0 < edgeGap terminals reward p a
      -- Q7.3：正gap用Q6次数界和gap≤1；零gap的N*gap严格为零。
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
  -- Q7.4：真实父亏损分解保留birth≤1，对有限child求和并整理系数。
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
  -- Q7.5：同时量化任意历史和节点，归纳才能用于选择前的每个历史前缀。
  | zero =>
    -- 基础步：剩余深度0迫使p为终局；反链+固定奖励使其亏损为0。
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
      -- 归纳步：所有合法child剩余深度降低，run/table/零罚项传给历史前缀。
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
        -- 用全树最大分支数统一递推常数，保持与具体历史和T无关。
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
  -- Q8.1：先固定实例级delta，再量化所有events；不能随历史或T回选gap。
  obtain ⟨delta, hDelta, hGaps⟩ := finite_tree_positive_edge_gap terminals reward
  refine ⟨delta, hDelta, ?_⟩
  intro events hTable hLegal hRule
  let H := gamma * cacheWeight prediction (workflowResources qids root terminals)
  let penalty := coldForecastPenalty qids root terminals prediction gamma law initial
  let cacheTime := coverageVisits terminals c H (topologyDepth terminals)
  have hH : 0 ≤ H := mul_nonneg hGamma (sum_nonneg (fun r _ ↦ hPrediction r))
  have run : BoundedTreeRun terminals c H penalty events := {
    -- Q1：固定表、合法执行、实际选择规则和统一罚项包络组成有界运行。
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
    -- Q3/Q4：由成功持久发布的覆盖得到零罚项，而非仅假设罚项有界。
    exact coldForecastPenalty_after_coverage qids root terminals prediction gamma c H law initial
      hInitial before (run.prefix hp) hc hH hAntichain ht p a
  obtain ⟨leaf, hl⟩ := hTerminals
  have hRoot : [] ∈ workflowNodes terminals :=
    (workflowNodes_mem terminals []).mpr ⟨leaf, hl, List.nil_prefix⟩
  have hResult := actual_subtree_log_deficit terminals reward c H delta cacheTime penalty
    hReward hc hH hDelta hAntichain hGaps (topologyDepth terminals) events run hTable hZero
    [] hRoot (by simp)
  -- Q8.2：根每个完整event回传一次，根计数=T，根亏损就是训练质量regret。
  simpa only [root_count_eq_length] using hResult

end AgentUCTPaper
