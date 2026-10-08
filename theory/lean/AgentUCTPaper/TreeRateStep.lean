import AgentUCTPaper.TreeForecast
import AgentUCTPaper.TreeDecomposition
import AgentUCTPaper.TreeRateAlgebra

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
  -- Q6.1：局部动作流保留实际child选择；burnin同时覆盖cache与均值偏差阶段。
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
      -- Q5：有限探索窗口已使每个孩子超过偏差阈值；局部计数等于回传计数。
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
      -- 最优child的D/N≤delta/4，真实均值恒等式给出Q≥V(parent)-delta/4。
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
      -- Q6.2：使用真实index最大性；覆盖后双方冷罚项均为0。
      rw [hSelected, hZero before hp hCacheTime best hBest,
        hZero before hp hCacheTime a ha] at hMax
      have hCapLocal := selected_count_from_subtree_bias hc.le hDelta (hInit a ha)
        hBestQ hChosenQ hGap hMax
      -- Q6.3：bonus平方恒等式给当前次数界；最终父log支配所有早期历史。
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
  -- Q6.4：转回全局真实计数；早期burnin和末次增量+1已经由计数引理保留。
  rwa [hCount] at hBound

end AgentUCTPaper
