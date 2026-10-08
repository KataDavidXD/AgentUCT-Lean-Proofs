import AgentUCTPaper.TreeRate

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
