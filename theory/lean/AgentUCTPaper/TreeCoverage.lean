import AgentUCTPaper.TreeExploration

/-! # Explicit recursive coverage and cache saturation of the actual run -/

set_option autoImplicit false

noncomputable section

namespace AgentUCTPaper

open Finset

variable {Action : Type*} [DecidableEq Action]

def coverageVisits (terminals : Finset (List Action)) (c H : ℝ) : ℕ → ℕ
  | 0 => 1
  | depth + 1 => 1 + (workflowNodes terminals).sup (fun p ↦
      2 * explorationWindowStart c H (Fintype.card (ChildArm terminals p))
        (coverageVisits terminals c H depth))

theorem coverageVisits_positive (terminals : Finset (List Action)) (c H : ℝ) (depth : ℕ) :
    0 < coverageVisits terminals c H depth := by
  cases depth <;> simp only [coverageVisits] <;> omega

theorem actual_subtree_coverage (terminals : Finset (List Action)) (c H : ℝ)
    (penalty : List (TreeEvaluation Action) → List Action → Action → ℝ)
    (events : List (TreeEvaluation Action)) (run : BoundedTreeRun terminals c H penalty events)
    (hc : 0 < c) (hH : 0 ≤ H)
    (hAntichain : ∀ p ∈ terminals, ∀ q ∈ terminals, p <+: q → p = q)
    (depth : ℕ) (p : List Action) (hNode : p ∈ workflowNodes terminals)
    (hDepth : topologyDepth terminals - p.length ≤ depth)
    (hCount : coverageVisits terminals c H depth ≤ backedCount events p) :
    ∀ leaf ∈ terminals, p <+: leaf → 0 < backedCount events leaf := by
  induction depth generalizing p with
  -- Q3.1：按剩余深度归纳；终局反链使基础步只可能观察该终局本身。
  | zero =>
    intro leaf hl hp
    have hlen := node_length_le_depth terminals leaf
      ((workflowNodes_mem terminals leaf).mpr ⟨leaf, hl, List.prefix_refl _⟩)
    have he : p = leaf := hp.eq_of_length_le (by omega)
    subst leaf
    exact (coverageVisits_positive terminals c H 0).trans_le hCount
  | succ depth ih =>
    intro leaf hl hp
    by_cases hTerminal : p ∈ terminals
    · have he := hAntichain p hTerminal leaf hl hp
      subst leaf
      exact (coverageVisits_positive terminals c H (depth + 1)).trans_le hCount
    · rcases prefix_eq_or_childAfter p leaf hp with he | ⟨a, ha⟩
      · exact (hTerminal (he ▸ hl)).elim
      · have hChildPath := (childAfter_some_iff p leaf a).mp ha
        have hChild := (availableChildren_mem terminals p a).mpr ⟨leaf, hl, hChildPath⟩
        have hWindow : 2 * explorationWindowStart c H (Fintype.card (ChildArm terminals p))
            (coverageVisits terminals c H depth) ≤
            (workflowNodes terminals).sup (fun q ↦
              2 * explorationWindowStart c H (Fintype.card (ChildArm terminals q))
                (coverageVisits terminals c H depth)) :=
          Finset.le_sup (f := fun q ↦
            2 * explorationWindowStart c H (Fintype.card (ChildArm terminals q))
              (coverageVisits terminals c H depth)) hNode
        have hBirth := nonterminal_birth_count (fun p ↦ p ∈ terminals) events {[]} p
          hTerminal run.legal
        -- Q3.2：父回传含至多一个birth，减去它仍足够容纳完整探索窗口。
        have hDecomp := parent_count_decomposition events p
        have hEnough : 2 * explorationWindowStart c H (Fintype.card (ChildArm terminals p))
            (coverageVisits terminals c H depth) ≤ (localActions events p).length := by
          simp only [coverageVisits] at hCount
          split_ifs at hBirth <;> omega
        have hChildN := actual_children_explored terminals c H penalty events run hc hH p
          hTerminal (coverageVisits terminals c H depth) hEnough a hChild
        have hChildDepth := child_remaining_depth_lt terminals p a hChild
        -- Q3.3：每child访问超过递归覆盖阈值，剩余深度降低后应用归纳。
        exact ih (p ++ [a]) (legal_child_is_node terminals p a hChild) (by omega)
          hChildN.le leaf hl hChildPath

theorem root_count_eq_length (events : List (TreeEvaluation Action)) :
    backedCount events [] = events.length := by simp [backedCount]

theorem actual_terminal_coverage (terminals : Finset (List Action)) (c H : ℝ)
    (penalty : List (TreeEvaluation Action) → List Action → Action → ℝ)
    (events : List (TreeEvaluation Action)) (run : BoundedTreeRun terminals c H penalty events)
    (hc : 0 < c) (hH : 0 ≤ H)
    (hAntichain : ∀ p ∈ terminals, ∀ q ∈ terminals, p <+: q → p = q)
    (hCount : coverageVisits terminals c H (topologyDepth terminals) ≤ events.length) :
    ∀ leaf ∈ terminals, 0 < backedCount events leaf := by
  intro leaf hl
  apply actual_subtree_coverage terminals c H penalty events run hc hH hAntichain
    (topologyDepth terminals) []
    ((workflowNodes_mem terminals []).mpr ⟨leaf, hl, List.nil_prefix⟩)
    (by simp) (by simpa [root_count_eq_length] using hCount) leaf hl List.nil_prefix

theorem visited_terminal_observed (terminals : Finset (List Action))
    (events : List (TreeEvaluation Action))
    (hTerminal : ∀ event ∈ events, event.terminal ∈ terminals)
    (hAntichain : ∀ p ∈ terminals, ∀ q ∈ terminals, p <+: q → p = q)
    (leaf : List Action) (hl : leaf ∈ terminals) (hCount : 0 < backedCount events leaf) :
    ∃ event ∈ events, event.terminal = leaf := by
  obtain ⟨event, he, hp⟩ := exists_backed_event_of_count_pos events leaf hCount
  exact ⟨event, he, (hAntichain leaf hl event.terminal (hTerminal event he)
    (hp.trans event.expanded_is_prefix)).symm⟩

variable {Qid : Type*} [DecidableEq Qid]

def workflowResources (qids : Finset Qid) (root : List Action)
    (terminals : Finset (List Action)) : Finset (Qid × List Action) :=
  terminals.biUnion (fun leaf ↦ panelDemand qids (root ++ leaf))

theorem actual_cache_coverage (qids : Finset Qid) (root : List Action)
    (terminals : Finset (List Action)) (c H : ℝ)
    (penalty : List (TreeEvaluation Action) → List Action → Action → ℝ)
    (physicalWeight : Qid × List Action → ℝ) (overhead : TreeEvaluation Action → ℝ)
    (events : List (TreeEvaluation Action)) (initial : MeteredTreeState Qid Action)
    (run : BoundedTreeRun terminals c H penalty events) (hc : 0 < c) (hH : 0 ≤ H)
    (hAntichain : ∀ p ∈ terminals, ∀ q ∈ terminals, p <+: q → p = q)
    (hCount : coverageVisits terminals c H (topologyDepth terminals) ≤ events.length) :
    workflowResources qids root terminals ⊆
      (replayMetered qids (fun x ↦ root ++ x) physicalWeight overhead events initial).materialized := by
  intro resource hr
  obtain ⟨leaf, hl, hd⟩ := mem_biUnion.mp hr
  exact visited_prefix_demand_cached qids root physicalWeight overhead events initial leaf
    (actual_terminal_coverage terminals c H penalty events run hc hH hAntichain hCount leaf hl) hd

theorem actual_restorable_coverage (qids : Finset Qid) (root : List Action)
    (terminals : Finset (List Action)) (c H : ℝ)
    (penalty : List (TreeEvaluation Action) → List Action → Action → ℝ)
    (physicalWeight : Qid × List Action → ℝ) (overhead : TreeEvaluation Action → ℝ)
    (events : List (TreeEvaluation Action)) (initial : MeteredTreeState Qid Action)
    (caches : PersistentCaches Qid Action)
    (hCache : caches.restorable = caches.everMaterialized)
    (hLedger : caches.everMaterialized = initial.materialized)
    (run : BoundedTreeRun terminals c H penalty events) (hc : 0 < c) (hH : 0 ≤ H)
    (hAntichain : ∀ p ∈ terminals, ∀ q ∈ terminals, p <+: q → p = q)
    (hCount : coverageVisits terminals c H (topologyDepth terminals) ≤ events.length) :
    workflowResources qids root terminals ⊆
      (replayPublished qids (fun x ↦ root ++ x) events caches).restorable := by
  -- Q4.1：持久缓存与已发布ledger一致，把已物化覆盖转为真正可恢复覆盖。
  rw [replayPublished_cache_matches_metered qids (fun x ↦ root ++ x) physicalWeight overhead
    events caches initial hCache hLedger]
  exact actual_cache_coverage qids root terminals c H penalty physicalWeight overhead events
    initial run hc hH hAntichain hCount

end AgentUCTPaper
