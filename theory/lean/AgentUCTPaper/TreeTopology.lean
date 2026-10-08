import AgentUCTPaper.TreeHistory
import AgentUCTPaper.TreeCacheVisit
import AgentUCTPaper.FiniteModel
import Mathlib.Data.Finset.Option

/-! # Finite workflow topology, legal local arms, and descendant maxima -/

set_option autoImplicit false

noncomputable section

namespace AgentUCTPaper

open Finset

variable {Action : Type*} [DecidableEq Action]

def workflowNodes (terminals : Finset (List Action)) : Finset (List Action) :=
  terminals.biUnion (fun leaf ↦ insert [] (executionPrefixes leaf))

def availableChildren (terminals : Finset (List Action)) (p : List Action) : Finset Action :=
  terminals.biUnion (fun leaf ↦ (childAfter p leaf).toFinset)

abbrev ChildArm (terminals : Finset (List Action)) (p : List Action) :=
  ↥(availableChildren terminals p)

theorem workflowNodes_mem (terminals : Finset (List Action)) (p : List Action) :
    p ∈ workflowNodes terminals ↔ ∃ leaf ∈ terminals, p <+: leaf := by
  simp only [workflowNodes, mem_biUnion, mem_insert, executionPrefixes_mem_iff]
  constructor
  · rintro ⟨leaf, hl, hp | hp⟩
    · subst p
      exact ⟨leaf, hl, List.nil_prefix⟩
    · exact ⟨leaf, hl, hp.2⟩
  · rintro ⟨leaf, hl, hp⟩
    refine ⟨leaf, hl, ?_⟩
    by_cases h : p = []
    · exact Or.inl h
    · exact Or.inr ⟨h, hp⟩

theorem availableChildren_mem (terminals : Finset (List Action)) (p : List Action) (a : Action) :
    a ∈ availableChildren terminals p ↔ ∃ leaf ∈ terminals, p ++ [a] <+: leaf := by
  simp [availableChildren, Option.mem_def, childAfter_some_iff]

theorem legal_child_is_node (terminals : Finset (List Action)) (p : List Action) (a : Action)
    (ha : a ∈ availableChildren terminals p) : p ++ [a] ∈ workflowNodes terminals := by
  rw [workflowNodes_mem]
  exact (availableChildren_mem terminals p a).mp ha

theorem legal_child_has_terminals (terminals : Finset (List Action)) (p : List Action) (a : Action)
    (ha : a ∈ availableChildren terminals p) : (subtreeTerminals terminals (p ++ [a])).Nonempty := by
  obtain ⟨leaf, hl, hp⟩ := (availableChildren_mem terminals p a).mp ha
  exact ⟨leaf, mem_filter.mpr ⟨hl, hp⟩⟩

theorem internal_has_child (terminals : Finset (List Action)) (p : List Action)
    (hNode : p ∈ workflowNodes terminals) (hInternal : p ∉ terminals) :
    (availableChildren terminals p).Nonempty := by
  obtain ⟨leaf, hl, hp⟩ := (workflowNodes_mem terminals p).mp hNode
  rcases prefix_eq_or_childAfter p leaf hp with he | ⟨a, ha⟩
  · exact (hInternal (he ▸ hl)).elim
  · exact ⟨a, (availableChildren_mem terminals p a).mpr
      ⟨leaf, hl, (childAfter_some_iff p leaf a).mp ha⟩⟩

theorem terminal_has_no_child (terminals : Finset (List Action))
    (hAntichain : ∀ p ∈ terminals, ∀ q ∈ terminals, p <+: q → p = q)
    (p : List Action) (hp : p ∈ terminals) : availableChildren terminals p = ∅ := by
  apply Finset.eq_empty_iff_forall_notMem.mpr
  intro a ha
  obtain ⟨leaf, hl, hpre⟩ := (availableChildren_mem terminals p a).mp ha
  have he := hAntichain p hp leaf hl ((List.prefix_append p [a]).trans hpre)
  have hlen := hpre.length_le
  simp [← he] at hlen

theorem subtreeValue_bounded (terminals : Finset (List Action)) (reward : List Action → ℝ)
    (hReward : ∀ leaf ∈ terminals, 0 ≤ reward leaf ∧ reward leaf ≤ 1) (p : List Action) :
    0 ≤ subtreeValue terminals reward p ∧ subtreeValue terminals reward p ≤ 1 := by
  by_cases h : (subtreeTerminals terminals p).Nonempty
  · obtain ⟨leaf, hl, _, he⟩ := subtreeValue_attained terminals reward p h
    rw [he]
    exact hReward leaf hl
  · simp [subtreeValue, h]

theorem subtreeValue_child_le (terminals : Finset (List Action)) (reward : List Action → ℝ)
    (p : List Action) (a : Action) (ha : a ∈ availableChildren terminals p) :
    subtreeValue terminals reward (p ++ [a]) ≤ subtreeValue terminals reward p := by
  obtain ⟨leaf, hl, hp, he⟩ := subtreeValue_attained terminals reward (p ++ [a])
    (legal_child_has_terminals terminals p a ha)
  rw [he]
  exact subtreeValue_upper terminals reward p leaf hl ((List.prefix_append p [a]).trans hp)

theorem internal_has_optimal_child (terminals : Finset (List Action)) (reward : List Action → ℝ)
    (p : List Action) (hNode : p ∈ workflowNodes terminals) (hInternal : p ∉ terminals) :
    ∃ a ∈ availableChildren terminals p,
      subtreeValue terminals reward (p ++ [a]) = subtreeValue terminals reward p := by
  obtain ⟨someLeaf, hs, hp⟩ := (workflowNodes_mem terminals p).mp hNode
  have hn : (subtreeTerminals terminals p).Nonempty := ⟨someLeaf, mem_filter.mpr ⟨hs, hp⟩⟩
  obtain ⟨leaf, hl, hp, he⟩ := subtreeValue_attained terminals reward p hn
  rcases prefix_eq_or_childAfter p leaf hp with hEq | ⟨a, ha⟩
  · exact (hInternal (hEq ▸ hl)).elim
  · have hpre := (childAfter_some_iff p leaf a).mp ha
    have hLegal := (availableChildren_mem terminals p a).mpr ⟨leaf, hl, hpre⟩
    refine ⟨a, hLegal, le_antisymm (subtreeValue_child_le terminals reward p a hLegal) ?_⟩
    rw [he]
    exact subtreeValue_upper terminals reward (p ++ [a]) leaf hl hpre

def edgeGap (terminals : Finset (List Action)) (reward : List Action → ℝ)
    (p : List Action) (a : Action) : ℝ :=
  subtreeValue terminals reward p - subtreeValue terminals reward (p ++ [a])

theorem edgeGap_nonnegative (terminals : Finset (List Action)) (reward : List Action → ℝ)
    (p : List Action) (a : Action) (ha : a ∈ availableChildren terminals p) :
    0 ≤ edgeGap terminals reward p a :=
  sub_nonneg.mpr (subtreeValue_child_le terminals reward p a ha)

theorem edgeGap_le_one (terminals : Finset (List Action)) (reward : List Action → ℝ)
    (hReward : ∀ leaf ∈ terminals, 0 ≤ reward leaf ∧ reward leaf ≤ 1)
    (p : List Action) (a : Action) : edgeGap terminals reward p a ≤ 1 := by
  have hp := subtreeValue_bounded terminals reward hReward p
  have hc := subtreeValue_bounded terminals reward hReward (p ++ [a])
  unfold edgeGap
  linarith

theorem finite_tree_positive_edge_gap (terminals : Finset (List Action))
    (reward : List Action → ℝ) :
    ∃ delta : ℝ, 0 < delta ∧ ∀ p ∈ workflowNodes terminals, ∀ a ∈ availableChildren terminals p,
      0 < edgeGap terminals reward p a → delta ≤ edgeGap terminals reward p a := by
  classical
  let gaps := (workflowNodes terminals).biUnion
    (fun p ↦ (availableChildren terminals p).image (edgeGap terminals reward p))
  obtain ⟨delta, hd, hBound⟩ := finite_positive_gap gaps
  refine ⟨delta, hd, ?_⟩
  intro p hp a ha hpos
  exact hBound _ (mem_biUnion.mpr ⟨p, hp, mem_image.mpr ⟨a, ha, rfl⟩⟩) hpos

def topologyDepth (terminals : Finset (List Action)) : ℕ := terminals.sup List.length

theorem node_length_le_depth (terminals : Finset (List Action)) (p : List Action)
    (hp : p ∈ workflowNodes terminals) : p.length ≤ topologyDepth terminals := by
  obtain ⟨leaf, hl, hpre⟩ := (workflowNodes_mem terminals p).mp hp
  exact hpre.length_le.trans (Finset.le_sup hl)

theorem child_remaining_depth_lt (terminals : Finset (List Action)) (p : List Action) (a : Action)
    (ha : a ∈ availableChildren terminals p) :
    topologyDepth terminals - (p ++ [a]).length < topologyDepth terminals - p.length := by
  have h := node_length_le_depth terminals (p ++ [a]) (legal_child_is_node terminals p a ha)
  simp only [List.length_append, List.length_singleton] at h ⊢
  omega

theorem projected_action_is_legal (terminals : Finset (List Action))
    (events : List (TreeEvaluation Action))
    (hTerminal : ∀ event ∈ events, event.terminal ∈ terminals) (p : List Action)
    (a : Action) (ha : a ∈ localActions events p) : a ∈ availableChildren terminals p := by
  obtain ⟨event, he, hAction⟩ := List.mem_filterMap.mp ha
  have hp := (childAfter_some_iff p event.expanded a).mp hAction
  exact (availableChildren_mem terminals p a).mpr
    ⟨event.terminal, hTerminal event he, hp.trans event.expanded_is_prefix⟩

theorem childArm_card (terminals : Finset (List Action)) (p : List Action) :
    Fintype.card (ChildArm terminals p) = (availableChildren terminals p).card := by
  simp [ChildArm]

end AgentUCTPaper
