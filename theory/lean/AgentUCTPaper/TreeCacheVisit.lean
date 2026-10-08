import AgentUCTPaper.TreeCheckpoint

/-! # Why next-edge cost vanishes at visited children

This derives the degeneracy from the actual shared event history, instead of assuming
zero penalties. Complete descendant evaluation can still require uncached resources.
-/

set_option autoImplicit false

noncomputable section

namespace AgentUCTPaper

open Finset

variable {Qid Action : Type*} [DecidableEq Qid] [DecidableEq Action]

omit [DecidableEq Qid] in
theorem executionPrefixes_mem_iff (path p : List Action) :
    p ∈ executionPrefixes path ↔ p ≠ [] ∧ p <+: path := by
  constructor
  · intro hp
    obtain ⟨i, hi, rfl⟩ := mem_image.mp hp
    obtain ⟨hi1, hiLen⟩ := mem_Icc.mp hi
    refine ⟨?_, List.take_prefix i path⟩
    intro hNil
    have hlen := congrArg List.length hNil
    simp only [List.length_take, Nat.min_eq_left hiLen, List.length_nil] at hlen
    omega
  · rintro ⟨hne, hp⟩
    have hpos := List.length_pos_iff.mpr hne
    exact mem_image.mpr ⟨p.length, mem_Icc.mpr ⟨hpos, hp.length_le⟩,
      (List.prefix_iff_eq_take.mp hp).symm⟩

omit [DecidableEq Qid] in
theorem panelDemand_prefix_mono (qids : Finset Qid) (short long : List Action)
    (hPath : short <+: long) : panelDemand qids short ⊆ panelDemand qids long := by
  intro ⟨q, p⟩ hp
  obtain ⟨hq, hp⟩ := (panelDemand_mem qids short p q).mp hp
  obtain ⟨hne, hpre⟩ := (executionPrefixes_mem_iff short p).mp hp
  exact (panelDemand_mem qids long p q).mpr
    ⟨hq, (executionPrefixes_mem_iff long p).mpr ⟨hne, hpre.trans hPath⟩⟩

theorem replayMetered_initial_cache_subset (qids : Finset Qid)
    (executionPath : List Action → List Action) (weight : Qid × List Action → ℝ)
    (overhead : TreeEvaluation Action → ℝ) (events : List (TreeEvaluation Action))
    (initial : MeteredTreeState Qid Action) :
    initial.materialized ⊆
      (replayMetered qids executionPath weight overhead events initial).materialized := by
  induction events generalizing initial with
  | nil => exact subset_rfl
  | cons event events ih =>
    exact (subset_union_left : initial.materialized ⊆
      (meterStep qids executionPath weight overhead initial event).materialized).trans
        (ih (meterStep qids executionPath weight overhead initial event))

theorem replayMetered_event_demand_subset (qids : Finset Qid)
    (executionPath : List Action → List Action) (weight : Qid × List Action → ℝ)
    (overhead : TreeEvaluation Action → ℝ) (events : List (TreeEvaluation Action))
    (initial : MeteredTreeState Qid Action) (event : TreeEvaluation Action) (he : event ∈ events) :
    panelDemand qids (executionPath event.terminal) ⊆
      (replayMetered qids executionPath weight overhead events initial).materialized := by
  induction events generalizing initial with
  | nil => simp at he
  | cons head events ih =>
    rcases List.mem_cons.mp he with rfl | he
    · exact (subset_union_right : panelDemand qids (executionPath event.terminal) ⊆
        (meterStep qids executionPath weight overhead initial event).materialized).trans
          (replayMetered_initial_cache_subset qids executionPath weight overhead events
            (meterStep qids executionPath weight overhead initial event))
    · exact ih (meterStep qids executionPath weight overhead initial head) he

theorem visited_prefix_demand_cached (qids : Finset Qid) (root : List Action)
    (weight : Qid × List Action → ℝ) (overhead : TreeEvaluation Action → ℝ)
    (events : List (TreeEvaluation Action)) (initial : MeteredTreeState Qid Action)
    (p : List Action) (hVisited : 0 < backedCount events p) :
    panelDemand qids (root ++ p) ⊆
      (replayMetered qids (fun x ↦ root ++ x) weight overhead events initial).materialized := by
  have hSome : ∃ e ∈ events, p <+: e.expanded := by
    by_contra! hMiss
    have hZero : backedCount events p = 0 := by
      simpa [backedCount, List.filter_eq_nil_iff] using hMiss
    omega
  obtain ⟨event, he, hp⟩ := hSome
  have hFull : root ++ p <+: root ++ event.terminal :=
    (List.prefix_append_right_inj root).mpr (hp.trans event.expanded_is_prefix)
  exact (panelDemand_prefix_mono qids _ _ hFull).trans
    (replayMetered_event_demand_subset qids (fun x ↦ root ++ x) weight overhead events initial
      event he)

theorem visited_prefix_no_cold_cost (qids : Finset Qid) (root : List Action)
    (weight : Qid × List Action → ℝ) (overhead : TreeEvaluation Action → ℝ)
    (events : List (TreeEvaluation Action)) (initial : MeteredTreeState Qid Action)
    (p : List Action) (hVisited : 0 < backedCount events p) :
    coldWork weight
      (replayMetered qids (fun x ↦ root ++ x) weight overhead events initial).materialized
      (panelDemand qids (root ++ p)) = 0 :=
  cached_demand_is_free weight _ _
    (visited_prefix_demand_cached qids root weight overhead events initial p hVisited)

/-- Exact production next-edge formula; this statement does not include future overhead. -/
theorem visited_child_next_edge_zero (qids : Finset Qid) (root : List Action)
    (weight : Qid × List Action → ℝ) (overhead : TreeEvaluation Action → ℝ)
    (events : List (TreeEvaluation Action)) (initial : MeteredTreeState Qid Action)
    (p : List Action) (a : Action) (hWeight : ∀ r, 0 ≤ weight r)
    (hVisited : 0 < backedCount events (p ++ [a])) :
    let cached :=
      (replayMetered qids (fun x ↦ root ++ x) weight overhead events initial).materialized
    max 0 (coldWork weight cached (panelDemand qids (root ++ (p ++ [a]))) -
      coldWork weight cached (panelDemand qids (root ++ p))) = 0 := by
  dsimp only
  rw [visited_prefix_no_cold_cost qids root weight overhead events initial _ hVisited]
  have hNonneg := coldWork_nonnegative weight hWeight
    (replayMetered qids (fun x ↦ root ++ x) weight overhead events initial).materialized
    (panelDemand qids (root ++ p))
  exact max_eq_left (by linarith)

/-- This does not require calibrated predictions or equality of physical and predicted weights. -/
theorem visited_child_any_forecast_next_edge_zero (qids : Finset Qid) (root : List Action)
    (physicalWeight forecastWeight : Qid × List Action → ℝ)
    (overhead : TreeEvaluation Action → ℝ) (events : List (TreeEvaluation Action))
    (initial : MeteredTreeState Qid Action) (p : List Action) (a : Action)
    (hForecast : ∀ r, 0 ≤ forecastWeight r) (hVisited : 0 < backedCount events (p ++ [a])) :
    let cached :=
      (replayMetered qids (fun x ↦ root ++ x) physicalWeight overhead events initial).materialized
    max 0 (coldWork forecastWeight cached (panelDemand qids (root ++ (p ++ [a]))) -
      coldWork forecastWeight cached (panelDemand qids (root ++ p))) = 0 := by
  dsimp only
  have hFree := cached_demand_is_free forecastWeight _ _
    (visited_prefix_demand_cached qids root physicalWeight overhead events initial _ hVisited)
  rw [hFree]
  have hNonneg := coldWork_nonnegative forecastWeight hForecast
    (replayMetered qids (fun x ↦ root ++ x) physicalWeight overhead events initial).materialized
    (panelDemand qids (root ++ p))
  exact max_eq_left (by linarith)

/-- Actual backed-up visits and actual restorable-cache state supply the premises above. -/
theorem actual_visited_child_next_edge_zero (qids : Finset Qid) (root : List Action)
    (physicalWeight forecastWeight : Qid × List Action → ℝ)
    (overhead : TreeEvaluation Action → ℝ) (events : List (TreeEvaluation Action))
    (initial : MeteredTreeState Qid Action) (caches : PersistentCaches Qid Action)
    (p : List Action) (a : Action) (hStats : initial.stats = emptyStatistics)
    (hCache : caches.restorable = caches.everMaterialized)
    (hLedger : caches.everMaterialized = initial.materialized)
    (hForecast : ∀ r, 0 ≤ forecastWeight r)
    (hVisited : 0 < ((replayMetered qids (fun x ↦ root ++ x) physicalWeight overhead events
      initial).stats (p ++ [a])).visits) :
    let cached := (replayPublished qids (fun x ↦ root ++ x) events caches).restorable
    max 0 (coldWork forecastWeight cached (panelDemand qids (root ++ (p ++ [a]))) -
      coldWork forecastWeight cached (panelDemand qids (root ++ p))) = 0 := by
  dsimp only
  rw [replayPublished_cache_matches_metered qids (fun x ↦ root ++ x) physicalWeight overhead
    events caches initial hCache hLedger]
  have hCount : 0 < backedCount events (p ++ [a]) := by
    rw [replayMetered_stats, replayBackup_visits, hStats] at hVisited
    simpa [emptyStatistics] using hVisited
  exact visited_child_any_forecast_next_edge_zero qids root physicalWeight forecastWeight overhead
    events initial p a hForecast hCount

end AgentUCTPaper
