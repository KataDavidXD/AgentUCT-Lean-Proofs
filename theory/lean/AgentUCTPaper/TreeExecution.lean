import AgentUCTPaper.TreeBackup
import AgentUCTPaper.Cache

/-! # A shared operational trace for backup and physical materialization

Resource identities are qid and full execution prefix within a fixed namespace.
`executionPath` embeds relative tree paths under the caller's execution root.
Successful execution persists every demanded prefix; nonreusable overhead is separate.
-/

set_option autoImplicit false

noncomputable section

namespace AgentUCTPaper

open Finset

variable {Qid Action : Type*} [DecidableEq Qid] [DecidableEq Action]

def executionPrefixes (path : List Action) : Finset (List Action) :=
  (Icc 1 path.length).image (fun stage ↦ path.take stage)

def panelDemand (qids : Finset Qid) (path : List Action) : Finset (Qid × List Action) :=
  qids ×ˢ executionPrefixes path

omit [DecidableEq Qid] in
theorem panelDemand_mem (qids : Finset Qid) (path p : List Action) (qid : Qid) :
    (qid, p) ∈ panelDemand qids path ↔ qid ∈ qids ∧ p ∈ executionPrefixes path := by
  simp [panelDemand]

omit [DecidableEq Qid] in
theorem different_qids_disjoint (q1 q2 : Qid) (path1 path2 : List Action) (h : q1 ≠ q2) :
    Disjoint (panelDemand {q1} path1) (panelDemand {q2} path2) := by
  apply Finset.disjoint_left.mpr
  intro resource h1 h2
  simp only [panelDemand, mem_product, mem_singleton] at h1 h2
  exact h (h1.1.symm.trans h2.1)

theorem other_qid_cache_cannot_pay (weight : Qid × List Action → ℝ)
    (q1 q2 : Qid) (path1 path2 : List Action) (h : q1 ≠ q2) :
    coldWork weight (panelDemand {q1} path1) (panelDemand {q2} path2) =
      cacheWeight weight (panelDemand {q2} path2) := by
  unfold coldWork cacheWeight
  rw [Finset.sdiff_eq_self_of_disjoint (different_qids_disjoint q1 q2 path1 path2 h).symm]

/-- Full-panel physical work sums the separate qid bills; it is not a panel average. -/
theorem coldWork_panel_sum (weight : Qid × List Action → ℝ)
    (cached : Finset (Qid × List Action)) (qids : Finset Qid) (path : List Action) :
    coldWork weight cached (panelDemand qids path) =
      ∑ qid ∈ qids, coldWork weight cached (panelDemand {qid} path) := by
  simp [coldWork, panelDemand, Finset.sdiff_eq_filter, Finset.sum_filter, Finset.sum_product]

def panelScore (qids : Finset Qid) (score : Qid → ℝ) : ℝ :=
  (∑ qid ∈ qids, score qid) / qids.card

omit [DecidableEq Qid] [DecidableEq Action] in
theorem panelScore_bounded (qids : Finset Qid) (score : Qid → ℝ)
    (hScore : ∀ qid ∈ qids, 0 ≤ score qid ∧ score qid ≤ 1) :
    panelScore qids score ∈ Set.Icc (0 : ℝ) 1 := by
  have h0 : 0 ≤ ∑ qid ∈ qids, score qid := sum_nonneg (fun q hq ↦ (hScore q hq).1)
  have h1 : (∑ qid ∈ qids, score qid) ≤ (qids.card : ℝ) := by
    simpa using sum_le_sum (fun q hq ↦ (hScore q hq).2)
  unfold panelScore
  constructor
  · exact div_nonneg h0 (Nat.cast_nonneg _)
  · by_cases hCard : qids.card = 0
    · simp [hCard]
    · exact (div_le_one (Nat.cast_pos.mpr (Nat.pos_of_ne_zero hCard))).mpr h1

structure MeteredTreeState (Qid Action : Type*) where
  stats : TreeStatistics Action
  materialized : Finset (Qid × List Action)
  coldPaid : ℝ
  overheadPaid : ℝ

def MeteredTreeState.totalPaid (state : MeteredTreeState Qid Action) : ℝ :=
  state.coldPaid + state.overheadPaid

def meterStep (qids : Finset Qid) (executionPath : List Action → List Action)
    (weight : Qid × List Action → ℝ) (overhead : TreeEvaluation Action → ℝ)
    (state : MeteredTreeState Qid Action) (event : TreeEvaluation Action) :
    MeteredTreeState Qid Action :=
  let demand := panelDemand qids (executionPath event.terminal)
  let cold := coldWork weight state.materialized demand
  let billed := { event with bill := cold + overhead event }
  { stats := backupEvent state.stats billed
    materialized := state.materialized ∪ demand
    coldPaid := state.coldPaid + cold
    overheadPaid := state.overheadPaid + overhead event }

def replayMetered (qids : Finset Qid) (executionPath : List Action → List Action)
    (weight : Qid × List Action → ℝ) (overhead : TreeEvaluation Action → ℝ)
    (events : List (TreeEvaluation Action)) (initial : MeteredTreeState Qid Action) :
    MeteredTreeState Qid Action :=
  events.foldl (meterStep qids executionPath weight overhead) initial

/-- Cache objects and historical work are distinct state components, even in the persistent case. -/
structure PersistentCaches (Qid Action : Type*) where
  restorable : Finset (Qid × List Action)
  everMaterialized : Finset (Qid × List Action)

def publishComplete (qids : Finset Qid) (executionPath : List Action → List Action)
    (caches : PersistentCaches Qid Action) (event : TreeEvaluation Action) :
    PersistentCaches Qid Action :=
  let demand := panelDemand qids (executionPath event.terminal)
  ⟨caches.restorable ∪ demand, caches.everMaterialized ∪ demand⟩

def replayPublished (qids : Finset Qid) (executionPath : List Action → List Action)
    (events : List (TreeEvaluation Action)) (initial : PersistentCaches Qid Action) :
    PersistentCaches Qid Action := events.foldl (publishComplete qids executionPath) initial

/-- Equality follows from the initial state and successful persistence.
Eviction is a different transition and is not covered by this result. -/
theorem replayPublished_cache_equals_ledger (qids : Finset Qid)
    (executionPath : List Action → List Action) (events : List (TreeEvaluation Action))
    (initial : PersistentCaches Qid Action)
    (hInitial : initial.restorable = initial.everMaterialized) :
    (replayPublished qids executionPath events initial).restorable =
      (replayPublished qids executionPath events initial).everMaterialized := by
  induction events generalizing initial with
  | nil => exact hInitial
  | cons event events ih =>
    exact ih (publishComplete qids executionPath initial event)
      (by simp [publishComplete, hInitial])

theorem replayPublished_ledger_matches_metered (qids : Finset Qid)
    (executionPath : List Action → List Action) (weight : Qid × List Action → ℝ)
    (overhead : TreeEvaluation Action → ℝ) (events : List (TreeEvaluation Action))
    (caches : PersistentCaches Qid Action) (initial : MeteredTreeState Qid Action)
    (hInitial : caches.everMaterialized = initial.materialized) :
    (replayPublished qids executionPath events caches).everMaterialized =
      (replayMetered qids executionPath weight overhead events initial).materialized := by
  induction events generalizing caches initial with
  | nil => exact hInitial
  | cons event events ih =>
    exact ih (publishComplete qids executionPath caches event)
      (meterStep qids executionPath weight overhead initial event)
      (by simp [publishComplete, meterStep, hInitial])

theorem replayPublished_cache_matches_metered (qids : Finset Qid)
    (executionPath : List Action → List Action) (weight : Qid × List Action → ℝ)
    (overhead : TreeEvaluation Action → ℝ) (events : List (TreeEvaluation Action))
    (caches : PersistentCaches Qid Action) (initial : MeteredTreeState Qid Action)
    (hCache : caches.restorable = caches.everMaterialized)
    (hLedger : caches.everMaterialized = initial.materialized) :
    (replayPublished qids executionPath events caches).restorable =
      (replayMetered qids executionPath weight overhead events initial).materialized := by
  exact (replayPublished_cache_equals_ledger qids executionPath events caches hCache).trans
    (replayPublished_ledger_matches_metered qids executionPath weight overhead events caches
      initial hLedger)

theorem meterStep_stats (qids : Finset Qid) (executionPath : List Action → List Action)
    (weight : Qid × List Action → ℝ) (overhead : TreeEvaluation Action → ℝ)
    (state : MeteredTreeState Qid Action) (event : TreeEvaluation Action) :
    (meterStep qids executionPath weight overhead state event).stats =
      backupEvent state.stats event := rfl

theorem replayMetered_stats (qids : Finset Qid) (executionPath : List Action → List Action)
    (weight : Qid × List Action → ℝ) (overhead : TreeEvaluation Action → ℝ)
    (events : List (TreeEvaluation Action)) (initial : MeteredTreeState Qid Action) :
    (replayMetered qids executionPath weight overhead events initial).stats =
      replayBackup events initial.stats := by
  induction events generalizing initial with
  | nil => rfl
  | cons event events ih =>
    exact ih (meterStep qids executionPath weight overhead initial event)

theorem meterStep_cold_conservation (qids : Finset Qid)
    (executionPath : List Action → List Action) (weight : Qid × List Action → ℝ)
    (overhead : TreeEvaluation Action → ℝ) (state : MeteredTreeState Qid Action)
    (event : TreeEvaluation Action) :
    (meterStep qids executionPath weight overhead state event).coldPaid - state.coldPaid =
      cacheWeight weight (meterStep qids executionPath weight overhead state event).materialized -
        cacheWeight weight state.materialized := by
  simp only [meterStep, cache_union_accounting]
  ring

theorem replayMetered_cold_conservation (qids : Finset Qid)
    (executionPath : List Action → List Action) (weight : Qid × List Action → ℝ)
    (overhead : TreeEvaluation Action → ℝ) (events : List (TreeEvaluation Action))
    (initial : MeteredTreeState Qid Action) :
    (replayMetered qids executionPath weight overhead events initial).coldPaid - initial.coldPaid =
      cacheWeight weight
          (replayMetered qids executionPath weight overhead events initial).materialized -
        cacheWeight weight initial.materialized := by
  induction events generalizing initial with
  | nil => simp [replayMetered]
  | cons event events ih =>
    have h := ih (meterStep qids executionPath weight overhead initial event)
    have hstep := meterStep_cold_conservation qids executionPath weight overhead initial event
    change (replayMetered qids executionPath weight overhead events
      (meterStep qids executionPath weight overhead initial event)).coldPaid - initial.coldPaid =
      cacheWeight weight (replayMetered qids executionPath weight overhead events
        (meterStep qids executionPath weight overhead initial event)).materialized -
          cacheWeight weight initial.materialized
    linarith

theorem replayMetered_overhead (qids : Finset Qid) (executionPath : List Action → List Action)
    (weight : Qid × List Action → ℝ) (overhead : TreeEvaluation Action → ℝ)
    (events : List (TreeEvaluation Action)) (initial : MeteredTreeState Qid Action) :
    (replayMetered qids executionPath weight overhead events initial).overheadPaid =
      initial.overheadPaid + (events.map overhead).sum := by
  induction events generalizing initial with
  | nil => simp [replayMetered]
  | cons event events ih =>
    change (replayMetered qids executionPath weight overhead events
      (meterStep qids executionPath weight overhead initial event)).overheadPaid = _
    rw [ih]
    simp [meterStep, add_assoc]

theorem replayMetered_total (qids : Finset Qid) (executionPath : List Action → List Action)
    (weight : Qid × List Action → ℝ) (overhead : TreeEvaluation Action → ℝ)
    (events : List (TreeEvaluation Action)) (initial : MeteredTreeState Qid Action) :
    (replayMetered qids executionPath weight overhead events initial).totalPaid -
        initial.totalPaid =
      cacheWeight weight
          (replayMetered qids executionPath weight overhead events initial).materialized -
        cacheWeight weight initial.materialized + (events.map overhead).sum := by
  have hc := replayMetered_cold_conservation qids executionPath weight overhead events initial
  have ho := replayMetered_overhead qids executionPath weight overhead events initial
  unfold MeteredTreeState.totalPaid
  linarith

theorem replayMetered_cache_subset (qids : Finset Qid)
    (executionPath : List Action → List Action) (weight : Qid × List Action → ℝ)
    (overhead : TreeEvaluation Action → ℝ) (events : List (TreeEvaluation Action))
    (initial : MeteredTreeState Qid Action) (resources : Finset (Qid × List Action))
    (hInitial : initial.materialized ⊆ resources)
    (hDemand : ∀ e ∈ events, panelDemand qids (executionPath e.terminal) ⊆ resources) :
    (replayMetered qids executionPath weight overhead events initial).materialized ⊆ resources := by
  induction events generalizing initial with
  | nil => exact hInitial
  | cons event events ih =>
    apply ih (meterStep qids executionPath weight overhead initial event)
    · exact union_subset hInitial (hDemand event (by simp))
    · exact fun e he ↦ hDemand e (by simp [he])

theorem replayMetered_cold_budget (qids : Finset Qid)
    (executionPath : List Action → List Action) (weight : Qid × List Action → ℝ)
    (overhead : TreeEvaluation Action → ℝ) (events : List (TreeEvaluation Action))
    (initial : MeteredTreeState Qid Action) (resources : Finset (Qid × List Action))
    (hWeight : ∀ resource, 0 ≤ weight resource) (hInitial : initial.materialized ⊆ resources)
    (hDemand : ∀ e ∈ events, panelDemand qids (executionPath e.terminal) ⊆ resources) :
    (replayMetered qids executionPath weight overhead events initial).coldPaid - initial.coldPaid ≤
      cacheWeight weight resources - cacheWeight weight initial.materialized := by
  rw [replayMetered_cold_conservation]
  exact sub_le_sub_right (cacheWeight_mono weight hWeight
    (replayMetered_cache_subset qids executionPath weight overhead events initial resources
      hInitial hDemand)) _

/-- A cached completion still contributes a visit and reward, but no new cold work. -/
theorem meterStep_cached_visit (qids : Finset Qid) (executionPath : List Action → List Action)
    (weight : Qid × List Action → ℝ) (overhead : TreeEvaluation Action → ℝ)
    (state : MeteredTreeState Qid Action) (event : TreeEvaluation Action)
    (hCached : panelDemand qids (executionPath event.terminal) ⊆ state.materialized) :
    (meterStep qids executionPath weight overhead state event).coldPaid = state.coldPaid ∧
      ((meterStep qids executionPath weight overhead state event).stats []).visits =
        (state.stats []).visits + 1 ∧
      (meterStep qids executionPath weight overhead state event).overheadPaid =
        state.overheadPaid + overhead event := by
  simp [meterStep, cached_demand_is_free weight _ _ hCached, backupEvent]

end AgentUCTPaper
