import AgentUCTPaper.TreeExecution
import AgentUCTPaper.CostModel

/-! # Deriving deepest-checkpoint execution from a prefix-complete ledger -/

set_option autoImplicit false

noncomputable section

namespace AgentUCTPaper

open Finset

variable {Qid Action : Type*} [DecidableEq Qid] [DecidableEq Action]

def savedStages (cached : Finset (Qid × List Action)) (qid : Qid) (path : List Action) :
    Finset ℕ := insert 0 ((Icc 1 path.length).filter (fun i ↦ (qid, path.take i) ∈ cached))

def deepestSaved (cached : Finset (Qid × List Action)) (qid : Qid) (path : List Action) : ℕ :=
  (savedStages cached qid path).max' ⟨0, by simp [savedStages]⟩

def PrefixCompleteCache (cached : Finset (Qid × List Action)) : Prop :=
  ∀ q p, (q, p) ∈ cached → ∀ i, 1 ≤ i → i ≤ p.length → (q, p.take i) ∈ cached

theorem deepestSaved_mem (cached : Finset (Qid × List Action)) (qid : Qid) (path : List Action) :
    deepestSaved cached qid path ∈ savedStages cached qid path := Finset.max'_mem _ _

theorem deepestSaved_le_length (cached : Finset (Qid × List Action))
    (qid : Qid) (path : List Action) : deepestSaved cached qid path ≤ path.length := by
  rcases mem_insert.mp (deepestSaved_mem cached qid path) with h | h
  · omega
  · exact (mem_Icc.mp (mem_filter.mp h).1).2

theorem cached_stage_le_deepest (cached : Finset (Qid × List Action))
    (qid : Qid) (path : List Action) (i : ℕ)
    (hi : i ∈ Icc 1 path.length) (hCached : (qid, path.take i) ∈ cached) :
    i ≤ deepestSaved cached qid path := by
  apply Finset.le_max'
  simp [savedStages, hi, hCached]

theorem cached_stage_iff_le_deepest (cached : Finset (Qid × List Action))
    (hClosed : PrefixCompleteCache cached) (qid : Qid) (path : List Action) (i : ℕ)
    (hi : i ∈ Icc 1 path.length) :
    (qid, path.take i) ∈ cached ↔ i ≤ deepestSaved cached qid path := by
  constructor
  · exact cached_stage_le_deepest cached qid path i hi
  · intro hle
    have hi1 := (mem_Icc.mp hi).1
    rcases mem_insert.mp (deepestSaved_mem cached qid path) with hz | hc
    · omega
    · have hd := deepestSaved_le_length cached qid path
      have h := hClosed qid (path.take (deepestSaved cached qid path))
        (mem_filter.mp hc).2 i hi1 (by simp [List.length_take, Nat.min_eq_left hd, hle])
      simpa [List.take_take, Nat.min_eq_left hle] using h

theorem missing_stage_iff_after_checkpoint (cached : Finset (Qid × List Action))
    (hClosed : PrefixCompleteCache cached) (qid : Qid) (path : List Action) (i : ℕ)
    (hi : i ∈ Icc 1 path.length) :
    (qid, path.take i) ∉ cached ↔ deepestSaved cached qid path < i := by
  rw [cached_stage_iff_le_deepest cached hClosed qid path i hi, not_le]

theorem singleton_panel_stage_image (qid : Qid) (path : List Action) :
    panelDemand {qid} path = (Icc 1 path.length).image (fun i ↦ (qid, path.take i)) := by
  ext ⟨q, p⟩
  simp only [panelDemand, executionPrefixes, mem_product, mem_singleton, mem_image, Prod.mk.injEq]
  aesop

theorem panel_missing_is_checkpoint_suffix (cached : Finset (Qid × List Action))
    (hClosed : PrefixCompleteCache cached) (qid : Qid) (path : List Action) :
    panelDemand {qid} path \ cached =
      (Ioc (deepestSaved cached qid path) path.length).image (fun i ↦ (qid, path.take i)) := by
  rw [singleton_panel_stage_image]
  ext resource
  constructor
  · intro h
    obtain ⟨i, hi, rfl⟩ := mem_image.mp (mem_sdiff.mp h).1
    exact mem_image.mpr ⟨i, mem_Ioc.mpr
      ⟨(missing_stage_iff_after_checkpoint cached hClosed qid path i hi).mp (mem_sdiff.mp h).2,
        (mem_Icc.mp hi).2⟩, rfl⟩
  · intro h
    obtain ⟨i, hi, rfl⟩ := mem_image.mp h
    have hrange : i ∈ Icc 1 path.length := mem_Icc.mpr
      ⟨by have := (mem_Ioc.mp hi).1; omega, (mem_Ioc.mp hi).2⟩
    exact mem_sdiff.mpr ⟨mem_image.mpr ⟨i, hrange, rfl⟩,
      (missing_stage_iff_after_checkpoint cached hClosed qid path i hrange).mpr
        (mem_Ioc.mp hi).1⟩

omit [DecidableEq Qid] [DecidableEq Action] in
theorem prefix_keys_injective (qid : Qid) (path : List Action) {i j : ℕ}
    (hi : i ≤ path.length) (hj : j ≤ path.length)
    (heq : (qid, path.take i) = (qid, path.take j)) : i = j := by
  have hlen := congrArg (fun r : Qid × List Action ↦ r.2.length) heq
  simpa [List.length_take, Nat.min_eq_left hi, Nat.min_eq_left hj] using hlen

theorem coldWork_eq_deepest_suffix (weight : Qid × List Action → ℝ)
    (cached : Finset (Qid × List Action)) (hClosed : PrefixCompleteCache cached)
    (qid : Qid) (path : List Action) :
    coldWork weight cached (panelDemand {qid} path) =
      checkpointSuffixBill (fun i ↦ weight (qid, path.take i))
        (deepestSaved cached qid path) path.length := by
  unfold coldWork checkpointSuffixBill
  rw [panel_missing_is_checkpoint_suffix cached hClosed qid path, Finset.sum_image]
  intro i hi j hj heq
  exact prefix_keys_injective qid path (mem_Ioc.mp hi).2 (mem_Ioc.mp hj).2 heq

omit [DecidableEq Qid] [DecidableEq Action] in
theorem empty_prefixComplete : PrefixCompleteCache (∅ : Finset (Qid × List Action)) := by
  simp [PrefixCompleteCache]

omit [DecidableEq Qid] in
theorem panelDemand_prefixComplete (qids : Finset Qid) (path : List Action) :
    PrefixCompleteCache (panelDemand qids path) := by
  intro q p hp i hi hlen
  obtain ⟨hq, hp⟩ := (panelDemand_mem qids path p q).mp hp
  obtain ⟨j, hj, rfl⟩ := mem_image.mp hp
  have hjlen := (mem_Icc.mp hj).2
  have hij : i ≤ j := by simpa [List.length_take, Nat.min_eq_left hjlen] using hlen
  apply (panelDemand_mem qids path ((path.take j).take i) q).mpr
  refine ⟨hq, mem_image.mpr ⟨i, mem_Icc.mpr ⟨hi, hij.trans hjlen⟩, ?_⟩⟩
  simp [List.take_take, Nat.min_eq_left hij]

theorem prefixComplete_union {left right : Finset (Qid × List Action)}
    (hLeft : PrefixCompleteCache left) (hRight : PrefixCompleteCache right) :
    PrefixCompleteCache (left ∪ right) := by
  intro q p hp i hi hlen
  rcases mem_union.mp hp with hp | hp
  · exact mem_union_left _ (hLeft q p hp i hi hlen)
  · exact mem_union_right _ (hRight q p hp i hi hlen)

theorem replayMetered_prefixComplete (qids : Finset Qid)
    (executionPath : List Action → List Action) (weight : Qid × List Action → ℝ)
    (overhead : TreeEvaluation Action → ℝ) (events : List (TreeEvaluation Action))
    (initial : MeteredTreeState Qid Action) (hInitial : PrefixCompleteCache initial.materialized) :
    PrefixCompleteCache
      (replayMetered qids executionPath weight overhead events initial).materialized := by
  induction events generalizing initial with
  | nil => exact hInitial
  | cons event events ih =>
    exact ih (meterStep qids executionPath weight overhead initial event)
      (prefixComplete_union hInitial
        (panelDemand_prefixComplete qids (executionPath event.terminal)))

end AgentUCTPaper
