import PanelPredictionError




set_option autoImplicit false
set_option maxRecDepth 8192
set_option maxHeartbeats 4000000
set_option linter.constructorNameAsVariable false
noncomputable section
namespace AgentUCTPanelAllocation
open AgentUCTNativeRefinement AgentUCTNativeRepair AgentUCTPaper
variable {Qid : Type*} [DecidableEq Qid]

theorem replay_receipts_seen (caps : Act → ℝ) (receipts : List (PhysicalReceipt Qid))
    (initial : ReceiptMeans Qid) :
    (replayReceipts caps receipts initial).seen = initial.seen ∪ (receipts.map PhysicalReceipt.callId).toFinset := by
  induction receipts generalizing initial with
  | nil => simp [replayReceipts]
  | cons r receipts ih =>
      change (replayReceipts caps receipts (observeReceipt caps initial r)).seen = _
      rw [ih]
      by_cases hn : r.callId ∈ initial.seen
      · simp [observeReceipt,hn,Finset.insert_union,Finset.insert_eq_of_mem hn]
      · simp [observeReceipt,hn,Finset.insert_union]

theorem fresh_batch_actual_bill (caps : Act → ℝ) (receipts : List (PhysicalReceipt Qid))
    (initial : ReceiptMeans Qid) (hids : (receipts.map PhysicalReceipt.callId).Nodup)
    (hfresh : ∀ r ∈ receipts, r.callId ∉ initial.seen) :
    (replayReceipts caps receipts initial).actualPaid = initial.actualPaid+(receipts.map PhysicalReceipt.actual).sum := by
  induction receipts generalizing initial with
  | nil => simp [replayReceipts]
  | cons r receipts ih =>
      have hn : r.callId ∉ initial.seen := hfresh r (by simp)
      have htail : (receipts.map PhysicalReceipt.callId).Nodup := (List.nodup_cons.mp hids).2
      have hnew : ∀ s ∈ receipts, s.callId ∉ (observeReceipt caps initial r).seen := by
        intro s hs
        simp only [observeReceipt,if_neg hn,Finset.mem_insert,not_or]
        constructor
        · intro heq
          apply (List.nodup_cons.mp hids).1
          exact List.mem_map.mpr ⟨s,hs,heq⟩
        · exact hfresh s (List.mem_cons_of_mem _ hs)
      change (replayReceipts caps receipts (observeReceipt caps initial r)).actualPaid = _
      rw [ih _ htail hnew,fresh_receipt_actual_bill_unclipped caps initial r hn]
      simp only [List.map_cons,List.sum_cons]
      ring

theorem clipped_receipt_does_not_reduce_actual_bill (caps : Act → ℝ) (initial : ReceiptMeans Qid)
    (r : PhysicalReceipt Qid) (hfresh : r.callId ∉ initial.seen)
    (hclip : caps (resourceAction r.resource) < r.actual) :
    (observeReceipt caps initial r).actualPaid-initial.actualPaid >
      (observeReceipt caps initial r).quotedValue r.callId := by
  rw [fresh_receipt_actual_bill_unclipped caps initial r hfresh]
  simpa [observeReceipt,hfresh,min_eq_right hclip.le] using hclip

def modelTokenBill {Field : Type*} (fields : Finset Field) (weights : Field → ℝ)
    (usage : Field → ℕ) : ℝ := ∑ field ∈ fields, (usage field : ℝ)*weights field

theorem model_token_bill_nonnegative {Field : Type*} (fields : Finset Field)
    (weights : Field → ℝ) (hweights : ∀ f ∈ fields, 0 ≤ weights f) (usage : Field → ℕ) :
    0 ≤ modelTokenBill fields weights usage :=
  Finset.sum_nonneg (fun f hf => mul_nonneg (Nat.cast_nonneg _) (hweights f hf))

theorem panel_model_token_bill_aggregate {Field Call : Type*}
    (fields : Finset Field) (weights : Field → ℝ) (qids : Finset Qid)
    (calls : Qid → Finset Call) (usage : Qid → Call → Field → ℕ) :
    (∑ qid ∈ qids, ∑ call ∈ calls qid, modelTokenBill fields weights (usage qid call)) =
      ∑ field ∈ fields, (∑ qid ∈ qids, ∑ call ∈ calls qid, (usage qid call field : ℝ))*weights field := by
  simp only [modelTokenBill]
  calc
    _ = ∑ qid ∈ qids, ∑ field ∈ fields, ∑ call ∈ calls qid,
        (usage qid call field : ℝ)*weights field := by
      apply Finset.sum_congr rfl
      intro qid hqid
      exact Finset.sum_comm
    _ = ∑ field ∈ fields, ∑ qid ∈ qids, ∑ call ∈ calls qid,
        (usage qid call field : ℝ)*weights field := Finset.sum_comm
    _ = _ := by simp only [Finset.sum_mul]

theorem native_after_initial_prefix (tape : SharedTape) (c : ℝ)
    (penalty : List (TreeEvaluation Act) → List Act → Act → ℝ)
    (actualBill : List (TreeEvaluation Act) → ℝ) (B : ℝ) (reward : List Act → ℝ)
    (fuel : ℕ) (before : List (TreeEvaluation Act)) :
    before <+: nativeAfter tape c penalty actualBill B reward fuel before := by
  induction fuel generalizing before with
  | zero => exact List.prefix_refl _
  | succ fuel ih =>
      simp only [nativeAfter]
      split_ifs
      · exact List.prefix_refl _
      · exact (List.prefix_append _ _).trans (ih _)

theorem native_generate_preserves_all_eight (tape : SharedTape) (c : ℝ)
    (penalty : List (TreeEvaluation Act) → List Act → Act → ℝ)
    (actualBill : List (TreeEvaluation Act) → ℝ) (B : ℝ) (reward : List Act → ℝ) (cap : ℕ) :
    repairedInitialization tape reward <+: nativeGenerate tape c penalty actualBill B reward cap :=
  native_after_initial_prefix tape c penalty actualBill B reward _ _

theorem native_generate_has_at_least_eight (tape : SharedTape) (c : ℝ)
    (penalty : List (TreeEvaluation Act) → List Act → Act → ℝ)
    (actualBill : List (TreeEvaluation Act) → ℝ) (B : ℝ) (reward : List Act → ℝ) (cap : ℕ) :
    8 ≤ (nativeGenerate tape c penalty actualBill B reward cap).length := by
  have hp := (native_generate_preserves_all_eight tape c penalty actualBill B reward cap).length_le
  simpa only [repaired_initialization_eight] using hp

def panel150Qids : Finset (Fin 150) := Finset.univ

theorem panel150_nonempty : panel150Qids.Nonempty := ⟨0,Finset.mem_univ _⟩
theorem panel150_cardinality : panel150Qids.card = 150 := by simp [panel150Qids]

end AgentUCTPanelAllocation
