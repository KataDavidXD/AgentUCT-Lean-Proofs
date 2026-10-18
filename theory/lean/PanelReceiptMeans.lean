import NativeDefinitionRefinement




set_option autoImplicit false
set_option maxRecDepth 8192
set_option maxHeartbeats 4000000
set_option linter.constructorNameAsVariable false
noncomputable section
namespace AgentUCTPanelAllocation
open AgentUCTNativeRefinement AgentUCTNativeRepair AgentUCTPaper
variable {Qid : Type*} [DecidableEq Qid]

def resourceAction (r : Qid × List Act) : Act := r.2.getLastD .stop

structure PhysicalReceipt (Qid : Type*) where
  callId : ℕ
  resource : Qid × List Act
  actual : ℝ

structure ReceiptMeans (Qid : Type*) where
  seen : Finset ℕ
  resource : ℕ → Qid × List Act
  quotedValue : ℕ → ℝ
  actualPaid : ℝ

def observeReceipt (caps : Act → ℝ) (s : ReceiptMeans Qid) (receipt : PhysicalReceipt Qid) : ReceiptMeans Qid :=
  if receipt.callId ∈ s.seen then s else
    ⟨insert receipt.callId s.seen,Function.update s.resource receipt.callId receipt.resource,
      Function.update s.quotedValue receipt.callId
        (min receipt.actual (caps (resourceAction receipt.resource))),s.actualPaid+receipt.actual⟩

theorem observe_seen_receipt_noop (caps : Act → ℝ) (s : ReceiptMeans Qid)
    (r : PhysicalReceipt Qid) (hseen : r.callId ∈ s.seen) : observeReceipt caps s r = s := by
  simp [observeReceipt,hseen]

theorem observe_receipt_seen (caps : Act → ℝ) (s : ReceiptMeans Qid) (r : PhysicalReceipt Qid) :
    r.callId ∈ (observeReceipt caps s r).seen := by
  by_cases h : r.callId ∈ s.seen <;> simp [observeReceipt,h]

theorem observe_receipt_idempotent (caps : Act → ℝ) (s : ReceiptMeans Qid)
    (r : PhysicalReceipt Qid) : observeReceipt caps (observeReceipt caps s r) r = observeReceipt caps s r :=
  observe_seen_receipt_noop caps _ r (observe_receipt_seen caps s r)

theorem fresh_receipt_actual_bill_unclipped (caps : Act → ℝ) (s : ReceiptMeans Qid)
    (r : PhysicalReceipt Qid) (hnew : r.callId ∉ s.seen) :
    (observeReceipt caps s r).actualPaid = s.actualPaid+r.actual := by
  simp [observeReceipt,hnew]

def BoundedReceipts (caps : Act → ℝ) (s : ReceiptMeans Qid) : Prop :=
  ∀ i ∈ s.seen, 0 ≤ s.quotedValue i ∧ s.quotedValue i ≤ caps (resourceAction (s.resource i))

theorem observe_preserves_bounded_receipts (caps : Act → ℝ) (s : ReceiptMeans Qid)
    (r : PhysicalReceipt Qid) (hcaps : ∀ a, 0 ≤ caps a) (hr : 0 ≤ r.actual)
    (hb : BoundedReceipts caps s) : BoundedReceipts caps (observeReceipt caps s r) := by
  by_cases hn : r.callId ∈ s.seen
  · simpa [observeReceipt,hn] using hb
  · intro i hi
    simp only [observeReceipt,if_neg hn,Finset.mem_insert] at hi
    rcases hi with rfl | hi
    · simp [observeReceipt,hn,hr,hcaps]
    · have hne : i ≠ r.callId := by intro he; subst i; exact hn hi
      simpa [observeReceipt,hn,hne] using hb i hi

def exactCallPool (s : ReceiptMeans Qid) (r : Qid × List Act) : Finset ℕ :=
  s.seen.filter fun i => s.resource i = r
def prefixCallPool (s : ReceiptMeans Qid) (r : Qid × List Act) : Finset ℕ :=
  s.seen.filter fun i => (s.resource i).2 = r.2
def actionCallPool (s : ReceiptMeans Qid) (a : Act) : Finset ℕ :=
  s.seen.filter fun i => resourceAction (s.resource i) = a
def selectedCallPool (s : ReceiptMeans Qid) (r : Qid × List Act) : Finset ℕ :=
  if (exactCallPool s r).Nonempty then exactCallPool s r
  else if (prefixCallPool s r).Nonempty then prefixCallPool s r
  else actionCallPool s (resourceAction r)

def liveReceiptPrice (priors caps : Act → ℝ) (s : ReceiptMeans Qid) (r : Qid × List Act) : ℝ :=
  onlineMean (min (caps (resourceAction r)) (priors (resourceAction r)))
    (selectedCallPool s r) s.quotedValue

theorem selected_call_pool_valid (s : ReceiptMeans Qid) (r : Qid × List Act)
    (i : ℕ) (hi : i ∈ selectedCallPool s r) :
    i ∈ s.seen ∧ resourceAction (s.resource i) = resourceAction r := by
  unfold selectedCallPool at hi
  split_ifs at hi with he hp
  · obtain ⟨hi,heq⟩ := Finset.mem_filter.mp hi
    exact ⟨hi,congrArg resourceAction heq⟩
  · obtain ⟨hi,heq⟩ := Finset.mem_filter.mp hi
    exact ⟨hi,by simp only [resourceAction,heq]⟩
  · exact Finset.mem_filter.mp hi

theorem live_receipt_price_envelope (priors caps : Act → ℝ) (s : ReceiptMeans Qid)
    (hpriors : ∀ a, 0 ≤ priors a) (hcaps : ∀ a, 0 ≤ caps a)
    (hb : BoundedReceipts caps s) (r : Qid × List Act) :
    0 ≤ liveReceiptPrice priors caps s r ∧ liveReceiptPrice priors caps s r ≤ caps (resourceAction r) := by
  apply onlineMean_envelope
  · exact le_min (hcaps _) (hpriors _)
  · exact min_le_left _ _
  · intro i hi
    obtain ⟨hseen,ha⟩ := selected_call_pool_valid s r i hi
    simpa only [ha] using hb i hseen

def replayReceipts (caps : Act → ℝ) (receipts : List (PhysicalReceipt Qid))
    (initial : ReceiptMeans Qid) : ReceiptMeans Qid := receipts.foldl (observeReceipt caps) initial

theorem replay_receipts_bounded (caps : Act → ℝ) (receipts : List (PhysicalReceipt Qid))
    (hcaps : ∀ a, 0 ≤ caps a) (hactual : ∀ r ∈ receipts, 0 ≤ r.actual)
    (initial : ReceiptMeans Qid) (hi : BoundedReceipts caps initial) :
    BoundedReceipts caps (replayReceipts caps receipts initial) := by
  induction receipts generalizing initial with
  | nil => exact hi
  | cons r receipts ih =>
      exact ih (fun r hr => hactual r (List.mem_cons_of_mem _ hr)) _
        (observe_preserves_bounded_receipts caps initial r hcaps (hactual r (by simp)) hi)

end AgentUCTPanelAllocation
