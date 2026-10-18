import PanelReceiptBilling





set_option autoImplicit false
set_option maxRecDepth 8192
set_option maxHeartbeats 4000000
set_option linter.constructorNameAsVariable false
noncomputable section
namespace AgentUCTPanelAllocation
open AgentUCTNativeRefinement AgentUCTNativeRepair AgentUCTPaper
variable {Qid : Type*} [DecidableEq Qid]

def receiptHistoryStep (caps : Act → ℝ)
    (rows : List (TreeEvaluation Act) → TreeEvaluation Act → List (PhysicalReceipt Qid))
    (s : List (TreeEvaluation Act) × ReceiptMeans Qid) (event : TreeEvaluation Act) :
    List (TreeEvaluation Act) × ReceiptMeans Qid :=
  ⟨s.1++[event],replayReceipts caps (rows s.1 event) s.2⟩

def replayReceiptHistory (caps : Act → ℝ)
    (rows : List (TreeEvaluation Act) → TreeEvaluation Act → List (PhysicalReceipt Qid))
    (initial : ReceiptMeans Qid) (events : List (TreeEvaluation Act)) :
    List (TreeEvaluation Act) × ReceiptMeans Qid :=
  events.foldl (receiptHistoryStep caps rows) ([],initial)

def meansFromHistory (caps : Act → ℝ)
    (rows : List (TreeEvaluation Act) → TreeEvaluation Act → List (PhysicalReceipt Qid))
    (initial : ReceiptMeans Qid) (events : List (TreeEvaluation Act)) : ReceiptMeans Qid :=
  (replayReceiptHistory caps rows initial events).2

theorem receipt_history_append (caps : Act → ℝ)
    (rows : List (TreeEvaluation Act) → TreeEvaluation Act → List (PhysicalReceipt Qid))
    (initial : ReceiptMeans Qid) (events : List (TreeEvaluation Act)) (event : TreeEvaluation Act) :
    replayReceiptHistory caps rows initial (events++[event]) =
      receiptHistoryStep caps rows (replayReceiptHistory caps rows initial events) event := by
  simp [replayReceiptHistory,List.foldl_append]

theorem receipt_history_projection (caps : Act → ℝ)
    (rows : List (TreeEvaluation Act) → TreeEvaluation Act → List (PhysicalReceipt Qid))
    (initial : ReceiptMeans Qid) (events : List (TreeEvaluation Act)) :
    (replayReceiptHistory caps rows initial events).1 = events := by
  induction events using List.reverseRecOn with
  | nil => rfl
  | append_singleton events event ih =>
      rw [receipt_history_append]
      simp only [receiptHistoryStep,ih]

theorem means_from_history_append (caps : Act → ℝ)
    (rows : List (TreeEvaluation Act) → TreeEvaluation Act → List (PhysicalReceipt Qid))
    (initial : ReceiptMeans Qid) (events : List (TreeEvaluation Act)) (event : TreeEvaluation Act) :
    meansFromHistory caps rows initial (events++[event]) =
      replayReceipts caps (rows events event) (meansFromHistory caps rows initial events) := by
  simp only [meansFromHistory,receipt_history_append,receiptHistoryStep,receipt_history_projection]

theorem causal_receipts_propagate_initial_error (tariff caps : Act → ℝ) (epsilon : ℝ)
    (rows : List (TreeEvaluation Act) → TreeEvaluation Act → List (PhysicalReceipt Qid))
    (initial : ReceiptMeans Qid) (he : 0 ≤ epsilon) (hc : ∀ a, tariff a ≤ caps a)
    (hi : ReceiptPriceError tariff epsilon initial)
    (hrows : ∀ before event r, r ∈ rows before event → r.actual = tariff (resourceAction r.resource))
    (events : List (TreeEvaluation Act)) :
    ReceiptPriceError tariff epsilon (meansFromHistory caps rows initial events) := by
  induction events using List.reverseRecOn with
  | nil => exact hi
  | append_singleton events event ih =>
      rw [means_from_history_append]
      exact stationary_replay_preserves_initial_price_error tariff caps epsilon _ he
        (hrows events event) hc _ ih

theorem causal_live_price_error_from_initial_state (priors caps tariff : Act → ℝ) (epsilon : ℝ)
    (rows : List (TreeEvaluation Act) → TreeEvaluation Act → List (PhysicalReceipt Qid))
    (initial : ReceiptMeans Qid) (he : 0 ≤ epsilon) (hc : ∀ a, tariff a ≤ caps a)
    (hp : ∀ a, |min (caps a) (priors a)-tariff a| ≤ epsilon)
    (hi : ReceiptPriceError tariff epsilon initial)
    (hrows : ∀ before event r, r ∈ rows before event → r.actual = tariff (resourceAction r.resource))
    (events : List (TreeEvaluation Act)) (r : Qid × List Act) :
    |liveReceiptPrice priors caps (meansFromHistory caps rows initial events) r -
      tariff (resourceAction r)| ≤ epsilon :=
  live_receipt_price_error priors caps tariff epsilon _ hp
    (causal_receipts_propagate_initial_error tariff caps epsilon rows initial he hc hi hrows events) r

def emptyReceiptMeans (qid : Qid) : ReceiptMeans Qid := ⟨∅,fun _ => (qid,[]),fun _ => 0,0⟩

theorem empty_receipt_means_has_zero_error (tariff : Act → ℝ) (epsilon : ℝ) (qid : Qid) :
    ReceiptPriceError tariff epsilon (emptyReceiptMeans qid) := by
  intro i hi; simp [emptyReceiptMeans] at hi

def causalPanelGenerate (qids : Finset Qid) (mode : ForecastMode) (tape : SharedTape)
    (free : Qid → List Act → Bool) (priors caps : Act → ℝ)
    (rows : List (TreeEvaluation Act) → TreeEvaluation Act → List (PhysicalReceipt Qid))
    (initial : ReceiptMeans Qid)
    (futureOverhead : List (TreeEvaluation Act) → List Act → ℝ)
    (physicalPrice : Qid × List Act → ℝ) (c beta Cref B : ℝ)
    (quality : Qid → List Act → ℝ) (cap : ℕ) : List (TreeEvaluation Act) :=
  panelGenerate qids mode tape free priors caps (meansFromHistory caps rows initial)
    futureOverhead physicalPrice c beta Cref B quality cap

theorem causal_panel_generated_allocation (qids : Finset Qid) (mode : ForecastMode) (tape : SharedTape)
    (ht : LegalSupportedTape tape) (free : Qid → List Act → Bool) (priors caps : Act → ℝ)
    (rows : List (TreeEvaluation Act) → TreeEvaluation Act → List (PhysicalReceipt Qid))
    (initial : ReceiptMeans Qid)
    (futureOverhead : List (TreeEvaluation Act) → List Act → ℝ)
    (physicalPrice : Qid × List Act → ℝ) (c beta Cref B : ℝ)
    (quality : Qid → List Act → ℝ) (cap : ℕ) :
    TreeAllocationRule nativeTerminals c
      (livePanelPenalty qids mode tape free priors caps (meansFromHistory caps rows initial) futureOverhead beta Cref)
      (causalPanelGenerate qids mode tape free priors caps rows initial futureOverhead physicalPrice c beta Cref B quality cap) :=
  panel_generated_allocation qids mode tape ht free priors caps _ futureOverhead physicalPrice c beta Cref B quality cap

end AgentUCTPanelAllocation
