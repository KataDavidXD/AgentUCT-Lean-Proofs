import PanelReceiptMeans




set_option autoImplicit false
set_option maxRecDepth 8192
set_option maxHeartbeats 4000000
set_option linter.constructorNameAsVariable false
noncomputable section
namespace AgentUCTPanelAllocation
open AgentUCTNativeRefinement AgentUCTNativeRepair AgentUCTPaper
variable {Qid : Type*} [DecidableEq Qid]

def livePanelForecast (qids : Finset Qid) (mode : ForecastMode) (tape : SharedTape)
    (free : Qid → List Act → Bool) (priors caps : Act → ℝ)
    (means : List (TreeEvaluation Act) → ReceiptMeans Qid)
    (futureOverhead : List (TreeEvaluation Act) → List Act → ℝ)
    (before : List (TreeEvaluation Act)) (p : List Act) (a : Act) : ℝ :=
  sourcePanelMC16 qids mode (ownPanelCache qids before) free
    (liveReceiptPrice priors caps (means before)) (tape.completion before p a) +
    (if mode = .next ∨ mode = .unpriced then 0 else futureOverhead before p)

def livePanelPenalty (qids : Finset Qid) (mode : ForecastMode) (tape : SharedTape)
    (free : Qid → List Act → Bool) (priors caps : Act → ℝ)
    (means : List (TreeEvaluation Act) → ReceiptMeans Qid)
    (futureOverhead : List (TreeEvaluation Act) → List Act → ℝ) (beta Cref : ℝ)
    (before : List (TreeEvaluation Act)) (p : List Act) (a : Act) : ℝ :=
  (beta/Cref) * livePanelForecast qids mode tape free priors caps means futureOverhead before p a

def panelActualBill (qids : Finset Qid) (physicalPrice : Qid × List Act → ℝ)
    (before : List (TreeEvaluation Act)) : ℝ := (replayPanel qids physicalPrice before).totalPaid

def panelGenerate (qids : Finset Qid) (mode : ForecastMode) (tape : SharedTape)
    (free : Qid → List Act → Bool) (priors caps : Act → ℝ)
    (means : List (TreeEvaluation Act) → ReceiptMeans Qid)
    (futureOverhead : List (TreeEvaluation Act) → List Act → ℝ)
    (physicalPrice : Qid × List Act → ℝ) (c beta Cref B : ℝ)
    (quality : Qid → List Act → ℝ) (cap : ℕ) : List (TreeEvaluation Act) :=
  nativeGenerate tape c (livePanelPenalty qids mode tape free priors caps means futureOverhead beta Cref)
    (panelActualBill qids physicalPrice) B (fun path => panelReward qids (fun qid => quality qid path)) cap

theorem panel_generated_allocation (qids : Finset Qid) (mode : ForecastMode) (tape : SharedTape)
    (ht : LegalSupportedTape tape) (free : Qid → List Act → Bool) (priors caps : Act → ℝ)
    (means : List (TreeEvaluation Act) → ReceiptMeans Qid)
    (futureOverhead : List (TreeEvaluation Act) → List Act → ℝ)
    (physicalPrice : Qid × List Act → ℝ) (c beta Cref B : ℝ)
    (quality : Qid → List Act → ℝ) (cap : ℕ) :
    TreeAllocationRule nativeTerminals c
      (livePanelPenalty qids mode tape free priors caps means futureOverhead beta Cref)
      (panelGenerate qids mode tape free priors caps means futureOverhead physicalPrice c beta Cref B quality cap) :=
  native_generated_tree_allocation_rule tape ht c _ _ B _ cap

theorem panel_generated_legal_tree (qids : Finset Qid) (mode : ForecastMode) (tape : SharedTape)
    (ht : LegalSupportedTape tape) (free : Qid → List Act → Bool) (priors caps : Act → ℝ)
    (means : List (TreeEvaluation Act) → ReceiptMeans Qid)
    (futureOverhead : List (TreeEvaluation Act) → List Act → ℝ)
    (physicalPrice : Qid × List Act → ℝ) (c beta Cref B : ℝ)
    (quality : Qid → List Act → ℝ) (cap : ℕ) :
    LegalTreeRun Terminal {[]}
      (panelGenerate qids mode tape free priors caps means futureOverhead physicalPrice c beta Cref B quality cap) :=
  native_generated_legal_tree tape ht c _ _ B _ cap

theorem supported_mc16_in_native_subtree (tape : SharedTape) (ht : LegalSupportedTape tape)
    (before : List (TreeEvaluation Act)) (p : List Act) (hp : Legal p)
    (a : Act) (ha : a ∈ available p) (i : Fin 16) :
    tape.completion before p a i ∈ subtreeTerminals nativeTerminals (p++[a]) := by
  obtain ⟨hterm,hpre⟩ := ht.2 before p a i hp ha
  exact Finset.mem_filter.mpr ⟨(native_terminals_iff_terminal _).mpr hterm,hpre⟩

theorem supported_mc16_native_law_mass (tape : SharedTape) (ht : LegalSupportedTape tape)
    (before : List (TreeEvaluation Act)) (p : List Act) (hp : Legal p)
    (a : Act) (ha : a ∈ available p) :
    (∑ path ∈ subtreeTerminals nativeTerminals (p++[a]),
      sampledLaw 16 (tape.completion before p a) path) = 1 :=
  sampledLaw_mass _ 16 (by decide) _ (supported_mc16_in_native_subtree tape ht before p hp a ha)

theorem supported_completion_historical_positive (tape : SharedTape) (ht : LegalSupportedTape tape)
    (before : List (TreeEvaluation Act)) (p : List Act) (hp : Legal p)
    (a : Act) (ha : a ∈ available p) (i : Fin 16) (smoothing : ℝ) (hs : 0 < smoothing) :
    ∃ tail, tape.completion before p a i = (p++[a])++tail ∧
      0 < pathProbability before smoothing (p++[a]) tail := by
  obtain ⟨hterm,tail,hpath⟩ := ht.2 before p a i hp ha
  refine ⟨tail,hpath.symm,?_⟩
  have hlegal : followLegal (p++[a]) tail = true := by
    have hfull := hterm.1
    rw [← hpath] at hfull
    simp only [Legal,followLegal_append,List.nil_append,Bool.and_eq_true,decide_eq_true_eq] at hfull
    exact hfull.2
  exact legal_tail_positive_probability before smoothing hs (p++[a]) tail hlegal

theorem live_panel_forecast_nonnegative (qids : Finset Qid) (mode : ForecastMode) (tape : SharedTape)
    (free : Qid → List Act → Bool) (priors caps : Act → ℝ)
    (means : List (TreeEvaluation Act) → ReceiptMeans Qid)
    (futureOverhead : List (TreeEvaluation Act) → List Act → ℝ)
    (hpriors : ∀ a, 0 ≤ priors a) (hcaps : ∀ a, 0 ≤ caps a)
    (hb : ∀ before, BoundedReceipts caps (means before))
    (ho : ∀ before p, 0 ≤ futureOverhead before p)
    (before : List (TreeEvaluation Act)) (p : List Act) (a : Act) :
    0 ≤ livePanelForecast qids mode tape free priors caps means futureOverhead before p a := by
  have hprices : ∀ resource, 0 ≤ liveReceiptPrice priors caps (means before) resource :=
    fun resource => (live_receipt_price_envelope priors caps _ hpriors hcaps (hb before) resource).1
  unfold livePanelForecast sourcePanelMC16 sourcePanelSample
  apply add_nonneg
  · apply div_nonneg _ (by norm_num)
    exact Finset.sum_nonneg (fun i _ => Finset.sum_nonneg (fun qid _ =>
      source_quotes_nonnegative mode _ free _ hprices qid _))
  · split_ifs
    · exact le_rfl
    · exact ho before p

theorem generated_panel_initial_bill_sum (qids : Finset Qid) (physicalPrice : Qid × List Act → ℝ)
    (reward : List Act → ℝ) :
    panelActualBill qids physicalPrice (repairedInitialization explicitTape reward) =
      ∑ qid ∈ qids, ∑ p ∈ pathHistoryCache (repairedInitialization explicitTape reward), physicalPrice (qid,p) :=
  replay_panel_actual_bill_sum qids physicalPrice _

theorem generated_panel_initial_stationary_bill (qids : Finset Qid) (reward : List Act → ℝ)
    (q a e b k : ℝ) :
    panelActualBill qids (fun resource => price q a e b k ((),resource.2))
      (repairedInitialization explicitTape reward) = (qids.card : ℝ)*(7*q+16*a+e) :=
  generated_homogeneous_initial_panel_bill qids reward q a e b k

end AgentUCTPanelAllocation
