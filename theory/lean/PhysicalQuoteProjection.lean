import UnseenReceiptQuotes

set_option autoImplicit false
set_option maxRecDepth 16384
set_option maxHeartbeats 6000000
noncomputable section
namespace AgentUCT32MConcrete
open AgentUCT32MContinuation AgentUCTSavedBudget AgentUCTObservability
  AgentUCTPhysicalDiagnostic AgentUCTNativeBudget AgentUCTPanelAllocation
  AgentUCTNativeRepair AgentUCTNativeRefinement AgentUCTPaper

def pathWarmDepth (cache : Finset (List Act)) (path : List Act) : ℕ :=
  ((Finset.range (path.length+1)).filter fun i => 0 < i ∧ path.take i ∈ cache).sup id

def pathSuffix (cache : Finset (List Act)) (path : List Act) : List (List Act) :=
  ((List.range (path.length+1)).filter fun i => pathWarmDepth cache path < i).map path.take

def pathQuote (mode : ForecastMode) (cache : Finset (List Act))
    (price : Act → ℝ) (path : List Act) : ℝ :=
  match mode with
  | .unpriced => 0
  | .complete => ((pathSuffix cache path).map fun p => price (p.getLastD .stop)).sum
  | .next => nextUnpaidBill ∅ (fun p => price (p.getLastD .stop)) (pathSuffix cache path)

theorem source_suffix_full_panel_projection (cache : Finset (List Act))
    (qid : Fin 150) (path : List Act) :
    sourceSuffix ((Finset.univ : Finset (Fin 150)) ×ˢ cache) (fun _ _ => false) qid path =
      (pathSuffix cache path).map fun p => (qid,p) := by
  have hw : lastWarmDepth ((Finset.univ : Finset (Fin 150)) ×ˢ cache) qid path =
      pathWarmDepth cache path := by
    unfold lastWarmDepth pathWarmDepth
    congr 1
    ext i
    simp only [Finset.mem_filter,Finset.mem_product,Finset.mem_univ,true_and]
  unfold sourceSuffix pathSuffix
  rw [hw]
  simp only [Bool.not_false,List.filter_true,List.map_map,Function.comp_def]

theorem next_unpaid_map_price {R S : Type*} [DecidableEq R] [DecidableEq S]
    (mapResource : R → S) (price : S → ℝ) (resources : List R) :
    nextUnpaidBill ∅ price (resources.map mapResource) =
      nextUnpaidBill ∅ (fun r => price (mapResource r)) resources := by
  induction resources with
  | nil => rfl
  | cons r rest ih =>
      simp only [List.map_cons,nextUnpaidBill,Finset.notMem_empty,false_or,ih]

theorem source_quote_full_panel_projection (mode : ForecastMode)
    (cache : Finset (List Act)) (price : Act → ℝ) (qid : Fin 150) (path : List Act) :
    sourceQidQuote mode ((Finset.univ : Finset (Fin 150)) ×ˢ cache)
      (fun _ _ => false) (fun r => price (resourceAction r)) qid path =
      pathQuote mode cache price path := by
  cases mode with
  | unpriced => rfl
  | complete =>
      simp only [sourceQidQuote,pathQuote,source_suffix_full_panel_projection,List.map_map,
        Function.comp_def,resourceAction]
  | next =>
      simp only [sourceQidQuote,pathQuote,source_suffix_full_panel_projection]
      exact next_unpaid_map_price _ _ _

theorem physical_mc16_full_panel_projection (mode : ForecastMode)
    (price : Act → ℝ) (before : List (TreeEvaluation Act)) (p : List Act) (a : Act) :
    sourcePanelMC16 panel150 mode (ownPanelCache panel150 before) (fun _ _ => false)
      (fun r => price (resourceAction r)) (budgetTape.completion before p a) =
      150 * pathQuote mode (pathHistoryCache before) price (safeCompletion (p++[a])) := by
  rw [own_panel_cache_product]
  simp only [panel150,sourcePanelMC16,sourcePanelSample,budgetTape,
    source_quote_full_panel_projection,Finset.sum_const,Finset.card_univ,Fintype.card_fin,
    nsmul_eq_mul]
  norm_num

theorem physical_reference_penalty_full_panel_projection (mode : ForecastMode)
    (Cref : ℝ) (before : List (TreeEvaluation Act)) (p : List Act) (a : Act) :
    (2/Cref) * sourcePanelMC16 panel150 mode (ownPanelCache panel150 before) (fun _ _ => false)
      (fun r => completedPrice unitRoleUnused (resourceAction r)) (budgetTape.completion before p a) =
      (300/Cref) * pathQuote mode (pathHistoryCache before)
        (completedPrice unitRoleUnused) (safeCompletion (p++[a])) := by
  rw [physical_mc16_full_panel_projection]
  ring

theorem completed_physical_bill_full_panel_projection
    (before : List (TreeEvaluation Act)) :
    completedBill unitRoleUnused before =
      150 * ∑ p ∈ pathHistoryCache before,completedPrice unitRoleUnused (p.getLastD .stop) := by
  unfold completedBill panelActualBill
  rw [replay_panel_actual_bill_sum]
  simp only [panel150,resourceAction,Finset.sum_const,Finset.card_univ,
    Fintype.card_fin,nsmul_eq_mul]
  norm_num

end AgentUCT32MConcrete
