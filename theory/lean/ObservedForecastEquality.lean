import ObservedReceiptEquality



set_option autoImplicit false
set_option maxRecDepth 16384
set_option maxHeartbeats 4000000
set_option linter.constructorNameAsVariable false
noncomputable section
namespace AgentUCTObservability
open AgentUCTPhysicalDiagnostic AgentUCTNativeBudget AgentUCTPanelAllocation
  AgentUCTNativeRepair AgentUCTNativeRefinement AgentUCTPaper
variable {Qid : Type*} [DecidableEq Qid] [Encodable Qid]

def CoveredPath (path : List Act) : Prop := ∀ a ∈ path,CoveredNativeAction a

theorem covered_prefix_resource (path : List Act) (hp : CoveredPath path) (qid : Qid) (i : ℕ) :
    CoveredNativeAction (resourceAction (qid,path.take i)) := by
  have hh := @List.getLastD_mem_cons Act (path.take i) .stop
  rcases List.mem_cons.mp hh with hh | hh
  · simp only [resourceAction,hh,CoveredNativeAction]
  · exact hp _ (List.mem_of_mem_take hh)

theorem source_suffix_covered (cache : Finset (Qid × List Act)) (free : Qid → List Act → Bool)
    (qid : Qid) (path : List Act) (hp : CoveredPath path) :
    ∀ r ∈ sourceSuffix cache free qid path,CoveredNativeAction (resourceAction r) := by
  intro r hr
  obtain ⟨i,_,rfl⟩ := List.mem_map.mp (List.mem_filter.mp hr).1
  exact covered_prefix_resource path hp qid i

theorem next_unpaid_prices_congr {R : Type*} [DecidableEq R] (f g : R → ℝ) (cache : Finset R)
    (resources : List R) (hp : ∀ r ∈ resources,f r = g r) :
    nextUnpaidBill cache f resources = nextUnpaidBill cache g resources := by
  induction resources with
  | nil => rfl
  | cons r rest ih =>
      simp only [nextUnpaidBill,hp r (by simp)]
      rw [ih (fun r hr => hp r (List.mem_cons_of_mem _ hr))]

theorem source_quote_prices_congr (mode : ForecastMode) (cache : Finset (Qid × List Act))
    (free : Qid → List Act → Bool) (f g : Qid × List Act → ℝ) (qid : Qid) (path : List Act)
    (hp : ∀ r ∈ sourceSuffix cache free qid path,f r = g r) :
    sourceQidQuote mode cache free f qid path = sourceQidQuote mode cache free g qid path := by
  cases mode with
  | unpriced => rfl
  | complete =>
      change ((sourceSuffix cache free qid path).map f).sum = ((sourceSuffix cache free qid path).map g).sum
      exact congrArg List.sum (List.map_congr_left hp)
  | next =>
      change nextUnpaidBill ∅ f (sourceSuffix cache free qid path) = nextUnpaidBill ∅ g (sourceSuffix cache free qid path)
      exact next_unpaid_prices_congr f g ∅ _ hp

theorem covered_source_quotes_equal (qids : Finset Qid) (f g priors priors' caps caps' : Act → ℝ)
    (qid : Qid) (before : List (TreeEvaluation Act)) (hp : AgreeCovered f g)
    (hprior : AgreeCovered priors priors') (hc : AgreeCovered caps caps') (hh : CoveredHistory qids before)
    (mode : ForecastMode) (free : Qid → List Act → Bool) (q : Qid) (path : List Act) (hpath : CoveredPath path) :
    sourceQidQuote mode (ownPanelCache qids before) free
      (liveReceiptPrice priors caps (observedMeans qids f caps qid before)) q path =
    sourceQidQuote mode (ownPanelCache qids before) free
      (liveReceiptPrice priors' caps' (observedMeans qids g caps' qid before)) q path := by
  apply source_quote_prices_congr
  intro r hr
  exact observed_live_prices_equal qids f g priors priors' caps caps' qid before hp hprior hc hh r
    (source_suffix_covered _ free q path hpath r hr)

def observedPenalty (qids : Finset Qid) (mode : ForecastMode) (f priors caps : Act → ℝ)
    (qid : Qid) (beta Cref : ℝ) :=
  livePanelPenalty qids mode budgetTape (fun _ _ => false) priors caps (observedMeans qids f caps qid)
    (fun _ _ => 0) beta Cref

theorem observed_all_root_mc16_equal (qids : Finset Qid) (f g priors priors' caps caps' : Act → ℝ)
    (qid : Qid) (before : List (TreeEvaluation Act)) (hp : AgreeCovered f g)
    (hprior : AgreeCovered priors priors') (hc : AgreeCovered caps caps') (hh : CoveredHistory qids before)
    (mode : ForecastMode) (q : Fin 8) :
    sourcePanelMC16 qids mode (ownPanelCache qids before) (fun _ _ => false)
      (liveReceiptPrice priors caps (observedMeans qids f caps qid before))
      (budgetTape.completion before [] (.query q)) =
    sourcePanelMC16 qids mode (ownPanelCache qids before) (fun _ _ => false)
      (liveReceiptPrice priors' caps' (observedMeans qids g caps' qid before))
      (budgetTape.completion before [] (.query q)) := by
  unfold sourcePanelMC16
  apply congrArg (fun x : ℝ => x/16)
  apply Finset.sum_congr rfl
  intro i _
  unfold sourcePanelSample
  apply Finset.sum_congr rfl
  intro input _
  have hcov : CoveredPath (budgetTape.completion before [] (.query q) i) := by
    change CoveredPath (safeCompletion [.query q])
    exact root_mc_samples_covered q
  exact covered_source_quotes_equal qids f g priors priors' caps caps' qid before hp hprior hc hh
    mode (fun _ _ => false) input _ hcov

theorem observed_all_root_penalties_equal (qids : Finset Qid) (f g priors priors' caps caps' : Act → ℝ)
    (qid : Qid) (before : List (TreeEvaluation Act)) (hp : AgreeCovered f g)
    (hprior : AgreeCovered priors priors') (hc : AgreeCovered caps caps') (hh : CoveredHistory qids before)
    (mode : ForecastMode) (beta Cref : ℝ) (q : Fin 8) :
    observedPenalty qids mode f priors caps qid beta Cref before [] (.query q) =
      observedPenalty qids mode g priors' caps' qid beta Cref before [] (.query q) := by
  unfold observedPenalty livePanelPenalty livePanelForecast
  rw [observed_all_root_mc16_equal qids f g priors priors' caps caps' qid before hp hprior hc hh mode q]

end AgentUCTObservability
