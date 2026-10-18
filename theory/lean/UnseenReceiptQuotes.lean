import WholeCrossingReceipts




set_option autoImplicit false
set_option maxRecDepth 16384
set_option maxHeartbeats 6000000
noncomputable section
namespace AgentUCT32MConcrete
open AgentUCT32MContinuation AgentUCTSavedBudget AgentUCTObservability
  AgentUCTPhysicalDiagnostic AgentUCTNativeBudget AgentUCTPanelAllocation
  AgentUCTNativeRepair AgentUCTNativeRefinement AgentUCTPaper

theorem observed_seen_resource_lookup {Qid : Type*} [DecidableEq Qid] [Encodable Qid]
    (qids : Finset Qid) (price caps : Act → ℝ) (qid : Qid)
    (events : List (TreeEvaluation Act)) (i : ℕ)
    (hi : i ∈ (observedMeans qids price caps qid events).seen) :
    ∃ r ∈ ownPanelCache qids events,
      i = resourceId r ∧ (observedMeans qids price caps qid events).resource i = r := by
  obtain ⟨hs,hp,hr⟩ := observed_means_all_resources_and_actual_bill qids price caps qid events
  rw [hs] at hi
  obtain ⟨r,hrmem,he⟩ := Finset.mem_image.mp hi
  refine ⟨r,hrmem,he.symm,?_⟩
  rw [← he]
  exact (hr r hrmem).1

theorem unmaterialized_prefix_uses_action_pool {Qid : Type*} [DecidableEq Qid] [Encodable Qid]
    (qids : Finset Qid) (price caps : Act → ℝ) (qid : Qid)
    (events : List (TreeEvaluation Act)) (r : Qid × List Act)
    (hnew : ∀ q, (q,r.2) ∉ ownPanelCache qids events) :
    selectedCallPool (observedMeans qids price caps qid events) r =
      actionCallPool (observedMeans qids price caps qid events) (resourceAction r) := by
  let means := observedMeans qids price caps qid events
  have he : ¬ (exactCallPool means r).Nonempty := by
    rintro ⟨i,hi⟩
    obtain ⟨hseen,hresource⟩ := Finset.mem_filter.mp hi
    obtain ⟨s,hs,hid,hlookup⟩ := observed_seen_resource_lookup qids price caps qid events i hseen
    have hsr : s = r := hlookup.symm.trans hresource
    exact hnew r.1 (hsr ▸ hs)
  have hp : ¬ (prefixCallPool means r).Nonempty := by
    rintro ⟨i,hi⟩
    obtain ⟨hseen,hpath⟩ := Finset.mem_filter.mp hi
    obtain ⟨s,hs,hid,hlookup⟩ := observed_seen_resource_lookup qids price caps qid events i hseen
    rw [hlookup] at hpath
    exact hnew s.1 (by simpa only [← hpath] using hs)
  change selectedCallPool means r = actionCallPool means (resourceAction r)
  simp only [selectedCallPool,if_neg he,if_neg hp]

theorem equal_action_unmaterialized_prefix_prices_exact {Qid : Type*} [DecidableEq Qid] [Encodable Qid]
    (qids : Finset Qid) (price priors caps : Act → ℝ) (qid : Qid)
    (events : List (TreeEvaluation Act)) (r s : Qid × List Act)
    (hr : ∀ q, (q,r.2) ∉ ownPanelCache qids events)
    (hs : ∀ q, (q,s.2) ∉ ownPanelCache qids events)
    (ha : resourceAction r = resourceAction s) :
    liveReceiptPrice priors caps (observedMeans qids price caps qid events) r =
      liveReceiptPrice priors caps (observedMeans qids price caps qid events) s := by
  unfold liveReceiptPrice
  rw [unmaterialized_prefix_uses_action_pool qids price caps qid events r hr,
    unmaterialized_prefix_uses_action_pool qids price caps qid events s hs,ha]

end AgentUCT32MConcrete
