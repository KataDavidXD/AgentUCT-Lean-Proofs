import InvoiceFootprint



set_option autoImplicit false
set_option maxRecDepth 16384
set_option maxHeartbeats 4000000
noncomputable section
namespace AgentUCTObservability
open AgentUCTPhysicalDiagnostic AgentUCTNativeBudget AgentUCTPanelAllocation
  AgentUCTNativeRepair AgentUCTNativeRefinement AgentUCTPaper
variable {Qid : Type*} [DecidableEq Qid] [Encodable Qid]

def CoveredHistory (qids : Finset Qid) (events : List (TreeEvaluation Act)) : Prop :=
  ∀ r ∈ ownPanelCache qids events,CoveredNativeAction (resourceAction r)

def AgreeCovered (f g : Act → ℝ) : Prop :=
  ∀ a,CoveredNativeAction a → f a = g a

def observedMeans (qids : Finset Qid) (price caps : Act → ℝ) (qid : Qid)
    (events : List (TreeEvaluation Act)) : ReceiptMeans Qid :=
  meansFromHistory caps (completeRows qids (fun r => price (resourceAction r))) (emptyReceiptMeans qid) events

theorem covered_history_prefix (qids : Finset Qid) (before after : List (TreeEvaluation Act))
    (hp : before <+: after) (ha : CoveredHistory qids after) : CoveredHistory qids before := by
  intro r hr
  exact ha r (own_panel_cache_prefix qids before after hp hr)

theorem complete_rows_equal_on_new (qids : Finset Qid) (f g : Act → ℝ)
    (before : List (TreeEvaluation Act)) (event : TreeEvaluation Act)
    (he : ∀ r ∈ newResources qids before event,f (resourceAction r) = g (resourceAction r)) :
    completeRows qids (fun r => f (resourceAction r)) before event =
      completeRows qids (fun r => g (resourceAction r)) before event := by
  unfold completeRows
  apply List.map_congr_left
  intro r hr
  simp only [resourceReceipt]
  rw [he r (Finset.mem_toList.mp hr)]

theorem replay_receipts_cap_congruence (caps caps' : Act → ℝ)
    (rows : List (PhysicalReceipt Qid)) (s : ReceiptMeans Qid)
    (hc : ∀ row ∈ rows,caps (resourceAction row.resource) = caps' (resourceAction row.resource)) :
    replayReceipts caps rows s = replayReceipts caps' rows s := by
  induction rows generalizing s with
  | nil => rfl
  | cons row rows ih =>
      have he : observeReceipt caps s row = observeReceipt caps' s row := by
        simp only [observeReceipt,hc row (by simp)]
      simp only [replayReceipts,List.foldl_cons]
      rw [he]
      exact ih _ (fun r hr => hc r (List.mem_cons_of_mem _ hr))

theorem observed_means_equal (qids : Finset Qid) (f g caps caps' : Act → ℝ) (qid : Qid)
    (events : List (TreeEvaluation Act)) (hp : AgreeCovered f g) (hc : AgreeCovered caps caps')
    (hh : CoveredHistory qids events) :
    observedMeans qids f caps qid events = observedMeans qids g caps' qid events := by
  induction events using List.reverseRecOn with
  | nil => rfl
  | append_singleton events event ih =>
      have hb := covered_history_prefix qids events (events++[event]) (List.prefix_append _ _) hh
      have hn : ∀ r ∈ newResources qids events event,CoveredNativeAction (resourceAction r) := by
        intro r hr
        apply hh r
        rw [own_panel_cache_append_one]
        exact Finset.mem_union_right _ (Finset.mem_sdiff.mp hr).1
      unfold observedMeans
      rw [means_from_history_append,means_from_history_append,
        complete_rows_equal_on_new qids f g events event (fun r hr => hp _ (hn r hr))]
      change replayReceipts caps _ (observedMeans qids f caps qid events) =
        replayReceipts caps' _ (observedMeans qids g caps' qid events)
      rw [ih hb]
      apply replay_receipts_cap_congruence
      intro row hr
      obtain ⟨hm,_,_⟩ := complete_rows_member_values qids _ events event row hr
      exact hc _ (hn row.resource hm)

theorem observed_live_prices_equal (qids : Finset Qid) (f g priors priors' caps caps' : Act → ℝ)
    (qid : Qid) (events : List (TreeEvaluation Act)) (hp : AgreeCovered f g)
    (hprior : AgreeCovered priors priors') (hc : AgreeCovered caps caps')
    (hh : CoveredHistory qids events) (r : Qid × List Act) (hr : CoveredNativeAction (resourceAction r)) :
    liveReceiptPrice priors caps (observedMeans qids f caps qid events) r =
      liveReceiptPrice priors' caps' (observedMeans qids g caps' qid events) r := by
  rw [observed_means_equal qids f g caps caps' qid events hp hc hh]
  simp only [liveReceiptPrice,hprior _ hr,hc _ hr]

theorem observed_actual_bills_equal (qids : Finset Qid) (f g : Act → ℝ)
    (events : List (TreeEvaluation Act)) (hp : AgreeCovered f g) (hh : CoveredHistory qids events) :
    panelActualBill qids (fun r => f (resourceAction r)) events =
      panelActualBill qids (fun r => g (resourceAction r)) events := by
  simp only [panelActualBill,replay_panel_actual_bill]
  apply Finset.sum_congr rfl
  intro r hr
  exact hp _ (hh r hr)

end AgentUCTObservability
