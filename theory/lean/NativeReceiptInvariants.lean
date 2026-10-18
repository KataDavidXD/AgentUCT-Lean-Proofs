import NativeResourceReceipts



set_option autoImplicit false
set_option maxRecDepth 16384
set_option maxHeartbeats 4000000
set_option linter.constructorNameAsVariable false
noncomputable section
namespace AgentUCTNativeBudget
open AgentUCTPanelAllocation AgentUCTNativeRepair AgentUCTNativeRefinement AgentUCTPaper
variable {Qid : Type*} [DecidableEq Qid] [Encodable Qid]

def ImmutableResourceReceipts (price : Qid × List Act → ℝ) (caps : Act → ℝ) (s : ReceiptMeans Qid) : Prop :=
  ∀ i ∈ s.seen,resourceId (s.resource i) = i ∧
    s.quotedValue i = min (price (s.resource i)) (caps (resourceAction (s.resource i)))

theorem observe_preserves_immutable_resource_receipts (price : Qid × List Act → ℝ) (caps : Act → ℝ)
    (s : ReceiptMeans Qid) (r : PhysicalReceipt Qid) (hi : ImmutableResourceReceipts price caps s)
    (hr : r.callId = resourceId r.resource ∧ r.actual = price r.resource) :
    ImmutableResourceReceipts price caps (observeReceipt caps s r) := by
  by_cases hn : r.callId ∈ s.seen
  · simpa [observeReceipt,hn] using hi
  · intro i hm
    simp only [observeReceipt,if_neg hn,Finset.mem_insert] at hm
    rcases hm with rfl | hm
    · simp only [observeReceipt,if_neg hn]
      constructor
      · simpa using hr.1.symm
      · simp [hr.2]
    · have hne : i ≠ r.callId := by intro he; subst i; exact hn hm
      simpa [observeReceipt,hn,hne] using hi i hm

theorem replay_preserves_immutable_resource_receipts (price : Qid × List Act → ℝ) (caps : Act → ℝ)
    (rows : List (PhysicalReceipt Qid)) (s : ReceiptMeans Qid) (hi : ImmutableResourceReceipts price caps s)
    (hr : ∀ r ∈ rows,r.callId = resourceId r.resource ∧ r.actual = price r.resource) :
    ImmutableResourceReceipts price caps (replayReceipts caps rows s) := by
  induction rows generalizing s with
  | nil => exact hi
  | cons r rows ih =>
      exact ih _ (observe_preserves_immutable_resource_receipts price caps s r hi (hr r (by simp)))
        (fun r hm => hr r (List.mem_cons_of_mem _ hm))

def taskMeans (qids : Finset Qid) (t : TariffInput) (caps : Act → ℝ) (qid : Qid)
    (before : List (TreeEvaluation Act)) :=
  meansFromHistory caps (completeRows qids (fun r => tariff t (resourceAction r))) (emptyReceiptMeans qid) before

theorem task_means_immutable (qids : Finset Qid) (t : TariffInput) (caps : Act → ℝ) (qid : Qid)
    (before : List (TreeEvaluation Act)) :
    ImmutableResourceReceipts (fun r => tariff t (resourceAction r)) caps (taskMeans qids t caps qid before) := by
  induction before using List.reverseRecOn with
  | nil => intro i hi; simp [taskMeans,meansFromHistory,replayReceiptHistory,emptyReceiptMeans] at hi
  | append_singleton before event ih =>
      change ImmutableResourceReceipts _ caps (meansFromHistory caps _ _ (before++[event]))
      rw [means_from_history_append]
      apply replay_preserves_immutable_resource_receipts _ caps _ _ ih
      intro r hr
      exact (complete_rows_member_values qids _ before event r hr).2

theorem task_means_full_cache_metadata_and_bill (qids : Finset Qid) (t : TariffInput)
    (caps : Act → ℝ) (qid : Qid) (before : List (TreeEvaluation Act)) :
    (taskMeans qids t caps qid before).seen = (ownPanelCache qids before).image resourceId ∧
    (taskMeans qids t caps qid before).actualPaid = physicalBill qids t before ∧
    ∀ r ∈ ownPanelCache qids before,
      (taskMeans qids t caps qid before).resource (resourceId r) = r ∧
      (taskMeans qids t caps qid before).quotedValue (resourceId r) =
        min (tariff t (resourceAction r)) (caps (resourceAction r)) := by
  obtain ⟨hs,hp⟩ := complete_receipt_history_seen_and_paid qids _ caps qid before
  change (taskMeans qids t caps qid before).seen = _ at hs
  refine ⟨hs,hp,?_⟩
  intro r hr
  have hm : resourceId r ∈ (taskMeans qids t caps qid before).seen := by
    rw [hs]; exact Finset.mem_image.mpr ⟨r,hr,rfl⟩
  obtain ⟨hid,hval⟩ := task_means_immutable qids t caps qid before _ hm
  have he : (taskMeans qids t caps qid before).resource (resourceId r) = r := resource_id_injective hid
  exact ⟨he,by simpa only [he] using hval⟩

omit [Encodable Qid] in
theorem own_panel_demand_of_completed_member (qids : Finset Qid) (events : List (TreeEvaluation Act))
    (event : TreeEvaluation Act) (he : event ∈ events) :
    panelDemand qids event.terminal ⊆ ownPanelCache qids events := by
  obtain ⟨pre,post,rfl⟩ := List.mem_iff_append.mp he
  have hs : panelDemand qids event.terminal ⊆ ownPanelCache qids (pre++[event]) := by
    rw [own_panel_cache_append_one]; exact Finset.subset_union_right
  exact hs.trans (own_panel_cache_prefix qids (pre++[event]) (pre++event::post)
    (by exact ⟨post,by simp⟩))

theorem warm10_complete_rows_empty (qids : Finset Qid) (t : TariffInput) (reward : List Act → ℝ) :
    completeRows qids (fun r => tariff t (resourceAction r)) (aNine reward) (aWarmEvent reward) = [] := by
  have hm : seedEvent reward hyde ∈ aNine reward := by
    simp [aNine,initialization]
  have hs := own_panel_demand_of_completed_member qids (aNine reward) (seedEvent reward hyde) hm
  have he : newResources qids (aNine reward) (aWarmEvent reward) = ∅ :=
    Finset.sdiff_eq_empty_iff_subset.mpr hs
  simp [completeRows,he]

theorem warm10_means_unchanged (qids : Finset Qid) (t : TariffInput) (caps : Act → ℝ)
    (qid : Qid) (reward : List Act → ℝ) :
    taskMeans qids t caps qid (aTen reward) = taskMeans qids t caps qid (aNine reward) := by
  unfold taskMeans aTen
  rw [means_from_history_append,warm10_complete_rows_empty]
  rfl

theorem task_means_observed_zero_error (qids : Finset Qid) (t : TariffInput) (caps : Act → ℝ)
    (qid : Qid) (hc : ∀ a,tariff t a ≤ caps a) (before : List (TreeEvaluation Act)) :
    ReceiptPriceError (tariff t) 0 (taskMeans qids t caps qid before) :=
  causal_receipts_propagate_initial_error (tariff t) caps 0 _ _ (by norm_num) hc
    (empty_receipt_means_has_zero_error _ 0 qid) (complete_receipt_rows_stationary qids t) before

theorem task_live_price_error_from_initial_priors (qids : Finset Qid) (t : TariffInput)
    (priors caps : Act → ℝ) (qid : Qid) (epsilon : ℝ) (he : 0 ≤ epsilon)
    (hc : ∀ a,tariff t a ≤ caps a) (hp : ∀ a,|min (caps a) (priors a)-tariff t a| ≤ epsilon)
    (before : List (TreeEvaluation Act)) (r : Qid × List Act) :
    |liveReceiptPrice priors caps (taskMeans qids t caps qid before) r-tariff t (resourceAction r)| ≤ epsilon :=
  causal_live_price_error_from_initial_state priors caps (tariff t) epsilon _ _ he hc hp
    (empty_receipt_means_has_zero_error _ epsilon qid) (complete_receipt_rows_stationary qids t) before r

theorem task_live_zero_action_exact (qids : Finset Qid) (t : TariffInput)
    (priors caps : Act → ℝ) (qid : Qid) (hc : ∀ a,tariff t a ≤ caps a)
    (hp : ∀ a,tariff t a = 0 → min (caps a) (priors a) = 0)
    (before : List (TreeEvaluation Act)) (r : Qid × List Act) (hz : tariff t (resourceAction r) = 0) :
    liveReceiptPrice priors caps (taskMeans qids t caps qid before) r = 0 := by
  have hr := task_means_observed_zero_error qids t caps qid hc before
  have hh : |liveReceiptPrice priors caps (taskMeans qids t caps qid before) r-0| ≤ 0 := by
    apply online_mean_absolute_error
    · simp [hp _ hz]
    · intro i hi
      obtain ⟨hseen,ha⟩ := selected_call_pool_valid _ r i hi
      simpa only [ha,hz] using hr i hseen
  exact by simpa using abs_nonpos_iff.mp hh

end AgentUCTNativeBudget
