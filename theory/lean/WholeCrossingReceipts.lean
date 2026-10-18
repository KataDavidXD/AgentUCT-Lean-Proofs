import CompleteBudgetReporting





set_option autoImplicit false
set_option maxRecDepth 16384
set_option maxHeartbeats 4000000
noncomputable section
namespace AgentUCT32MContinuation
open AgentUCTSavedBudget AgentUCTObservability AgentUCTObservabilityBoundary AgentUCTPhysicalDiagnostic
  AgentUCTNativeBudget AgentUCTPanelAllocation AgentUCTNativeRepair AgentUCTNativeRefinement AgentUCTPaper

theorem observed_means_immutable_all_resources {Qid : Type*} [DecidableEq Qid] [Encodable Qid]
    (qids : Finset Qid) (price caps : Act → ℝ) (qid : Qid)
    (events : List (TreeEvaluation Act)) :
    ImmutableResourceReceipts (fun r => price (resourceAction r)) caps
      (observedMeans qids price caps qid events) := by
  induction events using List.reverseRecOn with
  | nil => intro i hi; simp [observedMeans,meansFromHistory,replayReceiptHistory,emptyReceiptMeans] at hi
  | append_singleton events event ih =>
      unfold observedMeans
      rw [means_from_history_append]
      apply replay_preserves_immutable_resource_receipts _ caps _ _ ih
      intro r hr
      exact (complete_rows_member_values qids _ events event r hr).2

theorem observed_means_all_resources_and_actual_bill {Qid : Type*} [DecidableEq Qid] [Encodable Qid]
    (qids : Finset Qid) (price caps : Act → ℝ) (qid : Qid)
    (events : List (TreeEvaluation Act)) :
    (observedMeans qids price caps qid events).seen = (ownPanelCache qids events).image resourceId ∧
    (observedMeans qids price caps qid events).actualPaid =
      panelActualBill qids (fun r => price (resourceAction r)) events ∧
    ∀ r ∈ ownPanelCache qids events,
      (observedMeans qids price caps qid events).resource (resourceId r) = r ∧
      (observedMeans qids price caps qid events).quotedValue (resourceId r) =
        min (price (resourceAction r)) (caps (resourceAction r)) := by
  obtain ⟨hs,hp⟩ := complete_receipt_history_seen_and_paid qids
    (fun r => price (resourceAction r)) caps qid events
  change (observedMeans qids price caps qid events).seen = _ at hs
  refine ⟨hs,hp,?_⟩
  intro r hr
  have hm : resourceId r ∈ (observedMeans qids price caps qid events).seen := by
    rw [hs]; exact Finset.mem_image.mpr ⟨r,hr,rfl⟩
  obtain ⟨hid,hval⟩ := observed_means_immutable_all_resources qids price caps qid events _ hm
  have he : (observedMeans qids price caps qid events).resource (resourceId r) = r :=
    resource_id_injective hid
  exact ⟨he,by simpa only [he] using hval⟩

theorem full_control_all_prefix_receipt_metadata_and_bill
    (Cref epsilon : ℝ) (unused : Act → Fin 8 → ℕ) (mode : ForecastMode)
    (adverse : Bool) (cap k : ℕ) (qid : Fin 150) :
    let priorHistory := (controlRun Cref savedTarget epsilon unused mode adverse cap).take k
    let means := observedMeans panel150 (completedPrice unused) (completedCaps epsilon) qid priorHistory
    means.seen = (ownPanelCache panel150 priorHistory).image resourceId ∧
      means.actualPaid = completedBill unused priorHistory ∧
      ∀ r ∈ ownPanelCache panel150 priorHistory,means.resource (resourceId r) = r ∧
        means.quotedValue (resourceId r) = min (completedPrice unused (resourceAction r))
          (completedCaps epsilon (resourceAction r)) :=
  observed_means_all_resources_and_actual_bill _ _ _ _ _

theorem panel_bill_append_equals_actual_receipt_sum {Qid : Type*} [DecidableEq Qid] [Encodable Qid]
    (qids : Finset Qid) (price : Qid × List Act → ℝ)
    (before : List (TreeEvaluation Act)) (event : TreeEvaluation Act) :
    panelActualBill qids price (before++[event]) = panelActualBill qids price before +
      ((completeRows qids price before event).map PhysicalReceipt.actual).sum := by
  rw [panel_actual_bill_append_atomic,complete_rows_actual_sum]
  rfl

theorem strict_crossing_retains_whole_raw_invoice_and_reports_previous_state
    (Cref epsilon tolerance : ℝ) (unused : Act → Fin 8 → ℕ) (mode : ForecastMode)
    (adverse : Bool) (cap : ℕ) (ht : 0 ≤ tolerance)
    (hc : savedTarget+tolerance < completedBill unused
      (controlRun Cref savedTarget epsilon unused mode adverse cap)) :
    ∃ before : List (TreeEvaluation Act),∃ crossing : TreeEvaluation Act,
      controlRun Cref savedTarget epsilon unused mode adverse cap = before++[crossing] ∧
      panelReported panel150 (fun r => completedPrice unused (resourceAction r))
        (controlRun Cref savedTarget epsilon unused mode adverse cap) savedTarget tolerance = before ∧
      completedBill unused (controlRun Cref savedTarget epsilon unused mode adverse cap) =
        completedBill unused before +
          ((completeRows panel150 (fun r => completedPrice unused (resourceAction r))
            before crossing).map PhysicalReceipt.actual).sum ∧
      0 ≤ ((completeRows panel150 (fun r => completedPrice unused (resourceAction r))
            before crossing).map PhysicalReceipt.actual).sum ∧
      ∀ qid : Fin 150,∀ r ∈ newResources panel150 before crossing,
        resourceId r ∉ (observedMeans panel150 (completedPrice unused) (completedCaps epsilon)
          qid before).seen := by
  let events := controlRun Cref savedTarget epsilon unused mode adverse cap
  have hn : events ≠ [] := by
    have hlen := full_control_run_at_least_eight Cref epsilon unused mode adverse cap
    intro hnil; change 8 ≤ events.length at hlen; rw [hnil] at hlen; simp at hlen
  let before := events.take (events.length-1)
  let crossing := events.getLast hn
  have hsplit : events = before++[crossing] := (List.take_append_getLast events hn).symm
  refine ⟨before,crossing,hsplit,?_,?_,?_,?_⟩
  · exact full_control_run_reported_prefix_before_strict_crossing
      Cref epsilon tolerance unused mode adverse cap ht hc
  · change completedBill unused events = _
    rw [hsplit]
    exact panel_bill_append_equals_actual_receipt_sum _ _ _ _
  · apply List.sum_nonneg
    intro x hx
    obtain ⟨row,hrow,rfl⟩ := List.mem_map.mp hx
    rw [(complete_rows_member_values panel150 _ before crossing row hrow).2.2]
    exact completed_physical_prices_nonnegative unused _
  · intro qid r hr hm
    have hs := (observed_means_all_resources_and_actual_bill panel150
      (completedPrice unused) (completedCaps epsilon) qid before).1
    rw [hs] at hm
    obtain ⟨s,hs,heq⟩ := Finset.mem_image.mp hm
    have he : s = r := resource_id_injective heq
    exact (Finset.mem_sdiff.mp hr).2 (he ▸ hs)

end AgentUCT32MContinuation
