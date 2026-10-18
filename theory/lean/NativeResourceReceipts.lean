import NativeBudgetEndpoints





set_option autoImplicit false
set_option maxRecDepth 16384
set_option maxHeartbeats 4000000
set_option linter.constructorNameAsVariable false
noncomputable section
namespace AgentUCTNativeBudget
open AgentUCTPanelAllocation AgentUCTNativeRepair AgentUCTNativeRefinement AgentUCTPaper

def actCode : Act → ℕ
  | .stop => 0 | .query q => 1+q.val | .normalRetriever r => 9+r.val
  | .hydeRetriever r => 39+r.val | .selection s => 42+s.val | .width w => 46+w.val
  | .reranker r => 50+r.val | .topm m => 52+m.val | .context c => 55+c.val | .answer a => 58+a.val

theorem act_code_injective : Function.Injective actCode := by
  intro a b h
  cases a <;> cases b <;> simp only [actCode] at h <;>
    (try congr 1) <;> (try apply Fin.ext) <;> omega

noncomputable instance nativeActEncodable : Encodable Act := Encodable.ofInj actCode act_code_injective

variable {Qid : Type*} [DecidableEq Qid] [Encodable Qid]

def resourceId (r : Qid × List Act) : ℕ := Encodable.encode r

omit [DecidableEq Qid] in
theorem resource_id_injective : Function.Injective (@resourceId Qid _ ) :=
  Encodable.encode_injective

def newResources (qids : Finset Qid) (before : List (TreeEvaluation Act))
    (event : TreeEvaluation Act) := panelDemand qids event.terminal \ ownPanelCache qids before

def resourceReceipt (price : Qid × List Act → ℝ) (r : Qid × List Act) : PhysicalReceipt Qid :=
  ⟨resourceId r,r,price r⟩

def completeRows (qids : Finset Qid) (price : Qid × List Act → ℝ)
    (before : List (TreeEvaluation Act)) (event : TreeEvaluation Act) : List (PhysicalReceipt Qid) :=
  (newResources qids before event).toList.map (resourceReceipt price)

theorem complete_rows_resource_iff (qids : Finset Qid) (price : Qid × List Act → ℝ)
    (before : List (TreeEvaluation Act)) (event : TreeEvaluation Act) (r : Qid × List Act) :
    resourceReceipt price r ∈ completeRows qids price before event ↔ r ∈ newResources qids before event := by
  constructor
  · intro h
    obtain ⟨s,hs,he⟩ := List.mem_map.mp h
    have hsr : s = r := congrArg PhysicalReceipt.resource he
    simpa [hsr] using hs
  · intro h
    exact List.mem_map.mpr ⟨r,by simpa using h,rfl⟩

theorem complete_rows_unique_ids (qids : Finset Qid) (price : Qid × List Act → ℝ)
    (before : List (TreeEvaluation Act)) (event : TreeEvaluation Act) :
    ((completeRows qids price before event).map PhysicalReceipt.callId).Nodup := by
  simpa [completeRows,resourceReceipt,List.map_map,Function.comp_def] using
    (Finset.nodup_toList (newResources qids before event)).map resource_id_injective

theorem complete_rows_ids_exact (qids : Finset Qid) (price : Qid × List Act → ℝ)
    (before : List (TreeEvaluation Act)) (event : TreeEvaluation Act) :
    ((completeRows qids price before event).map PhysicalReceipt.callId).toFinset =
      (newResources qids before event).image resourceId := by
  ext i
  simp [completeRows,resourceReceipt,List.map_map,Function.comp_def]

theorem complete_rows_actual_sum (qids : Finset Qid) (price : Qid × List Act → ℝ)
    (before : List (TreeEvaluation Act)) (event : TreeEvaluation Act) :
    ((completeRows qids price before event).map PhysicalReceipt.actual).sum =
      cacheWeight price (newResources qids before event) := by
  simp [completeRows,resourceReceipt,List.map_map,Function.comp_def,cacheWeight]

theorem complete_rows_member_values (qids : Finset Qid) (price : Qid × List Act → ℝ)
    (before : List (TreeEvaluation Act)) (event : TreeEvaluation Act) (row : PhysicalReceipt Qid)
    (hr : row ∈ completeRows qids price before event) :
    row.resource ∈ newResources qids before event ∧ row.callId = resourceId row.resource ∧ row.actual = price row.resource := by
  obtain ⟨r,hm,he⟩ := List.mem_map.mp (show row ∈
    (newResources qids before event).toList.map (resourceReceipt price) from hr)
  rw [← he]
  exact ⟨Finset.mem_toList.mp hm,rfl,rfl⟩

theorem complete_rows_fresh (qids : Finset Qid) (price : Qid × List Act → ℝ)
    (before : List (TreeEvaluation Act)) (event : TreeEvaluation Act) (s : ReceiptMeans Qid)
    (hs : s.seen = (ownPanelCache qids before).image resourceId) :
    ∀ row ∈ completeRows qids price before event,row.callId ∉ s.seen := by
  intro row hr hi
  obtain ⟨hm,hid,ha⟩ := complete_rows_member_values qids price before event row hr
  rw [hs,hid] at hi
  obtain ⟨r,hr,he⟩ := Finset.mem_image.mp hi
  have heq : r = row.resource := resource_id_injective he
  exact (Finset.mem_sdiff.mp hm).2 (heq ▸ hr)

omit [Encodable Qid] in
theorem own_panel_cache_append_one (qids : Finset Qid) (before : List (TreeEvaluation Act))
    (event : TreeEvaluation Act) :
    ownPanelCache qids (before++[event]) = ownPanelCache qids before ∪ panelDemand qids event.terminal := by
  simp [ownPanelCache,List.foldl_append]

theorem weight_union_new_resources (qids : Finset Qid) (price : Qid × List Act → ℝ)
    (before : List (TreeEvaluation Act)) (event : TreeEvaluation Act) :
    cacheWeight price (ownPanelCache qids (before++[event])) =
      cacheWeight price (ownPanelCache qids before)+cacheWeight price (newResources qids before event) := by
  have hd : Disjoint (ownPanelCache qids before) (newResources qids before event) := by
    apply Finset.disjoint_left.mpr
    intro r hr hn
    exact (Finset.mem_sdiff.mp hn).2 hr
  have hu : ownPanelCache qids (before++[event]) = ownPanelCache qids before ∪ newResources qids before event := by
    rw [own_panel_cache_append_one]
    ext r
    simp only [newResources,Finset.mem_union,Finset.mem_sdiff]
    tauto
  rw [hu]
  exact Finset.sum_union hd

theorem complete_receipt_history_seen_and_paid (qids : Finset Qid) (price : Qid × List Act → ℝ)
    (caps : Act → ℝ) (qid : Qid) (events : List (TreeEvaluation Act)) :
    (meansFromHistory caps (completeRows qids price) (emptyReceiptMeans qid) events).seen =
      (ownPanelCache qids events).image resourceId ∧
    (meansFromHistory caps (completeRows qids price) (emptyReceiptMeans qid) events).actualPaid =
      panelActualBill qids price events := by
  induction events using List.reverseRecOn with
  | nil => simp [meansFromHistory,replayReceiptHistory,emptyReceiptMeans,ownPanelCache,
      panelActualBill,replayPanel,replayMetered,emptyPanelMeter,MeteredTreeState.totalPaid]
  | append_singleton events event ih =>
      rw [means_from_history_append]
      constructor
      · rw [replay_receipts_seen,ih.1,complete_rows_ids_exact]
        rw [own_panel_cache_append_one,← Finset.image_union]
        congr 1
        ext r
        simp only [newResources,Finset.mem_union,Finset.mem_sdiff]
        tauto
      · rw [fresh_batch_actual_bill caps _ _ (complete_rows_unique_ids qids price events event)
          (complete_rows_fresh qids price events event _ ih.1),ih.2,complete_rows_actual_sum]
        simp only [panelActualBill,replay_panel_actual_bill]
        exact (weight_union_new_resources qids price events event).symm

theorem complete_receipt_rows_stationary (qids : Finset Qid) (t : TariffInput)
    (before : List (TreeEvaluation Act)) (event : TreeEvaluation Act) (row : PhysicalReceipt Qid)
    (hr : row ∈ completeRows qids (fun r => tariff t (resourceAction r)) before event) :
    row.actual = tariff t (resourceAction row.resource) :=
  (complete_rows_member_values qids _ before event row hr).2.2

end AgentUCTNativeBudget
