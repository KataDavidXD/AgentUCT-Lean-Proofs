import PanelUnits




set_option autoImplicit false
set_option maxRecDepth 8192
set_option maxHeartbeats 3000000
noncomputable section
namespace AgentUCTNativeRepair
open AgentUCTNativeRefinement AgentUCTPaper Finset
variable {Qid : Type*} [DecidableEq Qid]

theorem homogeneous_panel_physical_bill (qids : Finset Qid) (unitPrice : List Act → ℝ)
    (events : List (TreeEvaluation Act)) :
    (replayPanel qids (fun resource => unitPrice resource.2) events).totalPaid =
      (qids.card : ℝ)*(ownState (fun resource => unitPrice resource.2) events).totalPaid := by
  rw [replay_panel_actual_bill_sum]
  have hu := replay_panel_actual_bill_sum ({()} : Finset Unit)
    (fun resource => unitPrice resource.2) events
  change (ownState (fun resource => unitPrice resource.2) events).totalPaid = _ at hu
  simp only [Finset.sum_singleton] at hu
  rw [hu]
  simp

theorem generated_homogeneous_initial_panel_bill (qids : Finset Qid)
    (reward : List Act → ℝ) (q a e b k : ℝ) :
    (replayPanel qids (fun resource => price q a e b k ((),resource.2))
      (repairedInitialization explicitTape reward)).totalPaid =
      (qids.card : ℝ)*(7*q+16*a+e) := by
  rw [homogeneous_panel_physical_bill qids (fun p => price q a e b k ((),p))
    (repairedInitialization explicitTape reward)]
  have hprice : (fun resource : Unit × List Act => price q a e b k ((),resource.2)) = price q a e b k := by
    funext resource
    rcases resource with ⟨⟨⟩,p⟩
    rfl
  rw [hprice]
  exact congrArg (fun value => (qids.card : ℝ)*value)
    (generated_common_initialization_cold_bill reward q a e b k)

theorem homogeneous_warm_depth (qids : Finset Qid) (paths : Finset (List Act))
    (qid : Qid) (hqid : qid ∈ qids) (path : List Act) :
    lastWarmDepth (qids ×ˢ paths) qid path = lastWarmDepth ({()} ×ˢ paths) () path := by
  simp [lastWarmDepth,Finset.mem_product,hqid]

theorem homogeneous_source_suffix (qids : Finset Qid) (paths : Finset (List Act))
    (freePath : List Act → Bool) (qid : Qid) (hqid : qid ∈ qids) (path : List Act) :
    sourceSuffix (qids ×ˢ paths) (fun _ p => freePath p) qid path =
      (sourceSuffix ({()} ×ˢ paths) (fun _ p => freePath p) () path).map
        (fun resource => (qid,resource.2)) := by
  have hm : ∀ indices : List ℕ,
      ((indices.map fun i => (qid,path.take i)).filter fun resource => !freePath resource.2) =
      ((indices.map fun i => ((),path.take i)).filter fun resource => !freePath resource.2).map
        (fun resource => (qid,resource.2)) := by
    intro indices
    induction indices with
    | nil => rfl
    | cons i indices ih =>
        simp only [List.map_cons,List.filter_cons]
        split_ifs <;> simp_all
  simp only [sourceSuffix,homogeneous_warm_depth qids paths qid hqid path]
  exact hm _

theorem empty_next_bill_map {R S : Type*} [DecidableEq R] [DecidableEq S]
    (f : R → S) (prices : S → ℝ) (resources : List R) :
    nextUnpaidBill ∅ prices (resources.map f) =
      nextUnpaidBill ∅ (fun resource => prices (f resource)) resources := by
  induction resources with
  | nil => rfl
  | cons r resources ih => simp [nextUnpaidBill,ih]

theorem homogeneous_source_qid_quote (qids : Finset Qid) (paths : Finset (List Act))
    (mode : ForecastMode) (freePath : List Act → Bool) (unitPrice : List Act → ℝ)
    (qid : Qid) (hqid : qid ∈ qids) (path : List Act) :
    sourceQidQuote mode (qids ×ˢ paths) (fun _ p => freePath p)
      (fun resource => unitPrice resource.2) qid path =
    sourceQidQuote mode ({()} ×ˢ paths) (fun _ p => freePath p)
      (fun resource => unitPrice resource.2) () path := by
  cases mode with
  | unpriced => rfl
  | complete =>
      simp [sourceQidQuote,homogeneous_source_suffix qids paths freePath qid hqid path,List.map_map,
        Function.comp_def]
  | next =>
      simp only [sourceQidQuote,homogeneous_source_suffix qids paths freePath qid hqid path,
        empty_next_bill_map]

theorem homogeneous_source_panel_mc16 (qids : Finset Qid) (paths : Finset (List Act))
    (mode : ForecastMode) (freePath : List Act → Bool) (unitPrice : List Act → ℝ)
    (samples : Fin 16 → List Act) :
    sourcePanelMC16 qids mode (qids ×ˢ paths) (fun _ p => freePath p)
      (fun resource => unitPrice resource.2) samples =
      (qids.card : ℝ)*sourceQidMC16 mode ({()} ×ˢ paths) (fun _ p => freePath p)
        (fun resource => unitPrice resource.2) () samples := by
  rw [mc16_panel_is_sum_of_qid_means]
  have h : ∀ qid ∈ qids,
      sourceQidMC16 mode (qids ×ˢ paths) (fun _ p => freePath p)
        (fun resource => unitPrice resource.2) qid samples =
      sourceQidMC16 mode ({()} ×ˢ paths) (fun _ p => freePath p)
        (fun resource => unitPrice resource.2) () samples := by
    intro qid hqid
    unfold sourceQidMC16
    congr 1
    exact Finset.sum_congr rfl (fun i _ => homogeneous_source_qid_quote qids paths mode freePath unitPrice qid hqid (samples i))
  rw [Finset.sum_congr rfl h]
  simp

omit [DecidableEq Qid] in
theorem panel_normalization_cancels_only_matching_reference (qids : Finset Qid)
    (beta unitForecast unitReference : ℝ) (hc : (qids.card : ℝ) ≠ 0) (hr : unitReference ≠ 0) :
    beta/((qids.card : ℝ)*unitReference)*((qids.card : ℝ)*unitForecast) =
      beta/unitReference*unitForecast := by
  field_simp

end AgentUCTNativeRepair
