import RepairHistory




set_option autoImplicit false
set_option maxRecDepth 8192
set_option maxHeartbeats 3000000
noncomputable section
namespace AgentUCTNativeRepair
open AgentUCTNativeRefinement AgentUCTPaper Finset
variable {Qid : Type*} [DecidableEq Qid]

def pathHistoryCache (events : List (TreeEvaluation Act)) : Finset (List Act) :=
  events.foldl (fun paths e => paths ∪ executionPrefixes e.terminal) ∅

def ownPanelCache (qids : Finset Qid) (events : List (TreeEvaluation Act)) : Finset (Qid × List Act) :=
  events.foldl (fun cache e => cache ∪ panelDemand qids e.terminal) ∅

theorem own_panel_cache_product (qids : Finset Qid) (events : List (TreeEvaluation Act)) :
    ownPanelCache qids events = qids ×ˢ pathHistoryCache events := by
  induction events using List.reverseRecOn with
  | nil => simp [ownPanelCache,pathHistoryCache]
  | append_singleton events e ih =>
      simp only [ownPanelCache,pathHistoryCache,List.foldl_append,List.foldl_cons,List.foldl_nil]
      change ownPanelCache qids events ∪ panelDemand qids e.terminal =
        qids ×ˢ (pathHistoryCache events ∪ executionPrefixes e.terminal)
      rw [ih]
      ext resource
      simp [panelDemand,Finset.mem_product]

def emptyPanelMeter : MeteredTreeState Qid Act := ⟨emptyStatistics,∅,0,0⟩

def replayPanel (qids : Finset Qid) (prices : Qid × List Act → ℝ)
    (events : List (TreeEvaluation Act)) : MeteredTreeState Qid Act :=
  replayMetered qids id prices (fun _ => 0) events emptyPanelMeter

theorem replay_panel_cache (qids : Finset Qid) (prices : Qid × List Act → ℝ)
    (events : List (TreeEvaluation Act)) :
    (replayPanel qids prices events).materialized = ownPanelCache qids events := by
  have h : ∀ es (s : MeteredTreeState Qid Act),
      (replayMetered qids id prices (fun _ => 0) es s).materialized =
        es.foldl (fun cache e => cache ∪ panelDemand qids e.terminal) s.materialized := by
    intro es
    induction es with
    | nil => intro s; rfl
    | cons e es ih => intro s; exact ih (meterStep qids id prices (fun _ => 0) s e)
  exact h events emptyPanelMeter

theorem replay_panel_actual_bill (qids : Finset Qid) (prices : Qid × List Act → ℝ)
    (events : List (TreeEvaluation Act)) :
    (replayPanel qids prices events).totalPaid = cacheWeight prices (ownPanelCache qids events) := by
  have h := replayMetered_total qids id prices (fun _ => 0) events (emptyPanelMeter : MeteredTreeState Qid Act)
  rw [← replay_panel_cache qids prices events]
  simpa [replayPanel,emptyPanelMeter,MeteredTreeState.totalPaid,cacheWeight] using h

theorem replay_panel_actual_bill_sum (qids : Finset Qid) (prices : Qid × List Act → ℝ)
    (events : List (TreeEvaluation Act)) :
    (replayPanel qids prices events).totalPaid =
      ∑ qid ∈ qids, ∑ p ∈ pathHistoryCache events, prices (qid,p) := by
  rw [replay_panel_actual_bill,own_panel_cache_product]
  exact Finset.sum_product _ _ _


def lastWarmDepth (cache : Finset (Qid × List Act)) (qid : Qid) (path : List Act) : ℕ :=
  ((Finset.range (path.length+1)).filter fun i => 0 < i ∧ (qid,path.take i) ∈ cache).sup id

def sourceSuffix (cache : Finset (Qid × List Act)) (free : Qid → List Act → Bool)
    (qid : Qid) (path : List Act) : List (Qid × List Act) :=
  let indices := (List.range (path.length+1)).filter fun i => lastWarmDepth cache qid path < i
  (indices.map fun i => (qid,path.take i)).filter fun resource => !free resource.1 resource.2

def sourceQidQuote (mode : ForecastMode) (cache : Finset (Qid × List Act))
    (free : Qid → List Act → Bool) (prices : Qid × List Act → ℝ) (qid : Qid) (path : List Act) : ℝ :=
  match mode with
  | .unpriced => 0
  | .complete => ((sourceSuffix cache free qid path).map prices).sum
  | .next => nextUnpaidBill ∅ prices (sourceSuffix cache free qid path)

def sourcePanelSample (qids : Finset Qid) (mode : ForecastMode)
    (cache : Finset (Qid × List Act)) (free : Qid → List Act → Bool)
    (prices : Qid × List Act → ℝ) (path : List Act) : ℝ :=
  ∑ qid ∈ qids, sourceQidQuote mode cache free prices qid path



def sourceNextLoop (prices : Qid × List Act → ℝ) : List (Qid × List Act) → ℝ
  | [] => 0
  | resource::rest => if 0 < prices resource then prices resource
      else prices resource + sourceNextLoop prices rest

theorem source_next_loop_eq_first_positive (prices : Qid × List Act → ℝ)
    (hprices : ∀ resource, 0 ≤ prices resource) (resources : List (Qid × List Act)) :
    sourceNextLoop prices resources = nextUnpaidBill ∅ prices resources := by
  induction resources with
  | nil => rfl
  | cons resource rest ih =>
      simp only [sourceNextLoop,nextUnpaidBill,Finset.not_mem_empty, false_or]
      by_cases h : 0 < prices resource
      · simp [h,not_le.mpr h]
      · have hz : prices resource = 0 := le_antisymm (le_of_not_gt h) (hprices resource)
        simp [h,hz,ih]

theorem source_quotes_nonnegative (mode : ForecastMode) (cache : Finset (Qid × List Act))
    (free : Qid → List Act → Bool) (prices : Qid × List Act → ℝ)
    (hprices : ∀ resource, 0 ≤ prices resource) (qid : Qid) (path : List Act) :
    0 ≤ sourceQidQuote mode cache free prices qid path := by
  cases mode with
  | unpriced => rfl
  | complete => exact List.sum_nonneg (fun r hr => by obtain ⟨resource,_,rfl⟩ := List.mem_map.mp hr; exact hprices resource)
  | next => exact nextUnpaidBill_nonneg ∅ prices _

def sourcePanelMC16 (qids : Finset Qid) (mode : ForecastMode)
    (cache : Finset (Qid × List Act)) (free : Qid → List Act → Bool)
    (prices : Qid × List Act → ℝ) (samples : Fin 16 → List Act) : ℝ :=
  (∑ i : Fin 16, sourcePanelSample qids mode cache free prices (samples i))/16

def sourceQidMC16 (mode : ForecastMode) (cache : Finset (Qid × List Act))
    (free : Qid → List Act → Bool) (prices : Qid × List Act → ℝ)
    (qid : Qid) (samples : Fin 16 → List Act) : ℝ :=
  (∑ i : Fin 16, sourceQidQuote mode cache free prices qid (samples i))/16

theorem mc16_panel_is_sum_of_qid_means (qids : Finset Qid) (mode : ForecastMode)
    (cache : Finset (Qid × List Act)) (free : Qid → List Act → Bool)
    (prices : Qid × List Act → ℝ) (samples : Fin 16 → List Act) :
    sourcePanelMC16 qids mode cache free prices samples =
      ∑ qid ∈ qids, sourceQidMC16 mode cache free prices qid samples := by
  simp only [sourcePanelMC16,sourcePanelSample,sourceQidMC16,Finset.sum_div]
  exact Finset.sum_comm

theorem homogeneous_panel_mc16_cardinality (qids : Finset Qid) (mode : ForecastMode)
    (cache : Finset (Qid × List Act)) (free : Qid → List Act → Bool)
    (prices : Qid × List Act → ℝ) (samples : Fin 16 → List Act) (perQid : Fin 16 → ℝ)
    (h : ∀ qid ∈ qids, ∀ i, sourceQidQuote mode cache free prices qid (samples i) = perQid i) :
    sourcePanelMC16 qids mode cache free prices samples =
      (qids.card : ℝ)*((∑ i : Fin 16, perQid i)/16) := by
  rw [mc16_panel_is_sum_of_qid_means]
  have hh : ∀ qid ∈ qids, sourceQidMC16 mode cache free prices qid samples =
      (∑ i : Fin 16, perQid i)/16 := by
    intro qid hqid
    unfold sourceQidMC16
    congr 1
    exact Finset.sum_congr rfl (fun i _ => h qid hqid i)
  rw [Finset.sum_congr rfl hh]
  simp

theorem panel_penalty_is_sum (qids : Finset Qid) (mode : ForecastMode)
    (cache : Finset (Qid × List Act)) (free : Qid → List Act → Bool)
    (prices : Qid × List Act → ℝ) (samples : Fin 16 → List Act) (beta Cref : ℝ) :
    (beta/Cref)*sourcePanelMC16 qids mode cache free prices samples =
      ∑ qid ∈ qids, (beta/Cref)*sourceQidMC16 mode cache free prices qid samples := by
  rw [mc16_panel_is_sum_of_qid_means,Finset.mul_sum]

def panelReward (qids : Finset Qid) (quality : Qid → ℝ) : ℝ :=
  (∑ qid ∈ qids, quality qid)/(qids.card : ℝ)

omit [DecidableEq Qid] in
theorem panel_reward_unit_interval (qids : Finset Qid) (quality : Qid → ℝ)
    (hne : qids.Nonempty) (h : ∀ qid ∈ qids, 0 ≤ quality qid ∧ quality qid ≤ 1) :
    0 ≤ panelReward qids quality ∧ panelReward qids quality ≤ 1 := by
  have hc : (0 : ℝ) < qids.card := by exact_mod_cast Finset.card_pos.mpr hne
  constructor
  · exact div_nonneg (Finset.sum_nonneg (fun q hq => (h q hq).1)) hc.le
  · apply (div_le_iff₀ hc).mpr
    simpa using Finset.sum_le_sum (fun q hq => (h q hq).2)

omit [DecidableEq Qid] in
theorem fixed_panel_reward_is_not_sum (qids : Finset Qid) (quality : ℝ) (hne : qids.Nonempty) :
    panelReward qids (fun _ => quality) = quality := by
  have hc : (qids.card : ℝ) ≠ 0 := by exact_mod_cast (Finset.card_ne_zero.mpr hne)
  simp [panelReward,hc]

omit [DecidableEq Qid] in


theorem aggregate_cap_guard_bound (qids : Finset Qid) (a : Qid → ℝ)
    (hcap : ∀ qid ∈ qids, 11*a qid ≤ formalAnswer6Cap) :
    formalGamma*(∑ qid ∈ qids, 12*a qid) ≤
      formalGamma*((qids.card : ℝ)*(12*(formalAnswer6Cap/11))) := by
  apply mul_le_mul_of_nonneg_left _ (by norm_num [formalGamma])
  have h : ∀ qid ∈ qids, 12*a qid ≤ 12*(formalAnswer6Cap/11) := by
    intro qid hqid
    have hh := hcap qid hqid
    linarith
  simpa using Finset.sum_le_sum h

theorem single_qid_upper_penalty_below_one :
    formalGamma*(12*(formalAnswer6Cap/11)) < 1 := by
  norm_num [formalGamma,formalAnswer6Cap]



theorem panel150_upper_penalty_above_one :
    1 < formalGamma*(150*(12*(formalAnswer6Cap/11))) := by
  norm_num [formalGamma,formalAnswer6Cap]

theorem panel150_constant_mean_maps_to_aggregate (qids : Finset Qid) (hcard : qids.card = 150)
    (mode : ForecastMode) (cache : Finset (Qid × List Act)) (free : Qid → List Act → Bool)
    (prices : Qid × List Act → ℝ) (samples : Fin 16 → List Act) (a : ℝ)
    (h : ∀ qid ∈ qids, ∀ i, sourceQidQuote mode cache free prices qid (samples i) = 12*a) :
    formalGamma*sourcePanelMC16 qids mode cache free prices samples = formalGamma*(150*(12*a)) := by
  rw [homogeneous_panel_mc16_cardinality qids mode cache free prices samples (fun _ => 12*a) h]
  simp [hcard]

end AgentUCTNativeRepair
