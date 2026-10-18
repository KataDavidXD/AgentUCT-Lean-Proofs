import PanelSourceAllocator




set_option autoImplicit false
set_option maxRecDepth 8192
set_option maxHeartbeats 4000000
set_option linter.constructorNameAsVariable false
noncomputable section
namespace AgentUCTPanelAllocation
open AgentUCTNativeRefinement AgentUCTNativeRepair AgentUCTPaper
variable {Qid : Type*} [DecidableEq Qid]

theorem allocation_rule_prefix (c : ℝ)
    (penalty : List (TreeEvaluation Act) → List Act → Act → ℝ)
    (before events : List (TreeEvaluation Act)) (hp : before <+: events)
    (ha : TreeAllocationRule nativeTerminals c penalty events) :
    TreeAllocationRule nativeTerminals c penalty before := by
  obtain ⟨rest,rfl⟩ := hp
  intro pre event after hsplit p a hchild
  exact ha pre event (after++rest) (by rw [hsplit]; simp only [List.append_assoc,List.cons_append]) p a hchild

theorem own_panel_cache_prefix (qids : Finset Qid) (before events : List (TreeEvaluation Act))
    (hp : before <+: events) : ownPanelCache qids before ⊆ ownPanelCache qids events := by
  obtain ⟨rest,rfl⟩ := hp
  have h : ∀ es : List (TreeEvaluation Act), ∀ cache : Finset (Qid × List Act),
      cache ⊆ es.foldl (fun cache e => cache ∪ panelDemand qids e.terminal) cache := by
    intro es
    induction es with
    | nil => intro cache; exact Finset.Subset.refl _
    | cons e es ih =>
        intro cache
        exact Finset.subset_union_left.trans (ih _)
  simpa only [ownPanelCache,List.foldl_append] using h rest (ownPanelCache qids before)

theorem panel_actual_bill_prefix_monotone (qids : Finset Qid) (price : Qid × List Act → ℝ)
    (hprice : ∀ r, 0 ≤ price r) (before events : List (TreeEvaluation Act)) (hp : before <+: events) :
    panelActualBill qids price before ≤ panelActualBill qids price events := by
  simp only [panelActualBill,replay_panel_actual_bill]
  exact cacheWeight_mono price hprice (own_panel_cache_prefix qids before events hp)

theorem panel_actual_bill_nonnegative (qids : Finset Qid) (price : Qid × List Act → ℝ)
    (hprice : ∀ r, 0 ≤ price r) (events : List (TreeEvaluation Act)) :
    0 ≤ panelActualBill qids price events := by
  rw [panelActualBill,replay_panel_actual_bill]
  exact Finset.sum_nonneg (fun r _ => hprice r)

def panelReportingIndex (qids : Finset Qid) (price : Qid × List Act → ℝ)
    (events : List (TreeEvaluation Act)) (B tolerance : ℝ) : ℕ :=
  T_B (fun n => panelActualBill qids price (events.take n)) events.length B tolerance

def panelReported (qids : Finset Qid) (price : Qid × List Act → ℝ)
    (events : List (TreeEvaluation Act)) (B tolerance : ℝ) : List (TreeEvaluation Act) :=
  events.take (panelReportingIndex qids price events B tolerance)

theorem panel_reporting_index_last_complete (qids : Finset Qid) (price : Qid × List Act → ℝ)
    (events : List (TreeEvaluation Act)) (B tolerance : ℝ) (last : ℕ)
    (hlast : last ≤ events.length)
    (hfit : affordable (panelActualBill qids price (events.take last)) B tolerance)
    (hmiss : ∀ n, last < n → n ≤ events.length →
      ¬ affordable (panelActualBill qids price (events.take n)) B tolerance) :
    panelReportingIndex qids price events B tolerance = last :=
  T_B_last_complete _ _ last B tolerance hlast hfit hmiss

theorem panel_reporting_index_affordable (qids : Finset Qid) (price : Qid × List Act → ℝ)
    (events : List (TreeEvaluation Act)) (B tolerance : ℝ) (hbudget : 0 ≤ B+tolerance) :
    panelReportingIndex qids price events B tolerance ≤ events.length ∧
      affordable (panelActualBill qids price (panelReported qids price events B tolerance)) B tolerance := by
  classical
  let set := (Finset.range (events.length+1)).filter fun n =>
    affordable (panelActualBill qids price (events.take n)) B tolerance
  have hzero : 0 ∈ set := by
    simp [set,affordable,panelActualBill,replayPanel,replayMetered,emptyPanelMeter,
      MeteredTreeState.totalPaid,hbudget]
  have hnonempty : set.Nonempty := ⟨0,hzero⟩
  have hmem := Finset.sup_mem_of_nonempty (f := id) hnonempty
  obtain ⟨n,hn,heq⟩ := hmem
  have he : n = panelReportingIndex qids price events B tolerance := by
    simpa only [panelReportingIndex,T_B] using heq
  subst n
  change panelReportingIndex qids price events B tolerance ∈
    (Finset.range (events.length+1)).filter (fun n =>
      affordable (panelActualBill qids price (events.take n)) B tolerance) at hn
  have hh := Finset.mem_filter.mp hn
  exact ⟨by have hh' := Finset.mem_range.mp hh.1; omega,hh.2⟩

theorem panel_reported_allocation (qids : Finset Qid) (price : Qid × List Act → ℝ)
    (events : List (TreeEvaluation Act)) (B tolerance c : ℝ)
    (penalty : List (TreeEvaluation Act) → List Act → Act → ℝ)
    (ha : TreeAllocationRule nativeTerminals c penalty events) :
    TreeAllocationRule nativeTerminals c penalty (panelReported qids price events B tolerance) :=
  allocation_rule_prefix c penalty _ events (List.take_prefix _ _) ha

theorem panel_reported_legal_tree (qids : Finset Qid) (price : Qid × List Act → ℝ)
    (events : List (TreeEvaluation Act)) (B tolerance : ℝ)
    (hlegal : LegalTreeRun Terminal {[]} events) :
    LegalTreeRun Terminal {[]} (panelReported qids price events B tolerance) :=
  legalTreeRun_prefix Terminal _ events {[]} (List.take_prefix _ _) hlegal

theorem panel_budget_best_completed (qids : Finset Qid) (price : Qid × List Act → ℝ)
    (events : List (TreeEvaluation Act)) (B tolerance : ℝ) (best : TreeEvaluation Act)
    (hbest : bestCompleted (panelReported qids price events B tolerance) = some best) :
    best ∈ panelReported qids price events B tolerance ∧
      ∀ e ∈ panelReported qids price events B tolerance, e.reward ≤ best.reward :=
  bestCompleted_spec _ best hbest

theorem physical_target_normalization (actual B Cref : ℝ) (hc : 0 < Cref) :
    targetReached actual (B*Cref) ↔ B ≤ actual/Cref := by
  unfold targetReached
  exact (le_div_iff₀ hc).symm

theorem physical_affordability_normalization (actual B Cref tolerance : ℝ) (hc : 0 < Cref) :
    affordable actual (B*Cref) tolerance ↔ actual/Cref ≤ B+tolerance/Cref := by
  unfold affordable
  rw [div_le_iff₀ hc]
  field_simp

theorem completed_initial_target_stops (tape : SharedTape) (c : ℝ)
    (penalty : List (TreeEvaluation Act) → List Act → Act → ℝ)
    (actualBill : List (TreeEvaluation Act) → ℝ) (B : ℝ) (reward : List Act → ℝ) (cap : ℕ)
    (hstop : targetReached (actualBill (repairedInitialization tape reward)) B) :
    nativeGenerate tape c penalty actualBill B reward cap = repairedInitialization tape reward := by
  unfold nativeGenerate
  cases cap-8 <;> simp [nativeAfter,hstop]

theorem zero_tariff_actual_bill (qids : Finset Qid) (events : List (TreeEvaluation Act)) :
    panelActualBill qids (fun _ => 0) events = 0 := by
  rw [panelActualBill,replay_panel_actual_bill]
  simp [cacheWeight]

theorem zero_tariff_target_never_reached (qids : Finset Qid) (events : List (TreeEvaluation Act))
    (B : ℝ) (hb : 0 < B) : ¬ targetReached (panelActualBill qids (fun _ => 0) events) B := by
  rw [zero_tariff_actual_bill]
  exact not_le.mpr hb

theorem native_after_zero_bill_length (tape : SharedTape) (c : ℝ)
    (penalty : List (TreeEvaluation Act) → List Act → Act → ℝ) (B : ℝ) (hb : 0 < B)
    (reward : List Act → ℝ) (fuel : ℕ) (before : List (TreeEvaluation Act)) :
    (nativeAfter tape c penalty (fun _ => 0) B reward fuel before).length = before.length+fuel := by
  induction fuel generalizing before with
  | zero => rfl
  | succ fuel ih =>
      simp only [nativeAfter,targetReached,if_neg (not_le.mpr hb),ih,
        List.length_append,List.length_singleton]
      omega

theorem zero_bill_count_cap_is_not_cost_termination (tape : SharedTape) (c : ℝ)
    (penalty : List (TreeEvaluation Act) → List Act → Act → ℝ) (B : ℝ) (hb : 0 < B)
    (reward : List Act → ℝ) (cap : ℕ) (hcap : 8 ≤ cap) :
    (nativeGenerate tape c penalty (fun _ => 0) B reward cap).length = cap := by
  rw [nativeGenerate,native_after_zero_bill_length tape c penalty B hb reward,
    repaired_initialization_eight]
  omega

end AgentUCTPanelAllocation
