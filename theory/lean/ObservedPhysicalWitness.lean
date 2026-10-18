import ObservedBudgetTrajectories
import NativeInvoiceCompletion






set_option autoImplicit false
set_option maxRecDepth 16384
set_option maxHeartbeats 4000000
set_option linter.constructorNameAsVariable false
noncomputable section
namespace AgentUCTObservability
open AgentUCTPhysicalDiagnostic AgentUCTNativeBudget AgentUCTPanelAllocation
  AgentUCTNativeRepair AgentUCTNativeRefinement AgentUCTPaper

def completedPriors (epsilon : ℝ) (unused : Act → Fin 8 → ℕ) (a : Act) : ℝ :=
  if CoveredNativeAction a then perturbedPriors integerTariffs epsilon a else completedPrice unused a

def completedCaps (epsilon : ℝ) (a : Act) : ℝ :=
  if CoveredNativeAction a then perturbedCaps integerTariffs epsilon a else fullStaticCap a

theorem completed_initial_prices_agree (epsilon : ℝ) (unused : Act → Fin 8 → ℕ) :
    AgreeCovered (perturbedPriors integerTariffs epsilon) (completedPriors epsilon unused) ∧
    AgreeCovered (perturbedCaps integerTariffs epsilon) (completedCaps epsilon) := by
  constructor <;> intro a ha <;> simp [completedPriors,completedCaps,ha]

def completedRun (epsilon : ℝ) (unused : Act → Fin 8 → ℕ) (mode : ForecastMode) (adverse : Bool) (cap : ℕ) :=
  observedRun panel150 mode (completedPrice unused) (completedPriors epsilon unused) (completedCaps epsilon)
    0 adverse (2/5) (1/2) (7/5) 2 (classCref panel150 integerTariffs) (taskBudget panel150 integerTariffs) cap

def completedNet (epsilon : ℝ) (unused : Act → Fin 8 → ℕ) (mode : ForecastMode) (adverse : Bool) (cap : ℕ) :=
  observedHistoryNet panel150 (completedPrice unused) (completedRun epsilon unused mode adverse cap)
    (taskBudget panel150 integerTariffs) (1/10000000) (1/20) (classCref panel150 integerTariffs)

def completedReferenceCref (unused : Act → Fin 8 → ℕ) : ℝ :=
  (panel150.card : ℝ)*medianThree
    (∑ r ∈ demand (AgentUCTNativeBudget.referencePath 0),completedPrice unused (resourceAction r))
    (∑ r ∈ demand (AgentUCTNativeBudget.referencePath 1),completedPrice unused (resourceAction r))
    (∑ r ∈ demand (AgentUCTNativeBudget.referencePath 2),completedPrice unused (resourceAction r))

theorem reference_resource_footprint_covered (i : Fin 3) :
    ∀ r ∈ demand (AgentUCTNativeBudget.referencePath i),CoveredNativeAction (resourceAction r) := by
  fin_cases i <;> decide

theorem completed_reference_actual_statistic (unused : Act → Fin 8 → ℕ) :
    completedReferenceCref unused = classCref panel150 integerTariffs := by
  have hb (i : Fin 3) : (∑ r ∈ demand (AgentUCTNativeBudget.referencePath i),completedPrice unused (resourceAction r)) =
      referenceColdBill integerTariffs i := by
    simp only [referenceColdBill,coldWork,Finset.sdiff_empty,cacheWeight,pathTariff]
    apply Finset.sum_congr rfl
    intro r hr
    exact (completed_price_agrees_on_all_observed_actions unused _ (reference_resource_footprint_covered i r hr)).symm
  simp only [completedReferenceCref,classCref,calibrationMedian,hb]

theorem completed_reference_differs_saved_configuration (unused : Act → Fin 8 → ℕ) :
    completedReferenceCref unused ≠ (1470690.0198555747 : ℝ) := by
  rw [completed_reference_actual_statistic]
  exact independent_cref_differs_saved_decimal

theorem completed_whole_history_prefix_observations (epsilon : ℝ) (unused : Act → Fin 8 → ℕ)
    (events : List (TreeEvaluation Act)) (hh : CoveredHistory panel150 events) (n : ℕ) :
    observedMeans panel150 (completedPrice unused) (completedCaps epsilon) 0 (events.take n) =
      taskMeans panel150 integerTariffs (perturbedCaps integerTariffs epsilon) 0 (events.take n) ∧
    panelActualBill panel150 (fun r => completedPrice unused (resourceAction r)) (events.take n) =
      physicalBill panel150 integerTariffs (events.take n) ∧
    (∀ mode : ForecastMode,∀ q : Fin 8,
      observedPenalty panel150 mode (completedPrice unused) (completedPriors epsilon unused) (completedCaps epsilon)
        0 2 (completedReferenceCref unused) (events.take n) [] (.query q) =
      causalPenalty panel150 mode integerTariffs (perturbedPriors integerTariffs epsilon)
        (perturbedCaps integerTariffs epsilon) 0 2 (classCref panel150 integerTariffs) (events.take n) [] (.query q)) := by
  have hprefix : CoveredHistory panel150 (events.take n) := covered_history_prefix panel150 (events.take n) events (List.take_prefix n events) hh
  have hinit := completed_initial_prices_agree epsilon unused
  have he := completed_price_agrees_on_all_observed_actions unused
  refine ⟨?_,?_,?_⟩
  · exact (observed_means_equal panel150 (tariff integerTariffs) (completedPrice unused)
      _ _ 0 _ he hinit.2 hprefix).symm
  · exact (observed_actual_bills_equal panel150 (tariff integerTariffs) (completedPrice unused) _ he hprefix).symm
  · intro mode q
    rw [completed_reference_actual_statistic]
    exact (observed_all_root_penalties_equal panel150 (tariff integerTariffs) (completedPrice unused)
      _ _ _ _ 0 _ he hinit.1 hinit.2 hprefix mode 2 _ q).symm

theorem completed_actual_reporting_indices (unused : Act → Fin 8 → ℕ) (reward : List Act → ℝ) :
    panelReportingIndex panel150 (fun r => completedPrice unused (resourceAction r))
      (aEleven reward) (taskBudget panel150 integerTariffs) (1/10000000) = 10 ∧
    panelReportingIndex panel150 (fun r => completedPrice unused (resourceAction r))
      (bTen reward) (taskBudget panel150 integerTariffs) (1/10000000) = 9 := by
  have hw : StrictResourceWindow (panel150.card : ℝ) integerTariffs (1/10000000) := by
    rw [AgentUCTNativeBudget.panel150_cardinality]; exact beta2_resource_window
  have he := completed_price_agrees_on_all_observed_actions unused
  have hh := companion_panel_caches_covered panel150 reward
  constructor
  · rw [← observed_reporting_index_equal panel150 (tariff integerTariffs) (completedPrice unused) _ _ _ he hh.1]
    exact resource_a_TB10 panel150 integerTariffs reward (1/10000000) hw
  · rw [← observed_reporting_index_equal panel150 (tariff integerTariffs) (completedPrice unused) _ _ _ he hh.2]
    exact resource_b_TB9 panel150 integerTariffs reward (1/10000000) hw

theorem completed_raw_and_retained_bills (unused : Act → Fin 8 → ℕ) (reward : List Act → ℝ) :
    panelActualBill panel150 (fun r => completedPrice unused (resourceAction r)) (aEleven reward) =
      (150:ℝ)*(baseBill integerTariffs+integerTariffs.bge+tailBill integerTariffs+crossBill integerTariffs) ∧
    panelActualBill panel150 (fun r => completedPrice unused (resourceAction r)) (bTen reward) =
      (150:ℝ)*(baseBill integerTariffs+integerTariffs.normalE5+2*tailBill integerTariffs+integerTariffs.bge) ∧
    panelActualBill panel150 (fun r => completedPrice unused (resourceAction r)) (aTen reward) =
      (150:ℝ)*(baseBill integerTariffs+integerTariffs.bge+tailBill integerTariffs) ∧
    panelActualBill panel150 (fun r => completedPrice unused (resourceAction r)) (bNine reward) =
      (150:ℝ)*(baseBill integerTariffs+integerTariffs.normalE5+tailBill integerTariffs) := by
  have he := completed_price_agrees_on_all_observed_actions unused
  have hh := companion_panel_caches_covered panel150 reward
  have hbill (es : List (TreeEvaluation Act)) (hs : CoveredHistory panel150 es) :
      panelActualBill panel150 (fun r => completedPrice unused (resourceAction r)) es = physicalBill panel150 integerTariffs es :=
    (observed_actual_bills_equal panel150 (tariff integerTariffs) (completedPrice unused) es he hs).symm
  rw [hbill _ hh.1,hbill _ hh.2,
    hbill _ (checkpoint_covered panel150 reward _ (Or.inr (Or.inr (Or.inl rfl)))),
    hbill _ (checkpoint_covered panel150 reward _ (Or.inr (Or.inr (Or.inr rfl)))),
    physical_a11_bill,physical_b10_bill,physical_a10_bill,physical_b9_bill,AgentUCTNativeBudget.panel150_cardinality]
  norm_num

theorem completed_source_tree_allocation (epsilon : ℝ) (unused : Act → Fin 8 → ℕ)
    (mode : ForecastMode) (adverse : Bool) (cap : ℕ) :
    LegalTreeRun Terminal {[]} (completedRun epsilon unused mode adverse cap) ∧
    TreeAllocationRule nativeTerminals (7/5)
      (observedPenalty panel150 mode (completedPrice unused) (completedPriors epsilon unused) (completedCaps epsilon)
        0 2 (classCref panel150 integerTariffs)) (completedRun epsilon unused mode adverse cap) :=
  ⟨native_generated_legal_tree budgetTape budget_tape_supported (7/5) _ _ _ _ cap,
   native_generated_tree_allocation_rule budgetTape budget_tape_supported (7/5) _ _ _ _ cap⟩

theorem beta2_all_unused_completions_full_trajectories (cap : ℕ) (hcap : 11 ≤ cap) :
    ∃ epsilon : ℝ,0 < epsilon ∧
      ∀ unused : Act → Fin 8 → ℕ,StaticUnusedInvoices unused →
        (∀ adverse : Bool,
          completedRun epsilon unused .complete adverse cap = aEleven (taskReward adverse (2/5) (1/2)) ∧
          completedRun epsilon unused .next adverse cap = bTen (taskReward adverse (2/5) (1/2))) ∧
        completedNet epsilon unused .next false cap < completedNet epsilon unused .complete false cap ∧
        completedNet epsilon unused .complete true cap < completedNet epsilon unused .next true cap := by
  obtain ⟨epsilon,he,hp,hm⟩ := beta2_causal_error_inputs_inhabited
  have hs : 0 ≤ (2:ℝ)/classCref panel150 integerTariffs := by rw [panel150_integer_cref]; norm_num [generatorRate]
  have hr : RootMargins integerTariffs (7/5) (penaltyScale panel150 2 (classCref panel150 integerTariffs)) (2/5) (1/2) := by
    rw [beta2_integer_penalty_scale]; exact beta2_root_margins
  have herr : ErrorMargins integerTariffs (7/5) (penaltyScale panel150 2 (classCref panel150 integerTariffs)) (2/5) (1/2)
      (10*(penaltyScale panel150 2 (classCref panel150 integerTariffs))*epsilon) := by
    simpa only [beta2_integer_penalty_scale] using hm
  have hw : StrictResourceWindow (panel150.card : ℝ) integerTariffs (1/10000000) := by
    rw [AgentUCTNativeBudget.panel150_cardinality]; exact beta2_resource_window
  have href := causal_positive_and_adverse_separation_same_controls panel150 integerTariffs
    _ _ (0 : Fin 150) (2/5) (1/2) (7/5) 2 _ epsilon (1/10000000) (1/20) cap hcap hs hp hr herr hw
    integer_tariffs_nonnegative beta2_retained_gap_bracket
  have hgenref (adverse : Bool) := causal_both_task_histories_generated panel150 integerTariffs
    _ _ (0 : Fin 150) adverse (2/5) (1/2) (7/5) 2 _ epsilon (1/10000000) cap hcap hs hp hr herr hw integer_tariffs_nonnegative
  refine ⟨epsilon,he,?_⟩
  intro unused hu
  have hagree := completed_price_agrees_on_all_observed_actions unused
  have hinit := completed_initial_prices_agree epsilon unused
  have hgen (adverse : Bool) := observed_both_full_histories_generated panel150 integerTariffs
    (completedPrice unused) _ _ _ _ (0 : Fin 150) adverse (2/5) (1/2) (7/5) 2 _ epsilon (1/10000000)
    cap hcap hs hp hr herr hw integer_tariffs_nonnegative hagree hinit.1 hinit.2
  have hnet (mode : ForecastMode) (adverse : Bool) (hm : mode = .complete ∨ mode = .next) :
      completedNet epsilon unused mode adverse cap = diagnosticNet epsilon mode adverse cap := by
    rcases hm with rfl | rfl
    · unfold completedNet completedRun diagnosticNet causalRetainedNet causalRetained
      rw [(hgen adverse).1,(hgenref adverse).1]
      exact (observed_history_net_equal panel150 (tariff integerTariffs) (completedPrice unused)
        _ _ _ _ _ hagree (companion_panel_caches_covered panel150 _).1).symm
    · unfold completedNet completedRun diagnosticNet causalRetainedNet causalRetained
      rw [(hgen adverse).2,(hgenref adverse).2]
      exact (observed_history_net_equal panel150 (tariff integerTariffs) (completedPrice unused)
        _ _ _ _ _ hagree (companion_panel_caches_covered panel150 _).2).symm
  refine ⟨hgen,?_,?_⟩
  · rw [hnet .next false (Or.inr rfl),hnet .complete false (Or.inl rfl)]
    exact href.1
  · rw [hnet .complete true (Or.inl rfl),hnet .next true (Or.inr rfl)]
    exact href.2

theorem complete_native_role_conditional_family_inhabited (cap : ℕ) (hcap : 11 ≤ cap) :
    ∃ epsilon : ℝ,0 < epsilon ∧ StaticUnusedInvoices unitRoleUnused ∧
      (∀ a f,completedCounts unitRoleUnused a f ≠ 0 → f ∈ fullRoleFields a) ∧
      (∀ a,completedPrice unitRoleUnused a ≤ fullStaticCap a) ∧
      (∀ adverse : Bool,
        completedRun epsilon unitRoleUnused .complete adverse cap = aEleven (taskReward adverse (2/5) (1/2)) ∧
        completedRun epsilon unitRoleUnused .next adverse cap = bTen (taskReward adverse (2/5) (1/2))) ∧
      completedNet epsilon unitRoleUnused .next false cap < completedNet epsilon unitRoleUnused .complete false cap ∧
      completedNet epsilon unitRoleUnused .complete true cap < completedNet epsilon unitRoleUnused .next true cap := by
  obtain ⟨epsilon,he,hfamily⟩ := beta2_all_unused_completions_full_trajectories cap hcap
  obtain ⟨hgen,hpos,hadverse⟩ := hfamily unitRoleUnused unit_role_unused_is_feasible
  exact ⟨epsilon,he,unit_role_unused_is_feasible,
    completed_invoices_all_native_roles _ unit_role_unused_is_feasible,
    completed_invoices_all_static_caps _ unit_role_unused_is_feasible,hgen,hpos,hadverse⟩

end AgentUCTObservability
