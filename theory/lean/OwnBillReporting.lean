import ChronologicalStopping





set_option autoImplicit false
set_option maxRecDepth 16384
set_option maxHeartbeats 4000000
noncomputable section
namespace AgentUCT32MContinuation
open AgentUCTSavedBudget AgentUCTObservability AgentUCTObservabilityBoundary AgentUCTPhysicalDiagnostic
  AgentUCTNativeBudget AgentUCTPanelAllocation AgentUCTNativeRepair AgentUCTNativeRefinement AgentUCTPaper

theorem completed_physical_prices_nonnegative (unused : Act → Fin 8 → ℕ) (a : Act) :
    0 ≤ completedPrice unused a := by
  unfold completedPrice modelTokenBill
  apply Finset.sum_nonneg
  intro f hf
  exact mul_nonneg (Nat.cast_nonneg _) (field_weight_bounds f).1

theorem full_control_run_at_least_eight (Cref epsilon : ℝ)
    (unused : Act → Fin 8 → ℕ) (mode : ForecastMode) (adverse : Bool) (cap : ℕ) :
    8 ≤ (controlRun Cref savedTarget epsilon unused mode adverse cap).length := by
  unfold controlRun nativeGenerate
  rw [budget_common_eight_initialization]
  have hh := (native_after_length_bounds budgetTape (7/5) (controlPenalty Cref epsilon unused mode)
    (completedBill unused) savedTarget (taskReward adverse (2/5) (1/2)) (cap-8)
    (initialization (taskReward adverse (2/5) (1/2)))).1
  simpa only [initialization,List.length_cons,List.length_nil] using hh

theorem full_control_run_first_crossing_unconditional_prefix_accounting
    (Cref epsilon : ℝ) (unused : Act → Fin 8 → ℕ) (mode : ForecastMode)
    (adverse : Bool) (cap : ℕ) :
    ∀ k,k < (controlRun Cref savedTarget epsilon unused mode adverse cap).length →
      completedBill unused ((controlRun Cref savedTarget epsilon unused mode adverse cap).take k) < savedTarget :=
  physical_control_run_strict_proper_prefixes Cref epsilon unused mode adverse cap
    (completed_physical_prices_nonnegative unused)

theorem full_control_run_reporting_index_before_strict_crossing
    (Cref epsilon tolerance : ℝ) (unused : Act → Fin 8 → ℕ) (mode : ForecastMode)
    (adverse : Bool) (cap : ℕ) (ht : 0 ≤ tolerance)
    (hc : savedTarget+tolerance < completedBill unused (controlRun Cref savedTarget epsilon unused mode adverse cap)) :
    panelReportingIndex panel150 (fun r => completedPrice unused (resourceAction r))
      (controlRun Cref savedTarget epsilon unused mode adverse cap) savedTarget tolerance =
        (controlRun Cref savedTarget epsilon unused mode adverse cap).length-1 := by
  let events := controlRun Cref savedTarget epsilon unused mode adverse cap
  have hevents : events.length = (controlRun Cref savedTarget epsilon unused mode adverse cap).length := rfl
  have hn : 0 < events.length := by
    have hh := full_control_run_at_least_eight Cref epsilon unused mode adverse cap
    dsimp only [events]; omega
  apply panel_reporting_index_last_complete
  · omega
  · have hh := full_control_run_first_crossing_unconditional_prefix_accounting
      Cref epsilon unused mode adverse cap (events.length-1) (by omega)
    exact hh.le.trans (le_add_of_nonneg_right ht)
  · intro n hlast hlen
    have he : n = events.length := by omega
    subst n
    rw [List.take_length]
    exact not_le.mpr hc

theorem full_control_run_reported_prefix_before_strict_crossing
    (Cref epsilon tolerance : ℝ) (unused : Act → Fin 8 → ℕ) (mode : ForecastMode)
    (adverse : Bool) (cap : ℕ) (ht : 0 ≤ tolerance)
    (hc : savedTarget+tolerance < completedBill unused (controlRun Cref savedTarget epsilon unused mode adverse cap)) :
    panelReported panel150 (fun r => completedPrice unused (resourceAction r))
      (controlRun Cref savedTarget epsilon unused mode adverse cap) savedTarget tolerance =
    (controlRun Cref savedTarget epsilon unused mode adverse cap).take
      ((controlRun Cref savedTarget epsilon unused mode adverse cap).length-1) := by
  unfold panelReported
  rw [full_control_run_reporting_index_before_strict_crossing Cref epsilon tolerance unused mode adverse cap ht hc]

end AgentUCT32MContinuation
