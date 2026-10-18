import ContinuationSemigroup





set_option autoImplicit false
set_option maxRecDepth 16384
set_option maxHeartbeats 4000000
noncomputable section
attribute [local instance] Classical.propDecidable
namespace AgentUCT32MContinuation
open AgentUCTSavedBudget AgentUCTObservability AgentUCTObservabilityBoundary AgentUCTPhysicalDiagnostic
  AgentUCTNativeBudget AgentUCTPanelAllocation AgentUCTNativeRepair AgentUCTNativeRefinement AgentUCTPaper

theorem panel_reporting_index_whole_if_affordable {Qid : Type*} [DecidableEq Qid]
    (qids : Finset Qid) (price : Qid × List Act → ℝ)
    (events : List (TreeEvaluation Act)) (B tolerance : ℝ)
    (hfit : affordable (panelActualBill qids price events) B tolerance) :
    panelReportingIndex qids price events B tolerance = events.length := by
  apply panel_reporting_index_last_complete
  · exact le_rfl
  · simpa only [List.take_length] using hfit
  · intro n hn hlen; omega

theorem full_control_reporting_index_exact (Cref epsilon tolerance : ℝ)
    (unused : Act → Fin 8 → ℕ) (mode : ForecastMode) (adverse : Bool)
    (cap : ℕ) (ht : 0 ≤ tolerance) :
    panelReportingIndex panel150 (fun r => completedPrice unused (resourceAction r))
      (controlRun Cref savedTarget epsilon unused mode adverse cap) savedTarget tolerance =
      if affordable (completedBill unused (controlRun Cref savedTarget epsilon unused mode adverse cap))
          savedTarget tolerance then
        (controlRun Cref savedTarget epsilon unused mode adverse cap).length
      else (controlRun Cref savedTarget epsilon unused mode adverse cap).length-1 := by
  split_ifs with hfit
  · exact panel_reporting_index_whole_if_affordable _ _ _ _ _ hfit
  · exact full_control_run_reporting_index_before_strict_crossing
      Cref epsilon tolerance unused mode adverse cap ht (lt_of_not_ge hfit)

theorem full_control_report_exact (Cref epsilon tolerance : ℝ)
    (unused : Act → Fin 8 → ℕ) (mode : ForecastMode) (adverse : Bool)
    (cap : ℕ) (ht : 0 ≤ tolerance) :
    panelReported panel150 (fun r => completedPrice unused (resourceAction r))
      (controlRun Cref savedTarget epsilon unused mode adverse cap) savedTarget tolerance =
      if affordable (completedBill unused (controlRun Cref savedTarget epsilon unused mode adverse cap))
          savedTarget tolerance then
        controlRun Cref savedTarget epsilon unused mode adverse cap
      else (controlRun Cref savedTarget epsilon unused mode adverse cap).take
        ((controlRun Cref savedTarget epsilon unused mode adverse cap).length-1) := by
  unfold panelReported
  rw [full_control_reporting_index_exact Cref epsilon tolerance unused mode adverse cap ht]
  split_ifs <;> simp only [List.take_length]

theorem full_control_cap_below_target_reports_every_complete_evaluation
    (Cref epsilon tolerance : ℝ) (unused : Act → Fin 8 → ℕ) (mode : ForecastMode)
    (adverse : Bool) (cap : ℕ) (hcap : 8 ≤ cap) (ht : 0 ≤ tolerance)
    (hbelow : completedBill unused (controlRun Cref savedTarget epsilon unused mode adverse cap) < savedTarget) :
    (controlRun Cref savedTarget epsilon unused mode adverse cap).length = cap ∧
    panelReportingIndex panel150 (fun r => completedPrice unused (resourceAction r))
      (controlRun Cref savedTarget epsilon unused mode adverse cap) savedTarget tolerance = cap := by
  have hs := (full_control_run_is_legal_allocated_and_target_or_cap
    Cref epsilon unused mode adverse cap hcap).2.2
  have hlen : (controlRun Cref savedTarget epsilon unused mode adverse cap).length = cap := by
    rcases hs with hs | hs
    · exact hs
    · exact False.elim (not_le.mpr hbelow hs)
  refine ⟨hlen,?_⟩
  rw [panel_reporting_index_whole_if_affordable _ _ _ _ _
    (hbelow.le.trans (le_add_of_nonneg_right ht)),hlen]

theorem full_control_report_is_legal_allocated_and_affordable
    (Cref epsilon tolerance : ℝ) (unused : Act → Fin 8 → ℕ) (mode : ForecastMode)
    (adverse : Bool) (cap : ℕ) (hcap : 8 ≤ cap) (ht : 0 ≤ tolerance) :
    let reported := panelReported panel150 (fun r => completedPrice unused (resourceAction r))
      (controlRun Cref savedTarget epsilon unused mode adverse cap) savedTarget tolerance
    LegalTreeRun Terminal {[]} reported ∧
      TreeAllocationRule nativeTerminals (7/5) (controlPenalty Cref epsilon unused mode) reported ∧
      affordable (completedBill unused reported) savedTarget tolerance := by
  obtain ⟨hl,ha,hs⟩ := full_control_run_is_legal_allocated_and_target_or_cap
    Cref epsilon unused mode adverse cap hcap
  have hb : 0 ≤ savedTarget+tolerance := by dsimp only [savedTarget]; linarith
  exact ⟨panel_reported_legal_tree _ _ _ _ _ hl,
    panel_reported_allocation _ _ _ _ _ _ _ ha,
    (panel_reporting_index_affordable _ _ _ _ _ hb).2⟩

theorem constructed_eight_cap_is_not_a_32m_target_stop
    (Cref epsilon tolerance : ℝ) (unused : Act → Fin 8 → ℕ) (mode : ForecastMode)
    (adverse : Bool) (ht : 0 ≤ tolerance) :
    (controlRun Cref savedTarget epsilon unused mode adverse 8).length = 8 ∧
    ¬ targetReached (completedBill unused (controlRun Cref savedTarget epsilon unused mode adverse 8)) savedTarget ∧
    panelReportingIndex panel150 (fun r => completedPrice unused (resourceAction r))
      (controlRun Cref savedTarget epsilon unused mode adverse 8) savedTarget tolerance = 8 := by
  have heq : controlRun Cref savedTarget epsilon unused mode adverse 8 =
      initialization (taskReward adverse (2/5) (1/2)) := by
    unfold controlRun nativeGenerate
    rw [budget_common_eight_initialization]
    simp only [nativeAfter]
  have hbelow := (initial_checkpoints_below_saved_target unused
    (taskReward adverse (2/5) (1/2))).1
  rw [heq]
  refine ⟨by simp [initialization],not_le.mpr hbelow,?_⟩
  rw [panel_reporting_index_whole_if_affordable _ _ _ _ _
    (hbelow.le.trans (le_add_of_nonneg_right ht))]
  simp [initialization]

end AgentUCT32MContinuation
