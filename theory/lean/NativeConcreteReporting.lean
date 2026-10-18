import NativeConcreteEndpoints
import AdverseRetainedNet
set_option autoImplicit false
noncomputable section
namespace AgentUCT32MConcrete
open AgentUCT32MContinuation AgentUCTSavedBudget AgentUCTObservability
  AgentUCTPhysicalDiagnostic AgentUCTNativeBudget AgentUCTPanelAllocation
  AgentUCTNativeRepair AgentUCTNativeRefinement AgentUCTPaper AgentUCTRealIndex
  AgentUCTNextExact

theorem favorableComplete_actual_first_crossing (cap : ℕ) (hcap : 45 ≤ cap) :
    (controlRun savedCref savedTarget uniformQuoteError unitRoleUnused .complete false cap).length = 44 ∧
    (∀ i,i < 44 → completedBill unitRoleUnused ((controlRun savedCref savedTarget uniformQuoteError unitRoleUnused .complete false cap).take i) < savedTarget) ∧
    savedTarget+1 < completedBill unitRoleUnused (controlRun savedCref savedTarget uniformQuoteError unitRoleUnused .complete false cap) := by
  rw [favorableComplete_actual_control_run cap hcap]
  exact ⟨favorableComplete_proposal_length,favorableComplete_proposal_all_proper_prefixes,favorableComplete_proposal_invoice_window.2⟩

theorem favorableComplete_actual_reporting_index (cap : ℕ) (hcap : 45 ≤ cap)
    (tolerance : ℝ) (ht : 0 ≤ tolerance) (htu : tolerance ≤ 1) :
    panelReportingIndex panel150 (fun r => completedPrice unitRoleUnused (resourceAction r))
      (controlRun savedCref savedTarget uniformQuoteError unitRoleUnused .complete false cap) savedTarget tolerance = 43 := by
  rw [favorableComplete_actual_control_run cap hcap]
  exact favorableComplete_proposal_reporting_index tolerance ht htu

theorem favorableComplete_actual_reported_prefix (cap : ℕ) (hcap : 45 ≤ cap)
    (tolerance : ℝ) (ht : 0 ≤ tolerance) (htu : tolerance ≤ 1) :
    panelReported panel150 (fun r => completedPrice unitRoleUnused (resourceAction r))
      (controlRun savedCref savedTarget uniformQuoteError unitRoleUnused .complete false cap) savedTarget tolerance = (controlRun savedCref savedTarget uniformQuoteError unitRoleUnused .complete false cap).take 43 := by
  rw [favorableComplete_actual_control_run cap hcap]
  exact favorableComplete_proposal_reported_prefix tolerance ht htu

theorem favorableComplete_actual_whole_invoice (cap : ℕ) (hcap : 45 ≤ cap) :
    completedBill unitRoleUnused (controlRun savedCref savedTarget uniformQuoteError unitRoleUnused .complete false cap) = (321718695836601/10000000:ℝ) := by
  rw [favorableComplete_actual_control_run cap hcap]
  exact favorableComplete_whole_physical_invoice

theorem favorableComplete_actual_retained_invoice (cap : ℕ) (hcap : 45 ≤ cap) :
    completedBill unitRoleUnused ((controlRun savedCref savedTarget uniformQuoteError unitRoleUnused .complete false cap).take 43) = (62692140633381/2000000:ℝ) := by
  rw [favorableComplete_actual_control_run cap hcap]
  exact favorableComplete_retained_physical_invoice

theorem favorableComplete_actual_crossing_charge (cap : ℕ) (hcap : 45 ≤ cap) :
    completedBill unitRoleUnused (controlRun savedCref savedTarget uniformQuoteError unitRoleUnused .complete false cap) - completedBill unitRoleUnused ((controlRun savedCref savedTarget uniformQuoteError unitRoleUnused .complete false cap).take 43) = (64515567732/78125:ℝ) := by
  rw [favorableComplete_actual_whole_invoice cap hcap,favorableComplete_actual_retained_invoice cap hcap]
  norm_num

theorem favorableComplete_actual_retained_quality (cap : ℕ) (hcap : 45 ≤ cap) :
    completedValue ((controlRun savedCref savedTarget uniformQuoteError unitRoleUnused .complete false cap).take 43) = (1/2:ℝ) := by
  rw [favorableComplete_actual_control_run cap hcap]
  exact favorableComplete_retained_proposal_quality

theorem favorableComplete_actual_reported_net (cap : ℕ) (hcap : 45 ≤ cap)
    (tolerance lambda : ℝ) (ht : 0 ≤ tolerance) (htu : tolerance ≤ 1) :
    observedHistoryNet panel150 (completedPrice unitRoleUnused) (controlRun savedCref savedTarget uniformQuoteError unitRoleUnused .complete false cap)
      savedTarget tolerance lambda savedCref = (1/2:ℝ)-lambda*(62692140633381/2000000:ℝ)/savedCref := by
  rw [favorableComplete_actual_control_run cap hcap]
  exact favorable_complete_observed_net_exact tolerance lambda savedCref ht htu

theorem favorableNext_actual_first_crossing (cap : ℕ) (hcap : 45 ≤ cap) :
    (controlRun savedCref savedTarget uniformQuoteError unitRoleUnused .next false cap).length = 37 ∧
    (∀ i,i < 37 → completedBill unitRoleUnused ((controlRun savedCref savedTarget uniformQuoteError unitRoleUnused .next false cap).take i) < savedTarget) ∧
    savedTarget+1 < completedBill unitRoleUnused (controlRun savedCref savedTarget uniformQuoteError unitRoleUnused .next false cap) := by
  rw [favorableNext_actual_control_run cap hcap]
  exact ⟨favorableNext_proposal_length,favorableNext_proposal_all_proper_prefixes,favorableNext_proposal_invoice_window.2⟩

theorem favorableNext_actual_reporting_index (cap : ℕ) (hcap : 45 ≤ cap)
    (tolerance : ℝ) (ht : 0 ≤ tolerance) (htu : tolerance ≤ 1) :
    panelReportingIndex panel150 (fun r => completedPrice unitRoleUnused (resourceAction r))
      (controlRun savedCref savedTarget uniformQuoteError unitRoleUnused .next false cap) savedTarget tolerance = 36 := by
  rw [favorableNext_actual_control_run cap hcap]
  exact favorableNext_proposal_reporting_index tolerance ht htu

theorem favorableNext_actual_reported_prefix (cap : ℕ) (hcap : 45 ≤ cap)
    (tolerance : ℝ) (ht : 0 ≤ tolerance) (htu : tolerance ≤ 1) :
    panelReported panel150 (fun r => completedPrice unitRoleUnused (resourceAction r))
      (controlRun savedCref savedTarget uniformQuoteError unitRoleUnused .next false cap) savedTarget tolerance = (controlRun savedCref savedTarget uniformQuoteError unitRoleUnused .next false cap).take 36 := by
  rw [favorableNext_actual_control_run cap hcap]
  exact favorableNext_proposal_reported_prefix tolerance ht htu

theorem favorableNext_actual_whole_invoice (cap : ℕ) (hcap : 45 ≤ cap) :
    completedBill unitRoleUnused (controlRun savedCref savedTarget uniformQuoteError unitRoleUnused .next false cap) = (646625512555167/20000000:ℝ) := by
  rw [favorableNext_actual_control_run cap hcap]
  exact favorableNext_whole_physical_invoice

theorem favorableNext_actual_retained_invoice (cap : ℕ) (hcap : 45 ≤ cap) :
    completedBill unitRoleUnused ((controlRun savedCref savedTarget uniformQuoteError unitRoleUnused .next false cap).take 36) = (155918255329191/5000000:ℝ) := by
  rw [favorableNext_actual_control_run cap hcap]
  exact favorableNext_retained_physical_invoice

theorem favorableNext_actual_crossing_charge (cap : ℕ) (hcap : 45 ≤ cap) :
    completedBill unitRoleUnused (controlRun savedCref savedTarget uniformQuoteError unitRoleUnused .next false cap) - completedBill unitRoleUnused ((controlRun savedCref savedTarget uniformQuoteError unitRoleUnused .next false cap).take 36) = (22952491238403/20000000:ℝ) := by
  rw [favorableNext_actual_whole_invoice cap hcap,favorableNext_actual_retained_invoice cap hcap]
  norm_num

theorem favorableNext_actual_retained_quality (cap : ℕ) (hcap : 45 ≤ cap) :
    completedValue ((controlRun savedCref savedTarget uniformQuoteError unitRoleUnused .next false cap).take 36) = (1/2:ℝ) := by
  rw [favorableNext_actual_control_run cap hcap]
  exact favorableNext_retained_proposal_quality

theorem favorableNext_actual_reported_net (cap : ℕ) (hcap : 45 ≤ cap)
    (tolerance lambda : ℝ) (ht : 0 ≤ tolerance) (htu : tolerance ≤ 1) :
    observedHistoryNet panel150 (completedPrice unitRoleUnused) (controlRun savedCref savedTarget uniformQuoteError unitRoleUnused .next false cap)
      savedTarget tolerance lambda savedCref = (1/2:ℝ)-lambda*(155918255329191/5000000:ℝ)/savedCref := by
  rw [favorableNext_actual_control_run cap hcap]
  exact favorable_next_observed_net_exact tolerance lambda savedCref ht htu

theorem adverseComplete_actual_first_crossing (cap : ℕ) (hcap : 45 ≤ cap) :
    (controlRun savedCref savedTarget uniformQuoteError unitRoleUnused .complete true cap).length = 45 ∧
    (∀ i,i < 45 → completedBill unitRoleUnused ((controlRun savedCref savedTarget uniformQuoteError unitRoleUnused .complete true cap).take i) < savedTarget) ∧
    savedTarget+1 < completedBill unitRoleUnused (controlRun savedCref savedTarget uniformQuoteError unitRoleUnused .complete true cap) := by
  rw [adverseComplete_actual_control_run cap hcap]
  exact ⟨adverseComplete_proposal_length,adverseComplete_proposal_all_proper_prefixes,adverseComplete_proposal_invoice_window.2⟩

theorem adverseComplete_actual_reporting_index (cap : ℕ) (hcap : 45 ≤ cap)
    (tolerance : ℝ) (ht : 0 ≤ tolerance) (htu : tolerance ≤ 1) :
    panelReportingIndex panel150 (fun r => completedPrice unitRoleUnused (resourceAction r))
      (controlRun savedCref savedTarget uniformQuoteError unitRoleUnused .complete true cap) savedTarget tolerance = 44 := by
  rw [adverseComplete_actual_control_run cap hcap]
  exact adverseComplete_proposal_reporting_index tolerance ht htu

theorem adverseComplete_actual_reported_prefix (cap : ℕ) (hcap : 45 ≤ cap)
    (tolerance : ℝ) (ht : 0 ≤ tolerance) (htu : tolerance ≤ 1) :
    panelReported panel150 (fun r => completedPrice unitRoleUnused (resourceAction r))
      (controlRun savedCref savedTarget uniformQuoteError unitRoleUnused .complete true cap) savedTarget tolerance = (controlRun savedCref savedTarget uniformQuoteError unitRoleUnused .complete true cap).take 44 := by
  rw [adverseComplete_actual_control_run cap hcap]
  exact adverseComplete_proposal_reported_prefix tolerance ht htu

theorem adverseComplete_actual_whole_invoice (cap : ℕ) (hcap : 45 ≤ cap) :
    completedBill unitRoleUnused (controlRun savedCref savedTarget uniformQuoteError unitRoleUnused .complete true cap) = (326759288764857/10000000:ℝ) := by
  rw [adverseComplete_actual_control_run cap hcap]
  exact adverseComplete_whole_physical_invoice

theorem adverseComplete_actual_retained_invoice (cap : ℕ) (hcap : 45 ≤ cap) :
    completedBill unitRoleUnused ((controlRun savedCref savedTarget uniformQuoteError unitRoleUnused .complete true cap).take 44) = (318501296095161/10000000:ℝ) := by
  rw [adverseComplete_actual_control_run cap hcap]
  exact adverseComplete_retained_physical_invoice

theorem adverseComplete_actual_crossing_charge (cap : ℕ) (hcap : 45 ≤ cap) :
    completedBill unitRoleUnused (controlRun savedCref savedTarget uniformQuoteError unitRoleUnused .complete true cap) - completedBill unitRoleUnused ((controlRun savedCref savedTarget uniformQuoteError unitRoleUnused .complete true cap).take 44) = (64515567732/78125:ℝ) := by
  rw [adverseComplete_actual_whole_invoice cap hcap,adverseComplete_actual_retained_invoice cap hcap]
  norm_num

theorem adverseComplete_actual_retained_quality (cap : ℕ) (hcap : 45 ≤ cap) :
    completedValue ((controlRun savedCref savedTarget uniformQuoteError unitRoleUnused .complete true cap).take 44) = (2/5:ℝ) := by
  rw [adverseComplete_actual_control_run cap hcap]
  exact adverseComplete_retained_proposal_quality

theorem adverseComplete_actual_reported_net (cap : ℕ) (hcap : 45 ≤ cap)
    (tolerance lambda : ℝ) (ht : 0 ≤ tolerance) (htu : tolerance ≤ 1) :
    observedHistoryNet panel150 (completedPrice unitRoleUnused) (controlRun savedCref savedTarget uniformQuoteError unitRoleUnused .complete true cap)
      savedTarget tolerance lambda savedCref = (2/5:ℝ)-lambda*(318501296095161/10000000:ℝ)/savedCref := by
  rw [adverseComplete_actual_control_run cap hcap]
  exact adverse_complete_observed_net_exact tolerance lambda savedCref ht htu

theorem adverseNext_actual_first_crossing (cap : ℕ) (hcap : 45 ≤ cap) :
    (controlRun savedCref savedTarget uniformQuoteError unitRoleUnused .next true cap).length = 36 ∧
    (∀ i,i < 36 → completedBill unitRoleUnused ((controlRun savedCref savedTarget uniformQuoteError unitRoleUnused .next true cap).take i) < savedTarget) ∧
    savedTarget+1 < completedBill unitRoleUnused (controlRun savedCref savedTarget uniformQuoteError unitRoleUnused .next true cap) := by
  rw [adverseNext_actual_control_run cap hcap]
  exact ⟨adverseNext_proposal_length,adverseNext_proposal_all_proper_prefixes,adverseNext_proposal_invoice_window.2⟩

theorem adverseNext_actual_reporting_index (cap : ℕ) (hcap : 45 ≤ cap)
    (tolerance : ℝ) (ht : 0 ≤ tolerance) (htu : tolerance ≤ 1) :
    panelReportingIndex panel150 (fun r => completedPrice unitRoleUnused (resourceAction r))
      (controlRun savedCref savedTarget uniformQuoteError unitRoleUnused .next true cap) savedTarget tolerance = 35 := by
  rw [adverseNext_actual_control_run cap hcap]
  exact adverseNext_proposal_reporting_index tolerance ht htu

theorem adverseNext_actual_reported_prefix (cap : ℕ) (hcap : 45 ≤ cap)
    (tolerance : ℝ) (ht : 0 ≤ tolerance) (htu : tolerance ≤ 1) :
    panelReported panel150 (fun r => completedPrice unitRoleUnused (resourceAction r))
      (controlRun savedCref savedTarget uniformQuoteError unitRoleUnused .next true cap) savedTarget tolerance = (controlRun savedCref savedTarget uniformQuoteError unitRoleUnused .next true cap).take 35 := by
  rw [adverseNext_actual_control_run cap hcap]
  exact adverseNext_proposal_reported_prefix tolerance ht htu

theorem adverseNext_actual_whole_invoice (cap : ℕ) (hcap : 45 ≤ cap) :
    completedBill unitRoleUnused (controlRun savedCref savedTarget uniformQuoteError unitRoleUnused .next true cap) = (646625512555167/20000000:ℝ) := by
  rw [adverseNext_actual_control_run cap hcap]
  exact adverseNext_whole_physical_invoice

theorem adverseNext_actual_retained_invoice (cap : ℕ) (hcap : 45 ≤ cap) :
    completedBill unitRoleUnused ((controlRun savedCref savedTarget uniformQuoteError unitRoleUnused .next true cap).take 35) = (155918255329191/5000000:ℝ) := by
  rw [adverseNext_actual_control_run cap hcap]
  exact adverseNext_retained_physical_invoice

theorem adverseNext_actual_crossing_charge (cap : ℕ) (hcap : 45 ≤ cap) :
    completedBill unitRoleUnused (controlRun savedCref savedTarget uniformQuoteError unitRoleUnused .next true cap) - completedBill unitRoleUnused ((controlRun savedCref savedTarget uniformQuoteError unitRoleUnused .next true cap).take 35) = (22952491238403/20000000:ℝ) := by
  rw [adverseNext_actual_whole_invoice cap hcap,adverseNext_actual_retained_invoice cap hcap]
  norm_num

theorem adverseNext_actual_retained_quality (cap : ℕ) (hcap : 45 ≤ cap) :
    completedValue ((controlRun savedCref savedTarget uniformQuoteError unitRoleUnused .next true cap).take 35) = (1/2:ℝ) := by
  rw [adverseNext_actual_control_run cap hcap]
  exact adverseNext_retained_proposal_quality

theorem adverseNext_actual_reported_net (cap : ℕ) (hcap : 45 ≤ cap)
    (tolerance lambda : ℝ) (ht : 0 ≤ tolerance) (htu : tolerance ≤ 1) :
    observedHistoryNet panel150 (completedPrice unitRoleUnused) (controlRun savedCref savedTarget uniformQuoteError unitRoleUnused .next true cap)
      savedTarget tolerance lambda savedCref = (1/2:ℝ)-lambda*(155918255329191/5000000:ℝ)/savedCref := by
  rw [adverseNext_actual_control_run cap hcap]
  exact adverse_next_observed_net_exact tolerance lambda savedCref ht htu

theorem favorable_actual_next_net_strictly_larger (cap : ℕ) (hcap : 45 ≤ cap)
    (tolerance : ℝ) (ht : 0 ≤ tolerance) (htu : tolerance ≤ 1) :
    observedHistoryNet panel150 (completedPrice unitRoleUnused) (controlRun savedCref savedTarget uniformQuoteError unitRoleUnused .complete false cap)
      savedTarget tolerance (1/20) savedCref <
    observedHistoryNet panel150 (completedPrice unitRoleUnused) (controlRun savedCref savedTarget uniformQuoteError unitRoleUnused .next false cap)
      savedTarget tolerance (1/20) savedCref := by
  rw [favorableComplete_actual_control_run cap hcap,favorableNext_actual_control_run cap hcap]
  exact favorable_saved32M_next_net_strictly_larger tolerance ht htu

theorem adverse_actual_next_net_strictly_larger (cap : ℕ) (hcap : 45 ≤ cap)
    (tolerance : ℝ) (ht : 0 ≤ tolerance) (htu : tolerance ≤ 1) :
    observedHistoryNet panel150 (completedPrice unitRoleUnused) (controlRun savedCref savedTarget uniformQuoteError unitRoleUnused .complete true cap)
      savedTarget tolerance (1/20) savedCref <
    observedHistoryNet panel150 (completedPrice unitRoleUnused) (controlRun savedCref savedTarget uniformQuoteError unitRoleUnused .next true cap)
      savedTarget tolerance (1/20) savedCref := by
  rw [adverseComplete_actual_control_run cap hcap,adverseNext_actual_control_run cap hcap]
  exact adverse_saved32M_next_net_strictly_larger tolerance ht htu

end AgentUCT32MConcrete
