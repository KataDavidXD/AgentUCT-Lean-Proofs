import EndpointInvoiceBase



set_option autoImplicit false
noncomputable section
namespace AgentUCTRealIndex
open AgentUCT32MConcrete AgentUCT32MContinuation AgentUCTSavedBudget
  AgentUCTObservability AgentUCTPhysicalDiagnostic AgentUCTNativeBudget
  AgentUCTPanelAllocation AgentUCTNativeRepair AgentUCTNativeRefinement AgentUCTPaper

theorem completed_bill_take_monotone (events : List (TreeEvaluation Act))
    (k last : ℕ) (hk : k ≤ last) :
    completedBill unitRoleUnused (events.take k) ≤
      completedBill unitRoleUnused (events.take last) := by
  apply panel_actual_bill_prefix_monotone
    panel150 (fun r => completedPrice unitRoleUnused (resourceAction r))
    (fun r => completed_physical_prices_nonnegative unitRoleUnused (resourceAction r))
  exact List.take_prefix_take_left hk

theorem proposed_proper_prefixes_below_target (events : List (TreeEvaluation Act))
    (hretained : completedBill unitRoleUnused (events.take (events.length-1)) < savedTarget) :
    ∀ k,k < events.length → completedBill unitRoleUnused (events.take k) < savedTarget := by
  intro k hk
  have hkle : k ≤ events.length-1 := by omega
  exact (completed_bill_take_monotone events k (events.length-1) hkle).trans_lt hretained

theorem proposed_exact_reporting_index (events : List (TreeEvaluation Act))
    (hn : 0 < events.length) (tolerance : ℝ) (ht : 0 ≤ tolerance)
    (hretained : completedBill unitRoleUnused (events.take (events.length-1)) < savedTarget)
    (hcrossing : savedTarget+tolerance < completedBill unitRoleUnused events) :
    panelReportingIndex panel150 (fun r => completedPrice unitRoleUnused (resourceAction r))
      events savedTarget tolerance = events.length-1 := by
  apply panel_reporting_index_last_complete
  · omega
  · exact hretained.le.trans (le_add_of_nonneg_right ht)
  · intro n hlast hlen
    have he : n = events.length := by omega
    subst n
    rw [List.take_length]
    exact not_le.mpr hcrossing

theorem proposed_exact_reported_prefix (events : List (TreeEvaluation Act))
    (hn : 0 < events.length) (tolerance : ℝ) (ht : 0 ≤ tolerance)
    (hretained : completedBill unitRoleUnused (events.take (events.length-1)) < savedTarget)
    (hcrossing : savedTarget+tolerance < completedBill unitRoleUnused events) :
    panelReported panel150 (fun r => completedPrice unitRoleUnused (resourceAction r))
      events savedTarget tolerance = events.take (events.length-1) := by
  unfold panelReported
  rw [proposed_exact_reporting_index events hn tolerance ht hretained hcrossing]

end AgentUCTRealIndex
