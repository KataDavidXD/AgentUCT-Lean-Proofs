import EndpointInvoiceProposals
import EndpointBudgetBase

set_option autoImplicit false
noncomputable section
namespace AgentUCTRealIndex
open AgentUCT32MConcrete AgentUCT32MContinuation AgentUCTSavedBudget
  AgentUCTObservability AgentUCTPhysicalDiagnostic AgentUCTNativeBudget
  AgentUCTPanelAllocation AgentUCTNativeRepair AgentUCTNativeRefinement AgentUCTPaper




theorem favorableComplete_proposal_length : favorableCompleteProposal.length = 44 := by rfl

theorem favorableComplete_proposal_invoice_window :
    completedBill unitRoleUnused (favorableCompleteProposal.take 43) < savedTarget ∧
      savedTarget+1 < completedBill unitRoleUnused favorableCompleteProposal := by
  rw [favorableComplete_retained_physical_invoice,favorableComplete_whole_physical_invoice]
  norm_num [savedTarget]

theorem favorableComplete_proposal_all_proper_prefixes :
    ∀ k,k < 44 → completedBill unitRoleUnused (favorableCompleteProposal.take k) < savedTarget := by
  have hr : completedBill unitRoleUnused (favorableCompleteProposal.take (favorableCompleteProposal.length-1)) < savedTarget := by
    simpa only [favorableComplete_proposal_length] using favorableComplete_proposal_invoice_window.1
  simpa only [favorableComplete_proposal_length] using proposed_proper_prefixes_below_target favorableCompleteProposal hr

theorem favorableComplete_proposal_reporting_index (tolerance : ℝ)
    (ht : 0 ≤ tolerance) (htu : tolerance ≤ 1) :
    panelReportingIndex panel150 (fun r => completedPrice unitRoleUnused (resourceAction r))
      favorableCompleteProposal savedTarget tolerance = 43 := by
  have hn : 0 < favorableCompleteProposal.length := by rw [favorableComplete_proposal_length]; omega
  have hr : completedBill unitRoleUnused (favorableCompleteProposal.take (favorableCompleteProposal.length-1)) < savedTarget := by
    simpa only [favorableComplete_proposal_length] using favorableComplete_proposal_invoice_window.1
  have hc : savedTarget+tolerance < completedBill unitRoleUnused favorableCompleteProposal := by
    have hw := favorableComplete_proposal_invoice_window.2
    linarith
  simpa only [favorableComplete_proposal_length] using proposed_exact_reporting_index favorableCompleteProposal hn tolerance ht hr hc

theorem favorableComplete_proposal_reported_prefix (tolerance : ℝ)
    (ht : 0 ≤ tolerance) (htu : tolerance ≤ 1) :
    panelReported panel150 (fun r => completedPrice unitRoleUnused (resourceAction r))
      favorableCompleteProposal savedTarget tolerance = favorableCompleteProposal.take 43 := by
  unfold panelReported
  rw [favorableComplete_proposal_reporting_index tolerance ht htu]

theorem favorableNext_proposal_length : favorableNextProposal.length = 37 := by rfl

theorem favorableNext_proposal_invoice_window :
    completedBill unitRoleUnused (favorableNextProposal.take 36) < savedTarget ∧
      savedTarget+1 < completedBill unitRoleUnused favorableNextProposal := by
  rw [favorableNext_retained_physical_invoice,favorableNext_whole_physical_invoice]
  norm_num [savedTarget]

theorem favorableNext_proposal_all_proper_prefixes :
    ∀ k,k < 37 → completedBill unitRoleUnused (favorableNextProposal.take k) < savedTarget := by
  have hr : completedBill unitRoleUnused (favorableNextProposal.take (favorableNextProposal.length-1)) < savedTarget := by
    simpa only [favorableNext_proposal_length] using favorableNext_proposal_invoice_window.1
  simpa only [favorableNext_proposal_length] using proposed_proper_prefixes_below_target favorableNextProposal hr

theorem favorableNext_proposal_reporting_index (tolerance : ℝ)
    (ht : 0 ≤ tolerance) (htu : tolerance ≤ 1) :
    panelReportingIndex panel150 (fun r => completedPrice unitRoleUnused (resourceAction r))
      favorableNextProposal savedTarget tolerance = 36 := by
  have hn : 0 < favorableNextProposal.length := by rw [favorableNext_proposal_length]; omega
  have hr : completedBill unitRoleUnused (favorableNextProposal.take (favorableNextProposal.length-1)) < savedTarget := by
    simpa only [favorableNext_proposal_length] using favorableNext_proposal_invoice_window.1
  have hc : savedTarget+tolerance < completedBill unitRoleUnused favorableNextProposal := by
    have hw := favorableNext_proposal_invoice_window.2
    linarith
  simpa only [favorableNext_proposal_length] using proposed_exact_reporting_index favorableNextProposal hn tolerance ht hr hc

theorem favorableNext_proposal_reported_prefix (tolerance : ℝ)
    (ht : 0 ≤ tolerance) (htu : tolerance ≤ 1) :
    panelReported panel150 (fun r => completedPrice unitRoleUnused (resourceAction r))
      favorableNextProposal savedTarget tolerance = favorableNextProposal.take 36 := by
  unfold panelReported
  rw [favorableNext_proposal_reporting_index tolerance ht htu]

theorem adverseComplete_proposal_length : adverseCompleteProposal.length = 45 := by rfl

theorem adverseComplete_proposal_invoice_window :
    completedBill unitRoleUnused (adverseCompleteProposal.take 44) < savedTarget ∧
      savedTarget+1 < completedBill unitRoleUnused adverseCompleteProposal := by
  rw [adverseComplete_retained_physical_invoice,adverseComplete_whole_physical_invoice]
  norm_num [savedTarget]

theorem adverseComplete_proposal_all_proper_prefixes :
    ∀ k,k < 45 → completedBill unitRoleUnused (adverseCompleteProposal.take k) < savedTarget := by
  have hr : completedBill unitRoleUnused (adverseCompleteProposal.take (adverseCompleteProposal.length-1)) < savedTarget := by
    simpa only [adverseComplete_proposal_length] using adverseComplete_proposal_invoice_window.1
  simpa only [adverseComplete_proposal_length] using proposed_proper_prefixes_below_target adverseCompleteProposal hr

theorem adverseComplete_proposal_reporting_index (tolerance : ℝ)
    (ht : 0 ≤ tolerance) (htu : tolerance ≤ 1) :
    panelReportingIndex panel150 (fun r => completedPrice unitRoleUnused (resourceAction r))
      adverseCompleteProposal savedTarget tolerance = 44 := by
  have hn : 0 < adverseCompleteProposal.length := by rw [adverseComplete_proposal_length]; omega
  have hr : completedBill unitRoleUnused (adverseCompleteProposal.take (adverseCompleteProposal.length-1)) < savedTarget := by
    simpa only [adverseComplete_proposal_length] using adverseComplete_proposal_invoice_window.1
  have hc : savedTarget+tolerance < completedBill unitRoleUnused adverseCompleteProposal := by
    have hw := adverseComplete_proposal_invoice_window.2
    linarith
  simpa only [adverseComplete_proposal_length] using proposed_exact_reporting_index adverseCompleteProposal hn tolerance ht hr hc

theorem adverseComplete_proposal_reported_prefix (tolerance : ℝ)
    (ht : 0 ≤ tolerance) (htu : tolerance ≤ 1) :
    panelReported panel150 (fun r => completedPrice unitRoleUnused (resourceAction r))
      adverseCompleteProposal savedTarget tolerance = adverseCompleteProposal.take 44 := by
  unfold panelReported
  rw [adverseComplete_proposal_reporting_index tolerance ht htu]

theorem adverseNext_proposal_length : adverseNextProposal.length = 36 := by rfl

theorem adverseNext_proposal_invoice_window :
    completedBill unitRoleUnused (adverseNextProposal.take 35) < savedTarget ∧
      savedTarget+1 < completedBill unitRoleUnused adverseNextProposal := by
  rw [adverseNext_retained_physical_invoice,adverseNext_whole_physical_invoice]
  norm_num [savedTarget]

theorem adverseNext_proposal_all_proper_prefixes :
    ∀ k,k < 36 → completedBill unitRoleUnused (adverseNextProposal.take k) < savedTarget := by
  have hr : completedBill unitRoleUnused (adverseNextProposal.take (adverseNextProposal.length-1)) < savedTarget := by
    simpa only [adverseNext_proposal_length] using adverseNext_proposal_invoice_window.1
  simpa only [adverseNext_proposal_length] using proposed_proper_prefixes_below_target adverseNextProposal hr

theorem adverseNext_proposal_reporting_index (tolerance : ℝ)
    (ht : 0 ≤ tolerance) (htu : tolerance ≤ 1) :
    panelReportingIndex panel150 (fun r => completedPrice unitRoleUnused (resourceAction r))
      adverseNextProposal savedTarget tolerance = 35 := by
  have hn : 0 < adverseNextProposal.length := by rw [adverseNext_proposal_length]; omega
  have hr : completedBill unitRoleUnused (adverseNextProposal.take (adverseNextProposal.length-1)) < savedTarget := by
    simpa only [adverseNext_proposal_length] using adverseNext_proposal_invoice_window.1
  have hc : savedTarget+tolerance < completedBill unitRoleUnused adverseNextProposal := by
    have hw := adverseNext_proposal_invoice_window.2
    linarith
  simpa only [adverseNext_proposal_length] using proposed_exact_reporting_index adverseNextProposal hn tolerance ht hr hc

theorem adverseNext_proposal_reported_prefix (tolerance : ℝ)
    (ht : 0 ≤ tolerance) (htu : tolerance ≤ 1) :
    panelReported panel150 (fun r => completedPrice unitRoleUnused (resourceAction r))
      adverseNextProposal savedTarget tolerance = adverseNextProposal.take 35 := by
  unfold panelReported
  rw [adverseNext_proposal_reporting_index tolerance ht htu]

end AgentUCTRealIndex
