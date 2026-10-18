import RetainedProposalQuality
import EndpointBudgetBase
import FavorableCompleteInvoice
import FavorableNextInvoice

set_option autoImplicit false
noncomputable section
namespace AgentUCTNextExact
open AgentUCTRealIndex AgentUCT32MConcrete AgentUCT32MContinuation AgentUCTSavedBudget
  AgentUCTObservability AgentUCTPhysicalDiagnostic AgentUCTNativeBudget
  AgentUCTPanelAllocation AgentUCTNativeRepair AgentUCTNativeRefinement AgentUCTPaper




def proposalRetainedNet (events : List (TreeEvaluation Act)) (lambda Cref : ℝ) : ℝ :=
  completedValue events-lambda*completedBill unitRoleUnused events/Cref

theorem favorable_complete_reporting_prefix (tolerance : ℝ)
    (ht : 0 ≤ tolerance) (htu : tolerance ≤ 1) :
    panelReported panel150 (fun r => completedPrice unitRoleUnused (resourceAction r))
      favorableCompleteProposal savedTarget tolerance = favorableCompleteProposal.take 43 := by
  have hn : favorableCompleteProposal.length = 44 := by rfl
  apply (show _ = favorableCompleteProposal.take (favorableCompleteProposal.length-1) from ?_).trans
    (by rw [hn])
  apply proposed_exact_reported_prefix
  · rw [hn]; omega
  · exact ht
  · rw [hn,favorableComplete_retained_physical_invoice]
    norm_num [savedTarget]
  · rw [favorableComplete_whole_physical_invoice]
    have h : savedTarget+1 < (321718695836601/10000000:ℝ) := by norm_num [savedTarget]
    linarith

theorem favorable_next_reporting_prefix (tolerance : ℝ)
    (ht : 0 ≤ tolerance) (htu : tolerance ≤ 1) :
    panelReported panel150 (fun r => completedPrice unitRoleUnused (resourceAction r))
      favorableNextProposal savedTarget tolerance = favorableNextProposal.take 36 := by
  have hn : favorableNextProposal.length = 37 := by rfl
  apply (show _ = favorableNextProposal.take (favorableNextProposal.length-1) from ?_).trans
    (by rw [hn])
  apply proposed_exact_reported_prefix
  · rw [hn]; omega
  · exact ht
  · rw [hn,favorableNext_retained_physical_invoice]
    norm_num [savedTarget]
  · rw [favorableNext_whole_physical_invoice]
    have h : savedTarget+1 < (646625512555167/20000000:ℝ) := by norm_num [savedTarget]
    linarith

theorem favorable_complete_observed_net_exact (tolerance lambda Cref : ℝ)
    (ht : 0 ≤ tolerance) (htu : tolerance ≤ 1) :
    observedHistoryNet panel150 (completedPrice unitRoleUnused) favorableCompleteProposal
      savedTarget tolerance lambda Cref = (1/2:ℝ)-lambda*(62692140633381/2000000)/Cref := by
  unfold observedHistoryNet
  rw [favorable_complete_reporting_prefix tolerance ht htu]
  dsimp only
  change completedValue (favorableCompleteProposal.take 43)-
    lambda*completedBill unitRoleUnused (favorableCompleteProposal.take 43)/Cref = _
  rw [favorableComplete_retained_proposal_quality,favorableComplete_retained_physical_invoice]

theorem favorable_next_observed_net_exact (tolerance lambda Cref : ℝ)
    (ht : 0 ≤ tolerance) (htu : tolerance ≤ 1) :
    observedHistoryNet panel150 (completedPrice unitRoleUnused) favorableNextProposal
      savedTarget tolerance lambda Cref = (1/2:ℝ)-lambda*(155918255329191/5000000)/Cref := by
  unfold observedHistoryNet
  rw [favorable_next_reporting_prefix tolerance ht htu]
  dsimp only
  change completedValue (favorableNextProposal.take 36)-
    lambda*completedBill unitRoleUnused (favorableNextProposal.take 36)/Cref = _
  rw [favorableNext_retained_proposal_quality,favorableNext_retained_physical_invoice]

theorem favorable_retained_bill_gap :
    completedBill unitRoleUnused (favorableCompleteProposal.take 43)-
      completedBill unitRoleUnused (favorableNextProposal.take 36) = (1624192508523/10000000:ℝ) := by
  rw [favorableComplete_retained_physical_invoice,favorableNext_retained_physical_invoice]
  norm_num

theorem favorable_observed_next_net_gain_exact (tolerance lambda Cref : ℝ)
    (ht : 0 ≤ tolerance) (htu : tolerance ≤ 1) :
    observedHistoryNet panel150 (completedPrice unitRoleUnused) favorableNextProposal
      savedTarget tolerance lambda Cref -
      observedHistoryNet panel150 (completedPrice unitRoleUnused) favorableCompleteProposal
        savedTarget tolerance lambda Cref = lambda*(1624192508523/10000000)/Cref := by
  rw [favorable_complete_observed_net_exact tolerance lambda Cref ht htu,
    favorable_next_observed_net_exact tolerance lambda Cref ht htu]
  ring

theorem favorable_observed_next_net_strictly_larger (tolerance lambda Cref : ℝ)
    (ht : 0 ≤ tolerance) (htu : tolerance ≤ 1) (hl : 0 < lambda) (hC : 0 < Cref) :
    observedHistoryNet panel150 (completedPrice unitRoleUnused) favorableCompleteProposal
      savedTarget tolerance lambda Cref <
      observedHistoryNet panel150 (completedPrice unitRoleUnused) favorableNextProposal
        savedTarget tolerance lambda Cref := by
  have hg := favorable_observed_next_net_gain_exact tolerance lambda Cref ht htu
  have hp : 0 < lambda*(1624192508523/10000000:ℝ)/Cref :=
    div_pos (mul_pos hl (by norm_num)) hC
  linarith

theorem favorable_saved32M_next_net_strictly_larger (tolerance : ℝ)
    (ht : 0 ≤ tolerance) (htu : tolerance ≤ 1) :
    observedHistoryNet panel150 (completedPrice unitRoleUnused) favorableCompleteProposal
      savedTarget tolerance (1/20) savedCref <
      observedHistoryNet panel150 (completedPrice unitRoleUnused) favorableNextProposal
        savedTarget tolerance (1/20) savedCref := by
  exact favorable_observed_next_net_strictly_larger tolerance (1/20) savedCref ht htu
    (by norm_num) saved_cref_positive

end AgentUCTNextExact
