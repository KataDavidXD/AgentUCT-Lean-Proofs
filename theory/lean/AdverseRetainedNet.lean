import FavorableRetainedNet
import AdverseCompleteInvoice
import AdverseNextInvoice

set_option autoImplicit false
noncomputable section
namespace AgentUCTNextExact
open AgentUCTRealIndex AgentUCT32MConcrete AgentUCT32MContinuation AgentUCTSavedBudget
  AgentUCTObservability AgentUCTPhysicalDiagnostic AgentUCTNativeBudget
  AgentUCTPanelAllocation AgentUCTNativeRepair AgentUCTNativeRefinement AgentUCTPaper




theorem adverse_complete_reporting_prefix (tolerance : ℝ)
    (ht : 0 ≤ tolerance) (htu : tolerance ≤ 1) :
    panelReported panel150 (fun r => completedPrice unitRoleUnused (resourceAction r))
      adverseCompleteProposal savedTarget tolerance = adverseCompleteProposal.take 44 := by
  have hn : adverseCompleteProposal.length = 45 := by rfl
  apply (show _ = adverseCompleteProposal.take (adverseCompleteProposal.length-1) from ?_).trans
    (by rw [hn])
  apply proposed_exact_reported_prefix
  · rw [hn]; omega
  · exact ht
  · rw [hn,adverseComplete_retained_physical_invoice]
    norm_num [savedTarget]
  · rw [adverseComplete_whole_physical_invoice]
    have h : savedTarget+1 < (326759288764857/10000000:ℝ) := by norm_num [savedTarget]
    linarith

theorem adverse_next_reporting_prefix (tolerance : ℝ)
    (ht : 0 ≤ tolerance) (htu : tolerance ≤ 1) :
    panelReported panel150 (fun r => completedPrice unitRoleUnused (resourceAction r))
      adverseNextProposal savedTarget tolerance = adverseNextProposal.take 35 := by
  have hn : adverseNextProposal.length = 36 := by rfl
  apply (show _ = adverseNextProposal.take (adverseNextProposal.length-1) from ?_).trans
    (by rw [hn])
  apply proposed_exact_reported_prefix
  · rw [hn]; omega
  · exact ht
  · rw [hn,adverseNext_retained_physical_invoice]
    norm_num [savedTarget]
  · rw [adverseNext_whole_physical_invoice]
    have h : savedTarget+1 < (646625512555167/20000000:ℝ) := by norm_num [savedTarget]
    linarith

theorem adverse_complete_observed_net_exact (tolerance lambda Cref : ℝ)
    (ht : 0 ≤ tolerance) (htu : tolerance ≤ 1) :
    observedHistoryNet panel150 (completedPrice unitRoleUnused) adverseCompleteProposal
      savedTarget tolerance lambda Cref = (2/5:ℝ)-lambda*(318501296095161/10000000)/Cref := by
  unfold observedHistoryNet
  rw [adverse_complete_reporting_prefix tolerance ht htu]
  dsimp only
  change completedValue (adverseCompleteProposal.take 44)-
    lambda*completedBill unitRoleUnused (adverseCompleteProposal.take 44)/Cref = _
  rw [adverseComplete_retained_proposal_quality,adverseComplete_retained_physical_invoice]

theorem adverse_next_observed_net_exact (tolerance lambda Cref : ℝ)
    (ht : 0 ≤ tolerance) (htu : tolerance ≤ 1) :
    observedHistoryNet panel150 (completedPrice unitRoleUnused) adverseNextProposal
      savedTarget tolerance lambda Cref = (1/2:ℝ)-lambda*(155918255329191/5000000)/Cref := by
  unfold observedHistoryNet
  rw [adverse_next_reporting_prefix tolerance ht htu]
  dsimp only
  change completedValue (adverseNextProposal.take 35)-
    lambda*completedBill unitRoleUnused (adverseNextProposal.take 35)/Cref = _
  rw [adverseNext_retained_proposal_quality,adverseNext_retained_physical_invoice]

theorem adverse_retained_bill_gap :
    completedBill unitRoleUnused (adverseCompleteProposal.take 44)-
      completedBill unitRoleUnused (adverseNextProposal.take 35) = (6664785436779/10000000:ℝ) := by
  rw [adverseComplete_retained_physical_invoice,adverseNext_retained_physical_invoice]
  norm_num

theorem adverse_retained_quality_gap :
    completedValue (adverseNextProposal.take 35)-
      completedValue (adverseCompleteProposal.take 44) = (1/10:ℝ) := by
  rw [adverseNext_retained_proposal_quality,adverseComplete_retained_proposal_quality]
  norm_num

theorem adverse_observed_next_net_gain_exact (tolerance lambda Cref : ℝ)
    (ht : 0 ≤ tolerance) (htu : tolerance ≤ 1) :
    observedHistoryNet panel150 (completedPrice unitRoleUnused) adverseNextProposal
      savedTarget tolerance lambda Cref -
      observedHistoryNet panel150 (completedPrice unitRoleUnused) adverseCompleteProposal
        savedTarget tolerance lambda Cref = (1/10:ℝ)+lambda*(6664785436779/10000000)/Cref := by
  rw [adverse_complete_observed_net_exact tolerance lambda Cref ht htu,
    adverse_next_observed_net_exact tolerance lambda Cref ht htu]
  ring

theorem adverse_observed_next_net_strictly_larger (tolerance lambda Cref : ℝ)
    (ht : 0 ≤ tolerance) (htu : tolerance ≤ 1) (hl : 0 ≤ lambda) (hC : 0 < Cref) :
    observedHistoryNet panel150 (completedPrice unitRoleUnused) adverseCompleteProposal
      savedTarget tolerance lambda Cref <
      observedHistoryNet panel150 (completedPrice unitRoleUnused) adverseNextProposal
        savedTarget tolerance lambda Cref := by
  have hg := adverse_observed_next_net_gain_exact tolerance lambda Cref ht htu
  have hp : 0 ≤ lambda*(6664785436779/10000000:ℝ)/Cref :=
    div_nonneg (mul_nonneg hl (by norm_num)) hC.le
  linarith

theorem adverse_saved32M_next_net_strictly_larger (tolerance : ℝ)
    (ht : 0 ≤ tolerance) (htu : tolerance ≤ 1) :
    observedHistoryNet panel150 (completedPrice unitRoleUnused) adverseCompleteProposal
      savedTarget tolerance (1/20) savedCref <
      observedHistoryNet panel150 (completedPrice unitRoleUnused) adverseNextProposal
        savedTarget tolerance (1/20) savedCref := by
  exact adverse_observed_next_net_strictly_larger tolerance (1/20) savedCref ht htu
    (by norm_num) saved_cref_positive

end AgentUCTNextExact
