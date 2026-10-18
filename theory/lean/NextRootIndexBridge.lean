import NextNormalQuote
import ProposalRewards
set_option autoImplicit false
set_option maxRecDepth 16384
set_option maxHeartbeats 16000000
noncomputable section
namespace AgentUCT32MConcrete
open AgentUCT32MContinuation AgentUCTSavedBudget AgentUCTObservability
  AgentUCTPhysicalDiagnostic AgentUCTNativeBudget AgentUCTPanelAllocation
  AgentUCTNativeRepair AgentUCTNativeRefinement AgentUCTPaper AgentUCTRealIndex AgentUCTNextExact

def nextNormalPenalty (before : List (TreeEvaluation Act)) : ℝ :=
  controlPenalty savedCref uniformQuoteError unitRoleUnused .next before [] (.query 0)

def nextNormalPenaltyLower : ℝ := (300/savedCref)*((4205751296/1000000000)*320-uniformQuoteError)
def nextNormalPenaltyUpper : ℝ := (300/savedCref)*((4205751296/1000000000)*320+uniformQuoteError)

theorem normal_next_penalty_interval (before : List (TreeEvaluation Act))
    (hs : normalWarmStages before 0 = {1,2,3}) :
    nextNormalPenaltyLower ≤ nextNormalPenalty before ∧ nextNormalPenalty before ≤ nextNormalPenaltyUpper := by
  have hh := completed_live_receipt_error_all_histories uniformQuoteError (by norm_num [uniformQuoteError])
    (by norm_num [uniformQuoteError]) before (0,(normalMCPath 0).take 4)
  change |concretePrice before (0,(normalMCPath 0).take 4)-completedPrice unitRoleUnused
    (resourceAction (0,(normalMCPath 0).take 4))| ≤ uniformQuoteError at hh
  rw [normal_first_resource_action 0 (by decide) 0,completed_price_rational_projection] at hh
  norm_num [rationalActionPrice] at hh
  obtain ⟨hl,hu⟩ := abs_le.mp hh
  have hc : 0 ≤ 300/savedCref := by norm_num [savedCref]
  have hlo := mul_le_mul_of_nonneg_left hl hc
  have hhi := mul_le_mul_of_nonneg_left hu hc
  unfold nextNormalPenalty
  rw [normal_penalty_exact savedCref before 0 (by decide) hs hs]
  unfold nextNormalPenaltyLower nextNormalPenaltyUpper
  constructor <;> nlinarith

theorem favorable_next_penalty_interval (k : ℕ) (hk : 8 ≤ k) :
    nextNormalPenaltyLower ≤ nextNormalPenalty (favorableNextProposal.take k) ∧
    nextNormalPenalty (favorableNextProposal.take k) ≤ nextNormalPenaltyUpper :=
  normal_next_penalty_interval _ (favorable_normal_stages k hk 0 (by decide))

theorem adverse_next_penalty_interval (k : ℕ) (hk : 8 ≤ k) :
    nextNormalPenaltyLower ≤ nextNormalPenalty (adverseNextProposal.take k) ∧
    nextNormalPenalty (adverseNextProposal.take k) ≤ nextNormalPenaltyUpper :=
  normal_next_penalty_interval _ (adverse_normal_stages k hk 0 (by decide))

end AgentUCT32MConcrete
