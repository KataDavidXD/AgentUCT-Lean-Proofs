import NextNormalQuote
import FavorableCompleteInvoice
import AdverseCompleteInvoice

set_option autoImplicit false
set_option maxRecDepth 32768
set_option maxHeartbeats 16000000
noncomputable section
namespace AgentUCTNextExact
open AgentUCTRealIndex AgentUCT32MConcrete AgentUCT32MContinuation AgentUCTSavedBudget
  AgentUCTObservability AgentUCTPhysicalDiagnostic AgentUCTNativeBudget
  AgentUCTPanelAllocation AgentUCTNativeRepair AgentUCTNativeRefinement AgentUCTPaper




theorem favorable_complete_initial_normal_stages (q : Fin 8) (hq : q ≠ hyde) :
    normalWarmStages (favorableCompleteProposal.take 8) q = {1,2,3} := by
  fin_cases q <;> (try simp [hyde] at hq) <;> decide

theorem favorable_complete_final_normal_stages (q : Fin 8) (hq : q ≠ hyde) :
    normalWarmStages favorableCompleteProposal q = {1,2,3} := by
  unfold normalWarmStages
  rw [favorableComplete_whole_cache_exact]
  fin_cases q <;> (try simp [hyde] at hq) <;> decide

theorem adverse_complete_initial_normal_stages (q : Fin 8) (hq : q ≠ hyde) :
    normalWarmStages (adverseCompleteProposal.take 8) q = {1,2,3} := by
  fin_cases q <;> (try simp [hyde] at hq) <;> decide

theorem adverse_complete_final_normal_stages (q : Fin 8) (hq : q ≠ hyde) :
    normalWarmStages adverseCompleteProposal q = {1,2,3} := by
  unfold normalWarmStages
  rw [adverseComplete_whole_cache_exact]
  fin_cases q <;> (try simp [hyde] at hq) <;> decide

theorem favorable_complete_normal_stages (k : ℕ) (hk : 8 ≤ k) (q : Fin 8) (hq : q ≠ hyde) :
    normalWarmStages (favorableCompleteProposal.take k) q = {1,2,3} :=
  normal_stages_between_equal_endpoints _ _ hk q
    (favorable_complete_initial_normal_stages q hq) (favorable_complete_final_normal_stages q hq)

theorem adverse_complete_normal_stages (k : ℕ) (hk : 8 ≤ k) (q : Fin 8) (hq : q ≠ hyde) :
    normalWarmStages (adverseCompleteProposal.take k) q = {1,2,3} :=
  normal_stages_between_equal_endpoints _ _ hk q
    (adverse_complete_initial_normal_stages q hq) (adverse_complete_final_normal_stages q hq)

theorem normal_complete_physical_quote_from_stages (before : List (TreeEvaluation Act))
    (q : Fin 8) (hq : q ≠ hyde) (hs : normalWarmStages before q = {1,2,3}) :
    pathQuote .complete (pathHistoryCache before) (completedPrice unitRoleUnused)
      (safeCompletion [.query q]) = (154035641216/1953125:ℝ) := by
  change pathQuote .complete (pathHistoryCache before) (completedPrice unitRoleUnused) (normalMCPath q) = _
  unfold pathQuote
  rw [normal_suffix_after_three before q hq hs,normal_mc_path q hq]
  norm_num [completed_price_rational_projection,rationalActionPrice,fullLeaf]

theorem favorable_complete_normal_root_physical_quote_exact (k : ℕ) (hk : 8 ≤ k)
    (q : Fin 8) (hq : q ≠ hyde) :
    pathQuote .complete (pathHistoryCache (favorableCompleteProposal.take k)) (completedPrice unitRoleUnused)
      (safeCompletion [.query q]) = (154035641216/1953125:ℝ) :=
  normal_complete_physical_quote_from_stages _ q hq (favorable_complete_normal_stages k hk q hq)

theorem adverse_complete_normal_root_physical_quote_exact (k : ℕ) (hk : 8 ≤ k)
    (q : Fin 8) (hq : q ≠ hyde) :
    pathQuote .complete (pathHistoryCache (adverseCompleteProposal.take k)) (completedPrice unitRoleUnused)
      (safeCompletion [.query q]) = (154035641216/1953125:ℝ) :=
  normal_complete_physical_quote_from_stages _ q hq (adverse_complete_normal_stages k hk q hq)

end AgentUCTNextExact
