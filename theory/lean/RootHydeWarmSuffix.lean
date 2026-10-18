import CompleteNormalQuote
import CachedSuffixCertificate

set_option autoImplicit false
set_option maxRecDepth 16384
set_option maxHeartbeats 16000000
noncomputable section
namespace AgentUCTNextExact
open AgentUCTRealIndex AgentUCT32MConcrete AgentUCT32MContinuation AgentUCTSavedBudget
  AgentUCTObservability AgentUCTPhysicalDiagnostic AgentUCTNativeBudget
  AgentUCTPanelAllocation AgentUCTNativeRepair AgentUCTNativeRefinement AgentUCTPaper




theorem hyde_root_initial_cached :
    safeCompletion [.query 1] ∈ pathHistoryCache (favorableCompleteProposal.take 9) ∧
    safeCompletion [.query 1] ∈ pathHistoryCache (favorableNextProposal.take 10) ∧
    safeCompletion [.query 1] ∈ pathHistoryCache (adverseCompleteProposal.take 9) ∧
    safeCompletion [.query 1] ∈ pathHistoryCache (adverseNextProposal.take 10) := by decide

theorem hyde_root_not_materialized_by_eight_seeds :
    safeCompletion [.query 1] ∉ pathHistoryCache (favorableCompleteProposal.take 8) ∧
    safeCompletion [.query 1] ∉ pathHistoryCache (favorableNextProposal.take 8) ∧
    safeCompletion [.query 1] ∉ pathHistoryCache (adverseCompleteProposal.take 8) ∧
    safeCompletion [.query 1] ∉ pathHistoryCache (adverseNextProposal.take 8) := by decide

theorem hyde_root_cached_suffix_empty (events : List (TreeEvaluation Act))
    (hc : safeCompletion [.query 1] ∈ pathHistoryCache events) :
    pathSuffix (pathHistoryCache events) (safeCompletion [.query 1]) = [] :=
  path_suffix_nil_of_cached _ _ hc

theorem hyde_root_suffix_empty_after_seed (events : List (TreeEvaluation Act)) (base k : ℕ)
    (hk : base ≤ k) (hc : safeCompletion [.query 1] ∈ pathHistoryCache (events.take base)) :
    pathSuffix (pathHistoryCache (events.take k)) (safeCompletion [.query 1]) = [] := by
  apply hyde_root_cached_suffix_empty
  exact path_cache_prefix _ _ (List.take_prefix_take_left hk) hc

theorem favorable_complete_hyde_root_suffix_empty (k : ℕ) (hk : 9 ≤ k) :
    pathSuffix (pathHistoryCache (favorableCompleteProposal.take k)) (safeCompletion [.query 1]) = [] :=
  hyde_root_suffix_empty_after_seed _ 9 k hk hyde_root_initial_cached.1

theorem favorable_next_hyde_root_suffix_empty (k : ℕ) (hk : 10 ≤ k) :
    pathSuffix (pathHistoryCache (favorableNextProposal.take k)) (safeCompletion [.query 1]) = [] :=
  hyde_root_suffix_empty_after_seed _ 10 k hk hyde_root_initial_cached.2.1

theorem adverse_complete_hyde_root_suffix_empty (k : ℕ) (hk : 9 ≤ k) :
    pathSuffix (pathHistoryCache (adverseCompleteProposal.take k)) (safeCompletion [.query 1]) = [] :=
  hyde_root_suffix_empty_after_seed _ 9 k hk hyde_root_initial_cached.2.2.1

theorem adverse_next_hyde_root_suffix_empty (k : ℕ) (hk : 10 ≤ k) :
    pathSuffix (pathHistoryCache (adverseNextProposal.take k)) (safeCompletion [.query 1]) = [] :=
  hyde_root_suffix_empty_after_seed _ 10 k hk hyde_root_initial_cached.2.2.2

end AgentUCTNextExact
