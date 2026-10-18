import PhysicalQuoteProjection
import NativeChoiceTools
import ReplayPrefixMembership



set_option autoImplicit false
noncomputable section
namespace AgentUCTRealIndex
open AgentUCT32MConcrete AgentUCT32MContinuation AgentUCTSavedBudget
  AgentUCTObservability AgentUCTPhysicalDiagnostic AgentUCTNativeBudget
  AgentUCTPanelAllocation AgentUCTNativeRepair AgentUCTNativeRefinement AgentUCTPaper

theorem path_warm_depth_eq_length_of_cached (cache : Finset (List Act)) (p : List Act)
    (hcache : p ∈ cache) : pathWarmDepth cache p = p.length := by
  have hupper : pathWarmDepth cache p ≤ p.length := by
    unfold pathWarmDepth
    apply Finset.sup_le
    intro i hi
    have hm := (Finset.mem_filter.mp hi).1
    have hr := Finset.mem_range.mp hm
    dsimp only [id]
    omega
  have hlower : p.length ≤ pathWarmDepth cache p := by
    by_cases hz : p.length = 0
    · rw [hz]
      exact Nat.zero_le _
    · have hp : 0 < p.length := by omega
      have hm : p.length ∈ ((Finset.range (p.length+1)).filter
          fun i => 0 < i ∧ p.take i ∈ cache) := by
        apply Finset.mem_filter.mpr
        exact ⟨Finset.mem_range.mpr (by omega),by simpa using And.intro hp hcache⟩
      exact Finset.le_sup (f := id) hm
  exact Nat.le_antisymm hupper hlower

theorem path_suffix_nil_of_cached (cache : Finset (List Act)) (p : List Act)
    (hcache : p ∈ cache) : pathSuffix cache p = [] := by
  unfold pathSuffix
  rw [path_warm_depth_eq_length_of_cached cache p hcache]
  have hf : ((List.range (p.length+1)).filter fun i => decide (p.length < i)) = [] := by
    apply List.filter_eq_nil_iff.mpr
    intro i hi
    have hr := List.mem_range.mp hi
    have hn : ¬ p.length < i := by omega
    simp [hn]
  rw [hf]
  rfl

theorem path_cache_of_prior_terminal (before : List (TreeEvaluation Act))
    (i : ℕ) (hi : i < before.length) (terminal : List Act)
    (hterm : before[i].terminal = terminal) (hpos : 0 < terminal.length) :
    terminal ∈ pathHistoryCache before := by
  apply (pathHistoryCache_nonempty_prefix before terminal).mpr
  refine ⟨hpos,before[i],List.getElem_mem hi,?_⟩
  rw [hterm]

theorem path_cache_of_prior_prefix (before : List (TreeEvaluation Act))
    (i : ℕ) (hi : i < before.length) (p : List Act)
    (hp : p <+: before[i].terminal) (hpos : 0 < p.length) :
    p ∈ pathHistoryCache before := by
  exact (pathHistoryCache_nonempty_prefix before p).mpr
    ⟨hpos,before[i],List.getElem_mem hi,hp⟩

theorem control_penalty_empty_of_prior_terminal (mode : ForecastMode) (Cref epsilon : ℝ)
    (before : List (TreeEvaluation Act)) (p : List Act) (a : Act)
    (i : ℕ) (hi : i < before.length)
    (hterm : before[i].terminal = safeCompletion (p++[a]))
    (hpos : 0 < (safeCompletion (p++[a])).length) :
    controlPenalty Cref epsilon unitRoleUnused mode before p a = 0 := by
  apply control_penalty_empty_suffix
  apply path_suffix_nil_of_cached
  exact path_cache_of_prior_terminal before i hi _ hterm hpos

theorem control_penalty_empty_of_prior_prefix (mode : ForecastMode) (Cref epsilon : ℝ)
    (before : List (TreeEvaluation Act)) (p : List Act) (a : Act)
    (i : ℕ) (hi : i < before.length)
    (hterm : safeCompletion (p++[a]) <+: before[i].terminal)
    (hpos : 0 < (safeCompletion (p++[a])).length) :
    controlPenalty Cref epsilon unitRoleUnused mode before p a = 0 := by
  apply control_penalty_empty_suffix
  apply path_suffix_nil_of_cached
  exact path_cache_of_prior_prefix before i hi _ hterm hpos

end AgentUCTRealIndex
