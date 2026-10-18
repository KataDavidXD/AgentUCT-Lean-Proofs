import ActualIndexCertificate
set_option autoImplicit false
set_option maxRecDepth 16384
set_option maxHeartbeats 16000000
noncomputable section
namespace AgentUCTNextExact
open AgentUCT32MConcrete AgentUCT32MContinuation AgentUCTSavedBudget AgentUCTObservability
  AgentUCTPhysicalDiagnostic AgentUCTNativeBudget AgentUCTPanelAllocation
  AgentUCTNativeRepair AgentUCTNativeRefinement AgentUCTPaper

def normalMCPath (q : Fin 8) := safeCompletion [.query q]
def normalWarmStages (history : List (TreeEvaluation Act)) (q : Fin 8) : Finset ℕ :=
  (Finset.range ((normalMCPath q).length+1)).filter
    (fun i => 0 < i ∧ (normalMCPath q).take i ∈ pathHistoryCache history)

theorem path_cache_prefix (before events : List (TreeEvaluation Act)) (hp : before <+: events) :
    pathHistoryCache before ⊆ pathHistoryCache events := by
  intro path hm
  have hi : ((0:Fin 150),path) ∈ ownPanelCache panel150 before := by
    rw [own_panel_cache_product]; simp [panel150,hm]
  have ho := own_panel_cache_prefix panel150 before events hp hi
  rw [own_panel_cache_product] at ho
  exact (Finset.mem_product.mp ho).2

theorem normal_stages_prefix (before events : List (TreeEvaluation Act)) (hp : before <+: events)
    (q : Fin 8) : normalWarmStages before q ⊆ normalWarmStages events q := by
  intro i hi
  obtain ⟨hrange,hpositive,hcached⟩ := Finset.mem_filter.mp hi
  exact Finset.mem_filter.mpr ⟨hrange,hpositive,path_cache_prefix before events hp hcached⟩

theorem favorable_initial_normal_stages (q : Fin 8) (hq : q ≠ hyde) :
    normalWarmStages (favorableNextProposal.take 8) q = {1,2,3} := by
  fin_cases q <;> (try simp [hyde] at hq) <;> decide

theorem favorable_final_normal_stages (q : Fin 8) (hq : q ≠ hyde) :
    normalWarmStages favorableNextProposal q = {1,2,3} := by
  fin_cases q <;> (try simp [hyde] at hq) <;> decide

theorem adverse_initial_normal_stages (q : Fin 8) (hq : q ≠ hyde) :
    normalWarmStages (adverseNextProposal.take 8) q = {1,2,3} := by
  fin_cases q <;> (try simp [hyde] at hq) <;> decide

theorem adverse_final_normal_stages (q : Fin 8) (hq : q ≠ hyde) :
    normalWarmStages adverseNextProposal q = {1,2,3} := by
  fin_cases q <;> (try simp [hyde] at hq) <;> decide

theorem normal_stages_between_equal_endpoints (events : List (TreeEvaluation Act)) (k : ℕ)
    (hk : 8 ≤ k) (q : Fin 8)
    (hinit : normalWarmStages (events.take 8) q = {1,2,3})
    (hfinal : normalWarmStages events q = {1,2,3}) :
    normalWarmStages (events.take k) q = {1,2,3} := by
  apply Finset.Subset.antisymm
  · rw [← hfinal]
    exact normal_stages_prefix _ _ (List.take_prefix _ _) q
  · rw [← hinit]
    apply normal_stages_prefix _ _ _ q
    exact List.take_prefix_take_left hk

theorem favorable_normal_stages (k : ℕ) (hk : 8 ≤ k) (q : Fin 8) (hq : q ≠ hyde) :
    normalWarmStages (favorableNextProposal.take k) q = {1,2,3} :=
  normal_stages_between_equal_endpoints _ _ hk q
    (favorable_initial_normal_stages q hq) (favorable_final_normal_stages q hq)

theorem adverse_normal_stages (k : ℕ) (hk : 8 ≤ k) (q : Fin 8) (hq : q ≠ hyde) :
    normalWarmStages (adverseNextProposal.take k) q = {1,2,3} :=
  normal_stages_between_equal_endpoints _ _ hk q
    (adverse_initial_normal_stages q hq) (adverse_final_normal_stages q hq)

theorem normal_warm_depth_three (history : List (TreeEvaluation Act)) (q : Fin 8)
    (hstages : normalWarmStages history q = {1,2,3}) :
    pathWarmDepth (pathHistoryCache history) (normalMCPath q) = 3 := by
  change (normalWarmStages history q).sup id = 3
  rw [hstages]
  decide

theorem normal_mc_path (q : Fin 8) (hq : q ≠ hyde) :
    normalMCPath q = fullLeaf q (.normalRetriever 0) 0 1 1 2 0 := by
  fin_cases q <;> (try simp [hyde] at hq) <;> decide

theorem normal_first_unpaid_absent (history : List (TreeEvaluation Act)) (q : Fin 8) (hq : q ≠ hyde)
    (hstages : normalWarmStages history q = {1,2,3}) (qid : Fin 150) :
    (qid,(normalMCPath q).take 4) ∉ ownPanelCache panel150 history := by
  intro h
  rw [own_panel_cache_product] at h
  have hc := (Finset.mem_product.mp h).2
  have hi : 4 ∈ normalWarmStages history q := by
    apply Finset.mem_filter.mpr
    refine ⟨?_,by norm_num,hc⟩
    rw [normal_mc_path q hq]
    norm_num [fullLeaf]
  rw [hstages] at hi
  norm_num at hi

end AgentUCTNextExact
