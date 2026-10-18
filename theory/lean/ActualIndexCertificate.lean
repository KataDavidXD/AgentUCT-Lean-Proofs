import ConcreteProposals
import ReplayClosedForms
import OrderedIndexCertificate
import UniformIndexDominance
import EqualBonusCancellation
set_option autoImplicit false
set_option maxRecDepth 16384
set_option maxHeartbeats 10000000
noncomputable section
namespace AgentUCT32MConcrete
open AgentUCT32MContinuation AgentUCTSavedBudget AgentUCTObservability
  AgentUCTPhysicalDiagnostic AgentUCTNativeBudget AgentUCTPanelAllocation
  AgentUCTNativeRepair AgentUCTNativeRefinement AgentUCTPaper AgentUCTRealIndex

theorem actual_index_interval (mode : ForecastMode) (Cref epsilon : ℝ)
    (hC : 0 < Cref) (he : 0 < epsilon) (hesmall : epsilon < 1/10)
    (before : List (TreeEvaluation Act)) (p : List Act) (a : Act)
    (hl : Legal p) (ha : a ∈ available p) (parent count : ℕ) (total quote blo bhi : ℝ)
    (hstat : replayBackup before emptyStatistics (p++[a]) = ⟨count,total⟩)
    (hparent : rawVisits before p = parent)
    (hquote : pathQuote mode (pathHistoryCache before) (completedPrice unitRoleUnused)
      (safeCompletion (p++[a])) = quote)
    (hbonus : blo ≤ treeBonus (7/5) parent count ∧ treeBonus (7/5) parent count ≤ bhi) :
    total/count + blo - (300/Cref)*quote - (3000/Cref)*epsilon ≤
      indexScore (7/5) (controlPenalty Cref epsilon unitRoleUnused mode) before p a ∧
    indexScore (7/5) (controlPenalty Cref epsilon unitRoleUnused mode) before p a ≤
      total/count + bhi - (300/Cref)*quote + (3000/Cref)*epsilon := by
  have hh := completed_control_penalty_error mode Cref epsilon hC he hesmall before p a hl ha
  rw [hquote] at hh
  obtain ⟨hlo,hhi⟩ := abs_le.mp hh
  have hn : rawVisits before (p++[a]) = count := by unfold rawVisits; rw [hstat]
  simp only [indexScore,hstat,hparent,hn,BackupStat.mean,treeIndex]
  constructor <;> linarith [hbonus.1,hbonus.2]

theorem next_unpaid_selected_receipt {R : Type*} [DecidableEq R]
    (prices target : R → ℝ) (lead rest : List R) (chosen : R)
    (hs : ∀ r,prices r ≤ 0 ↔ target r ≤ 0)
    (hlead : ∀ r ∈ lead,target r ≤ 0) (hchosen : 0 < target chosen) :
    nextUnpaidBill ∅ prices (lead++chosen::rest) = prices chosen := by
  induction lead with
  | nil => simp [nextUnpaidBill,show ¬ prices chosen ≤ 0 by exact fun h => not_le.mpr hchosen ((hs chosen).mp h)]
  | cons r lead ih =>
      simp only [List.cons_append,nextUnpaidBill,Finset.notMem_empty,false_or]
      rw [if_pos ((hs r).mpr (hlead r (by simp)))]
      exact ih (fun r hr => hlead r (List.mem_cons_of_mem _ hr))

end AgentUCT32MConcrete
