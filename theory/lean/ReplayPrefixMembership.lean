import ReplayClosedForms

set_option autoImplicit false
noncomputable section
namespace AgentUCTRealIndex
open AgentUCTPaper AgentUCTNativeRepair AgentUCTNativeRefinement Finset

variable {Action : Type*} [DecidableEq Action]

theorem executionPrefixes_mem_iff (terminal p : List Action) :
    p ∈ executionPrefixes terminal ↔ 0 < p.length ∧ p <+: terminal := by
  constructor
  · intro h
    obtain ⟨i,hi,rfl⟩ := Finset.mem_image.mp h
    have hi' : 1 ≤ i ∧ i ≤ terminal.length := Finset.mem_Icc.mp hi
    constructor
    · simp only [List.length_take, Nat.min_eq_left hi'.2]
      omega
    · exact List.take_prefix i terminal
  · rintro ⟨hpos,hpref⟩
    apply Finset.mem_image.mpr
    refine ⟨p.length,Finset.mem_Icc.mpr ⟨hpos,hpref.length_le⟩,?_⟩
    exact (List.prefix_iff_eq_take.mp hpref).symm

theorem pathHistoryCache_nonempty_prefix (events : List (TreeEvaluation Act)) (p : List Act) :
    p ∈ pathHistoryCache events ↔ 0 < p.length ∧ ∃ e ∈ events, p <+: e.terminal := by
  rw [pathHistoryCache_mem]
  simp only [executionPrefixes_mem_iff]
  aesop

theorem root_backedEvents (events : List (TreeEvaluation Action)) :
    backedEvents events [] = events := by
  simp [backedEvents]

theorem replayBackup_root_sum (events : List (TreeEvaluation Action)) :
    replayBackup events emptyStatistics [] =
      ⟨events.length,(events.map TreeEvaluation.reward).sum⟩ := by
  rw [replayBackup_empty_closed_form,root_backedEvents]

theorem replayBackup_from_summary (events : List (TreeEvaluation Action)) (p : List Action)
    (n : ℕ) (total : ℝ)
    (hcount : (backedEvents events p).length = n)
    (hreturn : ((backedEvents events p).map TreeEvaluation.reward).sum = total) :
    replayBackup events emptyStatistics p = ⟨n,total⟩ := by
  rw [replayBackup_empty_closed_form,hcount,hreturn]

theorem replayBackup_mean_from_summary (events : List (TreeEvaluation Action)) (p : List Action)
    (n : ℕ) (total : ℝ)
    (hcount : (backedEvents events p).length = n)
    (hreturn : ((backedEvents events p).map TreeEvaluation.reward).sum = total) :
    (replayBackup events emptyStatistics p).mean = total/n := by
  rw [replayBackup_from_summary events p n total hcount hreturn]
  rfl

end AgentUCTRealIndex
