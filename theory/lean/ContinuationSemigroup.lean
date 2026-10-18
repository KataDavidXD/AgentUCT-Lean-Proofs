import OwnBillReporting




set_option autoImplicit false
set_option maxRecDepth 16384
set_option maxHeartbeats 4000000
noncomputable section
namespace AgentUCT32MContinuation
open AgentUCTSavedBudget AgentUCTObservability AgentUCTObservabilityBoundary AgentUCTPhysicalDiagnostic
  AgentUCTNativeBudget AgentUCTPanelAllocation AgentUCTNativeRepair AgentUCTNativeRefinement AgentUCTPaper

theorem native_after_causal_semigroup (tape : SharedTape) (c : ℝ)
    (penalty : List (TreeEvaluation Act) → List Act → Act → ℝ)
    (actualBill : List (TreeEvaluation Act) → ℝ) (B : ℝ) (reward : List Act → ℝ)
    (first second : ℕ) (before : List (TreeEvaluation Act)) :
    nativeAfter tape c penalty actualBill B reward (first+second) before =
      nativeAfter tape c penalty actualBill B reward second
        (nativeAfter tape c penalty actualBill B reward first before) := by
  induction first generalizing before with
  | zero => simp only [Nat.zero_add,nativeAfter]
  | succ first ih =>
      rw [Nat.succ_add]
      simp only [nativeAfter]
      split_ifs with ht
      · exact (native_after_crossing_stops tape c penalty actualBill B reward before ht second).symm
      · exact ih _

theorem native_after_increasing_caps_are_own_prefixes (tape : SharedTape) (c : ℝ)
    (penalty : List (TreeEvaluation Act) → List Act → Act → ℝ)
    (actualBill : List (TreeEvaluation Act) → ℝ) (B : ℝ) (reward : List Act → ℝ)
    (first second : ℕ) (before : List (TreeEvaluation Act)) :
    nativeAfter tape c penalty actualBill B reward first before <+:
      nativeAfter tape c penalty actualBill B reward (first+second) before := by
  rw [native_after_causal_semigroup]
  exact native_after_initial_prefix _ _ _ _ _ _ _ _

theorem own_control_continuation_from_smaller_cap (Cref B epsilon : ℝ)
    (unused : Act → Fin 8 → ℕ) (mode : ForecastMode) (adverse : Bool)
    (cap extra : ℕ) (hcap : 8 ≤ cap) :
    controlRun Cref B epsilon unused mode adverse (cap+extra) =
      nativeAfter budgetTape (7/5) (controlPenalty Cref epsilon unused mode)
        (completedBill unused) B (taskReward adverse (2/5) (1/2)) extra
        (controlRun Cref B epsilon unused mode adverse cap) := by
  unfold controlRun nativeGenerate
  have h : cap+extra-8 = (cap-8)+extra := by omega
  rw [h,native_after_causal_semigroup]

theorem own_control_smaller_cap_is_prefix (Cref B epsilon : ℝ)
    (unused : Act → Fin 8 → ℕ) (mode : ForecastMode) (adverse : Bool)
    (cap extra : ℕ) (hcap : 8 ≤ cap) :
    controlRun Cref B epsilon unused mode adverse cap <+:
      controlRun Cref B epsilon unused mode adverse (cap+extra) := by
  rw [own_control_continuation_from_smaller_cap Cref B epsilon unused mode adverse cap extra hcap]
  exact native_after_initial_prefix _ _ _ _ _ _ _ _

theorem panel_actual_bill_append_atomic {Qid : Type*} [DecidableEq Qid]
    (qids : Finset Qid) (price : Qid × List Act → ℝ)
    (before : List (TreeEvaluation Act)) (event : TreeEvaluation Act) :
    panelActualBill qids price (before++[event]) = panelActualBill qids price before +
      coldWork price (ownPanelCache qids before) (panelDemand qids event.terminal) := by
  simp only [panelActualBill,replayPanel,replayMetered,List.foldl_append,
    List.foldl_cons,List.foldl_nil]
  change _ + _ = _
  simp only [meterStep,MeteredTreeState.totalPaid]
  rw [← replay_panel_cache qids price before]
  simp only [replayPanel,replayMetered,panelDemand,id_eq]
  ring

theorem completed_bill_append_atomic (unused : Act → Fin 8 → ℕ)
    (before : List (TreeEvaluation Act)) (event : TreeEvaluation Act) :
    completedBill unused (before++[event]) = completedBill unused before +
      coldWork (fun r => completedPrice unused (resourceAction r))
        (ownPanelCache panel150 before) (panelDemand panel150 event.terminal) :=
  panel_actual_bill_append_atomic _ _ _ _

theorem native_after_larger_actual_target_extends_own_history (tape : SharedTape) (c : ℝ)
    (penalty : List (TreeEvaluation Act) → List Act → Act → ℝ)
    (actualBill : List (TreeEvaluation Act) → ℝ) (small large : ℝ) (hB : small ≤ large)
    (reward : List Act → ℝ) (fuel : ℕ) (before : List (TreeEvaluation Act)) :
    nativeAfter tape c penalty actualBill small reward fuel before <+:
      nativeAfter tape c penalty actualBill large reward fuel before := by
  induction fuel generalizing before with
  | zero => exact ⟨[],by simp [nativeAfter]⟩
  | succ fuel ih =>
      simp only [nativeAfter]
      by_cases hs : targetReached (actualBill before) small
      · rw [if_pos hs]
        by_cases hl : targetReached (actualBill before) large
        · rw [if_pos hl]
        · rw [if_neg hl]
          exact (List.prefix_append _ _).trans (native_after_initial_prefix _ _ _ _ _ _ _ _)
      · have hl : ¬ targetReached (actualBill before) large := by
          intro hl; exact hs (hB.trans hl)
        rw [if_neg hs,if_neg hl]
        exact ih _

theorem own_control_continuation_preserves_earlier_cache_means_and_bills
    (Cref B epsilon : ℝ) (unused : Act → Fin 8 → ℕ) (mode : ForecastMode)
    (adverse : Bool) (cap extra : ℕ) (hcap : 8 ≤ cap) (qid : Fin 150) :
    let earlier := controlRun Cref B epsilon unused mode adverse cap
    let laterPrefix := (controlRun Cref B epsilon unused mode adverse (cap+extra)).take earlier.length
    ownPanelCache panel150 laterPrefix = ownPanelCache panel150 earlier ∧
      observedMeans panel150 (completedPrice unused) (completedCaps epsilon) qid laterPrefix =
        observedMeans panel150 (completedPrice unused) (completedCaps epsilon) qid earlier ∧
      completedBill unused laterPrefix = completedBill unused earlier ∧
      replayBackup laterPrefix emptyStatistics = replayBackup earlier emptyStatistics := by
  have hp := own_control_smaller_cap_is_prefix Cref B epsilon unused mode adverse cap extra hcap
  obtain ⟨rest,hp⟩ := hp
  have ht : (controlRun Cref B epsilon unused mode adverse (cap+extra)).take
      (controlRun Cref B epsilon unused mode adverse cap).length =
      controlRun Cref B epsilon unused mode adverse cap := by
    rw [← hp]; simp
  dsimp only
  rw [ht]
  exact ⟨rfl,rfl,rfl,rfl⟩

end AgentUCT32MContinuation
