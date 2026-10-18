import NativePrefixContinuation




set_option autoImplicit false
set_option maxRecDepth 16384
set_option maxHeartbeats 4000000
noncomputable section
namespace AgentUCTSavedBudget
open AgentUCTObservability AgentUCTObservabilityBoundary AgentUCTPhysicalDiagnostic
  AgentUCTNativeBudget AgentUCTPanelAllocation AgentUCTNativeRepair AgentUCTNativeRefinement AgentUCTPaper

theorem affordable_prefix_is_retained (unused : Act → Fin 8 → ℕ)
    (before events : List (TreeEvaluation Act)) (B tolerance : ℝ) (hp : before <+: events)
    (hfit : affordable (completedBill unused before) B tolerance) :
    before <+: panelReported panel150 (fun r => completedPrice unused (resourceAction r)) events B tolerance := by
  classical
  obtain ⟨rest,rfl⟩ := hp
  have htake : (before++rest).take before.length = before := by simp
  have hindex : before.length ≤ panelReportingIndex panel150
      (fun r => completedPrice unused (resourceAction r)) (before++rest) B tolerance := by
    unfold panelReportingIndex T_B
    apply Finset.le_sup (f := id)
    apply Finset.mem_filter.mpr
    constructor
    · apply Finset.mem_range.mpr
      simp only [List.length_append]
      omega
    · change affordable (panelActualBill panel150 (fun r => completedPrice unused (resourceAction r))
        ((before++rest).take before.length)) B tolerance
      rw [htake]
      exact hfit
  unfold panelReported
  have hh := List.take_prefix_take_left (l := before++rest) hindex
  rwa [htake] at hh

theorem native_after_global_reward_bound (tape : SharedTape) (c : ℝ)
    (penalty : List (TreeEvaluation Act) → List Act → Act → ℝ)
    (actualBill : List (TreeEvaluation Act) → ℝ) (B : ℝ) (reward : List Act → ℝ)
    (fuel : ℕ) (before : List (TreeEvaluation Act)) (upper : ℝ)
    (hglobal : ∀ path,reward path ≤ upper) (hb : ∀ e ∈ before,e.reward ≤ upper) :
    ∀ e ∈ nativeAfter tape c penalty actualBill B reward fuel before,e.reward ≤ upper := by
  induction fuel generalizing before with
  | zero => exact hb
  | succ fuel ih =>
      simp only [nativeAfter]
      split_ifs
      · exact hb
      · apply ih
        intro e he
        simp only [List.mem_append,List.mem_singleton] at he
        rcases he with he | rfl
        · exact hb e he
        · exact hglobal _

theorem favorable_global_quality_upper (path : List Act) :
    taskReward false (2/5) (1/2) path ≤ (1/2:ℝ) := by
  unfold taskReward
  split_ifs <;> norm_num

theorem favorable_control_run_quality_upper (Cref B epsilon : ℝ) (unused : Act → Fin 8 → ℕ)
    (mode : ForecastMode) (cap : ℕ) :
    ∀ e ∈ controlRun Cref B epsilon unused mode false cap,e.reward ≤ (1/2:ℝ) := by
  unfold controlRun nativeGenerate
  rw [budget_common_eight_initialization]
  apply native_after_global_reward_bound _ _ _ _ _ _ _ _ _ favorable_global_quality_upper
  intro e he
  rcases initialization_event_quality _ (2/5) (task_seed_table false (2/5) (1/2)) e he with h0 | hd
  · rw [h0]; norm_num
  · rw [hd]; norm_num

theorem saved32M_favorable_reported_quality_saturated (Cref epsilon : ℝ)
    (unused : Act → Fin 8 → ℕ) (cap : ℕ) (tolerance : ℝ) (hcap : 11 ≤ cap)
    (ht : 0 ≤ tolerance) (hC : ReferenceControlInterval Cref)
    (hp : AdmissibleInitialPrices integerTariffs (perturbedPriors integerTariffs epsilon)
      (perturbedCaps integerTariffs epsilon) epsilon)
    (he : ErrorMargins integerTariffs (7/5) ((150:ℝ)*2/Cref) (2/5) (1/2)
      (10*((150:ℝ)*2/Cref)*epsilon)) :
    completedValue (panelReported panel150 (fun r => completedPrice unused (resourceAction r))
      (controlRun Cref savedTarget epsilon unused .complete false cap) savedTarget tolerance) = (1/2:ℝ) ∧
    completedValue (panelReported panel150 (fun r => completedPrice unused (resourceAction r))
      (controlRun Cref savedTarget epsilon unused .next false cap) savedTarget tolerance) = (1/2:ℝ) := by
  let reward := taskReward false (2/5) (1/2)
  obtain ⟨ha,hb⟩ := control_prefixes_with_native_remainder Cref savedTarget epsilon unused false cap hcap hC hp he
    (initial_checkpoints_below_saved_target _ _)
  have hpa : aEleven reward <+: controlRun Cref savedTarget epsilon unused .complete false cap := by
    rw [ha]
    exact native_after_initial_prefix _ _ _ _ _ _ _ _
  have hpb : bTen reward <+: controlRun Cref savedTarget epsilon unused .next false cap := by
    rw [hb]
    exact native_after_initial_prefix _ _ _ _ _ _ _ _
  have hbills := companion_whole_bills_below_saved_target unused reward
  have hfa : affordable (completedBill unused (aEleven reward)) savedTarget tolerance := by
    exact hbills.1.le.trans (le_add_of_nonneg_right ht)
  have hfb : affordable (completedBill unused (bTen reward)) savedTarget tolerance := by
    exact hbills.2.le.trans (le_add_of_nonneg_right ht)
  have hreta := affordable_prefix_is_retained unused _ _ savedTarget tolerance hpa hfa
  have hretb := affordable_prefix_is_retained unused _ _ savedTarget tolerance hpb hfb
  have haMem : aColdEvent reward ∈ aEleven reward := by simp [aEleven,aTen,aNine]
  have hbMem : aColdEvent reward ∈ bTen reward := by simp [bTen]
  have hg : (aColdEvent reward).reward = (1/2:ℝ) := by
    simpa only [aColdEvent,routeEvent] using (task_cold_rewards false (2/5) (1/2)).1
  constructor
  · apply completed_value_from_witness
    · intro e hem
      apply favorable_control_run_quality_upper Cref savedTarget epsilon unused .complete cap e
      exact List.mem_of_mem_take hem
    · exact ⟨aColdEvent reward,hreta.sublist.subset haMem,hg⟩
  · apply completed_value_from_witness
    · intro e hem
      apply favorable_control_run_quality_upper Cref savedTarget epsilon unused .next cap e
      exact List.mem_of_mem_take hem
    · exact ⟨aColdEvent reward,hretb.sublist.subset hbMem,hg⟩

theorem saved32M_saturation_input_class_inhabited (cap : ℕ) (hcap : 11 ≤ cap) :
    ∃ epsilon : ℝ,0 < epsilon ∧ StaticUnusedInvoices unitRoleUnused ∧
      completedValue (panelReported panel150 (fun r => completedPrice unitRoleUnused (resourceAction r))
        (controlRun savedCref savedTarget epsilon unitRoleUnused .complete false cap) savedTarget (1/10000000)) = (1/2:ℝ) ∧
      completedValue (panelReported panel150 (fun r => completedPrice unitRoleUnused (resourceAction r))
        (controlRun savedCref savedTarget epsilon unitRoleUnused .next false cap) savedTarget (1/10000000)) = (1/2:ℝ) := by
  obtain ⟨e,he,hp,hm⟩ := interval_nonzero_quote_error_inputs savedCref saved_reference_in_control_interval
  exact ⟨e,he,unit_role_unused_is_feasible,saved32M_favorable_reported_quality_saturated savedCref e
    unitRoleUnused cap (1/10000000) hcap (by norm_num) saved_reference_in_control_interval hp hm⟩

def controlNet (Cref B epsilon : ℝ) (unused : Act → Fin 8 → ℕ)
    (mode : ForecastMode) (adverse : Bool) (cap : ℕ) (tolerance : ℝ) :=
  observedHistoryNet panel150 (completedPrice unused) (controlRun Cref B epsilon unused mode adverse cap)
    B tolerance (1/20) Cref

theorem saturated_saved32M_net_difference_uses_retained_bills (Cref epsilon : ℝ)
    (unused : Act → Fin 8 → ℕ) (cap : ℕ) (tolerance : ℝ) (hcap : 11 ≤ cap)
    (ht : 0 ≤ tolerance) (hC : ReferenceControlInterval Cref)
    (hp : AdmissibleInitialPrices integerTariffs (perturbedPriors integerTariffs epsilon)
      (perturbedCaps integerTariffs epsilon) epsilon)
    (he : ErrorMargins integerTariffs (7/5) ((150:ℝ)*2/Cref) (2/5) (1/2)
      (10*((150:ℝ)*2/Cref)*epsilon)) :
    controlNet Cref savedTarget epsilon unused .complete false cap tolerance -
      controlNet Cref savedTarget epsilon unused .next false cap tolerance =
    (1/20)*(completedBill unused (panelReported panel150 (fun r => completedPrice unused (resourceAction r))
        (controlRun Cref savedTarget epsilon unused .next false cap) savedTarget tolerance)-
      completedBill unused (panelReported panel150 (fun r => completedPrice unused (resourceAction r))
        (controlRun Cref savedTarget epsilon unused .complete false cap) savedTarget tolerance))/Cref := by
  obtain ⟨ha,hb⟩ := saved32M_favorable_reported_quality_saturated Cref epsilon unused cap tolerance hcap ht hC hp he
  unfold controlNet observedHistoryNet
  dsimp only
  rw [ha,hb]
  unfold completedBill
  ring

end AgentUCTSavedBudget
