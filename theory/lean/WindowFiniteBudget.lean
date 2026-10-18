import SavedQualitySaturation



set_option autoImplicit false
set_option maxRecDepth 16384
set_option maxHeartbeats 4000000
noncomputable section
namespace AgentUCTSavedBudget
open AgentUCTObservability AgentUCTObservabilityBoundary AgentUCTPhysicalDiagnostic
  AgentUCTNativeBudget AgentUCTPanelAllocation AgentUCTNativeRepair AgentUCTNativeRefinement AgentUCTPaper

theorem interval_retained_gap_bracket (Cref : ℝ) (hC : ReferenceControlInterval Cref) :
    (2/5:ℝ)-1/2 < (1/20)*(150:ℝ)*(integerTariffs.bge-integerTariffs.normalE5)/Cref ∧
    (1/20)*(150:ℝ)*(integerTariffs.bge-integerTariffs.normalE5)/Cref < (1/2:ℝ)-2/5 := by
  have hcpos : 0 < Cref := by rcases hC with ⟨hl,hu⟩; linarith
  constructor
  · rw [lt_div_iff₀ hcpos]
    norm_num [integerTariffs,e5Rate,bgeRate]
    nlinarith [hC.1]
  · rw [div_lt_iff₀ hcpos]
    norm_num [integerTariffs,e5Rate,bgeRate]
    nlinarith [hC.1]

theorem control_window_full_histories_generated (Cref B epsilon tolerance : ℝ)
    (unused : Act → Fin 8 → ℕ) (adverse : Bool) (cap : ℕ) (hcap : 11 ≤ cap)
    (hC : ReferenceControlInterval Cref) (hw : CompanionBudgetWindow B tolerance)
    (hp : AdmissibleInitialPrices integerTariffs (perturbedPriors integerTariffs epsilon)
      (perturbedCaps integerTariffs epsilon) epsilon)
    (he : ErrorMargins integerTariffs (7/5) ((150:ℝ)*2/Cref) (2/5) (1/2)
      (10*((150:ℝ)*2/Cref)*epsilon)) :
    controlRun Cref B epsilon unused .complete adverse cap = aEleven (taskReward adverse (2/5) (1/2)) ∧
    controlRun Cref B epsilon unused .next adverse cap = bTen (taskReward adverse (2/5) (1/2)) := by
  obtain ⟨ha,hb⟩ := control_prefixes_with_native_remainder Cref B epsilon unused adverse cap hcap hC hp he
    (companion_window_proper_checkpoints unused _ B tolerance hw)
  obtain ⟨haf,hbf,hax,hbx⟩ := companion_window_actual_crossing_bills unused _ B tolerance hw
  have hxA : B ≤ completedBill unused (aEleven (taskReward adverse (2/5) (1/2))) := by linarith [hw.1]
  have hxB : B ≤ completedBill unused (bTen (taskReward adverse (2/5) (1/2))) := by linarith [hw.1]
  constructor
  · rw [ha]
    exact native_after_crossing_stops _ _ _ _ _ _ _ hxA _
  · rw [hb]
    exact native_after_crossing_stops _ _ _ _ _ _ _ hxB _

theorem control_window_reporting_indices (unused : Act → Fin 8 → ℕ) (reward : List Act → ℝ)
    (B tolerance : ℝ) (hw : CompanionBudgetWindow B tolerance) :
    panelReportingIndex panel150 (fun r => completedPrice unused (resourceAction r))
      (aEleven reward) B tolerance = 10 ∧
    panelReportingIndex panel150 (fun r => completedPrice unused (resourceAction r))
      (bTen reward) B tolerance = 9 := by
  obtain ⟨ha,hb,hac,hbc⟩ := companion_window_actual_crossing_bills unused reward B tolerance hw
  constructor
  · apply panel_reporting_index_last_complete
    · rw [(resource_history_lengths reward).2.2.1]; omega
    · rw [a11_take10]
      exact ha.le.trans (le_add_of_nonneg_right hw.1)
    · intro n hn hlen
      rw [(resource_history_lengths reward).2.2.1] at hlen
      have he : n = 11 := by omega
      subst n
      rw [List.take_of_length_le (by rw [(resource_history_lengths reward).2.2.1])]
      exact not_le.mpr hac
  · apply panel_reporting_index_last_complete
    · rw [(resource_history_lengths reward).2.2.2.2]; omega
    · rw [b10_take9]
      exact hb.le.trans (le_add_of_nonneg_right hw.1)
    · intro n hn hlen
      rw [(resource_history_lengths reward).2.2.2.2] at hlen
      have he : n = 10 := by omega
      subst n
      rw [List.take_of_length_le (by rw [(resource_history_lengths reward).2.2.2.2])]
      exact not_le.mpr hbc

theorem completed_price_nonnegative (unused : Act → Fin 8 → ℕ) (action : Act) :
    0 ≤ completedPrice unused action := by
  unfold completedPrice modelTokenBill
  exact Finset.sum_nonneg (fun f hf => mul_nonneg (by positivity) (field_weight_bounds f).1)

theorem control_window_strict_whole_crossings (unused : Act → Fin 8 → ℕ)
    (reward : List Act → ℝ) (B tolerance : ℝ) (hw : CompanionBudgetWindow B tolerance) :
    (∀ k,k < 11 → completedBill unused ((aEleven reward).take k) < B) ∧
    B ≤ completedBill unused (aEleven reward) ∧
    (∀ k,k < 10 → completedBill unused ((bTen reward).take k) < B) ∧
    B ≤ completedBill unused (bTen reward) := by
  obtain ⟨ha,hb,hac,hbc⟩ := companion_window_actual_crossing_bills unused reward B tolerance hw
  have hprice : ∀ r : Fin 150 × List Act,0 ≤ completedPrice unused (resourceAction r) :=
    fun r => completed_price_nonnegative unused _
  constructor
  · intro k hk
    have hh := panel_actual_bill_prefix_monotone panel150 _ hprice
      ((aEleven reward).take k) ((aEleven reward).take 10) (List.take_prefix_take_left (by omega))
    rw [a11_take10] at hh
    exact hh.trans_lt ha
  constructor
  · linarith [hw.1]
  constructor
  · intro k hk
    have hh := panel_actual_bill_prefix_monotone panel150 _ hprice
      ((bTen reward).take k) ((bTen reward).take 9) (List.take_prefix_take_left (by omega))
    rw [b10_take9] at hh
    exact hh.trans_lt hb
  · linarith [hw.1]

theorem control_window_reported_prefixes (Cref B epsilon tolerance : ℝ)
    (unused : Act → Fin 8 → ℕ) (adverse : Bool) (cap : ℕ) (hcap : 11 ≤ cap)
    (hC : ReferenceControlInterval Cref) (hw : CompanionBudgetWindow B tolerance)
    (hp : AdmissibleInitialPrices integerTariffs (perturbedPriors integerTariffs epsilon)
      (perturbedCaps integerTariffs epsilon) epsilon)
    (he : ErrorMargins integerTariffs (7/5) ((150:ℝ)*2/Cref) (2/5) (1/2)
      (10*((150:ℝ)*2/Cref)*epsilon)) :
    panelReported panel150 (fun r => completedPrice unused (resourceAction r))
      (controlRun Cref B epsilon unused .complete adverse cap) B tolerance = aTen (taskReward adverse (2/5) (1/2)) ∧
    panelReported panel150 (fun r => completedPrice unused (resourceAction r))
      (controlRun Cref B epsilon unused .next adverse cap) B tolerance = bNine (taskReward adverse (2/5) (1/2)) := by
  obtain ⟨ha,hb⟩ := control_window_full_histories_generated Cref B epsilon tolerance unused adverse cap hcap hC hw hp he
  obtain ⟨hia,hib⟩ := control_window_reporting_indices unused (taskReward adverse (2/5) (1/2)) B tolerance hw
  rw [ha,hb]
  unfold panelReported
  rw [hia,hib,a11_take10,b10_take9]
  exact ⟨rfl,rfl⟩

theorem control_window_positive_and_adverse_net (Cref B epsilon tolerance : ℝ)
    (unused : Act → Fin 8 → ℕ) (cap : ℕ) (hcap : 11 ≤ cap)
    (hC : ReferenceControlInterval Cref) (hw : CompanionBudgetWindow B tolerance)
    (hp : AdmissibleInitialPrices integerTariffs (perturbedPriors integerTariffs epsilon)
      (perturbedCaps integerTariffs epsilon) epsilon)
    (he : ErrorMargins integerTariffs (7/5) ((150:ℝ)*2/Cref) (2/5) (1/2)
      (10*((150:ℝ)*2/Cref)*epsilon)) :
    controlNet Cref B epsilon unused .next false cap tolerance <
      controlNet Cref B epsilon unused .complete false cap tolerance ∧
    controlNet Cref B epsilon unused .complete true cap tolerance <
      controlNet Cref B epsilon unused .next true cap tolerance := by
  have hnetA (adverse : Bool) : controlNet Cref B epsilon unused .complete adverse cap tolerance =
      (if adverse then (2/5:ℝ) else 1/2)-
      (1/20)*((150:ℝ)*(baseBill integerTariffs+integerTariffs.bge+tailBill integerTariffs))/Cref := by
    have hrep := (control_window_reported_prefixes Cref B epsilon tolerance unused adverse cap hcap hC hw hp he).1
    have hbest := (retained_task_best adverse (2/5) (1/2) (by norm_num) (by norm_num)).1
    have hbill := (completed_raw_and_retained_bills unused (taskReward adverse (2/5) (1/2))).2.2.1
    unfold controlNet observedHistoryNet
    dsimp only
    rw [hrep,hbest,hbill]
  have hnetB (adverse : Bool) : controlNet Cref B epsilon unused .next adverse cap tolerance =
      (if adverse then (1/2:ℝ) else 2/5)-
      (1/20)*((150:ℝ)*(baseBill integerTariffs+integerTariffs.normalE5+tailBill integerTariffs))/Cref := by
    have hrep := (control_window_reported_prefixes Cref B epsilon tolerance unused adverse cap hcap hC hw hp he).2
    have hbest := (retained_task_best adverse (2/5) (1/2) (by norm_num) (by norm_num)).2
    have hbill := (completed_raw_and_retained_bills unused (taskReward adverse (2/5) (1/2))).2.2.2
    unfold controlNet observedHistoryNet
    dsimp only
    rw [hrep,hbest,hbill]
  have hg := interval_retained_gap_bracket Cref hC
  have hpos : controlNet Cref B epsilon unused .complete false cap tolerance-
      controlNet Cref B epsilon unused .next false cap tolerance =
      ((1/2:ℝ)-2/5)-(1/20)*(150:ℝ)*(integerTariffs.bge-integerTariffs.normalE5)/Cref := by
    rw [hnetA,hnetB]
    norm_num
    ring
  have hadv : controlNet Cref B epsilon unused .next true cap tolerance-
      controlNet Cref B epsilon unused .complete true cap tolerance =
      ((1/2:ℝ)-2/5)+(1/20)*(150:ℝ)*(integerTariffs.bge-integerTariffs.normalE5)/Cref := by
    rw [hnetB,hnetA]
    norm_num
    ring
  constructor <;> linarith

theorem uniform_control_window_class_inhabited (cap : ℕ) (hcap : 11 ≤ cap) :
    StaticUnusedInvoices unitRoleUnused ∧
      ∀ Cref B tolerance : ℝ,ReferenceControlInterval Cref → CompanionBudgetWindow B tolerance →
        (∀ adverse : Bool,
          controlRun Cref B uniformQuoteError unitRoleUnused .complete adverse cap = aEleven (taskReward adverse (2/5) (1/2)) ∧
          controlRun Cref B uniformQuoteError unitRoleUnused .next adverse cap = bTen (taskReward adverse (2/5) (1/2))) ∧
        controlNet Cref B uniformQuoteError unitRoleUnused .next false cap tolerance <
          controlNet Cref B uniformQuoteError unitRoleUnused .complete false cap tolerance ∧
        controlNet Cref B uniformQuoteError unitRoleUnused .complete true cap tolerance <
          controlNet Cref B uniformQuoteError unitRoleUnused .next true cap tolerance := by
  refine ⟨unit_role_unused_is_feasible,?_⟩
  intro Cref B tolerance hC hw
  obtain ⟨hp,he⟩ := uniform_quote_only_error_inputs Cref hC
  exact ⟨fun adverse => control_window_full_histories_generated Cref B uniformQuoteError tolerance
      unitRoleUnused adverse cap hcap hC hw hp he,
    control_window_positive_and_adverse_net Cref B uniformQuoteError tolerance unitRoleUnused cap hcap hC hw hp he⟩

end AgentUCTSavedBudget
