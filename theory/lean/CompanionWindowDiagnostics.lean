import SavedControlMargins



set_option autoImplicit false
set_option maxRecDepth 16384
set_option maxHeartbeats 4000000
noncomputable section
namespace AgentUCTSavedBudget
open AgentUCTObservability AgentUCTObservabilityBoundary AgentUCTPhysicalDiagnostic
  AgentUCTNativeBudget AgentUCTPanelAllocation AgentUCTNativeRepair AgentUCTNativeRefinement AgentUCTPaper

def completedBill (unused : Act → Fin 8 → ℕ) (events : List (TreeEvaluation Act)) : ℝ :=
  panelActualBill panel150 (fun r => completedPrice unused (resourceAction r)) events

def CompanionBudgetWindow (B tolerance : ℝ) : Prop :=
  0 ≤ tolerance ∧
  (150:ℝ)*(baseBill integerTariffs+integerTariffs.bge+tailBill integerTariffs) < B ∧
  (150:ℝ)*(baseBill integerTariffs+integerTariffs.normalE5+tailBill integerTariffs) < B ∧
  B+tolerance < (150:ℝ)*(baseBill integerTariffs+integerTariffs.bge+tailBill integerTariffs+crossBill integerTariffs) ∧
  B+tolerance < (150:ℝ)*(baseBill integerTariffs+integerTariffs.normalE5+2*tailBill integerTariffs+integerTariffs.bge)

theorem completed_bill_on_checkpoints (unused : Act → Fin 8 → ℕ) (reward : List Act → ℝ)
    (before : List (TreeEvaluation Act)) (hh : SelectionCheckpoint reward before) :
    completedBill unused before = physicalBill panel150 integerTariffs before :=
  (observed_actual_bills_equal panel150 (tariff integerTariffs) (completedPrice unused) before
    (completed_price_agrees_on_all_observed_actions unused) (checkpoint_covered panel150 reward before hh)).symm

theorem initial_checkpoints_below_saved_target (unused : Act → Fin 8 → ℕ) (reward : List Act → ℝ) :
    completedBill unused (initialization reward) < savedTarget ∧
    completedBill unused (aNine reward) < savedTarget ∧
    completedBill unused (aTen reward) < savedTarget ∧
    completedBill unused (bNine reward) < savedTarget := by
  rw [completed_bill_on_checkpoints unused reward _ (Or.inl rfl),
    completed_bill_on_checkpoints unused reward _ (Or.inr (Or.inl rfl)),
    completed_bill_on_checkpoints unused reward _ (Or.inr (Or.inr (Or.inl rfl))),
    completed_bill_on_checkpoints unused reward _ (Or.inr (Or.inr (Or.inr rfl))),
    physical_initial_bill,physical_a9_bill,physical_a10_bill,physical_b9_bill,
    AgentUCTNativeBudget.panel150_cardinality]
  simp +decide [baseBill,eightBill,integerTariffs,tailBill,finUniv8_explicit,identityQuery]
  norm_num [generatorRate,e5Rate,bgeRate,savedTarget]

theorem task_budget_window_inhabited :
    CompanionBudgetWindow (taskBudget panel150 integerTariffs) (1/10000000) := by
  have hw : StrictResourceWindow (panel150.card : ℝ) integerTariffs (1/10000000) := by
    rw [AgentUCTNativeBudget.panel150_cardinality]; exact beta2_resource_window
  obtain ⟨ha,hb,hac,hbc⟩ := strict_window_endpoints panel150 integerTariffs (fun _ => 0) (1/10000000) hw
  simp only [physical_a10_bill,physical_b9_bill,physical_a11_bill,physical_b10_bill,
    AgentUCTNativeBudget.panel150_cardinality] at ha hb hac hbc
  exact ⟨by norm_num,ha,hb,hac,hbc⟩

theorem saved_target_not_companion_window (tolerance : ℝ) (ht : 0 ≤ tolerance) :
    ¬ CompanionBudgetWindow savedTarget tolerance := by
  intro hw
  have hb := (companion_whole_bills_below_saved_target unitRoleUnused (fun _ => 0)).1
  rw [(completed_raw_and_retained_bills unitRoleUnused (fun _ => 0)).1] at hb
  have hc := hw.2.2.2.1
  dsimp only [savedTarget] at hc
  linarith

theorem companion_window_actual_crossing_bills (unused : Act → Fin 8 → ℕ)
    (reward : List Act → ℝ) (B tolerance : ℝ) (hw : CompanionBudgetWindow B tolerance) :
    completedBill unused (aTen reward) < B ∧ completedBill unused (bNine reward) < B ∧
    B+tolerance < completedBill unused (aEleven reward) ∧
    B+tolerance < completedBill unused (bTen reward) := by
  have hb := completed_raw_and_retained_bills unused reward
  dsimp only [completedBill]
  rw [hb.2.2.1,hb.2.2.2,hb.1,hb.2.1]
  exact ⟨hw.2.1,hw.2.2.1,hw.2.2.2.1,hw.2.2.2.2⟩

theorem companion_window_proper_checkpoints (unused : Act → Fin 8 → ℕ)
    (reward : List Act → ℝ) (B tolerance : ℝ) (hw : CompanionBudgetWindow B tolerance) :
    completedBill unused (initialization reward) < B ∧
    completedBill unused (aNine reward) < B ∧ completedBill unused (aTen reward) < B ∧
    completedBill unused (bNine reward) < B := by
  have ha := hw.2.1
  have hb := hw.2.2.1
  rw [completed_bill_on_checkpoints unused reward _ (Or.inl rfl),
    completed_bill_on_checkpoints unused reward _ (Or.inr (Or.inl rfl)),
    completed_bill_on_checkpoints unused reward _ (Or.inr (Or.inr (Or.inl rfl))),
    completed_bill_on_checkpoints unused reward _ (Or.inr (Or.inr (Or.inr rfl))),
    physical_initial_bill,physical_a9_bill,physical_a10_bill,physical_b9_bill,
    AgentUCTNativeBudget.panel150_cardinality]
  have hx : 0 < integerTariffs.bge+tailBill integerTariffs := by
    norm_num [integerTariffs,tailBill,generatorRate,bgeRate]
  norm_num only [Nat.cast_ofNat]
  exact ⟨by nlinarith,ha,ha,hb⟩

end AgentUCTSavedBudget
