import CompanionWindowDiagnostics




set_option autoImplicit false
set_option maxRecDepth 16384
set_option maxHeartbeats 4000000
noncomputable section
namespace AgentUCTSavedBudget
open AgentUCTObservability AgentUCTObservabilityBoundary AgentUCTPhysicalDiagnostic
  AgentUCTNativeBudget AgentUCTPanelAllocation AgentUCTNativeRepair AgentUCTNativeRefinement AgentUCTPaper

def controlPenalty (Cref epsilon : ℝ) (unused : Act → Fin 8 → ℕ) (mode : ForecastMode) :=
  observedPenalty panel150 mode (completedPrice unused) (completedPriors epsilon unused)
    (completedCaps epsilon) 0 2 Cref

def controlRun (Cref B epsilon : ℝ) (unused : Act → Fin 8 → ℕ)
    (mode : ForecastMode) (adverse : Bool) (cap : ℕ) :=
  nativeGenerate budgetTape (7/5) (controlPenalty Cref epsilon unused mode)
    (completedBill unused) B (taskReward adverse (2/5) (1/2)) cap

theorem interval_panel_scale (Cref : ℝ) : penaltyScale panel150 2 Cref = (150:ℝ)*2/Cref := by
  simp only [penaltyScale,AgentUCTNativeBudget.panel150_cardinality]
  ring

theorem control_five_causal_events (Cref epsilon : ℝ) (unused : Act → Fin 8 → ℕ)
    (adverse : Bool) (hC : ReferenceControlInterval Cref)
    (hp : AdmissibleInitialPrices integerTariffs (perturbedPriors integerTariffs epsilon)
      (perturbedCaps integerTariffs epsilon) epsilon)
    (he : ErrorMargins integerTariffs (7/5) ((150:ℝ)*2/Cref) (2/5) (1/2)
      (10*((150:ℝ)*2/Cref)*epsilon)) :
    nativeEvent budgetTape (7/5) (controlPenalty Cref epsilon unused .complete)
      (taskReward adverse (2/5) (1/2)) (initialization (taskReward adverse (2/5) (1/2))) =
        aColdEvent (taskReward adverse (2/5) (1/2)) ∧
    nativeEvent budgetTape (7/5) (controlPenalty Cref epsilon unused .next)
      (taskReward adverse (2/5) (1/2)) (initialization (taskReward adverse (2/5) (1/2))) =
        bColdEvent (taskReward adverse (2/5) (1/2)) ∧
    nativeEvent budgetTape (7/5) (controlPenalty Cref epsilon unused .complete)
      (taskReward adverse (2/5) (1/2)) (aNine (taskReward adverse (2/5) (1/2))) =
        aWarmEvent (taskReward adverse (2/5) (1/2)) ∧
    nativeEvent budgetTape (7/5) (controlPenalty Cref epsilon unused .complete)
      (taskReward adverse (2/5) (1/2)) (aTen (taskReward adverse (2/5) (1/2))) =
        aCrossEvent (taskReward adverse (2/5) (1/2)) ∧
    nativeEvent budgetTape (7/5) (controlPenalty Cref epsilon unused .next)
      (taskReward adverse (2/5) (1/2)) (bNine (taskReward adverse (2/5) (1/2))) =
        aColdEvent (taskReward adverse (2/5) (1/2)) := by
  let reward := taskReward adverse (2/5) (1/2)
  have hcpos : 0 < Cref := by rcases hC with ⟨hl,hu⟩; linarith
  have hscale : 0 ≤ (2:ℝ)/Cref := by positivity
  have hm : RootMargins integerTariffs (7/5) (penaltyScale panel150 2 Cref) (2/5) (1/2) := by
    rw [interval_panel_scale]; exact interval_root_margins Cref hC
  have herr : ErrorMargins integerTariffs (7/5) (penaltyScale panel150 2 Cref) (2/5) (1/2)
      (10*(penaltyScale panel150 2 Cref)*epsilon) := by
    rw [interval_panel_scale]; exact he
  have hra : 0 ≤ reward aCold := by
    dsimp only [reward]; rw [(task_cold_rewards adverse (2/5) (1/2)).1]; cases adverse <;> norm_num
  have hrb : reward bCold ≤ (1/2:ℝ) := by
    dsimp only [reward]; rw [(task_cold_rewards adverse (2/5) (1/2)).2.1]; cases adverse <;> norm_num
  obtain ⟨h1,h2,h3,h4,h5⟩ := causal_five_event_outputs panel150 integerTariffs
    (perturbedPriors integerTariffs epsilon) (perturbedCaps integerTariffs epsilon) (0:Fin 150)
    reward (2/5) (1/2) (7/5) 2 Cref epsilon hscale hp
    (task_seed_table adverse (2/5) (1/2)) hra hrb hm herr
  have ha := completed_price_agrees_on_all_observed_actions unused
  have hi := completed_initial_prices_agree epsilon unused
  have hcomm (before : List (TreeEvaluation Act)) (hh : SelectionCheckpoint reward before) (mode : ForecastMode) :
      nativeEvent budgetTape (7/5)
        (causalPenalty panel150 mode integerTariffs (perturbedPriors integerTariffs epsilon)
          (perturbedCaps integerTariffs epsilon) (0:Fin 150) 2 Cref) reward before =
      nativeEvent budgetTape (7/5) (controlPenalty Cref epsilon unused mode) reward before :=
    observed_checkpoint_events_equal panel150 (tariff integerTariffs) (completedPrice unused)
      _ _ _ _ (0:Fin 150) before reward ha hi.1 hi.2 hh mode (7/5) 2 Cref
  exact ⟨(hcomm _ (Or.inl rfl) .complete).symm.trans h1,
    (hcomm _ (Or.inl rfl) .next).symm.trans h2,
    (hcomm _ (Or.inr (Or.inl rfl)) .complete).symm.trans h3,
    (hcomm _ (Or.inr (Or.inr (Or.inl rfl))) .complete).symm.trans h4,
    (hcomm _ (Or.inr (Or.inr (Or.inr rfl))) .next).symm.trans h5⟩

theorem control_prefixes_with_native_remainder (Cref B epsilon : ℝ)
    (unused : Act → Fin 8 → ℕ) (adverse : Bool) (cap : ℕ) (hcap : 11 ≤ cap)
    (hC : ReferenceControlInterval Cref)
    (hp : AdmissibleInitialPrices integerTariffs (perturbedPriors integerTariffs epsilon)
      (perturbedCaps integerTariffs epsilon) epsilon)
    (he : ErrorMargins integerTariffs (7/5) ((150:ℝ)*2/Cref) (2/5) (1/2)
      (10*((150:ℝ)*2/Cref)*epsilon))
    (hb : completedBill unused (initialization (taskReward adverse (2/5) (1/2))) < B ∧
      completedBill unused (aNine (taskReward adverse (2/5) (1/2))) < B ∧
      completedBill unused (aTen (taskReward adverse (2/5) (1/2))) < B ∧
      completedBill unused (bNine (taskReward adverse (2/5) (1/2))) < B) :
    controlRun Cref B epsilon unused .complete adverse cap =
      nativeAfter budgetTape (7/5) (controlPenalty Cref epsilon unused .complete) (completedBill unused)
        B (taskReward adverse (2/5) (1/2)) (cap-11) (aEleven (taskReward adverse (2/5) (1/2))) ∧
    controlRun Cref B epsilon unused .next adverse cap =
      nativeAfter budgetTape (7/5) (controlPenalty Cref epsilon unused .next) (completedBill unused)
        B (taskReward adverse (2/5) (1/2)) (cap-10) (bTen (taskReward adverse (2/5) (1/2))) := by
  obtain ⟨h1,h2,h3,h4,h5⟩ := control_five_causal_events Cref epsilon unused adverse hC hp he
  constructor
  · unfold controlRun nativeGenerate
    rw [budget_common_eight_initialization,show cap-8 = (cap-11)+3 by omega,
      show (cap-11)+3 = ((cap-11)+2)+1 by omega,nativeAfter]
    simp only [targetReached]
    rw [if_neg (not_le.mpr hb.1),h1]
    change nativeAfter budgetTape (7/5) _ _ B _ ((cap-11)+2) (aNine _) = _
    rw [show (cap-11)+2 = ((cap-11)+1)+1 by omega,nativeAfter]
    simp only [targetReached]
    rw [if_neg (not_le.mpr hb.2.1),h3]
    change nativeAfter budgetTape (7/5) _ _ B _ ((cap-11)+1) (aTen _) = _
    rw [nativeAfter]
    simp only [targetReached]
    rw [if_neg (not_le.mpr hb.2.2.1),h4]
    rfl
  · unfold controlRun nativeGenerate
    rw [budget_common_eight_initialization,show cap-8 = (cap-10)+2 by omega,
      show (cap-10)+2 = ((cap-10)+1)+1 by omega,nativeAfter]
    simp only [targetReached]
    rw [if_neg (not_le.mpr hb.1),h2]
    change nativeAfter budgetTape (7/5) _ _ B _ ((cap-10)+1) (bNine _) = _
    rw [nativeAfter]
    simp only [targetReached]
    rw [if_neg (not_le.mpr hb.2.2.2),h5]
    rfl

theorem saved32M_common_generated_prefix_inputs_nonempty (cap : ℕ) (hcap : 11 ≤ cap) :
    ∃ epsilon : ℝ,0 < epsilon ∧ StaticUnusedInvoices unitRoleUnused ∧
      ∀ adverse : Bool,
      controlRun savedCref savedTarget epsilon unitRoleUnused .complete adverse cap =
        nativeAfter budgetTape (7/5) (controlPenalty savedCref epsilon unitRoleUnused .complete)
          (completedBill unitRoleUnused) savedTarget (taskReward adverse (2/5) (1/2)) (cap-11)
          (aEleven (taskReward adverse (2/5) (1/2))) ∧
      controlRun savedCref savedTarget epsilon unitRoleUnused .next adverse cap =
        nativeAfter budgetTape (7/5) (controlPenalty savedCref epsilon unitRoleUnused .next)
          (completedBill unitRoleUnused) savedTarget (taskReward adverse (2/5) (1/2)) (cap-10)
          (bTen (taskReward adverse (2/5) (1/2))) := by
  obtain ⟨e,he,hp,hm⟩ := interval_nonzero_quote_error_inputs savedCref saved_reference_in_control_interval
  refine ⟨e,he,unit_role_unused_is_feasible,?_⟩
  intro adverse
  exact control_prefixes_with_native_remainder savedCref savedTarget e unitRoleUnused adverse cap hcap
    saved_reference_in_control_interval hp hm (initial_checkpoints_below_saved_target _ _)

end AgentUCTSavedBudget
