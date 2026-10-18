import DefaultBudgetP1




set_option autoImplicit false
noncomputable section
namespace AgentUCTCanonicalBridge
open AgentUCTPaper Finset



def parameterTokenBill {Field : Type*} [DecidableEq Field]
    (fields : Finset Field) (parameterWeights : Field → ℝ) (tokens : Field → ℕ) : ℝ :=
  ∑ field ∈ fields, (tokens field : ℝ) * parameterWeights field

theorem parameterTokenBill_nonnegative {Field : Type*} [DecidableEq Field]
    (fields : Finset Field) (weights : Field → ℝ) (tokens : Field → ℕ)
    (hw : ∀ field ∈ fields, 0 ≤ weights field) :
    0 ≤ parameterTokenBill fields weights tokens := by
  exact Finset.sum_nonneg fun field hf => mul_nonneg (Nat.cast_nonneg _) (hw field hf)

theorem no_tokens_no_charge {Field : Type*} [DecidableEq Field]
    (fields : Finset Field) (weights : Field → ℝ) (tokens : Field → ℕ)
    (hzero : ∀ field ∈ fields, tokens field = 0) :
    parameterTokenBill fields weights tokens = 0 := by
  unfold parameterTokenBill
  apply Finset.sum_eq_zero
  intro field hf
  simp [hzero field hf]

theorem positive_charge_requires_model_tokens {Field : Type*} [DecidableEq Field]
    (fields : Finset Field) (weights : Field → ℝ) (tokens : Field → ℕ)
    (hp : 0 < parameterTokenBill fields weights tokens) :
    ∃ field ∈ fields, 0 < tokens field := by
  by_contra hn
  push_neg at hn
  have hz : ∀ field ∈ fields, tokens field = 0 := by
    intro field hf
    have h := hn field hf
    omega
  have hbill := no_tokens_no_charge fields weights tokens hz
  linarith

theorem positive_h_cannot_be_zero_model_work {Field : Type*} [DecidableEq Field]
    (fields : Finset Field) (weights : Field → ℝ) (tokens : Field → ℕ) (h : ℝ)
    (hh : 0 < h) (hactual : h = parameterTokenBill fields weights tokens)
    (hzero : ∀ field ∈ fields, tokens field = 0) : False := by
  have hb := no_tokens_no_charge fields weights tokens hzero
  linarith

variable {Qid Action : Type*} [DecidableEq Qid] [DecidableEq Action]



theorem warm_meter_step_zero
    (qids : Finset Qid) (executionPath : List Action → List Action)
    (weight : Qid × List Action → ℝ)
    (initial : MeteredTreeState Qid Action) (event : TreeEvaluation Action)
    (hwarm : panelDemand qids (executionPath event.terminal) ⊆ initial.materialized) :
    (meterStep qids executionPath weight (fun _ => 0) initial event).materialized =
        initial.materialized ∧
    (meterStep qids executionPath weight (fun _ => 0) initial event).totalPaid =
        initial.totalPaid ∧
    (meterStep qids executionPath weight (fun _ => 0) initial event).stats =
        backupEvent initial.stats event := by
  have hc := cached_demand_is_free weight initial.materialized
    (panelDemand qids (executionPath event.terminal)) hwarm
  have hu := Finset.union_eq_left.mpr hwarm
  refine ⟨hu, ?_, rfl⟩
  change (initial.coldPaid + coldWork weight initial.materialized
    (panelDemand qids (executionPath event.terminal))) + (initial.overheadPaid + 0) =
      initial.coldPaid + initial.overheadPaid
  rw [hc]
  ring

theorem warm_replay_cache_fixed
    (qids : Finset Qid) (executionPath : List Action → List Action)
    (weight : Qid × List Action → ℝ)
    (events : List (TreeEvaluation Action)) (initial : MeteredTreeState Qid Action)
    (hwarm : ∀ e ∈ events, panelDemand qids (executionPath e.terminal) ⊆ initial.materialized) :
    (replayMetered qids executionPath weight (fun _ => 0) events initial).materialized =
      initial.materialized := by
  induction events generalizing initial with
  | nil => rfl
  | cons event events ih =>
    have hm := (warm_meter_step_zero qids executionPath weight initial event
      (hwarm event (by simp))).1
    change (replayMetered qids executionPath weight (fun _ => 0) events
      (meterStep qids executionPath weight (fun _ => 0) initial event)).materialized = _
    rw [ih]
    · exact hm
    · intro e he
      rw [hm]
      exact hwarm e (by simp [he])

theorem warm_replay_actual_charge_zero
    (qids : Finset Qid) (executionPath : List Action → List Action)
    (weight : Qid × List Action → ℝ)
    (events : List (TreeEvaluation Action)) (initial : MeteredTreeState Qid Action)
    (hwarm : ∀ e ∈ events, panelDemand qids (executionPath e.terminal) ⊆ initial.materialized) :
    (replayMetered qids executionPath weight (fun _ => 0) events initial).totalPaid =
      initial.totalPaid := by
  have hc := warm_replay_cache_fixed qids executionPath weight events initial hwarm
  have ht := replayMetered_total qids executionPath weight (fun _ => 0) events initial
  rw [hc] at ht
  exact sub_eq_zero.mp (by simpa using ht)



theorem warm_replay_root_visits
    (qids : Finset Qid) (executionPath : List Action → List Action)
    (weight : Qid × List Action → ℝ)
    (events : List (TreeEvaluation Action)) (initial : MeteredTreeState Qid Action) :
    ((replayMetered qids executionPath weight (fun _ => 0) events initial).stats []).visits =
      (initial.stats []).visits + events.length := by
  rw [replayMetered_stats, replayBackup_visits]
  simp [backedCount]

theorem warm_replay_cannot_reach_cost_target
    (qids : Finset Qid) (executionPath : List Action → List Action)
    (weight : Qid × List Action → ℝ)
    (events : List (TreeEvaluation Action)) (initial : MeteredTreeState Qid Action) (B : ℝ)
    (hwarm : ∀ e ∈ events, panelDemand qids (executionPath e.terminal) ⊆ initial.materialized)
    (hB : initial.totalPaid < B) :
    ¬ B ≤ (replayMetered qids executionPath weight (fun _ => 0) events initial).totalPaid := by
  rw [warm_replay_actual_charge_zero qids executionPath weight events initial hwarm]
  exact not_le.mpr hB



theorem fully_warm_any_legal_run_cannot_cross
    (qids : Finset Qid) (root : List Action) (terminals : Finset (List Action))
    (weight : Qid × List Action → ℝ)
    (events : List (TreeEvaluation Action)) (initial : MeteredTreeState Qid Action) (B : ℝ)
    (hresources : workflowResources qids root terminals ⊆ initial.materialized)
    (hlegal : ∀ e ∈ events, e.terminal ∈ terminals) (hB : initial.totalPaid < B) :
    ¬ B ≤ (replayMetered qids (fun p => root ++ p) weight (fun _ => 0) events initial).totalPaid := by
  apply warm_replay_cannot_reach_cost_target qids (fun p => root ++ p) weight events initial B _ hB
  intro e he
  exact (terminal_demand_subset_resources qids root terminals e.terminal (hlegal e he)).trans hresources



theorem zero_overhead_budget_above_all_cold_work_unreachable
    (qids : Finset Qid) (root : List Action) (terminals : Finset (List Action))
    (weight : Qid × List Action → ℝ) (hw : ∀ resource, 0 ≤ weight resource)
    (events : List (TreeEvaluation Action)) (initial : MeteredTreeState Qid Action) (B : ℝ)
    (hinit : initial.materialized ⊆ workflowResources qids root terminals)
    (hlegal : ∀ e ∈ events, e.terminal ∈ terminals)
    (hB : cacheWeight weight (workflowResources qids root terminals) -
      cacheWeight weight initial.materialized < B) :
    ¬ B ≤ meteredSearchCost qids root weight (fun _ => 0) events initial := by
  have hb := meteredSearchCost_upper qids root terminals weight hw (fun _ => 0)
    events initial hinit hlegal
  simp only [List.map_const', List.sum_replicate, smul_zero, add_zero] at hb
  exact not_le.mpr (lt_of_le_of_lt hb hB)

inductive StopReason where
  | cost
  | evaluationCap
  | continueRun
  deriving DecidableEq



def stopReason (completed cap : ℕ) (actualSpent B : ℝ) : StopReason :=
  if B ≤ actualSpent then .cost else if cap ≤ completed then .evaluationCap else .continueRun

theorem zero_bill_run_stops_at_cap (completed cap : ℕ) (spent B : ℝ)
    (hB : spent < B) (hcap : cap ≤ completed) :
    stopReason completed cap spent B = .evaluationCap := by
  simp [stopReason, not_le.mpr hB, hcap]

theorem zero_bill_below_cap_continues (completed cap : ℕ) (spent B : ℝ)
    (hB : spent < B) (hcap : completed < cap) :
    stopReason completed cap spent B = .continueRun := by
  simp [stopReason, not_le.mpr hB, not_le.mpr hcap]

end AgentUCTCanonicalBridge
