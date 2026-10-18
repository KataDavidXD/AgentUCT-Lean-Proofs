import NativeBudgetWindow




set_option autoImplicit false
set_option maxRecDepth 16384
set_option maxHeartbeats 4000000
set_option linter.constructorNameAsVariable false
noncomputable section
namespace AgentUCTNativeBudget
open AgentUCTPanelAllocation AgentUCTNativeRepair AgentUCTNativeRefinement AgentUCTPaper

def choosePreferences (preferences candidates : List Act) : Act :=
  match preferences.filter (fun a => a ∈ candidates) with
  | [] => candidates.headD .stop
  | a::_ => a

theorem preferences_choose_candidate (preferences candidates : List Act) (hne : candidates ≠ []) :
    choosePreferences preferences candidates ∈ candidates := by
  unfold choosePreferences
  cases hf : preferences.filter (fun a => a ∈ candidates) with
  | nil => cases candidates <;> simp_all
  | cons a rest =>
      have hh : a ∈ preferences.filter (fun a => a ∈ candidates) := by rw [hf]; simp
      simpa using (List.mem_filter.mp hh).2

def rolloutGoal (p : List Act) : List Act :=
  if p <+: aCold then aCold else if p <+: aWarm then aWarm
  else if p <+: aCross then aCross else if p <+: bCold then bCold else finish p

def routePreferences (before : List (TreeEvaluation Act)) (phase : Phase) (p : List Act) : List Act :=
  if before.length < 8 then [preferredAction p] else
  if phase = .expansion ∧ p = [.query hyde] then [.hydeRetriever 1,.hydeRetriever 0,.hydeRetriever 2] else
  if phase = .expansion ∧ p = [.query branchB] then [.normalRetriever 1,.normalRetriever 0] else
  [((rolloutGoal p).drop p.length).headD .stop]

def mcGoal : List Act → List Act
  | [.query q] => if q = hyde then aCold else fullLeaf q (.normalRetriever 0) 0 1 1 2 0
  | p => rolloutGoal p

def safeCompletion (p : List Act) : List Act :=
  if Terminal (mcGoal p) ∧ p <+: mcGoal p then mcGoal p else finish p

def budgetTape : SharedTape where
  action := fun before phase p candidates => choosePreferences (routePreferences before phase p) candidates
  completion := fun _ p a _ => safeCompletion (p++[a])

theorem safe_completion_legal (p : List Act) (hp : Legal p) :
    Terminal (safeCompletion p) ∧ p <+: safeCompletion p := by
  unfold safeCompletion
  split_ifs with h
  · exact h
  · exact finish_legal_extension hp

theorem budget_tape_supported : LegalSupportedTape budgetTape := by
  constructor
  · intro before phase p candidates hp hne hsub
    exact preferences_choose_candidate _ candidates hne
  · intro before p a i hp ha
    exact safe_completion_legal (p++[a]) ((legal_append_action p a).mpr ⟨hp,ha⟩)

theorem budget_shared_resolver_inhabited : ∃ tape : SharedTape, LegalSupportedTape tape :=
  ⟨budgetTape,budget_tape_supported⟩

theorem before_eight_same_action (before : List (TreeEvaluation Act)) (hb : before.length < 8)
    (phase : Phase) (p candidates : List Act) :
    budgetTape.action before phase p candidates = explicitTape.action before phase p candidates := by
  by_cases h : preferredAction p ∈ candidates <;>
    simp [budgetTape,routePreferences,hb,choosePreferences,explicitTape,h]

theorem before_eight_same_rollout (before : List (TreeEvaluation Act)) (hb : before.length < 8)
    (fuel : ℕ) (p : List Act) :
    repairedRollout budgetTape before fuel p = repairedRollout explicitTape before fuel p := by
  induction fuel generalizing p with
  | zero => rfl
  | succ fuel ih =>
      simp only [repairedRollout]
      split_ifs
      · rfl
      · rw [before_eight_same_action before hb,ih]

theorem budget_initial_event (reward : List Act → ℝ) (before : List (TreeEvaluation Act))
    (hb : before.length < 8) (q : Fin 8) :
    initialEvent budgetTape reward before q = seedEvent reward q := by
  simp only [initialEvent,before_eight_same_rollout before hb,repaired_explicit_seed_terminal]
  rfl

theorem budget_common_eight_initialization (reward : List Act → ℝ) :
    repairedInitialization budgetTape reward = initialization reward := by
  simp [repairedInitialization,finRange8_explicit,initializeFrom,budget_initial_event,
    initialization,seedEvent]

theorem budget_initialization_legal_and_allocation (reward : List Act → ℝ) (c : ℝ)
    (penalty : List (TreeEvaluation Act) → List Act → Act → ℝ) :
    LegalTreeRun Terminal {[]} (initialization reward) ∧
    TreeAllocationRule nativeTerminals c penalty (initialization reward) := by
  rw [← budget_common_eight_initialization]
  exact native_common_initialization_legal_and_allocation budgetTape budget_tape_supported c penalty reward

end AgentUCTNativeBudget
