import RepairGrammar



set_option autoImplicit false
set_option maxRecDepth 16384
set_option maxHeartbeats 4000000
noncomputable section
namespace AgentUCTNativeRepair
open AgentUCTNativeRefinement AgentUCTPaper

def LegalSupportedTape (tape : SharedTape) : Prop :=
  (∀ before phase p candidates, Legal p → candidates ≠ [] →
    (∀ a ∈ candidates, a ∈ available p) →
    tape.action before phase p candidates ∈ candidates) ∧
  (∀ before p a i, Legal p → a ∈ available p →
    Terminal (tape.completion before p a i) ∧
    p++[a] <+: tape.completion before p a i)

def preferredAction (p : List Act) : Act := ((finish p).drop p.length).headD .stop




def explicitTape : SharedTape where
  action := fun _ _ p candidates =>
    if preferredAction p ∈ candidates then preferredAction p else candidates.headD .stop
  completion := fun _ p a _ => finish (p++[a])

theorem explicit_tape_supported : LegalSupportedTape explicitTape := by
  constructor
  · intro before phase p candidates hp hne hsub
    simp only [explicitTape]
    split_ifs with h
    · exact h
    · cases candidates with
      | nil => exact False.elim (hne rfl)
      | cons a rest => simp
  · intro before p a i hp ha
    exact finish_legal_extension ((legal_append_action p a).mpr ⟨hp,ha⟩)

theorem repaired_support_inhabited : ∃ tape : SharedTape, LegalSupportedTape tape :=
  ⟨explicitTape,explicit_tape_supported⟩

theorem ordered_legal_nil_iff {p : List Act} (hp : Legal p) :
    orderedLegalAvailable p = [] ↔ available p = [] := by
  rw [orderedLegalAvailable,legal_available_eq hp]
  constructor
  · intro h
    have hl := congrArg List.length h
    simp only [List.length_insertionSort,List.length_nil] at hl
    exact List.length_eq_zero.mp hl
  · intro h
    rw [h]
    rfl

theorem supported_action_legal (tape : SharedTape) (ht : LegalSupportedTape tape)
    (before : List (TreeEvaluation Act)) (phase : Phase) {p : List Act} (hp : Legal p)
    (candidates : List Act) (hne : candidates ≠ [])
    (hsub : ∀ a ∈ candidates, a ∈ available p) :
    Legal (p++[tape.action before phase p candidates]) := by
  exact (legal_append_action _ _).mpr ⟨hp,hsub _ (ht.1 before phase p candidates hp hne hsub)⟩

def repairedRollout (tape : SharedTape) (before : List (TreeEvaluation Act)) :
    ℕ → List Act → List Act
  | 0,p => p
  | fuel+1,p => if orderedLegalAvailable p = [] then p else
      repairedRollout tape before fuel (p++[tape.action before .rollout p (orderedLegalAvailable p)])

theorem repaired_rollout_prefix (tape : SharedTape) (before : List (TreeEvaluation Act))
    (fuel : ℕ) (p : List Act) : p <+: repairedRollout tape before fuel p := by
  induction fuel generalizing p with
  | zero => exact List.prefix_refl _
  | succ fuel ih =>
      simp only [repairedRollout]
      split_ifs
      · exact List.prefix_refl _
      · exact (List.prefix_append _ _).trans (ih _)

theorem repaired_rollout_terminal (tape : SharedTape) (ht : LegalSupportedTape tape)
    (before : List (TreeEvaluation Act)) (fuel : ℕ) (p : List Act)
    (hp : Legal p) (hfuel : 9 ≤ fuel+p.length) : Terminal (repairedRollout tape before fuel p) := by
  induction fuel generalizing p with
  | zero =>
      change Terminal p
      exact ⟨hp,by have hl := legal_length_le_nine hp; omega⟩
  | succ fuel ih =>
      simp only [repairedRollout]
      split_ifs with hne
      · exact (legal_no_actions_iff_terminal hp).mp ((ordered_legal_nil_iff hp).mp hne)
      · have hl := supported_action_legal tape ht before .rollout hp
          (orderedLegalAvailable p) hne (fun a ha => (ordered_legal_member_iff hp a).mp ha)
        exact ih _ hl (by simp only [List.length_append,List.length_singleton]; omega)

def firstMaximum (score : Act → ℝ) : List Act → Act
  | [] => .stop
  | a::rest => if rest = [] then a else
      let b := firstMaximum score rest
      if score a < score b then b else a

theorem firstMaximum_member (score : Act → ℝ) (choices : List Act) (hne : choices ≠ []) :
    firstMaximum score choices ∈ choices := by
  induction choices with
  | nil => exact False.elim (hne rfl)
  | cons a rest ih =>
      simp only [firstMaximum]
      split_ifs with hrest hscore
      · simp
      · exact List.mem_cons_of_mem _ (ih hrest)
      · simp

def repairedVisitedChoice (mode : ForecastMode) (tape : SharedTape)
    (prices : Unit × List Act → ℝ) (c gamma : ℝ) (before : List (TreeEvaluation Act))
    (p : List Act) : Act :=
  let choices := orderedLegalAvailable p
  match (choices.filter fun a => (replayBackup before emptyStatistics (p++[a])).visits = 0).head? with
  | some a => a
  | none => firstMaximum (nodeScore mode tape prices c gamma before p) choices

theorem repaired_visited_choice_member (mode : ForecastMode) (tape : SharedTape)
    (prices : Unit × List Act → ℝ) (c gamma : ℝ) (before : List (TreeEvaluation Act))
    (p : List Act) (hne : orderedLegalAvailable p ≠ []) :
    repairedVisitedChoice mode tape prices c gamma before p ∈ orderedLegalAvailable p := by
  dsimp only [repairedVisitedChoice]
  cases h : ((orderedLegalAvailable p).filter fun a =>
      (replayBackup before emptyStatistics (p++[a])).visits = 0).head? with
  | none =>
      simp only [h]
      exact firstMaximum_member _ _ hne
  | some a =>
      simp only [h]
      have hm : a ∈ ((orderedLegalAvailable p).filter fun a =>
          (replayBackup before emptyStatistics (p++[a])).visits = 0) :=
        List.mem_of_mem_head? (by rw [h]; simp)
      exact (List.mem_filter.mp hm).1

def repairedSelection (mode : ForecastMode) (tape : SharedTape)
    (prices : Unit × List Act → ℝ) (c gamma : ℝ) (before : List (TreeEvaluation Act)) :
    ℕ → List Act → List Act
  | 0,p => p
  | fuel+1,p =>
    if orderedLegalAvailable p = [] then p else
    let unexpanded := (orderedLegalAvailable p).filter fun a => p++[a] ∉ expandedNodes before
    if unexpanded = [] then
      repairedSelection mode tape prices c gamma before fuel
        (p++[repairedVisitedChoice mode tape prices c gamma before p])
    else p++[tape.action before .expansion p unexpanded]

theorem repaired_selection_legal (mode : ForecastMode) (tape : SharedTape)
    (ht : LegalSupportedTape tape) (prices : Unit × List Act → ℝ) (c gamma : ℝ)
    (before : List (TreeEvaluation Act)) (fuel : ℕ) (p : List Act) (hp : Legal p) :
    Legal (repairedSelection mode tape prices c gamma before fuel p) := by
  induction fuel generalizing p with
  | zero => exact hp
  | succ fuel ih =>
      simp only [repairedSelection]
      split_ifs with hnil hunexpanded
      · exact hp
      · apply ih
        exact (legal_append_action _ _).mpr ⟨hp,(ordered_legal_member_iff hp _).mp
          (repaired_visited_choice_member mode tape prices c gamma before p hnil)⟩
      · exact supported_action_legal tape ht before .expansion hp _ hunexpanded
          (fun a ha => (ordered_legal_member_iff hp a).mp (List.mem_filter.mp ha).1)

def repairedEvent (mode : ForecastMode) (tape : SharedTape)
    (prices : Unit × List Act → ℝ) (c gamma : ℝ) (reward : List Act → ℝ)
    (before : List (TreeEvaluation Act)) : TreeEvaluation Act :=
  let expanded := repairedSelection mode tape prices c gamma before 9 []
  let terminal := repairedRollout tape before 9 expanded
  ⟨expanded,terminal,reward terminal,0,repaired_rollout_prefix tape before 9 expanded⟩

def ValidEvent (event : TreeEvaluation Act) : Prop := Legal event.expanded ∧ Terminal event.terminal
def ValidHistory (events : List (TreeEvaluation Act)) : Prop := ∀ e ∈ events, ValidEvent e

theorem repaired_event_valid (mode : ForecastMode) (tape : SharedTape)
    (ht : LegalSupportedTape tape) (prices : Unit × List Act → ℝ) (c gamma : ℝ)
    (reward : List Act → ℝ) (before : List (TreeEvaluation Act)) :
    ValidEvent (repairedEvent mode tape prices c gamma reward before) := by
  have hl := repaired_selection_legal mode tape ht prices c gamma before 9 [] legal_nil
  exact ⟨hl,repaired_rollout_terminal tape ht before 9 _ hl (by omega)⟩

def initialEvent (tape : SharedTape) (reward : List Act → ℝ)
    (before : List (TreeEvaluation Act)) (q : Fin 8) : TreeEvaluation Act :=
  let terminal := repairedRollout tape before 9 [.query q]
  ⟨[.query q],terminal,reward terminal,0,repaired_rollout_prefix tape before 9 [.query q]⟩

def initializeFrom (tape : SharedTape) (reward : List Act → ℝ) :
    List (Fin 8) → List (TreeEvaluation Act) → List (TreeEvaluation Act)
  | [],before => before
  | q::roots,before => initializeFrom tape reward roots (before++[initialEvent tape reward before q])

def repairedInitialization (tape : SharedTape) (reward : List Act → ℝ) : List (TreeEvaluation Act) :=
  initializeFrom tape reward (List.finRange 8) []

theorem initial_event_valid (tape : SharedTape) (ht : LegalSupportedTape tape)
    (reward : List Act → ℝ) (before : List (TreeEvaluation Act)) (q : Fin 8) :
    ValidEvent (initialEvent tape reward before q) := by
  have hl : Legal [.query q] := by simp [Legal,followLegal,available,rootOrder]
  exact ⟨hl,repaired_rollout_terminal tape ht before 9 _ hl (by simp)⟩

theorem initializeFrom_valid (tape : SharedTape) (ht : LegalSupportedTape tape)
    (reward : List Act → ℝ) (roots : List (Fin 8)) (before : List (TreeEvaluation Act))
    (hb : ValidHistory before) : ValidHistory (initializeFrom tape reward roots before) := by
  induction roots generalizing before with
  | nil => exact hb
  | cons q roots ih =>
      apply ih
      intro e he
      rcases List.mem_append.mp he with he | he
      · exact hb e he
      · have heq : e = initialEvent tape reward before q := by simpa using he
        subst e
        exact initial_event_valid tape ht reward before q

theorem initializeFrom_length (tape : SharedTape) (reward : List Act → ℝ)
    (roots : List (Fin 8)) (before : List (TreeEvaluation Act)) :
    (initializeFrom tape reward roots before).length = before.length+roots.length := by
  induction roots generalizing before with
  | nil => simp [initializeFrom]
  | cons q roots ih => simp [initializeFrom,ih]; omega

theorem repaired_initialization_valid (tape : SharedTape) (ht : LegalSupportedTape tape)
    (reward : List Act → ℝ) : ValidHistory (repairedInitialization tape reward) := by
  exact initializeFrom_valid tape ht reward _ [] (by simp [ValidHistory])

theorem repaired_initialization_eight (tape : SharedTape) (reward : List Act → ℝ) :
    (repairedInitialization tape reward).length = 8 := by
  simp [repairedInitialization,initializeFrom_length]

def repairedAfterInit (mode : ForecastMode) (tape : SharedTape)
    (prices : Unit × List Act → ℝ) (c gamma B : ℝ) (reward : List Act → ℝ) :
    ℕ → List (TreeEvaluation Act) → List (TreeEvaluation Act)
  | 0,before => before
  | fuel+1,before => if targetReached (ownState prices before).totalPaid B then before else
      repairedAfterInit mode tape prices c gamma B reward fuel
        (before++[repairedEvent mode tape prices c gamma reward before])

def repairedGenerate (mode : ForecastMode) (tape : SharedTape)
    (prices : Unit × List Act → ℝ) (c gamma B : ℝ) (cap : ℕ) (reward : List Act → ℝ) :
    List (TreeEvaluation Act) :=
  repairedAfterInit mode tape prices c gamma B reward (cap-8) (repairedInitialization tape reward)

theorem repaired_after_init_valid (mode : ForecastMode) (tape : SharedTape)
    (ht : LegalSupportedTape tape) (prices : Unit × List Act → ℝ) (c gamma B : ℝ)
    (reward : List Act → ℝ) (fuel : ℕ) (before : List (TreeEvaluation Act)) (hb : ValidHistory before) :
    ValidHistory (repairedAfterInit mode tape prices c gamma B reward fuel before) := by
  induction fuel generalizing before with
  | zero => exact hb
  | succ fuel ih =>
      simp only [repairedAfterInit]
      split_ifs
      · exact hb
      · apply ih
        intro e he
        rcases List.mem_append.mp he with he | he
        · exact hb e he
        · have heq : e = repairedEvent mode tape prices c gamma reward before := by simpa using he
          subst e
          exact repaired_event_valid mode tape ht prices c gamma reward before

theorem repaired_generated_legality (mode : ForecastMode) (tape : SharedTape)
    (ht : LegalSupportedTape tape) (prices : Unit × List Act → ℝ) (c gamma B : ℝ)
    (cap : ℕ) (reward : List Act → ℝ) :
    ValidHistory (repairedGenerate mode tape prices c gamma B cap reward) :=
  repaired_after_init_valid mode tape ht prices c gamma B reward _ _
    (repaired_initialization_valid tape ht reward)

theorem explicit_generated_legality (mode : ForecastMode)
    (prices : Unit × List Act → ℝ) (c gamma B : ℝ) (cap : ℕ) (reward : List Act → ℝ) :
    ValidHistory (repairedGenerate mode explicitTape prices c gamma B cap reward) :=
  repaired_generated_legality mode explicitTape explicit_tape_supported prices c gamma B cap reward

end AgentUCTNativeRepair
