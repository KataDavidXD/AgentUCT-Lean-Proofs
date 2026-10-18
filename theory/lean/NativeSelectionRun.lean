import NativeLocalAllocation



set_option autoImplicit false
set_option maxRecDepth 8192
set_option maxHeartbeats 4000000
set_option linter.constructorNameAsVariable false
noncomputable section
namespace AgentUCTPanelAllocation
open AgentUCTNativeRefinement AgentUCTNativeRepair AgentUCTPaper

def nativeSelect (tape : SharedTape) (c : ℝ)
    (penalty : List (TreeEvaluation Act) → List Act → Act → ℝ)
    (before : List (TreeEvaluation Act)) : ℕ → List Act → List Act
  | 0,p => p
  | fuel+1,p =>
    if orderedLegalAvailable p = [] then p else
    let unexpanded := (orderedLegalAvailable p).filter fun a => p++[a] ∉ expandedNodes before
    if unexpanded = [] then
      nativeSelect tape c penalty before fuel
        (p++[nativeFirstChoice (indexScore c penalty before p) before p])
    else p++[tape.action before .expansion p unexpanded]

theorem native_select_prefix (tape : SharedTape) (c : ℝ)
    (penalty : List (TreeEvaluation Act) → List Act → Act → ℝ)
    (before : List (TreeEvaluation Act)) (fuel : ℕ) (p : List Act) :
    p <+: nativeSelect tape c penalty before fuel p := by
  induction fuel generalizing p with
  | zero => exact List.prefix_refl _
  | succ fuel ih =>
      simp only [nativeSelect]
      split_ifs
      · exact List.prefix_refl _
      · exact (List.prefix_append _ _).trans (ih _)
      · exact List.prefix_append _ _

theorem native_select_legal (tape : SharedTape) (ht : LegalSupportedTape tape) (c : ℝ)
    (penalty : List (TreeEvaluation Act) → List Act → Act → ℝ)
    (before : List (TreeEvaluation Act)) (fuel : ℕ) (p : List Act) (hp : Legal p) :
    Legal (nativeSelect tape c penalty before fuel p) := by
  induction fuel generalizing p with
  | zero => exact hp
  | succ fuel ih =>
      simp only [nativeSelect]
      split_ifs with hnil hunexpanded
      · exact hp
      · apply ih
        exact (legal_append_action p _).mpr ⟨hp,(ordered_legal_member_iff hp _).mp
          (native_first_choice_member _ before p hnil)⟩
      · exact supported_action_legal tape ht before .expansion hp _ hunexpanded
          (fun a ha => (ordered_legal_member_iff hp a).mp (List.mem_filter.mp ha).1)

def InsertOutcome (nodes : Finset (List Act)) (expanded : List Act) : Prop :=
  (expanded ∈ nodes ∧ Terminal expanded) ∨
    ∃ p ∈ nodes, ∃ a, expanded = p++[a] ∧ expanded ∉ nodes

theorem native_select_insert_outcome (tape : SharedTape) (ht : LegalSupportedTape tape)
    (c : ℝ) (penalty : List (TreeEvaluation Act) → List Act → Act → ℝ)
    (before : List (TreeEvaluation Act)) (fuel : ℕ) (p : List Act) (hp : Legal p)
    (hnode : p ∈ expandedNodes before) (hfuel : 9 ≤ fuel+p.length) :
    InsertOutcome (expandedNodes before) (nativeSelect tape c penalty before fuel p) := by
  induction fuel generalizing p with
  | zero =>
      change InsertOutcome (expandedNodes before) p
      exact Or.inl ⟨hnode,hp,by have hl := legal_length_le_nine hp; omega⟩
  | succ fuel ih =>
      simp only [nativeSelect]
      split_ifs with hnil hunexpanded
      · exact Or.inl ⟨hnode,(legal_no_actions_iff_terminal hp).mp ((ordered_legal_nil_iff hp).mp hnil)⟩
      · have ha := native_first_choice_member (indexScore c penalty before p) before p hnil
        have hnew : p++[nativeFirstChoice (indexScore c penalty before p) before p] ∈ expandedNodes before := by
          by_contra habsent
          have hm : nativeFirstChoice (indexScore c penalty before p) before p ∈
              (orderedLegalAvailable p).filter (fun a => p++[a] ∉ expandedNodes before) := by
            simp [ha,habsent]
          rw [hunexpanded] at hm
          exact List.not_mem_nil hm
        exact ih _ ((legal_append_action p _).mpr ⟨hp,(ordered_legal_member_iff hp _).mp ha⟩)
          hnew (by simp only [List.length_append,List.length_singleton]; omega)
      · have hm := ht.1 before .expansion p _ hp hunexpanded
          (fun a ha => (ordered_legal_member_iff hp a).mp (List.mem_filter.mp ha).1)
        exact Or.inr ⟨p,hnode,_,rfl,by simpa using (List.mem_filter.mp hm).2⟩

theorem native_select_local_decisions (tape : SharedTape) (ht : LegalSupportedTape tape)
    (c : ℝ) (penalty : List (TreeEvaluation Act) → List Act → Act → ℝ)
    (before : List (TreeEvaluation Act)) (hrun : LegalTreeRun Terminal {[]} before)
    (fuel : ℕ) (p : List Act) (hp : Legal p) (q : List Act) (a : Act)
    (hpq : p <+: q) (hchild : childAfter q (nativeSelect tape c penalty before fuel p) = some a) :
    LocalAllocation c penalty before q a := by
  induction fuel generalizing p q a with
  | zero =>
      have hlen := ((childAfter_some_iff q p a).mp hchild).length_le
      have hlen' := hpq.length_le
      simp only [List.length_append,List.length_singleton] at hlen
      omega
  | succ fuel ih =>
      simp only [nativeSelect] at hchild
      split_ifs at hchild with hnil hunexpanded
      · have hlen := ((childAfter_some_iff q p a).mp hchild).length_le
        have hlen' := hpq.length_le
        simp only [List.length_append,List.length_singleton] at hlen
        omega
      · let chosen := nativeFirstChoice (indexScore c penalty before p) before p
        have ha := native_first_choice_member (indexScore c penalty before p) before p hnil
        by_cases hqp : q = p
        · subst q
          have hs := native_select_prefix tape c penalty before fuel (p++[chosen])
          have hsame : a = chosen := by
            have hchosen := (childAfter_some_iff p _ chosen).mpr hs
            exact Option.some.inj (hchild.symm.trans hchosen)
          subst a
          exact native_first_choice_local_allocation c penalty before p hp hnil
        · have hqpre := (List.prefix_append q [a]).trans ((childAfter_some_iff q _ a).mp hchild)
          have hs := native_select_prefix tape c penalty before fuel (p++[chosen])
          have hlen : (p++[chosen]).length ≤ q.length := by
            have hneq : p.length < q.length := by
              by_contra hn
              exact hqp (hpq.eq_of_length_le (by omega)).symm
            simp only [List.length_append,List.length_singleton]
            omega
          have hsq := List.prefix_of_prefix_length_le hs hqpre hlen
          exact ih _ ((legal_append_action p chosen).mpr
            ⟨hp,(ordered_legal_member_iff hp chosen).mp ha⟩) q a hsq hchild
      · have hm := ht.1 before .expansion p _ hp hunexpanded
          (fun a ha => (ordered_legal_member_iff hp a).mp (List.mem_filter.mp ha).1)
        have hlen := ((childAfter_some_iff q _ a).mp hchild).length_le
        have hlen' := hpq.length_le
        simp only [List.length_append,List.length_singleton] at hlen
        have heq : p = q := hpq.eq_of_length_le (by omega)
        subst q
        have he : a = tape.action before .expansion p
            ((orderedLegalAvailable p).filter fun a => p++[a] ∉ expandedNodes before) := by
          let chosen := tape.action before .expansion p
            ((orderedLegalAvailable p).filter fun a => p++[a] ∉ expandedNodes before)
          have hchosen : childAfter p (p++[chosen]) = some chosen :=
            (childAfter_some_iff p (p++[chosen]) chosen).mpr (List.prefix_refl _)
          exact Option.some.inj (hchild.symm.trans hchosen)
        subst a
        exact newly_expanded_child_local_allocation c penalty before hrun p hp _
          (List.mem_filter.mp hm).1 (by simpa using (List.mem_filter.mp hm).2)

end AgentUCTPanelAllocation
