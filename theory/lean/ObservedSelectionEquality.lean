import ObservedForecastEquality




set_option autoImplicit false
set_option maxRecDepth 16384
set_option maxHeartbeats 4000000
set_option linter.constructorNameAsVariable false
noncomputable section
namespace AgentUCTObservability
open AgentUCTPhysicalDiagnostic AgentUCTNativeBudget AgentUCTPanelAllocation
  AgentUCTNativeRepair AgentUCTNativeRefinement AgentUCTPaper
variable {Qid : Type*} [DecidableEq Qid] [Encodable Qid]

theorem first_maximum_values_congr (f g : Act → ℝ) (choices : List Act)
    (he : ∀ a ∈ choices,f a = g a) : firstMaximum f choices = firstMaximum g choices := by
  induction choices with
  | nil => rfl
  | cons a rest ih =>
      by_cases hn : rest = []
      · subst rest; rfl
      · have hi := ih (fun r hr => he r (List.mem_cons_of_mem _ hr))
        have hm := firstMaximum_member g rest hn
        simp only [firstMaximum,if_neg hn,hi,he a (by simp),he _ (List.mem_cons_of_mem _ hm)]

theorem native_choice_values_congr (f g : Act → ℝ) (before : List (TreeEvaluation Act))
    (p : List Act) (he : ∀ a ∈ orderedLegalAvailable p,f a = g a) :
    nativeFirstChoice f before p = nativeFirstChoice g before p := by
  unfold nativeFirstChoice
  cases hf : (orderedLegalAvailable p).filter (fun a => rawVisits before (p++[a]) = 0) with
  | nil => exact first_maximum_values_congr f g _ he
  | cons a rest => rfl

theorem observed_root_choices_equal (qids : Finset Qid) (f g priors priors' caps caps' : Act → ℝ)
    (qid : Qid) (before : List (TreeEvaluation Act)) (hp : AgreeCovered f g)
    (hprior : AgreeCovered priors priors') (hc : AgreeCovered caps caps') (hh : CoveredHistory qids before)
    (mode : ForecastMode) (c beta Cref : ℝ) :
    nativeFirstChoice (indexScore c (observedPenalty qids mode f priors caps qid beta Cref) before []) before [] =
    nativeFirstChoice (indexScore c (observedPenalty qids mode g priors' caps' qid beta Cref) before []) before [] := by
  apply native_choice_values_congr
  intro a ha
  rw [ordered_legal_root_order] at ha
  obtain ⟨q,_,rfl⟩ := List.mem_map.mp ha
  simp only [indexScore,observed_all_root_penalties_equal qids f g priors priors' caps caps' qid before hp hprior hc hh]

def SelectionCheckpoint (reward : List Act → ℝ) (before : List (TreeEvaluation Act)) : Prop :=
  before = initialization reward ∨ before = aNine reward ∨ before = aTen reward ∨ before = bNine reward

theorem checkpoint_roots_present (reward : List Act → ℝ) (before : List (TreeEvaluation Act))
    (hh : SelectionCheckpoint reward before) : ∀ q : Fin 8,[.query q] ∈ expandedNodes before := by
  rcases hh with rfl | rfl | rfl | rfl
  · intro q; rw [initialization_nodes_exact]; exact roots_in_initial_nodes q
  · intro q; rw [a9_nodes_exact]; exact Finset.mem_insert_of_mem (roots_in_initial_nodes q)
  · intro q; rw [a10_nodes_exact]; exact Finset.mem_insert_of_mem (Finset.mem_insert_of_mem (roots_in_initial_nodes q))
  · intro q; rw [b9_nodes_exact]; exact Finset.mem_insert_of_mem (roots_in_initial_nodes q)

theorem checkpoint_all_roots_still_expand (reward : List Act → ℝ) (before : List (TreeEvaluation Act))
    (hh : SelectionCheckpoint reward before) :
    ∀ q : Fin 8,unexpandedAt (expandedNodes before) [.query q] ≠ [] := by
  rcases hh with rfl | rfl | rfl | rfl
  · rw [initialization_nodes_exact]; intro q; fin_cases q <;> decide
  · rw [a9_nodes_exact]; intro q; fin_cases q <;> decide
  · rw [a10_nodes_exact]; intro q; fin_cases q <;> decide
  · rw [b9_nodes_exact]; intro q; fin_cases q <;> decide

theorem checkpoint_covered (qids : Finset (Fin 150)) (reward : List Act → ℝ)
    (before : List (TreeEvaluation Act)) (hh : SelectionCheckpoint reward before) : CoveredHistory qids before := by
  rcases hh with rfl | rfl | rfl | rfl
  · exact covered_history_prefix qids _ _ (by unfold aEleven aTen aNine; simp) (companion_panel_caches_covered qids reward).1
  · exact covered_history_prefix qids _ _ (by unfold aEleven aTen; simp) (companion_panel_caches_covered qids reward).1
  · exact covered_history_prefix qids _ _ (List.prefix_append _ _) (companion_panel_caches_covered qids reward).1
  · exact covered_history_prefix qids _ _ (List.prefix_append _ _) (companion_panel_caches_covered qids reward).2

theorem root_comparison_complete_event_congruence (before : List (TreeEvaluation Act))
    (reward : List Act → ℝ) (c : ℝ) (f g : List (TreeEvaluation Act) → List Act → Act → ℝ)
    (hroot : ∀ q : Fin 8,f before [] (.query q) = g before [] (.query q))
    (hh : SelectionCheckpoint reward before) :
    nativeEvent budgetTape c f reward before = nativeEvent budgetTape c g reward before := by
  have hchoice : nativeFirstChoice (indexScore c f before []) before [] =
      nativeFirstChoice (indexScore c g before []) before [] := by
    apply native_choice_values_congr
    intro a ha
    rw [ordered_legal_root_order] at ha
    obtain ⟨q,_,rfl⟩ := List.mem_map.mp ha
    simp only [indexScore,hroot q]
  have hm := native_first_choice_member (indexScore c f before []) before []
    (show orderedLegalAvailable [] ≠ [] by decide)
  rw [ordered_legal_root_order] at hm
  obtain ⟨q,_,hq⟩ := List.mem_map.mp hm
  have hf : nativeFirstChoice (indexScore c f before []) before [] = .query q := hq.symm
  have hg : nativeFirstChoice (indexScore c g before []) before [] = .query q := hchoice.symm.trans hf
  exact event_equality_from_same_derived_root before reward c f g q
    (checkpoint_roots_present reward before hh) hf hg (checkpoint_all_roots_still_expand reward before hh q)

theorem observed_checkpoint_events_equal (qids : Finset (Fin 150))
    (f g priors priors' caps caps' : Act → ℝ) (qid : Fin 150)
    (before : List (TreeEvaluation Act)) (reward : List Act → ℝ) (hp : AgreeCovered f g)
    (hprior : AgreeCovered priors priors') (hc : AgreeCovered caps caps')
    (hh : SelectionCheckpoint reward before) (mode : ForecastMode) (c beta Cref : ℝ) :
    nativeEvent budgetTape c (observedPenalty qids mode f priors caps qid beta Cref) reward before =
    nativeEvent budgetTape c (observedPenalty qids mode g priors' caps' qid beta Cref) reward before := by
  apply root_comparison_complete_event_congruence before reward c _ _ _ hh
  intro q
  exact observed_all_root_penalties_equal qids f g priors priors' caps caps' qid before hp hprior hc
    (checkpoint_covered qids reward before hh) mode beta Cref q

end AgentUCTObservability
