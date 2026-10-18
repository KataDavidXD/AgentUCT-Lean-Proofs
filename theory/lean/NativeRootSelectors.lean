import NativeRootReference




set_option autoImplicit false
set_option maxRecDepth 16384
set_option maxHeartbeats 4000000
set_option linter.constructorNameAsVariable false
noncomputable section
namespace AgentUCTNativeBudget
open AgentUCTPanelAllocation AgentUCTNativeRepair AgentUCTNativeRefinement AgentUCTPaper
variable {Qid : Type*} [DecidableEq Qid]

def bonusGap2 (c : ℝ) := c*(Real.sqrt (Real.log 10)-Real.sqrt (Real.log 10/2))
def bonusGap3 (c : ℝ) := c*(Real.sqrt (Real.log 11)-Real.sqrt (Real.log 11/3))

structure RootMargins (t : TariffInput) (c gamma delta good : ℝ) : Prop where
  delta_pos : 0 < delta
  delta_le_good : delta ≤ good
  gamma_pos : 0 < gamma
  bge_pos : 0 < t.bge
  width_pos : 0 < t.w4
  next_initial_gap : gamma*(t.w4-t.bge) < delta
  next_other_gap : 0 < gamma*(t.w4-t.bge)
  complete_initial_gap : delta < gamma*(normalForecastBill t-(t.bge+tailBill t))
  complete_after9_gap : delta+bonusGap2 c < gamma*normalForecastBill t
  complete_after10_gap : delta+bonusGap3 c < gamma*normalForecastBill t
  next_after9_gap : good < gamma*(t.w4-t.bge)+bonusGap2 c

theorem ordered_legal_root_order : orderedLegalAvailable [] = rootOrder := by decide

theorem first_maximum_strict_unique (score : Act → ℝ) (choices : List Act) (chosen : Act)
    (hc : chosen ∈ choices) (hm : ∀ a ∈ choices, a ≠ chosen → score a < score chosen) :
    firstMaximum score choices = chosen := by
  have hn : choices ≠ [] := fun h => by simpa [h] using hc
  by_contra h
  have hsmall := hm _ (firstMaximum_member score choices hn) h
  have hmax := firstMaximum_max score choices hn chosen hc
  linarith

theorem root_choice_from_strict_indices (score : Act → ℝ) (before : List (TreeEvaluation Act))
    (chosen : Fin 8) (hv : ∀ q : Fin 8, 0 < rawVisits before [.query q])
    (hm : ∀ q : Fin 8,q ≠ chosen → score (.query q) < score (.query chosen)) :
    nativeFirstChoice score before [] = .query chosen := by
  have hpos : ∀ a ∈ orderedLegalAvailable [],0 < rawVisits before ([]++[a]) := by
    intro a ha
    rw [ordered_legal_root_order] at ha
    obtain ⟨q,hq,rfl⟩ := List.mem_map.mp ha
    exact hv q
  rw [native_first_choice_all_visited score before [] hpos,ordered_legal_root_order]
  apply first_maximum_strict_unique
  · simp [rootOrder]
  · intro a ha hne
    obtain ⟨q,hq,rfl⟩ := List.mem_map.mp ha
    exact hm q (fun he => hne (he ▸ rfl))

theorem initial_root_visits_positive (reward : List Act → ℝ) (q : Fin 8) :
    0 < rawVisits (initialization reward) [.query q] := by simp [rawVisits,initial_root_stat_exact]

theorem a9_root_visits_positive (reward : List Act → ℝ) (q : Fin 8) :
    0 < rawVisits (aNine reward) [.query q] := by
  simp only [rawVisits,a9_root_child_statistics]
  split_ifs <;> norm_num

theorem a10_root_visits_positive (reward : List Act → ℝ) (q : Fin 8) :
    0 < rawVisits (aTen reward) [.query q] := by
  simp only [rawVisits,a10_root_child_statistics]
  split_ifs <;> norm_num

theorem b9_root_visits_positive (reward : List Act → ℝ) (q : Fin 8) :
    0 < rawVisits (bNine reward) [.query q] := by
  simp only [rawVisits,b9_root_child_statistics]
  split_ifs <;> norm_num

theorem reference_complete_first_root (qids : Finset Qid) (t : TariffInput) (reward : List Act → ℝ)
    (delta good c beta Cref : ℝ) (hs : SeedTable reward delta)
    (hm : RootMargins t c (penaltyScale qids beta Cref) delta good) :
    nativeFirstChoice (indexScore c (referencePenalty qids .complete t beta Cref) (initialization reward) [])
      (initialization reward) [] = .query hyde := by
  apply root_choice_from_strict_indices _ _ hyde (initial_root_visits_positive reward)
  intro q hq
  rw [initial_complete_index qids t reward delta c beta Cref hs q,
    initial_complete_index qids t reward delta c beta Cref hs hyde]
  have hn : hyde ≠ branchB := by decide
  have hg := hm.complete_initial_gap
  by_cases hqb : q = branchB <;> simp only [hqb,if_neg hq,if_pos rfl,
    if_neg (show hyde ≠ branchB by decide),if_neg (show branchB ≠ hyde by decide),ite_true,ite_false] <;>
    nlinarith [hm.delta_pos]

theorem reference_next_first_root (qids : Finset Qid) (t : TariffInput) (reward : List Act → ℝ)
    (delta good c beta Cref : ℝ) (hs : SeedTable reward delta)
    (hm : RootMargins t c (penaltyScale qids beta Cref) delta good) :
    nativeFirstChoice (indexScore c (referencePenalty qids .next t beta Cref) (initialization reward) [])
      (initialization reward) [] = .query branchB := by
  apply root_choice_from_strict_indices _ _ branchB (initial_root_visits_positive reward)
  intro q hq
  rw [initial_next_index qids t reward delta c beta Cref hs hm.bge_pos hm.width_pos q,
    initial_next_index qids t reward delta c beta Cref hs hm.bge_pos hm.width_pos branchB]
  have hn : branchB ≠ hyde := by decide
  have hg := hm.next_initial_gap
  by_cases hqh : q = hyde <;> simp only [hqh,if_neg hq,if_pos rfl,
    if_neg (show hyde ≠ branchB by decide),if_neg (show branchB ≠ hyde by decide),ite_true,ite_false] <;>
    nlinarith [hm.delta_pos]

theorem reference_complete_second_root (qids : Finset Qid) (t : TariffInput) (reward : List Act → ℝ)
    (delta good c beta Cref : ℝ) (hs : SeedTable reward delta) (hr : 0 ≤ reward aCold)
    (hm : RootMargins t c (penaltyScale qids beta Cref) delta good) :
    nativeFirstChoice (indexScore c (referencePenalty qids .complete t beta Cref) (aNine reward) [])
      (aNine reward) [] = .query hyde := by
  apply root_choice_from_strict_indices _ _ hyde (a9_root_visits_positive reward)
  intro q hq
  rw [a9_complete_index qids t reward delta c beta Cref hs q,
    a9_complete_index qids t reward delta c beta Cref hs hyde]
  have hg := hm.complete_after9_gap
  unfold bonusGap2 at hg
  by_cases hqb : q = branchB <;> simp only [hqb,if_neg hq,if_pos rfl,
    if_neg (show hyde ≠ branchB by decide),if_neg (show branchB ≠ hyde by decide),ite_true,ite_false] <;>
    nlinarith [hm.delta_pos]

theorem reference_complete_third_root (qids : Finset Qid) (t : TariffInput) (reward : List Act → ℝ)
    (delta good c beta Cref : ℝ) (hs : SeedTable reward delta) (hr : 0 ≤ reward aCold)
    (hm : RootMargins t c (penaltyScale qids beta Cref) delta good) :
    nativeFirstChoice (indexScore c (referencePenalty qids .complete t beta Cref) (aTen reward) [])
      (aTen reward) [] = .query hyde := by
  apply root_choice_from_strict_indices _ _ hyde (a10_root_visits_positive reward)
  intro q hq
  rw [a10_complete_index qids t reward delta c beta Cref hs q,
    a10_complete_index qids t reward delta c beta Cref hs hyde]
  have hg := hm.complete_after10_gap
  unfold bonusGap3 at hg
  by_cases hqb : q = branchB <;> simp only [hqb,if_neg hq,if_pos rfl,
    if_neg (show hyde ≠ branchB by decide),if_neg (show branchB ≠ hyde by decide),ite_true,ite_false] <;>
    nlinarith [hm.delta_pos]

theorem reference_next_second_root (qids : Finset Qid) (t : TariffInput) (reward : List Act → ℝ)
    (delta good c beta Cref : ℝ) (hs : SeedTable reward delta) (hr : reward bCold ≤ good)
    (hm : RootMargins t c (penaltyScale qids beta Cref) delta good) :
    nativeFirstChoice (indexScore c (referencePenalty qids .next t beta Cref) (bNine reward) [])
      (bNine reward) [] = .query hyde := by
  apply root_choice_from_strict_indices _ _ hyde (b9_root_visits_positive reward)
  intro q hq
  rw [b9_next_index qids t reward delta c beta Cref hs hm.bge_pos hm.width_pos q,
    b9_next_index qids t reward delta c beta Cref hs hm.bge_pos hm.width_pos hyde]
  have hn : hyde ≠ branchB := by decide
  have hg := hm.next_after9_gap
  unfold bonusGap2 at hg
  by_cases hqb : q = branchB <;> simp only [hqb,if_neg hq,if_pos rfl,
    if_neg (show hyde ≠ branchB by decide),if_neg (show branchB ≠ hyde by decide),ite_true,ite_false] <;>
    nlinarith [hm.delta_le_good,hm.next_other_gap]

end AgentUCTNativeBudget
