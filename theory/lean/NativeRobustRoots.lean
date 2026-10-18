import NativeCausalQuoteError



set_option autoImplicit false
set_option maxRecDepth 16384
set_option maxHeartbeats 4000000
set_option linter.constructorNameAsVariable false
noncomputable section
namespace AgentUCTNativeBudget
open AgentUCTPanelAllocation AgentUCTNativeRepair AgentUCTNativeRefinement AgentUCTPaper
variable {Qid : Type*} [DecidableEq Qid]

structure ErrorMargins (t : TariffInput) (c gamma delta good E : ℝ) : Prop where
  delta_gap : 2*E < delta
  next_initial : 2*E < delta-gamma*(t.w4-t.bge)
  next_other : 2*E < gamma*(t.w4-t.bge)
  complete_initial : 2*E < gamma*(normalForecastBill t-(t.bge+tailBill t))-delta
  complete_after9 : 2*E < gamma*normalForecastBill t-delta-bonusGap2 c
  complete_after10 : 2*E < gamma*normalForecastBill t-delta-bonusGap3 c
  next_after9 : 2*E < gamma*(t.w4-t.bge)+bonusGap2 c-good

theorem root_choice_stable_under_derived_error (before : List (TreeEvaluation Act)) (c E : ℝ)
    (live reference : List (TreeEvaluation Act) → List Act → Act → ℝ) (chosen : Fin 8)
    (hv : ∀ q,0 < rawVisits before [.query q])
    (herr : ∀ q,|indexScore c live before [] (.query q)-indexScore c reference before [] (.query q)| ≤ E)
    (hgap : ∀ q,q ≠ chosen → indexScore c reference before [] (.query q)+2*E <
      indexScore c reference before [] (.query chosen)) :
    nativeFirstChoice (indexScore c live before []) before [] = .query chosen := by
  apply root_choice_from_strict_indices _ _ chosen hv
  intro q hq
  obtain ⟨hqlo,hqhi⟩ := abs_le.mp (herr q)
  obtain ⟨hclo,hchi⟩ := abs_le.mp (herr chosen)
  have hg := hgap q hq
  linarith

theorem reference_complete_initial_gap (qids : Finset Qid) (t : TariffInput) (reward : List Act → ℝ)
    (delta good c beta Cref E : ℝ) (hs : SeedTable reward delta)
    (hm : RootMargins t c (penaltyScale qids beta Cref) delta good)
    (he : ErrorMargins t c (penaltyScale qids beta Cref) delta good E) (q : Fin 8) (hq : q ≠ hyde) :
    indexScore c (referencePenalty qids .complete t beta Cref) (initialization reward) [] (.query q)+2*E <
      indexScore c (referencePenalty qids .complete t beta Cref) (initialization reward) [] (.query hyde) := by
  rw [initial_complete_index qids t reward delta c beta Cref hs q,
    initial_complete_index qids t reward delta c beta Cref hs hyde]
  have hg := he.complete_initial
  by_cases hqb : q = branchB <;> simp only [hqb,if_neg hq,
    if_neg (show hyde ≠ branchB by decide),if_neg (show branchB ≠ hyde by decide),ite_true,ite_false] <;>
    nlinarith [hm.delta_pos]

theorem reference_next_initial_gap (qids : Finset Qid) (t : TariffInput) (reward : List Act → ℝ)
    (delta good c beta Cref E : ℝ) (hs : SeedTable reward delta)
    (hm : RootMargins t c (penaltyScale qids beta Cref) delta good)
    (he : ErrorMargins t c (penaltyScale qids beta Cref) delta good E) (q : Fin 8) (hq : q ≠ branchB) :
    indexScore c (referencePenalty qids .next t beta Cref) (initialization reward) [] (.query q)+2*E <
      indexScore c (referencePenalty qids .next t beta Cref) (initialization reward) [] (.query branchB) := by
  rw [initial_next_index qids t reward delta c beta Cref hs hm.bge_pos hm.width_pos q,
    initial_next_index qids t reward delta c beta Cref hs hm.bge_pos hm.width_pos branchB]
  have hg := he.next_initial
  by_cases hqh : q = hyde <;> simp only [hqh,if_neg hq,
    if_neg (show hyde ≠ branchB by decide),if_neg (show branchB ≠ hyde by decide),ite_true,ite_false] <;>
    nlinarith [he.delta_gap]

theorem reference_complete_a9_gap (qids : Finset Qid) (t : TariffInput) (reward : List Act → ℝ)
    (delta good c beta Cref E : ℝ) (hs : SeedTable reward delta) (hr : 0 ≤ reward aCold)
    (hm : RootMargins t c (penaltyScale qids beta Cref) delta good)
    (he : ErrorMargins t c (penaltyScale qids beta Cref) delta good E) (q : Fin 8) (hq : q ≠ hyde) :
    indexScore c (referencePenalty qids .complete t beta Cref) (aNine reward) [] (.query q)+2*E <
      indexScore c (referencePenalty qids .complete t beta Cref) (aNine reward) [] (.query hyde) := by
  rw [a9_complete_index qids t reward delta c beta Cref hs q,
    a9_complete_index qids t reward delta c beta Cref hs hyde]
  have hg := he.complete_after9
  unfold bonusGap2 at hg
  by_cases hqb : q = branchB <;> simp only [hqb,if_neg hq,
    if_neg (show hyde ≠ branchB by decide),if_neg (show branchB ≠ hyde by decide),ite_true,ite_false] <;>
    nlinarith [hm.delta_pos]

theorem reference_complete_a10_gap (qids : Finset Qid) (t : TariffInput) (reward : List Act → ℝ)
    (delta good c beta Cref E : ℝ) (hs : SeedTable reward delta) (hr : 0 ≤ reward aCold)
    (hm : RootMargins t c (penaltyScale qids beta Cref) delta good)
    (he : ErrorMargins t c (penaltyScale qids beta Cref) delta good E) (q : Fin 8) (hq : q ≠ hyde) :
    indexScore c (referencePenalty qids .complete t beta Cref) (aTen reward) [] (.query q)+2*E <
      indexScore c (referencePenalty qids .complete t beta Cref) (aTen reward) [] (.query hyde) := by
  rw [a10_complete_index qids t reward delta c beta Cref hs q,
    a10_complete_index qids t reward delta c beta Cref hs hyde]
  have hg := he.complete_after10
  unfold bonusGap3 at hg
  by_cases hqb : q = branchB <;> simp only [hqb,if_neg hq,
    if_neg (show hyde ≠ branchB by decide),if_neg (show branchB ≠ hyde by decide),ite_true,ite_false] <;>
    nlinarith [hm.delta_pos]

theorem reference_next_b9_gap (qids : Finset Qid) (t : TariffInput) (reward : List Act → ℝ)
    (delta good c beta Cref E : ℝ) (hs : SeedTable reward delta) (hr : reward bCold ≤ good)
    (hm : RootMargins t c (penaltyScale qids beta Cref) delta good)
    (he : ErrorMargins t c (penaltyScale qids beta Cref) delta good E) (q : Fin 8) (hq : q ≠ hyde) :
    indexScore c (referencePenalty qids .next t beta Cref) (bNine reward) [] (.query q)+2*E <
      indexScore c (referencePenalty qids .next t beta Cref) (bNine reward) [] (.query hyde) := by
  rw [b9_next_index qids t reward delta c beta Cref hs hm.bge_pos hm.width_pos q,
    b9_next_index qids t reward delta c beta Cref hs hm.bge_pos hm.width_pos hyde]
  have hg := he.next_after9
  unfold bonusGap2 at hg
  by_cases hqb : q = branchB <;> simp only [hqb,if_neg hq,
    if_neg (show hyde ≠ branchB by decide),if_neg (show branchB ≠ hyde by decide),ite_true,ite_false] <;>
    nlinarith [hm.delta_le_good,he.next_other]

variable [Encodable Qid]
theorem causal_five_root_choices (qids : Finset Qid) (t : TariffInput) (priors caps : Act → ℝ) (qid : Qid)
    (reward : List Act → ℝ) (delta good c beta Cref epsilon : ℝ) (hE : 0 ≤ epsilon)
    (hscale : 0 ≤ beta/Cref) (hcap : ∀ a,tariff t a ≤ caps a)
    (hprior : ∀ a,|min (caps a) (priors a)-tariff t a| ≤ epsilon)
    (hz : ∀ a,tariff t a = 0 → min (caps a) (priors a) = 0)
    (hf : ∀ a,tariff t a = 0 ∨ epsilon < tariff t a)
    (hs : SeedTable reward delta) (hra : 0 ≤ reward aCold) (hrb : reward bCold ≤ good)
    (hm : RootMargins t c (penaltyScale qids beta Cref) delta good)
    (he : ErrorMargins t c (penaltyScale qids beta Cref) delta good (10*(penaltyScale qids beta Cref)*epsilon)) :
    nativeFirstChoice (indexScore c (causalPenalty qids .complete t priors caps qid beta Cref) (initialization reward) []) (initialization reward) [] = .query hyde ∧
    nativeFirstChoice (indexScore c (causalPenalty qids .next t priors caps qid beta Cref) (initialization reward) []) (initialization reward) [] = .query branchB ∧
    nativeFirstChoice (indexScore c (causalPenalty qids .complete t priors caps qid beta Cref) (aNine reward) []) (aNine reward) [] = .query hyde ∧
    nativeFirstChoice (indexScore c (causalPenalty qids .complete t priors caps qid beta Cref) (aTen reward) []) (aTen reward) [] = .query hyde ∧
    nativeFirstChoice (indexScore c (causalPenalty qids .next t priors caps qid beta Cref) (bNine reward) []) (bNine reward) [] = .query hyde := by
  refine ⟨?_,?_,?_,?_,?_⟩
  all_goals apply root_choice_stable_under_derived_error
  · exact initial_root_visits_positive reward
  · exact causal_root_index_error qids .complete t priors caps qid epsilon c beta Cref hE hscale hcap hprior hz hf _
  · exact reference_complete_initial_gap qids t reward delta good c beta Cref _ hs hm he
  · exact initial_root_visits_positive reward
  · exact causal_root_index_error qids .next t priors caps qid epsilon c beta Cref hE hscale hcap hprior hz hf _
  · exact reference_next_initial_gap qids t reward delta good c beta Cref _ hs hm he
  · exact a9_root_visits_positive reward
  · exact causal_root_index_error qids .complete t priors caps qid epsilon c beta Cref hE hscale hcap hprior hz hf _
  · exact reference_complete_a9_gap qids t reward delta good c beta Cref _ hs hra hm he
  · exact a10_root_visits_positive reward
  · exact causal_root_index_error qids .complete t priors caps qid epsilon c beta Cref hE hscale hcap hprior hz hf _
  · exact reference_complete_a10_gap qids t reward delta good c beta Cref _ hs hra hm he
  · exact b9_root_visits_positive reward
  · exact causal_root_index_error qids .next t priors caps qid epsilon c beta Cref hE hscale hcap hprior hz hf _
  · exact reference_next_b9_gap qids t reward delta good c beta Cref _ hs hrb hm he

end AgentUCTNativeBudget
