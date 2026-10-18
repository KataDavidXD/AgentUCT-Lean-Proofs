import NativeRobustRoots





set_option autoImplicit false
set_option maxRecDepth 16384
set_option maxHeartbeats 4000000
set_option linter.constructorNameAsVariable false
noncomputable section
namespace AgentUCTNativeBudget
open AgentUCTPanelAllocation AgentUCTNativeRepair AgentUCTNativeRefinement AgentUCTPaper
variable {Qid : Type*} [DecidableEq Qid] [Encodable Qid]

def AdmissibleInitialPrices (t : TariffInput) (priors caps : Act → ℝ) (epsilon : ℝ) : Prop :=
  0 ≤ epsilon ∧ (∀ a,tariff t a ≤ caps a) ∧
  (∀ a,|min (caps a) (priors a)-tariff t a| ≤ epsilon) ∧
  (∀ a,tariff t a = 0 → min (caps a) (priors a) = 0) ∧
  (∀ a,tariff t a = 0 ∨ epsilon < tariff t a)

omit [Encodable Qid] in
theorem event_equality_from_same_derived_root (before : List (TreeEvaluation Act)) (reward : List Act → ℝ)
    (c : ℝ) (live reference : List (TreeEvaluation Act) → List Act → Act → ℝ) (q : Fin 8)
    (hp : ∀ r : Fin 8,[.query r] ∈ expandedNodes before)
    (hl : nativeFirstChoice (indexScore c live before []) before [] = .query q)
    (hr : nativeFirstChoice (indexScore c reference before []) before [] = .query q)
    (hu : unexpandedAt (expandedNodes before) [.query q] ≠ []) :
    nativeEvent budgetTape c live reward before = nativeEvent budgetTape c reference reward before := by
  have hls := root_then_expand before c live q hp hl hu
  have hrs := root_then_expand before c reference q hp hr hu
  simp only [nativeEvent,hls,hrs]

theorem causal_five_event_outputs (qids : Finset Qid) (t : TariffInput) (priors caps : Act → ℝ) (qid : Qid)
    (reward : List Act → ℝ) (delta good c beta Cref epsilon : ℝ)
    (hscale : 0 ≤ beta/Cref) (hp : AdmissibleInitialPrices t priors caps epsilon)
    (hs : SeedTable reward delta) (hra : 0 ≤ reward aCold) (hrb : reward bCold ≤ good)
    (hm : RootMargins t c (penaltyScale qids beta Cref) delta good)
    (he : ErrorMargins t c (penaltyScale qids beta Cref) delta good (10*(penaltyScale qids beta Cref)*epsilon)) :
    nativeEvent budgetTape c (causalPenalty qids .complete t priors caps qid beta Cref) reward (initialization reward) = aColdEvent reward ∧
    nativeEvent budgetTape c (causalPenalty qids .next t priors caps qid beta Cref) reward (initialization reward) = bColdEvent reward ∧
    nativeEvent budgetTape c (causalPenalty qids .complete t priors caps qid beta Cref) reward (aNine reward) = aWarmEvent reward ∧
    nativeEvent budgetTape c (causalPenalty qids .complete t priors caps qid beta Cref) reward (aTen reward) = aCrossEvent reward ∧
    nativeEvent budgetTape c (causalPenalty qids .next t priors caps qid beta Cref) reward (bNine reward) = aColdEvent reward := by
  obtain ⟨h1,h2,h3,h4,h5⟩ := causal_five_root_choices qids t priors caps qid reward delta good c beta Cref epsilon
    hp.1 hscale hp.2.1 hp.2.2.1 hp.2.2.2.1 hp.2.2.2.2 hs hra hrb hm he
  have hi : ∀ q : Fin 8,[.query q] ∈ expandedNodes (initialization reward) := by
    intro q; rw [initialization_nodes_exact]; exact roots_in_initial_nodes q
  have ha9 : ∀ q : Fin 8,[.query q] ∈ expandedNodes (aNine reward) := by
    intro q; rw [a9_nodes_exact]; exact Finset.mem_insert_of_mem (roots_in_initial_nodes q)
  have ha10 : ∀ q : Fin 8,[.query q] ∈ expandedNodes (aTen reward) := by
    intro q; rw [a10_nodes_exact]
    exact Finset.mem_insert_of_mem (Finset.mem_insert_of_mem (roots_in_initial_nodes q))
  have hb9 : ∀ q : Fin 8,[.query q] ∈ expandedNodes (bNine reward) := by
    intro q; rw [b9_nodes_exact]; exact Finset.mem_insert_of_mem (roots_in_initial_nodes q)
  refine ⟨?_,?_,?_,?_,?_⟩
  · rw [event_equality_from_same_derived_root _ reward c _ (referencePenalty qids .complete t beta Cref) hyde hi h1
      (reference_complete_first_root qids t reward delta good c beta Cref hs hm)
      (by rw [initialization_nodes_exact]; exact (by rw [initial_A_unexpanded]; decide))]
    exact reference_complete_initial_event qids t reward delta good c beta Cref hs hm
  · rw [event_equality_from_same_derived_root _ reward c _ (referencePenalty qids .next t beta Cref) branchB hi h2
      (reference_next_first_root qids t reward delta good c beta Cref hs hm)
      (by rw [initialization_nodes_exact]; exact (by rw [initial_B_unexpanded]; decide))]
    exact reference_next_initial_event qids t reward delta good c beta Cref hs hm
  · rw [event_equality_from_same_derived_root _ reward c _ (referencePenalty qids .complete t beta Cref) hyde ha9 h3
      (reference_complete_second_root qids t reward delta good c beta Cref hs hra hm)
      (by rw [a9_nodes_exact]; exact (by rw [after_a9_A_unexpanded]; decide))]
    exact reference_complete_a9_event qids t reward delta good c beta Cref hs hra hm
  · rw [event_equality_from_same_derived_root _ reward c _ (referencePenalty qids .complete t beta Cref) hyde ha10 h4
      (reference_complete_third_root qids t reward delta good c beta Cref hs hra hm)
      (by rw [a10_nodes_exact]; exact (by rw [after_a10_A_unexpanded]; decide))]
    exact reference_complete_a10_event qids t reward delta good c beta Cref hs hra hm
  · rw [event_equality_from_same_derived_root _ reward c _ (referencePenalty qids .next t beta Cref) hyde hb9 h5
      (reference_next_second_root qids t reward delta good c beta Cref hs hrb hm)
      (by rw [b9_nodes_exact]; exact (by rw [after_b9_A_unexpanded]; decide))]
    exact reference_next_b9_event qids t reward delta good c beta Cref hs hrb hm

def causalTaskRun (qids : Finset Qid) (mode : ForecastMode) (t : TariffInput)
    (priors caps : Act → ℝ) (qid : Qid) (adverse : Bool) (delta good c beta Cref : ℝ) (cap : ℕ) :=
  nativeGenerate budgetTape c (causalPenalty qids mode t priors caps qid beta Cref)
    (physicalBill qids t) (taskBudget qids t) (taskReward adverse delta good) cap

theorem causal_both_task_histories_generated (qids : Finset Qid) (t : TariffInput) (priors caps : Act → ℝ) (qid : Qid)
    (adverse : Bool) (delta good c beta Cref epsilon tolerance : ℝ) (cap : ℕ) (hcap : 11 ≤ cap)
    (hscale : 0 ≤ beta/Cref) (hp : AdmissibleInitialPrices t priors caps epsilon)
    (hm : RootMargins t c (penaltyScale qids beta Cref) delta good)
    (he : ErrorMargins t c (penaltyScale qids beta Cref) delta good (10*(penaltyScale qids beta Cref)*epsilon))
    (hw : StrictResourceWindow (qids.card : ℝ) t tolerance) (htariff : ∀ a,0 ≤ tariff t a) :
    causalTaskRun qids .complete t priors caps qid adverse delta good c beta Cref cap = aEleven (taskReward adverse delta good) ∧
    causalTaskRun qids .next t priors caps qid adverse delta good c beta Cref cap = bTen (taskReward adverse delta good) := by
  let reward := taskReward adverse delta good
  have hg : 0 ≤ good := hm.delta_pos.le.trans hm.delta_le_good
  have hra : 0 ≤ reward aCold := by
    dsimp only [reward]
    rw [(task_cold_rewards adverse delta good).1]; cases adverse <;> simp [hg]
  have hrb : reward bCold ≤ good := by
    dsimp only [reward]
    rw [(task_cold_rewards adverse delta good).2.1]; cases adverse <;> simp [hm.delta_le_good]
  obtain ⟨h1,h2,h3,h4,h5⟩ := causal_five_event_outputs qids t priors caps qid reward delta good c beta Cref epsilon
    hscale hp (task_seed_table adverse delta good) hra hrb hm he
  have hi := initial_bill_below_task_budget qids t reward tolerance hw htariff
  obtain ⟨ha,hb,hac,hbc⟩ := strict_window_endpoints qids t reward tolerance hw
  have ha9 : physicalBill qids t (aNine reward) < taskBudget qids t := by
    rw [physical_a9_bill]; rwa [physical_a10_bill] at ha
  have hxa : taskBudget qids t ≤ physicalBill qids t (aEleven reward) :=
    (le_add_of_nonneg_right hw.2.2.2.2.1).trans hac.le
  have hxb : taskBudget qids t ≤ physicalBill qids t (bTen reward) :=
    (le_add_of_nonneg_right hw.2.2.2.2.1).trans hbc.le
  constructor
  · unfold causalTaskRun nativeGenerate
    rw [budget_common_eight_initialization,show cap-8 = (cap-11)+3 by omega,
      show (cap-11)+3 = ((cap-11)+2)+1 by omega,nativeAfter]
    simp only [targetReached]
    rw [if_neg (not_le.mpr hi),h1]
    change nativeAfter budgetTape c (causalPenalty qids .complete t priors caps qid beta Cref)
      (physicalBill qids t) (taskBudget qids t) reward ((cap-11)+2) (aNine reward) = _
    rw [show (cap-11)+2 = ((cap-11)+1)+1 by omega,nativeAfter]
    simp only [targetReached]
    rw [if_neg (not_le.mpr ha9),h3]
    change nativeAfter budgetTape c (causalPenalty qids .complete t priors caps qid beta Cref)
      (physicalBill qids t) (taskBudget qids t) reward ((cap-11)+1) (aTen reward) = _
    rw [nativeAfter]
    simp only [targetReached]
    rw [if_neg (not_le.mpr ha),h4]
    exact native_after_crossing_stops budgetTape c _ _ _ reward (aEleven reward) hxa (cap-11)
  · unfold causalTaskRun nativeGenerate
    rw [budget_common_eight_initialization,show cap-8 = (cap-10)+2 by omega,
      show (cap-10)+2 = ((cap-10)+1)+1 by omega,nativeAfter]
    simp only [targetReached]
    rw [if_neg (not_le.mpr hi),h2]
    change nativeAfter budgetTape c (causalPenalty qids .next t priors caps qid beta Cref)
      (physicalBill qids t) (taskBudget qids t) reward ((cap-10)+1) (bNine reward) = _
    rw [nativeAfter]
    simp only [targetReached]
    rw [if_neg (not_le.mpr hb),h5]
    exact native_after_crossing_stops budgetTape c _ _ _ reward (bTen reward) hxb (cap-10)

theorem causal_full_history_equal_reference (qids : Finset Qid) (t : TariffInput) (priors caps : Act → ℝ) (qid : Qid)
    (adverse : Bool) (delta good c beta Cref epsilon tolerance : ℝ) (cap : ℕ) (hcap : 11 ≤ cap)
    (hscale : 0 ≤ beta/Cref) (hp : AdmissibleInitialPrices t priors caps epsilon)
    (hm : RootMargins t c (penaltyScale qids beta Cref) delta good)
    (he : ErrorMargins t c (penaltyScale qids beta Cref) delta good (10*(penaltyScale qids beta Cref)*epsilon))
    (hw : StrictResourceWindow (qids.card : ℝ) t tolerance) (htariff : ∀ a,0 ≤ tariff t a) :
    causalTaskRun qids .complete t priors caps qid adverse delta good c beta Cref cap = referenceRun qids .complete t adverse delta good c beta Cref cap ∧
    causalTaskRun qids .next t priors caps qid adverse delta good c beta Cref cap = referenceRun qids .next t adverse delta good c beta Cref cap := by
  obtain ⟨ha,hb⟩ := causal_both_task_histories_generated qids t priors caps qid adverse delta good c beta Cref epsilon tolerance cap hcap hscale hp hm he hw htariff
  obtain ⟨hra,hrb⟩ := both_task_tables_generated qids t adverse delta good c beta Cref tolerance cap hcap hm hw htariff
  exact ⟨ha.trans hra.symm,hb.trans hrb.symm⟩

end AgentUCTNativeBudget
