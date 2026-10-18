import NativeReferenceCalibration





set_option autoImplicit false
set_option maxRecDepth 16384
set_option maxHeartbeats 4000000
set_option linter.constructorNameAsVariable false
noncomputable section
namespace AgentUCTNativeBudget
open AgentUCTPanelAllocation AgentUCTNativeRepair AgentUCTNativeRefinement AgentUCTPaper
variable {Qid : Type*} [DecidableEq Qid] [Encodable Qid]

def causalRetained (qids : Finset Qid) (mode : ForecastMode) (t : TariffInput)
    (priors caps : Act → ℝ) (qid : Qid) (adverse : Bool) (delta good c beta Cref tolerance : ℝ) (cap : ℕ) :=
  panelReported qids (fun r => tariff t (resourceAction r))
    (causalTaskRun qids mode t priors caps qid adverse delta good c beta Cref cap) (taskBudget qids t) tolerance

def causalRetainedNet (qids : Finset Qid) (mode : ForecastMode) (t : TariffInput)
    (priors caps : Act → ℝ) (qid : Qid) (adverse : Bool) (delta good c beta Cref tolerance lambda : ℝ) (cap : ℕ) : ℝ :=
  let retained := causalRetained qids mode t priors caps qid adverse delta good c beta Cref tolerance cap
  completedValue retained-lambda*(physicalBill qids t retained)/Cref

theorem causal_task_run_is_source_panel_allocator (qids : Finset Qid) (hn : qids.Nonempty)
    (mode : ForecastMode) (t : TariffInput) (priors caps : Act → ℝ) (qid : Qid)
    (adverse : Bool) (delta good c beta Cref : ℝ) (cap : ℕ) :
    causalTaskRun qids mode t priors caps qid adverse delta good c beta Cref cap =
      causalPanelGenerate qids mode budgetTape (fun _ _ => false) priors caps
        (completeRows qids (fun r => tariff t (resourceAction r))) (emptyReceiptMeans qid)
        (fun _ _ => 0) (fun r => tariff t (resourceAction r)) c beta Cref (taskBudget qids t)
        (fun _ path => taskReward adverse delta good path) cap := by
  have hr : (fun path => panelReward qids (fun _ => taskReward adverse delta good path)) = taskReward adverse delta good := by
    funext path
    exact fixed_panel_reward_is_not_sum qids _ hn
  unfold causalTaskRun causalPanelGenerate panelGenerate
  rw [hr]
  rfl

theorem causal_task_run_tree_allocation (qids : Finset Qid) (mode : ForecastMode) (t : TariffInput)
    (priors caps : Act → ℝ) (qid : Qid) (adverse : Bool) (delta good c beta Cref : ℝ) (cap : ℕ) :
    LegalTreeRun Terminal {[]} (causalTaskRun qids mode t priors caps qid adverse delta good c beta Cref cap) ∧
    TreeAllocationRule nativeTerminals c (causalPenalty qids mode t priors caps qid beta Cref)
      (causalTaskRun qids mode t priors caps qid adverse delta good c beta Cref cap) :=
  ⟨native_generated_legal_tree budgetTape budget_tape_supported c _ _ _ _ cap,
   native_generated_tree_allocation_rule budgetTape budget_tape_supported c _ _ _ _ cap⟩

theorem causal_retained_histories (qids : Finset Qid) (t : TariffInput) (priors caps : Act → ℝ) (qid : Qid)
    (adverse : Bool) (delta good c beta Cref epsilon tolerance : ℝ) (cap : ℕ) (hcap : 11 ≤ cap)
    (hscale : 0 ≤ beta/Cref) (hp : AdmissibleInitialPrices t priors caps epsilon)
    (hm : RootMargins t c (penaltyScale qids beta Cref) delta good)
    (he : ErrorMargins t c (penaltyScale qids beta Cref) delta good (10*(penaltyScale qids beta Cref)*epsilon))
    (hw : StrictResourceWindow (qids.card : ℝ) t tolerance) (htariff : ∀ a,0 ≤ tariff t a) :
    causalRetained qids .complete t priors caps qid adverse delta good c beta Cref tolerance cap = aTen (taskReward adverse delta good) ∧
    causalRetained qids .next t priors caps qid adverse delta good c beta Cref tolerance cap = bNine (taskReward adverse delta good) := by
  obtain ⟨ha,hb⟩ := causal_both_task_histories_generated qids t priors caps qid adverse delta good c beta Cref epsilon tolerance cap hcap hscale hp hm he hw htariff
  unfold causalRetained panelReported
  rw [ha,hb,resource_a_TB10 qids t _ tolerance hw,resource_b_TB9 qids t _ tolerance hw,a11_take10,b10_take9]
  exact ⟨rfl,rfl⟩

theorem causal_actual_TB_and_complete_receipt_bills (qids : Finset Qid) (t : TariffInput)
    (priors caps : Act → ℝ) (qid : Qid) (adverse : Bool) (delta good c beta Cref epsilon tolerance : ℝ)
    (cap : ℕ) (hcap : 11 ≤ cap) (hscale : 0 ≤ beta/Cref) (hp : AdmissibleInitialPrices t priors caps epsilon)
    (hm : RootMargins t c (penaltyScale qids beta Cref) delta good)
    (he : ErrorMargins t c (penaltyScale qids beta Cref) delta good (10*(penaltyScale qids beta Cref)*epsilon))
    (hw : StrictResourceWindow (qids.card : ℝ) t tolerance) (htariff : ∀ a,0 ≤ tariff t a) :
    panelReportingIndex qids (fun r => tariff t (resourceAction r))
      (causalTaskRun qids .complete t priors caps qid adverse delta good c beta Cref cap) (taskBudget qids t) tolerance = 10 ∧
    panelReportingIndex qids (fun r => tariff t (resourceAction r))
      (causalTaskRun qids .next t priors caps qid adverse delta good c beta Cref cap) (taskBudget qids t) tolerance = 9 ∧
    (taskMeans qids t caps qid (causalRetained qids .complete t priors caps qid adverse delta good c beta Cref tolerance cap)).actualPaid =
      (qids.card : ℝ)*(baseBill t+t.bge+tailBill t) ∧
    (taskMeans qids t caps qid (causalRetained qids .next t priors caps qid adverse delta good c beta Cref tolerance cap)).actualPaid =
      (qids.card : ℝ)*(baseBill t+t.normalE5+tailBill t) ∧
    (taskMeans qids t caps qid (causalTaskRun qids .complete t priors caps qid adverse delta good c beta Cref cap)).actualPaid =
      (qids.card : ℝ)*(baseBill t+t.bge+tailBill t+crossBill t) ∧
    (taskMeans qids t caps qid (causalTaskRun qids .next t priors caps qid adverse delta good c beta Cref cap)).actualPaid =
      (qids.card : ℝ)*(baseBill t+t.normalE5+2*tailBill t+t.bge) := by
  obtain ⟨ha,hb⟩ := causal_both_task_histories_generated qids t priors caps qid adverse delta good c beta Cref epsilon tolerance cap hcap hscale hp hm he hw htariff
  obtain ⟨hra,hrb⟩ := causal_retained_histories qids t priors caps qid adverse delta good c beta Cref epsilon tolerance cap hcap hscale hp hm he hw htariff
  rw [ha,hb,hra,hrb]
  refine ⟨resource_a_TB10 qids t _ tolerance hw,resource_b_TB9 qids t _ tolerance hw,?_,?_,?_,?_⟩
  all_goals rw [(task_means_full_cache_metadata_and_bill qids t caps qid _).2.1]
  · exact physical_a10_bill qids t _
  · exact physical_b9_bill qids t _
  · exact physical_a11_bill qids t _
  · exact physical_b10_bill qids t _

theorem causal_retained_net_difference (qids : Finset Qid) (t : TariffInput) (priors caps : Act → ℝ) (qid : Qid)
    (adverse : Bool) (delta good c beta Cref epsilon tolerance lambda : ℝ) (cap : ℕ) (hcap : 11 ≤ cap)
    (hscale : 0 ≤ beta/Cref) (hp : AdmissibleInitialPrices t priors caps epsilon)
    (hm : RootMargins t c (penaltyScale qids beta Cref) delta good)
    (he : ErrorMargins t c (penaltyScale qids beta Cref) delta good (10*(penaltyScale qids beta Cref)*epsilon))
    (hw : StrictResourceWindow (qids.card : ℝ) t tolerance) (htariff : ∀ a,0 ≤ tariff t a) :
    causalRetainedNet qids .complete t priors caps qid adverse delta good c beta Cref tolerance lambda cap-
      causalRetainedNet qids .next t priors caps qid adverse delta good c beta Cref tolerance lambda cap =
    (if adverse then delta-good else good-delta)-lambda*(qids.card : ℝ)*(t.bge-t.normalE5)/Cref := by
  obtain ⟨ha,hb⟩ := causal_retained_histories qids t priors caps qid adverse delta good c beta Cref epsilon tolerance cap hcap hscale hp hm he hw htariff
  dsimp only [causalRetainedNet]
  rw [ha,hb,(retained_task_best adverse delta good hm.delta_pos.le hm.delta_le_good).1,
    (retained_task_best adverse delta good hm.delta_pos.le hm.delta_le_good).2,physical_a10_bill,physical_b9_bill]
  cases adverse <;> simp only [Bool.false_eq_true,if_false,if_true] <;> ring

theorem causal_positive_and_adverse_separation_same_controls (qids : Finset Qid) (t : TariffInput)
    (priors caps : Act → ℝ) (qid : Qid) (delta good c beta Cref epsilon tolerance lambda : ℝ)
    (cap : ℕ) (hcap : 11 ≤ cap) (hscale : 0 ≤ beta/Cref) (hp : AdmissibleInitialPrices t priors caps epsilon)
    (hm : RootMargins t c (penaltyScale qids beta Cref) delta good)
    (he : ErrorMargins t c (penaltyScale qids beta Cref) delta good (10*(penaltyScale qids beta Cref)*epsilon))
    (hw : StrictResourceWindow (qids.card : ℝ) t tolerance) (htariff : ∀ a,0 ≤ tariff t a)
    (hgap : delta-good < lambda*(qids.card : ℝ)*(t.bge-t.normalE5)/Cref ∧
      lambda*(qids.card : ℝ)*(t.bge-t.normalE5)/Cref < good-delta) :
    causalRetainedNet qids .next t priors caps qid false delta good c beta Cref tolerance lambda cap <
      causalRetainedNet qids .complete t priors caps qid false delta good c beta Cref tolerance lambda cap ∧
    causalRetainedNet qids .complete t priors caps qid true delta good c beta Cref tolerance lambda cap <
      causalRetainedNet qids .next t priors caps qid true delta good c beta Cref tolerance lambda cap := by
  have hp1 := causal_retained_net_difference qids t priors caps qid false delta good c beta Cref epsilon tolerance lambda cap hcap hscale hp hm he hw htariff
  have hp2 := causal_retained_net_difference qids t priors caps qid true delta good c beta Cref epsilon tolerance lambda cap hcap hscale hp hm he hw htariff
  simp only [Bool.false_eq_true,if_false] at hp1
  simp only [if_true] at hp2
  constructor <;> linarith [hgap.1,hgap.2]

end AgentUCTNativeBudget
