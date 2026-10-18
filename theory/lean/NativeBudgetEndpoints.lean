import NativeBudgetRewards




set_option autoImplicit false
set_option maxRecDepth 16384
set_option maxHeartbeats 4000000
set_option linter.constructorNameAsVariable false
noncomputable section
namespace AgentUCTNativeBudget
open AgentUCTPanelAllocation AgentUCTNativeRepair AgentUCTNativeRefinement AgentUCTPaper
variable {Qid : Type*} [DecidableEq Qid]

def referenceRun (qids : Finset Qid) (mode : ForecastMode) (t : TariffInput)
    (adverse : Bool) (delta good c beta Cref : ℝ) (cap : ℕ) :=
  nativeGenerate budgetTape c (referencePenalty qids mode t beta Cref)
    (physicalBill qids t) (taskBudget qids t) (taskReward adverse delta good) cap

def retainedRun (qids : Finset Qid) (mode : ForecastMode) (t : TariffInput)
    (adverse : Bool) (delta good c beta Cref tolerance : ℝ) (cap : ℕ) :=
  panelReported qids (fun r => tariff t (resourceAction r))
    (referenceRun qids mode t adverse delta good c beta Cref cap) (taskBudget qids t) tolerance

def retainedNet (qids : Finset Qid) (mode : ForecastMode) (t : TariffInput)
    (adverse : Bool) (delta good c beta Cref tolerance lambda : ℝ) (cap : ℕ) : ℝ :=
  let retained := retainedRun qids mode t adverse delta good c beta Cref tolerance cap
  completedValue retained-lambda*(physicalBill qids t retained)/Cref

def wholeSpendingRetainedNet (qids : Finset Qid) (mode : ForecastMode) (t : TariffInput)
    (adverse : Bool) (delta good c beta Cref tolerance lambda : ℝ) (cap : ℕ) : ℝ :=
  completedValue (retainedRun qids mode t adverse delta good c beta Cref tolerance cap)-
    lambda*(physicalBill qids t (referenceRun qids mode t adverse delta good c beta Cref cap))/Cref

theorem retained_generated_histories (qids : Finset Qid) (t : TariffInput)
    (adverse : Bool) (delta good c beta Cref tolerance : ℝ) (cap : ℕ) (hc : 11 ≤ cap)
    (hm : RootMargins t c (penaltyScale qids beta Cref) delta good)
    (hw : StrictResourceWindow (qids.card : ℝ) t tolerance) (hp : ∀ a,0 ≤ tariff t a) :
    retainedRun qids .complete t adverse delta good c beta Cref tolerance cap = aTen (taskReward adverse delta good) ∧
    retainedRun qids .next t adverse delta good c beta Cref tolerance cap = bNine (taskReward adverse delta good) := by
  obtain ⟨ha,hb⟩ := both_task_tables_generated qids t adverse delta good c beta Cref tolerance cap hc hm hw hp
  unfold retainedRun referenceRun panelReported
  rw [ha,hb,resource_a_TB10 qids t _ tolerance hw,resource_b_TB9 qids t _ tolerance hw,a11_take10,b10_take9]
  exact ⟨rfl,rfl⟩

theorem retained_generated_best_and_bills (qids : Finset Qid) (t : TariffInput)
    (adverse : Bool) (delta good c beta Cref tolerance : ℝ) (cap : ℕ) (hc : 11 ≤ cap)
    (hm : RootMargins t c (penaltyScale qids beta Cref) delta good)
    (hw : StrictResourceWindow (qids.card : ℝ) t tolerance) (hp : ∀ a,0 ≤ tariff t a) :
    completedValue (retainedRun qids .complete t adverse delta good c beta Cref tolerance cap) =
      (if adverse then delta else good) ∧
    completedValue (retainedRun qids .next t adverse delta good c beta Cref tolerance cap) =
      (if adverse then good else delta) ∧
    physicalBill qids t (retainedRun qids .complete t adverse delta good c beta Cref tolerance cap) =
      (qids.card : ℝ)*(baseBill t+t.bge+tailBill t) ∧
    physicalBill qids t (retainedRun qids .next t adverse delta good c beta Cref tolerance cap) =
      (qids.card : ℝ)*(baseBill t+t.normalE5+tailBill t) := by
  obtain ⟨ha,hb⟩ := retained_generated_histories qids t adverse delta good c beta Cref tolerance cap hc hm hw hp
  rw [ha,hb,physical_a10_bill,physical_b9_bill]
  obtain ⟨hqa,hqb⟩ := retained_task_best adverse delta good hm.delta_pos.le hm.delta_le_good
  exact ⟨hqa,hqb,rfl,rfl⟩

theorem retained_generated_net_difference (qids : Finset Qid) (t : TariffInput)
    (adverse : Bool) (delta good c beta Cref tolerance lambda : ℝ) (cap : ℕ) (hc : 11 ≤ cap)
    (hm : RootMargins t c (penaltyScale qids beta Cref) delta good)
    (hw : StrictResourceWindow (qids.card : ℝ) t tolerance) (hp : ∀ a,0 ≤ tariff t a) :
    retainedNet qids .complete t adverse delta good c beta Cref tolerance lambda cap-
      retainedNet qids .next t adverse delta good c beta Cref tolerance lambda cap =
    (if adverse then delta-good else good-delta)-lambda*(qids.card : ℝ)*(t.bge-t.normalE5)/Cref := by
  obtain ⟨hqa,hqb,hba,hbb⟩ := retained_generated_best_and_bills qids t adverse delta good c beta Cref tolerance cap hc hm hw hp
  dsimp only [retainedNet]
  rw [hqa,hqb,hba,hbb]
  cases adverse <;> simp only [Bool.false_eq_true,if_false,if_true] <;> ring

theorem retained_positive_separation (qids : Finset Qid) (t : TariffInput)
    (delta good c beta Cref tolerance lambda : ℝ) (cap : ℕ) (hc : 11 ≤ cap)
    (hm : RootMargins t c (penaltyScale qids beta Cref) delta good)
    (hw : StrictResourceWindow (qids.card : ℝ) t tolerance) (hp : ∀ a,0 ≤ tariff t a)
    (hgap : lambda*(qids.card : ℝ)*(t.bge-t.normalE5)/Cref < good-delta) :
    retainedNet qids .next t false delta good c beta Cref tolerance lambda cap <
      retainedNet qids .complete t false delta good c beta Cref tolerance lambda cap := by
  have hh := retained_generated_net_difference qids t false delta good c beta Cref tolerance lambda cap hc hm hw hp
  simp only [Bool.false_eq_true,if_false] at hh
  linarith

theorem retained_adverse_separation (qids : Finset Qid) (t : TariffInput)
    (delta good c beta Cref tolerance lambda : ℝ) (cap : ℕ) (hc : 11 ≤ cap)
    (hm : RootMargins t c (penaltyScale qids beta Cref) delta good)
    (hw : StrictResourceWindow (qids.card : ℝ) t tolerance) (hp : ∀ a,0 ≤ tariff t a)
    (hgap : delta-good < lambda*(qids.card : ℝ)*(t.bge-t.normalE5)/Cref) :
    retainedNet qids .complete t true delta good c beta Cref tolerance lambda cap <
      retainedNet qids .next t true delta good c beta Cref tolerance lambda cap := by
  have hh := retained_generated_net_difference qids t true delta good c beta Cref tolerance lambda cap hc hm hw hp
  simp only [if_true] at hh
  linarith

theorem whole_crossing_bills (qids : Finset Qid) (t : TariffInput)
    (adverse : Bool) (delta good c beta Cref tolerance : ℝ) (cap : ℕ) (hc : 11 ≤ cap)
    (hm : RootMargins t c (penaltyScale qids beta Cref) delta good)
    (hw : StrictResourceWindow (qids.card : ℝ) t tolerance) (hp : ∀ a,0 ≤ tariff t a) :
    physicalBill qids t (referenceRun qids .complete t adverse delta good c beta Cref cap) =
      (qids.card : ℝ)*(baseBill t+t.bge+tailBill t+crossBill t) ∧
    physicalBill qids t (referenceRun qids .next t adverse delta good c beta Cref cap) =
      (qids.card : ℝ)*(baseBill t+t.normalE5+2*tailBill t+t.bge) := by
  obtain ⟨ha,hb⟩ := both_task_tables_generated qids t adverse delta good c beta Cref tolerance cap hc hm hw hp
  unfold referenceRun
  rw [ha,hb,physical_a11_bill,physical_b10_bill]
  exact ⟨rfl,rfl⟩

theorem whole_spending_retained_net_difference (qids : Finset Qid) (t : TariffInput)
    (adverse : Bool) (delta good c beta Cref tolerance lambda : ℝ) (cap : ℕ) (hc : 11 ≤ cap)
    (hm : RootMargins t c (penaltyScale qids beta Cref) delta good)
    (hw : StrictResourceWindow (qids.card : ℝ) t tolerance) (hp : ∀ a,0 ≤ tariff t a) :
    wholeSpendingRetainedNet qids .complete t adverse delta good c beta Cref tolerance lambda cap-
      wholeSpendingRetainedNet qids .next t adverse delta good c beta Cref tolerance lambda cap =
    (if adverse then delta-good else good-delta)+lambda*(qids.card : ℝ)*(t.normalE5+tailBill t-crossBill t)/Cref := by
  obtain ⟨hqa,hqb,hba,hbb⟩ := retained_generated_best_and_bills qids t adverse delta good c beta Cref tolerance cap hc hm hw hp
  obtain ⟨ha,hb⟩ := whole_crossing_bills qids t adverse delta good c beta Cref tolerance cap hc hm hw hp
  unfold wholeSpendingRetainedNet
  rw [hqa,hqb,ha,hb]
  cases adverse <;> simp only [Bool.false_eq_true,if_false,if_true] <;> ring

end AgentUCTNativeBudget
