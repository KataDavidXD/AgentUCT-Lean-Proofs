import NativeBudgetEvents




set_option autoImplicit false
set_option maxRecDepth 16384
set_option maxHeartbeats 4000000
set_option linter.constructorNameAsVariable false
noncomputable section
namespace AgentUCTNativeBudget
open AgentUCTPanelAllocation AgentUCTNativeRepair AgentUCTNativeRefinement AgentUCTPaper
variable {Qid : Type*} [DecidableEq Qid]

theorem native_after_crossing_stops (tape : SharedTape) (c : ℝ)
    (penalty : List (TreeEvaluation Act) → List Act → Act → ℝ)
    (actualBill : List (TreeEvaluation Act) → ℝ) (B : ℝ) (reward : List Act → ℝ)
    (before : List (TreeEvaluation Act)) (hb : B ≤ actualBill before) (fuel : ℕ) :
    nativeAfter tape c penalty actualBill B reward fuel before = before := by
  cases fuel <;> simp [nativeAfter,targetReached,hb]

theorem initial_bill_below_task_budget (qids : Finset Qid) (t : TariffInput)
    (reward : List Act → ℝ) (tolerance : ℝ)
    (hw : StrictResourceWindow (qids.card : ℝ) t tolerance) (hp : ∀ a,0 ≤ tariff t a) :
    physicalBill qids t (initialization reward) < taskBudget qids t := by
  have hpre : initialization reward <+: aTen reward :=
    (List.prefix_append _ _).trans (List.prefix_append _ _)
  have hh := panel_actual_bill_prefix_monotone qids (fun r => tariff t (resourceAction r))
    (fun r => hp _) (initialization reward) (aTen reward) hpre
  exact lt_of_le_of_lt hh (strict_window_endpoints qids t reward tolerance hw).1

theorem reference_complete_generated (qids : Finset Qid) (t : TariffInput)
    (reward : List Act → ℝ) (delta good c beta Cref tolerance : ℝ) (cap : ℕ)
    (hc : 11 ≤ cap) (hs : SeedTable reward delta) (hr : 0 ≤ reward aCold)
    (hm : RootMargins t c (penaltyScale qids beta Cref) delta good)
    (hw : StrictResourceWindow (qids.card : ℝ) t tolerance) (hp : ∀ a,0 ≤ tariff t a) :
    nativeGenerate budgetTape c (referencePenalty qids .complete t beta Cref)
      (physicalBill qids t) (taskBudget qids t) reward cap = aEleven reward := by
  have hi := initial_bill_below_task_budget qids t reward tolerance hw hp
  obtain ⟨ha,hb,hac,hbc⟩ := strict_window_endpoints qids t reward tolerance hw
  have ha9 : physicalBill qids t (aNine reward) < taskBudget qids t := by
    rw [physical_a9_bill]
    rwa [physical_a10_bill] at ha
  have hx : taskBudget qids t ≤ physicalBill qids t (aEleven reward) :=
    (le_add_of_nonneg_right hw.2.2.2.2.1).trans hac.le
  unfold nativeGenerate
  rw [budget_common_eight_initialization,show cap-8 = (cap-11)+3 by omega]
  rw [show (cap-11)+3 = ((cap-11)+2)+1 by omega,nativeAfter]
  simp only [targetReached]
  rw [if_neg (not_le.mpr hi),reference_complete_initial_event qids t reward delta good c beta Cref hs hm]
  change nativeAfter budgetTape c (referencePenalty qids .complete t beta Cref)
    (physicalBill qids t) (taskBudget qids t) reward ((cap-11)+2) (aNine reward) = _
  rw [show (cap-11)+2 = ((cap-11)+1)+1 by omega,nativeAfter]
  simp only [targetReached]
  rw [if_neg (not_le.mpr ha9),reference_complete_a9_event qids t reward delta good c beta Cref hs hr hm]
  change nativeAfter budgetTape c (referencePenalty qids .complete t beta Cref)
    (physicalBill qids t) (taskBudget qids t) reward ((cap-11)+1) (aTen reward) = _
  rw [nativeAfter]
  simp only [targetReached]
  rw [if_neg (not_le.mpr ha),reference_complete_a10_event qids t reward delta good c beta Cref hs hr hm]
  exact native_after_crossing_stops budgetTape c _ _ _ reward (aEleven reward) hx (cap-11)

theorem reference_next_generated (qids : Finset Qid) (t : TariffInput)
    (reward : List Act → ℝ) (delta good c beta Cref tolerance : ℝ) (cap : ℕ)
    (hc : 10 ≤ cap) (hs : SeedTable reward delta) (hr : reward bCold ≤ good)
    (hm : RootMargins t c (penaltyScale qids beta Cref) delta good)
    (hw : StrictResourceWindow (qids.card : ℝ) t tolerance) (hp : ∀ a,0 ≤ tariff t a) :
    nativeGenerate budgetTape c (referencePenalty qids .next t beta Cref)
      (physicalBill qids t) (taskBudget qids t) reward cap = bTen reward := by
  have hi := initial_bill_below_task_budget qids t reward tolerance hw hp
  obtain ⟨ha,hb,hac,hbc⟩ := strict_window_endpoints qids t reward tolerance hw
  have hx : taskBudget qids t ≤ physicalBill qids t (bTen reward) :=
    (le_add_of_nonneg_right hw.2.2.2.2.1).trans hbc.le
  unfold nativeGenerate
  rw [budget_common_eight_initialization,show cap-8 = (cap-10)+2 by omega]
  rw [show (cap-10)+2 = ((cap-10)+1)+1 by omega,nativeAfter]
  simp only [targetReached]
  rw [if_neg (not_le.mpr hi),reference_next_initial_event qids t reward delta good c beta Cref hs hm]
  change nativeAfter budgetTape c (referencePenalty qids .next t beta Cref)
    (physicalBill qids t) (taskBudget qids t) reward ((cap-10)+1) (bNine reward) = _
  rw [nativeAfter]
  simp only [targetReached]
  rw [if_neg (not_le.mpr hb),reference_next_b9_event qids t reward delta good c beta Cref hs hr hm]
  exact native_after_crossing_stops budgetTape c _ _ _ reward (bTen reward) hx (cap-10)

theorem generated_reference_actual_reporting_indices (qids : Finset Qid) (t : TariffInput)
    (reward : List Act → ℝ) (delta good c beta Cref tolerance : ℝ) (cap : ℕ)
    (hc : 11 ≤ cap) (hs : SeedTable reward delta) (hra : 0 ≤ reward aCold) (hrb : reward bCold ≤ good)
    (hm : RootMargins t c (penaltyScale qids beta Cref) delta good)
    (hw : StrictResourceWindow (qids.card : ℝ) t tolerance) (hp : ∀ a,0 ≤ tariff t a) :
    panelReportingIndex qids (fun r => tariff t (resourceAction r))
      (nativeGenerate budgetTape c (referencePenalty qids .complete t beta Cref)
        (physicalBill qids t) (taskBudget qids t) reward cap) (taskBudget qids t) tolerance = 10 ∧
    panelReportingIndex qids (fun r => tariff t (resourceAction r))
      (nativeGenerate budgetTape c (referencePenalty qids .next t beta Cref)
        (physicalBill qids t) (taskBudget qids t) reward cap) (taskBudget qids t) tolerance = 9 := by
  rw [reference_complete_generated qids t reward delta good c beta Cref tolerance cap hc hs hra hm hw hp,
    reference_next_generated qids t reward delta good c beta Cref tolerance cap (by omega) hs hrb hm hw hp]
  exact ⟨resource_a_TB10 qids t reward tolerance hw,resource_b_TB9 qids t reward tolerance hw⟩

end AgentUCTNativeBudget
