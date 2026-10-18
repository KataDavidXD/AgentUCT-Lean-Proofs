import NativeBudgetResources




set_option autoImplicit false
set_option maxRecDepth 16384
set_option maxHeartbeats 4000000
set_option linter.constructorNameAsVariable false
noncomputable section
namespace AgentUCTNativeBudget
open AgentUCTPanelAllocation AgentUCTNativeRepair AgentUCTNativeRefinement AgentUCTPaper
variable {Qid : Type*} [DecidableEq Qid]

structure TariffInput where
  query : Fin 8 → ℝ
  hydeE5 : ℝ
  bge : ℝ
  qwen : ℝ
  normalE5 : ℝ
  w2 : ℝ
  w4 : ℝ
  ans2 : ℝ
  ans6 : ℝ
  rerank : ℝ

def tariff (t : TariffInput) : Act → ℝ := taskTariff t.query t.hydeE5 t.bge t.qwen
  t.normalE5 t.w2 t.w4 t.ans2 t.ans6 t.rerank
def baseBill (t : TariffInput) := eightBill t.query t.hydeE5 t.w2 t.ans2
def tailBill (t : TariffInput) := t.w4+t.ans2
def crossBill (t : TariffInput) := t.qwen+t.w2+t.ans6
def physicalBill (qids : Finset Qid) (t : TariffInput) (events : List (TreeEvaluation Act)) : ℝ :=
  panelActualBill qids (fun r => tariff t (resourceAction r)) events
def taskBudget (qids : Finset Qid) (t : TariffInput) : ℝ :=
  (qids.card : ℝ)*(baseBill t+t.bge+tailBill t+tailBill t/2)

def StrictResourceWindow (n : ℝ) (t : TariffInput) (tolerance : ℝ) : Prop :=
  0 < n ∧ 0 < tailBill t ∧ 0 ≤ t.bge ∧ t.normalE5 < t.bge+tailBill t/2 ∧
  0 ≤ tolerance ∧ tolerance < n*(crossBill t-tailBill t/2) ∧
  tolerance < n*(t.normalE5+tailBill t/2)

theorem physical_bill_homogeneous (qids : Finset Qid) (t : TariffInput) (events : List (TreeEvaluation Act)) :
    physicalBill qids t events = (qids.card : ℝ)*(ownState (pathTariff (tariff t)) events).totalPaid := by
  exact homogeneous_panel_physical_bill qids (fun p => tariff t (p.getLastD .stop)) events

theorem physical_initial_bill (qids : Finset Qid) (t : TariffInput) (reward : List Act → ℝ) :
    physicalBill qids t (initialization reward) = (qids.card : ℝ)*baseBill t := by
  rw [physical_bill_homogeneous]
  exact congrArg (fun x => (qids.card : ℝ)*x) (eight_actual_bill reward t.query
    t.hydeE5 t.bge t.qwen t.normalE5 t.w2 t.w4 t.ans2 t.ans6 t.rerank)

theorem physical_a9_bill (qids : Finset Qid) (t : TariffInput) (reward : List Act → ℝ) :
    physicalBill qids t (aNine reward) = (qids.card : ℝ)*(baseBill t+t.bge+tailBill t) := by
  rw [physical_bill_homogeneous]
  unfold tariff
  rw [a_nine_actual_bill]
  simp only [baseBill,tailBill]
  ring

theorem physical_a10_bill (qids : Finset Qid) (t : TariffInput) (reward : List Act → ℝ) :
    physicalBill qids t (aTen reward) = (qids.card : ℝ)*(baseBill t+t.bge+tailBill t) := by
  rw [physical_bill_homogeneous,warm10_zero_model_increment]
  simpa only [physical_bill_homogeneous] using physical_a9_bill qids t reward

theorem physical_a11_bill (qids : Finset Qid) (t : TariffInput) (reward : List Act → ℝ) :
    physicalBill qids t (aEleven reward) =
      (qids.card : ℝ)*(baseBill t+t.bge+tailBill t+crossBill t) := by
  rw [physical_bill_homogeneous]
  unfold tariff
  rw [a_eleven_actual_bill]
  simp only [baseBill,tailBill,crossBill]
  ring

theorem physical_b9_bill (qids : Finset Qid) (t : TariffInput) (reward : List Act → ℝ) :
    physicalBill qids t (bNine reward) = (qids.card : ℝ)*(baseBill t+t.normalE5+tailBill t) := by
  rw [physical_bill_homogeneous]
  unfold tariff
  rw [b_nine_actual_bill]
  simp only [baseBill,tailBill]
  ring

theorem physical_b10_bill (qids : Finset Qid) (t : TariffInput) (reward : List Act → ℝ) :
    physicalBill qids t (bTen reward) = (qids.card : ℝ)*(baseBill t+t.normalE5+2*tailBill t+t.bge) := by
  rw [physical_bill_homogeneous]
  unfold tariff
  rw [b_ten_actual_bill]
  rfl

theorem resource_history_lengths (reward : List Act → ℝ) :
    (aNine reward).length = 9 ∧ (aTen reward).length = 10 ∧ (aEleven reward).length = 11 ∧
      (bNine reward).length = 9 ∧ (bTen reward).length = 10 := by
  simp [aNine,aTen,aEleven,bNine,bTen,initialization]

theorem a11_take10 (reward : List Act → ℝ) : (aEleven reward).take 10 = aTen reward := by
  exact List.take_left' (resource_history_lengths reward).2.1

theorem b10_take9 (reward : List Act → ℝ) : (bTen reward).take 9 = bNine reward := by
  exact List.take_left' (resource_history_lengths reward).2.2.2.1

theorem strict_window_endpoints (qids : Finset Qid) (t : TariffInput) (reward : List Act → ℝ)
    (tolerance : ℝ) (hw : StrictResourceWindow (qids.card : ℝ) t tolerance) :
    physicalBill qids t (aTen reward) < taskBudget qids t ∧
    physicalBill qids t (bNine reward) < taskBudget qids t ∧
    taskBudget qids t+tolerance < physicalBill qids t (aEleven reward) ∧
    taskBudget qids t+tolerance < physicalBill qids t (bTen reward) := by
  rcases hw with ⟨hn,ha,hb,he,ht,hac,hbc⟩
  rw [physical_a10_bill,physical_b9_bill,physical_a11_bill,physical_b10_bill]
  unfold taskBudget
  constructor
  · nlinarith
  constructor
  · have hp := mul_pos hn (show 0 < t.bge+tailBill t/2-t.normalE5 by linarith)
    nlinarith
  constructor <;> nlinarith

theorem resource_a_TB10 (qids : Finset Qid) (t : TariffInput) (reward : List Act → ℝ)
    (tolerance : ℝ) (hw : StrictResourceWindow (qids.card : ℝ) t tolerance) :
    panelReportingIndex qids (fun r => tariff t (resourceAction r)) (aEleven reward)
      (taskBudget qids t) tolerance = 10 := by
  obtain ⟨ha,hb,hac,hbc⟩ := strict_window_endpoints qids t reward tolerance hw
  apply panel_reporting_index_last_complete
  · rw [(resource_history_lengths reward).2.2.1]; omega
  · rw [a11_take10]
    exact le_trans ha.le (le_add_of_nonneg_right hw.2.2.2.2.1)
  · intro n hn hlen
    rw [(resource_history_lengths reward).2.2.1] at hlen
    have he : n = 11 := by omega
    subst n
    rw [show (aEleven reward).take 11 = aEleven reward by
      exact List.take_of_length_le (by rw [(resource_history_lengths reward).2.2.1])]
    exact not_le.mpr hac

theorem resource_b_TB9 (qids : Finset Qid) (t : TariffInput) (reward : List Act → ℝ)
    (tolerance : ℝ) (hw : StrictResourceWindow (qids.card : ℝ) t tolerance) :
    panelReportingIndex qids (fun r => tariff t (resourceAction r)) (bTen reward)
      (taskBudget qids t) tolerance = 9 := by
  obtain ⟨ha,hb,hac,hbc⟩ := strict_window_endpoints qids t reward tolerance hw
  apply panel_reporting_index_last_complete
  · rw [(resource_history_lengths reward).2.2.2.2]; omega
  · rw [b10_take9]
    exact le_trans hb.le (le_add_of_nonneg_right hw.2.2.2.2.1)
  · intro n hn hlen
    rw [(resource_history_lengths reward).2.2.2.2] at hlen
    have he : n = 10 := by omega
    subst n
    rw [show (bTen reward).take 10 = bTen reward by
      exact List.take_of_length_le (by rw [(resource_history_lengths reward).2.2.2.2])]
    exact not_le.mpr hbc

theorem resource_strict_actual_crossings (qids : Finset Qid) (t : TariffInput) (reward : List Act → ℝ)
    (tolerance : ℝ) (hw : StrictResourceWindow (qids.card : ℝ) t tolerance)
    (hp : ∀ a, 0 ≤ tariff t a) :
    (∀ k, k < 11 → physicalBill qids t ((aEleven reward).take k) < taskBudget qids t) ∧
    taskBudget qids t ≤ physicalBill qids t (aEleven reward) ∧
    (∀ k, k < 10 → physicalBill qids t ((bTen reward).take k) < taskBudget qids t) ∧
    taskBudget qids t ≤ physicalBill qids t (bTen reward) := by
  obtain ⟨ha,hb,hac,hbc⟩ := strict_window_endpoints qids t reward tolerance hw
  have hprice : ∀ r : Qid × List Act,0 ≤ tariff t (resourceAction r) := fun r => hp _
  constructor
  · intro k hk
    have hh := panel_actual_bill_prefix_monotone qids _ hprice
      ((aEleven reward).take k) ((aEleven reward).take 10) (List.take_prefix_take_left (by omega))
    rw [a11_take10] at hh
    exact lt_of_le_of_lt hh ha
  constructor
  · exact (le_add_of_nonneg_right hw.2.2.2.2.1).trans hac.le
  constructor
  · intro k hk
    have hh := panel_actual_bill_prefix_monotone qids _ hprice
      ((bTen reward).take k) ((bTen reward).take 9) (List.take_prefix_take_left (by omega))
    rw [b10_take9] at hh
    exact lt_of_le_of_lt hh hb
  · exact (le_add_of_nonneg_right hw.2.2.2.2.1).trans hbc.le

theorem strict_resource_window_inhabited : ∃ t : TariffInput, StrictResourceWindow 150 t 0 := by
  refine ⟨⟨fun _ => 1,1,2,2,1,2,5,5,4,3⟩,?_⟩
  norm_num [StrictResourceWindow,tailBill,crossBill]

end AgentUCTNativeBudget
