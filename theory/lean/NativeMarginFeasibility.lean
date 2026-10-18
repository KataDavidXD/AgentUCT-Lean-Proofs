import NativeRootSelectors




set_option autoImplicit false
set_option maxRecDepth 16384
set_option maxHeartbeats 4000000
set_option linter.constructorNameAsVariable false
noncomputable section
namespace AgentUCTNativeBudget
open AgentUCTPanelAllocation AgentUCTNativeRepair AgentUCTNativeRefinement AgentUCTPaper

theorem bonus_gap_two_positive (c : ℝ) (hc : 0 < c) : 0 < bonusGap2 c := by
  have hl : 0 < Real.log (10 : ℝ) := Real.log_pos (by norm_num)
  have hs := Real.sqrt_lt_sqrt (show 0 ≤ Real.log (10 : ℝ)/2 by positivity)
    (show Real.log (10 : ℝ)/2 < Real.log 10 by linarith)
  exact mul_pos hc (sub_pos.mpr hs)

theorem bonus_gap_three_positive (c : ℝ) (hc : 0 < c) : 0 < bonusGap3 c := by
  have hl : 0 < Real.log (11 : ℝ) := Real.log_pos (by norm_num)
  have hs := Real.sqrt_lt_sqrt (show 0 ≤ Real.log (11 : ℝ)/3 by positivity)
    (show Real.log (11 : ℝ)/3 < Real.log 11 by linarith)
  exact mul_pos hc (sub_pos.mpr hs)

def feasibleGood (c : ℝ) : ℝ := min 1 (bonusGap2 c)
def feasibleDelta (c : ℝ) : ℝ := 3*feasibleGood c/4
def feasibleTariffs (c : ℝ) : TariffInput :=
  ⟨fun q => if q = identityQuery then 0 else 1,1,1,1,1/2,1,1+feasibleGood c/2,1,1,
    4+feasibleGood c/2+feasibleDelta c+bonusGap2 c+bonusGap3 c⟩

theorem positive_bounded_feasible_good (c : ℝ) (hc : 0 < c) :
    0 < feasibleGood c ∧ feasibleGood c ≤ 1 ∧ feasibleGood c ≤ bonusGap2 c := by
  exact ⟨lt_min (by norm_num) (bonus_gap_two_positive c hc),min_le_left _ _,min_le_right _ _⟩

theorem root_structural_conditions_nonempty (c : ℝ) (hc : 0 < c) :
    RootMargins (feasibleTariffs c) c 1 (feasibleDelta c) (feasibleGood c) := by
  obtain ⟨hg,hg1,hg2⟩ := positive_bounded_feasible_good c hc
  have hd2 := bonus_gap_two_positive c hc
  have hd3 := bonus_gap_three_positive c hc
  constructor <;> dsimp [feasibleTariffs,feasibleDelta,normalForecastBill,tailBill] <;> nlinarith

theorem resource_window_same_nonempty_class (c : ℝ) (hc : 0 < c) :
    StrictResourceWindow 150 (feasibleTariffs c) 0 := by
  obtain ⟨hg,hg1,hg2⟩ := positive_bounded_feasible_good c hc
  dsimp [StrictResourceWindow,feasibleTariffs,tailBill,crossBill]
  constructor
  · norm_num
  constructor
  · linarith
  constructor
  · norm_num
  constructor
  · linarith
  constructor
  · rfl
  constructor <;> nlinarith

theorem same_class_nonnegative_tariffs (c : ℝ) (hc : 0 < c) (a : Act) :
    0 ≤ tariff (feasibleTariffs c) a := by
  obtain ⟨hg,hg1,hg2⟩ := positive_bounded_feasible_good c hc
  have hd2 := bonus_gap_two_positive c hc
  have hd3 := bonus_gap_three_positive c hc
  apply task_tariff_nonnegative
  · intro q
    dsimp [feasibleTariffs]
    split_ifs <;> norm_num
  · dsimp [feasibleTariffs,feasibleDelta]
    exact ⟨by norm_num,by norm_num,by norm_num,by norm_num,by norm_num,
      by nlinarith,by norm_num,by norm_num,by nlinarith⟩

theorem actual_default_c_positive_class :
    RootMargins (feasibleTariffs (7/5)) (7/5) 1 (feasibleDelta (7/5)) (feasibleGood (7/5)) ∧
    StrictResourceWindow 150 (feasibleTariffs (7/5)) 0 ∧
    (∀ a,0 ≤ tariff (feasibleTariffs (7/5)) a) :=
  ⟨root_structural_conditions_nonempty (7/5) (by norm_num),
   resource_window_same_nonempty_class (7/5) (by norm_num),
   same_class_nonnegative_tariffs (7/5) (by norm_num)⟩

end AgentUCTNativeBudget
