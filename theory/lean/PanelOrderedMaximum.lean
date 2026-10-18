import PanelHomogeneous



set_option autoImplicit false
noncomputable section
namespace AgentUCTPanelAllocation
open AgentUCTNativeRefinement AgentUCTNativeRepair AgentUCTPaper

def pickFirst (score : Act → ℝ) (a b : Act) : Act :=
  if score a < score b then b else a

theorem pickFirst_assoc (score : Act → ℝ) (a b d : Act) :
    pickFirst score (pickFirst score a b) d = pickFirst score a (pickFirst score b d) := by
  unfold pickFirst
  split_ifs <;> first | rfl | linarith

def leftOrderedMaximum (score : Act → ℝ) (choices : List Act) : Act :=
  choices.tail.foldl (pickFirst score) (choices.headD .stop)

theorem foldl_pickFirst (score : Act → ℝ) (a : Act) (rest : List Act)
    (hne : rest ≠ []) :
    rest.foldl (pickFirst score) a = pickFirst score a (firstMaximum score rest) := by
  induction rest generalizing a with
  | nil => exact False.elim (hne rfl)
  | cons b rest ih =>
      by_cases hr : rest = []
      · subst rest
        simp [firstMaximum]
      · rw [List.foldl_cons, ih _ hr]
        simp only [firstMaximum, if_neg hr]
        change pickFirst score (pickFirst score a b) (firstMaximum score rest) =
          pickFirst score a (pickFirst score b (firstMaximum score rest))
        exact pickFirst_assoc score a b _

theorem left_ordered_maximum_eq_firstMaximum (score : Act → ℝ) (choices : List Act) :
    leftOrderedMaximum score choices = firstMaximum score choices := by
  cases choices with
  | nil => rfl
  | cons a rest =>
      by_cases hr : rest = []
      · subst rest
        rfl
      · simp only [leftOrderedMaximum,List.tail_cons,List.headD_cons]
        rw [foldl_pickFirst score a rest hr]
        simp only [firstMaximum,if_neg hr,pickFirst]

def FirstOrderedMax (score : Act → ℝ) (choices : List Act) (chosen : Act) : Prop :=
  ∃ before after, choices = before ++ chosen :: after ∧
    (∀ b ∈ before, score b < score chosen) ∧
    (∀ b ∈ choices, score b ≤ score chosen)

theorem firstMaximum_first_ordered_max (score : Act → ℝ) (choices : List Act)
    (hne : choices ≠ []) : FirstOrderedMax score choices (firstMaximum score choices) := by
  induction choices with
  | nil => exact False.elim (hne rfl)
  | cons a rest ih =>
      by_cases hr : rest = []
      · subst rest
        exact ⟨[],[],rfl,by simp,by simp [firstMaximum]⟩
      · obtain ⟨pre,post,hdecomp,hstrict,hmax⟩ := ih hr
        by_cases hs : score a < score (firstMaximum score rest)
        · simp only [firstMaximum,if_neg hr,if_pos hs]
          refine ⟨a::pre,post,by simpa only [List.cons_append] using congrArg (a :: ·) hdecomp,?_,?_⟩
          · intro b hb
            rcases List.mem_cons.mp hb with rfl | hb
            · exact hs
            · exact hstrict b hb
          · intro b hb
            rcases List.mem_cons.mp hb with rfl | hb
            · exact hs.le
            · exact hmax b hb
        · simp only [firstMaximum,if_neg hr,if_neg hs]
          refine ⟨[],rest,rfl,by simp,?_⟩
          intro b hb
          rcases List.mem_cons.mp hb with rfl | hb
          · exact le_rfl
          · exact (hmax b hb).trans (le_of_not_gt hs)

theorem firstMaximum_max (score : Act → ℝ) (choices : List Act) (hne : choices ≠ [])
    (b : Act) (hb : b ∈ choices) : score b ≤ score (firstMaximum score choices) := by
  obtain ⟨_,_,_,_,hmax⟩ := firstMaximum_first_ordered_max score choices hne
  exact hmax b hb

theorem left_ordered_maximum_first_ordered_max (score : Act → ℝ)
    (choices : List Act) (hne : choices ≠ []) :
    FirstOrderedMax score choices (leftOrderedMaximum score choices) := by
  rw [left_ordered_maximum_eq_firstMaximum]
  exact firstMaximum_first_ordered_max score choices hne

end AgentUCTPanelAllocation
