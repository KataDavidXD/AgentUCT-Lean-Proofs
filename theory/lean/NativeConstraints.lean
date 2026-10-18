import NativeLiveMeans




set_option autoImplicit false
set_option maxRecDepth 8192
set_option maxHeartbeats 3000000
noncomputable section
namespace AgentUCTNativeRefinement
open AgentUCTPaper



def formalWidth4Prior : ℝ := 4201.545544703999
def formalAnswer2Prior : ℝ := 1460.9250638196363
def formalAnswer6Prior : ℝ := 2545.6265571607273
def formalAnswer6Cap : ℝ := 129200.67981311999
def formalGamma : ℝ := 2/1470690.0198555747

theorem frozen_priors_do_not_share_generator_price :
    ¬ ∃ a : ℝ, a = formalWidth4Prior ∧ a = formalAnswer2Prior := by
  rintro ⟨a,hw,ha⟩
  have hne : formalWidth4Prior ≠ formalAnswer2Prior := by
    norm_num [formalWidth4Prior,formalAnswer2Prior]
  exact hne (hw.symm.trans ha)

theorem frozen_priors_do_not_realize_elevenfold_answer :
    formalAnswer6Prior ≠ 11*formalAnswer2Prior := by
  norm_num [formalAnswer6Prior,formalAnswer2Prior]




theorem frozen_strong_guard_and_inactive_cap_incompatible (a c : ℝ) (hc : 0 ≤ c)
    (hcap : 11*a ≤ formalAnswer6Cap) :
    ¬ (1+treeBonus c 10 1 < formalGamma*(12*a)) := by
  have hg : 0 ≤ formalGamma := by norm_num [formalGamma]
  have hu : a ≤ formalAnswer6Cap/11 := by linarith
  have hm := mul_le_mul_of_nonneg_left hu (show 0 ≤ formalGamma*12 by positivity)
  have hn : formalGamma*12*(formalAnswer6Cap/11) < 1 := by
    norm_num [formalGamma,formalAnswer6Cap]
  have hb := treeBonus_nonnegative hc 10 1
  intro h
  nlinarith



theorem unpublished_failed_work_is_extra_bill (successWork failedWork : ℝ)
    (hf : 0 < failedWork) : successWork < successWork+failedWork := by linarith

end AgentUCTNativeRefinement
