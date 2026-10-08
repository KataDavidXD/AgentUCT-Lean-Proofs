import AgentUCT

/-! Finite cache-state models have a positive separation for every nonzero gap.
This is an instance-dependent separation; no uniform numerical lower bound is asserted. -/

noncomputable section
open Finset
namespace AgentUCTPaper

theorem finite_positive_gap (values : Finset ℝ) :
    ∃ delta : ℝ, 0 < delta ∧ ∀ g ∈ values, 0 < g → delta ≤ g := by
  classical
  induction values using Finset.induction_on with
  | empty => exact ⟨1, by norm_num, by simp⟩
  | @insert a s ha ih =>
    obtain ⟨delta, hd, hb⟩ := ih
    by_cases hp : 0 < a
    · refine ⟨min a delta, lt_min hp hd, ?_⟩
      intro g hg hgp
      rcases Finset.mem_insert.mp hg with hga | hgs
      · subst g
        exact min_le_left a delta
      · exact (min_le_right a delta).trans (hb g hgs hgp)
    · refine ⟨delta, hd, ?_⟩
      intro g hg hgp
      rcases Finset.mem_insert.mp hg with hga | hgs
      · exact (hp (hga ▸ hgp)).elim
      · exact hb g hgs hgp

/-- Apply `State = Finset Resource` for a finite qid-prefix materialization universe.
The net values must be fixed functions of this state: changing forecasters or
rollout distributions introduce further state and do not satisfy that model automatically. -/
theorem finite_state_gap_separation {State Arm : Type*} [Fintype State] [Fintype Arm]
    (value : State → Arm → ℝ) :
    ∃ delta : ℝ, 0 < delta ∧ ∀ s a b,
      0 < value s a - value s b → delta ≤ value s a - value s b := by
  classical
  let gaps := (Finset.univ : Finset (State × Arm × Arm)).image
    (fun x ↦ value x.1 x.2.1 - value x.1 x.2.2)
  obtain ⟨delta, hd, hb⟩ := finite_positive_gap gaps
  refine ⟨delta, hd, ?_⟩
  intro s a b hp
  apply hb _ _ hp
  exact Finset.mem_image.mpr ⟨(s, a, b), Finset.mem_univ _, rfl⟩

/-- Clipping a common baseline is not generally a common shift. Deep checkpoints
can make complete-path cold cost smaller than an uncached partial-prefix baseline. -/
theorem clipped_baseline_can_reverse_order :
    ((4 / 10 : ℝ) - 2 / 10 > 8 / 10 - 8 / 10) ∧
      ((4 / 10 : ℝ) - max 0 (2 / 10 - 1) < 8 / 10 - max 0 (8 / 10 - 1)) := by
  norm_num

end AgentUCTPaper
