import NativeGeneratedAllocation



set_option autoImplicit false
noncomputable section
namespace AgentUCTRealIndex
open AgentUCTPanelAllocation AgentUCTNativeRepair AgentUCTNativeRefinement AgentUCTPaper

theorem native_after_from_prefix_certificate (tape : SharedTape) (c : ℝ)
    (penalty : List (TreeEvaluation Act) → List Act → Act → ℝ)
    (actualBill : List (TreeEvaluation Act) → ℝ) (B : ℝ) (reward : List Act → ℝ)
    (proposal : List (TreeEvaluation Act)) (base : ℕ)
    (hproper : ∀ i,base ≤ i → i < proposal.length → actualBill (proposal.take i) < B)
    (hfinal : B ≤ actualBill proposal)
    (hstep : ∀ i,base ≤ i → (hi : i < proposal.length) →
      nativeEvent tape c penalty reward (proposal.take i) = proposal[i])
    (fuel k : ℕ) (hbase : base ≤ k) (hk : k ≤ proposal.length)
    (hfuel : proposal.length ≤ fuel+k) :
    nativeAfter tape c penalty actualBill B reward fuel (proposal.take k) = proposal := by
  induction fuel generalizing k with
  | zero =>
      have he : k = proposal.length := by omega
      subst k
      simp only [nativeAfter,List.take_length]
  | succ fuel ih =>
      by_cases he : k = proposal.length
      · subst k
        simp only [List.take_length,nativeAfter,targetReached,if_pos hfinal]
      · have hlt : k < proposal.length := by omega
        have hcontinue : ¬ targetReached (actualBill (proposal.take k)) B :=
          not_le.mpr (hproper k hbase hlt)
        rw [nativeAfter,if_neg hcontinue,hstep k hbase hlt,
          ← List.take_succ_eq_append_getElem hlt]
        exact ih (k+1) (by omega) (by omega) (by omega)

theorem native_after_from_base_certificate (tape : SharedTape) (c : ℝ)
    (penalty : List (TreeEvaluation Act) → List Act → Act → ℝ)
    (actualBill : List (TreeEvaluation Act) → ℝ) (B : ℝ) (reward : List Act → ℝ)
    (proposal : List (TreeEvaluation Act)) (base cap : ℕ)
    (hbase : base ≤ proposal.length) (hcap : proposal.length ≤ cap)
    (hproper : ∀ i,base ≤ i → i < proposal.length → actualBill (proposal.take i) < B)
    (hfinal : B ≤ actualBill proposal)
    (hstep : ∀ i,base ≤ i → (hi : i < proposal.length) →
      nativeEvent tape c penalty reward (proposal.take i) = proposal[i]) :
    nativeAfter tape c penalty actualBill B reward (cap-base) (proposal.take base) = proposal := by
  apply native_after_from_prefix_certificate tape c penalty actualBill B reward proposal base
    hproper hfinal hstep (cap-base) base (le_refl _) hbase
  omega

end AgentUCTRealIndex
