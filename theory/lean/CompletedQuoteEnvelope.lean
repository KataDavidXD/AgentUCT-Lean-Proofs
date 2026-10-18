import PhysicalQuoteProjection

set_option autoImplicit false
set_option maxRecDepth 16384
set_option maxHeartbeats 12000000
noncomputable section
namespace AgentUCT32MConcrete
open AgentUCT32MContinuation AgentUCTSavedBudget AgentUCTObservability
  AgentUCTPhysicalDiagnostic AgentUCTNativeBudget AgentUCTPanelAllocation
  AgentUCTNativeRepair AgentUCTNativeRefinement AgentUCTPaper

theorem completed_global_initial_quote_contract (epsilon : ℝ)
    (he : 0 < epsilon) (hehalf : epsilon < 1/2) :
    (∀ a,completedPrice unitRoleUnused a ≤ completedCaps epsilon a) ∧
    (∀ a,|min (completedCaps epsilon a) (completedPriors epsilon unitRoleUnused a)-
      completedPrice unitRoleUnused a| ≤ epsilon) ∧
    (∀ a,completedPrice unitRoleUnused a = 0 →
      min (completedCaps epsilon a) (completedPriors epsilon unitRoleUnused a) = 0) := by
  obtain ⟨hen,hcaps,hprior,hzero,hfloor⟩ := perturbed_initial_prices_admissible
    integerTariffs epsilon he hehalf integer_tariffs_positive_floor
  have hcap : ∀ a,completedPrice unitRoleUnused a ≤ completedCaps epsilon a := by
    intro a
    by_cases hc : CoveredNativeAction a
    · rw [completedCaps,if_pos hc,← completed_price_agrees_on_all_observed_actions unitRoleUnused a hc]
      exact hcaps a
    · simpa only [completedCaps,if_neg hc] using
        completed_invoices_all_static_caps unitRoleUnused unit_role_unused_is_feasible a
  refine ⟨hcap,?_,?_⟩
  · intro a
    by_cases hc : CoveredNativeAction a
    · simp only [completedCaps,completedPriors,if_pos hc]
      rw [← completed_price_agrees_on_all_observed_actions unitRoleUnused a hc]
      exact hprior a
    · rw [completedPriors,if_neg hc,min_eq_right (hcap a),sub_self,abs_zero]
      exact he.le
  · intro a hz
    by_cases hc : CoveredNativeAction a
    · have hzt : tariff integerTariffs a = 0 := by
        rw [completed_price_agrees_on_all_observed_actions unitRoleUnused a hc]
        exact hz
      simpa only [completedCaps,completedPriors,if_pos hc] using hzero a hzt
    · rw [completedPriors,if_neg hc,min_eq_right (hcap a),hz]

theorem completed_price_positive_floor (a : Act) :
    completedPrice unitRoleUnused a = 0 ∨ (1/10:ℝ) ≤ completedPrice unitRoleUnused a := by
  by_cases hc : CoveredNativeAction a
  · rw [← completed_price_agrees_on_all_observed_actions unitRoleUnused a hc]
    rcases integer_tariffs_positive_floor a with hz | hp
    · exact Or.inl hz
    · right; linarith
  · cases a with
    | normalRetriever r =>
        fin_cases r <;> (try simp [CoveredNativeAction] at hc) <;> norm_num [completedPrice,completedCounts,CoveredNativeAction,modelTokenBill,
          Fin.sum_univ_succ,frozenWeights,unitRoleUnused,fullRoleFields,fullNormalRoles,
          generatorRate,e5Rate,bgeRate,embeddingRate,sourceRoleFields,Fin.succ,Matrix.cons_val_zero,Matrix.cons_val_succ] <;> simp +decide [unitRoleUnused,fullRoleFields,sourceRoleFields] <;> norm_num
    | width w =>
        fin_cases w <;> (try simp [CoveredNativeAction] at hc) <;> norm_num [completedPrice,completedCounts,CoveredNativeAction,modelTokenBill,
          Fin.sum_univ_succ,frozenWeights,unitRoleUnused,fullRoleFields,fullNormalRoles,
          generatorRate,e5Rate,bgeRate,embeddingRate,sourceRoleFields,Fin.succ,Matrix.cons_val_zero,Matrix.cons_val_succ] <;> simp +decide [unitRoleUnused,fullRoleFields,sourceRoleFields] <;> norm_num
    | answer m =>
        fin_cases m <;> (try simp [CoveredNativeAction] at hc) <;> norm_num [completedPrice,completedCounts,CoveredNativeAction,modelTokenBill,
          Fin.sum_univ_succ,frozenWeights,unitRoleUnused,fullRoleFields,fullNormalRoles,
          generatorRate,e5Rate,bgeRate,embeddingRate,sourceRoleFields,Fin.succ,Matrix.cons_val_zero,Matrix.cons_val_succ] <;> simp +decide [unitRoleUnused,fullRoleFields,sourceRoleFields] <;> norm_num
    | stop | query _ | hydeRetriever _ | selection _ | reranker _ | topm _ | context _ =>
        simp [CoveredNativeAction] at hc

theorem completed_live_receipt_error_all_histories (epsilon : ℝ)
    (he : 0 < epsilon) (hehalf : epsilon < 1/2)
    (before : List (TreeEvaluation Act)) (r : Fin 150 × List Act) :
    |liveReceiptPrice (completedPriors epsilon unitRoleUnused) (completedCaps epsilon)
      (observedMeans panel150 (completedPrice unitRoleUnused) (completedCaps epsilon) 0 before) r-
      completedPrice unitRoleUnused (resourceAction r)| ≤ epsilon := by
  obtain ⟨hc,hp,hz⟩ := completed_global_initial_quote_contract epsilon he hehalf
  apply causal_live_price_error_from_initial_state _ _ _ epsilon _ _ he.le hc hp
    (empty_receipt_means_has_zero_error _ epsilon 0)
  intro events event row hr
  exact (complete_rows_member_values panel150 _ events event row hr).2.2

theorem completed_zero_action_price_exact (epsilon : ℝ)
    (he : 0 < epsilon) (hehalf : epsilon < 1/2)
    (before : List (TreeEvaluation Act)) (r : Fin 150 × List Act)
    (hrzero : completedPrice unitRoleUnused (resourceAction r) = 0) :
    liveReceiptPrice (completedPriors epsilon unitRoleUnused) (completedCaps epsilon)
      (observedMeans panel150 (completedPrice unitRoleUnused) (completedCaps epsilon) 0 before) r = 0 := by
  obtain ⟨hc,hp,hz⟩ := completed_global_initial_quote_contract epsilon he hehalf
  have hr := causal_receipts_propagate_initial_error (completedPrice unitRoleUnused) (completedCaps epsilon)
    0 (completeRows panel150 (fun r => completedPrice unitRoleUnused (resourceAction r)))
    (emptyReceiptMeans (0:Fin 150)) (by norm_num) hc
    (empty_receipt_means_has_zero_error _ 0 0)
    (fun before event row hrow => (complete_rows_member_values panel150 _ before event row hrow).2.2) before
  have hh : |liveReceiptPrice (completedPriors epsilon unitRoleUnused) (completedCaps epsilon)
      (observedMeans panel150 (completedPrice unitRoleUnused) (completedCaps epsilon) 0 before) r-0| ≤ 0 := by
    apply online_mean_absolute_error
    · simp [hz _ hrzero]
    · intro i hi
      obtain ⟨hseen,ha⟩ := selected_call_pool_valid _ r i hi
      have hri := hr i hseen
      change |(observedMeans panel150 (completedPrice unitRoleUnused) (completedCaps epsilon) 0 before).quotedValue i-
        completedPrice unitRoleUnused (resourceAction
          ((observedMeans panel150 (completedPrice unitRoleUnused) (completedCaps epsilon) 0 before).resource i))| ≤ 0 at hri
      simpa only [ha,hrzero] using hri
  exact by simpa using abs_nonpos_iff.mp hh

theorem completed_live_price_support_stable (epsilon : ℝ)
    (he : 0 < epsilon) (hesmall : epsilon < 1/10)
    (before : List (TreeEvaluation Act)) (r : Fin 150 × List Act) :
    liveReceiptPrice (completedPriors epsilon unitRoleUnused) (completedCaps epsilon)
      (observedMeans panel150 (completedPrice unitRoleUnused) (completedCaps epsilon) 0 before) r ≤ 0 ↔
      completedPrice unitRoleUnused (resourceAction r) ≤ 0 := by
  have hehalf : epsilon < 1/2 := by linarith
  rcases completed_price_positive_floor (resourceAction r) with hz | hp
  · rw [completed_zero_action_price_exact epsilon he hehalf before r hz,hz]
  · have herror := completed_live_receipt_error_all_histories epsilon he hehalf before r
    have hlo := (abs_le.mp herror).1
    have hpos : 0 < liveReceiptPrice (completedPriors epsilon unitRoleUnused) (completedCaps epsilon)
        (observedMeans panel150 (completedPrice unitRoleUnused) (completedCaps epsilon) 0 before) r := by linarith
    exact iff_of_false (not_le.mpr hpos) (by linarith)

end AgentUCT32MConcrete
