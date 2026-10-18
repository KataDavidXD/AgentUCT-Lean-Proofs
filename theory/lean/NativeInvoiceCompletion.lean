import ObservedReceiptEquality




set_option autoImplicit false
set_option maxRecDepth 16384
set_option maxHeartbeats 4000000
set_option linter.constructorNameAsVariable false
noncomputable section
namespace AgentUCTObservability
open AgentUCTPhysicalDiagnostic AgentUCTNativeBudget AgentUCTPanelAllocation
  AgentUCTNativeRepair AgentUCTNativeRefinement AgentUCTPaper

def fullNormalRoles (r : Fin 30) : Finset (Fin 8) :=
  if r.val = 0 then ∅ else if r.val = 1 then {4} else if r.val = 2 then {2}
  else if r.val = 3 then {2,4,5} else if r.val < 9 then {5}
  else if r.val < 12 then {4} else if r.val < 15 then {5}
  else if r.val < 18 then {2} else if r.val < 21 then {4,5}
  else if r.val < 24 then {2,4,5} else if r.val < 27 then {4} else {2}

def fullRoleFields (a : Act) : Finset (Fin 8) :=
  match a with | .normalRetriever r => fullNormalRoles r | _ => sourceRoleFields a

def fullNormalCap (r : Fin 30) : ℝ :=
  if r.val = 0 then 0 else if r.val = 1 then 112.10981376 else if r.val = 2 then 9761.202372608
  else if r.val = 3 then 10164.540539392001 else if r.val < 9 then 291.228353024
  else if r.val < 12 then 112.10981376 else if r.val < 15 then 291.228353024
  else if r.val < 18 then 9761.202372608 else if r.val < 21 then 403.338166784
  else if r.val < 24 then 10164.540539392001 else if r.val < 27 then 112.10981376 else 9761.202372608

def fullStaticCap (a : Act) : ℝ :=
  match a with | .normalRetriever r => fullNormalCap r | _ => sourceUsedCap a

def fullCountBound (a : Act) (f : Fin 8) : ℕ :=
  if f = 0 then 8192*attemptCeiling a else if f = 1 then 2048*attemptCeiling a
  else if f = 2 then (match a with | .normalRetriever _ => 16384 | _ => 8192)
  else if f = 4 then (match a with | .hydeRetriever _ => 512 | _ => 1024)
  else if f = 5 then 512 else 0

def StaticUnusedInvoices (unused : Act → Fin 8 → ℕ) : Prop :=
  ∀ a,¬ CoveredNativeAction a →
    (∀ f,unused a f ≠ 0 → f ∈ fullRoleFields a) ∧
    modelTokenBill Finset.univ frozenWeights (unused a) ≤ fullStaticCap a ∧
    (∀ f,unused a f ≤ fullCountBound a f)

def completedCounts (unused : Act → Fin 8 → ℕ) (a : Act) : Fin 8 → ℕ :=
  if CoveredNativeAction a then invoiceCounts a else unused a

def completedPrice (unused : Act → Fin 8 → ℕ) (a : Act) : ℝ :=
  modelTokenBill Finset.univ frozenWeights (completedCounts unused a)

theorem covered_full_role_agreement (a : Act) (ha : CoveredNativeAction a) :
    fullRoleFields a = sourceRoleFields a := by
  cases a with
  | normalRetriever r => rcases ha with hr | hr <;> subst r <;> decide
  | query _ | hydeRetriever _ | selection _ | width _ | reranker _ | stop | topm _ | context _ | answer _ => rfl

theorem covered_full_cap_agreement (a : Act) (ha : CoveredNativeAction a) :
    fullStaticCap a = sourceUsedCap a := by
  cases a with
  | normalRetriever r => rcases ha with hr | hr <;> subst r <;> norm_num [fullStaticCap,fullNormalCap,sourceUsedCap]
  | query _ | hydeRetriever _ | selection _ | width _ | reranker _ | stop | topm _ | context _ | answer _ => rfl

theorem completed_price_agrees_on_all_observed_actions (unused : Act → Fin 8 → ℕ) :
    AgreeCovered (tariff integerTariffs) (completedPrice unused) := by
  intro a ha
  simp only [completedPrice,completedCounts,if_pos ha]
  exact shadow_invoice_algebra a

theorem completed_invoices_all_native_roles (unused : Act → Fin 8 → ℕ) (hu : StaticUnusedInvoices unused)
    (a : Act) (f : Fin 8) (hf : completedCounts unused a f ≠ 0) : f ∈ fullRoleFields a := by
  by_cases ha : CoveredNativeAction a
  · rw [covered_full_role_agreement a ha]
    apply covered_invoices_respect_model_roles a ha f
    simpa only [completedCounts,if_pos ha] using hf
  · exact (hu a ha).1 f (by simpa only [completedCounts,if_neg ha] using hf)

theorem completed_invoices_all_static_caps (unused : Act → Fin 8 → ℕ) (hu : StaticUnusedInvoices unused)
    (a : Act) : completedPrice unused a ≤ fullStaticCap a := by
  by_cases ha : CoveredNativeAction a
  · rw [← completed_price_agrees_on_all_observed_actions unused a ha,covered_full_cap_agreement a ha]
    have hm := covered_invoice_static_caps a ha
    have hn : (0:ℝ) ≤ if tariff integerTariffs a = 0 then 0 else 1/2 := by split_ifs <;> norm_num
    linarith
  · simpa only [completedPrice,completedCounts,if_neg ha] using (hu a ha).2.1

def unitRoleUnused (a : Act) (f : Fin 8) : ℕ := if f ∈ fullRoleFields a then 1 else 0

theorem field_weight_bounds (f : Fin 8) : 0 ≤ frozenWeights f ∧ frozenWeights f ≤ generatorRate := by
  fin_cases f <;> norm_num [frozenWeights,generatorRate,e5Rate,bgeRate,embeddingRate]

theorem unit_role_bill_bound (a : Act) : modelTokenBill Finset.univ frozenWeights (unitRoleUnused a) ≤ 8*generatorRate := by
  have hs : ∀ f : Fin 8,frozenWeights f*(unitRoleUnused a f : ℝ) ≤ generatorRate := by
    intro f
    by_cases hf : f ∈ fullRoleFields a
    · simpa [unitRoleUnused,hf] using (field_weight_bounds f).2
    · simp [unitRoleUnused,hf,generatorRate]; norm_num
  have hh := Finset.sum_le_sum (s := (Finset.univ : Finset (Fin 8))) (fun f _ => hs f)
  simpa [modelTokenBill,mul_comm] using hh

theorem unused_static_cap_floor (a : Act) (ha : ¬ CoveredNativeAction a) : 8*generatorRate ≤ fullStaticCap a := by
  cases a with
  | normalRetriever r => fin_cases r <;> (try norm_num [CoveredNativeAction] at ha) <;>
      norm_num [fullStaticCap,fullNormalCap,generatorRate]
  | width w => norm_num [fullStaticCap,sourceUsedCap,generatorRate]
  | answer m => norm_num [fullStaticCap,sourceUsedCap,generatorRate]
  | query _ | hydeRetriever _ | selection _ | reranker _ | stop | topm _ | context _ => simp [CoveredNativeAction] at ha

theorem unit_role_count_bounds (a : Act) (f : Fin 8) : unitRoleUnused a f ≤ fullCountBound a f := by
  cases a with
  | query q => fin_cases q <;> fin_cases f <;> decide
  | normalRetriever r => fin_cases r <;> fin_cases f <;> decide
  | hydeRetriever r => fin_cases r <;> fin_cases f <;> decide
  | selection s => fin_cases s <;> fin_cases f <;> decide
  | width w => fin_cases w <;> fin_cases f <;> decide
  | reranker r => fin_cases r <;> fin_cases f <;> decide
  | answer m => fin_cases m <;> fin_cases f <;> decide
  | context c => fin_cases c <;> fin_cases f <;> decide
  | topm m => fin_cases m <;> fin_cases f <;> decide
  | stop => fin_cases f <;> decide

theorem shadow_invoice_count_bounds (a : Act) (f : Fin 8) : invoiceCounts a f ≤ fullCountBound a f := by
  cases a with
  | query q => fin_cases q <;> fin_cases f <;> decide
  | normalRetriever r => fin_cases r <;> fin_cases f <;> decide
  | hydeRetriever r => fin_cases r <;> fin_cases f <;> decide
  | selection s => fin_cases s <;> fin_cases f <;> decide
  | width w => fin_cases w <;> fin_cases f <;> decide
  | reranker r => fin_cases r <;> fin_cases f <;> decide
  | answer m => fin_cases m <;> fin_cases f <;> decide
  | context c => fin_cases c <;> fin_cases f <;> decide
  | topm m => fin_cases m <;> fin_cases f <;> decide
  | stop => fin_cases f <;> decide

theorem completed_invoices_all_token_bounds (unused : Act → Fin 8 → ℕ) (hu : StaticUnusedInvoices unused)
    (a : Act) (f : Fin 8) : completedCounts unused a f ≤ fullCountBound a f := by
  by_cases ha : CoveredNativeAction a
  · simpa only [completedCounts,if_pos ha] using shadow_invoice_count_bounds a f
  · simpa only [completedCounts,if_neg ha] using (hu a ha).2.2 f

theorem unit_role_unused_is_feasible : StaticUnusedInvoices unitRoleUnused := by
  intro a ha
  constructor
  · intro f hf
    by_contra hn
    simp [unitRoleUnused,hn] at hf
  · exact ⟨(unit_role_bill_bound a).trans (unused_static_cap_floor a ha),unit_role_count_bounds a⟩

theorem completed_table_static_nonempty : ∃ unused : Act → Fin 8 → ℕ,
    StaticUnusedInvoices unused ∧
    (∀ a f,completedCounts unused a f ≠ 0 → f ∈ fullRoleFields a) ∧
    (∀ a,completedPrice unused a ≤ fullStaticCap a) :=
  ⟨unitRoleUnused,unit_role_unused_is_feasible,
    completed_invoices_all_native_roles _ unit_role_unused_is_feasible,
    completed_invoices_all_static_caps _ unit_role_unused_is_feasible⟩

end AgentUCTObservability
