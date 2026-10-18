import BetaTwoTrajectories





set_option autoImplicit false
set_option maxRecDepth 16384
set_option maxHeartbeats 4000000
noncomputable section
namespace AgentUCTPhysicalDiagnostic
open AgentUCTNativeBudget AgentUCTPanelAllocation AgentUCTNativeRepair AgentUCTNativeRefinement AgentUCTPaper

def CoveredNativeAction : Act → Prop
  | .normalRetriever r => r = 0 ∨ r = 1
  | .width w => w = 0 ∨ w = 1
  | .answer m => m = 0 ∨ m = 2
  | _ => True

instance coveredNativeActionDecidable (a : Act) : Decidable (CoveredNativeAction a) := by cases a <;> unfold CoveredNativeAction <;> infer_instance

def sourceRoleFields : Act → Finset (Fin 8)
  | .query q => if q = identityQuery then ∅ else {0,1}
  | .normalRetriever r => if r = 0 then ∅ else if r = 1 then {4} else if r = 2 then {2} else ∅
  | .hydeRetriever r => if r = 0 then {4} else if r = 1 then {5} else {2}
  | .width _ => {0,1}
  | .answer _ => {0,1}
  | .reranker r => if r = 0 then ∅ else {0,1}
  | _ => ∅

def sourceUsedCap : Act → ℝ
  | .query q => if q = identityQuery then 0 else 129200.67981311999
  | .normalRetriever r => if r = 0 then 0 else if r = 1 then 112.10981376 else 0
  | .hydeRetriever r => if r = 0 then 56.05490688 else if r = 1 then 291.228353024 else 4880.601186304
  | .width _ => 86133.78654208
  | .answer _ => 129200.67981311999
  | .reranker r => if r = 0 then 0 else 86133.78654208
  | _ => 0

theorem covered_invoices_respect_model_roles (a : Act) (ha : CoveredNativeAction a) (f : Fin 8)
    (hf : invoiceCounts a f ≠ 0) : f ∈ sourceRoleFields a := by
  cases a with
  | query q => by_cases hq : q = identityQuery <;> fin_cases f <;> simp_all [invoiceCounts,sourceRoleFields]
  | normalRetriever r => rcases ha with hr | hr <;> subst r <;> fin_cases f <;> simp_all [invoiceCounts,sourceRoleFields]
  | hydeRetriever r => fin_cases r <;> fin_cases f <;> simp_all [invoiceCounts,sourceRoleFields]
  | width w => rcases ha with hw | hw <;> subst w <;> fin_cases f <;> simp_all [invoiceCounts,sourceRoleFields]
  | answer m => rcases ha with hm | hm <;> subst m <;> fin_cases f <;> simp_all [invoiceCounts,sourceRoleFields]
  | reranker r => fin_cases r <;> fin_cases f <;> simp_all [invoiceCounts,sourceRoleFields]
  | selection s => fin_cases f <;> simp [invoiceCounts] at hf
  | stop => fin_cases f <;> simp [invoiceCounts] at hf
  | topm m => fin_cases f <;> simp [invoiceCounts] at hf
  | context c => fin_cases f <;> simp [invoiceCounts] at hf

theorem covered_invoice_static_caps (a : Act) (ha : CoveredNativeAction a) :
    tariff integerTariffs a+(if tariff integerTariffs a = 0 then 0 else 1/2) ≤ sourceUsedCap a := by
  cases a with
  | normalRetriever r => rcases ha with hr | hr <;> subst r <;>
      norm_num [tariff,taskTariff,integerTariffs,sourceUsedCap,generatorRate,e5Rate,bgeRate,embeddingRate]
  | query q => by_cases hq : q = identityQuery <;>
      norm_num [tariff,taskTariff,integerTariffs,sourceUsedCap,hq,generatorRate,e5Rate,bgeRate,embeddingRate]
  | hydeRetriever r => fin_cases r <;>
      norm_num [tariff,taskTariff,integerTariffs,sourceUsedCap,generatorRate,e5Rate,bgeRate,embeddingRate]
  | width w => rcases ha with hw | hw <;> subst w <;>
      norm_num [tariff,taskTariff,integerTariffs,sourceUsedCap,generatorRate,e5Rate,bgeRate,embeddingRate]
  | answer m => rcases ha with hm | hm <;> subst m <;>
      norm_num [tariff,taskTariff,integerTariffs,sourceUsedCap,generatorRate,e5Rate,bgeRate,embeddingRate,
        show (2 : Fin 3) ≠ 0 by decide]
  | reranker r => fin_cases r <;>
      norm_num [tariff,taskTariff,integerTariffs,sourceUsedCap,generatorRate,e5Rate,bgeRate,embeddingRate]
  | selection _ | stop | topm _ | context _ => simp [tariff,taskTariff,sourceUsedCap]

theorem unit_companion_caches_covered (reward : List Act → ℝ) :
    (∀ r ∈ ownCache (aEleven reward),CoveredNativeAction (resourceAction r)) ∧
    (∀ r ∈ ownCache (bTen reward),CoveredNativeAction (resourceAction r)) := by
  change (∀ r ∈ ownCache (aEleven (fun _ => 0)),CoveredNativeAction (resourceAction r)) ∧
    (∀ r ∈ ownCache (bTen (fun _ => 0)),CoveredNativeAction (resourceAction r))
  decide

theorem companion_panel_caches_covered (qids : Finset (Fin 150)) (reward : List Act → ℝ) :
    (∀ r ∈ ownPanelCache qids (aEleven reward),CoveredNativeAction (resourceAction r)) ∧
    (∀ r ∈ ownPanelCache qids (bTen reward),CoveredNativeAction (resourceAction r)) := by
  constructor
  ·
    intro r hr
    rw [own_panel_cache_product] at hr
    have hp := (Finset.mem_product.mp hr).2
    have hu : ((),r.2) ∈ ownCache (aEleven reward) := by
      rw [← unit_panel_cache_is_own,own_panel_cache_product]
      exact Finset.mem_product.mpr ⟨by simp,hp⟩
    simpa only [resourceAction] using (unit_companion_caches_covered reward).1 ((),r.2) hu
  · intro r hr
    rw [own_panel_cache_product] at hr
    have hp := (Finset.mem_product.mp hr).2
    have hu : ((),r.2) ∈ ownCache (bTen reward) := by
      rw [← unit_panel_cache_is_own,own_panel_cache_product]
      exact Finset.mem_product.mpr ⟨by simp,hp⟩
    simpa only [resourceAction] using (unit_companion_caches_covered reward).2 ((),r.2) hu

theorem root_mc_samples_covered (q : Fin 8) :
    ∀ a ∈ safeCompletion [.query q],CoveredNativeAction a := by
  fin_cases q <;> decide

def attemptCeiling : Act → ℕ
  | .query _ => 3
  | .answer _ => 3
  | .width _ => 2
  | .reranker _ => 2
  | _ => 0

theorem invoice_integer_count_bounds (a : Act) :
    invoiceCounts a 0 ≤ 8192*attemptCeiling a ∧ invoiceCounts a 1 ≤ 2048*attemptCeiling a ∧
    invoiceCounts a 2 ≤ 8192 ∧ invoiceCounts a 4 ≤ 1024 ∧ invoiceCounts a 5 ≤ 512 ∧
    invoiceCounts a 3 = 0 ∧ invoiceCounts a 6 = 0 ∧ invoiceCounts a 7 = 0 := by
  cases a <;> simp only [invoiceCounts,attemptCeiling]
  all_goals (try split_ifs) <;> decide

theorem shadow_table_not_all_native_roles :
    invoiceCounts (.normalRetriever 2) 4 ≠ 0 ∧ (4 : Fin 8) ∉ sourceRoleFields (.normalRetriever 2) := by
  decide

theorem generated_integer_invoice_footprint_nonempty (cap : ℕ) (hcap : 11 ≤ cap) :
    ∃ epsilon : ℝ,0 < epsilon ∧
      (∀ adverse : Bool,
        (∀ r ∈ ownPanelCache panel150 (diagnosticRun epsilon .complete adverse cap),
          CoveredNativeAction (resourceAction r)) ∧
        (∀ r ∈ ownPanelCache panel150 (diagnosticRun epsilon .next adverse cap),
          CoveredNativeAction (resourceAction r))) ∧
      diagnosticNet epsilon .next false cap < diagnosticNet epsilon .complete false cap ∧
      diagnosticNet epsilon .complete true cap < diagnosticNet epsilon .next true cap := by
  obtain ⟨epsilon,he,hgen,hpos,hadverse,herr⟩ := beta2_complete_causal_class_nonempty cap hcap
  refine ⟨epsilon,he,?_,hpos,hadverse⟩
  intro adverse
  rw [(hgen adverse).1,(hgen adverse).2]
  exact companion_panel_caches_covered panel150 _

end AgentUCTPhysicalDiagnostic
