import NativePanel150Witness





set_option autoImplicit false
set_option maxRecDepth 16384
set_option maxHeartbeats 4000000
noncomputable section
namespace AgentUCTPhysicalDiagnostic
open AgentUCTNativeBudget AgentUCTPanelAllocation AgentUCTNativeRepair AgentUCTNativeRefinement AgentUCTPaper

def generatorRate : ℝ := 4.205751296
def e5Rate : ℝ := 0.10948224
def bgeRate : ℝ := 0.568805377
def embeddingRate : ℝ := 0.595776512
def frozenWeights (f : Fin 8) : ℝ :=
  ![generatorRate,generatorRate,embeddingRate,0,e5Rate,bgeRate,0,embeddingRate] f

def invoiceCounts (a : Act) : Fin 8 → ℕ :=
  match a with
  | .query q => if q = identityQuery then ![0,0,0,0,0,0,0,0] else ![496,16,0,0,0,0,0,0]
  | .normalRetriever r => if r = 0 then ![0,0,0,0,0,0,0,0] else ![0,0,0,0,25,0,0,0]
  | .hydeRetriever r => if r = 0 then ![0,0,0,0,37,0,0,0]
      else if r = 1 then ![0,0,0,0,0,38,0,0] else ![0,0,39,0,0,0,0,0]
  | .width w => if w = 0 then ![384,128,0,0,0,0,0,0]
      else if w = 1 then ![192,128,0,0,0,0,0,0] else ![0,0,0,0,0,0,0,0]
  | .answer m => if m = 0 then ![1291,16,0,0,0,0,0,0]
      else if m = 2 then ![2032,16,0,0,0,0,0,0] else ![0,0,0,0,0,0,0,0]
  | .reranker r => if r = 0 then ![0,0,0,0,0,0,0,0] else ![16256,128,0,0,0,0,0,0]
  | _ => ![0,0,0,0,0,0,0,0]

def integerTariffs : TariffInput :=
  ⟨fun q => if q = identityQuery then 0 else generatorRate*512,
   e5Rate*37,bgeRate*38,embeddingRate*39,e5Rate*25,
   generatorRate*512,generatorRate*320,generatorRate*1307,generatorRate*2048,generatorRate*16384⟩

theorem shadow_invoice_algebra (a : Act) :
    tariff integerTariffs a = modelTokenBill Finset.univ frozenWeights (invoiceCounts a) := by
  cases a <;> simp only [tariff,taskTariff,integerTariffs,invoiceCounts]
  all_goals (try split_ifs) <;> simp [modelTokenBill,Fin.sum_univ_succ,frozenWeights] <;> ring

theorem integer_tariffs_nonnegative (a : Act) : 0 ≤ tariff integerTariffs a := by
  cases a <;> simp only [tariff,taskTariff,integerTariffs]
  all_goals (try split_ifs) <;> norm_num [generatorRate,e5Rate,bgeRate,embeddingRate]

theorem integer_tariffs_positive_floor (a : Act) :
    tariff integerTariffs a = 0 ∨ (1/2:ℝ) ≤ tariff integerTariffs a := by
  cases a <;> simp only [tariff,taskTariff,integerTariffs]
  all_goals (try split_ifs) <;> norm_num [generatorRate,e5Rate,bgeRate,embeddingRate]

theorem reference_queries_not_identity : ∀ i : Fin 3,referenceQuery i ≠ identityQuery := by
  intro i; fin_cases i <;> decide

theorem independent_integer_median : calibrationMedian integerTariffs = generatorRate*2331 := by
  have hq : ∀ i : Fin 3,integerTariffs.query (referenceQuery i) = generatorRate*512 := by
    intro i; simp only [integerTariffs,if_neg (reference_queries_not_identity i)]
  rw [independent_calibration_median_exact integerTariffs (generatorRate*512) hq]
  simp only [integerTariffs]; ring

theorem panel150_integer_cref : classCref panel150 integerTariffs = (150:ℝ)*(generatorRate*2331) := by
  rw [classCref,AgentUCTNativeBudget.panel150_cardinality,independent_integer_median]
  norm_num

theorem beta2_integer_penalty_scale :
    penaltyScale panel150 2 (classCref panel150 integerTariffs) = 2/(generatorRate*2331) := by
  rw [penaltyScale,panel150_integer_cref,AgentUCTNativeBudget.panel150_cardinality]
  norm_num [generatorRate]

theorem independent_cref_differs_saved_decimal :
    classCref panel150 integerTariffs ≠ (1470690.0198555747:ℝ) := by
  rw [panel150_integer_cref]; norm_num [generatorRate]

theorem integer_physical_bill_fields (qids : Finset (Fin 150)) (events : List (TreeEvaluation Act)) :
    physicalBill qids integerTariffs events =
      ∑ r ∈ ownPanelCache qids events,modelTokenBill Finset.univ frozenWeights (invoiceCounts (resourceAction r)) :=
  class_bill_from_actual_token_fields qids integerTariffs Finset.univ frozenWeights invoiceCounts shadow_invoice_algebra events

theorem integer_budget_exact : taskBudget panel150 integerTariffs =
    (150:ℝ)*(generatorRate*(41153/2)+e5Rate*37+bgeRate*38) := by
  simp +decide [taskBudget,baseBill,eightBill,integerTariffs,tailBill,
    AgentUCTNativeBudget.panel150_cardinality,finUniv8_explicit,identityQuery]
  ring

theorem integer_budget_differs_saved_target : taskBudget panel150 integerTariffs ≠ (32000000:ℝ) := by
  rw [integer_budget_exact]
  norm_num [generatorRate,e5Rate,bgeRate]

end AgentUCTPhysicalDiagnostic
