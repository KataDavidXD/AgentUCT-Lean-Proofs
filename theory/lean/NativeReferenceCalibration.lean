import NativeNonzeroFeasibility






set_option autoImplicit false
set_option maxRecDepth 16384
set_option maxHeartbeats 4000000
set_option linter.constructorNameAsVariable false
noncomputable section
namespace AgentUCTNativeBudget
open AgentUCTPanelAllocation AgentUCTNativeRepair AgentUCTNativeRefinement AgentUCTPaper

def referenceQuery (i : Fin 3) : Fin 8 := ![0,4,7] i
def referencePath (i : Fin 3) : List Act := seedPath (referenceQuery i)

theorem reference_paths_legal_distinct :
    (∀ i : Fin 3,Terminal (referencePath i)) ∧ Function.Injective referencePath := by
  constructor
  · intro i; fin_cases i <;> decide
  · intro i j h
    fin_cases i <;> fin_cases j <;> simp_all +decide

def referenceColdBill (t : TariffInput) (i : Fin 3) : ℝ :=
  coldWork (pathTariff (tariff t)) ∅ (demand (referencePath i))

def medianThree (x y z : ℝ) := max (min x y) (min (max x y) z)

def calibrationMedian (t : TariffInput) : ℝ :=
  medianThree (referenceColdBill t 0) (referenceColdBill t 1) (referenceColdBill t 2)

def classCref {RefQid : Type*} (referenceIds : Finset RefQid) (t : TariffInput) : ℝ :=
  (referenceIds.card : ℝ)*calibrationMedian t

theorem reference_cold_bill_exact (t : TariffInput) (i : Fin 3) :
    referenceColdBill t i = t.query (referenceQuery i)+t.w2+t.ans2 := by
  have hq : referenceQuery i ≠ hyde := by fin_cases i <;> decide
  unfold referenceColdBill referencePath
  simp only [coldWork,Finset.sdiff_empty]
  have hh := seed_actual_weight t.query t.hydeE5 t.bge t.qwen t.normalE5 t.w2 t.w4 t.ans2 t.ans6 t.rerank (referenceQuery i)
  simpa only [tariff,if_neg hq,add_zero] using hh

theorem independent_calibration_median_exact (t : TariffInput) (queryBill : ℝ)
    (hq : ∀ i : Fin 3,t.query (referenceQuery i) = queryBill) :
    calibrationMedian t = queryBill+t.w2+t.ans2 := by
  simp [calibrationMedian,reference_cold_bill_exact,hq,medianThree]

theorem feasible_class_independent_cref {RefQid : Type*} (referenceIds : Finset RefQid) (c : ℝ) :
    classCref referenceIds (feasibleTariffs c) = (referenceIds.card : ℝ)*3 := by
  have hq : ∀ i : Fin 3,(feasibleTariffs c).query (referenceQuery i) = 1 := by
    intro i
    change (if referenceQuery i = identityQuery then (0:ℝ) else 1) = 1
    fin_cases i <;> simp +decide [referenceQuery,identityQuery]
  have hh := independent_calibration_median_exact (feasibleTariffs c) 1 hq
  have hm : calibrationMedian (feasibleTariffs c) = 3 := by norm_num [feasibleTariffs] at hh; exact hh
  simp only [classCref,hm]

theorem class_cref_positive {RefQid : Type*} (referenceIds : Finset RefQid) (t : TariffInput)
    (hn : referenceIds.Nonempty) (hm : 0 < calibrationMedian t) : 0 < classCref referenceIds t := by
  have hc : (0:ℝ) < referenceIds.card := by exact_mod_cast Finset.card_pos.mpr hn
  exact mul_pos hc hm

theorem class_cref_penalty_cardinality {Qid RefQid : Type*} [DecidableEq Qid]
    (qids : Finset Qid) (referenceIds : Finset RefQid) (t : TariffInput) (beta : ℝ)
    (hn : qids.Nonempty) (hcard : referenceIds.card = qids.card) (hm : calibrationMedian t ≠ 0) :
    penaltyScale qids beta (classCref referenceIds t) = beta/calibrationMedian t := by
  have hc : (qids.card : ℝ) ≠ 0 := by exact_mod_cast Finset.card_ne_zero.mpr hn
  unfold penaltyScale classCref
  rw [hcard]
  field_simp

def PhysicalTokenRealization {Field : Type*} (t : TariffInput) (fields : Finset Field)
    (weights : Field → ℝ) (usage : Act → Field → ℕ) : Prop :=
  ∀ a,tariff t a = modelTokenBill fields weights (usage a)

theorem class_bill_from_actual_token_fields {Qid Field : Type*} [DecidableEq Qid]
    (qids : Finset Qid) (t : TariffInput) (fields : Finset Field) (weights : Field → ℝ)
    (usage : Act → Field → ℕ) (ht : PhysicalTokenRealization t fields weights usage)
    (events : List (TreeEvaluation Act)) :
    physicalBill qids t events =
      ∑ r ∈ ownPanelCache qids events,modelTokenBill fields weights (usage (resourceAction r)) := by
  simp only [physicalBill,panelActualBill,replay_panel_actual_bill,cacheWeight]
  exact Finset.sum_congr rfl (fun r _ => ht _)

theorem reference_cref_token_units {RefQid Field : Type*} (referenceIds : Finset RefQid)
    (t : TariffInput) (fields : Finset Field) (weights : Field → ℝ) (usage : Act → Field → ℕ)
    (ht : PhysicalTokenRealization t fields weights usage) :
    classCref referenceIds t = (referenceIds.card : ℝ)*
      medianThree
        (∑ r ∈ demand (referencePath 0),modelTokenBill fields weights (usage (resourceAction r)))
        (∑ r ∈ demand (referencePath 1),modelTokenBill fields weights (usage (resourceAction r)))
        (∑ r ∈ demand (referencePath 2),modelTokenBill fields weights (usage (resourceAction r))) := by
  have hb : ∀ i : Fin 3, referenceColdBill t i =
      ∑ r ∈ demand (referencePath i),modelTokenBill fields weights (usage (resourceAction r)) := by
    intro i
    simp only [referenceColdBill,coldWork,Finset.sdiff_empty,pathTariff]
    exact Finset.sum_congr rfl (fun r _ => ht _)
  simp only [classCref,calibrationMedian,hb]

end AgentUCTNativeBudget
