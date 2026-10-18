import NativeBudgetRollouts




set_option autoImplicit false
set_option maxRecDepth 16384
set_option maxHeartbeats 4000000
set_option linter.constructorNameAsVariable false
noncomputable section
namespace AgentUCTNativeBudget
open AgentUCTPanelAllocation AgentUCTNativeRepair AgentUCTNativeRefinement AgentUCTPaper

def normalSample (q : Fin 8) : List Act := fullLeaf q (.normalRetriever 0) 0 1 1 2 0

theorem unit_panel_cache_is_own (events : List (TreeEvaluation Act)) : ownPanelCache {()} events = ownCache events := rfl

theorem source_a_initial_suffix : sourceSuffix initialCache (fun _ _ => false) () aCold =
    (List.range 8).map (fun i => ((),aCold.take (i+2))) := by decide

theorem source_a_after_own_publication_suffix :
    sourceSuffix (initialCache ∪ demand aCold) (fun _ _ => false) () aCold = [] := by decide

theorem source_a_after_other_publication_suffix :
    sourceSuffix (initialCache ∪ demand bCold) (fun _ _ => false) () aCold =
      (List.range 8).map (fun i => ((),aCold.take (i+2))) := by decide

theorem source_normal_initial_suffix (q : Fin 8) (hq : q ≠ hyde) :
    sourceSuffix initialCache (fun _ _ => false) () (normalSample q) =
      (List.range 6).map (fun i => ((),(normalSample q).take (i+4))) := by
  fin_cases q <;> simp_all +decide [hyde]

theorem source_normal_after_a_publication_suffix (q : Fin 8) (hq : q ≠ hyde) :
    sourceSuffix (initialCache ∪ demand aCold) (fun _ _ => false) () (normalSample q) =
      (List.range 6).map (fun i => ((),(normalSample q).take (i+4))) := by
  fin_cases q <;> simp_all +decide [hyde]

theorem source_normal_after_b_publication_suffix (q : Fin 8) (hq : q ≠ hyde) :
    sourceSuffix (initialCache ∪ demand bCold) (fun _ _ => false) () (normalSample q) =
      (List.range 6).map (fun i => ((),(normalSample q).take (i+4))) := by
  fin_cases q <;> simp_all +decide [hyde]

theorem source_a_initial_complete (t : TariffInput) :
    sourceQidQuote .complete initialCache (fun _ _ => false) (pathTariff (tariff t)) () aCold = t.bge+tailBill t := by
  rw [sourceQidQuote,source_a_initial_suffix]
  simp +decide [List.range_succ,List.map_cons,List.sum_cons,pathTariff,tariff,taskTariff,
    resourceAction,aCold,leaf,hyde,tailBill] <;> ring

theorem source_a_initial_next (t : TariffInput) (hb : 0 < t.bge) :
    sourceQidQuote .next initialCache (fun _ _ => false) (pathTariff (tariff t)) () aCold = t.bge := by
  rw [sourceQidQuote,source_a_initial_suffix]
  simp +decide [List.range_succ,List.map_cons,nextUnpaidBill,pathTariff,tariff,taskTariff,
    resourceAction,aCold,leaf,hyde,not_le.mpr hb]

theorem source_a_published_complete (t : TariffInput) :
    sourceQidQuote .complete (initialCache ∪ demand aCold) (fun _ _ => false) (pathTariff (tariff t)) () aCold = 0 := by
  rw [sourceQidQuote,source_a_after_own_publication_suffix]
  rfl

theorem source_a_published_next (t : TariffInput) :
    sourceQidQuote .next (initialCache ∪ demand aCold) (fun _ _ => false) (pathTariff (tariff t)) () aCold = 0 := by
  rw [sourceQidQuote,source_a_after_own_publication_suffix]
  rfl

theorem source_a_other_publication_complete (t : TariffInput) :
    sourceQidQuote .complete (initialCache ∪ demand bCold) (fun _ _ => false) (pathTariff (tariff t)) () aCold = t.bge+tailBill t := by
  rw [sourceQidQuote,source_a_after_other_publication_suffix]
  rw [← source_a_initial_suffix]
  exact source_a_initial_complete t

theorem source_a_other_publication_next (t : TariffInput) (hb : 0 < t.bge) :
    sourceQidQuote .next (initialCache ∪ demand bCold) (fun _ _ => false) (pathTariff (tariff t)) () aCold = t.bge := by
  rw [sourceQidQuote,source_a_after_other_publication_suffix]
  rw [← source_a_initial_suffix]
  exact source_a_initial_next t hb

def normalForecastBill (t : TariffInput) : ℝ := t.w4+t.rerank+t.ans6

theorem source_normal_initial_complete (q : Fin 8) (hq : q ≠ hyde) (t : TariffInput) :
    sourceQidQuote .complete initialCache (fun _ _ => false) (pathTariff (tariff t)) () (normalSample q) =
      normalForecastBill t := by
  rw [sourceQidQuote,source_normal_initial_suffix q hq]
  simp +decide [List.range_succ,List.map_cons,List.sum_cons,pathTariff,tariff,taskTariff,
    resourceAction,normalSample,fullLeaf,normalForecastBill] <;> ring

theorem source_normal_initial_next (q : Fin 8) (hq : q ≠ hyde) (t : TariffInput) (hw : 0 < t.w4) :
    sourceQidQuote .next initialCache (fun _ _ => false) (pathTariff (tariff t)) () (normalSample q) = t.w4 := by
  rw [sourceQidQuote,source_normal_initial_suffix q hq]
  simp +decide [List.range_succ,List.map_cons,nextUnpaidBill,pathTariff,tariff,taskTariff,
    resourceAction,normalSample,fullLeaf,not_le.mpr hw]

theorem source_normal_a_publication_complete (q : Fin 8) (hq : q ≠ hyde) (t : TariffInput) :
    sourceQidQuote .complete (initialCache ∪ demand aCold) (fun _ _ => false) (pathTariff (tariff t)) () (normalSample q) =
      normalForecastBill t := by
  rw [sourceQidQuote,source_normal_after_a_publication_suffix q hq,← source_normal_initial_suffix q hq]
  exact source_normal_initial_complete q hq t

theorem source_normal_b_publication_complete (q : Fin 8) (hq : q ≠ hyde) (t : TariffInput) :
    sourceQidQuote .complete (initialCache ∪ demand bCold) (fun _ _ => false) (pathTariff (tariff t)) () (normalSample q) =
      normalForecastBill t := by
  rw [sourceQidQuote,source_normal_after_b_publication_suffix q hq,← source_normal_initial_suffix q hq]
  exact source_normal_initial_complete q hq t

theorem source_normal_b_publication_next (q : Fin 8) (hq : q ≠ hyde) (t : TariffInput) (hw : 0 < t.w4) :
    sourceQidQuote .next (initialCache ∪ demand bCold) (fun _ _ => false) (pathTariff (tariff t)) () (normalSample q) = t.w4 := by
  rw [sourceQidQuote,source_normal_after_b_publication_suffix q hq,← source_normal_initial_suffix q hq]
  exact source_normal_initial_next q hq t hw

variable {Qid : Type*} [DecidableEq Qid]

theorem stationary_panel_constant_sample (qids : Finset Qid) (mode : ForecastMode) (t : TariffInput)
    (before : List (TreeEvaluation Act)) (path : List Act) :
    sourcePanelMC16 qids mode (ownPanelCache qids before) (fun _ _ => false)
      (fun r => tariff t (resourceAction r)) (fun _ => path) =
    (qids.card : ℝ)*sourceQidQuote mode (ownCache before) (fun _ _ => false) (pathTariff (tariff t)) () path := by
  rw [own_panel_cache_product]
  change sourcePanelMC16 qids mode (qids ×ˢ pathHistoryCache before) (fun _ _ => false)
    (fun r => tariff t (r.2.getLastD .stop)) (fun _ => path) = _
  rw [homogeneous_source_panel_mc16 qids (pathHistoryCache before) mode (fun _ => false)
    (fun p => tariff t (p.getLastD .stop)) (fun _ => path)]
  have hc : ({()} : Finset Unit) ×ˢ pathHistoryCache before = ownCache before :=
    (own_panel_cache_product {()} before).symm.trans (unit_panel_cache_is_own before)
  rw [hc]
  change (qids.card : ℝ)*sourceQidMC16 mode (ownCache before) (fun _ _ => false)
    (pathTariff (tariff t)) () (fun _ => path) = _
  simp [sourceQidMC16]

def tariffRootForecast (qids : Finset Qid) (mode : ForecastMode) (t : TariffInput)
    (before : List (TreeEvaluation Act)) (q : Fin 8) : ℝ :=
  sourcePanelMC16 qids mode (ownPanelCache qids before) (fun _ _ => false)
    (fun r => tariff t (resourceAction r)) (budgetTape.completion before [] (.query q))

theorem tariff_root_hyde_constant (qids : Finset Qid) (mode : ForecastMode) (t : TariffInput)
    (before : List (TreeEvaluation Act)) :
    tariffRootForecast qids mode t before hyde = (qids.card : ℝ)*
      sourceQidQuote mode (ownCache before) (fun _ _ => false) (pathTariff (tariff t)) () aCold := by
  have hs : budgetTape.completion before [] (.query hyde) = fun _ => aCold := by
    funext i; exact mc_root_hyde_completion before i
  rw [tariffRootForecast,hs,stationary_panel_constant_sample]

theorem tariff_root_normal_constant (qids : Finset Qid) (mode : ForecastMode) (t : TariffInput)
    (before : List (TreeEvaluation Act)) (q : Fin 8) (hq : q ≠ hyde) :
    tariffRootForecast qids mode t before q = (qids.card : ℝ)*
      sourceQidQuote mode (ownCache before) (fun _ _ => false) (pathTariff (tariff t)) () (normalSample q) := by
  have hs : budgetTape.completion before [] (.query q) = fun _ => normalSample q := by
    funext i; exact mc_root_normal_completion before q hq i
  rw [tariffRootForecast,hs,stationary_panel_constant_sample]

theorem tariff_initial_complete_root (qids : Finset Qid) (t : TariffInput) (reward : List Act → ℝ) (q : Fin 8) :
    tariffRootForecast qids .complete t (initialization reward) q =
      (qids.card : ℝ)*(if q = hyde then t.bge+tailBill t else normalForecastBill t) := by
  by_cases hq : q = hyde
  · subst q
    rw [tariff_root_hyde_constant,initialization_cache_exact,source_a_initial_complete]
    simp
  · rw [tariff_root_normal_constant qids .complete t _ q hq,initialization_cache_exact,source_normal_initial_complete q hq]
    simp [hq]

theorem tariff_initial_next_root (qids : Finset Qid) (t : TariffInput) (reward : List Act → ℝ)
    (hb : 0 < t.bge) (hw : 0 < t.w4) (q : Fin 8) :
    tariffRootForecast qids .next t (initialization reward) q =
      (qids.card : ℝ)*(if q = hyde then t.bge else t.w4) := by
  by_cases hq : q = hyde
  · subst q
    rw [tariff_root_hyde_constant,initialization_cache_exact,source_a_initial_next t hb]
    simp
  · rw [tariff_root_normal_constant qids .next t _ q hq,initialization_cache_exact,source_normal_initial_next q hq t hw]
    simp [hq]

theorem tariff_a9_complete_root (qids : Finset Qid) (t : TariffInput) (reward : List Act → ℝ) (q : Fin 8) :
    tariffRootForecast qids .complete t (aNine reward) q =
      (qids.card : ℝ)*(if q = hyde then 0 else normalForecastBill t) := by
  by_cases hq : q = hyde
  · subst q
    rw [tariff_root_hyde_constant,aNine,ownCache_append,initialization_cache_exact]
    change _*sourceQidQuote .complete (initialCache ∪ demand aCold) _ _ _ aCold = _
    rw [source_a_published_complete]
    simp
  · rw [tariff_root_normal_constant qids .complete t _ q hq,aNine,ownCache_append,initialization_cache_exact]
    change _*sourceQidQuote .complete (initialCache ∪ demand aCold) _ _ _ (normalSample q) = _
    rw [source_normal_a_publication_complete q hq]
    simp [hq]

theorem tariff_a10_complete_root (qids : Finset Qid) (t : TariffInput) (reward : List Act → ℝ) (q : Fin 8) :
    tariffRootForecast qids .complete t (aTen reward) q =
      (qids.card : ℝ)*(if q = hyde then 0 else normalForecastBill t) := by
  by_cases hq : q = hyde
  · subst q
    rw [tariff_root_hyde_constant,warm10_cache_unchanged]
    rw [← tariff_root_hyde_constant]
    exact tariff_a9_complete_root qids t reward hyde
  · rw [tariff_root_normal_constant qids .complete t _ q hq,warm10_cache_unchanged]
    rw [← tariff_root_normal_constant qids .complete t _ q hq]
    exact tariff_a9_complete_root qids t reward q

theorem tariff_b9_next_root (qids : Finset Qid) (t : TariffInput) (reward : List Act → ℝ)
    (hb : 0 < t.bge) (hw : 0 < t.w4) (q : Fin 8) :
    tariffRootForecast qids .next t (bNine reward) q =
      (qids.card : ℝ)*(if q = hyde then t.bge else t.w4) := by
  by_cases hq : q = hyde
  · subst q
    rw [tariff_root_hyde_constant,bNine,ownCache_append,initialization_cache_exact]
    change _*sourceQidQuote .next (initialCache ∪ demand bCold) _ _ _ aCold = _
    rw [source_a_other_publication_next t hb]
    simp
  · rw [tariff_root_normal_constant qids .next t _ q hq,bNine,ownCache_append,initialization_cache_exact]
    change _*sourceQidQuote .next (initialCache ∪ demand bCold) _ _ _ (normalSample q) = _
    rw [source_normal_b_publication_next q hq t hw]
    simp [hq]

end AgentUCTNativeBudget
