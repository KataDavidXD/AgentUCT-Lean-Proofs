import PanelCausalMeans




set_option autoImplicit false
set_option maxRecDepth 16384
set_option maxHeartbeats 4000000
set_option linter.constructorNameAsVariable false
noncomputable section
namespace AgentUCTNativeBudget
open AgentUCTPanelAllocation AgentUCTNativeRepair AgentUCTNativeRefinement AgentUCTPaper Finset

def aCold : List Act := leaf hyde (.hydeRetriever 1) 1 0
def aWarm : List Act := seedPath hyde
def aCross : List Act := leaf hyde (.hydeRetriever 2) 0 2
def bCold : List Act := leaf branchB (.normalRetriever 1) 1 0

theorem native_budget_paths_terminal : Terminal aCold ∧ Terminal aWarm ∧
    Terminal aCross ∧ Terminal bCold := by decide

def routeEvent (reward : List Act → ℝ) (q : Fin 8) (r : Act) (w : Fin 4) (m : Fin 3) : TreeEvaluation Act :=
  ⟨[.query q,r],leaf q r w m,reward (leaf q r w m),0,
   by exact ⟨(leaf q r w m).drop 2,by simp [leaf]⟩⟩

def aColdEvent (reward : List Act → ℝ) := routeEvent reward hyde (.hydeRetriever 1) 1 0
def aWarmEvent (reward : List Act → ℝ) := routeEvent reward hyde (.hydeRetriever 0) 0 0
def aCrossEvent (reward : List Act → ℝ) := routeEvent reward hyde (.hydeRetriever 2) 0 2
def bColdEvent (reward : List Act → ℝ) := routeEvent reward branchB (.normalRetriever 1) 1 0

def aNine (reward : List Act → ℝ) := initialization reward ++ [aColdEvent reward]
def aTen (reward : List Act → ℝ) := aNine reward ++ [aWarmEvent reward]
def aEleven (reward : List Act → ℝ) := aTen reward ++ [aCrossEvent reward]
def bNine (reward : List Act → ℝ) := initialization reward ++ [bColdEvent reward]
def bTen (reward : List Act → ℝ) := bNine reward ++ [aColdEvent reward]

def taskTariff (query : Fin 8 → ℝ) (hydeE5 bge qwen normalE5 w2 w4 ans2 ans6 rerank : ℝ) : Act → ℝ
  | .query q => query q
  | .normalRetriever r => if r = 0 then 0 else normalE5
  | .hydeRetriever r => if r = 0 then hydeE5 else if r = 1 then bge else qwen
  | .width w => if w = 0 then w2 else if w = 1 then w4 else 0
  | .answer m => if m = 0 then ans2 else if m = 2 then ans6 else 0
  | .reranker r => if r = 0 then 0 else rerank
  | _ => 0

def pathTariff (tariff : Act → ℝ) (resource : Unit × List Act) : ℝ := tariff (resourceAction resource)

def eightBill (query : Fin 8 → ℝ) (hydeE5 w2 ans2 : ℝ) : ℝ :=
  (∑ q : Fin 8, query q)+8*(w2+ans2)+hydeE5

theorem task_tariff_nonnegative (query : Fin 8 → ℝ) (hquery : ∀ q,0 ≤ query q)
    (hydeE5 bge qwen normalE5 w2 w4 ans2 ans6 rerank : ℝ)
    (h : 0 ≤ hydeE5 ∧ 0 ≤ bge ∧ 0 ≤ qwen ∧ 0 ≤ normalE5 ∧ 0 ≤ w2 ∧
      0 ≤ w4 ∧ 0 ≤ ans2 ∧ 0 ≤ ans6 ∧ 0 ≤ rerank) (a : Act) :
    0 ≤ taskTariff query hydeE5 bge qwen normalE5 w2 w4 ans2 ans6 rerank a := by
  rcases h with ⟨h1,h2,h3,h4,h5,h6,h7,h8,h9⟩
  cases a <;> simp only [taskTariff] <;> (try split_ifs) <;> simp_all

theorem seed_actual_weight (query : Fin 8 → ℝ) (hydeE5 bge qwen normalE5 w2 w4 ans2 ans6 rerank : ℝ)
    (q : Fin 8) :
    cacheWeight (pathTariff (taskTariff query hydeE5 bge qwen normalE5 w2 w4 ans2 ans6 rerank)) (demand (seedPath q)) =
      query q+w2+ans2+(if q = hyde then hydeE5 else 0) := by
  simp only [seedPath]
  rw [demand_leaf_explicit]
  fin_cases q <;> simp +decide [seedRetriever,hyde,cacheWeight,pathTariff,resourceAction,
    taskTariff,leaf,Finset.sum_insert] <;> ring

theorem eight_actual_bill (reward : List Act → ℝ) (query : Fin 8 → ℝ)
    (hydeE5 bge qwen normalE5 w2 w4 ans2 ans6 rerank : ℝ) :
    (ownState (pathTariff (taskTariff query hydeE5 bge qwen normalE5 w2 w4 ans2 ans6 rerank))
      (initialization reward)).totalPaid = eightBill query hydeE5 w2 ans2 := by
  rw [ownState_actual_bill,initialization_cache_exact]
  unfold cacheWeight initialCache
  rw [Finset.sum_biUnion (fun i _ j _ hij => seed_demands_disjoint i j hij)]
  change (∑ q : Fin 8, cacheWeight _ (demand (seedPath q))) = _
  simp_rw [seed_actual_weight]
  simp +decide [eightBill,finUniv8_explicit,hyde]
  ring

theorem a_cold_initial_actual (query : Fin 8 → ℝ) (hydeE5 bge qwen normalE5 w2 w4 ans2 ans6 rerank : ℝ) :
    coldWork (pathTariff (taskTariff query hydeE5 bge qwen normalE5 w2 w4 ans2 ans6 rerank)) initialCache (demand aCold) =
      bge+w4+ans2 := by
  unfold coldWork aCold
  rw [ownCache_initial_restrict,demand_leaf_explicit]
  simp only [seedPath]
  rw [demand_leaf_explicit]
  simp +decide [seedRetriever,hyde,leaf,Finset.sdiff_eq_filter,Finset.filter_insert,
    Finset.filter_singleton,cacheWeight,pathTariff,resourceAction,taskTariff,Finset.sum_insert]
  ring

theorem b_cold_initial_actual (query : Fin 8 → ℝ) (hydeE5 bge qwen normalE5 w2 w4 ans2 ans6 rerank : ℝ) :
    coldWork (pathTariff (taskTariff query hydeE5 bge qwen normalE5 w2 w4 ans2 ans6 rerank)) initialCache (demand bCold) =
      normalE5+w4+ans2 := by
  unfold coldWork bCold
  rw [ownCache_initial_restrict,demand_leaf_explicit]
  simp only [seedPath]
  rw [demand_leaf_explicit]
  simp +decide [seedRetriever,branchB,hyde,leaf,Finset.sdiff_eq_filter,Finset.filter_insert,
    Finset.filter_singleton,cacheWeight,pathTariff,resourceAction,taskTariff,Finset.sum_insert]
  ring

theorem genuine_seed_warm_after_a9 (reward : List Act → ℝ) : demand aWarm ⊆ ownCache (aNine reward) := by
  rw [aNine,ownCache_append,initialization_cache_exact]
  apply Finset.Subset.trans _ Finset.subset_union_left
  exact Finset.subset_biUnion_of_mem (fun q : Fin 8 => demand (seedPath q)) (Finset.mem_univ hyde)

theorem warm10_zero_new_resources (reward : List Act → ℝ) :
    demand aWarm \ ownCache (aNine reward) = ∅ :=
  Finset.sdiff_eq_empty_iff_subset.mpr (genuine_seed_warm_after_a9 reward)

theorem warm10_zero_model_increment (reward : List Act → ℝ) (tariff : Act → ℝ) :
    (ownState (pathTariff tariff) (aTen reward)).totalPaid =
      (ownState (pathTariff tariff) (aNine reward)).totalPaid := by
  rw [aTen,ownState_append_bill]
  change _+coldWork (pathTariff tariff) (ownCache (aNine reward)) (demand aWarm) = _
  rw [coldWork,warm10_zero_new_resources]
  simp [cacheWeight]

theorem warm10_cache_unchanged (reward : List Act → ℝ) : ownCache (aTen reward) = ownCache (aNine reward) := by
  rw [aTen,ownCache_append]
  exact Finset.union_eq_left.mpr (genuine_seed_warm_after_a9 reward)

theorem cross_after_a9_demand (reward : List Act → ℝ) :
    demand aCross \ ownCache (aNine reward) = demand aCross \ initialCache := by
  rw [aNine,ownCache_append,initialization_cache_exact]
  change demand aCross \ (initialCache ∪ demand aCold) = _
  have hdif : ∀ X Y Z : Finset (Unit × List Act), X \ (Y ∪ Z) = (X \ Y) \ Z := by
    intro X Y Z; ext resource
    simp only [Finset.mem_sdiff,Finset.mem_union]; tauto
  rw [hdif]
  unfold aCross
  rw [ownCache_initial_restrict,demand_leaf_explicit]
  simp only [seedPath]
  rw [demand_leaf_explicit]
  unfold aCold
  rw [demand_leaf_explicit]
  simp +decide [seedRetriever,hyde,leaf,Finset.sdiff_eq_filter,Finset.filter_insert,Finset.filter_singleton]

theorem a_after_b9_demand (reward : List Act → ℝ) :
    demand aCold \ ownCache (bNine reward) = demand aCold \ initialCache := by
  rw [bNine,ownCache_append,initialization_cache_exact]
  change demand aCold \ (initialCache ∪ demand bCold) = _
  have hdif : ∀ X Y Z : Finset (Unit × List Act), X \ (Y ∪ Z) = (X \ Y) \ Z := by
    intro X Y Z; ext resource
    simp only [Finset.mem_sdiff,Finset.mem_union]; tauto
  rw [hdif]
  unfold aCold
  rw [ownCache_initial_restrict,demand_leaf_explicit]
  simp only [seedPath]
  rw [demand_leaf_explicit]
  unfold bCold
  rw [demand_leaf_explicit]
  simp +decide [seedRetriever,hyde,branchB,leaf,Finset.sdiff_eq_filter,Finset.filter_insert,Finset.filter_singleton]

theorem cross_initial_actual (query : Fin 8 → ℝ) (hydeE5 bge qwen normalE5 w2 w4 ans2 ans6 rerank : ℝ) :
    coldWork (pathTariff (taskTariff query hydeE5 bge qwen normalE5 w2 w4 ans2 ans6 rerank)) initialCache (demand aCross) =
      qwen+w2+ans6 := by
  unfold coldWork aCross
  rw [ownCache_initial_restrict,demand_leaf_explicit]
  simp only [seedPath]
  rw [demand_leaf_explicit]
  simp +decide [seedRetriever,hyde,leaf,Finset.sdiff_eq_filter,Finset.filter_insert,
    Finset.filter_singleton,pathTariff,resourceAction,taskTariff,Finset.sum_insert]
  ring

theorem a_nine_actual_bill (reward : List Act → ℝ) (query : Fin 8 → ℝ)
    (hydeE5 bge qwen normalE5 w2 w4 ans2 ans6 rerank : ℝ) :
    (ownState (pathTariff (taskTariff query hydeE5 bge qwen normalE5 w2 w4 ans2 ans6 rerank))
      (aNine reward)).totalPaid = eightBill query hydeE5 w2 ans2+bge+w4+ans2 := by
  rw [aNine,ownState_append_bill,eight_actual_bill,initialization_cache_exact]
  change _+coldWork _ initialCache (demand aCold) = _
  rw [a_cold_initial_actual]
  ring

theorem a_ten_actual_bill (reward : List Act → ℝ) (query : Fin 8 → ℝ)
    (hydeE5 bge qwen normalE5 w2 w4 ans2 ans6 rerank : ℝ) :
    (ownState (pathTariff (taskTariff query hydeE5 bge qwen normalE5 w2 w4 ans2 ans6 rerank))
      (aTen reward)).totalPaid = eightBill query hydeE5 w2 ans2+bge+w4+ans2 := by
  rw [warm10_zero_model_increment,a_nine_actual_bill]

theorem a_eleven_actual_bill (reward : List Act → ℝ) (query : Fin 8 → ℝ)
    (hydeE5 bge qwen normalE5 w2 w4 ans2 ans6 rerank : ℝ) :
    (ownState (pathTariff (taskTariff query hydeE5 bge qwen normalE5 w2 w4 ans2 ans6 rerank))
      (aEleven reward)).totalPaid = eightBill query hydeE5 w2 ans2+bge+w4+ans2+qwen+w2+ans6 := by
  rw [aEleven,ownState_append_bill,a_ten_actual_bill]
  change _+coldWork _ (ownCache (aTen reward)) (demand aCross) = _
  rw [warm10_cache_unchanged,coldWork,cross_after_a9_demand]
  change _+coldWork _ initialCache (demand aCross) = _
  rw [cross_initial_actual]
  ring

theorem b_nine_actual_bill (reward : List Act → ℝ) (query : Fin 8 → ℝ)
    (hydeE5 bge qwen normalE5 w2 w4 ans2 ans6 rerank : ℝ) :
    (ownState (pathTariff (taskTariff query hydeE5 bge qwen normalE5 w2 w4 ans2 ans6 rerank))
      (bNine reward)).totalPaid = eightBill query hydeE5 w2 ans2+normalE5+w4+ans2 := by
  rw [bNine,ownState_append_bill,eight_actual_bill,initialization_cache_exact]
  change _+coldWork _ initialCache (demand bCold) = _
  rw [b_cold_initial_actual]
  ring

theorem b_ten_actual_bill (reward : List Act → ℝ) (query : Fin 8 → ℝ)
    (hydeE5 bge qwen normalE5 w2 w4 ans2 ans6 rerank : ℝ) :
    (ownState (pathTariff (taskTariff query hydeE5 bge qwen normalE5 w2 w4 ans2 ans6 rerank))
      (bTen reward)).totalPaid = eightBill query hydeE5 w2 ans2+normalE5+2*(w4+ans2)+bge := by
  rw [bTen,ownState_append_bill,b_nine_actual_bill]
  change _+coldWork _ (ownCache (bNine reward)) (demand aCold) = _
  rw [coldWork,a_after_b9_demand]
  change _+coldWork _ initialCache (demand aCold) = _
  rw [a_cold_initial_actual]
  ring

end AgentUCTNativeBudget
