import NativeInitialization



set_option autoImplicit false
set_option maxRecDepth 8192
set_option maxHeartbeats 4000000
noncomputable section
namespace AgentUCTNativeRefinement
open AgentUCTPaper Finset

def hiddenA (r : Fin 3) : List Act := leaf hyde (.hydeRetriever r) 1 0
def hiddenB : List Act := leaf branchB (.normalRetriever 0) 1 2

def extraEvent (reward : List Act → ℝ) (q : Fin 8) (r : Act) : TreeEvaluation Act :=
  let terminal := leaf q r 1 (if q = hyde then 0 else 2)
  ⟨[.query q,r],terminal,reward terminal,0,
    by exact ⟨terminal.drop 2, by simp [terminal,leaf]⟩⟩

theorem ownCache_append (before : List (TreeEvaluation Act)) (event : TreeEvaluation Act) :
    ownCache (before ++ [event]) = ownCache before ∪ demand event.terminal := by
  simp [ownCache,List.foldl_append]

theorem ownCache_initial_restrict (q : Fin 8) (r : Act) (w : Fin 4) (m : Fin 3) :
    demand (leaf q r w m) \ initialCache =
      demand (leaf q r w m) \ demand (seedPath q) := by
  ext resource
  simp only [Finset.mem_sdiff]
  by_cases hs : resource ∈ demand (leaf q r w m)
  · have hquery := demand_leaf_head q r w m resource hs
    have hi : resource ∈ initialCache ↔ resource ∈ demand (seedPath q) := by
      constructor
      · intro hc
        obtain ⟨t,_,ht⟩ := Finset.mem_biUnion.mp hc
        have hj := demand_leaf_head t (seedRetriever t) 0 0 resource ht
        have he := hquery.symm.trans hj
        simp only [Option.some.injEq,Act.query.injEq] at he
        simpa [he] using ht
      · intro ht
        exact Finset.mem_biUnion.mpr ⟨q,Finset.mem_univ _,ht⟩
    simp [hs,hi]
  · simp [hs]

theorem initialCache_mem_on_leaf (q : Fin 8) (r : Act) (w : Fin 4) (m : Fin 3)
    (resource : Unit × List Act) (hr : resource ∈ demand (leaf q r w m)) :
    resource ∈ initialCache ↔ resource ∈ demand (seedPath q) := by
  have hquery := demand_leaf_head q r w m resource hr
  constructor
  · intro hc
    obtain ⟨t,_,ht⟩ := Finset.mem_biUnion.mp hc
    have hj := demand_leaf_head t (seedRetriever t) 0 0 resource ht
    have he := hquery.symm.trans hj
    simp only [Option.some.injEq,Act.query.injEq] at he
    simpa [he] using ht
  · intro ht
    exact Finset.mem_biUnion.mpr ⟨q,Finset.mem_univ _,ht⟩

theorem initial_hidden_A_cold (q a e b k : ℝ) (r : Fin 3) :
    coldWork (price q a e b k) initialCache (demand (hiddenA r)) =
      2*a + (if r = 0 then 0 else if r = 1 then b else k) := by
  unfold coldWork hiddenA
  rw [ownCache_initial_restrict]
  rw [demand_leaf_explicit]
  simp only [seedPath]
  rw [demand_leaf_explicit]
  fin_cases r <;>
    simp +decide [seedRetriever,hyde,leaf,Finset.sdiff_eq_filter,Finset.filter_insert,
      Finset.filter_singleton,price,actionPrice,identityQuery,Finset.sum_insert] <;> ring

theorem initial_hidden_B_cold (q a e b k : ℝ) :
    coldWork (price q a e b k) initialCache (demand hiddenB) = 12*a := by
  unfold coldWork hiddenB
  rw [ownCache_initial_restrict,demand_leaf_explicit]
  simp only [seedPath]
  rw [demand_leaf_explicit]
  simp +decide [seedRetriever,branchB,leaf,Finset.sdiff_eq_filter,
    Finset.filter_insert,Finset.filter_singleton,price,actionPrice,identityQuery,
    Finset.sum_insert]
  ring

theorem initial_normal_hidden_cold (q a e b k : ℝ) (t : Fin 8) (ht : t ≠ hyde) :
    coldWork (price q a e b k) initialCache (demand (leaf t (.normalRetriever 0) 1 2)) =
      12*a := by
  unfold coldWork
  rw [ownCache_initial_restrict,demand_leaf_explicit]
  simp only [seedPath]
  rw [demand_leaf_explicit]
  simp +decide [seedRetriever,ht,leaf,Finset.sdiff_eq_filter,Finset.filter_insert,
    Finset.filter_singleton,price,actionPrice,Finset.sum_insert]
  ring

theorem hidden_A_pairwise_new (q a e b k : ℝ) (r t : Fin 3) (hrt : r ≠ t) :
    coldWork (price q a e b k) (initialCache ∪ demand (hiddenA r)) (demand (hiddenA t)) =
      coldWork (price q a e b k) initialCache (demand (hiddenA t)) := by
  unfold coldWork hiddenA
  have hd : demand (leaf hyde (.hydeRetriever t) 1 0) \
      (initialCache ∪ demand (leaf hyde (.hydeRetriever r) 1 0)) =
        demand (leaf hyde (.hydeRetriever t) 1 0) \ initialCache := by
    have hdif : ∀ X Y Z : Finset (Unit × List Act), X \ (Y ∪ Z) = (X \ Y) \ Z := by
      intro X Y Z
      ext resource
      simp only [Finset.mem_sdiff,Finset.mem_union]
      tauto
    rw [hdif]
    rw [ownCache_initial_restrict]
    rw [demand_leaf_explicit]
    simp only [seedPath]
    rw [demand_leaf_explicit]
    rw [demand_leaf_explicit]
    fin_cases r <;> fin_cases t <;> simp_all +decide [leaf]
  rw [hd]

theorem native_resource_overlap :
    demand (seedPath hyde) ∩ demand (hiddenA 0) =
      {((),[.query hyde]),((),[.query hyde,.hydeRetriever 0]),
       ((),[.query hyde,.hydeRetriever 0,.selection 0])} := by
  simp only [seedPath,hiddenA]
  rw [demand_leaf_explicit,demand_leaf_explicit]
  simp +decide [leaf]

theorem native_overlap_bill (q a e b k : ℝ) :
    cacheWeight (price q a e b k) (demand (seedPath hyde) ∩ demand (hiddenA 0)) = q+e := by
  rw [native_resource_overlap]
  simp +decide [cacheWeight,price,actionPrice,hyde,identityQuery,Finset.sum_insert]

theorem extra_hyde_terminal (reward : List Act → ℝ) (r : Fin 3) :
    (extraEvent reward hyde (.hydeRetriever r)).terminal = hiddenA r := by
  simp [extraEvent,hiddenA]

theorem ownState_append_bill (p : Unit × List Act → ℝ)
    (before : List (TreeEvaluation Act)) (event : TreeEvaluation Act) :
    (ownState p (before ++ [event])).totalPaid =
      (ownState p before).totalPaid + coldWork p (ownCache before) (demand event.terminal) := by
  simp only [ownState,replayMetered,List.foldl_append,List.foldl_cons,List.foldl_nil]
  change _ + _ = _
  simp only [meterStep,MeteredTreeState.totalPaid]
  rw [← ownState_cache p before]
  simp only [ownState,replayMetered,demand,id_eq]
  ring

end AgentUCTNativeRefinement
