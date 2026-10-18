import NativeResolver




set_option autoImplicit false
set_option maxRecDepth 8192
set_option maxHeartbeats 3000000
noncomputable section
namespace AgentUCTNativeRefinement
open AgentUCTPaper Finset

def exactReceiptPool (before : List (TreeEvaluation Act)) (resource : Unit × List Act) :
    Finset (Unit × List Act) := (ownCache before).filter fun r => r = resource

def prefixReceiptPool (before : List (TreeEvaluation Act)) (resource : Unit × List Act) :
    Finset (Unit × List Act) := (ownCache before).filter fun r => r.2 = resource.2

def actionReceiptPool (before : List (TreeEvaluation Act)) (action : Act) :
    Finset (Unit × List Act) := (ownCache before).filter fun r => r.2.getLast? = some action

def onlineQuote (q a e b k : ℝ) (caps : Act → ℝ)
    (before : List (TreeEvaluation Act)) (resource : Unit × List Act) : ℝ :=
  match resource.2.getLast? with
  | none => 0
  | some action =>
      let prior := min (caps action) (actionPrice q a e b k action)
      let receipts := if (exactReceiptPool before resource).Nonempty then exactReceiptPool before resource
        else if (prefixReceiptPool before resource).Nonempty then prefixReceiptPool before resource
        else actionReceiptPool before action
      onlineMean prior receipts (fun r => min (price q a e b k r) (caps action))

theorem mean_constant_on {I : Type*} (value : ℝ) (samples : Finset I) (values : I → ℝ)
    (h : ∀ i ∈ samples, values i = value) : onlineMean value samples values = value := by
  have he : (∑ i ∈ samples,values i) = ∑ _i ∈ samples,value := Finset.sum_congr rfl h
  unfold onlineMean
  rw [he]
  change onlineMean value samples (fun _ => value) = value
  exact stationary_hierarchy_mean value samples

theorem online_quote_exact_stationary (q a e b k : ℝ) (caps : Act → ℝ)
    (before : List (TreeEvaluation Act)) (resource : Unit × List Act)
    (hcap : ∀ action, actionPrice q a e b k action ≤ caps action) :
    onlineQuote q a e b k caps before resource = price q a e b k resource := by
  unfold onlineQuote price
  cases hl : resource.2.getLast? with
  | none => rfl
  | some action =>
    dsimp only
    rw [min_eq_right (hcap action)]
    apply mean_constant_on
    intro r hr
    split_ifs at hr with he hp
    · have heq := (Finset.mem_filter.mp hr).2
      subst r
      simp [hl,min_eq_left (hcap action)]
    · have heq := (Finset.mem_filter.mp hr).2
      simp [heq,hl,min_eq_left (hcap action)]
    · have hlast := (Finset.mem_filter.mp hr).2
      simp [hlast,min_eq_left (hcap action)]



theorem native_initial_query_receipt_present (reward : List Act → ℝ) (q : Fin 8) :
    ((),[.query q]) ∈ ownCache (initialization reward) := by
  rw [initialization_cache_exact]
  apply Finset.mem_biUnion.mpr
  refine ⟨q,Finset.mem_univ _,?_⟩
  simp only [seedPath]
  rw [demand_leaf_explicit]
  simp

theorem native_live_common_state_price_error_zero (q a e b k : ℝ) (caps : Act → ℝ)
    (reward : List Act → ℝ) (resource : Unit × List Act)
    (hcap : ∀ action, actionPrice q a e b k action ≤ caps action) :
    |onlineQuote q a e b k caps (initialization reward) resource-price q a e b k resource| = 0 := by
  rw [online_quote_exact_stationary q a e b k caps _ _ hcap]
  simp

theorem initial_positive_missing_resource (q a e b k : ℝ) (ha : 0 < a) :
    ∃ resource ∈ demand (hiddenA 0), resource ∉ initialCache ∧ 0 < price q a e b k resource := by
  let resource : Unit × List Act :=
    ((),[.query hyde,.hydeRetriever 0,.selection 0,.width 1])
  have hm : resource ∈ demand (hiddenA 0) := by
    simp only [hiddenA]
    rw [demand_leaf_explicit]
    simp [resource]
  have hs : resource ∉ demand (seedPath hyde) := by
    simp only [seedPath]
    rw [demand_leaf_explicit]
    simp +decide [resource,leaf,seedRetriever]
  refine ⟨resource,hm,?_,?_⟩
  · exact fun hc => hs ((initialCache_mem_on_leaf hyde (.hydeRetriever 0) 1 0 resource hm).1 hc)
  · simpa [price,resource,actionPrice] using ha

end AgentUCTNativeRefinement
