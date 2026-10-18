import NativeReceipt



set_option autoImplicit false
set_option maxRecDepth 8192
set_option maxHeartbeats 4000000
noncomputable section
namespace AgentUCTNativeRefinement
open AgentUCTPaper Finset

def referencePath (q : Fin 8) : List Act :=
  if q = hyde then hiddenA 0 else leaf q (.normalRetriever 0) 1 2

def orderedResources (p : List Act) : List (Unit × List Act) :=
  (List.range p.length).map fun n => ((),p.take (n+1))

def completeQuote (q a e b k : ℝ) (before : List (TreeEvaluation Act)) (branch : Fin 8) : ℝ :=
  coldWork (price q a e b k) (ownCache before) (demand (referencePath branch))

def nextQuote (q a e b k : ℝ) (before : List (TreeEvaluation Act)) (branch : Fin 8) : ℝ :=
  nextUnpaidBill (ownCache before) (price q a e b k) (orderedResources (referencePath branch))

theorem referencePath_legal (q : Fin 8) : Terminal (referencePath q) := by
  by_cases hq : q = hyde
  · simpa [referencePath,hq] using hidden_hyde_terminal 0
  · simpa [referencePath,hq] using hidden_normal_terminal q hq

theorem initial_complete_quotes (reward : List Act → ℝ) (q a e b k : ℝ) (branch : Fin 8) :
    completeQuote q a e b k (initialization reward) branch =
      if branch = hyde then 2*a else 12*a := by
  unfold completeQuote
  rw [initialization_cache_exact]
  by_cases h : branch = hyde
  · subst branch
    simpa [referencePath] using initial_hidden_A_cold q a e b k 0
  · simpa [referencePath,h] using initial_normal_hidden_cold q a e b k branch h

theorem orderedResources_member_demand (p : List Act) (resource : Unit × List Act)
    (hr : resource ∈ orderedResources p) : resource ∈ demand p := by
  obtain ⟨n, hn, rfl⟩ := List.mem_map.mp hr
  have hn0 : n < p.length := List.mem_range.mp hn
  apply (panelDemand_mem {()} p (p.take (n+1)) ()).2
  exact ⟨by simp,Finset.mem_image.mpr ⟨n+1,Finset.mem_Icc.mpr ⟨by omega,by omega⟩,rfl⟩⟩

theorem nextBill_cache_congr (C D : Finset (Unit × List Act)) (p : Unit × List Act → ℝ)
    (rs : List (Unit × List Act)) (h : ∀ r ∈ rs, r ∈ C ↔ r ∈ D) :
    nextUnpaidBill C p rs = nextUnpaidBill D p rs := by
  induction rs with
  | nil => rfl
  | cons r rs ih =>
    simp only [nextUnpaidBill,h r (by simp)]
    rw [ih (fun t ht => h t (by simp [ht]))]

theorem initial_next_quotes (reward : List Act → ℝ) (q a e b k : ℝ) (ha : 0 < a)
    (branch : Fin 8) : nextQuote q a e b k (initialization reward) branch = a := by
  unfold nextQuote
  rw [initialization_cache_exact]
  have hc : nextUnpaidBill initialCache (price q a e b k) (orderedResources (referencePath branch)) =
      nextUnpaidBill (demand (seedPath branch)) (price q a e b k)
        (orderedResources (referencePath branch)) := by
    apply nextBill_cache_congr
    intro resource hr
    have hm := orderedResources_member_demand (referencePath branch) resource hr
    by_cases h : branch = hyde
    · subst branch
      exact initialCache_mem_on_leaf hyde (.hydeRetriever 0) 1 0 resource hm
    · exact initialCache_mem_on_leaf branch (.normalRetriever 0) 1 2 resource
        (by simpa [referencePath,h] using hm)
  rw [hc]
  fin_cases branch <;>
    simp +decide [referencePath,hiddenA,seedPath,seedRetriever,hyde,leaf,
      orderedResources,List.range_succ,nextUnpaidBill,
      price,actionPrice,not_le.mpr ha]

def observedTransition (before : List (TreeEvaluation Act)) (p : List Act) (action : Act) : ℕ :=
  (before.filter fun event => decide (childAfter p event.terminal = some action)).length

def historicalProbability (before : List (TreeEvaluation Act)) (p : List Act)
    (smoothing : ℝ) (action : Act) : ℝ :=
  ((observedTransition before p action : ℝ) + smoothing / (available p).length) /
    ((∑ a ∈ (available p).toFinset, (observedTransition before p a : ℝ)) + smoothing)

theorem historical_positive_support (before : List (TreeEvaluation Act))
    (p : List Act) (smoothing : ℝ) (hs : 0 < smoothing) (action : Act)
    (ha : action ∈ available p) :
    0 < historicalProbability before p smoothing action := by
  have hl : 0 < (available p).length := List.length_pos_iff.mpr (List.ne_nil_of_mem ha)
  have hln : (0 : ℝ) < (available p).length := Nat.cast_pos.mpr hl
  have hn : (0 : ℝ) ≤ observedTransition before p action := Nat.cast_nonneg _
  have hz : (0 : ℝ) ≤ ∑ a ∈ (available p).toFinset, (observedTransition before p a : ℝ) := by
    exact Finset.sum_nonneg fun _ _ => Nat.cast_nonneg _
  exact div_pos (lt_of_lt_of_le (div_pos hs hln) (le_add_of_nonneg_left hn))
    (by linarith)

def pathProbability (before : List (TreeEvaluation Act)) (smoothing : ℝ) :
    List Act → List Act → ℝ
  | _, [] => 1
  | p, action :: rest => historicalProbability before p smoothing action *
      pathProbability before smoothing (p ++ [action]) rest

theorem legal_tail_positive_probability (before : List (TreeEvaluation Act))
    (smoothing : ℝ) (hs : 0 < smoothing) (p tail : List Act)
    (hlegal : followLegal p tail = true) :
    0 < pathProbability before smoothing p tail := by
  induction tail generalizing p with
  | nil => simp [pathProbability]
  | cons action tail ih =>
    simp only [followLegal,Bool.and_eq_true,decide_eq_true_eq] at hlegal
    exact mul_pos (historical_positive_support before p smoothing hs action hlegal.1)
      (ih (p++[action]) hlegal.2)

theorem native_mc16_supported (before : List (TreeEvaluation Act))
    (smoothing : ℝ) (hs : 0 < smoothing) (branch : Fin 8) :
    0 < (pathProbability before smoothing [.query branch]
      ((referencePath branch).drop 1))^16 := by
  have hlegal := (referencePath_legal branch).1
  have hp : referencePath branch = .query branch :: (referencePath branch).drop 1 := by
    by_cases hb : branch = hyde <;> simp [referencePath,hb,hiddenA,leaf]
  change followLegal [] (referencePath branch) = true at hlegal
  rw [hp] at hlegal
  simp only [followLegal,Bool.and_eq_true] at hlegal
  have h := legal_tail_positive_probability before smoothing hs [.query branch]
    ((referencePath branch).drop 1) hlegal.2
  positivity

theorem sixteen_repeated_samples_quote (bill : List Act → ℝ) (branch : Fin 8) :
    (∑ _i : Fin 16, bill (referencePath branch))/16 = bill (referencePath branch) := by
  simp



theorem common_state_error_margin (u delta gamma a estimateA estimateB eps : ℝ)
    (hg : 0 ≤ gamma) (heA : |estimateA-2*a| ≤ eps)
    (heB : |estimateB-12*a| ≤ eps) (hmargin : delta < gamma*(10*a-2*eps)) :
    u+delta-gamma*estimateB < u-gamma*estimateA := by
  obtain ⟨hAl,hAr⟩ := abs_le.mp heA
  obtain ⟨hBl,hBr⟩ := abs_le.mp heB
  have hA := mul_le_mul_of_nonneg_left hAr hg
  have hB := mul_le_mul_of_nonneg_left (show 12*a-estimateB ≤ eps by linarith) hg
  nlinarith

end AgentUCTNativeRefinement
