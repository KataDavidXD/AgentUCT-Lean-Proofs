import NativeStopBatch




set_option autoImplicit false
set_option maxRecDepth 8192
set_option maxHeartbeats 3000000
noncomputable section
namespace AgentUCTNativeRefinement
open AgentUCTPaper Finset

def normalNames : List String :=
  ["retriever.bm25","retriever.dense_e5","retriever.qwen3_embedding","retriever.rrf",
   "retriever.bge_m3_dense","retriever.bge_m3_sparse","retriever.bge_m3_hybrid",
   "retriever.bge_m3_hybrid:dense=0.25","retriever.bge_m3_hybrid:dense=0.75",
   "retriever.rrf:bm25+e5:k=10","retriever.rrf:bm25+e5:k=60","retriever.rrf:bm25+e5:k=100",
   "retriever.rrf:bm25+bge:k=10","retriever.rrf:bm25+bge:k=60","retriever.rrf:bm25+bge:k=100",
   "retriever.rrf:bm25+qwen:k=10","retriever.rrf:bm25+qwen:k=60","retriever.rrf:bm25+qwen:k=100",
   "retriever.rrf:e5+bge:k=10","retriever.rrf:e5+bge:k=60","retriever.rrf:e5+bge:k=100",
   "retriever.rrf:bm25+e5+bge+qwen:k=10","retriever.rrf:bm25+e5+bge+qwen:k=60",
   "retriever.rrf:bm25+e5+bge+qwen:k=100",
   "retriever.weighted:bm25+e5:alpha=0.25","retriever.weighted:bm25+e5:alpha=0.5",
   "retriever.weighted:bm25+e5:alpha=0.75","retriever.weighted:bm25+qwen:alpha=0.25",
   "retriever.weighted:bm25+qwen:alpha=0.5","retriever.weighted:bm25+qwen:alpha=0.75"]

def codeName : Act → String
  | .query q => queryNames[q.val]!
  | .normalRetriever r => normalNames[r.val]!
  | .hydeRetriever r => ["retriever.hyde_e5","retriever.hyde_bge","retriever.hyde_qwen"][r.val]!
  | .selection s => ["selection.relevance","selection.mmr:lambda=0.3",
      "selection.mmr:lambda=0.6","selection.mmr:lambda=0.9"][s.val]!
  | .width w => ["retrieve.k=2","retrieve.k=4","retrieve.k=6","retrieve.k=10"][w.val]!
  | .stop => "control.stop"
  | .reranker r => ["reranker.identity","reranker.qwen3"][r.val]!
  | .topm m => ["top_m=2","top_m=4","top_m=6"][m.val]!
  | .context c => ["context.ranked","context.reverse","context.ends"][c.val]!
  | .answer m => ["answer.generate:m=2","answer.generate:m=4","answer.generate:m=6"][m.val]!




def nativeOrderKey : Act → ℕ
  | .query q => q.val
  | .normalRetriever r =>
      [5,6,7,8,0,4,1,2,3,15,17,16,9,11,10,18,20,19,21,23,22,12,14,13,24,25,26,27,28,29][r.val]!
  | .hydeRetriever r => [1,0,2][r.val]!
  | .selection s => [3,0,1,2][s.val]!
  | .width w => [1,2,3,0][w.val]!
  | .context c => [1,2,0][c.val]!
  | .reranker r => r.val
  | .topm m => m.val
  | .answer m => m.val
  | .stop => 0

def orderedAvailable (p : List Act) : List Act :=
  (available p).insertionSort (fun a b => nativeOrderKey a ≤ nativeOrderKey b)

theorem ordinary_retriever_names_complete_and_unique :
    normalNames.length = 30 ∧ normalNames.Nodup := by decide

theorem native_sorted_initialization_order : orderedAvailable [] = rootOrder := by decide

theorem native_hyde_tie_order : orderedAvailable [.query hyde] =
    [.hydeRetriever 1,.hydeRetriever 0,.hydeRetriever 2] := by decide

inductive Phase where | expansion | rollout deriving DecidableEq
inductive ForecastMode where | complete | next | unpriced deriving DecidableEq

structure SharedTape where
  action : List (TreeEvaluation Act) → Phase → List Act → List Act → Act
  completion : List (TreeEvaluation Act) → List Act → Act → Fin 16 → List Act



def SupportedTape (tape : SharedTape) : Prop :=
  (∀ before phase p candidates, candidates ≠ [] →
    tape.action before phase p candidates ∈ candidates) ∧
  (∀ before p action i, action ∈ available p →
    Terminal (tape.completion before p action i) ∧
    p++[action] <+: tape.completion before p action i)

def forecast (mode : ForecastMode) (tape : SharedTape)
    (prices : Unit × List Act → ℝ) (before : List (TreeEvaluation Act))
    (p : List Act) (action : Act) : ℝ :=
  match mode with
  | .unpriced => 0
  | .complete => (∑ i : Fin 16, coldWork prices (ownCache before)
      (demand (tape.completion before p action i)))/16
  | .next => (∑ i : Fin 16, nextUnpaidBill (ownCache before) prices
      (orderedResources (tape.completion before p action i)))/16

def expandedNodes (before : List (TreeEvaluation Act)) : Finset (List Act) :=
  insert [] (before.map TreeEvaluation.expanded).toFinset

def nodeScore (mode : ForecastMode) (tape : SharedTape)
    (prices : Unit × List Act → ℝ) (c gamma : ℝ) (before : List (TreeEvaluation Act))
    (p : List Act) (action : Act) : ℝ :=
  treeIndex (replayBackup before emptyStatistics (p++[action])).mean c
    (gamma*forecast mode tape prices before p action)
    (replayBackup before emptyStatistics p).visits
    (replayBackup before emptyStatistics (p++[action])).visits


def visitedChoice (mode : ForecastMode) (tape : SharedTape)
    (prices : Unit × List Act → ℝ) (c gamma : ℝ) (before : List (TreeEvaluation Act))
    (p : List Act) : Act :=
  let choices := orderedAvailable p
  match (choices.filter fun a => (replayBackup before emptyStatistics (p++[a])).visits = 0).head? with
  | some action => action
  | none => choices.tail.foldl (fun chosen a =>
      if nodeScore mode tape prices c gamma before p chosen <
          nodeScore mode tape prices c gamma before p a then a else chosen)
      (choices.headD .stop)



def selectExpansion (mode : ForecastMode) (tape : SharedTape)
    (prices : Unit × List Act → ℝ) (c gamma : ℝ) (before : List (TreeEvaluation Act)) :
    ℕ → List Act → List Act
  | 0, p => p
  | fuel+1, p =>
    if available p = [] then p else
    let unexpanded := (orderedAvailable p).filter fun a => p++[a] ∉ expandedNodes before
    if unexpanded = [] then
      selectExpansion mode tape prices c gamma before fuel
        (p++[visitedChoice mode tape prices c gamma before p])
    else p++[tape.action before .expansion p unexpanded]

def rollout (tape : SharedTape) (before : List (TreeEvaluation Act)) :
    ℕ → List Act → List Act
  | 0, p => p
  | fuel+1, p => if available p = [] then p else
      rollout tape before fuel (p++[tape.action before .rollout p (orderedAvailable p)])

theorem rollout_preserves_expanded_prefix (tape : SharedTape)
    (before : List (TreeEvaluation Act)) (fuel : ℕ) (p : List Act) :
    p <+: rollout tape before fuel p := by
  induction fuel generalizing p with
  | zero => exact List.prefix_refl _
  | succ fuel ih =>
    simp only [rollout]
    split_ifs
    · exact List.prefix_refl _
    · exact (List.prefix_append _ _).trans (ih _)

def resolveEvent (mode : ForecastMode) (tape : SharedTape)
    (prices : Unit × List Act → ℝ) (c gamma : ℝ) (reward : List Act → ℝ)
    (before : List (TreeEvaluation Act)) : TreeEvaluation Act :=
  let expanded := selectExpansion mode tape prices c gamma before 9 []
  let terminal := rollout tape before 9 expanded
  ⟨expanded,terminal,reward terminal,0,rollout_preserves_expanded_prefix tape before 9 expanded⟩

def generateAfterInit (mode : ForecastMode) (tape : SharedTape)
    (prices : Unit × List Act → ℝ) (c gamma B : ℝ) (reward : List Act → ℝ) :
    ℕ → List (TreeEvaluation Act) → List (TreeEvaluation Act)
  | 0, before => before
  | fuel+1, before => if targetReached (ownState prices before).totalPaid B then before else
      generateAfterInit mode tape prices c gamma B reward fuel
        (before++[resolveEvent mode tape prices c gamma reward before])




def generateNative (mode : ForecastMode) (tape : SharedTape)
    (prices : Unit × List Act → ℝ) (c gamma B : ℝ) (cap : ℕ) (reward : List Act → ℝ) :
    List (TreeEvaluation Act) :=
  generateAfterInit mode tape prices c gamma B reward (cap-8) (nativeFirstAdvance reward B)

theorem generated_native_retains_initialization (mode : ForecastMode) (tape : SharedTape)
    (prices : Unit × List Act → ℝ) (c gamma B : ℝ) (cap : ℕ) (reward : List Act → ℝ) :
    initialization reward <+: generateNative mode tape prices c gamma B cap reward := by
  have h : ∀ fuel before, before <+:
      generateAfterInit mode tape prices c gamma B reward fuel before := by
    intro fuel
    induction fuel with
    | zero => intro before; exact List.prefix_refl _
    | succ fuel ih =>
      intro before
      simp only [generateAfterInit]
      split_ifs
      · exact List.prefix_refl _
      · exact (List.prefix_append _ _).trans (ih _)
  exact h (cap-8) (initialization reward)

theorem generated_native_cost_stop (mode : ForecastMode) (tape : SharedTape)
    (prices : Unit × List Act → ℝ) (c gamma B : ℝ) (cap : ℕ) (reward : List Act → ℝ)
    (hcost : targetReached (ownState prices (initialization reward)).totalPaid B) :
    generateNative mode tape prices c gamma B cap reward = initialization reward := by
  unfold generateNative nativeFirstAdvance
  cases cap-8 <;> simp [generateAfterInit,hcost]

theorem generated_native_count_bound (mode : ForecastMode) (tape : SharedTape)
    (prices : Unit × List Act → ℝ) (c gamma B : ℝ) (cap : ℕ) (reward : List Act → ℝ)
    (hcap : 8 ≤ cap) :
    (generateNative mode tape prices c gamma B cap reward).length ≤ cap := by
  have h : ∀ fuel before,
      (generateAfterInit mode tape prices c gamma B reward fuel before).length ≤
        before.length+fuel := by
    intro fuel
    induction fuel with
    | zero => intro before; simp [generateAfterInit]
    | succ fuel ih =>
      intro before
      simp only [generateAfterInit]
      split_ifs
      · omega
      · have hh := ih (before++[resolveEvent mode tape prices c gamma reward before])
        simp only [List.length_append,List.length_singleton] at hh
        omega
  have hh := h (cap-8) (nativeFirstAdvance reward B)
  rw [native_first_advance_is_eight] at hh
  exact hh.trans (by omega)

def reportedEvents (mode : ForecastMode) (tape : SharedTape)
    (prices : Unit × List Act → ℝ) (c gamma B : ℝ) (cap : ℕ) (reward : List Act → ℝ) :
    List (TreeEvaluation Act) :=
  let run := generateNative mode tape prices c gamma B cap reward
  run.take (T_B (fun n => (ownState prices (run.take n)).totalPaid) run.length B snapshotTolerance)

theorem reported_events_are_own_history_prefix (mode : ForecastMode) (tape : SharedTape)
    (prices : Unit × List Act → ℝ) (c gamma B : ℝ) (cap : ℕ) (reward : List Act → ℝ) :
    reportedEvents mode tape prices c gamma B cap reward <+:
      generateNative mode tape prices c gamma B cap reward := List.take_prefix _ _

end AgentUCTNativeRefinement
