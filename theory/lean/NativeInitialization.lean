import NativeGrammar



set_option autoImplicit false
set_option maxRecDepth 8192
set_option maxHeartbeats 4000000
noncomputable section
namespace AgentUCTNativeRefinement
open AgentUCTPaper Finset

def seedEvent (reward : List Act → ℝ) (q : Fin 8) : TreeEvaluation Act :=
  ⟨[.query q], seedPath q, reward (seedPath q), 0,
    by exact ⟨(seedPath q).drop 1, by simp [seedPath,leaf]⟩⟩

def initialization (reward : List Act → ℝ) : List (TreeEvaluation Act) :=
  (List.finRange 8).map (seedEvent reward)

def demand (p : List Act) : Finset (Unit × List Act) := panelDemand {()} p

def emptyMeter : MeteredTreeState Unit Act := ⟨emptyStatistics, ∅, 0, 0⟩

def ownState (price : Unit × List Act → ℝ) (events : List (TreeEvaluation Act)) :
    MeteredTreeState Unit Act :=
  replayMetered {()} id price (fun _ => 0) events emptyMeter

def ownCache (events : List (TreeEvaluation Act)) : Finset (Unit × List Act) :=
  events.foldl (fun cache e => cache ∪ demand e.terminal) ∅

theorem ownState_cache (price : Unit × List Act → ℝ) (events : List (TreeEvaluation Act)) :
    (ownState price events).materialized = ownCache events := by
  unfold ownState ownCache
  have h : ∀ (es : List (TreeEvaluation Act)) (s : MeteredTreeState Unit Act),
      (replayMetered {()} id price (fun _ => 0) es s).materialized =
        es.foldl (fun cache e => cache ∪ demand e.terminal) s.materialized := by
    intro es
    induction es with
    | nil => intro s; rfl
    | cons e es ih => intro s; exact ih (meterStep {()} id price (fun _ => 0) s e)
  exact h events emptyMeter

theorem ownState_backup (price : Unit × List Act → ℝ) (events : List (TreeEvaluation Act)) :
    (ownState price events).stats = replayBackup events emptyStatistics := by
  exact replayMetered_stats {()} id price (fun _ => 0) events emptyMeter

theorem ownState_actual_bill (price : Unit × List Act → ℝ) (events : List (TreeEvaluation Act)) :
    (ownState price events).totalPaid = cacheWeight price (ownCache events) := by
  have h := replayMetered_total {()} id price (fun _ => 0) events emptyMeter
  rw [← ownState_cache price events]
  simpa [ownState,emptyMeter,MeteredTreeState.totalPaid,cacheWeight] using h

theorem initialization_root_visits (reward : List Act → ℝ) :
    (replayBackup (initialization reward) emptyStatistics []).visits = 8 := by
  rw [replayBackup_root_visits]
  simp [initialization]

theorem initialization_child_stats (reward : List Act → ℝ) (q : Fin 8) :
    (replayBackup (initialization reward) emptyStatistics [.query q]).visits = 1 ∧
    (replayBackup (initialization reward) emptyStatistics [.query q]).mean =
      reward (seedPath q) := by
  fin_cases q <;>
    simp +decide [initialization,seedEvent,replayBackup,backupEvent,emptyStatistics,
      BackupStat.mean,finRange8_explicit]



theorem initialization_deeper_nodes_unvisited (reward : List Act → ℝ)
    (q : Fin 8) (r : Act) :
    (replayBackup (initialization reward) emptyStatistics [.query q,r]).visits = 0 := by
  rw [replayBackup_visits]
  simp [emptyStatistics,backedCount,initialization,seedEvent,List.filter_map]

def actionPrice (queryCost generatorCost e5Cost bgeCost qwenCost : ℝ) : Act → ℝ
  | .query q => if q = identityQuery then 0 else queryCost
  | .normalRetriever r => if r = 0 then 0 else e5Cost
  | .hydeRetriever r => if r = 0 then e5Cost else if r = 1 then bgeCost else qwenCost
  | .width _ => generatorCost
  | .answer m => if m = 2 then 11 * generatorCost else generatorCost
  | _ => 0

def price (q a e b k : ℝ) (resource : Unit × List Act) : ℝ :=
  match resource.2.getLast? with
  | none => 0
  | some action => actionPrice q a e b k action

def initialBill (q a e : ℝ) : ℝ := 7*q + 16*a + e

theorem demand_leaf_explicit (q : Fin 8) (r : Act) (w : Fin 4) (m : Fin 3) :
    demand (leaf q r w m) =
      {((),[.query q]),
       ((),[.query q,r]),
       ((),[.query q,r,.selection 0]),
       ((),[.query q,r,.selection 0,.width w]),
       ((),[.query q,r,.selection 0,.width w,.stop]),
       ((),[.query q,r,.selection 0,.width w,.stop,.reranker 0]),
       ((),[.query q,r,.selection 0,.width w,.stop,.reranker 0,.topm m]),
       ((),[.query q,r,.selection 0,.width w,.stop,.reranker 0,.topm m,.context 0]),
       ((),leaf q r w m)} := by
  have hi : (Finset.Icc 1 9 : Finset ℕ) = {1,2,3,4,5,6,7,8,9} := by decide
  simp only [demand,panelDemand,executionPrefixes,leaf,List.length_cons,List.length_nil]
  rw [hi]
  simp

def initialCache : Finset (Unit × List Act) :=
  Finset.univ.biUnion fun q : Fin 8 => demand (seedPath q)

theorem initialization_cache_exact (reward : List Act → ℝ) :
    ownCache (initialization reward) = initialCache := by
  ext resource
  simp +decide [ownCache,initialization,seedEvent,initialCache,finRange8_explicit,
    finUniv8_explicit]

theorem demand_leaf_head (q : Fin 8) (r : Act) (w : Fin 4) (m : Fin 3)
    (resource : Unit × List Act) (h : resource ∈ demand (leaf q r w m)) :
    resource.2.head? = some (.query q) := by
  rw [demand_leaf_explicit] at h
  simp only [Finset.mem_insert, Finset.mem_singleton] at h
  rcases h with h|h|h|h|h|h|h|h|h <;> subst resource <;> rfl

theorem seed_demands_disjoint (q t : Fin 8) (h : q ≠ t) :
    Disjoint (demand (seedPath q)) (demand (seedPath t)) := by
  apply Finset.disjoint_left.mpr
  intro resource hq ht
  have he := (demand_leaf_head q (seedRetriever q) 0 0 resource hq).symm.trans
    (demand_leaf_head t (seedRetriever t) 0 0 resource ht)
  simp only [Option.some.injEq, Act.query.injEq] at he
  exact h he

theorem seed_bill (q a e b k : ℝ) (t : Fin 8) :
    cacheWeight (price q a e b k) (demand (seedPath t)) =
      (if t = identityQuery then 0 else q) + 2*a + (if t = hyde then e else 0) := by
  simp only [seedPath]
  rw [demand_leaf_explicit]
  fin_cases t <;>
    simp +decide [seedRetriever,identityQuery,cacheWeight,price,actionPrice,
      leaf,Finset.sum_insert] <;> ring

theorem initialization_full_cold_bill (reward : List Act → ℝ) (q a e b k : ℝ) :
    (ownState (price q a e b k) (initialization reward)).totalPaid = initialBill q a e := by
  rw [ownState_actual_bill,initialization_cache_exact]
  unfold cacheWeight initialCache
  rw [Finset.sum_biUnion (fun i _ j _ hij => seed_demands_disjoint i j hij)]
  change (∑ t : Fin 8, cacheWeight (price q a e b k) (demand (seedPath t))) = _
  simp_rw [seed_bill]
  simp +decide [finUniv8_explicit,hyde,identityQuery,initialBill]
  ring

end AgentUCTNativeRefinement
