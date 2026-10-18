import BudgetP1



set_option autoImplicit false
set_option maxRecDepth 4096
set_option maxHeartbeats 2000000
noncomputable section
namespace AgentUCTDefaultBudgetP1V2
open AgentUCTPaper Finset


abbrev Resource := Unit × List Bool
def leaf (branch hidden : Bool) : List Bool :=
  [branch, hidden, branch && hidden]
def terminals : Finset (List Bool) :=
  {leaf false false, leaf false true, leaf true false, leaf true true}
def demand (branch hidden : Bool) : Finset Resource :=
  panelDemand AgentUCTBudgetP1V2.qids (AgentUCTBudgetP1V2.executionRoot ++ leaf branch hidden)
def actionPrice (a r : ℝ) (action : Bool) : ℝ := if action then r else a
def prices (a r : ℝ) (resource : Resource) : ℝ :=
  match resource.2.getLast? with
  | none => 0
  | some action => actionPrice a r action
def cache (events : List (TreeEvaluation Bool)) : Finset Resource :=
  (replayPublished AgentUCTBudgetP1V2.qids (fun x => AgentUCTBudgetP1V2.executionRoot ++ x) events AgentUCTBudgetP1V2.initialCaches).restorable
def spend (a r h : ℝ) (events : List (TreeEvaluation Bool)) : ℝ :=
  meteredSearchCost AgentUCTBudgetP1V2.qids AgentUCTBudgetP1V2.executionRoot (prices a r) (fun _ => h) events AgentUCTBudgetP1V2.initialMeter
def reward (u delta good bad : ℝ) (path : List Bool) : ℝ :=
  if path = leaf true true then bad else AgentUCTBudgetP1V2.reward u delta good bad path
def discoverB (u delta good bad : ℝ) : TreeEvaluation Bool :=
  ⟨[true,true], leaf true true, bad, 0, by simp [leaf]⟩
def completeTrace := AgentUCTBudgetP1V2.completeTrace
def shortTrace (u delta good bad : ℝ) := AgentUCTBudgetP1V2.initialization u delta good bad ++ [discoverB u delta good bad]
def warmB := AgentUCTBudgetP1V2.warmB
def adverseTrace (u delta good bad : ℝ) :=
  AgentUCTBudgetP1V2.initialization u delta good bad ++ [discoverB u delta good bad, warmB u delta good bad]

theorem demand_explicit (branch hidden : Bool) :
    demand branch hidden = {((), [false]), ((), [false,branch]),
      ((), [false,branch,hidden]), ((), [false,branch,hidden,branch && hidden])} := by
  have hI : (Finset.Icc 1 4 : Finset ℕ) = {1,2,3,4} := by decide
  cases branch <;> cases hidden <;>
    norm_num [demand, panelDemand, AgentUCTBudgetP1V2.qids, AgentUCTBudgetP1V2.executionRoot, leaf, executionPrefixes, hI]

theorem initialization_cache (u delta good bad : ℝ) :
    cache (AgentUCTBudgetP1V2.initialization u delta good bad) = demand false false ∪ demand true false := by
  simp [cache, AgentUCTBudgetP1V2.initialization, AgentUCTBudgetP1V2.seedA, AgentUCTBudgetP1V2.seedB, AgentUCTBudgetP1V2.event, AgentUCTBudgetP1V2.leaf, replayPublished,
    publishComplete, AgentUCTBudgetP1V2.initialCaches, demand, leaf, List.foldl]

theorem residual_bills (a r u delta good bad : ℝ) :
    coldWork (prices a r) (cache (AgentUCTBudgetP1V2.initialization u delta good bad)) (demand false true) = r+a ∧
    coldWork (prices a r) (cache (AgentUCTBudgetP1V2.initialization u delta good bad)) (demand true true) = 2*r := by
  rw [initialization_cache]
  simp +decide [demand_explicit, coldWork, prices, actionPrice, Finset.sdiff_eq_filter,
    Finset.filter_insert, Finset.filter_singleton, Finset.sum_insert]
  ring

theorem own_overlap (branch : Bool) :
    demand branch false ∩ demand branch true = {((),[false]), ((),[false,branch])} := by
  cases branch <;> ext resource <;> simp +decide [demand_explicit]

theorem own_overlap_weight (a r : ℝ) (branch : Bool) :
    cacheWeight (prices a r) (demand branch false ∩ demand branch true) =
      a + actionPrice a r branch := by
  rw [own_overlap]
  cases branch <;> simp [cacheWeight, prices, actionPrice] <;> ring



def sample16 (branch : Bool) (i : Fin 16) : List Bool := leaf branch (decide (12 ≤ i.val))
def law (_before : List (TreeEvaluation Bool)) (p : List Bool) (chosen : Bool) (path : List Bool) : ℝ :=
  if p = [] then sampledLaw 16 (sample16 chosen) path
  else uniformTerminalLaw terminals (p ++ [chosen]) path
def completePenalty (a r gamma : ℝ) :=
  coldForecastPenalty AgentUCTBudgetP1V2.qids AgentUCTBudgetP1V2.executionRoot terminals (prices a r) gamma law AgentUCTBudgetP1V2.initialCaches
def nextPenalty (a r gamma : ℝ) (before : List (TreeEvaluation Bool)) (p : List Bool)
    (chosen : Bool) : ℝ :=
  gamma * ∑ path ∈ subtreeTerminals terminals (p ++ [chosen]),
    law before p chosen path * nextUnpaidBill (cache before) (prices a r) (AgentUCTBudgetP1V2.orderedResources path)

theorem sample16_legal (branch : Bool) (i : Fin 16) :
    sample16 branch i ∈ subtreeTerminals terminals [branch] := by
  cases branch <;> simp [sample16, subtreeTerminals, terminals, leaf]
  all_goals omega

theorem sample16_mass (branch : Bool) :
    ∑ path ∈ subtreeTerminals terminals [branch], sampledLaw 16 (sample16 branch) path = 1 := by
  exact sampledLaw_mass _ 16 (by decide) _ (sample16_legal branch)

theorem sample16_weights (branch hidden : Bool) :
    sampledLaw 16 (sample16 branch) (leaf branch hidden) = if hidden then 1/4 else 3/4 := by
  cases branch <;> cases hidden <;>
    norm_num [sampledLaw, sample16, leaf, Fin.sum_univ_succ]

theorem initial_forecasts (a r gamma u delta good bad : ℝ) :
    completePenalty a r gamma (AgentUCTBudgetP1V2.initialization u delta good bad) [] false = gamma*((r+a)/4) ∧
    completePenalty a r gamma (AgentUCTBudgetP1V2.initialization u delta good bad) [] true = gamma*((2*r)/4) := by
  have hwA : sampledLaw 16 (sample16 false) [false,true,false] = 1/4 := by
    simpa [leaf] using sample16_weights false true
  have hwB : sampledLaw 16 (sample16 true) [true,true,true] = 1/4 := by
    simpa [leaf] using sample16_weights true true
  unfold completePenalty coldForecastPenalty
  change gamma * referenceColdCost AgentUCTBudgetP1V2.qids AgentUCTBudgetP1V2.executionRoot terminals (prices a r)
    (law (AgentUCTBudgetP1V2.initialization u delta good bad) [] false)
    (cache (AgentUCTBudgetP1V2.initialization u delta good bad)) [false] = _ ∧
    gamma * referenceColdCost AgentUCTBudgetP1V2.qids AgentUCTBudgetP1V2.executionRoot terminals (prices a r)
    (law (AgentUCTBudgetP1V2.initialization u delta good bad) [] true)
    (cache (AgentUCTBudgetP1V2.initialization u delta good bad)) [true] = _
  rw [initialization_cache]
  have hI : (Finset.Icc 1 4 : Finset ℕ) = {1,2,3,4} := by decide
  simp +decide [referenceColdCost, law, terminals, subtreeTerminals, leaf,
    hwA, hwB, panelDemand, AgentUCTBudgetP1V2.qids, AgentUCTBudgetP1V2.executionRoot, executionPrefixes, hI,
    coldWork, demand_explicit, prices, actionPrice, Finset.sdiff_eq_filter,
    Finset.filter_insert, Finset.filter_singleton, Finset.sum_insert]
  constructor <;> (apply Or.inl; ring)

theorem initial_next_forecasts (a r gamma u delta good bad : ℝ) (hr : 0 < r) :
    nextPenalty a r gamma (AgentUCTBudgetP1V2.initialization u delta good bad) [] false = gamma*(r/4) ∧
    nextPenalty a r gamma (AgentUCTBudgetP1V2.initialization u delta good bad) [] true = gamma*(r/4) := by
  have hwA : sampledLaw 16 (sample16 false) [false,true,false] = 1/4 := by
    simpa [leaf] using sample16_weights false true
  have hwB : sampledLaw 16 (sample16 true) [true,true,true] = 1/4 := by
    simpa [leaf] using sample16_weights true true
  rw [nextPenalty, nextPenalty, initialization_cache]
  simp +decide [law, terminals, subtreeTerminals, leaf, hwA, hwB,
    AgentUCTBudgetP1V2.orderedResources, AgentUCTBudgetP1V2.executionRoot, demand_explicit, prices, actionPrice,
    nextUnpaidBill, List.range_succ, Finset.filter_insert, Finset.filter_singleton,
    Finset.sum_insert, not_le.mpr hr]
  ring_nf
  simp

theorem complete_legal (u delta good bad : ℝ) :
    LegalTreeRun (fun p => p ∈ terminals) {[]} (completeTrace u delta good bad) := by
  simp +decide [completeTrace, AgentUCTBudgetP1V2.completeTrace, AgentUCTBudgetP1V2.initialization, AgentUCTBudgetP1V2.seedA, AgentUCTBudgetP1V2.seedB,
    AgentUCTBudgetP1V2.discoverA, AgentUCTBudgetP1V2.warmA, AgentUCTBudgetP1V2.replayA, AgentUCTBudgetP1V2.event, LegalTreeRun, LegalTreeEvent,
    growTree, terminals, leaf, AgentUCTBudgetP1V2.leaf]
theorem short_legal (u delta good bad : ℝ) :
    LegalTreeRun (fun p => p ∈ terminals) {[]} (shortTrace u delta good bad) := by
  simp +decide [shortTrace, AgentUCTBudgetP1V2.initialization, AgentUCTBudgetP1V2.seedA, AgentUCTBudgetP1V2.seedB, discoverB, AgentUCTBudgetP1V2.event,
    LegalTreeRun, LegalTreeEvent, growTree, terminals, leaf, AgentUCTBudgetP1V2.leaf]
theorem adverse_legal (u delta good bad : ℝ) :
    LegalTreeRun (fun p => p ∈ terminals) {[]} (adverseTrace u delta good bad) := by
  simp +decide [adverseTrace, AgentUCTBudgetP1V2.initialization, AgentUCTBudgetP1V2.seedA, AgentUCTBudgetP1V2.seedB, discoverB, warmB,
    AgentUCTBudgetP1V2.warmB, AgentUCTBudgetP1V2.event, LegalTreeRun, LegalTreeEvent, growTree, terminals, leaf, AgentUCTBudgetP1V2.leaf]

def LocalRule (c : ℝ)
    (penalty : List (TreeEvaluation Bool) → List Bool → Bool → ℝ)
    (before : List (TreeEvaluation Bool)) (e : TreeEvaluation Bool) : Prop :=
  ∀ p a, childAfter p e.expanded = some a →
    (∀ b ∈ availableChildren terminals p,
      (replayBackup before emptyStatistics (p ++ [b])).visits = 0 →
      (replayBackup before emptyStatistics (p ++ [a])).visits = 0) ∧
    ((∀ b ∈ availableChildren terminals p,
      0 < (replayBackup before emptyStatistics (p ++ [b])).visits) →
      ∀ b ∈ availableChildren terminals p,
        treeIndex (replayBackup before emptyStatistics (p ++ [b])).mean c
          (penalty before p b) (replayBackup before emptyStatistics p).visits
          (replayBackup before emptyStatistics (p ++ [b])).visits ≤
        treeIndex (replayBackup before emptyStatistics (p ++ [a])).mean c
          (penalty before p a) (replayBackup before emptyStatistics p).visits
          (replayBackup before emptyStatistics (p ++ [a])).visits)

theorem allocation_from_local (c : ℝ) (penalty) (events : List (TreeEvaluation Bool))
    (hs : ∀ n (hn : n < events.length), LocalRule c penalty (events.take n) events[n]) :
    TreeAllocationRule terminals c penalty events := by
  intro before e after he p a hp
  have hn : before.length < events.length := by simp [he]
  have hs' := hs before.length hn
  have ht : events.take before.length = before := by simp [he]
  have hg : events[before.length] = e := by simp [he]
  rw [ht, hg] at hs'
  exact hs' p a hp

theorem shallow_children (p : List Bool) (hl : p.length ≤ 1) :
    availableChildren terminals p = availableChildren AgentUCTBudgetP1V2.terminals p := by
  cases p with
  | nil => simp +decide [availableChildren, terminals, AgentUCTBudgetP1V2.terminals,
      leaf, AgentUCTBudgetP1V2.leaf, childAfter]
  | cons b tail =>
    have ht : tail = [] := List.eq_nil_of_length_eq_zero (by simp only [List.length_cons] at hl; omega)
    subst tail
    cases b <;> simp +decide [availableChildren, terminals, AgentUCTBudgetP1V2.terminals,
      leaf, AgentUCTBudgetP1V2.leaf, childAfter]

theorem shallow_event_children (e : TreeEvaluation Bool) (hl : e.expanded.length ≤ 2)
    (p : List Bool) (chosen : Bool) (hp : childAfter p e.expanded = some chosen) :
    availableChildren terminals p = availableChildren AgentUCTBudgetP1V2.terminals p := by
  have hpre := (childAfter_some_iff p e.expanded chosen).mp hp
  have hlen := hpre.length_le
  simp only [List.length_append, List.length_cons, List.length_nil] at hlen
  exact shallow_children p (by omega)

theorem transfer_local (c : ℝ) (penalty) (before : List (TreeEvaluation Bool))
    (e : TreeEvaluation Bool)
    (hchildren : ∀ p a, childAfter p e.expanded = some a →
      availableChildren terminals p = availableChildren AgentUCTBudgetP1V2.terminals p)
    (hold : AgentUCTBudgetP1V2.LocalRule c penalty before e) :
    LocalRule c penalty before e := by
  intro p a hp
  simpa only [hchildren p a hp] using hold p a hp

theorem complete_after_publication (a r gamma u delta good bad : ℝ)
    (n : ℕ) (hn0 : 3 ≤ n) (hn1 : n ≤ 4) :
    completePenalty a r gamma ((completeTrace u delta good bad).take n) [] false = 0 ∧
    completePenalty a r gamma ((completeTrace u delta good bad).take n) [] true = gamma*((2*r)/4) ∧
    completePenalty a r gamma ((completeTrace u delta good bad).take n) [false] false = 0 ∧
    completePenalty a r gamma ((completeTrace u delta good bad).take n) [false] true = 0 := by
  have hwB : sampledLaw 16 (sample16 true) [true,true,true] = 1/4 := by
    simpa [leaf] using sample16_weights true true
  have hI : (Finset.Icc 1 4 : Finset ℕ) = {1,2,3,4} := by decide
  interval_cases n <;>
    simp +decide [completePenalty, coldForecastPenalty, referenceColdCost, law,
      uniformTerminalLaw, hwB, terminals, subtreeTerminals, leaf,
      completeTrace, AgentUCTBudgetP1V2.completeTrace, AgentUCTBudgetP1V2.initialization,
      AgentUCTBudgetP1V2.seedA, AgentUCTBudgetP1V2.seedB, AgentUCTBudgetP1V2.discoverA,
      AgentUCTBudgetP1V2.warmA, AgentUCTBudgetP1V2.replayA, AgentUCTBudgetP1V2.event,
      AgentUCTBudgetP1V2.leaf, replayPublished, publishComplete, AgentUCTBudgetP1V2.initialCaches,
      panelDemand, AgentUCTBudgetP1V2.executionRoot, AgentUCTBudgetP1V2.qids,
      executionPrefixes, hI, coldWork, prices, actionPrice,
      Finset.sdiff_eq_filter, Finset.filter_insert, Finset.filter_singleton, Finset.sum_insert] <;>
    (apply Or.inl; ring)

theorem complete_root_initial (a r gamma c u delta good bad : ℝ)
    (hsplit : delta < gamma*((r-a)/4)) :
    AgentUCTBudgetP1V2.RootMax c (completePenalty a r gamma)
      (AgentUCTBudgetP1V2.initialization u delta good bad) false := by
  obtain ⟨ha, hb⟩ := initial_forecasts a r gamma u delta good bad
  intro chosen
  cases chosen
  · exact le_refl _
  · simp [AgentUCTBudgetP1V2.initialization, AgentUCTBudgetP1V2.seedA,
      AgentUCTBudgetP1V2.seedB, AgentUCTBudgetP1V2.event, AgentUCTBudgetP1V2.reward,
      AgentUCTBudgetP1V2.leaf] at ha hb
    simp [AgentUCTBudgetP1V2.initialization, AgentUCTBudgetP1V2.seedA,
      AgentUCTBudgetP1V2.seedB, AgentUCTBudgetP1V2.event, replayBackup, backupEvent,
      emptyStatistics, BackupStat.mean, AgentUCTBudgetP1V2.reward,
      AgentUCTBudgetP1V2.leaf, treeIndex, ha, hb]
    linarith

theorem complete_root_warm (a r gamma c u delta good bad : ℝ)
    (hc : 0 ≤ c) (hu : 0 ≤ u) (hg : 0 ≤ good) (hu1 : u+delta ≤ 1)
    (hwarm : 1 + max (treeBonus c 3 1) (treeBonus c 4 1) < gamma*((2*r)/4))
    (n : ℕ) (hn0 : 3 ≤ n) (hn1 : n ≤ 4) :
    AgentUCTBudgetP1V2.RootMax c (completePenalty a r gamma)
      ((completeTrace u delta good bad).take n) false := by
  obtain ⟨ha, hb, _, _⟩ := complete_after_publication a r gamma u delta good bad n hn0 hn1
  have hB3 := le_max_left (treeBonus c 3 1) (treeBonus c 4 1)
  have hB4 := le_max_right (treeBonus c 3 1) (treeBonus c 4 1)
  intro chosen
  cases chosen
  · exact le_refl _
  · interval_cases n
    · have hA := treeBonus_nonnegative hc 3 2
      simp [completeTrace, AgentUCTBudgetP1V2.completeTrace, AgentUCTBudgetP1V2.initialization,
        AgentUCTBudgetP1V2.seedA, AgentUCTBudgetP1V2.seedB, AgentUCTBudgetP1V2.discoverA,
        AgentUCTBudgetP1V2.warmA, AgentUCTBudgetP1V2.replayA, AgentUCTBudgetP1V2.event,
        AgentUCTBudgetP1V2.reward, AgentUCTBudgetP1V2.leaf] at ha hb
      simp [completeTrace, AgentUCTBudgetP1V2.completeTrace, AgentUCTBudgetP1V2.initialization,
        AgentUCTBudgetP1V2.seedA, AgentUCTBudgetP1V2.seedB, AgentUCTBudgetP1V2.discoverA,
        AgentUCTBudgetP1V2.warmA, AgentUCTBudgetP1V2.replayA, AgentUCTBudgetP1V2.event,
        replayBackup, backupEvent, emptyStatistics, BackupStat.mean,
        AgentUCTBudgetP1V2.reward, AgentUCTBudgetP1V2.leaf, treeIndex, ha, hb]
      nlinarith
    · have hA := treeBonus_nonnegative hc 4 3
      simp [completeTrace, AgentUCTBudgetP1V2.completeTrace, AgentUCTBudgetP1V2.initialization,
        AgentUCTBudgetP1V2.seedA, AgentUCTBudgetP1V2.seedB, AgentUCTBudgetP1V2.discoverA,
        AgentUCTBudgetP1V2.warmA, AgentUCTBudgetP1V2.replayA, AgentUCTBudgetP1V2.event,
        AgentUCTBudgetP1V2.reward, AgentUCTBudgetP1V2.leaf] at ha hb
      simp [completeTrace, AgentUCTBudgetP1V2.completeTrace, AgentUCTBudgetP1V2.initialization,
        AgentUCTBudgetP1V2.seedA, AgentUCTBudgetP1V2.seedB, AgentUCTBudgetP1V2.discoverA,
        AgentUCTBudgetP1V2.warmA, AgentUCTBudgetP1V2.replayA, AgentUCTBudgetP1V2.event,
        replayBackup, backupEvent, emptyStatistics, BackupStat.mean,
        AgentUCTBudgetP1V2.reward, AgentUCTBudgetP1V2.leaf, treeIndex, ha, hb]
      nlinarith

theorem complete_allocation (a r gamma c u delta good bad : ℝ)
    (hc : 0 ≤ c) (hu : 0 ≤ u) (hg : 0 ≤ good) (hug : u ≤ good) (hu1 : u+delta ≤ 1)
    (hsplit : delta < gamma*((r-a)/4))
    (hwarm : 1 + max (treeBonus c 3 1) (treeBonus c 4 1) < gamma*((2*r)/4)) :
    TreeAllocationRule terminals c (completePenalty a r gamma) (completeTrace u delta good bad) := by
  apply allocation_from_local
  intro n hn
  have hn' : n < 5 := by simpa [completeTrace, AgentUCTBudgetP1V2.completeTrace,
    AgentUCTBudgetP1V2.initialization] using hn
  interval_cases n
  · apply transfer_local
    · exact shallow_event_children (AgentUCTBudgetP1V2.seedA u delta good bad) (by norm_num [AgentUCTBudgetP1V2.seedA, AgentUCTBudgetP1V2.event])
    · exact AgentUCTBudgetP1V2.seedA_local c _ u delta good bad
  · apply transfer_local
    · exact shallow_event_children (AgentUCTBudgetP1V2.seedB u delta good bad) (by norm_num [AgentUCTBudgetP1V2.seedB, AgentUCTBudgetP1V2.event])
    · exact AgentUCTBudgetP1V2.seedB_local c _ u delta good bad
  · apply transfer_local
    · exact shallow_event_children (AgentUCTBudgetP1V2.discoverA u delta good bad) (by norm_num [AgentUCTBudgetP1V2.discoverA, AgentUCTBudgetP1V2.event])
    · exact AgentUCTBudgetP1V2.discover_local c _ u delta good bad false
        (complete_root_initial a r gamma c u delta good bad hsplit)
  · apply transfer_local
    · exact shallow_event_children (AgentUCTBudgetP1V2.warmA u delta good bad) (by norm_num [AgentUCTBudgetP1V2.warmA, AgentUCTBudgetP1V2.event])
    · exact AgentUCTBudgetP1V2.warmA_local c _ u delta good bad
        (complete_root_warm a r gamma c u delta good bad hc hu hg hu1 hwarm 3 (by decide) (by decide))
  · apply transfer_local
    · intro p chosen hp
      rcases AgentUCTBudgetP1V2.parents3 p chosen false true false hp with
        ⟨rfl,rfl⟩ | ⟨rfl,rfl⟩ | ⟨rfl,rfl⟩
      · exact shallow_children [] (by simp)
      · exact shallow_children [false] (by simp)
      · simp +decide [availableChildren, terminals, AgentUCTBudgetP1V2.terminals,
          leaf, AgentUCTBudgetP1V2.leaf, childAfter]
    · obtain ⟨_,_,hz0,hz1⟩ := complete_after_publication a r gamma u delta good bad 4 (by decide) (by decide)
      exact AgentUCTBudgetP1V2.replayA_local c _ u delta good bad hug hz0 hz1
        (complete_root_warm a r gamma c u delta good bad hc hu hg hu1 hwarm 4 (by decide) (by decide))

theorem next_root_initial (a r gamma c u delta good bad : ℝ)
    (hr : 0 < r) (hd : 0 ≤ delta) :
    AgentUCTBudgetP1V2.RootMax c (nextPenalty a r gamma)
      (AgentUCTBudgetP1V2.initialization u delta good bad) true := by
  obtain ⟨ha,hb⟩ := initial_next_forecasts a r gamma u delta good bad hr
  intro chosen
  cases chosen
  · simp [AgentUCTBudgetP1V2.initialization, AgentUCTBudgetP1V2.seedA,
      AgentUCTBudgetP1V2.seedB, AgentUCTBudgetP1V2.event, AgentUCTBudgetP1V2.reward,
      AgentUCTBudgetP1V2.leaf] at ha hb
    simp [AgentUCTBudgetP1V2.initialization, AgentUCTBudgetP1V2.seedA,
      AgentUCTBudgetP1V2.seedB, AgentUCTBudgetP1V2.event, replayBackup, backupEvent,
      emptyStatistics, BackupStat.mean, AgentUCTBudgetP1V2.reward,
      AgentUCTBudgetP1V2.leaf, treeIndex, ha, hb]
    linarith
  · exact le_refl _

theorem short_allocation (a r gamma c u delta good bad : ℝ) (hr : 0 < r) (hd : 0 ≤ delta) :
    TreeAllocationRule terminals c (nextPenalty a r gamma) (shortTrace u delta good bad) := by
  apply allocation_from_local
  intro n hn
  have hn' : n < 3 := by simpa [shortTrace, AgentUCTBudgetP1V2.initialization] using hn
  interval_cases n
  · apply transfer_local
    · exact shallow_event_children (AgentUCTBudgetP1V2.seedA u delta good bad) (by norm_num [AgentUCTBudgetP1V2.seedA, AgentUCTBudgetP1V2.event])
    · exact AgentUCTBudgetP1V2.seedA_local c _ u delta good bad
  · apply transfer_local
    · exact shallow_event_children (AgentUCTBudgetP1V2.seedB u delta good bad) (by norm_num [AgentUCTBudgetP1V2.seedB, AgentUCTBudgetP1V2.event])
    · exact AgentUCTBudgetP1V2.seedB_local c _ u delta good bad
  · change LocalRule c (nextPenalty a r gamma) (AgentUCTBudgetP1V2.initialization u delta good bad)
      (AgentUCTBudgetP1V2.discoverB u delta good bad)
    apply transfer_local
    · exact shallow_event_children (AgentUCTBudgetP1V2.discoverB u delta good bad) (by norm_num [AgentUCTBudgetP1V2.discoverB, AgentUCTBudgetP1V2.event])
    · exact AgentUCTBudgetP1V2.discover_local c _ u delta good bad true
        (next_root_initial a r gamma c u delta good bad hr hd)

theorem unpriced_allocation (c u delta good bad : ℝ) (hd : 0 ≤ delta) :
    TreeAllocationRule terminals c (fun _ _ _ => 0) (shortTrace u delta good bad) := by
  apply allocation_from_local
  intro n hn
  have hn' : n < 3 := by simpa [shortTrace, AgentUCTBudgetP1V2.initialization] using hn
  interval_cases n
  · apply transfer_local
    · exact shallow_event_children (AgentUCTBudgetP1V2.seedA u delta good bad) (by norm_num [AgentUCTBudgetP1V2.seedA, AgentUCTBudgetP1V2.event])
    · exact AgentUCTBudgetP1V2.seedA_local c _ u delta good bad
  · apply transfer_local
    · exact shallow_event_children (AgentUCTBudgetP1V2.seedB u delta good bad) (by norm_num [AgentUCTBudgetP1V2.seedB, AgentUCTBudgetP1V2.event])
    · exact AgentUCTBudgetP1V2.seedB_local c _ u delta good bad
  · change LocalRule c (fun _ _ _ => 0) (AgentUCTBudgetP1V2.initialization u delta good bad)
      (AgentUCTBudgetP1V2.discoverB u delta good bad)
    apply transfer_local
    · exact shallow_event_children (AgentUCTBudgetP1V2.discoverB u delta good bad) (by norm_num [AgentUCTBudgetP1V2.discoverB, AgentUCTBudgetP1V2.event])
    · exact AgentUCTBudgetP1V2.discover_local c _ u delta good bad true
        (AgentUCTBudgetP1V2.unpriced_root_initial c u delta good bad hd)

def ownReceiptIndices (before : List (TreeEvaluation Bool)) (resource : Resource) : Finset ℕ :=
  (Finset.range before.length).filter (fun i =>
    resource ∈ cache (before.take (i+1)) \ cache (before.take i))
def actionReceiptIndices (before : List (TreeEvaluation Bool)) (action : Bool) : Finset (ℕ × Resource) :=
  ((Finset.range before.length).product
    (workflowResources AgentUCTBudgetP1V2.qids AgentUCTBudgetP1V2.executionRoot terminals)).filter
    (fun sample => sample.2 ∈ cache (before.take (sample.1+1)) \ cache (before.take sample.1) ∧
      sample.2.2.getLast? = some action)

theorem onlineMean_constant_on {I : Type*} (prior : ℝ) (samples : Finset I) (values : I → ℝ)
    (hv : ∀ i ∈ samples, values i = prior) : onlineMean prior samples values = prior := by
  have hsum : (∑ i ∈ samples, values i) = ∑ _i ∈ samples, prior :=
    Finset.sum_congr rfl hv
  unfold onlineMean
  rw [hsum]
  change onlineMean prior samples (fun _ => prior) = prior
  exact AgentUCTBudgetP1V2.constant_receipt_mean prior samples




def defaultQuote (a r : ℝ) (before : List (TreeEvaluation Bool)) (resource : Resource) : ℝ :=
  match resource.2.getLast? with
  | none => 0
  | some action =>
    let prefixSamples := ownReceiptIndices before resource
    let shared := ownReceiptIndices before resource
    if prefixSamples.Nonempty then onlineMean (actionPrice a r action) prefixSamples (fun _ => prices a r resource)
    else if shared.Nonempty then onlineMean (actionPrice a r action) shared (fun _ => prices a r resource)
    else onlineMean (actionPrice a r action) (actionReceiptIndices before action)
      (fun sample => prices a r sample.2)

theorem default_quote_exact (a r : ℝ) (before : List (TreeEvaluation Bool)) (resource : Resource) :
    defaultQuote a r before resource = prices a r resource := by
  unfold defaultQuote prices
  cases hl : resource.2.getLast? with
  | none => simp
  | some action =>
    simp only
    split_ifs
    · exact AgentUCTBudgetP1V2.constant_receipt_mean _ _
    · apply onlineMean_constant_on
      intro sample hs
      have hlast := (Finset.mem_filter.mp hs).2.2
      simp only [prices, hlast]

theorem clipping_inactive (a r capFalse capTrue : ℝ) (ha : a ≤ capFalse) (hr : r ≤ capTrue)
    (action : Bool) :
    min (actionPrice capFalse capTrue action) (actionPrice a r action) = actionPrice a r action := by
  cases action <;> simp [actionPrice, min_eq_right, ha, hr]

def childCount (before : List (TreeEvaluation Bool)) (p : List Bool) (chosen : Bool) : ℕ :=
  (before.filter (fun e => childAfter p e.terminal = some chosen)).length
def smoothedProbability (before : List (TreeEvaluation Bool)) (p : List Bool) (chosen : Bool) : ℝ :=
  ((childCount before p chosen : ℝ) + 1/2) /
    ((childCount before p false : ℝ) + childCount before p true + 1)

theorem smoothed_probability_positive (before : List (TreeEvaluation Bool)) (p : List Bool) (chosen : Bool) :
    0 < smoothedProbability before p chosen := by
  unfold smoothedProbability
  positivity

theorem historical_initial_hidden_mass (u delta good bad : ℝ) (branch : Bool) :
    smoothedProbability (AgentUCTBudgetP1V2.initialization u delta good bad) [branch] true = 1/4 ∧
    smoothedProbability (AgentUCTBudgetP1V2.initialization u delta good bad) [branch] false = 3/4 := by
  cases branch <;> norm_num [smoothedProbability, childCount, AgentUCTBudgetP1V2.initialization,
    AgentUCTBudgetP1V2.seedA, AgentUCTBudgetP1V2.seedB, AgentUCTBudgetP1V2.event,
    AgentUCTBudgetP1V2.leaf, childAfter]

theorem saved_sample16_supported (before : List (TreeEvaluation Bool)) (branch : Bool) (i : Fin 16) :
    sample16 branch i ∈ subtreeTerminals terminals [branch] ∧
    0 < smoothedProbability before [branch] (decide (12 ≤ i.val)) := by
  exact ⟨sample16_legal branch i, smoothed_probability_positive _ _ _⟩

def liveCompletePenalty (a r gamma : ℝ) (before : List (TreeEvaluation Bool)) (p : List Bool)
    (chosen : Bool) : ℝ :=
  coldForecastPenalty AgentUCTBudgetP1V2.qids AgentUCTBudgetP1V2.executionRoot terminals
    (defaultQuote a r before) gamma law AgentUCTBudgetP1V2.initialCaches before p chosen

theorem live_penalty_exact (a r gamma : ℝ) : liveCompletePenalty a r gamma = completePenalty a r gamma := by
  funext before p chosen
  have hprice : defaultQuote a r before = prices a r := funext (default_quote_exact a r before)
  simp only [liveCompletePenalty, hprice, completePenalty]

theorem complete_prefix_spend (a r h u delta good bad : ℝ) (n : ℕ) (hn : n ≤ 5) :
    spend a r h ((completeTrace u delta good bad).take n) =
      if n=0 then 0 else if n=1 then 4*a+h else if n=2 then 6*a+r+2*h
      else 6*a+r+(r+a)+(n:ℝ)*h := by
  have hI : (Finset.Icc 1 4 : Finset ℕ) = {1,2,3,4} := by decide
  interval_cases n <;> simp +decide [spend, meteredSearchCost, replayMetered, meterStep,
    AgentUCTBudgetP1V2.initialMeter, MeteredTreeState.totalPaid, completeTrace,
    AgentUCTBudgetP1V2.completeTrace, AgentUCTBudgetP1V2.initialization,
    AgentUCTBudgetP1V2.seedA, AgentUCTBudgetP1V2.seedB, AgentUCTBudgetP1V2.discoverA,
    AgentUCTBudgetP1V2.warmA, AgentUCTBudgetP1V2.replayA, AgentUCTBudgetP1V2.event,
    AgentUCTBudgetP1V2.leaf, List.foldl, panelDemand, AgentUCTBudgetP1V2.qids,
    AgentUCTBudgetP1V2.executionRoot, executionPrefixes, hI, coldWork,
    prices, actionPrice, Finset.sdiff_eq_filter, Finset.filter_insert,
    Finset.filter_singleton, Finset.sum_insert] <;> ring

theorem short_prefix_spend (a r h u delta good bad : ℝ) (n : ℕ) (hn : n ≤ 3) :
    spend a r h ((shortTrace u delta good bad).take n) =
      if n=0 then 0 else if n=1 then 4*a+h else if n=2 then 6*a+r+2*h
      else 6*a+r+2*r+3*h := by
  have hI : (Finset.Icc 1 4 : Finset ℕ) = {1,2,3,4} := by decide
  interval_cases n <;> simp +decide [spend, meteredSearchCost, replayMetered, meterStep,
    AgentUCTBudgetP1V2.initialMeter, MeteredTreeState.totalPaid, shortTrace,
    AgentUCTBudgetP1V2.initialization, AgentUCTBudgetP1V2.seedA, AgentUCTBudgetP1V2.seedB,
    discoverB, AgentUCTBudgetP1V2.event, AgentUCTBudgetP1V2.leaf, leaf, List.foldl,
    panelDemand, AgentUCTBudgetP1V2.qids, AgentUCTBudgetP1V2.executionRoot,
    executionPrefixes, hI, coldWork, prices, actionPrice, Finset.sdiff_eq_filter,
    Finset.filter_insert, Finset.filter_singleton, Finset.sum_insert] <;> ring

theorem adverse_prefix_spend (a r h u delta good bad : ℝ) (n : ℕ) (hn : n ≤ 4) :
    spend a r h ((adverseTrace u delta good bad).take n) =
      if n=0 then 0 else if n=1 then 4*a+h else if n=2 then 6*a+r+2*h
      else 6*a+r+2*r+(n:ℝ)*h := by
  have hI : (Finset.Icc 1 4 : Finset ℕ) = {1,2,3,4} := by decide
  interval_cases n <;> simp +decide [spend, meteredSearchCost, replayMetered, meterStep,
    AgentUCTBudgetP1V2.initialMeter, MeteredTreeState.totalPaid, adverseTrace,
    AgentUCTBudgetP1V2.initialization, AgentUCTBudgetP1V2.seedA, AgentUCTBudgetP1V2.seedB,
    discoverB, warmB, AgentUCTBudgetP1V2.warmB, AgentUCTBudgetP1V2.event,
    AgentUCTBudgetP1V2.leaf, leaf, List.foldl, panelDemand, AgentUCTBudgetP1V2.qids,
    AgentUCTBudgetP1V2.executionRoot, executionPrefixes, hI, coldWork,
    prices, actionPrice, Finset.sdiff_eq_filter, Finset.filter_insert,
    Finset.filter_singleton, Finset.sum_insert] <;> ring

def T_B (a r h B : ℝ) (events : List (TreeEvaluation Bool)) : ℕ :=
  AgentUCTBudgetP1V2.lastAffordable (fun n => spend a r h (events.take n)) B events.length
def FirstCompleteCrossing (a r h B : ℝ) (events : List (TreeEvaluation Bool)) : Prop :=
  (∀ n < events.length, spend a r h (events.take n) < B) ∧ B < spend a r h events
def PreCoverage (events : List (TreeEvaluation Bool)) : Prop :=
  ∃ path ∈ terminals, ∀ e ∈ events, e.terminal ≠ path
def endpointNet (a r h lambda : ℝ) (run retained : List (TreeEvaluation Bool)) : ℝ :=
  AgentUCTBudgetP1V2.recommendedQuality retained - lambda * spend a r h run

theorem complete_budget (a r h B u delta good bad : ℝ)
    (ha : 0 ≤ a) (hr : 0 ≤ r) (hh : 0 < h)
    (hfit : 6*a+r+(r+a)+4*h < B) (hcross : B < 6*a+r+(r+a)+5*h) :
    FirstCompleteCrossing a r h B (completeTrace u delta good bad) ∧
    T_B a r h B (completeTrace u delta good bad) = 4 := by
  have h4 := complete_prefix_spend a r h u delta good bad 4 (by decide)
  have h5 := complete_prefix_spend a r h u delta good bad 5 (by decide)
  norm_num at h4 h5
  constructor
  · constructor
    · intro n hn
      have hn' : n < 5 := by simpa [completeTrace, AgentUCTBudgetP1V2.completeTrace,
        AgentUCTBudgetP1V2.initialization] using hn
      rw [complete_prefix_spend a r h u delta good bad n (by omega)]
      interval_cases n <;> norm_num <;> linarith
    · simpa only [List.take_length] using h5.symm ▸ hcross
  · change AgentUCTBudgetP1V2.lastAffordable _ B 5 = 4
    simp only [AgentUCTBudgetP1V2.lastAffordable]
    rw [h4,h5]
    simp [not_le.mpr hcross, hfit.le]

theorem short_budget (a r h B u delta good bad : ℝ)
    (ha : 0 ≤ a) (hr : 0 ≤ r) (hh : 0 < h)
    (hfit : 6*a+r+2*h < B) (hcross : B < 6*a+r+2*r+3*h) :
    FirstCompleteCrossing a r h B (shortTrace u delta good bad) ∧
    T_B a r h B (shortTrace u delta good bad) = 2 := by
  have h2 := short_prefix_spend a r h u delta good bad 2 (by decide)
  have h3 := short_prefix_spend a r h u delta good bad 3 (by decide)
  norm_num at h2 h3
  constructor
  · constructor
    · intro n hn
      have hn' : n < 3 := by simpa [shortTrace, AgentUCTBudgetP1V2.initialization] using hn
      rw [short_prefix_spend a r h u delta good bad n (by omega)]
      interval_cases n <;> norm_num <;> linarith
    · simpa only [List.take_length] using h3.symm ▸ hcross
  · change AgentUCTBudgetP1V2.lastAffordable _ B 3 = 2
    simp only [AgentUCTBudgetP1V2.lastAffordable]
    rw [h2,h3]
    simp [not_le.mpr hcross, hfit.le]

theorem precoverage (u delta good bad : ℝ) :
    PreCoverage ((completeTrace u delta good bad).take 4) ∧
    PreCoverage ((shortTrace u delta good bad).take 2) := by
  constructor <;> refine ⟨leaf true true, by simp [terminals], ?_⟩ <;>
    simp [completeTrace, AgentUCTBudgetP1V2.completeTrace, shortTrace,
      AgentUCTBudgetP1V2.initialization, AgentUCTBudgetP1V2.seedA, AgentUCTBudgetP1V2.seedB,
      AgentUCTBudgetP1V2.discoverA, AgentUCTBudgetP1V2.warmA, AgentUCTBudgetP1V2.replayA,
      AgentUCTBudgetP1V2.event, AgentUCTBudgetP1V2.leaf, leaf]

theorem best_before_crossing (u delta good bad : ℝ) (hd : 0 < delta) (hg : u+delta < good) :
    AgentUCTBudgetP1V2.recommendedQuality ((completeTrace u delta good bad).take 4) = good ∧
    AgentUCTBudgetP1V2.recommendedQuality ((shortTrace u delta good bad).take 2) = u+delta := by
  exact AgentUCTBudgetP1V2.best_before_crossing u delta good bad hd hg

theorem endpoint_gap (a r h lambda u delta good bad : ℝ) (hd : 0 < delta) (hg : u+delta < good) :
    endpointNet a r h lambda (completeTrace u delta good bad) ((completeTrace u delta good bad).take 4) -
      endpointNet a r h lambda (shortTrace u delta good bad) ((shortTrace u delta good bad).take 2) =
      good-(u+delta)+lambda*(r-a-2*h) := by
  obtain ⟨hA,hB⟩ := best_before_crossing u delta good bad hd hg
  have hCA := complete_prefix_spend a r h u delta good bad 5 (by decide)
  have hCB := short_prefix_spend a r h u delta good bad 3 (by decide)
  norm_num [completeTrace, AgentUCTBudgetP1V2.completeTrace, shortTrace,
    AgentUCTBudgetP1V2.initialization] at hCA hCB
  simp only [endpointNet, hA, hB]
  simp only [completeTrace, AgentUCTBudgetP1V2.completeTrace, shortTrace,
    AgentUCTBudgetP1V2.initialization, List.cons_append, List.nil_append]
  rw [hCA,hCB]
  ring

def liveNextPenalty (a r gamma : ℝ) (before : List (TreeEvaluation Bool)) (p : List Bool) (chosen : Bool) : ℝ :=
  gamma * ∑ path ∈ subtreeTerminals terminals (p ++ [chosen]),
    law before p chosen path * nextUnpaidBill (cache before) (defaultQuote a r before)
      (AgentUCTBudgetP1V2.orderedResources path)
theorem live_next_exact (a r gamma : ℝ) : liveNextPenalty a r gamma = nextPenalty a r gamma := by
  funext before p chosen
  have hprice : defaultQuote a r before = prices a r := funext (default_quote_exact a r before)
  simp only [liveNextPenalty, hprice, nextPenalty]

structure Separation (a r h B gamma c u delta good bad lambda : ℝ) : Prop where
  legalComplete : LegalTreeRun (fun p => p ∈ terminals) {[]} (completeTrace u delta good bad)
  legalNext : LegalTreeRun (fun p => p ∈ terminals) {[]} (shortTrace u delta good bad)
  liveCompleteAllocated : TreeAllocationRule terminals c (liveCompletePenalty a r gamma)
    (completeTrace u delta good bad)
  liveNextAllocated : TreeAllocationRule terminals c (liveNextPenalty a r gamma)
    (shortTrace u delta good bad)
  unpricedAllocated : TreeAllocationRule terminals c (fun _ _ _ => 0) (shortTrace u delta good bad)
  completeStops : FirstCompleteCrossing a r h B (completeTrace u delta good bad)
  nextStops : FirstCompleteCrossing a r h B (shortTrace u delta good bad)
  completeHorizon : T_B a r h B (completeTrace u delta good bad) = 4
  nextHorizon : T_B a r h B (shortTrace u delta good bad) = 2
  beforeCoverage : PreCoverage ((completeTrace u delta good bad).take 4) ∧
    PreCoverage ((shortTrace u delta good bad).take 2)
  qualityGap : AgentUCTBudgetP1V2.recommendedQuality ((shortTrace u delta good bad).take 2) <
    AgentUCTBudgetP1V2.recommendedQuality ((completeTrace u delta good bad).take 4)
  netGap : endpointNet a r h lambda (shortTrace u delta good bad) ((shortTrace u delta good bad).take 2) <
    endpointNet a r h lambda (completeTrace u delta good bad) ((completeTrace u delta good bad).take 4)




theorem default_mean_mc16_precoverage_separation (a r h B gamma c u delta good bad lambda : ℝ)
    (ha : 0 ≤ a) (hr : 0 < r) (hh : 0 < h) (hc : 0 < c)
    (hu : 0 ≤ u) (hg : 0 ≤ good) (hug : u+delta < good) (hu1 : u+delta ≤ 1)
    (hd : 0 < delta) (hlambda : 0 ≤ lambda)
    (hsplit : delta < gamma*((r-a)/4))
    (hwarm : 1+max (treeBonus c 3 1) (treeBonus c 4 1) < gamma*((2*r)/4))
    (hnet : 2*h ≤ r-a)
    (hfit : 6*a+r+(r+a)+4*h < B) (hcross : B < 6*a+r+(r+a)+5*h) :
    Separation a r h B gamma c u delta good bad lambda := by
  obtain ⟨hstopA,hTA⟩ := complete_budget a r h B u delta good bad ha hr.le hh hfit hcross
  obtain ⟨hstopB,hTB⟩ := short_budget a r h B u delta good bad ha hr.le hh (by linarith) (by linarith)
  obtain ⟨hQA,hQB⟩ := best_before_crossing u delta good bad hd hug
  have hJ := endpoint_gap a r h lambda u delta good bad hd hug
  have hcost := mul_nonneg hlambda (show 0 ≤ r-a-2*h by linarith)
  have halloc := complete_allocation a r gamma c u delta good bad hc.le hu hg
    (by linarith) hu1 hsplit hwarm
  have hnalloc := short_allocation a r gamma c u delta good bad hr hd.le
  rw [← live_penalty_exact] at halloc
  rw [← live_next_exact] at hnalloc
  exact {
    legalComplete := complete_legal u delta good bad
    legalNext := short_legal u delta good bad
    liveCompleteAllocated := halloc
    liveNextAllocated := hnalloc
    unpricedAllocated := unpriced_allocation c u delta good bad hd.le
    completeStops := hstopA
    nextStops := hstopB
    completeHorizon := hTA
    nextHorizon := hTB
    beforeCoverage := precoverage u delta good bad
    qualityGap := by rw [hQA,hQB]; exact hug
    netGap := by linarith
  }

theorem favorable_instance_c14 :
    Separation 1 4 1 (39/2) 2 (7/5) (2/5) (1/10) (9/10) (1/2) (1/20) := by
  apply default_mean_mc16_precoverage_separation 1 4 1 (39/2) 2 (7/5)
    (2/5) (1/10) (9/10) (1/2) (1/20) <;> norm_num
  have hx := AgentUCTBudgetP1V2.bonus_14_bound
  nlinarith

theorem next_after_B (a r gamma u delta good bad : ℝ) (hr : 0 < r) :
    nextPenalty a r gamma ((adverseTrace u delta good bad).take 3) [] false = gamma*(r/4) ∧
    nextPenalty a r gamma ((adverseTrace u delta good bad).take 3) [] true = 0 := by
  have hwA : sampledLaw 16 (sample16 false) [false,true,false] = 1/4 := by
    simpa [leaf] using sample16_weights false true
  simp +decide [nextPenalty, cache, replayPublished, publishComplete,
    AgentUCTBudgetP1V2.initialCaches, adverseTrace, AgentUCTBudgetP1V2.initialization,
    AgentUCTBudgetP1V2.seedA, AgentUCTBudgetP1V2.seedB, discoverB, warmB,
    AgentUCTBudgetP1V2.warmB, AgentUCTBudgetP1V2.event, AgentUCTBudgetP1V2.leaf,
    law, terminals, subtreeTerminals, leaf, hwA, AgentUCTBudgetP1V2.orderedResources,
    AgentUCTBudgetP1V2.executionRoot, panelDemand, AgentUCTBudgetP1V2.qids,
    executionPrefixes, show (Finset.Icc 1 4 : Finset ℕ) = {1,2,3,4} from by decide,
    prices, actionPrice, nextUnpaidBill, List.range_succ, Finset.filter_insert,
    Finset.filter_singleton, Finset.sum_insert, not_le.mpr hr]
  apply Or.inl
  ring

theorem next_root_warm (a r gamma c u delta good bad : ℝ)
    (hr : 0 < r) (hc : 0 ≤ c) (hu : u ≤ 1) (hd : 0 ≤ u+delta) (hb : 0 ≤ bad)
    (hwarm : 1+treeBonus c 3 1 < gamma*(r/4)) :
    AgentUCTBudgetP1V2.RootMax c (nextPenalty a r gamma)
      ((adverseTrace u delta good bad).take 3) true := by
  obtain ⟨ha,hb'⟩ := next_after_B a r gamma u delta good bad hr
  intro chosen
  cases chosen
  · simp [adverseTrace, AgentUCTBudgetP1V2.initialization, AgentUCTBudgetP1V2.seedA,
      AgentUCTBudgetP1V2.seedB, discoverB, warmB, AgentUCTBudgetP1V2.warmB,
      AgentUCTBudgetP1V2.event, AgentUCTBudgetP1V2.reward, AgentUCTBudgetP1V2.leaf] at ha hb'
    have hB := treeBonus_nonnegative hc 3 2
    simp [adverseTrace, AgentUCTBudgetP1V2.initialization, AgentUCTBudgetP1V2.seedA,
      AgentUCTBudgetP1V2.seedB, discoverB, warmB, AgentUCTBudgetP1V2.warmB,
      AgentUCTBudgetP1V2.event, replayBackup, backupEvent, emptyStatistics,
      BackupStat.mean, AgentUCTBudgetP1V2.reward, AgentUCTBudgetP1V2.leaf, treeIndex, ha, hb']
    nlinarith
  · exact le_refl _

theorem warmB_local (c : ℝ) (penalty) (u delta good bad : ℝ)
    (hroot : AgentUCTBudgetP1V2.RootMax c penalty ((adverseTrace u delta good bad).take 3) true) :
    LocalRule c penalty ((adverseTrace u delta good bad).take 3) (warmB u delta good bad) := by
  intro p chosen hp
  rcases AgentUCTBudgetP1V2.parents2 p chosen true false hp with ⟨rfl,rfl⟩ | ⟨rfl,rfl⟩
  · constructor
    · intro b hb hz
      cases b <;> simp [adverseTrace, AgentUCTBudgetP1V2.initialization,
        AgentUCTBudgetP1V2.seedA, AgentUCTBudgetP1V2.seedB, discoverB, warmB,
        AgentUCTBudgetP1V2.warmB, AgentUCTBudgetP1V2.event,
        replayBackup, backupEvent, emptyStatistics] at hz
    · intro h b hb; exact hroot b
  · constructor
    · intro b hb hz
      simp [adverseTrace, AgentUCTBudgetP1V2.initialization, AgentUCTBudgetP1V2.seedA,
        AgentUCTBudgetP1V2.seedB, discoverB, warmB, AgentUCTBudgetP1V2.warmB,
        AgentUCTBudgetP1V2.event, replayBackup, backupEvent, emptyStatistics]
    · intro h
      have hh := h false (by simp [availableChildren, terminals, leaf, childAfter])
      simp [adverseTrace, AgentUCTBudgetP1V2.initialization, AgentUCTBudgetP1V2.seedA,
        AgentUCTBudgetP1V2.seedB, discoverB, warmB, AgentUCTBudgetP1V2.warmB,
        AgentUCTBudgetP1V2.event, replayBackup, backupEvent, emptyStatistics] at hh

theorem adverse_allocation (a r gamma c u delta good bad : ℝ)
    (hr : 0 < r) (hc : 0 ≤ c) (hu : u ≤ 1) (hd0 : 0 ≤ delta) (hd : 0 ≤ u+delta) (hb : 0 ≤ bad)
    (hwarm : 1+treeBonus c 3 1 < gamma*(r/4)) :
    TreeAllocationRule terminals c (nextPenalty a r gamma) (adverseTrace u delta good bad) := by
  apply allocation_from_local
  intro n hn
  have hn' : n < 4 := by simpa [adverseTrace, AgentUCTBudgetP1V2.initialization] using hn
  interval_cases n
  · apply transfer_local
    · exact shallow_event_children (AgentUCTBudgetP1V2.seedA u delta good bad)
        (by norm_num [AgentUCTBudgetP1V2.seedA, AgentUCTBudgetP1V2.event])
    · exact AgentUCTBudgetP1V2.seedA_local c _ u delta good bad
  · apply transfer_local
    · exact shallow_event_children (AgentUCTBudgetP1V2.seedB u delta good bad)
        (by norm_num [AgentUCTBudgetP1V2.seedB, AgentUCTBudgetP1V2.event])
    · exact AgentUCTBudgetP1V2.seedB_local c _ u delta good bad
  · change LocalRule c (nextPenalty a r gamma) (AgentUCTBudgetP1V2.initialization u delta good bad)
      (AgentUCTBudgetP1V2.discoverB u delta good bad)
    apply transfer_local
    · exact shallow_event_children (AgentUCTBudgetP1V2.discoverB u delta good bad)
        (by norm_num [AgentUCTBudgetP1V2.discoverB, AgentUCTBudgetP1V2.event])
    · exact AgentUCTBudgetP1V2.discover_local c _ u delta good bad true
        (next_root_initial a r gamma c u delta good bad hr hd0)
  · exact warmB_local c _ u delta good bad
      (next_root_warm a r gamma c u delta good bad hr hc hu hd hb hwarm)

theorem adverse_budget (a r h B u delta good bad : ℝ)
    (ha : 0 ≤ a) (hr : 0 ≤ r) (hh : 0 < h)
    (hfit : 6*a+r+2*r+3*h < B) (hcross : B < 6*a+r+2*r+4*h) :
    FirstCompleteCrossing a r h B (adverseTrace u delta good bad) ∧
    T_B a r h B (adverseTrace u delta good bad) = 3 := by
  have h3 := adverse_prefix_spend a r h u delta good bad 3 (by decide)
  have h4 := adverse_prefix_spend a r h u delta good bad 4 (by decide)
  norm_num at h3 h4
  constructor
  · constructor
    · intro n hn
      have hn' : n < 4 := by simpa [adverseTrace, AgentUCTBudgetP1V2.initialization] using hn
      rw [adverse_prefix_spend a r h u delta good bad n (by omega)]
      interval_cases n <;> norm_num <;> linarith
    · simpa only [List.take_length] using h4.symm ▸ hcross
  · change AgentUCTBudgetP1V2.lastAffordable _ B 4 = 3
    simp only [AgentUCTBudgetP1V2.lastAffordable]
    rw [h3,h4]
    simp [not_le.mpr hcross, hfit.le]

theorem adverse_best (u delta bad : ℝ) (hd : 0 < delta) (hb : u+delta < bad) :
    AgentUCTBudgetP1V2.recommendedQuality ((completeTrace u delta u bad).take 4) = u+delta ∧
    AgentUCTBudgetP1V2.recommendedQuality ((adverseTrace u delta u bad).take 3) = bad := by
  have hu : u < u+delta := by linarith
  have hn : ¬u+delta < u := by linarith
  simp [AgentUCTBudgetP1V2.recommendedQuality, bestCompleted, bestFrom, keepBest,
    completeTrace, AgentUCTBudgetP1V2.completeTrace, adverseTrace,
    AgentUCTBudgetP1V2.initialization, AgentUCTBudgetP1V2.seedA, AgentUCTBudgetP1V2.seedB,
    AgentUCTBudgetP1V2.discoverA, discoverB, AgentUCTBudgetP1V2.warmA, warmB,
    AgentUCTBudgetP1V2.warmB, AgentUCTBudgetP1V2.replayA, AgentUCTBudgetP1V2.event,
    AgentUCTBudgetP1V2.reward, AgentUCTBudgetP1V2.leaf, hu, hn, hb]

theorem adverse_endpoint_gap (a r h lambda u delta bad : ℝ) (hd : 0 < delta) (hb : u+delta < bad) :
    endpointNet a r h lambda (adverseTrace u delta u bad) ((adverseTrace u delta u bad).take 3) -
      endpointNet a r h lambda (completeTrace u delta u bad) ((completeTrace u delta u bad).take 4) =
      bad-(u+delta)-lambda*(r-a-h) := by
  obtain ⟨hA,hB⟩ := adverse_best u delta bad hd hb
  have hCA := complete_prefix_spend a r h u delta u bad 5 (by decide)
  have hCB := adverse_prefix_spend a r h u delta u bad 4 (by decide)
  norm_num [completeTrace, AgentUCTBudgetP1V2.completeTrace, adverseTrace,
    AgentUCTBudgetP1V2.initialization] at hCA hCB
  simp only [endpointNet, hA, hB]
  simp only [completeTrace, AgentUCTBudgetP1V2.completeTrace, adverseTrace,
    AgentUCTBudgetP1V2.initialization, List.cons_append, List.nil_append]
  rw [hCA,hCB]
  ring

structure Reversal (a r h B gamma c u delta bad lambda : ℝ) : Prop where
  legalComplete : LegalTreeRun (fun p => p ∈ terminals) {[]} (completeTrace u delta u bad)
  legalNext : LegalTreeRun (fun p => p ∈ terminals) {[]} (adverseTrace u delta u bad)
  completeAllocated : TreeAllocationRule terminals c (liveCompletePenalty a r gamma) (completeTrace u delta u bad)
  nextAllocated : TreeAllocationRule terminals c (liveNextPenalty a r gamma) (adverseTrace u delta u bad)
  completeStops : FirstCompleteCrossing a r h B (completeTrace u delta u bad)
  nextStops : FirstCompleteCrossing a r h B (adverseTrace u delta u bad)
  completeHorizon : T_B a r h B (completeTrace u delta u bad) = 4
  nextHorizon : T_B a r h B (adverseTrace u delta u bad) = 3
  beforeCoverage : PreCoverage ((completeTrace u delta u bad).take 4) ∧
    PreCoverage ((adverseTrace u delta u bad).take 3)
  reversedQuality : AgentUCTBudgetP1V2.recommendedQuality ((completeTrace u delta u bad).take 4) <
    AgentUCTBudgetP1V2.recommendedQuality ((adverseTrace u delta u bad).take 3)
  reversedNet : endpointNet a r h lambda (completeTrace u delta u bad) ((completeTrace u delta u bad).take 4) <
    endpointNet a r h lambda (adverseTrace u delta u bad) ((adverseTrace u delta u bad).take 3)

theorem default_mean_mc16_precoverage_reversal (a r h B gamma c u delta bad lambda : ℝ)
    (ha : 0 ≤ a) (hr : 0 < r) (hh : 0 < h) (hc : 0 < c) (hu : 0 ≤ u) (hu1 : u+delta ≤ 1)
    (hd : 0 < delta) (hb0 : 0 ≤ bad) (hb : u+delta < bad)
    (hsplit : delta < gamma*((r-a)/4))
    (hwarm : 1+max (treeBonus c 3 1) (treeBonus c 4 1) < gamma*((2*r)/4))
    (hnwarm : 1+treeBonus c 3 1 < gamma*(r/4))
    (htail : h ≤ r-a) (hBfit : 6*a+r+2*r+3*h < B) (hBcross : B < 6*a+r+(r+a)+5*h)
    (hnet : lambda*(r-a-h) < bad-(u+delta)) :
    Reversal a r h B gamma c u delta bad lambda := by
  obtain ⟨hstopA,hTA⟩ := complete_budget a r h B u delta u bad ha hr.le hh (by linarith) hBcross
  obtain ⟨hstopB,hTB⟩ := adverse_budget a r h B u delta u bad ha hr.le hh hBfit (by linarith)
  obtain ⟨hQA,hQB⟩ := adverse_best u delta bad hd hb
  have hJ := adverse_endpoint_gap a r h lambda u delta bad hd hb
  have halloc := complete_allocation a r gamma c u delta u bad hc.le hu hu (le_refl _) hu1 hsplit hwarm
  have hnalloc := adverse_allocation a r gamma c u delta u bad hr hc.le (by linarith) hd.le (by linarith) hb0 hnwarm
  rw [←live_penalty_exact] at halloc
  rw [←live_next_exact] at hnalloc
  have hpreB : PreCoverage ((adverseTrace u delta u bad).take 3) := by
    refine ⟨leaf false true, by simp [terminals], ?_⟩
    simp [adverseTrace, AgentUCTBudgetP1V2.initialization, AgentUCTBudgetP1V2.seedA,
      AgentUCTBudgetP1V2.seedB, discoverB, warmB, AgentUCTBudgetP1V2.warmB,
      AgentUCTBudgetP1V2.event, AgentUCTBudgetP1V2.leaf, leaf]
  exact {
    legalComplete := complete_legal u delta u bad
    legalNext := adverse_legal u delta u bad
    completeAllocated := halloc
    nextAllocated := hnalloc
    completeStops := hstopA
    nextStops := hstopB
    completeHorizon := hTA
    nextHorizon := hTB
    beforeCoverage := ⟨(precoverage u delta u bad).1,hpreB⟩
    reversedQuality := by rw [hQA,hQB]; exact hb
    reversedNet := by linarith
  }

theorem adverse_instance_c14 :
    Reversal 1 (5/2) 1 (67/4) 10 (7/5) (1/4) (1/4) 1 (1/20) := by
  apply default_mean_mc16_precoverage_reversal 1 (5/2) 1 (67/4) 10 (7/5)
    (1/4) (1/4) 1 (1/20) <;> norm_num
  · have hx := AgentUCTBudgetP1V2.bonus_14_bound
    nlinarith
  · have hx := (le_max_left (treeBonus (7/5) 3 1) (treeBonus (7/5) 4 1)).trans
      AgentUCTBudgetP1V2.bonus_14_bound
    nlinarith

theorem sampled_event_probability_positive (before : List (TreeEvaluation Bool)) (branch : Bool) :
    0 < ∏ i : Fin 16, smoothedProbability before [branch] (decide (12 ≤ i.val)) := by
  exact Finset.prod_pos (fun i _ => smoothed_probability_positive _ _ _)

theorem initial_reference_error_zero (u delta good bad : ℝ) (branch hidden : Bool) :
    |sampledLaw 16 (sample16 branch) (leaf branch hidden) -
      smoothedProbability (AgentUCTBudgetP1V2.initialization u delta good bad) [branch] hidden| = 0 := by
  obtain ⟨ht,hf⟩ := historical_initial_hidden_mass u delta good bad branch
  cases hidden <;> simp [sample16_weights, ht, hf]




theorem singleton_mc16_law (before : List (TreeEvaluation Bool)) (branch hidden : Bool)
    (path : List Bool) (hp : path ∈ subtreeTerminals terminals ([branch] ++ [hidden])) :
    law before [branch] hidden path = sampledLaw 16 (fun _ : Fin 16 => leaf branch hidden) path := by
  obtain ⟨ht,hpre⟩ := mem_filter.mp hp
  simp only [terminals,mem_insert,mem_singleton] at ht
  rcases ht with rfl | rfl | rfl | rfl
  all_goals cases branch <;> cases hidden <;> simp [leaf] at hpre <;>
    norm_num [law, uniformTerminalLaw, subtreeTerminals, terminals, leaf,
      sampledLaw, Fin.sum_univ_succ] <;> decide

theorem physical_prices_nonnegative (a r : ℝ) (ha : 0 ≤ a) (hr : 0 ≤ r) :
    ∀ resource, 0 ≤ prices a r resource := by
  intro resource
  unfold prices
  cases resource.2.getLast? with
  | none => positivity
  | some action => cases action <;> simp [actionPrice, ha, hr]

theorem fixed_rewards_unit_interval (u delta good bad : ℝ)
    (hu : 0 ≤ u) (hd : 0 ≤ delta) (hs : u+delta ≤ 1)
    (hg0 : 0 ≤ good) (hg1 : good ≤ 1) (hb0 : 0 ≤ bad) (hb1 : bad ≤ 1) :
    ∀ path ∈ terminals, 0 ≤ reward u delta good bad path ∧ reward u delta good bad path ≤ 1 := by
  intro path ht
  simp only [terminals, mem_insert, mem_singleton] at ht
  rcases ht with rfl | rfl | rfl | rfl <;>
    simp [reward, leaf, AgentUCTBudgetP1V2.reward, AgentUCTBudgetP1V2.leaf] <;>
    constructor <;> linarith

theorem fixed_table_traces (u delta good bad : ℝ) :
    FixedTableEvents terminals (reward u delta good bad) (completeTrace u delta good bad) ∧
    FixedTableEvents terminals (reward u delta good bad) (shortTrace u delta good bad) ∧
    FixedTableEvents terminals (reward u delta good bad) (adverseTrace u delta good bad) := by
  constructor
  · intro e he
    simp [completeTrace, AgentUCTBudgetP1V2.completeTrace, AgentUCTBudgetP1V2.initialization] at he
    rcases he with rfl | rfl | rfl | rfl | rfl <;>
      simp [AgentUCTBudgetP1V2.seedA, AgentUCTBudgetP1V2.seedB, AgentUCTBudgetP1V2.discoverA,
        AgentUCTBudgetP1V2.warmA, AgentUCTBudgetP1V2.replayA, AgentUCTBudgetP1V2.event,
        terminals, reward, leaf, AgentUCTBudgetP1V2.reward, AgentUCTBudgetP1V2.leaf]
  constructor
  · intro e he
    simp [shortTrace, AgentUCTBudgetP1V2.initialization] at he
    rcases he with rfl | rfl | rfl <;>
      simp [AgentUCTBudgetP1V2.seedA, AgentUCTBudgetP1V2.seedB, discoverB,
        AgentUCTBudgetP1V2.event, terminals, reward, leaf, AgentUCTBudgetP1V2.reward,
        AgentUCTBudgetP1V2.leaf]
  · intro e he
    simp [adverseTrace, AgentUCTBudgetP1V2.initialization] at he
    rcases he with rfl | rfl | rfl | rfl <;>
      simp [AgentUCTBudgetP1V2.seedA, AgentUCTBudgetP1V2.seedB, discoverB, warmB,
        AgentUCTBudgetP1V2.warmB, AgentUCTBudgetP1V2.event, terminals, reward, leaf,
        AgentUCTBudgetP1V2.reward, AgentUCTBudgetP1V2.leaf]

theorem terminals_antichain : ∀ p ∈ terminals, ∀ q ∈ terminals, p <+: q → p=q := by
  simp +decide [terminals,leaf]

theorem subtree_value_of_max (p winner : List Bool) (u delta good bad : ℝ)
    (hw : winner ∈ terminals) (hp : p <+: winner)
    (hmax : ∀ path ∈ terminals, p <+: path → reward u delta good bad path ≤ reward u delta good bad winner) :
    subtreeValue terminals (reward u delta good bad) p = reward u delta good bad winner := by
  have hn : (subtreeTerminals terminals p).Nonempty := ⟨winner,mem_filter.mpr ⟨hw,hp⟩⟩
  obtain ⟨path,ht,hpre,hv⟩ := subtreeValue_attained terminals (reward u delta good bad) p hn
  exact le_antisymm (hv ▸ hmax path ht hpre)
    (subtreeValue_upper terminals (reward u delta good bad) p winner hw hp)

theorem favorable_branch_values (u delta good bad : ℝ)
    (hd : 0 ≤ delta) (hg : u+delta ≤ good) (hb : bad ≤ u+delta) :
    subtreeValue terminals (reward u delta good bad) [false] = good ∧
    subtreeValue terminals (reward u delta good bad) [true] = u+delta ∧
    subtreeValue terminals (reward u delta good bad) [] = good := by
  constructor
  · have h := subtree_value_of_max [false] (leaf false true) u delta good bad
      (by simp [terminals]) (by simp [leaf])
    simp [reward,leaf,AgentUCTBudgetP1V2.reward,AgentUCTBudgetP1V2.leaf] at h
    apply h
    intro path ht hp
    simp only [terminals,mem_insert,mem_singleton] at ht
    rcases ht with rfl | rfl | rfl | rfl <;>
      simp [leaf, reward, AgentUCTBudgetP1V2.reward,AgentUCTBudgetP1V2.leaf] at hp ⊢ <;> linarith
  constructor
  · have h := subtree_value_of_max [true] (leaf true false) u delta good bad
      (by simp [terminals]) (by simp [leaf])
    simp [reward,leaf,AgentUCTBudgetP1V2.reward,AgentUCTBudgetP1V2.leaf] at h
    apply h
    intro path ht hp
    simp only [terminals,mem_insert,mem_singleton] at ht
    rcases ht with rfl | rfl | rfl | rfl <;>
      simp [leaf, reward, AgentUCTBudgetP1V2.reward,AgentUCTBudgetP1V2.leaf] at hp ⊢ <;> linarith
  · have h := subtree_value_of_max [] (leaf false true) u delta good bad
      (by simp [terminals]) List.nil_prefix
    simp [reward,leaf,AgentUCTBudgetP1V2.reward,AgentUCTBudgetP1V2.leaf] at h
    apply h
    intro path ht
    simp only [terminals,mem_insert,mem_singleton] at ht
    rcases ht with rfl | rfl | rfl | rfl <;>
      simp [leaf, reward, AgentUCTBudgetP1V2.reward,AgentUCTBudgetP1V2.leaf] <;> linarith

theorem separation_attains_true_optimum (a r h B gamma c u delta good bad lambda : ℝ)
    (hsep : Separation a r h B gamma c u delta good bad lambda)
    (hd : 0 < delta) (hg : u+delta < good) (hb : bad ≤ u+delta) :
    AgentUCTBudgetP1V2.recommendedQuality ((completeTrace u delta good bad).take
      (T_B a r h B (completeTrace u delta good bad))) = subtreeValue terminals (reward u delta good bad) [] ∧
    subtreeValue terminals (reward u delta good bad) [] -
      AgentUCTBudgetP1V2.recommendedQuality ((shortTrace u delta good bad).take
        (T_B a r h B (shortTrace u delta good bad))) = good-(u+delta) ∧
    subtreeValue terminals (reward u delta good bad) [false] -
      subtreeValue terminals (reward u delta good bad) [true] = good-(u+delta) := by
  obtain ⟨hA,hB,hV⟩ := favorable_branch_values u delta good bad hd.le hg.le hb
  obtain ⟨hQA,hQB⟩ := best_before_crossing u delta good bad hd hg
  rw [hsep.completeHorizon,hsep.nextHorizon,hQA,hQB,hA,hB,hV]
  exact ⟨rfl,rfl,rfl⟩

theorem favorable_instance_optimal :
    AgentUCTBudgetP1V2.recommendedQuality ((completeTrace (2/5) (1/10) (9/10) (1/2)).take 4) =
      subtreeValue terminals (reward (2/5) (1/10) (9/10) (1/2)) [] ∧
    subtreeValue terminals (reward (2/5) (1/10) (9/10) (1/2)) [] -
      AgentUCTBudgetP1V2.recommendedQuality ((shortTrace (2/5) (1/10) (9/10) (1/2)).take 2) = 2/5 := by
  have hx := separation_attains_true_optimum 1 4 1 (39/2) 2 (7/5) (2/5) (1/10) (9/10) (1/2) (1/20)
    favorable_instance_c14 (by norm_num) (by norm_num) (by norm_num)
  rw [favorable_instance_c14.completeHorizon,favorable_instance_c14.nextHorizon] at hx
  norm_num at hx
  exact ⟨hx.1,hx.2.1⟩

theorem favorable_instance_reward_bounds : ∀ path ∈ terminals,
    0 ≤ reward (2/5) (1/10) (9/10) (1/2) path ∧ reward (2/5) (1/10) (9/10) (1/2) path ≤ 1 := by
  apply fixed_rewards_unit_interval <;> norm_num
theorem adverse_instance_reward_bounds : ∀ path ∈ terminals,
    0 ≤ reward (1/4) (1/4) (1/4) 1 path ∧ reward (1/4) (1/4) (1/4) 1 path ≤ 1 := by
  apply fixed_rewards_unit_interval <;> norm_num

theorem favorable_instance_net_gap :
    endpointNet 1 4 1 (1/20) (completeTrace (2/5) (1/10) (9/10) (1/2))
      ((completeTrace (2/5) (1/10) (9/10) (1/2)).take 4) -
    endpointNet 1 4 1 (1/20) (shortTrace (2/5) (1/10) (9/10) (1/2))
      ((shortTrace (2/5) (1/10) (9/10) (1/2)).take 2) = 9/20 := by
  rw [endpoint_gap 1 4 1 (1/20) (2/5) (1/10) (9/10) (1/2) (by norm_num) (by norm_num)]
  norm_num
theorem adverse_instance_net_gap :
    endpointNet 1 (5/2) 1 (1/20) (adverseTrace (1/4) (1/4) (1/4) 1)
      ((adverseTrace (1/4) (1/4) (1/4) 1).take 3) -
    endpointNet 1 (5/2) 1 (1/20) (completeTrace (1/4) (1/4) (1/4) 1)
      ((completeTrace (1/4) (1/4) (1/4) 1).take 4) = 19/40 := by
  rw [adverse_endpoint_gap 1 (5/2) 1 (1/20) (1/4) (1/4) 1 (by norm_num) (by norm_num)]
  norm_num

theorem adverse_global_value (u delta bad : ℝ) (hd : 0 ≤ delta) (hb : u+delta ≤ bad) :
    subtreeValue terminals (reward u delta u bad) [] = bad := by
  have h := subtree_value_of_max [] (leaf true true) u delta u bad
    (by simp [terminals]) List.nil_prefix
  simp [reward,leaf,AgentUCTBudgetP1V2.reward,AgentUCTBudgetP1V2.leaf] at h
  apply h
  intro path ht
  simp only [terminals,mem_insert,mem_singleton] at ht
  rcases ht with rfl | rfl | rfl | rfl <;>
    simp [leaf,reward,AgentUCTBudgetP1V2.reward,AgentUCTBudgetP1V2.leaf] <;> linarith

theorem adverse_instance_optimal :
    AgentUCTBudgetP1V2.recommendedQuality ((adverseTrace (1/4) (1/4) (1/4) 1).take 3) =
      subtreeValue terminals (reward (1/4) (1/4) (1/4) 1) [] ∧
    subtreeValue terminals (reward (1/4) (1/4) (1/4) 1) [] -
      AgentUCTBudgetP1V2.recommendedQuality ((completeTrace (1/4) (1/4) (1/4) 1).take 4) = 1/2 := by
  obtain ⟨hA,hB⟩ := adverse_best (1/4) (1/4) 1 (by norm_num) (by norm_num)
  rw [adverse_global_value (1/4) (1/4) 1 (by norm_num) (by norm_num),hA,hB]
  norm_num

end AgentUCTDefaultBudgetP1V2
