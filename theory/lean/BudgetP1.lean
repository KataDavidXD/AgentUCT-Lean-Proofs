import AgentUCTPaper.TreeObjectives
import AgentUCTPaper.OnlineMean







set_option autoImplicit false
set_option maxRecDepth 4096
set_option maxHeartbeats 1000000
noncomputable section

namespace AgentUCTBudgetP1V2
open AgentUCTPaper Finset

abbrev Resource := Unit × List Bool
def leaf (branch hidden : Bool) : List Bool := [branch, hidden, false]
def terminals : Finset (List Bool) :=
  {leaf false false, leaf false true, leaf true false, leaf true true}
def qids : Finset Unit := {()}
def executionRoot : List Bool := [false]
def demand (branch hidden : Bool) : Finset Resource :=
  panelDemand qids (executionRoot ++ leaf branch hidden)
def initialCaches : PersistentCaches Unit Bool := ⟨∅, ∅⟩
def initialMeter : MeteredTreeState Unit Bool := ⟨emptyStatistics, ∅, 0, 0⟩



def prices (s r a b : ℝ) (resource : Resource) : ℝ :=
  if resource.2 = [false] then s else
  if resource.2 = [false, false, true] ∨ resource.2 = [false, true, true] then r else
  if resource.2 = [false, false, true, false] then a else
  if resource.2 = [false, true, true, false] then b else 0

def reward (u delta good bad : ℝ) (path : List Bool) : ℝ :=
  if path = leaf false true then good else
  if path = leaf true true then bad else
  if path = leaf true false then u + delta else u

def event (expanded : List Bool) (branch hidden : Bool) (u delta good bad : ℝ)
    (hp : expanded <+: leaf branch hidden) : TreeEvaluation Bool :=
  ⟨expanded, leaf branch hidden, reward u delta good bad (leaf branch hidden), 0, hp⟩
def seedA (u delta good bad : ℝ) := event [false] false false u delta good bad (by simp [leaf])
def seedB (u delta good bad : ℝ) := event [true] true false u delta good bad (by simp [leaf])
def discoverA (u delta good bad : ℝ) :=
  event [false, true] false true u delta good bad (by simp [leaf])
def discoverB (u delta good bad : ℝ) :=
  event [true, true] true true u delta good bad (by simp [leaf])
def warmA (u delta good bad : ℝ) :=
  event [false, false] false false u delta good bad (by simp [leaf])
def replayA (u delta good bad : ℝ) :=
  event (leaf false true) false true u delta good bad (List.prefix_refl _)
def initialization (u delta good bad : ℝ) := [seedA u delta good bad, seedB u delta good bad]
def completeTrace (u delta good bad : ℝ) :=
  initialization u delta good bad ++
    [discoverA u delta good bad, warmA u delta good bad, replayA u delta good bad]
def shortTrace (u delta good bad : ℝ) :=
  initialization u delta good bad ++ [discoverB u delta good bad]

def cache (events : List (TreeEvaluation Bool)) : Finset Resource :=
  (replayPublished qids (fun x => executionRoot ++ x) events initialCaches).restorable
def spend (s r a b h : ℝ) (events : List (TreeEvaluation Bool)) : ℝ :=
  meteredSearchCost qids executionRoot (prices s r a b) (fun _ => h) events initialMeter

theorem demand_explicit (branch hidden : Bool) :
    demand branch hidden =
      {((), [false]), ((), [false, branch]), ((), [false, branch, hidden]),
        ((), [false, branch, hidden, false])} := by
  have hI : (Finset.Icc 1 4 : Finset ℕ) = {1, 2, 3, 4} := by decide
  cases branch <;> cases hidden <;>
    norm_num [demand, panelDemand, qids, executionRoot, leaf, executionPrefixes, hI]

theorem initialization_cache (u delta good bad : ℝ) :
    cache (initialization u delta good bad) = demand false false ∪ demand true false := by
  simp [cache, initialization, seedA, seedB, event, replayPublished, publishComplete,
    initialCaches, demand, List.foldl, Finset.union_assoc]

theorem initialization_cold (s r a b u delta good bad : ℝ) :
    coldWork (prices s r a b) (cache (initialization u delta good bad)) (demand false true) = r + a ∧
    coldWork (prices s r a b) (cache (initialization u delta good bad)) (demand true true) = r + b := by
  rw [initialization_cache]
  simp +decide [demand_explicit, coldWork, prices, Finset.sum_insert, Finset.sdiff_eq_filter,
    Finset.filter_insert, Finset.filter_singleton]

theorem initialization_spend (s r a b h u delta good bad : ℝ) :
    spend s r a b h (initialization u delta good bad) = s + 2 * h := by
  have hI : (Finset.Icc 1 4 : Finset ℕ) = {1, 2, 3, 4} := by decide
  simp +decide [spend, meteredSearchCost, replayMetered, meterStep, initialMeter,
    MeteredTreeState.totalPaid, initialization, seedA, seedB, event, List.foldl,
    panelDemand, qids, executionRoot, leaf, executionPrefixes, hI,
    coldWork, prices, Finset.sdiff_eq_filter, Finset.filter_insert, Finset.filter_singleton,
    Finset.sum_insert]
  ring

def law (_before : List (TreeEvaluation Bool)) (p : List Bool) (a : Bool) :=
  uniformTerminalLaw terminals (p ++ [a])
def completePenalty (s r a b gamma : ℝ) :=
  coldForecastPenalty qids executionRoot terminals (prices s r a b) gamma law initialCaches
def orderedResources (path : List Bool) : List Resource :=
  (List.range (executionRoot ++ path).length).map
    (fun i => ((), (executionRoot ++ path).take (i + 1)))
def nextPenalty (s r a b gamma : ℝ) (before : List (TreeEvaluation Bool))
    (p : List Bool) (chosen : Bool) : ℝ :=
  gamma * ∑ path ∈ subtreeTerminals terminals (p ++ [chosen]),
    law before p chosen path * nextUnpaidBill (cache before) (prices s r a b) (orderedResources path)

theorem shared_overlap (branch : Bool) :
    demand branch false ∩ demand branch true = {((), [false]), ((), [false, branch])} := by
  cases branch <;> ext resource <;> simp +decide [demand_explicit] <;> tauto

theorem complete_forecasts_initial (s r a b gamma u delta good bad : ℝ) :
    completePenalty s r a b gamma (initialization u delta good bad) [] false = gamma * ((r + a) / 2) ∧
    completePenalty s r a b gamma (initialization u delta good bad) [] true = gamma * ((r + b) / 2) := by
  unfold completePenalty coldForecastPenalty
  change gamma * referenceColdCost qids executionRoot terminals (prices s r a b)
    (law (initialization u delta good bad) [] false)
    (cache (initialization u delta good bad)) [false] = _ ∧
    gamma * referenceColdCost qids executionRoot terminals (prices s r a b)
    (law (initialization u delta good bad) [] true)
    (cache (initialization u delta good bad)) [true] = _
  rw [initialization_cache]
  have hI : (Finset.Icc 1 4 : Finset ℕ) = {1, 2, 3, 4} := by decide
  simp +decide [referenceColdCost, uniformTerminalLaw, law, terminals, subtreeTerminals,
    leaf, panelDemand, executionRoot, qids, executionPrefixes, hI,
    coldWork, demand_explicit, prices, Finset.sdiff_eq_filter,
    Finset.filter_insert, Finset.filter_singleton, Finset.sum_insert]
  constructor <;> (apply Or.inl; ring)

theorem next_forecasts_initial (s r a b gamma u delta good bad : ℝ) (hr : 0 < r) :
    nextPenalty s r a b gamma (initialization u delta good bad) [] false = gamma * (r / 2) ∧
    nextPenalty s r a b gamma (initialization u delta good bad) [] true = gamma * (r / 2) := by
  rw [nextPenalty, nextPenalty, initialization_cache]
  simp +decide [uniformTerminalLaw, law, terminals, subtreeTerminals, leaf,
    orderedResources, executionRoot, demand_explicit, prices, nextUnpaidBill,
    List.range_succ, Finset.filter_insert, Finset.filter_singleton, Finset.sum_insert,
    not_le.mpr hr]
  constructor <;> first | ring | (apply Or.inl; ring)

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

theorem allocation_from_local (c : ℝ) (penalty)
    (events : List (TreeEvaluation Bool))
    (hs : ∀ n (hn : n < events.length), LocalRule c penalty (events.take n) events[n]) :
    TreeAllocationRule terminals c penalty events := by
  intro before e after he p a hp
  have hn : before.length < events.length := by simp [he]
  have hs' := hs before.length hn
  have ht : events.take before.length = before := by simp [he]
  have hg : events[before.length] = e := by simp [he]
  rw [ht, hg] at hs'
  exact hs' p a hp

theorem complete_legal (u delta good bad : ℝ) :
    LegalTreeRun (fun p => p ∈ terminals) {[]} (completeTrace u delta good bad) := by
  simp +decide [completeTrace, initialization, seedA, seedB, discoverA, warmA, replayA,
    event, LegalTreeRun, LegalTreeEvent, growTree, terminals, leaf]

theorem short_legal (u delta good bad : ℝ) :
    LegalTreeRun (fun p => p ∈ terminals) {[]} (shortTrace u delta good bad) := by
  simp +decide [shortTrace, initialization, seedA, seedB, discoverB,
    event, LegalTreeRun, LegalTreeEvent, growTree, terminals, leaf]

theorem parents1 (p : List Bool) (a b : Bool) (hp : childAfter p [b] = some a) :
    p = [] ∧ a = b := by
  cases p with
  | nil => simpa [childAfter] using hp.symm
  | cons x xs =>
    have hpre := (childAfter_some_iff (x :: xs) [b] a).mp hp
    have hl := hpre.length_le
    simp only [List.length_append, List.length_cons, List.length_nil] at hl
    omega

theorem parents2 (p : List Bool) (a b d : Bool) (hp : childAfter p [b, d] = some a) :
    (p = [] ∧ a = b) ∨ (p = [b] ∧ a = d) := by
  cases p with
  | nil => simp [childAfter] at hp; simp [hp]
  | cons x xs =>
    have hpre := (childAfter_some_iff (x :: xs) [b, d] a).mp hp
    have hl := hpre.length_le
    simp only [List.length_append, List.length_cons, List.length_nil] at hl
    have hx : xs = [] := List.eq_nil_of_length_eq_zero (by omega)
    subst xs
    simp [childAfter] at hp
    simp_all

theorem parents3 (p : List Bool) (a b d e : Bool) (hp : childAfter p [b, d, e] = some a) :
    (p = [] ∧ a = b) ∨ (p = [b] ∧ a = d) ∨ (p = [b, d] ∧ a = e) := by
  cases p with
  | nil => simp [childAfter] at hp; simp [hp]
  | cons x xs =>
    cases xs with
    | nil => simp [childAfter] at hp; simp_all
    | cons y ys =>
      have hpre := (childAfter_some_iff (x :: y :: ys) [b, d, e] a).mp hp
      have hl := hpre.length_le
      simp only [List.length_append, List.length_cons, List.length_nil] at hl
      have hy : ys = [] := List.eq_nil_of_length_eq_zero (by omega)
      subst ys
      simp [childAfter] at hp
      simp_all

theorem complete_prefix_spend (s r a b h u delta good bad : ℝ) (n : ℕ) (hn : n ≤ 5) :
    spend s r a b h ((completeTrace u delta good bad).take n) =
      if n = 0 then 0 else if n = 1 then s + h else if n = 2 then s + 2 * h
      else s + r + a + (n : ℝ) * h := by
  have hI : (Finset.Icc 1 4 : Finset ℕ) = {1, 2, 3, 4} := by decide
  interval_cases n <;>
    simp +decide [spend, meteredSearchCost, replayMetered, meterStep, initialMeter,
      MeteredTreeState.totalPaid, completeTrace, initialization, seedA, seedB,
      discoverA, warmA, replayA, event, List.foldl, panelDemand, qids, executionRoot,
      leaf, executionPrefixes, hI, coldWork, prices, Finset.sdiff_eq_filter,
      Finset.filter_insert, Finset.filter_singleton, Finset.sum_insert] <;> ring

theorem short_prefix_spend (s r a b h u delta good bad : ℝ) (n : ℕ) (hn : n ≤ 3) :
    spend s r a b h ((shortTrace u delta good bad).take n) =
      if n = 0 then 0 else if n = 1 then s + h else if n = 2 then s + 2 * h
      else s + r + b + 3 * h := by
  have hI : (Finset.Icc 1 4 : Finset ℕ) = {1, 2, 3, 4} := by decide
  interval_cases n <;>
    simp +decide [spend, meteredSearchCost, replayMetered, meterStep, initialMeter,
      MeteredTreeState.totalPaid, shortTrace, initialization, seedA, seedB,
      discoverB, event, List.foldl, panelDemand, qids, executionRoot,
      leaf, executionPrefixes, hI, coldWork, prices, Finset.sdiff_eq_filter,
      Finset.filter_insert, Finset.filter_singleton, Finset.sum_insert] <;> ring

theorem complete_penalty_after_publication (s r a b gamma u delta good bad : ℝ)
    (n : ℕ) (hlo : 3 ≤ n) (hhi : n ≤ 4) :
    let before := (completeTrace u delta good bad).take n
    completePenalty s r a b gamma before [] false = 0 ∧
    completePenalty s r a b gamma before [] true = gamma * ((r + b) / 2) ∧
    completePenalty s r a b gamma before [false] false = 0 ∧
    completePenalty s r a b gamma before [false] true = 0 := by
  have hI : (Finset.Icc 1 4 : Finset ℕ) = {1, 2, 3, 4} := by decide
  interval_cases n <;>
    simp +decide [completePenalty, coldForecastPenalty, referenceColdCost,
      uniformTerminalLaw, law, terminals, subtreeTerminals,
      completeTrace, initialization, seedA, seedB, discoverA, warmA, replayA, event,
      replayPublished, publishComplete, initialCaches, List.foldl,
      leaf, panelDemand, executionRoot, qids, executionPrefixes, hI,
      coldWork, prices, Finset.sdiff_eq_filter,
      Finset.filter_insert, Finset.filter_singleton, Finset.sum_insert] <;>
    (apply Or.inl; ring)

theorem seedA_local (c : ℝ) (penalty) (u delta good bad : ℝ) :
    LocalRule c penalty [] (seedA u delta good bad) := by
  intro p a hp
  obtain ⟨rfl, rfl⟩ := parents1 p a false hp
  constructor
  · intro b hb hz; simp [replayBackup, emptyStatistics]
  · intro h
    have hh := h false (by simp [availableChildren, terminals, leaf, childAfter])
    simp [replayBackup, emptyStatistics] at hh

theorem seedB_local (c : ℝ) (penalty) (u delta good bad : ℝ) :
    LocalRule c penalty [seedA u delta good bad] (seedB u delta good bad) := by
  intro p a hp
  obtain ⟨rfl, rfl⟩ := parents1 p a true hp
  constructor
  · intro b hb hz; simp [replayBackup, backupEvent, emptyStatistics, seedA, event]
  · intro h
    have hh := h true (by simp [availableChildren, terminals, leaf, childAfter])
    simp [replayBackup, backupEvent, emptyStatistics, seedA, event] at hh

theorem discover_local (c : ℝ) (penalty) (u delta good bad : ℝ) (branch : Bool)
    (hroot : ∀ b,
      treeIndex (replayBackup (initialization u delta good bad) emptyStatistics [b]).mean c
        (penalty (initialization u delta good bad) [] b)
        (replayBackup (initialization u delta good bad) emptyStatistics []).visits
        (replayBackup (initialization u delta good bad) emptyStatistics [b]).visits ≤
      treeIndex (replayBackup (initialization u delta good bad) emptyStatistics [branch]).mean c
        (penalty (initialization u delta good bad) [] branch)
        (replayBackup (initialization u delta good bad) emptyStatistics []).visits
        (replayBackup (initialization u delta good bad) emptyStatistics [branch]).visits) :
    LocalRule c penalty (initialization u delta good bad)
      (event [branch, true] branch true u delta good bad (by simp [leaf])) := by
  intro p a hp
  rcases parents2 p a branch true hp with ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩
  · constructor
    · intro b hb hz
      cases b <;> simp [initialization, seedA, seedB, event,
        replayBackup, backupEvent, emptyStatistics] at hz
    · intro h b hb
      exact hroot b
  · constructor
    · intro b hb hz
      cases branch <;> cases b <;>
        simp [initialization, seedA, seedB, event, replayBackup, backupEvent, emptyStatistics]
    · intro h
      have hh := h false (by cases branch <;>
        simp [availableChildren, terminals, leaf, childAfter])
      cases branch <;> simp [initialization, seedA, seedB, event,
        replayBackup, backupEvent, emptyStatistics] at hh

def RootMax (c : ℝ) (penalty : List (TreeEvaluation Bool) → List Bool → Bool → ℝ)
    (before : List (TreeEvaluation Bool)) (chosen : Bool) : Prop :=
  ∀ b, treeIndex (replayBackup before emptyStatistics [b]).mean c (penalty before [] b)
      (replayBackup before emptyStatistics []).visits (replayBackup before emptyStatistics [b]).visits ≤
    treeIndex (replayBackup before emptyStatistics [chosen]).mean c (penalty before [] chosen)
      (replayBackup before emptyStatistics []).visits
      (replayBackup before emptyStatistics [chosen]).visits

theorem warmA_local (c : ℝ) (penalty) (u delta good bad : ℝ)
    (hroot : RootMax c penalty ((completeTrace u delta good bad).take 3) false) :
    LocalRule c penalty ((completeTrace u delta good bad).take 3) (warmA u delta good bad) := by
  intro p a hp
  rcases parents2 p a false false hp with ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩
  · constructor
    · intro b hb hz
      cases b <;> simp [completeTrace, initialization, seedA, seedB, discoverA, warmA,
        replayA, event, replayBackup, backupEvent, emptyStatistics] at hz
    · intro h b hb; exact hroot b
  · constructor
    · intro b hb hz
      simp [completeTrace, initialization, seedA, seedB, discoverA, warmA,
        replayA, event, replayBackup, backupEvent, emptyStatistics]
    · intro h
      have hh := h false (by simp [availableChildren, terminals, leaf, childAfter])
      simp [completeTrace, initialization, seedA, seedB, discoverA, warmA,
        replayA, event, replayBackup, backupEvent, emptyStatistics] at hh

theorem replayA_local (c : ℝ) (penalty) (u delta good bad : ℝ) (hgood : u ≤ good)
    (hz0 : penalty ((completeTrace u delta good bad).take 4) [false] false = 0)
    (hz1 : penalty ((completeTrace u delta good bad).take 4) [false] true = 0)
    (hroot : RootMax c penalty ((completeTrace u delta good bad).take 4) false) :
    LocalRule c penalty ((completeTrace u delta good bad).take 4) (replayA u delta good bad) := by
  intro p a hp
  rcases parents3 p a false true false hp with
    ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩
  · constructor
    · intro b hb hz
      cases b <;> simp [completeTrace, initialization, seedA, seedB, discoverA, warmA,
        replayA, event, replayBackup, backupEvent, emptyStatistics] at hz
    · intro h b hb; exact hroot b
  · constructor
    · intro b hb hz
      cases b <;> simp [completeTrace, initialization, seedA, seedB, discoverA, warmA,
        replayA, event, replayBackup, backupEvent, emptyStatistics] at hz
    · intro h b hb
      cases b
      · simp [completeTrace, initialization, seedA, seedB, discoverA, warmA,
          replayA, event, reward, leaf] at hz0 hz1
        simp [completeTrace, initialization, seedA, seedB, discoverA, warmA,
          replayA, event, replayBackup, backupEvent, emptyStatistics, BackupStat.mean,
          reward, leaf, hz0, hz1, treeIndex]
        linarith
      · exact le_refl _
  · constructor
    · intro b hb hz
      simp [completeTrace, initialization, seedA, seedB, discoverA, warmA,
        replayA, event, replayBackup, backupEvent, emptyStatistics]
    · intro h
      have hh := h false (by simp [availableChildren, terminals, leaf, childAfter])
      simp [completeTrace, initialization, seedA, seedB, discoverA, warmA,
        replayA, event, replayBackup, backupEvent, emptyStatistics] at hh

theorem complete_root_initial (s r a b gamma c u delta good bad : ℝ)
    (hsplit : delta < gamma * ((r + b) / 2 - (r + a) / 2)) :
    RootMax c (completePenalty s r a b gamma) (initialization u delta good bad) false := by
  intro chosen
  cases chosen
  · exact le_refl _
  · obtain ⟨ha, hb⟩ := complete_forecasts_initial s r a b gamma u delta good bad
    simp [initialization, seedA, seedB, event, reward, leaf] at ha hb
    simp [initialization, seedA, seedB, event, replayBackup, backupEvent, emptyStatistics,
      BackupStat.mean, reward, leaf, treeIndex, ha, hb]
    nlinarith

theorem short_root_initial (s r a b gamma c u delta good bad : ℝ)
    (hr : 0 < r) (hd : 0 ≤ delta) :
    RootMax c (nextPenalty s r a b gamma) (initialization u delta good bad) true := by
  intro chosen
  cases chosen
  · obtain ⟨ha, hb⟩ := next_forecasts_initial s r a b gamma u delta good bad hr
    simp [initialization, seedA, seedB, event, reward, leaf] at ha hb
    simp [initialization, seedA, seedB, event, replayBackup, backupEvent, emptyStatistics,
      BackupStat.mean, reward, leaf, treeIndex, ha, hb]
    linarith
  · exact le_refl _

theorem unpriced_root_initial (c u delta good bad : ℝ) (hd : 0 ≤ delta) :
    RootMax c (fun _ _ _ => 0) (initialization u delta good bad) true := by
  intro chosen
  cases chosen
  · simp [initialization, seedA, seedB, event, replayBackup, backupEvent, emptyStatistics,
      BackupStat.mean, reward, leaf, treeIndex]
    linarith
  · exact le_refl _

theorem complete_root_warm (s r a b gamma c u delta good bad : ℝ)
    (hc : 0 ≤ c) (hu : 0 ≤ u) (hg : 0 ≤ good) (hu1 : u + delta ≤ 1)
    (hp : 1 + max (treeBonus c 3 1) (treeBonus c 4 1) < gamma * ((r + b) / 2))
    (n : ℕ) (hn0 : 3 ≤ n) (hn1 : n ≤ 4) :
    RootMax c (completePenalty s r a b gamma) ((completeTrace u delta good bad).take n) false := by
  obtain ⟨ha, hb, _, _⟩ := complete_penalty_after_publication s r a b gamma u delta good bad n hn0 hn1
  have hB3 := le_max_left (treeBonus c 3 1) (treeBonus c 4 1)
  have hB4 := le_max_right (treeBonus c 3 1) (treeBonus c 4 1)
  intro chosen
  cases chosen
  · exact le_refl _
  · interval_cases n
    · have hA := treeBonus_nonnegative hc 3 2
      simp [completeTrace, initialization, seedA, seedB, discoverA, warmA, replayA,
        event, reward, leaf] at ha hb
      simp [completeTrace, initialization, seedA, seedB, discoverA, warmA, replayA, event,
        replayBackup, backupEvent, emptyStatistics, BackupStat.mean, reward, leaf,
        treeIndex, ha, hb]
      nlinarith
    · have hA := treeBonus_nonnegative hc 4 3
      simp [completeTrace, initialization, seedA, seedB, discoverA, warmA, replayA,
        event, reward, leaf] at ha hb
      simp [completeTrace, initialization, seedA, seedB, discoverA, warmA, replayA, event,
        replayBackup, backupEvent, emptyStatistics, BackupStat.mean, reward, leaf,
        treeIndex, ha, hb]
      nlinarith

theorem complete_allocation (s r a b gamma c u delta good bad : ℝ)
    (hc : 0 ≤ c) (hu : 0 ≤ u) (hg : 0 ≤ good) (hug : u ≤ good) (hu1 : u + delta ≤ 1)
    (hsplit : delta < gamma * ((r + b) / 2 - (r + a) / 2))
    (hp : 1 + max (treeBonus c 3 1) (treeBonus c 4 1) < gamma * ((r + b) / 2)) :
    TreeAllocationRule terminals c (completePenalty s r a b gamma) (completeTrace u delta good bad) := by
  apply allocation_from_local
  intro n hn
  have hn' : n < 5 := by simpa [completeTrace, initialization] using hn
  interval_cases n
  · exact seedA_local c _ u delta good bad
  · exact seedB_local c _ u delta good bad
  · exact discover_local c _ u delta good bad false
      (complete_root_initial s r a b gamma c u delta good bad hsplit)
  · exact warmA_local c _ u delta good bad
      (complete_root_warm s r a b gamma c u delta good bad hc hu hg hu1 hp 3 (by decide) (by decide))
  · obtain ⟨_, _, hz0, hz1⟩ := complete_penalty_after_publication s r a b gamma u delta good bad 4 (by decide) (by decide)
    exact replayA_local c _ u delta good bad hug hz0 hz1
      (complete_root_warm s r a b gamma c u delta good bad hc hu hg hu1 hp 4 (by decide) (by decide))

theorem short_allocation (s r a b gamma c u delta good bad : ℝ)
    (hr : 0 < r) (hd : 0 ≤ delta) :
    TreeAllocationRule terminals c (nextPenalty s r a b gamma) (shortTrace u delta good bad) := by
  apply allocation_from_local
  intro n hn
  have hn' : n < 3 := by simpa [shortTrace, initialization] using hn
  interval_cases n
  · exact seedA_local c _ u delta good bad
  · exact seedB_local c _ u delta good bad
  · exact discover_local c _ u delta good bad true
      (short_root_initial s r a b gamma c u delta good bad hr hd)

theorem unpriced_allocation (c u delta good bad : ℝ) (hd : 0 ≤ delta) :
    TreeAllocationRule terminals c (fun _ _ _ => 0) (shortTrace u delta good bad) := by
  apply allocation_from_local
  intro n hn
  have hn' : n < 3 := by simpa [shortTrace, initialization] using hn
  interval_cases n
  · exact seedA_local c _ u delta good bad
  · exact seedB_local c _ u delta good bad
  · exact discover_local c _ u delta good bad true
      (unpriced_root_initial c u delta good bad hd)

def lastAffordable (cost : ℕ → ℝ) (B : ℝ) : ℕ → ℕ
  | 0 => 0
  | n + 1 => if cost (n + 1) ≤ B then n + 1 else lastAffordable cost B n
def T_B (s r a b h B : ℝ) (events : List (TreeEvaluation Bool)) : ℕ :=
  lastAffordable (fun n => spend s r a b h (events.take n)) B events.length
def FirstCompleteCrossing (s r a b h B : ℝ) (events : List (TreeEvaluation Bool)) : Prop :=
  (∀ n < events.length, spend s r a b h (events.take n) < B) ∧
    B < spend s r a b h events
def PreCoverage (events : List (TreeEvaluation Bool)) : Prop :=
  ∃ path ∈ terminals, ∀ e ∈ events, e.terminal ≠ path
def recommendedQuality (events : List (TreeEvaluation Bool)) : ℝ :=
  match bestCompleted events with | none => 0 | some e => e.reward
def endpointNet (s r a b h lambda : ℝ) (run retained : List (TreeEvaluation Bool)) : ℝ :=
  recommendedQuality retained - lambda * spend s r a b h run

theorem complete_budget (s r a b h B u delta good bad : ℝ)
    (hs : 0 ≤ s) (hr : 0 ≤ r) (ha : 0 ≤ a) (hh : 0 < h)
    (hfit : s + r + a + 4 * h < B) (hcross : B < s + r + a + 5 * h) :
    FirstCompleteCrossing s r a b h B (completeTrace u delta good bad) ∧
    T_B s r a b h B (completeTrace u delta good bad) = 4 := by
  have h4 := complete_prefix_spend s r a b h u delta good bad 4 (by decide)
  have h5 := complete_prefix_spend s r a b h u delta good bad 5 (by decide)
  norm_num at h4 h5
  constructor
  · constructor
    · intro n hn
      have hn' : n < 5 := by simpa [completeTrace, initialization] using hn
      rw [complete_prefix_spend s r a b h u delta good bad n (by omega)]
      interval_cases n <;> norm_num <;> linarith
    · simpa only [List.take_length] using h5.symm ▸ hcross
  · change lastAffordable _ B 5 = 4
    simp only [lastAffordable]
    rw [h4, h5]
    simp [not_le.mpr hcross, hfit.le]

theorem short_budget (s r a b h B u delta good bad : ℝ)
    (hs : 0 ≤ s) (hh : 0 < h) (hfit : s + 2 * h < B)
    (hcross : B < s + r + b + 3 * h) :
    FirstCompleteCrossing s r a b h B (shortTrace u delta good bad) ∧
    T_B s r a b h B (shortTrace u delta good bad) = 2 := by
  have h2 := short_prefix_spend s r a b h u delta good bad 2 (by decide)
  have h3 := short_prefix_spend s r a b h u delta good bad 3 (by decide)
  norm_num at h2 h3
  constructor
  · constructor
    · intro n hn
      have hn' : n < 3 := by simpa [shortTrace, initialization] using hn
      rw [short_prefix_spend s r a b h u delta good bad n (by omega)]
      interval_cases n <;> norm_num <;> linarith
    · simpa only [List.take_length] using h3.symm ▸ hcross
  · change lastAffordable _ B 3 = 2
    simp only [lastAffordable]
    rw [h2, h3]
    simp [not_le.mpr hcross, hfit.le]

theorem precoverage_before_crossing (u delta good bad : ℝ) :
    PreCoverage ((completeTrace u delta good bad).take 4) ∧
    PreCoverage ((shortTrace u delta good bad).take 2) := by
  constructor <;> refine ⟨leaf true true, by simp [terminals], ?_⟩ <;>
    simp [completeTrace, shortTrace, initialization, seedA, seedB, discoverA, warmA,
      replayA, event, leaf]

theorem best_before_crossing (u delta good bad : ℝ) (hd : 0 < delta)
    (hgood : u + delta < good) :
    recommendedQuality ((completeTrace u delta good bad).take 4) = good ∧
    recommendedQuality ((shortTrace u delta good bad).take 2) = u + delta := by
  have hu : u < u + delta := by linarith
  have hug : ¬ good < u := by linarith
  simp [recommendedQuality, bestCompleted, bestFrom, keepBest, completeTrace,
    shortTrace, initialization, seedA, seedB, discoverA, warmA, replayA, event,
    reward, leaf, hu, hgood, hug]

theorem endpoint_gap_identity (s r a b h lambda u delta good bad : ℝ)
    (hd : 0 < delta) (hgood : u + delta < good) :
    endpointNet s r a b h lambda (completeTrace u delta good bad)
        ((completeTrace u delta good bad).take 4) -
      endpointNet s r a b h lambda (shortTrace u delta good bad)
        ((shortTrace u delta good bad).take 2) =
      good - (u + delta) + lambda * (b - a - 2 * h) := by
  obtain ⟨ha, hb⟩ := best_before_crossing u delta good bad hd hgood
  have hc := complete_prefix_spend s r a b h u delta good bad 5 (by decide)
  have hs := short_prefix_spend s r a b h u delta good bad 3 (by decide)
  norm_num [completeTrace, shortTrace, initialization] at hc hs
  simp only [endpointNet, ha, hb]
  simp only [completeTrace, shortTrace, initialization, List.cons_append, List.nil_append]
  rw [hc, hs]
  ring



theorem margins_from_prediction_error (c gamma r a b rp ap bp epsA epsB delta : ℝ)
    (hg : 0 ≤ gamma)
    (hea : |(rp + ap) - (r + a)| ≤ epsA)
    (heb : |(rp + bp) - (r + b)| ≤ epsB)
    (hsplit : delta < gamma * (((r + b) - (r + a) - epsA - epsB) / 2))
    (hwarm : 1 + max (treeBonus c 3 1) (treeBonus c 4 1) < gamma * (((r + b) - epsB) / 2)) :
    delta < gamma * ((rp + bp) / 2 - (rp + ap) / 2) ∧
    1 + max (treeBonus c 3 1) (treeBonus c 4 1) < gamma * ((rp + bp) / 2) := by
  obtain ⟨hal, har⟩ := abs_le.mp hea
  obtain ⟨hbl, hbr⟩ := abs_le.mp heb
  have hs := mul_le_mul_of_nonneg_left
    (show (((r + b) - (r + a) - epsA - epsB) / 2) ≤
      ((rp + bp) / 2 - (rp + ap) / 2) by linarith) hg
  have hw := mul_le_mul_of_nonneg_left
    (show ((r + b) - epsB) / 2 ≤ (rp + bp) / 2 by linarith) hg
  exact ⟨hsplit.trans_le hs, hwarm.trans_le hw⟩

theorem physical_prices_nonnegative (s r a b : ℝ)
    (hs : 0 ≤ s) (hr : 0 ≤ r) (ha : 0 ≤ a) (hb : 0 ≤ b) :
    ∀ resource, 0 ≤ prices s r a b resource := by
  intro resource
  unfold prices
  split_ifs <;> first | assumption | positivity

theorem fixed_table_traces (u delta good bad : ℝ) :
    FixedTableEvents terminals (reward u delta good bad) (completeTrace u delta good bad) ∧
    FixedTableEvents terminals (reward u delta good bad) (shortTrace u delta good bad) := by
  constructor
  · intro e he
    simp [completeTrace, initialization] at he
    rcases he with rfl | rfl | rfl | rfl | rfl <;>
      simp [seedA, seedB, discoverA, warmA, replayA, event, terminals]
  · intro e he
    simp [shortTrace, initialization] at he
    rcases he with rfl | rfl | rfl <;>
      simp [seedA, seedB, discoverB, event, terminals]

structure Separation (s r a b h B rp ap bp gamma c u delta good bad lambda : ℝ) : Prop where
  legalComplete : LegalTreeRun (fun p => p ∈ terminals) {[]} (completeTrace u delta good bad)
  legalComparator : LegalTreeRun (fun p => p ∈ terminals) {[]} (shortTrace u delta good bad)
  completeAllocated : TreeAllocationRule terminals c (completePenalty s rp ap bp gamma)
    (completeTrace u delta good bad)
  nextAllocated : TreeAllocationRule terminals c (nextPenalty s rp ap bp gamma)
    (shortTrace u delta good bad)
  unpricedAllocated : TreeAllocationRule terminals c (fun _ _ _ => 0) (shortTrace u delta good bad)
  completeStops : FirstCompleteCrossing s r a b h B (completeTrace u delta good bad)
  comparatorStops : FirstCompleteCrossing s r a b h B (shortTrace u delta good bad)
  completeHorizon : T_B s r a b h B (completeTrace u delta good bad) = 4
  comparatorHorizon : T_B s r a b h B (shortTrace u delta good bad) = 2
  beforeCoverage : PreCoverage ((completeTrace u delta good bad).take 4) ∧
    PreCoverage ((shortTrace u delta good bad).take 2)
  qualityGap : recommendedQuality ((shortTrace u delta good bad).take 2) <
    recommendedQuality ((completeTrace u delta good bad).take 4)
  netGap : endpointNet s r a b h lambda (shortTrace u delta good bad)
      ((shortTrace u delta good bad).take 2) <
    endpointNet s r a b h lambda (completeTrace u delta good bad)
      ((completeTrace u delta good bad).take 4)





theorem precoverage_full_trajectory_separation
    (s r a b h B rp ap bp gamma c u delta good bad lambda epsA epsB : ℝ)
    (hs : 0 ≤ s) (hr : 0 ≤ r) (ha : 0 ≤ a) (hb : 0 ≤ b) (hh : 0 < h)
    (hrp : 0 < rp) (hgamma : 0 ≤ gamma) (hc : 0 ≤ c)
    (hu : 0 ≤ u) (hg : 0 ≤ good) (hug : u + delta < good) (hu1 : u + delta ≤ 1)
    (hd : 0 < delta) (hlambda : 0 ≤ lambda)
    (hea : |(rp + ap) - (r + a)| ≤ epsA)
    (heb : |(rp + bp) - (r + b)| ≤ epsB)
    (hsplit : delta < gamma * (((r + b) - (r + a) - epsA - epsB) / 2))
    (hwarm : 1 + max (treeBonus c 3 1) (treeBonus c 4 1) < gamma * (((r + b) - epsB) / 2))
    (hnet : 2 * h ≤ b - a)
    (hfit : s + r + a + 4 * h < B)
    (hcross : B < s + r + a + 5 * h)
    (hnextCross : B < s + r + b + 3 * h) :
    Separation s r a b h B rp ap bp gamma c u delta good bad lambda := by
  obtain ⟨hsplit', hwarm'⟩ := margins_from_prediction_error c gamma r a b rp ap bp epsA epsB delta
    hgamma hea heb hsplit hwarm
  obtain ⟨hstopA, hTA⟩ := complete_budget s r a b h B u delta good bad hs hr ha hh hfit hcross
  obtain ⟨hstopB, hTB⟩ := short_budget s r a b h B u delta good bad hs hh (by linarith) hnextCross
  obtain ⟨hQA, hQB⟩ := best_before_crossing u delta good bad hd hug
  have hJ := endpoint_gap_identity s r a b h lambda u delta good bad hd hug
  have hcost : 0 ≤ lambda * (b - a - 2 * h) := mul_nonneg hlambda (by linarith)
  exact {
    legalComplete := complete_legal u delta good bad
    legalComparator := short_legal u delta good bad
    completeAllocated := complete_allocation s rp ap bp gamma c u delta good bad hc hu hg
      (by linarith) hu1 hsplit' hwarm'
    nextAllocated := short_allocation s rp ap bp gamma c u delta good bad hrp hd.le
    unpricedAllocated := unpriced_allocation c u delta good bad hd.le
    completeStops := hstopA
    comparatorStops := hstopB
    completeHorizon := hTA
    comparatorHorizon := hTB
    beforeCoverage := precoverage_before_crossing u delta good bad
    qualityGap := by rw [hQA, hQB]; exact hug
    netGap := by linarith
  }

def warmB (u delta good bad : ℝ) :=
  event [true, false] true false u delta good bad (by simp [leaf])
def adverseTrace (u delta good bad : ℝ) :=
  initialization u delta good bad ++ [discoverB u delta good bad, warmB u delta good bad]

theorem adverse_legal (u delta good bad : ℝ) :
    LegalTreeRun (fun p => p ∈ terminals) {[]} (adverseTrace u delta good bad) := by
  simp +decide [adverseTrace, initialization, seedA, seedB, discoverB, warmB,
    event, LegalTreeRun, LegalTreeEvent, growTree, terminals, leaf]

theorem next_after_B_publication (s r a b gamma u delta good bad : ℝ) (hr : 0 < r) :
    nextPenalty s r a b gamma ((adverseTrace u delta good bad).take 3) [] false = gamma * (r / 2) ∧
    nextPenalty s r a b gamma ((adverseTrace u delta good bad).take 3) [] true = 0 := by
  simp +decide [nextPenalty, cache, replayPublished, publishComplete, initialCaches,
    adverseTrace, initialization, seedA, seedB, discoverB, warmB, event,
    uniformTerminalLaw, law, terminals, subtreeTerminals, leaf,
    orderedResources, executionRoot, panelDemand, qids, executionPrefixes,
    show (Finset.Icc 1 4 : Finset ℕ) = {1, 2, 3, 4} from by decide,
    prices, nextUnpaidBill, List.range_succ, Finset.filter_insert,
    Finset.filter_singleton, Finset.sum_insert, not_le.mpr hr]
  apply Or.inl
  ring

theorem adverse_root_warm (s r a b gamma c u delta good bad : ℝ)
    (hr : 0 < r) (hc : 0 ≤ c) (hu : u ≤ 1) (hd : 0 ≤ u + delta) (hb : 0 ≤ bad)
    (hp : 1 + treeBonus c 3 1 < gamma * (r / 2)) :
    RootMax c (nextPenalty s r a b gamma) ((adverseTrace u delta good bad).take 3) true := by
  intro chosen
  cases chosen
  · obtain ⟨ha, hb'⟩ := next_after_B_publication s r a b gamma u delta good bad hr
    simp [adverseTrace, initialization, seedA, seedB, discoverB, warmB,
      event, reward, leaf] at ha hb'
    have hB := treeBonus_nonnegative hc 3 2
    simp [adverseTrace, initialization, seedA, seedB, discoverB, warmB, event,
      replayBackup, backupEvent, emptyStatistics, BackupStat.mean, reward, leaf,
      treeIndex, ha, hb']
    nlinarith
  · exact le_refl _

theorem warmB_local (c : ℝ) (penalty) (u delta good bad : ℝ)
    (hroot : RootMax c penalty ((adverseTrace u delta good bad).take 3) true) :
    LocalRule c penalty ((adverseTrace u delta good bad).take 3) (warmB u delta good bad) := by
  intro p a hp
  rcases parents2 p a true false hp with ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩
  · constructor
    · intro b hb hz
      cases b <;> simp [adverseTrace, initialization, seedA, seedB, discoverB, warmB,
        event, replayBackup, backupEvent, emptyStatistics] at hz
    · intro h b hb; exact hroot b
  · constructor
    · intro b hb hz
      simp [adverseTrace, initialization, seedA, seedB, discoverB, warmB,
        event, replayBackup, backupEvent, emptyStatistics]
    · intro h
      have hh := h false (by simp [availableChildren, terminals, leaf, childAfter])
      simp [adverseTrace, initialization, seedA, seedB, discoverB, warmB,
        event, replayBackup, backupEvent, emptyStatistics] at hh

theorem adverse_next_allocation (s r a b gamma c u delta good bad : ℝ)
    (hr : 0 < r) (hc : 0 ≤ c) (hu : u ≤ 1) (hd0 : 0 ≤ delta)
    (hd : 0 ≤ u + delta) (hb : 0 ≤ bad)
    (hp : 1 + treeBonus c 3 1 < gamma * (r / 2)) :
    TreeAllocationRule terminals c (nextPenalty s r a b gamma) (adverseTrace u delta good bad) := by
  apply allocation_from_local
  intro n hn
  have hn' : n < 4 := by simpa [adverseTrace, initialization] using hn
  interval_cases n
  · exact seedA_local c _ u delta good bad
  · exact seedB_local c _ u delta good bad
  · exact discover_local c _ u delta good bad true
      (short_root_initial s r a b gamma c u delta good bad hr hd0)
  · exact warmB_local c _ u delta good bad
      (adverse_root_warm s r a b gamma c u delta good bad hr hc hu hd hb hp)

theorem adverse_prefix_spend (s r a b h u delta good bad : ℝ) (n : ℕ) (hn : n ≤ 4) :
    spend s r a b h ((adverseTrace u delta good bad).take n) =
      if n = 0 then 0 else if n = 1 then s + h else if n = 2 then s + 2 * h
      else s + r + b + (n : ℝ) * h := by
  have hI : (Finset.Icc 1 4 : Finset ℕ) = {1, 2, 3, 4} := by decide
  interval_cases n <;>
    simp +decide [spend, meteredSearchCost, replayMetered, meterStep, initialMeter,
      MeteredTreeState.totalPaid, adverseTrace, initialization, seedA, seedB,
      discoverB, warmB, event, List.foldl, panelDemand, qids, executionRoot,
      leaf, executionPrefixes, hI, coldWork, prices, Finset.sdiff_eq_filter,
      Finset.filter_insert, Finset.filter_singleton, Finset.sum_insert] <;> ring

theorem adverse_budget (s r a b h B u delta good bad : ℝ)
    (hs : 0 ≤ s) (hr : 0 ≤ r) (hb : 0 ≤ b) (hh : 0 < h)
    (hfit : s + r + b + 3 * h < B) (hcross : B < s + r + b + 4 * h) :
    FirstCompleteCrossing s r a b h B (adverseTrace u delta good bad) ∧
    T_B s r a b h B (adverseTrace u delta good bad) = 3 := by
  have h3 := adverse_prefix_spend s r a b h u delta good bad 3 (by decide)
  have h4 := adverse_prefix_spend s r a b h u delta good bad 4 (by decide)
  norm_num at h3 h4
  constructor
  · constructor
    · intro n hn
      have hn' : n < 4 := by simpa [adverseTrace, initialization] using hn
      rw [adverse_prefix_spend s r a b h u delta good bad n (by omega)]
      interval_cases n <;> norm_num <;> linarith
    · simpa only [List.take_length] using h4.symm ▸ hcross
  · change lastAffordable _ B 4 = 3
    simp only [lastAffordable]
    rw [h3, h4]
    simp [not_le.mpr hcross, hfit.le]

theorem adverse_best (u delta bad : ℝ) (hd : 0 < delta) (hbad : u + delta < bad) :
    recommendedQuality ((completeTrace u delta u bad).take 4) = u + delta ∧
    recommendedQuality ((adverseTrace u delta u bad).take 3) = bad := by
  have hu : u < u + delta := by linarith
  have hn : ¬ u + delta < u := by linarith
  simp [recommendedQuality, bestCompleted, bestFrom, keepBest, completeTrace,
    adverseTrace, initialization, seedA, seedB, discoverA, discoverB, warmA,
    warmB, replayA, event, reward, leaf, hu, hn, hbad]



theorem adverse_endpoint_gap (s r a b h lambda u delta bad : ℝ)
    (hd : 0 < delta) (hbad : u + delta < bad) :
    endpointNet s r a b h lambda (adverseTrace u delta u bad)
        ((adverseTrace u delta u bad).take 3) -
      endpointNet s r a b h lambda (completeTrace u delta u bad)
        ((completeTrace u delta u bad).take 4) =
      bad - (u + delta) - lambda * (b - a - h) := by
  obtain ⟨hA, hB⟩ := adverse_best u delta bad hd hbad
  have hCA := complete_prefix_spend s r a b h u delta u bad 5 (by decide)
  have hCB := adverse_prefix_spend s r a b h u delta u bad 4 (by decide)
  norm_num [completeTrace, adverseTrace, initialization] at hCA hCB
  simp only [endpointNet, hA, hB]
  simp only [completeTrace, adverseTrace, initialization, List.cons_append, List.nil_append]
  rw [hCA, hCB]
  ring

structure Reversal (s r a b h B gamma c u delta bad lambda : ℝ) : Prop where
  legalComplete : LegalTreeRun (fun p => p ∈ terminals) {[]} (completeTrace u delta u bad)
  legalComparator : LegalTreeRun (fun p => p ∈ terminals) {[]} (adverseTrace u delta u bad)
  completeAllocated : TreeAllocationRule terminals c (completePenalty s r a b gamma)
    (completeTrace u delta u bad)
  nextAllocated : TreeAllocationRule terminals c (nextPenalty s r a b gamma)
    (adverseTrace u delta u bad)
  completeStops : FirstCompleteCrossing s r a b h B
    (completeTrace u delta u bad)
  comparatorStops : FirstCompleteCrossing s r a b h B
    (adverseTrace u delta u bad)
  completeHorizon : T_B s r a b h B (completeTrace u delta u bad) = 4
  comparatorHorizon : T_B s r a b h B (adverseTrace u delta u bad) = 3
  beforeCoverage : PreCoverage ((completeTrace u delta u bad).take 4) ∧
    PreCoverage ((adverseTrace u delta u bad).take 3)
  reversedQuality : recommendedQuality ((completeTrace u delta u bad).take 4) <
    recommendedQuality ((adverseTrace u delta u bad).take 3)
  reversedNet : endpointNet s r a b h lambda (completeTrace u delta u bad)
      ((completeTrace u delta u bad).take 4) <
    endpointNet s r a b h lambda (adverseTrace u delta u bad)
      ((adverseTrace u delta u bad).take 3)




theorem precoverage_full_trajectory_reversal
    (s r a b h B gamma c u delta bad lambda : ℝ)
    (hs : 0 ≤ s) (hr : 0 < r) (ha : 0 ≤ a) (hb : 0 ≤ b) (hh : 0 < h)
    (hc : 0 ≤ c) (hu : 0 ≤ u) (hu1 : u + delta ≤ 1)
    (hd : 0 < delta) (hbad0 : 0 ≤ bad) (hbad : u + delta < bad)
    (hsplit : delta < gamma * ((r + b) / 2 - (r + a) / 2))
    (hwarm : 1 + max (treeBonus c 3 1) (treeBonus c 4 1) < gamma * ((r + b) / 2))
    (hnext : 1 + treeBonus c 3 1 < gamma * (r / 2))
    (hfit : h ≤ b - a) (hcross : b - a < 2 * h)
    (hBfit : s + r + b + 3 * h < B) (hBcross : B < s + r + a + 5 * h)
    (hnet : lambda * (b - a - h) < bad - (u + delta)) :
    Reversal s r a b h B gamma c u delta bad lambda := by
  obtain ⟨hstopA, hTA⟩ := complete_budget s r a b h B
    u delta u bad hs hr.le ha hh (by linarith) (by linarith)
  obtain ⟨hstopB, hTB⟩ := adverse_budget s r a b h B u delta u bad hs hr.le hb hh
    hBfit (by linarith)
  obtain ⟨hQA, hQB⟩ := adverse_best u delta bad hd hbad
  have hJ := adverse_endpoint_gap s r a b h lambda u delta bad hd hbad
  have hpreA := (precoverage_before_crossing u delta u bad).1
  have hpreB : PreCoverage ((adverseTrace u delta u bad).take 3) := by
    refine ⟨leaf false true, by simp [terminals], ?_⟩
    simp [adverseTrace, initialization, seedA, seedB, discoverB, warmB, event, leaf]
  exact {
    legalComplete := complete_legal u delta u bad
    legalComparator := adverse_legal u delta u bad
    completeAllocated := complete_allocation s r a b gamma c u delta u bad hc hu hu
      (le_refl _) hu1 hsplit hwarm
    nextAllocated := adverse_next_allocation s r a b gamma c u delta u bad hr hc
      (by linarith) hd.le (by linarith) hbad0 hnext
    completeStops := hstopA
    comparatorStops := hstopB
    completeHorizon := hTA
    comparatorHorizon := hTB
    beforeCoverage := ⟨hpreA, hpreB⟩
    reversedQuality := by rw [hQA, hQB]; exact hbad
    reversedNet := by linarith
  }

theorem subtree_value_of_max (p winner : List Bool) (u delta good bad : ℝ)
    (hw : winner ∈ terminals) (hp : p <+: winner)
    (hmax : ∀ path ∈ terminals, p <+: path → reward u delta good bad path ≤
      reward u delta good bad winner) :
    subtreeValue terminals (reward u delta good bad) p = reward u delta good bad winner := by
  have hn : (subtreeTerminals terminals p).Nonempty := ⟨winner, mem_filter.mpr ⟨hw, hp⟩⟩
  obtain ⟨path, ht, hpre, hv⟩ := subtreeValue_attained terminals (reward u delta good bad) p hn
  exact le_antisymm (hv ▸ hmax path ht hpre)
    (subtreeValue_upper terminals (reward u delta good bad) p winner hw hp)


theorem favorable_branch_values (u delta good bad : ℝ)
    (hd : 0 ≤ delta) (hg : u + delta ≤ good) (hb : bad ≤ u + delta) :
    subtreeValue terminals (reward u delta good bad) [false] = good ∧
    subtreeValue terminals (reward u delta good bad) [true] = u + delta ∧
    subtreeValue terminals (reward u delta good bad) [] = good := by
  constructor
  · have h := subtree_value_of_max [false] (leaf false true) u delta good bad
      (by simp [terminals]) (by simp [leaf])
    simp only [reward, Bool.false_eq_true, false_and, ite_true] at h
    apply h
    intro path ht hp
    simp only [terminals, mem_insert, mem_singleton] at ht
    rcases ht with rfl | rfl | rfl | rfl <;>
      simp [leaf, reward] at hp ⊢ <;> linarith
  constructor
  · have h := subtree_value_of_max [true] (leaf true false) u delta good bad
      (by simp [terminals]) (by simp [leaf])
    simp [reward, leaf] at h
    apply h
    intro path ht hp
    simp only [terminals, mem_insert, mem_singleton] at ht
    rcases ht with rfl | rfl | rfl | rfl <;>
      simp [leaf, reward] at hp ⊢ <;> linarith
  · have h := subtree_value_of_max [] (leaf false true) u delta good bad
      (by simp [terminals]) List.nil_prefix
    simp [reward, leaf] at h
    apply h
    intro path ht
    simp only [terminals, mem_insert, mem_singleton] at ht
    rcases ht with rfl | rfl | rfl | rfl <;>
      simp [leaf, reward] <;> linarith

theorem adverse_global_value (u delta bad : ℝ) (hd : 0 ≤ delta) (hb : u + delta ≤ bad) :
    subtreeValue terminals (reward u delta u bad) [] = bad := by
  have h := subtree_value_of_max [] (leaf true true) u delta u bad
    (by simp [terminals]) List.nil_prefix
  simp [reward, leaf] at h
  apply h
  intro path ht
  simp only [terminals, mem_insert, mem_singleton] at ht
  rcases ht with rfl | rfl | rfl | rfl <;> simp [leaf, reward] <;> linarith

theorem fixed_rewards_unit_interval (u delta good bad : ℝ)
    (hu : 0 ≤ u) (hd : 0 ≤ delta) (hs : u + delta ≤ 1)
    (hg0 : 0 ≤ good) (hg1 : good ≤ 1) (hb0 : 0 ≤ bad) (hb1 : bad ≤ 1) :
    ∀ path ∈ terminals, 0 ≤ reward u delta good bad path ∧ reward u delta good bad path ≤ 1 := by
  intro path ht
  simp only [terminals, mem_insert, mem_singleton] at ht
  rcases ht with rfl | rfl | rfl | rfl <;> simp [leaf, reward] <;> constructor <;> linarith

theorem terminals_antichain :
    ∀ p ∈ terminals, ∀ q ∈ terminals, p <+: q → p = q := by
  simp +decide [terminals, leaf]

theorem law_probability (before : List (TreeEvaluation Bool)) (p : List Bool) (chosen : Bool)
    (h : (subtreeTerminals terminals (p ++ [chosen])).Nonempty) :
    (∀ path, 0 ≤ law before p chosen path) ∧
      (∑ path ∈ subtreeTerminals terminals (p ++ [chosen]), law before p chosen path) = 1 := by
  exact uniformTerminalLaw_probability terminals (p ++ [chosen]) h



theorem common_overhead_index_order (qA qB c costA costB gamma h : ℝ)
    (parent countA countB : ℕ) :
    treeIndex qA c (gamma * (costA + h)) parent countA ≤
        treeIndex qB c (gamma * (costB + h)) parent countB ↔
      treeIndex qA c (gamma * costA) parent countA ≤
        treeIndex qB c (gamma * costB) parent countB := by
  unfold treeIndex
  constructor <;> intro hx <;> nlinarith

theorem bonus_14_bound : max (treeBonus (7 / 5) 3 1) (treeBonus (7 / 5) 4 1) ≤ 14 / 5 := by
  have hl4 := Real.log_le_sub_one_of_pos (show (0 : ℝ) < 4 by norm_num)
  have hl5 := Real.log_le_sub_one_of_pos (show (0 : ℝ) < 5 by norm_num)
  have hs4 : Real.sqrt (Real.log 4) ≤ 2 := Real.sqrt_le_iff.mpr ⟨by norm_num, by linarith⟩
  have hs5 : Real.sqrt (Real.log 5) ≤ 2 := Real.sqrt_le_iff.mpr ⟨by norm_num, by linarith⟩
  apply max_le
  · norm_num [treeBonus]
    linarith
  · norm_num [treeBonus]
    linarith




theorem separation_attains_true_optimum
    (s r a b h B rp ap bp gamma c u delta good bad lambda : ℝ)
    (hsep : Separation s r a b h B rp ap bp gamma c u delta good bad lambda)
    (hd : 0 < delta) (hg : u + delta < good) (hb : bad ≤ u + delta) :
    recommendedQuality ((completeTrace u delta good bad).take
      (T_B s r a b h B (completeTrace u delta good bad))) =
      subtreeValue terminals (reward u delta good bad) [] ∧
    subtreeValue terminals (reward u delta good bad) [] -
      recommendedQuality ((shortTrace u delta good bad).take
        (T_B s r a b h B (shortTrace u delta good bad))) = good - (u + delta) ∧
    subtreeValue terminals (reward u delta good bad) [false] -
      subtreeValue terminals (reward u delta good bad) [true] = good - (u + delta) := by
  obtain ⟨hA, hB, hV⟩ := favorable_branch_values u delta good bad hd.le hg.le hb
  obtain ⟨hQA, hQB⟩ := best_before_crossing u delta good bad hd hg
  rw [hsep.completeHorizon, hsep.comparatorHorizon, hQA, hQB, hA, hB, hV]
  exact ⟨rfl, rfl, rfl⟩



theorem favorable_instance_c14 :
    Separation 1 1 1 4 1 (15 / 2) 1 1 4 2 (7 / 5) (2 / 5) (1 / 10)
      (9 / 10) (1 / 2) (1 / 20) := by
  apply precoverage_full_trajectory_separation 1 1 1 4 1 (15 / 2) 1 1 4 2 (7 / 5)
    (2 / 5) (1 / 10) (9 / 10) (1 / 2) (1 / 20) (1 / 10) (1 / 10) <;> norm_num
  have hx := bonus_14_bound
  nlinarith

theorem favorable_instance_optimal :
    recommendedQuality ((completeTrace (2 / 5) (1 / 10) (9 / 10) (1 / 2)).take 4) =
      subtreeValue terminals (reward (2 / 5) (1 / 10) (9 / 10) (1 / 2)) [] ∧
    subtreeValue terminals (reward (2 / 5) (1 / 10) (9 / 10) (1 / 2)) [] -
      recommendedQuality ((shortTrace (2 / 5) (1 / 10) (9 / 10) (1 / 2)).take 2) = 2 / 5 := by
  have hx := separation_attains_true_optimum 1 1 1 4 1 (15 / 2) 1 1 4 2 (7 / 5)
    (2 / 5) (1 / 10) (9 / 10) (1 / 2) (1 / 20) favorable_instance_c14
    (by norm_num) (by norm_num) (by norm_num)
  rw [favorable_instance_c14.completeHorizon, favorable_instance_c14.comparatorHorizon] at hx
  norm_num at hx
  exact ⟨hx.1, hx.2.1⟩

theorem favorable_instance_reward_bounds :
    ∀ path ∈ terminals, 0 ≤ reward (2 / 5) (1 / 10) (9 / 10) (1 / 2) path ∧
      reward (2 / 5) (1 / 10) (9 / 10) (1 / 2) path ≤ 1 := by
  apply fixed_rewards_unit_interval <;> norm_num



theorem adverse_instance_c14 :
    Reversal 1 1 1 (5 / 2) 1 (31 / 4) 10 (7 / 5) (1 / 4) (1 / 4) 1 (1 / 20) := by
  apply precoverage_full_trajectory_reversal 1 1 1 (5 / 2) 1 (31 / 4) 10 (7 / 5)
    (1 / 4) (1 / 4) 1 (1 / 20) <;> norm_num
  · have hx := bonus_14_bound
    nlinarith
  · have hx := (le_max_left (treeBonus (7 / 5) 3 1) (treeBonus (7 / 5) 4 1)).trans bonus_14_bound
    nlinarith

theorem adverse_instance_reward_bounds :
    ∀ path ∈ terminals, 0 ≤ reward (1 / 4) (1 / 4) (1 / 4) 1 path ∧
      reward (1 / 4) (1 / 4) (1 / 4) 1 path ≤ 1 := by
  apply fixed_rewards_unit_interval <;> norm_num

theorem cross_branch_overlap (hiddenA hiddenB : Bool) :
    demand false hiddenA ∩ demand true hiddenB = {((), [false])} := by
  cases hiddenA <;> cases hiddenB <;> ext resource <;> simp +decide [demand_explicit]

theorem overlap_weight (s r a b : ℝ) (branch : Bool) :
    cacheWeight (prices s r a b) (demand branch false ∩ demand branch true) = s := by
  rw [shared_overlap]
  cases branch <;> simp [cacheWeight, prices]

theorem published_caches_after_discovery (u delta good bad : ℝ) :
    cache ((completeTrace u delta good bad).take 3) =
      demand false false ∪ demand true false ∪ demand false true ∧
    cache ((shortTrace u delta good bad).take 3) =
      demand false false ∪ demand true false ∪ demand true true := by
  simp [cache, completeTrace, shortTrace, initialization, seedA, seedB, discoverA,
    discoverB, warmA, replayA, event, replayPublished, publishComplete, initialCaches,
    demand, List.foldl]

theorem physical_cold_after_discovery (s r a b u delta good bad : ℝ) :
    coldWork (prices s r a b) (cache ((completeTrace u delta good bad).take 3))
      (demand false true) = 0 ∧
    coldWork (prices s r a b) (cache ((completeTrace u delta good bad).take 3))
      (demand true true) = r + b ∧
    coldWork (prices s r a b) (cache ((shortTrace u delta good bad).take 3))
      (demand true true) = 0 ∧
    coldWork (prices s r a b) (cache ((shortTrace u delta good bad).take 3))
      (demand false true) = r + a := by
  obtain ⟨hA, hB⟩ := published_caches_after_discovery u delta good bad
  rw [hA, hB]
  simp +decide [demand_explicit, coldWork, prices, Finset.sdiff_eq_filter,
    Finset.filter_insert, Finset.filter_singleton, Finset.sum_insert]





theorem equal_predicted_tail_margin_impossible (r a gamma delta : ℝ) (hd : 0 < delta) :
    ¬ delta < gamma * ((r + a) / 2 - (r + a) / 2) := by
  simp
  linarith



def ownReceiptIndices (before : List (TreeEvaluation Bool)) (resource : Resource) : Finset ℕ :=
  (Finset.range before.length).filter (fun i =>
    resource ∈ cache (before.take (i + 1)) \ cache (before.take i))




def updatedPrices (s r a b : ℝ) (before : List (TreeEvaluation Bool)) (resource : Resource) : ℝ :=
  onlineMean (prices s r a b resource) (ownReceiptIndices before resource)
    (fun _ => prices s r a b resource)

theorem constant_receipt_mean {I : Type*} (value : ℝ) (samples : Finset I) :
    onlineMean value samples (fun _ => value) = value := by
  have hn : ((samples.card : ℝ) + 1) ≠ 0 := by positivity
  simp only [onlineMean, Finset.sum_const, nsmul_eq_mul]
  apply (div_eq_iff hn).mpr
  ring

theorem updated_prices_exact (s r a b : ℝ) (before : List (TreeEvaluation Bool)) :
    updatedPrices s r a b before = prices s r a b := by
  funext resource
  exact constant_receipt_mean _ _

def updatedCompletePenalty (s r a b gamma : ℝ) (before : List (TreeEvaluation Bool))
    (p : List Bool) (chosen : Bool) : ℝ :=
  coldForecastPenalty qids executionRoot terminals (updatedPrices s r a b before)
    gamma law initialCaches before p chosen

theorem updated_penalty_exact (s r a b gamma : ℝ) :
    updatedCompletePenalty s r a b gamma = completePenalty s r a b gamma := by
  funext before p chosen
  simp only [updatedCompletePenalty, updated_prices_exact, completePenalty]

theorem own_updated_complete_allocation (s r a b gamma c u delta good bad : ℝ)
    (hc : 0 ≤ c) (hu : 0 ≤ u) (hg : 0 ≤ good) (hug : u ≤ good) (hu1 : u + delta ≤ 1)
    (hsplit : delta < gamma * ((r + b) / 2 - (r + a) / 2))
    (hp : 1 + max (treeBonus c 3 1) (treeBonus c 4 1) < gamma * ((r + b) / 2)) :
    TreeAllocationRule terminals c (updatedCompletePenalty s r a b gamma)
      (completeTrace u delta good bad) := by
  rw [updated_penalty_exact]
  exact complete_allocation s r a b gamma c u delta good bad hc hu hg hug hu1 hsplit hp

theorem favorable_instance_net_gap :
    endpointNet 1 1 1 4 1 (1 / 20) (completeTrace (2 / 5) (1 / 10) (9 / 10) (1 / 2))
      ((completeTrace (2 / 5) (1 / 10) (9 / 10) (1 / 2)).take 4) -
    endpointNet 1 1 1 4 1 (1 / 20) (shortTrace (2 / 5) (1 / 10) (9 / 10) (1 / 2))
      ((shortTrace (2 / 5) (1 / 10) (9 / 10) (1 / 2)).take 2) = 9 / 20 := by
  rw [endpoint_gap_identity 1 1 1 4 1 (1 / 20) (2 / 5) (1 / 10) (9 / 10) (1 / 2)
    (by norm_num) (by norm_num)]
  norm_num

theorem adverse_instance_net_gap :
    endpointNet 1 1 1 (5 / 2) 1 (1 / 20) (adverseTrace (1 / 4) (1 / 4) (1 / 4) 1)
      ((adverseTrace (1 / 4) (1 / 4) (1 / 4) 1).take 3) -
    endpointNet 1 1 1 (5 / 2) 1 (1 / 20) (completeTrace (1 / 4) (1 / 4) (1 / 4) 1)
      ((completeTrace (1 / 4) (1 / 4) (1 / 4) 1).take 4) = 19 / 40 := by
  rw [adverse_endpoint_gap 1 1 1 (5 / 2) 1 (1 / 20) (1 / 4) (1 / 4) 1
    (by norm_num) (by norm_num)]
  norm_num

end AgentUCTBudgetP1V2
