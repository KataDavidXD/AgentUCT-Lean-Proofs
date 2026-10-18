import NativeBudgetGenerated



set_option autoImplicit false
set_option maxRecDepth 16384
set_option maxHeartbeats 4000000
set_option linter.constructorNameAsVariable false
noncomputable section
namespace AgentUCTNativeBudget
open AgentUCTPanelAllocation AgentUCTNativeRepair AgentUCTNativeRefinement AgentUCTPaper
variable {Qid : Type*} [DecidableEq Qid]

def taskReward (adverse : Bool) (delta good : ℝ) (path : List Act) : ℝ :=
  if path = aCold then (if adverse then 0 else good)
  else if path = bCold then (if adverse then good else delta)
  else if path = seedPath branchB then delta else 0

theorem seed_distinct_budget_cold (q : Fin 8) : seedPath q ≠ aCold ∧ seedPath q ≠ bCold := by
  fin_cases q <;> decide

theorem seeds_equal_iff (q r : Fin 8) : seedPath q = seedPath r ↔ q = r := by
  constructor
  · intro h
    have hh := congrArg List.head? h
    simpa [seedPath,leaf] using hh
  · rintro rfl; rfl

theorem task_seed_table (adverse : Bool) (delta good : ℝ) :
    SeedTable (taskReward adverse delta good) delta := by
  intro q
  simp [taskReward,(seed_distinct_budget_cold q).1,(seed_distinct_budget_cold q).2,seeds_equal_iff]

theorem task_cold_rewards (adverse : Bool) (delta good : ℝ) :
    taskReward adverse delta good aCold = (if adverse then 0 else good) ∧
    taskReward adverse delta good bCold = (if adverse then good else delta) ∧
    taskReward adverse delta good aWarm = 0 ∧ taskReward adverse delta good aCross = 0 := by
  simp [taskReward,show bCold ≠ aCold by decide,
    show aWarm ≠ aCold by decide,show aWarm ≠ bCold by decide,show aWarm ≠ seedPath branchB by decide,
    show aCross ≠ aCold by decide,show aCross ≠ bCold by decide,show aCross ≠ seedPath branchB by decide]

theorem task_reward_unit_interval (adverse : Bool) (delta good : ℝ)
    (hd : 0 ≤ delta ∧ delta ≤ good) (hg : 0 ≤ good ∧ good ≤ 1) (path : List Act) :
    0 ≤ taskReward adverse delta good path ∧ taskReward adverse delta good path ≤ 1 := by
  unfold taskReward
  split_ifs <;> rcases hd with ⟨hd0,hdg⟩ <;> rcases hg with ⟨hg0,hg1⟩ <;> constructor <;> linarith

theorem task_true_terminal_optimum (adverse : Bool) (delta good : ℝ)
    (hd : delta ≤ good) (hg : 0 ≤ good) :
    (∀ path,Terminal path → taskReward adverse delta good path ≤ good) ∧
    ∃ path,Terminal path ∧ taskReward adverse delta good path = good := by
  constructor
  · intro path hp
    unfold taskReward
    split_ifs <;> linarith
  · cases adverse
    · exact ⟨aCold,native_budget_paths_terminal.1,(task_cold_rewards false delta good).1⟩
    · exact ⟨bCold,native_budget_paths_terminal.2.2.2,(task_cold_rewards true delta good).2.1⟩

theorem both_task_tables_generated (qids : Finset Qid) (t : TariffInput)
    (adverse : Bool) (delta good c beta Cref tolerance : ℝ) (cap : ℕ) (hc : 11 ≤ cap)
    (hm : RootMargins t c (penaltyScale qids beta Cref) delta good)
    (hw : StrictResourceWindow (qids.card : ℝ) t tolerance) (hp : ∀ a,0 ≤ tariff t a) :
    nativeGenerate budgetTape c (referencePenalty qids .complete t beta Cref)
      (physicalBill qids t) (taskBudget qids t) (taskReward adverse delta good) cap =
      aEleven (taskReward adverse delta good) ∧
    nativeGenerate budgetTape c (referencePenalty qids .next t beta Cref)
      (physicalBill qids t) (taskBudget qids t) (taskReward adverse delta good) cap =
      bTen (taskReward adverse delta good) := by
  have hg : 0 ≤ good := le_trans hm.delta_pos.le hm.delta_le_good
  have hra : 0 ≤ taskReward adverse delta good aCold := by
    rw [(task_cold_rewards adverse delta good).1]; cases adverse <;> simp [hg]
  have hrb : taskReward adverse delta good bCold ≤ good := by
    rw [(task_cold_rewards adverse delta good).2.1]; cases adverse <;> simp [hm.delta_le_good]
  exact ⟨reference_complete_generated qids t _ delta good c beta Cref tolerance cap hc
    (task_seed_table adverse delta good) hra hm hw hp,
    reference_next_generated qids t _ delta good c beta Cref tolerance cap (by omega)
      (task_seed_table adverse delta good) hrb hm hw hp⟩

def completedValue (events : List (TreeEvaluation Act)) : ℝ :=
  match bestCompleted events with | none => 0 | some best => best.reward

theorem completed_value_from_witness (events : List (TreeEvaluation Act)) (value : ℝ)
    (hu : ∀ e ∈ events,e.reward ≤ value) (he : ∃ e ∈ events,e.reward = value) :
    completedValue events = value := by
  unfold completedValue
  cases hb : bestCompleted events with
  | none =>
      have hn : events = [] := by cases events <;> simp_all [bestCompleted]
      obtain ⟨e,hem,her⟩ := he
      simp [hn] at hem
  | some best =>
      obtain ⟨hm,hmax⟩ := bestCompleted_spec events best hb
      obtain ⟨e,hem,her⟩ := he
      exact le_antisymm (hu best hm) (her ▸ hmax e hem)

theorem initialization_event_quality (reward : List Act → ℝ) (delta : ℝ)
    (hs : SeedTable reward delta) (e : TreeEvaluation Act) (he : e ∈ initialization reward) :
    e.reward = 0 ∨ e.reward = delta := by
  obtain ⟨q,hq,rfl⟩ := List.mem_map.mp he
  change reward (seedPath q) = 0 ∨ reward (seedPath q) = delta
  rw [hs q]
  split_ifs <;> simp

theorem initialization_delta_witness (reward : List Act → ℝ) (delta : ℝ)
    (hs : SeedTable reward delta) :
    ∃ e ∈ initialization reward,e.reward = delta := by
  refine ⟨seedEvent reward branchB,List.mem_map.mpr ⟨branchB,by simp,rfl⟩,?_⟩
  exact (hs branchB).trans (if_pos rfl)

theorem retained_task_best (adverse : Bool) (delta good : ℝ) (hd : 0 ≤ delta) (hg : delta ≤ good) :
    completedValue (aTen (taskReward adverse delta good)) = (if adverse then delta else good) ∧
    completedValue (bNine (taskReward adverse delta good)) = (if adverse then good else delta) := by
  have hs := task_seed_table adverse delta good
  have h0 : 0 ≤ good := hd.trans hg
  have hseed := initialization_event_quality _ delta hs
  have hw := initialization_delta_witness _ delta hs
  constructor
  · apply completed_value_from_witness
    · intro e he
      simp only [aTen,aNine,List.mem_append,List.mem_singleton] at he
      rcases he with (he | rfl) | rfl
      · rcases hseed e he with he0 | hed <;> (first | rw [he0] | rw [hed]) <;> cases adverse <;> simp [hd,h0,hg]
      · change taskReward adverse delta good aCold ≤ _
        rw [(task_cold_rewards adverse delta good).1]; cases adverse <;> simp [hd]
      · change taskReward adverse delta good aWarm ≤ _
        rw [(task_cold_rewards adverse delta good).2.2.1]; cases adverse <;> simp [hd,h0]
    · cases adverse
      · refine ⟨aColdEvent (taskReward false delta good),by simp [aTen,aNine],?_⟩
        simpa using (task_cold_rewards false delta good).1
      · obtain ⟨e,hem,her⟩ := hw
        exact ⟨e,by simp [aTen,aNine,hem],her⟩
  · apply completed_value_from_witness
    · intro e he
      simp only [bNine,List.mem_append,List.mem_singleton] at he
      rcases he with he | rfl
      · rcases hseed e he with he0 | hed <;> (first | rw [he0] | rw [hed]) <;> cases adverse <;> simp [hd,h0,hg]
      · change taskReward adverse delta good bCold ≤ _
        rw [(task_cold_rewards adverse delta good).2.1]
    · exact ⟨bColdEvent (taskReward adverse delta good),by simp [bNine],(task_cold_rewards adverse delta good).2.1⟩

end AgentUCTNativeBudget
