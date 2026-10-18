import RepairResolver



set_option autoImplicit false
set_option maxRecDepth 8192
set_option maxHeartbeats 3000000
noncomputable section
namespace AgentUCTNativeRepair
open AgentUCTNativeRefinement AgentUCTPaper

theorem preferred_action_legal {p : List Act} (hp : Legal p) (hne : available p ≠ []) :
    preferredAction p ∈ available p := by
  cases legal_shape hp <;>
    simp_all [preferredAction,finish,fullLeaf,seedPath,leaf,seedRetriever,available,rootOrder,retrievers]
  split_ifs <;> simp_all

theorem finish_stable_next {p : List Act} (hp : Legal p) (hne : available p ≠ []) :
    finish (p++[preferredAction p]) = finish p := by
  cases legal_shape hp <;>
    simp_all [preferredAction,finish,fullLeaf,seedPath,leaf,seedRetriever,available]

theorem finish_terminal_identity {p : List Act} (hp : Terminal p) : finish p = p := by
  obtain ⟨hl,hlen⟩ := hp
  cases legal_shape hl <;> simp_all [finish,fullLeaf]

theorem explicit_rollout_action {p : List Act} (hp : Legal p) (hne : available p ≠ [])
    (before : List (TreeEvaluation Act)) :
    explicitTape.action before .rollout p (orderedLegalAvailable p) = preferredAction p := by
  have hm := (ordered_legal_member_iff hp _).mpr (preferred_action_legal hp hne)
  simp [explicitTape,hm]

theorem explicit_rollout_finish (before : List (TreeEvaluation Act)) (fuel : ℕ) (p : List Act)
    (hp : Legal p) (hfuel : 9 ≤ fuel+p.length) :
    repairedRollout explicitTape before fuel p = finish p := by
  induction fuel generalizing p with
  | zero =>
      have ht : Terminal p := ⟨hp,by have hl := legal_length_le_nine hp; omega⟩
      simpa [repairedRollout] using (finish_terminal_identity ht).symm
  | succ fuel ih =>
      simp only [repairedRollout]
      split_ifs with hnil
      · have ht := (legal_no_actions_iff_terminal hp).mp ((ordered_legal_nil_iff hp).mp hnil)
        exact (finish_terminal_identity ht).symm
      · have hn : available p ≠ [] := fun h => hnil ((ordered_legal_nil_iff hp).mpr h)
        rw [explicit_rollout_action hp hn before]
        rw [ih _ ((legal_append_action _ _).mpr ⟨hp,preferred_action_legal hp hn⟩)
          (by simp only [List.length_append,List.length_singleton]; omega)]
        exact finish_stable_next hp hn

theorem repaired_explicit_seed_terminal (before : List (TreeEvaluation Act)) (q : Fin 8) :
    repairedRollout explicitTape before 9 [.query q] = seedPath q := by
  have hl : Legal [.query q] := by simp [Legal,followLegal,available,rootOrder]
  simpa [finish] using explicit_rollout_finish before 9 [.query q] hl (by simp)

theorem explicit_initial_event (reward : List Act → ℝ) (before : List (TreeEvaluation Act)) (q : Fin 8) :
    initialEvent explicitTape reward before q = seedEvent reward q := by
  simp [initialEvent,repaired_explicit_seed_terminal,seedEvent]

theorem explicit_common_initialization (reward : List Act → ℝ) :
    repairedInitialization explicitTape reward = initialization reward := by
  simp [repairedInitialization,initialization,finRange8_explicit,initializeFrom,explicit_initial_event]

theorem generated_common_initialization_cold_bill (reward : List Act → ℝ) (q a e b k : ℝ) :
    (ownState (price q a e b k) (repairedInitialization explicitTape reward)).totalPaid = 7*q+16*a+e := by
  rw [explicit_common_initialization]
  exact initialization_full_cold_bill reward q a e b k

theorem generated_initial_root_backup (reward : List Act → ℝ) :
    (replayBackup (repairedInitialization explicitTape reward) emptyStatistics []).visits = 8 := by
  rw [explicit_common_initialization]
  exact initialization_root_visits reward

theorem generated_initial_child_backup (reward : List Act → ℝ) (q : Fin 8) :
    (replayBackup (repairedInitialization explicitTape reward) emptyStatistics [.query q]).visits = 1 ∧
    (replayBackup (repairedInitialization explicitTape reward) emptyStatistics [.query q]).mean = reward (seedPath q) := by
  rw [explicit_common_initialization]
  exact initialization_child_stats reward q

theorem generated_initial_deeper_unvisited (reward : List Act → ℝ) (q : Fin 8) (r : Act) :
    (replayBackup (repairedInitialization explicitTape reward) emptyStatistics [.query q,r]).visits = 0 := by
  rw [explicit_common_initialization]
  exact initialization_deeper_nodes_unvisited reward q r

theorem generated_initial_cache_exact (reward : List Act → ℝ) :
    ownCache (repairedInitialization explicitTape reward) = initialCache := by
  rw [explicit_common_initialization]
  exact initialization_cache_exact reward

theorem generated_initial_terminals_distinct (reward : List Act → ℝ) :
    ((repairedInitialization explicitTape reward).map TreeEvaluation.terminal).Nodup := by
  rw [explicit_common_initialization]
  simpa [initialization,seedEvent,List.map_map,Function.comp_def] using
    List.Nodup.map seedPath_injective (List.nodup_finRange 8)

theorem repaired_after_init_prefix (mode : ForecastMode) (tape : SharedTape)
    (prices : Unit × List Act → ℝ) (c gamma B : ℝ) (reward : List Act → ℝ)
    (fuel : ℕ) (before : List (TreeEvaluation Act)) :
    before <+: repairedAfterInit mode tape prices c gamma B reward fuel before := by
  induction fuel generalizing before with
  | zero => exact List.prefix_refl _
  | succ fuel ih =>
      simp only [repairedAfterInit]
      split_ifs
      · exact List.prefix_refl _
      · exact (List.prefix_append _ _).trans (ih _)

theorem generated_initialization_prefix (mode : ForecastMode) (tape : SharedTape)
    (prices : Unit × List Act → ℝ) (c gamma B : ℝ) (cap : ℕ) (reward : List Act → ℝ) :
    repairedInitialization tape reward <+: repairedGenerate mode tape prices c gamma B cap reward :=
  repaired_after_init_prefix mode tape prices c gamma B reward _ _

theorem generated_count_cap (mode : ForecastMode) (tape : SharedTape)
    (prices : Unit × List Act → ℝ) (c gamma B : ℝ) (cap : ℕ) (reward : List Act → ℝ)
    (hcap : 8 ≤ cap) : (repairedGenerate mode tape prices c gamma B cap reward).length ≤ cap := by
  have h : ∀ fuel before,
      (repairedAfterInit mode tape prices c gamma B reward fuel before).length ≤ before.length+fuel := by
    intro fuel
    induction fuel with
    | zero => intro before; simp [repairedAfterInit]
    | succ fuel ih =>
        intro before
        simp only [repairedAfterInit]
        split_ifs
        · omega
        · have hh := ih (before++[repairedEvent mode tape prices c gamma reward before])
          simp only [List.length_append,List.length_singleton] at hh
          omega
  have hh := h (cap-8) (repairedInitialization tape reward)
  rw [repaired_initialization_eight] at hh
  exact hh.trans (by omega)

theorem generated_actual_cost_stop (mode : ForecastMode) (tape : SharedTape)
    (prices : Unit × List Act → ℝ) (c gamma B : ℝ) (cap : ℕ) (reward : List Act → ℝ)
    (hcost : targetReached (ownState prices (repairedInitialization tape reward)).totalPaid B) :
    repairedGenerate mode tape prices c gamma B cap reward = repairedInitialization tape reward := by
  unfold repairedGenerate
  cases cap-8 <;> simp [repairedAfterInit,hcost]

def repairedReported (mode : ForecastMode) (tape : SharedTape)
    (prices : Unit × List Act → ℝ) (c gamma B : ℝ) (cap : ℕ) (reward : List Act → ℝ) :
    List (TreeEvaluation Act) :=
  let run := repairedGenerate mode tape prices c gamma B cap reward
  run.take (T_B (fun n => (ownState prices (run.take n)).totalPaid) run.length B snapshotTolerance)

theorem repaired_reported_legal (mode : ForecastMode) (tape : SharedTape)
    (ht : LegalSupportedTape tape) (prices : Unit × List Act → ℝ) (c gamma B : ℝ)
    (cap : ℕ) (reward : List Act → ℝ) :
    ValidHistory (repairedReported mode tape prices c gamma B cap reward) := by
  intro e he
  exact repaired_generated_legality mode tape ht prices c gamma B cap reward e
    (List.mem_of_mem_take he)

end AgentUCTNativeRepair
