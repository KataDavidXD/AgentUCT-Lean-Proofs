import NativeBudgetForecast




set_option autoImplicit false
set_option maxRecDepth 16384
set_option maxHeartbeats 4000000
set_option linter.constructorNameAsVariable false
noncomputable section
namespace AgentUCTNativeBudget
open AgentUCTPanelAllocation AgentUCTNativeRepair AgentUCTNativeRefinement AgentUCTPaper
variable {Qid : Type*} [DecidableEq Qid]

def SeedTable (reward : List Act → ℝ) (delta : ℝ) : Prop :=
  ∀ q, reward (seedPath q) = if q = branchB then delta else 0

def referencePenalty (qids : Finset Qid) (mode : ForecastMode) (t : TariffInput) (beta Cref : ℝ)
    (before : List (TreeEvaluation Act)) (p : List Act) (a : Act) : ℝ :=
  (beta/Cref)*sourcePanelMC16 qids mode (ownPanelCache qids before) (fun _ _ => false)
    (fun r => tariff t (resourceAction r)) (budgetTape.completion before p a)

def penaltyScale (qids : Finset Qid) (beta Cref : ℝ) : ℝ := (beta/Cref)*(qids.card : ℝ)

theorem reference_penalty_root (qids : Finset Qid) (mode : ForecastMode) (t : TariffInput)
    (beta Cref : ℝ) (before : List (TreeEvaluation Act)) (q : Fin 8) :
    referencePenalty qids mode t beta Cref before [] (.query q) =
      (beta/Cref)*tariffRootForecast qids mode t before q := rfl

theorem initial_complete_index (qids : Finset Qid) (t : TariffInput) (reward : List Act → ℝ)
    (delta c beta Cref : ℝ) (hs : SeedTable reward delta) (q : Fin 8) :
    indexScore c (referencePenalty qids .complete t beta Cref) (initialization reward) [] (.query q) =
      (if q = branchB then delta else 0)+c*Real.sqrt (Real.log 9)-penaltyScale qids beta Cref*
        (if q = hyde then t.bge+tailBill t else normalForecastBill t) := by
  unfold SeedTable at hs
  simp only [indexScore,List.nil_append,reference_penalty_root,tariff_initial_complete_root,rawVisits,
    initial_root_stat_exact,replayBackup_root_visits]
  simp only [initialization,List.length_map,List.length_finRange,treeIndex,treeBonus,
    BackupStat.mean,Nat.cast_one,div_one,hs,penaltyScale]
  norm_num
  ring

theorem initial_next_index (qids : Finset Qid) (t : TariffInput) (reward : List Act → ℝ)
    (delta c beta Cref : ℝ) (hs : SeedTable reward delta) (hb : 0 < t.bge) (hw : 0 < t.w4) (q : Fin 8) :
    indexScore c (referencePenalty qids .next t beta Cref) (initialization reward) [] (.query q) =
      (if q = branchB then delta else 0)+c*Real.sqrt (Real.log 9)-penaltyScale qids beta Cref*
        (if q = hyde then t.bge else t.w4) := by
  unfold SeedTable at hs
  simp only [indexScore,List.nil_append,reference_penalty_root,tariff_initial_next_root qids t reward hb hw,
    rawVisits,initial_root_stat_exact,replayBackup_root_visits]
  simp only [initialization,List.length_map,List.length_finRange,treeIndex,treeBonus,
    BackupStat.mean,Nat.cast_one,div_one,hs,penaltyScale]
  norm_num
  ring

theorem a9_complete_index (qids : Finset Qid) (t : TariffInput) (reward : List Act → ℝ)
    (delta c beta Cref : ℝ) (hs : SeedTable reward delta) (q : Fin 8) :
    indexScore c (referencePenalty qids .complete t beta Cref) (aNine reward) [] (.query q) =
      if q = hyde then reward aCold/2+c*Real.sqrt (Real.log 10/2) else
      (if q = branchB then delta else 0)+c*Real.sqrt (Real.log 10)-penaltyScale qids beta Cref*normalForecastBill t := by
  unfold SeedTable at hs
  simp only [indexScore,List.nil_append,reference_penalty_root,tariff_a9_complete_root,rawVisits,
    a9_root_child_statistics,replayBackup_root_visits]
  fin_cases q <;> simp +decide [treeIndex,treeBonus,BackupStat.mean,aNine,initialization,hyde,branchB,hs,penaltyScale] <;> ring

theorem a10_complete_index (qids : Finset Qid) (t : TariffInput) (reward : List Act → ℝ)
    (delta c beta Cref : ℝ) (hs : SeedTable reward delta) (q : Fin 8) :
    indexScore c (referencePenalty qids .complete t beta Cref) (aTen reward) [] (.query q) =
      if q = hyde then reward aCold/3+c*Real.sqrt (Real.log 11/3) else
      (if q = branchB then delta else 0)+c*Real.sqrt (Real.log 11)-penaltyScale qids beta Cref*normalForecastBill t := by
  unfold SeedTable at hs
  simp only [indexScore,List.nil_append,reference_penalty_root,tariff_a10_complete_root,rawVisits,
    a10_root_child_statistics,replayBackup_root_visits]
  fin_cases q <;> simp +decide [treeIndex,treeBonus,BackupStat.mean,aTen,aNine,initialization,hyde,branchB,hs,penaltyScale] <;> ring

theorem b9_next_index (qids : Finset Qid) (t : TariffInput) (reward : List Act → ℝ)
    (delta c beta Cref : ℝ) (hs : SeedTable reward delta) (hb : 0 < t.bge) (hw : 0 < t.w4) (q : Fin 8) :
    indexScore c (referencePenalty qids .next t beta Cref) (bNine reward) [] (.query q) =
      if q = branchB then (delta+reward bCold)/2+c*Real.sqrt (Real.log 10/2)-penaltyScale qids beta Cref*t.w4 else
      c*Real.sqrt (Real.log 10)-penaltyScale qids beta Cref*(if q = hyde then t.bge else t.w4) := by
  unfold SeedTable at hs
  simp only [indexScore,List.nil_append,reference_penalty_root,tariff_b9_next_root qids t reward hb hw,rawVisits,
    b9_root_child_statistics,replayBackup_root_visits]
  fin_cases q <;> simp +decide [treeIndex,treeBonus,BackupStat.mean,bNine,initialization,hyde,branchB,hs,penaltyScale] <;> ring

end AgentUCTNativeBudget
