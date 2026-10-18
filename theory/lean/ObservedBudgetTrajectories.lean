import ObservedSelectionEquality




set_option autoImplicit false
set_option maxRecDepth 16384
set_option maxHeartbeats 4000000
set_option linter.constructorNameAsVariable false
noncomputable section
namespace AgentUCTObservability
open AgentUCTPhysicalDiagnostic AgentUCTNativeBudget AgentUCTPanelAllocation
  AgentUCTNativeRepair AgentUCTNativeRefinement AgentUCTPaper

def observedRun (qids : Finset (Fin 150)) (mode : ForecastMode) (f priors caps : Act → ℝ)
    (qid : Fin 150) (adverse : Bool) (delta good c beta Cref B : ℝ) (cap : ℕ) :=
  nativeGenerate budgetTape c (observedPenalty qids mode f priors caps qid beta Cref)
    (panelActualBill qids (fun r => f (resourceAction r))) B (taskReward adverse delta good) cap

def observedHistoryNet (qids : Finset (Fin 150)) (f : Act → ℝ) (events : List (TreeEvaluation Act))
    (B tolerance lambda Cref : ℝ) : ℝ :=
  let retained := panelReported qids (fun r => f (resourceAction r)) events B tolerance
  completedValue retained-lambda*(panelActualBill qids (fun r => f (resourceAction r)) retained)/Cref

theorem observed_reporting_index_equal (qids : Finset (Fin 150)) (f g : Act → ℝ)
    (events : List (TreeEvaluation Act)) (B tolerance : ℝ) (hp : AgreeCovered f g)
    (hh : CoveredHistory qids events) :
    panelReportingIndex qids (fun r => f (resourceAction r)) events B tolerance =
      panelReportingIndex qids (fun r => g (resourceAction r)) events B tolerance := by
  unfold panelReportingIndex
  have he : (fun n => panelActualBill qids (fun r => f (resourceAction r)) (events.take n)) =
      (fun n => panelActualBill qids (fun r => g (resourceAction r)) (events.take n)) := by
    funext n
    exact observed_actual_bills_equal qids f g _ hp
      (covered_history_prefix qids _ events (List.take_prefix _ _) hh)
  rw [he]

theorem observed_reported_prefix_equal (qids : Finset (Fin 150)) (f g : Act → ℝ)
    (events : List (TreeEvaluation Act)) (B tolerance : ℝ) (hp : AgreeCovered f g)
    (hh : CoveredHistory qids events) :
    panelReported qids (fun r => f (resourceAction r)) events B tolerance =
      panelReported qids (fun r => g (resourceAction r)) events B tolerance := by
  unfold panelReported
  rw [observed_reporting_index_equal qids f g events B tolerance hp hh]

theorem observed_history_net_equal (qids : Finset (Fin 150)) (f g : Act → ℝ)
    (events : List (TreeEvaluation Act)) (B tolerance lambda Cref : ℝ) (hp : AgreeCovered f g)
    (hh : CoveredHistory qids events) :
    observedHistoryNet qids f events B tolerance lambda Cref =
      observedHistoryNet qids g events B tolerance lambda Cref := by
  unfold observedHistoryNet
  rw [observed_reported_prefix_equal qids f g events B tolerance hp hh]
  have hc : CoveredHistory qids (panelReported qids (fun r => g (resourceAction r)) events B tolerance) :=
    covered_history_prefix qids _ events (List.take_prefix _ _) hh
  have he := observed_actual_bills_equal qids f g _ hp hc
  dsimp only
  rw [he]

theorem observed_both_full_histories_generated (qids : Finset (Fin 150)) (t : TariffInput)
    (f priors priors' caps caps' : Act → ℝ) (qid : Fin 150) (adverse : Bool)
    (delta good c beta Cref epsilon tolerance : ℝ) (cap : ℕ) (hcap : 11 ≤ cap)
    (hscale : 0 ≤ beta/Cref) (hp : AdmissibleInitialPrices t priors caps epsilon)
    (hm : RootMargins t c (penaltyScale qids beta Cref) delta good)
    (he : ErrorMargins t c (penaltyScale qids beta Cref) delta good (10*(penaltyScale qids beta Cref)*epsilon))
    (hw : StrictResourceWindow (qids.card : ℝ) t tolerance) (htariff : ∀ a,0 ≤ tariff t a)
    (hf : AgreeCovered (tariff t) f) (hprior : AgreeCovered priors priors') (hc : AgreeCovered caps caps') :
    observedRun qids .complete f priors' caps' qid adverse delta good c beta Cref (taskBudget qids t) cap =
      aEleven (taskReward adverse delta good) ∧
    observedRun qids .next f priors' caps' qid adverse delta good c beta Cref (taskBudget qids t) cap =
      bTen (taskReward adverse delta good) := by
  let reward := taskReward adverse delta good
  have hg : 0 ≤ good := hm.delta_pos.le.trans hm.delta_le_good
  have hra : 0 ≤ reward aCold := by
    dsimp only [reward]; rw [(task_cold_rewards adverse delta good).1]; cases adverse <;> simp [hg]
  have hrb : reward bCold ≤ good := by
    dsimp only [reward]; rw [(task_cold_rewards adverse delta good).2.1]; cases adverse <;> simp [hm.delta_le_good]
  obtain ⟨h1,h2,h3,h4,h5⟩ := causal_five_event_outputs qids t priors caps qid reward delta good c beta Cref epsilon
    hscale hp (task_seed_table adverse delta good) hra hrb hm he
  have hcomm (before : List (TreeEvaluation Act)) (hh : SelectionCheckpoint reward before) (mode : ForecastMode) :
      nativeEvent budgetTape c (causalPenalty qids mode t priors caps qid beta Cref) reward before =
      nativeEvent budgetTape c (observedPenalty qids mode f priors' caps' qid beta Cref) reward before :=
    observed_checkpoint_events_equal qids (tariff t) f priors priors' caps caps' qid before reward hf hprior hc hh mode c beta Cref
  have h1' := (hcomm _ (Or.inl rfl) .complete).symm.trans h1
  have h2' := (hcomm _ (Or.inl rfl) .next).symm.trans h2
  have h3' := (hcomm _ (Or.inr (Or.inl rfl)) .complete).symm.trans h3
  have h4' := (hcomm _ (Or.inr (Or.inr (Or.inl rfl))) .complete).symm.trans h4
  have h5' := (hcomm _ (Or.inr (Or.inr (Or.inr rfl))) .next).symm.trans h5
  have hbill (events : List (TreeEvaluation Act)) (hh : CoveredHistory qids events) :
      panelActualBill qids (fun r => f (resourceAction r)) events = physicalBill qids t events :=
    (observed_actual_bills_equal qids (tariff t) f events hf hh).symm
  have hi := initial_bill_below_task_budget qids t reward tolerance hw htariff
  obtain ⟨ha,hb,hac,hbc⟩ := strict_window_endpoints qids t reward tolerance hw
  have ha9 : physicalBill qids t (aNine reward) < taskBudget qids t := by
    rw [physical_a9_bill]; rwa [physical_a10_bill] at ha
  have hfulla : CoveredHistory qids (aEleven reward) := (companion_panel_caches_covered qids reward).1
  have hfullb : CoveredHistory qids (bTen reward) := (companion_panel_caches_covered qids reward).2
  have hxa : taskBudget qids t ≤ panelActualBill qids (fun r => f (resourceAction r)) (aEleven reward) := by
    rw [hbill _ hfulla]; exact (le_add_of_nonneg_right hw.2.2.2.2.1).trans hac.le
  have hxb : taskBudget qids t ≤ panelActualBill qids (fun r => f (resourceAction r)) (bTen reward) := by
    rw [hbill _ hfullb]; exact (le_add_of_nonneg_right hw.2.2.2.2.1).trans hbc.le
  constructor
  · unfold observedRun nativeGenerate
    rw [budget_common_eight_initialization,show cap-8 = (cap-11)+3 by omega,
      show (cap-11)+3 = ((cap-11)+2)+1 by omega,nativeAfter]
    simp only [targetReached]
    rw [hbill _ (checkpoint_covered qids reward _ (Or.inl rfl)),if_neg (not_le.mpr hi),h1']
    change nativeAfter budgetTape c (observedPenalty qids .complete f priors' caps' qid beta Cref)
      (panelActualBill qids (fun r => f (resourceAction r))) (taskBudget qids t) reward ((cap-11)+2) (aNine reward) = _
    rw [show (cap-11)+2 = ((cap-11)+1)+1 by omega,nativeAfter]
    simp only [targetReached]
    rw [hbill _ (checkpoint_covered qids reward _ (Or.inr (Or.inl rfl))),if_neg (not_le.mpr ha9),h3']
    change nativeAfter budgetTape c (observedPenalty qids .complete f priors' caps' qid beta Cref)
      (panelActualBill qids (fun r => f (resourceAction r))) (taskBudget qids t) reward ((cap-11)+1) (aTen reward) = _
    rw [nativeAfter]
    simp only [targetReached]
    rw [hbill _ (checkpoint_covered qids reward _ (Or.inr (Or.inr (Or.inl rfl)))),if_neg (not_le.mpr ha),h4']
    exact native_after_crossing_stops budgetTape c _ _ _ reward (aEleven reward) hxa (cap-11)
  · unfold observedRun nativeGenerate
    rw [budget_common_eight_initialization,show cap-8 = (cap-10)+2 by omega,
      show (cap-10)+2 = ((cap-10)+1)+1 by omega,nativeAfter]
    simp only [targetReached]
    rw [hbill _ (checkpoint_covered qids reward _ (Or.inl rfl)),if_neg (not_le.mpr hi),h2']
    change nativeAfter budgetTape c (observedPenalty qids .next f priors' caps' qid beta Cref)
      (panelActualBill qids (fun r => f (resourceAction r))) (taskBudget qids t) reward ((cap-10)+1) (bNine reward) = _
    rw [nativeAfter]
    simp only [targetReached]
    rw [hbill _ (checkpoint_covered qids reward _ (Or.inr (Or.inr (Or.inr rfl)))),if_neg (not_le.mpr hb),h5']
    exact native_after_crossing_stops budgetTape c _ _ _ reward (bTen reward) hxb (cap-10)

end AgentUCTObservability
