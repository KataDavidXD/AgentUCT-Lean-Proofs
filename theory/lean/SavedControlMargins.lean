import SavedBudgetBoundary



set_option autoImplicit false
set_option maxRecDepth 16384
set_option maxHeartbeats 4000000
noncomputable section
namespace AgentUCTSavedBudget
open AgentUCTObservability AgentUCTObservabilityBoundary AgentUCTPhysicalDiagnostic
  AgentUCTNativeBudget AgentUCTPanelAllocation AgentUCTNativeRepair AgentUCTNativeRefinement AgentUCTPaper

def savedCref : ℝ := 1470690.0198555747
def savedTarget : ℝ := 32000000
def savedScale : ℝ := (150:ℝ)*2/savedCref

theorem saved_cref_positive : 0 < savedCref := by norm_num [savedCref]

theorem saved_scale_is_panel_penalty : penaltyScale panel150 2 savedCref = savedScale := by
  simp only [penaltyScale,savedScale,AgentUCTNativeBudget.panel150_cardinality]
  ring

theorem saved_controls_root_margins :
    RootMargins integerTariffs (7/5) savedScale (2/5) (1/2) := by
  obtain ⟨hlo,hhi,h3⟩ := fixed_exploration_bounds
  constructor <;>
    norm_num [integerTariffs,generatorRate,e5Rate,bgeRate,embeddingRate,
      normalForecastBill,tailBill,savedScale,savedCref] <;> linarith

theorem saved_controls_nonzero_error_inputs :
    ∃ epsilon : ℝ,0 < epsilon ∧
      AdmissibleInitialPrices integerTariffs (perturbedPriors integerTariffs epsilon)
        (perturbedCaps integerTariffs epsilon) epsilon ∧
      ErrorMargins integerTariffs (7/5) savedScale (2/5) (1/2) (10*savedScale*epsilon) := by
  obtain ⟨epsilon,he,hh,hm⟩ := root_margin_positive_error_exists integerTariffs _ _ _ _ saved_controls_root_margins
  exact ⟨epsilon,he,perturbed_initial_prices_admissible _ _ he hh integer_tariffs_positive_floor,hm⟩

theorem saved_cref_retained_gap_bracket :
    (2/5:ℝ)-1/2 < (1/20)*(panel150.card : ℝ)*(integerTariffs.bge-integerTariffs.normalE5)/savedCref ∧
    (1/20)*(panel150.card : ℝ)*(integerTariffs.bge-integerTariffs.normalE5)/savedCref < (1/2:ℝ)-2/5 := by
  rw [AgentUCTNativeBudget.panel150_cardinality]
  norm_num [integerTariffs,generatorRate,e5Rate,bgeRate,savedCref]

def ReferenceControlInterval (Cref : ℝ) : Prop := 1470000 ≤ Cref ∧ Cref ≤ 1471000

theorem saved_reference_in_control_interval : ReferenceControlInterval savedCref := by
  norm_num [ReferenceControlInterval,savedCref]

theorem independent_reference_in_control_interval :
    ReferenceControlInterval (classCref panel150 integerTariffs) := by
  rw [panel150_integer_cref]
  norm_num [ReferenceControlInterval,generatorRate]

theorem interval_root_margins (Cref : ℝ) (hC : ReferenceControlInterval Cref) :
    RootMargins integerTariffs (7/5) ((150:ℝ)*2/Cref) (2/5) (1/2) := by
  have hcpos : 0 < Cref := by rcases hC with ⟨hl,hu⟩; linarith
  let gamma : ℝ := 300/Cref
  have hgpos : 0 < gamma := div_pos (by norm_num) hcpos
  have hprod : gamma*Cref = 300 := by dsimp only [gamma]; field_simp
  have hglo : (300:ℝ)/1471000 ≤ gamma := by
    have hm := mul_le_mul_of_nonneg_left hC.2 hgpos.le
    rw [hprod] at hm
    nlinarith
  have hghi : gamma ≤ (300:ℝ)/1470000 := by
    have hm := mul_le_mul_of_nonneg_left hC.1 hgpos.le
    rw [hprod] at hm
    nlinarith
  obtain ⟨hlo,hhi,h3⟩ := fixed_exploration_bounds
  have hs : (150:ℝ)*2/Cref = gamma := by dsimp only [gamma]; norm_num
  rw [hs]
  constructor <;> norm_num [integerTariffs,generatorRate,e5Rate,bgeRate,embeddingRate,
    normalForecastBill,tailBill] <;> nlinarith

theorem interval_nonzero_price_and_index_error_inputs (Cref : ℝ) (hC : ReferenceControlInterval Cref) :
    ∃ epsilon sigma : ℝ,0 < epsilon ∧ 0 < sigma ∧
      AdmissibleInitialPrices integerTariffs (perturbedPriors integerTariffs epsilon)
        (perturbedCaps integerTariffs epsilon) epsilon ∧
      ErrorMargins integerTariffs (7/5) ((150:ℝ)*2/Cref) (2/5) (1/2)
        (10*((150:ℝ)*2/Cref)*epsilon+sigma) := by
  have root := interval_root_margins Cref hC
  obtain ⟨e,he,hehalf,hm⟩ := root_margin_positive_error_exists integerTariffs _ _ _ _ root
  let epsilon := e/2
  let sigma := 5*((150:ℝ)*2/Cref)*e/2
  have ep : 0 < epsilon := by dsimp only [epsilon]; linarith
  have eh : epsilon < 1/2 := by dsimp only [epsilon]; linarith
  have hgamma : 0 < (150:ℝ)*2/Cref := root.gamma_pos
  have sp : 0 < sigma := by dsimp only [sigma]; positivity
  have ele : 10*((150:ℝ)*2/Cref)*epsilon+sigma ≤ 10*((150:ℝ)*2/Cref)*e := by
    dsimp only [epsilon,sigma]; nlinarith [root.gamma_pos]
  refine ⟨epsilon,sigma,ep,sp,perturbed_initial_prices_admissible _ _ ep eh integer_tariffs_positive_floor,?_⟩
  cases hm
  constructor <;> linarith

theorem interval_nonzero_quote_error_inputs (Cref : ℝ) (hC : ReferenceControlInterval Cref) :
    ∃ epsilon : ℝ,0 < epsilon ∧
      AdmissibleInitialPrices integerTariffs (perturbedPriors integerTariffs epsilon)
        (perturbedCaps integerTariffs epsilon) epsilon ∧
      ErrorMargins integerTariffs (7/5) ((150:ℝ)*2/Cref) (2/5) (1/2)
        (10*((150:ℝ)*2/Cref)*epsilon) := by
  obtain ⟨e,he,hehalf,hm⟩ := root_margin_positive_error_exists integerTariffs _ _ _ _ (interval_root_margins Cref hC)
  exact ⟨e,he,perturbed_initial_prices_admissible _ _ he hehalf integer_tariffs_positive_floor,hm⟩

theorem interval_penalty_scale_bounds (Cref : ℝ) (hC : ReferenceControlInterval Cref) :
    (300:ℝ)/1471000 ≤ (150:ℝ)*2/Cref ∧ (150:ℝ)*2/Cref ≤ (300:ℝ)/1470000 := by
  have hcpos : 0 < Cref := by rcases hC with ⟨hl,hu⟩; linarith
  have hgpos : 0 < (150:ℝ)*2/Cref := by positivity
  have hprod : ((150:ℝ)*2/Cref)*Cref = 300 := by field_simp; norm_num
  constructor
  · have hm := mul_le_mul_of_nonneg_left hC.2 hgpos.le
    rw [hprod] at hm
    nlinarith
  · have hm := mul_le_mul_of_nonneg_left hC.1 hgpos.le
    rw [hprod] at hm
    nlinarith

def uniformQuoteError : ℝ := 1/1000000
def uniformIndexError : ℝ := 1/1000

theorem uniform_nonzero_error_inputs (Cref : ℝ) (hC : ReferenceControlInterval Cref) :
    0 < uniformQuoteError ∧ 0 < uniformIndexError ∧
    AdmissibleInitialPrices integerTariffs (perturbedPriors integerTariffs uniformQuoteError)
      (perturbedCaps integerTariffs uniformQuoteError) uniformQuoteError ∧
    ErrorMargins integerTariffs (7/5) ((150:ℝ)*2/Cref) (2/5) (1/2)
      (10*((150:ℝ)*2/Cref)*uniformQuoteError+uniformIndexError) := by
  obtain ⟨hglo,hghi⟩ := interval_penalty_scale_bounds Cref hC
  obtain ⟨hlo,hhi,h3⟩ := fixed_exploration_bounds
  refine ⟨by norm_num [uniformQuoteError],by norm_num [uniformIndexError],
    perturbed_initial_prices_admissible _ _ (by norm_num [uniformQuoteError])
      (by norm_num [uniformQuoteError]) integer_tariffs_positive_floor,?_⟩
  constructor <;> norm_num [uniformQuoteError,uniformIndexError,integerTariffs,
    generatorRate,e5Rate,bgeRate,embeddingRate,normalForecastBill,tailBill] <;> nlinarith

theorem uniform_quote_only_error_inputs (Cref : ℝ) (hC : ReferenceControlInterval Cref) :
    AdmissibleInitialPrices integerTariffs (perturbedPriors integerTariffs uniformQuoteError)
      (perturbedCaps integerTariffs uniformQuoteError) uniformQuoteError ∧
    ErrorMargins integerTariffs (7/5) ((150:ℝ)*2/Cref) (2/5) (1/2)
      (10*((150:ℝ)*2/Cref)*uniformQuoteError) := by
  obtain ⟨hep,hsp,hp,hm⟩ := uniform_nonzero_error_inputs Cref hC
  refine ⟨hp,?_⟩
  cases hm
  constructor <;> linarith

theorem uniform_initial_bge_quote_error_positive (reward : List Act → ℝ) :
    0 < |liveReceiptPrice (perturbedPriors integerTariffs uniformQuoteError)
      (perturbedCaps integerTariffs uniformQuoteError)
      (taskMeans panel150 integerTariffs (perturbedCaps integerTariffs uniformQuoteError) (0:Fin 150)
        (initialization reward)) ((0:Fin 150),aCold.take 2)-integerTariffs.bge| := by
  exact common_initial_bge_actual_nonzero_error panel150 integerTariffs (0:Fin 150) reward
    uniformQuoteError (by norm_num [uniformQuoteError]) (by norm_num [integerTariffs,bgeRate])

end AgentUCTSavedBudget
