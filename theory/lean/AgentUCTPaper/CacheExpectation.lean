import AgentUCTPaper.Cache
import Mathlib.MeasureTheory.Function.ConditionalExpectation.Basic

/-! # Expected cold-cost forecasts inherit the persistent-cache budget

The pathwise bound comes from actual successful materialization, not an assumed
bound on forecasts. The expectation step uses genuine conditional expectation.
Conditioning sigma-fields should contain the decision whose cost is forecast;
the algebra needs only that they are sub-sigma-fields of the ambient space.
-/

noncomputable section

open Finset MeasureTheory

namespace AgentUCTPaper

variable {Resource Ω : Type*} [DecidableEq Resource]

/-- Omitted actual cold work is charged against the same persistent materialization
ledger. It cannot exceed the weight of all newly materialized resources. -/
theorem omitted_cold_sum_bounds (weight : Resource → ℝ)
    (hnonneg : ∀ resource, 0 ≤ weight resource)
    (cached demand : Ω → ℕ → Finset Resource) (initial resourceSet : Finset Resource)
    (horizon : ℕ)
    (hinitial : ∀ ω, cached ω 0 = initial)
    (hstep : ∀ ω t, cached ω (t + 1) = cached ω t ∪ demand ω t)
    (hfinite : ∀ ω, cached ω horizon ⊆ resourceSet)
    (actual : Ω → ℕ → ℝ)
    (hactual : ∀ ω t, t ∈ range horizon →
      0 ≤ actual ω t ∧ actual ω t ≤ coldWork weight (cached ω t) (demand ω t))
    (ω : Ω) :
    0 ≤ ∑ t ∈ range horizon, actual ω t ∧
      (∑ t ∈ range horizon, actual ω t) ≤
        cacheWeight weight resourceSet - cacheWeight weight initial := by
  constructor
  · exact sum_nonneg fun t ht => (hactual ω t ht).1
  · calc
      (∑ t ∈ range horizon, actual ω t) ≤
          ∑ t ∈ range horizon, coldWork weight (cached ω t) (demand ω t) :=
        sum_le_sum fun t ht => (hactual ω t ht).2
      _ ≤ cacheWeight weight resourceSet - cacheWeight weight initial := by
        simpa only [hinitial ω] using cumulative_coldWork_le_universe weight hnonneg
          (cached ω) (demand ω) (hstep ω) horizon resourceSet (hfinite ω)

variable [mΩ : MeasurableSpace Ω]

/-- Integrating the actual pathwise materialization bound gives the expected budget.
Integrability is an explicit interface; no measurability of the random ledger is
silently inferred from its finite-set representation. -/
theorem expected_omitted_cold_budget (P : Measure Ω) [IsProbabilityMeasure P]
    (weight : Resource → ℝ) (hnonneg : ∀ resource, 0 ≤ weight resource)
    (cached demand : Ω → ℕ → Finset Resource) (initial resourceSet : Finset Resource)
    (horizon : ℕ)
    (hinitial : ∀ ω, cached ω 0 = initial)
    (hstep : ∀ ω t, cached ω (t + 1) = cached ω t ∪ demand ω t)
    (hfinite : ∀ ω, cached ω horizon ⊆ resourceSet)
    (actual : Ω → ℕ → ℝ)
    (hactual : ∀ ω t, t ∈ range horizon →
      0 ≤ actual ω t ∧ actual ω t ≤ coldWork weight (cached ω t) (demand ω t))
    (hintegrable : Integrable (fun ω => ∑ t ∈ range horizon, actual ω t) P) :
    (∫ ω, ∑ t ∈ range horizon, actual ω t ∂P) ≤
      cacheWeight weight resourceSet - cacheWeight weight initial := by
  calc
    (∫ ω, ∑ t ∈ range horizon, actual ω t ∂P) ≤
        ∫ _, (cacheWeight weight resourceSet - cacheWeight weight initial) ∂P :=
      integral_mono_ae hintegrable (integrable_const _) (Filter.Eventually.of_forall
        fun ω => (omitted_cold_sum_bounds weight hnonneg cached demand initial resourceSet
          horizon hinitial hstep hfinite actual hactual ω).2)
    _ = cacheWeight weight resourceSet - cacheWeight weight initial := by simp

omit [DecidableEq Resource] in
/-- The conditional expectation of the selected actual cold bill. Its conditioning
information is supplied explicitly and can include the already chosen action. -/
def conditionalColdForecast (P : Measure Ω) (info : ℕ → MeasurableSpace Ω)
    (actual : Ω → ℕ → ℝ) (ω : Ω) (t : ℕ) : ℝ :=
  (P[fun x => actual x t | info t]) ω

omit [DecidableEq Resource] in
/-- Every finite sum of canonical conditional-expectation forecasts is integrable. -/
theorem integrable_conditionalColdForecast_sum (P : Measure Ω)
    (info : ℕ → MeasurableSpace Ω) (actual : Ω → ℕ → ℝ) (horizon : ℕ) :
    Integrable (fun ω => ∑ t ∈ range horizon,
      conditionalColdForecast P info actual ω t) P := by
  exact integrable_finset_sum _ fun _ _ => integrable_condExp

omit [DecidableEq Resource] in
/-- Conditional unbiasedness conserves total expected cost. This is proved from
`integral_condExp`, not supplied as a hypothesis on the cumulative forecasts. -/
theorem integral_forecast_sum_eq_actual (P : Measure Ω) [IsProbabilityMeasure P]
    (info : ℕ → MeasurableSpace Ω) (hinfo : ∀ t, info t ≤ mΩ)
    (actual forecast : Ω → ℕ → ℝ) (horizon : ℕ)
    (hintegrable : ∀ t ∈ range horizon, Integrable (fun ω => actual ω t) P)
    (hforecast : ∀ t ∈ range horizon,
      (fun ω => forecast ω t) =ᵐ[P] (fun ω => conditionalColdForecast P info actual ω t)) :
    (∫ ω, ∑ t ∈ range horizon, forecast ω t ∂P) =
      ∫ ω, ∑ t ∈ range horizon, actual ω t ∂P := by
  have hforecastInt : ∀ t ∈ range horizon, Integrable (fun ω => forecast ω t) P := by
    intro t ht
    exact integrable_condExp.congr (hforecast t ht).symm
  rw [integral_finset_sum _ hforecastInt, integral_finset_sum _ hintegrable]
  apply sum_congr rfl
  intro t ht
  calc
    (∫ ω, forecast ω t ∂P) = ∫ ω, conditionalColdForecast P info actual ω t ∂P :=
      integral_congr_ae (hforecast t ht)
    _ = ∫ ω, actual ω t ∂P := integral_condExp (hinfo t)

/-- The finite qid-prefix materialization budget also bounds the expected sum of
conditionally unbiased omitted-cold-cost forecasts, even for adaptive cache demands.
Only the actual cold component is covered; repeatedly incurred overhead is separate. -/
theorem expected_forecast_cold_budget (P : Measure Ω) [IsProbabilityMeasure P]
    (weight : Resource → ℝ) (hnonneg : ∀ resource, 0 ≤ weight resource)
    (cached demand : Ω → ℕ → Finset Resource) (initial resourceSet : Finset Resource)
    (horizon : ℕ)
    (hinitial : ∀ ω, cached ω 0 = initial)
    (hstep : ∀ ω t, cached ω (t + 1) = cached ω t ∪ demand ω t)
    (hfinite : ∀ ω, cached ω horizon ⊆ resourceSet)
    (actual forecast : Ω → ℕ → ℝ)
    (hactual : ∀ ω t, t ∈ range horizon →
      0 ≤ actual ω t ∧ actual ω t ≤ coldWork weight (cached ω t) (demand ω t))
    (hintegrable : ∀ t ∈ range horizon, Integrable (fun ω => actual ω t) P)
    (info : ℕ → MeasurableSpace Ω) (hinfo : ∀ t, info t ≤ mΩ)
    (hforecast : ∀ t ∈ range horizon,
      (fun ω => forecast ω t) =ᵐ[P] (fun ω => conditionalColdForecast P info actual ω t)) :
    (∫ ω, ∑ t ∈ range horizon, forecast ω t ∂P) ≤
      cacheWeight weight resourceSet - cacheWeight weight initial := by
  rw [integral_forecast_sum_eq_actual P info hinfo actual forecast horizon hintegrable hforecast]
  exact expected_omitted_cold_budget P weight hnonneg cached demand initial resourceSet horizon
    hinitial hstep hfinite actual hactual (integrable_finset_sum _ hintegrable)

end AgentUCTPaper
