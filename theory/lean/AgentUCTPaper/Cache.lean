import AgentUCT

/-! # Exact accounting for persistent qid-prefix materialization

A resource can be a qid-prefix pair with any additional execution-identity fields.
The cache is a finite set of materialized resources.  These results concern the
fixed physical cost attached to each resource, not a changing cost forecast.
-/

noncomputable section

open Finset

namespace AgentUCTPaper

variable {Resource : Type*} [DecidableEq Resource]

/-- Total physical work represented by a set of materialized resources. -/
def cacheWeight (weight : Resource → ℝ) (cached : Finset Resource) : ℝ :=
  ∑ resource ∈ cached, weight resource

/-- Work needed to materialize the demanded resources absent from the cache. -/
def coldWork (weight : Resource → ℝ) (cached demand : Finset Resource) : ℝ :=
  ∑ resource ∈ demand \ cached, weight resource

/-- Materializing a union adds exactly the work of its previously absent resources. -/
theorem cache_union_accounting (weight : Resource → ℝ) (cached demand : Finset Resource) :
    cacheWeight weight (cached ∪ demand) =
      cacheWeight weight cached + coldWork weight cached demand := by
  unfold cacheWeight coldWork
  have hdisj : Disjoint cached (demand \ cached) := by
    exact disjoint_left.mpr fun _ hcached hcold => (mem_sdiff.mp hcold).2 hcached
  have hunion : cached ∪ demand = cached ∪ (demand \ cached) := by
    ext resource
    simp only [mem_union, mem_sdiff]
    tauto
  rw [hunion, sum_union hdisj]

/-- Replaying a demand already represented by materialized resources incurs no cold work.
This says nothing about fresh per-evaluation search or scoring overhead. -/
theorem cached_demand_is_free (weight : Resource → ℝ) (cached demand : Finset Resource)
    (halready : demand ⊆ cached) : coldWork weight cached demand = 0 := by
  simp [coldWork, sdiff_eq_empty_iff_subset.mpr halready]

omit [DecidableEq Resource] in
/-- Nonnegative resource weights make cache weight monotone under inclusion. -/
theorem cacheWeight_mono (weight : Resource → ℝ) (hnonneg : ∀ resource, 0 ≤ weight resource)
    {cached larger : Finset Resource} (hsub : cached ⊆ larger) :
    cacheWeight weight cached ≤ cacheWeight weight larger := by
  exact sum_le_sum_of_subset_of_nonneg hsub (fun resource _ _ => hnonneg resource)

/-- The incremental work is nonnegative when physical resource costs are nonnegative. -/
theorem coldWork_nonnegative (weight : Resource → ℝ)
    (hnonneg : ∀ resource, 0 ≤ weight resource) (cached demand : Finset Resource) :
    0 ≤ coldWork weight cached demand := by
  exact sum_nonneg fun resource _ => hnonneg resource

/-- A cache cannot increase the physical work for a fixed demand. -/
theorem coldWork_le_fullWork (weight : Resource → ℝ)
    (hnonneg : ∀ resource, 0 ≤ weight resource) (cached demand : Finset Resource) :
    coldWork weight cached demand ≤ cacheWeight weight demand := by
  exact sum_le_sum_of_subset_of_nonneg sdiff_subset (fun resource _ _ => hnonneg resource)

/-- Pathwise conservation of successful materialization work. The transition assumes
persistence, no eviction, and that every newly demanded resource is materialized.
It allows arbitrary adaptive demands and needs no stochastic independence. -/
theorem cumulative_coldWork_eq (weight : Resource → ℝ)
    (cached demand : ℕ → Finset Resource)
    (hstep : ∀ t, cached (t + 1) = cached t ∪ demand t) (horizon : ℕ) :
    (∑ t ∈ range horizon, coldWork weight (cached t) (demand t)) =
      cacheWeight weight (cached horizon) - cacheWeight weight (cached 0) := by
  induction horizon with
  | zero => simp
  | succ horizon ih =>
    rw [sum_range_succ, ih, hstep, cache_union_accounting]
    ring

/-- A finite materializable resource universe bounds all cold work, independent of
how many evaluations replay already materialized qid-prefix resources. -/
theorem cumulative_coldWork_le_universe (weight : Resource → ℝ)
    (hnonneg : ∀ resource, 0 ≤ weight resource)
    (cached demand : ℕ → Finset Resource)
    (hstep : ∀ t, cached (t + 1) = cached t ∪ demand t)
    (horizon : ℕ) (resourceSet : Finset Resource) (hfinite : cached horizon ⊆ resourceSet) :
    (∑ t ∈ range horizon, coldWork weight (cached t) (demand t)) ≤
      cacheWeight weight resourceSet - cacheWeight weight (cached 0) := by
  rw [cumulative_coldWork_eq weight cached demand hstep horizon]
  exact sub_le_sub_right (cacheWeight_mono weight hnonneg hfinite) _

/-- Unshared per-evaluation overhead is charged at every evaluation. Cache conservation
applies only to the materialized-resource portion of total search cost. -/
theorem total_search_cost_accounting (weight : Resource → ℝ)
    (cached demand : ℕ → Finset Resource) (overhead : ℕ → ℝ)
    (hstep : ∀ t, cached (t + 1) = cached t ∪ demand t) (horizon : ℕ) :
    (∑ t ∈ range horizon, (coldWork weight (cached t) (demand t) + overhead t)) =
      cacheWeight weight (cached horizon) - cacheWeight weight (cached 0) +
        ∑ t ∈ range horizon, overhead t := by
  rw [sum_add_distrib, cumulative_coldWork_eq weight cached demand hstep horizon]

omit [DecidableEq Resource] in
/-- Per-resource forecast errors propagate through nonnegative execution probabilities.
Use the cold qid-prefix resources as `resources`; `inclusion` gives the marginal
probability that the completion evaluates each resource.  These probabilities need
not sum to one, and dependencies among resource demands require no extra assumption. -/
theorem weighted_resource_forecast_error (resources : Finset Resource)
    (inclusion predicted actual radius : Resource → ℝ)
    (hprob : ∀ resource ∈ resources, 0 ≤ inclusion resource)
    (herror : ∀ resource ∈ resources, |predicted resource - actual resource| ≤ radius resource) :
    |(∑ resource ∈ resources, inclusion resource * predicted resource) -
        ∑ resource ∈ resources, inclusion resource * actual resource| ≤
      ∑ resource ∈ resources, inclusion resource * radius resource := by
  rw [← sum_sub_distrib]
  calc
    |∑ resource ∈ resources,
        (inclusion resource * predicted resource - inclusion resource * actual resource)| ≤
        ∑ resource ∈ resources,
          |inclusion resource * predicted resource - inclusion resource * actual resource| :=
      abs_sum_le_sum_abs _ _
    _ = ∑ resource ∈ resources,
        inclusion resource * |predicted resource - actual resource| := by
      apply sum_congr rfl
      intro resource hresource
      rw [← mul_sub, abs_mul, abs_of_nonneg (hprob resource hresource)]
    _ ≤ ∑ resource ∈ resources, inclusion resource * radius resource := by
      exact sum_le_sum fun resource hresource =>
        mul_le_mul_of_nonneg_left (herror resource hresource) (hprob resource hresource)

omit [DecidableEq Resource] in
/-- The uncertainty radius of future evaluation overhead adds to the resource radius.
This is a deterministic coverage statement; calibration of all input error bounds
is a separate statistical obligation. -/
theorem total_search_cost_forecast_error (resources : Finset Resource)
    (inclusion predicted actual radius : Resource → ℝ)
    (predictedOverhead actualOverhead overheadRadius : ℝ)
    (hprob : ∀ resource ∈ resources, 0 ≤ inclusion resource)
    (herror : ∀ resource ∈ resources, |predicted resource - actual resource| ≤ radius resource)
    (hoverhead : |predictedOverhead - actualOverhead| ≤ overheadRadius) :
    |((∑ resource ∈ resources, inclusion resource * predicted resource) + predictedOverhead) -
        ((∑ resource ∈ resources, inclusion resource * actual resource) + actualOverhead)| ≤
      (∑ resource ∈ resources, inclusion resource * radius resource) + overheadRadius := by
  have hsplit :
      ((∑ resource ∈ resources, inclusion resource * predicted resource) + predictedOverhead) -
          ((∑ resource ∈ resources, inclusion resource * actual resource) + actualOverhead) =
        ((∑ resource ∈ resources, inclusion resource * predicted resource) -
          ∑ resource ∈ resources, inclusion resource * actual resource) +
            (predictedOverhead - actualOverhead) := by ring
  rw [hsplit]
  exact (abs_add_le _ _).trans
    (add_le_add
      (weighted_resource_forecast_error resources inclusion predicted actual radius hprob herror)
      hoverhead)

end AgentUCTPaper
