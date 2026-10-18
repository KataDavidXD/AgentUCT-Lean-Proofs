import NativeForecast




set_option autoImplicit false
set_option maxRecDepth 8192
set_option maxHeartbeats 3000000
noncomputable section
namespace AgentUCTNativeRefinement
open AgentUCTPaper Finset

def snapshotTolerance : ℝ := 1/10000000
def targetReached (actual B : ℝ) : Prop := B ≤ actual
def affordable (actual B tolerance : ℝ) : Prop := actual ≤ B+tolerance
instance (actual B : ℝ) : Decidable (targetReached actual B) :=
  inferInstanceAs (Decidable (B ≤ actual))

theorem equality_crossing_is_affordable (B tolerance : ℝ) (ht : 0 ≤ tolerance) :
    targetReached B B ∧ affordable B B tolerance := by
  constructor
  · exact le_rfl
  · exact le_add_of_nonneg_right ht

theorem tolerance_crossing_is_affordable (actual B tolerance : ℝ)
    (hcross : B ≤ actual) (hfit : actual ≤ B+tolerance) :
    targetReached actual B ∧ affordable actual B tolerance := ⟨hcross,hfit⟩

theorem crossing_reward_exclusion_requires_tolerance_gap (actual B tolerance : ℝ)
    (hgap : B+tolerance < actual) : ¬ affordable actual B tolerance := not_le.mpr hgap

def T_B (spent : ℕ → ℝ) (complete : ℕ) (B tolerance : ℝ) : ℕ := by
  classical
  exact ((Finset.range (complete+1)).filter fun n => affordable (spent n) B tolerance).sup id

theorem T_B_last_complete (spent : ℕ → ℝ) (complete last : ℕ) (B tolerance : ℝ)
    (hlast : last ≤ complete) (hfit : affordable (spent last) B tolerance)
    (hexclude : ∀ n, last < n → n ≤ complete → ¬ affordable (spent n) B tolerance) :
    T_B spent complete B tolerance = last := by
  classical
  unfold T_B
  apply le_antisymm
  · apply Finset.sup_le
    intro n hn
    change n ≤ last
    obtain ⟨hn,hfitn⟩ := Finset.mem_filter.mp hn
    have hc : n ≤ complete := by have hh := Finset.mem_range.mp hn; omega
    by_contra h
    exact hexclude n (by omega) hc hfitn
  · have hm : last ∈ (Finset.range (complete+1)).filter
        (fun n => affordable (spent n) B tolerance) := by
      exact Finset.mem_filter.mpr ⟨Finset.mem_range.mpr (by omega),hfit⟩
    exact Finset.le_sup (f := id) hm




def nativeFirstAdvance (reward : List Act → ℝ) (_B : ℝ) : List (TreeEvaluation Act) :=
  initialization reward

theorem native_first_advance_is_eight (reward : List Act → ℝ) (B : ℝ) :
    (nativeFirstAdvance reward B).length = 8 := by simp [nativeFirstAdvance,initialization]

theorem eight_initialization_count_cap_interface (cap : ℕ) (hcap : 8 ≤ cap) :
    ∀ reward B, (nativeFirstAdvance reward B).length ≤ cap := by
  intro reward B
  rw [native_first_advance_is_eight]
  exact hcap

theorem native_initial_target_can_cross_earlier (reward : List Act → ℝ)
    (q a e b k B : ℝ) (hfirst : B ≤ (ownState (price q a e b k)
      ((initialization reward).take 1)).totalPaid) :
    targetReached (ownState (price q a e b k) ((initialization reward).take 1)).totalPaid B ∧
    (nativeFirstAdvance reward B).length = 8 := ⟨hfirst,native_first_advance_is_eight reward B⟩

variable {Resource : Type*} [DecidableEq Resource]

structure BillCache (Resource : Type*) where
  materialized : Finset Resource
  totalPaid : ℝ

def publishDemand (weight : Resource → ℝ) (s : BillCache Resource)
    (demand : Finset Resource) : BillCache Resource :=
  ⟨s.materialized ∪ demand,s.totalPaid+coldWork weight s.materialized demand⟩

def publishBatches (weight : Resource → ℝ) (demands : List (Finset Resource))
    (s : BillCache Resource) : BillCache Resource := demands.foldl (publishDemand weight) s

theorem shared_context_receipt_conservation (weight : Resource → ℝ)
    (demands : List (Finset Resource)) (s : BillCache Resource) :
    (publishBatches weight demands s).totalPaid-s.totalPaid =
      cacheWeight weight (publishBatches weight demands s).materialized-
        cacheWeight weight s.materialized := by
  induction demands generalizing s with
  | nil => simp [publishBatches]
  | cons demand demands ih =>
    have h := ih (publishDemand weight s demand)
    change (publishBatches weight demands (publishDemand weight s demand)).totalPaid-s.totalPaid =
      cacheWeight weight (publishBatches weight demands (publishDemand weight s demand)).materialized-
        cacheWeight weight s.materialized
    have hu := cache_union_accounting weight s.materialized demand
    simp only [publishDemand] at h
    simp only [publishDemand]
    linarith

theorem already_shared_context_adds_zero (weight : Resource → ℝ)
    (s : BillCache Resource) (demand : Finset Resource) (hcache : demand ⊆ s.materialized) :
    (publishDemand weight s demand).totalPaid = s.totalPaid ∧
    (publishDemand weight s demand).materialized = s.materialized := by
  simp [publishDemand,cached_demand_is_free weight _ _ hcache,Finset.union_eq_left.mpr hcache]

variable {Qid : Type*} [DecidableEq Qid]

def initialPathResources : Finset (List Act) :=
  Finset.univ.biUnion fun q : Fin 8 => executionPrefixes (seedPath q)

def contextInitialDemand (qids : Finset Qid) : Finset (Qid × List Act) :=
  qids ×ˢ initialPathResources



theorem context_initialization_union (contexts : Finset (Finset Qid)) :
    (contexts.biUnion contextInitialDemand) =
      contextInitialDemand (contexts.biUnion id) := by
  ext resource
  simp only [Finset.mem_biUnion,contextInitialDemand,Finset.mem_product]
  constructor
  · rintro ⟨qids,hqids,hq,hpath⟩
    exact ⟨⟨qids,hqids,hq⟩,hpath⟩
  · rintro ⟨⟨qids,hqids,hq⟩,hpath⟩
    exact ⟨qids,hqids,hq,hpath⟩

theorem multi_context_initial_bill_is_physical_sum (contexts : Finset (Finset Qid))
    (weight : Qid × List Act → ℝ) :
    cacheWeight weight (contexts.biUnion contextInitialDemand) =
      ∑ qid ∈ contexts.biUnion id, ∑ p ∈ initialPathResources, weight (qid,p) := by
  rw [context_initialization_union]
  exact Finset.sum_product _ _ _

theorem repeated_context_cannot_double_the_initial_bill (qids : Finset Qid)
    (weight : Qid × List Act → ℝ) :
    (publishBatches weight [contextInitialDemand qids,contextInitialDemand qids]
      ⟨∅,0⟩).totalPaid = cacheWeight weight (contextInitialDemand qids) := by
  simp [publishBatches,publishDemand,coldWork,cacheWeight]

end AgentUCTNativeRefinement
