import AgentUCTPaper.DynamicCompletion
import AgentUCTPaper.TreeNextUnpaid

set_option autoImplicit false
noncomputable section
namespace AgentUCTPaper
open Finset

/-- One calibration pseudo-observation and physical observations only. -/
def onlineMean {I : Type*} (prior : ℝ) (samples : Finset I) (value : I → ℝ) : ℝ :=
  (prior + ∑ i ∈ samples, value i) / (samples.card + 1 : ℝ)

theorem onlineMean_envelope {I : Type*} (prior cap : ℝ)
    (samples : Finset I) (value : I → ℝ)
    (hp : 0 ≤ prior) (hpc : prior ≤ cap)
    (hv : ∀ i ∈ samples, 0 ≤ value i ∧ value i ≤ cap) :
    0 ≤ onlineMean prior samples value ∧ onlineMean prior samples value ≤ cap := by
  -- Q9.1：分母card+1>0；prior和各物理预测样本均在[0,cap]。
  have hd : (0 : ℝ) < samples.card + 1 := by positivity
  have hs0 : 0 ≤ ∑ i ∈ samples, value i := sum_nonneg (fun i hi ↦ (hv i hi).1)
  have hsc : (∑ i ∈ samples, value i) ≤ samples.card * cap := by
    calc
      _ ≤ ∑ _i ∈ samples, cap := sum_le_sum (fun i hi ↦ (hv i hi).2)
      _ = _ := by simp
  constructor
  · exact div_nonneg (add_nonneg hp hs0) (le_of_lt hd)
  · apply (div_le_iff₀ hd).2
    nlinarith

/-- Samples retain multiplicity; their indices, not distinct outcomes, carry mass. -/
def sampledLaw {G : Type*} [DecidableEq G] (n : ℕ) (sample : Fin n → G) (g : G) : ℝ :=
  ∑ i : Fin n, if sample i = g then (1 : ℝ) / n else 0

theorem sampledLaw_nonneg {G : Type*} [DecidableEq G]
    (n : ℕ) (sample : Fin n → G) (g : G) : 0 ≤ sampledLaw n sample g := by
  apply sum_nonneg
  intro i _
  split_ifs <;> positivity

theorem sampledLaw_expectation {G : Type*} [DecidableEq G]
    (outcomes : Finset G) (n : ℕ) (sample : Fin n → G)
    (hSample : ∀ i, sample i ∈ outcomes) (bill : G → ℝ) :
    (∑ g ∈ outcomes, sampledLaw n sample g * bill g) =
      (∑ i : Fin n, bill (sample i)) / n := by
  -- Q9.2a：先展开按样本索引定义的law；交换完成与样本的有限和。
  simp only [sampledLaw, sum_mul]
  rw [sum_comm]
  calc
    _ = ∑ i : Fin n, bill (sample i) / n := by
      apply sum_congr rfl
      intro i _
      simp only [ite_mul, zero_mul]
      rw [sum_ite_eq outcomes (sample i)]
      -- Q9.2b：每个合法样本恰命中一个完成；重复完成的不同索引继续分别计数。
      simp [hSample i, div_eq_mul_inv, mul_comm]
    _ = _ := by rw [sum_div]

theorem sampledLaw_mass {G : Type*} [DecidableEq G]
    (outcomes : Finset G) (n : ℕ) (hn : 0 < n) (sample : Fin n → G)
    (hSample : ∀ i, sample i ∈ outcomes) :
    (∑ g ∈ outcomes, sampledLaw n sample g) = 1 := by
  -- Q9.2：样本按索引保留重复；用常量账1的期望式得到总质量1，要求n>0。
  have h := sampledLaw_expectation outcomes n sample hSample (fun _ ↦ 1)
  simpa [Nat.ne_of_gt hn] using h

/-- Concrete online prices discharge the live-price premise of the shared-cache
quality theorem. The empirical law above discharges its law/mass premises;
coverage and eventual zero penalties remain the theorem's essential mechanism. -/
theorem onlineMean_completion_envelope {I R G : Type*} [DecidableEq R]
    (outcomes : Finset G) (law : G → ℝ) (hLaw : ∀ g ∈ outcomes, 0 ≤ law g)
    (demands : G → Finset R) (base prior : R → ℝ) (cached : Finset R)
    (samples : R → Finset I) (value : R → I → ℝ)
    (hPrior : ∀ r, 0 ≤ prior r ∧ prior r ≤ base r)
    (hValue : ∀ r i, i ∈ samples r → 0 ≤ value r i ∧ value r i ≤ base r) :
    0 ≤ ∑ g ∈ outcomes, law g * coldWork
      (fun r ↦ onlineMean (prior r) (samples r) (value r)) cached (demands g) ∧
    (∑ g ∈ outcomes, law g * coldWork
      (fun r ↦ onlineMean (prior r) (samples r) (value r)) cached (demands g)) ≤
      ∑ g ∈ outcomes, law g * coldWork base cached (demands g) := by
  apply completion_prediction_envelope outcomes law hLaw demands base _ cached
  · intro r
    exact (onlineMean_envelope _ _ _ _ (hPrior r).1 (hPrior r).2 (hValue r)).1
  · intro r
    exact (onlineMean_envelope _ _ _ _ (hPrior r).1 (hPrior r).2 (hValue r)).2

theorem online_mean_shared_root_log_bound
    {I Qid Action : Type*} [DecidableEq Qid] [DecidableEq Action]
    (qids : Finset Qid) (root : List Action)
    (terminals : Finset (List Action)) (hTerminals : terminals.Nonempty)
    (reward : List Action → ℝ)
    (hReward : ∀ leaf ∈ terminals, 0 ≤ reward leaf ∧ reward leaf ≤ 1)
    (hAntichain : ∀ p ∈ terminals, ∀ q ∈ terminals, p <+: q → p = q)
    (base prior : Qid × List Action → ℝ)
    (hPrior : ∀ r, 0 ≤ prior r ∧ prior r ≤ base r)
    (samples : List (TreeEvaluation Action) → Qid × List Action → Finset I)
    (value : List (TreeEvaluation Action) → Qid × List Action → I → ℝ)
    (hValue : ∀ before r i, i ∈ samples before r →
      0 ≤ value before r i ∧ value before r i ≤ base r)
    (gamma c : ℝ) (hGamma : 0 ≤ gamma) (hc : 0 < c)
    (law : List (TreeEvaluation Action) → List Action → Action → List Action → ℝ)
    (hLaw : ∀ before p a, a ∈ availableChildren terminals p →
      ∀ leaf ∈ subtreeTerminals terminals (p ++ [a]), 0 ≤ law before p a leaf)
    (hMass : ∀ before p a, a ∈ availableChildren terminals p →
      ∑ leaf ∈ subtreeTerminals terminals (p ++ [a]), law before p a leaf = 1)
    (initial : PersistentCaches Qid Action)
    (hInitial : initial.restorable = initial.everMaterialized)
    (extra : List (TreeEvaluation Action) → Finset (Qid × List Action)) :
    ∃ delta : ℝ, 0 < delta ∧ ∀ events : List (TreeEvaluation Action),
      FixedTableEvents terminals reward events →
      LegalTreeRun (fun p ↦ p ∈ terminals) {[]} events →
      TreeAllocationRule terminals c (fun before p a ↦
        sharedColdPenalty qids root terminals
          (fun r ↦ onlineMean (prior r) (samples before r) (value before r))
          gamma law initial extra before p a) events →
      let H := gamma * cacheWeight base (workflowResources qids root terminals)
      let cacheTime := coverageVisits terminals c H (topologyDepth terminals)
      let constants := treeRateConstants terminals c H delta cacheTime (topologyDepth terminals)
      backedDeficit (subtreeValue terminals reward []) events [] ≤
        constants.1 * Real.log (events.length + 1 : ℕ) + constants.2 := by
  -- Q9.3：只需供给每个历史的价格非负和固定包络；其他主定理假设原样传递。
  apply checkpoint_conditioned_shared_root_log_bound qids root terminals hTerminals reward
    hReward hAntichain base (fun r ↦ le_trans (hPrior r).1 (hPrior r).2)
    (fun before r ↦ onlineMean (prior r) (samples before r) (value before r))
    _ _ gamma c hGamma hc law hLaw hMass initial hInitial extra
  · intro before r
    exact (onlineMean_envelope _ _ _ _ (hPrior r).1 (hPrior r).2 (hValue before r)).1
  · intro before r
    exact (onlineMean_envelope _ _ _ _ (hPrior r).1 (hPrior r).2 (hValue before r)).2

end AgentUCTPaper
