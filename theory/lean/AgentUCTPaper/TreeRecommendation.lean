import AgentUCTPaper.TreeObjectives

/-! # Training shortlist, validation transfer, and the distinct endpoint objective -/

set_option autoImplicit false

noncomputable section

namespace AgentUCTPaper

variable {Action : Type*} [DecidableEq Action]

omit [DecidableEq Action] in
theorem ranked_head_dominates (reward : List Action → ℝ) (head : List Action)
    (tail : List (List Action))
    (hRank : (head :: tail).Pairwise (fun p q ↦ reward q ≤ reward p)) :
    ∀ p ∈ head :: tail, reward p ≤ reward head := by
  intro p hp
  rcases List.mem_cons.mp hp with rfl | hp
  · exact le_rfl
  · exact (List.pairwise_cons.mp hRank).1 p hp

omit [DecidableEq Action] in
theorem ranked_head_in_shortlist (head : List Action) (tail : List (List Action))
    (k : ℕ) (hk : 0 < k) : head ∈ (head :: tail).take k := by
  cases k with
  | zero => omega
  | succ k => simp

theorem ranked_training_head_gap (terminals : Finset (List Action)) (reward : List Action → ℝ)
    (events : List (TreeEvaluation Action)) (hTable : FixedTableEvents terminals reward events)
    (head : List Action) (tail : List (List Action))
    (hRank : (head :: tail).Pairwise (fun p q ↦ reward q ≤ reward p))
    (hComplete : ∀ event ∈ events, event.terminal ∈ head :: tail)
    (hNonempty : events ≠ []) :
    subtreeValue terminals reward [] - reward head ≤
      backedDeficit (subtreeValue terminals reward []) events [] / events.length := by
  have hSum := sum_returns_le_best (reward head) events (by
    intro event he
    rw [(hTable event he).2]
    exact ranked_head_dominates reward head tail hRank _ (hComplete event he))
  have hLen : 0 < events.length := List.length_pos_iff.mpr hNonempty
  rw [le_div_iff₀ (Nat.cast_pos.mpr hLen), backedDeficit_identity, root_count_eq_length]
  have hReturn : backedReturn events [] = (events.map TreeEvaluation.reward).sum := by
    simp [backedReturn]
  rw [hReturn]
  nlinarith

theorem validation_shortlist_gap (terminals : Finset (List Action))
    (train valid : List Action → ℝ) (epsilon : ℝ)
    (events : List (TreeEvaluation Action)) (hTable : FixedTableEvents terminals train events)
    (head : List Action) (tail : List (List Action)) (chosen : List Action) (k : ℕ) (hk : 0 < k)
    (hRank : (head :: tail).Pairwise (fun p q ↦ train q ≤ train p))
    (hComplete : ∀ event ∈ events, event.terminal ∈ head :: tail)
    (hSound : ∀ p ∈ head :: tail, p ∈ terminals) (hNonempty : events ≠ [])
    (hSelected : ∀ p ∈ (head :: tail).take k, valid p ≤ valid chosen)
    (hDifference : ∀ p ∈ terminals, |valid p - train p| ≤ epsilon) :
    subtreeValue terminals valid [] - valid chosen ≤
      backedDeficit (subtreeValue terminals train []) events [] / events.length + 2 * epsilon := by
  have hHead := hSound head (by simp)
  have hHas : (subtreeTerminals terminals []).Nonempty :=
    ⟨head, Finset.mem_filter.mpr ⟨hHead, List.nil_prefix⟩⟩
  obtain ⟨opt, hOpt, _, hValue⟩ := subtreeValue_attained terminals valid [] hHas
  have hOptDiff := (abs_le.mp (hDifference opt hOpt)).2
  have hTrainOpt := subtreeValue_upper terminals train [] opt hOpt List.nil_prefix
  have hHeadDiff := (abs_le.mp (hDifference head hHead)).1
  have hChoose := hSelected head (ranked_head_in_shortlist head tail k hk)
  have hGap := ranked_training_head_gap terminals train events hTable head tail hRank
    hComplete hNonempty
  rw [hValue]
  linarith

/-- All workflows may be observed and yet training top-1 can exclude the validation optimum. -/
theorem validation_top_one_counterexample :
    let ranked := [true, false]
    let train := fun b : Bool ↦ if b then (1 : ℝ) else 0
    let valid := fun b : Bool ↦ if b then (0 : ℝ) else 1
    ranked.Pairwise (fun a b ↦ train b ≤ train a) ∧
      true ∈ ranked.take 1 ∧ false ∉ ranked.take 1 ∧ valid false - valid true = 1 := by
  norm_num

def endpointJ (quality cost lambda reference : ℝ) : ℝ := quality - lambda * cost / reference

theorem endpointJ_gap_identity (actualQuality comparatorQuality actualCost comparatorCost
    lambda reference : ℝ) :
    endpointJ comparatorQuality comparatorCost lambda reference -
      endpointJ actualQuality actualCost lambda reference =
    (comparatorQuality - actualQuality) + lambda * (actualCost - comparatorCost) / reference := by
  unfold endpointJ
  ring

/-- Quality optimality alone does not remove the already-paid optimization-cost gap. -/
theorem equal_quality_positive_endpoint_gap (quality actualCost comparatorCost lambda reference : ℝ)
    (hCost : comparatorCost < actualCost) (hLambda : 0 < lambda) (hReference : 0 < reference) :
    0 < endpointJ quality comparatorCost lambda reference -
      endpointJ quality actualCost lambda reference := by
  rw [endpointJ_gap_identity, sub_self, zero_add]
  exact div_pos (mul_pos hLambda (sub_pos.mpr hCost)) hReference

end AgentUCTPaper
