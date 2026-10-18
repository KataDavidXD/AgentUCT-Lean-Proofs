import CoreLogBounds
import NativeLocalAllocation




set_option autoImplicit false
noncomputable section
namespace AgentUCTRealIndex
open AgentUCTPanelAllocation AgentUCTNativeRepair AgentUCTNativeRefinement AgentUCTPaper

theorem index_weak_order_from_intervals (qa qb ca cb bonusLower bonusUpper : ℝ)
    (bonusA bonusB : ℝ) (ha : bonusLower ≤ bonusA) (hb : bonusB ≤ bonusUpper)
    (hmargin : qb+bonusUpper-cb ≤ qa+bonusLower-ca) :
    qb+bonusB-cb ≤ qa+bonusA-ca := by linarith

theorem index_tie_from_equal_components (qa qb ca cb bonusA bonusB : ℝ)
    (hq : qa = qb) (hc : ca = cb) (hb : bonusA = bonusB) :
    qa+bonusA-ca = qb+bonusB-cb := by rw [hq,hc,hb]

theorem firstMaximum_dominated_head (score : Act → ℝ) (head : Act) (rest : List Act)
    (hrest : ∀ a ∈ rest, score a ≤ score head) : firstMaximum score (head::rest) = head := by
  by_cases hn : rest = []
  · subst rest; rfl
  · have hm := firstMaximum_member score rest hn
    have hle := hrest _ hm
    simp only [firstMaximum,if_neg hn,not_lt_of_ge hle,if_false]

theorem firstMaximum_from_ordered_certificate (score : Act → ℝ)
    (earlier later : List Act) (chosen : Act)
    (hearlier : ∀ a ∈ earlier, score a < score chosen)
    (hlater : ∀ a ∈ later, score a ≤ score chosen) :
    firstMaximum score (earlier++chosen::later) = chosen := by
  induction earlier with
  | nil => exact firstMaximum_dominated_head score chosen later hlater
  | cons a earlier ih =>
      have ht := ih (fun b hb => hearlier b (List.mem_cons_of_mem _ hb))
      have hn : earlier++chosen::later ≠ [] := by simp
      simp only [List.cons_append,firstMaximum,if_neg hn,ht,hearlier a (by simp),if_true]

theorem exact_ties_keep_first (score : Act → ℝ) (head : Act) (rest : List Act)
    (heq : ∀ a ∈ rest, score a = score head) : firstMaximum score (head::rest) = head :=
  firstMaximum_dominated_head score head rest (fun a ha => (heq a ha).le)

theorem ordered_tie_pair_keeps_first (score : Act → ℝ) (a b : Act) (rest : List Act)
    (heq : score b = score a) (hle : ∀ r ∈ rest, score r ≤ score a) :
    firstMaximum score (a::b::rest) = a := by
  apply firstMaximum_dominated_head
  intro r hr
  rcases List.mem_cons.mp hr with rfl | hr
  · exact heq.le
  · exact hle r hr

theorem visited_choice_from_ordered_certificate (score : Act → ℝ)
    (history : List (TreeEvaluation Act)) (path : List Act) (earlier later : List Act) (chosen : Act)
    (hchoices : orderedLegalAvailable path = earlier++chosen::later)
    (hvisited : ∀ a ∈ orderedLegalAvailable path, 0 < rawVisits history (path++[a]))
    (hearlier : ∀ a ∈ earlier, score a < score chosen)
    (hlater : ∀ a ∈ later, score a ≤ score chosen) :
    nativeFirstChoice score history path = chosen := by
  rw [native_first_choice_all_visited score history path hvisited,hchoices]
  exact firstMaximum_from_ordered_certificate score earlier later chosen hearlier hlater

end AgentUCTRealIndex
