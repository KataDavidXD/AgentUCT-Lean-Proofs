import NativeConstraints



set_option autoImplicit false
set_option maxRecDepth 8192
set_option maxHeartbeats 3000000
namespace AgentUCTNativeRepair
open AgentUCTNativeRefinement AgentUCTPaper

inductive Shape : List Act → Prop where
  | nil : Shape []
  | query (q : Fin 8) : Shape [.query q]
  | retrieve (q : Fin 8) (r : Act) (hr : r ∈ retrievers q) : Shape [.query q,r]
  | select (q : Fin 8) (r : Act) (hr : r ∈ retrievers q) (s : Fin 4) :
      Shape [.query q,r,.selection s]
  | width (q : Fin 8) (r : Act) (hr : r ∈ retrievers q) (s w : Fin 4) :
      Shape [.query q,r,.selection s,.width w]
  | stop (q : Fin 8) (r : Act) (hr : r ∈ retrievers q) (s w : Fin 4) :
      Shape [.query q,r,.selection s,.width w,.stop]
  | rerank (q : Fin 8) (r : Act) (hr : r ∈ retrievers q) (s w : Fin 4) (k : Fin 2) :
      Shape [.query q,r,.selection s,.width w,.stop,.reranker k]
  | topm (q : Fin 8) (r : Act) (hr : r ∈ retrievers q) (s w : Fin 4) (k : Fin 2) (m : Fin 3) :
      Shape [.query q,r,.selection s,.width w,.stop,.reranker k,.topm m]
  | context (q : Fin 8) (r : Act) (hr : r ∈ retrievers q) (s w : Fin 4) (k : Fin 2) (m t : Fin 3) :
      Shape [.query q,r,.selection s,.width w,.stop,.reranker k,.topm m,.context t]
  | answer (q : Fin 8) (r : Act) (hr : r ∈ retrievers q) (s w : Fin 4) (k : Fin 2) (m t : Fin 3) :
      Shape [.query q,r,.selection s,.width w,.stop,.reranker k,.topm m,.context t,.answer m]

theorem followLegal_append (p xs ys : List Act) :
    followLegal p (xs++ys) = (followLegal p xs && followLegal (p++xs) ys) := by
  induction xs generalizing p with
  | nil => simp [followLegal]
  | cons a xs ih => simp [followLegal,ih,List.append_assoc,Bool.and_assoc]

theorem legal_append_action (p : List Act) (a : Act) :
    Legal (p++[a]) ↔ Legal p ∧ a ∈ available p := by
  simp [Legal,followLegal_append,followLegal]

theorem legal_nil : Legal [] := rfl

theorem shape_step {p : List Act} (hp : Shape p) {a : Act} (ha : a ∈ available p) :
    Shape (p++[a]) := by
  cases hp with
  | nil =>
      obtain ⟨q,_,rfl⟩ := List.mem_map.mp ha
      exact Shape.query q
  | query q => exact Shape.retrieve q a ha
  | retrieve q r hr =>
      obtain ⟨s,_,rfl⟩ := List.mem_map.mp ha
      exact Shape.select q r hr s
  | select q r hr s =>
      obtain ⟨w,_,rfl⟩ := List.mem_map.mp ha
      exact Shape.width q r hr s w
  | width q r hr s w =>
      have he : a = .stop := by simpa [available] using ha
      subst a
      exact Shape.stop q r hr s w
  | stop q r hr s w =>
      obtain ⟨k,_,rfl⟩ := List.mem_map.mp ha
      exact Shape.rerank q r hr s w k
  | rerank q r hr s w k =>
      obtain ⟨m,_,rfl⟩ := List.mem_map.mp ha
      exact Shape.topm q r hr s w k m
  | topm q r hr s w k m =>
      obtain ⟨t,_,rfl⟩ := List.mem_map.mp ha
      exact Shape.context q r hr s w k m t
  | context q r hr s w k m t =>
      have he : a = .answer m := by simpa [available] using ha
      subst a
      exact Shape.answer q r hr s w k m t
  | answer q r hr s w k m t => simp [available] at ha

theorem legal_shape {p : List Act} (hp : Legal p) : Shape p := by
  induction p using List.reverseRecOn with
  | nil => exact Shape.nil
  | append_singleton p a ih =>
      obtain ⟨hl,ha⟩ := (legal_append_action p a).mp hp
      exact shape_step (ih hl) ha

theorem legal_length_le_nine {p : List Act} (hp : Legal p) : p.length ≤ 9 := by
  cases legal_shape hp <;> simp

theorem legal_no_actions_iff_terminal {p : List Act} (hp : Legal p) :
    available p = [] ↔ Terminal p := by
  cases legal_shape hp <;>
    simp [available,rootOrder,retrievers,Terminal,hp]
  split_ifs <;> simp

def fullLeaf (q : Fin 8) (r : Act) (s w : Fin 4) (k : Fin 2) (m t : Fin 3) : List Act :=
  [.query q,r,.selection s,.width w,.stop,.reranker k,.topm m,.context t,.answer m]

theorem fullLeaf_terminal (q : Fin 8) (r : Act) (hr : r ∈ retrievers q)
    (s w : Fin 4) (k : Fin 2) (m t : Fin 3) : Terminal (fullLeaf q r s w k m t) := by
  simp [Terminal,Legal,followLegal,available,rootOrder,fullLeaf,hr]



def finish : List Act → List Act
  | [] => seedPath 0
  | [.query q] => seedPath q
  | [.query q,r] => fullLeaf q r 0 0 0 0 0
  | [.query q,r,.selection s] => fullLeaf q r s 0 0 0 0
  | [.query q,r,.selection s,.width w] => fullLeaf q r s w 0 0 0
  | [.query q,r,.selection s,.width w,.stop] => fullLeaf q r s w 0 0 0
  | [.query q,r,.selection s,.width w,.stop,.reranker k] => fullLeaf q r s w k 0 0
  | [.query q,r,.selection s,.width w,.stop,.reranker k,.topm m] => fullLeaf q r s w k m 0
  | [.query q,r,.selection s,.width w,.stop,.reranker k,.topm m,.context t] => fullLeaf q r s w k m t
  | [.query q,r,.selection s,.width w,.stop,.reranker k,.topm m,.context t,.answer _] =>
      fullLeaf q r s w k m t
  | _ => seedPath 0

theorem finish_legal_extension {p : List Act} (hp : Legal p) :
    Terminal (finish p) ∧ p <+: finish p := by
  cases legal_shape hp with
  | nil => exact ⟨seedPath_terminal 0,List.nil_prefix⟩
  | query q =>
      refine ⟨seedPath_terminal q, ?_⟩
      exact ⟨(seedPath q).drop 1, by simp [finish,seedPath,leaf]⟩
  | retrieve q r hr =>
      exact ⟨fullLeaf_terminal q r hr 0 0 0 0 0,⟨_,rfl⟩⟩
  | select q r hr s =>
      exact ⟨fullLeaf_terminal q r hr s 0 0 0 0,⟨_,rfl⟩⟩
  | width q r hr s w =>
      exact ⟨fullLeaf_terminal q r hr s w 0 0 0,⟨_,rfl⟩⟩
  | stop q r hr s w =>
      exact ⟨fullLeaf_terminal q r hr s w 0 0 0,⟨_,rfl⟩⟩
  | rerank q r hr s w k =>
      exact ⟨fullLeaf_terminal q r hr s w k 0 0,⟨_,rfl⟩⟩
  | topm q r hr s w k m =>
      exact ⟨fullLeaf_terminal q r hr s w k m 0,⟨_,rfl⟩⟩
  | context q r hr s w k m t =>
      exact ⟨fullLeaf_terminal q r hr s w k m t,⟨_,rfl⟩⟩
  | answer q r hr s w k m t =>
      exact ⟨fullLeaf_terminal q r hr s w k m t,List.prefix_refl _⟩



def legalAvailable (p : List Act) : List Act := if Legal p then available p else []

def orderedLegalAvailable (p : List Act) : List Act :=
  (legalAvailable p).insertionSort (fun a b => nativeOrderKey a ≤ nativeOrderKey b)

theorem legal_available_eq {p : List Act} (hp : Legal p) : legalAvailable p = available p := by
  simp [legalAvailable,hp]

theorem illegal_available_empty {p : List Act} (hp : ¬ Legal p) : legalAvailable p = [] := by
  simp [legalAvailable,hp]

theorem ordered_legal_member_iff {p : List Act} (hp : Legal p) (a : Act) :
    a ∈ orderedLegalAvailable p ↔ a ∈ available p := by
  simp [orderedLegalAvailable,legalAvailable,hp,List.mem_insertionSort]

theorem independent_bad_prefix_guarded : legalAvailable [.query 0,.stop] = [] := by decide

end AgentUCTNativeRepair
