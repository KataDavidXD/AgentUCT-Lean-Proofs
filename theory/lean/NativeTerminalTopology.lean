import PanelOrderedMaximum


set_option autoImplicit false
set_option maxRecDepth 8192
set_option maxHeartbeats 4000000
noncomputable section
namespace AgentUCTPanelAllocation
open AgentUCTNativeRefinement AgentUCTNativeRepair AgentUCTPaper

abbrev TailCode := Fin 4 × Fin 4 × Fin 2 × Fin 3 × Fin 3

def codedLeaf (q : Fin 8) (r : Act) (code : TailCode) : List Act :=
  fullLeaf q r code.1 code.2.1 code.2.2.1 code.2.2.2.1 code.2.2.2.2

def nativeTerminals : Finset (List Act) :=
  (Finset.univ : Finset (Fin 8)).biUnion fun q =>
    (retrievers q).toFinset.biUnion fun r =>
      (Finset.univ : Finset TailCode).image (codedLeaf q r)

theorem native_terminals_mem (p : List Act) :
    p ∈ nativeTerminals ↔ ∃ q r, r ∈ retrievers q ∧ ∃ code : TailCode, codedLeaf q r code = p := by
  simp [nativeTerminals]

theorem native_terminals_iff_terminal (p : List Act) :
    p ∈ nativeTerminals ↔ Terminal p := by
  constructor
  · intro hp
    obtain ⟨q,r,hr,code,rfl⟩ := (native_terminals_mem p).mp hp
    exact fullLeaf_terminal q r hr _ _ _ _ _
  · intro hp
    have hs := legal_shape hp.1
    have hlen := hp.2
    cases hs <;> simp only [List.length_cons,List.length_nil] at hlen
    case answer q r hr s w k m t =>
      exact (native_terminals_mem _).mpr ⟨q,r,hr,⟨s,w,k,m,t⟩,rfl⟩
    all_goals omega

theorem legal_of_prefix {p leaf : List Act} (hp : p <+: leaf) (hl : Legal leaf) : Legal p := by
  obtain ⟨rest,rfl⟩ := hp
  have h : (followLegal [] p && followLegal p rest) = true := by
    simpa only [Legal,followLegal_append,List.nil_append] using hl
  unfold Legal
  cases hx : followLegal [] p <;> simp_all

theorem native_workflow_nodes_iff_legal (p : List Act) :
    p ∈ workflowNodes nativeTerminals ↔ Legal p := by
  rw [workflowNodes_mem]
  constructor
  · rintro ⟨leaf,hl,hp⟩
    exact legal_of_prefix hp ((native_terminals_iff_terminal leaf).mp hl).1
  · intro hp
    obtain ⟨hl,hpre⟩ := finish_legal_extension hp
    exact ⟨finish p,(native_terminals_iff_terminal _).mpr hl,hpre⟩

theorem native_available_children_iff {p : List Act} (hp : Legal p) (a : Act) :
    a ∈ availableChildren nativeTerminals p ↔ a ∈ available p := by
  rw [availableChildren_mem]
  constructor
  · rintro ⟨leaf,hl,hpre⟩
    exact (legal_append_action p a).mp
      (legal_of_prefix hpre ((native_terminals_iff_terminal leaf).mp hl).1) |>.2
  · intro ha
    obtain ⟨hl,hpre⟩ := finish_legal_extension ((legal_append_action p a).mpr ⟨hp,ha⟩)
    exact ⟨finish (p++[a]),(native_terminals_iff_terminal _).mpr hl,hpre⟩

theorem native_available_children_eq {p : List Act} (hp : Legal p) :
    availableChildren nativeTerminals p = (orderedLegalAvailable p).toFinset := by
  ext a
  simp only [List.mem_toFinset,native_available_children_iff hp,ordered_legal_member_iff hp]

theorem native_terminal_antichain (p q : List Act) (hp : p ∈ nativeTerminals)
    (hq : q ∈ nativeTerminals) (hpre : p <+: q) : p = q := by
  have hlp := ((native_terminals_iff_terminal p).mp hp).2
  have hlq := ((native_terminals_iff_terminal q).mp hq).2
  exact hpre.eq_of_length_le (by omega)

theorem native_terminals_nonempty : nativeTerminals.Nonempty :=
  ⟨seedPath 0,(native_terminals_iff_terminal _).mpr (seedPath_terminal 0)⟩

theorem native_terminal_no_children (p : List Act) (hp : p ∈ nativeTerminals) :
    availableChildren nativeTerminals p = ∅ :=
  terminal_has_no_child nativeTerminals (fun p hp q hq hpre =>
    native_terminal_antichain p q hp hq hpre) p hp

end AgentUCTPanelAllocation
