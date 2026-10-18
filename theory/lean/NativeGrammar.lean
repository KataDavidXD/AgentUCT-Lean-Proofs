import BillingBoundary




set_option autoImplicit false
set_option maxRecDepth 4096
set_option maxHeartbeats 3000000
namespace AgentUCTNativeRefinement
open AgentUCTPaper Finset

inductive Act where
  | query : Fin 8 → Act
  | normalRetriever : Fin 30 → Act
  | hydeRetriever : Fin 3 → Act
  | selection : Fin 4 → Act
  | width : Fin 4 → Act
  | stop : Act
  | reranker : Fin 2 → Act
  | topm : Fin 3 → Act
  | context : Fin 3 → Act
  | answer : Fin 3 → Act
  deriving DecidableEq, Repr


def queryNames : List String :=
  ["query.decomposition", "query.hyde", "query.identity", "query.query2doc",
   "query.query2doc:q=1", "query.query2doc:q=3", "query.rewrite", "query.synonyms"]

def rootOrder : List Act := (List.finRange 8).map Act.query
theorem finRange8_explicit : List.finRange 8 = [0,1,2,3,4,5,6,7] := by decide
theorem finUniv8_explicit : (Finset.univ : Finset (Fin 8)) = {0,1,2,3,4,5,6,7} := by decide
def hyde : Fin 8 := 1
def identityQuery : Fin 8 := 2
def branchB : Fin 8 := 5





def retrievers (q : Fin 8) : List Act :=
  if q = hyde then (List.finRange 3).map Act.hydeRetriever
  else (List.finRange 30).map Act.normalRetriever

def available : List Act → List Act
  | [] => rootOrder
  | [.query q] => retrievers q
  | [.query _, _] => (List.finRange 4).map Act.selection
  | [.query _, _, .selection _] => (List.finRange 4).map Act.width
  | [.query _, _, .selection _, .width _] => [.stop]
  | [.query _, _, .selection _, .width _, .stop] => (List.finRange 2).map Act.reranker
  | [.query _, _, .selection _, .width _, .stop, .reranker _] =>
      (List.finRange 3).map Act.topm
  | [.query _, _, .selection _, .width _, .stop, .reranker _, .topm _] =>
      (List.finRange 3).map Act.context
  | [.query _, _, .selection _, .width _, .stop, .reranker _, .topm m, .context _] =>
      [.answer m]
  | _ => []

def followLegal : List Act → List Act → Bool
  | _, [] => true
  | p, a :: rest => decide (a ∈ available p) && followLegal (p ++ [a]) rest

def Legal (p : List Act) : Prop := followLegal [] p = true
def Terminal (p : List Act) : Prop := Legal p ∧ p.length = 9

instance (p : List Act) : Decidable (Legal p) := inferInstanceAs (Decidable (_ = _))
instance (p : List Act) : Decidable (Terminal p) := inferInstanceAs (Decidable (_ ∧ _))

def leaf (q : Fin 8) (r : Act) (w : Fin 4) (m : Fin 3) : List Act :=
  [.query q, r, .selection 0, .width w, .stop, .reranker 0, .topm m,
    .context 0, .answer m]

def seedRetriever (q : Fin 8) : Act :=
  if q = hyde then .hydeRetriever 0 else .normalRetriever 0

def seedPath (q : Fin 8) : List Act := leaf q (seedRetriever q) 0 0

theorem eight_real_root_actions : rootOrder.length = 8 ∧ rootOrder.Nodup ∧
    queryNames.length = 8 ∧ queryNames.Nodup := by decide

theorem root_actions_exact : available [] = rootOrder := rfl

theorem normal_and_hyde_branching (q : Fin 8) :
    (available [.query q]).length = if q = hyde then 3 else 30 := by
  simp [available, retrievers]
  split_ifs <;> simp

theorem seedPath_terminal (q : Fin 8) : Terminal (seedPath q) := by
  fin_cases q <;> decide

theorem seedPath_injective : Function.Injective seedPath := by
  intro q r h
  have hhead := congrArg List.head? h
  simpa [seedPath, leaf] using hhead


theorem eight_distinct_legal_seed_paths :
    ((List.finRange 8).map seedPath).length = 8 ∧
    ((List.finRange 8).map seedPath).Nodup ∧
    ∀ p ∈ (List.finRange 8).map seedPath, Terminal p := by
  refine ⟨by simp, ?_, ?_⟩
  · exact List.Nodup.map seedPath_injective (List.nodup_finRange 8)
  · intro p hp
    obtain ⟨q, _, rfl⟩ := List.mem_map.mp hp
    exact seedPath_terminal q




def terminalCount : ℕ := (7 * 30 + 3) * 4 * 4 * 2 * 3 * 3
theorem native_terminal_count_arithmetic : terminalCount = 61344 := by decide

theorem hidden_hyde_terminal (r : Fin 3) :
    Terminal (leaf hyde (.hydeRetriever r) 1 0) := by
  fin_cases r <;> decide

theorem hidden_normal_terminal (q : Fin 8) (hq : q ≠ hyde) :
    Terminal (leaf q (.normalRetriever 0) 1 2) := by
  fin_cases q <;> simp_all [hyde, Terminal, Legal, followLegal, available,
    rootOrder, retrievers, leaf]

end AgentUCTNativeRefinement
