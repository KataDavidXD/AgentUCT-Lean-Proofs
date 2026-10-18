import NativeOwnCache



set_option autoImplicit false
set_option maxRecDepth 8192
set_option maxHeartbeats 3000000
noncomputable section
namespace AgentUCTNativeRefinement
open AgentUCTPaper AgentUCTCanonicalBridge Finset

abbrev TokenField := Fin 8
def tokenNames : List String :=
  ["generator_4b_input_tokens","generator_4b_output_tokens",
   "query_embedding_06b_input_tokens","reranker_06b_input_tokens",
   "e5_input_tokens","bge_m3_input_tokens","actor_scoring_tokens","index_build_tokens"]

def parameterWeights (generator e5 bge qwen : ℝ) (field : TokenField) : ℝ :=
  if field = 0 ∨ field = 1 then generator else
  if field = 2 ∨ field = 7 then qwen else
  if field = 4 then e5 else if field = 5 then bge else 0

def oneField (field : TokenField) (count : ℕ) : TokenField → ℕ :=
  fun f => if f = field then count else 0



def generatorUsage (count : ℕ) : TokenField → ℕ :=
  fun f => if f = 0 ∨ f = 1 then count else 0



def usedTokens (queryTokens generatorTokens e5Tokens bgeTokens qwenTokens : ℕ) :
    Act → TokenField → ℕ
  | .query q => if q = identityQuery then oneField 0 0 else generatorUsage queryTokens
  | .hydeRetriever r => if r = 0 then oneField 4 e5Tokens
      else if r = 1 then oneField 5 bgeTokens else oneField 2 qwenTokens
  | .width _ => generatorUsage generatorTokens
  | .answer m => generatorUsage (if m = 2 then 11*generatorTokens else generatorTokens)
  | _ => oneField 0 0

def ObservedAction (action : Act) : Prop :=
  (∀ r : Fin 30, action = .normalRetriever r → r = 0) ∧
  (∀ r : Fin 2, action = .reranker r → r = 0)

theorem one_field_bill (weights : TokenField → ℝ) (field : TokenField) (count : ℕ) :
    parameterTokenBill Finset.univ weights (oneField field count) =
      (count : ℝ) * weights field := by
  simp [parameterTokenBill,oneField]

theorem generator_usage_bill (generator e5 bge qwen : ℝ) (count : ℕ) :
    parameterTokenBill Finset.univ (parameterWeights generator e5 bge qwen)
      (generatorUsage count) = 2*(count : ℝ)*generator := by
  simp +decide [parameterTokenBill,generatorUsage,parameterWeights,finUniv8_explicit]
  ring

theorem observed_action_physical_bill (generator e5 bge qwen : ℝ)
    (nq na ne nb nk : ℕ) (action : Act) (ha : ObservedAction action) :
    parameterTokenBill Finset.univ (parameterWeights generator e5 bge qwen)
      (usedTokens nq na ne nb nk action) =
    actionPrice (2*(nq : ℝ)*generator) (2*(na : ℝ)*generator)
      ((ne : ℝ)*e5) ((nb : ℝ)*bge) ((nk : ℝ)*qwen) action := by
  cases action with
  | query q =>
      by_cases hq : q = identityQuery <;>
        simp [usedTokens,hq,actionPrice,one_field_bill,generator_usage_bill,parameterWeights]
  | normalRetriever r =>
      have hr := ha.1 r rfl
      subst r
      simp [usedTokens,actionPrice,one_field_bill,parameterWeights]
  | hydeRetriever r =>
      fin_cases r <;> simp [usedTokens,actionPrice,one_field_bill,parameterWeights]
  | width w => simp [usedTokens,actionPrice,generator_usage_bill]
  | answer m =>
      fin_cases m <;> simp [usedTokens,actionPrice,generator_usage_bill] <;> ring
  | selection s => simp [usedTokens,actionPrice,one_field_bill]
  | stop => simp [usedTokens,actionPrice,one_field_bill]
  | reranker r => simp [usedTokens,actionPrice,one_field_bill]
  | topm m => simp [usedTokens,actionPrice,one_field_bill]
  | context c => simp [usedTokens,actionPrice,one_field_bill]



theorem stationary_hierarchy_mean {I : Type*} (value : ℝ) (samples : Finset I) :
    onlineMean value samples (fun _ => value) = value := by
  unfold onlineMean
  simp only [Finset.sum_const,nsmul_eq_mul]
  have hd : (samples.card : ℝ)+1 ≠ 0 := by positivity
  apply (div_eq_iff hd).2
  ring

theorem clipped_mean_can_drift (prior actual cap : ℝ) (hprior : prior = actual)
    (hcap : cap < actual) :
    (prior + min actual cap) / 2 < actual := by
  rw [hprior,min_eq_right (le_of_lt hcap)]
  linarith



theorem one_receipt_prediction_error (prior actual : ℝ) :
    |(prior+actual)/2 - actual| = |prior-actual|/2 := by
  rw [show (prior+actual)/2 - actual = (prior-actual)/2 by ring,abs_div]
  norm_num

theorem no_recurring_model_overhead_on_zero_tokens (weights : TokenField → ℝ)
    (h : ℝ) (hh : 0 < h) :
    ¬ h = parameterTokenBill Finset.univ weights (fun _ => 0) := by
  intro he
  have hz := no_tokens_no_charge Finset.univ weights (fun _ => 0) (by simp)
  linarith

end AgentUCTNativeRefinement
