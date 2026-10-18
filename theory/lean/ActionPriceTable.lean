import CompletedPanelError
set_option autoImplicit false
set_option maxRecDepth 16384
set_option maxHeartbeats 16000000
noncomputable section
namespace AgentUCT32MConcrete
open AgentUCT32MContinuation AgentUCTSavedBudget AgentUCTObservability
  AgentUCTPhysicalDiagnostic AgentUCTNativeBudget AgentUCTPanelAllocation
  AgentUCTNativeRepair AgentUCTNativeRefinement AgentUCTPaper

def rationalActionPrice : Act → ℚ
  | .stop => 0
  | .query i => match i.val with
    | 0 => 4205751296/1953125
    | 1 => 4205751296/1953125
    | 2 => 0
    | 3 => 4205751296/1953125
    | 4 => 4205751296/1953125
    | 5 => 4205751296/1953125
    | 6 => 4205751296/1953125
    | _ => 4205751296/1953125
  | .normalRetriever i => match i.val with
    | 0 => 0
    | 1 => 85533/31250
    | 2 => 1163626/1953125
    | 3 => 1274064129/1000000000
    | 4 => 568805377/1000000000
    | 5 => 568805377/1000000000
    | 6 => 568805377/1000000000
    | 7 => 568805377/1000000000
    | 8 => 568805377/1000000000
    | 9 => 85533/781250
    | 10 => 85533/781250
    | 11 => 85533/781250
    | 12 => 568805377/1000000000
    | 13 => 568805377/1000000000
    | 14 => 568805377/1000000000
    | 15 => 1163626/1953125
    | 16 => 1163626/1953125
    | 17 => 1163626/1953125
    | 18 => 678287617/1000000000
    | 19 => 678287617/1000000000
    | 20 => 678287617/1000000000
    | 21 => 1274064129/1000000000
    | 22 => 1274064129/1000000000
    | 23 => 1274064129/1000000000
    | 24 => 85533/781250
    | 25 => 85533/781250
    | 26 => 85533/781250
    | 27 => 1163626/1953125
    | 28 => 1163626/1953125
    | _ => 1163626/1953125
  | .hydeRetriever i => match i.val with
    | 0 => 3164721/781250
    | 1 => 10807302163/500000000
    | _ => 45381414/1953125
  | .selection i => match i.val with
    | 0 => 0
    | 1 => 0
    | 2 => 0
    | _ => 0
  | .width i => match i.val with
    | 0 => 4205751296/1953125
    | 1 => 525718912/390625
    | 2 => 16428716/1953125
    | _ => 16428716/1953125
  | .reranker i => match i.val with
    | 0 => 0
    | _ => 134584041472/1953125
  | .topm i => match i.val with
    | 0 => 0
    | 1 => 0
    | _ => 0
  | .context i => match i.val with
    | 0 => 0
    | 1 => 0
    | _ => 0
  | .answer i => match i.val with
    | 0 => 10736165906/1953125
    | 1 => 16428716/1953125
    | _ => 16823005184/1953125

theorem completed_price_rational_projection (a : Act) :
    completedPrice unitRoleUnused a = (rationalActionPrice a : ℝ) := by
  cases a with
  | stop => norm_num [rationalActionPrice,completedPrice,completedCounts,CoveredNativeAction,modelTokenBill,Fin.sum_univ_succ,frozenWeights,unitRoleUnused,fullRoleFields,fullNormalRoles,generatorRate,e5Rate,bgeRate,embeddingRate,sourceRoleFields,Fin.succ,Matrix.cons_val_zero,Matrix.cons_val_succ,invoiceCounts,integerTariffs,perturbedCaps,tariff] <;> simp +decide [unitRoleUnused,fullRoleFields,sourceRoleFields] <;> norm_num
  | query i => fin_cases i <;> (norm_num [rationalActionPrice,completedPrice,completedCounts,CoveredNativeAction,modelTokenBill,Fin.sum_univ_succ,frozenWeights,unitRoleUnused,fullRoleFields,fullNormalRoles,generatorRate,e5Rate,bgeRate,embeddingRate,sourceRoleFields,Fin.succ,Matrix.cons_val_zero,Matrix.cons_val_succ,invoiceCounts,integerTariffs,perturbedCaps,tariff] <;> simp +decide [unitRoleUnused,fullRoleFields,sourceRoleFields] <;> norm_num)
  | normalRetriever i => fin_cases i <;> (norm_num [rationalActionPrice,completedPrice,completedCounts,CoveredNativeAction,modelTokenBill,Fin.sum_univ_succ,frozenWeights,unitRoleUnused,fullRoleFields,fullNormalRoles,generatorRate,e5Rate,bgeRate,embeddingRate,sourceRoleFields,Fin.succ,Matrix.cons_val_zero,Matrix.cons_val_succ,invoiceCounts,integerTariffs,perturbedCaps,tariff] <;> simp +decide [unitRoleUnused,fullRoleFields,sourceRoleFields] <;> norm_num)
  | hydeRetriever i => fin_cases i <;> (norm_num [rationalActionPrice,completedPrice,completedCounts,CoveredNativeAction,modelTokenBill,Fin.sum_univ_succ,frozenWeights,unitRoleUnused,fullRoleFields,fullNormalRoles,generatorRate,e5Rate,bgeRate,embeddingRate,sourceRoleFields,Fin.succ,Matrix.cons_val_zero,Matrix.cons_val_succ,invoiceCounts,integerTariffs,perturbedCaps,tariff] <;> simp +decide [unitRoleUnused,fullRoleFields,sourceRoleFields] <;> norm_num)
  | selection i => fin_cases i <;> (norm_num [rationalActionPrice,completedPrice,completedCounts,CoveredNativeAction,modelTokenBill,Fin.sum_univ_succ,frozenWeights,unitRoleUnused,fullRoleFields,fullNormalRoles,generatorRate,e5Rate,bgeRate,embeddingRate,sourceRoleFields,Fin.succ,Matrix.cons_val_zero,Matrix.cons_val_succ,invoiceCounts,integerTariffs,perturbedCaps,tariff] <;> simp +decide [unitRoleUnused,fullRoleFields,sourceRoleFields] <;> norm_num)
  | width i => fin_cases i <;> (norm_num [rationalActionPrice,completedPrice,completedCounts,CoveredNativeAction,modelTokenBill,Fin.sum_univ_succ,frozenWeights,unitRoleUnused,fullRoleFields,fullNormalRoles,generatorRate,e5Rate,bgeRate,embeddingRate,sourceRoleFields,Fin.succ,Matrix.cons_val_zero,Matrix.cons_val_succ,invoiceCounts,integerTariffs,perturbedCaps,tariff] <;> simp +decide [unitRoleUnused,fullRoleFields,sourceRoleFields] <;> norm_num)
  | reranker i => fin_cases i <;> (norm_num [rationalActionPrice,completedPrice,completedCounts,CoveredNativeAction,modelTokenBill,Fin.sum_univ_succ,frozenWeights,unitRoleUnused,fullRoleFields,fullNormalRoles,generatorRate,e5Rate,bgeRate,embeddingRate,sourceRoleFields,Fin.succ,Matrix.cons_val_zero,Matrix.cons_val_succ,invoiceCounts,integerTariffs,perturbedCaps,tariff] <;> simp +decide [unitRoleUnused,fullRoleFields,sourceRoleFields] <;> norm_num)
  | topm i => fin_cases i <;> (norm_num [rationalActionPrice,completedPrice,completedCounts,CoveredNativeAction,modelTokenBill,Fin.sum_univ_succ,frozenWeights,unitRoleUnused,fullRoleFields,fullNormalRoles,generatorRate,e5Rate,bgeRate,embeddingRate,sourceRoleFields,Fin.succ,Matrix.cons_val_zero,Matrix.cons_val_succ,invoiceCounts,integerTariffs,perturbedCaps,tariff] <;> simp +decide [unitRoleUnused,fullRoleFields,sourceRoleFields] <;> norm_num)
  | context i => fin_cases i <;> (norm_num [rationalActionPrice,completedPrice,completedCounts,CoveredNativeAction,modelTokenBill,Fin.sum_univ_succ,frozenWeights,unitRoleUnused,fullRoleFields,fullNormalRoles,generatorRate,e5Rate,bgeRate,embeddingRate,sourceRoleFields,Fin.succ,Matrix.cons_val_zero,Matrix.cons_val_succ,invoiceCounts,integerTariffs,perturbedCaps,tariff] <;> simp +decide [unitRoleUnused,fullRoleFields,sourceRoleFields] <;> norm_num)
  | answer i => fin_cases i <;> (norm_num [rationalActionPrice,completedPrice,completedCounts,CoveredNativeAction,modelTokenBill,Fin.sum_univ_succ,frozenWeights,unitRoleUnused,fullRoleFields,fullNormalRoles,generatorRate,e5Rate,bgeRate,embeddingRate,sourceRoleFields,Fin.succ,Matrix.cons_val_zero,Matrix.cons_val_succ,invoiceCounts,integerTariffs,perturbedCaps,tariff] <;> simp +decide [unitRoleUnused,fullRoleFields,sourceRoleFields] <;> norm_num)

end AgentUCT32MConcrete
