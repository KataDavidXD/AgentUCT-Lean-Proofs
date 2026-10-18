import ConcreteProposals
import ReplayPrefixMembership

set_option autoImplicit false
set_option maxRecDepth 32768
set_option maxHeartbeats 16000000
noncomputable section
namespace AgentUCTRealIndex
open AgentUCT32MConcrete AgentUCT32MContinuation AgentUCTSavedBudget
  AgentUCTObservability AgentUCTPhysicalDiagnostic AgentUCTNativeBudget
  AgentUCTPanelAllocation AgentUCTNativeRepair AgentUCTNativeRefinement AgentUCTPaper




def actionCode : Act → ℕ
  | .query i => i.val+1
  | .normalRetriever i => i.val+9
  | .hydeRetriever i => i.val+39
  | .selection i => i.val+42
  | .width i => i.val+46
  | .stop => 50
  | .reranker i => i.val+51
  | .topm i => i.val+53
  | .context i => i.val+56
  | .answer i => i.val+59

def pathCode (p : List Act) : ℕ := p.foldl (fun n a => n*64+actionCode a) 0

def rationalInvoice (events : List (TreeEvaluation Act)) : ℚ :=
  150 * ∑ p ∈ pathHistoryCache events, rationalActionPrice (p.getLastD .stop)

theorem completed_bill_rational_invoice (events : List (TreeEvaluation Act)) :
    completedBill unitRoleUnused events = (rationalInvoice events : ℝ) := by
  rw [completed_physical_bill_full_panel_projection]
  simp_rw [completed_price_rational_projection]
  unfold rationalInvoice
  push_cast
  rfl

end AgentUCTRealIndex
