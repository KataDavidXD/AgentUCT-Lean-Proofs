import ActionPriceTable
set_option autoImplicit false
set_option maxRecDepth 16384
set_option maxHeartbeats 10000000
noncomputable section
namespace AgentUCT32MConcrete
open AgentUCT32MContinuation AgentUCTSavedBudget AgentUCTObservability
  AgentUCTPhysicalDiagnostic AgentUCTNativeBudget AgentUCTPanelAllocation
  AgentUCTNativeRepair AgentUCTNativeRefinement AgentUCTPaper



def favorableCompleteEvent1 : TreeEvaluation Act :=
  ⟨[.query 0],[.query 0,.normalRetriever 0,.selection 0,.width 0,.stop,.reranker 0,.topm 0,.context 0,.answer 0],(taskReward false (2/5) (1/2)) [.query 0,.normalRetriever 0,.selection 0,.width 0,.stop,.reranker 0,.topm 0,.context 0,.answer 0],0,by decide⟩

def favorableCompleteEvent2 : TreeEvaluation Act :=
  ⟨[.query 1],[.query 1,.hydeRetriever 0,.selection 0,.width 0,.stop,.reranker 0,.topm 0,.context 0,.answer 0],(taskReward false (2/5) (1/2)) [.query 1,.hydeRetriever 0,.selection 0,.width 0,.stop,.reranker 0,.topm 0,.context 0,.answer 0],0,by decide⟩

def favorableCompleteEvent3 : TreeEvaluation Act :=
  ⟨[.query 2],[.query 2,.normalRetriever 0,.selection 0,.width 0,.stop,.reranker 0,.topm 0,.context 0,.answer 0],(taskReward false (2/5) (1/2)) [.query 2,.normalRetriever 0,.selection 0,.width 0,.stop,.reranker 0,.topm 0,.context 0,.answer 0],0,by decide⟩

def favorableCompleteEvent4 : TreeEvaluation Act :=
  ⟨[.query 3],[.query 3,.normalRetriever 0,.selection 0,.width 0,.stop,.reranker 0,.topm 0,.context 0,.answer 0],(taskReward false (2/5) (1/2)) [.query 3,.normalRetriever 0,.selection 0,.width 0,.stop,.reranker 0,.topm 0,.context 0,.answer 0],0,by decide⟩

def favorableCompleteEvent5 : TreeEvaluation Act :=
  ⟨[.query 4],[.query 4,.normalRetriever 0,.selection 0,.width 0,.stop,.reranker 0,.topm 0,.context 0,.answer 0],(taskReward false (2/5) (1/2)) [.query 4,.normalRetriever 0,.selection 0,.width 0,.stop,.reranker 0,.topm 0,.context 0,.answer 0],0,by decide⟩

def favorableCompleteEvent6 : TreeEvaluation Act :=
  ⟨[.query 5],[.query 5,.normalRetriever 0,.selection 0,.width 0,.stop,.reranker 0,.topm 0,.context 0,.answer 0],(taskReward false (2/5) (1/2)) [.query 5,.normalRetriever 0,.selection 0,.width 0,.stop,.reranker 0,.topm 0,.context 0,.answer 0],0,by decide⟩

def favorableCompleteEvent7 : TreeEvaluation Act :=
  ⟨[.query 6],[.query 6,.normalRetriever 0,.selection 0,.width 0,.stop,.reranker 0,.topm 0,.context 0,.answer 0],(taskReward false (2/5) (1/2)) [.query 6,.normalRetriever 0,.selection 0,.width 0,.stop,.reranker 0,.topm 0,.context 0,.answer 0],0,by decide⟩

def favorableCompleteEvent8 : TreeEvaluation Act :=
  ⟨[.query 7],[.query 7,.normalRetriever 0,.selection 0,.width 0,.stop,.reranker 0,.topm 0,.context 0,.answer 0],(taskReward false (2/5) (1/2)) [.query 7,.normalRetriever 0,.selection 0,.width 0,.stop,.reranker 0,.topm 0,.context 0,.answer 0],0,by decide⟩

def favorableCompleteEvent9 : TreeEvaluation Act :=
  ⟨[.query 1,.hydeRetriever 1],[.query 1,.hydeRetriever 1,.selection 0,.width 1,.stop,.reranker 0,.topm 0,.context 0,.answer 0],(taskReward false (2/5) (1/2)) [.query 1,.hydeRetriever 1,.selection 0,.width 1,.stop,.reranker 0,.topm 0,.context 0,.answer 0],0,by decide⟩

def favorableCompleteEvent10 : TreeEvaluation Act :=
  ⟨[.query 1,.hydeRetriever 0],[.query 1,.hydeRetriever 0,.selection 0,.width 0,.stop,.reranker 0,.topm 0,.context 0,.answer 0],(taskReward false (2/5) (1/2)) [.query 1,.hydeRetriever 0,.selection 0,.width 0,.stop,.reranker 0,.topm 0,.context 0,.answer 0],0,by decide⟩

def favorableCompleteEvent11 : TreeEvaluation Act :=
  ⟨[.query 1,.hydeRetriever 2],[.query 1,.hydeRetriever 2,.selection 0,.width 0,.stop,.reranker 0,.topm 2,.context 0,.answer 2],(taskReward false (2/5) (1/2)) [.query 1,.hydeRetriever 2,.selection 0,.width 0,.stop,.reranker 0,.topm 2,.context 0,.answer 2],0,by decide⟩

def favorableCompleteEvent12 : TreeEvaluation Act :=
  ⟨[.query 1,.hydeRetriever 1,.selection 0],[.query 1,.hydeRetriever 1,.selection 0,.width 1,.stop,.reranker 0,.topm 0,.context 0,.answer 0],(taskReward false (2/5) (1/2)) [.query 1,.hydeRetriever 1,.selection 0,.width 1,.stop,.reranker 0,.topm 0,.context 0,.answer 0],0,by decide⟩

def favorableCompleteEvent13 : TreeEvaluation Act :=
  ⟨[.query 1,.hydeRetriever 0,.selection 0],[.query 1,.hydeRetriever 0,.selection 0,.width 0,.stop,.reranker 0,.topm 0,.context 0,.answer 0],(taskReward false (2/5) (1/2)) [.query 1,.hydeRetriever 0,.selection 0,.width 0,.stop,.reranker 0,.topm 0,.context 0,.answer 0],0,by decide⟩

def favorableCompleteEvent14 : TreeEvaluation Act :=
  ⟨[.query 1,.hydeRetriever 2,.selection 0],[.query 1,.hydeRetriever 2,.selection 0,.width 0,.stop,.reranker 0,.topm 2,.context 0,.answer 2],(taskReward false (2/5) (1/2)) [.query 1,.hydeRetriever 2,.selection 0,.width 0,.stop,.reranker 0,.topm 2,.context 0,.answer 2],0,by decide⟩

def favorableCompleteEvent15 : TreeEvaluation Act :=
  ⟨[.query 1,.hydeRetriever 1,.selection 1],[.query 1,.hydeRetriever 1,.selection 1,.width 0,.stop,.reranker 0,.topm 0,.context 0,.answer 0],(taskReward false (2/5) (1/2)) [.query 1,.hydeRetriever 1,.selection 1,.width 0,.stop,.reranker 0,.topm 0,.context 0,.answer 0],0,by decide⟩

def favorableCompleteEvent16 : TreeEvaluation Act :=
  ⟨[.query 1,.hydeRetriever 1,.selection 2],[.query 1,.hydeRetriever 1,.selection 2,.width 0,.stop,.reranker 0,.topm 0,.context 0,.answer 0],(taskReward false (2/5) (1/2)) [.query 1,.hydeRetriever 1,.selection 2,.width 0,.stop,.reranker 0,.topm 0,.context 0,.answer 0],0,by decide⟩

def favorableCompleteEvent17 : TreeEvaluation Act :=
  ⟨[.query 1,.hydeRetriever 0,.selection 1],[.query 1,.hydeRetriever 0,.selection 1,.width 0,.stop,.reranker 0,.topm 0,.context 0,.answer 0],(taskReward false (2/5) (1/2)) [.query 1,.hydeRetriever 0,.selection 1,.width 0,.stop,.reranker 0,.topm 0,.context 0,.answer 0],0,by decide⟩

def favorableCompleteEvent18 : TreeEvaluation Act :=
  ⟨[.query 1,.hydeRetriever 2,.selection 1],[.query 1,.hydeRetriever 2,.selection 1,.width 0,.stop,.reranker 0,.topm 0,.context 0,.answer 0],(taskReward false (2/5) (1/2)) [.query 1,.hydeRetriever 2,.selection 1,.width 0,.stop,.reranker 0,.topm 0,.context 0,.answer 0],0,by decide⟩

def favorableCompleteEvent19 : TreeEvaluation Act :=
  ⟨[.query 1,.hydeRetriever 1,.selection 3],[.query 1,.hydeRetriever 1,.selection 3,.width 0,.stop,.reranker 0,.topm 0,.context 0,.answer 0],(taskReward false (2/5) (1/2)) [.query 1,.hydeRetriever 1,.selection 3,.width 0,.stop,.reranker 0,.topm 0,.context 0,.answer 0],0,by decide⟩

def favorableCompleteEvent20 : TreeEvaluation Act :=
  ⟨[.query 1,.hydeRetriever 0,.selection 2],[.query 1,.hydeRetriever 0,.selection 2,.width 0,.stop,.reranker 0,.topm 0,.context 0,.answer 0],(taskReward false (2/5) (1/2)) [.query 1,.hydeRetriever 0,.selection 2,.width 0,.stop,.reranker 0,.topm 0,.context 0,.answer 0],0,by decide⟩

def favorableCompleteEvent21 : TreeEvaluation Act :=
  ⟨[.query 1,.hydeRetriever 2,.selection 2],[.query 1,.hydeRetriever 2,.selection 2,.width 0,.stop,.reranker 0,.topm 0,.context 0,.answer 0],(taskReward false (2/5) (1/2)) [.query 1,.hydeRetriever 2,.selection 2,.width 0,.stop,.reranker 0,.topm 0,.context 0,.answer 0],0,by decide⟩

def favorableCompleteEvent22 : TreeEvaluation Act :=
  ⟨[.query 1,.hydeRetriever 1,.selection 0,.width 1],[.query 1,.hydeRetriever 1,.selection 0,.width 1,.stop,.reranker 0,.topm 0,.context 0,.answer 0],(taskReward false (2/5) (1/2)) [.query 1,.hydeRetriever 1,.selection 0,.width 1,.stop,.reranker 0,.topm 0,.context 0,.answer 0],0,by decide⟩

def favorableCompleteEvent23 : TreeEvaluation Act :=
  ⟨[.query 1,.hydeRetriever 1,.selection 1,.width 0],[.query 1,.hydeRetriever 1,.selection 1,.width 0,.stop,.reranker 0,.topm 0,.context 0,.answer 0],(taskReward false (2/5) (1/2)) [.query 1,.hydeRetriever 1,.selection 1,.width 0,.stop,.reranker 0,.topm 0,.context 0,.answer 0],0,by decide⟩

def favorableCompleteEvent24 : TreeEvaluation Act :=
  ⟨[.query 1,.hydeRetriever 0,.selection 3],[.query 1,.hydeRetriever 0,.selection 3,.width 0,.stop,.reranker 0,.topm 0,.context 0,.answer 0],(taskReward false (2/5) (1/2)) [.query 1,.hydeRetriever 0,.selection 3,.width 0,.stop,.reranker 0,.topm 0,.context 0,.answer 0],0,by decide⟩

def favorableCompleteEvent25 : TreeEvaluation Act :=
  ⟨[.query 1,.hydeRetriever 2,.selection 3],[.query 1,.hydeRetriever 2,.selection 3,.width 0,.stop,.reranker 0,.topm 0,.context 0,.answer 0],(taskReward false (2/5) (1/2)) [.query 1,.hydeRetriever 2,.selection 3,.width 0,.stop,.reranker 0,.topm 0,.context 0,.answer 0],0,by decide⟩

def favorableCompleteEvent26 : TreeEvaluation Act :=
  ⟨[.query 1,.hydeRetriever 1,.selection 2,.width 0],[.query 1,.hydeRetriever 1,.selection 2,.width 0,.stop,.reranker 0,.topm 0,.context 0,.answer 0],(taskReward false (2/5) (1/2)) [.query 1,.hydeRetriever 1,.selection 2,.width 0,.stop,.reranker 0,.topm 0,.context 0,.answer 0],0,by decide⟩

def favorableCompleteEvent27 : TreeEvaluation Act :=
  ⟨[.query 1,.hydeRetriever 0,.selection 1,.width 0],[.query 1,.hydeRetriever 0,.selection 1,.width 0,.stop,.reranker 0,.topm 0,.context 0,.answer 0],(taskReward false (2/5) (1/2)) [.query 1,.hydeRetriever 0,.selection 1,.width 0,.stop,.reranker 0,.topm 0,.context 0,.answer 0],0,by decide⟩

def favorableCompleteEvent28 : TreeEvaluation Act :=
  ⟨[.query 1,.hydeRetriever 2,.selection 1,.width 0],[.query 1,.hydeRetriever 2,.selection 1,.width 0,.stop,.reranker 0,.topm 0,.context 0,.answer 0],(taskReward false (2/5) (1/2)) [.query 1,.hydeRetriever 2,.selection 1,.width 0,.stop,.reranker 0,.topm 0,.context 0,.answer 0],0,by decide⟩

def favorableCompleteEvent29 : TreeEvaluation Act :=
  ⟨[.query 1,.hydeRetriever 1,.selection 3,.width 0],[.query 1,.hydeRetriever 1,.selection 3,.width 0,.stop,.reranker 0,.topm 0,.context 0,.answer 0],(taskReward false (2/5) (1/2)) [.query 1,.hydeRetriever 1,.selection 3,.width 0,.stop,.reranker 0,.topm 0,.context 0,.answer 0],0,by decide⟩

def favorableCompleteEvent30 : TreeEvaluation Act :=
  ⟨[.query 1,.hydeRetriever 0,.selection 2,.width 0],[.query 1,.hydeRetriever 0,.selection 2,.width 0,.stop,.reranker 0,.topm 0,.context 0,.answer 0],(taskReward false (2/5) (1/2)) [.query 1,.hydeRetriever 0,.selection 2,.width 0,.stop,.reranker 0,.topm 0,.context 0,.answer 0],0,by decide⟩

def favorableCompleteEvent31 : TreeEvaluation Act :=
  ⟨[.query 1,.hydeRetriever 2,.selection 2,.width 0],[.query 1,.hydeRetriever 2,.selection 2,.width 0,.stop,.reranker 0,.topm 0,.context 0,.answer 0],(taskReward false (2/5) (1/2)) [.query 1,.hydeRetriever 2,.selection 2,.width 0,.stop,.reranker 0,.topm 0,.context 0,.answer 0],0,by decide⟩

def favorableCompleteEvent32 : TreeEvaluation Act :=
  ⟨[.query 1,.hydeRetriever 1,.selection 0,.width 3],[.query 1,.hydeRetriever 1,.selection 0,.width 3,.stop,.reranker 0,.topm 0,.context 0,.answer 0],(taskReward false (2/5) (1/2)) [.query 1,.hydeRetriever 1,.selection 0,.width 3,.stop,.reranker 0,.topm 0,.context 0,.answer 0],0,by decide⟩

def favorableCompleteEvent33 : TreeEvaluation Act :=
  ⟨[.query 1,.hydeRetriever 0,.selection 3,.width 0],[.query 1,.hydeRetriever 0,.selection 3,.width 0,.stop,.reranker 0,.topm 0,.context 0,.answer 0],(taskReward false (2/5) (1/2)) [.query 1,.hydeRetriever 0,.selection 3,.width 0,.stop,.reranker 0,.topm 0,.context 0,.answer 0],0,by decide⟩

def favorableCompleteEvent34 : TreeEvaluation Act :=
  ⟨[.query 1,.hydeRetriever 2,.selection 3,.width 0],[.query 1,.hydeRetriever 2,.selection 3,.width 0,.stop,.reranker 0,.topm 0,.context 0,.answer 0],(taskReward false (2/5) (1/2)) [.query 1,.hydeRetriever 2,.selection 3,.width 0,.stop,.reranker 0,.topm 0,.context 0,.answer 0],0,by decide⟩

def favorableCompleteEvent35 : TreeEvaluation Act :=
  ⟨[.query 1,.hydeRetriever 1,.selection 0,.width 0],[.query 1,.hydeRetriever 1,.selection 0,.width 0,.stop,.reranker 0,.topm 0,.context 0,.answer 0],(taskReward false (2/5) (1/2)) [.query 1,.hydeRetriever 1,.selection 0,.width 0,.stop,.reranker 0,.topm 0,.context 0,.answer 0],0,by decide⟩

def favorableCompleteEvent36 : TreeEvaluation Act :=
  ⟨[.query 1,.hydeRetriever 1,.selection 1,.width 3],[.query 1,.hydeRetriever 1,.selection 1,.width 3,.stop,.reranker 0,.topm 0,.context 0,.answer 0],(taskReward false (2/5) (1/2)) [.query 1,.hydeRetriever 1,.selection 1,.width 3,.stop,.reranker 0,.topm 0,.context 0,.answer 0],0,by decide⟩

def favorableCompleteEvent37 : TreeEvaluation Act :=
  ⟨[.query 1,.hydeRetriever 0,.selection 0,.width 0],[.query 1,.hydeRetriever 0,.selection 0,.width 0,.stop,.reranker 0,.topm 0,.context 0,.answer 0],(taskReward false (2/5) (1/2)) [.query 1,.hydeRetriever 0,.selection 0,.width 0,.stop,.reranker 0,.topm 0,.context 0,.answer 0],0,by decide⟩

def favorableCompleteEvent38 : TreeEvaluation Act :=
  ⟨[.query 1,.hydeRetriever 2,.selection 0,.width 0],[.query 1,.hydeRetriever 2,.selection 0,.width 0,.stop,.reranker 0,.topm 2,.context 0,.answer 2],(taskReward false (2/5) (1/2)) [.query 1,.hydeRetriever 2,.selection 0,.width 0,.stop,.reranker 0,.topm 2,.context 0,.answer 2],0,by decide⟩

def favorableCompleteEvent39 : TreeEvaluation Act :=
  ⟨[.query 1,.hydeRetriever 1,.selection 2,.width 3],[.query 1,.hydeRetriever 1,.selection 2,.width 3,.stop,.reranker 0,.topm 0,.context 0,.answer 0],(taskReward false (2/5) (1/2)) [.query 1,.hydeRetriever 1,.selection 2,.width 3,.stop,.reranker 0,.topm 0,.context 0,.answer 0],0,by decide⟩

def favorableCompleteEvent40 : TreeEvaluation Act :=
  ⟨[.query 1,.hydeRetriever 0,.selection 1,.width 3],[.query 1,.hydeRetriever 0,.selection 1,.width 3,.stop,.reranker 0,.topm 0,.context 0,.answer 0],(taskReward false (2/5) (1/2)) [.query 1,.hydeRetriever 0,.selection 1,.width 3,.stop,.reranker 0,.topm 0,.context 0,.answer 0],0,by decide⟩

def favorableCompleteEvent41 : TreeEvaluation Act :=
  ⟨[.query 1,.hydeRetriever 2,.selection 1,.width 3],[.query 1,.hydeRetriever 2,.selection 1,.width 3,.stop,.reranker 0,.topm 0,.context 0,.answer 0],(taskReward false (2/5) (1/2)) [.query 1,.hydeRetriever 2,.selection 1,.width 3,.stop,.reranker 0,.topm 0,.context 0,.answer 0],0,by decide⟩

def favorableCompleteEvent42 : TreeEvaluation Act :=
  ⟨[.query 1,.hydeRetriever 1,.selection 3,.width 3],[.query 1,.hydeRetriever 1,.selection 3,.width 3,.stop,.reranker 0,.topm 0,.context 0,.answer 0],(taskReward false (2/5) (1/2)) [.query 1,.hydeRetriever 1,.selection 3,.width 3,.stop,.reranker 0,.topm 0,.context 0,.answer 0],0,by decide⟩

def favorableCompleteEvent43 : TreeEvaluation Act :=
  ⟨[.query 1,.hydeRetriever 0,.selection 2,.width 3],[.query 1,.hydeRetriever 0,.selection 2,.width 3,.stop,.reranker 0,.topm 0,.context 0,.answer 0],(taskReward false (2/5) (1/2)) [.query 1,.hydeRetriever 0,.selection 2,.width 3,.stop,.reranker 0,.topm 0,.context 0,.answer 0],0,by decide⟩

def favorableCompleteEvent44 : TreeEvaluation Act :=
  ⟨[.query 1,.hydeRetriever 2,.selection 2,.width 3],[.query 1,.hydeRetriever 2,.selection 2,.width 3,.stop,.reranker 0,.topm 0,.context 0,.answer 0],(taskReward false (2/5) (1/2)) [.query 1,.hydeRetriever 2,.selection 2,.width 3,.stop,.reranker 0,.topm 0,.context 0,.answer 0],0,by decide⟩

def favorableCompleteProposal : List (TreeEvaluation Act) :=
  [favorableCompleteEvent1,favorableCompleteEvent2,favorableCompleteEvent3,favorableCompleteEvent4,favorableCompleteEvent5,favorableCompleteEvent6,favorableCompleteEvent7,favorableCompleteEvent8,favorableCompleteEvent9,favorableCompleteEvent10,favorableCompleteEvent11,favorableCompleteEvent12,favorableCompleteEvent13,favorableCompleteEvent14,favorableCompleteEvent15,favorableCompleteEvent16,favorableCompleteEvent17,favorableCompleteEvent18,favorableCompleteEvent19,favorableCompleteEvent20,favorableCompleteEvent21,favorableCompleteEvent22,favorableCompleteEvent23,favorableCompleteEvent24,favorableCompleteEvent25,favorableCompleteEvent26,favorableCompleteEvent27,favorableCompleteEvent28,favorableCompleteEvent29,favorableCompleteEvent30,favorableCompleteEvent31,favorableCompleteEvent32,favorableCompleteEvent33,favorableCompleteEvent34,favorableCompleteEvent35,favorableCompleteEvent36,favorableCompleteEvent37,favorableCompleteEvent38,favorableCompleteEvent39,favorableCompleteEvent40,favorableCompleteEvent41,favorableCompleteEvent42,favorableCompleteEvent43,favorableCompleteEvent44]

def favorableNextEvent1 : TreeEvaluation Act :=
  ⟨[.query 0],[.query 0,.normalRetriever 0,.selection 0,.width 0,.stop,.reranker 0,.topm 0,.context 0,.answer 0],(taskReward false (2/5) (1/2)) [.query 0,.normalRetriever 0,.selection 0,.width 0,.stop,.reranker 0,.topm 0,.context 0,.answer 0],0,by decide⟩

def favorableNextEvent2 : TreeEvaluation Act :=
  ⟨[.query 1],[.query 1,.hydeRetriever 0,.selection 0,.width 0,.stop,.reranker 0,.topm 0,.context 0,.answer 0],(taskReward false (2/5) (1/2)) [.query 1,.hydeRetriever 0,.selection 0,.width 0,.stop,.reranker 0,.topm 0,.context 0,.answer 0],0,by decide⟩

def favorableNextEvent3 : TreeEvaluation Act :=
  ⟨[.query 2],[.query 2,.normalRetriever 0,.selection 0,.width 0,.stop,.reranker 0,.topm 0,.context 0,.answer 0],(taskReward false (2/5) (1/2)) [.query 2,.normalRetriever 0,.selection 0,.width 0,.stop,.reranker 0,.topm 0,.context 0,.answer 0],0,by decide⟩

def favorableNextEvent4 : TreeEvaluation Act :=
  ⟨[.query 3],[.query 3,.normalRetriever 0,.selection 0,.width 0,.stop,.reranker 0,.topm 0,.context 0,.answer 0],(taskReward false (2/5) (1/2)) [.query 3,.normalRetriever 0,.selection 0,.width 0,.stop,.reranker 0,.topm 0,.context 0,.answer 0],0,by decide⟩

def favorableNextEvent5 : TreeEvaluation Act :=
  ⟨[.query 4],[.query 4,.normalRetriever 0,.selection 0,.width 0,.stop,.reranker 0,.topm 0,.context 0,.answer 0],(taskReward false (2/5) (1/2)) [.query 4,.normalRetriever 0,.selection 0,.width 0,.stop,.reranker 0,.topm 0,.context 0,.answer 0],0,by decide⟩

def favorableNextEvent6 : TreeEvaluation Act :=
  ⟨[.query 5],[.query 5,.normalRetriever 0,.selection 0,.width 0,.stop,.reranker 0,.topm 0,.context 0,.answer 0],(taskReward false (2/5) (1/2)) [.query 5,.normalRetriever 0,.selection 0,.width 0,.stop,.reranker 0,.topm 0,.context 0,.answer 0],0,by decide⟩

def favorableNextEvent7 : TreeEvaluation Act :=
  ⟨[.query 6],[.query 6,.normalRetriever 0,.selection 0,.width 0,.stop,.reranker 0,.topm 0,.context 0,.answer 0],(taskReward false (2/5) (1/2)) [.query 6,.normalRetriever 0,.selection 0,.width 0,.stop,.reranker 0,.topm 0,.context 0,.answer 0],0,by decide⟩

def favorableNextEvent8 : TreeEvaluation Act :=
  ⟨[.query 7],[.query 7,.normalRetriever 0,.selection 0,.width 0,.stop,.reranker 0,.topm 0,.context 0,.answer 0],(taskReward false (2/5) (1/2)) [.query 7,.normalRetriever 0,.selection 0,.width 0,.stop,.reranker 0,.topm 0,.context 0,.answer 0],0,by decide⟩

def favorableNextEvent9 : TreeEvaluation Act :=
  ⟨[.query 5,.normalRetriever 1],[.query 5,.normalRetriever 1,.selection 0,.width 1,.stop,.reranker 0,.topm 0,.context 0,.answer 0],(taskReward false (2/5) (1/2)) [.query 5,.normalRetriever 1,.selection 0,.width 1,.stop,.reranker 0,.topm 0,.context 0,.answer 0],0,by decide⟩

def favorableNextEvent10 : TreeEvaluation Act :=
  ⟨[.query 1,.hydeRetriever 1],[.query 1,.hydeRetriever 1,.selection 0,.width 1,.stop,.reranker 0,.topm 0,.context 0,.answer 0],(taskReward false (2/5) (1/2)) [.query 1,.hydeRetriever 1,.selection 0,.width 1,.stop,.reranker 0,.topm 0,.context 0,.answer 0],0,by decide⟩

def favorableNextEvent11 : TreeEvaluation Act :=
  ⟨[.query 0,.normalRetriever 0],[.query 0,.normalRetriever 0,.selection 0,.width 0,.stop,.reranker 0,.topm 0,.context 0,.answer 0],(taskReward false (2/5) (1/2)) [.query 0,.normalRetriever 0,.selection 0,.width 0,.stop,.reranker 0,.topm 0,.context 0,.answer 0],0,by decide⟩

def favorableNextEvent12 : TreeEvaluation Act :=
  ⟨[.query 2,.normalRetriever 0],[.query 2,.normalRetriever 0,.selection 0,.width 0,.stop,.reranker 0,.topm 0,.context 0,.answer 0],(taskReward false (2/5) (1/2)) [.query 2,.normalRetriever 0,.selection 0,.width 0,.stop,.reranker 0,.topm 0,.context 0,.answer 0],0,by decide⟩

def favorableNextEvent13 : TreeEvaluation Act :=
  ⟨[.query 3,.normalRetriever 0],[.query 3,.normalRetriever 0,.selection 0,.width 0,.stop,.reranker 0,.topm 0,.context 0,.answer 0],(taskReward false (2/5) (1/2)) [.query 3,.normalRetriever 0,.selection 0,.width 0,.stop,.reranker 0,.topm 0,.context 0,.answer 0],0,by decide⟩

def favorableNextEvent14 : TreeEvaluation Act :=
  ⟨[.query 4,.normalRetriever 0],[.query 4,.normalRetriever 0,.selection 0,.width 0,.stop,.reranker 0,.topm 0,.context 0,.answer 0],(taskReward false (2/5) (1/2)) [.query 4,.normalRetriever 0,.selection 0,.width 0,.stop,.reranker 0,.topm 0,.context 0,.answer 0],0,by decide⟩

def favorableNextEvent15 : TreeEvaluation Act :=
  ⟨[.query 6,.normalRetriever 0],[.query 6,.normalRetriever 0,.selection 0,.width 0,.stop,.reranker 0,.topm 0,.context 0,.answer 0],(taskReward false (2/5) (1/2)) [.query 6,.normalRetriever 0,.selection 0,.width 0,.stop,.reranker 0,.topm 0,.context 0,.answer 0],0,by decide⟩

def favorableNextEvent16 : TreeEvaluation Act :=
  ⟨[.query 7,.normalRetriever 0],[.query 7,.normalRetriever 0,.selection 0,.width 0,.stop,.reranker 0,.topm 0,.context 0,.answer 0],(taskReward false (2/5) (1/2)) [.query 7,.normalRetriever 0,.selection 0,.width 0,.stop,.reranker 0,.topm 0,.context 0,.answer 0],0,by decide⟩

def favorableNextEvent17 : TreeEvaluation Act :=
  ⟨[.query 1,.hydeRetriever 0],[.query 1,.hydeRetriever 0,.selection 0,.width 0,.stop,.reranker 0,.topm 0,.context 0,.answer 0],(taskReward false (2/5) (1/2)) [.query 1,.hydeRetriever 0,.selection 0,.width 0,.stop,.reranker 0,.topm 0,.context 0,.answer 0],0,by decide⟩

def favorableNextEvent18 : TreeEvaluation Act :=
  ⟨[.query 5,.normalRetriever 0],[.query 5,.normalRetriever 0,.selection 0,.width 0,.stop,.reranker 0,.topm 0,.context 0,.answer 0],(taskReward false (2/5) (1/2)) [.query 5,.normalRetriever 0,.selection 0,.width 0,.stop,.reranker 0,.topm 0,.context 0,.answer 0],0,by decide⟩

def favorableNextEvent19 : TreeEvaluation Act :=
  ⟨[.query 1,.hydeRetriever 2],[.query 1,.hydeRetriever 2,.selection 0,.width 0,.stop,.reranker 0,.topm 2,.context 0,.answer 2],(taskReward false (2/5) (1/2)) [.query 1,.hydeRetriever 2,.selection 0,.width 0,.stop,.reranker 0,.topm 2,.context 0,.answer 2],0,by decide⟩

def favorableNextEvent20 : TreeEvaluation Act :=
  ⟨[.query 5,.normalRetriever 4],[.query 5,.normalRetriever 4,.selection 0,.width 0,.stop,.reranker 0,.topm 0,.context 0,.answer 0],(taskReward false (2/5) (1/2)) [.query 5,.normalRetriever 4,.selection 0,.width 0,.stop,.reranker 0,.topm 0,.context 0,.answer 0],0,by decide⟩

def favorableNextEvent21 : TreeEvaluation Act :=
  ⟨[.query 0,.normalRetriever 4],[.query 0,.normalRetriever 4,.selection 0,.width 0,.stop,.reranker 0,.topm 0,.context 0,.answer 0],(taskReward false (2/5) (1/2)) [.query 0,.normalRetriever 4,.selection 0,.width 0,.stop,.reranker 0,.topm 0,.context 0,.answer 0],0,by decide⟩

def favorableNextEvent22 : TreeEvaluation Act :=
  ⟨[.query 2,.normalRetriever 4],[.query 2,.normalRetriever 4,.selection 0,.width 0,.stop,.reranker 0,.topm 0,.context 0,.answer 0],(taskReward false (2/5) (1/2)) [.query 2,.normalRetriever 4,.selection 0,.width 0,.stop,.reranker 0,.topm 0,.context 0,.answer 0],0,by decide⟩

def favorableNextEvent23 : TreeEvaluation Act :=
  ⟨[.query 3,.normalRetriever 4],[.query 3,.normalRetriever 4,.selection 0,.width 0,.stop,.reranker 0,.topm 0,.context 0,.answer 0],(taskReward false (2/5) (1/2)) [.query 3,.normalRetriever 4,.selection 0,.width 0,.stop,.reranker 0,.topm 0,.context 0,.answer 0],0,by decide⟩

def favorableNextEvent24 : TreeEvaluation Act :=
  ⟨[.query 4,.normalRetriever 4],[.query 4,.normalRetriever 4,.selection 0,.width 0,.stop,.reranker 0,.topm 0,.context 0,.answer 0],(taskReward false (2/5) (1/2)) [.query 4,.normalRetriever 4,.selection 0,.width 0,.stop,.reranker 0,.topm 0,.context 0,.answer 0],0,by decide⟩

def favorableNextEvent25 : TreeEvaluation Act :=
  ⟨[.query 6,.normalRetriever 4],[.query 6,.normalRetriever 4,.selection 0,.width 0,.stop,.reranker 0,.topm 0,.context 0,.answer 0],(taskReward false (2/5) (1/2)) [.query 6,.normalRetriever 4,.selection 0,.width 0,.stop,.reranker 0,.topm 0,.context 0,.answer 0],0,by decide⟩

def favorableNextEvent26 : TreeEvaluation Act :=
  ⟨[.query 7,.normalRetriever 4],[.query 7,.normalRetriever 4,.selection 0,.width 0,.stop,.reranker 0,.topm 0,.context 0,.answer 0],(taskReward false (2/5) (1/2)) [.query 7,.normalRetriever 4,.selection 0,.width 0,.stop,.reranker 0,.topm 0,.context 0,.answer 0],0,by decide⟩

def favorableNextEvent27 : TreeEvaluation Act :=
  ⟨[.query 1,.hydeRetriever 1,.selection 0],[.query 1,.hydeRetriever 1,.selection 0,.width 1,.stop,.reranker 0,.topm 0,.context 0,.answer 0],(taskReward false (2/5) (1/2)) [.query 1,.hydeRetriever 1,.selection 0,.width 1,.stop,.reranker 0,.topm 0,.context 0,.answer 0],0,by decide⟩

def favorableNextEvent28 : TreeEvaluation Act :=
  ⟨[.query 1,.hydeRetriever 0,.selection 0],[.query 1,.hydeRetriever 0,.selection 0,.width 0,.stop,.reranker 0,.topm 0,.context 0,.answer 0],(taskReward false (2/5) (1/2)) [.query 1,.hydeRetriever 0,.selection 0,.width 0,.stop,.reranker 0,.topm 0,.context 0,.answer 0],0,by decide⟩

def favorableNextEvent29 : TreeEvaluation Act :=
  ⟨[.query 5,.normalRetriever 6],[.query 5,.normalRetriever 6,.selection 0,.width 0,.stop,.reranker 0,.topm 0,.context 0,.answer 0],(taskReward false (2/5) (1/2)) [.query 5,.normalRetriever 6,.selection 0,.width 0,.stop,.reranker 0,.topm 0,.context 0,.answer 0],0,by decide⟩

def favorableNextEvent30 : TreeEvaluation Act :=
  ⟨[.query 1,.hydeRetriever 2,.selection 0],[.query 1,.hydeRetriever 2,.selection 0,.width 0,.stop,.reranker 0,.topm 2,.context 0,.answer 2],(taskReward false (2/5) (1/2)) [.query 1,.hydeRetriever 2,.selection 0,.width 0,.stop,.reranker 0,.topm 2,.context 0,.answer 2],0,by decide⟩

def favorableNextEvent31 : TreeEvaluation Act :=
  ⟨[.query 0,.normalRetriever 6],[.query 0,.normalRetriever 6,.selection 0,.width 0,.stop,.reranker 0,.topm 0,.context 0,.answer 0],(taskReward false (2/5) (1/2)) [.query 0,.normalRetriever 6,.selection 0,.width 0,.stop,.reranker 0,.topm 0,.context 0,.answer 0],0,by decide⟩

def favorableNextEvent32 : TreeEvaluation Act :=
  ⟨[.query 2,.normalRetriever 6],[.query 2,.normalRetriever 6,.selection 0,.width 0,.stop,.reranker 0,.topm 0,.context 0,.answer 0],(taskReward false (2/5) (1/2)) [.query 2,.normalRetriever 6,.selection 0,.width 0,.stop,.reranker 0,.topm 0,.context 0,.answer 0],0,by decide⟩

def favorableNextEvent33 : TreeEvaluation Act :=
  ⟨[.query 3,.normalRetriever 6],[.query 3,.normalRetriever 6,.selection 0,.width 0,.stop,.reranker 0,.topm 0,.context 0,.answer 0],(taskReward false (2/5) (1/2)) [.query 3,.normalRetriever 6,.selection 0,.width 0,.stop,.reranker 0,.topm 0,.context 0,.answer 0],0,by decide⟩

def favorableNextEvent34 : TreeEvaluation Act :=
  ⟨[.query 4,.normalRetriever 6],[.query 4,.normalRetriever 6,.selection 0,.width 0,.stop,.reranker 0,.topm 0,.context 0,.answer 0],(taskReward false (2/5) (1/2)) [.query 4,.normalRetriever 6,.selection 0,.width 0,.stop,.reranker 0,.topm 0,.context 0,.answer 0],0,by decide⟩

def favorableNextEvent35 : TreeEvaluation Act :=
  ⟨[.query 6,.normalRetriever 6],[.query 6,.normalRetriever 6,.selection 0,.width 0,.stop,.reranker 0,.topm 0,.context 0,.answer 0],(taskReward false (2/5) (1/2)) [.query 6,.normalRetriever 6,.selection 0,.width 0,.stop,.reranker 0,.topm 0,.context 0,.answer 0],0,by decide⟩

def favorableNextEvent36 : TreeEvaluation Act :=
  ⟨[.query 7,.normalRetriever 6],[.query 7,.normalRetriever 6,.selection 0,.width 0,.stop,.reranker 0,.topm 0,.context 0,.answer 0],(taskReward false (2/5) (1/2)) [.query 7,.normalRetriever 6,.selection 0,.width 0,.stop,.reranker 0,.topm 0,.context 0,.answer 0],0,by decide⟩

def favorableNextEvent37 : TreeEvaluation Act :=
  ⟨[.query 5,.normalRetriever 7],[.query 5,.normalRetriever 7,.selection 0,.width 0,.stop,.reranker 0,.topm 0,.context 0,.answer 0],(taskReward false (2/5) (1/2)) [.query 5,.normalRetriever 7,.selection 0,.width 0,.stop,.reranker 0,.topm 0,.context 0,.answer 0],0,by decide⟩

def favorableNextProposal : List (TreeEvaluation Act) :=
  [favorableNextEvent1,favorableNextEvent2,favorableNextEvent3,favorableNextEvent4,favorableNextEvent5,favorableNextEvent6,favorableNextEvent7,favorableNextEvent8,favorableNextEvent9,favorableNextEvent10,favorableNextEvent11,favorableNextEvent12,favorableNextEvent13,favorableNextEvent14,favorableNextEvent15,favorableNextEvent16,favorableNextEvent17,favorableNextEvent18,favorableNextEvent19,favorableNextEvent20,favorableNextEvent21,favorableNextEvent22,favorableNextEvent23,favorableNextEvent24,favorableNextEvent25,favorableNextEvent26,favorableNextEvent27,favorableNextEvent28,favorableNextEvent29,favorableNextEvent30,favorableNextEvent31,favorableNextEvent32,favorableNextEvent33,favorableNextEvent34,favorableNextEvent35,favorableNextEvent36,favorableNextEvent37]

def adverseCompleteEvent1 : TreeEvaluation Act :=
  ⟨[.query 0],[.query 0,.normalRetriever 0,.selection 0,.width 0,.stop,.reranker 0,.topm 0,.context 0,.answer 0],(taskReward true (2/5) (1/2)) [.query 0,.normalRetriever 0,.selection 0,.width 0,.stop,.reranker 0,.topm 0,.context 0,.answer 0],0,by decide⟩

def adverseCompleteEvent2 : TreeEvaluation Act :=
  ⟨[.query 1],[.query 1,.hydeRetriever 0,.selection 0,.width 0,.stop,.reranker 0,.topm 0,.context 0,.answer 0],(taskReward true (2/5) (1/2)) [.query 1,.hydeRetriever 0,.selection 0,.width 0,.stop,.reranker 0,.topm 0,.context 0,.answer 0],0,by decide⟩

def adverseCompleteEvent3 : TreeEvaluation Act :=
  ⟨[.query 2],[.query 2,.normalRetriever 0,.selection 0,.width 0,.stop,.reranker 0,.topm 0,.context 0,.answer 0],(taskReward true (2/5) (1/2)) [.query 2,.normalRetriever 0,.selection 0,.width 0,.stop,.reranker 0,.topm 0,.context 0,.answer 0],0,by decide⟩

def adverseCompleteEvent4 : TreeEvaluation Act :=
  ⟨[.query 3],[.query 3,.normalRetriever 0,.selection 0,.width 0,.stop,.reranker 0,.topm 0,.context 0,.answer 0],(taskReward true (2/5) (1/2)) [.query 3,.normalRetriever 0,.selection 0,.width 0,.stop,.reranker 0,.topm 0,.context 0,.answer 0],0,by decide⟩

def adverseCompleteEvent5 : TreeEvaluation Act :=
  ⟨[.query 4],[.query 4,.normalRetriever 0,.selection 0,.width 0,.stop,.reranker 0,.topm 0,.context 0,.answer 0],(taskReward true (2/5) (1/2)) [.query 4,.normalRetriever 0,.selection 0,.width 0,.stop,.reranker 0,.topm 0,.context 0,.answer 0],0,by decide⟩

def adverseCompleteEvent6 : TreeEvaluation Act :=
  ⟨[.query 5],[.query 5,.normalRetriever 0,.selection 0,.width 0,.stop,.reranker 0,.topm 0,.context 0,.answer 0],(taskReward true (2/5) (1/2)) [.query 5,.normalRetriever 0,.selection 0,.width 0,.stop,.reranker 0,.topm 0,.context 0,.answer 0],0,by decide⟩

def adverseCompleteEvent7 : TreeEvaluation Act :=
  ⟨[.query 6],[.query 6,.normalRetriever 0,.selection 0,.width 0,.stop,.reranker 0,.topm 0,.context 0,.answer 0],(taskReward true (2/5) (1/2)) [.query 6,.normalRetriever 0,.selection 0,.width 0,.stop,.reranker 0,.topm 0,.context 0,.answer 0],0,by decide⟩

def adverseCompleteEvent8 : TreeEvaluation Act :=
  ⟨[.query 7],[.query 7,.normalRetriever 0,.selection 0,.width 0,.stop,.reranker 0,.topm 0,.context 0,.answer 0],(taskReward true (2/5) (1/2)) [.query 7,.normalRetriever 0,.selection 0,.width 0,.stop,.reranker 0,.topm 0,.context 0,.answer 0],0,by decide⟩

def adverseCompleteEvent9 : TreeEvaluation Act :=
  ⟨[.query 1,.hydeRetriever 1],[.query 1,.hydeRetriever 1,.selection 0,.width 1,.stop,.reranker 0,.topm 0,.context 0,.answer 0],(taskReward true (2/5) (1/2)) [.query 1,.hydeRetriever 1,.selection 0,.width 1,.stop,.reranker 0,.topm 0,.context 0,.answer 0],0,by decide⟩

def adverseCompleteEvent10 : TreeEvaluation Act :=
  ⟨[.query 1,.hydeRetriever 0],[.query 1,.hydeRetriever 0,.selection 0,.width 0,.stop,.reranker 0,.topm 0,.context 0,.answer 0],(taskReward true (2/5) (1/2)) [.query 1,.hydeRetriever 0,.selection 0,.width 0,.stop,.reranker 0,.topm 0,.context 0,.answer 0],0,by decide⟩

def adverseCompleteEvent11 : TreeEvaluation Act :=
  ⟨[.query 1,.hydeRetriever 2],[.query 1,.hydeRetriever 2,.selection 0,.width 0,.stop,.reranker 0,.topm 2,.context 0,.answer 2],(taskReward true (2/5) (1/2)) [.query 1,.hydeRetriever 2,.selection 0,.width 0,.stop,.reranker 0,.topm 2,.context 0,.answer 2],0,by decide⟩

def adverseCompleteEvent12 : TreeEvaluation Act :=
  ⟨[.query 1,.hydeRetriever 1,.selection 0],[.query 1,.hydeRetriever 1,.selection 0,.width 1,.stop,.reranker 0,.topm 0,.context 0,.answer 0],(taskReward true (2/5) (1/2)) [.query 1,.hydeRetriever 1,.selection 0,.width 1,.stop,.reranker 0,.topm 0,.context 0,.answer 0],0,by decide⟩

def adverseCompleteEvent13 : TreeEvaluation Act :=
  ⟨[.query 1,.hydeRetriever 0,.selection 0],[.query 1,.hydeRetriever 0,.selection 0,.width 0,.stop,.reranker 0,.topm 0,.context 0,.answer 0],(taskReward true (2/5) (1/2)) [.query 1,.hydeRetriever 0,.selection 0,.width 0,.stop,.reranker 0,.topm 0,.context 0,.answer 0],0,by decide⟩

def adverseCompleteEvent14 : TreeEvaluation Act :=
  ⟨[.query 1,.hydeRetriever 2,.selection 0],[.query 1,.hydeRetriever 2,.selection 0,.width 0,.stop,.reranker 0,.topm 2,.context 0,.answer 2],(taskReward true (2/5) (1/2)) [.query 1,.hydeRetriever 2,.selection 0,.width 0,.stop,.reranker 0,.topm 2,.context 0,.answer 2],0,by decide⟩

def adverseCompleteEvent15 : TreeEvaluation Act :=
  ⟨[.query 1,.hydeRetriever 1,.selection 1],[.query 1,.hydeRetriever 1,.selection 1,.width 0,.stop,.reranker 0,.topm 0,.context 0,.answer 0],(taskReward true (2/5) (1/2)) [.query 1,.hydeRetriever 1,.selection 1,.width 0,.stop,.reranker 0,.topm 0,.context 0,.answer 0],0,by decide⟩

def adverseCompleteEvent16 : TreeEvaluation Act :=
  ⟨[.query 1,.hydeRetriever 0,.selection 1],[.query 1,.hydeRetriever 0,.selection 1,.width 0,.stop,.reranker 0,.topm 0,.context 0,.answer 0],(taskReward true (2/5) (1/2)) [.query 1,.hydeRetriever 0,.selection 1,.width 0,.stop,.reranker 0,.topm 0,.context 0,.answer 0],0,by decide⟩

def adverseCompleteEvent17 : TreeEvaluation Act :=
  ⟨[.query 1,.hydeRetriever 2,.selection 1],[.query 1,.hydeRetriever 2,.selection 1,.width 0,.stop,.reranker 0,.topm 0,.context 0,.answer 0],(taskReward true (2/5) (1/2)) [.query 1,.hydeRetriever 2,.selection 1,.width 0,.stop,.reranker 0,.topm 0,.context 0,.answer 0],0,by decide⟩

def adverseCompleteEvent18 : TreeEvaluation Act :=
  ⟨[.query 1,.hydeRetriever 1,.selection 2],[.query 1,.hydeRetriever 1,.selection 2,.width 0,.stop,.reranker 0,.topm 0,.context 0,.answer 0],(taskReward true (2/5) (1/2)) [.query 1,.hydeRetriever 1,.selection 2,.width 0,.stop,.reranker 0,.topm 0,.context 0,.answer 0],0,by decide⟩

def adverseCompleteEvent19 : TreeEvaluation Act :=
  ⟨[.query 1,.hydeRetriever 0,.selection 2],[.query 1,.hydeRetriever 0,.selection 2,.width 0,.stop,.reranker 0,.topm 0,.context 0,.answer 0],(taskReward true (2/5) (1/2)) [.query 1,.hydeRetriever 0,.selection 2,.width 0,.stop,.reranker 0,.topm 0,.context 0,.answer 0],0,by decide⟩

def adverseCompleteEvent20 : TreeEvaluation Act :=
  ⟨[.query 1,.hydeRetriever 2,.selection 2],[.query 1,.hydeRetriever 2,.selection 2,.width 0,.stop,.reranker 0,.topm 0,.context 0,.answer 0],(taskReward true (2/5) (1/2)) [.query 1,.hydeRetriever 2,.selection 2,.width 0,.stop,.reranker 0,.topm 0,.context 0,.answer 0],0,by decide⟩

def adverseCompleteEvent21 : TreeEvaluation Act :=
  ⟨[.query 1,.hydeRetriever 1,.selection 3],[.query 1,.hydeRetriever 1,.selection 3,.width 0,.stop,.reranker 0,.topm 0,.context 0,.answer 0],(taskReward true (2/5) (1/2)) [.query 1,.hydeRetriever 1,.selection 3,.width 0,.stop,.reranker 0,.topm 0,.context 0,.answer 0],0,by decide⟩

def adverseCompleteEvent22 : TreeEvaluation Act :=
  ⟨[.query 1,.hydeRetriever 0,.selection 3],[.query 1,.hydeRetriever 0,.selection 3,.width 0,.stop,.reranker 0,.topm 0,.context 0,.answer 0],(taskReward true (2/5) (1/2)) [.query 1,.hydeRetriever 0,.selection 3,.width 0,.stop,.reranker 0,.topm 0,.context 0,.answer 0],0,by decide⟩

def adverseCompleteEvent23 : TreeEvaluation Act :=
  ⟨[.query 1,.hydeRetriever 2,.selection 3],[.query 1,.hydeRetriever 2,.selection 3,.width 0,.stop,.reranker 0,.topm 0,.context 0,.answer 0],(taskReward true (2/5) (1/2)) [.query 1,.hydeRetriever 2,.selection 3,.width 0,.stop,.reranker 0,.topm 0,.context 0,.answer 0],0,by decide⟩

def adverseCompleteEvent24 : TreeEvaluation Act :=
  ⟨[.query 1,.hydeRetriever 1,.selection 1,.width 0],[.query 1,.hydeRetriever 1,.selection 1,.width 0,.stop,.reranker 0,.topm 0,.context 0,.answer 0],(taskReward true (2/5) (1/2)) [.query 1,.hydeRetriever 1,.selection 1,.width 0,.stop,.reranker 0,.topm 0,.context 0,.answer 0],0,by decide⟩

def adverseCompleteEvent25 : TreeEvaluation Act :=
  ⟨[.query 1,.hydeRetriever 0,.selection 1,.width 0],[.query 1,.hydeRetriever 0,.selection 1,.width 0,.stop,.reranker 0,.topm 0,.context 0,.answer 0],(taskReward true (2/5) (1/2)) [.query 1,.hydeRetriever 0,.selection 1,.width 0,.stop,.reranker 0,.topm 0,.context 0,.answer 0],0,by decide⟩

def adverseCompleteEvent26 : TreeEvaluation Act :=
  ⟨[.query 1,.hydeRetriever 2,.selection 1,.width 0],[.query 1,.hydeRetriever 2,.selection 1,.width 0,.stop,.reranker 0,.topm 0,.context 0,.answer 0],(taskReward true (2/5) (1/2)) [.query 1,.hydeRetriever 2,.selection 1,.width 0,.stop,.reranker 0,.topm 0,.context 0,.answer 0],0,by decide⟩

def adverseCompleteEvent27 : TreeEvaluation Act :=
  ⟨[.query 1,.hydeRetriever 1,.selection 2,.width 0],[.query 1,.hydeRetriever 1,.selection 2,.width 0,.stop,.reranker 0,.topm 0,.context 0,.answer 0],(taskReward true (2/5) (1/2)) [.query 1,.hydeRetriever 1,.selection 2,.width 0,.stop,.reranker 0,.topm 0,.context 0,.answer 0],0,by decide⟩

def adverseCompleteEvent28 : TreeEvaluation Act :=
  ⟨[.query 1,.hydeRetriever 0,.selection 2,.width 0],[.query 1,.hydeRetriever 0,.selection 2,.width 0,.stop,.reranker 0,.topm 0,.context 0,.answer 0],(taskReward true (2/5) (1/2)) [.query 1,.hydeRetriever 0,.selection 2,.width 0,.stop,.reranker 0,.topm 0,.context 0,.answer 0],0,by decide⟩

def adverseCompleteEvent29 : TreeEvaluation Act :=
  ⟨[.query 1,.hydeRetriever 2,.selection 2,.width 0],[.query 1,.hydeRetriever 2,.selection 2,.width 0,.stop,.reranker 0,.topm 0,.context 0,.answer 0],(taskReward true (2/5) (1/2)) [.query 1,.hydeRetriever 2,.selection 2,.width 0,.stop,.reranker 0,.topm 0,.context 0,.answer 0],0,by decide⟩

def adverseCompleteEvent30 : TreeEvaluation Act :=
  ⟨[.query 1,.hydeRetriever 1,.selection 3,.width 0],[.query 1,.hydeRetriever 1,.selection 3,.width 0,.stop,.reranker 0,.topm 0,.context 0,.answer 0],(taskReward true (2/5) (1/2)) [.query 1,.hydeRetriever 1,.selection 3,.width 0,.stop,.reranker 0,.topm 0,.context 0,.answer 0],0,by decide⟩

def adverseCompleteEvent31 : TreeEvaluation Act :=
  ⟨[.query 1,.hydeRetriever 0,.selection 3,.width 0],[.query 1,.hydeRetriever 0,.selection 3,.width 0,.stop,.reranker 0,.topm 0,.context 0,.answer 0],(taskReward true (2/5) (1/2)) [.query 1,.hydeRetriever 0,.selection 3,.width 0,.stop,.reranker 0,.topm 0,.context 0,.answer 0],0,by decide⟩

def adverseCompleteEvent32 : TreeEvaluation Act :=
  ⟨[.query 1,.hydeRetriever 2,.selection 3,.width 0],[.query 1,.hydeRetriever 2,.selection 3,.width 0,.stop,.reranker 0,.topm 0,.context 0,.answer 0],(taskReward true (2/5) (1/2)) [.query 1,.hydeRetriever 2,.selection 3,.width 0,.stop,.reranker 0,.topm 0,.context 0,.answer 0],0,by decide⟩

def adverseCompleteEvent33 : TreeEvaluation Act :=
  ⟨[.query 1,.hydeRetriever 1,.selection 0,.width 1],[.query 1,.hydeRetriever 1,.selection 0,.width 1,.stop,.reranker 0,.topm 0,.context 0,.answer 0],(taskReward true (2/5) (1/2)) [.query 1,.hydeRetriever 1,.selection 0,.width 1,.stop,.reranker 0,.topm 0,.context 0,.answer 0],0,by decide⟩

def adverseCompleteEvent34 : TreeEvaluation Act :=
  ⟨[.query 1,.hydeRetriever 0,.selection 0,.width 0],[.query 1,.hydeRetriever 0,.selection 0,.width 0,.stop,.reranker 0,.topm 0,.context 0,.answer 0],(taskReward true (2/5) (1/2)) [.query 1,.hydeRetriever 0,.selection 0,.width 0,.stop,.reranker 0,.topm 0,.context 0,.answer 0],0,by decide⟩

def adverseCompleteEvent35 : TreeEvaluation Act :=
  ⟨[.query 1,.hydeRetriever 2,.selection 0,.width 0],[.query 1,.hydeRetriever 2,.selection 0,.width 0,.stop,.reranker 0,.topm 2,.context 0,.answer 2],(taskReward true (2/5) (1/2)) [.query 1,.hydeRetriever 2,.selection 0,.width 0,.stop,.reranker 0,.topm 2,.context 0,.answer 2],0,by decide⟩

def adverseCompleteEvent36 : TreeEvaluation Act :=
  ⟨[.query 1,.hydeRetriever 1,.selection 1,.width 3],[.query 1,.hydeRetriever 1,.selection 1,.width 3,.stop,.reranker 0,.topm 0,.context 0,.answer 0],(taskReward true (2/5) (1/2)) [.query 1,.hydeRetriever 1,.selection 1,.width 3,.stop,.reranker 0,.topm 0,.context 0,.answer 0],0,by decide⟩

def adverseCompleteEvent37 : TreeEvaluation Act :=
  ⟨[.query 1,.hydeRetriever 0,.selection 1,.width 3],[.query 1,.hydeRetriever 0,.selection 1,.width 3,.stop,.reranker 0,.topm 0,.context 0,.answer 0],(taskReward true (2/5) (1/2)) [.query 1,.hydeRetriever 0,.selection 1,.width 3,.stop,.reranker 0,.topm 0,.context 0,.answer 0],0,by decide⟩

def adverseCompleteEvent38 : TreeEvaluation Act :=
  ⟨[.query 1,.hydeRetriever 2,.selection 1,.width 3],[.query 1,.hydeRetriever 2,.selection 1,.width 3,.stop,.reranker 0,.topm 0,.context 0,.answer 0],(taskReward true (2/5) (1/2)) [.query 1,.hydeRetriever 2,.selection 1,.width 3,.stop,.reranker 0,.topm 0,.context 0,.answer 0],0,by decide⟩

def adverseCompleteEvent39 : TreeEvaluation Act :=
  ⟨[.query 1,.hydeRetriever 1,.selection 2,.width 3],[.query 1,.hydeRetriever 1,.selection 2,.width 3,.stop,.reranker 0,.topm 0,.context 0,.answer 0],(taskReward true (2/5) (1/2)) [.query 1,.hydeRetriever 1,.selection 2,.width 3,.stop,.reranker 0,.topm 0,.context 0,.answer 0],0,by decide⟩

def adverseCompleteEvent40 : TreeEvaluation Act :=
  ⟨[.query 1,.hydeRetriever 0,.selection 2,.width 3],[.query 1,.hydeRetriever 0,.selection 2,.width 3,.stop,.reranker 0,.topm 0,.context 0,.answer 0],(taskReward true (2/5) (1/2)) [.query 1,.hydeRetriever 0,.selection 2,.width 3,.stop,.reranker 0,.topm 0,.context 0,.answer 0],0,by decide⟩

def adverseCompleteEvent41 : TreeEvaluation Act :=
  ⟨[.query 1,.hydeRetriever 2,.selection 2,.width 3],[.query 1,.hydeRetriever 2,.selection 2,.width 3,.stop,.reranker 0,.topm 0,.context 0,.answer 0],(taskReward true (2/5) (1/2)) [.query 1,.hydeRetriever 2,.selection 2,.width 3,.stop,.reranker 0,.topm 0,.context 0,.answer 0],0,by decide⟩

def adverseCompleteEvent42 : TreeEvaluation Act :=
  ⟨[.query 1,.hydeRetriever 1,.selection 3,.width 3],[.query 1,.hydeRetriever 1,.selection 3,.width 3,.stop,.reranker 0,.topm 0,.context 0,.answer 0],(taskReward true (2/5) (1/2)) [.query 1,.hydeRetriever 1,.selection 3,.width 3,.stop,.reranker 0,.topm 0,.context 0,.answer 0],0,by decide⟩

def adverseCompleteEvent43 : TreeEvaluation Act :=
  ⟨[.query 1,.hydeRetriever 0,.selection 3,.width 3],[.query 1,.hydeRetriever 0,.selection 3,.width 3,.stop,.reranker 0,.topm 0,.context 0,.answer 0],(taskReward true (2/5) (1/2)) [.query 1,.hydeRetriever 0,.selection 3,.width 3,.stop,.reranker 0,.topm 0,.context 0,.answer 0],0,by decide⟩

def adverseCompleteEvent44 : TreeEvaluation Act :=
  ⟨[.query 1,.hydeRetriever 2,.selection 3,.width 3],[.query 1,.hydeRetriever 2,.selection 3,.width 3,.stop,.reranker 0,.topm 0,.context 0,.answer 0],(taskReward true (2/5) (1/2)) [.query 1,.hydeRetriever 2,.selection 3,.width 3,.stop,.reranker 0,.topm 0,.context 0,.answer 0],0,by decide⟩

def adverseCompleteEvent45 : TreeEvaluation Act :=
  ⟨[.query 1,.hydeRetriever 1,.selection 0,.width 3],[.query 1,.hydeRetriever 1,.selection 0,.width 3,.stop,.reranker 0,.topm 0,.context 0,.answer 0],(taskReward true (2/5) (1/2)) [.query 1,.hydeRetriever 1,.selection 0,.width 3,.stop,.reranker 0,.topm 0,.context 0,.answer 0],0,by decide⟩

def adverseCompleteProposal : List (TreeEvaluation Act) :=
  [adverseCompleteEvent1,adverseCompleteEvent2,adverseCompleteEvent3,adverseCompleteEvent4,adverseCompleteEvent5,adverseCompleteEvent6,adverseCompleteEvent7,adverseCompleteEvent8,adverseCompleteEvent9,adverseCompleteEvent10,adverseCompleteEvent11,adverseCompleteEvent12,adverseCompleteEvent13,adverseCompleteEvent14,adverseCompleteEvent15,adverseCompleteEvent16,adverseCompleteEvent17,adverseCompleteEvent18,adverseCompleteEvent19,adverseCompleteEvent20,adverseCompleteEvent21,adverseCompleteEvent22,adverseCompleteEvent23,adverseCompleteEvent24,adverseCompleteEvent25,adverseCompleteEvent26,adverseCompleteEvent27,adverseCompleteEvent28,adverseCompleteEvent29,adverseCompleteEvent30,adverseCompleteEvent31,adverseCompleteEvent32,adverseCompleteEvent33,adverseCompleteEvent34,adverseCompleteEvent35,adverseCompleteEvent36,adverseCompleteEvent37,adverseCompleteEvent38,adverseCompleteEvent39,adverseCompleteEvent40,adverseCompleteEvent41,adverseCompleteEvent42,adverseCompleteEvent43,adverseCompleteEvent44,adverseCompleteEvent45]

def adverseNextEvent1 : TreeEvaluation Act :=
  ⟨[.query 0],[.query 0,.normalRetriever 0,.selection 0,.width 0,.stop,.reranker 0,.topm 0,.context 0,.answer 0],(taskReward true (2/5) (1/2)) [.query 0,.normalRetriever 0,.selection 0,.width 0,.stop,.reranker 0,.topm 0,.context 0,.answer 0],0,by decide⟩

def adverseNextEvent2 : TreeEvaluation Act :=
  ⟨[.query 1],[.query 1,.hydeRetriever 0,.selection 0,.width 0,.stop,.reranker 0,.topm 0,.context 0,.answer 0],(taskReward true (2/5) (1/2)) [.query 1,.hydeRetriever 0,.selection 0,.width 0,.stop,.reranker 0,.topm 0,.context 0,.answer 0],0,by decide⟩

def adverseNextEvent3 : TreeEvaluation Act :=
  ⟨[.query 2],[.query 2,.normalRetriever 0,.selection 0,.width 0,.stop,.reranker 0,.topm 0,.context 0,.answer 0],(taskReward true (2/5) (1/2)) [.query 2,.normalRetriever 0,.selection 0,.width 0,.stop,.reranker 0,.topm 0,.context 0,.answer 0],0,by decide⟩

def adverseNextEvent4 : TreeEvaluation Act :=
  ⟨[.query 3],[.query 3,.normalRetriever 0,.selection 0,.width 0,.stop,.reranker 0,.topm 0,.context 0,.answer 0],(taskReward true (2/5) (1/2)) [.query 3,.normalRetriever 0,.selection 0,.width 0,.stop,.reranker 0,.topm 0,.context 0,.answer 0],0,by decide⟩

def adverseNextEvent5 : TreeEvaluation Act :=
  ⟨[.query 4],[.query 4,.normalRetriever 0,.selection 0,.width 0,.stop,.reranker 0,.topm 0,.context 0,.answer 0],(taskReward true (2/5) (1/2)) [.query 4,.normalRetriever 0,.selection 0,.width 0,.stop,.reranker 0,.topm 0,.context 0,.answer 0],0,by decide⟩

def adverseNextEvent6 : TreeEvaluation Act :=
  ⟨[.query 5],[.query 5,.normalRetriever 0,.selection 0,.width 0,.stop,.reranker 0,.topm 0,.context 0,.answer 0],(taskReward true (2/5) (1/2)) [.query 5,.normalRetriever 0,.selection 0,.width 0,.stop,.reranker 0,.topm 0,.context 0,.answer 0],0,by decide⟩

def adverseNextEvent7 : TreeEvaluation Act :=
  ⟨[.query 6],[.query 6,.normalRetriever 0,.selection 0,.width 0,.stop,.reranker 0,.topm 0,.context 0,.answer 0],(taskReward true (2/5) (1/2)) [.query 6,.normalRetriever 0,.selection 0,.width 0,.stop,.reranker 0,.topm 0,.context 0,.answer 0],0,by decide⟩

def adverseNextEvent8 : TreeEvaluation Act :=
  ⟨[.query 7],[.query 7,.normalRetriever 0,.selection 0,.width 0,.stop,.reranker 0,.topm 0,.context 0,.answer 0],(taskReward true (2/5) (1/2)) [.query 7,.normalRetriever 0,.selection 0,.width 0,.stop,.reranker 0,.topm 0,.context 0,.answer 0],0,by decide⟩

def adverseNextEvent9 : TreeEvaluation Act :=
  ⟨[.query 5,.normalRetriever 1],[.query 5,.normalRetriever 1,.selection 0,.width 1,.stop,.reranker 0,.topm 0,.context 0,.answer 0],(taskReward true (2/5) (1/2)) [.query 5,.normalRetriever 1,.selection 0,.width 1,.stop,.reranker 0,.topm 0,.context 0,.answer 0],0,by decide⟩

def adverseNextEvent10 : TreeEvaluation Act :=
  ⟨[.query 1,.hydeRetriever 1],[.query 1,.hydeRetriever 1,.selection 0,.width 1,.stop,.reranker 0,.topm 0,.context 0,.answer 0],(taskReward true (2/5) (1/2)) [.query 1,.hydeRetriever 1,.selection 0,.width 1,.stop,.reranker 0,.topm 0,.context 0,.answer 0],0,by decide⟩

def adverseNextEvent11 : TreeEvaluation Act :=
  ⟨[.query 0,.normalRetriever 0],[.query 0,.normalRetriever 0,.selection 0,.width 0,.stop,.reranker 0,.topm 0,.context 0,.answer 0],(taskReward true (2/5) (1/2)) [.query 0,.normalRetriever 0,.selection 0,.width 0,.stop,.reranker 0,.topm 0,.context 0,.answer 0],0,by decide⟩

def adverseNextEvent12 : TreeEvaluation Act :=
  ⟨[.query 2,.normalRetriever 0],[.query 2,.normalRetriever 0,.selection 0,.width 0,.stop,.reranker 0,.topm 0,.context 0,.answer 0],(taskReward true (2/5) (1/2)) [.query 2,.normalRetriever 0,.selection 0,.width 0,.stop,.reranker 0,.topm 0,.context 0,.answer 0],0,by decide⟩

def adverseNextEvent13 : TreeEvaluation Act :=
  ⟨[.query 3,.normalRetriever 0],[.query 3,.normalRetriever 0,.selection 0,.width 0,.stop,.reranker 0,.topm 0,.context 0,.answer 0],(taskReward true (2/5) (1/2)) [.query 3,.normalRetriever 0,.selection 0,.width 0,.stop,.reranker 0,.topm 0,.context 0,.answer 0],0,by decide⟩

def adverseNextEvent14 : TreeEvaluation Act :=
  ⟨[.query 4,.normalRetriever 0],[.query 4,.normalRetriever 0,.selection 0,.width 0,.stop,.reranker 0,.topm 0,.context 0,.answer 0],(taskReward true (2/5) (1/2)) [.query 4,.normalRetriever 0,.selection 0,.width 0,.stop,.reranker 0,.topm 0,.context 0,.answer 0],0,by decide⟩

def adverseNextEvent15 : TreeEvaluation Act :=
  ⟨[.query 6,.normalRetriever 0],[.query 6,.normalRetriever 0,.selection 0,.width 0,.stop,.reranker 0,.topm 0,.context 0,.answer 0],(taskReward true (2/5) (1/2)) [.query 6,.normalRetriever 0,.selection 0,.width 0,.stop,.reranker 0,.topm 0,.context 0,.answer 0],0,by decide⟩

def adverseNextEvent16 : TreeEvaluation Act :=
  ⟨[.query 7,.normalRetriever 0],[.query 7,.normalRetriever 0,.selection 0,.width 0,.stop,.reranker 0,.topm 0,.context 0,.answer 0],(taskReward true (2/5) (1/2)) [.query 7,.normalRetriever 0,.selection 0,.width 0,.stop,.reranker 0,.topm 0,.context 0,.answer 0],0,by decide⟩

def adverseNextEvent17 : TreeEvaluation Act :=
  ⟨[.query 5,.normalRetriever 0],[.query 5,.normalRetriever 0,.selection 0,.width 0,.stop,.reranker 0,.topm 0,.context 0,.answer 0],(taskReward true (2/5) (1/2)) [.query 5,.normalRetriever 0,.selection 0,.width 0,.stop,.reranker 0,.topm 0,.context 0,.answer 0],0,by decide⟩

def adverseNextEvent18 : TreeEvaluation Act :=
  ⟨[.query 1,.hydeRetriever 0],[.query 1,.hydeRetriever 0,.selection 0,.width 0,.stop,.reranker 0,.topm 0,.context 0,.answer 0],(taskReward true (2/5) (1/2)) [.query 1,.hydeRetriever 0,.selection 0,.width 0,.stop,.reranker 0,.topm 0,.context 0,.answer 0],0,by decide⟩

def adverseNextEvent19 : TreeEvaluation Act :=
  ⟨[.query 5,.normalRetriever 4],[.query 5,.normalRetriever 4,.selection 0,.width 0,.stop,.reranker 0,.topm 0,.context 0,.answer 0],(taskReward true (2/5) (1/2)) [.query 5,.normalRetriever 4,.selection 0,.width 0,.stop,.reranker 0,.topm 0,.context 0,.answer 0],0,by decide⟩

def adverseNextEvent20 : TreeEvaluation Act :=
  ⟨[.query 0,.normalRetriever 4],[.query 0,.normalRetriever 4,.selection 0,.width 0,.stop,.reranker 0,.topm 0,.context 0,.answer 0],(taskReward true (2/5) (1/2)) [.query 0,.normalRetriever 4,.selection 0,.width 0,.stop,.reranker 0,.topm 0,.context 0,.answer 0],0,by decide⟩

def adverseNextEvent21 : TreeEvaluation Act :=
  ⟨[.query 2,.normalRetriever 4],[.query 2,.normalRetriever 4,.selection 0,.width 0,.stop,.reranker 0,.topm 0,.context 0,.answer 0],(taskReward true (2/5) (1/2)) [.query 2,.normalRetriever 4,.selection 0,.width 0,.stop,.reranker 0,.topm 0,.context 0,.answer 0],0,by decide⟩

def adverseNextEvent22 : TreeEvaluation Act :=
  ⟨[.query 3,.normalRetriever 4],[.query 3,.normalRetriever 4,.selection 0,.width 0,.stop,.reranker 0,.topm 0,.context 0,.answer 0],(taskReward true (2/5) (1/2)) [.query 3,.normalRetriever 4,.selection 0,.width 0,.stop,.reranker 0,.topm 0,.context 0,.answer 0],0,by decide⟩

def adverseNextEvent23 : TreeEvaluation Act :=
  ⟨[.query 4,.normalRetriever 4],[.query 4,.normalRetriever 4,.selection 0,.width 0,.stop,.reranker 0,.topm 0,.context 0,.answer 0],(taskReward true (2/5) (1/2)) [.query 4,.normalRetriever 4,.selection 0,.width 0,.stop,.reranker 0,.topm 0,.context 0,.answer 0],0,by decide⟩

def adverseNextEvent24 : TreeEvaluation Act :=
  ⟨[.query 6,.normalRetriever 4],[.query 6,.normalRetriever 4,.selection 0,.width 0,.stop,.reranker 0,.topm 0,.context 0,.answer 0],(taskReward true (2/5) (1/2)) [.query 6,.normalRetriever 4,.selection 0,.width 0,.stop,.reranker 0,.topm 0,.context 0,.answer 0],0,by decide⟩

def adverseNextEvent25 : TreeEvaluation Act :=
  ⟨[.query 7,.normalRetriever 4],[.query 7,.normalRetriever 4,.selection 0,.width 0,.stop,.reranker 0,.topm 0,.context 0,.answer 0],(taskReward true (2/5) (1/2)) [.query 7,.normalRetriever 4,.selection 0,.width 0,.stop,.reranker 0,.topm 0,.context 0,.answer 0],0,by decide⟩

def adverseNextEvent26 : TreeEvaluation Act :=
  ⟨[.query 1,.hydeRetriever 2],[.query 1,.hydeRetriever 2,.selection 0,.width 0,.stop,.reranker 0,.topm 2,.context 0,.answer 2],(taskReward true (2/5) (1/2)) [.query 1,.hydeRetriever 2,.selection 0,.width 0,.stop,.reranker 0,.topm 2,.context 0,.answer 2],0,by decide⟩

def adverseNextEvent27 : TreeEvaluation Act :=
  ⟨[.query 5,.normalRetriever 6],[.query 5,.normalRetriever 6,.selection 0,.width 0,.stop,.reranker 0,.topm 0,.context 0,.answer 0],(taskReward true (2/5) (1/2)) [.query 5,.normalRetriever 6,.selection 0,.width 0,.stop,.reranker 0,.topm 0,.context 0,.answer 0],0,by decide⟩

def adverseNextEvent28 : TreeEvaluation Act :=
  ⟨[.query 1,.hydeRetriever 1,.selection 0],[.query 1,.hydeRetriever 1,.selection 0,.width 1,.stop,.reranker 0,.topm 0,.context 0,.answer 0],(taskReward true (2/5) (1/2)) [.query 1,.hydeRetriever 1,.selection 0,.width 1,.stop,.reranker 0,.topm 0,.context 0,.answer 0],0,by decide⟩

def adverseNextEvent29 : TreeEvaluation Act :=
  ⟨[.query 0,.normalRetriever 6],[.query 0,.normalRetriever 6,.selection 0,.width 0,.stop,.reranker 0,.topm 0,.context 0,.answer 0],(taskReward true (2/5) (1/2)) [.query 0,.normalRetriever 6,.selection 0,.width 0,.stop,.reranker 0,.topm 0,.context 0,.answer 0],0,by decide⟩

def adverseNextEvent30 : TreeEvaluation Act :=
  ⟨[.query 2,.normalRetriever 6],[.query 2,.normalRetriever 6,.selection 0,.width 0,.stop,.reranker 0,.topm 0,.context 0,.answer 0],(taskReward true (2/5) (1/2)) [.query 2,.normalRetriever 6,.selection 0,.width 0,.stop,.reranker 0,.topm 0,.context 0,.answer 0],0,by decide⟩

def adverseNextEvent31 : TreeEvaluation Act :=
  ⟨[.query 3,.normalRetriever 6],[.query 3,.normalRetriever 6,.selection 0,.width 0,.stop,.reranker 0,.topm 0,.context 0,.answer 0],(taskReward true (2/5) (1/2)) [.query 3,.normalRetriever 6,.selection 0,.width 0,.stop,.reranker 0,.topm 0,.context 0,.answer 0],0,by decide⟩

def adverseNextEvent32 : TreeEvaluation Act :=
  ⟨[.query 4,.normalRetriever 6],[.query 4,.normalRetriever 6,.selection 0,.width 0,.stop,.reranker 0,.topm 0,.context 0,.answer 0],(taskReward true (2/5) (1/2)) [.query 4,.normalRetriever 6,.selection 0,.width 0,.stop,.reranker 0,.topm 0,.context 0,.answer 0],0,by decide⟩

def adverseNextEvent33 : TreeEvaluation Act :=
  ⟨[.query 6,.normalRetriever 6],[.query 6,.normalRetriever 6,.selection 0,.width 0,.stop,.reranker 0,.topm 0,.context 0,.answer 0],(taskReward true (2/5) (1/2)) [.query 6,.normalRetriever 6,.selection 0,.width 0,.stop,.reranker 0,.topm 0,.context 0,.answer 0],0,by decide⟩

def adverseNextEvent34 : TreeEvaluation Act :=
  ⟨[.query 7,.normalRetriever 6],[.query 7,.normalRetriever 6,.selection 0,.width 0,.stop,.reranker 0,.topm 0,.context 0,.answer 0],(taskReward true (2/5) (1/2)) [.query 7,.normalRetriever 6,.selection 0,.width 0,.stop,.reranker 0,.topm 0,.context 0,.answer 0],0,by decide⟩

def adverseNextEvent35 : TreeEvaluation Act :=
  ⟨[.query 1,.hydeRetriever 0,.selection 0],[.query 1,.hydeRetriever 0,.selection 0,.width 0,.stop,.reranker 0,.topm 0,.context 0,.answer 0],(taskReward true (2/5) (1/2)) [.query 1,.hydeRetriever 0,.selection 0,.width 0,.stop,.reranker 0,.topm 0,.context 0,.answer 0],0,by decide⟩

def adverseNextEvent36 : TreeEvaluation Act :=
  ⟨[.query 5,.normalRetriever 7],[.query 5,.normalRetriever 7,.selection 0,.width 0,.stop,.reranker 0,.topm 0,.context 0,.answer 0],(taskReward true (2/5) (1/2)) [.query 5,.normalRetriever 7,.selection 0,.width 0,.stop,.reranker 0,.topm 0,.context 0,.answer 0],0,by decide⟩

def adverseNextProposal : List (TreeEvaluation Act) :=
  [adverseNextEvent1,adverseNextEvent2,adverseNextEvent3,adverseNextEvent4,adverseNextEvent5,adverseNextEvent6,adverseNextEvent7,adverseNextEvent8,adverseNextEvent9,adverseNextEvent10,adverseNextEvent11,adverseNextEvent12,adverseNextEvent13,adverseNextEvent14,adverseNextEvent15,adverseNextEvent16,adverseNextEvent17,adverseNextEvent18,adverseNextEvent19,adverseNextEvent20,adverseNextEvent21,adverseNextEvent22,adverseNextEvent23,adverseNextEvent24,adverseNextEvent25,adverseNextEvent26,adverseNextEvent27,adverseNextEvent28,adverseNextEvent29,adverseNextEvent30,adverseNextEvent31,adverseNextEvent32,adverseNextEvent33,adverseNextEvent34,adverseNextEvent35,adverseNextEvent36]

end AgentUCT32MConcrete
