import GenericCompleteRoot
set_option autoImplicit false
set_option maxRecDepth 16384
set_option maxHeartbeats 16000000
noncomputable section
namespace AgentUCT32MConcrete
open AgentUCTPaper AgentUCTNativeBudget

theorem favorableComplete_proposal_rewards (e : TreeEvaluation AgentUCTNativeRefinement.Act) (he : e ∈ favorableCompleteProposal) :
    0 ≤ e.reward ∧ e.reward ≤ 1 := by
  simp only [favorableCompleteProposal,List.mem_cons,List.not_mem_nil,or_false] at he
  rcases he with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> simp only [favorableCompleteEvent1,favorableCompleteEvent2,favorableCompleteEvent3,favorableCompleteEvent4,favorableCompleteEvent5,favorableCompleteEvent6,favorableCompleteEvent7,favorableCompleteEvent8,favorableCompleteEvent9,favorableCompleteEvent10,favorableCompleteEvent11,favorableCompleteEvent12,favorableCompleteEvent13,favorableCompleteEvent14,favorableCompleteEvent15,favorableCompleteEvent16,favorableCompleteEvent17,favorableCompleteEvent18,favorableCompleteEvent19,favorableCompleteEvent20,favorableCompleteEvent21,favorableCompleteEvent22,favorableCompleteEvent23,favorableCompleteEvent24,favorableCompleteEvent25,favorableCompleteEvent26,favorableCompleteEvent27,favorableCompleteEvent28,favorableCompleteEvent29,favorableCompleteEvent30,favorableCompleteEvent31,favorableCompleteEvent32,favorableCompleteEvent33,favorableCompleteEvent34,favorableCompleteEvent35,favorableCompleteEvent36,favorableCompleteEvent37,favorableCompleteEvent38,favorableCompleteEvent39,favorableCompleteEvent40,favorableCompleteEvent41,favorableCompleteEvent42,favorableCompleteEvent43,favorableCompleteEvent44] <;> apply task_reward_in_unit

theorem favorableComplete_prefix_rewards (k : ℕ) (e : TreeEvaluation AgentUCTNativeRefinement.Act)
    (he : e ∈ favorableCompleteProposal.take k) : 0 ≤ e.reward ∧ e.reward ≤ 1 :=
  favorableComplete_proposal_rewards e (List.mem_of_mem_take he)

theorem favorableNext_proposal_rewards (e : TreeEvaluation AgentUCTNativeRefinement.Act) (he : e ∈ favorableNextProposal) :
    0 ≤ e.reward ∧ e.reward ≤ 1 := by
  simp only [favorableNextProposal,List.mem_cons,List.not_mem_nil,or_false] at he
  rcases he with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> simp only [favorableNextEvent1,favorableNextEvent2,favorableNextEvent3,favorableNextEvent4,favorableNextEvent5,favorableNextEvent6,favorableNextEvent7,favorableNextEvent8,favorableNextEvent9,favorableNextEvent10,favorableNextEvent11,favorableNextEvent12,favorableNextEvent13,favorableNextEvent14,favorableNextEvent15,favorableNextEvent16,favorableNextEvent17,favorableNextEvent18,favorableNextEvent19,favorableNextEvent20,favorableNextEvent21,favorableNextEvent22,favorableNextEvent23,favorableNextEvent24,favorableNextEvent25,favorableNextEvent26,favorableNextEvent27,favorableNextEvent28,favorableNextEvent29,favorableNextEvent30,favorableNextEvent31,favorableNextEvent32,favorableNextEvent33,favorableNextEvent34,favorableNextEvent35,favorableNextEvent36,favorableNextEvent37] <;> apply task_reward_in_unit

theorem favorableNext_prefix_rewards (k : ℕ) (e : TreeEvaluation AgentUCTNativeRefinement.Act)
    (he : e ∈ favorableNextProposal.take k) : 0 ≤ e.reward ∧ e.reward ≤ 1 :=
  favorableNext_proposal_rewards e (List.mem_of_mem_take he)

theorem adverseComplete_proposal_rewards (e : TreeEvaluation AgentUCTNativeRefinement.Act) (he : e ∈ adverseCompleteProposal) :
    0 ≤ e.reward ∧ e.reward ≤ 1 := by
  simp only [adverseCompleteProposal,List.mem_cons,List.not_mem_nil,or_false] at he
  rcases he with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> simp only [adverseCompleteEvent1,adverseCompleteEvent2,adverseCompleteEvent3,adverseCompleteEvent4,adverseCompleteEvent5,adverseCompleteEvent6,adverseCompleteEvent7,adverseCompleteEvent8,adverseCompleteEvent9,adverseCompleteEvent10,adverseCompleteEvent11,adverseCompleteEvent12,adverseCompleteEvent13,adverseCompleteEvent14,adverseCompleteEvent15,adverseCompleteEvent16,adverseCompleteEvent17,adverseCompleteEvent18,adverseCompleteEvent19,adverseCompleteEvent20,adverseCompleteEvent21,adverseCompleteEvent22,adverseCompleteEvent23,adverseCompleteEvent24,adverseCompleteEvent25,adverseCompleteEvent26,adverseCompleteEvent27,adverseCompleteEvent28,adverseCompleteEvent29,adverseCompleteEvent30,adverseCompleteEvent31,adverseCompleteEvent32,adverseCompleteEvent33,adverseCompleteEvent34,adverseCompleteEvent35,adverseCompleteEvent36,adverseCompleteEvent37,adverseCompleteEvent38,adverseCompleteEvent39,adverseCompleteEvent40,adverseCompleteEvent41,adverseCompleteEvent42,adverseCompleteEvent43,adverseCompleteEvent44,adverseCompleteEvent45] <;> apply task_reward_in_unit

theorem adverseComplete_prefix_rewards (k : ℕ) (e : TreeEvaluation AgentUCTNativeRefinement.Act)
    (he : e ∈ adverseCompleteProposal.take k) : 0 ≤ e.reward ∧ e.reward ≤ 1 :=
  adverseComplete_proposal_rewards e (List.mem_of_mem_take he)

theorem adverseNext_proposal_rewards (e : TreeEvaluation AgentUCTNativeRefinement.Act) (he : e ∈ adverseNextProposal) :
    0 ≤ e.reward ∧ e.reward ≤ 1 := by
  simp only [adverseNextProposal,List.mem_cons,List.not_mem_nil,or_false] at he
  rcases he with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> simp only [adverseNextEvent1,adverseNextEvent2,adverseNextEvent3,adverseNextEvent4,adverseNextEvent5,adverseNextEvent6,adverseNextEvent7,adverseNextEvent8,adverseNextEvent9,adverseNextEvent10,adverseNextEvent11,adverseNextEvent12,adverseNextEvent13,adverseNextEvent14,adverseNextEvent15,adverseNextEvent16,adverseNextEvent17,adverseNextEvent18,adverseNextEvent19,adverseNextEvent20,adverseNextEvent21,adverseNextEvent22,adverseNextEvent23,adverseNextEvent24,adverseNextEvent25,adverseNextEvent26,adverseNextEvent27,adverseNextEvent28,adverseNextEvent29,adverseNextEvent30,adverseNextEvent31,adverseNextEvent32,adverseNextEvent33,adverseNextEvent34,adverseNextEvent35,adverseNextEvent36] <;> apply task_reward_in_unit

theorem adverseNext_prefix_rewards (k : ℕ) (e : TreeEvaluation AgentUCTNativeRefinement.Act)
    (he : e ∈ adverseNextProposal.take k) : 0 ≤ e.reward ∧ e.reward ≤ 1 :=
  adverseNext_proposal_rewards e (List.mem_of_mem_take he)

end AgentUCT32MConcrete
