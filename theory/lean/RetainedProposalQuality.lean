import NextNormalQuote
set_option autoImplicit false
set_option maxRecDepth 16384
set_option maxHeartbeats 16000000
noncomputable section
namespace AgentUCTNextExact
open AgentUCT32MConcrete AgentUCT32MContinuation AgentUCTSavedBudget AgentUCTObservability
  AgentUCTPhysicalDiagnostic AgentUCTNativeBudget AgentUCTPanelAllocation
  AgentUCTNativeRepair AgentUCTNativeRefinement AgentUCTPaper



theorem adverse_global_quality_upper (path : List Act) : taskReward true (2/5) (1/2) path ≤ (1/2:ℝ) := by
  unfold taskReward
  split_ifs <;> norm_num

theorem favorableComplete_proposal_reward_rule (event : TreeEvaluation Act) (h : event ∈ favorableCompleteProposal) :
    event.reward = taskReward false (2/5) (1/2) event.terminal := by
  simp only [favorableCompleteProposal,List.mem_cons,List.not_mem_nil,or_false] at h
  rcases h with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> rfl

theorem favorableComplete_retained_proposal_quality :
    completedValue (favorableCompleteProposal.take 43) = (1/2:ℝ) := by
  apply completed_value_from_witness
  · intro event h
    exact by
      rw [favorableComplete_proposal_reward_rule event (List.mem_of_mem_take h)]
      exact favorable_global_quality_upper _
  · refine ⟨favorableCompleteEvent9,?_,?_⟩
    · simp only [favorableCompleteProposal]
      simp
    · norm_num [favorableCompleteEvent9,taskReward,aCold,bCold,seedPath,seedRetriever,leaf,fullLeaf,hyde,branchB] <;> simp +decide

theorem favorableNext_proposal_reward_rule (event : TreeEvaluation Act) (h : event ∈ favorableNextProposal) :
    event.reward = taskReward false (2/5) (1/2) event.terminal := by
  simp only [favorableNextProposal,List.mem_cons,List.not_mem_nil,or_false] at h
  rcases h with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> rfl

theorem favorableNext_retained_proposal_quality :
    completedValue (favorableNextProposal.take 36) = (1/2:ℝ) := by
  apply completed_value_from_witness
  · intro event h
    exact by
      rw [favorableNext_proposal_reward_rule event (List.mem_of_mem_take h)]
      exact favorable_global_quality_upper _
  · refine ⟨favorableNextEvent10,?_,?_⟩
    · simp only [favorableNextProposal]
      simp
    · norm_num [favorableNextEvent10,taskReward,aCold,bCold,seedPath,seedRetriever,leaf,fullLeaf,hyde,branchB] <;> simp +decide

theorem adverseComplete_proposal_reward_rule (event : TreeEvaluation Act) (h : event ∈ adverseCompleteProposal) :
    event.reward = taskReward true (2/5) (1/2) event.terminal := by
  simp only [adverseCompleteProposal,List.mem_cons,List.not_mem_nil,or_false] at h
  rcases h with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> rfl

theorem adverseComplete_proposal_no_bCold :
    ∀ event ∈ adverseCompleteProposal, event.terminal ≠ bCold := by decide +kernel

theorem adverseComplete_proposal_quality_at_most_delta (event : TreeEvaluation Act) (h : event ∈ adverseCompleteProposal) :
    event.reward ≤ (2/5:ℝ) := by
  rw [adverseComplete_proposal_reward_rule event h]
  have hb := adverseComplete_proposal_no_bCold event h
  unfold taskReward
  split_ifs <;> norm_num <;> contradiction

theorem adverseComplete_retained_proposal_quality :
    completedValue (adverseCompleteProposal.take 44) = (2/5:ℝ) := by
  apply completed_value_from_witness
  · intro event h
    exact adverseComplete_proposal_quality_at_most_delta event (List.mem_of_mem_take h)
  · refine ⟨adverseCompleteEvent6,?_,?_⟩
    · simp only [adverseCompleteProposal]
      simp
    · norm_num [adverseCompleteEvent6,taskReward,aCold,bCold,seedPath,seedRetriever,leaf,fullLeaf,hyde,branchB] <;> simp +decide

theorem adverseNext_proposal_reward_rule (event : TreeEvaluation Act) (h : event ∈ adverseNextProposal) :
    event.reward = taskReward true (2/5) (1/2) event.terminal := by
  simp only [adverseNextProposal,List.mem_cons,List.not_mem_nil,or_false] at h
  rcases h with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> rfl

theorem adverseNext_retained_proposal_quality :
    completedValue (adverseNextProposal.take 35) = (1/2:ℝ) := by
  apply completed_value_from_witness
  · intro event h
    exact by
      rw [adverseNext_proposal_reward_rule event (List.mem_of_mem_take h)]
      exact adverse_global_quality_upper _
  · refine ⟨adverseNextEvent9,?_,?_⟩
    · simp only [adverseNextProposal]
      simp
    · norm_num [adverseNextEvent9,taskReward,aCold,bCold,seedPath,seedRetriever,leaf,fullLeaf,hyde,branchB] <;> simp +decide

end AgentUCTNextExact
