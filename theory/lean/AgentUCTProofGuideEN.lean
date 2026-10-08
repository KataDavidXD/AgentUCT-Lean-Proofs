import AgentUCTCompleteProofsEN

/-!
# AgentUCT: an English guide to the complete Lean proofs

## How to read this development

Open this file in VS Code with the Lean 4 extension, from the directory containing
lakefile.toml. Place the cursor on a #check command to see the declaration's complete
type in the Lean Infoview. Go to Definition opens the complete proof in
AgentUCTCompleteProofsEN.lean. That file contains every project definition and proof
body, arranged by import dependencies, with a SOURCE banner for each original file.
AgentUCT.lean and AgentUCTPaper/*.lean are the canonical modular sources.

A theorem has the form `theorem name (inputs) (h : assumption) : conclusion := by ...`.
Read its type first: hypotheses are part of the claim. Then follow the named `have`
steps and the proof's final `exact`, `simpa`, or `calc`. A successful tactic checks
the implication from the listed hypotheses; it does not establish those hypotheses
for a Python run or a real dataset.

Common Lean vocabulary:
* `intro`: fix an arbitrary object or assume the next premise.
* `obtain`: unpack an existential statement or a conjunction.
* `have`: state and prove a named intermediate fact.
* `calc`: chain equalities or inequalities, with a justification for each step.
* `rw`: replace an expression using a proved equality.
* `apply`: reduce a goal to the premises of a suitable theorem.
* `induction`: prove the base case and the recursive step.
* `simp` / `simpa`: simplify using established definitions and rewrite lemmas.
* `linarith`, `nlinarith`, `omega`: discharge arithmetic consequences of available
  facts; sign conditions and the mathematical estimates still need to be supplied.

The commands below resolve 96 real declarations. They provide a navigation layer;
the imported complete-proof file supplies all definitions and proof bodies.

## Result and scope

The main tree theorem bounds cumulative fixed-training-quality regret by
`A * log(T + 1) + B`. Its constants depend on the finite instance, positive edge-gap
bound, branching/depth, exploration coefficient, and cold-cost envelope. They are
uniform over legal finite histories and horizons for that instance.

The result requires a fixed finite terminal tree, fixed bounded terminal rewards,
the actual backup/allocation rules, successful persistent resource publication,
and nonnegative penalties dominated by completion cold costs with a fixed envelope.
Separate results cover physical cold accounting, local cost/error certificates,
retrospectively affordable completed prefixes, recommendation bounds, and exact
resource-demand quotients. The final section states the guarantees still missing.

## 0. Objects, hypotheses, and quantifier order

`TreeEvaluation` records one completed feedback event: `expanded` is the backed-up
tree node and `terminal` is the completed rollout. Rollout publication and node
backup are distinct operations. `LegalTreeRun` describes legal expansion;
`TreeAllocationRule` separately states the actual maximizing selection rule.

`FixedTableEvents` makes every observed return equal the same terminal reward table.
`PersistentCaches` distinguishes restorable resources from the publication ledger;
the main theorems require their initial equality and use persistent replay updates.
`BoundedTreeRun` combines the operational premises and a common penalty envelope.

The critical quantifier order is `exists delta > 0, forall events, ... bound`.
Choose one gap bound for the instance before choosing the history or horizon.
-/
#check AgentUCTPaper.TreeEvaluation
#check AgentUCTPaper.LegalTreeRun
#check AgentUCTPaper.TreeAllocationRule
#check AgentUCTPaper.FixedTableEvents
#check AgentUCTPaper.PersistentCaches
#check AgentUCTPaper.BoundedTreeRun

/-! ## E1-E3. Actual backups, mean deficit, and parent decomposition

1. Induct on the event list. Replay visits equal the number of actual backed-up
   events, and replay reward sums equal the corresponding return sums.
2. Divide the reward sum by the count to recover the operational mean. Define
   `D = N * V - S`; for positive count, the mean identity is `Q = V - D / N`.
3. Fixed rewards and terminal antichain membership give zero deficit at terminals.
4. Partition a parent's backed events into its birth event and its next-child
   events. The resulting identity retains child deficits and `N_child * gap`.
5. Bound a non-root birth deficit by 1; the root has no birth deficit. Relate local
   choice streams to global backed counts and transport actual index maximality.

Conclusion: the later induction analyzes real replay statistics, including the
non-root birth offset. It does not replace them with independent arm means.
-/
#check AgentUCTPaper.replayBackup_visits
#check AgentUCTPaper.replayBackup_rewardSum
#check AgentUCTPaper.replayBackup_mean
#check AgentUCTPaper.backedDeficit_identity
#check AgentUCTPaper.operational_mean_deficit
#check AgentUCTPaper.operational_mean_le_subtreeValue
#check AgentUCTPaper.terminal_backedDeficit_zero
#check AgentUCTPaper.operational_subtree_deficit_decomposition
#check AgentUCTPaper.internal_birthDeficit_le_one
#check AgentUCTPaper.root_birthDeficit_zero
#check AgentUCTPaper.localBefore_parent_count
#check AgentUCTPaper.projected_index_max

/-! ## E4. Physical cold work and checkpoint suffixes

1. Split each demand into cached and missing resources; only the latter incur cold
   work. Cache union makes the sequential sums telescope resource by resource.
2. Replay the metered events to obtain exact cold-work conservation.
3. With prefix-complete checkpoints, the missing resources equal the suffix beyond
   the deepest recoverable checkpoint.
4. A rollout can publish a prefix whose tree node was never expanded. Its cache
   publication therefore need not change that node's visit count.

Conclusion: physical reuse is a resource-union property. It is recorded separately
from tree statistics and separately from the allocation's predicted penalty.
-/
#check AgentUCTPaper.coldWork_sequential_union
#check AgentUCTPaper.replayMetered_cold_conservation
#check AgentUCTPaper.coldWork_eq_deepest_suffix
#check AgentUCTPaper.rollout_publication_without_backup

/-! ## Q1. A fixed envelope for adaptive completion penalties

1. Every terminal demand is contained in the finite workflow resource union.
2. Nonnegative resource prices bound any missing-demand sum by the full union sum.
3. A nonnegative completion law of total mass 1 preserves that bound in expectation.
4. Resourcewise live prices bounded by fixed base prices inherit the same envelope.

Conclusion: `0 <= penalty <= H` for every relevant history. H is a proof constant;
the operational accounting uses actual completed evaluations and their bills.
-/
#check AgentUCTPaper.referenceColdCost_bounded
#check AgentUCTPaper.coldForecastPenalty_bounded
#check AgentUCTPaper.completion_prediction_envelope

/-! ## Q2. A finite exploration window

1. The unvisited-first rule initializes all legal children.
2. Suppose a target child remains at count at most m through a sufficiently late
   window. Its exploration bonus exceeds H + 2, so its index exceeds 2.
3. Maximality forces the selected child's index to exceed 2. Its mean is at most 1
   and penalty is nonnegative, so its bonus exceeds 1.
4. Rearranging the bonus formula bounds each selected child's pre-selection count
   by a logarithmic cap.
5. Sum the possible selections over the finite children. Their total is smaller
   than the window length, contradicting one actual selection at each step.
6. The explicit window start satisfies both the pressure and length inequalities;
   transport the local conclusion back to actual tree visits.

Conclusion: each child eventually exceeds any fixed visit threshold. Means and
penalties may adapt within their stated bounds during this argument.
-/
#check AgentUCTPaper.initialized_after_unvisited_first
#check AgentUCTPaper.selected_count_under_pressure
#check AgentUCTPaper.small_count_window_bound
#check AgentUCTPaper.finite_window_explores
#check AgentUCTPaper.explorationWindowStart
#check AgentUCTPaper.explorationWindow_pressure
#check AgentUCTPaper.explorationWindow_long_enough
#check AgentUCTPaper.finite_explicit_window_explores
#check AgentUCTPaper.actual_children_explored

/-! ## Q3-Q4. Terminal coverage, restorable coverage, and zero penalties

1. Induct on remaining tree depth. At depth zero, the terminal antichain identifies
   the only possible terminal observation.
2. At an internal node, remove its at-most-one birth visit. The remaining visits
   contain a complete exploration window for every child.
3. Apply the induction hypothesis to each child at its smaller remaining depth.
4. Terminal evaluation publishes the full panel-prefix demand. Persistence turns
   published coverage into restorable coverage.
5. Every legal completion now has an empty missing set. Its cold cost and the
   completion-law-weighted cold penalty are exactly zero.

Conclusion: penalties vanish after an instance-dependent finite coverage threshold.
A bounded penalty alone does not supply this conclusion. Forecast accuracy is not
needed to sum over an empty missing set.
-/
#check AgentUCTPaper.coverageVisits
#check AgentUCTPaper.actual_subtree_coverage
#check AgentUCTPaper.actual_terminal_coverage
#check AgentUCTPaper.actual_restorable_coverage
#check AgentUCTPaper.referenceColdCost_zero
#check AgentUCTPaper.coldForecastPenalty_after_coverage

/-! ## Q5-Q6. Small subtree bias and bounded late suboptimal selection

1. Finiteness gives a common positive lower bound delta for all positive edge gaps.
2. Assume child deficit `D <= A * log(N + 1) + B`. Choose an explicit visit target
   with a positive denominator and two terms each at most delta / 8.
3. Use `log(N + 1) <= 4 * sqrt(N)` to obtain `D / N <= delta / 4` beyond that target.
4. The finite exploration window gets every child beyond the target. At the same
   burn-in threshold, completion penalties have already vanished.
5. The optimal child's actual mean is at least `V(parent) - delta / 4`; a positive-
   gap child has value at most `V(parent) - delta`. Actual index maximality forces
   a sufficiently large exploration bonus for a selected suboptimal child.
6. Check signs, square the bonus inequality, and multiply by its positive count
   denominator. The formal count cap uses the conservative coefficient
   `4 * c^2 / delta^2` times the parent's final logarithm.
7. Add the early burn-in selections and the last count increment +1.

Conclusion: the suboptimal-child count has an explicit logarithmic upper bound,
with finite instance-dependent burn-in retained in the constant term.
-/
#check AgentUCTPaper.finite_tree_positive_edge_gap
#check AgentUCTPaper.biasVisitTarget
#check AgentUCTPaper.logarithmic_deficit_small
#check AgentUCTPaper.selected_count_from_subtree_bias
#check AgentUCTPaper.count_le_burnin_add_cap
#check AgentUCTPaper.actual_suboptimal_child_count

/-! ## Q7-Q8. Depth induction and root cumulative quality regret

1. Base case: a terminal's deficit is zero.
2. Use the exact parent decomposition from E3. Positive-gap terms use Q6 and
   gap <= 1; zero-gap terms are exactly zero. The birth term is at most 1.
3. Apply the induction bound to each child. Since child counts do not exceed the
   parent count, one parent logarithm controls all child logarithms.
4. Sum over children and use the finite tree's maximum branching factor to define
   a common coefficient pair `treeRateConstants` for each remaining depth.
5. Quantify over every valid history prefix during induction. This makes the child
   hypothesis available at the pre-selection histories used by Q6.
6. At the root, N equals the number T of completed evaluations. Its deficit is
   `sum_t (V(root) - reward(terminal_t))`, giving `A * log(T + 1) + B`.
7. Extend to shared caches by union. More restorable resources preserve coverage;
   any nonnegative actual penalty dominated by the complete cold penalty also
   becomes zero and satisfies the same induction argument.

Conclusion: this is cumulative fixed-training-quality regret on a fixed finite
tree. `uniform_root` means constants uniform over legal histories, and imposes no
uniform-rollout requirement. Own-cache net value and endpoint J have separate claims.
-/
#check AgentUCTPaper.treeRateConstants
#check AgentUCTPaper.parent_deficit_log_bound
#check AgentUCTPaper.actual_subtree_log_deficit
#check AgentUCTPaper.root_count_eq_length
#check AgentUCTPaper.root_deficit_is_terminal_quality_regret
#check AgentUCTPaper.cold_forecast_uniform_root_log_bound
#check AgentUCTPaper.shared_cache_uniform_root_log_bound
#check AgentUCTPaper.dominated_cold_shared_root_log_bound
#check AgentUCTPaper.checkpoint_conditioned_shared_root_log_bound

/-! ## Q9. Online means and finite sampled completion laws

1. A prior and prediction samples in [0, cap] have an online average in [0, cap]:
   its denominator is the positive sample count plus 1.
2. Index completion samples by Fin n. Distinct indices remain distinct samples
   even when they refer to the same terminal completion.
3. Exchange the finite sums to equate the sampled-law expectation with the sample
   mean. With n > 0, applying this identity to the constant bill 1 gives mass 1.
4. Supply the resulting nonnegative online prices and fixed envelope to the
   history-dependent shared-cache theorem.

Conclusion: the adaptive estimator preserves the structural quality-regret theorem.
The finite-sample identities establish normalization and accounting algebra.
Statistical forecast-error guarantees require additional assumptions and proofs.
-/
#check AgentUCTPaper.onlineMean_envelope
#check AgentUCTPaper.sampledLaw_expectation
#check AgentUCTPaper.sampledLaw_mass
#check AgentUCTPaper.onlineMean_completion_envelope
#check AgentUCTPaper.online_mean_shared_root_log_bound

/-! ## L. Same-state tradeoff and conditional error certificates

1. Ordinary index maximality gives a nonnegative index loss when moving to the
   priced choice. Priced-index maximality bounds the loss by gamma times predicted
   cost saving. With gamma > 0, the priced choice has no higher predicted cost.
2. If both candidates' absolute cost errors are bounded, subtract the two radii
   from predicted saving to obtain a lower bound on physical saving.
3. To certify actual net gain, also bound both quality errors and weight the cost
   errors by nonnegative gamma.
4. Rewrite reference costs as resource sums. Propagate resourcewise errors into
   full-cost errors and derive the selected net-gap bound from valid cost radii.
5. The mean uniquely minimizes squared error for the specified law. This claim
   concerns that supplied law; it does not certify an empirical completion law.

Conclusion: these are same-state, conditional certificates. The compared index U
includes exploration bonuses, so its loss cannot be called true quality loss.
-/
#check AgentUCTPaper.priced_choice_tradeoff
#check AgentUCTPaper.physical_saving_certificate
#check AgentUCTPaper.actual_net_gain_certificate
#check AgentUCTPaper.referenceColdCost_resource_form
#check AgentUCTPaper.full_reference_cost_error
#check AgentUCTPaper.full_cost_mean_unique_mse_minimizer
#check AgentUCTPaper.selected_net_gap_from_cost_radii

/-! ## N. Next penalties, own trajectories, budgets, and recommendations

1. The legacy direct-edge `nextEdgePenalty` vanishes once that edge is cached.
   Coupled-history equality with UCT additionally requires the same complete-event
   resolver. It is a theorem about that specific legacy penalty.
2. The current first-unpaid `nextUnpaidBill` is bounded by the full missing suffix.
   Proxy-to-full regret transfer retains the cumulative omitted-tail term.
3. Compare each policy using its own actual resource union; do not substitute a
   common cache ledger for both trajectories.
4. For budget reports, complete the evaluation and record the actual bill. Select
   the last affordable completed prefix retrospectively; crossing events stay in
   the run record and their later rewards do not enter earlier snapshots.
5. Best-observed training quality has a simple-gap bound from cumulative quality
   regret. Validation shortlist bounds additionally assume a uniform deviation
   bound. The top-one counterexample records a genuine limitation.
6. Endpoint `J = U - B` has its own gap identity. Equal charged B cancels the cost
   difference, so Delta J equals Delta U at that endpoint.

Conclusion: local index tradeoffs, trajectory net value, cumulative quality regret,
training recommendation, and endpoint J answer different mathematical questions.
-/
#check AgentUCTPaper.next_edge_allocation_iff_uct
#check AgentUCTPaper.next_edge_coupled_history_eq_uct
#check AgentUCTPaper.nextUnpaidBill_le_complete
#check AgentUCTPaper.next_edge_tail_regret_transfer
#check AgentUCTPaper.own_cache_cost_difference
#check AgentUCTPaper.own_cache_policy_regret_bound
#check AgentUCTPaper.own_cache_budget_coverage
#check AgentUCTPaper.best_training_simple_gap
#check AgentUCTPaper.validation_shortlist_gap
#check AgentUCTPaper.validation_top_one_counterexample
#check AgentUCTPaper.endpointJ_gap_identity
#check AgentUCTPaper.equal_quality_positive_endpoint_gap
#check AgentUCTPaper.next_edge_linear_regret

/-! ## G. Graph information and exact demand-based compression

1. Exchange question and prefix sums to obtain the full-panel residual-cost quotient.
   Full-panel publication preserves the rectangular cache property used by it.
2. For live prices, update the missing-resource sum by the corresponding price
   differences. For query-selective demand, group only identical demand profiles.
3. Construct witnesses with equal aggregate summaries and different missing costs
   or rankings when a summary merges demand-separating profiles.

Conclusion: the stated quotients preserve the specified resource information.
The witnesses rule out the particular lossy summaries under consideration.
-/
#check AgentUCTPaper.full_panel_residual_quotient
#check AgentUCTPaper.full_panel_history_rectangular
#check AgentUCTPaper.full_panel_live_completion_quotient
#check AgentUCTPaper.full_panel_live_price_update
#check AgentUCTPaper.demand_group_cost_quotient
#check AgentUCTPaper.demand_group_publication
#check AgentUCTPaper.demand_separating_merge_loses_information
#check AgentUCTPaper.GraphWitness.no_count_only_optimal_policy
#check AgentUCTPaper.ReachablePairs.active_pair_ranking_reverses

/-! ## A. Proven Results and Extension Directions

The finite-tree quality theorem, execution-accounting identities, same-state
conditional cost certificates, and full-panel cost quotients are proved under
their stated assumptions. The extensions below introduce new models or evidence
and have separate acceptance criteria.

Established dynamic results:
1. Induct over a finite actual demand list to obtain exact union cold accounting.
   Retain repeated proposal and repair overhead as separate charged terms.
2. Expand generation-before and completion-after expected costs using an execution
   law of mass 1; the two-stage identity needs no independence assumption.
3. Valid optimistic quality bounds and pessimistic cost bounds give one-step loss
   at most `rq + gamma * rc`. Sum this inequality over the actual history.
4. Fresh resources at every step can produce linear cold-work growth. A recurring
   omitted suffix can likewise accumulate a persistent proxy error.

Extension direction 1 -- stochastic rewards:
The fixed-tree main theorem assumes repeated evaluation of a terminal gives its
fixed table reward. A stochastic extension must specify conditional reward means,
noise assumptions, concentration under adaptive sampling, and the replacement
for the exact mean-deficit identity. Publication failures and cache eviction also
require explicit operational models beyond the persistent-successful-cache result.

Extension direction 2 -- certified forecast errors:
Existing net-value certificates assume valid error radii. Derive those radii for
the actual sampled completion law and online physical-cost estimator, including
adaptive selection, sample dependence, and any required uniform coverage.

Extension direction 3 -- held-out test generalization:
The cumulative theorem uses a fixed training panel. State the data-distribution
assumptions and control adaptive model selection to transfer a recommendation
bound to fresh test questions. Validation deviation assumptions are conditional
inputs in the existing results; a general test guarantee is not derived here.

Extension direction 4 -- a quality rate on a growing edit tree:
Dynamic cost identities and conditional optimistic-loss bounds are proved. A whole-
tree logarithmic quality-regret rate for AFlow-style ongoing generation/repair
would also need a model of newly arriving nodes, changing depth/branching/gaps,
coverage of newly created demands, and the comparator class over time.

Extension direction 5 -- Python refinement:
Define a representation relation from concrete Python histories, checkpoints,
resource keys, bills, failures, and statistics to the Lean structures. Prove that
each Python transition preserves this relation and implements the stated backup,
publication, selection, and completed-prefix accounting rules. The current Lean
development certifies its abstract model; that implementation correspondence
remains to be established.

Additional boundary: a frozen empty-cache static penalty need not become zero after
coverage. Analyze its resulting objective under suitable assumptions separately.
-/
#check AgentUCTPaper.dynamic_spend_union
#check AgentUCTPaper.dynamic_spend_with_overhead
#check AgentUCTPaper.generated_completion_two_stage
#check AgentUCTPaper.dynamic_optimistic_net_loss
#check AgentUCTPaper.dynamic_optimistic_cumulative
#check AgentUCTPaper.fresh_dynamic_resource_cost
#check AgentUCTPaper.recurring_omitted_suffix
