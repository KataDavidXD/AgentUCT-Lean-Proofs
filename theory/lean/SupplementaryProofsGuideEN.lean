import SupplementaryProofs

/-!
# Reading the supplementary finite-budget proofs

This guide covers the conditional finite-budget histories and accounting inputs
in the supplement to arXiv:2607.24162v3. Open a `#check` below to inspect the full
statement; use Go to Definition to follow its proof. The 133 supplementary
mathematical modules contain 3,307 public theorems. They reuse the modular core,
whose 385 theorems also have the separate AgentUCTCompleteProofsEN reading edition.

## 1. A constructed 13M example with two net directions

Start with NativeGrammar for the legal workflow tree and NativeBudgetResolver for
the common legal completion tape. PanelSourceAllocator, PanelReceiptBilling and
PanelBudgetReporting define ordered allocation, receipts and retrospective
reporting. NativeCausalGenerated and ObservedBudgetTrajectories connect the
current own-history observations to the actual generated choices.

WindowFiniteBudget proves a nonempty stationary accounting-task family with
150-query panels, eight common charged seeds, beta = 2, c = 1.4, lambda = 0.05,
13M actual-cost cutoff, tolerance 1e-7 and a cap of at least eleven. The reference
lies in [1,470,000, 1,471,000]; covered initial-price error is at most 1e-6.
Each mode owns its cache and receipts. Complete retains ten evaluations and
NextC nine. The favorable and adverse reward tables give training-net difference
`± 0.1 - lambda * 2831.6322489 / Cref`, with opposite signs. These examples
describe a mechanism under their input conditions; they are not a uniform
finite-budget comparison of policies.
-/

#check AgentUCTSavedBudget.control_window_full_histories_generated
#check AgentUCTSavedBudget.control_window_reporting_indices
#check AgentUCTSavedBudget.control_window_strict_whole_crossings
#check AgentUCTSavedBudget.control_window_positive_and_adverse_net
#check AgentUCTSavedBudget.uniform_control_window_class_inhabited

/-!
## 2. Per-query and full-panel quote projection

PhysicalQuoteProjection relates the per-query suffix loop to the panel quote.
In general the quote is (1/16) times the sum over samples and queries. In this
homogeneous product-cache construction it is (150/16) times the sample sum;
the declared identical common completion tape reduces this to 150 times one
path quote. Complete sums the whole suffix; NextC stops at its first strictly
positive predicted price. The projection always uses the mode's own cache.
CompletedQuoteEnvelope and CompletedPanelError handle the initial-price error
and zero/positive support conditions separately. These are real-arithmetic
identities, not a floating-point error certificate.
-/

#check AgentUCT32MConcrete.source_suffix_full_panel_projection
#check AgentUCT32MConcrete.source_quote_full_panel_projection
#check AgentUCT32MConcrete.physical_mc16_full_panel_projection
#check AgentUCT32MConcrete.physical_reference_penalty_full_panel_projection
#check AgentUCT32MConcrete.completed_physical_bill_full_panel_projection

/-!
## 3. The specified complete 32M continuations

NativeConcreteEndpoints derives all four complete native histories from the
declared integer invoices, reward tables, perturbed initial prices, 150-query
panel and fixed legal MC16 tape. The reference is 1470690.0198555747, beta = 2,
c = 1.4 and every common cap is at least 45. NativeConcreteReporting establishes
the first actual crossing and the last affordable complete prefix for every
reporting tolerance in [0,1]. Crossing evaluations are fully charged; their
future reward, receipts and cache state do not enter the earlier snapshot.

In favorable Complete/NextC and adverse Complete/NextC order, whole-history
lengths are 44/37/45/36 and retained counts are 43/36/44/35. Favorable retained
qualities saturate at 0.5/0.5, while adverse retained qualities are 0.4/0.5.
The AgentUCT-minus-NextC training-net differences at 32M are
`-lambda * 162419.2508523 / Cref` and
`-0.1 - lambda * 666478.5436779 / Cref`. Thus NextC has strictly larger training
net for lambda > 0 in the favorable task and lambda >= 0 in the adverse task.
The positive early 13M example does not persist at this specified 32M cutoff.

The Choices modules certify each ordered comparison, including comparisons
below the root. The Invoice, RetainedNet and Reporting modules give readable
endpoint summaries; follow them before inspecting individual certificates.
-/

#check AgentUCT32MConcrete.favorableComplete_actual_control_run
#check AgentUCT32MConcrete.favorableNext_actual_control_run
#check AgentUCT32MConcrete.adverseComplete_actual_control_run
#check AgentUCT32MConcrete.adverseNext_actual_control_run
#check AgentUCT32MConcrete.favorableComplete_actual_first_crossing
#check AgentUCT32MConcrete.favorableComplete_actual_reporting_index
#check AgentUCT32MConcrete.favorableNext_actual_reporting_index
#check AgentUCT32MConcrete.adverseComplete_actual_reporting_index
#check AgentUCT32MConcrete.adverseNext_actual_reporting_index
#check AgentUCT32MConcrete.favorableComplete_actual_reported_net
#check AgentUCT32MConcrete.favorableNext_actual_reported_net
#check AgentUCT32MConcrete.adverseComplete_actual_reported_net
#check AgentUCT32MConcrete.adverseNext_actual_reported_net
#check AgentUCT32MConcrete.favorable_actual_next_net_strictly_larger
#check AgentUCT32MConcrete.adverse_actual_next_net_strictly_larger

/-!
## 4. Initial-price and implementation boundaries

SavedInitialPriorBoundary proves that the specified saved width-k4 prior falls
outside this constructed family's uniform price-error envelope. It does not
identify a service run with the construction. Such a correspondence also needs
the service's invocation cardinality, initial price table, completion law,
arithmetic and receipts. Positive recurring proposer, repair or replay charges
would change the bills.

These proofs use exact real arithmetic and a specified legal tape. They do not
verify Python/IEEE floating-point refinement, the default PRNG or a random-seed
realization, live services, all legal tapes or empirical quality. The objective
here is best observed training quality minus retained search cost. Benchmark
endpoint J uses validation selection, test quality and all its declared phases.
No correspondence between those different objectives is asserted.
-/

#check AgentUCTSavedPriorDiagnostic.initial_saved_width_four_quote
#check AgentUCTSavedPriorDiagnostic.initial_saved_width_four_error_exceeds_uniform
#check AgentUCTSavedPriorDiagnostic.saved_width_four_prior_not_uniform_admissible
