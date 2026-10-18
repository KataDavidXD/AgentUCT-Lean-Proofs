# AgentUCT Lean Proofs

Public mathematical companion to **Agent-UCT: Upper Confidence Bounds Applied
to Trees for Cost-Aware Agentic Workflow Optimization**,
[arXiv:2607.24162v3](https://arxiv.org/abs/2607.24162v3), 10 October 2026.
The paper and its supplement define the claim scope. The
[Python search core](https://github.com/KataDavidXD/AgentUCT) is maintained
separately.

This repository provides the mathematical core, an English core reading edition,
and the supplementary finite-budget constructions already described in v3.
The supplementary sources add the minimal project import closure for those
constructions. It contains no benchmark runs or experiment runtime.

## Start reading

1. Read Sections 2-4 and the proof-to-claim table in the
   [v3 paper and supplement](https://arxiv.org/pdf/2607.24162v3).
2. Open the [English core proof guide](theory/lean/AgentUCTProofGuideEN.lean).
   Each `#check` displays an actual declaration with its explicit hypotheses.
3. Follow the guide into the [English core proof edition](theory/lean/AgentUCTCompleteProofsEN.lean),
   or use the [modular entry point](theory/lean/AgentUCTPaper.lean) when editing.
4. For the 13M/32M constructed histories, open the
   [supplementary English guide](theory/lean/SupplementaryProofsGuideEN.lean)
   and [supplementary entry point](theory/lean/SupplementaryProofs.lean).
5. See [WORKFLOW.md](WORKFLOW.md) to build and audit the proofs.

The two core editions each contain the same 385 public theorems. Import **either**
`AgentUCTPaper` **or** `AgentUCTCompleteProofsEN` in a downstream file. The
supplementary entry point adds 3,307 public theorems in 133 mathematical modules
and reuses the required modular-core dependencies. Use `SupplementaryProofs` for these
constructions. The combined modular development has 3,692 distinct public
theorems; the English core edition remains a 385-theorem reading edition.

## Main result and assumptions

For a finite fixed-reward terminal tree, the main chain proves

$$R_Q(T)\le A_D\log(T+1)+B_D.$$

Here `T` counts complete training-panel evaluations, including free cache
replays. The assumptions include legal incremental expansion, unvisited-child
priority, raw-return ancestor backup, successful persistent compatible cache
publication, a positive exploration coefficient, and nonnegative adaptive cold
forecasts bounded by a fixed finite resource envelope. Instance constants and
the positive gap bound are chosen before the history and horizon.

The proof uses actual recursive backup statistics and retains the non-root
birth offset. Coverage makes cold penalties vanish; boundedness alone does
not establish that step.

| Paper topic | Source entry |
| --- | --- |
| Counts, raw means and subtree deficits | [TreeBackup](theory/lean/AgentUCTPaper/TreeBackup.lean), [TreeReturns](theory/lean/AgentUCTPaper/TreeReturns.lean), [TreeDecomposition](theory/lean/AgentUCTPaper/TreeDecomposition.lean) |
| Execution, suffix restoration and cold-work accounting | [TreeExecution](theory/lean/AgentUCTPaper/TreeExecution.lean), [TreeCheckpoint](theory/lean/AgentUCTPaper/TreeCheckpoint.lean) |
| Exploration, coverage and the whole-tree rate | [TreeExploration](theory/lean/AgentUCTPaper/TreeExploration.lean), [TreeCoverage](theory/lean/AgentUCTPaper/TreeCoverage.lean), [TreeRate](theory/lean/AgentUCTPaper/TreeRate.lean) |
| Adaptive prices, completion laws and shared publication | [OnlineMean](theory/lean/AgentUCTPaper/OnlineMean.lean), [TreeSharedCache](theory/lean/AgentUCTPaper/TreeSharedCache.lean) |
| Completion forecasts and first-unpaid pricing | [TreeCostEstimation](theory/lean/AgentUCTPaper/TreeCostEstimation.lean), [TreeNextUnpaid](theory/lean/AgentUCTPaper/TreeNextUnpaid.lean) |
| Own-cache budgets and recommendation bounds | [TreeFiniteBudget](theory/lean/AgentUCTPaper/TreeFiniteBudget.lean), [TreeRecommendation](theory/lean/AgentUCTPaper/TreeRecommendation.lean) |
| Demand summaries and information distinctions | [TreeDemandQuotient](theory/lean/AgentUCTPaper/TreeDemandQuotient.lean), [TreeGraphInformation](theory/lean/AgentUCTPaper/TreeGraphInformation.lean) |
| Local pricing certificates and finite dynamic histories | [TreeDecisionValue](theory/lean/AgentUCTPaper/TreeDecisionValue.lean), [DynamicCompletion](theory/lean/AgentUCTPaper/DynamicCompletion.lean) |

These are conditional mathematical statements. The development does not
machine-verify the Python implementation, certify a model or dataset, establish
uniform finite-budget test superiority, or extend the fixed-tree rate to
arbitrary generated programs. Conditional stochastic and local counterexample
modules retain their own assumptions; they are separate from the deterministic
whole-tree argument.

## Supplementary finite-budget constructions

The supplement's section *Conditional Finite-Budget Histories and Accounting
Inputs* describes a stationary constructed task with 150-query panels, a shared
legal MC16 tape, each policy's own cache and receipts, and exact real arithmetic.
The proof derives the histories from the inputs and ordered allocator. A
history's complete crossing evaluation is charged in full; reporting retains
the last affordable complete prefix and excludes future reward and state.

| Construction | What it establishes | Reading entry |
| --- | --- | --- |
| 13M window | Eight common charged seeds; Complete/NextC retain 10/9 evaluations. Favorable and adverse reward tables give opposite training-net signs under the stated prices and controls. | [WindowFiniteBudget](theory/lean/WindowFiniteBudget.lean) |
| Quote projection | Per-query suffix bills sum over the panel and average over sixteen samples. The homogeneous product cache and declared common tape yield the stated factor of 150, using each mode's own cache. | [PhysicalQuoteProjection](theory/lean/PhysicalQuoteProjection.lean) |
| 32M continuation | Four complete native histories, first crossing, retained counts and invoices. Favorable quality saturates at 0.5 for both modes; NextC has higher training net when the cost weight is positive. | [NativeConcreteEndpoints](theory/lean/NativeConcreteEndpoints.lean), [NativeConcreteReporting](theory/lean/NativeConcreteReporting.lean) |
| Initial-price boundary | The specified saved width-k4 prior falls outside this constructed family's uniform error envelope. | [SavedInitialPriorBoundary](theory/lean/SavedInitialPriorBoundary.lean) |

At 13M, the favorable/adverse AgentUCT-minus-NextC training-net difference is
`+/- 0.1 - lambda * 2831.6322489 / Cref`, with `lambda = 0.05` and the declared
reference interval. At the specified 32M inputs, the favorable difference is
`-lambda * 162419.2508523 / Cref`; the adverse difference is
`-0.1 - lambda * 666478.5436779 / Cref`. The 32M proof uses a cap of at least 45,
reporting tolerance in `[0,1]`, specified perturbed initial prices and the fixed
legal completion tape. It does not establish the same trajectories for every
legal tape or a Python random seed.

These quantities use best observed **training** quality minus retained search
cost. The experiments' endpoint `J` uses validation selection, test quality and
all declared optimization phases. The sources do not identify those objectives
or establish Python floating-point, PRNG or service refinement.

## Build and verify

Install [elan](https://github.com/leanprover/elan) and Python 3.11 or later,
then run:

```sh
git clone https://github.com/KataDavidXD/AgentUCT-Lean-Proofs.git
cd AgentUCT-Lean-Proofs
python scripts/verify_proofs.py --bootstrap
```

The project pins **Lean 4.24.0** and **mathlib v4.24.0** through the toolchain
and Lake manifest. The script builds the core and supplement, checks the audit entry points, and
asks Lean for the axioms of every public theorem in three separate groups:
core modular (385), core English (385), and supplementary (3,307). Only
`propext`, `Classical.choice` and `Quot.sound` are accepted.
See the current [GitHub Actions run](https://github.com/KataDavidXD/AgentUCT-Lean-Proofs/actions/workflows/lean.yml)
for the current revision's verification status.

## Source and publication scope

The core snapshot originated on 8 October 2026. The supplementary sources are
the existing mathematical construction described in v3, added with its minimal
project import closure. Original theorem statements and proof bodies are
retained. This is a source release for those already disclosed claims; it does
not add later research results or claim coverage of every experimental or
implementation obligation. Each result's scope is determined by its Lean
statement and the corresponding paper claim.

The default branch contains proof sources, the English reading aid, dependency
locks and verification code. Earlier standalone PDFs, manuscript copies,
development records and vendored authoring tools have been removed from the
current tree. Use the linked arXiv paper for the published text. Git history
retains earlier repository revisions.

[PROVENANCE.md](PROVENANCE.md) records the source boundary and rights;
[THIRD_PARTY_NOTICES.md](THIRD_PARTY_NOTICES.md) lists external dependencies.

Please cite [the paper](https://doi.org/10.48550/arXiv.2607.24162), referring to
[v3](https://arxiv.org/abs/2607.24162v3) for this repository's claim scope.
