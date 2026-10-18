# AgentUCT Lean Proofs

Public mathematical companion to **Agent-UCT: Upper Confidence Bounds Applied
to Trees for Cost-Aware Agentic Workflow Optimization**,
[arXiv:2607.24162v3](https://arxiv.org/abs/2607.24162v3), 10 October 2026.
The paper and its supplement define the claim scope. The
[Python search core](https://github.com/KataDavidXD/AgentUCT) is maintained
separately.

This repository provides the existing Lean development, an English reading
edition and a reproducible proof check. It is a selected mathematical companion,
not a complete artifact for every supplemental construction or experiment.
It contains no benchmark runs or experiment runtime.

## Start reading

1. Read Sections 2-4 and the proof-to-claim table in the
   [v3 paper and supplement](https://arxiv.org/pdf/2607.24162v3).
2. Open the [English proof guide](theory/lean/AgentUCTProofGuideEN.lean).
   Each `#check` displays an actual declaration with its explicit hypotheses.
3. Follow the guide into the [English complete-proof edition](theory/lean/AgentUCTCompleteProofsEN.lean),
   or use the [modular entry point](theory/lean/AgentUCTPaper.lean) when editing.
4. See [WORKFLOW.md](WORKFLOW.md) to build and audit the proofs.

The two proof editions define the same names. Import **either**
`AgentUCTPaper` **or** `AgentUCTCompleteProofsEN` in a downstream file.

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

## Build and verify

Install [elan](https://github.com/leanprover/elan) and Python 3.11 or later,
then run:

```sh
git clone https://github.com/KataDavidXD/AgentUCT-Lean-Proofs.git
cd AgentUCT-Lean-Proofs
python scripts/verify_proofs.py --bootstrap
```

The project pins **Lean 4.24.0** and **mathlib v4.24.0** through the toolchain
and Lake manifest. The script builds the retained sources, checks the audit
entry points, and asks Lean for the axioms of every public theorem in each
edition. Only `propext`, `Classical.choice` and `Quot.sound` are accepted.
See the current [GitHub Actions run](https://github.com/KataDavidXD/AgentUCT-Lean-Proofs/actions/workflows/lean.yml)
for the current revision's verification status.

## Source and publication scope

The mathematical snapshot originated on 8 October 2026 and is retained here
with its original statements. The public cleanup aligns navigation and claims
with v3; it adds no new theorem or later construction. The repository does
not claim coverage of every result added to the final supplement. A result's
scope is determined by its Lean statement and the corresponding paper claim.

The default branch contains proof sources, the English reading aid, dependency
locks and verification code. Earlier standalone PDFs, manuscript copies,
development records and vendored authoring tools have been removed from the
current tree. Use the linked arXiv paper for the published text. Git history
retains earlier repository revisions.

[PROVENANCE.md](PROVENANCE.md) records the source boundary and rights;
[THIRD_PARTY_NOTICES.md](THIRD_PARTY_NOTICES.md) lists external dependencies.

Please cite [the paper](https://doi.org/10.48550/arXiv.2607.24162), referring to
[v3](https://arxiv.org/abs/2607.24162v3) for this repository's claim scope.
