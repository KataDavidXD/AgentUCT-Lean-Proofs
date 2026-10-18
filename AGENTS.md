# Public proof companion

Keep public claims within arXiv:2607.24162v3, including its supplement.
Keep this repository limited to the corresponding mathematical sources,
English reading aids, pinned dependencies and proof-verification code.
Do not import research-workspace snapshots, benchmark records, model assets,
server configuration, development logs or later unpublished constructions.

Canonical core proof edits belong in `theory/lean/AgentUCT.lean` and
`theory/lean/AgentUCTPaper/*.lean`. Supplementary mathematical sources are the
133-module import closure of `SupplementaryProofs.lean`; the English guide
explains its four disclosed constructions. Preserve theorem statements,
signatures and explicit assumptions. After canonical core edits, regenerate the English edition
with `python theory/scripts/build_english_proof_bundle.py`, then build the
actual project and audit theorem axioms with `python scripts/verify_proofs.py`.
Import either core proof edition; they define the same names.
The supplement reuses the required modular-core dependencies. Keep the verifier's three groups
separate: core modular 385, core English 385 and supplementary 3,307 public
theorems. Do not describe the core English edition as containing the supplement.

The 13M construction gives favorable and adverse examples under declared
inputs. At the specified 32M cutoff, favorable quality saturates and the extra
search charge removes the early gain; adverse net is also lower. Preserve
the real-arithmetic, specified-invoice, perturbed-prior, own-cache and fixed-tape
assumptions. Do not claim Python Float, PRNG or service refinement, all-tape
trajectories, or universal finite-budget superiority. Do not add publication
venue, submission identifiers, review information or private-workspace links.

Read `WORKFLOW.md` before proof work. Record the actual verification outcome.
Lean model proofs do not establish Python refinement or empirical quality.
This repository does not launch model experiments.
