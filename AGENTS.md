# Public proof companion

Keep public claims within arXiv:2607.24162v3, including its supplement.
Keep this repository limited to the corresponding mathematical sources,
English reading aids, pinned dependencies and proof-verification code.
Do not import research-workspace snapshots, benchmark records, model assets,
server configuration, development logs or later unpublished constructions.

Canonical proof edits belong in `theory/lean/AgentUCT.lean` and
`theory/lean/AgentUCTPaper/*.lean`. Preserve theorem statements, signatures and
explicit assumptions. After canonical edits, regenerate the English edition
with `python theory/scripts/build_english_proof_bundle.py`, then build the
actual project and audit theorem axioms with `python scripts/verify_proofs.py`.
Import either proof edition; they define the same names.

Read `WORKFLOW.md` before proof work. Record the actual verification outcome.
Lean model proofs do not establish Python refinement or empirical quality.
This repository does not launch model experiments.
