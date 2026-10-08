# AgentUCT proof archive

This is a private proof/workflow repository. Keep it private. Original research
materials retain their authors' rights; vendored tools retain their MIT licenses.

Canonical proof edits belong in `theory/lean/AgentUCT.lean` and
`theory/lean/AgentUCTPaper/*.lean`. Preserve declaration statements and explicit
assumptions. Regenerate the English reading edition with
`python theory/scripts/build_english_proof_bundle.py` after canonical edits.
Import either `AgentUCTPaper` or `AgentUCTCompleteProofsEN`, since they define
the same names.

Read `WORKFLOW.md` and the vendored Lean skill before proof work. Use LSP goal
inspection when available. Compile the actual edited project and audit theorem
axioms. Record what was checked; keep historical logs separate from new checks.
Do not treat Lean model proofs as Python refinement or empirical quality evidence.

The authorized scope here is CPU proof tooling and document work. AAMAS27 model
experiments belong on No12-1 under `/data1/user1/AAMAS27`; read that project's
README sections 10-11 before any experiment. No custom fingerprint, SHA or
source-byte admission gates. No search-cost admission check before model calls:
finish evaluations, record actual charges, retain crossing evaluations, and
select the last complete affordable snapshot retrospectively. Preserve live
jobs and per-GPU ownership/locks; release only the matching project holder
before an authorized experiment. The project layout is six Qwen3.5-4B generator
GPUs, one shared retrieval GPU, and one reserve. Repeat that policy in experiment
invocation records. This archive does not launch model experiments.
