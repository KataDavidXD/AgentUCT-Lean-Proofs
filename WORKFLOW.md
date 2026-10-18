# Reproduce the Lean checks

## Requirements

- Python 3.11 or later, using only its standard library.
- [elan](https://github.com/leanprover/elan), with `lean` and `lake` on `PATH`.
- Git and network access for the pinned Lake dependencies and mathlib cache.

Lean is fixed at 4.24.0 in `theory/lean/lean-toolchain`. The project requests
mathlib v4.24.0; `lake-manifest.json` pins its dependency revisions.

## From a clean clone

From the repository root:

```sh
python scripts/verify_proofs.py --bootstrap
```

`--bootstrap` retrieves the required mathlib compiled cache. On an already
prepared checkout, use `python scripts/verify_proofs.py`.

The verifier:

1. Inventories the core and supplementary mathematical declarations and checks for proof
   placeholders or custom axiom declarations outside comments and strings.
2. Builds the core entry point, English core reading edition and guide, plus
   `SupplementaryProofs` and `SupplementaryProofsGuideEN` with all their imports.
3. Compiles the additional Lean audit entry points without recompiling every
   supplementary source a second time.
4. Runs `#print axioms` for every public theorem in three separate groups:
   core modular (385), core English (385), supplementary (3,307). It
   accepts only `propext`, `Classical.choice` and `Quot.sound`.
5. Fails on compiler errors, missing declarations or nonstandard axioms.
   Non-fatal Lean lint warnings are counted separately in the report and retained
   in logs. Existing proof bodies are preserved rather than rewritten to remove
   presentation lints such as unused simp arguments or local variables.

The core has 45 mathematical source files, including its original root module;
the supplement adds 133 mathematical modules. The combined modular mathematical
scope has 3,692 distinct public theorems. The verifier reads the supplementary
entry point's project import closure and excludes the already counted core from
its supplementary audit. The English core edition does not contain the added
finite-budget constructions.

Local reports and logs go to ignored `.verification/`. An optional
`--output PATH` selects another output directory. GitHub Actions runs the same
checks from a clean checkout. Inspect the status for the revision being used;
a past green run does not verify later edits. Reports include actual elapsed
times for the build and each axiom audit.
CI sets `LEAN_NUM_THREADS=2` to keep the Lean task pool modest on the hosted
runner and passes `--sequential` to build project modules one at a time in
import order. This avoids overlapping large project elaborations; the final
default build, additional audits and all three axiom groups still run.
The job allows up to 120 minutes for a clean build and the complete official
per-theorem axiom queries; a clean hosted build alone can approach an hour.
For the same build strategy locally, add `--sequential` to the command above.
Each module's label is printed as it starts, and its output is retained in
the local report directory. The workflow's final step prints the verification report and, on failure, the
build-log tail. These diagnostics contain only this public proof project;
the workflow does not upload a source or log archive.

## Read or edit

Open `theory/lean` with the Lean 4 editor extension. Start from
`AgentUCTProofGuideEN.lean` for the core or `SupplementaryProofsGuideEN.lean`
for the finite-budget constructions; each `#check` exposes the referenced
declaration's actual type. Follow the SOURCE banners in
`AgentUCTCompleteProofsEN.lean` to the canonical core module when editing.

After a canonical core edit, regenerate its reading edition:

```sh
python theory/scripts/build_english_proof_bundle.py
python scripts/verify_proofs.py
```

The generator writes only the English core edition and an ignored local source map.
Supplementary edits are checked through `SupplementaryProofs`; they do not
require merging those modules into the core reading edition.
Preserve theorem statements and hypotheses when making presentation changes.
Neither editor diagnostics nor source scanning substitutes for a successful
Lean build and axiom audit.

## Interpretation

These checks validate the listed conditional mathematics. The paper's
Python-to-Lean refinement and experimental evidence have separate obligations.
This workflow has no model calls or experiment launchers.
