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

1. Inventories the modular mathematical declarations and checks for proof
   placeholders or custom axiom declarations outside comments and strings.
2. Builds the configured modular entry point, English reading edition and guide.
3. Compiles the remaining Lean audit entry points.
4. Runs `#print axioms` for every public theorem in both proof editions and
   accepts only `propext`, `Classical.choice` and `Quot.sound`.
5. Fails on compiler errors, warnings, missing declarations or nonstandard axioms.

Local reports and logs go to ignored `.verification/`. An optional
`--output PATH` selects another output directory. GitHub Actions runs the same
checks from a clean checkout. Inspect the status for the revision being used;
a past green run does not verify later edits.

## Read or edit

Open `theory/lean` with the Lean 4 editor extension. Start from
`AgentUCTProofGuideEN.lean`; each `#check` exposes the referenced declaration's
actual type. Follow the SOURCE banners in `AgentUCTCompleteProofsEN.lean` to
the canonical module when editing.

After a canonical edit, regenerate the reading edition:

```sh
python theory/scripts/build_english_proof_bundle.py
python scripts/verify_proofs.py
```

The generator writes only the English edition and an ignored local source map.
Preserve theorem statements and hypotheses when making presentation changes.
Neither editor diagnostics nor source scanning substitutes for a successful
Lean build and axiom audit.

## Interpretation

These checks validate the listed conditional mathematics. The paper's
Python-to-Lean refinement and experimental evidence have separate obligations.
This workflow has no model calls or experiment launchers.
