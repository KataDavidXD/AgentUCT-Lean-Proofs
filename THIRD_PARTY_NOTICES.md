# Third-party dependencies

| Component | Upstream | License |
| --- | --- | --- |
| Lean 4 | [leanprover/lean4](https://github.com/leanprover/lean4) | Apache-2.0 |
| mathlib | [leanprover-community/mathlib4](https://github.com/leanprover-community/mathlib4) | Apache-2.0 |
| Aesop | [leanprover-community/aesop](https://github.com/leanprover-community/aesop) | Apache-2.0 |

Lean is installed through elan; mathlib and its transitive dependencies are
fetched at the revisions in `theory/lean/lake-manifest.json`. Each dependency's
own license governs that dependency. No third-party source bundle is vendored
in the current tree.

Original AgentUCT research materials retain their authors' existing rights;
this cleanup grants no new license to the proofs or paper.
