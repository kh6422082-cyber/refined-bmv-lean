# Refined BMV lower bounds in Lean 4

This repository contains the Lean 4 formalization accompanying **Dimension-independent lower bounds for matrix-word averages at low degrees**.

All main mathematical results and their required proof dependencies are formalized. The development covers arbitrary positive finite dimension. The six finite strong comparisons include singular positive semidefinite inputs; the exponential bounds use positive definite inputs.

## Build and independently verify

Install Lean using [elan](https://github.com/leanprover/elan). This repository pins:

- Lean `leanprover/lean4:v4.34.0` in `lean-toolchain`.
- mathlib commit `5ed2965256430c3649e86755f9576b54eca72435` in `lakefile.toml` and `lake-manifest.json`.

From the repository root:

```sh
lake exe cache get
lake build
lake env lean Audit.lean
```

For a build plus a machine-readable audit report, run:

```sh
lake exe cache get
python3 scripts/verify_release.py
```

On Windows, `python` can be used in place of `python3`. The script rejects proof placeholders, newly introduced target axioms, and native proof evaluation; it checks every audit record against the allowlist `propext`, `Classical.choice`, `Quot.sound`.

The delivered development contains **55 Lean source files** and **200 audited declarations**. Exact finite certificates use `decide +kernel`. There are no `sorry`, `admit`, newly introduced target axioms, or `native_decide` in the delivered Lean sources.

## Main results

- The complete word averages, binomial normalization, and reality of the averages.
- The PSD strong comparisons at `(3,3)`, `(4,3)`, `(3,4)`, `(4,4)`, `(5,4)`, and `(4,5)`.
- The quantitative PSD cubic bound when the endpoint moment is positive.
- The one-letter equality and the two-letter lower bound at arbitrary positive degree.
- Every ALT instance used by the manuscript, including all positive integer parameters required for the bridge.
- The noncommuting symmetric Lie--Trotter limit and `L(n,m) <= T(n,m)` for every positive integer `n,m` and positive definite input pair.
- The complete low-degree region of Corollary 2.3, including its unbounded boundary degrees.
- The positive-definite equality classification `p(5,4) = L(5,4)` if and only if the input matrices commute.

See [THEOREM_MAP.md](THEOREM_MAP.md) for the correspondence between manuscript results and Lean declarations. The aggregate entry point is [RefinedBMV.lean](RefinedBMV.lean); the final theorem assembly is [PaperResults.lean](RefinedBMV/PaperResults.lean).

## Scope

This is a formalization of the main conclusions and their necessary dependencies, rather than a line-by-line transcription of every background assertion in the manuscript. The unrestricted real-parameter ALT background theorem is not separately formalized; all instances used in the main proofs are independently proved. Some auxiliary arguments use alternative formal proof routes. See [SCOPE.md](SCOPE.md).

## Verification records

The `verification` directory contains the original local verification records. The release verification script generates a fresh release-project build/audit record. The original `build_report.json` distinguishes actual recompilation from matching-hash reuse. `release_build_report.json` records whether this repository's own compiled artifacts were absent before the release build; cached pinned mathlib dependency artifacts may still be used. Platform-specific olean hashes are provenance data, not portable source identifiers.

GitHub Actions runs the pinned project build and axiom audit on pushes and pull requests. Inspect the run for the exact commit being cited; the workflow's presence is not itself a statement that a run has passed.

## Citation and license

Cite the manuscript together with an immutable repository commit or release URL. Repository ownership is not a declaration of manuscript authorship. The manuscript's author metadata remains to be finalized by its authors.

The code is distributed under [Apache-2.0](LICENSE). Gordon Hsu's Schur triangulation proof is incorporated with its original copyright header; attribution and compatibility changes appear in [THIRD_PARTY_NOTICES.md](THIRD_PARTY_NOTICES.md).
