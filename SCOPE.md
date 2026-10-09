# Formalization scope

All main mathematical conclusions of the accompanying manuscript and all dependencies required to prove them are included. The complete region is exactly the union of positive-degree pairs with `min(n,m) <= 2` and the six pairs `(3,3)`, `(4,3)`, `(3,4)`, `(4,4)`, `(5,4)`, `(4,5)`; it is not the entire rectangle through degree five.

The machine-readable [coverage record](verification/paper_coverage.json) distinguishes:

- `required_main_results_complete: true`;
- `remaining_required_proofs: []`;
- `paper_coverage_complete: false`, where this last field denotes strict statement-by-statement coverage of the whole manuscript, including background assertions and unused intermediates.

The full ALT background theorem for arbitrary real `r >= 1` and real `q > 0` is not separately formalized. The repository instead proves every positive integer `q` instance at `r = n/q` for natural `n >= q`, including every positive integer `r = k` family needed by the exponential bridge. None of the main formal proofs assumes the unrestricted background theorem.

Three proof routes replace the corresponding auxiliary presentation:

1. The two-letter boundary bounds each word individually, replacing the manuscript's uniform gap-average identity.
2. The even-disk argument uses the second-order Schwarz lemma directly, replacing the auxiliary function `H(w^2)`.
3. The noncommuting product limit uses matching first derivatives, local linear norm bounds, and a power-difference estimate, replacing the matrix-logarithm-series argument.

The original auxiliary steps are not claimed to be individually formalized. Their target conclusions are established by the complete replacement proofs.

The inequality and quantitative results include singular PSD inputs where stated. Ordinary matrix-logarithm/exponential bridge applications are restricted to positive definite inputs. The equality classification at `(5,4)` concerns positive definite inputs.
