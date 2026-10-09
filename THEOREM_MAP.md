# Manuscript-to-Lean correspondence

The manuscript is **Dimension-independent lower bounds for matrix-word averages at low degrees**, initially supplied as version 0.1 dated 9 October 2026. This map lists the public entry points; their supporting proofs are included in the repository.

| Manuscript result | Lean declaration | Source |
|---|---|---|
| Theorem 2.1, PSD strong chain | `RefinedBMV.paper_theorem_2_1_psd` | [PaperMain.lean](RefinedBMV/PaperMain.lean) |
| Theorem 2.1, exponential consequence | `RefinedBMV.paper_theorem_2_1_exponential` | [PaperResults.lean](RefinedBMV/PaperResults.lean) |
| Theorem 2.2, PSD/Hermitian strong chain | `RefinedBMV.paper_theorem_2_2_psd` | [PaperMain.lean](RefinedBMV/PaperMain.lean) |
| Theorem 2.2, P=U equality | `RefinedBMV.paper_theorem_2_2_equality` | [PaperMain.lean](RefinedBMV/PaperMain.lean) |
| Theorem 2.2, full exponential chain and equality | `RefinedBMV.paper_theorem_2_2_exponential` | [PaperResults.lean](RefinedBMV/PaperResults.lean) |
| Corollary 2.3, complete positive-input region | `RefinedBMV.paper_corollary_2_3` | [PaperResults.lean](RefinedBMV/PaperResults.lean) |
| Corollary 2.3, six-pair PSD clause | `RefinedBMV.paper_corollary_2_3_finite_psd` | [PaperResults.lean](RefinedBMV/PaperResults.lean) |
| Commuting equalities (2.5) | `RefinedBMV.paper_commuting_equalities` | [Commuting.lean](RefinedBMV/Commuting.lean) |
| Exponential bridge, Lemma 3.1 | `RefinedBMV.paper_lemma_3_1` | [ExponentialBridge.lean](RefinedBMV/ExponentialBridge.lean) |
| Actual CFC-power product limit | `RefinedBMV.cfc_trotter_tendsto` | [ExponentialBridge.lean](RefinedBMV/ExponentialBridge.lean) |
| General noncommuting symmetric Lie--Trotter limit | `RefinedBMV.symmetric_trotter_tendsto_multiple` | [SymmetricTrotter.lean](RefinedBMV/SymmetricTrotter.lean) |
| ALT used instances (3.1) | `RefinedBMV.alt_rational_sandwich_psd`, `RefinedBMV.alt_integer_sandwich_psd` | [ALTFamilies.lean](RefinedBMV/ALTFamilies.lean) |
| Every finite-step bridge comparison (3.2) | `RefinedBMV.alt_trotter_approximants_le` | [ALTFamilies.lean](RefinedBMV/ALTFamilies.lean) |
| Reversed comparison (3.3) | `RefinedBMV.reversed34_psd` | [Reversed34.lean](RefinedBMV/Reversed34.lean) |
| Reversed comparison (3.4) | `RefinedBMV.reversed45_psd` | [Reversed45.lean](RefinedBMV/Reversed45.lean) |
| Proposition 3.2, one letter | `RefinedBMV.paper_proposition_3_2_one` | [OneLetter.lean](RefinedBMV/OneLetter.lean) |
| Proposition 3.2, two letters | `RefinedBMV.paper_proposition_3_2_two` | [TwoLetterBoundary.lean](RefinedBMV/TwoLetterBoundary.lean) |
| Proposition 4.1, complete PSD strong chain | `RefinedBMV.paper_proposition_4_1_psd` | [Strong43.lean](RefinedBMV/Strong43.lean) |
| Exponential equality (6.7) | `RefinedBMV.paper_exponential_equality54` | [PaperResults.lean](RefinedBMV/PaperResults.lean) |
| Proposition 7.1, PSD strong conclusion | `RefinedBMV.paper_proposition_7_1_psd` | [CubicALT.lean](RefinedBMV/CubicALT.lean) |
| Proposition 7.1, quantitative PSD conclusion | `RefinedBMV.paper_proposition_7_1_quantitative` | [CubicQuantitative.lean](RefinedBMV/CubicQuantitative.lean) |
| Appendix finite certificates | `RefinedBMV.certificate44`, `RefinedBMV.certificate44sos`, `RefinedBMV.certificate54` | [Certificates.lean](RefinedBMV/Certificates.lean) |

Numerical inequalities use `reTrace`. The development also proves the relevant full complex traces are real, including [the actual exponential trace](RefinedBMV/ExponentialBridge.lean). Matrix fractional powers are explicit CFC matrix powers, rather than entrywise powers of a function type.
