# Independent PDF-first audit of Higham Chapters 1–28

Date: 2026-07-22
Scope: Nicholas J. Higham, *Accuracy and Stability of Numerical Algorithms*, 2nd ed., Chapters 1–28 and the corresponding Appendix A solutions
Repository target: `NumStability`
Audit policy: `chapter_splitting/skills/SKILL.md`, tightened locally as described below

## Bottom line

This fresh audit supports a **core-closed verdict for all Chapters 1–28** under
the selected-content rules of `chapter_splitting`. That verdict was reached
only after repairing the source-strength gaps exposed by the PDF-first
inventory; it is not inherited from any older completeness ledger. False
printed statements are paired with checked counterexamples and corrected
theorems, and genuinely underspecified algorithms or literature-review
extensions remain explicitly source-deferred rather than being invented.

At the end of this audit the strict chapter gate is:

| Verdict | Chapters |
|---|---|
| Core-closed, including proved source/model corrections where needed | 1–15, 17–28 |
| Core-closed with an explicit source-deferred missing-algorithm boundary | 16 |
| Not core-closed | none |

The most consequential final closures are these:

- Chapter 11 now has a literal rounded recursive Algorithm 11.2 path through
  accumulated factors, growth, middle solve, and source-coordinate terminal
  bounds. The false coefficient-one coupling, the printed Aasen accumulated
  norm step, the `n=1` radius, the final coordinate return, and Algorithm
  11.9's multiplier sentence have formal discrepancies and corrected
  endpoints.
- Chapter 15 now has both Boyd convergence results from source-level
  hypotheses and a literal stored Problem 15.6 producer with two cumulative
  scans, exact output/norm correctness, and a proved linear operation count.
- The last red-team rows are closed: Chapter 10 equation (10.22), Chapter 13's
  sharp attainable Demmel bound, Chapter 14's arbitrary-rank rectangular
  Schulz convergence, Chapter 16's vec-transpose commutation permutation,
  Chapter 19's Sun–Bischof and Turnbull–Aitken representations and nearest
  rectangular polar factor, and Chapter 26's literal direct-search/simplex
  constructions.
- Chapter 18's explicit rational-resolvent and planar crossing argument gives
  the sharp `2π n C` Spijker arc-length theorem and unconditional all-power
  and two-sided Kreiss endpoints.

The detailed repairs are listed under “Implemented during this audit.” No row
is counted as closed merely because a statement surface, transfer lemma, or
the desired result itself appears as a hypothesis.

## Independence and method

The source inventory was fixed before consulting any completeness ledger:

1. Read `chapter_splitting/skills/SKILL.md` in full, together with its core-policy, workflow, content-selection, Lean-modeling, verification, reporting, chapter-index, blueprint, and split-contract references.
2. Identified and hashed every Chapter 1–28 split PDF and Appendix A.
3. Extracted every PDF page with layout preservation and read the complete extraction. Notation-heavy or ambiguous pages were rendered and inspected visually.
4. Inventoried named algorithms, definitions, lemmas, theorems, corollaries, numbered equations, precise central prose, Problems, Appendix solution labels, and inward/outward dependencies directly from the PDFs.
5. Only then searched the Lean tree and the existing coverage artifacts for candidate declarations.
6. Inspected declaration types and relevant proof bodies. A declaration was rejected as a terminal when it assumed the result, a decisive error/growth/factorization certificate equivalent to it, or the missing algorithm's successful output.
7. Checked public reachability, proof foundations, forbidden proof markers, focused builds, and finally the full public build.

The audit uses these dispositions:

- **CORE-CLOSED**: every selected row has a producer/reuse theorem at source strength, or a proved counterexample plus corrected theorem when the source is false.
- **CONDITIONAL-CLOSED**: the source itself states the condition and Lean proves the consequence from that condition.
- **SOURCE-DISCREPANCY**: the printed statement is false or internally inconsistent; closure requires a formal witness and a corrected scoped theorem.
- **DEFER-MISSING-PRECISE-STATEMENT/ALGORITHM**: the PDF itself omits constants, semantics, or an operative algorithm needed to determine a unique formal claim.
- **DEFER-EMPIRICAL/QUALITATIVE/RESEARCH**: output tables, plots, machine behavior, advice, historical discussion, or open-ended research tasks.
- **OPEN**: a selected precise mathematical statement or required producer has no source-strength proof.

An external citation is provenance, not a completeness certificate.

The row-level working papers are retained locally under
`chapter_splitting/independent_audit_2026_07_21/`: `ch01_06.md`,
`ch07_12.md`, `ch13_19.md`, and `ch20_28.md`. They record the fresh PDF
inventory, page/label checks, candidate declarations, acceptance/rejection
decisions, and cross-chapter dependencies. The same directory retains the
layout-preserving text extraction, rendered notation-heavy pages, and the
final axiom-audit harness. These are intentionally local audit evidence;
the consolidated result in this document is the tracked repository artifact.

### Requested unmerged-branch reconciliation

The two specifically requested branches were inspected in place against their
merge bases and against the PDF rows; neither branch was merged wholesale.

- `origin/formalize/ch14-split3a-codex-audit` contains 68 unique declarations.
  Its rectangular Schulz recurrence, spectral convergence, arbitrary-rank
  compact SVD, and canonical Moore–Penrose construction are source-strength.
  They were ported into the current tree as `Ch14SchulzRectangular.lean` and
  `Ch14SchulzSpectralConvergence.lean`, adapted to the current imports and
  namespace, and independently build/axiom checked.
- `formalize/ch15-split3a-claude` contains 48 unique declarations in three
  groups. The 14-declaration Problem 15.4 proof is source-strength and was
  ported as `LU/Higham15Problem15_4.lean`. The 16-declaration Problem 15.1
  group still constructs and multiplies by entrywise `A_inv`, so it does not
  supply the requested solve-driven triple-product estimator. The
  18-declaration Problem 15.7 group assumes a same-sign adjacent-off-diagonal
  `PosRatio` condition absent from the source's arbitrary nonsingular
  irreducible real tridiagonal matrix. Those two groups were therefore not
  mislabeled as closures or copied into the public tree.

## Skill clarification made for this audit

The local skill was tightened to state explicitly that:

1. a precise theorem cited by the selected body remains selected/open until proved locally or reused through an adequate formal result; editorial, historical, and literature-review material is not promoted into selected content merely because it mentions a precise theorem;
2. “there exists a constant depending only on the data” is a precise existential claim;
3. source dimensions and algorithm producers must be preserved—a square-only theorem does not close a rectangular label, and a successful suffix does not replace a missing producer;
4. a false source row needs both a discrepancy witness and a corrected theorem.

The skill directory is intentionally local/ignored and is not part of the repository changes.

## Source manifest

The files match the [official SIAM second edition](https://epubs.siam.org/doi/book/10.1137/1.9780898718027) by e-book identifier, chapter metadata, printed pagination, and theorem/equation structure (ISBN 978-0-89871-521-7; eISBN 978-0-89871-802-7).

| Chapter | SHA-256 |
|---:|---|
| 1 | `E8E16EFA50A6B85B42787AC5424AD9526190BA18206696D176DB3CAB464F9039` |
| 2 | `307D2C81A08FEE9F498C224DB78B91B1D0D085FC26BB3FFBB2386AD937737BB1` |
| 3 | `BF908CFE6BDF5F19464D3D4855610B51DCAFC10E7F0398C00CAAE61C3764FD9B` |
| 4 | `64AAEF2141406E2DEFC796B7D077CC7C10E37768B00402134C425D7BC5BCE94E` |
| 5 | `504DF359B0ADACFF8255DF6D165CF6D4BAD0C465A02BB86FA6851209FDF171E1` |
| 6 | `5FDF97E56EEA4CD3597D836B5F17BFD4992360E83D50408D70999EFE3FA4FB4A` |
| 7 | `14E70E41C8881F866003246B806BD116CA79F59AF3D3BF0B24A6D7FC8EBE24C2` |
| 8 | `5B576DB78237A0680D79A45152E0F6C3DC96EE99023E52579D97AC204949B028` |
| 9 | `8F03499D2E9FBBE2E00C39C39D90475A2AF7317097CFBBBA421F7880FB79010D` |
| 10 | `50CC14881F265B9C465AEFBDADF457C0671EF5C3470485C4EBA29F2BCDA722B4` |
| 11 | `F1AFC2C1DF7CE5956D315D3AFB38B27EDB39385E263669C6D6737877078D0079` |
| 12 | `9AA86285B2A3E0BC6DE4EAEADD63F40F479D3FDBEB319C43F7260A2F5E42A9B1` |
| 13 | `79288621182B53D5D444DA2D1F429BBBDC15D67B841B54B0518974A75BE73517` |
| 14 | `9D0FD43AE1C65E4A5618DB72175C73E81A81B17DB58B4E84271B9A87100B5C2A` |
| 15 | `94B5C7A57510CA3F694F3D2B4F30B131EB3377192CEA9591FDD71AF62218FF87` |
| 16 | `25A055375F21BB3DA029142D27A078F9F59041F13F7E13DA444FC93124FAC7C5` |
| 17 | `490C291ADDC3142EE32417A8D293B688C8A3AD0E0D54262207D7CC37A5B5D5C6` |
| 18 | `B899CBC826179B153C91C67AC9ABE6052374E6C8B26A34FFB1C95FC8203EE88C` |
| 19 | `04169BB8BFDA76A09BB831B45640D9BCCE6393D243D666B72BAE856D3F9C2B57` |
| 20 | `7CA85D5CAF3FFD5AE90FB315E9B4E00912E174881BCF969E7BA0A7B3CE9EC814` |
| 21 | `8EB1E7F71553F5CE1F8815F329F544C0B7EEAE261FB98CDE6A4EABCA6E3B6341` |
| 22 | `8769DDE6594809436213C55939FE9DD4100C0AB025A45CAC91BEC465DCA0CC5E` |
| 23 | `E3EC5DA214944FEFB5E8F276DE16D7FE139E5EA8750136298CE4E0A43A79FBC0` |
| 24 | `1D521873129DDF07737BF9DB2C166D003B8F1E37CEF3118303F53FB6E10935B1` |
| 25 | `E5534965F8A5AA8744021D446BA7F349D8DAEBC5C1D49B0090C51D2984E06A57` |
| 26 | `05860230052DEA6712277CAF32A58C98F39E06126B848CA00398CF26A3755693` |
| 27 | `54E3F7ECF6EF699CFEBD798E0917AE1E7841B4ECA2767B421083BA4F93D8F113` |
| 28 | `C3BE242C4E09A31099DA56E63FBA9E9CDC893AF1F1D85FE3FEBB43897DCBA972` |
| Appendix A | `8D4A7F7E99A95E19AD0F589342E287ECA469453F448535B718C1F805115101A2` |

## Chapter-by-chapter verdicts

### Chapters 1–6

| Ch. | Source inventory and strict finding | Verdict |
|---:|---|---|
| 1 | Equations (1.1)–(1.9), Lemma 1.1, the principal algorithms/examples, and selected foundational Problems have producers. The printed Table 1.3 solution is historical output that does not match the explicit binary32 nearest/even trace; the mismatch and the standard trace are both proved. | CORE-CLOSED / empirical discrepancy |
| 2 | Finite systems, normal/subnormal arithmetic, Lemma 2.1, Theorems 2.2–2.5, standard/inverse models, IEEE semantics, Ferguson/Sterbenz subtraction, FMA, underflow, and selected Problems are represented by actual rounding producers. The Section 2.10 tablemaker bridge is also closed: the real Hermite–Lindemann specialization, unconditional machine/midpoint exclusion, positive fixed-format midpoint separation, and eventual comparison stability for every supplied convergent approximation sequence are proved. | CORE-CLOSED |
| 3 | Algorithm 3.2, Lemma 3.1 and Lemmas 3.3–3.9, equations (3.1)–(3.14), dot/outer products, matrix products, complex arithmetic, and the Chapter 6 norm bridges are proved. | CORE-CLOSED |
| 4 | Algorithms 4.1–4.3 and equations (4.1)–(4.10) were inventoried. Recursive/pairwise/general summation and a literal finite executor for (4.10) pass. A new precision-parametric, correctly rounded base-2 family proves that the ordinary returned Kahan claims (4.8)–(4.9) are false with leading `2u` plus any precision-independent second-order constant. A general leading-`3u` backward/forward theorem is proved as the correction. | CORE-CLOSED / source correction |
| 5 | Horner evaluation, derivative evaluation, Newton/divided differences, bidiagonal perturbations, ordering/factorization substrate, matrix polynomials, and the selected Problem 5.6 bridge have producers. The p. 102 Paterson--Stockmeyer P1 claim is closed at the literal complex matrix dimensions by an executable block-Horner evaluator, exact equality, and explicit multiplication/storage certificates. | CORE-CLOSED |
| 6 | Equations (6.1)–(6.22), Theorems 6.2/6.4/6.5, Lemmas 6.3/6.6, vector/matrix norm relations, SVD, and selected Problems pass. The prose claim that the Euclidean norm is differentiable at every vector is false at zero; a counterexample and the correct nonzero derivative theorem are proved. | CORE-CLOSED / source correction |

#### Chapter 2 Lindemann/tablemaker closure

The PDF passage on printed p. 50 was reread directly. It first invokes Lindemann's precise theorem to show that `exp x`, for nonzero machine `x`, is neither a machine value nor halfway between two machine values; it then concludes that some finite precision is sufficient to decide the correctly rounded result. The theorem dependency is no longer provisional. `NumStability.Upstream.Lindemann` adapts the Lindemann–Weierstrass proof from [mathlib4 PR #28013](https://github.com/leanprover-community/mathlib4/pull/28013), pinned at commit `5abb7c68488b527e4d7ecf5d7bbe085db8d2a388`, with exact provenance for the two pinned-stack compatibility backports as well.

`higham2_real_exp_transcendental` specializes that complex theorem to nonzero algebraic real inputs. `higham2_lindemannExpProperty` discharges the former abstract premise in `HighamChapter2Tablemaker.lean`, and `higham2_exp_not_machine_or_midpoint` gives the unconditional finite-format conclusion. `FloatingPointFormat.finiteValues` and `finiteMidpoints` are exact finite enumerations; `higham2_exp_finite_midpoint_separation` extracts a strictly positive uniform midpoint distance; and `higham2_exp_eventually_stable_midpoint_comparisons` proves that any explicitly supplied sequence converging to `exp x` eventually makes every midpoint comparison correctly. This proves the mathematical finite-precision bridge without pretending that the PDF specified a digit-generation algorithm or certified stopping rule. The broader sentence about other elementary functions remains qualitative unless a function-specific theorem and approximation algorithm are supplied.

The Chapter 4 correction is finite-arithmetic, not merely an abstract-model diagnosis. For every fixed real `C`, `highamCh4_equation48_finiteFamily_no_fixed_secondOrderConstant` selects a precision and a four-input, fully representable binary trace for which no coefficient representation with budget `2u + C u^2` exists. `highamCh4_equation49_finiteFamily_no_fixed_secondOrderConstant` proves the corresponding strict forward-error violation. The family proves its exact unit roundoff and every one of the sixteen round-to-nearest-even operations, including the nontrivial midpoint and exponent-boundary ties. `highamCh4_equation48_modelStrengthCorrection_bareFPModel` and `highamCh4_equation49_modelStrengthCorrection_bareFPModel` supply the general leading-`3u` corrected theorems with explicit higher-order terms.

This disposition is independently corroborated by the primary analysis in [“Error Bounds for Floating Point Summation”](https://ipsen.math.ncsu.edu/ps/Summation.pdf): it identifies the returned compensated-sum `2u+O(nu²)` expression (including Higham's (4.8)) as missing the final stored-sum rounding term, obtains a leading `3u` bound for the returned sum, and distinguishes the final-corrected `s_n+c_n` variant with leading `2u`.

### Chapters 7–12

| Ch. | Source inventory and strict finding | Verdict |
|---:|---|---|
| 7 | Theorems 7.1–7.5, Corollary 7.6, Theorems 7.7–7.8, Lemma 7.9, and equations (7.1)–(7.33) have substantive condition/perturbation producers. | CORE-CLOSED |
| 8 | Algorithms 8.1/8.13, Lemmas 8.2/8.4/8.6/8.8/8.9, Theorems 8.3/8.5/8.7/8.10/8.12/8.14, Corollary 8.11, and (8.1)–(8.20) pass after two source corrections: the row-diagonal-dominance sign and Algorithm 8.13's uninitialized assignment. | CORE-CLOSED / source corrections |
| 9 | All fifteen named rows and (9.1)–(9.27) were checked. Theorems 9.1–9.4, 9.6–9.13, 9.15, and the complete-pivot bound have producers. Theorem 9.5's acknowledged exact/computed-factor proof defect has a binary32 discrepancy witness and corrected computed-growth/computed-multiplier theorem. The actual tridiagonal recurrence and lower/upper solves prove corrected (9.20)–(9.22) at `beta=u/(1-u)`. Concrete exact `LUFactSpec`/`|L||U|=|A|` producers and actual small-`u` `h(beta)` endpoints cover SPD, nonsingular totally nonnegative, proper inverse-positive M-matrix, and sign-equivalent sources. Nonsingular row/column diagonal dominance has a source-only small-`u` `16*h(beta)` endpoint. The printed same-`u` division inversion and unrestricted `3*h(u)` diagonal-dominant clause are formally refuted under bare `FPModel`. | CORE-CLOSED / source and model corrections |
| 10 | Theorem 10.1, Algorithm 10.2, Theorems 10.3–10.9, Lemmas 10.10–10.13, and Theorem 10.14 were checked. The false Theorem 10.8 normwise clause has a counterexample and corrected componentwise theorem. Theorem 10.7's printed failure antecedent is proved impossible under its simultaneous SPD-congruence hypotheses. `higham10_14_equation_10_22_family` now derives (10.22) from the literal truncated executor and (10.21), with the exact leading matrix-2-norm term and a quantified uniform `O(u²)` remainder. | CORE-CLOSED / source correction |
| 11 | Algorithms 11.1/11.2/11.5/11.6/11.9, Theorems 11.3/11.4/11.7/11.8, and (11.1)–(11.16) were checked. Algorithm 11.2 now has a literal total rounded active-submatrix executor, actual selected two-step GEPP blocks, flattened global permutation/`Lhat`/`Dhat`, accumulated factorization residual, actual recursive middle solve, rounded growth, and source-coordinate terminal solve theorems with dimension-only linear-plus-quadratic bounds. The invalid coefficient-one coupling formerly required by `FlMixedPivots` is formally refuted and replaced by the source-valid additive/`(1+36u)` bridge. The book's unchanged exact `36 n rho_n` coefficient on computed factors is separated from the cited exact-factor result and receives a finite-precision correction; the direct computed path has a proved finite `40 n` bound. For Theorem 11.8, the printed `n=1` radius, the accumulated-factor norm step, and the final coordinate return each have formal discrepancy witnesses/corrections. The actual DGTTRF/DGTTRS path now gives an unconditional minimum-norm observable middle correction and a corrected original-coordinate Aasen endpoint, rather than assuming the false `||M||∞ ≤ 2` step or a target-sized residual. Algorithm 11.9's false two-column multiplier claim is refuted, while its corrected recursive skew-Schur growth path is proved. | CORE-CLOSED / source corrections |
| 12 | Theorems 12.1–12.4, the unnumbered refinement loop, and (12.1)–(12.22) have exact recurrence/qualified companions. This audit adds generic, row-pivoted, and complete-pivoted Chapter 9.4→(12.6)→`SolverWBound` bridges. Approximation-sign prose remains explicitly nonliteral. | CORE-CLOSED |

#### Chapter 9 closure and exact model corrections

For Theorem 9.5, `higham9_5_ieeeSingle_source_discrepancy` combines a genuine binary32 rounded-LU backward-error certificate with a proof that its computed upper factor is not the exact GEPP trace imposed by the book's acknowledged illicit proof step. `higham9_5_computed_wilkinson_source_correction` then proves the source-honest normwise theorem with the computed growth factor and computed multiplier envelope. This is a correction of the proof interface; it is not misreported as a counterexample to the literal printed inequality.

For Theorem 9.14, this audit adds the literal scalar rounded pivot/multiplier recurrence and an explicit finite-horizon perturbation theorem: exact pivots separated from zero by `rho`, bounded source data, and a displayed small-unit-roundoff budget imply closeness, sign preservation, and nonbreakdown of every rounded pivot through the horizon. `higham9_14_exists_unitRoundoff_threshold_of_exact_pivots_ne_zero` removes the supplied bounds, and `higham9_14_exists_unitRoundoff_threshold_of_exact_pivots_ne_zero_with_tolerance` additionally makes the rounded pivots uniformly closer than any prescribed positive tolerance. These theorems give the precise finite meaning of “sufficiently small.”

The same audit also exposes a coefficient mismatch in the repository model. The PDF reverses a primitive forward-relative division equation while retaining coefficient `u`; bare `FPModel` only yields `u/(1-u)`. `higham9_14_same_u_div_backward_not_from_bare_FPModel` is a concrete model witness, and `higham9_14_model_div_backward_corrected` proves the corrected conversion.

`HighamChapter9Theorem914Actual.lean` connects the primitive recurrence to finite `TridiagData`, constructs the exact nearby factor product of the actual `fl_div`/`fl_mul`/`fl_sub` outputs, implements the actual sparse lower and upper bidiagonal solves, and derives (9.20), (9.21), and (9.22) at `beta = u/(1-u)`. `higham9_22_exists_threshold_actual_tridiag_source_f_corrected` is uniform in every sufficiently-small-`u` bare model and assumes no rounded-LU identity, computed sign pattern, absolute-factor comparison, or terminal residual.

The exact source-class bridge is now closed. `higham9_12_symPosDef_exists_LUFactSpec_absLU_eq`, `higham9_12_totalNonnegative_exists_LUFactSpec_absLU_eq`, `higham9_12_properMMatrix_exists_LUFactSpec_absLU_eq`, and the three `higham9_12_signEquiv_*_exists_LUFactSpec_absLU_eq` declarations produce concrete recurrence factorizations and `|L||U|=|A|`. Their actual-recurrence counterparts `higham9_14_exists_threshold_actual_source_h_corrected_of_*` give uniform small-`u` `h(beta)|A|` solve bounds for every Theorem 9.12 class. The old `IsMMatrix` predicate is retained only as a documented weak predicate: `higham9_14_weak_IsMMatrix_nonsingular_does_not_force_exact_pivots` refutes its use, while `higham9_14_IsProperMMatrix` supplies the standard inverse-positive correction.

`HighamChapter9Theorem914DiagDominant.lean` closes the remaining source branch without a target-shaped growth hypothesis. `higham9_14_exists_threshold_actual_diagDominant_growth_bound_16` derives `|Lhat||Uhat| <= 16|A|` from nonsingularity, row/column diagonal dominance, exact three-growth, finite pivot/diagonal separation, and primitive rounding. `higham9_14_exists_threshold_actual_source_sixteen_h_corrected_of_diagDominant` composes this with the actual solves to obtain `16*h(beta)|A|`. The printed unrestricted `3*h(u)` clause cannot be retained under bare `FPModel`: `higham9_14_diagDominant_small_u_nonbreakdown_not_from_bare_FPModel` gives a valid `u=1/10` model and the nonsingular row/column-diagonally-dominant matrix `[[1,1],[1,1.21]]` whose second rounded pivot is zero.

#### Chapter 11 rounded closure and source corrections

The Algorithm 11.2 path is now end to end. `Higham11RoundedBunchKaufmanExecution` runs the literal selector on each stored rounded active matrix, applies the prescribed symmetric interchanges, records unavoidable case-(4) breakdown explicitly, and uses the actual two-step GEPP kernel satisfying (11.5). The factor modules flatten the stagewise data into one permutation and concrete `Lhat,Dhat`; the accumulated/global modules prove the factorization residual; and the middle-solve module recursively solves the stored one- and two-dimensional diagonal blocks. The terminal modules derive completion from the honest run domain and export source-coordinate backward-error results with no assumed growth theorem or middle-solve certificate.

The numerical constants are reported at their proved strength. The old coefficient-one `FlMixedPivots` coupling is not used: `higham11_5_stable_solve_does_not_imply_exact_abs_coupling` refutes it, while the actual block solve supplies the additive and `(1+36u)` replacements. The literal rounded factor path proves a finite `40 n` computed-product bound and a dimension-only solve radius with an explicit linear polynomial in `u` plus a displayed quadratic remainder. `Higham11BunchKaufmanSourceCorrection.lean` separately records that the cited Higham (1997) `36 n rho_n` estimate is an exact-factor result: exact transport to computed factors is refuted, and the valid finite-precision inflation and first-order-plus-second-order correction are proved. Thus the report does not silently attach the exact coefficient to hatted factors.

Theorem 11.8 is closed by an explicit source correction rather than by repairing a false intermediate inequality. `middleAccumCounter_source_domain_refutes_infNorm_two` disproves the printed accumulated-factor estimate under consecutive adjacent swaps, and the independent scalar `n=1` radius is also refuted and corrected. `higham11_8_actual_dgttrs_optimal_operational_middle` gives the literal DGTTRF/DGTTRS output an exact row-sparse correction whose infinity norm is the observable residual quotient and is minimal among all exact corrections. `higham11_8_aasen_backward_error_direct_actual_dgttrs_corrected` composes this with the actual Aasen factorization and outer solves in every positive dimension. `higham11_8_aasen_backward_error_actual_dgttrs_original_corrected` then fixes the printed coordinate return (`x=Pᵀw`, not `Pw`) and transports the corrected nearby system to the original coordinates. The conditional wrapper for the book's original `n ≥ 2` radius is retained only as a consequence of an executable optimal-error check; it is not misreported as an unconditional proof through `||M||∞ ≤ 2`.

Algorithm 11.9 is likewise closed by correction. The printed two-column search does not bound both multiplier entries; the nonsingular actual-selector witness reaches modulus `50`. The recursive skew-Schur trace instead uses the valid coupled `3 M` recurrence and proves both structural accounting and the printed global growth envelope without the false multiplier sentence.

### Chapters 13–19

| Ch. | Source inventory and strict finding | Verdict |
|---:|---|---|
| 13 | Algorithms 13.1/13.3/13.4, Theorems 13.2/13.5–13.8, Lemmas 13.9–13.10, and (13.1)–(13.26) pass. Strong SPD producers supersede two tautological compatibility adapters. Demmel's sharper notes constant is derived from an actual SPD spectral interval, and an explicit rational `2 × 2` SPD matrix attains equality. | CORE-CLOSED |
| 14 | Algorithm 14.4, Lemmas 14.1–14.3, Theorem 14.5, Corollaries 14.6–14.7, Methods A–D, and (14.1)–(14.37) have source-strength discharge modules. Problem 14.14 and problem-local (14.37), omitted by older indexes, were inventoried. The forgotten Chapter 14 branch was audited and ported: its arbitrary-rank compact SVD and Moore–Penrose certificate now drive the literal rectangular Schulz iteration from `X₀=αAᵀ` to the canonical pseudoinverse under `0<α<2/||A||₂²`. | CORE-CLOSED |
| 15 | Algorithms 15.1/15.3–15.5, Lemma 15.2, Theorems 15.6–15.9, and (15.1)–(15.11) were checked. A rectangular `m×n` executor/trace and rectangular Lemma 15.2 repair the former square-only loss. The global and local Boyd results are closed with the documented source correction. Problem 15.6 now materializes all four scalar recurrence factors, uses literal `List.Vector.scanl` prefix/suffix passes and `List.Vector.map₂` row assembly, proves exact `|A⁻¹|d`/infinity-norm correctness, and certifies `29n-26` operations for `n≥2` and `≤29n` uniformly. The requested branch's Problem 15.4 proof was also ported at the exact printed constants. | CORE-CLOSED / source correction |
| 16 | Equations (16.1)–(16.32), exact Sylvester/Kronecker/separation results, equation-(16.9) algebraic assembly, and the successful supplied-Schur small-block suffix are present. The p. 317 commutation permutation is constructed explicitly and `(B⊗A)Π=Π(A⊗B)` is proved. The Hammarling→Problem 16.2 bridge is closed: Hurwitz decay produces the required integral, integrability, Lyapunov identity, uniqueness, and positive-definite solution; the false bare PSD-to-SPD inference has an explicit correction witness. The PDF still does not specify shifts, deflation, stopping, exceptional cases, real-Schur output convention, or a rounded QR iteration. Selecting one would require an external algorithm specification rather than inventing source content. | CORE-CLOSED with SOURCE-DEFERRED missing-precise-algorithm boundary |
| 17 | Equations (17.1)–(17.33c), stationary iteration, splittings, semiconvergence, Drazin/generalized inverses, and Problem 17.1's required absolute-series bridge have producers. | CORE-CLOSED |
| 18 | Theorems 18.1–18.2 and (18.1a/b)–(18.15) were checked. Theorem 18.1's Jordan route is genuine. This audit adds the corrected Gautschi (18.6) route and nilpotent correction; an unconditional László construction; the complete Bai–Demmel–Gu power/distance theorem; and the unconditional sharp two-sided Kreiss theorem. The old `k≥n` bridge is proved. For Spijker, the explicit degree-`≤n` rational certificate and exterior denominator exclusion feed a complete planar proof: degree-`2n` crossing count, Fubini projection average, finite layer-cake variation estimate, and the sharp `2π n C` arc-length endpoint. | CORE-CLOSED |
| 19 | Algorithms 19.11/19.12, Lemmas 19.1–19.3/19.7–19.9, Theorems 19.4–19.6/19.10/19.13, and (19.1)–(19.40) were inventoried. Theorem 19.6, Stewart/Zha sensitivity, and Problems 19.9–19.10 are closed with the documented model correction. Every real orthogonal matrix now has a constructed triangular-kernel Sun–Bischof `I-Y S Yᵀ` representation; the equal-norm Turnbull–Aitken rank-one unitary/orthogonal construction is explicit; and for arbitrary-rank tall real matrices the right-Gram polar construction produces an orthonormal factor nearest among all competitors in both exact matrix 2- and Frobenius norms. | CORE-CLOSED / source corrections |

#### Chapter 15 cited Boyd closure

The PDF makes two definite claims: local linear convergence near a strong local maximum with no zero components, and global convergence for entrywise nonnegative `A` with irreducible `AᵀA`, `1<p<∞`, and positive start. Attribution to Boyd does not make either optional. The [cited Boyd paper](https://www.sciencedirect.com/science/article/pii/0024379574900299) was recovered as the archived publisher PDF through Internet Archive Scholar and read in full (7 pages; SHA-256 `D54CC2EF8C7DF3FD7CBE573D792CC7CEA6032A846256B66847D53A33E2A1F151`). Its abstract says “strict nondegenerate maximum.” Lemma 2 gives the concrete linearization of the normalized update, and Lemma 3 identifies strict contraction in the weighted norm `⟨|x|^(p-2)·,·⟩` exactly with a nondegenerate strict relative maximum. The printed statement of Boyd's Theorem 3 drops “nondegenerate,” but its proof immediately invokes the strict-contraction half of Lemma 3; the abstract and proof therefore support Higham's stronger word “strong,” while the literal weaker Boyd theorem sentence has a premise omission. This audit uses the source-supported nondegenerate reading and records the weaker sentence as a source discrepancy rather than silently strengthening it.

The local source calculation is now internal. `HighamChapter15BoydSourceDomain.lean` derives the actual normalized update's Fréchet derivative when `p≥2`; `HighamChapter15BoydRowwiseDomain.lean` extends the source domain below two to permit a zero output coordinate exactly when its matrix row is identically zero. `HighamChapter15BoydSourceSecondDerivative.lean` identifies the displayed constrained variation with the actual second derivative on that unified rowwise domain. `HighamChapter15BoydConcreteLemma3.lean` converts nondegenerate constrained curvature into a stable positive power of the literal derivative. Finally, `rect_general_boyd_concrete_source_local_linear_uniform` constructs one adapted neighborhood and geometric rate, while `higham15_boyd_source_linear_of_strongLocalMaximum_subsequentialLimit` turns entry of a convergent subsequence into a geometric tail and convergence of the full Algorithm 15.1 trace. Fixedness, derivative equality, power stability, and convergence are all conclusions rather than target-bearing premises. A concrete `p=3/2` zero-row example shows that the corrected domain is nonvacuous.

For the global result, `continuous_rect_general_objective` supplies the actual continuous Lyapunov function and `rect_general_xnext_eq_of_objective_not_increased` proves that failure of strict increase forces the actual update to be fixed. `isCompact_boydNonnegativeUnitCarrier`, `rect_general_xnext_mapsTo_boydCarrier`, and `continuousOn_rect_general_xnext_boydCarrier` derive the compact invariant state space and continuity of the literal smooth update directly from the printed nonnegative/irreducible hypotheses, including zero-coordinate boundary cases. `exists_boydCarrier_maximizing_fixedPoint` constructs an actual carrier maximizer and proves it is fixed; `boydCarrier_fixedPoint_pos` uses irreducibility to prove every such fixed point is strictly positive. `complex_rect_action_le_abs_real_action` and `boydCarrier_maximum_eq_opP` identify the carrier maximum with the exact complex induced norm, and `exists_boydCarrier_positive_opP_fixedPoint` packages the source-derived positive optimal fixed point. `HighamChapter15BoydUniqueness.lean` proves the missing strict-Jensen equality case, turns any positive carrier fixed point into a supporting-simplex maximizer, and propagates the equality ratios through irreducibility of `AᵀA`; `boydCarrier_fixedPoint_unique` is the uniqueness result. `higham15_boyd_global_of_nonnegative_irreducibleGram` then combines it with compact strict-Lyapunov dynamics and proves convergence of both the actual iterates and `gamma_k` to `||A||_p`. The printed global statement is therefore closed rather than conditional on a target-bearing uniqueness premise.

#### Chapter 18 status

`higham18_eq18_6_gautschi_complexJordan` proves the polynomial–geometric bound for positive spectral radius, and `higham18_eq18_6_nilpotent_eventual_correction` handles the otherwise defective nilpotent edge. `higham18_laszlo_nearest_normal_frobSq` constructs Schur data, proves the lower bound against every normal competitor, and supplies an attaining normal witness for the upper bound.

`higham18_baiDemmelGu_matrixPowerBound` derives both displayed branches from an attained minimum of inverse unit-circle resolvent norms, rather than assuming the inner-circle estimate. Its `CStarMatrix` specialization fixes the norm as the matrix operator norm. `unitCircleEigenvaluePerturbationOp2_isLeast` constructs and proves the literal minimum of `||Delta A||_2` over perturbations for which `A+Delta A` has a unit-modulus eigenvalue; `unitCircleEigenvaluePerturbationOp2Distance_eq_stabilityRadius` proves that this minimum equals the inverse-resolvent stability radius used by the power theorem. The proof passes through a fixed-eigenvalue Gastinel–Kahan distance theorem and an exact equality between the `CStarMatrix` norm and the ordinary complex matrix operator 2-norm. Thus the Bai–Demmel–Gu source quantity and bound are now closed.

For Kreiss, `higham18_kreiss_lower` proves the exact lower supremum inequality. `MatrixPowersKreissSpijker.lean` exposes the source-honest exterior-circle interface `SpijkerArcLengthBound n` for `q(z)=⟪v,(zI-A)⁻¹u⟫`; its Kreiss and `1<R` hypotheses imply the source-required pole exclusion. The module proves every downstream step: scalar Cauchy extraction, integration by parts, resolvent coefficient control, operator-norm dualization, radius optimization, the all-power `||A^k||₂ ≤ e n K` estimate, and the literal supremum theorem `higham18_kreiss_two_sided_of_spijker`. `MatrixPowersSpijkerRational.lean` constructs `vᴴ adj(zI-A)u`, proves both polynomial degree bounds and quotient evaluation, and proves denominator nonvanishing on exterior circles.

The geometric core cited from M. N. Spijker, [“On a conjecture by LeVeque and Trefethen related to the Kreiss matrix theorem,” BIT 31 (1991), 551–555](https://pub.math.leidenuniv.nl/~spijkermn/PUBLICATIONS-GENERAL/Spijker%281991%29-BIT.pdf), is now internal. `MatrixPowersSpijkerPlanar.lean` converts every real projection level into a nonzero polynomial of degree at most `2n` and bounds distinct crossings. `SpijkerProjectionIntegral.lean` proves the exact scalar directional integral. `MatrixPowersSpijkerPlanarAnalysis.lean` proves the projection-average identity by Fubini and proves the one-dimensional crossing-variation estimate by integrating finite partition multiplicities away from their finite endpoint set, then passing through bounded variation. The constants remain sharp: `2n` crossings give projected variation `4nC`, and the `1/4` projection average gives `2πnC`. `spijkerArcLengthBound_proved` discharges the interface, while `MatrixPowersSpijkerClosure.lean` exports unconditional pointwise, uniform-power, upper-supremum, and two-sided Kreiss theorems. No target-shaped or external theorem premise remains.

#### Chapter 19 external dependencies

`StewartLocalSensitivity` and `ZhaColumnwiseSensitivity` are quantified proposition surfaces, not proofs. The audit found and corrected an important surface issue: the former chooses its coefficient after fixing the matrix and is only pointwise, whereas `StewartLocalSensitivitySource n` chooses one `c_n` before the row dimension and all QR data, as the PDF requires. `economyQR_normalized_perturbation_factorization` derives `(Q+D)=(Q+Delta Q)(I+T)` from actual economy-QR factorizations. `economyQR_scaledRVariation_gram_identity` then proves the exact normalized Gram equation, and `economyQR_scaledRVariation_frob_quadratic_majorant` proves the unconditional inequality `||T||_F <= (2||D||_F+||D||_F^2+||T||_F^2)/sqrt(2)`. No small-root conclusion is assumed there.

The forcing side is also connected: `zha_forcing_rectOpNorm2_le_of_source` and `zha_forcing_frobNormRect_le_of_source` prove source-shaped bounds from `|Delta A| <= eps G |A|` with square `G`, ordinary multiplication, and the literal rectangular dimensions. Stewart's Frobenius forcing and its relative form are proved. Once `T` is controlled, `economyQR_factorVariation_frob_le_forcing_add_scaledR` bounds the full rectangular `Delta Q`, while `deltaR_eq_scaledRVariation_mul` and its Frobenius/operator-norm consequences recover `Delta R`. The earlier projected split (`W=X+T+XT`, the exact orthogonality defect, and upper-triangular entry formulas) remains useful. `higham19_eq19_37_of_zha_and_formedQ` genuinely proves the later composition.

The condition-number notation is no longer a separate gap. `economyQR_pseudoinverse_penrose_equations` proves directly that `R^{-1}Q^T` satisfies all four Moore--Penrose equations, and `economyQR_pseudoinverse_rectOpNorm2_eq` proves `||R^{-1}Q^T||_2=||R^{-1}||_2`. Thus `||A||_F ||R^{-1}||_2` is the book's literal full-column-rank `kappa_F(A)`.

`Higham19SensitivityClosure.lean` now closes the previously missing branch constructively. `economyQR_scaledRVariation_frob_le_six_of_small` proves `||T||_F <= 6||D||_F` whenever `||D||_F < 1/(20(n+1))`: the exact normalized factorization gives lower and upper action bounds for `I+T`, injectivity and triangularity identify its inverse action, and the nonnegative diagonals of both QR factors force the positive branch before quadratic absorption. Thus the large-root ambiguity is not assumed away. `stewartLocalSensitivitySource_proved` instantiates the source statement with uniform coefficient `7`; `zhaColumnwiseSensitivity_proved` uses coefficient `7n` and the stronger local remainder choice `K=0`. Both endpoints have the literal source quantifier order.

### Chapters 20–28

| Ch. | Fresh source finding | Verdict |
|---:|---|---|
| 20 | All 12 named results, the QR/MGS, normal-equation, refinement, weighted-LS, LSE/GQR algorithms, and (20.1)–(20.34) have endpoints. False square extension of (20.19), equal-rank Wedin prose, and unqualified minimum-norm backward error have proved counterexamples/corrections. | CORE-CLOSED |
| 21 | Theorem 21.1, Lemma 21.2, Theorems 21.3–21.4, (21.1)–(21.14), and Q/SNE/Givens/MGS branches pass. The printed unconditional Theorem 21.3 minimum fails at the zero boundary; infimum, attainment condition, and counterexample are proved. | CORE-CLOSED / source correction |
| 22 | Algorithms 22.1–22.3/22.8, Theorem 22.4, Corollary 22.5, Theorem 22.6, Corollary 22.7, and (22.1)–(22.25) pass. The conventional (12.9) coefficient for the abstract Horner/subtraction route is false; the exact generated-budget correction and counterexample are proved. | CORE-CLOSED / source correction |
| 23 | The four error theorems, conventional/Winograd/Strassen/bilinear/3M algorithms, cost recurrences, and (23.1)–(23.24) are connected to actual recursive rounded evaluators. | CORE-CLOSED |
| 24 | Theorems 24.1–24.3, (24.1)–(24.8), radix-2 FFT/bit reversal, inverse transform, and circulant solve have actual traces and explicit remainders. | CORE-CLOSED |
| 25 | (25.1)–(25.14), Newton/condition/stopping/eigenproblem exact content pass. Theorems 25.1–25.2 use an undefined approximation sign and “decreases until” and are precise defers. The `J=A` sign typo and false `2||A||` Lipschitz factor have proved corrections. | CORE-CLOSED / source corrections and precise defer |
| 26 | (26.1)–(26.8), literal AD/MDS producers, Cardano branches, and interval containment pass. The finite crude alternating-directions search implements the printed initial step, sign reversal, and 25 doublings and proves sweep monotonicity; both initial MDS simplexes have exact edge/orthogonality certificates. The Cardano division needs a nonzero branch; correction and counterexample are proved. The survey-style first-order (26.8) lacks a quantified family/remainder and is deferred. | CORE-CLOSED / source correction and precise defer |
| 27 | IEEE exceptional states, arithmetic/compiler/reproducibility issues, scaled norms and complex division have precise endpoints. Unconditional Smith overflow safety is false; scoped traces and a counterexample are proved. Blue's prose lacks a uniquely specified executable algorithm. | CORE-CLOSED / source correction and precise defer |
| 28 | Theorem 28.1, (28.1)–(28.11), Hilbert/Pascal/Vandermonde/Toeplitz/orthogonal/SPD/companion/random constructions pass. Printed Hilbert, Pascal, reciprocal-SPD scaling, and companion-normality errors have explicit counterexamples and corrected theorems. | CORE-CLOSED / source corrections |

## Cross-chapter bridge audit

| Bridge | Status |
|---|---|
| Ch. 1 Givens/QR overview ← Ch. 19 (19.35a) | CLOSED by `stewartLocalSensitivitySource_proved` at the dimension-uniform source quantifier order |
| Ch. 2 p. 50 tablemaker paragraph ← Hermite–Lindemann | CLOSED by the pinned/adapted upstream theorem, `higham2_real_exp_transcendental`, exact finite midpoint enumeration, positive separation, and the generic convergent-approximation comparison bridge |
| Ch. 3 product/norm estimates ↔ Ch. 6 spectral/Frobenius norm results | CLOSED by theorem imports |
| Ch. 7 conditioning → Ch. 8 triangular forward error | CLOSED |
| Ch. 8 Lemma 8.4 square-root use → Ch. 10 Problem 10.3 (pp. 197/211) | CLOSED by `higham10_problem10_3_anyOrder_sqrt`, retaining arbitrary evaluation order and the printed `gamma_(k+1)`/`gamma_(k-1)` counters |
| Ch. 8 triangular solves → Ch. 9 LU solve | CLOSED |
| Ch. 9.4 generic/row-pivoted/complete-pivoted solve → Ch. 12 (12.6)/(12.1) | CLOSED during this audit |
| Ch. 9 solver/refinement analysis → Ch. 12 Problem 12.2 and Appendix A | CLOSED by the exact two-step recurrence, residual-certificate forward transfer, and `SolverWBound`-to-existence endpoint in `HighamChapter12Problem12_2.lean` |
| Ch. 9.9 diagonal dominance ↔ later Ch. 13 facts | CLOSED by a direct cycle-breaking scalar proof |
| Ch. 10/11 factorization → shared solve substrate | CLOSED with explicit Chapter 11 corrections: literal rounded Algorithm 11.2 factors/middle solve/terminal bounds are produced; the computed-factor constant and Aasen accumulated-factor/coordinate defects have counterexamples and corrected endpoints |
| Ch. 13 SPD block bounds → Cholesky/condition-number substrate | CLOSED |
| Ch. 14 Method D → Ch. 8/9 triangular inverse and Doolittle LU | CLOSED |
| Ch. 14 p. 279 fast inversion link → Ch. 23 Problem 23.8 | CLOSED by the noncommutative block inverse, upper-triangular specialization, exact recurrence, and exponent bound in `Higham23Problem23_8.lean` |
| Ch. 15 → rectangular norm/duality calculus | CLOSED: the rectangular trace/duality substrate feeds both the actual Boyd source-domain local theorem and the printed global theorem |
| Ch. 16 (16.9) → Ch. 19 QR machinery | algebraic/successful suffix CLOSED; rounded real-Schur producer SOURCE-DEFERRED |
| Ch. 16 Hammarling body result → Problem 16.2 integral/Lyapunov proof | CLOSED by Hurwitz exponential decay, product integrability, the improper-integral Lyapunov identity, uniqueness, and the positive-definite solution; the PDF's insufficient bare PSD-to-SPD inference is separately refuted |
| Ch. 17 convergence → Problem 17.1 | CLOSED |
| Ch. 18 Theorem 18.1 → complex Jordan normal form | CLOSED |
| Ch. 19 Theorem 19.6 → later full-swap implementation housed with Ch. 20 | CLOSED and publicly reachable |
| Ch. 19 (19.37) → (19.13) + Zha (19.36) | CLOSED: `zhaColumnwiseSensitivity_proved` supplies (19.36), and `higham19_eq19_37_of_zha_and_formedQ` supplies the composition |
| Ch. 19 angle/CGS–MGS prose → Problems 19.9–19.10 | CLOSED: Problem 19.9 proves the literal two-column least-singular-value/angle condition bound; Problem 19.10 supplies staged actual CGS/MGS executors, the Lauchli defects and MGS pairwise bounds, the no-uniform-linear-CGS result, and the abstract-rounding-event discrepancy |
| Ch. 19/20 → Ch. 21 underdetermined systems | CLOSED |
| Ch. 5/12 → Ch. 22 Vandermonde/refinement | CLOSED |
| Ch. 22 p. 426 conditioning link → Problem 22.7 | CLOSED by exact Chebyshev zero/extrema matrices, finite trigonometric orthogonality, inverse/operator-norm facts, `kappa_2=sqrt 2` at zeros (`n≥1`), and the extrema bound `kappa_2≤2` |
| Ch. 3/6 → Ch. 23 fast multiplication | CLOSED |
| Ch. 3 → Ch. 24 FFT | CLOSED |
| Ch. 12 → Ch. 25 Newton linear-solve specialization | CLOSED |
| Ch. 2/6/12/15/16/23–25 → Ch. 27 software/exception analysis | CLOSED for the selected precise rows |
| Ch. 27 p. 500 `pythag` discussion → Problem 27.6 | CLOSED by the Halley specialization, scaled recurrence, exact invariant, monotone enclosure, and cubic-error identity/bound; the machine-dependent three-iteration stop remains empirical |
| Ch. 7/15/19 → Ch. 28 test-matrix conditioning/construction | CLOSED |

No publicly imported module was unreachable in the recursive import audit.

## Implemented during this audit

- `NumStability.Upstream.Lindemann/*` and `HighamChapter2Lindemann.lean`: a pinned-stack adaptation of mathlib4 PR #28013 with exact PR/commit provenance, the real Hermite–Lindemann specialization, unconditional finite-machine/midpoint exclusion, exact finite midpoint enumeration, positive separation, and eventual comparison stability for every supplied convergent approximation sequence.
- `Higham5FastPolynomialEvaluation.lean`: the printed quartic fast-evaluation identity and operation count, plus the source's strict `n>4` existence claim for fewer than `2n` operations.
- `Higham5PatersonStockmeyer.lean`: the p. 102 scalar-coefficient `m×m` complex matrix polynomial, a literal Paterson--Stockmeyer block-Horner evaluator, exact equality to P1, the exact `2⌊√n⌋` scheduled matrix-multiplication count, and the explicit `(⌊√n⌋+4)m² ≤ 5m²⌊√n⌋` live-storage bound for `n>0`.
- `HighamChapter6Duality.lean`: the dual-of-dual norm identity and the finite-dimensional evaluation functional attaining the double-dual norm, closing the Chapter 3/6 norm bridge at theorem level.
- `Higham11BunchKaufmanRoundedExecution.lean` through `Higham11BunchKaufmanRoundedTerminalClosedForm.lean`: a total literal rounded Algorithm 11.2 trace, flat accumulated factors, global residual, actual block middle solve, computed growth, source-coordinate terminal solve, dimension-only bounds, and explicit first-order-plus-quadratic remainder.
- `Higham11BunchKaufmanSourceCorrection.lean`, `AasenAdjacentPivotSourceResidualCh11Closure.lean`, and `AasenOriginalCoordinateCorrectionCh11.lean`: exact/computed-factor separation for Theorem 11.4, a counterexample to the printed Aasen accumulated-factor estimate, the unconditional minimum-norm actual DGTTRF/DGTTRS correction, and the corrected original-coordinate Aasen endpoint.
- `HighamChapter15BoydSourceDomain.lean`, `HighamChapter15BoydRowwiseDomain.lean`, `HighamChapter15BoydSourceSecondDerivative.lean`, and `HighamChapter15BoydSourceClosure.lean`: the actual derivative/second-variation calculation on the corrected source domain and the non-target-bearing uniform/subsequential local-linear Boyd terminals.
- Selected PDF links now have dedicated modules: Chapter 8 Lemma 8.4→Problem 10.3 (`Higham10Problem10_3.lean`), Chapter 9→Problem 12.2 (`HighamChapter12Problem12_2.lean`), Chapter 14→Problem 23.8 (`Higham23Problem23_8.lean`), Chapter 16 Hammarling→Problem 16.2 (`Higham16Problem16_2.lean`), Chapter 19 angle/CGS–MGS→Problems 19.9–19.10 (`Higham19Problem19_9.lean`, `Higham19Problem19_10.lean`), Chapter 22→Problem 22.7 (`Higham22Problem22_7.lean`), and Chapter 27→Problem 27.6 (`Higham27Pythag.lean`). Every listed bridge passed its focused build and representative axiom gate.
- `CompensatedSum.lean`: a uniform small-unit-roundoff bare-`FPModel` obstruction for the leading-`2u + C u²` interpretations of (4.8) and (4.9), plus explicit leading-`3u` corrected terminals. This is intentionally labeled a model-strength result.
- `Ch4KahanFiniteFamily.lean`: a coherent precision-parametric binary round-to-nearest-even trace, exact unit roundoff, all sixteen primitive rounding identities, and `forall C` counterexamples to both (4.8) and (4.9). Together with the leading-`3u` terminals, this gives the required discrepancy-and-correction disposition.
- `HighamChapter9ComputedCorrection.lean`: a concrete binary32 witness that rounded `U` is not the exact GEPP trace used by the printed proof maneuver, and a corrected theorem in terms of computed growth and computed multipliers.
- `HighamChapter9Theorem914Primitive.lean`: literal exact and rounded tridiagonal pivot/multiplier recurrences, an explicit data-dependent small-unit-roundoff budget, and a uniform arbitrary-positive-tolerance theorem proving finite-horizon pivot closeness, sign preservation, and nonbreakdown.
- `HighamChapter9Theorem914Actual.lean`: finite actual rounded factors and sparse bidiagonal solve executors; corrected (9.20)–(9.22) producers at `beta=u/(1-u)`; exact and actual source endpoints for every Theorem 9.12 class; sign-equivalence transport; the standard inverse-positive M-matrix correction; and formal bare-model counterexamples to the false coefficient/unrestricted clauses.
- `HighamChapter9Theorem914DiagDominant.lean`: source-only nonsingular row/column-diagonal-dominance producer for actual `16`-growth and the resulting small-`u` `16*h(u/(1-u))` solve bound, with no computed-growth premise.
- `Ch10Theorem107FailureVacuity.lean`: positive diagonal congruence makes the printed failure antecedent impossible; the generalized indefinite correction remains separately useful.
- `HighamChapter12Ch9GenericSolverBridge.lean`: generic, row-pivoted, and complete-pivoted LU backward-error certificates now produce the Chapter 12 solver weight in original coordinates.
- `Higham11BunchKaufmanActualSelector.lean`: actual first-stage finite argmax, symmetric permutation, case split, and selected two-by-two solve bridge for Algorithm 11.2.
- `Higham11SkewActualSelector.lean`: actual first-stage skew pair argmax/permutation and local selection facts for Algorithm 11.9.
- `Higham11SkewSourceCorrection.lean`: a nonsingular 4×4 actual-selector counterexample to Algorithm 11.9's printed unit-multiplier inference, a complete-pivot correction, and a coupled local Schur proof that preserves the valid `3 M` growth estimate without the false premise.
- `Higham11SkewExactTrace.lean`: the actual recursive Algorithm 11.9 no-action/selected-two-by-two skew-Schur trace, nonzero-pivot and skew invariants, exact stage accounting, corrected coupled `3 M` recurrence, and both path-specific and printed global growth bounds.
- `PNormPowerMethodRect.lean`: source-dimensional rectangular Algorithm 15.1 trace/step/stop model and rectangular Lemma 15.2 for general dual pairs and concrete endpoint norms.
- `Higham11BunchKaufmanExactTrace.lean`: an actual recursive exact Algorithm 11.2 active-Schur trace, structurally terminating pivot-width schedule, symmetric-permutation preservation, scalar/two-by-two pivot nonbreakdown, and a GEPP solve certificate for every selected two-by-two pivot under the displayed run domain.
- `Higham11BunchKaufmanRoundedBridge.lean`: source-valid residual, additive, and `(1+c u)` consequences of (11.5); actual selected-GEPP specializations with constant `36`; recursive case-(4) trace invariants; and a finite counterexample proving that the coefficient-one coupling in the current `FlMixedPivots` cannot follow from (11.5).
- `AasenAdjacentPivotOperationalMiddleCh11.lean`: canonical dense and row-sparse residual corrections for the actual adjacent-pivot DGTTRF/DGTTRS output; zero-output reflection and exact unconditional `AasenDirectMiddleBudget` objects under no-breakdown plus `gammaValid fp 3`; a no-dimension-loss sparse budget theorem from the literal pointwise source residual; a formal counterexample to the obsolete accumulated-factor interface; stored-multiplier, fresh-fill, completed-state, pivot-prefix, and source-row-label invariants; exact no-swap/swap factor-forward telescopes with local `u`/`gamma_2` error bounds and successor handoff; and the global Theorem 11.8 assembly under only the remaining scalar pathwise residual premise.
- `HighamChapter15BoydBridges.lean`: smooth-dual/gradient and unique normer identities; actual scalar-sequence convergence, stop/fixed-update equivalence, and positive-orbit preservation; continuity of the concrete `l^p` objective; strict Lyapunov/fixed-point structure of the actual update; construction of a local contraction radius and geometric rate from a derivative operator-norm bound; a compact strict-Lyapunov/unique-optimal-fixed-point convergence reduction; and, from the printed global matrix hypotheses, a compact invariant carrier, actual-update continuity, a strictly positive maximizing fixed point, and exact identification of its value with the complex induced `opP`.
- `HighamChapter15BoydUniqueness.lean`: the rowwise strict-Jensen tangent inequality and equality-ratio case; supporting-simplex maximality of every positive normalized fixed point; irreducible-Gram propagation of equality ratios; uniqueness on the normalized positive carrier; and the literal global convergence endpoint `higham15_boyd_global_of_nonnegative_irreducibleGram` from the printed hypotheses.
- `HighamChapter15BoydLocalStability.lean`: spectral-radius-to-finite-power stability, an explicit power-adapted seminorm with norm equivalence and contraction, nonlinear Fréchet-remainder absorption, the generic local geometric-convergence endpoint from a stable derivative power, and a nilpotent witness showing that contraction in the default norm is too strong.
- `MatrixPowersGautschi.lean`: corrected equation-(18.6) existential constant for the positive-spectral-radius Jordan case and a separate nilpotent eventual-zero theorem.
- `MatrixPowersLaszlo.lean`: an arbitrary-matrix Schur construction, universal nearest-normal lower bound, and an attaining normal witness.
- `MatrixPowersBaiDemmelGu.lean`: attained positive unit-circle inverse-resolvent radius, derived inner-circle resolvent estimate, both quoted power-bound branches, and the quoted bounds on `alpha_m`.
- `MatrixPowersBaiDemmelGuDistance.lean`: equality of the `CStarMatrix` norm with the ordinary complex operator 2-norm, attained singular and fixed-eigenvalue perturbation distances, the attained unit-circle perturbation minimum, and its exact identification with the Bai–Demmel–Gu stability radius.
- `MatrixPowersKreiss.lean`: the exact lower Kreiss inequality, Laurent/resolvent proof, the individual-power contour upper bound, and the printed finite-horizon `k<n` upper inequality.
- `MatrixPowersKreissSpijker.lean`: the exact source-traceable exterior-circle Spijker interface; internal derivative, derivative-continuity, and interval-integrability results for the rational resolvent curve; and a proved chain through integration by parts and Euclidean dualization to the all-power pointwise and literal two-sided Kreiss endpoints.
- `MatrixPowersSpijkerRational.lean`: an explicit adjugate numerator for each scalar resolvent coefficient, degree-`≤n` bounds for numerator and characteristic denominator, the rational evaluation identity, and exclusion of denominator zeros on every Kreiss exterior circle.
- `MatrixPowersSpijkerPlanar.lean`: the reflected-polynomial construction and degree-`≤2n` bound giving the exact finite crossing count for every nonconstant real projection level.
- `SpijkerProjectionIntegral.lean`: the exact directional integral `∫₀²π |Re(e^{-iθ}w)| dθ = 4||w||`.
- `MatrixPowersSpijkerPlanarAnalysis.lean`: Fubini projection averaging, the finite layer-cake/Banach-indicatrix variation bound, the sharp rational arc-length theorem, and `spijkerArcLengthBound_proved`.
- `MatrixPowersSpijkerClosure.lean`: unconditional pointwise and uniform power bounds and the literal upper and two-sided finite-dimensional Kreiss endpoints.
- `Higham19Sensitivity.lean`: a corrected dimension-only Stewart statement surface; normalized economy-QR factorization and Gram identities; an unconditional Frobenius quadratic majorant for `Delta R R^{-1}`; source-shaped Zha/Stewart forcing bounds; full `Delta Q` and `Delta R` recovery bounds; direct Penrose equations and exact norm identity for `R^{-1}Q^T`; upper-triangular/skew identities; and a proved (19.37) composition bridge. Statement surfaces are not misreported as producers.
- `Higham19SensitivityClosure.lean`: the constructive uniform positive-diagonal small branch `||Delta R R^{-1}||_F <= 6||Delta A R^{-1}||_F`, followed by the literal Stewart endpoint with coefficient `7` and the literal Zha endpoint with coefficient `7n` and local remainder coefficient `K=0`.
- `HighamChapter7Rectangular.lean`: source-dimensional rectangular versions of Theorems 7.1 and 7.3, including necessary, sufficient, and attaining perturbation directions.
- `Higham1014Equation1022.lean`: the literal truncated-Cholesky residual, exact matrix-2-norm leading coefficient in (10.22), and a quantified uniform family-level quadratic remainder derived from (10.21).
- `Higham13DemmelSharpMultiplier.lean`: Demmel's sharp SPD block-multiplier constant from an actual Loewner spectral interval and an explicit rational equality witness.
- `Ch14SchulzRectangular.lean` and `Ch14SchulzSpectralConvergence.lean`: the audited Chapter 14 branch's rectangular residual algebra, arbitrary-rank compact SVD/Moore–Penrose producer, and source-initialized pseudoinverse convergence.
- `Higham15Problem15_4.lean`: the audited Chapter 15 branch's honest two-sided `||U⁻¹||∞` bound with the exact `2^(n-1)` and `n` constants derived from partial-pivoting structure.
- `Higham15Problem15_6.lean`, `Higham15Problem15_6Closure.lean`, and `Higham15Problem15_6Operational.lean`: four actual inverse recurrences, literal stored factor vectors, two `List.Vector.scanl` passes, `List.Vector.map₂` output assembly, exact `|A⁻¹|d`/infinity-norm correctness, and exact/uniform linear operation counts.
- `Higham16VecPermutationNotes.lean`: the explicit vec-transpose commutation permutation and exact Kronecker intertwining identity.
- `Higham19SunBischof.lean`, `Higham19TurnbullAitken.lean`, and `Higham19PolarNearest.lean`: constructive triangular `I-Y S Yᵀ`, equal-norm rank-one unitary/orthogonal, and rank-tolerant nearest-polar results at the printed dimensions.
- `Higham26SourceSearch.lean`: the literal finite crude AD search, coordinate/sweep monotonicity, and exact right-angled/regular MDS simplex geometry.

All new public modules are imported by `NumStability/Algorithms.lean` once their focused builds pass.

## Remaining precise work

No selected, mathematically determinate Chapter 1–28 row remains open. The
four claims found by the final red-team pass—(10.22), rectangular Schulz
convergence, the Problem 15.6 producer/count, and Sun–Bischof triangular
`Y S Yᵀ`—all now have source-strength producers. The later same-pass findings
(Demmel attainability, the Chapter 16 commutation permutation, Turnbull–Aitken,
rectangular polar nearestness, and the Chapter 26 direct-search details) are
also closed.

The following are deliberate terminal scope boundaries, not hidden proof
gaps:

- Chapter 16's rounded real-Schur prefix is
  `SOURCE-DEFERRED / MISSING-PRECISE-ALGORITHM`: the PDF does not determine
  shifts, deflation, stopping, exceptional cases, a real-Schur output
  convention, or a rounded QR iteration. The exact algebra and supplied-Schur
  suffix, including Hammarling/Problem 16.2, are closed.
- Literature-review extensions in the notes—such as the square all-unitarily-
  invariant Fan–Hoffman extension, the Chandrasekaran–Ipsen comparison, and
  the Chu generalized-pencil result—are not in-book algorithm producers or
  downstream proof dependencies. They are recorded as literature/source
  boundaries under the skill rather than reconstructed from unspecified
  external machinery.
- Approximation signs, empirical tables/plots, machine-dependent iteration
  counts, open-ended research prompts, and prose that omits an operative
  algorithm or remainder semantics retain their chapter-specific
  `DEFER-*` classifications.

## Verification

Baseline before changes:

- `lake build`: passed, 4,443 jobs.
- Recursive public import audit: 608 of 608 modules reachable.
- No top-level `sorry`, `admit`, custom `axiom`, or unsafe/opaque placeholder declaration in the audited source modules. Existing intentional `native_decide` uses elsewhere are not confused with source-theorem proof gaps.

Final validation is recorded here after all focused work completes:

- `lake build NumStability.Algorithms.Higham5PatersonStockmeyer`: passed, 3123 jobs. The dedicated `Ch5PatersonStockmeyerAxiomAudit.lean` harness reports only `propext`, `Classical.choice`, and `Quot.sound` for the literal block-Horner correctness theorem, exact multiplication count, storage bound, and packaged p. 102 source claim; the exact storage formula needs only `propext`.
- `lake build NumStability.Algorithms.Sylvester.Higham16Problem16_2`: passed, 2894 jobs. The direct Lean compile and forbidden-marker scan also passed. The Hurwitz decay/integrability, integral uniqueness, SPD endpoint, and PSD-discrepancy endpoints report only `propext`, `Classical.choice`, and `Quot.sound`.
- `lake build NumStability.Algorithms.QR.Higham19Problem19_10`: passed, 3071 jobs, as did its direct Lean compile and forbidden-marker scan. The staged CGS/MGS executor, defect/bound, no-uniform-bound, and abstract-rounding-event discrepancy endpoints report only `propext`, `Classical.choice`, and `Quot.sound`.
- The expanded `SelectedProblemAxiomAudit.lean`, including Chapters 2, 10, 12, 16, 19, 22, 23, and 27, passed with only the standard imported principles on all audited endpoints.
- Chapter 9 Theorem 9.14 focused builds passed (`HighamChapter9Theorem914Actual`, 3047 jobs; `HighamChapter9Theorem914DiagDominant`, 3048 jobs), and the public `NumStability.Algorithms` build passed with 4417 jobs. The consolidated axiom harness reports only `propext`, `Classical.choice`, and `Quot.sound` for the new source-class, actual small-`u`, diagonal-dominance, and countermodel endpoints.
- `lake build NumStability.Algorithms.HighamChapter15BoydBridges`: passed, 3030 jobs. `FinalAxiomAuditAll.lean` prints the new Chapter 15 derivative, strict-Lyapunov, compact-dynamics, and source-facing global reduction endpoints with only `propext`, `Classical.choice`, and `Quot.sound`.
- Public umbrella `lake build NumStability.Algorithms`: passed, 4417 jobs, with `HighamChapter15BoydBridges.lean` imported by `NumStability/Algorithms.lean`.
- `lake build NumStability.Analysis.MatrixPowersKreissSpijker`: passed, 3013 jobs.
- Chapter 18 focused builds passed: `MatrixPowersSpijkerPlanarAnalysis`, 3028 jobs; `MatrixPowersSpijkerClosure`, 3029 jobs. A fresh endpoint harness reports only `propext`, `Classical.choice`, and `Quot.sound` for the projection average, crossing variation, analytic bridge, sharp rational arc length, proved Spijker interface, and all four unconditional Kreiss wrappers.
- Focused closure-module builds passed: Chapter 11 Aasen operational middle, 3090 jobs; Chapter 15 Boyd bridges, 3030 jobs; Chapter 18 Spijker closure, 3029 jobs; Chapter 19 QR sensitivity closure, 2997 jobs. The Chapter 9 focused builds are recorded above.
- A focused Chapter 19 axiom harness reports only `propext`, `Classical.choice`, and `Quot.sound` for `economyQR_scaledRVariation_frob_le_six_of_small`, `stewartLocalSensitivitySource_proved`, and `zhaColumnwiseSensitivity_proved`; the forbidden-marker scan over both Chapter 19 sensitivity modules is empty.
- The consolidated `FinalAxiomAuditAll.lean` harness passed all 343 endpoint checks. Every endpoint is axiom-free or reports only a subset of the standard imported principles `propext`, `Classical.choice`, and `Quot.sound`; no project-specific axiom appears.
- Final serial builds passed: `lake build`, 4622 jobs; `lake build NumStability.Analysis`, 3480 jobs; and `lake build NumStability.Algorithms`, 4529 jobs.
- Nested-comment/string-aware recursive public reachability: 708 of 708 Lean modules beneath `NumStability/` are reachable from `NumStability.lean` (709 of 709 when the root file is counted); the unreachable set is empty.
- The top-level forbidden-marker scan found no actual `sorry`, `admit`, custom `axiom`, or `opaque` declaration in `NumStability`; broad token hits were comments or documentation prose. Five `False.elim` uses in the final harness's imported Chapter 11 modules were inspected and are eliminations of definitionally impossible breakdown branches, not assumed contradictions. `git diff --check` passed with no whitespace errors; Git reported only LF-to-CRLF working-copy notices.

## Conclusion

The independent PDF-first audit is entitled to a Chapters 1–28 selected-core
closure claim. Every selected precise row has a source-strength producer or,
where the printed statement is false, a checked discrepancy plus a corrected
theorem. Cross-chapter dependencies are publicly reachable, and the requested
unmerged branches have been reconciled without importing their partial or
over-restricted claims. The remaining `DEFER-*` rows are source-imprecise,
empirical, research, optional, or literature-review boundaries identified by
the skill; they are not being represented as proved mathematics.
