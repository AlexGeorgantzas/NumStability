# Higham Chapters 1--28 -- fresh PDF-first source-strength audit (2026-07-21)

## Result

This audit re-read the 28 source PDFs and reconstructed the source inventory
before consulting the repository's coverage ledgers.  It uses **terminal** in
the precise sense defined below: a selected source claim is either proved at
source strength, refuted by a compiled counterexample and paired with a
faithful correction, or explicitly classified because the source does not
state a determinate proposition.  A terminal deferral is not represented as a
Lean proof of the words printed in the book.

The final build and hygiene results are recorded in [Verification](#verification).

## Frozen repository and source corpus

- Repository: `https://github.com/AlexGeorgantzas/lean-numerical-stability.git`
- Audited branch: `audit/ch1-28-full-2026-07-18`
- Remote baseline: `origin/main`
- Baseline commit: `2bb76d004b7dddd0e6dfb61f84c0be8e6816fa19`
- Source: Nicholas J. Higham, *Accuracy and Stability of Numerical
  Algorithms*, 2nd ed. (SIAM, 2002), Chapters 1--28
- Lean toolchain: `leanprover/lean4:v4.29.0-rc3`
- Mathlib revision: `e8ea1afc32790ce1d4e1a4e45cc412ba9388716b`
- Corpus: 28 PDFs, 513 PDF pages, 7,102,905 bytes
- SHA-256 of the 28 PDF byte streams concatenated in chapter order:
  `ad45eea4a5b197728cd00653a32d0b61bc009a2c35898d7dbe7e00f0ca7f362b`

The individual source fingerprints used by the audit are:

| Ch. | Pages | SHA-256 |
|---:|---:|---|
| 1 | 33 | `E8E16EFA50A6B85B42787AC5424AD9526190BA18206696D176DB3CAB464F9039` |
| 2 | 26 | `307D2C81A08FEE9F498C224DB78B91B1D0D085FC26BB3FFBB2386AD937737BB1` |
| 3 | 18 | `BF908CFE6BDF5F19464D3D4855610B51DCAFC10E7F0398C00CAAE61C3764FD9B` |
| 4 | 14 | `64AAEF2141406E2DEFC796B7D077CC7C10E37768B00402134C425D7BC5BCE94E` |
| 5 | 12 | `504DF359B0ADACFF8255DF6D165CF6D4BAD0C465A02BB86FA6851209FDF171E1` |
| 6 | 13 | `5FDF97E56EEA4CD3597D836B5F17BFD4992360E83D50408D70999EFE3FA4FB4A` |
| 7 | 19 | `14E70E41C8881F866003246B806BD116CA79F59AF3D3BF0B24A6D7FC8EBE24C2` |
| 8 | 18 | `5B576DB78237A0680D79A45152E0F6C3DC96EE99023E52579D97AC204949B028` |
| 9 | 37 | `8F03499D2E9FBBE2E00C39C39D90475A2AF7317097CFBBBA421F7880FB79010D` |
| 10 | 18 | `50CC14881F265B9C465AEFBDADF457C0671EF5C3470485C4EBA29F2BCDA722B4` |
| 11 | 17 | `F1AFC2C1DF7CE5956D315D3AFB38B27EDB39385E263669C6D6737877078D0079` |
| 12 | 14 | `9AA86285B2A3E0BC6DE4EAEADD63F40F479D3FDBEB319C43F7260A2F5E42A9B1` |
| 13 | 14 | `79288621182B53D5D444DA2D1F429BBBDC15D67B841B54B0518974A75BE73517` |
| 14 | 27 | `9D0FD43AE1C65E4A5618DB72175C73E81A81B17DB58B4E84271B9A87100B5C2A` |
| 15 | 18 | `94B5C7A57510CA3F694F3D2B4F30B131EB3377192CEA9591FDD71AF62218FF87` |
| 16 | 15 | `25A055375F21BB3DA029142D27A078F9F59041F13F7E13DA444FC93124FAC7C5` |
| 17 | 17 | `490C291ADDC3142EE32417A8D293B688C8A3AD0E0D54262207D7CC37A5B5D5C6` |
| 18 | 14 | `B899CBC826179B153C91C67AC9ABE6052374E6C8B26A34FFB1C95FC8203EE88C` |
| 19 | 28 | `04169BB8BFDA76A09BB831B45640D9BCCE6393D243D666B72BAE856D3F9C2B57` |
| 20 | 26 | `7CA85D5CAF3FFD5AE90FB315E9B4E00912E174881BCF969E7BA0A7B3CE9EC814` |
| 21 | 8 | `8EB1E7F71553F5CE1F8815F329F544C0B7EEAE261FB98CDE6A4EABCA6E3B6341` |
| 22 | 18 | `8769DDE6594809436213C55939FE9DD4100C0AB025A45CAC91BEC465DCA0CC5E` |
| 23 | 17 | `E3EC5DA214944FEFB5E8F276DE16D7FE139E5EA8750136298CE4E0A43A79FBC0` |
| 24 | 7 | `1D521873129DDF07737BF9DB2C166D003B8F1E37CEF3118303F53FB6E10935B1` |
| 25 | 11 | `E5534965F8A5AA8744021D446BA7F349D8DAEBC5C1D49B0090C51D2984E06A57` |
| 26 | 17 | `05860230052DEA6712277CAF32A58C98F39E06126B848CA00398CF26A3755693` |
| 27 | 21 | `54E3F7ECF6EF699CFEBD798E0917AE1E7841B4ECA2767B421083BA4F93D8F113` |
| 28 | 16 | `C3BE242C4E09A31099DA56E63FBA9E9CDC893AF1F1D85FE3FEBB43897DCBA972` |

## Independent inventory

Fresh extraction found:

- 165 distinct named body headings (`Theorem`, `Lemma`, `Corollary`, and
  `Algorithm`);
- 585 distinct numbered body-equation labels; and
- 597 numbered labels after adding the 12 labels that occur only in optional
  Problems: (6.23)--(6.24), (8.21), (13.26), (14.37), (19.38)--(19.40),
  (21.12)--(21.14), and (25.15).

This independently recovered Theorem 9.7, which an earlier planning inventory
had omitted, and corrected several body/problem boundary counts.  Equation
numbers in Lean identifiers were treated only as navigation aids: declaration
types and producers were inspected before a row was accepted.

## Audit gate

The repository's `chapter_splitting` policy was generalized from chapter-local
splitting to a repository-wide source-strength audit.  The following rules were
then applied uniformly.

1. Every precise selected named result, body equation, central mathematical
   prose claim, algorithm, and consumed Problem dependency needs a compiled
   source-level terminal result.
2. An implementation-facing theorem must start from the actual executor.  A
   caller-supplied residual, execution trace, growth estimate, pivot fact, or
   target-shaped certificate does not close the source row.
3. Hidden nonbreakdown, rank, conditioning, differentiability, dimensional,
   and smallness hypotheses must either be derived from the printed domain or
   appear explicitly as a qualified correction.
4. A false printed claim is terminal only when Lean checks a counterexample
   and an appropriately scoped corrected statement is supplied.
5. Undefined approximation symbols, unspecified algorithms, empirical
   assertions, and unquantified adjectives are classified explicitly rather
   than converted into invented propositions.
6. Problems are optional unless a selected body result consumes them.  A
   consumed Problem is promoted into the proof dependency surface.

Terminal classifications used below are:

- **SOURCE-CLOSED**: compiled at source strength;
- **SOURCE-DISCREPANCY**: a compiled counterexample plus a faithful correction;
- **DEFER-UNDEFINED-SOURCE**: the source does not determine a proposition;
- **DEFER-EXTERNAL-CITATION**: the chapter cites a result but does not provide
  enough proof or statement detail for an honest local reconstruction; and
- **OPTIONAL-PROBLEM-NOT-SELECTED**: outside core mode and not consumed.

## New defects found and repaired in this run

This rerun found source-strength or traceability defects not visible in the
previous headline audit.

### Chapter 5 -- literal complex Algorithm 5.1

`HighamChapter5ComplexAlgorithm51.lean` implements the actual rounded complex
Horner recurrence and proves its running backward/forward error.  In
particular, the local complex multiplication/addition step produces the
printed `sqrt 2 * gamma_2` scale instead of borrowing a real Horner theorem.

### Chapter 6 -- omitted precise norm prose

`Higham6Asides.lean` now proves that the Euclidean norm is not differentiable
at zero, gives its Fréchet derivative away from zero, and supplies genuine
equality cases for Hölder's inequality from power-profile/common-ray data.
`Higham6BlockAntidiag.lean` proves the printed block-antidiagonal induced
`p`-norm identity, including the conjugate-exponent swap, without assuming the
desired matrix norm formula.

### Chapter 8 -- Lemma 8.8 and Algorithm 8.13 source defects

`HighamChapter8Lemma88SourceDiscrepancy.lean` checks a two-by-two row-dominant
counterexample to the printed Lemma 8.8 inequality direction and retains the
corrected theorem.  Algorithm 8.13's literal pseudocode divides an
uninitialized `y_i`; the ledger now marks that row `DEFER-UNDEFINED-SOURCE` and
links the existing corrected recurrence and bound.

### Chapter 14 -- Schulz inverse iteration

`Ch14SchulzIteration.lean` formalizes the exact Schulz iterate, the left and
right residual-squaring identities, the closed form
`E_k = E_0^(2^k)`, the double-exponential norm estimate, residual convergence,
and convergence of the iterates to the inverse.  The source initialization
`X_0 = alpha A^T` is tied to the spectral smallness condition rather than
replaced by an assumed residual contraction.

### Chapter 15 -- convergence and finite termination prose

`HighamChapter15ConvergenceProse.lean` supplies the missing monotone bounded
`gamma_k` limit, compact-sphere subsequence, continuous-update fixed-limit and
concrete Euclidean stationary bridge, finite-label termination arguments for
the `p=1` and square `p=infinity` cases, and the exact rank-one Euclidean norm
behavior.  The printed assertion that the rank-one method reaches the answer
on its second step "whatever" the starting vector is is false for an allowed
dual selection; Lean records the counterexample and the corrected theorem for
a non-annihilated rank-one pairing.  The rectangular `p=infinity` count depends on the
row dimension, so the printed `n+1` count is not silently generalized beyond
the square model.  Boyd's strong-local linear-convergence and nonnegative-
irreducible global-convergence results are `DEFER-EXTERNAL-CITATION`.  The
unqualified general-`p` stationary-limit sentence is
`DEFER-UNDEFINED-SOURCE` because the chapter's set-valued dual choice at zero
does not specify the continuity/zero-case domain needed by that statement; the
compiled conditional and `p=2` corrections make the determinate content
explicit.

### Chapter 16 -- actual small-block Sylvester solve

`Higham16PivotedSmallBlocks.lean` implements option-valued complete-pivot
solvers for the 1-, 2-, and 4-dimensional vectorized blocks.  Successful
execution derives nonbreakdown and its operational residual budget; callers do
not supply a pivot sequence or target residual.  The chapter still does not
specify the rounded QR/real-Schur producer, shift/deflation policy, or its
"modest" constant, so that preceding phase remains
`DEFER-UNDEFINED-SOURCE` rather than being filled by an invented algorithm.

### Chapter 17 -- consumed Problem 17.1

Problem 17.1 is consumed by (17.8), (17.11), and (17.29), so it is not optional
under the audit gate.  `higham17_problem17_1` now derives entrywise absolute
summability of the matrix-power series and summability of the infinity norms
directly from `spectralRadius B < 1`.

### Chapter 18 -- precise external and undefined boundaries

The ledger now records the László nearest-normal bound, the Bai--Demmel--Gu
distance-to-instability power bound, and the Kreiss matrix theorem as
`DEFER-EXTERNAL-CITATION` instead of silently omitting them.  Equation (18.6)
is `DEFER-UNDEFINED-SOURCE` because its constant is not defined.  Theorem 18.2
also retains its explicit deferral because its statement depends on an
unquantified instruction to ignore `O(epsilon^2)` terms.

### Chapter 19 -- actual Householder bridges and hidden domains

The single-step Householder application theorem now begins with the actual
normalized reflector construction and actual `fl_householderApply` output.
The Chapter 19.6 route is promoted from the later least-squares development so
that the canonical Chapter 19 endpoint starts with the genuine full-swap
pivoted stored-QR execution and does not assume `StageDataReady` or
`StrongStageModel`.  The Theorem 19.5/19.14 source wrapper derives computed
diagonal nonbreakdown from the actual Theorem 19.4 factorization, a source left
inverse, and the printed conditioning/smallness domain.  Lemma 19.3's compact
stored sequence now has a chapter-facing actual producer and gamma-collapse
endpoint.

The rank-only operational reading of MGS Theorem 19.13 is false in the
repository's standard relative-error model.  `Higham19Alg12MGSNonbreakdown.lean`
constructs a full-rank `2 x 2` input and an admissible `FPModel` with `u=1/16`
whose actual second MGS pivot is zero, even though the routine gamma/model
smallness conditions hold.  The terminal correction is a source-facing
success-or-breakdown theorem plus the existing successful-run source-rate
certificate.  Deriving success from a stronger conditioning threshold would
strengthen that correction; it is not used to relabel the false rank-only
claim as proved.

### Chapter 22 -- equation (22.22) traceability

`higham22_eq22_22_four_node_six_factor` specializes the actual factor sequence
to the printed four-node, six-factor display.  The row no longer relies only on
a semantic statement that it is an immediate instance of Algorithm 22.2.

### Chapter 23 -- the small-entry Strassen example

`higham23_strassen_small_entry_example` instantiates the exact seven-product
arithmetic graph and verifies the order-one cancellation expression for the
printed identity/epsilon example.  The prose claim that a particular floating-
point error "will be of order `u/epsilon^2`" remains
`DEFER-UNDEFINED-SOURCE`: no rounding mode, values, inequality, or asymptotic
quantifiers are specified.

### Chapter 28 -- Hilbert determinant asymptotics

The exact determinant product and the existing leading-log limit are valid,
but the literal ratio-asymptotic surface in (28.2) is not.  The audit adds a
compiled contradiction from the exact product/central-binomial ratio and
retains the corrected leading-log theorem.  Equations (28.5)--(28.11) remain
`DEFER-UNDEFINED-SOURCE` because their approximate/random-matrix displays omit
the required convergence modes or quantitative errors; nearby exact
probability-law theorems remain source-closed.

## Explicit terminal deferrals

These are source boundaries, not unreported proof holes.

| Chapter/source | Classification | Reason |
|---|---|---|
| Ch. 8, literal Algorithm 8.13 | DEFER-UNDEFINED-SOURCE | The printed pseudocode divides an uninitialized `y_i`; the corrected initialized recurrence is formalized separately. |
| Ch. 12, qualitative envelopes and approximate Theorem 12.4 condition | DEFER-MISSING-PRECISE-STATEMENT | `approximately`, `lesssim`, dropped terms, and unparameterized `O(u^2)` do not define finite propositions; exact companions are proved. |
| Ch. 14, higher-order GJE clauses and general-`D` sentence | DEFER-MISSING-PRECISE-STATEMENT | The source does not parameterize its `O(u^2)` remainders or quantify “negligible effect”; all determinate operational and leading-coefficient content is proved. |
| Ch. 15, Boyd strong-local and global convergence prose | DEFER-EXTERNAL-CITATION | The two dynamics results are cited without their external proof development. |
| Ch. 15, general-`p` stationary-limit prose | DEFER-UNDEFINED-SOURCE | Set-valued dual choice at zero and the needed continuity/zero-case domain are not specified; conditional and `p=2` corrections are proved. |
| Ch. 16, rounded QR/real-Schur producer | DEFER-UNDEFINED-SOURCE | No concrete QR iteration, shifts, deflation rule, or value for the "modest" constant. |
| Ch. 18, (18.6) | DEFER-UNDEFINED-SOURCE | Constant in the displayed estimate is undefined. |
| Ch. 18, Theorem 18.2 | DEFER-UNDEFINED-SOURCE | Depends on an unquantified first-order/O(epsilon-squared) convention. |
| Ch. 18, three cited matrix-power theorems | DEFER-EXTERNAL-CITATION | External theorems are named but not developed locally. |
| Ch. 19, Theorem 12.4 prose and (19.19)--(19.21) “modest” functions | DEFER-MISSING-PRECISE-STATEMENT | The inherited prose uses undefined `approximately`/“small” relations, and the source does not specify the numerical functions or a rounded construction. |
| Ch. 20, (20.14) | DEFER-UNDEFINED-SOURCE | `c_{m,n}` and the comparison relation are undefined. |
| Ch. 23, p. 442 error-order prose | DEFER-UNDEFINED-SOURCE | Heuristic order statement lacks a fixed rounding execution and quantifiers. |
| Ch. 25, (25.8)--(25.9), Theorems 25.1--25.2 | DEFER-UNDEFINED-SOURCE | `approximately`, decrease/stopping language, and required thresholds are not defined. |
| Ch. 26, (26.8) | DEFER-UNDEFINED-SOURCE | First-order linearization omits differentiability and a remainder statement; conditional and affine interpretations are proved. |
| Ch. 27, Blue three-accumulator prose | DEFER-UNDEFINED-SOURCE | No executable threshold policy or quantitative error/safety theorem. |
| Ch. 28, (28.5)--(28.11) | DEFER-UNDEFINED-SOURCE | Approximate/random-matrix displays omit error terms or modes of convergence. |

## Chapter disposition

`TERMINAL` means that every selected row has one of the explicit terminal
classifications above.  It does not erase a printed-source discrepancy or
deferral.

| Ch. | Disposition | Fresh-audit note |
|---:|---|---|
| 1 | TERMINAL / SOURCE-CLOSED | Arithmetic principles and exact selected prose rechecked. |
| 2 | TERMINAL / SOURCE-CLOSED | Standard and no-guard models rechecked at the source domain. |
| 3 | TERMINAL / SOURCE-CLOSED | Dot products, arbitrary order, and no-guard bridge rechecked. |
| 4 | TERMINAL / SOURCE-CLOSED | Literal summation executors and selected bounds rechecked. |
| 5 | TERMINAL / SOURCE-CLOSED | Added literal complex Algorithm 5.1 execution and bound. |
| 6 | TERMINAL / SOURCE-DISCREPANCY | Added a compiled refutation of differentiability at zero, the corrected nonzero derivative, Hölder equality, and block-antidiagonal endpoints. |
| 7 | TERMINAL / SOURCE-DISCREPANCY | Existing same-`p` scaling correction rechecked. |
| 8 | TERMINAL / SOURCE-DISCREPANCY / DEFER | Added Lemma 8.8 refutation; literal Algorithm 8.13 is undefined. |
| 9 | TERMINAL / SOURCE-CLOSED | Fifteen named results, complete-pivot history, and complex domains rechecked. |
| 10 | TERMINAL / SOURCE-DISCREPANCY | Pivoted/complex Cholesky domain corrections rechecked. |
| 11 | TERMINAL / SOURCE-DISCREPANCY | Actual block solve and `n=1` correction rechecked. |
| 12 | TERMINAL / SOURCE-CLOSED / DEFER | Actual LU/refinement bridges rechecked; imprecise asymptotic prose remains explicit. |
| 13 | TERMINAL / SOURCE-CLOSED | Block LU rows and consumers rechecked. |
| 14 | TERMINAL / SOURCE-CLOSED / SOURCE-DISCREPANCY / DEFER | Added source-initialized Schulz convergence; GJE corrections rechecked; unparameterized higher-order prose remains explicit. |
| 15 | TERMINAL / SOURCE-DISCREPANCY / DEFER | Added convergence, finite termination, rank-one correction, and external classification. |
| 16 | TERMINAL / SOURCE-CLOSED / DEFER | Added actual complete-pivot block solve; unspecified Schur producer remains explicit. |
| 17 | TERMINAL / SOURCE-CLOSED | Promoted and proved consumed Problem 17.1. |
| 18 | TERMINAL / SOURCE-CLOSED / DEFER | Explicit undefined and external-citation boundary. |
| 19 | TERMINAL / SOURCE-CLOSED / SOURCE-DISCREPANCY / DEFER | Actual QR producers promoted; MGS rank-only nonbreakdown is refuted and corrected; undefined qualitative prose remains explicit. |
| 20 | TERMINAL / SOURCE-DISCREPANCY / DEFER | Actual least-squares routes rechecked; (20.14) remains undefined. |
| 21 | TERMINAL / SOURCE-DISCREPANCY | Underdetermined-system corrections rechecked. |
| 22 | TERMINAL / SOURCE-DISCREPANCY | Added literal (22.22) wrapper; corrected refinement route rechecked. |
| 23 | TERMINAL / SOURCE-CLOSED / DEFER | Added exact small-entry instance; heuristic error-order prose remains undefined. |
| 24 | TERMINAL / SOURCE-CLOSED | Literal FFT/circulant executors and Chapter 9 bridge rechecked. |
| 25 | TERMINAL / SOURCE-DISCREPANCY / DEFER | Exact identities and corrections proved; approximate named claims remain undefined. |
| 26 | TERMINAL / SOURCE-DISCREPANCY / DEFER | Exact AD graph closed; zero branch corrected; (26.8) remains undefined. |
| 27 | TERMINAL / SOURCE-DISCREPANCY / DEFER | Smith correction and safety scopes rechecked; Blue prose remains undefined. |
| 28 | TERMINAL / SOURCE-DISCREPANCY / DEFER | Literal ratio asymptotic refuted; leading-log and precise probability laws retained. |

## Inter-chapter bridge audit

The 60 exact earlier-label producer-to-consumer chapter pairs recovered from
the bodies were checked at declaration type and producer level:

```text
2->3  2->4  2->5  3->5  6->7  2->8  3->8  7->8  3->9  7->9  8->9
3->10  6->10  7->10  8->10  9->10
9->11
3->12  7->12  9->12
9->13  10->13
3->14  6->14  7->14  8->14  9->14
6->15  7->15  8->15  9->15
7->16  8->16  15->16
7->17
3->19  6->19  8->19  12->19  13->19
7->20  10->20  12->20  19->20
7->21  19->21  20->21
2->22  3->22  5->22  12->22
3->23
3->24
7->25
9->26  15->26
2->27  15->27
8->28  15->28
```

The audit separately checked prose/problem dependencies that this exact-label
graph does not expose.  The material changes in this run were the literal
complex Chapter 5 producer, Chapter 17 Problem 17.1 as a consumed dependency,
Chapter 19's actual Householder producer/domain bridges, and equation-specific
Chapter 22/23 wrappers.  No selected consumer is accepted merely because a
semantically related theorem exists elsewhere.

## Hidden-hypothesis findings

- Actual rounded algorithms are separated from exact algebraic suffixes.
  Successful option-valued execution is used where nonbreakdown cannot be
  unconditional.
- Source rank plus a quantitative perturbation threshold is used to derive
  computed nonsingularity when the theorem needs it.  Where rank alone does
  not force actual MGS nonbreakdown, the repository supplies a compiled
  counterexample and a success-or-breakdown correction rather than advertising
  a bare `hpivot` theorem as rank-only source closure.
- Rectangular dimensions matter in the Chapter 15 infinity-norm termination
  count; the row and column label sets are not conflated.
- The Chapter 19 rowwise QR theorem's old `StageDataReady` route remains useful
  internally but is not the canonical source-facing endpoint.
- A near-singular Sylvester block cannot have an unconditional useful rounded
  error bound in the abstract `FPModel` without conditioning/nonbreakdown; the
  executable theorem therefore reports success and derives its obligations.
- First-order and asymptotic prose is not silently strengthened into an exact
  finite theorem.

## Verification

The final checks were run only after all proof-writing lanes had stopped.

- Focused builds passed for all 12 new Lean modules and their changed import
  consumers.  The Chapter 15/19 source-strength bridge replay also passed.
- A root-owned full `lake build` completed successfully: **4,443 jobs**, exit
  code 0.  Its output contained lint warnings but no build errors.
- An audit harness imported `NumStability.Algorithms` and ran `#print axioms`
  on 23 new or source-critical endpoints spanning Chapters 5, 6, 8, 14--17,
  19, 22, 23, and 28.  Every endpoint depended only on
  `[propext, Classical.choice, Quot.sound]`.
- Import-graph traversal from `NumStability.Algorithms` reached **561 of 608**
  Lean modules.  The 47 modules outside that umbrella are all deliberately
  standalone `NumStability.Analysis.*` modules or `NumStability.FloatingPoint`;
  no `NumStability.Algorithms.*` module was unreachable, and all 12 new audit
  modules were reachable.
- A declaration-line scan over the entire `NumStability/**/*.lean` tree found
  no `sorry`, `admit`, global `axiom`, `opaque`, or unsafe theorem/definition
  declaration.
- `git diff --check` passed.
- The final `git fetch origin main` used
  `https://github.com/AlexGeorgantzas/lean-numerical-stability.git` and left
  both `HEAD` and `origin/main` at
  `2bb76d004b7dddd0e6dfb61f84c0be8e6816fa19`.  Thus no remote-tracked path
  required a content merge or a local-over-remote conflict decision.
