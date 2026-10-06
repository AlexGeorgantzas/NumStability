# Higham Parallel Formalization Blueprint

This is the shared planning document for the four-person parallel formalization.
It is based on a first pass over PDFs `ch01` through `ch28` and Appendix A,
followed by a second pass against the extracted section/label/equation index.

The clean location index is `planning/chapter_index.md`.  That file is the
location ledger: section titles, primary theorem-like labels, local numbered
equations, and problem/Appendix-A solution numbers.  Use the PDFs themselves as
the source of truth for the exact statements.

## Scope

Formalize these items:

- Main definitions, notation, and data structures used later: floating point
  systems, rounding model, error measures, condition numbers, norms, factorizations,
  residuals, structured matrices, and algorithm outputs.
- Every primary `Theorem`, `Lemma`, `Corollary`, and `Algorithm` listed in
  `planning/chapter_index.md`.
- Numbered equations that define reusable objects, recurrences, algorithms,
  perturbation models, or error bounds.  Equations used only as local arithmetic
  in an example can be formalized inside that example's proof rather than exported.
- Problems and Appendix A solutions when they prove a main-text result, are cited
  by a main proof, or provide a reusable lemma.  Research-problem exercises are
  not required for the end-to-end library unless a later proof uses them.

Do not spend formalization time on historical notes, prose-only warnings,
MATLAB timing tables, figures, or numerical experiments unless they are needed
as named examples or counterexamples.

## Contract Mechanism

Every reusable result gets a contract before implementation.  Use this contract
shape in the theorem prover, issue tracker, or a local markdown ledger:

- `id`: stable name, for example `H03.Lemma3_1.gamma_product`,
  `H08.Alg8_1.back_substitution`, `H16.Eq16_15.sylvester_backward_error`.
- `source`: chapter, section, PDF page, and label/equation number.
- `owner`: one split number.
- `kind`: definition, algorithm spec, theorem, lemma, corollary, equation, example.
- `statement`: exact formal signature and conclusion, paraphrased in the ledger
  and exact in the formal code.
- `dependencies`: contract IDs used in the proof.
- `status`: `interface`, `placeholder`, `implemented`, `merged`, or `retired`.

Placeholder rule:

- A split may use a temporary placeholder only for a contract owned by another
  split, and only with the exact statement agreed in the shared contract.
- A split must not reprove or locally redefine another split's owned result.
- In Lean-like systems, put temporary axioms/constants only in interface files,
  not inside proof files.  The final merge must have no remaining nontrusted
  placeholders, `sorry`s, or local axioms.
- If a proof needs a result from a later chapter in the same split, implement the
  later result first or place it in the split's own internal interface.  If a
  proof needs a later chapter from another split, use the shared contract.

Recommended namespace tiers:

- `Higham.Core`: Chapters 1-6.  Arithmetic model, error calculus, summation,
  polynomials, norms, SVD basics.
- `Higham.Linear`: Chapters 7-14.  Linear systems, triangular solves, LU,
  Cholesky, symmetric indefinite factorizations, refinement, block LU, inverse.
- `Higham.Structured`: Chapters 15-19.  Condition estimation, Sylvester equations,
  stationary iteration, matrix powers, QR.
- `Higham.Applications`: Chapters 20-28.  Least squares, underdetermined systems,
  Vandermonde systems, fast algorithms, FFT, nonlinear equations, automatic error
  analysis, software issues, test matrices.

## Four Splits

| Split | Chapters | Approx. PDF pages | Main responsibility |
| --- | --- | ---: | --- |
| 1 | 1-6 and Appendix A solutions 1.x-6.x | 116 | Foundations: floating point model, gamma calculus, summation, polynomials, norms |
| 2 | 7-12 and Appendix A solutions 7.x-12.x | 123 | Linear system perturbation, triangular solves, LU, Cholesky, LDLT, refinement |
| 3 | 13-19 and Appendix A solutions 13.x-19.x | 133 | Block/inverse/condition-estimation, Sylvester, iteration, matrix powers, QR |
| 4 | 20-28 and Appendix A solutions 20.x-28.x | 141 | LS/underdetermined systems, Vandermonde, fast algorithms, FFT, nonlinear, testing/software/test matrices |

This is intentionally contiguous and dependency-aware.  Split 1 exports the
largest number of foundations, but has fewer later specialized algorithms.
Split 4 has more pages but many are software/test-matrix material rather than
dense theorem chains.

## Split 1 Ledger: Chapters 1-6

Exports:

- Floating point and error vocabulary: `fl`, unit roundoff `u`, absolute/relative
  error, componentwise error, forward/backward/mixed error, conditioning,
  cancellation, stable reformulations, and sample-variance formulas.
- Floating point systems: normalized/subnormal numbers, rounding maps, arithmetic
  models `(1+δ)`, weaker no-guard models, IEEE features, exact subtraction, FMA,
  elementary-function accuracy assumptions.
- Gamma/theta calculus: products and quotients of `(1+δ)` terms, `γ_n`, first-order
  and simplified bounds, complex arithmetic error model.
- Basic arithmetic kernels: inner products, outer products, matrix-vector and
  matrix-matrix multiplication, running error bounds, recursive/pairwise and
  compensated summation, Horner and derivative evaluation.
- Norm infrastructure: vector/matrix norms, induced norms, dual norms, monotone
  and absolute norms, norm equivalence, SVD, condition numbers, distance to
  singularity.

Key primary labels:

- Ch1: Lemma 1.1.
- Ch2: Lemma 2.1; Theorems 2.2-2.5.
- Ch3: Lemmas 3.1, 3.3-3.9; Algorithm 3.2.
- Ch4: Algorithms 4.1-4.3.
- Ch5: Algorithms 5.1-5.2.
- Ch6: Theorems 6.2, 6.4, 6.5; Lemmas 6.3, 6.6.

Internal order:

1. Formalize general algebra/norm preliminaries needed by Ch3 and Ch6.
2. Formalize floating point model and rounding theorems from Ch2.
3. Formalize gamma/theta calculus from Ch3.
4. Formalize arithmetic kernels, summation, Horner, and norms.

Known outward dependencies:

- Ch1's QR example references QR stability results from Ch19.  Treat this as an
  illustrative cross-reference.  If formalized as a theorem, use Split 3 contract
  `H19.Theorem19_10.givens_qr_backward_error`.
- Ch3 mentions norm results from Ch6.  Because both are in Split 1, implement the
  required Ch6 norm lemmas before closing the Ch3 matrix bounds.

## Split 2 Ledger: Chapters 7-12

Imports from Split 1:

- `H01-H03` error model, gamma/theta lemmas, componentwise inequalities.
- `H06` norm, SVD, dual norm, monotone/absolute norm, and condition-number tools.

Exports:

- Normwise and componentwise backward errors for linear systems; Oettli-Prager,
  Rigal-Gaches, perturbation and condition-number bounds.
- Scaling results for condition minimization and practical error bounds.
- Triangular solve algorithms, substitution backward and forward error bounds,
  inverse comparison matrices, fan-in algorithm.
- LU factorization existence, Doolittle algorithm, GE error analysis, pivot growth,
  diagonal/banded/tridiagonal special cases, sensitivity of LU.
- Cholesky/SPD/PSD factorization, Cholesky error bounds, Schur complement
  perturbations, positive-definite symmetric-part material.
- Symmetric indefinite block `LDL^T`, Bunch-Parlett, Bunch-Kaufman, rook pivoting,
  tridiagonal symmetric pivoting, Aasen, skew-symmetric variant.
- Mixed and fixed precision iterative refinement and stability after refinement.

Key primary labels:

- Ch7: Theorems 7.1-7.8; Corollary 7.6; Lemma 7.9.
- Ch8: Algorithm 8.1, Algorithm 8.13; Lemmas 8.2, 8.4, 8.6, 8.8, 8.9;
  Theorems 8.3, 8.5, 8.7, 8.10, 8.12, 8.14; Corollary 8.11.
- Ch9: Theorems 9.1, 9.3-9.5, 9.8-9.15; Lemma 9.6; Algorithm 9.2.
- Ch10: Theorems 10.1, 10.3-10.9, 10.14; Algorithm 10.2;
  Lemmas 10.10-10.13.
- Ch11: Algorithms 11.1, 11.2, 11.5, 11.6, 11.9; Theorems 11.3, 11.4, 11.7, 11.8.
- Ch12: Theorems 12.1-12.4.

Cycle breaker:

- Ch9 states diagonal-dominance results that the prose derives from the later
  block diagonal-dominance theory in Ch13.  Do not make Ch9 depend on Split 3 for
  this.  Split 2 should prove the scalar diagonal-dominance case directly or
  factor an elementary scalar lemma that Split 3 later generalizes.

## Split 3 Ledger: Chapters 13-19

Imports from Split 1:

- Floating point model, gamma/theta calculus, norms, SVD, matrix multiplication
  and product perturbation lemmas.

Imports from Split 2:

- Linear system perturbation, triangular substitution, LU/GE, Cholesky/SPD, LDLT,
  iterative refinement.

Exports:

- Partitioned, block, and recursively partitioned LU algorithms and block LU
  error analysis.
- Block diagonal dominance and SPD block Schur complement lemmas.
- Matrix inverse residual analysis, triangular inverse methods, Gauss-Jordan
  elimination and its special-case bounds.
- Condition estimation algorithms: p-norm power method, LAPACK 1-norm estimator,
  LINPACK estimator, tridiagonal condition-number theorems.
- Sylvester and Lyapunov equations: Kronecker/vec formulation, Schur method,
  backward-error formula, residual/backward-error relationship, condition number,
  practical bounds.
- Stationary iterative methods: forward, backward, componentwise, singular-system,
  and stopping-rule error skeletons.
- Matrix powers: exact-power decomposition, finite precision power bounds,
  pseudospectral application to stationary iteration.
- QR: Householder, Givens, classical and modified Gram-Schmidt algorithms and
  their backward/stability theorems.

Key primary labels:

- Ch13: Algorithms 13.1, 13.3, 13.4; Theorems 13.2, 13.5-13.8;
  Lemmas 13.9, 13.10.
- Ch14: Lemmas 14.1-14.3; Algorithm 14.4; Theorem 14.5; Corollaries 14.6, 14.7.
- Ch15: Algorithms 15.1, 15.3-15.5; Lemma 15.2; Theorems 15.6-15.9.
- Ch16: no primary theorem labels, but equations (16.1)-(16.30) define reusable
  Sylvester/Lyapunov objects and bounds.  Treat section-level results as contracts.
- Ch17: no primary theorem labels, but equations (17.1)-(17.35) define the
  stationary-iteration error analysis and should become section-level contracts.
- Ch18: Theorems 18.1, 18.2.
- Ch19: Lemmas 19.1-19.3, 19.7-19.9; Theorems 19.4-19.6, 19.10, 19.13;
  Algorithms 19.11, 19.12.

Internal order:

1. Implement Ch13 and Ch14 after importing Split 2 LU/triangular material.
2. Implement Ch15 condition-estimation algorithms and tridiagonal results.
3. Implement Ch19 QR core early enough for Ch16 and Split 4.
4. Close Ch16-Ch18 structured/iterative material.

Known outward dependencies:

- Split 4's least-squares chapters require Ch19 QR contracts immediately.
  Export `H19.Theorem19_4.householder_qr_backward_error`,
  `H19.Theorem19_10.givens_qr_backward_error`, and
  `H19.Theorem19_13.mgs_qr_bounds` first.

## Split 4 Ledger: Chapters 20-28

Imports from Split 1:

- Floating point model, gamma/theta calculus, norms, SVD, polynomial tools,
  summation and matrix multiplication kernels.

Imports from Split 2:

- Linear-system perturbation, triangular solves, GE/LU/Cholesky, refinement.

Imports from Split 3:

- QR, matrix powers, condition estimation, inverse/GJE, Vandermonde preliminaries
  as needed.

Exports:

- Least squares perturbation, QR/MGS/normal-equation/seminormal-equation methods,
  iterative refinement for LS, normwise backward error, weighted LS, equality
  constrained LS, generalized QR.
- Underdetermined systems and minimum-norm solution perturbation/backward error.
- Vandermonde and Vandermonde-like systems: inversion algorithms, Björck-Pereyra
  style stability, residual bounds, extended Clenshaw recurrence.
- Fast algorithms: Winograd inner product, Strassen, bilinear noncommutative
  algorithms, 3M method.
- FFT: Cooley-Tukey factorization, FFT forward error, circulant systems.
- Nonlinear systems: finite precision Newton method, limiting residual accuracy,
  conditioning, stopping tests.
- Automatic error analysis: direct search methods, interval analysis, and examples
  tied to GE growth, condition estimators, fast inversion, and cubic roots.
- Software issues: IEEE exploitation, arithmetic parameter tests, portability,
  underflow/overflow-safe kernels, multiple/mixed precision.
- Test matrices: Hilbert/Cauchy/Pascal/Toeplitz/companion/random/randsvd matrices.

Key primary labels:

- Ch20: Theorems 20.1-20.5, 20.7-20.10; Lemmas 20.6, 20.11.
- Ch21: Theorems 21.1, 21.3, 21.4; Lemma 21.2.
- Ch22: Algorithms 22.1-22.3, 22.8; Theorems 22.4, 22.6;
  Corollaries 22.5, 22.7.
- Ch23: Theorems 23.1-23.4.
- Ch24: Theorems 24.1-24.3.
- Ch25: Theorems 25.1, 25.2.
- Ch26: no primary theorem labels; treat direct-search algorithms, convergence
  tests, interval arithmetic, and example objective functions as section contracts.
- Ch27: no primary theorem labels; formalize reusable IEEE/software predicates,
  model assumptions, and underflow/overflow-safe algorithms as definitions and
  executable/spec contracts.
- Ch28: Theorem 28.1 and definitions/properties of test matrices.

Integration responsibility:

- Split 4 owns the final `NoPlaceholders` audit because it imports the largest
  upstream surface.  This is not ownership of other splits' proofs; it is the
  final merge check that all temporary interfaces have been replaced by real
  theorems.

## Chapter Skeleton

For exact section/page labels see `planning/chapter_index.md`.

### Chapter 1: Principles of Finite Precision Computation

Formalize notation for real/complex matrices and vectors, `fl`, unit roundoff,
absolute/relative/componentwise error, forward/backward/mixed error, conditioning,
cancellation, stable formula transformations, sample variance formulas, and the
linear-system residual/backward-error lemma.  Main reusable result: Lemma 1.1.
Appendix A supplies proofs or worked results for Problems 1.1-1.10, especially
sample variance and stable elementary formula exercises.

### Chapter 2: Floating Point Arithmetic

Formalize floating point systems, normalized/subnormal numbers, rounding maps,
unit roundoff, arithmetic models, IEEE special values, guard-digit and exact
subtraction properties, FMA contracts, and elementary-function assumptions.
Primary reusable results are Lemma 2.1 and Theorems 2.2-2.5.  Appendix A
solutions 2.x close proofs of Lemma 2.1, Theorem 2.3, gradual underflow facts,
FMA exact residuals, and convergence tests.

### Chapter 3: Rounding Error Analysis

Formalize inner/outer product error analysis, gamma/theta notation, running
error analysis, matrix-vector/matrix-matrix error bounds, complex arithmetic,
matrix product perturbation lemmas, and rank-one update error bounds.  Primary
contracts are Lemmas 3.1, 3.3-3.9 and Algorithm 3.2.

### Chapter 4: Summation

Formalize recursive summation, pairwise/fan-in style summation, compensated and
doubly compensated summation algorithms, exact correction property, forward and
backward summation bounds, and statistical estimates as optional non-core
material.  Primary contracts are Algorithms 4.1-4.3.

### Chapter 5: Polynomials

Formalize Horner evaluation, running Horner error bound, derivative evaluation
algorithm, Newton interpolation/divided differences, Leja ordering specification,
and matrix-polynomial variants.  Primary contracts are Algorithms 5.1 and 5.2.

### Chapter 6: Norms

Formalize vector p-norms, dual norms, absolute/monotone norms, induced matrix
norms, norm equivalence constants, matrix condition numbers, distance to
singularity, matrix p-norm comparisons, SVD, and auxiliary norm lemmas used by
later matrix bounds.  Primary contracts are Theorems 6.2, 6.4, 6.5 and Lemmas
6.3, 6.6.

### Chapter 7: Accuracy and Stability of Linear Systems

Formalize normwise and componentwise backward errors, residual formulas,
forward-error perturbation bounds, condition numbers, diagonal scaling
minimization results, inverse perturbation, numerical stability definitions, and
practical error estimators.  Primary contracts are Theorems 7.1-7.8, Corollary
7.6, and Lemma 7.9.

### Chapter 8: Triangular Systems

Formalize back substitution, order-independent substitution bounds, triangular
condition measures, special forward-error bounds, comparison matrices for inverse
bounds, and the parallel fan-in algorithm.  Primary contracts are Algorithms
8.1 and 8.13, Lemmas 8.2/8.4/8.6/8.8/8.9, Theorems 8.3/8.5/8.7/8.10/8.12/8.14,
and Corollary 8.11.

### Chapter 9: LU Factorization and Linear Equations

Formalize GE, partial/complete/rook pivoting, LU existence and uniqueness,
Doolittle algorithm, GE backward error, growth factor bounds, special classes
such as diagonal dominance, banded and tridiagonal matrices, scaling and pivoting
strategy material, a posteriori tests, and LU sensitivity.  Primary contracts are
Theorems 9.1, 9.3-9.5, 9.8-9.15; Lemma 9.6; Algorithm 9.2.

### Chapter 10: Symmetric Positive Definite Systems

Formalize SPD/PSD matrices, Cholesky existence and algorithm, Cholesky backward
and forward error, success/failure criteria, Cholesky perturbation theory, Schur
complement perturbations, complete pivoting for PSD matrices, and matrices with
positive definite symmetric part.  Primary contracts are Theorems 10.1, 10.3-10.9,
10.14; Algorithm 10.2; Lemmas 10.10-10.13.

### Chapter 11: Symmetric Indefinite and Skew-Symmetric Systems

Formalize block `LDL^T`, 1-by-1 and 2-by-2 pivots, Bunch-Parlett, Bunch-Kaufman,
rook pivoting, tridiagonal symmetric factorization, Aasen's method, and the
skew-symmetric pivot strategy.  Primary contracts are Algorithms 11.1, 11.2,
11.5, 11.6, 11.9 and Theorems 11.3, 11.4, 11.7, 11.8.

### Chapter 12: Iterative Refinement

Formalize solver/residual assumptions, mixed and fixed precision refinement,
one-step refinement stability, componentwise residual computation, and conditions
under which refinement implies stability.  Primary contracts are Theorems
12.1-12.4.

### Chapter 13: Block LU Factorization

Formalize partitioned, block, and recursive LU algorithms, block LU existence,
block Schur complements, block diagonal dominance, block LU error bounds, and
SPD block bounds.  Primary contracts are Algorithms 13.1, 13.3, 13.4; Theorems
13.2, 13.5-13.8; Lemmas 13.9, 13.10.

### Chapter 14: Matrix Inversion

Formalize inverse residual notions, triangular inverse methods, block inverse
methods, inverse by LU, Gauss-Jordan elimination, GJE error bounds, special SPD
and diagonally dominant cases, parallel inversion and Hyman's method as needed.
Primary contracts are Lemmas 14.1-14.3, Algorithm 14.4, Theorem 14.5, and
Corollaries 14.6-14.7.

### Chapter 15: Condition Number Estimation

Formalize componentwise condition estimation, p-norm power method, LAPACK
1-norm estimator, block estimator, LINPACK estimator, randomized Dixon bound,
and tridiagonal condition-number formulas.  Primary contracts are Algorithms
15.1, 15.3-15.5; Lemma 15.2; Theorems 15.6-15.9.

### Chapter 16: The Sylvester Equation

Formalize the Sylvester equation, Kronecker/vec conversion, eigenvalue
nonsingularity condition, Schur and Hessenberg-Schur methods, normwise backward
error, residual/backward-error implications, SVD-based backward-error formula,
condition number, Lyapunov equation specialization, and practical error bounds.
There are no primary labels; use equations and section-level results as contracts.

### Chapter 17: Stationary Iterative Methods

Formalize stationary iteration splittings, forward error recurrence, Jacobi and
SOR specializations, normwise and componentwise limiting error bounds, singular
system background and error recurrences, and stopping tests.  There are no primary
labels; use equations and section-level results as contracts.

### Chapter 18: Matrix Powers

Formalize exact matrix-power behavior via Jordan/decomposition tools, finite
precision matrix-power recurrences, sufficient conditions for computed powers to
tend to zero, pseudospectral criteria, and application to stationary iteration.
Primary contracts are Theorems 18.1 and 18.2.

### Chapter 19: QR Factorization

Formalize Householder transformations, computed Householder vectors, sequence
of transformations, Householder QR backward error, column pivoting row-wise
stability, aggregated Householder transformations, Givens rotations, iterative
refinement with QR, CGS/MGS algorithms, MGS stability, and QR sensitivity.
Primary contracts are Lemmas 19.1-19.3, 19.7-19.9; Theorems 19.4-19.6, 19.10,
19.13; Algorithms 19.11, 19.12.

### Chapter 20: Least Squares Problems

Formalize LS perturbation theory including Wedin's theorem, componentwise LS
perturbation, QR/MGS/normal-equation/seminormal-equation solution methods,
iterative refinement, LS backward error, weighted LS, equality constrained LS,
generalized QR, and Wedin proof lemma.  Primary contracts are Theorems 20.1-20.5,
20.7-20.10 and Lemmas 20.6, 20.11.

### Chapter 21: Underdetermined Systems

Formalize minimum-norm solution methods, perturbation bounds for underdetermined
systems, normwise backward error for minimum-norm solutions, and the Q method
error analysis.  Primary contracts are Theorems 21.1, 21.3, 21.4 and Lemma 21.2.

### Chapter 22: Vandermonde Systems

Formalize Vandermonde and confluent/Vandermonde-like matrices, inverse
construction, dual and primal algorithms, orthogonal-polynomial recurrences,
forward and residual error bounds, Björck-Pereyra style corollaries, and extended
Clenshaw recurrence.  Primary contracts are Algorithms 22.1-22.3, 22.8; Theorems
22.4, 22.6; Corollaries 22.5, 22.7.

### Chapter 23: Fast Matrix Multiplication

Formalize Winograd inner products, Strassen's method, Winograd variant,
bilinear noncommutative algorithms, 3M complex multiplication, and their forward
error bounds.  Primary contracts are Theorems 23.1-23.4.

### Chapter 24: FFT and Circulant Systems

Formalize the DFT matrix, Cooley-Tukey radix-2 factorization, FFT roundoff
bound under twiddle-factor assumptions, circulant diagonalization, and circulant
linear-system backward error.  Primary contracts are Theorems 24.1-24.3.

### Chapter 25: Nonlinear Systems

Formalize finite precision Newton iterations, residual limiting accuracy,
componentwise and normwise conditioning for nonlinear systems, special examples,
and stopping rules.  Primary contracts are Theorems 25.1 and 25.2.

### Chapter 26: Automatic Error Analysis

Formalize direct search optimization problem setup, alternating directions and
multidirectional search algorithm specs, convergence tests, example objective
functions for GE growth/condition estimation/fast inversion/cubic roots, interval
arithmetic definitions, and error-linearization ideas.  There are no primary
labels; use section-level algorithm and equation contracts.

### Chapter 27: Software Issues in Floating Point Arithmetic

Formalize IEEE special values and predicates needed by algorithms, exception flag
assumptions, arithmetic-parameter discovery, floating point testing predicates,
portable model assumptions, underflow/overflow-safe norm and complex division
algorithms, and multiple/mixed precision contracts.  There are no primary labels;
use definitions and algorithm specs as contracts.

### Chapter 28: Test Matrices

Formalize Hilbert, Cauchy, random, randsvd, Pascal, tridiagonal Toeplitz, and
companion matrices; determinant/inverse/conditioning formulas where stated; and
the Haar random orthogonal construction.  Primary contract is Theorem 28.1, plus
equation-defined matrix families.

### Appendix A

Appendix A is not a fifth split.  Its solutions are assigned by problem prefix:
solutions `1.x-6.x` to Split 1, `7.x-12.x` to Split 2, `13.x-19.x` to Split 3,
and `20.x-28.x` to Split 4.  Each split must scan its Appendix A portion for:

- proofs omitted in the chapter text,
- lemmas used by later chapters,
- counterexamples that justify a theorem's hypotheses,
- reusable formulas not present in the main chapter.

## Cross-Split Imports

Split 2 may placeholder only these Split 1 families:

- `H02.rounding_model`, `H02.exact_subtraction`, `H03.gamma_theta`,
  `H03.inner_product_bounds`, `H06.norms`, `H06.svd`, `H06.condition_distance`.

Split 3 may placeholder these upstream families:

- From Split 1: all Split 1 families above.
- From Split 2: `H07.linear_system_backward_error`, `H08.triangular_solve`,
  `H09.lu_ge_core`, `H10.cholesky_core`, `H12.iterative_refinement`.

Split 4 may placeholder these upstream families:

- From Split 1: arithmetic, gamma/theta, norms, SVD, polynomial and matrix
  multiplication kernels.
- From Split 2: linear-system perturbation, triangular solve, LU/GE, Cholesky,
  refinement.
- From Split 3: block LU, inverse/GJE, condition estimators, Sylvester if needed,
  stationary/matrix powers, QR, Vandermonde preliminaries.

Forward-reference exceptions:

- Ch1 QR example may point to Ch19 as an illustrative contract.
- Ch9 diagonal-dominance theorem must be proved directly in Split 2 or factored
  into an early scalar lemma to avoid a Ch9-Ch13 cycle.
- Ch16 mentions Schur decomposition stability via Ch19-style tools; both are
  Split 3, so keep this internal.

## Merge Plan

1. Freeze all contracts before proof work begins.  A changed contract requires
   notifying every split that imports it.
2. Each split creates interface files for exported contracts first.  Dependent
   splits import these interfaces for placeholders.
3. Implement split-owned definitions before split-owned theorems.  Do not create
   a second definition for an upstream object.
4. Every pull request must update contract status and list new upstream imports.
5. Merge order for final integration: Split 1, Split 2, Split 3, Split 4, then the
   final no-placeholder branch.
6. Final checks:
   - every primary label in `planning/chapter_index.md` has an implemented contract,
   - every required equation contract is either implemented or local to an
     implemented proof,
   - every Appendix A proof dependency is closed,
   - no placeholders, local axioms, or `sorry`s remain,
   - no duplicate definitions of floating point, norms, factorizations, residuals,
     condition numbers, or named algorithms exist.

## Daily Working Rule

Before starting a theorem, the formalizer must search the contract ledger for
the concepts and results it uses.  If a needed result is owned by another split,
import its placeholder.  If it is missing from the ledger, add a contract and
assign ownership before proving anything.  This is the rule that prevents
parallel work from becoming duplicate work.
