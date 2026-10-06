# Project Decision Log

This file records design decisions for the LeanFpAnalysis project.  It is
intended as thesis source material and durable project memory.

The log is project-wide, not only a benchmark log.  It should record decisions
about library design, proof organization, documentation, branches, benchmark
methodology, and thesis-facing rationale.

Important: do not include this file in solver-facing generated workspaces.  It
may contain rationale, rejected alternatives, expected difficulty, and private
project context.

## Branch Policy

### Decision: Keep Benchmark Work On A Dedicated Branch

Benchmark artifacts live on branch `benchmark`.

This includes:

- benchmark task files;
- condition-specific stubs;
- generated-workspace scripts;
- run protocols;
- task-selection rationale;
- contamination checks;
- solver-attempt logs, when added.

Reason: benchmark design is exploratory and has different risks from the core
library.  It may need several iterations, and it must avoid accidentally mixing
solver-facing material with private design rationale.  Keeping it on its own
branch lets the core library remain stable while benchmark infrastructure
evolves.

`main` is the core-library branch.  It may keep project-wide thesis notes like
this file and reusable public documentation, but benchmark harness files should
not live on `main` unless explicitly merged later.

## Core Library Decisions

### Decision: Use An Axiomatic Floating-Point Model

The library is built around `FPModel`, an axiomatic model over `Real`, rather
than a specific IEEE 754 formalization.

Reason: the goal is automatic stability analysis in a general mathematical
floating-point model.  The core theorem statements should be reusable across
formats and rounding implementations, as long as they satisfy the model
axioms.

Consequence: avoid adding IEEE-specific assumptions to core modules.  If they
are ever needed, they should belong in a separate optional module.

### Decision: Build Stability Proofs Compositionally

New results should reuse existing lower-level contracts whenever possible:
rounding lemmas support summation, summation supports dot products, dot
products support matvec/matmul, and triangular solve contracts support
higher-level solve analyses.

Reason: the thesis goal is not only to formalize isolated theorems, but to test
whether a library of reusable stability components helps future analyses.

### Decision: Mark Abstract Interfaces Honestly

Some high-level results are specification-transfer theorems: they take an
external or abstract hypothesis that is already close to the desired numerical
contract, then package the consequence.

Reason: these are useful named interfaces, but they should not be advertised as
fully derived floating-point analyses from `FPModel`.

Consequence: wrappers around external assumptions should be documented as
abstract/specification-transfer results.

### Decision: Keep Public Lookup Documentation

The files `docs/LIBRARY_LOOKUP.md` and `examples/LibraryLookup.lean` are public
library documentation.

Reason: the library is large.  A central lookup guide helps humans and tools
discover relevant definitions and theorem families without relying on private
agent memory.

These files are allowed on `main` because they describe the library generally.
They should avoid task-specific proof scripts.

### Decision: Use Mathlib As The Source Of Truth For Exact Norms

Exact vector and matrix norms should come from Mathlib.  When the object
already has a Mathlib-native type, statements should use Mathlib notation
directly, such as `x ⬝ᵥ y`, `‖WithLp.toLp 2 x‖`, or `‖A‖`.

Reason: exact norms and dot products are mathematical infrastructure, not
floating-point algorithms.  Re-defining them locally creates a parallel exact
algebra world and makes reuse of Mathlib harder.

Consequence: local exact aliases should not be independent definitions.
Compatibility wrappers are acceptable only when they bridge existing legacy
representations to Mathlib.  In particular, `frobNorm A` is a rectangular
wrapper over Mathlib's Frobenius norm,
`‖(Matrix.of A : RMat m n)‖`, not a separate Frobenius norm.

### Decision: Separate Mathlib Matrices From Legacy Algorithm Matrices

The library now records the intended matrix shapes explicitly:

- `RMat m n := Matrix (Fin m) (Fin n) ℝ`;
- `RSqMat n := RMat n n`;
- `RMatFn m n := Fin m → Fin n → ℝ`.

Reason: new exact matrix-facing APIs should move toward Mathlib-native
rectangular matrices, especially for QR and least-squares analyses.  Existing
`fl_*` algorithms still use function-shaped matrices heavily, so an immediate
global migration would be too disruptive.

Consequence: use `RMat` for new exact matrix interfaces when possible.  Use
`RMatFn` only when interoperating with existing algorithm code or square
matrix infrastructure.  Wrappers such as `frobNorm` and `infNorm` keep legacy
statements readable while still using Mathlib norms internally.

### Decision: Prioritize Rectangular Real Matrices Before Complex Matrices

The implementation-backed QR rebuild should support rectangular real matrices
before attempting complex matrices.

Reason: QR factorization and least-squares algorithms are naturally
rectangular.  Complex matrices are important, but complex floating-point
arithmetic requires an explicit model choice: either primitive complex rounded
operations or operations built from rounded real arithmetic on real and
imaginary parts.

Consequence: avoid adding new square-only exact infrastructure unless the
algorithm is inherently square.  Keep the core `FPModel` real-valued for now;
complex support should be a later explicit layer.

### Decision: Repass The Library For Implementation-Backed Stability Proofs

The end-to-end rebuild should audit every algorithmic stability theorem and
classify it as either implementation-backed or contract/specification-transfer.

Implementation-backed means:

- a concrete rounded `fl_*` algorithm is defined from `FPModel` primitives;
- the advertised error contract is proved from that algorithm;
- higher-level theorems may then consume the contract as a reusable interface.

Reason: this is the difference between the current dot-product layer and the
current QR layer.  `fl_dotProduct` is a concrete rounded recurrence, and
`dotProduct_backward_error` is proved from that recurrence using primitive
rounding, summation, and gamma lemmas.  By contrast, the current Householder QR
theorem takes `OrthogonalSequenceBackwardError` as a hypothesis, and
`HouseholderAppError` states the one-step reflector error contract without yet
deriving it from rounded Householder construction/application code.

Consequence: contracts should not be deleted.  They are useful modular
interfaces.  But a module should not be described as a full end-to-end
floating-point stability proof until the missing bridge theorem exists:

`FPModel` primitives -> concrete `fl_*` implementation -> contract proof ->
final stability theorem.

For thesis language, the current QR result should be described as a valid
conditional/compositional theorem, not yet as a full proof that a concrete
rounded Householder QR implementation is backward stable.

### Decision: Treat Existential `Q` As Normal For Householder QR Backward Error

After the Householder rebuild, the preferred QR result is
implementation-backed for the computed `R` factor:
`fl_householderQR_R_structured_backward_error` proves the concrete
zero-aware rounded recursive Householder `R` algorithm satisfies the QR
backward-error contract.

The theorem still states the orthogonal factor existentially: there exists an
exact orthogonal `Q` such that `A + ΔA = Q R_hat`.

Reason: this is the usual mathematical shape of the Householder QR
backward-error theorem.  The exact `Q` is the product of ideal orthogonal
reflectors used in the backward-error representation; it is not necessarily a
separately computed floating-point output.  For QR solve, the algorithm applies
the same rounded reflector sequence to the right-hand side directly, so an
explicit returned `Q` is not required for the solve theorem either.

Consequence: the current Householder QR `R` and QR-solve results can be
described as implementation-backed stability proofs under their stated model
and side assumptions.  A future explicit-`Q` API would be a separate algorithmic
feature, not a prerequisite for the Higham-style backward-error theorem.

### Decision: Build The Explicit Householder `Q` Layer In Two Steps

The first explicit-`Q` layer exposes the exact orthogonal witness associated
with the zero-aware rounded `R` algorithm, not a separately rounded accumulated
`Q_hat`.

Reason: the existing backward-error proof already constructs an exact
orthogonal `Q` witness through the same branch choices and rounded trailing
panels as `fl_householderQR_R`.  Making that witness explicit is a small,
source-aligned step.  A rounded accumulated `Q_hat` would require a separate
floating-point algorithm for forming/storing `Q` and a new analysis of that
algorithm.

Consequence: the current implementation adds `fl_householderQR_Q` and the
paired `fl_householderQR_witness`, proves the `Q` field orthogonal, and
keeps the `R` field tied to the existing structured backward-error theorem.
The next milestone was to prove the perturbation equation directly with this
explicit witness `Q`.  This is now done by
`fl_householderQR_witness_explicit_backward_error_of_global_gammaValid`,
which proves the witness fields satisfy `Q R = A + ΔA` with the same
branch-dependent backward-error bound.

The remaining distinction is still important: this is an exact orthogonal
`Q` witness used in the backward-error representation, not a separately rounded
accumulated `Q_hat`.  A rounded `Q_hat` API should be designed only after
deciding whether the library needs to model explicitly forming `Q` or only
applying the reflector sequence.

### Decision: Add Rounded Householder `Q_hat` Without Overclaiming

After exposing and proving the exact Householder QR witness, the next API layer
adds a concrete rounded accumulated `Q_hat`:
`fl_householderQRPanel_Qhat`, `fl_householderQR_Qhat`,
`HouseholderQRComputedFactors`, and `fl_householderQR_computed`.

Reason: explicitly forming `Q` is a separate floating-point algorithm from
producing the backward-stable `R` factor.  The computed `Q_hat` should therefore
be represented by its own rounded operation order: in each nonzero Householder
branch, the same rounded reflector used for the panel update is applied to the
embedded trailing accumulator.

Consequence: the library can now name both objects honestly.  The exact
`Q` object is the orthogonal witness used in the proved perturbation
equation.  The rounded `Q_hat` object is a concrete algorithmic output, but its
orthogonality/backward-error bridge is still future work and must not be
advertised as already proved.

The first bridge theorem for this layer is
`fl_householderQRPanel_Qhat_succ_succ_nonzero_step_error`.  It proves that
one nonzero rounded `Q_hat` accumulator update satisfies the same rectangular
Householder matrix-step error already proved for the low-level rounded
reflector application.  This is a local one-step result, not yet the full
recursive accumulated `Q_hat` theorem.

The next local bridge is
`fl_householderQRPanel_Qhat_succ_succ_nonzero_residual_bound`, which
packages that same one-step update as an exact Householder application plus a
single bounded residual matrix.  This residual form is the one needed for a
future recursive accumulated-`Q_hat` analysis.  The computed-factor API also
now exposes `R_hat` wrappers for upper-triangularity and structured backward
error; those facts are inherited from `R` and intentionally do not claim
that the rounded `Q_hat` has already been analyzed.

The zero-column skip branch is covered by
`fl_householderQRPanel_Qhat_succ_succ_zero_residual_bound`, which models
the skip as identity transformation on the embedded trailing accumulator with
zero residual.  This matters because the Householder QR recursion has two branches,
and future accumulated-`Q_hat` proofs should not silently assume all active
columns are nonzero.

The computed-factor `R_hat` field is now connected to the explicit exact
witness theorem by
`fl_householderQR_computed_R_hat_explicit_backward_error_of_global_gammaValid`.
This makes the public computed-factor API usable for the already-proved
backward-error statement while preserving the important distinction that the
rounded `Q_hat` field is not yet proved stable.

The branch-specific `Q_hat` residual lemmas are now packaged by a single
branch-combined interface: `householderQRPanel_Qhat_stepP`,
`fl_householderQRPanel_Qhat_tail`,
`householderQRPanel_Qhat_stepCoeff`, and
`fl_householderQRPanel_Qhat_succ_succ_residual_bound`.  This is an
engineering step toward the full recursive proof: future proofs can reason
about one zero-aware step uniformly instead of splitting zero/nonzero columns at
every use site.

The local step theorem is now bundled as
`fl_householderQRPanel_Qhat_succ_succ_step_interface`, which provides
exact-step orthogonality, nonnegative branch coefficient, and residual form in
one statement.  This keeps the next recursive proof closer to the mathematical
sequence theorem shape: orthogonal step plus bounded residual.

The exact embedding norm facts
`frobNormSq_embedTrailingOne`, `frobNorm_embedTrailingOne`, and
`frobNorm_embedTrailingOne_of_orthogonal` were added because the accumulated
`Q_hat` proof will need to bound norms of embedded trailing accumulators.
These are exact algebra lemmas, not floating-point assumptions.

The first recursive accumulated `Q_hat` theorem is now in place.  The raw bound
is `householderQRPanel_QhatAccumBound`, the perturbation contract is
`HouseholderQRPanelQhatAccumError`, and
`fl_householderQRPanel_Qhat_accum_error` proves that the concrete rounded
panel accumulator is an exact orthogonal matrix plus a bounded perturbation.
The public square/global wrappers expose the same fact for
`fl_householderQR_Qhat` and the `Q_hat` field of
`fl_householderQR_computed`.

This is deliberately still a raw recursive theorem.  It closes the immediate
recursive perturbation layer, but it does not yet simplify the accumulated
bound into a Higham-style closed-form growth estimate, nor does it identify the
exact orthogonal factor with the previously exposed `fl_householderQR_Q`
witness.  Those are the next QR proof obligations before claiming a polished
computed-`Q_hat` stability result.

The next refinement introduces `householderQRPanel_QhatClosedBound`.  This is
still recursive, but it removes direct dependence on the actual accumulated
`Q_hat` norm at each step: from the accumulated tail theorem, the embedded tail
accumulator has norm at most `sqrt (m + 1) + ηtail`, where the `sqrt` term is
the exact Frobenius norm of an embedded orthogonal block and `ηtail` is the
already accumulated perturbation.  This is a cleaner proof object for thesis
exposition because it shows how the local reflector residuals accumulate
through an orthogonal-plus-perturbation decomposition, without pretending that
we have already derived a final compact Higham-style closed-form constant.

The exact orthogonal factor in the computed-`Q_hat` perturbation theorem is now
fixed to the same `Q` witness used by the Householder QR backward-error
proof.  The key algebraic bridge is that the existing recursive `Q`
definition has the same one-step orientation as the rounded `Q_hat` residual
recurrence; in the nonzero branch this follows from symmetry of the exact
Householder reflector.  This removes an important ambiguity: `Q_hat` is no
longer only "some exact orthogonal matrix plus perturbation"; it is the
specific exact witness `Q` plus a bounded perturbation.

This is still not the final textbook-facing computed-`Q_hat` theorem.  The
remaining step is to simplify the recursive bound
`householderQRPanel_QhatClosedBound` into a compact growth estimate suitable for
comparison with a Higham-style constant.

The next proof layer introduces a dimension-only uniform recurrence
`householderQR_QhatUniformClosedBound`.  It replaces the branch-sensitive local
coefficient at each step by the global coefficient
`householderConstructApplyBound fp n`, and replaces every embedded orthogonal
block norm by `sqrt n`.  This is justified by proving monotonicity of
`householderConstructApplyBound` from monotonicity of `sqrt` and `gamma`, then
proving the branch-sensitive closed bound is below the uniform recurrence.

Reason: this creates a public theorem that is easier to explain than the raw
branch-sensitive bound:
`Q_hat = Q + ΔQ` with `‖ΔQ‖_F` bounded by a dimension-only recurrence.
It is not yet the final closed form, but it is a clean intermediate theorem on
the way to a Higham-style compact growth factor.

The uniform recurrence has now been solved exactly.  If
`c = householderConstructApplyBound fp n`, then the recurrence
`η₀ = 0`, `ηₖ₊₁ = ηₖ + c (sqrt n + ηₖ)` equals
`ηₖ = ((1 + c)^k - 1) sqrt n`.  The public computed-factor theorem now states
that the rounded accumulated `Q_hat` differs from the exact exact witness `Q`
by a perturbation bounded by this closed-form expression.

This final step is algebraic and local to the proof architecture.  It does not
change the Householder one-step coefficient, which is still the
implementation-backed coefficient derived from the low-level rounded
Householder construction/application proof.

The current computed-factor API is now packaged by
`HouseholderQRComputedFactorsExplicitError`.  This combines the two relevant
facts for `(Q_hat, R_hat)`: the computed `R_hat` satisfies the explicit
exact-witness backward-error theorem, and the computed `Q_hat` is that same
exact witness plus a perturbation bounded by the closed-form `Q_hat` growth
factor.  This is useful thesis language because it avoids saying that the
rounded `Q_hat` is exactly orthogonal while still explaining precisely how it
relates to the exact orthogonal factor used in the backward-error proof.

The exact closed-form `Q_hat` bound has also been weakened to a simpler growth
corollary:
`((1+c)^k - 1) sqrt(n) ≤ k*c*(1+c)^k*sqrt(n)`.  This is not a new Higham
result or a new floating-point assumption; it is a local algebraic corollary
used for easier presentation.  The closed-form theorem remains sharper, while
the growth theorem is useful when thesis prose needs a familiar
"number of steps times one-step coefficient times growth factor" expression.

### Decision: Do Not Treat Rounded `Q_hat` As Exactly Orthogonal

Higham Theorem 18.4 uses an exact orthogonal matrix `Q`: the product of exact
Householder reflectors corresponding to the exact application of each computed
algorithm step.  The explicitly rounded accumulated factor `Q_hat` is a
different object.  Under a general Higham-style `FPModel`, applying rounded
matrix updates to accumulate `Q_hat` does not preserve exact orthogonality.

Reason: claiming `Q_hat` itself is the orthogonal factor would be mathematically
false in the general floating-point model.  The correct end-to-end statement is
two-layered: prove the concrete rounded `R_hat` satisfies the QR backward-error
equation with the exact orthogonal witness `Q`, and prove the concrete
rounded `Q_hat` is a bounded perturbation of that same `Q`.

Consequence: the library now exposes source-facing growth wrappers for both
layers.  `fl_householderQR_computed_R_hat_explicit_backward_error_highamGrowth_of_global_gammaValid`
states the implementation-backed `R_hat` result with a compact
`n*c*(1+c)^n*‖A‖_F` coefficient, while
`fl_householderQR_computed_Q_hat_fixed_Q_growth_accum_error_of_global_gammaValid`
states the matching perturbation bound for `Q_hat`.  The theorem
`fl_householderQR_computed_residual_error_highamGrowth_of_global_gammaValid`
directly uses the product `Q_hat * R_hat` and proves a residual bound for the
computed factors, without asserting exact orthogonality of `Q_hat`.

### Decision: Make Higham's Hidden QR Constant Explicit In Lean

Higham states the Householder QR bound with a hidden constant in notation such
as `n γ_cm`.  Lean cannot use an unspecified `c*m` unless we make it a real
index.  The library therefore introduces
`householderConstructApplyGammaIndex n = 3*(11*n+23)`.

Reason: the concrete one-step Householder construction/application proof
produces
`sqrt(n*u^2) + 2*gamma(11*n+23)`.  We prove this is bounded by one gamma term:
`householderConstructApplyBound_le_gamma`.  Then
`residualAccumBound_gamma_le_gamma_mul` absorbs `n` repeated steps into
`gamma (n * householderConstructApplyGammaIndex n)`.

Consequence: the theorem
`fl_householderQR_computed_R_hat_explicit_backward_error_gammaHigham_of_global_gammaValid`
is now the closest formal version of Higham Theorem 18.4 for the concrete
rounded `R_hat` implementation:
`‖ΔA‖_F ≤ gamma(n*K) ‖A‖_F`, where
`K = householderConstructApplyGammaIndex n`.  The constant is explicit and
proved from the implementation-backed lower-level bounds, rather than hidden
or assumed.

### Decision: Keep QR Solve Publicly Existential But Add Fixed-Witness Components

The final QR solve backward-error statement is about the computed solution:
there exist perturbations `ΔA` and `Δb` such that
`(A + ΔA) x_hat = b + Δb`.  That final contract does not need to expose the
orthogonal factor `Q`.

However, for the end-to-end rebuild audit, the component theorem should still
make clear that the zero-aware rounded QR `R` panel and the zero-aware rounded RHS
transform are explained by the same exact Householder factor.  Therefore the
library now has fixed-witness component contracts:
`HouseholderQRRhsPanelExplicitBackwardError` and
`HouseholderQRPanelSolveFixedBackwardError`.

Reason: this closes an avoidable ambiguity in the solve layer.  The proof no
longer merely says that some shared orthogonal factor exists for the zero-aware
components; it can name the exact factor generated by the same zero-aware recursion,
`fl_householderQR_Q`.

Consequence: the public theorem
`fl_householderQR_solve_components_fixed_Q_backward_error_of_global_gammaValid`
is the preferred citation when discussing the implementation-backed QR solve
components.  The final `QRSolveBackwardError` remains existential because that
is the natural mathematical shape of the solved-system perturbation result.
Its implementation-backed proof now consumes the fixed-`Q` component
bridge directly, so the public existential theorem is not bypassing the
fixed-witness layer internally.

### Decision: Use `min m p` Stages For Rectangular Householder QR Panels

Higham's Householder QR theorem is naturally rectangular: for a tall
`m × n` matrix, the algorithm performs `n` reflector stages.  The earlier
square-facing wrappers counted `n` stages for an `n × n` matrix, which was
fine for the square specialization but not precise enough for rectangular
panels.

Reason: the recursive panel algorithm shrinks both the active row and column
dimensions.  Therefore a general `m × p` panel performs at most `min m p`
stages; in the tall case `p ≤ m`, this becomes exactly the number of columns
`p`.  This is the right bridge between the concrete recursive implementation
and Higham's rectangular statement.

Consequence: the library now has
`fl_householderQRPanel_R_explicit_backward_error_gammaHigham_of_global_gammaValid`
for rectangular panels and
`fl_householderQRPanel_R_explicit_backward_error_tall_gammaHigham_of_global_gammaValid`
for the tall specialization.  These remain implementation-backed: they start
from the concrete zero-aware rounded `R` panel theorem and then absorb its
recursive coefficient into one explicit gamma term.  The theorem uses the
exact orthogonal witness `Q`, not the rounded accumulated `Q_hat`.

The structural part is now packaged too.  `IsUpperTrapezoidal` generalizes the
square `IsUpperTriangular` predicate, and
`fl_householderQRPanel_R_upper_trapezoidal` proves that the concrete
recursive `R` panel has the rectangular QR shape.  The structured theorem
`fl_householderQRPanel_R_structured_explicit_backward_error_tall_gammaHigham_of_global_gammaValid`
combines this shape fact with the tall explicit-`Q` gamma theorem.

The rectangular computed-factor API follows the same honest policy as the
square computed-factor API.  `HouseholderQRPanelComputedFactors` and
`fl_householderQRPanel_computed` expose the concrete panel-level
`(Q_hat, R_hat)` output.  The theorem
`fl_householderQRPanel_computed_explicit_error_tall_gammaHigham_of_global_gammaValid`
packages two facts: the computed `R_hat` has the structured tall rectangular
single-gamma backward-error theorem against exact `Q`, and the rounded
`Q_hat` is a bounded perturbation of that same `Q`.  It does not assert
that rounded `Q_hat` is exactly orthogonal.

The library also now has a direct residual theorem for the rectangular
computed product:
`fl_householderQRPanel_computed_residual_error_tall_gammaHigham_of_global_gammaValid`.
This proves that the concrete rounded product `Q_hat * R_hat` equals the input
panel plus a bounded residual.  It required two exact rectangular algebra
lemmas, `matMulRect_add_left` and `frobNorm_matMulRect_le`, both of which are
pure matrix algebra and do not add new floating-point assumptions.

### Decision: Keep QR Solve Bounds Stage-Separated

The concrete Householder QR solve now has
`fl_householderQR_solve_backward_error_gammaHigham_of_global_gammaValid`.
This theorem replaces the QR-factorization part of the final solve bound by
the same explicit single-gamma coefficient used for the Householder QR
factorization:
`gamma fp (n * householderConstructApplyGammaIndex n) * ‖A‖_F`.

Reason: QR solve is a composition of stages.  The factorization stage is now
absorbed into the Householder QR gamma coefficient, but the back-substitution
stage has its own theorem and contributes the separate term
`gamma fp n * ‖R‖_F`.  Collapsing both terms into one QR-looking gamma
would hide which part comes from factorization and which part comes from the
triangular solve.

Consequence: the theorem is more source-facing than the raw recursive
coefficient version, while still preserving the stage structure required for
the end-to-end audit.

### Decision: Bound QR RHS Recursion Without Hiding Intermediate Computations

The Householder QR RHS transform has a raw recursive perturbation bound,
`householderQRRhsBackwardBound`, that depends on the actual intermediate
rounded right-hand sides generated by the concrete Householder recursion.

Reason: this is the most implementation-faithful theorem: each recursive term
corresponds to the actual vector passed to the next rounded reflector.  However,
for source-facing QR solve statements we also need a readable bound of the form
coefficient times `‖b‖∞`.

Consequence: add the intermediate proof layer rather than replacing the raw
bound.  `fl_householder_first_column_rhs_step_infNormVec_le` proves one-step
RHS norm growth from the concrete `fl_householderApply` bridge, and
`householderQRRhsBackwardBound_le_growthCoeff_of_global_gammaValid` proves
that the recursive RHS bound is at most
`householderQRRhsGrowthCoeff fp n * ‖b‖∞`.  This keeps the implementation
trace visible while making a cleaner Theorem 18.5 statement possible.  The
current preferred theorem is
`fl_householderQR_solve_backward_error_gammaHigham_closedInputBounds_of_global_gammaValid`,
which combines the single-gamma QR factorization matrix term, the separate
back-substitution matrix term, and a conservative nonrecursive RHS growth
bound.  The back-substitution matrix term is no longer printed with
`‖R‖_F`: the exact-witness QR backward-error theorem proves
`‖R‖_F ≤ (1 + gamma_K) ‖A‖_F`, so the final matrix coefficient depends
only on the original input `A`.  The closed RHS expression is marked as a local
derived citation bound; it is not advertised as Higham's sharp hidden constant.

## Benchmark Summary

The detailed benchmark design currently lives on branch `benchmark`.

Current durable decisions from that branch:

- use two benchmark conditions, not three;
- make Condition A a bare isolated workspace;
- make Condition C a fresh full-library workspace with public docs but no
  private memory or task-specific hints;
- give both conditions byte-identical task files;
- satisfy `import LeanFpAnalysis.FP` in Condition A with task-specific bare
  stubs and in Condition C with the real library;
- do not pre-solve benchmark tasks with Codex before evaluation.

Reason for keeping the detailed benchmark log on `benchmark`: the task ladder,
stubs, scripts, contamination protocol, and solver-run machinery are still
active experimental work.

### Decision: Make Zero-Aware Householder QR the Canonical API

The earlier rebuild kept two public Householder QR paths: an older recursive
path that required every active first column to be nonzero, and a later
zero-aware path whose names ended in ``.

Reason: this was a useful migration device while proving the zero-column skip
case, but it is the wrong final API.  A user should not have to choose between
"normal" and "safe" Householder QR.  The mathematically general algorithm is the
one that handles zero active columns by exact skip branches and nonzero columns
by the rounded Householder construction/application bridge.

Consequence: the zero-aware path now owns the canonical names
`fl_householderQR_R`, `fl_householderQR_Q`, `fl_householderQR_witness`,
`fl_householderQR_Qhat`, `fl_householderQR_computed`, `fl_householderQR_rhs`,
and `fl_householderQR_solve`.  The obsolete nonzero-only recursive QR/RHS/solve
proof path was removed rather than kept as a parallel public API.  The one-step
rounded Householder update helper remains, because it is the real rounded
kernel used in the nonzero branch of the canonical algorithm.

### Decision: Expose Householder QR As One Result Object

After removing the `_safe` duplicate path, the remaining public QR API still had
separate names such as `fl_householderQR_R`, `fl_householderQR_Q`, and
`fl_householderQR_Qhat`.

Reason: these names are useful internally while proving individual facts about
one component, but they make the library look like it contains several
different QR algorithms.  Mathematically, Householder QR is one factorization
algorithm that returns factors.  A user should call one algorithm and project
the factor needed in a proof.

Consequence: the public API now includes `fl_householderQR fp n A`, returning a
`HouseholderQRResult n` with fields `.Q_exact`, `.R`, and `.Q`.  New theorem
statements can use `(fl_householderQR fp n A).R` for the computed triangular
factor, `(fl_householderQR fp n A).Q_exact` for the exact orthogonal witness,
and `(fl_householderQR fp n A).Q` for the rounded accumulated factor.  The older
component names remain as compatibility projection helpers during the migration,
but they should not be documented as separate algorithms.

### Decision: Rename the Householder QR Factor Fields Honestly

The first unified object API used `.Q` for the exact orthogonal witness and
`.Qhat` for the rounded accumulated factor.  This was mathematically accurate
inside the proof stack but confusing at the public API level: in numerical
linear algebra, users naturally expect the `Q` field of a computed QR result to
refer to the computed/rounded factor.

Reason: the exact witness is not a floating-point output of the algorithm.  It
is an exact mathematical object tied to the same Householder branch choices and
used to state the backward-error equation.  The rounded accumulated factor is
the algorithmic output.

Consequence: the public result fields are now `.Q_exact`, `.R`, and `.Q`.
The exact witness appears explicitly as `.Q_exact`; the rounded computed factor
uses the natural `.Q` name.  Compatibility helpers such as
`fl_householderQR_Q` and `fl_householderQR_Qhat` remain during the migration.

### Decision: Close The Householder QR Componentwise Panel Gap

Higham Theorem 18.4 has both a normwise Frobenius backward-error statement and
a componentwise statement of the form `|ΔA|` bounded by a scalar multiple of
`G |A|`, where `G` is nonnegative and `‖G‖_F = 1`.  The earlier implementation
backed the rectangular Householder QR `R` theorem by the concrete zero-aware
rounded panel algorithm, but it collapsed each first-column Householder step to
a single Frobenius residual before the recursive QR proof.

Reason: that was enough for the normwise part, but it did not preserve the
columnwise perturbation information used by Higham's componentwise statement.
The source proves bounds for applying each Householder reflector columnwise;
the formal proof should carry that information through the recursive QR
composition instead of treating the componentwise theorem as a separate
assumption.

Consequence: `HouseholderQR.lean` now has a proof-facing columnwise contract
`HouseholderQRPanelColumnwiseBackwardError`, column Frobenius helpers, a stored
first-column theorem retaining both Frobenius and columnwise bounds for the same
residual, and the recursive implementation-backed theorem
`fl_householderQRPanel_R_columnwise_backward_error`.  The source-facing theorem
`fl_householderQRPanel_R_higham_backward_error_gammaHigham_of_global_gammaValid`
packages the concrete rounded panel algorithm into the Higham-style `G |A|`
componentwise statement.  This closes the rectangular Householder QR
factorization gap discussed earlier; QR solve, Givens QR, LU, Cholesky, and
other high-level algorithms still require their own separate end-to-end audits.
