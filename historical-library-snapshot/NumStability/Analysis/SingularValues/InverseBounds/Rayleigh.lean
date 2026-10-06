import NumStability.Analysis.MatrixAlgebra
import NumStability.Analysis.MatrixSpectral

/-!
# Analysis.SingularValues.InverseBounds.Rayleigh

W05 semantic leaf. Declaration commands are copied byte-identically from the frozen C0004 owners.
-/

-- Analysis/InverseOpNorm2.lean
--
-- The exact-spectral inverse operator 2-norm `‖P⁻¹‖₂ = 1/σ_min(P)`, built from
-- the Hermitian spectral machinery of `MatrixSpectral.lean`.
--
-- Higham, Accuracy and Stability of Numerical Algorithms, 2nd ed., relies on
-- the identity `‖P⁻¹‖₂ = 1/σ_min(P)` (where `σ_min(P)² = λ_min(PᵀP)`) to turn a
-- separation/eigenvalue lower bound into an inverse-operator Frobenius bound.
-- For the structured Sylvester / Lyapunov condition numbers of
-- `Higham16Psi.lean` / `Higham16Lyapunov.lean`, that inverse-operator bound `M`
-- is currently taken as SUPPLIED DATA.  This file removes that caveat at the
-- spectral level: from a Rayleigh `λ_min` lower bound on the Gram matrix `PᵀP`
-- it constructs a concrete `M = 1/σ_min` and proves the vector inverse bound
-- `∀ x, ‖x‖₂ ≤ (1/σ_min) ‖P x‖₂`, then packages it as a `SepLowerBound` so it
-- discharges `SylvesterInverseOpBound` / `LyapunovInverseOpBound` through the
-- repository's existing `sylvesterInverseOpBound_of_sepLowerBound` bridge.
--
-- The reusable spectral core is:
--
--   * `rayleigh_lower_bound_of_le_finiteHermitianEigenvalues` -- for a symmetric
--     PSD matrix `G` with `λmin ≤ λ_i(G)` for all `i`, the Rayleigh lower bound
--     `λmin · ‖x‖² ≤ ⟪x, G x⟫`.  This is exactly the min-Rayleigh characterization
--     `⟪x, G x⟫ ≥ λ_min ‖x‖²`, obtained from the Hermitian spectral theorem via
--     the repository's `finiteLoewnerLe`/eigenvalue Loewner bridge.
--
-- Applied to the Gram matrix `G = PᵀP` (always symmetric PSD, with
-- `⟪x, PᵀP x⟫ = ‖P x‖²`), it yields
--
--   * `sigmaMin_mul_vecNorm2_le_matMulVec` -- `σ · ‖x‖₂ ≤ ‖P x‖₂` with
--     `σ = Real.sqrt λmin` = `σ_min(P)` (Rayleigh λmin form of the singular-value
--     lower bound), and
--   * `vecNorm2_le_inv_sigmaMin_mul_matMulVec` -- `‖x‖₂ ≤ (1/σ) ‖P x‖₂`, the
--     concrete `‖P⁻¹‖₂ = 1/σ_min` operator bound with `M = 1/σ_min`.
--
-- The Sylvester/Lyapunov bridge:
--
--   * `sepLowerBound_of_sylvesterOp_sigmaMin` -- if the Sylvester operator itself
--     satisfies the vector σ_min lower bound `σ · ‖Y‖_F ≤ ‖T(Y)‖_F`, then
--     `SepLowerBound n A B σ` holds; composing with the repository's
--     `sylvesterInverseOpBound_of_sepLowerBound` discharges
--     `SylvesterInverseOpBound n A B (1/σ)` with the EXACT `M = 1/σ`.
--   * `lyapunovInverseOpBound_of_sigmaMin` -- the analogous discharge for
--     `LyapunovInverseOpBound`.
--
-- Honest scope.  What is NEW and unconditional here is the spectral core: the
-- Rayleigh `λ_min` lower bound and the exact `σ · ‖x‖₂ ≤ ‖P x‖₂` singular-value
-- bound for a general real matrix `P`, i.e. `‖P⁻¹‖₂ = 1/σ_min(P)` as a genuine
-- operator bound rather than supplied data.  The remaining wiring to close the
-- Sylvester/Lyapunov modules with NO supplied `M` at all is the vec-isometry
-- identity `‖Y‖_F = ‖vec Y‖₂` and `frobNorm (T Y) = ‖P · vec Y‖₂` connecting the
-- repository's hand-rolled `frobNorm` to the Kronecker coefficient `P`; that
-- Frobenius↔ℓ² bridge is not yet present in the repository, so this file
-- delivers the operator-norm core and
-- packages the σ_min hypothesis in the exact shape the existing
-- `SepLowerBound → SylvesterInverseOpBound` bridge consumes.





namespace NumStability

open scoped BigOperators

-- ============================================================
-- Reusable spectral core: the Rayleigh λ_min lower bound
-- ============================================================

/-- **Rayleigh minimum characterization / `λ_min` lower bound.**

    For a symmetric real finite matrix `G` all of whose Hermitian eigenvalues
    are at least `λmin`, the quadratic (Rayleigh) form is bounded below:
      `λmin · ‖x‖₂² ≤ ⟪x, G x⟫`  for every `x`.

    This is the reusable spectral core.  It is the exact
    `⟪x, G x⟫ ≥ λ_min ‖x‖²` Rayleigh minimum characterization, obtained from the
    Hermitian spectral theorem through the repository's eigenvalue→Loewner
    bridge (`finiteLoewnerLe_smul_id_of_le_finiteHermitianEigenvalues`): the
    hypothesis `λmin ≤ λ_i(G)` gives the Loewner inequality `λmin·I ⪯ G`, whose
    quadratic form on the left is `λmin·‖x‖²`. -/
theorem rayleigh_lower_bound_of_le_finiteHermitianEigenvalues
    {ι : Type*} [Fintype ι] [DecidableEq ι]
    (G : ι → ι → ℝ) (hG : IsSymmetricFiniteMatrix G) {lam : ℝ}
    (hEig : ∀ a : ι, lam ≤ finiteHermitianEigenvalues G hG a) (x : ι → ℝ) :
    lam * finiteVecNorm2Sq x ≤ finiteQuadraticForm G x := by
  have hLoewner :
      finiteLoewnerLe (fun i j => lam * finiteIdMatrix i j) G :=
    finiteLoewnerLe_smul_id_of_le_finiteHermitianEigenvalues G hG hEig
  have hq := hLoewner x
  rwa [finiteQuadraticForm_smul_finiteIdMatrix] at hq

-- ============================================================
-- The Gram matrix `PᵀP`: symmetric, PSD, and `⟪x, PᵀP x⟫ = ‖P x‖²`
-- ============================================================


































































-- ============================================================
-- The exact σ_min lower bound  `σ · ‖x‖₂ ≤ ‖P x‖₂`
-- ============================================================













































































-- ============================================================
-- Sylvester / Lyapunov bridge: discharging the supplied-`M` hypothesis
-- ============================================================








































































-- ============================================================
-- Axiom check (uncomment locally to verify the standard trio)
-- ============================================================
--
-- `#print axioms` for all public results above reports exactly
--   [propext, Classical.choice, Quot.sound]
-- (the standard Mathlib trio); no incomplete-proof or custom axioms.
--
-- #print axioms vecNorm2_le_inv_sigmaMin_mul_matMulVec
-- #print axioms sigmaMin_mul_vecNorm2_le_matMulVec
-- #print axioms rayleigh_lower_bound_of_le_finiteHermitianEigenvalues
-- #print axioms sylvesterInverseOpBound_of_sigmaMin
-- #print axioms lyapunovInverseOpBound_of_sigmaMin

end NumStability
