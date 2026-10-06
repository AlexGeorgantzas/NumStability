import NumStability.Algorithms.MatrixEquations.Sylvester.Conditioning.StructuredLyapunov
import NumStability.Algorithms.MatrixEquations.Sylvester.Conditioning.StructuredSylvester
import NumStability.Algorithms.MatrixEquations.Sylvester.Equation.Basic
import NumStability.Algorithms.MatrixEquations.Sylvester.Equation.Lyapunov
import NumStability.Analysis.MatrixAlgebra
import NumStability.Analysis.MatrixSpectral

/-!
# Algorithms.MatrixEquations.Sylvester.Conditioning.SingularValue

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
























-- ============================================================
-- The Gram matrix `PᵀP`: symmetric, PSD, and `⟪x, PᵀP x⟫ = ‖P x‖²`
-- ============================================================


































































-- ============================================================
-- The exact σ_min lower bound  `σ · ‖x‖₂ ≤ ‖P x‖₂`
-- ============================================================













































































-- ============================================================
-- Sylvester / Lyapunov bridge: discharging the supplied-`M` hypothesis
-- ============================================================

/-- **From a Sylvester-operator σ_min bound to `SepLowerBound`.**

    If the Sylvester operator `T(Y) = AY - YB` satisfies the vector-level
    singular-value lower bound `σ · ‖Y‖_F ≤ ‖T(Y)‖_F` with `σ > 0`, then
    `SepLowerBound n A B σ` holds (`sep(A,B) ≥ σ`).  The hypothesis is exactly
    the shape produced by `sigmaMin_mul_vecNorm2_le_matMulVec` for the vectorized
    Sylvester coefficient `P` (once the vec-isometry `‖Y‖_F = ‖vec Y‖₂`,
    `‖T Y‖_F = ‖P · vec Y‖₂` is supplied).

    This packages the exact `σ = σ_min` so that composing with the repository's
    `sylvesterInverseOpBound_of_sepLowerBound` discharges
    `SylvesterInverseOpBound n A B (1/σ)` with `M = 1/σ_min` — no supplied `M`. -/
theorem sepLowerBound_of_sylvesterOp_sigmaMin (n : ℕ)
    (A B : Fin n → Fin n → ℝ) (σ : ℝ) (hσ : 0 < σ)
    (hbnd : ∀ Y : Fin n → Fin n → ℝ,
      σ * frobNorm Y ≤ frobNorm (sylvesterOp n A B Y)) :
    SepLowerBound n A B σ := by
  refine ⟨hσ, ?_⟩
  intro Y _hY
  have h := hbnd Y
  -- Square: `σ² ‖Y‖² = (σ ‖Y‖)² ≤ ‖T Y‖²`.
  have hlhs_nn : 0 ≤ σ * frobNorm Y := mul_nonneg (le_of_lt hσ) (frobNorm_nonneg Y)
  have hsq : (σ * frobNorm Y) ^ 2 ≤ frobNorm (sylvesterOp n A B Y) ^ 2 := by
    have hr_nn : 0 ≤ frobNorm (sylvesterOp n A B Y) := frobNorm_nonneg _
    nlinarith [h, hlhs_nn, hr_nn]
  have hlhs_eq : (σ * frobNorm Y) ^ 2 = σ ^ 2 * frobNormSq Y := by
    rw [mul_pow, frobNorm_sq]
  have hrhs_eq :
      frobNorm (sylvesterOp n A B Y) ^ 2 = frobNormSq (sylvesterOp n A B Y) :=
    frobNorm_sq _
  rw [hlhs_eq, hrhs_eq] at hsq
  exact hsq

/-- **Exact `SylvesterInverseOpBound` from a σ_min lower bound.**

    A Sylvester-operator singular-value bound `σ · ‖Y‖_F ≤ ‖T(Y)‖_F` (σ > 0)
    yields `SylvesterInverseOpBound n A B (1/σ)` with the EXACT `M = 1/σ_min`,
    discharging the supplied-`M` hypothesis of `Higham16Psi.lean`.  Obtained by
    composing `sepLowerBound_of_sylvesterOp_sigmaMin` with the repository's
    `sylvesterInverseOpBound_of_sepLowerBound`. -/
theorem sylvesterInverseOpBound_of_sigmaMin (n : ℕ)
    (A B : Fin n → Fin n → ℝ) (σ : ℝ) (hσ : 0 < σ)
    (hbnd : ∀ Y : Fin n → Fin n → ℝ,
      σ * frobNorm Y ≤ frobNorm (sylvesterOp n A B Y)) :
    SylvesterInverseOpBound n A B (1 / σ) :=
  sylvesterInverseOpBound_of_sepLowerBound n A B σ hσ
    (sepLowerBound_of_sylvesterOp_sigmaMin n A B σ hσ hbnd)

/-- **Exact `LyapunovInverseOpBound` from a σ_min lower bound.**

    A Lyapunov-operator singular-value bound `σ · ‖Y‖_F ≤ ‖L(Y)‖_F` (σ > 0)
    yields `LyapunovInverseOpBound n A (1/σ)` with the EXACT `M = 1/σ_min`,
    discharging the supplied-`M` hypothesis of `Higham16Lyapunov.lean`.  Uses
    `lyapunovOp = sylvesterOp` with `B = -Aᵀ` and the Sylvester σ_min bridge. -/
theorem lyapunovInverseOpBound_of_sigmaMin (n : ℕ)
    (A : Fin n → Fin n → ℝ) (σ : ℝ) (hσ : 0 < σ)
    (hbnd : ∀ Y : Fin n → Fin n → ℝ,
      σ * frobNorm Y ≤ frobNorm (lyapunovOp n A Y)) :
    LyapunovInverseOpBound n A (1 / σ) := by
  -- Transfer the bound to the Sylvester operator with `B = -Aᵀ`.
  have hbnd' : ∀ Y : Fin n → Fin n → ℝ,
      σ * frobNorm Y ≤
        frobNorm (sylvesterOp n A (fun i j => -matTranspose A i j) Y) := by
    intro Y
    have h := hbnd Y
    rwa [lyapunovOp_eq_sylvesterOp n A Y] at h
  have hSep : SepLowerBound n A (fun i j => -matTranspose A i j) σ :=
    sepLowerBound_of_sylvesterOp_sigmaMin n A (fun i j => -matTranspose A i j)
      σ hσ hbnd'
  exact lyapunovInverseOpBound_of_sepLowerBound n A σ hσ hSep

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
