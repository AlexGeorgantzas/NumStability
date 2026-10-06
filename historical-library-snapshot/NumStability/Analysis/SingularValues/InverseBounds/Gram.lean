import NumStability.Analysis.MatrixAlgebra
import NumStability.Analysis.MatrixSpectral

/-!
# Analysis.SingularValues.InverseBounds.Gram

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

/-- The Gram matrix `PᵀP` of a square real matrix `P` is symmetric.
    `(PᵀP)ᵢⱼ = ∑ₖ Pₖᵢ Pₖⱼ`, symmetric in `i, j`. -/
theorem isSymmetricFiniteMatrix_gram {n : ℕ} (P : Fin n → Fin n → ℝ) :
    IsSymmetricFiniteMatrix (matMul n (matTranspose P) P) := by
  intro i j
  unfold matMul matTranspose
  exact Finset.sum_congr rfl (fun k _ => by ring)

/-- **The Gram quadratic-form identity `⟪x, PᵀP x⟫ = ‖P x‖₂²`.**

    The quadratic form of the Gram matrix `PᵀP` evaluated at `x` equals the
    squared Euclidean norm of `P x`.  This is the algebraic bridge that turns the
    spectral Rayleigh lower bound on `PᵀP` into a norm lower bound on `P x`. -/
theorem finiteQuadraticForm_gram_eq_vecNorm2Sq {n : ℕ}
    (P : Fin n → Fin n → ℝ) (x : Fin n → ℝ) :
    finiteQuadraticForm (matMul n (matTranspose P) P) x =
      vecNorm2Sq (matMulVec n P x) := by
  -- Let `y = P x`.  `⟪x, PᵀP x⟫ = ∑ᵢ xᵢ (Pᵀ y)ᵢ = ∑ₖ yₖ² = ‖y‖²`.
  have hmv : ∀ i : Fin n,
      finiteMatVec (matMul n (matTranspose P) P) x i =
        matMulVec n (matTranspose P) (matMulVec n P x) i := by
    intro i
    have h := matMulVec_matMul n (matTranspose P) P x i
    -- `finiteMatVec M x = matMulVec n M x` on `Fin n` (both `fun i => ∑ⱼ Mᵢⱼ xⱼ`).
    simpa [finiteMatVec, matMulVec] using h
  unfold finiteQuadraticForm vecNorm2Sq
  set y : Fin n → ℝ := matMulVec n P x with hy
  calc
    (∑ i : Fin n, x i * finiteMatVec (matMul n (matTranspose P) P) x i)
        = ∑ i : Fin n, x i * matMulVec n (matTranspose P) y i := by
            exact Finset.sum_congr rfl (fun i _ => by rw [hmv i])
    _ = ∑ i : Fin n, x i * ∑ k : Fin n, P k i * y k := by
            refine Finset.sum_congr rfl (fun i _ => ?_)
            unfold matMulVec matTranspose; rfl
    _ = ∑ i : Fin n, ∑ k : Fin n, x i * (P k i * y k) := by
            refine Finset.sum_congr rfl (fun i _ => ?_)
            rw [Finset.mul_sum]
    _ = ∑ k : Fin n, ∑ i : Fin n, x i * (P k i * y k) := by
            rw [Finset.sum_comm]
    _ = ∑ k : Fin n, y k * ∑ i : Fin n, P k i * x i := by
            refine Finset.sum_congr rfl (fun k _ => ?_)
            rw [Finset.mul_sum]
            exact Finset.sum_congr rfl (fun i _ => by ring)
    _ = ∑ k : Fin n, y k * y k := by
            refine Finset.sum_congr rfl (fun k _ => ?_)
            have : (∑ i : Fin n, P k i * x i) = y k := by
              rw [hy]; unfold matMulVec; rfl
            rw [this]
    _ = ∑ k : Fin n, y k ^ 2 := by
            exact Finset.sum_congr rfl (fun k _ => by ring)

/-- The Gram matrix `PᵀP` is positive semidefinite: its quadratic form
    `‖P x‖₂² ≥ 0`.  Proved directly from `finiteQuadraticForm_gram_eq_vecNorm2Sq`,
    no Mathlib PSD bridge required. -/
theorem finitePSD_gram {n : ℕ} (P : Fin n → Fin n → ℝ) :
    finitePSD (matMul n (matTranspose P) P) := by
  intro x
  rw [finiteQuadraticForm_gram_eq_vecNorm2Sq]
  exact vecNorm2Sq_nonneg _

/-- The Gram matrix `PᵀP` and the `Fin n` squared-norm conventions agree:
    `finiteVecNorm2Sq x = vecNorm2Sq x` on `Fin n` (both `∑ᵢ xᵢ²`). -/
theorem finiteVecNorm2Sq_eq_vecNorm2Sq {n : ℕ} (x : Fin n → ℝ) :
    finiteVecNorm2Sq x = vecNorm2Sq x := rfl

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
