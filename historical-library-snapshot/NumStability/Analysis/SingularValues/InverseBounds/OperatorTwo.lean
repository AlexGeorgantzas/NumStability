import NumStability.Analysis.MatrixAlgebra
import NumStability.Analysis.MatrixSpectral
import NumStability.Analysis.SingularValues.InverseBounds.Gram
import NumStability.Analysis.SingularValues.InverseBounds.Rayleigh

/-!
# Analysis.SingularValues.InverseBounds.OperatorTwo

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

/-- **The squared singular-value lower bound `λmin · ‖x‖² ≤ ‖P x‖²`.**

    Combining the Rayleigh `λ_min` lower bound on the Gram matrix `PᵀP` with the
    identity `⟪x, PᵀP x⟫ = ‖P x‖²`: if every Hermitian eigenvalue of `PᵀP` is at
    least `λmin`, then `λmin · ‖x‖₂² ≤ ‖P x‖₂²`. -/
theorem lamMin_mul_vecNorm2Sq_le_matMulVec {n : ℕ}
    (P : Fin n → Fin n → ℝ) {lam : ℝ}
    (hEig : ∀ a : Fin n,
      lam ≤ finiteHermitianEigenvalues (matMul n (matTranspose P) P)
        (isSymmetricFiniteMatrix_gram P) a)
    (x : Fin n → ℝ) :
    lam * vecNorm2Sq x ≤ vecNorm2Sq (matMulVec n P x) := by
  have hray :=
    rayleigh_lower_bound_of_le_finiteHermitianEigenvalues
      (matMul n (matTranspose P) P) (isSymmetricFiniteMatrix_gram P) hEig x
  rwa [finiteQuadraticForm_gram_eq_vecNorm2Sq, finiteVecNorm2Sq_eq_vecNorm2Sq]
    at hray

/-- `a² ≤ b²` with `0 ≤ b` gives `a ≤ b` (used to take square roots of the
    squared singular-value lower bound; here `b = ‖P x‖₂ ≥ 0`). -/
theorem le_of_sq_le_sq_of_nonneg {a b : ℝ} (hb : 0 ≤ b)
    (h : a ^ 2 ≤ b ^ 2) : a ≤ b := by
  by_contra hlt
  push_neg at hlt
  -- `b < a`, with `0 ≤ b < a`, forces `b² < a²`, contradicting `a² ≤ b²`.
  nlinarith [hlt, hb, h]

/-- **The exact singular-value lower bound `σ_min · ‖x‖₂ ≤ ‖P x‖₂`.**

    With `σ = Real.sqrt λmin` (= `σ_min(P)`, since `σ_min(P)² = λ_min(PᵀP)`), the
    Rayleigh `λ_min` bound gives the vector inequality
      `σ · ‖x‖₂ ≤ ‖P x‖₂`  for every `x`.
    This is the exact `‖P⁻¹‖₂ = 1/σ_min(P)` operator relation in its
    lower-bound (Rayleigh) form. -/
theorem sigmaMin_mul_vecNorm2_le_matMulVec {n : ℕ}
    (P : Fin n → Fin n → ℝ) {lam : ℝ} (hlam : 0 ≤ lam)
    (hEig : ∀ a : Fin n,
      lam ≤ finiteHermitianEigenvalues (matMul n (matTranspose P) P)
        (isSymmetricFiniteMatrix_gram P) a)
    (x : Fin n → ℝ) :
    Real.sqrt lam * vecNorm2 x ≤ vecNorm2 (matMulVec n P x) := by
  set σ := Real.sqrt lam with hσdef
  -- Square both sides: `(σ ‖x‖)² = λ ‖x‖² ≤ ‖P x‖²`.
  have hsq_bound : lam * vecNorm2Sq x ≤ vecNorm2Sq (matMulVec n P x) :=
    lamMin_mul_vecNorm2Sq_le_matMulVec P hEig x
  have hlhs_sq : (σ * vecNorm2 x) ^ 2 = lam * vecNorm2Sq x := by
    rw [mul_pow, hσdef, Real.sq_sqrt hlam, vecNorm2_sq]
  have hrhs_sq : vecNorm2 (matMulVec n P x) ^ 2 = vecNorm2Sq (matMulVec n P x) :=
    vecNorm2_sq _
  have hsq : (σ * vecNorm2 x) ^ 2 ≤ vecNorm2 (matMulVec n P x) ^ 2 := by
    rw [hlhs_sq, hrhs_sq]; exact hsq_bound
  exact le_of_sq_le_sq_of_nonneg (vecNorm2_nonneg _) hsq

/-- **The inverse operator-2 bound `‖x‖₂ ≤ (1/√lam) ‖P x‖₂`.**

    With `σ = Real.sqrt lam > 0` for any lower bound `lam ≤ λ_i(PᵀP)` on the Gram
    eigenvalues, the singular-value lower bound rearranges to the inverse-operator
    bound with `M = 1/√lam`:
      `‖x‖₂ ≤ (1/√lam) ‖P x‖₂`  for every `x`.
    This is the vector-action form of `‖P⁻¹‖₂ ≤ 1/√lam`; it becomes the tight
    identity `‖P⁻¹‖₂ = 1/σ_min(P)` exactly at the sharp instantiation
    `lam = λ_min(PᵀP)` (so `√lam = σ_min(P)`). -/
theorem vecNorm2_le_inv_sigmaMin_mul_matMulVec {n : ℕ}
    (P : Fin n → Fin n → ℝ) {lam : ℝ} (hlam : 0 < lam)
    (hEig : ∀ a : Fin n,
      lam ≤ finiteHermitianEigenvalues (matMul n (matTranspose P) P)
        (isSymmetricFiniteMatrix_gram P) a)
    (x : Fin n → ℝ) :
    vecNorm2 x ≤ (1 / Real.sqrt lam) * vecNorm2 (matMulVec n P x) := by
  set σ := Real.sqrt lam with hσdef
  have hσpos : 0 < σ := by rw [hσdef]; exact Real.sqrt_pos.mpr hlam
  have hbnd : σ * vecNorm2 x ≤ vecNorm2 (matMulVec n P x) :=
    sigmaMin_mul_vecNorm2_le_matMulVec P (le_of_lt hlam) hEig x
  rw [one_div, ← div_eq_inv_mul, le_div_iff₀ hσpos, mul_comm]
  exact hbnd

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
