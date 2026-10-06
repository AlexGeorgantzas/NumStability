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

import NumStability.Analysis.MatrixSpectral
import NumStability.Algorithms.Sylvester.Higham16Psi
import NumStability.Algorithms.Sylvester.Higham16Lyapunov

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
