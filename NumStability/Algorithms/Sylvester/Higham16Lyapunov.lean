-- Algorithms/Sylvester/Higham16Lyapunov.lean
--
-- Concrete realizations of the structured Lyapunov condition number Psi for
-- Higham, Accuracy and Stability of Numerical Algorithms, 2nd ed.,
-- Chapter 16.3, equation (16.27).
--
-- The certificate predicate `LyapunovConditionFirstOrderBound` (in
-- `SylvesterPerturbation.lean`) is the theorem-facing form of the (16.27)
-- structured first-order bound for the Lyapunov equation `A X + X A^T = C`: a
-- real `Psi` that dominates the structured inverse first-order Lyapunov
-- perturbation map, so that the printed relative bound
-- `||dX||_F / ||X||_F <= sqrt 2 * Psi * eps` follows through
-- `lyapunov_relative_first_order_bound_of_condition`.  (The Lyapunov data has
-- only the two blocks `(dA / alpha, dC / gamma)`, whence the `sqrt 2` in place
-- of the Sylvester `sqrt 3`.)
--
-- This file constructs concrete `Psi` witnesses that INSTANTIATE that
-- predicate, mirroring the Sylvester `Higham16Psi.lean` module:
--
--   * `lyapunovCond_of_inverseOpBound` / `_isLyapunovConditionFirstOrderBound`
--     -- the honest GENERAL certificate instantiation.  Higham writes the
--     Lyapunov condition number through `||P^{-1}||` with the vec/Kronecker
--     coefficient `P = I kron A + A kron I` (eq (16.27)).  The exact
--     operator-norm construction of `||P^{-1}||` from `A` needs an
--     SVD / operator-norm API that is not present here, so we take the
--     inverse-operator Frobenius bound `M` (an upper bound on `||P^{-1}||_2`,
--     i.e. `1 / sep(A,-A^T)`) as SUPPLIED data, exactly as the book writes the
--     condition number in terms of `||P^{-1}||`.  From `M` we build the
--     closed-form `Psi = M * (2 * alpha * ||X||_F + gamma) / ||X||_F` and prove
--     it satisfies the certificate.  (The factor `2 alpha` replaces the
--     Sylvester `(alpha + beta)` because the Lyapunov data perturbation
--     `dB = -dA^T` is tied to `dA`, so both product blocks scale with `alpha`.)
--
--   * `lyapunovCondDiagonal` / `_isLyapunovConditionFirstOrderBound` -- the
--     concrete DIAGONAL case.  With `A = diag a` and an entrywise separation
--     lower bound `s <= |a_i + a_j|` (so `s > 0` is a lower bound on
--     `sep(A,-A^T)` and `1/s` bounds every entry of the explicit inverse of the
--     diagonal Lyapunov coefficient, whose entries are `(a_i + a_j)^{-1}`), the
--     inverse-operator bound `M = 1/s` is explicit, and
--     `lyapunovCondDiagonal = (1/s) * (2 * alpha * ||X||_F + gamma) / ||X||_F`.
--     This closes (16.27) for the diagonalizable / distinct-eigenvalue Lyapunov
--     case (eigenvalues `a_i` of `A`, all pairwise sums `a_i + a_j` separated).
--
--   * `H16_eq16_27_lyapunov_condition_diagonal` -- the labeled (16.27) wrapper
--     tying the diagonal `Psi` to the printed relative first-order perturbation
--     bound via `lyapunov_relative_first_order_bound_of_condition`.
--
-- Honest scope.  The DIAGONAL witness is fully self-contained (no supplied
-- operator-norm data beyond the entrywise separation `s`, which is elementary
-- for diagonal matrices).  It therefore covers exactly the case where `A` is
-- diagonal with separated diagonal-pair sums `a_i + a_j` -- i.e. the
-- diagonalizable Lyapunov operator with distinct eigenvalues expressed in
-- eigencoordinates.  The GENERAL witness takes the `||P^{-1}||`-type bound `M`
-- as data, matching how Higham states the condition number; instantiating `M`
-- for a nondiagonal `A` from the entries of `A` alone is precisely the missing
-- SVD/operator-norm step (identical to the Sylvester Psi module).

import NumStability.Algorithms.Sylvester.SylvesterPerturbation
import NumStability.Algorithms.Sylvester.Higham16

namespace NumStability

open scoped BigOperators Matrix.Norms.Frobenius

-- ============================================================
-- Pair-norm single-block bounds (from eq (16.27))
-- ============================================================

/-- Higham, 2nd ed., §16.3, eq (16.27) (p. 317):
    the `dA / alpha` block of the normalized Lyapunov data perturbation is
    bounded by the stacked pair norm.  Since `lyapunovScaledPerturbationPairNorm`
    is the square root of the sum of the two nonnegative normalized squared
    blocks, a single block is bounded by the whole square root, giving
    `||dA||_F <= alpha * pairNorm`. -/
theorem frobNorm_le_alpha_mul_lyapunovPairNorm (n : ℕ)
    (ΔA ΔC : Fin n → Fin n → ℝ) (α γ : ℝ) (hα : 0 < α) :
    frobNorm ΔA ≤
      α * lyapunovScaledPerturbationPairNorm n ΔA ΔC α γ := by
  have hterm :
      (frobNorm ΔA / α) ^ 2 ≤
        frobNormSq ΔA / α ^ 2 + frobNormSq ΔC / γ ^ 2 := by
    have hC : 0 ≤ frobNormSq ΔC / γ ^ 2 :=
      div_nonneg (frobNormSq_nonneg ΔC) (sq_nonneg γ)
    have heq : (frobNorm ΔA / α) ^ 2 = frobNormSq ΔA / α ^ 2 := by
      rw [div_pow, frobNorm_sq]
    rw [heq]; linarith
  have hnn : 0 ≤ frobNorm ΔA / α :=
    div_nonneg (frobNorm_nonneg ΔA) (le_of_lt hα)
  have hsqrt :
      frobNorm ΔA / α ≤
        lyapunovScaledPerturbationPairNorm n ΔA ΔC α γ := by
    unfold lyapunovScaledPerturbationPairNorm
    calc frobNorm ΔA / α
        = Real.sqrt ((frobNorm ΔA / α) ^ 2) := (Real.sqrt_sq hnn).symm
      _ ≤ Real.sqrt (frobNormSq ΔA / α ^ 2 + frobNormSq ΔC / γ ^ 2) :=
            Real.sqrt_le_sqrt hterm
  rw [div_le_iff₀ hα] at hsqrt
  linarith [hsqrt]

/-- Higham, 2nd ed., §16.3, eq (16.27) (p. 317): the `dC / gamma` block. -/
theorem frobNorm_le_gamma_mul_lyapunovPairNorm (n : ℕ)
    (ΔA ΔC : Fin n → Fin n → ℝ) (α γ : ℝ) (hγ : 0 < γ) :
    frobNorm ΔC ≤
      γ * lyapunovScaledPerturbationPairNorm n ΔA ΔC α γ := by
  have hterm :
      (frobNorm ΔC / γ) ^ 2 ≤
        frobNormSq ΔA / α ^ 2 + frobNormSq ΔC / γ ^ 2 := by
    have hA : 0 ≤ frobNormSq ΔA / α ^ 2 :=
      div_nonneg (frobNormSq_nonneg ΔA) (sq_nonneg α)
    have heq : (frobNorm ΔC / γ) ^ 2 = frobNormSq ΔC / γ ^ 2 := by
      rw [div_pow, frobNorm_sq]
    rw [heq]; linarith
  have hnn : 0 ≤ frobNorm ΔC / γ :=
    div_nonneg (frobNorm_nonneg ΔC) (le_of_lt hγ)
  have hsqrt :
      frobNorm ΔC / γ ≤
        lyapunovScaledPerturbationPairNorm n ΔA ΔC α γ := by
    unfold lyapunovScaledPerturbationPairNorm
    calc frobNorm ΔC / γ
        = Real.sqrt ((frobNorm ΔC / γ) ^ 2) := (Real.sqrt_sq hnn).symm
      _ ≤ Real.sqrt (frobNormSq ΔA / α ^ 2 + frobNormSq ΔC / γ ^ 2) :=
            Real.sqrt_le_sqrt hterm
  rw [div_le_iff₀ hγ] at hsqrt
  linarith [hsqrt]

-- ============================================================
-- Linearized right-hand side bound (from eq (16.27))
-- ============================================================

/-- Higham, 2nd ed., §16.3, eq (16.27) (p. 317):
    the linearized first-order Lyapunov right-hand side
    `R = dC - dA X - X dA^T` has Frobenius norm bounded by
    `(2 * alpha * ||X||_F + gamma) * pairNorm`.

    The two product blocks `dA X` and `X dA^T` both scale with `alpha`
    (`||dA^T||_F = ||dA||_F`), giving the Lyapunov coefficient `2 alpha ||X|| + gamma`
    in place of the Sylvester `(alpha + beta) ||X|| + gamma`. -/
theorem lyapunov_first_order_rhs_frobNorm_le (n : ℕ)
    (X ΔA ΔC : Fin n → Fin n → ℝ) (α γ : ℝ)
    (hα : 0 < α) (hγ : 0 < γ) :
    frobNorm
        (fun i j =>
          ΔC i j - matMul n ΔA X i j - matMul n X (matTranspose ΔA) i j) ≤
      (2 * α * frobNorm X + γ) *
        lyapunovScaledPerturbationPairNorm n ΔA ΔC α γ := by
  set T := lyapunovScaledPerturbationPairNorm n ΔA ΔC α γ with hT
  -- Block bounds from (16.27).
  have hA := frobNorm_le_alpha_mul_lyapunovPairNorm n ΔA ΔC α γ hα
  have hC := frobNorm_le_gamma_mul_lyapunovPairNorm n ΔA ΔC α γ hγ
  -- `||dA^T||_F = ||dA||_F <= alpha * T`.
  have hAT : frobNorm (matTranspose ΔA) ≤ α * T := by
    rw [frobNorm_transpose]; exact hA
  -- Submultiplicativity for the two product blocks.
  have hAX : frobNorm (matMul n ΔA X) ≤ (α * T) * frobNorm X :=
    le_trans (frobNorm_matMul_le ΔA X)
      (mul_le_mul_of_nonneg_right hA (frobNorm_nonneg X))
  have hXAT : frobNorm (matMul n X (matTranspose ΔA)) ≤ frobNorm X * (α * T) :=
    le_trans (frobNorm_matMul_le X (matTranspose ΔA))
      (mul_le_mul_of_nonneg_left hAT (frobNorm_nonneg X))
  -- Rewrite `dC - dA X - X dA^T = dC + (-(dA X) - X dA^T)` and apply triangle.
  have h_rw :
      (fun i j =>
          ΔC i j - matMul n ΔA X i j - matMul n X (matTranspose ΔA) i j) =
        (fun i j =>
          ΔC i j +
            (-matMul n ΔA X i j - matMul n X (matTranspose ΔA) i j)) := by
    ext i j; ring
  rw [h_rw]
  have htri1 :=
    frobNorm_add_le ΔC
      (fun i j => -matMul n ΔA X i j - matMul n X (matTranspose ΔA) i j)
  have htri2 :=
    frobNorm_sub_le (fun i j => -matMul n ΔA X i j) (matMul n X (matTranspose ΔA))
  -- `||-(dA X)||_F = ||dA X||_F`.
  have hneg : frobNorm (fun i j => -matMul n ΔA X i j) = frobNorm (matMul n ΔA X) := by
    rw [show (fun i j => -matMul n ΔA X i j)
          = (fun i j => -(matMul n ΔA X) i j) from rfl, frobNorm_neg]
  -- Combine all bounds.
  have hbudget :
      frobNorm ΔC +
          (frobNorm (matMul n ΔA X) + frobNorm (matMul n X (matTranspose ΔA))) ≤
        (2 * α * frobNorm X + γ) * T := by
    have hXnn := frobNorm_nonneg X
    nlinarith [hA, hC, hAX, hXAT]
  calc
    frobNorm
        (fun i j =>
          ΔC i j +
            (-matMul n ΔA X i j - matMul n X (matTranspose ΔA) i j))
        ≤ frobNorm ΔC +
            frobNorm
              (fun i j =>
                -matMul n ΔA X i j - matMul n X (matTranspose ΔA) i j) := htri1
    _ ≤ frobNorm ΔC +
          (frobNorm (matMul n ΔA X) +
            frobNorm (matMul n X (matTranspose ΔA))) := by
            rw [hneg] at htri2; linarith [htri2]
    _ ≤ (2 * α * frobNorm X + γ) * T := hbudget

/-- Higham, 2nd ed., Section 16.3, equation (16.27):
    source-numbered alias for the `dA / alpha` Lyapunov pair-norm block bound. -/
alias H16_eq16_27_frobNorm_le_alpha_mul_lyapunovPairNorm :=
  frobNorm_le_alpha_mul_lyapunovPairNorm

/-- Higham, 2nd ed., Section 16.3, equation (16.27):
    source-numbered alias for the `dC / gamma` Lyapunov pair-norm block bound. -/
alias H16_eq16_27_frobNorm_le_gamma_mul_lyapunovPairNorm :=
  frobNorm_le_gamma_mul_lyapunovPairNorm

/-- Higham, 2nd ed., Section 16.3, equation (16.27):
    source-numbered alias for the Lyapunov first-order right-hand-side
    Frobenius bound. -/
alias H16_eq16_27_lyapunov_first_order_rhs_frobNorm_le :=
  lyapunov_first_order_rhs_frobNorm_le

-- ============================================================
-- General certificate instantiation from a supplied inverse-operator bound
-- (eq (16.27), the `||P^{-1}||`-structured condition number taken as data)
-- ============================================================

/-- Higham, 2nd ed., §16.3, eq (16.27) (p. 317):
    an inverse-operator Frobenius bound for the Lyapunov operator
    `L(Y) = A Y + Y A^T`.  `M` bounds the norm of the inverse map, i.e.
    `M >= 1 / sep(A,-A^T)`; in the vec/Kronecker picture this is the
    `||P^{-1}||_2`-type quantity, with `P = I kron A + A kron I` (eq (16.27)).
    We take it as SUPPLIED data: the closed-form construction of `||P^{-1}||`
    from `A` needs an SVD/operator-norm API not available here. -/
def LyapunovInverseOpBound (n : ℕ) (A : Fin n → Fin n → ℝ) (M : ℝ) : Prop :=
  ∀ Y : Fin n → Fin n → ℝ,
    frobNorm Y ≤ M * frobNorm (lyapunovOp n A Y)

/-- Higham, 2nd ed., Section 16.3, equation (16.27):
    source-numbered abbreviation for the supplied Lyapunov inverse-operator
    bound underlying the structured condition number. -/
abbrev H16_eq16_27_LyapunovInverseOpBound :=
  LyapunovInverseOpBound

/-- Higham, 2nd ed., §16.3, eq (16.27) (p. 317):
    a `SepLowerBound` for `(A, -A^T)` supplies a Lyapunov inverse-operator bound
    with `M = 1 / sigma`.  This records that `LyapunovInverseOpBound` is exactly
    the `||P^{-1}||` (= `1 / sep(A,-A^T)`) data the book uses to define the
    Lyapunov condition number. -/
theorem lyapunovInverseOpBound_of_sepLowerBound (n : ℕ)
    (A : Fin n → Fin n → ℝ) (σ : ℝ) (hσ : 0 < σ)
    (hSep : SepLowerBound n A (fun i j => -matTranspose A i j) σ) :
    LyapunovInverseOpBound n A (1 / σ) := by
  intro Y
  -- `L(Y) = T(Y)` for the Sylvester operator with `B = -A^T`.
  have hLeq : lyapunovOp n A Y = sylvesterOp n A (fun i j => -matTranspose A i j) Y :=
    lyapunovOp_eq_sylvesterOp n A Y
  rw [hLeq]
  by_cases hY : frobNormSq Y = 0
  · -- `Y = 0`, both sides vanish.
    have hYnorm : frobNorm Y = 0 := by
      rw [frobNorm_eq_sqrt_frobNormSq, Real.sqrt_eq_zero (frobNormSq_nonneg Y)]
      exact hY
    rw [hYnorm]
    have : 0 ≤ 1 / σ *
        frobNorm (sylvesterOp n A (fun i j => -matTranspose A i j) Y) :=
      mul_nonneg (by positivity) (frobNorm_nonneg _)
    linarith
  · -- `sigma * ||Y|| <= ||T(Y)||`, then divide by sigma.
    have hbnd := hSep.2 Y hY
    rw [← frobNorm_sq, ← frobNorm_sq] at hbnd
    have hσ_nn : 0 ≤ σ := le_of_lt hσ
    have hstep :
        σ * frobNorm Y ≤
          frobNorm (sylvesterOp n A (fun i j => -matTranspose A i j) Y) := by
      nlinarith [sq_nonneg (σ * frobNorm Y -
          frobNorm (sylvesterOp n A (fun i j => -matTranspose A i j) Y)),
        frobNorm_nonneg (sylvesterOp n A (fun i j => -matTranspose A i j) Y),
        frobNorm_nonneg Y]
    rw [one_div, ← div_eq_inv_mul, le_div_iff₀ hσ, mul_comm]
    exact hstep

/-- Higham, 2nd ed., §16.3, eq (16.27) (p. 317):
    the concrete structured Lyapunov condition number built from a supplied
    inverse-operator bound `M` and the data weights `alpha, gamma`, matching the
    printed `Psi = ||P^{-1}[ ... ]|| / ||vec X||`:
      `Psi = M * (2 * alpha * ||X||_F + gamma) / ||X||_F`.
    (The `/ ||X||_F` is exactly the book's normalization by `||vec X||`; the
    `2 alpha` reflects the tied Lyapunov perturbation `dB = -dA^T`.) -/
noncomputable def lyapunovCond_of_inverseOpBound (n : ℕ)
    (X : Fin n → Fin n → ℝ) (α γ M : ℝ) : ℝ :=
  M * (2 * α * frobNorm X + γ) / frobNorm X

/-- Higham, 2nd ed., Section 16.3, equation (16.27):
    source-numbered abbreviation for the supplied-inverse-bound Lyapunov
    condition number value. -/
noncomputable abbrev H16_eq16_27_lyapunovCond_of_inverseOpBound :=
  lyapunovCond_of_inverseOpBound

/-- Higham, 2nd ed., §16.3, eq (16.27) (p. 317):
    the supplied-`M` structured condition number satisfies the certificate
    predicate `LyapunovConditionFirstOrderBound`.  This turns the (16.27)
    certificate into a usable theorem for any Lyapunov operator equipped with an
    inverse-operator (i.e. `||P^{-1}||`) bound. -/
theorem lyapunovCond_of_inverseOpBound_isLyapunovConditionFirstOrderBound (n : ℕ)
    (A X : Fin n → Fin n → ℝ) (α γ M : ℝ)
    (hα : 0 < α) (hγ : 0 < γ) (hM : 0 ≤ M)
    (hX : 0 < frobNorm X)
    (hInv : LyapunovInverseOpBound n A M) :
    LyapunovConditionFirstOrderBound n A X α γ
      (lyapunovCond_of_inverseOpBound n X α γ M) := by
  intro ΔA ΔC ΔX hLin
  set T := lyapunovScaledPerturbationPairNorm n ΔA ΔC α γ with hT
  -- `L(dX) = R` pointwise, so `||L(dX)|| = ||R||`.
  have hopeq :
      frobNorm (lyapunovOp n A ΔX) =
        frobNorm
          (fun i j =>
            ΔC i j - matMul n ΔA X i j - matMul n X (matTranspose ΔA) i j) := by
    congr 1; ext i j; exact hLin i j
  -- Inverse-operator bound applied to `dX`.
  have hInvX := hInv ΔX
  rw [hopeq] at hInvX
  -- Structured RHS bound.
  have hrhs :=
    lyapunov_first_order_rhs_frobNorm_le n X ΔA ΔC α γ hα hγ
  have hTnn : 0 ≤ T := by
    rw [hT]; unfold lyapunovScaledPerturbationPairNorm; exact Real.sqrt_nonneg _
  -- Chain: ||dX|| <= M ||R|| <= M (2 a ||X|| + g) T.
  have hchain :
      frobNorm ΔX ≤ M * ((2 * α * frobNorm X + γ) * T) := by
    calc
      frobNorm ΔX
          ≤ M * frobNorm
              (fun i j =>
                ΔC i j - matMul n ΔA X i j -
                  matMul n X (matTranspose ΔA) i j) := hInvX
      _ ≤ M * ((2 * α * frobNorm X + γ) * T) :=
            mul_le_mul_of_nonneg_left hrhs hM
  -- Rewrite the certificate RHS `Psi * ||X|| * T` into `M (2 a ||X|| + g) T`.
  have hpsi :
      lyapunovCond_of_inverseOpBound n X α γ M * frobNorm X * T =
        M * ((2 * α * frobNorm X + γ) * T) := by
    unfold lyapunovCond_of_inverseOpBound
    field_simp
  rw [hpsi]
  exact hchain

/-- Higham, 2nd ed., §16.3, eq (16.27) (p. 317):
    a positive `SepLowerBound` certificate for `(A, -A^T)` instantiates the
    Lyapunov condition-number predicate with the safe inverse-operator constant
    `M = 1 / sigma`. This is a source-facing sep-based realization of the
    Lyapunov condition number; it is not the exact displayed operator norm when
    that norm is sharper. -/
theorem lyapunovCond_of_sepLowerBound_isLyapunovConditionFirstOrderBound (n : ℕ)
    (A X : Fin n → Fin n → ℝ) (α γ sigma : ℝ)
    (hα : 0 < α) (hγ : 0 < γ) (hsigma : 0 < sigma)
    (hX : 0 < frobNorm X)
    (hSep : SepLowerBound n A (fun i j => -matTranspose A i j) sigma) :
    LyapunovConditionFirstOrderBound n A X α γ
      (lyapunovCond_of_inverseOpBound n X α γ (1 / sigma)) := by
  have hInv := lyapunovInverseOpBound_of_sepLowerBound n A sigma hsigma hSep
  have hMnn : (0 : ℝ) ≤ 1 / sigma := by positivity
  exact lyapunovCond_of_inverseOpBound_isLyapunovConditionFirstOrderBound n
    A X α γ (1 / sigma) hα hγ hMnn hX hInv

/-- Higham, 2nd ed., Section 16.3-16.4, equations (16.26)-(16.27):
    a positive lower bound on the exact infimum model of `sep(A,-A^T)`
    instantiates the Lyapunov structured first-order condition certificate
    through the safe reciprocal condition value `1 / sigma`. -/
theorem lyapunovCond_of_pos_le_sylvesterSepInf_isLyapunovConditionFirstOrderBound
    (n : Nat)
    (A X : Fin n -> Fin n -> Real) (alpha gamma sigma : Real)
    (halpha : 0 < alpha) (hgamma : 0 < gamma) (hsigma : 0 < sigma)
    (hX : 0 < frobNorm X)
    (hle : sigma <= sylvesterSepInf n A (fun i j => -matTranspose A i j)) :
    LyapunovConditionFirstOrderBound n A X alpha gamma
      (lyapunovCond_of_inverseOpBound n X alpha gamma (1 / sigma)) := by
  exact
    lyapunovCond_of_sepLowerBound_isLyapunovConditionFirstOrderBound n
      A X alpha gamma sigma halpha hgamma hsigma hX
      (SepLowerBound_of_pos_le_sylvesterSepInf n A
        (fun i j => -matTranspose A i j) sigma hsigma hle)

/-- Higham, 2nd ed., Section 16.3, equation (16.27):
    source-numbered alias for turning a positive `SepLowerBound(A,-A^T)` into
    supplied Lyapunov inverse-operator data. -/
alias H16_eq16_27_lyapunovInverseOpBound_of_sepLowerBound :=
  lyapunovInverseOpBound_of_sepLowerBound

/-- Higham, 2nd ed., Section 16.3, equation (16.27):
    source-numbered alias for the supplied-inverse-bound Lyapunov
    condition-certificate constructor. -/
alias H16_eq16_27_lyapunovCond_of_inverseOpBound_isLyapunovConditionFirstOrderBound :=
  lyapunovCond_of_inverseOpBound_isLyapunovConditionFirstOrderBound

/-- Higham, 2nd ed., Section 16.3, equation (16.27):
    source-numbered alias for the sep-lower-bound Lyapunov
    condition-certificate constructor. -/
alias H16_eq16_27_lyapunovCond_of_sepLowerBound_isLyapunovConditionFirstOrderBound :=
  lyapunovCond_of_sepLowerBound_isLyapunovConditionFirstOrderBound

/-- Higham, 2nd ed., Section 16.3, equation (16.27):
    source-numbered alias for the exact-infimum Lyapunov
    condition-certificate constructor. -/
alias H16_eq16_27_lyapunovCond_of_pos_le_sylvesterSepInf_isLyapunovConditionFirstOrderBound :=
  lyapunovCond_of_pos_le_sylvesterSepInf_isLyapunovConditionFirstOrderBound

/-- Higham, 2nd ed., Chapter 16.3, equations (16.26)-(16.27):
    Frobenius Lyapunov perturbation bound from a supplied positive
    `SepLowerBound` certificate for `sep(A, -A^T)`.

    Scope: exact arithmetic and certificate transfer. This does not claim
    rounded arithmetic, automatic Schur production, or an estimator for
    `sigma`. -/
theorem lyapunov_perturbation_bound_of_sepLowerBound (n : Nat)
    (A X DeltaA DeltaC DeltaX : Fin n -> Fin n -> Real)
    (sigma : Real) (hsigma : 0 < sigma)
    (hSep : SepLowerBound n A (fun i j => -matTranspose A i j) sigma)
    (alpha gamma eps : Real)
    (halpha : 0 <= alpha) (hgamma : 0 <= gamma) (heps : 0 <= eps)
    (hDeltaA : frobNorm DeltaA <= eps * alpha)
    (hDeltaC : frobNorm DeltaC <= eps * gamma)
    (hLin : forall i j,
      sylvesterOp n A (fun i' j' => -matTranspose A i' j') DeltaX i j =
        DeltaC i j - matMul n DeltaA X i j +
          matMul n X (fun i' j' => -matTranspose DeltaA i' j') i j)
    (hDeltaX_ne : Not (frobNormSq DeltaX = 0)) :
    frobNorm DeltaX <=
      (1 / sigma) * (2 * alpha * frobNorm X + gamma) * eps := by
  exact
    lyapunov_perturbation_bound n A X DeltaA DeltaC DeltaX
      sigma hsigma hSep alpha gamma eps halpha hgamma heps
      hDeltaA hDeltaC hLin hDeltaX_ne

/-- Higham, 2nd ed., Chapter 16.3, equations (16.26)-(16.27):
    total Frobenius Lyapunov perturbation bound from a supplied positive
    `SepLowerBound` certificate for `sep(A, -A^T)`.

    This version removes the nonzero perturbation side condition by proving the
    zero-perturbation case directly. -/
theorem lyapunov_perturbation_bound_of_sepLowerBound_total (n : Nat)
    (A X DeltaA DeltaC DeltaX : Fin n -> Fin n -> Real)
    (sigma : Real) (hsigma : 0 < sigma)
    (hSep : SepLowerBound n A (fun i j => -matTranspose A i j) sigma)
    (alpha gamma eps : Real)
    (halpha : 0 <= alpha) (hgamma : 0 <= gamma) (heps : 0 <= eps)
    (hDeltaA : frobNorm DeltaA <= eps * alpha)
    (hDeltaC : frobNorm DeltaC <= eps * gamma)
    (hLin : forall i j,
      sylvesterOp n A (fun i' j' => -matTranspose A i' j') DeltaX i j =
        DeltaC i j - matMul n DeltaA X i j +
          matMul n X (fun i' j' => -matTranspose DeltaA i' j') i j) :
    frobNorm DeltaX <=
      (1 / sigma) * (2 * alpha * frobNorm X + gamma) * eps := by
  by_cases hDeltaX_ne : Not (frobNormSq DeltaX = 0)
  · exact
      lyapunov_perturbation_bound_of_sepLowerBound n
        A X DeltaA DeltaC DeltaX sigma hsigma hSep
        alpha gamma eps halpha hgamma heps hDeltaA hDeltaC hLin hDeltaX_ne
  · have hDeltaX_sq : frobNormSq DeltaX = 0 := Classical.not_not.mp hDeltaX_ne
    have hDeltaX : frobNorm DeltaX = 0 := by
      simp [frobNorm_eq_sqrt_frobNormSq, hDeltaX_sq]
    rw [hDeltaX]
    have hprod : 0 <= 2 * alpha * frobNorm X :=
      mul_nonneg (mul_nonneg (by positivity) halpha) (frobNorm_nonneg X)
    have hmiddle : 0 <= 2 * alpha * frobNorm X + gamma :=
      add_nonneg hprod hgamma
    exact mul_nonneg (mul_nonneg (by positivity) hmiddle) heps

/-- Higham, 2nd ed., Chapter 16.3, equations (16.26)-(16.27):
    relative Lyapunov perturbation bound from a supplied positive
    `SepLowerBound` certificate for `sep(A, -A^T)`.

    Scope: exact arithmetic and certificate transfer. The conclusion is the
    relative form of the perturbation inequality under the supplied separation
    certificate. -/
theorem lyapunov_relative_perturbation_of_sepLowerBound (n : Nat)
    (A X DeltaA DeltaC DeltaX : Fin n -> Fin n -> Real)
    (sigma : Real) (hsigma : 0 < sigma)
    (hSep : SepLowerBound n A (fun i j => -matTranspose A i j) sigma)
    (alpha gamma eps : Real)
    (halpha : 0 <= alpha) (hgamma : 0 <= gamma) (heps : 0 <= eps)
    (hDeltaA : frobNorm DeltaA <= eps * alpha)
    (hDeltaC : frobNorm DeltaC <= eps * gamma)
    (hLin : forall i j,
      sylvesterOp n A (fun i' j' => -matTranspose A i' j') DeltaX i j =
        DeltaC i j - matMul n DeltaA X i j +
          matMul n X (fun i' j' => -matTranspose DeltaA i' j') i j)
    (hDeltaX_ne : Not (frobNormSq DeltaX = 0))
    (hX_ne : Not (frobNorm X = 0))
    (hX_pos : 0 < frobNorm X) :
    frobNorm DeltaX / frobNorm X <=
      condSylvester n A (fun i j => -matTranspose A i j) X
        alpha alpha gamma sigma * eps := by
  have hDeltaB :
      frobNorm (fun i j => -matTranspose DeltaA i j) <= eps * alpha := by
    rw [show (fun i j => -matTranspose DeltaA i j) =
        (fun i j => -(matTranspose DeltaA) i j) from by ext i j; rfl]
    rw [frobNorm_neg, frobNorm_transpose]
    exact hDeltaA
  exact
    sylvester_relative_perturbation n A
      (fun i j => -matTranspose A i j) X DeltaA
      (fun i j => -matTranspose DeltaA i j) DeltaC DeltaX
      sigma hsigma hSep alpha alpha gamma eps halpha halpha hgamma heps
      hDeltaA hDeltaB hDeltaC hLin hDeltaX_ne hX_ne hX_pos

/-- Higham, 2nd ed., Chapter 16.3, equations (16.26)-(16.27):
    total relative Lyapunov perturbation bound from a supplied positive
    `SepLowerBound` certificate for `sep(A, -A^T)`.

    The total absolute theorem handles the zero perturbation case; this wrapper
    divides by the positive Frobenius norm of the exact solution. -/
theorem lyapunov_relative_perturbation_of_sepLowerBound_total (n : Nat)
    (A X DeltaA DeltaC DeltaX : Fin n -> Fin n -> Real)
    (sigma : Real) (hsigma : 0 < sigma)
    (hSep : SepLowerBound n A (fun i j => -matTranspose A i j) sigma)
    (alpha gamma eps : Real)
    (halpha : 0 <= alpha) (hgamma : 0 <= gamma) (heps : 0 <= eps)
    (hDeltaA : frobNorm DeltaA <= eps * alpha)
    (hDeltaC : frobNorm DeltaC <= eps * gamma)
    (hLin : forall i j,
      sylvesterOp n A (fun i' j' => -matTranspose A i' j') DeltaX i j =
        DeltaC i j - matMul n DeltaA X i j +
          matMul n X (fun i' j' => -matTranspose DeltaA i' j') i j)
    (hX_pos : 0 < frobNorm X) :
    frobNorm DeltaX / frobNorm X <=
      condSylvester n A (fun i j => -matTranspose A i j) X
        alpha alpha gamma sigma * eps := by
  have hAbs :=
    lyapunov_perturbation_bound_of_sepLowerBound_total n
      A X DeltaA DeltaC DeltaX sigma hsigma hSep
      alpha gamma eps halpha hgamma heps hDeltaA hDeltaC hLin
  calc
    frobNorm DeltaX / frobNorm X
        <= ((1 / sigma) * (2 * alpha * frobNorm X + gamma) * eps) /
            frobNorm X := div_le_div_of_nonneg_right hAbs (le_of_lt hX_pos)
    _ = condSylvester n A (fun i j => -matTranspose A i j) X
          alpha alpha gamma sigma * eps := by
        unfold condSylvester
        field_simp [hsigma.ne', hX_pos.ne']
        ring

/-- Higham, 2nd ed., Chapter 16.3-16.4, equations (16.26)-(16.27):
    Frobenius Lyapunov perturbation bound from a positive lower bound on the
    exact infimum model of `sep(A, -A^T)`.

    Scope: exact arithmetic and certificate transfer. This is not a rounded
    solve, Schur-production, or separation-estimation result. -/
theorem lyapunov_perturbation_bound_of_pos_le_sylvesterSepInf (n : Nat)
    (A X DeltaA DeltaC DeltaX : Fin n -> Fin n -> Real)
    (sigma : Real) (hsigma : 0 < sigma)
    (hle : sigma <= sylvesterSepInf n A (fun i j => -matTranspose A i j))
    (alpha gamma eps : Real)
    (halpha : 0 <= alpha) (hgamma : 0 <= gamma) (heps : 0 <= eps)
    (hDeltaA : frobNorm DeltaA <= eps * alpha)
    (hDeltaC : frobNorm DeltaC <= eps * gamma)
    (hLin : forall i j,
      sylvesterOp n A (fun i' j' => -matTranspose A i' j') DeltaX i j =
        DeltaC i j - matMul n DeltaA X i j +
          matMul n X (fun i' j' => -matTranspose DeltaA i' j') i j)
    (hDeltaX_ne : Not (frobNormSq DeltaX = 0)) :
    frobNorm DeltaX <=
      (1 / sigma) * (2 * alpha * frobNorm X + gamma) * eps := by
  exact
    lyapunov_perturbation_bound_of_sepLowerBound n
      A X DeltaA DeltaC DeltaX sigma hsigma
      (SepLowerBound_of_pos_le_sylvesterSepInf n A
        (fun i j => -matTranspose A i j) sigma hsigma hle)
      alpha gamma eps halpha hgamma heps hDeltaA hDeltaC hLin hDeltaX_ne

/-- Higham, 2nd ed., Chapter 16.3-16.4, equations (16.26)-(16.27):
    total Frobenius Lyapunov perturbation bound from a positive lower bound on
    the exact infimum model of `sep(A, -A^T)`.

    This routes through the total `SepLowerBound` wrapper. -/
theorem lyapunov_perturbation_bound_of_pos_le_sylvesterSepInf_total (n : Nat)
    (A X DeltaA DeltaC DeltaX : Fin n -> Fin n -> Real)
    (sigma : Real) (hsigma : 0 < sigma)
    (hle : sigma <= sylvesterSepInf n A (fun i j => -matTranspose A i j))
    (alpha gamma eps : Real)
    (halpha : 0 <= alpha) (hgamma : 0 <= gamma) (heps : 0 <= eps)
    (hDeltaA : frobNorm DeltaA <= eps * alpha)
    (hDeltaC : frobNorm DeltaC <= eps * gamma)
    (hLin : forall i j,
      sylvesterOp n A (fun i' j' => -matTranspose A i' j') DeltaX i j =
        DeltaC i j - matMul n DeltaA X i j +
          matMul n X (fun i' j' => -matTranspose DeltaA i' j') i j) :
    frobNorm DeltaX <=
      (1 / sigma) * (2 * alpha * frobNorm X + gamma) * eps := by
  exact
    lyapunov_perturbation_bound_of_sepLowerBound_total n
      A X DeltaA DeltaC DeltaX sigma hsigma
      (SepLowerBound_of_pos_le_sylvesterSepInf n A
        (fun i j => -matTranspose A i j) sigma hsigma hle)
      alpha gamma eps halpha hgamma heps hDeltaA hDeltaC hLin

/-- Higham, 2nd ed., Chapter 16.3-16.4, equations (16.26)-(16.27):
    relative Lyapunov perturbation bound from a positive lower bound on the
    exact infimum model of `sep(A, -A^T)`.

    Scope: exact arithmetic and certificate transfer. The theorem only
    transfers the supplied exact-infimum certificate into the existing
    Lyapunov/Sylvester perturbation theorem. -/
theorem lyapunov_relative_perturbation_of_pos_le_sylvesterSepInf (n : Nat)
    (A X DeltaA DeltaC DeltaX : Fin n -> Fin n -> Real)
    (sigma : Real) (hsigma : 0 < sigma)
    (hle : sigma <= sylvesterSepInf n A (fun i j => -matTranspose A i j))
    (alpha gamma eps : Real)
    (halpha : 0 <= alpha) (hgamma : 0 <= gamma) (heps : 0 <= eps)
    (hDeltaA : frobNorm DeltaA <= eps * alpha)
    (hDeltaC : frobNorm DeltaC <= eps * gamma)
    (hLin : forall i j,
      sylvesterOp n A (fun i' j' => -matTranspose A i' j') DeltaX i j =
        DeltaC i j - matMul n DeltaA X i j +
          matMul n X (fun i' j' => -matTranspose DeltaA i' j') i j)
    (hDeltaX_ne : Not (frobNormSq DeltaX = 0))
    (hX_ne : Not (frobNorm X = 0))
    (hX_pos : 0 < frobNorm X) :
    frobNorm DeltaX / frobNorm X <=
      condSylvester n A (fun i j => -matTranspose A i j) X
        alpha alpha gamma sigma * eps := by
  exact
    lyapunov_relative_perturbation_of_sepLowerBound n
      A X DeltaA DeltaC DeltaX sigma hsigma
      (SepLowerBound_of_pos_le_sylvesterSepInf n A
        (fun i j => -matTranspose A i j) sigma hsigma hle)
      alpha gamma eps halpha hgamma heps hDeltaA hDeltaC hLin
      hDeltaX_ne hX_ne hX_pos

/-- Higham, 2nd ed., Chapter 16.3-16.4, equations (16.26)-(16.27):
    total relative Lyapunov perturbation bound from a positive lower bound on
    the exact infimum model of `sep(A, -A^T)`.

    This routes through the total `SepLowerBound` wrapper and divides by
    `||X||_F`. -/
theorem lyapunov_relative_perturbation_of_pos_le_sylvesterSepInf_total (n : Nat)
    (A X DeltaA DeltaC DeltaX : Fin n -> Fin n -> Real)
    (sigma : Real) (hsigma : 0 < sigma)
    (hle : sigma <= sylvesterSepInf n A (fun i j => -matTranspose A i j))
    (alpha gamma eps : Real)
    (halpha : 0 <= alpha) (hgamma : 0 <= gamma) (heps : 0 <= eps)
    (hDeltaA : frobNorm DeltaA <= eps * alpha)
    (hDeltaC : frobNorm DeltaC <= eps * gamma)
    (hLin : forall i j,
      sylvesterOp n A (fun i' j' => -matTranspose A i' j') DeltaX i j =
        DeltaC i j - matMul n DeltaA X i j +
          matMul n X (fun i' j' => -matTranspose DeltaA i' j') i j)
    (hX_pos : 0 < frobNorm X) :
    frobNorm DeltaX / frobNorm X <=
      condSylvester n A (fun i j => -matTranspose A i j) X
        alpha alpha gamma sigma * eps := by
  exact
    lyapunov_relative_perturbation_of_sepLowerBound_total n
      A X DeltaA DeltaC DeltaX sigma hsigma
      (SepLowerBound_of_pos_le_sylvesterSepInf n A
        (fun i j => -matTranspose A i j) sigma hsigma hle)
      alpha gamma eps halpha hgamma heps hDeltaA hDeltaC hLin hX_pos

/-- Higham, 2nd ed., Chapter 16.3, equation (16.27):
    source-numbered alias for the total sep-certificate Lyapunov perturbation
    bound. -/
theorem H16_eq16_27_lyapunov_perturbation_bound_of_sepLowerBound_total
    (n : Nat)
    (A X DeltaA DeltaC DeltaX : Fin n -> Fin n -> Real)
    (sigma : Real) (hsigma : 0 < sigma)
    (hSep : SepLowerBound n A (fun i j => -matTranspose A i j) sigma)
    (alpha gamma eps : Real)
    (halpha : 0 <= alpha) (hgamma : 0 <= gamma) (heps : 0 <= eps)
    (hDeltaA : frobNorm DeltaA <= eps * alpha)
    (hDeltaC : frobNorm DeltaC <= eps * gamma)
    (hLin : forall i j,
      sylvesterOp n A (fun i' j' => -matTranspose A i' j') DeltaX i j =
        DeltaC i j - matMul n DeltaA X i j +
          matMul n X (fun i' j' => -matTranspose DeltaA i' j') i j) :
    frobNorm DeltaX <=
      (1 / sigma) * (2 * alpha * frobNorm X + gamma) * eps := by
  exact
    lyapunov_perturbation_bound_of_sepLowerBound_total n
      A X DeltaA DeltaC DeltaX sigma hsigma hSep
      alpha gamma eps halpha hgamma heps hDeltaA hDeltaC hLin

/-- Higham, 2nd ed., Chapter 16.3, equation (16.27):
    source-numbered alias for the total relative sep-certificate Lyapunov
    perturbation bound. -/
theorem H16_eq16_27_lyapunov_relative_perturbation_of_sepLowerBound_total
    (n : Nat)
    (A X DeltaA DeltaC DeltaX : Fin n -> Fin n -> Real)
    (sigma : Real) (hsigma : 0 < sigma)
    (hSep : SepLowerBound n A (fun i j => -matTranspose A i j) sigma)
    (alpha gamma eps : Real)
    (halpha : 0 <= alpha) (hgamma : 0 <= gamma) (heps : 0 <= eps)
    (hDeltaA : frobNorm DeltaA <= eps * alpha)
    (hDeltaC : frobNorm DeltaC <= eps * gamma)
    (hLin : forall i j,
      sylvesterOp n A (fun i' j' => -matTranspose A i' j') DeltaX i j =
        DeltaC i j - matMul n DeltaA X i j +
          matMul n X (fun i' j' => -matTranspose DeltaA i' j') i j)
    (hX_pos : 0 < frobNorm X) :
    frobNorm DeltaX / frobNorm X <=
      condSylvester n A (fun i j => -matTranspose A i j) X
        alpha alpha gamma sigma * eps := by
  exact
    lyapunov_relative_perturbation_of_sepLowerBound_total n
      A X DeltaA DeltaC DeltaX sigma hsigma hSep
      alpha gamma eps halpha hgamma heps hDeltaA hDeltaC hLin hX_pos

/-- Higham, 2nd ed., Chapter 16.3, equations (16.26)-(16.27):
    source-numbered alias for the total exact-infimum Lyapunov perturbation
    bound. -/
theorem H16_eq16_27_lyapunov_perturbation_bound_of_pos_le_sylvesterSepInf_total
    (n : Nat)
    (A X DeltaA DeltaC DeltaX : Fin n -> Fin n -> Real)
    (sigma : Real) (hsigma : 0 < sigma)
    (hle : sigma <= sylvesterSepInf n A (fun i j => -matTranspose A i j))
    (alpha gamma eps : Real)
    (halpha : 0 <= alpha) (hgamma : 0 <= gamma) (heps : 0 <= eps)
    (hDeltaA : frobNorm DeltaA <= eps * alpha)
    (hDeltaC : frobNorm DeltaC <= eps * gamma)
    (hLin : forall i j,
      sylvesterOp n A (fun i' j' => -matTranspose A i' j') DeltaX i j =
        DeltaC i j - matMul n DeltaA X i j +
          matMul n X (fun i' j' => -matTranspose DeltaA i' j') i j) :
    frobNorm DeltaX <=
      (1 / sigma) * (2 * alpha * frobNorm X + gamma) * eps := by
  exact
    lyapunov_perturbation_bound_of_pos_le_sylvesterSepInf_total n
      A X DeltaA DeltaC DeltaX sigma hsigma hle
      alpha gamma eps halpha hgamma heps hDeltaA hDeltaC hLin

/-- Higham, 2nd ed., Chapter 16.3, equations (16.26)-(16.27):
    source-numbered alias for the total relative exact-infimum Lyapunov
    perturbation bound. -/
theorem H16_eq16_27_lyapunov_relative_perturbation_of_pos_le_sylvesterSepInf_total
    (n : Nat)
    (A X DeltaA DeltaC DeltaX : Fin n -> Fin n -> Real)
    (sigma : Real) (hsigma : 0 < sigma)
    (hle : sigma <= sylvesterSepInf n A (fun i j => -matTranspose A i j))
    (alpha gamma eps : Real)
    (halpha : 0 <= alpha) (hgamma : 0 <= gamma) (heps : 0 <= eps)
    (hDeltaA : frobNorm DeltaA <= eps * alpha)
    (hDeltaC : frobNorm DeltaC <= eps * gamma)
    (hLin : forall i j,
      sylvesterOp n A (fun i' j' => -matTranspose A i' j') DeltaX i j =
        DeltaC i j - matMul n DeltaA X i j +
          matMul n X (fun i' j' => -matTranspose DeltaA i' j') i j)
    (hX_pos : 0 < frobNorm X) :
    frobNorm DeltaX / frobNorm X <=
      condSylvester n A (fun i j => -matTranspose A i j) X
        alpha alpha gamma sigma * eps := by
  exact
    lyapunov_relative_perturbation_of_pos_le_sylvesterSepInf_total n
      A X DeltaA DeltaC DeltaX sigma hsigma hle
      alpha gamma eps halpha hgamma heps hDeltaA hDeltaC hLin hX_pos

/-- Higham, 2nd ed., Section 16.3, equation (16.27):
    source-facing sep-based first-order Lyapunov bound before the
    `sqrt 2 * eps` relative wrapper. This simply applies the structured
    Lyapunov condition certificate instantiated by
    `lyapunovCond_of_sepLowerBound_isLyapunovConditionFirstOrderBound` to a
    supplied linearized perturbation equation. -/
theorem lyapunov_first_order_bound_of_sepLowerBound (n : Nat)
    (A X DeltaA DeltaC DeltaX : Fin n -> Fin n -> Real)
    (alpha gamma sigma : Real)
    (halpha : 0 < alpha) (hgamma : 0 < gamma)
    (hsigma : 0 < sigma) (hX : 0 < frobNorm X)
    (hSep : SepLowerBound n A (fun i j => -matTranspose A i j) sigma)
    (hLin : forall i j,
      lyapunovOp n A DeltaX i j =
        DeltaC i j - matMul n DeltaA X i j -
          matMul n X (matTranspose DeltaA) i j) :
    frobNorm DeltaX <=
      lyapunovCond_of_inverseOpBound n X alpha gamma (1 / sigma) *
        frobNorm X *
        lyapunovScaledPerturbationPairNorm n DeltaA DeltaC alpha gamma := by
  exact
    (lyapunovCond_of_sepLowerBound_isLyapunovConditionFirstOrderBound n
      A X alpha gamma sigma halpha hgamma hsigma hX hSep)
      DeltaA DeltaC DeltaX hLin

/-- Higham, 2nd ed., Section 16.3-16.4, equations (16.26)-(16.27):
    source-facing first-order Lyapunov bound from a positive lower bound on
    the exact infimum model of `sep(A,-A^T)`, exposed before the relative
    `sqrt 2 * eps` wrapper. -/
theorem lyapunov_first_order_bound_of_pos_le_sylvesterSepInf (n : Nat)
    (A X DeltaA DeltaC DeltaX : Fin n -> Fin n -> Real)
    (alpha gamma sigma : Real)
    (halpha : 0 < alpha) (hgamma : 0 < gamma)
    (hsigma : 0 < sigma) (hX : 0 < frobNorm X)
    (hle : sigma <= sylvesterSepInf n A (fun i j => -matTranspose A i j))
    (hLin : forall i j,
      lyapunovOp n A DeltaX i j =
        DeltaC i j - matMul n DeltaA X i j -
          matMul n X (matTranspose DeltaA) i j) :
    frobNorm DeltaX <=
      lyapunovCond_of_inverseOpBound n X alpha gamma (1 / sigma) *
        frobNorm X *
        lyapunovScaledPerturbationPairNorm n DeltaA DeltaC alpha gamma := by
  exact
    (lyapunovCond_of_pos_le_sylvesterSepInf_isLyapunovConditionFirstOrderBound n
      A X alpha gamma sigma halpha hgamma hsigma hX hle)
      DeltaA DeltaC DeltaX hLin

/-- Higham, 2nd ed., Chapter 16.3, equation (16.27):
    source-numbered alias for the raw sep-based first-order Lyapunov bound. -/
alias H16_eq16_27_lyapunov_first_order_bound_of_sepLowerBound :=
  lyapunov_first_order_bound_of_sepLowerBound

/-- Higham, 2nd ed., Chapter 16.3, equations (16.26)-(16.27):
    source-numbered alias for the raw exact-infimum first-order Lyapunov bound. -/
alias H16_eq16_27_lyapunov_first_order_bound_of_pos_le_sylvesterSepInf :=
  lyapunov_first_order_bound_of_pos_le_sylvesterSepInf

/-- Higham, 2nd ed., §16.3, eq (16.27) (p. 317):
    sep-based Lyapunov first-order perturbation bound. If
    `SepLowerBound A (-A^T) sigma` holds, then the printed relative bound
    follows with the safe condition-number value
    `lyapunovCond_of_inverseOpBound ... (1 / sigma)`.

    Scope: this is an exact-arithmetic theorem from a supplied sep lower-bound
    certificate. It does not compute the sharper nondiagonal operator norm
    `||P^{-1}[...]||`. -/
theorem H16_eq16_27_lyapunov_condition_of_sepLowerBound (n : ℕ)
    (A X ΔA ΔC ΔX : Fin n → Fin n → ℝ)
    (α γ sigma ε : ℝ)
    (hα : 0 < α) (hγ : 0 < γ)
    (hsigma : 0 < sigma) (hε : 0 ≤ ε)
    (hX : 0 < frobNorm X)
    (hSep : SepLowerBound n A (fun i j => -matTranspose A i j) sigma)
    (hΔA : frobNorm ΔA ≤ ε * α)
    (hΔC : frobNorm ΔC ≤ ε * γ)
    (hLin : ∀ i j,
      lyapunovOp n A ΔX i j =
        ΔC i j - matMul n ΔA X i j - matMul n X (matTranspose ΔA) i j) :
    frobNorm ΔX / frobNorm X ≤
      Real.sqrt 2 *
        lyapunovCond_of_inverseOpBound n X α γ (1 / sigma) * ε := by
  have hCond :=
    lyapunovCond_of_sepLowerBound_isLyapunovConditionFirstOrderBound n
      A X α γ sigma hα hγ hsigma hX hSep
  have hΨnn : 0 ≤ lyapunovCond_of_inverseOpBound n X α γ (1 / sigma) := by
    unfold lyapunovCond_of_inverseOpBound
    have hMnn : (0 : ℝ) ≤ 1 / sigma := by positivity
    have hnum : 0 ≤ 2 * α * frobNorm X + γ := by
      have hXnn : 0 ≤ frobNorm X := le_of_lt hX
      nlinarith [le_of_lt hα, le_of_lt hγ, hXnn]
    positivity
  exact lyapunov_relative_first_order_bound_of_condition n
    A X ΔA ΔC ΔX α γ
    (lyapunovCond_of_inverseOpBound n X α γ (1 / sigma)) ε
    hCond hX hΨnn hα hγ hε hΔA hΔC hLin

/-- Higham, 2nd ed., §16.3-§16.4, equations (16.26)-(16.27):
    Lyapunov first-order perturbation bound from a positive lower bound on the
    exact infimum model of `sep(A,-A^T)`.  This is the same safe condition
    value as the `SepLowerBound` route, but exposes the printed infimum/minimum
    surface directly. -/
theorem H16_eq16_27_lyapunov_condition_of_pos_le_sylvesterSepInf (n : Nat)
    (A X DeltaA DeltaC DeltaX : Fin n -> Fin n -> Real)
    (alpha gamma sigma eps : Real)
    (halpha : 0 < alpha) (hgamma : 0 < gamma)
    (hsigma : 0 < sigma) (heps : 0 <= eps)
    (hX : 0 < frobNorm X)
    (hle : sigma <= sylvesterSepInf n A (fun i j => -matTranspose A i j))
    (hDeltaA : frobNorm DeltaA <= eps * alpha)
    (hDeltaC : frobNorm DeltaC <= eps * gamma)
    (hLin : forall i j,
      lyapunovOp n A DeltaX i j =
        DeltaC i j - matMul n DeltaA X i j -
          matMul n X (matTranspose DeltaA) i j) :
    frobNorm DeltaX / frobNorm X <=
      Real.sqrt 2 *
        lyapunovCond_of_inverseOpBound n X alpha gamma (1 / sigma) * eps := by
  exact
    H16_eq16_27_lyapunov_condition_of_sepLowerBound n
      A X DeltaA DeltaC DeltaX alpha gamma sigma eps
      halpha hgamma hsigma heps hX
      (SepLowerBound_of_pos_le_sylvesterSepInf n A
        (fun i j => -matTranspose A i j) sigma hsigma hle)
      hDeltaA hDeltaC hLin

/-- Higham, 2nd ed., Section 16.3, equation (16.27):
    sep-based relative first-order Lyapunov perturbation bound with the safe
    condition value `lyapunovCond_of_inverseOpBound ... (1 / sigma)`. -/
theorem lyapunov_relative_first_order_bound_of_sepLowerBound (n : Nat)
    (A X DeltaA DeltaC DeltaX : Fin n -> Fin n -> Real)
    (alpha gamma sigma eps : Real)
    (halpha : 0 < alpha) (hgamma : 0 < gamma)
    (hsigma : 0 < sigma) (heps : 0 <= eps)
    (hX : 0 < frobNorm X)
    (hSep : SepLowerBound n A (fun i j => -matTranspose A i j) sigma)
    (hDeltaA : frobNorm DeltaA <= eps * alpha)
    (hDeltaC : frobNorm DeltaC <= eps * gamma)
    (hLin : forall i j,
      lyapunovOp n A DeltaX i j =
        DeltaC i j - matMul n DeltaA X i j -
          matMul n X (matTranspose DeltaA) i j) :
    frobNorm DeltaX / frobNorm X <=
      Real.sqrt 2 *
        lyapunovCond_of_inverseOpBound n X alpha gamma (1 / sigma) * eps := by
  exact
    H16_eq16_27_lyapunov_condition_of_sepLowerBound n
      A X DeltaA DeltaC DeltaX alpha gamma sigma eps
      halpha hgamma hsigma heps hX hSep
      hDeltaA hDeltaC hLin

/-- Higham, 2nd ed., Section 16.3-16.4, equations (16.26)-(16.27):
    relative first-order Lyapunov perturbation bound from a positive lower
    bound on the exact infimum model of `sep(A,-A^T)`. -/
theorem lyapunov_relative_first_order_bound_of_pos_le_sylvesterSepInf
    (n : Nat)
    (A X DeltaA DeltaC DeltaX : Fin n -> Fin n -> Real)
    (alpha gamma sigma eps : Real)
    (halpha : 0 < alpha) (hgamma : 0 < gamma)
    (hsigma : 0 < sigma) (heps : 0 <= eps)
    (hX : 0 < frobNorm X)
    (hle : sigma <= sylvesterSepInf n A (fun i j => -matTranspose A i j))
    (hDeltaA : frobNorm DeltaA <= eps * alpha)
    (hDeltaC : frobNorm DeltaC <= eps * gamma)
    (hLin : forall i j,
      lyapunovOp n A DeltaX i j =
        DeltaC i j - matMul n DeltaA X i j -
          matMul n X (matTranspose DeltaA) i j) :
    frobNorm DeltaX / frobNorm X <=
      Real.sqrt 2 *
        lyapunovCond_of_inverseOpBound n X alpha gamma (1 / sigma) * eps := by
  exact
    H16_eq16_27_lyapunov_condition_of_pos_le_sylvesterSepInf n
      A X DeltaA DeltaC DeltaX alpha gamma sigma eps
      halpha hgamma hsigma heps hX hle
      hDeltaA hDeltaC hLin

/-- Higham, 2nd ed., Chapter 16.3, equation (16.27):
    source-numbered alias for the relative first-order sep-certificate
    Lyapunov perturbation bound. -/
theorem H16_eq16_27_lyapunov_relative_first_order_bound_of_sepLowerBound
    (n : Nat)
    (A X DeltaA DeltaC DeltaX : Fin n -> Fin n -> Real)
    (alpha gamma sigma eps : Real)
    (halpha : 0 < alpha) (hgamma : 0 < gamma)
    (hsigma : 0 < sigma) (heps : 0 <= eps)
    (hX : 0 < frobNorm X)
    (hSep : SepLowerBound n A (fun i j => -matTranspose A i j) sigma)
    (hDeltaA : frobNorm DeltaA <= eps * alpha)
    (hDeltaC : frobNorm DeltaC <= eps * gamma)
    (hLin : forall i j,
      lyapunovOp n A DeltaX i j =
        DeltaC i j - matMul n DeltaA X i j -
          matMul n X (matTranspose DeltaA) i j) :
    frobNorm DeltaX / frobNorm X <=
      Real.sqrt 2 *
        lyapunovCond_of_inverseOpBound n X alpha gamma (1 / sigma) * eps := by
  exact
    lyapunov_relative_first_order_bound_of_sepLowerBound n
      A X DeltaA DeltaC DeltaX alpha gamma sigma eps
      halpha hgamma hsigma heps hX hSep
      hDeltaA hDeltaC hLin

/-- Higham, 2nd ed., Chapter 16.3, equations (16.26)-(16.27):
    source-numbered alias for the relative first-order exact-infimum Lyapunov
    perturbation bound. -/
theorem H16_eq16_27_lyapunov_relative_first_order_bound_of_pos_le_sylvesterSepInf
    (n : Nat)
    (A X DeltaA DeltaC DeltaX : Fin n -> Fin n -> Real)
    (alpha gamma sigma eps : Real)
    (halpha : 0 < alpha) (hgamma : 0 < gamma)
    (hsigma : 0 < sigma) (heps : 0 <= eps)
    (hX : 0 < frobNorm X)
    (hle : sigma <= sylvesterSepInf n A (fun i j => -matTranspose A i j))
    (hDeltaA : frobNorm DeltaA <= eps * alpha)
    (hDeltaC : frobNorm DeltaC <= eps * gamma)
    (hLin : forall i j,
      lyapunovOp n A DeltaX i j =
        DeltaC i j - matMul n DeltaA X i j -
          matMul n X (matTranspose DeltaA) i j) :
    frobNorm DeltaX / frobNorm X <=
      Real.sqrt 2 *
        lyapunovCond_of_inverseOpBound n X alpha gamma (1 / sigma) * eps := by
  exact
    lyapunov_relative_first_order_bound_of_pos_le_sylvesterSepInf n
      A X DeltaA DeltaC DeltaX alpha gamma sigma eps
      halpha hgamma hsigma heps hX hle
      hDeltaA hDeltaC hLin

-- ============================================================
-- A posteriori source wrappers from Chapter 16.4
-- ============================================================

/-- Higham, 2nd ed., Chapter 16.4, equation (16.28):
    a supplied exact `SepLowerBound` certificate for `sep(A,-A^T)`
    instantiates the Lyapunov a posteriori error-residual bound.

    Scope: exact arithmetic and certificate transfer. The residual in the
    conclusion is the Lyapunov residual `C - (A Xhat + Xhat A^T)`. -/
theorem lyapunov_aposteriori_bound_of_sepLowerBound (n : Nat)
    (A C X Xhat : Fin n -> Fin n -> Real)
    (sigma : Real)
    (hSep : SepLowerBound n A (fun i j => -matTranspose A i j) sigma)
    (hExact : forall i j, lyapunovOp n A X i j = C i j)
    (hE_ne : Not (frobNormSq (fun i j => X i j - Xhat i j) = 0)) :
    frobNorm (fun i j => X i j - Xhat i j) <=
      (1 / sigma) * frobNorm (lyapunovResidual n A C Xhat) := by
  have hExactSylv :
      forall i j,
        sylvesterOp n A (fun i j => -matTranspose A i j) X i j = C i j := by
    intro i j
    rw [<- lyapunovOp_eq_sylvesterOp n A X]
    exact hExact i j
  have h :=
    sylvester_aposteriori_bound_of_sepLowerBound n A
      (fun i j => -matTranspose A i j) C X Xhat sigma hSep hExactSylv hE_ne
  simpa [lyapunovResidual_eq_sylvesterResidual_special n A C Xhat] using h

/-- Higham, 2nd ed., Chapter 16.4, equation (16.28):
    the source-shaped relative Lyapunov a posteriori bound follows from a
    supplied exact `SepLowerBound` certificate for `sep(A,-A^T)`.

    Scope: exact arithmetic and certificate transfer, divided by the norm of
    the exact Lyapunov solution. -/
theorem lyapunov_relative_aposteriori_bound_of_sepLowerBound (n : Nat)
    (A C X Xhat : Fin n -> Fin n -> Real)
    (sigma : Real)
    (hSep : SepLowerBound n A (fun i j => -matTranspose A i j) sigma)
    (hExact : forall i j, lyapunovOp n A X i j = C i j)
    (hE_ne : Not (frobNormSq (fun i j => X i j - Xhat i j) = 0))
    (hX_pos : 0 < frobNorm X) :
    frobNorm (fun i j => X i j - Xhat i j) / frobNorm X <=
      ((1 / sigma) * frobNorm (lyapunovResidual n A C Xhat)) /
        frobNorm X := by
  have hExactSylv :
      forall i j,
        sylvesterOp n A (fun i j => -matTranspose A i j) X i j = C i j := by
    intro i j
    rw [<- lyapunovOp_eq_sylvesterOp n A X]
    exact hExact i j
  have h :=
    sylvester_relative_aposteriori_bound_of_sepLowerBound n A
      (fun i j => -matTranspose A i j) C X Xhat sigma hSep hExactSylv hE_ne
      hX_pos
  simpa [lyapunovResidual_eq_sylvesterResidual_special n A C Xhat] using h

/-- Higham, 2nd ed., Chapter 16.4, equations (16.26) and (16.28):
    a positive lower bound on the exact infimum model of `sep(A,-A^T)`
    instantiates the Lyapunov a posteriori error-residual bound.

    Scope: exact arithmetic and certificate transfer from the exact-infimum
    separation model. -/
theorem lyapunov_aposteriori_bound_of_pos_le_sylvesterSepInf (n : Nat)
    (A C X Xhat : Fin n -> Fin n -> Real)
    (sigma : Real) (hsigma : 0 < sigma)
    (hle : sigma <= sylvesterSepInf n A (fun i j => -matTranspose A i j))
    (hExact : forall i j, lyapunovOp n A X i j = C i j)
    (hE_ne : Not (frobNormSq (fun i j => X i j - Xhat i j) = 0)) :
    frobNorm (fun i j => X i j - Xhat i j) <=
      (1 / sigma) * frobNorm (lyapunovResidual n A C Xhat) := by
  exact
    lyapunov_aposteriori_bound_of_sepLowerBound n A C X Xhat sigma
      (SepLowerBound_of_pos_le_sylvesterSepInf n A
        (fun i j => -matTranspose A i j) sigma hsigma hle)
      hExact hE_ne

/-- Higham, 2nd ed., Chapter 16.4, equations (16.26) and (16.28):
    the source-shaped relative Lyapunov a posteriori bound follows from a
    positive lower bound on the exact infimum model of `sep(A,-A^T)`.

    Scope: exact arithmetic and certificate transfer, divided by the norm of
    the exact Lyapunov solution. -/
theorem lyapunov_relative_aposteriori_bound_of_pos_le_sylvesterSepInf
    (n : Nat)
    (A C X Xhat : Fin n -> Fin n -> Real)
    (sigma : Real) (hsigma : 0 < sigma)
    (hle : sigma <= sylvesterSepInf n A (fun i j => -matTranspose A i j))
    (hExact : forall i j, lyapunovOp n A X i j = C i j)
    (hE_ne : Not (frobNormSq (fun i j => X i j - Xhat i j) = 0))
    (hX_pos : 0 < frobNorm X) :
    frobNorm (fun i j => X i j - Xhat i j) / frobNorm X <=
      ((1 / sigma) * frobNorm (lyapunovResidual n A C Xhat)) /
        frobNorm X := by
  exact
    lyapunov_relative_aposteriori_bound_of_sepLowerBound n A C X Xhat sigma
      (SepLowerBound_of_pos_le_sylvesterSepInf n A
        (fun i j => -matTranspose A i j) sigma hsigma hle)
      hExact hE_ne hX_pos

/-- Higham, 2nd ed., Chapter 16.4, equation (16.28):
    source-numbered alias for the sep-certificate Lyapunov a posteriori
    residual-error bound, preserving the explicit nonzero-error side condition. -/
alias H16_eq16_28_lyapunov_aposteriori_bound_of_sepLowerBound :=
  lyapunov_aposteriori_bound_of_sepLowerBound

/-- Higham, 2nd ed., Chapter 16.4, equation (16.28):
    source-numbered alias for the relative sep-certificate Lyapunov
    a posteriori residual-error bound, preserving the explicit nonzero-error
    and positive-solution-norm side conditions. -/
alias H16_eq16_28_lyapunov_relative_aposteriori_bound_of_sepLowerBound :=
  lyapunov_relative_aposteriori_bound_of_sepLowerBound

/-- Higham, 2nd ed., Chapter 16.4, equations (16.26) and (16.28):
    source-numbered alias for the exact-infimum Lyapunov a posteriori
    residual-error bound, preserving the explicit nonzero-error side condition. -/
alias H16_eq16_28_lyapunov_aposteriori_bound_of_pos_le_sylvesterSepInf :=
  lyapunov_aposteriori_bound_of_pos_le_sylvesterSepInf

/-- Higham, 2nd ed., Chapter 16.4, equations (16.26) and (16.28):
    source-numbered alias for the relative exact-infimum Lyapunov a posteriori
    residual-error bound, preserving the explicit nonzero-error and
    positive-solution-norm side conditions. -/
alias H16_eq16_28_lyapunov_relative_aposteriori_bound_of_pos_le_sylvesterSepInf :=
  lyapunov_relative_aposteriori_bound_of_pos_le_sylvesterSepInf

/-- Higham, 2nd ed., Chapter 16.4, equation (16.28):
    total source-facing Lyapunov a posteriori error-residual bound from a
    supplied exact `SepLowerBound` certificate for `sep(A,-A^T)`.

    This version removes the nonzero error side condition by proving the
    zero-error case directly. -/
theorem lyapunov_aposteriori_bound_of_sepLowerBound_total (n : Nat)
    (A C X Xhat : Fin n -> Fin n -> Real)
    (sigma : Real)
    (hSep : SepLowerBound n A (fun i j => -matTranspose A i j) sigma)
    (hExact : forall i j, lyapunovOp n A X i j = C i j) :
    frobNorm (fun i j => X i j - Xhat i j) <=
      (1 / sigma) * frobNorm (lyapunovResidual n A C Xhat) := by
  by_cases hE_ne :
      Not (frobNormSq (fun i j => X i j - Xhat i j) = 0)
  · exact
      lyapunov_aposteriori_bound_of_sepLowerBound n A C X Xhat sigma
        hSep hExact hE_ne
  · have hE_sq :
        frobNormSq (fun i j => X i j - Xhat i j) = 0 :=
      Classical.not_not.mp hE_ne
    have hE :
        frobNorm (fun i j => X i j - Xhat i j) = 0 := by
      simp [frobNorm_eq_sqrt_frobNormSq, hE_sq]
    have hsigma : 0 < sigma := hSep.1
    rw [hE]
    exact mul_nonneg (by positivity) (frobNorm_nonneg _)

/-- Higham, 2nd ed., Chapter 16.4, equation (16.28):
    total relative Lyapunov a posteriori error-residual bound from a supplied
    exact `SepLowerBound` certificate for `sep(A,-A^T)`.

    The absolute total theorem handles zero error; this wrapper only divides by
    the positive norm of the exact solution. -/
theorem lyapunov_relative_aposteriori_bound_of_sepLowerBound_total (n : Nat)
    (A C X Xhat : Fin n -> Fin n -> Real)
    (sigma : Real)
    (hSep : SepLowerBound n A (fun i j => -matTranspose A i j) sigma)
    (hExact : forall i j, lyapunovOp n A X i j = C i j)
    (hX_pos : 0 < frobNorm X) :
    frobNorm (fun i j => X i j - Xhat i j) / frobNorm X <=
      ((1 / sigma) * frobNorm (lyapunovResidual n A C Xhat)) /
        frobNorm X := by
  have hAbs :=
    lyapunov_aposteriori_bound_of_sepLowerBound_total n A C X Xhat sigma
      hSep hExact
  exact div_le_div_of_nonneg_right hAbs (le_of_lt hX_pos)

/-- Higham, 2nd ed., Chapter 16.4, equations (16.26) and (16.28):
    total Lyapunov a posteriori error-residual bound from a positive lower
    bound on the exact infimum model of `sep(A,-A^T)`.

    This routes through the total `SepLowerBound` wrapper. -/
theorem lyapunov_aposteriori_bound_of_pos_le_sylvesterSepInf_total (n : Nat)
    (A C X Xhat : Fin n -> Fin n -> Real)
    (sigma : Real) (hsigma : 0 < sigma)
    (hle : sigma <= sylvesterSepInf n A (fun i j => -matTranspose A i j))
    (hExact : forall i j, lyapunovOp n A X i j = C i j) :
    frobNorm (fun i j => X i j - Xhat i j) <=
      (1 / sigma) * frobNorm (lyapunovResidual n A C Xhat) := by
  exact
    lyapunov_aposteriori_bound_of_sepLowerBound_total n A C X Xhat sigma
      (SepLowerBound_of_pos_le_sylvesterSepInf n A
        (fun i j => -matTranspose A i j) sigma hsigma hle)
      hExact

/-- Higham, 2nd ed., Chapter 16.4, equations (16.26) and (16.28):
    total relative Lyapunov a posteriori error-residual bound from a positive
    lower bound on the exact infimum model of `sep(A,-A^T)`.

    This routes through the total `SepLowerBound` wrapper and divides by
    `||X||_F`. -/
theorem lyapunov_relative_aposteriori_bound_of_pos_le_sylvesterSepInf_total
    (n : Nat)
    (A C X Xhat : Fin n -> Fin n -> Real)
    (sigma : Real) (hsigma : 0 < sigma)
    (hle : sigma <= sylvesterSepInf n A (fun i j => -matTranspose A i j))
    (hExact : forall i j, lyapunovOp n A X i j = C i j)
    (hX_pos : 0 < frobNorm X) :
    frobNorm (fun i j => X i j - Xhat i j) / frobNorm X <=
      ((1 / sigma) * frobNorm (lyapunovResidual n A C Xhat)) /
        frobNorm X := by
  exact
    lyapunov_relative_aposteriori_bound_of_sepLowerBound_total n
      A C X Xhat sigma
      (SepLowerBound_of_pos_le_sylvesterSepInf n A
        (fun i j => -matTranspose A i j) sigma hsigma hle)
      hExact hX_pos

/-- Higham, 2nd ed., Chapter 16.4, equation (16.28):
    source-numbered alias for the total sep-certificate Lyapunov a posteriori
    residual-error bound. -/
theorem H16_eq16_28_lyapunov_aposteriori_bound_of_sepLowerBound_total
    (n : Nat)
    (A C X Xhat : Fin n -> Fin n -> Real)
    (sigma : Real)
    (hSep : SepLowerBound n A (fun i j => -matTranspose A i j) sigma)
    (hExact : forall i j, lyapunovOp n A X i j = C i j) :
    frobNorm (fun i j => X i j - Xhat i j) <=
      (1 / sigma) * frobNorm (lyapunovResidual n A C Xhat) := by
  exact
    lyapunov_aposteriori_bound_of_sepLowerBound_total n
      A C X Xhat sigma hSep hExact

/-- Higham, 2nd ed., Chapter 16.4, equation (16.28):
    source-numbered alias for the total relative sep-certificate Lyapunov
    a posteriori residual-error bound. -/
theorem H16_eq16_28_lyapunov_relative_aposteriori_bound_of_sepLowerBound_total
    (n : Nat)
    (A C X Xhat : Fin n -> Fin n -> Real)
    (sigma : Real)
    (hSep : SepLowerBound n A (fun i j => -matTranspose A i j) sigma)
    (hExact : forall i j, lyapunovOp n A X i j = C i j)
    (hX_pos : 0 < frobNorm X) :
    frobNorm (fun i j => X i j - Xhat i j) / frobNorm X <=
      ((1 / sigma) * frobNorm (lyapunovResidual n A C Xhat)) /
        frobNorm X := by
  exact
    lyapunov_relative_aposteriori_bound_of_sepLowerBound_total n
      A C X Xhat sigma hSep hExact hX_pos

/-- Higham, 2nd ed., Chapter 16.4, equations (16.26) and (16.28):
    source-numbered alias for the total exact-infimum Lyapunov a posteriori
    residual-error bound. -/
theorem H16_eq16_28_lyapunov_aposteriori_bound_of_pos_le_sylvesterSepInf_total
    (n : Nat)
    (A C X Xhat : Fin n -> Fin n -> Real)
    (sigma : Real) (hsigma : 0 < sigma)
    (hle : sigma <= sylvesterSepInf n A (fun i j => -matTranspose A i j))
    (hExact : forall i j, lyapunovOp n A X i j = C i j) :
    frobNorm (fun i j => X i j - Xhat i j) <=
      (1 / sigma) * frobNorm (lyapunovResidual n A C Xhat) := by
  exact
    lyapunov_aposteriori_bound_of_pos_le_sylvesterSepInf_total n
      A C X Xhat sigma hsigma hle hExact

/-- Higham, 2nd ed., Chapter 16.4, equations (16.26) and (16.28):
    source-numbered alias for the total relative exact-infimum Lyapunov
    a posteriori residual-error bound. -/
theorem H16_eq16_28_lyapunov_relative_aposteriori_bound_of_pos_le_sylvesterSepInf_total
    (n : Nat)
    (A C X Xhat : Fin n -> Fin n -> Real)
    (sigma : Real) (hsigma : 0 < sigma)
    (hle : sigma <= sylvesterSepInf n A (fun i j => -matTranspose A i j))
    (hExact : forall i j, lyapunovOp n A X i j = C i j)
    (hX_pos : 0 < frobNorm X) :
    frobNorm (fun i j => X i j - Xhat i j) / frobNorm X <=
      ((1 / sigma) * frobNorm (lyapunovResidual n A C Xhat)) /
        frobNorm X := by
  exact
    lyapunov_relative_aposteriori_bound_of_pos_le_sylvesterSepInf_total n
      A C X Xhat sigma hsigma hle hExact hX_pos

-- ============================================================
-- Diagonal-case condition-number realization
-- (eq (16.27), diagonal / distinct-eigenvalue)
-- ============================================================

/-- Higham, 2nd ed., §16.1, eqs (16.1)-(16.3), diagonal Lyapunov case (p. 307):
    in diagonal coordinates the Lyapunov operator `A Y + Y A^T` acts entrywise as
    multiplication by `a_i + a_j`.  Uses the Lyapunov = Sylvester(`B = -A^T`)
    identity together with the diagonal Sylvester-apply lemma of `Higham16.lean`
    (with `b = -a`). -/
theorem lyapunovOp_diagonal_apply (n : ℕ)
    (a : Fin n → ℝ) (Y : Fin n → Fin n → ℝ) (i j : Fin n) :
    lyapunovOp n (Matrix.diagonal a) Y i j = (a i + a j) * Y i j := by
  -- `-diag(a)^T = diag(-a)` as a function.
  have hB :
      (fun i' j' => -matTranspose (Matrix.diagonal a) i' j') =
        (Matrix.diagonal fun k => -a k) := by
    ext p q
    simp only [matTranspose, Matrix.diagonal]
    by_cases hpq : q = p
    · subst hpq; simp
    · have hpq' : p ≠ q := fun h => hpq h.symm
      simp [hpq, hpq']
  rw [lyapunovOp_eq_sylvesterOp, hB]
  have h := sylvesterOpRect_diagonal_apply n n a (fun k => -a k) Y i j
  rw [sylvesterOpRect_square_eq_sylvesterOp] at h
  rw [h]; ring

/-- Higham, 2nd ed., §16.1, eq (16.3), diagonal Lyapunov case (p. 307):
    from an entrywise separation lower bound `s <= |a_i + a_j|` (with `s > 0`,
    the explicit inverse of the diagonal Lyapunov coefficient has every entry
    `(a_i + a_j)^{-1}` bounded by `1/s`), the diagonal Lyapunov operator
    satisfies the inverse-operator bound with `M = 1/s`.  This is the concrete
    `||P^{-1}||`-type constant for the separated diagonal case: no SVD is
    needed. -/
theorem lyapunovInverseOpBound_diagonal (n : ℕ)
    (a : Fin n → ℝ) (s : ℝ) (hs : 0 < s)
    (hsep : ∀ i j, s ≤ |a i + a j|) :
    LyapunovInverseOpBound n (Matrix.diagonal a) (1 / s) := by
  intro Y
  -- entrywise: |Y i j| <= (1/s) * |L(Y) i j|.
  have hentry : ∀ i j : Fin n,
      |Y i j| ≤ (1 / s) * |lyapunovOp n (Matrix.diagonal a) Y i j| := by
    intro i j
    have happ := lyapunovOp_diagonal_apply n a Y i j
    rw [happ, abs_mul]
    -- goal: |Y i j| <= (1/s) * (|a_i + a_j| * |Y i j|).
    have hYnn : 0 ≤ |Y i j| := abs_nonneg _
    have hlow : s ≤ |a i + a j| := hsep i j
    rw [one_div, ← mul_assoc]
    -- reduce to 1 * |Y| <= (s⁻¹ |a+a|) * |Y| using s⁻¹|a+a| >= 1.
    have hcoeff : (1 : ℝ) ≤ s ⁻¹ * |a i + a j| := by
      rw [le_inv_mul_iff₀ hs, mul_one]; exact hlow
    calc |Y i j| = 1 * |Y i j| := (one_mul _).symm
      _ ≤ (s ⁻¹ * |a i + a j|) * |Y i j| :=
            mul_le_mul_of_nonneg_right hcoeff hYnn
  -- Frobenius from entrywise via the library helper.
  have hMnn : (0 : ℝ) ≤ 1 / s := by positivity
  exact frobNorm_le_const_mul_frobNorm_of_entrywise_abs_le Y
    (lyapunovOp n (Matrix.diagonal a) Y) hMnn hentry

/-- Higham, 2nd ed., Chapter 16.4, equation (16.26), diagonal Lyapunov case:
    an entrywise lower bound on all sums `|a_i + a_j|` gives a
    `SepLowerBound` certificate for `(diag a, -(diag a)^T)`. -/
theorem SepLowerBound_lyapunov_diagonal_of_entrywise_abs_ge (n : Nat)
    (a : Fin n -> Real) (s : Real) (hs : 0 < s)
    (hsep : forall i j, s <= |a i + a j|) :
    SepLowerBound n (Matrix.diagonal a)
      (fun i j => -matTranspose (Matrix.diagonal a) i j) s := by
  have hB :
      (fun i j => -matTranspose (Matrix.diagonal a) i j) =
        (Matrix.diagonal fun k => -a k) := by
    ext p q
    simp only [matTranspose, Matrix.diagonal]
    by_cases hpq : q = p
    · subst hpq
      simp
    · have hpq' : p ≠ q := fun h => hpq h.symm
      simp [hpq, hpq']
  have hgap : forall i j, s <= |a i - (fun k : Fin n => -a k) j| := by
    intro i j
    simpa [sub_eq_add_neg] using hsep i j
  rw [hB]
  exact
    SepLowerBound_diagonal_of_entrywise_abs_ge n a
      (fun k : Fin n => -a k) s hs hgap

/-- Higham, 2nd ed., Chapter 16.4, equation (16.26), diagonal Lyapunov case:
    in positive dimension, the same entrywise sum gap is below the exact
    infimum model of `sep(diag a, -(diag a)^T)`. -/
theorem sylvesterSepInf_lyapunov_diagonal_ge_of_entrywise_abs_ge (n : Nat)
    (a : Fin n -> Real) (s : Real) (hs : 0 < s)
    (hsep : forall i j, s <= |a i + a j|)
    (hn : 0 < n) :
    s <= sylvesterSepInf n (Matrix.diagonal a)
      (fun i j => -matTranspose (Matrix.diagonal a) i j) := by
  exact
    SepLowerBound_le_sylvesterSepInf_of_pos_dim n (Matrix.diagonal a)
      (fun i j => -matTranspose (Matrix.diagonal a) i j) s
      (SepLowerBound_lyapunov_diagonal_of_entrywise_abs_ge n a s hs hsep)
      hn

/-- Higham, 2nd ed., Chapter 16.4, equation (16.26): source-numbered
    alias for the diagonal Lyapunov `sep(A,-A^T)` lower-bound certificate. -/
alias H16_eq16_26_SepLowerBound_lyapunov_diagonal_of_entrywise_abs_ge :=
  SepLowerBound_lyapunov_diagonal_of_entrywise_abs_ge

/-- Higham, 2nd ed., Chapter 16.4, equation (16.26): source-numbered
    alias for the diagonal Lyapunov exact-infimum lower-bound route. -/
alias H16_eq16_26_sylvesterSepInf_lyapunov_diagonal_ge_of_entrywise_abs_ge :=
  sylvesterSepInf_lyapunov_diagonal_ge_of_entrywise_abs_ge

/-- Higham, 2nd ed., Chapter 16.3, equations (16.26)-(16.27), diagonal
    Lyapunov case: Frobenius perturbation bound from the entrywise certificate
    `s <= |a_i + a_j|`. -/
theorem lyapunov_perturbation_bound_diagonal (n : Nat)
    (a : Fin n -> Real) (X DeltaA DeltaC DeltaX : Fin n -> Fin n -> Real)
    (s : Real) (hs : 0 < s)
    (hsep : forall i j, s <= |a i + a j|)
    (alpha gamma eps : Real)
    (halpha : 0 <= alpha) (hgamma : 0 <= gamma) (heps : 0 <= eps)
    (hDeltaA : frobNorm DeltaA <= eps * alpha)
    (hDeltaC : frobNorm DeltaC <= eps * gamma)
    (hLin : forall i j,
      sylvesterOp n (Matrix.diagonal a)
          (fun i' j' => -matTranspose (Matrix.diagonal a) i' j') DeltaX i j =
        DeltaC i j - matMul n DeltaA X i j +
          matMul n X (fun i' j' => -matTranspose DeltaA i' j') i j)
    (hDeltaX_ne : Not (frobNormSq DeltaX = 0)) :
    frobNorm DeltaX <=
      (1 / s) * (2 * alpha * frobNorm X + gamma) * eps := by
  exact
    lyapunov_perturbation_bound_of_sepLowerBound n (Matrix.diagonal a)
      X DeltaA DeltaC DeltaX s hs
      (SepLowerBound_lyapunov_diagonal_of_entrywise_abs_ge n a s hs hsep)
      alpha gamma eps halpha hgamma heps hDeltaA hDeltaC hLin hDeltaX_ne

/-- Higham, 2nd ed., Chapter 16.3, equations (16.26)-(16.27), diagonal
    Lyapunov case: relative perturbation bound from the entrywise certificate
    `s <= |a_i + a_j|`. -/
theorem lyapunov_relative_perturbation_diagonal (n : Nat)
    (a : Fin n -> Real) (X DeltaA DeltaC DeltaX : Fin n -> Fin n -> Real)
    (s : Real) (hs : 0 < s)
    (hsep : forall i j, s <= |a i + a j|)
    (alpha gamma eps : Real)
    (halpha : 0 <= alpha) (hgamma : 0 <= gamma) (heps : 0 <= eps)
    (hDeltaA : frobNorm DeltaA <= eps * alpha)
    (hDeltaC : frobNorm DeltaC <= eps * gamma)
    (hLin : forall i j,
      sylvesterOp n (Matrix.diagonal a)
          (fun i' j' => -matTranspose (Matrix.diagonal a) i' j') DeltaX i j =
        DeltaC i j - matMul n DeltaA X i j +
          matMul n X (fun i' j' => -matTranspose DeltaA i' j') i j)
    (hDeltaX_ne : Not (frobNormSq DeltaX = 0))
    (hX_ne : Not (frobNorm X = 0))
    (hX_pos : 0 < frobNorm X) :
    frobNorm DeltaX / frobNorm X <=
      condSylvester n (Matrix.diagonal a)
        (fun i j => -matTranspose (Matrix.diagonal a) i j) X
        alpha alpha gamma s * eps := by
  exact
    lyapunov_relative_perturbation_of_sepLowerBound n (Matrix.diagonal a)
      X DeltaA DeltaC DeltaX s hs
      (SepLowerBound_lyapunov_diagonal_of_entrywise_abs_ge n a s hs hsep)
      alpha gamma eps halpha hgamma heps hDeltaA hDeltaC hLin
      hDeltaX_ne hX_ne hX_pos

/-- Higham, 2nd ed., Chapter 16.3, equations (16.26)-(16.27), diagonal
    Lyapunov case: total Frobenius perturbation bound from the entrywise
    certificate `s <= |a_i + a_j|`. -/
theorem lyapunov_perturbation_bound_diagonal_total (n : Nat)
    (a : Fin n -> Real) (X DeltaA DeltaC DeltaX : Fin n -> Fin n -> Real)
    (s : Real) (hs : 0 < s)
    (hsep : forall i j, s <= |a i + a j|)
    (alpha gamma eps : Real)
    (halpha : 0 <= alpha) (hgamma : 0 <= gamma) (heps : 0 <= eps)
    (hDeltaA : frobNorm DeltaA <= eps * alpha)
    (hDeltaC : frobNorm DeltaC <= eps * gamma)
    (hLin : forall i j,
      sylvesterOp n (Matrix.diagonal a)
          (fun i' j' => -matTranspose (Matrix.diagonal a) i' j') DeltaX i j =
        DeltaC i j - matMul n DeltaA X i j +
          matMul n X (fun i' j' => -matTranspose DeltaA i' j') i j) :
    frobNorm DeltaX <=
      (1 / s) * (2 * alpha * frobNorm X + gamma) * eps := by
  exact
    lyapunov_perturbation_bound_of_sepLowerBound_total n (Matrix.diagonal a)
      X DeltaA DeltaC DeltaX s hs
      (SepLowerBound_lyapunov_diagonal_of_entrywise_abs_ge n a s hs hsep)
      alpha gamma eps halpha hgamma heps hDeltaA hDeltaC hLin

/-- Higham, 2nd ed., Chapter 16.3, equations (16.26)-(16.27), diagonal
    Lyapunov case: total relative perturbation bound from the entrywise
    certificate `s <= |a_i + a_j|`. -/
theorem lyapunov_relative_perturbation_diagonal_total (n : Nat)
    (a : Fin n -> Real) (X DeltaA DeltaC DeltaX : Fin n -> Fin n -> Real)
    (s : Real) (hs : 0 < s)
    (hsep : forall i j, s <= |a i + a j|)
    (alpha gamma eps : Real)
    (halpha : 0 <= alpha) (hgamma : 0 <= gamma) (heps : 0 <= eps)
    (hDeltaA : frobNorm DeltaA <= eps * alpha)
    (hDeltaC : frobNorm DeltaC <= eps * gamma)
    (hLin : forall i j,
      sylvesterOp n (Matrix.diagonal a)
          (fun i' j' => -matTranspose (Matrix.diagonal a) i' j') DeltaX i j =
        DeltaC i j - matMul n DeltaA X i j +
          matMul n X (fun i' j' => -matTranspose DeltaA i' j') i j)
    (hX_pos : 0 < frobNorm X) :
    frobNorm DeltaX / frobNorm X <=
      condSylvester n (Matrix.diagonal a)
        (fun i j => -matTranspose (Matrix.diagonal a) i j) X
        alpha alpha gamma s * eps := by
  exact
    lyapunov_relative_perturbation_of_sepLowerBound_total n (Matrix.diagonal a)
      X DeltaA DeltaC DeltaX s hs
      (SepLowerBound_lyapunov_diagonal_of_entrywise_abs_ge n a s hs hsep)
      alpha gamma eps halpha hgamma heps hDeltaA hDeltaC hLin hX_pos

/-- Higham, 2nd ed., Chapter 16.3, equation (16.27), diagonal case:
    source-numbered alias for the total diagonal Lyapunov perturbation
    bound. -/
theorem H16_eq16_27_lyapunov_perturbation_bound_diagonal_total
    (n : Nat)
    (a : Fin n -> Real) (X DeltaA DeltaC DeltaX : Fin n -> Fin n -> Real)
    (s : Real) (hs : 0 < s)
    (hsep : forall i j, s <= |a i + a j|)
    (alpha gamma eps : Real)
    (halpha : 0 <= alpha) (hgamma : 0 <= gamma) (heps : 0 <= eps)
    (hDeltaA : frobNorm DeltaA <= eps * alpha)
    (hDeltaC : frobNorm DeltaC <= eps * gamma)
    (hLin : forall i j,
      sylvesterOp n (Matrix.diagonal a)
          (fun i' j' => -matTranspose (Matrix.diagonal a) i' j') DeltaX i j =
        DeltaC i j - matMul n DeltaA X i j +
          matMul n X (fun i' j' => -matTranspose DeltaA i' j') i j) :
    frobNorm DeltaX <=
      (1 / s) * (2 * alpha * frobNorm X + gamma) * eps := by
  exact
    lyapunov_perturbation_bound_diagonal_total n
      a X DeltaA DeltaC DeltaX s hs hsep
      alpha gamma eps halpha hgamma heps hDeltaA hDeltaC hLin

/-- Higham, 2nd ed., Chapter 16.3, equation (16.27), diagonal case:
    source-numbered alias for the total relative diagonal Lyapunov
    perturbation bound. -/
theorem H16_eq16_27_lyapunov_relative_perturbation_diagonal_total
    (n : Nat)
    (a : Fin n -> Real) (X DeltaA DeltaC DeltaX : Fin n -> Fin n -> Real)
    (s : Real) (hs : 0 < s)
    (hsep : forall i j, s <= |a i + a j|)
    (alpha gamma eps : Real)
    (halpha : 0 <= alpha) (hgamma : 0 <= gamma) (heps : 0 <= eps)
    (hDeltaA : frobNorm DeltaA <= eps * alpha)
    (hDeltaC : frobNorm DeltaC <= eps * gamma)
    (hLin : forall i j,
      sylvesterOp n (Matrix.diagonal a)
          (fun i' j' => -matTranspose (Matrix.diagonal a) i' j') DeltaX i j =
        DeltaC i j - matMul n DeltaA X i j +
          matMul n X (fun i' j' => -matTranspose DeltaA i' j') i j)
    (hX_pos : 0 < frobNorm X) :
    frobNorm DeltaX / frobNorm X <=
      condSylvester n (Matrix.diagonal a)
        (fun i j => -matTranspose (Matrix.diagonal a) i j) X
        alpha alpha gamma s * eps := by
  exact
    lyapunov_relative_perturbation_diagonal_total n
      a X DeltaA DeltaC DeltaX s hs hsep
      alpha gamma eps halpha hgamma heps hDeltaA hDeltaC hLin hX_pos

/-- Higham, 2nd ed., Chapter 16.4, equation (16.28), diagonal Lyapunov case:
    an entrywise lower bound on `|a_i + a_j|` gives the residual-error bound. -/
theorem lyapunov_aposteriori_bound_diagonal (n : Nat)
    (a : Fin n -> Real) (C X Xhat : Fin n -> Fin n -> Real)
    (s : Real) (hs : 0 < s)
    (hsep : forall i j, s <= |a i + a j|)
    (hExact : forall i j,
      lyapunovOp n (Matrix.diagonal a) X i j = C i j)
    (hE_ne : Not (frobNormSq (fun i j => X i j - Xhat i j) = 0)) :
    frobNorm (fun i j => X i j - Xhat i j) <=
      (1 / s) * frobNorm (lyapunovResidual n (Matrix.diagonal a) C Xhat) := by
  have hB :
      (fun i j => -matTranspose (Matrix.diagonal a) i j) =
        (Matrix.diagonal fun k => -a k) := by
    ext p q
    simp only [matTranspose, Matrix.diagonal]
    by_cases hpq : q = p
    · subst hpq
      simp
    · have hpq' : p ≠ q := fun h => hpq h.symm
      simp [hpq, hpq']
  have hgap : forall i j, s <= |a i - (fun k : Fin n => -a k) j| := by
    intro i j
    simpa [sub_eq_add_neg] using hsep i j
  have hSep :
      SepLowerBound n (Matrix.diagonal a)
        (fun i j => -matTranspose (Matrix.diagonal a) i j) s := by
    rw [hB]
    exact
      SepLowerBound_diagonal_of_entrywise_abs_ge n a
        (fun k : Fin n => -a k) s hs hgap
  exact
    lyapunov_aposteriori_bound_of_sepLowerBound n (Matrix.diagonal a)
      C X Xhat s hSep hExact hE_ne

/-- Higham, 2nd ed., Chapter 16.4, equation (16.28), diagonal Lyapunov case:
    the relative residual-error bound follows from the same entrywise gap. -/
theorem lyapunov_relative_aposteriori_bound_diagonal (n : Nat)
    (a : Fin n -> Real) (C X Xhat : Fin n -> Fin n -> Real)
    (s : Real) (hs : 0 < s)
    (hsep : forall i j, s <= |a i + a j|)
    (hExact : forall i j,
      lyapunovOp n (Matrix.diagonal a) X i j = C i j)
    (hE_ne : Not (frobNormSq (fun i j => X i j - Xhat i j) = 0))
    (hX_pos : 0 < frobNorm X) :
    frobNorm (fun i j => X i j - Xhat i j) / frobNorm X <=
      ((1 / s) *
        frobNorm (lyapunovResidual n (Matrix.diagonal a) C Xhat)) /
        frobNorm X := by
  have hB :
      (fun i j => -matTranspose (Matrix.diagonal a) i j) =
        (Matrix.diagonal fun k => -a k) := by
    ext p q
    simp only [matTranspose, Matrix.diagonal]
    by_cases hpq : q = p
    · subst hpq
      simp
    · have hpq' : p ≠ q := fun h => hpq h.symm
      simp [hpq, hpq']
  have hgap : forall i j, s <= |a i - (fun k : Fin n => -a k) j| := by
    intro i j
    simpa [sub_eq_add_neg] using hsep i j
  have hSep :
      SepLowerBound n (Matrix.diagonal a)
        (fun i j => -matTranspose (Matrix.diagonal a) i j) s := by
    rw [hB]
    exact
      SepLowerBound_diagonal_of_entrywise_abs_ge n a
        (fun k : Fin n => -a k) s hs hgap
  exact
    lyapunov_relative_aposteriori_bound_of_sepLowerBound n
      (Matrix.diagonal a) C X Xhat s hSep hExact hE_ne hX_pos

/-- Higham, 2nd ed., Chapter 16.4, equation (16.28), diagonal case:
    source-numbered alias for the direct diagonal Lyapunov a posteriori
    residual-error bound, preserving the explicit nonzero-error side condition. -/
alias H16_eq16_28_lyapunov_aposteriori_bound_diagonal :=
  lyapunov_aposteriori_bound_diagonal

/-- Higham, 2nd ed., Chapter 16.4, equation (16.28), diagonal case:
    source-numbered alias for the relative direct diagonal Lyapunov a posteriori
    residual-error bound, preserving the explicit nonzero-error and
    positive-solution-norm side conditions. -/
alias H16_eq16_28_lyapunov_relative_aposteriori_bound_diagonal :=
  lyapunov_relative_aposteriori_bound_diagonal

/-- Higham, 2nd ed., Chapter 16.4, equation (16.28), diagonal Lyapunov case:
    total residual-error bound from an entrywise lower bound on `|a_i + a_j|`.

    The zero-error case is handled by the total `SepLowerBound` wrapper. -/
theorem lyapunov_aposteriori_bound_diagonal_total (n : Nat)
    (a : Fin n -> Real) (C X Xhat : Fin n -> Fin n -> Real)
    (s : Real) (hs : 0 < s)
    (hsep : forall i j, s <= |a i + a j|)
    (hExact : forall i j,
      lyapunovOp n (Matrix.diagonal a) X i j = C i j) :
    frobNorm (fun i j => X i j - Xhat i j) <=
      (1 / s) * frobNorm (lyapunovResidual n (Matrix.diagonal a) C Xhat) := by
  exact
    lyapunov_aposteriori_bound_of_sepLowerBound_total n (Matrix.diagonal a)
      C X Xhat s
      (SepLowerBound_lyapunov_diagonal_of_entrywise_abs_ge n a s hs hsep)
      hExact

/-- Higham, 2nd ed., Chapter 16.4, equation (16.28), diagonal Lyapunov case:
    total relative residual-error bound from the same entrywise sum gap.

    This routes through the total `SepLowerBound` wrapper and divides by
    `||X||_F`. -/
theorem lyapunov_relative_aposteriori_bound_diagonal_total (n : Nat)
    (a : Fin n -> Real) (C X Xhat : Fin n -> Fin n -> Real)
    (s : Real) (hs : 0 < s)
    (hsep : forall i j, s <= |a i + a j|)
    (hExact : forall i j,
      lyapunovOp n (Matrix.diagonal a) X i j = C i j)
    (hX_pos : 0 < frobNorm X) :
    frobNorm (fun i j => X i j - Xhat i j) / frobNorm X <=
      ((1 / s) *
        frobNorm (lyapunovResidual n (Matrix.diagonal a) C Xhat)) /
        frobNorm X := by
  exact
    lyapunov_relative_aposteriori_bound_of_sepLowerBound_total n
      (Matrix.diagonal a) C X Xhat s
      (SepLowerBound_lyapunov_diagonal_of_entrywise_abs_ge n a s hs hsep)
      hExact hX_pos

/-- Higham, 2nd ed., Chapter 16.4, equation (16.28), diagonal case:
    source-numbered alias for the total diagonal Lyapunov a posteriori
    residual-error bound. -/
theorem H16_eq16_28_lyapunov_aposteriori_bound_diagonal_total
    (n : Nat)
    (a : Fin n -> Real) (C X Xhat : Fin n -> Fin n -> Real)
    (s : Real) (hs : 0 < s)
    (hsep : forall i j, s <= |a i + a j|)
    (hExact : forall i j,
      lyapunovOp n (Matrix.diagonal a) X i j = C i j) :
    frobNorm (fun i j => X i j - Xhat i j) <=
      (1 / s) * frobNorm (lyapunovResidual n (Matrix.diagonal a) C Xhat) := by
  exact
    lyapunov_aposteriori_bound_diagonal_total n
      a C X Xhat s hs hsep hExact

/-- Higham, 2nd ed., Chapter 16.4, equation (16.28), diagonal case:
    source-numbered alias for the total relative diagonal Lyapunov
    a posteriori residual-error bound. -/
theorem H16_eq16_28_lyapunov_relative_aposteriori_bound_diagonal_total
    (n : Nat)
    (a : Fin n -> Real) (C X Xhat : Fin n -> Fin n -> Real)
    (s : Real) (hs : 0 < s)
    (hsep : forall i j, s <= |a i + a j|)
    (hExact : forall i j,
      lyapunovOp n (Matrix.diagonal a) X i j = C i j)
    (hX_pos : 0 < frobNorm X) :
    frobNorm (fun i j => X i j - Xhat i j) / frobNorm X <=
      ((1 / s) *
        frobNorm (lyapunovResidual n (Matrix.diagonal a) C Xhat)) /
        frobNorm X := by
  exact
    lyapunov_relative_aposteriori_bound_diagonal_total n
      a C X Xhat s hs hsep hExact hX_pos

/-- Higham, 2nd ed., §16.3, eq (16.27), diagonal case (p. 317):
    the concrete structured Lyapunov condition number for the separated diagonal
    operator, with the explicit inverse-operator constant `1/s` coming from the
    diagonal Lyapunov coefficient (entries `(a_i + a_j)^{-1}`, each bounded by
    `1/s`):
      `lyapunovCondDiagonal = (1/s) * (2 * alpha * ||X||_F + gamma) / ||X||_F`. -/
noncomputable def lyapunovCondDiagonal (n : ℕ)
    (X : Fin n → Fin n → ℝ) (α γ s : ℝ) : ℝ :=
  lyapunovCond_of_inverseOpBound n X α γ (1 / s)

/-- Higham, 2nd ed., Section 16.3, equation (16.27), diagonal case:
    source-numbered abbreviation for the explicit diagonal Lyapunov condition
    number value. -/
noncomputable abbrev H16_eq16_27_lyapunovCondDiagonal :=
  lyapunovCondDiagonal

/-- Higham, 2nd ed., §16.3, eq (16.27), diagonal case (p. 317):
    the diagonal structured condition number `lyapunovCondDiagonal` satisfies the
    certificate predicate `LyapunovConditionFirstOrderBound` for the separated
    diagonal Lyapunov operator `A = diag a`.  This CLOSES (16.27) for the
    diagonalizable / distinct-eigenvalue case (eigenvalues `a_i` of `A`, all
    pairwise sums `a_i + a_j` separated by `s`). -/
theorem lyapunovCondDiagonal_isLyapunovConditionFirstOrderBound (n : ℕ)
    (a : Fin n → ℝ) (X : Fin n → Fin n → ℝ) (α γ s : ℝ)
    (hα : 0 < α) (hγ : 0 < γ) (hs : 0 < s)
    (hX : 0 < frobNorm X)
    (hsep : ∀ i j, s ≤ |a i + a j|) :
    LyapunovConditionFirstOrderBound n (Matrix.diagonal a) X
      α γ (lyapunovCondDiagonal n X α γ s) := by
  have hInv := lyapunovInverseOpBound_diagonal n a s hs hsep
  have hMnn : (0 : ℝ) ≤ 1 / s := by positivity
  unfold lyapunovCondDiagonal
  exact lyapunovCond_of_inverseOpBound_isLyapunovConditionFirstOrderBound n
    (Matrix.diagonal a) X α γ (1 / s)
    hα hγ hMnn hX hInv

/-- Higham, 2nd ed., Section 16.3, equation (16.27), diagonal case:
    source-numbered alias for the diagonal Lyapunov condition certificate. -/
alias H16_eq16_27_lyapunovCondDiagonal_isLyapunovConditionFirstOrderBound :=
  lyapunovCondDiagonal_isLyapunovConditionFirstOrderBound

-- ============================================================
-- Labeled (16.27) wrapper for the diagonal case
-- ============================================================

/-- Higham, 2nd ed., §16.3, eq (16.27), diagonal case (p. 317):
    the printed structured relative first-order perturbation bound
      `||dX||_F / ||X||_F <= sqrt 2 * Psi * eps`
    with the CONCRETE diagonal Lyapunov condition number
    `Psi = lyapunovCondDiagonal`.

    Hypotheses: `A = diag a` with entrywise pair-sum separation `s`, data
    weights `alpha, gamma`, normwise data budgets `||dA|| <= eps*alpha`,
    `||dC|| <= eps*gamma`, and the linearized first-order Lyapunov equation
    `A dX + dX A^T = dC - dA X - X dA^T`.

    Honest scope: this is the (16.27) closure for the separated diagonal
    (equivalently: distinct-eigenvalue, diagonalized) Lyapunov equation. -/
theorem H16_eq16_27_lyapunov_condition_diagonal (n : ℕ)
    (a : Fin n → ℝ) (X ΔA ΔC ΔX : Fin n → Fin n → ℝ)
    (α γ s ε : ℝ)
    (hα : 0 < α) (hγ : 0 < γ) (hs : 0 < s) (hε : 0 ≤ ε)
    (hX : 0 < frobNorm X)
    (hsep : ∀ i j, s ≤ |a i + a j|)
    (hΔA : frobNorm ΔA ≤ ε * α)
    (hΔC : frobNorm ΔC ≤ ε * γ)
    (hLin : ∀ i j,
      lyapunovOp n (Matrix.diagonal a) ΔX i j =
        ΔC i j - matMul n ΔA X i j - matMul n X (matTranspose ΔA) i j) :
    frobNorm ΔX / frobNorm X ≤
      Real.sqrt 2 * lyapunovCondDiagonal n X α γ s * ε := by
  have hCond :=
    lyapunovCondDiagonal_isLyapunovConditionFirstOrderBound n a X α γ s
      hα hγ hs hX hsep
  have hΨnn : 0 ≤ lyapunovCondDiagonal n X α γ s := by
    unfold lyapunovCondDiagonal lyapunovCond_of_inverseOpBound
    have h1 : (0 : ℝ) ≤ 1 / s := by positivity
    have h2 : 0 ≤ 2 * α * frobNorm X + γ := by
      have := frobNorm_nonneg X; nlinarith
    positivity
  exact lyapunov_relative_first_order_bound_of_condition n
    (Matrix.diagonal a) X ΔA ΔC ΔX
    α γ (lyapunovCondDiagonal n X α γ s) ε
    hCond hX hΨnn hα hγ hε hΔA hΔC hLin

/-- Higham, 2nd ed., Section 16.3, equation (16.27), diagonal case:
    relative first-order Lyapunov perturbation bound with the concrete
    diagonal condition number `lyapunovCondDiagonal`. -/
theorem lyapunov_relative_first_order_bound_diagonal (n : Nat)
    (a : Fin n -> Real) (X DeltaA DeltaC DeltaX : Fin n -> Fin n -> Real)
    (alpha gamma s eps : Real)
    (halpha : 0 < alpha) (hgamma : 0 < gamma)
    (hs : 0 < s) (heps : 0 <= eps)
    (hX : 0 < frobNorm X)
    (hsep : forall i j, s <= |a i + a j|)
    (hDeltaA : frobNorm DeltaA <= eps * alpha)
    (hDeltaC : frobNorm DeltaC <= eps * gamma)
    (hLin : forall i j,
      lyapunovOp n (Matrix.diagonal a) DeltaX i j =
        DeltaC i j - matMul n DeltaA X i j -
          matMul n X (matTranspose DeltaA) i j) :
    frobNorm DeltaX / frobNorm X <=
      Real.sqrt 2 * lyapunovCondDiagonal n X alpha gamma s * eps := by
  exact
    H16_eq16_27_lyapunov_condition_diagonal n
      a X DeltaA DeltaC DeltaX alpha gamma s eps
      halpha hgamma hs heps hX hsep
      hDeltaA hDeltaC hLin

/-- Higham, 2nd ed., Chapter 16.3, equation (16.27), diagonal case:
    source-numbered alias for the relative first-order diagonal Lyapunov
    perturbation bound with the concrete diagonal condition number. -/
theorem H16_eq16_27_lyapunov_relative_first_order_bound_diagonal
    (n : Nat)
    (a : Fin n -> Real) (X DeltaA DeltaC DeltaX : Fin n -> Fin n -> Real)
    (alpha gamma s eps : Real)
    (halpha : 0 < alpha) (hgamma : 0 < gamma)
    (hs : 0 < s) (heps : 0 <= eps)
    (hX : 0 < frobNorm X)
    (hsep : forall i j, s <= |a i + a j|)
    (hDeltaA : frobNorm DeltaA <= eps * alpha)
    (hDeltaC : frobNorm DeltaC <= eps * gamma)
    (hLin : forall i j,
      lyapunovOp n (Matrix.diagonal a) DeltaX i j =
        DeltaC i j - matMul n DeltaA X i j -
          matMul n X (matTranspose DeltaA) i j) :
    frobNorm DeltaX / frobNorm X <=
      Real.sqrt 2 * lyapunovCondDiagonal n X alpha gamma s * eps := by
  exact
    lyapunov_relative_first_order_bound_diagonal n
      a X DeltaA DeltaC DeltaX alpha gamma s eps
      halpha hgamma hs heps hX hsep
      hDeltaA hDeltaC hLin

end NumStability
