/-
# Higham, 2nd ed., Chapter 14.4, Corollary 14.6 (p. 277)

Symmetric-positive-definite Gauss–Jordan elimination: forward stability and a
relative-2-norm residual bound with the printed `κ₂(A)^{1/2}` / `κ₂(A)`
constants.

The source-facing route in this module follows the proof on p. 277 directly:

* positive computed pivots and the symmetric-GE factor relation produce the
  scaled Cholesky factor `R_hat = D⁻¹ U_hat` with
  `A + DeltaA = R_hatᵀ R_hat`;
* certified inverses give the exact diagonal cancellation
  `|U_hat⁻¹||U_hat| = |R_hat⁻¹||R_hat|`, while the Gram inverse identity gives
  `kappa₂(R_hat) = kappa₂(A+DeltaA)^(1/2)`; and
* the two-factor Theorem 14.5 endpoints (14.31)/(14.32), supplied explicitly as
  `hRes`/`hFwd`, yield the printed `8n³` residual and `8n^(5/2)` forward leading
  coefficients from genuine norm-budget hypotheses.

The file also retains older accumulation-surrogate results for compatibility.
Those carry a three-factor second-stage remainder and are not the final
source-facing Corollary 14.6 surface.  Full actual-GJE closure still requires
the algorithmic symmetric-factor relation and the perturbative
`kappa₂(A+DeltaA)^(1/2) = kappa₂(A)^(1/2) + O(u)` family-level asymptotic
bridge; an exact finite Weyl envelope is proved below instead.  Remaining gaps
are listed at the end of the file.
-/
import NumStability.Algorithms.GaussJordan
import NumStability.Algorithms.HighamChapter10
import NumStability.Algorithms.Chapter14Problem1415Weyl

namespace NumStability.Ch14Ext

open scoped BigOperators
open scoped Matrix.Norms.L2Operator
open NumStability

-- ═══════════════════════════════════════════════════════════════════════════
-- §1  Spectral Cholesky identity and Lemma-6.6 aggregation discharges
-- ═══════════════════════════════════════════════════════════════════════════

/-- **Spectral Cholesky identity** (closing the step flagged open at
`HighamChapter10.lean:970`).  For a real matrix `R`, the l2 operator norm of
`RᵀR` is the square of the l2 operator norm of `R`.  Obtained from mathlib's
C*-identity `Matrix.l2_opNorm_conjTranspose_mul_self` and `Rᴴ = Rᵀ` over `ℝ`. -/
theorem ch14ext_opNorm2_transpose_mul_self_eq (n : ℕ) (R : Fin n → Fin n → ℝ) :
    opNorm2 (matMul n (fun i j => R j i) R) = opNorm2 R ^ 2 := by
  set Rm : Matrix (Fin n) (Fin n) ℝ := R with hRm
  have hmul : matMul n (fun i j => R j i) R = (Matrix.conjTranspose Rm * Rm) := by
    funext i j
    simp [matMul, Matrix.mul_apply, hRm]
  rw [hmul]
  have hcstar : opNorm2 (Matrix.conjTranspose Rm * Rm) = opNorm2 R * opNorm2 R :=
    Matrix.l2_opNorm_conjTranspose_mul_self (A := Rm)
  rw [hcstar, sq]

/-- The exact matrix operator `2`-norm is invariant under transpose. -/
theorem ch14ext_opNorm2_transpose_eq (n : ℕ) (R : Fin n → Fin n → ℝ) :
    opNorm2 (fun i j => R j i) = opNorm2 R := by
  set Rm : Matrix (Fin n) (Fin n) ℝ := R with hRm
  have htranspose : (fun i j => R j i) = Matrix.conjTranspose Rm := by
    funext i j
    simp [hRm]
  rw [htranspose]
  exact Matrix.l2_opNorm_conjTranspose Rm

/-- Companion C*-identity `||R Rᵀ||₂ = ||R||₂²`. -/
theorem ch14ext_opNorm2_mul_transpose_self_eq
    (n : ℕ) (R : Fin n → Fin n → ℝ) :
    opNorm2 (matMul n R (fun i j => R j i)) = opNorm2 R ^ 2 := by
  have h :=
    ch14ext_opNorm2_transpose_mul_self_eq n (fun i j => R j i)
  simpa [ch14ext_opNorm2_transpose_eq] using h

/-- **Exact Cholesky condition identity.**

If `R_inv` is a genuine two-sided inverse of `R`, the repository inverse of
`RᵀR` is `R_inv R_invᵀ`, and therefore
`kappa₂(R)^2 = kappa₂(RᵀR)`.  The inverse certificate prevents an unrelated
matrix from being used as the inverse argument of `kappa2`. -/
theorem ch14ext_cor146_kappa2_sq_eq_kappa2_gram
    (n : ℕ) (R R_inv : Fin n → Fin n → ℝ)
    (hInv : IsInverse n R R_inv) :
    kappa2 R R_inv ^ 2 =
      kappa2 (matMul n (fun i j => R j i) R)
        (nonsingInv n (matMul n (fun i j => R j i) R)) := by
  have hGramInv :
      nonsingInv n (matMul n (fun i j => R j i) R) =
        matMul n R_inv (fun i j => R_inv j i) := by
    simpa [rectMatMul, finiteTranspose, matMul] using
      (nonsingInv_rectMatMul_transpose_self_of_IsInverse hInv)
  rw [hGramInv]
  unfold kappa2
  rw [ch14ext_opNorm2_transpose_mul_self_eq,
    ch14ext_opNorm2_mul_transpose_self_eq]
  ring

/-- Square-root form of `ch14ext_cor146_kappa2_sq_eq_kappa2_gram`. -/
theorem ch14ext_cor146_kappa2_eq_sqrt_kappa2_gram
    (n : ℕ) (R R_inv : Fin n → Fin n → ℝ)
    (hInv : IsInverse n R R_inv) :
    kappa2 R R_inv =
      Real.sqrt
        (kappa2 (matMul n (fun i j => R j i) R)
          (nonsingInv n (matMul n (fun i j => R j i) R))) := by
  have hkappa : 0 ≤ kappa2 R R_inv := by
    unfold kappa2
    exact mul_nonneg (opNorm2_nonneg R) (opNorm2_nonneg R_inv)
  rw [← ch14ext_cor146_kappa2_sq_eq_kappa2_gram n R R_inv hInv,
    Real.sqrt_sq hkappa]

/-- **Exact finite perturbation envelope for `kappa₂`.**

For a nonempty square matrix and an additive perturbation smaller than the
smallest singular value, the all-index Weyl bound gives

`kappa₂(A + Delta) <= (||A||₂ + ||Delta||₂) /
  (sigma_min(A) - ||Delta||₂)`.

The perturbed inverse argument carries an actual right-inverse certificate;
the strict singular-value guard itself makes the original matrix nonsingular. -/
theorem ch14ext_cor146_kappa2_add_le_of_opNorm2_lt_sigmaMin
    {k : ℕ}
    (A Delta B_inv : Fin (k + 1) → Fin (k + 1) → ℝ)
    (hBInv : IsRightInverse (k + 1)
      (fun i j => A i j + Delta i j) B_inv)
    (hsmall : opNorm2 Delta <
      complexMatrixSingularValue (realRectToCMatrix A) (Fin.last k)) :
    kappa2 (fun i j => A i j + Delta i j) B_inv ≤
      (opNorm2 A + opNorm2 Delta) *
        (complexMatrixSingularValue (realRectToCMatrix A) (Fin.last k) -
          opNorm2 Delta)⁻¹ := by
  let top : Fin (k + 1) := ⟨0, Nat.succ_pos k⟩
  let last : Fin (k + 1) := Fin.last k
  let B : Fin (k + 1) → Fin (k + 1) → ℝ :=
    fun i j => A i j + Delta i j
  let sigmaA : Fin (k + 1) → ℝ :=
    fun i => complexMatrixSingularValue (realRectToCMatrix A) i
  let sigmaB : Fin (k + 1) → ℝ :=
    fun i => complexMatrixSingularValue (realRectToCMatrix B) i
  have hdelta : 0 ≤ opNorm2 Delta := opNorm2_nonneg Delta
  have hsigmaBLast : 0 < sigmaB last := by
    simpa [sigmaB, last, B] using
      (higham14_problem14_15_last_singularValue_pos_of_isRightInverse
        B B_inv hBInv)
  have htopWeyl : |sigmaB top - sigmaA top| ≤ opNorm2 Delta := by
    simpa [sigmaA, sigmaB, B] using
      (ch14ext_problem14_15_all_index_singularValue_abs_sub_le_opNorm2
        A Delta top)
  have hlastWeyl : |sigmaB last - sigmaA last| ≤ opNorm2 Delta := by
    simpa [sigmaA, sigmaB, B] using
      (ch14ext_problem14_15_all_index_singularValue_abs_sub_le_opNorm2
        A Delta last)
  have htop : sigmaB top ≤ sigmaA top + opNorm2 Delta := by
    have := (abs_le.mp htopWeyl).2
    linarith
  have hlast : sigmaA last - opNorm2 Delta ≤ sigmaB last := by
    have := (abs_le.mp hlastWeyl).1
    linarith
  have hden : 0 < sigmaA last - opNorm2 Delta := by
    simpa [sigmaA, last] using sub_pos.mpr hsmall
  have hnum : 0 ≤ sigmaA top + opNorm2 Delta :=
    add_nonneg
      (complexMatrixSingularValue_nonneg (realRectToCMatrix A) top) hdelta
  calc
    kappa2 B B_inv = sigmaB top / sigmaB last := by
      simpa [sigmaB, top, last, B] using
        (higham14_problem14_13_kappa2_eq_top_div_last_singularValue_of_rightInverse
          B B_inv hBInv)
    _ ≤ (sigmaA top + opNorm2 Delta) / sigmaB last :=
      div_le_div_of_nonneg_right htop hsigmaBLast.le
    _ ≤ (sigmaA top + opNorm2 Delta) /
          (sigmaA last - opNorm2 Delta) :=
      div_le_div_of_nonneg_left hnum hden hlast
    _ = (opNorm2 A + opNorm2 Delta) *
          (complexMatrixSingularValue (realRectToCMatrix A) (Fin.last k) -
            opNorm2 Delta)⁻¹ := by
      rw [show sigmaA top = opNorm2 A by
        symm
        simpa [sigmaA, top] using
          (higham14_problem14_13_opNorm2_eq_complex_top_singularValue
            (Nat.succ_pos k) A)]
      simp only [sigmaA, last, div_eq_mul_inv]

/-- The exact Weyl envelope transferred through a certified Cholesky/Gram
factorization.  This is a finite inequality, not an `O(u)` assertion. -/
theorem ch14ext_cor146_kappa2_factor_le_sqrt_perturbationEnvelope
    {k : ℕ}
    (A A_inv Delta R R_inv : Fin (k + 1) → Fin (k + 1) → ℝ)
    (hAInv : IsRightInverse (k + 1) A A_inv)
    (hRInv : IsInverse (k + 1) R R_inv)
    (hGram : matMul (k + 1) (fun i j => R j i) R =
      (fun i j => A i j + Delta i j))
    (hsmall : kappa2 A A_inv * opNorm2 Delta / opNorm2 A < 1) :
    kappa2 R R_inv ≤
      Real.sqrt
        ((opNorm2 A + opNorm2 Delta) *
          (complexMatrixSingularValue (realRectToCMatrix A) (Fin.last k) -
            opNorm2 Delta)⁻¹) := by
  let Gram : Fin (k + 1) → Fin (k + 1) → ℝ :=
    matMul (k + 1) (fun i j => R j i) R
  let B : Fin (k + 1) → Fin (k + 1) → ℝ :=
    fun i j => A i j + Delta i j
  have hGramRight : IsRightInverse (k + 1) Gram (nonsingInv (k + 1) Gram) := by
    have hraw : IsRightInverse (k + 1) Gram
        (matMul (k + 1) R_inv (fun i j => R_inv j i)) := by
      simpa [Gram, rectMatMul, finiteTranspose, matMul] using
        (IsRightInverse_rectMatMul_transpose_self_of_IsInverse hRInv)
    have hinv : nonsingInv (k + 1) Gram =
        matMul (k + 1) R_inv (fun i j => R_inv j i) := by
      simpa [Gram, rectMatMul, finiteTranspose, matMul] using
        (nonsingInv_rectMatMul_transpose_self_of_IsInverse hRInv)
    rw [hinv]
    exact hraw
  have hBRight : IsRightInverse (k + 1) B (nonsingInv (k + 1) B) := by
    have hGB : Gram = B := by simpa [Gram, B] using hGram
    rw [← hGB]
    exact hGramRight
  have hsigmaPos : 0 <
      complexMatrixSingularValue (realRectToCMatrix A) (Fin.last k) :=
    higham14_problem14_15_last_singularValue_pos_of_isRightInverse
      A A_inv hAInv
  have hDeltaSmall : opNorm2 Delta <
      complexMatrixSingularValue (realRectToCMatrix A) (Fin.last k) := by
    calc
      opNorm2 Delta ≤
          (kappa2 A A_inv * opNorm2 Delta / opNorm2 A) *
            complexMatrixSingularValue (realRectToCMatrix A) (Fin.last k) :=
        higham14_problem14_15_opNorm2_le_kappa2_scaled_last_singularValue
          A A_inv Delta hAInv
      _ < 1 * complexMatrixSingularValue
            (realRectToCMatrix A) (Fin.last k) :=
        mul_lt_mul_of_pos_right hsmall hsigmaPos
      _ = complexMatrixSingularValue
            (realRectToCMatrix A) (Fin.last k) := one_mul _
  have hpert :=
    ch14ext_cor146_kappa2_add_le_of_opNorm2_lt_sigmaMin
      A Delta (nonsingInv (k + 1) B)
      (by simpa [B] using hBRight) hDeltaSmall
  have hfactor :=
    ch14ext_cor146_kappa2_eq_sqrt_kappa2_gram (k + 1) R R_inv hRInv
  have hGB : Gram = B := by simpa [Gram, B] using hGram
  have hfactorB : kappa2 R R_inv =
      Real.sqrt (kappa2 B (nonsingInv (k + 1) B)) := by
    simpa [Gram, hGB] using hfactor
  rw [hfactorB]
  exact Real.sqrt_le_sqrt (by simpa [B] using hpert)

/-! ### Positive-pivot symmetric-GE to Cholesky bridge

The source does not identify the unit-lower factor with the transpose of the
upper factor.  Instead, symmetry gives `U_hat = D^2 L_hat^T`; positive pivots
make `D = diag(U_hat)^(1/2)` well-defined, and
`R_hat = D^{-1} U_hat = D L_hat^T`.  The following declarations encode and
prove exactly that structural step.  They deliberately keep `L_hat`, `U_hat`,
and `R_hat` distinct.
-/

/-- The positive-pivot diagonal scale `D_ii = sqrt(U_hat_ii)` from the proof of
Corollary 14.6. -/
noncomputable def ch14ext_cor146_pivotScale (n : ℕ)
    (U_hat : Fin n → Fin n → ℝ) (i : Fin n) : ℝ :=
  Real.sqrt (U_hat i i)

/-- The scaled upper factor `R_hat = D^{-1} U_hat` from the proof of
Corollary 14.6. -/
noncomputable def ch14ext_cor146_scaledUpper (n : ℕ)
    (U_hat : Fin n → Fin n → ℝ) : Fin n → Fin n → ℝ :=
  fun i j => U_hat i j / ch14ext_cor146_pivotScale n U_hat i

/-- Positive pivots and the symmetric-GE relation
`U_hat_ij = U_hat_ii * L_hat_ji` imply both diagonal-scaling identities
`U_hat = D R_hat` and `R_hat = D L_hat^T`. -/
theorem ch14ext_cor146_positivePivot_scaledUpper_relations
    (n : ℕ) (L_hat U_hat : Fin n → Fin n → ℝ)
    (hpiv : ∀ i : Fin n, 0 < U_hat i i)
    (hsym : ∀ i j : Fin n, U_hat i j = U_hat i i * L_hat j i) :
    (∀ i j : Fin n,
      U_hat i j = ch14ext_cor146_pivotScale n U_hat i *
        ch14ext_cor146_scaledUpper n U_hat i j) ∧
    (∀ i j : Fin n,
      ch14ext_cor146_scaledUpper n U_hat i j =
        ch14ext_cor146_pivotScale n U_hat i * L_hat j i) := by
  constructor
  · intro i j
    have hdne : ch14ext_cor146_pivotScale n U_hat i ≠ 0 :=
      ne_of_gt (Real.sqrt_pos.2 (hpiv i))
    calc
      U_hat i j =
          (U_hat i j / ch14ext_cor146_pivotScale n U_hat i) *
            ch14ext_cor146_pivotScale n U_hat i :=
        (div_mul_cancel₀ _ hdne).symm
      _ = ch14ext_cor146_pivotScale n U_hat i *
            ch14ext_cor146_scaledUpper n U_hat i j := by
        simp [ch14ext_cor146_scaledUpper, mul_comm]
  · intro i j
    let d := ch14ext_cor146_pivotScale n U_hat i
    have hdpos : 0 < d := by
      simpa [d, ch14ext_cor146_pivotScale] using Real.sqrt_pos.2 (hpiv i)
    have hdne : d ≠ 0 := ne_of_gt hdpos
    have hUscale :
        U_hat i j = d * ch14ext_cor146_scaledUpper n U_hat i j := by
      calc
        U_hat i j = (U_hat i j / d) * d := (div_mul_cancel₀ _ hdne).symm
        _ = d * ch14ext_cor146_scaledUpper n U_hat i j := by
          simp [d, ch14ext_cor146_scaledUpper, mul_comm]
    have hdsq : d * d = U_hat i i := by
      simpa [d, ch14ext_cor146_pivotScale] using
        Real.mul_self_sqrt (le_of_lt (hpiv i))
    apply mul_left_cancel₀ hdne
    calc
      d * ch14ext_cor146_scaledUpper n U_hat i j = U_hat i j := hUscale.symm
      _ = U_hat i i * L_hat j i := hsym i j
      _ = (d * d) * L_hat j i := by rw [hdsq]
      _ = d * (d * L_hat j i) := by ring

/-- A diagonal scaling satisfying `U_hat = D R_hat` and
`R_hat = D L_hat^T` turns the LU product into the Cholesky product
`R_hat^T R_hat`. -/
theorem ch14ext_cor146_diagScaled_lu_product_eq_cholesky
    (n : ℕ) (L_hat U_hat R_hat : Fin n → Fin n → ℝ)
    (d : Fin n → ℝ)
    (hU : ∀ i j : Fin n, U_hat i j = d i * R_hat i j)
    (hR : ∀ i j : Fin n, R_hat i j = d i * L_hat j i) :
    matMul n L_hat U_hat = matMul n (fun i j => R_hat j i) R_hat := by
  funext i j
  simp only [matMul]
  apply Finset.sum_congr rfl
  intro k _
  rw [hU k j, hR k i]
  ring

/-- If `U = D R` with a nonsingular diagonal `D`, then
`R_inv D⁻¹` is the inverse of `U` whenever `R_inv` is the inverse of `R`. -/
theorem ch14ext_cor146_diagScaled_inverse
    (n : ℕ) (d : Fin n → ℝ)
    (R R_inv U U_inv : Fin n → Fin n → ℝ)
    (hd : ∀ i : Fin n, d i ≠ 0)
    (hU : ∀ i j : Fin n, U i j = d i * R i j)
    (hUinv : ∀ i j : Fin n, U_inv i j = R_inv i j / d j)
    (hRInv : IsInverse n R R_inv) :
    IsInverse n U U_inv := by
  constructor
  · intro i j
    calc
      (∑ k : Fin n, U_inv i k * U k j) =
          ∑ k : Fin n, R_inv i k * R k j := by
        apply Finset.sum_congr rfl
        intro k _
        rw [hUinv i k, hU k j]
        field_simp [hd k]
      _ = if i = j then 1 else 0 := hRInv.1 i j
  · intro i j
    calc
      (∑ k : Fin n, U i k * U_inv k j) =
          ∑ k : Fin n, (d i / d j) * (R i k * R_inv k j) := by
        apply Finset.sum_congr rfl
        intro k _
        rw [hU i k, hUinv k j]
        ring
      _ = (d i / d j) * ∑ k : Fin n, R i k * R_inv k j := by
        rw [Finset.mul_sum]
      _ = (d i / d j) * (if i = j then 1 else 0) := by
        rw [hRInv.2 i j]
      _ = if i = j then 1 else 0 := by
        split_ifs with hij
        · subst j
          simp [hd i]
        · ring

/-- Entrywise cancellation behind the source identity
`|U⁻¹||U| = |R⁻¹||R|` for `U = D R` and `U⁻¹ = R⁻¹D⁻¹`. -/
theorem ch14ext_cor146_abs_diagonalScaling_cancel
    (n : ℕ) (d : Fin n → ℝ)
    (R R_inv U U_inv : Fin n → Fin n → ℝ)
    (hd : ∀ i : Fin n, d i ≠ 0)
    (hU : ∀ i j : Fin n, U i j = d i * R i j)
    (hUinv : ∀ i j : Fin n, U_inv i j = R_inv i j / d j) :
    matMul n (absMatrix n U_inv) (absMatrix n U) =
      matMul n (absMatrix n R_inv) (absMatrix n R) := by
  funext i j
  simp only [matMul, absMatrix]
  apply Finset.sum_congr rfl
  intro k _
  rw [hUinv i k, hU k j, abs_div, abs_mul]
  field_simp [abs_ne_zero.mpr (hd k)]

/-- The cancellation formula follows from actual inverse certificates; the
explicit formula `U_inv = R_inv D⁻¹` is derived by uniqueness of inverses. -/
theorem ch14ext_cor146_abs_inverseProduct_eq_of_diagonalScaling
    (n : ℕ) (d : Fin n → ℝ)
    (R R_inv U U_inv : Fin n → Fin n → ℝ)
    (hd : ∀ i : Fin n, d i ≠ 0)
    (hU : ∀ i j : Fin n, U i j = d i * R i j)
    (hRInv : IsInverse n R R_inv)
    (hUInv : IsInverse n U U_inv) :
    matMul n (absMatrix n U_inv) (absMatrix n U) =
      matMul n (absMatrix n R_inv) (absMatrix n R) := by
  let U_inv' : Fin n → Fin n → ℝ := fun i j => R_inv i j / d j
  have hUInv' : IsInverse n U U_inv' :=
    ch14ext_cor146_diagScaled_inverse n d R R_inv U U_inv' hd hU
      (by intro i j; rfl) hRInv
  have hUinv_eq : U_inv = U_inv' := by
    calc
      U_inv = nonsingInv n U :=
        (nonsingInv_eq_of_isRightInverse U U_inv hUInv.2).symm
      _ = U_inv' := nonsingInv_eq_of_isRightInverse U U_inv' hUInv'.2
  apply ch14ext_cor146_abs_diagonalScaling_cancel
    n d R R_inv U U_inv hd hU
  intro i j
  rw [hUinv_eq]

/-- Positive pivots and the explicit symmetric-factor relation specialize the
diagonal cancellation to `R_hat = D⁻¹ U_hat`. -/
theorem ch14ext_cor146_positivePivot_abs_inverseProduct_eq
    (n : ℕ) (L_hat U_hat U_inv R_inv : Fin n → Fin n → ℝ)
    (hpiv : ∀ i : Fin n, 0 < U_hat i i)
    (hsym : ∀ i j : Fin n, U_hat i j = U_hat i i * L_hat j i)
    (hRInv : IsInverse n (ch14ext_cor146_scaledUpper n U_hat) R_inv)
    (hUInv : IsInverse n U_hat U_inv) :
    matMul n (absMatrix n U_inv) (absMatrix n U_hat) =
      matMul n (absMatrix n R_inv)
        (absMatrix n (ch14ext_cor146_scaledUpper n U_hat)) := by
  rcases ch14ext_cor146_positivePivot_scaledUpper_relations
      n L_hat U_hat hpiv hsym with ⟨hU, _⟩
  exact ch14ext_cor146_abs_inverseProduct_eq_of_diagonalScaling
    n (ch14ext_cor146_pivotScale n U_hat)
    (ch14ext_cor146_scaledUpper n U_hat) R_inv U_hat U_inv
    (fun i => ne_of_gt (Real.sqrt_pos.2 (hpiv i))) hU hRInv hUInv

/-- The explicit symmetric-GE backward perturbation used in Corollary 14.6. -/
noncomputable def ch14ext_cor146_symmetricGEDelta (n : ℕ)
    (A L_hat U_hat : Fin n → Fin n → ℝ) : Fin n → Fin n → ℝ :=
  fun i j => matMul n L_hat U_hat i j - A i j

/-- **Corollary 14.6 positive-pivot/Cholesky structural specialization.**

From a symmetric-GE factor relation, positive computed pivots, and the standard
LU backward-error certificate, the scaled upper factor satisfies
`A + DeltaA = R_hat^T R_hat`.  The perturbation is symmetric and retains the
source componentwise `gamma_n |L_hat||U_hat|` bound.  No residual or forward
error conclusion is assumed here. -/
theorem ch14ext_cor146_positivePivot_cholesky_backward_error
    (n : ℕ) (fp : FPModel)
    (A L_hat U_hat : Fin n → Fin n → ℝ)
    (hSPD : IsSymPosDef n A)
    (hLU : LUBackwardError n A L_hat U_hat (gamma fp n))
    (hpiv : ∀ i : Fin n, 0 < U_hat i i)
    (hsym : ∀ i j : Fin n, U_hat i j = U_hat i i * L_hat j i) :
    (∀ i : Fin n, 0 < ch14ext_cor146_pivotScale n U_hat i) ∧
    (∀ i j : Fin n,
      A i j + ch14ext_cor146_symmetricGEDelta n A L_hat U_hat i j =
        matMul n
          (fun a b => ch14ext_cor146_scaledUpper n U_hat b a)
          (ch14ext_cor146_scaledUpper n U_hat) i j) ∧
    (∀ i j : Fin n,
      ch14ext_cor146_symmetricGEDelta n A L_hat U_hat i j =
        ch14ext_cor146_symmetricGEDelta n A L_hat U_hat j i) ∧
    (∀ i j : Fin n,
      |ch14ext_cor146_symmetricGEDelta n A L_hat U_hat i j| ≤
        gamma fp n * ∑ k : Fin n, |L_hat i k| * |U_hat k j|) := by
  rcases ch14ext_cor146_positivePivot_scaledUpper_relations
      n L_hat U_hat hpiv hsym with ⟨hU, hR⟩
  have hprod :=
    ch14ext_cor146_diagScaled_lu_product_eq_cholesky
      n L_hat U_hat (ch14ext_cor146_scaledUpper n U_hat)
      (ch14ext_cor146_pivotScale n U_hat) hU hR
  refine ⟨?_, ?_, ?_, ?_⟩
  · intro i
    exact Real.sqrt_pos.2 (hpiv i)
  · intro i j
    dsimp [ch14ext_cor146_symmetricGEDelta]
    rw [congrFun (congrFun hprod i) j]
    ring
  · intro i j
    have hgram :
        matMul n
            (fun a b => ch14ext_cor146_scaledUpper n U_hat b a)
            (ch14ext_cor146_scaledUpper n U_hat) i j =
          matMul n
            (fun a b => ch14ext_cor146_scaledUpper n U_hat b a)
            (ch14ext_cor146_scaledUpper n U_hat) j i := by
      simp only [matMul]
      apply Finset.sum_congr rfl
      intro k _
      ring
    calc
      ch14ext_cor146_symmetricGEDelta n A L_hat U_hat i j =
          matMul n L_hat U_hat i j - A i j := rfl
      _ = matMul n
            (fun a b => ch14ext_cor146_scaledUpper n U_hat b a)
            (ch14ext_cor146_scaledUpper n U_hat) i j - A i j := by
          rw [congrFun (congrFun hprod i) j]
      _ = matMul n
            (fun a b => ch14ext_cor146_scaledUpper n U_hat b a)
            (ch14ext_cor146_scaledUpper n U_hat) j i - A j i := by
          rw [hgram, hSPD.1 i j]
      _ = matMul n L_hat U_hat j i - A j i := by
          rw [congrFun (congrFun hprod j) i]
      _ = ch14ext_cor146_symmetricGEDelta n A L_hat U_hat j i := rfl
  · intro i j
    simpa [ch14ext_cor146_symmetricGEDelta, matMul] using hLU.backward_bound i j

/-- **First-stage aggregation discharge** (Corollary 14.6 `alpha`).
The `|L̂||Û| = |R̂ᵀ||R̂|` aggregation obeys the printed first-stage budget
`‖ |R̂ᵀ||R̂| |x| ‖₂ ≤ n‖R̂‖₂² ‖x‖₂`, via `higham10_7_absRT_absR_opNorm2Le`
(Lemma 6.6). -/
theorem ch14ext_spd_firstStage_agg_le (n : ℕ) (R : Fin n → Fin n → ℝ)
    (x : Fin n → ℝ) :
    vecNorm2 (fun i : Fin n =>
      ∑ j : Fin n, (∑ k : Fin n, |R k i| * |R k j|) * |x j|)
      ≤ (n : ℝ) * opNorm2 R ^ 2 * vecNorm2 x := by
  have hM : opNorm2Le
      (matMul n (fun i j => |R j i|) (fun i j => |R i j|))
      ((n : ℝ) * opNorm2 R ^ 2) :=
    higham10_7_absRT_absR_opNorm2Le n R (opNorm2 R) (opNorm2_nonneg R)
      (opNorm2Le_opNorm2 R)
  have hEq : (fun i : Fin n =>
      ∑ j : Fin n, (∑ k : Fin n, |R k i| * |R k j|) * |x j|)
      = matMulVec n (matMul n (fun i j => |R j i|) (fun i j => |R i j|))
          (fun j => |x j|) := by
    funext i
    simp [matMulVec, matMul]
  rw [hEq]
  calc vecNorm2 (matMulVec n (matMul n (fun i j => |R j i|) (fun i j => |R i j|))
        (fun j => |x j|))
      ≤ (n : ℝ) * opNorm2 R ^ 2 * vecNorm2 (fun j => |x j|) := hM _
    _ = (n : ℝ) * opNorm2 R ^ 2 * vecNorm2 x := by rw [vecNorm2_abs]

/-- **Second-stage `X` aggregation discharge** (Corollary 14.6 `beta`).
The accumulation second-stage term is the three-factor `|R̂ᵀ||R̂⁻¹||R̂|`; via the
Lemma 6.6 chain and submultiplicativity it obeys
`‖ |R̂ᵀ||R̂⁻¹||R̂| |x| ‖₂ ≤ n^{3/2}‖R̂‖₂²‖R̂⁻¹‖₂ ‖x‖₂`. -/
theorem ch14ext_spd_secondStageX_agg_le (n : ℕ) (R Rinv : Fin n → Fin n → ℝ)
    (x : Fin n → ℝ) :
    vecNorm2 (fun i : Fin n =>
      ∑ j : Fin n, (∑ k₁ : Fin n, |R k₁ i| *
        (∑ k₂ : Fin n, |Rinv k₁ k₂| * |R k₂ j|)) * |x j|)
      ≤ (n : ℝ) * Real.sqrt n * opNorm2 R ^ 2 * opNorm2 Rinv * vecNorm2 x := by
  have hT : opNorm2Le (fun i j => |R j i|) (Real.sqrt n * opNorm2 R) :=
    opNorm2Le_abs_transpose_of_opNorm2Le n R (opNorm2 R) (opNorm2_nonneg R)
      (opNorm2Le_opNorm2 R)
  have hI : opNorm2Le (fun i j => |Rinv i j|) (Real.sqrt n * opNorm2 Rinv) :=
    opNorm2Le_abs_of_opNorm2Le n Rinv (opNorm2 Rinv) (opNorm2_nonneg Rinv)
      (opNorm2Le_opNorm2 Rinv)
  have hR : opNorm2Le (fun i j => |R i j|) (Real.sqrt n * opNorm2 R) :=
    opNorm2Le_abs_of_opNorm2Le n R (opNorm2 R) (opNorm2_nonneg R)
      (opNorm2Le_opNorm2 R)
  have hInner : opNorm2Le (matMul n (fun i j => |Rinv i j|) (fun i j => |R i j|))
      (Real.sqrt n * opNorm2 Rinv * (Real.sqrt n * opNorm2 R)) :=
    opNorm2Le_matMul n _ _ _ _
      (mul_nonneg (Real.sqrt_nonneg _) (opNorm2_nonneg Rinv)) hI hR
  have hOuter : opNorm2Le
      (matMul n (fun i j => |R j i|)
        (matMul n (fun i j => |Rinv i j|) (fun i j => |R i j|)))
      (Real.sqrt n * opNorm2 R *
        (Real.sqrt n * opNorm2 Rinv * (Real.sqrt n * opNorm2 R))) :=
    opNorm2Le_matMul n _ _ _ _
      (mul_nonneg (Real.sqrt_nonneg _) (opNorm2_nonneg R)) hT hInner
  have hEq : (fun i : Fin n =>
      ∑ j : Fin n, (∑ k₁ : Fin n, |R k₁ i| *
        (∑ k₂ : Fin n, |Rinv k₁ k₂| * |R k₂ j|)) * |x j|)
      = matMulVec n
          (matMul n (fun i j => |R j i|)
            (matMul n (fun i j => |Rinv i j|) (fun i j => |R i j|)))
          (fun j => |x j|) := by
    funext i
    rfl
  rw [hEq]
  have hsqrt : Real.sqrt n * Real.sqrt n = (n : ℝ) :=
    Real.mul_self_sqrt (Nat.cast_nonneg n)
  calc vecNorm2 (matMulVec n
        (matMul n (fun i j => |R j i|)
          (matMul n (fun i j => |Rinv i j|) (fun i j => |R i j|)))
        (fun j => |x j|))
      ≤ (Real.sqrt n * opNorm2 R *
          (Real.sqrt n * opNorm2 Rinv * (Real.sqrt n * opNorm2 R)))
          * vecNorm2 (fun j => |x j|) := hOuter _
    _ = (n : ℝ) * Real.sqrt n * opNorm2 R ^ 2 * opNorm2 Rinv * vecNorm2 x := by
        rw [vecNorm2_abs]
        have h : Real.sqrt n * opNorm2 R *
            (Real.sqrt n * opNorm2 Rinv * (Real.sqrt n * opNorm2 R))
            = (Real.sqrt n * Real.sqrt n) * Real.sqrt n
                * opNorm2 R ^ 2 * opNorm2 Rinv := by ring
        rw [h, hsqrt]

/-- **Second-stage `Y` aggregation discharge** (Corollary 14.6 `eta`).
`‖ |R̂ᵀ||R̂⁻¹| |y| ‖₂ ≤ n‖R̂‖₂‖R̂⁻¹‖₂ ‖y‖₂`, via the Lemma 6.6 chain. -/
theorem ch14ext_spd_secondStageY_agg_le (n : ℕ) (R Rinv : Fin n → Fin n → ℝ)
    (y : Fin n → ℝ) :
    vecNorm2 (fun i : Fin n =>
      ∑ k : Fin n, |R k i| * (∑ j : Fin n, |Rinv k j| * |y j|))
      ≤ (n : ℝ) * opNorm2 R * opNorm2 Rinv * vecNorm2 y := by
  have hT : opNorm2Le (fun i j => |R j i|) (Real.sqrt n * opNorm2 R) :=
    opNorm2Le_abs_transpose_of_opNorm2Le n R (opNorm2 R) (opNorm2_nonneg R)
      (opNorm2Le_opNorm2 R)
  have hI : opNorm2Le (fun i j => |Rinv i j|) (Real.sqrt n * opNorm2 Rinv) :=
    opNorm2Le_abs_of_opNorm2Le n Rinv (opNorm2 Rinv) (opNorm2_nonneg Rinv)
      (opNorm2Le_opNorm2 Rinv)
  have hProd : opNorm2Le (matMul n (fun i j => |R j i|) (fun i j => |Rinv i j|))
      (Real.sqrt n * opNorm2 R * (Real.sqrt n * opNorm2 Rinv)) :=
    opNorm2Le_matMul n _ _ _ _
      (mul_nonneg (Real.sqrt_nonneg _) (opNorm2_nonneg R)) hT hI
  have hEq : (fun i : Fin n =>
      ∑ k : Fin n, |R k i| * (∑ j : Fin n, |Rinv k j| * |y j|))
      = matMulVec n (matMul n (fun i j => |R j i|) (fun i j => |Rinv i j|))
          (fun j => |y j|) := by
    funext i
    simp only [matMulVec, matMul, Finset.mul_sum, Finset.sum_mul, mul_assoc]
    rw [Finset.sum_comm]
  rw [hEq]
  have hsqrt : Real.sqrt n * Real.sqrt n = (n : ℝ) :=
    Real.mul_self_sqrt (Nat.cast_nonneg n)
  calc vecNorm2 (matMulVec n (matMul n (fun i j => |R j i|) (fun i j => |Rinv i j|))
        (fun j => |y j|))
      ≤ (Real.sqrt n * opNorm2 R * (Real.sqrt n * opNorm2 Rinv))
          * vecNorm2 (fun j => |y j|) := hProd _
    _ = (n : ℝ) * opNorm2 R * opNorm2 Rinv * vecNorm2 y := by
        rw [vecNorm2_abs]
        have h : Real.sqrt n * opNorm2 R * (Real.sqrt n * opNorm2 Rinv)
            = (Real.sqrt n * Real.sqrt n) * opNorm2 R * opNorm2 Rinv := by ring
        rw [h, hsqrt]

/-- **Absolute-inverse operator-2 bound** (Lemma 6.6 for `|A⁻¹|`):
`‖ |A_inv| ‖₂ ≤ √n ‖A_inv‖₂`. -/
theorem ch14ext_opNorm2_absMatrix_le (n : ℕ) (A_inv : Fin n → Fin n → ℝ) :
    opNorm2 (fun i j => |A_inv i j|) ≤ Real.sqrt n * opNorm2 A_inv :=
  opNorm2_le_of_opNorm2Le _
    (mul_nonneg (Real.sqrt_nonneg _) (opNorm2_nonneg A_inv))
    (opNorm2Le_abs_of_opNorm2Le n A_inv (opNorm2 A_inv) (opNorm2_nonneg A_inv)
      (opNorm2Le_opNorm2 A_inv))

/-! ### Direct two-factor specialization of Theorem 14.5

The printed proof uses the two-factor matrix `|U_hat⁻¹||U_hat|` appearing in
(14.31)/(14.32), rather than the three-factor accumulation surrogate used by
the older wrappers later in this file.  These theorems isolate that exact
source route. -/

/-- Lemma 6.6 gives the source estimate
`|| |U_inv||U| ||_2 <= n * kappa_2(U)` in vector-action form. -/
theorem ch14ext_cor146_condU_opNorm2Le (n : ℕ)
    (U U_inv : Fin n → Fin n → ℝ) :
    opNorm2Le (matMul n (absMatrix n U_inv) (absMatrix n U))
      ((n : ℝ) * kappa2 U U_inv) := by
  have hInvAbs : opNorm2Le (absMatrix n U_inv)
      (Real.sqrt n * opNorm2 U_inv) := by
    simpa [absMatrix] using
      opNorm2Le_abs_of_opNorm2Le n U_inv (opNorm2 U_inv)
        (opNorm2_nonneg U_inv) (opNorm2Le_opNorm2 U_inv)
  have hUAbs : opNorm2Le (absMatrix n U)
      (Real.sqrt n * opNorm2 U) := by
    simpa [absMatrix] using
      opNorm2Le_abs_of_opNorm2Le n U (opNorm2 U)
        (opNorm2_nonneg U) (opNorm2Le_opNorm2 U)
  have hprod :=
    opNorm2Le_matMul n (absMatrix n U_inv) (absMatrix n U)
      (Real.sqrt n * opNorm2 U_inv) (Real.sqrt n * opNorm2 U)
      (mul_nonneg (Real.sqrt_nonneg _) (opNorm2_nonneg U_inv)) hInvAbs hUAbs
  have hsqrt : Real.sqrt n * Real.sqrt n = (n : ℝ) :=
    Real.mul_self_sqrt (Nat.cast_nonneg n)
  have hcoeff :
      (Real.sqrt n * opNorm2 U_inv) * (Real.sqrt n * opNorm2 U) =
        (n : ℝ) * kappa2 U U_inv := by
    unfold kappa2
    rw [show Real.sqrt n * opNorm2 U_inv * (Real.sqrt n * opNorm2 U) =
      (Real.sqrt n * Real.sqrt n) * (opNorm2 U * opNorm2 U_inv) by ring, hsqrt]
  rw [← hcoeff]
  exact hprod

/-- The source diagonal cancellation feeds Lemma 6.6 with `R_hat`, not with
the generally differently conditioned row-scaled matrix `U_hat`. -/
theorem ch14ext_cor146_positivePivot_condU_opNorm2Le
    (n : ℕ) (L_hat U_hat U_inv R_inv : Fin n → Fin n → ℝ)
    (hpiv : ∀ i : Fin n, 0 < U_hat i i)
    (hsym : ∀ i j : Fin n, U_hat i j = U_hat i i * L_hat j i)
    (hRInv : IsInverse n (ch14ext_cor146_scaledUpper n U_hat) R_inv)
    (hUInv : IsInverse n U_hat U_inv) :
    opNorm2Le (matMul n (absMatrix n U_inv) (absMatrix n U_hat))
      ((n : ℝ) *
        kappa2 (ch14ext_cor146_scaledUpper n U_hat) R_inv) := by
  rw [ch14ext_cor146_positivePivot_abs_inverseProduct_eq
    n L_hat U_hat U_inv R_inv hpiv hsym hRInv hUInv]
  exact ch14ext_cor146_condU_opNorm2Le
    n (ch14ext_cor146_scaledUpper n U_hat) R_inv

/-- Norm reduction for the (14.31) two-factor endpoint from a direct operator
certificate for `|U_inv||U|`.  This is the reusable core needed after diagonal
scaling cancellation. -/
theorem ch14ext_cor146_residual_twoFactor_of_cond_bound
    (n : ℕ) (fp : FPModel)
    (A L_hat U_hat U_inv : Fin n → Fin n → ℝ)
    (b x_hat : Fin n → ℝ)
    (luFactor kappaRoot : ℝ)
    (hluFactor : 0 ≤ luFactor)
    (hAbsLU : opNorm2Le
      (matMul n (absMatrix n L_hat) (absMatrix n U_hat))
      ((n : ℝ) * luFactor * opNorm2 A))
    (hCond : opNorm2Le
      (matMul n (absMatrix n U_inv) (absMatrix n U_hat))
      ((n : ℝ) * kappaRoot))
    (hRes : ∀ i : Fin n,
      |b i - ∑ j : Fin n, A i j * x_hat j| ≤
        8 * (n : ℝ) * fp.u *
          matMulVec n
            (matMul n
              (matMul n (absMatrix n L_hat) (absMatrix n U_hat))
              (matMul n (absMatrix n U_inv) (absMatrix n U_hat)))
            (absVec n x_hat) i) :
    vecNorm2 (fun i : Fin n => b i - ∑ j : Fin n, A i j * x_hat j) ≤
      8 * (n : ℝ) ^ 3 * fp.u * luFactor * kappaRoot *
        opNorm2 A * vecNorm2 x_hat := by
  let MLU : Fin n → Fin n → ℝ :=
    matMul n (absMatrix n L_hat) (absMatrix n U_hat)
  let B : Fin n → Fin n → ℝ :=
    matMul n (absMatrix n U_inv) (absMatrix n U_hat)
  let r : Fin n → ℝ := fun i => b i - ∑ j : Fin n, A i j * x_hat j
  let cLU : ℝ := (n : ℝ) * luFactor * opNorm2 A
  let cB : ℝ := (n : ℝ) * kappaRoot
  let c : ℝ := 8 * (n : ℝ) * fp.u
  have hcLU : 0 ≤ cLU :=
    mul_nonneg (mul_nonneg (Nat.cast_nonneg n) hluFactor) (opNorm2_nonneg A)
  have hc : 0 ≤ c :=
    mul_nonneg (mul_nonneg (by norm_num) (Nat.cast_nonneg n)) fp.u_nonneg
  have hB : opNorm2Le B cB := by simpa [B, cB] using hCond
  have hProd : opNorm2Le (matMul n MLU B) (cLU * cB) :=
    opNorm2Le_matMul n MLU B cLU cB hcLU
      (by simpa [MLU, cLU] using hAbsLU) hB
  have hAbs : ∀ i : Fin n,
      |r i| ≤ c * matMulVec n (matMul n MLU B) (absVec n x_hat) i := by
    intro i
    simpa [r, c, MLU, B] using hRes i
  have hnorm :=
    vecNorm2_le_of_abs_le r
      (fun i => c * matMulVec n (matMul n MLU B) (absVec n x_hat) i) hAbs
  have habsNorm : vecNorm2 (absVec n x_hat) = vecNorm2 x_hat := by
    simpa [absVec] using vecNorm2_abs x_hat
  change vecNorm2 r ≤ _
  calc
    vecNorm2 r ≤
        vecNorm2 (fun i => c * matMulVec n (matMul n MLU B)
          (absVec n x_hat) i) := hnorm
    _ = c * vecNorm2 (matMulVec n (matMul n MLU B) (absVec n x_hat)) := by
      rw [vecNorm2_smul, abs_of_nonneg hc]
    _ ≤ c * ((cLU * cB) * vecNorm2 (absVec n x_hat)) :=
      mul_le_mul_of_nonneg_left (hProd (absVec n x_hat)) hc
    _ = 8 * (n : ℝ) ^ 3 * fp.u * luFactor * kappaRoot *
          opNorm2 A * vecNorm2 x_hat := by
      rw [habsNorm]
      simp only [c, cLU, cB]
      ring

/-- Forward-error companion of
`ch14ext_cor146_residual_twoFactor_of_cond_bound`, reducing (14.32) from a
direct operator certificate for `|U_inv||U|`. -/
theorem ch14ext_cor146_forward_twoFactor_of_cond_bound
    (n : ℕ) (fp : FPModel)
    (A A_inv L_hat U_hat U_inv : Fin n → Fin n → ℝ)
    (x x_hat : Fin n → ℝ)
    (luFactor kappaRoot : ℝ)
    (hluFactor : 0 ≤ luFactor)
    (hAbsLU : opNorm2Le
      (matMul n (absMatrix n L_hat) (absMatrix n U_hat))
      ((n : ℝ) * luFactor * opNorm2 A))
    (hCond : opNorm2Le
      (matMul n (absMatrix n U_inv) (absMatrix n U_hat))
      ((n : ℝ) * kappaRoot))
    (hFwd : ∀ i : Fin n,
      |x i - x_hat i| ≤
        2 * (n : ℝ) * fp.u *
          (matMulVec n
              (matMul n (absMatrix n A_inv)
                (matMul n (absMatrix n L_hat) (absMatrix n U_hat)))
              (absVec n x_hat) i +
            3 * matMulVec n
              (matMul n (absMatrix n U_inv) (absMatrix n U_hat))
              (absVec n x_hat) i)) :
    vecNorm2 (fun i : Fin n => x i - x_hat i) ≤
      2 * (n : ℝ) * fp.u *
        ((n : ℝ) * Real.sqrt n * luFactor * kappa2 A A_inv +
          3 * (n : ℝ) * kappaRoot) * vecNorm2 x_hat := by
  let MLU : Fin n → Fin n → ℝ :=
    matMul n (absMatrix n L_hat) (absMatrix n U_hat)
  let M1 : Fin n → Fin n → ℝ := matMul n (absMatrix n A_inv) MLU
  let B : Fin n → Fin n → ℝ :=
    matMul n (absMatrix n U_inv) (absMatrix n U_hat)
  let e : Fin n → ℝ := fun i => x i - x_hat i
  let cLU : ℝ := (n : ℝ) * luFactor * opNorm2 A
  let c1 : ℝ := (Real.sqrt n * opNorm2 A_inv) * cLU
  let cB : ℝ := (n : ℝ) * kappaRoot
  let c : ℝ := 2 * (n : ℝ) * fp.u
  have hcLU : 0 ≤ cLU :=
    mul_nonneg (mul_nonneg (Nat.cast_nonneg n) hluFactor) (opNorm2_nonneg A)
  have hcAinv : 0 ≤ Real.sqrt n * opNorm2 A_inv :=
    mul_nonneg (Real.sqrt_nonneg _) (opNorm2_nonneg A_inv)
  have hc : 0 ≤ c :=
    mul_nonneg (mul_nonneg (by norm_num) (Nat.cast_nonneg n)) fp.u_nonneg
  have hAinvAbs : opNorm2Le (absMatrix n A_inv)
      (Real.sqrt n * opNorm2 A_inv) := by
    simpa [absMatrix] using
      opNorm2Le_abs_of_opNorm2Le n A_inv (opNorm2 A_inv)
        (opNorm2_nonneg A_inv) (opNorm2Le_opNorm2 A_inv)
  have hM1 : opNorm2Le M1 c1 :=
    opNorm2Le_matMul n (absMatrix n A_inv) MLU
      (Real.sqrt n * opNorm2 A_inv) cLU hcAinv hAinvAbs
      (by simpa [MLU, cLU] using hAbsLU)
  have hB : opNorm2Le B cB := by simpa [B, cB] using hCond
  have hAbs : ∀ i : Fin n,
      |e i| ≤ c *
        (matMulVec n M1 (absVec n x_hat) i +
          3 * matMulVec n B (absVec n x_hat) i) := by
    intro i
    simpa [e, c, M1, MLU, B] using hFwd i
  have hnorm :=
    vecNorm2_le_of_abs_le e
      (fun i => c *
        (matMulVec n M1 (absVec n x_hat) i +
          3 * matMulVec n B (absVec n x_hat) i)) hAbs
  have hsum :
      vecNorm2 (fun i =>
          matMulVec n M1 (absVec n x_hat) i +
            3 * matMulVec n B (absVec n x_hat) i) ≤
        (c1 + 3 * cB) * vecNorm2 (absVec n x_hat) := by
    calc
      vecNorm2 (fun i =>
          matMulVec n M1 (absVec n x_hat) i +
            3 * matMulVec n B (absVec n x_hat) i) ≤
          vecNorm2 (matMulVec n M1 (absVec n x_hat)) +
            vecNorm2 (fun i => 3 * matMulVec n B (absVec n x_hat) i) :=
        vecNorm2_add_le _ _
      _ = vecNorm2 (matMulVec n M1 (absVec n x_hat)) +
            3 * vecNorm2 (matMulVec n B (absVec n x_hat)) := by
        rw [vecNorm2_smul]
        norm_num
      _ ≤ c1 * vecNorm2 (absVec n x_hat) +
            3 * (cB * vecNorm2 (absVec n x_hat)) := by
        exact add_le_add (hM1 (absVec n x_hat))
          (mul_le_mul_of_nonneg_left (hB (absVec n x_hat)) (by norm_num))
      _ = (c1 + 3 * cB) * vecNorm2 (absVec n x_hat) := by ring
  have habsNorm : vecNorm2 (absVec n x_hat) = vecNorm2 x_hat := by
    simpa [absVec] using vecNorm2_abs x_hat
  change vecNorm2 e ≤ _
  calc
    vecNorm2 e ≤ vecNorm2 (fun i => c *
        (matMulVec n M1 (absVec n x_hat) i +
          3 * matMulVec n B (absVec n x_hat) i)) := hnorm
    _ = c * vecNorm2 (fun i =>
          matMulVec n M1 (absVec n x_hat) i +
            3 * matMulVec n B (absVec n x_hat) i) := by
      rw [vecNorm2_smul, abs_of_nonneg hc]
    _ ≤ c * ((c1 + 3 * cB) * vecNorm2 (absVec n x_hat)) :=
      mul_le_mul_of_nonneg_left hsum hc
    _ = 2 * (n : ℝ) * fp.u *
          ((n : ℝ) * Real.sqrt n * luFactor * kappa2 A A_inv +
            3 * (n : ℝ) * kappaRoot) * vecNorm2 x_hat := by
      rw [habsNorm]
      simp only [c, c1, cLU, cB]
      unfold kappa2
      ring

/-- **Corollary 14.6 residual with the exact Cholesky condition factor.**

Positive pivots and the symmetry-exploited factor relation produce the
perturbation `DeltaA` and `A + DeltaA = R_hatᵀ R_hat`.  Certified inverses of
`U_hat` and `R_hat` give the exact cancellation
`|U_hat⁻¹||U_hat| = |R_hat⁻¹||R_hat|`, so the residual bound contains
`sqrt(kappa₂(A + DeltaA))` without a separate `kappa₂(U_hat)` hypothesis. -/
theorem ch14ext_cor146_residual_positivePivot_exactGram_of_theorem14_5
    (n : ℕ) (fp : FPModel)
    (A L_hat U_hat U_inv R_inv : Fin n → Fin n → ℝ)
    (b x_hat : Fin n → ℝ)
    (luFactor : ℝ)
    (hSPD : IsSymPosDef n A)
    (hLU : LUBackwardError n A L_hat U_hat (gamma fp n))
    (hpiv : ∀ i : Fin n, 0 < U_hat i i)
    (hsym : ∀ i j : Fin n, U_hat i j = U_hat i i * L_hat j i)
    (hUInv : IsInverse n U_hat U_inv)
    (hRInv : IsInverse n (ch14ext_cor146_scaledUpper n U_hat) R_inv)
    (hluFactor : 0 ≤ luFactor)
    (hAbsLU : opNorm2Le
      (matMul n (absMatrix n L_hat) (absMatrix n U_hat))
      ((n : ℝ) * luFactor * opNorm2 A))
    (hRes : ∀ i : Fin n,
      |b i - ∑ j : Fin n, A i j * x_hat j| ≤
        8 * (n : ℝ) * fp.u *
          matMulVec n
            (matMul n
              (matMul n (absMatrix n L_hat) (absMatrix n U_hat))
              (matMul n (absMatrix n U_inv) (absMatrix n U_hat)))
            (absVec n x_hat) i) :
    vecNorm2 (fun i : Fin n => b i - ∑ j : Fin n, A i j * x_hat j) ≤
      8 * (n : ℝ) ^ 3 * fp.u * luFactor *
        Real.sqrt
          (kappa2
            (fun i j => A i j +
              ch14ext_cor146_symmetricGEDelta n A L_hat U_hat i j)
            (nonsingInv n (fun i j => A i j +
              ch14ext_cor146_symmetricGEDelta n A L_hat U_hat i j))) *
        opNorm2 A * vecNorm2 x_hat := by
  have hstruct :=
    ch14ext_cor146_positivePivot_cholesky_backward_error
      n fp A L_hat U_hat hSPD hLU hpiv hsym
  have hGram :
      matMul n
          (fun i j => ch14ext_cor146_scaledUpper n U_hat j i)
          (ch14ext_cor146_scaledUpper n U_hat) =
        (fun i j => A i j +
          ch14ext_cor146_symmetricGEDelta n A L_hat U_hat i j) := by
    funext i j
    exact (hstruct.2.1 i j).symm
  have hCond :=
    ch14ext_cor146_positivePivot_condU_opNorm2Le
      n L_hat U_hat U_inv R_inv hpiv hsym hRInv hUInv
  have hbase :=
    ch14ext_cor146_residual_twoFactor_of_cond_bound
      n fp A L_hat U_hat U_inv b x_hat luFactor
      (kappa2 (ch14ext_cor146_scaledUpper n U_hat) R_inv)
      hluFactor hAbsLU hCond hRes
  have hkappa :=
    ch14ext_cor146_kappa2_eq_sqrt_kappa2_gram
      n (ch14ext_cor146_scaledUpper n U_hat) R_inv hRInv
  have hkappa' :
      kappa2 (ch14ext_cor146_scaledUpper n U_hat) R_inv =
        Real.sqrt
          (kappa2
            (fun i j => A i j +
              ch14ext_cor146_symmetricGEDelta n A L_hat U_hat i j)
            (nonsingInv n (fun i j => A i j +
              ch14ext_cor146_symmetricGEDelta n A L_hat U_hat i j))) := by
    simpa only [hGram] using hkappa
  simpa only [hkappa'] using hbase

/-- **Corollary 14.6 forward error with the exact Cholesky condition factor.**

This is the relative form of the exact pre-asymptotic (14.32) reduction.  The
factor `||x_hat||₂ / ||x||₂` is retained rather than replaced by an unproved
fixed-model `1 + O(u)` statement. -/
theorem ch14ext_cor146_forward_relative_positivePivot_exactGram_of_theorem14_5
    (n : ℕ) (fp : FPModel)
    (A A_inv L_hat U_hat U_inv R_inv : Fin n → Fin n → ℝ)
    (x x_hat : Fin n → ℝ)
    (luFactor : ℝ)
    (hSPD : IsSymPosDef n A)
    (hLU : LUBackwardError n A L_hat U_hat (gamma fp n))
    (hpiv : ∀ i : Fin n, 0 < U_hat i i)
    (hsym : ∀ i j : Fin n, U_hat i j = U_hat i i * L_hat j i)
    (hUInv : IsInverse n U_hat U_inv)
    (hRInv : IsInverse n (ch14ext_cor146_scaledUpper n U_hat) R_inv)
    (hxpos : 0 < vecNorm2 x)
    (hluFactor : 0 ≤ luFactor)
    (hAbsLU : opNorm2Le
      (matMul n (absMatrix n L_hat) (absMatrix n U_hat))
      ((n : ℝ) * luFactor * opNorm2 A))
    (hFwd : ∀ i : Fin n,
      |x i - x_hat i| ≤
        2 * (n : ℝ) * fp.u *
          (matMulVec n
              (matMul n (absMatrix n A_inv)
                (matMul n (absMatrix n L_hat) (absMatrix n U_hat)))
              (absVec n x_hat) i +
            3 * matMulVec n
              (matMul n (absMatrix n U_inv) (absMatrix n U_hat))
              (absVec n x_hat) i)) :
    vecNorm2 (fun i : Fin n => x i - x_hat i) / vecNorm2 x ≤
      2 * (n : ℝ) * fp.u *
        ((n : ℝ) * Real.sqrt n * luFactor * kappa2 A A_inv +
          3 * (n : ℝ) *
            Real.sqrt
              (kappa2
                (fun i j => A i j +
                  ch14ext_cor146_symmetricGEDelta n A L_hat U_hat i j)
                (nonsingInv n (fun i j => A i j +
                  ch14ext_cor146_symmetricGEDelta n A L_hat U_hat i j)))) *
        (vecNorm2 x_hat / vecNorm2 x) := by
  have hstruct :=
    ch14ext_cor146_positivePivot_cholesky_backward_error
      n fp A L_hat U_hat hSPD hLU hpiv hsym
  have hGram :
      matMul n
          (fun i j => ch14ext_cor146_scaledUpper n U_hat j i)
          (ch14ext_cor146_scaledUpper n U_hat) =
        (fun i j => A i j +
          ch14ext_cor146_symmetricGEDelta n A L_hat U_hat i j) := by
    funext i j
    exact (hstruct.2.1 i j).symm
  have hCond :=
    ch14ext_cor146_positivePivot_condU_opNorm2Le
      n L_hat U_hat U_inv R_inv hpiv hsym hRInv hUInv
  have hbase :=
    ch14ext_cor146_forward_twoFactor_of_cond_bound
      n fp A A_inv L_hat U_hat U_inv x x_hat luFactor
      (kappa2 (ch14ext_cor146_scaledUpper n U_hat) R_inv)
      hluFactor hAbsLU hCond hFwd
  have hkappa :=
    ch14ext_cor146_kappa2_eq_sqrt_kappa2_gram
      n (ch14ext_cor146_scaledUpper n U_hat) R_inv hRInv
  have hkappa' :
      kappa2 (ch14ext_cor146_scaledUpper n U_hat) R_inv =
        Real.sqrt
          (kappa2
            (fun i j => A i j +
              ch14ext_cor146_symmetricGEDelta n A L_hat U_hat i j)
            (nonsingInv n (fun i j => A i j +
              ch14ext_cor146_symmetricGEDelta n A L_hat U_hat i j))) := by
    simpa only [hGram] using hkappa
  have habs :
      vecNorm2 (fun i : Fin n => x i - x_hat i) ≤
        2 * (n : ℝ) * fp.u *
          ((n : ℝ) * Real.sqrt n * luFactor * kappa2 A A_inv +
            3 * (n : ℝ) *
              Real.sqrt
                (kappa2
                  (fun i j => A i j +
                    ch14ext_cor146_symmetricGEDelta n A L_hat U_hat i j)
                  (nonsingInv n (fun i j => A i j +
                    ch14ext_cor146_symmetricGEDelta n A L_hat U_hat i j)))) *
          vecNorm2 x_hat := by
    simpa only [hkappa'] using hbase
  calc
    vecNorm2 (fun i : Fin n => x i - x_hat i) / vecNorm2 x ≤
        (2 * (n : ℝ) * fp.u *
          ((n : ℝ) * Real.sqrt n * luFactor * kappa2 A A_inv +
            3 * (n : ℝ) *
              Real.sqrt
                (kappa2
                  (fun i j => A i j +
                    ch14ext_cor146_symmetricGEDelta n A L_hat U_hat i j)
                  (nonsingInv n (fun i j => A i j +
                    ch14ext_cor146_symmetricGEDelta n A L_hat U_hat i j)))) *
          vecNorm2 x_hat) / vecNorm2 x :=
      div_le_div_of_nonneg_right habs hxpos.le
    _ = 2 * (n : ℝ) * fp.u *
          ((n : ℝ) * Real.sqrt n * luFactor * kappa2 A A_inv +
            3 * (n : ℝ) *
              Real.sqrt
                (kappa2
                  (fun i j => A i j +
                    ch14ext_cor146_symmetricGEDelta n A L_hat U_hat i j)
                  (nonsingInv n (fun i j => A i j +
                    ch14ext_cor146_symmetricGEDelta n A L_hat U_hat i j)))) *
          (vecNorm2 x_hat / vecNorm2 x) := by
      rw [mul_div_assoc]

/-- **Corollary 14.6 residual, direct two-factor specialization of (14.31).**

Assume the parent leading-order componentwise residual, the source Cholesky/LU
budget
`|| |L_hat||U_hat| ||_2 <= n * luFactor * ||A||_2`, and the condition-number
comparison `kappa_2(U_hat) <= kappaRoot`.  Then
`||b-A*x_hat||_2 <= 8 n^3 u luFactor kappaRoot ||A||_2 ||x_hat||_2`.

For Higham's proof, `luFactor = (1-n*gamma_n)⁻¹` and
`kappaRoot = kappa_2(A+DeltaA)^(1/2)`.  Neither structural premise mentions the
residual conclusion. -/
theorem ch14ext_cor146_residual_twoFactor_of_theorem14_5
    (n : ℕ) (fp : FPModel)
    (A L_hat U_hat U_inv : Fin n → Fin n → ℝ)
    (b x_hat : Fin n → ℝ)
    (luFactor kappaRoot : ℝ)
    (hluFactor : 0 ≤ luFactor)
    (hAbsLU : opNorm2Le
      (matMul n (absMatrix n L_hat) (absMatrix n U_hat))
      ((n : ℝ) * luFactor * opNorm2 A))
    (hKappaRoot : kappa2 U_hat U_inv ≤ kappaRoot)
    (hRes : ∀ i : Fin n,
      |b i - ∑ j : Fin n, A i j * x_hat j| ≤
        8 * (n : ℝ) * fp.u *
          matMulVec n
            (matMul n
              (matMul n (absMatrix n L_hat) (absMatrix n U_hat))
              (matMul n (absMatrix n U_inv) (absMatrix n U_hat)))
            (absVec n x_hat) i) :
    vecNorm2 (fun i : Fin n => b i - ∑ j : Fin n, A i j * x_hat j) ≤
      8 * (n : ℝ) ^ 3 * fp.u * luFactor * kappaRoot *
        opNorm2 A * vecNorm2 x_hat := by
  let MLU : Fin n → Fin n → ℝ :=
    matMul n (absMatrix n L_hat) (absMatrix n U_hat)
  let B : Fin n → Fin n → ℝ :=
    matMul n (absMatrix n U_inv) (absMatrix n U_hat)
  let r : Fin n → ℝ := fun i => b i - ∑ j : Fin n, A i j * x_hat j
  let cLU : ℝ := (n : ℝ) * luFactor * opNorm2 A
  let cB : ℝ := (n : ℝ) * kappaRoot
  let c : ℝ := 8 * (n : ℝ) * fp.u
  have hcLU : 0 ≤ cLU :=
    mul_nonneg (mul_nonneg (Nat.cast_nonneg n) hluFactor) (opNorm2_nonneg A)
  have hc : 0 ≤ c :=
    mul_nonneg (mul_nonneg (by norm_num) (Nat.cast_nonneg n)) fp.u_nonneg
  have hBbase := ch14ext_cor146_condU_opNorm2Le n U_hat U_inv
  have hB : opNorm2Le B cB := by
    apply opNorm2Le_mono (by simpa [B] using hBbase)
    exact mul_le_mul_of_nonneg_left hKappaRoot (Nat.cast_nonneg n)
  have hProd : opNorm2Le (matMul n MLU B) (cLU * cB) :=
    opNorm2Le_matMul n MLU B cLU cB hcLU (by simpa [MLU, cLU] using hAbsLU) hB
  have hAbs : ∀ i : Fin n,
      |r i| ≤ c * matMulVec n (matMul n MLU B) (absVec n x_hat) i := by
    intro i
    simpa [r, c, MLU, B] using hRes i
  have hnorm :=
    vecNorm2_le_of_abs_le r
      (fun i => c * matMulVec n (matMul n MLU B) (absVec n x_hat) i) hAbs
  have habsNorm : vecNorm2 (absVec n x_hat) = vecNorm2 x_hat := by
    simpa [absVec] using vecNorm2_abs x_hat
  change vecNorm2 r ≤ _
  calc
    vecNorm2 r ≤
        vecNorm2 (fun i => c * matMulVec n (matMul n MLU B) (absVec n x_hat) i) :=
      hnorm
    _ = c * vecNorm2 (matMulVec n (matMul n MLU B) (absVec n x_hat)) := by
      rw [vecNorm2_smul, abs_of_nonneg hc]
    _ ≤ c * ((cLU * cB) * vecNorm2 (absVec n x_hat)) :=
      mul_le_mul_of_nonneg_left (hProd (absVec n x_hat)) hc
    _ = 8 * (n : ℝ) ^ 3 * fp.u * luFactor * kappaRoot *
          opNorm2 A * vecNorm2 x_hat := by
      rw [habsNorm]
      simp only [c, cLU, cB]
      ring

/-- **Corollary 14.6 forward error, direct two-factor specialization of
(14.32).**

Under the same two source norm budgets as the residual theorem, the parent
componentwise forward-error endpoint gives
`2 n u (n sqrt(n) luFactor kappa_2(A) + 3 n kappaRoot) ||x_hat||_2`.
This is the exact pre-asymptotic norm reduction used before Higham weakens the
coefficient to the printed `8 n^(5/2) u kappa_2(A)`. -/
theorem ch14ext_cor146_forward_twoFactor_of_theorem14_5
    (n : ℕ) (fp : FPModel)
    (A A_inv L_hat U_hat U_inv : Fin n → Fin n → ℝ)
    (x x_hat : Fin n → ℝ)
    (luFactor kappaRoot : ℝ)
    (hluFactor : 0 ≤ luFactor)
    (hAbsLU : opNorm2Le
      (matMul n (absMatrix n L_hat) (absMatrix n U_hat))
      ((n : ℝ) * luFactor * opNorm2 A))
    (hKappaRoot : kappa2 U_hat U_inv ≤ kappaRoot)
    (hFwd : ∀ i : Fin n,
      |x i - x_hat i| ≤
        2 * (n : ℝ) * fp.u *
          (matMulVec n
              (matMul n (absMatrix n A_inv)
                (matMul n (absMatrix n L_hat) (absMatrix n U_hat)))
              (absVec n x_hat) i +
            3 * matMulVec n
              (matMul n (absMatrix n U_inv) (absMatrix n U_hat))
              (absVec n x_hat) i)) :
    vecNorm2 (fun i : Fin n => x i - x_hat i) ≤
      2 * (n : ℝ) * fp.u *
        ((n : ℝ) * Real.sqrt n * luFactor * kappa2 A A_inv +
          3 * (n : ℝ) * kappaRoot) * vecNorm2 x_hat := by
  let MLU : Fin n → Fin n → ℝ :=
    matMul n (absMatrix n L_hat) (absMatrix n U_hat)
  let M1 : Fin n → Fin n → ℝ := matMul n (absMatrix n A_inv) MLU
  let B : Fin n → Fin n → ℝ :=
    matMul n (absMatrix n U_inv) (absMatrix n U_hat)
  let e : Fin n → ℝ := fun i => x i - x_hat i
  let cLU : ℝ := (n : ℝ) * luFactor * opNorm2 A
  let c1 : ℝ := (Real.sqrt n * opNorm2 A_inv) * cLU
  let cB : ℝ := (n : ℝ) * kappaRoot
  let c : ℝ := 2 * (n : ℝ) * fp.u
  have hcLU : 0 ≤ cLU :=
    mul_nonneg (mul_nonneg (Nat.cast_nonneg n) hluFactor) (opNorm2_nonneg A)
  have hcAinv : 0 ≤ Real.sqrt n * opNorm2 A_inv :=
    mul_nonneg (Real.sqrt_nonneg _) (opNorm2_nonneg A_inv)
  have hc : 0 ≤ c :=
    mul_nonneg (mul_nonneg (by norm_num) (Nat.cast_nonneg n)) fp.u_nonneg
  have hAinvAbs : opNorm2Le (absMatrix n A_inv)
      (Real.sqrt n * opNorm2 A_inv) := by
    simpa [absMatrix] using
      opNorm2Le_abs_of_opNorm2Le n A_inv (opNorm2 A_inv)
        (opNorm2_nonneg A_inv) (opNorm2Le_opNorm2 A_inv)
  have hM1 : opNorm2Le M1 c1 := by
    exact opNorm2Le_matMul n (absMatrix n A_inv) MLU
      (Real.sqrt n * opNorm2 A_inv) cLU hcAinv hAinvAbs
      (by simpa [MLU, cLU] using hAbsLU)
  have hBbase := ch14ext_cor146_condU_opNorm2Le n U_hat U_inv
  have hB : opNorm2Le B cB := by
    apply opNorm2Le_mono (by simpa [B] using hBbase)
    exact mul_le_mul_of_nonneg_left hKappaRoot (Nat.cast_nonneg n)
  have hAbs : ∀ i : Fin n,
      |e i| ≤ c *
        (matMulVec n M1 (absVec n x_hat) i +
          3 * matMulVec n B (absVec n x_hat) i) := by
    intro i
    simpa [e, c, M1, MLU, B] using hFwd i
  have hnorm :=
    vecNorm2_le_of_abs_le e
      (fun i => c *
        (matMulVec n M1 (absVec n x_hat) i +
          3 * matMulVec n B (absVec n x_hat) i)) hAbs
  have hsum :
      vecNorm2 (fun i =>
          matMulVec n M1 (absVec n x_hat) i +
            3 * matMulVec n B (absVec n x_hat) i) ≤
        (c1 + 3 * cB) * vecNorm2 (absVec n x_hat) := by
    calc
      vecNorm2 (fun i =>
          matMulVec n M1 (absVec n x_hat) i +
            3 * matMulVec n B (absVec n x_hat) i) ≤
          vecNorm2 (matMulVec n M1 (absVec n x_hat)) +
            vecNorm2 (fun i => 3 * matMulVec n B (absVec n x_hat) i) :=
        vecNorm2_add_le _ _
      _ = vecNorm2 (matMulVec n M1 (absVec n x_hat)) +
            3 * vecNorm2 (matMulVec n B (absVec n x_hat)) := by
        rw [vecNorm2_smul]
        norm_num
      _ ≤ c1 * vecNorm2 (absVec n x_hat) +
            3 * (cB * vecNorm2 (absVec n x_hat)) := by
        exact add_le_add (hM1 (absVec n x_hat))
          (mul_le_mul_of_nonneg_left (hB (absVec n x_hat)) (by norm_num))
      _ = (c1 + 3 * cB) * vecNorm2 (absVec n x_hat) := by ring
  have habsNorm : vecNorm2 (absVec n x_hat) = vecNorm2 x_hat := by
    simpa [absVec] using vecNorm2_abs x_hat
  change vecNorm2 e ≤ _
  calc
    vecNorm2 e ≤ vecNorm2 (fun i => c *
        (matMulVec n M1 (absVec n x_hat) i +
          3 * matMulVec n B (absVec n x_hat) i)) := hnorm
    _ = c * vecNorm2 (fun i =>
          matMulVec n M1 (absVec n x_hat) i +
            3 * matMulVec n B (absVec n x_hat) i) := by
      rw [vecNorm2_smul, abs_of_nonneg hc]
    _ ≤ c * ((c1 + 3 * cB) * vecNorm2 (absVec n x_hat)) :=
      mul_le_mul_of_nonneg_left hsum hc
    _ = 2 * (n : ℝ) * fp.u *
          ((n : ℝ) * Real.sqrt n * luFactor * kappa2 A A_inv +
            3 * (n : ℝ) * kappaRoot) * vecNorm2 x_hat := by
      rw [habsNorm]
      simp only [c, c1, cLU, cB]
      unfold kappa2
      ring

/-- **Corollary 14.6 forward stability, printed leading coefficient.**

At first-order strength, take `|| |L_hat||U_hat| ||_2 <= n||A||_2` and
`kappa_2(U_hat) <= kappa_2(A)`.  For `n >= 1`, the direct (14.32)
specialization weakens to Higham's printed
`8 n^(5/2) u kappa_2(A) ||x_hat||_2` bound.  The factor `n^(5/2)` is represented
as `n^2 * sqrt(n)`. -/
theorem ch14ext_cor146_forward_printed_leading_of_theorem14_5
    (n : ℕ) (fp : FPModel) (hn : 1 ≤ n)
    (A A_inv L_hat U_hat U_inv : Fin n → Fin n → ℝ)
    (x x_hat : Fin n → ℝ)
    (hAbsLU : opNorm2Le
      (matMul n (absMatrix n L_hat) (absMatrix n U_hat))
      ((n : ℝ) * opNorm2 A))
    (hKappa : kappa2 U_hat U_inv ≤ kappa2 A A_inv)
    (hFwd : ∀ i : Fin n,
      |x i - x_hat i| ≤
        2 * (n : ℝ) * fp.u *
          (matMulVec n
              (matMul n (absMatrix n A_inv)
                (matMul n (absMatrix n L_hat) (absMatrix n U_hat)))
              (absVec n x_hat) i +
            3 * matMulVec n
              (matMul n (absMatrix n U_inv) (absMatrix n U_hat))
              (absVec n x_hat) i)) :
    vecNorm2 (fun i : Fin n => x i - x_hat i) ≤
      8 * (n : ℝ) ^ 2 * Real.sqrt n * fp.u * kappa2 A A_inv *
        vecNorm2 x_hat := by
  have hbase :
      vecNorm2 (fun i : Fin n => x i - x_hat i) ≤
        2 * (n : ℝ) * fp.u *
          ((n : ℝ) * Real.sqrt n * kappa2 A A_inv +
            3 * (n : ℝ) * kappa2 A A_inv) * vecNorm2 x_hat := by
    simpa using
      ch14ext_cor146_forward_twoFactor_of_theorem14_5
        n fp A A_inv L_hat U_hat U_inv x x_hat
        1 (kappa2 A A_inv) (by norm_num)
        (by simpa using hAbsLU) hKappa hFwd
  have hnR : (1 : ℝ) ≤ (n : ℝ) := by exact_mod_cast hn
  have hsqrtOne : (1 : ℝ) ≤ Real.sqrt n := by
    have hsqrt := Real.sqrt_le_sqrt hnR
    simpa using hsqrt
  have hkap : 0 ≤ kappa2 A A_inv := by
    unfold kappa2
    exact mul_nonneg (opNorm2_nonneg A) (opNorm2_nonneg A_inv)
  have hthree :
      3 * (n : ℝ) * kappa2 A A_inv ≤
        3 * (n : ℝ) * Real.sqrt n * kappa2 A A_inv := by
    calc
      3 * (n : ℝ) * kappa2 A A_inv =
          (3 * (n : ℝ) * kappa2 A A_inv) * 1 := by ring
      _ ≤ (3 * (n : ℝ) * kappa2 A A_inv) * Real.sqrt n :=
        mul_le_mul_of_nonneg_left hsqrtOne
          (mul_nonneg (mul_nonneg (by norm_num) (Nat.cast_nonneg n)) hkap)
      _ = 3 * (n : ℝ) * Real.sqrt n * kappa2 A A_inv := by ring
  have hinner :
      (n : ℝ) * Real.sqrt n * kappa2 A A_inv +
          3 * (n : ℝ) * kappa2 A A_inv ≤
        4 * (n : ℝ) * Real.sqrt n * kappa2 A A_inv := by
    calc
      (n : ℝ) * Real.sqrt n * kappa2 A A_inv +
          3 * (n : ℝ) * kappa2 A A_inv ≤
        (n : ℝ) * Real.sqrt n * kappa2 A A_inv +
          3 * (n : ℝ) * Real.sqrt n * kappa2 A A_inv :=
        add_le_add (le_refl _) hthree
      _ = 4 * (n : ℝ) * Real.sqrt n * kappa2 A A_inv := by ring
  have h2nu : 0 ≤ 2 * (n : ℝ) * fp.u :=
    mul_nonneg (mul_nonneg (by norm_num) (Nat.cast_nonneg n)) fp.u_nonneg
  calc
    vecNorm2 (fun i : Fin n => x i - x_hat i) ≤
        2 * (n : ℝ) * fp.u *
          ((n : ℝ) * Real.sqrt n * kappa2 A A_inv +
            3 * (n : ℝ) * kappa2 A A_inv) * vecNorm2 x_hat := hbase
    _ ≤ 2 * (n : ℝ) * fp.u *
          (4 * (n : ℝ) * Real.sqrt n * kappa2 A A_inv) * vecNorm2 x_hat :=
      mul_le_mul_of_nonneg_right
        (mul_le_mul_of_nonneg_left hinner h2nu) (vecNorm2_nonneg x_hat)
    _ = 8 * (n : ℝ) ^ 2 * Real.sqrt n * fp.u * kappa2 A A_inv *
          vecNorm2 x_hat := by ring

/-- Relative-2-norm form of
`ch14ext_cor146_forward_printed_leading_of_theorem14_5`.
The explicit `||x_hat||_2 / ||x||_2` factor is retained; Higham absorbs its
`1 + O(u)` expansion into the displayed `O(u^2)` remainder. -/
theorem ch14ext_cor146_forward_relative_printed_leading_of_theorem14_5
    (n : ℕ) (fp : FPModel) (hn : 1 ≤ n)
    (A A_inv L_hat U_hat U_inv : Fin n → Fin n → ℝ)
    (x x_hat : Fin n → ℝ)
    (hxpos : 0 < vecNorm2 x)
    (hAbsLU : opNorm2Le
      (matMul n (absMatrix n L_hat) (absMatrix n U_hat))
      ((n : ℝ) * opNorm2 A))
    (hKappa : kappa2 U_hat U_inv ≤ kappa2 A A_inv)
    (hFwd : ∀ i : Fin n,
      |x i - x_hat i| ≤
        2 * (n : ℝ) * fp.u *
          (matMulVec n
              (matMul n (absMatrix n A_inv)
                (matMul n (absMatrix n L_hat) (absMatrix n U_hat)))
              (absVec n x_hat) i +
            3 * matMulVec n
              (matMul n (absMatrix n U_inv) (absMatrix n U_hat))
              (absVec n x_hat) i)) :
    vecNorm2 (fun i : Fin n => x i - x_hat i) / vecNorm2 x ≤
      8 * (n : ℝ) ^ 2 * Real.sqrt n * fp.u * kappa2 A A_inv *
        (vecNorm2 x_hat / vecNorm2 x) := by
  have habs :=
    ch14ext_cor146_forward_printed_leading_of_theorem14_5
      n fp hn A A_inv L_hat U_hat U_inv x x_hat hAbsLU hKappa hFwd
  calc
    vecNorm2 (fun i : Fin n => x i - x_hat i) / vecNorm2 x ≤
        (8 * (n : ℝ) ^ 2 * Real.sqrt n * fp.u * kappa2 A A_inv *
          vecNorm2 x_hat) / vecNorm2 x :=
      div_le_div_of_nonneg_right habs (le_of_lt hxpos)
    _ = 8 * (n : ℝ) ^ 2 * Real.sqrt n * fp.u * kappa2 A A_inv *
          (vecNorm2 x_hat / vecNorm2 x) := by
      rw [mul_div_assoc]

-- ═══════════════════════════════════════════════════════════════════════════
-- §2  Legacy accumulation residual route, aggregation constants derived
-- ═══════════════════════════════════════════════════════════════════════════

/-- **Legacy accumulation surrogate for the Corollary 14.6 residual.**

    Specialises Codex's
    `gje_spd_residual_relative_norm2_of_cumulative_product_certificates_c3_cap`
    by discharging its three free norm-aggregation constants from the
    SPD/Cholesky Lemma-6.6 operator-2 chain of §1.  First stage
    `alpha = n‖R̂‖₂²` is the printed budget `‖|L̂||Û|‖₂ ≤ n‖A‖₂`
    (`‖R̂‖₂² = ‖A‖₂` under exact Cholesky, §3′); the second-stage constants are
    the accumulation three-factor terms `beta = n^{3/2}‖R̂‖₂²‖R̂⁻¹‖₂`,
    `eta = n‖R̂‖₂‖R̂⁻¹‖₂·c_y`, with `c_y` the intermediate-vector norm ratio
    `‖y‖₂ ≤ c_y‖x̂‖₂`. -/
theorem ch14ext_gje_spd_residual_relative_norm2_derived
    (n : ℕ) (fp : FPModel)
    (A R_hat R_inv : Fin n → Fin n → ℝ)
    (b y x_hat : Fin n → ℝ)
    (N_hat DeltaN : Fin n → Fin n → Fin n → ℝ)
    (start : ℕ)
    (hSPD : IsSymPosDef n A)
    (hLU : LUBackwardError n A (fun i j => R_hat j i) R_hat (gamma fp n))
    (hn : gammaValid fp n)
    (hnpos : 1 ≤ n)
    (hn3 : gammaValid fp 3)
    (hidx : ∀ r : Fin (n - 1),
      start + ((n - 1) - 1 - r.val) < n)
    (hDelta : ∀ r : Fin (n - 1), ∀ i j : Fin n,
      |DeltaN (Fin.mk (start + ((n - 1) - 1 - r.val)) (hidx r)) i j| ≤
        gamma fp 3 *
          |N_hat (Fin.mk (start + ((n - 1) - 1 - r.val)) (hidx r)) i j|)
    (hy : ∀ i : Fin n, ∑ j : Fin n, R_hat j i * y j = b i)
    (hBackwardEq : ∀ i : Fin n,
      ∑ j : Fin n,
          (R_hat i j +
            (matMul n
                (gje_cumulative_product n
                  (fun k a b => N_hat k a b + DeltaN k a b)
                  start (start + (n - 1))) R_hat i j -
              matMul n
                (gje_cumulative_product n N_hat start (start + (n - 1)))
                R_hat i j)) *
            x_hat j =
        y i +
          (matMulVec n
              (gje_cumulative_product n
                (fun k a b => N_hat k a b + DeltaN k a b)
                start (start + (n - 1))) y i -
            matMulVec n
              (gje_cumulative_product n N_hat start (start + (n - 1))) y i))
    (hRinvDom : ∀ i j : Fin n,
      |gje_cumulative_product n (fun s a b => |N_hat s a b|)
        start (start + (n - 1)) i j| ≤ |R_inv i j|)
    (hApos : 0 < opNorm2 A) (hxpos : 0 < vecNorm2 x_hat)
    (cy : ℝ) (hcy : 0 ≤ cy)
    (hyx : vecNorm2 y ≤ cy * vecNorm2 x_hat) :
    vecNorm2 (fun i : Fin n => b i - ∑ j : Fin n, A i j * x_hat j) /
        (opNorm2 A * vecNorm2 x_hat) ≤
      (gamma fp n * ((n : ℝ) * opNorm2 R_hat ^ 2) +
          (3 * (n : ℝ) * fp.u + gje_c3_quadratic_remainder fp n) *
            (((n : ℝ) * Real.sqrt n * opNorm2 R_hat ^ 2 * opNorm2 R_inv) +
              ((n : ℝ) * opNorm2 R_hat * opNorm2 R_inv * cy))) / opNorm2 A := by
  have hcprod : 0 ≤ (n : ℝ) * opNorm2 R_hat * opNorm2 R_inv :=
    mul_nonneg (mul_nonneg (Nat.cast_nonneg n) (opNorm2_nonneg R_hat))
      (opNorm2_nonneg R_inv)
  have hbeta : 0 ≤ (n : ℝ) * Real.sqrt n * opNorm2 R_hat ^ 2 * opNorm2 R_inv :=
    mul_nonneg (mul_nonneg (mul_nonneg (Nat.cast_nonneg n) (Real.sqrt_nonneg _))
      (pow_nonneg (opNorm2_nonneg R_hat) 2)) (opNorm2_nonneg R_inv)
  have heta : 0 ≤ (n : ℝ) * opNorm2 R_hat * opNorm2 R_inv * cy :=
    mul_nonneg hcprod hcy
  have hRT_Rinv_y :
      vecNorm2 (fun i : Fin n =>
        ∑ k : Fin n, |R_hat k i| *
          (∑ j : Fin n, |R_inv k j| * |y j|)) ≤
        ((n : ℝ) * opNorm2 R_hat * opNorm2 R_inv * cy) * vecNorm2 x_hat := by
    calc vecNorm2 (fun i : Fin n =>
          ∑ k : Fin n, |R_hat k i| * (∑ j : Fin n, |R_inv k j| * |y j|))
        ≤ (n : ℝ) * opNorm2 R_hat * opNorm2 R_inv * vecNorm2 y :=
          ch14ext_spd_secondStageY_agg_le n R_hat R_inv y
      _ ≤ (n : ℝ) * opNorm2 R_hat * opNorm2 R_inv * (cy * vecNorm2 x_hat) :=
          mul_le_mul_of_nonneg_left hyx hcprod
      _ = ((n : ℝ) * opNorm2 R_hat * opNorm2 R_inv * cy) * vecNorm2 x_hat := by ring
  exact gje_spd_residual_relative_norm2_of_cumulative_product_certificates_c3_cap
    n fp A R_hat R_inv b y x_hat N_hat DeltaN start
    hSPD hLU hn hnpos hn3 hidx hDelta hy hBackwardEq hRinvDom
    ((n : ℝ) * opNorm2 R_hat ^ 2)
    ((n : ℝ) * Real.sqrt n * opNorm2 R_hat ^ 2 * opNorm2 R_inv)
    ((n : ℝ) * opNorm2 R_hat * opNorm2 R_inv * cy)
    hApos hxpos hbeta heta
    (ch14ext_spd_firstStage_agg_le n R_hat x_hat)
    (ch14ext_spd_secondStageX_agg_le n R_hat R_inv x_hat)
    hRT_Rinv_y

-- ═══════════════════════════════════════════════════════════════════════════
-- §3  Legacy accumulation forward route, aggregation derived
-- ═══════════════════════════════════════════════════════════════════════════

/-- **Legacy accumulation surrogate for the Corollary 14.6 forward error.**

    Forward-error companion to §2, specialising Codex's
    `gje_spd_forward_error_relative_norm2_of_cumulative_product_certificates_c3_cap`
    with the same discharged `alpha`, `beta`, `eta`.  The `‖|A⁻¹|‖₂` outer
    factor is kept as in the wrapper; §3′ reduces it to `√n‖A⁻¹‖₂` and exposes
    the printed leading constant `n^{3/2}γ_n κ₂(A)`. -/
theorem ch14ext_gje_spd_forward_error_relative_norm2_derived
    (n : ℕ) (fp : FPModel)
    (A A_inv R_hat R_inv : Fin n → Fin n → ℝ)
    (b y x x_hat : Fin n → ℝ)
    (N_hat DeltaN : Fin n → Fin n → Fin n → ℝ)
    (start : ℕ)
    (hSPD : IsSymPosDef n A)
    (hLU : LUBackwardError n A (fun i j => R_hat j i) R_hat (gamma fp n))
    (hAinv : IsLeftInverse n A A_inv)
    (hn : gammaValid fp n)
    (hnpos : 1 ≤ n)
    (hn3 : gammaValid fp 3)
    (hidx : ∀ r : Fin (n - 1),
      start + ((n - 1) - 1 - r.val) < n)
    (hDelta : ∀ r : Fin (n - 1), ∀ i j : Fin n,
      |DeltaN (Fin.mk (start + ((n - 1) - 1 - r.val)) (hidx r)) i j| ≤
        gamma fp 3 *
          |N_hat (Fin.mk (start + ((n - 1) - 1 - r.val)) (hidx r)) i j|)
    (hy : ∀ i : Fin n, ∑ j : Fin n, R_hat j i * y j = b i)
    (hExact : ∀ i : Fin n, ∑ j : Fin n, A i j * x j = b i)
    (hBackwardEq : ∀ i : Fin n,
      ∑ j : Fin n,
          (R_hat i j +
            (matMul n
                (gje_cumulative_product n
                  (fun k a b => N_hat k a b + DeltaN k a b)
                  start (start + (n - 1))) R_hat i j -
              matMul n
                (gje_cumulative_product n N_hat start (start + (n - 1)))
                R_hat i j)) *
            x_hat j =
        y i +
          (matMulVec n
              (gje_cumulative_product n
                (fun k a b => N_hat k a b + DeltaN k a b)
                start (start + (n - 1))) y i -
            matMulVec n
              (gje_cumulative_product n N_hat start (start + (n - 1))) y i))
    (hRinvDom : ∀ i j : Fin n,
      |gje_cumulative_product n (fun s a b => |N_hat s a b|)
        start (start + (n - 1)) i j| ≤ |R_inv i j|)
    (hxpos : 0 < vecNorm2 x)
    (cy : ℝ) (hcy : 0 ≤ cy)
    (hyx : vecNorm2 y ≤ cy * vecNorm2 x_hat) :
    vecNorm2 (fun i : Fin n => x i - x_hat i) / vecNorm2 x ≤
      opNorm2 (fun i j : Fin n => |A_inv i j|) *
        (gamma fp n * ((n : ℝ) * opNorm2 R_hat ^ 2) +
          (3 * (n : ℝ) * fp.u + gje_c3_quadratic_remainder fp n) *
            (((n : ℝ) * Real.sqrt n * opNorm2 R_hat ^ 2 * opNorm2 R_inv) +
              ((n : ℝ) * opNorm2 R_hat * opNorm2 R_inv * cy))) *
        (vecNorm2 x_hat / vecNorm2 x) := by
  have hcprod : 0 ≤ (n : ℝ) * opNorm2 R_hat * opNorm2 R_inv :=
    mul_nonneg (mul_nonneg (Nat.cast_nonneg n) (opNorm2_nonneg R_hat))
      (opNorm2_nonneg R_inv)
  have hbeta : 0 ≤ (n : ℝ) * Real.sqrt n * opNorm2 R_hat ^ 2 * opNorm2 R_inv :=
    mul_nonneg (mul_nonneg (mul_nonneg (Nat.cast_nonneg n) (Real.sqrt_nonneg _))
      (pow_nonneg (opNorm2_nonneg R_hat) 2)) (opNorm2_nonneg R_inv)
  have heta : 0 ≤ (n : ℝ) * opNorm2 R_hat * opNorm2 R_inv * cy :=
    mul_nonneg hcprod hcy
  have hRT_Rinv_y :
      vecNorm2 (fun i : Fin n =>
        ∑ k : Fin n, |R_hat k i| *
          (∑ j : Fin n, |R_inv k j| * |y j|)) ≤
        ((n : ℝ) * opNorm2 R_hat * opNorm2 R_inv * cy) * vecNorm2 x_hat := by
    calc vecNorm2 (fun i : Fin n =>
          ∑ k : Fin n, |R_hat k i| * (∑ j : Fin n, |R_inv k j| * |y j|))
        ≤ (n : ℝ) * opNorm2 R_hat * opNorm2 R_inv * vecNorm2 y :=
          ch14ext_spd_secondStageY_agg_le n R_hat R_inv y
      _ ≤ (n : ℝ) * opNorm2 R_hat * opNorm2 R_inv * (cy * vecNorm2 x_hat) :=
          mul_le_mul_of_nonneg_left hyx hcprod
      _ = ((n : ℝ) * opNorm2 R_hat * opNorm2 R_inv * cy) * vecNorm2 x_hat := by ring
  exact gje_spd_forward_error_relative_norm2_of_cumulative_product_certificates_c3_cap
    n fp A A_inv R_hat R_inv b y x x_hat N_hat DeltaN start
    hSPD hLU hAinv hn hnpos hn3 hidx hDelta hy hExact hBackwardEq hRinvDom
    ((n : ℝ) * opNorm2 R_hat ^ 2)
    ((n : ℝ) * Real.sqrt n * opNorm2 R_hat ^ 2 * opNorm2 R_inv)
    ((n : ℝ) * opNorm2 R_hat * opNorm2 R_inv * cy)
    hxpos hbeta heta
    (ch14ext_spd_firstStage_agg_le n R_hat x_hat)
    (ch14ext_spd_secondStageX_agg_le n R_hat R_inv x_hat)
    hRT_Rinv_y

-- ═══════════════════════════════════════════════════════════════════════════
-- §3′  Legacy accumulation forward route with a κ₂(A) leading term
-- ═══════════════════════════════════════════════════════════════════════════

/-- **Legacy accumulation route with the printed `κ₂(A)` leading term**
    (Higham, 2nd ed., p. 277, second display).

    For the exact SPD Cholesky factorisation `A = R̂ᵀR̂` (`hChol`), the relative
    forward error satisfies

    `‖x - x̂‖₂ / ‖x‖₂ ≤ (n^{3/2} γ_n κ₂(A) + √n‖A⁻¹‖₂ · C · (β + η)) · (‖x̂‖₂/‖x‖₂)`

    where `C = 3nu + gje_c3_quadratic_remainder`,
    `β = n^{3/2}‖A‖₂‖R̂⁻¹‖₂`, `η = n‖R̂‖₂‖R̂⁻¹‖₂ c_y`.

    The **leading** coefficient `n^{3/2} γ_n κ₂(A)` is exactly Higham's dominant
    first `(14.32)` term `2nu‖|A⁻¹||L̂||Û|‖₂ ≤ 2n^{5/2}u κ₂(A)` — the printed
    forward-stability constant `8n^{5/2}u κ₂(A)` at leading order — obtained by
    combining the spectral Cholesky identity `‖R̂‖₂² = ‖A‖₂`
    (`ch14ext_opNorm2_transpose_mul_self_eq` + `hChol`), the first-stage
    Lemma-6.6 budget `‖|R̂ᵀ||R̂|‖₂ ≤ n‖A‖₂`, and the Lemma-6.6 bound
    `‖|A⁻¹|‖₂ ≤ √n‖A⁻¹‖₂`.  `κ₂(A) = ‖A‖₂‖A⁻¹‖₂` is the repository `kappa2`.

    The second additive term is the honest accumulation second-stage remainder
    (three-factor `|R̂ᵀ||R̂⁻¹||R̂|`), kept explicit; it is a genuinely different,
    scale-dependent quantity from the printed two-factor `|Û⁻¹||Û|`, hence not
    folded into a `κ₂^{1/2}` multiple (see the closing residual note). -/
theorem ch14ext_gje_spd_forward_stability_kappa2_leading
    (n : ℕ) (fp : FPModel)
    (A A_inv R_hat R_inv : Fin n → Fin n → ℝ)
    (b y x x_hat : Fin n → ℝ)
    (N_hat DeltaN : Fin n → Fin n → Fin n → ℝ)
    (start : ℕ)
    (hSPD : IsSymPosDef n A)
    (hLU : LUBackwardError n A (fun i j => R_hat j i) R_hat (gamma fp n))
    (hAinv : IsLeftInverse n A A_inv)
    (hn : gammaValid fp n)
    (hnpos : 1 ≤ n)
    (hn3 : gammaValid fp 3)
    (hidx : ∀ r : Fin (n - 1),
      start + ((n - 1) - 1 - r.val) < n)
    (hDelta : ∀ r : Fin (n - 1), ∀ i j : Fin n,
      |DeltaN (Fin.mk (start + ((n - 1) - 1 - r.val)) (hidx r)) i j| ≤
        gamma fp 3 *
          |N_hat (Fin.mk (start + ((n - 1) - 1 - r.val)) (hidx r)) i j|)
    (hy : ∀ i : Fin n, ∑ j : Fin n, R_hat j i * y j = b i)
    (hExact : ∀ i : Fin n, ∑ j : Fin n, A i j * x j = b i)
    (hBackwardEq : ∀ i : Fin n,
      ∑ j : Fin n,
          (R_hat i j +
            (matMul n
                (gje_cumulative_product n
                  (fun k a b => N_hat k a b + DeltaN k a b)
                  start (start + (n - 1))) R_hat i j -
              matMul n
                (gje_cumulative_product n N_hat start (start + (n - 1)))
                R_hat i j)) *
            x_hat j =
        y i +
          (matMulVec n
              (gje_cumulative_product n
                (fun k a b => N_hat k a b + DeltaN k a b)
                start (start + (n - 1))) y i -
            matMulVec n
              (gje_cumulative_product n N_hat start (start + (n - 1))) y i))
    (hRinvDom : ∀ i j : Fin n,
      |gje_cumulative_product n (fun s a b => |N_hat s a b|)
        start (start + (n - 1)) i j| ≤ |R_inv i j|)
    (hxpos : 0 < vecNorm2 x)
    (cy : ℝ) (hcy : 0 ≤ cy)
    (hyx : vecNorm2 y ≤ cy * vecNorm2 x_hat)
    (hChol : matMul n (fun i j => R_hat j i) R_hat = A) :
    vecNorm2 (fun i : Fin n => x i - x_hat i) / vecNorm2 x ≤
      ((n : ℝ) * Real.sqrt n * gamma fp n * kappa2 A A_inv +
          Real.sqrt n * opNorm2 A_inv *
            (3 * (n : ℝ) * fp.u + gje_c3_quadratic_remainder fp n) *
            (((n : ℝ) * Real.sqrt n * opNorm2 A * opNorm2 R_inv) +
              ((n : ℝ) * opNorm2 R_hat * opNorm2 R_inv * cy))) *
        (vecNorm2 x_hat / vecNorm2 x) := by
  have heqA : opNorm2 R_hat ^ 2 = opNorm2 A := by
    rw [← ch14ext_opNorm2_transpose_mul_self_eq n R_hat, hChol]
  have hFwd :=
    ch14ext_gje_spd_forward_error_relative_norm2_derived
      n fp A A_inv R_hat R_inv b y x x_hat N_hat DeltaN start
      hSPD hLU hAinv hn hnpos hn3 hidx hDelta hy hExact hBackwardEq hRinvDom
      hxpos cy hcy hyx
  rw [heqA] at hFwd
  -- nonnegativity of the middle factor and the norm ratio
  have hgamma : 0 ≤ gamma fp n := gamma_nonneg fp hn
  have hnA : 0 ≤ (n : ℝ) * opNorm2 A :=
    mul_nonneg (Nat.cast_nonneg n) (opNorm2_nonneg A)
  have hC_nonneg : 0 ≤ 3 * (n : ℝ) * fp.u + gje_c3_quadratic_remainder fp n :=
    le_trans (gje_c3_nonneg fp n hnpos hn3)
      (gje_c3_le_three_n_u_plus_quadratic_remainder fp n hn3)
  have hBETA : 0 ≤ (n : ℝ) * Real.sqrt n * opNorm2 A * opNorm2 R_inv :=
    mul_nonneg (mul_nonneg (mul_nonneg (Nat.cast_nonneg n) (Real.sqrt_nonneg _))
      (opNorm2_nonneg A)) (opNorm2_nonneg R_inv)
  have hETA : 0 ≤ (n : ℝ) * opNorm2 R_hat * opNorm2 R_inv * cy :=
    mul_nonneg (mul_nonneg (mul_nonneg (Nat.cast_nonneg n) (opNorm2_nonneg R_hat))
      (opNorm2_nonneg R_inv)) hcy
  have hratio : 0 ≤ vecNorm2 x_hat / vecNorm2 x :=
    div_nonneg (vecNorm2_nonneg x_hat) (vecNorm2_nonneg x)
  have hMid : 0 ≤ gamma fp n * ((n : ℝ) * opNorm2 A) +
      (3 * (n : ℝ) * fp.u + gje_c3_quadratic_remainder fp n) *
        (((n : ℝ) * Real.sqrt n * opNorm2 A * opNorm2 R_inv) +
          ((n : ℝ) * opNorm2 R_hat * opNorm2 R_inv * cy)) :=
    add_nonneg (mul_nonneg hgamma hnA)
      (mul_nonneg hC_nonneg (add_nonneg hBETA hETA))
  have hSr : 0 ≤ (gamma fp n * ((n : ℝ) * opNorm2 A) +
      (3 * (n : ℝ) * fp.u + gje_c3_quadratic_remainder fp n) *
        (((n : ℝ) * Real.sqrt n * opNorm2 A * opNorm2 R_inv) +
          ((n : ℝ) * opNorm2 R_hat * opNorm2 R_inv * cy)))
      * (vecNorm2 x_hat / vecNorm2 x) :=
    mul_nonneg hMid hratio
  calc vecNorm2 (fun i : Fin n => x i - x_hat i) / vecNorm2 x
      ≤ opNorm2 (fun i j : Fin n => |A_inv i j|) *
          (gamma fp n * ((n : ℝ) * opNorm2 A) +
            (3 * (n : ℝ) * fp.u + gje_c3_quadratic_remainder fp n) *
              (((n : ℝ) * Real.sqrt n * opNorm2 A * opNorm2 R_inv) +
                ((n : ℝ) * opNorm2 R_hat * opNorm2 R_inv * cy))) *
          (vecNorm2 x_hat / vecNorm2 x) := hFwd
    _ = opNorm2 (fun i j : Fin n => |A_inv i j|) *
          ((gamma fp n * ((n : ℝ) * opNorm2 A) +
            (3 * (n : ℝ) * fp.u + gje_c3_quadratic_remainder fp n) *
              (((n : ℝ) * Real.sqrt n * opNorm2 A * opNorm2 R_inv) +
                ((n : ℝ) * opNorm2 R_hat * opNorm2 R_inv * cy))) *
          (vecNorm2 x_hat / vecNorm2 x)) := by ring
    _ ≤ (Real.sqrt n * opNorm2 A_inv) *
          ((gamma fp n * ((n : ℝ) * opNorm2 A) +
            (3 * (n : ℝ) * fp.u + gje_c3_quadratic_remainder fp n) *
              (((n : ℝ) * Real.sqrt n * opNorm2 A * opNorm2 R_inv) +
                ((n : ℝ) * opNorm2 R_hat * opNorm2 R_inv * cy))) *
          (vecNorm2 x_hat / vecNorm2 x)) :=
        mul_le_mul_of_nonneg_right (ch14ext_opNorm2_absMatrix_le n A_inv) hSr
    _ = ((n : ℝ) * Real.sqrt n * gamma fp n * kappa2 A A_inv +
          Real.sqrt n * opNorm2 A_inv *
            (3 * (n : ℝ) * fp.u + gje_c3_quadratic_remainder fp n) *
            (((n : ℝ) * Real.sqrt n * opNorm2 A * opNorm2 R_inv) +
              ((n : ℝ) * opNorm2 R_hat * opNorm2 R_inv * cy))) *
          (vecNorm2 x_hat / vecNorm2 x) := by
        unfold kappa2; ring

-- ═══════════════════════════════════════════════════════════════════════════
-- §2′  Legacy accumulation residual, exact-Cholesky first stage exposed
-- ═══════════════════════════════════════════════════════════════════════════

/-- **Legacy accumulation residual, exact-Cholesky first-stage form**.

    For the exact SPD Cholesky factorisation `A = R̂ᵀR̂` (`hChol`), the
    relative-2-norm residual satisfies

    `‖b - Ax̂‖₂ / (‖A‖₂‖x̂‖₂) ≤ n γ_n + C · (β + η)/‖A‖₂`,

    where `C = 3nu + gje_c3_quadratic_remainder`,
    `β = n^{3/2}‖A‖₂‖R̂⁻¹‖₂`, `η = n‖R̂‖₂‖R̂⁻¹‖₂ c_y`.

    The scale-invariant first term `n γ_n` is the accumulation first-stage
    `γ_n‖|L̂||Û|‖₂ / ‖A‖₂` with the printed budget `‖|L̂||Û|‖₂ ≤ n‖A‖₂`
    (spectral Cholesky identity `‖R̂‖₂² = ‖A‖₂`).  The second term is the honest
    accumulation second-stage remainder.  The printed `8n³u κ₂(A)^{1/2}`
    residual constant is *not* reached here: it requires the (14.31) two-factor
    `|Û⁻¹||Û|` shape rather than the accumulation three-factor term (residual
    note at end of file). -/
theorem ch14ext_gje_spd_residual_relative_norm2_exact_cholesky
    (n : ℕ) (fp : FPModel)
    (A R_hat R_inv : Fin n → Fin n → ℝ)
    (b y x_hat : Fin n → ℝ)
    (N_hat DeltaN : Fin n → Fin n → Fin n → ℝ)
    (start : ℕ)
    (hSPD : IsSymPosDef n A)
    (hLU : LUBackwardError n A (fun i j => R_hat j i) R_hat (gamma fp n))
    (hn : gammaValid fp n)
    (hnpos : 1 ≤ n)
    (hn3 : gammaValid fp 3)
    (hidx : ∀ r : Fin (n - 1),
      start + ((n - 1) - 1 - r.val) < n)
    (hDelta : ∀ r : Fin (n - 1), ∀ i j : Fin n,
      |DeltaN (Fin.mk (start + ((n - 1) - 1 - r.val)) (hidx r)) i j| ≤
        gamma fp 3 *
          |N_hat (Fin.mk (start + ((n - 1) - 1 - r.val)) (hidx r)) i j|)
    (hy : ∀ i : Fin n, ∑ j : Fin n, R_hat j i * y j = b i)
    (hBackwardEq : ∀ i : Fin n,
      ∑ j : Fin n,
          (R_hat i j +
            (matMul n
                (gje_cumulative_product n
                  (fun k a b => N_hat k a b + DeltaN k a b)
                  start (start + (n - 1))) R_hat i j -
              matMul n
                (gje_cumulative_product n N_hat start (start + (n - 1)))
                R_hat i j)) *
            x_hat j =
        y i +
          (matMulVec n
              (gje_cumulative_product n
                (fun k a b => N_hat k a b + DeltaN k a b)
                start (start + (n - 1))) y i -
            matMulVec n
              (gje_cumulative_product n N_hat start (start + (n - 1))) y i))
    (hRinvDom : ∀ i j : Fin n,
      |gje_cumulative_product n (fun s a b => |N_hat s a b|)
        start (start + (n - 1)) i j| ≤ |R_inv i j|)
    (hApos : 0 < opNorm2 A) (hxpos : 0 < vecNorm2 x_hat)
    (cy : ℝ) (hcy : 0 ≤ cy)
    (hyx : vecNorm2 y ≤ cy * vecNorm2 x_hat)
    (hChol : matMul n (fun i j => R_hat j i) R_hat = A) :
    vecNorm2 (fun i : Fin n => b i - ∑ j : Fin n, A i j * x_hat j) /
        (opNorm2 A * vecNorm2 x_hat) ≤
      gamma fp n * n +
        (3 * (n : ℝ) * fp.u + gje_c3_quadratic_remainder fp n) *
          (((n : ℝ) * Real.sqrt n * opNorm2 A * opNorm2 R_inv) +
            ((n : ℝ) * opNorm2 R_hat * opNorm2 R_inv * cy)) / opNorm2 A := by
  have heqA : opNorm2 R_hat ^ 2 = opNorm2 A := by
    rw [← ch14ext_opNorm2_transpose_mul_self_eq n R_hat, hChol]
  have hRes :=
    ch14ext_gje_spd_residual_relative_norm2_derived
      n fp A R_hat R_inv b y x_hat N_hat DeltaN start
      hSPD hLU hn hnpos hn3 hidx hDelta hy hBackwardEq hRinvDom
      hApos hxpos cy hcy hyx
  rw [heqA] at hRes
  refine le_trans hRes (le_of_eq ?_)
  field_simp

-- ═══════════════════════════════════════════════════════════════════════════
-- Residual note (honest SUBSTANTIVE_PARTIAL scope)
-- ═══════════════════════════════════════════════════════════════════════════

/-
Summary of what is closed and what remains for Corollary 14.6 (p. 277).

CLOSED / DERIVED here (all unconditional except the noted structural inputs):
* `ch14ext_cor146_positivePivot_cholesky_backward_error` keeps `L_hat`,
  `U_hat`, and `R_hat` distinct and proves the source scaling step
  `A + DeltaA = R_hat^T R_hat`, positivity of the diagonal scale, symmetry of
  `DeltaA`, and the inherited componentwise LU backward bound.
* `ch14ext_opNorm2_transpose_mul_self_eq`: the spectral Cholesky identity
  `‖R̂ᵀR̂‖₂ = ‖R̂‖₂²`, previously flagged open at `HighamChapter10.lean:970`,
  obtained from mathlib's C*-identity `Matrix.l2_opNorm_conjTranspose_mul_self`.
* `ch14ext_cor146_kappa2_sq_eq_kappa2_gram` and its square-root form prove,
  under a two-sided inverse certificate, the exact identity
  `kappa₂(R_hat)^2 = kappa₂(R_hat^T R_hat)` using the repository Gram inverse.
* `ch14ext_cor146_abs_inverseProduct_eq_of_diagonalScaling` derives the inverse
  scaling formula by uniqueness and proves the exact cancellation
  `|U_hat⁻¹||U_hat| = |R_hat⁻¹||R_hat|`.  Its positive-pivot specialization
  keeps the symmetry-exploited factor relation explicit.
* `ch14ext_cor146_kappa2_factor_le_sqrt_perturbationEnvelope` uses the proved
  all-index Weyl inequality to give a finite rational envelope for
  `kappa₂(R_hat)` under the explicit relative smallness guard.  It makes no
  asymptotic claim.
* `ch14ext_cor146_residual_positivePivot_exactGram_of_theorem14_5` and
  `ch14ext_cor146_forward_relative_positivePivot_exactGram_of_theorem14_5`
  wire the cancellation and Gram identity into (14.31)/(14.32), replacing the
  old `kappa₂(U_hat) <= kappaRoot` premise by actual inverse certificates and
  the exact `sqrt(kappa₂(A+DeltaA))` factor.  The forward theorem retains the
  explicit `‖x_hat‖₂/‖x‖₂` ratio.
* The three SPD/Cholesky norm-aggregation constants `alpha, beta, eta` are
  DERIVED from genuine operator-2 certificates via the Lemma-6.6 chain
  (`ch14ext_spd_firstStage_agg_le`, `_secondStageX_`, `_secondStageY_`),
  supporting the retained legacy accumulation route.

REMAINING (why this is SUBSTANTIVE_PARTIAL, not FULL_CLOSURE):
* (R1) The final direct wrappers inherit the parent Theorem-14.5 componentwise
  endpoints as `hRes` / `hFwd`.  These are prior theorem conclusions, not the
  Corollary 14.6 targets, but they are not yet wired to one actual GJE execution
  in this module.
* (R2) The source LU norm budget
  `‖|L_hat||U_hat|‖₂ <= n(1-n gamma_n)⁻¹‖A‖₂` remains the explicit `hAbsLU`
  premise.  The condition-number/Gram bridge is no longer open.
* (R3) Positive pivots and the symmetric-GE relation
  `U_hat_ij = U_hat_ii L_hat_ji`, together with actual inverse certificates
  for `U_hat` and `R_hat`, are explicit source/structural premises.  Deriving
  them from the repository's concrete symmetric GJE trace remains algorithmic
  work outside this module.
* (R4) Replacing `(1-n gamma_n)⁻¹` by `1+O(u)` and
  `kappa₂(A+DeltaA)^(1/2)` by `kappa₂(A)^(1/2)+O(u)` requires a genuine family
  indexed by a vanishing roundoff parameter.  The fixed `FPModel` data here do
  not provide that family; the exact Weyl envelope above is the proved finite
  substitute.
* (R5) The retained accumulation theorems specialize
  `LUBackwardError A (R_hat^T) R_hat`; because that predicate has unit-lower
  diagonal data, it also forces `R_hat` to have unit diagonal.  They are legacy
  partial results, not the final source-facing SPD factor model.
-/
