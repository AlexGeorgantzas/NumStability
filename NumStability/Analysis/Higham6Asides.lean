/-
Higham, *Accuracy and Stability of Numerical Algorithms*, 2nd ed.,
Chapter 6 (Norms), §6.1-6.2: unnumbered body-prose asides.

This file closes four body-prose asides as named theorems, importing and
reusing the existing norm layer (`NumStability.Analysis.Norms`,
`MatrixAlgebra`) plus Mathlib's `l2` operator-norm and unitary-group API.
It edits no existing file.

  (i)   Condition-number lower bounds (p. 108-109):
        `κ(X) = ‖X‖·‖X⁻¹‖ ≥ 1` for any submultiplicative matrix norm, and
        `κ_F(X) ≥ √n` for the Frobenius norm.
  (ii)  Two-sided unitary invariance (p. 108-109): `‖UAV‖₂ = ‖A‖₂` and
        `‖UAV‖_F = ‖A‖_F` for unitary `U`, `V`.
  (iii) The max-norm `‖A‖_M := maxᵢⱼ|aᵢⱼ|` is NOT consistent: the best bound
        is `‖AB‖_M ≤ n‖A‖_M‖B‖_M` with equality at `A = B = J` (all ones).
  (iv)  Block antidiagonal `p`-norm identity `‖[[0,A],[Aᴴ,0]]‖_p =
        max(‖A‖_p,‖A‖_q)` (p. 113), for `p = 2` where it reduces to `‖A‖₂`.

All statements/labels are the unnumbered asides of §6.2; see the printed
displays on pp. 108-109 and p. 113.
-/
import Mathlib.Analysis.CStarAlgebra.Matrix
import Mathlib.Analysis.Calculus.FDeriv.Norm
import Mathlib.Analysis.InnerProductSpace.Calculus
import Mathlib.Analysis.SpecialFunctions.Sqrt
import NumStability.Analysis.Norms

namespace NumStability

open scoped BigOperators
open scoped Matrix
open scoped Matrix.Norms.L2Operator
open scoped RealInnerProductSpace

/-! ### Source correction: differentiability of the Euclidean norm

Higham, Chapter 6, p. 105, says that the `2`-norm is differentiable for all
vectors and gives its gradient as `x / ‖x‖₂`.  The displayed formula itself is
undefined at `x = 0`, and the norm is not differentiable there.  The first
theorem below is a compiled counterexample to the literal universal claim; the
second is the corrected nonzero statement over finite-dimensional complex
Euclidean space, viewed as a real normed space.
-/

/-- **Counterexample to the literal Chapter 6 prose claim.**  The Euclidean
norm on the one-dimensional complex space is not real-differentiable at zero. -/
theorem higham6_euclideanNorm_not_differentiableAt_zero :
    ¬ DifferentiableAt ℝ
      (fun x : EuclideanSpace ℂ (Fin 1) => ‖x‖) 0 :=
  not_differentiableAt_norm_zero _

/-- **Corrected Chapter 6 norm derivative.**  At every nonzero complex vector,
the real Fréchet derivative of `x ↦ ‖x‖₂` is the functional
`h ↦ Re ⟪x,h⟫ / ‖x‖₂`, equivalently the gradient is `x / ‖x‖₂`. -/
theorem higham6_euclideanNorm_hasFDerivAt_of_ne_zero {n : ℕ}
    (x : EuclideanSpace ℂ (Fin n)) (hx : x ≠ 0) :
    HasFDerivAt (fun y : EuclideanSpace ℂ (Fin n) => ‖y‖)
      ((1 / ‖x‖) • innerSL ℝ x) x := by
  have hsq :
      HasFDerivAt (fun y : EuclideanSpace ℂ (Fin n) => ‖y‖ ^ 2)
        (2 • innerSL ℝ x) x :=
    (hasStrictFDerivAt_norm_sq x).hasFDerivAt
  have hxnorm : ‖x‖ ≠ 0 := norm_ne_zero_iff.mpr hx
  have hsqrt := hsq.sqrt (by positivity : ‖x‖ ^ 2 ≠ 0)
  convert hsqrt using 1
  · funext y
    rw [Real.sqrt_sq (norm_nonneg y)]
  · rw [Real.sqrt_sq (norm_nonneg x)]
    ext h
    simp only [ContinuousLinearMap.coe_smul', Pi.smul_apply, smul_eq_mul,
      innerSL_apply_apply]
    field_simp [hxnorm]
    ring

/-! ### Equality cases in Hölder's inequality (6.1)

For `p,q > 1`, the book gives two sufficient equality conditions: the vectors
of powers of the magnitudes are linearly dependent, and all scalar products
`conj (x i) * y i` lie on the same complex ray.  The power-profile hypothesis
below is the standard explicit parametrization
`‖yᵢ‖ = t ‖xᵢ‖^(p-1)`.  Since `(p-1)q=p`, it implies
`‖yᵢ‖^q = t^q ‖xᵢ‖^p`, exactly the stated linear dependence.  The common-ray
hypothesis uses a unit complex direction `z`, including zero coordinates
without a special case.
-/

/-- A common unit complex ray turns the triangle inequality for the Hölder
pairing into equality. -/
lemma higham6_holder_commonRay_norm_eq {n : ℕ} (x y : CVec n) (z : ℂ)
    (hz : ‖z‖ = 1)
    (hphase : ∀ i, star (x i) * y i =
      ((‖x i‖ * ‖y i‖ : ℝ) : ℂ) * z) :
    ‖∑ i : Fin n, star (x i) * y i‖ =
      ∑ i : Fin n, ‖x i‖ * ‖y i‖ := by
  have hsum :
      (∑ i : Fin n, star (x i) * y i) =
        ((∑ i : Fin n, ‖x i‖ * ‖y i‖ : ℝ) : ℂ) * z := by
    simp_rw [hphase]
    rw [← Finset.sum_mul]
    push_cast
    rfl
  rw [hsum, norm_mul, hz, mul_one, Complex.norm_real]
  exact Real.norm_of_nonneg (Finset.sum_nonneg fun i _ =>
    mul_nonneg (norm_nonneg _) (norm_nonneg _))

/-- The magnitude power profile from the equality paragraph after (6.1)
makes the scalar Hölder inequality an equality. -/
lemma higham6_holder_scalar_equality_of_powerProfile {n : ℕ} {p q : ℝ}
    (hpq : p.HolderConjugate q) (x y : CVec n) (t : ℝ) (ht : 0 ≤ t)
    (hmag : ∀ i, ‖y i‖ = t * ‖x i‖ ^ (p - 1)) :
    (∑ i : Fin n, ‖x i‖ * ‖y i‖) =
      complexVecLpNorm (ENNReal.ofReal p) x *
        complexVecLpNorm (ENNReal.ofReal q) y := by
  have hp : 0 < p := hpq.pos
  have hq : 0 < q := hpq.symm.pos
  have hp1 : 0 < p - 1 := hpq.sub_one_pos
  have hexp : (p - 1) * q = p := hpq.sub_one_mul_conj
  let S : ℝ := ∑ i : Fin n, ‖x i‖ ^ p
  have hS : 0 ≤ S := Finset.sum_nonneg fun i _ =>
    Real.rpow_nonneg (norm_nonneg _) _
  have hxterm : ∀ i : Fin n,
      ‖x i‖ * ‖x i‖ ^ (p - 1) = ‖x i‖ ^ p := by
    intro i
    rcases eq_or_lt_of_le (norm_nonneg (x i)) with hzero | hpos
    · rw [← hzero]
      simp [hp.ne', hp1.ne']
    · calc
        ‖x i‖ * ‖x i‖ ^ (p - 1) =
            ‖x i‖ ^ 1 * ‖x i‖ ^ (p - 1) := by rw [Real.rpow_one]
        _ = ‖x i‖ ^ (1 + (p - 1)) :=
          (Real.rpow_add hpos 1 (p - 1)).symm
        _ = ‖x i‖ ^ p := by ring_nf
  have hlhs : (∑ i : Fin n, ‖x i‖ * ‖y i‖) = t * S := by
    calc
      (∑ i : Fin n, ‖x i‖ * ‖y i‖) =
          ∑ i : Fin n, t * ‖x i‖ ^ p := by
        apply Finset.sum_congr rfl
        intro i _hi
        rw [hmag, ← hxterm]
        ring
      _ = t * S := by rw [Finset.mul_sum]
  have hyterm : ∀ i : Fin n,
      ‖y i‖ ^ q = t ^ q * ‖x i‖ ^ p := by
    intro i
    rw [hmag, Real.mul_rpow ht (Real.rpow_nonneg (norm_nonneg _) _)]
    rw [← Real.rpow_mul (norm_nonneg _) (p - 1) q, hexp]
  have hysum : (∑ i : Fin n, ‖y i‖ ^ q) = t ^ q * S := by
    simp_rw [hyterm]
    rw [Finset.mul_sum]
  rw [complexVecLpNorm_ofReal_eq_sum_rpow hp,
    complexVecLpNorm_ofReal_eq_sum_rpow hq, hlhs, hysum]
  rw [show (∑ i : Fin n, ‖x i‖ ^ p) = S by rfl]
  by_cases hSzero : S = 0
  · simp [hSzero, hp.ne', hq.ne']
  have hSpos : 0 < S := lt_of_le_of_ne hS (Ne.symm hSzero)
  rw [Real.mul_rpow (Real.rpow_nonneg ht q) hS]
  have htq : (t ^ q) ^ q⁻¹ = t := by
    rw [← Real.rpow_mul ht]
    rw [mul_inv_cancel₀ hq.ne', Real.rpow_one]
  rw [htq]
  symm
  calc
    S ^ p⁻¹ * (t * S ^ q⁻¹) =
        t * (S ^ p⁻¹ * S ^ q⁻¹) := by ring
    _ = t * S ^ (p⁻¹ + q⁻¹) := by
      rw [Real.rpow_add hSpos]
    _ = t * S := by
      rw [hpq.inv_add_inv_eq_one, Real.rpow_one]

/-- **Hölder equality under Higham's two sufficient conditions.**  This is the
finite complex equality statement immediately following equation (6.1). -/
theorem higham6_holder_equality_of_powerProfile_sameRay {n : ℕ} {p q : ℝ}
    (hpq : p.HolderConjugate q) (x y : CVec n) (t : ℝ) (ht : 0 ≤ t)
    (hmag : ∀ i, ‖y i‖ = t * ‖x i‖ ^ (p - 1))
    (z : ℂ) (hz : ‖z‖ = 1)
    (hphase : ∀ i, star (x i) * y i =
      ((‖x i‖ * ‖y i‖ : ℝ) : ℂ) * z) :
    ‖∑ i : Fin n, star (x i) * y i‖ =
      complexVecLpNorm (ENNReal.ofReal p) x *
        complexVecLpNorm (ENNReal.ofReal q) y := by
  rw [higham6_holder_commonRay_norm_eq x y z hz hphase]
  exact higham6_holder_scalar_equality_of_powerProfile hpq x y t ht hmag

/-- **Endpoint equality is possible.**  The single-coordinate unit vector
attains equality for both conjugate endpoint pairs `(1,∞)` and `(∞,1)`, as
asserted after (6.1). -/
theorem higham6_holder_endpoint_equality_standardBasis :
    let e : CVec 1 := standardBasisCVec (n := 1) (0 : Fin 1)
    (‖∑ i : Fin 1, star (e i) * e i‖ =
        complexVecLpNorm 1 e * complexVecLpNorm (⊤ : ENNReal) e) ∧
      (‖∑ i : Fin 1, star (e i) * e i‖ =
        complexVecLpNorm (⊤ : ENNReal) e * complexVecLpNorm 1 e) := by
  dsimp
  rw [complexVecLpNorm_one_eq_complexVecOneNorm,
    complexVecLpNorm_infty_eq_complexVecInfNorm,
    complexVecOneNorm_standardBasisCVec,
    complexVecInfNorm_standardBasisCVec]
  simp [standardBasisCVec]

/-! ### Bridge lemmas between `complexMatrixMul` / `complexMatrixOp2` and
    Mathlib's `Matrix` multiplication and `l2` operator norm. -/

/-- The source-facing `complexMatrixMul` is Mathlib matrix multiplication under
    the `complexCMatrixAsMatrix` view. -/
theorem ch6aside_complexMatrixMul_eq_matMul {m n p : ℕ}
    (A : CMatrix m n) (B : CMatrix n p) :
    complexMatrixMul A B =
      (complexCMatrixAsMatrix A * complexCMatrixAsMatrix B :
        Matrix (Fin m) (Fin p) ℂ) := by
  funext i j
  simp [complexMatrixMul, Matrix.mul_apply, complexCMatrixAsMatrix]

/-- The source-facing operator `2`-norm equals Mathlib's `l2` operator norm of
    the matrix view. -/
theorem ch6aside_op2_eq_l2 {m n : ℕ} (A : CMatrix m n) :
    complexMatrixOp2 A = ‖complexCMatrixAsMatrix A‖ := by
  rw [complexMatrixOp2]
  exact (Matrix.l2_opNorm_def (complexCMatrixAsMatrix A)).symm

/-! ### (i) Condition-number lower bounds -/

/-- **Abstract condition-number bound** `κ(X) ≥ 1` (Higham §6.2, p. 108-109:
    "The condition number satisfies `κ(X) ≥ 1`").  For any matrix norm `N` that
    is submultiplicative (`consistent`), nonnegative, and definite, and any `X`
    with a right inverse `Xinv` (`X·Xinv = I`), we have `1 ≤ N(X)·N(Xinv)`.
    The constant `1` is *derived* from `N(I) ≤ N(X)N(Xinv)` and `N(I) ≥ 1`. -/
theorem ch6aside_conditionNumber_ge_one {n : ℕ} (hn : 0 < n)
    (N : CMatrix n n → ℝ)
    (hsub : ∀ A B : CMatrix n n, N (complexMatrixMul A B) ≤ N A * N B)
    (hnn : ∀ A : CMatrix n n, 0 ≤ N A)
    (hdef : ∀ A : CMatrix n n, N A = 0 → A = 0)
    {X Xinv : CMatrix n n}
    (hinv : complexMatrixMul X Xinv = (1 : Matrix (Fin n) (Fin n) ℂ)) :
    1 ≤ N X * N Xinv := by
  -- The identity matrix is nonzero (n ≥ 1), so `N 1 > 0` by definiteness.
  have hone_ne : (1 : Matrix (Fin n) (Fin n) ℂ) ≠ 0 := by
    intro h
    have := congrFun (congrFun h ⟨0, hn⟩) ⟨0, hn⟩
    simp [Matrix.one_apply_eq] at this
  have hNone_pos : 0 < N (1 : Matrix (Fin n) (Fin n) ℂ) := by
    rcases lt_or_eq_of_le (hnn (1 : Matrix (Fin n) (Fin n) ℂ)) with h | h
    · exact h
    · exact absurd (hdef _ h.symm) hone_ne
  -- `1·1 = 1`, so submultiplicativity gives `N 1 ≤ N 1 · N 1`, hence `1 ≤ N 1`.
  have h11 : complexMatrixMul (1 : Matrix (Fin n) (Fin n) ℂ)
      (1 : Matrix (Fin n) (Fin n) ℂ) = (1 : Matrix (Fin n) (Fin n) ℂ) := by
    rw [ch6aside_complexMatrixMul_eq_matMul]
    simp
  have hNone_ge : (1 : ℝ) ≤ N (1 : Matrix (Fin n) (Fin n) ℂ) := by
    have hle := hsub (1 : Matrix (Fin n) (Fin n) ℂ) (1 : Matrix (Fin n) (Fin n) ℂ)
    rw [h11] at hle
    nlinarith [hNone_pos]
  -- `N 1 = N (X·Xinv) ≤ N X · N Xinv`.
  have hchain : N (1 : Matrix (Fin n) (Fin n) ℂ) ≤ N X * N Xinv := by
    have := hsub X Xinv
    rwa [hinv] at this
  linarith [hNone_ge, hchain]

/-- **Operator `2`-norm is submultiplicative** (consistent).  This is the
    Chapter 6 "all subordinate norms are consistent" aside, for `‖·‖₂`. -/
theorem ch6aside_op2_mul_le {m n p : ℕ}
    (A : CMatrix m n) (B : CMatrix n p) :
    complexMatrixOp2 (complexMatrixMul A B) ≤
      complexMatrixOp2 A * complexMatrixOp2 B := by
  rw [ch6aside_op2_eq_l2, ch6aside_op2_eq_l2, ch6aside_op2_eq_l2,
    ch6aside_complexMatrixMul_eq_matMul]
  exact Matrix.l2_opNorm_mul (complexCMatrixAsMatrix A) (complexCMatrixAsMatrix B)

/-- **Condition-number bound for the operator `2`-norm**: `κ₂(X) ≥ 1`. -/
theorem ch6aside_op2_conditionNumber_ge_one {n : ℕ} (hn : 0 < n)
    {X Xinv : CMatrix n n}
    (hinv : complexMatrixMul X Xinv = (1 : Matrix (Fin n) (Fin n) ℂ)) :
    1 ≤ complexMatrixOp2 X * complexMatrixOp2 Xinv :=
  ch6aside_conditionNumber_ge_one hn complexMatrixOp2
    ch6aside_op2_mul_le complexMatrixOp2_nonneg
    (fun _A hA => complexMatrix_eq_zero_of_op2_eq_zero hA) hinv

/-- The Frobenius norm of the `n × n` identity is `√n` (`‖I‖_F = √n`, used in
    Higham's `κ_F(X) ≥ √n`, p. 109). -/
theorem ch6aside_frobenius_one {n : ℕ} :
    complexMatrixFrobenius (1 : Matrix (Fin n) (Fin n) ℂ) = Real.sqrt n := by
  have hsq : complexMatrixFrobeniusSq (1 : Matrix (Fin n) (Fin n) ℂ) = (n : ℝ) := by
    unfold complexMatrixFrobeniusSq
    have hrow : ∀ i : Fin n,
        (∑ j : Fin n, ‖(1 : Matrix (Fin n) (Fin n) ℂ) i j‖ ^ 2) = 1 := by
      intro i
      rw [Finset.sum_eq_single i]
      · simp [Matrix.one_apply_eq]
      · intro j _ hji
        rw [Matrix.one_apply_ne (fun h => hji h.symm)]
        simp
      · intro h; exact absurd (Finset.mem_univ i) h
    rw [Finset.sum_congr rfl (fun i _ => hrow i)]
    simp
  rw [complexMatrixFrobenius, hsq]

/-- **Frobenius norm is submultiplicative** (consistent): `‖AB‖_F ≤ ‖A‖_F‖B‖_F`.
    Assembled from `‖AB‖_F ≤ ‖A‖₂‖B‖_F` and `‖A‖₂ ≤ ‖A‖_F`. -/
theorem ch6aside_frobenius_mul_le {m n p : ℕ} (hn : 0 < n)
    (A : CMatrix m n) (B : CMatrix n p) :
    complexMatrixFrobenius (complexMatrixMul A B) ≤
      complexMatrixFrobenius A * complexMatrixFrobenius B := by
  calc complexMatrixFrobenius (complexMatrixMul A B)
      ≤ complexMatrixOp2 A * complexMatrixFrobenius B :=
        complexMatrixFrobenius_mul_le_op2_mul A B
    _ ≤ complexMatrixFrobenius A * complexMatrixFrobenius B := by
        exact mul_le_mul_of_nonneg_right
          (complexMatrixOp2_le_complexMatrixFrobenius hn A)
          (complexMatrixFrobenius_nonneg B)

/-- **Condition-number bound for the Frobenius norm**: `κ_F(X) ≥ √n`
    (Higham §6.2, p. 109).  Derived from `√n = ‖I‖_F = ‖X·X⁻¹‖_F ≤ ‖X‖_F‖X⁻¹‖_F`. -/
theorem ch6aside_conditionF_ge_sqrt_n {n : ℕ} (hn : 0 < n)
    {X Xinv : CMatrix n n}
    (hinv : complexMatrixMul X Xinv = (1 : Matrix (Fin n) (Fin n) ℂ)) :
    Real.sqrt n ≤ complexMatrixFrobenius X * complexMatrixFrobenius Xinv := by
  have hstep := ch6aside_frobenius_mul_le hn X Xinv
  rw [hinv, ch6aside_frobenius_one] at hstep
  exact hstep

/-! ### (ii) Two-sided unitary invariance of the `2`- and Frobenius norms -/

/-- The `l2` operator norm of the `m × m` identity is `1` (`m ≥ 1`). -/
private theorem ch6aside_l2_one {m : ℕ} [Nonempty (Fin m)] :
    ‖(1 : Matrix (Fin m) (Fin m) ℂ)‖ = 1 := by
  rw [show (1 : Matrix (Fin m) (Fin m) ℂ)
        = Matrix.diagonal (fun _ => (1 : ℂ)) from Matrix.diagonal_one.symm,
      Matrix.l2_opNorm_diagonal, Pi.norm_def, Finset.sup_const Finset.univ_nonempty]
  simp

/-- The `l2` operator norm of a unitary matrix is `1` (`m ≥ 1`). -/
private theorem ch6aside_l2_unitary {m : ℕ} [Nonempty (Fin m)]
    {U : Matrix (Fin m) (Fin m) ℂ} (hU : U ∈ Matrix.unitaryGroup (Fin m) ℂ) :
    ‖U‖ = 1 := by
  have h1 : Uᴴ * U = 1 := by
    have := (Matrix.mem_unitaryGroup_iff' (A := U)).mp hU
    rwa [Matrix.star_eq_conjTranspose] at this
  have hsq : ‖Uᴴ * U‖ = ‖U‖ * ‖U‖ := Matrix.l2_opNorm_conjTranspose_mul_self U
  rw [h1, ch6aside_l2_one] at hsq
  nlinarith [norm_nonneg U]

/-- **Two-sided unitary invariance of the operator `2`-norm** (Higham §6.2,
    p. 108-109: "`‖UAV‖ = ‖A‖`" for the unitarily invariant `2`-norm).
    For unitary `U ∈ ℂ^{m×m}`, `V ∈ ℂ^{n×n}`, `‖UAV‖₂ = ‖A‖₂`. -/
theorem ch6aside_op2_two_sided_unitary_invariant {m n : ℕ}
    [Nonempty (Fin m)] [Nonempty (Fin n)]
    {U : Matrix (Fin m) (Fin m) ℂ} {V : Matrix (Fin n) (Fin n) ℂ}
    (hU : U ∈ Matrix.unitaryGroup (Fin m) ℂ) (hV : V ∈ Matrix.unitaryGroup (Fin n) ℂ)
    (A : CMatrix m n) :
    complexMatrixOp2
        ((U * complexCMatrixAsMatrix A * V : Matrix (Fin m) (Fin n) ℂ)) =
      complexMatrixOp2 A := by
  set Am : Matrix (Fin m) (Fin n) ℂ := complexCMatrixAsMatrix A with hAm
  have hUn : ‖U‖ = 1 := ch6aside_l2_unitary hU
  have hVn : ‖V‖ = 1 := ch6aside_l2_unitary hV
  have hUHU : Uᴴ * U = 1 := by
    have := (Matrix.mem_unitaryGroup_iff' (A := U)).mp hU
    rwa [Matrix.star_eq_conjTranspose] at this
  have hVVH : V * Vᴴ = 1 := by
    have := (Matrix.mem_unitaryGroup_iff (A := V)).mp hV
    rwa [Matrix.star_eq_conjTranspose] at this
  rw [ch6aside_op2_eq_l2, ch6aside_op2_eq_l2]
  have hcast : (complexCMatrixAsMatrix
      ((U * Am * V : Matrix (Fin m) (Fin n) ℂ))) = U * Am * V := rfl
  rw [hcast, ← hAm]
  -- upper bound: ‖U Am V‖ ≤ ‖Am‖
  have hle : ‖U * Am * V‖ ≤ ‖Am‖ := by
    calc ‖U * Am * V‖ ≤ ‖U * Am‖ * ‖V‖ := Matrix.l2_opNorm_mul _ _
      _ ≤ (‖U‖ * ‖Am‖) * ‖V‖ := by gcongr; exact Matrix.l2_opNorm_mul _ _
      _ = ‖Am‖ := by rw [hUn, hVn]; ring
  -- lower bound: ‖Am‖ = ‖Uᴴ (U Am V) Vᴴ‖ ≤ ‖U Am V‖
  have hUHn : ‖Uᴴ‖ = 1 := by rw [Matrix.l2_opNorm_conjTranspose]; exact hUn
  have hVHn : ‖Vᴴ‖ = 1 := by rw [Matrix.l2_opNorm_conjTranspose]; exact hVn
  have hge : ‖Am‖ ≤ ‖U * Am * V‖ := by
    have hAmrw : Am = Uᴴ * (U * Am * V) * Vᴴ := by
      have : Uᴴ * (U * Am * V) * Vᴴ = (Uᴴ * U) * Am * (V * Vᴴ) := by
        simp only [Matrix.mul_assoc]
      rw [this, hUHU, hVVH, Matrix.one_mul, Matrix.mul_one]
    calc ‖Am‖ = ‖Uᴴ * (U * Am * V) * Vᴴ‖ := by rw [← hAmrw]
      _ ≤ ‖Uᴴ * (U * Am * V)‖ * ‖Vᴴ‖ := Matrix.l2_opNorm_mul _ _
      _ ≤ (‖Uᴴ‖ * ‖U * Am * V‖) * ‖Vᴴ‖ := by gcongr; exact Matrix.l2_opNorm_mul _ _
      _ = ‖U * Am * V‖ := by rw [hUHn, hVHn]; ring
  exact le_antisymm hle hge

/-- The squared Frobenius norm equals `tr(AᴴA)` (embedded in `ℂ`); the identity
    `‖A‖_F² = tr(AᴴA)` that drives Frobenius unitary invariance. -/
theorem ch6aside_frobeniusSq_eq_trace {m n : ℕ} (A : CMatrix m n) :
    (complexMatrixFrobeniusSq A : ℂ) =
      ((complexCMatrixAsMatrix A)ᴴ * complexCMatrixAsMatrix A).trace := by
  unfold complexMatrixFrobeniusSq Matrix.trace
  push_cast
  rw [Finset.sum_comm]
  refine Finset.sum_congr rfl fun i _ => ?_
  rw [Matrix.diag_apply, Matrix.mul_apply]
  refine Finset.sum_congr rfl fun k _ => ?_
  rw [Matrix.conjTranspose_apply]
  simp only [complexCMatrixAsMatrix, Complex.star_def]
  rw [← Complex.normSq_eq_conj_mul_self, Complex.normSq_eq_norm_sq]
  push_cast
  ring

/-- **Two-sided unitary invariance of the Frobenius norm** (Higham §6.2,
    p. 108-109).  For unitary `U ∈ ℂ^{m×m}`, `V ∈ ℂ^{n×n}`, `‖UAV‖_F = ‖A‖_F`. -/
theorem ch6aside_frobenius_two_sided_unitary_invariant {m n : ℕ}
    {U : Matrix (Fin m) (Fin m) ℂ} {V : Matrix (Fin n) (Fin n) ℂ}
    (hU : U ∈ Matrix.unitaryGroup (Fin m) ℂ) (hV : V ∈ Matrix.unitaryGroup (Fin n) ℂ)
    (A : CMatrix m n) :
    complexMatrixFrobenius
        ((U * complexCMatrixAsMatrix A * V : Matrix (Fin m) (Fin n) ℂ)) =
      complexMatrixFrobenius A := by
  set Am : Matrix (Fin m) (Fin n) ℂ := complexCMatrixAsMatrix A with hAm
  have hUHU : Uᴴ * U = 1 := by
    have := (Matrix.mem_unitaryGroup_iff' (A := U)).mp hU
    rwa [Matrix.star_eq_conjTranspose] at this
  have hVVH : V * Vᴴ = 1 := by
    have := (Matrix.mem_unitaryGroup_iff (A := V)).mp hV
    rwa [Matrix.star_eq_conjTranspose] at this
  -- FrobSq (U Am V) = FrobSq Am via trace cyclicity.
  have hsq : complexMatrixFrobeniusSq
      ((U * Am * V : Matrix (Fin m) (Fin n) ℂ)) = complexMatrixFrobeniusSq A := by
    have hcast : complexCMatrixAsMatrix
        ((U * Am * V : Matrix (Fin m) (Fin n) ℂ)) = U * Am * V := rfl
    have key :
        (((U * Am * V)ᴴ) * (U * Am * V)).trace = (Amᴴ * Am).trace := by
      have hexp : ((U * Am * V)ᴴ) * (U * Am * V) = Vᴴ * (Amᴴ * Am) * V := by
        rw [Matrix.conjTranspose_mul, Matrix.conjTranspose_mul]
        simp only [Matrix.mul_assoc]
        rw [← Matrix.mul_assoc Uᴴ U (Am * V), hUHU, Matrix.one_mul]
      rw [hexp, Matrix.trace_mul_cycle Vᴴ (Amᴴ * Am) V, ← Matrix.mul_assoc,
        hVVH, Matrix.one_mul]
    have hc : (complexMatrixFrobeniusSq ((U * Am * V : Matrix (Fin m) (Fin n) ℂ)) : ℂ)
        = (complexMatrixFrobeniusSq A : ℂ) := by
      rw [ch6aside_frobeniusSq_eq_trace, ch6aside_frobeniusSq_eq_trace,
        hcast, ← hAm, key]
    exact_mod_cast hc
  rw [complexMatrixFrobenius, complexMatrixFrobenius, hsq]

/-! ### (iii) The max-norm is not consistent -/

/-- **Best consistency bound for the max-norm** (Higham §6.2, p. 108: "The best
    bound that holds for all `A ∈ Cᵐˣⁿ` and `B ∈ Cⁿˣᵖ` is
    `‖AB‖_M ≤ n‖A‖_M‖B‖_M`").  Here `‖A‖_M := maxᵢⱼ|aᵢⱼ|`. -/
theorem ch6aside_maxNorm_mul_le {m n p : ℕ}
    (A : CMatrix m n) (B : CMatrix n p) :
    complexMatrixEntrywiseMaxNorm (complexMatrixMul A B) ≤
      (n : ℝ) * complexMatrixEntrywiseMaxNorm A *
        complexMatrixEntrywiseMaxNorm B := by
  apply complexMatrixEntrywiseMaxNorm_le_of_coord_le
  · exact mul_nonneg
      (mul_nonneg (Nat.cast_nonneg n) (complexMatrixEntrywiseMaxNorm_nonneg A))
      (complexMatrixEntrywiseMaxNorm_nonneg B)
  · intro i j
    have hbound : ‖complexMatrixMul A B i j‖ ≤
        ∑ k : Fin n, ‖A i k‖ * ‖B k j‖ := by
      unfold complexMatrixMul
      calc ‖∑ k : Fin n, A i k * B k j‖
          ≤ ∑ k : Fin n, ‖A i k * B k j‖ := norm_sum_le _ _
        _ = ∑ k : Fin n, ‖A i k‖ * ‖B k j‖ := by simp
    have hterm : ∀ k : Fin n, ‖A i k‖ * ‖B k j‖ ≤
        complexMatrixEntrywiseMaxNorm A * complexMatrixEntrywiseMaxNorm B := by
      intro k
      exact mul_le_mul (complexMatrixEntrywiseMaxNorm_coord_le A i k)
        (complexMatrixEntrywiseMaxNorm_coord_le B k j) (norm_nonneg _)
        (complexMatrixEntrywiseMaxNorm_nonneg A)
    calc ‖complexMatrixMul A B i j‖
        ≤ ∑ k : Fin n, ‖A i k‖ * ‖B k j‖ := hbound
      _ ≤ ∑ _k : Fin n, complexMatrixEntrywiseMaxNorm A *
            complexMatrixEntrywiseMaxNorm B :=
          Finset.sum_le_sum (fun k _ => hterm k)
      _ = (n : ℝ) * complexMatrixEntrywiseMaxNorm A *
            complexMatrixEntrywiseMaxNorm B := by
          rw [Finset.sum_const, Finset.card_univ, Fintype.card_fin]
          rw [nsmul_eq_mul]; ring

/-- Max-norm of the all-ones `n × n` matrix `J` is `1` (`n ≥ 1`). -/
theorem ch6aside_maxNorm_allOnes {n : ℕ} (hn : 0 < n) :
    complexMatrixEntrywiseMaxNorm (fun _ _ : Fin n => (1 : ℂ)) = 1 := by
  refine le_antisymm ?_ ?_
  · exact complexMatrixEntrywiseMaxNorm_le_of_coord_le _ (by norm_num)
      (fun i j => by simp)
  · have := complexMatrixEntrywiseMaxNorm_coord_le
      (fun _ _ : Fin n => (1 : ℂ)) ⟨0, hn⟩ ⟨0, hn⟩
    simpa using this

/-- The all-ones product: `J·J = n·J` (each entry equals `n`). -/
theorem ch6aside_maxNorm_allOnes_mul {n : ℕ} :
    complexMatrixMul (fun _ _ : Fin n => (1 : ℂ)) (fun _ _ : Fin n => (1 : ℂ)) =
      (fun _ _ : Fin n => (n : ℂ)) := by
  funext i j
  simp [complexMatrixMul, Finset.card_univ]

/-- **Equality in the max-norm bound at `A = B = J` (all ones)** (Higham §6.2,
    p. 108: "with equality when `aᵢⱼ ≡ 1` and `bᵢⱼ ≡ 1`"):
    `‖J·J‖_M = n·‖J‖_M·‖J‖_M`. -/
theorem ch6aside_maxNorm_equality_allOnes {n : ℕ} (hn : 0 < n) :
    complexMatrixEntrywiseMaxNorm
        (complexMatrixMul (fun _ _ : Fin n => (1 : ℂ))
          (fun _ _ : Fin n => (1 : ℂ))) =
      (n : ℝ) * complexMatrixEntrywiseMaxNorm (fun _ _ : Fin n => (1 : ℂ)) *
        complexMatrixEntrywiseMaxNorm (fun _ _ : Fin n => (1 : ℂ)) := by
  rw [ch6aside_maxNorm_allOnes_mul, ch6aside_maxNorm_allOnes hn]
  have hconst : complexMatrixEntrywiseMaxNorm (fun _ _ : Fin n => (n : ℂ)) =
      (n : ℝ) := by
    refine le_antisymm ?_ ?_
    · exact complexMatrixEntrywiseMaxNorm_le_of_coord_le _ (Nat.cast_nonneg n)
        (fun i j => by simp)
    · have := complexMatrixEntrywiseMaxNorm_coord_le
        (fun _ _ : Fin n => (n : ℂ)) ⟨0, hn⟩ ⟨0, hn⟩
      simpa using this
  rw [hconst]; ring

/-- **The max-norm is not consistent** (Higham §6.2, p. 108: "An example of a
    norm that is not consistent is the max norm").  For `n ≥ 2` there exist
    matrices (`A = B = J`, all ones) with `‖A‖_M·‖B‖_M < ‖AB‖_M`, so
    `‖AB‖_M ≤ ‖A‖_M‖B‖_M` fails. -/
theorem ch6aside_maxNorm_not_consistent {n : ℕ} (hn : 2 ≤ n) :
    ∃ A B : CMatrix n n,
      complexMatrixEntrywiseMaxNorm A * complexMatrixEntrywiseMaxNorm B <
        complexMatrixEntrywiseMaxNorm (complexMatrixMul A B) := by
  have h0 : 0 < n := by omega
  refine ⟨(fun _ _ => 1), (fun _ _ => 1), ?_⟩
  rw [ch6aside_maxNorm_equality_allOnes h0, ch6aside_maxNorm_allOnes h0]
  have hn2 : (2 : ℝ) ≤ (n : ℝ) := by exact_mod_cast hn
  nlinarith

/-! ### (iv) Block antidiagonal `p`-norm identity (`p = 2`)

Higham §6.2, p. 113 (unnumbered display after (6.21)):
`‖[[0, A], [Aᴴ, 0]]‖_p = max(‖A‖_p, ‖A‖_q)`, `1/p + 1/q = 1`.  For `p = 2`
we have `q = 2`, so the right side is `max(‖A‖₂, ‖A‖₂) = ‖A‖₂`.

We assemble the reduction using the repo/Mathlib `l2` operator-norm API.  Write
`H := [[0, A], [Aᴴ, 0]]` (Mathlib `fromBlocks`, indexed by `Fin m ⊕ Fin n`).
The two structural facts below are proved outright; the norm identity is then
derived from the C*-identity `‖H‖² = ‖HᴴH‖`, the Hermitian symmetry `Hᴴ = H`,
the block-diagonal square `H² = diag(AAᴴ, AᴴA)`, and `‖AAᴴ‖ = ‖AᴴA‖ = ‖A‖²`,
reducing everything to the single standard fact that the `l2` operator norm of a
block-diagonal matrix is the max of the block norms (`hblock`), which is absent
from Mathlib. -/

/-- **The block antidiagonal matrix `[[0,A],[Aᴴ,0]]` is Hermitian.** -/
theorem ch6aside_blockAntidiag_hermitian {m n : ℕ} (A : CMatrix m n) :
    (Matrix.fromBlocks (0 : Matrix (Fin m) (Fin m) ℂ) (complexCMatrixAsMatrix A)
        ((complexCMatrixAsMatrix A)ᴴ) (0 : Matrix (Fin n) (Fin n) ℂ))ᴴ =
      Matrix.fromBlocks (0 : Matrix (Fin m) (Fin m) ℂ) (complexCMatrixAsMatrix A)
        ((complexCMatrixAsMatrix A)ᴴ) (0 : Matrix (Fin n) (Fin n) ℂ) := by
  rw [Matrix.fromBlocks_conjTranspose]
  simp

/-- **Square of the block antidiagonal matrix is block diagonal:**
    `[[0,A],[Aᴴ,0]]² = diag(A Aᴴ, Aᴴ A)`. -/
theorem ch6aside_blockAntidiag_sq {m n : ℕ} (A : CMatrix m n) :
    (Matrix.fromBlocks (0 : Matrix (Fin m) (Fin m) ℂ) (complexCMatrixAsMatrix A)
        ((complexCMatrixAsMatrix A)ᴴ) (0 : Matrix (Fin n) (Fin n) ℂ)) *
      (Matrix.fromBlocks (0 : Matrix (Fin m) (Fin m) ℂ) (complexCMatrixAsMatrix A)
        ((complexCMatrixAsMatrix A)ᴴ) (0 : Matrix (Fin n) (Fin n) ℂ)) =
      Matrix.fromBlocks
        (complexCMatrixAsMatrix A * (complexCMatrixAsMatrix A)ᴴ)
        (0 : Matrix (Fin m) (Fin n) ℂ) (0 : Matrix (Fin n) (Fin m) ℂ)
        ((complexCMatrixAsMatrix A)ᴴ * complexCMatrixAsMatrix A) := by
  rw [Matrix.fromBlocks_multiply]
  simp

/-- **Block antidiagonal `2`-norm identity** (Higham §6.2, p. 113, at `p = 2`):
    `‖[[0,A],[Aᴴ,0]]‖₂ = ‖A‖₂`.  The reduction is proved in full; the sole
    residual is `hblock`, the standard "`l2` norm of a block-diagonal matrix is
    the max of the block norms", which Mathlib does not provide. -/
theorem ch6aside_blockAntidiag_op2_eq {m n : ℕ} (A : CMatrix m n)
    (hblock :
      ‖Matrix.fromBlocks (complexCMatrixAsMatrix A * (complexCMatrixAsMatrix A)ᴴ)
          (0 : Matrix (Fin m) (Fin n) ℂ) (0 : Matrix (Fin n) (Fin m) ℂ)
          ((complexCMatrixAsMatrix A)ᴴ * complexCMatrixAsMatrix A)‖ =
        max ‖complexCMatrixAsMatrix A * (complexCMatrixAsMatrix A)ᴴ‖
          ‖(complexCMatrixAsMatrix A)ᴴ * complexCMatrixAsMatrix A‖) :
    ‖Matrix.fromBlocks (0 : Matrix (Fin m) (Fin m) ℂ) (complexCMatrixAsMatrix A)
        ((complexCMatrixAsMatrix A)ᴴ) (0 : Matrix (Fin n) (Fin n) ℂ)‖ =
      complexMatrixOp2 A := by
  set Am := complexCMatrixAsMatrix A with hAm
  set H := Matrix.fromBlocks (0 : Matrix (Fin m) (Fin m) ℂ) Am Amᴴ
    (0 : Matrix (Fin n) (Fin n) ℂ) with hH
  rw [ch6aside_op2_eq_l2, ← hAm]
  -- `‖A Aᴴ‖ = ‖Aᴴ A‖ = ‖A‖²`.
  have hAHA : ‖Amᴴ * Am‖ = ‖Am‖ * ‖Am‖ :=
    Matrix.l2_opNorm_conjTranspose_mul_self Am
  have hAAH : ‖Am * Amᴴ‖ = ‖Am‖ * ‖Am‖ := by
    have h := Matrix.l2_opNorm_conjTranspose_mul_self (Amᴴ)
    rwa [Matrix.conjTranspose_conjTranspose, Matrix.l2_opNorm_conjTranspose] at h
  -- `‖H‖² = ‖HᴴH‖ = ‖H²‖ = ‖diag(AAᴴ, AᴴA)‖ = max(‖A‖²,‖A‖²) = ‖A‖²`.
  have hHH : ‖H‖ * ‖H‖ = ‖Am‖ * ‖Am‖ := by
    have hcstar : ‖Hᴴ * H‖ = ‖H‖ * ‖H‖ := Matrix.l2_opNorm_conjTranspose_mul_self H
    have hherm : Hᴴ = H := by
      rw [hH, Matrix.fromBlocks_conjTranspose]; simp
    have hsq : H * H = Matrix.fromBlocks (Am * Amᴴ)
        (0 : Matrix (Fin m) (Fin n) ℂ) (0 : Matrix (Fin n) (Fin m) ℂ) (Amᴴ * Am) := by
      rw [hH, Matrix.fromBlocks_multiply]; simp
    rw [hherm, hsq, hblock, hAAH, hAHA, max_self] at hcstar
    exact hcstar.symm
  have hsq2 : ‖H‖ ^ 2 = ‖Am‖ ^ 2 := by rw [sq, sq]; exact hHH
  exact (sq_eq_sq₀ (norm_nonneg H) (norm_nonneg Am)).mp hsq2

end NumStability
