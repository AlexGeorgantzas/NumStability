import Mathlib.Analysis.SpecialFunctions.Sqrt
import NumStability.Source.Higham.Chapter06.Asides.UnitaryInvariance

/-!
# Higham Chapter 6: condition-number lower bounds

Source correspondence for the p. 108--109 submultiplicativity and
condition-number bounds, including the Frobenius lower bound by the square root
of the dimension.
-/

namespace NumStability

open scoped BigOperators
open scoped Matrix
open scoped Matrix.Norms.L2Operator

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

end NumStability
