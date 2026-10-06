import NumStability.Algorithms.MatrixInversion

namespace NumStability

open scoped BigOperators

/-!
# Chapter 14, Problem 14.13: the one-dimensional boundary

The Appendix A AM-GM list contains two copies of `sigma_1^2 / 2`, so that
argument starts at dimension two.  The printed inequality itself also covers
dimension one.  This file proves that scalar case and combines it with the
existing `k + 2` result.

The source expression divides by `sqrt n`, so the source-facing theorem keeps
the mathematically intended hypothesis `0 < n`.  We deliberately do not turn
Lean's totalized division at `n = 0` into a claimed zero-dimensional extension.
-/

/-- In dimension one, a nonsingular matrix has 2-norm condition number one. -/
theorem ch14ext_problem14_13_kappa2_eq_one_fin_one
    (A Ainv : Fin 1 -> Fin 1 -> Real)
    (hRight : IsRightInverse 1 A Ainv) :
    kappa2 A Ainv = 1 := by
  let sigma : Real :=
    complexMatrixSingularValue (realRectToCMatrix A) (0 : Fin 1)
  have hdet_pos :=
    higham14_problem14_13_abs_det_pos_of_isRightInverse A Ainv hRight
  have hsigma_pos : 0 < sigma := by
    rw [higham14_problem14_13_abs_det_eq_prod_complex_singularValue A] at hdet_pos
    simpa [sigma] using hdet_pos
  have hkappa :=
    higham14_problem14_13_kappa2_eq_top_div_last_singularValue_of_rightInverse
      A Ainv hRight
  have htop : (⟨0, Nat.succ_pos 0⟩ : Fin 1) = Fin.last 0 := by
    rfl
  rw [htop] at hkappa
  simpa [sigma, div_self hsigma_pos.ne'] using hkappa

/-- For a one-by-one matrix, the Frobenius norm is its absolute determinant. -/
theorem ch14ext_problem14_13_frobNorm_eq_abs_det_fin_one
    (A : Fin 1 -> Fin 1 -> Real) :
    frobNorm A = |Matrix.det (A : Matrix (Fin 1) (Fin 1) Real)| := by
  let sigma : Real :=
    complexMatrixSingularValue (realRectToCMatrix A) (0 : Fin 1)
  have hfrob_sq : frobNorm A ^ 2 = sigma ^ 2 := by
    simpa [sigma] using
      higham14_problem14_13_frobNorm_sq_eq_sum_complex_singularValue_sq A
  have hdet :
      |Matrix.det (A : Matrix (Fin 1) (Fin 1) Real)| = sigma := by
    simpa [sigma] using
      higham14_problem14_13_abs_det_eq_prod_complex_singularValue A
  rw [hdet]
  exact
    (sq_eq_sq₀ (frobNorm_nonneg A)
      (complexMatrixSingularValue_nonneg (realRectToCMatrix A) (0 : Fin 1))).mp
      hfrob_sq

/-- Equation (14.37) in the missing scalar case. -/
theorem ch14ext_problem14_13_gej_bound_fin_one
    (A Ainv : Fin 1 -> Fin 1 -> Real)
    (hRight : IsRightInverse 1 A Ainv) :
    kappa2 A Ainv <
      (2 / |Matrix.det (A : Matrix (Fin 1) (Fin 1) Real)|) *
        (frobNorm A / Real.sqrt (1 : Real)) ^ (1 : Nat) := by
  have hkappa := ch14ext_problem14_13_kappa2_eq_one_fin_one A Ainv hRight
  have hfrob := ch14ext_problem14_13_frobNorm_eq_abs_det_fin_one A
  have hdet_ne : |Matrix.det (A : Matrix (Fin 1) (Fin 1) Real)| ≠ 0 :=
    ne_of_gt
      (higham14_problem14_13_abs_det_pos_of_isRightInverse A Ainv hRight)
  calc
    kappa2 A Ainv = 1 := hkappa
    _ < 2 := by norm_num
    _ =
        (2 / |Matrix.det (A : Matrix (Fin 1) (Fin 1) Real)|) *
          (frobNorm A / Real.sqrt (1 : Real)) ^ (1 : Nat) := by
            rw [hfrob, Real.sqrt_one, div_one, pow_one]
            field_simp [hdet_ne]

/-- Higham, Chapter 14, Problem 14.13(a), equation (14.37), for every
    positive matrix dimension. -/
theorem ch14ext_problem14_13_gej_bound_of_isRightInverse_pos
    {n : Nat} (hn : 0 < n) (A Ainv : Fin n -> Fin n -> Real)
    (hRight : IsRightInverse n A Ainv) :
    kappa2 A Ainv <
      (2 / |Matrix.det (A : Matrix (Fin n) (Fin n) Real)|) *
        (frobNorm A / Real.sqrt (n : Real)) ^ n := by
  cases n with
  | zero => simp at hn
  | succ m =>
      cases m with
      | zero =>
          simpa using ch14ext_problem14_13_gej_bound_fin_one A Ainv hRight
      | succ k =>
          simpa [Nat.succ_eq_add_one, Nat.add_assoc] using
            higham14_problem14_13_gej_bound_of_isRightInverse
              (k := k) A Ainv hRight

/-- Higham, Chapter 14, Problem 14.13(b), now including dimension one. -/
theorem ch14ext_problem14_13_kappa2_lt_two_mul_hadamardConditionNumber_of_unit_rows_pos
    {n : Nat} (hn : 0 < n) (A Ainv : Fin n -> Fin n -> Real)
    (hRight : IsRightInverse n A Ainv)
    (hrow : forall i : Fin n, higham14_rowNorm2 A i = 1) :
    kappa2 A Ainv < 2 * higham14_hadamardConditionNumber A := by
  refine
    higham14_problem14_13_kappa_lt_two_mul_hadamardConditionNumber_of_unit_rows
      A hrow ?_
  have hgej :=
    ch14ext_problem14_13_gej_bound_of_isRightInverse_pos hn A Ainv hRight
  have hfrob :=
    higham14_problem14_13_frobNorm_eq_sqrt_card_of_rowNorm2_eq_one A hrow
  have hsqrt_pos : 0 < Real.sqrt (n : Real) :=
    Real.sqrt_pos.mpr (Nat.cast_pos.mpr hn)
  rw [hfrob] at hgej
  rw [div_self hsqrt_pos.ne', one_pow, mul_one] at hgej
  exact hgej

end NumStability
