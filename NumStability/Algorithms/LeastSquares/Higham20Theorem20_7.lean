import NumStability.Algorithms.QR.Higham19Thm6CoxHigham
import NumStability.Algorithms.QR.Higham19Thm6CoxHighamConcrete
import NumStability.Algorithms.QR.HouseholderApply
import NumStability.Algorithms.QR.HouseholderQRSupport
import NumStability.Algorithms.LeastSquares.LSQRSolve

namespace NumStability

open scoped BigOperators

namespace Theorem20_7

/-!
# Higham, Chapter 20, Theorem 20.7: computed-reflector dependency

The row-wise weighted least-squares theorem uses the Cox--Higham analysis of
column-pivoted Householder QR.  The first missing implementation bridge is
Lemma 2.2 of Cox--Higham: the error in one *computed* reflector application
must be bounded entrywise relative to the exact reflector constructed from the
same active column.

The library's implementation applies an analysis-only normalized vector
`w = sqrt beta * v` with coefficient one.  The Cox--Higham row scale, however,
is the raw Householder vector `v`.  The lemmas below keep these two objects
separate and prove the scaling identity needed to pass between them.  In
particular, no exact-normalization property is assumed of the computed vector.
-/

/-- Taking absolute values in the Cox--Higham multiplier eliminates the
possibility of cancellation while preserving both Euclidean-norm premises.

This is the form needed for the componentwise application error, whose
rank-one term contains `sum |v_j| |b_j|`. -/
theorem raw_abs_multiplier_le_sqrt_two {n : ℕ}
    (v b : Fin n → ℝ) (sigma beta : ℝ)
    (hsigma : 0 < |sigma|)
    (hvnorm : Real.sqrt 2 * |sigma| ≤ vecNorm2 v)
    (hb : vecNorm2 b ≤ |sigma|)
    (hbeta : beta * vecNorm2 v ^ 2 = 2) :
    beta * (∑ j : Fin n, |v j| * |b j|) ≤ Real.sqrt 2 := by
  have hsqrt2_pos : (0 : ℝ) < Real.sqrt 2 := Real.sqrt_pos.mpr (by norm_num)
  have hvpos : 0 < vecNorm2 v := by
    have hpos : 0 < Real.sqrt 2 * |sigma| :=
      mul_pos hsqrt2_pos hsigma
    linarith
  have hbeta_pos : 0 < beta := by
    have hsq_pos : 0 < vecNorm2 v ^ 2 := sq_pos_of_pos hvpos
    nlinarith [hbeta]
  have hcore :=
    Wave19.householder_multiplier_le_sqrt_two
      (fun j : Fin n => |v j|) (fun j : Fin n => |b j|)
      sigma beta hsigma
      (by simpa [vecNorm2_abs] using hvnorm)
      (by simpa [vecNorm2_abs] using hb)
      (by simpa [vecNorm2_abs] using hbeta)
  have hsum_nonneg : 0 ≤ ∑ j : Fin n, |v j| * |b j| :=
    Finset.sum_nonneg (fun j _ => mul_nonneg (abs_nonneg _) (abs_nonneg _))
  rw [abs_of_nonneg (mul_nonneg (le_of_lt hbeta_pos) hsum_nonneg)] at hcore
  exact hcore

/-- Exact conversion of one normalized outer-product row to raw Householder
scaling.  It is the dimensional identity behind Cox--Higham Lemma 2.2. -/
theorem normalized_outer_row_eq_raw {n : ℕ}
    (v b : Fin n → ℝ) (beta : ℝ) (hbeta : 0 ≤ beta) (i : Fin n) :
    |householderNormalizedVector n v beta i| *
        (∑ j : Fin n,
          |householderNormalizedVector n v beta j| * |b j|) =
      beta * |v i| * (∑ j : Fin n, |v j| * |b j|) := by
  have hsqrt_nonneg : 0 ≤ Real.sqrt beta := Real.sqrt_nonneg beta
  have hsum :
      (∑ j : Fin n,
          |householderNormalizedVector n v beta j| * |b j|) =
        Real.sqrt beta * (∑ j : Fin n, |v j| * |b j|) := by
    rw [Finset.mul_sum]
    apply Finset.sum_congr rfl
    intro j _
    simp only [householderNormalizedVector, abs_mul,
      abs_of_nonneg hsqrt_nonneg]
    ring
  rw [hsum]
  simp only [householderNormalizedVector, abs_mul,
    abs_of_nonneg hsqrt_nonneg]
  have hsqrt_sq : Real.sqrt beta * Real.sqrt beta = beta :=
    Real.mul_self_sqrt hbeta
  calc
    Real.sqrt beta * |v i| *
          (Real.sqrt beta * (∑ j : Fin n, |v j| * |b j|)) =
        (Real.sqrt beta * Real.sqrt beta) * |v i| *
          (∑ j : Fin n, |v j| * |b j|) := by ring
    _ = beta * |v i| * (∑ j : Fin n, |v j| * |b j|) := by
      rw [hsqrt_sq]

/-- Entrywise form of the primitive perturbation matrix extracted from one
rounded normalized Householder application. -/
theorem normalized_delta_entry_abs_le
    (fp : FPModel) (a n : ℕ)
    (v vhat : Fin n → ℝ) (eps : ℝ)
    (eta : Fin n → ℝ) (deltaW : ℝ) (deltaMul deltaSub : Fin n → ℝ)
    (hvec : HouseholderVectorError n v vhat eps)
    (heps_nonneg : 0 ≤ eps)
    (heps_bound : eps ≤ gamma fp a)
    (heta : ∀ j : Fin n, |eta j| ≤ gamma fp n)
    (hdeltaW : |deltaW| ≤ fp.u)
    (hdeltaMul : ∀ i : Fin n, |deltaMul i| ≤ fp.u)
    (hdeltaSub : ∀ i : Fin n, |deltaSub i| ≤ fp.u)
    (hvalid : gammaValid fp (2 * a + n + 3))
    (i j : Fin n) :
    |householderApplyDeltaMatrix n (householder n v 1) vhat 1
        eta deltaW deltaMul deltaSub i j| ≤
      idMatrix n i j * fp.u +
        gamma fp (2 * a + n + 3) * |v i| * |v j| := by
  obtain ⟨theta, htheta, hentry⟩ :=
    householderApplyDeltaMatrix_normalized_entry_gamma
      fp a n v vhat eps eta deltaW deltaMul deltaSub hvec heps_nonneg
      heps_bound heta hdeltaW hdeltaMul hdeltaSub hvalid i j
  rw [hentry]
  by_cases hij : i = j
  · subst j
    simp only [idMatrix, if_pos, one_mul]
    have houter :
        |v i * v i * theta| ≤
          gamma fp (2 * a + n + 3) * |v i| * |v i| := by
      rw [abs_mul, abs_mul]
      calc
        |v i| * |v i| * |theta| ≤
            |v i| * |v i| * gamma fp (2 * a + n + 3) :=
          mul_le_mul_of_nonneg_left htheta
            (mul_nonneg (abs_nonneg _) (abs_nonneg _))
        _ = gamma fp (2 * a + n + 3) * |v i| * |v i| := by ring
    calc
      |deltaSub i - v i * v i * theta| ≤
          |deltaSub i| + |v i * v i * theta| := abs_sub _ _
      _ ≤ fp.u + gamma fp (2 * a + n + 3) * |v i| * |v i| := by
        exact add_le_add (hdeltaSub i) houter
  · simp only [idMatrix, if_neg hij, zero_mul, zero_add, zero_sub, abs_neg]
    rw [abs_mul, abs_mul]
    calc
      |v i| * |v j| * |theta| ≤
          |v i| * |v j| * gamma fp (2 * a + n + 3) :=
        mul_le_mul_of_nonneg_left htheta
          (mul_nonneg (abs_nonneg _) (abs_nonneg _))
      _ = gamma fp (2 * a + n + 3) * |v i| * |v j| := by ring

/-- The primitive perturbation matrix acts on a column with Higham's
componentwise diagonal-plus-rank-one bound. -/
theorem normalized_delta_matMulVec_entry_abs_le
    (fp : FPModel) (a n : ℕ)
    (v vhat : Fin n → ℝ) (eps : ℝ) (b : Fin n → ℝ)
    (eta : Fin n → ℝ) (deltaW : ℝ) (deltaMul deltaSub : Fin n → ℝ)
    (hvec : HouseholderVectorError n v vhat eps)
    (heps_nonneg : 0 ≤ eps)
    (heps_bound : eps ≤ gamma fp a)
    (heta : ∀ j : Fin n, |eta j| ≤ gamma fp n)
    (hdeltaW : |deltaW| ≤ fp.u)
    (hdeltaMul : ∀ i : Fin n, |deltaMul i| ≤ fp.u)
    (hdeltaSub : ∀ i : Fin n, |deltaSub i| ≤ fp.u)
    (hvalid : gammaValid fp (2 * a + n + 3))
    (i : Fin n) :
    |matMulVec n
        (householderApplyDeltaMatrix n (householder n v 1) vhat 1
          eta deltaW deltaMul deltaSub) b i| ≤
      fp.u * |b i| +
        gamma fp (2 * a + n + 3) * |v i| *
          (∑ j : Fin n, |v j| * |b j|) := by
  let D := householderApplyDeltaMatrix n (householder n v 1) vhat 1
    eta deltaW deltaMul deltaSub
  calc
    |matMulVec n D b i| ≤ ∑ j : Fin n, |D i j| * |b j| :=
      abs_matMulVec_le n D b i
    _ ≤ ∑ j : Fin n,
        (idMatrix n i j * fp.u +
          gamma fp (2 * a + n + 3) * |v i| * |v j|) * |b j| := by
      apply Finset.sum_le_sum
      intro j _
      exact mul_le_mul_of_nonneg_right
        (normalized_delta_entry_abs_le fp a n v vhat eps eta deltaW
          deltaMul deltaSub hvec heps_nonneg heps_bound heta hdeltaW
          hdeltaMul hdeltaSub hvalid i j)
        (abs_nonneg (b j))
    _ = fp.u * |b i| +
        gamma fp (2 * a + n + 3) * |v i| *
          (∑ j : Fin n, |v j| * |b j|) := by
      simp only [add_mul, Finset.sum_add_distrib]
      have hdiag :
          (∑ j : Fin n, idMatrix n i j * fp.u * |b j|) =
            fp.u * |b i| := by
        simp [idMatrix, Finset.sum_ite_eq, Finset.mem_univ]
      rw [hdiag]
      congr 1
      rw [Finset.mul_sum]
      apply Finset.sum_congr rfl
      intro j _
      ring

/-- One concrete rounded normalized-reflector application differs from the
matching exact reflector by the componentwise bound used in Cox--Higham
Lemma 2.2.  All error variables are obtained from `FPModel`; none are public
hypotheses. -/
theorem fl_householderApply_normalized_entrywise_error
    (fp : FPModel) (a n : ℕ)
    (v vhat : Fin n → ℝ) (eps : ℝ) (b : Fin n → ℝ)
    (hvec : HouseholderVectorError n v vhat eps)
    (heps_nonneg : 0 ≤ eps)
    (heps_bound : eps ≤ gamma fp a)
    (hvalid : gammaValid fp (2 * a + n + 3))
    (i : Fin n) :
    |fl_householderApply fp n vhat 1 b i -
        matMulVec n (householder n v 1) b i| ≤
      fp.u * |b i| +
        gamma fp (2 * a + n + 3) * |v i| *
          (∑ j : Fin n, |v j| * |b j|) := by
  have hn : gammaValid fp n := gammaValid_mono fp (by omega) hvalid
  obtain ⟨eta, deltaW, deltaMul, deltaSub, heta, hdeltaW,
      hdeltaMul, hdeltaSub, hmatrix⟩ :=
    fl_householderApply_matrix_unroll fp n vhat 1 b hn
  let P := householder n v 1
  let D := householderApplyDeltaMatrix n P vhat 1
    eta deltaW deltaMul deltaSub
  have herr :
      fl_householderApply fp n vhat 1 b i - matMulVec n P b i =
        matMulVec n D b i := by
    rw [show fl_householderApply fp n vhat 1 b i =
        matMulVec n
          (householderApplyRoundedMatrix n vhat 1 eta deltaW deltaMul deltaSub)
          b i from congrFun hmatrix i]
    unfold matMulVec D householderApplyDeltaMatrix
    rw [← Finset.sum_sub_distrib]
    apply Finset.sum_congr rfl
    intro j _
    ring
  rw [herr]
  exact normalized_delta_matMulVec_entry_abs_le fp a n v vhat eps b
    eta deltaW deltaMul deltaSub hvec heps_nonneg heps_bound heta hdeltaW
    hdeltaMul hdeltaSub hvalid i

/-- Raw-vector form of the computed-reflector application bound.

The exact reflector is `I - beta*v*vᵀ`, while the implementation is analyzed
through its normalized vector.  The sign-choice and pivot-maximality premises
are exactly Cox--Higham equations (2.5) and (2.4). -/
theorem fl_householderApply_raw_entrywise_error
    (fp : FPModel) (a n : ℕ)
    (vraw vhat b : Fin n → ℝ) (beta sigma eps : ℝ)
    (hbeta_nonneg : 0 ≤ beta)
    (hvec : HouseholderVectorError n
      (householderNormalizedVector n vraw beta) vhat eps)
    (heps_nonneg : 0 ≤ eps)
    (heps_bound : eps ≤ gamma fp a)
    (hsigma : 0 < |sigma|)
    (hvnorm : Real.sqrt 2 * |sigma| ≤ vecNorm2 vraw)
    (hb : vecNorm2 b ≤ |sigma|)
    (hbeta : beta * vecNorm2 vraw ^ 2 = 2)
    (hvalid : gammaValid fp (2 * a + n + 3))
    (i : Fin n) :
    |fl_householderApply fp n vhat 1 b i -
        matMulVec n (householder n vraw beta) b i| ≤
      fp.u * |b i| +
        gamma fp (2 * a + n + 3) * Real.sqrt 2 * |vraw i| := by
  let vnorm := householderNormalizedVector n vraw beta
  have happ :=
    fl_householderApply_normalized_entrywise_error fp a n vnorm vhat eps b
      hvec heps_nonneg heps_bound hvalid i
  rw [householder_normalizedVector_eq n vraw beta hbeta_nonneg] at happ
  have hscale := normalized_outer_row_eq_raw vraw b beta hbeta_nonneg i
  have hmult :=
    raw_abs_multiplier_le_sqrt_two vraw b sigma beta hsigma hvnorm hb hbeta
  have hrow :
      beta * |vraw i| * (∑ j : Fin n, |vraw j| * |b j|) ≤
        Real.sqrt 2 * |vraw i| := by
    calc
      beta * |vraw i| * (∑ j : Fin n, |vraw j| * |b j|) =
          |vraw i| *
            (beta * (∑ j : Fin n, |vraw j| * |b j|)) := by ring
      _ ≤ |vraw i| * Real.sqrt 2 :=
        mul_le_mul_of_nonneg_left hmult (abs_nonneg (vraw i))
      _ = Real.sqrt 2 * |vraw i| := by ring
  have hgamma_nonneg : 0 ≤ gamma fp (2 * a + n + 3) :=
    gamma_nonneg fp hvalid
  calc
    |fl_householderApply fp n vhat 1 b i -
        matMulVec n (householder n vraw beta) b i| ≤
      fp.u * |b i| +
        gamma fp (2 * a + n + 3) * |vnorm i| *
          (∑ j : Fin n, |vnorm j| * |b j|) := happ
    _ = fp.u * |b i| + gamma fp (2 * a + n + 3) *
        (beta * |vraw i| *
          (∑ j : Fin n, |vraw j| * |b j|)) := by
      rw [← hscale]
      ring
    _ ≤ fp.u * |b i| + gamma fp (2 * a + n + 3) *
        (Real.sqrt 2 * |vraw i|) := by
      exact add_le_add le_rfl
        (mul_le_mul_of_nonneg_left hrow hgamma_nonneg)
    _ = fp.u * |b i| +
        gamma fp (2 * a + n + 3) * Real.sqrt 2 * |vraw i| := by ring

/-- The exact Householder scale is the Euclidean norm of its input, up to the
chosen sign. -/
theorem abs_householderScale_eq_vecNorm2 {n : ℕ} (hn : 0 < n)
    (x : Fin n → ℝ) :
    |householderScale hn x| = vecNorm2 x := by
  unfold householderScale vecNorm2 vecNorm2Sq
  rw [abs_mul, abs_householderSign, one_mul,
    abs_of_nonneg (Real.sqrt_nonneg _)]
  congr 2
  funext i
  ring

/-- The sign convention makes the scale and the leading entry have the same
sign. -/
theorem householderScale_mul_first_nonneg {n : ℕ} (hn : 0 < n)
    (x : Fin n → ℝ) :
    0 ≤ householderScale hn x * x ⟨0, hn⟩ := by
  by_cases hneg : x ⟨0, hn⟩ < 0
  · have hscale :
        householderScale hn x =
          -Real.sqrt (∑ i : Fin n, x i * x i) := by
      simp [householderScale, householderSign, hneg]
    rw [hscale]
    exact mul_nonneg_of_nonpos_of_nonpos
      (neg_nonpos.mpr (Real.sqrt_nonneg _)) (le_of_lt hneg)
  · have hscale :
        householderScale hn x =
          Real.sqrt (∑ i : Fin n, x i * x i) := by
      simp [householderScale, householderSign, hneg]
    rw [hscale]
    exact mul_nonneg (Real.sqrt_nonneg _) (le_of_not_gt hneg)

/-- Cox--Higham equation (2.5) follows from the exact Householder sign choice;
it is not an additional reflector assumption. -/
theorem householderVector_sign_norm_bound {n : ℕ} (hn : 0 < n)
    (x : Fin n → ℝ) :
    Real.sqrt 2 * vecNorm2 x ≤ vecNorm2 (householderVector hn x) := by
  have hsq :
      2 * vecNorm2 x ^ 2 ≤ vecNorm2 (householderVector hn x) ^ 2 := by
    calc
      2 * vecNorm2 x ^ 2 = 2 * (∑ i : Fin n, x i * x i) := by
        rw [vecNorm2_sq]
        simp [vecNorm2Sq, pow_two]
      _ = 2 * (householderScale hn x * householderScale hn x) := by
        rw [householderScale_mul_self hn x]
      _ = 2 * householderScale hn x * householderScale hn x := by ring
      _ ≤ 2 * householderScale hn x *
          (x ⟨0, hn⟩ + householderScale hn x) := by
        nlinarith [householderScale_mul_first_nonneg hn x]
      _ = 2 * householderScale hn x *
          householderVector hn x ⟨0, hn⟩ := by
        rw [householderVector_zero]
      _ = ∑ i : Fin n,
          householderVector hn x i * householderVector hn x i := by
        rw [householderVector_norm_sq_eq_two_scale_mul hn x]
      _ = vecNorm2 (householderVector hn x) ^ 2 := by
        rw [vecNorm2_sq]
        simp [vecNorm2Sq, pow_two]
  apply (sq_le_sq₀
    (mul_nonneg (Real.sqrt_nonneg _) (vecNorm2_nonneg x))
    (vecNorm2_nonneg (householderVector hn x))).mp
  calc
    (Real.sqrt 2 * vecNorm2 x) ^ 2 = 2 * vecNorm2 x ^ 2 := by
      rw [mul_pow, Real.sq_sqrt (by norm_num : (0 : ℝ) ≤ 2)]
    _ ≤ vecNorm2 (householderVector hn x) ^ 2 := hsq

/-- Specialization to the actual Householder construction kernel.  This is
the implementation-backed one-step estimate required before the recursive
column-pivoted QR proof for Theorem 20.7 can be assembled. -/
theorem fl_householderConstructApply_raw_entrywise_error
    (fp : FPModel) {n : ℕ} (hn : 0 < n)
    (x b : Fin n → ℝ) (hx : x ≠ 0)
    (hb : vecNorm2 b ≤ vecNorm2 x)
    (hvalid : gammaValid fp (11 * n + 23))
    (i : Fin n) :
    |fl_householderApply fp n
          (fl_householderNormalizedVector fp hn x) 1 b i -
        matMulVec n
          (householder n (householderVector hn x)
            (householderBetaFromScale hn x)) b i| ≤
      fp.u * |b i| + gamma fp (11 * n + 23) * Real.sqrt 2 *
        |householderVector hn x i| := by
  let a : ℕ := 5 * n + 10
  let beta := householderBetaFromScale hn x
  let vraw := householderVector hn x
  have hvalid_vec : gammaValid fp (8 * n + 16) :=
    gammaValid_mono fp (by omega) hvalid
  have hvec : HouseholderVectorError n
      (householderNormalizedVector n vraw beta)
      (fl_householderNormalizedVector fp hn x) (gamma fp a) := by
    simpa [a, beta, vraw] using
      fl_householderVectorError fp hn x hx hvalid_vec
  have hvalid_a : gammaValid fp a :=
    gammaValid_mono fp (by unfold a; omega) hvalid
  have hbeta_nonneg : 0 ≤ beta := by
    exact le_of_lt (householderBetaFromScale_pos_of_ne_zero hn x hx)
  have hbeta : beta * vecNorm2 vraw ^ 2 = 2 := by
    rw [vecNorm2_sq]
    simpa [beta, vraw, vecNorm2Sq, pow_two] using
      householderBetaFromScale_mul_norm_sq hn x hx
  have hvalid_apply : gammaValid fp (2 * a + n + 3) := by
    have hidx : 2 * a + n + 3 = 11 * n + 23 := by
      unfold a
      omega
    simpa [hidx] using hvalid
  have hsigma : 0 < |householderScale hn x| :=
    abs_pos.mpr (householderScale_ne_zero_of_ne_zero hn x hx)
  have hvnorm :
      Real.sqrt 2 * |householderScale hn x| ≤ vecNorm2 vraw := by
    simpa [vraw, abs_householderScale_eq_vecNorm2 hn x] using
      householderVector_sign_norm_bound hn x
  have hbscale : vecNorm2 b ≤ |householderScale hn x| := by
    simpa [abs_householderScale_eq_vecNorm2 hn x] using hb
  have happ := fl_householderApply_raw_entrywise_error fp a n vraw
    (fl_householderNormalizedVector fp hn x) b beta
    (householderScale hn x) (gamma fp a)
    hbeta_nonneg hvec (gamma_nonneg fp hvalid_a) le_rfl hsigma hvnorm hbscale
    hbeta hvalid_apply i
  have hidx : 2 * a + n + 3 = 11 * n + 23 := by
    unfold a
    omega
  simpa [a, beta, vraw, hidx] using happ

/-- Row-growth collapse of the concrete one-step error.  The folding premise
only chooses the generic `gamma-tilde` constant; the data premises are the
forward row maximum and the raw-vector inequality (2.10). -/
theorem fl_householderConstructApply_rowGrowth_entrywise_error
    (fp : FPModel) {n : ℕ} (hn : 0 < n)
    (x b : Fin n → ℝ) (hx : x ≠ 0)
    (hb_pivot : vecNorm2 b ≤ vecNorm2 x)
    (alpha gammaTilde : ℝ) (i : Fin n)
    (halpha : 0 ≤ alpha)
    (hb_row : |b i| ≤ alpha)
    (hv_row : |householderVector hn x i| ≤ 2 * alpha)
    (hfold : fp.u +
      2 * (Real.sqrt 2 * gamma fp (11 * n + 23)) ≤ gammaTilde)
    (hvalid : gammaValid fp (11 * n + 23)) :
    |fl_householderApply fp n
          (fl_householderNormalizedVector fp hn x) 1 b i -
        matMulVec n
          (householder n (householderVector hn x)
            (householderBetaFromScale hn x)) b i| ≤
      gammaTilde * alpha := by
  have hraw := fl_householderConstructApply_raw_entrywise_error
    fp hn x b hx hb_pivot hvalid i
  apply Wave19.perStep_entrywise_le_gamma_rowGrowth
    (fl_householderApply fp n
      (fl_householderNormalizedVector fp hn x) 1 b i -
      matMulVec n
        (householder n (householderVector hn x)
          (householderBetaFromScale hn x)) b i)
    (b i) (householderVector hn x i) fp.u
    (Real.sqrt 2 * gamma fp (11 * n + 23)) gammaTilde alpha
    halpha fp.u_nonneg
    (mul_nonneg (Real.sqrt_nonneg _)
      (gamma_nonneg fp hvalid))
  · calc
      |fl_householderApply fp n
            (fl_householderNormalizedVector fp hn x) 1 b i -
          matMulVec n
            (householder n (householderVector hn x)
              (householderBetaFromScale hn x)) b i| ≤
          fp.u * |b i| + gamma fp (11 * n + 23) * Real.sqrt 2 *
            |householderVector hn x i| := hraw
      _ = fp.u * |b i| +
          (Real.sqrt 2 * gamma fp (11 * n + 23)) *
            |householderVector hn x i| := by ring
  · exact hb_row
  · exact hv_row
  · exact hfold

/-- Matrix-panel form of the implementation-backed one-step estimate.  The
pivot-maximality premise is stated for the executed active panel columns. -/
theorem fl_householderConstructApplyMatrixRect_raw_entrywise_error
    (fp : FPModel) {n p : ℕ} (hn : 0 < n)
    (x : Fin n → ℝ) (A : Fin n → Fin p → ℝ) (hx : x ≠ 0)
    (hpivot : ∀ j : Fin p, vecNorm2 (fun s => A s j) ≤ vecNorm2 x)
    (hvalid : gammaValid fp (11 * n + 23))
    (i : Fin n) (j : Fin p) :
    |fl_householderApplyMatrixRect fp n p
          (fl_householderNormalizedVector fp hn x) 1 A i j -
        matMulRect n n p
          (householder n (householderVector hn x)
            (householderBetaFromScale hn x)) A i j| ≤
      fp.u * |A i j| + gamma fp (11 * n + 23) * Real.sqrt 2 *
        |householderVector hn x i| := by
  simpa [fl_householderApplyMatrixRect, matMulRect] using
    fl_householderConstructApply_raw_entrywise_error fp hn x
      (fun s => A s j) hx (hpivot j) hvalid i

/-- Matrix-panel row-growth collapse of the concrete computed step. -/
theorem fl_householderConstructApplyMatrixRect_rowGrowth_entrywise_error
    (fp : FPModel) {n p : ℕ} (hn : 0 < n)
    (x : Fin n → ℝ) (A : Fin n → Fin p → ℝ) (hx : x ≠ 0)
    (hpivot : ∀ j : Fin p, vecNorm2 (fun s => A s j) ≤ vecNorm2 x)
    (alpha : Fin n → ℝ) (gammaTilde : ℝ)
    (halpha : ∀ i, 0 ≤ alpha i)
    (hA_row : ∀ i j, |A i j| ≤ alpha i)
    (hv_row : ∀ i, |householderVector hn x i| ≤ 2 * alpha i)
    (hfold : fp.u +
      2 * (Real.sqrt 2 * gamma fp (11 * n + 23)) ≤ gammaTilde)
    (hvalid : gammaValid fp (11 * n + 23))
    (i : Fin n) (j : Fin p) :
    |fl_householderApplyMatrixRect fp n p
          (fl_householderNormalizedVector fp hn x) 1 A i j -
        matMulRect n n p
          (householder n (householderVector hn x)
            (householderBetaFromScale hn x)) A i j| ≤
      gammaTilde * alpha i := by
  simpa [fl_householderApplyMatrixRect, matMulRect] using
    fl_householderConstructApply_rowGrowth_entrywise_error fp hn x
      (fun s => A s j) hx (hpivot j) (alpha i) gammaTilde i
      (halpha i) (hA_row i j) (hv_row i) hfold hvalid

/-- Source-faithful raw-vector transport through one exact reflector.

Unlike the older normalized recursive bridge, the size premise
`|v_i| ≤ 2*alpha_i` is imposed on the raw Householder vector—the object for
which Cox--Higham equation (2.10) is dimensionally valid. -/
theorem raw_householder_transport_entrywise_le {m p : ℕ}
    (v : Fin m → ℝ) (Eta : Fin m → Fin p → ℝ)
    (alpha : Fin m → ℝ) (gammaTilde beta : ℝ)
    (hvpos : 0 < vecNorm2 v)
    (hbeta : beta * vecNorm2 v ^ 2 = 2)
    (halpha : ∀ i, 0 ≤ alpha i)
    (hv_row : ∀ i, |v i| ≤ 2 * alpha i)
    (hratio : ∀ j : Fin p,
      vecNorm2 (fun s => Eta s j) / vecNorm2 v ≤ gammaTilde)
    (i : Fin m) (j : Fin p) :
    |matMulRect m m p (householder m v beta) Eta i j| ≤
      |Eta i j| + 4 * gammaTilde * alpha i := by
  have haction :
      matMulRect m m p (householder m v beta) Eta i j =
        Eta i j - beta * v i * (∑ s : Fin m, v s * Eta s j) := by
    have hcol :
        matMulRect m m p (householder m v beta) Eta i j =
          matMulVec m (householder m v beta) (fun s => Eta s j) i := rfl
    rw [hcol, householder_matMulVec_eq]
  have hvsq_ne : vecNorm2 v ^ 2 ≠ 0 := ne_of_gt (sq_pos_of_pos hvpos)
  have hcoef : beta = 2 / vecNorm2 v ^ 2 :=
    (eq_div_iff hvsq_ne).2 hbeta
  have hrank := Wave19.zk_rankOne_entrywise_le
    v (fun s => Eta s j) (alpha i) i hvpos (halpha i) (hv_row i)
  have hratio_j := hratio j
  have hscale_nonneg : 0 ≤ 4 * alpha i := by
    exact mul_nonneg (by norm_num) (halpha i)
  have hrank_scaled :
      |beta * v i * (∑ s : Fin m, v s * Eta s j)| ≤
        4 * gammaTilde * alpha i := by
    rw [hcoef]
    calc
      |(2 / vecNorm2 v ^ 2) * v i *
          (∑ s : Fin m, v s * Eta s j)| ≤
          4 * alpha i *
            (vecNorm2 (fun s => Eta s j) / vecNorm2 v) := hrank
      _ ≤ 4 * alpha i * gammaTilde :=
        mul_le_mul_of_nonneg_left hratio_j hscale_nonneg
      _ = 4 * gammaTilde * alpha i := by ring
  rw [haction]
  exact le_trans (abs_sub _ _) (add_le_add le_rfl hrank_scaled)

/-- Transport specialization for the exact reflector constructed from the
active pivot column.  Positivity and normalization of the raw reflector are
derived internally. -/
theorem householderConstruct_transport_entrywise_le {m p : ℕ}
    (hm : 0 < m) (x : Fin m → ℝ) (hx : x ≠ 0)
    (Eta : Fin m → Fin p → ℝ)
    (alpha : Fin m → ℝ) (gammaTilde : ℝ)
    (halpha : ∀ i, 0 ≤ alpha i)
    (hv_row : ∀ i, |householderVector hm x i| ≤ 2 * alpha i)
    (hratio : ∀ j : Fin p,
      vecNorm2 (fun s => Eta s j) /
        vecNorm2 (householderVector hm x) ≤ gammaTilde)
    (i : Fin m) (j : Fin p) :
    |matMulRect m m p
        (householder m (householderVector hm x)
          (householderBetaFromScale hm x)) Eta i j| ≤
      |Eta i j| + 4 * gammaTilde * alpha i := by
  have hvpos : 0 < vecNorm2 (householderVector hm x) := by
    have hvne : vecNorm2 (householderVector hm x) ≠ 0 := by
      intro hzero
      have hall := (vecNorm2_eq_zero_iff (householderVector hm x)).mp hzero
      exact (householderVector_zero_ne_zero_of_ne_zero hm x hx)
        (hall ⟨0, hm⟩)
    exact lt_of_le_of_ne (vecNorm2_nonneg _) (Ne.symm hvne)
  have hbeta :
      householderBetaFromScale hm x *
        vecNorm2 (householderVector hm x) ^ 2 = 2 := by
    rw [vecNorm2_sq]
    simpa [vecNorm2Sq, pow_two] using
      householderBetaFromScale_mul_norm_sq hm x hx
  exact raw_householder_transport_entrywise_le
    (householderVector hm x) Eta alpha gammaTilde
    (householderBetaFromScale hm x) hvpos hbeta halpha hv_row hratio i j

/-! ## The source-faithful per-error telescope

The older recursive interface attempted to bound an already accumulated
perturbation by one reflector norm.  That is not the Cox--Higham argument.
For the error `f` made at stage `i`, the paper first expands the *single*
orthogonal image

`P₀ ⋯ Pᵢ₋₁ f = f - Σₖ βₖ vₖ vₖᵀ (Pₖ₊₁ ⋯ Pᵢ₋₁ f)`

and bounds every rank-one term with the ratio `‖f‖₂ / ‖vₖ‖₂`.  The
lemmas below formalize exactly that expansion.  In particular, their ratio
hypothesis is about the current, unaccumulated `f`; no same-gamma bound for a
recursive sum is assumed.
-/

/-- The `k`th rank-one term in the Cox--Higham expansion of
`P₀ ⋯ Pᵢ₋₁ f`. -/
noncomputable def rawHouseholderZTerm {m : ℕ}
    (v : ℕ → Fin m → ℝ) (β : ℕ → ℝ) (f : Fin m → ℝ)
    (i k : ℕ) : Fin m → ℝ :=
  fun l =>
    β k * v k l *
      (∑ s : Fin m, v k s *
        Wave19.applyProd
          (fun t => householder m (v t) (β t)) (k + 1)
          (i - (k + 1)) f s)

/-- Exact Cox--Higham expansion of one transported stage error.

This is the algebra between equations (2.11) and (2.12).  It follows by
telescoping the suffixes `Pₖ ⋯ Pᵢ₋₁ f`; no norm estimate and no
accumulated-error premise is involved. -/
theorem applyProd_rawHouseholder_coordinate_expansion {m : ℕ}
    (v : ℕ → Fin m → ℝ) (β : ℕ → ℝ) (f : Fin m → ℝ)
    (i : ℕ) (l : Fin m) :
    Wave19.applyProd (fun t => householder m (v t) (β t)) 0 i f l =
      f l - ∑ k ∈ Finset.range i, rawHouseholderZTerm v β f i k l := by
  let P : ℕ → Fin m → Fin m → ℝ :=
    fun t => householder m (v t) (β t)
  let g : ℕ → ℝ :=
    fun k => Wave19.applyProd P k (i - k) f l
  have hgstep : ∀ k < i,
      g k - g (k + 1) = -rawHouseholderZTerm v β f i k l := by
    intro k hk
    have hlen : i - k = (i - (k + 1)) + 1 := by omega
    have htail :
        g k =
          g (k + 1) - rawHouseholderZTerm v β f i k l := by
      simp only [g, hlen, Wave19.applyProd_succ, P]
      rw [householder_matMulVec_eq]
      rfl
    linarith
  have htel := Finset.sum_range_sub' g i
  have hsum :
      (∑ k ∈ Finset.range i, (g k - g (k + 1))) =
        -∑ k ∈ Finset.range i, rawHouseholderZTerm v β f i k l := by
    calc
      (∑ k ∈ Finset.range i, (g k - g (k + 1))) =
          ∑ k ∈ Finset.range i,
            -rawHouseholderZTerm v β f i k l := by
              apply Finset.sum_congr rfl
              intro k hk
              exact hgstep k (Finset.mem_range.mp hk)
      _ = -∑ k ∈ Finset.range i,
          rawHouseholderZTerm v β f i k l := by
            rw [Finset.sum_neg_distrib]
  have hg0 : g 0 =
      Wave19.applyProd (fun t => householder m (v t) (β t)) 0 i f l := by
    simp [g, P]
  have hgi : g i = f l := by
    simp [g]
  rw [hsum, hg0, hgi] at htel
  linarith

/-- Append one matrix at the inner end of `applyProd`.

`applyProd P a len` is defined by recursion at the outer end; this companion
identity is what connects it to the right-growing `Qacc` trace. -/
theorem applyProd_snoc {m : ℕ} (P : ℕ → Fin m → Fin m → ℝ)
    (a len : ℕ) (x : Fin m → ℝ) :
    Wave19.applyProd P a (len + 1) x =
      Wave19.applyProd P a len (matMulVec m (P (a + len)) x) := by
  induction len generalizing a x with
  | zero => simp [Wave19.applyProd]
  | succ len ih =>
      calc
        Wave19.applyProd P a ((len + 1) + 1) x =
            matMulVec m (P a) (Wave19.applyProd P (a + 1) (len + 1) x) := rfl
        _ = matMulVec m (P a)
            (Wave19.applyProd P (a + 1) len
              (matMulVec m (P ((a + 1) + len)) x)) := by
              rw [ih]
        _ = matMulVec m (P a)
            (Wave19.applyProd P (a + 1) len
              (matMulVec m (P (a + (len + 1))) x)) := by
              rw [show (a + 1) + len = a + (len + 1) by omega]
        _ = Wave19.applyProd P a (len + 1)
            (matMulVec m (P (a + (len + 1))) x) := rfl

/-- The matrix accumulated by the concrete residual telescope acts as the
corresponding ordered product when every stage matrix is symmetric. -/
theorem qacc_matMulVec_eq_applyProd {m : ℕ}
    (P : ℕ → Fin m → Fin m → ℝ)
    (hsymm : ∀ k, matTranspose (P k) = P k)
    (len : ℕ) (x : Fin m → ℝ) :
    matMulVec m (Wave19.Qacc P len) x =
      Wave19.applyProd P 0 len x := by
  induction len generalizing x with
  | zero =>
      simp [Wave19.Qacc, matMulVec_id]
  | succ len ih =>
      ext l
      rw [Wave19.Qacc, matMulVec_matMul]
      rw [hsymm len]
      rw [ih]
      simpa using congrFun (applyProd_snoc P 0 len x).symm l

/-- Rectangular-column version of `qacc_matMulVec_eq_applyProd`. -/
theorem qacc_matMulRect_eq_applyProd {m p : ℕ}
    (P : ℕ → Fin m → Fin m → ℝ)
    (hsymm : ∀ k, matTranspose (P k) = P k)
    (len : ℕ) (E : Fin m → Fin p → ℝ)
    (r : Fin m) (j : Fin p) :
    matMulRect m m p (Wave19.Qacc P len) E r j =
      Wave19.applyProd P 0 len (fun s => E s j) r := by
  have h := qacc_matMulVec_eq_applyProd P hsymm len (fun s => E s j)
  exact congrFun h r

/-- Entrywise bound for the image of one stage error through all preceding
raw Householder reflectors.

The decisive premise is `hratio`: it compares the norm of this one error `f`
with each earlier raw vector.  This is the source-faithful replacement for the
invalid premise comparing a recursively accumulated perturbation with a
single reflector. -/
theorem applyProd_rawHouseholder_entrywise_le {m : ℕ}
    (v : ℕ → Fin m → ℝ) (β : ℕ → ℝ) (f : Fin m → ℝ)
    (alpha : Fin m → ℝ) (gammaTilde : ℝ) (i : ℕ) (l : Fin m)
    (hgammaTilde : 0 ≤ gammaTilde)
    (halpha : ∀ r, 0 ≤ alpha r)
    (horth : ∀ k, IsOrthogonal m (householder m (v k) (β k)))
    (hvpos : ∀ k < i, 0 < vecNorm2 (v k))
    (hbeta : ∀ k < i, β k * vecNorm2 (v k) ^ 2 = 2)
    (hvrow : ∀ k < i, ∀ r, |v k r| ≤ 2 * alpha r)
    (hratio : ∀ k < i, vecNorm2 f / vecNorm2 (v k) ≤ gammaTilde)
    (hfrow : |f l| ≤ gammaTilde * alpha l) :
    |Wave19.applyProd (fun t => householder m (v t) (β t)) 0 i f l| ≤
      (1 + 4 * (i : ℝ)) * gammaTilde * alpha l := by
  let P : ℕ → Fin m → Fin m → ℝ :=
    fun t => householder m (v t) (β t)
  let zterm : ℕ → Fin m → ℝ := rawHouseholderZTerm v β f i
  apply Wave19.y_i_entrywise_bound
    (Wave19.applyProd P 0 i f) f zterm gammaTilde (alpha l) i l
    hgammaTilde (halpha l)
  · simpa [P, zterm] using
      applyProd_rawHouseholder_coordinate_expansion v β f i l
  · exact hfrow
  · intro k hk
    have hki : k < i := Finset.mem_range.mp hk
    let wk : Fin m → ℝ :=
      Wave19.applyProd P (k + 1) (i - (k + 1)) f
    have hwknorm : vecNorm2 wk = vecNorm2 f := by
      exact Wave19.vecNorm2_applyProd P horth (k + 1)
        (i - (k + 1)) f
    have hrank := Wave19.zk_rankOne_entrywise_le
      (v k) wk (alpha l) l (hvpos k hki) (halpha l) (hvrow k hki l)
    have hratioW : vecNorm2 wk / vecNorm2 (v k) ≤ gammaTilde := by
      rw [hwknorm]
      exact hratio k hki
    have hscale : 0 ≤ 4 * alpha l :=
      mul_nonneg (by norm_num) (halpha l)
    have hbound :
        |(2 / vecNorm2 (v k) ^ 2) * v k l *
            (∑ s : Fin m, v k s * wk s)| ≤
          4 * gammaTilde * alpha l := by
      calc
        |(2 / vecNorm2 (v k) ^ 2) * v k l *
            (∑ s : Fin m, v k s * wk s)| ≤
            4 * alpha l * (vecNorm2 wk / vecNorm2 (v k)) := hrank
        _ ≤ 4 * alpha l * gammaTilde :=
          mul_le_mul_of_nonneg_left hratioW hscale
        _ = 4 * gammaTilde * alpha l := by ring
    have hvsq_ne : vecNorm2 (v k) ^ 2 ≠ 0 :=
      ne_of_gt (sq_pos_of_pos (hvpos k hki))
    have hcoef : β k = 2 / vecNorm2 (v k) ^ 2 :=
      (eq_div_iff hvsq_ne).2 (hbeta k hki)
    simpa [zterm, rawHouseholderZTerm, P, wk, hcoef] using hbound

/-- The per-error transport bound with its ratio discharged by the executed
sigma ordering.

Here `sigma` is the pivot scale at the stage where `f` was created.  The same
scale bounds `‖f‖₂` from above and every preceding raw reflector norm from
below.  This is precisely Cox--Higham equation (2.12). -/
theorem applyProd_rawHouseholder_entrywise_le_of_sigma_ordering {m : ℕ}
    (v : ℕ → Fin m → ℝ) (β : ℕ → ℝ) (f : Fin m → ℝ)
    (alpha : Fin m → ℝ)
    (sigma u gamma gammaTilde : ℝ) (i : ℕ) (l : Fin m)
    (hgammaTilde : 0 ≤ gammaTilde)
    (halpha : ∀ r, 0 ≤ alpha r)
    (horth : ∀ k, IsOrthogonal m (householder m (v k) (β k)))
    (hvpos : ∀ k < i, 0 < vecNorm2 (v k))
    (hbeta : ∀ k < i, β k * vecNorm2 (v k) ^ 2 = 2)
    (hvrow : ∀ k < i, ∀ r, |v k r| ≤ 2 * alpha r)
    (hsigma : 0 < |sigma|)
    (huGamma : 0 ≤ u + 2 * gamma)
    (hfNorm : vecNorm2 f ≤ (u + 2 * gamma) * |sigma|)
    (hvSigma : ∀ k < i, Real.sqrt 2 * |sigma| ≤ vecNorm2 (v k))
    (hfold : (u + 2 * gamma) / Real.sqrt 2 ≤ gammaTilde)
    (hfrow : |f l| ≤ gammaTilde * alpha l) :
    |Wave19.applyProd (fun t => householder m (v t) (β t)) 0 i f l| ≤
      (1 + 4 * (i : ℝ)) * gammaTilde * alpha l := by
  apply applyProd_rawHouseholder_entrywise_le v β f alpha gammaTilde i l
    hgammaTilde halpha horth hvpos hbeta hvrow
  · intro k hk
    exact Wave19.sigma_ordering_norm_ratio_le f (v k)
      sigma u gamma gammaTilde hsigma huGamma hfNorm (hvSigma k hk) hfold
  · exact hfrow

/-- One fixed-shape telescope stage, with the transported error bounded by the
raw-vector sigma-ordering argument. -/
theorem qacc_rawHouseholder_stageImage_entrywise_le_of_sigma_ordering
    {m p : ℕ}
    (v : ℕ → Fin m → ℝ) (β : ℕ → ℝ)
    (E : Fin m → Fin p → ℝ) (alpha : Fin m → ℝ)
    (sigma u gamma gammaTilde : ℝ) (k : ℕ) (r : Fin m) (j : Fin p)
    (hgammaTilde : 0 ≤ gammaTilde)
    (halpha : ∀ s, 0 ≤ alpha s)
    (horth : ∀ q, IsOrthogonal m (householder m (v q) (β q)))
    (hvpos : ∀ q < k + 1, 0 < vecNorm2 (v q))
    (hbeta : ∀ q < k + 1, β q * vecNorm2 (v q) ^ 2 = 2)
    (hvrow : ∀ q < k + 1, ∀ s, |v q s| ≤ 2 * alpha s)
    (hsigma : 0 < |sigma|)
    (huGamma : 0 ≤ u + 2 * gamma)
    (hfNorm : vecNorm2 (fun s => E s j) ≤
      (u + 2 * gamma) * |sigma|)
    (hvSigma : ∀ q < k + 1,
      Real.sqrt 2 * |sigma| ≤ vecNorm2 (v q))
    (hfold : (u + 2 * gamma) / Real.sqrt 2 ≤ gammaTilde)
    (hfrow : |E r j| ≤ gammaTilde * alpha r) :
    |matMulRect m m p
        (Wave19.Qacc (fun q => householder m (v q) (β q)) (k + 1)) E r j| ≤
      (1 + 4 * ((k : ℝ) + 1)) * gammaTilde * alpha r := by
  let P : ℕ → Fin m → Fin m → ℝ :=
    fun q => householder m (v q) (β q)
  rw [qacc_matMulRect_eq_applyProd P
    (fun q => householder_symmetric m (v q) (β q)) (k + 1) E r j]
  have h := applyProd_rawHouseholder_entrywise_le_of_sigma_ordering
    v β (fun s => E s j) alpha sigma u gamma gammaTilde (k + 1) r
    hgammaTilde halpha horth hvpos hbeta hvrow hsigma huGamma hfNorm
    hvSigma hfold hfrow
  simpa [P, Nat.cast_add, Nat.cast_one] using h

/-- Source-faithful constructor for the Cox--Higham concrete stage bound.

The data are a fixed-shape executed trace: raw reflectors `v,β`, individual
stage residuals `Eseq`, and the pivot scale `sigma k` at each stage.  The norm
premise concerns `Eseq k` itself.  The conclusion is the exact stage envelope
consumed by the existing QR/minimizer assembly. -/
theorem concreteStageBound_of_rawHouseholder_sigmaTrace {m n : ℕ}
    (A : Fin m → Fin n → ℝ) (pi : Equiv.Perm (Fin n))
    (v : ℕ → Fin m → ℝ) (β : ℕ → ℝ)
    (Eseq : ℕ → Fin m → Fin n → ℝ)
    (alpha : Fin m → ℝ) (sigma u gamma gammaTilde : ℕ → ℝ)
    (dA : Fin m → Fin n → ℝ)
    (hdA : ∀ r j,
      dA r j = Wave19.DAacc
        (fun q => householder m (v q) (β q)) Eseq j.val r j)
    (hgammaTilde : ∀ k, 0 ≤ gammaTilde k)
    (halpha : ∀ r, 0 ≤ alpha r)
    (horth : ∀ q, IsOrthogonal m (householder m (v q) (β q)))
    (hvpos : ∀ k q, q < k + 1 → 0 < vecNorm2 (v q))
    (hbeta : ∀ k q, q < k + 1 → β q * vecNorm2 (v q) ^ 2 = 2)
    (hvrow : ∀ k q, q < k + 1 → ∀ r,
      |v q r| ≤ 2 * alpha r)
    (hsigma : ∀ k, 0 < |sigma k|)
    (huGamma : ∀ k, 0 ≤ u k + 2 * gamma k)
    (hfNorm : ∀ k j,
      vecNorm2 (fun s => Eseq k s j) ≤
        (u k + 2 * gamma k) * |sigma k|)
    (hvSigma : ∀ k q, q < k + 1 →
      Real.sqrt 2 * |sigma k| ≤ vecNorm2 (v q))
    (hfold : ∀ k,
      (u k + 2 * gamma k) / Real.sqrt 2 ≤ gammaTilde k)
    (hgammaUniform : ∀ k, gammaTilde k ≤ gammaTilde 0)
    (hfrow : ∀ k r j, |Eseq k r j| ≤ gammaTilde k * alpha r) :
    Wave19.ConcreteEntrywiseStageBound A pi dA alpha (gammaTilde 0) := by
  apply Wave19.concreteStageBound_of_yBounds A pi
    (fun q => householder m (v q) (β q)) Eseq alpha (gammaTilde 0) dA hdA
  intro k r j
  have hstage :=
    qacc_rawHouseholder_stageImage_entrywise_le_of_sigma_ordering
      v β (Eseq k) alpha (sigma k) (u k) (gamma k) (gammaTilde k)
      k r j (hgammaTilde k) halpha horth
      (hvpos k) (hbeta k) (hvrow k) (hsigma k) (huGamma k)
      (hfNorm k j) (hvSigma k) (hfold k) (hfrow k r j)
  have hcoeff_nonneg : 0 ≤ 1 + 4 * ((k : ℝ) + 1) := by positivity
  have halpha_r : 0 ≤ alpha r := halpha r
  calc
    |matMulRect m m n
        (Wave19.Qacc (fun q => householder m (v q) (β q)) (k + 1))
        (Eseq k) r j| ≤
        (1 + 4 * ((k : ℝ) + 1)) * gammaTilde k * alpha r := hstage
    _ ≤ (1 + 4 * ((k : ℝ) + 1)) * gammaTilde 0 * alpha r := by
      exact mul_le_mul_of_nonneg_right
        (mul_le_mul_of_nonneg_left (hgammaUniform k) hcoeff_nonneg) halpha_r

/-! ## A column-swap-aware fixed-shape residual telescope

The computed pivoted loop has a column exchange before each reflector.  The
plain `DAacc` telescope deliberately has no such exchange, so using it directly
would silently analyze a different algorithm.  The following accumulator keeps
the swaps in the state.  Its perturbation recurrence is

`Dₖ₊₁ = (Dₖ Sₖ) + Qₖ₊₁ Eₖ`,

and its permutation recurrence is the matching composition on the source
matrix.  This is the fixed-shape form needed for an actually executed pivoted
trace.
-/

/-- Accumulated source-column permutation for a sequence of executed swaps. -/
noncomputable def pivotPermAcc {p : ℕ}
    (Sseq : ℕ → Equiv.Perm (Fin p)) : ℕ → Equiv.Perm (Fin p)
  | 0 => Equiv.refl _
  | k + 1 => (Sseq k).trans (pivotPermAcc Sseq k)

/-- Nesting one more column permutation agrees with `pivotPermAcc`. -/
theorem columnPermuteMatrix_pivotPermAcc_succ {m p : ℕ}
    (A : Fin m → Fin p → ℝ) (Sseq : ℕ → Equiv.Perm (Fin p))
    (k : ℕ) :
    Wave13.columnPermuteMatrix
        (Wave13.columnPermuteMatrix A (pivotPermAcc Sseq k)) (Sseq k) =
      Wave13.columnPermuteMatrix A (pivotPermAcc Sseq (k + 1)) := by
  funext i j
  rfl

/-- Row multiplication commutes with a column permutation. -/
theorem columnPermuteMatrix_matMulRect {m p : ℕ}
    (M : Fin m → Fin m → ℝ) (A : Fin m → Fin p → ℝ)
    (S : Equiv.Perm (Fin p)) :
    Wave13.columnPermuteMatrix (matMulRect m m p M A) S =
      matMulRect m m p M (Wave13.columnPermuteMatrix A S) := by
  rfl

/-- Column permutation distributes over entrywise matrix addition. -/
theorem columnPermuteMatrix_add {m p : ℕ}
    (A B : Fin m → Fin p → ℝ) (S : Equiv.Perm (Fin p)) :
    Wave13.columnPermuteMatrix (fun i j => A i j + B i j) S =
      fun i j => Wave13.columnPermuteMatrix A S i j +
        Wave13.columnPermuteMatrix B S i j := by
  rfl

/-- Perturbation accumulator for a fixed-shape trace with a column swap before
each reflector application. -/
noncomputable def pivotDAacc {m p : ℕ}
    (Pseq : ℕ → Fin m → Fin m → ℝ)
    (Sseq : ℕ → Equiv.Perm (Fin p))
    (Eseq : ℕ → Fin m → Fin p → ℝ) :
    ℕ → Fin m → Fin p → ℝ
  | 0 => fun _ _ => 0
  | k + 1 => fun i j =>
      Wave13.columnPermuteMatrix (pivotDAacc Pseq Sseq Eseq k) (Sseq k) i j +
        matMulRect m m p (Wave19.Qacc Pseq (k + 1)) (Eseq k) i j

/-- **Column-swap-aware entrywise residual telescope.**

If an executed step first permutes the current columns and then applies the
exact reflector plus its individual residual,

`Aₖ₊₁ = Pₖ (Aₖ Sₖ) + Eₖ`,

then the state after `r` steps is

`Aᵣ = Qᵣᵀ (A₀ Piᵣ + Dᵣ)`

with `Piᵣ = pivotPermAcc Sseq r` and `Dᵣ = pivotDAacc ... r`. -/
theorem pivoted_entrywise_residual_telescope {m p : ℕ} (r : ℕ)
    (Aseq : ℕ → Fin m → Fin p → ℝ)
    (Pseq : ℕ → Fin m → Fin m → ℝ)
    (Sseq : ℕ → Equiv.Perm (Fin p))
    (Eseq : ℕ → Fin m → Fin p → ℝ)
    (hP : ∀ k, IsOrthogonal m (Pseq k))
    (hStep : ∀ k, k < r → ∀ i j,
      Aseq (k + 1) i j =
        matMulRect m m p (Pseq k)
          (Wave13.columnPermuteMatrix (Aseq k) (Sseq k)) i j + Eseq k i j) :
    ∀ i j, Aseq r i j =
      matMulRect m m p (matTranspose (Wave19.Qacc Pseq r))
        (fun a b =>
          Wave13.columnPermuteMatrix (Aseq 0) (pivotPermAcc Sseq r) a b +
            pivotDAacc Pseq Sseq Eseq r a b) i j := by
  induction r with
  | zero =>
      intro i j
      simp [Wave19.Qacc, pivotPermAcc, pivotDAacc, matTranspose_id,
        matMulRect_id_left, Wave13.columnPermuteMatrix]
  | succ r ih =>
      intro i j
      have hStepPrefix : ∀ k, k < r → ∀ i j,
          Aseq (k + 1) i j =
            matMulRect m m p (Pseq k)
              (Wave13.columnPermuteMatrix (Aseq k) (Sseq k)) i j +
                Eseq k i j :=
        fun k hk => hStep k (Nat.lt_trans hk (Nat.lt_succ_self r))
      have ihr := ih hStepPrefix
      set Q : Fin m → Fin m → ℝ := Wave19.Qacc Pseq r with hQdef
      set D : Fin m → Fin p → ℝ := pivotDAacc Pseq Sseq Eseq r with hDdef
      set Pi : Equiv.Perm (Fin p) := pivotPermAcc Sseq r with hPidef
      set P : Fin m → Fin m → ℝ := Pseq r with hPdef
      set S : Equiv.Perm (Fin p) := Sseq r with hSdef
      set Q' : Fin m → Fin m → ℝ :=
        matMul m Q (matTranspose P) with hQ'def
      have hQorth : IsOrthogonal m Q := Wave19.Qacc_orthogonal Pseq hP r
      have hPorth : IsOrthogonal m P := hP r
      have hQ'orth : IsOrthogonal m Q' := hQorth.mul hPorth.transpose
      set B : Fin m → Fin p → ℝ := fun a b =>
        Wave13.columnPermuteMatrix (Aseq 0) Pi a b + D a b with hBdef
      have hAhat : ∀ i j,
          Aseq r i j = matMulRect m m p (matTranspose Q) B i j := by
        intro a b
        simpa [Q, D, Pi, B] using ihr a b
      have hAhatEq : Aseq r = matMulRect m m p (matTranspose Q) B :=
        funext fun a => funext fun b => hAhat a b
      set C : Fin m → Fin p → ℝ :=
        Wave13.columnPermuteMatrix B S with hCdef
      have hSwapEq :
          Wave13.columnPermuteMatrix (Aseq r) S =
            matMulRect m m p (matTranspose Q) C := by
        rw [hAhatEq, columnPermuteMatrix_matMulRect]
      have hNext : ∀ i j,
          Aseq (r + 1) i j =
            matMulRect m m p P
              (Wave13.columnPermuteMatrix (Aseq r) S) i j + Eseq r i j := by
        intro a b
        simpa [P, S] using hStep r (Nat.lt_succ_self r) a b
      have hQinv : matMul m (matTranspose Q') Q' = idMatrix m :=
        funext fun a => funext fun b => hQ'orth.left_inv a b
      have hQ'T : matTranspose Q' = matMul m P (matTranspose Q) := by
        show matTranspose (matMul m Q (matTranspose P)) = _
        rw [matTranspose_matMul, matTranspose_involutive]
      have eq1 :
          matMulRect m m p (matTranspose Q') C =
            matMulRect m m p P
              (Wave13.columnPermuteMatrix (Aseq r) S) := by
        rw [hQ'T, matMulRect_assoc_square_left, ← hSwapEq]
      set E' : Fin m → Fin p → ℝ :=
        matMulRect m m p Q' (Eseq r) with hE'def
      have eq2 : matMulRect m m p (matTranspose Q') E' = Eseq r := by
        show matMulRect m m p (matTranspose Q')
          (matMulRect m m p Q' (Eseq r)) = _
        rw [← matMulRect_assoc_square_left, hQinv, matMulRect_id_left]
      have hCexpand : C = fun a b =>
          Wave13.columnPermuteMatrix (Aseq 0)
              (pivotPermAcc Sseq (r + 1)) a b +
            Wave13.columnPermuteMatrix D S a b := by
        funext a b
        simp only [C, B, Wave13.columnPermuteMatrix]
        rfl
      have hDsucc : ∀ a b,
          pivotDAacc Pseq Sseq Eseq (r + 1) a b =
            Wave13.columnPermuteMatrix D S a b + E' a b := by
        intro a b
        simp only [pivotDAacc, hDdef, hSdef, hE'def, hQ'def, hQdef, hPdef,
          Wave19.Qacc]
      have hBE :
          (fun a b =>
            Wave13.columnPermuteMatrix (Aseq 0)
                (pivotPermAcc Sseq (r + 1)) a b +
              pivotDAacc Pseq Sseq Eseq (r + 1) a b) =
            fun a b => C a b + E' a b := by
        funext a b
        rw [hDsucc a b, hCexpand]
        ring
      have hQaccSucc : Wave19.Qacc Pseq (r + 1) = Q' := by
        simp only [Wave19.Qacc, hQ'def, hQdef, hPdef]
      rw [hQaccSucc, hBE, hNext i j]
      calc
        matMulRect m m p P
              (Wave13.columnPermuteMatrix (Aseq r) S) i j + Eseq r i j =
            matMulRect m m p (matTranspose Q') C i j +
              matMulRect m m p (matTranspose Q') E' i j := by
                rw [← congrFun (congrFun eq1 i) j,
                  ← congrFun (congrFun eq2 i) j]
        _ = matMulRect m m p (matTranspose Q')
            (fun a b => C a b + E' a b) i j :=
          (congrFun
            (congrFun (matMulRect_add_right m m p (matTranspose Q') C E') i) j).symm

/-- Entrywise bound for the swap-aware perturbation accumulator.

At stage `k`, the swap fixes completed positions `< k` and maps the active
suffix into itself.  The stage residual is zero on completed columns.  Hence a
column completed at position `j` receives exactly the first `j+1` transported
stage errors, even though its source label may move among active columns before
completion. -/
theorem pivotDAacc_entrywise_bound {m p : ℕ}
    (Pseq : ℕ → Fin m → Fin m → ℝ)
    (Sseq : ℕ → Equiv.Perm (Fin p))
    (Eseq : ℕ → Fin m → Fin p → ℝ)
    (stageBound : ℕ → Fin m → ℝ)
    (hSfix : ∀ k j, j.val < k → Sseq k j = j)
    (hSactive : ∀ k j, k ≤ j.val → k ≤ (Sseq k j).val)
    (hyZero : ∀ k i j, j.val < k →
      matMulRect m m p (Wave19.Qacc Pseq (k + 1)) (Eseq k) i j = 0)
    (hyBound : ∀ k i j,
      |matMulRect m m p (Wave19.Qacc Pseq (k + 1)) (Eseq k) i j| ≤
        stageBound k i)
    (r : ℕ) (i : Fin m) (j : Fin p) :
    |pivotDAacc Pseq Sseq Eseq r i j| ≤
      ∑ k ∈ Finset.range (Nat.min r (j.val + 1)), stageBound k i := by
  induction r generalizing i j with
  | zero => simp [pivotDAacc]
  | succ r ih =>
      rw [pivotDAacc]
      by_cases hj : j.val < r
      · have hfix : Sseq r j = j := hSfix r j hj
        have hy0 :
            matMulRect m m p (Wave19.Qacc Pseq (r + 1)) (Eseq r) i j = 0 :=
          hyZero r i j hj
        have hminOld : Nat.min r (j.val + 1) = j.val + 1 :=
          Nat.min_eq_right (by omega)
        have hminNew : Nat.min (r + 1) (j.val + 1) = j.val + 1 :=
          Nat.min_eq_right (by omega)
        simpa [Wave13.columnPermuteMatrix, hfix, hy0, hminOld, hminNew]
          using ih i j
      · have hrj : r ≤ j.val := Nat.le_of_not_gt hj
        let sj : Fin p := Sseq r j
        have hrsj : r ≤ sj.val := hSactive r j hrj
        have hminOld : Nat.min r (sj.val + 1) = r :=
          Nat.min_eq_left (by omega)
        have hminNew : Nat.min (r + 1) (j.val + 1) = r + 1 :=
          Nat.min_eq_left (by omega)
        have hprev := ih i sj
        rw [hminOld] at hprev
        have hy := hyBound r i j
        calc
          |Wave13.columnPermuteMatrix
                (pivotDAacc Pseq Sseq Eseq r) (Sseq r) i j +
              matMulRect m m p (Wave19.Qacc Pseq (r + 1)) (Eseq r) i j| ≤
              |pivotDAacc Pseq Sseq Eseq r i sj| +
                |matMulRect m m p (Wave19.Qacc Pseq (r + 1)) (Eseq r) i j| := by
                  simpa [Wave13.columnPermuteMatrix, sj] using
                    abs_add_le
                      (pivotDAacc Pseq Sseq Eseq r i sj)
                      (matMulRect m m p (Wave19.Qacc Pseq (r + 1))
                        (Eseq r) i j)
          _ ≤ (∑ k ∈ Finset.range r, stageBound k i) + stageBound r i :=
            add_le_add hprev hy
          _ = ∑ k ∈ Finset.range (Nat.min (r + 1) (j.val + 1)),
              stageBound k i := by
                rw [hminNew, Finset.sum_range_succ]

/-- Final-horizon specialization: column `j` receives the first `j+1` stage
images. -/
theorem pivotDAacc_final_entrywise_bound {m p : ℕ}
    (Pseq : ℕ → Fin m → Fin m → ℝ)
    (Sseq : ℕ → Equiv.Perm (Fin p))
    (Eseq : ℕ → Fin m → Fin p → ℝ)
    (stageBound : ℕ → Fin m → ℝ)
    (hSfix : ∀ k j, j.val < k → Sseq k j = j)
    (hSactive : ∀ k j, k ≤ j.val → k ≤ (Sseq k j).val)
    (hyZero : ∀ k i j, j.val < k →
      matMulRect m m p (Wave19.Qacc Pseq (k + 1)) (Eseq k) i j = 0)
    (hyBound : ∀ k i j,
      |matMulRect m m p (Wave19.Qacc Pseq (k + 1)) (Eseq k) i j| ≤
        stageBound k i)
    (i : Fin m) (j : Fin p) :
    |pivotDAacc Pseq Sseq Eseq p i j| ≤
      ∑ k ∈ Finset.range (j.val + 1), stageBound k i := by
  have h := pivotDAacc_entrywise_bound Pseq Sseq Eseq stageBound
    hSfix hSactive hyZero hyBound p i j
  have hmin : Nat.min p (j.val + 1) = j.val + 1 :=
    Nat.min_eq_right (by omega)
  simpa [hmin] using h

/-- Printed Cox--Higham row envelope for a swap-aware trace. -/
theorem pivotDAacc_coxHigham_rowwise_bound {m p : ℕ}
    (Pseq : ℕ → Fin m → Fin m → ℝ)
    (Sseq : ℕ → Equiv.Perm (Fin p))
    (Eseq : ℕ → Fin m → Fin p → ℝ)
    (alpha : Fin m → ℝ) (gammaTilde : ℝ)
    (hgammaTilde : 0 ≤ gammaTilde) (halpha : ∀ i, 0 ≤ alpha i)
    (hSfix : ∀ k j, j.val < k → Sseq k j = j)
    (hSactive : ∀ k j, k ≤ j.val → k ≤ (Sseq k j).val)
    (hyZero : ∀ k i j, j.val < k →
      matMulRect m m p (Wave19.Qacc Pseq (k + 1)) (Eseq k) i j = 0)
    (hyBound : ∀ k i j,
      |matMulRect m m p (Wave19.Qacc Pseq (k + 1)) (Eseq k) i j| ≤
        (1 + 4 * ((k : ℝ) + 1)) * gammaTilde * alpha i)
    (i : Fin m) (j : Fin p) :
    |pivotDAacc Pseq Sseq Eseq p i j| ≤
      ((j.val : ℝ) + 1) ^ 2 * (5 * gammaTilde) * alpha i := by
  have h := pivotDAacc_final_entrywise_bound Pseq Sseq Eseq
    (fun k i => (1 + 4 * ((k : ℝ) + 1)) * gammaTilde * alpha i)
    hSfix hSactive hyZero hyBound i j
  have hfactor :
      (∑ k ∈ Finset.range (j.val + 1),
        (1 + 4 * ((k : ℝ) + 1)) * gammaTilde * alpha i) =
      (∑ k ∈ Finset.range (j.val + 1),
        (1 + 4 * ((k : ℝ) + 1))) * gammaTilde * alpha i := by
    rw [← Finset.sum_mul, ← Finset.sum_mul]
  rw [hfactor] at h
  have hsum := Wave19.stage_sum_le_five_j_sq (j.val + 1)
  have hscale : 0 ≤ gammaTilde * alpha i :=
    mul_nonneg hgammaTilde (halpha i)
  calc
    |pivotDAacc Pseq Sseq Eseq p i j| ≤
        (∑ k ∈ Finset.range (j.val + 1),
          (1 + 4 * ((k : ℝ) + 1))) * gammaTilde * alpha i := h
    _ = (∑ k ∈ Finset.range (j.val + 1),
          (1 + 4 * ((k : ℝ) + 1))) * (gammaTilde * alpha i) := by ring
    _ ≤ (5 * ((j.val + 1 : ℕ) : ℝ) ^ 2) *
          (gammaTilde * alpha i) :=
      mul_le_mul_of_nonneg_right hsum hscale
    _ = (5 * ((j.val + 1 : ℕ) : ℝ) ^ 2) * gammaTilde * alpha i := by ring
    _ = ((j.val : ℝ) + 1) ^ 2 * (5 * gammaTilde) * alpha i := by
      push_cast
      ring

/-! ## The actually executed active-max stored QR trace

We now instantiate the swap-aware recursion with a concrete loop.  At stage
`k` it selects the active trailing column of maximal Euclidean norm, swaps that
column into position `k`, forms the signed raw Householder vector on rows
`k:m`, and calls the repository's rounded compact stored-panel kernel. -/

/-- Exact beta-spec reflectors are orthogonal, including the zero-vector case
where `betaSpec = 0` and the reflector is the identity. -/
theorem householder_betaSpec_orthogonal (m : ℕ) (v : Fin m → ℝ) :
    IsOrthogonal m (householder m v (householderBetaSpec m v)) := by
  by_cases hden : (∑ i : Fin m, v i * v i) = 0
  · have hbeta : householderBetaSpec m v = 0 := by
      simp [householderBetaSpec, hden]
    have heq : householder m v (householderBetaSpec m v) = idMatrix m := by
      ext i j
      simp [householder, hbeta]
    rw [heq]
    exact idMatrix_orthogonal m
  · exact householder_orthogonal m v (householderBetaSpec m v)
      (householderBeta_mul_inner_self_eq_two m v hden)

/-- Row index corresponding to active column stage `k`. -/
def pivotedQRActiveRow {m n : ℕ} (hmn : n ≤ m) (k : ℕ) (hk : k < n) : Fin m :=
  ⟨k, lt_of_lt_of_le hk hmn⟩

/-- Column index corresponding to active stage `k`. -/
def pivotedQRActiveCol {n : ℕ} (k : ℕ) (hk : k < n) : Fin n := ⟨k, hk⟩

/-- Concrete full-shape column-pivoted stored Householder QR matrix trace. -/
noncomputable def fl_pivotedStoredQRMatrixSeq (fp : FPModel) {m n : ℕ}
    (hmn : n ≤ m) (A : Fin m → Fin n → ℝ) :
    ℕ → Fin m → Fin n → ℝ
  | 0 => A
  | k + 1 =>
      if hk : k < n then
        let Aprev := fl_pivotedStoredQRMatrixSeq fp hmn A k
        let row := pivotedQRActiveRow hmn k hk
        let col := pivotedQRActiveCol k hk
        let q := householderActiveMaxPivotColumn row col Aprev
        let S : Equiv.Perm (Fin n) := Equiv.swap col q
        let As := Wave13.columnPermuteMatrix Aprev S
        let x : Fin m → ℝ := fun i => As i col
        let alpha := signedHouseholderAlpha
          (Real.sqrt (householderTrailingNorm2Sq m row x)) (x row)
        let v := householderTrailingActiveVector m row x alpha
        let beta := householderBetaSpec m v
        fl_householderStoredPanelStep fp m n k v beta As
      else
        fl_pivotedStoredQRMatrixSeq fp hmn A k

/-- Executed stage swap, extended by the identity after the QR horizon. -/
noncomputable def pivotedStoredQRSwapSeq (fp : FPModel) {m n : ℕ}
    (hmn : n ≤ m) (A : Fin m → Fin n → ℝ)
    (k : ℕ) : Equiv.Perm (Fin n) :=
  if hk : k < n then
    let row := pivotedQRActiveRow hmn k hk
    let col := pivotedQRActiveCol k hk
    Equiv.swap col
      (householderActiveMaxPivotColumn row col
        (fl_pivotedStoredQRMatrixSeq fp hmn A k))
  else
    Equiv.refl _

/-- Panel after the actually executed active-max column exchange. -/
noncomputable def pivotedStoredQRSwappedPanel (fp : FPModel) {m n : ℕ}
    (hmn : n ≤ m) (A : Fin m → Fin n → ℝ)
    (k : ℕ) : Fin m → Fin n → ℝ :=
  Wave13.columnPermuteMatrix (fl_pivotedStoredQRMatrixSeq fp hmn A k)
    (pivotedStoredQRSwapSeq fp hmn A k)

/-- Raw signed Householder vector formed by executed stage `k`. -/
noncomputable def pivotedStoredQRRawVector (fp : FPModel) {m n : ℕ}
    (hmn : n ≤ m) (A : Fin m → Fin n → ℝ)
    (k : ℕ) : Fin m → ℝ :=
  if hk : k < n then
    let row := pivotedQRActiveRow hmn k hk
    let col := pivotedQRActiveCol k hk
    let As := pivotedStoredQRSwappedPanel fp hmn A k
    let x : Fin m → ℝ := fun i => As i col
    let alpha := signedHouseholderAlpha
      (Real.sqrt (householderTrailingNorm2Sq m row x)) (x row)
    householderTrailingActiveVector m row x alpha
  else
    0

/-- Exact raw beta paired with the executed signed vector. -/
noncomputable def pivotedStoredQRBeta (fp : FPModel) {m n : ℕ}
    (hmn : n ≤ m) (A : Fin m → Fin n → ℝ)
    (k : ℕ) : ℝ :=
  householderBetaSpec m (pivotedStoredQRRawVector fp hmn A k)

/-- Exact reflector sequence paired with the executed rounded trace. -/
noncomputable def pivotedStoredQRPseq (fp : FPModel) {m n : ℕ}
    (hmn : n ≤ m) (A : Fin m → Fin n → ℝ)
    (k : ℕ) : Fin m → Fin m → ℝ :=
  householder m (pivotedStoredQRRawVector fp hmn A k)
    (pivotedStoredQRBeta fp hmn A k)

/-- Individual residual of one actually executed swapped-and-reflected stage. -/
noncomputable def pivotedStoredQREseq (fp : FPModel) {m n : ℕ}
    (hmn : n ≤ m) (A : Fin m → Fin n → ℝ)
    (k : ℕ) : Fin m → Fin n → ℝ :=
  fun i j =>
    fl_pivotedStoredQRMatrixSeq fp hmn A (k + 1) i j -
      matMulRect m m n (pivotedStoredQRPseq fp hmn A k)
        (pivotedStoredQRSwappedPanel fp hmn A k) i j

/-- The executed trace recurrence, expressed through the named stage data. -/
theorem fl_pivotedStoredQRMatrixSeq_succ_of_lt (fp : FPModel) {m n : ℕ}
    (hmn : n ≤ m) (A : Fin m → Fin n → ℝ)
    (k : ℕ) (hk : k < n) :
    fl_pivotedStoredQRMatrixSeq fp hmn A (k + 1) =
      fl_householderStoredPanelStep fp m n k
        (pivotedStoredQRRawVector fp hmn A k)
        (pivotedStoredQRBeta fp hmn A k)
        (pivotedStoredQRSwappedPanel fp hmn A k) := by
  simp [fl_pivotedStoredQRMatrixSeq, pivotedStoredQRRawVector,
    pivotedStoredQRBeta, pivotedStoredQRSwappedPanel,
    pivotedStoredQRSwapSeq, hk]

/-- The exact reflector sequence of the actual trace is orthogonal. -/
theorem pivotedStoredQRPseq_orthogonal (fp : FPModel) {m n : ℕ}
    (hmn : n ≤ m) (A : Fin m → Fin n → ℝ) (k : ℕ) :
    IsOrthogonal m (pivotedStoredQRPseq fp hmn A k) := by
  exact householder_betaSpec_orthogonal m
    (pivotedStoredQRRawVector fp hmn A k)

/-- The named stage residual gives the exact swapped recurrence required by
`pivoted_entrywise_residual_telescope`. -/
theorem pivotedStoredQR_step_with_residual (fp : FPModel) {m n : ℕ}
    (hmn : n ≤ m) (A : Fin m → Fin n → ℝ)
    (k : ℕ) (i : Fin m) (j : Fin n) :
    fl_pivotedStoredQRMatrixSeq fp hmn A (k + 1) i j =
      matMulRect m m n (pivotedStoredQRPseq fp hmn A k)
          (Wave13.columnPermuteMatrix
            (fl_pivotedStoredQRMatrixSeq fp hmn A k)
            (pivotedStoredQRSwapSeq fp hmn A k)) i j +
        pivotedStoredQREseq fp hmn A k i j := by
  simp only [pivotedStoredQREseq, pivotedStoredQRSwappedPanel]
  ring

/-- Executed stage swaps fix every already completed column position. -/
theorem pivotedStoredQRSwapSeq_fix_prefix (fp : FPModel) {m n : ℕ}
    (hmn : n ≤ m) (A : Fin m → Fin n → ℝ)
    (k : ℕ) (j : Fin n) (hj : j.val < k) :
    pivotedStoredQRSwapSeq fp hmn A k j = j := by
  by_cases hk : k < n
  · let row := pivotedQRActiveRow hmn k hk
    let col := pivotedQRActiveCol k hk
    let q := householderActiveMaxPivotColumn row col
      (fl_pivotedStoredQRMatrixSeq fp hmn A k)
    have hjc : j ≠ col := by
      intro h
      subst j
      exact (Nat.lt_irrefl k hj)
    have hqge : k ≤ q.val := by
      simpa [q, col] using
        householderActiveMaxPivotColumn_ge row col
          (fl_pivotedStoredQRMatrixSeq fp hmn A k)
    have hjq : j ≠ q := by
      intro h
      subst j
      omega
    simp only [pivotedStoredQRSwapSeq, dif_pos hk]
    exact Equiv.swap_apply_of_ne_of_ne hjc hjq
  · simp [pivotedStoredQRSwapSeq, hk]

/-- Executed stage swaps map the active suffix into itself. -/
theorem pivotedStoredQRSwapSeq_maps_active (fp : FPModel) {m n : ℕ}
    (hmn : n ≤ m) (A : Fin m → Fin n → ℝ)
    (k : ℕ) (j : Fin n) (hj : k ≤ j.val) :
    k ≤ (pivotedStoredQRSwapSeq fp hmn A k j).val := by
  by_cases hk : k < n
  · let row := pivotedQRActiveRow hmn k hk
    let col := pivotedQRActiveCol k hk
    let q := householderActiveMaxPivotColumn row col
      (fl_pivotedStoredQRMatrixSeq fp hmn A k)
    have hqge : k ≤ q.val := by
      simpa [q, col] using
        householderActiveMaxPivotColumn_ge row col
          (fl_pivotedStoredQRMatrixSeq fp hmn A k)
    simp only [pivotedStoredQRSwapSeq, dif_pos hk]
    by_cases hjc : j = col
    · subst j
      rw [Equiv.swap_apply_left]
      exact hqge
    · by_cases hjq : j = q
      · subst j
        rw [Equiv.swap_apply_right]
        rfl
      · rw [Equiv.swap_apply_of_ne_of_ne hjc hjq]
        exact hj
  · simp [pivotedStoredQRSwapSeq, hk]
    exact hj

/-- A transposition permutation is exactly the corresponding concrete column
swap. -/
theorem columnPermuteMatrix_swap_eq_householderSwapColumns {m n : ℕ}
    (A : Fin m → Fin n → ℝ) (a b : Fin n) :
    Wave13.columnPermuteMatrix A (Equiv.swap a b) =
      householderSwapColumns A a b := by
  funext i j
  simp only [Wave13.columnPermuteMatrix, householderSwapColumns,
    Equiv.swap_apply_def]
  split_ifs <;> rfl

/-- The executed selector really places an active trailing-norm-maximal column
in the displayed pivot position. -/
theorem pivotedStoredQRSwappedPanel_pivot_max (fp : FPModel) {m n : ℕ}
    (hmn : n ≤ m) (A : Fin m → Fin n → ℝ)
    (k : ℕ) (hk : k < n) :
    ∀ l : Fin n, k ≤ l.val →
      householderTrailingColumnNorm2Sq
          (pivotedQRActiveRow hmn k hk)
          (pivotedStoredQRSwappedPanel fp hmn A k) l ≤
        householderTrailingColumnNorm2Sq
          (pivotedQRActiveRow hmn k hk)
          (pivotedStoredQRSwappedPanel fp hmn A k)
          (pivotedQRActiveCol k hk) := by
  let Aprev := fl_pivotedStoredQRMatrixSeq fp hmn A k
  let row := pivotedQRActiveRow hmn k hk
  let col := pivotedQRActiveCol k hk
  let q := householderActiveMaxPivotColumn row col Aprev
  have hswap :
      pivotedStoredQRSwappedPanel fp hmn A k =
        householderSwapColumns Aprev col q := by
    unfold pivotedStoredQRSwappedPanel
    have hS : pivotedStoredQRSwapSeq fp hmn A k = Equiv.swap col q := by
      simp [pivotedStoredQRSwapSeq, hk, row, col, q, Aprev]
    rw [hS]
    exact columnPermuteMatrix_swap_eq_householderSwapColumns Aprev col q
  rw [hswap]
  exact householderSwapColumns_activeMaxPivotColumn_pivot_max row col Aprev

/-- Storage plus prefix-fixing swaps preserve exact lower-trapezoidal zeros in
the actual pivoted trace. -/
theorem fl_pivotedStoredQRMatrixSeq_prefix_lower_zero (fp : FPModel)
    {m n : ℕ} (hmn : n ≤ m) (A : Fin m → Fin n → ℝ) :
    ∀ k, k ≤ n → ∀ (i : Fin m) (j : Fin n),
      j.val < k → j.val < i.val →
        fl_pivotedStoredQRMatrixSeq fp hmn A k i j = 0 := by
  intro k
  induction k with
  | zero =>
      intro _hk i j hj _
      exact (Nat.not_lt_zero j.val hj).elim
  | succ k ih =>
      intro hkSucc i j hjSucc hji
      have hk : k < n := Nat.lt_of_succ_le hkSucc
      have hstepPoint :
          fl_pivotedStoredQRMatrixSeq fp hmn A (k + 1) i j =
            fl_householderStoredPanelStep fp m n k
              (pivotedStoredQRRawVector fp hmn A k)
              (pivotedStoredQRBeta fp hmn A k)
              (pivotedStoredQRSwappedPanel fp hmn A k) i j := by
        exact congrFun (congrFun
          (fl_pivotedStoredQRMatrixSeq_succ_of_lt fp hmn A k hk) i) j
      rcases Nat.lt_succ_iff_lt_or_eq.mp hjSucc with hj | hj
      · have hfix := pivotedStoredQRSwapSeq_fix_prefix fp hmn A k j hj
        calc
          fl_pivotedStoredQRMatrixSeq fp hmn A (k + 1) i j =
              fl_householderStoredPanelStep fp m n k
                (pivotedStoredQRRawVector fp hmn A k)
                (pivotedStoredQRBeta fp hmn A k)
                (pivotedStoredQRSwappedPanel fp hmn A k) i j := hstepPoint
          _ = pivotedStoredQRSwappedPanel fp hmn A k i j := by
            simp [fl_householderStoredPanelStep, hj]
          _ = fl_pivotedStoredQRMatrixSeq fp hmn A k i j := by
            simp [pivotedStoredQRSwappedPanel, Wave13.columnPermuteMatrix, hfix]
          _ = 0 := ih (Nat.le_of_lt hk) i j hj hji
      · let col : Fin n := ⟨k, hk⟩
        have hjfin : j = col := Fin.ext hj
        subst j
        have hki : k < i.val := by simpa [col] using hji
        rw [hstepPoint]
        simp [fl_householderStoredPanelStep, col, hki]

/-- The final matrix of the actual pivoted stored trace is upper
trapezoidal. -/
theorem fl_pivotedStoredQRMatrixSeq_upperTrapezoidal (fp : FPModel)
    {m n : ℕ} (hmn : n ≤ m) (A : Fin m → Fin n → ℝ) :
    IsUpperTrapezoidal m n (fl_pivotedStoredQRMatrixSeq fp hmn A n) := by
  intro i j hji
  exact fl_pivotedStoredQRMatrixSeq_prefix_lower_zero fp hmn A n le_rfl
    i j j.isLt hji

/-- After the QR horizon the concrete trace is held fixed. -/
theorem fl_pivotedStoredQRMatrixSeq_succ_of_ge (fp : FPModel) {m n : ℕ}
    (hmn : n ≤ m) (A : Fin m → Fin n → ℝ)
    (k : ℕ) (hk : n ≤ k) :
    fl_pivotedStoredQRMatrixSeq fp hmn A (k + 1) =
      fl_pivotedStoredQRMatrixSeq fp hmn A k := by
  simp [fl_pivotedStoredQRMatrixSeq, Nat.not_lt.mpr hk]

/-- Executed pivot scale: Euclidean norm of the displayed active trailing
column after the stage swap. -/
noncomputable def pivotedStoredQRSigma (fp : FPModel) {m n : ℕ}
    (hmn : n ≤ m) (A : Fin m → Fin n → ℝ) (k : ℕ) : ℝ :=
  if hk : k < n then
    Real.sqrt
      (householderTrailingColumnNorm2Sq
        (pivotedQRActiveRow hmn k hk)
        (pivotedStoredQRSwappedPanel fp hmn A k)
        (pivotedQRActiveCol k hk))
  else
    0

/-- The executed signed raw vector has a zero prefix before its stage row. -/
theorem pivotedStoredQRRawVector_zero_prefix (fp : FPModel) {m n : ℕ}
    (hmn : n ≤ m) (A : Fin m → Fin n → ℝ)
    (k : ℕ) (hk : k < n) (i : Fin m) (hi : i.val < k) :
    pivotedStoredQRRawVector fp hmn A k i = 0 := by
  simp only [pivotedStoredQRRawVector, dif_pos hk]
  exact householderTrailingActiveVector_zero_prefix m
    (pivotedQRActiveRow hmn k hk)
    (fun r => pivotedStoredQRSwappedPanel fp hmn A k r
      (pivotedQRActiveCol k hk))
    (signedHouseholderAlpha
      (Real.sqrt
        (householderTrailingNorm2Sq m (pivotedQRActiveRow hmn k hk)
          (fun r => pivotedStoredQRSwappedPanel fp hmn A k r
            (pivotedQRActiveCol k hk))))
      (pivotedStoredQRSwappedPanel fp hmn A k
        (pivotedQRActiveRow hmn k hk) (pivotedQRActiveCol k hk))) i hi

/-- Local Cox--Higham sign bound for the actually constructed raw vector. -/
theorem pivotedStoredQRRawVector_sigma_sign_bound (fp : FPModel) {m n : ℕ}
    (hmn : n ≤ m) (A : Fin m → Fin n → ℝ)
    (k : ℕ) (hk : k < n) :
    Real.sqrt 2 * |pivotedStoredQRSigma fp hmn A k| ≤
      vecNorm2 (pivotedStoredQRRawVector fp hmn A k) := by
  let row := pivotedQRActiveRow hmn k hk
  let col := pivotedQRActiveCol k hk
  let As := pivotedStoredQRSwappedPanel fp hmn A k
  let x : Fin m → ℝ := fun i => As i col
  let T := householderTrailingNorm2Sq m row x
  let v := householderTrailingActiveVector m row x
    (signedHouseholderAlpha (Real.sqrt T) (x row))
  have hT : 0 ≤ T := by
    exact householderTrailingNorm2Sq_nonneg m row x
  have hraw : 2 * T ≤ ∑ i : Fin m, v i * v i := by
    simpa [T, v] using
      householderTrailingActiveVector_inner_self_ge_two_trailingNorm2Sq_signed
        m row x
  have hsigma : pivotedStoredQRSigma fp hmn A k = Real.sqrt T := by
    simp [pivotedStoredQRSigma, hk, T, row, col, As, x,
      householderTrailingColumnNorm2Sq]
  have hv : pivotedStoredQRRawVector fp hmn A k = v := by
    simp [pivotedStoredQRRawVector, hk, v, T, row, col, As, x]
  rw [hsigma, abs_of_nonneg (Real.sqrt_nonneg _), hv]
  apply (sq_le_sq₀
    (mul_nonneg (Real.sqrt_nonneg _) (Real.sqrt_nonneg _))
    (vecNorm2_nonneg v)).mp
  calc
    (Real.sqrt 2 * Real.sqrt T) ^ 2 = 2 * T := by
      rw [mul_pow, Real.sq_sqrt (by norm_num : (0 : ℝ) ≤ 2),
        Real.sq_sqrt hT]
    _ ≤ ∑ i : Fin m, v i * v i := hraw
    _ = vecNorm2 v ^ 2 := by
      rw [vecNorm2_sq]
      simp [vecNorm2Sq, pow_two]

/-- Exact beta-spec normalization in Euclidean-norm notation. -/
theorem householderBetaSpec_mul_vecNorm2_sq_eq_two_of_pos {m : ℕ}
    (v : Fin m → ℝ) (hv : 0 < vecNorm2 v) :
    householderBetaSpec m v * vecNorm2 v ^ 2 = 2 := by
  have hden : (∑ i : Fin m, v i * v i) ≠ 0 := by
    intro hzero
    have hsq : vecNorm2 v ^ 2 = 0 := by
      rw [vecNorm2_sq]
      simpa [vecNorm2Sq, pow_two] using hzero
    nlinarith [sq_pos_of_pos hv]
  rw [vecNorm2_sq]
  simpa [vecNorm2Sq, pow_two] using
    householderBeta_mul_inner_self_eq_two m v hden

/-- An exact stage reflector preserves every already completed stored column. -/
theorem pivotedStoredQRPseq_completed_column_preservation (fp : FPModel)
    {m n : ℕ} (hmn : n ≤ m) (A : Fin m → Fin n → ℝ)
    (k : ℕ) (hk : k < n) (j : Fin n) (hj : j.val < k) :
    matMulVec m (pivotedStoredQRPseq fp hmn A k)
        (fun r => pivotedStoredQRSwappedPanel fp hmn A k r j) =
      fun r => fl_pivotedStoredQRMatrixSeq fp hmn A k r j := by
  let v := pivotedStoredQRRawVector fp hmn A k
  let beta := pivotedStoredQRBeta fp hmn A k
  let xcol : Fin m → ℝ :=
    fun r => pivotedStoredQRSwappedPanel fp hmn A k r j
  have hfix := pivotedStoredQRSwapSeq_fix_prefix fp hmn A k j hj
  have hxcol : xcol = fun r => fl_pivotedStoredQRMatrixSeq fp hmn A k r j := by
    funext r
    simp [xcol, pivotedStoredQRSwappedPanel,
      Wave13.columnPermuteMatrix, hfix]
  have hvprefix : ∀ r : Fin m, r.val < k → v r = 0 := by
    intro r hr
    exact pivotedStoredQRRawVector_zero_prefix fp hmn A k hk r hr
  have hsupport : ∀ r : Fin m, k ≤ r.val → xcol r = 0 := by
    intro r hr
    rw [hxcol]
    exact fl_pivotedStoredQRMatrixSeq_prefix_lower_zero fp hmn A k
      (Nat.le_of_lt hk) r j hj (lt_of_lt_of_le hj hr)
  have hpres := matMulVec_householder_eq_self_of_zero_prefix_support
    m k v xcol beta hvprefix hsupport
  simpa [pivotedStoredQRPseq, v, beta, xcol, hxcol] using hpres

/-- The exact reflector paired with an executed nonzero pivot stage annihilates
the displayed pivot-column tail.  This is the exact-zero fact needed to turn
the concrete stored-panel update into its explicit compact arithmetic budget;
it is derived from the same positive executed scale used by the Cox--Higham
transport argument. -/
theorem pivotedStoredQRPseq_pivot_column_zero_below (fp : FPModel)
    {m n : ℕ} (hmn : n ≤ m) (A : Fin m → Fin n → ℝ)
    (k : ℕ) (hk : k < n)
    (hsigma : 0 < |pivotedStoredQRSigma fp hmn A k|)
    (i : Fin m) (hi : k < i.val) :
    matMulVec m (pivotedStoredQRPseq fp hmn A k)
        (fun r => pivotedStoredQRSwappedPanel fp hmn A k r
          (pivotedQRActiveCol k hk)) i = 0 := by
  let row := pivotedQRActiveRow hmn k hk
  let col := pivotedQRActiveCol k hk
  let As := pivotedStoredQRSwappedPanel fp hmn A k
  let x : Fin m → ℝ := fun r => As r col
  let T := householderTrailingNorm2Sq m row x
  let alpha := signedHouseholderAlpha (Real.sqrt T) (x row)
  let v := householderTrailingActiveVector m row x alpha
  have hsigma_eq : pivotedStoredQRSigma fp hmn A k = Real.sqrt T := by
    simp [pivotedStoredQRSigma, hk, T, row, col, As, x,
      householderTrailingColumnNorm2Sq]
  have hsqrt_pos : 0 < Real.sqrt T := by
    rw [hsigma_eq, abs_of_nonneg (Real.sqrt_nonneg _)] at hsigma
    exact hsigma
  have hTpos : 0 < T := Real.sqrt_pos.mp hsqrt_pos
  have halpha : alpha * alpha = T := by
    simpa [alpha, T] using
      signedHouseholderAlpha_sqrt_trailingNorm2Sq_sq m row x
  have hsign : alpha * x row ≤ 0 := by
    simpa [alpha, T] using
      signedHouseholderAlpha_sqrt_trailingNorm2Sq_mul_pivot_nonpos m row x
  have hpivot_ne : x row ≠ alpha :=
    householder_pivot_ne_alpha_of_trailingNorm2Sq_pos_mul_nonpos
      m row x alpha halpha hTpos hsign
  have hden : (∑ r : Fin m, v r * v r) ≠ 0 := by
    simpa [v] using
      householderTrailingActiveVector_inner_self_ne_zero_of_pivot_ne_alpha
        m row x alpha hpivot_ne
  have hzero :=
    matMulVec_householder_trailingActiveVector_eq_zero_of_pivot_lt
      m row x alpha halpha hden i (by simpa [row] using hi)
  simpa [pivotedStoredQRPseq, pivotedStoredQRRawVector,
    pivotedStoredQRBeta, hk, row, col, As, x, T, alpha, v] using hzero

/-- The individual residual of an executed stage is exactly zero on completed
columns. -/
theorem pivotedStoredQREseq_completed_column_zero (fp : FPModel)
    {m n : ℕ} (hmn : n ≤ m) (A : Fin m → Fin n → ℝ)
    (k : ℕ) (i : Fin m) (j : Fin n) (hj : j.val < k) :
    pivotedStoredQREseq fp hmn A k i j = 0 := by
  by_cases hk : k < n
  · have hfix := pivotedStoredQRSwapSeq_fix_prefix fp hmn A k j hj
    have hnext :
        fl_pivotedStoredQRMatrixSeq fp hmn A (k + 1) i j =
          fl_pivotedStoredQRMatrixSeq fp hmn A k i j := by
      rw [show fl_pivotedStoredQRMatrixSeq fp hmn A (k + 1) i j =
          fl_householderStoredPanelStep fp m n k
            (pivotedStoredQRRawVector fp hmn A k)
            (pivotedStoredQRBeta fp hmn A k)
            (pivotedStoredQRSwappedPanel fp hmn A k) i j from
        congrFun (congrFun
          (fl_pivotedStoredQRMatrixSeq_succ_of_lt fp hmn A k hk) i) j]
      simp [fl_householderStoredPanelStep, hj, pivotedStoredQRSwappedPanel,
        Wave13.columnPermuteMatrix, hfix]
    have hpres := congrFun
      (pivotedStoredQRPseq_completed_column_preservation fp hmn A k hk j hj) i
    simp only [pivotedStoredQREseq, hnext]
    exact sub_eq_zero.mpr hpres.symm
  · have hkge : n ≤ k := Nat.le_of_not_gt hk
    have hnext := congrFun (congrFun
      (fl_pivotedStoredQRMatrixSeq_succ_of_ge fp hmn A k hkge) i) j
    have hP : pivotedStoredQRPseq fp hmn A k = idMatrix m := by
      have hv : pivotedStoredQRRawVector fp hmn A k = 0 := by
        simp [pivotedStoredQRRawVector, hk]
      ext a b
      simp [pivotedStoredQRPseq, pivotedStoredQRBeta, hv,
        householderBetaSpec, householder]
    have hAs : pivotedStoredQRSwappedPanel fp hmn A k =
        fl_pivotedStoredQRMatrixSeq fp hmn A k := by
      funext a b
      simp [pivotedStoredQRSwappedPanel, pivotedStoredQRSwapSeq, hk,
        Wave13.columnPermuteMatrix]
    rw [pivotedStoredQREseq, hnext, hP, hAs, matMulRect_id_left]
    ring

/-- The local compact-arithmetic budget attached to one column of the actual
pivoted stored-panel stage.  Completed columns carry zero budget because the
stored recursion and the exact reflector both preserve them. -/
noncomputable def pivotedStoredQRComponentBudget (fp : FPModel) {m n : ℕ}
    (hmn : n ≤ m) (A : Fin m → Fin n → ℝ)
    (k : ℕ) (i : Fin m) (j : Fin n) : ℝ :=
  if j.val < k then 0
  else
    householderCompactComponentBudget fp m
      (pivotedStoredQRRawVector fp hmn A k)
      (pivotedStoredQRBeta fp hmn A k)
      (fun r => pivotedStoredQRSwappedPanel fp hmn A k r j) i

/-- The residual of the actually executed matrix stage is bounded by the
repository's explicit compact Householder arithmetic budget.  Thus the local
`error_row` readiness field is not an abstract algorithmic residual premise:
it follows from a pointwise domination of this concrete nonnegative budget. -/
theorem pivotedStoredQREseq_abs_le_componentBudget (fp : FPModel)
    {m n : ℕ} (hmn : n ≤ m) (A : Fin m → Fin n → ℝ)
    (hm : gammaValid fp m) (k : ℕ) (hk : k < n)
    (hsigma : 0 < |pivotedStoredQRSigma fp hmn A k|)
    (i : Fin m) (j : Fin n) :
    |pivotedStoredQREseq fp hmn A k i j| ≤
      pivotedStoredQRComponentBudget fp hmn A k i j := by
  let v := pivotedStoredQRRawVector fp hmn A k
  let beta := pivotedStoredQRBeta fp hmn A k
  let As := pivotedStoredQRSwappedPanel fp hmn A k
  have hcompleted : j.val < k →
      ∀ r : Fin m,
        matMulVec m (householder m v beta) (fun a => As a j) r = As r j := by
    intro hj r
    have hpres := congrFun
      (pivotedStoredQRPseq_completed_column_preservation fp hmn A k hk j hj) r
    have hfix := pivotedStoredQRSwapSeq_fix_prefix fp hmn A k j hj
    simpa [pivotedStoredQRPseq, v, beta, As,
      pivotedStoredQRSwappedPanel, Wave13.columnPermuteMatrix, hfix] using hpres
  have hpivot : j.val = k →
      ∀ r : Fin m, k < r.val →
        matMulVec m (householder m v beta) (fun a => As a j) r = 0 := by
    intro hj r hr
    have hjfin : j = pivotedQRActiveCol k hk := Fin.ext hj
    subst j
    simpa [pivotedStoredQRPseq, v, beta, As] using
      pivotedStoredQRPseq_pivot_column_zero_below fp hmn A k hk hsigma r hr
  have hbound :=
    fl_householderStoredPanelStep_column_componentwise_error_bound
      fp m n k v beta As hm j hcompleted hpivot i
  simp only [pivotedStoredQREseq]
  rw [fl_pivotedStoredQRMatrixSeq_succ_of_lt fp hmn A k hk]
  simpa [pivotedStoredQREseq, pivotedStoredQRPseq,
    pivotedStoredQRComponentBudget, matMulRect, v, beta, As] using hbound

/-- Column-norm form of `pivotedStoredQREseq_abs_le_componentBudget`, obtained
from the concrete stored-panel forward-error theorem. -/
theorem pivotedStoredQREseq_norm_le_componentBudget (fp : FPModel)
    {m n : ℕ} (hmn : n ≤ m) (A : Fin m → Fin n → ℝ)
    (hm : gammaValid fp m) (k : ℕ) (hk : k < n)
    (hsigma : 0 < |pivotedStoredQRSigma fp hmn A k|)
    (j : Fin n) :
    vecNorm2 (fun i => pivotedStoredQREseq fp hmn A k i j) ≤
      vecNorm2 (fun i => pivotedStoredQRComponentBudget fp hmn A k i j) := by
  let v := pivotedStoredQRRawVector fp hmn A k
  let beta := pivotedStoredQRBeta fp hmn A k
  let As := pivotedStoredQRSwappedPanel fp hmn A k
  have hcompleted : j.val < k →
      ∀ r : Fin m,
        matMulVec m (householder m v beta) (fun a => As a j) r = As r j := by
    intro hj r
    have hpres := congrFun
      (pivotedStoredQRPseq_completed_column_preservation fp hmn A k hk j hj) r
    have hfix := pivotedStoredQRSwapSeq_fix_prefix fp hmn A k j hj
    simpa [pivotedStoredQRPseq, v, beta, As,
      pivotedStoredQRSwappedPanel, Wave13.columnPermuteMatrix, hfix] using hpres
  have hpivot : j.val = k →
      ∀ r : Fin m, k < r.val →
        matMulVec m (householder m v beta) (fun a => As a j) r = 0 := by
    intro hj r hr
    have hjfin : j = pivotedQRActiveCol k hk := Fin.ext hj
    subst j
    simpa [pivotedStoredQRPseq, v, beta, As] using
      pivotedStoredQRPseq_pivot_column_zero_below fp hmn A k hk hsigma r hr
  have hbound :=
    fl_householderStoredPanelStep_column_forward_error_bound
      fp m n k v beta As hm j hcompleted hpivot
  simp only [pivotedStoredQREseq]
  rw [fl_pivotedStoredQRMatrixSeq_succ_of_lt fp hmn A k hk]
  simpa [pivotedStoredQREseq, pivotedStoredQRPseq,
    pivotedStoredQRComponentBudget, matMulRect, v, beta, As] using hbound

/-- Transporting a zero completed-column residual through `Qacc` remains zero. -/
theorem pivotedStoredQR_QaccE_completed_column_zero (fp : FPModel)
    {m n : ℕ} (hmn : n ≤ m) (A : Fin m → Fin n → ℝ)
    (k : ℕ) (i : Fin m) (j : Fin n) (hj : j.val < k) :
    matMulRect m m n
        (Wave19.Qacc (pivotedStoredQRPseq fp hmn A) (k + 1))
        (pivotedStoredQREseq fp hmn A k) i j = 0 := by
  unfold matMulRect
  apply Finset.sum_eq_zero
  intro s _
  rw [pivotedStoredQREseq_completed_column_zero fp hmn A k s j hj]
  ring

/-- Honest per-stage obligations for the concrete raw-vector pivoted trace.

Every field concerns an individual executed residual or an executed raw
reflector.  In particular there is no norm bound on an accumulated recursive
perturbation.  `sigmaOrder` is the cross-stage Cox--Higham ordering invariant;
the local `q = k` case is already proved by
`pivotedStoredQRRawVector_sigma_sign_bound`, while controlling earlier stages
against a later computed pivot remains the genuine roundoff-ordering
obligation. -/
structure PivotedStoredQRRawReady (fp : FPModel) {m n : ℕ}
    (hmn : n ≤ m) (A : Fin m → Fin n → ℝ)
    (alpha : Fin m → ℝ) (gammaTilde : ℝ)
    (errorCoeff : ℕ → ℝ) : Prop where
  gamma_nonneg : 0 ≤ gammaTilde
  alpha_nonneg : ∀ i, 0 ≤ alpha i
  coeff_nonneg : ∀ k, k < n → 0 ≤ errorCoeff k
  sigma_pos : ∀ k, k < n → 0 < |pivotedStoredQRSigma fp hmn A k|
  vector_row : ∀ k, k < n → ∀ i,
    |pivotedStoredQRRawVector fp hmn A k i| ≤ 2 * alpha i
  error_row : ∀ k, k < n → ∀ i j,
    |pivotedStoredQREseq fp hmn A k i j| ≤ gammaTilde * alpha i
  error_norm : ∀ k, k < n → ∀ j,
    vecNorm2 (fun i => pivotedStoredQREseq fp hmn A k i j) ≤
      errorCoeff k * |pivotedStoredQRSigma fp hmn A k|
  sigmaOrder : ∀ k, k < n → ∀ q, q ≤ k →
    Real.sqrt 2 * |pivotedStoredQRSigma fp hmn A k| ≤
      vecNorm2 (pivotedStoredQRRawVector fp hmn A q)
  fold : ∀ k, k < n → errorCoeff k / Real.sqrt 2 ≤ gammaTilde

/-- All genuinely local numerical obligations for the actual stored matrix
recursion, stated against the explicit compact-operation budget.  Unlike
`PivotedStoredQRRawReady`, this interface contains neither a bundled residual
bound nor a cross-stage pivot-order field. -/
structure PivotedStoredQRLocalBudgetReady (fp : FPModel) {m n : ℕ}
    (hmn : n ≤ m) (A : Fin m → Fin n → ℝ)
    (alpha : Fin m → ℝ) (gammaTilde : ℝ)
    (errorCoeff : ℕ → ℝ) : Prop where
  gamma_nonneg : 0 ≤ gammaTilde
  alpha_nonneg : ∀ i, 0 ≤ alpha i
  coeff_nonneg : ∀ k, k < n → 0 ≤ errorCoeff k
  sigma_pos : ∀ k, k < n → 0 < |pivotedStoredQRSigma fp hmn A k|
  vector_row : ∀ k, k < n → ∀ i,
    |pivotedStoredQRRawVector fp hmn A k i| ≤ 2 * alpha i
  component_row : ∀ k, k < n → ∀ i j,
    pivotedStoredQRComponentBudget fp hmn A k i j ≤ gammaTilde * alpha i
  component_norm : ∀ k, k < n → ∀ j,
    vecNorm2 (fun i => pivotedStoredQRComponentBudget fp hmn A k i j) ≤
      errorCoeff k * |pivotedStoredQRSigma fp hmn A k|
  fold : ∀ k, k < n → errorCoeff k / Real.sqrt 2 ≤ gammaTilde

/-- The strict-history part of the Cox--Higham executed-pivot ordering.  The
missing reflexive case is a theorem of the actual signed-vector construction,
so this predicate exposes exactly the remaining `q < k` obligation. -/
def PivotedStoredQRSigmaHistoryOrdered (fp : FPModel) {m n : ℕ}
    (hmn : n ≤ m) (A : Fin m → Fin n → ℝ) : Prop :=
  ∀ k, k < n → ∀ q, q < k →
    Real.sqrt 2 * |pivotedStoredQRSigma fp hmn A k| ≤
      vecNorm2 (pivotedStoredQRRawVector fp hmn A q)

/-! ### Bare-model obstruction for strict pivot-scale history

Cox--Higham's strict pivot-scale history is valid for the exact-reflector
stage sequence used in their analysis.  It is not valid for a recursion that
feeds each rounded compact-update residual back into the next pivot selection.
The following two-by-two execution is an explicit `FPModel` counterexample.
Every operation is exact except subtraction, which takes the allowed relative
error `1/4`.  The first pivot scale is `1`; rounding raises the only remaining
tail to `9/8`, so the strict `q < k` history fails. -/

/-- A legal model whose subtractions attain relative error `1/4`. -/
noncomputable def subInflatedQuarterFPModel : FPModel where
  u := (1 : ℝ) / 4
  u_nonneg := by norm_num
  fl_add := fun x y => x + y
  fl_sub := fun x y => (x - y) * (5 / 4 : ℝ)
  fl_mul := fun x y => x * y
  fl_div := fun x y => x / y
  fl_sqrt := fun x => Real.sqrt x
  fl_add_zero := by intro x; ring
  model_add := by
    intro x y
    exact ⟨0, by norm_num, by ring⟩
  model_sub := by
    intro x y
    exact ⟨(1 : ℝ) / 4, by norm_num, by ring⟩
  model_mul := by
    intro x y
    exact ⟨0, by norm_num, by ring⟩
  model_div := by
    intro x y _hy
    exact ⟨0, by norm_num, by ring⟩
  model_sqrt := by
    intro x _hx
    exact ⟨0, by norm_num, by ring⟩

/-- Two columns of norms `1` and `9/10`; the first active column is the unique
maximizer and has the raw signed vector `(1,1)`. -/
noncomputable def sigmaCounterA : Fin 2 → Fin 2 → ℝ
  | ⟨0, _⟩, ⟨0, _⟩ => 0
  | ⟨1, _⟩, ⟨0, _⟩ => 1
  | ⟨0, _⟩, ⟨1, _⟩ => 9 / 10
  | ⟨1, _⟩, ⟨1, _⟩ => 0

theorem sigmaCounter_pivot0 :
    householderActiveMaxPivotColumn (0 : Fin 2) (0 : Fin 2) sigmaCounterA = 0 := by
  let q := householderActiveMaxPivotColumn (0 : Fin 2) (0 : Fin 2) sigmaCounterA
  have hmax := householderActiveMaxPivotColumn_pivot_max
    (0 : Fin 2) (0 : Fin 2) sigmaCounterA (0 : Fin 2) (by norm_num)
  change q = 0
  have hqv : q.val = 0 := by
    by_contra hne
    have hq1 : q.val = 1 := by omega
    have hqeq : q = (1 : Fin 2) := Fin.ext hq1
    change householderTrailingColumnNorm2Sq (0 : Fin 2) sigmaCounterA 0 ≤
      householderTrailingColumnNorm2Sq (0 : Fin 2) sigmaCounterA q at hmax
    rw [hqeq] at hmax
    norm_num [householderTrailingColumnNorm2Sq,
      householderTrailingNorm2Sq, sigmaCounterA,
      householderTrailingPart, vecNorm2Sq] at hmax
  exact Fin.ext hqv

theorem sigmaCounter_swap0 :
    pivotedStoredQRSwappedPanel subInflatedQuarterFPModel (m := 2) (n := 2)
      (by omega) sigmaCounterA 0 = sigmaCounterA := by
  funext i j
  simp [pivotedStoredQRSwappedPanel, pivotedStoredQRSwapSeq,
    fl_pivotedStoredQRMatrixSeq, pivotedQRActiveRow, pivotedQRActiveCol,
    sigmaCounter_pivot0, Wave13.columnPermuteMatrix]

theorem sigmaCounter_A1_11 :
    fl_pivotedStoredQRMatrixSeq subInflatedQuarterFPModel (m := 2) (n := 2)
      (by omega) sigmaCounterA 1 (1 : Fin 2) (1 : Fin 2) = -(9 / 8 : ℝ) := by
  rw [fl_pivotedStoredQRMatrixSeq_succ_of_lt subInflatedQuarterFPModel
    (m := 2) (n := 2) (by omega) sigmaCounterA 0 (by omega)]
  have hswap :
      pivotedStoredQRSwappedPanel subInflatedQuarterFPModel (m := 2) (n := 2)
        (by omega) sigmaCounterA 0 = sigmaCounterA := sigmaCounter_swap0
  have hv :
      pivotedStoredQRRawVector subInflatedQuarterFPModel (m := 2) (n := 2)
        (by omega) sigmaCounterA 0 = fun _ => (1 : ℝ) := by
    funext i
    fin_cases i <;>
      norm_num [pivotedStoredQRRawVector, pivotedQRActiveRow,
        pivotedQRActiveCol, hswap, householderTrailingActiveVector,
        householderActiveVector, householderTrailingPart,
        householderTrailingNorm2Sq, vecNorm2Sq, Fin.sum_univ_two,
        signedHouseholderAlpha, sigmaCounterA]
  have hbeta :
      pivotedStoredQRBeta subInflatedQuarterFPModel (m := 2) (n := 2)
        (by omega) sigmaCounterA 0 = 1 := by
    norm_num [pivotedStoredQRBeta, hv, householderBetaSpec, Fin.sum_univ_two]
  rw [hv, hbeta, hswap]
  norm_num [fl_householderStoredPanelStep,
    fl_householderApplyCompactPanel, fl_householderApplyCompact,
    fl_dotProduct, Fin.foldl_succ, sigmaCounterA,
    subInflatedQuarterFPModel]

theorem sigmaCounter_rawVector0 :
    pivotedStoredQRRawVector subInflatedQuarterFPModel (m := 2) (n := 2)
      (by omega) sigmaCounterA 0 = fun _ => (1 : ℝ) := by
  funext i
  fin_cases i <;>
    norm_num [pivotedStoredQRRawVector, pivotedQRActiveRow,
      pivotedQRActiveCol, sigmaCounter_swap0,
      householderTrailingActiveVector, householderActiveVector,
      householderTrailingPart, householderTrailingNorm2Sq, vecNorm2Sq,
      Fin.sum_univ_two, signedHouseholderAlpha, sigmaCounterA]

theorem sigmaCounter_sigma0 :
    pivotedStoredQRSigma subInflatedQuarterFPModel (m := 2) (n := 2)
      (by omega) sigmaCounterA 0 = 1 := by
  norm_num [pivotedStoredQRSigma, pivotedQRActiveRow, pivotedQRActiveCol,
    sigmaCounter_swap0, householderTrailingColumnNorm2Sq,
    householderTrailingNorm2Sq, householderTrailingPart,
    vecNorm2Sq, Fin.sum_univ_two, sigmaCounterA]

theorem sigmaCounter_pivot1 :
    householderActiveMaxPivotColumn (1 : Fin 2) (1 : Fin 2)
      (fl_pivotedStoredQRMatrixSeq subInflatedQuarterFPModel
        (by omega) sigmaCounterA 1) = 1 := by
  apply Fin.ext
  have hge := householderActiveMaxPivotColumn_ge
    (1 : Fin 2) (1 : Fin 2)
    (fl_pivotedStoredQRMatrixSeq subInflatedQuarterFPModel
      (by omega) sigmaCounterA 1)
  omega

theorem sigmaCounter_swap1_11 :
    pivotedStoredQRSwappedPanel subInflatedQuarterFPModel (m := 2) (n := 2)
      (by omega) sigmaCounterA 1 (1 : Fin 2) (1 : Fin 2) = -(9 / 8 : ℝ) := by
  simp [pivotedStoredQRSwappedPanel, pivotedStoredQRSwapSeq,
    pivotedQRActiveRow, pivotedQRActiveCol, sigmaCounter_pivot1,
    Wave13.columnPermuteMatrix, sigmaCounter_A1_11]

theorem sigmaCounter_sigma1 :
    pivotedStoredQRSigma subInflatedQuarterFPModel (m := 2) (n := 2)
      (by omega) sigmaCounterA 1 = 9 / 8 := by
  norm_num [pivotedStoredQRSigma, pivotedQRActiveRow, pivotedQRActiveCol,
    householderTrailingColumnNorm2Sq, householderTrailingNorm2Sq,
    householderTrailingPart, vecNorm2Sq, Fin.sum_univ_two,
    sigmaCounter_swap1_11]
  have h81 : Real.sqrt (81 : ℝ) = 9 := by
    nlinarith [Real.sq_sqrt (by norm_num : (0 : ℝ) ≤ 81),
      Real.sqrt_nonneg (81 : ℝ)]
  have h64 : Real.sqrt (64 : ℝ) = 8 := by
    nlinarith [Real.sq_sqrt (by norm_num : (0 : ℝ) ≤ 64),
      Real.sqrt_nonneg (64 : ℝ)]
  rw [h81, h64]

theorem sigmaCounter_rawVector0_norm :
    vecNorm2
        (pivotedStoredQRRawVector subInflatedQuarterFPModel (m := 2) (n := 2)
          (by omega) sigmaCounterA 0) = Real.sqrt 2 := by
  rw [sigmaCounter_rawVector0]
  simp [vecNorm2, vecNorm2Sq]

/-- The strict history demanded by the legacy readiness interface is false for
the literal rounded trace under the bare `FPModel`. -/
theorem sigmaHistory_not_forall_literal_rounded_trace :
    ¬ PivotedStoredQRSigmaHistoryOrdered subInflatedQuarterFPModel
      (m := 2) (n := 2) (by omega) sigmaCounterA := by
  intro h
  have h10 := h 1 (by omega) 0 (by omega)
  rw [sigmaCounter_sigma1, sigmaCounter_rawVector0_norm] at h10
  norm_num [abs_of_nonneg] at h10

/-! ### Printed row-scale obstruction for the no-row-swap trace

The selected theorem is a row-pivoted analysis.  The literal recursion above
performs column exchanges but no common source-row permutation.  Consequently
even its raw-vector bound cannot be charged to the initial maximum of the same
source row: a zero first source row can become the active pivot row. -/

noncomputable def rowScaleCounterA : Fin 2 → Fin 2 → ℝ
  | ⟨0, _⟩, _ => 0
  | ⟨1, _⟩, ⟨0, _⟩ => 1
  | ⟨1, _⟩, ⟨1, _⟩ => 1 / 2

theorem rowScaleCounter_pivot0 :
    householderActiveMaxPivotColumn (0 : Fin 2) (0 : Fin 2)
      rowScaleCounterA = 0 := by
  let q := householderActiveMaxPivotColumn (0 : Fin 2) (0 : Fin 2)
    rowScaleCounterA
  have hmax := householderActiveMaxPivotColumn_pivot_max
    (0 : Fin 2) (0 : Fin 2) rowScaleCounterA (0 : Fin 2) (by norm_num)
  change q = 0
  have hqv : q.val = 0 := by
    by_contra hne
    have hq1 : q.val = 1 := by omega
    have hqeq : q = (1 : Fin 2) := Fin.ext hq1
    change householderTrailingColumnNorm2Sq (0 : Fin 2) rowScaleCounterA 0 ≤
      householderTrailingColumnNorm2Sq (0 : Fin 2) rowScaleCounterA q at hmax
    rw [hqeq] at hmax
    norm_num [householderTrailingColumnNorm2Sq,
      householderTrailingNorm2Sq, rowScaleCounterA,
      householderTrailingPart, vecNorm2Sq] at hmax
  exact Fin.ext hqv

theorem rowScaleCounter_swap0 :
    pivotedStoredQRSwappedPanel
      (FPModel.exactWithUnitRoundoff 0 (by norm_num)) (m := 2) (n := 2)
      (by omega) rowScaleCounterA 0 = rowScaleCounterA := by
  funext i j
  simp [pivotedStoredQRSwappedPanel, pivotedStoredQRSwapSeq,
    fl_pivotedStoredQRMatrixSeq, pivotedQRActiveRow, pivotedQRActiveCol,
    rowScaleCounter_pivot0, Wave13.columnPermuteMatrix]

theorem rowScaleCounter_rawVector0 :
    pivotedStoredQRRawVector
      (FPModel.exactWithUnitRoundoff 0 (by norm_num)) (m := 2) (n := 2)
      (by omega) rowScaleCounterA 0 = fun _ => (1 : ℝ) := by
  funext i
  fin_cases i <;>
    norm_num [pivotedStoredQRRawVector, pivotedQRActiveRow,
      pivotedQRActiveCol, rowScaleCounter_swap0,
      householderTrailingActiveVector, householderActiveVector,
      householderTrailingPart, householderTrailingNorm2Sq, vecNorm2Sq,
      Fin.sum_univ_two, signedHouseholderAlpha, rowScaleCounterA]

/-- Literal source row maximum for the two-column counterexample. -/
noncomputable def rowScaleCounterRowMax (i : Fin 2) : ℝ :=
  max |rowScaleCounterA i (0 : Fin 2)| |rowScaleCounterA i (1 : Fin 2)|

theorem rowScaleCounter_rowMax0 :
    rowScaleCounterRowMax (0 : Fin 2) = 0 := by
  simp [rowScaleCounterRowMax, rowScaleCounterA]

/-- No multiple of the printed initial source-row scale can instantiate even
the raw-vector field of `PivotedStoredQRLocalBudgetReady` for the literal
no-row-swap trace.  This obstruction already occurs in exact arithmetic. -/
theorem localBudgetReady_not_forall_printed_source_row_scale :
    ¬ ∀ (C gammaTilde : ℝ) (errorCoeff : ℕ → ℝ),
      PivotedStoredQRLocalBudgetReady
        (FPModel.exactWithUnitRoundoff 0 (by norm_num)) (m := 2) (n := 2)
        (by omega) rowScaleCounterA
        (fun i => C * rowScaleCounterRowMax i)
        gammaTilde errorCoeff := by
  intro h
  have ready := h 1 0 (fun _ => 0)
  have hv := ready.vector_row 0 (by omega) (0 : Fin 2)
  rw [rowScaleCounter_rawVector0, rowScaleCounter_rowMax0] at hv
  norm_num at hv

/-- Local compact-operation budgets plus strict cross-stage ordering produce
the legacy per-residual interface.  The residual inequalities themselves are
derived here from the literal stored-panel recursion. -/
theorem PivotedStoredQRLocalBudgetReady.toRawReady
    (fp : FPModel) {m n : ℕ} (hmn : n ≤ m)
    (A : Fin m → Fin n → ℝ) (alpha : Fin m → ℝ)
    (gammaTilde : ℝ) (errorCoeff : ℕ → ℝ)
    (hm : gammaValid fp m)
    (ready : PivotedStoredQRLocalBudgetReady fp hmn A alpha gammaTilde errorCoeff)
    (history : PivotedStoredQRSigmaHistoryOrdered fp hmn A) :
    PivotedStoredQRRawReady fp hmn A alpha gammaTilde errorCoeff := by
  refine
    { gamma_nonneg := ready.gamma_nonneg
      alpha_nonneg := ready.alpha_nonneg
      coeff_nonneg := ready.coeff_nonneg
      sigma_pos := ready.sigma_pos
      vector_row := ready.vector_row
      error_row := ?_
      error_norm := ?_
      sigmaOrder := ?_
      fold := ready.fold }
  · intro k hk i j
    exact (pivotedStoredQREseq_abs_le_componentBudget
      fp hmn A hm k hk (ready.sigma_pos k hk) i j).trans
        (ready.component_row k hk i j)
  · intro k hk j
    exact (pivotedStoredQREseq_norm_le_componentBudget
      fp hmn A hm k hk (ready.sigma_pos k hk) j).trans
        (ready.component_norm k hk j)
  · intro k hk q hq
    rcases lt_or_eq_of_le hq with hlt | heq
    · exact history k hk q hlt
    · subst q
      exact pivotedStoredQRRawVector_sigma_sign_bound fp hmn A k hk

/-- Cox--Higham per-stage transported-error bound for the actual executed
pivoted trace. -/
theorem pivotedStoredQR_stageImage_entrywise_le
    (fp : FPModel) {m n : ℕ} (hmn : n ≤ m)
    (A : Fin m → Fin n → ℝ) (alpha : Fin m → ℝ)
    (gammaTilde : ℝ) (errorCoeff : ℕ → ℝ)
    (ready : PivotedStoredQRRawReady fp hmn A alpha gammaTilde errorCoeff)
    (k : ℕ) (i : Fin m) (j : Fin n) :
    |matMulRect m m n
        (Wave19.Qacc (pivotedStoredQRPseq fp hmn A) (k + 1))
        (pivotedStoredQREseq fp hmn A k) i j| ≤
      (1 + 4 * ((k : ℝ) + 1)) * gammaTilde * alpha i := by
  by_cases hk : k < n
  · apply qacc_rawHouseholder_stageImage_entrywise_le_of_sigma_ordering
      (fun q => pivotedStoredQRRawVector fp hmn A q)
      (fun q => pivotedStoredQRBeta fp hmn A q)
      (pivotedStoredQREseq fp hmn A k) alpha
      (pivotedStoredQRSigma fp hmn A k) (errorCoeff k) 0 gammaTilde
      k i j ready.gamma_nonneg ready.alpha_nonneg
      (fun q => pivotedStoredQRPseq_orthogonal fp hmn A q)
    · intro q hq
      have hqle : q ≤ k := by omega
      have hlower := ready.sigmaOrder k hk q hqle
      have hpos : 0 < Real.sqrt 2 *
          |pivotedStoredQRSigma fp hmn A k| :=
        mul_pos (Real.sqrt_pos.mpr (by norm_num)) (ready.sigma_pos k hk)
      linarith
    · intro q hq
      apply householderBetaSpec_mul_vecNorm2_sq_eq_two_of_pos
      have hqle : q ≤ k := by omega
      have hlower := ready.sigmaOrder k hk q hqle
      have hpos : 0 < Real.sqrt 2 *
          |pivotedStoredQRSigma fp hmn A k| :=
        mul_pos (Real.sqrt_pos.mpr (by norm_num)) (ready.sigma_pos k hk)
      linarith
    · intro q hq r
      exact ready.vector_row q (by omega) r
    · exact ready.sigma_pos k hk
    · simpa using ready.coeff_nonneg k hk
    · simpa using ready.error_norm k hk j
    · intro q hq
      exact ready.sigmaOrder k hk q (by omega)
    · simpa using ready.fold k hk
    · exact ready.error_row k hk i j
  · have hkge : n ≤ k := Nat.le_of_not_gt hk
    have hjk : j.val < k := lt_of_lt_of_le j.isLt hkge
    rw [pivotedStoredQR_QaccE_completed_column_zero fp hmn A k i j hjk,
      abs_zero]
    exact mul_nonneg
      (mul_nonneg (by positivity) ready.gamma_nonneg) (ready.alpha_nonneg i)

/-! ## Actual-recursion QR endpoint -/

/-- Backward factorization delivered by the actually executed active-max,
stored-panel recursion.

The permutation, orthogonal factor, triangular factor, and perturbation in this
statement are definitions of the concrete trace above, not independently
postulated witnesses.  The only numerical hypotheses are the individual-stage
raw-vector obligations collected in `PivotedStoredQRRawReady`. -/
theorem fl_pivotedStoredQR_actual_rowwise_backward_error
    (fp : FPModel) {m n : ℕ} (hmn : n ≤ m)
    (A : Fin m → Fin n → ℝ) (alpha : Fin m → ℝ)
    (gammaTilde : ℝ) (errorCoeff : ℕ → ℝ)
    (ready : PivotedStoredQRRawReady fp hmn A alpha gammaTilde errorCoeff) :
    let Pseq := pivotedStoredQRPseq fp hmn A
    let Sseq := pivotedStoredQRSwapSeq fp hmn A
    let Eseq := pivotedStoredQREseq fp hmn A
    let Q := Wave19.Qacc Pseq n
    let R := fl_pivotedStoredQRMatrixSeq fp hmn A n
    let pi := pivotPermAcc Sseq n
    let dA := pivotDAacc Pseq Sseq Eseq n
    IsOrthogonal m Q ∧
      IsUpperTrapezoidal m n R ∧
      (∀ i j,
        R i j = matMulRect m m n (matTranspose Q)
          (fun a b => Wave13.columnPermuteMatrix A pi a b + dA a b) i j) ∧
      (∀ i j,
        Wave13.columnPermuteMatrix A pi i j + dA i j =
          matMulRect m m n Q R i j) ∧
      ∀ i j,
        |dA i j| ≤ ((j.val : ℝ) + 1) ^ 2 *
          (5 * gammaTilde) * alpha i := by
  dsimp only
  let Pseq := pivotedStoredQRPseq fp hmn A
  let Sseq := pivotedStoredQRSwapSeq fp hmn A
  let Eseq := pivotedStoredQREseq fp hmn A
  let Q := Wave19.Qacc Pseq n
  let R := fl_pivotedStoredQRMatrixSeq fp hmn A n
  let pi := pivotPermAcc Sseq n
  let dA := pivotDAacc Pseq Sseq Eseq n
  let B : Fin m → Fin n → ℝ := fun i j =>
    Wave13.columnPermuteMatrix A pi i j + dA i j
  have hP : ∀ k, IsOrthogonal m (Pseq k) := by
    intro k
    exact pivotedStoredQRPseq_orthogonal fp hmn A k
  have hQ : IsOrthogonal m Q := by
    exact Wave19.Qacc_orthogonal Pseq hP n
  have hR : IsUpperTrapezoidal m n R := by
    exact fl_pivotedStoredQRMatrixSeq_upperTrapezoidal fp hmn A
  have hTel : ∀ i j, R i j =
      matMulRect m m n (matTranspose Q) B i j := by
    intro i j
    simpa [Pseq, Sseq, Eseq, Q, R, pi, dA, B,
      fl_pivotedStoredQRMatrixSeq] using
      pivoted_entrywise_residual_telescope n
        (fl_pivotedStoredQRMatrixSeq fp hmn A) Pseq Sseq Eseq hP
        (fun k _hk i j => pivotedStoredQR_step_with_residual fp hmn A k i j)
        i j
  have hTelEq : R = matMulRect m m n (matTranspose Q) B :=
    funext fun i => funext fun j => hTel i j
  have hQQT : matMul m Q (matTranspose Q) = idMatrix m :=
    funext fun i => funext fun j => hQ.right_inv i j
  have hReconstructEq : matMulRect m m n Q R = B := by
    rw [hTelEq, ← matMulRect_assoc_square_left, hQQT,
      matMulRect_id_left]
  have hBound : ∀ i j,
      |dA i j| ≤ ((j.val : ℝ) + 1) ^ 2 *
        (5 * gammaTilde) * alpha i := by
    intro i j
    exact pivotDAacc_coxHigham_rowwise_bound Pseq Sseq Eseq alpha
      gammaTilde ready.gamma_nonneg ready.alpha_nonneg
      (fun k j hj => pivotedStoredQRSwapSeq_fix_prefix fp hmn A k j hj)
      (fun k j hj => pivotedStoredQRSwapSeq_maps_active fp hmn A k j hj)
      (fun k i j hj =>
        pivotedStoredQR_QaccE_completed_column_zero fp hmn A k i j hj)
      (fun k i j =>
        pivotedStoredQR_stageImage_entrywise_le fp hmn A alpha gammaTilde
          errorCoeff ready k i j)
      i j
  refine ⟨hQ, hR, ?_, ?_, hBound⟩
  · intro i j
    simpa [B] using hTel i j
  · intro i j
    exact (congrFun (congrFun hReconstructEq i) j).symm

/-! ## The paired, actually executed right-hand-side transform -/

/-- Rounded right-hand-side sequence driven by exactly the raw vectors and
beta values selected by `fl_pivotedStoredQRMatrixSeq`.  Column swaps act only
on the matrix; the right-hand side follows the common row reflectors. -/
noncomputable def fl_pivotedStoredQRRhsSeq (fp : FPModel) {m n : ℕ}
    (hmn : n ≤ m) (A : Fin m → Fin n → ℝ) (b : Fin m → ℝ) :
    ℕ → Fin m → ℝ
  | 0 => b
  | k + 1 =>
      if _hk : k < n then
        fl_householderStoredRhsStep fp m k
          (pivotedStoredQRRawVector fp hmn A k)
          (pivotedStoredQRBeta fp hmn A k)
          (fl_pivotedStoredQRRhsSeq fp hmn A b k)
      else
        fl_pivotedStoredQRRhsSeq fp hmn A b k

@[simp] theorem fl_pivotedStoredQRRhsSeq_zero (fp : FPModel) {m n : ℕ}
    (hmn : n ≤ m) (A : Fin m → Fin n → ℝ) (b : Fin m → ℝ) :
    fl_pivotedStoredQRRhsSeq fp hmn A b 0 = b := rfl

/-- The concrete RHS recurrence before the QR horizon. -/
theorem fl_pivotedStoredQRRhsSeq_succ_of_lt (fp : FPModel) {m n : ℕ}
    (hmn : n ≤ m) (A : Fin m → Fin n → ℝ) (b : Fin m → ℝ)
    (k : ℕ) (hk : k < n) :
    fl_pivotedStoredQRRhsSeq fp hmn A b (k + 1) =
      fl_householderStoredRhsStep fp m k
        (pivotedStoredQRRawVector fp hmn A k)
        (pivotedStoredQRBeta fp hmn A k)
        (fl_pivotedStoredQRRhsSeq fp hmn A b k) := by
  simp [fl_pivotedStoredQRRhsSeq, hk]

/-- The RHS trace is held fixed after the QR horizon. -/
theorem fl_pivotedStoredQRRhsSeq_succ_of_ge (fp : FPModel) {m n : ℕ}
    (hmn : n ≤ m) (A : Fin m → Fin n → ℝ) (b : Fin m → ℝ)
    (k : ℕ) (hk : n ≤ k) :
    fl_pivotedStoredQRRhsSeq fp hmn A b (k + 1) =
      fl_pivotedStoredQRRhsSeq fp hmn A b k := by
  simp [fl_pivotedStoredQRRhsSeq, Nat.not_lt.mpr hk]

/-- Individual residual of one actually executed RHS transformation. -/
noncomputable def pivotedStoredQRRhsEseq (fp : FPModel) {m n : ℕ}
    (hmn : n ≤ m) (A : Fin m → Fin n → ℝ) (b : Fin m → ℝ)
    (k : ℕ) : Fin m → ℝ :=
  fun i =>
    fl_pivotedStoredQRRhsSeq fp hmn A b (k + 1) i -
      matMulVec m (pivotedStoredQRPseq fp hmn A k)
        (fl_pivotedStoredQRRhsSeq fp hmn A b k) i

/-- The named RHS residual gives the exact same-reflector recurrence. -/
theorem pivotedStoredQRRhs_step_with_residual (fp : FPModel) {m n : ℕ}
    (hmn : n ≤ m) (A : Fin m → Fin n → ℝ) (b : Fin m → ℝ)
    (k : ℕ) (i : Fin m) :
    fl_pivotedStoredQRRhsSeq fp hmn A b (k + 1) i =
      matMulVec m (pivotedStoredQRPseq fp hmn A k)
          (fl_pivotedStoredQRRhsSeq fp hmn A b k) i +
        pivotedStoredQRRhsEseq fp hmn A b k i := by
  simp only [pivotedStoredQRRhsEseq]
  ring

/-- One-column encoding used to reuse the checked rectangular telescope for
the paired RHS vector. -/
noncomputable def pivotedStoredQRRhsMatrixSeq (fp : FPModel) {m n : ℕ}
    (hmn : n ≤ m) (A : Fin m → Fin n → ℝ) (b : Fin m → ℝ)
    (k : ℕ) : Fin m → Fin 1 → ℝ :=
  fun i _ => fl_pivotedStoredQRRhsSeq fp hmn A b k i

/-- One-column encoding of the individual RHS residual. -/
noncomputable def pivotedStoredQRRhsEMatrixSeq (fp : FPModel) {m n : ℕ}
    (hmn : n ≤ m) (A : Fin m → Fin n → ℝ) (b : Fin m → ℝ)
    (k : ℕ) : Fin m → Fin 1 → ℝ :=
  fun i _ => pivotedStoredQRRhsEseq fp hmn A b k i

/-- Accumulated source-side RHS perturbation for the actual trace. -/
noncomputable def pivotedStoredQRRhsDelta (fp : FPModel) {m n : ℕ}
    (hmn : n ≤ m) (A : Fin m → Fin n → ℝ) (b : Fin m → ℝ) :
    Fin m → ℝ :=
  fun i => Wave19.DAacc (pivotedStoredQRPseq fp hmn A)
    (pivotedStoredQRRhsEMatrixSeq fp hmn A b) n i 0

/-- Exact RHS telescope for the actually executed common-reflector trace. -/
theorem pivotedStoredQRRhs_telescope (fp : FPModel) {m n : ℕ}
    (hmn : n ≤ m) (A : Fin m → Fin n → ℝ) (b : Fin m → ℝ)
    (i : Fin m) :
    fl_pivotedStoredQRRhsSeq fp hmn A b n i =
      matMulVec m
        (matTranspose
          (Wave19.Qacc (pivotedStoredQRPseq fp hmn A) n))
        (fun a => b a + pivotedStoredQRRhsDelta fp hmn A b a) i := by
  have h := Wave19.entrywise_residual_telescope n
    (pivotedStoredQRRhsMatrixSeq fp hmn A b)
    (pivotedStoredQRPseq fp hmn A)
    (pivotedStoredQRRhsEMatrixSeq fp hmn A b)
    (fun k => pivotedStoredQRPseq_orthogonal fp hmn A k)
    (fun k _hk r _j => by
      simpa [pivotedStoredQRRhsMatrixSeq,
        pivotedStoredQRRhsEMatrixSeq, matMulRect, matMulVec] using
        pivotedStoredQRRhs_step_with_residual fp hmn A b k r)
    i (0 : Fin 1)
  simpa [pivotedStoredQRRhsMatrixSeq, pivotedStoredQRRhsDelta,
    matMulRect, matMulVec] using h

/-- Local, individual-stage obligations for the paired RHS transform.  The
cross-stage scale information is shared with the matrix-side readiness object;
it is not duplicated as an accumulated RHS-error premise. -/
structure PivotedStoredQRRhsRawReady (fp : FPModel) {m n : ℕ}
    (hmn : n ≤ m) (A : Fin m → Fin n → ℝ) (b : Fin m → ℝ)
    (rho : Fin m → ℝ) (gammaTilde : ℝ)
    (errorCoeff : ℕ → ℝ) : Prop where
  rho_nonneg : ∀ i, 0 ≤ rho i
  coeff_nonneg : ∀ k, k < n → 0 ≤ errorCoeff k
  vector_row : ∀ k, k < n → ∀ i,
    |pivotedStoredQRRawVector fp hmn A k i| ≤ 2 * rho i
  error_row : ∀ k, k < n → ∀ i,
    |pivotedStoredQRRhsEseq fp hmn A b k i| ≤ gammaTilde * rho i
  error_norm : ∀ k, k < n →
    vecNorm2 (pivotedStoredQRRhsEseq fp hmn A b k) ≤
      errorCoeff k * |pivotedStoredQRSigma fp hmn A k|
  fold : ∀ k, k < n → errorCoeff k / Real.sqrt 2 ≤ gammaTilde

/-- Per-stage transported RHS error, using the same raw-reflector expansion as
the matrix columns. -/
theorem pivotedStoredQRRhs_stageImage_entrywise_le
    (fp : FPModel) {m n : ℕ} (hmn : n ≤ m)
    (A : Fin m → Fin n → ℝ) (b : Fin m → ℝ)
    (alpha rho : Fin m → ℝ) (gammaTilde : ℝ)
    (matrixErrorCoeff rhsErrorCoeff : ℕ → ℝ)
    (matrixReady :
      PivotedStoredQRRawReady fp hmn A alpha gammaTilde matrixErrorCoeff)
    (rhsReady :
      PivotedStoredQRRhsRawReady fp hmn A b rho gammaTilde rhsErrorCoeff)
    (k : ℕ) (hk : k < n) (i : Fin m) :
    |matMulVec m
        (Wave19.Qacc (pivotedStoredQRPseq fp hmn A) (k + 1))
        (pivotedStoredQRRhsEseq fp hmn A b k) i| ≤
      (1 + 4 * ((k : ℝ) + 1)) * gammaTilde * rho i := by
  simpa [matMulRect, matMulVec] using
    (qacc_rawHouseholder_stageImage_entrywise_le_of_sigma_ordering
      (fun q => pivotedStoredQRRawVector fp hmn A q)
      (fun q => pivotedStoredQRBeta fp hmn A q)
      (pivotedStoredQRRhsEMatrixSeq fp hmn A b k) rho
      (pivotedStoredQRSigma fp hmn A k) (rhsErrorCoeff k) 0 gammaTilde
      k i (0 : Fin 1) matrixReady.gamma_nonneg rhsReady.rho_nonneg
      (fun q => pivotedStoredQRPseq_orthogonal fp hmn A q)
      (fun q hq => by
        have hqle : q ≤ k := by omega
        have hlower := matrixReady.sigmaOrder k hk q hqle
        have hpos : 0 < Real.sqrt 2 *
            |pivotedStoredQRSigma fp hmn A k| :=
          mul_pos (Real.sqrt_pos.mpr (by norm_num))
            (matrixReady.sigma_pos k hk)
        linarith)
      (fun q hq => by
        apply householderBetaSpec_mul_vecNorm2_sq_eq_two_of_pos
        have hqle : q ≤ k := by omega
        have hlower := matrixReady.sigmaOrder k hk q hqle
        have hpos : 0 < Real.sqrt 2 *
            |pivotedStoredQRSigma fp hmn A k| :=
          mul_pos (Real.sqrt_pos.mpr (by norm_num))
            (matrixReady.sigma_pos k hk)
        linarith)
      (fun q hq r => rhsReady.vector_row q (by omega) r)
      (matrixReady.sigma_pos k hk)
      (by simpa using rhsReady.coeff_nonneg k hk)
      (by simpa [pivotedStoredQRRhsEMatrixSeq] using
        rhsReady.error_norm k hk)
      (fun q hq => matrixReady.sigmaOrder k hk q (by omega))
      (by simpa using rhsReady.fold k hk)
      (by simpa [pivotedStoredQRRhsEMatrixSeq] using
        rhsReady.error_row k hk i))

/-- Printed final RHS envelope for the actual common-reflector trace. -/
theorem pivotedStoredQRRhsDelta_rowwise_bound
    (fp : FPModel) {m n : ℕ} (hmn : n ≤ m)
    (A : Fin m → Fin n → ℝ) (b : Fin m → ℝ)
    (alpha rho : Fin m → ℝ) (gammaTilde : ℝ)
    (matrixErrorCoeff rhsErrorCoeff : ℕ → ℝ)
    (matrixReady :
      PivotedStoredQRRawReady fp hmn A alpha gammaTilde matrixErrorCoeff)
    (rhsReady :
      PivotedStoredQRRhsRawReady fp hmn A b rho gammaTilde rhsErrorCoeff)
    (i : Fin m) :
    |pivotedStoredQRRhsDelta fp hmn A b i| ≤
      (n : ℝ) ^ 2 * (5 * gammaTilde) * rho i := by
  have h := Wave19.entrywise_residual_telescope_bound n
    (pivotedStoredQRPseq fp hmn A)
    (pivotedStoredQRRhsEMatrixSeq fp hmn A b)
    (fun k i => (1 + 4 * ((k : ℝ) + 1)) * gammaTilde * rho i)
    (fun k hk r _j => by
      simpa [pivotedStoredQRRhsEMatrixSeq, matMulRect, matMulVec] using
        pivotedStoredQRRhs_stageImage_entrywise_le fp hmn A b alpha rho
          gammaTilde matrixErrorCoeff rhsErrorCoeff matrixReady rhsReady
          k hk r)
    i (0 : Fin 1)
  have hfactor :
      (∑ k ∈ Finset.range n,
          (1 + 4 * ((k : ℝ) + 1)) * gammaTilde * rho i) =
        (∑ k ∈ Finset.range n, (1 + 4 * ((k : ℝ) + 1))) *
          gammaTilde * rho i := by
    rw [← Finset.sum_mul, ← Finset.sum_mul]
  rw [hfactor] at h
  have hsum := Wave19.stage_sum_le_five_j_sq n
  have hscale : 0 ≤ gammaTilde * rho i :=
    mul_nonneg matrixReady.gamma_nonneg (rhsReady.rho_nonneg i)
  calc
    |pivotedStoredQRRhsDelta fp hmn A b i| ≤
        (∑ k ∈ Finset.range n, (1 + 4 * ((k : ℝ) + 1))) *
          gammaTilde * rho i := by
            simpa [pivotedStoredQRRhsDelta] using h
    _ = (∑ k ∈ Finset.range n, (1 + 4 * ((k : ℝ) + 1))) *
          (gammaTilde * rho i) := by ring
    _ ≤ (5 * (n : ℝ) ^ 2) * (gammaTilde * rho i) :=
      mul_le_mul_of_nonneg_right hsum hscale
    _ = (n : ℝ) ^ 2 * (5 * gammaTilde) * rho i := by ring

/-- Source-side reconstruction of the transformed RHS. -/
theorem pivotedStoredQRRhs_reconstruct (fp : FPModel) {m n : ℕ}
    (hmn : n ≤ m) (A : Fin m → Fin n → ℝ) (b : Fin m → ℝ)
    (i : Fin m) :
    b i + pivotedStoredQRRhsDelta fp hmn A b i =
      matMulVec m (Wave19.Qacc (pivotedStoredQRPseq fp hmn A) n)
        (fl_pivotedStoredQRRhsSeq fp hmn A b n) i := by
  let Q := Wave19.Qacc (pivotedStoredQRPseq fp hmn A) n
  let c := fl_pivotedStoredQRRhsSeq fp hmn A b n
  let d := pivotedStoredQRRhsDelta fp hmn A b
  have hQ : IsOrthogonal m Q :=
    Wave19.Qacc_orthogonal _
      (fun k => pivotedStoredQRPseq_orthogonal fp hmn A k) n
  have hTelEq : c = matMulVec m (matTranspose Q) (fun a => b a + d a) :=
    funext fun r => by
      simpa [Q, c, d] using pivotedStoredQRRhs_telescope fp hmn A b r
  have hQQT : matMul m Q (matTranspose Q) = idMatrix m :=
    funext fun r => funext fun s => hQ.right_inv r s
  have hReconstruct : matMulVec m Q c = fun a => b a + d a := by
    funext r
    rw [hTelEq, ← matMulVec_matMul m Q (matTranspose Q) _ r, hQQT,
      matMulVec_id]
  exact (congrFun hReconstruct i).symm

/-! ## Exact top solve and least-squares minimizer handoff -/

/-! A pivot-position column factor cannot in general be relabeled as the same
source-column factor.  The valid permutation-independent source envelope is
the uniform `n^2` factor. -/

theorem pivotPositionFactor_le_sourceDimensionFactor {n : ℕ}
    (pi : Equiv.Perm (Fin n)) (j : Fin n) :
    (((pi.symm j).val : ℝ) + 1) ^ 2 ≤ (n : ℝ) ^ 2 := by
  have hnat : (pi.symm j).val + 1 ≤ n := Nat.succ_le_iff.mpr (pi.symm j).isLt
  have hreal : ((pi.symm j).val : ℝ) + 1 ≤ (n : ℝ) := by
    exact_mod_cast hnat
  exact pow_le_pow_left₀ (by positivity) hreal 2

/-- A swap on two columns refutes the proposed position-`j^2` to
source-`j^2` translation. -/
theorem pivotPositionFactor_not_le_sourceColumnFactor_forall :
    ¬ ∀ (pi : Equiv.Perm (Fin 2)) (j : Fin 2),
      (((pi.symm j).val : ℝ) + 1) ^ 2 ≤ ((j.val : ℝ) + 1) ^ 2 := by
  intro h
  have hbad := h (Equiv.swap (0 : Fin 2) (1 : Fin 2)) (0 : Fin 2)
  norm_num at hbad

/-- Square leading block of the final concrete upper-trapezoidal factor. -/
noncomputable def pivotedStoredQRTopR (fp : FPModel) {m n : ℕ}
    (hmn : n ≤ m) (A : Fin m → Fin n → ℝ) : Fin n → Fin n → ℝ :=
  fun i j => fl_pivotedStoredQRMatrixSeq fp hmn A n
    ⟨i.val, lt_of_lt_of_le i.isLt hmn⟩ j

/-- Leading transformed RHS paired with `pivotedStoredQRTopR`. -/
noncomputable def pivotedStoredQRTopRhs (fp : FPModel) {m n : ℕ}
    (hmn : n ≤ m) (A : Fin m → Fin n → ℝ) (b : Fin m → ℝ) :
    Fin n → ℝ :=
  fun i => fl_pivotedStoredQRRhsSeq fp hmn A b n
    ⟨i.val, lt_of_lt_of_le i.isLt hmn⟩

/-- If a pivot-coordinate vector solves the displayed top triangular system
exactly, the actual matrix/RHS telescopes make its unpermuted coordinate vector
an exact least-squares minimizer for the source-side perturbations.

This is the exact minimizer assembly used after the numerical QR analysis.  It
does not assume least-squares optimality as input. -/
theorem fl_pivotedStoredQR_exactTopSolve_isLeastSquaresMinimizer
    (fp : FPModel) {m n : ℕ} (hmn : n ≤ m)
    (A : Fin m → Fin n → ℝ) (b : Fin m → ℝ)
    (alpha betaScale : Fin m → ℝ) (gammaTilde : ℝ)
    (matrixErrorCoeff rhsErrorCoeff : ℕ → ℝ)
    (matrixReady :
      PivotedStoredQRRawReady fp hmn A alpha gammaTilde matrixErrorCoeff)
    (rhsReady :
      PivotedStoredQRRhsRawReady fp hmn A b betaScale gammaTilde
        rhsErrorCoeff)
    (xPivot : Fin n → ℝ)
    (hsolve : ∀ r : Fin n,
      matMulVec n (pivotedStoredQRTopR fp hmn A) xPivot r =
        pivotedStoredQRTopRhs fp hmn A b r) :
    let Pseq := pivotedStoredQRPseq fp hmn A
    let Sseq := pivotedStoredQRSwapSeq fp hmn A
    let Eseq := pivotedStoredQREseq fp hmn A
    let pi := pivotPermAcc Sseq n
    let dAPivot := pivotDAacc Pseq Sseq Eseq n
    let DeltaA := fun i j => dAPivot i (pi.symm j)
    let Deltab := pivotedStoredQRRhsDelta fp hmn A b
    IsLeastSquaresMinimizer
        (fun i j => A i j + DeltaA i j)
        (fun i => b i + Deltab i)
        (vecPermute pi.symm xPivot) ∧
      (∀ i j,
        |DeltaA i j| ≤ (((pi.symm j).val : ℝ) + 1) ^ 2 *
          (5 * gammaTilde) * alpha i) ∧
      ∀ i,
        |Deltab i| ≤ (n : ℝ) ^ 2 *
          (5 * gammaTilde) * betaScale i := by
  dsimp only
  let Pseq := pivotedStoredQRPseq fp hmn A
  let Sseq := pivotedStoredQRSwapSeq fp hmn A
  let Eseq := pivotedStoredQREseq fp hmn A
  let pi := pivotPermAcc Sseq n
  let Q := Wave19.Qacc Pseq n
  let Rfull := fl_pivotedStoredQRMatrixSeq fp hmn A n
  let Rtop := pivotedStoredQRTopR fp hmn A
  let cfull := fl_pivotedStoredQRRhsSeq fp hmn A b n
  let ctop := pivotedStoredQRTopRhs fp hmn A b
  let dAPivot := pivotDAacc Pseq Sseq Eseq n
  let DeltaA : Fin m → Fin n → ℝ := fun i j => dAPivot i (pi.symm j)
  let Deltab := pivotedStoredQRRhsDelta fp hmn A b
  let APivot : Fin m → Fin n → ℝ := fun i j =>
    Wave13.columnPermuteMatrix A pi i j + dAPivot i j
  let bPert : Fin m → ℝ := fun i => b i + Deltab i
  have hP : ∀ k, IsOrthogonal m (Pseq k) := by
    intro k
    exact pivotedStoredQRPseq_orthogonal fp hmn A k
  have hQ : IsOrthogonal m Q := Wave19.Qacc_orthogonal Pseq hP n
  have hRupper : IsUpperTrapezoidal m n Rfull :=
    fl_pivotedStoredQRMatrixSeq_upperTrapezoidal fp hmn A
  have hAhat : Rfull = matMulRect m m n (matTranspose Q) APivot := by
    funext i j
    simpa [Pseq, Sseq, Eseq, Q, Rfull, pi, dAPivot, APivot,
      fl_pivotedStoredQRMatrixSeq] using
      pivoted_entrywise_residual_telescope n
        (fl_pivotedStoredQRMatrixSeq fp hmn A) Pseq Sseq Eseq hP
        (fun k _hk r s => pivotedStoredQR_step_with_residual fp hmn A k r s)
        i j
  have hbhat : cfull = matMulVec m (matTranspose Q) bPert := by
    funext i
    simpa [Pseq, Q, cfull, Deltab, bPert] using
      pivotedStoredQRRhs_telescope fp hmn A b i
  have hA_top : ∀ (i : Fin m) (j : Fin n) (hi : i.val < n),
      Rfull i j = Rtop ⟨i.val, hi⟩ j := by
    intro i j hi
    congr 2
  have hA_bottom : ∀ (i : Fin m) (j : Fin n), n ≤ i.val →
      Rfull i j = 0 := by
    intro i j hi
    exact hRupper i j (lt_of_lt_of_le j.isLt hi)
  have hb_top : ∀ (i : Fin m) (hi : i.val < n),
      cfull i = ctop ⟨i.val, hi⟩ := by
    intro i hi
    congr 1
  have hNEtrans : RectLSNormalEquations Rfull cfull xPivot :=
    RectLSNormalEquations.of_top_solve_zero_bottom
      Rfull cfull Rtop ctop xPivot hA_top hA_bottom hb_top
      (by simpa [Rtop, ctop] using hsolve)
  have hNEPivot : RectLSNormalEquations APivot bPert xPivot :=
    RectLSNormalEquations.of_orthogonal_left
      (matTranspose Q) APivot Rfull bPert cfull xPivot hQ.transpose
      hAhat hbhat hNEtrans
  have hMinPivot : IsLeastSquaresMinimizer APivot bPert xPivot :=
    hNEPivot.isLeastSquaresMinimizer
  have hPermData :
      rectPermuteCols pi (fun i j => A i j + DeltaA i j) = APivot := by
    funext i j
    simp [rectPermuteCols, DeltaA, APivot, Wave13.columnPermuteMatrix]
  have hMinPerm : IsLeastSquaresMinimizer
      (rectPermuteCols pi (fun i j => A i j + DeltaA i j)) bPert xPivot := by
    rw [hPermData]
    exact hMinPivot
  have hMinSource : IsLeastSquaresMinimizer
      (fun i j => A i j + DeltaA i j) bPert
      (vecPermute pi.symm xPivot) :=
    IsLeastSquaresMinimizer.of_permuteCols pi
      (fun i j => A i j + DeltaA i j) bPert xPivot hMinPerm
  have hQR := fl_pivotedStoredQR_actual_rowwise_backward_error fp hmn A
    alpha gammaTilde matrixErrorCoeff matrixReady
  have hDeltaA : ∀ i j,
      |DeltaA i j| ≤ (((pi.symm j).val : ℝ) + 1) ^ 2 *
        (5 * gammaTilde) * alpha i := by
    intro i j
    simpa [Pseq, Sseq, Eseq, pi, dAPivot, DeltaA] using
      hQR.2.2.2.2 i (pi.symm j)
  have hDeltab : ∀ i,
      |Deltab i| ≤ (n : ℝ) ^ 2 *
        (5 * gammaTilde) * betaScale i := by
    intro i
    simpa [Deltab] using
      pivotedStoredQRRhsDelta_rowwise_bound fp hmn A b alpha betaScale
        gammaTilde matrixErrorCoeff rhsErrorCoeff matrixReady rhsReady i
  exact ⟨by simpa [DeltaA, Deltab, bPert] using hMinSource,
    hDeltaA, hDeltab⟩

/-- Correct source-column packaging of
`fl_pivotedStoredQR_exactTopSolve_isLeastSquaresMinimizer`.

The pivot-coordinate perturbation retains its sharper position-dependent
factor.  After unpermuting an arbitrary pivot permutation, the universally
valid source-coordinate statement has the uniform `n^2` column factor. -/
theorem fl_pivotedStoredQR_exactTopSolve_isLeastSquaresMinimizer_source_n_sq
    (fp : FPModel) {m n : ℕ} (hmn : n ≤ m)
    (A : Fin m → Fin n → ℝ) (b : Fin m → ℝ)
    (alpha betaScale : Fin m → ℝ) (gammaTilde : ℝ)
    (matrixErrorCoeff rhsErrorCoeff : ℕ → ℝ)
    (matrixReady :
      PivotedStoredQRRawReady fp hmn A alpha gammaTilde matrixErrorCoeff)
    (rhsReady :
      PivotedStoredQRRhsRawReady fp hmn A b betaScale gammaTilde
        rhsErrorCoeff)
    (xPivot : Fin n → ℝ)
    (hsolve : ∀ r : Fin n,
      matMulVec n (pivotedStoredQRTopR fp hmn A) xPivot r =
        pivotedStoredQRTopRhs fp hmn A b r) :
    let Pseq := pivotedStoredQRPseq fp hmn A
    let Sseq := pivotedStoredQRSwapSeq fp hmn A
    let Eseq := pivotedStoredQREseq fp hmn A
    let pi := pivotPermAcc Sseq n
    let dAPivot := pivotDAacc Pseq Sseq Eseq n
    let DeltaA := fun i j => dAPivot i (pi.symm j)
    let Deltab := pivotedStoredQRRhsDelta fp hmn A b
    IsLeastSquaresMinimizer
        (fun i j => A i j + DeltaA i j)
        (fun i => b i + Deltab i)
        (vecPermute pi.symm xPivot) ∧
      (∀ i j,
        |DeltaA i j| ≤ (n : ℝ) ^ 2 * (5 * gammaTilde) * alpha i) ∧
      ∀ i,
        |Deltab i| ≤ (n : ℝ) ^ 2 * (5 * gammaTilde) * betaScale i := by
  dsimp only
  have h := fl_pivotedStoredQR_exactTopSolve_isLeastSquaresMinimizer
    fp hmn A b alpha betaScale gammaTilde matrixErrorCoeff rhsErrorCoeff
      matrixReady rhsReady xPivot hsolve
  dsimp only at h
  refine ⟨h.1, ?_, h.2.2⟩
  intro i j
  let pi := pivotPermAcc (pivotedStoredQRSwapSeq fp hmn A) n
  have hfactor := pivotPositionFactor_le_sourceDimensionFactor pi j
  have hc : 0 ≤ (5 * gammaTilde) * alpha i :=
    mul_nonneg (mul_nonneg (by norm_num) matrixReady.gamma_nonneg)
      (matrixReady.alpha_nonneg i)
  calc
    |pivotDAacc (pivotedStoredQRPseq fp hmn A)
          (pivotedStoredQRSwapSeq fp hmn A)
          (pivotedStoredQREseq fp hmn A) n i
          ((pivotPermAcc (pivotedStoredQRSwapSeq fp hmn A) n).symm j)|
        ≤ (((pi.symm j).val : ℝ) + 1) ^ 2 *
            (5 * gammaTilde) * alpha i := by simpa [pi] using h.2.1 i j
    _ = (((pi.symm j).val : ℝ) + 1) ^ 2 *
          ((5 * gammaTilde) * alpha i) := by ring
    _ ≤ (n : ℝ) ^ 2 * ((5 * gammaTilde) * alpha i) :=
      mul_le_mul_of_nonneg_right hfactor hc
    _ = (n : ℝ) ^ 2 * (5 * gammaTilde) * alpha i := by ring

/-! ## Rounded back substitution on the actual trace -/

/-- Pivot-coordinate matrix perturbation after pulling a top-block triangular
solve perturbation back through the concrete orthogonal factor. -/
noncomputable def pivotedStoredQRBackSubPivotDelta (fp : FPModel) {m n : ℕ}
    (hmn : n ≤ m) (A : Fin m → Fin n → ℝ)
    (dR : Fin n → Fin n → ℝ) : Fin m → Fin n → ℝ :=
  let Pseq := pivotedStoredQRPseq fp hmn A
  let Sseq := pivotedStoredQRSwapSeq fp hmn A
  let Eseq := pivotedStoredQREseq fp hmn A
  let dA := pivotDAacc Pseq Sseq Eseq n
  let Q := Wave19.Qacc Pseq n
  fun i j => dA i j +
    matMulRect m m n Q (rectTopBlock (m := m) dR) i j

/-- Source-column ordering of `pivotedStoredQRBackSubPivotDelta`. -/
noncomputable def pivotedStoredQRBackSubSourceDelta (fp : FPModel) {m n : ℕ}
    (hmn : n ≤ m) (A : Fin m → Fin n → ℝ)
    (dR : Fin n → Fin n → ℝ) : Fin m → Fin n → ℝ :=
  let pi := pivotPermAcc (pivotedStoredQRSwapSeq fp hmn A) n
  fun i j => pivotedStoredQRBackSubPivotDelta fp hmn A dR i (pi.symm j)

/-- Computed pivot-coordinate vector returned by floating-point back
substitution on the actual final leading block. -/
noncomputable def pivotedStoredQRReturnedPivotX (fp : FPModel) {m n : ℕ}
    (hmn : n ≤ m) (A : Fin m → Fin n → ℝ) (b : Fin m → ℝ) :
    Fin n → ℝ :=
  fl_backSub fp n (pivotedStoredQRTopR fp hmn A)
    (pivotedStoredQRTopRhs fp hmn A b)

/-- Returned vector in source-column coordinates. -/
noncomputable def pivotedStoredQRReturnedX (fp : FPModel) {m n : ℕ}
    (hmn : n ≤ m) (A : Fin m → Fin n → ℝ) (b : Fin m → ℝ) :
    Fin n → ℝ :=
  let pi := pivotPermAcc (pivotedStoredQRSwapSeq fp hmn A) n
  vecPermute pi.symm (pivotedStoredQRReturnedPivotX fp hmn A b)

/-- The actual QR/RHS recursion followed by the repository's floating-point
back substitution returns an exact minimizer after the explicit pulled-back
triangular perturbation.

The theorem deliberately reports the triangular correction separately.  The
QR part and RHS part retain their proved rowwise bounds; no rowwise bound for
`Q [dR;0]` is asserted here.  Establishing that additional source estimate is
the remaining triangular-solve ingredient of the printed Theorem 20.7 matrix
bound. -/
theorem fl_pivotedStoredQR_returnedX_exactMinimizer_with_triangular_correction
    (fp : FPModel) {m n : ℕ} (hmn : n ≤ m)
    (A : Fin m → Fin n → ℝ) (b : Fin m → ℝ)
    (alpha betaScale : Fin m → ℝ) (gammaTilde : ℝ)
    (matrixErrorCoeff rhsErrorCoeff : ℕ → ℝ)
    (matrixReady :
      PivotedStoredQRRawReady fp hmn A alpha gammaTilde matrixErrorCoeff)
    (rhsReady :
      PivotedStoredQRRhsRawReady fp hmn A b betaScale gammaTilde
        rhsErrorCoeff)
    (hdiag : ∀ i : Fin n, pivotedStoredQRTopR fp hmn A i i ≠ 0)
    (hgamma : gammaValid fp n) :
    ∃ dR : Fin n → Fin n → ℝ,
      (∀ i j,
        |dR i j| ≤ gamma fp n * |pivotedStoredQRTopR fp hmn A i j|) ∧
      IsLeastSquaresMinimizer
        (fun i j => A i j +
          pivotedStoredQRBackSubSourceDelta fp hmn A dR i j)
        (fun i => b i + pivotedStoredQRRhsDelta fp hmn A b i)
        (pivotedStoredQRReturnedX fp hmn A b) ∧
      (∀ i j,
        |pivotDAacc (pivotedStoredQRPseq fp hmn A)
            (pivotedStoredQRSwapSeq fp hmn A)
            (pivotedStoredQREseq fp hmn A) n i j| ≤
          ((j.val : ℝ) + 1) ^ 2 * (5 * gammaTilde) * alpha i) ∧
      ∀ i,
        |pivotedStoredQRRhsDelta fp hmn A b i| ≤
          (n : ℝ) ^ 2 * (5 * gammaTilde) * betaScale i := by
  let Pseq := pivotedStoredQRPseq fp hmn A
  let Sseq := pivotedStoredQRSwapSeq fp hmn A
  let Eseq := pivotedStoredQREseq fp hmn A
  let pi := pivotPermAcc Sseq n
  let Q := Wave19.Qacc Pseq n
  let Rfull := fl_pivotedStoredQRMatrixSeq fp hmn A n
  let Rtop := pivotedStoredQRTopR fp hmn A
  let cfull := fl_pivotedStoredQRRhsSeq fp hmn A b n
  let ctop := pivotedStoredQRTopRhs fp hmn A b
  let dA := pivotDAacc Pseq Sseq Eseq n
  let db := pivotedStoredQRRhsDelta fp hmn A b
  let xPivot := pivotedStoredQRReturnedPivotX fp hmn A b
  have hP : ∀ k, IsOrthogonal m (Pseq k) := by
    intro k
    exact pivotedStoredQRPseq_orthogonal fp hmn A k
  have hQ : IsOrthogonal m Q := Wave19.Qacc_orthogonal Pseq hP n
  have hRupper : IsUpperTrapezoidal m n Rfull :=
    fl_pivotedStoredQRMatrixSeq_upperTrapezoidal fp hmn A
  have hRtopUpper : ∀ i j : Fin n, j.val < i.val → Rtop i j = 0 := by
    intro i j hji
    exact hRupper ⟨i.val, lt_of_lt_of_le i.isLt hmn⟩ j hji
  rcases backSub_backward_error fp n Rtop ctop
      (by simpa [Rtop] using hdiag) hRtopUpper hgamma with
    ⟨dR, hdR, hsolve⟩
  refine ⟨dR, ?_, ?_, ?_, ?_⟩
  · simpa [Rtop] using hdR
  · let topdR := rectTopBlock (m := m) dR
    let APivot : Fin m → Fin n → ℝ := fun i j =>
      Wave13.columnPermuteMatrix A pi i j + dA i j
    let APivotTotal : Fin m → Fin n → ℝ := fun i j =>
      APivot i j + matMulRect m m n Q topdR i j
    let Atrans : Fin m → Fin n → ℝ := fun i j => Rfull i j + topdR i j
    let bPert : Fin m → ℝ := fun i => b i + db i
    have hAhat : Rfull = matMulRect m m n (matTranspose Q) APivot := by
      funext i j
      simpa [Pseq, Sseq, Eseq, Q, Rfull, pi, dA, APivot,
        fl_pivotedStoredQRMatrixSeq] using
        pivoted_entrywise_residual_telescope n
          (fl_pivotedStoredQRMatrixSeq fp hmn A) Pseq Sseq Eseq hP
          (fun k _hk r s =>
            pivotedStoredQR_step_with_residual fp hmn A k r s) i j
    have hbhat : cfull = matMulVec m (matTranspose Q) bPert := by
      funext i
      simpa [Pseq, Q, cfull, db, bPert] using
        pivotedStoredQRRhs_telescope fp hmn A b i
    have hQTQ : matMul m (matTranspose Q) Q = idMatrix m :=
      funext fun i => funext fun j => hQ.left_inv i j
    have hpull :
        matMulRect m m n (matTranspose Q)
            (matMulRect m m n Q topdR) = topdR := by
      rw [← matMulRect_assoc_square_left, hQTQ, matMulRect_id_left]
    have hAtrans : Atrans =
        matMulRect m m n (matTranspose Q) APivotTotal := by
      rw [show APivotTotal = fun i j =>
          APivot i j + matMulRect m m n Q topdR i j by rfl,
        matMulRect_add_right, ← hAhat, hpull]
    have hA_top : ∀ (i : Fin m) (j : Fin n) (hi : i.val < n),
        Atrans i j = (fun r s => Rtop r s + dR r s) ⟨i.val, hi⟩ j := by
      intro i j hi
      have hRi : Rfull i j = Rtop ⟨i.val, hi⟩ j := by
        simp [Rfull, Rtop]
        congr 2
      have hdi : topdR i j = dR ⟨i.val, hi⟩ j := by
        simpa [topdR] using rectTopBlock_top dR i j hi
      simpa [Atrans] using congrArg₂ (· + ·) hRi hdi
    have hA_bottom : ∀ (i : Fin m) (j : Fin n), n ≤ i.val →
        Atrans i j = 0 := by
      intro i j hi
      have htopzero : topdR i j = 0 := by
        simpa [topdR] using rectTopBlock_bottom dR i j hi
      rw [show Atrans i j = Rfull i j + topdR i j by rfl,
        hRupper i j (lt_of_lt_of_le j.isLt hi), htopzero]
      ring
    have hb_top : ∀ (i : Fin m) (hi : i.val < n),
        cfull i = ctop ⟨i.val, hi⟩ := by
      intro i hi
      congr 1
    have hsolve' : ∀ r : Fin n,
        matMulVec n (fun i j => Rtop i j + dR i j) xPivot r = ctop r := by
      intro r
      simpa [matMulVec, xPivot, pivotedStoredQRReturnedPivotX,
        Rtop, ctop] using hsolve r
    have hNEtrans : RectLSNormalEquations Atrans cfull xPivot :=
      RectLSNormalEquations.of_top_solve_zero_bottom
        Atrans cfull (fun i j => Rtop i j + dR i j) ctop xPivot
        hA_top hA_bottom hb_top hsolve'
    have hNEPivot : RectLSNormalEquations APivotTotal bPert xPivot :=
      RectLSNormalEquations.of_orthogonal_left
        (matTranspose Q) APivotTotal Atrans bPert cfull xPivot hQ.transpose
        hAtrans hbhat hNEtrans
    have hMinPivot : IsLeastSquaresMinimizer APivotTotal bPert xPivot :=
      hNEPivot.isLeastSquaresMinimizer
    have hPermData : rectPermuteCols pi
        (fun i j => A i j +
          pivotedStoredQRBackSubSourceDelta fp hmn A dR i j) =
        APivotTotal := by
      funext i j
      simp [rectPermuteCols, pivotedStoredQRBackSubSourceDelta,
        pivotedStoredQRBackSubPivotDelta, Pseq, Sseq, Eseq, pi, Q, dA,
        APivotTotal, APivot, topdR, Wave13.columnPermuteMatrix]
      ring
    have hMinPerm : IsLeastSquaresMinimizer
        (rectPermuteCols pi
          (fun i j => A i j +
            pivotedStoredQRBackSubSourceDelta fp hmn A dR i j))
        bPert xPivot := by
      rw [hPermData]
      exact hMinPivot
    have hMinSource := IsLeastSquaresMinimizer.of_permuteCols pi
      (fun i j => A i j +
        pivotedStoredQRBackSubSourceDelta fp hmn A dR i j)
      bPert xPivot hMinPerm
    simpa [bPert, db, xPivot, pivotedStoredQRReturnedX, pi, Sseq] using
      hMinSource
  · have hQR := fl_pivotedStoredQR_actual_rowwise_backward_error fp hmn A
      alpha gammaTilde matrixErrorCoeff matrixReady
    simpa [Pseq, Sseq, Eseq] using hQR.2.2.2.2
  · intro i
    simpa [db] using
      pivotedStoredQRRhsDelta_rowwise_bound fp hmn A b alpha betaScale
        gammaTilde matrixErrorCoeff rhsErrorCoeff matrixReady rhsReady i

/-- Literal rounded-back-substitution endpoint with honest source-column
packaging of the QR perturbation.

The exact minimizer uses the total source perturbation including the explicit
pulled-back triangular correction.  The bound below is deliberately only for
the QR part: it converts the sharp pivot-position factor to the valid uniform
source factor `n^2`; it does not claim the still-unproved rowwise bound for the
triangular correction. -/
theorem
    fl_pivotedStoredQR_returnedX_exactMinimizer_with_triangular_correction_source_n_sq
    (fp : FPModel) {m n : ℕ} (hmn : n ≤ m)
    (A : Fin m → Fin n → ℝ) (b : Fin m → ℝ)
    (alpha betaScale : Fin m → ℝ) (gammaTilde : ℝ)
    (matrixErrorCoeff rhsErrorCoeff : ℕ → ℝ)
    (matrixReady :
      PivotedStoredQRRawReady fp hmn A alpha gammaTilde matrixErrorCoeff)
    (rhsReady :
      PivotedStoredQRRhsRawReady fp hmn A b betaScale gammaTilde
        rhsErrorCoeff)
    (hdiag : ∀ i : Fin n, pivotedStoredQRTopR fp hmn A i i ≠ 0)
    (hgamma : gammaValid fp n) :
    let pi := pivotPermAcc (pivotedStoredQRSwapSeq fp hmn A) n
    ∃ dR : Fin n → Fin n → ℝ,
      (∀ i j,
        |dR i j| ≤ gamma fp n * |pivotedStoredQRTopR fp hmn A i j|) ∧
      IsLeastSquaresMinimizer
        (fun i j => A i j +
          pivotedStoredQRBackSubSourceDelta fp hmn A dR i j)
        (fun i => b i + pivotedStoredQRRhsDelta fp hmn A b i)
        (pivotedStoredQRReturnedX fp hmn A b) ∧
      (∀ i j,
        |pivotDAacc (pivotedStoredQRPseq fp hmn A)
            (pivotedStoredQRSwapSeq fp hmn A)
            (pivotedStoredQREseq fp hmn A) n i (pi.symm j)| ≤
          (n : ℝ) ^ 2 * (5 * gammaTilde) * alpha i) ∧
      ∀ i,
        |pivotedStoredQRRhsDelta fp hmn A b i| ≤
          (n : ℝ) ^ 2 * (5 * gammaTilde) * betaScale i := by
  dsimp only
  rcases fl_pivotedStoredQR_returnedX_exactMinimizer_with_triangular_correction
      fp hmn A b alpha betaScale gammaTilde matrixErrorCoeff rhsErrorCoeff
      matrixReady rhsReady hdiag hgamma with
    ⟨dR, hdR, hmin, hbase, hdb⟩
  refine ⟨dR, hdR, hmin, ?_, hdb⟩
  intro i j
  let pi := pivotPermAcc (pivotedStoredQRSwapSeq fp hmn A) n
  have hfactor := pivotPositionFactor_le_sourceDimensionFactor pi j
  have hc : 0 ≤ (5 * gammaTilde) * alpha i :=
    mul_nonneg (mul_nonneg (by norm_num) matrixReady.gamma_nonneg)
      (matrixReady.alpha_nonneg i)
  calc
    |pivotDAacc (pivotedStoredQRPseq fp hmn A)
          (pivotedStoredQRSwapSeq fp hmn A)
          (pivotedStoredQREseq fp hmn A) n i (pi.symm j)|
        ≤ ((((pi.symm j).val : ℝ) + 1) ^ 2) *
            (5 * gammaTilde) * alpha i := hbase i (pi.symm j)
    _ = ((((pi.symm j).val : ℝ) + 1) ^ 2) *
          ((5 * gammaTilde) * alpha i) := by ring
    _ ≤ (n : ℝ) ^ 2 * ((5 * gammaTilde) * alpha i) :=
      mul_le_mul_of_nonneg_right hfactor hc
    _ = (n : ℝ) ^ 2 * (5 * gammaTilde) * alpha i := by ring

end Theorem20_7

end NumStability
