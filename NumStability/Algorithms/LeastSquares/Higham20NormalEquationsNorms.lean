-- Source-norm closure for Higham's equations (20.13a)-(20.13b).

import NumStability.Algorithms.LeastSquares.Higham20Equations
import NumStability.Algorithms.LeastSquares.Higham20Remaining

namespace NumStability

open scoped BigOperators

private theorem frobNormRect_sq_eq_complexMatrixFrobeniusSq_realRect
    {m n : Nat} (A : Fin m -> Fin n -> Real) :
    frobNormRect A ^ 2 =
      complexMatrixFrobeniusSq (realRectToCMatrix A) := by
  rw [frobNormRect_sq]
  simp [frobNormSqRect, complexMatrixFrobeniusSq, realRectToCMatrix,
    Real.norm_eq_abs, sq_abs]

/-- Rectangular real Frobenius norm squared is bounded by the number of
columns times the squared Euclidean operator norm. -/
theorem frobNormRect_sq_le_card_mul_complexMatrixOp2_sq {m n : Nat}
    (A : Fin m -> Fin n -> Real) :
    frobNormRect A ^ 2 <=
      (n : Real) * complexMatrixOp2 (realRectToCMatrix A) ^ 2 := by
  rw [frobNormRect_sq_eq_complexMatrixFrobeniusSq_realRect]
  exact complexMatrixFrobeniusSq_le_card_mul_complexMatrixOp2_sq
    (realRectToCMatrix A)

/-- The exact entrywise Gram majorant `|A^T||A|`. -/
noncomputable def higham20NormalEqAbsGram {m n : Nat}
    (A : Fin m -> Fin n -> Real) : Fin n -> Fin n -> Real :=
  fun i j => Finset.univ.sum (fun k : Fin m => |A k i| * |A k j|)

/-- The exact entrywise right-hand-side majorant `|A^T||b|`. -/
noncomputable def higham20NormalEqAbsRhs {m n : Nat}
    (A : Fin m -> Fin n -> Real) (b : Fin m -> Real) : Fin n -> Real :=
  fun j => Finset.univ.sum (fun i : Fin m => |A i j| * |b i|)

/-- The natural Gram majorant has the source envelope
`|| |A^T||A| ||_F <= n ||A||_2^2`. -/
theorem higham20NormalEqAbsGram_frobNormRect_le {m n : Nat}
    (A : Fin m -> Fin n -> Real) :
    frobNormRect (higham20NormalEqAbsGram A) <=
      (n : Real) * complexMatrixOp2 (realRectToCMatrix A) ^ 2 := by
  let Aabs : Fin m -> Fin n -> Real := absMatrixRect A
  have hprod :
      higham20NormalEqAbsGram A =
        rectMatMul (finiteTranspose Aabs) Aabs := by
    ext i j
    simp [higham20NormalEqAbsGram, rectMatMul, finiteTranspose, Aabs,
      absMatrixRect]
  rw [hprod]
  calc
    frobNormRect (rectMatMul (finiteTranspose Aabs) Aabs) <=
        frobNormRect (finiteTranspose Aabs) * frobNormRect Aabs :=
      frobNormRect_rectMatMul_le _ _
    _ = frobNormRect A ^ 2 := by
      rw [frobNormRect_finiteTranspose]
      have habs : frobNormRect Aabs = frobNormRect A := by
        simpa [Aabs, absMatrixRect] using frobNormRect_abs A
      rw [habs]
      ring
    _ <= (n : Real) * complexMatrixOp2 (realRectToCMatrix A) ^ 2 :=
      frobNormRect_sq_le_card_mul_complexMatrixOp2_sq A

private theorem higham20_realRectMatrixRank_finiteTranspose
    {m n : Nat} (A : Fin m -> Fin n -> Real) :
    realRectMatrixRank (finiteTranspose A) = realRectMatrixRank A := by
  unfold realRectMatrixRank complexMatrixRank
  have hmatrix :
      (realRectToCMatrix (finiteTranspose A) :
          Matrix (Fin n) (Fin m) Complex) =
        Matrix.transpose
          (realRectToCMatrix A : Matrix (Fin m) (Fin n) Complex) := by
    ext i j
    rfl
  rw [hmatrix, Matrix.rank_transpose]

private theorem higham20_realRectMatrixRank_le_width
    {m n : Nat} (A : Fin m -> Fin n -> Real) :
    realRectMatrixRank A <= n := by
  simpa [realRectMatrixRank, complexMatrixRank] using
    (Matrix.rank_le_width
      (realRectToCMatrix A : Matrix (Fin m) (Fin n) Complex))

/-- The natural RHS majorant has the source envelope
`|| |A^T||b| ||_2 <= sqrt(n) ||A||_2 ||b||_2`. -/
theorem higham20NormalEqAbsRhs_vecNorm2_le {m n : Nat}
    (hn : 0 < n) (hmn : n <= m)
    (A : Fin m -> Fin n -> Real) (b : Fin m -> Real) :
    vecNorm2 (higham20NormalEqAbsRhs A b) <=
      Real.sqrt (n : Real) * complexMatrixOp2 (realRectToCMatrix A) *
        vecNorm2 b := by
  let AT : Fin n -> Fin m -> Real := finiteTranspose A
  have hm : 0 < m := lt_of_lt_of_le hn hmn
  have hATbase :
      rectOpNorm2Le AT (complexMatrixOp2 (realRectToCMatrix AT)) :=
    rectOpNorm2Le_of_complexMatrixOp2_realRectToCMatrix_le AT le_rfl
  have hATabs0 :=
    rectOpNorm2Le_absMatrixRect_sqrt_rank_mul_of_rectOpNorm2Le
      hm AT (complexMatrixOp2_nonneg _) hATbase
  have hrank : realRectMatrixRank AT <= n := by
    rw [show AT = finiteTranspose A by rfl,
      higham20_realRectMatrixRank_finiteTranspose]
    exact higham20_realRectMatrixRank_le_width A
  have hsqrt :
      Real.sqrt (realRectMatrixRank AT : Real) <= Real.sqrt (n : Real) :=
    Real.sqrt_le_sqrt (by exact_mod_cast hrank)
  have hATnorm :
      complexMatrixOp2 (realRectToCMatrix AT) =
        complexMatrixOp2 (realRectToCMatrix A) := by
    simpa [AT] using
      complexMatrixOp2_realRectToCMatrix_finiteTranspose_eq A
  have hATabs :
      rectOpNorm2Le (absMatrixRect AT)
        (Real.sqrt (n : Real) *
          complexMatrixOp2 (realRectToCMatrix A)) := by
    apply rectOpNorm2Le_mono _ hATabs0
    rw [hATnorm]
    exact mul_le_mul_of_nonneg_right hsqrt (complexMatrixOp2_nonneg _)
  have haction :
      higham20NormalEqAbsRhs A b =
        rectMatMulVec (absMatrixRect AT) (absVec m b) := by
    ext j
    simp [higham20NormalEqAbsRhs, rectMatMulVec, absMatrixRect,
      finiteTranspose, AT, absVec]
  rw [haction]
  calc
    vecNorm2 (rectMatMulVec (absMatrixRect AT) (absVec m b)) <=
        (Real.sqrt (n : Real) *
          complexMatrixOp2 (realRectToCMatrix A)) *
            vecNorm2 (absVec m b) := hATabs _
    _ = Real.sqrt (n : Real) *
        complexMatrixOp2 (realRectToCMatrix A) * vecNorm2 b := by
      rw [show vecNorm2 (absVec m b) = vecNorm2 b by
        simpa [absVec] using vecNorm2_abs b]

/-- The absolute Gram majorant of a square factor is bounded by the square
of its Frobenius norm. -/
theorem higham20NormalEqAbsGram_frobNormRect_le_frobNormRect_sq {n : Nat}
    (R : Fin n -> Fin n -> Real) :
    frobNormRect (higham20NormalEqAbsGram R) <= frobNormRect R ^ 2 := by
  let Rabs : Fin n -> Fin n -> Real := absMatrixRect R
  have hprod :
      higham20NormalEqAbsGram R =
        rectMatMul (finiteTranspose Rabs) Rabs := by
    ext i j
    simp [higham20NormalEqAbsGram, rectMatMul, finiteTranspose, Rabs,
      absMatrixRect]
  rw [hprod]
  calc
    frobNormRect (rectMatMul (finiteTranspose Rabs) Rabs) <=
        frobNormRect (finiteTranspose Rabs) * frobNormRect Rabs :=
      frobNormRect_rectMatMul_le _ _
    _ = frobNormRect R ^ 2 := by
      rw [frobNormRect_finiteTranspose]
      have habs : frobNormRect Rabs = frobNormRect R := by
        simpa [Rabs, absMatrixRect] using frobNormRect_abs R
      rw [habs]
      ring

/-- Equation (20.11) controls the computed Cholesky factor norm directly.
The proof uses only diagonal entries: summing the column-square estimates
avoids a spurious factor `n` in the smallness denominator. -/
theorem higham20_cholesky_R_frob_sq_le_source {m n : Nat}
    (fp : FPModel) (A : Fin m -> Fin n -> Real)
    (C_hat R_hat : Fin n -> Fin n -> Real)
    (hGram : GramProductError n C_hat (rectLSGram A)
      (higham20NormalEqAbsGram A) (gamma fp m))
    (hChol : CholeskyBackwardError n C_hat R_hat (gamma fp (n + 1)))
    (hsmall : gamma fp (n + 1) < 1) :
    frobNormRect R_hat ^ 2 <=
      ((1 + gamma fp m) * frobNormRect A ^ 2) /
        (1 - gamma fp (n + 1)) := by
  have habsdiagA (i : Fin n) :
      higham20NormalEqAbsGram A i i =
        Finset.univ.sum (fun k : Fin m => A k i ^ 2) := by
    unfold higham20NormalEqAbsGram
    apply Finset.sum_congr rfl
    intro k _
    rw [show |A k i| * |A k i| = |A k i * A k i| by rw [abs_mul]]
    rw [abs_of_nonneg (mul_self_nonneg _)]
    ring
  have habsdiagR (i : Fin n) :
      Finset.univ.sum (fun k : Fin n => |R_hat k i| * |R_hat k i|) =
        Finset.univ.sum (fun k : Fin n => R_hat k i ^ 2) := by
    apply Finset.sum_congr rfl
    intro k _
    rw [show |R_hat k i| * |R_hat k i| =
        |R_hat k i * R_hat k i| by rw [abs_mul]]
    rw [abs_of_nonneg (mul_self_nonneg _)]
    ring
  have hcol (i : Fin n) :
      Finset.univ.sum (fun k : Fin n => R_hat k i ^ 2) <=
        (1 + gamma fp m) *
            Finset.univ.sum (fun k : Fin m => A k i ^ 2) +
          gamma fp (n + 1) *
            Finset.univ.sum (fun k : Fin n => R_hat k i ^ 2) := by
    have hgramdiagA :
        rectLSGram A i i =
          Finset.univ.sum (fun k : Fin m => A k i ^ 2) := by
      unfold rectLSGram
      apply Finset.sum_congr rfl
      intro k _
      ring
    have hCabs := hGram.bound i i
    have hCle :
        C_hat i i - rectLSGram A i i <=
          gamma fp m * higham20NormalEqAbsGram A i i :=
      (le_abs_self _).trans hCabs
    have hC :
        C_hat i i <=
          (1 + gamma fp m) *
            Finset.univ.sum (fun k : Fin m => A k i ^ 2) := by
      rw [hgramdiagA, habsdiagA] at hCle
      nlinarith
    have hRabs := hChol.backward_bound i i
    have hRle :
        Finset.univ.sum (fun k : Fin n => R_hat k i * R_hat k i) -
            C_hat i i <=
          gamma fp (n + 1) *
            Finset.univ.sum (fun k : Fin n => |R_hat k i| * |R_hat k i|) :=
      (le_abs_self _).trans hRabs
    rw [habsdiagR] at hRle
    have hsquares :
        Finset.univ.sum (fun k : Fin n => R_hat k i * R_hat k i) =
          Finset.univ.sum (fun k : Fin n => R_hat k i ^ 2) := by
      apply Finset.sum_congr rfl
      intro k _
      ring
    rw [hsquares] at hRle
    linarith
  have hsum :
      frobNormSqRect R_hat <=
        (1 + gamma fp m) * frobNormSqRect A +
          gamma fp (n + 1) * frobNormSqRect R_hat := by
    unfold frobNormSqRect
    calc
      Finset.univ.sum (fun i : Fin n =>
          Finset.univ.sum (fun j : Fin n => R_hat i j ^ 2)) =
          Finset.univ.sum (fun j : Fin n =>
            Finset.univ.sum (fun i : Fin n => R_hat i j ^ 2)) := by
        rw [Finset.sum_comm]
      _ <= Finset.univ.sum (fun j : Fin n =>
          ((1 + gamma fp m) *
              Finset.univ.sum (fun i : Fin m => A i j ^ 2) +
            gamma fp (n + 1) *
              Finset.univ.sum (fun i : Fin n => R_hat i j ^ 2))) :=
        Finset.sum_le_sum (fun j _ => hcol j)
      _ = (1 + gamma fp m) *
            Finset.univ.sum (fun j : Fin n =>
              Finset.univ.sum (fun i : Fin m => A i j ^ 2)) +
          gamma fp (n + 1) *
            Finset.univ.sum (fun j : Fin n =>
              Finset.univ.sum (fun i : Fin n => R_hat i j ^ 2)) := by
        rw [Finset.sum_add_distrib, ← Finset.mul_sum, ← Finset.mul_sum]
      _ = (1 + gamma fp m) *
            Finset.univ.sum (fun i : Fin m =>
              Finset.univ.sum (fun j : Fin n => A i j ^ 2)) +
          gamma fp (n + 1) *
            Finset.univ.sum (fun i : Fin n =>
              Finset.univ.sum (fun j : Fin n => R_hat i j ^ 2)) := by
        rw [
          Finset.sum_comm (f := fun j : Fin n => fun i : Fin m => A i j ^ 2),
          Finset.sum_comm (f := fun j : Fin n => fun i : Fin n => R_hat i j ^ 2)]
  have hden : 0 < 1 - gamma fp (n + 1) := by linarith
  rw [frobNormRect_sq, frobNormRect_sq]
  apply (le_div_iff₀ hden).2
  nlinarith

/-- Fully source-scaled norm envelope for the computed
`|R_hat^T||R_hat|` term in (20.12). -/
theorem higham20_computed_R_absGram_frobNormRect_le_source {m n : Nat}
    (fp : FPModel) (A : Fin m -> Fin n -> Real)
    (C_hat R_hat : Fin n -> Fin n -> Real)
    (hGram : GramProductError n C_hat (rectLSGram A)
      (higham20NormalEqAbsGram A) (gamma fp m))
    (hChol : CholeskyBackwardError n C_hat R_hat (gamma fp (n + 1)))
    (hsmall : gamma fp (n + 1) < 1) :
    frobNormRect (higham20NormalEqAbsGram R_hat) <=
      (n : Real) * ((1 + gamma fp m) / (1 - gamma fp (n + 1))) *
        complexMatrixOp2 (realRectToCMatrix A) ^ 2 := by
  have hR := higham20_cholesky_R_frob_sq_le_source fp A C_hat R_hat
    hGram hChol hsmall
  have hden : 0 < 1 - gamma fp (n + 1) := by linarith
  have hfactor : 0 <= (1 + gamma fp m) / (1 - gamma fp (n + 1)) :=
    div_nonneg (add_nonneg zero_le_one hGram.eps_nonneg) hden.le
  calc
    frobNormRect (higham20NormalEqAbsGram R_hat) <=
        frobNormRect R_hat ^ 2 :=
      higham20NormalEqAbsGram_frobNormRect_le_frobNormRect_sq R_hat
    _ <= ((1 + gamma fp m) * frobNormRect A ^ 2) /
        (1 - gamma fp (n + 1)) := hR
    _ = ((1 + gamma fp m) / (1 - gamma fp (n + 1))) *
        frobNormRect A ^ 2 := by ring
    _ <= ((1 + gamma fp m) / (1 - gamma fp (n + 1))) *
        ((n : Real) * complexMatrixOp2 (realRectToCMatrix A) ^ 2) :=
      mul_le_mul_of_nonneg_left
        (frobNormRect_sq_le_card_mul_complexMatrixOp2_sq A) hfactor
    _ = (n : Real) * ((1 + gamma fp m) / (1 - gamma fp (n + 1))) *
        complexMatrixOp2 (realRectToCMatrix A) ^ 2 := by ring

/-- The additional quadratic-and-higher term produced when (20.11) is used
to replace the computed `R_hat` norm by the source `A` norm. -/
noncomputable def higham20Eq20_13aComputedRemainder
    (fp : FPModel) (m n : Nat) (A_norm : Real) : Real :=
  higham20Eq20_13aRemainder fp m n A_norm +
    (n : Real) * gamma fp (3 * n + 1) *
      ((gamma fp m + gamma fp (n + 1)) /
        (1 - gamma fp (n + 1))) * A_norm ^ 2

/-- Exact coefficient expansion for the source-scaled `(20.13a)` estimate.
The new summand is a product of two gamma-order quantities and therefore is
the finite replacement for the part of `O(u^2)` coming from (20.11). -/
theorem higham20_eq20_13a_computed_R_coefficient_exact
    (fp : FPModel) (m n : Nat) (A_norm : Real)
    (hm : gammaValid fp m) (h3n1 : gammaValid fp (3 * n + 1))
    (hsmall : gamma fp (n + 1) < 1) :
    ((n : Real) * gamma fp m +
        (n : Real) * gamma fp (3 * n + 1) *
          ((1 + gamma fp m) / (1 - gamma fp (n + 1)))) * A_norm ^ 2 =
      higham20Eq20_13aLeading fp m n A_norm +
        higham20Eq20_13aComputedRemainder fp m n A_norm := by
  have hden : 1 - gamma fp (n + 1) ≠ 0 := ne_of_gt (by linarith)
  have hbase :=
    higham20_eq20_13a_gamma_coefficient_exact fp m n A_norm hm h3n1
  calc
    ((n : Real) * gamma fp m +
        (n : Real) * gamma fp (3 * n + 1) *
          ((1 + gamma fp m) / (1 - gamma fp (n + 1)))) * A_norm ^ 2 =
      (((n : Real) * gamma fp m +
          (n : Real) * gamma fp (3 * n + 1)) * A_norm ^ 2) +
        (n : Real) * gamma fp (3 * n + 1) *
          ((gamma fp m + gamma fp (n + 1)) /
            (1 - gamma fp (n + 1))) * A_norm ^ 2 := by
      field_simp [hden]
      ring
    _ = (higham20Eq20_13aLeading fp m n A_norm +
          higham20Eq20_13aRemainder fp m n A_norm) +
        (n : Real) * gamma fp (3 * n + 1) *
          ((gamma fp m + gamma fp (n + 1)) /
            (1 - gamma fp (n + 1))) * A_norm ^ 2 := by
      rw [hbase]
    _ = higham20Eq20_13aLeading fp m n A_norm +
        higham20Eq20_13aComputedRemainder fp m n A_norm := by
      unfold higham20Eq20_13aComputedRemainder
      ring

/-- Equations (20.13a)-(20.13b) with all source norm envelopes discharged.

Unlike the earlier envelope adapter, `absATA` and `absATb` are fixed to the
actual `|A^T||A|` and `|A^T||b|` majorants.  Equation (20.11) supplies the
computed-`R_hat` norm estimate.  The conclusion keeps Higham's exact printed
first-order coefficients and records every additional term in the explicit
`higham20Eq20_13aComputedRemainder`. -/
theorem higham20_eq20_13a_b_normal_equations_source_closed
    (fp : FPModel) (m n : Nat)
    (A : Fin m -> Fin n -> Real) (b : Fin m -> Real)
    (C_hat : Fin n -> Fin n -> Real) (c_hat : Fin n -> Real)
    (R_hat : Fin n -> Fin n -> Real)
    (hn : 0 < n) (hmn : n <= m)
    (hGram : GramProductError n C_hat (rectLSGram A)
      (higham20NormalEqAbsGram A) (gamma fp m))
    (hGramVec : GramVecError n c_hat (rectLSRhs A b)
      (higham20NormalEqAbsRhs A b) (gamma fp m))
    (hChol : CholeskyBackwardError n C_hat R_hat (gamma fp (n + 1)))
    (hR_diag : forall i : Fin n, R_hat i i ≠ 0)
    (hm : gammaValid fp m) (h3n1 : gammaValid fp (3 * n + 1))
    (hsmall : gamma fp (n + 1) < 1) :
    let R_hatT := fun i j : Fin n => R_hat j i
    let y_hat := fl_forwardSub fp n R_hatT c_hat
    let x_hat := fl_backSub fp n R_hat y_hat
    exists (DeltaA : Fin n -> Fin n -> Real) (Deltac : Fin n -> Real),
      (forall i, Finset.univ.sum (fun j : Fin n =>
        (rectLSGram A i j + DeltaA i j) * x_hat j) =
          rectLSRhs A b i + Deltac i) /\
      complexMatrixOp2 (realRectToCMatrix DeltaA) <=
        higham20Eq20_13aLeading fp m n
            (complexMatrixOp2 (realRectToCMatrix A)) +
          higham20Eq20_13aComputedRemainder fp m n
            (complexMatrixOp2 (realRectToCMatrix A)) /\
      vecNorm2 Deltac <=
        higham20Eq20_13bLeading fp m n
            (complexMatrixOp2 (realRectToCMatrix A)) (vecNorm2 b) +
          higham20Eq20_13bRemainder fp m n
            (complexMatrixOp2 (realRectToCMatrix A)) (vecNorm2 b) := by
  dsimp
  have hn1 : gammaValid fp (n + 1) :=
    gammaValid_mono fp (by omega) h3n1
  obtain ⟨DeltaA, Deltac, hEq, hDeltaA, hDeltac⟩ :=
    ls_normal_equations_backward fp n (rectLSGram A) (rectLSRhs A b)
      (higham20NormalEqAbsGram A) (higham20NormalEqAbsRhs A b)
      C_hat c_hat R_hat hGram hGramVec hChol hR_diag hm hn1
  refine ⟨DeltaA, Deltac, hEq, ?_, ?_⟩
  · let Rgram : Fin n -> Fin n -> Real := higham20NormalEqAbsGram R_hat
    let Aop := complexMatrixOp2 (realRectToCMatrix A)
    let rho := (1 + gamma fp m) / (1 - gamma fp (n + 1))
    let majorant : Fin n -> Fin n -> Real := fun i j =>
      gamma fp m * higham20NormalEqAbsGram A i j +
        gamma fp (3 * n + 1) * Rgram i j
    have hgm : 0 <= gamma fp m := gamma_nonneg fp hm
    have hg3 : 0 <= gamma fp (3 * n + 1) := gamma_nonneg fp h3n1
    have hcoeff :=
      higham20_cholesky_solve_coefficient_le_gamma_3n1 fp n h3n1
    have hRgram_nonneg : forall i j, 0 <= Rgram i j := by
      intro i j
      exact Finset.sum_nonneg (fun k _ =>
        mul_nonneg (abs_nonneg _) (abs_nonneg _))
    have hAgram_nonneg : forall i j,
        0 <= higham20NormalEqAbsGram A i j := by
      intro i j
      exact Finset.sum_nonneg (fun k _ =>
        mul_nonneg (abs_nonneg _) (abs_nonneg _))
    have hmajorant_nonneg : forall i j, 0 <= majorant i j := by
      intro i j
      exact add_nonneg (mul_nonneg hgm (hAgram_nonneg i j))
        (mul_nonneg hg3 (hRgram_nonneg i j))
    have hDeltaA_majorant : forall i j, |DeltaA i j| <= majorant i j := by
      intro i j
      calc
        |DeltaA i j| <=
            gamma fp m * higham20NormalEqAbsGram A i j +
              (gamma fp (n + 1) + 2 * gamma fp n + gamma fp n ^ 2) *
                Rgram i j := hDeltaA i j
        _ <= gamma fp m * higham20NormalEqAbsGram A i j +
              gamma fp (3 * n + 1) * Rgram i j := by
          exact add_le_add_right
            (mul_le_mul_of_nonneg_right hcoeff (hRgram_nonneg i j)) _
        _ = majorant i j := rfl
    have hAgram_norm :
        frobNormRect (higham20NormalEqAbsGram A) <= (n : Real) * Aop ^ 2 := by
      exact higham20NormalEqAbsGram_frobNormRect_le A
    have hRgram_norm :
        frobNormRect Rgram <= (n : Real) * rho * Aop ^ 2 := by
      exact higham20_computed_R_absGram_frobNormRect_le_source
        fp A C_hat R_hat hGram hChol hsmall
    have hDeltaA_frob :
        frobNormRect DeltaA <=
          ((n : Real) * gamma fp m +
            (n : Real) * gamma fp (3 * n + 1) * rho) * Aop ^ 2 := by
      calc
        frobNormRect DeltaA <= frobNormRect majorant :=
          frobNormRect_le_of_entry_abs_le DeltaA majorant
            hmajorant_nonneg hDeltaA_majorant
        _ <= frobNormRect
              (fun i j => gamma fp m * higham20NormalEqAbsGram A i j) +
            frobNormRect (fun i j => gamma fp (3 * n + 1) * Rgram i j) :=
          frobNormRect_add_le _ _
        _ = gamma fp m * frobNormRect (higham20NormalEqAbsGram A) +
            gamma fp (3 * n + 1) * frobNormRect Rgram := by
          rw [frobNormRect_smul, frobNormRect_smul,
            abs_of_nonneg hgm, abs_of_nonneg hg3]
        _ <= gamma fp m * ((n : Real) * Aop ^ 2) +
            gamma fp (3 * n + 1) * ((n : Real) * rho * Aop ^ 2) :=
          add_le_add
            (mul_le_mul_of_nonneg_left hAgram_norm hgm)
            (mul_le_mul_of_nonneg_left hRgram_norm hg3)
        _ = ((n : Real) * gamma fp m +
            (n : Real) * gamma fp (3 * n + 1) * rho) * Aop ^ 2 := by ring
    have hfinite_nonneg :
        0 <= ((n : Real) * gamma fp m +
          (n : Real) * gamma fp (3 * n + 1) * rho) * Aop ^ 2 := by
      have hden : 0 < 1 - gamma fp (n + 1) := by linarith
      have hrho : 0 <= rho := by
        exact div_nonneg (add_nonneg zero_le_one hgm) hden.le
      positivity
    have hop :
        complexMatrixOp2 (realRectToCMatrix DeltaA) <=
          ((n : Real) * gamma fp m +
            (n : Real) * gamma fp (3 * n + 1) * rho) * Aop ^ 2 :=
      complexMatrixOp2_realRectToCMatrix_le_of_rectOpNorm2Le DeltaA
        hfinite_nonneg (rectOpNorm2Le_of_frobNormRect_le DeltaA hDeltaA_frob)
    rw [higham20_eq20_13a_computed_R_coefficient_exact
      fp m n Aop hm h3n1 hsmall] at hop
    exact hop
  · let Aop := complexMatrixOp2 (realRectToCMatrix A)
    have hgm : 0 <= gamma fp m := gamma_nonneg fp hm
    have hRhsNorm :
        vecNorm2 (higham20NormalEqAbsRhs A b) <=
          Real.sqrt (n : Real) * Aop * vecNorm2 b :=
      higham20NormalEqAbsRhs_vecNorm2_le hn hmn A b
    have hnormDeltac :
        vecNorm2 Deltac <= gamma fp m *
          vecNorm2 (higham20NormalEqAbsRhs A b) := by
      calc
        vecNorm2 Deltac <=
            vecNorm2 (fun i => gamma fp m * higham20NormalEqAbsRhs A b i) :=
          vecNorm2_le_of_abs_le Deltac
            (fun i => gamma fp m * higham20NormalEqAbsRhs A b i) hDeltac
        _ = gamma fp m * vecNorm2 (higham20NormalEqAbsRhs A b) := by
          rw [vecNorm2_smul, abs_of_nonneg hgm]
    have hfinite :
        vecNorm2 Deltac <=
          Real.sqrt (n : Real) * gamma fp m * Aop * vecNorm2 b := by
      calc
        vecNorm2 Deltac <=
            gamma fp m * vecNorm2 (higham20NormalEqAbsRhs A b) := hnormDeltac
        _ <= gamma fp m *
            (Real.sqrt (n : Real) * Aop * vecNorm2 b) :=
          mul_le_mul_of_nonneg_left hRhsNorm hgm
        _ = Real.sqrt (n : Real) * gamma fp m * Aop * vecNorm2 b := by ring
    rw [higham20_eq20_13b_gamma_coefficient_exact
      fp m n Aop (vecNorm2 b) hm] at hfinite
    exact hfinite

/-- Fully concrete `(20.13a)`-`(20.13b)` endpoint for the repository's
rounded Gram product, rounded Gram right-hand side, Cholesky factorization,
and two rounded triangular solves. -/
theorem higham20_eq20_13a_b_fl_gram_fl_cholesky_source_closed
    (fp : FPModel) (m n : Nat)
    (A : Fin m -> Fin n -> Real) (b : Fin m -> Real)
    (hn : 0 < n) (hmn : n <= m)
    (hsym : forall i j : Fin n,
      fl_matMul fp n m n (fun i k => A k i) A i j =
        fl_matMul fp n m n (fun i k => A k i) A j i)
    (hpiv : forall j : Fin n, 0 <= fl_cholPivot fp n
      (fl_matMul fp n m n (fun i k => A k i) A) j)
    (hdiag : forall j : Fin n,
      fl_cholesky fp n
        (fl_matMul fp n m n (fun i k => A k i) A) j j ≠ 0)
    (hm : gammaValid fp m) (h3n1 : gammaValid fp (3 * n + 1))
    (hsmall : gamma fp (n + 1) < 1) :
    let C_hat := fl_matMul fp n m n (fun i k => A k i) A
    let c_hat := fl_matVec fp n m (fun i k => A k i) b
    let R_hat := fl_cholesky fp n C_hat
    let R_hatT := fun i j : Fin n => R_hat j i
    let y_hat := fl_forwardSub fp n R_hatT c_hat
    let x_hat := fl_backSub fp n R_hat y_hat
    exists (DeltaA : Fin n -> Fin n -> Real) (Deltac : Fin n -> Real),
      (forall i, Finset.univ.sum (fun j : Fin n =>
        (rectLSGram A i j + DeltaA i j) * x_hat j) =
          rectLSRhs A b i + Deltac i) /\
      complexMatrixOp2 (realRectToCMatrix DeltaA) <=
        higham20Eq20_13aLeading fp m n
            (complexMatrixOp2 (realRectToCMatrix A)) +
          higham20Eq20_13aComputedRemainder fp m n
            (complexMatrixOp2 (realRectToCMatrix A)) /\
      vecNorm2 Deltac <=
        higham20Eq20_13bLeading fp m n
            (complexMatrixOp2 (realRectToCMatrix A)) (vecNorm2 b) +
          higham20Eq20_13bRemainder fp m n
            (complexMatrixOp2 (realRectToCMatrix A)) (vecNorm2 b) := by
  dsimp
  have hn1 : gammaValid fp (n + 1) :=
    gammaValid_mono fp (by omega) h3n1
  have hGram : GramProductError n
      (fl_matMul fp n m n (fun i k => A k i) A)
      (rectLSGram A) (higham20NormalEqAbsGram A) (gamma fp m) := by
    simpa [rectLSGram, higham20NormalEqAbsGram] using
      gramProductError_from_fl_matMul fp m n A hm
  have hGramVec : GramVecError n
      (fl_matVec fp n m (fun i k => A k i) b)
      (rectLSRhs A b) (higham20NormalEqAbsRhs A b) (gamma fp m) := by
    simpa [rectLSRhs, higham20NormalEqAbsRhs] using
      gramVecError_from_fl_matVec fp m n A b hm
  exact higham20_eq20_13a_b_normal_equations_source_closed
    fp m n A b
    (fl_matMul fp n m n (fun i k => A k i) A)
    (fl_matVec fp n m (fun i k => A k i) b)
    (fl_cholesky fp n (fl_matMul fp n m n (fun i k => A k i) A))
    hn hmn hGram hGramVec
    (fl_cholesky_backward_error fp n
      (fl_matMul fp n m n (fun i k => A k i) A)
      hsym hn1 hpiv hdiag)
    hdiag hm h3n1 hsmall

end NumStability
