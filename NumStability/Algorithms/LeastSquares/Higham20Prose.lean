-- Source-facing exact prose and symbolic examples from Higham, 2nd ed., Chapter 20.

import NumStability.Algorithms.LeastSquares.LSQRSolve
import NumStability.Algorithms.Underdetermined.Higham21ProjectorNorm
import NumStability.Analysis.HighamChapter7

namespace NumStability

open scoped BigOperators Matrix.Norms.Frobenius

/-! ## The exact 3 by 2 perturbation example on printed page 383 -/

/-- The coefficient matrix in the symbolic `3 x 2` example following
Theorem 20.1 (Higham, 2nd ed., Chapter 20, printed page 383). -/
noncomputable def higham20DeltaExampleA (delta : Real) : Fin 3 -> Fin 2 -> Real :=
  ![![1, 0], ![0, delta], ![0, 0]]

/-- The matrix perturbation in the page-383 symbolic example. -/
noncomputable def higham20DeltaExampleDeltaA (delta : Real) :
    Fin 3 -> Fin 2 -> Real :=
  ![![0, 0], ![0, 0], ![0, delta / 2]]

noncomputable def higham20DeltaExampleB : Fin 3 -> Real := ![1, 0, 1]
noncomputable def higham20DeltaExampleX : Fin 2 -> Real := ![1, 0]
noncomputable def higham20DeltaExampleR : Fin 3 -> Real := ![0, 0, 1]

/-- The perturbed least-squares solution printed in the page-383 example. -/
noncomputable def higham20DeltaExampleY (delta : Real) : Fin 2 -> Real :=
  ![1, 2 / (5 * delta)]

/-- The perturbed residual printed in the page-383 example. -/
noncomputable def higham20DeltaExampleS : Fin 3 -> Real := ![0, -(2 / 5), 4 / 5]

/-- Exact solution and residual identities for the unperturbed side of the
page-383 symbolic example. -/
theorem higham20_delta_example_unperturbed_identities (delta : Real) :
    rectMatMulVec (higham20DeltaExampleA delta) higham20DeltaExampleX =
        fun i => higham20DeltaExampleB i - higham20DeltaExampleR i := by
  funext i
  fin_cases i <;>
    norm_num [higham20DeltaExampleA, higham20DeltaExampleX,
      higham20DeltaExampleB, higham20DeltaExampleR, rectMatMulVec]

/-- Exact solution and residual identities for the perturbed side of the
page-383 symbolic example. -/
theorem higham20_delta_example_perturbed_identities {delta : Real}
    (hdelta : delta ≠ 0) :
    rectMatMulVec
        (fun i j => higham20DeltaExampleA delta i j +
          higham20DeltaExampleDeltaA delta i j)
        (higham20DeltaExampleY delta) =
      fun i => higham20DeltaExampleB i - higham20DeltaExampleS i := by
  funext i
  fin_cases i <;>
    norm_num [higham20DeltaExampleA, higham20DeltaExampleDeltaA,
      higham20DeltaExampleY, higham20DeltaExampleB, higham20DeltaExampleS,
      rectMatMulVec] <;>
    field_simp [hdelta]

/-- Exact normal-equation orthogonality for both residuals in the page-383
symbolic example.  This proves that the displayed `x` and `y` are the two
least-squares minimizers, rather than merely solving the displayed residual
equations. -/
theorem higham20_delta_example_normal_equations (delta : Real) :
    (forall j : Fin 2,
      (∑ i : Fin 3, higham20DeltaExampleA delta i j *
        higham20DeltaExampleR i) = 0) /\
    (forall j : Fin 2,
      (∑ i : Fin 3,
        (higham20DeltaExampleA delta i j +
          higham20DeltaExampleDeltaA delta i j) *
        higham20DeltaExampleS i) = 0) := by
  constructor <;> intro j <;> fin_cases j <;>
    simp [higham20DeltaExampleA, higham20DeltaExampleDeltaA,
      higham20DeltaExampleR, higham20DeltaExampleS, Fin.sum_univ_succ]
  all_goals ring

/-- The two exact relative changes in the page-383 symbolic example.  The
first equality is stated for positive `delta`, as in the source regime.

The source prints `1 / sqrt 5` for the second *relative* change, but direct
calculation gives `||r-s||₂ = 1 / sqrt 5` and `||b||₂ = sqrt 2`; hence the
relative change is `1 / sqrt 10`.  This endpoint records the mathematically
verified value rather than silently reproducing the apparent source typo. -/
theorem higham20_delta_example_relative_changes {delta : Real}
    (hdelta : 0 < delta) :
    vecNorm2 (fun j => higham20DeltaExampleX j - higham20DeltaExampleY delta j) /
        vecNorm2 higham20DeltaExampleX = 2 / (5 * delta) /\
      vecNorm2 (fun i => higham20DeltaExampleR i - higham20DeltaExampleS i) /
        vecNorm2 higham20DeltaExampleB = 1 / Real.sqrt 10 := by
  have hdelta0 : delta ≠ 0 := ne_of_gt hdelta
  constructor
  · rw [show (fun j => higham20DeltaExampleX j - higham20DeltaExampleY delta j) =
        ![0, -(2 / (5 * delta))] by
      funext j
      fin_cases j <;>
        simp [higham20DeltaExampleX, higham20DeltaExampleY]]
    rw [show vecNorm2 (![0, -(2 / (5 * delta))] : Fin 2 -> Real) =
        2 / (5 * delta) by
      unfold vecNorm2 vecNorm2Sq
      rw [show (∑ j : Fin 2, (![0, -(2 / (5 * delta))] : Fin 2 → Real) j ^ 2) =
          (2 / (5 * delta)) ^ 2 by
        simp [Fin.sum_univ_succ]]
      rw [Real.sqrt_sq_eq_abs, abs_of_pos (by positivity : 0 < 2 / (5 * delta))]]
    rw [show vecNorm2 higham20DeltaExampleX = 1 by
      unfold vecNorm2 vecNorm2Sq
      norm_num [higham20DeltaExampleX, Fin.sum_univ_succ]]
    ring
  · rw [show (fun i => higham20DeltaExampleR i - higham20DeltaExampleS i) =
        ![0, 2 / 5, 1 / 5] by
      funext i
      fin_cases i <;>
        norm_num [higham20DeltaExampleR, higham20DeltaExampleS]]
    rw [show vecNorm2 (![0, 2 / 5, 1 / 5] : Fin 3 -> Real) =
        1 / Real.sqrt 5 by
      unfold vecNorm2 vecNorm2Sq
      rw [show (∑ i : Fin 3, (![0, 2 / 5, 1 / 5] : Fin 3 → Real) i ^ 2) =
          (1 / 5 : Real) by
        norm_num [Fin.sum_univ_succ]]
      have hsqrt5 : 0 < Real.sqrt 5 := Real.sqrt_pos.2 (by norm_num)
      rw [show (1 / 5 : Real) = (1 / Real.sqrt 5) ^ 2 by
        rw [div_pow]
        field_simp [ne_of_gt hsqrt5]
        nlinarith [Real.sq_sqrt (by norm_num : (0 : Real) <= 5)]]
      rw [Real.sqrt_sq_eq_abs, abs_of_pos (one_div_pos.mpr hsqrt5)]]
    rw [show vecNorm2 higham20DeltaExampleB = Real.sqrt 2 by
      unfold vecNorm2 vecNorm2Sq
      congr 1
      norm_num [higham20DeltaExampleB, Fin.sum_univ_succ]]
    have hsqrt2 : 0 < Real.sqrt 2 := Real.sqrt_pos.2 (by norm_num)
    have hsqrt5 : 0 < Real.sqrt 5 := Real.sqrt_pos.2 (by norm_num)
    have hsqrt10 : Real.sqrt 10 = Real.sqrt 2 * Real.sqrt 5 := by
      rw [show (10 : Real) = 2 * 5 by norm_num,
        Real.sqrt_mul (by norm_num : (0 : Real) ≤ 2)]
    rw [hsqrt10]
    field_simp [ne_of_gt hsqrt2, ne_of_gt hsqrt5]

/-! ## The exact complementary range-projector norm on printed page 383 -/

/-- Higham, 2nd ed., Chapter 20, printed page 383:

    `||I - A A⁺||₂ = min {1, m - n}`

for a full-column `m`-by-`n` matrix.  The left side is stated in the
repository's exact complexified Euclidean operator-norm API.  Full column rank
is exposed by the left-inverse identity `A⁺ A = I`; the supplied
Moore--Penrose certificate provides symmetry of the range projection `A A⁺`.

The proof applies the exact complementary-domain-projector theorem to the
transposed interface `(A⁺, A)`.  It therefore includes both source branches:
the norm is zero when `m = n`, and it is one when `n < m`. -/
theorem higham20_fullColumn_range_projector_complement_complexMatrixOp2_eq_min_one_sub
    {m n : Nat} (A : Fin m -> Fin n -> Real)
    (Aplus : Fin n -> Fin m -> Real) (hnm : n <= m)
    (hleft : rectMatMul Aplus A = idMatrix n)
    (hMP : RectMoorePenrosePseudoinverse m n A Aplus) :
    complexMatrixOp2
        (realRectToCMatrix
          (fun i j => idMatrix m i j - rectMatMul A Aplus i j)) =
      ((Nat.min 1 (m - n) : Nat) : Real) := by
  exact higham21_projector_complement_complexMatrixOp2_eq_min_one_sub
    Aplus A hnm hleft hMP.range_projection_symmetric

/-! ## The componentwise condition number `cond₂` -/

/-- The nonnegative matrix `|A⁺| |A|` in Higham's definition
`cond₂(A) = || |A⁺| |A| ||₂` on printed page 385.  The pseudoinverse is an
explicit argument so the definition can share the repository's existing
Penrose and full-column-rank APIs. -/
noncomputable def higham20Cond2Matrix {m n : Nat}
    (A : Fin m → Fin n → Real) (Aplus : Fin n → Fin m → Real) :
    Fin n → Fin n → Real :=
  fun j k => ∑ i : Fin m, |Aplus j i| * |A i k|

/-- Higham's page-385 componentwise condition number
`cond₂(A) = || |A⁺| |A| ||₂`. -/
noncomputable def higham20Cond2 {m n : Nat}
    (A : Fin m → Fin n → Real) (Aplus : Fin n → Fin m → Real) : Real :=
  complexMatrixOp2 (realRectToCMatrix (higham20Cond2Matrix A Aplus))

/-- The specialization `cond₂(Aᵀ)` used in the page-385 column-scaling
discussion, written directly as
`|| |(A⁺)ᵀ| |Aᵀ| ||₂`. -/
noncomputable def higham20Cond2Transpose {m n : Nat}
    (A : Fin m → Fin n → Real) (Aplus : Fin n → Fin m → Real) : Real :=
  complexMatrixOp2
    (realRectToCMatrix (fun i k : Fin m =>
      ∑ j : Fin n, |Aplus j i| * |A k j|))

/-! ## Column-scaling invariance of the componentwise bounds -/

noncomputable def higham20ColumnUnscale {n : Nat} (d x : Fin n -> Real) :
    Fin n -> Real := fun j => (d j)⁻¹ * x j

noncomputable def higham20ColumnScaledMajorant {m n : Nat}
    (E : Fin m -> Fin n -> Real) (d : Fin n -> Real) : Fin m -> Fin n -> Real :=
  ch7RectRightScale E (fun j => |d j|)

noncomputable def higham20ColumnScaledAplus {m n : Nat}
    (Aplus : Fin n -> Fin m -> Real) (d : Fin n -> Real) :
    Fin n -> Fin m -> Real :=
  ch7RectLeftScale (fun j => (d j)⁻¹) Aplus

noncomputable def higham20ColumnScaledGramInv {n : Nat}
    (G : Fin n -> Fin n -> Real) (d : Fin n -> Real) : Fin n -> Fin n -> Real :=
  fun j k => (d j)⁻¹ * G j k * (d k)⁻¹

/-- The page-385 quantity `cond₂(Aᵀ)` is exactly invariant when the columns of
`A` are scaled by a nonsingular real diagonal matrix and its pseudoinverse is
transformed contravariantly. -/
theorem higham20_cond2Transpose_column_scaling_invariant {m n : Nat}
    (A : Fin m → Fin n → Real) (Aplus : Fin n → Fin m → Real)
    (d : Fin n → Real) (hd : ∀ j, d j ≠ 0) :
    higham20Cond2Transpose (ch7RectRightScale A d)
        (higham20ColumnScaledAplus Aplus d) =
      higham20Cond2Transpose A Aplus := by
  unfold higham20Cond2Transpose
  congr 1
  ext i k
  unfold realRectToCMatrix higham20ColumnScaledAplus ch7RectLeftScale
    ch7RectRightScale
  congr 1
  apply Finset.sum_congr rfl
  intro j _
  rw [abs_mul, abs_inv, abs_mul]
  calc
    (|d j|⁻¹ * |Aplus j i|) * (|A k j| * |d j|) =
        (|d j|⁻¹ * |d j|) * (|Aplus j i| * |A k j|) := by ring
    _ = |Aplus j i| * |A k j| := by
      rw [inv_mul_cancel₀ (abs_ne_zero.mpr (hd j))]
      ring

theorem higham20_column_scaling_data_majorant_invariant {m n : Nat}
    (E : Fin m -> Fin n -> Real) (f : Fin m -> Real)
    (y d : Fin n -> Real) (hd : forall j, d j ≠ 0) :
    lsComponentwiseDataMajorant (higham20ColumnScaledMajorant E d) f
        (higham20ColumnUnscale d y) =
      lsComponentwiseDataMajorant E f y := by
  funext i
  unfold lsComponentwiseDataMajorant higham20ColumnScaledMajorant
    higham20ColumnUnscale ch7RectRightScale rectMatMulVec absVec
  congr 1
  apply Finset.sum_congr rfl
  intro j _
  rw [abs_mul, abs_inv, mul_assoc, ← mul_assoc (|d j|)]
  rw [mul_inv_cancel₀ (abs_ne_zero.mpr (hd j))]
  ring

theorem higham20_column_scaling_transpose_majorant {m n : Nat}
    (E : Fin m -> Fin n -> Real) (s : Fin m -> Real) (d : Fin n -> Real) :
    lsComponentwiseTransposeMajorant (higham20ColumnScaledMajorant E d) s =
      fun j => |d j| * lsComponentwiseTransposeMajorant E s j := by
  funext j
  unfold lsComponentwiseTransposeMajorant higham20ColumnScaledMajorant
    ch7RectRightScale
  rw [Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro i _
  ring

theorem higham20_column_scaling_projection_invariant {m n : Nat}
    (A : Fin m -> Fin n -> Real) (Aplus : Fin n -> Fin m -> Real)
    (d : Fin n -> Real) (hd : forall j, d j ≠ 0) :
    lsAugmentedProjectionBlock (ch7RectRightScale A d)
        (higham20ColumnScaledAplus Aplus d) =
      lsAugmentedProjectionBlock A Aplus := by
  ext i k
  unfold lsAugmentedProjectionBlock rectMatMulVec ch7RectRightScale
    higham20ColumnScaledAplus ch7RectLeftScale
  congr 1
  apply Finset.sum_congr rfl
  intro j _
  field_simp [hd j]

/-- Exact column-scaling invariance of the printed residual majorant (20.7)
when `E = |A|` is scaled along with the data. -/
theorem higham20_eq20_7_column_scaling_invariant {m n : Nat}
    (A E : Fin m -> Fin n -> Real) (Aplus : Fin n -> Fin m -> Real)
    (f s : Fin m -> Real) (y d : Fin n -> Real)
    (hd : forall j, d j ≠ 0) :
    lsAugmentedEq20_7Majorant (ch7RectRightScale A d)
        (higham20ColumnScaledAplus Aplus d)
        (lsComponentwiseDataMajorant (higham20ColumnScaledMajorant E d) f
          (higham20ColumnUnscale d y))
        (lsComponentwiseTransposeMajorant (higham20ColumnScaledMajorant E d) s) =
      lsAugmentedEq20_7Majorant A Aplus
        (lsComponentwiseDataMajorant E f y)
        (lsComponentwiseTransposeMajorant E s) := by
  rw [higham20_column_scaling_data_majorant_invariant E f y d hd,
    higham20_column_scaling_transpose_majorant E s d]
  funext i
  unfold lsAugmentedEq20_7Majorant
  rw [higham20_column_scaling_projection_invariant A Aplus d hd]
  unfold higham20ColumnScaledAplus ch7RectLeftScale
  congr 1
  apply Finset.sum_congr rfl
  intro j _
  rw [abs_mul, abs_inv]
  calc
    |d j|⁻¹ * |Aplus j i| * (|d j| *
        lsComponentwiseTransposeMajorant E s j) =
        (|d j|⁻¹ * |d j|) *
          (|Aplus j i| * lsComponentwiseTransposeMajorant E s j) := by ring
    _ = |Aplus j i| * lsComponentwiseTransposeMajorant E s j := by
      rw [inv_mul_cancel₀ (abs_ne_zero.mpr (hd j))]
      ring

/-- Exact covariance of the printed solution majorant (20.8): its `j`th
component is multiplied by `|d_j|^{-1}`, exactly matching the coordinate
change `y -> D^{-1} y`. -/
theorem higham20_eq20_8_column_scaling_covariant {m n : Nat}
    (E : Fin m -> Fin n -> Real) (Aplus : Fin n -> Fin m -> Real)
    (G : Fin n -> Fin n -> Real) (f s : Fin m -> Real)
    (y d : Fin n -> Real) (hd : forall j, d j ≠ 0) :
    lsAugmentedEq20_8Majorant (higham20ColumnScaledAplus Aplus d)
        (higham20ColumnScaledGramInv G d)
        (lsComponentwiseDataMajorant (higham20ColumnScaledMajorant E d) f
          (higham20ColumnUnscale d y))
        (lsComponentwiseTransposeMajorant (higham20ColumnScaledMajorant E d) s) =
      fun j => |(d j)⁻¹| *
        lsAugmentedEq20_8Majorant Aplus G
          (lsComponentwiseDataMajorant E f y)
          (lsComponentwiseTransposeMajorant E s) j := by
  rw [higham20_column_scaling_data_majorant_invariant E f y d hd,
    higham20_column_scaling_transpose_majorant E s d]
  funext j
  unfold lsAugmentedEq20_8Majorant higham20ColumnScaledAplus
    higham20ColumnScaledGramInv ch7RectLeftScale rectMatMulVec matMulVec
    absMatrixRect absMatrix
  rw [abs_inv]
  rw [mul_add]
  congr 1
  · rw [Finset.mul_sum]
    apply Finset.sum_congr rfl
    intro i _
    rw [abs_mul, abs_inv]
    ring
  · rw [Finset.mul_sum]
    apply Finset.sum_congr rfl
    intro k _
    rw [abs_mul, abs_mul, abs_inv, abs_inv]
    calc
      (|d j|⁻¹ * |G j k| * |d k|⁻¹) *
          (|d k| * lsComponentwiseTransposeMajorant E s k) =
          |d j|⁻¹ * |G j k| *
            (|d k|⁻¹ * |d k|) *
              lsComponentwiseTransposeMajorant E s k := by ring
      _ = |d j|⁻¹ *
          (|G j k| * lsComponentwiseTransposeMajorant E s k) := by
        rw [inv_mul_cancel₀ (abs_ne_zero.mpr (hd k))]
        ring

/-! ## The page-388 Van der Sluis instantiation -/

/-- Higham, 2nd ed., Chapter 20, printed page 388: if `B` is obtained by
scaling every column of full-column-rank `A` to unit 2-norm, then
`kappa_2(B) <= sqrt(n) min_F kappa_2(A F)`.

The pseudoinverse-side matrix remains explicit, as in the repository's exact
Theorem 7.5 API; `hleft` says it is the full-column left inverse. -/
theorem higham20_van_der_sluis_column_normalization {m n : Nat}
    (hn : 0 < n) (A : Fin m -> Fin n -> Real)
    (Aplus : Fin n -> Fin m -> Real)
    (hleft : forall i j : Fin n,
      (∑ k : Fin m, Aplus i k * A k j) = if i = j then 1 else 0) :
    exists mu : Real,
      IsLeast (ch7Op2RightScaledCondSet A Aplus) mu /\
      ch7Op2RightScaledCond A Aplus
          (ch7ColumnEquilibratingScale2 A)
          (fun j => ch7RectColumnNorm2 A j) <=
        Real.sqrt (n : Real) * mu :=
  theorem7_5_p2_column_equilibration_exists_min_right_scalings_of_rect_left_inverse
    hn A Aplus hleft

/-! ## A genuine sufficient condition for the negative lambda-star branch -/

/-- A left-null vector whose pairing with the residual is nonzero makes the
Rayleigh quotient of the Theorem 20.5 eigenmatrix strictly negative whenever
`mu` and `||y||` are nonzero.  Consequently the printed least eigenvalue
`lambda_*` is negative. -/
theorem higham20_lambdaStar_neg_of_leftNull_residual_pairing {m n : Nat}
    (theta : Real) (A : Fin (m + 1) -> Fin n -> Real)
    (r z : Fin (m + 1) -> Real) (y : Fin n -> Real)
    (hmu : lsNormwiseBackwardErrorMu theta y ≠ 0)
    (hy : y ≠ 0)
    (hleftNull : forall j : Fin n, (∑ i : Fin (m + 1), A i j * z i) = 0)
    (hpair : (∑ i : Fin (m + 1), r i * z i) ≠ 0) :
    lsNormwiseBackwardErrorLambdaStar theta A r y < 0 := by
  let M := lsNormwiseBackwardErrorEigenMatrix theta A r y
  have hmu_pos : 0 < lsNormwiseBackwardErrorMu theta y :=
    lt_of_le_of_ne (lsNormwiseBackwardErrorMu_nonneg theta y) (Ne.symm hmu)
  have hysq_pos : 0 < vecNorm2Sq y := by
    rw [← vecNorm2_sq y]
    exact sq_pos_of_ne_zero (fun h => hy (funext ((vecNorm2_eq_zero_iff y).mp h)))
  have hgram :
      finiteQuadraticForm
          (fun i k : Fin (m + 1) => ∑ j : Fin n, A i j * A k j) z = 0 := by
    rw [finiteQuadraticForm_rowGram_transpose_eq_vecNorm2Sq_rectMatMulVec_finiteTranspose]
    have hz : rectMatMulVec (finiteTranspose A) z = 0 := by
      funext j
      simpa [rectMatMulVec, finiteTranspose, mul_comm] using hleftNull j
    rw [hz]
    simp [vecNorm2Sq]
  have houter :
      finiteQuadraticForm (fun i k : Fin (m + 1) => r i * r k) z =
        (∑ i : Fin (m + 1), r i * z i) ^ 2 := by
    unfold finiteQuadraticForm finiteMatVec
    calc
      (∑ i : Fin (m + 1), z i *
          (∑ j : Fin (m + 1), r i * r j * z j)) =
          ∑ i : Fin (m + 1),
            (z i * r i) * (∑ j : Fin (m + 1), r j * z j) := by
        apply Finset.sum_congr rfl
        intro i _
        have hin :
            (∑ j : Fin (m + 1), r i * r j * z j) =
              r i * (∑ j : Fin (m + 1), r j * z j) := by
          rw [Finset.mul_sum]
          apply Finset.sum_congr rfl
          intro j _
          ring
        rw [hin]
        ring
      _ = (∑ i : Fin (m + 1), z i * r i) *
          (∑ j : Fin (m + 1), r j * z j) := by
        rw [Finset.sum_mul]
      _ = (∑ i : Fin (m + 1), r i * z i) ^ 2 := by
        have hdot : (∑ i : Fin (m + 1), z i * r i) =
            ∑ i : Fin (m + 1), r i * z i := by
          apply Finset.sum_congr rfl
          intro i _
          ring
        rw [hdot]
        ring
  have hpenalty :
      finiteQuadraticForm
          (fun i k : Fin (m + 1) =>
            lsNormwiseBackwardErrorMu theta y *
              (r i * r k / vecNorm2Sq y)) z =
        lsNormwiseBackwardErrorMu theta y *
          ((∑ i : Fin (m + 1), r i * z i) ^ 2 / vecNorm2Sq y) := by
    have hmatrix :
        (fun i k : Fin (m + 1) =>
          lsNormwiseBackwardErrorMu theta y *
            (r i * r k / vecNorm2Sq y)) =
          fun i k : Fin (m + 1) =>
            (lsNormwiseBackwardErrorMu theta y / vecNorm2Sq y) *
              (r i * r k) := by
      ext i k
      ring
    rw [hmatrix,
      finiteQuadraticForm_smul
        (lsNormwiseBackwardErrorMu theta y / vecNorm2Sq y)
        (fun i k : Fin (m + 1) => r i * r k) z,
      houter]
    ring
  have hquad :
      finiteQuadraticForm M z =
        -(lsNormwiseBackwardErrorMu theta y *
          ((∑ i : Fin (m + 1), r i * z i) ^ 2 / vecNorm2Sq y)) := by
    unfold M lsNormwiseBackwardErrorEigenMatrix
    rw [finiteQuadraticForm_sub, hgram, hpenalty]
    ring
  have hquad_neg : finiteQuadraticForm M z < 0 := by
    rw [hquad]
    have hsquare : 0 < (∑ i : Fin (m + 1), r i * z i) ^ 2 :=
      sq_pos_of_ne_zero hpair
    have hquot : 0 <
        (∑ i : Fin (m + 1), r i * z i) ^ 2 / vecNorm2Sq y :=
      div_pos hsquare hysq_pos
    nlinarith [mul_pos hmu_pos hquot]
  have hlower :=
    lsNormwiseBackwardErrorLambdaStar_mul_vecNorm2Sq_le_eigenMatrix_quadraticForm
      theta A r y z
  by_contra hnot
  have hlambda : 0 <= lsNormwiseBackwardErrorLambdaStar theta A r y :=
    le_of_not_gt hnot
  have hprod : 0 <=
      lsNormwiseBackwardErrorLambdaStar theta A r y * vecNorm2Sq z :=
    mul_nonneg hlambda (vecNorm2Sq_nonneg z)
  linarith

end NumStability
