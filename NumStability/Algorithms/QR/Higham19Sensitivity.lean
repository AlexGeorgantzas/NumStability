-- Algorithms/QR/Higham19Sensitivity.lean
--
-- Exact formal statement surfaces for Higham (19.35a/b) and (19.36), the
-- normalized Gram equation and its unconditional quadratic Frobenius
-- majorant, full-factor recovery bounds, and the algebraic/norm composition
-- from Zha sensitivity and formed-Q error to equation (19.37).  The remaining
-- source obligation is the positive-diagonal local-branch theorem converting
-- the quadratic majorant to a uniform linear estimate; this file deliberately
-- does not disguise that step as an assumption of a theorem named "closed".

import Mathlib.LinearAlgebra.Matrix.Block
import NumStability.Algorithms.Cholesky.CholeskyPerturbation
import NumStability.Algorithms.QR.GramSchmidt

namespace NumStability

open scoped BigOperators

namespace H19Sensitivity

/-- Entrywise matrix difference, kept explicit to avoid dependence on a
particular `Matrix` coercion. -/
def diff {m n : ℕ} (A B : Fin m → Fin n → ℝ) : Fin m → Fin n → ℝ :=
  fun i j => A i j - B i j

/-- Entrywise matrix sum. -/
def add {m n : ℕ} (A B : Fin m → Fin n → ℝ) : Fin m → Fin n → ℝ :=
  fun i j => A i j + B i j

/-- Economy-size QR data with the normalization used in Section 19.9:
orthonormal columns and a square upper-triangular factor with nonnegative
diagonal. -/
structure EconomyQR {m n : ℕ} (A Q : Fin m → Fin n → ℝ)
    (R : Fin n → Fin n → ℝ) : Prop where
  orthonormal : GramSchmidtOrthonormalColumns Q
  upper : IsUpperTrapezoidal n n R
  diagonal_nonnegative : ∀ j : Fin n, 0 ≤ R j j
  factorization : A = rectMatMul Q R

/-- Pointwise quantified statement of Stewart's local normwise QR
sensitivity, equations (19.35a) and (19.35b).

The parameter `kappaF` is the source's Frobenius condition number of `A`.
Invertibility of `R` records the printed full-column-rank assumption.  The
conclusion uses the literal relative Frobenius ratios.  `delta` is the meaning
of "for sufficiently small Delta A" and is uniform over every nearby
normalized economy QR factorization.

Because `A,Q,R` are fixed before `c` is chosen, this proposition alone does
*not* express the source's stronger assertion that `c_n` depends only on the
number of columns.  `StewartLocalSensitivitySource` below records that
quantifier order exactly. -/
def StewartLocalSensitivity {m n : ℕ}
    (A Q : Fin m → Fin n → ℝ) (R : Fin n → Fin n → ℝ)
    (kappaF : ℝ) : Prop :=
  EconomyQR A Q R ∧
    (∃ Rinv : Fin n → Fin n → ℝ, IsInverse n R Rinv) ∧
    ∃ c delta : ℝ, 0 ≤ c ∧ 0 < delta ∧
      ∀ (dA dQ : Fin m → Fin n → ℝ) (dR : Fin n → Fin n → ℝ),
        frobNormRect dA < delta →
        EconomyQR (add A dA) (add Q dQ) (add R dR) →
        frobNormRect dR / frobNormRect R ≤
            c * kappaF * (frobNormRect dA / frobNormRect A) ∧
          frobNormRect dQ ≤
            c * kappaF * (frobNormRect dA / frobNormRect A)

/-- Source-strength quantifier order for Stewart's equations (19.35a/b).

The single coefficient `c` is chosen before the row dimension, matrix, and QR
factors, so it depends only on the number of columns `n`, exactly as the
printed `c_n` does.  For an economy QR factorization the Frobenius condition
number is represented by
`||A||_F * ||R⁻¹||₂`.  The Penrose and exact norm bridges below prove that
`R⁻¹Qᵀ` is the Moore--Penrose inverse and has operator norm `||R⁻¹||₂`. -/
def StewartLocalSensitivitySource (n : ℕ) : Prop :=
  ∃ c : ℝ, 0 ≤ c ∧
    ∀ (m : ℕ), n ≤ m →
      ∀ (A Q : Fin m → Fin n → ℝ)
        (R Rinv : Fin n → Fin n → ℝ),
        EconomyQR A Q R → IsInverse n R Rinv →
        ∃ delta : ℝ, 0 < delta ∧
          ∀ (dA dQ : Fin m → Fin n → ℝ)
            (dR : Fin n → Fin n → ℝ),
            frobNormRect dA < delta →
            EconomyQR (add A dA) (add Q dQ) (add R dR) →
            frobNormRect dR / frobNormRect R ≤
                c * (frobNormRect A * rectOpNorm2 Rinv) *
                  (frobNormRect dA / frobNormRect A) ∧
              frobNormRect dQ ≤
                c * (frobNormRect A * rectOpNorm2 Rinv) *
                  (frobNormRect dA / frobNormRect A)

/-- Higham (2nd ed.), Section 19.9, p. 374: the perturbation class used in
Zha's summary is `|dA| <= epsilon * (G * |A|)`.  In particular, `G` is an
`m`-by-`m` nonnegative matrix and juxtaposition in the source is matrix
multiplication, not an entrywise product. -/
def ZhaWeightedPerturbation {m n : ℕ}
    (A dA : Fin m → Fin n → ℝ) (G : Fin m → Fin m → ℝ)
    (epsilon : ℝ) : Prop :=
  ∀ i j,
    |dA i j| ≤ epsilon * rectMatMul G (absMatrixRect A) i j

/-- The matrix appearing in Higham's notation
`cond(R^{-1}) = || |R| |R^{-1}| ||_2`. -/
noncomputable def zhaConditionMatrix {n : ℕ}
    (R Rinv : Fin n → Fin n → ℝ) : Fin n → Fin n → ℝ :=
  rectMatMul (absMatrix n R) (absMatrix n Rinv)

/-- The right-scaled perturbation forcing used in the local QR equations:
`W = Qᵀ ΔA R⁻¹`.  The dimensions are the literal economy-QR dimensions
from Section 19.9. -/
noncomputable def projectedForcing {m n : ℕ}
    (Q dA : Fin m → Fin n → ℝ) (Rinv : Fin n → Fin n → ℝ) :
    Fin n → Fin n → ℝ :=
  rectMatMul (finiteTranspose Q) (rectMatMul dA Rinv)

/-- Tangential change of the economy-size orthogonal factor, `X = Qᵀ ΔQ`. -/
noncomputable def projectedQVariation {m n : ℕ}
    (Q dQ : Fin m → Fin n → ℝ) : Fin n → Fin n → ℝ :=
  rectMatMul (finiteTranspose Q) dQ

/-- Right-scaled triangular change, `T = ΔR R⁻¹`. -/
noncomputable def scaledRVariation {n : ℕ}
    (dR Rinv : Fin n → Fin n → ℝ) : Fin n → Fin n → ℝ :=
  rectMatMul dR Rinv

/-- Exact quantified statement of Zha's columnwise QR sensitivity (19.36).

The quantifier order makes the first-order coefficient `c` depend only on
the dimensions `m,n`.  The source's `G` is square, nonnegative, and has exact
operator 2-norm one.  The two displayed norms are operator 2-norms, and the
printed `O(epsilon^2)` is represented by a local nonnegative coefficient
`K`; no perturbation estimate is assumed as a premise.

The componentwise-to-condition-number forcing lemmas and exact
upper-triangular/skew equations below supply its source-facing hypotheses;
`Higham19SensitivityClosure` proves this proposition from those ingredients
by closing the quantitative local nonlinear majorant argument. -/
def ZhaColumnwiseSensitivity (m n : ℕ) : Prop :=
  n ≤ m ∧
    ∃ c : ℝ, 0 ≤ c ∧
      ∀ (A Q : Fin m → Fin n → ℝ) (R Rinv : Fin n → Fin n → ℝ)
        (G : Fin m → Fin m → ℝ),
        EconomyQR A Q R → IsInverse n R Rinv →
        (∀ i k, 0 ≤ G i k) → rectOpNorm2 G = 1 →
        ∃ K delta : ℝ, 0 ≤ K ∧ 0 < delta ∧
          ∀ (epsilon : ℝ) (dA dQ : Fin m → Fin n → ℝ)
            (dR : Fin n → Fin n → ℝ),
            0 ≤ epsilon → epsilon < delta →
            ZhaWeightedPerturbation A dA G epsilon →
            EconomyQR (add A dA) (add Q dQ) (add R dR) →
            rectOpNorm2 dR / rectOpNorm2 R ≤
                c * epsilon * rectOpNorm2 (zhaConditionMatrix R Rinv) +
                  K * epsilon ^ 2 ∧
              rectOpNorm2 dQ ≤
                c * epsilon * rectOpNorm2 (zhaConditionMatrix R Rinv) +
                  K * epsilon ^ 2

private theorem rectMatMul_mono_left {m n p : ℕ}
    {A B : Fin m → Fin n → ℝ} {C : Fin n → Fin p → ℝ}
    (hAB : ∀ i j, A i j ≤ B i j) (hC : ∀ i j, 0 ≤ C i j) :
    ∀ i j, rectMatMul A C i j ≤ rectMatMul B C i j := by
  intro i j
  unfold rectMatMul
  apply Finset.sum_le_sum
  intro k _
  exact mul_le_mul_of_nonneg_right (hAB i k) (hC k j)

private theorem rectMatMul_mono_right {m n p : ℕ}
    {A : Fin m → Fin n → ℝ} {B C : Fin n → Fin p → ℝ}
    (hA : ∀ i j, 0 ≤ A i j) (hBC : ∀ i j, B i j ≤ C i j) :
    ∀ i j, rectMatMul A B i j ≤ rectMatMul A C i j := by
  intro i j
  unfold rectMatMul
  apply Finset.sum_le_sum
  intro k _
  exact mul_le_mul_of_nonneg_left (hBC k j) (hA i k)

/-- An exact economy QR factorization gives the entrywise majorization
`|A| <= |Q| |R|` used in Zha's componentwise analysis. -/
theorem economyQR_abs_le_abs_factors {m n : ℕ}
    {A Q : Fin m → Fin n → ℝ} {R : Fin n → Fin n → ℝ}
    (hqr : EconomyQR A Q R) :
    ∀ i j,
      absMatrixRect A i j ≤
        rectMatMul (absMatrixRect Q) (absMatrix n R) i j := by
  intro i j
  unfold absMatrixRect
  rw [show A i j = rectMatMul Q R i j by
    exact congrFun (congrFun hqr.factorization i) j]
  unfold rectMatMul absMatrix
  calc
    |∑ k : Fin n, Q i k * R k j| ≤
        ∑ k : Fin n, |Q i k * R k j| :=
      Finset.abs_sum_le_sum_abs _ _
    _ = ∑ k : Fin n, |Q i k| * |R k j| := by
      apply Finset.sum_congr rfl
      intro k _
      exact abs_mul _ _

/-- Orthonormal columns have squared Frobenius norm equal to the number of
columns. -/
theorem frobNormSqRect_eq_nat_of_orthonormal {m n : ℕ}
    {Q : Fin m → Fin n → ℝ}
    (hQ : GramSchmidtOrthonormalColumns Q) :
    frobNormSqRect Q = (n : ℝ) := by
  rw [frobNormSqRect_eq_sum_vecNorm2Sq_cols]
  calc
    (∑ j : Fin n, vecNorm2Sq (fun i : Fin m => Q i j)) =
        ∑ _j : Fin n, (1 : ℝ) := by
      apply Finset.sum_congr rfl
      intro j _
      have hj := hQ j j
      simpa [rectangularGram, matMulRect, finiteTranspose, idMatrix,
        vecNorm2Sq, pow_two] using hj
    _ = (n : ℝ) := by simp

/-- Orthonormal columns have Frobenius norm `sqrt n`. -/
theorem frobNormRect_eq_sqrt_nat_of_orthonormal {m n : ℕ}
    {Q : Fin m → Fin n → ℝ}
    (hQ : GramSchmidtOrthonormalColumns Q) :
    frobNormRect Q = Real.sqrt (n : ℝ) := by
  unfold frobNormRect
  rw [frobNormSqRect_eq_nat_of_orthonormal hQ]

set_option maxHeartbeats 1000000 in
/-- Converse to `rectOpNorm2Le_rectOpNorm2`: a rectangular vector-action
certificate bounds the exact Euclidean operator norm. -/
theorem rectOpNorm2_le_of_rectOpNorm2Le {m n : ℕ}
    (M : Fin m → Fin n → ℝ) {c : ℝ}
    (hc : 0 ≤ c) (hM : rectOpNorm2Le M c) :
    rectOpNorm2 M ≤ c := by
  unfold rectOpNorm2
  rw [Matrix.l2_opNorm_def]
  refine ContinuousLinearMap.opNorm_le_bound _ hc ?_
  intro x
  let y : Fin n → ℝ := WithLp.ofLp x
  have hxnorm : ‖x‖ = vecNorm2 y := by
    unfold vecNorm2 vecNorm2Sq y
    rw [EuclideanSpace.norm_eq]
    simp [Real.norm_eq_abs, sq_abs]
  have hynorm :
      ‖((Matrix.toEuclideanLin ≪≫ₗ LinearMap.toContinuousLinearMap)
          ((M : Matrix (Fin m) (Fin n) ℝ))) x‖ =
        vecNorm2 (rectMatMulVec M y) := by
    unfold vecNorm2 vecNorm2Sq rectMatMulVec y
    rw [EuclideanSpace.norm_eq]
    simp [Matrix.toLpLin_apply, Matrix.mulVec, dotProduct,
      Real.norm_eq_abs, sq_abs]
  calc
    ‖((Matrix.toEuclideanLin ≪≫ₗ LinearMap.toContinuousLinearMap)
          ((M : Matrix (Fin m) (Fin n) ℝ))) x‖
        = vecNorm2 (rectMatMulVec M y) := hynorm
    _ ≤ c * vecNorm2 y := hM y
    _ = c * ‖x‖ := by rw [hxnorm]

/-- The economy-QR pseudoinverse candidate `R⁻¹Qᵀ`. -/
noncomputable def economyQRPseudoinverse {m n : ℕ}
    (Q : Fin m → Fin n → ℝ) (Rinv : Fin n → Fin n → ℝ) :
    Fin n → Fin m → ℝ :=
  rectMatMul Rinv (finiteTranspose Q)

/-- For an exact full-column-rank economy QR factorization,
`R⁻¹Qᵀ` is a left inverse of `A`. -/
theorem economyQR_pseudoinverse_left_inverse {m n : ℕ}
    {A Q : Fin m → Fin n → ℝ} {R Rinv : Fin n → Fin n → ℝ}
    (hqr : EconomyQR A Q R) (hInv : IsInverse n R Rinv) :
    rectMatMul (economyQRPseudoinverse Q Rinv) A = idMatrix n := by
  have hQtQ : rectMatMul (finiteTranspose Q) Q = idMatrix n := by
    ext i j
    exact hqr.orthonormal i j
  have hRinvR : rectMatMul Rinv R = idMatrix n := by
    ext i j
    exact hInv.1 i j
  rw [hqr.factorization, economyQRPseudoinverse]
  rw [rectMatMul_assoc Rinv (finiteTranspose Q) (rectMatMul Q R)]
  rw [← rectMatMul_assoc (finiteTranspose Q) Q R, hQtQ,
    rectMatMul_id_left, hRinvR]

/-- The range projection of the economy-QR pseudoinverse candidate is
`Q Qᵀ`, hence is symmetric. -/
theorem economyQR_pseudoinverse_range_projection_symmetric {m n : ℕ}
    {A Q : Fin m → Fin n → ℝ} {R Rinv : Fin n → Fin n → ℝ}
    (hqr : EconomyQR A Q R) (hInv : IsInverse n R Rinv) :
    IsSymmetricFiniteMatrix
      (rectMatMul A (economyQRPseudoinverse Q Rinv)) := by
  have hRRinv : rectMatMul R Rinv = idMatrix n := by
    ext i j
    exact hInv.2 i j
  have hprojection :
      rectMatMul A (economyQRPseudoinverse Q Rinv) =
        rectMatMul Q (finiteTranspose Q) := by
    rw [hqr.factorization, economyQRPseudoinverse]
    rw [rectMatMul_assoc Q R (rectMatMul Rinv (finiteTranspose Q))]
    rw [← rectMatMul_assoc R Rinv (finiteTranspose Q), hRRinv,
      rectMatMul_id_left]
  rw [hprojection]
  intro i j
  unfold rectMatMul finiteTranspose
  apply Finset.sum_congr rfl
  intro k _
  ring

/-- The economy-QR candidate satisfies all four Moore--Penrose equations.

The four clauses are kept in the repository's rectangular matrix language so
Chapter 19 does not depend backwards on the Chapter 20/21 pseudoinverse
packaging. -/
theorem economyQR_pseudoinverse_penrose_equations {m n : ℕ}
    {A Q : Fin m → Fin n → ℝ} {R Rinv : Fin n → Fin n → ℝ}
    (hqr : EconomyQR A Q R) (hInv : IsInverse n R Rinv) :
    let Aplus := economyQRPseudoinverse Q Rinv
    rectMatMul (rectMatMul A Aplus) A = A ∧
      rectMatMul (rectMatMul Aplus A) Aplus = Aplus ∧
      IsSymmetricFiniteMatrix (rectMatMul A Aplus) ∧
      IsSymmetricFiniteMatrix (rectMatMul Aplus A) := by
  dsimp only
  let Aplus : Fin n → Fin m → ℝ := economyQRPseudoinverse Q Rinv
  have hleft : rectMatMul Aplus A = idMatrix n := by
    simpa [Aplus] using economyQR_pseudoinverse_left_inverse hqr hInv
  refine ⟨?_, ?_, ?_, ?_⟩
  · rw [rectMatMul_assoc, hleft, rectMatMul_id_right]
  · rw [hleft, rectMatMul_id_left]
  · simpa [Aplus] using
      economyQR_pseudoinverse_range_projection_symmetric hqr hInv
  · rw [hleft]
    intro i j
    simp [idMatrix, eq_comm]

/-- The operator 2-norm of the economy-QR pseudoinverse candidate is exactly
the operator 2-norm of `R⁻¹`:
`||R⁻¹Qᵀ||₂ = ||R⁻¹||₂`.

The upper bound uses that `Qᵀ` is nonexpansive.  The reverse bound follows
from `(R⁻¹Qᵀ)Q=R⁻¹` and nonexpansiveness of `Q`. -/
theorem economyQR_pseudoinverse_rectOpNorm2_eq {m n : ℕ}
    {A Q : Fin m → Fin n → ℝ} {R Rinv : Fin n → Fin n → ℝ}
    (hqr : EconomyQR A Q R) :
    rectOpNorm2 (economyQRPseudoinverse Q Rinv) = rectOpNorm2 Rinv := by
  let Aplus : Fin n → Fin m → ℝ := economyQRPseudoinverse Q Rinv
  have hQ : rectOpNorm2Le Q 1 := hqr.orthonormal.rectOpNorm2Le_one
  have hQt : rectOpNorm2Le (finiteTranspose Q) 1 :=
    rectOpNorm2Le_finiteTranspose_of_rectOpNorm2Le Q (by norm_num) hQ
  have hupperCert : rectOpNorm2Le Aplus (rectOpNorm2 Rinv * 1) := by
    simpa [Aplus, economyQRPseudoinverse] using
      (rectOpNorm2Le_rectMatMul Rinv (finiteTranspose Q)
        (rectOpNorm2_nonneg Rinv) (rectOpNorm2Le_rectOpNorm2 Rinv) hQt)
  have hupper : rectOpNorm2 Aplus ≤ rectOpNorm2 Rinv := by
    have h := rectOpNorm2_le_of_rectOpNorm2Le Aplus
      (mul_nonneg (rectOpNorm2_nonneg Rinv) (by norm_num)) hupperCert
    simpa using h
  have hQtQ : rectMatMul (finiteTranspose Q) Q = idMatrix n := by
    ext i j
    exact hqr.orthonormal i j
  have hAplusQ : rectMatMul Aplus Q = Rinv := by
    simp only [Aplus, economyQRPseudoinverse]
    rw [rectMatMul_assoc, hQtQ, rectMatMul_id_right]
  have hlowerCert :
      rectOpNorm2Le (rectMatMul Aplus Q) (rectOpNorm2 Aplus * 1) :=
    rectOpNorm2Le_rectMatMul Aplus Q (rectOpNorm2_nonneg Aplus)
      (rectOpNorm2Le_rectOpNorm2 Aplus) hQ
  have hlower : rectOpNorm2 Rinv ≤ rectOpNorm2 Aplus := by
    have h := rectOpNorm2_le_of_rectOpNorm2Le (rectMatMul Aplus Q)
      (mul_nonneg (rectOpNorm2_nonneg Aplus) (by norm_num)) hlowerCert
    rw [hAplusQ] at h
    simpa using h
  exact le_antisymm hupper hlower

/-- The exact factor perturbation identity.  This is the nonlinear equation
from which QR sensitivity proofs split the first-order and quadratic terms. -/
theorem economyQR_perturbation_identity {m n : ℕ}
    {A Q dA dQ : Fin m → Fin n → ℝ}
    {R dR : Fin n → Fin n → ℝ}
    (hbase : EconomyQR A Q R)
    (hpert : EconomyQR (add A dA) (add Q dQ) (add R dR)) :
    dA = fun i j =>
      rectMatMul dQ R i j + rectMatMul Q dR i j +
        rectMatMul dQ dR i j := by
  funext i j
  have hA := congrFun (congrFun hbase.factorization i) j
  have hAp := congrFun (congrFun hpert.factorization i) j
  unfold add at hAp
  have hexpand :
      rectMatMul (fun i j => Q i j + dQ i j)
          (fun i j => R i j + dR i j) i j =
        rectMatMul Q R i j + rectMatMul dQ R i j +
          rectMatMul Q dR i j + rectMatMul dQ dR i j := by
    unfold rectMatMul
    simp_rw [add_mul, mul_add, Finset.sum_add_distrib]
    ring
  rw [hexpand] at hAp
  linarith

/-- Multiplying the exact perturbation identity by a right inverse of `R`
isolates `dQ` and the scaled triangular perturbation `dR R^{-1}`. -/
theorem economyQR_perturbation_right_inverse_identity {m n : ℕ}
    {A Q dA dQ : Fin m → Fin n → ℝ}
    {R dR Rinv : Fin n → Fin n → ℝ}
    (hbase : EconomyQR A Q R)
    (hpert : EconomyQR (add A dA) (add Q dQ) (add R dR))
    (hRright : IsRightInverse n R Rinv) :
    rectMatMul dA Rinv = fun i j =>
      dQ i j + rectMatMul Q (rectMatMul dR Rinv) i j +
        rectMatMul dQ (rectMatMul dR Rinv) i j := by
  have hperturb := economyQR_perturbation_identity hbase hpert
  have hRR : rectMatMul R Rinv = idMatrix n := by
    funext i j
    exact hRright i j
  rw [hperturb, rectMatMul_add_left, rectMatMul_add_left]
  rw [rectMatMul_assoc, rectMatMul_assoc, rectMatMul_assoc, hRR]
  rw [rectMatMul_id_right]

/-- Right scaling by the base triangular inverse gives an exact normalized QR
factorization

`Q + dA R⁻¹ = (Q + dQ) (I + dR R⁻¹)`.

This is the convenient Cholesky/Gram starting point for the local sensitivity
majorant.  It is derived from the two actual QR factorizations and a right
inverse; no small-factor-variation premise is used. -/
theorem economyQR_normalized_perturbation_factorization {m n : ℕ}
    {A Q dA dQ : Fin m → Fin n → ℝ}
    {R dR Rinv : Fin n → Fin n → ℝ}
    (hbase : EconomyQR A Q R)
    (hpert : EconomyQR (add A dA) (add Q dQ) (add R dR))
    (hRright : IsRightInverse n R Rinv) :
    add Q (rectMatMul dA Rinv) =
      rectMatMul (add Q dQ)
        (add (idMatrix n) (scaledRVariation dR Rinv)) := by
  have hright := economyQR_perturbation_right_inverse_identity
    hbase hpert hRright
  funext i j
  have hij := congrFun (congrFun hright i) j
  unfold add
  rw [hij]
  unfold rectMatMul
  simp_rw [mul_add, Finset.sum_add_distrib]
  have hid :
      (∑ x : Fin n, (Q i x + dQ i x) * idMatrix n x j) =
        Q i j + dQ i j := by
    simpa [rectMatMul, add] using
      congrFun (congrFun (rectMatMul_id_right (add Q dQ)) i) j
  rw [hid]
  simp only [scaledRVariation, rectMatMul]
  simp_rw [add_mul, Finset.sum_add_distrib]
  ring

/-- Symmetric forcing in the normalized Gram equation:
`QᵀD + DᵀQ + DᵀD`. -/
noncomputable def normalizedGramForcing {m n : ℕ}
    (Q D : Fin m → Fin n → ℝ) : Fin n → Fin n → ℝ :=
  fun i j =>
    rectMatMul (finiteTranspose Q) D i j +
      rectMatMul (finiteTranspose D) Q i j +
      rectMatMul (finiteTranspose D) D i j

/-- Exact normalized Gram equation for the scaled triangular variation.

Writing `D = dA R⁻¹` and `T = dR R⁻¹`, orthonormality of the
perturbed `Q` factor and
`Q + D = (Q+dQ)(I+T)` give

`T + Tᵀ + TᵀT = QᵀD + DᵀQ + DᵀD`.

This equation removes `dQ` entirely from the triangular-factor majorant. -/
theorem economyQR_scaledRVariation_gram_identity {m n : ℕ}
    {A Q dA dQ : Fin m → Fin n → ℝ}
    {R dR Rinv : Fin n → Fin n → ℝ}
    (hbase : EconomyQR A Q R)
    (hpert : EconomyQR (add A dA) (add Q dQ) (add R dR))
    (hRright : IsRightInverse n R Rinv) :
    let D := rectMatMul dA Rinv
    let T := scaledRVariation dR Rinv
    ∀ i j : Fin n,
      T i j + T j i + rectMatMul (finiteTranspose T) T i j =
        normalizedGramForcing Q D i j := by
  dsimp only
  let D : Fin m → Fin n → ℝ := rectMatMul dA Rinv
  let T : Fin n → Fin n → ℝ := scaledRVariation dR Rinv
  let S : Fin n → Fin n → ℝ := add (idMatrix n) T
  let Qp : Fin m → Fin n → ℝ := add Q dQ
  have hfac : add Q D = rectMatMul Qp S := by
    simpa [D, T, S, Qp] using
      (economyQR_normalized_perturbation_factorization hbase hpert hRright)
  have hgram :
      rectangularGram (add Q D) =
        rectMatMul (finiteTranspose S) S := by
    rw [hfac]
    simpa [matMulRect_eq_rectMatMul] using
      (rectangularGram_matMulRect_of_orthonormal_left
        hpert.orthonormal S)
  have hleft :
      gramSchmidtOrthogonalityResidual (add Q D) =
        normalizedGramForcing Q D := by
    have hexp := gramSchmidtOrthogonalityResidual_eq_close_expansion
      (Qhat := add Q D) (Q := Q) hbase.orthonormal
    funext i j
    have hij := congrFun (congrFun hexp i) j
    simpa [normalizedGramForcing, add, rectMatMul, finiteTranspose] using hij
  intro i j
  have hgramij := congrFun (congrFun hgram i) j
  have hleftij := congrFun (congrFun hleft i) j
  unfold gramSchmidtOrthogonalityResidual at hleftij
  rw [hgramij] at hleftij
  have hsexpand :
      rectMatMul (finiteTranspose S) S i j - idMatrix n i j =
        T i j + T j i + rectMatMul (finiteTranspose T) T i j := by
    simp only [S, add, rectMatMul, finiteTranspose]
    simp_rw [add_mul, mul_add, Finset.sum_add_distrib]
    have hleftId :
        (∑ x : Fin n, idMatrix n x i * T x j) = T i j := by
      simp [idMatrix]
    have hrightId :
        (∑ x : Fin n, T x i * idMatrix n x j) = T j i := by
      simpa [rectMatMul, finiteTranspose] using
        congrFun (congrFun (rectMatMul_id_right (finiteTranspose T)) i) j
    have hidId :
        (∑ x : Fin n, idMatrix n x i * idMatrix n x j) =
          idMatrix n i j := by
      simp [idMatrix, eq_comm]
    rw [hleftId, hrightId, hidId]
    ring
  rw [hsexpand] at hleftij
  exact hleftij

/-- Unconditional quadratic Frobenius majorant for the scaled triangular QR
variation.

With `d = ||dA R⁻¹||_F` and `t = ||dR R⁻¹||_F`, the exact Gram
equation and the upper-triangular `up` projection give

`t ≤ (2d + d² + t²) / √2`.

This is the nonlinear majorant equation behind Stewart's local estimate.  It
does not assume `t` is small.  Converting it into the source's uniform linear
bound still requires the genuine positive-diagonal/local-branch theorem that
rules out the large quadratic root when `d` is sufficiently small. -/
theorem economyQR_scaledRVariation_frob_quadratic_majorant {m n : ℕ}
    {A Q dA dQ : Fin m → Fin n → ℝ}
    {R dR Rinv : Fin n → Fin n → ℝ}
    (hbase : EconomyQR A Q R)
    (hpert : EconomyQR (add A dA) (add Q dQ) (add R dR))
    (hInv : IsInverse n R Rinv) :
    let D := rectMatMul dA Rinv
    let T := scaledRVariation dR Rinv
    frobNormRect T ≤
      (2 * frobNormRect D + frobNormRect D ^ 2 +
          frobNormRect T ^ 2) / Real.sqrt 2 := by
  dsimp only
  let D : Fin m → Fin n → ℝ := rectMatMul dA Rinv
  let T : Fin n → Fin n → ℝ := scaledRVariation dR Rinv
  let E : Fin n → Fin n → ℝ := normalizedGramForcing Q D
  let TT : Fin n → Fin n → ℝ :=
    rectMatMul (finiteTranspose T) T
  let Y : Fin n → Fin n → ℝ := fun i j => E i j - TT i j
  have hgram := economyQR_scaledRVariation_gram_identity
    hbase hpert hInv.2
  have hYeq : ∀ i j : Fin n, Y i j = T i j + T j i := by
    intro i j
    have hij := hgram i j
    simp only [Y, E, TT]
    linarith
  have hYsym : ∀ i j : Fin n, Y i j = Y j i := by
    intro i j
    rw [hYeq i j, hYeq j i]
    ring
  have hdRupper : ∀ i j : Fin n, j.val < i.val → dR i j = 0 := by
    intro i j hji
    have hR := hbase.upper i j hji
    have hRdR := hpert.upper i j hji
    unfold add at hRdR
    linarith
  have hRinvUpper : ∀ i j : Fin n, j.val < i.val → Rinv i j = 0 := by
    let RM : Matrix (Fin n) (Fin n) ℝ := R
    let RinvM : Matrix (Fin n) (Fin n) ℝ := Rinv
    have hmul : RM * RinvM = 1 := by
      ext i j
      simpa [RM, RinvM, Matrix.mul_apply, rectMatMul, idMatrix] using
        hInv.2 i j
    letI : Invertible RM := invertibleOfRightInverse RM RinvM hmul
    have hRblock : Matrix.BlockTriangular RM id := by
      intro i j hji
      exact hbase.upper i j (by simpa [RM] using hji)
    have hinvBlock : Matrix.BlockTriangular RM⁻¹ id :=
      Matrix.blockTriangular_inv_of_blockTriangular hRblock
    have hspecified : ⅟ RM = RinvM := invOf_eq_right_inv hmul
    have hnonsing : RM⁻¹ = RinvM := by
      rw [← Matrix.invOf_eq_nonsing_inv]
      exact hspecified
    rw [hnonsing] at hinvBlock
    intro i j hji
    exact hinvBlock (by simpa [RinvM] using hji)
  have hTupper : ∀ i j : Fin n, j.val < i.val → T i j = 0 := by
    simpa [T, scaledRVariation, rectMatMul, matMul] using
      (matMul_upper_upper dR Rinv hdRupper hRinvUpper)
  have hTrecover : ∀ i j : Fin n, T i j = upHalf Y i j := by
    have hYfun : Y = fun i j => T i j + T j i := by
      funext i j
      exact hYeq i j
    intro i j
    rw [hYfun]
    exact (upHalf_add_transpose T hTupper i j).symm
  have hT_up : frobNormRect T = frobNormRect (upHalf Y) := by
    congr 1
    funext i j
    exact hTrecover i j
  have hUp : frobNormRect (upHalf Y) ≤
      frobNormRect Y / Real.sqrt 2 := by
    simpa [frobNormRect_eq_frobNorm] using
      (frobNorm_upHalf_le Y hYsym)
  have hYtri : frobNormRect Y ≤
      frobNormRect E + frobNormRect TT := by
    simpa [Y] using frobNormRect_sub_le E TT
  have hQT : rectOpNorm2Le (finiteTranspose Q) 1 :=
    rectOpNorm2Le_finiteTranspose_of_rectOpNorm2Le Q (by norm_num)
      hbase.orthonormal.rectOpNorm2Le_one
  have hQD : frobNormRect (rectMatMul (finiteTranspose Q) D) ≤
      frobNormRect D := by
    have h := frobNormRect_rectMatMul_le_mul_of_rectOpNorm2Le
      (finiteTranspose Q) D (by norm_num) hQT
    simpa using h
  have hDtQ : frobNormRect (rectMatMul (finiteTranspose D) Q) ≤
      frobNormRect D := by
    have h := frobNormRect_rectMatMul_le_mul_of_transpose_rectOpNorm2Le
      (finiteTranspose D) Q (by norm_num) hQT
    simpa [frobNormRect_finiteTranspose] using h
  have hDtD : frobNormRect (rectMatMul (finiteTranspose D) D) ≤
      frobNormRect D ^ 2 := by
    have h := frobNormRect_rectMatMul_le (finiteTranspose D) D
    simpa [frobNormRect_finiteTranspose, pow_two] using h
  have hEtri : frobNormRect E ≤
      frobNormRect (rectMatMul (finiteTranspose Q) D) +
        frobNormRect (rectMatMul (finiteTranspose D) Q) +
        frobNormRect (rectMatMul (finiteTranspose D) D) := by
    have h12 := frobNormRect_add_le
      (rectMatMul (finiteTranspose Q) D)
      (rectMatMul (finiteTranspose D) Q)
    have h123 := frobNormRect_add_le
      (fun i j => rectMatMul (finiteTranspose Q) D i j +
        rectMatMul (finiteTranspose D) Q i j)
      (rectMatMul (finiteTranspose D) D)
    calc
      frobNormRect E ≤
          frobNormRect (fun i j =>
            rectMatMul (finiteTranspose Q) D i j +
              rectMatMul (finiteTranspose D) Q i j) +
            frobNormRect (rectMatMul (finiteTranspose D) D) := by
        simpa [E, normalizedGramForcing] using h123
      _ ≤
          (frobNormRect (rectMatMul (finiteTranspose Q) D) +
            frobNormRect (rectMatMul (finiteTranspose D) Q)) +
            frobNormRect (rectMatMul (finiteTranspose D) D) :=
        add_le_add h12 le_rfl
  have hE : frobNormRect E ≤
      2 * frobNormRect D + frobNormRect D ^ 2 := by
    calc
      frobNormRect E ≤
          frobNormRect (rectMatMul (finiteTranspose Q) D) +
            frobNormRect (rectMatMul (finiteTranspose D) Q) +
            frobNormRect (rectMatMul (finiteTranspose D) D) := hEtri
      _ ≤ frobNormRect D + frobNormRect D + frobNormRect D ^ 2 :=
        add_le_add (add_le_add hQD hDtQ) hDtD
      _ = 2 * frobNormRect D + frobNormRect D ^ 2 := by ring
  have hTT : frobNormRect TT ≤ frobNormRect T ^ 2 := by
    have h := frobNormRect_rectMatMul_le (finiteTranspose T) T
    simpa [TT, frobNormRect_finiteTranspose, pow_two] using h
  calc
    frobNormRect T = frobNormRect (upHalf Y) := hT_up
    _ ≤ frobNormRect Y / Real.sqrt 2 := hUp
    _ ≤ (frobNormRect E + frobNormRect TT) / Real.sqrt 2 :=
      div_le_div_of_nonneg_right hYtri (Real.sqrt_nonneg _)
    _ ≤ ((2 * frobNormRect D + frobNormRect D ^ 2) +
          frobNormRect T ^ 2) / Real.sqrt 2 := by
      apply div_le_div_of_nonneg_right _ (Real.sqrt_nonneg _)
      exact add_le_add hE hTT
    _ = (2 * frobNormRect D + frobNormRect D ^ 2 +
          frobNormRect T ^ 2) / Real.sqrt 2 := by ring

/-- Once the triangular variation is controlled, the full rectangular
orthogonal-factor variation obeys the exact source-dimensional estimate

`||dQ||_F ≤ ||dA R⁻¹||_F + ||dR R⁻¹||_F`.

It follows directly from
`dA R⁻¹ = dQ + (Q+dQ)(dR R⁻¹)` and nonexpansiveness of an
orthonormal-column left factor. -/
theorem economyQR_factorVariation_frob_le_forcing_add_scaledR {m n : ℕ}
    {A Q dA dQ : Fin m → Fin n → ℝ}
    {R dR Rinv : Fin n → Fin n → ℝ}
    (hbase : EconomyQR A Q R)
    (hpert : EconomyQR (add A dA) (add Q dQ) (add R dR))
    (hRright : IsRightInverse n R Rinv) :
    let D := rectMatMul dA Rinv
    let T := scaledRVariation dR Rinv
    frobNormRect dQ ≤ frobNormRect D + frobNormRect T := by
  dsimp only
  let D : Fin m → Fin n → ℝ := rectMatMul dA Rinv
  let T : Fin n → Fin n → ℝ := scaledRVariation dR Rinv
  let Qp : Fin m → Fin n → ℝ := add Q dQ
  have hright := economyQR_perturbation_right_inverse_identity
    hbase hpert hRright
  have hdiff : (fun i j => D i j - dQ i j) = rectMatMul Qp T := by
    funext i j
    have hij := congrFun (congrFun hright i) j
    simp only [D, T, Qp, add, rectMatMul] at hij ⊢
    simp_rw [add_mul, Finset.sum_add_distrib]
    simp only [scaledRVariation, rectMatMul]
    linarith
  have hdQeq : dQ = fun i j => D i j - rectMatMul Qp T i j := by
    funext i j
    have hij := congrFun (congrFun hdiff i) j
    linarith
  have hQpTnorm : frobNormRect (rectMatMul Qp T) ≤ frobNormRect T := by
    have hQp : rectOpNorm2Le Qp 1 :=
      hpert.orthonormal.rectOpNorm2Le_one
    have h := frobNormRect_rectMatMul_le_mul_of_rectOpNorm2Le
      Qp T (by norm_num) hQp
    simpa using h
  rw [hdQeq]
  exact (frobNormRect_sub_le D (rectMatMul Qp T)).trans
    (add_le_add le_rfl hQpTnorm)

/-- A two-sided inverse recovers the unscaled triangular perturbation from
`T = dR R⁻¹`: `dR = T R`. -/
theorem deltaR_eq_scaledRVariation_mul {n : ℕ}
    {R dR Rinv : Fin n → Fin n → ℝ}
    (hInv : IsInverse n R Rinv) :
    dR = rectMatMul (scaledRVariation dR Rinv) R := by
  have hRinvR : rectMatMul Rinv R = idMatrix n := by
    funext i j
    exact hInv.1 i j
  rw [scaledRVariation, rectMatMul_assoc, hRinvR, rectMatMul_id_right]

/-- Frobenius recovery bound for the source's relative `dR` estimate. -/
theorem deltaR_frobNormRect_le_scaledRVariation_mul_frobNormRect {n : ℕ}
    {R dR Rinv : Fin n → Fin n → ℝ}
    (hInv : IsInverse n R Rinv) :
    frobNormRect dR ≤
      frobNormRect (scaledRVariation dR Rinv) * frobNormRect R := by
  calc
    frobNormRect dR =
        frobNormRect (rectMatMul (scaledRVariation dR Rinv) R) := by
      exact congrArg (fun M => frobNormRect M)
        (deltaR_eq_scaledRVariation_mul
          (R := R) (dR := dR) (Rinv := Rinv) hInv)
    _ ≤ frobNormRect (scaledRVariation dR Rinv) * frobNormRect R :=
      frobNormRect_rectMatMul_le _ _

/-- Operator-2 recovery bound for the source's relative `dR` estimate. -/
theorem deltaR_rectOpNorm2_le_scaledRVariation_mul_rectOpNorm2 {n : ℕ}
    {R dR Rinv : Fin n → Fin n → ℝ}
    (hInv : IsInverse n R Rinv) :
    rectOpNorm2 dR ≤
      rectOpNorm2 (scaledRVariation dR Rinv) * rectOpNorm2 R := by
  have hT := rectOpNorm2Le_rectOpNorm2 (scaledRVariation dR Rinv)
  have hR := rectOpNorm2Le_rectOpNorm2 R
  have hprod := rectOpNorm2Le_rectMatMul
    (scaledRVariation dR Rinv) R
    (rectOpNorm2_nonneg (scaledRVariation dR Rinv)) hT hR
  calc
    rectOpNorm2 dR =
        rectOpNorm2 (rectMatMul (scaledRVariation dR Rinv) R) := by
      exact congrArg (fun M => rectOpNorm2 M)
        (deltaR_eq_scaledRVariation_mul
          (R := R) (dR := dR) (Rinv := Rinv) hInv)
    _ ≤ rectOpNorm2 (scaledRVariation dR Rinv) * rectOpNorm2 R :=
      rectOpNorm2_le_of_rectOpNorm2Le _
        (mul_nonneg (rectOpNorm2_nonneg _) (rectOpNorm2_nonneg _)) hprod

/-- The difference of the two normalized triangular factors is upper
triangular.  This is a consequence of the two QR factorizations, not an
extra perturbation hypothesis. -/
theorem economyQR_deltaR_upper {m n : ℕ}
    {A Q dA dQ : Fin m → Fin n → ℝ}
    {R dR : Fin n → Fin n → ℝ}
    (hbase : EconomyQR A Q R)
    (hpert : EconomyQR (add A dA) (add Q dQ) (add R dR)) :
    IsUpperTrapezoidal n n dR := by
  intro i j hji
  have hR := hbase.upper i j hji
  have hRdR := hpert.upper i j hji
  unfold add at hRdR
  linarith

/-- A specified inverse of an upper-triangular square matrix is upper
triangular.  This is a thin adapter from the repository's entrywise inverse
predicate to Mathlib's block-triangular inverse theorem. -/
theorem upper_inverse_of_isInverse {n : ℕ}
    {R Rinv : Fin n → Fin n → ℝ}
    (hR : IsUpperTrapezoidal n n R) (hInv : IsInverse n R Rinv) :
    IsUpperTrapezoidal n n Rinv := by
  let RM : Matrix (Fin n) (Fin n) ℝ := R
  let RinvM : Matrix (Fin n) (Fin n) ℝ := Rinv
  have hmul : RM * RinvM = 1 := by
    ext i j
    simpa [RM, RinvM, Matrix.mul_apply, rectMatMul, idMatrix] using hInv.2 i j
  letI : Invertible RM := invertibleOfRightInverse RM RinvM hmul
  have hRblock : Matrix.BlockTriangular RM id := by
    intro i j hji
    exact hR i j (by simpa [RM] using hji)
  have hinvBlock : Matrix.BlockTriangular RM⁻¹ id :=
    Matrix.blockTriangular_inv_of_blockTriangular hRblock
  have hspecified : ⅟ RM = RinvM := invOf_eq_right_inv hmul
  have hnonsing : RM⁻¹ = RinvM := by
    rw [← Matrix.invOf_eq_nonsing_inv]
    exact hspecified
  rw [hnonsing] at hinvBlock
  intro i j hji
  exact hinvBlock (by simpa [RinvM] using hji)

/-- Ordinary multiplication preserves upper-triangular support. -/
theorem upper_rectMatMul_of_upper {n : ℕ}
    {S T : Fin n → Fin n → ℝ}
    (hS : IsUpperTrapezoidal n n S)
    (hT : IsUpperTrapezoidal n n T) :
    IsUpperTrapezoidal n n (rectMatMul S T) := by
  have hSblock : Matrix.BlockTriangular (S : Matrix (Fin n) (Fin n) ℝ) id := by
    intro i j hji
    exact hS i j (by simpa using hji)
  have hTblock : Matrix.BlockTriangular (T : Matrix (Fin n) (Fin n) ℝ) id := by
    intro i j hji
    exact hT i j (by simpa using hji)
  have hprod := hSblock.mul hTblock
  intro i j hji
  exact hprod (by simpa [Matrix.mul_apply, rectMatMul] using hji)

/-- The scaled triangular variation `T = ΔR R⁻¹` is upper triangular under
the source QR normalization and the supplied exact inverse. -/
theorem economyQR_scaledRVariation_upper {m n : ℕ}
    {A Q dA dQ : Fin m → Fin n → ℝ}
    {R dR Rinv : Fin n → Fin n → ℝ}
    (hbase : EconomyQR A Q R)
    (hpert : EconomyQR (add A dA) (add Q dQ) (add R dR))
    (hInv : IsInverse n R Rinv) :
    IsUpperTrapezoidal n n (scaledRVariation dR Rinv) := by
  exact upper_rectMatMul_of_upper
    (economyQR_deltaR_upper hbase hpert)
    (upper_inverse_of_isInverse hbase.upper hInv)

/-- Projecting the exact right-scaled perturbation equation by `Qᵀ` gives
the nonlinear identity
`W = X + T + X*T`, where `W = Qᵀ ΔA R⁻¹`, `X = Qᵀ ΔQ`, and
`T = ΔR R⁻¹`. -/
theorem economyQR_projected_perturbation_identity {m n : ℕ}
    {A Q dA dQ : Fin m → Fin n → ℝ}
    {R dR Rinv : Fin n → Fin n → ℝ}
    (hbase : EconomyQR A Q R)
    (hpert : EconomyQR (add A dA) (add Q dQ) (add R dR))
    (hRright : IsRightInverse n R Rinv) :
    projectedForcing Q dA Rinv = fun i j =>
      projectedQVariation Q dQ i j + scaledRVariation dR Rinv i j +
        rectMatMul (projectedQVariation Q dQ)
          (scaledRVariation dR Rinv) i j := by
  let QT : Fin n → Fin m → ℝ := finiteTranspose Q
  let X : Fin n → Fin n → ℝ := projectedQVariation Q dQ
  let T : Fin n → Fin n → ℝ := scaledRVariation dR Rinv
  have hright := economyQR_perturbation_right_inverse_identity
    hbase hpert hRright
  have hQtQ : rectMatMul QT Q = idMatrix n := by
    ext i j
    exact hbase.orthonormal i j
  have hleft := congrArg (rectMatMul QT) hright
  change rectMatMul QT (rectMatMul dA Rinv) =
      rectMatMul QT (fun i j =>
        dQ i j + rectMatMul Q T i j + rectMatMul dQ T i j) at hleft
  rw [rectMatMul_add_right, rectMatMul_add_right] at hleft
  rw [← rectMatMul_assoc QT Q T, hQtQ, rectMatMul_id_left] at hleft
  rw [← rectMatMul_assoc QT dQ T] at hleft
  simpa [projectedForcing, projectedQVariation, scaledRVariation, QT, X, T]
    using hleft

/-- Exact skew defect forced by the orthonormality of both `Q` and
`Q + ΔQ`: `X + Xᵀ = -ΔQᵀΔQ`.  Thus the failure of `X = QᵀΔQ` to be skew is
already quadratic in the factor perturbation. -/
theorem economyQR_projectedQVariation_skew_defect {m n : ℕ}
    {A Q dA dQ : Fin m → Fin n → ℝ}
    {R dR : Fin n → Fin n → ℝ}
    (hbase : EconomyQR A Q R)
    (hpert : EconomyQR (add A dA) (add Q dQ) (add R dR)) :
    ∀ i j : Fin n,
      projectedQVariation Q dQ i j + projectedQVariation Q dQ j i =
        -rectangularGram dQ i j := by
  intro i j
  have hb := hbase.orthonormal i j
  have hp := hpert.orthonormal i j
  simp only [rectangularGram, matMulRect, finiteTranspose, add] at hb hp
  simp only [projectedQVariation, rectMatMul, finiteTranspose, rectangularGram,
    matMulRect]
  simp_rw [add_mul, mul_add, Finset.sum_add_distrib] at hp
  have hcross :
      (∑ k : Fin m, dQ k i * Q k j) =
        ∑ k : Fin m, Q k j * dQ k i := by
    apply Finset.sum_congr rfl
    intro k _
    ring
  rw [hcross] at hp
  linarith

/-- Entrywise upper-triangular/skew splitting of the nonlinear QR equation.

For `W = Qᵀ ΔA R⁻¹`, `X = Qᵀ ΔQ`, and `T = ΔR R⁻¹`, this theorem proves:
* the exact quadratic skew defect of `X`;
* upper-triangularity of `T`;
* strict-lower entries of `X` from `W - X*T`;
* strict-upper and diagonal entries of `T` from the mirrored skew equation.

No sensitivity estimate is assumed.  These are the algebraic splitting
equations that precede the local nonlinear majorant argument behind (19.35)
and (19.36). -/
theorem economyQR_upper_skew_entry_split {m n : ℕ}
    {A Q dA dQ : Fin m → Fin n → ℝ}
    {R dR Rinv : Fin n → Fin n → ℝ}
    (hbase : EconomyQR A Q R)
    (hpert : EconomyQR (add A dA) (add Q dQ) (add R dR))
    (hInv : IsInverse n R Rinv) :
    let W := projectedForcing Q dA Rinv
    let X := projectedQVariation Q dQ
    let T := scaledRVariation dR Rinv
    (∀ i j : Fin n, X i j + X j i = -rectangularGram dQ i j) ∧
      IsUpperTrapezoidal n n T ∧
      (∀ i j : Fin n, j.val < i.val →
        X i j = W i j - rectMatMul X T i j) ∧
      (∀ i j : Fin n, i.val < j.val →
        T i j = W i j + W j i + rectangularGram dQ i j -
          rectMatMul X T j i - rectMatMul X T i j) ∧
      (∀ i : Fin n,
        T i i = W i i + rectangularGram dQ i i / 2 -
          rectMatMul X T i i) := by
  dsimp only
  have hW := economyQR_projected_perturbation_identity
    hbase hpert hInv.2
  have hskew := economyQR_projectedQVariation_skew_defect hbase hpert
  have hTupper := economyQR_scaledRVariation_upper hbase hpert hInv
  refine ⟨hskew, hTupper, ?_, ?_, ?_⟩
  · intro i j hji
    have hWij := congrFun (congrFun hW i) j
    have hTij := hTupper i j hji
    linarith
  · intro i j hij
    have hWij := congrFun (congrFun hW i) j
    have hWji := congrFun (congrFun hW j) i
    have hTji := hTupper j i hij
    have hXskew := hskew i j
    linarith
  · intro i
    have hWii := congrFun (congrFun hW i) i
    have hXskew := hskew i i
    linarith

/-- Entrywise transport of Zha's perturbation through `R^{-1}`.  The bound
contains exactly the nonnegative product `G |A| |R^{-1}|`; no norm estimate
or factor perturbation is assumed. -/
theorem zhaWeightedPerturbation_mul_right_inverse_abs_le {m n : ℕ}
    {A dA : Fin m → Fin n → ℝ} {G : Fin m → Fin m → ℝ}
    {Rinv : Fin n → Fin n → ℝ} {epsilon : ℝ}
    (hweighted : ZhaWeightedPerturbation A dA G epsilon) :
    ∀ i j,
      |rectMatMul dA Rinv i j| ≤
        epsilon *
          rectMatMul G
            (rectMatMul (absMatrixRect A) (absMatrix n Rinv)) i j := by
  intro i j
  unfold rectMatMul
  calc
    |∑ k : Fin n, dA i k * Rinv k j| ≤
        ∑ k : Fin n, |dA i k * Rinv k j| :=
      Finset.abs_sum_le_sum_abs _ _
    _ = ∑ k : Fin n, |dA i k| * |Rinv k j| := by
      apply Finset.sum_congr rfl
      intro k _
      exact abs_mul _ _
    _ ≤ ∑ k : Fin n,
        (epsilon * rectMatMul G (absMatrixRect A) i k) * |Rinv k j| := by
      apply Finset.sum_le_sum
      intro k _
      exact mul_le_mul_of_nonneg_right (hweighted i k) (abs_nonneg _)
    _ = epsilon *
        rectMatMul G
          (rectMatMul (absMatrixRect A) (absMatrix n Rinv)) i j := by
      rw [← rectMatMul_assoc]
      unfold rectMatMul absMatrix
      rw [Finset.mul_sum]
      apply Finset.sum_congr rfl
      intro k _
      ring

/-- The componentwise hypothesis in (19.36) controls the forcing term
`dA R^{-1}` by `epsilon * sqrt(n) * cond(R^{-1})` in operator 2-norm.

This is a genuine producer for the key columnwise-to-Skeel-condition bridge:
it derives the estimate from the source perturbation class, orthonormality,
the factorization `A=QR`, nonnegativity and `||G||_2 <= 1`.  The exact
triangular/skew split is now `economyQR_upper_skew_entry_split`; the remaining
open step for all of (19.36) is its quantitative local nonlinear majorant,
which must convert the forcing bound into separate bounds for `dQ` and `dR`.
-/
theorem zha_forcing_rectOpNorm2Le {m n : ℕ}
    {A Q dA : Fin m → Fin n → ℝ}
    {R Rinv : Fin n → Fin n → ℝ}
    {G : Fin m → Fin m → ℝ} {epsilon : ℝ}
    (hqr : EconomyQR A Q R)
    (hepsilon : 0 ≤ epsilon)
    (hGnonneg : ∀ i k, 0 ≤ G i k)
    (hGnorm : rectOpNorm2Le G 1)
    (hweighted : ZhaWeightedPerturbation A dA G epsilon) :
    rectOpNorm2Le (rectMatMul dA Rinv)
      (epsilon * (Real.sqrt (n : ℝ) *
        rectOpNorm2 (zhaConditionMatrix R Rinv))) := by
  let absQ : Fin m → Fin n → ℝ := absMatrixRect Q
  let absR : Fin n → Fin n → ℝ := absMatrix n R
  let absRinv : Fin n → Fin n → ℝ := absMatrix n Rinv
  let condM : Fin n → Fin n → ℝ := zhaConditionMatrix R Rinv
  let budget : Fin m → Fin n → ℝ :=
    rectMatMul G (rectMatMul absQ condM)
  have hAabs : ∀ i j, absMatrixRect A i j ≤ rectMatMul absQ absR i j := by
    simpa [absQ, absR] using economyQR_abs_le_abs_factors hqr
  have hGabsA : ∀ i j,
      rectMatMul G (absMatrixRect A) i j ≤
        rectMatMul G (rectMatMul absQ absR) i j :=
    rectMatMul_mono_right hGnonneg hAabs
  have habsRinv : ∀ i j, 0 ≤ absRinv i j := by
    intro i j
    exact abs_nonneg _
  have htransport :=
    zhaWeightedPerturbation_mul_right_inverse_abs_le
      (Rinv := Rinv) hweighted
  have hentry : ∀ i j,
      |rectMatMul dA Rinv i j| ≤ epsilon * budget i j := by
    intro i j
    calc
      |rectMatMul dA Rinv i j| ≤
          epsilon *
            rectMatMul G
              (rectMatMul (absMatrixRect A) absRinv) i j := by
        simpa [absRinv] using htransport i j
      _ ≤ epsilon *
          rectMatMul (rectMatMul G (rectMatMul absQ absR)) absRinv i j := by
        apply mul_le_mul_of_nonneg_left _ hepsilon
        rw [← rectMatMul_assoc]
        exact rectMatMul_mono_left hGabsA habsRinv i j
      _ = epsilon * budget i j := by
        simp only [budget, condM, zhaConditionMatrix, absR, absRinv]
        rw [rectMatMul_assoc, rectMatMul_assoc]
  have hQfrob : frobNormRect Q = Real.sqrt (n : ℝ) :=
    frobNormRect_eq_sqrt_nat_of_orthonormal hqr.orthonormal
  have habsQnorm : rectOpNorm2Le absQ (Real.sqrt (n : ℝ)) := by
    simpa [absQ, hQfrob] using
      (rectOpNorm2Le_absMatrixRect_frobNormRect Q)
  have hcond : rectOpNorm2Le condM (rectOpNorm2 condM) :=
    rectOpNorm2Le_rectOpNorm2 condM
  have hGQ : rectOpNorm2Le (rectMatMul G absQ)
      (1 * Real.sqrt (n : ℝ)) :=
    rectOpNorm2Le_rectMatMul G absQ (by norm_num) hGnorm habsQnorm
  have hbudget : rectOpNorm2Le budget
      ((1 * Real.sqrt (n : ℝ)) * rectOpNorm2 condM) := by
    simpa [budget, rectMatMul_assoc] using
      (rectOpNorm2Le_rectMatMul (rectMatMul G absQ) condM
        (mul_nonneg zero_le_one (Real.sqrt_nonneg _)) hGQ hcond)
  have hscaled : rectOpNorm2Le (fun i j => epsilon * budget i j)
      (epsilon * ((1 * Real.sqrt (n : ℝ)) * rectOpNorm2 condM)) := by
    intro x
    have haction :
        rectMatMulVec (fun i j => epsilon * budget i j) x =
          fun i => epsilon * rectMatMulVec budget x i := by
      funext i
      unfold rectMatMulVec
      rw [Finset.mul_sum]
      apply Finset.sum_congr rfl
      intro j _
      ring
    rw [haction, vecNorm2_smul, abs_of_nonneg hepsilon]
    calc
      epsilon * vecNorm2 (rectMatMulVec budget x) ≤
          epsilon *
            (((1 * Real.sqrt (n : ℝ)) * rectOpNorm2 condM) *
              vecNorm2 x) :=
        mul_le_mul_of_nonneg_left (hbudget x) hepsilon
      _ =
          (epsilon * ((1 * Real.sqrt (n : ℝ)) * rectOpNorm2 condM)) *
            vecNorm2 x := by ring
  have hfinal := rectOpNorm2Le_of_abs_entry_le hentry hscaled
  simpa [condM, zhaConditionMatrix] using hfinal

/-- Exact-norm form of the forcing estimate, under the source normalization
`||G||_2 = 1`.  This is the completed componentwise-to-condition-number
portion of Zha's (19.36) argument. -/
theorem zha_forcing_rectOpNorm2_le_of_source {m n : ℕ}
    {A Q dA : Fin m → Fin n → ℝ}
    {R Rinv : Fin n → Fin n → ℝ}
    {G : Fin m → Fin m → ℝ} {epsilon : ℝ}
    (hqr : EconomyQR A Q R)
    (hepsilon : 0 ≤ epsilon)
    (hGnonneg : ∀ i k, 0 ≤ G i k)
    (hGnorm : rectOpNorm2 G = 1)
    (hweighted : ZhaWeightedPerturbation A dA G epsilon) :
    rectOpNorm2 (rectMatMul dA Rinv) ≤
      epsilon * (Real.sqrt (n : ℝ) *
        rectOpNorm2 (zhaConditionMatrix R Rinv)) := by
  have hGcert : rectOpNorm2Le G 1 := by
    have h := rectOpNorm2Le_rectOpNorm2 G
    rwa [hGnorm] at h
  have hcert := zha_forcing_rectOpNorm2Le
    (R := R) (Rinv := Rinv) hqr hepsilon hGnonneg hGcert hweighted
  exact rectOpNorm2_le_of_rectOpNorm2Le _
    (mul_nonneg hepsilon
      (mul_nonneg (Real.sqrt_nonneg _)
        (rectOpNorm2_nonneg (zhaConditionMatrix R Rinv))))
    hcert

/-- Frobenius form of the source-shaped Zha forcing estimate, ready for the
unconditional quadratic Gram majorant.  The only dimension conversion is
Lemma 6.6(a), `||M||_F ≤ √n ||M||₂`, using the literal `n ≤ m`
economy-QR dimensions. -/
theorem zha_forcing_frobNormRect_le_of_source {m n : ℕ}
    (hnm : n ≤ m)
    {A Q dA : Fin m → Fin n → ℝ}
    {R Rinv : Fin n → Fin n → ℝ}
    {G : Fin m → Fin m → ℝ} {epsilon : ℝ}
    (hqr : EconomyQR A Q R)
    (hepsilon : 0 ≤ epsilon)
    (hGnonneg : ∀ i k, 0 ≤ G i k)
    (hGnorm : rectOpNorm2 G = 1)
    (hweighted : ZhaWeightedPerturbation A dA G epsilon) :
    frobNormRect (rectMatMul dA Rinv) ≤
      Real.sqrt (n : ℝ) *
        (epsilon * (Real.sqrt (n : ℝ) *
          rectOpNorm2 (zhaConditionMatrix R Rinv))) := by
  have hfrob := frobNormRect_le_sqrt_min_mul_rectOpNorm2
    (rectMatMul dA Rinv)
  have hop := zha_forcing_rectOpNorm2_le_of_source
    (R := R) (Rinv := Rinv) hqr hepsilon hGnonneg hGnorm hweighted
  calc
    frobNormRect (rectMatMul dA Rinv) ≤
        Real.sqrt (Nat.min m n : ℝ) *
          rectOpNorm2 (rectMatMul dA Rinv) := hfrob
    _ = Real.sqrt (n : ℝ) * rectOpNorm2 (rectMatMul dA Rinv) := by
      simp [Nat.min_eq_right hnm]
    _ ≤ Real.sqrt (n : ℝ) *
        (epsilon * (Real.sqrt (n : ℝ) *
          rectOpNorm2 (zhaConditionMatrix R Rinv))) :=
      mul_le_mul_of_nonneg_left hop (Real.sqrt_nonneg _)

/-- Projecting Zha's forcing by `Qᵀ` does not enlarge its operator 2-norm.
Together with `economyQR_upper_skew_entry_split`, this connects the literal
componentwise source hypothesis to every leading term in the nonlinear
triangular/skew equations. -/
theorem zha_projectedForcing_rectOpNorm2Le {m n : ℕ}
    {A Q dA : Fin m → Fin n → ℝ}
    {R Rinv : Fin n → Fin n → ℝ}
    {G : Fin m → Fin m → ℝ} {epsilon : ℝ}
    (hqr : EconomyQR A Q R)
    (hepsilon : 0 ≤ epsilon)
    (hGnonneg : ∀ i k, 0 ≤ G i k)
    (hGnorm : rectOpNorm2Le G 1)
    (hweighted : ZhaWeightedPerturbation A dA G epsilon) :
    rectOpNorm2Le (projectedForcing Q dA Rinv)
      (epsilon * (Real.sqrt (n : ℝ) *
        rectOpNorm2 (zhaConditionMatrix R Rinv))) := by
  have hforcing := zha_forcing_rectOpNorm2Le
    (R := R) (Rinv := Rinv) hqr hepsilon hGnonneg hGnorm hweighted
  have hQT : rectOpNorm2Le (finiteTranspose Q) 1 :=
    rectOpNorm2Le_finiteTranspose_of_rectOpNorm2Le Q (by norm_num)
      hqr.orthonormal.rectOpNorm2Le_one
  have hprod := rectOpNorm2Le_rectMatMul
    (finiteTranspose Q) (rectMatMul dA Rinv) (by norm_num) hQT hforcing
  simpa [projectedForcing] using hprod

/-- Exact-norm version of the projected Zha forcing estimate under the
source normalization `||G||₂ = 1`. -/
theorem zha_projectedForcing_rectOpNorm2_le_of_source {m n : ℕ}
    {A Q dA : Fin m → Fin n → ℝ}
    {R Rinv : Fin n → Fin n → ℝ}
    {G : Fin m → Fin m → ℝ} {epsilon : ℝ}
    (hqr : EconomyQR A Q R)
    (hepsilon : 0 ≤ epsilon)
    (hGnonneg : ∀ i k, 0 ≤ G i k)
    (hGnorm : rectOpNorm2 G = 1)
    (hweighted : ZhaWeightedPerturbation A dA G epsilon) :
    rectOpNorm2 (projectedForcing Q dA Rinv) ≤
      epsilon * (Real.sqrt (n : ℝ) *
        rectOpNorm2 (zhaConditionMatrix R Rinv)) := by
  have hGcert : rectOpNorm2Le G 1 := by
    have h := rectOpNorm2Le_rectOpNorm2 G
    rwa [hGnorm] at h
  have hcert := zha_projectedForcing_rectOpNorm2Le
    (R := R) (Rinv := Rinv) hqr hepsilon hGnonneg hGcert hweighted
  exact rectOpNorm2_le_of_rectOpNorm2Le _
    (mul_nonneg hepsilon
      (mul_nonneg (Real.sqrt_nonneg _)
        (rectOpNorm2_nonneg (zhaConditionMatrix R Rinv))))
    hcert

/-- Stewart-route forcing bound before the nonlinear triangular/skew solve:
`||ΔA R⁻¹||_F ≤ ||ΔA||_F ||R⁻¹||₂`. -/
theorem stewart_forcing_frobNormRect_le {m n : ℕ}
    (dA : Fin m → Fin n → ℝ) (Rinv : Fin n → Fin n → ℝ) :
    frobNormRect (rectMatMul dA Rinv) ≤
      frobNormRect dA * rectOpNorm2 Rinv := by
  have hRinv : rectOpNorm2Le Rinv (rectOpNorm2 Rinv) :=
    rectOpNorm2Le_rectOpNorm2 Rinv
  have hRinvT : rectOpNorm2Le (finiteTranspose Rinv) (rectOpNorm2 Rinv) :=
    rectOpNorm2Le_finiteTranspose_of_rectOpNorm2Le Rinv
      (rectOpNorm2_nonneg Rinv) hRinv
  exact frobNormRect_rectMatMul_le_mul_of_transpose_rectOpNorm2Le
    dA Rinv (rectOpNorm2_nonneg Rinv) hRinvT

/-- The `Qᵀ` projection is also nonexpansive in the Stewart Frobenius route,
so the complete normalized forcing `W = Qᵀ ΔA R⁻¹` has the same bound. -/
theorem stewart_projectedForcing_frobNormRect_le {m n : ℕ}
    {A Q : Fin m → Fin n → ℝ} {R : Fin n → Fin n → ℝ}
    (dA : Fin m → Fin n → ℝ) (Rinv : Fin n → Fin n → ℝ)
    (hqr : EconomyQR A Q R) :
    frobNormRect (projectedForcing Q dA Rinv) ≤
      frobNormRect dA * rectOpNorm2 Rinv := by
  have hQT : rectOpNorm2Le (finiteTranspose Q) 1 :=
    rectOpNorm2Le_finiteTranspose_of_rectOpNorm2Le Q (by norm_num)
      hqr.orthonormal.rectOpNorm2Le_one
  have hprojection :
      frobNormRect (projectedForcing Q dA Rinv) ≤
        frobNormRect (rectMatMul dA Rinv) := by
    have h := frobNormRect_rectMatMul_le_mul_of_rectOpNorm2Le
      (finiteTranspose Q) (rectMatMul dA Rinv) (by norm_num) hQT
    simpa [projectedForcing] using h
  exact hprojection.trans (stewart_forcing_frobNormRect_le dA Rinv)

/-- Relative form of the Stewart forcing bridge.  The mixed factor
`||A||_F ||R⁻¹||₂` is exposed explicitly; the Penrose and norm theorems above
identify it with the book's full-column-rank `κ_F(A)` convention. -/
theorem stewart_projectedForcing_relative_le {m n : ℕ}
    {A Q : Fin m → Fin n → ℝ} {R : Fin n → Fin n → ℝ}
    (dA : Fin m → Fin n → ℝ) (Rinv : Fin n → Fin n → ℝ)
    (hqr : EconomyQR A Q R) (hA : 0 < frobNormRect A) :
    frobNormRect (projectedForcing Q dA Rinv) ≤
      (frobNormRect A * rectOpNorm2 Rinv) *
        (frobNormRect dA / frobNormRect A) := by
  calc
    frobNormRect (projectedForcing Q dA Rinv) ≤
        frobNormRect dA * rectOpNorm2 Rinv :=
      stewart_projectedForcing_frobNormRect_le dA Rinv hqr
    _ = (frobNormRect A * rectOpNorm2 Rinv) *
        (frobNormRect dA / frobNormRect A) := by
      field_simp

lemma diff_decompose {m n : ℕ}
    (Qhat Qtilde Q : Fin m → Fin n → ℝ) :
    diff Qhat Q = fun i j => diff Qhat Qtilde i j + diff Qtilde Q i j := by
  funext i j
  simp [diff]

/-- Equation (19.37), honest composition form.

Zha's exact-factor sensitivity supplies the first term `Qtilde-Q`; the
formed-Householder estimate (19.13) supplies `Qhat-Qtilde`.  This theorem
performs the previously absent triangle/Frobenius-to-operator composition and
keeps both second-order remainders explicit.  It does not claim to prove the
external Zha local-sensitivity theorem itself. -/
theorem higham19_eq19_37_of_zha_and_formedQ
    {m n : ℕ} (Qhat Qtilde Q : Fin m → Fin n → ℝ)
    (c u phi zhaRemainder formedFirstOrder formedRemainder : ℝ)
    (hzha : frobNormRect (diff Qtilde Q) ≤
      c * u * phi + zhaRemainder)
    (hformed : frobNormRect (diff Qhat Qtilde) ≤
      formedFirstOrder + formedRemainder)
    :
    rectOpNorm2Le (diff Qhat Q)
      (c * u * phi + zhaRemainder +
        (formedFirstOrder + formedRemainder)) := by
  have htri :
      frobNormRect (diff Qhat Q) ≤
        frobNormRect (diff Qhat Qtilde) + frobNormRect (diff Qtilde Q) := by
    rw [diff_decompose Qhat Qtilde Q]
    exact frobNormRect_add_le _ _
  have hfrob :
      frobNormRect (diff Qhat Q) ≤
        c * u * phi + zhaRemainder +
          (formedFirstOrder + formedRemainder) := by
    calc
      frobNormRect (diff Qhat Q) ≤
          frobNormRect (diff Qhat Qtilde) + frobNormRect (diff Qtilde Q) := htri
      _ ≤ (formedFirstOrder + formedRemainder) +
          (c * u * phi + zhaRemainder) := add_le_add hformed hzha
      _ = c * u * phi + zhaRemainder +
          (formedFirstOrder + formedRemainder) := by ring
  exact rectOpNorm2Le_of_frobNormRect_le _ hfrob

/-- Specialization of (19.37) after absorbing the formed-Q first-order term
into the dimension-dependent coefficient and combining both quadratic
remainders. -/
theorem higham19_eq19_37_absorbed
    {m n : ℕ} (Qhat Qtilde Q : Fin m → Fin n → ℝ)
    (c u phi remainder : ℝ)
    (hcombined : frobNormRect (diff Qhat Qtilde) +
        frobNormRect (diff Qtilde Q) ≤ c * u * phi + remainder) :
    rectOpNorm2Le (diff Qhat Q) (c * u * phi + remainder) := by
  have htri : frobNormRect (diff Qhat Q) ≤
      frobNormRect (diff Qhat Qtilde) + frobNormRect (diff Qtilde Q) := by
    rw [diff_decompose Qhat Qtilde Q]
    exact frobNormRect_add_le _ _
  exact rectOpNorm2Le_of_frobNormRect_le _ (htri.trans hcombined)

end H19Sensitivity

end NumStability
