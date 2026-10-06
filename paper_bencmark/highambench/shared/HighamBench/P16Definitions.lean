import Mathlib.Algebra.BigOperators.Fin
import Mathlib.Data.Real.Basic
import Mathlib.Tactic
import Mathlib.Analysis.Matrix.Normed

namespace HighamBench

open scoped BigOperators Matrix.Norms.Frobenius

noncomputable def gamma (u : ℝ) (n : ℕ) : ℝ :=
  ((n : ℝ) * u) / (1 - (n : ℝ) * u)

def GammaValid (u : ℝ) (n : ℕ) : Prop :=
  (n : ℝ) * u < 1

abbrev P16Matrix (n : ℕ) := Matrix (Fin n) (Fin n) ℝ

abbrev P16Vector (n : ℕ) := Fin n → ℝ

noncomputable def p16MatVec {n : ℕ} (A : P16Matrix n)
    (x : P16Vector n) : P16Vector n :=
  fun i ↦ ∑ j : Fin n, A i j * x j

noncomputable def p16FrobNorm {n : ℕ} (A : P16Matrix n) : ℝ :=
  ‖A‖

noncomputable def p16VecNorm {n : ℕ} (x : P16Vector n) : ℝ :=
  Real.sqrt (∑ i : Fin n, x i ^ 2)

noncomputable def p16Residual {n : ℕ} (A : P16Matrix n)
    (b x : P16Vector n) : P16Vector n :=
  b - p16MatVec A x

def p16IsNonsingular {n : ℕ} (A : P16Matrix n) : Prop :=
  Function.Bijective (p16MatVec A)

def p16NormwiseBackwardErrorAdmissible {n : ℕ}
    (A : P16Matrix n) (b xHat : P16Vector n) (epsilon : ℝ) : Prop :=
  ∃ deltaA : P16Matrix n, ∃ deltaB : P16Vector n,
    p16MatVec (A + deltaA) xHat = b + deltaB ∧
      p16FrobNorm deltaA ≤ epsilon * p16FrobNorm A ∧
      p16VecNorm deltaB ≤ epsilon * p16VecNorm b

noncomputable def p16NormalizedResidual {n : ℕ}
    (A : P16Matrix n) (b xHat : P16Vector n) : ℝ :=
  p16VecNorm (p16Residual A b xHat) /
    (p16FrobNorm A * p16VecNorm xHat + p16VecNorm b)

noncomputable def p16ConditionNumberF {n : ℕ}
    (A Ainv : P16Matrix n) : ℝ :=
  p16FrobNorm Ainv * p16FrobNorm A

abbrev P16RectMatrix (m k : ℕ) := Matrix (Fin m) (Fin k) ℝ

noncomputable def p16RectMatVec {m k : ℕ} (A : P16RectMatrix m k)
    (x : P16Vector k) : P16Vector m :=
  fun i ↦ ∑ j : Fin k, A i j * x j

noncomputable def p16SquareRectMul {n k : ℕ} (A : P16Matrix n)
    (B : P16RectMatrix n k) : P16RectMatrix n k :=
  fun i j ↦ ∑ q : Fin n, A i q * B q j

noncomputable def p16RectMatMul {m k q : ℕ} (A : P16RectMatrix m k)
    (B : P16RectMatrix k q) : P16RectMatrix m q :=
  fun i j ↦ ∑ r : Fin k, A i r * B r j

noncomputable def p16RectFrobNorm {m k : ℕ}
    (A : P16RectMatrix m k) : ℝ :=
  ‖A‖

noncomputable def p16Augment {n k : ℕ} (b : P16Vector n)
    (phi : ℝ) (C : P16RectMatrix n k) : P16RectMatrix n (k + 1) :=
  fun i ↦ Fin.cases (b i * phi) (fun j ↦ C i j)

def p16MinGainAtLeast {m k : ℕ} (A : P16RectMatrix m k)
    (sigma : ℝ) : Prop :=
  ∀ x : P16Vector k, sigma * p16VecNorm x ≤ p16VecNorm (p16RectMatVec A x)

def p16NearRankDeficient {m k : ℕ} (A : P16RectMatrix m k)
    (delta : ℝ) : Prop :=
  ∃ x : P16Vector k,
    p16VecNorm x = 1 ∧ p16VecNorm (p16RectMatVec A x) ≤ delta

def p16IsLeastSquaresSolution {m k : ℕ} (A : P16RectMatrix m k)
    (b : P16Vector m) (y : P16Vector k) : Prop :=
  ∀ z : P16Vector k,
    p16VecNorm (b - p16RectMatVec A y) ≤
      p16VecNorm (b - p16RectMatVec A z)

structure P16PolynomialFactor where
  degreeN : ℕ
  degreeK : ℕ
  coefficient : Fin (degreeN + 1) → Fin (degreeK + 1) → ℝ
  coefficient_nonneg : ∀ i j, 0 ≤ coefficient i j

noncomputable def p16PolynomialFactorValue (c : P16PolynomialFactor)
    (n k : ℕ) : ℝ :=
  ∑ i : Fin (c.degreeN + 1), ∑ j : Fin (c.degreeK + 1),
    c.coefficient i j * (n : ℝ) ^ (i : ℕ) * (k : ℝ) ^ (j : ℕ)

noncomputable def p16ForwardError {n : ℕ} (x xHat : P16Vector n) : ℝ :=
  p16VecNorm (xHat - x) / p16VecNorm x

structure P16FirstOrderSemantics where
  secondOrder : ℝ → Prop
  zero_secondOrder : secondOrder 0

def p16FirstOrderLe (semantics : P16FirstOrderSemantics)
    (lhs rhs : ℝ) : Prop :=
  ∃ remainder : ℝ,
    semantics.secondOrder remainder ∧ lhs ≤ rhs + |remainder|

noncomputable def p16BackwardError {n : ℕ} (A : P16Matrix n)
    (b xHat : P16Vector n) : ℝ :=
  p16NormalizedResidual A b xHat

def p16AugmentedColumn {n k : ℕ} (rhs : P16Vector n)
    (C : P16RectMatrix n k) (j : Fin (k + 1)) : P16Vector n :=
  Fin.cases rhs (fun q row ↦ C row q) j

structure P16FixedLowPrecisionMGSRestart {n : ℕ}
    (A : P16Matrix n) (residualHat correctionHat : P16Vector n)
    (uLow : ℝ) (dimensionFactor : P16PolynomialFactor) where
  dimension_pos : 0 < n
  uLow_pos : 0 < uLow
  gamma_valid : GammaValid uLow n
  keyDimension : ℕ
  keyDimension_pos : 0 < keyDimension
  keyDimension_le : keyDimension ≤ n
  basis : P16RectMatrix n keyDimension
  basisNext : P16RectMatrix n (keyDimension + 1)
  hessenberg : P16RectMatrix (keyDimension + 1) keyDimension
  arnoldiProduct : P16RectMatrix n keyDimension
  arnoldiProductError : P16RectMatrix n keyDimension
  arnoldi_product_equation :
    arnoldiProduct = p16SquareRectMul A basis + arnoldiProductError
  basis_fully_stored : ∀ row col,
    basis row col = basisNext row col.castSucc
  mgsWork : Fin keyDimension → ℕ → P16Vector n
  mgsProjectionError : Fin keyDimension → Fin keyDimension → ℝ
  mgsUpdateError : Fin keyDimension → Fin keyDimension → P16Vector n
  mgsNormalizationError : Fin keyDimension → P16Vector n
  mgs_work_initial : ∀ j row,
    mgsWork j 0 row = arnoldiProduct row j
  mgs_projection : ∀ j q, q.1 ≤ j.1 →
    hessenberg q.castSucc j =
      (∑ row : Fin n, basisNext row q.castSucc * mgsWork j q.1 row) +
        mgsProjectionError j q
  mgs_projection_error_bound : ∀ j q, q.1 ≤ j.1 →
    |mgsProjectionError j q| ≤
      gamma uLow n *
        (∑ row : Fin n, |basisNext row q.castSucc * mgsWork j q.1 row|)
  mgs_update : ∀ j q, q.1 ≤ j.1 →
    mgsWork j (q.1 + 1) =
      mgsWork j q.1 -
        (fun row ↦ hessenberg q.castSucc j * basisNext row q.castSucc) +
          mgsUpdateError j q
  mgs_update_error_bound : ∀ j q, q.1 ≤ j.1 →
    p16VecNorm (mgsUpdateError j q) ≤
      uLow *
        (p16VecNorm (mgsWork j q.1) +
          |hessenberg q.castSucc j| *
            p16VecNorm (fun row ↦ basisNext row q.castSucc))
  mgs_normalization : ∀ j,
    (fun row ↦ hessenberg j.succ j * basisNext row j.succ) =
      mgsWork j (j.1 + 1) + mgsNormalizationError j
  mgs_normalization_error_bound : ∀ j,
    p16VecNorm (mgsNormalizationError j) ≤
      uLow * p16VecNorm (mgsWork j (j.1 + 1))
  epsilonC : ℝ
  epsilonB : ℝ
  epsilonLS : ℝ
  epsilonX : ℝ
  residualNorm : ℝ
  residualNorm_eq : residualNorm = p16VecNorm residualHat
  residual_starts_basis : ∀ row,
    residualHat row = residualNorm * basisNext row 0
  epsilonB_eq : epsilonB = 0
  product_error_bound :
    p16RectFrobNorm arnoldiProductError ≤
      epsilonC * p16RectFrobNorm (p16SquareRectMul A basis)
  leastSquaresRhsError : P16Vector n
  leastSquaresMatrixError : P16RectMatrix n keyDimension
  leastSquaresY : P16Vector keyDimension
  least_squares_solution :
    p16IsLeastSquaresSolution
      (arnoldiProduct + leastSquaresMatrixError)
      (residualHat + leastSquaresRhsError) leastSquaresY
  least_squares_column_bound : ∀ j : Fin (keyDimension + 1),
    p16VecNorm
        (p16AugmentedColumn leastSquaresRhsError leastSquaresMatrixError j) ≤
      epsilonLS *
        p16VecNorm (p16AugmentedColumn residualHat arnoldiProduct j)
  correctionFormationError : P16Vector n
  correction_formation_equation :
    correctionHat = p16RectMatVec basis leastSquaresY +
      correctionFormationError
  correction_formation_bound :
    p16VecNorm correctionFormationError ≤
      epsilonX * p16RectFrobNorm basis * p16VecNorm leastSquaresY
  accuracy_nonneg :
    0 ≤ epsilonC ∧ 0 ≤ epsilonB ∧ 0 ≤ epsilonLS ∧ 0 ≤ epsilonX
  productWeight : ℝ
  leastSquaresWeight : ℝ
  correctionWeight : ℝ
  weights_nonneg :
    0 ≤ productWeight ∧ 0 ≤ leastSquaresWeight ∧ 0 ≤ correctionWeight
  epsilonC_le : epsilonC ≤ productWeight * uLow
  epsilonLS_le : epsilonLS ≤ leastSquaresWeight * uLow
  epsilonX_le : epsilonX ≤ correctionWeight * uLow
  basisLowerGain : ℝ
  imageLowerGain : ℝ
  basisLowerGain_pos : 0 < basisLowerGain
  basis_gain : p16MinGainAtLeast basis basisLowerGain
  image_gain : p16MinGainAtLeast (p16SquareRectMul A basis) imageLowerGain
  basis_not_numerically_rank_deficient :
    epsilonX * p16RectFrobNorm basis < basisLowerGain
  key_near_dependence : keyDimension < n → ∀ phi, 0 < phi →
    p16NearRankDeficient
      (p16Augment residualHat phi arnoldiProduct)
      ((epsilonC + epsilonB + epsilonLS) *
        p16PolynomialFactorValue dimensionFactor n keyDimension *
          p16RectFrobNorm (p16Augment residualHat phi arnoldiProduct))
  key_image_full_rank :
    (epsilonC + epsilonB + epsilonLS) *
        p16RectFrobNorm arnoldiProduct < imageLowerGain
  alpha : ℝ
  beta : ℝ
  lambda : ℝ
  coefficients_nonneg : 0 ≤ alpha ∧ 0 ≤ beta ∧ 0 ≤ lambda
  alpha_eq :
    alpha = p16RectFrobNorm arnoldiProduct /
      (basisLowerGain * p16FrobNorm A)
  beta_eq : beta = max 1 alpha
  lambda_eq : lambda = p16RectFrobNorm basis / basisLowerGain
  modularAccuracy : ℝ
  modular_accuracy_eq :
    modularAccuracy =
      alpha * epsilonC + beta * epsilonB + beta * epsilonLS +
        lambda * epsilonX
  dimension_factor_bound :
    alpha * productWeight + beta * (1 + leastSquaresWeight) +
        lambda * correctionWeight ≤
      p16PolynomialFactorValue dimensionFactor n keyDimension

noncomputable def p16FixedMGSBackwardError {n : ℕ}
    {A : P16Matrix n} {residualHat correctionHat : P16Vector n}
    {uLow : ℝ} {dimensionFactor : P16PolynomialFactor}
    (_run : P16FixedLowPrecisionMGSRestart
      A residualHat correctionHat uLow dimensionFactor) : ℝ :=
  p16VecNorm (residualHat - p16MatVec A correctionHat) /
    (p16VecNorm residualHat + p16FrobNorm A * p16VecNorm correctionHat)

noncomputable def p16FixedMGSDimensionCoefficient {n : ℕ}
    {A : P16Matrix n} {residualHat correctionHat : P16Vector n}
    {uLow : ℝ} {dimensionFactor : P16PolynomialFactor}
    (run : P16FixedLowPrecisionMGSRestart
      A residualHat correctionHat uLow dimensionFactor) : ℝ :=
  p16PolynomialFactorValue dimensionFactor n run.keyDimension

end HighamBench
