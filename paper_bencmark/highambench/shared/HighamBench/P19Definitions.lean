import Mathlib.Algebra.BigOperators.Fin
import Mathlib.Data.Real.Basic
import Mathlib.Tactic
import Mathlib.Analysis.Asymptotics.Lemmas
import Mathlib.Analysis.CStarAlgebra.Matrix
import Mathlib.Analysis.Matrix.Normed

namespace HighamBench

open scoped BigOperators Matrix.Norms.L2Operator Matrix.Norms.Frobenius

abbrev P19Matrix (n : ℕ) := Matrix (Fin n) (Fin n) ℝ

abbrev P19RectMatrix (m k : ℕ) := Matrix (Fin m) (Fin k) ℝ

abbrev P19Vector (n : ℕ) := Fin n → ℝ

noncomputable def p19VecNorm2Sq {n : ℕ} (x : Fin n → ℝ) : ℝ :=
  ∑ i, x i ^ 2

noncomputable def p19VecNorm2 {n : ℕ} (x : Fin n → ℝ) : ℝ :=
  Real.sqrt (p19VecNorm2Sq x)

def p19Add {n : ℕ} (x y : Fin n → ℝ) : Fin n → ℝ :=
  fun i => x i + y i

def p19Scale {n : ℕ} (a : ℝ) (x : Fin n → ℝ) : Fin n → ℝ :=
  fun i => a * x i

def p19ModularEnvelope (alpha beta lambda epsilonC epsilonB ug epsilonX : ℝ) : ℝ :=
  alpha * epsilonC + beta * epsilonB + beta * ug + lambda * epsilonX

noncomputable def p19MatVec {n : ℕ} (A : P19Matrix n)
    (x : P19Vector n) : P19Vector n :=
  fun i ↦ ∑ j : Fin n, A i j * x j

noncomputable def p19RectMatVec {m k : ℕ} (A : P19RectMatrix m k)
    (x : P19Vector k) : P19Vector m :=
  fun i ↦ ∑ j : Fin k, A i j * x j

noncomputable def p19SquareRectMul {n k : ℕ} (A : P19Matrix n)
    (B : P19RectMatrix n k) : P19RectMatrix n k :=
  fun i j ↦ ∑ q : Fin n, A i q * B q j

noncomputable def p19RectMatMul {m k q : ℕ} (A : P19RectMatrix m k)
    (B : P19RectMatrix k q) : P19RectMatrix m q :=
  fun i j ↦ ∑ r : Fin k, A i r * B r j

noncomputable def p19FrobNorm {m k : ℕ} (A : P19RectMatrix m k) : ℝ :=
  ‖A‖

def p19Column {m k : ℕ} (A : P19RectMatrix m k) (j : Fin k) : P19Vector m :=
  fun i ↦ A i j

noncomputable def p19Augment {n k : ℕ} (b : P19Vector n)
    (C : P19RectMatrix n k) : P19RectMatrix n (k + 1) :=
  fun i ↦ Fin.cases (b i) (fun j ↦ C i j)

def p19ScaledFirstBasisVector {k : ℕ} (beta : ℝ) : P19Vector (k + 1) :=
  fun i ↦ if i.val = 0 then beta else 0

def p19IsUpperHessenberg {k : ℕ}
    (H : P19RectMatrix (k + 1) k) : Prop :=
  ∀ i j, j.val + 1 < i.val → H i j = 0

def p19InversePair {n : ℕ} (A Ainv : P19Matrix n) : Prop :=
  (∀ x : P19Vector n, p19MatVec Ainv (p19MatVec A x) = x) ∧
    ∀ x : P19Vector n, p19MatVec A (p19MatVec Ainv x) = x

def p19IsLeastSquaresSolution {m k : ℕ} (A : P19RectMatrix m k)
    (b : P19Vector m) (y : P19Vector k) : Prop :=
  ∀ z : P19Vector k,
    p19VecNorm2 (b - p19RectMatVec A y) ≤
      p19VecNorm2 (b - p19RectMatVec A z)

def p19FullColumnRank {m k : ℕ} (A : P19RectMatrix m k) : Prop :=
  Function.Injective (p19RectMatVec A)

structure P19SingularValueData {m k : ℕ} (A : P19RectMatrix m k) where
  sigmaMin : ℝ
  sigmaMax : ℝ
  sigmaMin_nonneg : 0 ≤ sigmaMin
  sigmaMax_nonneg : 0 ≤ sigmaMax
  lower_gain : ∀ x : P19Vector k,
    sigmaMin * p19VecNorm2 x ≤ p19VecNorm2 (p19RectMatVec A x)
  upper_gain : ∀ x : P19Vector k,
    p19VecNorm2 (p19RectMatVec A x) ≤ sigmaMax * p19VecNorm2 x
  min_attained : 0 < k → ∃ x : P19Vector k,
    p19VecNorm2 x = 1 ∧ p19VecNorm2 (p19RectMatVec A x) = sigmaMin
  max_attained : 0 < k → ∃ x : P19Vector k,
    p19VecNorm2 x = 1 ∧ p19VecNorm2 (p19RectMatVec A x) = sigmaMax

structure P19PolynomialFactor where
  degreeN : ℕ
  degreeK : ℕ
  coefficient : Fin (degreeN + 1) → Fin (degreeK + 1) → ℝ
  coefficient_nonneg : ∀ i j, 0 ≤ coefficient i j

noncomputable def p19PolynomialFactorValue (c : P19PolynomialFactor)
    (n k : ℕ) : ℝ :=
  ∑ i : Fin (c.degreeN + 1), ∑ j : Fin (c.degreeK + 1),
    c.coefficient i j * (n : ℝ) ^ (i : ℕ) * (k : ℝ) ^ (j : ℕ)

noncomputable def p19RectConditionF2 {m k : ℕ}
    (A : P19RectMatrix m k) (sigmaMin : ℝ) : ℝ :=
  p19FrobNorm A / sigmaMin

noncomputable def p19ConditionNumberF {n : ℕ}
    (A Ainv : P19Matrix n) : ℝ :=
  p19FrobNorm Ainv * p19FrobNorm A

noncomputable def p19ForwardError {n : ℕ}
    (x xHat : P19Vector n) : ℝ :=
  p19VecNorm2 (xHat - x) / p19VecNorm2 x

structure P19FirstOrderSemantics where
  small : ℝ → Prop
  secondOrder : ℝ → Prop
  zero_secondOrder : secondOrder 0

def p19FirstOrderLe (semantics : P19FirstOrderSemantics)
    (lhs rhs : ℝ) : Prop :=
  ∃ remainder : ℝ,
    semantics.secondOrder remainder ∧ lhs ≤ rhs + |remainder|

noncomputable def p19SafeRelativeMagnitude (actual reference : ℝ) : ℝ :=
  if reference = 0 then 0 else actual / reference

abbrev P19Theorem31Dimension (n : ℕ) :=
  {k : ℕ // 0 < k ∧ k ≤ n}

structure P19Theorem31System (n : ℕ) where
  dimension_pos : 0 < n
  A : P19Matrix n
  Ainv : P19Matrix n
  ML : P19Matrix n
  MLinv : P19Matrix n
  b : P19Vector n
  xExact : P19Vector n
  A_inverse : p19InversePair A Ainv
  ML_inverse : p19InversePair ML MLinv
  b_nonzero : b ≠ 0
  exact_solution : p19MatVec A xExact = b

structure P19Theorem31BasisFamily {n : ℕ}
    (system : P19Theorem31System n) where
  basis : (k : ℕ) → P19RectMatrix n k
  full_rank : ∀ k, 0 < k → k ≤ n → p19FullColumnRank (basis k)
  column_prefix : ∀ k, k < n → ∀ i (j : Fin k),
    basis k i j = basis (k + 1) i j.castSucc

noncomputable def p19StaticExactC {n k : ℕ}
    (system : P19Theorem31System n) (Z : P19RectMatrix n k) :
    P19RectMatrix n k :=
  p19SquareRectMul system.MLinv (p19SquareRectMul system.A Z)

noncomputable def p19StaticExactB {n : ℕ}
    (system : P19Theorem31System n) : P19Vector n :=
  p19MatVec system.MLinv system.b

structure P19Algorithm2Iteration {n : ℕ}
    (system : P19Theorem31System n)
    (semantics : P19FirstOrderSemantics)
    (basisFamily : P19Theorem31BasisFamily system)
    (k : P19Theorem31Dimension n) where
  dimensionFactor : ℝ
  dimensionFactor_one_le : 1 ≤ dimensionFactor
  epsilonC : ℝ
  epsilonB : ℝ
  ug : ℝ
  epsilonX : ℝ
  computedC : P19RectMatrix n k.1
  deltaC : P19RectMatrix n k.1
  computation_equation :
    computedC = p19StaticExactC system (basisFamily.basis k.1) + deltaC
  computedB : P19Vector n
  deltaB : P19Vector n
  rhs_equation : computedB = p19StaticExactB system + deltaB
  vHat : P19RectMatrix n k.1
  vHatNext : P19RectMatrix n (k.1 + 1)
  beta : ℝ
  hessenberg : P19RectMatrix (k.1 + 1) k.1
  hessenberg_upper : p19IsUpperHessenberg hessenberg
  mgs_givens_relation :
    p19Augment computedB computedC =
      p19RectMatMul vHatNext
        (p19Augment (p19ScaledFirstBasisVector beta) hessenberg)
  vHat_prefix : ∀ i (j : Fin k.1),
    vHat i j = vHatNext i j.castSucc
  leastSquaresDeltaB : P19Vector n
  leastSquaresDeltaC : P19RectMatrix n k.1
  yHat : P19Vector k.1
  computedCSpectrum : P19SingularValueData computedC
  exactCSpectrum :
    P19SingularValueData
      (p19StaticExactC system (basisFamily.basis k.1))
  xHat : P19Vector n
  deltaX : P19Vector n
  solution_equation :
    xHat = p19RectMatVec (basisFamily.basis k.1) yHat + deltaX
  vHatSpectrum : P19SingularValueData vHat

structure P19Algorithm2Conditions {n : ℕ}
    {system : P19Theorem31System n}
    {semantics : P19FirstOrderSemantics}
    {basisFamily : P19Theorem31BasisFamily system}
    {k : P19Theorem31Dimension n}
    (iteration : P19Algorithm2Iteration system semantics basisFamily k) where
  accuracy_nonneg :
    0 ≤ iteration.epsilonC ∧ 0 ≤ iteration.epsilonB ∧
      0 ≤ iteration.ug ∧ 0 ≤ iteration.epsilonX
  computation_error_bound :
    p19FrobNorm iteration.deltaC ≤
      iteration.epsilonC *
        p19FrobNorm (p19StaticExactC system (basisFamily.basis k.1))
  rhs_error_bound :
    p19VecNorm2 iteration.deltaB ≤
      iteration.epsilonB * p19VecNorm2 (p19StaticExactB system)
  least_squares_solution :
    p19IsLeastSquaresSolution
      (iteration.computedC + iteration.leastSquaresDeltaC)
      (iteration.computedB + iteration.leastSquaresDeltaB) iteration.yHat
  least_squares_column_bound : ∀ j : Fin (k.1 + 1),
    p19VecNorm2
        (p19Column
          (p19Augment iteration.leastSquaresDeltaB
            iteration.leastSquaresDeltaC) j) ≤
      iteration.dimensionFactor * iteration.ug *
        p19VecNorm2
          (p19Column
            (p19Augment iteration.computedB iteration.computedC) j)
  computedC_numerically_nonsingular :
    semantics.small
      (iteration.ug *
        p19RectConditionF2 iteration.computedC
          iteration.computedCSpectrum.sigmaMin)
  combined_model_small :
    semantics.small
      ((iteration.epsilonC + iteration.epsilonB + iteration.ug) *
        p19RectConditionF2
          (p19StaticExactC system (basisFamily.basis k.1))
          iteration.exactCSpectrum.sigmaMin)
  solution_error_bound :
    p19VecNorm2 iteration.deltaX ≤
      iteration.epsilonX *
        p19VecNorm2 (p19RectMatVec (basisFamily.basis k.1) iteration.yHat)
  solution_small : semantics.small iteration.epsilonX

def p19IterationWellConditioned {n : ℕ}
    {system : P19Theorem31System n}
    {semantics : P19FirstOrderSemantics}
    {basisFamily : P19Theorem31BasisFamily system}
    {k : P19Theorem31Dimension n}
    (iteration : P19Algorithm2Iteration system semantics basisFamily k) : Prop :=
  1 / iteration.vHatSpectrum.sigmaMin ≤ 4 / 3 ∧
    iteration.vHatSpectrum.sigmaMax ≤ 4 / 3

def p19NearRankDeficient {m k : ℕ} (A : P19RectMatrix m k)
    (threshold : ℝ) : Prop :=
  ∃ x : P19Vector k,
    p19VecNorm2 x = 1 ∧
      p19VecNorm2 (p19RectMatVec A x) < threshold

def p19MGSNearDependence {n : ℕ}
    {system : P19Theorem31System n}
    {semantics : P19FirstOrderSemantics}
    {basisFamily : P19Theorem31BasisFamily system}
    {k : P19Theorem31Dimension n}
    (iteration : P19Algorithm2Iteration system semantics basisFamily k) : Prop :=
  ∀ phi : ℝ, 0 < phi →
    p19NearRankDeficient
      (p19Augment
        (fun i ↦ p19StaticExactB system i * phi)
        (p19StaticExactC system (basisFamily.basis k.1)))
      (iteration.dimensionFactor * (iteration.ug + iteration.epsilonC) *
        p19FrobNorm
          (p19Augment
            (fun i ↦ p19StaticExactB system i * phi)
            (p19StaticExactC system (basisFamily.basis k.1))))

structure P19Theorem31Family (n : ℕ)
    (semantics : P19FirstOrderSemantics) where
  system : P19Theorem31System n
  basisFamily : P19Theorem31BasisFamily system
  iteration : ∀ k : P19Theorem31Dimension n,
    P19Algorithm2Iteration system semantics basisFamily k

structure P19MGSSelectionLaw {n : ℕ}
    {semantics : P19FirstOrderSemantics}
    (family : P19Theorem31Family n semantics) where
  first_dimension_good :
    p19IterationWellConditioned
      (family.iteration
        ⟨1, Nat.zero_lt_one, family.system.dimension_pos⟩)
  loss_implies_near_dependence : ∀ (k : ℕ)
      (hkpos : 0 < k) (hklt : k < n),
    let current : P19Theorem31Dimension n :=
      ⟨k, hkpos, Nat.le_of_lt hklt⟩
    let next : P19Theorem31Dimension n :=
      ⟨k + 1, Nat.succ_pos k, Nat.succ_le_iff.mpr hklt⟩
    ¬ p19IterationWellConditioned (family.iteration next) →
      p19MGSNearDependence (family.iteration current)

noncomputable def p19StaticSplitOperator {n : ℕ}
    (system : P19Theorem31System n) (MRinv : P19Matrix n) :
    P19Matrix n :=
  p19SquareRectMul system.MLinv (p19SquareRectMul system.A MRinv)

noncomputable def p19StaticSplitInverse {n : ℕ}
    (system : P19Theorem31System n) (MR : P19Matrix n) :
    P19Matrix n :=
  p19SquareRectMul MR (p19SquareRectMul system.Ainv system.ML)

structure P19StaticRightQuantities {n : ℕ}
    {semantics : P19FirstOrderSemantics}
    (family : P19Theorem31Family n semantics)
    (k : P19Theorem31Dimension n)
    (MR MRinv : P19Matrix n) where
  mrzSpectrum :
    P19SingularValueData
      (p19SquareRectMul MR (family.basisFamily.basis k.1))
  mrz_sigmaMin_pos : 0 < mrzSpectrum.sigmaMin
  exactC_norm_pos :
    0 < p19FrobNorm
      (p19StaticExactC family.system (family.basisFamily.basis k.1))
  split_operator_norm_pos :
    0 < p19FrobNorm (p19StaticSplitOperator family.system MRinv)
  mr_condition_pos : 0 < p19ConditionNumberF MR MRinv
  split_condition_pos :
    0 < p19ConditionNumberF
      (p19StaticSplitOperator family.system MRinv)
      (p19StaticSplitInverse family.system MR)

noncomputable def p19StaticAlpha {n : ℕ}
    {semantics : P19FirstOrderSemantics}
    {family : P19Theorem31Family n semantics}
    {k : P19Theorem31Dimension n}
    (MR MRinv : P19Matrix n)
    (q : P19StaticRightQuantities family k MR MRinv) : ℝ :=
  (p19ConditionNumberF MR MRinv / q.mrzSpectrum.sigmaMin) *
    (p19FrobNorm
        (p19StaticExactC family.system (family.basisFamily.basis k.1)) /
      p19FrobNorm (p19StaticSplitOperator family.system MRinv))

noncomputable def p19StaticBeta {n : ℕ}
    {semantics : P19FirstOrderSemantics}
    {family : P19Theorem31Family n semantics}
    {k : P19Theorem31Dimension n}
    (MR MRinv : P19Matrix n)
    (q : P19StaticRightQuantities family k MR MRinv) : ℝ :=
  max 1
      ((p19FrobNorm
          (p19StaticExactC family.system (family.basisFamily.basis k.1)) /
          p19FrobNorm (p19StaticSplitOperator family.system MRinv)) /
        q.mrzSpectrum.sigmaMin) *
    p19ConditionNumberF MR MRinv

noncomputable def p19StaticLambda {n : ℕ}
    (system : P19Theorem31System n) (MR MRinv : P19Matrix n) : ℝ :=
  1 /
    p19ConditionNumberF
      (p19StaticSplitOperator system MRinv)
      (p19StaticSplitInverse system MR)

noncomputable def p19StaticXi {n : ℕ}
    {semantics : P19FirstOrderSemantics}
    {family : P19Theorem31Family n semantics}
    {k : P19Theorem31Dimension n}
    (MR MRinv : P19Matrix n)
    (q : P19StaticRightQuantities family k MR MRinv) : ℝ :=
  let run := family.iteration k
  p19ModularEnvelope (p19StaticAlpha MR MRinv q)
    (p19StaticBeta MR MRinv q)
    (p19StaticLambda family.system MR MRinv)
    run.epsilonC run.epsilonB run.ug run.epsilonX

structure P19StaticAppendixAExpansion {n : ℕ}
    {semantics : P19FirstOrderSemantics}
    (family : P19Theorem31Family n semantics)
    (k : P19Theorem31Dimension n)
    (MR MRinv : P19Matrix n)
    (q : P19StaticRightQuantities family k MR MRinv) where
  computationContribution : P19Vector n
  rhsContribution : P19Vector n
  gmresContribution : P19Vector n
  solutionContribution : P19Vector n
  remainder : P19Vector n
  error_decomposition :
    (family.iteration k).xHat - family.system.xExact =
      computationContribution + rhsContribution + gmresContribution +
        solutionContribution + remainder
  remainder_second_order :
    semantics.secondOrder
      (p19VecNorm2 remainder / p19VecNorm2 family.system.xExact)
  computation_gain_bound :
    p19VecNorm2 computationContribution /
          p19VecNorm2 family.system.xExact ≤
      (family.iteration k).dimensionFactor *
        p19ConditionNumberF
          (p19StaticSplitOperator family.system MRinv)
          (p19StaticSplitInverse family.system MR) *
        (p19StaticAlpha MR MRinv q *
          p19SafeRelativeMagnitude
            (p19FrobNorm (family.iteration k).deltaC)
            (p19FrobNorm
              (p19StaticExactC family.system
                (family.basisFamily.basis k.1))))
  rhs_gain_bound :
    p19VecNorm2 rhsContribution / p19VecNorm2 family.system.xExact ≤
      (family.iteration k).dimensionFactor *
        p19ConditionNumberF
          (p19StaticSplitOperator family.system MRinv)
          (p19StaticSplitInverse family.system MR) *
        (p19StaticBeta MR MRinv q *
          p19SafeRelativeMagnitude
            (p19VecNorm2 (family.iteration k).deltaB)
            (p19VecNorm2 (p19StaticExactB family.system)))
  gmres_gain_bound :
    p19VecNorm2 gmresContribution / p19VecNorm2 family.system.xExact ≤
      (family.iteration k).dimensionFactor *
        p19ConditionNumberF
          (p19StaticSplitOperator family.system MRinv)
          (p19StaticSplitInverse family.system MR) *
        (p19StaticBeta MR MRinv q * (family.iteration k).ug)
  solution_gain_bound :
    p19VecNorm2 solutionContribution /
          p19VecNorm2 family.system.xExact ≤
      p19ConditionNumberF
          (p19StaticSplitOperator family.system MRinv)
          (p19StaticSplitInverse family.system MR) *
        (p19StaticLambda family.system MR MRinv *
          p19SafeRelativeMagnitude
            (p19VecNorm2 (family.iteration k).deltaX)
            (p19VecNorm2
              (p19RectMatVec (family.basisFamily.basis k.1)
                (family.iteration k).yHat)))

structure P19StaticAppendixATheory {n : ℕ}
    {semantics : P19FirstOrderSemantics}
    (family : P19Theorem31Family n semantics) where
  rightQuantities : ∀ (k : P19Theorem31Dimension n)
      (MR MRinv : P19Matrix n), p19InversePair MR MRinv →
    P19StaticRightQuantities family k MR MRinv
  expansion : ∀ (k : P19Theorem31Dimension n),
    p19IterationWellConditioned (family.iteration k) →
    (k.1 = n ∨ p19MGSNearDependence (family.iteration k)) →
    P19Algorithm2Conditions (family.iteration k) →
    ∀ (MR MRinv : P19Matrix n) (hMR : p19InversePair MR MRinv),
      P19StaticAppendixAExpansion family k MR MRinv
        (rightQuantities k MR MRinv hMR)

noncomputable def p19OpNorm2 {n : ℕ} (A : Fin n → Fin n → ℝ) : ℝ :=
  @norm (Matrix (Fin n) (Fin n) ℝ)
    Matrix.instL2OpNormedAddCommGroup.toNorm
    (A : Matrix (Fin n) (Fin n) ℝ)

noncomputable def p19Kappa2 {n : ℕ}
    (A Ainv : Fin n → Fin n → ℝ) : ℝ :=
  p19OpNorm2 A * p19OpNorm2 Ainv

noncomputable def p19InitialResidual {n : ℕ} (A : P19Matrix n)
    (b xInitial : P19Vector n) : P19Vector n :=
  b - p19MatVec A xInitial

noncomputable def p19AbsRectMatVec {m k : ℕ} (A : P19RectMatrix m k)
    (x : P19Vector k) : P19Vector m :=
  fun i ↦ ∑ j : Fin k, |A i j| * |x j|

inductive P19StaticSquareKappaChoice where
  | frobenius
  | inducedTwo

noncomputable def p19StaticKappa (choice : P19StaticSquareKappaChoice)
    {n : ℕ} (A Ainv : P19Matrix n) : ℝ :=
  match choice with
  | .frobenius => p19ConditionNumberF A Ainv
  | .inducedTwo => p19Kappa2 A Ainv

structure P19StaticFixedRightPreconditioner {n : ℕ}
    {semantics : P19FirstOrderSemantics}
    (family : P19Theorem31Family n semantics) where
  MR : P19Matrix n
  MRinv : P19Matrix n
  MR_inverse : p19InversePair MR MRinv
  right_operator_inverse :
    p19InversePair (p19SquareRectMul family.system.A MRinv)
      (p19SquareRectMul MR family.system.Ainv)
  nontrivial : MR ≠ 1
  left_preconditioner_identity : family.system.ML = 1
  left_preconditioner_inverse_identity : family.system.MLinv = 1

noncomputable def p19StaticSystemKappa
    (choice : P19StaticSquareKappaChoice) {n : ℕ}
    {semantics : P19FirstOrderSemantics}
    (family : P19Theorem31Family n semantics) : ℝ :=
  p19StaticKappa choice family.system.A family.system.Ainv

noncomputable def p19StaticRightPreconditionerKappa
    (choice : P19StaticSquareKappaChoice) {n : ℕ}
    {semantics : P19FirstOrderSemantics}
    {family : P19Theorem31Family n semantics}
    (preconditioner : P19StaticFixedRightPreconditioner family) : ℝ :=
  p19StaticKappa choice preconditioner.MR preconditioner.MRinv

noncomputable def p19StaticRightOperatorKappa
    (choice : P19StaticSquareKappaChoice) {n : ℕ}
    {semantics : P19FirstOrderSemantics}
    {family : P19Theorem31Family n semantics}
    (preconditioner : P19StaticFixedRightPreconditioner family) : ℝ :=
  p19StaticKappa choice
    (p19SquareRectMul family.system.A preconditioner.MRinv)
    (p19SquareRectMul preconditioner.MR family.system.Ainv)

noncomputable def p19StaticCondition316Value
    (choice : P19StaticSquareKappaChoice) {n : ℕ}
    {semantics : P19FirstOrderSemantics}
    {family : P19Theorem31Family n semantics}
    (preconditioner : P19StaticFixedRightPreconditioner family)
    (ug um ua etaR rhoAR : ℝ) : ℝ :=
  max (ug * p19StaticRightOperatorKappa choice preconditioner)
    (max (ug * p19StaticRightPreconditionerKappa choice preconditioner)
      (max (um * etaR *
          p19StaticRightPreconditionerKappa choice preconditioner)
        (max (ua * p19StaticSystemKappa choice family * rhoAR)
          (ua * p19StaticRightOperatorKappa choice preconditioner *
            p19StaticRightPreconditionerKappa choice preconditioner))))

noncomputable def p19StaticRightAttainableEnvelope
    (choice : P19StaticSquareKappaChoice) {n : ℕ}
    {semantics : P19FirstOrderSemantics}
    {family : P19Theorem31Family n semantics}
    (preconditioner : P19StaticFixedRightPreconditioner family)
    (ug um ua etaR rhoAR : ℝ) : ℝ :=
  ug * p19StaticRightOperatorKappa choice preconditioner *
      p19StaticRightPreconditionerKappa choice preconditioner +
    um * etaR * p19StaticRightPreconditionerKappa choice preconditioner +
      ua * p19StaticSystemKappa choice family * rhoAR

noncomputable def p19StaticFlexibleAttainableEnvelope
    (choice : P19StaticSquareKappaChoice) {n : ℕ}
    {semantics : P19FirstOrderSemantics}
    {family : P19Theorem31Family n semantics}
    (preconditioner : P19StaticFixedRightPreconditioner family)
    (ug ua rhoAR : ℝ) : ℝ :=
  ug * p19StaticRightOperatorKappa choice preconditioner *
      p19StaticRightPreconditionerKappa choice preconditioner +
    ua * p19StaticSystemKappa choice family * rhoAR

structure P19StaticFixedRightCore {n : ℕ}
    {semantics : P19FirstOrderSemantics}
    (family : P19Theorem31Family n semantics)
    (preconditioner : P19StaticFixedRightPreconditioner family)
    (k : P19Theorem31Dimension n) where
  ug : ℝ
  um : ℝ
  ua : ℝ
  etaR : ℝ
  rhoAR : ℝ
  zHat : P19RectMatrix n k.1
  preconditionerDelta : Fin k.1 → P19Matrix n
  preconditioner_application : ∀ j,
    p19Column zHat j =
      p19MatVec (preconditioner.MRinv + preconditionerDelta j)
        (p19Column (family.iteration k).vHat j)
  matrixDelta : Fin k.1 → P19Matrix n
  matrix_application : ∀ j,
    p19Column (family.iteration k).computedC j =
      p19MatVec (family.system.A + matrixDelta j) (p19Column zHat j)
  search_space_equation : ∀ j,
    p19Column (family.basisFamily.basis k.1) j =
      p19Column zHat j +
        p19MatVec family.system.Ainv
          (p19MatVec (matrixDelta j) (p19Column zHat j))
  computation_exact : (family.iteration k).deltaC = 0
  computation_accuracy_zero : (family.iteration k).epsilonC = 0
  rhs_exact : (family.iteration k).deltaB = 0
  rhs_accuracy_zero : (family.iteration k).epsilonB = 0
  gmresMagnitude : ℝ
  basisPreconditionerMagnitude : ℝ
  matrixMagnitude : ℝ

structure P19StaticFixedRightCoreConditions
    (choice : P19StaticSquareKappaChoice) {n : ℕ}
    {semantics : P19FirstOrderSemantics}
    {family : P19Theorem31Family n semantics}
    {preconditioner : P19StaticFixedRightPreconditioner family}
    {k : P19Theorem31Dimension n}
    (core : P19StaticFixedRightCore family preconditioner k) where
  parameters_nonneg :
    0 ≤ core.ug ∧ 0 ≤ core.um ∧ 0 ≤ core.ua ∧ 0 ≤ core.etaR ∧
      0 ≤ core.rhoAR
  magnitudes_nonneg :
    0 ≤ core.gmresMagnitude ∧ 0 ≤ core.basisPreconditionerMagnitude ∧
      0 ≤ core.matrixMagnitude
  least_squares_solution :
    p19IsLeastSquaresSolution
      ((family.iteration k).computedC +
        (family.iteration k).leastSquaresDeltaC)
      ((family.iteration k).computedB +
        (family.iteration k).leastSquaresDeltaB)
      (family.iteration k).yHat
  least_squares_error_covered : ∀ j : Fin (k.1 + 1),
    p19VecNorm2
        (p19Column
          (p19Augment (family.iteration k).leastSquaresDeltaB
            (family.iteration k).leastSquaresDeltaC) j) ≤
      core.gmresMagnitude *
        p19VecNorm2
          (p19Column
            (p19Augment (family.iteration k).computedB
              (family.iteration k).computedC) j)
  basis_preconditioner_error_covered : ∀ j,
    p19FrobNorm (core.preconditionerDelta j) ≤
      core.basisPreconditionerMagnitude * p19FrobNorm preconditioner.MRinv
  matrix_error_covered : ∀ j i q,
    |core.matrixDelta j i q| ≤ core.matrixMagnitude * |family.system.A i q|
  gmres_magnitude_bound :
    core.gmresMagnitude ≤ (family.iteration k).dimensionFactor * core.ug
  basis_preconditioner_magnitude_bound :
    core.basisPreconditionerMagnitude ≤
      (family.iteration k).dimensionFactor * core.um * core.etaR
  matrix_magnitude_bound :
    core.matrixMagnitude ≤ (family.iteration k).dimensionFactor * core.ua
  rho_denominator_pos :
    0 < p19VecNorm2
      (p19RectMatVec core.zHat (family.iteration k).yHat)
  rho_equation :
    core.rhoAR =
      p19VecNorm2 (p19AbsRectMatVec core.zHat (family.iteration k).yHat) /
        p19VecNorm2 (p19RectMatVec core.zHat (family.iteration k).yHat)
  condition316 :
    semantics.small
      (p19StaticCondition316Value choice preconditioner
        core.ug core.um core.ua core.etaR core.rhoAR)

structure P19StaticRightIteration {n : ℕ}
    {semantics : P19FirstOrderSemantics}
    (family : P19Theorem31Family n semantics)
    (preconditioner : P19StaticFixedRightPreconditioner family)
    (k : P19Theorem31Dimension n) where
  core : P19StaticFixedRightCore family preconditioner k
  solutionBasisDelta : P19RectMatrix n k.1
  solutionPreconditionerDelta : P19Matrix n
  solution_equation :
    (family.iteration k).xHat =
      p19MatVec (preconditioner.MRinv + solutionPreconditionerDelta)
        (p19RectMatVec
          ((family.iteration k).vHat + solutionBasisDelta)
          (family.iteration k).yHat)
  reapplicationMagnitude : ℝ

structure P19StaticRightConditions
    (choice : P19StaticSquareKappaChoice) {n : ℕ}
    {semantics : P19FirstOrderSemantics}
    {family : P19Theorem31Family n semantics}
    {preconditioner : P19StaticFixedRightPreconditioner family}
    {k : P19Theorem31Dimension n}
    (iteration : P19StaticRightIteration family preconditioner k) where
  core : P19StaticFixedRightCoreConditions choice iteration.core
  reapplication_magnitude_nonneg : 0 ≤ iteration.reapplicationMagnitude
  solution_basis_error_covered : ∀ i j,
    |iteration.solutionBasisDelta i j| ≤
      iteration.core.gmresMagnitude * |(family.iteration k).vHat i j|
  solution_preconditioner_error_covered :
    p19FrobNorm iteration.solutionPreconditionerDelta ≤
      iteration.reapplicationMagnitude * p19FrobNorm preconditioner.MRinv
  reapplication_magnitude_bound :
    iteration.reapplicationMagnitude ≤
      (family.iteration k).dimensionFactor *
        iteration.core.um * iteration.core.etaR

structure P19StaticFlexibleIteration {n : ℕ}
    {semantics : P19FirstOrderSemantics}
    (family : P19Theorem31Family n semantics)
    (preconditioner : P19StaticFixedRightPreconditioner family)
    (k : P19Theorem31Dimension n) where
  core : P19StaticFixedRightCore family preconditioner k
  solutionBasisDelta : P19RectMatrix n k.1
  solution_equation :
    (family.iteration k).xHat =
      p19RectMatVec (core.zHat + solutionBasisDelta)
        (family.iteration k).yHat

structure P19StaticFlexibleConditions
    (choice : P19StaticSquareKappaChoice) {n : ℕ}
    {semantics : P19FirstOrderSemantics}
    {family : P19Theorem31Family n semantics}
    {preconditioner : P19StaticFixedRightPreconditioner family}
    {k : P19Theorem31Dimension n}
    (iteration : P19StaticFlexibleIteration family preconditioner k) where
  core : P19StaticFixedRightCoreConditions choice iteration.core
  solution_basis_error_covered : ∀ i j,
    |iteration.solutionBasisDelta i j| ≤
      iteration.core.gmresMagnitude * |iteration.core.zHat i j|

structure P19StaticRightFamily (n : ℕ)
    (semantics : P19FirstOrderSemantics) where
  family : P19Theorem31Family n semantics
  preconditioner : P19StaticFixedRightPreconditioner family
  iteration : ∀ k : P19Theorem31Dimension n,
    P19StaticRightIteration family preconditioner k

structure P19StaticFlexibleFamily (n : ℕ)
    (semantics : P19FirstOrderSemantics) where
  family : P19Theorem31Family n semantics
  preconditioner : P19StaticFixedRightPreconditioner family
  iteration : ∀ k : P19Theorem31Dimension n,
    P19StaticFlexibleIteration family preconditioner k

structure P19StaticRightAppendixCExpansion
    (choice : P19StaticSquareKappaChoice) {n : ℕ}
    {semantics : P19FirstOrderSemantics}
    (right : P19StaticRightFamily n semantics)
    (k : P19Theorem31Dimension n) where
  gmresContribution : P19Vector n
  reapplicationContribution : P19Vector n
  matrixContribution : P19Vector n
  remainder : P19Vector n
  error_decomposition :
    (right.family.iteration k).xHat - right.family.system.xExact =
      gmresContribution + reapplicationContribution + matrixContribution +
        remainder
  remainder_second_order :
    semantics.secondOrder
      (p19VecNorm2 remainder / p19VecNorm2 right.family.system.xExact)
  gmres_gain_bound :
    p19VecNorm2 gmresContribution /
          p19VecNorm2 right.family.system.xExact ≤
      (right.iteration k).core.gmresMagnitude *
        p19StaticRightOperatorKappa choice right.preconditioner *
          p19StaticRightPreconditionerKappa choice right.preconditioner
  reapplication_gain_bound :
    p19VecNorm2 reapplicationContribution /
          p19VecNorm2 right.family.system.xExact ≤
      (right.iteration k).reapplicationMagnitude *
        p19StaticRightPreconditionerKappa choice right.preconditioner
  matrix_gain_bound :
    p19VecNorm2 matrixContribution /
          p19VecNorm2 right.family.system.xExact ≤
      (right.iteration k).core.matrixMagnitude *
        p19StaticSystemKappa choice right.family *
          (right.iteration k).core.rhoAR

structure P19StaticFlexibleAppendixDExpansion
    (choice : P19StaticSquareKappaChoice) {n : ℕ}
    {semantics : P19FirstOrderSemantics}
    (flexible : P19StaticFlexibleFamily n semantics)
    (k : P19Theorem31Dimension n) where
  gmresContribution : P19Vector n
  matrixContribution : P19Vector n
  remainder : P19Vector n
  error_decomposition :
    (flexible.family.iteration k).xHat - flexible.family.system.xExact =
      gmresContribution + matrixContribution + remainder
  remainder_second_order :
    semantics.secondOrder
      (p19VecNorm2 remainder / p19VecNorm2 flexible.family.system.xExact)
  gmres_gain_bound :
    p19VecNorm2 gmresContribution /
          p19VecNorm2 flexible.family.system.xExact ≤
      (flexible.iteration k).core.gmresMagnitude *
        p19StaticRightOperatorKappa choice flexible.preconditioner *
          p19StaticRightPreconditionerKappa choice flexible.preconditioner
  matrix_gain_bound :
    p19VecNorm2 matrixContribution /
          p19VecNorm2 flexible.family.system.xExact ≤
      (flexible.iteration k).core.matrixMagnitude *
        p19StaticSystemKappa choice flexible.family *
          (flexible.iteration k).core.rhoAR

structure P19StaticRightAppendixCTheory
    (choice : P19StaticSquareKappaChoice) {n : ℕ}
    {semantics : P19FirstOrderSemantics}
    (right : P19StaticRightFamily n semantics) where
  expansion : ∀ (k : P19Theorem31Dimension n),
    p19IterationWellConditioned (right.family.iteration k) →
    (k.1 = n ∨ p19MGSNearDependence (right.family.iteration k)) →
    P19StaticRightConditions choice (right.iteration k) →
      P19StaticRightAppendixCExpansion choice right k

structure P19StaticFlexibleAppendixDTheory
    (choice : P19StaticSquareKappaChoice) {n : ℕ}
    {semantics : P19FirstOrderSemantics}
    (flexible : P19StaticFlexibleFamily n semantics) where
  expansion : ∀ (k : P19Theorem31Dimension n),
    p19IterationWellConditioned (flexible.family.iteration k) →
    (k.1 = n ∨ p19MGSNearDependence (flexible.family.iteration k)) →
    P19StaticFlexibleConditions choice (flexible.iteration k) →
      P19StaticFlexibleAppendixDExpansion choice flexible k

end HighamBench
