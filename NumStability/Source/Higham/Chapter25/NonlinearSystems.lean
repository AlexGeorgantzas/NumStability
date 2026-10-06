/-
Copyright (c) 2026 QED. All rights reserved.
Released under Apache 2.0 license as described in LICENSES/Apache-2.0.txt.
SPDX-License-Identifier: Apache-2.0
See LICENSES/Apache-2.0.txt.
Authors: QED
-/
import NumStability.Analysis.Rounding
import NumStability.Analysis.MatrixAlgebra
import NumStability.Algorithms.IterativeRefinement
import Mathlib.Analysis.Calculus.FDeriv.Basic
import Mathlib.Analysis.Calculus.ImplicitContDiff
import Mathlib.Analysis.Normed.Operator.NNNorm
import Mathlib.Analysis.SpecialFunctions.Pow.Real
import Mathlib.Data.Real.Pointwise
import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.NormNum
import Mathlib.Tactic.Ring

namespace NumStability

open scoped BigOperators
open scoped Pointwise
open Filter Topology

/-! # Higham Chapter 25: nonlinear systems and Newton's method

This module records the exact algebraic content of equations (25.1)--(25.7),
(25.10)--(25.14), and the structured example (25.12)--(25.13).  The limiting
claims in Theorems 25.1 and 25.2 use an undefined approximation relation and
the prose phrase "decreases until"; they are therefore tracked in the chapter
ledger rather than replaced by a weaker theorem.
-/

section NewtonStep

variable {n : ℕ}

/-- Equation (25.1): the Newton correction solves `J(xᵢ)dᵢ = -F(xᵢ)`. -/
def higham25NewtonEquation
    (J : Fin n → Fin n → ℝ) (F d : Fin n → ℝ) : Prop :=
  ∀ i, ∑ j, J i j * d j = -F i

/-- The two-line implementation immediately following (25.1). -/
def higham25ExactNewtonStep
    (J : Fin n → Fin n → ℝ) (F x xNext : Fin n → ℝ) : Prop :=
  ∃ d, higham25NewtonEquation J F d ∧ xNext = fun i => x i + d i

/-- Unfolded source-facing form of the exact Newton step. -/
theorem higham25_eq25_1_implementation
    (J : Fin n → Fin n → ℝ) (F x xNext : Fin n → ℝ) :
    higham25ExactNewtonStep J F x xNext ↔
      ∃ d : Fin n → ℝ, (∀ i, ∑ j, J i j * d j = -F i) ∧
        xNext = fun i => x i + d i := by
  rfl

/-- Equation (25.2), represented without pretending that a possibly singular
matrix has an inverse: `d̂ᵢ` is any exact solution of the perturbed linear
system and the final addition has error `εᵢ`. -/
structure Higham25RoundedNewtonStep
    (J : Fin n → Fin n → ℝ) (F x xNext : Fin n → ℝ) where
  /-- Error in forming the residual. -/
  e : Fin n → ℝ
  /-- Error in forming the Jacobian and solving the Newton equation. -/
  E : Fin n → Fin n → ℝ
  /-- Error in adding the correction to the current iterate. -/
  ε : Fin n → ℝ
  /-- The computed Newton correction. -/
  d : Fin n → ℝ
  solve : ∀ i, ∑ j, (J i j + E i j) * d j = -(F i + e i)
  update : xNext = fun i => x i + d i + ε i

/-- Equation (25.3): residual-evaluation error budget. -/
def higham25ResidualErrorBound
    (u : ℝ) (FNorm psi eNorm : ℝ) : Prop :=
  eNorm ≤ u * FNorm + psi

/-- Equation (25.4): Jacobian-formation and solver error budget. -/
def higham25JacobianErrorBound
    (u phi ENorm : ℝ) : Prop :=
  ENorm ≤ u * phi

/-- The displayed addition-error budget following (25.4). -/
def higham25AdditionErrorBound
    (u xNorm dNorm epsilonNorm : ℝ) : Prop :=
  epsilonNorm ≤ u * (xNorm + dNorm)

/-- Equation (25.5), kept as the exact scalar smallness premise. -/
def higham25Eq25_5 (u kappaJ : ℝ) : Prop :=
  u * kappaJ ≤ (1 : ℝ) / 8

/-- Equation (25.6), kept as the exact per-iterate smallness premise. -/
def higham25Eq25_6 (u invJNorm phi : ℝ) : Prop :=
  u * invJNorm * phi ≤ (1 : ℝ) / 8

/-- Equation (25.7), kept as the exact initial-neighborhood premise. -/
def higham25Eq25_7 (beta invJStarNorm initialError : ℝ) : Prop :=
  beta * invJStarNorm * initialError ≤ (1 : ℝ) / 8

end NewtonStep

section LinearSystemSpecialization

variable {n : ℕ}

/-- The exact residual used by iterative refinement, viewed as the nonlinear
function `F(x) = b - A x` from Higham Section 25.3. -/
noncomputable def higham25LinearSystemResidual
    (A : Fin n → Fin n → ℝ) (b x : Fin n → ℝ) : Fin n → ℝ :=
  fun i ↦ b i - ∑ j : Fin n, A i j * x j

/-- A Newton correction for `F(x) = b - A x` is exactly the usual iterative
refinement correction `A d = b - A x`.  The Jacobian of the displayed `F` is
`-A`; the minus sign cancels the minus sign in the Newton equation. -/
theorem higham25_linearSystem_newtonCorrection_iff_refinementCorrection
    (A : Fin n → Fin n → ℝ) (b x d : Fin n → ℝ) :
    higham25NewtonEquation (fun i j ↦ -A i j)
        (higham25LinearSystemResidual A b x) d ↔
      ∀ i : Fin n,
        ∑ j : Fin n, A i j * d j = higham25LinearSystemResidual A b x i := by
  unfold higham25NewtonEquation higham25LinearSystemResidual
  constructor
  · intro h i
    have hi := congrArg Neg.neg (h i)
    simpa only [neg_mul, Finset.sum_neg_distrib, neg_neg] using hi
  · intro h i
    have hi := congrArg Neg.neg (h i)
    simpa only [neg_mul, Finset.sum_neg_distrib, neg_neg] using hi

/-- The Jacobian of the linear residual is constant. -/
noncomputable def higham25LinearSystemJacobian
    (A : Fin n → Fin n → ℝ) (_x : Fin n → ℝ) : Fin n → Fin n → ℝ :=
  fun i j ↦ -A i j

theorem higham25_linearSystemJacobian_constant
    (A : Fin n → Fin n → ℝ) (x y : Fin n → ℝ) :
    higham25LinearSystemJacobian A x = higham25LinearSystemJacobian A y := by
  rfl

/-- Consequently the Lipschitz constant in Section 25.3 can be chosen to be
zero (shown here in the Frobenius/Euclidean norm pair). -/
theorem higham25_linearSystemJacobian_lipschitz_zero
    (A : Fin n → Fin n → ℝ) (x y : Fin n → ℝ) :
    frobNorm (fun i j ↦
        higham25LinearSystemJacobian A x i j -
          higham25LinearSystemJacobian A y i j) ≤
      0 * vecNorm2 (fun i ↦ x i - y i) := by
  have hz : frobNorm (fun i j ↦
      higham25LinearSystemJacobian A x i j -
        higham25LinearSystemJacobian A y i j) = 0 := by
    rw [frobNorm_eq_zero_iff]
    intro i j
    simp [higham25LinearSystemJacobian]
  simp [hz]

/-- Genuine Chapter 12 bridge for the Section 25.3 specialization: the actual
rounded residual evaluator satisfies the conventional `gamma_(n+1)` bound for
the nonlinear residual `F(x) = b - A x`. -/
theorem higham25_linearSystem_actualResidual_bridge_ch12
    (fp : FPModel) (A : Fin n → Fin n → ℝ) (x b : Fin n → ℝ)
    (hn : gammaValid fp n) (hn1 : gammaValid fp (n + 1)) :
    ∀ i : Fin n,
      |fl_residual fp n A x b i - higham25LinearSystemResidual A b x i| ≤
        gamma fp (n + 1) *
          (|b i| + ∑ j : Fin n, |A i j| * |x j|) := by
  simpa [higham25LinearSystemResidual] using
    conventional_residual_error fp n A x b hn hn1

/-- Frobenius norm of the derivative product
`A⁻¹ [x₁ I  x₂ I  ⋯  xₙ I]` in the linear-system specialization of
equation (25.11), written as its literal three-index sum. -/
noncomputable def higham25LinearSystemDataDerivativeFrob
    (Ainv : Fin n → Fin n → ℝ) (x : Fin n → ℝ) : ℝ :=
  Real.sqrt (∑ i : Fin n, ∑ p : Fin n, ∑ q : Fin n,
    (Ainv i p * x q) ^ 2)

/-- The block derivative product has Frobenius norm
`||A⁻¹||_F ||x||₂`, which is the calculation printed below (25.11). -/
theorem higham25_linearSystemDataDerivativeFrob_eq
    (Ainv : Fin n → Fin n → ℝ) (x : Fin n → ℝ) :
    higham25LinearSystemDataDerivativeFrob Ainv x =
      frobNorm Ainv * vecNorm2 x := by
  have hfactor :
      (∑ i : Fin n, ∑ p : Fin n, ∑ q : Fin n,
          (Ainv i p * x q) ^ 2) =
        frobNormSq Ainv * vecNorm2Sq x := by
    simp_rw [mul_pow]
    calc
      (∑ i : Fin n, ∑ p : Fin n, ∑ q : Fin n,
          Ainv i p ^ 2 * x q ^ 2) =
          ∑ i : Fin n, ∑ p : Fin n,
            Ainv i p ^ 2 * (∑ q : Fin n, x q ^ 2) := by
              apply Finset.sum_congr rfl
              intro i _
              apply Finset.sum_congr rfl
              intro p _
              rw [Finset.mul_sum]
      _ = ∑ i : Fin n,
            (∑ p : Fin n, Ainv i p ^ 2) *
              (∑ q : Fin n, x q ^ 2) := by
              apply Finset.sum_congr rfl
              intro i _
              rw [Finset.sum_mul]
      _ = (∑ i : Fin n, ∑ p : Fin n, Ainv i p ^ 2) *
            (∑ q : Fin n, x q ^ 2) := by
              rw [Finset.sum_mul]
      _ = frobNormSq Ainv * vecNorm2Sq x := by
              rfl
  unfold higham25LinearSystemDataDerivativeFrob
  rw [hfactor, Real.sqrt_mul (frobNormSq_nonneg Ainv)]
  simp [frobNorm_eq_sqrt_frobNormSq, vecNorm2]

/-- Therefore the relative condition number in (25.11), with data
`d = vec(A)` and Frobenius norms, is exactly `||A⁻¹||_F ||A||_F`. -/
theorem higham25_linearSystem_condition_frobenius
    (A Ainv : Fin n → Fin n → ℝ) (x : Fin n → ℝ)
    (hx : vecNorm2 x ≠ 0) :
    higham25LinearSystemDataDerivativeFrob Ainv x *
        frobNorm A / vecNorm2 x =
      frobNorm Ainv * frobNorm A := by
  rw [higham25_linearSystemDataDerivativeFrob_eq]
  field_simp [hx]

end LinearSystemSpecialization

section Eigenproblem

variable {n : ℕ}

/-- Equation (25.10): eigenproblem residual with coordinate normalization. -/
def higham25EigenResidual
    (A : Fin n → Fin n → ℝ) (s : Fin n)
    (x : Fin n → ℝ) (lambda : ℝ) : (Fin n → ℝ) × ℝ :=
  (fun i => (∑ j, A i j * x j) - lambda * x i, x s - 1)

/-- Vanishing of (25.10) is exactly the eigen-equation together with the
chosen coordinate normalization. -/
theorem higham25_eq25_10_zero_iff
    (A : Fin n → Fin n → ℝ) (s : Fin n)
    (x : Fin n → ℝ) (lambda : ℝ) :
    higham25EigenResidual A s x lambda = (0, 0) ↔
      (∀ i, ∑ j, A i j * x j = lambda * x i) ∧ x s = 1 := by
  constructor
  · intro h
    have hfirst := congrArg Prod.fst h
    have hsecond := congrArg Prod.snd h
    constructor
    · intro i
      have hi := congrFun hfirst i
      simp [higham25EigenResidual] at hi
      linarith
    · simp [higham25EigenResidual] at hsecond
      linarith
  · rintro ⟨heig, hnorm⟩
    apply Prod.ext
    · funext i
      simp [higham25EigenResidual, heig i]
    · simp [higham25EigenResidual, hnorm]

end Eigenproblem

section Conditioning

variable {X D Y : Type*}
variable [AddCommGroup X] [AddCommGroup Y]

/-- Exact first-order algebra behind (25.11).  If `L` is a left inverse of
the derivative in the solution variable, the linearized equation determines
the solution perturbation as `-L (F_d Δd)`. -/
theorem higham25_eq25_11_first_order
    (Fx : X → Y) (Fd : D → Y) (L : Y → X)
    (hLNeg : ∀ a, L (-a) = -L a)
    (hleft : ∀ x, L (Fx x) = x)
    (dx : X) (dd : D) (hlinearized : Fx dx + Fd dd = 0) :
    dx = -L (Fd dd) := by
  have hfx : Fx dx = -(Fd dd) := by
    exact eq_neg_of_add_eq_zero_left hlinearized
  calc
    dx = L (Fx dx) := (hleft dx).symm
    _ = L (-(Fd dd)) := by rw [hfx]
    _ = -L (Fd dd) := hLNeg _

/-- Scalar form of the relative condition expression in equation (25.11). -/
noncomputable def higham25Eq25_11Condition
    (derivativeGain dataNorm solutionNorm : ℝ) : ℝ :=
  derivativeGain * dataNorm / solutionNorm

/-- The normalized closed-ball supremum in the linearized (25.11) problem. -/
noncomputable def higham25LinearizedRelativeCondition
    {D X : Type*} [NormedAddCommGroup D] [NormedSpace ℝ D]
    [NormedAddCommGroup X] [NormedSpace ℝ X]
    (L : D →L[ℝ] X) (dataNorm solutionNorm : ℝ) : ℝ :=
  sSup ((fun h => ‖L h‖ * dataNorm / solutionNorm) ''
    Metric.closedBall 0 1)

/-- The linearized supremum is exactly the operator-norm expression on the
right of (25.11). -/
theorem higham25_linearizedRelativeCondition_eq
    {D X : Type*} [NormedAddCommGroup D] [NormedSpace ℝ D]
    [NormedAddCommGroup X] [NormedSpace ℝ X]
    (L : D →L[ℝ] X) (dataNorm solutionNorm : ℝ)
    (hdata : 0 ≤ dataNorm) (hsolution : 0 < solutionNorm) :
    higham25LinearizedRelativeCondition L dataNorm solutionNorm =
      ‖L‖ * dataNorm / solutionNorm := by
  let c := dataNorm / solutionNorm
  have hc : 0 ≤ c := div_nonneg hdata hsolution.le
  have hset :
      ((fun h => ‖L h‖ * dataNorm / solutionNorm) ''
          Metric.closedBall (0 : D) 1) =
        c • ((fun h => ‖L h‖) '' Metric.closedBall (0 : D) 1) := by
    ext y
    constructor
    · rintro ⟨h, hh, rfl⟩
      refine ⟨‖L h‖, ⟨h, hh, rfl⟩, ?_⟩
      simp [c, smul_eq_mul]
      ring
    · rintro ⟨z, ⟨h, hh, rfl⟩, rfl⟩
      refine ⟨h, hh, ?_⟩
      simp [c, smul_eq_mul]
      ring
  unfold higham25LinearizedRelativeCondition
  rw [hset, Real.sSup_smul_of_nonneg hc,
    ContinuousLinearMap.sSup_unitClosedBall_eq_norm]
  simp [c, smul_eq_mul]
  ring

theorem higham25_sSup_closedBall_eq_mul_opNorm
    {D X : Type*} [NormedAddCommGroup D] [NormedSpace ℝ D]
    [NormedAddCommGroup X] [NormedSpace ℝ X]
    (L : D →L[ℝ] X) (r : ℝ) (hr : 0 ≤ r) :
    sSup ((fun h => ‖L h‖) '' Metric.closedBall (0 : D) r) = r * ‖L‖ := by
  rcases hr.eq_or_lt with rfl | hrpos
  · simp [Metric.closedBall_zero]
  · have hset :
        ((fun h => ‖L h‖) '' Metric.closedBall (0 : D) r) =
          r • ((fun h => ‖L h‖) '' Metric.closedBall (0 : D) 1) := by
      ext y
      constructor
      · rintro ⟨h, hh, rfl⟩
        let z : D := r⁻¹ • h
        have hz : z ∈ Metric.closedBall (0 : D) 1 := by
          rw [mem_closedBall_zero_iff]
          simp [z, norm_smul, abs_of_pos hrpos]
          have hhnorm := mem_closedBall_zero_iff.mp hh
          exact (inv_mul_le_one₀ hrpos).2 hhnorm
        refine ⟨‖L z‖, ⟨z, hz, rfl⟩, ?_⟩
        simp [z, smul_eq_mul, norm_smul, abs_of_pos hrpos]
        field_simp [ne_of_gt hrpos]
      · rintro ⟨zv, ⟨z, hz, rfl⟩, rfl⟩
        refine ⟨r • z, ?_, ?_⟩
        · rw [mem_closedBall_zero_iff, norm_smul, Real.norm_eq_abs,
            abs_of_pos hrpos]
          have hznorm := mem_closedBall_zero_iff.mp hz
          nlinarith
        · simp [smul_eq_mul, norm_smul, abs_of_pos hrpos]
    rw [hset, Real.sSup_smul_of_nonneg hrpos.le,
      ContinuousLinearMap.sSup_unitClosedBall_eq_norm]
    simp [smul_eq_mul]

/-- The literal epsilon-indexed supremum in the linearized version of the
condition-number definition preceding (25.11). -/
noncomputable def higham25LinearizedEpsilonCondition
    {D X : Type*} [NormedAddCommGroup D] [NormedSpace ℝ D]
    [NormedAddCommGroup X] [NormedSpace ℝ X]
    (L : D →L[ℝ] X) (dataNorm solutionNorm epsilon : ℝ) : ℝ :=
  sSup ((fun dd => ‖L dd‖ / (epsilon * solutionNorm)) ''
    Metric.closedBall 0 (epsilon * dataNorm))

theorem higham25_linearizedEpsilonCondition_eq
    {D X : Type*} [NormedAddCommGroup D] [NormedSpace ℝ D]
    [NormedAddCommGroup X] [NormedSpace ℝ X]
    (L : D →L[ℝ] X) (dataNorm solutionNorm epsilon : ℝ)
    (hdata : 0 ≤ dataNorm) (hsolution : 0 < solutionNorm)
    (hepsilon : 0 < epsilon) :
    higham25LinearizedEpsilonCondition L dataNorm solutionNorm epsilon =
      ‖L‖ * dataNorm / solutionNorm := by
  let c := (epsilon * solutionNorm)⁻¹
  have hc : 0 ≤ c := inv_nonneg.mpr (mul_nonneg hepsilon.le hsolution.le)
  have hset :
      ((fun dd => ‖L dd‖ / (epsilon * solutionNorm)) ''
          Metric.closedBall (0 : D) (epsilon * dataNorm)) =
        c • ((fun dd => ‖L dd‖) ''
          Metric.closedBall (0 : D) (epsilon * dataNorm)) := by
    ext y
    constructor
    · rintro ⟨dd, hdd, rfl⟩
      refine ⟨‖L dd‖, ⟨dd, hdd, rfl⟩, ?_⟩
      simp [c, smul_eq_mul, div_eq_mul_inv]
      ring
    · rintro ⟨z, ⟨dd, hdd, rfl⟩, rfl⟩
      refine ⟨dd, hdd, ?_⟩
      simp [c, smul_eq_mul, div_eq_mul_inv]
      ring
  unfold higham25LinearizedEpsilonCondition
  rw [hset, Real.sSup_smul_of_nonneg hc,
    higham25_sSup_closedBall_eq_mul_opNorm L (epsilon * dataNorm)
      (mul_nonneg hepsilon.le hdata)]
  simp [c, smul_eq_mul]
  field_simp [ne_of_gt hepsilon, ne_of_gt hsolution]

/-- Therefore the linearized shrinking-ball supremum has the exact limit in
(25.11); the remaining nonlinear step is to compare the implicit solution map
with this derivative model. -/
theorem higham25_linearizedEpsilonCondition_tendsto
    {D X : Type*} [NormedAddCommGroup D] [NormedSpace ℝ D]
    [NormedAddCommGroup X] [NormedSpace ℝ X]
    (L : D →L[ℝ] X) (dataNorm solutionNorm : ℝ)
    (hdata : 0 ≤ dataNorm) (hsolution : 0 < solutionNorm) :
    Filter.Tendsto (fun epsilon =>
      higham25LinearizedEpsilonCondition L dataNorm solutionNorm epsilon)
      (nhdsWithin 0 (Set.Ioi 0))
      (nhds (‖L‖ * dataNorm / solutionNorm)) := by
  have heq : Filter.EventuallyEq (nhdsWithin 0 (Set.Ioi 0))
      (fun epsilon =>
        higham25LinearizedEpsilonCondition L dataNorm solutionNorm epsilon)
      (fun _ => ‖L‖ * dataNorm / solutionNorm) := by
    filter_upwards [self_mem_nhdsWithin] with epsilon hepsilon
    exact higham25_linearizedEpsilonCondition_eq L dataNorm solutionNorm epsilon
      hdata hsolution hepsilon
  exact tendsto_const_nhds.congr' heq.symm

/-- The literal perturbed equation occurring in the condition-number
definition before (25.11).  The predicate keeps the base solution and base
data visible: a feasible pair satisfies `F (xStar + dx) (dStar + dd) = 0`. -/
def higham25PerturbedSolutionPredicate
    {X D Y : Type*} [Add X] [Add D] [Zero Y]
    (F : X → D → Y) (xStar : X) (dStar : D) (dx : X) (dd : D) : Prop :=
  F (xStar + dx) (dStar + dd) = 0

/-- Feasible normalized perturbation values in the literal supremum preceding
(25.11), restricted to an explicit solution-perturbation domain. -/
def higham25ActualConditionValues
    {D X : Type*} [PseudoMetricSpace D] [Zero D] [Norm X]
    (isSolution : X → D → Prop) (solutionDomain : Set X)
    (dataNorm solutionNorm epsilon : ℝ) : Set ℝ :=
  {q | ∃ dx ∈ solutionDomain, ∃ dd ∈ Metric.closedBall (0 : D)
      (epsilon * dataNorm),
      isSolution dx dd ∧ q = ‖dx‖ / (epsilon * solutionNorm)}

/-- The source's epsilon-indexed actual feasible supremum. -/
noncomputable def higham25ActualEpsilonCondition
    {D X : Type*} [PseudoMetricSpace D] [Zero D] [Norm X]
    (isSolution : X → D → Prop) (solutionDomain : Set X)
    (dataNorm solutionNorm epsilon : ℝ) : ℝ :=
  sSup (higham25ActualConditionValues isSolution solutionDomain
    dataNorm solutionNorm epsilon)

/-- An explicit-domain solution-map contract.  It is not a condition-number
hypothesis: it states existence and uniqueness of the actual nonlinear
solutions represented by `phi`, including the base solution. -/
structure Higham25ActualSolutionMapContract
    {D X : Type*} [Zero D] [Zero X]
    (isSolution : X → D → Prop) (solutionDomain : Set X)
    (phi : D → X) : Prop where
  map_zero : phi 0 = 0
  zero_mem : (0 : X) ∈ solutionDomain
  zero_solves : isSolution 0 0
  mapsTo : ∀ dd, phi dd ∈ solutionDomain
  solves : ∀ dd, isSolution (phi dd) dd
  unique : ∀ dx ∈ solutionDomain, ∀ dd, isSolution dx dd → dx = phi dd

/-- The source-facing local solution-map contract behind (25.11).  Both
domains are genuine neighborhoods of the base point; existence and
uniqueness are asserted only there, exactly as in the implicit-function
theorem used by Higham. -/
structure Higham25LocalSolutionMapContract
    {D X : Type*} [TopologicalSpace D] [TopologicalSpace X] [Zero D] [Zero X]
    (isSolution : X → D → Prop) (dataDomain : Set D)
    (solutionDomain : Set X) (phi : D → X) : Prop where
  data_mem_nhds : dataDomain ∈ nhds (0 : D)
  solution_mem_nhds : solutionDomain ∈ nhds (0 : X)
  map_zero : phi 0 = 0
  mapsTo : ∀ dd ∈ dataDomain, phi dd ∈ solutionDomain
  solves : ∀ dd ∈ dataDomain, isSolution (phi dd) dd
  unique : ∀ dx ∈ solutionDomain, ∀ dd ∈ dataDomain,
    isSolution dx dd → dx = phi dd

/-- The hypotheses printed before (25.11) give the precise Mathlib
implicit-function predicate: the full derivative splits into the data
partial `Fd` and an invertible solution partial `Fx`. -/
theorem higham25_isContDiffImplicitAt_of_partialEquiv
    {D X Y : Type*}
    [NormedAddCommGroup D] [NormedSpace ℝ D]
    [NormedAddCommGroup X] [NormedSpace ℝ X]
    [NormedAddCommGroup Y] [NormedSpace ℝ Y]
    (f : D × X → Y) (Fd : D →L[ℝ] Y) (Fx : X ≃L[ℝ] Y)
    (hderiv : HasFDerivAt f
      (Fd.comp (ContinuousLinearMap.fst ℝ D X) +
        Fx.toContinuousLinearMap.comp (ContinuousLinearMap.snd ℝ D X)) (0, 0))
    (hcont : ContDiffAt ℝ (1 : WithTop ℕ∞) f (0, 0)) :
    IsContDiffImplicitAt (1 : WithTop ℕ∞) f
      (Fd.comp (ContinuousLinearMap.fst ℝ D X) +
        Fx.toContinuousLinearMap.comp (ContinuousLinearMap.snd ℝ D X)) (0, 0) where
  hasFDerivAt := hderiv
  contDiffAt := hcont
  bijective := by
    have heq :
        (Fd.comp (ContinuousLinearMap.fst ℝ D X) +
          Fx.toContinuousLinearMap.comp (ContinuousLinearMap.snd ℝ D X)).comp
            (ContinuousLinearMap.inr ℝ D X) = Fx.toContinuousLinearMap := by
      ext x
      simp [ContinuousLinearMap.comp_apply]
    rw [heq]
    exact Fx.bijective
  ne_zero := one_ne_zero

/-- Differentiating the local identity `f(d, phi d) = f(0,0)` yields the
source's first-order formula `D phi(0) = -Fx⁻¹ Fd`. -/
theorem higham25_implicitFunction_hasFDerivAt
    {D X Y : Type*}
    [NormedAddCommGroup D] [NormedSpace ℝ D] [CompleteSpace D]
    [NormedAddCommGroup X] [NormedSpace ℝ X] [CompleteSpace X]
    [NormedAddCommGroup Y] [NormedSpace ℝ Y] [CompleteSpace Y]
    {n : WithTop ℕ∞} (f : D × X → Y) (f' : D × X →L[ℝ] Y)
    (h : IsContDiffImplicitAt n f f' ((0 : D), (0 : X)))
    (Fd : D →L[ℝ] Y) (Fx : X ≃L[ℝ] Y)
    (hf' : f' = Fd.comp (ContinuousLinearMap.fst ℝ D X) +
      Fx.toContinuousLinearMap.comp (ContinuousLinearMap.snd ℝ D X)) :
    HasFDerivAt h.implicitFunction
      (-(Fx.symm.toContinuousLinearMap.comp Fd)) 0 := by
  let phi : D → X := h.implicitFunction
  let A : D →L[ℝ] X := fderiv ℝ phi 0
  have hphi0 : phi 0 = 0 := by
    have hbase := h.eventually_implicitFunction_apply_eq.self_of_nhds
    exact hbase rfl
  have hphiDiff : DifferentiableAt ℝ phi 0 :=
    h.contDiffAt_implicitFunction.differentiableAt h.ne_zero
  have hphiDeriv : HasFDerivAt phi A 0 := hphiDiff.hasFDerivAt
  have hpair : HasFDerivAt (fun d : D => (d, phi d))
      ((ContinuousLinearMap.id ℝ D).prod A) 0 := by
    simpa only [id_eq] using
      (hasFDerivAt_id (𝕜 := ℝ) (0 : D)).prodMk hphiDeriv
  have hfAt : HasFDerivAt f f' (0, phi 0) := by
    simpa only [hphi0] using h.hasFDerivAt
  have hcomp : HasFDerivAt (fun d : D => f (d, phi d))
      (f'.comp ((ContinuousLinearMap.id ℝ D).prod A)) 0 := by
    simpa only [Function.comp_apply] using hfAt.comp 0 hpair
  have hevent : (fun d : D => f (d, phi d)) =ᶠ[nhds (0 : D)]
      (fun _ : D => f (0, 0)) := h.apply_implicitFunction
  have hzero : f'.comp ((ContinuousLinearMap.id ℝ D).prod A) = 0 := by
    calc
      f'.comp ((ContinuousLinearMap.id ℝ D).prod A) =
          fderiv ℝ (fun d : D => f (d, phi d)) 0 := hcomp.fderiv.symm
      _ = fderiv ℝ (fun _ : D => f (0, 0)) 0 := hevent.fderiv_eq
      _ = 0 := (hasFDerivAt_const (x := (0 : D)) (f (0, 0))).fderiv
  have hA : A = -(Fx.symm.toContinuousLinearMap.comp Fd) := by
    ext d
    have hz := DFunLike.congr_fun hzero d
    have hsum : Fd d + Fx (A d) = 0 := by
      simpa [hf', ContinuousLinearMap.comp_apply] using hz
    have hx : Fx (A d) = -Fd d :=
      eq_neg_of_add_eq_zero_right hsum
    apply Fx.injective
    simpa [ContinuousLinearMap.comp_apply] using hx
  simpa [phi, A, hA] using hphiDeriv

/-- Mathlib's implicit-function theorem produces Higham's local solution
map, including local existence and local uniqueness rather than a
target-bearing global solution-map assumption. -/
theorem higham25_implicitFunction_local_solution_contract
    {D X Y : Type*}
    [NormedAddCommGroup D] [NormedSpace ℝ D] [CompleteSpace D]
    [NormedAddCommGroup X] [NormedSpace ℝ X] [CompleteSpace X]
    [NormedAddCommGroup Y] [NormedSpace ℝ Y] [CompleteSpace Y]
    {n : WithTop ℕ∞} (f : D × X → Y) (f' : D × X →L[ℝ] Y)
    (h : IsContDiffImplicitAt n f f' ((0 : D), (0 : X))) :
    ∃ dataDomain : Set D, ∃ solutionDomain : Set X,
      Higham25LocalSolutionMapContract
        (fun dx dd ↦ f (dd, dx) = f (0, 0)) dataDomain solutionDomain
        h.implicitFunction := by
  let phi : D → X := h.implicitFunction
  let solveSet : Set D := {dd | f (dd, phi dd) = f (0, 0)}
  let uniqueSet : Set (D × X) :=
    {p | f p = f (0, 0) → phi p.1 = p.2}
  have hsolve : solveSet ∈ nhds (0 : D) := by
    simpa [solveSet, phi] using h.apply_implicitFunction
  have hunique : uniqueSet ∈ nhds ((0 : D), (0 : X)) := by
    simpa [uniqueSet, phi] using h.eventually_implicitFunction_apply_eq
  rcases mem_nhds_prod_iff.mp hunique with ⟨U, hU, V, hV, hUV⟩
  have hphi0 : phi 0 = 0 := by
    have hbase := h.eventually_implicitFunction_apply_eq.self_of_nhds
    exact hbase rfl
  have hpre : phi ⁻¹' V ∈ nhds (0 : D) := by
    have hVphi : V ∈ nhds (phi 0) := by
      rw [hphi0]
      exact hV
    exact h.contDiffAt_implicitFunction.continuousAt.preimage_mem_nhds hVphi
  let dataDomain : Set D := U ∩ solveSet ∩ phi ⁻¹' V
  refine ⟨dataDomain, V, ?_⟩
  refine
    { data_mem_nhds := inter_mem (inter_mem hU hsolve) hpre
      solution_mem_nhds := hV
      map_zero := hphi0
      mapsTo := ?_
      solves := ?_
      unique := ?_ }
  · intro dd hdd
    exact hdd.2
  · intro dd hdd
    exact hdd.1.2
  · intro dx hdx dd hdd hfdx
    exact (hUV ⟨hdd.1.1, hdx⟩ hfdx).symm

/-- A uniform Taylor-remainder contract on the shrinking data balls.  This is
the precise explicit replacement for the source's phrase "sufficiently
small": the unnormalized remainder is at most `epsilon * remainder epsilon`,
and its coefficient tends to zero. -/
structure Higham25TaylorRemainderContract
    {D X : Type*} [NormedAddCommGroup D] [NormedSpace ℝ D]
    [NormedAddCommGroup X] [NormedSpace ℝ X]
    (phi : D → X) (L : D →L[ℝ] X) (dataNorm : ℝ) where
  radius : ℝ
  radius_pos : 0 < radius
  remainder : ℝ → ℝ
  remainder_nonneg : ∀ epsilon, 0 < epsilon → epsilon < radius →
    0 ≤ remainder epsilon
  remainder_tendsto : Tendsto remainder (nhdsWithin 0 (Set.Ioi 0)) (nhds 0)
  bound : ∀ epsilon, 0 < epsilon → epsilon < radius →
    ∀ dd ∈ Metric.closedBall (0 : D) (epsilon * dataNorm),
      ‖phi dd - L dd‖ ≤ epsilon * remainder epsilon

/-- Fréchet differentiability at the base point supplies the source's local
first-order Taylor estimate.  Unlike `Higham25TaylorRemainderContract`, this
statement does not assume a pre-packaged shrinking-ball remainder: it follows
directly from `HasFDerivAt`. -/
theorem higham25_taylor_linear_bound_of_hasFDerivAt
    {D X : Type*} [NormedAddCommGroup D] [NormedSpace ℝ D]
    [NormedAddCommGroup X] [NormedSpace ℝ X]
    (phi : D → X) (L : D →L[ℝ] X) (hphi0 : phi 0 = 0)
    (hderiv : HasFDerivAt phi L 0) :
    ∀ c : ℝ, 0 < c →
      ∀ᶠ dd in 𝓝 (0 : D), ‖phi dd - L dd‖ ≤ c * ‖dd‖ := by
  intro c hc
  have hbound := hderiv.isLittleO.bound hc
  filter_upwards [hbound] with dd hdd
  simpa [hphi0] using hdd

/-- Supremums of two nonempty bounded real images differ by at most a uniform
pointwise error. -/
theorem higham25_abs_sSup_image_sub_sSup_image_le
    {A : Type*} (S : Set A) (f g : A → ℝ) (q : ℝ)
    (hS : S.Nonempty) (hf : BddAbove (f '' S)) (hg : BddAbove (g '' S))
    (hclose : ∀ a ∈ S, |f a - g a| ≤ q) :
    |sSup (f '' S) - sSup (g '' S)| ≤ q := by
  have hfg : sSup (f '' S) ≤ sSup (g '' S) + q := by
    apply csSup_le (hS.image f)
    rintro _ ⟨a, ha, rfl⟩
    have hpoint0 := (abs_le.mp (hclose a ha)).2
    have hsup := le_csSup hg ⟨a, ha, rfl⟩
    linarith
  have hgf : sSup (g '' S) ≤ sSup (f '' S) + q := by
    apply csSup_le (hS.image g)
    rintro _ ⟨a, ha, rfl⟩
    have hpoint : g a ≤ f a + q := by
      have := (abs_le.mp (hclose a ha)).1
      linarith
    have hsup := le_csSup hf ⟨a, ha, rfl⟩
    linarith
  rw [abs_le]
  constructor <;> linarith

/-- The explicit solution-map contract gives a concrete feasible witness for
every positive epsilon: zero data perturbation and zero solution perturbation.
This rules out a vacuous supremum domain. -/
theorem higham25_actualConditionValues_nonempty
    {D X : Type*} [NormedAddCommGroup D] [NormedAddCommGroup X]
    (isSolution : X → D → Prop) (solutionDomain : Set X) (phi : D → X)
    (contract : Higham25ActualSolutionMapContract isSolution solutionDomain phi)
    (dataNorm solutionNorm epsilon : ℝ) (hdata : 0 ≤ dataNorm)
    (hepsilon : 0 < epsilon) :
    (higham25ActualConditionValues isSolution solutionDomain
      dataNorm solutionNorm epsilon).Nonempty := by
  refine ⟨(0 : ℝ), (0 : X), contract.zero_mem, (0 : D), ?_,
    contract.zero_solves, ?_⟩
  · rw [mem_closedBall_zero_iff]
    simpa using mul_nonneg hepsilon.le hdata
  · simp

/-- Under the actual-solution-map contract, the literal feasible value set is
exactly the value set generated by the solution map. -/
theorem higham25_actualConditionValues_eq_solutionMap_image
    {D X : Type*} [NormedAddCommGroup D] [NormedAddCommGroup X]
    (isSolution : X → D → Prop) (solutionDomain : Set X) (phi : D → X)
    (contract : Higham25ActualSolutionMapContract isSolution solutionDomain phi)
    (dataNorm solutionNorm epsilon : ℝ) :
    higham25ActualConditionValues isSolution solutionDomain
        dataNorm solutionNorm epsilon =
      (fun dd => ‖phi dd‖ / (epsilon * solutionNorm)) ''
        Metric.closedBall (0 : D) (epsilon * dataNorm) := by
  ext q
  constructor
  · rintro ⟨dx, hdx, dd, hdd, hsolve, rfl⟩
    refine ⟨dd, hdd, ?_⟩
    rw [contract.unique dx hdx dd hsolve]
  · rintro ⟨dd, hdd, rfl⟩
    exact ⟨phi dd, contract.mapsTo dd, dd, hdd, contract.solves dd, rfl⟩

/-- On every shrinking data ball contained in the local IFT domain, Higham's
literal nonlinear feasible set agrees with the graph of the local solution
map.  This is the bridge from local existence/uniqueness to the supremum in
(25.11). -/
theorem higham25_actualConditionValues_eq_localSolutionGraph
    {D X : Type*} [NormedAddCommGroup D] [NormedAddCommGroup X]
    (isSolution : X → D → Prop) (dataDomain : Set D)
    (solutionDomain : Set X) (phi : D → X)
    (contract : Higham25LocalSolutionMapContract
      isSolution dataDomain solutionDomain phi)
    (dataNorm solutionNorm epsilon : ℝ)
    (hball : Metric.closedBall (0 : D) (epsilon * dataNorm) ⊆ dataDomain) :
    higham25ActualConditionValues isSolution solutionDomain
        dataNorm solutionNorm epsilon =
      higham25ActualConditionValues (fun dx dd ↦ dx = phi dd) Set.univ
        dataNorm solutionNorm epsilon := by
  ext q
  constructor
  · rintro ⟨dx, hdx, dd, hdd, hsolve, rfl⟩
    exact ⟨dx, Set.mem_univ dx, dd, hdd,
      contract.unique dx hdx dd (hball hdd) hsolve, rfl⟩
  · rintro ⟨dx, -, dd, hdd, hgraph, rfl⟩
    subst dx
    exact ⟨phi dd, contract.mapsTo dd (hball hdd), dd, hdd,
      contract.solves dd (hball hdd), rfl⟩

/-- A neighborhood of zero eventually contains every data perturbation ball
used by the epsilon-limit in (25.11). -/
theorem higham25_eventually_closedBall_subset_of_mem_nhds
    {D : Type*} [NormedAddCommGroup D] [NormedSpace ℝ D]
    (dataDomain : Set D) (dataNorm : ℝ)
    (hdomain : dataDomain ∈ nhds (0 : D)) (hdata : 0 ≤ dataNorm) :
    ∀ᶠ epsilon in nhdsWithin 0 (Set.Ioi 0),
      Metric.closedBall (0 : D) (epsilon * dataNorm) ⊆ dataDomain := by
  rcases hdata.eq_or_lt with hzero | hpos
  · have hdataZero : dataNorm = 0 := hzero.symm
    have hmem : (0 : D) ∈ dataDomain := mem_of_mem_nhds hdomain
    filter_upwards with epsilon
    intro dd hdd
    have hddZero : dd = 0 := by
      simpa [hdataZero] using hdd
    simpa [hddZero] using hmem
  · rcases Metric.eventually_nhds_iff_ball.mp hdomain with ⟨r, hr, hball⟩
    have hepsilonRadius : 0 < r / dataNorm := div_pos hr hpos
    have hev : ∀ᶠ epsilon in nhdsWithin 0 (Set.Ioi 0),
        epsilon < r / dataNorm :=
      mem_nhdsWithin_of_mem_nhds (Iio_mem_nhds hepsilonRadius)
    filter_upwards [hev] with epsilon hepsilon
    intro dd hdd
    apply hball dd
    apply Metric.closedBall_subset_ball
        (show epsilon * dataNorm < r by
          calc
            epsilon * dataNorm < (r / dataNorm) * dataNorm :=
              mul_lt_mul_of_pos_right hepsilon hpos
            _ = r := by field_simp [ne_of_gt hpos])
    exact hdd

/-- A local first-order remainder bound controls the difference between the
actual nonlinear supremum and its linearized counterpart.  This is the
quantitative bridge needed to use `HasFDerivAt` directly in (25.11). -/
theorem higham25_actualEpsilonCondition_sub_linearized_abs_le_of_linear_bound
    {D X : Type*} [NormedAddCommGroup D] [NormedSpace ℝ D]
    [NormedAddCommGroup X] [NormedSpace ℝ X]
    (isSolution : X → D → Prop) (solutionDomain : Set X) (phi : D → X)
    (L : D →L[ℝ] X) (dataNorm solutionNorm epsilon c : ℝ)
    (hdata : 0 ≤ dataNorm) (hsolution : 0 < solutionNorm)
    (hepsilon : 0 < epsilon) (hc : 0 ≤ c)
    (contract : Higham25ActualSolutionMapContract isSolution solutionDomain phi)
    (hbound : ∀ dd ∈ Metric.closedBall (0 : D) (epsilon * dataNorm),
      ‖phi dd - L dd‖ ≤ c * ‖dd‖) :
    |higham25ActualEpsilonCondition isSolution solutionDomain
        dataNorm solutionNorm epsilon -
      higham25LinearizedEpsilonCondition L dataNorm solutionNorm epsilon| ≤
        c * dataNorm / solutionNorm := by
  let S : Set D := Metric.closedBall 0 (epsilon * dataNorm)
  let f : D → ℝ := fun dd => ‖phi dd‖ / (epsilon * solutionNorm)
  let g : D → ℝ := fun dd => ‖L dd‖ / (epsilon * solutionNorm)
  let q : ℝ := c * dataNorm / solutionNorm
  have hS : S.Nonempty := by
    refine ⟨0, ?_⟩
    rw [mem_closedBall_zero_iff]
    simpa [S] using mul_nonneg hepsilon.le hdata
  have hgpoint : ∀ dd ∈ S,
      g dd ≤ ‖L‖ * dataNorm / solutionNorm := by
    intro dd hdd
    have hdnorm : ‖dd‖ ≤ epsilon * dataNorm := by
      simpa [S] using mem_closedBall_zero_iff.mp hdd
    have hL := L.le_opNorm dd
    have hden : 0 < epsilon * solutionNorm := mul_pos hepsilon hsolution
    apply (div_le_iff₀ hden).2
    calc
      ‖L dd‖ ≤ ‖L‖ * ‖dd‖ := hL
      _ ≤ ‖L‖ * (epsilon * dataNorm) :=
        mul_le_mul_of_nonneg_left hdnorm (norm_nonneg L)
      _ = (‖L‖ * dataNorm / solutionNorm) *
          (epsilon * solutionNorm) := by
        field_simp [ne_of_gt hsolution]
  have hg : BddAbove (g '' S) := by
    refine ⟨‖L‖ * dataNorm / solutionNorm, ?_⟩
    rintro _ ⟨dd, hdd, rfl⟩
    exact hgpoint dd hdd
  have hq : 0 ≤ q :=
    div_nonneg (mul_nonneg hc hdata) hsolution.le
  have hclose : ∀ dd ∈ S, |f dd - g dd| ≤ q := by
    intro dd hdd
    have hden : 0 < epsilon * solutionNorm := mul_pos hepsilon hsolution
    have hdnorm : ‖dd‖ ≤ epsilon * dataNorm := by
      simpa [S] using mem_closedBall_zero_iff.mp hdd
    have hnormdiff : |‖phi dd‖ - ‖L dd‖| ≤ ‖phi dd - L dd‖ :=
      abs_norm_sub_norm_le _ _
    have hrem := hbound dd (by simpa [S] using hdd)
    have hrem' : ‖phi dd - L dd‖ ≤ c * (epsilon * dataNorm) :=
      hrem.trans (mul_le_mul_of_nonneg_left hdnorm hc)
    dsimp [f, g, q]
    rw [← sub_div, abs_div, abs_of_pos hden]
    apply (div_le_iff₀ hden).2
    calc
      |‖phi dd‖ - ‖L dd‖| ≤ ‖phi dd - L dd‖ := hnormdiff
      _ ≤ c * (epsilon * dataNorm) := hrem'
      _ = (c * dataNorm / solutionNorm) *
          (epsilon * solutionNorm) := by
        field_simp [ne_of_gt hsolution]
  have hf : BddAbove (f '' S) := by
    refine ⟨‖L‖ * dataNorm / solutionNorm + q, ?_⟩
    rintro _ ⟨dd, hdd, rfl⟩
    have hfg0 := (abs_le.mp (hclose dd hdd)).2
    have hgdd := hgpoint dd hdd
    linarith
  unfold higham25ActualEpsilonCondition higham25LinearizedEpsilonCondition
  rw [higham25_actualConditionValues_eq_solutionMap_image
    isSolution solutionDomain phi contract dataNorm solutionNorm epsilon]
  exact higham25_abs_sSup_image_sub_sSup_image_le S f g q hS hf hg hclose

/-- Equation (25.11) from an actual unique solution map and an ordinary
Fréchet derivative at the base data.  In particular, the Taylor remainder is
derived from `HasFDerivAt`; it is not assumed through the older uniform
remainder contract.  Producing the local unique solution map from the source's
implicit-function hypotheses remains a separate obligation. -/
theorem higham25_eq25_11_of_actualSolutionMap_hasFDerivAt
    {D X : Type*} [NormedAddCommGroup D] [NormedSpace ℝ D]
    [NormedAddCommGroup X] [NormedSpace ℝ X]
    (isSolution : X → D → Prop) (solutionDomain : Set X) (phi : D → X)
    (L : D →L[ℝ] X) (dataNorm solutionNorm : ℝ)
    (hdata : 0 ≤ dataNorm) (hsolution : 0 < solutionNorm)
    (contract : Higham25ActualSolutionMapContract isSolution solutionDomain phi)
    (hderiv : HasFDerivAt phi L 0) :
    Tendsto (fun epsilon =>
      higham25ActualEpsilonCondition isSolution solutionDomain
        dataNorm solutionNorm epsilon)
      (nhdsWithin 0 (Set.Ioi 0))
      (nhds (‖L‖ * dataNorm / solutionNorm)) := by
  refine Metric.tendsto_nhds.mpr ?_
  intro eta heta
  rcases hdata.eq_or_lt with hdataZero | hdataPos
  · have hdataEq : dataNorm = 0 := hdataZero.symm
    filter_upwards [self_mem_nhdsWithin] with epsilon hepsilon
    have hbound : ∀ dd ∈ Metric.closedBall (0 : D) (epsilon * dataNorm),
        ‖phi dd - L dd‖ ≤ (0 : ℝ) * ‖dd‖ := by
      intro dd hdd
      have hdnorm : ‖dd‖ ≤ 0 := by
        simpa [hdataEq] using mem_closedBall_zero_iff.mp hdd
      have hddZero : dd = 0 := by
        apply norm_eq_zero.mp
        exact le_antisymm hdnorm (norm_nonneg dd)
      subst dd
      simp [contract.map_zero]
    have hclose :=
      higham25_actualEpsilonCondition_sub_linearized_abs_le_of_linear_bound
        isSolution solutionDomain phi L dataNorm solutionNorm epsilon 0
        hdata hsolution hepsilon le_rfl contract hbound
    have hlin := higham25_linearizedEpsilonCondition_eq
      L dataNorm solutionNorm epsilon hdata hsolution hepsilon
    rw [Real.dist_eq, ← hlin]
    have hzero : (0 : ℝ) * dataNorm / solutionNorm = 0 := by simp
    rw [hzero] at hclose
    exact lt_of_le_of_lt hclose heta
  · let c : ℝ := eta * solutionNorm / (2 * dataNorm)
    have hc : 0 < c := by
      exact div_pos (mul_pos heta hsolution) (mul_pos (by norm_num) hdataPos)
    have hev := higham25_taylor_linear_bound_of_hasFDerivAt
      phi L contract.map_zero hderiv c hc
    rcases Metric.eventually_nhds_iff_ball.mp hev with ⟨r, hr, hrbound⟩
    let epsilonRadius : ℝ := r / dataNorm
    have hepsilonRadius : 0 < epsilonRadius := div_pos hr hdataPos
    have hevRadius : ∀ᶠ epsilon in nhdsWithin 0 (Set.Ioi 0),
        epsilon < epsilonRadius := by
      exact mem_nhdsWithin_of_mem_nhds (Iio_mem_nhds hepsilonRadius)
    filter_upwards [self_mem_nhdsWithin, hevRadius] with epsilon hepsilon heradius
    have hball : ∀ dd ∈ Metric.closedBall (0 : D) (epsilon * dataNorm),
        ‖phi dd - L dd‖ ≤ c * ‖dd‖ := by
      intro dd hdd
      apply hrbound dd
      rw [mem_ball_zero_iff]
      have hdnorm : ‖dd‖ ≤ epsilon * dataNorm :=
        mem_closedBall_zero_iff.mp hdd
      have hepsilonData : epsilon * dataNorm < r := by
        calc
          epsilon * dataNorm < epsilonRadius * dataNorm :=
            mul_lt_mul_of_pos_right heradius hdataPos
          _ = r := by
            dsimp [epsilonRadius]
            field_simp [ne_of_gt hdataPos]
      exact hdnorm.trans_lt hepsilonData
    have hclose :=
      higham25_actualEpsilonCondition_sub_linearized_abs_le_of_linear_bound
        isSolution solutionDomain phi L dataNorm solutionNorm epsilon c
        hdata hsolution hepsilon hc.le contract hball
    have hlin := higham25_linearizedEpsilonCondition_eq
      L dataNorm solutionNorm epsilon hdata hsolution hepsilon
    rw [Real.dist_eq, ← hlin]
    have hhalf : c * dataNorm / solutionNorm = eta / 2 := by
      dsimp [c]
      field_simp [ne_of_gt hdataPos, ne_of_gt hsolution]
    rw [hhalf] at hclose
    linarith

/-- Local existence and uniqueness are sufficient for (25.11): the shrinking
balls eventually lie in the data neighborhood, where the literal feasible
set agrees with the graph of `phi`. -/
theorem higham25_eq25_11_of_localSolutionMap_hasFDerivAt
    {D X : Type*} [NormedAddCommGroup D] [NormedSpace ℝ D]
    [NormedAddCommGroup X] [NormedSpace ℝ X]
    (isSolution : X → D → Prop) (dataDomain : Set D)
    (solutionDomain : Set X) (phi : D → X)
    (L : D →L[ℝ] X) (dataNorm solutionNorm : ℝ)
    (hdata : 0 ≤ dataNorm) (hsolution : 0 < solutionNorm)
    (contract : Higham25LocalSolutionMapContract
      isSolution dataDomain solutionDomain phi)
    (hderiv : HasFDerivAt phi L 0) :
    Tendsto (fun epsilon =>
      higham25ActualEpsilonCondition isSolution solutionDomain
        dataNorm solutionNorm epsilon)
      (nhdsWithin 0 (Set.Ioi 0))
      (nhds (‖L‖ * dataNorm / solutionNorm)) := by
  have graphContract : Higham25ActualSolutionMapContract
      (fun dx dd ↦ dx = phi dd) Set.univ phi :=
    { map_zero := contract.map_zero
      zero_mem := Set.mem_univ 0
      zero_solves := contract.map_zero.symm
      mapsTo := fun dd ↦ Set.mem_univ (phi dd)
      solves := fun _ ↦ rfl
      unique := fun _ _ _ hgraph ↦ hgraph }
  have hgraphLimit := higham25_eq25_11_of_actualSolutionMap_hasFDerivAt
    (fun dx dd ↦ dx = phi dd) Set.univ phi L dataNorm solutionNorm
    hdata hsolution graphContract hderiv
  have hballs := higham25_eventually_closedBall_subset_of_mem_nhds
    dataDomain dataNorm contract.data_mem_nhds hdata
  have heq :
      (fun epsilon => higham25ActualEpsilonCondition
        (fun dx dd ↦ dx = phi dd) Set.univ dataNorm solutionNorm epsilon) =ᶠ[
        nhdsWithin 0 (Set.Ioi 0)]
      (fun epsilon => higham25ActualEpsilonCondition isSolution solutionDomain
        dataNorm solutionNorm epsilon) := by
    filter_upwards [hballs] with epsilon hball
    unfold higham25ActualEpsilonCondition
    exact congrArg sSup
      (higham25_actualConditionValues_eq_localSolutionGraph
        isSolution dataDomain solutionDomain phi contract
        dataNorm solutionNorm epsilon hball).symm
  exact hgraphLimit.congr' heq

/-- Equation (25.11) directly from Higham's printed implicit-function
hypotheses.  The theorem produces the local nonlinear solution map, proves
its derivative is `-Fx⁻¹ Fd`, and evaluates the literal epsilon-indexed
condition-number supremum. -/
theorem higham25_eq25_11_of_implicitFunction
    {D X Y : Type*}
    [NormedAddCommGroup D] [NormedSpace ℝ D] [CompleteSpace D]
    [NormedAddCommGroup X] [NormedSpace ℝ X] [CompleteSpace X]
    [NormedAddCommGroup Y] [NormedSpace ℝ Y] [CompleteSpace Y]
    (f : D × X → Y) (Fd : D →L[ℝ] Y) (Fx : X ≃L[ℝ] Y)
    (dataNorm solutionNorm : ℝ)
    (hbase : f (0, 0) = 0)
    (hderiv : HasFDerivAt f
      (Fd.comp (ContinuousLinearMap.fst ℝ D X) +
        Fx.toContinuousLinearMap.comp (ContinuousLinearMap.snd ℝ D X)) (0, 0))
    (hcont : ContDiffAt ℝ (1 : WithTop ℕ∞) f (0, 0))
    (hdata : 0 ≤ dataNorm) (hsolution : 0 < solutionNorm) :
    ∃ phi : D → X, ∃ dataDomain : Set D, ∃ solutionDomain : Set X,
      Higham25LocalSolutionMapContract
          (fun dx dd ↦ f (dd, dx) = 0) dataDomain solutionDomain phi ∧
        HasFDerivAt phi (-(Fx.symm.toContinuousLinearMap.comp Fd)) 0 ∧
        Tendsto (fun epsilon =>
          higham25ActualEpsilonCondition (fun dx dd ↦ f (dd, dx) = 0)
            solutionDomain dataNorm solutionNorm epsilon)
          (nhdsWithin 0 (Set.Ioi 0))
          (nhds (‖Fx.symm.toContinuousLinearMap.comp Fd‖ *
            dataNorm / solutionNorm)) := by
  let f' : D × X →L[ℝ] Y :=
    Fd.comp (ContinuousLinearMap.fst ℝ D X) +
      Fx.toContinuousLinearMap.comp (ContinuousLinearMap.snd ℝ D X)
  have himplicit : IsContDiffImplicitAt (1 : WithTop ℕ∞) f f' (0, 0) := by
    exact higham25_isContDiffImplicitAt_of_partialEquiv f Fd Fx hderiv hcont
  rcases higham25_implicitFunction_local_solution_contract f f' himplicit with
    ⟨dataDomain, solutionDomain, hlocal⟩
  have hlocalZero : Higham25LocalSolutionMapContract
      (fun dx dd ↦ f (dd, dx) = 0) dataDomain solutionDomain
        himplicit.implicitFunction := by
    simpa only [hbase] using hlocal
  have hphi : HasFDerivAt himplicit.implicitFunction
      (-(Fx.symm.toContinuousLinearMap.comp Fd)) 0 := by
    apply higham25_implicitFunction_hasFDerivAt f f' himplicit Fd Fx
    rfl
  refine ⟨himplicit.implicitFunction, dataDomain, solutionDomain,
    hlocalZero, hphi, ?_⟩
  have hlimit := higham25_eq25_11_of_localSolutionMap_hasFDerivAt
    (fun dx dd ↦ f (dd, dx) = 0) dataDomain solutionDomain
    himplicit.implicitFunction (-(Fx.symm.toContinuousLinearMap.comp Fd))
    dataNorm solutionNorm hdata hsolution hlocalZero hphi
  simpa only [norm_neg] using hlimit

/-- The nonlinear solution-map supremum differs from its derivative-model
supremum by a vanishing normalized Taylor remainder. -/
theorem higham25_actualEpsilonCondition_sub_linearized_abs_le
    {D X : Type*} [NormedAddCommGroup D] [NormedSpace ℝ D]
    [NormedAddCommGroup X] [NormedSpace ℝ X]
    (isSolution : X → D → Prop) (solutionDomain : Set X) (phi : D → X)
    (L : D →L[ℝ] X) (dataNorm solutionNorm epsilon : ℝ)
    (hdata : 0 ≤ dataNorm) (hsolution : 0 < solutionNorm)
    (hepsilon : 0 < epsilon)
    (contract : Higham25ActualSolutionMapContract isSolution solutionDomain phi)
    (taylor : Higham25TaylorRemainderContract phi L dataNorm)
    (hradius : epsilon < taylor.radius) :
    |higham25ActualEpsilonCondition isSolution solutionDomain
        dataNorm solutionNorm epsilon -
      higham25LinearizedEpsilonCondition L dataNorm solutionNorm epsilon| ≤
        taylor.remainder epsilon / solutionNorm := by
  let S : Set D := Metric.closedBall 0 (epsilon * dataNorm)
  let f : D → ℝ := fun dd => ‖phi dd‖ / (epsilon * solutionNorm)
  let g : D → ℝ := fun dd => ‖L dd‖ / (epsilon * solutionNorm)
  let q : ℝ := taylor.remainder epsilon / solutionNorm
  have hS : S.Nonempty := by
    refine ⟨0, ?_⟩
    rw [mem_closedBall_zero_iff]
    simpa [S] using mul_nonneg hepsilon.le hdata
  have hgpoint : ∀ dd ∈ S,
      g dd ≤ ‖L‖ * dataNorm / solutionNorm := by
    intro dd hdd
    have hdnorm : ‖dd‖ ≤ epsilon * dataNorm := by
      simpa [S] using mem_closedBall_zero_iff.mp hdd
    have hL := L.le_opNorm dd
    have hden : 0 < epsilon * solutionNorm := mul_pos hepsilon hsolution
    apply (div_le_iff₀ hden).2
    calc
      ‖L dd‖ ≤ ‖L‖ * ‖dd‖ := hL
      _ ≤ ‖L‖ * (epsilon * dataNorm) :=
        mul_le_mul_of_nonneg_left hdnorm (norm_nonneg L)
      _ = (‖L‖ * dataNorm / solutionNorm) *
          (epsilon * solutionNorm) := by
        field_simp [ne_of_gt hsolution]
  have hg : BddAbove (g '' S) := by
    refine ⟨‖L‖ * dataNorm / solutionNorm, ?_⟩
    rintro _ ⟨dd, hdd, rfl⟩
    exact hgpoint dd hdd
  have hq : 0 ≤ q := div_nonneg
    (taylor.remainder_nonneg epsilon hepsilon hradius) hsolution.le
  have hclose : ∀ dd ∈ S, |f dd - g dd| ≤ q := by
    intro dd hdd
    have hden : 0 < epsilon * solutionNorm := mul_pos hepsilon hsolution
    have hnormdiff : |‖phi dd‖ - ‖L dd‖| ≤ ‖phi dd - L dd‖ :=
      abs_norm_sub_norm_le _ _
    have hrem := taylor.bound epsilon hepsilon hradius dd (by simpa [S] using hdd)
    dsimp [f, g, q]
    rw [← sub_div, abs_div, abs_of_pos hden]
    apply (div_le_iff₀ hden).2
    calc
      |‖phi dd‖ - ‖L dd‖| ≤ ‖phi dd - L dd‖ := hnormdiff
      _ ≤ epsilon * taylor.remainder epsilon := hrem
      _ = (taylor.remainder epsilon / solutionNorm) *
          (epsilon * solutionNorm) := by
        field_simp [ne_of_gt hsolution]
  have hf : BddAbove (f '' S) := by
    refine ⟨‖L‖ * dataNorm / solutionNorm + q, ?_⟩
    rintro _ ⟨dd, hdd, rfl⟩
    have hfg0 := (abs_le.mp (hclose dd hdd)).2
    have hgdd := hgpoint dd hdd
    linarith
  unfold higham25ActualEpsilonCondition higham25LinearizedEpsilonCondition
  rw [higham25_actualConditionValues_eq_solutionMap_image
    isSolution solutionDomain phi contract dataNorm solutionNorm epsilon]
  exact higham25_abs_sSup_image_sub_sSup_image_le S f g q hS hf hg hclose

/-- Equation (25.11), at the strongest honest explicit domain: the literal
actual feasible supremum for a unique nonlinear solution map tends to the
printed inverse-derivative operator-norm expression. -/
theorem higham25_eq25_11_of_actualSolutionMap
    {D X : Type*} [NormedAddCommGroup D] [NormedSpace ℝ D]
    [NormedAddCommGroup X] [NormedSpace ℝ X]
    (isSolution : X → D → Prop) (solutionDomain : Set X) (phi : D → X)
    (L : D →L[ℝ] X) (dataNorm solutionNorm : ℝ)
    (hdata : 0 ≤ dataNorm) (hsolution : 0 < solutionNorm)
    (contract : Higham25ActualSolutionMapContract isSolution solutionDomain phi)
    (taylor : Higham25TaylorRemainderContract phi L dataNorm) :
    Tendsto (fun epsilon =>
      higham25ActualEpsilonCondition isSolution solutionDomain
        dataNorm solutionNorm epsilon)
      (nhdsWithin 0 (Set.Ioi 0))
      (nhds (‖L‖ * dataNorm / solutionNorm)) := by
  have hlinear := higham25_linearizedEpsilonCondition_tendsto
    L dataNorm solutionNorm hdata hsolution
  have hremainder : Tendsto (fun epsilon =>
      taylor.remainder epsilon / solutionNorm)
      (nhdsWithin 0 (Set.Ioi 0)) (nhds 0) := by
    simpa using taylor.remainder_tendsto.div_const solutionNorm
  refine Metric.tendsto_nhds.mpr ?_
  intro epsilon hepsilon
  have hevRadius : ∀ᶠ e in nhdsWithin 0 (Set.Ioi 0), e < taylor.radius := by
    have : Set.Iio taylor.radius ∈ nhds (0 : ℝ) :=
      Iio_mem_nhds taylor.radius_pos
    exact mem_of_superset (mem_nhdsWithin_of_mem_nhds this) (by intro e he; exact he)
  have hevLin : ∀ᶠ e in nhdsWithin 0 (Set.Ioi 0),
      dist (higham25LinearizedEpsilonCondition L dataNorm solutionNorm e)
        (‖L‖ * dataNorm / solutionNorm) < epsilon / 2 :=
    (Metric.tendsto_nhds.mp hlinear (epsilon / 2) (half_pos hepsilon))
  have hevRem : ∀ᶠ e in nhdsWithin 0 (Set.Ioi 0),
      taylor.remainder e / solutionNorm < epsilon / 2 := by
    have h := Metric.tendsto_nhds.mp hremainder (epsilon / 2) (half_pos hepsilon)
    filter_upwards [h] with e he
    rw [Real.dist_eq, sub_zero] at he
    exact lt_of_le_of_lt (le_abs_self _) he
  filter_upwards [self_mem_nhdsWithin, hevRadius, hevLin, hevRem] with e hepos herad hlin hrem
  have hactual := higham25_actualEpsilonCondition_sub_linearized_abs_le
    isSolution solutionDomain phi L dataNorm solutionNorm e hdata hsolution
    hepos contract taylor herad
  rw [Real.dist_eq] at hlin ⊢
  calc
    |higham25ActualEpsilonCondition isSolution solutionDomain
        dataNorm solutionNorm e - ‖L‖ * dataNorm / solutionNorm| ≤
      |higham25ActualEpsilonCondition isSolution solutionDomain
          dataNorm solutionNorm e -
        higham25LinearizedEpsilonCondition L dataNorm solutionNorm e| +
      |higham25LinearizedEpsilonCondition L dataNorm solutionNorm e -
        ‖L‖ * dataNorm / solutionNorm| := by
          rw [show higham25ActualEpsilonCondition isSolution solutionDomain
              dataNorm solutionNorm e - ‖L‖ * dataNorm / solutionNorm =
            (higham25ActualEpsilonCondition isSolution solutionDomain
                dataNorm solutionNorm e -
              higham25LinearizedEpsilonCondition L dataNorm solutionNorm e) +
            (higham25LinearizedEpsilonCondition L dataNorm solutionNorm e -
              ‖L‖ * dataNorm / solutionNorm) by ring]
          exact abs_add_le _ _
    _ < epsilon := by linarith

end Conditioning

section WozniakowskiExample

/-- Equation (25.12). -/
def higham25Eq25_12 (mu x1 x2 : ℝ) : ℝ × ℝ :=
  (x1 - x2, x1 ^ 2 + mu * x2 ^ 2 - mu)

/-- The positive solution displayed after equation (25.12). -/
noncomputable def higham25Eq25_12Solution (mu : ℝ) : ℝ :=
  Real.sqrt (mu / (1 + mu))

theorem higham25_eq25_12_solution (mu : ℝ) (hmu : 0 < mu) :
    higham25Eq25_12 mu (higham25Eq25_12Solution mu)
        (higham25Eq25_12Solution mu) = (0, 0) := by
  have hden : 0 < 1 + mu := by linarith
  have hnonneg : 0 ≤ mu / (1 + mu) := div_nonneg (le_of_lt hmu) (le_of_lt hden)
  have hsquare : higham25Eq25_12Solution mu ^ 2 = mu / (1 + mu) := by
    simpa [higham25Eq25_12Solution] using Real.sq_sqrt hnonneg
  apply Prod.ext <;> simp [higham25Eq25_12, hsquare]
  field_simp [ne_of_gt hden]
  ring

/-- Parameterized exact function used to interpret the rounding model (25.13). -/
def higham25Eq25_13Parameterized (mu d x1 x2 : ℝ) : ℝ × ℝ :=
  (x1 - x2, d * (x1 ^ 2 + mu * x2 ^ 2) - mu)

/-- Equation (25.13) as an exact representability predicate. -/
def higham25Eq25_13Model
    (u gamma3 mu x1 x2 computed1 computed2 : ℝ) : Prop :=
  ∃ delta1 delta2 delta3,
    |delta1| ≤ u ∧ |delta2| ≤ u ∧ |delta3| ≤ gamma3 ∧
      computed1 = (1 + delta1) * (x1 - x2) ∧
      computed2 =
        (1 + delta2) * ((1 + delta3) * (x1 ^ 2 + mu * x2 ^ 2) - mu)

/-- The literal straightforward evaluation order used for the quadratic core
of (25.13): square both variables, scale the second square by `mu`, then add. -/
noncomputable def higham25Eq25_13RoundedQuadraticCore
    (fp : FPModel) (mu x1 x2 : ℝ) : ℝ :=
  fp.fl_add (fp.fl_mul x1 x1) (fp.fl_mul mu (fp.fl_mul x2 x2))

/-- The complete rounded evaluator whose two outputs are displayed in (25.13). -/
noncomputable def higham25Eq25_13RoundedEval
    (fp : FPModel) (mu x1 x2 : ℝ) : ℝ × ℝ :=
  (fp.fl_sub x1 x2,
    fp.fl_sub (higham25Eq25_13RoundedQuadraticCore fp mu x1 x2) mu)

/-- The four rounded operations in the nonnegative quadratic core yield the
single `gamma₃` factor printed in (25.13).  The first squared term traverses
two rounding factors and the second traverses three; positivity makes their
weighted average another `gamma₃` perturbation. -/
theorem higham25_eq25_13_roundedQuadraticCore_model
    (fp : FPModel) (h3 : gammaValid fp 3)
    (mu x1 x2 : ℝ) (hmu : 0 ≤ mu) :
    ∃ delta3, |delta3| ≤ gamma fp 3 ∧
      higham25Eq25_13RoundedQuadraticCore fp mu x1 x2 =
        (1 + delta3) * (x1 ^ 2 + mu * x2 ^ 2) := by
  obtain ⟨da, hda, ha⟩ := fp.model_mul x1 x1
  obtain ⟨db, hdb, hb⟩ := fp.model_mul x2 x2
  obtain ⟨dc, hdc, hc⟩ := fp.model_mul mu (fp.fl_mul x2 x2)
  obtain ⟨dd, hdd, hd⟩ :=
    fp.model_add (fp.fl_mul x1 x1) (fp.fl_mul mu (fp.fl_mul x2 x2))
  have h1 : gammaValid fp 1 := gammaValid_mono fp (by omega) h3
  have h2 : gammaValid fp 2 := gammaValid_mono fp (by omega) h3
  have hda1 : |da| ≤ gamma fp 1 := le_trans hda (u_le_gamma fp one_pos h1)
  have hdb1 : |db| ≤ gamma fp 1 := le_trans hdb (u_le_gamma fp one_pos h1)
  have hdc1 : |dc| ≤ gamma fp 1 := le_trans hdc (u_le_gamma fp one_pos h1)
  have hdd1 : |dd| ≤ gamma fp 1 := le_trans hdd (u_le_gamma fp one_pos h1)
  obtain ⟨ta, hta, htaeq⟩ :=
    gamma_mul fp 1 1 da dd hda1 hdd1 (by simpa using h2)
  obtain ⟨tb2, htb2, htb2eq⟩ :=
    gamma_mul fp 1 1 db dc hdb1 hdc1 (by simpa using h2)
  obtain ⟨tb, htb, htbeq⟩ :=
    gamma_mul fp 2 1 tb2 dd htb2 hdd1 (by simpa using h3)
  let a := x1 ^ 2
  let b := mu * x2 ^ 2
  have ha0 : 0 ≤ a := sq_nonneg x1
  have hb0 : 0 ≤ b := mul_nonneg hmu (sq_nonneg x2)
  have hta3 : |ta| ≤ gamma fp 3 :=
    le_trans hta (gamma_mono fp (by omega) h3)
  have hcore : higham25Eq25_13RoundedQuadraticCore fp mu x1 x2 =
      a * (1 + ta) + b * (1 + tb) := by
    unfold higham25Eq25_13RoundedQuadraticCore
    rw [hd, ha, hc, hb]
    dsimp [a, b]
    rw [← htaeq, ← htbeq, ← htb2eq]
    ring
  by_cases hq : a + b = 0
  · refine ⟨0, ?_, ?_⟩
    · simpa using gamma_nonneg fp h3
    · have haz : a = 0 := by nlinarith
      have hbz : b = 0 := by nlinarith
      have hsum : x1 ^ 2 + mu * x2 ^ 2 = 0 := by simpa [a, b] using hq
      rw [hcore, haz, hbz, hsum]
      simp
  · let d := (a * ta + b * tb) / (a + b)
    refine ⟨d, ?_, ?_⟩
    · have hqpos : 0 < a + b :=
        lt_of_le_of_ne (add_nonneg ha0 hb0) (Ne.symm hq)
      have hnum : |a * ta + b * tb| ≤ (a + b) * gamma fp 3 := by
        calc
          |a * ta + b * tb| ≤ |a * ta| + |b * tb| := abs_add_le _ _
          _ = a * |ta| + b * |tb| := by
            rw [abs_mul, abs_mul, abs_of_nonneg ha0, abs_of_nonneg hb0]
          _ ≤ a * gamma fp 3 + b * gamma fp 3 :=
            add_le_add (mul_le_mul_of_nonneg_left hta3 ha0)
              (mul_le_mul_of_nonneg_left htb hb0)
          _ = (a + b) * gamma fp 3 := by ring
      dsimp [d]
      rw [abs_div, abs_of_pos hqpos]
      exact (div_le_iff₀ hqpos).2 (by simpa [mul_comm] using hnum)
    · rw [hcore]
      dsimp [d]
      field_simp [hq]
      ring

/-- Equation (25.13), end to end: the literal rounded evaluator produces the
three source error witnesses with radii `u`, `u`, and `gamma₃`. -/
theorem higham25_eq25_13_roundedEval_model
    (fp : FPModel) (h3 : gammaValid fp 3)
    (mu x1 x2 : ℝ) (hmu : 0 ≤ mu) :
    higham25Eq25_13Model fp.u (gamma fp 3) mu x1 x2
      (higham25Eq25_13RoundedEval fp mu x1 x2).1
      (higham25Eq25_13RoundedEval fp mu x1 x2).2 := by
  obtain ⟨d1, hd1, hfirst⟩ := fp.model_sub x1 x2
  obtain ⟨d2, hd2, hsecond⟩ :=
    fp.model_sub (higham25Eq25_13RoundedQuadraticCore fp mu x1 x2) mu
  obtain ⟨d3, hd3, hcore⟩ :=
    higham25_eq25_13_roundedQuadraticCore_model fp h3 mu x1 x2 hmu
  refine ⟨d1, d2, d3, hd1, hd2, hd3, ?_, ?_⟩
  · simpa [higham25Eq25_13RoundedEval, mul_comm] using hfirst
  · dsimp [higham25Eq25_13RoundedEval]
    rw [hsecond, hcore]
    ring

/-- The derivative calculation displayed after (25.13): at the positive
solution `v`, applying `F_x(v;1)` to `(v/2,v/2)` equals `F_d(v;1)`. -/
theorem higham25_eq25_13_sensitivity_direction (mu : ℝ) (_hmu : 0 < mu) :
    let v := higham25Eq25_12Solution mu
    (v / 2 - v / 2,
      2 * v * (v / 2) + 2 * mu * v * (v / 2)) =
      (0, v ^ 2 + mu * v ^ 2) := by
  dsimp
  apply Prod.ext
  · simp
  · simp
    ring

/-- Consequently the relative condition number of this one-parameter example
is `1/2` whenever the solution norm is nonzero, independently of `mu`. -/
theorem higham25_eq25_13_condition_half
    (solutionNorm : ℝ) (hsolution : solutionNorm ≠ 0) :
    higham25Eq25_11Condition (solutionNorm / 2) 1 solutionNorm = (1 : ℝ) / 2 := by
  simp [higham25Eq25_11Condition]
  field_simp [hsolution]

end WozniakowskiExample

section Stopping

/-- Exact scalar form of the "solving" step after equation (25.14). -/
theorem higham25_eq25_14_denominator_bound
    (c currentError nextError stepNorm : ℝ)
    (hnext : nextError ≤ c * currentError ^ 2)
    (htriangle : currentError ≤ stepNorm + nextError)
    (hden : 0 < 1 - c * currentError) :
    currentError ≤ stepNorm / (1 - c * currentError) := by
  apply (le_div_iff₀ hden).2
  nlinarith [hnext]

/-- Rigorous endpoint of the stopping argument following (25.14).  The
source's phrase "small enough" is exposed as the exact reciprocal-square
premise needed to replace the denominator by the factor `2`. -/
theorem higham25_eq25_14_step_squared_bound
    (c currentError nextError stepNorm : ℝ)
    (hc : 0 ≤ c) (hcurrent : 0 ≤ currentError) (hstep : 0 ≤ stepNorm)
    (hnext : nextError ≤ c * currentError ^ 2)
    (htriangle : currentError ≤ stepNorm + nextError)
    (hden : 0 < 1 - c * currentError)
    (hsmall : (1 : ℝ) / (1 - c * currentError) ^ 2 ≤ 2) :
    nextError ≤ 2 * c * stepNorm ^ 2 := by
  have hcur := higham25_eq25_14_denominator_bound c currentError nextError stepNorm
    hnext htriangle hden
  have hquot_nonneg : 0 ≤ stepNorm / (1 - c * currentError) :=
    div_nonneg hstep (le_of_lt hden)
  have hsquare : currentError ^ 2 ≤ (stepNorm / (1 - c * currentError)) ^ 2 :=
    (sq_le_sq₀ hcurrent hquot_nonneg).2 hcur
  calc
    nextError ≤ c * currentError ^ 2 := hnext
    _ ≤ c * (stepNorm / (1 - c * currentError)) ^ 2 :=
      mul_le_mul_of_nonneg_left hsquare hc
    _ = c * stepNorm ^ 2 * ((1 : ℝ) / (1 - c * currentError) ^ 2) := by
      field_simp [ne_of_gt hden]
    _ ≤ c * stepNorm ^ 2 * 2 := by
      apply mul_le_mul_of_nonneg_left hsmall
      positivity
    _ = 2 * c * stepNorm ^ 2 := by ring

end Stopping

end NumStability
