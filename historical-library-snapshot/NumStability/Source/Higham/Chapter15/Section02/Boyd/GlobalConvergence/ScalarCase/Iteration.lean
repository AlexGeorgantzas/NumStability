import Mathlib.Algebra.BigOperators.Group.Finset.Basic
import Mathlib.Algebra.BigOperators.Ring.Finset
import Mathlib.Algebra.Order.BigOperators.Group.Finset
import Mathlib.Analysis.Calculus.Deriv.Add
import Mathlib.Analysis.Calculus.FDeriv.Basic
import Mathlib.Analysis.Calculus.LocalExtr.Basic
import Mathlib.Analysis.Convex.SpecificFunctions.Basic
import Mathlib.Analysis.InnerProductSpace.NormPow
import Mathlib.Analysis.MeanInequalitiesPow
import Mathlib.Analysis.SpecialFunctions.Sqrt
import Mathlib.Data.Fintype.BigOperators
import Mathlib.Data.Real.Basic
import Mathlib.LinearAlgebra.Matrix.Irreducible.Defs
import Mathlib.Order.Fin.Basic
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Ring
import Mathlib.Topology.MetricSpace.Contracting
import Mathlib.Topology.MetricSpace.ProperSpace
import Mathlib.Topology.Order.Compact
import Mathlib.Topology.Order.MonotoneConvergence
import Mathlib.Topology.Sequences
import NumStability.Algorithms.CondEstimation
import NumStability.Algorithms.NormEstimation.OneNorm.PowerMethod.PNormPowerMethod
import NumStability.Algorithms.NormEstimation.PNorm.Boyd.Carrier.BoydInterface
import NumStability.Algorithms.NormEstimation.PNorm.Boyd.Differentiation.BoydInterface
import NumStability.Algorithms.NormEstimation.PNorm.Boyd.Differentiation.PNormGeneral
import NumStability.Algorithms.NormEstimation.PNorm.Boyd.FixedPoints.BoydInterface
import NumStability.Algorithms.NormEstimation.PNorm.Boyd.LocalStability.BoydInterface
import NumStability.Algorithms.NormEstimation.PNorm.Boyd.Uniqueness.Basic
import NumStability.Algorithms.NormEstimation.PNorm.Convergence.BoydInterface
import NumStability.Algorithms.NormEstimation.PNorm.Convergence.ConvergenceStatements
import NumStability.Algorithms.NormEstimation.PNorm.Duality.BoydInterface
import NumStability.Algorithms.NormEstimation.PNorm.Duality.BoydUniqueness
import NumStability.Algorithms.NormEstimation.PNorm.Duality.ConvergenceStatements
import NumStability.Algorithms.NormEstimation.PNorm.Duality.PNormGeneral
import NumStability.Algorithms.NormEstimation.PNorm.Duality.PNormPowerMethod
import NumStability.Algorithms.NormEstimation.PNorm.OneAndInfinityNorms.Rectangular
import NumStability.Algorithms.NormEstimation.PNorm.OneAndInfinityNorms.Square
import NumStability.Algorithms.NormEstimation.PNorm.PowerMethod.BoydInterface
import NumStability.Algorithms.NormEstimation.PNorm.PowerMethod.PNormGeneral
import NumStability.Algorithms.NormEstimation.PNorm.PowerMethod.PNormPowerMethod
import NumStability.Algorithms.NormEstimation.PNorm.Rectangular.BoydInterface
import NumStability.Algorithms.NormEstimation.PNorm.Rectangular.PNormGeneral
import NumStability.Algorithms.NormEstimation.PNorm.Rectangular.PNormRectangular
import NumStability.Analysis.MatrixAlgebra
import NumStability.Analysis.MatrixNorms.Lp
import NumStability.Analysis.SingularValues.Realification
import NumStability.Source.Higham.Chapter15.Algorithm01.PNormPowerMethod.ConvergenceStatements
import NumStability.Source.Higham.Chapter15.Algorithm01.PNormPowerMethod.PNormPowerMethod
import NumStability.Source.Higham.Chapter15.Algorithm01.PNormPowerMethod.PNormRectangular
import NumStability.Source.Higham.Chapter15.Equation02.Subgradient.PNormGeneral
import NumStability.Source.Higham.Chapter15.Equation02.Subgradient.PNormPowerMethod
import NumStability.Source.Higham.Chapter15.Equation03.GradientQuotient.ConvergenceStatements
import NumStability.Source.Higham.Chapter15.Equation03.GradientQuotient.PNormGeneral
import NumStability.Source.Higham.Chapter15.Equation03.GradientQuotient.PNormPowerMethod
import NumStability.Source.Higham.Chapter15.Equation04.NormalizedDualDiscrepancy.Basic
import NumStability.Source.Higham.Chapter15.Equation05.SubgradientInequality.Basic
import NumStability.Source.Higham.Chapter15.Lemma02.PNormPowerMethod.BoydInterface
import NumStability.Source.Higham.Chapter15.Lemma02.PNormPowerMethod.BoydUniqueness
import NumStability.Source.Higham.Chapter15.Lemma02.PNormPowerMethod.PNormPowerMethod
import NumStability.Source.Higham.Chapter15.Lemma02.PNormPowerMethod.PNormRectangular
import NumStability.Source.Higham.Chapter15.Section02.Boyd.Corrections.ConvergenceStatements
import NumStability.Source.Higham.Chapter15.Section02.Boyd.EndpointTermination.ConvergenceStatements
import NumStability.Source.Higham.Chapter15.Section02.Boyd.GlobalConvergence.BoydInterface
import NumStability.Source.Higham.Chapter15.Section02.Boyd.GlobalConvergence.BoydUniqueness
import NumStability.Source.Higham.Chapter15.Section02.Boyd.GlobalConvergence.ConvergenceStatements
import NumStability.Source.Higham.Chapter15.Section02.Boyd.LocalConvergence.BoydInterface

/-!
# Iteration

Canonical destination for the frozen declaration block of
`NumStability.Algorithms.HighamChapter15BoydScalar`, routed by wave R02 of the August 2026 repository reorganization
completion phase. Declaration names, kinds, visibilities, signatures and
proofs are unchanged; only the module they live in has changed. Private
declarations keep their logical names and are re-mangled against this module,
exactly as recorded in the reviewed private normalization.
-/

/-!
# HighamChapter15BoydScalar (compatibility module)

Historical path, retained so existing imports of `NumStability.Algorithms.HighamChapter15BoydScalar`
keep resolving. Most of its declarations moved unchanged to the
canonical modules imported above.

The declarations still defined below are private declarations and
their users. Lean mangles a private name to
`_private.<module>.<n>.<name>`, so relocating one renames it and
breaks the frozen declaration graph; anything referring to one must
therefore stay with it. This module is a declaration-bearing facade,
not a pure import shim.
-/

namespace NumStability

namespace Ch15

open scoped BigOperators Topology

open Filter

private noncomputable def scalarBasis : Fin 1 → ℝ := basisVec (0 : Fin 1)

/-- The nonnegative `p`-unit carrier is a singleton in source dimension one. -/
theorem boydScalar_carrier_eq_basis {p : ℝ} (hp : 1 ≤ p)
    {x : Fin 1 → ℝ} (hx : x ∈ boydNonnegativeUnitCarrier p) :
    x = scalarBasis := by
  have hxrepr : x = fun i => x 0 * scalarBasis i := by
    funext i
    have hi : i = (0 : Fin 1) := Subsingleton.elim _ _
    subst i
    simp [scalarBasis, basisVec]
  have hnorm := hx.2
  rw [hxrepr, realVecLpNorm_smul_real hp,
    show realVecLpNorm p scalarBasis = 1 by
      simpa [scalarBasis] using realVecLpNorm_basisVec hp (0 : Fin 1)] at hnorm
  have hx0 : x 0 = 1 := by
    rw [abs_of_nonneg (hx.1 0), mul_one] at hnorm
    exact hnorm
  rw [hxrepr, hx0]
  simp

/-- The positive scalar basis vector lies in the nonnegative unit carrier. -/
theorem boydScalar_basis_mem_carrier {p : ℝ} (hp : 1 ≤ p) :
    scalarBasis ∈ boydNonnegativeUnitCarrier p := by
  constructor
  · intro i
    have hi : i = (0 : Fin 1) := Subsingleton.elim _ _
    subst i
    simp [scalarBasis, basisVec]
  · exact realVecLpNorm_basisVec hp (0 : Fin 1)

/-- For a nonnegative rectangular matrix, the transpose-dual vector produced
at the positive scalar basis is nonnegative.  The zero-image branch is handled
explicitly, so no positivity property of an arbitrary normer of the zero
vector is assumed. -/
theorem boydScalar_zof_basis_nonneg {m : ℕ} {p q : ℝ}
    (hpq : p.HolderConjugate q) (A : Fin m → Fin 1 → ℝ)
    (hA : ∀ i j, 0 ≤ A i j) :
    ∀ j, 0 ≤ (RectPNormPair.general (by omega) hpq A).zof scalarBasis j := by
  let P := RectPNormPair.general (by omega : 0 < 1) hpq A
  have hy_nonneg : ∀ i, 0 ≤ P.yof scalarBasis i := by
    intro i
    unfold RectPNormPair.yof
    exact Finset.sum_nonneg fun j _ =>
      mul_nonneg (hA i j) (by
        have hj : j = (0 : Fin 1) := Subsingleton.elim _ _
        subst j
        simp [scalarBasis, basisVec])
  by_cases hy : P.yof scalarBasis = 0
  · have hAzero : ∀ i, A i (0 : Fin 1) = 0 := by
      intro i
      have hyi : P.yof scalarBasis i = 0 := by
        simpa using congrFun hy i
      have heval : P.yof scalarBasis i = A i 0 := by
        change (∑ j : Fin 1, A i j * scalarBasis j) = A i 0
        simp [scalarBasis, basisVec]
      rw [heval] at hyi
      exact hyi
    intro j
    have hj : j = (0 : Fin 1) := Subsingleton.elim _ _
    subst j
    change 0 ≤ ∑ i : Fin m,
      A i 0 * realLpDual hpq (P.yof scalarBasis) i
    simp [hAzero]
  · have hdual : ∀ i, 0 ≤ realLpDual hpq (P.yof scalarBasis) i :=
      realLpDual_nonneg_of_nonneg hpq (P.yof scalarBasis) hy hy_nonneg
    intro j
    change 0 ≤ ∑ i : Fin m,
      A i j * realLpDual hpq (P.yof scalarBasis) i
    exact Finset.sum_nonneg fun i _ => mul_nonneg (hA i j) (hdual i)

/-- One literal smooth Boyd update of the positive scalar basis remains
nonnegative, including the total-dual zero branch. -/
theorem boydScalar_xnext_basis_nonneg {m : ℕ} {p q : ℝ}
    (hpq : p.HolderConjugate q) (A : Fin m → Fin 1 → ℝ)
    (hA : ∀ i j, 0 ≤ A i j) :
    ∀ j, 0 ≤ (RectPNormPair.general (by omega) hpq A).xnext scalarBasis j := by
  let P := RectPNormPair.general (by omega : 0 < 1) hpq A
  have hznonneg : ∀ j, 0 ≤ P.zof scalarBasis j := by
    simpa [P] using boydScalar_zof_basis_nonneg hpq A hA
  by_cases hz : P.zof scalarBasis = 0
  · change ∀ j, 0 ≤ realLpDualUnit (by omega) hpq.symm
      (P.zof scalarBasis) j
    simp [realLpDualUnit, hz, basisVec]
  · have hdual : ∀ j,
        0 ≤ realLpDual hpq.symm (P.zof scalarBasis) j :=
      realLpDual_nonneg_of_nonneg hpq.symm (P.zof scalarBasis) hz hznonneg
    change ∀ j, 0 ≤ realLpDualUnit (by omega) hpq.symm
      (P.zof scalarBasis) j
    simpa [realLpDualUnit, hz] using hdual

/-- The scalar basis is a fixed point of the literal Algorithm 15.1 map for
every entrywise nonnegative rectangular matrix. -/
theorem boydScalar_xnext_basis_eq {m : ℕ} {p q : ℝ}
    (hpq : p.HolderConjugate q) (A : Fin m → Fin 1 → ℝ)
    (hA : ∀ i j, 0 ≤ A i j) :
    (RectPNormPair.general (by omega) hpq A).xnext scalarBasis = scalarBasis := by
  let P := RectPNormPair.general (by omega : 0 < 1) hpq A
  apply boydScalar_carrier_eq_basis (le_of_lt hpq.lt)
  constructor
  · simpa [P] using boydScalar_xnext_basis_nonneg hpq A hA
  · exact P.dqIn_punit (P.zof scalarBasis)

/-- Every iterate started at the scalar basis is the scalar basis. -/
theorem boydScalar_xseq_basis_eq {m : ℕ} {p q : ℝ}
    (hpq : p.HolderConjugate q) (A : Fin m → Fin 1 → ℝ)
    (hA : ∀ i j, 0 ≤ A i j) (k : ℕ) :
    (RectPNormPair.general (by omega) hpq A).xseq scalarBasis k = scalarBasis := by
  let P := RectPNormPair.general (by omega : 0 < 1) hpq A
  induction k with
  | zero => rfl
  | succ k ih =>
      rw [RectPNormPair.xseq, ih]
      exact boydScalar_xnext_basis_eq hpq A hA

/-- Scalar-domain closure of Higham p. 291 / Boyd's printed global theorem.
Unlike the nonlinear Perron proof, this theorem requires no impossible
`Nontrivial (Fin 1)` instance. -/
theorem higham15_boyd_global_scalar
    {m : ℕ} {p q : ℝ} (hpq : p.HolderConjugate q)
    (A : Fin m → Fin 1 → ℝ)
    (hA : ∀ i j, 0 ≤ A i j)
    (_hGram : Matrix.IsIrreducible
      (Matrix.of (rectGram A) : Matrix (Fin 1) (Fin 1) ℝ))
    (x0 : Fin 1 → ℝ) (hx0 : ∀ j, 0 < x0 j) :
    ∃ xbar : Fin 1 → ℝ,
      xbar ∈ boydNonnegativeUnitCarrier p ∧
      (∀ j, 0 < xbar j) ∧
      (RectPNormPair.general (by omega) hpq A).xnext xbar = xbar ∧
      realVecLpNorm p ((RectPNormPair.general (by omega) hpq A).yof xbar) =
        (RectPNormPair.general (by omega) hpq A).opP ∧
      Tendsto ((RectPNormPair.general (by omega) hpq A).xseq
        (realLpNormalizedStart p x0)) atTop (nhds xbar) ∧
      Tendsto ((RectPNormPair.general (by omega) hpq A).gammaSeq
        (realLpNormalizedStart p x0)) atTop
        (nhds (RectPNormPair.general (by omega) hpq A).opP) := by
  let P := RectPNormPair.general (by omega : 0 < 1) hpq A
  have hebasis : scalarBasis ∈ boydNonnegativeUnitCarrier p :=
    boydScalar_basis_mem_carrier (le_of_lt hpq.lt)
  have hfixed : P.xnext scalarBasis = scalarBasis := by
    simpa [P] using boydScalar_xnext_basis_eq hpq A hA
  have hoptimal : realVecLpNorm p (P.yof scalarBasis) = P.opP := by
    apply boydCarrier_maximum_eq_opP (by omega) hpq A hA hebasis
    intro x hx
    rw [boydScalar_carrier_eq_basis (le_of_lt hpq.lt) hx]
  have hxstart_mem : realLpNormalizedStart p x0 ∈
      boydNonnegativeUnitCarrier p := by
    constructor
    · intro j
      exact (realLpNormalizedStart_pos (by omega)
        (le_of_lt hpq.lt) x0 hx0 j).le
    · exact realLpNormalizedStart_norm_eq_one (by omega)
        (le_of_lt hpq.lt) x0 hx0
  have hxstart : realLpNormalizedStart p x0 = scalarBasis :=
    boydScalar_carrier_eq_basis (le_of_lt hpq.lt) hxstart_mem
  have hxseq : ∀ k, P.xseq (realLpNormalizedStart p x0) k = scalarBasis := by
    intro k
    rw [hxstart]
    simpa [P] using boydScalar_xseq_basis_eq hpq A hA k
  refine ⟨scalarBasis, hebasis, ?_, hfixed, hoptimal, ?_, ?_⟩
  · intro j
    have hj : j = (0 : Fin 1) := Subsingleton.elim _ _
    subst j
    simp [scalarBasis, basisVec]
  · have hfun : P.xseq (realLpNormalizedStart p x0) =
        fun _ => scalarBasis := by
      funext k
      exact hxseq k
    rw [hfun]
    exact tendsto_const_nhds
  · have hfun : P.gammaSeq (realLpNormalizedStart p x0) =
        fun _ => P.opP := by
      funext k
      simp only [RectPNormPair.gammaSeq, hxseq k]
      exact hoptimal
    rw [hfun]
    exact tendsto_const_nhds

/-- Boyd's global convergence statement at every positive printed domain
dimension.  Dimension one is discharged directly; dimensions at least two use
the nonlinear Perron--Frobenius theorem. -/
theorem higham15_boyd_global_of_nonnegative_irreducibleGram_all_dimensions
    {m n : ℕ} (hn : 0 < n)
    {p q : ℝ} (hpq : p.HolderConjugate q)
    (A : Fin m → Fin n → ℝ)
    (hA : ∀ i j, 0 ≤ A i j)
    (hGram : Matrix.IsIrreducible
      (Matrix.of (rectGram A) : Matrix (Fin n) (Fin n) ℝ))
    (x0 : Fin n → ℝ) (hx0 : ∀ j, 0 < x0 j) :
    ∃ xbar : Fin n → ℝ,
      xbar ∈ boydNonnegativeUnitCarrier p ∧
      (∀ j, 0 < xbar j) ∧
      (RectPNormPair.general hn hpq A).xnext xbar = xbar ∧
      realVecLpNorm p ((RectPNormPair.general hn hpq A).yof xbar) =
        (RectPNormPair.general hn hpq A).opP ∧
      Tendsto ((RectPNormPair.general hn hpq A).xseq
        (realLpNormalizedStart p x0)) atTop (nhds xbar) ∧
      Tendsto ((RectPNormPair.general hn hpq A).gammaSeq
        (realLpNormalizedStart p x0)) atTop
        (nhds (RectPNormPair.general hn hpq A).opP) := by
  by_cases hscalar : n = 1
  · subst n
    exact higham15_boyd_global_scalar hpq A hA hGram x0 hx0
  · have htwo : 2 ≤ n := by omega
    letI : Nontrivial (Fin n) := Fin.nontrivial_iff_two_le.mpr htwo
    exact higham15_boyd_global_of_nonnegative_irreducibleGram
      hn hpq A hA hGram x0 hx0

end Ch15
end NumStability
