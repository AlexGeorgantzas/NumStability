-- Analysis/LiebTrace.lean
--
-- Domain-side foundations for the finite-dimensional Lieb/Tropp trace-MGF
-- route used by future matrix-concentration formalizations.

import NumStability.Analysis.CStarMatrixExpectation
import NumStability.Analysis.OperatorLog
import Mathlib.Analysis.CStarAlgebra.ContinuousFunctionalCalculus.Integral
import Mathlib.Analysis.CStarAlgebra.ContinuousFunctionalCalculus.Pi
import Mathlib.Analysis.Calculus.DSlope
import Mathlib.Analysis.Matrix.Order
import Mathlib.Analysis.Matrix.HermitianFunctionalCalculus
import Mathlib.Analysis.Convex.Basic
import Mathlib.Analysis.Normed.Module.Basic
import Mathlib.Algebra.Polynomial.Basic
import Mathlib.Analysis.SpecialFunctions.Integrals.Basic
import Mathlib.Analysis.SpecialFunctions.Log.NegMulLog
import Mathlib.MeasureTheory.Integral.Bochner.Basic
import Mathlib.Topology.Algebra.Polynomial
import Mathlib.Topology.ContinuousMap.Weierstrass

namespace NumStability

open scoped BigOperators ComplexOrder Kronecker MatrixOrder

/-!
## Lieb trace-concavity target vocabulary

Tropp's matrix Laplace-transform proof of matrix Bernstein uses Lieb's theorem:
for fixed self-adjoint `H`, the map

`A |-> Re tr(exp(H + log A))`

is concave on the strictly positive cone.  This file records the local domain
and functional vocabulary for that theorem and closes the elementary convexity
of the strictly positive cone for finite complex `CStarMatrix` objects.

It proves the finite-dimensional Lieb trace-concavity foundation through the
local relative-entropy/Effros perspective route.  Downstream RandNLA files
carry the iid trace-MGF iteration; the scalar matrix-CGF/log-MGF constants,
matrix Bernstein/Khintchine, and paper-level spectral concentration theorems
remain separate concentration layers.
-/

/-- The strictly positive cone in finite complex `CStarMatrix` form. -/
def strictPositiveCStarMatrixCone {ι : Type*} [Fintype ι] [DecidableEq ι] :
    Set (CStarMatrix ι ι ℂ) :=
  {A | IsStrictlyPositive A}

@[simp]
theorem mem_strictPositiveCStarMatrixCone {ι : Type*} [Fintype ι] [DecidableEq ι]
    {A : CStarMatrix ι ι ℂ} :
    A ∈ strictPositiveCStarMatrixCone (ι := ι) ↔ IsStrictlyPositive A :=
  Iff.rfl

/-- Positive real scalar multiples preserve strict positivity for complex
`CStarMatrix` objects. -/
theorem cstarMatrix_isStrictlyPositive_pos_real_smul
    {ι : Type*} [Fintype ι] [DecidableEq ι]
    {A : CStarMatrix ι ι ℂ} {a : ℝ} (ha : 0 < a)
    (hA : IsStrictlyPositive A) :
    IsStrictlyPositive (a • A) := by
  change IsStrictlyPositive ((a : ℂ) • A)
  exact IsStrictlyPositive.smul (show 0 < (a : ℂ) by exact_mod_cast ha) hA

/-- Nonnegative real scalar multiples preserve nonnegativity for complex
`CStarMatrix` objects. -/
theorem cstarMatrix_nonneg_nonneg_real_smul
    {ι : Type*} [Fintype ι] [DecidableEq ι]
    {A : CStarMatrix ι ι ℂ} {a : ℝ} (ha : 0 ≤ a) (hA : 0 ≤ A) :
    0 ≤ a • A := by
  change 0 ≤ ((a : ℂ) • A)
  exact smul_nonneg (show 0 ≤ (a : ℂ) by exact_mod_cast ha) hA

noncomputable instance cstarMatrix_orderClosedTopology
    {ι : Type*} [Fintype ι] :
    OrderClosedTopology (CStarMatrix ι ι ℂ) := by
  letI hstar : StarOrderedRing (CStarMatrix ι ι ℂ) :=
    CStarMatrix.instStarOrderedRing
  exact @CStarAlgebra.instOrderClosedTopology
    (CStarMatrix ι ι ℂ) inferInstance inferInstance hstar

noncomputable instance cstarMatrix_real_isOrderedModule
    {ι : Type*} [Fintype ι] [DecidableEq ι] :
    IsOrderedModule ℝ (CStarMatrix ι ι ℂ) where
  smul_le_smul_of_nonneg_left r hr A B hAB := by
    change ((r : ℂ) • A) ≤ ((r : ℂ) • B)
    exact smul_le_smul_of_nonneg_left hAB
      (show 0 ≤ (r : ℂ) by exact_mod_cast hr)
  smul_le_smul_of_nonneg_right A hA r s hrs := by
    have hdiff_nonneg : 0 ≤ (s - r) • A :=
      cstarMatrix_nonneg_nonneg_real_smul (ι := ι)
        (sub_nonneg.mpr hrs) hA
    rw [← sub_nonneg]
    convert hdiff_nonneg using 1
    module

noncomputable instance cstarMatrix_real_isBoundedSMul
    {ι : Type*} [Fintype ι] [DecidableEq ι] :
    IsBoundedSMul ℝ (CStarMatrix ι ι ℂ) := by
  exact .of_norm_smul_le (fun r A => NormedSpace.norm_smul_le r A)

noncomputable instance cstarMatrix_realSpectrumCompact
    {ι : Type*} [Fintype ι] [DecidableEq ι]
    (A : CStarMatrix ι ι ℂ) :
    CompactSpace (spectrum ℝ A) :=
  spectrum.instCompactSpace (𝕜 := ℝ) (a := A)

noncomputable instance cstarMatrix_realSpectrumContinuousMapContinuousENorm
    {ι : Type*} [Fintype ι] [DecidableEq ι]
    (A : CStarMatrix ι ι ℂ) :
    ContinuousENorm C(↑(spectrum ℝ A), ℝ) :=
  SeminormedAddGroup.toContinuousENorm

/-- The second-order exponential Taylor remainder
`exp x - x - 1 - x^2 / 2` is monotone on the real line.

This scalar calculus lemma is a reusable dependency for Bernstein-style
matrix-CGF estimates. -/
theorem real_exp_quadratic_remainder_monotone :
    Monotone (fun x : ℝ => Real.exp x - x - 1 - x ^ 2 / 2) := by
  let f : ℝ → ℝ := fun x => Real.exp x - x - 1 - x ^ 2 / 2
  have hfderiv : ∀ x : ℝ, HasDerivAt f (Real.exp x - 1 - x) x := by
    intro x
    unfold f
    have h_exp : HasDerivAt (fun t : ℝ => Real.exp t) (Real.exp x) x :=
      Real.hasDerivAt_exp x
    have h_id : HasDerivAt (fun t : ℝ => t) 1 x := hasDerivAt_id x
    have h_one : HasDerivAt (fun _t : ℝ => (1 : ℝ)) 0 x :=
      hasDerivAt_const x 1
    have h_sq_div : HasDerivAt (fun t : ℝ => t ^ 2 / 2) x x := by
      have hpow : HasDerivAt (fun t : ℝ => t ^ 2) (2 * x) x := by
        simpa using (h_id.pow 2)
      convert hpow.div_const 2 using 1
      ring
    convert ((h_exp.sub h_id).sub h_one).sub h_sq_div using 1
    ring
  refine monotone_of_deriv_nonneg ?hdiff ?hnonneg
  · intro x
    exact (hfderiv x).differentiableAt
  · intro x
    rw [(hfderiv x).deriv]
    have h := Real.add_one_le_exp x
    linarith

/-- The elementary nonnegativity of the first-order exponential Taylor
remainder. -/
theorem real_exp_sub_self_sub_one_nonneg (theta : ℝ) :
    0 ≤ Real.exp theta - theta - 1 := by
  have h := Real.add_one_le_exp theta
  linarith

/-- For nonnegative `theta`, the exponential first-order Taylor remainder
dominates `theta^2 / 2`. -/
theorem real_sq_div_two_le_exp_sub_self_sub_one_of_nonneg {theta : ℝ}
    (htheta : 0 ≤ theta) :
    theta ^ 2 / 2 ≤ Real.exp theta - theta - 1 := by
  have hmono := real_exp_quadratic_remainder_monotone
  have hle := hmono htheta
  dsimp at hle
  simp at hle
  linarith

/-- The second-order Taylor polynomial is an upper bound for `exp` on the
nonpositive real axis. -/
theorem real_exp_le_one_add_self_add_sq_div_two_of_nonpos {y : ℝ}
    (hy : y ≤ 0) :
    Real.exp y ≤ 1 + y + y ^ 2 / 2 := by
  have hmono := real_exp_quadratic_remainder_monotone
  have hle := hmono hy
  dsimp at hle
  simp at hle
  linarith

/-- The exponential series tail beginning at degree two. -/
theorem real_exp_tail_two_hasSum (a : ℝ) :
    HasSum (fun n : ℕ => a ^ (n + 2) / ((n + 2).factorial : ℝ))
      (Real.exp a - 1 - a) := by
  have hexp : HasSum (fun n : ℕ => a ^ n / (n.factorial : ℝ)) (Real.exp a) := by
    simpa [Real.exp_eq_exp_ℝ] using
      (NormedSpace.expSeries_div_hasSum_exp (𝔸 := ℝ) a)
  have htail :=
    (hasSum_nat_add_iff'
      (f := fun n : ℕ => a ^ n / (n.factorial : ℝ)) 2).2 hexp
  convert htail using 1
  simp [Finset.sum_range_succ, Nat.factorial]
  ring

/-- Scalar Bernstein parabola for `0 ≤ x ≤ 1`.

This is the power-series part of Tropp's matrix Bernstein scalar inequality:
all degree-`≥ 2` tail terms are bounded by replacing `x^k` with `x^2`. -/
theorem real_exp_mul_le_quadratic_of_nonneg_of_nonneg_of_le_one
    {a x : ℝ} (ha : 0 ≤ a) (hx0 : 0 ≤ x) (hx1 : x ≤ 1) :
    Real.exp (a * x) ≤ 1 + a * x + (Real.exp a - a - 1) * x ^ 2 := by
  have htail_ax := real_exp_tail_two_hasSum (a * x)
  have htail_a := real_exp_tail_two_hasSum a
  have hsumm_ax := htail_ax.summable
  have hsumm_a := htail_a.summable
  have hsumm_scaled :
      Summable (fun n : ℕ =>
        x ^ 2 * (a ^ (n + 2) / ((n + 2).factorial : ℝ))) :=
    hsumm_a.mul_left (x ^ 2)
  have hterm : ∀ n : ℕ,
      (a * x) ^ (n + 2) / ((n + 2).factorial : ℝ) ≤
        x ^ 2 * (a ^ (n + 2) / ((n + 2).factorial : ℝ)) := by
    intro n
    have hfact_pos : 0 < (((n + 2).factorial : ℕ) : ℝ) := by
      exact_mod_cast Nat.factorial_pos (n + 2)
    have hxpow : x ^ (n + 2) ≤ x ^ 2 := by
      have hxn : x ^ n ≤ 1 := pow_le_one₀ hx0 hx1
      calc
        x ^ (n + 2) = x ^ n * x ^ 2 := by ring_nf
        _ ≤ 1 * x ^ 2 := mul_le_mul_of_nonneg_right hxn (sq_nonneg x)
        _ = x ^ 2 := one_mul _
    have hapow_nonneg : 0 ≤ a ^ (n + 2) := pow_nonneg ha _
    have hnum : (a * x) ^ (n + 2) ≤ x ^ 2 * a ^ (n + 2) := by
      calc
        (a * x) ^ (n + 2) = a ^ (n + 2) * x ^ (n + 2) := by
          rw [mul_pow]
        _ ≤ a ^ (n + 2) * x ^ 2 :=
          mul_le_mul_of_nonneg_left hxpow hapow_nonneg
        _ = x ^ 2 * a ^ (n + 2) := by ring
    calc
      (a * x) ^ (n + 2) / ((n + 2).factorial : ℝ) ≤
          (x ^ 2 * a ^ (n + 2)) / ((n + 2).factorial : ℝ) := by
        exact div_le_div_of_nonneg_right hnum hfact_pos.le
      _ = x ^ 2 * (a ^ (n + 2) / ((n + 2).factorial : ℝ)) := by ring
  have htail_le := Summable.tsum_le_tsum hterm hsumm_ax hsumm_scaled
  rw [htail_ax.tsum_eq, hsumm_a.tsum_mul_left] at htail_le
  rw [htail_a.tsum_eq] at htail_le
  nlinarith

/-- Scalar Bernstein parabola for all `x ≤ 1`.

For `0 ≤ x`, this is proved by comparing exponential series tails.  For
`x ≤ 0`, it follows from the second-order Taylor upper bound on the
nonpositive real axis and the lower bound
`a^2 / 2 ≤ exp a - a - 1`. -/
theorem real_exp_mul_le_quadratic_of_nonneg_of_le_one
    {a x : ℝ} (ha : 0 ≤ a) (hx1 : x ≤ 1) :
    Real.exp (a * x) ≤ 1 + a * x + (Real.exp a - a - 1) * x ^ 2 := by
  rcases le_or_gt 0 x with hx0 | hxneg
  · exact real_exp_mul_le_quadratic_of_nonneg_of_nonneg_of_le_one ha hx0 hx1
  · have hy : a * x ≤ 0 := mul_nonpos_of_nonneg_of_nonpos ha hxneg.le
    have hquad := real_exp_le_one_add_self_add_sq_div_two_of_nonpos hy
    have hc := real_sq_div_two_le_exp_sub_self_sub_one_of_nonneg ha
    have hx2 : 0 ≤ x ^ 2 := sq_nonneg x
    have hcx : (a ^ 2 / 2) * x ^ 2 ≤
        (Real.exp a - a - 1) * x ^ 2 :=
      mul_le_mul_of_nonneg_right hc hx2
    nlinarith [sq_nonneg (a * x)]

/-- Scaled scalar Bernstein parabola.  If `theta ≥ 0`, `R > 0`, and `x ≤ R`,
then `exp(theta x)` lies below the quadratic interpolant used in the
matrix-Bernstein one-step CGF estimate. -/
theorem real_exp_mul_le_quadratic_scaled_of_nonneg_of_pos_of_le
    {theta R x : ℝ} (htheta : 0 ≤ theta) (hR : 0 < R) (hx : x ≤ R) :
    Real.exp (theta * x) ≤
      1 + theta * x + ((Real.exp (theta * R) - theta * R - 1) / R ^ 2) * x ^ 2 := by
  have ha : 0 ≤ theta * R := mul_nonneg htheta hR.le
  have hu : x / R ≤ 1 := (div_le_one hR).mpr hx
  have hbase := real_exp_mul_le_quadratic_of_nonneg_of_le_one ha hu
  have hR2pos : 0 < R ^ 2 := sq_pos_of_pos hR
  have hrewrite_exp : theta * R * (x / R) = theta * x := by
    field_simp [hR.ne']
  have hrewrite_quad : (x / R) ^ 2 = x ^ 2 / R ^ 2 := by
    field_simp [hR.ne']
  rw [hrewrite_exp, hrewrite_quad] at hbase
  field_simp [hR.ne'] at hbase ⊢
  nlinarith [hR2pos.le]

/-- The real continuous functional calculus evaluates scalar quadratics as the
corresponding matrix polynomial.

This is a reusable bridge for matrix-CGF proofs: after a scalar Bernstein
parabola inequality is proved on the spectrum, this lemma turns the CFC
right-hand side into the Loewner-order polynomial
`I + theta X + beta X^2`. -/
theorem cstarMatrix_cfc_quadratic_eq
    {ι : Type*} [Fintype ι] [DecidableEq ι]
    {X : CStarMatrix ι ι ℂ} (hX : IsSelfAdjoint X) (theta beta : ℝ) :
    cfc (p := IsSelfAdjoint)
        (fun x : ℝ => 1 + theta * x + beta * x ^ 2) X =
      (1 : CStarMatrix ι ι ℂ) + theta • X + beta • (X * X) := by
  have hlinear :
      cfc (p := IsSelfAdjoint) (fun x : ℝ => 1 + theta * x) X =
        (1 : CStarMatrix ι ι ℂ) + theta • X := by
    rw [cfc_const_add (R := ℝ) (A := CStarMatrix ι ι ℂ)
      (p := IsSelfAdjoint) (r := 1) (f := fun x : ℝ => theta * x)
      (a := X) (hf := by fun_prop) (ha := hX)]
    have hmulid :
        cfc (p := IsSelfAdjoint) (fun x : ℝ => theta * x) X =
          theta • X := by
      simpa using
        (cfc_const_mul_id (R := ℝ) (A := CStarMatrix ι ι ℂ)
          (p := IsSelfAdjoint) (r := theta) (a := X) (ha := hX))
    rw [hmulid]
    have hone :
        algebraMap ℝ (CStarMatrix ι ι ℂ) (1 : ℝ) =
          (1 : CStarMatrix ι ι ℂ) := by
      exact (algebraMap ℝ (CStarMatrix ι ι ℂ)).map_one
    rw [hone]
  have hquad :
      cfc (p := IsSelfAdjoint) (fun x : ℝ => beta * x ^ 2) X =
        beta • (X * X) := by
    rw [cfc_const_mul (R := ℝ) (A := CStarMatrix ι ι ℂ)
      (p := IsSelfAdjoint) (r := beta) (f := fun x : ℝ => x ^ 2)
      (a := X) (hf := by fun_prop)]
    have hpow :
        cfc (p := IsSelfAdjoint) (fun x : ℝ => x ^ 2) X =
          X * X := by
      simpa [pow_two] using
        (cfc_pow_id (R := ℝ) (A := CStarMatrix ι ι ℂ)
          (p := IsSelfAdjoint) (a := X) (n := 2) (ha := hX))
    rw [hpow]
  rw [cfc_add (R := ℝ) (A := CStarMatrix ι ι ℂ)
    (p := IsSelfAdjoint) (f := fun x : ℝ => 1 + theta * x)
    (g := fun x : ℝ => beta * x ^ 2) (a := X)
    (hf := by fun_prop) (hg := by fun_prop)]
  rw [hlinear, hquad]

/-- Scalar Bernstein-parabola inequalities lift through the real continuous
functional calculus to Loewner-order matrix inequalities.

The hypothesis is deliberately just the scalar pointwise inequality on
`spectrum ℝ X`.  A later scalar-calculus theorem can instantiate it with the
usual Bernstein coefficient, after which this bridge supplies the operator
inequality needed in the matrix-CGF route. -/
theorem cstarMatrix_cfc_real_exp_mul_le_quadratic_of_spectrum
    {ι : Type*} [Fintype ι] [DecidableEq ι]
    {X : CStarMatrix ι ι ℂ} (hX : IsSelfAdjoint X) (theta beta : ℝ)
    (hpoint : ∀ x ∈ spectrum ℝ X,
      Real.exp (theta * x) ≤ 1 + theta * x + beta * x ^ 2) :
    cfc (p := IsSelfAdjoint) (fun x : ℝ => Real.exp (theta * x)) X ≤
      (1 : CStarMatrix ι ι ℂ) + theta • X + beta • (X * X) := by
  have hmono :
      cfc (p := IsSelfAdjoint) (fun x : ℝ => Real.exp (theta * x)) X ≤
        cfc (p := IsSelfAdjoint)
          (fun x : ℝ => 1 + theta * x + beta * x ^ 2) X := by
    exact cfc_mono (R := ℝ) (A := CStarMatrix ι ι ℂ)
      (p := IsSelfAdjoint) (a := X)
      (f := fun x : ℝ => Real.exp (theta * x))
      (g := fun x : ℝ => 1 + theta * x + beta * x ^ 2)
      hpoint (hf := by fun_prop) (hg := by fun_prop)
  exact hmono.trans
    (le_of_eq (cstarMatrix_cfc_quadratic_eq hX theta beta))

/-- Explicit Bernstein-parabola CFC lift with upper spectral bound `x ≤ R`.

This combines the scalar Bernstein parabola with the real continuous
functional calculus, yielding the one-step Loewner polynomial shape used in
matrix-CGF proofs. -/
theorem cstarMatrix_cfc_real_exp_mul_le_bernstein_quadratic_of_spectrum_le
    {ι : Type*} [Fintype ι] [DecidableEq ι]
    {X : CStarMatrix ι ι ℂ} (hX : IsSelfAdjoint X)
    {theta R : ℝ} (htheta : 0 ≤ theta) (hR : 0 < R)
    (hspec : ∀ x ∈ spectrum ℝ X, x ≤ R) :
    cfc (p := IsSelfAdjoint) (fun x : ℝ => Real.exp (theta * x)) X ≤
      (1 : CStarMatrix ι ι ℂ) + theta • X +
        ((Real.exp (theta * R) - theta * R - 1) / R ^ 2) • (X * X) := by
  exact cstarMatrix_cfc_real_exp_mul_le_quadratic_of_spectrum hX theta
    ((Real.exp (theta * R) - theta * R - 1) / R ^ 2)
    (fun x hx =>
      real_exp_mul_le_quadratic_scaled_of_nonneg_of_pos_of_le
        htheta hR (hspec x hx))

/-- Real scalar multiplication preserves self-adjointness for finite complex
C⋆-matrices. -/
theorem cstarMatrix_real_smul_isSelfAdjoint
    {ι : Type*} [Fintype ι] [DecidableEq ι]
    {X : CStarMatrix ι ι ℂ} (hX : IsSelfAdjoint X) (a : ℝ) :
    IsSelfAdjoint (a • X : CStarMatrix ι ι ℂ) := by
  change IsSelfAdjoint ((a : ℂ) • X)
  exact (isSelfAdjoint_iff.mpr
    (by simp : star (a : ℂ) = (a : ℂ))).smul hX

/-- The composed real-CFC exponential `x ↦ exp (theta x)` agrees with the
normed-algebra exponential of the real scalar multiple `theta • X`. -/
theorem cstarMatrix_cfc_real_exp_mul_eq_normedSpace_exp_real_smul
    {ι : Type*} [Fintype ι] [DecidableEq ι]
    {X : CStarMatrix ι ι ℂ} (hX : IsSelfAdjoint X) (theta : ℝ) :
    cfc (p := IsSelfAdjoint) (fun x : ℝ => Real.exp (theta * x)) X =
      NormedSpace.exp (theta • X : CStarMatrix ι ι ℂ) := by
  rw [cfc_comp' (R := ℝ) (A := CStarMatrix ι ι ℂ)
    (p := IsSelfAdjoint) (g := Real.exp)
    (f := fun x : ℝ => theta * x) (a := X)]
  rw [cfc_const_mul_id (R := ℝ) (A := CStarMatrix ι ι ℂ)
    (p := IsSelfAdjoint) (r := theta) (a := X) (ha := hX)]
  exact CFC.real_exp_eq_normedSpace_exp
    (A := CStarMatrix ι ι ℂ)
    (a := (theta • X : CStarMatrix ι ι ℂ))
    (cstarMatrix_real_smul_isSelfAdjoint hX theta)

/-- The square of a self-adjoint finite complex C⋆-matrix is nonnegative. -/
theorem cstarMatrix_selfAdjoint_mul_self_nonneg
    {ι : Type*} [Fintype ι] [DecidableEq ι]
    {X : CStarMatrix ι ι ℂ} (hX : IsSelfAdjoint X) :
    0 ≤ X * X := by
  have hstar : star X = X := isSelfAdjoint_iff.mp hX
  have hsq : 0 ≤ star X * X := star_mul_self_nonneg X
  rw [hstar] at hsq
  exact hsq

/-- Functional-calculus proof of the elementary operator inequality
`I + B ≤ exp B` for nonnegative finite complex C⋆-matrices. -/
theorem cstarMatrix_one_add_le_normedSpace_exp_of_nonneg
    {ι : Type*} [Fintype ι] [DecidableEq ι]
    {B : CStarMatrix ι ι ℂ} (hB : 0 ≤ B) :
    (1 : CStarMatrix ι ι ℂ) + B ≤ NormedSpace.exp B := by
  have hBsa : IsSelfAdjoint B := IsSelfAdjoint.of_nonneg hB
  have hmono :
      cfc (p := IsSelfAdjoint) (fun x : ℝ => 1 + x) B ≤
        cfc (p := IsSelfAdjoint) Real.exp B := by
    exact cfc_mono (R := ℝ) (A := CStarMatrix ι ι ℂ)
      (p := IsSelfAdjoint) (a := B)
      (f := fun x : ℝ => 1 + x) (g := Real.exp)
      (fun x _hx => by simpa [add_comm] using Real.add_one_le_exp x)
      (hf := by fun_prop) (hg := by fun_prop)
  have hleft :
      cfc (p := IsSelfAdjoint) (fun x : ℝ => 1 + x) B =
        (1 : CStarMatrix ι ι ℂ) + B := by
    rw [cfc_const_add (R := ℝ) (A := CStarMatrix ι ι ℂ)
      (p := IsSelfAdjoint) (r := 1) (f := fun x : ℝ => x)
      (a := B) (hf := by fun_prop) (ha := hBsa)]
    have hid : cfc (p := IsSelfAdjoint) (fun x : ℝ => x) B = B := by
      simpa [id] using cfc_id (R := ℝ) (A := CStarMatrix ι ι ℂ)
        (p := IsSelfAdjoint) (a := B) (ha := hBsa)
    rw [hid]
    have hone :
        algebraMap ℝ (CStarMatrix ι ι ℂ) (1 : ℝ) =
          (1 : CStarMatrix ι ι ℂ) := by
      exact (algebraMap ℝ (CStarMatrix ι ι ℂ)).map_one
    rw [hone]
  have hright :
      cfc (p := IsSelfAdjoint) Real.exp B = NormedSpace.exp B := by
    exact CFC.real_exp_eq_normedSpace_exp
      (A := CStarMatrix ι ι ℂ) (a := B) hBsa
  simpa [hleft, hright] using hmono

/-- Operator logarithm bound `log (I + B) ≤ B` for nonnegative finite complex
C⋆-matrices. -/
theorem cstarMatrix_log_one_add_le_self_of_nonneg
    {ι : Type*} [Fintype ι] [DecidableEq ι]
    {B : CStarMatrix ι ι ℂ} (hB : 0 ≤ B) :
    CFC.log ((1 : CStarMatrix ι ι ℂ) + B) ≤ B := by
  have hle : (1 : CStarMatrix ι ι ℂ) + B ≤ NormedSpace.exp B :=
    cstarMatrix_one_add_le_normedSpace_exp_of_nonneg hB
  have hsp : IsStrictlyPositive ((1 : CStarMatrix ι ι ℂ) + B) := by
    have hone :
        IsStrictlyPositive
          (((1 : ℝ) : ℂ) • (1 : CStarMatrix ι ι ℂ)) :=
      cstarMatrix_pos_real_smul_one_isStrictlyPositive (ι := ι) zero_lt_one
    have hsp' :
        IsStrictlyPositive
          (((1 : ℝ) : ℂ) • (1 : CStarMatrix ι ι ℂ) + B) :=
      hone.add_nonneg hB
    simpa using hsp'
  have hlog := cstarMatrix_log_le_log
    ((1 : CStarMatrix ι ι ℂ) + B) (NormedSpace.exp B) hle hsp
  rw [cstarMatrix_log_normedSpace_exp_of_isSelfAdjoint
    B (IsSelfAdjoint.of_nonneg hB)] at hlog
  exact hlog

/-- One-sample Bernstein matrix-CGF expectation bound after centering.

If `X` is self-adjoint, `E X = 0`, and every real spectral value of `X` is
bounded above by `R`, then the expectation of the CFC exponential is bounded
by the Bernstein variance proxy `I + g(theta,R) E[X^2]`. -/
theorem FiniteProbability.expectationCStarMatrix_cfc_real_exp_mul_le_bernstein_variance_proxy
    {Ω : Type*} [Fintype Ω]
    {ι : Type*} [Fintype ι] [DecidableEq ι]
    (P : FiniteProbability Ω)
    {X : Ω → CStarMatrix ι ι ℂ} (hX : ∀ ω, IsSelfAdjoint (X ω))
    (hmean : P.expectationCStarMatrix X = 0)
    {theta R : ℝ} (htheta : 0 ≤ theta) (hR : 0 < R)
    (hspec : ∀ ω x, x ∈ spectrum ℝ (X ω) → x ≤ R) :
    P.expectationCStarMatrix
        (fun ω => cfc (p := IsSelfAdjoint)
          (fun x : ℝ => Real.exp (theta * x)) (X ω)) ≤
      (1 : CStarMatrix ι ι ℂ) +
        ((Real.exp (theta * R) - theta * R - 1) / R ^ 2) •
          P.expectationCStarMatrix (fun ω => X ω * X ω) := by
  let beta : ℝ := (Real.exp (theta * R) - theta * R - 1) / R ^ 2
  have hpoint : ∀ ω,
      cfc (p := IsSelfAdjoint) (fun x : ℝ => Real.exp (theta * x)) (X ω) ≤
        (1 : CStarMatrix ι ι ℂ) + theta • X ω +
          beta • (X ω * X ω) := by
    intro ω
    exact cstarMatrix_cfc_real_exp_mul_le_bernstein_quadratic_of_spectrum_le
      (hX ω) htheta hR (fun x hx => hspec ω x hx)
  have hmono :=
    P.expectationCStarMatrix_mono
      (fun ω => cfc (p := IsSelfAdjoint)
        (fun x : ℝ => Real.exp (theta * x)) (X ω))
      (fun ω => (1 : CStarMatrix ι ι ℂ) + theta • X ω +
        beta • (X ω * X ω))
      hpoint
  have hlin :
      P.expectationCStarMatrix
          (fun ω => (1 : CStarMatrix ι ι ℂ) + theta • X ω +
            beta • (X ω * X ω)) =
        (1 : CStarMatrix ι ι ℂ) + theta • P.expectationCStarMatrix X +
          beta • P.expectationCStarMatrix (fun ω => X ω * X ω) := by
    rw [FiniteProbability.expectationCStarMatrix_add]
    rw [FiniteProbability.expectationCStarMatrix_add]
    rw [FiniteProbability.expectationCStarMatrix_const]
    rw [FiniteProbability.expectationCStarMatrix_real_smul]
    rw [FiniteProbability.expectationCStarMatrix_real_smul]
  calc
    P.expectationCStarMatrix
        (fun ω => cfc (p := IsSelfAdjoint)
          (fun x : ℝ => Real.exp (theta * x)) (X ω))
        ≤ P.expectationCStarMatrix
            (fun ω => (1 : CStarMatrix ι ι ℂ) + theta • X ω +
              beta • (X ω * X ω)) := hmono
    _ = (1 : CStarMatrix ι ι ℂ) + theta • P.expectationCStarMatrix X +
          beta • P.expectationCStarMatrix (fun ω => X ω * X ω) := hlin
    _ = (1 : CStarMatrix ι ι ℂ) +
          beta • P.expectationCStarMatrix (fun ω => X ω * X ω) := by
        rw [hmean]
        change (1 : CStarMatrix ι ι ℂ) +
            (theta : ℂ) • (0 : CStarMatrix ι ι ℂ) +
              (beta : ℂ) • P.expectationCStarMatrix (fun ω => X ω * X ω) =
          (1 : CStarMatrix ι ι ℂ) +
            (beta : ℂ) • P.expectationCStarMatrix (fun ω => X ω * X ω)
        simp

/-- Support-aware one-sample Bernstein matrix-CGF expectation bound after
centering.

This variant requires the spectral upper bound only on positive-probability
atoms.  It is the form needed by finite sampling laws whose retained-sample
side condition is derived from `0 < P.prob sample`. -/
theorem FiniteProbability.expectationCStarMatrix_cfc_real_exp_mul_le_bernstein_variance_proxy_of_prob_pos
    {Ω : Type*} [Fintype Ω]
    {ι : Type*} [Fintype ι] [DecidableEq ι]
    (P : FiniteProbability Ω)
    {X : Ω → CStarMatrix ι ι ℂ} (hX : ∀ ω, IsSelfAdjoint (X ω))
    (hmean : P.expectationCStarMatrix X = 0)
    {theta R : ℝ} (htheta : 0 ≤ theta) (hR : 0 < R)
    (hspec : ∀ ω, 0 < P.prob ω →
      ∀ x, x ∈ spectrum ℝ (X ω) → x ≤ R) :
    P.expectationCStarMatrix
        (fun ω => cfc (p := IsSelfAdjoint)
          (fun x : ℝ => Real.exp (theta * x)) (X ω)) ≤
      (1 : CStarMatrix ι ι ℂ) +
        ((Real.exp (theta * R) - theta * R - 1) / R ^ 2) •
          P.expectationCStarMatrix (fun ω => X ω * X ω) := by
  let beta : ℝ := (Real.exp (theta * R) - theta * R - 1) / R ^ 2
  have hpoint : ∀ ω, 0 < P.prob ω →
      cfc (p := IsSelfAdjoint) (fun x : ℝ => Real.exp (theta * x)) (X ω) ≤
        (1 : CStarMatrix ι ι ℂ) + theta • X ω +
          beta • (X ω * X ω) := by
    intro ω hω
    exact cstarMatrix_cfc_real_exp_mul_le_bernstein_quadratic_of_spectrum_le
      (hX ω) htheta hR (fun x hx => hspec ω hω x hx)
  have hmono :=
    P.expectationCStarMatrix_mono_of_prob_pos
      (fun ω => cfc (p := IsSelfAdjoint)
        (fun x : ℝ => Real.exp (theta * x)) (X ω))
      (fun ω => (1 : CStarMatrix ι ι ℂ) + theta • X ω +
        beta • (X ω * X ω))
      hpoint
  have hlin :
      P.expectationCStarMatrix
          (fun ω => (1 : CStarMatrix ι ι ℂ) + theta • X ω +
            beta • (X ω * X ω)) =
        (1 : CStarMatrix ι ι ℂ) + theta • P.expectationCStarMatrix X +
          beta • P.expectationCStarMatrix (fun ω => X ω * X ω) := by
    rw [FiniteProbability.expectationCStarMatrix_add]
    rw [FiniteProbability.expectationCStarMatrix_add]
    rw [FiniteProbability.expectationCStarMatrix_const]
    rw [FiniteProbability.expectationCStarMatrix_real_smul]
    rw [FiniteProbability.expectationCStarMatrix_real_smul]
  calc
    P.expectationCStarMatrix
        (fun ω => cfc (p := IsSelfAdjoint)
          (fun x : ℝ => Real.exp (theta * x)) (X ω))
        ≤ P.expectationCStarMatrix
            (fun ω => (1 : CStarMatrix ι ι ℂ) + theta • X ω +
              beta • (X ω * X ω)) := hmono
    _ = (1 : CStarMatrix ι ι ℂ) + theta • P.expectationCStarMatrix X +
          beta • P.expectationCStarMatrix (fun ω => X ω * X ω) := hlin
    _ = (1 : CStarMatrix ι ι ℂ) +
          beta • P.expectationCStarMatrix (fun ω => X ω * X ω) := by
        rw [hmean]
        change (1 : CStarMatrix ι ι ℂ) +
            (theta : ℂ) • (0 : CStarMatrix ι ι ℂ) +
              (beta : ℂ) • P.expectationCStarMatrix (fun ω => X ω * X ω) =
          (1 : CStarMatrix ι ι ℂ) +
            (beta : ℂ) • P.expectationCStarMatrix (fun ω => X ω * X ω)
        simp

/-- One-sample Bernstein matrix-CGF/log-MGF variance proxy.

This is the local Tropp-style logarithmic step for one centered self-adjoint
matrix sample: the operator logarithm of the expected exponential is bounded
by `g(theta,R) E[X^2]`.  It closes the formerly open one-sample
CGF/log-MGF dependency, but not yet the iid iteration or final tail
optimization. -/
theorem FiniteProbability.cstarMatrix_log_expectationCStarMatrix_cfc_real_exp_mul_le_bernstein_variance_proxy
    {Ω : Type*} [Fintype Ω]
    {ι : Type*} [Fintype ι] [DecidableEq ι]
    (P : FiniteProbability Ω)
    {X : Ω → CStarMatrix ι ι ℂ} (hX : ∀ ω, IsSelfAdjoint (X ω))
    (hmean : P.expectationCStarMatrix X = 0)
    {theta R : ℝ} (htheta : 0 ≤ theta) (hR : 0 < R)
    (hspec : ∀ ω x, x ∈ spectrum ℝ (X ω) → x ≤ R) :
    CFC.log
        (P.expectationCStarMatrix
          (fun ω => cfc (p := IsSelfAdjoint)
            (fun x : ℝ => Real.exp (theta * x)) (X ω))) ≤
      ((Real.exp (theta * R) - theta * R - 1) / R ^ 2) •
        P.expectationCStarMatrix (fun ω => X ω * X ω) := by
  let beta : ℝ := (Real.exp (theta * R) - theta * R - 1) / R ^ 2
  let V : CStarMatrix ι ι ℂ :=
    P.expectationCStarMatrix (fun ω => X ω * X ω)
  have hbeta_nonneg : 0 ≤ beta := by
    have hnum : 0 ≤ Real.exp (theta * R) - theta * R - 1 :=
      real_exp_sub_self_sub_one_nonneg (theta * R)
    have hden : 0 ≤ R ^ 2 := sq_nonneg R
    exact div_nonneg hnum hden
  have hV_nonneg : 0 ≤ V := by
    exact P.expectationCStarMatrix_nonneg
      (fun ω => X ω * X ω)
      (fun ω => cstarMatrix_selfAdjoint_mul_self_nonneg (hX ω))
  have hB_nonneg : 0 ≤ beta • V :=
    cstarMatrix_nonneg_nonneg_real_smul (ι := ι) hbeta_nonneg hV_nonneg
  have hcgf :=
    P.expectationCStarMatrix_cfc_real_exp_mul_le_bernstein_variance_proxy
      hX hmean htheta hR hspec
  have hstrict :
      IsStrictlyPositive
        (P.expectationCStarMatrix
          (fun ω => cfc (p := IsSelfAdjoint)
            (fun x : ℝ => Real.exp (theta * x)) (X ω))) := by
    apply P.expectationCStarMatrix_isStrictlyPositive
    intro ω
    rw [cstarMatrix_cfc_real_exp_mul_eq_normedSpace_exp_real_smul
      (hX ω) theta]
    exact cstarMatrix_normedSpace_exp_isStrictlyPositive_of_isSelfAdjoint
      (theta • X ω : CStarMatrix ι ι ℂ)
      (cstarMatrix_real_smul_isSelfAdjoint (hX ω) theta)
  have hlogmono :=
    cstarMatrix_log_le_log
      (P.expectationCStarMatrix
        (fun ω => cfc (p := IsSelfAdjoint)
          (fun x : ℝ => Real.exp (theta * x)) (X ω)))
      ((1 : CStarMatrix ι ι ℂ) + beta • V)
      (by simpa [beta, V] using hcgf)
      hstrict
  have hlogquad :=
    cstarMatrix_log_one_add_le_self_of_nonneg (B := beta • V) hB_nonneg
  exact hlogmono.trans (by simpa [beta, V] using hlogquad)

/-- Support-aware one-sample Bernstein matrix-CGF/log-MGF variance proxy.

The spectral upper bound is required only on atoms with positive probability.
This removes the zero-mass-sample artifact that otherwise appears when applying
the generic theorem to finite sampling distributions. -/
theorem FiniteProbability.cstarMatrix_log_expectationCStarMatrix_cfc_real_exp_mul_le_bernstein_variance_proxy_of_prob_pos
    {Ω : Type*} [Fintype Ω]
    {ι : Type*} [Fintype ι] [DecidableEq ι]
    (P : FiniteProbability Ω)
    {X : Ω → CStarMatrix ι ι ℂ} (hX : ∀ ω, IsSelfAdjoint (X ω))
    (hmean : P.expectationCStarMatrix X = 0)
    {theta R : ℝ} (htheta : 0 ≤ theta) (hR : 0 < R)
    (hspec : ∀ ω, 0 < P.prob ω →
      ∀ x, x ∈ spectrum ℝ (X ω) → x ≤ R) :
    CFC.log
        (P.expectationCStarMatrix
          (fun ω => cfc (p := IsSelfAdjoint)
            (fun x : ℝ => Real.exp (theta * x)) (X ω))) ≤
      ((Real.exp (theta * R) - theta * R - 1) / R ^ 2) •
        P.expectationCStarMatrix (fun ω => X ω * X ω) := by
  let beta : ℝ := (Real.exp (theta * R) - theta * R - 1) / R ^ 2
  let V : CStarMatrix ι ι ℂ :=
    P.expectationCStarMatrix (fun ω => X ω * X ω)
  have hbeta_nonneg : 0 ≤ beta := by
    have hnum : 0 ≤ Real.exp (theta * R) - theta * R - 1 :=
      real_exp_sub_self_sub_one_nonneg (theta * R)
    have hden : 0 ≤ R ^ 2 := sq_nonneg R
    exact div_nonneg hnum hden
  have hV_nonneg : 0 ≤ V := by
    exact P.expectationCStarMatrix_nonneg
      (fun ω => X ω * X ω)
      (fun ω => cstarMatrix_selfAdjoint_mul_self_nonneg (hX ω))
  have hB_nonneg : 0 ≤ beta • V :=
    cstarMatrix_nonneg_nonneg_real_smul (ι := ι) hbeta_nonneg hV_nonneg
  have hcgf :=
    P.expectationCStarMatrix_cfc_real_exp_mul_le_bernstein_variance_proxy_of_prob_pos
      hX hmean htheta hR hspec
  have hstrict :
      IsStrictlyPositive
        (P.expectationCStarMatrix
          (fun ω => cfc (p := IsSelfAdjoint)
            (fun x : ℝ => Real.exp (theta * x)) (X ω))) := by
    apply P.expectationCStarMatrix_isStrictlyPositive
    intro ω
    rw [cstarMatrix_cfc_real_exp_mul_eq_normedSpace_exp_real_smul
      (hX ω) theta]
    exact cstarMatrix_normedSpace_exp_isStrictlyPositive_of_isSelfAdjoint
      (theta • X ω : CStarMatrix ι ι ℂ)
      (cstarMatrix_real_smul_isSelfAdjoint (hX ω) theta)
  have hlogmono :=
    cstarMatrix_log_le_log
      (P.expectationCStarMatrix
        (fun ω => cfc (p := IsSelfAdjoint)
          (fun x : ℝ => Real.exp (theta * x)) (X ω)))
      ((1 : CStarMatrix ι ι ℂ) + beta • V)
      (by simpa [beta, V] using hcgf)
      hstrict
  have hlogquad :=
    cstarMatrix_log_one_add_le_self_of_nonneg (B := beta • V) hB_nonneg
  exact hlogmono.trans (by simpa [beta, V] using hlogquad)

/-- Normed-exponential form of the one-sample Bernstein matrix-CGF/log-MGF
variance proxy. -/
theorem FiniteProbability.cstarMatrix_log_expectationCStarMatrix_normed_exp_real_smul_le_bernstein_variance_proxy
    {Ω : Type*} [Fintype Ω]
    {ι : Type*} [Fintype ι] [DecidableEq ι]
    (P : FiniteProbability Ω)
    {X : Ω → CStarMatrix ι ι ℂ} (hX : ∀ ω, IsSelfAdjoint (X ω))
    (hmean : P.expectationCStarMatrix X = 0)
    {theta R : ℝ} (htheta : 0 ≤ theta) (hR : 0 < R)
    (hspec : ∀ ω x, x ∈ spectrum ℝ (X ω) → x ≤ R) :
    CFC.log
        (P.expectationCStarMatrix
          (fun ω => NormedSpace.exp
            (theta • X ω : CStarMatrix ι ι ℂ))) ≤
      ((Real.exp (theta * R) - theta * R - 1) / R ^ 2) •
        P.expectationCStarMatrix (fun ω => X ω * X ω) := by
  have hEq :
      P.expectationCStarMatrix
          (fun ω => NormedSpace.exp
            (theta • X ω : CStarMatrix ι ι ℂ)) =
        P.expectationCStarMatrix
          (fun ω => cfc (p := IsSelfAdjoint)
            (fun x : ℝ => Real.exp (theta * x)) (X ω)) := by
    apply congrArg
    funext ω
    exact (cstarMatrix_cfc_real_exp_mul_eq_normedSpace_exp_real_smul
      (hX ω) theta).symm
  rw [hEq]
  exact
    P.cstarMatrix_log_expectationCStarMatrix_cfc_real_exp_mul_le_bernstein_variance_proxy
      hX hmean htheta hR hspec

/-- Support-aware normed-exponential form of the one-sample Bernstein
matrix-CGF/log-MGF variance proxy. -/
theorem FiniteProbability.cstarMatrix_log_expectationCStarMatrix_normed_exp_real_smul_le_bernstein_variance_proxy_of_prob_pos
    {Ω : Type*} [Fintype Ω]
    {ι : Type*} [Fintype ι] [DecidableEq ι]
    (P : FiniteProbability Ω)
    {X : Ω → CStarMatrix ι ι ℂ} (hX : ∀ ω, IsSelfAdjoint (X ω))
    (hmean : P.expectationCStarMatrix X = 0)
    {theta R : ℝ} (htheta : 0 ≤ theta) (hR : 0 < R)
    (hspec : ∀ ω, 0 < P.prob ω →
      ∀ x, x ∈ spectrum ℝ (X ω) → x ≤ R) :
    CFC.log
        (P.expectationCStarMatrix
          (fun ω => NormedSpace.exp
            (theta • X ω : CStarMatrix ι ι ℂ))) ≤
      ((Real.exp (theta * R) - theta * R - 1) / R ^ 2) •
        P.expectationCStarMatrix (fun ω => X ω * X ω) := by
  have hEq :
      P.expectationCStarMatrix
          (fun ω => NormedSpace.exp
            (theta • X ω : CStarMatrix ι ι ℂ)) =
        P.expectationCStarMatrix
          (fun ω => cfc (p := IsSelfAdjoint)
            (fun x : ℝ => Real.exp (theta * x)) (X ω)) := by
    apply congrArg
    funext ω
    exact (cstarMatrix_cfc_real_exp_mul_eq_normedSpace_exp_real_smul
      (hX ω) theta).symm
  rw [hEq]
  exact
    P.cstarMatrix_log_expectationCStarMatrix_cfc_real_exp_mul_le_bernstein_variance_proxy_of_prob_pos
      hX hmean htheta hR hspec

/-- A positive multiple of a strictly positive matrix plus a nonnegative
multiple of a nonnegative matrix is strictly positive. -/
theorem cstarMatrix_isStrictlyPositive_pos_nonneg_real_smul_add
    {ι : Type*} [Fintype ι] [DecidableEq ι]
    {A B : CStarMatrix ι ι ℂ} {a b : ℝ}
    (ha : 0 < a) (hb : 0 ≤ b)
    (hA : IsStrictlyPositive A) (hB : 0 ≤ B) :
    IsStrictlyPositive (a • A + b • B) := by
  change IsStrictlyPositive ((a : ℂ) • A + (b : ℂ) • B)
  exact
    (IsStrictlyPositive.smul
      (show 0 < (a : ℂ) by exact_mod_cast ha) hA).add_nonneg
      (smul_nonneg (show 0 ≤ (b : ℂ) by exact_mod_cast hb) hB)

/-- The strictly positive cone of finite complex `CStarMatrix` objects is
convex over real scalars.  This closes the domain-convexity prerequisite for
stating Lieb trace concavity as a `ConcaveOn` theorem over this local domain. -/
theorem strictPositiveCStarMatrixCone_convex
    {ι : Type*} [Fintype ι] [DecidableEq ι] :
    Convex ℝ (strictPositiveCStarMatrixCone (ι := ι)) := by
  intro A hA B hB a b ha hb hab
  dsimp [strictPositiveCStarMatrixCone] at hA hB ⊢
  have hapos_or_zero : a = 0 ∨ 0 < a := by
    rcases eq_or_lt_of_le ha with h | h
    · exact Or.inl h.symm
    · exact Or.inr h
  have hbpos_or_zero : b = 0 ∨ 0 < b := by
    rcases eq_or_lt_of_le hb with h | h
    · exact Or.inl h.symm
    · exact Or.inr h
  rcases hapos_or_zero with rfl | hapos
  · have hb1 : b = 1 := by linarith
    subst hb1
    change IsStrictlyPositive (((0 : ℝ) : ℂ) • A + ((1 : ℝ) : ℂ) • B)
    simpa using hB
  rcases hbpos_or_zero with rfl | _hbpos
  · have ha1 : a = 1 := by linarith
    subst ha1
    change IsStrictlyPositive (((1 : ℝ) : ℂ) • A + ((0 : ℝ) : ℂ) • B)
    simpa using hA
  exact cstarMatrix_isStrictlyPositive_pos_nonneg_real_smul_add (ι := ι)
    hapos hb hA hB.nonneg

/-- The operator logarithm of a complex `CStarMatrix` is self-adjoint in the
real continuous-functional-calculus sense used by the Lieb trace functional. -/
theorem cstarMatrix_log_isSelfAdjoint
    {ι : Type*} [Fintype ι] [DecidableEq ι]
    (A : CStarMatrix ι ι ℂ) :
    IsSelfAdjoint (CFC.log A) := by
  exact IsSelfAdjoint.cfc

/-- For self-adjoint `H`, the argument `H + log A` in the Lieb trace functional
is self-adjoint. -/
theorem liebTraceArgument_isSelfAdjoint
    {ι : Type*} [Fintype ι] [DecidableEq ι]
    {H A : CStarMatrix ι ι ℂ} (hH : IsSelfAdjoint H) :
    IsSelfAdjoint (H + CFC.log A) := by
  exact hH.add (cstarMatrix_log_isSelfAdjoint A)

/-- For self-adjoint `H`, the argument `H + log A` is star-normal, so it is in
the domain of the complex CFC exponential used by `liebTraceFunctional`. -/
theorem liebTraceArgument_isStarNormal
    {ι : Type*} [Fintype ι] [DecidableEq ι]
    {H A : CStarMatrix ι ι ℂ} (hH : IsSelfAdjoint H) :
    IsStarNormal (H + CFC.log A) :=
  (liebTraceArgument_isSelfAdjoint hH).isStarNormal

/-- The complex CFC exponential in the local Lieb functional is nonnegative
whenever the fixed matrix `H` is self-adjoint. -/
theorem liebTraceCfcExp_nonneg
    {ι : Type*} [Fintype ι] [DecidableEq ι]
    {H A : CStarMatrix ι ι ℂ} (hH : IsSelfAdjoint H) :
    0 ≤ cfc (p := IsStarNormal) Complex.exp (H + CFC.log A) := by
  let X := H + CFC.log A
  have hX : IsSelfAdjoint X := liebTraceArgument_isSelfAdjoint hH
  exact cfc_nonneg (R := ℂ) (A := CStarMatrix ι ι ℂ)
    (p := IsStarNormal) (a := X) (f := Complex.exp) (by
      intro z hz
      have hzreal := SpectrumRestricts.real_iff.mp hX.spectrumRestricts z hz
      rw [hzreal]
      simpa [Complex.ofReal_exp] using
        (show (0 : ℂ) ≤ (Real.exp z.re : ℂ) by
          exact_mod_cast Real.exp_nonneg z.re))

/-- The complex CFC exponential in the local Lieb functional is strictly
positive whenever the fixed matrix `H` is self-adjoint.

This closes the strict-positivity exponential domain bridge needed before a
future one-step Tropp trace-MGF theorem can take `log (E[exp X])` without a
separate regularization hypothesis. -/
theorem liebTraceCfcExp_isStrictlyPositive
    {ι : Type*} [Fintype ι] [DecidableEq ι]
    {H A : CStarMatrix ι ι ℂ} (hH : IsSelfAdjoint H) :
    IsStrictlyPositive
      (cfc (p := IsStarNormal) Complex.exp (H + CFC.log A)) := by
  exact cstarMatrix_cfc_complex_exp_isStrictlyPositive_of_isSelfAdjoint
    (H + CFC.log A) (liebTraceArgument_isSelfAdjoint hH)

/-- The trace of the complex CFC exponential in the local Lieb functional is
real-valued whenever the fixed matrix `H` is self-adjoint. -/
theorem liebTraceFunctional_trace_im_eq_zero
    {ι : Type*} [Fintype ι] [DecidableEq ι]
    {H A : CStarMatrix ι ι ℂ} (hH : IsSelfAdjoint H) :
    (cstarMatrixTrace
      (cfc (p := IsStarNormal) Complex.exp (H + CFC.log A))).im = 0 := by
  exact cstarMatrixTrace_im_eq_zero_of_isSelfAdjoint
    (IsSelfAdjoint.of_nonneg (liebTraceCfcExp_nonneg hH))

/-- The trace functional that appears in the finite-dimensional Lieb theorem.
The theorem still to be proved is concavity of this function on
`strictPositiveCStarMatrixCone` for fixed self-adjoint `H`. -/
noncomputable def liebTraceFunctional
    {ι : Type*} [Fintype ι] [DecidableEq ι]
    (H : CStarMatrix ι ι ℂ) (A : CStarMatrix ι ι ℂ) : ℝ :=
  (cstarMatrixTrace
    (cfc (p := IsStarNormal) Complex.exp (H + CFC.log A))).re

/-- The local CFC form of the Lieb functional agrees with the standard
normed-algebra exponential form used in Tropp's trace-MGF statements. -/
theorem liebTraceFunctional_eq_normedSpace_exp
    {ι : Type*} [Fintype ι] [DecidableEq ι]
    {H A : CStarMatrix ι ι ℂ} (hH : IsSelfAdjoint H) :
    liebTraceFunctional H A =
      (cstarMatrixTrace (NormedSpace.exp (H + CFC.log A))).re := by
  dsimp [liebTraceFunctional]
  exact congrArg (fun M : CStarMatrix ι ι ℂ => (cstarMatrixTrace M).re)
    (CFC.complex_exp_eq_normedSpace_exp (A := CStarMatrix ι ι ℂ)
      (p := IsStarNormal) (a := H + CFC.log A)
      (liebTraceArgument_isStarNormal hH))

/-- Normalization of the Lieb functional at `H = 0`: on the strictly positive
cone it reduces to the real part of the trace. -/
theorem liebTraceFunctional_zero_eq_trace
    {ι : Type*} [Fintype ι] [DecidableEq ι]
    {A : CStarMatrix ι ι ℂ} (hA : IsStrictlyPositive A) :
    liebTraceFunctional (0 : CStarMatrix ι ι ℂ) A =
      (cstarMatrixTrace A).re := by
  dsimp [liebTraceFunctional]
  exact congrArg (fun M : CStarMatrix ι ι ℂ => (cstarMatrixTrace M).re)
    (by
      simpa using cstarMatrix_cfc_complex_exp_log_of_isStrictlyPositive A hA)

/-- The local Lieb trace functional is nonnegative for self-adjoint `H`. -/
theorem liebTraceFunctional_nonneg
    {ι : Type*} [Fintype ι] [DecidableEq ι]
    {H A : CStarMatrix ι ι ℂ} (hH : IsSelfAdjoint H) :
    0 ≤ liebTraceFunctional H A := by
  dsimp [liebTraceFunctional]
  exact cstarMatrixTrace_re_nonneg_of_nonneg (liebTraceCfcExp_nonneg hH)

/-- Local statement shape for the finite-dimensional Lieb trace-concavity
foundation needed by the Tropp trace-MGF route.  This is a target proposition,
not a proved theorem and not a hidden hypothesis. -/
def liebTraceConcavityTarget
    {ι : Type*} [Fintype ι] [DecidableEq ι]
    (H : CStarMatrix ι ι ℂ) : Prop :=
  ConcaveOn ℝ (strictPositiveCStarMatrixCone (ι := ι))
    (liebTraceFunctional H)

/-- The `H = 0` special case of the Lieb trace-concavity target: after
`exp(log A) = A`, the functional is affine, hence concave, on the strictly
positive cone.  This is a sanity-check subcase of Lieb, not the full theorem
for arbitrary self-adjoint `H`. -/
theorem liebTraceConcavityTarget_zero
    {ι : Type*} [Fintype ι] [DecidableEq ι] :
    liebTraceConcavityTarget (0 : CStarMatrix ι ι ℂ) := by
  constructor
  · exact strictPositiveCStarMatrixCone_convex (ι := ι)
  · intro A hA B hB a b ha hb hab
    have hcomb :
        IsStrictlyPositive (a • A + b • B) :=
      (strictPositiveCStarMatrixCone_convex (ι := ι)) hA hB ha hb hab
    rw [liebTraceFunctional_zero_eq_trace (A := A) hA]
    rw [liebTraceFunctional_zero_eq_trace (A := B) hB]
    rw [liebTraceFunctional_zero_eq_trace (A := a • A + b • B) hcomb]
    have htrace :
        (cstarMatrixTrace (a • A + b • B)).re =
          a * (cstarMatrixTrace A).re + b * (cstarMatrixTrace B).re := by
      rw [cstarMatrixTrace_add]
      change
        (cstarMatrixTrace ((a : ℂ) • A)).re +
            (cstarMatrixTrace ((b : ℂ) • B)).re =
          a * (cstarMatrixTrace A).re + b * (cstarMatrixTrace B).re
      rw [cstarMatrixTrace_smul, cstarMatrixTrace_smul]
      simp
    rw [htrace]
    simp [smul_eq_mul]

/-- Conditional one-step Tropp trace-MGF domination from a supplied Lieb
trace-concavity theorem.

This theorem closes the Jensen/log-exp composition part of the Tropp route:
if `liebTraceConcavityTarget H` is available for the fixed self-adjoint matrix
`H`, then every finite self-adjoint matrix random variable `X` satisfies

`E Re tr exp(H + X) ≤ Re tr exp(H + log (E exp X))`.

The hypothesis `hLieb` is intentionally explicit.  This theorem is not a proof
of matrix Bernstein or CACM Algorithm 1 equation (2).  The unconditional wrapper
`FiniteProbability.expectationReal_trace_normed_exp_add_le` discharges the
Lieb hypothesis using the theorem proved later in this file. -/
theorem FiniteProbability.expectationReal_trace_normed_exp_add_le_of_liebTraceConcavityTarget
    {Ω : Type*} [Fintype Ω]
    {ι : Type*} [Fintype ι] [DecidableEq ι]
    (P : FiniteProbability Ω)
    {H : CStarMatrix ι ι ℂ} (hH : IsSelfAdjoint H)
    {X : Ω → CStarMatrix ι ι ℂ} (hX : ∀ ω, IsSelfAdjoint (X ω))
    (hLieb : liebTraceConcavityTarget H) :
    P.expectationReal
      (fun ω => (cstarMatrixTrace (NormedSpace.exp (H + X ω))).re) ≤
    (cstarMatrixTrace
      (NormedSpace.exp
        (H + CFC.log (P.expectationCStarMatrix
          (fun ω => NormedSpace.exp (X ω)))))).re := by
  let M : Ω → CStarMatrix ι ι ℂ := fun ω => NormedSpace.exp (X ω)
  have hM : ∀ ω, M ω ∈ strictPositiveCStarMatrixCone (ι := ι) := by
    intro ω
    dsimp [M, strictPositiveCStarMatrixCone]
    exact cstarMatrix_normedSpace_exp_isStrictlyPositive_of_isSelfAdjoint
      (X ω) (hX ω)
  have hconcave :
      ConcaveOn ℝ (strictPositiveCStarMatrixCone (ι := ι))
        (fun A =>
          (cstarMatrixTrace
            (cfc (p := IsStarNormal) Complex.exp (H + CFC.log A))).re) := by
    change liebTraceConcavityTarget H
    exact hLieb
  have hineq :=
    P.expectationReal_trace_cfc_exp_add_log_le_of_concaveOn
      (H := H) (s := strictPositiveCStarMatrixCone (ι := ι)) (M := M)
      hconcave hM
  convert hineq using 1
  · apply congrArg P.expectationReal
    funext ω
    dsimp [M]
    rw [cstarMatrix_log_normedSpace_exp_of_isSelfAdjoint (X ω) (hX ω)]
    rw [← CFC.complex_exp_eq_normedSpace_exp (A := CStarMatrix ι ι ℂ)
      (p := IsStarNormal) (a := H + X ω) ((hH.add (hX ω)).isStarNormal)]
    rfl
  · dsimp [M]
    rw [← CFC.complex_exp_eq_normedSpace_exp (A := CStarMatrix ι ι ℂ)
      (p := IsStarNormal)
      (a := H + CFC.log
        (P.expectationCStarMatrix (fun ω => NormedSpace.exp (X ω))))
      ((hH.add (cstarMatrix_log_isSelfAdjoint
        (P.expectationCStarMatrix
          (fun ω => NormedSpace.exp (X ω))))).isStarNormal)]
    rfl

/-!
## Matrix relative entropy route vocabulary

Tropp's monograph also derives Lieb's theorem through matrix relative entropy.
The following scalar/vector facts close the commutative nonnegativity step
used as a model for the later matrix proof, and the C-star definition records
the noncommutative vocabulary.  They do not prove matrix relative-entropy
nonnegativity, joint convexity, the variational formula, Lieb concavity,
trace-MGF domination, or matrix Bernstein.
-/

/-- Scalar relative entropy on positive real numbers, written as a total real
function so it can be summed over finite index types. -/
noncomputable def realRelativeEntropy (a b : ℝ) : ℝ :=
  a * (Real.log a - Real.log b) - (a - b)

/-- The normalized entropy kernel `x log x - (x - 1)`, i.e. scalar relative
entropy from `x` to `1`.  This is the function used by the finite
operator-perspective route for normalized matrix relative entropy. -/
noncomputable def realEntropyKernel (x : ℝ) : ℝ :=
  x * Real.log x - (x - 1)

theorem realRelativeEntropy_eq_mul_realEntropyKernel_mul_inv
    {a b : ℝ} (ha : 0 < a) (hb : 0 < b) :
    realRelativeEntropy a b = b * realEntropyKernel (a * b⁻¹) := by
  have hlog_ratio :
      Real.log (a * b⁻¹) = Real.log a - Real.log b := by
    rw [← div_eq_mul_inv]
    exact Real.log_div (ne_of_gt ha) (ne_of_gt hb)
  dsimp [realRelativeEntropy, realEntropyKernel]
  rw [hlog_ratio]
  field_simp [ne_of_gt hb]

@[simp]
theorem realRelativeEntropy_self (a : ℝ) :
    realRelativeEntropy a a = 0 := by
  simp [realRelativeEntropy]

/-- Scalar relative entropy is nonnegative on positive real inputs.  This is
the one-dimensional inequality behind Tropp's vector relative-entropy
nonnegativity argument. -/
theorem realRelativeEntropy_nonneg {a b : ℝ} (ha : 0 < a) (hb : 0 < b) :
    0 ≤ realRelativeEntropy a b := by
  have hba_pos : 0 < b / a := div_pos hb ha
  have hlog_le : Real.log (b / a) ≤ b / a - 1 :=
    Real.log_le_sub_one_of_pos hba_pos
  have hneg : 1 - b / a ≤ -Real.log (b / a) := by
    linarith
  have hmul : a * (1 - b / a) ≤ a * (-Real.log (b / a)) :=
    mul_le_mul_of_nonneg_left hneg ha.le
  have hleft_eq : a * (1 - b / a) = a - b := by
    field_simp [ne_of_gt ha]
  have hlogba : Real.log (b / a) = Real.log b - Real.log a :=
    Real.log_div (ne_of_gt hb) (ne_of_gt ha)
  have hneglog : -Real.log (b / a) = Real.log a - Real.log b := by
    rw [hlogba]
    ring
  have hcore : a - b ≤ a * (Real.log a - Real.log b) := by
    simpa [hleft_eq, hneglog] using hmul
  dsimp [realRelativeEntropy]
  linarith

/-- Finite-vector relative entropy, the commutative model for matrix relative
entropy in Tropp's proof route. -/
noncomputable def finiteRealRelativeEntropy
    {ι : Type*} [Fintype ι] (a b : ι → ℝ) : ℝ :=
  ∑ i, realRelativeEntropy (a i) (b i)

@[simp]
theorem finiteRealRelativeEntropy_self
    {ι : Type*} [Fintype ι] (a : ι → ℝ) :
    finiteRealRelativeEntropy a a = 0 := by
  simp [finiteRealRelativeEntropy]

/-- Finite-vector relative entropy is nonnegative when both vectors are
coordinatewise positive. -/
theorem finiteRealRelativeEntropy_nonneg
    {ι : Type*} [Fintype ι] {a b : ι → ℝ}
    (ha : ∀ i, 0 < a i) (hb : ∀ i, 0 < b i) :
    0 ≤ finiteRealRelativeEntropy a b := by
  exact Finset.sum_nonneg
    (fun i _ => realRelativeEntropy_nonneg (ha i) (hb i))

/-- Finite log-sum inequality for strictly positive real vectors.

This is the commutative Jensen layer behind the joint-convexity route for
relative entropy.  It is a local finite-dimensional theorem, not an assumption
of the later noncommutative matrix joint-convexity target. -/
theorem finite_log_sum_inequality
    {ι : Type*} [Fintype ι] [Nonempty ι]
    {p q : ι → ℝ} (hp : ∀ i, 0 < p i) (hq : ∀ i, 0 < q i) :
    (∑ i, p i) * Real.log ((∑ i, p i) / (∑ i, q i)) ≤
      ∑ i, p i * Real.log (p i / q i) := by
  classical
  let P : ℝ := ∑ i, p i
  let Q : ℝ := ∑ i, q i
  have hPpos : 0 < P := by
    dsimp [P]
    exact Finset.sum_pos (fun i _ => hp i) Finset.univ_nonempty
  have hQpos : 0 < Q := by
    dsimp [Q]
    exact Finset.sum_pos (fun i _ => hq i) Finset.univ_nonempty
  let w : ι → ℝ := fun i => q i / Q
  let r : ι → ℝ := fun i => p i / q i
  have hw_nonneg : ∀ i ∈ (Finset.univ : Finset ι), 0 ≤ w i := by
    intro i _
    exact div_nonneg (le_of_lt (hq i)) (le_of_lt hQpos)
  have hw_sum : ∑ i ∈ (Finset.univ : Finset ι), w i = 1 := by
    change ∑ i, q i / Q = 1
    rw [← Finset.sum_div]
    exact div_self (ne_of_gt hQpos)
  have hr_mem : ∀ i ∈ (Finset.univ : Finset ι), r i ∈ Set.Ici (0 : ℝ) := by
    intro i _
    exact le_of_lt (div_pos (hp i) (hq i))
  have hj := Real.convexOn_mul_log.map_sum_le
    (t := (Finset.univ : Finset ι)) (w := w) (p := r)
    hw_nonneg hw_sum hr_mem
  have hsum_wr :
      (∑ i ∈ (Finset.univ : Finset ι), w i • r i) = P / Q := by
    change ∑ i, (q i / Q) * (p i / q i) = P / Q
    calc
      ∑ i, (q i / Q) * (p i / q i) = ∑ i, p i / Q := by
        apply Finset.sum_congr rfl
        intro i _
        field_simp [ne_of_gt (hq i), ne_of_gt hQpos]
      _ = P / Q := by
        rw [← Finset.sum_div]
  have hsum_rhs :
      (∑ i ∈ (Finset.univ : Finset ι), w i • (r i * Real.log (r i))) =
        (1 / Q) * (∑ i, p i * Real.log (p i / q i)) := by
    change ∑ i, (q i / Q) * ((p i / q i) * Real.log (p i / q i)) =
      (1 / Q) * (∑ i, p i * Real.log (p i / q i))
    rw [Finset.mul_sum]
    apply Finset.sum_congr rfl
    intro i _
    field_simp [ne_of_gt (hq i), ne_of_gt hQpos]
  rw [hsum_wr, hsum_rhs] at hj
  have hmul := mul_le_mul_of_nonneg_left hj (le_of_lt hQpos)
  have hleft :
      Q * (P / Q * Real.log (P / Q)) = P * Real.log (P / Q) := by
    field_simp [ne_of_gt hQpos]
  have hright :
      Q * ((1 / Q) * (∑ i, p i * Real.log (p i / q i))) =
        ∑ i, p i * Real.log (p i / q i) := by
    field_simp [ne_of_gt hQpos]
  rw [hleft, hright] at hmul
  simpa [P, Q] using hmul

/-- Positive-weight scalar joint convexity for the local real relative entropy.

The statement is homogeneous in the two weights, so no `a + b = 1`
normalization is needed in this positive-weight version. -/
theorem realRelativeEntropy_jointConvex_of_pos_weights
    {x y a b α β : ℝ}
    (hx : 0 < x) (hy : 0 < y) (ha : 0 < a) (hb : 0 < b)
    (hα : 0 < α) (hβ : 0 < β) :
    realRelativeEntropy (α * x + β * y) (α * a + β * b) ≤
      α * realRelativeEntropy x a + β * realRelativeEntropy y b := by
  classical
  let p : Fin 2 → ℝ := fun i => if i = 0 then α * x else β * y
  let q : Fin 2 → ℝ := fun i => if i = 0 then α * a else β * b
  have hp : ∀ i, 0 < p i := by
    intro i
    fin_cases i <;> simp [p, mul_pos hα hx, mul_pos hβ hy]
  have hq : ∀ i, 0 < q i := by
    intro i
    fin_cases i <;> simp [q, mul_pos hα ha, mul_pos hβ hb]
  have hlog := finite_log_sum_inequality (p := p) (q := q) hp hq
  have hp_sum : (∑ i, p i) = α * x + β * y := by
    rw [Fin.sum_univ_two]
    simp [p]
  have hq_sum : (∑ i, q i) = α * a + β * b := by
    rw [Fin.sum_univ_two]
    simp [q]
  have hterm0 : (α * x) / (α * a) = x / a := by
    field_simp [ne_of_gt hα, ne_of_gt ha]
  have hterm1 : (β * y) / (β * b) = y / b := by
    field_simp [ne_of_gt hβ, ne_of_gt hb]
  have hrhs : (∑ i, p i * Real.log (p i / q i)) =
      α * x * Real.log (x / a) + β * y * Real.log (y / b) := by
    rw [Fin.sum_univ_two]
    simp [p, q, hterm0, hterm1]
  rw [hp_sum, hq_sum, hrhs] at hlog
  have hPpos : 0 < α * x + β * y :=
    add_pos (mul_pos hα hx) (mul_pos hβ hy)
  have hQpos : 0 < α * a + β * b :=
    add_pos (mul_pos hα ha) (mul_pos hβ hb)
  have hlogP : Real.log ((α * x + β * y) / (α * a + β * b)) =
      Real.log (α * x + β * y) - Real.log (α * a + β * b) :=
    Real.log_div (ne_of_gt hPpos) (ne_of_gt hQpos)
  have hlogx : Real.log (x / a) = Real.log x - Real.log a :=
    Real.log_div (ne_of_gt hx) (ne_of_gt ha)
  have hlogy : Real.log (y / b) = Real.log y - Real.log b :=
    Real.log_div (ne_of_gt hy) (ne_of_gt hb)
  dsimp [realRelativeEntropy]
  rw [← hlogP, ← hlogx, ← hlogy]
  nlinarith [hlog]

/-- Scalar joint convexity for the local real relative entropy. -/
theorem realRelativeEntropy_jointConvex
    {x y a b α β : ℝ}
    (hx : 0 < x) (hy : 0 < y) (ha : 0 < a) (hb : 0 < b)
    (hα : 0 ≤ α) (hβ : 0 ≤ β) (hαβ : α + β = 1) :
    realRelativeEntropy (α * x + β * y) (α * a + β * b) ≤
      α * realRelativeEntropy x a + β * realRelativeEntropy y b := by
  by_cases hαzero : α = 0
  · have hβone : β = 1 := by linarith
    subst α
    subst β
    simp [realRelativeEntropy]
  by_cases hβzero : β = 0
  · have hαone : α = 1 := by linarith
    subst α
    subst β
    simp [realRelativeEntropy]
  have hαpos : 0 < α := lt_of_le_of_ne hα (Ne.symm hαzero)
  have hβpos : 0 < β := lt_of_le_of_ne hβ (Ne.symm hβzero)
  exact realRelativeEntropy_jointConvex_of_pos_weights
    hx hy ha hb hαpos hβpos

/-- Finite-vector joint convexity for the local real relative entropy.  This
is the commutative finite-dimensional counterpart of the noncommutative
matrix relative-entropy joint-convexity theorem still open in the bottleneck
ledger. -/
theorem finiteRealRelativeEntropy_jointConvex
    {ι : Type*} [Fintype ι]
    {x y a b : ι → ℝ} {α β : ℝ}
    (hx : ∀ i, 0 < x i) (hy : ∀ i, 0 < y i)
    (ha : ∀ i, 0 < a i) (hb : ∀ i, 0 < b i)
    (hα : 0 ≤ α) (hβ : 0 ≤ β) (hαβ : α + β = 1) :
    finiteRealRelativeEntropy (fun i => α * x i + β * y i)
        (fun i => α * a i + β * b i) ≤
      α * finiteRealRelativeEntropy x a +
        β * finiteRealRelativeEntropy y b := by
  classical
  dsimp [finiteRealRelativeEntropy]
  calc
    ∑ i, realRelativeEntropy (α * x i + β * y i)
        (α * a i + β * b i)
        ≤ ∑ i, (α * realRelativeEntropy (x i) (a i) +
            β * realRelativeEntropy (y i) (b i)) := by
          apply Finset.sum_le_sum
          intro i _
          exact realRelativeEntropy_jointConvex
            (hx i) (hy i) (ha i) (hb i) hα hβ hαβ
    _ = α * (∑ i, realRelativeEntropy (x i) (a i)) +
          β * (∑ i, realRelativeEntropy (y i) (b i)) := by
          rw [Finset.sum_add_distrib, Finset.mul_sum, Finset.mul_sum]

/-- Trace expansion for a diagonal--overlap--diagonal product.

This is the finite-dimensional algebraic core behind Tropp's generalized
Klein expansion: after diagonalizing two Hermitian matrices, their mixed trace
products reduce to scalar weights times squared overlaps of eigenvectors. -/
theorem matrixTrace_diagonal_mul_mul_diagonal_mul_star
    {ι : Type*} [Fintype ι] [DecidableEq ι]
    (D E : ι → ℂ) (W : Matrix ι ι ℂ) :
    Matrix.trace (Matrix.diagonal D * W * Matrix.diagonal E * star W) =
      ∑ j : ι, ∑ k : ι, D j * W j k * E k * star (W j k) := by
  rw [Matrix.trace]
  apply Finset.sum_congr rfl
  intro i _hi
  simp [Matrix.diag, Matrix.mul_apply, Matrix.conjTranspose_apply,
    Matrix.star_eq_conjTranspose, Matrix.diagonal_apply, Finset.sum_ite_eq',
    Finset.sum_ite_eq]

/-- Real-part form of the diagonal--overlap trace expansion for finite sums of
separated scalar kernels. -/
theorem matrixTrace_sum_diagonal_mul_mul_diagonal_mul_star_re
    {ι κ : Type*} [Fintype ι] [DecidableEq ι] [Fintype κ]
    (f g : κ → ι → ℝ) (W : Matrix ι ι ℂ) :
    (∑ r : κ, Matrix.trace
      (Matrix.diagonal (fun j : ι => (f r j : ℂ)) * W *
        Matrix.diagonal (fun k : ι => (g r k : ℂ)) * star W)).re =
      ∑ j : ι, ∑ k : ι,
        (∑ r : κ, f r j * g r k) * Complex.normSq (W j k) := by
  simp_rw [matrixTrace_diagonal_mul_mul_diagonal_mul_star]
  rw [Complex.re_sum]
  simp_rw [Complex.re_sum]
  rw [Finset.sum_comm]
  apply Finset.sum_congr rfl
  intro j _hj
  rw [Finset.sum_comm]
  apply Finset.sum_congr rfl
  intro k _hk
  rw [Finset.sum_mul Finset.univ]
  apply Finset.sum_congr rfl
  intro r _hr
  simp [Complex.normSq, mul_assoc, mul_left_comm, mul_comm]
  ring

/-- Spectral-overlap expansion for traces of products of Hermitian continuous
functional calculi.

For Hermitian matrices `A` and `H`, diagonalize both matrices and let
`W = U_Aᴴ U_H` be the unitary overlap matrix between their eigenbases.  Then a
finite sum of mixed traces has real part

`sum_j sum_k (sum_r f_r(lambda_j) g_r(mu_k)) |W_jk|^2`.

This closes the source-aligned spectral expansion dependency in Tropp's
generalized Klein proof route.  The remaining Klein step is the scalar
first-order convexity kernel specialized to `phi(t)=t log t - t`. -/
theorem matrixTrace_sum_hermitianCfc_mul_cfc_re
    {ι κ : Type*} [Fintype ι] [DecidableEq ι] [Fintype κ]
    {A H : Matrix ι ι ℂ} (hA : Matrix.IsHermitian A)
    (hH : Matrix.IsHermitian H) (f g : κ → ℝ → ℝ) :
    (∑ r : κ, Matrix.trace (hA.cfc (f r) * hH.cfc (g r))).re =
      ∑ j : ι, ∑ k : ι,
        (∑ r : κ, f r (hA.eigenvalues j) * g r (hH.eigenvalues k)) *
          Complex.normSq
            (((star (hA.eigenvectorUnitary : Matrix ι ι ℂ)) *
              (hH.eigenvectorUnitary : Matrix ι ι ℂ)) j k) := by
  let W : Matrix ι ι ℂ :=
    (star (hA.eigenvectorUnitary : Matrix ι ι ℂ)) *
      (hH.eigenvectorUnitary : Matrix ι ι ℂ)
  have htrace : ∀ r : κ,
      Matrix.trace (hA.cfc (f r) * hH.cfc (g r)) =
        Matrix.trace
          (Matrix.diagonal (fun j : ι => (f r (hA.eigenvalues j) : ℂ)) *
            W * Matrix.diagonal
              (fun k : ι => (g r (hH.eigenvalues k) : ℂ)) * star W) := by
    intro r
    rw [Matrix.IsHermitian.cfc, Matrix.IsHermitian.cfc]
    simp only [Unitary.conjStarAlgAut_apply]
    let U : Matrix ι ι ℂ := hA.eigenvectorUnitary
    let V : Matrix ι ι ℂ := hH.eigenvectorUnitary
    let D : Matrix ι ι ℂ :=
      Matrix.diagonal (RCLike.ofReal ∘ f r ∘ hA.eigenvalues)
    let E : Matrix ι ι ℂ :=
      Matrix.diagonal (RCLike.ofReal ∘ g r ∘ hH.eigenvalues)
    change Matrix.trace ((U * D * star U) * (V * E * star V)) =
      Matrix.trace (D * (star U * V) * E * star (star U * V))
    calc
      Matrix.trace (U * D * star U * (V * E * star V))
          = Matrix.trace (U * (D * (star U * (V * E * star V)))) := by
            exact congrArg Matrix.trace (by simp [Matrix.mul_assoc])
      _ = Matrix.trace ((D * (star U * (V * E * star V))) * U) := by
            exact Matrix.trace_mul_comm U (D * (star U * (V * E * star V)))
      _ = Matrix.trace (D * (star U * V) * E * (star V * U)) := by
            congr 1
            noncomm_ring
      _ = Matrix.trace (D * (star U * V) * E * star (star U * V)) := by
            have hWstar : star (star U * V) = star V * U := by
              simp [Matrix.star_eq_conjTranspose]
            rw [hWstar]
  simp_rw [htrace]
  exact matrixTrace_sum_diagonal_mul_mul_diagonal_mul_star_re
    (fun r j => f r (hA.eigenvalues j))
    (fun r k => g r (hH.eigenvalues k)) W

/-- Single-product version of the Hermitian CFC spectral-overlap trace
expansion. -/
theorem matrixTrace_hermitianCfc_mul_cfc_re
    {ι : Type*} [Fintype ι] [DecidableEq ι]
    {A H : Matrix ι ι ℂ} (hA : Matrix.IsHermitian A)
    (hH : Matrix.IsHermitian H) (f g : ℝ → ℝ) :
    (Matrix.trace (hA.cfc f * hH.cfc g)).re =
      ∑ j : ι, ∑ k : ι,
        (f (hA.eigenvalues j) * g (hH.eigenvalues k)) *
          Complex.normSq
            (((star (hA.eigenvectorUnitary : Matrix ι ι ℂ)) *
              (hH.eigenvectorUnitary : Matrix ι ι ℂ)) j k) := by
  let f' : Unit → ℝ → ℝ := fun _ => f
  let g' : Unit → ℝ → ℝ := fun _ => g
  have h :=
    matrixTrace_sum_hermitianCfc_mul_cfc_re
      (A := A) (H := H) hA hH f' g'
  simpa [f', g'] using h

/-- Nonnegative-kernel corollary of the Hermitian CFC trace-product expansion.

If the separated scalar kernel has nonnegative sum at every eigenvalue pair,
then the real part of the corresponding finite sum of mixed CFC traces is
nonnegative.  This is the weighted-squared-overlap positivity step in Tropp's
generalized Klein proof route. -/
theorem matrixTrace_sum_hermitianCfc_mul_cfc_nonneg_of_kernel_nonneg
    {ι κ : Type*} [Fintype ι] [DecidableEq ι] [Fintype κ]
    {A H : Matrix ι ι ℂ} (hA : Matrix.IsHermitian A)
    (hH : Matrix.IsHermitian H) (f g : κ → ℝ → ℝ)
    (hkernel : ∀ a b : ℝ, 0 ≤ ∑ r : κ, f r a * g r b) :
    0 ≤ (∑ r : κ, Matrix.trace (hA.cfc (f r) * hH.cfc (g r))).re := by
  rw [matrixTrace_sum_hermitianCfc_mul_cfc_re hA hH f g]
  apply Finset.sum_nonneg
  intro j _hj
  apply Finset.sum_nonneg
  intro k _hk
  exact mul_nonneg
    (hkernel (hA.eigenvalues j) (hH.eigenvalues k))
    (Complex.normSq_nonneg _)

/-- Eigenvalue-local version of the nonnegative-kernel corollary.

This is useful when the scalar kernel is known only on the positive spectra of
the two Hermitian matrices, as in the entropy kernel `t log t - t`. -/
theorem matrixTrace_sum_hermitianCfc_mul_cfc_nonneg_of_eigen_kernel_nonneg
    {ι κ : Type*} [Fintype ι] [DecidableEq ι] [Fintype κ]
    {A H : Matrix ι ι ℂ} (hA : Matrix.IsHermitian A)
    (hH : Matrix.IsHermitian H) (f g : κ → ℝ → ℝ)
    (hkernel : ∀ j k : ι,
      0 ≤ ∑ r : κ, f r (hA.eigenvalues j) * g r (hH.eigenvalues k)) :
    0 ≤ (∑ r : κ, Matrix.trace (hA.cfc (f r) * hH.cfc (g r))).re := by
  rw [matrixTrace_sum_hermitianCfc_mul_cfc_re hA hH f g]
  apply Finset.sum_nonneg
  intro j _hj
  apply Finset.sum_nonneg
  intro k _hk
  exact mul_nonneg (hkernel j k) (Complex.normSq_nonneg _)

/-- Four-term Hermitian CFC trace inequality from a global scalar first-order
kernel inequality.

The displayed trace is the separated-kernel expansion of
`tr(phi(A)) - tr(phi(H)) - tr(psi(H) * (A - H))`.  This theorem deliberately
keeps it in separated CFC form; the remaining bridge to the compact
`CStarMatrix` logarithm statement is tracked separately in the bottleneck
ledger. -/
theorem matrixTrace_hermitianCfc_firstOrderKernel_sum_nonneg
    {ι : Type*} [Fintype ι] [DecidableEq ι]
    {A H : Matrix ι ι ℂ} (hA : Matrix.IsHermitian A)
    (hH : Matrix.IsHermitian H) (φ ψ : ℝ → ℝ)
    (hscalar : ∀ a b : ℝ, 0 ≤ φ a - φ b - ψ b * (a - b)) :
    0 ≤
      (Matrix.trace (hA.cfc φ * hH.cfc (fun _ : ℝ => 1)) +
        Matrix.trace (hA.cfc (fun _ : ℝ => -1) * hH.cfc φ) +
        Matrix.trace (hA.cfc (fun a : ℝ => -a) * hH.cfc ψ) +
        Matrix.trace (hA.cfc (fun _ : ℝ => 1) *
          hH.cfc (fun b : ℝ => ψ b * b))).re := by
  let f : Fin 4 → ℝ → ℝ := fun r =>
    if r = 0 then φ
    else if r = 1 then (fun _ : ℝ => -1)
    else if r = 2 then (fun a : ℝ => -a)
    else (fun _ : ℝ => 1)
  let g : Fin 4 → ℝ → ℝ := fun r =>
    if r = 0 then (fun _ : ℝ => 1)
    else if r = 1 then φ
    else if r = 2 then ψ
    else (fun b : ℝ => ψ b * b)
  have hkernel : ∀ a b : ℝ, 0 ≤ ∑ r : Fin 4, f r a * g r b := by
    intro a b
    have h := hscalar a b
    convert h using 1
    rw [Fin.sum_univ_four]
    simp [f, g]
    ring
  have hmain :=
    matrixTrace_sum_hermitianCfc_mul_cfc_nonneg_of_kernel_nonneg
      hA hH f g hkernel
  convert hmain using 1
  rw [Fin.sum_univ_four]
  simp [f, g]

/-- Positive-eigenvalue version of the four-term Hermitian CFC trace
first-order kernel inequality. -/
theorem matrixTrace_hermitianCfc_firstOrderKernel_sum_nonneg_of_eigen
    {ι : Type*} [Fintype ι] [DecidableEq ι]
    {A H : Matrix ι ι ℂ} (hA : Matrix.IsHermitian A)
    (hH : Matrix.IsHermitian H) (φ ψ : ℝ → ℝ)
    (hscalar :
      ∀ a b : ℝ,
        0 < a → 0 < b → 0 ≤ φ a - φ b - ψ b * (a - b))
    (hApos : ∀ j : ι, 0 < hA.eigenvalues j)
    (hHpos : ∀ k : ι, 0 < hH.eigenvalues k) :
    0 ≤
      (Matrix.trace (hA.cfc φ * hH.cfc (fun _ : ℝ => 1)) +
        Matrix.trace (hA.cfc (fun _ : ℝ => -1) * hH.cfc φ) +
        Matrix.trace (hA.cfc (fun a : ℝ => -a) * hH.cfc ψ) +
        Matrix.trace (hA.cfc (fun _ : ℝ => 1) *
          hH.cfc (fun b : ℝ => ψ b * b))).re := by
  let f : Fin 4 → ℝ → ℝ := fun r =>
    if r = 0 then φ
    else if r = 1 then (fun _ : ℝ => -1)
    else if r = 2 then (fun a : ℝ => -a)
    else (fun _ : ℝ => 1)
  let g : Fin 4 → ℝ → ℝ := fun r =>
    if r = 0 then (fun _ : ℝ => 1)
    else if r = 1 then φ
    else if r = 2 then ψ
    else (fun b : ℝ => ψ b * b)
  have hkernel : ∀ j k : ι,
      0 ≤ ∑ r : Fin 4, f r (hA.eigenvalues j) * g r (hH.eigenvalues k) := by
    intro j k
    have h :=
      hscalar (hA.eigenvalues j) (hH.eigenvalues k) (hApos j) (hHpos k)
    convert h using 1
    rw [Fin.sum_univ_four]
    simp [f, g]
    ring
  have hmain :=
    matrixTrace_sum_hermitianCfc_mul_cfc_nonneg_of_eigen_kernel_nonneg
      hA hH f g hkernel
  convert hmain using 1
  rw [Fin.sum_univ_four]
  simp [f, g]

/-- Scalar first-order convexity kernel for `phi(t) = t log t - t` on the
positive real line. -/
theorem realEntropy_firstOrderKernel_nonneg
    {a b : ℝ} (ha : 0 < a) (hb : 0 < b) :
    0 ≤ (a * Real.log a - a) - (b * Real.log b - b) -
      Real.log b * (a - b) := by
  have h := realRelativeEntropy_nonneg ha hb
  dsimp [realRelativeEntropy] at h
  linarith

/-- Hermitian CFC entropy first-order trace inequality in separated-kernel
form.

This closes the scalar first-order convexity specialization in Tropp's
generalized Klein route for Hermitian matrices with positive eigenvalues.  It
does not yet identify this separated expression with the compact complex
`CStarMatrix` logarithm statement. -/
theorem matrixTrace_hermitianCfc_entropy_firstOrder_sum_nonneg
    {ι : Type*} [Fintype ι] [DecidableEq ι]
    {A H : Matrix ι ι ℂ} (hA : Matrix.IsHermitian A)
    (hH : Matrix.IsHermitian H)
    (hApos : ∀ j : ι, 0 < hA.eigenvalues j)
    (hHpos : ∀ k : ι, 0 < hH.eigenvalues k) :
    0 ≤
      (Matrix.trace
          (hA.cfc (fun a : ℝ => a * Real.log a - a) *
            hH.cfc (fun _ : ℝ => 1)) +
        Matrix.trace
          (hA.cfc (fun _ : ℝ => -1) *
            hH.cfc (fun b : ℝ => b * Real.log b - b)) +
        Matrix.trace
          (hA.cfc (fun a : ℝ => -a) *
            hH.cfc (fun b : ℝ => Real.log b)) +
        Matrix.trace
          (hA.cfc (fun _ : ℝ => 1) *
            hH.cfc (fun b : ℝ => Real.log b * b))).re := by
  exact matrixTrace_hermitianCfc_firstOrderKernel_sum_nonneg_of_eigen
    hA hH
    (fun a : ℝ => a * Real.log a - a)
    (fun b : ℝ => Real.log b)
    (fun a b ha hb => realEntropy_firstOrderKernel_nonneg ha hb)
    hApos hHpos

/-- Hermitian CFC sends the constant-one function to the identity matrix. -/
theorem matrix_isHermitian_cfc_const_one
    {ι : Type*} [Fintype ι] [DecidableEq ι]
    {A : Matrix ι ι ℂ} (hA : Matrix.IsHermitian A) :
    hA.cfc (fun _ : ℝ => 1) = 1 := by
  rw [Matrix.IsHermitian.cfc]
  change
    ((Unitary.conjStarAlgAut ℂ (Matrix ι ι ℂ)) hA.eigenvectorUnitary)
      (Matrix.diagonal (fun _ : ι => (1 : ℂ))) = 1
  rw [Matrix.diagonal_one]
  exact map_one _

/-- Hermitian CFC sends the constant negative-one function to `-1`. -/
theorem matrix_isHermitian_cfc_const_neg_one
    {ι : Type*} [Fintype ι] [DecidableEq ι]
    {A : Matrix ι ι ℂ} (hA : Matrix.IsHermitian A) :
    hA.cfc (fun _ : ℝ => -1) = -1 := by
  rw [Matrix.IsHermitian.cfc]
  have hdiag :
      Matrix.diagonal (RCLike.ofReal ∘ (fun _ : ℝ => -1) ∘ hA.eigenvalues) =
        Matrix.diagonal (fun _ : ι => (-1 : ℂ)) := by
    ext i j
    by_cases h : i = j
    · subst h
      simp [Matrix.diagonal]
    · simp [Matrix.diagonal, h]
  rw [hdiag]
  rw [show Matrix.diagonal (fun _ : ι => (-1 : ℂ)) =
      -(1 : Matrix ι ι ℂ) by
        ext i j
        by_cases h : i = j
        · subst h
          simp [Matrix.diagonal]
        · simp [Matrix.diagonal, h]]
  rw [map_neg, map_one]

/-- Hermitian CFC sends `a ↦ -a` to matrix negation. -/
theorem matrix_isHermitian_cfc_neg_id
    {ι : Type*} [Fintype ι] [DecidableEq ι]
    {A : Matrix ι ι ℂ} (hA : Matrix.IsHermitian A) :
    hA.cfc (fun a : ℝ => -a) = -A := by
  rw [Matrix.IsHermitian.cfc]
  let τ := ((Unitary.conjStarAlgAut ℂ (Matrix ι ι ℂ)) hA.eigenvectorUnitary)
  let D : Matrix ι ι ℂ :=
    Matrix.diagonal (fun i : ι => (hA.eigenvalues i : ℂ))
  have hdiag :
      Matrix.diagonal (RCLike.ofReal ∘ (fun a : ℝ => -a) ∘ hA.eigenvalues) =
        -D := by
    ext i j
    by_cases h : i = j
    · subst h
      simp [D, Matrix.diagonal]
    · simp [D, Matrix.diagonal, h]
  rw [hdiag]
  change τ (-D) = -A
  rw [hA.spectral_theorem]
  change τ (-D) = -τ D
  rw [map_neg]

/-- Hermitian CFC sends the identity function to the source matrix. -/
theorem matrix_isHermitian_cfc_id
    {ι : Type*} [Fintype ι] [DecidableEq ι]
    {A : Matrix ι ι ℂ} (hA : Matrix.IsHermitian A) :
    hA.cfc (fun a : ℝ => a) = A := by
  rw [Matrix.IsHermitian.cfc]
  let τ := ((Unitary.conjStarAlgAut ℂ (Matrix ι ι ℂ)) hA.eigenvectorUnitary)
  let D : Matrix ι ι ℂ :=
    Matrix.diagonal (fun i : ι => (hA.eigenvalues i : ℂ))
  change τ D = A
  exact hA.spectral_theorem.symm

/-- Hermitian CFC depends only on the values of the scalar function on the
chosen eigenvalue list. -/
theorem matrix_isHermitian_cfc_congr_eigen
    {ι : Type*} [Fintype ι] [DecidableEq ι]
    {A : Matrix ι ι ℂ} (hA : Matrix.IsHermitian A)
    {f g : ℝ → ℝ}
    (hfg : ∀ i : ι, f (hA.eigenvalues i) = g (hA.eigenvalues i)) :
    hA.cfc f = hA.cfc g := by
  rw [Matrix.IsHermitian.cfc, Matrix.IsHermitian.cfc]
  congr 1
  ext i j
  by_cases hij : i = j
  · subst hij
    simp [Matrix.diagonal, hfg]
  · simp [Matrix.diagonal, hij]

/-- Hermitian CFC is multiplicative for scalar products on a fixed finite
Hermitian matrix. -/
theorem matrix_isHermitian_cfc_mul
    {ι : Type*} [Fintype ι] [DecidableEq ι]
    {A : Matrix ι ι ℂ} (hA : Matrix.IsHermitian A)
    (f g : ℝ → ℝ) :
    hA.cfc (fun a : ℝ => f a * g a) =
      hA.cfc f * hA.cfc g := by
  rw [Matrix.IsHermitian.cfc, Matrix.IsHermitian.cfc, Matrix.IsHermitian.cfc]
  let τ := ((Unitary.conjStarAlgAut ℂ (Matrix ι ι ℂ)) hA.eigenvectorUnitary)
  let Dfg : Matrix ι ι ℂ :=
    Matrix.diagonal
      (RCLike.ofReal ∘ (fun a : ℝ => f a * g a) ∘ hA.eigenvalues)
  let Df : Matrix ι ι ℂ :=
    Matrix.diagonal (RCLike.ofReal ∘ f ∘ hA.eigenvalues)
  let Dg : Matrix ι ι ℂ :=
    Matrix.diagonal (RCLike.ofReal ∘ g ∘ hA.eigenvalues)
  change τ Dfg = τ Df * τ Dg
  rw [← map_mul]
  congr 1
  rw [Matrix.diagonal_mul_diagonal]
  ext i j
  by_cases hij : i = j
  · subst hij
    simp [Dfg, Matrix.diagonal]
  · simp [Dfg, Matrix.diagonal, hij]

/-- Powers of a scalar function pass through finite Hermitian CFC. -/
theorem matrix_isHermitian_cfc_fun_pow_nat
    {ι : Type*} [Fintype ι] [DecidableEq ι]
    {A : Matrix ι ι ℂ} (hA : Matrix.IsHermitian A)
    (f : ℝ → ℝ) (n : ℕ) :
    hA.cfc (fun a : ℝ => (f a) ^ n) = (hA.cfc f) ^ n := by
  induction n with
  | zero =>
      simpa using matrix_isHermitian_cfc_const_one hA
  | succ n ih =>
      calc
        hA.cfc (fun a : ℝ => (f a) ^ (n + 1)) =
            hA.cfc (fun a : ℝ => (f a) ^ n * f a) := by
              apply matrix_isHermitian_cfc_congr_eigen hA
              intro i
              rw [pow_succ]
        _ = hA.cfc (fun a : ℝ => (f a) ^ n) * hA.cfc f := by
              exact matrix_isHermitian_cfc_mul hA
                (fun a : ℝ => (f a) ^ n) f
        _ = (hA.cfc f) ^ (n + 1) := by
              rw [ih, pow_succ]

/-- For a positive-definite matrix, finite Hermitian CFC of scalar inverse is
the ordinary nonsingular inverse. -/
theorem matrix_isHermitian_cfc_inv_of_posDef
    {ι : Type*} [Fintype ι] [DecidableEq ι]
    {A : Matrix ι ι ℂ} (hA : Matrix.PosDef A) :
    hA.isHermitian.cfc (fun a : ℝ => a⁻¹) = A⁻¹ := by
  have hleft : hA.isHermitian.cfc (fun a : ℝ => a⁻¹) * A = 1 := by
    calc
      hA.isHermitian.cfc (fun a : ℝ => a⁻¹) * A =
          hA.isHermitian.cfc (fun a : ℝ => a⁻¹) *
            hA.isHermitian.cfc (fun a : ℝ => a) := by
            exact congrArg
              (fun M => hA.isHermitian.cfc (fun a : ℝ => a⁻¹) * M)
              (matrix_isHermitian_cfc_id hA.isHermitian).symm
      _ = hA.isHermitian.cfc (fun a : ℝ => a⁻¹ * a) := by
            rw [← matrix_isHermitian_cfc_mul hA.isHermitian
              (fun a : ℝ => a⁻¹) (fun a : ℝ => a)]
      _ = hA.isHermitian.cfc (fun _ : ℝ => 1) := by
            apply matrix_isHermitian_cfc_congr_eigen hA.isHermitian
            intro i
            field_simp [ne_of_gt (hA.eigenvalues_pos i)]
      _ = 1 := matrix_isHermitian_cfc_const_one hA.isHermitian
  exact (Matrix.inv_eq_left_inv hleft).symm

/-- Positive-definite right inverse powers as a single Hermitian CFC factor. -/
theorem matrix_posDef_mul_inv_pow_eq_cfc
    {ι : Type*} [Fintype ι] [DecidableEq ι]
    {A : Matrix ι ι ℂ} (hA : Matrix.PosDef A) (n : ℕ) :
    A * (A⁻¹) ^ n =
      hA.isHermitian.cfc (fun a : ℝ => a * (a⁻¹) ^ n) := by
  calc
    A * (A⁻¹) ^ n =
        hA.isHermitian.cfc (fun a : ℝ => a) *
          (hA.isHermitian.cfc (fun a : ℝ => a⁻¹)) ^ n := by
          rw [matrix_isHermitian_cfc_id hA.isHermitian,
            matrix_isHermitian_cfc_inv_of_posDef hA]
    _ = hA.isHermitian.cfc (fun a : ℝ => a) *
          hA.isHermitian.cfc (fun a : ℝ => (a⁻¹) ^ n) := by
          rw [matrix_isHermitian_cfc_fun_pow_nat hA.isHermitian
            (fun a : ℝ => a⁻¹) n]
    _ = hA.isHermitian.cfc (fun a : ℝ => a * (a⁻¹) ^ n) := by
          rw [← matrix_isHermitian_cfc_mul hA.isHermitian]

/-- Hermitian CFC form of `phi(a) = a log a - a`. -/
theorem matrix_isHermitian_cfc_entropy
    {ι : Type*} [Fintype ι] [DecidableEq ι]
    {A : Matrix ι ι ℂ} (hA : Matrix.IsHermitian A) :
    hA.cfc (fun a : ℝ => a * Real.log a - a) =
      A * hA.cfc Real.log - A := by
  rw [Matrix.IsHermitian.cfc]
  rw [Matrix.IsHermitian.cfc]
  let τ := ((Unitary.conjStarAlgAut ℂ (Matrix ι ι ℂ)) hA.eigenvectorUnitary)
  let Did : Matrix ι ι ℂ :=
    Matrix.diagonal (fun i : ι => (hA.eigenvalues i : ℂ))
  let Dlog : Matrix ι ι ℂ :=
    Matrix.diagonal (fun i : ι => (Real.log (hA.eigenvalues i) : ℂ))
  let Dφ : Matrix ι ι ℂ :=
    Matrix.diagonal
      (fun i : ι => ((hA.eigenvalues i * Real.log (hA.eigenvalues i) -
        hA.eigenvalues i : ℝ) : ℂ))
  change τ Dφ = A * τ Dlog - A
  rw [hA.spectral_theorem]
  change τ Dφ = τ Did * τ Dlog - τ Did
  rw [← map_mul, ← map_sub]
  congr 1
  change Dφ =
    Matrix.diagonal (fun i : ι => (hA.eigenvalues i : ℂ)) *
        Matrix.diagonal (fun i : ι => (Real.log (hA.eigenvalues i) : ℂ)) -
      Matrix.diagonal (fun i : ι => (hA.eigenvalues i : ℂ))
  rw [Matrix.diagonal_mul_diagonal]
  ext i j
  by_cases h : i = j
  · subst h
    simp [Dφ, Matrix.diagonal, sub_eq_add_neg]
  · simp [Dφ, Matrix.diagonal, h]

/-- Hermitian CFC form of `a ↦ a log a`. -/
theorem matrix_isHermitian_cfc_xlog
    {ι : Type*} [Fintype ι] [DecidableEq ι]
    {A : Matrix ι ι ℂ} (hA : Matrix.IsHermitian A) :
    hA.cfc (fun a : ℝ => a * Real.log a) =
      A * hA.cfc Real.log := by
  rw [Matrix.IsHermitian.cfc]
  rw [Matrix.IsHermitian.cfc]
  let τ := ((Unitary.conjStarAlgAut ℂ (Matrix ι ι ℂ)) hA.eigenvectorUnitary)
  let Did : Matrix ι ι ℂ :=
    Matrix.diagonal (fun i : ι => (hA.eigenvalues i : ℂ))
  let Dlog : Matrix ι ι ℂ :=
    Matrix.diagonal (fun i : ι => (Real.log (hA.eigenvalues i) : ℂ))
  let Dφ : Matrix ι ι ℂ :=
    Matrix.diagonal
      (fun i : ι => ((hA.eigenvalues i * Real.log (hA.eigenvalues i) : ℝ) : ℂ))
  change τ Dφ = A * τ Dlog
  rw [hA.spectral_theorem]
  change τ Dφ = τ Did * τ Dlog
  rw [← map_mul]
  congr 1
  rw [Matrix.diagonal_mul_diagonal]
  ext i j
  by_cases h : i = j
  · subst h
    simp [Dφ, Matrix.diagonal]
  · simp [Dφ, Matrix.diagonal, h]

/-- Hermitian CFC form of `a ↦ log a * a`. -/
theorem matrix_isHermitian_cfc_log_mul_id
    {ι : Type*} [Fintype ι] [DecidableEq ι]
    {A : Matrix ι ι ℂ} (hA : Matrix.IsHermitian A) :
    hA.cfc (fun a : ℝ => Real.log a * a) =
      hA.cfc Real.log * A := by
  rw [Matrix.IsHermitian.cfc]
  rw [Matrix.IsHermitian.cfc]
  let τ := ((Unitary.conjStarAlgAut ℂ (Matrix ι ι ℂ)) hA.eigenvectorUnitary)
  let Did : Matrix ι ι ℂ :=
    Matrix.diagonal (fun i : ι => (hA.eigenvalues i : ℂ))
  let Dlog : Matrix ι ι ℂ :=
    Matrix.diagonal (fun i : ι => (Real.log (hA.eigenvalues i) : ℂ))
  let Dlogid : Matrix ι ι ℂ :=
    Matrix.diagonal
      (fun i : ι => ((Real.log (hA.eigenvalues i) *
        hA.eigenvalues i : ℝ) : ℂ))
  change τ Dlogid = τ Dlog * A
  rw [hA.spectral_theorem]
  change τ Dlogid = τ Dlog * τ Did
  rw [← map_mul]
  congr 1
  rw [Matrix.diagonal_mul_diagonal]
  ext i j
  by_cases h : i = j
  · subst h
    simp [Dlogid, Matrix.diagonal]
  · simp [Dlogid, Matrix.diagonal, h]

/-- Spectral-overlap formula for finite-dimensional matrix relative entropy.

For positive matrices this is the Umegaki relative-entropy trace written in
the eigenbases of `X` and `A`; the weights are squared overlaps between the
two eigenvector bases.  This is the source-facing companion to the
superoperator trace target: it identifies the repository's compact trace
definition with the scalar relative-entropy kernel before the remaining
`L_X R_A^{-1}` CFC trace term is matched to the same sum. -/
theorem matrixTrace_hermitianCfc_relativeEntropy_re_eq_sum
    {ι : Type*} [Fintype ι] [DecidableEq ι]
    {X A : Matrix ι ι ℂ} (hX : Matrix.IsHermitian X)
    (hA : Matrix.IsHermitian A) :
    (Matrix.trace (X * hX.cfc Real.log - X * hA.cfc Real.log - (X - A))).re =
      ∑ j : ι, ∑ k : ι,
        realRelativeEntropy (hX.eigenvalues j) (hA.eigenvalues k) *
          Complex.normSq
            (((star (hX.eigenvectorUnitary : Matrix ι ι ℂ)) *
              (hA.eigenvectorUnitary : Matrix ι ι ℂ)) j k) := by
  classical
  let f : Fin 4 → ℝ → ℝ := fun r =>
    if r = 0 then (fun x : ℝ => x * Real.log x)
    else if r = 1 then (fun x : ℝ => -x)
    else if r = 2 then (fun x : ℝ => -x)
    else (fun _ : ℝ => 1)
  let g : Fin 4 → ℝ → ℝ := fun r =>
    if r = 0 then (fun _ : ℝ => 1)
    else if r = 1 then Real.log
    else if r = 2 then (fun _ : ℝ => 1)
    else (fun y : ℝ => y)
  have hmain := matrixTrace_sum_hermitianCfc_mul_cfc_re hX hA f g
  have hlhs :
      (∑ r : Fin 4, Matrix.trace (hX.cfc (f r) * hA.cfc (g r))).re =
        (Matrix.trace (X * hX.cfc Real.log - X * hA.cfc Real.log -
          (X - A))).re := by
    rw [Fin.sum_univ_four]
    simp [f, g]
    rw [matrix_isHermitian_cfc_xlog hX]
    rw [matrix_isHermitian_cfc_const_one hA]
    rw [matrix_isHermitian_cfc_neg_id hX]
    rw [matrix_isHermitian_cfc_const_one hX]
    rw [matrix_isHermitian_cfc_id hA]
    simp [Matrix.trace_neg]
    ring
  have hrhs :
      (∑ j : ι, ∑ k : ι,
        (∑ r : Fin 4, f r (hX.eigenvalues j) * g r (hA.eigenvalues k)) *
          Complex.normSq
            (((star (hX.eigenvectorUnitary : Matrix ι ι ℂ)) *
              (hA.eigenvectorUnitary : Matrix ι ι ℂ)) j k)) =
        ∑ j : ι, ∑ k : ι,
          realRelativeEntropy (hX.eigenvalues j) (hA.eigenvalues k) *
            Complex.normSq
              (((star (hX.eigenvectorUnitary : Matrix ι ι ℂ)) *
                (hA.eigenvectorUnitary : Matrix ι ι ℂ)) j k) := by
    apply Finset.sum_congr rfl
    intro j _hj
    apply Finset.sum_congr rfl
    intro k _hk
    congr 1
    rw [Fin.sum_univ_four]
    simp [f, g, realRelativeEntropy]
    ring
  rw [← hlhs, ← hrhs]
  exact hmain

/-- Single-power overlap expansion for the polynomial trace terms in the
source-faithful superoperator route.

For positive-definite `X` and `A`, the term
`tr(X^n A A^{-n})` has exactly the same eigenbasis-overlap weights as the
compact relative-entropy trace representation, with scalar kernel
`λ^n μ (μ^{-1})^n = μ (λ/μ)^n`.  This is the polynomial substrate needed
before passing to the entropy kernel by uniform approximation. -/
theorem matrixTrace_pow_mul_inv_pow_re_eq_sum
    {ι : Type*} [Fintype ι] [DecidableEq ι]
    {X A : Matrix ι ι ℂ} (hX : Matrix.PosDef X)
    (hA : Matrix.PosDef A) (n : ℕ) :
    (Matrix.trace (X ^ n * A * (A⁻¹) ^ n)).re =
      ∑ j : ι, ∑ k : ι,
        ((hX.isHermitian.eigenvalues j) ^ n *
          (hA.isHermitian.eigenvalues k *
            ((hA.isHermitian.eigenvalues k)⁻¹) ^ n)) *
          Complex.normSq
            (((star (hX.isHermitian.eigenvectorUnitary : Matrix ι ι ℂ)) *
              (hA.isHermitian.eigenvectorUnitary : Matrix ι ι ℂ)) j k) := by
  classical
  have hXpow :
      hX.isHermitian.cfc (fun x : ℝ => x ^ n) = X ^ n := by
    rw [matrix_isHermitian_cfc_fun_pow_nat hX.isHermitian (fun x : ℝ => x) n]
    rw [matrix_isHermitian_cfc_id hX.isHermitian]
  have hAterm :
      A * (A⁻¹) ^ n =
        hA.isHermitian.cfc (fun y : ℝ => y * (y⁻¹) ^ n) :=
    matrix_posDef_mul_inv_pow_eq_cfc hA n
  rw [Matrix.mul_assoc, ← hXpow, hAterm]
  exact matrixTrace_hermitianCfc_mul_cfc_re
    hX.isHermitian hA.isHermitian
    (fun x : ℝ => x ^ n)
    (fun y : ℝ => y * (y⁻¹) ^ n)

/-- Polynomial overlap expansion for the source-faithful superoperator trace
approximants.

This sums `matrixTrace_pow_mul_inv_pow_re_eq_sum` over the real-polynomial
coefficients.  It identifies the real part of the finite-polynomial
superoperator trace formula with the overlap-weighted scalar polynomial
\(\mu\,p(\lambda/\mu)\). -/
theorem matrixPolynomialTraceRatio_re_eq_sum
    {ι : Type*} [Fintype ι] [DecidableEq ι]
    {X A : Matrix ι ι ℂ} (hX : Matrix.PosDef X)
    (hA : Matrix.PosDef A) (q : Polynomial ℝ) :
    ((∑ n ∈ ((q.map (algebraMap ℝ ℂ)).support),
        (q.map (algebraMap ℝ ℂ)).coeff n *
          Matrix.trace (X ^ n * A * (A⁻¹) ^ n))).re =
      ∑ j : ι, ∑ k : ι,
        (hA.isHermitian.eigenvalues k *
          Polynomial.eval
            (hX.isHermitian.eigenvalues j *
              (hA.isHermitian.eigenvalues k)⁻¹) q) *
          Complex.normSq
            (((star (hX.isHermitian.eigenvectorUnitary : Matrix ι ι ℂ)) *
              (hA.isHermitian.eigenvectorUnitary : Matrix ι ι ℂ)) j k) := by
  classical
  let qC : Polynomial ℂ := q.map (algebraMap ℝ ℂ)
  have hsupport : qC.support = q.support := by
    simpa [qC] using
      (Polynomial.support_map_of_injective q
        (f := algebraMap ℝ ℂ) Complex.ofReal_injective)
  have hterm : ∀ n : ℕ,
      ((qC.coeff n) *
          Matrix.trace (X ^ n * A * (A⁻¹) ^ n)).re =
        ∑ j : ι, ∑ k : ι,
          (q.coeff n *
            ((hX.isHermitian.eigenvalues j) ^ n *
              (hA.isHermitian.eigenvalues k *
                ((hA.isHermitian.eigenvalues k)⁻¹) ^ n))) *
            Complex.normSq
              (((star (hX.isHermitian.eigenvectorUnitary : Matrix ι ι ℂ)) *
                (hA.isHermitian.eigenvectorUnitary : Matrix ι ι ℂ)) j k) := by
    intro n
    have hpow := matrixTrace_pow_mul_inv_pow_re_eq_sum hX hA n
    calc
      ((qC.coeff n) *
          Matrix.trace (X ^ n * A * (A⁻¹) ^ n)).re =
          q.coeff n *
            (Matrix.trace (X ^ n * A * (A⁻¹) ^ n)).re := by
            simp [qC, Polynomial.coeff_map]
      _ = q.coeff n *
          (∑ j : ι, ∑ k : ι,
            ((hX.isHermitian.eigenvalues j) ^ n *
              (hA.isHermitian.eigenvalues k *
                ((hA.isHermitian.eigenvalues k)⁻¹) ^ n)) *
              Complex.normSq
                (((star (hX.isHermitian.eigenvectorUnitary : Matrix ι ι ℂ)) *
                  (hA.isHermitian.eigenvectorUnitary : Matrix ι ι ℂ)) j k)) := by
            rw [hpow]
      _ = ∑ j : ι, ∑ k : ι,
          (q.coeff n *
            ((hX.isHermitian.eigenvalues j) ^ n *
              (hA.isHermitian.eigenvalues k *
                ((hA.isHermitian.eigenvalues k)⁻¹) ^ n))) *
            Complex.normSq
              (((star (hX.isHermitian.eigenvectorUnitary : Matrix ι ι ℂ)) *
                (hA.isHermitian.eigenvectorUnitary : Matrix ι ι ℂ)) j k) := by
            rw [Finset.mul_sum]
            apply Finset.sum_congr rfl
            intro j _hj
            rw [Finset.mul_sum]
            apply Finset.sum_congr rfl
            intro k _hk
            ring
  calc
    ((∑ n ∈ ((q.map (algebraMap ℝ ℂ)).support),
        (q.map (algebraMap ℝ ℂ)).coeff n *
          Matrix.trace (X ^ n * A * (A⁻¹) ^ n))).re =
        ∑ n ∈ qC.support,
          ((qC.coeff n) *
            Matrix.trace (X ^ n * A * (A⁻¹) ^ n)).re := by
          simp [qC, Complex.re_sum]
    _ = ∑ n ∈ q.support, ∑ j : ι, ∑ k : ι,
          (q.coeff n *
            ((hX.isHermitian.eigenvalues j) ^ n *
              (hA.isHermitian.eigenvalues k *
                ((hA.isHermitian.eigenvalues k)⁻¹) ^ n))) *
            Complex.normSq
              (((star (hX.isHermitian.eigenvectorUnitary : Matrix ι ι ℂ)) *
                (hA.isHermitian.eigenvectorUnitary : Matrix ι ι ℂ)) j k) := by
          rw [hsupport]
          apply Finset.sum_congr rfl
          intro n _hn
          exact hterm n
    _ = ∑ j : ι, ∑ k : ι, ∑ n ∈ q.support,
          (q.coeff n *
            ((hX.isHermitian.eigenvalues j) ^ n *
              (hA.isHermitian.eigenvalues k *
                ((hA.isHermitian.eigenvalues k)⁻¹) ^ n))) *
            Complex.normSq
              (((star (hX.isHermitian.eigenvectorUnitary : Matrix ι ι ℂ)) *
                (hA.isHermitian.eigenvectorUnitary : Matrix ι ι ℂ)) j k) := by
          rw [Finset.sum_comm]
          apply Finset.sum_congr rfl
          intro j _hj
          rw [Finset.sum_comm]
    _ = ∑ j : ι, ∑ k : ι,
        (hA.isHermitian.eigenvalues k *
          Polynomial.eval
            (hX.isHermitian.eigenvalues j *
              (hA.isHermitian.eigenvalues k)⁻¹) q) *
          Complex.normSq
            (((star (hX.isHermitian.eigenvectorUnitary : Matrix ι ι ℂ)) *
              (hA.isHermitian.eigenvectorUnitary : Matrix ι ι ℂ)) j k) := by
          apply Finset.sum_congr rfl
          intro j _hj
          apply Finset.sum_congr rfl
          intro k _hk
          rw [← Finset.sum_mul]
          congr 1
          calc
            ∑ n ∈ q.support,
                q.coeff n *
                  ((hX.isHermitian.eigenvalues j) ^ n *
                    (hA.isHermitian.eigenvalues k *
                      ((hA.isHermitian.eigenvalues k)⁻¹) ^ n)) =
                hA.isHermitian.eigenvalues k *
                  ∑ n ∈ q.support,
                    q.coeff n *
                      (hX.isHermitian.eigenvalues j *
                        (hA.isHermitian.eigenvalues k)⁻¹) ^ n := by
                  rw [Finset.mul_sum]
                  apply Finset.sum_congr rfl
                  intro n _hn
                  rw [mul_pow]
                  ring
            _ = hA.isHermitian.eigenvalues k *
                Polynomial.eval
                  (hX.isHermitian.eigenvalues j *
                    (hA.isHermitian.eigenvalues k)⁻¹) q := by
                  rw [Polynomial.eval_eq_sum]
                  simp [Polynomial.sum]

/-- Uniform convergence of polynomial entropy-kernel approximants at the
finite eigenvalue-ratio set gives convergence of the overlap-weighted scalar
side of the source-faithful superoperator trace formula. -/
theorem tendsto_matrixPolynomialTraceRatio_overlap_sum_of_uniform_approx
    {α ι : Type*} [Fintype ι] [DecidableEq ι]
    {l : Filter α} {s : Set ℝ} (p : α → Polynomial ℝ)
    (X A : Matrix ι ι ℂ) (hX : Matrix.PosDef X) (hA : Matrix.PosDef A)
    (h_tendsto : TendstoUniformlyOn
      (fun t x => Polynomial.eval x (p t)) realEntropyKernel l s)
    (hratio : ∀ j k : ι,
      hX.isHermitian.eigenvalues j *
        (hA.isHermitian.eigenvalues k)⁻¹ ∈ s) :
    Filter.Tendsto
      (fun t =>
        ∑ j : ι, ∑ k : ι,
          (hA.isHermitian.eigenvalues k *
            Polynomial.eval
              (hX.isHermitian.eigenvalues j *
                (hA.isHermitian.eigenvalues k)⁻¹) (p t)) *
            Complex.normSq
              (((star (hX.isHermitian.eigenvectorUnitary :
                  Matrix ι ι ℂ)) *
                (hA.isHermitian.eigenvectorUnitary :
                  Matrix ι ι ℂ)) j k))
      l
      (nhds
        (∑ j : ι, ∑ k : ι,
          realRelativeEntropy (hX.isHermitian.eigenvalues j)
              (hA.isHermitian.eigenvalues k) *
            Complex.normSq
              (((star (hX.isHermitian.eigenvectorUnitary :
                  Matrix ι ι ℂ)) *
                (hA.isHermitian.eigenvectorUnitary :
                  Matrix ι ι ℂ)) j k))) := by
  classical
  refine tendsto_finset_sum (Finset.univ : Finset ι) ?_
  intro j _hj
  refine tendsto_finset_sum (Finset.univ : Finset ι) ?_
  intro k _hk
  let ratio : ℝ :=
    hX.isHermitian.eigenvalues j *
      (hA.isHermitian.eigenvalues k)⁻¹
  let weight : ℝ :=
    Complex.normSq
      (((star (hX.isHermitian.eigenvectorUnitary :
          Matrix ι ι ℂ)) *
        (hA.isHermitian.eigenvectorUnitary :
          Matrix ι ι ℂ)) j k)
  have hp :
      Filter.Tendsto
        (fun t => Polynomial.eval ratio (p t)) l
        (nhds (realEntropyKernel ratio)) :=
    h_tendsto.tendsto_at (by simpa [ratio] using hratio j k)
  have hmul :
      Filter.Tendsto
        (fun t =>
          (hA.isHermitian.eigenvalues k *
            Polynomial.eval ratio (p t)) * weight)
        l
        (nhds
          ((hA.isHermitian.eigenvalues k *
            realEntropyKernel ratio) * weight)) :=
    (tendsto_const_nhds.mul hp).mul tendsto_const_nhds
  simpa [ratio, weight,
    realRelativeEntropy_eq_mul_realEntropyKernel_mul_inv
      (hX.eigenvalues_pos j) (hA.eigenvalues_pos k)] using hmul

/-- Compact Hermitian matrix form of the entropy first-order trace inequality.

This bridges the separated four-term CFC statement to the usual
`tr(A log A - A + log A * (X - A)) <= tr(X log X - X)` expression, still in
plain `Matrix`/Hermitian-CFC vocabulary. -/
theorem matrixTrace_hermitianCfc_entropy_firstOrder_compact_nonneg
    {ι : Type*} [Fintype ι] [DecidableEq ι]
    {X A : Matrix ι ι ℂ} (hX : Matrix.IsHermitian X)
    (hA : Matrix.IsHermitian A)
    (hXpos : ∀ j : ι, 0 < hX.eigenvalues j)
    (hApos : ∀ k : ι, 0 < hA.eigenvalues k) :
    (Matrix.trace
      (A * hA.cfc Real.log - A + hA.cfc Real.log * (X - A))).re ≤
        (Matrix.trace (X * hX.cfc Real.log - X)).re := by
  have hsep :=
    matrixTrace_hermitianCfc_entropy_firstOrder_sum_nonneg
      hX hA hXpos hApos
  have hsimp :
      (Matrix.trace
          (hX.cfc (fun a : ℝ => a * Real.log a - a) *
            hA.cfc (fun _ : ℝ => 1)) +
        Matrix.trace
          (hX.cfc (fun _ : ℝ => -1) *
            hA.cfc (fun b : ℝ => b * Real.log b - b)) +
        Matrix.trace
          (hX.cfc (fun a : ℝ => -a) *
            hA.cfc (fun b : ℝ => Real.log b)) +
        Matrix.trace
          (hX.cfc (fun _ : ℝ => 1) *
            hA.cfc (fun b : ℝ => Real.log b * b))).re =
        (Matrix.trace (X * hX.cfc Real.log - X)).re -
          (Matrix.trace
            (A * hA.cfc Real.log - A + hA.cfc Real.log * (X - A))).re := by
    rw [matrix_isHermitian_cfc_entropy hX]
    rw [matrix_isHermitian_cfc_const_one hA]
    rw [matrix_isHermitian_cfc_const_neg_one hX]
    rw [matrix_isHermitian_cfc_entropy hA]
    rw [matrix_isHermitian_cfc_neg_id hX]
    rw [matrix_isHermitian_cfc_const_one hX]
    rw [matrix_isHermitian_cfc_log_mul_id hA]
    rw [Matrix.mul_one, one_mul, neg_mul, one_mul]
    rw [Matrix.trace_add]
    rw [Matrix.trace_neg]
    rw [Matrix.trace_sub, Matrix.trace_sub]
    rw [show -X * hA.cfc (fun b : ℝ => Real.log b) =
        -(X * hA.cfc (fun b : ℝ => Real.log b)) by
          rw [neg_mul]]
    rw [Matrix.trace_neg]
    rw [Matrix.trace_mul_comm (hA.cfc Real.log) (X - A)]
    have hmulsub :
        (X - A) * hA.cfc Real.log =
          X * hA.cfc Real.log - A * hA.cfc Real.log := by
      ext i j
      simp [Matrix.mul_apply, Finset.sum_add_distrib, sub_eq_add_neg, add_mul]
    rw [hmulsub, Matrix.trace_sub]
    rw [Matrix.trace_mul_comm X (hA.cfc Real.log)]
    rw [Matrix.trace_mul_comm (hA.cfc Real.log) A]
    simp
    ring
  rw [hsimp] at hsep
  linarith

/-- The spectral-order nonnegativity of a complex `CStarMatrix` implies
positive semidefiniteness in the corresponding plain `Matrix` order. -/
theorem cstarMatrix_nonneg_to_matrix_posSemidef
    {ι : Type*} [Fintype ι] [DecidableEq ι]
    {M : CStarMatrix ι ι ℂ} (hM : 0 ≤ M) :
    Matrix.PosSemidef (CStarMatrix.ofMatrix.symm M : Matrix ι ι ℂ) := by
  rw [StarOrderedRing.nonneg_iff] at hM
  induction hM using AddSubmonoid.closure_induction with
  | mem M hM =>
      rcases hM with ⟨S, rfl⟩
      simpa [CStarMatrix.mul_apply, CStarMatrix.conjTranspose_apply] using
        (Matrix.posSemidef_conjTranspose_mul_self
          (CStarMatrix.ofMatrix.symm S : Matrix ι ι ℂ))
  | zero =>
      exact Matrix.PosSemidef.zero
  | add M N hM hN ihM ihN =>
      exact ihM.add ihN

/-- Strict positivity of a complex `CStarMatrix` implies positive definiteness
of the corresponding plain `Matrix`. -/
theorem cstarMatrix_isStrictlyPositive_to_matrix_posDef
    {ι : Type*} [Fintype ι] [DecidableEq ι]
    {M : CStarMatrix ι ι ℂ} (hM : IsStrictlyPositive M) :
    Matrix.PosDef (CStarMatrix.ofMatrix.symm M : Matrix ι ι ℂ) := by
  have hpsd := cstarMatrix_nonneg_to_matrix_posSemidef hM.nonneg
  exact hpsd.posDef_iff_isUnit.mpr hM.isUnit

/-- Plain matrix positive definiteness of the underlying matrix gives strict
positivity of the corresponding complex `CStarMatrix`. -/
theorem cstarMatrix_isStrictlyPositive_of_matrix_posDef
    {ι : Type*} [Fintype ι] [DecidableEq ι]
    {M : CStarMatrix ι ι ℂ}
    (hM : Matrix.PosDef (CStarMatrix.ofMatrix.symm M : Matrix ι ι ℂ)) :
    IsStrictlyPositive M := by
  have hnonneg : 0 ≤ M :=
    cstarMatrix_nonneg_of_matrix_posSemidef hM.posSemidef
  have hunitMat : IsUnit (CStarMatrix.ofMatrix.symm M : Matrix ι ι ℂ) :=
    hM.isUnit
  have hunit : IsUnit M := by
    rw [isUnit_iff_exists] at hunitMat ⊢
    rcases hunitMat with ⟨N, hMN, hNM⟩
    refine ⟨CStarMatrix.ofMatrix N, ?_, ?_⟩
    · ext i j
      have hij := congrArg (fun X : Matrix ι ι ℂ => X i j) hMN
      simpa [CStarMatrix.mul_apply, Matrix.mul_apply, CStarMatrix.one_apply]
        using hij
    · ext i j
      have hij := congrArg (fun X : Matrix ι ι ℂ => X i j) hNM
      simpa [CStarMatrix.mul_apply, Matrix.mul_apply, CStarMatrix.one_apply]
        using hij
  exact hunit.isStrictlyPositive hnonneg

/-- Diagonal embedding of finite complex vectors into finite complex
`CStarMatrix` objects, bundled as a real star-algebra homomorphism. -/
noncomputable def cstarMatrixDiagonalStarAlgHom
    (ι : Type*) [Fintype ι] [DecidableEq ι] :
    (ι → ℂ) →⋆ₐ[ℝ] CStarMatrix ι ι ℂ where
  toFun v := CStarMatrix.ofMatrix (Matrix.diagonal v)
  map_zero' := by
    ext i j
    simp [Matrix.diagonal]
  map_one' := by
    change CStarMatrix.ofMatrix (Matrix.diagonal (1 : ι → ℂ)) =
      (1 : CStarMatrix ι ι ℂ)
    exact Matrix.diagonal_one
  map_add' v w := by
    ext i j
    change Matrix.diagonal (v + w) i j =
      (Matrix.diagonal v + Matrix.diagonal w) i j
    rw [Matrix.diagonal_add]
    rfl
  map_mul' v w := by
    ext i j
    change Matrix.diagonal (v * w) i j =
      (Matrix.diagonal v * Matrix.diagonal w) i j
    rw [Matrix.diagonal_mul_diagonal]
    rfl
  commutes' r := by
    ext i j
    change Matrix.diagonal (algebraMap ℝ (ι → ℂ) r) i j =
      (algebraMap ℝ (Matrix ι ι ℂ) r) i j
    rw [Matrix.algebraMap_eq_diagonal]
  map_star' v := by
    ext i j
    change Matrix.diagonal (star v) i j = star (Matrix.diagonal v j i)
    by_cases h : i = j
    · subst h
      simp [Matrix.diagonal, Pi.star_apply]
    · have hji : j ≠ i := fun hji => h hji.symm
      simp [Matrix.diagonal, h, hji, Pi.star_apply]

/-- The finite diagonal embedding is continuous. -/
theorem cstarMatrixDiagonalStarAlgHom_continuous
    {ι : Type*} [Fintype ι] [DecidableEq ι] :
    Continuous
      (cstarMatrixDiagonalStarAlgHom ι :
        (ι → ℂ) → CStarMatrix ι ι ℂ) := by
  have hdiag :
      Continuous (fun v : ι → ℂ => (Matrix.diagonal v : Matrix ι ι ℂ)) := by
    apply continuous_pi
    intro i
    apply continuous_pi
    intro j
    by_cases h : i = j
    · subst h
      simpa [Matrix.diagonal] using
        (continuous_apply i : Continuous fun v : ι → ℂ => v i)
    · simpa [Matrix.diagonal, h] using continuous_const
  simpa [cstarMatrixDiagonalStarAlgHom] using
    ((CStarMatrix.ofMatrixL (m := ι) (n := ι) (A := ℂ)).continuous.comp hdiag)

/-- The real logarithm is continuous on the union of the scalar spectra of a
finite nonzero real vector embedded into complex scalars. -/
theorem continuousOn_log_iUnion_spectrum_ofReal
    {ι : Type*} [Fintype ι] (a : ι → ℝ) (ha : ∀ i, a i ≠ 0) :
    ContinuousOn Real.log (⋃ i, spectrum ℝ (algebraMap ℝ ℂ (a i))) := by
  exact Real.continuousOn_log.mono (by
    intro x hx hx0
    rw [Set.mem_iUnion] at hx
    rcases hx with ⟨i, hxi⟩
    have hx_singleton : x ∈ ({a i} : Set ℝ) :=
      CFC.spectrum_algebraMap_subset (A := ℂ) (p := IsSelfAdjoint)
        (r := a i) hxi
    have hxeq : x = a i := by
      simpa using hx_singleton
    exact ha i (by
      rw [← hxeq, hx0]))

/-- Coordinatewise operator-log reduction for finite nonzero real vectors
embedded into complex scalars. -/
theorem piComplex_log_ofReal
    {ι : Type*} [Fintype ι] (a : ι → ℝ) (ha : ∀ i, a i ≠ 0) :
    CFC.log (fun i : ι => (a i : ℂ)) =
      (fun i : ι => (Real.log (a i) : ℂ)) := by
  have hself : IsSelfAdjoint (fun i : ι => (a i : ℂ)) := by
    rw [isSelfAdjoint_iff]
    funext i
    simp
  have hself_coord : ∀ i, IsSelfAdjoint ((a i : ℂ)) := by
    intro i
    rw [isSelfAdjoint_iff]
    simp
  funext i
  dsimp [CFC.log]
  rw [cfc_map_pi (S := ℂ) Real.log (fun i : ι => (a i : ℂ))
    (hf := by
      simpa using continuousOn_log_iUnion_spectrum_ofReal a ha)
    (ha := hself) (ha' := hself_coord)]
  simpa using (CFC.log_algebraMap (A := ℂ) (r := a i))

/-- Diagonal matrices with real diagonal entries. -/
noncomputable def cstarMatrixRealDiagonal
    {ι : Type*} [Fintype ι] [DecidableEq ι] (a : ι → ℝ) :
    CStarMatrix ι ι ℂ :=
  (cstarMatrixDiagonalStarAlgHom ι) (fun i => (a i : ℂ))

/-- Real diagonal matrices are closed under real weighted sums, coordinatewise. -/
theorem cstarMatrixRealDiagonal_smul_add
    {ι : Type*} [Fintype ι] [DecidableEq ι]
    (a b : ι → ℝ) (α β : ℝ) :
    (α • cstarMatrixRealDiagonal a + β • cstarMatrixRealDiagonal b :
        CStarMatrix ι ι ℂ) =
      cstarMatrixRealDiagonal (fun i => α * a i + β * b i) := by
  ext i j
  by_cases h : i = j
  · subst h
    simp [cstarMatrixRealDiagonal, cstarMatrixDiagonalStarAlgHom,
      Matrix.diagonal]
  · simp [cstarMatrixRealDiagonal, cstarMatrixDiagonalStarAlgHom,
      Matrix.diagonal, h]

/-- The trace of a real diagonal `CStarMatrix` is the sum of its diagonal
entries. -/
theorem cstarMatrixTrace_realDiagonal
    {ι : Type*} [Fintype ι] [DecidableEq ι] (a : ι → ℝ) :
    cstarMatrixTrace (cstarMatrixRealDiagonal a) = ∑ i, (a i : ℂ) := by
  simp [cstarMatrixTrace, cstarMatrixRealDiagonal,
    cstarMatrixDiagonalStarAlgHom, Matrix.diagonal]

/-- The operator logarithm of a nonzero real diagonal matrix is the real
diagonal matrix of coordinatewise logarithms. -/
theorem cstarMatrix_log_realDiagonal
    {ι : Type*} [Fintype ι] [DecidableEq ι]
    (a : ι → ℝ) (ha : ∀ i, a i ≠ 0) :
    CFC.log (cstarMatrixRealDiagonal a) =
      cstarMatrixRealDiagonal (fun i => Real.log (a i)) := by
  have hself : IsSelfAdjoint (fun i : ι => (a i : ℂ)) := by
    rw [isSelfAdjoint_iff]
    funext i
    simp
  have hdiag_self :
      IsSelfAdjoint (cstarMatrixRealDiagonal a) := by
    rw [isSelfAdjoint_iff]
    ext i j
    change star (Matrix.diagonal (fun i : ι => (a i : ℂ)) j i) =
      Matrix.diagonal (fun i : ι => (a i : ℂ)) i j
    by_cases h : i = j
    · subst h
      simp [Matrix.diagonal]
    · have hji : j ≠ i := fun hji => h hji.symm
      simp [Matrix.diagonal, h, hji]
  have hcont :
      ContinuousOn Real.log (spectrum ℝ (fun i : ι => (a i : ℂ))) := by
    rw [Pi.spectrum_eq]
    simpa using continuousOn_log_iUnion_spectrum_ofReal a ha
  have hmap :
      (cstarMatrixDiagonalStarAlgHom ι) (cfc Real.log (fun i : ι => (a i : ℂ))) =
        cfc Real.log
          ((cstarMatrixDiagonalStarAlgHom ι) (fun i : ι => (a i : ℂ))) := by
    exact StarAlgHom.map_cfc
      (R := ℝ) (S := ℝ) (A := ι → ℂ) (B := CStarMatrix ι ι ℂ)
      (p := IsSelfAdjoint) (q := IsSelfAdjoint)
      (φ := cstarMatrixDiagonalStarAlgHom ι) Real.log
      (fun i : ι => (a i : ℂ))
      (hf := hcont)
      (hφ := cstarMatrixDiagonalStarAlgHom_continuous)
      (ha := hself) (hφa := hdiag_self)
  change cfc Real.log
      ((cstarMatrixDiagonalStarAlgHom ι) (fun i : ι => (a i : ℂ))) =
    (cstarMatrixDiagonalStarAlgHom ι)
      (fun i : ι => (Real.log (a i) : ℂ))
  rw [← hmap]
  congr 1
  exact piComplex_log_ofReal a ha

/-- Finite complex `CStarMatrix` relative entropy vocabulary for the
Tropp/Lieb proof route.  The real part is used so that the definition lands in
`ℝ`, matching the real-valued convexity statements used elsewhere in this
file. -/
noncomputable def cstarMatrixRelativeEntropy
    {ι : Type*} [Fintype ι] [DecidableEq ι]
    (A B : CStarMatrix ι ι ℂ) : ℝ :=
  (cstarMatrixTrace
    (A * (CFC.log A - CFC.log B) - (A - B))).re

/-- Diagonal normalization for the local C-star matrix relative entropy
vocabulary. -/
theorem cstarMatrixRelativeEntropy_self
    {ι : Type*} [Fintype ι] [DecidableEq ι]
    (A : CStarMatrix ι ι ℂ) :
    cstarMatrixRelativeEntropy A A = 0 := by
  simp [cstarMatrixRelativeEntropy]

/-- Diagonal reduction for C-star matrix relative entropy.  On real diagonal
matrices with nonzero diagonal entries, the matrix expression is exactly the
finite-vector relative entropy. -/
theorem cstarMatrixRelativeEntropy_realDiagonal
    {ι : Type*} [Fintype ι] [DecidableEq ι]
    {a b : ι → ℝ} (ha : ∀ i, a i ≠ 0) (hb : ∀ i, b i ≠ 0) :
    cstarMatrixRelativeEntropy
        (cstarMatrixRealDiagonal a) (cstarMatrixRealDiagonal b) =
      finiteRealRelativeEntropy a b := by
  rw [cstarMatrixRelativeEntropy,
    cstarMatrix_log_realDiagonal a ha,
    cstarMatrix_log_realDiagonal b hb]
  let φ := cstarMatrixDiagonalStarAlgHom ι
  have hinner :
      cstarMatrixRealDiagonal a *
          (cstarMatrixRealDiagonal (fun i => Real.log (a i)) -
            cstarMatrixRealDiagonal (fun i => Real.log (b i))) -
        (cstarMatrixRealDiagonal a - cstarMatrixRealDiagonal b) =
        cstarMatrixRealDiagonal (fun i => realRelativeEntropy (a i) (b i)) := by
    change
      φ (fun i : ι => (a i : ℂ)) *
          (φ (fun i : ι => (Real.log (a i) : ℂ)) -
            φ (fun i : ι => (Real.log (b i) : ℂ))) -
        (φ (fun i : ι => (a i : ℂ)) -
          φ (fun i : ι => (b i : ℂ))) =
        φ (fun i : ι => (realRelativeEntropy (a i) (b i) : ℂ))
    rw [← map_sub, ← map_sub, ← map_mul, ← map_sub]
    congr 1
    funext i
    simp [realRelativeEntropy]
  rw [hinner, cstarMatrixTrace_realDiagonal]
  simp [finiteRealRelativeEntropy, Complex.re_sum]

/-- Diagonal C-star matrix relative entropy is nonnegative for positive real
diagonal entries.  This is the commutative diagonal matrix case, not the full
noncommutative matrix relative-entropy theorem. -/
theorem cstarMatrixRelativeEntropy_realDiagonal_nonneg
    {ι : Type*} [Fintype ι] [DecidableEq ι]
    {a b : ι → ℝ} (ha : ∀ i, 0 < a i) (hb : ∀ i, 0 < b i) :
    0 ≤ cstarMatrixRelativeEntropy
        (cstarMatrixRealDiagonal a) (cstarMatrixRealDiagonal b) := by
  rw [cstarMatrixRelativeEntropy_realDiagonal
    (a := a) (b := b)
    (fun i => ne_of_gt (ha i)) (fun i => ne_of_gt (hb i))]
  exact finiteRealRelativeEntropy_nonneg ha hb

/-- A convex combination with nonnegative weights summing to one preserves
strict positivity of positive real coordinates. -/
theorem positive_weighted_sum_pos
    {x y α β : ℝ} (hx : 0 < x) (hy : 0 < y)
    (hα : 0 ≤ α) (hβ : 0 ≤ β) (hαβ : α + β = 1) :
    0 < α * x + β * y := by
  by_cases hαzero : α = 0
  · have hβone : β = 1 := by linarith
    subst α
    subst β
    simpa using hy
  · have hαpos : 0 < α := lt_of_le_of_ne hα (Ne.symm hαzero)
    exact add_pos_of_pos_of_nonneg (mul_pos hαpos hx) (mul_nonneg hβ hy.le)

/-- Joint convexity of local C-star matrix relative entropy on the real
diagonal subalgebra.

This is the commutative diagonal subcase of the still-open noncommutative
joint-convexity theorem
`cstarMatrixRelativeEntropyJointConvexOnStrictPositive`. -/
theorem cstarMatrixRelativeEntropy_realDiagonal_jointConvex
    {ι : Type*} [Fintype ι] [DecidableEq ι]
    {x y a b : ι → ℝ} {α β : ℝ}
    (hx : ∀ i, 0 < x i) (hy : ∀ i, 0 < y i)
    (ha : ∀ i, 0 < a i) (hb : ∀ i, 0 < b i)
    (hα : 0 ≤ α) (hβ : 0 ≤ β) (hαβ : α + β = 1) :
    cstarMatrixRelativeEntropy
        (α • cstarMatrixRealDiagonal x + β • cstarMatrixRealDiagonal y)
        (α • cstarMatrixRealDiagonal a + β • cstarMatrixRealDiagonal b) ≤
      α * cstarMatrixRelativeEntropy
          (cstarMatrixRealDiagonal x) (cstarMatrixRealDiagonal a) +
        β * cstarMatrixRelativeEntropy
          (cstarMatrixRealDiagonal y) (cstarMatrixRealDiagonal b) := by
  rw [cstarMatrixRealDiagonal_smul_add,
    cstarMatrixRealDiagonal_smul_add]
  rw [cstarMatrixRelativeEntropy_realDiagonal
    (ha := fun i => ne_of_gt
      (positive_weighted_sum_pos (hx i) (hy i) hα hβ hαβ))
    (hb := fun i => ne_of_gt
      (positive_weighted_sum_pos (ha i) (hb i) hα hβ hαβ))]
  rw [cstarMatrixRelativeEntropy_realDiagonal
    (ha := fun i => ne_of_gt (hx i))
    (hb := fun i => ne_of_gt (ha i))]
  rw [cstarMatrixRelativeEntropy_realDiagonal
    (ha := fun i => ne_of_gt (hy i))
    (hb := fun i => ne_of_gt (hb i))]
  exact finiteRealRelativeEntropy_jointConvex hx hy ha hb hα hβ hαβ

/-- Scalar-identity reduction for C-star matrix relative entropy.  This is a
commutative sanity check inside the matrix vocabulary: on real scalar
identities, matrix relative entropy is the scalar relative entropy multiplied
by the matrix dimension. -/
theorem cstarMatrixRelativeEntropy_algebraMap_real
    {ι : Type*} [Fintype ι] [DecidableEq ι] (a b : ℝ) :
    cstarMatrixRelativeEntropy
        (algebraMap ℝ (CStarMatrix ι ι ℂ) a)
        (algebraMap ℝ (CStarMatrix ι ι ℂ) b) =
      (Fintype.card ι : ℝ) * realRelativeEntropy a b := by
  have hloga : CFC.log (algebraMap ℝ (CStarMatrix ι ι ℂ) a) =
      algebraMap ℝ (CStarMatrix ι ι ℂ) (Real.log a) :=
    CFC.log_algebraMap (A := CStarMatrix ι ι ℂ) (r := a)
  have hlogb : CFC.log (algebraMap ℝ (CStarMatrix ι ι ℂ) b) =
      algebraMap ℝ (CStarMatrix ι ι ℂ) (Real.log b) :=
    CFC.log_algebraMap (A := CStarMatrix ι ι ℂ) (r := b)
  rw [cstarMatrixRelativeEntropy, hloga, hlogb]
  have hinner :
      (algebraMap ℝ (CStarMatrix ι ι ℂ) a) *
          (algebraMap ℝ (CStarMatrix ι ι ℂ) (Real.log a) -
            algebraMap ℝ (CStarMatrix ι ι ℂ) (Real.log b)) -
        (algebraMap ℝ (CStarMatrix ι ι ℂ) a -
          algebraMap ℝ (CStarMatrix ι ι ℂ) b) =
        algebraMap ℝ (CStarMatrix ι ι ℂ) (realRelativeEntropy a b) := by
    simp [realRelativeEntropy, map_sub, map_mul]
  rw [hinner]
  simp [cstarMatrixTrace, Algebra.algebraMap_eq_smul_one, mul_comm]

/-- C-star matrix relative entropy is nonnegative for positive real scalar
identities.  This closes only the scalar-identity matrix case; it is not the
full noncommutative matrix relative-entropy nonnegativity theorem. -/
theorem cstarMatrixRelativeEntropy_algebraMap_real_nonneg
    {ι : Type*} [Fintype ι] [DecidableEq ι] {a b : ℝ}
    (ha : 0 < a) (hb : 0 < b) :
    0 ≤ cstarMatrixRelativeEntropy
        (algebraMap ℝ (CStarMatrix ι ι ℂ) a)
        (algebraMap ℝ (CStarMatrix ι ι ℂ) b) := by
  rw [cstarMatrixRelativeEntropy_algebraMap_real]
  exact mul_nonneg (Nat.cast_nonneg _) (realRelativeEntropy_nonneg ha hb)

/-!
## Hansen-Pedersen Jensen source target

Effros's matrix-perspective proof of relative-entropy joint convexity starts
from the Hansen-Pedersen two-point Jensen inequality.  The definitions below
record the exact finite C-star-matrix target needed by that source route.  They
are target propositions, not hidden hypotheses.  The identity-function case is
proved as a sanity check that the target shape agrees with the local
continuous-functional-calculus vocabulary.
-/

/-- Positive-cone ordinary matrix convexity target in the local finite
C-star-matrix vocabulary.  This is the source hypothesis that Effros uses
before applying the Hansen-Pedersen-Jensen transfer theorem. -/
def cstarMatrixPositiveOperatorConvexTarget
    {ι : Type*} [Fintype ι] [DecidableEq ι] (f : ℝ → ℝ) : Prop :=
  ∀ (a b : ℝ), 0 ≤ a → 0 ≤ b → a + b = 1 →
    ∀ (T1 T2 : CStarMatrix ι ι ℂ),
      IsStrictlyPositive T1 → IsStrictlyPositive T2 →
      cfc (p := IsSelfAdjoint) f (a • T1 + b • T2) ≤
        a • cfc (p := IsSelfAdjoint) f T1 +
          b • cfc (p := IsSelfAdjoint) f T2

/-- Positive-cone ordinary matrix convexity at every finite matrix size.

The Hansen-Pedersen block-matrix proof of operator Jensen uses a larger
matrix algebra, so the source-faithful hypothesis is the all-finite-size
version rather than only the fixed-index target above. -/
def cstarMatrixPositiveOperatorConvexAllFiniteTarget.{u}
    (f : ℝ → ℝ) : Prop :=
  ∀ {κ : Type u} [Fintype κ] [DecidableEq κ],
    cstarMatrixPositiveOperatorConvexTarget (ι := κ) f

/-- The identity-function sanity case of the positive-cone ordinary matrix
convexity target.  This proves only the affine case and does not prove
operator convexity for nonlinear functions. -/
theorem cstarMatrixPositiveOperatorConvexTarget_id
    {ι : Type*} [Fintype ι] [DecidableEq ι] :
    cstarMatrixPositiveOperatorConvexTarget (ι := ι)
      (fun x : ℝ => x) := by
  intro a b _ha _hb _hab T1 T2 hT1 hT2
  rw [cfc_id' ℝ (a • T1 + b • T2)]
  have hcf1 :
      cfc (p := IsSelfAdjoint) (fun x : ℝ => x) T1 = T1 :=
    cfc_id' ℝ T1 hT1.isSelfAdjoint
  have hcf2 :
      cfc (p := IsSelfAdjoint) (fun x : ℝ => x) T2 = T2 :=
    cfc_id' ℝ T2 hT2.isSelfAdjoint
  rw [hcf1, hcf2]

/-- All-finite-size identity-function sanity case for the source-faithful
ordinary matrix-convexity hypothesis. -/
theorem cstarMatrixPositiveOperatorConvexAllFiniteTarget_id.{u} :
    cstarMatrixPositiveOperatorConvexAllFiniteTarget.{u}
      (fun x : ℝ => x) := by
  intro κ _ _
  exact cstarMatrixPositiveOperatorConvexTarget_id (ι := κ)

/-- Two-point Hansen-Pedersen Jensen target in the local finite C-star-matrix
vocabulary.  The intended source theorem says this holds for matrix-convex
functions `f` under the normalization `A* A + B* B = I`. -/
def cstarMatrixHansenPedersenJensenTwoPointTarget
    {ι : Type*} [Fintype ι] [DecidableEq ι] (f : ℝ → ℝ) : Prop :=
  ∀ (A B T1 T2 : CStarMatrix ι ι ℂ),
    IsSelfAdjoint T1 → IsSelfAdjoint T2 →
    star A * A + star B * B = 1 →
      cfc (p := IsSelfAdjoint) f (star A * T1 * A + star B * T2 * B) ≤
        star A * cfc (p := IsSelfAdjoint) f T1 * A +
          star B * cfc (p := IsSelfAdjoint) f T2 * B

/-- The identity-function sanity case of the local Hansen-Pedersen Jensen
target.  This proves only the affine equality built into the target shape; it
does not prove operator Jensen for nonlinear matrix-convex functions. -/
theorem cstarMatrixHansenPedersenJensenTwoPointTarget_id
    {ι : Type*} [Fintype ι] [DecidableEq ι] :
    cstarMatrixHansenPedersenJensenTwoPointTarget (ι := ι)
      (fun x : ℝ => x) := by
  intro A B T1 T2 hT1 hT2 _hAB
  rw [cfc_id' ℝ (star A * T1 * A + star B * T2 * B)]
  rw [cfc_id' ℝ T1 hT1]
  rw [cfc_id' ℝ T2 hT2]

/-- Continuous functional calculus distributes over a block diagonal matrix.

This is a block-diagonal CFC dependency for the Hansen--Pedersen proof: it
identifies \(f(\operatorname{diag}(T_1,T_2))\) with
\(\operatorname{diag}(f(T_1),f(T_2))\) under the usual self-adjointness and
continuity-on-spectrum hypotheses. -/
theorem cstarMatrixBlockDiagonal_cfc
    {ι : Type*} [Fintype ι] [DecidableEq ι]
    (f : ℝ → ℝ) (T1 T2 : CStarMatrix ι ι ℂ)
    (hT1 : IsSelfAdjoint T1) (hT2 : IsSelfAdjoint T2)
    (hf : ContinuousOn f (spectrum ℝ T1 ∪ spectrum ℝ T2)) :
    cfc (p := IsSelfAdjoint) f (cstarMatrixBlockDiagonal T1 T2) =
      cstarMatrixBlockDiagonal
        (cfc (p := IsSelfAdjoint) f T1)
        (cfc (p := IsSelfAdjoint) f T2) := by
  let φ := cstarMatrixBlockDiagonalStarAlgHom ι
  letI :
      ContinuousFunctionalCalculus ℝ
        (CStarMatrix ι ι ℂ × CStarMatrix ι ι ℂ) IsSelfAdjoint :=
    IsSelfAdjoint.instContinuousFunctionalCalculus
      (A := CStarMatrix ι ι ℂ × CStarMatrix ι ι ℂ)
  have hpair : IsSelfAdjoint (T1, T2) := by
    rw [isSelfAdjoint_iff]
    ext <;> simp [isSelfAdjoint_iff.mp hT1, isSelfAdjoint_iff.mp hT2]
  have hdiag : IsSelfAdjoint (φ (T1, T2)) :=
    cstarMatrixBlockDiagonal_isSelfAdjoint hT1 hT2
  have hmap :
      φ (cfc (p := IsSelfAdjoint) f (T1, T2)) =
        cfc (p := IsSelfAdjoint) f (φ (T1, T2)) := by
    set_option backward.isDefEq.respectTransparency false in
    exact StarAlgHom.map_cfc
      (R := ℝ) (S := ℝ)
      (A := CStarMatrix ι ι ℂ × CStarMatrix ι ι ℂ)
      (B := CStarMatrix (ι ⊕ ι) (ι ⊕ ι) ℂ)
      (p := IsSelfAdjoint) (q := IsSelfAdjoint)
      (φ := φ) f (T1, T2)
      (hf := by simpa [Prod.spectrum_eq] using hf)
      (hφ := cstarMatrixBlockDiagonalStarAlgHom_continuous)
      (ha := hpair) (hφa := hdiag)
  have hprod :
      cfc (p := IsSelfAdjoint) f (T1, T2) =
        (cfc (p := IsSelfAdjoint) f T1,
          cfc (p := IsSelfAdjoint) f T2) := by
    exact cfc_map_prod
      (S := ℝ) (pab := IsSelfAdjoint)
      (pa := IsSelfAdjoint) (pb := IsSelfAdjoint)
      f T1 T2 (hf := hf) (hab := hpair) (ha := hT1) (hb := hT2)
  calc
    cfc (p := IsSelfAdjoint) f (cstarMatrixBlockDiagonal T1 T2) =
        φ (cfc (p := IsSelfAdjoint) f (T1, T2)) := by
      simpa [φ] using hmap.symm
    _ = cstarMatrixBlockDiagonal
        (cfc (p := IsSelfAdjoint) f T1)
        (cfc (p := IsSelfAdjoint) f T2) := by
      rw [hprod]
      rfl

/-- Continuous functional calculus commutes with conjugation by a unitary
finite C⋆-matrix.

This is the conjugation half of the standard pinching/reflection proof:
if \(U\) is unitary and \(T=T^*\), then
\[
  f(UTU^*) = U f(T) U^* .
\]
It does not by itself prove the pinching average or Hansen--Pedersen
compression Jensen inequality. -/
theorem cstarMatrix_cfc_unitary_conj
    {ι : Type*} [Fintype ι] [DecidableEq ι]
    (u : unitary (CStarMatrix ι ι ℂ)) (T : CStarMatrix ι ι ℂ)
    (hT : IsSelfAdjoint T) (f : ℝ → ℝ)
    (hf : ContinuousOn f (spectrum ℝ T)) :
    cfc (p := IsSelfAdjoint) f
        ((u : CStarMatrix ι ι ℂ) * T *
          star (u : CStarMatrix ι ι ℂ)) =
      (u : CStarMatrix ι ι ℂ) *
        cfc (p := IsSelfAdjoint) f T *
          star (u : CStarMatrix ι ι ℂ) := by
  let e := Unitary.conjStarAlgAut ℂ (CStarMatrix ι ι ℂ) u
  let φ : CStarMatrix ι ι ℂ →⋆ₐ[ℂ] CStarMatrix ι ι ℂ :=
    { toFun := e
      map_one' := map_one e
      map_mul' := map_mul e
      map_zero' := map_zero e
      map_add' := map_add e
      commutes' := by
        intro z
        simp [Algebra.algebraMap_eq_smul_one]
      map_star' := e.map_star' }
  have hφT : φ T =
      (u : CStarMatrix ι ι ℂ) * T *
        star (u : CStarMatrix ι ι ℂ) := by
    simp [φ, e, Unitary.conjStarAlgAut_apply]
    rfl
  letI : StarHomClass
      (CStarMatrix ι ι ℂ ≃⋆ₐ[ℂ] CStarMatrix ι ι ℂ)
      (CStarMatrix ι ι ℂ) (CStarMatrix ι ι ℂ) :=
    { map_star := fun e x => e.map_star' x }
  have hmap :
      φ (cfc (p := IsSelfAdjoint) f T) =
        cfc (p := IsSelfAdjoint) f (φ T) := by
    exact StarAlgHom.map_cfc
      (R := ℝ) (S := ℂ)
      (A := CStarMatrix ι ι ℂ) (B := CStarMatrix ι ι ℂ)
      (p := IsSelfAdjoint) (q := IsSelfAdjoint)
      (φ := φ) f T
      (hf := hf)
      (hφ := by
        have heiso :
            Isometry (e : CStarMatrix ι ι ℂ → CStarMatrix ι ι ℂ) :=
          StarAlgEquiv.isometry
            (F := CStarMatrix ι ι ℂ ≃⋆ₐ[ℂ] CStarMatrix ι ι ℂ) e
        simpa [φ] using heiso.continuous)
      (ha := hT) (hφa := by cfc_tac)
  rw [← hφT, ← hmap]
  simp [φ, e, Unitary.conjStarAlgAut_apply]
  rfl

/-- Compression by a rectangular C⋆-matrix preserves nonnegativity. -/
theorem cstarMatrix_compression_nonneg
    {α β : Type*} [Fintype α] [DecidableEq α] [Fintype β] [DecidableEq β]
    {M : CStarMatrix α α ℂ} (hM : 0 ≤ M)
    (V : CStarMatrix α β ℂ) :
    0 ≤ CStarMatrix.conjTranspose V * M * V := by
  apply cstarMatrix_nonneg_of_matrix_posSemidef
  let Vm : Matrix α β ℂ := CStarMatrix.ofMatrix.symm V
  let Mm : Matrix α α ℂ := CStarMatrix.ofMatrix.symm M
  have hMpsd : Matrix.PosSemidef Mm := by
    simpa [Mm] using cstarMatrix_nonneg_to_matrix_posSemidef hM
  have hmatrix :
      CStarMatrix.ofMatrix.symm
          (CStarMatrix.conjTranspose V * M * V) =
        Vm.conjTranspose * Mm * Vm := by
    ext i j
    simp [Vm, Mm, CStarMatrix.mul_apply, Matrix.mul_apply,
      CStarMatrix.conjTranspose_apply, Matrix.conjTranspose_apply]
  simpa [hmatrix] using hMpsd.conjTranspose_mul_mul_same Vm

/-- Compression by an injective rectangular matrix preserves strict
positivity. -/
theorem cstarMatrix_compression_isStrictlyPositive_of_injective_mulVec
    {α β : Type*} [Fintype α] [DecidableEq α] [Fintype β] [DecidableEq β]
    {M : CStarMatrix α α ℂ} (hM : IsStrictlyPositive M)
    (V : CStarMatrix α β ℂ)
    (hinj :
      Function.Injective
        (CStarMatrix.ofMatrix.symm V : Matrix α β ℂ).mulVec) :
    IsStrictlyPositive (CStarMatrix.conjTranspose V * M * V) := by
  classical
  let Vm : Matrix α β ℂ := CStarMatrix.ofMatrix.symm V
  let Mm : Matrix α α ℂ := CStarMatrix.ofMatrix.symm M
  have hMpos : Matrix.PosDef Mm := by
    simpa [Mm] using cstarMatrix_isStrictlyPositive_to_matrix_posDef hM
  have hcomp : Matrix.PosDef (Vm.conjTranspose * Mm * Vm) :=
    hMpos.conjTranspose_mul_mul_same hinj
  have hmatrix :
      CStarMatrix.ofMatrix.symm
          (CStarMatrix.conjTranspose V * M * V) =
        Vm.conjTranspose * Mm * Vm := by
    ext i j
    simp [Vm, Mm, CStarMatrix.mul_apply, Matrix.mul_apply,
      CStarMatrix.conjTranspose_apply, Matrix.conjTranspose_apply]
  have htarget : Matrix.PosDef
      (CStarMatrix.ofMatrix.symm
        (CStarMatrix.conjTranspose V * M * V) : Matrix β β ℂ) := by
    simpa [hmatrix] using hcomp
  exact cstarMatrix_isStrictlyPositive_of_matrix_posDef htarget

/-- Compression by a rectangular C⋆-matrix is monotone for the spectral order. -/
theorem cstarMatrix_compression_mono
    {α β : Type*} [Fintype α] [DecidableEq α] [Fintype β] [DecidableEq β]
    {X Y : CStarMatrix α α ℂ} (hXY : X ≤ Y)
    (V : CStarMatrix α β ℂ) :
    CStarMatrix.conjTranspose V * X * V ≤
      CStarMatrix.conjTranspose V * Y * V := by
  rw [← sub_nonneg]
  have hnonneg : 0 ≤ Y - X := sub_nonneg.mpr hXY
  have hcomp := cstarMatrix_compression_nonneg hnonneg V
  have hdiff :
      CStarMatrix.conjTranspose V * (Y - X) * V =
        CStarMatrix.conjTranspose V * Y * V -
          CStarMatrix.conjTranspose V * X * V := by
    have hneg :
        CStarMatrix.conjTranspose V * (-X) * V =
          -(CStarMatrix.conjTranspose V * X * V) := by
      ext i j
      simp [CStarMatrix.mul_apply]
    calc
      CStarMatrix.conjTranspose V * (Y - X) * V =
          CStarMatrix.conjTranspose V * (Y + -X) * V := by
            rw [sub_eq_add_neg]
      _ = (CStarMatrix.conjTranspose V * Y +
            CStarMatrix.conjTranspose V * (-X)) * V := by
            rw [cstarMatrix_mul_add_rect]
      _ = CStarMatrix.conjTranspose V * Y * V +
            CStarMatrix.conjTranspose V * (-X) * V := by
            rw [cstarMatrix_add_mul_rect]
      _ = CStarMatrix.conjTranspose V * Y * V -
            CStarMatrix.conjTranspose V * X * V := by
            rw [hneg]
            rfl
  simpa [hdiff] using hcomp

/-- Reflection-pinching CFC inequality for a block-column range reflection.

This closes the convexity half of the Hansen--Pedersen block proof: ordinary
operator convexity on the doubled finite matrix algebra gives
`f((D + RDR)/2) <= (f(D) + f(RDR))/2`, and unitary invariance of CFC rewrites
`f(RDR)` as `R f(D) R`.  The remaining bottleneck is the separate corner CFC
identification
`Vᴴ f((D + RDR)/2) V = f(Vᴴ D V)`. -/
theorem cstarMatrixColumnPair_reflectionAverage_cfc_le_average_of_sum
    {ι : Type u} [Fintype ι] [DecidableEq ι]
    {A B : CStarMatrix ι ι ℂ}
    (hAB : star A * A + star B * B = 1)
    (f : ℝ → ℝ)
    (hconv : cstarMatrixPositiveOperatorConvexAllFiniteTarget.{u} f)
    (D : CStarMatrix (ι ⊕ ι) (ι ⊕ ι) ℂ)
    (hD : IsStrictlyPositive D)
    (hf : ContinuousOn f (spectrum ℝ D)) :
    cfc (p := IsSelfAdjoint) f
        ((1 / 2 : ℂ) •
          (D + cstarMatrixColumnPairRangeReflection A B * D *
            cstarMatrixColumnPairRangeReflection A B)) ≤
      (1 / 2 : ℝ) • cfc (p := IsSelfAdjoint) f D +
        (1 / 2 : ℝ) •
          (cstarMatrixColumnPairRangeReflection A B *
            cfc (p := IsSelfAdjoint) f D *
              cstarMatrixColumnPairRangeReflection A B) := by
  let R : CStarMatrix (ι ⊕ ι) (ι ⊕ ι) ℂ :=
    cstarMatrixColumnPairRangeReflection A B
  have hRself : IsSelfAdjoint R := by
    dsimp [R]
    exact cstarMatrixColumnPairRangeReflection_isSelfAdjoint A B
  have hRstar : star R = R := by
    simpa [isSelfAdjoint_iff] using hRself
  have hRDRstrict : IsStrictlyPositive (R * D * R) := by
    have hstrict :
        IsStrictlyPositive (R * D * star R) := by
      dsimp [R]
      exact cstarMatrixColumnPairRangeReflection_conj_isStrictlyPositive_of_sum
        hAB hD
    simpa [hRstar] using hstrict
  have hconvD :
      cfc (p := IsSelfAdjoint) f
          ((1 / 2 : ℝ) • D + (1 / 2 : ℝ) • (R * D * R)) ≤
        (1 / 2 : ℝ) • cfc (p := IsSelfAdjoint) f D +
          (1 / 2 : ℝ) • cfc (p := IsSelfAdjoint) f (R * D * R) := by
    exact hconv
      (a := (1 / 2 : ℝ)) (b := (1 / 2 : ℝ))
      (by norm_num) (by norm_num) (by norm_num)
      D (R * D * R) hD hRDRstrict
  have hcfR :
      cfc (p := IsSelfAdjoint) f (R * D * R) =
        R * cfc (p := IsSelfAdjoint) f D * R := by
    let u : unitary (CStarMatrix (ι ⊕ ι) (ι ⊕ ι) ℂ) :=
      ⟨R, by
        dsimp [R]
        exact cstarMatrixColumnPairRangeReflection_mem_unitary_of_sum hAB⟩
    have hconj :=
      cstarMatrix_cfc_unitary_conj u D hD.isSelfAdjoint f hf
    simpa [u, hRstar] using hconj
  have hleft :
      ((1 / 2 : ℝ) • D + (1 / 2 : ℝ) • (R * D * R)) =
        (1 / 2 : ℂ) • (D + R * D * R) := by
    ext i j
    simp
    ring
  rw [← hleft]
  simpa [R, hcfR] using hconvD

/-- Compressed form of the reflection-pinching CFC inequality.

After compressing the reflection-average inequality by the block column
`V=[A;B]`, the reflected right-hand term collapses because the range reflection
fixes `V` and `Vᴴ`.  The only missing step toward Hansen--Pedersen Jensen is
therefore the nonlinear corner identity identifying the left side with
`f(Vᴴ D V)`. -/
theorem cstarMatrixColumnPair_reflectionAverage_compressed_cfc_le_compressed_of_sum
    {ι : Type u} [Fintype ι] [DecidableEq ι]
    {A B : CStarMatrix ι ι ℂ}
    (hAB : star A * A + star B * B = 1)
    (f : ℝ → ℝ)
    (hconv : cstarMatrixPositiveOperatorConvexAllFiniteTarget.{u} f)
    (D : CStarMatrix (ι ⊕ ι) (ι ⊕ ι) ℂ)
    (hD : IsStrictlyPositive D)
    (hf : ContinuousOn f (spectrum ℝ D)) :
    CStarMatrix.conjTranspose (cstarMatrixColumnPair A B) *
        cfc (p := IsSelfAdjoint) f
          ((1 / 2 : ℂ) •
            (D + cstarMatrixColumnPairRangeReflection A B * D *
              cstarMatrixColumnPairRangeReflection A B)) *
        cstarMatrixColumnPair A B ≤
      CStarMatrix.conjTranspose (cstarMatrixColumnPair A B) *
        cfc (p := IsSelfAdjoint) f D *
        cstarMatrixColumnPair A B := by
  let V : CStarMatrix (ι ⊕ ι) ι ℂ := cstarMatrixColumnPair A B
  let R : CStarMatrix (ι ⊕ ι) (ι ⊕ ι) ℂ :=
    cstarMatrixColumnPairRangeReflection A B
  let F : CStarMatrix (ι ⊕ ι) (ι ⊕ ι) ℂ :=
    cfc (p := IsSelfAdjoint) f D
  have hpinch :=
    cstarMatrixColumnPair_reflectionAverage_cfc_le_average_of_sum
      (A := A) (B := B) hAB f hconv D hD hf
  have hcomp := cstarMatrix_compression_mono hpinch V
  have hright_half :
      ((1 / 2 : ℝ) • F + (1 / 2 : ℝ) • (R * F * R)) =
        (1 / 2 : ℂ) • (F + R * F * R) := by
    ext i j
    simp [F, R]
    ring
  have hright :
      CStarMatrix.conjTranspose V *
          ((1 / 2 : ℝ) • F + (1 / 2 : ℝ) • (R * F * R)) * V =
        CStarMatrix.conjTranspose V * F * V := by
    rw [hright_half]
    dsimp [V, R, F]
    exact cstarMatrixColumnPair_reflectionAverage_compression_of_sum hAB
      (cfc (p := IsSelfAdjoint) f D)
  calc
    CStarMatrix.conjTranspose (cstarMatrixColumnPair A B) *
        cfc (p := IsSelfAdjoint) f
          ((1 / 2 : ℂ) •
            (D + cstarMatrixColumnPairRangeReflection A B * D *
              cstarMatrixColumnPairRangeReflection A B)) *
        cstarMatrixColumnPair A B =
        CStarMatrix.conjTranspose V *
          cfc (p := IsSelfAdjoint) f
            ((1 / 2 : ℂ) • (D + R * D * R)) * V := rfl
    _ ≤ CStarMatrix.conjTranspose V *
          ((1 / 2 : ℝ) • F + (1 / 2 : ℝ) • (R * F * R)) * V := hcomp
    _ = CStarMatrix.conjTranspose V * F * V := hright
    _ = CStarMatrix.conjTranspose (cstarMatrixColumnPair A B) *
        cfc (p := IsSelfAdjoint) f D *
        cstarMatrixColumnPair A B := rfl

/-- The block column \(V=[A;B]\) has injective `mulVec` action whenever
`VᴴV=I`.

This is the matrix-side injectivity needed to transfer strict positivity of a
block diagonal \(D\) to the compression \(V^*DV\). -/
theorem cstarMatrixColumnPair_mulVec_injective_of_sum
    {ι : Type*} [Fintype ι] [DecidableEq ι]
    {A B : CStarMatrix ι ι ℂ}
    (hAB : star A * A + star B * B = 1) :
    Function.Injective
      (CStarMatrix.ofMatrix.symm (cstarMatrixColumnPair A B) :
        Matrix (ι ⊕ ι) ι ℂ).mulVec := by
  classical
  let Vc : CStarMatrix (ι ⊕ ι) ι ℂ := cstarMatrixColumnPair A B
  let V : Matrix (ι ⊕ ι) ι ℂ := CStarMatrix.ofMatrix.symm Vc
  have hVV : V.conjTranspose * V = 1 := by
    have hC :
        CStarMatrix.conjTranspose Vc * Vc =
          (1 : CStarMatrix ι ι ℂ) := by
      simpa [Vc] using cstarMatrixColumnPair_conjTranspose_mul_self_eq_one_of_sum hAB
    ext i j
    have hc := congrArg (fun M : CStarMatrix ι ι ℂ => M i j) hC
    simpa [V, Vc, CStarMatrix.mul_apply, Matrix.mul_apply,
      Matrix.conjTranspose_apply, CStarMatrix.star_apply,
      CStarMatrix.one_apply] using hc
  intro x y hxy
  have hsub : V.mulVec (x - y) = 0 := by
    rw [Matrix.mulVec_sub, hxy, sub_self]
  have hleft : (V.conjTranspose * V).mulVec (x - y) = 0 := by
    rw [← Matrix.mulVec_mulVec]
    rw [hsub, Matrix.mulVec_zero]
  have hzero : x - y = 0 := by
    simpa [hVV, Matrix.one_mulVec] using hleft
  exact sub_eq_zero.mp hzero

/-- The block-column compression by `V=[A;B]` preserves strict positivity when
`VᴴV=I`. -/
theorem cstarMatrixColumnPair_compression_isStrictlyPositive_of_sum
    {ι : Type*} [Fintype ι] [DecidableEq ι]
    {A B : CStarMatrix ι ι ℂ}
    (hAB : star A * A + star B * B = 1)
    {D : CStarMatrix (ι ⊕ ι) (ι ⊕ ι) ℂ}
    (hD : IsStrictlyPositive D) :
    IsStrictlyPositive
      (CStarMatrix.conjTranspose (cstarMatrixColumnPair A B) *
        D * cstarMatrixColumnPair A B) := by
  exact cstarMatrix_compression_isStrictlyPositive_of_injective_mulVec
    hD (cstarMatrixColumnPair A B)
    (by simpa using cstarMatrixColumnPair_mulVec_injective_of_sum hAB)

/-- A strict-positive block diagonal stays strict-positive after compression by
the block isometry \(V=[A;B]\). -/
theorem cstarMatrixColumnPair_compress_blockDiagonal_isStrictlyPositive_of_sum
    {ι : Type*} [Fintype ι] [DecidableEq ι]
    {A B T1 T2 : CStarMatrix ι ι ℂ}
    (hAB : star A * A + star B * B = 1)
    (hT1 : IsStrictlyPositive T1) (hT2 : IsStrictlyPositive T2) :
    IsStrictlyPositive
      (CStarMatrix.conjTranspose (cstarMatrixColumnPair A B) *
        cstarMatrixBlockDiagonal T1 T2 *
          cstarMatrixColumnPair A B) := by
  classical
  let Vc : CStarMatrix (ι ⊕ ι) ι ℂ := cstarMatrixColumnPair A B
  let D : CStarMatrix (ι ⊕ ι) (ι ⊕ ι) ℂ :=
    cstarMatrixBlockDiagonal T1 T2
  let V : Matrix (ι ⊕ ι) ι ℂ := CStarMatrix.ofMatrix.symm Vc
  let Dm : Matrix (ι ⊕ ι) (ι ⊕ ι) ℂ := CStarMatrix.ofMatrix.symm D
  have hDstrict : IsStrictlyPositive D :=
    cstarMatrixBlockDiagonal_isStrictlyPositive hT1 hT2
  have hDpos : Matrix.PosDef Dm :=
    cstarMatrix_isStrictlyPositive_to_matrix_posDef hDstrict
  have hinj : Function.Injective V.mulVec := by
    simpa [V, Vc] using cstarMatrixColumnPair_mulVec_injective_of_sum hAB
  have hpos : Matrix.PosDef (V.conjTranspose * Dm * V) :=
    hDpos.conjTranspose_mul_mul_same hinj
  have hmatrix :
      CStarMatrix.ofMatrix.symm (CStarMatrix.conjTranspose Vc * D * Vc) =
        V.conjTranspose * Dm * V := by
    ext i j
    simp [V, Dm, Vc, D, CStarMatrix.mul_apply, Matrix.mul_apply,
      Matrix.conjTranspose_apply]
  have htarget : Matrix.PosDef
      (CStarMatrix.ofMatrix.symm
        (CStarMatrix.conjTranspose Vc * D * Vc) : Matrix ι ι ℂ) := by
    simpa [hmatrix] using hpos
  exact cstarMatrix_isStrictlyPositive_of_matrix_posDef htarget

/-- The Hansen--Pedersen two-point compression
`A* T1 A + B* T2 B` is strictly positive whenever `T1,T2` are strictly
positive and `A* A + B* B = I`. -/
theorem cstarMatrixHansenPedersenCompression_isStrictlyPositive_of_sum
    {ι : Type*} [Fintype ι] [DecidableEq ι]
    {A B T1 T2 : CStarMatrix ι ι ℂ}
    (hAB : star A * A + star B * B = 1)
    (hT1 : IsStrictlyPositive T1) (hT2 : IsStrictlyPositive T2) :
    IsStrictlyPositive (star A * T1 * A + star B * T2 * B) := by
  have hcompress :=
    cstarMatrixColumnPair_compress_blockDiagonal_isStrictlyPositive_of_sum
      (A := A) (B := B) (T1 := T1) (T2 := T2) hAB hT1 hT2
  simpa [cstarMatrixColumnPair_conjTranspose_mul_blockDiagonal_mul_columnPair]
    using hcompress

/-- Source-route transfer target: ordinary matrix convexity on the positive
cone should imply the two-point Hansen-Pedersen noncommutative Jensen
inequality on the same positive cone.  This is the theorem supplied by the
Hansen-Pedersen source; it is named here as an open local target, not assumed. -/
def cstarMatrixPositiveHansenPedersenTransferTarget
    {ι : Type*} [Fintype ι] [DecidableEq ι] (f : ℝ → ℝ) : Prop :=
  cstarMatrixPositiveOperatorConvexTarget (ι := ι) f →
    ∀ (A B T1 T2 : CStarMatrix ι ι ℂ),
      IsStrictlyPositive T1 → IsStrictlyPositive T2 →
      star A * A + star B * B = 1 →
        cfc (p := IsSelfAdjoint) f (star A * T1 * A + star B * T2 * B) ≤
          star A * cfc (p := IsSelfAdjoint) f T1 * A +
            star B * cfc (p := IsSelfAdjoint) f T2 * B

/-- Source-faithful all-finite-size Hansen-Pedersen transfer target.

Unlike `cstarMatrixPositiveHansenPedersenTransferTarget`, this target exposes
the matrix-convexity hypothesis at every finite size, matching the usual
block-matrix proof route through a doubled index type. -/
def cstarMatrixPositiveHansenPedersenTransferAllFiniteTarget.{u}
    (f : ℝ → ℝ) : Prop :=
  cstarMatrixPositiveOperatorConvexAllFiniteTarget.{u} f →
    ∀ {ι : Type u} [Fintype ι] [DecidableEq ι]
      (A B T1 T2 : CStarMatrix ι ι ℂ),
      IsStrictlyPositive T1 → IsStrictlyPositive T2 →
      star A * A + star B * B = 1 →
        cfc (p := IsSelfAdjoint) f (star A * T1 * A + star B * T2 * B) ≤
          star A * cfc (p := IsSelfAdjoint) f T1 * A +
            star B * cfc (p := IsSelfAdjoint) f T2 * B

/-- The concrete operator-convexity source target for the function
`x ↦ x log x` on the positive cone.  Effros cites this as the input used
before applying Hansen-Pedersen Jensen. -/
def cstarMatrixXLogXPositiveOperatorConvexTarget
    {ι : Type*} [Fintype ι] [DecidableEq ι] : Prop :=
  cstarMatrixPositiveOperatorConvexTarget (ι := ι)
    (fun x : ℝ => x * Real.log x)

/-- The concrete Hansen-Pedersen transfer target for the function
`x ↦ x log x` on the positive cone.  Together with
`cstarMatrixXLogXPositiveOperatorConvexTarget`, this is the source-faithful
split of `cstarMatrixXLogXHansenPedersenJensenTarget`. -/
def cstarMatrixXLogXHansenPedersenTransferTarget
    {ι : Type*} [Fintype ι] [DecidableEq ι] : Prop :=
  cstarMatrixPositiveHansenPedersenTransferTarget (ι := ι)
    (fun x : ℝ => x * Real.log x)

/-- The all-finite-size ordinary matrix-convexity source target for
`x ↦ x log x`. -/
def cstarMatrixXLogXPositiveOperatorConvexAllFiniteTarget.{u} : Prop :=
  cstarMatrixPositiveOperatorConvexAllFiniteTarget.{u}
    (fun x : ℝ => x * Real.log x)

/-- The concrete ordinary operator-convexity target for the normalized entropy
kernel `x log x - (x - 1)`. -/
def cstarMatrixEntropyKernelPositiveOperatorConvexTarget
    {ι : Type*} [Fintype ι] [DecidableEq ι] : Prop :=
  cstarMatrixPositiveOperatorConvexTarget (ι := ι) realEntropyKernel

/-- All-finite-size ordinary operator convexity for the normalized entropy
kernel. -/
def cstarMatrixEntropyKernelPositiveOperatorConvexAllFiniteTarget.{u} : Prop :=
  cstarMatrixPositiveOperatorConvexAllFiniteTarget.{u} realEntropyKernel

/-- The source-faithful all-finite-size Hansen-Pedersen transfer target for
`x ↦ x log x`. -/
def cstarMatrixXLogXHansenPedersenTransferAllFiniteTarget.{u} : Prop :=
  cstarMatrixPositiveHansenPedersenTransferAllFiniteTarget.{u}
    (fun x : ℝ => x * Real.log x)

/-- The concrete Hansen-Pedersen source target for the Effros/Tropp
relative-entropy route: operator Jensen for `x ↦ x log x` on positive
matrices.  Closing this target, together with the perspective construction and
trace representation, is the next source-aligned path toward
`cstarMatrixRelativeEntropyJointConvexOnStrictPositive`. -/
def cstarMatrixXLogXHansenPedersenJensenTarget
    {ι : Type*} [Fintype ι] [DecidableEq ι] : Prop :=
  ∀ (A B T1 T2 : CStarMatrix ι ι ℂ),
    IsStrictlyPositive T1 → IsStrictlyPositive T2 →
    star A * A + star B * B = 1 →
      cfc (p := IsSelfAdjoint) (fun x : ℝ => x * Real.log x)
          (star A * T1 * A + star B * T2 * B) ≤
        star A * cfc (p := IsSelfAdjoint) (fun x : ℝ => x * Real.log x) T1 * A +
          star B * cfc (p := IsSelfAdjoint) (fun x : ℝ => x * Real.log x) T2 * B

/-- The concrete Hansen-Pedersen target for the normalized entropy kernel
`x log x - (x - 1)`.  This affine correction is the scalar kernel in the
operator-perspective representation of normalized matrix relative entropy. -/
def cstarMatrixEntropyKernelHansenPedersenJensenTarget
    {ι : Type*} [Fintype ι] [DecidableEq ι] : Prop :=
  ∀ (A B T1 T2 : CStarMatrix ι ι ℂ),
    IsStrictlyPositive T1 → IsStrictlyPositive T2 →
    star A * A + star B * B = 1 →
      cfc (p := IsSelfAdjoint) realEntropyKernel
          (star A * T1 * A + star B * T2 * B) ≤
        star A * cfc (p := IsSelfAdjoint) realEntropyKernel T1 * A +
          star B * cfc (p := IsSelfAdjoint) realEntropyKernel T2 * B

/-- Assembly adapter for the source-faithful Hansen-Pedersen split.  Once the
ordinary positive-cone operator-convexity theorem for `x ↦ x log x` and the
Hansen-Pedersen transfer theorem are proved locally, the concrete two-point
Jensen target follows without an additional hypothesis. -/
theorem cstarMatrixXLogXHansenPedersenJensenTarget_of_positiveOperatorConvex_of_transfer
    {ι : Type*} [Fintype ι] [DecidableEq ι]
    (hconv : cstarMatrixXLogXPositiveOperatorConvexTarget (ι := ι))
    (htransfer : cstarMatrixXLogXHansenPedersenTransferTarget (ι := ι)) :
    cstarMatrixXLogXHansenPedersenJensenTarget (ι := ι) := by
  exact htransfer hconv

/-- Functional-calculus normalization for the scalar derivative
`x ↦ 1 + log x` of `x ↦ x log x` on the strictly positive cone. -/
theorem cstarMatrix_cfc_one_add_log_eq_one_add_log
    {ι : Type*} [Fintype ι] [DecidableEq ι]
    (A : CStarMatrix ι ι ℂ) (hA : IsStrictlyPositive A) :
    cfc (p := IsSelfAdjoint) (fun x : ℝ => 1 + Real.log x) A =
      1 + CFC.log A := by
  have hzero : (0 : ℝ) ∉ spectrum ℝ A := spectrum.zero_notMem ℝ hA.isUnit
  have hcont : ContinuousOn Real.log (spectrum ℝ A) := by
    intro x hx
    have hx0 : x ≠ 0 := by
      intro hxeq
      exact hzero (by simpa [hxeq] using hx)
    exact (Real.continuousAt_log hx0).continuousWithinAt
  rw [show
      cfc (p := IsSelfAdjoint) (fun x : ℝ => 1 + Real.log x) A =
        algebraMap ℝ (CStarMatrix ι ι ℂ) 1 +
          cfc (p := IsSelfAdjoint) Real.log A from
    cfc_const_add (A := CStarMatrix ι ι ℂ) (p := IsSelfAdjoint)
      (R := ℝ) 1 Real.log A hcont hA.isSelfAdjoint]
  rfl

/-- Bendat-Sherman-route derivative monotonicity target for
`x ↦ x log x`: the formal derivative `x ↦ 1 + log x` is operator-monotone on
the strictly positive cone.  This is only a route dependency; converting it to
operator convexity still requires a local Bendat-Sherman theorem. -/
def cstarMatrixXLogXDerivativeMonotoneTarget
    {ι : Type*} [Fintype ι] [DecidableEq ι] : Prop :=
  ∀ (A B : CStarMatrix ι ι ℂ),
    IsStrictlyPositive A → IsStrictlyPositive B → A ≤ B →
      cfc (p := IsSelfAdjoint) (fun x : ℝ => 1 + Real.log x) A ≤
        cfc (p := IsSelfAdjoint) (fun x : ℝ => 1 + Real.log x) B

/-- The derivative monotonicity target follows from the repository's
operator-log monotonicity wrapper.  This closes a Bendat-Sherman-route
subdependency but not the Bendat-Sherman convexity theorem itself. -/
theorem cstarMatrixXLogXDerivativeMonotoneTarget_of_log_monotone
    {ι : Type*} [Fintype ι] [DecidableEq ι] :
    cstarMatrixXLogXDerivativeMonotoneTarget (ι := ι) := by
  intro A B hA hB hAB
  rw [cstarMatrix_cfc_one_add_log_eq_one_add_log A hA,
    cstarMatrix_cfc_one_add_log_eq_one_add_log B hB]
  exact add_le_add_right (cstarMatrix_log_le_log A B hAB hA) 1

/-- Generic positive-cone operator-monotonicity target in the local finite
C-star-matrix vocabulary. -/
def cstarMatrixStrictPositiveOperatorMonotoneTarget
    {ι : Type*} [Fintype ι] [DecidableEq ι] (f : ℝ → ℝ) : Prop :=
  ∀ (A B : CStarMatrix ι ι ℂ),
    IsStrictlyPositive A → IsStrictlyPositive B → A ≤ B →
      cfc (p := IsSelfAdjoint) f A ≤ cfc (p := IsSelfAdjoint) f B

/-- The first divided difference of `x ↦ x log x`, normalized on the diagonal
by the formal derivative `1 + log c`.  Bendat-Sherman's source theorem is more
faithfully represented through monotonicity of these divided differences than
through the derivative value alone. -/
noncomputable def realXLogXDividedDifference (c x : ℝ) : ℝ :=
  if x = c then
    1 + Real.log c
  else
    (x * Real.log x - c * Real.log c) / (x - c)

@[simp]
theorem realXLogXDividedDifference_self (c : ℝ) :
    realXLogXDividedDifference c c = 1 + Real.log c := by
  simp [realXLogXDividedDifference]

/-- Off the diagonal, the first divided difference of `x ↦ x log x` can be
written as `log c` plus a logarithmic ratio term.  This scalar normalization is
a listed Bendat-Sherman-route dependency for the future integral-representation
proof of divided-difference operator monotonicity. -/
theorem realXLogXDividedDifference_eq_log_add_ratio
    {c x : ℝ} (hc : 0 < c) (hx : 0 < x) (hxc : x ≠ c) :
    realXLogXDividedDifference c x =
      Real.log c + x * Real.log (x / c) / (x - c) := by
  have hlogdiv : Real.log (x / c) = Real.log x - Real.log c :=
    Real.log_div (ne_of_gt hx) (ne_of_gt hc)
  have hsub : x - c ≠ 0 := sub_ne_zero.mpr hxc
  dsimp [realXLogXDividedDifference]
  rw [if_neg hxc]
  rw [hlogdiv]
  field_simp [hsub]
  ring

/-- Normalized scalar form of the first divided difference of `x ↦ x log x`:
after setting `t = x / c`, the off-diagonal part is
`log c + t log t / (t - 1)`.  The remaining unproved operator step is that
this normalized logarithmic kernel is operator-monotone. -/
theorem realXLogXDividedDifference_eq_log_add_normalized
    {c x : ℝ} (hc : 0 < c) (hx : 0 < x) (hxc : x ≠ c) :
    realXLogXDividedDifference c x =
      Real.log c + (x / c) * Real.log (x / c) / (x / c - 1) := by
  rw [realXLogXDividedDifference_eq_log_add_ratio hc hx hxc]
  have hcne : c ≠ 0 := ne_of_gt hc
  have hsub : x - c ≠ 0 := sub_ne_zero.mpr hxc
  have hratio : x / c - 1 ≠ 0 := by
    intro h
    have hxdiv : x / c = 1 := by linarith
    have hmul := congrArg (fun y : ℝ => y * c) hxdiv
    have hxc_eq : x = c := by
      field_simp [hcne] at hmul
      linarith
    exact hxc hxc_eq
  field_simp [hcne, hsub, hratio]

/-- The diagonal-normalized logarithmic kernel appearing in the first divided
difference of `x ↦ x log x`.

The off-diagonal expression is `t log t / (t - 1)`, and the diagonal value is
the continuous extension `1`. -/
noncomputable def realNormalizedLogKernel (t : ℝ) : ℝ :=
  if t = 1 then 1 else t * Real.log t / (t - 1)

@[simp]
theorem realNormalizedLogKernel_one :
    realNormalizedLogKernel 1 = 1 := by
  simp [realNormalizedLogKernel]

theorem realNormalizedLogKernel_eq_of_ne_one {t : ℝ} (ht : t ≠ 1) :
    realNormalizedLogKernel t = t * Real.log t / (t - 1) := by
  simp [realNormalizedLogKernel, ht]

/-- The normalized logarithmic kernel is `t` times the divided slope of
`log` at the base point `1`.

This scalar identity exposes the continuity at `t = 1` through mathlib's
`dslope` API. -/
theorem realNormalizedLogKernel_eq_mul_dslope_log (t : ℝ) :
    realNormalizedLogKernel t = t * dslope Real.log (1 : ℝ) t := by
  by_cases ht : t = 1
  · subst t
    simp [Real.deriv_log]
  · rw [realNormalizedLogKernel_eq_of_ne_one ht]
    rw [dslope_of_ne (f := Real.log) (a := (1 : ℝ)) (b := t)]
    · simp [slope]
      field_simp [sub_ne_zero.mpr ht]
    · exact ht

/-- The normalized logarithmic kernel is continuous on the positive real line. -/
theorem continuousOn_realNormalizedLogKernel_Ioi :
    ContinuousOn realNormalizedLogKernel (Set.Ioi (0 : ℝ)) := by
  have hds : ContinuousOn (dslope Real.log (1 : ℝ)) (Set.Ioi (0 : ℝ)) := by
    rw [continuousOn_dslope (f := Real.log) (a := (1 : ℝ))
      (s := Set.Ioi (0 : ℝ))
      (isOpen_Ioi.mem_nhds (show (1 : ℝ) ∈ Set.Ioi 0 by norm_num))]
    constructor
    · intro x hx
      exact (Real.continuousAt_log (ne_of_gt hx)).continuousWithinAt
    · exact Real.differentiableAt_log one_ne_zero
  have hprod : ContinuousOn (fun t : ℝ => t * dslope Real.log (1 : ℝ) t)
      (Set.Ioi (0 : ℝ)) :=
    continuousOn_id.mul hds
  exact hprod.congr fun t _ht => realNormalizedLogKernel_eq_mul_dslope_log t

/-- The scalar first divided difference of `x ↦ x log x` factors through the
normalized logarithmic kernel after the change of variables `t = x / c`.

This closes the scalar normalization dependency for the Bendat--Sherman route:
the remaining open part is operator monotonicity of this normalized kernel and
the Bendat--Sherman bridge itself. -/
theorem realXLogXDividedDifference_eq_log_add_normalizedKernel
    {c x : ℝ} (hc : 0 < c) (hx : 0 < x) :
    realXLogXDividedDifference c x =
      Real.log c + realNormalizedLogKernel (x / c) := by
  by_cases hxc : x = c
  · subst x
    have hcne : c ≠ 0 := ne_of_gt hc
    simp [realNormalizedLogKernel, hcne]
    ring
  · have hratio : x / c ≠ 1 := by
      intro h
      have hmul := congrArg (fun y : ℝ => y * c) h
      have hx_eq_c : x = c := by
        field_simp [ne_of_gt hc] at hmul
        linarith
      exact hxc hx_eq_c
    rw [realXLogXDividedDifference_eq_log_add_normalized hc hx hxc]
    rw [realNormalizedLogKernel_eq_of_ne_one hratio]

/-- Scalar integral representation of the off-diagonal normalized logarithmic
kernel.

For `t > 0` and `t ≠ 1`,
`t log t / (t - 1)` is the integral of the fractional kernels
`t / (u + (1 - u)t)` over `u ∈ [0,1]`.  This is the scalar identity needed
before the operator-valued integral route can be closed. -/
theorem real_normalizedLogKernel_offdiag_intervalIntegral
    {t : ℝ} (ht : 0 < t) (ht1 : t ≠ 1) :
    (∫ u in (0 : ℝ)..1, t / (u + (1 - u) * t)) =
      t * Real.log t / (t - 1) := by
  let F : ℝ → ℝ :=
    fun u => (t / (1 - t)) * Real.log (t + (1 - t) * u)
  have hdenpos_Icc :
      ∀ u ∈ Set.Icc (0 : ℝ) 1, 0 < t + (1 - t) * u := by
    intro u hu
    have hu1 : u ≤ 1 := hu.2
    calc
      0 < (1 - u) * t + u := by
        nlinarith [mul_nonneg (sub_nonneg.mpr hu1) (le_of_lt ht), hu.1]
      _ = t + (1 - t) * u := by ring
  have hderiv :
      ∀ u ∈ Set.Ioo (0 : ℝ) 1,
        HasDerivAt F (t / (u + (1 - u) * t)) u := by
    intro u hu
    have huIcc : u ∈ Set.Icc (0 : ℝ) 1 :=
      ⟨le_of_lt hu.1, le_of_lt hu.2⟩
    have hdenpos : 0 < t + (1 - t) * u := hdenpos_Icc u huIcc
    have hne : t + (1 - t) * u ≠ 0 := ne_of_gt hdenpos
    have hlog :
        HasDerivAt
          (fun u : ℝ => Real.log (t + (1 - t) * u))
          ((1 - t) / (t + (1 - t) * u)) u := by
      have hlin :
          HasDerivAt (fun u : ℝ => t + (1 - t) * u) (1 - t) u := by
        simpa [mul_comm, mul_left_comm, mul_assoc] using
          ((hasDerivAt_id u).const_mul (1 - t)).const_add t
      simpa [div_eq_mul_inv] using hlin.log hne
    have hmul := hlog.const_mul (t / (1 - t))
    convert hmul using 1
    · field_simp [sub_ne_zero.mpr ht1.symm, hne]
      ring
  have hcont : ContinuousOn F (Set.Icc (0 : ℝ) 1) := by
    refine ContinuousOn.const_mul ?_ _
    refine ContinuousOn.log ?_ ?_
    · fun_prop
    · intro u hu
      exact ne_of_gt (hdenpos_Icc u hu)
  have hcontg :
      ContinuousOn
        (fun u : ℝ => t / (u + (1 - u) * t)) (Set.Icc (0 : ℝ) 1) := by
    refine ContinuousOn.div (by fun_prop) (by fun_prop) ?_
    intro u hu hzero
    have hpos : 0 < u + (1 - u) * t := by
      calc
        0 < t + (1 - t) * u := hdenpos_Icc u hu
        _ = u + (1 - u) * t := by ring
    exact ne_of_gt hpos hzero
  have hint :
      IntervalIntegrable
        (fun u : ℝ => t / (u + (1 - u) * t)) MeasureTheory.volume 0 1 := by
    exact hcontg.intervalIntegrable_of_Icc (by norm_num)
  have hFTC :=
    intervalIntegral.integral_eq_sub_of_hasDerivAt_of_le
      (a := (0 : ℝ)) (b := 1) (f := F)
      (f' := fun u : ℝ => t / (u + (1 - u) * t))
      (by norm_num) hcont hderiv hint
  rw [hFTC]
  dsimp [F]
  have h1 : t + (1 - t) * 1 = 1 := by ring
  have h0 : t + (1 - t) * 0 = t := by ring
  rw [h1, h0, Real.log_one]
  field_simp [sub_ne_zero.mpr ht1.symm]
  have hden : t - 1 ≠ 0 := sub_ne_zero.mpr ht1
  field_simp [hden]
  ring

open MeasureTheory Set in
/-- Set-integral form of the normalized logarithmic-kernel representation.

This packages the off-diagonal interval-integral identity together with the
diagonal value `realNormalizedLogKernel 1 = 1`, using Lebesgue measure
restricted to `[0,1]`. -/
theorem realNormalizedLogKernel_setIntegral
    {t : ℝ} (ht : 0 < t) :
    (∫ u in Set.Icc (0 : ℝ) 1, t / (u + (1 - u) * t)) =
      realNormalizedLogKernel t := by
  by_cases ht1 : t = 1
  · subst t
    calc
      (∫ u in Set.Icc (0 : ℝ) 1,
          (1 : ℝ) / (u + (1 - u) * (1 : ℝ))) =
          ∫ _u in Set.Icc (0 : ℝ) 1, (1 : ℝ) := by
            refine setIntegral_congr_fun measurableSet_Icc ?_
            intro u _hu
            norm_num
      _ = 1 := by
            simp [Real.volume_real_Icc_of_le (show (0 : ℝ) ≤ 1 by norm_num)]
      _ = realNormalizedLogKernel 1 := by simp
  · have hinterval := real_normalizedLogKernel_offdiag_intervalIntegral (t := t) ht ht1
    have hIoc :
        (∫ u in Set.Ioc (0 : ℝ) 1, t / (u + (1 - u) * t)) =
          t * Real.log t / (t - 1) := by
      simpa [intervalIntegral.integral_of_le (show (0 : ℝ) ≤ 1 by norm_num)]
        using hinterval
    have hIcc_eq_Ioc :
        (∫ u in Set.Icc (0 : ℝ) 1, t / (u + (1 - u) * t)) =
          ∫ u in Set.Ioc (0 : ℝ) 1, t / (u + (1 - u) * t) := by
      exact (setIntegral_congr_set (Ioc_ae_eq_Icc (a := (0 : ℝ)) (b := 1))).symm
    rw [hIcc_eq_Ioc, hIoc, realNormalizedLogKernel_eq_of_ne_one ht1]

/-- The normalized logarithmic kernel recovers `x log x` after multiplying by
`x - 1`.

This is the scalar bridge from the already formalized normalized-kernel
integral representation back to the operator-convexity target function
`x ↦ x log x`. -/
theorem real_xlog_eq_sub_one_mul_realNormalizedLogKernel (x : ℝ) :
    (x - 1) * realNormalizedLogKernel x = x * Real.log x := by
  by_cases hx : x = 1
  · subst x
    simp [realNormalizedLogKernel]
  · rw [realNormalizedLogKernel_eq_of_ne_one hx]
    field_simp [sub_ne_zero.mpr hx]

open MeasureTheory Set in
/-- Scalar set-integral representation of `x log x` obtained from the
normalized logarithmic-kernel representation.

For positive `x`, the factor `(x - 1)` times the normalized fractional-kernel
integral is exactly `x log x`.  This closes the scalar normalization layer for
the direct shifted-inverse route; the remaining open part is the operator
integral assembly proving matrix convexity of `x ↦ x log x`. -/
theorem real_xlog_eq_sub_one_mul_normalizedKernel_setIntegral
    {x : ℝ} (hx : 0 < x) :
    (x - 1) *
        (∫ u in Set.Icc (0 : ℝ) 1, x / (u + (1 - u) * x)) =
      x * Real.log x := by
  rw [realNormalizedLogKernel_setIntegral hx]
  exact real_xlog_eq_sub_one_mul_realNormalizedLogKernel x

open MeasureTheory Set in
/-- Scalar integral representation of `x log x` using the actual
unit-interval kernel.

This rewrites the normalized-kernel representation by pushing the scalar factor
`x - 1` inside the integral.  It is the scalar source identity for the direct
operator-convexity route. -/
theorem real_xlog_eq_unit_interval_xlog_kernel_integral
    {x : ℝ} (hx : 0 < x) :
    (∫ u in Set.Icc (0 : ℝ) 1,
        x * (x - 1) / (u + (1 - u) * x)) =
      x * Real.log x := by
  rw [← real_xlog_eq_sub_one_mul_normalizedKernel_setIntegral hx]
  rw [← MeasureTheory.integral_const_mul
    (μ := (volume : Measure ℝ).restrict (Set.Icc (0 : ℝ) 1))
    (r := x - 1)
    (f := fun u : ℝ => x / (u + (1 - u) * x))]
  refine setIntegral_congr_fun measurableSet_Icc ?_
  intro u _hu
  ring

/-- Scalar algebra for the direct shifted-inverse route.

For \(x>0\) and \(0 \le u < 1\), the integrand
\((x-1)^2/(u+(1-u)x)\) decomposes into an affine term in `x` plus a positive
multiple of the shifted inverse kernel
\(x \mapsto (x+u/(1-u))^{-1}\).  This is the scalar decomposition needed
before turning shifted inverse-kernel convexity into operator convexity of
`x ↦ x log x`. -/
theorem real_unit_interval_xlog_integrand_eq_affine_add_shifted_inv
    {u x : ℝ} (hx : 0 < x) (hu0 : 0 ≤ u) (hu1 : u < 1) :
    (x - 1) ^ 2 / (u + (1 - u) * x) =
      (1 / (1 - u)) * x - (2 - u) / (1 - u) ^ 2 +
        (1 / (1 - u) ^ 3) * (x + u / (1 - u))⁻¹ := by
  have hαpos : 0 < 1 - u := by linarith
  have hα : 1 - u ≠ 0 := ne_of_gt hαpos
  have hshift : 0 < x + u / (1 - u) := by positivity
  have hshift_ne : x + u / (1 - u) ≠ 0 := ne_of_gt hshift
  have hden : u + (1 - u) * x ≠ 0 := by
    have hden_pos : 0 < u + (1 - u) * x :=
      add_pos_of_nonneg_of_pos hu0 (mul_pos hαpos hx)
    exact ne_of_gt hden_pos
  field_simp [hα, hshift_ne, hden]
  ring

/-- CFC lift of the scalar affine-plus-shifted-inverse decomposition.

For a strictly positive finite C-star matrix `A` and `0 ≤ u < 1`, functional
calculus applied to the scalar integrand
`(x - 1)^2 / (u + (1 - u) x)` is the corresponding affine expression in `A`
plus a positive multiple of the shifted-inverse CFC kernel.  This is a direct
route dependency toward assembling the integral representation of
operator-convexity for `x ↦ x log x`; it does not yet perform the operator
integral assembly. -/
theorem cstarMatrix_cfc_unit_interval_xlog_integrand_eq_affine_add_shifted_inv
    {ι : Type*} [Fintype ι] [DecidableEq ι]
    {A : CStarMatrix ι ι ℂ} (hA : IsStrictlyPositive A)
    {u : ℝ} (hu0 : 0 ≤ u) (hu1 : u < 1) :
    cfc (p := IsSelfAdjoint)
        (fun x : ℝ => (x - 1) ^ 2 / (u + (1 - u) * x)) A =
      (1 / (1 - u)) • A -
        ((2 - u) / (1 - u) ^ 2) • (1 : CStarMatrix ι ι ℂ) +
        (1 / (1 - u) ^ 3) •
          cfc (p := IsSelfAdjoint)
            (fun x : ℝ => (x + u / (1 - u))⁻¹) A := by
  have hαpos : 0 < 1 - u := by linarith
  have hshift_nonneg : 0 ≤ u / (1 - u) :=
    div_nonneg hu0 (le_of_lt hαpos)
  have hpos_spectrum : ∀ x ∈ spectrum ℝ A, 0 < x := by
    intro x hx
    have hx_nonneg : 0 ≤ x := cstarMatrix_spectrum_nonneg_of_nonneg hA.nonneg hx
    have hx_ne : x ≠ 0 := by
      intro hxeq
      exact (spectrum.zero_notMem ℝ hA.isUnit) (by simpa [hxeq] using hx)
    exact lt_of_le_of_ne hx_nonneg (Ne.symm hx_ne)
  have hshift_cont :
      ContinuousOn (fun x : ℝ => (x + u / (1 - u))⁻¹) (spectrum ℝ A) := by
    refine ContinuousOn.inv₀ (by fun_prop) ?_
    intro x hx hzero
    have hx_pos : 0 < x := hpos_spectrum x hx
    have hsum_pos : 0 < x + u / (1 - u) :=
      add_pos_of_pos_of_nonneg hx_pos hshift_nonneg
    exact ne_of_gt hsum_pos hzero
  have hlinear :
      cfc (p := IsSelfAdjoint)
          (fun x : ℝ => (1 / (1 - u)) * x - (2 - u) / (1 - u) ^ 2) A =
        (1 / (1 - u)) • A -
          ((2 - u) / (1 - u) ^ 2) • (1 : CStarMatrix ι ι ℂ) := by
    rw [cfc_sub
      (f := fun x : ℝ => (1 / (1 - u)) * x)
      (g := fun _ : ℝ => (2 - u) / (1 - u) ^ 2) (a := A)
      (hf := by fun_prop) (hg := by fun_prop)]
    have hmulid :
        cfc (p := IsSelfAdjoint) (fun x : ℝ => (1 / (1 - u)) * x) A =
          (1 / (1 - u)) • A := by
      simpa using
        (cfc_const_mul_id (R := ℝ) (A := CStarMatrix ι ι ℂ)
          (p := IsSelfAdjoint) (r := 1 / (1 - u)) (a := A)
          (ha := hA.isSelfAdjoint))
    have hconst :
        cfc (p := IsSelfAdjoint)
            (fun _ : ℝ => (2 - u) / (1 - u) ^ 2) A =
          ((2 - u) / (1 - u) ^ 2) •
            (1 : CStarMatrix ι ι ℂ) := by
      simpa [Algebra.algebraMap_eq_smul_one] using
        (cfc_const (p := IsSelfAdjoint)
          ((2 - u) / (1 - u) ^ 2) A hA.isSelfAdjoint)
    rw [hmulid, hconst]
  have hshift_scaled :
      cfc (p := IsSelfAdjoint)
          (fun x : ℝ => (1 / (1 - u) ^ 3) *
            (x + u / (1 - u))⁻¹) A =
        (1 / (1 - u) ^ 3) •
          cfc (p := IsSelfAdjoint)
            (fun x : ℝ => (x + u / (1 - u))⁻¹) A := by
    rw [cfc_const_mul (R := ℝ) (A := CStarMatrix ι ι ℂ)
      (p := IsSelfAdjoint) (r := 1 / (1 - u) ^ 3)
      (f := fun x : ℝ => (x + u / (1 - u))⁻¹) (a := A)
      (hf := hshift_cont)]
  have hcongr :
      cfc (p := IsSelfAdjoint)
          (fun x : ℝ => (x - 1) ^ 2 / (u + (1 - u) * x)) A =
        cfc (p := IsSelfAdjoint)
          (fun x : ℝ =>
            (1 / (1 - u)) * x - (2 - u) / (1 - u) ^ 2 +
              (1 / (1 - u) ^ 3) * (x + u / (1 - u))⁻¹) A := by
    refine cfc_congr ?_
    intro x hx
    exact real_unit_interval_xlog_integrand_eq_affine_add_shifted_inv
      (hpos_spectrum x hx) hu0 hu1
  rw [hcongr]
  calc
    cfc (p := IsSelfAdjoint)
        (fun x : ℝ =>
          (1 / (1 - u)) * x - (2 - u) / (1 - u) ^ 2 +
            (1 / (1 - u) ^ 3) * (x + u / (1 - u))⁻¹) A =
        cfc (p := IsSelfAdjoint)
            (fun x : ℝ => (1 / (1 - u)) * x -
              (2 - u) / (1 - u) ^ 2) A +
          cfc (p := IsSelfAdjoint)
            (fun x : ℝ => (1 / (1 - u) ^ 3) *
              (x + u / (1 - u))⁻¹) A := by
          rw [cfc_add
            (f := fun x : ℝ => (1 / (1 - u)) * x -
              (2 - u) / (1 - u) ^ 2)
            (g := fun x : ℝ => (1 / (1 - u) ^ 3) *
              (x + u / (1 - u))⁻¹) (a := A)
            (hf := by fun_prop)
            (hg := ContinuousOn.const_mul hshift_cont _)]
    _ = (1 / (1 - u)) • A -
        ((2 - u) / (1 - u) ^ 2) • (1 : CStarMatrix ι ι ℂ) +
        (1 / (1 - u) ^ 3) •
          cfc (p := IsSelfAdjoint)
            (fun x : ℝ => (x + u / (1 - u))⁻¹) A := by
          rw [hlinear, hshift_scaled]

/-- Scalar algebra for the actual normalized-kernel integrand of `x log x`.

Multiplying the normalized logarithmic-kernel integrand by `x - 1` gives
`x * (x - 1) / (u + (1 - u) x)`.  For `x > 0` and `0 ≤ u < 1`, this
decomposes into an affine term in `x` plus a nonnegative multiple (for
`u ≥ 0`) of the shifted inverse kernel. -/
theorem real_unit_interval_xlog_kernel_integrand_eq_affine_add_shifted_inv
    {u x : ℝ} (hx : 0 < x) (hu0 : 0 ≤ u) (hu1 : u < 1) :
    x * (x - 1) / (u + (1 - u) * x) =
      (1 / (1 - u)) * x - 1 / (1 - u) ^ 2 +
        (u / (1 - u) ^ 3) * (x + u / (1 - u))⁻¹ := by
  have hαpos : 0 < 1 - u := by linarith
  have hα : 1 - u ≠ 0 := ne_of_gt hαpos
  have hshift : 0 < x + u / (1 - u) := by positivity
  have hshift_ne : x + u / (1 - u) ≠ 0 := ne_of_gt hshift
  have hden : u + (1 - u) * x ≠ 0 := by
    have hden_pos : 0 < u + (1 - u) * x :=
      add_pos_of_nonneg_of_pos hu0 (mul_pos hαpos hx)
    exact ne_of_gt hden_pos
  field_simp [hα, hshift_ne, hden]
  ring

/-- CFC lift of the actual `x log x` normalized-kernel integrand.

This is the matrix-valued version of
`real_unit_interval_xlog_kernel_integrand_eq_affine_add_shifted_inv`; unlike
the auxiliary `(x - 1)^2` integrand, this is the integrand whose scalar
integral reconstructs `x log x`. -/
theorem cstarMatrix_cfc_unit_interval_xlog_kernel_integrand_eq_affine_add_shifted_inv
    {ι : Type*} [Fintype ι] [DecidableEq ι]
    {A : CStarMatrix ι ι ℂ} (hA : IsStrictlyPositive A)
    {u : ℝ} (hu0 : 0 ≤ u) (hu1 : u < 1) :
    cfc (p := IsSelfAdjoint)
        (fun x : ℝ => x * (x - 1) / (u + (1 - u) * x)) A =
      (1 / (1 - u)) • A -
        (1 / (1 - u) ^ 2) • (1 : CStarMatrix ι ι ℂ) +
        (u / (1 - u) ^ 3) •
          cfc (p := IsSelfAdjoint)
            (fun x : ℝ => (x + u / (1 - u))⁻¹) A := by
  have hαpos : 0 < 1 - u := by linarith
  have hshift_nonneg : 0 ≤ u / (1 - u) :=
    div_nonneg hu0 (le_of_lt hαpos)
  have hpos_spectrum : ∀ x ∈ spectrum ℝ A, 0 < x := by
    intro x hx
    have hx_nonneg : 0 ≤ x := cstarMatrix_spectrum_nonneg_of_nonneg hA.nonneg hx
    have hx_ne : x ≠ 0 := by
      intro hxeq
      exact (spectrum.zero_notMem ℝ hA.isUnit) (by simpa [hxeq] using hx)
    exact lt_of_le_of_ne hx_nonneg (Ne.symm hx_ne)
  have hshift_cont :
      ContinuousOn (fun x : ℝ => (x + u / (1 - u))⁻¹) (spectrum ℝ A) := by
    refine ContinuousOn.inv₀ (by fun_prop) ?_
    intro x hx hzero
    have hx_pos : 0 < x := hpos_spectrum x hx
    have hsum_pos : 0 < x + u / (1 - u) :=
      add_pos_of_pos_of_nonneg hx_pos hshift_nonneg
    exact ne_of_gt hsum_pos hzero
  have hlinear :
      cfc (p := IsSelfAdjoint)
          (fun x : ℝ => (1 / (1 - u)) * x - 1 / (1 - u) ^ 2) A =
        (1 / (1 - u)) • A -
          (1 / (1 - u) ^ 2) • (1 : CStarMatrix ι ι ℂ) := by
    have hfun :
        (fun x : ℝ => (1 / (1 - u)) * x - 1 / (1 - u) ^ 2) =
          (fun x : ℝ => (1 / (1 - u)) * x - ((1 - u) ^ 2)⁻¹) := by
      ext x
      have hsq : 1 / (1 - u) ^ 2 = (((1 - u) ^ 2)⁻¹ : ℝ) := by
        rw [one_div]
      rw [hsq]
    rw [hfun]
    rw [cfc_sub
      (f := fun x : ℝ => (1 / (1 - u)) * x)
      (g := fun _ : ℝ => ((1 - u) ^ 2)⁻¹) (a := A)
      (hf := by fun_prop) (hg := by fun_prop)]
    have hmulid :
        cfc (p := IsSelfAdjoint) (fun x : ℝ => (1 / (1 - u)) * x) A =
          (1 / (1 - u)) • A := by
      simpa using
        (cfc_const_mul_id (R := ℝ) (A := CStarMatrix ι ι ℂ)
          (p := IsSelfAdjoint) (r := 1 / (1 - u)) (a := A)
          (ha := hA.isSelfAdjoint))
    have hconst :
        cfc (p := IsSelfAdjoint) (fun _ : ℝ => ((1 - u) ^ 2)⁻¹) A =
          (((1 - u) ^ 2)⁻¹) • (1 : CStarMatrix ι ι ℂ) := by
      simpa [Algebra.algebraMap_eq_smul_one] using
        (cfc_const (p := IsSelfAdjoint) (((1 - u) ^ 2)⁻¹) A hA.isSelfAdjoint)
    rw [hmulid, hconst]
    simp [one_div]
  have hshift_scaled :
      cfc (p := IsSelfAdjoint)
          (fun x : ℝ => (u / (1 - u) ^ 3) *
            (x + u / (1 - u))⁻¹) A =
        (u / (1 - u) ^ 3) •
          cfc (p := IsSelfAdjoint)
            (fun x : ℝ => (x + u / (1 - u))⁻¹) A := by
    rw [cfc_const_mul (R := ℝ) (A := CStarMatrix ι ι ℂ)
      (p := IsSelfAdjoint) (r := u / (1 - u) ^ 3)
      (f := fun x : ℝ => (x + u / (1 - u))⁻¹) (a := A)
      (hf := hshift_cont)]
  have hcongr :
      cfc (p := IsSelfAdjoint)
          (fun x : ℝ => x * (x - 1) / (u + (1 - u) * x)) A =
        cfc (p := IsSelfAdjoint)
          (fun x : ℝ =>
            (1 / (1 - u)) * x - 1 / (1 - u) ^ 2 +
              (u / (1 - u) ^ 3) * (x + u / (1 - u))⁻¹) A := by
    refine cfc_congr ?_
    intro x hx
    exact real_unit_interval_xlog_kernel_integrand_eq_affine_add_shifted_inv
      (hpos_spectrum x hx) hu0 hu1
  rw [hcongr]
  calc
    cfc (p := IsSelfAdjoint)
        (fun x : ℝ =>
          (1 / (1 - u)) * x - 1 / (1 - u) ^ 2 +
            (u / (1 - u) ^ 3) * (x + u / (1 - u))⁻¹) A =
        cfc (p := IsSelfAdjoint)
            (fun x : ℝ => (1 / (1 - u)) * x - 1 / (1 - u) ^ 2) A +
          cfc (p := IsSelfAdjoint)
            (fun x : ℝ => (u / (1 - u) ^ 3) *
              (x + u / (1 - u))⁻¹) A := by
          rw [cfc_add
            (f := fun x : ℝ => (1 / (1 - u)) * x - 1 / (1 - u) ^ 2)
            (g := fun x : ℝ => (u / (1 - u) ^ 3) *
              (x + u / (1 - u))⁻¹) (a := A)
            (hf := by fun_prop)
            (hg := ContinuousOn.const_mul hshift_cont _)]
    _ = (1 / (1 - u)) • A -
        (1 / (1 - u) ^ 2) • (1 : CStarMatrix ι ι ℂ) +
        (u / (1 - u) ^ 3) •
          cfc (p := IsSelfAdjoint)
            (fun x : ℝ => (x + u / (1 - u))⁻¹) A := by
          rw [hlinear, hshift_scaled]

/-- The unital CFC kernel `x ↦ 1 - (1 + x)⁻¹` is operator-monotone on
the nonnegative cone of finite complex C-star matrices.

This is the C-star-matrix version of the inverse-kernel monotonicity used in
the standard integral-representation proof that logarithmic kernels are
operator-monotone.  It avoids the non-unital CFC API and works in the same
unital CFC vocabulary as the surrounding Lieb/Tropp route. -/
theorem cstarMatrix_cfc_one_sub_one_add_inv_monotone
    {ι : Type*} [Fintype ι] [DecidableEq ι]
    {A B : CStarMatrix ι ι ℂ} (hA : 0 ≤ A) (hB : 0 ≤ B) (hAB : A ≤ B) :
    cfc (p := IsSelfAdjoint) (fun x : ℝ => 1 - (1 + x)⁻¹) A ≤
      cfc (p := IsSelfAdjoint) (fun x : ℝ => 1 - (1 + x)⁻¹) B := by
  have hone : IsStrictlyPositive (1 : CStarMatrix ι ι ℂ) := by
    simp
  have hAstrict : IsStrictlyPositive (1 + A : CStarMatrix ι ι ℂ) :=
    hone.add_nonneg hA
  have hBstrict : IsStrictlyPositive (1 + B : CStarMatrix ι ι ℂ) :=
    hone.add_nonneg hB
  let uA : (CStarMatrix ι ι ℂ)ˣ := hAstrict.isUnit.unit
  let uB : (CStarMatrix ι ι ℂ)ˣ := hBstrict.isUnit.unit
  have huA : (uA : CStarMatrix ι ι ℂ) = 1 + A :=
    hAstrict.isUnit.unit_spec
  have huB : (uB : CStarMatrix ι ι ℂ) = 1 + B :=
    hBstrict.isUnit.unit_spec
  have hAB1 : (uA : CStarMatrix ι ι ℂ) ≤ uB := by
    rw [huA, huB]
    simpa [add_comm, add_left_comm, add_assoc] using
      add_le_add_right hAB (1 : CStarMatrix ι ι ℂ)
  have hinv : (↑uB⁻¹ : CStarMatrix ι ι ℂ) ≤ uA⁻¹ := by
    exact CStarAlgebra.inv_le_inv (a := uA) (b := uB)
      (by simpa [huA] using hAstrict.nonneg) hAB1
  have horder :
      1 - (↑uA⁻¹ : CStarMatrix ι ι ℂ) ≤
        1 - (↑uB⁻¹ : CStarMatrix ι ι ℂ) := by
    have hdiff :
        0 ≤ (↑uA⁻¹ : CStarMatrix ι ι ℂ) -
          (↑uB⁻¹ : CStarMatrix ι ι ℂ) :=
      sub_nonneg.mpr hinv
    rw [← sub_nonneg]
    convert hdiff using 1
    abel
  have oneSub_eq (C : CStarMatrix ι ι ℂ) (hC : 0 ≤ C) :
      cfc (p := IsSelfAdjoint) (fun x : ℝ => 1 - (1 + x)⁻¹) C =
        1 - cfc (p := IsSelfAdjoint) (fun x : ℝ => x⁻¹)
          (1 + C : CStarMatrix ι ι ℂ) := by
    have hginvC : ContinuousOn (fun x : ℝ => (1 + x)⁻¹) (spectrum ℝ C) := by
      refine ContinuousOn.inv₀ (by fun_prop) ?_
      intro x hx hzero
      have hx_nonneg : 0 ≤ x := cstarMatrix_spectrum_nonneg_of_nonneg hC hx
      linarith
    have hinv_shiftC :
        ContinuousOn (fun x : ℝ => x⁻¹) ((fun x : ℝ => 1 + x) '' spectrum ℝ C) := by
      refine ContinuousOn.inv₀ (by fun_prop) ?_
      rintro y ⟨x, hx, rfl⟩ hzero
      have hx_nonneg : 0 ≤ x := cstarMatrix_spectrum_nonneg_of_nonneg hC hx
      linarith
    have hcomp :
        cfc (p := IsSelfAdjoint) (fun x : ℝ => (1 + x)⁻¹) C =
          cfc (p := IsSelfAdjoint) (fun x : ℝ => x⁻¹)
            (cfc (p := IsSelfAdjoint) (fun x : ℝ => 1 + x) C) := by
      rw [cfc_comp' (g := fun x : ℝ => x⁻¹) (f := fun x : ℝ => 1 + x)
        (a := C) (hg := hinv_shiftC)]
    have hadd :
        cfc (p := IsSelfAdjoint) (fun x : ℝ => 1 + x) C =
          (1 + C : CStarMatrix ι ι ℂ) := by
      rw [cfc_add (f := fun _ : ℝ => 1) (g := fun x : ℝ => x) (a := C)
        (hf := by fun_prop) (hg := by fun_prop)]
      rw [cfc_const_one ℝ C, cfc_id' ℝ C]
    calc
      cfc (p := IsSelfAdjoint) (fun x : ℝ => 1 - (1 + x)⁻¹) C
          = cfc (p := IsSelfAdjoint) (fun _ : ℝ => 1) C -
              cfc (p := IsSelfAdjoint) (fun x : ℝ => (1 + x)⁻¹) C := by
              rw [cfc_sub (f := fun _ : ℝ => 1)
                (g := fun x : ℝ => (1 + x)⁻¹) (a := C)
                (hf := by fun_prop) (hg := hginvC)]
      _ = 1 - cfc (p := IsSelfAdjoint) (fun x : ℝ => x⁻¹)
            (1 + C : CStarMatrix ι ι ℂ) := by
              rw [cfc_const_one ℝ C]
              rw [hcomp, hadd]
  have hAe :
      cfc (p := IsSelfAdjoint) (fun x : ℝ => 1 - (1 + x)⁻¹) A =
        1 - (↑uA⁻¹ : CStarMatrix ι ι ℂ) := by
    rw [oneSub_eq A hA]
    rw [← huA]
    rw [cfc_inv_id (a := uA) (R := ℝ)
      (ha := by simpa [huA] using IsSelfAdjoint.of_nonneg hAstrict.nonneg)]
  have hBe :
      cfc (p := IsSelfAdjoint) (fun x : ℝ => 1 - (1 + x)⁻¹) B =
        1 - (↑uB⁻¹ : CStarMatrix ι ι ℂ) := by
    rw [oneSub_eq B hB]
    rw [← huB]
    rw [cfc_inv_id (a := uB) (R := ℝ)
      (ha := by simpa [huB] using IsSelfAdjoint.of_nonneg hBstrict.nonneg)]
  simpa [hAe, hBe] using horder

/-- The fractional kernel `x ↦ x / (1 + x)` is operator-monotone on the
nonnegative cone of finite complex C-star matrices.

This is a directly usable integrand form of
`cstarMatrix_cfc_one_sub_one_add_inv_monotone`, since
`x / (1 + x) = 1 - (1 + x)⁻¹` on the nonnegative spectrum. -/
theorem cstarMatrix_cfc_pos_over_one_add_monotone
    {ι : Type*} [Fintype ι] [DecidableEq ι]
    {A B : CStarMatrix ι ι ℂ} (hA : 0 ≤ A) (hB : 0 ≤ B) (hAB : A ≤ B) :
    cfc (p := IsSelfAdjoint) (fun x : ℝ => x / (1 + x)) A ≤
      cfc (p := IsSelfAdjoint) (fun x : ℝ => x / (1 + x)) B := by
  have hmono := cstarMatrix_cfc_one_sub_one_add_inv_monotone (ι := ι) hA hB hAB
  have hAe :
      cfc (p := IsSelfAdjoint) (fun x : ℝ => x / (1 + x)) A =
        cfc (p := IsSelfAdjoint) (fun x : ℝ => 1 - (1 + x)⁻¹) A := by
    refine cfc_congr ?_
    intro x hx
    have hx_nonneg : 0 ≤ x := cstarMatrix_spectrum_nonneg_of_nonneg hA hx
    have hden : 1 + x ≠ 0 := ne_of_gt (by linarith : 0 < 1 + x)
    field_simp [hden]
    ring
  have hBe :
      cfc (p := IsSelfAdjoint) (fun x : ℝ => x / (1 + x)) B =
        cfc (p := IsSelfAdjoint) (fun x : ℝ => 1 - (1 + x)⁻¹) B := by
    refine cfc_congr ?_
    intro x hx
    have hx_nonneg : 0 ≤ x := cstarMatrix_spectrum_nonneg_of_nonneg hB hx
    have hden : 1 + x ≠ 0 := ne_of_gt (by linarith : 0 < 1 + x)
    field_simp [hden]
    ring
  simpa [hAe, hBe] using hmono

/-- The scaled fractional kernel `x ↦ x / (s + x)` is operator-monotone on
the nonnegative cone of finite complex C-star matrices, for every `s > 0`.

This is the next integrand form needed by the logarithmic-kernel
integral-representation route. -/
theorem cstarMatrix_cfc_pos_over_pos_add_monotone
    {ι : Type*} [Fintype ι] [DecidableEq ι]
    {s : ℝ} (hs : 0 < s)
    {A B : CStarMatrix ι ι ℂ} (hA : 0 ≤ A) (hB : 0 ≤ B) (hAB : A ≤ B) :
    cfc (p := IsSelfAdjoint) (fun x : ℝ => x / (s + x)) A ≤
      cfc (p := IsSelfAdjoint) (fun x : ℝ => x / (s + x)) B := by
  let r : ℝ := s⁻¹
  have hr_pos : 0 < r := inv_pos.mpr hs
  have hr_nonneg : 0 ≤ r := le_of_lt hr_pos
  have hA' : 0 ≤ r • A :=
    cstarMatrix_nonneg_nonneg_real_smul (ι := ι) hr_nonneg hA
  have hB' : 0 ≤ r • B :=
    cstarMatrix_nonneg_nonneg_real_smul (ι := ι) hr_nonneg hB
  have hAB' : r • A ≤ r • B := by
    change ((r : ℂ) • A) ≤ ((r : ℂ) • B)
    exact smul_le_smul_of_nonneg_left hAB
      (show 0 ≤ (r : ℂ) by exact_mod_cast hr_nonneg)
  have hmono :=
    cstarMatrix_cfc_pos_over_one_add_monotone
      (ι := ι) (A := r • A) (B := r • B) hA' hB' hAB'
  have hcontA :
      ContinuousOn (fun y : ℝ => y / (1 + y))
        ((fun x : ℝ => r * x) '' spectrum ℝ A) := by
    refine ContinuousOn.div (by fun_prop) (by fun_prop) ?_
    rintro y ⟨x, hx, rfl⟩ hzero
    have hx_nonneg : 0 ≤ x := cstarMatrix_spectrum_nonneg_of_nonneg hA hx
    have hden_pos : 0 < 1 + r * x := by nlinarith [mul_nonneg hr_nonneg hx_nonneg]
    exact ne_of_gt hden_pos hzero
  have hcontB :
      ContinuousOn (fun y : ℝ => y / (1 + y))
        ((fun x : ℝ => r * x) '' spectrum ℝ B) := by
    refine ContinuousOn.div (by fun_prop) (by fun_prop) ?_
    rintro y ⟨x, hx, rfl⟩ hzero
    have hx_nonneg : 0 ≤ x := cstarMatrix_spectrum_nonneg_of_nonneg hB hx
    have hden_pos : 0 < 1 + r * x := by nlinarith [mul_nonneg hr_nonneg hx_nonneg]
    exact ne_of_gt hden_pos hzero
  have scaled_eq (C : CStarMatrix ι ι ℂ) (hC : 0 ≤ C)
      (hcont :
        ContinuousOn (fun y : ℝ => y / (1 + y))
          ((fun x : ℝ => r * x) '' spectrum ℝ C)) :
      cfc (p := IsSelfAdjoint) (fun x : ℝ => x / (s + x)) C =
        cfc (p := IsSelfAdjoint) (fun x : ℝ => x / (1 + x)) (r • C) := by
    calc
      cfc (p := IsSelfAdjoint) (fun x : ℝ => x / (s + x)) C =
          cfc (p := IsSelfAdjoint) (fun x : ℝ => (r * x) / (1 + r * x)) C := by
            refine cfc_congr ?_
            intro x hx
            have hx_nonneg : 0 ≤ x := cstarMatrix_spectrum_nonneg_of_nonneg hC hx
            have hs_ne : s ≠ 0 := ne_of_gt hs
            have hden : s + x ≠ 0 := ne_of_gt (by linarith : 0 < s + x)
            have hden_scaled : 1 + r * x ≠ 0 := by
              have hpos : 0 < 1 + r * x := by nlinarith [mul_nonneg hr_nonneg hx_nonneg]
              exact ne_of_gt hpos
            field_simp [r, hs_ne, hden, hden_scaled]
            have hrs : r * s = 1 := by
              dsimp [r]
              field_simp [hs_ne]
            nlinarith [hrs]
      _ = cfc (p := IsSelfAdjoint) (fun x : ℝ => x / (1 + x)) (r • C) := by
            simpa using
              (cfc_comp_const_mul (r := r)
                (f := fun y : ℝ => y / (1 + y)) (a := C) (hf := hcont)
                (ha := IsSelfAdjoint.of_nonneg hC))
  have hAe := scaled_eq A hA hcontA
  have hBe := scaled_eq B hB hcontB
  simpa [hAe, hBe] using hmono

/-- Interior unit-interval fractional kernels are operator-monotone.

For `0 < u < 1`, the kernel
`x ↦ x / (u + (1 - u) x)` is a positive scalar multiple of
`x ↦ x / (s + x)` with `s = u / (1 - u)`.  This is the pointwise
operator-monotonicity side of the scalar logarithmic integral identity; the
endpoint/a.e. and concrete `cfc_integral` side-condition discharge remain
separate. -/
theorem cstarMatrix_cfc_unit_interval_fractional_kernel_monotone
    {ι : Type*} [Fintype ι] [DecidableEq ι]
    {u : ℝ} (hu0 : 0 < u) (hu1 : u < 1)
    {A B : CStarMatrix ι ι ℂ} (hA : 0 ≤ A) (hB : 0 ≤ B) (hAB : A ≤ B) :
    cfc (p := IsSelfAdjoint) (fun x : ℝ => x / (u + (1 - u) * x)) A ≤
      cfc (p := IsSelfAdjoint) (fun x : ℝ => x / (u + (1 - u) * x)) B := by
  let s : ℝ := u / (1 - u)
  have hden_pos : 0 < 1 - u := by linarith
  have hs : 0 < s := div_pos hu0 hden_pos
  have hscale_nonneg : 0 ≤ (1 - u)⁻¹ := by positivity
  have hs_mul : s * (1 - u) = u := by
    dsimp [s]
    field_simp [ne_of_gt hden_pos]
  have hbase :=
    cstarMatrix_cfc_pos_over_pos_add_monotone
      (ι := ι) (s := s) hs hA hB hAB
  have hcontBase (C : CStarMatrix ι ι ℂ) (hC : 0 ≤ C) :
      ContinuousOn (fun x : ℝ => x / (s + x)) (spectrum ℝ C) := by
    refine ContinuousOn.div (by fun_prop) (by fun_prop) ?_
    intro x hx hzero
    have hx_nonneg : 0 ≤ x := cstarMatrix_spectrum_nonneg_of_nonneg hC hx
    have hden : 0 < s + x := by linarith
    exact ne_of_gt hden hzero
  have scaled_eq (C : CStarMatrix ι ι ℂ) (hC : 0 ≤ C) :
      cfc (p := IsSelfAdjoint) (fun x : ℝ => x / (u + (1 - u) * x)) C =
        (1 - u)⁻¹ •
          cfc (p := IsSelfAdjoint) (fun x : ℝ => x / (s + x)) C := by
    calc
      cfc (p := IsSelfAdjoint) (fun x : ℝ => x / (u + (1 - u) * x)) C =
          cfc (p := IsSelfAdjoint)
            (fun x : ℝ => (1 - u)⁻¹ * (x / (s + x))) C := by
            refine cfc_congr ?_
            intro x hx
            have hx_nonneg : 0 ≤ x := cstarMatrix_spectrum_nonneg_of_nonneg hC hx
            have hden1 : u + (1 - u) * x ≠ 0 := by
              have hpos : 0 < u + (1 - u) * x := by
                nlinarith [mul_nonneg (le_of_lt hden_pos) hx_nonneg]
              exact ne_of_gt hpos
            have hden2 : s + x ≠ 0 := by
              have hpos : 0 < s + x := by linarith
              exact ne_of_gt hpos
            field_simp [hden1, hden2, ne_of_gt hden_pos]
            nlinarith [hs_mul]
      _ = (1 - u)⁻¹ •
            cfc (p := IsSelfAdjoint) (fun x : ℝ => x / (s + x)) C := by
            rw [cfc_const_mul (r := (1 - u)⁻¹)
              (f := fun x : ℝ => x / (s + x)) (a := C)
              (hf := hcontBase C hC)]
  rw [scaled_eq A hA, scaled_eq B hB]
  exact smul_le_smul_of_nonneg_left hbase hscale_nonneg

/-- Unit-interval fractional kernels are operator-monotone on the strictly
positive cone, including the endpoints.

The endpoint `u = 0` is the constant-one CFC kernel on strictly positive
spectra, and `u = 1` is the identity kernel.  The interior case is
`cstarMatrix_cfc_unit_interval_fractional_kernel_monotone`. -/
theorem cstarMatrix_cfc_unit_interval_fractional_kernel_monotone_of_mem_Icc
    {ι : Type*} [Fintype ι] [DecidableEq ι]
    {u : ℝ} (hu0 : 0 ≤ u) (hu1 : u ≤ 1)
    {A B : CStarMatrix ι ι ℂ}
    (hA : IsStrictlyPositive A) (hB : IsStrictlyPositive B) (hAB : A ≤ B) :
    cfc (p := IsSelfAdjoint) (fun x : ℝ => x / (u + (1 - u) * x)) A ≤
      cfc (p := IsSelfAdjoint) (fun x : ℝ => x / (u + (1 - u) * x)) B := by
  have hzero_eq (C : CStarMatrix ι ι ℂ) (hC : IsStrictlyPositive C) :
      cfc (p := IsSelfAdjoint)
          (fun x : ℝ => x / ((0 : ℝ) + (1 - (0 : ℝ)) * x)) C =
        (1 : CStarMatrix ι ι ℂ) := by
    calc
      cfc (p := IsSelfAdjoint)
          (fun x : ℝ => x / ((0 : ℝ) + (1 - (0 : ℝ)) * x)) C =
          cfc (p := IsSelfAdjoint) (fun _x : ℝ => (1 : ℝ)) C := by
            refine cfc_congr ?_
            intro x hx
            have hx0 : x ≠ 0 := by
              intro hxeq
              exact (spectrum.zero_notMem ℝ hC.isUnit) (by simpa [hxeq] using hx)
            field_simp [hx0]
            ring
      _ = 1 := by rw [cfc_const_one ℝ C]
  have hone_eq (C : CStarMatrix ι ι ℂ) (hC : IsStrictlyPositive C) :
      cfc (p := IsSelfAdjoint)
          (fun x : ℝ => x / ((1 : ℝ) + (1 - (1 : ℝ)) * x)) C = C := by
    calc
      cfc (p := IsSelfAdjoint)
          (fun x : ℝ => x / ((1 : ℝ) + (1 - (1 : ℝ)) * x)) C =
          cfc (p := IsSelfAdjoint) (fun x : ℝ => x) C := by
            refine cfc_congr ?_
            intro x _hx
            field_simp
            ring
      _ = C := by simpa using (cfc_id' ℝ C hC.isSelfAdjoint)
  by_cases h0 : u = 0
  · subst u
    rw [hzero_eq A hA, hzero_eq B hB]
  by_cases h1 : u = 1
  · subst u
    rw [hone_eq A hA, hone_eq B hB]
    exact hAB
  have hu0lt : 0 < u := lt_of_le_of_ne hu0 (Ne.symm h0)
  have hu1lt : u < 1 := lt_of_le_of_ne hu1 h1
  exact cstarMatrix_cfc_unit_interval_fractional_kernel_monotone
    (ι := ι) hu0lt hu1lt hA.nonneg hB.nonneg hAB

open Set Function in
/-- Joint continuity of the unit-interval logarithmic-integral kernel on a
strictly positive spectrum.

This is one of the concrete `cfc_integral` side conditions for the normalized
logarithmic-kernel route. -/
theorem continuousOn_uncurry_unit_interval_fractional_kernel_spectrum
    {ι : Type*} [Fintype ι] [DecidableEq ι]
    {A : CStarMatrix ι ι ℂ} (hA : IsStrictlyPositive A) :
    ContinuousOn (uncurry (fun u x : ℝ => x / (u + (1 - u) * x)))
      (Set.Icc (0 : ℝ) 1 ×ˢ spectrum ℝ A) := by
  refine ContinuousOn.div ?_ ?_ ?_
  · fun_prop
  · fun_prop
  · rintro ⟨u, x⟩ hux hzero
    rcases hux with ⟨hu, hx⟩
    have hx_nonneg : 0 ≤ x := cstarMatrix_spectrum_nonneg_of_nonneg hA.nonneg hx
    have hx_ne : x ≠ 0 := by
      intro hxeq
      exact (spectrum.zero_notMem ℝ hA.isUnit) (by simpa [hxeq] using hx)
    have hx_pos : 0 < x := lt_of_le_of_ne hx_nonneg (Ne.symm hx_ne)
    have hu1 : u ≤ 1 := hu.2
    have hden_pos : 0 < u + (1 - u) * x := by
      nlinarith [mul_nonneg (sub_nonneg.mpr hu1) (le_of_lt hx_pos), hu.1]
    exact ne_of_gt hden_pos hzero

open Set Function in
/-- Joint continuity of the actual `x log x` unit-interval kernel on a
strictly positive spectrum. -/
theorem continuousOn_uncurry_unit_interval_xlog_kernel_spectrum
    {ι : Type*} [Fintype ι] [DecidableEq ι]
    {A : CStarMatrix ι ι ℂ} (hA : IsStrictlyPositive A) :
    ContinuousOn
      (uncurry (fun u x : ℝ => x * (x - 1) / (u + (1 - u) * x)))
      (Set.Icc (0 : ℝ) 1 ×ˢ spectrum ℝ A) := by
  refine ContinuousOn.div ?_ ?_ ?_
  · fun_prop
  · fun_prop
  · rintro ⟨u, x⟩ hux hzero
    rcases hux with ⟨hu, hx⟩
    have hx_nonneg : 0 ≤ x := cstarMatrix_spectrum_nonneg_of_nonneg hA.nonneg hx
    have hx_ne : x ≠ 0 := by
      intro hxeq
      exact (spectrum.zero_notMem ℝ hA.isUnit) (by simpa [hxeq] using hx)
    have hx_pos : 0 < x := lt_of_le_of_ne hx_nonneg (Ne.symm hx_ne)
    have hu1 : u ≤ 1 := hu.2
    have hden_pos : 0 < u + (1 - u) * x := by
      nlinarith [mul_nonneg (sub_nonneg.mpr hu1) (le_of_lt hx_pos), hu.1]
    exact ne_of_gt hden_pos hzero

/-- Uniform scalar bound for the unit-interval fractional kernel.

For `u ∈ [0,1]` and `0 < z ≤ M`,
`z / (u + (1 - u) z)` lies below `max 1 M`.  This is the scalar
boundedness estimate needed by the concrete `cfc_integral` side-condition
discharge in the normalized logarithmic-kernel route. -/
theorem real_unit_interval_fractional_kernel_abs_le_max_of_le
    {u z M : ℝ} (hu0 : 0 ≤ u) (hu1 : u ≤ 1) (hz : 0 < z) (hM : z ≤ M) :
    |z / (u + (1 - u) * z)| ≤ max 1 M := by
  have hden_pos : 0 < u + (1 - u) * z := by
    by_cases hu_zero : u = 0
    · subst u
      simpa using hz
    · have hu_pos : 0 < u := lt_of_le_of_ne hu0 (Ne.symm hu_zero)
      have hterm_nonneg : 0 ≤ (1 - u) * z :=
        mul_nonneg (sub_nonneg.mpr hu1) (le_of_lt hz)
      nlinarith
  have hratio_nonneg : 0 ≤ z / (u + (1 - u) * z) :=
    div_nonneg (le_of_lt hz) (le_of_lt hden_pos)
  rw [abs_of_nonneg hratio_nonneg]
  by_cases hzle : z ≤ 1
  · have hd_ge_z : z ≤ u + (1 - u) * z := by
      have hnonneg : 0 ≤ u * (1 - z) :=
        mul_nonneg hu0 (sub_nonneg.mpr hzle)
      nlinarith
    have hratio_le_one : z / (u + (1 - u) * z) ≤ 1 :=
      (div_le_iff₀ hden_pos).mpr (by simpa using hd_ge_z)
    exact le_trans hratio_le_one (le_max_left 1 M)
  · have h1z : 1 ≤ z := le_of_lt (lt_of_not_ge hzle)
    have hd_ge_one : 1 ≤ u + (1 - u) * z := by
      have hnonneg : 0 ≤ (1 - u) * (z - 1) :=
        mul_nonneg (sub_nonneg.mpr hu1) (sub_nonneg.mpr h1z)
      nlinarith
    have hratio_le_z : z / (u + (1 - u) * z) ≤ z := by
      have hzle_zd : z ≤ z * (u + (1 - u) * z) := by
        simpa using mul_le_mul_of_nonneg_left hd_ge_one (le_of_lt hz)
      exact (div_le_iff₀ hden_pos).mpr (by simpa [mul_comm] using hzle_zd)
    exact le_trans hratio_le_z (le_trans hM (le_max_right 1 M))

/-- If `0 < z ≤ M`, then `|z - 1|` is bounded by `max 1 M`. -/
theorem real_abs_sub_one_le_max_one_of_pos_le
    {z M : ℝ} (hz : 0 < z) (hM : z ≤ M) :
    |z - 1| ≤ max 1 M := by
  by_cases hzle : z ≤ 1
  · have hnonpos : z - 1 ≤ 0 := by linarith
    rw [abs_of_nonpos hnonpos]
    exact le_trans (by linarith : -(z - 1) ≤ 1) (le_max_left 1 M)
  · have hnonneg : 0 ≤ z - 1 := by linarith
    rw [abs_of_nonneg hnonneg]
    exact le_trans (by linarith : z - 1 ≤ z) (le_trans hM (le_max_right 1 M))

/-- Uniform scalar bound for the actual `x log x` unit-interval kernel. -/
theorem real_unit_interval_xlog_kernel_abs_le_max_sq_of_le
    {u z M : ℝ} (hu0 : 0 ≤ u) (hu1 : u ≤ 1) (hz : 0 < z) (hM : z ≤ M) :
    |z * (z - 1) / (u + (1 - u) * z)| ≤ (max 1 M) ^ 2 := by
  have hfrac :=
    real_unit_interval_fractional_kernel_abs_le_max_of_le hu0 hu1 hz hM
  have hsub := real_abs_sub_one_le_max_one_of_pos_le hz hM
  have hmax_nonneg : 0 ≤ max 1 M := le_trans zero_le_one (le_max_left 1 M)
  have hrewrite :
      z * (z - 1) / (u + (1 - u) * z) =
        (z / (u + (1 - u) * z)) * (z - 1) := by
    ring
  rw [hrewrite, abs_mul]
  simpa [sq] using
    mul_le_mul hfrac hsub (abs_nonneg (z - 1)) hmax_nonneg

open Set Function in
/-- Spectrum-specialized boundedness estimate for the unit-interval
fractional kernel.

If `A` is strictly positive and `M` bounds its real spectrum from above, then
the integrand `z / (u + (1 - u) z)` is uniformly bounded by `max 1 M` on
`u ∈ [0,1]` and `z ∈ spectrum ℝ A`. -/
theorem real_unit_interval_fractional_kernel_spectrum_norm_le_max
    {ι : Type*} [Fintype ι] [DecidableEq ι]
    {A : CStarMatrix ι ι ℂ} (hA : IsStrictlyPositive A)
    {u z M : ℝ} (hu : u ∈ Set.Icc (0 : ℝ) 1) (hz : z ∈ spectrum ℝ A)
    (hM : ∀ y ∈ spectrum ℝ A, y ≤ M) :
    ‖z / (u + (1 - u) * z)‖ ≤ max 1 M := by
  change |z / (u + (1 - u) * z)| ≤ max 1 M
  have hz_nonneg : 0 ≤ z := cstarMatrix_spectrum_nonneg_of_nonneg hA.nonneg hz
  have hz_ne : z ≠ 0 := by
    intro hzeq
    exact (spectrum.zero_notMem ℝ hA.isUnit) (by simpa [hzeq] using hz)
  have hz_pos : 0 < z := lt_of_le_of_ne hz_nonneg (Ne.symm hz_ne)
  exact real_unit_interval_fractional_kernel_abs_le_max_of_le
    hu.1 hu.2 hz_pos (hM z hz)

open Set Function in
/-- Spectrum-specialized boundedness estimate for the actual `x log x`
unit-interval kernel. -/
theorem real_unit_interval_xlog_kernel_spectrum_norm_le_max_sq
    {ι : Type*} [Fintype ι] [DecidableEq ι]
    {A : CStarMatrix ι ι ℂ} (hA : IsStrictlyPositive A)
    {u z M : ℝ} (hu : u ∈ Set.Icc (0 : ℝ) 1) (hz : z ∈ spectrum ℝ A)
    (hM : ∀ y ∈ spectrum ℝ A, y ≤ M) :
    ‖z * (z - 1) / (u + (1 - u) * z)‖ ≤ (max 1 M) ^ 2 := by
  change |z * (z - 1) / (u + (1 - u) * z)| ≤ (max 1 M) ^ 2
  have hz_nonneg : 0 ≤ z := cstarMatrix_spectrum_nonneg_of_nonneg hA.nonneg hz
  have hz_ne : z ≠ 0 := by
    intro hzeq
    exact (spectrum.zero_notMem ℝ hA.isUnit) (by simpa [hzeq] using hz)
  have hz_pos : 0 < z := lt_of_le_of_ne hz_nonneg (Ne.symm hz_ne)
  exact real_unit_interval_xlog_kernel_abs_le_max_sq_of_le
    hu.1 hu.2 hz_pos (hM z hz)

open Set Function MeasureTheory in
/-- Almost-everywhere spectrum bound for the unit-interval fractional kernel
with respect to Lebesgue measure restricted to `[0,1]`. -/
theorem ae_unit_interval_fractional_kernel_spectrum_norm_le_max
    {ι : Type*} [Fintype ι] [DecidableEq ι]
    {A : CStarMatrix ι ι ℂ} (hA : IsStrictlyPositive A) {M : ℝ}
    (hM : ∀ y ∈ spectrum ℝ A, y ≤ M) :
    ∀ᵐ u ∂((volume : Measure ℝ).restrict (Set.Icc (0 : ℝ) 1)),
      ∀ z ∈ spectrum ℝ A,
        ‖z / (u + (1 - u) * z)‖ ≤ max 1 M := by
  filter_upwards
    [self_mem_ae_restrict (measurableSet_Icc : MeasurableSet (Set.Icc (0 : ℝ) 1))]
    with u hu z hz
  exact real_unit_interval_fractional_kernel_spectrum_norm_le_max hA hu hz hM

open Set Function MeasureTheory in
/-- Almost-everywhere spectrum bound for the actual `x log x`
unit-interval kernel. -/
theorem ae_unit_interval_xlog_kernel_spectrum_norm_le_max_sq
    {ι : Type*} [Fintype ι] [DecidableEq ι]
    {A : CStarMatrix ι ι ℂ} (hA : IsStrictlyPositive A) {M : ℝ}
    (hM : ∀ y ∈ spectrum ℝ A, y ≤ M) :
    ∀ᵐ u ∂((volume : Measure ℝ).restrict (Set.Icc (0 : ℝ) 1)),
      ∀ z ∈ spectrum ℝ A,
        ‖z * (z - 1) / (u + (1 - u) * z)‖ ≤ (max 1 M) ^ 2 := by
  filter_upwards
    [self_mem_ae_restrict (measurableSet_Icc : MeasurableSet (Set.Icc (0 : ℝ) 1))]
    with u hu z hz
  exact real_unit_interval_xlog_kernel_spectrum_norm_le_max_sq hA hu hz hM

open Set MeasureTheory in
/-- The constant bound `max 1 M` has finite integral over `[0,1]`. -/
theorem hasFiniteIntegral_const_max_one_spectrum_bound (M : ℝ) :
    HasFiniteIntegral (fun _ : ℝ => max 1 M)
      ((volume : Measure ℝ).restrict (Set.Icc (0 : ℝ) 1)) := by
  exact hasFiniteIntegral_const (max 1 M)

open Set MeasureTheory in
/-- The squared constant bound `(max 1 M)^2` has finite integral over
`[0,1]`. -/
theorem hasFiniteIntegral_const_max_one_spectrum_bound_sq (M : ℝ) :
    HasFiniteIntegral (fun _ : ℝ => (max 1 M) ^ 2)
      ((volume : Measure ℝ).restrict (Set.Icc (0 : ℝ) 1)) := by
  exact hasFiniteIntegral_const ((max 1 M) ^ 2)

open Set Function in
/-- Subtype-domain continuity for the unit-interval fractional kernel.

This is the continuity side condition in the shape expected by
`cfc_integral` when the integration type is the compact interval subtype
`{u : ℝ // u ∈ [0,1]}`. -/
theorem continuousOn_uncurry_unit_interval_subtype_fractional_kernel_spectrum
    {ι : Type*} [Fintype ι] [DecidableEq ι]
    {A : CStarMatrix ι ι ℂ} (hA : IsStrictlyPositive A) :
    ContinuousOn
      (uncurry (fun u : {u : ℝ // u ∈ Set.Icc (0 : ℝ) 1} =>
        fun x : ℝ => x / (u.1 + (1 - u.1) * x)))
      (Set.univ ×ˢ spectrum ℝ A) := by
  refine ContinuousOn.div ?_ ?_ ?_
  · fun_prop
  · fun_prop
  · rintro ⟨u, x⟩ hux hzero
    rcases hux with ⟨_hu, hx⟩
    have huIcc : u.1 ∈ Set.Icc (0 : ℝ) 1 := u.2
    have hx_nonneg : 0 ≤ x := cstarMatrix_spectrum_nonneg_of_nonneg hA.nonneg hx
    have hx_ne : x ≠ 0 := by
      intro hxeq
      exact (spectrum.zero_notMem ℝ hA.isUnit) (by simpa [hxeq] using hx)
    have hx_pos : 0 < x := lt_of_le_of_ne hx_nonneg (Ne.symm hx_ne)
    have hden_pos : 0 < u.1 + (1 - u.1) * x := by
      nlinarith [mul_nonneg (sub_nonneg.mpr huIcc.2) (le_of_lt hx_pos), huIcc.1]
    exact ne_of_gt hden_pos hzero

open Set Function MeasureTheory in
/-- Almost-everywhere subtype-domain spectrum bound for the unit-interval
fractional kernel, for any measure on the interval subtype. -/
theorem ae_unit_interval_subtype_fractional_kernel_spectrum_norm_le_max
    {ι : Type*} [Fintype ι] [DecidableEq ι]
    {A : CStarMatrix ι ι ℂ} (hA : IsStrictlyPositive A) {M : ℝ}
    (hM : ∀ y ∈ spectrum ℝ A, y ≤ M)
    (μ : Measure {u : ℝ // u ∈ Set.Icc (0 : ℝ) 1}) :
    ∀ᵐ u ∂μ, ∀ z ∈ spectrum ℝ A,
        ‖z / (u.1 + (1 - u.1) * z)‖ ≤ max 1 M := by
  exact Filter.Eventually.of_forall fun u z hz =>
    real_unit_interval_fractional_kernel_spectrum_norm_le_max hA u.2 hz hM

open Set Function MeasureTheory in
/-- The constant bound `max 1 M` has finite integral for any finite measure on
the unit-interval subtype. -/
theorem hasFiniteIntegral_unit_interval_subtype_const_max_one_spectrum_bound
    (M : ℝ) (μ : Measure {u : ℝ // u ∈ Set.Icc (0 : ℝ) 1}) [IsFiniteMeasure μ] :
    HasFiniteIntegral (fun _ : {u : ℝ // u ∈ Set.Icc (0 : ℝ) 1} => max 1 M) μ := by
  exact hasFiniteIntegral_const (max 1 M)

open MeasureTheory Set Function in
/-- CFC form of the normalized logarithmic-kernel integral representation.

For a strictly positive finite C-star matrix `A`, if `M` is any scalar upper
bound for the real spectrum of `A`, then functional calculus applied to
`realNormalizedLogKernel` equals the Bochner integral of the unit-interval
fractional CFC kernels.  The `M` hypothesis is only the explicit bound needed
by mathlib's `cfc_setIntegral` API. -/
theorem cstarMatrix_cfc_realNormalizedLogKernel_eq_unit_interval_integral
    {ι : Type*} [Fintype ι] [DecidableEq ι]
    {A : CStarMatrix ι ι ℂ} (hA : IsStrictlyPositive A) {M : ℝ}
    (hM : ∀ y ∈ spectrum ℝ A, y ≤ M) :
    cfc (p := IsSelfAdjoint) realNormalizedLogKernel A =
      ∫ u in Set.Icc (0 : ℝ) 1,
        cfc (p := IsSelfAdjoint)
          (fun z : ℝ => z / (u + (1 - u) * z)) A := by
  let f : ℝ → ℝ → ℝ := fun u z => z / (u + (1 - u) * z)
  have hscalar_on_spectrum :
      ∀ z ∈ spectrum ℝ A,
        (∫ u in Set.Icc (0 : ℝ) 1, f u z) = realNormalizedLogKernel z := by
    intro z hz
    have hz_nonneg : 0 ≤ z := cstarMatrix_spectrum_nonneg_of_nonneg hA.nonneg hz
    have hz_ne : z ≠ 0 := by
      intro hzeq
      exact (spectrum.zero_notMem ℝ hA.isUnit) (by simpa [hzeq] using hz)
    have hz_pos : 0 < z := lt_of_le_of_ne hz_nonneg (Ne.symm hz_ne)
    exact realNormalizedLogKernel_setIntegral hz_pos
  calc
    cfc (p := IsSelfAdjoint) realNormalizedLogKernel A =
        cfc (p := IsSelfAdjoint)
          (fun z : ℝ => ∫ u in Set.Icc (0 : ℝ) 1, f u z) A := by
          refine cfc_congr ?_
          intro z hz
          exact (hscalar_on_spectrum z hz).symm
    _ = ∫ u in Set.Icc (0 : ℝ) 1,
        cfc (p := IsSelfAdjoint) (f u) A := by
          exact cfc_setIntegral
            (p := IsSelfAdjoint) (f := f) (bound := fun _ : ℝ => max 1 M)
            (a := A) (hs := (measurableSet_Icc : MeasurableSet (Set.Icc (0 : ℝ) 1)))
            (hf := continuousOn_uncurry_unit_interval_fractional_kernel_spectrum hA)
            (bound_ge := ae_unit_interval_fractional_kernel_spectrum_norm_le_max hA hM)
            (bound_int := hasFiniteIntegral_const_max_one_spectrum_bound M)
            (ha := hA.isSelfAdjoint)

open MeasureTheory Set Function in
/-- CFC integral representation of `x ↦ x log x` through the corrected
unit-interval kernel.

For a strictly positive finite C-star matrix `A`, functional calculus applied
to `x log x` equals the Bochner integral of the CFC kernels
`x * (x - 1) / (u + (1 - u) x)`.  The scalar upper bound `M` is only the
explicit boundedness witness required by mathlib's `cfc_setIntegral` API. -/
theorem cstarMatrix_cfc_xlog_eq_unit_interval_xlog_kernel_integral
    {ι : Type*} [Fintype ι] [DecidableEq ι]
    {A : CStarMatrix ι ι ℂ} (hA : IsStrictlyPositive A) {M : ℝ}
    (hM : ∀ y ∈ spectrum ℝ A, y ≤ M) :
    cfc (p := IsSelfAdjoint) (fun z : ℝ => z * Real.log z) A =
      ∫ u in Set.Icc (0 : ℝ) 1,
        cfc (p := IsSelfAdjoint)
          (fun z : ℝ => z * (z - 1) / (u + (1 - u) * z)) A := by
  let f : ℝ → ℝ → ℝ :=
    fun u z => z * (z - 1) / (u + (1 - u) * z)
  have hscalar_on_spectrum :
      ∀ z ∈ spectrum ℝ A,
        (∫ u in Set.Icc (0 : ℝ) 1, f u z) = z * Real.log z := by
    intro z hz
    have hz_nonneg : 0 ≤ z := cstarMatrix_spectrum_nonneg_of_nonneg hA.nonneg hz
    have hz_ne : z ≠ 0 := by
      intro hzeq
      exact (spectrum.zero_notMem ℝ hA.isUnit) (by simpa [hzeq] using hz)
    have hz_pos : 0 < z := lt_of_le_of_ne hz_nonneg (Ne.symm hz_ne)
    exact real_xlog_eq_unit_interval_xlog_kernel_integral hz_pos
  calc
    cfc (p := IsSelfAdjoint) (fun z : ℝ => z * Real.log z) A =
        cfc (p := IsSelfAdjoint)
          (fun z : ℝ => ∫ u in Set.Icc (0 : ℝ) 1, f u z) A := by
          refine cfc_congr ?_
          intro z hz
          exact (hscalar_on_spectrum z hz).symm
    _ = ∫ u in Set.Icc (0 : ℝ) 1,
        cfc (p := IsSelfAdjoint) (f u) A := by
          exact cfc_setIntegral
            (p := IsSelfAdjoint) (f := f)
            (bound := fun _ : ℝ => (max 1 M) ^ 2)
            (a := A) (hs := (measurableSet_Icc : MeasurableSet (Set.Icc (0 : ℝ) 1)))
            (hf := continuousOn_uncurry_unit_interval_xlog_kernel_spectrum hA)
            (bound_ge := ae_unit_interval_xlog_kernel_spectrum_norm_le_max_sq hA hM)
            (bound_int := hasFiniteIntegral_const_max_one_spectrum_bound_sq M)
            (ha := hA.isSelfAdjoint)

open MeasureTheory Set Function in
/-- Set-integral monotonicity specialized to finite complex C-star matrices.

The statement is just `setIntegral_mono_on`, but the local proof fixes the
matrix-order/additive-instance diamond explicitly.  This keeps later
operator-integral arguments from depending on fragile typeclass search. -/
theorem cstarMatrix_setIntegral_mono_on
    {ι X : Type*} [Fintype ι] [DecidableEq ι] [MeasurableSpace X]
    {μ : Measure X} {f g : X → CStarMatrix ι ι ℂ} {s : Set X}
    (hf : IntegrableOn f s μ) (hg : IntegrableOn g s μ)
    (hs : MeasurableSet s) (hmono : ∀ x ∈ s, f x ≤ g x) :
    ∫ x in s, f x ∂μ ≤ ∫ x in s, g x ∂μ := by
  have hadd_left :
      ∀ a b : CStarMatrix ι ι ℂ, a ≤ b → ∀ c, a + c ≤ b + c := by
    intro a b hab c
    exact add_le_add_left hab c
  have hadd_right :
      ∀ a b : CStarMatrix ι ι ℂ, a ≤ b → ∀ c, c + a ≤ c + b := by
    intro a b hab c
    exact add_le_add_right hab c
  have hsmul_left :
      ∀ ⦃a : ℝ⦄, 0 ≤ a →
        ∀ ⦃B C : CStarMatrix ι ι ℂ⦄, B ≤ C → a • B ≤ a • C := by
    intro a ha B C hBC
    change ((a : ℂ) • B) ≤ ((a : ℂ) • C)
    exact smul_le_smul_of_nonneg_left hBC
      (show 0 ≤ (a : ℂ) by exact_mod_cast ha)
  have hsmul_right :
      ∀ ⦃B : CStarMatrix ι ι ℂ⦄, 0 ≤ B →
        ∀ ⦃a b : ℝ⦄, a ≤ b → a • B ≤ b • B := by
    intro B hB a b hab
    change ((a : ℂ) • B) ≤ ((b : ℂ) • B)
    exact smul_le_smul_of_nonneg_right
      (show (a : ℂ) ≤ (b : ℂ) by exact_mod_cast hab) hB
  let hnorm : NormedAddCommGroup (CStarMatrix ι ι ℂ) := inferInstance
  let hnormspace : NormedSpace ℝ (CStarMatrix ι ι ℂ) := inferInstance
  let hpo : PartialOrder (CStarMatrix ι ι ℂ) := inferInstance
  let hclosed : ClosedIciTopology (CStarMatrix ι ι ℂ) := inferInstance
  let horderedAdd : @IsOrderedAddMonoid (CStarMatrix ι ι ℂ)
      (@AddCommGroup.toAddCommMonoid (CStarMatrix ι ι ℂ)
        (@NormedAddCommGroup.toAddCommGroup (CStarMatrix ι ι ℂ) hnorm))
      hpo.toPreorder :=
    ⟨hadd_left, hadd_right⟩
  let horderedModule : IsOrderedModule ℝ (CStarMatrix ι ι ℂ) :=
    { smul_le_smul_of_nonneg_left := by
        intro a ha B C hBC
        exact hsmul_left ha hBC
      smul_le_smul_of_nonneg_right := by
        intro B hB a b hab
        exact hsmul_right hB hab }
  exact @MeasureTheory.setIntegral_mono_on X (CStarMatrix ι ι ℂ)
    inferInstance hnorm hnormspace hpo horderedAdd horderedModule μ f g s hclosed
    hf hg hs hmono

open MeasureTheory Set Function in
/-- Compression by a fixed rectangular `CStarMatrix` commutes with Bochner
set integrals. -/
theorem cstarMatrix_compression_setIntegral
    {α β X : Type*} [Fintype α] [DecidableEq α] [Fintype β] [DecidableEq β]
    [MeasurableSpace X] {μ : Measure X} {s : Set X}
    (V : CStarMatrix α β ℂ) {f : X → CStarMatrix α α ℂ}
    (hf : IntegrableOn f s μ) :
    CStarMatrix.conjTranspose V * (∫ x in s, f x ∂μ) * V =
      ∫ x in s, CStarMatrix.conjTranspose V * f x * V ∂μ := by
  have h :=
    (cstarMatrixCompressionCLM V).integral_comp_comm
      (μ := μ.restrict s) hf
  simpa using h.symm

open MeasureTheory Set Function in
/-- Operator monotonicity of the normalized logarithmic kernel under explicit
spectral upper bounds.

This combines the scalar integral representation of
`realNormalizedLogKernel`, the CFC set-integral equality, and pointwise
operator monotonicity of the unit-interval fractional kernels. -/
theorem cstarMatrix_cfc_realNormalizedLogKernel_monotone_of_spectrum_bound
    {ι : Type*} [Fintype ι] [DecidableEq ι]
    {A B : CStarMatrix ι ι ℂ}
    (hA : IsStrictlyPositive A) (hB : IsStrictlyPositive B) (hAB : A ≤ B)
    {MA MB : ℝ}
    (hMA : ∀ y ∈ spectrum ℝ A, y ≤ MA)
    (hMB : ∀ y ∈ spectrum ℝ B, y ≤ MB) :
    cfc (p := IsSelfAdjoint) realNormalizedLogKernel A ≤
      cfc (p := IsSelfAdjoint) realNormalizedLogKernel B := by
  rw [cstarMatrix_cfc_realNormalizedLogKernel_eq_unit_interval_integral hA hMA,
    cstarMatrix_cfc_realNormalizedLogKernel_eq_unit_interval_integral hB hMB]
  let fA : ℝ → CStarMatrix ι ι ℂ :=
    fun u => cfc (p := IsSelfAdjoint)
      (fun z : ℝ => z / (u + (1 - u) * z)) A
  let fB : ℝ → CStarMatrix ι ι ℂ :=
    fun u => cfc (p := IsSelfAdjoint)
      (fun z : ℝ => z / (u + (1 - u) * z)) B
  have hAi : IntegrableOn fA (Set.Icc (0 : ℝ) 1) := by
    exact integrableOn_cfc
      (hs := (measurableSet_Icc : MeasurableSet (Set.Icc (0 : ℝ) 1)))
      (f := fun u z : ℝ => z / (u + (1 - u) * z))
      (bound := fun _ : ℝ => max 1 MA)
      (a := A)
      (hf := continuousOn_uncurry_unit_interval_fractional_kernel_spectrum hA)
      (bound_ge := ae_unit_interval_fractional_kernel_spectrum_norm_le_max hA hMA)
      (bound_int := hasFiniteIntegral_const_max_one_spectrum_bound MA)
      (ha := hA.isSelfAdjoint)
  have hBi : IntegrableOn fB (Set.Icc (0 : ℝ) 1) := by
    exact integrableOn_cfc
      (hs := (measurableSet_Icc : MeasurableSet (Set.Icc (0 : ℝ) 1)))
      (f := fun u z : ℝ => z / (u + (1 - u) * z))
      (bound := fun _ : ℝ => max 1 MB)
      (a := B)
      (hf := continuousOn_uncurry_unit_interval_fractional_kernel_spectrum hB)
      (bound_ge := ae_unit_interval_fractional_kernel_spectrum_norm_le_max hB hMB)
      (bound_int := hasFiniteIntegral_const_max_one_spectrum_bound MB)
      (ha := hB.isSelfAdjoint)
  exact cstarMatrix_setIntegral_mono_on hAi hBi measurableSet_Icc fun u hu => by
    exact cstarMatrix_cfc_unit_interval_fractional_kernel_monotone_of_mem_Icc
      hu.1 hu.2 hA hB hAB

/-- Operator monotonicity of the normalized logarithmic kernel on the strictly
positive cone.  The spectral upper bounds required by the concrete CFC
integral API are discharged from boundedness of the finite real spectra. -/
theorem cstarMatrix_cfc_realNormalizedLogKernel_monotone
    {ι : Type*} [Fintype ι] [DecidableEq ι]
    {A B : CStarMatrix ι ι ℂ}
    (hA : IsStrictlyPositive A) (hB : IsStrictlyPositive B) (hAB : A ≤ B) :
    cfc (p := IsSelfAdjoint) realNormalizedLogKernel A ≤
      cfc (p := IsSelfAdjoint) realNormalizedLogKernel B := by
  rcases (spectrum.isBounded (𝕜 := ℝ) A).bddAbove with ⟨MA, hMA⟩
  rcases (spectrum.isBounded (𝕜 := ℝ) B).bddAbove with ⟨MB, hMB⟩
  exact cstarMatrix_cfc_realNormalizedLogKernel_monotone_of_spectrum_bound
    hA hB hAB hMA hMB

/-- CFC normalization of the first divided difference of `x ↦ x log x`.

For a positive base point `c`, the divided-difference CFC equals the scalar
constant `log c` plus the normalized logarithmic kernel applied to the scaled
matrix `c⁻¹ A`. -/
theorem cstarMatrix_cfc_realXLogXDividedDifference_eq_log_add_scaled_normalizedKernel
    {ι : Type*} [Fintype ι] [DecidableEq ι]
    {A : CStarMatrix ι ι ℂ} (hA : IsStrictlyPositive A)
    {c : ℝ} (hc : 0 < c) :
    cfc (p := IsSelfAdjoint) (realXLogXDividedDifference c) A =
      algebraMap ℝ (CStarMatrix ι ι ℂ) (Real.log c) +
        cfc (p := IsSelfAdjoint) realNormalizedLogKernel ((c⁻¹) • A) := by
  have hpos_spectrum : ∀ z ∈ spectrum ℝ A, 0 < z := by
    intro z hz
    have hz_nonneg : 0 ≤ z := cstarMatrix_spectrum_nonneg_of_nonneg hA.nonneg hz
    have hz_ne : z ≠ 0 := by
      intro hzeq
      exact (spectrum.zero_notMem ℝ hA.isUnit) (by simpa [hzeq] using hz)
    exact lt_of_le_of_ne hz_nonneg (Ne.symm hz_ne)
  have hcongr :
      cfc (p := IsSelfAdjoint) (realXLogXDividedDifference c) A =
        cfc (p := IsSelfAdjoint)
          (fun z : ℝ => Real.log c + realNormalizedLogKernel (z / c)) A := by
    refine cfc_congr ?_
    intro z hz
    exact realXLogXDividedDifference_eq_log_add_normalizedKernel
      hc (hpos_spectrum z hz)
  rw [hcongr]
  have hcont_div : ContinuousOn (fun z : ℝ => realNormalizedLogKernel (z / c))
      (spectrum ℝ A) := by
    refine continuousOn_realNormalizedLogKernel_Ioi.comp ?_ ?_
    · exact ContinuousOn.div continuousOn_id continuousOn_const (by
        intro z _hz hzero
        exact ne_of_gt hc hzero)
    · intro z hz
      exact div_pos (hpos_spectrum z hz) hc
  calc
    cfc (p := IsSelfAdjoint)
        (fun z : ℝ => Real.log c + realNormalizedLogKernel (z / c)) A =
        algebraMap ℝ (CStarMatrix ι ι ℂ) (Real.log c) +
          cfc (p := IsSelfAdjoint) (fun z : ℝ => realNormalizedLogKernel (z / c)) A := by
          exact cfc_const_add (R := ℝ) (A := CStarMatrix ι ι ℂ) (p := IsSelfAdjoint)
            (r := Real.log c) (f := fun z : ℝ => realNormalizedLogKernel (z / c))
            (a := A) (hf := hcont_div) (ha := hA.isSelfAdjoint)
    _ = algebraMap ℝ (CStarMatrix ι ι ℂ) (Real.log c) +
        cfc (p := IsSelfAdjoint) realNormalizedLogKernel ((c⁻¹) • A) := by
          have hdiv_eq_mul :
              (fun z : ℝ => realNormalizedLogKernel (z / c)) =
                (fun z : ℝ => realNormalizedLogKernel (c⁻¹ * z)) := by
            ext z
            rw [div_eq_inv_mul]
          rw [hdiv_eq_mul]
          have hcont_image : ContinuousOn realNormalizedLogKernel
              ((fun x : ℝ => c⁻¹ * x) '' spectrum ℝ A) := by
            exact continuousOn_realNormalizedLogKernel_Ioi.mono fun y hy => by
              rcases hy with ⟨z, hz, rfl⟩
              exact mul_pos (inv_pos.mpr hc) (hpos_spectrum z hz)
          congr 1
          exact cfc_comp_const_mul (R := ℝ) (A := CStarMatrix ι ι ℂ) (p := IsSelfAdjoint)
            (r := c⁻¹) (f := realNormalizedLogKernel) (a := A)
            (hf := hcont_image) (ha := hA.isSelfAdjoint)

/-- Finite nonnegative combinations of scaled fractional kernels
`x ↦ x / (s + x)` are operator-monotone on the nonnegative cone.

This is a finite-sum precursor to the integral-representation lift used for
the normalized logarithmic kernel. -/
theorem cstarMatrix_cfc_finset_sum_nonneg_mul_pos_over_pos_add_monotone
    {ι κ : Type*} [Fintype ι] [DecidableEq ι] [DecidableEq κ]
    (t : Finset κ) (w σ : κ → ℝ)
    (hw : ∀ k ∈ t, 0 ≤ w k) (hσ : ∀ k ∈ t, 0 < σ k)
    {A B : CStarMatrix ι ι ℂ} (hA : 0 ≤ A) (hB : 0 ≤ B) (hAB : A ≤ B) :
    cfc (p := IsSelfAdjoint)
        (∑ k ∈ t, fun x : ℝ => w k * (x / (σ k + x))) A ≤
      cfc (p := IsSelfAdjoint)
        (∑ k ∈ t, fun x : ℝ => w k * (x / (σ k + x))) B := by
  have hcontKernel (C : CStarMatrix ι ι ℂ) (hC : 0 ≤ C)
      (k : κ) (hk : k ∈ t) :
      ContinuousOn (fun x : ℝ => w k * (x / (σ k + x))) (spectrum ℝ C) := by
    refine ContinuousOn.const_mul ?_ (w k)
    refine ContinuousOn.div (by fun_prop) (by fun_prop) ?_
    intro x hx hzero
    have hx_nonneg : 0 ≤ x := cstarMatrix_spectrum_nonneg_of_nonneg hC hx
    have hden_pos : 0 < σ k + x := by linarith [hσ k hk]
    exact ne_of_gt hden_pos hzero
  have hcontBase (C : CStarMatrix ι ι ℂ) (hC : 0 ≤ C)
      (k : κ) (hk : k ∈ t) :
      ContinuousOn (fun x : ℝ => x / (σ k + x)) (spectrum ℝ C) := by
    refine ContinuousOn.div (by fun_prop) (by fun_prop) ?_
    intro x hx hzero
    have hx_nonneg : 0 ≤ x := cstarMatrix_spectrum_nonneg_of_nonneg hC hx
    have hden_pos : 0 < σ k + x := by linarith [hσ k hk]
    exact ne_of_gt hden_pos hzero
  have hterm (k : κ) (hk : k ∈ t) :
      cfc (p := IsSelfAdjoint) (fun x : ℝ => w k * (x / (σ k + x))) A ≤
        cfc (p := IsSelfAdjoint) (fun x : ℝ => w k * (x / (σ k + x))) B := by
    have hbase :=
      cstarMatrix_cfc_pos_over_pos_add_monotone
        (ι := ι) (s := σ k) (hσ k hk) hA hB hAB
    have hAe :
        cfc (p := IsSelfAdjoint) (fun x : ℝ => w k * (x / (σ k + x))) A =
          w k • cfc (p := IsSelfAdjoint) (fun x : ℝ => x / (σ k + x)) A := by
      rw [cfc_const_mul (r := w k)
        (f := fun x : ℝ => x / (σ k + x)) (a := A)
        (hf := hcontBase A hA k hk)]
    have hBe :
        cfc (p := IsSelfAdjoint) (fun x : ℝ => w k * (x / (σ k + x))) B =
          w k • cfc (p := IsSelfAdjoint) (fun x : ℝ => x / (σ k + x)) B := by
      rw [cfc_const_mul (r := w k)
        (f := fun x : ℝ => x / (σ k + x)) (a := B)
        (hf := hcontBase B hB k hk)]
    rw [hAe, hBe]
    change ((w k : ℂ) •
        cfc (p := IsSelfAdjoint) (fun x : ℝ => x / (σ k + x)) A) ≤
      ((w k : ℂ) •
        cfc (p := IsSelfAdjoint) (fun x : ℝ => x / (σ k + x)) B)
    exact smul_le_smul_of_nonneg_left hbase
      (show 0 ≤ (w k : ℂ) by exact_mod_cast hw k hk)
  rw [cfc_sum (f := fun k : κ => fun x : ℝ => w k * (x / (σ k + x)))
      (a := A) (s := t) (hf := hcontKernel A hA)]
  rw [cfc_sum (f := fun k : κ => fun x : ℝ => w k * (x / (σ k + x)))
      (a := B) (s := t) (hf := hcontKernel B hB)]
  exact Finset.sum_le_sum fun k hk => hterm k hk

open MeasureTheory Set Function in
/-- Pointwise operator order for a family of CFC integrands passes through the
Bochner integral.

This is the order-theoretic half of the logarithmic-kernel integral route:
once a scalar integral representation is available and the continuity/bounded
integrability hypotheses of `cfc_integral` are discharged, a pointwise family
of CFC monotonicity inequalities integrates to the corresponding monotonicity
inequality for the integrated scalar kernel. -/
theorem cfc_integral_mono_of_forall_of_bound
    {X A : Type*} {p : A → Prop}
    [MeasurableSpace X] [TopologicalSpace X] [OpensMeasurableSpace X]
    {μ : Measure X}
    [NormedRing A] [StarRing A] [NormedAlgebra ℝ A]
    [ContinuousFunctionalCalculus ℝ A p]
    [CompleteSpace A]
    [PartialOrder A] [IsOrderedAddMonoid A] [IsOrderedModule ℝ A]
    [ClosedIciTopology A]
    (f : X → ℝ → ℝ) (boundA boundB : X → ℝ) {a b : A}
    [SecondCountableTopologyEither X C(spectrum ℝ a, ℝ)]
    [SecondCountableTopologyEither X C(spectrum ℝ b, ℝ)]
    (ha : p a) (hb : p b)
    (hacont : ContinuousOn (uncurry f) (univ ×ˢ spectrum ℝ a))
    (hbcont : ContinuousOn (uncurry f) (univ ×ˢ spectrum ℝ b))
    (hAbound : ∀ᵐ x ∂μ, ∀ z ∈ spectrum ℝ a, ‖f x z‖ ≤ boundA x)
    (hBbound : ∀ᵐ x ∂μ, ∀ z ∈ spectrum ℝ b, ‖f x z‖ ≤ boundB x)
    (hAint : HasFiniteIntegral boundA μ)
    (hBint : HasFiniteIntegral boundB μ)
    (hmono : ∀ x : X, cfc (p := p) (f x) a ≤ cfc (p := p) (f x) b) :
    cfc (p := p) (fun z : ℝ => ∫ x, f x z ∂μ) a ≤
      cfc (p := p) (fun z : ℝ => ∫ x, f x z ∂μ) b := by
  have hAi : Integrable (fun x : X => cfc (p := p) (f x) a) μ := by
    exact integrable_cfc (p := p) f boundA a hacont hAbound hAint ha
  have hBi : Integrable (fun x : X => cfc (p := p) (f x) b) μ := by
    exact integrable_cfc (p := p) f boundB b hbcont hBbound hBint hb
  have hAe := cfc_integral (p := p) f boundA a hacont hAbound hAint ha
  have hBe := cfc_integral (p := p) f boundB b hbcont hBbound hBint hb
  rw [hAe, hBe]
  exact MeasureTheory.integral_mono hAi hBi hmono

/-- Bendat-Sherman-route divided-difference monotonicity target for
`x ↦ x log x`: for every positive base point `c`, the first divided difference
is operator-monotone on the strictly positive cone. -/
def cstarMatrixXLogXDividedDifferenceMonotoneTarget
    {ι : Type*} [Fintype ι] [DecidableEq ι] : Prop :=
  ∀ c : ℝ, 0 < c →
    cstarMatrixStrictPositiveOperatorMonotoneTarget (ι := ι)
      (realXLogXDividedDifference c)

/-- The first divided difference of `x ↦ x log x` is operator-monotone on the
strictly positive cone.

The proof reduces the CFC of the divided difference to a constant plus the
normalized logarithmic kernel applied to `c⁻¹ A`, then reuses the normalized
kernel monotonicity theorem. -/
theorem cstarMatrixXLogXDividedDifferenceMonotoneTarget_of_normalizedLogKernel
    {ι : Type*} [Fintype ι] [DecidableEq ι] :
    cstarMatrixXLogXDividedDifferenceMonotoneTarget (ι := ι) := by
  intro c hc A B hA hB hAB
  rw [cstarMatrix_cfc_realXLogXDividedDifference_eq_log_add_scaled_normalizedKernel hA hc,
    cstarMatrix_cfc_realXLogXDividedDifference_eq_log_add_scaled_normalizedKernel hB hc]
  have hA' : IsStrictlyPositive ((c⁻¹) • A : CStarMatrix ι ι ℂ) :=
    cstarMatrix_isStrictlyPositive_pos_real_smul (ι := ι) (inv_pos.mpr hc) hA
  have hB' : IsStrictlyPositive ((c⁻¹) • B : CStarMatrix ι ι ℂ) :=
    cstarMatrix_isStrictlyPositive_pos_real_smul (ι := ι) (inv_pos.mpr hc) hB
  have hAB' : ((c⁻¹) • A : CStarMatrix ι ι ℂ) ≤ (c⁻¹) • B := by
    change (((c⁻¹ : ℝ) : ℂ) • A) ≤ (((c⁻¹ : ℝ) : ℂ) • B)
    exact smul_le_smul_of_nonneg_left hAB
      (show 0 ≤ (((c⁻¹ : ℝ) : ℂ)) by exact_mod_cast (le_of_lt (inv_pos.mpr hc)))
  simpa [add_comm, add_left_comm, add_assoc] using
    add_le_add_left
      (cstarMatrix_cfc_realNormalizedLogKernel_monotone hA' hB' hAB')
      (algebraMap ℝ (CStarMatrix ι ι ℂ) (Real.log c))

/-- Exact finite Bendat-Sherman divided-difference bridge target for the
current route: divided-difference operator-monotonicity for `x ↦ x log x`
should imply ordinary positive-cone operator convexity of `x ↦ x log x`.
This is the source-faithful active bottleneck; it is not assumed by any final
paper-level result. -/
def cstarMatrixBendatShermanDividedDifferenceBridgeTarget
    {ι : Type*} [Fintype ι] [DecidableEq ι] : Prop :=
  cstarMatrixXLogXDividedDifferenceMonotoneTarget (ι := ι) →
    cstarMatrixXLogXPositiveOperatorConvexTarget (ι := ι)

/-- If the source-faithful finite Bendat-Sherman divided-difference bridge and
the needed divided-difference monotonicity theorem are proved locally, then the
concrete `x log x` operator-convexity target closes.  This is dependency
wiring only. -/
theorem cstarMatrixXLogXPositiveOperatorConvexTarget_of_bendatShermanDividedDifferenceBridge
    {ι : Type*} [Fintype ι] [DecidableEq ι]
    (hbridge : cstarMatrixBendatShermanDividedDifferenceBridgeTarget (ι := ι))
    (hdd : cstarMatrixXLogXDividedDifferenceMonotoneTarget (ι := ι)) :
    cstarMatrixXLogXPositiveOperatorConvexTarget (ι := ι) :=
  hbridge hdd

/-- Exact finite Bendat-Sherman bridge target for the current route: derivative
operator-monotonicity of `x ↦ x log x` should imply ordinary positive-cone
operator convexity of `x ↦ x log x`.  This names the missing source theorem as
the active bottleneck; it is not assumed by any final paper-level result. -/
def cstarMatrixBendatShermanDerivativeBridgeTarget
    {ι : Type*} [Fintype ι] [DecidableEq ι] : Prop :=
  cstarMatrixXLogXDerivativeMonotoneTarget (ι := ι) →
    cstarMatrixXLogXPositiveOperatorConvexTarget (ι := ι)

/-- If the finite Bendat-Sherman bridge is proved locally, the already proved
operator-log monotonicity dependency closes the concrete `x log x`
operator-convexity target.  This is an adapter for the listed bottleneck
dependency, not a proof of the Bendat-Sherman bridge itself. -/
theorem cstarMatrixXLogXPositiveOperatorConvexTarget_of_bendatShermanDerivativeBridge
    {ι : Type*} [Fintype ι] [DecidableEq ι]
    (hbridge : cstarMatrixBendatShermanDerivativeBridgeTarget (ι := ι)) :
    cstarMatrixXLogXPositiveOperatorConvexTarget (ι := ι) :=
  hbridge cstarMatrixXLogXDerivativeMonotoneTarget_of_log_monotone

/-!
## Inverse-convexity substrate for the direct operator-convexity route

A second source-standard route to operator convexity of `x ↦ x log x` uses its
integral representation in terms of shifted inverse kernels.  The next lemmas
formalize the finite matrix arithmetic-harmonic mean step behind that route:
the inverse map is convex on the positive-definite cone.  This does not yet
prove operator convexity of `x log x`; it closes only the reusable Schur
complement dependency for that route.
-/

/-- The Schur-complement block associated with a positive-definite matrix and
its inverse is positive semidefinite. -/
theorem matrix_posDef_inverse_schur_block
    {ι : Type*} [Fintype ι] [DecidableEq ι]
    {A : Matrix ι ι ℂ} (hA : Matrix.PosDef A) :
    (Matrix.fromBlocks A (1 : Matrix ι ι ℂ) (1 : Matrix ι ι ℂ) A⁻¹).PosSemidef := by
  letI := hA.isUnit.invertible
  have hschur :
      (Matrix.fromBlocks A (1 : Matrix ι ι ℂ) (Matrix.conjTranspose (1 : Matrix ι ι ℂ))
        A⁻¹).PosSemidef := by
    rw [Matrix.PosDef.fromBlocks₁₁ (B := (1 : Matrix ι ι ℂ)) (D := A⁻¹) hA]
    simpa using (Matrix.PosSemidef.zero : Matrix.PosSemidef (0 : Matrix ι ι ℂ))
  simpa using hschur

/-- Positive-semidefinite block inequality for the convex combination of two
inverse Schur blocks. -/
theorem matrix_weighted_inverse_schur_block
    {ι : Type*} [Fintype ι] [DecidableEq ι]
    {A B : Matrix ι ι ℂ} (hA : Matrix.PosDef A) (hB : Matrix.PosDef B)
    {a b : ℝ} (ha : 0 ≤ a) (hb : 0 ≤ b) (hab : a + b = 1) :
    (Matrix.fromBlocks (((a : ℂ) • A) + ((b : ℂ) • B))
      (1 : Matrix ι ι ℂ) (1 : Matrix ι ι ℂ)
      (((a : ℂ) • A⁻¹) + ((b : ℂ) • B⁻¹))).PosSemidef := by
  have hblockA := matrix_posDef_inverse_schur_block (ι := ι) hA
  have hblockB := matrix_posDef_inverse_schur_block (ι := ι) hB
  have hsum :
      ((a : ℂ) • Matrix.fromBlocks A (1 : Matrix ι ι ℂ) (1 : Matrix ι ι ℂ) A⁻¹ +
        (b : ℂ) • Matrix.fromBlocks B (1 : Matrix ι ι ℂ) (1 : Matrix ι ι ℂ) B⁻¹).PosSemidef :=
    (hblockA.smul (show 0 ≤ (a : ℂ) by exact_mod_cast ha)).add
      (hblockB.smul (show 0 ≤ (b : ℂ) by exact_mod_cast hb))
  have hsum' :
      (Matrix.fromBlocks (((a : ℂ) • A) + ((b : ℂ) • B))
        (((a : ℂ) • (1 : Matrix ι ι ℂ)) + ((b : ℂ) • (1 : Matrix ι ι ℂ)))
        (((a : ℂ) • (1 : Matrix ι ι ℂ)) + ((b : ℂ) • (1 : Matrix ι ι ℂ)))
        (((a : ℂ) • A⁻¹) + ((b : ℂ) • B⁻¹))).PosSemidef := by
    simpa [Matrix.fromBlocks_smul, Matrix.fromBlocks_add] using hsum
  have hone :
      ((a : ℂ) • (1 : Matrix ι ι ℂ)) + ((b : ℂ) • (1 : Matrix ι ι ℂ)) = 1 := by
    rw [← add_smul]
    have habc : (a : ℂ) + (b : ℂ) = 1 := by exact_mod_cast hab
    simp [habc]
  simpa [hone] using hsum'

/-- A nontrivial convex combination of positive-definite matrices is
positive definite; endpoint weights reduce to the corresponding endpoint
matrix. -/
theorem matrix_posDef_weighted_sum
    {ι : Type*} [Fintype ι] [DecidableEq ι]
    {A B : Matrix ι ι ℂ} (hA : Matrix.PosDef A) (hB : Matrix.PosDef B)
    {a b : ℝ} (ha : 0 ≤ a) (hb : 0 ≤ b) (hab : a + b = 1) :
    Matrix.PosDef (((a : ℂ) • A) + ((b : ℂ) • B)) := by
  by_cases ha0 : a = 0
  · have hb1 : b = 1 := by nlinarith
    simpa [ha0, hb1] using hB
  · by_cases hb0 : b = 0
    · have ha1 : a = 1 := by nlinarith
      simpa [hb0, ha1] using hA
    · have hapos : 0 < a := lt_of_le_of_ne ha (Ne.symm ha0)
      have hbpos : 0 < b := lt_of_le_of_ne hb (Ne.symm hb0)
      exact (hA.smul (show 0 < (a : ℂ) by exact_mod_cast hapos)).add
        (hB.smul (show 0 < (b : ℂ) by exact_mod_cast hbpos))

/-- Finite-dimensional inverse convexity on the positive-definite cone.

This is the matrix arithmetic-harmonic mean inequality obtained from the Schur
complement block proof.  It is intended as the reusable inverse-kernel
foundation for a direct integral-representation proof of operator convexity of
`x ↦ x log x`. -/
theorem matrix_inv_convex_posDef
    {ι : Type*} [Fintype ι] [DecidableEq ι]
    {A B : Matrix ι ι ℂ} (hA : Matrix.PosDef A) (hB : Matrix.PosDef B)
    {a b : ℝ} (ha : 0 ≤ a) (hb : 0 ≤ b) (hab : a + b = 1) :
    (((a : ℂ) • A) + ((b : ℂ) • B))⁻¹ ≤
      ((a : ℂ) • A⁻¹) + ((b : ℂ) • B⁻¹) := by
  let C : Matrix ι ι ℂ := ((a : ℂ) • A) + ((b : ℂ) • B)
  let D : Matrix ι ι ℂ := ((a : ℂ) • A⁻¹) + ((b : ℂ) • B⁻¹)
  have hC : Matrix.PosDef C := matrix_posDef_weighted_sum hA hB ha hb hab
  letI := hC.isUnit.invertible
  have hblock : (Matrix.fromBlocks C (1 : Matrix ι ι ℂ) (1 : Matrix ι ι ℂ) D).PosSemidef := by
    simpa [C, D] using matrix_weighted_inverse_schur_block hA hB ha hb hab
  have hschur :
      (D - Matrix.conjTranspose (1 : Matrix ι ι ℂ) * C⁻¹ *
        (1 : Matrix ι ι ℂ)).PosSemidef := by
    exact (Matrix.PosDef.fromBlocks₁₁ (B := (1 : Matrix ι ι ℂ)) (D := D) hC).mp
      (by simpa using hblock)
  rw [Matrix.le_iff]
  simpa [C, D] using hschur

/-- C-star-matrix inverse-kernel convexity on the strictly positive finite cone.

This is the C⋆-order bridge form of `matrix_inv_convex_posDef`: the proof
converts the strictly positive inputs to plain positive-definite matrices,
uses the finite Schur-complement inverse-convexity theorem, then lifts the
plain Loewner inequality back to C⋆ spectral order.  It is stated through
real CFC because `CStarMatrix` has unit inverses but no global `Inv`
instance. -/
theorem cstarMatrix_cfc_inv_convex_isStrictlyPositive
    {ι : Type*} [Fintype ι] [DecidableEq ι]
    {A B : CStarMatrix ι ι ℂ} (hA : IsStrictlyPositive A)
    (hB : IsStrictlyPositive B)
    {a b : ℝ} (ha : 0 ≤ a) (hb : 0 ≤ b) (hab : a + b = 1) :
    cfc (p := IsSelfAdjoint) (fun x : ℝ => x⁻¹) (a • A + b • B) ≤
      a • cfc (p := IsSelfAdjoint) (fun x : ℝ => x⁻¹) A +
        b • cfc (p := IsSelfAdjoint) (fun x : ℝ => x⁻¹) B := by
  have hC : IsStrictlyPositive (a • A + b • B) :=
    strictPositiveCStarMatrixCone_convex
      (by simpa using hA) (by simpa using hB) ha hb hab
  let uA : (CStarMatrix ι ι ℂ)ˣ := hA.isUnit.unit
  let uB : (CStarMatrix ι ι ℂ)ˣ := hB.isUnit.unit
  let uC : (CStarMatrix ι ι ℂ)ˣ := hC.isUnit.unit
  have huA : (uA : CStarMatrix ι ι ℂ) = A := hA.isUnit.unit_spec
  have huB : (uB : CStarMatrix ι ι ℂ) = B := hB.isUnit.unit_spec
  have huC : (uC : CStarMatrix ι ι ℂ) = a • A + b • B := hC.isUnit.unit_spec
  have hcfA :
      cfc (p := IsSelfAdjoint) (fun x : ℝ => x⁻¹) A =
        (↑uA⁻¹ : CStarMatrix ι ι ℂ) := by
    rw [← huA]
    exact cfc_inv_id (a := uA) (R := ℝ)
      (ha := by simpa [huA] using IsSelfAdjoint.of_nonneg hA.nonneg)
  have hcfB :
      cfc (p := IsSelfAdjoint) (fun x : ℝ => x⁻¹) B =
        (↑uB⁻¹ : CStarMatrix ι ι ℂ) := by
    rw [← huB]
    exact cfc_inv_id (a := uB) (R := ℝ)
      (ha := by simpa [huB] using IsSelfAdjoint.of_nonneg hB.nonneg)
  have hcfC :
      cfc (p := IsSelfAdjoint) (fun x : ℝ => x⁻¹) (a • A + b • B) =
        (↑uC⁻¹ : CStarMatrix ι ι ℂ) := by
    rw [← huC]
    exact cfc_inv_id (a := uC) (R := ℝ)
      (ha := by simpa [huC] using IsSelfAdjoint.of_nonneg hC.nonneg)
  rw [hcfA, hcfB, hcfC]
  apply cstarMatrix_le_of_matrix_le
  have hAm :
      Matrix.PosDef (CStarMatrix.ofMatrix.symm A : Matrix ι ι ℂ) :=
    cstarMatrix_isStrictlyPositive_to_matrix_posDef hA
  have hBm :
      Matrix.PosDef (CStarMatrix.ofMatrix.symm B : Matrix ι ι ℂ) :=
    cstarMatrix_isStrictlyPositive_to_matrix_posDef hB
  have hmat := matrix_inv_convex_posDef hAm hBm ha hb hab
  have hunitInvMatrix (u : (CStarMatrix ι ι ℂ)ˣ) :
      CStarMatrix.ofMatrix.symm (↑u⁻¹ : CStarMatrix ι ι ℂ) =
        (CStarMatrix.ofMatrix.symm (↑u : CStarMatrix ι ι ℂ) : Matrix ι ι ℂ)⁻¹ := by
    symm
    refine Matrix.inv_eq_right_inv ?_
    change CStarMatrix.ofMatrix.symm
        ((↑u : CStarMatrix ι ι ℂ) * (↑u⁻¹ : CStarMatrix ι ι ℂ)) =
      (1 : Matrix ι ι ℂ)
    exact congrArg
      (fun X : CStarMatrix ι ι ℂ =>
        (CStarMatrix.ofMatrix.symm X : Matrix ι ι ℂ))
      u.mul_inv
  calc
    CStarMatrix.ofMatrix.symm (↑uC⁻¹ : CStarMatrix ι ι ℂ)
        = (CStarMatrix.ofMatrix.symm (↑uC : CStarMatrix ι ι ℂ) :
            Matrix ι ι ℂ)⁻¹ := hunitInvMatrix uC
    _ = ((a : ℂ) • CStarMatrix.ofMatrix.symm A +
          (b : ℂ) • CStarMatrix.ofMatrix.symm B)⁻¹ := by
        congr 1
    _ ≤ (a : ℂ) • (CStarMatrix.ofMatrix.symm A)⁻¹ +
          (b : ℂ) • (CStarMatrix.ofMatrix.symm B)⁻¹ := hmat
    _ = CStarMatrix.ofMatrix.symm
          (a • (↑uA⁻¹ : CStarMatrix ι ι ℂ) +
            b • (↑uB⁻¹ : CStarMatrix ι ι ℂ)) := by
        rw [← huA, ← huB]
        rw [← hunitInvMatrix uA, ← hunitInvMatrix uB]
        ext i j
        simp

/-- Shifted inverse kernels reduce to the ordinary inverse kernel after adding
a positive scalar identity.

This is the CFC bridge for the direct integral route: on a nonnegative finite
C⋆-matrix, \(x \mapsto (s+x)^{-1}\) is the ordinary inverse functional
calculus applied to \(sI+A\). -/
theorem cstarMatrix_cfc_shifted_inv_eq_cfc_inv_add_smul_one
    {ι : Type*} [Fintype ι] [DecidableEq ι]
    {A : CStarMatrix ι ι ℂ} (hA : 0 ≤ A) {s : ℝ} (hs : 0 < s) :
    cfc (p := IsSelfAdjoint) (fun x : ℝ => (s + x)⁻¹) A =
      cfc (p := IsSelfAdjoint) (fun x : ℝ => x⁻¹)
        (s • (1 : CStarMatrix ι ι ℂ) + A) := by
  have hshift :
      ContinuousOn (fun x : ℝ => (s + x)⁻¹) (spectrum ℝ A) := by
    refine ContinuousOn.inv₀ (by fun_prop) ?_
    intro x hx hzero
    have hx_nonneg : 0 ≤ x := cstarMatrix_spectrum_nonneg_of_nonneg hA hx
    linarith
  have hinv_shift :
      ContinuousOn (fun x : ℝ => x⁻¹)
        ((fun x : ℝ => s + x) '' spectrum ℝ A) := by
    refine ContinuousOn.inv₀ (by fun_prop) ?_
    rintro y ⟨x, hx, rfl⟩ hzero
    have hx_nonneg : 0 ≤ x := cstarMatrix_spectrum_nonneg_of_nonneg hA hx
    linarith
  have hcomp :
      cfc (p := IsSelfAdjoint) (fun x : ℝ => (s + x)⁻¹) A =
        cfc (p := IsSelfAdjoint) (fun x : ℝ => x⁻¹)
          (cfc (p := IsSelfAdjoint) (fun x : ℝ => s + x) A) := by
    rw [cfc_comp' (g := fun x : ℝ => x⁻¹) (f := fun x : ℝ => s + x)
      (a := A) (hg := hinv_shift)]
  have hadd :
      cfc (p := IsSelfAdjoint) (fun x : ℝ => s + x) A =
        s • (1 : CStarMatrix ι ι ℂ) + A := by
    rw [cfc_const_add (R := ℝ) (A := CStarMatrix ι ι ℂ)
      (p := IsSelfAdjoint) (r := s) (f := fun x : ℝ => x) (a := A)
      (hf := by fun_prop) (ha := IsSelfAdjoint.of_nonneg hA)]
    rw [show cfc (fun x : ℝ => x) A = A from
      cfc_id' ℝ A (IsSelfAdjoint.of_nonneg hA)]
    simp [Algebra.algebraMap_eq_smul_one]
  rw [hcomp, hadd]

/-- Shifted inverse kernels preserve rectangular intertwining.

If a nonnegative square matrix `E` intertwines a rectangular block column `V`
with a nonnegative square matrix `X`, i.e. `E * V = V * X`, then every shifted
inverse kernel satisfies
\[
  (sI+E)^{-1} V = V (sI+X)^{-1}.
\]
In CFC notation this is the first concrete nonlinear corner dependency for the
Hansen--Pedersen route. -/
theorem cstarMatrix_cfc_shifted_inv_mul_rect_eq_mul_cfc_shifted_inv_of_mul_eq
    {α β : Type*} [Fintype α] [DecidableEq α] [Fintype β] [DecidableEq β]
    {E : CStarMatrix α α ℂ} {X : CStarMatrix β β ℂ}
    (hE : 0 ≤ E) (hX : 0 ≤ X)
    {s : ℝ} (hs : 0 < s) (V : CStarMatrix α β ℂ)
    (hEV : E * V = V * X) :
    cfc (p := IsSelfAdjoint) (fun x : ℝ => (s + x)⁻¹) E * V =
      V * cfc (p := IsSelfAdjoint) (fun x : ℝ => (s + x)⁻¹) X := by
  let SE : CStarMatrix α α ℂ := s • (1 : CStarMatrix α α ℂ) + E
  let SX : CStarMatrix β β ℂ := s • (1 : CStarMatrix β β ℂ) + X
  have hSEstrict : IsStrictlyPositive SE :=
    (cstarMatrix_pos_real_smul_one_isStrictlyPositive (ι := α) hs).add_nonneg hE
  have hSXstrict : IsStrictlyPositive SX :=
    (cstarMatrix_pos_real_smul_one_isStrictlyPositive (ι := β) hs).add_nonneg hX
  have hSEV : SE * V = V * SX := by
    have hsleft :
        (s • (1 : CStarMatrix α α ℂ)) * V = (s : ℂ) • V := by
      ext i j
      simp [CStarMatrix.mul_apply, CStarMatrix.one_apply, CStarMatrix.smul_apply]
    have hsright :
        V * (s • (1 : CStarMatrix β β ℂ)) = (s : ℂ) • V := by
      ext i j
      simp [CStarMatrix.mul_apply, CStarMatrix.one_apply, CStarMatrix.smul_apply]
      ring
    calc
      SE * V = (s • (1 : CStarMatrix α α ℂ)) * V + E * V := by
          dsimp [SE]
          rw [cstarMatrix_add_mul_rect]
      _ = (s : ℂ) • V + V * X := by
          rw [hsleft, hEV]
      _ = V * (s • (1 : CStarMatrix β β ℂ)) + V * X := by
          rw [hsright]
      _ = V * SX := by
          dsimp [SX]
          rw [← cstarMatrix_mul_add_rect]
  let uE : (CStarMatrix α α ℂ)ˣ := hSEstrict.isUnit.unit
  let uX : (CStarMatrix β β ℂ)ˣ := hSXstrict.isUnit.unit
  have huE : (uE : CStarMatrix α α ℂ) = SE := hSEstrict.isUnit.unit_spec
  have huX : (uX : CStarMatrix β β ℂ) = SX := hSXstrict.isUnit.unit_spec
  have hcfE :
      cfc (p := IsSelfAdjoint) (fun x : ℝ => (s + x)⁻¹) E =
        (↑uE⁻¹ : CStarMatrix α α ℂ) := by
    rw [cstarMatrix_cfc_shifted_inv_eq_cfc_inv_add_smul_one hE hs]
    change cfc (p := IsSelfAdjoint) (fun x : ℝ => x⁻¹) SE =
      (↑uE⁻¹ : CStarMatrix α α ℂ)
    rw [← huE]
    exact cfc_inv_id (a := uE) (R := ℝ)
      (ha := by simpa [huE] using IsSelfAdjoint.of_nonneg hSEstrict.nonneg)
  have hcfX :
      cfc (p := IsSelfAdjoint) (fun x : ℝ => (s + x)⁻¹) X =
        (↑uX⁻¹ : CStarMatrix β β ℂ) := by
    rw [cstarMatrix_cfc_shifted_inv_eq_cfc_inv_add_smul_one hX hs]
    change cfc (p := IsSelfAdjoint) (fun x : ℝ => x⁻¹) SX =
      (↑uX⁻¹ : CStarMatrix β β ℂ)
    rw [← huX]
    exact cfc_inv_id (a := uX) (R := ℝ)
      (ha := by simpa [huX] using IsSelfAdjoint.of_nonneg hSXstrict.nonneg)
  rw [hcfE, hcfX]
  have hunit : (uE : CStarMatrix α α ℂ) * V =
      V * (uX : CStarMatrix β β ℂ) := by
    simpa [huE, huX] using hSEV
  exact cstarMatrix_units_inv_mul_rect_eq_mul_units_inv_of_mul_eq uE uX V hunit

/-- Shifted inverse corner identity for the reflection-average block used in
the Hansen--Pedersen proof.

This is a source-aligned nonlinear dependency: for the particular kernels
\(x \mapsto (s+x)^{-1}\), the compressed CFC of the reflected average is the
CFC of the compressed corner.  It does not yet assemble the full `x log x`
corner identity; it is the kernel-level step needed for that assembly. -/
theorem cstarMatrixColumnPair_reflectionAverage_shifted_inv_corner_of_sum
    {ι : Type u} [Fintype ι] [DecidableEq ι]
    {A B : CStarMatrix ι ι ℂ}
    (hAB : star A * A + star B * B = 1)
    (D : CStarMatrix (ι ⊕ ι) (ι ⊕ ι) ℂ)
    (hD : IsStrictlyPositive D)
    {s : ℝ} (hs : 0 < s) :
    let V : CStarMatrix (ι ⊕ ι) ι ℂ := cstarMatrixColumnPair A B
    let E : CStarMatrix (ι ⊕ ι) (ι ⊕ ι) ℂ :=
      (1 / 2 : ℂ) •
        (D + cstarMatrixColumnPairRangeReflection A B * D *
          cstarMatrixColumnPairRangeReflection A B)
    CStarMatrix.conjTranspose V *
        cfc (p := IsSelfAdjoint) (fun x : ℝ => (s + x)⁻¹) E * V =
      cfc (p := IsSelfAdjoint) (fun x : ℝ => (s + x)⁻¹)
        (CStarMatrix.conjTranspose V * D * V) := by
  intro V E
  let R : CStarMatrix (ι ⊕ ι) (ι ⊕ ι) ℂ :=
    cstarMatrixColumnPairRangeReflection A B
  let X : CStarMatrix ι ι ℂ :=
    CStarMatrix.conjTranspose V * D * V
  have hRself : IsSelfAdjoint R := by
    dsimp [R]
    exact cstarMatrixColumnPairRangeReflection_isSelfAdjoint A B
  have hRstar : star R = R := by
    simpa [isSelfAdjoint_iff] using hRself
  have hRDRstrict : IsStrictlyPositive (R * D * R) := by
    have hstrict : IsStrictlyPositive (R * D * star R) := by
      dsimp [R]
      exact cstarMatrixColumnPairRangeReflection_conj_isStrictlyPositive_of_sum
        hAB hD
    simpa [hRstar] using hstrict
  have hE_nonneg : 0 ≤ E := by
    have hsum : 0 ≤ D + R * D * R :=
      add_nonneg hD.nonneg hRDRstrict.nonneg
    have hhalf : 0 ≤ ((1 / 2 : ℝ) : ℂ) := by
      exact_mod_cast (show 0 ≤ (1 / 2 : ℝ) by norm_num)
    simpa [E, R] using smul_nonneg hhalf hsum
  have hX_nonneg : 0 ≤ X := by
    dsimp [X]
    exact cstarMatrix_compression_nonneg hD.nonneg V
  have hEV : E * V = V * X := by
    dsimp [E, X, V, R]
    exact cstarMatrixColumnPair_reflectionAverage_mul_columnPair_of_sum hAB D
  have hinter :=
    cstarMatrix_cfc_shifted_inv_mul_rect_eq_mul_cfc_shifted_inv_of_mul_eq
      hE_nonneg hX_nonneg hs V hEV
  have hVV :
      CStarMatrix.conjTranspose V * V =
        (1 : CStarMatrix ι ι ℂ) := by
    dsimp [V]
    exact cstarMatrixColumnPair_conjTranspose_mul_self_eq_one_of_sum hAB
  calc
    CStarMatrix.conjTranspose V *
        cfc (p := IsSelfAdjoint) (fun x : ℝ => (s + x)⁻¹) E * V =
        CStarMatrix.conjTranspose V *
          (cfc (p := IsSelfAdjoint) (fun x : ℝ => (s + x)⁻¹) E * V) := by
          rw [cstarMatrix_mul_assoc_rect]
    _ = CStarMatrix.conjTranspose V *
          (V * cfc (p := IsSelfAdjoint) (fun x : ℝ => (s + x)⁻¹) X) := by
          rw [hinter]
    _ = (CStarMatrix.conjTranspose V * V) *
          cfc (p := IsSelfAdjoint) (fun x : ℝ => (s + x)⁻¹) X := by
          rw [← cstarMatrix_mul_assoc_rect]
    _ = (1 : CStarMatrix ι ι ℂ) *
          cfc (p := IsSelfAdjoint) (fun x : ℝ => (s + x)⁻¹) X := by
          rw [hVV]
    _ = cfc (p := IsSelfAdjoint) (fun x : ℝ => (s + x)⁻¹) X :=
          cstarMatrix_one_mul_rect _

open MeasureTheory Set Function in
/-- Kernel corner identity for the actual `x log x` integral kernel on the
open unit interval.

This upgrades the shifted-inverse corner identity to the integrand
`x * (x - 1) / (u + (1 - u) * x)` that appears in the CFC integral
representation of `x log x`.  Endpoints are intentionally excluded; later
integral assembly can use the existing `Ioo =ᵐ Icc` replacement lemmas. -/
theorem cstarMatrixColumnPair_reflectionAverage_xlog_kernel_corner_of_sum
    {ι : Type u} [Fintype ι] [DecidableEq ι]
    {A B : CStarMatrix ι ι ℂ}
    (hAB : star A * A + star B * B = 1)
    (D : CStarMatrix (ι ⊕ ι) (ι ⊕ ι) ℂ)
    (hD : IsStrictlyPositive D)
    {u : ℝ} (hu0 : 0 < u) (hu1 : u < 1) :
    let V : CStarMatrix (ι ⊕ ι) ι ℂ := cstarMatrixColumnPair A B
    let E : CStarMatrix (ι ⊕ ι) (ι ⊕ ι) ℂ :=
      (1 / 2 : ℂ) •
        (D + cstarMatrixColumnPairRangeReflection A B * D *
          cstarMatrixColumnPairRangeReflection A B)
    CStarMatrix.conjTranspose V *
        cfc (p := IsSelfAdjoint)
          (fun x : ℝ => x * (x - 1) / (u + (1 - u) * x)) E * V =
      cfc (p := IsSelfAdjoint)
        (fun x : ℝ => x * (x - 1) / (u + (1 - u) * x))
        (CStarMatrix.conjTranspose V * D * V) := by
  intro V E
  let R : CStarMatrix (ι ⊕ ι) (ι ⊕ ι) ℂ :=
    cstarMatrixColumnPairRangeReflection A B
  let X : CStarMatrix ι ι ℂ := CStarMatrix.conjTranspose V * D * V
  have hRself : IsSelfAdjoint R := by
    dsimp [R]
    exact cstarMatrixColumnPairRangeReflection_isSelfAdjoint A B
  have hRstar : star R = R := by
    simpa [isSelfAdjoint_iff] using hRself
  have hRDRstrict : IsStrictlyPositive (R * D * R) := by
    have hstrict : IsStrictlyPositive (R * D * star R) := by
      dsimp [R]
      exact cstarMatrixColumnPairRangeReflection_conj_isStrictlyPositive_of_sum
        hAB hD
    simpa [hRstar] using hstrict
  have hEstrict : IsStrictlyPositive E := by
    have hsum : IsStrictlyPositive (D + R * D * R) :=
      hD.add_nonneg hRDRstrict.nonneg
    dsimp [E, R]
    exact IsStrictlyPositive.smul
      (show 0 < ((1 / 2 : ℂ)) by norm_num) hsum
  have hXstrict : IsStrictlyPositive X := by
    dsimp [X, V]
    exact cstarMatrixColumnPair_compression_isStrictlyPositive_of_sum hAB hD
  have hcompE :
      CStarMatrix.conjTranspose V * E * V = X := by
    dsimp [E, X, V, R]
    exact cstarMatrixColumnPair_reflectionAverage_compression_of_sum hAB D
  have hVV :
      CStarMatrix.conjTranspose V * V =
        (1 : CStarMatrix ι ι ℂ) := by
    dsimp [V]
    exact cstarMatrixColumnPair_conjTranspose_mul_self_eq_one_of_sum hAB
  have hcompOne :
      CStarMatrix.conjTranspose V *
          (1 : CStarMatrix (ι ⊕ ι) (ι ⊕ ι) ℂ) * V =
        (1 : CStarMatrix ι ι ℂ) :=
    cstarMatrix_compression_one_of_conjTranspose_mul_self_eq_one V hVV
  have hαpos : 0 < 1 - u := by linarith
  have hshift_pos : 0 < u / (1 - u) := div_pos hu0 hαpos
  have hshift :
      CStarMatrix.conjTranspose V *
          cfc (p := IsSelfAdjoint)
            (fun x : ℝ => (x + u / (1 - u))⁻¹) E * V =
        cfc (p := IsSelfAdjoint)
          (fun x : ℝ => (x + u / (1 - u))⁻¹) X := by
    have hcorner :=
      cstarMatrixColumnPair_reflectionAverage_shifted_inv_corner_of_sum
        (A := A) (B := B) hAB D hD hshift_pos
    simpa [X, V, E, add_comm] using hcorner
  have hEdecomp :=
    cstarMatrix_cfc_unit_interval_xlog_kernel_integrand_eq_affine_add_shifted_inv
      hEstrict (le_of_lt hu0) hu1
  have hXdecomp :=
    cstarMatrix_cfc_unit_interval_xlog_kernel_integrand_eq_affine_add_shifted_inv
      hXstrict (le_of_lt hu0) hu1
  rw [hEdecomp, hXdecomp]
  rw [cstarMatrix_compression_add, cstarMatrix_compression_sub]
  rw [cstarMatrix_compression_real_smul, cstarMatrix_compression_real_smul,
    cstarMatrix_compression_real_smul]
  rw [hcompE, hcompOne, hshift]

open MeasureTheory Set Function in
/-- Full `x log x` corner identity for the reflection-average block used in
the Hansen-Pedersen proof.

This assembles the open-interval kernel corner identities through the local CFC
integral representation of `x log x`. -/
theorem cstarMatrixColumnPair_reflectionAverage_xlog_corner_of_sum
    {ι : Type u} [Fintype ι] [DecidableEq ι]
    {A B : CStarMatrix ι ι ℂ}
    (hAB : star A * A + star B * B = 1)
    (D : CStarMatrix (ι ⊕ ι) (ι ⊕ ι) ℂ)
    (hD : IsStrictlyPositive D) :
    let V : CStarMatrix (ι ⊕ ι) ι ℂ := cstarMatrixColumnPair A B
    let E : CStarMatrix (ι ⊕ ι) (ι ⊕ ι) ℂ :=
      (1 / 2 : ℂ) •
        (D + cstarMatrixColumnPairRangeReflection A B * D *
          cstarMatrixColumnPairRangeReflection A B)
    CStarMatrix.conjTranspose V *
        cfc (p := IsSelfAdjoint) (fun x : ℝ => x * Real.log x) E * V =
      cfc (p := IsSelfAdjoint) (fun x : ℝ => x * Real.log x)
        (CStarMatrix.conjTranspose V * D * V) := by
  intro V E
  let R : CStarMatrix (ι ⊕ ι) (ι ⊕ ι) ℂ :=
    cstarMatrixColumnPairRangeReflection A B
  let X : CStarMatrix ι ι ℂ := CStarMatrix.conjTranspose V * D * V
  let fE : ℝ → CStarMatrix (ι ⊕ ι) (ι ⊕ ι) ℂ := fun u =>
    cfc (p := IsSelfAdjoint)
      (fun z : ℝ => z * (z - 1) / (u + (1 - u) * z)) E
  let fX : ℝ → CStarMatrix ι ι ℂ := fun u =>
    cfc (p := IsSelfAdjoint)
      (fun z : ℝ => z * (z - 1) / (u + (1 - u) * z)) X
  have hRself : IsSelfAdjoint R := by
    dsimp [R]
    exact cstarMatrixColumnPairRangeReflection_isSelfAdjoint A B
  have hRstar : star R = R := by
    simpa [isSelfAdjoint_iff] using hRself
  have hRDRstrict : IsStrictlyPositive (R * D * R) := by
    have hstrict : IsStrictlyPositive (R * D * star R) := by
      dsimp [R]
      exact cstarMatrixColumnPairRangeReflection_conj_isStrictlyPositive_of_sum
        hAB hD
    simpa [hRstar] using hstrict
  have hEstrict : IsStrictlyPositive E := by
    have hsum : IsStrictlyPositive (D + R * D * R) :=
      hD.add_nonneg hRDRstrict.nonneg
    dsimp [E, R]
    exact IsStrictlyPositive.smul
      (show 0 < ((1 / 2 : ℂ)) by norm_num) hsum
  have hXstrict : IsStrictlyPositive X := by
    dsimp [X, V]
    exact cstarMatrixColumnPair_compression_isStrictlyPositive_of_sum hAB hD
  rcases (spectrum.isBounded (𝕜 := ℝ) E).bddAbove with ⟨ME, hME⟩
  rcases (spectrum.isBounded (𝕜 := ℝ) X).bddAbove with ⟨MX, hMX⟩
  have hE_Icc : IntegrableOn fE (Set.Icc (0 : ℝ) 1) := by
    exact integrableOn_cfc
      (hs := (measurableSet_Icc : MeasurableSet (Set.Icc (0 : ℝ) 1)))
      (f := fun u z : ℝ => z * (z - 1) / (u + (1 - u) * z))
      (bound := fun _ : ℝ => (max 1 ME) ^ 2)
      (a := E)
      (hf := continuousOn_uncurry_unit_interval_xlog_kernel_spectrum hEstrict)
      (bound_ge := ae_unit_interval_xlog_kernel_spectrum_norm_le_max_sq hEstrict hME)
      (bound_int := hasFiniteIntegral_const_max_one_spectrum_bound_sq ME)
      (ha := hEstrict.isSelfAdjoint)
  have hrepE :=
    cstarMatrix_cfc_xlog_eq_unit_interval_xlog_kernel_integral hEstrict hME
  have hrepX :=
    cstarMatrix_cfc_xlog_eq_unit_interval_xlog_kernel_integral hXstrict hMX
  have hcompress :
      CStarMatrix.conjTranspose V * (∫ u in Set.Icc (0 : ℝ) 1, fE u) * V =
        ∫ u in Set.Icc (0 : ℝ) 1,
          CStarMatrix.conjTranspose V * fE u * V := by
    exact cstarMatrix_compression_setIntegral V hE_Icc
  have hE_Icc_Ioo :
      (∫ u in Set.Icc (0 : ℝ) 1,
          CStarMatrix.conjTranspose V * fE u * V) =
        ∫ u in Set.Ioo (0 : ℝ) 1,
          CStarMatrix.conjTranspose V * fE u * V := by
    exact (setIntegral_congr_set
      (Ioo_ae_eq_Icc (a := (0 : ℝ)) (b := 1))).symm
  have hX_Icc_Ioo :
      (∫ u in Set.Icc (0 : ℝ) 1, fX u) =
        ∫ u in Set.Ioo (0 : ℝ) 1, fX u := by
    exact (setIntegral_congr_set
      (Ioo_ae_eq_Icc (a := (0 : ℝ)) (b := 1))).symm
  have hpoint :
      ∀ u ∈ Set.Ioo (0 : ℝ) 1,
        CStarMatrix.conjTranspose V * fE u * V = fX u := by
    intro u hu
    dsimp [fE, fX, X, V, E]
    exact cstarMatrixColumnPair_reflectionAverage_xlog_kernel_corner_of_sum
      (A := A) (B := B) hAB D hD hu.1 hu.2
  have hIoo :
      (∫ u in Set.Ioo (0 : ℝ) 1,
          CStarMatrix.conjTranspose V * fE u * V) =
        ∫ u in Set.Ioo (0 : ℝ) 1, fX u := by
    exact setIntegral_congr_fun measurableSet_Ioo hpoint
  calc
    CStarMatrix.conjTranspose V *
        cfc (p := IsSelfAdjoint) (fun x : ℝ => x * Real.log x) E * V =
        CStarMatrix.conjTranspose V * (∫ u in Set.Icc (0 : ℝ) 1, fE u) * V := by
          rw [hrepE]
    _ = ∫ u in Set.Icc (0 : ℝ) 1,
          CStarMatrix.conjTranspose V * fE u * V := hcompress
    _ = ∫ u in Set.Ioo (0 : ℝ) 1,
          CStarMatrix.conjTranspose V * fE u * V := hE_Icc_Ioo
    _ = ∫ u in Set.Ioo (0 : ℝ) 1, fX u := hIoo
    _ = ∫ u in Set.Icc (0 : ℝ) 1, fX u := hX_Icc_Ioo.symm
    _ = cfc (p := IsSelfAdjoint) (fun x : ℝ => x * Real.log x) X := by
          rw [hrepX]
    _ = cfc (p := IsSelfAdjoint) (fun x : ℝ => x * Real.log x)
        (CStarMatrix.conjTranspose V * D * V) := rfl

/-- Shifted inverse kernels are convex on the nonnegative finite C⋆-matrix
cone.

This is the shifted-kernel form needed by the direct integral route toward
operator convexity of \(x\log x\). -/
theorem cstarMatrix_cfc_shifted_inv_convex_nonneg
    {ι : Type*} [Fintype ι] [DecidableEq ι]
    {A B : CStarMatrix ι ι ℂ} (hA : 0 ≤ A) (hB : 0 ≤ B)
    {s : ℝ} (hs : 0 < s)
    {a b : ℝ} (ha : 0 ≤ a) (hb : 0 ≤ b) (hab : a + b = 1) :
    cfc (p := IsSelfAdjoint) (fun x : ℝ => (s + x)⁻¹) (a • A + b • B) ≤
      a • cfc (p := IsSelfAdjoint) (fun x : ℝ => (s + x)⁻¹) A +
        b • cfc (p := IsSelfAdjoint) (fun x : ℝ => (s + x)⁻¹) B := by
  have hshiftA :
      IsStrictlyPositive (s • (1 : CStarMatrix ι ι ℂ) + A) :=
    (cstarMatrix_pos_real_smul_one_isStrictlyPositive (ι := ι) hs).add_nonneg hA
  have hshiftB :
      IsStrictlyPositive (s • (1 : CStarMatrix ι ι ℂ) + B) :=
    (cstarMatrix_pos_real_smul_one_isStrictlyPositive (ι := ι) hs).add_nonneg hB
  have hcombo_nonneg : 0 ≤ a • A + b • B := by
    exact add_nonneg (cstarMatrix_nonneg_nonneg_real_smul (ι := ι) ha hA)
      (cstarMatrix_nonneg_nonneg_real_smul (ι := ι) hb hB)
  have harg :
      a • (s • (1 : CStarMatrix ι ι ℂ) + A) +
        b • (s • (1 : CStarMatrix ι ι ℂ) + B) =
      s • (1 : CStarMatrix ι ι ℂ) + (a • A + b • B) := by
    ext i j
    have hsabc : (a : ℂ) * (s : ℂ) + (s : ℂ) * (b : ℂ) = (s : ℂ) := by
      have hsab : a * s + s * b = s := by nlinarith [hab]
      exact_mod_cast hsab
    by_cases hij : i = j
    · subst j
      simp [CStarMatrix.smul_apply]
      calc
        (a : ℂ) * ((s : ℂ) + A i i) +
            (b : ℂ) * ((s : ℂ) + B i i) =
            ((a : ℂ) * (s : ℂ) + (s : ℂ) * (b : ℂ)) +
              ((a : ℂ) * A i i + (b : ℂ) * B i i) := by ring
        _ = (s : ℂ) + ((a : ℂ) * A i i + (b : ℂ) * B i i) := by
          rw [hsabc]
    · simp [CStarMatrix.smul_apply, hij]
  rw [cstarMatrix_cfc_shifted_inv_eq_cfc_inv_add_smul_one hcombo_nonneg hs,
    cstarMatrix_cfc_shifted_inv_eq_cfc_inv_add_smul_one hA hs,
    cstarMatrix_cfc_shifted_inv_eq_cfc_inv_add_smul_one hB hs]
  rw [← harg]
  exact cstarMatrix_cfc_inv_convex_isStrictlyPositive hshiftA hshiftB ha hb hab

/-- Interior unit-interval convexity of the `x log x - x + 1` integrand.

For `0 < u < 1`, the CFC integrand
`x ↦ (x - 1)^2 / (u + (1 - u) x)` is operator-convex on the strictly
positive finite C-star matrix cone.  The proof uses the CFC decomposition into
an affine term plus a shifted inverse kernel, then applies the shifted-inverse
convexity theorem above.

This closes the fixed-interior-parameter convexity dependency for the direct
integral route.  The remaining direct-route step is to assemble these
pointwise inequalities through the operator-valued integral and add the affine
`x - 1` term. -/
theorem cstarMatrix_cfc_unit_interval_xlog_integrand_convex_of_pos_lt_one
    {ι : Type*} [Fintype ι] [DecidableEq ι]
    {A B : CStarMatrix ι ι ℂ} (hA : IsStrictlyPositive A)
    (hB : IsStrictlyPositive B)
    {u : ℝ} (hu0 : 0 < u) (hu1 : u < 1)
    {a b : ℝ} (ha : 0 ≤ a) (hb : 0 ≤ b) (hab : a + b = 1) :
    cfc (p := IsSelfAdjoint)
        (fun x : ℝ => (x - 1) ^ 2 / (u + (1 - u) * x))
        (a • A + b • B) ≤
      a • cfc (p := IsSelfAdjoint)
          (fun x : ℝ => (x - 1) ^ 2 / (u + (1 - u) * x)) A +
        b • cfc (p := IsSelfAdjoint)
          (fun x : ℝ => (x - 1) ^ 2 / (u + (1 - u) * x)) B := by
  let s : ℝ := u / (1 - u)
  let γ : ℝ := 1 / (1 - u) ^ 3
  let α : ℝ := 1 / (1 - u)
  let β : ℝ := (2 - u) / (1 - u) ^ 2
  have hu0le : 0 ≤ u := le_of_lt hu0
  have hden_pos : 0 < 1 - u := by linarith
  have hs : 0 < s := by
    dsimp [s]
    exact div_pos hu0 hden_pos
  have hγ_nonneg : 0 ≤ γ := by
    dsimp [γ]
    positivity
  have hcombo_strict :
      IsStrictlyPositive (a • A + b • B : CStarMatrix ι ι ℂ) :=
    strictPositiveCStarMatrixCone_convex
      (by simpa using hA) (by simpa using hB) ha hb hab
  have hshift_comm (C : CStarMatrix ι ι ℂ) :
      cfc (p := IsSelfAdjoint) (fun x : ℝ => (s + x)⁻¹) C =
        cfc (p := IsSelfAdjoint) (fun x : ℝ => (x + s)⁻¹) C := by
    refine cfc_congr ?_
    intro x _hx
    change (s + x)⁻¹ = (x + s)⁻¹
    rw [add_comm s x]
  have hshift_base :
      cfc (p := IsSelfAdjoint) (fun x : ℝ => (x + s)⁻¹)
          (a • A + b • B) ≤
        a • cfc (p := IsSelfAdjoint) (fun x : ℝ => (x + s)⁻¹) A +
          b • cfc (p := IsSelfAdjoint) (fun x : ℝ => (x + s)⁻¹) B := by
    have hbase :=
      cstarMatrix_cfc_shifted_inv_convex_nonneg
        (A := A) (B := B) hA.nonneg hB.nonneg (s := s) hs ha hb hab
    simpa [hshift_comm] using hbase
  have hshift_scaled :
      γ • cfc (p := IsSelfAdjoint) (fun x : ℝ => (x + s)⁻¹)
          (a • A + b • B) ≤
        γ • (a • cfc (p := IsSelfAdjoint) (fun x : ℝ => (x + s)⁻¹) A +
          b • cfc (p := IsSelfAdjoint) (fun x : ℝ => (x + s)⁻¹) B) := by
    exact smul_le_smul_of_nonneg_left hshift_base hγ_nonneg
  have hβsplit :
      β • (1 : CStarMatrix ι ι ℂ) =
        a • (β • (1 : CStarMatrix ι ι ℂ)) +
          b • (β • (1 : CStarMatrix ι ι ℂ)) := by
    calc
      β • (1 : CStarMatrix ι ι ℂ) =
          (a + b) • (β • (1 : CStarMatrix ι ι ℂ)) := by
            rw [hab]
            module
      _ = a • (β • (1 : CStarMatrix ι ι ℂ)) +
          b • (β • (1 : CStarMatrix ι ι ℂ)) := by
            module
  have haffine :
      α • (a • A + b • B : CStarMatrix ι ι ℂ) -
          β • (1 : CStarMatrix ι ι ℂ) +
          γ • (a • cfc (p := IsSelfAdjoint) (fun x : ℝ => (x + s)⁻¹) A +
            b • cfc (p := IsSelfAdjoint) (fun x : ℝ => (x + s)⁻¹) B) =
        a • (α • A - β • (1 : CStarMatrix ι ι ℂ) +
            γ • cfc (p := IsSelfAdjoint) (fun x : ℝ => (x + s)⁻¹) A) +
          b • (α • B - β • (1 : CStarMatrix ι ι ℂ) +
            γ • cfc (p := IsSelfAdjoint) (fun x : ℝ => (x + s)⁻¹) B) := by
    conv_lhs =>
      rw [hβsplit]
    module
  rw [cstarMatrix_cfc_unit_interval_xlog_integrand_eq_affine_add_shifted_inv
      hcombo_strict hu0le hu1,
    cstarMatrix_cfc_unit_interval_xlog_integrand_eq_affine_add_shifted_inv
      hA hu0le hu1,
    cstarMatrix_cfc_unit_interval_xlog_integrand_eq_affine_add_shifted_inv
      hB hu0le hu1]
  change
    α • (a • A + b • B : CStarMatrix ι ι ℂ) -
        β • (1 : CStarMatrix ι ι ℂ) +
        γ • cfc (p := IsSelfAdjoint) (fun x : ℝ => (x + s)⁻¹)
          (a • A + b • B) ≤
      a • (α • A - β • (1 : CStarMatrix ι ι ℂ) +
          γ • cfc (p := IsSelfAdjoint) (fun x : ℝ => (x + s)⁻¹) A) +
        b • (α • B - β • (1 : CStarMatrix ι ι ℂ) +
          γ • cfc (p := IsSelfAdjoint) (fun x : ℝ => (x + s)⁻¹) B)
  calc
    α • (a • A + b • B : CStarMatrix ι ι ℂ) -
        β • (1 : CStarMatrix ι ι ℂ) +
        γ • cfc (p := IsSelfAdjoint) (fun x : ℝ => (x + s)⁻¹)
          (a • A + b • B) ≤
        α • (a • A + b • B : CStarMatrix ι ι ℂ) -
          β • (1 : CStarMatrix ι ι ℂ) +
          γ • (a • cfc (p := IsSelfAdjoint) (fun x : ℝ => (x + s)⁻¹) A +
            b • cfc (p := IsSelfAdjoint) (fun x : ℝ => (x + s)⁻¹) B) := by
          simpa [add_comm, add_left_comm, add_assoc] using
            add_le_add_left hshift_scaled
              (α • (a • A + b • B : CStarMatrix ι ι ℂ) -
                β • (1 : CStarMatrix ι ι ℂ))
    _ = a • (α • A - β • (1 : CStarMatrix ι ι ℂ) +
          γ • cfc (p := IsSelfAdjoint) (fun x : ℝ => (x + s)⁻¹) A) +
        b • (α • B - β • (1 : CStarMatrix ι ι ℂ) +
          γ • cfc (p := IsSelfAdjoint) (fun x : ℝ => (x + s)⁻¹) B) := haffine

/-- Interior unit-interval convexity of the actual `x log x` kernel integrand.

For `0 < u < 1`, the CFC integrand
`x ↦ x * (x - 1) / (u + (1 - u) x)` is operator-convex on the strictly
positive finite C-star matrix cone.  This is the pointwise convexity theorem
for the integrand that appears after multiplying the normalized logarithmic
kernel by `x - 1`, hence it is the source-aligned direct-route dependency for
operator convexity of `x ↦ x log x`. -/
theorem cstarMatrix_cfc_unit_interval_xlog_kernel_integrand_convex_of_pos_lt_one
    {ι : Type*} [Fintype ι] [DecidableEq ι]
    {A B : CStarMatrix ι ι ℂ} (hA : IsStrictlyPositive A)
    (hB : IsStrictlyPositive B)
    {u : ℝ} (hu0 : 0 < u) (hu1 : u < 1)
    {a b : ℝ} (ha : 0 ≤ a) (hb : 0 ≤ b) (hab : a + b = 1) :
    cfc (p := IsSelfAdjoint)
        (fun x : ℝ => x * (x - 1) / (u + (1 - u) * x))
        (a • A + b • B) ≤
      a • cfc (p := IsSelfAdjoint)
          (fun x : ℝ => x * (x - 1) / (u + (1 - u) * x)) A +
        b • cfc (p := IsSelfAdjoint)
          (fun x : ℝ => x * (x - 1) / (u + (1 - u) * x)) B := by
  let s : ℝ := u / (1 - u)
  let γ : ℝ := u / (1 - u) ^ 3
  let α : ℝ := 1 / (1 - u)
  let β : ℝ := 1 / (1 - u) ^ 2
  have hu0le : 0 ≤ u := le_of_lt hu0
  have hden_pos : 0 < 1 - u := by linarith
  have hs : 0 < s := by
    dsimp [s]
    exact div_pos hu0 hden_pos
  have hγ_nonneg : 0 ≤ γ := by
    dsimp [γ]
    positivity
  have hcombo_strict :
      IsStrictlyPositive (a • A + b • B : CStarMatrix ι ι ℂ) :=
    strictPositiveCStarMatrixCone_convex
      (by simpa using hA) (by simpa using hB) ha hb hab
  have hshift_comm (C : CStarMatrix ι ι ℂ) :
      cfc (p := IsSelfAdjoint) (fun x : ℝ => (s + x)⁻¹) C =
        cfc (p := IsSelfAdjoint) (fun x : ℝ => (x + s)⁻¹) C := by
    refine cfc_congr ?_
    intro x _hx
    change (s + x)⁻¹ = (x + s)⁻¹
    rw [add_comm s x]
  have hshift_base :
      cfc (p := IsSelfAdjoint) (fun x : ℝ => (x + s)⁻¹)
          (a • A + b • B) ≤
        a • cfc (p := IsSelfAdjoint) (fun x : ℝ => (x + s)⁻¹) A +
          b • cfc (p := IsSelfAdjoint) (fun x : ℝ => (x + s)⁻¹) B := by
    have hbase :=
      cstarMatrix_cfc_shifted_inv_convex_nonneg
        (A := A) (B := B) hA.nonneg hB.nonneg (s := s) hs ha hb hab
    simpa [hshift_comm] using hbase
  have hshift_scaled :
      γ • cfc (p := IsSelfAdjoint) (fun x : ℝ => (x + s)⁻¹)
          (a • A + b • B) ≤
        γ • (a • cfc (p := IsSelfAdjoint) (fun x : ℝ => (x + s)⁻¹) A +
          b • cfc (p := IsSelfAdjoint) (fun x : ℝ => (x + s)⁻¹) B) := by
    exact smul_le_smul_of_nonneg_left hshift_base hγ_nonneg
  have hβsplit :
      β • (1 : CStarMatrix ι ι ℂ) =
        a • (β • (1 : CStarMatrix ι ι ℂ)) +
          b • (β • (1 : CStarMatrix ι ι ℂ)) := by
    calc
      β • (1 : CStarMatrix ι ι ℂ) =
          (a + b) • (β • (1 : CStarMatrix ι ι ℂ)) := by
            rw [hab]
            module
      _ = a • (β • (1 : CStarMatrix ι ι ℂ)) +
          b • (β • (1 : CStarMatrix ι ι ℂ)) := by
            module
  have haffine :
      α • (a • A + b • B : CStarMatrix ι ι ℂ) -
          β • (1 : CStarMatrix ι ι ℂ) +
          γ • (a • cfc (p := IsSelfAdjoint) (fun x : ℝ => (x + s)⁻¹) A +
            b • cfc (p := IsSelfAdjoint) (fun x : ℝ => (x + s)⁻¹) B) =
        a • (α • A - β • (1 : CStarMatrix ι ι ℂ) +
            γ • cfc (p := IsSelfAdjoint) (fun x : ℝ => (x + s)⁻¹) A) +
          b • (α • B - β • (1 : CStarMatrix ι ι ℂ) +
            γ • cfc (p := IsSelfAdjoint) (fun x : ℝ => (x + s)⁻¹) B) := by
    conv_lhs =>
      rw [hβsplit]
    module
  rw [cstarMatrix_cfc_unit_interval_xlog_kernel_integrand_eq_affine_add_shifted_inv
      hcombo_strict hu0le hu1,
    cstarMatrix_cfc_unit_interval_xlog_kernel_integrand_eq_affine_add_shifted_inv
      hA hu0le hu1,
    cstarMatrix_cfc_unit_interval_xlog_kernel_integrand_eq_affine_add_shifted_inv
      hB hu0le hu1]
  change
    α • (a • A + b • B : CStarMatrix ι ι ℂ) -
        β • (1 : CStarMatrix ι ι ℂ) +
        γ • cfc (p := IsSelfAdjoint) (fun x : ℝ => (x + s)⁻¹)
          (a • A + b • B) ≤
      a • (α • A - β • (1 : CStarMatrix ι ι ℂ) +
          γ • cfc (p := IsSelfAdjoint) (fun x : ℝ => (x + s)⁻¹) A) +
        b • (α • B - β • (1 : CStarMatrix ι ι ℂ) +
          γ • cfc (p := IsSelfAdjoint) (fun x : ℝ => (x + s)⁻¹) B)
  calc
    α • (a • A + b • B : CStarMatrix ι ι ℂ) -
        β • (1 : CStarMatrix ι ι ℂ) +
        γ • cfc (p := IsSelfAdjoint) (fun x : ℝ => (x + s)⁻¹)
          (a • A + b • B) ≤
        α • (a • A + b • B : CStarMatrix ι ι ℂ) -
          β • (1 : CStarMatrix ι ι ℂ) +
          γ • (a • cfc (p := IsSelfAdjoint) (fun x : ℝ => (x + s)⁻¹) A +
            b • cfc (p := IsSelfAdjoint) (fun x : ℝ => (x + s)⁻¹) B) := by
          simpa [add_comm, add_left_comm, add_assoc] using
            add_le_add_left hshift_scaled
              (α • (a • A + b • B : CStarMatrix ι ι ℂ) -
                β • (1 : CStarMatrix ι ι ℂ))
    _ = a • (α • A - β • (1 : CStarMatrix ι ι ℂ) +
          γ • cfc (p := IsSelfAdjoint) (fun x : ℝ => (x + s)⁻¹) A) +
        b • (α • B - β • (1 : CStarMatrix ι ι ℂ) +
          γ • cfc (p := IsSelfAdjoint) (fun x : ℝ => (x + s)⁻¹) B) := haffine

open MeasureTheory Set Function in
/-- Positive-cone operator convexity of `x ↦ x log x` from the corrected
unit-interval kernel route.

This theorem closes the direct finite-dimensional operator-convexity
dependency for `x log x`: the CFC integral representation reduces the claim to
the pointwise interior kernel convexity theorem, and endpoints are removed by
the almost-everywhere equality `Ioo =ᵐ Icc`. -/
theorem cstarMatrixXLogXPositiveOperatorConvexTarget_of_unit_interval_kernel
    {ι : Type*} [Fintype ι] [DecidableEq ι] :
    cstarMatrixXLogXPositiveOperatorConvexTarget (ι := ι) := by
  intro a b ha hb hab A B hA hB
  letI : IsBoundedSMul ℝ (CStarMatrix ι ι ℂ) :=
    cstarMatrix_real_isBoundedSMul
  let C : CStarMatrix ι ι ℂ := a • A + b • B
  have hC : IsStrictlyPositive C :=
    strictPositiveCStarMatrixCone_convex
      (by simpa using hA) (by simpa using hB) ha hb hab
  rcases (spectrum.isBounded (𝕜 := ℝ) C).bddAbove with ⟨MC, hMC⟩
  rcases (spectrum.isBounded (𝕜 := ℝ) A).bddAbove with ⟨MA, hMA⟩
  rcases (spectrum.isBounded (𝕜 := ℝ) B).bddAbove with ⟨MB, hMB⟩
  let fC : ℝ → CStarMatrix ι ι ℂ := fun u =>
    cfc (p := IsSelfAdjoint)
      (fun z : ℝ => z * (z - 1) / (u + (1 - u) * z)) C
  let fA : ℝ → CStarMatrix ι ι ℂ := fun u =>
    cfc (p := IsSelfAdjoint)
      (fun z : ℝ => z * (z - 1) / (u + (1 - u) * z)) A
  let fB : ℝ → CStarMatrix ι ι ℂ := fun u =>
    cfc (p := IsSelfAdjoint)
      (fun z : ℝ => z * (z - 1) / (u + (1 - u) * z)) B
  have hC_Icc : IntegrableOn fC (Set.Icc (0 : ℝ) 1) := by
    exact integrableOn_cfc
      (hs := (measurableSet_Icc : MeasurableSet (Set.Icc (0 : ℝ) 1)))
      (f := fun u z : ℝ => z * (z - 1) / (u + (1 - u) * z))
      (bound := fun _ : ℝ => (max 1 MC) ^ 2)
      (a := C)
      (hf := continuousOn_uncurry_unit_interval_xlog_kernel_spectrum hC)
      (bound_ge := ae_unit_interval_xlog_kernel_spectrum_norm_le_max_sq hC hMC)
      (bound_int := hasFiniteIntegral_const_max_one_spectrum_bound_sq MC)
      (ha := hC.isSelfAdjoint)
  have hA_Icc : IntegrableOn fA (Set.Icc (0 : ℝ) 1) := by
    exact integrableOn_cfc
      (hs := (measurableSet_Icc : MeasurableSet (Set.Icc (0 : ℝ) 1)))
      (f := fun u z : ℝ => z * (z - 1) / (u + (1 - u) * z))
      (bound := fun _ : ℝ => (max 1 MA) ^ 2)
      (a := A)
      (hf := continuousOn_uncurry_unit_interval_xlog_kernel_spectrum hA)
      (bound_ge := ae_unit_interval_xlog_kernel_spectrum_norm_le_max_sq hA hMA)
      (bound_int := hasFiniteIntegral_const_max_one_spectrum_bound_sq MA)
      (ha := hA.isSelfAdjoint)
  have hB_Icc : IntegrableOn fB (Set.Icc (0 : ℝ) 1) := by
    exact integrableOn_cfc
      (hs := (measurableSet_Icc : MeasurableSet (Set.Icc (0 : ℝ) 1)))
      (f := fun u z : ℝ => z * (z - 1) / (u + (1 - u) * z))
      (bound := fun _ : ℝ => (max 1 MB) ^ 2)
      (a := B)
      (hf := continuousOn_uncurry_unit_interval_xlog_kernel_spectrum hB)
      (bound_ge := ae_unit_interval_xlog_kernel_spectrum_norm_le_max_sq hB hMB)
      (bound_int := hasFiniteIntegral_const_max_one_spectrum_bound_sq MB)
      (ha := hB.isSelfAdjoint)
  have hC_Ioo : IntegrableOn fC (Set.Ioo (0 : ℝ) 1) :=
    hC_Icc.mono_set Ioo_subset_Icc_self
  have hA_Ioo : IntegrableOn fA (Set.Ioo (0 : ℝ) 1) :=
    hA_Icc.mono_set Ioo_subset_Icc_self
  have hB_Ioo : IntegrableOn fB (Set.Ioo (0 : ℝ) 1) :=
    hB_Icc.mono_set Ioo_subset_Icc_self
  have hR_Ioo :
      IntegrableOn (fun u : ℝ => a • fA u + b • fB u)
        (Set.Ioo (0 : ℝ) 1) :=
    by
      change IntegrableOn (fun u : ℝ => (a : ℂ) • fA u + (b : ℂ) • fB u)
        (Set.Ioo (0 : ℝ) 1)
      exact (hA_Ioo.smul (a : ℂ)).add (hB_Ioo.smul (b : ℂ))
  have hmono :
      ∀ u ∈ Set.Ioo (0 : ℝ) 1, fC u ≤ a • fA u + b • fB u := by
    intro u hu
    exact cstarMatrix_cfc_unit_interval_xlog_kernel_integrand_convex_of_pos_lt_one
      hA hB hu.1 hu.2 ha hb hab
  have hineq :
      ∫ u in Set.Ioo (0 : ℝ) 1, fC u ≤
        ∫ u in Set.Ioo (0 : ℝ) 1, (a • fA u + b • fB u) := by
    exact cstarMatrix_setIntegral_mono_on hC_Ioo hR_Ioo measurableSet_Ioo hmono
  have hRint :
      (∫ u in Set.Ioo (0 : ℝ) 1, (a • fA u + b • fB u)) =
        a • (∫ u in Set.Ioo (0 : ℝ) 1, fA u) +
          b • (∫ u in Set.Ioo (0 : ℝ) 1, fB u) := by
    change (∫ u in Set.Ioo (0 : ℝ) 1, ((a : ℂ) • fA) u + ((b : ℂ) • fB) u) =
        (a : ℂ) • (∫ u in Set.Ioo (0 : ℝ) 1, fA u) +
          (b : ℂ) • (∫ u in Set.Ioo (0 : ℝ) 1, fB u)
    rw [MeasureTheory.integral_add (hA_Ioo.smul (a : ℂ)) (hB_Ioo.smul (b : ℂ))]
    simp_rw [Pi.smul_apply]
    rw [MeasureTheory.integral_smul, MeasureTheory.integral_smul]
  have hC_Icc_Ioo :
      (∫ u in Set.Icc (0 : ℝ) 1, fC u) =
        ∫ u in Set.Ioo (0 : ℝ) 1, fC u := by
    exact (setIntegral_congr_set (Ioo_ae_eq_Icc (a := (0 : ℝ)) (b := 1))).symm
  have hA_Icc_Ioo :
      (∫ u in Set.Icc (0 : ℝ) 1, fA u) =
        ∫ u in Set.Ioo (0 : ℝ) 1, fA u := by
    exact (setIntegral_congr_set (Ioo_ae_eq_Icc (a := (0 : ℝ)) (b := 1))).symm
  have hB_Icc_Ioo :
      (∫ u in Set.Icc (0 : ℝ) 1, fB u) =
        ∫ u in Set.Ioo (0 : ℝ) 1, fB u := by
    exact (setIntegral_congr_set (Ioo_ae_eq_Icc (a := (0 : ℝ)) (b := 1))).symm
  have hrepC :=
    cstarMatrix_cfc_xlog_eq_unit_interval_xlog_kernel_integral hC hMC
  have hrepA :=
    cstarMatrix_cfc_xlog_eq_unit_interval_xlog_kernel_integral hA hMA
  have hrepB :=
    cstarMatrix_cfc_xlog_eq_unit_interval_xlog_kernel_integral hB hMB
  calc
    cfc (p := IsSelfAdjoint) (fun x : ℝ => x * Real.log x)
        (a • A + b • B : CStarMatrix ι ι ℂ) =
        ∫ u in Set.Icc (0 : ℝ) 1, fC u := by
          simpa [C, fC] using hrepC
    _ = ∫ u in Set.Ioo (0 : ℝ) 1, fC u := hC_Icc_Ioo
    _ ≤ ∫ u in Set.Ioo (0 : ℝ) 1, (a • fA u + b • fB u) := hineq
    _ = a • (∫ u in Set.Ioo (0 : ℝ) 1, fA u) +
          b • (∫ u in Set.Ioo (0 : ℝ) 1, fB u) := hRint
    _ = a • (∫ u in Set.Icc (0 : ℝ) 1, fA u) +
          b • (∫ u in Set.Icc (0 : ℝ) 1, fB u) := by
          rw [hA_Icc_Ioo, hB_Icc_Ioo]
    _ = a • cfc (p := IsSelfAdjoint) (fun x : ℝ => x * Real.log x) A +
          b • cfc (p := IsSelfAdjoint) (fun x : ℝ => x * Real.log x) B := by
          rw [hrepA, hrepB]

/-- The direct kernel route closes ordinary positive-cone operator convexity of
`x ↦ x log x` at every finite matrix size, which is the source-faithful
hypothesis used by the Hansen-Pedersen block-matrix route. -/
theorem cstarMatrixXLogXPositiveOperatorConvexAllFiniteTarget_of_unit_interval_kernel.{u} :
    cstarMatrixXLogXPositiveOperatorConvexAllFiniteTarget.{u} := by
  intro κ _ _
  exact cstarMatrixXLogXPositiveOperatorConvexTarget_of_unit_interval_kernel
    (ι := κ)

/-- Concrete Hansen-Pedersen two-point Jensen theorem for `x ↦ x log x`.

This uses the reflection-average proof route: the direct kernel integral route
gives all-finite-size operator convexity, the reflection pinching inequality
compresses the block average, and
`cstarMatrixColumnPair_reflectionAverage_xlog_corner_of_sum` identifies the
compressed nonlinear corner with the CFC of the compressed corner. -/
theorem cstarMatrixXLogXHansenPedersenJensenTarget_of_reflectionAverage_xlog_corner
    {ι : Type u} [Fintype ι] [DecidableEq ι] :
    cstarMatrixXLogXHansenPedersenJensenTarget (ι := ι) := by
  intro A B T1 T2 hT1 hT2 hAB
  let f : ℝ → ℝ := fun x => x * Real.log x
  let V : CStarMatrix (ι ⊕ ι) ι ℂ := cstarMatrixColumnPair A B
  let D : CStarMatrix (ι ⊕ ι) (ι ⊕ ι) ℂ :=
    cstarMatrixBlockDiagonal T1 T2
  have hD : IsStrictlyPositive D := by
    dsimp [D]
    exact cstarMatrixBlockDiagonal_isStrictlyPositive hT1 hT2
  have hfD : ContinuousOn f (spectrum ℝ D) := by
    intro x hx
    have hx_nonneg : 0 ≤ x :=
      cstarMatrix_spectrum_nonneg_of_nonneg hD.nonneg hx
    have hx_ne : x ≠ 0 := by
      intro hxeq
      exact (spectrum.zero_notMem ℝ hD.isUnit) (by simpa [hxeq] using hx)
    exact ((continuousAt_id.mul
      (Real.continuousAt_log hx_ne))).continuousWithinAt
  have hfUnion : ContinuousOn f (spectrum ℝ T1 ∪ spectrum ℝ T2) := by
    intro x hx
    have hx_mem : x ∈ spectrum ℝ T1 ∨ x ∈ spectrum ℝ T2 := by
      simpa using hx
    have hx_pos : 0 < x := by
      rcases hx_mem with hx1 | hx2
      · have hx_nonneg : 0 ≤ x :=
          cstarMatrix_spectrum_nonneg_of_nonneg hT1.nonneg hx1
        have hx_ne : x ≠ 0 := by
          intro hxeq
          exact (spectrum.zero_notMem ℝ hT1.isUnit)
            (by simpa [hxeq] using hx1)
        exact lt_of_le_of_ne hx_nonneg (Ne.symm hx_ne)
      · have hx_nonneg : 0 ≤ x :=
          cstarMatrix_spectrum_nonneg_of_nonneg hT2.nonneg hx2
        have hx_ne : x ≠ 0 := by
          intro hxeq
          exact (spectrum.zero_notMem ℝ hT2.isUnit)
            (by simpa [hxeq] using hx2)
        exact lt_of_le_of_ne hx_nonneg (Ne.symm hx_ne)
    have hx_ne : x ≠ 0 := ne_of_gt hx_pos
    exact ((continuousAt_id.mul
      (Real.continuousAt_log hx_ne))).continuousWithinAt
  have hpinch :=
    cstarMatrixColumnPair_reflectionAverage_compressed_cfc_le_compressed_of_sum
      (A := A) (B := B) hAB f
      cstarMatrixXLogXPositiveOperatorConvexAllFiniteTarget_of_unit_interval_kernel
      D hD hfD
  have hcorner :=
    cstarMatrixColumnPair_reflectionAverage_xlog_corner_of_sum
      (A := A) (B := B) hAB D hD
  have hdiag :=
    cstarMatrixBlockDiagonal_cfc f T1 T2
      hT1.isSelfAdjoint hT2.isSelfAdjoint hfUnion
  have hleftCompress :
      CStarMatrix.conjTranspose V * D * V =
        star A * T1 * A + star B * T2 * B := by
    dsimp [V, D]
    exact cstarMatrixColumnPair_conjTranspose_mul_blockDiagonal_mul_columnPair
      A B T1 T2
  have hrightCompress :
      CStarMatrix.conjTranspose V * cfc (p := IsSelfAdjoint) f D * V =
        star A * cfc (p := IsSelfAdjoint) f T1 * A +
          star B * cfc (p := IsSelfAdjoint) f T2 * B := by
    rw [hdiag]
    dsimp [V]
    exact cstarMatrixColumnPair_conjTranspose_mul_blockDiagonal_mul_columnPair
      A B (cfc (p := IsSelfAdjoint) f T1)
      (cfc (p := IsSelfAdjoint) f T2)
  have htarget :
      cfc (p := IsSelfAdjoint) f
          (CStarMatrix.conjTranspose V * D * V) ≤
        CStarMatrix.conjTranspose V *
          cfc (p := IsSelfAdjoint) f D * V := by
    simpa [V, D, f] using hcorner ▸ hpinch
  calc
    cfc (p := IsSelfAdjoint) (fun x : ℝ => x * Real.log x)
        (star A * T1 * A + star B * T2 * B) =
        cfc (p := IsSelfAdjoint) f
          (CStarMatrix.conjTranspose V * D * V) := by
          rw [hleftCompress]
    _ ≤ CStarMatrix.conjTranspose V *
          cfc (p := IsSelfAdjoint) f D * V := htarget
    _ = star A *
          cfc (p := IsSelfAdjoint) (fun x : ℝ => x * Real.log x) T1 * A +
          star B *
            cfc (p := IsSelfAdjoint) (fun x : ℝ => x * Real.log x) T2 * B := by
          simpa [f] using hrightCompress

/-- The concrete Hansen-Pedersen source target now follows from the
reflection-average proof, without assuming a separate transfer theorem. -/
theorem cstarMatrixXLogXHansenPedersenJensenTarget_of_unit_interval_kernel
    {ι : Type u} [Fintype ι] [DecidableEq ι] :
    cstarMatrixXLogXHansenPedersenJensenTarget (ι := ι) :=
  cstarMatrixXLogXHansenPedersenJensenTarget_of_reflectionAverage_xlog_corner

/-- Functional-calculus expansion of the normalized entropy kernel
`x log x - (x - 1)` on the strictly positive cone. -/
theorem cstarMatrix_cfc_realEntropyKernel_eq_xlog_sub_id_add_one
    {ι : Type*} [Fintype ι] [DecidableEq ι]
    {A : CStarMatrix ι ι ℂ} (hA : IsStrictlyPositive A) :
    cfc (p := IsSelfAdjoint) realEntropyKernel A =
      cfc (p := IsSelfAdjoint) (fun x : ℝ => x * Real.log x) A -
        A + 1 := by
  have hlog_cont : ContinuousOn Real.log (spectrum ℝ A) := by
    intro x hx
    have hx_ne : x ≠ 0 := by
      intro hxeq
      exact (spectrum.zero_notMem ℝ hA.isUnit) (by simpa [hxeq] using hx)
    exact (Real.continuousAt_log hx_ne).continuousWithinAt
  have hxlog_cont :
      ContinuousOn (fun x : ℝ => x * Real.log x) (spectrum ℝ A) :=
    continuousOn_id.mul hlog_cont
  have hlin_cont : ContinuousOn (fun x : ℝ => x - 1) (spectrum ℝ A) := by
    fun_prop
  have hlin :
      cfc (p := IsSelfAdjoint) (fun x : ℝ => x - 1) A =
        A - 1 := by
    rw [cfc_sub (f := fun x : ℝ => x) (g := fun _ : ℝ => 1) (a := A)
      (hf := by fun_prop) (hg := by fun_prop)]
    have hid :
        cfc (p := IsSelfAdjoint) (fun x : ℝ => x) A = A :=
      cfc_id' ℝ A hA.isSelfAdjoint
    have hone :
        cfc (p := IsSelfAdjoint) (fun _ : ℝ => 1) A = 1 := by
      rw [cfc_const_one ℝ A]
    rw [hid, hone]
  rw [show realEntropyKernel = fun x : ℝ => (x * Real.log x) - (x - 1) by
    funext x
    rfl]
  rw [cfc_sub (f := fun x : ℝ => x * Real.log x)
    (g := fun x : ℝ => x - 1) (a := A)
    (hf := hxlog_cont) (hg := hlin_cont)]
  rw [hlin]
  abel

/-- Ordinary operator convexity of the normalized entropy kernel follows from
ordinary operator convexity of `x log x` plus affine correction. -/
theorem cstarMatrixEntropyKernelPositiveOperatorConvexTarget_of_xlog
    {ι : Type*} [Fintype ι] [DecidableEq ι]
    (hxlog : cstarMatrixXLogXPositiveOperatorConvexTarget (ι := ι)) :
    cstarMatrixEntropyKernelPositiveOperatorConvexTarget (ι := ι) := by
  intro a b ha hb hab A B hA hB
  let C : CStarMatrix ι ι ℂ := a • A + b • B
  have hC : IsStrictlyPositive C := by
    exact (strictPositiveCStarMatrixCone_convex (ι := ι))
      (by simpa [strictPositiveCStarMatrixCone] using hA)
      (by simpa [strictPositiveCStarMatrixCone] using hB)
      ha hb hab
  have hx := hxlog a b ha hb hab A B hA hB
  have hshift :
      cfc (p := IsSelfAdjoint) (fun x : ℝ => x * Real.log x) C - C + 1 ≤
        (a • cfc (p := IsSelfAdjoint)
            (fun x : ℝ => x * Real.log x) A +
          b • cfc (p := IsSelfAdjoint)
            (fun x : ℝ => x * Real.log x) B) - C + 1 := by
    simpa [sub_eq_add_neg, add_assoc, add_comm, add_left_comm] using
      add_le_add_right hx (-C + 1)
  have hleft :
      cfc (p := IsSelfAdjoint) realEntropyKernel C =
        cfc (p := IsSelfAdjoint) (fun x : ℝ => x * Real.log x) C - C + 1 :=
    cstarMatrix_cfc_realEntropyKernel_eq_xlog_sub_id_add_one hC
  have hright :
      a • cfc (p := IsSelfAdjoint) realEntropyKernel A +
          b • cfc (p := IsSelfAdjoint) realEntropyKernel B =
        (a • cfc (p := IsSelfAdjoint)
            (fun x : ℝ => x * Real.log x) A +
          b • cfc (p := IsSelfAdjoint)
            (fun x : ℝ => x * Real.log x) B) - C + 1 := by
    rw [cstarMatrix_cfc_realEntropyKernel_eq_xlog_sub_id_add_one hA,
      cstarMatrix_cfc_realEntropyKernel_eq_xlog_sub_id_add_one hB]
    calc
      a • (cfc (p := IsSelfAdjoint) (fun x : ℝ => x * Real.log x) A -
            A + 1) +
          b • (cfc (p := IsSelfAdjoint) (fun x : ℝ => x * Real.log x) B -
            B + 1) =
        (a • cfc (p := IsSelfAdjoint) (fun x : ℝ => x * Real.log x) A +
          b • cfc (p := IsSelfAdjoint) (fun x : ℝ => x * Real.log x) B) -
            (a • A + b • B) + (a + b) • (1 : CStarMatrix ι ι ℂ) := by
            module
      _ =
        (a • cfc (p := IsSelfAdjoint) (fun x : ℝ => x * Real.log x) A +
          b • cfc (p := IsSelfAdjoint) (fun x : ℝ => x * Real.log x) B) -
            C + 1 := by
            dsimp [C]
            ext i j
            simp [CStarMatrix.smul_apply, CStarMatrix.one_apply, hab]
  rw [hleft, hright]
  exact hshift

/-- Unconditional ordinary positive-cone operator convexity of the normalized
entropy kernel. -/
theorem cstarMatrixEntropyKernelPositiveOperatorConvexTarget_of_unit_interval_kernel
    {ι : Type*} [Fintype ι] [DecidableEq ι] :
    cstarMatrixEntropyKernelPositiveOperatorConvexTarget (ι := ι) :=
  cstarMatrixEntropyKernelPositiveOperatorConvexTarget_of_xlog
    cstarMatrixXLogXPositiveOperatorConvexTarget_of_unit_interval_kernel

/-- All-finite-size ordinary operator convexity of the normalized entropy
kernel. -/
theorem cstarMatrixEntropyKernelPositiveOperatorConvexAllFiniteTarget_of_unit_interval_kernel.{u} :
    cstarMatrixEntropyKernelPositiveOperatorConvexAllFiniteTarget.{u} := by
  intro κ _ _
  exact cstarMatrixEntropyKernelPositiveOperatorConvexTarget_of_unit_interval_kernel

/-- The concrete Hansen-Pedersen Jensen theorem for the normalized entropy
kernel follows from the already proved `x log x` theorem plus affine
linearity.  This is the function that the finite matrix-perspective route uses
for normalized matrix relative entropy. -/
theorem cstarMatrixEntropyKernelHansenPedersenJensenTarget_of_xlog
    {ι : Type*} [Fintype ι] [DecidableEq ι]
    (hxlog : cstarMatrixXLogXHansenPedersenJensenTarget (ι := ι)) :
    cstarMatrixEntropyKernelHansenPedersenJensenTarget (ι := ι) := by
  intro A B T1 T2 hT1 hT2 hAB
  let C : CStarMatrix ι ι ℂ := star A * T1 * A + star B * T2 * B
  have hC : IsStrictlyPositive C :=
    cstarMatrixHansenPedersenCompression_isStrictlyPositive_of_sum
      (A := A) (B := B) (T1 := T1) (T2 := T2) hAB hT1 hT2
  have hx :=
    hxlog A B T1 T2 hT1 hT2 hAB
  have hshift :
      cfc (p := IsSelfAdjoint) (fun x : ℝ => x * Real.log x) C - C + 1 ≤
        (star A * cfc (p := IsSelfAdjoint)
            (fun x : ℝ => x * Real.log x) T1 * A +
          star B * cfc (p := IsSelfAdjoint)
            (fun x : ℝ => x * Real.log x) T2 * B) - C + 1 := by
    simpa [sub_eq_add_neg, add_assoc, add_comm, add_left_comm] using
      add_le_add_right hx (-C + 1)
  have hleft :
      cfc (p := IsSelfAdjoint) realEntropyKernel C =
        cfc (p := IsSelfAdjoint) (fun x : ℝ => x * Real.log x) C - C + 1 :=
    cstarMatrix_cfc_realEntropyKernel_eq_xlog_sub_id_add_one hC
  have hright :
      star A * cfc (p := IsSelfAdjoint) realEntropyKernel T1 * A +
          star B * cfc (p := IsSelfAdjoint) realEntropyKernel T2 * B =
        (star A * cfc (p := IsSelfAdjoint)
            (fun x : ℝ => x * Real.log x) T1 * A +
          star B * cfc (p := IsSelfAdjoint)
            (fun x : ℝ => x * Real.log x) T2 * B) - C + 1 := by
    rw [cstarMatrix_cfc_realEntropyKernel_eq_xlog_sub_id_add_one hT1,
      cstarMatrix_cfc_realEntropyKernel_eq_xlog_sub_id_add_one hT2]
    let F1 : CStarMatrix ι ι ℂ :=
      cfc (p := IsSelfAdjoint) (fun x : ℝ => x * Real.log x) T1
    let F2 : CStarMatrix ι ι ℂ :=
      cfc (p := IsSelfAdjoint) (fun x : ℝ => x * Real.log x) T2
    have hAexp :
        star A * (F1 - T1 + 1) * A =
          star A * F1 * A - star A * T1 * A + star A * A := by
      have hAone :
          star A * (1 : CStarMatrix ι ι ℂ) * A = star A * A := by
        ext i j
        simp [CStarMatrix.mul_apply, CStarMatrix.one_apply]
      ext i j
      simp [F1, CStarMatrix.mul_apply, Finset.sum_add_distrib,
        add_mul, mul_add, sub_eq_add_neg, add_assoc]
      ring_nf
      simpa [CStarMatrix.mul_apply] using congrArg (fun M : CStarMatrix ι ι ℂ => M i j) hAone
    have hBexp :
        star B * (F2 - T2 + 1) * B =
          star B * F2 * B - star B * T2 * B + star B * B := by
      have hBone :
          star B * (1 : CStarMatrix ι ι ℂ) * B = star B * B := by
        ext i j
        simp [CStarMatrix.mul_apply, CStarMatrix.one_apply]
      ext i j
      simp [F2, CStarMatrix.mul_apply, Finset.sum_add_distrib,
        add_mul, mul_add, sub_eq_add_neg, add_assoc]
      ring_nf
      simpa [CStarMatrix.mul_apply] using congrArg (fun M : CStarMatrix ι ι ℂ => M i j) hBone
    calc
      star A * (F1 - T1 + 1) * A +
          star B * (F2 - T2 + 1) * B =
        (star A * F1 * A - star A * T1 * A + star A * A) +
          (star B * F2 * B - star B * T2 * B + star B * B) := by
            rw [hAexp, hBexp]
      _ =
        (star A * F1 * A + star B * F2 * B) -
          (star A * T1 * A + star B * T2 * B) +
          (star A * A + star B * B) := by
            abel
      _ =
        (star A * F1 * A + star B * F2 * B) - C + 1 := by
            dsimp [C]
            rw [hAB]
  rw [hleft, hright]
  exact hshift

/-- Unconditional concrete Hansen-Pedersen Jensen theorem for the normalized
entropy kernel, obtained from the unit-interval `x log x` route. -/
theorem cstarMatrixEntropyKernelHansenPedersenJensenTarget_of_unit_interval_kernel
    {ι : Type*} [Fintype ι] [DecidableEq ι] :
    cstarMatrixEntropyKernelHansenPedersenJensenTarget (ι := ι) :=
  cstarMatrixEntropyKernelHansenPedersenJensenTarget_of_xlog
    cstarMatrixXLogXHansenPedersenJensenTarget_of_unit_interval_kernel

/-!
## Square-root substrate for the finite perspective route

Effros's perspective theorem is stated using \(B^{1/2}\) and \(B^{-1/2}\).
The following local C-star matrix lemmas expose that algebra through the real
continuous functional calculus.  They are still only dependencies for the
perspective route; they do not prove the perspective theorem or relative
entropy joint convexity by themselves.
-/

/-- Positive square root of a finite C-star matrix through real CFC. -/
noncomputable def cstarMatrixPositiveSqrt
    {ι : Type*} [Fintype ι] [DecidableEq ι]
    (A : CStarMatrix ι ι ℂ) : CStarMatrix ι ι ℂ :=
  cfc (p := IsSelfAdjoint) Real.sqrt A

/-- Positive inverse square root of a finite C-star matrix through real CFC. -/
noncomputable def cstarMatrixPositiveInvSqrt
    {ι : Type*} [Fintype ι] [DecidableEq ι]
    (A : CStarMatrix ι ι ℂ) : CStarMatrix ι ι ℂ :=
  cfc (p := IsSelfAdjoint) (fun x : ℝ => (Real.sqrt x)⁻¹) A

/-- The real CFC square root is self-adjoint. -/
theorem cstarMatrixPositiveSqrt_isSelfAdjoint
    {ι : Type*} [Fintype ι] [DecidableEq ι]
    (A : CStarMatrix ι ι ℂ) :
    IsSelfAdjoint (cstarMatrixPositiveSqrt A) := by
  dsimp [cstarMatrixPositiveSqrt]
  exact IsSelfAdjoint.cfc

/-- The real CFC inverse square root is self-adjoint. -/
theorem cstarMatrixPositiveInvSqrt_isSelfAdjoint
    {ι : Type*} [Fintype ι] [DecidableEq ι]
    (A : CStarMatrix ι ι ℂ) :
    IsSelfAdjoint (cstarMatrixPositiveInvSqrt A) := by
  dsimp [cstarMatrixPositiveInvSqrt]
  exact IsSelfAdjoint.cfc

/-- Spectrum-local continuity of `x ↦ (sqrt x)⁻¹` on a strictly positive
finite C-star matrix. -/
theorem continuousOn_real_inv_sqrt_spectrum_of_isStrictlyPositive
    {ι : Type*} [Fintype ι] [DecidableEq ι]
    {A : CStarMatrix ι ι ℂ} (hA : IsStrictlyPositive A) :
    ContinuousOn (fun x : ℝ => (Real.sqrt x)⁻¹) (spectrum ℝ A) := by
  exact (Real.continuous_sqrt.continuousOn).inv₀ (by
    intro x hx
    have hx_nonneg : 0 ≤ x :=
      cstarMatrix_spectrum_nonneg_of_nonneg hA.nonneg hx
    have hx_ne : x ≠ 0 := by
      intro hxeq
      exact (spectrum.zero_notMem ℝ hA.isUnit) (by simpa [hxeq] using hx)
    have hx_pos : 0 < x := lt_of_le_of_ne hx_nonneg (Ne.symm hx_ne)
    exact ne_of_gt (Real.sqrt_pos.2 hx_pos))

/-- The positive CFC square root squares to the original strictly positive
matrix. -/
theorem cstarMatrixPositiveSqrt_mul_self
    {ι : Type*} [Fintype ι] [DecidableEq ι]
    {A : CStarMatrix ι ι ℂ} (hA : IsStrictlyPositive A) :
    cstarMatrixPositiveSqrt A * cstarMatrixPositiveSqrt A = A := by
  have hmul :
      cfc (p := IsSelfAdjoint)
          (fun x : ℝ => Real.sqrt x * Real.sqrt x) A =
        cstarMatrixPositiveSqrt A * cstarMatrixPositiveSqrt A := by
    simpa [cstarMatrixPositiveSqrt] using
      (cfc_mul (p := IsSelfAdjoint)
        (f := Real.sqrt) (g := Real.sqrt) (a := A)
        (hf := Real.continuous_sqrt.continuousOn)
        (hg := Real.continuous_sqrt.continuousOn))
  have hcongr :
      cfc (p := IsSelfAdjoint)
          (fun x : ℝ => Real.sqrt x * Real.sqrt x) A =
        cfc (p := IsSelfAdjoint) (fun x : ℝ => x) A := by
    apply cfc_congr
    intro x hx
    exact Real.mul_self_sqrt
      (cstarMatrix_spectrum_nonneg_of_nonneg hA.nonneg hx)
  rw [← hmul, hcongr]
  exact cfc_id' ℝ A hA.isSelfAdjoint

/-- The inverse square root is a left inverse for the positive square root. -/
theorem cstarMatrixPositiveInvSqrt_mul_sqrt
    {ι : Type*} [Fintype ι] [DecidableEq ι]
    {A : CStarMatrix ι ι ℂ} (hA : IsStrictlyPositive A) :
    cstarMatrixPositiveInvSqrt A * cstarMatrixPositiveSqrt A = 1 := by
  have hmul :
      cfc (p := IsSelfAdjoint)
          (fun x : ℝ => (Real.sqrt x)⁻¹ * Real.sqrt x) A =
        cstarMatrixPositiveInvSqrt A * cstarMatrixPositiveSqrt A := by
    simpa [cstarMatrixPositiveInvSqrt, cstarMatrixPositiveSqrt] using
      (cfc_mul (p := IsSelfAdjoint)
        (f := fun x : ℝ => (Real.sqrt x)⁻¹) (g := Real.sqrt) (a := A)
        (hf := continuousOn_real_inv_sqrt_spectrum_of_isStrictlyPositive hA)
        (hg := Real.continuous_sqrt.continuousOn))
  have hcongr :
      cfc (p := IsSelfAdjoint)
          (fun x : ℝ => (Real.sqrt x)⁻¹ * Real.sqrt x) A =
        cfc (p := IsSelfAdjoint) (fun _ : ℝ => 1) A := by
    apply cfc_congr
    intro x hx
    have hx_nonneg : 0 ≤ x :=
      cstarMatrix_spectrum_nonneg_of_nonneg hA.nonneg hx
    have hx_ne : x ≠ 0 := by
      intro hxeq
      exact (spectrum.zero_notMem ℝ hA.isUnit) (by simpa [hxeq] using hx)
    have hx_pos : 0 < x := lt_of_le_of_ne hx_nonneg (Ne.symm hx_ne)
    have hsqrt_ne : Real.sqrt x ≠ 0 :=
      ne_of_gt (Real.sqrt_pos.2 hx_pos)
    field_simp [hsqrt_ne]
  rw [← hmul, hcongr]
  simpa using
    (cfc_const (R := ℝ) (A := CStarMatrix ι ι ℂ)
      (p := IsSelfAdjoint) (1 : ℝ) A)

/-- The inverse square root is a right inverse for the positive square root. -/
theorem cstarMatrixPositiveSqrt_mul_invSqrt
    {ι : Type*} [Fintype ι] [DecidableEq ι]
    {A : CStarMatrix ι ι ℂ} (hA : IsStrictlyPositive A) :
    cstarMatrixPositiveSqrt A * cstarMatrixPositiveInvSqrt A = 1 := by
  have hmul :
      cfc (p := IsSelfAdjoint)
          (fun x : ℝ => Real.sqrt x * (Real.sqrt x)⁻¹) A =
        cstarMatrixPositiveSqrt A * cstarMatrixPositiveInvSqrt A := by
    simpa [cstarMatrixPositiveInvSqrt, cstarMatrixPositiveSqrt] using
      (cfc_mul (p := IsSelfAdjoint)
        (f := Real.sqrt) (g := fun x : ℝ => (Real.sqrt x)⁻¹) (a := A)
        (hf := Real.continuous_sqrt.continuousOn)
        (hg := continuousOn_real_inv_sqrt_spectrum_of_isStrictlyPositive hA))
  have hcongr :
      cfc (p := IsSelfAdjoint)
          (fun x : ℝ => Real.sqrt x * (Real.sqrt x)⁻¹) A =
        cfc (p := IsSelfAdjoint) (fun _ : ℝ => 1) A := by
    apply cfc_congr
    intro x hx
    have hx_nonneg : 0 ≤ x :=
      cstarMatrix_spectrum_nonneg_of_nonneg hA.nonneg hx
    have hx_ne : x ≠ 0 := by
      intro hxeq
      exact (spectrum.zero_notMem ℝ hA.isUnit) (by simpa [hxeq] using hx)
    have hx_pos : 0 < x := lt_of_le_of_ne hx_nonneg (Ne.symm hx_ne)
    have hsqrt_ne : Real.sqrt x ≠ 0 :=
      ne_of_gt (Real.sqrt_pos.2 hx_pos)
    field_simp [hsqrt_ne]
  rw [← hmul, hcongr]
  simpa using
    (cfc_const (R := ℝ) (A := CStarMatrix ι ι ℂ)
      (p := IsSelfAdjoint) (1 : ℝ) A)

/-- The positive CFC inverse square root is a unit. -/
theorem cstarMatrixPositiveInvSqrt_isUnit
    {ι : Type*} [Fintype ι] [DecidableEq ι]
    {A : CStarMatrix ι ι ℂ} (hA : IsStrictlyPositive A) :
    IsUnit (cstarMatrixPositiveInvSqrt A) := by
  refine isUnit_iff_exists.mpr
    ⟨cstarMatrixPositiveSqrt A, ?_, ?_⟩
  · exact cstarMatrixPositiveInvSqrt_mul_sqrt hA
  · exact cstarMatrixPositiveSqrt_mul_invSqrt hA

/-- Squaring a nonnegative real square root after coercion to `ℂ` returns the
original scalar. -/
theorem complex_ofReal_sqrt_mul_self_of_nonneg {a : ℝ} (ha : 0 ≤ a) :
    ((Real.sqrt a : ℂ) * (Real.sqrt a : ℂ)) = (a : ℂ) := by
  exact_mod_cast Real.mul_self_sqrt ha

/-- The positive CFC square root is strictly positive when the input is. -/
theorem cstarMatrixPositiveSqrt_isStrictlyPositive
    {ι : Type*} [Fintype ι] [DecidableEq ι]
    {A : CStarMatrix ι ι ℂ} (hA : IsStrictlyPositive A) :
    IsStrictlyPositive (cstarMatrixPositiveSqrt A) := by
  have hnonneg : 0 ≤ cstarMatrixPositiveSqrt A := by
    dsimp [cstarMatrixPositiveSqrt]
    exact cfc_nonneg (R := ℝ) (A := CStarMatrix ι ι ℂ)
      (p := IsSelfAdjoint) (a := A) (f := Real.sqrt)
      (fun x _hx => Real.sqrt_nonneg x)
  have hunit : IsUnit (cstarMatrixPositiveSqrt A) := by
    refine isUnit_iff_exists.mpr
      ⟨cstarMatrixPositiveInvSqrt A, ?_, ?_⟩
    · exact cstarMatrixPositiveSqrt_mul_invSqrt hA
    · exact cstarMatrixPositiveInvSqrt_mul_sqrt hA
  exact hunit.isStrictlyPositive hnonneg

/-- Normalization identity \(A^{-1/2} A A^{-1/2}=I\) for the CFC inverse
square root. -/
theorem cstarMatrixPositiveInvSqrt_mul_self_mul
    {ι : Type*} [Fintype ι] [DecidableEq ι]
    {A : CStarMatrix ι ι ℂ} (hA : IsStrictlyPositive A) :
    cstarMatrixPositiveInvSqrt A * A * cstarMatrixPositiveInvSqrt A = 1 := by
  let R : CStarMatrix ι ι ℂ := cstarMatrixPositiveInvSqrt A
  let S : CStarMatrix ι ι ℂ := cstarMatrixPositiveSqrt A
  have hRS : R * S = 1 := by
    dsimp [R, S]
    exact cstarMatrixPositiveInvSqrt_mul_sqrt hA
  have hSR : S * R = 1 := by
    dsimp [R, S]
    exact cstarMatrixPositiveSqrt_mul_invSqrt hA
  have hAeq : A = S * S := by
    dsimp [S]
    exact (cstarMatrixPositiveSqrt_mul_self hA).symm
  change R * A * R = 1
  rw [hAeq]
  calc
    R * (S * S) * R = (R * S) * (S * R) := by
      exact
        (congrArg (fun T : CStarMatrix ι ι ℂ => T * R)
          (mul_assoc R S S).symm).trans
            (mul_assoc (R * S) S R)
    _ = 1 := by
      rw [hRS, hSR]
      exact mul_one (1 : CStarMatrix ι ι ℂ)

/-- The square of the positive CFC inverse square root is the inverse unit of
the original strictly positive matrix. -/
theorem cstarMatrixPositiveInvSqrt_mul_self_eq_unit_inv
    {ι : Type*} [Fintype ι] [DecidableEq ι]
    {A : CStarMatrix ι ι ℂ} (hA : IsStrictlyPositive A) :
    cstarMatrixPositiveInvSqrt A * cstarMatrixPositiveInvSqrt A =
      ((↑(hA.isUnit.unit⁻¹) : CStarMatrix ι ι ℂ)) := by
  let Q : CStarMatrix ι ι ℂ := cstarMatrixPositiveInvSqrt A
  let S : CStarMatrix ι ι ℂ := cstarMatrixPositiveSqrt A
  let u : (CStarMatrix ι ι ℂ)ˣ := hA.isUnit.unit
  have hQS : Q * S = 1 := by
    dsimp [Q, S]
    exact cstarMatrixPositiveInvSqrt_mul_sqrt hA
  have hAeq : A = S * S := by
    dsimp [S]
    exact (cstarMatrixPositiveSqrt_mul_self hA).symm
  have hu : (u : CStarMatrix ι ι ℂ) = A := by
    dsimp [u]
  have hright : (Q * Q) * (u : CStarMatrix ι ι ℂ) = 1 := by
    rw [hu, hAeq]
    calc
      (Q * Q) * (S * S) = Q * (Q * (S * S)) := by
        exact cstarMatrix_mul_assoc_rect Q Q (S * S)
      _ = Q * ((Q * S) * S) := by
        exact congrArg (fun T : CStarMatrix ι ι ℂ => Q * T)
          (cstarMatrix_mul_assoc_rect Q S S).symm
      _ = Q * (1 * S) := by
        rw [hQS]
      _ = Q * S := by
        exact congrArg (fun T : CStarMatrix ι ι ℂ => Q * T)
          (one_mul S)
      _ = 1 := hQS
  calc
    Q * Q = (Q * Q) * 1 := by
      exact (mul_one (Q * Q)).symm
    _ = (Q * Q) * ((u : CStarMatrix ι ι ℂ) *
        (↑u⁻¹ : CStarMatrix ι ι ℂ)) := by
        exact congrArg (fun T : CStarMatrix ι ι ℂ => (Q * Q) * T)
          (Units.mul_inv u).symm
    _ = ((Q * Q) * (u : CStarMatrix ι ι ℂ)) *
        (↑u⁻¹ : CStarMatrix ι ι ℂ) := by
        exact (cstarMatrix_mul_assoc_rect (Q * Q)
          (u : CStarMatrix ι ι ℂ) (↑u⁻¹ : CStarMatrix ι ι ℂ)).symm
    _ = 1 * (↑u⁻¹ : CStarMatrix ι ι ℂ) := by
        rw [hright]
    _ = (↑u⁻¹ : CStarMatrix ι ι ℂ) := by
        exact one_mul (↑u⁻¹ : CStarMatrix ι ι ℂ)

/-- The positive square root of a strictly positive C-star matrix commutes
with the inverse unit of that matrix. -/
theorem cstarMatrixPositiveSqrt_commute_unit_inv
    {ι : Type*} [Fintype ι] [DecidableEq ι]
    {A : CStarMatrix ι ι ℂ} (hA : IsStrictlyPositive A) :
    Commute (cstarMatrixPositiveSqrt A)
      ((↑(hA.isUnit.unit⁻¹) : CStarMatrix ι ι ℂ)) := by
  let u : (CStarMatrix ι ι ℂ)ˣ := hA.isUnit.unit
  have hu : (u : CStarMatrix ι ι ℂ) = A := by
    dsimp [u]
  have hcomm : Commute A ((↑u⁻¹ : CStarMatrix ι ι ℂ)) := by
    calc
      A * (↑u⁻¹ : CStarMatrix ι ι ℂ) =
          (u : CStarMatrix ι ι ℂ) * (↑u⁻¹ : CStarMatrix ι ι ℂ) := by
            rw [← hu]
      _ = 1 := Units.mul_inv u
      _ = (↑u⁻¹ : CStarMatrix ι ι ℂ) * (u : CStarMatrix ι ι ℂ) := by
            exact (Units.inv_mul u).symm
      _ = (↑u⁻¹ : CStarMatrix ι ι ℂ) * A := by
            rw [hu]
  have htarget : Commute (cfc Real.sqrt A)
      ((↑u⁻¹ : CStarMatrix ι ι ℂ)) :=
    hcomm.cfc_real Real.sqrt
  simpa [cstarMatrixPositiveSqrt] using htarget

/-- Congruence by the positive inverse square root preserves strict
positivity. -/
theorem cstarMatrixPositiveInvSqrt_conj_isStrictlyPositive
    {ι : Type*} [Fintype ι] [DecidableEq ι]
    {X A : CStarMatrix ι ι ℂ}
    (hX : IsStrictlyPositive X) (hA : IsStrictlyPositive A) :
    IsStrictlyPositive
      (cstarMatrixPositiveInvSqrt A * X * cstarMatrixPositiveInvSqrt A) := by
  let R : CStarMatrix ι ι ℂ := cstarMatrixPositiveInvSqrt A
  have hRunit : IsUnit R := by
    dsimp [R]
    exact cstarMatrixPositiveInvSqrt_isUnit hA
  have hRstar : star R = R := by
    exact isSelfAdjoint_iff.mp
      (by
        dsimp [R]
        exact cstarMatrixPositiveInvSqrt_isSelfAdjoint A)
  have hRstar' :
      star (cstarMatrixPositiveInvSqrt A) =
        cstarMatrixPositiveInvSqrt A := by
    simpa [R] using hRstar
  have hraw : IsStrictlyPositive (R * X * star R) :=
    (hRunit.isStrictlyPositive_star_right_conjugate_iff).mpr hX
  have htarget :
      R * X * star R =
        cstarMatrixPositiveInvSqrt A * X * cstarMatrixPositiveInvSqrt A := by
    dsimp [R]
    rw [hRstar']
  simpa [htarget] using hraw

/-!
### Algebraic normalizers for the Effros perspective

The finite perspective proof uses
\[
  V_A=\sqrt a\, A^{1/2}(aA+bB)^{-1/2}, \qquad
  V_B=\sqrt b\, B^{1/2}(aA+bB)^{-1/2}
\]
so that \(V_A^*V_A+V_B^*V_B=I\).  The lemmas below close this
normalization step in the local C-star matrix vocabulary.  They are direct
dependencies for the source-faithful Effros route; they still do not prove the
superoperator trace representation of Umegaki relative entropy.
-/

/-- Finite C-star matrix perspective \(A^{1/2} f(A^{-1/2}XA^{-1/2}) A^{1/2}\). -/
noncomputable def cstarMatrixPerspective
    {ι : Type*} [Fintype ι] [DecidableEq ι]
    (f : ℝ → ℝ) (X A : CStarMatrix ι ι ℂ) : CStarMatrix ι ι ℂ :=
  cstarMatrixPositiveSqrt A *
    cfc (p := IsSelfAdjoint) f
      (cstarMatrixPositiveInvSqrt A * X * cstarMatrixPositiveInvSqrt A) *
    cstarMatrixPositiveSqrt A

/-- The perspective proof's normalized block weight
\(\sqrt a\,A^{1/2}C^{-1/2}\). -/
noncomputable def cstarMatrixPerspectiveWeight
    {ι : Type*} [Fintype ι] [DecidableEq ι]
    (a : ℝ) (A C : CStarMatrix ι ι ℂ) : CStarMatrix ι ι ℂ :=
  (Real.sqrt a : ℂ) •
    (cstarMatrixPositiveSqrt A * cstarMatrixPositiveInvSqrt C)

/-- The square of an Effros perspective block weight is the corresponding
normalized congruence. -/
theorem cstarMatrixPerspectiveWeight_star_mul_self
    {ι : Type*} [Fintype ι] [DecidableEq ι]
    {a : ℝ} (ha : 0 ≤ a)
    {A C : CStarMatrix ι ι ℂ}
    (hA : IsStrictlyPositive A) :
    star (cstarMatrixPerspectiveWeight a A C) *
        cstarMatrixPerspectiveWeight a A C =
      a • (cstarMatrixPositiveInvSqrt C * A *
        cstarMatrixPositiveInvSqrt C) := by
  let S : CStarMatrix ι ι ℂ := cstarMatrixPositiveSqrt A
  let R : CStarMatrix ι ι ℂ := cstarMatrixPositiveInvSqrt C
  have hSstar : star S = S := by
    dsimp [S]
    exact isSelfAdjoint_iff.mp (cstarMatrixPositiveSqrt_isSelfAdjoint A)
  have hRstar : star R = R := by
    dsimp [R]
    exact isSelfAdjoint_iff.mp (cstarMatrixPositiveInvSqrt_isSelfAdjoint C)
  have hSS : S * S = A := by
    dsimp [S]
    exact cstarMatrixPositiveSqrt_mul_self hA
  have hsqrtre : star (Real.sqrt a : ℂ) = (Real.sqrt a : ℂ) := by
    simp
  have hsqrt_sq : (Real.sqrt a : ℂ) * (Real.sqrt a : ℂ) = (a : ℂ) :=
    complex_ofReal_sqrt_mul_self_of_nonneg ha
  have hstarSR : star (S * R) = R * S := by
    ext i j
    have hSentry : ∀ p q : ι, star (S q p) = S p q := by
      intro p q
      exact congrArg (fun M : CStarMatrix ι ι ℂ => M p q) hSstar
    have hRentry : ∀ p q : ι, star (R q p) = R p q := by
      intro p q
      exact congrArg (fun M : CStarMatrix ι ι ℂ => M p q) hRstar
    simp [CStarMatrix.mul_apply, CStarMatrix.star_apply, hSentry, hRentry]
    apply Finset.sum_congr rfl
    intro x _
    rw [mul_comm]
  dsimp [cstarMatrixPerspectiveWeight, S, R] at hSstar hRstar hSS ⊢
  calc
    star ((Real.sqrt a : ℂ) • (S * R)) *
        ((Real.sqrt a : ℂ) • (S * R)) =
      ((Real.sqrt a : ℂ) * (Real.sqrt a : ℂ)) •
        ((R * S) * (S * R)) := by
        rw [star_smul, hstarSR, hsqrtre]
        rw [cstarMatrix_smul_mul_rect, cstarMatrix_mul_smul_rect, smul_smul]
    _ = (a : ℂ) • (R * A * R) := by
        rw [hsqrt_sq]
        congr 1
        calc
          (R * S) * (S * R) = R * (S * S) * R := by
            rw [cstarMatrix_mul_assoc_rect R S (S * R)]
            rw [← cstarMatrix_mul_assoc_rect S S R]
            rw [← cstarMatrix_mul_assoc_rect R (S * S) R]
          _ = R * A * R := by rw [hSS]
    _ = a • (R * A * R) := rfl

/-- The two Effros perspective block weights form an isometry when
`C = a • A + b • B` and `a+b=1`. -/
theorem cstarMatrixPerspectiveWeights_star_mul_self_add
    {ι : Type*} [Fintype ι] [DecidableEq ι]
    {a b : ℝ} (ha : 0 ≤ a) (hb : 0 ≤ b) (hab : a + b = 1)
    {A B : CStarMatrix ι ι ℂ}
    (hA : IsStrictlyPositive A) (hB : IsStrictlyPositive B) :
    star (cstarMatrixPerspectiveWeight a A (a • A + b • B)) *
        cstarMatrixPerspectiveWeight a A (a • A + b • B) +
      star (cstarMatrixPerspectiveWeight b B (a • A + b • B)) *
        cstarMatrixPerspectiveWeight b B (a • A + b • B) =
      1 := by
  let C : CStarMatrix ι ι ℂ := a • A + b • B
  let R : CStarMatrix ι ι ℂ := cstarMatrixPositiveInvSqrt C
  have hC : IsStrictlyPositive C :=
    strictPositiveCStarMatrixCone_convex
      (by simpa [strictPositiveCStarMatrixCone] using hA)
      (by simpa [strictPositiveCStarMatrixCone] using hB)
      ha hb hab
  have hlin :
      R * C * R =
        a • (R * A * R) + b • (R * B * R) := by
    dsimp [C]
    change R * (((a : ℂ) • A + (b : ℂ) • B)) * R =
      (a : ℂ) • (R * A * R) + (b : ℂ) • (R * B * R)
    calc
      R * (((a : ℂ) • A + (b : ℂ) • B)) * R =
          (R * ((a : ℂ) • A) + R * ((b : ℂ) • B)) * R := by
            rw [cstarMatrix_mul_add_rect]
      _ = R * ((a : ℂ) • A) * R + R * ((b : ℂ) • B) * R := by
            rw [cstarMatrix_add_mul_rect]
      _ = (a : ℂ) • (R * A * R) + (b : ℂ) • (R * B * R) := by
            rw [cstarMatrix_mul_smul_rect, cstarMatrix_mul_smul_rect,
              cstarMatrix_smul_mul_rect, cstarMatrix_smul_mul_rect]
  rw [cstarMatrixPerspectiveWeight_star_mul_self (a := a) ha hA,
    cstarMatrixPerspectiveWeight_star_mul_self (a := b) hb hB]
  rw [← hlin]
  dsimp [R, C]
  exact cstarMatrixPositiveInvSqrt_mul_self_mul hC

/-- Compressing a normalized argument by one Effros perspective block weight
returns the corresponding normalized weighted numerator. -/
theorem cstarMatrixPerspectiveWeight_compress_normalized
    {ι : Type*} [Fintype ι] [DecidableEq ι]
    {a : ℝ} (ha : 0 ≤ a)
    {X A C : CStarMatrix ι ι ℂ}
    (hA : IsStrictlyPositive A) :
    star (cstarMatrixPerspectiveWeight a A C) *
        (cstarMatrixPositiveInvSqrt A * X *
          cstarMatrixPositiveInvSqrt A) *
        cstarMatrixPerspectiveWeight a A C =
      a • (cstarMatrixPositiveInvSqrt C * X *
        cstarMatrixPositiveInvSqrt C) := by
  let S : CStarMatrix ι ι ℂ := cstarMatrixPositiveSqrt A
  let R : CStarMatrix ι ι ℂ := cstarMatrixPositiveInvSqrt A
  let Q : CStarMatrix ι ι ℂ := cstarMatrixPositiveInvSqrt C
  have hSstar : star S = S := by
    dsimp [S]
    exact isSelfAdjoint_iff.mp (cstarMatrixPositiveSqrt_isSelfAdjoint A)
  have hQstar : star Q = Q := by
    dsimp [Q]
    exact isSelfAdjoint_iff.mp (cstarMatrixPositiveInvSqrt_isSelfAdjoint C)
  have hstarSQ : star (S * Q) = Q * S := by
    ext i j
    have hSentry : ∀ p q : ι, star (S q p) = S p q := by
      intro p q
      exact congrArg (fun M : CStarMatrix ι ι ℂ => M p q) hSstar
    have hQentry : ∀ p q : ι, star (Q q p) = Q p q := by
      intro p q
      exact congrArg (fun M : CStarMatrix ι ι ℂ => M p q) hQstar
    simp [CStarMatrix.mul_apply, CStarMatrix.star_apply, hSentry, hQentry]
    apply Finset.sum_congr rfl
    intro x _
    rw [mul_comm]
  have hSR : S * R = 1 := by
    dsimp [S, R]
    exact cstarMatrixPositiveSqrt_mul_invSqrt hA
  have hRS : R * S = 1 := by
    dsimp [S, R]
    exact cstarMatrixPositiveInvSqrt_mul_sqrt hA
  have hsqrtre : star (Real.sqrt a : ℂ) = (Real.sqrt a : ℂ) := by
    simp
  have hsqrt_sq : (Real.sqrt a : ℂ) * (Real.sqrt a : ℂ) = (a : ℂ) :=
    complex_ofReal_sqrt_mul_self_of_nonneg ha
  have halg :
      ((Q * S) * (R * X * R)) * (S * Q) = Q * X * Q := by
    calc
      ((Q * S) * (R * X * R)) * (S * Q) =
          (Q * S) * ((R * X * R) * (S * Q)) := by
            rw [cstarMatrix_mul_assoc_rect]
      _ = (Q * S) * ((R * X) * (R * (S * Q))) := by
            rw [cstarMatrix_mul_assoc_rect (R * X) R (S * Q)]
      _ = (Q * S) * ((R * X) * ((R * S) * Q)) := by
            rw [← cstarMatrix_mul_assoc_rect R S Q]
      _ = (Q * S) * ((R * X) * (1 * Q)) := by
            rw [hRS]
      _ = (Q * S) * ((R * X) * Q) := by
            rw [cstarMatrix_one_mul_rect Q]
      _ = ((Q * S) * (R * X)) * Q := by
            rw [← cstarMatrix_mul_assoc_rect (Q * S) (R * X) Q]
      _ = (Q * (S * (R * X))) * Q := by
            rw [cstarMatrix_mul_assoc_rect Q S (R * X)]
      _ = (Q * ((S * R) * X)) * Q := by
            rw [← cstarMatrix_mul_assoc_rect S R X]
      _ = (Q * (1 * X)) * Q := by
            rw [hSR]
      _ = (Q * X) * Q := by
            rw [cstarMatrix_one_mul_rect X]
      _ = Q * X * Q := rfl
  dsimp [cstarMatrixPerspectiveWeight, S, R, Q] at hstarSQ hSR hRS halg ⊢
  calc
    star ((Real.sqrt a : ℂ) • (S * Q)) *
        (R * X * R) *
        ((Real.sqrt a : ℂ) • (S * Q)) =
      ((Real.sqrt a : ℂ) • ((Q * S) * (R * X * R))) *
        ((Real.sqrt a : ℂ) • (S * Q)) := by
        rw [star_smul, hstarSQ, hsqrtre]
        rw [cstarMatrix_smul_mul_rect]
    _ = (Real.sqrt a : ℂ) •
        (((Q * S) * (R * X * R)) *
          ((Real.sqrt a : ℂ) • (S * Q))) := by
        rw [cstarMatrix_smul_mul_rect]
    _ = (Real.sqrt a : ℂ) •
        ((Real.sqrt a : ℂ) •
          (((Q * S) * (R * X * R)) * (S * Q))) := by
        rw [cstarMatrix_mul_smul_rect]
    _ = ((Real.sqrt a : ℂ) * (Real.sqrt a : ℂ)) •
        (((Q * S) * (R * X * R)) * (S * Q)) := by
        rw [smul_smul]
    _ = (a : ℂ) • (Q * X * Q) := by
        rw [hsqrt_sq, halg]
    _ = a • (Q * X * Q) := rfl

/-- Right normalization of an Effros perspective block weight:
\(\sqrt a\,A^{1/2}C^{-1/2}C^{1/2}=\sqrt a\,A^{1/2}\). -/
theorem cstarMatrixPerspectiveWeight_mul_positiveSqrt
    {ι : Type*} [Fintype ι] [DecidableEq ι]
    {a : ℝ} {A C : CStarMatrix ι ι ℂ}
    (hC : IsStrictlyPositive C) :
    cstarMatrixPerspectiveWeight a A C * cstarMatrixPositiveSqrt C =
      (Real.sqrt a : ℂ) • cstarMatrixPositiveSqrt A := by
  let S : CStarMatrix ι ι ℂ := cstarMatrixPositiveSqrt A
  let Q : CStarMatrix ι ι ℂ := cstarMatrixPositiveInvSqrt C
  let T : CStarMatrix ι ι ℂ := cstarMatrixPositiveSqrt C
  have hQT : Q * T = 1 := by
    dsimp [Q, T]
    exact cstarMatrixPositiveInvSqrt_mul_sqrt hC
  dsimp [cstarMatrixPerspectiveWeight, S, Q, T] at hQT ⊢
  calc
    ((Real.sqrt a : ℂ) • (S * Q)) * T =
        (Real.sqrt a : ℂ) • ((S * Q) * T) := by
          rw [cstarMatrix_smul_mul_rect]
    _ = (Real.sqrt a : ℂ) • (S * (Q * T)) := by
          rw [cstarMatrix_mul_assoc_rect]
    _ = (Real.sqrt a : ℂ) • (S * 1) := by
          rw [hQT]
    _ = (Real.sqrt a : ℂ) • S := by
          rw [cstarMatrix_mul_one_rect]

/-- Left normalization of an Effros perspective block weight:
\(C^{1/2}(\sqrt a\,A^{1/2}C^{-1/2})^*
  =\sqrt a\,A^{1/2}\). -/
theorem cstarMatrixPositiveSqrt_mul_perspectiveWeight_star
    {ι : Type*} [Fintype ι] [DecidableEq ι]
    {a : ℝ} {A C : CStarMatrix ι ι ℂ}
    (hC : IsStrictlyPositive C) :
    cstarMatrixPositiveSqrt C * star (cstarMatrixPerspectiveWeight a A C) =
      (Real.sqrt a : ℂ) • cstarMatrixPositiveSqrt A := by
  let S : CStarMatrix ι ι ℂ := cstarMatrixPositiveSqrt A
  let Q : CStarMatrix ι ι ℂ := cstarMatrixPositiveInvSqrt C
  let T : CStarMatrix ι ι ℂ := cstarMatrixPositiveSqrt C
  have hSstar : star S = S := by
    dsimp [S]
    exact isSelfAdjoint_iff.mp (cstarMatrixPositiveSqrt_isSelfAdjoint A)
  have hQstar : star Q = Q := by
    dsimp [Q]
    exact isSelfAdjoint_iff.mp (cstarMatrixPositiveInvSqrt_isSelfAdjoint C)
  have hTQ : T * Q = 1 := by
    dsimp [T, Q]
    exact cstarMatrixPositiveSqrt_mul_invSqrt hC
  have hstarSQ : star (S * Q) = Q * S := by
    ext i j
    have hSentry : ∀ p q : ι, star (S q p) = S p q := by
      intro p q
      exact congrArg (fun M : CStarMatrix ι ι ℂ => M p q) hSstar
    have hQentry : ∀ p q : ι, star (Q q p) = Q p q := by
      intro p q
      exact congrArg (fun M : CStarMatrix ι ι ℂ => M p q) hQstar
    simp [CStarMatrix.mul_apply, CStarMatrix.star_apply, hSentry, hQentry]
    apply Finset.sum_congr rfl
    intro x _
    rw [mul_comm]
  have hsqrtre : star (Real.sqrt a : ℂ) = (Real.sqrt a : ℂ) := by
    simp
  dsimp [cstarMatrixPerspectiveWeight, S, Q, T] at hstarSQ hTQ ⊢
  calc
    T * star ((Real.sqrt a : ℂ) • (S * Q)) =
        T * ((Real.sqrt a : ℂ) • (Q * S)) := by
          rw [star_smul, hstarSQ, hsqrtre]
    _ = (Real.sqrt a : ℂ) • (T * (Q * S)) := by
          rw [cstarMatrix_mul_smul_rect]
    _ = (Real.sqrt a : ℂ) • ((T * Q) * S) := by
          rw [← cstarMatrix_mul_assoc_rect]
    _ = (Real.sqrt a : ℂ) • (1 * S) := by
          rw [hTQ]
    _ = (Real.sqrt a : ℂ) • S := by
          rw [cstarMatrix_one_mul_rect]

/-- Compressing a weighted Jensen output by the mixed square root recovers the
corresponding weighted perspective value. -/
theorem cstarMatrixPerspectiveWeight_value_uncompress
    {ι : Type*} [Fintype ι] [DecidableEq ι]
    {a : ℝ} (ha : 0 ≤ a)
    {F A C : CStarMatrix ι ι ℂ}
    (hC : IsStrictlyPositive C) :
    cstarMatrixPositiveSqrt C *
        (star (cstarMatrixPerspectiveWeight a A C) * F *
          cstarMatrixPerspectiveWeight a A C) *
        cstarMatrixPositiveSqrt C =
      a • (cstarMatrixPositiveSqrt A * F *
        cstarMatrixPositiveSqrt A) := by
  let S : CStarMatrix ι ι ℂ := cstarMatrixPositiveSqrt A
  let T : CStarMatrix ι ι ℂ := cstarMatrixPositiveSqrt C
  let W : CStarMatrix ι ι ℂ := cstarMatrixPerspectiveWeight a A C
  have hTW : T * star W = (Real.sqrt a : ℂ) • S := by
    dsimp [T, W, S]
    exact cstarMatrixPositiveSqrt_mul_perspectiveWeight_star (a := a)
      (A := A) hC
  have hWT : W * T = (Real.sqrt a : ℂ) • S := by
    dsimp [T, W, S]
    exact cstarMatrixPerspectiveWeight_mul_positiveSqrt (a := a)
      (A := A) hC
  have hsqrt_sq : (Real.sqrt a : ℂ) * (Real.sqrt a : ℂ) = (a : ℂ) :=
    complex_ofReal_sqrt_mul_self_of_nonneg ha
  dsimp [T, W, S] at hTW hWT ⊢
  calc
    cstarMatrixPositiveSqrt C *
        (star (cstarMatrixPerspectiveWeight a A C) * F *
          cstarMatrixPerspectiveWeight a A C) *
        cstarMatrixPositiveSqrt C =
      (T * star W) * F * (W * T) := by
        change T * (star W * F * W) * T =
          (T * star W) * F * (W * T)
        rw [← cstarMatrix_mul_assoc_rect T (star W * F) W]
        rw [← cstarMatrix_mul_assoc_rect T (star W) F]
        rw [cstarMatrix_mul_assoc_rect ((T * star W) * F) W T]
    _ = ((Real.sqrt a : ℂ) • S) * F *
        ((Real.sqrt a : ℂ) • S) := by
        rw [hTW, hWT]
    _ = ((Real.sqrt a : ℂ) * (Real.sqrt a : ℂ)) • (S * F * S) := by
        rw [cstarMatrix_smul_mul_rect]
        rw [cstarMatrix_smul_mul_rect]
        rw [cstarMatrix_mul_smul_rect]
        rw [smul_smul]
    _ = (a : ℂ) • (S * F * S) := by rw [hsqrt_sq]
    _ = a • (S * F * S) := rfl

/-- Joint convexity of the finite C-star matrix perspective for the normalized
entropy kernel, obtained from the concrete Hansen--Pedersen Jensen theorem.

This is the ordinary finite perspective layer of the Effros route.  It is a
real dependency for the source-faithful superoperator proof of matrix
relative-entropy joint convexity, but it is not by itself the trace
representation of Umegaki relative entropy. -/
theorem cstarMatrixEntropyKernelPerspective_jointConvex
    {ι : Type*} [Fintype ι] [DecidableEq ι]
    {a b : ℝ} (ha : 0 ≤ a) (hb : 0 ≤ b) (hab : a + b = 1)
    {X Y A B : CStarMatrix ι ι ℂ}
    (hX : IsStrictlyPositive X) (hY : IsStrictlyPositive Y)
    (hA : IsStrictlyPositive A) (hB : IsStrictlyPositive B) :
    cstarMatrixPerspective realEntropyKernel
        (a • X + b • Y) (a • A + b • B) ≤
      a • cstarMatrixPerspective realEntropyKernel X A +
        b • cstarMatrixPerspective realEntropyKernel Y B := by
  let C : CStarMatrix ι ι ℂ := a • A + b • B
  let Z : CStarMatrix ι ι ℂ := a • X + b • Y
  let QA : CStarMatrix ι ι ℂ := cstarMatrixPositiveInvSqrt A
  let QB : CStarMatrix ι ι ℂ := cstarMatrixPositiveInvSqrt B
  let QC : CStarMatrix ι ι ℂ := cstarMatrixPositiveInvSqrt C
  let SC : CStarMatrix ι ι ℂ := cstarMatrixPositiveSqrt C
  let WA : CStarMatrix ι ι ℂ := cstarMatrixPerspectiveWeight a A C
  let WB : CStarMatrix ι ι ℂ := cstarMatrixPerspectiveWeight b B C
  let TA : CStarMatrix ι ι ℂ := QA * X * QA
  let TB : CStarMatrix ι ι ℂ := QB * Y * QB
  have hC : IsStrictlyPositive C :=
    strictPositiveCStarMatrixCone_convex
      (by simpa [strictPositiveCStarMatrixCone] using hA)
      (by simpa [strictPositiveCStarMatrixCone] using hB)
      ha hb hab
  have hZ : IsStrictlyPositive Z :=
    strictPositiveCStarMatrixCone_convex
      (by simpa [strictPositiveCStarMatrixCone] using hX)
      (by simpa [strictPositiveCStarMatrixCone] using hY)
      ha hb hab
  have hTA : IsStrictlyPositive TA := by
    dsimp [TA, QA]
    exact cstarMatrixPositiveInvSqrt_conj_isStrictlyPositive hX hA
  have hTB : IsStrictlyPositive TB := by
    dsimp [TB, QB]
    exact cstarMatrixPositiveInvSqrt_conj_isStrictlyPositive hY hB
  have hWsum : star WA * WA + star WB * WB = 1 := by
    dsimp [WA, WB, C]
    exact cstarMatrixPerspectiveWeights_star_mul_self_add
      ha hb hab hA hB
  have hJ :=
    cstarMatrixEntropyKernelHansenPedersenJensenTarget_of_unit_interval_kernel
      WA WB TA TB hTA hTB hWsum
  have harg :
      star WA * TA * WA + star WB * TB * WB =
        QC * Z * QC := by
    have hlin :
        QC * Z * QC =
          a • (QC * X * QC) + b • (QC * Y * QC) := by
      dsimp [Z]
      change QC * (((a : ℂ) • X + (b : ℂ) • Y)) * QC =
        (a : ℂ) • (QC * X * QC) + (b : ℂ) • (QC * Y * QC)
      calc
        QC * (((a : ℂ) • X + (b : ℂ) • Y)) * QC =
            (QC * ((a : ℂ) • X) + QC * ((b : ℂ) • Y)) * QC := by
              rw [cstarMatrix_mul_add_rect]
        _ = QC * ((a : ℂ) • X) * QC + QC * ((b : ℂ) • Y) * QC := by
              rw [cstarMatrix_add_mul_rect]
        _ = (a : ℂ) • (QC * X * QC) + (b : ℂ) • (QC * Y * QC) := by
              rw [cstarMatrix_mul_smul_rect, cstarMatrix_mul_smul_rect,
                cstarMatrix_smul_mul_rect, cstarMatrix_smul_mul_rect]
    rw [cstarMatrixPerspectiveWeight_compress_normalized
        (a := a) ha (X := X) hA,
      cstarMatrixPerspectiveWeight_compress_normalized
        (a := b) hb (X := Y) hB]
    exact hlin.symm
  rw [harg] at hJ
  have hcomp := cstarMatrix_compression_mono hJ SC
  have hSCstar : CStarMatrix.conjTranspose SC = SC := by
    dsimp [SC]
    rw [← CStarMatrix.star_eq_conjTranspose]
    exact isSelfAdjoint_iff.mp (cstarMatrixPositiveSqrt_isSelfAdjoint C)
  have hleft :
      CStarMatrix.conjTranspose SC *
          cfc (p := IsSelfAdjoint) realEntropyKernel (QC * Z * QC) *
          SC =
        cstarMatrixPerspective realEntropyKernel Z C := by
    dsimp [cstarMatrixPerspective, SC, QC, Z, C]
    rw [hSCstar]
  have hright :
      CStarMatrix.conjTranspose SC *
          (star WA * cfc (p := IsSelfAdjoint) realEntropyKernel TA * WA +
            star WB * cfc (p := IsSelfAdjoint) realEntropyKernel TB * WB) *
          SC =
        a • cstarMatrixPerspective realEntropyKernel X A +
          b • cstarMatrixPerspective realEntropyKernel Y B := by
    rw [cstarMatrix_compression_add SC
      (star WA * cfc (p := IsSelfAdjoint) realEntropyKernel TA * WA)
      (star WB * cfc (p := IsSelfAdjoint) realEntropyKernel TB * WB)]
    rw [hSCstar]
    rw [cstarMatrixPerspectiveWeight_value_uncompress
        (a := a) ha (F := cfc (p := IsSelfAdjoint) realEntropyKernel TA)
        (A := A) (C := C) hC,
      cstarMatrixPerspectiveWeight_value_uncompress
        (a := b) hb (F := cfc (p := IsSelfAdjoint) realEntropyKernel TB)
        (A := B) (C := C) hC]
    dsimp [cstarMatrixPerspective, TA, TB, QA, QB]
  dsimp [cstarMatrixPerspective, Z, C] at hleft
  rw [hleft, hright] at hcomp
  exact hcomp

/-- Conditional adapter retained for the generic Hansen-Pedersen split:
if a separate transfer theorem is supplied, the concrete source target follows. -/
theorem cstarMatrixXLogXHansenPedersenJensenTarget_of_transfer
    {ι : Type*} [Fintype ι] [DecidableEq ι]
    (htransfer : cstarMatrixXLogXHansenPedersenTransferTarget (ι := ι)) :
    cstarMatrixXLogXHansenPedersenJensenTarget (ι := ι) := by
  exact cstarMatrixXLogXHansenPedersenJensenTarget_of_positiveOperatorConvex_of_transfer
    cstarMatrixXLogXPositiveOperatorConvexTarget_of_unit_interval_kernel htransfer

/-- Source-faithful all-finite-size transfer bridge.  The standard
Hansen-Pedersen proof uses ordinary operator convexity in a larger finite
matrix algebra; after the direct kernel route supplies that all-size
operator-convexity hypothesis, the assembled two-point target is blocked only
by the all-finite-size transfer theorem. -/
theorem cstarMatrixXLogXHansenPedersenJensenTarget_of_allFiniteTransfer
    {ι : Type u} [Fintype ι] [DecidableEq ι]
    (htransfer : cstarMatrixXLogXHansenPedersenTransferAllFiniteTarget.{u}) :
    cstarMatrixXLogXHansenPedersenJensenTarget (ι := ι) := by
  intro A B T1 T2 hT1 hT2 hAB
  exact htransfer
    cstarMatrixXLogXPositiveOperatorConvexAllFiniteTarget_of_unit_interval_kernel
    A B T1 T2 hT1 hT2 hAB

/-!
## Kronecker lift substrate for the matrix-perspective route

Tropp's relative-entropy proof route also uses the commuting pair
`A ⊗ I` and `I ⊗ H` before applying a matrix perspective.  The following
lemmas expose the finite-dimensional Kronecker algebra and positivity facts
locally, reusing mathlib's Kronecker product rather than rebuilding it.
-/

/-- The vectorized identity matrix, indexed by matrix coordinates. -/
noncomputable def matrixVecId
    {ι : Type*} [DecidableEq ι] : ι × ι → ℂ :=
  fun p => if p.1 = p.2 then 1 else 0

/-- Vectorize a finite matrix by product-indexing its entries. -/
noncomputable def matrixVec
    {ι : Type*} (M : Matrix ι ι ℂ) : ι × ι → ℂ :=
  fun p => M p.1 p.2

/-- Complex quadratic form \(v^* M v\) for finite complex matrices. -/
noncomputable def matrixComplexQuadraticForm
    {ν : Type*} [Fintype ν] (M : Matrix ν ν ℂ) (v : ν → ℂ) : ℂ :=
  ∑ i, star (v i) * Matrix.mulVec M v i

/-- For a fixed vector, the finite complex quadratic form is continuous in the
matrix argument.  This is the analytic continuity hook needed before a later
polynomial-to-CFC/log transfer. -/
theorem continuous_matrixComplexQuadraticForm
    {ν : Type*} [Fintype ν] (v : ν → ℂ) :
    Continuous fun M : Matrix ν ν ℂ => matrixComplexQuadraticForm M v := by
  classical
  simp [matrixComplexQuadraticForm, Matrix.mulVec, dotProduct]
  fun_prop

/-- A positive semidefinite finite complex matrix has nonnegative real
quadratic form in the local `matrixComplexQuadraticForm` notation. -/
theorem matrixComplexQuadraticForm_re_nonneg_of_posSemidef
    {ν : Type*} [Fintype ν]
    {M : Matrix ν ν ℂ} (hM : Matrix.PosSemidef M) (v : ν → ℂ) :
    0 ≤ (matrixComplexQuadraticForm M v).re := by
  simpa [matrixComplexQuadraticForm, dotProduct] using
    hM.re_dotProduct_nonneg v

/-- Loewner positivity of `N - M` implies monotonicity of the real quadratic
form.  This is the scalar extraction step needed after applying a product-index
perspective inequality. -/
theorem matrixComplexQuadraticForm_re_mono_of_posSemidef_sub
    {ν : Type*} [Fintype ν]
    {M N : Matrix ν ν ℂ}
    (hMN : Matrix.PosSemidef (N - M)) (v : ν → ℂ) :
    (matrixComplexQuadraticForm M v).re ≤
      (matrixComplexQuadraticForm N v).re := by
  have hnonneg :=
    matrixComplexQuadraticForm_re_nonneg_of_posSemidef hMN v
  have hsub :
      matrixComplexQuadraticForm (N - M) v =
        matrixComplexQuadraticForm N v - matrixComplexQuadraticForm M v := by
    simp [matrixComplexQuadraticForm, Matrix.mulVec, dotProduct,
      Finset.mul_sum, Finset.sum_add_distrib, sub_eq_add_neg, add_mul,
      mul_add]
  rw [hsub] at hnonneg
  simpa using hnonneg

/-- C-star Loewner order implies monotonicity of the real quadratic form after
forgetting to the underlying finite matrix. -/
theorem matrixComplexQuadraticForm_re_mono_of_cstarMatrix_le
    {ν : Type*} [Fintype ν] [DecidableEq ν]
    {M N : CStarMatrix ν ν ℂ} (hMN : M ≤ N) (v : ν → ℂ) :
    (matrixComplexQuadraticForm
        (CStarMatrix.ofMatrix.symm M : Matrix ν ν ℂ) v).re ≤
      (matrixComplexQuadraticForm
        (CStarMatrix.ofMatrix.symm N : Matrix ν ν ℂ) v).re := by
  have hpsd :
      Matrix.PosSemidef
        (CStarMatrix.ofMatrix.symm (N - M) : Matrix ν ν ℂ) :=
    cstarMatrix_nonneg_to_matrix_posSemidef (sub_nonneg.mpr hMN)
  have hpsd' :
      Matrix.PosSemidef
        ((CStarMatrix.ofMatrix.symm N : Matrix ν ν ℂ) -
          (CStarMatrix.ofMatrix.symm M : Matrix ν ν ℂ)) := by
    simpa using hpsd
  exact matrixComplexQuadraticForm_re_mono_of_posSemidef_sub hpsd' v

/-- Summing a function over the diagonal of a finite product type. -/
theorem finset_sum_product_diagonal
    {ι : Type*} [Fintype ι] [DecidableEq ι]
    {α : Type*} [AddCommMonoid α] (F : ι → ι → α) :
    (∑ x : ι × ι, if x.1 = x.2 then F x.1 x.2 else 0) =
      ∑ i, F i i := by
  classical
  rw [Fintype.sum_prod_type]
  simp

/-- The Kronecker matrix \(A\otimes B^{\mathsf T}\) represents
\(M\mapsto AMB\) under the product-index vectorization. -/
theorem matrix_kronecker_transpose_mulVec_matrixVec
    {ι : Type*} [Fintype ι] [DecidableEq ι]
    (A B M : Matrix ι ι ℂ) :
    Matrix.mulVec (A ⊗ₖ B.transpose) (matrixVec M) =
      matrixVec (A * M * B) := by
  classical
  ext p
  simp [Matrix.mulVec, matrixVec, Matrix.mul_apply, Matrix.kroneckerMap_apply,
    Matrix.transpose_apply, dotProduct]
  rw [Fintype.sum_prod_type]
  calc
    (∑ x : ι, ∑ y : ι, A p.1 x * B y p.2 * M x y) =
        ∑ y : ι, ∑ x : ι, A p.1 x * B y p.2 * M x y := by
          rw [Finset.sum_comm]
    _ = ∑ y : ι, (∑ x : ι, A p.1 x * M x y) * B y p.2 := by
        apply Finset.sum_congr rfl
        intro y _
        rw [Finset.sum_mul]
        apply Finset.sum_congr rfl
        intro x _
        ring

/-- Powers of the Kronecker lift can be pushed to the two matrix factors,
with the right factor transposed in the vectorization convention. -/
theorem matrix_kronecker_transpose_pow
    {ι : Type*} [Fintype ι] [DecidableEq ι]
    (A B : Matrix ι ι ℂ) (n : ℕ) :
    (A ⊗ₖ B.transpose) ^ n = (A ^ n) ⊗ₖ (B ^ n).transpose := by
  classical
  induction n with
  | zero =>
      simp
  | succ n ih =>
      calc
        (A ⊗ₖ B.transpose) ^ (n + 1) =
            ((A ^ n) ⊗ₖ (B ^ n).transpose) * (A ⊗ₖ B.transpose) := by
              rw [pow_succ, ih]
        _ = (A ^ n * A) ⊗ₖ ((B ^ n).transpose * B.transpose) := by
              rw [← Matrix.mul_kronecker_mul]
        _ = (A ^ (n + 1)) ⊗ₖ (B ^ (n + 1)).transpose := by
              rw [pow_succ, pow_succ', Matrix.transpose_mul]

/-- Powers of the Kronecker left-right lift represent repeated left/right
multiplication under product-index vectorization.  This is the polynomial
substrate for the remaining superoperator functional-calculus step. -/
theorem matrix_kronecker_transpose_pow_mulVec_matrixVec
    {ι : Type*} [Fintype ι] [DecidableEq ι]
    (A B M : Matrix ι ι ℂ) (n : ℕ) :
    Matrix.mulVec ((A ⊗ₖ B.transpose) ^ n) (matrixVec M) =
      matrixVec (A ^ n * M * B ^ n) := by
  classical
  induction n with
  | zero =>
      ext p
      simp [matrixVec]
  | succ n ih =>
      calc
        Matrix.mulVec ((A ⊗ₖ B.transpose) ^ (n + 1)) (matrixVec M)
            = Matrix.mulVec ((A ⊗ₖ B.transpose) * (A ⊗ₖ B.transpose) ^ n)
                (matrixVec M) := by
                rw [pow_succ']
        _ = Matrix.mulVec (A ⊗ₖ B.transpose)
              (Matrix.mulVec ((A ⊗ₖ B.transpose) ^ n) (matrixVec M)) := by
                rw [Matrix.mulVec_mulVec]
        _ = Matrix.mulVec (A ⊗ₖ B.transpose)
              (matrixVec (A ^ n * M * B ^ n)) := by
                rw [ih]
        _ = matrixVec (A * (A ^ n * M * B ^ n) * B) := by
                rw [matrix_kronecker_transpose_mulVec_matrixVec]
        _ = matrixVec (A ^ (n + 1) * M * B ^ (n + 1)) := by
                congr 1
                rw [pow_succ', pow_succ]
                noncomm_ring

/-- The vectorized identity is the vectorization of the ordinary identity
matrix. -/
theorem matrixVec_one
    {ι : Type*} [Fintype ι] [DecidableEq ι] :
    matrixVec (1 : Matrix ι ι ℂ) = matrixVecId (ι := ι) := by
  classical
  ext p
  by_cases h : p.1 = p.2
  · rcases p with ⟨i, j⟩
    dsimp at h ⊢
    subst j
    simp [matrixVec, matrixVecId]
  · simp [matrixVec, matrixVecId, h]

/-- Pairing the vectorized identity with an ordinary vectorized matrix returns
the trace.  This is the Hilbert-Schmidt trace functional used by the
superoperator perspective route. -/
theorem matrixVecId_inner_matrixVec
    {ι : Type*} [Fintype ι] [DecidableEq ι] (M : Matrix ι ι ℂ) :
    (∑ x : ι × ι, star (matrixVecId x) * matrixVec M x) =
      Matrix.trace M := by
  classical
  simp [matrixVecId, matrixVec, Matrix.trace]
  simpa using (finset_sum_product_diagonal (F := fun i j => M i j))

/-- Transposing a finite complex self-adjoint matrix is self-adjoint in the
ordinary `conjTranspose` sense.  This is the right-factor domain side condition
for the Kronecker left-right lift `A ⊗ B.transpose`. -/
theorem matrix_transpose_conjTranspose_eq_self_of_isSelfAdjoint
    {ι : Type*} [Fintype ι] [DecidableEq ι]
    {B : Matrix ι ι ℂ} (hB : IsSelfAdjoint B) :
    B.transpose.conjTranspose = B.transpose := by
  classical
  have hBct : B.conjTranspose = B := by
    rw [← Matrix.star_eq_conjTranspose]
    exact hB.star_eq
  ext i j
  have hji := congrFun (congrFun hBct j) i
  simp [Matrix.conjTranspose, Matrix.transpose_apply] at hji ⊢
  exact hji

/-- The Kronecker left-right lift `A ⊗ B.transpose` is self-adjoint whenever
the two source matrices are self-adjoint.  This closes the CFC domain
side-condition for the polynomial-to-functional-calculus trace route. -/
theorem matrix_kronecker_transpose_isSelfAdjoint_of_isSelfAdjoint
    {ι : Type*} [Fintype ι] [DecidableEq ι]
    {A B : Matrix ι ι ℂ}
    (hA : IsSelfAdjoint A) (hB : IsSelfAdjoint B) :
    IsSelfAdjoint (A ⊗ₖ B.transpose) := by
  classical
  have hAct : A.conjTranspose = A := by
    rw [← Matrix.star_eq_conjTranspose]
    exact hA.star_eq
  have hBtct : B.transpose.conjTranspose = B.transpose :=
    matrix_transpose_conjTranspose_eq_self_of_isSelfAdjoint hB
  change star (A ⊗ₖ B.transpose) = A ⊗ₖ B.transpose
  rw [Matrix.star_eq_conjTranspose, Matrix.conjTranspose_kronecker, hAct,
    hBtct]

/-- Positive semidefiniteness is preserved by the Kronecker left-right lift
`A ⊗ B.transpose`. -/
theorem matrix_kronecker_transpose_posSemidef
    {ι : Type*} [Fintype ι] [DecidableEq ι]
    {A B : Matrix ι ι ℂ}
    (hA : Matrix.PosSemidef A) (hB : Matrix.PosSemidef B) :
    Matrix.PosSemidef (A ⊗ₖ B.transpose) :=
  hA.kronecker hB.transpose

/-- Positive definiteness is preserved by the Kronecker left-right lift
`A ⊗ B.transpose`. -/
theorem matrix_kronecker_transpose_posDef
    {ι : Type*} [Fintype ι] [DecidableEq ι]
    {A B : Matrix ι ι ℂ}
    (hA : Matrix.PosDef A) (hB : Matrix.PosDef B) :
    Matrix.PosDef (A ⊗ₖ B.transpose) :=
  hA.kronecker hB.transpose

/-- The finite left-right ratio shape `X ⊗ (A⁻¹).transpose` is positive
definite when both source matrices are positive definite.  This is the concrete
matrix-domain side condition for the later superoperator-log theorem. -/
theorem matrix_kronecker_inv_transpose_posDef
    {ι : Type*} [Fintype ι] [DecidableEq ι]
    {X A : Matrix ι ι ℂ}
    (hX : Matrix.PosDef X) (hA : Matrix.PosDef A) :
    Matrix.PosDef (X ⊗ₖ (A⁻¹).transpose) :=
  hX.kronecker hA.inv.transpose

/-- Finite-matrix continuous functional calculus on the self-adjoint domain,
with the matrix instances supplied explicitly.  This wrapper avoids repeating
the low-level instance arguments when using mathlib's matrix CFC API for
Kronecker superoperators. -/
noncomputable def matrixSelfAdjointCfc
    {ν : Type*} [Fintype ν] [DecidableEq ν]
    (f : ℝ → ℝ) (M : Matrix ν ν ℂ) : Matrix ν ν ℂ :=
  @cfc ℝ (Matrix ν ν ℂ) IsSelfAdjoint inferInstance inferInstance
    inferInstance inferInstance inferInstance inferInstance inferInstance
    Matrix.instStarRing inferInstance
    Matrix.IsHermitian.instContinuousFunctionalCalculus f M

/-- On finite complex matrices, self-adjoint CFC of a real polynomial agrees
with ordinary algebraic polynomial evaluation. -/
theorem matrixSelfAdjointCfc_polynomial
    {ν : Type*} [Fintype ν] [DecidableEq ν]
    (M : Matrix ν ν ℂ) (q : Polynomial ℝ) (hM : IsSelfAdjoint M) :
    matrixSelfAdjointCfc (fun x : ℝ => Polynomial.eval x q) M =
      Polynomial.aeval M q := by
  rw [matrixSelfAdjointCfc]
  exact @cfc_polynomial ℝ (Matrix ν ν ℂ) IsSelfAdjoint inferInstance
    inferInstance inferInstance inferInstance inferInstance inferInstance
    inferInstance Matrix.instStarRing inferInstance
    Matrix.IsHermitian.instContinuousFunctionalCalculus q M hM

/-- Real polynomials uniformly approximate `log` on every positive compact
interval.  This is the scalar Weierstrass input for the later matrix-CFC log
transfer. -/
theorem exists_realPolynomial_near_log_on_Icc
    (a b ε : ℝ) (ha : 0 < a) (hε : 0 < ε) :
    ∃ p : Polynomial ℝ,
      ∀ x ∈ Set.Icc a b, |Polynomial.eval x p - Real.log x| < ε := by
  exact exists_polynomial_near_of_continuousOn a b Real.log
    (Real.continuousOn_log.mono (by
      intro x hx
      exact ne_of_gt (lt_of_lt_of_le ha hx.1))) ε hε

/-- Real polynomials uniformly approximate `x log x` on every positive compact
interval. -/
theorem exists_realPolynomial_near_xlog_on_Icc
    (a b ε : ℝ) (_ha : 0 < a) (hε : 0 < ε) :
    ∃ p : Polynomial ℝ,
      ∀ x ∈ Set.Icc a b,
        |Polynomial.eval x p - x * Real.log x| < ε := by
  exact exists_polynomial_near_of_continuousOn a b
    (fun x : ℝ => x * Real.log x)
    (Real.continuous_mul_log.continuousOn) ε hε

/-- Real polynomials uniformly approximate the normalized entropy kernel
`x log x - (x - 1)` on every positive compact interval. -/
theorem exists_realPolynomial_near_realEntropyKernel_on_Icc
    (a b ε : ℝ) (_ha : 0 < a) (hε : 0 < ε) :
    ∃ p : Polynomial ℝ,
      ∀ x ∈ Set.Icc a b,
        |Polynomial.eval x p - realEntropyKernel x| < ε := by
  have hcont :
      ContinuousOn realEntropyKernel (Set.Icc a b) := by
    simpa [realEntropyKernel] using
      (Real.continuous_mul_log.sub
        (continuous_id.sub continuous_const)).continuousOn
  exact exists_polynomial_near_of_continuousOn a b realEntropyKernel hcont ε hε

/-- Positive definite finite complex matrices have strictly positive real
spectrum.  This is the domain bridge that keeps logarithmic and entropy-kernel
approximations on a positive compact interval. -/
theorem matrix_posDef_spectrum_real_pos
    {ι : Type*} [Fintype ι] [DecidableEq ι]
    {A : Matrix ι ι ℂ} (hA : Matrix.PosDef A) :
    ∀ x ∈ spectrum ℝ A, 0 < x := by
  intro x hx
  rw [hA.isHermitian.spectrum_real_eq_range_eigenvalues] at hx
  rcases hx with ⟨i, rfl⟩
  exact hA.eigenvalues_pos i

/-- The real spectrum of a positive definite finite complex matrix lies in a
positive compact interval.  The nonempty-index assumption is the finite
dimension witness needed to take explicit eigenvalue min/max bounds. -/
theorem matrix_posDef_spectrum_real_subset_Icc
    {ι : Type*} [Fintype ι] [DecidableEq ι] [Nonempty ι]
    {A : Matrix ι ι ℂ} (hA : Matrix.PosDef A) :
    ∃ a b : ℝ, 0 < a ∧ spectrum ℝ A ⊆ Set.Icc a b := by
  classical
  let e : ι → ℝ := hA.isHermitian.eigenvalues
  have hne : (Finset.univ : Finset ι).Nonempty :=
    ⟨Classical.arbitrary ι, Finset.mem_univ _⟩
  let a : ℝ := (Finset.univ : Finset ι).inf' hne e
  let b : ℝ := (Finset.univ : Finset ι).sup' hne e
  have ha : 0 < a := by
    dsimp [a]
    rw [Finset.lt_inf'_iff]
    intro i _
    exact hA.eigenvalues_pos i
  refine ⟨a, b, ha, ?_⟩
  intro x hx
  rw [hA.isHermitian.spectrum_real_eq_range_eigenvalues] at hx
  rcases hx with ⟨i, rfl⟩
  constructor
  · exact Finset.inf'_le e (Finset.mem_univ i)
  · exact Finset.le_sup' e (Finset.mem_univ i)

/-- On any subset of a positive compact interval, the entropy kernel admits a
sequence of real-polynomial approximants converging uniformly on that subset.
This packages the Weierstrass approximation input in the `TendstoUniformlyOn`
form used by finite-matrix CFC continuity. -/
theorem exists_realPolynomial_tendstoUniformlyOn_realEntropyKernel_on_subset_Icc
    {s : Set ℝ} {a b : ℝ} (ha : 0 < a) (hs : s ⊆ Set.Icc a b) :
    ∃ p : ℕ → Polynomial ℝ,
      TendstoUniformlyOn (fun n x => Polynomial.eval x (p n))
        realEntropyKernel Filter.atTop s := by
  classical
  have hexists : ∀ n : ℕ, ∃ q : Polynomial ℝ,
      ∀ x ∈ Set.Icc a b,
        |Polynomial.eval x q - realEntropyKernel x| <
          ((n + 1 : ℕ) : ℝ)⁻¹ := by
    intro n
    exact exists_realPolynomial_near_realEntropyKernel_on_Icc a b
      (((n + 1 : ℕ) : ℝ)⁻¹) ha
      (inv_pos.mpr (by exact_mod_cast Nat.succ_pos n))
  let p : ℕ → Polynomial ℝ := fun n => Classical.choose (hexists n)
  refine ⟨p, ?_⟩
  rw [Metric.tendstoUniformlyOn_iff]
  intro ε hε
  have htendsto :
      Filter.Tendsto (fun n : ℕ => ((n + 1 : ℕ) : ℝ)⁻¹)
        Filter.atTop (nhds 0) := by
    convert (tendsto_one_div_add_atTop_nhds_zero_nat (𝕜 := ℝ)) using 1
    ext n
    norm_num
  have hsmall :
      ∀ᶠ n in Filter.atTop, ((n + 1 : ℕ) : ℝ)⁻¹ < ε :=
    htendsto.eventually (Iio_mem_nhds hε)
  filter_upwards [hsmall] with n hn x hx
  have happrox := Classical.choose_spec (hexists n) x (hs hx)
  have hdist :
      dist (realEntropyKernel x) (Polynomial.eval x (p n)) <
        ((n + 1 : ℕ) : ℝ)⁻¹ := by
    simpa [p, Real.dist_eq, abs_sub_comm] using happrox
  exact lt_trans hdist hn

/-- Positive definite finite complex matrices have real-polynomial entropy
kernel approximants converging uniformly on their real spectrum. -/
theorem exists_realPolynomial_tendstoUniformlyOn_realEntropyKernel_spectrum_of_posDef
    {ι : Type*} [Fintype ι] [DecidableEq ι] [Nonempty ι]
    {A : Matrix ι ι ℂ} (hA : Matrix.PosDef A) :
    ∃ p : ℕ → Polynomial ℝ,
      TendstoUniformlyOn (fun n x => Polynomial.eval x (p n))
        realEntropyKernel Filter.atTop (spectrum ℝ A) := by
  rcases matrix_posDef_spectrum_real_subset_Icc hA with ⟨a, b, ha, hs⟩
  exact exists_realPolynomial_tendstoUniformlyOn_realEntropyKernel_on_subset_Icc
    ha hs

/-- The vectorized identity converts powers of a Kronecker left-right lift into
ordinary traces of matching powers.  This is a polynomial trace-representation
substrate for the finite superoperator log route. -/
theorem matrixComplexQuadraticForm_vecId_kronecker_transpose_pow
    {ι : Type*} [Fintype ι] [DecidableEq ι]
    (A B : Matrix ι ι ℂ) (n : ℕ) :
    matrixComplexQuadraticForm ((A ⊗ₖ B.transpose) ^ n)
        (matrixVecId (ι := ι)) =
      Matrix.trace (A ^ n * B ^ n) := by
  classical
  rw [← matrixVec_one]
  rw [matrixComplexQuadraticForm,
    matrix_kronecker_transpose_pow_mulVec_matrixVec]
  simp [matrixVec, Matrix.trace, Matrix.mul_apply]
  calc
    (∑ x : ι × ι,
        star (if x.1 = x.2 then (1 : ℂ) else 0) *
          ∑ x_1 : ι, (A ^ n) x.1 x_1 * (B ^ n) x_1 x.2) =
      ∑ i : ι, ∑ j : ι, (A ^ n) i j * (B ^ n) j i := by
        simpa using
          (finset_sum_product_diagonal (F := fun i k =>
            ∑ j : ι, (A ^ n) i j * (B ^ n) j k))
    _ = ∑ i : ι, ∑ j : ι, (A ^ n) i j * (B ^ n) j i := rfl

/-- The vectorized-identity pairing of a powered Kronecker left-right lift,
followed by a right-multiplication lift, is the trace
`tr(A^n C B^n)`.  This is the polynomial substrate for the Effros
superoperator perspective term `p(L_A R_B) R_C`. -/
theorem matrixComplexQuadraticForm_vecId_kronecker_transpose_pow_right
    {ι : Type*} [Fintype ι] [DecidableEq ι]
    (A B C : Matrix ι ι ℂ) (n : ℕ) :
    matrixComplexQuadraticForm
        (((A ⊗ₖ B.transpose) ^ n) *
          ((1 : Matrix ι ι ℂ) ⊗ₖ C.transpose))
        (matrixVecId (ι := ι)) =
      Matrix.trace (A ^ n * C * B ^ n) := by
  classical
  rw [matrixComplexQuadraticForm]
  rw [← Matrix.mulVec_mulVec]
  have hright :
      Matrix.mulVec ((1 : Matrix ι ι ℂ) ⊗ₖ C.transpose)
          (matrixVecId (ι := ι)) = matrixVec C := by
    rw [← matrixVec_one]
    rw [matrix_kronecker_transpose_mulVec_matrixVec]
    simp
  rw [hright]
  rw [matrix_kronecker_transpose_pow_mulVec_matrixVec]
  exact matrixVecId_inner_matrixVec (A ^ n * C * B ^ n)

/-- The complex quadratic form is linear in its matrix argument over finite
sums. -/
theorem matrixComplexQuadraticForm_sum
    {ν α : Type*} [Fintype ν] (s : Finset α) (M : α → Matrix ν ν ℂ)
    (v : ν → ℂ) :
    matrixComplexQuadraticForm (∑ a ∈ s, M a) v =
      ∑ a ∈ s, matrixComplexQuadraticForm (M a) v := by
  classical
  simp [matrixComplexQuadraticForm, Matrix.sum_mulVec, Finset.mul_sum]
  rw [Finset.sum_comm]

/-- The complex quadratic form is linear in scalar multiplication of its
matrix argument. -/
theorem matrixComplexQuadraticForm_smul
    {ν : Type*} [Fintype ν] (c : ℂ) (M : Matrix ν ν ℂ) (v : ν → ℂ) :
    matrixComplexQuadraticForm (c • M) v =
      c * matrixComplexQuadraticForm M v := by
  classical
  simp [matrixComplexQuadraticForm, Matrix.smul_mulVec, Finset.mul_sum,
    mul_assoc, mul_comm]

/-- The complex quadratic form is additive in its matrix argument. -/
theorem matrixComplexQuadraticForm_add
    {ν : Type*} [Fintype ν] (M N : Matrix ν ν ℂ) (v : ν → ℂ) :
    matrixComplexQuadraticForm (M + N) v =
      matrixComplexQuadraticForm M v +
        matrixComplexQuadraticForm N v := by
  classical
  simpa using
    (matrixComplexQuadraticForm_sum (ν := ν)
      (s := ({true, false} : Finset Bool))
      (M := fun b : Bool => cond b M N) v)

/-- Finite polynomial combinations of a Kronecker left-right lift have the
corresponding polynomial trace-pairing formula against the vectorized identity.
This is the finite polynomial layer immediately below the remaining CFC/log
superoperator step. -/
theorem matrixComplexQuadraticForm_vecId_kronecker_transpose_polynomial
    {ι : Type*} [Fintype ι] [DecidableEq ι]
    (A B : Matrix ι ι ℂ) (s : Finset ℕ) (coeff : ℕ → ℂ) :
    matrixComplexQuadraticForm
        (∑ k ∈ s, coeff k • ((A ⊗ₖ B.transpose) ^ k))
        (matrixVecId (ι := ι)) =
      ∑ k ∈ s, coeff k * Matrix.trace (A ^ k * B ^ k) := by
  classical
  rw [matrixComplexQuadraticForm_sum]
  apply Finset.sum_congr rfl
  intro k hk
  rw [matrixComplexQuadraticForm_smul,
    matrixComplexQuadraticForm_vecId_kronecker_transpose_pow]

/-- Finite polynomial combinations of a Kronecker left-right lift followed by
a right-multiplication lift have the corresponding trace formula. -/
theorem matrixComplexQuadraticForm_vecId_kronecker_transpose_polynomial_right
    {ι : Type*} [Fintype ι] [DecidableEq ι]
    (A B C : Matrix ι ι ℂ) (s : Finset ℕ) (coeff : ℕ → ℂ) :
    matrixComplexQuadraticForm
        ((∑ k ∈ s, coeff k • ((A ⊗ₖ B.transpose) ^ k)) *
          ((1 : Matrix ι ι ℂ) ⊗ₖ C.transpose))
        (matrixVecId (ι := ι)) =
      ∑ k ∈ s, coeff k * Matrix.trace (A ^ k * C * B ^ k) := by
  classical
  rw [Finset.sum_mul]
  simp only [Matrix.smul_mul]
  rw [matrixComplexQuadraticForm_sum]
  apply Finset.sum_congr rfl
  intro k _hk
  rw [matrixComplexQuadraticForm_smul,
    matrixComplexQuadraticForm_vecId_kronecker_transpose_pow_right]

/-- Polynomial evaluation of a Kronecker left-right lift has the corresponding
trace-pairing formula against the vectorized identity.  This restates the
finite-polynomial layer in Lean's standard `Polynomial.aeval` vocabulary, which
is the interface used by functional-calculus approximation arguments. -/
theorem matrixComplexQuadraticForm_vecId_kronecker_transpose_aeval
    {ι : Type*} [Fintype ι] [DecidableEq ι]
    (A B : Matrix ι ι ℂ) (p : Polynomial ℂ) :
    matrixComplexQuadraticForm
        (Polynomial.aeval (A ⊗ₖ B.transpose) p)
        (matrixVecId (ι := ι)) =
      ∑ k ∈ p.support, p.coeff k * Matrix.trace (A ^ k * B ^ k) := by
  classical
  conv_lhs =>
    rw [Polynomial.as_sum_support_C_mul_X_pow p]
  simp only [map_sum, map_mul, Polynomial.aeval_C, Polynomial.aeval_X_pow]
  simp [Algebra.algebraMap_eq_smul_one,
    matrixComplexQuadraticForm_vecId_kronecker_transpose_polynomial]

/-- Polynomial evaluation of a Kronecker left-right lift followed by a
right-multiplication lift has the corresponding trace formula.  This is the
standard-polynomial interface for the finite superoperator perspective route. -/
theorem matrixComplexQuadraticForm_vecId_kronecker_transpose_aeval_right
    {ι : Type*} [Fintype ι] [DecidableEq ι]
    (A B C : Matrix ι ι ℂ) (p : Polynomial ℂ) :
    matrixComplexQuadraticForm
        ((Polynomial.aeval (A ⊗ₖ B.transpose) p) *
          ((1 : Matrix ι ι ℂ) ⊗ₖ C.transpose))
        (matrixVecId (ι := ι)) =
      ∑ k ∈ p.support, p.coeff k * Matrix.trace (A ^ k * C * B ^ k) := by
  classical
  conv_lhs =>
    rw [Polynomial.as_sum_support_C_mul_X_pow p]
  simp only [map_sum, map_mul, Polynomial.aeval_C, Polynomial.aeval_X_pow]
  simp [Algebra.algebraMap_eq_smul_one,
    matrixComplexQuadraticForm_vecId_kronecker_transpose_polynomial_right]

/-- Real-polynomial CFC of a self-adjoint Kronecker left-right lift has the
same vectorized-identity trace pairing as the corresponding complexified
polynomial.  This is the CFC polynomial layer immediately below the remaining
logarithmic approximation theorem for the superoperator route. -/
theorem matrixComplexQuadraticForm_vecId_matrixSelfAdjointCfc_kronecker_transpose_realPolynomial
    {ι : Type*} [Fintype ι] [DecidableEq ι]
    (A B : Matrix ι ι ℂ)
    (hA : IsSelfAdjoint A) (hB : IsSelfAdjoint B) (q : Polynomial ℝ) :
    matrixComplexQuadraticForm
        (matrixSelfAdjointCfc (fun x : ℝ => Polynomial.eval x q)
          (A ⊗ₖ B.transpose))
        (matrixVecId (ι := ι)) =
      ∑ k ∈ (q.map (algebraMap ℝ ℂ)).support,
        (q.map (algebraMap ℝ ℂ)).coeff k *
          Matrix.trace (A ^ k * B ^ k) := by
  classical
  have hK : IsSelfAdjoint (A ⊗ₖ B.transpose) :=
    matrix_kronecker_transpose_isSelfAdjoint_of_isSelfAdjoint hA hB
  rw [matrixSelfAdjointCfc_polynomial (M := A ⊗ₖ B.transpose) (q := q) hK]
  rw [← Polynomial.aeval_map_algebraMap ℂ (A ⊗ₖ B.transpose) q]
  exact matrixComplexQuadraticForm_vecId_kronecker_transpose_aeval
    A B (q.map (algebraMap ℝ ℂ))

/-- Real-polynomial CFC of the concrete finite left-right ratio
`X ⊗ (A⁻¹).transpose`, followed by right multiplication by `A`, has the
finite superoperator-perspective trace formula.  The remaining red-bottleneck
step is to pass this polynomial identity to the logarithmic kernel. -/
theorem matrixComplexQuadraticForm_vecId_matrixSelfAdjointCfc_kronecker_inv_transpose_realPolynomial_right
    {ι : Type*} [Fintype ι] [DecidableEq ι]
    (X A : Matrix ι ι ℂ)
    (hX : Matrix.PosDef X) (hA : Matrix.PosDef A) (q : Polynomial ℝ) :
    matrixComplexQuadraticForm
        (matrixSelfAdjointCfc (fun x : ℝ => Polynomial.eval x q)
          (X ⊗ₖ (A⁻¹).transpose) *
          ((1 : Matrix ι ι ℂ) ⊗ₖ A.transpose))
        (matrixVecId (ι := ι)) =
      ∑ k ∈ (q.map (algebraMap ℝ ℂ)).support,
        (q.map (algebraMap ℝ ℂ)).coeff k *
          Matrix.trace (X ^ k * A * (A⁻¹) ^ k) := by
  classical
  have hXsa : IsSelfAdjoint X := hX.isHermitian.isSelfAdjoint
  have hAinv : IsSelfAdjoint A⁻¹ := hA.inv.isHermitian.isSelfAdjoint
  have hK : IsSelfAdjoint (X ⊗ₖ (A⁻¹).transpose) :=
    matrix_kronecker_transpose_isSelfAdjoint_of_isSelfAdjoint hXsa hAinv
  rw [matrixSelfAdjointCfc_polynomial
    (M := X ⊗ₖ (A⁻¹).transpose) (q := q) hK]
  rw [← Polynomial.aeval_map_algebraMap ℂ
    (X ⊗ₖ (A⁻¹).transpose) q]
  exact matrixComplexQuadraticForm_vecId_kronecker_transpose_aeval_right
    X A⁻¹ A (q.map (algebraMap ℝ ℂ))

/-- If scalar functions converge uniformly on the real spectrum of a finite
self-adjoint matrix, then the corresponding CFC matrices also converge after
right multiplication and pairing by a fixed finite quadratic form.

This is the analytic transfer hook for the superoperator trace route: after
the finite polynomial trace formula is proved, this lemma lets a later proof
pass the identity through a uniform polynomial approximation to the logarithmic
or entropy kernel. -/
theorem tendsto_matrixComplexQuadraticForm_matrixSelfAdjointCfc_mul
    {X ν : Type*} [Fintype ν] [DecidableEq ν]
    {l : Filter X} (F : X → ℝ → ℝ) (f : ℝ → ℝ)
    (M R : Matrix ν ν ℂ) (v : ν → ℂ)
    (h_tendsto : TendstoUniformlyOn F f l (spectrum ℝ M))
    (hF : ∀ᶠ x in l, ContinuousOn (F x) (spectrum ℝ M)) :
    Filter.Tendsto
      (fun x => matrixComplexQuadraticForm
        (matrixSelfAdjointCfc (F x) M * R) v)
      l
      (nhds (matrixComplexQuadraticForm
        (matrixSelfAdjointCfc f M * R) v)) := by
  haveI : StarRing (Matrix ν ν ℂ) := Matrix.instStarRing
  have hcfc :
      Filter.Tendsto (fun x => matrixSelfAdjointCfc (F x) M) l
        (nhds (matrixSelfAdjointCfc f M)) := by
    dsimp [matrixSelfAdjointCfc]
    exact @tendsto_cfc_fun X ℝ (Matrix ν ν ℂ) IsSelfAdjoint
      inferInstance inferInstance inferInstance inferInstance inferInstance
      inferInstance Matrix.instStarRing inferInstance inferInstance
      Matrix.IsHermitian.instContinuousFunctionalCalculus
      l F f M h_tendsto hF
  have hcont :
      Continuous fun N : Matrix ν ν ℂ =>
        matrixComplexQuadraticForm (N * R) v := by
    exact (continuous_matrixComplexQuadraticForm v).comp
      (continuous_id.mul continuous_const)
  exact hcont.tendsto _ |>.comp hcfc

/-- Uniform polynomial approximation to the normalized entropy kernel transfers
the finite-polynomial superoperator trace formula to the CFC entropy-kernel
trace term.

The hypothesis is deliberately explicit: this theorem does not assert the
existence of a concrete approximating net for a given spectrum.  Instead it
closes the analytic passage from such a uniform approximation, once supplied,
to the source-faithful Effros/Umegaki superoperator expression. -/
theorem tendsto_superoperator_entropyKernel_of_realPolynomial_uniform_approx
    {X ι : Type*} [Fintype ι] [DecidableEq ι]
    {l : Filter X} (p : X → Polynomial ℝ)
    (Xmat A : Matrix ι ι ℂ)
    (hX : Matrix.PosDef Xmat) (hA : Matrix.PosDef A)
    (h_tendsto : TendstoUniformlyOn
      (fun t x => Polynomial.eval x (p t)) realEntropyKernel l
      (spectrum ℝ (Xmat ⊗ₖ (A⁻¹).transpose))) :
    Filter.Tendsto
      (fun t =>
        ∑ k ∈ ((p t).map (algebraMap ℝ ℂ)).support,
          ((p t).map (algebraMap ℝ ℂ)).coeff k *
            Matrix.trace (Xmat ^ k * A * (A⁻¹) ^ k))
      l
      (nhds
        (matrixComplexQuadraticForm
          (matrixSelfAdjointCfc realEntropyKernel
            (Xmat ⊗ₖ (A⁻¹).transpose) *
            ((1 : Matrix ι ι ℂ) ⊗ₖ A.transpose))
          (matrixVecId (ι := ι)))) := by
  have hF :
      ∀ᶠ t in l,
        ContinuousOn (fun x => Polynomial.eval x (p t))
          (spectrum ℝ (Xmat ⊗ₖ (A⁻¹).transpose)) := by
    filter_upwards with t
    exact (p t).continuous.continuousOn
  have hmain : Filter.Tendsto
      (fun t => matrixComplexQuadraticForm
        (matrixSelfAdjointCfc (fun x => Polynomial.eval x (p t))
          (Xmat ⊗ₖ (A⁻¹).transpose) *
          ((1 : Matrix ι ι ℂ) ⊗ₖ A.transpose))
        (matrixVecId (ι := ι)))
      l
      (nhds
        (matrixComplexQuadraticForm
          (matrixSelfAdjointCfc realEntropyKernel
            (Xmat ⊗ₖ (A⁻¹).transpose) *
            ((1 : Matrix ι ι ℂ) ⊗ₖ A.transpose))
          (matrixVecId (ι := ι)))) :=
    tendsto_matrixComplexQuadraticForm_matrixSelfAdjointCfc_mul
      (F := fun t x => Polynomial.eval x (p t)) (f := realEntropyKernel)
      (M := Xmat ⊗ₖ (A⁻¹).transpose)
      (R := (1 : Matrix ι ι ℂ) ⊗ₖ A.transpose)
      (v := matrixVecId (ι := ι)) h_tendsto hF
  convert hmain using 1
  ext t
  exact (matrixComplexQuadraticForm_vecId_matrixSelfAdjointCfc_kronecker_inv_transpose_realPolynomial_right
    Xmat A hX hA (p t)).symm

/-- For positive definite source matrices, the entropy-kernel superoperator
trace term is the uniform limit of the finite real-polynomial trace formulas.

This removes the earlier explicit approximation hypothesis by constructing a
polynomial approximating sequence on the positive real spectrum of
`X ⊗ (A⁻¹).transpose`.  It is still an analytic representation theorem, not
yet the noncommutative relative-entropy joint convexity theorem. -/
theorem exists_realPolynomial_tendsto_superoperator_entropyKernel_trace_of_posDef
    {ι : Type*} [Fintype ι] [DecidableEq ι] [Nonempty ι]
    (Xmat A : Matrix ι ι ℂ)
    (hX : Matrix.PosDef Xmat) (hA : Matrix.PosDef A) :
    ∃ p : ℕ → Polynomial ℝ,
      Filter.Tendsto
        (fun n =>
          ∑ k ∈ ((p n).map (algebraMap ℝ ℂ)).support,
            ((p n).map (algebraMap ℝ ℂ)).coeff k *
              Matrix.trace (Xmat ^ k * A * (A⁻¹) ^ k))
        Filter.atTop
        (nhds
          (matrixComplexQuadraticForm
            (matrixSelfAdjointCfc realEntropyKernel
              (Xmat ⊗ₖ (A⁻¹).transpose) *
              ((1 : Matrix ι ι ℂ) ⊗ₖ A.transpose))
            (matrixVecId (ι := ι)))) := by
  have hK : Matrix.PosDef (Xmat ⊗ₖ (A⁻¹).transpose) :=
    matrix_kronecker_inv_transpose_posDef hX hA
  rcases
      exists_realPolynomial_tendstoUniformlyOn_realEntropyKernel_spectrum_of_posDef
        (A := Xmat ⊗ₖ (A⁻¹).transpose) hK with
    ⟨p, hp⟩
  exact ⟨p,
    tendsto_superoperator_entropyKernel_of_realPolynomial_uniform_approx
      p Xmat A hX hA hp⟩

/-- A single real-polynomial entropy-kernel approximating sequence can be
chosen to converge both on the concrete superoperator spectrum and at every
source eigenvalue ratio `λ_j μ_k^{-1}`.

This is the limiting bridge that puts the polynomial trace identities and the
overlap scalar side on the same sequence. -/
theorem exists_realPolynomial_tendsto_superoperator_entropyKernel_trace_and_overlap_of_posDef
    {ι : Type*} [Fintype ι] [DecidableEq ι] [Nonempty ι]
    (Xmat A : Matrix ι ι ℂ)
    (hX : Matrix.PosDef Xmat) (hA : Matrix.PosDef A) :
    ∃ p : ℕ → Polynomial ℝ,
      Filter.Tendsto
        (fun n =>
          ∑ k ∈ ((p n).map (algebraMap ℝ ℂ)).support,
            ((p n).map (algebraMap ℝ ℂ)).coeff k *
              Matrix.trace (Xmat ^ k * A * (A⁻¹) ^ k))
        Filter.atTop
        (nhds
          (matrixComplexQuadraticForm
            (matrixSelfAdjointCfc realEntropyKernel
              (Xmat ⊗ₖ (A⁻¹).transpose) *
              ((1 : Matrix ι ι ℂ) ⊗ₖ A.transpose))
            (matrixVecId (ι := ι)))) ∧
      Filter.Tendsto
        (fun n =>
          ∑ j : ι, ∑ k : ι,
            (hA.isHermitian.eigenvalues k *
              Polynomial.eval
                (hX.isHermitian.eigenvalues j *
                  (hA.isHermitian.eigenvalues k)⁻¹) (p n)) *
              Complex.normSq
                (((star (hX.isHermitian.eigenvectorUnitary :
                    Matrix ι ι ℂ)) *
                  (hA.isHermitian.eigenvectorUnitary :
                    Matrix ι ι ℂ)) j k))
        Filter.atTop
        (nhds
          (∑ j : ι, ∑ k : ι,
            realRelativeEntropy (hX.isHermitian.eigenvalues j)
                (hA.isHermitian.eigenvalues k) *
              Complex.normSq
                (((star (hX.isHermitian.eigenvectorUnitary :
                    Matrix ι ι ℂ)) *
                  (hA.isHermitian.eigenvectorUnitary :
                    Matrix ι ι ℂ)) j k))) := by
  classical
  let K : Matrix (ι × ι) (ι × ι) ℂ :=
    Xmat ⊗ₖ (A⁻¹).transpose
  have hK : Matrix.PosDef K := by
    dsimp [K]
    exact matrix_kronecker_inv_transpose_posDef hX hA
  rcases matrix_posDef_spectrum_real_subset_Icc hK with
    ⟨aK, bK, haK, hsK⟩
  let ratio : ι × ι → ℝ := fun jk =>
    hX.isHermitian.eigenvalues jk.1 *
      (hA.isHermitian.eigenvalues jk.2)⁻¹
  have huniv_pair : (Finset.univ : Finset (ι × ι)).Nonempty :=
    ⟨(Classical.arbitrary ι, Classical.arbitrary ι), Finset.mem_univ _⟩
  let aR : ℝ := (Finset.univ : Finset (ι × ι)).inf' huniv_pair ratio
  let bR : ℝ := (Finset.univ : Finset (ι × ι)).sup' huniv_pair ratio
  have haR : 0 < aR := by
    dsimp [aR]
    rw [Finset.lt_inf'_iff]
    intro jk _hjk
    exact mul_pos (hX.eigenvalues_pos jk.1)
      (inv_pos.mpr (hA.eigenvalues_pos jk.2))
  have hratio_Icc :
      ∀ j k : ι, ratio (j, k) ∈ Set.Icc aR bR := by
    intro j k
    constructor
    · exact Finset.inf'_le ratio (Finset.mem_univ (j, k))
    · exact Finset.le_sup' ratio (Finset.mem_univ (j, k))
  let a : ℝ := min aK aR
  let b : ℝ := max bK bR
  have ha : 0 < a := lt_min haK haR
  have hs_union :
      (spectrum ℝ K ∪ Set.range ratio) ⊆ Set.Icc a b := by
    intro x hx
    rcases hx with hx | hx
    · have hxK := hsK hx
      constructor
      · exact le_trans (min_le_left aK aR) hxK.1
      · exact le_trans hxK.2 (le_max_left bK bR)
    · rcases hx with ⟨jk, rfl⟩
      have hr := hratio_Icc jk.1 jk.2
      constructor
      · exact le_trans (min_le_right aK aR) hr.1
      · exact le_trans hr.2 (le_max_right bK bR)
  rcases
      exists_realPolynomial_tendstoUniformlyOn_realEntropyKernel_on_subset_Icc
        (s := spectrum ℝ K ∪ Set.range ratio) ha hs_union with
    ⟨p, hp⟩
  refine ⟨p, ?_, ?_⟩
  · exact tendsto_superoperator_entropyKernel_of_realPolynomial_uniform_approx
      p Xmat A hX hA (hp.mono (Set.subset_union_left))
  · exact tendsto_matrixPolynomialTraceRatio_overlap_sum_of_uniform_approx
      p Xmat A hX hA hp
      (fun j k => by
        refine Or.inr ⟨(j, k), ?_⟩
        rfl)

/-- Polynomial evaluation on finite complex matrices is continuous in the
matrix argument.  This is the domain-side continuity companion to the
quadratic-form continuity hook for later CFC/log approximation. -/
theorem continuous_matrix_polynomial_aeval
    {ν : Type*} [Fintype ν] [DecidableEq ν] (p : Polynomial ℂ) :
    Continuous fun M : Matrix ν ν ℂ => Polynomial.aeval M p := by
  classical
  rw [Polynomial.as_sum_support_C_mul_X_pow p]
  simp only [map_sum, map_mul, Polynomial.aeval_C, Polynomial.aeval_X_pow]
  fun_prop

/-- The vectorized identity converts a Kronecker lift with a transpose into
the ordinary trace pairing.  This is the finite trace-representation substrate
for the remaining Effros superoperator perspective route. -/
theorem matrixComplexQuadraticForm_vecId_kronecker_transpose
    {ι : Type*} [Fintype ι] [DecidableEq ι]
    (A B : Matrix ι ι ℂ) :
    matrixComplexQuadraticForm (A ⊗ₖ B.transpose) (matrixVecId (ι := ι)) =
      Matrix.trace (A * B) := by
  classical
  simp [matrixComplexQuadraticForm, matrixVecId, Matrix.mulVec, Matrix.trace,
    Matrix.mul_apply, Matrix.kroneckerMap_apply, Matrix.transpose_apply]
  calc
    (∑ x : ι × ι,
        if x.1 = x.2 then
          ∑ j : ι × ι,
            A x.1 j.1 * B j.2 x.2 *
              if j.1 = j.2 then (1 : ℂ) else 0
        else 0) =
      ∑ i : ι, ∑ j : ι × ι,
        A i j.1 * B j.2 i * if j.1 = j.2 then (1 : ℂ) else 0 := by
        simpa using
          (finset_sum_product_diagonal (F := fun i k =>
            ∑ j : ι × ι,
              A i j.1 * B j.2 k * if j.1 = j.2 then (1 : ℂ) else 0))
    _ = ∑ i : ι, ∑ j : ι, A i j * B j i := by
        apply Finset.sum_congr rfl
        intro i _
        simpa [mul_ite] using
          (finset_sum_product_diagonal (F := fun j k => A i j * B k i))
    _ = ∑ x : ι, ∑ j : ι, A x j * B j x := rfl

/-- The left Kronecker lift `A ↦ A ⊗ I` is affine for real weighted sums. -/
theorem matrix_kronecker_left_identity_real_smul_add
    {ι : Type*} [Fintype ι] [DecidableEq ι]
    (a b : ℝ) (A B : Matrix ι ι ℂ) :
    ((a • A + b • B) ⊗ₖ (1 : Matrix ι ι ℂ)) =
      a • (A ⊗ₖ (1 : Matrix ι ι ℂ)) +
        b • (B ⊗ₖ (1 : Matrix ι ι ℂ)) := by
  ext i j
  simp [Matrix.kroneckerMap_apply, add_mul]
  ring

/-- The right Kronecker lift `A ↦ I ⊗ A` is affine for real weighted sums. -/
theorem matrix_kronecker_right_identity_real_smul_add
    {ι : Type*} [Fintype ι] [DecidableEq ι]
    (a b : ℝ) (A B : Matrix ι ι ℂ) :
    ((1 : Matrix ι ι ℂ) ⊗ₖ (a • A + b • B)) =
      a • ((1 : Matrix ι ι ℂ) ⊗ₖ A) +
        b • ((1 : Matrix ι ι ℂ) ⊗ₖ B) := by
  ext i j
  simp [Matrix.kroneckerMap_apply, mul_add]
  ring

/-- Multiplying the two source Kronecker lifts in left-right order gives the
plain Kronecker product. -/
theorem matrix_kronecker_left_identity_mul_right_identity
    {ι : Type*} [Fintype ι] [DecidableEq ι]
    (A H : Matrix ι ι ℂ) :
    (A ⊗ₖ (1 : Matrix ι ι ℂ)) *
        ((1 : Matrix ι ι ℂ) ⊗ₖ H) =
      A ⊗ₖ H := by
  rw [← Matrix.mul_kronecker_mul]
  simp

/-- Multiplying the two source Kronecker lifts in right-left order gives the
same plain Kronecker product. -/
theorem matrix_kronecker_right_identity_mul_left_identity
    {ι : Type*} [Fintype ι] [DecidableEq ι]
    (A H : Matrix ι ι ℂ) :
    ((1 : Matrix ι ι ℂ) ⊗ₖ H) *
        (A ⊗ₖ (1 : Matrix ι ι ℂ)) =
      A ⊗ₖ H := by
  rw [← Matrix.mul_kronecker_mul]
  simp

/-- The two Kronecker lifts `A ⊗ I` and `I ⊗ H` commute. -/
theorem matrix_kronecker_left_right_commute
    {ι : Type*} [Fintype ι] [DecidableEq ι]
    (A H : Matrix ι ι ℂ) :
    (A ⊗ₖ (1 : Matrix ι ι ℂ)) *
        ((1 : Matrix ι ι ℂ) ⊗ₖ H) =
      ((1 : Matrix ι ι ℂ) ⊗ₖ H) *
        (A ⊗ₖ (1 : Matrix ι ι ℂ)) := by
  rw [matrix_kronecker_left_identity_mul_right_identity,
    matrix_kronecker_right_identity_mul_left_identity]

/-- Positive definiteness is preserved by the left Kronecker lift `A ↦ A ⊗ I`. -/
theorem matrix_kronecker_posDef_left_identity
    {ι : Type*} [Fintype ι] [DecidableEq ι]
    {A : Matrix ι ι ℂ} (hA : Matrix.PosDef A) :
    Matrix.PosDef (A ⊗ₖ (1 : Matrix ι ι ℂ)) :=
  hA.kronecker Matrix.PosDef.one

/-- Positive definiteness is preserved by the right Kronecker lift `A ↦ I ⊗ A`. -/
theorem matrix_kronecker_posDef_right_identity
    {ι : Type*} [Fintype ι] [DecidableEq ι]
    {A : Matrix ι ι ℂ} (hA : Matrix.PosDef A) :
    Matrix.PosDef ((1 : Matrix ι ι ℂ) ⊗ₖ A) :=
  Matrix.PosDef.one.kronecker hA

/-- The right Kronecker lift `A ↦ I ⊗ Aᵀ` is affine for real weighted sums.
This is the concrete matrix representation of right multiplication under the
repository's vectorization convention. -/
theorem matrix_kronecker_right_identity_transpose_real_smul_add
    {ι : Type*} [Fintype ι] [DecidableEq ι]
    (a b : ℝ) (A B : Matrix ι ι ℂ) :
    ((1 : Matrix ι ι ℂ) ⊗ₖ (a • A + b • B).transpose) =
      a • ((1 : Matrix ι ι ℂ) ⊗ₖ A.transpose) +
        b • ((1 : Matrix ι ι ℂ) ⊗ₖ B.transpose) := by
  rw [Matrix.transpose_add, Matrix.transpose_smul, Matrix.transpose_smul]
  exact matrix_kronecker_right_identity_real_smul_add a b A.transpose B.transpose

/-- Product-index C-star matrix for the finite left-multiplication lift
`L_A`, represented as `A ⊗ I`. -/
noncomputable def cstarMatrixSuperoperatorLeftLift
    {ι : Type*} [Fintype ι] [DecidableEq ι]
    (A : CStarMatrix ι ι ℂ) : CStarMatrix (ι × ι) (ι × ι) ℂ :=
  CStarMatrix.ofMatrix
    ((CStarMatrix.ofMatrix.symm A : Matrix ι ι ℂ) ⊗ₖ
      (1 : Matrix ι ι ℂ))

/-- Product-index C-star matrix for the finite right-multiplication lift
`R_A`, represented as `I ⊗ Aᵀ` under the repository's vectorization
convention. -/
noncomputable def cstarMatrixSuperoperatorRightLift
    {ι : Type*} [Fintype ι] [DecidableEq ι]
    (A : CStarMatrix ι ι ℂ) : CStarMatrix (ι × ι) (ι × ι) ℂ :=
  CStarMatrix.ofMatrix
    ((1 : Matrix ι ι ℂ) ⊗ₖ
      (CStarMatrix.ofMatrix.symm A : Matrix ι ι ℂ).transpose)

/-- The product-index left-multiplication lift is affine for real weighted
sums. -/
theorem cstarMatrixSuperoperatorLeftLift_real_smul_add
    {ι : Type*} [Fintype ι] [DecidableEq ι]
    (a b : ℝ) (A B : CStarMatrix ι ι ℂ) :
    cstarMatrixSuperoperatorLeftLift (a • A + b • B) =
      a • cstarMatrixSuperoperatorLeftLift A +
        b • cstarMatrixSuperoperatorLeftLift B := by
  ext i j
  simp [cstarMatrixSuperoperatorLeftLift, Matrix.kroneckerMap_apply, add_mul]
  ring

/-- The product-index right-multiplication lift is affine for real weighted
sums. -/
theorem cstarMatrixSuperoperatorRightLift_real_smul_add
    {ι : Type*} [Fintype ι] [DecidableEq ι]
    (a b : ℝ) (A B : CStarMatrix ι ι ℂ) :
    cstarMatrixSuperoperatorRightLift (a • A + b • B) =
      a • cstarMatrixSuperoperatorRightLift A +
        b • cstarMatrixSuperoperatorRightLift B := by
  ext i j
  simp [cstarMatrixSuperoperatorRightLift, Matrix.kroneckerMap_apply,
    Matrix.transpose_apply, mul_add]
  ring

/-- Strict positivity is preserved by the product-index left-multiplication
lift. -/
theorem cstarMatrixSuperoperatorLeftLift_isStrictlyPositive
    {ι : Type*} [Fintype ι] [DecidableEq ι]
    {A : CStarMatrix ι ι ℂ} (hA : IsStrictlyPositive A) :
    IsStrictlyPositive (cstarMatrixSuperoperatorLeftLift A) := by
  apply cstarMatrix_isStrictlyPositive_of_matrix_posDef
  have hAm : Matrix.PosDef (CStarMatrix.ofMatrix.symm A : Matrix ι ι ℂ) :=
    cstarMatrix_isStrictlyPositive_to_matrix_posDef hA
  simpa [cstarMatrixSuperoperatorLeftLift] using
    matrix_kronecker_posDef_left_identity (ι := ι) hAm

/-- Strict positivity is preserved by the product-index right-multiplication
lift. -/
theorem cstarMatrixSuperoperatorRightLift_isStrictlyPositive
    {ι : Type*} [Fintype ι] [DecidableEq ι]
    {A : CStarMatrix ι ι ℂ} (hA : IsStrictlyPositive A) :
    IsStrictlyPositive (cstarMatrixSuperoperatorRightLift A) := by
  apply cstarMatrix_isStrictlyPositive_of_matrix_posDef
  have hAm : Matrix.PosDef (CStarMatrix.ofMatrix.symm A : Matrix ι ι ℂ) :=
    cstarMatrix_isStrictlyPositive_to_matrix_posDef hA
  have hright :
      Matrix.PosDef
        ((1 : Matrix ι ι ℂ) ⊗ₖ
          (CStarMatrix.ofMatrix.symm A : Matrix ι ι ℂ).transpose) :=
    Matrix.PosDef.one.kronecker hAm.transpose
  simpa [cstarMatrixSuperoperatorRightLift] using hright

/-- The product-index left and right superoperator lifts commute. -/
theorem cstarMatrixSuperoperatorLeftLift_rightLift_commute
    {ι : Type*} [Fintype ι] [DecidableEq ι]
    (X A : CStarMatrix ι ι ℂ) :
    Commute (cstarMatrixSuperoperatorLeftLift X)
      (cstarMatrixSuperoperatorRightLift A) := by
  ext i j
  simpa [cstarMatrixSuperoperatorLeftLift,
    cstarMatrixSuperoperatorRightLift] using
    congrFun
      (congrFun
        (matrix_kronecker_left_right_commute
          (CStarMatrix.ofMatrix.symm X : Matrix ι ι ℂ)
          (CStarMatrix.ofMatrix.symm A : Matrix ι ι ℂ).transpose) i) j

/-- The inverse square root of the right superoperator lift commutes with the
left superoperator lift.  This is the CFC commutation step needed to rewrite
the normalized argument inside the finite perspective. -/
theorem cstarMatrixSuperoperatorPositiveInvSqrtRightLift_commute_leftLift
    {ι : Type*} [Fintype ι] [DecidableEq ι]
    (X A : CStarMatrix ι ι ℂ) :
    Commute
      (cstarMatrixPositiveInvSqrt (cstarMatrixSuperoperatorRightLift A))
      (cstarMatrixSuperoperatorLeftLift X) := by
  have hcomm :
      Commute (cstarMatrixSuperoperatorRightLift A)
        (cstarMatrixSuperoperatorLeftLift X) :=
    (cstarMatrixSuperoperatorLeftLift_rightLift_commute X A).symm
  simpa [cstarMatrixPositiveInvSqrt] using
    hcomm.cfc_real (fun x : ℝ => (Real.sqrt x)⁻¹)

/-- The square root of the right superoperator lift commutes with the left
superoperator lift. -/
theorem cstarMatrixSuperoperatorPositiveSqrtRightLift_commute_leftLift
    {ι : Type*} [Fintype ι] [DecidableEq ι]
    (X A : CStarMatrix ι ι ℂ) :
    Commute
      (cstarMatrixPositiveSqrt (cstarMatrixSuperoperatorRightLift A))
      (cstarMatrixSuperoperatorLeftLift X) := by
  have hcomm :
      Commute (cstarMatrixSuperoperatorRightLift A)
        (cstarMatrixSuperoperatorLeftLift X) :=
    (cstarMatrixSuperoperatorLeftLift_rightLift_commute X A).symm
  simpa [cstarMatrixPositiveSqrt] using
    hcomm.cfc_real Real.sqrt

/-- The normalized argument in the ordinary product-index perspective can be
reordered because the left lift commutes with the inverse square root of the
right lift. -/
theorem cstarMatrixSuperoperatorPerspective_normalizedArgument_reorder
    {ι : Type*} [Fintype ι] [DecidableEq ι]
    (X A : CStarMatrix ι ι ℂ) :
    cstarMatrixPositiveInvSqrt (cstarMatrixSuperoperatorRightLift A) *
        cstarMatrixSuperoperatorLeftLift X *
        cstarMatrixPositiveInvSqrt (cstarMatrixSuperoperatorRightLift A) =
      cstarMatrixSuperoperatorLeftLift X *
        (cstarMatrixPositiveInvSqrt (cstarMatrixSuperoperatorRightLift A) *
          cstarMatrixPositiveInvSqrt (cstarMatrixSuperoperatorRightLift A)) := by
  let Q : CStarMatrix (ι × ι) (ι × ι) ℂ :=
    cstarMatrixPositiveInvSqrt (cstarMatrixSuperoperatorRightLift A)
  let L : CStarMatrix (ι × ι) (ι × ι) ℂ :=
    cstarMatrixSuperoperatorLeftLift X
  have hQL : Commute Q L := by
    dsimp [Q, L]
    exact cstarMatrixSuperoperatorPositiveInvSqrtRightLift_commute_leftLift X A
  dsimp [Q, L] at hQL ⊢
  calc
    cstarMatrixPositiveInvSqrt (cstarMatrixSuperoperatorRightLift A) *
        cstarMatrixSuperoperatorLeftLift X *
        cstarMatrixPositiveInvSqrt (cstarMatrixSuperoperatorRightLift A) =
      (cstarMatrixSuperoperatorLeftLift X *
          cstarMatrixPositiveInvSqrt (cstarMatrixSuperoperatorRightLift A)) *
        cstarMatrixPositiveInvSqrt (cstarMatrixSuperoperatorRightLift A) := by
        rw [hQL.eq]
    _ =
      cstarMatrixSuperoperatorLeftLift X *
        (cstarMatrixPositiveInvSqrt (cstarMatrixSuperoperatorRightLift A) *
          cstarMatrixPositiveInvSqrt (cstarMatrixSuperoperatorRightLift A)) := by
        exact mul_assoc _ _ _

/-- For strictly positive `A`, the normalized argument in the ordinary
product-index perspective is `L_X` multiplied by the inverse unit of the right
lift `R_A`. -/
theorem cstarMatrixSuperoperatorPerspective_normalizedArgument_eq_leftLift_mul_rightLift_unit_inv
    {ι : Type*} [Fintype ι] [DecidableEq ι]
    (X : CStarMatrix ι ι ℂ) {A : CStarMatrix ι ι ℂ}
    (hA : IsStrictlyPositive A) :
    cstarMatrixPositiveInvSqrt (cstarMatrixSuperoperatorRightLift A) *
        cstarMatrixSuperoperatorLeftLift X *
        cstarMatrixPositiveInvSqrt (cstarMatrixSuperoperatorRightLift A) =
      cstarMatrixSuperoperatorLeftLift X *
        (↑((cstarMatrixSuperoperatorRightLift_isStrictlyPositive hA).isUnit.unit⁻¹) :
          CStarMatrix (ι × ι) (ι × ι) ℂ) := by
  rw [cstarMatrixSuperoperatorPerspective_normalizedArgument_reorder]
  rw [cstarMatrixPositiveInvSqrt_mul_self_eq_unit_inv
    (cstarMatrixSuperoperatorRightLift_isStrictlyPositive hA)]

/-- The product-index ratio `L_X R_A^{-1}` commutes with the square root of
the right lift.  This is the CFC-commutation input for the final outer
square-root trace bridge. -/
theorem cstarMatrixSuperoperatorLeftLift_mul_rightLift_unit_inv_commute_positiveSqrtRightLift
    {ι : Type*} [Fintype ι] [DecidableEq ι]
    (X : CStarMatrix ι ι ℂ) {A : CStarMatrix ι ι ℂ}
    (hA : IsStrictlyPositive A) :
    Commute
      (cstarMatrixSuperoperatorLeftLift X *
        (↑((cstarMatrixSuperoperatorRightLift_isStrictlyPositive hA).isUnit.unit⁻¹) :
          CStarMatrix (ι × ι) (ι × ι) ℂ))
      (cstarMatrixPositiveSqrt (cstarMatrixSuperoperatorRightLift A)) := by
  let L : CStarMatrix (ι × ι) (ι × ι) ℂ :=
    cstarMatrixSuperoperatorLeftLift X
  let S : CStarMatrix (ι × ι) (ι × ι) ℂ :=
    cstarMatrixPositiveSqrt (cstarMatrixSuperoperatorRightLift A)
  let Rinv : CStarMatrix (ι × ι) (ι × ι) ℂ :=
    (↑((cstarMatrixSuperoperatorRightLift_isStrictlyPositive hA).isUnit.unit⁻¹) :
      CStarMatrix (ι × ι) (ι × ι) ℂ)
  have hSL : Commute S L := by
    dsimp [S, L]
    exact cstarMatrixSuperoperatorPositiveSqrtRightLift_commute_leftLift X A
  have hSR : Commute S Rinv := by
    dsimp [S, Rinv]
    exact cstarMatrixPositiveSqrt_commute_unit_inv
      (cstarMatrixSuperoperatorRightLift_isStrictlyPositive hA)
  dsimp [L, S, Rinv] at hSL hSR ⊢
  calc
    (cstarMatrixSuperoperatorLeftLift X *
        (↑((cstarMatrixSuperoperatorRightLift_isStrictlyPositive hA).isUnit.unit⁻¹) :
          CStarMatrix (ι × ι) (ι × ι) ℂ)) *
        cstarMatrixPositiveSqrt (cstarMatrixSuperoperatorRightLift A) =
      cstarMatrixSuperoperatorLeftLift X *
        ((↑((cstarMatrixSuperoperatorRightLift_isStrictlyPositive hA).isUnit.unit⁻¹) :
          CStarMatrix (ι × ι) (ι × ι) ℂ) *
          cstarMatrixPositiveSqrt (cstarMatrixSuperoperatorRightLift A)) := by
        exact cstarMatrix_mul_assoc_rect _ _ _
    _ =
      cstarMatrixSuperoperatorLeftLift X *
        (cstarMatrixPositiveSqrt (cstarMatrixSuperoperatorRightLift A) *
          (↑((cstarMatrixSuperoperatorRightLift_isStrictlyPositive hA).isUnit.unit⁻¹) :
            CStarMatrix (ι × ι) (ι × ι) ℂ)) := by
        rw [hSR.eq]
    _ =
      (cstarMatrixSuperoperatorLeftLift X *
          cstarMatrixPositiveSqrt (cstarMatrixSuperoperatorRightLift A)) *
        (↑((cstarMatrixSuperoperatorRightLift_isStrictlyPositive hA).isUnit.unit⁻¹) :
          CStarMatrix (ι × ι) (ι × ι) ℂ) := by
        exact (cstarMatrix_mul_assoc_rect _ _ _).symm
    _ =
      (cstarMatrixPositiveSqrt (cstarMatrixSuperoperatorRightLift A) *
          cstarMatrixSuperoperatorLeftLift X) *
        (↑((cstarMatrixSuperoperatorRightLift_isStrictlyPositive hA).isUnit.unit⁻¹) :
          CStarMatrix (ι × ι) (ι × ι) ℂ) := by
        rw [hSL.eq]
    _ =
      cstarMatrixPositiveSqrt (cstarMatrixSuperoperatorRightLift A) *
        (cstarMatrixSuperoperatorLeftLift X *
          (↑((cstarMatrixSuperoperatorRightLift_isStrictlyPositive hA).isUnit.unit⁻¹) :
            CStarMatrix (ι × ι) (ι × ι) ℂ)) := by
        exact cstarMatrix_mul_assoc_rect _ _ _

/-- The entropy-kernel CFC of the product-index ratio commutes with the square
root of the right lift. -/
theorem cstarMatrixSuperoperatorEntropyKernelCfc_ratio_commute_positiveSqrtRightLift
    {ι : Type*} [Fintype ι] [DecidableEq ι]
    (X : CStarMatrix ι ι ℂ) {A : CStarMatrix ι ι ℂ}
    (hA : IsStrictlyPositive A) :
    Commute
      (cfc (p := IsSelfAdjoint) realEntropyKernel
        (cstarMatrixSuperoperatorLeftLift X *
          (↑((cstarMatrixSuperoperatorRightLift_isStrictlyPositive hA).isUnit.unit⁻¹) :
            CStarMatrix (ι × ι) (ι × ι) ℂ)))
      (cstarMatrixPositiveSqrt (cstarMatrixSuperoperatorRightLift A)) := by
  have hcomm :=
    cstarMatrixSuperoperatorLeftLift_mul_rightLift_unit_inv_commute_positiveSqrtRightLift
      X hA
  simpa using hcomm.cfc_real realEntropyKernel

/-- The outer square roots in the product-index perspective collapse to the
right lift once the CFC ratio term is known to commute with the square root. -/
theorem cstarMatrixSuperoperatorPerspective_outerSqrt_cfc_ratio_mul_outerSqrt
    {ι : Type*} [Fintype ι] [DecidableEq ι]
    (X : CStarMatrix ι ι ℂ) {A : CStarMatrix ι ι ℂ}
    (hA : IsStrictlyPositive A) :
    cstarMatrixPositiveSqrt (cstarMatrixSuperoperatorRightLift A) *
        cfc (p := IsSelfAdjoint) realEntropyKernel
          (cstarMatrixSuperoperatorLeftLift X *
            (↑((cstarMatrixSuperoperatorRightLift_isStrictlyPositive hA).isUnit.unit⁻¹) :
              CStarMatrix (ι × ι) (ι × ι) ℂ)) *
        cstarMatrixPositiveSqrt (cstarMatrixSuperoperatorRightLift A) =
      cfc (p := IsSelfAdjoint) realEntropyKernel
          (cstarMatrixSuperoperatorLeftLift X *
            (↑((cstarMatrixSuperoperatorRightLift_isStrictlyPositive hA).isUnit.unit⁻¹) :
              CStarMatrix (ι × ι) (ι × ι) ℂ)) *
        cstarMatrixSuperoperatorRightLift A := by
  let S : CStarMatrix (ι × ι) (ι × ι) ℂ :=
    cstarMatrixPositiveSqrt (cstarMatrixSuperoperatorRightLift A)
  let F : CStarMatrix (ι × ι) (ι × ι) ℂ :=
    cfc (p := IsSelfAdjoint) realEntropyKernel
      (cstarMatrixSuperoperatorLeftLift X *
        (↑((cstarMatrixSuperoperatorRightLift_isStrictlyPositive hA).isUnit.unit⁻¹) :
          CStarMatrix (ι × ι) (ι × ι) ℂ))
  have hFS : Commute F S := by
    dsimp [F, S]
    exact
      cstarMatrixSuperoperatorEntropyKernelCfc_ratio_commute_positiveSqrtRightLift
        X hA
  have hSsq : S * S = cstarMatrixSuperoperatorRightLift A := by
    dsimp [S]
    exact cstarMatrixPositiveSqrt_mul_self
      (cstarMatrixSuperoperatorRightLift_isStrictlyPositive hA)
  dsimp [F, S] at hFS hSsq ⊢
  calc
    cstarMatrixPositiveSqrt (cstarMatrixSuperoperatorRightLift A) *
        cfc realEntropyKernel
          (cstarMatrixSuperoperatorLeftLift X *
            (↑((cstarMatrixSuperoperatorRightLift_isStrictlyPositive hA).isUnit.unit⁻¹) :
              CStarMatrix (ι × ι) (ι × ι) ℂ)) *
        cstarMatrixPositiveSqrt (cstarMatrixSuperoperatorRightLift A) =
      (cfc realEntropyKernel
          (cstarMatrixSuperoperatorLeftLift X *
            (↑((cstarMatrixSuperoperatorRightLift_isStrictlyPositive hA).isUnit.unit⁻¹) :
              CStarMatrix (ι × ι) (ι × ι) ℂ)) *
        cstarMatrixPositiveSqrt (cstarMatrixSuperoperatorRightLift A)) *
        cstarMatrixPositiveSqrt (cstarMatrixSuperoperatorRightLift A) := by
        rw [← hFS.eq]
    _ =
      cfc realEntropyKernel
          (cstarMatrixSuperoperatorLeftLift X *
            (↑((cstarMatrixSuperoperatorRightLift_isStrictlyPositive hA).isUnit.unit⁻¹) :
              CStarMatrix (ι × ι) (ι × ι) ℂ)) *
        (cstarMatrixPositiveSqrt (cstarMatrixSuperoperatorRightLift A) *
          cstarMatrixPositiveSqrt (cstarMatrixSuperoperatorRightLift A)) := by
        exact cstarMatrix_mul_assoc_rect _ _ _
    _ =
      cfc realEntropyKernel
          (cstarMatrixSuperoperatorLeftLift X *
            (↑((cstarMatrixSuperoperatorRightLift_isStrictlyPositive hA).isUnit.unit⁻¹) :
              CStarMatrix (ι × ι) (ι × ι) ℂ)) *
        cstarMatrixSuperoperatorRightLift A := by
        rw [hSsq]

/-- The ordinary product-index perspective equals the relative-modular CFC
term multiplied by the right lift, in C-star matrix form. -/
theorem cstarMatrixSuperoperatorPerspective_eq_cfc_ratio_mul_rightLift
    {ι : Type*} [Fintype ι] [DecidableEq ι]
    (X : CStarMatrix ι ι ℂ) {A : CStarMatrix ι ι ℂ}
    (hA : IsStrictlyPositive A) :
    cstarMatrixPerspective realEntropyKernel
        (cstarMatrixSuperoperatorLeftLift X)
        (cstarMatrixSuperoperatorRightLift A) =
      cfc (p := IsSelfAdjoint) realEntropyKernel
          (cstarMatrixSuperoperatorLeftLift X *
            (↑((cstarMatrixSuperoperatorRightLift_isStrictlyPositive hA).isUnit.unit⁻¹) :
              CStarMatrix (ι × ι) (ι × ι) ℂ)) *
        cstarMatrixSuperoperatorRightLift A := by
  dsimp [cstarMatrixPerspective]
  rw [cstarMatrixSuperoperatorPerspective_normalizedArgument_eq_leftLift_mul_rightLift_unit_inv
    X hA]
  exact cstarMatrixSuperoperatorPerspective_outerSqrt_cfc_ratio_mul_outerSqrt
    X hA

/-- Forgetting a C-star matrix unit inverse to the underlying finite matrix
gives the ordinary nonsingular inverse. -/
theorem cstarMatrix_unit_inv_to_matrix
    {ι : Type*} [Fintype ι] [DecidableEq ι]
    (u : (CStarMatrix ι ι ℂ)ˣ) :
    CStarMatrix.ofMatrix.symm (↑u⁻¹ : CStarMatrix ι ι ℂ) =
      (CStarMatrix.ofMatrix.symm (u : CStarMatrix ι ι ℂ) :
        Matrix ι ι ℂ)⁻¹ := by
  symm
  refine Matrix.inv_eq_right_inv ?_
  change CStarMatrix.ofMatrix.symm
      ((u : CStarMatrix ι ι ℂ) *
        (↑u⁻¹ : CStarMatrix ι ι ℂ)) =
    (1 : Matrix ι ι ℂ)
  exact congrArg
    (fun X : CStarMatrix ι ι ℂ =>
      (CStarMatrix.ofMatrix.symm X : Matrix ι ι ℂ))
    u.mul_inv

/-- The inverse unit of the product-index right lift has the expected
Kronecker matrix representation \(I\otimes (A^{-1})^{\mathsf T}\). -/
theorem cstarMatrixSuperoperatorRightLift_unit_inv_to_matrix
    {ι : Type*} [Fintype ι] [DecidableEq ι]
    {A : CStarMatrix ι ι ℂ} (hA : IsStrictlyPositive A) :
    CStarMatrix.ofMatrix.symm
        (↑((cstarMatrixSuperoperatorRightLift_isStrictlyPositive hA).isUnit.unit⁻¹) :
          CStarMatrix (ι × ι) (ι × ι) ℂ) =
      ((1 : Matrix ι ι ℂ) ⊗ₖ
        (CStarMatrix.ofMatrix.symm A : Matrix ι ι ℂ)⁻¹.transpose) := by
  let u : (CStarMatrix (ι × ι) (ι × ι) ℂ)ˣ :=
    (cstarMatrixSuperoperatorRightLift_isStrictlyPositive hA).isUnit.unit
  have hu :
      (u : CStarMatrix (ι × ι) (ι × ι) ℂ) =
        cstarMatrixSuperoperatorRightLift A := by
    dsimp [u]
  calc
    CStarMatrix.ofMatrix.symm
        (↑((cstarMatrixSuperoperatorRightLift_isStrictlyPositive hA).isUnit.unit⁻¹) :
          CStarMatrix (ι × ι) (ι × ι) ℂ) =
      CStarMatrix.ofMatrix.symm
        (↑u⁻¹ : CStarMatrix (ι × ι) (ι × ι) ℂ) := by
        rfl
    _ =
      (CStarMatrix.ofMatrix.symm
        (u : CStarMatrix (ι × ι) (ι × ι) ℂ) :
        Matrix (ι × ι) (ι × ι) ℂ)⁻¹ :=
        cstarMatrix_unit_inv_to_matrix u
    _ =
      (CStarMatrix.ofMatrix.symm (cstarMatrixSuperoperatorRightLift A) :
        Matrix (ι × ι) (ι × ι) ℂ)⁻¹ := by
        rw [hu]
    _ =
      (((1 : Matrix ι ι ℂ) ⊗ₖ
        (CStarMatrix.ofMatrix.symm A : Matrix ι ι ℂ).transpose))⁻¹ := by
        simp [cstarMatrixSuperoperatorRightLift]
    _ =
      (1 : Matrix ι ι ℂ)⁻¹ ⊗ₖ
        ((CStarMatrix.ofMatrix.symm A : Matrix ι ι ℂ).transpose)⁻¹ := by
        rw [Matrix.inv_kronecker]
    _ =
      ((1 : Matrix ι ι ℂ) ⊗ₖ
        (CStarMatrix.ofMatrix.symm A : Matrix ι ι ℂ)⁻¹.transpose) := by
        rw [inv_one]
        rw [← Matrix.transpose_nonsing_inv]

/-- Trace of a finite Kronecker product factors as the product of traces. -/
theorem matrix_trace_kronecker
    {ι : Type*} [Fintype ι] [DecidableEq ι]
    (A H : Matrix ι ι ℂ) :
    Matrix.trace (A ⊗ₖ H) = Matrix.trace A * Matrix.trace H := by
  simpa using (Matrix.trace_kronecker A H)

/-- Trace normalization for the left Kronecker lift `A ↦ A ⊗ I`. -/
theorem matrix_trace_kronecker_left_identity
    {ι : Type*} [Fintype ι] [DecidableEq ι]
    (A : Matrix ι ι ℂ) :
    Matrix.trace (A ⊗ₖ (1 : Matrix ι ι ℂ)) =
      (Fintype.card ι : ℂ) * Matrix.trace A := by
  rw [matrix_trace_kronecker, Matrix.trace_one]
  ring

/-- Trace normalization for the right Kronecker lift `A ↦ I ⊗ A`. -/
theorem matrix_trace_kronecker_right_identity
    {ι : Type*} [Fintype ι] [DecidableEq ι]
    (A : Matrix ι ι ℂ) :
    Matrix.trace ((1 : Matrix ι ι ℂ) ⊗ₖ A) =
      (Fintype.card ι : ℂ) * Matrix.trace A := by
  rw [matrix_trace_kronecker, Matrix.trace_one]

/-!
## Left and right multiplication for the Effros perspective route

The noncommutative joint-convexity theorem for matrix relative entropy is
usually proved by representing relative entropy through the perspective of the
operator-convex function `t ↦ t log t`.  In finite matrix form this route uses
left and right multiplication operators, typically denoted `L_X` and `R_A`.
The lemmas below close the algebraic part of that vocabulary: left/right
multiplication are endomorphisms of the C-star matrix vector space, are affine
in their matrix argument, commute with one another, and become invertible when
the underlying matrix is a unit, hence when it is strictly positive.
-/

/-- Left multiplication by a finite complex `CStarMatrix`, as a complex-linear
endomorphism of the matrix vector space. -/
noncomputable def cstarMatrixLeftMul
    {ι : Type*} [Fintype ι] [DecidableEq ι]
    (A : CStarMatrix ι ι ℂ) : Module.End ℂ (CStarMatrix ι ι ℂ) :=
  LinearMap.mulLeft ℂ A

/-- Right multiplication by a finite complex `CStarMatrix`, as a complex-linear
endomorphism of the matrix vector space. -/
noncomputable def cstarMatrixRightMul
    {ι : Type*} [Fintype ι] [DecidableEq ι]
    (A : CStarMatrix ι ι ℂ) : Module.End ℂ (CStarMatrix ι ι ℂ) :=
  LinearMap.mulRight ℂ A

@[simp]
theorem cstarMatrixLeftMul_apply
    {ι : Type*} [Fintype ι] [DecidableEq ι]
    (A Z : CStarMatrix ι ι ℂ) :
    cstarMatrixLeftMul A Z = A * Z := by
  rfl

@[simp]
theorem cstarMatrixRightMul_apply
    {ι : Type*} [Fintype ι] [DecidableEq ι]
    (A Z : CStarMatrix ι ι ℂ) :
    cstarMatrixRightMul A Z = Z * A := by
  rfl

@[simp]
theorem cstarMatrixLeftMul_one
    {ι : Type*} [Fintype ι] [DecidableEq ι] :
    cstarMatrixLeftMul (1 : CStarMatrix ι ι ℂ) = 1 := by
  apply LinearMap.ext
  intro Z
  exact one_mul Z

@[simp]
theorem cstarMatrixRightMul_one
    {ι : Type*} [Fintype ι] [DecidableEq ι] :
    cstarMatrixRightMul (1 : CStarMatrix ι ι ℂ) = 1 := by
  apply LinearMap.ext
  intro Z
  exact mul_one Z

/-- Left multiplication sends products to products of endomorphisms. -/
theorem cstarMatrixLeftMul_mul
    {ι : Type*} [Fintype ι] [DecidableEq ι]
    (A B : CStarMatrix ι ι ℂ) :
    cstarMatrixLeftMul (A * B) =
      cstarMatrixLeftMul A * cstarMatrixLeftMul B := by
  apply LinearMap.ext
  intro Z
  rw [Module.End.mul_eq_comp]
  simp only [LinearMap.comp_apply, cstarMatrixLeftMul_apply]
  exact mul_assoc A B Z

/-- Right multiplication sends products to products of endomorphisms in the
opposite order. -/
theorem cstarMatrixRightMul_mul
    {ι : Type*} [Fintype ι] [DecidableEq ι]
    (A B : CStarMatrix ι ι ℂ) :
    cstarMatrixRightMul (A * B) =
      cstarMatrixRightMul B * cstarMatrixRightMul A := by
  apply LinearMap.ext
  intro Z
  rw [Module.End.mul_eq_comp]
  simp only [LinearMap.comp_apply, cstarMatrixRightMul_apply]
  exact (mul_assoc Z A B).symm

/-- Left multiplication commutes with natural powers.  This is the polynomial
functional-calculus algebra needed before the full Effros perspective route. -/
theorem cstarMatrixLeftMul_pow
    {ι : Type*} [Fintype ι] [DecidableEq ι]
    (A : CStarMatrix ι ι ℂ) (n : ℕ) :
    cstarMatrixLeftMul (A ^ n) = (cstarMatrixLeftMul A) ^ n := by
  induction n with
  | zero =>
      simp
  | succ n ih =>
      calc
        cstarMatrixLeftMul (A ^ (n + 1)) =
            cstarMatrixLeftMul (A ^ n * A) := by
          rw [pow_succ]
          rfl
        _ = cstarMatrixLeftMul (A ^ n) * cstarMatrixLeftMul A :=
            cstarMatrixLeftMul_mul (A ^ n) A
        _ = (cstarMatrixLeftMul A) ^ n * cstarMatrixLeftMul A := by
            rw [ih]
        _ = (cstarMatrixLeftMul A) ^ (n + 1) := by rw [pow_succ]

/-- Right multiplication commutes with natural powers.  The anti-order in
`cstarMatrixRightMul_mul` disappears for powers of a single matrix. -/
theorem cstarMatrixRightMul_pow
    {ι : Type*} [Fintype ι] [DecidableEq ι]
    (A : CStarMatrix ι ι ℂ) (n : ℕ) :
    cstarMatrixRightMul (A ^ n) = (cstarMatrixRightMul A) ^ n := by
  induction n with
  | zero =>
      simp
  | succ n ih =>
      calc
        cstarMatrixRightMul (A ^ (n + 1)) =
            cstarMatrixRightMul (A ^ n * A) := by
          rw [pow_succ]
          rfl
        _ = cstarMatrixRightMul A * cstarMatrixRightMul (A ^ n) :=
            cstarMatrixRightMul_mul (A ^ n) A
        _ = cstarMatrixRightMul A * (cstarMatrixRightMul A) ^ n := by
            rw [ih]
        _ = (cstarMatrixRightMul A) ^ (n + 1) := by rw [pow_succ']

/-- Left multiplication is affine in the matrix argument for real weighted
sums.  This is the `L_{aA+bB} = a L_A + b L_B` part of the finite-dimensional
matrix-perspective route. -/
theorem cstarMatrixLeftMul_real_smul_add
    {ι : Type*} [Fintype ι] [DecidableEq ι]
    (a b : ℝ) (A B : CStarMatrix ι ι ℂ) :
    cstarMatrixLeftMul (a • A + b • B) =
      (a : ℂ) • cstarMatrixLeftMul A + (b : ℂ) • cstarMatrixLeftMul B := by
  ext Z i j
  simp [cstarMatrixLeftMul, add_mul]

/-- Right multiplication is affine in the matrix argument for real weighted
sums.  This is the `R_{aA+bB} = a R_A + b R_B` part of the finite-dimensional
matrix-perspective route. -/
theorem cstarMatrixRightMul_real_smul_add
    {ι : Type*} [Fintype ι] [DecidableEq ι]
    (a b : ℝ) (A B : CStarMatrix ι ι ℂ) :
    cstarMatrixRightMul (a • A + b • B) =
      (a : ℂ) • cstarMatrixRightMul A + (b : ℂ) • cstarMatrixRightMul B := by
  ext Z i j
  simp [cstarMatrixRightMul, mul_add]

/-- Applying `L_A R_B` gives the expected two-sided product. -/
theorem cstarMatrixLeftMul_mul_rightMul_apply
    {ι : Type*} [Fintype ι] [DecidableEq ι]
    (A B Z : CStarMatrix ι ι ℂ) :
    ((cstarMatrixLeftMul A) * (cstarMatrixRightMul B)) Z = A * Z * B := by
  rw [Module.End.mul_eq_comp]
  simp only [LinearMap.comp_apply, cstarMatrixLeftMul_apply,
    cstarMatrixRightMul_apply]
  exact (mul_assoc A Z B).symm

/-- Applying `R_B L_A` gives the same two-sided product as `L_A R_B`. -/
theorem cstarMatrixRightMul_mul_leftMul_apply
    {ι : Type*} [Fintype ι] [DecidableEq ι]
    (A B Z : CStarMatrix ι ι ℂ) :
    ((cstarMatrixRightMul B) * (cstarMatrixLeftMul A)) Z = A * Z * B := by
  rw [Module.End.mul_eq_comp]
  simp only [LinearMap.comp_apply, cstarMatrixLeftMul_apply,
    cstarMatrixRightMul_apply]

/-- Left and right multiplication commute as endomorphisms. -/
theorem cstarMatrixLeftRightMul_commute
    {ι : Type*} [Fintype ι] [DecidableEq ι]
    (A B : CStarMatrix ι ι ℂ) :
    (cstarMatrixLeftMul A) * (cstarMatrixRightMul B) =
      (cstarMatrixRightMul B) * (cstarMatrixLeftMul A) := by
  apply LinearMap.ext
  intro Z
  rw [cstarMatrixLeftMul_mul_rightMul_apply,
    cstarMatrixRightMul_mul_leftMul_apply]

theorem cstarMatrixLeftMul_unit_inv_mul
    {ι : Type*} [Fintype ι] [DecidableEq ι]
    (u : (CStarMatrix ι ι ℂ)ˣ) :
    cstarMatrixLeftMul ((↑u⁻¹ : CStarMatrix ι ι ℂ)) *
        cstarMatrixLeftMul (u : CStarMatrix ι ι ℂ) = 1 := by
  apply LinearMap.ext
  intro Z
  rw [Module.End.mul_eq_comp]
  simp only [LinearMap.comp_apply, cstarMatrixLeftMul_apply]
  have hinv :
      (↑u⁻¹ : CStarMatrix ι ι ℂ) *
        (u : CStarMatrix ι ι ℂ) = 1 := by
    exact Units.inv_mul u
  calc
    (↑u⁻¹ : CStarMatrix ι ι ℂ) *
        ((u : CStarMatrix ι ι ℂ) * Z) =
        ((↑u⁻¹ : CStarMatrix ι ι ℂ) *
          (u : CStarMatrix ι ι ℂ)) * Z := by
      exact (mul_assoc (↑u⁻¹ : CStarMatrix ι ι ℂ)
        (u : CStarMatrix ι ι ℂ) Z).symm
    _ = 1 * Z := by rw [hinv]
    _ = Z := by exact one_mul Z

theorem cstarMatrixLeftMul_unit_mul_inv
    {ι : Type*} [Fintype ι] [DecidableEq ι]
    (u : (CStarMatrix ι ι ℂ)ˣ) :
    cstarMatrixLeftMul (u : CStarMatrix ι ι ℂ) *
        cstarMatrixLeftMul ((↑u⁻¹ : CStarMatrix ι ι ℂ)) = 1 := by
  apply LinearMap.ext
  intro Z
  rw [Module.End.mul_eq_comp]
  simp only [LinearMap.comp_apply, cstarMatrixLeftMul_apply]
  have hinv :
      (u : CStarMatrix ι ι ℂ) *
        (↑u⁻¹ : CStarMatrix ι ι ℂ) = 1 := by
    exact Units.mul_inv u
  calc
    (u : CStarMatrix ι ι ℂ) *
        ((↑u⁻¹ : CStarMatrix ι ι ℂ) * Z) =
        ((u : CStarMatrix ι ι ℂ) *
          (↑u⁻¹ : CStarMatrix ι ι ℂ)) * Z := by
      exact (mul_assoc (u : CStarMatrix ι ι ℂ)
        (↑u⁻¹ : CStarMatrix ι ι ℂ) Z).symm
    _ = 1 * Z := by rw [hinv]
    _ = Z := by exact one_mul Z

theorem cstarMatrixRightMul_unit_inv_mul
    {ι : Type*} [Fintype ι] [DecidableEq ι]
    (u : (CStarMatrix ι ι ℂ)ˣ) :
    cstarMatrixRightMul ((↑u⁻¹ : CStarMatrix ι ι ℂ)) *
        cstarMatrixRightMul (u : CStarMatrix ι ι ℂ) = 1 := by
  apply LinearMap.ext
  intro Z
  rw [Module.End.mul_eq_comp]
  simp only [LinearMap.comp_apply, cstarMatrixRightMul_apply]
  have hinv :
      (u : CStarMatrix ι ι ℂ) *
        (↑u⁻¹ : CStarMatrix ι ι ℂ) = 1 := by
    exact Units.mul_inv u
  calc
    (Z * (u : CStarMatrix ι ι ℂ)) *
        (↑u⁻¹ : CStarMatrix ι ι ℂ) =
        Z * ((u : CStarMatrix ι ι ℂ) *
          (↑u⁻¹ : CStarMatrix ι ι ℂ)) := by
      exact mul_assoc Z (u : CStarMatrix ι ι ℂ)
        (↑u⁻¹ : CStarMatrix ι ι ℂ)
    _ = Z * 1 := by rw [hinv]
    _ = Z := by exact mul_one Z

theorem cstarMatrixRightMul_unit_mul_inv
    {ι : Type*} [Fintype ι] [DecidableEq ι]
    (u : (CStarMatrix ι ι ℂ)ˣ) :
    cstarMatrixRightMul (u : CStarMatrix ι ι ℂ) *
        cstarMatrixRightMul ((↑u⁻¹ : CStarMatrix ι ι ℂ)) = 1 := by
  apply LinearMap.ext
  intro Z
  rw [Module.End.mul_eq_comp]
  simp only [LinearMap.comp_apply, cstarMatrixRightMul_apply]
  have hinv :
      (↑u⁻¹ : CStarMatrix ι ι ℂ) *
        (u : CStarMatrix ι ι ℂ) = 1 := by
    exact Units.inv_mul u
  calc
    (Z * (↑u⁻¹ : CStarMatrix ι ι ℂ)) *
        (u : CStarMatrix ι ι ℂ) =
        Z * ((↑u⁻¹ : CStarMatrix ι ι ℂ) *
          (u : CStarMatrix ι ι ℂ)) := by
      exact mul_assoc Z (↑u⁻¹ : CStarMatrix ι ι ℂ)
        (u : CStarMatrix ι ι ℂ)
    _ = Z * 1 := by rw [hinv]
    _ = Z := by exact mul_one Z

/-- If `A` is a unit, then left multiplication by `A` is a unit in the
endomorphism ring. -/
theorem cstarMatrixLeftMul_isUnit_of_isUnit
    {ι : Type*} [Fintype ι] [DecidableEq ι]
    {A : CStarMatrix ι ι ℂ} (hA : IsUnit A) :
    IsUnit (cstarMatrixLeftMul A) := by
  rcases hA with ⟨u, rfl⟩
  refine ⟨{ val := cstarMatrixLeftMul (u : CStarMatrix ι ι ℂ)
            inv := cstarMatrixLeftMul ((↑u⁻¹ : CStarMatrix ι ι ℂ))
            val_inv := cstarMatrixLeftMul_unit_mul_inv u
            inv_val := cstarMatrixLeftMul_unit_inv_mul u }, rfl⟩

/-- If `A` is a unit, then right multiplication by `A` is a unit in the
endomorphism ring. -/
theorem cstarMatrixRightMul_isUnit_of_isUnit
    {ι : Type*} [Fintype ι] [DecidableEq ι]
    {A : CStarMatrix ι ι ℂ} (hA : IsUnit A) :
    IsUnit (cstarMatrixRightMul A) := by
  rcases hA with ⟨u, rfl⟩
  refine ⟨{ val := cstarMatrixRightMul (u : CStarMatrix ι ι ℂ)
            inv := cstarMatrixRightMul ((↑u⁻¹ : CStarMatrix ι ι ℂ))
            val_inv := cstarMatrixRightMul_unit_mul_inv u
            inv_val := cstarMatrixRightMul_unit_inv_mul u }, rfl⟩

/-- Strict positivity supplies invertibility of the left-multiplication
operator. -/
theorem cstarMatrixLeftMul_isUnit_of_isStrictlyPositive
    {ι : Type*} [Fintype ι] [DecidableEq ι]
    {A : CStarMatrix ι ι ℂ} (hA : IsStrictlyPositive A) :
    IsUnit (cstarMatrixLeftMul A) :=
  cstarMatrixLeftMul_isUnit_of_isUnit hA.isUnit

/-- Strict positivity supplies invertibility of the right-multiplication
operator. -/
theorem cstarMatrixRightMul_isUnit_of_isStrictlyPositive
    {ι : Type*} [Fintype ι] [DecidableEq ι]
    {A : CStarMatrix ι ι ℂ} (hA : IsStrictlyPositive A) :
    IsUnit (cstarMatrixRightMul A) :=
  cstarMatrixRightMul_isUnit_of_isUnit hA.isUnit

/-- The finite-dimensional ratio endomorphism `L_X R_A^{-1}` used in the
Effros/Tropp perspective route, with `A` supplied as an explicit unit. -/
noncomputable def cstarMatrixLeftRightRatio
    {ι : Type*} [Fintype ι] [DecidableEq ι]
    (X : CStarMatrix ι ι ℂ) (u : (CStarMatrix ι ι ℂ)ˣ) :
    Module.End ℂ (CStarMatrix ι ι ℂ) :=
  cstarMatrixLeftMul X *
    cstarMatrixRightMul ((↑u⁻¹ : CStarMatrix ι ι ℂ))

@[simp]
theorem cstarMatrixLeftRightRatio_apply
    {ι : Type*} [Fintype ι] [DecidableEq ι]
    (X Z : CStarMatrix ι ι ℂ) (u : (CStarMatrix ι ι ℂ)ˣ) :
    cstarMatrixLeftRightRatio X u Z =
      X * Z * (↑u⁻¹ : CStarMatrix ι ι ℂ) := by
  rw [cstarMatrixLeftRightRatio,
    cstarMatrixLeftMul_mul_rightMul_apply]

/-- Applying `L_X R_A^{-1}` to `A` gives `X`.  This is the elementary
normalization behind the finite matrix-perspective representation. -/
theorem cstarMatrixLeftRightRatio_apply_unit
    {ι : Type*} [Fintype ι] [DecidableEq ι]
    (X : CStarMatrix ι ι ℂ) (u : (CStarMatrix ι ι ℂ)ˣ) :
    cstarMatrixLeftRightRatio X u (u : CStarMatrix ι ι ℂ) = X := by
  rw [cstarMatrixLeftRightRatio_apply]
  have hinv :
      (u : CStarMatrix ι ι ℂ) *
        (↑u⁻¹ : CStarMatrix ι ι ℂ) = 1 :=
    Units.mul_inv u
  calc
    X * (u : CStarMatrix ι ι ℂ) *
        (↑u⁻¹ : CStarMatrix ι ι ℂ) =
        X * ((u : CStarMatrix ι ι ℂ) *
          (↑u⁻¹ : CStarMatrix ι ι ℂ)) := by
      exact mul_assoc X (u : CStarMatrix ι ι ℂ)
        (↑u⁻¹ : CStarMatrix ι ι ℂ)
    _ = X * 1 := by rw [hinv]
    _ = X := by exact mul_one X

/-- Variant of `cstarMatrixLeftRightRatio_apply_unit` where the base matrix is
known equal to the supplied unit. -/
theorem cstarMatrixLeftRightRatio_apply_of_unit_eq
    {ι : Type*} [Fintype ι] [DecidableEq ι]
    (X : CStarMatrix ι ι ℂ) (u : (CStarMatrix ι ι ℂ)ˣ)
    {A : CStarMatrix ι ι ℂ} (hA : (u : CStarMatrix ι ι ℂ) = A) :
    cstarMatrixLeftRightRatio X u A = X := by
  rw [← hA]
  exact cstarMatrixLeftRightRatio_apply_unit X u

/-- Strict positivity supplies the unit needed for the ratio map, and the
ratio map sends its base point `A` to the numerator `X`. -/
theorem cstarMatrixLeftRightRatio_apply_of_isStrictlyPositive
    {ι : Type*} [Fintype ι] [DecidableEq ι]
    {X A : CStarMatrix ι ι ℂ} (hA : IsStrictlyPositive A) :
    cstarMatrixLeftRightRatio X hA.isUnit.unit A = X := by
  exact cstarMatrixLeftRightRatio_apply_of_unit_eq X hA.isUnit.unit
    hA.isUnit.unit_spec

/-!
## Conditional relative-entropy route to Lieb concavity

Tropp's monograph route derives Lieb trace concavity from two deeper matrix
relative-entropy facts: a variational formula and joint convexity.  The theorem
below formalizes that reduction in the local vocabulary.  It deliberately keeps
both deeper facts as explicit hypotheses; it does not prove the noncommutative
relative-entropy theorem or Lieb concavity outright.
-/

/-- The variational objective used in the relative-entropy route to Lieb
trace concavity.

The local relative entropy is normalized as
`D(X;A) = Re tr(X * (log X - log A) - (X - A))`.  With this normalization the
Legendre variational formula for `Re tr(exp(H + log A))` contains the extra
constant `Re tr A`. -/
noncomputable def cstarMatrixEntropyVariationalObjective
    {ι : Type*} [Fintype ι] [DecidableEq ι]
    (H X A : CStarMatrix ι ι ℂ) : ℝ :=
  (cstarMatrixTrace (X * H)).re - cstarMatrixRelativeEntropy X A +
    (cstarMatrixTrace A).re

/-- The optimizer candidate `X = exp(H + log A)` attains the value of the
normalized variational objective.

This closes only the equality/attainment algebra in the entropy variational
formula.  It does not prove that this candidate is the global maximizer. -/
theorem cstarMatrixEntropyVariationalObjective_liebOptimizer
    {ι : Type*} [Fintype ι] [DecidableEq ι]
    {H A : CStarMatrix ι ι ℂ} (hH : IsSelfAdjoint H) :
    cstarMatrixEntropyVariationalObjective H
        (cfc (p := IsStarNormal) Complex.exp (H + CFC.log A)) A =
      liebTraceFunctional H A := by
  let X : CStarMatrix ι ι ℂ :=
    cfc (p := IsStarNormal) Complex.exp (H + CFC.log A)
  have hlogX : CFC.log X = H + CFC.log A := by
    dsimp [X]
    exact cstarMatrix_log_cfc_complex_exp_of_isSelfAdjoint
      (H + CFC.log A) (liebTraceArgument_isSelfAdjoint hH)
  have hdiff : CFC.log X - CFC.log A = H := by
    rw [hlogX]
    abel
  dsimp [cstarMatrixEntropyVariationalObjective, cstarMatrixRelativeEntropy,
    liebTraceFunctional, X]
  change (cstarMatrixTrace (X * H)).re -
      (cstarMatrixTrace (X * (CFC.log X - CFC.log A) - (X - A))).re +
        (cstarMatrixTrace A).re =
    (cstarMatrixTrace X).re
  rw [hdiff]
  rw [cstarMatrixTrace_sub, cstarMatrixTrace_sub]
  simp

/-- Joint convexity of local C-star matrix relative entropy on the strictly
positive cone.  This is a named target proposition for the Tropp route, not a
proved theorem in this file. -/
def cstarMatrixRelativeEntropyJointConvexOnStrictPositive
    {ι : Type*} [Fintype ι] [DecidableEq ι] : Prop :=
  ∀ {X Y A B : CStarMatrix ι ι ℂ},
    X ∈ strictPositiveCStarMatrixCone (ι := ι) →
    Y ∈ strictPositiveCStarMatrixCone (ι := ι) →
    A ∈ strictPositiveCStarMatrixCone (ι := ι) →
    B ∈ strictPositiveCStarMatrixCone (ι := ι) →
    ∀ {a b : ℝ}, 0 ≤ a → 0 ≤ b → a + b = 1 →
      cstarMatrixRelativeEntropy (a • X + b • Y) (a • A + b • B) ≤
        a * cstarMatrixRelativeEntropy X A +
          b * cstarMatrixRelativeEntropy Y B

/-- The finite-dimensional superoperator entropy-kernel trace term
\(v_I^* f(L_XR_A^{-1})R_A v_I\), represented concretely by Kronecker
matrices. -/
noncomputable def matrixSuperoperatorEntropyKernelTrace
    {ι : Type*} [Fintype ι] [DecidableEq ι]
    (X A : Matrix ι ι ℂ) : ℝ :=
  (matrixComplexQuadraticForm
    (matrixSelfAdjointCfc realEntropyKernel
      (X ⊗ₖ (A⁻¹).transpose) *
      ((1 : Matrix ι ι ℂ) ⊗ₖ A.transpose))
    (matrixVecId (ι := ι))).re

/-- The scalar trace pairing obtained by applying the ordinary finite matrix
perspective to the product-index left/right superoperator lifts and then
pairing against the vectorized identity.

This is the finite-dimensional Effros perspective object that should later be
identified with `matrixSuperoperatorEntropyKernelTrace`.  Keeping it separate
prevents the library from silently replacing that still-open equality bridge by
an unproved identification. -/
noncomputable def cstarMatrixSuperoperatorPerspectiveTrace
    {ι : Type*} [Fintype ι] [DecidableEq ι]
    (X A : CStarMatrix ι ι ℂ) : ℝ :=
  (matrixComplexQuadraticForm
    (CStarMatrix.ofMatrix.symm
      (cstarMatrixPerspective realEntropyKernel
        (cstarMatrixSuperoperatorLeftLift X)
        (cstarMatrixSuperoperatorRightLift A)) :
      Matrix (ι × ι) (ι × ι) ℂ)
    (matrixVecId (ι := ι))).re

/-- The ordinary product-index perspective trace agrees with the concrete
relative-modular Kronecker trace term used in
`matrixSuperoperatorEntropyKernelTrace`. -/
theorem cstarMatrixSuperoperatorPerspectiveTrace_eq_matrixSuperoperatorEntropyKernelTrace
    {ι : Type*} [Fintype ι] [DecidableEq ι]
    {X A : CStarMatrix ι ι ℂ}
    (hX : X ∈ strictPositiveCStarMatrixCone (ι := ι))
    (hA : A ∈ strictPositiveCStarMatrixCone (ι := ι)) :
    cstarMatrixSuperoperatorPerspectiveTrace X A =
      matrixSuperoperatorEntropyKernelTrace
        (CStarMatrix.ofMatrix.symm X : Matrix ι ι ℂ)
        (CStarMatrix.ofMatrix.symm A : Matrix ι ι ℂ) := by
  classical
  dsimp [strictPositiveCStarMatrixCone] at hX hA
  let Xm : Matrix ι ι ℂ := CStarMatrix.ofMatrix.symm X
  let Am : Matrix ι ι ℂ := CStarMatrix.ofMatrix.symm A
  let Rinv : CStarMatrix (ι × ι) (ι × ι) ℂ :=
    (↑((cstarMatrixSuperoperatorRightLift_isStrictlyPositive hA).isUnit.unit⁻¹) :
      CStarMatrix (ι × ι) (ι × ι) ℂ)
  let Ratio : CStarMatrix (ι × ι) (ι × ι) ℂ :=
    cstarMatrixSuperoperatorLeftLift X * Rinv
  let RatioM : Matrix (ι × ι) (ι × ι) ℂ :=
    Xm ⊗ₖ (Am⁻¹).transpose
  have hXm : Matrix.PosDef Xm := by
    dsimp [Xm]
    exact cstarMatrix_isStrictlyPositive_to_matrix_posDef hX
  have hAm : Matrix.PosDef Am := by
    dsimp [Am]
    exact cstarMatrix_isStrictlyPositive_to_matrix_posDef hA
  have hRatioM_pos : Matrix.PosDef RatioM := by
    dsimp [RatioM, Xm, Am]
    exact matrix_kronecker_inv_transpose_posDef hXm hAm
  have hRatio_matrix :
      (CStarMatrix.ofMatrix.symm Ratio :
        Matrix (ι × ι) (ι × ι) ℂ) = RatioM := by
    change
      ((CStarMatrix.ofMatrix.symm (cstarMatrixSuperoperatorLeftLift X) :
          Matrix (ι × ι) (ι × ι) ℂ) *
        (CStarMatrix.ofMatrix.symm Rinv :
          Matrix (ι × ι) (ι × ι) ℂ)) = RatioM
    rw [cstarMatrixSuperoperatorRightLift_unit_inv_to_matrix hA]
    dsimp [cstarMatrixSuperoperatorLeftLift, Rinv, RatioM, Xm, Am]
    change
      (((CStarMatrix.ofMatrix.symm X : Matrix ι ι ℂ) ⊗ₖ
          (1 : Matrix ι ι ℂ)) *
        ((1 : Matrix ι ι ℂ) ⊗ₖ
          (CStarMatrix.ofMatrix.symm A : Matrix ι ι ℂ)⁻¹.transpose)) =
        (CStarMatrix.ofMatrix.symm X : Matrix ι ι ℂ) ⊗ₖ
          (CStarMatrix.ofMatrix.symm A : Matrix ι ι ℂ)⁻¹.transpose
    exact matrix_kronecker_left_identity_mul_right_identity
      (CStarMatrix.ofMatrix.symm X : Matrix ι ι ℂ)
      (CStarMatrix.ofMatrix.symm A : Matrix ι ι ℂ)⁻¹.transpose
  have hRatio_cstar : Ratio = CStarMatrix.ofMatrix RatioM := by
    apply CStarMatrix.ofMatrix.symm.injective
    simpa using hRatio_matrix
  have hcfc :
      (CStarMatrix.ofMatrix.symm
        (cfc (p := IsSelfAdjoint) realEntropyKernel Ratio) :
        Matrix (ι × ι) (ι × ι) ℂ) =
        matrixSelfAdjointCfc realEntropyKernel RatioM := by
    rw [hRatio_cstar]
    dsimp [matrixSelfAdjointCfc]
    rfl
  have hpersp :=
    cstarMatrixSuperoperatorPerspective_eq_cfc_ratio_mul_rightLift
      X hA
  dsimp [cstarMatrixSuperoperatorPerspectiveTrace]
  rw [hpersp]
  dsimp [Ratio, Rinv] at hcfc
  dsimp [matrixSuperoperatorEntropyKernelTrace, RatioM, Xm, Am]
  change
    (matrixComplexQuadraticForm
        ((CStarMatrix.ofMatrix.symm
            (cfc realEntropyKernel
              (cstarMatrixSuperoperatorLeftLift X *
                (↑((cstarMatrixSuperoperatorRightLift_isStrictlyPositive hA).isUnit.unit⁻¹) :
                  CStarMatrix (ι × ι) (ι × ι) ℂ))) :
            Matrix (ι × ι) (ι × ι) ℂ) *
          (CStarMatrix.ofMatrix.symm (cstarMatrixSuperoperatorRightLift A) :
            Matrix (ι × ι) (ι × ι) ℂ))
        (matrixVecId (ι := ι))).re =
      (matrixComplexQuadraticForm
        (matrixSelfAdjointCfc realEntropyKernel
            ((CStarMatrix.ofMatrix.symm X : Matrix ι ι ℂ) ⊗ₖ
              (CStarMatrix.ofMatrix.symm A : Matrix ι ι ℂ)⁻¹.transpose) *
          ((1 : Matrix ι ι ℂ) ⊗ₖ
            (CStarMatrix.ofMatrix.symm A : Matrix ι ι ℂ).transpose))
        (matrixVecId (ι := ι))).re
  rw [hcfc]
  dsimp [RatioM, Xm, Am]
  simp [cstarMatrixSuperoperatorRightLift]

/-- The product-index superoperator perspective trace is jointly convex on the
strictly positive cone.

This theorem is the scalar extraction of
`cstarMatrixEntropyKernelPerspective_jointConvex` after the left/right
superoperator lifts.  It closes the product-index perspective-convexity
dependency of the Effros route, while the later equality
`cstarMatrixSuperoperatorPerspectiveTrace = matrixSuperoperatorEntropyKernelTrace`
remains a separate bottleneck. -/
theorem cstarMatrixSuperoperatorPerspectiveTrace_jointConvex
    {ι : Type*} [Fintype ι] [DecidableEq ι]
    {X Y A B : CStarMatrix ι ι ℂ}
    (hX : X ∈ strictPositiveCStarMatrixCone (ι := ι))
    (hY : Y ∈ strictPositiveCStarMatrixCone (ι := ι))
    (hA : A ∈ strictPositiveCStarMatrixCone (ι := ι))
    (hB : B ∈ strictPositiveCStarMatrixCone (ι := ι))
    {a b : ℝ} (ha : 0 ≤ a) (hb : 0 ≤ b) (hab : a + b = 1) :
    cstarMatrixSuperoperatorPerspectiveTrace
        (a • X + b • Y) (a • A + b • B) ≤
      a * cstarMatrixSuperoperatorPerspectiveTrace X A +
        b * cstarMatrixSuperoperatorPerspectiveTrace Y B := by
  classical
  dsimp [strictPositiveCStarMatrixCone] at hX hY hA hB
  let LX : CStarMatrix (ι × ι) (ι × ι) ℂ :=
    cstarMatrixSuperoperatorLeftLift X
  let LY : CStarMatrix (ι × ι) (ι × ι) ℂ :=
    cstarMatrixSuperoperatorLeftLift Y
  let RA : CStarMatrix (ι × ι) (ι × ι) ℂ :=
    cstarMatrixSuperoperatorRightLift A
  let RB : CStarMatrix (ι × ι) (ι × ι) ℂ :=
    cstarMatrixSuperoperatorRightLift B
  let PX : CStarMatrix (ι × ι) (ι × ι) ℂ :=
    cstarMatrixPerspective realEntropyKernel LX RA
  let PY : CStarMatrix (ι × ι) (ι × ι) ℂ :=
    cstarMatrixPerspective realEntropyKernel LY RB
  let vI : ι × ι → ℂ := matrixVecId (ι := ι)
  have hpersp :
      cstarMatrixPerspective realEntropyKernel
          (cstarMatrixSuperoperatorLeftLift (a • X + b • Y))
          (cstarMatrixSuperoperatorRightLift (a • A + b • B)) ≤
        a • PX + b • PY := by
    have hbase :
        cstarMatrixPerspective realEntropyKernel
            (a • LX + b • LY) (a • RA + b • RB) ≤
          a • cstarMatrixPerspective realEntropyKernel LX RA +
            b • cstarMatrixPerspective realEntropyKernel LY RB :=
      cstarMatrixEntropyKernelPerspective_jointConvex
        (ι := ι × ι) ha hb hab
        (X := LX) (Y := LY) (A := RA) (B := RB)
        (by
          dsimp [LX]
          exact cstarMatrixSuperoperatorLeftLift_isStrictlyPositive hX)
        (by
          dsimp [LY]
          exact cstarMatrixSuperoperatorLeftLift_isStrictlyPositive hY)
        (by
          dsimp [RA]
          exact cstarMatrixSuperoperatorRightLift_isStrictlyPositive hA)
        (by
          dsimp [RB]
          exact cstarMatrixSuperoperatorRightLift_isStrictlyPositive hB)
    simpa [LX, LY, RA, RB, PX, PY,
      cstarMatrixSuperoperatorLeftLift_real_smul_add,
      cstarMatrixSuperoperatorRightLift_real_smul_add] using hbase
  have hq :=
    matrixComplexQuadraticForm_re_mono_of_cstarMatrix_le hpersp vI
  have hrhs :
      (matrixComplexQuadraticForm
          (CStarMatrix.ofMatrix.symm (a • PX + b • PY) :
            Matrix (ι × ι) (ι × ι) ℂ) vI).re =
        a * (matrixComplexQuadraticForm
          (CStarMatrix.ofMatrix.symm PX :
            Matrix (ι × ι) (ι × ι) ℂ) vI).re +
        b * (matrixComplexQuadraticForm
          (CStarMatrix.ofMatrix.symm PY :
            Matrix (ι × ι) (ι × ι) ℂ) vI).re := by
    have hmat :
        (CStarMatrix.ofMatrix.symm (a • PX + b • PY) :
          Matrix (ι × ι) (ι × ι) ℂ) =
          (a : ℂ) •
              (CStarMatrix.ofMatrix.symm PX :
                Matrix (ι × ι) (ι × ι) ℂ) +
            (b : ℂ) •
              (CStarMatrix.ofMatrix.symm PY :
                Matrix (ι × ι) (ι × ι) ℂ) := by
      ext i j
      simp
    rw [hmat, matrixComplexQuadraticForm_add,
      matrixComplexQuadraticForm_smul, matrixComplexQuadraticForm_smul]
    simp [Complex.mul_re]
  dsimp [cstarMatrixSuperoperatorPerspectiveTrace, LX, LY, RA, RB, PX, PY, vI]
    at hq hrhs ⊢
  rw [hrhs] at hq
  simpa using hq

/-- Equality bridge between the local relative entropy and the ordinary
product-index perspective trace.

This is the next exact Effros-route bottleneck after product-index perspective
joint convexity.  It is intentionally stated as a proposition rather than
silently identified with the already-proved Kronecker trace representation,
because that remaining finite CFC/square-root bridge is not proved yet. -/
def cstarMatrixRelativeEntropyPerspectiveTraceRepresentation
    {ι : Type*} [Fintype ι] [DecidableEq ι] : Prop :=
  ∀ {X A : CStarMatrix ι ι ℂ},
    X ∈ strictPositiveCStarMatrixCone (ι := ι) →
    A ∈ strictPositiveCStarMatrixCone (ι := ι) →
      cstarMatrixRelativeEntropy X A =
        cstarMatrixSuperoperatorPerspectiveTrace X A

/-- Conditional reduction of relative-entropy joint convexity to the exact
finite superoperator perspective-trace representation.

This theorem does not close joint convexity by itself.  It records that, after
`cstarMatrixSuperoperatorPerspectiveTrace_jointConvex`, the only remaining
Effros-route equality is
`cstarMatrixRelativeEntropyPerspectiveTraceRepresentation`. -/
theorem cstarMatrixRelativeEntropyJointConvexOnStrictPositive_of_perspectiveTraceRepresentation
    {ι : Type*} [Fintype ι] [DecidableEq ι]
    (hrepr :
      cstarMatrixRelativeEntropyPerspectiveTraceRepresentation (ι := ι)) :
    cstarMatrixRelativeEntropyJointConvexOnStrictPositive (ι := ι) := by
  intro X Y A B hX hY hA hB a b ha hb hab
  have hmixX :
      a • X + b • Y ∈ strictPositiveCStarMatrixCone (ι := ι) :=
    strictPositiveCStarMatrixCone_convex hX hY ha hb hab
  have hmixA :
      a • A + b • B ∈ strictPositiveCStarMatrixCone (ι := ι) :=
    strictPositiveCStarMatrixCone_convex hA hB ha hb hab
  have hconv :=
    cstarMatrixSuperoperatorPerspectiveTrace_jointConvex
      hX hY hA hB ha hb hab
  rw [hrepr hmixX hmixA, hrepr hX hA, hrepr hY hB]
  exact hconv

/-- The remaining finite-matrix superoperator overlap expansion needed for
the Umegaki trace-representation route. -/
def matrixSuperoperatorEntropyKernelOverlapExpansion
    {ι : Type*} [Fintype ι] [DecidableEq ι] : Prop :=
  ∀ {X A : Matrix ι ι ℂ},
    (hX : Matrix.PosDef X) → (hA : Matrix.PosDef A) →
      matrixSuperoperatorEntropyKernelTrace X A =
        ∑ j : ι, ∑ k : ι,
          realRelativeEntropy (hX.isHermitian.eigenvalues j)
              (hA.isHermitian.eigenvalues k) *
            Complex.normSq
              (((star (hX.isHermitian.eigenvectorUnitary :
                  Matrix ι ι ℂ)) *
                (hA.isHermitian.eigenvectorUnitary :
                  Matrix ι ι ℂ)) j k)

/-- The superoperator entropy-kernel trace term has the same finite
eigenbasis-overlap expansion as the compact Umegaki relative-entropy trace,
in every nonempty finite dimension. -/
theorem matrixSuperoperatorEntropyKernelOverlapExpansion_of_nonempty
    {ι : Type*} [Fintype ι] [DecidableEq ι] [Nonempty ι] :
    matrixSuperoperatorEntropyKernelOverlapExpansion (ι := ι) := by
  intro X A hX hA
  rcases
      exists_realPolynomial_tendsto_superoperator_entropyKernel_trace_and_overlap_of_posDef
        X A hX hA with
    ⟨p, htrace, hoverlap⟩
  let traceSeq : ℕ → ℂ := fun n =>
    ∑ k ∈ ((p n).map (algebraMap ℝ ℂ)).support,
      ((p n).map (algebraMap ℝ ℂ)).coeff k *
        Matrix.trace (X ^ k * A * (A⁻¹) ^ k)
  let overlapSeq : ℕ → ℝ := fun n =>
    ∑ j : ι, ∑ k : ι,
      (hA.isHermitian.eigenvalues k *
        Polynomial.eval
          (hX.isHermitian.eigenvalues j *
            (hA.isHermitian.eigenvalues k)⁻¹) (p n)) *
        Complex.normSq
          (((star (hX.isHermitian.eigenvectorUnitary :
              Matrix ι ι ℂ)) *
            (hA.isHermitian.eigenvectorUnitary :
              Matrix ι ι ℂ)) j k)
  have hpoly : ∀ n : ℕ, (traceSeq n).re = overlapSeq n := by
    intro n
    dsimp [traceSeq, overlapSeq]
    exact matrixPolynomialTraceRatio_re_eq_sum hX hA (p n)
  have htraceRe :
      Filter.Tendsto (fun n => (traceSeq n).re) Filter.atTop
        (nhds (matrixSuperoperatorEntropyKernelTrace X A)) := by
    have h :=
      (Complex.continuous_re.tendsto
        (matrixComplexQuadraticForm
          (matrixSelfAdjointCfc realEntropyKernel
            (X ⊗ₖ (A⁻¹).transpose) *
            ((1 : Matrix ι ι ℂ) ⊗ₖ A.transpose))
          (matrixVecId (ι := ι)))).comp htrace
    change
      Filter.Tendsto (fun n => (traceSeq n).re) Filter.atTop
        (nhds
          (matrixComplexQuadraticForm
            (matrixSelfAdjointCfc realEntropyKernel
              (X ⊗ₖ (A⁻¹).transpose) *
              ((1 : Matrix ι ι ℂ) ⊗ₖ A.transpose))
            (matrixVecId (ι := ι))).re) at h
    simpa [matrixSuperoperatorEntropyKernelTrace] using h
  have htraceOverlap :
      Filter.Tendsto overlapSeq Filter.atTop
        (nhds (matrixSuperoperatorEntropyKernelTrace X A)) :=
    htraceRe.congr' (Filter.Eventually.of_forall hpoly)
  have hoverlap' :
      Filter.Tendsto overlapSeq Filter.atTop
        (nhds
          (∑ j : ι, ∑ k : ι,
            realRelativeEntropy (hX.isHermitian.eigenvalues j)
                (hA.isHermitian.eigenvalues k) *
              Complex.normSq
                (((star (hX.isHermitian.eigenvectorUnitary :
                    Matrix ι ι ℂ)) *
                  (hA.isHermitian.eigenvectorUnitary :
                    Matrix ι ι ℂ)) j k))) := by
    simpa [overlapSeq] using hoverlap
  exact tendsto_nhds_unique htraceOverlap hoverlap'

/-- Empty finite dimensions satisfy the superoperator overlap expansion
vacuously: both the trace pairing and the finite overlap sum are zero. -/
theorem matrixSuperoperatorEntropyKernelOverlapExpansion_of_isEmpty
    {ι : Type*} [Fintype ι] [DecidableEq ι] [IsEmpty ι] :
    matrixSuperoperatorEntropyKernelOverlapExpansion (ι := ι) := by
  intro X A hX hA
  simp [matrixSuperoperatorEntropyKernelTrace, matrixComplexQuadraticForm,
    matrixVecId]

/-- The finite-dimensional superoperator entropy-kernel trace term has the
source-faithful spectral-overlap expansion in all finite dimensions. -/
theorem matrixSuperoperatorEntropyKernelOverlapExpansion_all
    {ι : Type*} [Fintype ι] [DecidableEq ι] :
    matrixSuperoperatorEntropyKernelOverlapExpansion (ι := ι) := by
  cases isEmpty_or_nonempty ι with
  | inl h =>
      letI : IsEmpty ι := h
      intro X A hX hA
      exact matrixSuperoperatorEntropyKernelOverlapExpansion_of_isEmpty
        (ι := ι) hX hA
  | inr h =>
      letI : Nonempty ι := h
      intro X A hX hA
      exact matrixSuperoperatorEntropyKernelOverlapExpansion_of_nonempty
        (ι := ι) hX hA

/-- If the superoperator entropy-kernel term has the same spectral-overlap
expansion as the compact relative-entropy trace, then the two finite-matrix
representations agree.  This is a conditional bottleneck adapter; it does not
prove the superoperator overlap expansion. -/
theorem matrixRelativeEntropyTraceRepresentation_of_superoperator_overlap
    {ι : Type*} [Fintype ι] [DecidableEq ι]
    (hoverlap : matrixSuperoperatorEntropyKernelOverlapExpansion (ι := ι)) :
    ∀ {X A : Matrix ι ι ℂ}, (hX : Matrix.PosDef X) → (hA : Matrix.PosDef A) →
      (Matrix.trace
        (X * hX.isHermitian.cfc Real.log -
          X * hA.isHermitian.cfc Real.log - (X - A))).re =
        matrixSuperoperatorEntropyKernelTrace X A := by
  intro X A hX hA
  have hcompact :=
    matrixTrace_hermitianCfc_relativeEntropy_re_eq_sum
      hX.isHermitian hA.isHermitian
  have hsuper := hoverlap hX hA
  rw [hcompact, hsuper]

/-- Source-faithful superoperator trace representation needed by the
Effros/Tropp route to local matrix relative-entropy joint convexity.

This is deliberately a named bottleneck proposition: it is not assumed by any
paper-level theorem marked closed.  It states the intended finite-dimensional
Umegaki representation through the relative modular operator
`L_X R_A^{-1}`, represented concretely as the Kronecker matrix
`X ⊗ (A⁻¹).transpose` paired against the vectorized identity. -/
def cstarMatrixRelativeEntropyTraceRepresentationBySuperoperator
    {ι : Type*} [Fintype ι] [DecidableEq ι] : Prop :=
  ∀ {X A : CStarMatrix ι ι ℂ},
    X ∈ strictPositiveCStarMatrixCone (ι := ι) →
    A ∈ strictPositiveCStarMatrixCone (ι := ι) →
      let Xm : Matrix ι ι ℂ := CStarMatrix.ofMatrix.symm X
      let Am : Matrix ι ι ℂ := CStarMatrix.ofMatrix.symm A
      cstarMatrixRelativeEntropy X A =
        matrixSuperoperatorEntropyKernelTrace Xm Am

/-- Source-faithful finite-dimensional Umegaki trace representation through
the relative modular superoperator `L_X R_A^{-1}`.

This closes the concrete trace-representation dependency in the Effros/Tropp
route: the local `CStarMatrix` relative entropy agrees with the Kronecker
superoperator entropy-kernel trace term used above. -/
theorem cstarMatrixRelativeEntropyTraceRepresentationBySuperoperator_all
    {ι : Type*} [Fintype ι] [DecidableEq ι] :
    cstarMatrixRelativeEntropyTraceRepresentationBySuperoperator (ι := ι) := by
  intro X A hX hA
  dsimp [strictPositiveCStarMatrixCone] at hX hA
  let Xm : Matrix ι ι ℂ := CStarMatrix.ofMatrix.symm X
  let Am : Matrix ι ι ℂ := CStarMatrix.ofMatrix.symm A
  have hXm : Matrix.PosDef Xm := by
    dsimp [Xm]
    exact cstarMatrix_isStrictlyPositive_to_matrix_posDef hX
  have hAm : Matrix.PosDef Am := by
    dsimp [Am]
    exact cstarMatrix_isStrictlyPositive_to_matrix_posDef hA
  have hrepr :=
    matrixRelativeEntropyTraceRepresentation_of_superoperator_overlap
      (ι := ι) matrixSuperoperatorEntropyKernelOverlapExpansion_all hXm hAm
  have hlogX :
      CFC.log X = CStarMatrix.ofMatrix (hXm.isHermitian.cfc Real.log) := by
    change cfc Real.log X = hXm.isHermitian.cfc Real.log
    dsimp [Xm]
    exact hXm.isHermitian.cfc_eq Real.log
  have hlogA :
      CFC.log A = CStarMatrix.ofMatrix (hAm.isHermitian.cfc Real.log) := by
    change cfc Real.log A = hAm.isHermitian.cfc Real.log
    dsimp [Am]
    exact hAm.isHermitian.cfc_eq Real.log
  have hinner :
      X * (CFC.log X - CFC.log A) - (X - A) =
        X * CFC.log X - X * CFC.log A - (X - A) := by
    ext i j
    simp [CStarMatrix.mul_apply, Finset.sum_add_distrib, sub_eq_add_neg,
      mul_add]
  dsimp [cstarMatrixRelativeEntropy]
  rw [hinner, hlogX, hlogA]
  simpa [cstarMatrixTrace, Matrix.trace, Xm, Am] using hrepr

/-- The local relative entropy also agrees with the ordinary product-index
perspective trace.  This closes the equality bridge between the
Effros-product-perspective convexity theorem and the source-faithful
relative-modular trace representation. -/
theorem cstarMatrixRelativeEntropyPerspectiveTraceRepresentation_all
    {ι : Type*} [Fintype ι] [DecidableEq ι] :
    cstarMatrixRelativeEntropyPerspectiveTraceRepresentation (ι := ι) := by
  intro X A hX hA
  have hsuper :=
    cstarMatrixRelativeEntropyTraceRepresentationBySuperoperator_all
      (ι := ι) hX hA
  have hpersp :=
    cstarMatrixSuperoperatorPerspectiveTrace_eq_matrixSuperoperatorEntropyKernelTrace
      hX hA
  exact hsuper.trans hpersp.symm

/-- Finite-dimensional local C-star matrix relative entropy is jointly convex
on the strictly positive cone. -/
theorem cstarMatrixRelativeEntropyJointConvexOnStrictPositive_all
    {ι : Type*} [Fintype ι] [DecidableEq ι] :
    cstarMatrixRelativeEntropyJointConvexOnStrictPositive (ι := ι) :=
  cstarMatrixRelativeEntropyJointConvexOnStrictPositive_of_perspectiveTraceRepresentation
    cstarMatrixRelativeEntropyPerspectiveTraceRepresentation_all

/-- Nonnegativity of local C-star matrix relative entropy on the strictly
positive cone.  This is the Klein-inequality-type foundation needed for the
maximality half of the entropy variational formula. -/
def cstarMatrixRelativeEntropyNonnegOnStrictPositive
    {ι : Type*} [Fintype ι] [DecidableEq ι] : Prop :=
  ∀ {X A : CStarMatrix ι ι ℂ},
    X ∈ strictPositiveCStarMatrixCone (ι := ι) →
    A ∈ strictPositiveCStarMatrixCone (ι := ι) →
      0 ≤ cstarMatrixRelativeEntropy X A

/-- Generalized Klein first-order trace inequality for the local entropy trace
functional.

For the matrix entropy `Phi(X) = Re tr(X log X - X)`, this states that
`Phi` lies above its first-order affine approximation at `A` on the strictly
positive cone:

`Phi(A) + Re tr((log A) * (X - A)) <= Phi(X)`.

Tropp's matrix-concentration notes prove matrix-relative-entropy
nonnegativity from this inequality.  This is a named target proposition, not a
proved theorem in this file. -/
def cstarMatrixEntropyTraceFirstOrderConvexityOnStrictPositive
    {ι : Type*} [Fintype ι] [DecidableEq ι] : Prop :=
  ∀ {X A : CStarMatrix ι ι ℂ},
    X ∈ strictPositiveCStarMatrixCone (ι := ι) →
    A ∈ strictPositiveCStarMatrixCone (ι := ι) →
      (cstarMatrixTrace
        (A * CFC.log A - A + CFC.log A * (X - A))).re ≤
        (cstarMatrixTrace (X * CFC.log X - X)).re

/-- The generalized Klein first-order trace inequality implies
nonnegativity of local C-star matrix relative entropy on the strictly positive
cone.

This closes a source-aligned reduction: the remaining analytic task for
nonnegativity is the first-order trace inequality itself, not an implicit
assumption of relative-entropy nonnegativity. -/
theorem cstarMatrixRelativeEntropyNonnegOnStrictPositive_of_entropyTraceFirstOrder
    {ι : Type*} [Fintype ι] [DecidableEq ι]
    (hKlein :
      cstarMatrixEntropyTraceFirstOrderConvexityOnStrictPositive (ι := ι)) :
    cstarMatrixRelativeEntropyNonnegOnStrictPositive (ι := ι) := by
  intro X A hX hA
  have hineq := hKlein hX hA
  dsimp [cstarMatrixRelativeEntropy]
  have htrace :
      cstarMatrixTrace
          (A * CFC.log A - A + CFC.log A * (X - A)) =
        cstarMatrixTrace (X * CFC.log A - A) := by
    rw [cstarMatrixTrace_add]
    rw [cstarMatrixTrace_sub]
    rw [cstarMatrixTrace_mul_comm (CFC.log A) (X - A)]
    have hmulsub :
        (X - A) * CFC.log A = X * CFC.log A - A * CFC.log A := by
      ext i j
      simp [CStarMatrix.mul_apply, Finset.sum_add_distrib, sub_eq_add_neg,
        add_mul]
    rw [hmulsub, cstarMatrixTrace_sub]
    repeat rw [cstarMatrixTrace_sub]
    rw [cstarMatrixTrace_mul_comm X (CFC.log A)]
    abel
  rw [htrace] at hineq
  have hD :
      (cstarMatrixTrace
        (X * (CFC.log X - CFC.log A) - (X - A))).re =
        (cstarMatrixTrace (X * CFC.log X - X)).re -
          (cstarMatrixTrace (X * CFC.log A - A)).re := by
    have hinner :
        X * (CFC.log X - CFC.log A) - (X - A) =
          (X * CFC.log X - X) - (X * CFC.log A - A) := by
      ext i j
      simp [CStarMatrix.mul_apply, Finset.sum_add_distrib, sub_eq_add_neg,
        mul_add]
      abel
    rw [hinner, cstarMatrixTrace_sub]
    simp
  rw [hD]
  linarith

/-- Nonnegativity of local C-star matrix relative entropy implies the
generalized Klein first-order trace inequality for the local entropy trace
functional.

Together with
`cstarMatrixRelativeEntropyNonnegOnStrictPositive_of_entropyTraceFirstOrder`,
this shows that, under the repository's normalization, the two bottleneck
statements are algebraically equivalent.  Proving the first-order trace
inequality is therefore not a smaller downstream task; it is the same
noncommutative entropy foundation in first-order convexity form. -/
theorem cstarMatrixEntropyTraceFirstOrderConvexityOnStrictPositive_of_relativeEntropy_nonneg
    {ι : Type*} [Fintype ι] [DecidableEq ι]
    (hnonneg :
      cstarMatrixRelativeEntropyNonnegOnStrictPositive (ι := ι)) :
    cstarMatrixEntropyTraceFirstOrderConvexityOnStrictPositive (ι := ι) := by
  intro X A hX hA
  have hDnonneg := hnonneg hX hA
  have htrace :
      cstarMatrixTrace
          (A * CFC.log A - A + CFC.log A * (X - A)) =
        cstarMatrixTrace (X * CFC.log A - A) := by
    rw [cstarMatrixTrace_add]
    rw [cstarMatrixTrace_sub]
    rw [cstarMatrixTrace_mul_comm (CFC.log A) (X - A)]
    have hmulsub :
        (X - A) * CFC.log A = X * CFC.log A - A * CFC.log A := by
      ext i j
      simp [CStarMatrix.mul_apply, Finset.sum_add_distrib, sub_eq_add_neg,
        add_mul]
    rw [hmulsub, cstarMatrixTrace_sub]
    repeat rw [cstarMatrixTrace_sub]
    rw [cstarMatrixTrace_mul_comm X (CFC.log A)]
    abel
  have hD :
      (cstarMatrixTrace
        (X * (CFC.log X - CFC.log A) - (X - A))).re =
        (cstarMatrixTrace (X * CFC.log X - X)).re -
          (cstarMatrixTrace (X * CFC.log A - A)).re := by
    have hinner :
        X * (CFC.log X - CFC.log A) - (X - A) =
          (X * CFC.log X - X) - (X * CFC.log A - A) := by
      ext i j
      simp [CStarMatrix.mul_apply, Finset.sum_add_distrib, sub_eq_add_neg,
        mul_add]
      abel
    rw [hinner, cstarMatrixTrace_sub]
    simp
  dsimp [cstarMatrixRelativeEntropy] at hDnonneg
  rw [hD] at hDnonneg
  rw [htrace]
  linarith

/-- In the local finite C-star matrix vocabulary, generalized Klein's
first-order trace inequality is equivalent to nonnegativity of the normalized
matrix relative entropy.

This is a bottleneck clarification theorem: it does not prove either side, but
it pins down that the two source formulations carry exactly the same remaining
noncommutative content in this formalization. -/
theorem cstarMatrixEntropyTraceFirstOrderConvexityOnStrictPositive_iff_relativeEntropy_nonneg
    {ι : Type*} [Fintype ι] [DecidableEq ι] :
    cstarMatrixEntropyTraceFirstOrderConvexityOnStrictPositive (ι := ι) ↔
      cstarMatrixRelativeEntropyNonnegOnStrictPositive (ι := ι) := by
  constructor
  · exact cstarMatrixRelativeEntropyNonnegOnStrictPositive_of_entropyTraceFirstOrder
  · exact cstarMatrixEntropyTraceFirstOrderConvexityOnStrictPositive_of_relativeEntropy_nonneg

/-- Generalized Klein first-order trace inequality on the strictly positive
finite complex `CStarMatrix` cone.

This closes the noncommutative entropy nonnegativity foundation on the chosen
Tropp route: it translates strict positivity to positive Hermitian spectra,
uses the Hermitian compact entropy-kernel theorem, and then translates the
operator logarithms back to the local `CStarMatrix` vocabulary. -/
theorem cstarMatrixEntropyTraceFirstOrderConvexityOnStrictPositive_of_hermitianCfc
    {ι : Type*} [Fintype ι] [DecidableEq ι] :
    cstarMatrixEntropyTraceFirstOrderConvexityOnStrictPositive (ι := ι) := by
  intro X A hX hA
  dsimp [strictPositiveCStarMatrixCone] at hX hA
  have hXsa : IsSelfAdjoint X := IsSelfAdjoint.of_nonneg hX.nonneg
  have hAsa : IsSelfAdjoint A := IsSelfAdjoint.of_nonneg hA.nonneg
  have hXherm : Matrix.IsHermitian X :=
    Matrix.isHermitian_iff_isSelfAdjoint.mpr hXsa
  have hAherm : Matrix.IsHermitian A :=
    Matrix.isHermitian_iff_isSelfAdjoint.mpr hAsa
  have hXpos : ∀ j : ι, 0 < hXherm.eigenvalues j := by
    intro j
    have hposDef : Matrix.PosDef X :=
      cstarMatrix_isStrictlyPositive_to_matrix_posDef hX
    exact hposDef.eigenvalues_pos j
  have hApos : ∀ j : ι, 0 < hAherm.eigenvalues j := by
    intro j
    have hposDef : Matrix.PosDef A :=
      cstarMatrix_isStrictlyPositive_to_matrix_posDef hA
    exact hposDef.eigenvalues_pos j
  have hlogX :
      CFC.log X = CStarMatrix.ofMatrix (hXherm.cfc Real.log) := by
    change cfc Real.log X = hXherm.cfc Real.log
    exact hXherm.cfc_eq Real.log
  have hlogA :
      CFC.log A = CStarMatrix.ofMatrix (hAherm.cfc Real.log) := by
    change cfc Real.log A = hAherm.cfc Real.log
    exact hAherm.cfc_eq Real.log
  have hcompact :=
    matrixTrace_hermitianCfc_entropy_firstOrder_compact_nonneg
      hXherm hAherm hXpos hApos
  rw [hlogX, hlogA]
  simpa [cstarMatrixTrace, Matrix.trace] using hcompact

/-- Nonnegativity of local finite-dimensional C-star matrix relative entropy
on the strictly positive cone. -/
theorem cstarMatrixRelativeEntropyNonnegOnStrictPositive_of_hermitianCfc
    {ι : Type*} [Fintype ι] [DecidableEq ι] :
    cstarMatrixRelativeEntropyNonnegOnStrictPositive (ι := ι) :=
  cstarMatrixRelativeEntropyNonnegOnStrictPositive_of_entropyTraceFirstOrder
    cstarMatrixEntropyTraceFirstOrderConvexityOnStrictPositive_of_hermitianCfc

/-- Normalized variational formula for the local Lieb trace functional.
This proposition packages the exact optimizer and domination statement needed
to derive Lieb concavity from joint convexity of matrix relative entropy.  The
optimizer equality is already proved by
`cstarMatrixEntropyVariationalObjective_liebOptimizer`; the global domination
part remains a target foundation, not a theorem proved here. -/
def cstarMatrixEntropyVariationalFormula
    {ι : Type*} [Fintype ι] [DecidableEq ι]
    (H : CStarMatrix ι ι ℂ) : Prop :=
  ∀ A : CStarMatrix ι ι ℂ,
    A ∈ strictPositiveCStarMatrixCone (ι := ι) →
      ∃ X : CStarMatrix ι ι ℂ,
        X ∈ strictPositiveCStarMatrixCone (ι := ι) ∧
        cstarMatrixEntropyVariationalObjective H X A =
          liebTraceFunctional H A ∧
        ∀ Y : CStarMatrix ι ι ℂ,
          Y ∈ strictPositiveCStarMatrixCone (ι := ι) →
            cstarMatrixEntropyVariationalObjective H Y A ≤
              liebTraceFunctional H A

/-- The normalized entropy variational formula follows from nonnegativity of
matrix relative entropy on the strictly positive cone.

This theorem closes the algebraic reduction of the variational formula to the
Klein-inequality-type nonnegativity foundation.  It does not prove that
nonnegativity foundation. -/
theorem cstarMatrixEntropyVariationalFormula_of_relativeEntropy_nonneg
    {ι : Type*} [Fintype ι] [DecidableEq ι]
    {H : CStarMatrix ι ι ℂ} (hH : IsSelfAdjoint H)
    (hnonneg : cstarMatrixRelativeEntropyNonnegOnStrictPositive (ι := ι)) :
    cstarMatrixEntropyVariationalFormula H := by
  intro A hA
  let X : CStarMatrix ι ι ℂ :=
    cfc (p := IsStarNormal) Complex.exp (H + CFC.log A)
  have hX : X ∈ strictPositiveCStarMatrixCone (ι := ι) := by
    dsimp [X, strictPositiveCStarMatrixCone]
    exact liebTraceCfcExp_isStrictlyPositive (A := A) hH
  refine ⟨X, hX, ?_, ?_⟩
  · dsimp [X]
    exact cstarMatrixEntropyVariationalObjective_liebOptimizer (A := A) hH
  · intro Y hY
    have hlogX : CFC.log X = H + CFC.log A := by
      dsimp [X]
      exact cstarMatrix_log_cfc_complex_exp_of_isSelfAdjoint
        (H + CFC.log A) (liebTraceArgument_isSelfAdjoint hH)
    have hmul :
        Y * (CFC.log Y - CFC.log X) =
          Y * (CFC.log Y - CFC.log A) - Y * H := by
      rw [hlogX]
      ext i j
      simp [CStarMatrix.mul_apply, Finset.sum_add_distrib, sub_eq_add_neg,
        mul_add, add_assoc, add_comm]
    have hobj :
        cstarMatrixEntropyVariationalObjective H Y A =
          liebTraceFunctional H A - cstarMatrixRelativeEntropy Y X := by
      dsimp [cstarMatrixEntropyVariationalObjective, cstarMatrixRelativeEntropy,
        liebTraceFunctional, X]
      change (cstarMatrixTrace (Y * H)).re -
          (cstarMatrixTrace
            (Y * (CFC.log Y - CFC.log A) - (Y - A))).re +
            (cstarMatrixTrace A).re =
        (cstarMatrixTrace X).re -
          (cstarMatrixTrace
            (Y * (CFC.log Y - CFC.log X) - (Y - X))).re
      rw [hmul]
      repeat rw [cstarMatrixTrace_sub]
      simp
      ring
    rw [hobj]
    have hD : 0 ≤ cstarMatrixRelativeEntropy Y X := hnonneg hY hX
    linarith

/-- The normalized entropy variational formula in the local finite-dimensional
C-star matrix vocabulary.

This is now unconditional apart from the source-domain hypothesis that `H` is
self-adjoint, because local relative-entropy nonnegativity has been proved by
the Hermitian CFC generalized-Klein theorem above. -/
theorem cstarMatrixEntropyVariationalFormula_of_hermitianCfc
    {ι : Type*} [Fintype ι] [DecidableEq ι]
    {H : CStarMatrix ι ι ℂ} (hH : IsSelfAdjoint H) :
    cstarMatrixEntropyVariationalFormula H :=
  cstarMatrixEntropyVariationalFormula_of_relativeEntropy_nonneg hH
    cstarMatrixRelativeEntropyNonnegOnStrictPositive_of_hermitianCfc

/-- Conditional reduction from the relative-entropy route to the local Lieb
trace-concavity target.

If the local matrix relative entropy is jointly convex on the strictly positive
cone and the usual entropy variational formula holds for the fixed matrix `H`,
then `A ↦ Re tr(exp(H + log A))` is concave on that cone.  The hypotheses are
the exact remaining noncommutative foundations in this route; no concentration
or Lieb theorem is assumed implicitly. -/
theorem liebTraceConcavityTarget_of_relativeEntropy_route
    {ι : Type*} [Fintype ι] [DecidableEq ι]
    {H : CStarMatrix ι ι ℂ} (_hH : IsSelfAdjoint H)
    (hjoint : cstarMatrixRelativeEntropyJointConvexOnStrictPositive (ι := ι))
    (hvar : cstarMatrixEntropyVariationalFormula H) :
    liebTraceConcavityTarget H := by
  constructor
  · exact strictPositiveCStarMatrixCone_convex (ι := ι)
  · intro A hA B hB a b ha hb hab
    rcases hvar A hA with ⟨X, hX, hXA, _hupperA⟩
    rcases hvar B hB with ⟨Y, hY, hYB, _hupperB⟩
    have hmixX : a • X + b • Y ∈ strictPositiveCStarMatrixCone (ι := ι) := by
      exact (strictPositiveCStarMatrixCone_convex (ι := ι)) hX hY ha hb hab
    have hmixA : a • A + b • B ∈ strictPositiveCStarMatrixCone (ι := ι) := by
      exact (strictPositiveCStarMatrixCone_convex (ι := ι)) hA hB ha hb hab
    rcases hvar (a • A + b • B) hmixA with ⟨_Z, _hZ, _hZeq, hupperMix⟩
    have hD := hjoint (X := X) (Y := Y) (A := A) (B := B)
      hX hY hA hB ha hb hab
    have htrace :
        (cstarMatrixTrace ((a • X + b • Y) * H)).re =
          a * (cstarMatrixTrace (X * H)).re +
            b * (cstarMatrixTrace (Y * H)).re := by
      have hmul :
          ((a • X + b • Y) * H : CStarMatrix ι ι ℂ) =
            (a : ℂ) • (X * H) + (b : ℂ) • (Y * H) := by
        ext i j
        simp [CStarMatrix.mul_apply, Finset.sum_add_distrib, Finset.mul_sum,
          add_mul, mul_assoc]
      rw [hmul, cstarMatrixTrace_add, cstarMatrixTrace_smul,
        cstarMatrixTrace_smul]
      simp
    have htraceA :
        (cstarMatrixTrace (a • A + b • B)).re =
          a * (cstarMatrixTrace A).re +
            b * (cstarMatrixTrace B).re := by
      have ha :
          cstarMatrixTrace (a • A) =
            (a : ℂ) * cstarMatrixTrace A := by
        simpa using cstarMatrixTrace_smul (a := (a : ℂ)) A
      have hb :
          cstarMatrixTrace (b • B) =
            (b : ℂ) * cstarMatrixTrace B := by
        simpa using cstarMatrixTrace_smul (a := (b : ℂ)) B
      rw [cstarMatrixTrace_add, ha, hb]
      simp
    have hobj :
        a * liebTraceFunctional H A + b * liebTraceFunctional H B ≤
          cstarMatrixEntropyVariationalObjective H
            (a • X + b • Y) (a • A + b • B) := by
      rw [← hXA, ← hYB]
      dsimp [cstarMatrixEntropyVariationalObjective]
      linarith
    exact hobj.trans (hupperMix (a • X + b • Y) hmixX)

/-- The remaining conditional route to finite-dimensional Lieb trace
concavity after closing generalized Klein and the variational formula.

The only explicit noncommutative foundation still assumed here is joint
convexity of the local finite-dimensional C-star matrix relative entropy on
the strictly positive cone. -/
theorem liebTraceConcavityTarget_of_relativeEntropy_jointConvex
    {ι : Type*} [Fintype ι] [DecidableEq ι]
    {H : CStarMatrix ι ι ℂ} (hH : IsSelfAdjoint H)
    (hjoint : cstarMatrixRelativeEntropyJointConvexOnStrictPositive (ι := ι)) :
    liebTraceConcavityTarget H :=
  liebTraceConcavityTarget_of_relativeEntropy_route hH hjoint
    (cstarMatrixEntropyVariationalFormula_of_hermitianCfc hH)

/-- Finite-dimensional Lieb trace concavity for the local C-star matrix model.

This is the concentration-facing form: the relative-entropy joint-convexity
foundation has been discharged by the finite-dimensional Effros perspective
route, so only the source-faithful self-adjointness hypothesis on `H` remains. -/
theorem liebTraceConcavityTarget_all
    {ι : Type*} [Fintype ι] [DecidableEq ι]
    {H : CStarMatrix ι ι ℂ} (hH : IsSelfAdjoint H) :
    liebTraceConcavityTarget H :=
  liebTraceConcavityTarget_of_relativeEntropy_jointConvex hH
    (cstarMatrixRelativeEntropyJointConvexOnStrictPositive_all (ι := ι))

/-- One-step Tropp trace-MGF domination in finite dimensions.

This is the concentration-facing form obtained by combining finite-dimensional
Lieb trace concavity with the finite-probability Jensen adapter.  It no longer
assumes the Lieb concavity theorem as a hidden hypothesis. -/
theorem FiniteProbability.expectationReal_trace_normed_exp_add_le
    {Ω : Type*} [Fintype Ω]
    {ι : Type*} [Fintype ι] [DecidableEq ι]
    (P : FiniteProbability Ω)
    {H : CStarMatrix ι ι ℂ} (hH : IsSelfAdjoint H)
    {X : Ω → CStarMatrix ι ι ℂ} (hX : ∀ ω, IsSelfAdjoint (X ω)) :
    P.expectationReal
      (fun ω => (cstarMatrixTrace (NormedSpace.exp (H + X ω))).re) ≤
    (cstarMatrixTrace
      (NormedSpace.exp
        (H + CFC.log (P.expectationCStarMatrix
          (fun ω => NormedSpace.exp (X ω)))))).re :=
  P.expectationReal_trace_normed_exp_add_le_of_liebTraceConcavityTarget
    hH hX (liebTraceConcavityTarget_all hH)

end NumStability
