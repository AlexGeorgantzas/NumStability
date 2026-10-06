-- Analysis/Problem2_25.lean
--
-- Problem-specific theorem surface for Higham Chapter 2, Problem 2.25.

import NumStability.Analysis.CramersRule
import NumStability.Analysis.FusedMultiplyAdd

namespace NumStability

noncomputable section

/-!
# Higham Chapter 2, Problem 2.25

Problem 2.25 asks for Kahan's FMA determinant computation

```text
w = b*c
e = w - b*c
x = (a*d - w) + e
```

for `det [[a,b],[c,d]] = a*d - b*c`.  This module records the exact algebraic
core and the finite round-to-even theorem obtained when the two FMA residuals
are exactly representable and only the final addition is rounded.
-/

/-- Exact FMA correction term for the rounded product `w ≈ b*c`. -/
def problem2_25_fmaCorrection (w b c : ℝ) : ℝ :=
  fusedMultiplyAddExact (-b) c w

/-- Exact FMA main term `a*d - w`. -/
def problem2_25_fmaMain (a d w : ℝ) : ℝ :=
  fusedMultiplyAddExact a d (-w)

/-- Exact Kahan FMA determinant core before the final addition rounding. -/
def problem2_25_fmaCore (a b c d w : ℝ) : ℝ :=
  problem2_25_fmaMain a d w + problem2_25_fmaCorrection w b c

/-- Finite round-to-even FMA correction term. -/
def problem2_25_finiteFmaCorrection
    (fmt : FloatingPointFormat) (w b c : ℝ) : ℝ :=
  fmt.finiteRoundToEvenFMA (-b) c w

/-- Finite round-to-even FMA main term. -/
def problem2_25_finiteFmaMain
    (fmt : FloatingPointFormat) (a d w : ℝ) : ℝ :=
  fmt.finiteRoundToEvenFMA a d (-w)

/-- Finite FMA determinant core before the final rounded addition. -/
def problem2_25_finiteFmaCore
    (fmt : FloatingPointFormat) (a b c d w : ℝ) : ℝ :=
  problem2_25_finiteFmaMain fmt a d w +
    problem2_25_finiteFmaCorrection fmt w b c

/-- Source-facing finite Kahan FMA determinant algorithm with a rounded final
addition.  The rounded initial product `w` is left as an explicit input; the
correction theorem below is independent of the particular finite multiplication
routine that produced it. -/
def problem2_25_finiteFmaDet
    (fmt : FloatingPointFormat) (a b c d w : ℝ) : ℝ :=
  fmt.finiteRoundToEven (problem2_25_finiteFmaCore fmt a b c d w)

/-- The source algorithm's first computed value, `w = fl(b*c)`, in the finite
round-to-even model. -/
def problem2_25_finiteRoundedProduct
    (fmt : FloatingPointFormat) (b c : ℝ) : ℝ :=
  fmt.finiteRoundToEvenOp BasicOp.mul b c

/-- The source-facing finite Kahan FMA determinant algorithm with the rounded
initial product `w = fl(b*c)` wired into the subsequent FMA residuals. -/
def problem2_25_finiteFmaDetWithRoundedProduct
    (fmt : FloatingPointFormat) (a b c d : ℝ) : ℝ :=
  problem2_25_finiteFmaDet fmt a b c d
    (problem2_25_finiteRoundedProduct fmt b c)

/-- Exact-residual side condition for the source-shaped rounded-product
algorithm: after `w = fl(b*c)`, both FMA residuals used by the determinant
core are finite representable. -/
def problem2_25_roundedProductResidualsRepresentable
    (fmt : FloatingPointFormat) (a b c d : ℝ) : Prop :=
  fmt.finiteSystem
      (problem2_25_fmaMain a d
        (problem2_25_finiteRoundedProduct fmt b c)) ∧
    fmt.finiteSystem
      (problem2_25_fmaCorrection
        (problem2_25_finiteRoundedProduct fmt b c) b c)

/-- The rounded initial product is a finite value of the model format. -/
theorem problem2_25_finiteRoundedProduct_finiteSystem
    (fmt : FloatingPointFormat) (b c : ℝ) :
    fmt.finiteSystem (problem2_25_finiteRoundedProduct fmt b c) := by
  exact fmt.finiteRoundToEvenOp_finiteSystem BasicOp.mul b c

/-- The exact FMA residual core computes `det [[a,b],[c,d]]`, independently of
the rounded product value `w`. -/
theorem problem2_25_fmaCore_eq_det2x2
    (a b c d w : ℝ) :
    problem2_25_fmaCore a b c d w = det2x2 a b c d := by
  unfold problem2_25_fmaCore problem2_25_fmaMain problem2_25_fmaCorrection
    fusedMultiplyAddExact det2x2
  ring

/-- If the FMA correction residual is representable, finite round-to-even FMA
returns the exact correction `w - b*c`. -/
theorem problem2_25_finiteFmaCorrection_eq_exact_of_finiteSystem
    {fmt : FloatingPointFormat} {w b c : ℝ}
    (hcorr : fmt.finiteSystem (problem2_25_fmaCorrection w b c)) :
    problem2_25_finiteFmaCorrection fmt w b c =
      problem2_25_fmaCorrection w b c := by
  exact fmt.finiteRoundToEvenFMA_eq_exact_of_finiteSystem hcorr

/-- If the FMA main residual is representable, finite round-to-even FMA returns
the exact `a*d - w` term. -/
theorem problem2_25_finiteFmaMain_eq_exact_of_finiteSystem
    {fmt : FloatingPointFormat} {a d w : ℝ}
    (hmain : fmt.finiteSystem (problem2_25_fmaMain a d w)) :
    problem2_25_finiteFmaMain fmt a d w = problem2_25_fmaMain a d w := by
  exact fmt.finiteRoundToEvenFMA_eq_exact_of_finiteSystem hmain

/-- With exact representability of the two FMA residuals, the finite FMA core
is exactly the determinant before the final addition rounding. -/
theorem problem2_25_finiteFmaCore_eq_det2x2_of_exact_residuals
    {fmt : FloatingPointFormat} {a b c d w : ℝ}
    (hmain : fmt.finiteSystem (problem2_25_fmaMain a d w))
    (hcorr : fmt.finiteSystem (problem2_25_fmaCorrection w b c)) :
    problem2_25_finiteFmaCore fmt a b c d w = det2x2 a b c d := by
  calc
    problem2_25_finiteFmaCore fmt a b c d w
        = problem2_25_fmaCore a b c d w := by
          simp [problem2_25_finiteFmaCore, problem2_25_fmaCore,
            problem2_25_finiteFmaMain_eq_exact_of_finiteSystem hmain,
            problem2_25_finiteFmaCorrection_eq_exact_of_finiteSystem hcorr]
    _ = det2x2 a b c d := problem2_25_fmaCore_eq_det2x2 a b c d w

/-- Problem 2.25 relative-error theorem surface: if the two FMA residuals are
exactly representable and the exact determinant is in finite-normal range, then
the final rounded determinant satisfies the strict unit-roundoff relative-error
model. -/
theorem problem2_25_finiteFmaDet_signedRelErrorWitness_lt
    {fmt : FloatingPointFormat} {a b c d w : ℝ}
    (hmain : fmt.finiteSystem (problem2_25_fmaMain a d w))
    (hcorr : fmt.finiteSystem (problem2_25_fmaCorrection w b c))
    (hdet : fmt.finiteNormalRange (det2x2 a b c d)) :
    ∃ δ : ℝ,
      |δ| < fmt.unitRoundoff ∧
        signedRelErrorWitness
          (problem2_25_finiteFmaDet fmt a b c d w)
          (det2x2 a b c d) δ := by
  have hcore :
      problem2_25_finiteFmaCore fmt a b c d w = det2x2 a b c d :=
    problem2_25_finiteFmaCore_eq_det2x2_of_exact_residuals hmain hcorr
  rcases fmt.finiteRoundToEven_signedRelErrorWitness_lt_of_finiteNormalRange
      hdet with
    ⟨δ, _hround, hδ, hwit⟩
  refine ⟨δ, hδ, ?_⟩
  unfold problem2_25_finiteFmaDet
  rw [hcore]
  exact hwit

/-- Relative-error form of the preceding theorem. -/
theorem problem2_25_finiteFmaDet_relError_lt_unitRoundoff
    {fmt : FloatingPointFormat} {a b c d w : ℝ}
    (hmain : fmt.finiteSystem (problem2_25_fmaMain a d w))
    (hcorr : fmt.finiteSystem (problem2_25_fmaCorrection w b c))
    (hdet : fmt.finiteNormalRange (det2x2 a b c d)) :
    relError
        (problem2_25_finiteFmaDet fmt a b c d w)
        (det2x2 a b c d) < fmt.unitRoundoff := by
  rcases problem2_25_finiteFmaDet_signedRelErrorWitness_lt
      hmain hcorr hdet with
    ⟨δ, hδ, hwit⟩
  have hdet_ne : relErrorDefined (det2x2 a b c d) :=
    fmt.finiteNormalRange_ne_zero hdet
  rw [relError_eq_abs_of_signedRelErrorWitness hdet_ne hwit]
  exact hδ

/-- Source-shaped specialization of the relative-error theorem: the first
computed quantity is the rounded product `w = fl(b*c)`, as in Problem 2.25's
displayed algorithm.  The residual representability hypotheses remain explicit
because they are the still-open binary/IEEE exact-residual side conditions. -/
theorem problem2_25_finiteFmaDetWithRoundedProduct_signedRelErrorWitness_lt
    {fmt : FloatingPointFormat} {a b c d : ℝ}
    (hmain : fmt.finiteSystem
      (problem2_25_fmaMain a d
        (problem2_25_finiteRoundedProduct fmt b c)))
    (hcorr : fmt.finiteSystem
      (problem2_25_fmaCorrection
        (problem2_25_finiteRoundedProduct fmt b c) b c))
    (hdet : fmt.finiteNormalRange (det2x2 a b c d)) :
    ∃ δ : ℝ,
      |δ| < fmt.unitRoundoff ∧
        signedRelErrorWitness
          (problem2_25_finiteFmaDetWithRoundedProduct fmt a b c d)
          (det2x2 a b c d) δ := by
  exact problem2_25_finiteFmaDet_signedRelErrorWitness_lt hmain hcorr hdet

/-- Relative-error form of the source-shaped rounded-product specialization. -/
theorem problem2_25_finiteFmaDetWithRoundedProduct_relError_lt_unitRoundoff
    {fmt : FloatingPointFormat} {a b c d : ℝ}
    (hmain : fmt.finiteSystem
      (problem2_25_fmaMain a d
        (problem2_25_finiteRoundedProduct fmt b c)))
    (hcorr : fmt.finiteSystem
      (problem2_25_fmaCorrection
        (problem2_25_finiteRoundedProduct fmt b c) b c))
    (hdet : fmt.finiteNormalRange (det2x2 a b c d)) :
    relError (problem2_25_finiteFmaDetWithRoundedProduct fmt a b c d)
        (det2x2 a b c d) < fmt.unitRoundoff := by
  exact problem2_25_finiteFmaDet_relError_lt_unitRoundoff hmain hcorr hdet

theorem problem2_25_finiteFmaDetWithRoundedProduct_highRelativeAccuracy
    {fmt : FloatingPointFormat} {a b c d : ℝ}
    (hres : problem2_25_roundedProductResidualsRepresentable fmt a b c d)
    (hdet : fmt.finiteNormalRange (det2x2 a b c d)) :
    ∃ δ : ℝ,
      |δ| < fmt.unitRoundoff ∧
        signedRelErrorWitness
          (problem2_25_finiteFmaDetWithRoundedProduct fmt a b c d)
          (det2x2 a b c d) δ ∧
        relError (problem2_25_finiteFmaDetWithRoundedProduct fmt a b c d)
          (det2x2 a b c d) < fmt.unitRoundoff := by
  rcases hres with ⟨hmain, hcorr⟩
  rcases problem2_25_finiteFmaDetWithRoundedProduct_signedRelErrorWitness_lt
      hmain hcorr hdet with
    ⟨δ, hδ, hwit⟩
  refine ⟨δ, hδ, hwit, ?_⟩
  exact problem2_25_finiteFmaDetWithRoundedProduct_relError_lt_unitRoundoff
    hmain hcorr hdet

end

end NumStability
