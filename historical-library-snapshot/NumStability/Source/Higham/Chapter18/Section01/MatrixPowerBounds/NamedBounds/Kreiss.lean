import Mathlib.Analysis.Complex.Exponential
import NumStability.Analysis.LinearOperators.MatrixPowers.Kreiss.ResolventBound

/-!
# Source.Higham.Chapter18.Section01.MatrixPowerBounds.NamedBounds.Kreiss

W06 semantic leaf. Whole declaration commands are copied from the frozen C0005 owners; local private notations are expanded at their use sites.
-/

/-
# The lower half of the Kreiss matrix theorem

Higham, *Accuracy and Stability of Numerical Algorithms*, 2nd ed.,
Chapter 18, p. 348, quotes the finite-dimensional Kreiss matrix theorem

  phi(A) <= sup_k ||A^k||_2 <= e n phi(A),

where

  phi(A) = sup_{|z|>1} (|z|-1) ||(zI-A)^{-1}||_2.

This module proves the first inequality without assuming either a resolvent
bound or the desired conclusion.  The proof is the Banach-algebra Laurent
series argument: a uniform bound on all powers makes

  sum_{k>=0} z^(-k-1) A^k

absolutely summable for every |z|>1.  The geometric identities identify its
sum with the resolvent, and summing the norm majorant gives

  (|z|-1) ||(zI-A)^{-1}|| <= M.

The final theorem packages both suprema literally as `sSup`s whenever the
power norms are bounded above.  Thus it specializes verbatim to complex
matrices with the operator 2-norm.  The dimension-dependent reverse
inequality is deliberately not claimed here.
-/




namespace NumStability

open scoped Real Topology
open Complex Metric Set

section ComplexBanachAlgebra

variable {A : Type*} [NormedRing A] [NormedAlgebra ℂ A] [CompleteSpace A]






















































































































































































































/-- **Higham Chapter 18, lower Kreiss inequality** in literal supremum form:

`phi(a) <= sup_k ||a^k||`.

The boundedness premise merely states that the real-valued right-hand
supremum is finite; no resolvent estimate or target inequality is assumed. -/
theorem higham18_kreiss_lower
    (a : A) (hbdd : BddAbove (matrixPowerNormSet a)) :
    kreissConstant a ≤ matrixPowerNormSup a :=
  kreissConstant_le_of_powerBound a (powerBound_matrixPowerNormSup a hbdd)

/-! ## The contour part of the reverse direction

The following results isolate exactly the elementary part of the upper
Kreiss inequality.  They give the sharp contour estimate for every radius
`R>1`, and hence the standard `e (k+1) K` bound for each individual power.
The genuinely finite-dimensional step that replaces `k+1` by the matrix
dimension for all later powers is separate and is not assumed here.
-/


























































































































































/-- Literal-`phi` finite-horizon upper endpoint.  For an `n`-dimensional
matrix this proves the printed `e n phi(A)` estimate for every `k<n`; the
remaining `k≥n` reduction is precisely the unformalized deep step of the
finite-dimensional Kreiss theorem. -/
theorem higham18_kreiss_upper_first_dim [Nontrivial A]
    (a : A)
    (hres : ∀ z : ℂ, 1 < ‖z‖ → z ∈ resolventSet ℂ a)
    (hbdd : BddAbove (kreissResolventValueSet a))
    {k n : ℕ} (hk : k < n) :
    ‖a ^ k‖ ≤ Real.exp 1 * n * kreissConstant a :=
  norm_pow_le_exp_mul_dim_of_lt_of_kreissResolventBound a
    (kreissResolventBound_kreissConstant a hres hbdd) hk

end ComplexBanachAlgebra

end NumStability
