import Mathlib.Algebra.BigOperators.Group.Finset.Basic
import Mathlib.Algebra.BigOperators.Ring.Finset
import Mathlib.Algebra.Order.BigOperators.Group.Finset
import Mathlib.Analysis.Calculus.Deriv.Add
import Mathlib.Analysis.Calculus.LocalExtr.Basic
import Mathlib.Analysis.InnerProductSpace.NormPow
import Mathlib.Analysis.SpecialFunctions.Sqrt
import Mathlib.Data.Fintype.BigOperators
import Mathlib.Data.Real.Basic
import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Ring
import NumStability.Algorithms.LU.GrowthFactor
import NumStability.Algorithms.NormEstimation.PNorm.Boyd.Differentiation.PNormGeneral
import NumStability.Algorithms.NormEstimation.PNorm.Duality.PNormGeneral
import NumStability.Algorithms.NormEstimation.PNorm.PowerMethod.PNormPowerMethod
import NumStability.Analysis.MatrixAlgebra
import NumStability.Analysis.MatrixNorms.Lp
import NumStability.Analysis.SingularValues.Realification

/-!
# NumStability Algorithms NormEstimation PNorm PowerMethod PNormGeneral

Canonical destination for material split out of
`NumStability.Algorithms.PNormPowerMethodGeneralP` by wave W10 of the August 2026 repository reorganization.
Declaration names, statements and proofs are unchanged; only the
module they live in has changed. The historical module still
resolves and re-exports this one.
-/

namespace NumStability

namespace Ch15

open scoped BigOperators

/-- The exact induced matrix `l^p` norm for a real square matrix, inherited
from the repository's least-bound complex matrix `L^p` norm. -/
noncomputable def realMatrixLpNorm {n : ℕ} (hn : 0 < n)
    (p : ℝ) (hp : 1 ≤ p) (A : Fin n → Fin n → ℝ) : ℝ :=
  complexMatrixLpNormOfReal hn p hp (realRectToCMatrix A)

/-- Concrete general-`p` instance of every duality/operator primitive used by
Higham's p-norm power method. -/
noncomputable def pNormPair_general {n : ℕ} (hn : 0 < n)
    {p q : ℝ} (hpq : p.HolderConjugate q)
    (A : Fin n → Fin n → ℝ) : PNormPair n where
  A := A
  pN := realVecLpNorm p
  qN := realVecLpNorm q
  opP := realMatrixLpNorm hn p (le_of_lt hpq.lt) A
  dp := realLpDual hpq
  dq := realLpDualUnit hn hpq.symm
  pN_nonneg := fun v => by
    haveI : Fact (1 ≤ ENNReal.ofReal p) := ⟨by
      rw [ENNReal.one_le_ofReal]
      exact le_of_lt hpq.lt⟩
    exact (complexVecLpNorm_isComplexVectorNorm
      (n := n) (ENNReal.ofReal p)).nonneg _
  dp_attains := fun v => (realLpDual_spec hpq v).2
  dp_qunit := fun v => (realLpDual_spec hpq v).1
  dq_attains := realLpDualUnit_attains hn hpq.symm
  dq_punit := realLpDualUnit_norm_eq_one hn hpq.symm
  holder := fun u v => (le_abs_self _).trans (realVecLpNorm_holder hpq u v)
  op_bound := fun v => by
    have hval := complexMatrixLpNormOfReal_isComplexMatrixLpNormValue
      (m := n) (n := n) hn p (le_of_lt hpq.lt) (realRectToCMatrix A)
    have hbound := hval.1 (fun j : Fin n => (v j : ℂ))
    simpa [realMatrixLpNorm, realVecLpNorm, complexMatrixVecMul,
      realRectToCMatrix] using hbound

/-- Fully concrete smooth general-`p` instance (`1 < p,q < infinity`) for
Higham's equations (15.2), (15.3), and (15.5). -/
noncomputable def SmoothPNormPair.general {n : ℕ} (hn : 0 < n)
    {p q : ℝ} (hpq : p.HolderConjugate q)
    (A : Fin n → Fin n → ℝ) : SmoothPNormPair n where
  P := pNormPair_general hn hpq A
  p := p
  q := q
  one_lt_p := hpq.lt
  one_lt_q := hpq.symm.lt
  conjugate := hpq.inv_add_inv_eq_one
  pN_zero := realVecLpNorm_zero (le_of_lt hpq.lt)
  pN_pos := fun x hx => realVecLpNorm_pos (le_of_lt hpq.lt) hx
  dp_qnorm_one := fun x hx => realLpDual_norm_eq_one hpq hx
  pN_gradient := fun x hx => realLpDual_hasDirectionalGradientAt hpq x hx

end Ch15
end NumStability
