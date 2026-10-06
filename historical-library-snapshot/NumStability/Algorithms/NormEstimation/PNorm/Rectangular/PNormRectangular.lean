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
import NumStability.Algorithms.NormEstimation.PNorm.Duality.PNormGeneral
import NumStability.Analysis.MatrixAlgebra
import NumStability.Analysis.MatrixNorms.Lp
import NumStability.Analysis.SingularValues.Realification

/-!
# NumStability Algorithms NormEstimation PNorm Rectangular PNormRectangular

Canonical destination for material split out of
`NumStability.Algorithms.PNormPowerMethodRect` by wave W10 of the August 2026 repository reorganization.
Declaration names, statements and proofs are unchanged; only the
module they live in has changed. The historical module still
resolves and re-exports this one.
-/

namespace NumStability

open scoped BigOperators

open Ch15

/-- Dual-norm data for the literal rectangular p-norm power method.

`pIn`/`qIn` live on the domain `R^n`; `pOut`/`qOut` live on the
codomain `R^m`.  The fields are exactly the dual-attainment, Holder, and
operator-norm facts used in Higham's proof of Lemma 15.2.  In particular, no
field is any inequality from Lemma 15.2 itself. -/
structure RectPNormPair (m n : ℕ) where
  A : Fin m → Fin n → ℝ
  pIn : (Fin n → ℝ) → ℝ
  qIn : (Fin n → ℝ) → ℝ
  pOut : (Fin m → ℝ) → ℝ
  qOut : (Fin m → ℝ) → ℝ
  opP : ℝ
  dpOut : (Fin m → ℝ) → (Fin m → ℝ)
  dqIn : (Fin n → ℝ) → (Fin n → ℝ)
  pIn_nonneg : ∀ v, 0 ≤ pIn v
  pOut_nonneg : ∀ v, 0 ≤ pOut v
  dpOut_attains : ∀ v, (∑ i : Fin m, dpOut v i * v i) = pOut v
  dpOut_qunit : ∀ v, qOut (dpOut v) ≤ 1
  dqIn_attains : ∀ w, (∑ j : Fin n, dqIn w j * w j) = qIn w
  dqIn_punit : ∀ w, pIn (dqIn w) = 1
  holderIn : ∀ u v, (∑ j : Fin n, u j * v j) ≤ qIn u * pIn v
  holderOut : ∀ u v, (∑ i : Fin m, u i * v i) ≤ qOut u * pOut v
  op_bound : ∀ v, pOut (fun i => ∑ j : Fin n, A i j * v j) ≤ opP * pIn v

namespace RectPNormPair

variable {m n : ℕ} (P : RectPNormPair m n)

/-- `y = A x`, with the source dimensions `x : R^n`, `y : R^m`. -/
noncomputable def yof (x : Fin n → ℝ) : Fin m → ℝ :=
  fun i => ∑ j : Fin n, P.A i j * x j

/-- `z = A^T dualp(y)`, with `z : R^n`. -/
noncomputable def zof (x : Fin n → ℝ) : Fin n → ℝ :=
  fun j => ∑ i : Fin m, P.A i j * P.dpOut (P.yof x) i

/-- The nonterminal update `x := dualq(z)`. -/
noncomputable def xnext (x : Fin n → ℝ) : Fin n → ℝ :=
  P.dqIn (P.zof x)

/-- The exact scalar stopping test in Algorithm 15.1. -/
def StopsAt (x : Fin n → ℝ) : Prop :=
  P.qIn (P.zof x) ≤ ∑ j : Fin n, P.zof x j * x j

/-- State of the literal rectangular loop. -/
structure State where
  x : Fin n → ℝ
  γ : ℝ

/-- One literal loop step of rectangular Algorithm 15.1. -/
noncomputable def powerStep (st : State (n := n)) : State (n := n) × Bool :=
  let y := P.yof st.x
  let z := P.zof st.x
  let γ := P.pOut y
  let zTx := ∑ j : Fin n, z j * st.x j
  if P.qIn z ≤ zTx then
    (⟨st.x, γ⟩, true)
  else
    (⟨P.dqIn z, γ⟩, false)

lemma powerStep_gamma_eq (st : State (n := n)) :
    (P.powerStep st).1.γ = P.pOut (P.yof st.x) := by
  simp only [powerStep]
  split_ifs <;> rfl

/-- The transpose-pairing identity used in Lemma 15.2. -/
lemma z_dot (x v : Fin n → ℝ) :
    (∑ j : Fin n, P.zof x j * v j) =
      ∑ i : Fin m, P.dpOut (P.yof x) i * P.yof v i := by
  unfold zof yof
  simp_rw [Finset.sum_mul]
  rw [Finset.sum_comm]
  apply Finset.sum_congr rfl
  intro i _hi
  rw [Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro j _hj
  ring

/-- Functional iteration underlying Algorithm 15.1.  Stopping is recorded
separately by `StopsAt`, so this trace does not assert termination. -/
noncomputable def xseq (x0 : Fin n → ℝ) : ℕ → (Fin n → ℝ)
  | 0 => x0
  | k + 1 => P.xnext (xseq x0 k)

lemma xseq_punit (x0 : Fin n → ℝ) (hx0 : P.pIn x0 = 1) (k : ℕ) :
    P.pIn (P.xseq x0 k) = 1 := by
  cases k with
  | zero => exact hx0
  | succ k => simpa [xseq, xnext] using P.dqIn_punit (P.zof (P.xseq x0 k))

noncomputable def gammaSeq (x0 : Fin n → ℝ) (k : ℕ) : ℝ :=
  P.pOut (P.yof (P.xseq x0 k))

theorem gammaSeq_le_opP (x0 : Fin n → ℝ) (hx0 : P.pIn x0 = 1) (k : ℕ) :
    P.gammaSeq x0 k ≤ P.opP := by
  have hk := P.xseq_punit x0 hx0 k
  have h := P.op_bound (P.xseq x0 k)
  rw [hk, mul_one] at h
  simpa [gammaSeq, yof] using h

/-- Exact induced rectangular real matrix `l^p` norm used by the concrete
general-`p` instance below. -/
noncomputable def realRectMatrixLpNorm {m n : ℕ} (hn : 0 < n)
    (p : ℝ) (hp : 1 ≤ p) (A : Fin m → Fin n → ℝ) : ℝ :=
  complexMatrixLpNormOfReal hn p hp (realRectToCMatrix A)

/-- Concrete literal-rectangular instance for every Holder-conjugate
`1 < p,q < infinity`. -/
noncomputable def general {m n : ℕ} (hn : 0 < n)
    {p q : ℝ} (hpq : p.HolderConjugate q)
    (A : Fin m → Fin n → ℝ) : RectPNormPair m n where
  A := A
  pIn := realVecLpNorm p
  qIn := realVecLpNorm q
  pOut := realVecLpNorm p
  qOut := realVecLpNorm q
  opP := realRectMatrixLpNorm hn p (le_of_lt hpq.lt) A
  dpOut := realLpDual hpq
  dqIn := realLpDualUnit hn hpq.symm
  pIn_nonneg := fun v => by
    haveI : Fact (1 ≤ ENNReal.ofReal p) := ⟨by
      rw [ENNReal.one_le_ofReal]
      exact le_of_lt hpq.lt⟩
    exact (complexVecLpNorm_isComplexVectorNorm
      (n := n) (ENNReal.ofReal p)).nonneg _
  pOut_nonneg := fun v => by
    haveI : Fact (1 ≤ ENNReal.ofReal p) := ⟨by
      rw [ENNReal.one_le_ofReal]
      exact le_of_lt hpq.lt⟩
    exact (complexVecLpNorm_isComplexVectorNorm
      (n := m) (ENNReal.ofReal p)).nonneg _
  dpOut_attains := fun v => (realLpDual_spec hpq v).2
  dpOut_qunit := fun v => (realLpDual_spec hpq v).1
  dqIn_attains := realLpDualUnit_attains hn hpq.symm
  dqIn_punit := realLpDualUnit_norm_eq_one hn hpq.symm
  holderIn := fun u v => (le_abs_self _).trans (realVecLpNorm_holder hpq u v)
  holderOut := fun u v => (le_abs_self _).trans (realVecLpNorm_holder hpq u v)
  op_bound := fun v => by
    have hval := complexMatrixLpNormOfReal_isComplexMatrixLpNormValue
      (m := m) (n := n) hn p (le_of_lt hpq.lt) (realRectToCMatrix A)
    have hbound := hval.1 (fun j : Fin n => (v j : ℂ))
    simpa [realRectMatrixLpNorm, realVecLpNorm, complexMatrixVecMul,
      realRectToCMatrix] using hbound

end RectPNormPair
end NumStability
