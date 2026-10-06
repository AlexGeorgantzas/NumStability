import Mathlib.Algebra.BigOperators.Group.Finset.Basic
import Mathlib.Algebra.BigOperators.Ring.Finset
import Mathlib.Algebra.Order.BigOperators.Group.Finset
import Mathlib.Analysis.Calculus.Deriv.Add
import Mathlib.Analysis.Calculus.LocalExtr.Basic
import Mathlib.Analysis.SpecialFunctions.Sqrt
import Mathlib.Data.Fintype.BigOperators
import Mathlib.Data.Real.Basic
import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Ring
import NumStability.Algorithms.LU.GrowthFactor
import NumStability.Algorithms.NormEstimation.OneNorm.PowerMethod.CondEstimation
import NumStability.Algorithms.NormEstimation.OneNorm.PowerMethod.PNormPowerMethod
import NumStability.Algorithms.NormEstimation.PNorm.PowerMethod.PNormPowerMethod
import NumStability.Analysis.MatrixAlgebra
import NumStability.Source.Higham.Chapter15.Lemma02.PNormPowerMethod.PNormPowerMethod

/-!
# Chapter15 Algorithm01 PNormPowerMethod PNormPowerMethod

Canonical destination for material split out of
`NumStability.Algorithms.PNormPowerMethod` by wave W10 of the August 2026 repository reorganization.
Declaration names, statements and proofs are unchanged; only the
module they live in has changed. The historical module still
resolves and re-exports this one.
-/

namespace NumStability

namespace Ch15

open scoped BigOperators

namespace PNormPair

variable {n : ℕ} (P : PNormPair n)

/-- State carried by Algorithm 15.1: the current iterate `x` and the running
    estimate `γ` (Higham §15.2, p. 289). -/
structure State (n : ℕ) where
  /-- Current iterate `x` (kept at unit p-norm). -/
  x : Fin n → ℝ
  /-- Running lower-bound estimate `γ`. -/
  γ : ℝ

/-- **One step of Algorithm 15.1** (Higham §15.2, p. 289), the p-norm power
    method loop body.  Given the current `x`:

      `y = A x;  z = Aᵀ dualp(y);  γ = ‖y‖_p;`
      `if ‖z‖_q ≤ zᵀ x then (converged, return x)  else x = dualq(z)`.

    Returns the updated state together with the convergence flag.  The estimate
    `γ = ‖y‖_p` is set on every step (as in Higham's code, where `γ = ‖y‖_p` is
    recorded before the test). -/
noncomputable def powerStep (st : State n) : State n × Bool :=
  let y := P.yof st.x
  let z := fun j => ∑ i : Fin n, P.A i j * P.dp y i
  let γ := P.pN y
  let zTx := ∑ j : Fin n, z j * st.x j
  if P.qN z ≤ zTx then
    (⟨st.x, γ⟩, true)
  else
    (⟨P.dq z, γ⟩, false)

/-- The estimate returned by `powerStep` is always `γ = ‖A x‖_p`, whichever
    branch is taken (Algorithm 15.1 records `γ = ‖y‖_p`). -/
lemma powerStep_gamma_eq (st : State n) :
    (P.powerStep st).1.γ = P.pN (P.yof st.x) := by
  simp only [powerStep]
  split_ifs <;> rfl

/-- **Algorithm 15.1 postcondition — lower bound** (Higham §15.2, p. 289:
    "computes γ … such that γ ≤ ‖A‖_p").

    If the current iterate has unit p-norm, the estimate returned by one step of
    Algorithm 15.1 satisfies `γ ≤ ‖A‖_p`. -/
theorem powerStep_gamma_le_opP (st : State n) (hx : P.pN st.x = 1) :
    (P.powerStep st).1.γ ≤ P.opP := by
  rw [P.powerStep_gamma_eq st]
  have hb := P.op_bound st.x
  rw [hx, mul_one] at hb
  simpa [yof] using hb

/-- **Algorithm 15.1 postcondition — the scaling identity** (Higham §15.2,
    p. 289: "computes γ … such that … ‖A x‖_p = γ ‖x‖_p").

    With the current iterate at unit p-norm, the returned estimate satisfies
    `‖A x‖_p = γ · ‖x‖_p` (both sides equal `γ = ‖A x‖_p`). -/
theorem powerStep_scaling (st : State n) (hx : P.pN st.x = 1) :
    P.pN (P.yof st.x) = (P.powerStep st).1.γ * P.pN st.x := by
  rw [P.powerStep_gamma_eq st, hx, mul_one]

/-- **Increasing sequence of norm approximations** (Higham §15.2, p. 291).

    `γₖ ≤ γₖ₊₁`.  "For all values of p the power method has the desirable
    property of generating an increasing sequence of norm approximations."
    Immediate from Lemma 15.2(b): `‖yₖ‖_p ≤ ‖zₖ‖_q ≤ ‖yₖ₊₁‖_p`. -/
theorem gammaSeq_mono (x0 : Fin n → ℝ) (hx0 : P.pN x0 = 1) (k : ℕ) :
    P.gammaSeq x0 k ≤ P.gammaSeq x0 (k + 1) := by
  have hk := P.xseq_punit x0 hx0 k
  have hb := P.lemma152b (P.xseq x0 k) hk
  have h13 : P.pN (P.yof (P.xseq x0 k)) ≤ P.pN (P.yof (P.xnext (P.xseq x0 k))) :=
    le_trans hb.1 hb.2.1
  simpa [gammaSeq, xseq] using h13

/-- **Genuine lower bound on the operator p-norm** (Higham §15.2, p. 290-291).

    `γₖ ≤ ‖A‖_p` for every `k`: each estimate under-estimates the true operator
    p-norm.  This is the guarantee `γ ≤ ‖A‖_p` promised by Algorithm 15.1. -/
theorem gammaSeq_le_opP (x0 : Fin n → ℝ) (hx0 : P.pN x0 = 1) (k : ℕ) :
    P.gammaSeq x0 k ≤ P.opP := by
  cases k with
  | zero =>
    have hb := P.op_bound (P.xseq x0 0)
    rw [show P.xseq x0 0 = x0 from rfl, hx0, mul_one] at hb
    simpa [gammaSeq, yof] using hb
  | succ k =>
    have hk := P.xseq_punit x0 hx0 k
    have hb := P.lemma152b (P.xseq x0 k) hk
    simpa [gammaSeq, xseq] using hb.2.2

/-- **Monotone from the start** (Higham §15.2, p. 291): `γ₀ ≤ γₖ` for all `k`. -/
theorem gammaSeq_ge_start (x0 : Fin n → ℝ) (hx0 : P.pN x0 = 1) (k : ℕ) :
    P.gammaSeq x0 0 ≤ P.gammaSeq x0 k := by
  induction k with
  | zero => exact le_refl _
  | succ k ih => exact le_trans ih (P.gammaSeq_mono x0 hx0 k)

end PNormPair

/-- **2-norm estimate is a lower bound on `‖A‖₂`** (Higham §15.2, p. 291).

    Every estimate `γₖ = ‖A xₖ‖₂` produced by the 2-norm power method
    under-estimates the exact spectral norm `opNorm2 A`. -/
theorem gammaSeq_two_le_opNorm2 {n : ℕ} (hn : 0 < n) (A : Fin n → Fin n → ℝ)
    (x0 : Fin n → ℝ) (hx0 : vecNorm2 x0 = 1) (k : ℕ) :
    (pNormPair_two hn A).gammaSeq x0 k ≤ opNorm2 A :=
  (pNormPair_two hn A).gammaSeq_le_opP x0 hx0 k

/-- **2-norm estimates increase** (Higham §15.2, p. 291): `γₖ ≤ γₖ₊₁`. -/
theorem gammaSeq_two_mono {n : ℕ} (hn : 0 < n) (A : Fin n → Fin n → ℝ)
    (x0 : Fin n → ℝ) (hx0 : vecNorm2 x0 = 1) (k : ℕ) :
    (pNormPair_two hn A).gammaSeq x0 k ≤ (pNormPair_two hn A).gammaSeq x0 (k + 1) :=
  (pNormPair_two hn A).gammaSeq_mono x0 hx0 k

/-- **1-norm estimate is a lower bound on `‖A‖₁`** (Higham §15.2, p. 291;
    cf. Algorithm 15.1's guarantee `γ ≤ ‖A‖_p`). -/
theorem gammaSeq_one_le_oneNorm {n : ℕ} (hn : 0 < n) (A : Fin n → Fin n → ℝ)
    (x0 : Fin n → ℝ) (hx0 : oneNormVec x0 = 1) (k : ℕ) :
    (pNormPair_one hn A).gammaSeq x0 k ≤ oneNorm A :=
  (pNormPair_one hn A).gammaSeq_le_opP x0 hx0 k

/-- **1-norm estimates increase** (Higham §15.2, p. 291): `γₖ ≤ γₖ₊₁`. -/
theorem gammaSeq_one_mono {n : ℕ} (hn : 0 < n) (A : Fin n → Fin n → ℝ)
    (x0 : Fin n → ℝ) (hx0 : oneNormVec x0 = 1) (k : ℕ) :
    (pNormPair_one hn A).gammaSeq x0 k ≤ (pNormPair_one hn A).gammaSeq x0 (k + 1) :=
  (pNormPair_one hn A).gammaSeq_mono x0 hx0 k

end Ch15
end NumStability
