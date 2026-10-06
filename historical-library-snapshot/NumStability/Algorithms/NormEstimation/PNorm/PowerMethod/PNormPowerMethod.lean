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
import NumStability.Algorithms.NormEstimation.PNorm.Duality.PNormPowerMethod
import NumStability.Analysis.MatrixAlgebra

/-!
# NumStability Algorithms NormEstimation PNorm PowerMethod PNormPowerMethod

Canonical destination for material split out of
`NumStability.Algorithms.PNormPowerMethod` by wave W10 of the August 2026 repository reorganization.
Declaration names, statements and proofs are unchanged; only the
module they live in has changed. The historical module still
resolves and re-exports this one.
-/

namespace NumStability

namespace Ch15

open scoped BigOperators

/-- **Dual-norm data for the p-norm power method** (Higham §15.2, p. 289).

    Bundles a square matrix `A` together with the p-norm `pN = ‖·‖_p`, the dual
    q-norm `qN = ‖·‖_q` (`1/p + 1/q = 1`), the operator p-norm `opP = ‖A‖_p`, and
    the two dual maps `dp = dualp`, `dq = dualq`, subject to *exactly* the
    printed properties that Lemma 15.2's proof invokes (Higham p. 289-291):

    * `pN_nonneg`  — `‖·‖_p` is a nonnegative functional;
    * `dp_attains` — `dualp(v)ᵀ v = ‖v‖_p`   (Hölder equality for `dualp`);
    * `dp_qunit`   — `‖dualp(v)‖_q ≤ 1`       (unit q-norm normalization; `≤`
                     suffices for the proof and is weaker than Higham's `= 1`);
    * `dq_attains` — `dualq(w)ᵀ w = ‖w‖_q`   (Hölder equality for `dualq`);
    * `dq_punit`   — `‖dualq(w)‖_p = 1`       (the iterates have unit p-norm);
    * `holder`     — `uᵀ v ≤ ‖u‖_q ‖v‖_p`     (Hölder inequality);
    * `op_bound`   — `‖A v‖_p ≤ ‖A‖_p ‖v‖_p`  (operator-norm submultiplicativity).

    None of these fields is the Lemma 15.2 chain; the chain is derived below. -/
structure PNormPair (n : ℕ) where
  /-- The matrix `A ∈ ℝ^{n×n}` whose p-norm is being estimated. -/
  A     : Fin n → Fin n → ℝ
  /-- The vector p-norm `‖·‖_p`. -/
  pN    : (Fin n → ℝ) → ℝ
  /-- The dual vector q-norm `‖·‖_q` (`1/p + 1/q = 1`). -/
  qN    : (Fin n → ℝ) → ℝ
  /-- The operator p-norm `‖A‖_p`. -/
  opP   : ℝ
  /-- The dual map `dualp`: unit q-norm, attaining Hölder equality. -/
  dp    : (Fin n → ℝ) → (Fin n → ℝ)
  /-- The dual map `dualq`: unit p-norm, attaining Hölder equality. -/
  dq    : (Fin n → ℝ) → (Fin n → ℝ)
  /-- `‖·‖_p` is nonnegative. -/
  pN_nonneg   : ∀ v, 0 ≤ pN v
  /-- Higham §15.2, p. 289: `dualp(v)ᵀ v = ‖v‖_p`. -/
  dp_attains  : ∀ v, (∑ i : Fin n, dp v i * v i) = pN v
  /-- Higham §15.2, p. 289: `‖dualp(v)‖_q = 1` (here weakened to `≤ 1`). -/
  dp_qunit    : ∀ v, qN (dp v) ≤ 1
  /-- Dual attainment for `dualq`: `dualq(w)ᵀ w = ‖w‖_q`. -/
  dq_attains  : ∀ w, (∑ i : Fin n, dq w i * w i) = qN w
  /-- The iterate `x = dualq(z)` has unit p-norm: `‖dualq(w)‖_p = 1`. -/
  dq_punit    : ∀ w, pN (dq w) = 1
  /-- Hölder inequality: `uᵀ v ≤ ‖u‖_q ‖v‖_p`. -/
  holder      : ∀ u v, (∑ i : Fin n, u i * v i) ≤ qN u * pN v
  /-- Operator-norm bound: `‖A v‖_p ≤ ‖A‖_p ‖v‖_p`. -/
  op_bound    : ∀ v, pN (fun i => ∑ j : Fin n, A i j * v j) ≤ opP * pN v

namespace PNormPair

variable {n : ℕ} (P : PNormPair n)

/-- `y = A x` (Algorithm 15.1, first line of the loop). -/
noncomputable def yof (x : Fin n → ℝ) : Fin n → ℝ :=
  fun i => ∑ j : Fin n, P.A i j * x j

/-- `z = Aᵀ dualp(y)` (Algorithm 15.1, second line of the loop):
    `zⱼ = ∑ᵢ Aᵢⱼ dualp(y)ᵢ`. -/
noncomputable def zof (x : Fin n → ℝ) : Fin n → ℝ :=
  fun j => ∑ i : Fin n, P.A i j * P.dp (P.yof x) i

/-- The next iterate `x = dualq(z)` (Algorithm 15.1, last line of the loop). -/
noncomputable def xnext (x : Fin n → ℝ) : Fin n → ℝ := P.dq (P.zof x)

/-- **Adjoint identity** for the transpose step (Algorithm 15.1).

    `zᵀ v = dualp(y)ᵀ (A v)`, i.e. `(Aᵀ u)ᵀ v = uᵀ (A v)`.  This is the pure
    algebraic fact underlying `z = Aᵀ dualp(y)`; it is proved, not assumed. -/
lemma z_dot (x v : Fin n → ℝ) :
    (∑ j : Fin n, P.zof x j * v j)
      = ∑ i : Fin n, P.dp (P.yof x) i * (∑ j : Fin n, P.A i j * v j) := by
  unfold zof
  have h1 : ∀ j : Fin n, (∑ i : Fin n, P.A i j * P.dp (P.yof x) i) * v j
      = ∑ i : Fin n, (P.A i j * P.dp (P.yof x) i) * v j :=
    fun j => by rw [Finset.sum_mul]
  simp_rw [h1]
  rw [Finset.sum_comm]
  refine Finset.sum_congr rfl (fun i _ => ?_)
  rw [Finset.mul_sum]
  refine Finset.sum_congr rfl (fun j _ => ?_)
  ring

/-- Linearity of the matrix action in the difference form needed by the
subgradient chain rule. -/
lemma yof_sub (v x : Fin n → ℝ) :
    P.yof (fun i => v i - x i) = fun i => P.yof v i - P.yof x i := by
  funext i
  simp only [yof, mul_sub, Finset.sum_sub_distrib]

/-- The norming functional `dualp(x)` is a subgradient of the vector norm.
This derives the displayed subgradient inequality from Hölder attainment and
the unit dual-norm bound; it is not assumed as part of `PNormPair`. -/
theorem dp_isSubgradient (x : Fin n → ℝ) :
    IsSubgradient P.pN x (P.dp x) := by
  intro v
  have hdual : (∑ i : Fin n, P.dp x i * v i) ≤ P.pN v := by
    calc
      (∑ i : Fin n, P.dp x i * v i) ≤ P.qN (P.dp x) * P.pN v :=
        P.holder _ _
      _ ≤ 1 * P.pN v :=
        mul_le_mul_of_nonneg_right (P.dp_qunit _) (P.pN_nonneg _)
      _ = P.pN v := one_mul _
  calc
    P.pN x + (∑ i : Fin n, P.dp x i * (v i - x i))
        = ∑ i : Fin n, P.dp x i * v i := by
          rw [← P.dp_attains x]
          simp_rw [mul_sub]
          rw [Finset.sum_sub_distrib]
          ring
    _ ≤ P.pN v := hdual

/-- The iterate sequence of Algorithm 15.1 (functional iteration of `xnext`):
    `x₀` given, `xₖ₊₁ = dualq(zₖ)`.  Each iterate after the start has unit
    p-norm; see `xseq_punit`. -/
noncomputable def xseq (x0 : Fin n → ℝ) : ℕ → (Fin n → ℝ)
  | 0 => x0
  | k + 1 => P.xnext (xseq x0 k)

/-- Every iterate has unit p-norm, `‖xₖ‖_p = 1` (given `‖x₀‖_p = 1`).

    Higham normalizes `x₀ = x₀/‖x₀‖_p` and each `xₖ₊₁ = dualq(zₖ)` has unit
    p-norm by construction. -/
lemma xseq_punit (x0 : Fin n → ℝ) (hx0 : P.pN x0 = 1) (k : ℕ) :
    P.pN (P.xseq x0 k) = 1 := by
  cases k with
  | zero => simpa [xseq] using hx0
  | succ k => simpa [xseq] using P.dq_punit _

/-- The estimate sequence `γₖ = ‖yₖ‖_p = ‖A xₖ‖_p` (Higham §15.2, p. 291). -/
noncomputable def gammaSeq (x0 : Fin n → ℝ) (k : ℕ) : ℝ :=
  P.pN (P.yof (P.xseq x0 k))

end PNormPair

/-- **The 2-norm power method as a `PNormPair`** (Higham §15.2, `p = 2`).

    For `p = 2` the algorithm "reduces to the usual power method applied to
    AᵀA" (Higham p. 289).  Here `‖·‖_p = ‖·‖_q = ‖·‖₂` and `‖A‖_p = opNorm2 A`
    is the exact ℓ² (spectral) operator norm from `MatrixAlgebra`.  All seven
    dual/Hölder/operator hypotheses are discharged from repository lemmas, so
    Lemma 15.2, `gammaSeq_mono`, and `gammaSeq_le_opP` hold for this concrete
    instance — a non-vacuous witness. -/
noncomputable def pNormPair_two {n : ℕ} (hn : 0 < n)
    (A : Fin n → Fin n → ℝ) : PNormPair n where
  A := A
  pN := vecNorm2
  qN := vecNorm2
  opP := opNorm2 A
  dp := normalize2 hn
  dq := normalize2 hn
  pN_nonneg := vecNorm2_nonneg
  dp_attains := normalize2_attains hn
  dp_qunit := fun v => le_of_eq (normalize2_unit hn v)
  dq_attains := normalize2_attains hn
  dq_punit := normalize2_unit hn
  holder := holder_two
  op_bound := opBound_two A

/-- The source-strength smooth interior (`1 < p,q < ∞`) refinement of
`PNormPair` used for Higham's equations (15.2), (15.3), and (15.5).

The inherited `PNormPair` fields give Hölder duality and attainment.  The new
fields record the printed conjugate-exponent regime, exact normalized `dualp`
away from zero, positivity of the p-norm, and the standard fact that
`dualp(x)` is its gradient at every nonzero `x`.  Thus the displayed equations
below are consequences of the normalized p/q-dual interface, not fields of the
structure. -/
structure SmoothPNormPair (n : ℕ) where
  /-- The underlying matrix, p/q norms, operator norm, and normalized duals. -/
  P : PNormPair n
  /-- The primal exponent. -/
  p : ℝ
  /-- The conjugate exponent. -/
  q : ℝ
  /-- Higham's smooth-interior hypothesis on the primal exponent. -/
  one_lt_p : 1 < p
  /-- The corresponding smooth-interior hypothesis on the dual exponent. -/
  one_lt_q : 1 < q
  /-- Conjugacy: `1/p + 1/q = 1`. -/
  conjugate : p⁻¹ + q⁻¹ = 1
  /-- The primal norm vanishes at zero. -/
  pN_zero : P.pN 0 = 0
  /-- The primal norm is positive away from zero. -/
  pN_pos : ∀ x, x ≠ 0 → 0 < P.pN x
  /-- Higham's normalized convention: `‖dualp(x)‖_q = 1` for `x ≠ 0`. -/
  dp_qnorm_one : ∀ x, x ≠ 0 → P.qN (P.dp x) = 1
  /-- Away from zero, the gradient of `‖x‖_p` is `dualp(x)`. -/
  pN_gradient : ∀ x, x ≠ 0 → HasDirectionalGradientAt P.pN (P.dp x) x

namespace SmoothPNormPair

variable {n : ℕ} (S : SmoothPNormPair n)

/-- The chain rule gives `Aᵀ dualp(Ax)` as the gradient of `x ↦ ‖Ax‖_p`. -/
theorem composite_hasDirectionalGradientAt (x : Fin n → ℝ)
    (hy : S.P.yof x ≠ 0) :
    HasDirectionalGradientAt (fun v => S.P.pN (S.P.yof v))
      (S.P.zof x) x := by
  intro h
  have hbase := S.pN_gradient (S.P.yof x) hy (S.P.yof h)
  have haffine : ∀ t : ℝ,
      S.P.yof (fun i => x i + t * h i) =
        fun i => S.P.yof x i + t * S.P.yof h i := by
    intro t
    funext i
    simp only [PNormPair.yof, mul_add, Finset.sum_add_distrib,
      Finset.mul_sum]
    congr 1
    apply Finset.sum_congr rfl
    intro j _
    ring
  convert hbase using 1
  · funext t
    change S.P.pN (S.P.yof (fun i => x i + t * h i)) = _
    rw [haffine t]
  · simpa [PNormPair.yof] using S.P.z_dot x h

/-- The concrete Euclidean instance of the smooth conjugate p/q interface. -/
noncomputable def two {n : ℕ} (hn : 0 < n)
    (A : Fin n → Fin n → ℝ) : SmoothPNormPair n where
  P := pNormPair_two hn A
  p := 2
  q := 2
  one_lt_p := by norm_num
  one_lt_q := by norm_num
  conjugate := by norm_num
  pN_zero := by simpa using (vecNorm2_zero (n := n))
  pN_pos := vecNorm2_pos_of_ne
  dp_qnorm_one := fun x _hx => normalize2_unit hn x
  pN_gradient := vecNorm2_hasDirectionalGradientAt hn

end SmoothPNormPair
end Ch15
end NumStability
