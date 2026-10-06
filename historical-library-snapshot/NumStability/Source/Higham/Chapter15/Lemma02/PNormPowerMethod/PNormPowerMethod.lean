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

/-!
# Chapter15 Lemma02 PNormPowerMethod PNormPowerMethod

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

/-- **Lemma 15.2 (a)** (Higham §15.2, p. 290).

    `zₖᵀ xₖ = ‖yₖ‖_p`.

    Proof (Higham p. 291): `zₖᵀ xₖ = dualp(yₖ)ᵀ A xₖ = dualp(yₖ)ᵀ yₖ = ‖yₖ‖_p`,
    the last step by the `dualp` attainment relation. -/
theorem lemma152a (x : Fin n → ℝ) :
    (∑ j : Fin n, P.zof x j * x j) = P.pN (P.yof x) := by
  rw [P.z_dot x x]
  have hyof : (∑ i : Fin n, P.dp (P.yof x) i * (∑ j : Fin n, P.A i j * x j))
       = ∑ i : Fin n, P.dp (P.yof x) i * P.yof x i := rfl
  rw [hyof, P.dp_attains]

/-- **Lemma 15.2 (b)** (Higham §15.2, p. 290-291), the increasing chain.

    For an iterate `x` with `‖x‖_p = 1`,
      `‖yₖ‖_p ≤ ‖zₖ‖_q ≤ ‖yₖ₊₁‖_p ≤ ‖A‖_p`.

    Proof (Higham p. 291):
      `‖yₖ‖_p = zₖᵀ xₖ ≤ ‖zₖ‖_q ‖xₖ‖_p = ‖zₖ‖_q`      (a) + Hölder + ‖xₖ‖_p = 1
             `= zₖᵀ xₖ₊₁ ≤ ‖dualp(yₖ)‖_q ‖A xₖ₊₁‖_p ≤ ‖yₖ₊₁‖_p`   dualq attains,
                                                                    Hölder,
                                                                    ‖dualp‖_q ≤ 1
             `≤ ‖A‖_p`.                                         operator bound. -/
theorem lemma152b (x : Fin n → ℝ) (hx : P.pN x = 1) :
    P.pN (P.yof x) ≤ P.qN (P.zof x) ∧
    P.qN (P.zof x) ≤ P.pN (P.yof (P.xnext x)) ∧
    P.pN (P.yof (P.xnext x)) ≤ P.opP := by
  -- (i)  ‖yₖ‖_p = zᵀxₖ ≤ ‖zₖ‖_q ‖xₖ‖_p = ‖zₖ‖_q
  have step1 : P.pN (P.yof x) ≤ P.qN (P.zof x) := by
    rw [← P.lemma152a x]
    calc (∑ j : Fin n, P.zof x j * x j)
        ≤ P.qN (P.zof x) * P.pN x := P.holder _ _
      _ = P.qN (P.zof x) := by rw [hx, mul_one]
  -- ‖zₖ‖_q = zₖᵀ xₖ₊₁  (xₖ₊₁ = dualq(zₖ) attains the dual norm of zₖ)
  have hz_xnext : (∑ j : Fin n, P.zof x j * P.xnext x j) = P.qN (P.zof x) := by
    unfold xnext
    rw [show (∑ j : Fin n, P.zof x j * P.dq (P.zof x) j)
          = ∑ j : Fin n, P.dq (P.zof x) j * P.zof x j from
        Finset.sum_congr rfl (fun j _ => by ring)]
    exact P.dq_attains _
  -- (ii)  ‖zₖ‖_q = zₖᵀ xₖ₊₁ = dualp(yₖ)ᵀ (A xₖ₊₁) ≤ ‖dualp(yₖ)‖_q ‖yₖ₊₁‖_p ≤ ‖yₖ₊₁‖_p
  have step2 : P.qN (P.zof x) ≤ P.pN (P.yof (P.xnext x)) := by
    rw [← hz_xnext, P.z_dot x (P.xnext x)]
    calc (∑ i : Fin n, P.dp (P.yof x) i * (∑ j : Fin n, P.A i j * P.xnext x j))
        ≤ P.qN (P.dp (P.yof x)) *
            P.pN (fun i => ∑ j : Fin n, P.A i j * P.xnext x j) := P.holder _ _
      _ ≤ 1 * P.pN (P.yof (P.xnext x)) :=
          mul_le_mul_of_nonneg_right (P.dp_qunit _) (P.pN_nonneg _)
      _ = P.pN (P.yof (P.xnext x)) := one_mul _
  -- (iii)  ‖yₖ₊₁‖_p = ‖A xₖ₊₁‖_p ≤ ‖A‖_p ‖xₖ₊₁‖_p = ‖A‖_p   (‖xₖ₊₁‖_p = 1)
  have step3 : P.pN (P.yof (P.xnext x)) ≤ P.opP := by
    have hb := P.op_bound (P.xnext x)
    have hxn : P.pN (P.xnext x) = 1 := P.dq_punit _
    rw [hxn, mul_one] at hb
    exact hb
  exact ⟨step1, step2, step3⟩

/-- **Convergence-test equality** (Higham §15.2, p. 291).

    Because `‖yₖ‖_p = zₖᵀ xₖ ≤ ‖zₖ‖_q` always holds (Lemma 15.2(a) + Hölder,
    with `‖xₖ‖_p = 1`), the algorithm's test `‖zₖ‖_q ≤ zₖᵀ xₖ` is equivalent to
    the equality `‖zₖ‖_q = zₖᵀ xₖ`.  This is the observation Higham uses to note
    that the scalar convergence test is really testing the vector equation. -/
theorem convergence_test_iff (x : Fin n → ℝ) (hx : P.pN x = 1) :
    P.qN (P.zof x) ≤ (∑ j : Fin n, P.zof x j * x j)
      ↔ P.qN (P.zof x) = (∑ j : Fin n, P.zof x j * x j) := by
  have hle : (∑ j : Fin n, P.zof x j * x j) ≤ P.qN (P.zof x) := by
    rw [P.lemma152a x]
    exact (P.lemma152b x hx).1
  constructor
  · intro h; exact le_antisymm h hle
  · intro h; exact le_of_eq h

end PNormPair

/-- **Strictness in Lemma 15.2(b)** (Higham §15.2, p. 291).

    "The first inequality in (b) is strict if convergence is not obtained on the
    kth iteration."  Higham identifies (p. 291) the convergence test
    `‖zₖ‖_q ≤ zₖᵀ xₖ`, equivalently `‖zₖ‖_q ≤ ‖yₖ‖_p` by (a).  Its negation,
    `‖yₖ‖_p < ‖zₖ‖_q`, is precisely the strict first inequality.  We state this
    as the honest equivalence: non-convergence (`¬ ‖zₖ‖_q ≤ ‖yₖ‖_p`) is exactly
    the strict inequality `‖yₖ‖_p < ‖zₖ‖_q`.  Combined with
    `convergence_test_iff` (which, using `‖xₖ‖_p = 1`, identifies the test
    `‖zₖ‖_q ≤ zₖᵀ xₖ` with `‖zₖ‖_q ≤ ‖yₖ‖_p`), this is Higham's remark that the
    first inequality of (b) is strict precisely when the kth step does not
    converge. -/
theorem lemma152b_strict {n : ℕ} (P : PNormPair n) (x : Fin n → ℝ) :
    (¬ P.qN (P.zof x) ≤ P.pN (P.yof x)) ↔ P.pN (P.yof x) < P.qN (P.zof x) := by
  constructor
  · intro h; exact lt_of_not_ge h
  · intro h; exact not_le.mpr h

/-- **Lemma 15.2 for `p = 2`** (Higham §15.2, p. 290-291), stated directly in
    the 2-norm.  For a unit vector `x` (`‖x‖₂ = 1`):
      `‖A x‖₂ ≤ ‖z‖₂ ≤ ‖A xₖ₊₁‖₂ ≤ ‖A‖₂`,
    where `z = Aᵀ (Ax/‖Ax‖₂)` and `xₖ₊₁ = normalize₂(z)`, together with
    `(a) zᵀ x = ‖A x‖₂`.  Genuinely non-vacuous: it is `lemma152b` at the
    concrete instance `pNormPair_two`. -/
theorem lemma152_two {n : ℕ} (hn : 0 < n) (A : Fin n → Fin n → ℝ)
    (x : Fin n → ℝ) (hx : vecNorm2 x = 1) :
    (∑ j : Fin n, (pNormPair_two hn A).zof x j * x j)
        = vecNorm2 ((pNormPair_two hn A).yof x) ∧
    vecNorm2 ((pNormPair_two hn A).yof x) ≤ vecNorm2 ((pNormPair_two hn A).zof x) ∧
    vecNorm2 ((pNormPair_two hn A).zof x)
        ≤ vecNorm2 ((pNormPair_two hn A).yof ((pNormPair_two hn A).xnext x)) ∧
    vecNorm2 ((pNormPair_two hn A).yof ((pNormPair_two hn A).xnext x))
        ≤ opNorm2 A :=
  ⟨(pNormPair_two hn A).lemma152a x, (pNormPair_two hn A).lemma152b x hx⟩

/-- **Lemma 15.2 for `p = 1`** (Higham §15.2, p. 290-291), stated in the
    1-norm.  For a unit vector `x` (`‖x‖₁ = 1`):
      `(a) zᵀ x = ‖A x‖₁`  and
      `‖A x‖₁ ≤ ‖z‖_∞ ≤ ‖A xₖ₊₁‖₁ ≤ ‖A‖₁`,
    where `z = Aᵀ sign(Ax)` and `xₖ₊₁ = ±e_j`.  This is the mathematics
    behind the LAPACK 1-norm estimator (Algorithm 15.3 = specialization).
    Non-vacuous: `lemma152b` at `pNormPair_one`. -/
theorem lemma152_one {n : ℕ} (hn : 0 < n) (A : Fin n → Fin n → ℝ)
    (x : Fin n → ℝ) (hx : oneNormVec x = 1) :
    (∑ j : Fin n, (pNormPair_one hn A).zof x j * x j)
        = oneNormVec ((pNormPair_one hn A).yof x) ∧
    oneNormVec ((pNormPair_one hn A).yof x)
        ≤ infNormVec ((pNormPair_one hn A).zof x) ∧
    infNormVec ((pNormPair_one hn A).zof x)
        ≤ oneNormVec ((pNormPair_one hn A).yof ((pNormPair_one hn A).xnext x)) ∧
    oneNormVec ((pNormPair_one hn A).yof ((pNormPair_one hn A).xnext x))
        ≤ oneNorm A :=
  ⟨(pNormPair_one hn A).lemma152a x, (pNormPair_one hn A).lemma152b x hx⟩

end Ch15
end NumStability
