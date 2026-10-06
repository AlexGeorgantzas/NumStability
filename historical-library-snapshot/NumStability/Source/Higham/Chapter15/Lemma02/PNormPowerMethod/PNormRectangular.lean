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
import NumStability.Algorithms.NormEstimation.OneNorm.PowerMethod.CondEstimation
import NumStability.Algorithms.NormEstimation.PNorm.OneAndInfinityNorms.Rectangular
import NumStability.Algorithms.NormEstimation.PNorm.Rectangular.PNormRectangular
import NumStability.Analysis.MatrixAlgebra
import NumStability.Analysis.MatrixNorms.Lp
import NumStability.Analysis.SingularValues.Realification

/-!
# Chapter15 Lemma02 PNormPowerMethod PNormRectangular

Canonical destination for material split out of
`NumStability.Algorithms.PNormPowerMethodRect` by wave W10 of the August 2026 repository reorganization.
Declaration names, statements and proofs are unchanged; only the
module they live in has changed. The historical module still
resolves and re-exports this one.
-/

namespace NumStability

open scoped BigOperators

open Ch15

namespace RectPNormPair

variable {m n : ℕ} (P : RectPNormPair m n)

/-- Higham Lemma 15.2(a), at its literal `m x n` source dimensions. -/
theorem higham15_lemma15_2a_rectangular (x : Fin n → ℝ) :
    (∑ j : Fin n, P.zof x j * x j) = P.pOut (P.yof x) := by
  rw [P.z_dot x x]
  exact P.dpOut_attains _

/-- Higham Lemma 15.2(b), at its literal `m x n` source dimensions. -/
theorem higham15_lemma15_2b_rectangular (x : Fin n → ℝ)
    (hx : P.pIn x = 1) :
    P.pOut (P.yof x) ≤ P.qIn (P.zof x) ∧
      P.qIn (P.zof x) ≤ P.pOut (P.yof (P.xnext x)) ∧
        P.pOut (P.yof (P.xnext x)) ≤ P.opP := by
  have hfirst : P.pOut (P.yof x) ≤ P.qIn (P.zof x) := by
    rw [← P.higham15_lemma15_2a_rectangular x]
    calc
      (∑ j : Fin n, P.zof x j * x j) ≤
          P.qIn (P.zof x) * P.pIn x := P.holderIn _ _
      _ = P.qIn (P.zof x) := by rw [hx, mul_one]
  have hznext :
      (∑ j : Fin n, P.zof x j * P.xnext x j) = P.qIn (P.zof x) := by
    unfold xnext
    rw [show (∑ j : Fin n, P.zof x j * P.dqIn (P.zof x) j) =
        ∑ j : Fin n, P.dqIn (P.zof x) j * P.zof x j by
      apply Finset.sum_congr rfl
      intro j _hj
      ring]
    exact P.dqIn_attains _
  have hmiddle : P.qIn (P.zof x) ≤ P.pOut (P.yof (P.xnext x)) := by
    rw [← hznext, P.z_dot x (P.xnext x)]
    calc
      (∑ i : Fin m, P.dpOut (P.yof x) i * P.yof (P.xnext x) i) ≤
          P.qOut (P.dpOut (P.yof x)) * P.pOut (P.yof (P.xnext x)) :=
        P.holderOut _ _
      _ ≤ 1 * P.pOut (P.yof (P.xnext x)) :=
        mul_le_mul_of_nonneg_right (P.dpOut_qunit _) (P.pOut_nonneg _)
      _ = P.pOut (P.yof (P.xnext x)) := one_mul _
  have hlast : P.pOut (P.yof (P.xnext x)) ≤ P.opP := by
    have h := P.op_bound (P.xnext x)
    have hunit : P.pIn (P.xnext x) = 1 := by
      simp only [xnext]
      exact P.dqIn_punit _
    rw [hunit, mul_one] at h
    simpa [yof] using h
  exact ⟨hfirst, hmiddle, hlast⟩

/-- Package of both parts of Higham Lemma 15.2 at rectangular strength. -/
theorem higham15_lemma15_2_rectangular (x : Fin n → ℝ)
    (hx : P.pIn x = 1) :
    (∑ j : Fin n, P.zof x j * x j) = P.pOut (P.yof x) ∧
      P.pOut (P.yof x) ≤ P.qIn (P.zof x) ∧
      P.qIn (P.zof x) ≤ P.pOut (P.yof (P.xnext x)) ∧
      P.pOut (P.yof (P.xnext x)) ≤ P.opP := by
  exact ⟨P.higham15_lemma15_2a_rectangular x,
    P.higham15_lemma15_2b_rectangular x hx⟩

/-- The first inequality is strict exactly when the loop does not stop. -/
theorem higham15_lemma15_2_rectangular_strict (x : Fin n → ℝ)
    :
    ¬ P.StopsAt x ↔ P.pOut (P.yof x) < P.qIn (P.zof x) := by
  have heq := P.higham15_lemma15_2a_rectangular x
  simp only [StopsAt, heq]
  exact not_le

theorem gammaSeq_mono (x0 : Fin n → ℝ) (hx0 : P.pIn x0 = 1) (k : ℕ) :
    P.gammaSeq x0 k ≤ P.gammaSeq x0 (k + 1) := by
  have hk := P.xseq_punit x0 hx0 k
  have h := P.higham15_lemma15_2b_rectangular (P.xseq x0 k) hk
  exact h.1.trans (by simpa [gammaSeq, xseq] using h.2.1)

/-- Direct source-strength rectangular Lemma 15.2 for `p=1`. -/
theorem higham15_lemma15_2_rectangular_one {m n : ℕ} (hn : 0 < n)
    (A : Fin m → Fin n → ℝ) (x : Fin n → ℝ)
    (hx : oneNormVec x = 1) :
    (∑ j : Fin n, (one hn A).zof x j * x j) =
        oneNormVec ((one hn A).yof x) ∧
      oneNormVec ((one hn A).yof x) ≤ infNormVec ((one hn A).zof x) ∧
      infNormVec ((one hn A).zof x) ≤
        oneNormVec ((one hn A).yof ((one hn A).xnext x)) ∧
      oneNormVec ((one hn A).yof ((one hn A).xnext x)) ≤ oneNormRect A :=
  (one hn A).higham15_lemma15_2_rectangular x hx

/-- Direct source-strength rectangular Lemma 15.2 for `p=infinity`. -/
theorem higham15_lemma15_2_rectangular_infinity {m n : ℕ}
    (hm : 0 < m) (hn : 0 < n)
    (A : Fin m → Fin n → ℝ) (x : Fin n → ℝ)
    (hx : infNormVec x = 1) :
    (∑ j : Fin n, (infinity hm hn A).zof x j * x j) =
        infNormVec ((infinity hm hn A).yof x) ∧
      infNormVec ((infinity hm hn A).yof x) ≤
        oneNormVec ((infinity hm hn A).zof x) ∧
      oneNormVec ((infinity hm hn A).zof x) ≤
        infNormVec ((infinity hm hn A).yof ((infinity hm hn A).xnext x)) ∧
      infNormVec ((infinity hm hn A).yof ((infinity hm hn A).xnext x)) ≤
        infNormRect A :=
  (infinity hm hn A).higham15_lemma15_2_rectangular x hx

end RectPNormPair
end NumStability
