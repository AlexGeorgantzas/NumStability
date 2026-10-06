import Mathlib.Algebra.BigOperators.Group.Finset.Basic
import Mathlib.Algebra.BigOperators.Ring.Finset
import Mathlib.Algebra.Order.BigOperators.Group.Finset
import Mathlib.Data.Real.Basic
import Mathlib.LinearAlgebra.Matrix.Orthogonal
import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Ring
import NumStability.Algorithms.DotProduct
import NumStability.Algorithms.LU.GaussianElimination
import NumStability.Algorithms.LU.GrowthFactor
import NumStability.Algorithms.LU.LUSolve
import NumStability.Algorithms.LinearSystems.LU.Doolittle.Assembly.Core
import NumStability.Algorithms.LinearSystems.LU.Doolittle.Basic
import NumStability.Algorithms.LinearSystems.Triangular.BackSubstitution
import NumStability.Algorithms.LinearSystems.Triangular.ForwardSubstitution
import NumStability.Algorithms.MatMul
import NumStability.Algorithms.MatVec
import NumStability.Algorithms.TestMatrices.UpperTriangularStress
import NumStability.Analysis.Error.RoundingProducts.Core
import NumStability.Analysis.ForwardError
import NumStability.Analysis.MatrixAlgebra
import NumStability.Analysis.MatrixNorms.HadamardDeterminant
import NumStability.Analysis.Perturbation.LeastSquares.Wedin
import NumStability.Analysis.Rounding
import NumStability.FloatingPoint.Model
import NumStability.Source.Higham.Chapter09.Problems
import NumStability.Source.Higham.Chapter09.Section01
import NumStability.Source.Higham.Chapter09.Section02
import NumStability.Source.Higham.Chapter09.Section03
import NumStability.Source.Higham.Chapter09.Section04
import NumStability.Source.Higham.Chapter09.Section05
import NumStability.Source.Higham.Chapter09.Section06
import NumStability.Source.Higham.Chapter09.Section08
import NumStability.Source.Higham.Chapter09.Section10
import NumStability.Source.Higham.Chapter09.Section11
import NumStability.Source.Higham.Chapter14.Section03.LUFactorInversion.MethodD.MethodDUpperCertificate

/-!
# Chapter14 Section03 LUFactorInversion MethodB MethodsBC

Canonical destination for material split out of
`NumStability.Algorithms.Ch14MethodsBC` by wave W08 of the August 2026 repository reorganization.
Declaration names, statements and proofs are unchanged; only the
module they live in has changed. The historical module still
resolves and re-exports this one.
-/

open scoped BigOperators

namespace NumStability

namespace Ch14Ext

/-- The upper-triangular inverse used by full-matrix Method B. -/
noncomputable def ch14ext_methodBUpperInverse (n : ℕ) (fp : FPModel)
    (U : Fin n → Fin n → ℝ) : Fin n → Fin n → ℝ :=
  ch14ext_method2InvUpper n fp U

/-- **Method B, computed matrix (Higham p. 268).**

After computing `X_U` by the concrete upper Method 2 loop, solve
`X_hat L = X_U` from the right.  Row `i` is the back-substitution solve
`L^T (X_hat i)^T = (X_U i)^T`. -/
noncomputable def ch14ext_methodBComputedInverse (n : ℕ) (fp : FPModel)
    (L U : Fin n → Fin n → ℝ) : Fin n → Fin n → ℝ :=
  fun i =>
    fl_backSub fp n (fun a b => L b a)
      (fun a => ch14ext_methodBUpperInverse n fp U i a)

/-- A componentwise LU backward-error certificate can be weakened to a larger
nonnegative accumulator. -/
theorem ch14ext_LUBackwardError_mono {n : ℕ}
    {A L U : Fin n → Fin n → ℝ} {eps eps' : ℝ}
    (h : eps ≤ eps') (hLU : LUBackwardError n A L U eps) :
    LUBackwardError n A L U eps' where
  L_diag := hLU.L_diag
  L_upper_zero := hLU.L_upper_zero
  U_lower_zero := hLU.U_lower_zero
  backward_bound := by
    intro i j
    exact le_trans (hLU.backward_bound i j)
      (mul_le_mul_of_nonneg_right h
        (Finset.sum_nonneg fun k _ =>
          mul_nonneg (abs_nonneg (L i k)) (abs_nonneg (U k j))))

/-- The right-side triangular solve in Method B supplies its own
`X_hat L - X_U` certificate.

This is derived row by row from Higham Theorem 8.5
`backSub_backward_error`; no solve residual is assumed. -/
theorem ch14ext_methodB_right_solve_residual (n : ℕ) (fp : FPModel)
    (L U : Fin n → Fin n → ℝ)
    (hn : gammaValid fp n)
    (hLdiag : ∀ j : Fin n, L j j ≠ 0)
    (hLT : ∀ i j : Fin n, j.val > i.val → L i j = 0) :
    ∀ i j : Fin n,
      |∑ k : Fin n, ch14ext_methodBComputedInverse n fp L U i k * L k j -
          ch14ext_methodBUpperInverse n fp U i j| ≤
        gamma fp n *
          ∑ k : Fin n, |ch14ext_methodBComputedInverse n fp L U i k| * |L k j| := by
  intro i j
  obtain ⟨Delta, hDelta, hEq⟩ :=
    backSub_backward_error fp n (fun a b => L b a)
      (fun a => ch14ext_methodBUpperInverse n fp U i a)
      hLdiag (fun a b hab => hLT b a hab) hn
  have hEq' :
      (∑ k : Fin n, ch14ext_methodBComputedInverse n fp L U i k * L k j) +
          (∑ k : Fin n, Delta j k *
            ch14ext_methodBComputedInverse n fp L U i k) =
        ch14ext_methodBUpperInverse n fp U i j := by
    rw [← hEq j]
    rw [← Finset.sum_add_distrib]
    apply Finset.sum_congr rfl
    intro k _
    simp only [ch14ext_methodBComputedInverse]
    ring
  have hResidual :
      (∑ k : Fin n, ch14ext_methodBComputedInverse n fp L U i k * L k j) -
          ch14ext_methodBUpperInverse n fp U i j =
        -(∑ k : Fin n, Delta j k *
          ch14ext_methodBComputedInverse n fp L U i k) := by
    linarith [hEq']
  rw [hResidual, abs_neg]
  calc
    |∑ k : Fin n, Delta j k * ch14ext_methodBComputedInverse n fp L U i k|
        ≤ ∑ k : Fin n,
            |Delta j k * ch14ext_methodBComputedInverse n fp L U i k| :=
          Finset.abs_sum_le_sum_abs _ _
    _ = ∑ k : Fin n,
          |ch14ext_methodBComputedInverse n fp L U i k| * |Delta j k| := by
          apply Finset.sum_congr rfl
          intro k _
          rw [abs_mul, mul_comm]
    _ ≤ ∑ k : Fin n,
          |ch14ext_methodBComputedInverse n fp L U i k| *
            (gamma fp n * |L k j|) := by
          apply Finset.sum_le_sum
          intro k _
          exact mul_le_mul_of_nonneg_left (hDelta j k) (abs_nonneg _)
    _ = gamma fp n *
          ∑ k : Fin n, |ch14ext_methodBComputedInverse n fp L U i k| * |L k j| := by
          rw [Finset.mul_sum]
          apply Finset.sum_congr rfl
          intro k _
          ring

/-- Equation (14.18)'s algebraic composer at an arbitrary nonnegative
accumulator `eps`.

The hypotheses are local certificates, not the conclusion: LU factorization,
the upper inverse, and the right-side triangular solve.  This epsilon-generic
form is needed because the concrete Method 2 inverse is certified at
`gamma_(n+2)`, while the original repository wrapper fixed `gamma_n`. -/
theorem ch14ext_methodB_left_residual_eps {n : ℕ} (eps : ℝ) (heps : 0 ≤ eps)
    (A L U XU Xhat : Fin n → Fin n → ℝ)
    (hLU : LUBackwardError n A L U eps)
    (hXU : ∀ i j : Fin n,
      |∑ k : Fin n, XU i k * U k j - (if i = j then 1 else 0)| ≤
        eps * ∑ k : Fin n, |XU i k| * |U k j|)
    (hXL : ∀ i j : Fin n,
      |∑ k : Fin n, Xhat i k * L k j - XU i j| ≤
        eps * ∑ k : Fin n, |Xhat i k| * |L k j|) :
    ∀ i j : Fin n,
      |∑ k : Fin n, Xhat i k * A k j - (if i = j then 1 else 0)| ≤
        (3 * eps + eps ^ 2) *
          ∑ k1 : Fin n, |Xhat i k1| *
            (∑ k2 : Fin n, |L k1 k2| * |U k2 j|) := by
  intro i j
  let B := fun i' j' =>
    ∑ k1 : Fin n, |Xhat i' k1| *
      (∑ k2 : Fin n, |L k1 k2| * |U k2 j'|)
  have hLU_contrib : ∀ i' j' : Fin n,
      |∑ k : Fin n, Xhat i' k *
        (A k j' - ∑ l : Fin n, L k l * U l j')| ≤ eps * B i' j' := by
    intro i' j'
    calc
      |∑ k : Fin n, Xhat i' k *
          (A k j' - ∑ l : Fin n, L k l * U l j')|
          ≤ ∑ k : Fin n, |Xhat i' k| *
              |A k j' - ∑ l : Fin n, L k l * U l j'| := by
                calc
                  _ ≤ ∑ k : Fin n,
                      |Xhat i' k *
                        (A k j' - ∑ l : Fin n, L k l * U l j')| :=
                    Finset.abs_sum_le_sum_abs _ _
                  _ = _ := by
                    apply Finset.sum_congr rfl
                    intro k _
                    exact abs_mul _ _
      _ ≤ ∑ k : Fin n, |Xhat i' k| *
            (eps * ∑ l : Fin n, |L k l| * |U l j'|) := by
              apply Finset.sum_le_sum
              intro k _
              apply mul_le_mul_of_nonneg_left _ (abs_nonneg _)
              simpa [abs_sub_comm] using hLU.backward_bound k j'
      _ = eps * B i' j' := by
              simp only [B, Finset.mul_sum]
              apply Finset.sum_congr rfl
              intro k _
              ring_nf
  have hE1U : ∀ i' j' : Fin n,
      |∑ k : Fin n,
        (∑ l : Fin n, Xhat i' l * L l k - XU i' k) * U k j'| ≤
        eps * B i' j' := by
    intro i' j'
    calc
      |∑ k : Fin n,
          (∑ l : Fin n, Xhat i' l * L l k - XU i' k) * U k j'|
          ≤ ∑ k : Fin n,
              |∑ l : Fin n, Xhat i' l * L l k - XU i' k| * |U k j'| := by
                calc
                  _ ≤ ∑ k : Fin n,
                      |(∑ l : Fin n, Xhat i' l * L l k - XU i' k) * U k j'| :=
                    Finset.abs_sum_le_sum_abs _ _
                  _ = _ := by
                    apply Finset.sum_congr rfl
                    intro k _
                    exact abs_mul _ _
      _ ≤ ∑ k : Fin n,
            (eps * ∑ l : Fin n, |Xhat i' l| * |L l k|) * |U k j'| := by
              apply Finset.sum_le_sum
              intro k _
              exact mul_le_mul_of_nonneg_right (hXL i' k) (abs_nonneg _)
      _ = eps * B i' j' := by
              have hfact : ∀ k : Fin n,
                  (eps * ∑ l : Fin n, |Xhat i' l| * |L l k|) * |U k j'| =
                    eps * ((∑ l : Fin n, |Xhat i' l| * |L l k|) * |U k j'|) :=
                fun _ => by ring
              simp_rw [hfact, ← Finset.mul_sum, Finset.sum_mul]
              congr 1
              simp only [B]
              rw [Finset.sum_comm]
              apply Finset.sum_congr rfl
              intro l _
              simp_rw [mul_assoc]
              rw [← Finset.mul_sum]
  have hXU_bound : ∀ i' k : Fin n,
      |XU i' k| ≤ (1 + eps) *
        ∑ l : Fin n, |Xhat i' l| * |L l k| := by
    intro i' k
    let S := ∑ l : Fin n, |Xhat i' l| * |L l k|
    have hsum : |∑ l : Fin n, Xhat i' l * L l k| ≤ S := by
      dsimp [S]
      calc
        _ ≤ ∑ l : Fin n, |Xhat i' l * L l k| :=
          Finset.abs_sum_le_sum_abs _ _
        _ = _ := by
          apply Finset.sum_congr rfl
          intro l _
          exact abs_mul _ _
    have herr := hXL i' k
    have htri : |XU i' k| ≤
        |∑ l : Fin n, Xhat i' l * L l k| +
          |∑ l : Fin n, Xhat i' l * L l k - XU i' k| := by
      have h := abs_add_le
        (XU i' k - ∑ l : Fin n, Xhat i' l * L l k)
        (∑ l : Fin n, Xhat i' l * L l k)
      rw [sub_add_cancel, abs_sub_comm] at h
      linarith
    dsimp [S] at hsum ⊢
    linarith
  have hE2 : ∀ i' j' : Fin n,
      |∑ k : Fin n, XU i' k * U k j' - (if i' = j' then 1 else 0)| ≤
        eps * (1 + eps) * B i' j' := by
    intro i' j'
    calc
      |∑ k : Fin n, XU i' k * U k j' - (if i' = j' then 1 else 0)|
          ≤ eps * ∑ k : Fin n, |XU i' k| * |U k j'| := hXU i' j'
      _ ≤ eps * ∑ k : Fin n,
          ((1 + eps) * ∑ l : Fin n, |Xhat i' l| * |L l k|) * |U k j'| := by
            apply mul_le_mul_of_nonneg_left _ heps
            apply Finset.sum_le_sum
            intro k _
            exact mul_le_mul_of_nonneg_right (hXU_bound i' k) (abs_nonneg _)
      _ = eps * (1 + eps) * B i' j' := by
            rw [show eps * ∑ k : Fin n,
                ((1 + eps) * ∑ l : Fin n, |Xhat i' l| * |L l k|) * |U k j'| =
                eps * (1 + eps) * ∑ k : Fin n,
                  (∑ l : Fin n, |Xhat i' l| * |L l k|) * |U k j'| from by
              rw [Finset.mul_sum, Finset.mul_sum]
              apply Finset.sum_congr rfl
              intro k _
              ring]
            congr 1
            simp only [B]
            simp_rw [Finset.sum_mul]
            rw [Finset.sum_comm]
            apply Finset.sum_congr rfl
            intro l _
            simp_rw [mul_assoc]
            rw [← Finset.mul_sum]
  have hFub :
      ∑ k : Fin n, (∑ l : Fin n, Xhat i l * L l k) * U k j =
        ∑ k : Fin n, Xhat i k * (∑ l : Fin n, L k l * U l j) := by
    simp_rw [Finset.sum_mul, Finset.mul_sum]
    rw [Finset.sum_comm]
    apply Finset.sum_congr rfl
    intro k _
    apply Finset.sum_congr rfl
    intro l _
    ring
  have hDecomp :
      ∑ k : Fin n, Xhat i k * A k j - (if i = j then 1 else 0) =
        (∑ k : Fin n, XU i k * U k j - (if i = j then 1 else 0)) +
        (∑ k : Fin n,
          (∑ l : Fin n, Xhat i l * L l k - XU i k) * U k j) +
        (∑ k : Fin n,
          Xhat i k * (A k j - ∑ l : Fin n, L k l * U l j)) := by
    simp_rw [sub_mul, Finset.sum_sub_distrib, mul_sub, Finset.sum_sub_distrib]
    linarith [hFub]
  rw [hDecomp]
  have h1 := hE2 i j
  have h2 := hE1U i j
  have h3 := hLU_contrib i j
  calc
    |(∑ k : Fin n, XU i k * U k j - (if i = j then 1 else 0)) +
        (∑ k : Fin n,
          (∑ l : Fin n, Xhat i l * L l k - XU i k) * U k j) +
        (∑ k : Fin n,
          Xhat i k * (A k j - ∑ l : Fin n, L k l * U l j))|
        ≤ |∑ k : Fin n, XU i k * U k j - (if i = j then 1 else 0)| +
          |∑ k : Fin n,
            (∑ l : Fin n, Xhat i l * L l k - XU i k) * U k j| +
          |∑ k : Fin n,
            Xhat i k * (A k j - ∑ l : Fin n, L k l * U l j)| := by
              rw [add_assoc]
              calc
                _ ≤ |∑ k : Fin n, XU i k * U k j -
                        (if i = j then 1 else 0)| +
                      |(∑ k : Fin n,
                        (∑ l : Fin n, Xhat i l * L l k - XU i k) * U k j) +
                        (∑ k : Fin n,
                          Xhat i k * (A k j - ∑ l : Fin n, L k l * U l j))| :=
                    abs_add_le _ _
                _ ≤ _ := by
                  have h := abs_add_le
                    (∑ k : Fin n,
                      (∑ l : Fin n, Xhat i l * L l k - XU i k) * U k j)
                    (∑ k : Fin n,
                      Xhat i k * (A k j - ∑ l : Fin n, L k l * U l j))
                  linarith
    _ ≤ eps * (1 + eps) * B i j + eps * B i j + eps * B i j := by
          linarith
    _ = (3 * eps + eps ^ 2) * B i j := by ring

/-- **Higham equation (14.18), concrete Method B.**

The upper inverse and the right-side solve are the concrete rounded algorithms
above.  The only non-algorithmic input is the standard LU backward-error
certificate for the computed factors.  Its `gamma_n` coefficient is weakened
internally to the shared honest accumulator `gamma_(n+2)`. -/
theorem ch14ext_methodB_eq14_18 (n : ℕ) (fp : FPModel)
    (A L U : Fin n → Fin n → ℝ)
    (hn2 : gammaValid fp (n + 2))
    (hLdiag : ∀ j : Fin n, L j j ≠ 0)
    (hLT : ∀ i j : Fin n, j.val > i.val → L i j = 0)
    (hUdiag : ∀ j : Fin n, U j j ≠ 0)
    (hUT : ∀ i j : Fin n, j.val < i.val → U i j = 0)
    (hLU : LUBackwardError n A L U (gamma fp n)) :
    ∀ i j : Fin n,
      |∑ k : Fin n, ch14ext_methodBComputedInverse n fp L U i k * A k j -
          (if i = j then 1 else 0)| ≤
        (3 * gamma fp (n + 2) + gamma fp (n + 2) ^ 2) *
          ∑ k1 : Fin n, |ch14ext_methodBComputedInverse n fp L U i k1| *
            (∑ k2 : Fin n, |L k1 k2| * |U k2 j|) := by
  have hn : gammaValid fp n := gammaValid_mono fp (by omega) hn2
  have hmono : gamma fp n ≤ gamma fp (n + 2) := gamma_mono fp (by omega) hn2
  have hLU' : LUBackwardError n A L U (gamma fp (n + 2)) :=
    ch14ext_LUBackwardError_mono hmono hLU
  have hXU := ch14ext_method2Upper_left_residual n fp U hn2 hUT hUdiag
  have hXL0 := ch14ext_methodB_right_solve_residual n fp L U hn hLdiag hLT
  have hXL : ∀ i j : Fin n,
      |∑ k : Fin n, ch14ext_methodBComputedInverse n fp L U i k * L k j -
          ch14ext_methodBUpperInverse n fp U i j| ≤
        gamma fp (n + 2) *
          ∑ k : Fin n, |ch14ext_methodBComputedInverse n fp L U i k| * |L k j| := by
    intro i j
    exact le_trans (hXL0 i j)
      (mul_le_mul_of_nonneg_right hmono
        (Finset.sum_nonneg fun k _ =>
          mul_nonneg (abs_nonneg _) (abs_nonneg _)))
  exact ch14ext_methodB_left_residual_eps (gamma fp (n + 2))
    (gamma_nonneg fp hn2) A L U
    (ch14ext_methodBUpperInverse n fp U)
    (ch14ext_methodBComputedInverse n fp L U) hLU' hXU hXL

/-- **Implementation-facing Method B endpoint for equation (14.18).**

The LU certificate is derived from the concrete rounded Doolittle
factorization, exactly as in the Method D Doolittle endpoint.  Thus the only
extra successful-factorization condition is a nonzero diagonal for `U`; the
unit diagonal and triangular shapes of `L` and `U` come from `hD`. -/
theorem ch14ext_methodB_eq14_18_doolittle (n : ℕ) (fp : FPModel)
    (A L U : Fin n → Fin n → ℝ)
    (hn2 : gammaValid fp (n + 2))
    (hUnz : ∀ j : Fin n, U j j ≠ 0)
    (hD : DoolittleLU n A L U fp) :
    ∀ i j : Fin n,
      |∑ k : Fin n, ch14ext_methodBComputedInverse n fp L U i k * A k j -
          (if i = j then 1 else 0)| ≤
        (3 * gamma fp (n + 2) + gamma fp (n + 2) ^ 2) *
          ∑ k1 : Fin n, |ch14ext_methodBComputedInverse n fp L U i k1| *
            (∑ k2 : Fin n, |L k1 k2| * |U k2 j|) := by
  have hn : gammaValid fp n := gammaValid_mono fp (by omega) hn2
  have hLU : LUBackwardError n A L U (gamma fp n) :=
    DoolittleLU.to_LUBackwardError n fp A L U hn hD
  exact ch14ext_methodB_eq14_18 n fp A L U hn2
    (fun j => by rw [hD.L_diag j]; norm_num)
    hD.L_upper_zero hUnz hD.U_lower_zero hLU

end Ch14Ext
end NumStability
