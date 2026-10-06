/-
Higham, *Accuracy and Stability of Numerical Algorithms*, 2nd ed.,
Chapter 14 ("Matrix Inversion"), Sections 14.3.2-14.3.3, equations
(14.18)-(14.19), pp. 268-269.

This extension supplies computed objects for the two full-matrix inversion
methods whose original repository wrappers only accepted their final residual
certificates as hypotheses.

* Method B computes an upper-triangular inverse by the concrete upper Method 2
  loop, then solves X L = X_U row by row with `fl_backSub` on L^T.  Both local
  residual certificates are derived from the floating-point model and composed
  with the LU backward error at the honest accumulator gamma_(n+2).
* Method C implements the literal reverse loop printed on p. 269: each stage
  performs a rounded column dot product, a rounded row dot product and division,
  and the rounded diagonal reciprocal/dot/subtraction update.  Local rounding
  certificates are composed by scalar-leading block induction into the complete
  whole-loop mixed residual (14.19), with no residual hypothesis on any newly
  computed row, column, diagonal, or final result.
-/

import NumStability.Algorithms.Ch14MethodDUpperCertificate
import NumStability.Algorithms.DotProduct
import NumStability.Algorithms.LU.Doolittle
import NumStability.Algorithms.LinearSystems.Triangular.BackSubstitution

namespace NumStability.Ch14Ext

open scoped BigOperators

/-! ## Method B: concrete upper inverse followed by a right-side solve -/

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

/-! ## Method C: one literal reverse-loop stage -/

/-- Method C's column update at a scalar-leading reverse stage:
`x21 = fl(-X22*l21)`. -/
noncomputable def ch14ext_methodCStageColumn (fp : FPModel) (m : ℕ)
    (X22 : Fin m → Fin m → ℝ) (l21 : Fin m → ℝ) : Fin m → ℝ :=
  fun i => fl_dotProduct fp m (fun q => -X22 i q) l21

/-- Rounded numerator in Method C's row update, `fl(-u12^T*X22)`. -/
noncomputable def ch14ext_methodCStageRowNumerator (fp : FPModel) (m : ℕ)
    (u12 : Fin m → ℝ) (X22 : Fin m → Fin m → ℝ) : Fin m → ℝ :=
  fun j => fl_dotProduct fp m (fun q => -u12 q) (fun q => X22 q j)

/-- Method C's row update, including the printed division by `u11`. -/
noncomputable def ch14ext_methodCStageRow (fp : FPModel) (m : ℕ)
    (u11 : ℝ) (u12 : Fin m → ℝ) (X22 : Fin m → Fin m → ℝ) : Fin m → ℝ :=
  fun j => fp.fl_div (ch14ext_methodCStageRowNumerator fp m u12 X22 j) u11

/-- Rounded dot product used by Method C's diagonal update. -/
noncomputable def ch14ext_methodCStageDiagDot (fp : FPModel) (m : ℕ)
    (u11 : ℝ) (u12 : Fin m → ℝ) (X22 : Fin m → Fin m → ℝ)
    (l21 : Fin m → ℝ) : ℝ :=
  fl_dotProduct fp m (ch14ext_methodCStageRow fp m u11 u12 X22) l21

/-- Method C's diagonal update exactly as printed on p. 269:
`x11 = fl(fl(1/u11) - fl(x12^T*l21))`. -/
noncomputable def ch14ext_methodCStageDiag (fp : FPModel) (m : ℕ)
    (u11 : ℝ) (u12 : Fin m → ℝ) (X22 : Fin m → Fin m → ℝ)
    (l21 : Fin m → ℝ) : ℝ :=
  fp.fl_sub (fp.fl_div 1 u11)
    (ch14ext_methodCStageDiagDot fp m u11 u12 X22 l21)

/-- Local column-equation defect of a Method C reverse stage. -/
noncomputable def ch14ext_methodCStageColumnResidual (fp : FPModel) (m : ℕ)
    (X22 : Fin m → Fin m → ℝ) (l21 : Fin m → ℝ) (i : Fin m) : ℝ :=
  ch14ext_methodCStageColumn fp m X22 l21 i +
    ∑ q : Fin m, X22 i q * l21 q

/-- Local row-equation defect of a Method C reverse stage. -/
noncomputable def ch14ext_methodCStageRowResidual (fp : FPModel) (m : ℕ)
    (u11 : ℝ) (u12 : Fin m → ℝ) (X22 : Fin m → Fin m → ℝ)
    (j : Fin m) : ℝ :=
  u11 * ch14ext_methodCStageRow fp m u11 u12 X22 j +
    ∑ q : Fin m, u12 q * X22 q j

/-- Local diagonal-equation defect of a Method C reverse stage. -/
noncomputable def ch14ext_methodCStageDiagResidual (fp : FPModel) (m : ℕ)
    (u11 : ℝ) (u12 : Fin m → ℝ) (X22 : Fin m → Fin m → ℝ)
    (l21 : Fin m → ℝ) : ℝ :=
  u11 * (ch14ext_methodCStageDiag fp m u11 u12 X22 l21 +
    ∑ q : Fin m, ch14ext_methodCStageRow fp m u11 u12 X22 q * l21 q) - 1

/-- The rounded column update derives its local residual directly from the dot
product error theorem. -/
theorem ch14ext_methodCStageColumn_residual_bound (fp : FPModel) (m : ℕ)
    (X22 : Fin m → Fin m → ℝ) (l21 : Fin m → ℝ)
    (hm : gammaValid fp m) (i : Fin m) :
    |ch14ext_methodCStageColumnResidual fp m X22 l21 i| ≤
      gamma fp m * ∑ q : Fin m, |X22 i q| * |l21 q| := by
  have h := dotProduct_error_bound fp m (fun q => -X22 i q) l21 hm
  simpa [ch14ext_methodCStageColumnResidual, ch14ext_methodCStageColumn,
    Finset.sum_neg_distrib, abs_neg] using h

/-- The rounded row dot product followed by rounded division derives the local
row equation with the accumulated coefficient `gamma_(m+1)`. -/
theorem ch14ext_methodCStageRow_residual_bound (fp : FPModel) (m : ℕ)
    (u11 : ℝ) (u12 : Fin m → ℝ) (X22 : Fin m → Fin m → ℝ)
    (hu11 : u11 ≠ 0) (hm1 : gammaValid fp (m + 1)) (j : Fin m) :
    |ch14ext_methodCStageRowResidual fp m u11 u12 X22 j| ≤
      gamma fp (m + 1) * ∑ q : Fin m, |u12 q| * |X22 q j| := by
  let t := ch14ext_methodCStageRowNumerator fp m u12 X22 j
  let S := ∑ q : Fin m, u12 q * X22 q j
  let B := ∑ q : Fin m, |u12 q| * |X22 q j|
  have hm : gammaValid fp m := gammaValid_mono fp (by omega) hm1
  have hgamma_m : 0 ≤ gamma fp m := gamma_nonneg fp hm
  have hB : 0 ≤ B :=
    Finset.sum_nonneg fun q _ => mul_nonneg (abs_nonneg _) (abs_nonneg _)
  have hdot0 := dotProduct_error_bound fp m (fun q => -u12 q) (fun q => X22 q j) hm
  have hdot : |t + S| ≤ gamma fp m * B := by
    simpa [t, S, B, ch14ext_methodCStageRowNumerator,
      Finset.sum_neg_distrib, abs_neg] using hdot0
  have hS : |S| ≤ B := by
    dsimp [S, B]
    calc
      _ ≤ ∑ q : Fin m, |u12 q * X22 q j| := Finset.abs_sum_le_sum_abs _ _
      _ = _ := by
        apply Finset.sum_congr rfl
        intro q _
        exact abs_mul _ _
  have ht : |t| ≤ (1 + gamma fp m) * B := by
    have htri : |t| ≤ |t + S| + |S| := by
      have h := abs_add_le (t + S) (-S)
      simpa [abs_neg] using h
    linarith
  obtain ⟨delta, hdelta, hdiv⟩ := fp.model_div t u11 hu11
  have hurow :
      u11 * ch14ext_methodCStageRow fp m u11 u12 X22 j = t * (1 + delta) := by
    simp only [ch14ext_methodCStageRow, t] at hdiv ⊢
    rw [hdiv]
    field_simp [hu11]
  have hres :
      ch14ext_methodCStageRowResidual fp m u11 u12 X22 j =
        (t + S) + delta * t := by
    simp only [ch14ext_methodCStageRowResidual, S]
    rw [hurow]
    ring
  have hdeltaTerm : |delta * t| ≤ fp.u * ((1 + gamma fp m) * B) := by
    rw [abs_mul]
    exact mul_le_mul hdelta ht (abs_nonneg t) fp.u_nonneg
  have hcoef :
      gamma fp m + fp.u * (1 + gamma fp m) ≤ gamma fp (m + 1) := by
    have h1valid : gammaValid fp 1 := gammaValid_mono fp (by omega) hm1
    have hu1 : fp.u ≤ gamma fp 1 := u_le_gamma fp one_pos h1valid
    have hsum := gamma_sum_le fp m 1 hm1
    have hone : 0 ≤ 1 + gamma fp m := by linarith
    have hmul : fp.u * (1 + gamma fp m) ≤
        gamma fp 1 * (1 + gamma fp m) :=
      mul_le_mul_of_nonneg_right hu1 hone
    calc
      gamma fp m + fp.u * (1 + gamma fp m)
          ≤ gamma fp m + gamma fp 1 * (1 + gamma fp m) := by
            linarith [hmul]
      _ = gamma fp m + gamma fp 1 + gamma fp m * gamma fp 1 := by ring
      _ ≤ gamma fp (m + 1) := hsum
  rw [hres]
  calc
    |(t + S) + delta * t| ≤ |t + S| + |delta * t| := abs_add_le _ _
    _ ≤ gamma fp m * B + fp.u * ((1 + gamma fp m) * B) :=
      add_le_add hdot hdeltaTerm
    _ = (gamma fp m + fp.u * (1 + gamma fp m)) * B := by ring
    _ ≤ gamma fp (m + 1) * B := mul_le_mul_of_nonneg_right hcoef hB

/-- Explicit local budget for Method C's rounded diagonal update.  It records
the reciprocal error, the dot-product error, and the final subtraction error
separately; every term is generated by a modeled rounded operation. -/
noncomputable def ch14ext_methodCStageDiagBudget (fp : FPModel) (m : ℕ)
    (u11 : ℝ) (u12 : Fin m → ℝ) (X22 : Fin m → Fin m → ℝ)
    (l21 : Fin m → ℝ) : ℝ :=
  fp.u +
    |u11| * (gamma fp m *
      ∑ q : Fin m, |ch14ext_methodCStageRow fp m u11 u12 X22 q| * |l21 q|) +
    |u11| * fp.u *
      (|fp.fl_div 1 u11| +
        |ch14ext_methodCStageDiagDot fp m u11 u12 X22 l21|)

/-- The printed reciprocal/dot/subtraction diagonal update derives its local
equation defect from the three corresponding floating-point model laws. -/
theorem ch14ext_methodCStageDiag_residual_bound (fp : FPModel) (m : ℕ)
    (u11 : ℝ) (u12 : Fin m → ℝ) (X22 : Fin m → Fin m → ℝ)
    (l21 : Fin m → ℝ) (hu11 : u11 ≠ 0) (hm : gammaValid fp m) :
    |ch14ext_methodCStageDiagResidual fp m u11 u12 X22 l21| ≤
      ch14ext_methodCStageDiagBudget fp m u11 u12 X22 l21 := by
  let r := fp.fl_div 1 u11
  let t := ch14ext_methodCStageDiagDot fp m u11 u12 X22 l21
  let S := ∑ q : Fin m,
    ch14ext_methodCStageRow fp m u11 u12 X22 q * l21 q
  let B := ∑ q : Fin m,
    |ch14ext_methodCStageRow fp m u11 u12 X22 q| * |l21 q|
  obtain ⟨deltaR, hdeltaR, hrecip⟩ := fp.model_div 1 u11 hu11
  obtain ⟨deltaS, hdeltaS, hsub⟩ := fp.model_sub r t
  have hdot0 := dotProduct_error_bound fp m
    (ch14ext_methodCStageRow fp m u11 u12 X22) l21 hm
  have hdot : |t - S| ≤ gamma fp m * B := by
    simpa [t, S, B, ch14ext_methodCStageDiagDot] using hdot0
  have hur : u11 * r = 1 + deltaR := by
    dsimp [r]
    rw [hrecip]
    field_simp [hu11]
  have hx :
      ch14ext_methodCStageDiag fp m u11 u12 X22 l21 =
        (r - t) * (1 + deltaS) := by
    simpa [ch14ext_methodCStageDiag, r, t] using hsub
  have hres :
      ch14ext_methodCStageDiagResidual fp m u11 u12 X22 l21 =
        deltaR - u11 * (t - S) + u11 * deltaS * (r - t) := by
    simp only [ch14ext_methodCStageDiagResidual, S]
    rw [hx]
    calc
      u11 * ((r - t) * (1 + deltaS) +
          ∑ q : Fin m, ch14ext_methodCStageRow fp m u11 u12 X22 q * l21 q) - 1 =
          (u11 * r - 1) - u11 * (t -
            ∑ q : Fin m, ch14ext_methodCStageRow fp m u11 u12 X22 q * l21 q) +
              u11 * deltaS * (r - t) := by ring
      _ = deltaR - u11 * (t -
            ∑ q : Fin m, ch14ext_methodCStageRow fp m u11 u12 X22 q * l21 q) +
              u11 * deltaS * (r - t) := by rw [hur]; ring
  have hrt : |r - t| ≤ |r| + |t| := abs_sub r t
  have hmiddle : |u11 * (t - S)| ≤ |u11| * (gamma fp m * B) := by
    rw [abs_mul]
    exact mul_le_mul_of_nonneg_left hdot (abs_nonneg _)
  have hlast : |u11 * deltaS * (r - t)| ≤
      |u11| * fp.u * (|r| + |t|) := by
    calc
      |u11 * deltaS * (r - t)| = |u11| * |deltaS| * |r - t| := by
        simp only [abs_mul]
      _ ≤ |u11| * fp.u * |r - t| := by
        exact mul_le_mul_of_nonneg_right
          (mul_le_mul_of_nonneg_left hdeltaS (abs_nonneg u11)) (abs_nonneg _)
      _ ≤ |u11| * fp.u * (|r| + |t|) := by
        exact mul_le_mul_of_nonneg_left hrt
          (mul_nonneg (abs_nonneg u11) fp.u_nonneg)
  rw [hres]
  calc
    |deltaR - u11 * (t - S) + u11 * deltaS * (r - t)|
        ≤ |deltaR| + |u11 * (t - S)| + |u11 * deltaS * (r - t)| := by
          linarith [abs_add_le (deltaR - u11 * (t - S))
            (u11 * deltaS * (r - t)), abs_sub deltaR (u11 * (t - S))]
    _ ≤ fp.u + |u11| * (gamma fp m * B) +
          |u11| * fp.u * (|r| + |t|) :=
      add_le_add (add_le_add hdeltaR hmiddle) hlast
    _ = ch14ext_methodCStageDiagBudget fp m u11 u12 X22 l21 := by
      simp [ch14ext_methodCStageDiagBudget, r, t, B]

/-! ### Exact recurrence-to-mixed-residual decompositions -/

/-- The newly exposed `(1,1)` block of `U X L - I` is the local diagonal
defect plus the upper row applied to the local column defects. -/
theorem ch14ext_methodCStage_topLeft_decomposition (fp : FPModel) (m : ℕ)
    (u11 : ℝ) (u12 l21 : Fin m → ℝ) (X22 : Fin m → Fin m → ℝ) :
    u11 *
        (ch14ext_methodCStageDiag fp m u11 u12 X22 l21 +
          ∑ q : Fin m,
            ch14ext_methodCStageRow fp m u11 u12 X22 q * l21 q) +
        ∑ p : Fin m, u12 p *
          (ch14ext_methodCStageColumn fp m X22 l21 p +
            ∑ q : Fin m, X22 p q * l21 q) - 1 =
      ch14ext_methodCStageDiagResidual fp m u11 u12 X22 l21 +
        ∑ p : Fin m, u12 p *
          ch14ext_methodCStageColumnResidual fp m X22 l21 p := by
  simp only [ch14ext_methodCStageDiagResidual,
    ch14ext_methodCStageColumnResidual]
  ring_nf

/-- The newly exposed top-right block of `U X L - I` is the local row defect
postmultiplied by the trailing lower-triangular block. -/
theorem ch14ext_methodCStage_topRight_decomposition (fp : FPModel) (m : ℕ)
    (u11 : ℝ) (u12 : Fin m → ℝ) (X22 L22 : Fin m → Fin m → ℝ)
    (j : Fin m) :
    ∑ p : Fin m,
        (u11 * ch14ext_methodCStageRow fp m u11 u12 X22 p +
          ∑ q : Fin m, u12 q * X22 q p) * L22 p j =
      ∑ p : Fin m,
        ch14ext_methodCStageRowResidual fp m u11 u12 X22 p * L22 p j := by
  simp only [ch14ext_methodCStageRowResidual]

/-- The newly exposed bottom-left block of `U X L - I` is the trailing upper
block applied to the local column defect. -/
theorem ch14ext_methodCStage_bottomLeft_decomposition (fp : FPModel) (m : ℕ)
    (U22 X22 : Fin m → Fin m → ℝ) (l21 : Fin m → ℝ) (i : Fin m) :
    ∑ p : Fin m, U22 i p *
        (ch14ext_methodCStageColumn fp m X22 l21 p +
          ∑ q : Fin m, X22 p q * l21 q) =
      ∑ p : Fin m, U22 i p *
        ch14ext_methodCStageColumnResidual fp m X22 l21 p := by
  simp only [ch14ext_methodCStageColumnResidual]

/-! ### The scalar-leading block matrices for one printed reverse-k stage -/

/-- Lower-triangular factor at a scalar-leading Method C stage,
`L = [[1, 0], [l21, L22]]`. -/
def ch14ext_methodCStageL (m : ℕ) (l21 : Fin m → ℝ)
    (L22 : Fin m → Fin m → ℝ) : Fin (1 + m) → Fin (1 + m) → ℝ :=
  fun i j =>
    Fin.addCases
      (fun _ : Fin 1 =>
        Fin.addCases (fun _ : Fin 1 => 1) (fun _ : Fin m => 0) j)
      (fun a : Fin m =>
        Fin.addCases (fun _ : Fin 1 => l21 a) (fun b : Fin m => L22 a b) j)
      i

/-- Upper-triangular factor at a scalar-leading Method C stage,
`U = [[u11, u12^T], [0, U22]]`. -/
def ch14ext_methodCStageU (m : ℕ) (u11 : ℝ) (u12 : Fin m → ℝ)
    (U22 : Fin m → Fin m → ℝ) : Fin (1 + m) → Fin (1 + m) → ℝ :=
  fun i j =>
    Fin.addCases
      (fun _ : Fin 1 =>
        Fin.addCases (fun _ : Fin 1 => u11) (fun b : Fin m => u12 b) j)
      (fun a : Fin m =>
        Fin.addCases (fun _ : Fin 1 => 0) (fun b : Fin m => U22 a b) j)
      i

/-- Matrix after one literal reverse Method C stage,
`X = [[x11, x12^T], [x21, X22]]`, with all newly exposed entries supplied by
the rounded computations above. -/
noncomputable def ch14ext_methodCStageX (fp : FPModel) (m : ℕ)
    (u11 : ℝ) (u12 l21 : Fin m → ℝ) (X22 : Fin m → Fin m → ℝ) :
    Fin (1 + m) → Fin (1 + m) → ℝ :=
  fun i j =>
    Fin.addCases
      (fun _ : Fin 1 =>
        Fin.addCases
          (fun _ : Fin 1 => ch14ext_methodCStageDiag fp m u11 u12 X22 l21)
          (fun b : Fin m => ch14ext_methodCStageRow fp m u11 u12 X22 b) j)
      (fun a : Fin m =>
        Fin.addCases
          (fun _ : Fin 1 => ch14ext_methodCStageColumn fp m X22 l21 a)
          (fun b : Fin m => X22 a b) j)
      i

/-- The actual mixed residual entry of the assembled one-stage matrices. -/
noncomputable def ch14ext_methodCStageMixedResidual (fp : FPModel) (m : ℕ)
    (u11 : ℝ) (u12 l21 : Fin m → ℝ)
    (U22 X22 L22 : Fin m → Fin m → ℝ) :
    Fin (1 + m) → Fin (1 + m) → ℝ :=
  fun i j =>
    ∑ k1 : Fin (1 + m), ch14ext_methodCStageU m u11 u12 U22 i k1 *
      (∑ k2 : Fin (1 + m),
        ch14ext_methodCStageX fp m u11 u12 l21 X22 k1 k2 *
          ch14ext_methodCStageL m l21 L22 k2 j) -
      if i = j then 1 else 0

/-- The actual `(1,1)` entry of the assembled mixed residual is exactly the
diagonal stage defect plus the propagated column defects. -/
theorem ch14ext_methodCStageMixedResidual_lead_lead (fp : FPModel) (m : ℕ)
    (u11 : ℝ) (u12 l21 : Fin m → ℝ)
    (U22 X22 L22 : Fin m → Fin m → ℝ) :
    ch14ext_methodCStageMixedResidual fp m u11 u12 l21 U22 X22 L22
        (Fin.castAdd m (0 : Fin 1)) (Fin.castAdd m (0 : Fin 1)) =
      ch14ext_methodCStageDiagResidual fp m u11 u12 X22 l21 +
        ∑ p : Fin m, u12 p *
          ch14ext_methodCStageColumnResidual fp m X22 l21 p := by
  rw [← ch14ext_methodCStage_topLeft_decomposition]
  simp only [ch14ext_methodCStageMixedResidual, Fin.sum_univ_add,
    ch14ext_methodCStageU, ch14ext_methodCStageX, ch14ext_methodCStageL,
    Fin.addCases_left, Fin.addCases_right,
    Finset.univ_unique, Finset.sum_singleton]
  simp only [if_pos]
  ring_nf

/-- The actual top-right block of the assembled mixed residual is the local row
defect postmultiplied by `L22`. -/
theorem ch14ext_methodCStageMixedResidual_lead_trailing (fp : FPModel) (m : ℕ)
    (u11 : ℝ) (u12 l21 : Fin m → ℝ)
    (U22 X22 L22 : Fin m → Fin m → ℝ) (j : Fin m) :
    ch14ext_methodCStageMixedResidual fp m u11 u12 l21 U22 X22 L22
        (Fin.castAdd m (0 : Fin 1)) (Fin.natAdd 1 j) =
      ∑ p : Fin m,
        ch14ext_methodCStageRowResidual fp m u11 u12 X22 p * L22 p j := by
  have hne :
      (Fin.castAdd m (0 : Fin 1) : Fin (1 + m)) ≠ Fin.natAdd 1 j := by
    intro h
    have hval := congrArg Fin.val h
    simp only [Fin.val_castAdd, Fin.val_natAdd] at hval
    omega
  rw [← ch14ext_methodCStage_topRight_decomposition]
  simp only [ch14ext_methodCStageMixedResidual, Fin.sum_univ_add,
    ch14ext_methodCStageU, ch14ext_methodCStageX, ch14ext_methodCStageL,
    Fin.addCases_left, Fin.addCases_right,
    Finset.univ_unique, Finset.sum_singleton]
  rw [if_neg hne, sub_zero]
  simp only [mul_zero, zero_add]
  have hFub :
      ∑ q : Fin m, u12 q * (∑ p : Fin m, X22 q p * L22 p j) =
        ∑ p : Fin m, (∑ q : Fin m, u12 q * X22 q p) * L22 p j := by
    simp_rw [Finset.mul_sum, Finset.sum_mul]
    rw [Finset.sum_comm]
    apply Finset.sum_congr rfl
    intro p _
    apply Finset.sum_congr rfl
    intro q _
    ring
  rw [hFub]
  rw [Finset.mul_sum, ← Finset.sum_add_distrib]
  apply Finset.sum_congr rfl
  intro p _
  ring

/-- The actual bottom-left block of the assembled mixed residual is `U22`
applied to the local column defects. -/
theorem ch14ext_methodCStageMixedResidual_trailing_lead (fp : FPModel) (m : ℕ)
    (u11 : ℝ) (u12 l21 : Fin m → ℝ)
    (U22 X22 L22 : Fin m → Fin m → ℝ) (i : Fin m) :
    ch14ext_methodCStageMixedResidual fp m u11 u12 l21 U22 X22 L22
        (Fin.natAdd 1 i) (Fin.castAdd m (0 : Fin 1)) =
      ∑ p : Fin m, U22 i p *
        ch14ext_methodCStageColumnResidual fp m X22 l21 p := by
  have hne :
      (Fin.natAdd 1 i : Fin (1 + m)) ≠ Fin.castAdd m (0 : Fin 1) := by
    intro h
    have hval := congrArg Fin.val h
    simp only [Fin.val_castAdd, Fin.val_natAdd] at hval
    omega
  rw [← ch14ext_methodCStage_bottomLeft_decomposition]
  simp only [ch14ext_methodCStageMixedResidual, Fin.sum_univ_add,
    ch14ext_methodCStageU, ch14ext_methodCStageX, ch14ext_methodCStageL,
    Fin.addCases_left, Fin.addCases_right,
    Finset.univ_unique, Finset.sum_singleton]
  rw [if_neg hne, sub_zero]
  ring_nf

/-- The actual trailing block of the assembled mixed residual is unchanged by
the reverse stage; it is precisely the previous-stage mixed residual. -/
theorem ch14ext_methodCStageMixedResidual_trailing_trailing
    (fp : FPModel) (m : ℕ) (u11 : ℝ) (u12 l21 : Fin m → ℝ)
    (U22 X22 L22 : Fin m → Fin m → ℝ) (i j : Fin m) :
    ch14ext_methodCStageMixedResidual fp m u11 u12 l21 U22 X22 L22
        (Fin.natAdd 1 i) (Fin.natAdd 1 j) =
      ∑ p : Fin m, U22 i p * (∑ q : Fin m, X22 p q * L22 q j) -
        (if i = j then 1 else 0) := by
  simp only [ch14ext_methodCStageMixedResidual, Fin.sum_univ_add,
    ch14ext_methodCStageU, ch14ext_methodCStageX, ch14ext_methodCStageL,
    Fin.addCases_left, Fin.addCases_right,
    Finset.univ_unique, Finset.sum_singleton, zero_mul, zero_add]
  by_cases hij : i = j
  · subst j
    simp
  · simp [hij]

/-- **Method C reverse-stage residual bounds.**

All three newly computed regions are bounded from the literal rounded
recurrence.  The trailing `(2,2)` mixed residual is the sole recursive input,
so this theorem is a genuine dependency step rather than a restatement of
(14.19). -/
theorem ch14ext_methodCStage_residual_bounds (fp : FPModel) (m : ℕ)
    (u11 : ℝ) (u12 l21 : Fin m → ℝ)
    (U22 X22 L22 : Fin m → Fin m → ℝ)
    (hu11 : u11 ≠ 0) (hm1 : gammaValid fp (m + 1)) :
    (|ch14ext_methodCStageDiagResidual fp m u11 u12 X22 l21 +
        ∑ p : Fin m, u12 p *
          ch14ext_methodCStageColumnResidual fp m X22 l21 p| ≤
      ch14ext_methodCStageDiagBudget fp m u11 u12 X22 l21 +
        gamma fp m * ∑ p : Fin m, |u12 p| *
          (∑ q : Fin m, |X22 p q| * |l21 q|)) ∧
    (∀ j : Fin m,
      |∑ p : Fin m,
          ch14ext_methodCStageRowResidual fp m u11 u12 X22 p * L22 p j| ≤
        gamma fp (m + 1) *
          ∑ p : Fin m,
            (∑ q : Fin m, |u12 q| * |X22 q p|) * |L22 p j|) ∧
    (∀ i : Fin m,
      |∑ p : Fin m, U22 i p *
          ch14ext_methodCStageColumnResidual fp m X22 l21 p| ≤
        gamma fp m *
          ∑ p : Fin m, |U22 i p| *
            (∑ q : Fin m, |X22 p q| * |l21 q|)) := by
  have hm : gammaValid fp m := gammaValid_mono fp (by omega) hm1
  constructor
  · calc
      |ch14ext_methodCStageDiagResidual fp m u11 u12 X22 l21 +
          ∑ p : Fin m, u12 p *
            ch14ext_methodCStageColumnResidual fp m X22 l21 p|
          ≤ |ch14ext_methodCStageDiagResidual fp m u11 u12 X22 l21| +
              |∑ p : Fin m, u12 p *
                ch14ext_methodCStageColumnResidual fp m X22 l21 p| :=
            abs_add_le _ _
      _ ≤ ch14ext_methodCStageDiagBudget fp m u11 u12 X22 l21 +
            ∑ p : Fin m, |u12 p| *
              |ch14ext_methodCStageColumnResidual fp m X22 l21 p| := by
            exact add_le_add
              (ch14ext_methodCStageDiag_residual_bound fp m u11 u12 X22 l21
                hu11 hm)
              (le_trans (Finset.abs_sum_le_sum_abs _ _)
                (by
                  apply Finset.sum_le_sum
                  intro p _
                  rw [abs_mul]))
      _ ≤ ch14ext_methodCStageDiagBudget fp m u11 u12 X22 l21 +
            ∑ p : Fin m, |u12 p| *
              (gamma fp m * ∑ q : Fin m, |X22 p q| * |l21 q|) := by
            apply add_le_add le_rfl
            apply Finset.sum_le_sum
            intro p _
            exact mul_le_mul_of_nonneg_left
              (ch14ext_methodCStageColumn_residual_bound fp m X22 l21 hm p)
              (abs_nonneg _)
      _ = ch14ext_methodCStageDiagBudget fp m u11 u12 X22 l21 +
            gamma fp m * ∑ p : Fin m, |u12 p| *
              (∑ q : Fin m, |X22 p q| * |l21 q|) := by
            congr 1
            rw [Finset.mul_sum]
            apply Finset.sum_congr rfl
            intro p _
            ring
  constructor
  · intro j
    calc
      |∑ p : Fin m,
          ch14ext_methodCStageRowResidual fp m u11 u12 X22 p * L22 p j|
          ≤ ∑ p : Fin m,
              |ch14ext_methodCStageRowResidual fp m u11 u12 X22 p * L22 p j| :=
            Finset.abs_sum_le_sum_abs _ _
      _ = ∑ p : Fin m,
            |ch14ext_methodCStageRowResidual fp m u11 u12 X22 p| * |L22 p j| := by
            apply Finset.sum_congr rfl
            intro p _
            exact abs_mul _ _
      _ ≤ ∑ p : Fin m,
            (gamma fp (m + 1) *
              ∑ q : Fin m, |u12 q| * |X22 q p|) * |L22 p j| := by
            apply Finset.sum_le_sum
            intro p _
            exact mul_le_mul_of_nonneg_right
              (ch14ext_methodCStageRow_residual_bound fp m u11 u12 X22
                hu11 hm1 p) (abs_nonneg _)
      _ = gamma fp (m + 1) *
            ∑ p : Fin m,
              (∑ q : Fin m, |u12 q| * |X22 q p|) * |L22 p j| := by
            rw [Finset.mul_sum]
            apply Finset.sum_congr rfl
            intro p _
            ring
  · intro i
    calc
      |∑ p : Fin m, U22 i p *
          ch14ext_methodCStageColumnResidual fp m X22 l21 p|
          ≤ ∑ p : Fin m,
              |U22 i p * ch14ext_methodCStageColumnResidual fp m X22 l21 p| :=
            Finset.abs_sum_le_sum_abs _ _
      _ = ∑ p : Fin m, |U22 i p| *
            |ch14ext_methodCStageColumnResidual fp m X22 l21 p| := by
            apply Finset.sum_congr rfl
            intro p _
            exact abs_mul _ _
      _ ≤ ∑ p : Fin m, |U22 i p| *
            (gamma fp m * ∑ q : Fin m, |X22 p q| * |l21 q|) := by
            apply Finset.sum_le_sum
            intro p _
            exact mul_le_mul_of_nonneg_left
              (ch14ext_methodCStageColumn_residual_bound fp m X22 l21 hm p)
              (abs_nonneg _)
      _ = gamma fp m *
            ∑ p : Fin m, |U22 i p| *
              (∑ q : Fin m, |X22 p q| * |l21 q|) := by
            rw [Finset.mul_sum]
            apply Finset.sum_congr rfl
            intro p _
            ring

/-! ### Uniform diagonal budget for whole-loop accumulation -/

/-- The diagonal reciprocal/dot/subtraction defect can be absorbed into the
same absolute-product envelope used by (14.19).

Here `N` is a fixed bounding dimension for the whole reverse loop and
`g = gamma fp (N+2)`.  The coefficient `4g + 3g²` is derived by:

* bounding the rounded dot by `(1+g)` times its absolute dot product;
* using `gamma_inv` on the final subtraction factor to recover the unrounded
  difference from the stored diagonal entry; and
* charging the bare reciprocal error through
  `u ≤ g(1-u) ≤ g |u11| (1+g)(|x11|+|x12||l21|)`.

No diagonal residual or final mixed residual is assumed. -/
theorem ch14ext_methodCStageDiag_residual_uniform (fp : FPModel) (N m : ℕ)
    (u11 : ℝ) (u12 : Fin m → ℝ) (X22 : Fin m → Fin m → ℝ)
    (l21 : Fin m → ℝ)
    (hu11 : u11 ≠ 0) (hmN : m ≤ N)
    (hN2 : gammaValid fp (N + 2)) :
    |ch14ext_methodCStageDiagResidual fp m u11 u12 X22 l21| ≤
      (4 * gamma fp (N + 2) + 3 * gamma fp (N + 2) ^ 2) * |u11| *
        (|ch14ext_methodCStageDiag fp m u11 u12 X22 l21| +
          ∑ q : Fin m,
            |ch14ext_methodCStageRow fp m u11 u12 X22 q| * |l21 q|) := by
  let g := gamma fp (N + 2)
  let r := fp.fl_div 1 u11
  let t := ch14ext_methodCStageDiagDot fp m u11 u12 X22 l21
  let S := ∑ q : Fin m,
    ch14ext_methodCStageRow fp m u11 u12 X22 q * l21 q
  let B := ∑ q : Fin m,
    |ch14ext_methodCStageRow fp m u11 u12 X22 q| * |l21 q|
  let x := ch14ext_methodCStageDiag fp m u11 u12 X22 l21
  let W := |x| + B
  have hm : gammaValid fp m := gammaValid_mono fp (by omega) hN2
  have h1 : gammaValid fp 1 := gammaValid_mono fp (by omega) hN2
  have h2 : gammaValid fp 2 := gammaValid_mono fp (by omega) hN2
  have hg : 0 ≤ g := gamma_nonneg fp hN2
  have hgm : gamma fp m ≤ g := gamma_mono fp (by omega) hN2
  have hg1 : gamma fp 1 ≤ g := gamma_mono fp (by omega) hN2
  have hg2 : gamma fp 2 ≤ g := gamma_mono fp (by omega) hN2
  have huG : fp.u ≤ g := le_trans (u_le_gamma fp one_pos h1) hg1
  have hu_lt_one : fp.u < 1 := by
    simpa [gammaValid] using h1
  have hB : 0 ≤ B := by
    dsimp [B]
    exact Finset.sum_nonneg fun q _ =>
      mul_nonneg (abs_nonneg _) (abs_nonneg _)
  have hW : 0 ≤ W := add_nonneg (abs_nonneg _) hB
  have hB_le_W : B ≤ W := by
    dsimp [W]
    linarith [abs_nonneg x]
  have hS : |S| ≤ B := by
    dsimp [S, B]
    calc
      |∑ q : Fin m,
          ch14ext_methodCStageRow fp m u11 u12 X22 q * l21 q|
          ≤ ∑ q : Fin m,
              |ch14ext_methodCStageRow fp m u11 u12 X22 q * l21 q| :=
            Finset.abs_sum_le_sum_abs _ _
      _ = _ := by
        apply Finset.sum_congr rfl
        intro q _
        exact abs_mul _ _
  have hdot0 := dotProduct_error_bound fp m
    (ch14ext_methodCStageRow fp m u11 u12 X22) l21 hm
  have hdot : |t - S| ≤ gamma fp m * B := by
    simpa [t, S, B, ch14ext_methodCStageDiagDot] using hdot0
  have ht0 : |t| ≤ (1 + gamma fp m) * B := by
    have htri : |t| ≤ |t - S| + |S| := by
      have h := abs_add_le (t - S) S
      simpa using h
    have hgm_nonneg := gamma_nonneg fp hm
    nlinarith
  have ht : |t| ≤ (1 + g) * B := by
    refine le_trans ht0 ?_
    exact mul_le_mul_of_nonneg_right (by linarith) hB
  obtain ⟨deltaR, hdeltaR, hrecip⟩ := fp.model_div 1 u11 hu11
  obtain ⟨deltaS, hdeltaS, hsub⟩ := fp.model_sub r t
  have hur : u11 * r = 1 + deltaR := by
    dsimp [r]
    rw [hrecip]
    field_simp [hu11]
  have hx : x = (r - t) * (1 + deltaS) := by
    simpa [x, ch14ext_methodCStageDiag, r, t] using hsub
  have hdeltaS1 : |deltaS| ≤ gamma fp 1 :=
    le_trans hdeltaS (u_le_gamma fp one_pos h1)
  have hposS : 0 < 1 + deltaS := by
    linarith [neg_abs_le deltaS]
  obtain ⟨theta, htheta, hinv⟩ :=
    gamma_inv fp 1 deltaS hdeltaS1 hposS (by simpa using h2)
  have hy : r - t = x * (1 + theta) := by
    calc
      r - t = ((r - t) * (1 + deltaS)) * (1 / (1 + deltaS)) := by
        field_simp [hposS.ne']
      _ = x * (1 / (1 + deltaS)) := by rw [← hx]
      _ = x * (1 + theta) := by rw [hinv]
  have hthetaG : |theta| ≤ g := le_trans htheta (by simpa using hg2)
  have honeTheta : |1 + theta| ≤ 1 + g := by
    calc
      |1 + theta| ≤ |(1 : ℝ)| + |theta| := abs_add_le _ _
      _ ≤ 1 + g := by norm_num; linarith
  have hyBound : |r - t| ≤ (1 + g) * |x| := by
    rw [hy, abs_mul]
    calc
      |x| * |1 + theta| ≤ |x| * (1 + g) :=
        mul_le_mul_of_nonneg_left honeTheta (abs_nonneg _)
      _ = (1 + g) * |x| := by ring
  have hr : |r| ≤ (1 + g) * W := by
    have htri : |r| ≤ |r - t| + |t| := by
      have h := abs_add_le (r - t) t
      simpa using h
    calc
      |r| ≤ |r - t| + |t| := htri
      _ ≤ (1 + g) * |x| + (1 + g) * B := add_le_add hyBound ht
      _ = (1 + g) * W := by simp only [W]; ring
  have hrt : |r| + |t| ≤ 2 * (1 + g) * W := by
    have htW : |t| ≤ (1 + g) * W :=
      le_trans ht (mul_le_mul_of_nonneg_left hB_le_W (by linarith))
    nlinarith
  have hposR : 0 < 1 + deltaR := by
    linarith [neg_abs_le deltaR]
  have hrecipAmp : 1 - fp.u ≤ |u11| * (1 + g) * W := by
    calc
      1 - fp.u ≤ |1 + deltaR| := by
        rw [abs_of_pos hposR]
        linarith [neg_abs_le deltaR]
      _ = |u11| * |r| := by rw [← hur, abs_mul]
      _ ≤ |u11| * ((1 + g) * W) :=
        mul_le_mul_of_nonneg_left hr (abs_nonneg _)
      _ = |u11| * (1 + g) * W := by ring
  have hgammaOneIdentity : gamma fp 1 * (1 - fp.u) = fp.u := by
    have hden : 1 - fp.u ≠ 0 := by linarith
    unfold gamma
    norm_num
    field_simp [hden]
  have huScaled : fp.u ≤ g * (1 - fp.u) := by
    calc
      fp.u = gamma fp 1 * (1 - fp.u) := hgammaOneIdentity.symm
      _ ≤ g * (1 - fp.u) :=
        mul_le_mul_of_nonneg_right hg1 (by linarith)
  have hbare : fp.u ≤ g * (1 + g) * |u11| * W := by
    calc
      fp.u ≤ g * (1 - fp.u) := huScaled
      _ ≤ g * (|u11| * (1 + g) * W) :=
        mul_le_mul_of_nonneg_left hrecipAmp hg
      _ = g * (1 + g) * |u11| * W := by ring
  have hmiddle :
      |u11| * (gamma fp m * B) ≤ g * |u11| * W := by
    calc
      |u11| * (gamma fp m * B) ≤ |u11| * (g * B) :=
        mul_le_mul_of_nonneg_left
          (mul_le_mul_of_nonneg_right hgm hB) (abs_nonneg _)
      _ ≤ |u11| * (g * W) :=
        mul_le_mul_of_nonneg_left
          (mul_le_mul_of_nonneg_left hB_le_W hg) (abs_nonneg _)
      _ = g * |u11| * W := by ring
  have hlast :
      |u11| * fp.u * (|r| + |t|) ≤
        (2 * g * (1 + g)) * |u11| * W := by
    calc
      |u11| * fp.u * (|r| + |t|) ≤ |u11| * g * (|r| + |t|) :=
        mul_le_mul_of_nonneg_right
          (mul_le_mul_of_nonneg_left huG (abs_nonneg _))
          (add_nonneg (abs_nonneg _) (abs_nonneg _))
      _ ≤ |u11| * g * (2 * (1 + g) * W) :=
        mul_le_mul_of_nonneg_left hrt
          (mul_nonneg (abs_nonneg _) hg)
      _ = (2 * g * (1 + g)) * |u11| * W := by ring
  have hbase :=
    ch14ext_methodCStageDiag_residual_bound fp m u11 u12 X22 l21 hu11 hm
  refine le_trans hbase ?_
  change fp.u + |u11| * (gamma fp m * B) +
      |u11| * fp.u * (|r| + |t|) ≤
    (4 * g + 3 * g ^ 2) * |u11| * W
  calc
    fp.u + |u11| * (gamma fp m * B) +
        |u11| * fp.u * (|r| + |t|)
        ≤ (g * (1 + g) * |u11| * W) +
            (g * |u11| * W) +
            ((2 * g * (1 + g)) * |u11| * W) :=
          add_le_add (add_le_add hbare hmiddle) hlast
    _ = (4 * g + 3 * g ^ 2) * |u11| * W := by ring

/-! ### Absolute-product block identities for equation (14.19) -/

/-- The componentwise `|U||X||L|` envelope for one assembled Method C stage. -/
noncomputable def ch14ext_methodCStageAbsProduct (fp : FPModel) (m : ℕ)
    (u11 : ℝ) (u12 l21 : Fin m → ℝ)
    (U22 X22 L22 : Fin m → Fin m → ℝ) :
    Fin (1 + m) → Fin (1 + m) → ℝ :=
  fun i j =>
    ∑ p : Fin (1 + m), |ch14ext_methodCStageU m u11 u12 U22 i p| *
      (∑ q : Fin (1 + m),
        |ch14ext_methodCStageX fp m u11 u12 l21 X22 p q| *
          |ch14ext_methodCStageL m l21 L22 q j|)

theorem ch14ext_methodCStageAbsProduct_lead_lead (fp : FPModel) (m : ℕ)
    (u11 : ℝ) (u12 l21 : Fin m → ℝ)
    (U22 X22 L22 : Fin m → Fin m → ℝ) :
    ch14ext_methodCStageAbsProduct fp m u11 u12 l21 U22 X22 L22
        (Fin.castAdd m (0 : Fin 1)) (Fin.castAdd m (0 : Fin 1)) =
      |u11| *
          (|ch14ext_methodCStageDiag fp m u11 u12 X22 l21| +
            ∑ q : Fin m,
              |ch14ext_methodCStageRow fp m u11 u12 X22 q| * |l21 q|) +
        ∑ p : Fin m, |u12 p| *
          (|ch14ext_methodCStageColumn fp m X22 l21 p| +
            ∑ q : Fin m, |X22 p q| * |l21 q|) := by
  simp only [ch14ext_methodCStageAbsProduct, Fin.sum_univ_add,
    ch14ext_methodCStageU, ch14ext_methodCStageX, ch14ext_methodCStageL,
    Fin.addCases_left, Fin.addCases_right,
    Finset.univ_unique, Finset.sum_singleton, abs_one, mul_one]

theorem ch14ext_methodCStageAbsProduct_lead_trailing (fp : FPModel) (m : ℕ)
    (u11 : ℝ) (u12 l21 : Fin m → ℝ)
    (U22 X22 L22 : Fin m → Fin m → ℝ) (j : Fin m) :
    ch14ext_methodCStageAbsProduct fp m u11 u12 l21 U22 X22 L22
        (Fin.castAdd m (0 : Fin 1)) (Fin.natAdd 1 j) =
      |u11| *
          (∑ q : Fin m,
            |ch14ext_methodCStageRow fp m u11 u12 X22 q| * |L22 q j|) +
        ∑ p : Fin m, |u12 p| *
          (∑ q : Fin m, |X22 p q| * |L22 q j|) := by
  simp only [ch14ext_methodCStageAbsProduct, Fin.sum_univ_add,
    ch14ext_methodCStageU, ch14ext_methodCStageX, ch14ext_methodCStageL,
    Fin.addCases_left, Fin.addCases_right,
    Finset.univ_unique, Finset.sum_singleton, abs_zero,
    mul_zero, zero_add]

theorem ch14ext_methodCStageAbsProduct_trailing_lead (fp : FPModel) (m : ℕ)
    (u11 : ℝ) (u12 l21 : Fin m → ℝ)
    (U22 X22 L22 : Fin m → Fin m → ℝ) (i : Fin m) :
    ch14ext_methodCStageAbsProduct fp m u11 u12 l21 U22 X22 L22
        (Fin.natAdd 1 i) (Fin.castAdd m (0 : Fin 1)) =
      ∑ p : Fin m, |U22 i p| *
        (|ch14ext_methodCStageColumn fp m X22 l21 p| +
          ∑ q : Fin m, |X22 p q| * |l21 q|) := by
  simp only [ch14ext_methodCStageAbsProduct, Fin.sum_univ_add,
    ch14ext_methodCStageU, ch14ext_methodCStageX, ch14ext_methodCStageL,
    Fin.addCases_left, Fin.addCases_right,
    Finset.univ_unique, Finset.sum_singleton, abs_one, abs_zero,
    mul_one, zero_mul, zero_add]

theorem ch14ext_methodCStageAbsProduct_trailing_trailing
    (fp : FPModel) (m : ℕ) (u11 : ℝ) (u12 l21 : Fin m → ℝ)
    (U22 X22 L22 : Fin m → Fin m → ℝ) (i j : Fin m) :
    ch14ext_methodCStageAbsProduct fp m u11 u12 l21 U22 X22 L22
        (Fin.natAdd 1 i) (Fin.natAdd 1 j) =
      ∑ p : Fin m, |U22 i p| *
        (∑ q : Fin m, |X22 p q| * |L22 q j|) := by
  simp only [ch14ext_methodCStageAbsProduct, Fin.sum_univ_add,
    ch14ext_methodCStageU, ch14ext_methodCStageX, ch14ext_methodCStageL,
    Fin.addCases_left, Fin.addCases_right,
    Finset.univ_unique, Finset.sum_singleton, abs_zero,
    mul_zero, zero_mul, zero_add]

/-! ### One-stage composer with a recursive trailing certificate -/

/-- A complete Method C induction step for the mixed residual.

The newly exposed row, column, and diagonal are all discharged from their
rounded operations.  The sole residual hypothesis is on the untouched trailing
stage, exactly the induction hypothesis needed by the whole reverse loop. -/
theorem ch14ext_methodCStage_mixed_residual_bound (fp : FPModel) (N m : ℕ)
    (u11 : ℝ) (u12 l21 : Fin m → ℝ)
    (U22 X22 L22 : Fin m → Fin m → ℝ)
    (hu11 : u11 ≠ 0) (hmN : m ≤ N)
    (hN2 : gammaValid fp (N + 2))
    (h22 : ∀ i j : Fin m,
      |∑ p : Fin m, U22 i p * (∑ q : Fin m, X22 p q * L22 q j) -
          (if i = j then 1 else 0)| ≤
        (4 * gamma fp (N + 2) + 3 * gamma fp (N + 2) ^ 2) *
          ∑ p : Fin m, |U22 i p| *
            (∑ q : Fin m, |X22 p q| * |L22 q j|)) :
    ∀ i j : Fin (1 + m),
      |ch14ext_methodCStageMixedResidual fp m u11 u12 l21 U22 X22 L22 i j| ≤
        (4 * gamma fp (N + 2) + 3 * gamma fp (N + 2) ^ 2) *
          ch14ext_methodCStageAbsProduct fp m u11 u12 l21 U22 X22 L22 i j := by
  let g := gamma fp (N + 2)
  let C := 4 * g + 3 * g ^ 2
  have hm : gammaValid fp m := gammaValid_mono fp (by omega) hN2
  have hm1 : gammaValid fp (m + 1) := gammaValid_mono fp (by omega) hN2
  have hg : 0 ≤ g := gamma_nonneg fp hN2
  have hC : 0 ≤ C := by
    dsimp [C]
    nlinarith [sq_nonneg g]
  have hgC : g ≤ C := by
    dsimp [C]
    nlinarith [sq_nonneg g]
  have hgmC : gamma fp m ≤ C :=
    le_trans (gamma_mono fp (by omega) hN2) hgC
  have hgm1C : gamma fp (m + 1) ≤ C :=
    le_trans (gamma_mono fp (by omega) hN2) hgC
  have hdiag := ch14ext_methodCStageDiag_residual_uniform fp N m
    u11 u12 X22 l21 hu11 hmN hN2
  have hstage := ch14ext_methodCStage_residual_bounds fp m
    u11 u12 l21 U22 X22 L22 hu11 hm1
  intro i j
  refine Fin.addCases (fun a => ?_) (fun b => ?_) i
  · have ha : a = (0 : Fin 1) := Subsingleton.elim _ _
    subst a
    refine Fin.addCases (fun d => ?_) (fun e => ?_) j
    · have hd : d = (0 : Fin 1) := Subsingleton.elim _ _
      subst d
      rw [ch14ext_methodCStageMixedResidual_lead_lead,
        ch14ext_methodCStageAbsProduct_lead_lead]
      have hcol :
          |∑ p : Fin m, u12 p *
              ch14ext_methodCStageColumnResidual fp m X22 l21 p| ≤
            C * ∑ p : Fin m, |u12 p| *
              (|ch14ext_methodCStageColumn fp m X22 l21 p| +
                ∑ q : Fin m, |X22 p q| * |l21 q|) := by
        calc
          |∑ p : Fin m, u12 p *
              ch14ext_methodCStageColumnResidual fp m X22 l21 p|
              ≤ ∑ p : Fin m,
                  |u12 p * ch14ext_methodCStageColumnResidual fp m X22 l21 p| :=
                Finset.abs_sum_le_sum_abs _ _
          _ = ∑ p : Fin m, |u12 p| *
                |ch14ext_methodCStageColumnResidual fp m X22 l21 p| := by
                apply Finset.sum_congr rfl
                intro p _
                exact abs_mul _ _
          _ ≤ ∑ p : Fin m, |u12 p| *
                (C * (|ch14ext_methodCStageColumn fp m X22 l21 p| +
                  ∑ q : Fin m, |X22 p q| * |l21 q|)) := by
                apply Finset.sum_le_sum
                intro p _
                apply mul_le_mul_of_nonneg_left _ (abs_nonneg _)
                calc
                  |ch14ext_methodCStageColumnResidual fp m X22 l21 p|
                      ≤ gamma fp m *
                          ∑ q : Fin m, |X22 p q| * |l21 q| :=
                        ch14ext_methodCStageColumn_residual_bound
                          fp m X22 l21 hm p
                  _ ≤ C * ∑ q : Fin m, |X22 p q| * |l21 q| :=
                        mul_le_mul_of_nonneg_right hgmC
                          (Finset.sum_nonneg fun q _ =>
                            mul_nonneg (abs_nonneg _) (abs_nonneg _))
                  _ ≤ C * (|ch14ext_methodCStageColumn fp m X22 l21 p| +
                        ∑ q : Fin m, |X22 p q| * |l21 q|) :=
                        mul_le_mul_of_nonneg_left
                          (le_add_of_nonneg_left (abs_nonneg
                            (ch14ext_methodCStageColumn fp m X22 l21 p))) hC
          _ = C * ∑ p : Fin m, |u12 p| *
                (|ch14ext_methodCStageColumn fp m X22 l21 p| +
                  ∑ q : Fin m, |X22 p q| * |l21 q|) := by
                rw [Finset.mul_sum]
                apply Finset.sum_congr rfl
                intro p _
                ring
      change
        |ch14ext_methodCStageDiagResidual fp m u11 u12 X22 l21 +
            ∑ p : Fin m, u12 p *
              ch14ext_methodCStageColumnResidual fp m X22 l21 p| ≤
          C *
            (|u11| *
                (|ch14ext_methodCStageDiag fp m u11 u12 X22 l21| +
                  ∑ q : Fin m,
                    |ch14ext_methodCStageRow fp m u11 u12 X22 q| * |l21 q|) +
              ∑ p : Fin m, |u12 p| *
                (|ch14ext_methodCStageColumn fp m X22 l21 p| +
                  ∑ q : Fin m, |X22 p q| * |l21 q|))
      calc
        |ch14ext_methodCStageDiagResidual fp m u11 u12 X22 l21 +
            ∑ p : Fin m, u12 p *
              ch14ext_methodCStageColumnResidual fp m X22 l21 p|
            ≤ |ch14ext_methodCStageDiagResidual fp m u11 u12 X22 l21| +
                |∑ p : Fin m, u12 p *
                  ch14ext_methodCStageColumnResidual fp m X22 l21 p| :=
              abs_add_le _ _
        _ ≤ C *
              (|u11| *
                (|ch14ext_methodCStageDiag fp m u11 u12 X22 l21| +
                  ∑ q : Fin m,
                    |ch14ext_methodCStageRow fp m u11 u12 X22 q| * |l21 q|)) +
              C * ∑ p : Fin m, |u12 p| *
                (|ch14ext_methodCStageColumn fp m X22 l21 p| +
                  ∑ q : Fin m, |X22 p q| * |l21 q|) := by
              simpa [C, g, mul_assoc] using add_le_add hdiag hcol
        _ = C *
            (|u11| *
                (|ch14ext_methodCStageDiag fp m u11 u12 X22 l21| +
                  ∑ q : Fin m,
                    |ch14ext_methodCStageRow fp m u11 u12 X22 q| * |l21 q|) +
              ∑ p : Fin m, |u12 p| *
                (|ch14ext_methodCStageColumn fp m X22 l21 p| +
                  ∑ q : Fin m, |X22 p q| * |l21 q|)) := by ring
    · rw [ch14ext_methodCStageMixedResidual_lead_trailing,
        ch14ext_methodCStageAbsProduct_lead_trailing]
      have hFub :
          ∑ p : Fin m,
              (∑ q : Fin m, |u12 q| * |X22 q p|) * |L22 p e| =
            ∑ q : Fin m, |u12 q| *
              (∑ p : Fin m, |X22 q p| * |L22 p e|) := by
        simp_rw [Finset.sum_mul, Finset.mul_sum]
        rw [Finset.sum_comm]
        apply Finset.sum_congr rfl
        intro p _
        apply Finset.sum_congr rfl
        intro q _
        ring
      have hrow0 := hstage.2.1 e
      have hrow :
          |∑ p : Fin m,
              ch14ext_methodCStageRowResidual fp m u11 u12 X22 p * L22 p e| ≤
            C * ∑ q : Fin m, |u12 q| *
              (∑ p : Fin m, |X22 q p| * |L22 p e|) := by
        refine le_trans hrow0 ?_
        calc
          gamma fp (m + 1) *
              ∑ p : Fin m,
                (∑ q : Fin m, |u12 q| * |X22 q p|) * |L22 p e|
              ≤ C * ∑ p : Fin m,
                (∑ q : Fin m, |u12 q| * |X22 q p|) * |L22 p e| :=
                mul_le_mul_of_nonneg_right hgm1C
                  (Finset.sum_nonneg fun p _ =>
                    mul_nonneg
                      (Finset.sum_nonneg fun q _ =>
                        mul_nonneg (abs_nonneg _) (abs_nonneg _))
                      (abs_nonneg _))
          _ = C * ∑ q : Fin m, |u12 q| *
              (∑ p : Fin m, |X22 q p| * |L22 p e|) := by rw [hFub]
      refine le_trans hrow ?_
      apply mul_le_mul_of_nonneg_left _ hC
      exact le_add_of_nonneg_left
        (mul_nonneg (abs_nonneg _)
          (Finset.sum_nonneg fun q _ =>
            mul_nonneg (abs_nonneg _) (abs_nonneg _)))
  · refine Fin.addCases (fun d => ?_) (fun e => ?_) j
    · have hd : d = (0 : Fin 1) := Subsingleton.elim _ _
      subst d
      rw [ch14ext_methodCStageMixedResidual_trailing_lead,
        ch14ext_methodCStageAbsProduct_trailing_lead]
      have hcol0 := hstage.2.2 b
      refine le_trans hcol0 ?_
      calc
        gamma fp m * ∑ p : Fin m, |U22 b p| *
              (∑ q : Fin m, |X22 p q| * |l21 q|)
            ≤ C * ∑ p : Fin m, |U22 b p| *
              (∑ q : Fin m, |X22 p q| * |l21 q|) :=
              mul_le_mul_of_nonneg_right hgmC
                (Finset.sum_nonneg fun p _ =>
                  mul_nonneg (abs_nonneg _)
                    (Finset.sum_nonneg fun q _ =>
                      mul_nonneg (abs_nonneg _) (abs_nonneg _)))
        _ ≤ C * ∑ p : Fin m, |U22 b p| *
              (|ch14ext_methodCStageColumn fp m X22 l21 p| +
                ∑ q : Fin m, |X22 p q| * |l21 q|) := by
              apply mul_le_mul_of_nonneg_left _ hC
              apply Finset.sum_le_sum
              intro p _
              apply mul_le_mul_of_nonneg_left _ (abs_nonneg _)
              linarith [abs_nonneg
                (ch14ext_methodCStageColumn fp m X22 l21 p)]
    · rw [ch14ext_methodCStageMixedResidual_trailing_trailing,
        ch14ext_methodCStageAbsProduct_trailing_trailing]
      exact h22 b e

/-! ### The complete printed reverse loop -/

/-- Number of scalar reverse stages.  A `List Unit` is used so a cons stage is
definitionally `1 +` the trailing dimension, exactly matching the block stage
above. -/
def ch14ext_methodCDim : List Unit → ℕ
  | [] => 0
  | () :: rest => 1 + ch14ext_methodCDim rest

@[simp] theorem ch14ext_methodCDim_nil : ch14ext_methodCDim [] = 0 := rfl

@[simp] theorem ch14ext_methodCDim_cons (rest : List Unit) :
    ch14ext_methodCDim (() :: rest) = 1 + ch14ext_methodCDim rest := rfl

/-- Canonical scalar-stage list for an ordinary matrix dimension `n`. -/
def ch14ext_methodCSteps (n : ℕ) : List Unit := List.replicate n ()

/-- The canonical stage list has exactly the source-facing dimension `n`. -/
@[simp] theorem ch14ext_methodCDim_steps (n : ℕ) :
    ch14ext_methodCDim (ch14ext_methodCSteps n) = n := by
  induction n with
  | zero => rfl
  | succ n ih =>
      change 1 + ch14ext_methodCDim (List.replicate n ()) = n + 1
      have ih' : ch14ext_methodCDim (List.replicate n ()) = n := by
        simpa [ch14ext_methodCSteps] using ih
      rw [ih']
      omega

/-- The concrete whole-loop Method C inverse.  The recursion peels the leading
scalar of the current trailing submatrix, recursively computes `X22`, then
executes the three rounded assignments from (14.19)'s reverse-`k` loop. -/
noncomputable def ch14ext_methodCInv (fp : FPModel) :
    (steps : List Unit) →
      (U L : Fin (ch14ext_methodCDim steps) →
        Fin (ch14ext_methodCDim steps) → ℝ) →
      Fin (ch14ext_methodCDim steps) → Fin (ch14ext_methodCDim steps) → ℝ
  | [], U, _ => U
  | () :: rest, U, L =>
      ch14ext_methodCStageX fp (ch14ext_methodCDim rest)
        (U (Fin.castAdd (ch14ext_methodCDim rest) (0 : Fin 1))
          (Fin.castAdd (ch14ext_methodCDim rest) (0 : Fin 1)))
        (fun j => U (Fin.castAdd (ch14ext_methodCDim rest) (0 : Fin 1))
          (Fin.natAdd 1 j))
        (fun i => L (Fin.natAdd 1 i)
          (Fin.castAdd (ch14ext_methodCDim rest) (0 : Fin 1)))
        (ch14ext_methodCInv fp rest
          (fun i j => U (Fin.natAdd 1 i) (Fin.natAdd 1 j))
          (fun i j => L (Fin.natAdd 1 i) (Fin.natAdd 1 j)))

@[simp] theorem ch14ext_methodCInv_cons (fp : FPModel) (rest : List Unit)
    (U L : Fin (1 + ch14ext_methodCDim rest) →
      Fin (1 + ch14ext_methodCDim rest) → ℝ) :
    ch14ext_methodCInv fp (() :: rest) U L =
      ch14ext_methodCStageX fp (ch14ext_methodCDim rest)
        (U (Fin.castAdd (ch14ext_methodCDim rest) (0 : Fin 1))
          (Fin.castAdd (ch14ext_methodCDim rest) (0 : Fin 1)))
        (fun j => U (Fin.castAdd (ch14ext_methodCDim rest) (0 : Fin 1))
          (Fin.natAdd 1 j))
        (fun i => L (Fin.natAdd 1 i)
          (Fin.castAdd (ch14ext_methodCDim rest) (0 : Fin 1)))
        (ch14ext_methodCInv fp rest
          (fun i j => U (Fin.natAdd 1 i) (Fin.natAdd 1 j))
          (fun i j => L (Fin.natAdd 1 i) (Fin.natAdd 1 j))) := rfl

/-- Reindex a stage-list Method C computation onto an ordinary `Fin n` index.

The equality `hdim` is packaging data only: it transports the source matrices
to the internal stage-list dimension and transports the computed inverse back.
The source-facing `ch14ext_methodCInvNat` below fixes `steps` canonically. -/
noncomputable def ch14ext_methodCInvReindex (fp : FPModel) {n : ℕ}
    (steps : List Unit) (hdim : ch14ext_methodCDim steps = n)
    (U L : Fin n → Fin n → ℝ) : Fin n → Fin n → ℝ :=
  fun i j =>
    ch14ext_methodCInv fp steps
      (fun p q => U (Fin.cast hdim p) (Fin.cast hdim q))
      (fun p q => L (Fin.cast hdim p) (Fin.cast hdim q))
      (Fin.cast hdim.symm i) (Fin.cast hdim.symm j)

/-- Method C's concrete reverse-loop result with the public index type
directly equal to `Fin n`. -/
noncomputable def ch14ext_methodCInvNat (fp : FPModel) (n : ℕ)
    (U L : Fin n → Fin n → ℝ) : Fin n → Fin n → ℝ :=
  ch14ext_methodCInvReindex fp (ch14ext_methodCSteps n)
    (ch14ext_methodCDim_steps n) U L

/-- Reassembling an upper-triangular matrix from its scalar-leading blocks
recovers the original matrix. -/
theorem ch14ext_methodCStageU_eq_of_upper (m : ℕ)
    (U : Fin (1 + m) → Fin (1 + m) → ℝ)
    (hUT : ∀ i j : Fin (1 + m), j.val < i.val → U i j = 0) :
    ch14ext_methodCStageU m
        (U (Fin.castAdd m (0 : Fin 1)) (Fin.castAdd m (0 : Fin 1)))
        (fun j => U (Fin.castAdd m (0 : Fin 1)) (Fin.natAdd 1 j))
        (fun i j => U (Fin.natAdd 1 i) (Fin.natAdd 1 j)) = U := by
  funext i j
  refine Fin.addCases (fun a => ?_) (fun b => ?_) i
  · have ha : a = (0 : Fin 1) := Subsingleton.elim _ _
    subst a
    refine Fin.addCases (fun d => ?_) (fun e => ?_) j
    · have hd : d = (0 : Fin 1) := Subsingleton.elim _ _
      subst d
      rfl
    · simp only [ch14ext_methodCStageU, Fin.addCases_left,
        Fin.addCases_right]
  · refine Fin.addCases (fun d => ?_) (fun e => ?_) j
    · have hd : d = (0 : Fin 1) := Subsingleton.elim _ _
      subst d
      simp only [ch14ext_methodCStageU, Fin.addCases_right,
        Fin.addCases_left]
      exact (hUT (Fin.natAdd 1 b) (Fin.castAdd m (0 : Fin 1)) (by
        simp only [Fin.val_natAdd, Fin.val_castAdd]
        omega)).symm
    · simp only [ch14ext_methodCStageU, Fin.addCases_right]

/-- Reassembling a unit lower-triangular matrix from its scalar-leading blocks
recovers the original matrix. -/
theorem ch14ext_methodCStageL_eq_of_unit_lower (m : ℕ)
    (L : Fin (1 + m) → Fin (1 + m) → ℝ)
    (hLunit : ∀ i : Fin (1 + m), L i i = 1)
    (hLT : ∀ i j : Fin (1 + m), j.val > i.val → L i j = 0) :
    ch14ext_methodCStageL m
        (fun i => L (Fin.natAdd 1 i) (Fin.castAdd m (0 : Fin 1)))
        (fun i j => L (Fin.natAdd 1 i) (Fin.natAdd 1 j)) = L := by
  funext i j
  refine Fin.addCases (fun a => ?_) (fun b => ?_) i
  · have ha : a = (0 : Fin 1) := Subsingleton.elim _ _
    subst a
    refine Fin.addCases (fun d => ?_) (fun e => ?_) j
    · have hd : d = (0 : Fin 1) := Subsingleton.elim _ _
      subst d
      simp only [ch14ext_methodCStageL, Fin.addCases_left]
      exact (hLunit (Fin.castAdd m (0 : Fin 1))).symm
    · simp only [ch14ext_methodCStageL, Fin.addCases_left,
        Fin.addCases_right]
      exact (hLT (Fin.castAdd m (0 : Fin 1)) (Fin.natAdd 1 e) (by
        simp only [Fin.val_natAdd, Fin.val_castAdd]
        omega)).symm
  · refine Fin.addCases (fun d => ?_) (fun e => ?_) j
    · have hd : d = (0 : Fin 1) := Subsingleton.elim _ _
      subst d
      simp only [ch14ext_methodCStageL, Fin.addCases_right,
        Fin.addCases_left]
    · simp only [ch14ext_methodCStageL, Fin.addCases_right]

/-- Whole-loop Method C mixed residual at a fixed bounding dimension `N`.

This is the induction theorem behind equation (14.19).  Every reverse stage is
the concrete rounded recurrence in `ch14ext_methodCInv`; no local or final
residual is accepted as a hypothesis. -/
theorem ch14ext_methodCInv_mixed_residual (fp : FPModel) (N : ℕ)
    (hN2 : gammaValid fp (N + 2)) :
    ∀ (steps : List Unit)
      (U L : Fin (ch14ext_methodCDim steps) →
        Fin (ch14ext_methodCDim steps) → ℝ),
      ch14ext_methodCDim steps ≤ N →
      (∀ i : Fin (ch14ext_methodCDim steps), U i i ≠ 0) →
      (∀ i j : Fin (ch14ext_methodCDim steps),
        j.val < i.val → U i j = 0) →
      (∀ i : Fin (ch14ext_methodCDim steps), L i i = 1) →
      (∀ i j : Fin (ch14ext_methodCDim steps),
        j.val > i.val → L i j = 0) →
      ∀ i j : Fin (ch14ext_methodCDim steps),
        |∑ p : Fin (ch14ext_methodCDim steps), U i p *
              (∑ q : Fin (ch14ext_methodCDim steps),
                ch14ext_methodCInv fp steps U L p q * L q j) -
            (if i = j then 1 else 0)| ≤
          (4 * gamma fp (N + 2) + 3 * gamma fp (N + 2) ^ 2) *
            ∑ p : Fin (ch14ext_methodCDim steps), |U i p| *
              (∑ q : Fin (ch14ext_methodCDim steps),
                |ch14ext_methodCInv fp steps U L p q| * |L q j|) := by
  intro steps
  induction steps with
  | nil =>
      intro U L _ _ _ _ _ i
      exact i.elim0
  | cons a rest ih =>
      cases a
      intro U L hdim hUdiag hUT hLunit hLT i j
      let m := ch14ext_methodCDim rest
      let head : Fin (1 + m) := Fin.castAdd m (0 : Fin 1)
      let u11 : ℝ := U head head
      let u12 : Fin m → ℝ := fun q => U head (Fin.natAdd 1 q)
      let l21 : Fin m → ℝ := fun q => L (Fin.natAdd 1 q) head
      let U22 : Fin m → Fin m → ℝ :=
        fun p q => U (Fin.natAdd 1 p) (Fin.natAdd 1 q)
      let L22 : Fin m → Fin m → ℝ :=
        fun p q => L (Fin.natAdd 1 p) (Fin.natAdd 1 q)
      let X22 : Fin m → Fin m → ℝ :=
        ch14ext_methodCInv fp rest U22 L22
      have hmN : m ≤ N := by
        dsimp [m]
        dsimp [ch14ext_methodCDim] at hdim
        omega
      have hu11 : u11 ≠ 0 := hUdiag head
      have hUdiag22 : ∀ p : Fin m, U22 p p ≠ 0 := by
        intro p
        exact hUdiag (Fin.natAdd 1 p)
      have hUT22 : ∀ p q : Fin m, q.val < p.val → U22 p q = 0 := by
        intro p q hpq
        apply hUT
        simp only [Fin.val_natAdd]
        omega
      have hLunit22 : ∀ p : Fin m, L22 p p = 1 := by
        intro p
        exact hLunit (Fin.natAdd 1 p)
      have hLT22 : ∀ p q : Fin m, q.val > p.val → L22 p q = 0 := by
        intro p q hpq
        apply hLT
        simp only [Fin.val_natAdd]
        omega
      have h22raw := ih U22 L22 hmN hUdiag22 hUT22 hLunit22 hLT22
      have h22 : ∀ p q : Fin m,
          |∑ r : Fin m, U22 p r * (∑ s : Fin m, X22 r s * L22 s q) -
              (if p = q then 1 else 0)| ≤
            (4 * gamma fp (N + 2) + 3 * gamma fp (N + 2) ^ 2) *
              ∑ r : Fin m, |U22 p r| *
                (∑ s : Fin m, |X22 r s| * |L22 s q|) := by
        simpa [X22] using h22raw
      have hcomp := ch14ext_methodCStage_mixed_residual_bound fp N m
        u11 u12 l21 U22 X22 L22 hu11 hmN hN2 h22
      have hUeq : ch14ext_methodCStageU m u11 u12 U22 = U := by
        simpa [m, head, u11, u12, U22] using
          (ch14ext_methodCStageU_eq_of_upper m U hUT)
      have hLeq : ch14ext_methodCStageL m l21 L22 = L := by
        simpa [m, head, l21, L22] using
          (ch14ext_methodCStageL_eq_of_unit_lower m L hLunit hLT)
      have hXeq : ch14ext_methodCStageX fp m u11 u12 l21 X22 =
          ch14ext_methodCInv fp (() :: rest) U L := by
        rfl
      have hresult := hcomp i j
      simpa only [ch14ext_methodCStageMixedResidual,
        ch14ext_methodCStageAbsProduct, hUeq, hXeq, hLeq] using hresult

/-- **Higham equation (14.19), whole-loop Method C.**

For the matrix produced by the complete printed reverse-`k` recurrence,

`|U Xhat L - I| ≤ (4 gamma_(n+2) + 3 gamma_(n+2)^2) |U||Xhat||L|`,

where `n = ch14ext_methodCDim steps`.  The displayed coefficient is an honest
derived `c_n u` accumulator; in particular, the theorem has no one-stage or
whole-result residual premise. -/
theorem ch14ext_methodC_eq14_19 (fp : FPModel) (steps : List Unit)
    (U L : Fin (ch14ext_methodCDim steps) →
      Fin (ch14ext_methodCDim steps) → ℝ)
    (hn2 : gammaValid fp (ch14ext_methodCDim steps + 2))
    (hUdiag : ∀ i : Fin (ch14ext_methodCDim steps), U i i ≠ 0)
    (hUT : ∀ i j : Fin (ch14ext_methodCDim steps),
      j.val < i.val → U i j = 0)
    (hLunit : ∀ i : Fin (ch14ext_methodCDim steps), L i i = 1)
    (hLT : ∀ i j : Fin (ch14ext_methodCDim steps),
      j.val > i.val → L i j = 0) :
    ∀ i j : Fin (ch14ext_methodCDim steps),
      |∑ p : Fin (ch14ext_methodCDim steps), U i p *
            (∑ q : Fin (ch14ext_methodCDim steps),
              ch14ext_methodCInv fp steps U L p q * L q j) -
          (if i = j then 1 else 0)| ≤
        (4 * gamma fp (ch14ext_methodCDim steps + 2) +
            3 * gamma fp (ch14ext_methodCDim steps + 2) ^ 2) *
          ∑ p : Fin (ch14ext_methodCDim steps), |U i p| *
            (∑ q : Fin (ch14ext_methodCDim steps),
              |ch14ext_methodCInv fp steps U L p q| * |L q j|) :=
  ch14ext_methodCInv_mixed_residual fp (ch14ext_methodCDim steps) hn2
    steps U L le_rfl hUdiag hUT hLunit hLT

/-- Transport equation (14.19) from an arbitrary scalar-stage list to a
source-facing dimension `n`.  Eliminating `hdim` reduces all reindexing casts
to identities, so this theorem is exactly the whole-loop result above rather
than a new residual assumption. -/
theorem ch14ext_methodC_eq14_19_reindex (fp : FPModel) (n : ℕ)
    (steps : List Unit) (hdim : ch14ext_methodCDim steps = n)
    (U L : Fin n → Fin n → ℝ)
    (hn2 : gammaValid fp (n + 2))
    (hUdiag : ∀ i : Fin n, U i i ≠ 0)
    (hUT : ∀ i j : Fin n, j.val < i.val → U i j = 0)
    (hLunit : ∀ i : Fin n, L i i = 1)
    (hLT : ∀ i j : Fin n, j.val > i.val → L i j = 0) :
    ∀ i j : Fin n,
      |∑ p : Fin n, U i p *
            (∑ q : Fin n,
              ch14ext_methodCInvReindex fp steps hdim U L p q * L q j) -
          (if i = j then 1 else 0)| ≤
        (4 * gamma fp (n + 2) + 3 * gamma fp (n + 2) ^ 2) *
          ∑ p : Fin n, |U i p| *
            (∑ q : Fin n,
              |ch14ext_methodCInvReindex fp steps hdim U L p q| * |L q j|) := by
  subst n
  simpa [ch14ext_methodCInvReindex] using
    (ch14ext_methodC_eq14_19 fp steps U L hn2
      hUdiag hUT hLunit hLT)

/-- **Higham equation (14.19), arbitrary source dimension `n`.**

This is the clean `Fin n` endpoint.  Its computed matrix is the complete
reverse loop on the canonical `List.replicate n ()` stage list, transported by
the proved identity `ch14ext_methodCDim_steps`.  There is no target residual
hypothesis. -/
theorem ch14ext_methodC_eq14_19_nat (n : ℕ) (fp : FPModel)
    (U L : Fin n → Fin n → ℝ)
    (hn2 : gammaValid fp (n + 2))
    (hUdiag : ∀ i : Fin n, U i i ≠ 0)
    (hUT : ∀ i j : Fin n, j.val < i.val → U i j = 0)
    (hLunit : ∀ i : Fin n, L i i = 1)
    (hLT : ∀ i j : Fin n, j.val > i.val → L i j = 0) :
    ∀ i j : Fin n,
      |∑ p : Fin n, U i p *
            (∑ q : Fin n,
              ch14ext_methodCInvNat fp n U L p q * L q j) -
          (if i = j then 1 else 0)| ≤
        (4 * gamma fp (n + 2) + 3 * gamma fp (n + 2) ^ 2) *
          ∑ p : Fin n, |U i p| *
            (∑ q : Fin n,
              |ch14ext_methodCInvNat fp n U L p q| * |L q j|) := by
  simpa only [ch14ext_methodCInvNat] using
    (ch14ext_methodC_eq14_19_reindex fp n (ch14ext_methodCSteps n)
      (ch14ext_methodCDim_steps n) U L hn2 hUdiag hUT hLunit hLT)

/-- Doolittle-facing whole-loop Method C endpoint.  The unit lower-triangular
and upper-triangular shape obligations are supplied by the concrete rounded LU
factorization; only successful nonzero pivots and the gamma guard remain. -/
theorem ch14ext_methodC_eq14_19_doolittle (fp : FPModel) (steps : List Unit)
    (A L U : Fin (ch14ext_methodCDim steps) →
      Fin (ch14ext_methodCDim steps) → ℝ)
    (hn2 : gammaValid fp (ch14ext_methodCDim steps + 2))
    (hUnz : ∀ i : Fin (ch14ext_methodCDim steps), U i i ≠ 0)
    (hD : DoolittleLU (ch14ext_methodCDim steps) A L U fp) :
    ∀ i j : Fin (ch14ext_methodCDim steps),
      |∑ p : Fin (ch14ext_methodCDim steps), U i p *
            (∑ q : Fin (ch14ext_methodCDim steps),
              ch14ext_methodCInv fp steps U L p q * L q j) -
          (if i = j then 1 else 0)| ≤
        (4 * gamma fp (ch14ext_methodCDim steps + 2) +
            3 * gamma fp (ch14ext_methodCDim steps + 2) ^ 2) *
          ∑ p : Fin (ch14ext_methodCDim steps), |U i p| *
            (∑ q : Fin (ch14ext_methodCDim steps),
              |ch14ext_methodCInv fp steps U L p q| * |L q j|) := by
  exact ch14ext_methodC_eq14_19 fp steps U L hn2 hUnz hD.U_lower_zero
    (fun i => hD.L_diag i) hD.L_upper_zero

/-- Doolittle-facing equation (14.19) over the source dimension `Fin n`.
The concrete LU computation supplies the triangularity obligations; the inverse
is the complete canonical `n`-stage Method C reverse loop. -/
theorem ch14ext_methodC_eq14_19_nat_doolittle (n : ℕ) (fp : FPModel)
    (A L U : Fin n → Fin n → ℝ)
    (hn2 : gammaValid fp (n + 2))
    (hUnz : ∀ i : Fin n, U i i ≠ 0)
    (hD : DoolittleLU n A L U fp) :
    ∀ i j : Fin n,
      |∑ p : Fin n, U i p *
            (∑ q : Fin n,
              ch14ext_methodCInvNat fp n U L p q * L q j) -
          (if i = j then 1 else 0)| ≤
        (4 * gamma fp (n + 2) + 3 * gamma fp (n + 2) ^ 2) *
          ∑ p : Fin n, |U i p| *
            (∑ q : Fin n,
              |ch14ext_methodCInvNat fp n U L p q| * |L q j|) := by
  exact ch14ext_methodC_eq14_19_nat n fp U L hn2 hUnz
    hD.U_lower_zero (fun i => hD.L_diag i) hD.L_upper_zero

end NumStability.Ch14Ext
