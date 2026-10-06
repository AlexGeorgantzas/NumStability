import Mathlib.Algebra.Field.GeomSum
import Mathlib.Algebra.Polynomial.Roots
import Mathlib.Analysis.Complex.ExponentialBounds
import Mathlib.Analysis.Complex.Trigonometric
import Mathlib.Analysis.SpecialFunctions.Trigonometric.Basic
import Mathlib.Data.Fin.Tuple.Sort
import Mathlib.Data.Finset.Max
import Mathlib.Data.Fintype.Sort
import Mathlib.Data.Nat.Choose.Sum
import Mathlib.Data.Nat.Choose.Vandermonde
import Mathlib.LinearAlgebra.Matrix.Charpoly.Coeff
import Mathlib.LinearAlgebra.Matrix.SchurComplement
import Mathlib.Order.Interval.Finset.Fin
import Mathlib.Order.Interval.Finset.Nat
import NumStability.Algorithms.LU.GaussianElimination
import NumStability.Algorithms.LU.GrowthFactor
import NumStability.Algorithms.LU.LUSolve
import NumStability.Algorithms.LU.SpecialMatrices
import NumStability.Algorithms.LU.Tridiagonal
import NumStability.Algorithms.LU.TridiagonalCond
import NumStability.Algorithms.LU.TridiagonalRecurrence
import NumStability.Algorithms.LinearSystems.LU.BlockLU.BlockMatrices
import NumStability.Algorithms.LinearSystems.LU.BlockLU.PositiveDefinite
import NumStability.Algorithms.LinearSystems.LU.Doolittle.Assembly.Core
import NumStability.Analysis.FirstOrder.FixedPrecision
import NumStability.Analysis.MatrixNorms.EntrywiseMaximum
import NumStability.Source.Higham.Chapter07.LinearSystemsConditioning.ConditionNumbers
import NumStability.Source.Higham.Chapter07.LinearSystemsConditioning.Theorem04
import NumStability.Source.Higham.Chapter09.Section02
import NumStability.Source.Higham.Chapter09.Section03
import NumStability.Source.Higham.Chapter09.Section05

/-!
# Higham Chapter 9: Section06

Canonical source-correspondence owner from Chapter 9 destination-DAG layer 5.
-/

namespace NumStability

open scoped BigOperators
open ComplexConjugate
open Matrix

/-- **Theorem 9.12(a)**, SPD tridiagonal algebraic core.  If the exact
tridiagonal LU certificate has the source SPD factor shape `U = D L^T` with
positive diagonal `D`, then `|L||U| = |LU| = |A|` componentwise.  This proves
the local equality step in the printed proof; the existence of such a
factorization remains an explicit certificate input. -/
theorem higham9_12_spd_tridiag_absLU_eq_of_positive_DLT {n : ℕ}
    (A L U : Fin n → Fin n → ℝ) (d : Fin n → ℝ)
    (hStruct : IsTridiagLU n L U)
    (hLU_eq : ∀ i j : Fin n, ∑ k : Fin n, L i k * U k j = A i j)
    (hd_pos : ∀ k : Fin n, 0 < d k)
    (hDLT : ∀ k j : Fin n, U k j = d k * L j k) :
    ∀ i j : Fin n,
      ∑ k : Fin n, |L i k| * |U k j| = |A i j| :=
  tridiag_spd_shape_absLU_eq_absA L U A d hStruct hLU_eq hd_pos hDLT

/-- **Theorem 9.12(a)**, SPD tridiagonal backward-error handoff from the
explicit positive-`D L^T` LU certificate.  The theorem supplies the
componentwise growth hypothesis needed by the generic SPD LU backward-error
bound; it does not assert existence of the certificate. -/
theorem higham9_12_spd_tridiag_lu_backward_error_of_positive_DLT (n : ℕ)
    (A L_hat U_hat : Fin n → Fin n → ℝ) (d : Fin n → ℝ)
    (ε : ℝ) (hε : 0 ≤ ε)
    (hSPD : IsSymPosDef n A)
    (hLU : LUBackwardError n A L_hat U_hat ε)
    (hStruct : IsTridiagLU n L_hat U_hat)
    (hLU_eq : ∀ i j : Fin n, ∑ k : Fin n, L_hat i k * U_hat k j = A i j)
    (hd_pos : ∀ k : Fin n, 0 < d k)
    (hDLT : ∀ k j : Fin n, U_hat k j = d k * L_hat j k) :
    ∃ ΔA : Fin n → Fin n → ℝ,
      (∀ i j, |ΔA i j| ≤ ε * |A i j|) ∧
      (∀ i j, ∑ k : Fin n, L_hat i k * U_hat k j = A i j + ΔA i j) :=
  higham9_12_spd_lu_backward_error n A L_hat U_hat ε hε hSPD hLU
    (fun i j =>
      le_of_eq
        (higham9_12_spd_tridiag_absLU_eq_of_positive_DLT A L_hat U_hat d
          hStruct hLU_eq hd_pos hDLT i j))

/-- **Theorem 9.12(b/c)**, nonnegative LU factors give
`|L||U| = |A|`. -/
theorem higham9_12_nonneg_lu_optimal_growth (n : ℕ)
    (A L U : Fin n → Fin n → ℝ)
    (hNonneg : HasNonnegLUFactors n A L U) :
    ∀ i j : Fin n,
      ∑ k : Fin n, |L i k| * |U k j| = |A i j| :=
  nonneg_lu_optimal_growth n A L U hNonneg

/-- **Theorem 9.12**, max-entry growth consequence of optimal componentwise
growth.  If the unit-lower factor satisfies `|L||U| ≤ |A|`, then the final
upper factor has Higham max-entry growth factor at most one. -/
theorem higham9_growthFactorEntry_le_one_of_absLU_le_absA {n : ℕ} (hn : 0 < n)
    (A L U : Fin n → Fin n → ℝ)
    (hAmax : 0 < maxEntryNorm hn A)
    (hLdiag_abs : ∀ i : Fin n, |L i i| = 1)
    (hAbsLU_le : ∀ i j : Fin n,
      ∑ k : Fin n, |L i k| * |U k j| ≤ |A i j|) :
    growthFactorEntry hn A U hAmax ≤ 1 := by
  have hUmax_le_Amax : maxEntryNorm hn U ≤ maxEntryNorm hn A := by
    unfold maxEntryNorm
    apply Finset.sup'_le
    intro i _
    apply Finset.sup'_le
    intro j _
    have hterm :
        |L i i| * |U i j| ≤ ∑ k : Fin n, |L i k| * |U k j| :=
      Finset.single_le_sum
        (s := Finset.univ)
        (f := fun k : Fin n => |L i k| * |U k j|)
        (fun k _ => mul_nonneg (abs_nonneg _) (abs_nonneg _))
        (Finset.mem_univ i)
    have hU_le_absLU :
        |U i j| ≤ ∑ k : Fin n, |L i k| * |U k j| := by
      simpa [hLdiag_abs i] using hterm
    exact le_trans hU_le_absLU (le_trans (hAbsLU_le i j) (entry_le_maxEntryNorm hn A i j))
  unfold growthFactorEntry
  rw [div_le_iff₀ hAmax]
  simpa using hUmax_le_Amax

/-- **Theorem 9.12(a)**, max-entry growth consequence of the SPD
tridiagonal positive-`D L^T` LU certificate: Higham's growth factor satisfies
`rho <= 1`. -/
theorem higham9_12_spd_tridiag_growthFactorEntry_le_one {n : ℕ} (hn : 0 < n)
    (A L U : Fin n → Fin n → ℝ) (d : Fin n → ℝ)
    (hAmax : 0 < maxEntryNorm hn A)
    (hStruct : IsTridiagLU n L U)
    (hLU_eq : ∀ i j : Fin n, ∑ k : Fin n, L i k * U k j = A i j)
    (hd_pos : ∀ k : Fin n, 0 < d k)
    (hDLT : ∀ k j : Fin n, U k j = d k * L j k) :
    growthFactorEntry hn A U hAmax ≤ 1 := by
  apply higham9_growthFactorEntry_le_one_of_absLU_le_absA hn A L U hAmax
  · intro i
    simp [hStruct.L_diag i]
  · intro i j
    exact le_of_eq
      (higham9_12_spd_tridiag_absLU_eq_of_positive_DLT A L U d
        hStruct hLU_eq hd_pos hDLT i j)

/-- **Theorem 9.12(a)**, source-facing SPD max-entry growth package.

For a positive-dimensional SPD tridiagonal source matrix with a visible
positive-`D L^T` exact-LU certificate, the source max-entry denominator is
positive automatically, and Higham's max-entry growth factor satisfies
`rho <= 1`.  The exact-factor certificate remains explicit. -/
theorem higham9_12_spd_tridiag_growthFactorEntry_le_one_of_spd {n : ℕ}
    (hn : 0 < n)
    (A L U : Fin n → Fin n → ℝ) (d : Fin n → ℝ)
    (hSPD : IsSymPosDef n A)
    (hStruct : IsTridiagLU n L U)
    (hLU_eq : ∀ i j : Fin n, ∑ k : Fin n, L i k * U k j = A i j)
    (hd_pos : ∀ k : Fin n, 0 < d k)
    (hDLT : ∀ k j : Fin n, U k j = d k * L j k) :
    ∃ hAmax : 0 < maxEntryNorm hn A,
      growthFactorEntry hn A U hAmax ≤ 1 := by
  have hAmax : 0 < maxEntryNorm hn A :=
    maxEntryNorm_pos_of_det_ne_zero hn A
      (by simpa using isSymPosDef_det_ne_zero A hSPD)
  exact
    ⟨hAmax,
      higham9_12_spd_tridiag_growthFactorEntry_le_one hn A L U d hAmax
        hStruct hLU_eq hd_pos hDLT⟩

/-- **Theorem 9.12(b/c)**, nonnegative LU factors give max-entry growth
factor at most one. -/
theorem higham9_12_nonneg_lu_growthFactorEntry_le_one {n : ℕ} (hn : 0 < n)
    (A L U : Fin n → Fin n → ℝ)
    (hAmax : 0 < maxEntryNorm hn A)
    (hNonneg : HasNonnegLUFactors n A L U) :
    growthFactorEntry hn A U hAmax ≤ 1 := by
  apply higham9_growthFactorEntry_le_one_of_absLU_le_absA hn A L U hAmax
  · intro i
    simp [hNonneg.1.L_diag i]
  · intro i j
    exact le_of_eq (higham9_12_nonneg_lu_optimal_growth n A L U hNonneg i j)

/-- **Theorem 9.12(b/c)**, nonnegative LU no-growth with the positive
max-entry denominator derived from source nonsingularity. -/
theorem higham9_12_nonneg_lu_growthFactorEntry_le_one_of_det_ne_zero
    {n : ℕ} (hn : 0 < n)
    (A L U : Fin n → Fin n → ℝ)
    (hdetA : Matrix.det (Matrix.of A : Matrix (Fin n) (Fin n) ℝ) ≠ 0)
    (hNonneg : HasNonnegLUFactors n A L U) :
    ∃ hAmax : 0 < maxEntryNorm hn A,
      growthFactorEntry hn A U hAmax ≤ 1 := by
  have hAmax : 0 < maxEntryNorm hn A :=
    maxEntryNorm_pos_of_det_ne_zero hn A hdetA
  exact
    ⟨hAmax,
      higham9_12_nonneg_lu_growthFactorEntry_le_one hn A L U hAmax hNonneg⟩

/-- **Theorem 9.12(c)**, M-matrix optimal growth from nonnegative LU factors. -/
theorem higham9_12_mmatrix_lu_optimal_growth (n : ℕ)
    (A L U : Fin n → Fin n → ℝ)
    (hM : IsMMatrix n A)
    (hLU : LUFactSpec n A L U)
    (hL_nn : ∀ i k : Fin n, 0 ≤ L i k)
    (hU_nn : ∀ k j : Fin n, 0 ≤ U k j) :
    ∀ i j : Fin n,
      ∑ k : Fin n, |L i k| * |U k j| = |A i j| :=
  mmatrix_lu_optimal_growth n A L U hM hLU hL_nn hU_nn

/-- **Theorem 9.12(c)**, the M-matrix optimal-growth hypothesis also gives
Higham max-entry growth factor at most one. -/
theorem higham9_12_mmatrix_lu_growthFactorEntry_le_one {n : ℕ} (hn : 0 < n)
    (A L U : Fin n → Fin n → ℝ)
    (hAmax : 0 < maxEntryNorm hn A)
    (hM : IsMMatrix n A)
    (hLU : LUFactSpec n A L U)
    (hL_nn : ∀ i k : Fin n, 0 ≤ L i k)
    (hU_nn : ∀ k j : Fin n, 0 ≤ U k j) :
    growthFactorEntry hn A U hAmax ≤ 1 := by
  apply higham9_growthFactorEntry_le_one_of_absLU_le_absA hn A L U hAmax
  · intro i
    simp [hLU.L_diag i]
  · intro i j
    exact le_of_eq (higham9_12_mmatrix_lu_optimal_growth n A L U hM hLU hL_nn hU_nn i j)

/-- **Theorem 9.12(c)**, M-matrix no-growth with the positive max-entry
denominator derived from source nonsingularity. -/
theorem higham9_12_mmatrix_lu_growthFactorEntry_le_one_of_det_ne_zero
    {n : ℕ} (hn : 0 < n)
    (A L U : Fin n → Fin n → ℝ)
    (hdetA : Matrix.det (Matrix.of A : Matrix (Fin n) (Fin n) ℝ) ≠ 0)
    (hM : IsMMatrix n A)
    (hLU : LUFactSpec n A L U)
    (hL_nn : ∀ i k : Fin n, 0 ≤ L i k)
    (hU_nn : ∀ k j : Fin n, 0 ≤ U k j) :
    ∃ hAmax : 0 < maxEntryNorm hn A,
      growthFactorEntry hn A U hAmax ≤ 1 := by
  have hAmax : 0 < maxEntryNorm hn A :=
    maxEntryNorm_pos_of_det_ne_zero hn A hdetA
  exact
    ⟨hAmax,
      higham9_12_mmatrix_lu_growthFactorEntry_le_one hn A L U hAmax
        hM hLU hL_nn hU_nn⟩

/-- **Theorem 9.12(d)**, sign equivalence preserves optimal growth. -/
theorem higham9_12_sign_equiv_optimal_growth (n : ℕ)
    (B L_B U_B : Fin n → Fin n → ℝ)
    (D₁ D₂ : Fin n → Fin n → ℝ)
    (hD₁ : IsSignDiag n D₁) (hD₂ : IsSignDiag n D₂)
    (hB_growth : ∀ i j : Fin n,
      ∑ k : Fin n, |L_B i k| * |U_B k j| = |B i j|)
    (A : Fin n → Fin n → ℝ)
    (hA_eq : ∀ i j : Fin n,
      A i j = ∑ k₁ : Fin n, D₁ i k₁ * (∑ k₂ : Fin n, B k₁ k₂ * D₂ k₂ j))
    (L_A U_A : Fin n → Fin n → ℝ)
    (hLA_abs : ∀ i k : Fin n, |L_A i k| = |L_B i k|)
    (hUA_abs : ∀ k j : Fin n, |U_A k j| = |U_B k j|) :
    ∀ i j : Fin n,
      ∑ k : Fin n, |L_A i k| * |U_A k j| = |A i j| :=
  sign_equiv_optimal_growth n B L_B U_B D₁ D₂ hD₁ hD₂ hB_growth
    A hA_eq L_A U_A hLA_abs hUA_abs

/-- **Theorem 9.12(d)**, sign-equivalent optimal-growth factors also give
Higham max-entry growth factor at most one. -/
theorem higham9_12_sign_equiv_growthFactorEntry_le_one {n : ℕ} (hn : 0 < n)
    (B L_B U_B : Fin n → Fin n → ℝ)
    (D₁ D₂ : Fin n → Fin n → ℝ)
    (hD₁ : IsSignDiag n D₁) (hD₂ : IsSignDiag n D₂)
    (hB_growth : ∀ i j : Fin n,
      ∑ k : Fin n, |L_B i k| * |U_B k j| = |B i j|)
    (hLBdiag_abs : ∀ i : Fin n, |L_B i i| = 1)
    (A : Fin n → Fin n → ℝ)
    (hAmax : 0 < maxEntryNorm hn A)
    (hA_eq : ∀ i j : Fin n,
      A i j = ∑ k₁ : Fin n, D₁ i k₁ * (∑ k₂ : Fin n, B k₁ k₂ * D₂ k₂ j))
    (L_A U_A : Fin n → Fin n → ℝ)
    (hLA_abs : ∀ i k : Fin n, |L_A i k| = |L_B i k|)
    (hUA_abs : ∀ k j : Fin n, |U_A k j| = |U_B k j|) :
    growthFactorEntry hn A U_A hAmax ≤ 1 := by
  apply higham9_growthFactorEntry_le_one_of_absLU_le_absA hn A L_A U_A hAmax
  · intro i
    rw [hLA_abs i i, hLBdiag_abs i]
  · intro i j
    exact le_of_eq
      (higham9_12_sign_equiv_optimal_growth n B L_B U_B D₁ D₂ hD₁ hD₂
        hB_growth A hA_eq L_A U_A hLA_abs hUA_abs i j)

/-- **Theorem 9.12(d)**, sign-equivalent no-growth with the positive
max-entry denominator derived from source nonsingularity. -/
theorem higham9_12_sign_equiv_growthFactorEntry_le_one_of_det_ne_zero
    {n : ℕ} (hn : 0 < n)
    (B L_B U_B : Fin n → Fin n → ℝ)
    (D₁ D₂ : Fin n → Fin n → ℝ)
    (hD₁ : IsSignDiag n D₁) (hD₂ : IsSignDiag n D₂)
    (hB_growth : ∀ i j : Fin n,
      ∑ k : Fin n, |L_B i k| * |U_B k j| = |B i j|)
    (hLBdiag_abs : ∀ i : Fin n, |L_B i i| = 1)
    (A : Fin n → Fin n → ℝ)
    (hdetA : Matrix.det (Matrix.of A : Matrix (Fin n) (Fin n) ℝ) ≠ 0)
    (hA_eq : ∀ i j : Fin n,
      A i j = ∑ k₁ : Fin n, D₁ i k₁ * (∑ k₂ : Fin n, B k₁ k₂ * D₂ k₂ j))
    (L_A U_A : Fin n → Fin n → ℝ)
    (hLA_abs : ∀ i k : Fin n, |L_A i k| = |L_B i k|)
    (hUA_abs : ∀ k j : Fin n, |U_A k j| = |U_B k j|) :
    ∃ hAmax : 0 < maxEntryNorm hn A,
      growthFactorEntry hn A U_A hAmax ≤ 1 := by
  have hAmax : 0 < maxEntryNorm hn A :=
    maxEntryNorm_pos_of_det_ne_zero hn A hdetA
  exact
    ⟨hAmax,
      higham9_12_sign_equiv_growthFactorEntry_le_one hn B L_B U_B D₁ D₂
        hD₁ hD₂ hB_growth hLBdiag_abs A hAmax hA_eq L_A U_A hLA_abs hUA_abs⟩

/-- **Theorem 9.12(d)**, diagonal matrix generated by a sign vector. -/
def higham9_12_signDiagMatrix {n : ℕ} (d : Fin n → ℝ) :
    Fin n → Fin n → ℝ :=
  fun i j => if i = j then d i else 0

/-- **Theorem 9.12(d)**, a sign vector gives an `IsSignDiag` matrix. -/
theorem higham9_12_signDiagMatrix_isSignDiag {n : ℕ} {d : Fin n → ℝ}
    (hd : ∀ i : Fin n, |d i| = 1) :
    IsSignDiag n (higham9_12_signDiagMatrix d) := by
  constructor
  · intro i j hij
    simp [higham9_12_signDiagMatrix, hij]
  · intro i
    simp [higham9_12_signDiagMatrix, hd i]

/-- **Theorem 9.12(d)**, source `IsSignEquiv` data supplies the explicit
sign-diagonal matrix witnesses consumed by the existing sign-equivalence
growth theorems. -/
theorem higham9_12_sign_equiv_signDiag_witnesses {n : ℕ}
    {A B : Fin n → Fin n → ℝ}
    (hAB : IsSignEquiv n A B) :
    ∃ D₁ D₂ : Fin n → Fin n → ℝ,
      IsSignDiag n D₁ ∧ IsSignDiag n D₂ ∧
        (∀ i j : Fin n,
          A i j =
            ∑ k₁ : Fin n,
              D₁ i k₁ * (∑ k₂ : Fin n, B k₁ k₂ * D₂ k₂ j)) := by
  rcases hAB with ⟨d₁, d₂, hd₁, hd₂, hA⟩
  let D₁ : Fin n → Fin n → ℝ := higham9_12_signDiagMatrix d₁
  let D₂ : Fin n → Fin n → ℝ := higham9_12_signDiagMatrix d₂
  refine
    ⟨D₁, D₂,
      higham9_12_signDiagMatrix_isSignDiag hd₁,
      higham9_12_signDiagMatrix_isSignDiag hd₂, ?_⟩
  intro i j
  have hinner : ∀ k₁ : Fin n,
      (∑ k₂ : Fin n, B k₁ k₂ * D₂ k₂ j) = B k₁ j * d₂ j := by
    intro k₁
    rw [Finset.sum_eq_single j]
    · simp [D₂, higham9_12_signDiagMatrix]
    · intro k₂ _ hk₂
      simp [D₂, higham9_12_signDiagMatrix, hk₂]
    · intro hnot
      exact (hnot (Finset.mem_univ j)).elim
  have hsum :
      (∑ k₁ : Fin n,
        D₁ i k₁ * (∑ k₂ : Fin n, B k₁ k₂ * D₂ k₂ j)) =
        d₁ i * B i j * d₂ j := by
    rw [Finset.sum_eq_single i]
    · simp [D₁, higham9_12_signDiagMatrix, hinner]
      ring
    · intro k₁ _ hk₁
      simp [D₁, higham9_12_signDiagMatrix, Ne.symm hk₁]
    · intro hnot
      exact (hnot (Finset.mem_univ i)).elim
  rw [hA i j]
  exact hsum.symm

/-- **Theorem 9.12(d)**, source-predicate form of sign-equivalent optimal
growth.

This wraps the existing sign-diagonal theorem with the repository
`IsSignEquiv` predicate, leaving the absolute factor-structure hypotheses
visible. -/
theorem higham9_12_sign_equiv_optimal_growth_of_IsSignEquiv (n : ℕ)
    (A B L_B U_B L_A U_A : Fin n → Fin n → ℝ)
    (hAB : IsSignEquiv n A B)
    (hB_growth : ∀ i j : Fin n,
      ∑ k : Fin n, |L_B i k| * |U_B k j| = |B i j|)
    (hLA_abs : ∀ i k : Fin n, |L_A i k| = |L_B i k|)
    (hUA_abs : ∀ k j : Fin n, |U_A k j| = |U_B k j|) :
    ∀ i j : Fin n,
      ∑ k : Fin n, |L_A i k| * |U_A k j| = |A i j| := by
  obtain ⟨D₁, D₂, hD₁, hD₂, hA_eq⟩ :=
    higham9_12_sign_equiv_signDiag_witnesses hAB
  exact higham9_12_sign_equiv_optimal_growth n B L_B U_B D₁ D₂
    hD₁ hD₂ hB_growth A hA_eq L_A U_A hLA_abs hUA_abs

/-- **Theorem 9.12(d)**, source-predicate form of sign-equivalent max-entry
no-growth. -/
theorem higham9_12_sign_equiv_growthFactorEntry_le_one_of_IsSignEquiv
    {n : ℕ} (hn : 0 < n)
    (A B L_B U_B L_A U_A : Fin n → Fin n → ℝ)
    (hAB : IsSignEquiv n A B)
    (hB_growth : ∀ i j : Fin n,
      ∑ k : Fin n, |L_B i k| * |U_B k j| = |B i j|)
    (hLBdiag_abs : ∀ i : Fin n, |L_B i i| = 1)
    (hAmax : 0 < maxEntryNorm hn A)
    (hLA_abs : ∀ i k : Fin n, |L_A i k| = |L_B i k|)
    (hUA_abs : ∀ k j : Fin n, |U_A k j| = |U_B k j|) :
    growthFactorEntry hn A U_A hAmax ≤ 1 := by
  apply higham9_growthFactorEntry_le_one_of_absLU_le_absA hn A L_A U_A hAmax
  · intro i
    rw [hLA_abs i i, hLBdiag_abs i]
  · intro i j
    exact le_of_eq
      (higham9_12_sign_equiv_optimal_growth_of_IsSignEquiv
        n A B L_B U_B L_A U_A hAB hB_growth hLA_abs hUA_abs i j)

/-- **Theorem 9.12(d)**, source-predicate sign-equivalent no-growth with the
positive max-entry denominator derived from source nonsingularity. -/
theorem higham9_12_sign_equiv_growthFactorEntry_le_one_of_IsSignEquiv_det_ne_zero
    {n : ℕ} (hn : 0 < n)
    (A B L_B U_B L_A U_A : Fin n → Fin n → ℝ)
    (hAB : IsSignEquiv n A B)
    (hB_growth : ∀ i j : Fin n,
      ∑ k : Fin n, |L_B i k| * |U_B k j| = |B i j|)
    (hLBdiag_abs : ∀ i : Fin n, |L_B i i| = 1)
    (hdetA : Matrix.det (Matrix.of A : Matrix (Fin n) (Fin n) ℝ) ≠ 0)
    (hLA_abs : ∀ i k : Fin n, |L_A i k| = |L_B i k|)
    (hUA_abs : ∀ k j : Fin n, |U_A k j| = |U_B k j|) :
    ∃ hAmax : 0 < maxEntryNorm hn A,
      growthFactorEntry hn A U_A hAmax ≤ 1 := by
  have hAmax : 0 < maxEntryNorm hn A :=
    maxEntryNorm_pos_of_det_ne_zero hn A hdetA
  exact
    ⟨hAmax,
      higham9_12_sign_equiv_growthFactorEntry_le_one_of_IsSignEquiv
        hn A B L_B U_B L_A U_A hAB hB_growth hLBdiag_abs hAmax
        hLA_abs hUA_abs⟩

/-- **Theorem 9.12(b/c)**, native Matrix form of nonnegative-LU no-growth
with the positive max-entry denominator derived from source nonsingularity. -/
theorem higham9_12_matrix_nonneg_lu_growthFactorEntry_le_one_of_det_ne_zero
    {n : ℕ} (hn : 0 < n)
    (A L U : Matrix (Fin n) (Fin n) ℝ)
    (hdetA : Matrix.det A ≠ 0)
    (hNonneg : HasNonnegLUFactors n A L U) :
    ∃ hAmax : 0 < maxEntryNorm hn A,
      growthFactorEntry hn A U hAmax ≤ 1 :=
  higham9_12_nonneg_lu_growthFactorEntry_le_one_of_det_ne_zero
    hn A L U (by simpa using hdetA) hNonneg

/-- **Theorem 9.12(c)**, native Matrix form of the M-matrix no-growth
endpoint with the positive max-entry denominator derived from source
nonsingularity. -/
theorem higham9_12_matrix_mmatrix_lu_growthFactorEntry_le_one_of_det_ne_zero
    {n : ℕ} (hn : 0 < n)
    (A L U : Matrix (Fin n) (Fin n) ℝ)
    (hdetA : Matrix.det A ≠ 0)
    (hM : IsMMatrix n A)
    (hLU : LUFactSpec n A L U)
    (hL_nn : ∀ i k : Fin n, 0 ≤ L i k)
    (hU_nn : ∀ k j : Fin n, 0 ≤ U k j) :
    ∃ hAmax : 0 < maxEntryNorm hn A,
      growthFactorEntry hn A U hAmax ≤ 1 :=
  higham9_12_mmatrix_lu_growthFactorEntry_le_one_of_det_ne_zero
    hn A L U (by simpa using hdetA) hM hLU hL_nn hU_nn

/-- **Theorem 9.12(d)**, native Matrix form of sign-equivalent no-growth
with explicit sign-diagonal witnesses and nonsingular source denominator. -/
theorem higham9_12_matrix_sign_equiv_growthFactorEntry_le_one_of_det_ne_zero
    {n : ℕ} (hn : 0 < n)
    (B L_B U_B D₁ D₂ : Matrix (Fin n) (Fin n) ℝ)
    (hD₁ : IsSignDiag n D₁) (hD₂ : IsSignDiag n D₂)
    (hB_growth : ∀ i j : Fin n,
      ∑ k : Fin n, |L_B i k| * |U_B k j| = |B i j|)
    (hLBdiag_abs : ∀ i : Fin n, |L_B i i| = 1)
    (A : Matrix (Fin n) (Fin n) ℝ)
    (hdetA : Matrix.det A ≠ 0)
    (hA_eq : ∀ i j : Fin n,
      A i j = ∑ k₁ : Fin n, D₁ i k₁ * (∑ k₂ : Fin n, B k₁ k₂ * D₂ k₂ j))
    (L_A U_A : Matrix (Fin n) (Fin n) ℝ)
    (hLA_abs : ∀ i k : Fin n, |L_A i k| = |L_B i k|)
    (hUA_abs : ∀ k j : Fin n, |U_A k j| = |U_B k j|) :
    ∃ hAmax : 0 < maxEntryNorm hn A,
      growthFactorEntry hn A U_A hAmax ≤ 1 :=
  higham9_12_sign_equiv_growthFactorEntry_le_one_of_det_ne_zero
    hn B L_B U_B D₁ D₂ hD₁ hD₂ hB_growth hLBdiag_abs
    A (by simpa using hdetA) hA_eq L_A U_A hLA_abs hUA_abs

/-- **Theorem 9.12(d)**, native Matrix form of source-predicate
sign-equivalent no-growth with the positive denominator derived from
source nonsingularity. -/
theorem higham9_12_matrix_sign_equiv_growthFactorEntry_le_one_of_IsSignEquiv_det_ne_zero
    {n : ℕ} (hn : 0 < n)
    (A B L_B U_B L_A U_A : Matrix (Fin n) (Fin n) ℝ)
    (hAB : IsSignEquiv n A B)
    (hB_growth : ∀ i j : Fin n,
      ∑ k : Fin n, |L_B i k| * |U_B k j| = |B i j|)
    (hLBdiag_abs : ∀ i : Fin n, |L_B i i| = 1)
    (hdetA : Matrix.det A ≠ 0)
    (hLA_abs : ∀ i k : Fin n, |L_A i k| = |L_B i k|)
    (hUA_abs : ∀ k j : Fin n, |U_A k j| = |U_B k j|) :
    ∃ hAmax : 0 < maxEntryNorm hn A,
      growthFactorEntry hn A U_A hAmax ≤ 1 :=
  higham9_12_sign_equiv_growthFactorEntry_le_one_of_IsSignEquiv_det_ne_zero
    hn A B L_B U_B L_A U_A hAB hB_growth hLBdiag_abs
    (by simpa using hdetA) hLA_abs hUA_abs

/-- **Equations (9.18)--(9.19)**: tridiagonal source data. -/
abbrev higham9_18_TridiagData (n : ℕ) : Type :=
  TridiagData n

/-- **Equation (9.18)**: convert tridiagonal data to its matrix. -/
noncomputable def higham9_18_tridiag_to_matrix {n : ℕ}
    (T : higham9_18_TridiagData n) : Fin n → Fin n → ℝ :=
  tridiag_to_matrix T

/-- **Equation (9.18)**, the matrix assembled from tridiagonal source data is
tridiagonal in the repository structural predicate. -/
theorem higham9_18_tridiag_to_matrix_isTridiagonal {n : ℕ}
    (T : higham9_18_TridiagData n) :
    IsTridiagonal n (higham9_18_tridiag_to_matrix T) :=
  tridiag_to_matrix_isTridiagonal T

/-- **Equation (9.18)**, the matrix assembled from tridiagonal source data is
also a common-bandwidth-one matrix. -/
theorem higham9_18_tridiag_to_matrix_isBanded_one_one {n : ℕ}
    (T : higham9_18_TridiagData n) :
    IsBanded n 1 1 (higham9_18_tridiag_to_matrix T) :=
  isBanded_one_one_of_isTridiagonal
    (higham9_18_tridiag_to_matrix_isTridiagonal T)

/-- **Theorem 9.11 / equation (9.18)**, source-data tridiagonal Bohte solve
wrapper.

This instantiates the bandwidth-one Bohte solve interface for matrices
assembled from `TridiagData`; the tridiagonal GEPP growth estimate remains an
explicit source hypothesis. -/
theorem higham9_11_tridiag_data_bohte_solve_tight
    (fp : FPModel) {n : ℕ}
    (T : higham9_18_TridiagData n)
    (L_hat U_hat : Fin n → Fin n → ℝ)
    (b : Fin n → ℝ)
    (hL_diag : ∀ i : Fin n, L_hat i i ≠ 0)
    (hU_diag : ∀ i : Fin n, U_hat i i ≠ 0)
    (hLU : LUBackwardError n (higham9_18_tridiag_to_matrix T)
      L_hat U_hat (gamma fp n))
    (hn : gammaValid fp n)
    (hn3 : gammaValid fp (3 * n))
    (hGrowth : ∀ i j : Fin n,
      ∑ k : Fin n, |L_hat i k| * |U_hat k j| ≤
        2 * |higham9_18_tridiag_to_matrix T i j|) :
    let y_hat := fl_forwardSub fp n L_hat b
    let x_hat := fl_backSub fp n U_hat y_hat
    ∃ ΔA : Fin n → Fin n → ℝ,
      (∀ i j, |ΔA i j| ≤
        2 * gamma fp (3 * n) *
          |higham9_18_tridiag_to_matrix T i j|) ∧
      (∀ i, ∑ j : Fin n,
        (higham9_18_tridiag_to_matrix T i j + ΔA i j) * x_hat j = b i) :=
  higham9_11_bandwidth_one_bohte_solve_tight_of_isBanded fp n
    (higham9_18_tridiag_to_matrix T) L_hat U_hat b
    (higham9_18_tridiag_to_matrix_isBanded_one_one T)
    hL_diag hU_diag hLU hn hn3 hGrowth

/-- **Equation (9.19)**: computed tridiagonal LU recurrence. -/
noncomputable def higham9_19_tridiag_lu (fp : FPModel) {n : ℕ}
    (T : higham9_18_TridiagData n) : (Fin n → ℝ) × (Fin n → ℝ) :=
  tridiag_lu fp T

/-- **Equation (9.19)**: exact-arithmetic tridiagonal LU recurrence predicate.

This records the algebraic side of the displayed recurrence separately from
the rounded `FPModel` implementation. -/
abbrev higham9_19_TridiagExactLURecurrence {n : ℕ}
    (T : higham9_18_TridiagData n) (l_hat u_hat : Fin n → ℝ) : Prop :=
  TridiagExactLURecurrence T l_hat u_hat

/-- **Equation (9.19)**: a positive tridiagonal index's predecessor. -/
def higham9_19_tridiag_prevIndex {n : ℕ} (i : Fin n)
    (hi : 0 < i.val) : Fin n :=
  tridiag_prevIndex i hi

/-- **Equation (9.19)**, exact recurrence product certificate.

If the explicit tridiagonal factors satisfy the exact recurrence, their matrix
product is the source tridiagonal matrix. -/
theorem higham9_19_tridiag_exact_product_of_recurrence {n : ℕ}
    (T : higham9_18_TridiagData n) (l_hat u_hat : Fin n → ℝ)
    (hrec : higham9_19_TridiagExactLURecurrence T l_hat u_hat) :
    ∀ i j : Fin n,
      ∑ k : Fin n, tridiag_L_matrix l_hat i k *
        tridiag_U_matrix u_hat T.c k j =
        higham9_18_tridiag_to_matrix T i j :=
  tridiag_exact_product_of_recurrence T l_hat u_hat hrec

/-- **Equation (9.19)**, exact-product certificate as an ordinary exact
`LUFactSpec` for the explicit tridiagonal matrix builders. -/
theorem higham9_19_tridiag_LUFactSpec_of_exact_product {n : ℕ}
    (T : higham9_18_TridiagData n) (l_hat u_hat : Fin n → ℝ)
    (hLU_exact : ∀ i j : Fin n,
      ∑ k : Fin n, tridiag_L_matrix l_hat i k *
        tridiag_U_matrix u_hat T.c k j =
        higham9_18_tridiag_to_matrix T i j) :
    LUFactSpec n (higham9_18_tridiag_to_matrix T)
      (tridiag_L_matrix l_hat) (tridiag_U_matrix u_hat T.c) :=
  { L_diag := tridiag_L_diag l_hat
    L_upper_zero := tridiag_L_upper_zero l_hat
    U_lower_zero := tridiag_U_lower_zero u_hat T.c
    product_eq := hLU_exact }

/-- **Equation (9.19)**, exact tridiagonal recurrence as an ordinary exact
`LUFactSpec` for the explicit matrix builders. -/
theorem higham9_19_tridiag_LUFactSpec_of_recurrence {n : ℕ}
    (T : higham9_18_TridiagData n) (l_hat u_hat : Fin n → ℝ)
    (hrec : higham9_19_TridiagExactLURecurrence T l_hat u_hat) :
    LUFactSpec n (higham9_18_tridiag_to_matrix T)
      (tridiag_L_matrix l_hat) (tridiag_U_matrix u_hat T.c) :=
  higham9_19_tridiag_LUFactSpec_of_exact_product T l_hat u_hat
    (higham9_19_tridiag_exact_product_of_recurrence T l_hat u_hat hrec)

/-- **Theorem 9.11 / Equation (9.19)**, Bohte solve bound for exact
tridiagonal recurrence factors assembled from `TridiagData`.

The recurrence supplies an exact `LUFactSpec`, which is weakened to the public
`LUBackwardError` interface.  The remaining Bohte-specific tridiagonal GEPP
growth estimate `|Lhat||Uhat| <= 2|A|` is still an explicit source hypothesis. -/
theorem higham9_11_tridiag_data_bohte_solve_tight_of_exact_recurrence
    (fp : FPModel) {n : ℕ}
    (T : higham9_18_TridiagData n)
    (l_hat u_hat : Fin n → ℝ)
    (b : Fin n → ℝ)
    (hU_diag : ∀ i : Fin n, tridiag_U_matrix u_hat T.c i i ≠ 0)
    (hrec : higham9_19_TridiagExactLURecurrence T l_hat u_hat)
    (hn : gammaValid fp n)
    (hn3 : gammaValid fp (3 * n))
    (hGrowth : ∀ i j : Fin n,
      ∑ k : Fin n, |tridiag_L_matrix l_hat i k| *
          |tridiag_U_matrix u_hat T.c k j| ≤
        2 * |higham9_18_tridiag_to_matrix T i j|) :
    let y_hat := fl_forwardSub fp n (tridiag_L_matrix l_hat) b
    let x_hat := fl_backSub fp n (tridiag_U_matrix u_hat T.c) y_hat
    ∃ ΔA : Fin n → Fin n → ℝ,
      (∀ i j, |ΔA i j| ≤
        2 * gamma fp (3 * n) *
          |higham9_18_tridiag_to_matrix T i j|) ∧
      (∀ i, ∑ j : Fin n,
        (higham9_18_tridiag_to_matrix T i j + ΔA i j) * x_hat j = b i) :=
  higham9_11_tridiag_data_bohte_solve_tight fp T
    (tridiag_L_matrix l_hat) (tridiag_U_matrix u_hat T.c) b
    (fun i => by
      rw [tridiag_L_diag l_hat i]
      norm_num)
    hU_diag
    (higham9_LUFactSpec_to_LUBackwardError_gamma fp n hn
      (higham9_19_tridiag_LUFactSpec_of_recurrence T l_hat u_hat hrec))
    hn hn3 hGrowth

/-- **Theorem 9.11 / equation (9.18)**, native Matrix form of the source-data
tridiagonal Bohte solve wrapper. -/
theorem higham9_11_matrix_tridiag_data_bohte_solve_tight
    (fp : FPModel) {n : ℕ}
    (T : higham9_18_TridiagData n)
    (L_hat U_hat : Matrix (Fin n) (Fin n) ℝ)
    (b : Fin n → ℝ)
    (hL_diag : ∀ i : Fin n, L_hat i i ≠ 0)
    (hU_diag : ∀ i : Fin n, U_hat i i ≠ 0)
    (hLU : LUBackwardError n (higham9_18_tridiag_to_matrix T)
      L_hat U_hat (gamma fp n))
    (hn : gammaValid fp n)
    (hn3 : gammaValid fp (3 * n))
    (hGrowth : ∀ i j : Fin n,
      ∑ k : Fin n, |L_hat i k| * |U_hat k j| ≤
        2 * |higham9_18_tridiag_to_matrix T i j|) :
    let y_hat := fl_forwardSub fp n L_hat b
    let x_hat := fl_backSub fp n U_hat y_hat
    ∃ DeltaA : Matrix (Fin n) (Fin n) ℝ,
      (∀ i j, |DeltaA i j| ≤
        2 * gamma fp (3 * n) *
          |higham9_18_tridiag_to_matrix T i j|) ∧
      Matrix.mulVec
        (fun i j => higham9_18_tridiag_to_matrix T i j + DeltaA i j)
        x_hat = b := by
  intro y_hat x_hat
  obtain ⟨DeltaA, hDeltaA_bound, hDeltaA_eq⟩ :=
    higham9_11_tridiag_data_bohte_solve_tight fp T L_hat U_hat b
      hL_diag hU_diag hLU hn hn3 hGrowth
  refine ⟨DeltaA, hDeltaA_bound, ?_⟩
  funext i
  simpa [Matrix.mulVec, dotProduct] using hDeltaA_eq i

/-- **Theorem 9.11 / Equation (9.19)**, native Matrix form of the Bohte solve
bound for exact tridiagonal recurrence factors assembled from `TridiagData`. -/
theorem higham9_11_matrix_tridiag_data_bohte_solve_tight_of_exact_recurrence
    (fp : FPModel) {n : ℕ}
    (T : higham9_18_TridiagData n)
    (l_hat u_hat : Fin n → ℝ)
    (b : Fin n → ℝ)
    (hU_diag : ∀ i : Fin n, tridiag_U_matrix u_hat T.c i i ≠ 0)
    (hrec : higham9_19_TridiagExactLURecurrence T l_hat u_hat)
    (hn : gammaValid fp n)
    (hn3 : gammaValid fp (3 * n))
    (hGrowth : ∀ i j : Fin n,
      ∑ k : Fin n, |tridiag_L_matrix l_hat i k| *
          |tridiag_U_matrix u_hat T.c k j| ≤
        2 * |higham9_18_tridiag_to_matrix T i j|) :
    let y_hat := fl_forwardSub fp n (tridiag_L_matrix l_hat) b
    let x_hat := fl_backSub fp n (tridiag_U_matrix u_hat T.c) y_hat
    ∃ DeltaA : Matrix (Fin n) (Fin n) ℝ,
      (∀ i j, |DeltaA i j| ≤
        2 * gamma fp (3 * n) *
          |higham9_18_tridiag_to_matrix T i j|) ∧
      Matrix.mulVec
        (fun i j => higham9_18_tridiag_to_matrix T i j + DeltaA i j)
        x_hat = b := by
  intro y_hat x_hat
  obtain ⟨DeltaA, hDeltaA_bound, hDeltaA_eq⟩ :=
    higham9_11_tridiag_data_bohte_solve_tight_of_exact_recurrence
      fp T l_hat u_hat b hU_diag hrec hn hn3 hGrowth
  refine ⟨DeltaA, hDeltaA_bound, ?_⟩
  funext i
  simpa [Matrix.mulVec, dotProduct] using hDeltaA_eq i

/-- **Theorem 9.12(a)**, explicit tridiagonal-builder SPD algebraic core.
For factors assembled from equation (9.19)'s `L`/`U` builders, a visible
positive-`D L^T` certificate gives `|L||U| = |A|` componentwise. -/
theorem higham9_12_spd_tridiag_builder_absLU_eq_of_positive_DLT {n : ℕ}
    (T : higham9_18_TridiagData n) (l_hat u_hat d : Fin n → ℝ)
    (hLU_exact : ∀ i j : Fin n,
      ∑ k : Fin n, tridiag_L_matrix l_hat i k *
        tridiag_U_matrix u_hat T.c k j =
        higham9_18_tridiag_to_matrix T i j)
    (hd_pos : ∀ k : Fin n, 0 < d k)
    (hDLT : ∀ k j : Fin n,
      tridiag_U_matrix u_hat T.c k j = d k * tridiag_L_matrix l_hat j k) :
    ∀ i j : Fin n,
      ∑ k : Fin n, |tridiag_L_matrix l_hat i k| *
        |tridiag_U_matrix u_hat T.c k j| =
        |higham9_18_tridiag_to_matrix T i j| :=
  higham9_12_spd_tridiag_absLU_eq_of_positive_DLT
    (higham9_18_tridiag_to_matrix T)
    (tridiag_L_matrix l_hat) (tridiag_U_matrix u_hat T.c) d
    (tridiag_matrices_isTridiagLU l_hat u_hat T.c)
    hLU_exact hd_pos hDLT

/-- **Theorem 9.12(a)**, explicit tridiagonal-builder SPD max-entry growth
consequence `rho <= 1` from a positive-`D L^T` certificate. -/
theorem higham9_12_spd_tridiag_builder_growthFactorEntry_le_one {n : ℕ}
    (hn : 0 < n)
    (T : higham9_18_TridiagData n) (l_hat u_hat d : Fin n → ℝ)
    (hAmax : 0 < maxEntryNorm hn (higham9_18_tridiag_to_matrix T))
    (hLU_exact : ∀ i j : Fin n,
      ∑ k : Fin n, tridiag_L_matrix l_hat i k *
        tridiag_U_matrix u_hat T.c k j =
        higham9_18_tridiag_to_matrix T i j)
    (hd_pos : ∀ k : Fin n, 0 < d k)
    (hDLT : ∀ k j : Fin n,
      tridiag_U_matrix u_hat T.c k j = d k * tridiag_L_matrix l_hat j k) :
    growthFactorEntry hn (higham9_18_tridiag_to_matrix T)
      (tridiag_U_matrix u_hat T.c) hAmax ≤ 1 :=
  higham9_12_spd_tridiag_growthFactorEntry_le_one hn
    (higham9_18_tridiag_to_matrix T)
    (tridiag_L_matrix l_hat) (tridiag_U_matrix u_hat T.c) d
    hAmax
    (tridiag_matrices_isTridiagLU l_hat u_hat T.c)
    hLU_exact hd_pos hDLT

/-- **Theorem 9.12(a)**, explicit tridiagonal-builder SPD max-entry growth
package with the positive source denominator derived from SPD. -/
theorem higham9_12_spd_tridiag_builder_growthFactorEntry_le_one_of_spd
    {n : ℕ} (hn : 0 < n)
    (T : higham9_18_TridiagData n) (l_hat u_hat d : Fin n → ℝ)
    (hSPD : IsSymPosDef n (higham9_18_tridiag_to_matrix T))
    (hLU_exact : ∀ i j : Fin n,
      ∑ k : Fin n, tridiag_L_matrix l_hat i k *
        tridiag_U_matrix u_hat T.c k j =
        higham9_18_tridiag_to_matrix T i j)
    (hd_pos : ∀ k : Fin n, 0 < d k)
    (hDLT : ∀ k j : Fin n,
      tridiag_U_matrix u_hat T.c k j = d k * tridiag_L_matrix l_hat j k) :
    ∃ hAmax : 0 < maxEntryNorm hn (higham9_18_tridiag_to_matrix T),
      growthFactorEntry hn (higham9_18_tridiag_to_matrix T)
        (tridiag_U_matrix u_hat T.c) hAmax ≤ 1 := by
  have hAmax :
      0 < maxEntryNorm hn (higham9_18_tridiag_to_matrix T) :=
    maxEntryNorm_pos_of_det_ne_zero hn (higham9_18_tridiag_to_matrix T)
      (by
        simpa using
          isSymPosDef_det_ne_zero (higham9_18_tridiag_to_matrix T) hSPD)
  exact
    ⟨hAmax,
      higham9_12_spd_tridiag_builder_growthFactorEntry_le_one
        hn T l_hat u_hat d hAmax hLU_exact hd_pos hDLT⟩

/-- **Theorem 9.12(a)**, explicit tridiagonal-builder SPD backward-error
handoff from a positive-`D L^T` certificate. -/
theorem higham9_12_spd_tridiag_builder_lu_backward_error_of_positive_DLT
    (n : ℕ)
    (T : higham9_18_TridiagData n) (l_hat u_hat d : Fin n → ℝ)
    (ε : ℝ) (hε : 0 ≤ ε)
    (hSPD : IsSymPosDef n (higham9_18_tridiag_to_matrix T))
    (hLU : LUBackwardError n (higham9_18_tridiag_to_matrix T)
      (tridiag_L_matrix l_hat) (tridiag_U_matrix u_hat T.c) ε)
    (hLU_exact : ∀ i j : Fin n,
      ∑ k : Fin n, tridiag_L_matrix l_hat i k *
        tridiag_U_matrix u_hat T.c k j =
        higham9_18_tridiag_to_matrix T i j)
    (hd_pos : ∀ k : Fin n, 0 < d k)
    (hDLT : ∀ k j : Fin n,
      tridiag_U_matrix u_hat T.c k j = d k * tridiag_L_matrix l_hat j k) :
    ∃ ΔA : Fin n → Fin n → ℝ,
      (∀ i j, |ΔA i j| ≤ ε * |higham9_18_tridiag_to_matrix T i j|) ∧
      (∀ i j,
        ∑ k : Fin n, tridiag_L_matrix l_hat i k *
            tridiag_U_matrix u_hat T.c k j =
          higham9_18_tridiag_to_matrix T i j + ΔA i j) :=
  higham9_12_spd_tridiag_lu_backward_error_of_positive_DLT n
    (higham9_18_tridiag_to_matrix T)
    (tridiag_L_matrix l_hat) (tridiag_U_matrix u_hat T.c) d
    ε hε hSPD hLU
    (tridiag_matrices_isTridiagLU l_hat u_hat T.c)
    hLU_exact hd_pos hDLT

/-- **Theorem 9.12(a)**, exact-recurrence builder form of the SPD
positive-`D L^T` equality.  The equation (9.19) exact recurrence supplies the
product certificate. -/
theorem higham9_12_spd_tridiag_builder_absLU_eq_of_recurrence {n : ℕ}
    (T : higham9_18_TridiagData n) (l_hat u_hat d : Fin n → ℝ)
    (hrec : higham9_19_TridiagExactLURecurrence T l_hat u_hat)
    (hd_pos : ∀ k : Fin n, 0 < d k)
    (hDLT : ∀ k j : Fin n,
      tridiag_U_matrix u_hat T.c k j = d k * tridiag_L_matrix l_hat j k) :
    ∀ i j : Fin n,
      ∑ k : Fin n, |tridiag_L_matrix l_hat i k| *
        |tridiag_U_matrix u_hat T.c k j| =
        |higham9_18_tridiag_to_matrix T i j| :=
  higham9_12_spd_tridiag_builder_absLU_eq_of_positive_DLT T l_hat u_hat d
    (higham9_19_tridiag_exact_product_of_recurrence T l_hat u_hat hrec)
    hd_pos hDLT

/-- **Theorem 9.12(a)**, exact-recurrence builder form of the SPD
positive-`D L^T` max-entry growth consequence. -/
theorem higham9_12_spd_tridiag_builder_growthFactorEntry_le_one_of_recurrence
    {n : ℕ} (hn : 0 < n)
    (T : higham9_18_TridiagData n) (l_hat u_hat d : Fin n → ℝ)
    (hAmax : 0 < maxEntryNorm hn (higham9_18_tridiag_to_matrix T))
    (hrec : higham9_19_TridiagExactLURecurrence T l_hat u_hat)
    (hd_pos : ∀ k : Fin n, 0 < d k)
    (hDLT : ∀ k j : Fin n,
      tridiag_U_matrix u_hat T.c k j = d k * tridiag_L_matrix l_hat j k) :
    growthFactorEntry hn (higham9_18_tridiag_to_matrix T)
      (tridiag_U_matrix u_hat T.c) hAmax ≤ 1 :=
  higham9_12_spd_tridiag_builder_growthFactorEntry_le_one hn T l_hat u_hat d
    hAmax
    (higham9_19_tridiag_exact_product_of_recurrence T l_hat u_hat hrec)
    hd_pos hDLT

/-- **Theorem 9.12(a)**, exact-recurrence builder SPD max-entry growth
package with the positive source denominator derived from SPD. -/
theorem higham9_12_spd_tridiag_builder_growthFactorEntry_le_one_of_spd_recurrence
    {n : ℕ} (hn : 0 < n)
    (T : higham9_18_TridiagData n) (l_hat u_hat d : Fin n → ℝ)
    (hSPD : IsSymPosDef n (higham9_18_tridiag_to_matrix T))
    (hrec : higham9_19_TridiagExactLURecurrence T l_hat u_hat)
    (hd_pos : ∀ k : Fin n, 0 < d k)
    (hDLT : ∀ k j : Fin n,
      tridiag_U_matrix u_hat T.c k j = d k * tridiag_L_matrix l_hat j k) :
    ∃ hAmax : 0 < maxEntryNorm hn (higham9_18_tridiag_to_matrix T),
      growthFactorEntry hn (higham9_18_tridiag_to_matrix T)
        (tridiag_U_matrix u_hat T.c) hAmax ≤ 1 := by
  exact
    higham9_12_spd_tridiag_builder_growthFactorEntry_le_one_of_spd
      hn T l_hat u_hat d hSPD
      (higham9_19_tridiag_exact_product_of_recurrence T l_hat u_hat hrec)
      hd_pos hDLT

/-- **Theorem 9.12(a)**, exact-recurrence builder form of the SPD
positive-`D L^T` backward-error handoff. -/
theorem higham9_12_spd_tridiag_builder_lu_backward_error_of_recurrence
    (n : ℕ)
    (T : higham9_18_TridiagData n) (l_hat u_hat d : Fin n → ℝ)
    (ε : ℝ) (hε : 0 ≤ ε)
    (hSPD : IsSymPosDef n (higham9_18_tridiag_to_matrix T))
    (hLU : LUBackwardError n (higham9_18_tridiag_to_matrix T)
      (tridiag_L_matrix l_hat) (tridiag_U_matrix u_hat T.c) ε)
    (hrec : higham9_19_TridiagExactLURecurrence T l_hat u_hat)
    (hd_pos : ∀ k : Fin n, 0 < d k)
    (hDLT : ∀ k j : Fin n,
      tridiag_U_matrix u_hat T.c k j = d k * tridiag_L_matrix l_hat j k) :
    ∃ ΔA : Fin n → Fin n → ℝ,
      (∀ i j, |ΔA i j| ≤ ε * |higham9_18_tridiag_to_matrix T i j|) ∧
      (∀ i j,
        ∑ k : Fin n, tridiag_L_matrix l_hat i k *
            tridiag_U_matrix u_hat T.c k j =
          higham9_18_tridiag_to_matrix T i j + ΔA i j) :=
  higham9_12_spd_tridiag_builder_lu_backward_error_of_positive_DLT n
    T l_hat u_hat d ε hε hSPD hLU
    (higham9_19_tridiag_exact_product_of_recurrence T l_hat u_hat hrec)
    hd_pos hDLT

/-- **Theorem 9.12(a)**, native Matrix form of the SPD LU backward-error
handoff once the optimal componentwise growth inequality has been supplied. -/
theorem higham9_12_matrix_spd_lu_backward_error (n : ℕ)
    (A L_hat U_hat : Matrix (Fin n) (Fin n) ℝ)
    (ε : ℝ) (hε : 0 ≤ ε)
    (hSPD : IsSymPosDef n A)
    (hLU : LUBackwardError n A L_hat U_hat ε)
    (hGrowth : ∀ i j : Fin n,
      ∑ k : Fin n, |L_hat i k| * |U_hat k j| ≤ |A i j|) :
    ∃ DeltaA : Matrix (Fin n) (Fin n) ℝ,
      (∀ i j, |DeltaA i j| ≤ ε * |A i j|) ∧
      matMul n L_hat U_hat = fun i j => A i j + DeltaA i j := by
  obtain ⟨DeltaA, hDeltaA_bound, hDeltaA_eq⟩ :=
    higham9_12_spd_lu_backward_error n A L_hat U_hat ε hε hSPD hLU
      hGrowth
  refine ⟨DeltaA, hDeltaA_bound, ?_⟩
  ext i j
  simpa [matMul] using hDeltaA_eq i j

/-- **Theorem 9.12(a)**, native Matrix form of the SPD tridiagonal
backward-error handoff from a positive-`D L^T` certificate. -/
theorem higham9_12_matrix_spd_tridiag_lu_backward_error_of_positive_DLT
    (n : ℕ)
    (A L_hat U_hat : Matrix (Fin n) (Fin n) ℝ) (d : Fin n → ℝ)
    (ε : ℝ) (hε : 0 ≤ ε)
    (hSPD : IsSymPosDef n A)
    (hLU : LUBackwardError n A L_hat U_hat ε)
    (hStruct : IsTridiagLU n L_hat U_hat)
    (hLU_eq : matMul n L_hat U_hat = A)
    (hd_pos : ∀ k : Fin n, 0 < d k)
    (hDLT : ∀ k j : Fin n, U_hat k j = d k * L_hat j k) :
    ∃ DeltaA : Matrix (Fin n) (Fin n) ℝ,
      (∀ i j, |DeltaA i j| ≤ ε * |A i j|) ∧
      matMul n L_hat U_hat = fun i j => A i j + DeltaA i j := by
  obtain ⟨DeltaA, hDeltaA_bound, hDeltaA_eq⟩ :=
    higham9_12_spd_tridiag_lu_backward_error_of_positive_DLT n
      A L_hat U_hat d ε hε hSPD hLU hStruct
      (fun i j => by
        have hentry :=
          congrArg (fun M : Fin n → Fin n → ℝ => M i j) hLU_eq
        simpa [matMul] using hentry)
      hd_pos hDLT
  refine ⟨DeltaA, hDeltaA_bound, ?_⟩
  ext i j
  simpa [matMul] using hDeltaA_eq i j

/-- **Theorem 9.12(a)**, native Matrix form of the tridiagonal-builder SPD
backward-error handoff from a positive-`D L^T` certificate. -/
theorem higham9_12_matrix_spd_tridiag_builder_lu_backward_error_of_positive_DLT
    (n : ℕ)
    (T : higham9_18_TridiagData n) (l_hat u_hat d : Fin n → ℝ)
    (ε : ℝ) (hε : 0 ≤ ε)
    (hSPD : IsSymPosDef n (higham9_18_tridiag_to_matrix T))
    (hLU : LUBackwardError n (higham9_18_tridiag_to_matrix T)
      (tridiag_L_matrix l_hat) (tridiag_U_matrix u_hat T.c) ε)
    (hLU_exact :
      matMul n (tridiag_L_matrix l_hat)
          (tridiag_U_matrix u_hat T.c) =
        higham9_18_tridiag_to_matrix T)
    (hd_pos : ∀ k : Fin n, 0 < d k)
    (hDLT : ∀ k j : Fin n,
      tridiag_U_matrix u_hat T.c k j = d k * tridiag_L_matrix l_hat j k) :
    ∃ DeltaA : Matrix (Fin n) (Fin n) ℝ,
      (∀ i j, |DeltaA i j| ≤
        ε * |higham9_18_tridiag_to_matrix T i j|) ∧
      matMul n (tridiag_L_matrix l_hat)
          (tridiag_U_matrix u_hat T.c) =
        fun i j => higham9_18_tridiag_to_matrix T i j + DeltaA i j := by
  obtain ⟨DeltaA, hDeltaA_bound, hDeltaA_eq⟩ :=
    higham9_12_spd_tridiag_builder_lu_backward_error_of_positive_DLT n
      T l_hat u_hat d ε hε hSPD hLU
      (fun i j => by
        have hentry :=
          congrArg (fun M : Fin n → Fin n → ℝ => M i j) hLU_exact
        simpa [matMul] using hentry)
      hd_pos hDLT
  refine ⟨DeltaA, hDeltaA_bound, ?_⟩
  ext i j
  simpa [matMul] using hDeltaA_eq i j

/-- **Theorem 9.12(a)**, native Matrix form of the exact-recurrence
tridiagonal-builder SPD backward-error handoff. -/
theorem higham9_12_matrix_spd_tridiag_builder_lu_backward_error_of_recurrence
    (n : ℕ)
    (T : higham9_18_TridiagData n) (l_hat u_hat d : Fin n → ℝ)
    (ε : ℝ) (hε : 0 ≤ ε)
    (hSPD : IsSymPosDef n (higham9_18_tridiag_to_matrix T))
    (hLU : LUBackwardError n (higham9_18_tridiag_to_matrix T)
      (tridiag_L_matrix l_hat) (tridiag_U_matrix u_hat T.c) ε)
    (hrec : higham9_19_TridiagExactLURecurrence T l_hat u_hat)
    (hd_pos : ∀ k : Fin n, 0 < d k)
    (hDLT : ∀ k j : Fin n,
      tridiag_U_matrix u_hat T.c k j = d k * tridiag_L_matrix l_hat j k) :
    ∃ DeltaA : Matrix (Fin n) (Fin n) ℝ,
      (∀ i j, |DeltaA i j| ≤
        ε * |higham9_18_tridiag_to_matrix T i j|) ∧
      matMul n (tridiag_L_matrix l_hat)
          (tridiag_U_matrix u_hat T.c) =
        fun i j => higham9_18_tridiag_to_matrix T i j + DeltaA i j := by
  obtain ⟨DeltaA, hDeltaA_bound, hDeltaA_eq⟩ :=
    higham9_12_spd_tridiag_builder_lu_backward_error_of_recurrence n
      T l_hat u_hat d ε hε hSPD hLU hrec hd_pos hDLT
  refine ⟨DeltaA, hDeltaA_bound, ?_⟩
  ext i j
  simpa [matMul] using hDeltaA_eq i j

/-- **Theorem 9.13**, structural transpose adapter: tridiagonality is preserved
and reflected by the real matrix transpose.  This supplies the row/column
orientation bridge needed before the remaining row-dominant tridiagonal growth
proof. -/
theorem higham9_13_tridiagonal_transpose_iff {n : ℕ}
    (A : Fin n → Fin n → ℝ) :
    IsTridiagonal n (matTranspose A) ↔ IsTridiagonal n A := by
  constructor
  · intro h i j hij
    have hswap : j.val + 1 < i.val ∨ i.val + 1 < j.val := by
      rcases hij with hlt | hlt
      · exact Or.inr hlt
      · exact Or.inl hlt
    simpa [matTranspose] using h j i hswap
  · intro h i j hij
    have hswap : j.val + 1 < i.val ∨ i.val + 1 < j.val := by
      rcases hij with hlt | hlt
      · exact Or.inr hlt
      · exact Or.inl hlt
    simpa [matTranspose] using h j i hswap

/-- **Theorem 9.12 / Theorem 9.13 core**: for bidiagonal LU of a
column-diagonally-dominant tridiagonal matrix, `|L||U| ≤ 3|A|`. -/
theorem higham9_13_tridiag_growth_bound_3 {n : ℕ}
    (L U A : Fin n → Fin n → ℝ)
    (hStruct : IsTridiagLU n L U)
    (hLU_eq : ∀ i j : Fin n, ∑ k : Fin n, L i k * U k j = A i j)
    (hL_bound : ∀ i j : Fin n, |L i j| ≤ 1)
    (hA_tridiag : IsTridiagonal n A)
    (hColDom : IsDiagDominant n A) :
    ∀ i j : Fin n,
      ∑ k : Fin n, |L i k| * |U k j| ≤ 3 * |A i j| :=
  tridiag_growth_bound_3 L U A hStruct hLU_eq hL_bound hA_tridiag hColDom

/-- **Theorem 9.13**, max-entry growth consequence of the structural
tridiagonal bound.  The local componentwise theorem `|L||U| <= 3|A|`,
together with the unit lower diagonal in the tridiagonal LU structure, implies
Higham's max-entry growth factor satisfies `rho <= 3`. -/
theorem higham9_13_tridiag_growthFactorEntry_le_three {n : ℕ} (hn : 0 < n)
    (L U A : Fin n → Fin n → ℝ)
    (hStruct : IsTridiagLU n L U)
    (hLU_eq : ∀ i j : Fin n, ∑ k : Fin n, L i k * U k j = A i j)
    (hL_bound : ∀ i j : Fin n, |L i j| ≤ 1)
    (hA_tridiag : IsTridiagonal n A)
    (hColDom : IsDiagDominant n A)
    (hAmax : 0 < maxEntryNorm hn A) :
    growthFactorEntry hn A U hAmax ≤ 3 := by
  exact growthFactorEntry_le_of_absLU_componentwise hn A L U 3 (by norm_num)
    hAmax
    (fun i => by rw [hStruct.L_diag i, abs_one])
    (higham9_13_tridiag_growth_bound_3 L U A hStruct hLU_eq hL_bound
      hA_tridiag hColDom)

/-- **Theorem 9.13**, exact-LU structural handoff for column-dominant
tridiagonal matrices.  This removes the separate `IsTridiagLU` hypothesis
from the structural wrapper while keeping the source multiplier bound
`|L_ij| <= 1` visible. -/
theorem higham9_13_tridiag_growth_bound_3_of_LUFactSpec {n : ℕ}
    (A L U : Fin n → Fin n → ℝ)
    (hLU : LUFactSpec n A L U)
    (hdetA : Matrix.det (Matrix.of A : Matrix (Fin n) (Fin n) ℝ) ≠ 0)
    (hL_bound : ∀ i j : Fin n, |L i j| ≤ 1)
    (hA_tridiag : IsTridiagonal n A)
    (hColDom : IsDiagDominant n A) :
    ∀ i j : Fin n,
      ∑ k : Fin n, |L i k| * |U k j| ≤ 3 * |A i j| := by
  have hStruct : IsTridiagLU n L U :=
    hLU.isTridiagLU_of_tridiagonal hA_tridiag
      (hLU.det_ne_zero_iff_U_diag_ne_zero.mp hdetA)
  exact higham9_13_tridiag_growth_bound_3 L U A hStruct hLU.product_eq
    hL_bound hA_tridiag hColDom

/-- **Theorem 9.13**, max-entry growth consequence for an ordinary exact LU
factorization of a nonsingular column-diagonally-dominant tridiagonal matrix,
once the source multiplier bound `|L_ij| <= 1` is supplied. -/
theorem higham9_13_growthFactorEntry_le_three_of_LUFactSpec {n : ℕ}
    (hn : 0 < n) (A L U : Fin n → Fin n → ℝ)
    (hLU : LUFactSpec n A L U)
    (hdetA : Matrix.det (Matrix.of A : Matrix (Fin n) (Fin n) ℝ) ≠ 0)
    (hL_bound : ∀ i j : Fin n, |L i j| ≤ 1)
    (hA_tridiag : IsTridiagonal n A)
    (hColDom : IsDiagDominant n A)
    (hAmax : 0 < maxEntryNorm hn A) :
    growthFactorEntry hn A U hAmax ≤ 3 := by
  have hStruct : IsTridiagLU n L U :=
    hLU.isTridiagLU_of_tridiagonal hA_tridiag
      (hLU.det_ne_zero_iff_U_diag_ne_zero.mp hdetA)
  exact growthFactorEntry_le_of_absLU_componentwise hn A L U 3 (by norm_num)
    hAmax
    (fun i => by rw [hStruct.L_diag i, abs_one])
    (higham9_13_tridiag_growth_bound_3_of_LUFactSpec
      A L U hLU hdetA hL_bound hA_tridiag hColDom)

/-- **Theorem 9.13**, column-dominant multiplier bound for an ordinary exact
LU factorization of a nonsingular tridiagonal matrix.  This is the source
side condition `|l_ij| <= 1` derived from column diagonal dominance rather than
left as an extra hypothesis. -/
theorem higham9_13_colDiagDom_L_entries_bounded_of_LUFactSpec {n : ℕ}
    (A L U : Fin n → Fin n → ℝ)
    (hLU : LUFactSpec n A L U)
    (hdetA : Matrix.det (Matrix.of A : Matrix (Fin n) (Fin n) ℝ) ≠ 0)
    (hA_tridiag : IsTridiagonal n A)
    (hColDom : IsDiagDominant n A) :
    ∀ i j : Fin n, |L i j| ≤ 1 := by
  have hU_diag : ∀ i : Fin n, U i i ≠ 0 :=
    hLU.det_ne_zero_iff_U_diag_ne_zero.mp hdetA
  have hStruct : IsTridiagLU n L U :=
    hLU.isTridiagLU_of_tridiagonal hA_tridiag hU_diag
  exact tridiag_colDom_L_entries_bounded L U A hStruct hLU.product_eq
    hColDom hU_diag

/-- **Theorem 9.13**, exact-LU column-dominant tridiagonal componentwise
growth bound without a separate multiplier-bound hypothesis. -/
theorem higham9_13_colDiagDom_tridiag_growth_bound_3_of_LUFactSpec {n : ℕ}
    (A L U : Fin n → Fin n → ℝ)
    (hLU : LUFactSpec n A L U)
    (hdetA : Matrix.det (Matrix.of A : Matrix (Fin n) (Fin n) ℝ) ≠ 0)
    (hA_tridiag : IsTridiagonal n A)
    (hColDom : IsDiagDominant n A) :
    ∀ i j : Fin n,
      ∑ k : Fin n, |L i k| * |U k j| ≤ 3 * |A i j| :=
  higham9_13_tridiag_growth_bound_3_of_LUFactSpec A L U hLU hdetA
    (higham9_13_colDiagDom_L_entries_bounded_of_LUFactSpec
      A L U hLU hdetA hA_tridiag hColDom)
    hA_tridiag hColDom

/-- **Theorem 9.13**, exact-LU column-dominant tridiagonal max-entry growth
bound without a separate multiplier-bound hypothesis. -/
theorem higham9_13_colDiagDom_growthFactorEntry_le_three_of_LUFactSpec
    {n : ℕ} (hn : 0 < n) (A L U : Fin n → Fin n → ℝ)
    (hLU : LUFactSpec n A L U)
    (hdetA : Matrix.det (Matrix.of A : Matrix (Fin n) (Fin n) ℝ) ≠ 0)
    (hA_tridiag : IsTridiagonal n A)
    (hColDom : IsDiagDominant n A)
    (hAmax : 0 < maxEntryNorm hn A) :
    growthFactorEntry hn A U hAmax ≤ 3 :=
  higham9_13_growthFactorEntry_le_three_of_LUFactSpec hn A L U hLU hdetA
    (higham9_13_colDiagDom_L_entries_bounded_of_LUFactSpec
      A L U hLU hdetA hA_tridiag hColDom)
    hA_tridiag hColDom hAmax

/-- **Theorem 9.13**, row-dominant tridiagonal transpose specialization.

If `A` is row-diagonally dominant and tridiagonal, then `Aᵀ` is
column-diagonally dominant and tridiagonal. Hence any explicit bidiagonal LU
certificate for the transposed problem satisfies the same source `3|Aᵀ|`
componentwise growth bound. This is only the transpose structural bridge; it
does not construct the LU factors of `A` itself. -/
theorem higham9_13_rowDiagDom_transpose_tridiag_growth_bound_3 {n : ℕ}
    (L_T U_T A : Fin n → Fin n → ℝ)
    (hStructT : IsTridiagLU n L_T U_T)
    (hLU_eqT : ∀ i j : Fin n,
      ∑ k : Fin n, L_T i k * U_T k j = matTranspose A i j)
    (hL_boundT : ∀ i j : Fin n, |L_T i j| ≤ 1)
    (hA_tridiag : IsTridiagonal n A)
    (hRowDom : IsRowDiagDominant n A) :
    ∀ i j : Fin n,
      ∑ k : Fin n, |L_T i k| * |U_T k j| ≤
        3 * |matTranspose A i j| :=
  higham9_13_tridiag_growth_bound_3 L_T U_T (matTranspose A)
    hStructT hLU_eqT hL_boundT
    ((higham9_13_tridiagonal_transpose_iff A).2 hA_tridiag)
    ((higham9_9_colDiagDominant_transpose_iff_rowDiagDominant A).2 hRowDom)

/-- **Theorem 9.13**, row-dominant transpose max-entry growth consequence.

This is the max-entry growth-factor form of
`higham9_13_rowDiagDom_transpose_tridiag_growth_bound_3`: for the explicit LU
certificate of `Aᵀ`, the upper factor has `rho <= 3`. -/
theorem higham9_13_rowDiagDom_transpose_growthFactorEntry_le_three {n : ℕ}
    (hn : 0 < n)
    (L_T U_T A : Fin n → Fin n → ℝ)
    (hStructT : IsTridiagLU n L_T U_T)
    (hLU_eqT : ∀ i j : Fin n,
      ∑ k : Fin n, L_T i k * U_T k j = matTranspose A i j)
    (hL_boundT : ∀ i j : Fin n, |L_T i j| ≤ 1)
    (hA_tridiag : IsTridiagonal n A)
    (hRowDom : IsRowDiagDominant n A)
    (hAmaxT : 0 < maxEntryNorm hn (matTranspose A)) :
    growthFactorEntry hn (matTranspose A) U_T hAmaxT ≤ 3 := by
  exact higham9_13_tridiag_growthFactorEntry_le_three hn L_T U_T
    (matTranspose A) hStructT hLU_eqT hL_boundT
    ((higham9_13_tridiagonal_transpose_iff A).2 hA_tridiag)
    ((higham9_9_colDiagDominant_transpose_iff_rowDiagDominant A).2 hRowDom)
    hAmaxT

/-- **Theorem 9.13**, row-dominant transpose max-entry growth with the source
matrix denominator.

This variant records that `maxEntryNorm Aᵀ = maxEntryNorm A`, so the positivity
needed in the growth-factor denominator is the source matrix's max-entry
positivity, not a separate transposed-matrix assumption. -/
theorem higham9_13_rowDiagDom_transpose_growthFactorEntry_le_three_of_Amax
    {n : ℕ} (hn : 0 < n)
    (L_T U_T A : Fin n → Fin n → ℝ)
    (hStructT : IsTridiagLU n L_T U_T)
    (hLU_eqT : ∀ i j : Fin n,
      ∑ k : Fin n, L_T i k * U_T k j = matTranspose A i j)
    (hL_boundT : ∀ i j : Fin n, |L_T i j| ≤ 1)
    (hA_tridiag : IsTridiagonal n A)
    (hRowDom : IsRowDiagDominant n A)
    (hAmax : 0 < maxEntryNorm hn A) :
    growthFactorEntry hn (matTranspose A) U_T
      (by simpa [maxEntryNorm_matTranspose hn A] using hAmax) ≤ 3 := by
  exact higham9_13_rowDiagDom_transpose_growthFactorEntry_le_three hn
    L_T U_T A hStructT hLU_eqT hL_boundT hA_tridiag hRowDom
    (by simpa [maxEntryNorm_matTranspose hn A] using hAmax)

/-- **Theorem 9.13**, direct row-dominant tridiagonal growth bound.

This is the source proof orientation for row diagonal dominance: from an
explicit bidiagonal LU certificate of a row-diagonally-dominant tridiagonal
matrix, `|L||U| <= 3|A|` componentwise. -/
theorem higham9_13_rowDiagDom_tridiag_growth_bound_3 {n : ℕ}
    (L U A : Fin n → Fin n → ℝ)
    (hStruct : IsTridiagLU n L U)
    (hLU_eq : ∀ i j : Fin n, ∑ k : Fin n, L i k * U k j = A i j)
    (hA_tridiag : IsTridiagonal n A)
    (hRowDom : IsRowDiagDominant n A) :
    ∀ i j : Fin n,
      ∑ k : Fin n, |L i k| * |U k j| ≤ 3 * |A i j| :=
  tridiag_rowDom_growth_bound_3 L U A hStruct hLU_eq hA_tridiag hRowDom

/-- **Theorem 9.13**, max-entry growth consequence for the direct row-dominant
tridiagonal case. -/
theorem higham9_13_rowDiagDom_growthFactorEntry_le_three {n : ℕ} (hn : 0 < n)
    (L U A : Fin n → Fin n → ℝ)
    (hStruct : IsTridiagLU n L U)
    (hLU_eq : ∀ i j : Fin n, ∑ k : Fin n, L i k * U k j = A i j)
    (hA_tridiag : IsTridiagonal n A)
    (hRowDom : IsRowDiagDominant n A)
    (hAmax : 0 < maxEntryNorm hn A) :
    growthFactorEntry hn A U hAmax ≤ 3 := by
  exact growthFactorEntry_le_of_absLU_componentwise hn A L U 3 (by norm_num)
    hAmax
    (fun i => by rw [hStruct.L_diag i, abs_one])
    (higham9_13_rowDiagDom_tridiag_growth_bound_3 L U A hStruct hLU_eq
      hA_tridiag hRowDom)

/-- **Theorem 9.13**, exact-LU structural handoff for row-dominant
tridiagonal matrices.  A nonsingular tridiagonal matrix with an ordinary
exact LU certificate has the bidiagonal factor structure needed by Higham's
row-dominant proof, so the componentwise `|L||U| <= 3|A|` conclusion follows
without a separate `IsTridiagLU` assumption. -/
theorem higham9_13_rowDiagDom_tridiag_growth_bound_3_of_LUFactSpec {n : ℕ}
    (A L U : Fin n → Fin n → ℝ)
    (hLU : LUFactSpec n A L U)
    (hdetA : Matrix.det (Matrix.of A : Matrix (Fin n) (Fin n) ℝ) ≠ 0)
    (hA_tridiag : IsTridiagonal n A)
    (hRowDom : IsRowDiagDominant n A) :
    ∀ i j : Fin n,
      ∑ k : Fin n, |L i k| * |U k j| ≤ 3 * |A i j| := by
  have hStruct : IsTridiagLU n L U :=
    hLU.isTridiagLU_of_tridiagonal hA_tridiag
      (hLU.det_ne_zero_iff_U_diag_ne_zero.mp hdetA)
  exact higham9_13_rowDiagDom_tridiag_growth_bound_3 L U A hStruct
    hLU.product_eq hA_tridiag hRowDom

/-- **Theorem 9.13**, source-facing max-entry growth consequence for an
ordinary exact LU factorization of a nonsingular row-diagonally-dominant
tridiagonal matrix. -/
theorem higham9_13_rowDiagDom_growthFactorEntry_le_three_of_LUFactSpec
    {n : ℕ} (hn : 0 < n) (A L U : Fin n → Fin n → ℝ)
    (hLU : LUFactSpec n A L U)
    (hdetA : Matrix.det (Matrix.of A : Matrix (Fin n) (Fin n) ℝ) ≠ 0)
    (hA_tridiag : IsTridiagonal n A)
    (hRowDom : IsRowDiagDominant n A)
    (hAmax : 0 < maxEntryNorm hn A) :
    growthFactorEntry hn A U hAmax ≤ 3 := by
  have hStruct : IsTridiagLU n L U :=
    hLU.isTridiagLU_of_tridiagonal hA_tridiag
      (hLU.det_ne_zero_iff_U_diag_ne_zero.mp hdetA)
  exact growthFactorEntry_le_of_absLU_componentwise hn A L U 3 (by norm_num)
    hAmax
    (fun i => by rw [hStruct.L_diag i, abs_one])
    (higham9_13_rowDiagDom_tridiag_growth_bound_3_of_LUFactSpec
      A L U hLU hdetA hA_tridiag hRowDom)

/-- **Theorem 9.13**, source-data builder form for column-dominant
tridiagonal matrices.

The explicit `tridiag_L_matrix`/`tridiag_U_matrix` builders have the
bidiagonal shape required by the structural theorem.  This wrapper keeps the
exact-product certificate and multiplier bound explicit while removing the
separate `IsTridiagLU` hypothesis for matrices assembled from
`TridiagData`. -/
theorem higham9_13_tridiag_builder_growth_bound_3 {n : ℕ}
    (T : higham9_18_TridiagData n)
    (l_hat u_hat : Fin n → ℝ)
    (hLU_exact : ∀ i j : Fin n,
      ∑ k : Fin n, tridiag_L_matrix l_hat i k *
        tridiag_U_matrix u_hat T.c k j =
        higham9_18_tridiag_to_matrix T i j)
    (hl : ∀ i : Fin n, |l_hat i| ≤ 1)
    (hColDom : IsDiagDominant n (higham9_18_tridiag_to_matrix T)) :
    ∀ i j : Fin n,
      ∑ k : Fin n, |tridiag_L_matrix l_hat i k| *
        |tridiag_U_matrix u_hat T.c k j| ≤
        3 * |higham9_18_tridiag_to_matrix T i j| :=
  higham9_13_tridiag_growth_bound_3
    (tridiag_L_matrix l_hat) (tridiag_U_matrix u_hat T.c)
    (higham9_18_tridiag_to_matrix T)
    (tridiag_matrices_isTridiagLU l_hat u_hat T.c)
    hLU_exact
    (tridiag_L_matrix_entries_bounded l_hat hl)
    (higham9_18_tridiag_to_matrix_isTridiagonal T)
    hColDom

/-- **Theorem 9.13**, max-entry growth consequence for the source-data
tridiagonal builders in the column-dominant case. -/
theorem higham9_13_tridiag_builder_growthFactorEntry_le_three {n : ℕ}
    (hn : 0 < n)
    (T : higham9_18_TridiagData n)
    (l_hat u_hat : Fin n → ℝ)
    (hLU_exact : ∀ i j : Fin n,
      ∑ k : Fin n, tridiag_L_matrix l_hat i k *
        tridiag_U_matrix u_hat T.c k j =
        higham9_18_tridiag_to_matrix T i j)
    (hl : ∀ i : Fin n, |l_hat i| ≤ 1)
    (hColDom : IsDiagDominant n (higham9_18_tridiag_to_matrix T))
    (hAmax : 0 < maxEntryNorm hn (higham9_18_tridiag_to_matrix T)) :
    growthFactorEntry hn (higham9_18_tridiag_to_matrix T)
      (tridiag_U_matrix u_hat T.c) hAmax ≤ 3 :=
  higham9_13_tridiag_growthFactorEntry_le_three hn
    (tridiag_L_matrix l_hat) (tridiag_U_matrix u_hat T.c)
    (higham9_18_tridiag_to_matrix T)
    (tridiag_matrices_isTridiagLU l_hat u_hat T.c)
    hLU_exact
    (tridiag_L_matrix_entries_bounded l_hat hl)
    (higham9_18_tridiag_to_matrix_isTridiagonal T)
    hColDom hAmax

/-- **Theorem 9.13**, source-data column-dominant builder max-entry growth
with the positive source denominator derived from nonsingularity. -/
theorem higham9_13_tridiag_builder_growthFactorEntry_le_three_exists_hAmax
    {n : ℕ} (hn : 0 < n)
    (T : higham9_18_TridiagData n)
    (l_hat u_hat : Fin n → ℝ)
    (hLU_exact : ∀ i j : Fin n,
      ∑ k : Fin n, tridiag_L_matrix l_hat i k *
        tridiag_U_matrix u_hat T.c k j =
        higham9_18_tridiag_to_matrix T i j)
    (hl : ∀ i : Fin n, |l_hat i| ≤ 1)
    (hColDom : IsDiagDominant n (higham9_18_tridiag_to_matrix T))
    (hdetA :
      Matrix.det
        (Matrix.of (higham9_18_tridiag_to_matrix T) :
          Matrix (Fin n) (Fin n) ℝ) ≠ 0) :
    ∃ hAmax : 0 < maxEntryNorm hn (higham9_18_tridiag_to_matrix T),
      growthFactorEntry hn (higham9_18_tridiag_to_matrix T)
        (tridiag_U_matrix u_hat T.c) hAmax ≤ 3 := by
  have hAmax :
      0 < maxEntryNorm hn (higham9_18_tridiag_to_matrix T) :=
    maxEntryNorm_pos_of_det_ne_zero hn (higham9_18_tridiag_to_matrix T) hdetA
  exact
    ⟨hAmax,
      higham9_13_tridiag_builder_growthFactorEntry_le_three
        hn T l_hat u_hat hLU_exact hl hColDom hAmax⟩

/-- **Theorem 9.13**, source-data builder form for row-dominant tridiagonal
matrices.  The row-dominant structural theorem supplies the growth bound
without a separate multiplier-bound hypothesis. -/
theorem higham9_13_rowDiagDom_tridiag_builder_growth_bound_3 {n : ℕ}
    (T : higham9_18_TridiagData n)
    (l_hat u_hat : Fin n → ℝ)
    (hLU_exact : ∀ i j : Fin n,
      ∑ k : Fin n, tridiag_L_matrix l_hat i k *
        tridiag_U_matrix u_hat T.c k j =
        higham9_18_tridiag_to_matrix T i j)
    (hRowDom : IsRowDiagDominant n (higham9_18_tridiag_to_matrix T)) :
    ∀ i j : Fin n,
      ∑ k : Fin n, |tridiag_L_matrix l_hat i k| *
        |tridiag_U_matrix u_hat T.c k j| ≤
        3 * |higham9_18_tridiag_to_matrix T i j| :=
  higham9_13_rowDiagDom_tridiag_growth_bound_3
    (tridiag_L_matrix l_hat) (tridiag_U_matrix u_hat T.c)
    (higham9_18_tridiag_to_matrix T)
    (tridiag_matrices_isTridiagLU l_hat u_hat T.c)
    hLU_exact
    (higham9_18_tridiag_to_matrix_isTridiagonal T)
    hRowDom

/-- **Theorem 9.13**, max-entry growth consequence for the source-data
tridiagonal builders in the row-dominant case. -/
theorem higham9_13_rowDiagDom_tridiag_builder_growthFactorEntry_le_three
    {n : ℕ} (hn : 0 < n)
    (T : higham9_18_TridiagData n)
    (l_hat u_hat : Fin n → ℝ)
    (hLU_exact : ∀ i j : Fin n,
      ∑ k : Fin n, tridiag_L_matrix l_hat i k *
        tridiag_U_matrix u_hat T.c k j =
        higham9_18_tridiag_to_matrix T i j)
    (hRowDom : IsRowDiagDominant n (higham9_18_tridiag_to_matrix T))
    (hAmax : 0 < maxEntryNorm hn (higham9_18_tridiag_to_matrix T)) :
    growthFactorEntry hn (higham9_18_tridiag_to_matrix T)
      (tridiag_U_matrix u_hat T.c) hAmax ≤ 3 :=
  higham9_13_rowDiagDom_growthFactorEntry_le_three hn
    (tridiag_L_matrix l_hat) (tridiag_U_matrix u_hat T.c)
    (higham9_18_tridiag_to_matrix T)
    (tridiag_matrices_isTridiagLU l_hat u_hat T.c)
    hLU_exact
    (higham9_18_tridiag_to_matrix_isTridiagonal T)
    hRowDom hAmax

/-- **Theorem 9.13**, source-data row-dominant builder max-entry growth with
the positive source denominator derived from nonsingularity. -/
theorem higham9_13_rowDiagDom_tridiag_builder_growthFactorEntry_le_three_exists_hAmax
    {n : ℕ} (hn : 0 < n)
    (T : higham9_18_TridiagData n)
    (l_hat u_hat : Fin n → ℝ)
    (hLU_exact : ∀ i j : Fin n,
      ∑ k : Fin n, tridiag_L_matrix l_hat i k *
        tridiag_U_matrix u_hat T.c k j =
        higham9_18_tridiag_to_matrix T i j)
    (hRowDom : IsRowDiagDominant n (higham9_18_tridiag_to_matrix T))
    (hdetA :
      Matrix.det
        (Matrix.of (higham9_18_tridiag_to_matrix T) :
          Matrix (Fin n) (Fin n) ℝ) ≠ 0) :
    ∃ hAmax : 0 < maxEntryNorm hn (higham9_18_tridiag_to_matrix T),
      growthFactorEntry hn (higham9_18_tridiag_to_matrix T)
        (tridiag_U_matrix u_hat T.c) hAmax ≤ 3 := by
  have hAmax :
      0 < maxEntryNorm hn (higham9_18_tridiag_to_matrix T) :=
    maxEntryNorm_pos_of_det_ne_zero hn (higham9_18_tridiag_to_matrix T) hdetA
  exact
    ⟨hAmax,
      higham9_13_rowDiagDom_tridiag_builder_growthFactorEntry_le_three
        hn T l_hat u_hat hLU_exact hRowDom hAmax⟩

/-- **Theorem 9.13**, source-data column-dominant builder form from the exact
tridiagonal recurrence.

This discharges the exact-product certificate in
`higham9_13_tridiag_builder_growth_bound_3` from the displayed recurrence
(9.19). -/
theorem higham9_13_tridiag_builder_growth_bound_3_of_recurrence {n : ℕ}
    (T : higham9_18_TridiagData n)
    (l_hat u_hat : Fin n → ℝ)
    (hrec : higham9_19_TridiagExactLURecurrence T l_hat u_hat)
    (hl : ∀ i : Fin n, |l_hat i| ≤ 1)
    (hColDom : IsDiagDominant n (higham9_18_tridiag_to_matrix T)) :
    ∀ i j : Fin n,
      ∑ k : Fin n, |tridiag_L_matrix l_hat i k| *
        |tridiag_U_matrix u_hat T.c k j| ≤
        3 * |higham9_18_tridiag_to_matrix T i j| :=
  higham9_13_tridiag_builder_growth_bound_3 T l_hat u_hat
    (higham9_19_tridiag_exact_product_of_recurrence T l_hat u_hat hrec)
    hl hColDom

/-- **Theorem 9.13**, max-entry growth consequence for the source-data
column-dominant tridiagonal recurrence. -/
theorem higham9_13_tridiag_builder_growthFactorEntry_le_three_of_recurrence
    {n : ℕ} (hn : 0 < n)
    (T : higham9_18_TridiagData n)
    (l_hat u_hat : Fin n → ℝ)
    (hrec : higham9_19_TridiagExactLURecurrence T l_hat u_hat)
    (hl : ∀ i : Fin n, |l_hat i| ≤ 1)
    (hColDom : IsDiagDominant n (higham9_18_tridiag_to_matrix T))
    (hAmax : 0 < maxEntryNorm hn (higham9_18_tridiag_to_matrix T)) :
    growthFactorEntry hn (higham9_18_tridiag_to_matrix T)
      (tridiag_U_matrix u_hat T.c) hAmax ≤ 3 :=
  higham9_13_tridiag_builder_growthFactorEntry_le_three hn T l_hat u_hat
    (higham9_19_tridiag_exact_product_of_recurrence T l_hat u_hat hrec)
    hl hColDom hAmax

/-- **Theorem 9.13**, source-data column-dominant recurrence max-entry growth
with the positive source denominator derived from nonsingularity. -/
theorem higham9_13_tridiag_builder_growthFactorEntry_le_three_of_recurrence_exists_hAmax
    {n : ℕ} (hn : 0 < n)
    (T : higham9_18_TridiagData n)
    (l_hat u_hat : Fin n → ℝ)
    (hrec : higham9_19_TridiagExactLURecurrence T l_hat u_hat)
    (hl : ∀ i : Fin n, |l_hat i| ≤ 1)
    (hColDom : IsDiagDominant n (higham9_18_tridiag_to_matrix T))
    (hdetA :
      Matrix.det
        (Matrix.of (higham9_18_tridiag_to_matrix T) :
          Matrix (Fin n) (Fin n) ℝ) ≠ 0) :
    ∃ hAmax : 0 < maxEntryNorm hn (higham9_18_tridiag_to_matrix T),
      growthFactorEntry hn (higham9_18_tridiag_to_matrix T)
        (tridiag_U_matrix u_hat T.c) hAmax ≤ 3 := by
  exact
    higham9_13_tridiag_builder_growthFactorEntry_le_three_exists_hAmax
      hn T l_hat u_hat
      (higham9_19_tridiag_exact_product_of_recurrence T l_hat u_hat hrec)
      hl hColDom hdetA

/-- **Theorem 9.13**, source-data row-dominant builder form from the exact
tridiagonal recurrence. -/
theorem higham9_13_rowDiagDom_tridiag_builder_growth_bound_3_of_recurrence
    {n : ℕ}
    (T : higham9_18_TridiagData n)
    (l_hat u_hat : Fin n → ℝ)
    (hrec : higham9_19_TridiagExactLURecurrence T l_hat u_hat)
    (hRowDom : IsRowDiagDominant n (higham9_18_tridiag_to_matrix T)) :
    ∀ i j : Fin n,
      ∑ k : Fin n, |tridiag_L_matrix l_hat i k| *
        |tridiag_U_matrix u_hat T.c k j| ≤
        3 * |higham9_18_tridiag_to_matrix T i j| :=
  higham9_13_rowDiagDom_tridiag_builder_growth_bound_3 T l_hat u_hat
    (higham9_19_tridiag_exact_product_of_recurrence T l_hat u_hat hrec)
    hRowDom

/-- **Theorem 9.13**, max-entry growth consequence for the source-data
row-dominant tridiagonal recurrence. -/
theorem higham9_13_rowDiagDom_tridiag_builder_growthFactorEntry_le_three_of_recurrence
    {n : ℕ} (hn : 0 < n)
    (T : higham9_18_TridiagData n)
    (l_hat u_hat : Fin n → ℝ)
    (hrec : higham9_19_TridiagExactLURecurrence T l_hat u_hat)
    (hRowDom : IsRowDiagDominant n (higham9_18_tridiag_to_matrix T))
    (hAmax : 0 < maxEntryNorm hn (higham9_18_tridiag_to_matrix T)) :
    growthFactorEntry hn (higham9_18_tridiag_to_matrix T)
      (tridiag_U_matrix u_hat T.c) hAmax ≤ 3 :=
  higham9_13_rowDiagDom_tridiag_builder_growthFactorEntry_le_three hn
    T l_hat u_hat
    (higham9_19_tridiag_exact_product_of_recurrence T l_hat u_hat hrec)
    hRowDom hAmax

/-- **Theorem 9.13**, source-data row-dominant recurrence max-entry growth
with the positive source denominator derived from nonsingularity. -/
theorem higham9_13_rowDiagDom_tridiag_builder_growthFactorEntry_le_three_of_recurrence_exists_hAmax
    {n : ℕ} (hn : 0 < n)
    (T : higham9_18_TridiagData n)
    (l_hat u_hat : Fin n → ℝ)
    (hrec : higham9_19_TridiagExactLURecurrence T l_hat u_hat)
    (hRowDom : IsRowDiagDominant n (higham9_18_tridiag_to_matrix T))
    (hdetA :
      Matrix.det
        (Matrix.of (higham9_18_tridiag_to_matrix T) :
          Matrix (Fin n) (Fin n) ℝ) ≠ 0) :
    ∃ hAmax : 0 < maxEntryNorm hn (higham9_18_tridiag_to_matrix T),
      growthFactorEntry hn (higham9_18_tridiag_to_matrix T)
        (tridiag_U_matrix u_hat T.c) hAmax ≤ 3 := by
  exact
    higham9_13_rowDiagDom_tridiag_builder_growthFactorEntry_le_three_exists_hAmax
      hn T l_hat u_hat
      (higham9_19_tridiag_exact_product_of_recurrence T l_hat u_hat hrec)
      hRowDom hdetA

/-- **Theorem 9.14**, tridiagonal diagonally-dominant solve bound in the
absorbed `3γ_6` form. -/
theorem higham9_14_tridiag_diagDom_fu_bound_tight (n : ℕ)
    (A L_hat U_hat : Fin n → Fin n → ℝ)
    (y_hat x_hat : Fin n → ℝ)
    (b : Fin n → ℝ)
    (fp : FPModel) (h2 : gammaValid fp 2) (h6 : gammaValid fp 6)
    (ΔA_LU : Fin n → Fin n → ℝ)
    (hΔA_LU_bound : ∀ i j, |ΔA_LU i j| ≤
      gamma fp 2 * ∑ k : Fin n, |L_hat i k| * |U_hat k j|)
    (hΔA_LU_eq : ∀ i j,
      ∑ k : Fin n, L_hat i k * U_hat k j = A i j + ΔA_LU i j)
    (ΔL : Fin n → Fin n → ℝ)
    (hΔL_bound : ∀ i j, |ΔL i j| ≤ gamma fp 2 * |L_hat i j|)
    (hΔL_eq : ∀ i, ∑ j : Fin n, (L_hat i j + ΔL i j) * y_hat j = b i)
    (ΔU : Fin n → Fin n → ℝ)
    (hΔU_bound : ∀ i j, |ΔU i j| ≤ gamma fp 2 * |U_hat i j|)
    (hΔU_eq : ∀ i, ∑ j : Fin n, (U_hat i j + ΔU i j) * x_hat j = y_hat i)
    (hGrowth : ∀ i j : Fin n,
      ∑ k : Fin n, |L_hat i k| * |U_hat k j| ≤ 3 * |A i j|) :
    ∃ ΔA : Fin n → Fin n → ℝ,
      (∀ i j, |ΔA i j| ≤ 3 * gamma fp 6 * |A i j|) ∧
      (∀ i, ∑ j : Fin n, (A i j + ΔA i j) * x_hat j = b i) :=
  tridiag_diagDom_fu_bound_tight n A L_hat U_hat y_hat x_hat b fp h2 h6
    ΔA_LU hΔA_LU_bound hΔA_LU_eq
    ΔL hΔL_bound hΔL_eq
    ΔU hΔU_bound hΔU_eq
    hGrowth

/-- **Theorem 9.14**, structural tridiagonal diagonally-dominant specialization.

This packages the local Theorem 9.13 growth proof into the absorbed `3γ_6`
backward-error surface: when the computed factors have the bidiagonal
tridiagonal LU structure, multiply exactly to the source matrix, have
unit-bounded lower entries, and the source matrix is tridiagonal and
column-diagonally dominant, the growth hypothesis of
`higham9_14_tridiag_diagDom_fu_bound_tight` follows from
`higham9_13_tridiag_growth_bound_3`. -/
theorem higham9_14_tridiag_diagDom_fu_bound_from_structural_growth (n : ℕ)
    (A L_hat U_hat : Fin n → Fin n → ℝ)
    (y_hat x_hat : Fin n → ℝ)
    (b : Fin n → ℝ)
    (fp : FPModel) (h2 : gammaValid fp 2) (h6 : gammaValid fp 6)
    (hStruct : IsTridiagLU n L_hat U_hat)
    (hLU_exact : ∀ i j : Fin n,
      ∑ k : Fin n, L_hat i k * U_hat k j = A i j)
    (hL_bound : ∀ i j : Fin n, |L_hat i j| ≤ 1)
    (hA_tridiag : IsTridiagonal n A)
    (hColDom : IsDiagDominant n A)
    (ΔA_LU : Fin n → Fin n → ℝ)
    (hΔA_LU_bound : ∀ i j, |ΔA_LU i j| ≤
      gamma fp 2 * ∑ k : Fin n, |L_hat i k| * |U_hat k j|)
    (hΔA_LU_eq : ∀ i j,
      ∑ k : Fin n, L_hat i k * U_hat k j = A i j + ΔA_LU i j)
    (ΔL : Fin n → Fin n → ℝ)
    (hΔL_bound : ∀ i j, |ΔL i j| ≤ gamma fp 2 * |L_hat i j|)
    (hΔL_eq : ∀ i, ∑ j : Fin n, (L_hat i j + ΔL i j) * y_hat j = b i)
    (ΔU : Fin n → Fin n → ℝ)
    (hΔU_bound : ∀ i j, |ΔU i j| ≤ gamma fp 2 * |U_hat i j|)
    (hΔU_eq : ∀ i, ∑ j : Fin n, (U_hat i j + ΔU i j) * x_hat j = y_hat i) :
    ∃ ΔA : Fin n → Fin n → ℝ,
      (∀ i j, |ΔA i j| ≤ 3 * gamma fp 6 * |A i j|) ∧
      (∀ i, ∑ j : Fin n, (A i j + ΔA i j) * x_hat j = b i) :=
  higham9_14_tridiag_diagDom_fu_bound_tight n A L_hat U_hat y_hat x_hat b
    fp h2 h6 ΔA_LU hΔA_LU_bound hΔA_LU_eq
    ΔL hΔL_bound hΔL_eq ΔU hΔU_bound hΔU_eq
    (higham9_13_tridiag_growth_bound_3 L_hat U_hat A
      hStruct hLU_exact hL_bound hA_tridiag hColDom)

/-- **Theorem 9.14**, direct row-dominant structural tridiagonal
specialization.

This is the row-dominant analogue of
`higham9_14_tridiag_diagDom_fu_bound_from_structural_growth`; the growth
hypothesis is discharged by the direct row-dominant proof of Theorem 9.13, so
no separate multiplier-bound hypothesis is needed. -/
theorem higham9_14_tridiag_rowDiagDom_fu_bound_from_structural_growth (n : ℕ)
    (A L_hat U_hat : Fin n → Fin n → ℝ)
    (y_hat x_hat : Fin n → ℝ)
    (b : Fin n → ℝ)
    (fp : FPModel) (h2 : gammaValid fp 2) (h6 : gammaValid fp 6)
    (hStruct : IsTridiagLU n L_hat U_hat)
    (hLU_exact : ∀ i j : Fin n,
      ∑ k : Fin n, L_hat i k * U_hat k j = A i j)
    (hA_tridiag : IsTridiagonal n A)
    (hRowDom : IsRowDiagDominant n A)
    (ΔA_LU : Fin n → Fin n → ℝ)
    (hΔA_LU_bound : ∀ i j, |ΔA_LU i j| ≤
      gamma fp 2 * ∑ k : Fin n, |L_hat i k| * |U_hat k j|)
    (hΔA_LU_eq : ∀ i j,
      ∑ k : Fin n, L_hat i k * U_hat k j = A i j + ΔA_LU i j)
    (ΔL : Fin n → Fin n → ℝ)
    (hΔL_bound : ∀ i j, |ΔL i j| ≤ gamma fp 2 * |L_hat i j|)
    (hΔL_eq : ∀ i, ∑ j : Fin n, (L_hat i j + ΔL i j) * y_hat j = b i)
    (ΔU : Fin n → Fin n → ℝ)
    (hΔU_bound : ∀ i j, |ΔU i j| ≤ gamma fp 2 * |U_hat i j|)
    (hΔU_eq : ∀ i, ∑ j : Fin n, (U_hat i j + ΔU i j) * x_hat j = y_hat i) :
    ∃ ΔA : Fin n → Fin n → ℝ,
      (∀ i j, |ΔA i j| ≤ 3 * gamma fp 6 * |A i j|) ∧
      (∀ i, ∑ j : Fin n, (A i j + ΔA i j) * x_hat j = b i) :=
  higham9_14_tridiag_diagDom_fu_bound_tight n A L_hat U_hat y_hat x_hat b
    fp h2 h6 ΔA_LU hΔA_LU_bound hΔA_LU_eq
    ΔL hΔL_bound hΔL_eq ΔU hΔU_bound hΔU_eq
    (higham9_13_rowDiagDom_tridiag_growth_bound_3 L_hat U_hat A
      hStruct hLU_exact hA_tridiag hRowDom)

/-- **Theorem 9.14**, source-data builder specialization for column-dominant
tridiagonal matrices.

This instantiates the structural `3γ_6` backward-error wrapper with the
explicit tridiagonal matrix builders.  The exact-product and perturbation
certificates remain explicit hypotheses. -/
theorem higham9_14_tridiag_colDiagDom_fu_bound_from_builders (n : ℕ)
    (T : higham9_18_TridiagData n)
    (l_hat u_hat : Fin n → ℝ)
    (y_hat x_hat : Fin n → ℝ)
    (b : Fin n → ℝ)
    (fp : FPModel) (h2 : gammaValid fp 2) (h6 : gammaValid fp 6)
    (hLU_exact : ∀ i j : Fin n,
      ∑ k : Fin n, tridiag_L_matrix l_hat i k *
        tridiag_U_matrix u_hat T.c k j =
        higham9_18_tridiag_to_matrix T i j)
    (hl : ∀ i : Fin n, |l_hat i| ≤ 1)
    (hColDom : IsDiagDominant n (higham9_18_tridiag_to_matrix T))
    (ΔA_LU : Fin n → Fin n → ℝ)
    (hΔA_LU_bound : ∀ i j, |ΔA_LU i j| ≤
      gamma fp 2 * ∑ k : Fin n, |tridiag_L_matrix l_hat i k| *
        |tridiag_U_matrix u_hat T.c k j|)
    (hΔA_LU_eq : ∀ i j,
      ∑ k : Fin n, tridiag_L_matrix l_hat i k *
        tridiag_U_matrix u_hat T.c k j =
        higham9_18_tridiag_to_matrix T i j + ΔA_LU i j)
    (ΔL : Fin n → Fin n → ℝ)
    (hΔL_bound : ∀ i j,
      |ΔL i j| ≤ gamma fp 2 * |tridiag_L_matrix l_hat i j|)
    (hΔL_eq : ∀ i,
      ∑ j : Fin n, (tridiag_L_matrix l_hat i j + ΔL i j) * y_hat j = b i)
    (ΔU : Fin n → Fin n → ℝ)
    (hΔU_bound : ∀ i j,
      |ΔU i j| ≤ gamma fp 2 * |tridiag_U_matrix u_hat T.c i j|)
    (hΔU_eq : ∀ i,
      ∑ j : Fin n, (tridiag_U_matrix u_hat T.c i j + ΔU i j) * x_hat j =
        y_hat i) :
    ∃ ΔA : Fin n → Fin n → ℝ,
      (∀ i j, |ΔA i j| ≤
        3 * gamma fp 6 * |higham9_18_tridiag_to_matrix T i j|) ∧
      (∀ i, ∑ j : Fin n,
        (higham9_18_tridiag_to_matrix T i j + ΔA i j) * x_hat j = b i) :=
  higham9_14_tridiag_diagDom_fu_bound_from_structural_growth n
    (higham9_18_tridiag_to_matrix T)
    (tridiag_L_matrix l_hat) (tridiag_U_matrix u_hat T.c)
    y_hat x_hat b fp h2 h6
    (tridiag_matrices_isTridiagLU l_hat u_hat T.c)
    hLU_exact
    (tridiag_L_matrix_entries_bounded l_hat hl)
    (higham9_18_tridiag_to_matrix_isTridiagonal T)
    hColDom
    ΔA_LU hΔA_LU_bound hΔA_LU_eq
    ΔL hΔL_bound hΔL_eq
    ΔU hΔU_bound hΔU_eq

/-- **Theorem 9.14**, source-data builder specialization for row-dominant
tridiagonal matrices. -/
theorem higham9_14_tridiag_rowDiagDom_fu_bound_from_builders (n : ℕ)
    (T : higham9_18_TridiagData n)
    (l_hat u_hat : Fin n → ℝ)
    (y_hat x_hat : Fin n → ℝ)
    (b : Fin n → ℝ)
    (fp : FPModel) (h2 : gammaValid fp 2) (h6 : gammaValid fp 6)
    (hLU_exact : ∀ i j : Fin n,
      ∑ k : Fin n, tridiag_L_matrix l_hat i k *
        tridiag_U_matrix u_hat T.c k j =
        higham9_18_tridiag_to_matrix T i j)
    (hRowDom : IsRowDiagDominant n (higham9_18_tridiag_to_matrix T))
    (ΔA_LU : Fin n → Fin n → ℝ)
    (hΔA_LU_bound : ∀ i j, |ΔA_LU i j| ≤
      gamma fp 2 * ∑ k : Fin n, |tridiag_L_matrix l_hat i k| *
        |tridiag_U_matrix u_hat T.c k j|)
    (hΔA_LU_eq : ∀ i j,
      ∑ k : Fin n, tridiag_L_matrix l_hat i k *
        tridiag_U_matrix u_hat T.c k j =
        higham9_18_tridiag_to_matrix T i j + ΔA_LU i j)
    (ΔL : Fin n → Fin n → ℝ)
    (hΔL_bound : ∀ i j,
      |ΔL i j| ≤ gamma fp 2 * |tridiag_L_matrix l_hat i j|)
    (hΔL_eq : ∀ i,
      ∑ j : Fin n, (tridiag_L_matrix l_hat i j + ΔL i j) * y_hat j = b i)
    (ΔU : Fin n → Fin n → ℝ)
    (hΔU_bound : ∀ i j,
      |ΔU i j| ≤ gamma fp 2 * |tridiag_U_matrix u_hat T.c i j|)
    (hΔU_eq : ∀ i,
      ∑ j : Fin n, (tridiag_U_matrix u_hat T.c i j + ΔU i j) * x_hat j =
        y_hat i) :
    ∃ ΔA : Fin n → Fin n → ℝ,
      (∀ i j, |ΔA i j| ≤
        3 * gamma fp 6 * |higham9_18_tridiag_to_matrix T i j|) ∧
      (∀ i, ∑ j : Fin n,
        (higham9_18_tridiag_to_matrix T i j + ΔA i j) * x_hat j = b i) :=
  higham9_14_tridiag_rowDiagDom_fu_bound_from_structural_growth n
    (higham9_18_tridiag_to_matrix T)
    (tridiag_L_matrix l_hat) (tridiag_U_matrix u_hat T.c)
    y_hat x_hat b fp h2 h6
    (tridiag_matrices_isTridiagLU l_hat u_hat T.c)
    hLU_exact
    (higham9_18_tridiag_to_matrix_isTridiagonal T)
    hRowDom
    ΔA_LU hΔA_LU_bound hΔA_LU_eq
    ΔL hΔL_bound hΔL_eq
    ΔU hΔU_bound hΔU_eq

/-- **Theorem 9.14**, column-dominant builder specialization from the exact
tridiagonal recurrence.

This is an exact-recurrence specialization of the existing builder wrapper:
the product certificate is proved from equation (9.19), while the separate
floating-point perturbation certificates remain explicit. -/
theorem higham9_14_tridiag_colDiagDom_fu_bound_from_recurrence (n : ℕ)
    (T : higham9_18_TridiagData n)
    (l_hat u_hat : Fin n → ℝ)
    (y_hat x_hat : Fin n → ℝ)
    (b : Fin n → ℝ)
    (fp : FPModel) (h2 : gammaValid fp 2) (h6 : gammaValid fp 6)
    (hrec : higham9_19_TridiagExactLURecurrence T l_hat u_hat)
    (hl : ∀ i : Fin n, |l_hat i| ≤ 1)
    (hColDom : IsDiagDominant n (higham9_18_tridiag_to_matrix T))
    (ΔA_LU : Fin n → Fin n → ℝ)
    (hΔA_LU_bound : ∀ i j, |ΔA_LU i j| ≤
      gamma fp 2 * ∑ k : Fin n, |tridiag_L_matrix l_hat i k| *
        |tridiag_U_matrix u_hat T.c k j|)
    (hΔA_LU_eq : ∀ i j,
      ∑ k : Fin n, tridiag_L_matrix l_hat i k *
        tridiag_U_matrix u_hat T.c k j =
        higham9_18_tridiag_to_matrix T i j + ΔA_LU i j)
    (ΔL : Fin n → Fin n → ℝ)
    (hΔL_bound : ∀ i j,
      |ΔL i j| ≤ gamma fp 2 * |tridiag_L_matrix l_hat i j|)
    (hΔL_eq : ∀ i,
      ∑ j : Fin n, (tridiag_L_matrix l_hat i j + ΔL i j) * y_hat j = b i)
    (ΔU : Fin n → Fin n → ℝ)
    (hΔU_bound : ∀ i j,
      |ΔU i j| ≤ gamma fp 2 * |tridiag_U_matrix u_hat T.c i j|)
    (hΔU_eq : ∀ i,
      ∑ j : Fin n, (tridiag_U_matrix u_hat T.c i j + ΔU i j) * x_hat j =
        y_hat i) :
    ∃ ΔA : Fin n → Fin n → ℝ,
      (∀ i j, |ΔA i j| ≤
        3 * gamma fp 6 * |higham9_18_tridiag_to_matrix T i j|) ∧
      (∀ i, ∑ j : Fin n,
        (higham9_18_tridiag_to_matrix T i j + ΔA i j) * x_hat j = b i) :=
  higham9_14_tridiag_colDiagDom_fu_bound_from_builders n T l_hat u_hat
    y_hat x_hat b fp h2 h6
    (higham9_19_tridiag_exact_product_of_recurrence T l_hat u_hat hrec)
    hl hColDom
    ΔA_LU hΔA_LU_bound hΔA_LU_eq
    ΔL hΔL_bound hΔL_eq
    ΔU hΔU_bound hΔU_eq

/-- **Theorem 9.14**, row-dominant builder specialization from the exact
tridiagonal recurrence. -/
theorem higham9_14_tridiag_rowDiagDom_fu_bound_from_recurrence (n : ℕ)
    (T : higham9_18_TridiagData n)
    (l_hat u_hat : Fin n → ℝ)
    (y_hat x_hat : Fin n → ℝ)
    (b : Fin n → ℝ)
    (fp : FPModel) (h2 : gammaValid fp 2) (h6 : gammaValid fp 6)
    (hrec : higham9_19_TridiagExactLURecurrence T l_hat u_hat)
    (hRowDom : IsRowDiagDominant n (higham9_18_tridiag_to_matrix T))
    (ΔA_LU : Fin n → Fin n → ℝ)
    (hΔA_LU_bound : ∀ i j, |ΔA_LU i j| ≤
      gamma fp 2 * ∑ k : Fin n, |tridiag_L_matrix l_hat i k| *
        |tridiag_U_matrix u_hat T.c k j|)
    (hΔA_LU_eq : ∀ i j,
      ∑ k : Fin n, tridiag_L_matrix l_hat i k *
        tridiag_U_matrix u_hat T.c k j =
        higham9_18_tridiag_to_matrix T i j + ΔA_LU i j)
    (ΔL : Fin n → Fin n → ℝ)
    (hΔL_bound : ∀ i j,
      |ΔL i j| ≤ gamma fp 2 * |tridiag_L_matrix l_hat i j|)
    (hΔL_eq : ∀ i,
      ∑ j : Fin n, (tridiag_L_matrix l_hat i j + ΔL i j) * y_hat j = b i)
    (ΔU : Fin n → Fin n → ℝ)
    (hΔU_bound : ∀ i j,
      |ΔU i j| ≤ gamma fp 2 * |tridiag_U_matrix u_hat T.c i j|)
    (hΔU_eq : ∀ i,
      ∑ j : Fin n, (tridiag_U_matrix u_hat T.c i j + ΔU i j) * x_hat j =
        y_hat i) :
    ∃ ΔA : Fin n → Fin n → ℝ,
      (∀ i j, |ΔA i j| ≤
        3 * gamma fp 6 * |higham9_18_tridiag_to_matrix T i j|) ∧
      (∀ i, ∑ j : Fin n,
        (higham9_18_tridiag_to_matrix T i j + ΔA i j) * x_hat j = b i) :=
  higham9_14_tridiag_rowDiagDom_fu_bound_from_builders n T l_hat u_hat
    y_hat x_hat b fp h2 h6
    (higham9_19_tridiag_exact_product_of_recurrence T l_hat u_hat hrec)
    hRowDom
    ΔA_LU hΔA_LU_bound hΔA_LU_eq
    ΔL hΔL_bound hΔL_eq
    ΔU hΔU_bound hΔU_eq

/-- **Theorem 9.14**, column-dominant exact-LU tridiagonal specialization.

This is the ordinary exact-LU version of
`higham9_14_tridiag_diagDom_fu_bound_from_structural_growth`: the growth
hypothesis is discharged from `LUFactSpec`, tridiagonality, nonsingularity, and
column diagonal dominance, with the multiplier bound proved locally by
Theorem 9.13. -/
theorem higham9_14_tridiag_colDiagDom_fu_bound_from_LUFactSpec (n : ℕ)
    (A L_hat U_hat : Fin n → Fin n → ℝ)
    (y_hat x_hat : Fin n → ℝ)
    (b : Fin n → ℝ)
    (fp : FPModel) (h2 : gammaValid fp 2) (h6 : gammaValid fp 6)
    (hLU : LUFactSpec n A L_hat U_hat)
    (hdetA : Matrix.det (Matrix.of A : Matrix (Fin n) (Fin n) ℝ) ≠ 0)
    (hA_tridiag : IsTridiagonal n A)
    (hColDom : IsDiagDominant n A)
    (ΔA_LU : Fin n → Fin n → ℝ)
    (hΔA_LU_bound : ∀ i j, |ΔA_LU i j| ≤
      gamma fp 2 * ∑ k : Fin n, |L_hat i k| * |U_hat k j|)
    (hΔA_LU_eq : ∀ i j,
      ∑ k : Fin n, L_hat i k * U_hat k j = A i j + ΔA_LU i j)
    (ΔL : Fin n → Fin n → ℝ)
    (hΔL_bound : ∀ i j, |ΔL i j| ≤ gamma fp 2 * |L_hat i j|)
    (hΔL_eq : ∀ i, ∑ j : Fin n, (L_hat i j + ΔL i j) * y_hat j = b i)
    (ΔU : Fin n → Fin n → ℝ)
    (hΔU_bound : ∀ i j, |ΔU i j| ≤ gamma fp 2 * |U_hat i j|)
    (hΔU_eq : ∀ i, ∑ j : Fin n, (U_hat i j + ΔU i j) * x_hat j = y_hat i) :
    ∃ ΔA : Fin n → Fin n → ℝ,
      (∀ i j, |ΔA i j| ≤ 3 * gamma fp 6 * |A i j|) ∧
      (∀ i, ∑ j : Fin n, (A i j + ΔA i j) * x_hat j = b i) :=
  higham9_14_tridiag_diagDom_fu_bound_tight n A L_hat U_hat y_hat x_hat b
    fp h2 h6 ΔA_LU hΔA_LU_bound hΔA_LU_eq
    ΔL hΔL_bound hΔL_eq ΔU hΔU_bound hΔU_eq
    (higham9_13_colDiagDom_tridiag_growth_bound_3_of_LUFactSpec
      A L_hat U_hat hLU hdetA hA_tridiag hColDom)

/-- **Theorem 9.14**, row-dominant exact-LU tridiagonal specialization.

This packages the direct row-dominant Theorem 9.13 exact-LU growth wrapper into
the absorbed `3γ_6` backward-error surface. -/
theorem higham9_14_tridiag_rowDiagDom_fu_bound_from_LUFactSpec (n : ℕ)
    (A L_hat U_hat : Fin n → Fin n → ℝ)
    (y_hat x_hat : Fin n → ℝ)
    (b : Fin n → ℝ)
    (fp : FPModel) (h2 : gammaValid fp 2) (h6 : gammaValid fp 6)
    (hLU : LUFactSpec n A L_hat U_hat)
    (hdetA : Matrix.det (Matrix.of A : Matrix (Fin n) (Fin n) ℝ) ≠ 0)
    (hA_tridiag : IsTridiagonal n A)
    (hRowDom : IsRowDiagDominant n A)
    (ΔA_LU : Fin n → Fin n → ℝ)
    (hΔA_LU_bound : ∀ i j, |ΔA_LU i j| ≤
      gamma fp 2 * ∑ k : Fin n, |L_hat i k| * |U_hat k j|)
    (hΔA_LU_eq : ∀ i j,
      ∑ k : Fin n, L_hat i k * U_hat k j = A i j + ΔA_LU i j)
    (ΔL : Fin n → Fin n → ℝ)
    (hΔL_bound : ∀ i j, |ΔL i j| ≤ gamma fp 2 * |L_hat i j|)
    (hΔL_eq : ∀ i, ∑ j : Fin n, (L_hat i j + ΔL i j) * y_hat j = b i)
    (ΔU : Fin n → Fin n → ℝ)
    (hΔU_bound : ∀ i j, |ΔU i j| ≤ gamma fp 2 * |U_hat i j|)
    (hΔU_eq : ∀ i, ∑ j : Fin n, (U_hat i j + ΔU i j) * x_hat j = y_hat i) :
    ∃ ΔA : Fin n → Fin n → ℝ,
      (∀ i j, |ΔA i j| ≤ 3 * gamma fp 6 * |A i j|) ∧
      (∀ i, ∑ j : Fin n, (A i j + ΔA i j) * x_hat j = b i) :=
  higham9_14_tridiag_diagDom_fu_bound_tight n A L_hat U_hat y_hat x_hat b
    fp h2 h6 ΔA_LU hΔA_LU_bound hΔA_LU_eq
    ΔL hΔL_bound hΔL_eq ΔU hΔU_bound hΔU_eq
    (higham9_13_rowDiagDom_tridiag_growth_bound_3_of_LUFactSpec
      A L_hat U_hat hLU hdetA hA_tridiag hRowDom)

/-- **Equation (9.22)**, source scalar `f(u) = 4u + 3u² + u³`. -/
noncomputable def higham9_14_f (u : ℝ) : ℝ :=
  4 * u + 3 * u ^ 2 + u ^ 3

/-- **Theorem 9.14**, source scalar `h(u) = f(u)/(1-u)`. -/
noncomputable def higham9_14_h (u : ℝ) : ℝ :=
  higham9_14_f u / (1 - u)

/-- **Theorem 9.14**, source relation between the printed scalars:
`h(u) = f(u)/(1-u)`. -/
theorem higham9_14_h_eq_f_div (u : ℝ) :
    higham9_14_h u = higham9_14_f u / (1 - u) := by
  rfl

/-- **Theorem 9.14**, nonnegativity of the printed source polynomial
`f(u) = 4u + 3u² + u³` under the standard `0 <= u` side condition. -/
theorem higham9_14_f_nonneg {u : ℝ} (hu : 0 ≤ u) :
    0 ≤ higham9_14_f u := by
  unfold higham9_14_f
  have hu2 : 0 ≤ u ^ 2 := pow_nonneg hu 2
  have hu3 : 0 ≤ u ^ 3 := pow_nonneg hu 3
  nlinarith

/-- **Equation (9.22)**, monotonicity of the source scalar
`f(u)=4u+3u²+u³` on the nonnegative real line. -/
theorem higham9_14_f_mono_nonneg {u v : ℝ} (hu : 0 ≤ u) (huv : u ≤ v) :
    higham9_14_f u ≤ higham9_14_f v := by
  unfold higham9_14_f
  have hv : 0 ≤ v := hu.trans huv
  have hsq : u ^ 2 ≤ v ^ 2 := by
    nlinarith [mul_nonneg (sub_nonneg.mpr huv) (add_nonneg hv hu)]
  have hcube : u ^ 3 ≤ v ^ 3 := by
    have htail : 0 ≤ v ^ 2 + v * u + u ^ 2 := by
      nlinarith [sq_nonneg v, mul_nonneg hv hu, sq_nonneg u]
    nlinarith [mul_nonneg (sub_nonneg.mpr huv) htail]
  nlinarith

/-- **Theorem 9.14**, denominator-cleared form of the source relation between
`f(u)` and `h(u)`. -/
theorem higham9_14_h_mul_one_sub_eq_f {u : ℝ} (hden : 1 - u ≠ 0) :
    higham9_14_h u * (1 - u) = higham9_14_f u := by
  unfold higham9_14_h higham9_14_f
  field_simp [hden]

/-- **Theorem 9.14**, scalar monotonicity from the equation-(9.22)
coefficient to the final source coefficient.

For the standard small-unit-roundoff range `0 <= u < 1`, the final coefficient
`h(u) = f(u)/(1-u)` dominates the equation-(9.22) coefficient `f(u)`. -/
theorem higham9_14_f_le_h {u : ℝ} (hu : 0 ≤ u) (hu_lt_one : u < 1) :
    higham9_14_f u ≤ higham9_14_h u := by
  rw [higham9_14_h_eq_f_div]
  have hden_pos : 0 < 1 - u := by linarith
  rw [le_div_iff₀ hden_pos]
  have hf_nonneg : 0 ≤ higham9_14_f u := higham9_14_f_nonneg hu
  have hden_le_one : 1 - u ≤ 1 := by linarith
  calc
    higham9_14_f u * (1 - u)
        ≤ higham9_14_f u * 1 :=
          mul_le_mul_of_nonneg_left hden_le_one hf_nonneg
    _ = higham9_14_f u := by ring

/-- **Equation (9.20)**, source perturbation model for computed tridiagonal LU.

The supplied perturbation `DeltaA_LU` witnesses the matrix-form statement
`L_hat * U_hat = A + DeltaA_LU` with the printed componentwise coefficient
`u * |L_hat||U_hat|`.  This is a model predicate for the equation, not a proof
that a particular rounded recurrence produces the perturbation. -/
def higham9_20_tridiag_lu_perturbation_model (n : ℕ)
    (A L_hat U_hat DeltaA_LU : Fin n → Fin n → ℝ) (u : ℝ) : Prop :=
  (∀ i j : Fin n,
    ∑ k : Fin n, L_hat i k * U_hat k j = A i j + DeltaA_LU i j) ∧
  ∀ i j : Fin n,
    |DeltaA_LU i j| ≤
      u * ∑ k : Fin n, |L_hat i k| * |U_hat k j|

/-- **Equation (9.21)**, source perturbation model for the triangular solves.

The supplied perturbations `DeltaL` and `DeltaU` witness the forward- and
back-substitution equations and the printed componentwise coefficients
`u` and `2u + u^2`. -/
def higham9_21_tridiag_solve_perturbation_model (n : ℕ)
    (L_hat U_hat : Fin n → Fin n → ℝ)
    (y_hat x_hat b : Fin n → ℝ)
    (DeltaL DeltaU : Fin n → Fin n → ℝ) (u : ℝ) : Prop :=
  (∀ i : Fin n,
    ∑ j : Fin n, (L_hat i j + DeltaL i j) * y_hat j = b i) ∧
  (∀ i j : Fin n, |DeltaL i j| ≤ u * |L_hat i j|) ∧
  (∀ i : Fin n,
    ∑ j : Fin n, (U_hat i j + DeltaU i j) * x_hat j = y_hat i) ∧
  ∀ i j : Fin n, |DeltaU i j| ≤ (2 * u + u ^ 2) * |U_hat i j|

/-- **Equation (9.20)**, native `Matrix` product form of the tridiagonal LU
perturbation model. -/
theorem higham9_20_tridiag_lu_perturbation_model_iff_matrix_mul (n : ℕ)
    (A L_hat U_hat DeltaA_LU : Matrix (Fin n) (Fin n) ℝ) (u : ℝ) :
    higham9_20_tridiag_lu_perturbation_model n A L_hat U_hat
        DeltaA_LU u ↔
      (L_hat * U_hat = fun i j => A i j + DeltaA_LU i j) ∧
        ∀ i j : Fin n,
          |DeltaA_LU i j| ≤
            u * ∑ k : Fin n, |L_hat i k| * |U_hat k j| := by
  constructor
  · intro h20
    refine ⟨?_, h20.2⟩
    ext i j
    simpa [Matrix.mul_apply, dotProduct] using h20.1 i j
  · intro h20
    refine ⟨?_, h20.2⟩
    intro i j
    have hentry := congrFun (congrFun h20.1 i) j
    simpa [Matrix.mul_apply, dotProduct] using hentry

/-- **Equation (9.21)**, native `Matrix.mulVec` form of the triangular-solve
perturbation model. -/
theorem higham9_21_tridiag_solve_perturbation_model_iff_matrix_mulVec (n : ℕ)
    (L_hat U_hat : Matrix (Fin n) (Fin n) ℝ)
    (y_hat x_hat b : Fin n → ℝ)
    (DeltaL DeltaU : Matrix (Fin n) (Fin n) ℝ) (u : ℝ) :
    higham9_21_tridiag_solve_perturbation_model n L_hat U_hat
        y_hat x_hat b DeltaL DeltaU u ↔
      Matrix.mulVec (fun i j => L_hat i j + DeltaL i j) y_hat = b ∧
        (∀ i j : Fin n, |DeltaL i j| ≤ u * |L_hat i j|) ∧
        Matrix.mulVec (fun i j => U_hat i j + DeltaU i j) x_hat = y_hat ∧
        ∀ i j : Fin n,
          |DeltaU i j| ≤ (2 * u + u ^ 2) * |U_hat i j| := by
  constructor
  · intro h21
    rcases h21 with ⟨hforward, hDeltaL, hback, hDeltaU⟩
    refine ⟨?_, hDeltaL, ?_, hDeltaU⟩
    · funext i
      simpa [Matrix.mulVec, dotProduct] using hforward i
    · funext i
      simpa [Matrix.mulVec, dotProduct] using hback i
  · intro h21
    rcases h21 with ⟨hforward, hDeltaL, hback, hDeltaU⟩
    refine ⟨?_, hDeltaL, ?_, hDeltaU⟩
    · intro i
      simpa [Matrix.mulVec, dotProduct] using congrFun hforward i
    · intro i
      simpa [Matrix.mulVec, dotProduct] using congrFun hback i

/-- **Equation (9.20)**, coefficient monotonicity for supplied LU
perturbation models. -/
theorem higham9_20_tridiag_lu_perturbation_model_mono
    (n : ℕ) (A L_hat U_hat DeltaA_LU : Fin n → Fin n → ℝ)
    {u v : ℝ} (huv : u ≤ v)
    (h20 : higham9_20_tridiag_lu_perturbation_model n A L_hat U_hat
      DeltaA_LU u) :
    higham9_20_tridiag_lu_perturbation_model n A L_hat U_hat
      DeltaA_LU v := by
  refine ⟨h20.1, ?_⟩
  intro i j
  have hsum_nonneg :
      0 ≤ ∑ k : Fin n, |L_hat i k| * |U_hat k j| :=
    Finset.sum_nonneg fun k _ => mul_nonneg (abs_nonneg _) (abs_nonneg _)
  exact le_trans (h20.2 i j)
    (mul_le_mul_of_nonneg_right huv hsum_nonneg)

/-- **Equation (9.21)**, coefficient monotonicity for supplied triangular-solve
perturbation models. -/
theorem higham9_21_tridiag_solve_perturbation_model_mono
    (n : ℕ) (L_hat U_hat : Fin n → Fin n → ℝ)
    (y_hat x_hat b : Fin n → ℝ)
    (DeltaL DeltaU : Fin n → Fin n → ℝ)
    {u v : ℝ} (hu : 0 ≤ u) (huv : u ≤ v)
    (h21 : higham9_21_tridiag_solve_perturbation_model n L_hat U_hat
      y_hat x_hat b DeltaL DeltaU u) :
    higham9_21_tridiag_solve_perturbation_model n L_hat U_hat
      y_hat x_hat b DeltaL DeltaU v := by
  rcases h21 with ⟨hforward, hDeltaL, hback, hDeltaU⟩
  have hsq : u ^ 2 ≤ v ^ 2 := by
    have hprod : 0 ≤ (v - u) * (v + u) :=
      mul_nonneg (sub_nonneg.mpr huv) (by linarith)
    nlinarith
  have hcoeff : 2 * u + u ^ 2 ≤ 2 * v + v ^ 2 := by
    nlinarith
  refine ⟨hforward, ?_, hback, ?_⟩
  · intro i j
    exact le_trans (hDeltaL i j)
      (mul_le_mul_of_nonneg_right huv (abs_nonneg _))
  · intro i j
    exact le_trans (hDeltaU i j)
      (mul_le_mul_of_nonneg_right hcoeff (abs_nonneg _))

/-- **Equation (9.20)** from an existing LU backward-error certificate.

Any componentwise `LUBackwardError` certificate whose coefficient is bounded by
the source coefficient `u` supplies the explicit perturbation model used in
equation (9.20). -/
theorem higham9_20_tridiag_lu_perturbation_model_of_LUBackwardError_le
    (n : ℕ) (A L_hat U_hat : Fin n → Fin n → ℝ)
    (ε u : ℝ) (hε_le_u : ε ≤ u)
    (hLU : LUBackwardError n A L_hat U_hat ε) :
    ∃ DeltaA_LU : Fin n → Fin n → ℝ,
      higham9_20_tridiag_lu_perturbation_model n A L_hat U_hat
        DeltaA_LU u := by
  refine ⟨fun i j => ∑ k : Fin n, L_hat i k * U_hat k j - A i j, ?_⟩
  constructor
  · intro i j
    ring
  · intro i j
    have hsum_nonneg :
        0 ≤ ∑ k : Fin n, |L_hat i k| * |U_hat k j| :=
      Finset.sum_nonneg fun k _ => mul_nonneg (abs_nonneg _) (abs_nonneg _)
    exact le_trans (hLU.backward_bound i j)
      (mul_le_mul_of_nonneg_right hε_le_u hsum_nonneg)

/-- **Equation (9.20)** from a dense Doolittle loop certificate.

The literal square Algorithm 9.2 dense-loop certificate supplies the
componentwise LU backward-error certificate used by the equation-(9.20)
perturbation model, provided the caller weakens `γ_n` to the printed source
coefficient `u`. -/
theorem higham9_20_tridiag_lu_perturbation_model_of_DoolittleDenseLoopCertificate
    (fp : FPModel) (n : ℕ)
    (A L_hat U_hat : Fin n → Fin n → ℝ)
    (u : ℝ) (hn : gammaValid fp n)
    (hγ_le_u : gamma fp n ≤ u)
    (hC : higham9_2_DoolittleDenseLoopCertificate n A L_hat U_hat fp) :
    ∃ DeltaA_LU : Fin n → Fin n → ℝ,
      higham9_20_tridiag_lu_perturbation_model n A L_hat U_hat
        DeltaA_LU u :=
  higham9_20_tridiag_lu_perturbation_model_of_LUBackwardError_le
    n A L_hat U_hat (gamma fp n) u hγ_le_u
    (DoolittleDenseLoopCertificate.to_LUBackwardError hC hn)

/-- **Equation (9.20)** from an absolute-budget dense Doolittle certificate.

Absolute entry residual budgets for the square Algorithm 9.2 dense loop first
compress to a componentwise LU backward-error certificate and then supply the
equation-(9.20) perturbation model. -/
theorem higham9_20_tridiag_lu_perturbation_model_of_DoolittleDenseLoopAbsBudgetCertificate
    (fp : FPModel) (n : ℕ)
    (A L_hat U_hat : Fin n → Fin n → ℝ)
    (BU BL : Fin n → Fin n → ℝ)
    (u : ℝ) (hn : gammaValid fp n)
    (hγ_le_u : gamma fp n ≤ u)
    (hC : higham9_2_DoolittleDenseLoopAbsBudgetCertificate n
      A L_hat U_hat fp BU BL) :
    ∃ DeltaA_LU : Fin n → Fin n → ℝ,
      higham9_20_tridiag_lu_perturbation_model n A L_hat U_hat
        DeltaA_LU u :=
  higham9_20_tridiag_lu_perturbation_model_of_LUBackwardError_le
    n A L_hat U_hat (gamma fp n) u hγ_le_u
    (DoolittleDenseLoopAbsBudgetCertificate.to_LUBackwardError hC hn)

/-- **Equation (9.20)** from a square-specialized rectangular dense Doolittle
certificate.

At `m = n`, the rectangular Algorithm 9.2 dense-loop certificate feeds the
existing square Doolittle source perturbation model through the certified
rectangular-to-square bridge. -/
theorem higham9_20_tridiag_lu_perturbation_model_of_RectDoolittleDenseLoopCertificate_square
    (fp : FPModel) (n : ℕ)
    (A L_hat U_hat : Fin n → Fin n → ℝ)
    (u : ℝ) (hn : gammaValid fp n)
    (hγ_le_u : gamma fp n ≤ u)
    (hC : higham9_2_RectDoolittleDenseLoopCertificate
      (Nat.le_refl n) A L_hat U_hat fp) :
    ∃ DeltaA_LU : Fin n → Fin n → ℝ,
      higham9_20_tridiag_lu_perturbation_model n A L_hat U_hat
        DeltaA_LU u :=
  higham9_20_tridiag_lu_perturbation_model_of_DoolittleDenseLoopCertificate
    fp n A L_hat U_hat u hn hγ_le_u
    (higham9_2_rectDenseLoopCertificate_to_squareDenseLoopCertificate hC)

/-- **Equation (9.20)** from a square-specialized rectangular absolute-budget
Doolittle certificate.

This exposes the rectangular absolute-budget layer at the same source
perturbation interface as the square Algorithm 9.2 dense-loop certificate. -/
theorem higham9_20_tridiag_lu_perturbation_model_of_RectDoolittleDenseLoopAbsBudgetCertificate_square
    (fp : FPModel) (n : ℕ)
    (A L_hat U_hat : Fin n → Fin n → ℝ)
    (BU BL : Fin n → Fin n → ℝ)
    (u : ℝ) (hn : gammaValid fp n)
    (hγ_le_u : gamma fp n ≤ u)
    (hC : higham9_2_RectDoolittleDenseLoopAbsBudgetCertificate
      (Nat.le_refl n) A L_hat U_hat fp BU BL) :
    ∃ DeltaA_LU : Fin n → Fin n → ℝ,
      higham9_20_tridiag_lu_perturbation_model n A L_hat U_hat
        DeltaA_LU u :=
  higham9_20_tridiag_lu_perturbation_model_of_DoolittleDenseLoopAbsBudgetCertificate
    fp n A L_hat U_hat BU BL u hn hγ_le_u
    (higham9_2_rectAbsBudgetCertificate_to_squareAbsBudgetCertificate hC)

/-- **Equation (9.20)** from a square-specialized rectangular rounded-stage
Doolittle trace.

The rounded-stage trace is first compressed to the rectangular dense-loop
certificate API, and then reused by the square tridiagonal perturbation-model
wrapper. -/
theorem higham9_20_tridiag_lu_perturbation_model_of_RectDoolittleRoundedStageTrace_square
    (fp : FPModel) (n : ℕ)
    (A L_hat U_hat : Fin n → Fin n → ℝ)
    (u : ℝ) (hn : gammaValid fp n)
    (hγ_le_u : gamma fp n ≤ u)
    (hT : higham9_2_RectDoolittleRoundedStageTrace
      (Nat.le_refl n) A L_hat U_hat fp)
    (hU_diag : ∀ k : Fin n, U_hat k k ≠ 0)
    (hU_budget_le : ∀ k j : Fin n, k.val ≤ j.val →
      higham9_2_rectDoolittleUAbsBudget fp (Nat.le_refl n)
          A L_hat U_hat k j ≤ gamma fp n * |U_hat k j|)
    (hL_budget_le : ∀ i k : Fin n, k.val < i.val →
      higham9_2_rectDoolittleLAbsBudget fp A L_hat U_hat i k ≤
        gamma fp n * |L_hat i k * U_hat k k|) :
    ∃ DeltaA_LU : Fin n → Fin n → ℝ,
      higham9_20_tridiag_lu_perturbation_model n A L_hat U_hat
        DeltaA_LU u :=
  higham9_20_tridiag_lu_perturbation_model_of_RectDoolittleDenseLoopCertificate_square
    fp n A L_hat U_hat u hn hγ_le_u
    (higham9_2_rectRoundedStageTrace_to_rectDenseLoopCertificate
      hT hU_diag hn hU_budget_le hL_budget_le)

/-- **Equation (9.20)** from a square-specialized rectangular rounded-stage
Doolittle trace with the natural `γ_n` coefficient. -/
theorem higham9_20_tridiag_lu_perturbation_model_of_RectDoolittleRoundedStageTrace_square_gamma
    (fp : FPModel) (n : ℕ)
    (A L_hat U_hat : Fin n → Fin n → ℝ)
    (hn : gammaValid fp n)
    (hT : higham9_2_RectDoolittleRoundedStageTrace
      (Nat.le_refl n) A L_hat U_hat fp)
    (hU_diag : ∀ k : Fin n, U_hat k k ≠ 0)
    (hU_budget_le : ∀ k j : Fin n, k.val ≤ j.val →
      higham9_2_rectDoolittleUAbsBudget fp (Nat.le_refl n)
          A L_hat U_hat k j ≤ gamma fp n * |U_hat k j|)
    (hL_budget_le : ∀ i k : Fin n, k.val < i.val →
      higham9_2_rectDoolittleLAbsBudget fp A L_hat U_hat i k ≤
        gamma fp n * |L_hat i k * U_hat k k|) :
    ∃ DeltaA_LU : Fin n → Fin n → ℝ,
      higham9_20_tridiag_lu_perturbation_model n A L_hat U_hat
        DeltaA_LU (gamma fp n) :=
  higham9_20_tridiag_lu_perturbation_model_of_RectDoolittleRoundedStageTrace_square
    fp n A L_hat U_hat (gamma fp n) hn le_rfl
    hT hU_diag hU_budget_le hL_budget_le

/-- **Equation (9.20)** from the executable square rectangular rounded
Doolittle loop.

This is the concrete loop entry point for the LU perturbation model used by
the tridiagonal source analysis. -/
theorem higham9_20_tridiag_lu_perturbation_model_of_rectRoundedLoop_square
    (fp : FPModel) (n : ℕ)
    (A : Fin n → Fin n → ℝ)
    (u : ℝ) (hn : gammaValid fp n)
    (hγ_le_u : gamma fp n ≤ u)
    (hU_diag : ∀ k : Fin n,
      higham9_2_rectRoundedLoopU fp (Nat.le_refl n) A k k ≠ 0)
    (hU_budget_le : ∀ k j : Fin n, k.val ≤ j.val →
      higham9_2_rectDoolittleUAbsBudget fp (Nat.le_refl n) A
          (higham9_2_rectRoundedLoopL fp (Nat.le_refl n) A)
          (higham9_2_rectRoundedLoopU fp (Nat.le_refl n) A) k j ≤
        gamma fp n *
          |higham9_2_rectRoundedLoopU fp (Nat.le_refl n) A k j|)
    (hL_budget_le : ∀ i k : Fin n, k.val < i.val →
      higham9_2_rectDoolittleLAbsBudget fp A
          (higham9_2_rectRoundedLoopL fp (Nat.le_refl n) A)
          (higham9_2_rectRoundedLoopU fp (Nat.le_refl n) A) i k ≤
        gamma fp n *
          |higham9_2_rectRoundedLoopL fp (Nat.le_refl n) A i k *
            higham9_2_rectRoundedLoopU fp (Nat.le_refl n) A k k|) :
    let L_hat := higham9_2_rectRoundedLoopL fp (Nat.le_refl n) A
    let U_hat := higham9_2_rectRoundedLoopU fp (Nat.le_refl n) A
    ∃ DeltaA_LU : Fin n → Fin n → ℝ,
      higham9_20_tridiag_lu_perturbation_model n A L_hat U_hat
        DeltaA_LU u := by
  dsimp only
  exact
    higham9_20_tridiag_lu_perturbation_model_of_RectDoolittleRoundedStageTrace_square
      fp n A
      (higham9_2_rectRoundedLoopL fp (Nat.le_refl n) A)
      (higham9_2_rectRoundedLoopU fp (Nat.le_refl n) A)
      u hn hγ_le_u
      (higham9_2_rectRoundedLoopStageTrace fp (Nat.le_refl n) A)
      hU_diag hU_budget_le hL_budget_le

/-- **Equation (9.20)** from the executable square rectangular rounded
Doolittle loop with the natural `γ_n` coefficient. -/
theorem higham9_20_tridiag_lu_perturbation_model_of_rectRoundedLoop_square_gamma
    (fp : FPModel) (n : ℕ)
    (A : Fin n → Fin n → ℝ)
    (hn : gammaValid fp n)
    (hU_diag : ∀ k : Fin n,
      higham9_2_rectRoundedLoopU fp (Nat.le_refl n) A k k ≠ 0)
    (hU_budget_le : ∀ k j : Fin n, k.val ≤ j.val →
      higham9_2_rectDoolittleUAbsBudget fp (Nat.le_refl n) A
          (higham9_2_rectRoundedLoopL fp (Nat.le_refl n) A)
          (higham9_2_rectRoundedLoopU fp (Nat.le_refl n) A) k j ≤
        gamma fp n *
          |higham9_2_rectRoundedLoopU fp (Nat.le_refl n) A k j|)
    (hL_budget_le : ∀ i k : Fin n, k.val < i.val →
      higham9_2_rectDoolittleLAbsBudget fp A
          (higham9_2_rectRoundedLoopL fp (Nat.le_refl n) A)
          (higham9_2_rectRoundedLoopU fp (Nat.le_refl n) A) i k ≤
        gamma fp n *
          |higham9_2_rectRoundedLoopL fp (Nat.le_refl n) A i k *
            higham9_2_rectRoundedLoopU fp (Nat.le_refl n) A k k|) :
    let L_hat := higham9_2_rectRoundedLoopL fp (Nat.le_refl n) A
    let U_hat := higham9_2_rectRoundedLoopU fp (Nat.le_refl n) A
    ∃ DeltaA_LU : Fin n → Fin n → ℝ,
      higham9_20_tridiag_lu_perturbation_model n A L_hat U_hat
        DeltaA_LU (gamma fp n) :=
  higham9_20_tridiag_lu_perturbation_model_of_rectRoundedLoop_square
    fp n A (gamma fp n) hn le_rfl hU_diag hU_budget_le hL_budget_le

/-- **Equation (9.21)** for the actual triangular solves.

If the uniform triangular-solve coefficient `γ_n` is bounded by the source
coefficient `u`, then the computed `fl_forwardSub`/`fl_backSub` pair supplies
the explicit `DeltaL` and `DeltaU` model used in equation (9.21). -/
theorem higham9_21_tridiag_solve_perturbation_model_of_fl_triangular_solves_gamma_le
    (fp : FPModel) (n : ℕ)
    (L_hat U_hat : Fin n → Fin n → ℝ) (b : Fin n → ℝ)
    (u : ℝ) (hu : 0 ≤ u)
    (hL_diag : ∀ i : Fin n, L_hat i i ≠ 0)
    (hU_diag : ∀ i : Fin n, U_hat i i ≠ 0)
    (hLT : ∀ i j : Fin n, i.val < j.val → L_hat i j = 0)
    (hUT : ∀ i j : Fin n, j.val < i.val → U_hat i j = 0)
    (hn : gammaValid fp n)
    (hγ_le_u : gamma fp n ≤ u) :
    ∃ DeltaL DeltaU : Fin n → Fin n → ℝ,
      higham9_21_tridiag_solve_perturbation_model n L_hat U_hat
        (fl_forwardSub fp n L_hat b)
        (fl_backSub fp n U_hat (fl_forwardSub fp n L_hat b))
        b DeltaL DeltaU u := by
  obtain ⟨DeltaL, hDeltaL_bound, hDeltaL_eq⟩ :=
    forwardSub_backward_error fp n L_hat b hL_diag hLT hn
  obtain ⟨DeltaU, hDeltaU_bound, hDeltaU_eq⟩ :=
    backSub_backward_error fp n U_hat (fl_forwardSub fp n L_hat b)
      hU_diag hUT hn
  refine ⟨DeltaL, DeltaU, ?_, ?_, ?_, ?_⟩
  · exact hDeltaL_eq
  · intro i j
    exact le_trans (hDeltaL_bound i j)
      (mul_le_mul_of_nonneg_right hγ_le_u (abs_nonneg _))
  · exact hDeltaU_eq
  · intro i j
    have hu_le_ucoeff : u ≤ 2 * u + u ^ 2 := by
      nlinarith [sq_nonneg u, hu]
    have hγ_le_ucoeff : gamma fp n ≤ 2 * u + u ^ 2 :=
      hγ_le_u.trans hu_le_ucoeff
    exact le_trans (hDeltaU_bound i j)
      (mul_le_mul_of_nonneg_right hγ_le_ucoeff (abs_nonneg _))

/-- **Equation (9.21)** for actual triangular solves with the natural
`γ_n` source coefficient. -/
theorem higham9_21_tridiag_solve_perturbation_model_of_fl_triangular_solves_gamma
    (fp : FPModel) (n : ℕ)
    (L_hat U_hat : Fin n → Fin n → ℝ) (b : Fin n → ℝ)
    (hL_diag : ∀ i : Fin n, L_hat i i ≠ 0)
    (hU_diag : ∀ i : Fin n, U_hat i i ≠ 0)
    (hLT : ∀ i j : Fin n, i.val < j.val → L_hat i j = 0)
    (hUT : ∀ i j : Fin n, j.val < i.val → U_hat i j = 0)
    (hn : gammaValid fp n) :
    ∃ DeltaL DeltaU : Fin n → Fin n → ℝ,
      higham9_21_tridiag_solve_perturbation_model n L_hat U_hat
        (fl_forwardSub fp n L_hat b)
        (fl_backSub fp n U_hat (fl_forwardSub fp n L_hat b))
        b DeltaL DeltaU (gamma fp n) :=
  higham9_21_tridiag_solve_perturbation_model_of_fl_triangular_solves_gamma_le
    fp n L_hat U_hat b (gamma fp n) (gamma_nonneg fp hn)
    hL_diag hU_diag hLT hUT hn le_rfl

/-- **Equations (9.20)--(9.22)**, source-coefficient aggregation.

If the tridiagonal LU factorization perturbation has coefficient `u`, the
forward solve has coefficient `u`, and the back solve has coefficient
`2u + u²`, then the combined solve perturbation has the printed source
coefficient `f(u) = 4u + 3u² + u³` multiplying `|L̂||Û|`. -/
theorem higham9_14_source_f_bound (n : ℕ)
    (A L_hat U_hat : Fin n → Fin n → ℝ)
    (y_hat x_hat : Fin n → ℝ)
    (b : Fin n → ℝ)
    (u : ℝ) (hu : 0 ≤ u)
    (ΔA_LU : Fin n → Fin n → ℝ)
    (hΔA_LU_bound : ∀ i j, |ΔA_LU i j| ≤
      u * ∑ k : Fin n, |L_hat i k| * |U_hat k j|)
    (hΔA_LU_eq : ∀ i j,
      ∑ k : Fin n, L_hat i k * U_hat k j = A i j + ΔA_LU i j)
    (ΔL : Fin n → Fin n → ℝ)
    (hΔL_bound : ∀ i j, |ΔL i j| ≤ u * |L_hat i j|)
    (hΔL_eq : ∀ i, ∑ j : Fin n, (L_hat i j + ΔL i j) * y_hat j = b i)
    (ΔU : Fin n → Fin n → ℝ)
    (hΔU_bound : ∀ i j, |ΔU i j| ≤ (2 * u + u ^ 2) * |U_hat i j|)
    (hΔU_eq : ∀ i, ∑ j : Fin n, (U_hat i j + ΔU i j) * x_hat j = y_hat i) :
    ∃ ΔA : Fin n → Fin n → ℝ,
      (∀ i j, |ΔA i j| ≤
        higham9_14_f u * ∑ k : Fin n, |L_hat i k| * |U_hat k j|) ∧
      (∀ i, ∑ j : Fin n, (A i j + ΔA i j) * x_hat j = b i) := by
  have hUcoeff : 0 ≤ 2 * u + u ^ 2 := by
    nlinarith [sq_nonneg u, hu]
  obtain ⟨ΔA, hΔA_bound, hΔA_eq⟩ :=
    lu_solve_backward_error_mixed n A L_hat U_hat y_hat x_hat
      u u (2 * u + u ^ 2) hu hu hUcoeff
      ΔA_LU hΔA_LU_bound hΔA_LU_eq
      b ΔL hΔL_bound hΔL_eq ΔU hΔU_bound hΔU_eq
  refine ⟨ΔA, ?_, hΔA_eq⟩
  intro i j
  calc |ΔA i j|
      ≤ (u + u + (2 * u + u ^ 2) + u * (2 * u + u ^ 2)) *
          ∑ k : Fin n, |L_hat i k| * |U_hat k j| := hΔA_bound i j
    _ = higham9_14_f u * ∑ k : Fin n, |L_hat i k| * |U_hat k j| := by
        unfold higham9_14_f
        ring

/-- **Equations (9.20)--(9.22)**, aggregation from the explicit source models.

This wrapper consumes the equation (9.20) and (9.21) model predicates and
returns the printed equation (9.22) perturbation coefficient. -/
theorem higham9_22_source_f_bound_of_9_20_9_21_models (n : ℕ)
    (A L_hat U_hat : Fin n → Fin n → ℝ)
    (y_hat x_hat b : Fin n → ℝ)
    (u : ℝ) (hu : 0 ≤ u)
    (DeltaA_LU DeltaL DeltaU : Fin n → Fin n → ℝ)
    (h20 : higham9_20_tridiag_lu_perturbation_model n A L_hat U_hat
      DeltaA_LU u)
    (h21 : higham9_21_tridiag_solve_perturbation_model n L_hat U_hat
      y_hat x_hat b DeltaL DeltaU u) :
    ∃ DeltaA : Fin n → Fin n → ℝ,
      (∀ i j, |DeltaA i j| ≤
        higham9_14_f u * ∑ k : Fin n, |L_hat i k| * |U_hat k j|) ∧
      (∀ i, ∑ j : Fin n, (A i j + DeltaA i j) * x_hat j = b i) := by
  rcases h20 with ⟨hDeltaA_LU_eq, hDeltaA_LU_bound⟩
  rcases h21 with ⟨hDeltaL_eq, hDeltaL_bound, hDeltaU_eq, hDeltaU_bound⟩
  exact higham9_14_source_f_bound n A L_hat U_hat y_hat x_hat b u hu
    DeltaA_LU hDeltaA_LU_bound hDeltaA_LU_eq
    DeltaL hDeltaL_bound hDeltaL_eq
    DeltaU hDeltaU_bound hDeltaU_eq

/-- **Equations (9.20)--(9.22)**, native Matrix-model aggregation.

This is the source-facing Matrix form of
`higham9_22_source_f_bound_of_9_20_9_21_models`: the equation (9.20) model is
given as `Lhat * Uhat = A + ΔA_LU`, the equation (9.21) models are given as
`Matrix.mulVec` solve equations, and the conclusion is the equation-(9.22)
combined perturbation with `(A + ΔA) xhat = b`. -/
theorem higham9_22_matrix_source_f_bound_of_matrix_models (n : ℕ)
    (A L_hat U_hat : Matrix (Fin n) (Fin n) ℝ)
    (y_hat x_hat b : Fin n → ℝ)
    (u : ℝ) (hu : 0 ≤ u)
    (DeltaA_LU DeltaL DeltaU : Matrix (Fin n) (Fin n) ℝ)
    (h20 :
      (L_hat * U_hat = fun i j => A i j + DeltaA_LU i j) ∧
        ∀ i j : Fin n,
          |DeltaA_LU i j| ≤
            u * ∑ k : Fin n, |L_hat i k| * |U_hat k j|)
    (h21 :
      Matrix.mulVec (fun i j => L_hat i j + DeltaL i j) y_hat = b ∧
        (∀ i j : Fin n, |DeltaL i j| ≤ u * |L_hat i j|) ∧
        Matrix.mulVec (fun i j => U_hat i j + DeltaU i j) x_hat = y_hat ∧
        ∀ i j : Fin n,
          |DeltaU i j| ≤ (2 * u + u ^ 2) * |U_hat i j|) :
    ∃ DeltaA : Matrix (Fin n) (Fin n) ℝ,
      (∀ i j, |DeltaA i j| ≤
        higham9_14_f u * ∑ k : Fin n, |L_hat i k| * |U_hat k j|) ∧
      Matrix.mulVec (fun i j => A i j + DeltaA i j) x_hat = b := by
  have h20_model :
      higham9_20_tridiag_lu_perturbation_model n A L_hat U_hat
        DeltaA_LU u :=
    (higham9_20_tridiag_lu_perturbation_model_iff_matrix_mul
      n A L_hat U_hat DeltaA_LU u).2 h20
  have h21_model :
      higham9_21_tridiag_solve_perturbation_model n L_hat U_hat
        y_hat x_hat b DeltaL DeltaU u :=
    (higham9_21_tridiag_solve_perturbation_model_iff_matrix_mulVec
      n L_hat U_hat y_hat x_hat b DeltaL DeltaU u).2 h21
  obtain ⟨DeltaA, hDeltaA_bound, hDeltaA_eq⟩ :=
    higham9_22_source_f_bound_of_9_20_9_21_models n A L_hat U_hat
      y_hat x_hat b u hu DeltaA_LU DeltaL DeltaU h20_model h21_model
  refine ⟨DeltaA, hDeltaA_bound, ?_⟩
  funext i
  simpa [Matrix.mulVec, dotProduct] using hDeltaA_eq i

/-- **Theorem 9.14**, conditional `h(u)` source bound.

This is the final scalar step after `higham9_14_source_f_bound`: once the
remaining class-specific comparison
`|L̂||Û| <= |A|/(1-u)` is available, the printed bound
`|ΔA| <= h(u)|A|` follows. -/
theorem higham9_14_source_h_bound_of_absLUhat_bound (n : ℕ)
    (A L_hat U_hat : Fin n → Fin n → ℝ)
    (y_hat x_hat : Fin n → ℝ)
    (b : Fin n → ℝ)
    (u : ℝ) (hu : 0 ≤ u)
    (hAbsLUhat_bound : ∀ i j : Fin n,
      ∑ k : Fin n, |L_hat i k| * |U_hat k j| ≤ |A i j| / (1 - u))
    (ΔA_LU : Fin n → Fin n → ℝ)
    (hΔA_LU_bound : ∀ i j, |ΔA_LU i j| ≤
      u * ∑ k : Fin n, |L_hat i k| * |U_hat k j|)
    (hΔA_LU_eq : ∀ i j,
      ∑ k : Fin n, L_hat i k * U_hat k j = A i j + ΔA_LU i j)
    (ΔL : Fin n → Fin n → ℝ)
    (hΔL_bound : ∀ i j, |ΔL i j| ≤ u * |L_hat i j|)
    (hΔL_eq : ∀ i, ∑ j : Fin n, (L_hat i j + ΔL i j) * y_hat j = b i)
    (ΔU : Fin n → Fin n → ℝ)
    (hΔU_bound : ∀ i j, |ΔU i j| ≤ (2 * u + u ^ 2) * |U_hat i j|)
    (hΔU_eq : ∀ i, ∑ j : Fin n, (U_hat i j + ΔU i j) * x_hat j = y_hat i) :
    ∃ ΔA : Fin n → Fin n → ℝ,
      (∀ i j, |ΔA i j| ≤ higham9_14_h u * |A i j|) ∧
      (∀ i, ∑ j : Fin n, (A i j + ΔA i j) * x_hat j = b i) := by
  obtain ⟨ΔA, hΔA_bound, hΔA_eq⟩ :=
    higham9_14_source_f_bound n A L_hat U_hat y_hat x_hat b u hu
      ΔA_LU hΔA_LU_bound hΔA_LU_eq
      ΔL hΔL_bound hΔL_eq ΔU hΔU_bound hΔU_eq
  refine ⟨ΔA, ?_, hΔA_eq⟩
  intro i j
  have hf_nonneg : 0 ≤ higham9_14_f u := higham9_14_f_nonneg hu
  calc |ΔA i j|
      ≤ higham9_14_f u * ∑ k : Fin n, |L_hat i k| * |U_hat k j| :=
        hΔA_bound i j
    _ ≤ higham9_14_f u * (|A i j| / (1 - u)) :=
        mul_le_mul_of_nonneg_left (hAbsLUhat_bound i j) hf_nonneg
    _ = higham9_14_h u * |A i j| := by
        unfold higham9_14_h
        ring

/-- **Theorem 9.14**, denominator-cleared `h(u)` source bound.

This is the same conditional `h(u)` conclusion as
`higham9_14_source_h_bound_of_absLUhat_bound`, but with the comparison
hypothesis in the source-shaped form
`(1-u) * |L_hat||U_hat| <= |A|`. -/
theorem higham9_14_source_h_bound_of_absLUhat_mul_one_sub_bound (n : ℕ)
    (A L_hat U_hat : Fin n → Fin n → ℝ)
    (y_hat x_hat : Fin n → ℝ)
    (b : Fin n → ℝ)
    (u : ℝ) (hu : 0 ≤ u) (hu_lt_one : u < 1)
    (hAbsLUhat_mul_bound : ∀ i j : Fin n,
      (1 - u) * (∑ k : Fin n, |L_hat i k| * |U_hat k j|) ≤ |A i j|)
    (ΔA_LU : Fin n → Fin n → ℝ)
    (hΔA_LU_bound : ∀ i j, |ΔA_LU i j| ≤
      u * ∑ k : Fin n, |L_hat i k| * |U_hat k j|)
    (hΔA_LU_eq : ∀ i j,
      ∑ k : Fin n, L_hat i k * U_hat k j = A i j + ΔA_LU i j)
    (ΔL : Fin n → Fin n → ℝ)
    (hΔL_bound : ∀ i j, |ΔL i j| ≤ u * |L_hat i j|)
    (hΔL_eq : ∀ i, ∑ j : Fin n, (L_hat i j + ΔL i j) * y_hat j = b i)
    (ΔU : Fin n → Fin n → ℝ)
    (hΔU_bound : ∀ i j, |ΔU i j| ≤ (2 * u + u ^ 2) * |U_hat i j|)
    (hΔU_eq : ∀ i, ∑ j : Fin n, (U_hat i j + ΔU i j) * x_hat j = y_hat i) :
    ∃ ΔA : Fin n → Fin n → ℝ,
      (∀ i j, |ΔA i j| ≤ higham9_14_h u * |A i j|) ∧
      (∀ i, ∑ j : Fin n, (A i j + ΔA i j) * x_hat j = b i) := by
  refine higham9_14_source_h_bound_of_absLUhat_bound n A L_hat U_hat
    y_hat x_hat b u hu ?_ ΔA_LU hΔA_LU_bound hΔA_LU_eq
    ΔL hΔL_bound hΔL_eq ΔU hΔU_bound hΔU_eq
  intro i j
  have hpos : 0 < 1 - u := by linarith
  exact (le_div_iff₀ hpos).mpr (by
    simpa [mul_comm, mul_left_comm, mul_assoc] using hAbsLUhat_mul_bound i j)

/-- **Theorem 9.14**, model-consuming conditional `h(u)` source bound.

This combines the explicit equation (9.20)/(9.21) source models with the
class-specific comparison `|Lhat||Uhat| <= |A|/(1-u)`, yielding the printed
`h(u)|A|` backward-error surface. -/
theorem higham9_14_source_h_bound_of_9_20_9_21_models_absLUhat_bound (n : ℕ)
    (A L_hat U_hat : Fin n → Fin n → ℝ)
    (y_hat x_hat b : Fin n → ℝ)
    (u : ℝ) (hu : 0 ≤ u)
    (hAbsLUhat_bound : ∀ i j : Fin n,
      ∑ k : Fin n, |L_hat i k| * |U_hat k j| ≤ |A i j| / (1 - u))
    (DeltaA_LU DeltaL DeltaU : Fin n → Fin n → ℝ)
    (h20 : higham9_20_tridiag_lu_perturbation_model n A L_hat U_hat
      DeltaA_LU u)
    (h21 : higham9_21_tridiag_solve_perturbation_model n L_hat U_hat
      y_hat x_hat b DeltaL DeltaU u) :
    ∃ DeltaA : Fin n → Fin n → ℝ,
      (∀ i j, |DeltaA i j| ≤ higham9_14_h u * |A i j|) ∧
      (∀ i, ∑ j : Fin n, (A i j + DeltaA i j) * x_hat j = b i) := by
  rcases h20 with ⟨hDeltaA_LU_eq, hDeltaA_LU_bound⟩
  rcases h21 with ⟨hDeltaL_eq, hDeltaL_bound, hDeltaU_eq, hDeltaU_bound⟩
  exact higham9_14_source_h_bound_of_absLUhat_bound n A L_hat U_hat
    y_hat x_hat b u hu hAbsLUhat_bound
    DeltaA_LU hDeltaA_LU_bound hDeltaA_LU_eq
    DeltaL hDeltaL_bound hDeltaL_eq
    DeltaU hDeltaU_bound hDeltaU_eq

/-- **Theorem 9.14**, model-consuming denominator-cleared `h(u)` source bound.

This is the same source-facing final bound as
`higham9_14_source_h_bound_of_9_20_9_21_models_absLUhat_bound`, but the
class-specific comparison is given in the printed denominator-cleared form
`(1-u)|Lhat||Uhat| <= |A|`. -/
theorem higham9_14_source_h_bound_of_9_20_9_21_models_absLUhat_mul_one_sub_bound
    (n : ℕ)
    (A L_hat U_hat : Fin n → Fin n → ℝ)
    (y_hat x_hat b : Fin n → ℝ)
    (u : ℝ) (hu : 0 ≤ u) (hu_lt_one : u < 1)
    (hAbsLUhat_mul_bound : ∀ i j : Fin n,
      (1 - u) * (∑ k : Fin n, |L_hat i k| * |U_hat k j|) ≤ |A i j|)
    (DeltaA_LU DeltaL DeltaU : Fin n → Fin n → ℝ)
    (h20 : higham9_20_tridiag_lu_perturbation_model n A L_hat U_hat
      DeltaA_LU u)
    (h21 : higham9_21_tridiag_solve_perturbation_model n L_hat U_hat
      y_hat x_hat b DeltaL DeltaU u) :
    ∃ DeltaA : Fin n → Fin n → ℝ,
      (∀ i j, |DeltaA i j| ≤ higham9_14_h u * |A i j|) ∧
      (∀ i, ∑ j : Fin n, (A i j + DeltaA i j) * x_hat j = b i) := by
  rcases h20 with ⟨hDeltaA_LU_eq, hDeltaA_LU_bound⟩
  rcases h21 with ⟨hDeltaL_eq, hDeltaL_bound, hDeltaU_eq, hDeltaU_bound⟩
  exact higham9_14_source_h_bound_of_absLUhat_mul_one_sub_bound n
    A L_hat U_hat y_hat x_hat b u hu hu_lt_one hAbsLUhat_mul_bound
    DeltaA_LU hDeltaA_LU_bound hDeltaA_LU_eq
    DeltaL hDeltaL_bound hDeltaL_eq
    DeltaU hDeltaU_bound hDeltaU_eq

/-- **Theorem 9.14**, Matrix-model conditional `h(u)` source bound.

This is the native Matrix counterpart of
`higham9_14_source_h_bound_of_9_20_9_21_models_absLUhat_bound`. -/
theorem higham9_14_matrix_source_h_bound_of_matrix_models_absLUhat_bound
    (n : ℕ)
    (A L_hat U_hat : Matrix (Fin n) (Fin n) ℝ)
    (y_hat x_hat b : Fin n → ℝ)
    (u : ℝ) (hu : 0 ≤ u)
    (hAbsLUhat_bound : ∀ i j : Fin n,
      ∑ k : Fin n, |L_hat i k| * |U_hat k j| ≤ |A i j| / (1 - u))
    (DeltaA_LU DeltaL DeltaU : Matrix (Fin n) (Fin n) ℝ)
    (h20 :
      (L_hat * U_hat = fun i j => A i j + DeltaA_LU i j) ∧
        ∀ i j : Fin n,
          |DeltaA_LU i j| ≤
            u * ∑ k : Fin n, |L_hat i k| * |U_hat k j|)
    (h21 :
      Matrix.mulVec (fun i j => L_hat i j + DeltaL i j) y_hat = b ∧
        (∀ i j : Fin n, |DeltaL i j| ≤ u * |L_hat i j|) ∧
        Matrix.mulVec (fun i j => U_hat i j + DeltaU i j) x_hat = y_hat ∧
        ∀ i j : Fin n,
          |DeltaU i j| ≤ (2 * u + u ^ 2) * |U_hat i j|) :
    ∃ DeltaA : Matrix (Fin n) (Fin n) ℝ,
      (∀ i j, |DeltaA i j| ≤ higham9_14_h u * |A i j|) ∧
      Matrix.mulVec (fun i j => A i j + DeltaA i j) x_hat = b := by
  have h20_model :
      higham9_20_tridiag_lu_perturbation_model n A L_hat U_hat
        DeltaA_LU u :=
    (higham9_20_tridiag_lu_perturbation_model_iff_matrix_mul
      n A L_hat U_hat DeltaA_LU u).2 h20
  have h21_model :
      higham9_21_tridiag_solve_perturbation_model n L_hat U_hat
        y_hat x_hat b DeltaL DeltaU u :=
    (higham9_21_tridiag_solve_perturbation_model_iff_matrix_mulVec
      n L_hat U_hat y_hat x_hat b DeltaL DeltaU u).2 h21
  obtain ⟨DeltaA, hDeltaA_bound, hDeltaA_eq⟩ :=
    higham9_14_source_h_bound_of_9_20_9_21_models_absLUhat_bound
      n A L_hat U_hat y_hat x_hat b u hu hAbsLUhat_bound
      DeltaA_LU DeltaL DeltaU h20_model h21_model
  refine ⟨DeltaA, hDeltaA_bound, ?_⟩
  funext i
  simpa [Matrix.mulVec, dotProduct] using hDeltaA_eq i

/-- **Theorem 9.14**, Matrix-model denominator-cleared `h(u)` source bound.

This is the native Matrix counterpart of
`higham9_14_source_h_bound_of_9_20_9_21_models_absLUhat_mul_one_sub_bound`. -/
theorem higham9_14_matrix_source_h_bound_of_matrix_models_absLUhat_mul_one_sub_bound
    (n : ℕ)
    (A L_hat U_hat : Matrix (Fin n) (Fin n) ℝ)
    (y_hat x_hat b : Fin n → ℝ)
    (u : ℝ) (hu : 0 ≤ u) (hu_lt_one : u < 1)
    (hAbsLUhat_mul_bound : ∀ i j : Fin n,
      (1 - u) * (∑ k : Fin n, |L_hat i k| * |U_hat k j|) ≤ |A i j|)
    (DeltaA_LU DeltaL DeltaU : Matrix (Fin n) (Fin n) ℝ)
    (h20 :
      (L_hat * U_hat = fun i j => A i j + DeltaA_LU i j) ∧
        ∀ i j : Fin n,
          |DeltaA_LU i j| ≤
            u * ∑ k : Fin n, |L_hat i k| * |U_hat k j|)
    (h21 :
      Matrix.mulVec (fun i j => L_hat i j + DeltaL i j) y_hat = b ∧
        (∀ i j : Fin n, |DeltaL i j| ≤ u * |L_hat i j|) ∧
        Matrix.mulVec (fun i j => U_hat i j + DeltaU i j) x_hat = y_hat ∧
        ∀ i j : Fin n,
          |DeltaU i j| ≤ (2 * u + u ^ 2) * |U_hat i j|) :
    ∃ DeltaA : Matrix (Fin n) (Fin n) ℝ,
      (∀ i j, |DeltaA i j| ≤ higham9_14_h u * |A i j|) ∧
      Matrix.mulVec (fun i j => A i j + DeltaA i j) x_hat = b := by
  have h20_model :
      higham9_20_tridiag_lu_perturbation_model n A L_hat U_hat
        DeltaA_LU u :=
    (higham9_20_tridiag_lu_perturbation_model_iff_matrix_mul
      n A L_hat U_hat DeltaA_LU u).2 h20
  have h21_model :
      higham9_21_tridiag_solve_perturbation_model n L_hat U_hat
        y_hat x_hat b DeltaL DeltaU u :=
    (higham9_21_tridiag_solve_perturbation_model_iff_matrix_mulVec
      n L_hat U_hat y_hat x_hat b DeltaL DeltaU u).2 h21
  obtain ⟨DeltaA, hDeltaA_bound, hDeltaA_eq⟩ :=
    higham9_14_source_h_bound_of_9_20_9_21_models_absLUhat_mul_one_sub_bound
      n A L_hat U_hat y_hat x_hat b u hu hu_lt_one hAbsLUhat_mul_bound
      DeltaA_LU DeltaL DeltaU h20_model h21_model
  refine ⟨DeltaA, hDeltaA_bound, ?_⟩
  funext i
  simpa [Matrix.mulVec, dotProduct] using hDeltaA_eq i

/-- **Theorem 9.14**, optimal-growth model bridge to the final `h(u)` bound.

If a special tridiagonal class supplies the exact-arithmetic comparison
`|Lhat||Uhat| <= |A|`, then the source equation (9.20)/(9.21) models imply
the final printed `h(u)|A|` backward-error bound.  This does not prove the
rounded recurrence models; it consumes them explicitly. -/
theorem higham9_14_source_h_bound_of_absLU_le_absA_and_9_20_9_21_models
    (n : ℕ)
    (A L_hat U_hat : Fin n → Fin n → ℝ)
    (y_hat x_hat b : Fin n → ℝ)
    (u : ℝ) (hu : 0 ≤ u) (hu_lt_one : u < 1)
    (hAbsLU_le : ∀ i j : Fin n,
      ∑ k : Fin n, |L_hat i k| * |U_hat k j| ≤ |A i j|)
    (DeltaA_LU DeltaL DeltaU : Fin n → Fin n → ℝ)
    (h20 : higham9_20_tridiag_lu_perturbation_model n A L_hat U_hat
      DeltaA_LU u)
    (h21 : higham9_21_tridiag_solve_perturbation_model n L_hat U_hat
      y_hat x_hat b DeltaL DeltaU u) :
    ∃ DeltaA : Fin n → Fin n → ℝ,
      (∀ i j, |DeltaA i j| ≤ higham9_14_h u * |A i j|) ∧
      (∀ i, ∑ j : Fin n, (A i j + DeltaA i j) * x_hat j = b i) := by
  apply higham9_14_source_h_bound_of_9_20_9_21_models_absLUhat_mul_one_sub_bound
    n A L_hat U_hat y_hat x_hat b u hu hu_lt_one
  · intro i j
    have hcoef : 1 - u ≤ 1 := by linarith
    have hsum_nonneg :
        0 ≤ ∑ k : Fin n, |L_hat i k| * |U_hat k j| :=
      Finset.sum_nonneg fun k _ => mul_nonneg (abs_nonneg _) (abs_nonneg _)
    calc
      (1 - u) * (∑ k : Fin n, |L_hat i k| * |U_hat k j|)
          ≤ 1 * (∑ k : Fin n, |L_hat i k| * |U_hat k j|) :=
            mul_le_mul_of_nonneg_right hcoef hsum_nonneg
      _ = ∑ k : Fin n, |L_hat i k| * |U_hat k j| := by ring
      _ ≤ |A i j| := hAbsLU_le i j
  · exact h20
  · exact h21

/-- **Theorem 9.14**, model-consuming constant-growth source bound.

Equation (9.22) gives `f(u)|Lhat||Uhat|`.  If a structural theorem supplies
`|Lhat||Uhat| <= c|A|`, this wrapper exposes the resulting
`c f(u)|A|` bound while still leaving the equation (9.20)/(9.21) perturbation
models explicit. -/
theorem higham9_14_source_f_bound_of_absLU_le_const_absA_and_9_20_9_21_models
    (n : ℕ)
    (A L_hat U_hat : Fin n → Fin n → ℝ)
    (y_hat x_hat b : Fin n → ℝ)
    (c u : ℝ) (hu : 0 ≤ u)
    (hAbsLU_le : ∀ i j : Fin n,
      ∑ k : Fin n, |L_hat i k| * |U_hat k j| ≤ c * |A i j|)
    (DeltaA_LU DeltaL DeltaU : Fin n → Fin n → ℝ)
    (h20 : higham9_20_tridiag_lu_perturbation_model n A L_hat U_hat
      DeltaA_LU u)
    (h21 : higham9_21_tridiag_solve_perturbation_model n L_hat U_hat
      y_hat x_hat b DeltaL DeltaU u) :
    ∃ DeltaA : Fin n → Fin n → ℝ,
      (∀ i j, |DeltaA i j| ≤ c * higham9_14_f u * |A i j|) ∧
      (∀ i, ∑ j : Fin n, (A i j + DeltaA i j) * x_hat j = b i) := by
  obtain ⟨DeltaA, hDeltaA_bound, hDeltaA_eq⟩ :=
    higham9_22_source_f_bound_of_9_20_9_21_models n A L_hat U_hat
      y_hat x_hat b u hu DeltaA_LU DeltaL DeltaU h20 h21
  refine ⟨DeltaA, ?_, hDeltaA_eq⟩
  intro i j
  have hf_nonneg : 0 ≤ higham9_14_f u := higham9_14_f_nonneg hu
  calc
    |DeltaA i j|
        ≤ higham9_14_f u *
            ∑ k : Fin n, |L_hat i k| * |U_hat k j| :=
          hDeltaA_bound i j
    _ ≤ higham9_14_f u * (c * |A i j|) :=
          mul_le_mul_of_nonneg_left (hAbsLU_le i j) hf_nonneg
    _ = c * higham9_14_f u * |A i j| := by ring

/-- **Theorem 9.14**, model-consuming constant-growth final `h(u)` source
bound.

This is the final-coefficient counterpart of
`higham9_14_source_f_bound_of_absLU_le_const_absA_and_9_20_9_21_models`: if a
class-specific theorem supplies `|Lhat||Uhat| <= c|A|`, the equation
(9.20)/(9.21) models imply the widened final bound
`c h(u)|A|` under `0 <= u < 1`. -/
theorem higham9_14_source_h_bound_of_absLU_le_const_absA_and_9_20_9_21_models
    (n : ℕ)
    (A L_hat U_hat : Fin n → Fin n → ℝ)
    (y_hat x_hat b : Fin n → ℝ)
    (c u : ℝ) (hc : 0 ≤ c) (hu : 0 ≤ u) (hu_lt_one : u < 1)
    (hAbsLU_le : ∀ i j : Fin n,
      ∑ k : Fin n, |L_hat i k| * |U_hat k j| ≤ c * |A i j|)
    (DeltaA_LU DeltaL DeltaU : Fin n → Fin n → ℝ)
    (h20 : higham9_20_tridiag_lu_perturbation_model n A L_hat U_hat
      DeltaA_LU u)
    (h21 : higham9_21_tridiag_solve_perturbation_model n L_hat U_hat
      y_hat x_hat b DeltaL DeltaU u) :
    ∃ DeltaA : Fin n → Fin n → ℝ,
      (∀ i j, |DeltaA i j| ≤ c * higham9_14_h u * |A i j|) ∧
      (∀ i, ∑ j : Fin n, (A i j + DeltaA i j) * x_hat j = b i) := by
  obtain ⟨DeltaA, hDeltaA_bound, hDeltaA_eq⟩ :=
    higham9_14_source_f_bound_of_absLU_le_const_absA_and_9_20_9_21_models
      n A L_hat U_hat y_hat x_hat b c u hu hAbsLU_le
      DeltaA_LU DeltaL DeltaU h20 h21
  refine ⟨DeltaA, ?_, hDeltaA_eq⟩
  intro i j
  have hf_le_h : higham9_14_f u ≤ higham9_14_h u :=
    higham9_14_f_le_h hu hu_lt_one
  have hc_bound : c * higham9_14_f u ≤ c * higham9_14_h u :=
    mul_le_mul_of_nonneg_left hf_le_h hc
  exact (hDeltaA_bound i j).trans
    (mul_le_mul_of_nonneg_right hc_bound (abs_nonneg (A i j)))

/-- **Theorem 9.14**, optimal-growth model bridge to the equation-(9.22)
`f(u)` source bound.

If a special tridiagonal class supplies the exact-arithmetic comparison
`|Lhat||Uhat| <= |A|`, then the source equation (9.20)/(9.21) models imply
the `f(u)|A|` backward-error bound from equation (9.22). -/
theorem higham9_14_source_f_bound_of_absLU_le_absA_and_9_20_9_21_models
    (n : ℕ)
    (A L_hat U_hat : Fin n → Fin n → ℝ)
    (y_hat x_hat b : Fin n → ℝ)
    (u : ℝ) (hu : 0 ≤ u)
    (hAbsLU_le : ∀ i j : Fin n,
      ∑ k : Fin n, |L_hat i k| * |U_hat k j| ≤ |A i j|)
    (DeltaA_LU DeltaL DeltaU : Fin n → Fin n → ℝ)
    (h20 : higham9_20_tridiag_lu_perturbation_model n A L_hat U_hat
      DeltaA_LU u)
    (h21 : higham9_21_tridiag_solve_perturbation_model n L_hat U_hat
      y_hat x_hat b DeltaL DeltaU u) :
    ∃ DeltaA : Fin n → Fin n → ℝ,
      (∀ i j, |DeltaA i j| ≤ higham9_14_f u * |A i j|) ∧
      (∀ i, ∑ j : Fin n, (A i j + DeltaA i j) * x_hat j = b i) := by
  simpa [one_mul] using
    (higham9_14_source_f_bound_of_absLU_le_const_absA_and_9_20_9_21_models
      n A L_hat U_hat y_hat x_hat b 1 u hu
      (fun i j => by simpa [one_mul] using hAbsLU_le i j)
      DeltaA_LU DeltaL DeltaU h20 h21)

/-- **Theorem 9.14**, Matrix-model optimal-growth bridge to the final
`h(u)` source bound. -/
theorem higham9_14_matrix_source_h_bound_of_absLU_le_absA_and_matrix_models
    (n : ℕ)
    (A L_hat U_hat : Matrix (Fin n) (Fin n) ℝ)
    (y_hat x_hat b : Fin n → ℝ)
    (u : ℝ) (hu : 0 ≤ u) (hu_lt_one : u < 1)
    (hAbsLU_le : ∀ i j : Fin n,
      ∑ k : Fin n, |L_hat i k| * |U_hat k j| ≤ |A i j|)
    (DeltaA_LU DeltaL DeltaU : Matrix (Fin n) (Fin n) ℝ)
    (h20 :
      (L_hat * U_hat = fun i j => A i j + DeltaA_LU i j) ∧
        ∀ i j : Fin n,
          |DeltaA_LU i j| ≤
            u * ∑ k : Fin n, |L_hat i k| * |U_hat k j|)
    (h21 :
      Matrix.mulVec (fun i j => L_hat i j + DeltaL i j) y_hat = b ∧
        (∀ i j : Fin n, |DeltaL i j| ≤ u * |L_hat i j|) ∧
        Matrix.mulVec (fun i j => U_hat i j + DeltaU i j) x_hat = y_hat ∧
        ∀ i j : Fin n,
          |DeltaU i j| ≤ (2 * u + u ^ 2) * |U_hat i j|) :
    ∃ DeltaA : Matrix (Fin n) (Fin n) ℝ,
      (∀ i j, |DeltaA i j| ≤ higham9_14_h u * |A i j|) ∧
      Matrix.mulVec (fun i j => A i j + DeltaA i j) x_hat = b := by
  have h20_model :
      higham9_20_tridiag_lu_perturbation_model n A L_hat U_hat
        DeltaA_LU u :=
    (higham9_20_tridiag_lu_perturbation_model_iff_matrix_mul
      n A L_hat U_hat DeltaA_LU u).2 h20
  have h21_model :
      higham9_21_tridiag_solve_perturbation_model n L_hat U_hat
        y_hat x_hat b DeltaL DeltaU u :=
    (higham9_21_tridiag_solve_perturbation_model_iff_matrix_mulVec
      n L_hat U_hat y_hat x_hat b DeltaL DeltaU u).2 h21
  obtain ⟨DeltaA, hDeltaA_bound, hDeltaA_eq⟩ :=
    higham9_14_source_h_bound_of_absLU_le_absA_and_9_20_9_21_models
      n A L_hat U_hat y_hat x_hat b u hu hu_lt_one hAbsLU_le
      DeltaA_LU DeltaL DeltaU h20_model h21_model
  refine ⟨DeltaA, hDeltaA_bound, ?_⟩
  funext i
  simpa [Matrix.mulVec, dotProduct] using hDeltaA_eq i

/-- **Theorem 9.14**, Matrix-model constant-growth source bridge to the
equation-(9.22) `f(u)` bound. -/
theorem higham9_14_matrix_source_f_bound_of_absLU_le_const_absA_and_matrix_models
    (n : ℕ)
    (A L_hat U_hat : Matrix (Fin n) (Fin n) ℝ)
    (y_hat x_hat b : Fin n → ℝ)
    (c u : ℝ) (hu : 0 ≤ u)
    (hAbsLU_le : ∀ i j : Fin n,
      ∑ k : Fin n, |L_hat i k| * |U_hat k j| ≤ c * |A i j|)
    (DeltaA_LU DeltaL DeltaU : Matrix (Fin n) (Fin n) ℝ)
    (h20 :
      (L_hat * U_hat = fun i j => A i j + DeltaA_LU i j) ∧
        ∀ i j : Fin n,
          |DeltaA_LU i j| ≤
            u * ∑ k : Fin n, |L_hat i k| * |U_hat k j|)
    (h21 :
      Matrix.mulVec (fun i j => L_hat i j + DeltaL i j) y_hat = b ∧
        (∀ i j : Fin n, |DeltaL i j| ≤ u * |L_hat i j|) ∧
        Matrix.mulVec (fun i j => U_hat i j + DeltaU i j) x_hat = y_hat ∧
        ∀ i j : Fin n,
          |DeltaU i j| ≤ (2 * u + u ^ 2) * |U_hat i j|) :
    ∃ DeltaA : Matrix (Fin n) (Fin n) ℝ,
      (∀ i j, |DeltaA i j| ≤ c * higham9_14_f u * |A i j|) ∧
      Matrix.mulVec (fun i j => A i j + DeltaA i j) x_hat = b := by
  have h20_model :
      higham9_20_tridiag_lu_perturbation_model n A L_hat U_hat
        DeltaA_LU u :=
    (higham9_20_tridiag_lu_perturbation_model_iff_matrix_mul
      n A L_hat U_hat DeltaA_LU u).2 h20
  have h21_model :
      higham9_21_tridiag_solve_perturbation_model n L_hat U_hat
        y_hat x_hat b DeltaL DeltaU u :=
    (higham9_21_tridiag_solve_perturbation_model_iff_matrix_mulVec
      n L_hat U_hat y_hat x_hat b DeltaL DeltaU u).2 h21
  obtain ⟨DeltaA, hDeltaA_bound, hDeltaA_eq⟩ :=
    higham9_14_source_f_bound_of_absLU_le_const_absA_and_9_20_9_21_models
      n A L_hat U_hat y_hat x_hat b c u hu hAbsLU_le
      DeltaA_LU DeltaL DeltaU h20_model h21_model
  refine ⟨DeltaA, hDeltaA_bound, ?_⟩
  funext i
  simpa [Matrix.mulVec, dotProduct] using hDeltaA_eq i

/-- **Theorem 9.14**, Matrix-model constant-growth bridge to the final
`h(u)` source bound. -/
theorem higham9_14_matrix_source_h_bound_of_absLU_le_const_absA_and_matrix_models
    (n : ℕ)
    (A L_hat U_hat : Matrix (Fin n) (Fin n) ℝ)
    (y_hat x_hat b : Fin n → ℝ)
    (c u : ℝ) (hc : 0 ≤ c) (hu : 0 ≤ u) (hu_lt_one : u < 1)
    (hAbsLU_le : ∀ i j : Fin n,
      ∑ k : Fin n, |L_hat i k| * |U_hat k j| ≤ c * |A i j|)
    (DeltaA_LU DeltaL DeltaU : Matrix (Fin n) (Fin n) ℝ)
    (h20 :
      (L_hat * U_hat = fun i j => A i j + DeltaA_LU i j) ∧
        ∀ i j : Fin n,
          |DeltaA_LU i j| ≤
            u * ∑ k : Fin n, |L_hat i k| * |U_hat k j|)
    (h21 :
      Matrix.mulVec (fun i j => L_hat i j + DeltaL i j) y_hat = b ∧
        (∀ i j : Fin n, |DeltaL i j| ≤ u * |L_hat i j|) ∧
        Matrix.mulVec (fun i j => U_hat i j + DeltaU i j) x_hat = y_hat ∧
        ∀ i j : Fin n,
          |DeltaU i j| ≤ (2 * u + u ^ 2) * |U_hat i j|) :
    ∃ DeltaA : Matrix (Fin n) (Fin n) ℝ,
      (∀ i j, |DeltaA i j| ≤ c * higham9_14_h u * |A i j|) ∧
      Matrix.mulVec (fun i j => A i j + DeltaA i j) x_hat = b := by
  have h20_model :
      higham9_20_tridiag_lu_perturbation_model n A L_hat U_hat
        DeltaA_LU u :=
    (higham9_20_tridiag_lu_perturbation_model_iff_matrix_mul
      n A L_hat U_hat DeltaA_LU u).2 h20
  have h21_model :
      higham9_21_tridiag_solve_perturbation_model n L_hat U_hat
        y_hat x_hat b DeltaL DeltaU u :=
    (higham9_21_tridiag_solve_perturbation_model_iff_matrix_mulVec
      n L_hat U_hat y_hat x_hat b DeltaL DeltaU u).2 h21
  obtain ⟨DeltaA, hDeltaA_bound, hDeltaA_eq⟩ :=
    higham9_14_source_h_bound_of_absLU_le_const_absA_and_9_20_9_21_models
      n A L_hat U_hat y_hat x_hat b c u hc hu hu_lt_one hAbsLU_le
      DeltaA_LU DeltaL DeltaU h20_model h21_model
  refine ⟨DeltaA, hDeltaA_bound, ?_⟩
  funext i
  simpa [Matrix.mulVec, dotProduct] using hDeltaA_eq i

/-- **Theorem 9.14**, Matrix-model optimal-growth source bridge to the
equation-(9.22) `f(u)` bound. -/
theorem higham9_14_matrix_source_f_bound_of_absLU_le_absA_and_matrix_models
    (n : ℕ)
    (A L_hat U_hat : Matrix (Fin n) (Fin n) ℝ)
    (y_hat x_hat b : Fin n → ℝ)
    (u : ℝ) (hu : 0 ≤ u)
    (hAbsLU_le : ∀ i j : Fin n,
      ∑ k : Fin n, |L_hat i k| * |U_hat k j| ≤ |A i j|)
    (DeltaA_LU DeltaL DeltaU : Matrix (Fin n) (Fin n) ℝ)
    (h20 :
      (L_hat * U_hat = fun i j => A i j + DeltaA_LU i j) ∧
        ∀ i j : Fin n,
          |DeltaA_LU i j| ≤
            u * ∑ k : Fin n, |L_hat i k| * |U_hat k j|)
    (h21 :
      Matrix.mulVec (fun i j => L_hat i j + DeltaL i j) y_hat = b ∧
        (∀ i j : Fin n, |DeltaL i j| ≤ u * |L_hat i j|) ∧
        Matrix.mulVec (fun i j => U_hat i j + DeltaU i j) x_hat = y_hat ∧
        ∀ i j : Fin n,
          |DeltaU i j| ≤ (2 * u + u ^ 2) * |U_hat i j|) :
    ∃ DeltaA : Matrix (Fin n) (Fin n) ℝ,
      (∀ i j, |DeltaA i j| ≤ higham9_14_f u * |A i j|) ∧
      Matrix.mulVec (fun i j => A i j + DeltaA i j) x_hat = b := by
  have h20_model :
      higham9_20_tridiag_lu_perturbation_model n A L_hat U_hat
        DeltaA_LU u :=
    (higham9_20_tridiag_lu_perturbation_model_iff_matrix_mul
      n A L_hat U_hat DeltaA_LU u).2 h20
  have h21_model :
      higham9_21_tridiag_solve_perturbation_model n L_hat U_hat
        y_hat x_hat b DeltaL DeltaU u :=
    (higham9_21_tridiag_solve_perturbation_model_iff_matrix_mulVec
      n L_hat U_hat y_hat x_hat b DeltaL DeltaU u).2 h21
  obtain ⟨DeltaA, hDeltaA_bound, hDeltaA_eq⟩ :=
    higham9_14_source_f_bound_of_absLU_le_absA_and_9_20_9_21_models
      n A L_hat U_hat y_hat x_hat b u hu hAbsLU_le
      DeltaA_LU DeltaL DeltaU h20_model h21_model
  refine ⟨DeltaA, hDeltaA_bound, ?_⟩
  funext i
  simpa [Matrix.mulVec, dotProduct] using hDeltaA_eq i

/-- **Equations (9.20)--(9.22)**, source-coefficient weakening for explicit
perturbation models.

If the equation (9.20) and (9.21) models are established with coefficient
`u0`, then the same witnesses produce the equation-(9.22) `f(u)` source bound
for any larger coefficient `u`. -/
theorem higham9_22_source_f_bound_of_9_20_9_21_models_le (n : ℕ)
    (A L_hat U_hat : Fin n → Fin n → ℝ)
    (y_hat x_hat b : Fin n → ℝ)
    (u0 u : ℝ) (hu0 : 0 ≤ u0) (hu0_le_u : u0 ≤ u)
    (DeltaA_LU DeltaL DeltaU : Fin n → Fin n → ℝ)
    (h20 : higham9_20_tridiag_lu_perturbation_model n A L_hat U_hat
      DeltaA_LU u0)
    (h21 : higham9_21_tridiag_solve_perturbation_model n L_hat U_hat
      y_hat x_hat b DeltaL DeltaU u0) :
    ∃ DeltaA : Fin n → Fin n → ℝ,
      (∀ i j, |DeltaA i j| ≤
        higham9_14_f u * ∑ k : Fin n, |L_hat i k| * |U_hat k j|) ∧
      (∀ i, ∑ j : Fin n, (A i j + DeltaA i j) * x_hat j = b i) := by
  have hu : 0 ≤ u := hu0.trans hu0_le_u
  exact higham9_22_source_f_bound_of_9_20_9_21_models n A L_hat U_hat
    y_hat x_hat b u hu DeltaA_LU DeltaL DeltaU
    (higham9_20_tridiag_lu_perturbation_model_mono
      n A L_hat U_hat DeltaA_LU hu0_le_u h20)
    (higham9_21_tridiag_solve_perturbation_model_mono
      n L_hat U_hat y_hat x_hat b DeltaL DeltaU hu0 hu0_le_u h21)

/-- **Theorem 9.14**, constant-growth model source bound under coefficient
weakening.

This is the coefficient-weakened counterpart of
`higham9_14_source_f_bound_of_absLU_le_const_absA_and_9_20_9_21_models`:
models proved at `u0` may be consumed at any larger printed coefficient `u`. -/
theorem higham9_14_source_f_bound_of_absLU_le_const_absA_and_9_20_9_21_models_le
    (n : ℕ)
    (A L_hat U_hat : Fin n → Fin n → ℝ)
    (y_hat x_hat b : Fin n → ℝ)
    (c u0 u : ℝ) (hu0 : 0 ≤ u0) (hu0_le_u : u0 ≤ u)
    (hAbsLU_le : ∀ i j : Fin n,
      ∑ k : Fin n, |L_hat i k| * |U_hat k j| ≤ c * |A i j|)
    (DeltaA_LU DeltaL DeltaU : Fin n → Fin n → ℝ)
    (h20 : higham9_20_tridiag_lu_perturbation_model n A L_hat U_hat
      DeltaA_LU u0)
    (h21 : higham9_21_tridiag_solve_perturbation_model n L_hat U_hat
      y_hat x_hat b DeltaL DeltaU u0) :
    ∃ DeltaA : Fin n → Fin n → ℝ,
      (∀ i j, |DeltaA i j| ≤ c * higham9_14_f u * |A i j|) ∧
      (∀ i, ∑ j : Fin n, (A i j + DeltaA i j) * x_hat j = b i) := by
  have hu : 0 ≤ u := hu0.trans hu0_le_u
  exact higham9_14_source_f_bound_of_absLU_le_const_absA_and_9_20_9_21_models
    n A L_hat U_hat y_hat x_hat b c u hu hAbsLU_le
    DeltaA_LU DeltaL DeltaU
    (higham9_20_tridiag_lu_perturbation_model_mono
      n A L_hat U_hat DeltaA_LU hu0_le_u h20)
    (higham9_21_tridiag_solve_perturbation_model_mono
      n L_hat U_hat y_hat x_hat b DeltaL DeltaU hu0 hu0_le_u h21)

/-- **Theorem 9.14**, constant-growth final source bound under coefficient
weakening. -/
theorem higham9_14_source_h_bound_of_absLU_le_const_absA_and_9_20_9_21_models_le
    (n : ℕ)
    (A L_hat U_hat : Fin n → Fin n → ℝ)
    (y_hat x_hat b : Fin n → ℝ)
    (c u0 u : ℝ) (hc : 0 ≤ c) (hu0 : 0 ≤ u0) (hu0_le_u : u0 ≤ u)
    (hu_lt_one : u < 1)
    (hAbsLU_le : ∀ i j : Fin n,
      ∑ k : Fin n, |L_hat i k| * |U_hat k j| ≤ c * |A i j|)
    (DeltaA_LU DeltaL DeltaU : Fin n → Fin n → ℝ)
    (h20 : higham9_20_tridiag_lu_perturbation_model n A L_hat U_hat
      DeltaA_LU u0)
    (h21 : higham9_21_tridiag_solve_perturbation_model n L_hat U_hat
      y_hat x_hat b DeltaL DeltaU u0) :
    ∃ DeltaA : Fin n → Fin n → ℝ,
      (∀ i j, |DeltaA i j| ≤ c * higham9_14_h u * |A i j|) ∧
      (∀ i, ∑ j : Fin n, (A i j + DeltaA i j) * x_hat j = b i) := by
  have hu : 0 ≤ u := hu0.trans hu0_le_u
  exact higham9_14_source_h_bound_of_absLU_le_const_absA_and_9_20_9_21_models
    n A L_hat U_hat y_hat x_hat b c u hc hu hu_lt_one hAbsLU_le
    DeltaA_LU DeltaL DeltaU
    (higham9_20_tridiag_lu_perturbation_model_mono
      n A L_hat U_hat DeltaA_LU hu0_le_u h20)
    (higham9_21_tridiag_solve_perturbation_model_mono
      n L_hat U_hat y_hat x_hat b DeltaL DeltaU hu0 hu0_le_u h21)

/-- **Theorem 9.14**, optimal-growth model source bound under coefficient
weakening. -/
theorem higham9_14_source_f_bound_of_absLU_le_absA_and_9_20_9_21_models_le
    (n : ℕ)
    (A L_hat U_hat : Fin n → Fin n → ℝ)
    (y_hat x_hat b : Fin n → ℝ)
    (u0 u : ℝ) (hu0 : 0 ≤ u0) (hu0_le_u : u0 ≤ u)
    (hAbsLU_le : ∀ i j : Fin n,
      ∑ k : Fin n, |L_hat i k| * |U_hat k j| ≤ |A i j|)
    (DeltaA_LU DeltaL DeltaU : Fin n → Fin n → ℝ)
    (h20 : higham9_20_tridiag_lu_perturbation_model n A L_hat U_hat
      DeltaA_LU u0)
    (h21 : higham9_21_tridiag_solve_perturbation_model n L_hat U_hat
      y_hat x_hat b DeltaL DeltaU u0) :
    ∃ DeltaA : Fin n → Fin n → ℝ,
      (∀ i j, |DeltaA i j| ≤ higham9_14_f u * |A i j|) ∧
      (∀ i, ∑ j : Fin n, (A i j + DeltaA i j) * x_hat j = b i) := by
  simpa [one_mul] using
    (higham9_14_source_f_bound_of_absLU_le_const_absA_and_9_20_9_21_models_le
      n A L_hat U_hat y_hat x_hat b 1 u0 u hu0 hu0_le_u
      (fun i j => by simpa [one_mul] using hAbsLU_le i j)
      DeltaA_LU DeltaL DeltaU h20 h21)

/-- **Theorem 9.14**, optimal-growth final source bound under coefficient
weakening. -/
theorem higham9_14_source_h_bound_of_absLU_le_absA_and_9_20_9_21_models_le
    (n : ℕ)
    (A L_hat U_hat : Fin n → Fin n → ℝ)
    (y_hat x_hat b : Fin n → ℝ)
    (u0 u : ℝ) (hu0 : 0 ≤ u0) (hu0_le_u : u0 ≤ u)
    (hu_lt_one : u < 1)
    (hAbsLU_le : ∀ i j : Fin n,
      ∑ k : Fin n, |L_hat i k| * |U_hat k j| ≤ |A i j|)
    (DeltaA_LU DeltaL DeltaU : Fin n → Fin n → ℝ)
    (h20 : higham9_20_tridiag_lu_perturbation_model n A L_hat U_hat
      DeltaA_LU u0)
    (h21 : higham9_21_tridiag_solve_perturbation_model n L_hat U_hat
      y_hat x_hat b DeltaL DeltaU u0) :
    ∃ DeltaA : Fin n → Fin n → ℝ,
      (∀ i j, |DeltaA i j| ≤ higham9_14_h u * |A i j|) ∧
      (∀ i, ∑ j : Fin n, (A i j + DeltaA i j) * x_hat j = b i) := by
  simpa [one_mul] using
    (higham9_14_source_h_bound_of_absLU_le_const_absA_and_9_20_9_21_models_le
      n A L_hat U_hat y_hat x_hat b 1 u0 u (by norm_num) hu0 hu0_le_u
      hu_lt_one
      (fun i j => by simpa [one_mul] using hAbsLU_le i j)
      DeltaA_LU DeltaL DeltaU h20 h21)

/-- **Equations (9.20)--(9.22)**, Matrix source-coefficient weakening for
explicit perturbation models. -/
theorem higham9_22_matrix_source_f_bound_of_matrix_models_le (n : ℕ)
    (A L_hat U_hat : Matrix (Fin n) (Fin n) ℝ)
    (y_hat x_hat b : Fin n → ℝ)
    (u0 u : ℝ) (hu0 : 0 ≤ u0) (hu0_le_u : u0 ≤ u)
    (DeltaA_LU DeltaL DeltaU : Matrix (Fin n) (Fin n) ℝ)
    (h20 :
      (L_hat * U_hat = fun i j => A i j + DeltaA_LU i j) ∧
        ∀ i j : Fin n,
          |DeltaA_LU i j| ≤
            u0 * ∑ k : Fin n, |L_hat i k| * |U_hat k j|)
    (h21 :
      Matrix.mulVec (fun i j => L_hat i j + DeltaL i j) y_hat = b ∧
        (∀ i j : Fin n, |DeltaL i j| ≤ u0 * |L_hat i j|) ∧
        Matrix.mulVec (fun i j => U_hat i j + DeltaU i j) x_hat = y_hat ∧
        ∀ i j : Fin n,
          |DeltaU i j| ≤ (2 * u0 + u0 ^ 2) * |U_hat i j|) :
    ∃ DeltaA : Matrix (Fin n) (Fin n) ℝ,
      (∀ i j, |DeltaA i j| ≤
        higham9_14_f u * ∑ k : Fin n, |L_hat i k| * |U_hat k j|) ∧
      Matrix.mulVec (fun i j => A i j + DeltaA i j) x_hat = b := by
  have h20_model :
      higham9_20_tridiag_lu_perturbation_model n A L_hat U_hat
        DeltaA_LU u0 :=
    (higham9_20_tridiag_lu_perturbation_model_iff_matrix_mul
      n A L_hat U_hat DeltaA_LU u0).2 h20
  have h21_model :
      higham9_21_tridiag_solve_perturbation_model n L_hat U_hat
        y_hat x_hat b DeltaL DeltaU u0 :=
    (higham9_21_tridiag_solve_perturbation_model_iff_matrix_mulVec
      n L_hat U_hat y_hat x_hat b DeltaL DeltaU u0).2 h21
  obtain ⟨DeltaA, hDeltaA_bound, hDeltaA_eq⟩ :=
    higham9_22_source_f_bound_of_9_20_9_21_models_le n A L_hat U_hat
      y_hat x_hat b u0 u hu0 hu0_le_u DeltaA_LU DeltaL DeltaU
      h20_model h21_model
  refine ⟨DeltaA, hDeltaA_bound, ?_⟩
  funext i
  simpa [Matrix.mulVec, dotProduct] using hDeltaA_eq i

/-- **Theorem 9.14**, Matrix constant-growth model source bound under
coefficient weakening. -/
theorem higham9_14_matrix_source_f_bound_of_absLU_le_const_absA_and_matrix_models_le
    (n : ℕ)
    (A L_hat U_hat : Matrix (Fin n) (Fin n) ℝ)
    (y_hat x_hat b : Fin n → ℝ)
    (c u0 u : ℝ) (hu0 : 0 ≤ u0) (hu0_le_u : u0 ≤ u)
    (hAbsLU_le : ∀ i j : Fin n,
      ∑ k : Fin n, |L_hat i k| * |U_hat k j| ≤ c * |A i j|)
    (DeltaA_LU DeltaL DeltaU : Matrix (Fin n) (Fin n) ℝ)
    (h20 :
      (L_hat * U_hat = fun i j => A i j + DeltaA_LU i j) ∧
        ∀ i j : Fin n,
          |DeltaA_LU i j| ≤
            u0 * ∑ k : Fin n, |L_hat i k| * |U_hat k j|)
    (h21 :
      Matrix.mulVec (fun i j => L_hat i j + DeltaL i j) y_hat = b ∧
        (∀ i j : Fin n, |DeltaL i j| ≤ u0 * |L_hat i j|) ∧
        Matrix.mulVec (fun i j => U_hat i j + DeltaU i j) x_hat = y_hat ∧
        ∀ i j : Fin n,
          |DeltaU i j| ≤ (2 * u0 + u0 ^ 2) * |U_hat i j|) :
    ∃ DeltaA : Matrix (Fin n) (Fin n) ℝ,
      (∀ i j, |DeltaA i j| ≤ c * higham9_14_f u * |A i j|) ∧
      Matrix.mulVec (fun i j => A i j + DeltaA i j) x_hat = b := by
  have h20_model :
      higham9_20_tridiag_lu_perturbation_model n A L_hat U_hat
        DeltaA_LU u0 :=
    (higham9_20_tridiag_lu_perturbation_model_iff_matrix_mul
      n A L_hat U_hat DeltaA_LU u0).2 h20
  have h21_model :
      higham9_21_tridiag_solve_perturbation_model n L_hat U_hat
        y_hat x_hat b DeltaL DeltaU u0 :=
    (higham9_21_tridiag_solve_perturbation_model_iff_matrix_mulVec
      n L_hat U_hat y_hat x_hat b DeltaL DeltaU u0).2 h21
  obtain ⟨DeltaA, hDeltaA_bound, hDeltaA_eq⟩ :=
    higham9_14_source_f_bound_of_absLU_le_const_absA_and_9_20_9_21_models_le
      n A L_hat U_hat y_hat x_hat b c u0 u hu0 hu0_le_u hAbsLU_le
      DeltaA_LU DeltaL DeltaU h20_model h21_model
  refine ⟨DeltaA, hDeltaA_bound, ?_⟩
  funext i
  simpa [Matrix.mulVec, dotProduct] using hDeltaA_eq i

/-- **Theorem 9.14**, Matrix constant-growth final source bound under
coefficient weakening. -/
theorem higham9_14_matrix_source_h_bound_of_absLU_le_const_absA_and_matrix_models_le
    (n : ℕ)
    (A L_hat U_hat : Matrix (Fin n) (Fin n) ℝ)
    (y_hat x_hat b : Fin n → ℝ)
    (c u0 u : ℝ) (hc : 0 ≤ c) (hu0 : 0 ≤ u0) (hu0_le_u : u0 ≤ u)
    (hu_lt_one : u < 1)
    (hAbsLU_le : ∀ i j : Fin n,
      ∑ k : Fin n, |L_hat i k| * |U_hat k j| ≤ c * |A i j|)
    (DeltaA_LU DeltaL DeltaU : Matrix (Fin n) (Fin n) ℝ)
    (h20 :
      (L_hat * U_hat = fun i j => A i j + DeltaA_LU i j) ∧
        ∀ i j : Fin n,
          |DeltaA_LU i j| ≤
            u0 * ∑ k : Fin n, |L_hat i k| * |U_hat k j|)
    (h21 :
      Matrix.mulVec (fun i j => L_hat i j + DeltaL i j) y_hat = b ∧
        (∀ i j : Fin n, |DeltaL i j| ≤ u0 * |L_hat i j|) ∧
        Matrix.mulVec (fun i j => U_hat i j + DeltaU i j) x_hat = y_hat ∧
        ∀ i j : Fin n,
          |DeltaU i j| ≤ (2 * u0 + u0 ^ 2) * |U_hat i j|) :
    ∃ DeltaA : Matrix (Fin n) (Fin n) ℝ,
      (∀ i j, |DeltaA i j| ≤ c * higham9_14_h u * |A i j|) ∧
      Matrix.mulVec (fun i j => A i j + DeltaA i j) x_hat = b := by
  have h20_model :
      higham9_20_tridiag_lu_perturbation_model n A L_hat U_hat
        DeltaA_LU u0 :=
    (higham9_20_tridiag_lu_perturbation_model_iff_matrix_mul
      n A L_hat U_hat DeltaA_LU u0).2 h20
  have h21_model :
      higham9_21_tridiag_solve_perturbation_model n L_hat U_hat
        y_hat x_hat b DeltaL DeltaU u0 :=
    (higham9_21_tridiag_solve_perturbation_model_iff_matrix_mulVec
      n L_hat U_hat y_hat x_hat b DeltaL DeltaU u0).2 h21
  obtain ⟨DeltaA, hDeltaA_bound, hDeltaA_eq⟩ :=
    higham9_14_source_h_bound_of_absLU_le_const_absA_and_9_20_9_21_models_le
      n A L_hat U_hat y_hat x_hat b c u0 u hc hu0 hu0_le_u
      hu_lt_one hAbsLU_le DeltaA_LU DeltaL DeltaU h20_model h21_model
  refine ⟨DeltaA, hDeltaA_bound, ?_⟩
  funext i
  simpa [Matrix.mulVec, dotProduct] using hDeltaA_eq i

/-- **Theorem 9.14**, Matrix optimal-growth model source bound under
coefficient weakening. -/
theorem higham9_14_matrix_source_f_bound_of_absLU_le_absA_and_matrix_models_le
    (n : ℕ)
    (A L_hat U_hat : Matrix (Fin n) (Fin n) ℝ)
    (y_hat x_hat b : Fin n → ℝ)
    (u0 u : ℝ) (hu0 : 0 ≤ u0) (hu0_le_u : u0 ≤ u)
    (hAbsLU_le : ∀ i j : Fin n,
      ∑ k : Fin n, |L_hat i k| * |U_hat k j| ≤ |A i j|)
    (DeltaA_LU DeltaL DeltaU : Matrix (Fin n) (Fin n) ℝ)
    (h20 :
      (L_hat * U_hat = fun i j => A i j + DeltaA_LU i j) ∧
        ∀ i j : Fin n,
          |DeltaA_LU i j| ≤
            u0 * ∑ k : Fin n, |L_hat i k| * |U_hat k j|)
    (h21 :
      Matrix.mulVec (fun i j => L_hat i j + DeltaL i j) y_hat = b ∧
        (∀ i j : Fin n, |DeltaL i j| ≤ u0 * |L_hat i j|) ∧
        Matrix.mulVec (fun i j => U_hat i j + DeltaU i j) x_hat = y_hat ∧
        ∀ i j : Fin n,
          |DeltaU i j| ≤ (2 * u0 + u0 ^ 2) * |U_hat i j|) :
    ∃ DeltaA : Matrix (Fin n) (Fin n) ℝ,
      (∀ i j, |DeltaA i j| ≤ higham9_14_f u * |A i j|) ∧
      Matrix.mulVec (fun i j => A i j + DeltaA i j) x_hat = b := by
  have h20_model :
      higham9_20_tridiag_lu_perturbation_model n A L_hat U_hat
        DeltaA_LU u0 :=
    (higham9_20_tridiag_lu_perturbation_model_iff_matrix_mul
      n A L_hat U_hat DeltaA_LU u0).2 h20
  have h21_model :
      higham9_21_tridiag_solve_perturbation_model n L_hat U_hat
        y_hat x_hat b DeltaL DeltaU u0 :=
    (higham9_21_tridiag_solve_perturbation_model_iff_matrix_mulVec
      n L_hat U_hat y_hat x_hat b DeltaL DeltaU u0).2 h21
  obtain ⟨DeltaA, hDeltaA_bound, hDeltaA_eq⟩ :=
    higham9_14_source_f_bound_of_absLU_le_absA_and_9_20_9_21_models_le
      n A L_hat U_hat y_hat x_hat b u0 u hu0 hu0_le_u hAbsLU_le
      DeltaA_LU DeltaL DeltaU h20_model h21_model
  refine ⟨DeltaA, hDeltaA_bound, ?_⟩
  funext i
  simpa [Matrix.mulVec, dotProduct] using hDeltaA_eq i

/-- **Theorem 9.14**, Matrix optimal-growth final source bound under
coefficient weakening. -/
theorem higham9_14_matrix_source_h_bound_of_absLU_le_absA_and_matrix_models_le
    (n : ℕ)
    (A L_hat U_hat : Matrix (Fin n) (Fin n) ℝ)
    (y_hat x_hat b : Fin n → ℝ)
    (u0 u : ℝ) (hu0 : 0 ≤ u0) (hu0_le_u : u0 ≤ u)
    (hu_lt_one : u < 1)
    (hAbsLU_le : ∀ i j : Fin n,
      ∑ k : Fin n, |L_hat i k| * |U_hat k j| ≤ |A i j|)
    (DeltaA_LU DeltaL DeltaU : Matrix (Fin n) (Fin n) ℝ)
    (h20 :
      (L_hat * U_hat = fun i j => A i j + DeltaA_LU i j) ∧
        ∀ i j : Fin n,
          |DeltaA_LU i j| ≤
            u0 * ∑ k : Fin n, |L_hat i k| * |U_hat k j|)
    (h21 :
      Matrix.mulVec (fun i j => L_hat i j + DeltaL i j) y_hat = b ∧
        (∀ i j : Fin n, |DeltaL i j| ≤ u0 * |L_hat i j|) ∧
        Matrix.mulVec (fun i j => U_hat i j + DeltaU i j) x_hat = y_hat ∧
        ∀ i j : Fin n,
          |DeltaU i j| ≤ (2 * u0 + u0 ^ 2) * |U_hat i j|) :
    ∃ DeltaA : Matrix (Fin n) (Fin n) ℝ,
      (∀ i j, |DeltaA i j| ≤ higham9_14_h u * |A i j|) ∧
      Matrix.mulVec (fun i j => A i j + DeltaA i j) x_hat = b := by
  have h20_model :
      higham9_20_tridiag_lu_perturbation_model n A L_hat U_hat
        DeltaA_LU u0 :=
    (higham9_20_tridiag_lu_perturbation_model_iff_matrix_mul
      n A L_hat U_hat DeltaA_LU u0).2 h20
  have h21_model :
      higham9_21_tridiag_solve_perturbation_model n L_hat U_hat
        y_hat x_hat b DeltaL DeltaU u0 :=
    (higham9_21_tridiag_solve_perturbation_model_iff_matrix_mulVec
      n L_hat U_hat y_hat x_hat b DeltaL DeltaU u0).2 h21
  obtain ⟨DeltaA, hDeltaA_bound, hDeltaA_eq⟩ :=
    higham9_14_source_h_bound_of_absLU_le_absA_and_9_20_9_21_models_le
      n A L_hat U_hat y_hat x_hat b u0 u hu0 hu0_le_u hu_lt_one
      hAbsLU_le DeltaA_LU DeltaL DeltaU h20_model h21_model
  refine ⟨DeltaA, hDeltaA_bound, ?_⟩
  funext i
  simpa [Matrix.mulVec, dotProduct] using hDeltaA_eq i

/-- **Theorem 9.14**, source-model production from LU and triangular-solve
certificates.

This wrapper instantiates equations (9.20) and (9.21) from an existing
componentwise LU backward-error certificate and the actual
`fl_forwardSub`/`fl_backSub` triangular solves, then applies the constant-growth
equation-(9.22) bridge.  The coefficient comparisons remain explicit: the
theorem does not identify a `γ_n` dense certificate with the printed unit
roundoff coefficient unless the caller supplies the needed inequalities. -/
theorem higham9_14_source_f_bound_of_LUBackwardError_fl_triangular_solves_gamma_le
    (fp : FPModel) (n : ℕ)
    (A L_hat U_hat : Fin n → Fin n → ℝ)
    (b : Fin n → ℝ)
    (c ε u : ℝ) (hu : 0 ≤ u)
    (hn : gammaValid fp n)
    (hLU : LUBackwardError n A L_hat U_hat ε)
    (hε_le_u : ε ≤ u)
    (hγ_le_u : gamma fp n ≤ u)
    (hU_diag : ∀ i : Fin n, U_hat i i ≠ 0)
    (hAbsLU_le : ∀ i j : Fin n,
      ∑ k : Fin n, |L_hat i k| * |U_hat k j| ≤ c * |A i j|) :
    let y_hat := fl_forwardSub fp n L_hat b
    let x_hat := fl_backSub fp n U_hat y_hat
    ∃ DeltaA : Fin n → Fin n → ℝ,
      (∀ i j, |DeltaA i j| ≤ c * higham9_14_f u * |A i j|) ∧
      (∀ i, ∑ j : Fin n, (A i j + DeltaA i j) * x_hat j = b i) := by
  intro y_hat x_hat
  have hL_diag_ne : ∀ i : Fin n, L_hat i i ≠ 0 := by
    intro i
    rw [hLU.L_diag i]
    norm_num
  obtain ⟨DeltaA_LU, h20⟩ :=
    higham9_20_tridiag_lu_perturbation_model_of_LUBackwardError_le
      n A L_hat U_hat ε u hε_le_u hLU
  obtain ⟨DeltaL, DeltaU, h21_raw⟩ :=
    higham9_21_tridiag_solve_perturbation_model_of_fl_triangular_solves_gamma_le
      fp n L_hat U_hat b u hu hL_diag_ne hU_diag
      hLU.L_upper_zero hLU.U_lower_zero hn hγ_le_u
  have h21 :
      higham9_21_tridiag_solve_perturbation_model n L_hat U_hat
        y_hat x_hat b DeltaL DeltaU u := by
    simpa [y_hat, x_hat] using h21_raw
  exact higham9_14_source_f_bound_of_absLU_le_const_absA_and_9_20_9_21_models
    n A L_hat U_hat y_hat x_hat b c u hu hAbsLU_le
    DeltaA_LU DeltaL DeltaU h20 h21

/-- **Theorem 9.14**, gamma-specialized source-model production.

This is the common repository path where both the LU factorization and the
triangular solves are available with the same `γ_n` coefficient. -/
theorem higham9_14_source_f_bound_of_LUBackwardError_fl_triangular_solves_gamma
    (fp : FPModel) (n : ℕ)
    (A L_hat U_hat : Fin n → Fin n → ℝ)
    (b : Fin n → ℝ)
    (c : ℝ)
    (hn : gammaValid fp n)
    (hLU : LUBackwardError n A L_hat U_hat (gamma fp n))
    (hU_diag : ∀ i : Fin n, U_hat i i ≠ 0)
    (hAbsLU_le : ∀ i j : Fin n,
      ∑ k : Fin n, |L_hat i k| * |U_hat k j| ≤ c * |A i j|) :
    let y_hat := fl_forwardSub fp n L_hat b
    let x_hat := fl_backSub fp n U_hat y_hat
    ∃ DeltaA : Fin n → Fin n → ℝ,
      (∀ i j, |DeltaA i j| ≤
        c * higham9_14_f (gamma fp n) * |A i j|) ∧
      (∀ i, ∑ j : Fin n, (A i j + DeltaA i j) * x_hat j = b i) :=
  higham9_14_source_f_bound_of_LUBackwardError_fl_triangular_solves_gamma_le
    fp n A L_hat U_hat b c (gamma fp n) (gamma fp n)
    (gamma_nonneg fp hn) hn hLU le_rfl le_rfl hU_diag hAbsLU_le

/-- **Theorem 9.14**, exact-LU factor plus actual triangular solves.

This is an exact-factor specialization of
`higham9_14_source_f_bound_of_LUBackwardError_fl_triangular_solves_gamma_le`:
an exact `LUFactSpec` supplies equation (9.20) with zero LU-factorization
coefficient, while the actual `fl_forwardSub`/`fl_backSub` calls supply the
triangular-solve model.  This does not model a rounded LU factorization path. -/
theorem higham9_14_source_f_bound_of_LUFactSpec_fl_triangular_solves_gamma_le
    (fp : FPModel) (n : ℕ)
    (A L_hat U_hat : Fin n → Fin n → ℝ)
    (b : Fin n → ℝ)
    (c u : ℝ) (hu : 0 ≤ u)
    (hn : gammaValid fp n)
    (hLU : LUFactSpec n A L_hat U_hat)
    (hγ_le_u : gamma fp n ≤ u)
    (hU_diag : ∀ i : Fin n, U_hat i i ≠ 0)
    (hAbsLU_le : ∀ i j : Fin n,
      ∑ k : Fin n, |L_hat i k| * |U_hat k j| ≤ c * |A i j|) :
    let y_hat := fl_forwardSub fp n L_hat b
    let x_hat := fl_backSub fp n U_hat y_hat
    ∃ DeltaA : Fin n → Fin n → ℝ,
      (∀ i j, |DeltaA i j| ≤ c * higham9_14_f u * |A i j|) ∧
      (∀ i, ∑ j : Fin n, (A i j + DeltaA i j) * x_hat j = b i) :=
  higham9_14_source_f_bound_of_LUBackwardError_fl_triangular_solves_gamma_le
    fp n A L_hat U_hat b c 0 u hu hn (LUFactSpec.to_LUBackwardError_zero hLU)
    hu hγ_le_u hU_diag hAbsLU_le

/-- **Theorem 9.14**, exact-LU factor plus actual triangular solves with the
natural `γ_n` coefficient. -/
theorem higham9_14_source_f_bound_of_LUFactSpec_fl_triangular_solves_gamma
    (fp : FPModel) (n : ℕ)
    (A L_hat U_hat : Fin n → Fin n → ℝ)
    (b : Fin n → ℝ)
    (c : ℝ)
    (hn : gammaValid fp n)
    (hLU : LUFactSpec n A L_hat U_hat)
    (hU_diag : ∀ i : Fin n, U_hat i i ≠ 0)
    (hAbsLU_le : ∀ i j : Fin n,
      ∑ k : Fin n, |L_hat i k| * |U_hat k j| ≤ c * |A i j|) :
    let y_hat := fl_forwardSub fp n L_hat b
    let x_hat := fl_backSub fp n U_hat y_hat
    ∃ DeltaA : Fin n → Fin n → ℝ,
      (∀ i j, |DeltaA i j| ≤
        c * higham9_14_f (gamma fp n) * |A i j|) ∧
      (∀ i, ∑ j : Fin n, (A i j + DeltaA i j) * x_hat j = b i) :=
  higham9_14_source_f_bound_of_LUFactSpec_fl_triangular_solves_gamma_le
    fp n A L_hat U_hat b c (gamma fp n) (gamma_nonneg fp hn) hn
    hLU le_rfl hU_diag hAbsLU_le

/-- **Theorem 9.14**, LU-backward-error plus actual triangular solves with
optimal growth and source `f(u)` coefficient. -/
theorem higham9_14_source_f_bound_of_LUBackwardError_fl_triangular_solves_absLU_le_absA_gamma_le
    (fp : FPModel) (n : ℕ)
    (A L_hat U_hat : Fin n → Fin n → ℝ)
    (b : Fin n → ℝ)
    (ε u : ℝ) (hu : 0 ≤ u)
    (hn : gammaValid fp n)
    (hLU : LUBackwardError n A L_hat U_hat ε)
    (hε_le_u : ε ≤ u)
    (hγ_le_u : gamma fp n ≤ u)
    (hU_diag : ∀ i : Fin n, U_hat i i ≠ 0)
    (hAbsLU_le : ∀ i j : Fin n,
      ∑ k : Fin n, |L_hat i k| * |U_hat k j| ≤ |A i j|) :
    let y_hat := fl_forwardSub fp n L_hat b
    let x_hat := fl_backSub fp n U_hat y_hat
    ∃ DeltaA : Fin n → Fin n → ℝ,
      (∀ i j, |DeltaA i j| ≤ higham9_14_f u * |A i j|) ∧
      (∀ i, ∑ j : Fin n, (A i j + DeltaA i j) * x_hat j = b i) := by
  simpa [one_mul] using
    (higham9_14_source_f_bound_of_LUBackwardError_fl_triangular_solves_gamma_le
      fp n A L_hat U_hat b 1 ε u hu hn hLU hε_le_u hγ_le_u hU_diag
      (fun i j => by simpa [one_mul] using hAbsLU_le i j))

/-- **Theorem 9.14**, LU-backward-error plus actual triangular solves with
optimal growth and the natural source `f(γ_n)` coefficient. -/
theorem higham9_14_source_f_bound_of_LUBackwardError_fl_triangular_solves_absLU_le_absA_gamma
    (fp : FPModel) (n : ℕ)
    (A L_hat U_hat : Fin n → Fin n → ℝ)
    (b : Fin n → ℝ)
    (hn : gammaValid fp n)
    (hLU : LUBackwardError n A L_hat U_hat (gamma fp n))
    (hU_diag : ∀ i : Fin n, U_hat i i ≠ 0)
    (hAbsLU_le : ∀ i j : Fin n,
      ∑ k : Fin n, |L_hat i k| * |U_hat k j| ≤ |A i j|) :
    let y_hat := fl_forwardSub fp n L_hat b
    let x_hat := fl_backSub fp n U_hat y_hat
    ∃ DeltaA : Fin n → Fin n → ℝ,
      (∀ i j, |DeltaA i j| ≤
        higham9_14_f (gamma fp n) * |A i j|) ∧
      (∀ i, ∑ j : Fin n, (A i j + DeltaA i j) * x_hat j = b i) := by
  simpa [one_mul] using
    (higham9_14_source_f_bound_of_LUBackwardError_fl_triangular_solves_gamma
      fp n A L_hat U_hat b 1 hn hLU hU_diag
      (fun i j => by simpa [one_mul] using hAbsLU_le i j))

/-- **Theorem 9.14**, exact-LU factor plus actual triangular solves with
optimal growth and source `f(u)` coefficient. -/
theorem higham9_14_source_f_bound_of_LUFactSpec_fl_triangular_solves_absLU_le_absA_gamma_le
    (fp : FPModel) (n : ℕ)
    (A L_hat U_hat : Fin n → Fin n → ℝ)
    (b : Fin n → ℝ)
    (u : ℝ) (hu : 0 ≤ u)
    (hn : gammaValid fp n)
    (hLU : LUFactSpec n A L_hat U_hat)
    (hγ_le_u : gamma fp n ≤ u)
    (hU_diag : ∀ i : Fin n, U_hat i i ≠ 0)
    (hAbsLU_le : ∀ i j : Fin n,
      ∑ k : Fin n, |L_hat i k| * |U_hat k j| ≤ |A i j|) :
    let y_hat := fl_forwardSub fp n L_hat b
    let x_hat := fl_backSub fp n U_hat y_hat
    ∃ DeltaA : Fin n → Fin n → ℝ,
      (∀ i j, |DeltaA i j| ≤ higham9_14_f u * |A i j|) ∧
      (∀ i, ∑ j : Fin n, (A i j + DeltaA i j) * x_hat j = b i) := by
  simpa [one_mul] using
    (higham9_14_source_f_bound_of_LUFactSpec_fl_triangular_solves_gamma_le
      fp n A L_hat U_hat b 1 u hu hn hLU hγ_le_u hU_diag
      (fun i j => by simpa [one_mul] using hAbsLU_le i j))

/-- **Theorem 9.14**, exact-LU factor plus actual triangular solves with
optimal growth and the natural source `f(γ_n)` coefficient. -/
theorem higham9_14_source_f_bound_of_LUFactSpec_fl_triangular_solves_absLU_le_absA_gamma
    (fp : FPModel) (n : ℕ)
    (A L_hat U_hat : Fin n → Fin n → ℝ)
    (b : Fin n → ℝ)
    (hn : gammaValid fp n)
    (hLU : LUFactSpec n A L_hat U_hat)
    (hU_diag : ∀ i : Fin n, U_hat i i ≠ 0)
    (hAbsLU_le : ∀ i j : Fin n,
      ∑ k : Fin n, |L_hat i k| * |U_hat k j| ≤ |A i j|) :
    let y_hat := fl_forwardSub fp n L_hat b
    let x_hat := fl_backSub fp n U_hat y_hat
    ∃ DeltaA : Fin n → Fin n → ℝ,
      (∀ i j, |DeltaA i j| ≤
        higham9_14_f (gamma fp n) * |A i j|) ∧
      (∀ i, ∑ j : Fin n, (A i j + DeltaA i j) * x_hat j = b i) := by
  simpa [one_mul] using
    (higham9_14_source_f_bound_of_LUFactSpec_fl_triangular_solves_gamma
      fp n A L_hat U_hat b 1 hn hLU hU_diag
      (fun i j => by simpa [one_mul] using hAbsLU_le i j))

/-- **Theorem 9.14**, exact-LU factor plus actual triangular solves with a
constant-growth final `h(u)` coefficient.

An exact `LUFactSpec` provides equation (9.20) with zero coefficient, the
actual triangular solves provide equation (9.21), and a structural comparison
`|Lhat||Uhat| <= c|A|` yields the source-facing `c h(u)|A|` final bound. -/
theorem higham9_14_source_h_bound_of_LUFactSpec_fl_triangular_solves_const_gamma_le
    (fp : FPModel) (n : ℕ)
    (A L_hat U_hat : Fin n → Fin n → ℝ)
    (b : Fin n → ℝ)
    (c u : ℝ) (hc : 0 ≤ c) (hu : 0 ≤ u) (hu_lt_one : u < 1)
    (hn : gammaValid fp n)
    (hLU : LUFactSpec n A L_hat U_hat)
    (hγ_le_u : gamma fp n ≤ u)
    (hU_diag : ∀ i : Fin n, U_hat i i ≠ 0)
    (hAbsLU_le : ∀ i j : Fin n,
      ∑ k : Fin n, |L_hat i k| * |U_hat k j| ≤ c * |A i j|) :
    let y_hat := fl_forwardSub fp n L_hat b
    let x_hat := fl_backSub fp n U_hat y_hat
    ∃ DeltaA : Fin n → Fin n → ℝ,
      (∀ i j, |DeltaA i j| ≤ c * higham9_14_h u * |A i j|) ∧
      (∀ i, ∑ j : Fin n, (A i j + DeltaA i j) * x_hat j = b i) := by
  obtain ⟨DeltaA, hDeltaA_bound, hDeltaA_eq⟩ :=
    higham9_14_source_f_bound_of_LUFactSpec_fl_triangular_solves_gamma_le
      fp n A L_hat U_hat b c u hu hn hLU hγ_le_u hU_diag hAbsLU_le
  refine ⟨DeltaA, ?_, hDeltaA_eq⟩
  intro i j
  have hf_le_h : higham9_14_f u ≤ higham9_14_h u :=
    higham9_14_f_le_h hu hu_lt_one
  have hc_bound : c * higham9_14_f u ≤ c * higham9_14_h u :=
    mul_le_mul_of_nonneg_left hf_le_h hc
  exact (hDeltaA_bound i j).trans
    (mul_le_mul_of_nonneg_right hc_bound (abs_nonneg (A i j)))

/-- **Theorem 9.14**, exact-LU factor plus actual triangular solves with a
constant-growth final `h(γ_n)` coefficient. -/
theorem higham9_14_source_h_bound_of_LUFactSpec_fl_triangular_solves_const_gamma
    (fp : FPModel) (n : ℕ)
    (A L_hat U_hat : Fin n → Fin n → ℝ)
    (b : Fin n → ℝ)
    (c : ℝ) (hc : 0 ≤ c)
    (hn : gammaValid fp n)
    (hγ_lt_one : gamma fp n < 1)
    (hLU : LUFactSpec n A L_hat U_hat)
    (hU_diag : ∀ i : Fin n, U_hat i i ≠ 0)
    (hAbsLU_le : ∀ i j : Fin n,
      ∑ k : Fin n, |L_hat i k| * |U_hat k j| ≤ c * |A i j|) :
    let y_hat := fl_forwardSub fp n L_hat b
    let x_hat := fl_backSub fp n U_hat y_hat
    ∃ DeltaA : Fin n → Fin n → ℝ,
      (∀ i j, |DeltaA i j| ≤
        c * higham9_14_h (gamma fp n) * |A i j|) ∧
      (∀ i, ∑ j : Fin n, (A i j + DeltaA i j) * x_hat j = b i) :=
  higham9_14_source_h_bound_of_LUFactSpec_fl_triangular_solves_const_gamma_le
    fp n A L_hat U_hat b c (gamma fp n) hc (gamma_nonneg fp hn)
    hγ_lt_one hn hLU le_rfl hU_diag hAbsLU_le

/-- **Theorem 9.14**, LU-backward-error plus actual triangular solves with a
constant-growth final `h(u)` coefficient.

This is the constant-growth counterpart of
`higham9_14_source_h_bound_of_LUBackwardError_fl_triangular_solves_gamma_le`.
It is useful for diagonally dominant tridiagonal classes, where the structural
comparison is `|Lhat||Uhat| <= 3|A|` rather than the optimal-growth
comparison `|Lhat||Uhat| <= |A|`. -/
theorem higham9_14_source_h_bound_of_LUBackwardError_fl_triangular_solves_const_gamma_le
    (fp : FPModel) (n : ℕ)
    (A L_hat U_hat : Fin n → Fin n → ℝ)
    (b : Fin n → ℝ)
    (c ε u : ℝ) (hc : 0 ≤ c) (hu : 0 ≤ u) (hu_lt_one : u < 1)
    (hn : gammaValid fp n)
    (hLU : LUBackwardError n A L_hat U_hat ε)
    (hε_le_u : ε ≤ u)
    (hγ_le_u : gamma fp n ≤ u)
    (hU_diag : ∀ i : Fin n, U_hat i i ≠ 0)
    (hAbsLU_le : ∀ i j : Fin n,
      ∑ k : Fin n, |L_hat i k| * |U_hat k j| ≤ c * |A i j|) :
    let y_hat := fl_forwardSub fp n L_hat b
    let x_hat := fl_backSub fp n U_hat y_hat
    ∃ DeltaA : Fin n → Fin n → ℝ,
      (∀ i j, |DeltaA i j| ≤ c * higham9_14_h u * |A i j|) ∧
      (∀ i, ∑ j : Fin n, (A i j + DeltaA i j) * x_hat j = b i) := by
  obtain ⟨DeltaA, hDeltaA_bound, hDeltaA_eq⟩ :=
    higham9_14_source_f_bound_of_LUBackwardError_fl_triangular_solves_gamma_le
      fp n A L_hat U_hat b c ε u hu hn hLU hε_le_u hγ_le_u hU_diag
      hAbsLU_le
  refine ⟨DeltaA, ?_, hDeltaA_eq⟩
  intro i j
  have hf_le_h : higham9_14_f u ≤ higham9_14_h u :=
    higham9_14_f_le_h hu hu_lt_one
  have hc_bound : c * higham9_14_f u ≤ c * higham9_14_h u :=
    mul_le_mul_of_nonneg_left hf_le_h hc
  exact (hDeltaA_bound i j).trans
    (mul_le_mul_of_nonneg_right hc_bound (abs_nonneg (A i j)))

/-- **Theorem 9.14**, LU-backward-error plus actual triangular solves with a
constant-growth final `h(γ_n)` coefficient. -/
theorem higham9_14_source_h_bound_of_LUBackwardError_fl_triangular_solves_const_gamma
    (fp : FPModel) (n : ℕ)
    (A L_hat U_hat : Fin n → Fin n → ℝ)
    (b : Fin n → ℝ)
    (c : ℝ) (hc : 0 ≤ c)
    (hn : gammaValid fp n)
    (hγ_lt_one : gamma fp n < 1)
    (hLU : LUBackwardError n A L_hat U_hat (gamma fp n))
    (hU_diag : ∀ i : Fin n, U_hat i i ≠ 0)
    (hAbsLU_le : ∀ i j : Fin n,
      ∑ k : Fin n, |L_hat i k| * |U_hat k j| ≤ c * |A i j|) :
    let y_hat := fl_forwardSub fp n L_hat b
    let x_hat := fl_backSub fp n U_hat y_hat
    ∃ DeltaA : Fin n → Fin n → ℝ,
      (∀ i j, |DeltaA i j| ≤
        c * higham9_14_h (gamma fp n) * |A i j|) ∧
      (∀ i, ∑ j : Fin n, (A i j + DeltaA i j) * x_hat j = b i) :=
  higham9_14_source_h_bound_of_LUBackwardError_fl_triangular_solves_const_gamma_le
    fp n A L_hat U_hat b c (gamma fp n) (gamma fp n) hc
    (gamma_nonneg fp hn) hγ_lt_one hn hLU le_rfl le_rfl hU_diag hAbsLU_le

/-- **Theorem 9.14**, source-model production for the final `h(u)` bound.

This wrapper instantiates equations (9.20) and (9.21) from an existing
componentwise LU backward-error certificate and the actual
`fl_forwardSub`/`fl_backSub` triangular solves, then applies the exact-growth
`|Lhat||Uhat| <= |A|` bridge to Higham's final `h(u)|A|` source bound. -/
theorem higham9_14_source_h_bound_of_LUBackwardError_fl_triangular_solves_gamma_le
    (fp : FPModel) (n : ℕ)
    (A L_hat U_hat : Fin n → Fin n → ℝ)
    (b : Fin n → ℝ)
    (ε u : ℝ) (hu : 0 ≤ u) (hu_lt_one : u < 1)
    (hn : gammaValid fp n)
    (hLU : LUBackwardError n A L_hat U_hat ε)
    (hε_le_u : ε ≤ u)
    (hγ_le_u : gamma fp n ≤ u)
    (hU_diag : ∀ i : Fin n, U_hat i i ≠ 0)
    (hAbsLU_le : ∀ i j : Fin n,
      ∑ k : Fin n, |L_hat i k| * |U_hat k j| ≤ |A i j|) :
    let y_hat := fl_forwardSub fp n L_hat b
    let x_hat := fl_backSub fp n U_hat y_hat
    ∃ DeltaA : Fin n → Fin n → ℝ,
      (∀ i j, |DeltaA i j| ≤ higham9_14_h u * |A i j|) ∧
      (∀ i, ∑ j : Fin n, (A i j + DeltaA i j) * x_hat j = b i) := by
  intro y_hat x_hat
  have hL_diag_ne : ∀ i : Fin n, L_hat i i ≠ 0 := by
    intro i
    rw [hLU.L_diag i]
    norm_num
  obtain ⟨DeltaA_LU, h20⟩ :=
    higham9_20_tridiag_lu_perturbation_model_of_LUBackwardError_le
      n A L_hat U_hat ε u hε_le_u hLU
  obtain ⟨DeltaL, DeltaU, h21_raw⟩ :=
    higham9_21_tridiag_solve_perturbation_model_of_fl_triangular_solves_gamma_le
      fp n L_hat U_hat b u hu hL_diag_ne hU_diag
      hLU.L_upper_zero hLU.U_lower_zero hn hγ_le_u
  have h21 :
      higham9_21_tridiag_solve_perturbation_model n L_hat U_hat
        y_hat x_hat b DeltaL DeltaU u := by
    simpa [y_hat, x_hat] using h21_raw
  exact higham9_14_source_h_bound_of_absLU_le_absA_and_9_20_9_21_models
    n A L_hat U_hat y_hat x_hat b u hu hu_lt_one hAbsLU_le
    DeltaA_LU DeltaL DeltaU h20 h21

/-- **Theorem 9.14**, LU-backward-error plus actual triangular solves with
Higham's final `h(γ_n)` coefficient. -/
theorem higham9_14_source_h_bound_of_LUBackwardError_fl_triangular_solves_gamma
    (fp : FPModel) (n : ℕ)
    (A L_hat U_hat : Fin n → Fin n → ℝ)
    (b : Fin n → ℝ)
    (hn : gammaValid fp n)
    (hγ_lt_one : gamma fp n < 1)
    (hLU : LUBackwardError n A L_hat U_hat (gamma fp n))
    (hU_diag : ∀ i : Fin n, U_hat i i ≠ 0)
    (hAbsLU_le : ∀ i j : Fin n,
      ∑ k : Fin n, |L_hat i k| * |U_hat k j| ≤ |A i j|) :
    let y_hat := fl_forwardSub fp n L_hat b
    let x_hat := fl_backSub fp n U_hat y_hat
    ∃ DeltaA : Fin n → Fin n → ℝ,
      (∀ i j, |DeltaA i j| ≤
        higham9_14_h (gamma fp n) * |A i j|) ∧
      (∀ i, ∑ j : Fin n, (A i j + DeltaA i j) * x_hat j = b i) :=
  higham9_14_source_h_bound_of_LUBackwardError_fl_triangular_solves_gamma_le
    fp n A L_hat U_hat b (gamma fp n) (gamma fp n)
    (gamma_nonneg fp hn) hγ_lt_one hn hLU le_rfl le_rfl hU_diag hAbsLU_le

/-- **Theorem 9.14**, exact-LU factor plus actual triangular solves for
Higham's final `h(u)` bound.

This is an exact-factor specialization of
`higham9_14_source_h_bound_of_LUBackwardError_fl_triangular_solves_gamma_le`:
an exact `LUFactSpec` supplies equation (9.20) with zero LU-factorization
coefficient, while the actual `fl_forwardSub`/`fl_backSub` calls supply the
triangular-solve model. -/
theorem higham9_14_source_h_bound_of_LUFactSpec_fl_triangular_solves_gamma_le
    (fp : FPModel) (n : ℕ)
    (A L_hat U_hat : Fin n → Fin n → ℝ)
    (b : Fin n → ℝ)
    (u : ℝ) (hu : 0 ≤ u) (hu_lt_one : u < 1)
    (hn : gammaValid fp n)
    (hLU : LUFactSpec n A L_hat U_hat)
    (hγ_le_u : gamma fp n ≤ u)
    (hU_diag : ∀ i : Fin n, U_hat i i ≠ 0)
    (hAbsLU_le : ∀ i j : Fin n,
      ∑ k : Fin n, |L_hat i k| * |U_hat k j| ≤ |A i j|) :
    let y_hat := fl_forwardSub fp n L_hat b
    let x_hat := fl_backSub fp n U_hat y_hat
    ∃ DeltaA : Fin n → Fin n → ℝ,
      (∀ i j, |DeltaA i j| ≤ higham9_14_h u * |A i j|) ∧
      (∀ i, ∑ j : Fin n, (A i j + DeltaA i j) * x_hat j = b i) :=
  higham9_14_source_h_bound_of_LUBackwardError_fl_triangular_solves_gamma_le
    fp n A L_hat U_hat b 0 u hu hu_lt_one hn
    (LUFactSpec.to_LUBackwardError_zero hLU) hu hγ_le_u hU_diag hAbsLU_le

/-- **Theorem 9.14**, exact-LU factor plus actual triangular solves with
Higham's final `h(γ_n)` coefficient. -/
theorem higham9_14_source_h_bound_of_LUFactSpec_fl_triangular_solves_gamma
    (fp : FPModel) (n : ℕ)
    (A L_hat U_hat : Fin n → Fin n → ℝ)
    (b : Fin n → ℝ)
    (hn : gammaValid fp n)
    (hγ_lt_one : gamma fp n < 1)
    (hLU : LUFactSpec n A L_hat U_hat)
    (hU_diag : ∀ i : Fin n, U_hat i i ≠ 0)
    (hAbsLU_le : ∀ i j : Fin n,
      ∑ k : Fin n, |L_hat i k| * |U_hat k j| ≤ |A i j|) :
    let y_hat := fl_forwardSub fp n L_hat b
    let x_hat := fl_backSub fp n U_hat y_hat
    ∃ DeltaA : Fin n → Fin n → ℝ,
      (∀ i j, |DeltaA i j| ≤
        higham9_14_h (gamma fp n) * |A i j|) ∧
      (∀ i, ∑ j : Fin n, (A i j + DeltaA i j) * x_hat j = b i) :=
  higham9_14_source_h_bound_of_LUFactSpec_fl_triangular_solves_gamma_le
    fp n A L_hat U_hat b (gamma fp n) (gamma_nonneg fp hn)
    hγ_lt_one hn hLU le_rfl hU_diag hAbsLU_le

/-- **Theorem 9.14**, Matrix-facing LU-backward-error plus actual triangular
solves with a constant-growth source `f(u)` coefficient. -/
theorem higham9_14_matrix_source_f_bound_of_LUBackwardError_fl_triangular_solves_gamma_le
    (fp : FPModel) (n : ℕ)
    (A L_hat U_hat : Matrix (Fin n) (Fin n) ℝ)
    (b : Fin n → ℝ)
    (c ε u : ℝ) (hu : 0 ≤ u)
    (hn : gammaValid fp n)
    (hLU : LUBackwardError n A L_hat U_hat ε)
    (hε_le_u : ε ≤ u)
    (hγ_le_u : gamma fp n ≤ u)
    (hU_diag : ∀ i : Fin n, U_hat i i ≠ 0)
    (hAbsLU_le : ∀ i j : Fin n,
      ∑ k : Fin n, |L_hat i k| * |U_hat k j| ≤ c * |A i j|) :
    let y_hat := fl_forwardSub fp n L_hat b
    let x_hat := fl_backSub fp n U_hat y_hat
    ∃ DeltaA : Matrix (Fin n) (Fin n) ℝ,
      (∀ i j, |DeltaA i j| ≤ c * higham9_14_f u * |A i j|) ∧
      Matrix.mulVec (fun i j => A i j + DeltaA i j) x_hat = b := by
  intro y_hat x_hat
  obtain ⟨DeltaA, hDeltaA_bound, hDeltaA_eq⟩ :=
    higham9_14_source_f_bound_of_LUBackwardError_fl_triangular_solves_gamma_le
      fp n A L_hat U_hat b c ε u hu hn hLU hε_le_u hγ_le_u hU_diag
      hAbsLU_le
  refine ⟨DeltaA, hDeltaA_bound, ?_⟩
  funext i
  simpa [Matrix.mulVec, dotProduct] using hDeltaA_eq i

/-- **Theorem 9.14**, Matrix-facing exact-LU factor plus actual triangular
solves with a constant-growth source `f(u)` coefficient. -/
theorem higham9_14_matrix_source_f_bound_of_LUFactSpec_fl_triangular_solves_gamma_le
    (fp : FPModel) (n : ℕ)
    (A L_hat U_hat : Matrix (Fin n) (Fin n) ℝ)
    (b : Fin n → ℝ)
    (c u : ℝ) (hu : 0 ≤ u)
    (hn : gammaValid fp n)
    (hLU : LUFactSpec n A L_hat U_hat)
    (hγ_le_u : gamma fp n ≤ u)
    (hU_diag : ∀ i : Fin n, U_hat i i ≠ 0)
    (hAbsLU_le : ∀ i j : Fin n,
      ∑ k : Fin n, |L_hat i k| * |U_hat k j| ≤ c * |A i j|) :
    let y_hat := fl_forwardSub fp n L_hat b
    let x_hat := fl_backSub fp n U_hat y_hat
    ∃ DeltaA : Matrix (Fin n) (Fin n) ℝ,
      (∀ i j, |DeltaA i j| ≤ c * higham9_14_f u * |A i j|) ∧
      Matrix.mulVec (fun i j => A i j + DeltaA i j) x_hat = b := by
  intro y_hat x_hat
  obtain ⟨DeltaA, hDeltaA_bound, hDeltaA_eq⟩ :=
    higham9_14_source_f_bound_of_LUFactSpec_fl_triangular_solves_gamma_le
      fp n A L_hat U_hat b c u hu hn hLU hγ_le_u hU_diag hAbsLU_le
  refine ⟨DeltaA, hDeltaA_bound, ?_⟩
  funext i
  simpa [Matrix.mulVec, dotProduct] using hDeltaA_eq i

/-- **Theorem 9.14**, Matrix-facing LU-backward-error plus actual triangular
solves with the final `h(u)` coefficient. -/
theorem higham9_14_matrix_source_h_bound_of_LUBackwardError_fl_triangular_solves_gamma_le
    (fp : FPModel) (n : ℕ)
    (A L_hat U_hat : Matrix (Fin n) (Fin n) ℝ)
    (b : Fin n → ℝ)
    (ε u : ℝ) (hu : 0 ≤ u) (hu_lt_one : u < 1)
    (hn : gammaValid fp n)
    (hLU : LUBackwardError n A L_hat U_hat ε)
    (hε_le_u : ε ≤ u)
    (hγ_le_u : gamma fp n ≤ u)
    (hU_diag : ∀ i : Fin n, U_hat i i ≠ 0)
    (hAbsLU_le : ∀ i j : Fin n,
      ∑ k : Fin n, |L_hat i k| * |U_hat k j| ≤ |A i j|) :
    let y_hat := fl_forwardSub fp n L_hat b
    let x_hat := fl_backSub fp n U_hat y_hat
    ∃ DeltaA : Matrix (Fin n) (Fin n) ℝ,
      (∀ i j, |DeltaA i j| ≤ higham9_14_h u * |A i j|) ∧
      Matrix.mulVec (fun i j => A i j + DeltaA i j) x_hat = b := by
  intro y_hat x_hat
  obtain ⟨DeltaA, hDeltaA_bound, hDeltaA_eq⟩ :=
    higham9_14_source_h_bound_of_LUBackwardError_fl_triangular_solves_gamma_le
      fp n A L_hat U_hat b ε u hu hu_lt_one hn hLU hε_le_u hγ_le_u
      hU_diag hAbsLU_le
  refine ⟨DeltaA, hDeltaA_bound, ?_⟩
  funext i
  simpa [Matrix.mulVec, dotProduct] using hDeltaA_eq i

/-- **Theorem 9.14**, Matrix-facing exact-LU factor plus actual triangular
solves with the final `h(u)` coefficient. -/
theorem higham9_14_matrix_source_h_bound_of_LUFactSpec_fl_triangular_solves_gamma_le
    (fp : FPModel) (n : ℕ)
    (A L_hat U_hat : Matrix (Fin n) (Fin n) ℝ)
    (b : Fin n → ℝ)
    (u : ℝ) (hu : 0 ≤ u) (hu_lt_one : u < 1)
    (hn : gammaValid fp n)
    (hLU : LUFactSpec n A L_hat U_hat)
    (hγ_le_u : gamma fp n ≤ u)
    (hU_diag : ∀ i : Fin n, U_hat i i ≠ 0)
    (hAbsLU_le : ∀ i j : Fin n,
      ∑ k : Fin n, |L_hat i k| * |U_hat k j| ≤ |A i j|) :
    let y_hat := fl_forwardSub fp n L_hat b
    let x_hat := fl_backSub fp n U_hat y_hat
    ∃ DeltaA : Matrix (Fin n) (Fin n) ℝ,
      (∀ i j, |DeltaA i j| ≤ higham9_14_h u * |A i j|) ∧
      Matrix.mulVec (fun i j => A i j + DeltaA i j) x_hat = b := by
  intro y_hat x_hat
  obtain ⟨DeltaA, hDeltaA_bound, hDeltaA_eq⟩ :=
    higham9_14_source_h_bound_of_LUFactSpec_fl_triangular_solves_gamma_le
      fp n A L_hat U_hat b u hu hu_lt_one hn hLU hγ_le_u hU_diag
      hAbsLU_le
  refine ⟨DeltaA, hDeltaA_bound, ?_⟩
  funext i
  simpa [Matrix.mulVec, dotProduct] using hDeltaA_eq i

/-- **Theorem 9.14**, Matrix-facing LU-backward-error plus actual triangular
solves with the natural source `f(γ_n)` coefficient. -/
theorem higham9_14_matrix_source_f_bound_of_LUBackwardError_fl_triangular_solves_gamma
    (fp : FPModel) (n : ℕ)
    (A L_hat U_hat : Matrix (Fin n) (Fin n) ℝ)
    (b : Fin n → ℝ)
    (c : ℝ)
    (hn : gammaValid fp n)
    (hLU : LUBackwardError n A L_hat U_hat (gamma fp n))
    (hU_diag : ∀ i : Fin n, U_hat i i ≠ 0)
    (hAbsLU_le : ∀ i j : Fin n,
      ∑ k : Fin n, |L_hat i k| * |U_hat k j| ≤ c * |A i j|) :
    let y_hat := fl_forwardSub fp n L_hat b
    let x_hat := fl_backSub fp n U_hat y_hat
    ∃ DeltaA : Matrix (Fin n) (Fin n) ℝ,
      (∀ i j, |DeltaA i j| ≤
        c * higham9_14_f (gamma fp n) * |A i j|) ∧
      Matrix.mulVec (fun i j => A i j + DeltaA i j) x_hat = b :=
  higham9_14_matrix_source_f_bound_of_LUBackwardError_fl_triangular_solves_gamma_le
    fp n A L_hat U_hat b c (gamma fp n) (gamma fp n)
    (gamma_nonneg fp hn) hn hLU le_rfl le_rfl hU_diag hAbsLU_le

/-- **Theorem 9.14**, Matrix-facing exact-LU factor plus actual triangular
solves with the natural source `f(γ_n)` coefficient. -/
theorem higham9_14_matrix_source_f_bound_of_LUFactSpec_fl_triangular_solves_gamma
    (fp : FPModel) (n : ℕ)
    (A L_hat U_hat : Matrix (Fin n) (Fin n) ℝ)
    (b : Fin n → ℝ)
    (c : ℝ)
    (hn : gammaValid fp n)
    (hLU : LUFactSpec n A L_hat U_hat)
    (hU_diag : ∀ i : Fin n, U_hat i i ≠ 0)
    (hAbsLU_le : ∀ i j : Fin n,
      ∑ k : Fin n, |L_hat i k| * |U_hat k j| ≤ c * |A i j|) :
    let y_hat := fl_forwardSub fp n L_hat b
    let x_hat := fl_backSub fp n U_hat y_hat
    ∃ DeltaA : Matrix (Fin n) (Fin n) ℝ,
      (∀ i j, |DeltaA i j| ≤
        c * higham9_14_f (gamma fp n) * |A i j|) ∧
      Matrix.mulVec (fun i j => A i j + DeltaA i j) x_hat = b :=
  higham9_14_matrix_source_f_bound_of_LUFactSpec_fl_triangular_solves_gamma_le
    fp n A L_hat U_hat b c (gamma fp n) (gamma_nonneg fp hn) hn hLU
    le_rfl hU_diag hAbsLU_le

/-- **Theorem 9.14**, Matrix-facing LU-backward-error plus actual triangular
solves with Higham's final `h(γ_n)` coefficient. -/
theorem higham9_14_matrix_source_h_bound_of_LUBackwardError_fl_triangular_solves_gamma
    (fp : FPModel) (n : ℕ)
    (A L_hat U_hat : Matrix (Fin n) (Fin n) ℝ)
    (b : Fin n → ℝ)
    (hn : gammaValid fp n)
    (hγ_lt_one : gamma fp n < 1)
    (hLU : LUBackwardError n A L_hat U_hat (gamma fp n))
    (hU_diag : ∀ i : Fin n, U_hat i i ≠ 0)
    (hAbsLU_le : ∀ i j : Fin n,
      ∑ k : Fin n, |L_hat i k| * |U_hat k j| ≤ |A i j|) :
    let y_hat := fl_forwardSub fp n L_hat b
    let x_hat := fl_backSub fp n U_hat y_hat
    ∃ DeltaA : Matrix (Fin n) (Fin n) ℝ,
      (∀ i j, |DeltaA i j| ≤
        higham9_14_h (gamma fp n) * |A i j|) ∧
      Matrix.mulVec (fun i j => A i j + DeltaA i j) x_hat = b :=
  higham9_14_matrix_source_h_bound_of_LUBackwardError_fl_triangular_solves_gamma_le
    fp n A L_hat U_hat b (gamma fp n) (gamma fp n)
    (gamma_nonneg fp hn) hγ_lt_one hn hLU le_rfl le_rfl hU_diag hAbsLU_le

/-- **Theorem 9.14**, Matrix-facing exact-LU factor plus actual triangular
solves with Higham's final `h(γ_n)` coefficient. -/
theorem higham9_14_matrix_source_h_bound_of_LUFactSpec_fl_triangular_solves_gamma
    (fp : FPModel) (n : ℕ)
    (A L_hat U_hat : Matrix (Fin n) (Fin n) ℝ)
    (b : Fin n → ℝ)
    (hn : gammaValid fp n)
    (hγ_lt_one : gamma fp n < 1)
    (hLU : LUFactSpec n A L_hat U_hat)
    (hU_diag : ∀ i : Fin n, U_hat i i ≠ 0)
    (hAbsLU_le : ∀ i j : Fin n,
      ∑ k : Fin n, |L_hat i k| * |U_hat k j| ≤ |A i j|) :
    let y_hat := fl_forwardSub fp n L_hat b
    let x_hat := fl_backSub fp n U_hat y_hat
    ∃ DeltaA : Matrix (Fin n) (Fin n) ℝ,
      (∀ i j, |DeltaA i j| ≤
        higham9_14_h (gamma fp n) * |A i j|) ∧
      Matrix.mulVec (fun i j => A i j + DeltaA i j) x_hat = b :=
  higham9_14_matrix_source_h_bound_of_LUFactSpec_fl_triangular_solves_gamma_le
    fp n A L_hat U_hat b (gamma fp n) (gamma_nonneg fp hn)
    hγ_lt_one hn hLU le_rfl hU_diag hAbsLU_le

/-- **Theorem 9.14**, Matrix-facing LU-backward-error plus actual triangular
solves with a constant-growth final `h(u)` coefficient. -/
theorem higham9_14_matrix_source_h_bound_of_LUBackwardError_fl_triangular_solves_const_gamma_le
    (fp : FPModel) (n : ℕ)
    (A L_hat U_hat : Matrix (Fin n) (Fin n) ℝ)
    (b : Fin n → ℝ)
    (c ε u : ℝ) (hc : 0 ≤ c) (hu : 0 ≤ u) (hu_lt_one : u < 1)
    (hn : gammaValid fp n)
    (hLU : LUBackwardError n A L_hat U_hat ε)
    (hε_le_u : ε ≤ u)
    (hγ_le_u : gamma fp n ≤ u)
    (hU_diag : ∀ i : Fin n, U_hat i i ≠ 0)
    (hAbsLU_le : ∀ i j : Fin n,
      ∑ k : Fin n, |L_hat i k| * |U_hat k j| ≤ c * |A i j|) :
    let y_hat := fl_forwardSub fp n L_hat b
    let x_hat := fl_backSub fp n U_hat y_hat
    ∃ DeltaA : Matrix (Fin n) (Fin n) ℝ,
      (∀ i j, |DeltaA i j| ≤ c * higham9_14_h u * |A i j|) ∧
      Matrix.mulVec (fun i j => A i j + DeltaA i j) x_hat = b := by
  intro y_hat x_hat
  obtain ⟨DeltaA, hDeltaA_bound, hDeltaA_eq⟩ :=
    higham9_14_source_h_bound_of_LUBackwardError_fl_triangular_solves_const_gamma_le
      fp n A L_hat U_hat b c ε u hc hu hu_lt_one hn hLU hε_le_u
      hγ_le_u hU_diag hAbsLU_le
  refine ⟨DeltaA, hDeltaA_bound, ?_⟩
  funext i
  simpa [Matrix.mulVec, dotProduct] using hDeltaA_eq i

/-- **Theorem 9.14**, Matrix-facing exact-LU factor plus actual triangular
solves with a constant-growth final `h(u)` coefficient. -/
theorem higham9_14_matrix_source_h_bound_of_LUFactSpec_fl_triangular_solves_const_gamma_le
    (fp : FPModel) (n : ℕ)
    (A L_hat U_hat : Matrix (Fin n) (Fin n) ℝ)
    (b : Fin n → ℝ)
    (c u : ℝ) (hc : 0 ≤ c) (hu : 0 ≤ u) (hu_lt_one : u < 1)
    (hn : gammaValid fp n)
    (hLU : LUFactSpec n A L_hat U_hat)
    (hγ_le_u : gamma fp n ≤ u)
    (hU_diag : ∀ i : Fin n, U_hat i i ≠ 0)
    (hAbsLU_le : ∀ i j : Fin n,
      ∑ k : Fin n, |L_hat i k| * |U_hat k j| ≤ c * |A i j|) :
    let y_hat := fl_forwardSub fp n L_hat b
    let x_hat := fl_backSub fp n U_hat y_hat
    ∃ DeltaA : Matrix (Fin n) (Fin n) ℝ,
      (∀ i j, |DeltaA i j| ≤ c * higham9_14_h u * |A i j|) ∧
      Matrix.mulVec (fun i j => A i j + DeltaA i j) x_hat = b := by
  intro y_hat x_hat
  obtain ⟨DeltaA, hDeltaA_bound, hDeltaA_eq⟩ :=
    higham9_14_source_h_bound_of_LUFactSpec_fl_triangular_solves_const_gamma_le
      fp n A L_hat U_hat b c u hc hu hu_lt_one hn hLU hγ_le_u
      hU_diag hAbsLU_le
  refine ⟨DeltaA, hDeltaA_bound, ?_⟩
  funext i
  simpa [Matrix.mulVec, dotProduct] using hDeltaA_eq i

/-- **Theorem 9.14**, Matrix-facing LU-backward-error plus actual triangular
solves with a constant-growth final `h(γ_n)` coefficient. -/
theorem higham9_14_matrix_source_h_bound_of_LUBackwardError_fl_triangular_solves_const_gamma
    (fp : FPModel) (n : ℕ)
    (A L_hat U_hat : Matrix (Fin n) (Fin n) ℝ)
    (b : Fin n → ℝ)
    (c : ℝ) (hc : 0 ≤ c)
    (hn : gammaValid fp n)
    (hγ_lt_one : gamma fp n < 1)
    (hLU : LUBackwardError n A L_hat U_hat (gamma fp n))
    (hU_diag : ∀ i : Fin n, U_hat i i ≠ 0)
    (hAbsLU_le : ∀ i j : Fin n,
      ∑ k : Fin n, |L_hat i k| * |U_hat k j| ≤ c * |A i j|) :
    let y_hat := fl_forwardSub fp n L_hat b
    let x_hat := fl_backSub fp n U_hat y_hat
    ∃ DeltaA : Matrix (Fin n) (Fin n) ℝ,
      (∀ i j, |DeltaA i j| ≤
        c * higham9_14_h (gamma fp n) * |A i j|) ∧
      Matrix.mulVec (fun i j => A i j + DeltaA i j) x_hat = b :=
  higham9_14_matrix_source_h_bound_of_LUBackwardError_fl_triangular_solves_const_gamma_le
    fp n A L_hat U_hat b c (gamma fp n) (gamma fp n) hc
    (gamma_nonneg fp hn) hγ_lt_one hn hLU le_rfl le_rfl hU_diag hAbsLU_le

/-- **Theorem 9.14**, Matrix-facing exact-LU factor plus actual triangular
solves with a constant-growth final `h(γ_n)` coefficient. -/
theorem higham9_14_matrix_source_h_bound_of_LUFactSpec_fl_triangular_solves_const_gamma
    (fp : FPModel) (n : ℕ)
    (A L_hat U_hat : Matrix (Fin n) (Fin n) ℝ)
    (b : Fin n → ℝ)
    (c : ℝ) (hc : 0 ≤ c)
    (hn : gammaValid fp n)
    (hγ_lt_one : gamma fp n < 1)
    (hLU : LUFactSpec n A L_hat U_hat)
    (hU_diag : ∀ i : Fin n, U_hat i i ≠ 0)
    (hAbsLU_le : ∀ i j : Fin n,
      ∑ k : Fin n, |L_hat i k| * |U_hat k j| ≤ c * |A i j|) :
    let y_hat := fl_forwardSub fp n L_hat b
    let x_hat := fl_backSub fp n U_hat y_hat
    ∃ DeltaA : Matrix (Fin n) (Fin n) ℝ,
      (∀ i j, |DeltaA i j| ≤
        c * higham9_14_h (gamma fp n) * |A i j|) ∧
      Matrix.mulVec (fun i j => A i j + DeltaA i j) x_hat = b :=
  higham9_14_matrix_source_h_bound_of_LUFactSpec_fl_triangular_solves_const_gamma_le
    fp n A L_hat U_hat b c (gamma fp n) hc (gamma_nonneg fp hn)
    hγ_lt_one hn hLU le_rfl hU_diag hAbsLU_le

/-- **Theorem 9.14**, Matrix-facing LU-backward-error plus actual triangular
solves with optimal growth and source `f(u)` coefficient. -/
theorem higham9_14_matrix_source_f_bound_of_LUBackwardError_fl_triangular_solves_absLU_le_absA_gamma_le
    (fp : FPModel) (n : ℕ)
    (A L_hat U_hat : Matrix (Fin n) (Fin n) ℝ)
    (b : Fin n → ℝ)
    (ε u : ℝ) (hu : 0 ≤ u)
    (hn : gammaValid fp n)
    (hLU : LUBackwardError n A L_hat U_hat ε)
    (hε_le_u : ε ≤ u)
    (hγ_le_u : gamma fp n ≤ u)
    (hU_diag : ∀ i : Fin n, U_hat i i ≠ 0)
    (hAbsLU_le : ∀ i j : Fin n,
      ∑ k : Fin n, |L_hat i k| * |U_hat k j| ≤ |A i j|) :
    let y_hat := fl_forwardSub fp n L_hat b
    let x_hat := fl_backSub fp n U_hat y_hat
    ∃ DeltaA : Matrix (Fin n) (Fin n) ℝ,
      (∀ i j, |DeltaA i j| ≤ higham9_14_f u * |A i j|) ∧
      Matrix.mulVec (fun i j => A i j + DeltaA i j) x_hat = b := by
  simpa [one_mul] using
    (higham9_14_matrix_source_f_bound_of_LUBackwardError_fl_triangular_solves_gamma_le
      fp n A L_hat U_hat b 1 ε u hu hn hLU hε_le_u hγ_le_u hU_diag
      (fun i j => by simpa [one_mul] using hAbsLU_le i j))

/-- **Theorem 9.14**, Matrix-facing LU-backward-error plus actual triangular
solves with optimal growth and the natural source `f(γ_n)` coefficient. -/
theorem higham9_14_matrix_source_f_bound_of_LUBackwardError_fl_triangular_solves_absLU_le_absA_gamma
    (fp : FPModel) (n : ℕ)
    (A L_hat U_hat : Matrix (Fin n) (Fin n) ℝ)
    (b : Fin n → ℝ)
    (hn : gammaValid fp n)
    (hLU : LUBackwardError n A L_hat U_hat (gamma fp n))
    (hU_diag : ∀ i : Fin n, U_hat i i ≠ 0)
    (hAbsLU_le : ∀ i j : Fin n,
      ∑ k : Fin n, |L_hat i k| * |U_hat k j| ≤ |A i j|) :
    let y_hat := fl_forwardSub fp n L_hat b
    let x_hat := fl_backSub fp n U_hat y_hat
    ∃ DeltaA : Matrix (Fin n) (Fin n) ℝ,
      (∀ i j, |DeltaA i j| ≤
        higham9_14_f (gamma fp n) * |A i j|) ∧
      Matrix.mulVec (fun i j => A i j + DeltaA i j) x_hat = b := by
  simpa [one_mul] using
    (higham9_14_matrix_source_f_bound_of_LUBackwardError_fl_triangular_solves_gamma
      fp n A L_hat U_hat b 1 hn hLU hU_diag
      (fun i j => by simpa [one_mul] using hAbsLU_le i j))

/-- **Theorem 9.14**, Matrix-facing exact-LU factor plus actual triangular
solves with optimal growth and source `f(u)` coefficient. -/
theorem higham9_14_matrix_source_f_bound_of_LUFactSpec_fl_triangular_solves_absLU_le_absA_gamma_le
    (fp : FPModel) (n : ℕ)
    (A L_hat U_hat : Matrix (Fin n) (Fin n) ℝ)
    (b : Fin n → ℝ)
    (u : ℝ) (hu : 0 ≤ u)
    (hn : gammaValid fp n)
    (hLU : LUFactSpec n A L_hat U_hat)
    (hγ_le_u : gamma fp n ≤ u)
    (hU_diag : ∀ i : Fin n, U_hat i i ≠ 0)
    (hAbsLU_le : ∀ i j : Fin n,
      ∑ k : Fin n, |L_hat i k| * |U_hat k j| ≤ |A i j|) :
    let y_hat := fl_forwardSub fp n L_hat b
    let x_hat := fl_backSub fp n U_hat y_hat
    ∃ DeltaA : Matrix (Fin n) (Fin n) ℝ,
      (∀ i j, |DeltaA i j| ≤ higham9_14_f u * |A i j|) ∧
      Matrix.mulVec (fun i j => A i j + DeltaA i j) x_hat = b := by
  simpa [one_mul] using
    (higham9_14_matrix_source_f_bound_of_LUFactSpec_fl_triangular_solves_gamma_le
      fp n A L_hat U_hat b 1 u hu hn hLU hγ_le_u hU_diag
      (fun i j => by simpa [one_mul] using hAbsLU_le i j))

/-- **Theorem 9.14**, Matrix-facing exact-LU factor plus actual triangular
solves with optimal growth and the natural source `f(γ_n)` coefficient. -/
theorem higham9_14_matrix_source_f_bound_of_LUFactSpec_fl_triangular_solves_absLU_le_absA_gamma
    (fp : FPModel) (n : ℕ)
    (A L_hat U_hat : Matrix (Fin n) (Fin n) ℝ)
    (b : Fin n → ℝ)
    (hn : gammaValid fp n)
    (hLU : LUFactSpec n A L_hat U_hat)
    (hU_diag : ∀ i : Fin n, U_hat i i ≠ 0)
    (hAbsLU_le : ∀ i j : Fin n,
      ∑ k : Fin n, |L_hat i k| * |U_hat k j| ≤ |A i j|) :
    let y_hat := fl_forwardSub fp n L_hat b
    let x_hat := fl_backSub fp n U_hat y_hat
    ∃ DeltaA : Matrix (Fin n) (Fin n) ℝ,
      (∀ i j, |DeltaA i j| ≤
        higham9_14_f (gamma fp n) * |A i j|) ∧
      Matrix.mulVec (fun i j => A i j + DeltaA i j) x_hat = b := by
  simpa [one_mul] using
    (higham9_14_matrix_source_f_bound_of_LUFactSpec_fl_triangular_solves_gamma
      fp n A L_hat U_hat b 1 hn hLU hU_diag
      (fun i j => by simpa [one_mul] using hAbsLU_le i j))

/-- **Theorem 9.14**, Matrix-facing LU-backward-error plus actual triangular
solves with optimal growth and final `h(u)` coefficient. -/
theorem higham9_14_matrix_source_h_bound_of_LUBackwardError_fl_triangular_solves_absLU_le_absA_gamma_le
    (fp : FPModel) (n : ℕ)
    (A L_hat U_hat : Matrix (Fin n) (Fin n) ℝ)
    (b : Fin n → ℝ)
    (ε u : ℝ) (hu : 0 ≤ u) (hu_lt_one : u < 1)
    (hn : gammaValid fp n)
    (hLU : LUBackwardError n A L_hat U_hat ε)
    (hε_le_u : ε ≤ u)
    (hγ_le_u : gamma fp n ≤ u)
    (hU_diag : ∀ i : Fin n, U_hat i i ≠ 0)
    (hAbsLU_le : ∀ i j : Fin n,
      ∑ k : Fin n, |L_hat i k| * |U_hat k j| ≤ |A i j|) :
    let y_hat := fl_forwardSub fp n L_hat b
    let x_hat := fl_backSub fp n U_hat y_hat
    ∃ DeltaA : Matrix (Fin n) (Fin n) ℝ,
      (∀ i j, |DeltaA i j| ≤ higham9_14_h u * |A i j|) ∧
      Matrix.mulVec (fun i j => A i j + DeltaA i j) x_hat = b :=
  higham9_14_matrix_source_h_bound_of_LUBackwardError_fl_triangular_solves_gamma_le
    fp n A L_hat U_hat b ε u hu hu_lt_one hn hLU hε_le_u hγ_le_u
    hU_diag hAbsLU_le

/-- **Theorem 9.14**, Matrix-facing LU-backward-error plus actual triangular
solves with optimal growth and final `h(γ_n)` coefficient. -/
theorem higham9_14_matrix_source_h_bound_of_LUBackwardError_fl_triangular_solves_absLU_le_absA_gamma
    (fp : FPModel) (n : ℕ)
    (A L_hat U_hat : Matrix (Fin n) (Fin n) ℝ)
    (b : Fin n → ℝ)
    (hn : gammaValid fp n)
    (hγ_lt_one : gamma fp n < 1)
    (hLU : LUBackwardError n A L_hat U_hat (gamma fp n))
    (hU_diag : ∀ i : Fin n, U_hat i i ≠ 0)
    (hAbsLU_le : ∀ i j : Fin n,
      ∑ k : Fin n, |L_hat i k| * |U_hat k j| ≤ |A i j|) :
    let y_hat := fl_forwardSub fp n L_hat b
    let x_hat := fl_backSub fp n U_hat y_hat
    ∃ DeltaA : Matrix (Fin n) (Fin n) ℝ,
      (∀ i j, |DeltaA i j| ≤
        higham9_14_h (gamma fp n) * |A i j|) ∧
      Matrix.mulVec (fun i j => A i j + DeltaA i j) x_hat = b :=
  higham9_14_matrix_source_h_bound_of_LUBackwardError_fl_triangular_solves_gamma
    fp n A L_hat U_hat b hn hγ_lt_one hLU hU_diag hAbsLU_le

/-- **Theorem 9.14**, Matrix-facing exact-LU factor plus actual triangular
solves with optimal growth and final `h(u)` coefficient. -/
theorem higham9_14_matrix_source_h_bound_of_LUFactSpec_fl_triangular_solves_absLU_le_absA_gamma_le
    (fp : FPModel) (n : ℕ)
    (A L_hat U_hat : Matrix (Fin n) (Fin n) ℝ)
    (b : Fin n → ℝ)
    (u : ℝ) (hu : 0 ≤ u) (hu_lt_one : u < 1)
    (hn : gammaValid fp n)
    (hLU : LUFactSpec n A L_hat U_hat)
    (hγ_le_u : gamma fp n ≤ u)
    (hU_diag : ∀ i : Fin n, U_hat i i ≠ 0)
    (hAbsLU_le : ∀ i j : Fin n,
      ∑ k : Fin n, |L_hat i k| * |U_hat k j| ≤ |A i j|) :
    let y_hat := fl_forwardSub fp n L_hat b
    let x_hat := fl_backSub fp n U_hat y_hat
    ∃ DeltaA : Matrix (Fin n) (Fin n) ℝ,
      (∀ i j, |DeltaA i j| ≤ higham9_14_h u * |A i j|) ∧
      Matrix.mulVec (fun i j => A i j + DeltaA i j) x_hat = b :=
  higham9_14_matrix_source_h_bound_of_LUFactSpec_fl_triangular_solves_gamma_le
    fp n A L_hat U_hat b u hu hu_lt_one hn hLU hγ_le_u hU_diag hAbsLU_le

/-- **Theorem 9.14**, Matrix-facing exact-LU factor plus actual triangular
solves with optimal growth and final `h(γ_n)` coefficient. -/
theorem higham9_14_matrix_source_h_bound_of_LUFactSpec_fl_triangular_solves_absLU_le_absA_gamma
    (fp : FPModel) (n : ℕ)
    (A L_hat U_hat : Matrix (Fin n) (Fin n) ℝ)
    (b : Fin n → ℝ)
    (hn : gammaValid fp n)
    (hγ_lt_one : gamma fp n < 1)
    (hLU : LUFactSpec n A L_hat U_hat)
    (hU_diag : ∀ i : Fin n, U_hat i i ≠ 0)
    (hAbsLU_le : ∀ i j : Fin n,
      ∑ k : Fin n, |L_hat i k| * |U_hat k j| ≤ |A i j|) :
    let y_hat := fl_forwardSub fp n L_hat b
    let x_hat := fl_backSub fp n U_hat y_hat
    ∃ DeltaA : Matrix (Fin n) (Fin n) ℝ,
      (∀ i j, |DeltaA i j| ≤
        higham9_14_h (gamma fp n) * |A i j|) ∧
      Matrix.mulVec (fun i j => A i j + DeltaA i j) x_hat = b :=
  higham9_14_matrix_source_h_bound_of_LUFactSpec_fl_triangular_solves_gamma
    fp n A L_hat U_hat b hn hγ_lt_one hLU hU_diag hAbsLU_le

/-- **Theorem 9.14**, LU-backward-error plus actual triangular solves with
optimal growth and final `h(u)` coefficient.

This is the explicit `|Lhat||Uhat| <= |A|` alias of
`higham9_14_source_h_bound_of_LUBackwardError_fl_triangular_solves_gamma_le`,
matching the corresponding source-`f` surface. -/
theorem higham9_14_source_h_bound_of_LUBackwardError_fl_triangular_solves_absLU_le_absA_gamma_le
    (fp : FPModel) (n : ℕ)
    (A L_hat U_hat : Fin n → Fin n → ℝ)
    (b : Fin n → ℝ)
    (ε u : ℝ) (hu : 0 ≤ u) (hu_lt_one : u < 1)
    (hn : gammaValid fp n)
    (hLU : LUBackwardError n A L_hat U_hat ε)
    (hε_le_u : ε ≤ u)
    (hγ_le_u : gamma fp n ≤ u)
    (hU_diag : ∀ i : Fin n, U_hat i i ≠ 0)
    (hAbsLU_le : ∀ i j : Fin n,
      ∑ k : Fin n, |L_hat i k| * |U_hat k j| ≤ |A i j|) :
    let y_hat := fl_forwardSub fp n L_hat b
    let x_hat := fl_backSub fp n U_hat y_hat
    ∃ DeltaA : Fin n → Fin n → ℝ,
      (∀ i j, |DeltaA i j| ≤ higham9_14_h u * |A i j|) ∧
      (∀ i, ∑ j : Fin n, (A i j + DeltaA i j) * x_hat j = b i) :=
  higham9_14_source_h_bound_of_LUBackwardError_fl_triangular_solves_gamma_le
    fp n A L_hat U_hat b ε u hu hu_lt_one hn hLU
    hε_le_u hγ_le_u hU_diag hAbsLU_le

/-- **Theorem 9.14**, LU-backward-error plus actual triangular solves with
optimal growth and final `h(γ_n)` coefficient. -/
theorem higham9_14_source_h_bound_of_LUBackwardError_fl_triangular_solves_absLU_le_absA_gamma
    (fp : FPModel) (n : ℕ)
    (A L_hat U_hat : Fin n → Fin n → ℝ)
    (b : Fin n → ℝ)
    (hn : gammaValid fp n)
    (hγ_lt_one : gamma fp n < 1)
    (hLU : LUBackwardError n A L_hat U_hat (gamma fp n))
    (hU_diag : ∀ i : Fin n, U_hat i i ≠ 0)
    (hAbsLU_le : ∀ i j : Fin n,
      ∑ k : Fin n, |L_hat i k| * |U_hat k j| ≤ |A i j|) :
    let y_hat := fl_forwardSub fp n L_hat b
    let x_hat := fl_backSub fp n U_hat y_hat
    ∃ DeltaA : Fin n → Fin n → ℝ,
      (∀ i j, |DeltaA i j| ≤
        higham9_14_h (gamma fp n) * |A i j|) ∧
      (∀ i, ∑ j : Fin n, (A i j + DeltaA i j) * x_hat j = b i) :=
  higham9_14_source_h_bound_of_LUBackwardError_fl_triangular_solves_gamma
    fp n A L_hat U_hat b hn hγ_lt_one hLU hU_diag hAbsLU_le

/-- **Theorem 9.14**, exact-LU factor plus actual triangular solves with
optimal growth and final `h(u)` coefficient. -/
theorem higham9_14_source_h_bound_of_LUFactSpec_fl_triangular_solves_absLU_le_absA_gamma_le
    (fp : FPModel) (n : ℕ)
    (A L_hat U_hat : Fin n → Fin n → ℝ)
    (b : Fin n → ℝ)
    (u : ℝ) (hu : 0 ≤ u) (hu_lt_one : u < 1)
    (hn : gammaValid fp n)
    (hLU : LUFactSpec n A L_hat U_hat)
    (hγ_le_u : gamma fp n ≤ u)
    (hU_diag : ∀ i : Fin n, U_hat i i ≠ 0)
    (hAbsLU_le : ∀ i j : Fin n,
      ∑ k : Fin n, |L_hat i k| * |U_hat k j| ≤ |A i j|) :
    let y_hat := fl_forwardSub fp n L_hat b
    let x_hat := fl_backSub fp n U_hat y_hat
    ∃ DeltaA : Fin n → Fin n → ℝ,
      (∀ i j, |DeltaA i j| ≤ higham9_14_h u * |A i j|) ∧
      (∀ i, ∑ j : Fin n, (A i j + DeltaA i j) * x_hat j = b i) :=
  higham9_14_source_h_bound_of_LUFactSpec_fl_triangular_solves_gamma_le
    fp n A L_hat U_hat b u hu hu_lt_one hn hLU hγ_le_u hU_diag hAbsLU_le

/-- **Theorem 9.14**, exact-LU factor plus actual triangular solves with
optimal growth and final `h(γ_n)` coefficient. -/
theorem higham9_14_source_h_bound_of_LUFactSpec_fl_triangular_solves_absLU_le_absA_gamma
    (fp : FPModel) (n : ℕ)
    (A L_hat U_hat : Fin n → Fin n → ℝ)
    (b : Fin n → ℝ)
    (hn : gammaValid fp n)
    (hγ_lt_one : gamma fp n < 1)
    (hLU : LUFactSpec n A L_hat U_hat)
    (hU_diag : ∀ i : Fin n, U_hat i i ≠ 0)
    (hAbsLU_le : ∀ i j : Fin n,
      ∑ k : Fin n, |L_hat i k| * |U_hat k j| ≤ |A i j|) :
    let y_hat := fl_forwardSub fp n L_hat b
    let x_hat := fl_backSub fp n U_hat y_hat
    ∃ DeltaA : Fin n → Fin n → ℝ,
      (∀ i j, |DeltaA i j| ≤
        higham9_14_h (gamma fp n) * |A i j|) ∧
      (∀ i, ∑ j : Fin n, (A i j + DeltaA i j) * x_hat j = b i) :=
  higham9_14_source_h_bound_of_LUFactSpec_fl_triangular_solves_gamma
    fp n A L_hat U_hat b hn hγ_lt_one hLU hU_diag hAbsLU_le

/-- **Theorem 9.14**, dense Doolittle certificate plus actual triangular solves.

This is the source-facing `f(u)` specialization of
`higham9_14_source_f_bound_of_LUBackwardError_fl_triangular_solves_gamma_le`
for a literal Algorithm 9.2 square dense-loop certificate.  The coefficient
weakening `γ_n <= u` is explicit, matching the source statement's printed
unit-roundoff coefficient. -/
theorem higham9_14_source_f_bound_of_DoolittleDenseLoopCertificate_fl_triangular_solves_gamma_le
    (fp : FPModel) (n : ℕ)
    (A L_hat U_hat : Fin n → Fin n → ℝ)
    (b : Fin n → ℝ)
    (c u : ℝ) (hu : 0 ≤ u)
    (hn : gammaValid fp n)
    (hC : higham9_2_DoolittleDenseLoopCertificate n A L_hat U_hat fp)
    (hγ_le_u : gamma fp n ≤ u)
    (hU_diag : ∀ i : Fin n, U_hat i i ≠ 0)
    (hAbsLU_le : ∀ i j : Fin n,
      ∑ k : Fin n, |L_hat i k| * |U_hat k j| ≤ c * |A i j|) :
    let y_hat := fl_forwardSub fp n L_hat b
    let x_hat := fl_backSub fp n U_hat y_hat
    ∃ DeltaA : Fin n → Fin n → ℝ,
      (∀ i j, |DeltaA i j| ≤ c * higham9_14_f u * |A i j|) ∧
      (∀ i, ∑ j : Fin n, (A i j + DeltaA i j) * x_hat j = b i) :=
  higham9_14_source_f_bound_of_LUBackwardError_fl_triangular_solves_gamma_le
    fp n A L_hat U_hat b c (gamma fp n) u hu hn
    (DoolittleDenseLoopCertificate.to_LUBackwardError hC hn)
    hγ_le_u hγ_le_u hU_diag hAbsLU_le

/-- **Theorem 9.14**, absolute-budget Doolittle certificate plus actual
triangular solves.

This exposes the lower absolute-budget Algorithm 9.2 certificate layer at the
same source-facing `f(u)` tridiagonal-solve bound. -/
theorem higham9_14_source_f_bound_of_DoolittleDenseLoopAbsBudgetCertificate_fl_triangular_solves_gamma_le
    (fp : FPModel) (n : ℕ)
    (A L_hat U_hat : Fin n → Fin n → ℝ)
    (b : Fin n → ℝ)
    (BU BL : Fin n → Fin n → ℝ)
    (c u : ℝ) (hu : 0 ≤ u)
    (hn : gammaValid fp n)
    (hC : higham9_2_DoolittleDenseLoopAbsBudgetCertificate n
      A L_hat U_hat fp BU BL)
    (hγ_le_u : gamma fp n ≤ u)
    (hU_diag : ∀ i : Fin n, U_hat i i ≠ 0)
    (hAbsLU_le : ∀ i j : Fin n,
      ∑ k : Fin n, |L_hat i k| * |U_hat k j| ≤ c * |A i j|) :
    let y_hat := fl_forwardSub fp n L_hat b
    let x_hat := fl_backSub fp n U_hat y_hat
    ∃ DeltaA : Fin n → Fin n → ℝ,
      (∀ i j, |DeltaA i j| ≤ c * higham9_14_f u * |A i j|) ∧
      (∀ i, ∑ j : Fin n, (A i j + DeltaA i j) * x_hat j = b i) :=
  higham9_14_source_f_bound_of_LUBackwardError_fl_triangular_solves_gamma_le
    fp n A L_hat U_hat b c (gamma fp n) u hu hn
    (DoolittleDenseLoopAbsBudgetCertificate.to_LUBackwardError hC hn)
    hγ_le_u hγ_le_u hU_diag hAbsLU_le

/-- **Theorem 9.14**, dense Doolittle certificate with the final `h(u)` bound.

This is the exact-growth `|Lhat||Uhat| <= |A|` source-model specialization
for a literal Algorithm 9.2 square dense-loop certificate and the actual
`fl_forwardSub`/`fl_backSub` triangular solves. -/
theorem higham9_14_source_h_bound_of_DoolittleDenseLoopCertificate_fl_triangular_solves_gamma_le
    (fp : FPModel) (n : ℕ)
    (A L_hat U_hat : Fin n → Fin n → ℝ)
    (b : Fin n → ℝ)
    (u : ℝ) (hu : 0 ≤ u) (hu_lt_one : u < 1)
    (hn : gammaValid fp n)
    (hC : higham9_2_DoolittleDenseLoopCertificate n A L_hat U_hat fp)
    (hγ_le_u : gamma fp n ≤ u)
    (hU_diag : ∀ i : Fin n, U_hat i i ≠ 0)
    (hAbsLU_le : ∀ i j : Fin n,
      ∑ k : Fin n, |L_hat i k| * |U_hat k j| ≤ |A i j|) :
    let y_hat := fl_forwardSub fp n L_hat b
    let x_hat := fl_backSub fp n U_hat y_hat
    ∃ DeltaA : Fin n → Fin n → ℝ,
      (∀ i j, |DeltaA i j| ≤ higham9_14_h u * |A i j|) ∧
      (∀ i, ∑ j : Fin n, (A i j + DeltaA i j) * x_hat j = b i) :=
  higham9_14_source_h_bound_of_LUBackwardError_fl_triangular_solves_gamma_le
    fp n A L_hat U_hat b (gamma fp n) u hu hu_lt_one hn
    (DoolittleDenseLoopCertificate.to_LUBackwardError hC hn)
    hγ_le_u hγ_le_u hU_diag hAbsLU_le

/-- **Theorem 9.14**, absolute-budget Doolittle certificate with the final
`h(u)` bound.

This is the exact-growth `h(u)` source-model specialization for an absolute
budget square dense-loop certificate and the actual triangular solves. -/
theorem higham9_14_source_h_bound_of_DoolittleDenseLoopAbsBudgetCertificate_fl_triangular_solves_gamma_le
    (fp : FPModel) (n : ℕ)
    (A L_hat U_hat : Fin n → Fin n → ℝ)
    (b : Fin n → ℝ)
    (BU BL : Fin n → Fin n → ℝ)
    (u : ℝ) (hu : 0 ≤ u) (hu_lt_one : u < 1)
    (hn : gammaValid fp n)
    (hC : higham9_2_DoolittleDenseLoopAbsBudgetCertificate n
      A L_hat U_hat fp BU BL)
    (hγ_le_u : gamma fp n ≤ u)
    (hU_diag : ∀ i : Fin n, U_hat i i ≠ 0)
    (hAbsLU_le : ∀ i j : Fin n,
      ∑ k : Fin n, |L_hat i k| * |U_hat k j| ≤ |A i j|) :
    let y_hat := fl_forwardSub fp n L_hat b
    let x_hat := fl_backSub fp n U_hat y_hat
    ∃ DeltaA : Fin n → Fin n → ℝ,
      (∀ i j, |DeltaA i j| ≤ higham9_14_h u * |A i j|) ∧
      (∀ i, ∑ j : Fin n, (A i j + DeltaA i j) * x_hat j = b i) :=
  higham9_14_source_h_bound_of_LUBackwardError_fl_triangular_solves_gamma_le
    fp n A L_hat U_hat b (gamma fp n) u hu hu_lt_one hn
    (DoolittleDenseLoopAbsBudgetCertificate.to_LUBackwardError hC hn)
    hγ_le_u hγ_le_u hU_diag hAbsLU_le

/-- **Theorem 9.14**, Matrix-facing dense Doolittle certificate plus actual
triangular solves with source `f(u)` coefficient. -/
theorem higham9_14_matrix_source_f_bound_of_DoolittleDenseLoopCertificate_fl_triangular_solves_gamma_le
    (fp : FPModel) (n : ℕ)
    (A L_hat U_hat : Matrix (Fin n) (Fin n) ℝ)
    (b : Fin n → ℝ)
    (c u : ℝ) (hu : 0 ≤ u)
    (hn : gammaValid fp n)
    (hC : higham9_2_DoolittleDenseLoopCertificate n A L_hat U_hat fp)
    (hγ_le_u : gamma fp n ≤ u)
    (hU_diag : ∀ i : Fin n, U_hat i i ≠ 0)
    (hAbsLU_le : ∀ i j : Fin n,
      ∑ k : Fin n, |L_hat i k| * |U_hat k j| ≤ c * |A i j|) :
    let y_hat := fl_forwardSub fp n L_hat b
    let x_hat := fl_backSub fp n U_hat y_hat
    ∃ DeltaA : Matrix (Fin n) (Fin n) ℝ,
      (∀ i j, |DeltaA i j| ≤ c * higham9_14_f u * |A i j|) ∧
      Matrix.mulVec (fun i j => A i j + DeltaA i j) x_hat = b :=
  higham9_14_matrix_source_f_bound_of_LUBackwardError_fl_triangular_solves_gamma_le
    fp n A L_hat U_hat b c (gamma fp n) u hu hn
    (DoolittleDenseLoopCertificate.to_LUBackwardError hC hn)
    hγ_le_u hγ_le_u hU_diag hAbsLU_le

/-- **Theorem 9.14**, Matrix-facing absolute-budget Doolittle certificate plus
actual triangular solves with source `f(u)` coefficient. -/
theorem higham9_14_matrix_source_f_bound_of_DoolittleDenseLoopAbsBudgetCertificate_fl_triangular_solves_gamma_le
    (fp : FPModel) (n : ℕ)
    (A L_hat U_hat : Matrix (Fin n) (Fin n) ℝ)
    (b : Fin n → ℝ)
    (BU BL : Matrix (Fin n) (Fin n) ℝ)
    (c u : ℝ) (hu : 0 ≤ u)
    (hn : gammaValid fp n)
    (hC : higham9_2_DoolittleDenseLoopAbsBudgetCertificate n
      A L_hat U_hat fp BU BL)
    (hγ_le_u : gamma fp n ≤ u)
    (hU_diag : ∀ i : Fin n, U_hat i i ≠ 0)
    (hAbsLU_le : ∀ i j : Fin n,
      ∑ k : Fin n, |L_hat i k| * |U_hat k j| ≤ c * |A i j|) :
    let y_hat := fl_forwardSub fp n L_hat b
    let x_hat := fl_backSub fp n U_hat y_hat
    ∃ DeltaA : Matrix (Fin n) (Fin n) ℝ,
      (∀ i j, |DeltaA i j| ≤ c * higham9_14_f u * |A i j|) ∧
      Matrix.mulVec (fun i j => A i j + DeltaA i j) x_hat = b :=
  higham9_14_matrix_source_f_bound_of_LUBackwardError_fl_triangular_solves_gamma_le
    fp n A L_hat U_hat b c (gamma fp n) u hu hn
    (DoolittleDenseLoopAbsBudgetCertificate.to_LUBackwardError hC hn)
    hγ_le_u hγ_le_u hU_diag hAbsLU_le

/-- **Theorem 9.14**, Matrix-facing dense Doolittle certificate plus actual
triangular solves with final `h(u)` coefficient. -/
theorem higham9_14_matrix_source_h_bound_of_DoolittleDenseLoopCertificate_fl_triangular_solves_gamma_le
    (fp : FPModel) (n : ℕ)
    (A L_hat U_hat : Matrix (Fin n) (Fin n) ℝ)
    (b : Fin n → ℝ)
    (u : ℝ) (hu : 0 ≤ u) (hu_lt_one : u < 1)
    (hn : gammaValid fp n)
    (hC : higham9_2_DoolittleDenseLoopCertificate n A L_hat U_hat fp)
    (hγ_le_u : gamma fp n ≤ u)
    (hU_diag : ∀ i : Fin n, U_hat i i ≠ 0)
    (hAbsLU_le : ∀ i j : Fin n,
      ∑ k : Fin n, |L_hat i k| * |U_hat k j| ≤ |A i j|) :
    let y_hat := fl_forwardSub fp n L_hat b
    let x_hat := fl_backSub fp n U_hat y_hat
    ∃ DeltaA : Matrix (Fin n) (Fin n) ℝ,
      (∀ i j, |DeltaA i j| ≤ higham9_14_h u * |A i j|) ∧
      Matrix.mulVec (fun i j => A i j + DeltaA i j) x_hat = b :=
  higham9_14_matrix_source_h_bound_of_LUBackwardError_fl_triangular_solves_gamma_le
    fp n A L_hat U_hat b (gamma fp n) u hu hu_lt_one hn
    (DoolittleDenseLoopCertificate.to_LUBackwardError hC hn)
    hγ_le_u hγ_le_u hU_diag hAbsLU_le

/-- **Theorem 9.14**, Matrix-facing absolute-budget Doolittle certificate plus
actual triangular solves with final `h(u)` coefficient. -/
theorem higham9_14_matrix_source_h_bound_of_DoolittleDenseLoopAbsBudgetCertificate_fl_triangular_solves_gamma_le
    (fp : FPModel) (n : ℕ)
    (A L_hat U_hat : Matrix (Fin n) (Fin n) ℝ)
    (b : Fin n → ℝ)
    (BU BL : Matrix (Fin n) (Fin n) ℝ)
    (u : ℝ) (hu : 0 ≤ u) (hu_lt_one : u < 1)
    (hn : gammaValid fp n)
    (hC : higham9_2_DoolittleDenseLoopAbsBudgetCertificate n
      A L_hat U_hat fp BU BL)
    (hγ_le_u : gamma fp n ≤ u)
    (hU_diag : ∀ i : Fin n, U_hat i i ≠ 0)
    (hAbsLU_le : ∀ i j : Fin n,
      ∑ k : Fin n, |L_hat i k| * |U_hat k j| ≤ |A i j|) :
    let y_hat := fl_forwardSub fp n L_hat b
    let x_hat := fl_backSub fp n U_hat y_hat
    ∃ DeltaA : Matrix (Fin n) (Fin n) ℝ,
      (∀ i j, |DeltaA i j| ≤ higham9_14_h u * |A i j|) ∧
      Matrix.mulVec (fun i j => A i j + DeltaA i j) x_hat = b :=
  higham9_14_matrix_source_h_bound_of_LUBackwardError_fl_triangular_solves_gamma_le
    fp n A L_hat U_hat b (gamma fp n) u hu hu_lt_one hn
    (DoolittleDenseLoopAbsBudgetCertificate.to_LUBackwardError hC hn)
    hγ_le_u hγ_le_u hU_diag hAbsLU_le

/-- **Theorem 9.14**, Matrix-facing dense Doolittle certificate with a
constant-growth final `h(u)` bound. -/
theorem higham9_14_matrix_source_h_bound_of_DoolittleDenseLoopCertificate_fl_triangular_solves_const_gamma_le
    (fp : FPModel) (n : ℕ)
    (A L_hat U_hat : Matrix (Fin n) (Fin n) ℝ)
    (b : Fin n → ℝ)
    (c u : ℝ) (hc : 0 ≤ c) (hu : 0 ≤ u) (hu_lt_one : u < 1)
    (hn : gammaValid fp n)
    (hC : higham9_2_DoolittleDenseLoopCertificate n A L_hat U_hat fp)
    (hγ_le_u : gamma fp n ≤ u)
    (hU_diag : ∀ i : Fin n, U_hat i i ≠ 0)
    (hAbsLU_le : ∀ i j : Fin n,
      ∑ k : Fin n, |L_hat i k| * |U_hat k j| ≤ c * |A i j|) :
    let y_hat := fl_forwardSub fp n L_hat b
    let x_hat := fl_backSub fp n U_hat y_hat
    ∃ DeltaA : Matrix (Fin n) (Fin n) ℝ,
      (∀ i j, |DeltaA i j| ≤ c * higham9_14_h u * |A i j|) ∧
      Matrix.mulVec (fun i j => A i j + DeltaA i j) x_hat = b :=
  higham9_14_matrix_source_h_bound_of_LUBackwardError_fl_triangular_solves_const_gamma_le
    fp n A L_hat U_hat b c (gamma fp n) u hc hu hu_lt_one hn
    (DoolittleDenseLoopCertificate.to_LUBackwardError hC hn)
    hγ_le_u hγ_le_u hU_diag hAbsLU_le

/-- **Theorem 9.14**, Matrix-facing absolute-budget Doolittle certificate with
a constant-growth final `h(u)` bound. -/
theorem higham9_14_matrix_source_h_bound_of_DoolittleDenseLoopAbsBudgetCertificate_fl_triangular_solves_const_gamma_le
    (fp : FPModel) (n : ℕ)
    (A L_hat U_hat : Matrix (Fin n) (Fin n) ℝ)
    (b : Fin n → ℝ)
    (BU BL : Matrix (Fin n) (Fin n) ℝ)
    (c u : ℝ) (hc : 0 ≤ c) (hu : 0 ≤ u) (hu_lt_one : u < 1)
    (hn : gammaValid fp n)
    (hC : higham9_2_DoolittleDenseLoopAbsBudgetCertificate n
      A L_hat U_hat fp BU BL)
    (hγ_le_u : gamma fp n ≤ u)
    (hU_diag : ∀ i : Fin n, U_hat i i ≠ 0)
    (hAbsLU_le : ∀ i j : Fin n,
      ∑ k : Fin n, |L_hat i k| * |U_hat k j| ≤ c * |A i j|) :
    let y_hat := fl_forwardSub fp n L_hat b
    let x_hat := fl_backSub fp n U_hat y_hat
    ∃ DeltaA : Matrix (Fin n) (Fin n) ℝ,
      (∀ i j, |DeltaA i j| ≤ c * higham9_14_h u * |A i j|) ∧
      Matrix.mulVec (fun i j => A i j + DeltaA i j) x_hat = b :=
  higham9_14_matrix_source_h_bound_of_LUBackwardError_fl_triangular_solves_const_gamma_le
    fp n A L_hat U_hat b c (gamma fp n) u hc hu hu_lt_one hn
    (DoolittleDenseLoopAbsBudgetCertificate.to_LUBackwardError hC hn)
    hγ_le_u hγ_le_u hU_diag hAbsLU_le

/-- **Theorem 9.14**, Matrix-facing dense Doolittle certificate with a
constant-growth final `h(γ_n)` coefficient. -/
theorem higham9_14_matrix_source_h_bound_of_DoolittleDenseLoopCertificate_fl_triangular_solves_const_gamma
    (fp : FPModel) (n : ℕ)
    (A L_hat U_hat : Matrix (Fin n) (Fin n) ℝ)
    (b : Fin n → ℝ)
    (c : ℝ) (hc : 0 ≤ c)
    (hn : gammaValid fp n)
    (hγ_lt_one : gamma fp n < 1)
    (hC : higham9_2_DoolittleDenseLoopCertificate n A L_hat U_hat fp)
    (hU_diag : ∀ i : Fin n, U_hat i i ≠ 0)
    (hAbsLU_le : ∀ i j : Fin n,
      ∑ k : Fin n, |L_hat i k| * |U_hat k j| ≤ c * |A i j|) :
    let y_hat := fl_forwardSub fp n L_hat b
    let x_hat := fl_backSub fp n U_hat y_hat
    ∃ DeltaA : Matrix (Fin n) (Fin n) ℝ,
      (∀ i j, |DeltaA i j| ≤
        c * higham9_14_h (gamma fp n) * |A i j|) ∧
      Matrix.mulVec (fun i j => A i j + DeltaA i j) x_hat = b :=
  higham9_14_matrix_source_h_bound_of_DoolittleDenseLoopCertificate_fl_triangular_solves_const_gamma_le
    fp n A L_hat U_hat b c (gamma fp n) hc (gamma_nonneg fp hn)
    hγ_lt_one hn hC le_rfl hU_diag hAbsLU_le

/-- **Theorem 9.14**, Matrix-facing absolute-budget Doolittle certificate with
a constant-growth final `h(γ_n)` coefficient. -/
theorem higham9_14_matrix_source_h_bound_of_DoolittleDenseLoopAbsBudgetCertificate_fl_triangular_solves_const_gamma
    (fp : FPModel) (n : ℕ)
    (A L_hat U_hat : Matrix (Fin n) (Fin n) ℝ)
    (b : Fin n → ℝ)
    (BU BL : Matrix (Fin n) (Fin n) ℝ)
    (c : ℝ) (hc : 0 ≤ c)
    (hn : gammaValid fp n)
    (hγ_lt_one : gamma fp n < 1)
    (hC : higham9_2_DoolittleDenseLoopAbsBudgetCertificate n
      A L_hat U_hat fp BU BL)
    (hU_diag : ∀ i : Fin n, U_hat i i ≠ 0)
    (hAbsLU_le : ∀ i j : Fin n,
      ∑ k : Fin n, |L_hat i k| * |U_hat k j| ≤ c * |A i j|) :
    let y_hat := fl_forwardSub fp n L_hat b
    let x_hat := fl_backSub fp n U_hat y_hat
    ∃ DeltaA : Matrix (Fin n) (Fin n) ℝ,
      (∀ i j, |DeltaA i j| ≤
        c * higham9_14_h (gamma fp n) * |A i j|) ∧
      Matrix.mulVec (fun i j => A i j + DeltaA i j) x_hat = b :=
  higham9_14_matrix_source_h_bound_of_DoolittleDenseLoopAbsBudgetCertificate_fl_triangular_solves_const_gamma_le
    fp n A L_hat U_hat b BU BL c (gamma fp n) hc
    (gamma_nonneg fp hn) hγ_lt_one hn hC le_rfl hU_diag hAbsLU_le

/-- **Theorem 9.14**, Matrix-facing dense Doolittle certificate plus actual
triangular solves with the natural `γ_n` coefficient. -/
theorem higham9_14_matrix_source_f_bound_of_DoolittleDenseLoopCertificate_fl_triangular_solves_gamma
    (fp : FPModel) (n : ℕ)
    (A L_hat U_hat : Matrix (Fin n) (Fin n) ℝ)
    (b : Fin n → ℝ)
    (c : ℝ)
    (hn : gammaValid fp n)
    (hC : higham9_2_DoolittleDenseLoopCertificate n A L_hat U_hat fp)
    (hU_diag : ∀ i : Fin n, U_hat i i ≠ 0)
    (hAbsLU_le : ∀ i j : Fin n,
      ∑ k : Fin n, |L_hat i k| * |U_hat k j| ≤ c * |A i j|) :
    let y_hat := fl_forwardSub fp n L_hat b
    let x_hat := fl_backSub fp n U_hat y_hat
    ∃ DeltaA : Matrix (Fin n) (Fin n) ℝ,
      (∀ i j, |DeltaA i j| ≤
        c * higham9_14_f (gamma fp n) * |A i j|) ∧
      Matrix.mulVec (fun i j => A i j + DeltaA i j) x_hat = b :=
  higham9_14_matrix_source_f_bound_of_DoolittleDenseLoopCertificate_fl_triangular_solves_gamma_le
    fp n A L_hat U_hat b c (gamma fp n) (gamma_nonneg fp hn)
    hn hC le_rfl hU_diag hAbsLU_le

/-- **Theorem 9.14**, Matrix-facing absolute-budget Doolittle certificate plus
actual triangular solves with the natural `γ_n` coefficient. -/
theorem higham9_14_matrix_source_f_bound_of_DoolittleDenseLoopAbsBudgetCertificate_fl_triangular_solves_gamma
    (fp : FPModel) (n : ℕ)
    (A L_hat U_hat : Matrix (Fin n) (Fin n) ℝ)
    (b : Fin n → ℝ)
    (BU BL : Matrix (Fin n) (Fin n) ℝ)
    (c : ℝ)
    (hn : gammaValid fp n)
    (hC : higham9_2_DoolittleDenseLoopAbsBudgetCertificate n
      A L_hat U_hat fp BU BL)
    (hU_diag : ∀ i : Fin n, U_hat i i ≠ 0)
    (hAbsLU_le : ∀ i j : Fin n,
      ∑ k : Fin n, |L_hat i k| * |U_hat k j| ≤ c * |A i j|) :
    let y_hat := fl_forwardSub fp n L_hat b
    let x_hat := fl_backSub fp n U_hat y_hat
    ∃ DeltaA : Matrix (Fin n) (Fin n) ℝ,
      (∀ i j, |DeltaA i j| ≤
        c * higham9_14_f (gamma fp n) * |A i j|) ∧
      Matrix.mulVec (fun i j => A i j + DeltaA i j) x_hat = b :=
  higham9_14_matrix_source_f_bound_of_DoolittleDenseLoopAbsBudgetCertificate_fl_triangular_solves_gamma_le
    fp n A L_hat U_hat b BU BL c (gamma fp n)
    (gamma_nonneg fp hn) hn hC le_rfl hU_diag hAbsLU_le

/-- **Theorem 9.14**, Matrix-facing dense Doolittle certificate with Higham's
final `h(γ_n)` coefficient. -/
theorem higham9_14_matrix_source_h_bound_of_DoolittleDenseLoopCertificate_fl_triangular_solves_gamma
    (fp : FPModel) (n : ℕ)
    (A L_hat U_hat : Matrix (Fin n) (Fin n) ℝ)
    (b : Fin n → ℝ)
    (hn : gammaValid fp n)
    (hγ_lt_one : gamma fp n < 1)
    (hC : higham9_2_DoolittleDenseLoopCertificate n A L_hat U_hat fp)
    (hU_diag : ∀ i : Fin n, U_hat i i ≠ 0)
    (hAbsLU_le : ∀ i j : Fin n,
      ∑ k : Fin n, |L_hat i k| * |U_hat k j| ≤ |A i j|) :
    let y_hat := fl_forwardSub fp n L_hat b
    let x_hat := fl_backSub fp n U_hat y_hat
    ∃ DeltaA : Matrix (Fin n) (Fin n) ℝ,
      (∀ i j, |DeltaA i j| ≤
        higham9_14_h (gamma fp n) * |A i j|) ∧
      Matrix.mulVec (fun i j => A i j + DeltaA i j) x_hat = b :=
  higham9_14_matrix_source_h_bound_of_DoolittleDenseLoopCertificate_fl_triangular_solves_gamma_le
    fp n A L_hat U_hat b (gamma fp n) (gamma_nonneg fp hn)
    hγ_lt_one hn hC le_rfl hU_diag hAbsLU_le

/-- **Theorem 9.14**, Matrix-facing absolute-budget Doolittle certificate with
Higham's final `h(γ_n)` coefficient. -/
theorem higham9_14_matrix_source_h_bound_of_DoolittleDenseLoopAbsBudgetCertificate_fl_triangular_solves_gamma
    (fp : FPModel) (n : ℕ)
    (A L_hat U_hat : Matrix (Fin n) (Fin n) ℝ)
    (b : Fin n → ℝ)
    (BU BL : Matrix (Fin n) (Fin n) ℝ)
    (hn : gammaValid fp n)
    (hγ_lt_one : gamma fp n < 1)
    (hC : higham9_2_DoolittleDenseLoopAbsBudgetCertificate n
      A L_hat U_hat fp BU BL)
    (hU_diag : ∀ i : Fin n, U_hat i i ≠ 0)
    (hAbsLU_le : ∀ i j : Fin n,
      ∑ k : Fin n, |L_hat i k| * |U_hat k j| ≤ |A i j|) :
    let y_hat := fl_forwardSub fp n L_hat b
    let x_hat := fl_backSub fp n U_hat y_hat
    ∃ DeltaA : Matrix (Fin n) (Fin n) ℝ,
      (∀ i j, |DeltaA i j| ≤
        higham9_14_h (gamma fp n) * |A i j|) ∧
      Matrix.mulVec (fun i j => A i j + DeltaA i j) x_hat = b :=
  higham9_14_matrix_source_h_bound_of_DoolittleDenseLoopAbsBudgetCertificate_fl_triangular_solves_gamma_le
    fp n A L_hat U_hat b BU BL (gamma fp n)
    (gamma_nonneg fp hn) hγ_lt_one hn hC le_rfl hU_diag hAbsLU_le

/-- **Theorem 9.14**, Matrix-facing dense Doolittle certificate plus actual
triangular solves with optimal growth and source `f(u)` coefficient. -/
theorem higham9_14_matrix_source_f_bound_of_DoolittleDenseLoopCertificate_fl_triangular_solves_absLU_le_absA_gamma_le
    (fp : FPModel) (n : ℕ)
    (A L_hat U_hat : Matrix (Fin n) (Fin n) ℝ)
    (b : Fin n → ℝ)
    (u : ℝ) (hu : 0 ≤ u)
    (hn : gammaValid fp n)
    (hC : higham9_2_DoolittleDenseLoopCertificate n A L_hat U_hat fp)
    (hγ_le_u : gamma fp n ≤ u)
    (hU_diag : ∀ i : Fin n, U_hat i i ≠ 0)
    (hAbsLU_le : ∀ i j : Fin n,
      ∑ k : Fin n, |L_hat i k| * |U_hat k j| ≤ |A i j|) :
    let y_hat := fl_forwardSub fp n L_hat b
    let x_hat := fl_backSub fp n U_hat y_hat
    ∃ DeltaA : Matrix (Fin n) (Fin n) ℝ,
      (∀ i j, |DeltaA i j| ≤ higham9_14_f u * |A i j|) ∧
      Matrix.mulVec (fun i j => A i j + DeltaA i j) x_hat = b := by
  simpa [one_mul] using
    (higham9_14_matrix_source_f_bound_of_DoolittleDenseLoopCertificate_fl_triangular_solves_gamma_le
      fp n A L_hat U_hat b 1 u hu hn hC hγ_le_u hU_diag
      (fun i j => by simpa [one_mul] using hAbsLU_le i j))

/-- **Theorem 9.14**, Matrix-facing absolute-budget Doolittle certificate plus
actual triangular solves with optimal growth and source `f(u)` coefficient. -/
theorem higham9_14_matrix_source_f_bound_of_DoolittleDenseLoopAbsBudgetCertificate_fl_triangular_solves_absLU_le_absA_gamma_le
    (fp : FPModel) (n : ℕ)
    (A L_hat U_hat : Matrix (Fin n) (Fin n) ℝ)
    (b : Fin n → ℝ)
    (BU BL : Matrix (Fin n) (Fin n) ℝ)
    (u : ℝ) (hu : 0 ≤ u)
    (hn : gammaValid fp n)
    (hC : higham9_2_DoolittleDenseLoopAbsBudgetCertificate n
      A L_hat U_hat fp BU BL)
    (hγ_le_u : gamma fp n ≤ u)
    (hU_diag : ∀ i : Fin n, U_hat i i ≠ 0)
    (hAbsLU_le : ∀ i j : Fin n,
      ∑ k : Fin n, |L_hat i k| * |U_hat k j| ≤ |A i j|) :
    let y_hat := fl_forwardSub fp n L_hat b
    let x_hat := fl_backSub fp n U_hat y_hat
    ∃ DeltaA : Matrix (Fin n) (Fin n) ℝ,
      (∀ i j, |DeltaA i j| ≤ higham9_14_f u * |A i j|) ∧
      Matrix.mulVec (fun i j => A i j + DeltaA i j) x_hat = b := by
  simpa [one_mul] using
    (higham9_14_matrix_source_f_bound_of_DoolittleDenseLoopAbsBudgetCertificate_fl_triangular_solves_gamma_le
      fp n A L_hat U_hat b BU BL 1 u hu hn hC hγ_le_u hU_diag
      (fun i j => by simpa [one_mul] using hAbsLU_le i j))

/-- **Theorem 9.14**, Matrix-facing dense Doolittle certificate plus actual
triangular solves with optimal growth and the natural source `f(γ_n)`
coefficient. -/
theorem higham9_14_matrix_source_f_bound_of_DoolittleDenseLoopCertificate_fl_triangular_solves_absLU_le_absA_gamma
    (fp : FPModel) (n : ℕ)
    (A L_hat U_hat : Matrix (Fin n) (Fin n) ℝ)
    (b : Fin n → ℝ)
    (hn : gammaValid fp n)
    (hC : higham9_2_DoolittleDenseLoopCertificate n A L_hat U_hat fp)
    (hU_diag : ∀ i : Fin n, U_hat i i ≠ 0)
    (hAbsLU_le : ∀ i j : Fin n,
      ∑ k : Fin n, |L_hat i k| * |U_hat k j| ≤ |A i j|) :
    let y_hat := fl_forwardSub fp n L_hat b
    let x_hat := fl_backSub fp n U_hat y_hat
    ∃ DeltaA : Matrix (Fin n) (Fin n) ℝ,
      (∀ i j, |DeltaA i j| ≤
        higham9_14_f (gamma fp n) * |A i j|) ∧
      Matrix.mulVec (fun i j => A i j + DeltaA i j) x_hat = b := by
  simpa [one_mul] using
    (higham9_14_matrix_source_f_bound_of_DoolittleDenseLoopCertificate_fl_triangular_solves_gamma
      fp n A L_hat U_hat b 1 hn hC hU_diag
      (fun i j => by simpa [one_mul] using hAbsLU_le i j))

/-- **Theorem 9.14**, Matrix-facing absolute-budget Doolittle certificate plus
actual triangular solves with optimal growth and the natural source `f(γ_n)`
coefficient. -/
theorem higham9_14_matrix_source_f_bound_of_DoolittleDenseLoopAbsBudgetCertificate_fl_triangular_solves_absLU_le_absA_gamma
    (fp : FPModel) (n : ℕ)
    (A L_hat U_hat : Matrix (Fin n) (Fin n) ℝ)
    (b : Fin n → ℝ)
    (BU BL : Matrix (Fin n) (Fin n) ℝ)
    (hn : gammaValid fp n)
    (hC : higham9_2_DoolittleDenseLoopAbsBudgetCertificate n
      A L_hat U_hat fp BU BL)
    (hU_diag : ∀ i : Fin n, U_hat i i ≠ 0)
    (hAbsLU_le : ∀ i j : Fin n,
      ∑ k : Fin n, |L_hat i k| * |U_hat k j| ≤ |A i j|) :
    let y_hat := fl_forwardSub fp n L_hat b
    let x_hat := fl_backSub fp n U_hat y_hat
    ∃ DeltaA : Matrix (Fin n) (Fin n) ℝ,
      (∀ i j, |DeltaA i j| ≤
        higham9_14_f (gamma fp n) * |A i j|) ∧
      Matrix.mulVec (fun i j => A i j + DeltaA i j) x_hat = b := by
  simpa [one_mul] using
    (higham9_14_matrix_source_f_bound_of_DoolittleDenseLoopAbsBudgetCertificate_fl_triangular_solves_gamma
      fp n A L_hat U_hat b BU BL 1 hn hC hU_diag
      (fun i j => by simpa [one_mul] using hAbsLU_le i j))

/-- **Theorem 9.14**, Matrix-facing dense Doolittle certificate plus actual
triangular solves with optimal growth and final `h(u)` coefficient. -/
theorem higham9_14_matrix_source_h_bound_of_DoolittleDenseLoopCertificate_fl_triangular_solves_absLU_le_absA_gamma_le
    (fp : FPModel) (n : ℕ)
    (A L_hat U_hat : Matrix (Fin n) (Fin n) ℝ)
    (b : Fin n → ℝ)
    (u : ℝ) (hu : 0 ≤ u) (hu_lt_one : u < 1)
    (hn : gammaValid fp n)
    (hC : higham9_2_DoolittleDenseLoopCertificate n A L_hat U_hat fp)
    (hγ_le_u : gamma fp n ≤ u)
    (hU_diag : ∀ i : Fin n, U_hat i i ≠ 0)
    (hAbsLU_le : ∀ i j : Fin n,
      ∑ k : Fin n, |L_hat i k| * |U_hat k j| ≤ |A i j|) :
    let y_hat := fl_forwardSub fp n L_hat b
    let x_hat := fl_backSub fp n U_hat y_hat
    ∃ DeltaA : Matrix (Fin n) (Fin n) ℝ,
      (∀ i j, |DeltaA i j| ≤ higham9_14_h u * |A i j|) ∧
      Matrix.mulVec (fun i j => A i j + DeltaA i j) x_hat = b :=
  higham9_14_matrix_source_h_bound_of_DoolittleDenseLoopCertificate_fl_triangular_solves_gamma_le
    fp n A L_hat U_hat b u hu hu_lt_one hn hC hγ_le_u hU_diag hAbsLU_le

/-- **Theorem 9.14**, Matrix-facing absolute-budget Doolittle certificate plus
actual triangular solves with optimal growth and final `h(u)` coefficient. -/
theorem higham9_14_matrix_source_h_bound_of_DoolittleDenseLoopAbsBudgetCertificate_fl_triangular_solves_absLU_le_absA_gamma_le
    (fp : FPModel) (n : ℕ)
    (A L_hat U_hat : Matrix (Fin n) (Fin n) ℝ)
    (b : Fin n → ℝ)
    (BU BL : Matrix (Fin n) (Fin n) ℝ)
    (u : ℝ) (hu : 0 ≤ u) (hu_lt_one : u < 1)
    (hn : gammaValid fp n)
    (hC : higham9_2_DoolittleDenseLoopAbsBudgetCertificate n
      A L_hat U_hat fp BU BL)
    (hγ_le_u : gamma fp n ≤ u)
    (hU_diag : ∀ i : Fin n, U_hat i i ≠ 0)
    (hAbsLU_le : ∀ i j : Fin n,
      ∑ k : Fin n, |L_hat i k| * |U_hat k j| ≤ |A i j|) :
    let y_hat := fl_forwardSub fp n L_hat b
    let x_hat := fl_backSub fp n U_hat y_hat
    ∃ DeltaA : Matrix (Fin n) (Fin n) ℝ,
      (∀ i j, |DeltaA i j| ≤ higham9_14_h u * |A i j|) ∧
      Matrix.mulVec (fun i j => A i j + DeltaA i j) x_hat = b :=
  higham9_14_matrix_source_h_bound_of_DoolittleDenseLoopAbsBudgetCertificate_fl_triangular_solves_gamma_le
    fp n A L_hat U_hat b BU BL u hu hu_lt_one hn hC hγ_le_u hU_diag hAbsLU_le

/-- **Theorem 9.14**, Matrix-facing dense Doolittle certificate plus actual
triangular solves with optimal growth and final `h(γ_n)` coefficient. -/
theorem higham9_14_matrix_source_h_bound_of_DoolittleDenseLoopCertificate_fl_triangular_solves_absLU_le_absA_gamma
    (fp : FPModel) (n : ℕ)
    (A L_hat U_hat : Matrix (Fin n) (Fin n) ℝ)
    (b : Fin n → ℝ)
    (hn : gammaValid fp n)
    (hγ_lt_one : gamma fp n < 1)
    (hC : higham9_2_DoolittleDenseLoopCertificate n A L_hat U_hat fp)
    (hU_diag : ∀ i : Fin n, U_hat i i ≠ 0)
    (hAbsLU_le : ∀ i j : Fin n,
      ∑ k : Fin n, |L_hat i k| * |U_hat k j| ≤ |A i j|) :
    let y_hat := fl_forwardSub fp n L_hat b
    let x_hat := fl_backSub fp n U_hat y_hat
    ∃ DeltaA : Matrix (Fin n) (Fin n) ℝ,
      (∀ i j, |DeltaA i j| ≤
        higham9_14_h (gamma fp n) * |A i j|) ∧
      Matrix.mulVec (fun i j => A i j + DeltaA i j) x_hat = b :=
  higham9_14_matrix_source_h_bound_of_DoolittleDenseLoopCertificate_fl_triangular_solves_gamma
    fp n A L_hat U_hat b hn hγ_lt_one hC hU_diag hAbsLU_le

/-- **Theorem 9.14**, Matrix-facing absolute-budget Doolittle certificate plus
actual triangular solves with optimal growth and final `h(γ_n)` coefficient. -/
theorem higham9_14_matrix_source_h_bound_of_DoolittleDenseLoopAbsBudgetCertificate_fl_triangular_solves_absLU_le_absA_gamma
    (fp : FPModel) (n : ℕ)
    (A L_hat U_hat : Matrix (Fin n) (Fin n) ℝ)
    (b : Fin n → ℝ)
    (BU BL : Matrix (Fin n) (Fin n) ℝ)
    (hn : gammaValid fp n)
    (hγ_lt_one : gamma fp n < 1)
    (hC : higham9_2_DoolittleDenseLoopAbsBudgetCertificate n
      A L_hat U_hat fp BU BL)
    (hU_diag : ∀ i : Fin n, U_hat i i ≠ 0)
    (hAbsLU_le : ∀ i j : Fin n,
      ∑ k : Fin n, |L_hat i k| * |U_hat k j| ≤ |A i j|) :
    let y_hat := fl_forwardSub fp n L_hat b
    let x_hat := fl_backSub fp n U_hat y_hat
    ∃ DeltaA : Matrix (Fin n) (Fin n) ℝ,
      (∀ i j, |DeltaA i j| ≤
        higham9_14_h (gamma fp n) * |A i j|) ∧
      Matrix.mulVec (fun i j => A i j + DeltaA i j) x_hat = b :=
  higham9_14_matrix_source_h_bound_of_DoolittleDenseLoopAbsBudgetCertificate_fl_triangular_solves_gamma
    fp n A L_hat U_hat b BU BL hn hγ_lt_one hC hU_diag hAbsLU_le

/-- **Theorem 9.14**, dense Doolittle certificate with a constant-growth
final `h(u)` bound.

This variant keeps the structural comparison
`|Lhat||Uhat| <= c |A|`, needed for tridiagonal subclasses with a visible
constant such as `3`. -/
theorem higham9_14_source_h_bound_of_DoolittleDenseLoopCertificate_fl_triangular_solves_const_gamma_le
    (fp : FPModel) (n : ℕ)
    (A L_hat U_hat : Fin n → Fin n → ℝ)
    (b : Fin n → ℝ)
    (c u : ℝ) (hc : 0 ≤ c) (hu : 0 ≤ u) (hu_lt_one : u < 1)
    (hn : gammaValid fp n)
    (hC : higham9_2_DoolittleDenseLoopCertificate n A L_hat U_hat fp)
    (hγ_le_u : gamma fp n ≤ u)
    (hU_diag : ∀ i : Fin n, U_hat i i ≠ 0)
    (hAbsLU_le : ∀ i j : Fin n,
      ∑ k : Fin n, |L_hat i k| * |U_hat k j| ≤ c * |A i j|) :
    let y_hat := fl_forwardSub fp n L_hat b
    let x_hat := fl_backSub fp n U_hat y_hat
    ∃ DeltaA : Fin n → Fin n → ℝ,
      (∀ i j, |DeltaA i j| ≤ c * higham9_14_h u * |A i j|) ∧
      (∀ i, ∑ j : Fin n, (A i j + DeltaA i j) * x_hat j = b i) :=
  higham9_14_source_h_bound_of_LUBackwardError_fl_triangular_solves_const_gamma_le
    fp n A L_hat U_hat b c (gamma fp n) u hc hu hu_lt_one hn
    (DoolittleDenseLoopCertificate.to_LUBackwardError hC hn)
    hγ_le_u hγ_le_u hU_diag hAbsLU_le

/-- **Theorem 9.14**, absolute-budget Doolittle certificate with a
constant-growth final `h(u)` bound.

This exposes the lower absolute-budget dense-loop layer for tridiagonal
classes whose structural growth comparison has an explicit constant. -/
theorem higham9_14_source_h_bound_of_DoolittleDenseLoopAbsBudgetCertificate_fl_triangular_solves_const_gamma_le
    (fp : FPModel) (n : ℕ)
    (A L_hat U_hat : Fin n → Fin n → ℝ)
    (b : Fin n → ℝ)
    (BU BL : Fin n → Fin n → ℝ)
    (c u : ℝ) (hc : 0 ≤ c) (hu : 0 ≤ u) (hu_lt_one : u < 1)
    (hn : gammaValid fp n)
    (hC : higham9_2_DoolittleDenseLoopAbsBudgetCertificate n
      A L_hat U_hat fp BU BL)
    (hγ_le_u : gamma fp n ≤ u)
    (hU_diag : ∀ i : Fin n, U_hat i i ≠ 0)
    (hAbsLU_le : ∀ i j : Fin n,
      ∑ k : Fin n, |L_hat i k| * |U_hat k j| ≤ c * |A i j|) :
    let y_hat := fl_forwardSub fp n L_hat b
    let x_hat := fl_backSub fp n U_hat y_hat
    ∃ DeltaA : Fin n → Fin n → ℝ,
      (∀ i j, |DeltaA i j| ≤ c * higham9_14_h u * |A i j|) ∧
      (∀ i, ∑ j : Fin n, (A i j + DeltaA i j) * x_hat j = b i) :=
  higham9_14_source_h_bound_of_LUBackwardError_fl_triangular_solves_const_gamma_le
    fp n A L_hat U_hat b c (gamma fp n) u hc hu hu_lt_one hn
    (DoolittleDenseLoopAbsBudgetCertificate.to_LUBackwardError hC hn)
    hγ_le_u hγ_le_u hU_diag hAbsLU_le

/-- **Theorem 9.14**, dense Doolittle certificate plus actual triangular
solves with the natural `γ_n` coefficient. -/
theorem higham9_14_source_f_bound_of_DoolittleDenseLoopCertificate_fl_triangular_solves_gamma
    (fp : FPModel) (n : ℕ)
    (A L_hat U_hat : Fin n → Fin n → ℝ)
    (b : Fin n → ℝ)
    (c : ℝ)
    (hn : gammaValid fp n)
    (hC : higham9_2_DoolittleDenseLoopCertificate n A L_hat U_hat fp)
    (hU_diag : ∀ i : Fin n, U_hat i i ≠ 0)
    (hAbsLU_le : ∀ i j : Fin n,
      ∑ k : Fin n, |L_hat i k| * |U_hat k j| ≤ c * |A i j|) :
    let y_hat := fl_forwardSub fp n L_hat b
    let x_hat := fl_backSub fp n U_hat y_hat
    ∃ DeltaA : Fin n → Fin n → ℝ,
      (∀ i j, |DeltaA i j| ≤
        c * higham9_14_f (gamma fp n) * |A i j|) ∧
      (∀ i, ∑ j : Fin n, (A i j + DeltaA i j) * x_hat j = b i) :=
  higham9_14_source_f_bound_of_DoolittleDenseLoopCertificate_fl_triangular_solves_gamma_le
    fp n A L_hat U_hat b c (gamma fp n) (gamma_nonneg fp hn)
    hn hC le_rfl hU_diag hAbsLU_le

/-- **Theorem 9.14**, absolute-budget Doolittle certificate plus actual
triangular solves with the natural `γ_n` coefficient. -/
theorem higham9_14_source_f_bound_of_DoolittleDenseLoopAbsBudgetCertificate_fl_triangular_solves_gamma
    (fp : FPModel) (n : ℕ)
    (A L_hat U_hat : Fin n → Fin n → ℝ)
    (b : Fin n → ℝ)
    (BU BL : Fin n → Fin n → ℝ)
    (c : ℝ)
    (hn : gammaValid fp n)
    (hC : higham9_2_DoolittleDenseLoopAbsBudgetCertificate n
      A L_hat U_hat fp BU BL)
    (hU_diag : ∀ i : Fin n, U_hat i i ≠ 0)
    (hAbsLU_le : ∀ i j : Fin n,
      ∑ k : Fin n, |L_hat i k| * |U_hat k j| ≤ c * |A i j|) :
    let y_hat := fl_forwardSub fp n L_hat b
    let x_hat := fl_backSub fp n U_hat y_hat
    ∃ DeltaA : Fin n → Fin n → ℝ,
      (∀ i j, |DeltaA i j| ≤
        c * higham9_14_f (gamma fp n) * |A i j|) ∧
      (∀ i, ∑ j : Fin n, (A i j + DeltaA i j) * x_hat j = b i) :=
  higham9_14_source_f_bound_of_DoolittleDenseLoopAbsBudgetCertificate_fl_triangular_solves_gamma_le
    fp n A L_hat U_hat b BU BL c (gamma fp n)
    (gamma_nonneg fp hn) hn hC le_rfl hU_diag hAbsLU_le

/-- **Theorem 9.14**, dense Doolittle certificate plus actual triangular
solves with optimal growth and source `f(u)` coefficient. -/
theorem higham9_14_source_f_bound_of_DoolittleDenseLoopCertificate_fl_triangular_solves_absLU_le_absA_gamma_le
    (fp : FPModel) (n : ℕ)
    (A L_hat U_hat : Fin n → Fin n → ℝ)
    (b : Fin n → ℝ)
    (u : ℝ) (hu : 0 ≤ u)
    (hn : gammaValid fp n)
    (hC : higham9_2_DoolittleDenseLoopCertificate n A L_hat U_hat fp)
    (hγ_le_u : gamma fp n ≤ u)
    (hU_diag : ∀ i : Fin n, U_hat i i ≠ 0)
    (hAbsLU_le : ∀ i j : Fin n,
      ∑ k : Fin n, |L_hat i k| * |U_hat k j| ≤ |A i j|) :
    let y_hat := fl_forwardSub fp n L_hat b
    let x_hat := fl_backSub fp n U_hat y_hat
    ∃ DeltaA : Fin n → Fin n → ℝ,
      (∀ i j, |DeltaA i j| ≤ higham9_14_f u * |A i j|) ∧
      (∀ i, ∑ j : Fin n, (A i j + DeltaA i j) * x_hat j = b i) := by
  simpa [one_mul] using
    (higham9_14_source_f_bound_of_DoolittleDenseLoopCertificate_fl_triangular_solves_gamma_le
      fp n A L_hat U_hat b 1 u hu hn hC hγ_le_u hU_diag
      (fun i j => by simpa [one_mul] using hAbsLU_le i j))

/-- **Theorem 9.14**, absolute-budget Doolittle certificate plus actual
triangular solves with optimal growth and source `f(u)` coefficient. -/
theorem higham9_14_source_f_bound_of_DoolittleDenseLoopAbsBudgetCertificate_fl_triangular_solves_absLU_le_absA_gamma_le
    (fp : FPModel) (n : ℕ)
    (A L_hat U_hat : Fin n → Fin n → ℝ)
    (b : Fin n → ℝ)
    (BU BL : Fin n → Fin n → ℝ)
    (u : ℝ) (hu : 0 ≤ u)
    (hn : gammaValid fp n)
    (hC : higham9_2_DoolittleDenseLoopAbsBudgetCertificate n
      A L_hat U_hat fp BU BL)
    (hγ_le_u : gamma fp n ≤ u)
    (hU_diag : ∀ i : Fin n, U_hat i i ≠ 0)
    (hAbsLU_le : ∀ i j : Fin n,
      ∑ k : Fin n, |L_hat i k| * |U_hat k j| ≤ |A i j|) :
    let y_hat := fl_forwardSub fp n L_hat b
    let x_hat := fl_backSub fp n U_hat y_hat
    ∃ DeltaA : Fin n → Fin n → ℝ,
      (∀ i j, |DeltaA i j| ≤ higham9_14_f u * |A i j|) ∧
      (∀ i, ∑ j : Fin n, (A i j + DeltaA i j) * x_hat j = b i) := by
  simpa [one_mul] using
    (higham9_14_source_f_bound_of_DoolittleDenseLoopAbsBudgetCertificate_fl_triangular_solves_gamma_le
      fp n A L_hat U_hat b BU BL 1 u hu hn hC hγ_le_u hU_diag
      (fun i j => by simpa [one_mul] using hAbsLU_le i j))

/-- **Theorem 9.14**, dense Doolittle certificate plus actual triangular
solves with optimal growth and the natural source `f(γ_n)` coefficient. -/
theorem higham9_14_source_f_bound_of_DoolittleDenseLoopCertificate_fl_triangular_solves_absLU_le_absA_gamma
    (fp : FPModel) (n : ℕ)
    (A L_hat U_hat : Fin n → Fin n → ℝ)
    (b : Fin n → ℝ)
    (hn : gammaValid fp n)
    (hC : higham9_2_DoolittleDenseLoopCertificate n A L_hat U_hat fp)
    (hU_diag : ∀ i : Fin n, U_hat i i ≠ 0)
    (hAbsLU_le : ∀ i j : Fin n,
      ∑ k : Fin n, |L_hat i k| * |U_hat k j| ≤ |A i j|) :
    let y_hat := fl_forwardSub fp n L_hat b
    let x_hat := fl_backSub fp n U_hat y_hat
    ∃ DeltaA : Fin n → Fin n → ℝ,
      (∀ i j, |DeltaA i j| ≤
        higham9_14_f (gamma fp n) * |A i j|) ∧
      (∀ i, ∑ j : Fin n, (A i j + DeltaA i j) * x_hat j = b i) := by
  simpa [one_mul] using
    (higham9_14_source_f_bound_of_DoolittleDenseLoopCertificate_fl_triangular_solves_gamma
      fp n A L_hat U_hat b 1 hn hC hU_diag
      (fun i j => by simpa [one_mul] using hAbsLU_le i j))

/-- **Theorem 9.14**, absolute-budget Doolittle certificate plus actual
triangular solves with optimal growth and the natural source `f(γ_n)`
coefficient. -/
theorem higham9_14_source_f_bound_of_DoolittleDenseLoopAbsBudgetCertificate_fl_triangular_solves_absLU_le_absA_gamma
    (fp : FPModel) (n : ℕ)
    (A L_hat U_hat : Fin n → Fin n → ℝ)
    (b : Fin n → ℝ)
    (BU BL : Fin n → Fin n → ℝ)
    (hn : gammaValid fp n)
    (hC : higham9_2_DoolittleDenseLoopAbsBudgetCertificate n
      A L_hat U_hat fp BU BL)
    (hU_diag : ∀ i : Fin n, U_hat i i ≠ 0)
    (hAbsLU_le : ∀ i j : Fin n,
      ∑ k : Fin n, |L_hat i k| * |U_hat k j| ≤ |A i j|) :
    let y_hat := fl_forwardSub fp n L_hat b
    let x_hat := fl_backSub fp n U_hat y_hat
    ∃ DeltaA : Fin n → Fin n → ℝ,
      (∀ i j, |DeltaA i j| ≤
        higham9_14_f (gamma fp n) * |A i j|) ∧
      (∀ i, ∑ j : Fin n, (A i j + DeltaA i j) * x_hat j = b i) := by
  simpa [one_mul] using
    (higham9_14_source_f_bound_of_DoolittleDenseLoopAbsBudgetCertificate_fl_triangular_solves_gamma
      fp n A L_hat U_hat b BU BL 1 hn hC hU_diag
      (fun i j => by simpa [one_mul] using hAbsLU_le i j))

/-- **Theorem 9.14**, dense Doolittle certificate with Higham's final
`h(γ_n)` coefficient. -/
theorem higham9_14_source_h_bound_of_DoolittleDenseLoopCertificate_fl_triangular_solves_gamma
    (fp : FPModel) (n : ℕ)
    (A L_hat U_hat : Fin n → Fin n → ℝ)
    (b : Fin n → ℝ)
    (hn : gammaValid fp n)
    (hγ_lt_one : gamma fp n < 1)
    (hC : higham9_2_DoolittleDenseLoopCertificate n A L_hat U_hat fp)
    (hU_diag : ∀ i : Fin n, U_hat i i ≠ 0)
    (hAbsLU_le : ∀ i j : Fin n,
      ∑ k : Fin n, |L_hat i k| * |U_hat k j| ≤ |A i j|) :
    let y_hat := fl_forwardSub fp n L_hat b
    let x_hat := fl_backSub fp n U_hat y_hat
    ∃ DeltaA : Fin n → Fin n → ℝ,
      (∀ i j, |DeltaA i j| ≤
        higham9_14_h (gamma fp n) * |A i j|) ∧
      (∀ i, ∑ j : Fin n, (A i j + DeltaA i j) * x_hat j = b i) :=
  higham9_14_source_h_bound_of_DoolittleDenseLoopCertificate_fl_triangular_solves_gamma_le
    fp n A L_hat U_hat b (gamma fp n) (gamma_nonneg fp hn)
    hγ_lt_one hn hC le_rfl hU_diag hAbsLU_le

/-- **Theorem 9.14**, absolute-budget Doolittle certificate with Higham's
final `h(γ_n)` coefficient. -/
theorem higham9_14_source_h_bound_of_DoolittleDenseLoopAbsBudgetCertificate_fl_triangular_solves_gamma
    (fp : FPModel) (n : ℕ)
    (A L_hat U_hat : Fin n → Fin n → ℝ)
    (b : Fin n → ℝ)
    (BU BL : Fin n → Fin n → ℝ)
    (hn : gammaValid fp n)
    (hγ_lt_one : gamma fp n < 1)
    (hC : higham9_2_DoolittleDenseLoopAbsBudgetCertificate n
      A L_hat U_hat fp BU BL)
    (hU_diag : ∀ i : Fin n, U_hat i i ≠ 0)
    (hAbsLU_le : ∀ i j : Fin n,
      ∑ k : Fin n, |L_hat i k| * |U_hat k j| ≤ |A i j|) :
    let y_hat := fl_forwardSub fp n L_hat b
    let x_hat := fl_backSub fp n U_hat y_hat
    ∃ DeltaA : Fin n → Fin n → ℝ,
      (∀ i j, |DeltaA i j| ≤
        higham9_14_h (gamma fp n) * |A i j|) ∧
      (∀ i, ∑ j : Fin n, (A i j + DeltaA i j) * x_hat j = b i) :=
  higham9_14_source_h_bound_of_DoolittleDenseLoopAbsBudgetCertificate_fl_triangular_solves_gamma_le
    fp n A L_hat U_hat b BU BL (gamma fp n)
    (gamma_nonneg fp hn) hγ_lt_one hn hC le_rfl hU_diag hAbsLU_le

/-- **Theorem 9.14**, dense Doolittle certificate plus actual triangular
solves with optimal growth and final `h(u)` coefficient. -/
theorem higham9_14_source_h_bound_of_DoolittleDenseLoopCertificate_fl_triangular_solves_absLU_le_absA_gamma_le
    (fp : FPModel) (n : ℕ)
    (A L_hat U_hat : Fin n → Fin n → ℝ)
    (b : Fin n → ℝ)
    (u : ℝ) (hu : 0 ≤ u) (hu_lt_one : u < 1)
    (hn : gammaValid fp n)
    (hC : higham9_2_DoolittleDenseLoopCertificate n A L_hat U_hat fp)
    (hγ_le_u : gamma fp n ≤ u)
    (hU_diag : ∀ i : Fin n, U_hat i i ≠ 0)
    (hAbsLU_le : ∀ i j : Fin n,
      ∑ k : Fin n, |L_hat i k| * |U_hat k j| ≤ |A i j|) :
    let y_hat := fl_forwardSub fp n L_hat b
    let x_hat := fl_backSub fp n U_hat y_hat
    ∃ DeltaA : Fin n → Fin n → ℝ,
      (∀ i j, |DeltaA i j| ≤ higham9_14_h u * |A i j|) ∧
      (∀ i, ∑ j : Fin n, (A i j + DeltaA i j) * x_hat j = b i) :=
  higham9_14_source_h_bound_of_DoolittleDenseLoopCertificate_fl_triangular_solves_gamma_le
    fp n A L_hat U_hat b u hu hu_lt_one hn hC hγ_le_u hU_diag hAbsLU_le

/-- **Theorem 9.14**, absolute-budget Doolittle certificate plus actual
triangular solves with optimal growth and final `h(u)` coefficient. -/
theorem higham9_14_source_h_bound_of_DoolittleDenseLoopAbsBudgetCertificate_fl_triangular_solves_absLU_le_absA_gamma_le
    (fp : FPModel) (n : ℕ)
    (A L_hat U_hat : Fin n → Fin n → ℝ)
    (b : Fin n → ℝ)
    (BU BL : Fin n → Fin n → ℝ)
    (u : ℝ) (hu : 0 ≤ u) (hu_lt_one : u < 1)
    (hn : gammaValid fp n)
    (hC : higham9_2_DoolittleDenseLoopAbsBudgetCertificate n
      A L_hat U_hat fp BU BL)
    (hγ_le_u : gamma fp n ≤ u)
    (hU_diag : ∀ i : Fin n, U_hat i i ≠ 0)
    (hAbsLU_le : ∀ i j : Fin n,
      ∑ k : Fin n, |L_hat i k| * |U_hat k j| ≤ |A i j|) :
    let y_hat := fl_forwardSub fp n L_hat b
    let x_hat := fl_backSub fp n U_hat y_hat
    ∃ DeltaA : Fin n → Fin n → ℝ,
      (∀ i j, |DeltaA i j| ≤ higham9_14_h u * |A i j|) ∧
      (∀ i, ∑ j : Fin n, (A i j + DeltaA i j) * x_hat j = b i) :=
  higham9_14_source_h_bound_of_DoolittleDenseLoopAbsBudgetCertificate_fl_triangular_solves_gamma_le
    fp n A L_hat U_hat b BU BL u hu hu_lt_one hn hC hγ_le_u hU_diag hAbsLU_le

/-- **Theorem 9.14**, dense Doolittle certificate plus actual triangular
solves with optimal growth and final `h(γ_n)` coefficient. -/
theorem higham9_14_source_h_bound_of_DoolittleDenseLoopCertificate_fl_triangular_solves_absLU_le_absA_gamma
    (fp : FPModel) (n : ℕ)
    (A L_hat U_hat : Fin n → Fin n → ℝ)
    (b : Fin n → ℝ)
    (hn : gammaValid fp n)
    (hγ_lt_one : gamma fp n < 1)
    (hC : higham9_2_DoolittleDenseLoopCertificate n A L_hat U_hat fp)
    (hU_diag : ∀ i : Fin n, U_hat i i ≠ 0)
    (hAbsLU_le : ∀ i j : Fin n,
      ∑ k : Fin n, |L_hat i k| * |U_hat k j| ≤ |A i j|) :
    let y_hat := fl_forwardSub fp n L_hat b
    let x_hat := fl_backSub fp n U_hat y_hat
    ∃ DeltaA : Fin n → Fin n → ℝ,
      (∀ i j, |DeltaA i j| ≤
        higham9_14_h (gamma fp n) * |A i j|) ∧
      (∀ i, ∑ j : Fin n, (A i j + DeltaA i j) * x_hat j = b i) :=
  higham9_14_source_h_bound_of_DoolittleDenseLoopCertificate_fl_triangular_solves_gamma
    fp n A L_hat U_hat b hn hγ_lt_one hC hU_diag hAbsLU_le

/-- **Theorem 9.14**, absolute-budget Doolittle certificate plus actual
triangular solves with optimal growth and final `h(γ_n)` coefficient. -/
theorem higham9_14_source_h_bound_of_DoolittleDenseLoopAbsBudgetCertificate_fl_triangular_solves_absLU_le_absA_gamma
    (fp : FPModel) (n : ℕ)
    (A L_hat U_hat : Fin n → Fin n → ℝ)
    (b : Fin n → ℝ)
    (BU BL : Fin n → Fin n → ℝ)
    (hn : gammaValid fp n)
    (hγ_lt_one : gamma fp n < 1)
    (hC : higham9_2_DoolittleDenseLoopAbsBudgetCertificate n
      A L_hat U_hat fp BU BL)
    (hU_diag : ∀ i : Fin n, U_hat i i ≠ 0)
    (hAbsLU_le : ∀ i j : Fin n,
      ∑ k : Fin n, |L_hat i k| * |U_hat k j| ≤ |A i j|) :
    let y_hat := fl_forwardSub fp n L_hat b
    let x_hat := fl_backSub fp n U_hat y_hat
    ∃ DeltaA : Fin n → Fin n → ℝ,
      (∀ i j, |DeltaA i j| ≤
        higham9_14_h (gamma fp n) * |A i j|) ∧
      (∀ i, ∑ j : Fin n, (A i j + DeltaA i j) * x_hat j = b i) :=
  higham9_14_source_h_bound_of_DoolittleDenseLoopAbsBudgetCertificate_fl_triangular_solves_gamma
    fp n A L_hat U_hat b BU BL hn hγ_lt_one hC hU_diag hAbsLU_le

/-- **Theorem 9.14**, dense Doolittle certificate with a constant-growth
final `h(γ_n)` coefficient. -/
theorem higham9_14_source_h_bound_of_DoolittleDenseLoopCertificate_fl_triangular_solves_const_gamma
    (fp : FPModel) (n : ℕ)
    (A L_hat U_hat : Fin n → Fin n → ℝ)
    (b : Fin n → ℝ)
    (c : ℝ) (hc : 0 ≤ c)
    (hn : gammaValid fp n)
    (hγ_lt_one : gamma fp n < 1)
    (hC : higham9_2_DoolittleDenseLoopCertificate n A L_hat U_hat fp)
    (hU_diag : ∀ i : Fin n, U_hat i i ≠ 0)
    (hAbsLU_le : ∀ i j : Fin n,
      ∑ k : Fin n, |L_hat i k| * |U_hat k j| ≤ c * |A i j|) :
    let y_hat := fl_forwardSub fp n L_hat b
    let x_hat := fl_backSub fp n U_hat y_hat
    ∃ DeltaA : Fin n → Fin n → ℝ,
      (∀ i j, |DeltaA i j| ≤
        c * higham9_14_h (gamma fp n) * |A i j|) ∧
      (∀ i, ∑ j : Fin n, (A i j + DeltaA i j) * x_hat j = b i) :=
  higham9_14_source_h_bound_of_DoolittleDenseLoopCertificate_fl_triangular_solves_const_gamma_le
    fp n A L_hat U_hat b c (gamma fp n) hc (gamma_nonneg fp hn)
    hγ_lt_one hn hC le_rfl hU_diag hAbsLU_le

/-- **Theorem 9.14**, absolute-budget Doolittle certificate with a
constant-growth final `h(γ_n)` coefficient. -/
theorem higham9_14_source_h_bound_of_DoolittleDenseLoopAbsBudgetCertificate_fl_triangular_solves_const_gamma
    (fp : FPModel) (n : ℕ)
    (A L_hat U_hat : Fin n → Fin n → ℝ)
    (b : Fin n → ℝ)
    (BU BL : Fin n → Fin n → ℝ)
    (c : ℝ) (hc : 0 ≤ c)
    (hn : gammaValid fp n)
    (hγ_lt_one : gamma fp n < 1)
    (hC : higham9_2_DoolittleDenseLoopAbsBudgetCertificate n
      A L_hat U_hat fp BU BL)
    (hU_diag : ∀ i : Fin n, U_hat i i ≠ 0)
    (hAbsLU_le : ∀ i j : Fin n,
      ∑ k : Fin n, |L_hat i k| * |U_hat k j| ≤ c * |A i j|) :
    let y_hat := fl_forwardSub fp n L_hat b
    let x_hat := fl_backSub fp n U_hat y_hat
    ∃ DeltaA : Fin n → Fin n → ℝ,
      (∀ i j, |DeltaA i j| ≤
        c * higham9_14_h (gamma fp n) * |A i j|) ∧
      (∀ i, ∑ j : Fin n, (A i j + DeltaA i j) * x_hat j = b i) :=
  higham9_14_source_h_bound_of_DoolittleDenseLoopAbsBudgetCertificate_fl_triangular_solves_const_gamma_le
    fp n A L_hat U_hat b BU BL c (gamma fp n) hc
    (gamma_nonneg fp hn) hγ_lt_one hn hC le_rfl hU_diag hAbsLU_le

/-- **Theorem 9.14**, square-specialized rectangular dense Doolittle
certificate plus actual triangular solves.

This is the rectangular `m = n` entry point for the source-facing `f(u)` bound:
the rectangular dense-loop certificate is first converted to the square
Doolittle certificate API, then reused by the established Theorem 9.14 wrapper. -/
theorem higham9_14_source_f_bound_of_RectDoolittleDenseLoopCertificate_square_fl_triangular_solves_gamma_le
    (fp : FPModel) (n : ℕ)
    (A L_hat U_hat : Fin n → Fin n → ℝ)
    (b : Fin n → ℝ)
    (c u : ℝ) (hu : 0 ≤ u)
    (hn : gammaValid fp n)
    (hC : higham9_2_RectDoolittleDenseLoopCertificate
      (Nat.le_refl n) A L_hat U_hat fp)
    (hγ_le_u : gamma fp n ≤ u)
    (hU_diag : ∀ i : Fin n, U_hat i i ≠ 0)
    (hAbsLU_le : ∀ i j : Fin n,
      ∑ k : Fin n, |L_hat i k| * |U_hat k j| ≤ c * |A i j|) :
    let y_hat := fl_forwardSub fp n L_hat b
    let x_hat := fl_backSub fp n U_hat y_hat
    ∃ DeltaA : Fin n → Fin n → ℝ,
      (∀ i j, |DeltaA i j| ≤ c * higham9_14_f u * |A i j|) ∧
      (∀ i, ∑ j : Fin n, (A i j + DeltaA i j) * x_hat j = b i) :=
  higham9_14_source_f_bound_of_DoolittleDenseLoopCertificate_fl_triangular_solves_gamma_le
    fp n A L_hat U_hat b c u hu hn
    (higham9_2_rectDenseLoopCertificate_to_squareDenseLoopCertificate hC)
    hγ_le_u hU_diag hAbsLU_le

/-- **Theorem 9.14**, square-specialized rectangular absolute-budget
Doolittle certificate plus actual triangular solves. -/
theorem higham9_14_source_f_bound_of_RectDoolittleDenseLoopAbsBudgetCertificate_square_fl_triangular_solves_gamma_le
    (fp : FPModel) (n : ℕ)
    (A L_hat U_hat : Fin n → Fin n → ℝ)
    (b : Fin n → ℝ)
    (BU BL : Fin n → Fin n → ℝ)
    (c u : ℝ) (hu : 0 ≤ u)
    (hn : gammaValid fp n)
    (hC : higham9_2_RectDoolittleDenseLoopAbsBudgetCertificate
      (Nat.le_refl n) A L_hat U_hat fp BU BL)
    (hγ_le_u : gamma fp n ≤ u)
    (hU_diag : ∀ i : Fin n, U_hat i i ≠ 0)
    (hAbsLU_le : ∀ i j : Fin n,
      ∑ k : Fin n, |L_hat i k| * |U_hat k j| ≤ c * |A i j|) :
    let y_hat := fl_forwardSub fp n L_hat b
    let x_hat := fl_backSub fp n U_hat y_hat
    ∃ DeltaA : Fin n → Fin n → ℝ,
      (∀ i j, |DeltaA i j| ≤ c * higham9_14_f u * |A i j|) ∧
      (∀ i, ∑ j : Fin n, (A i j + DeltaA i j) * x_hat j = b i) :=
  higham9_14_source_f_bound_of_DoolittleDenseLoopAbsBudgetCertificate_fl_triangular_solves_gamma_le
    fp n A L_hat U_hat b BU BL c u hu hn
    (higham9_2_rectAbsBudgetCertificate_to_squareAbsBudgetCertificate hC)
    hγ_le_u hU_diag hAbsLU_le

/-- **Theorem 9.14**, square-specialized rectangular dense Doolittle
certificate with the final `h(u)` bound. -/
theorem higham9_14_source_h_bound_of_RectDoolittleDenseLoopCertificate_square_fl_triangular_solves_gamma_le
    (fp : FPModel) (n : ℕ)
    (A L_hat U_hat : Fin n → Fin n → ℝ)
    (b : Fin n → ℝ)
    (u : ℝ) (hu : 0 ≤ u) (hu_lt_one : u < 1)
    (hn : gammaValid fp n)
    (hC : higham9_2_RectDoolittleDenseLoopCertificate
      (Nat.le_refl n) A L_hat U_hat fp)
    (hγ_le_u : gamma fp n ≤ u)
    (hU_diag : ∀ i : Fin n, U_hat i i ≠ 0)
    (hAbsLU_le : ∀ i j : Fin n,
      ∑ k : Fin n, |L_hat i k| * |U_hat k j| ≤ |A i j|) :
    let y_hat := fl_forwardSub fp n L_hat b
    let x_hat := fl_backSub fp n U_hat y_hat
    ∃ DeltaA : Fin n → Fin n → ℝ,
      (∀ i j, |DeltaA i j| ≤ higham9_14_h u * |A i j|) ∧
      (∀ i, ∑ j : Fin n, (A i j + DeltaA i j) * x_hat j = b i) :=
  higham9_14_source_h_bound_of_DoolittleDenseLoopCertificate_fl_triangular_solves_gamma_le
    fp n A L_hat U_hat b u hu hu_lt_one hn
    (higham9_2_rectDenseLoopCertificate_to_squareDenseLoopCertificate hC)
    hγ_le_u hU_diag hAbsLU_le

/-- **Theorem 9.14**, square-specialized rectangular absolute-budget
Doolittle certificate with the final `h(u)` bound. -/
theorem higham9_14_source_h_bound_of_RectDoolittleDenseLoopAbsBudgetCertificate_square_fl_triangular_solves_gamma_le
    (fp : FPModel) (n : ℕ)
    (A L_hat U_hat : Fin n → Fin n → ℝ)
    (b : Fin n → ℝ)
    (BU BL : Fin n → Fin n → ℝ)
    (u : ℝ) (hu : 0 ≤ u) (hu_lt_one : u < 1)
    (hn : gammaValid fp n)
    (hC : higham9_2_RectDoolittleDenseLoopAbsBudgetCertificate
      (Nat.le_refl n) A L_hat U_hat fp BU BL)
    (hγ_le_u : gamma fp n ≤ u)
    (hU_diag : ∀ i : Fin n, U_hat i i ≠ 0)
    (hAbsLU_le : ∀ i j : Fin n,
      ∑ k : Fin n, |L_hat i k| * |U_hat k j| ≤ |A i j|) :
    let y_hat := fl_forwardSub fp n L_hat b
    let x_hat := fl_backSub fp n U_hat y_hat
    ∃ DeltaA : Fin n → Fin n → ℝ,
      (∀ i j, |DeltaA i j| ≤ higham9_14_h u * |A i j|) ∧
      (∀ i, ∑ j : Fin n, (A i j + DeltaA i j) * x_hat j = b i) :=
  higham9_14_source_h_bound_of_DoolittleDenseLoopAbsBudgetCertificate_fl_triangular_solves_gamma_le
    fp n A L_hat U_hat b BU BL u hu hu_lt_one hn
    (higham9_2_rectAbsBudgetCertificate_to_squareAbsBudgetCertificate hC)
    hγ_le_u hU_diag hAbsLU_le

/-- **Theorem 9.14**, Matrix-facing square-specialized rectangular dense
Doolittle certificate plus actual triangular solves with source `f(u)`
coefficient. -/
theorem higham9_14_matrix_source_f_bound_of_RectDoolittleDenseLoopCertificate_square_fl_triangular_solves_gamma_le
    (fp : FPModel) (n : ℕ)
    (A L_hat U_hat : Matrix (Fin n) (Fin n) ℝ)
    (b : Fin n → ℝ)
    (c u : ℝ) (hu : 0 ≤ u)
    (hn : gammaValid fp n)
    (hC : higham9_2_RectDoolittleDenseLoopCertificate
      (Nat.le_refl n) A L_hat U_hat fp)
    (hγ_le_u : gamma fp n ≤ u)
    (hU_diag : ∀ i : Fin n, U_hat i i ≠ 0)
    (hAbsLU_le : ∀ i j : Fin n,
      ∑ k : Fin n, |L_hat i k| * |U_hat k j| ≤ c * |A i j|) :
    let y_hat := fl_forwardSub fp n L_hat b
    let x_hat := fl_backSub fp n U_hat y_hat
    ∃ DeltaA : Matrix (Fin n) (Fin n) ℝ,
      (∀ i j, |DeltaA i j| ≤ c * higham9_14_f u * |A i j|) ∧
      Matrix.mulVec (fun i j => A i j + DeltaA i j) x_hat = b :=
  higham9_14_matrix_source_f_bound_of_DoolittleDenseLoopCertificate_fl_triangular_solves_gamma_le
    fp n A L_hat U_hat b c u hu hn
    (higham9_2_rectDenseLoopCertificate_to_squareDenseLoopCertificate hC)
    hγ_le_u hU_diag hAbsLU_le

/-- **Theorem 9.14**, Matrix-facing square-specialized rectangular
absolute-budget Doolittle certificate plus actual triangular solves with source
`f(u)` coefficient. -/
theorem higham9_14_matrix_source_f_bound_of_RectDoolittleDenseLoopAbsBudgetCertificate_square_fl_triangular_solves_gamma_le
    (fp : FPModel) (n : ℕ)
    (A L_hat U_hat : Matrix (Fin n) (Fin n) ℝ)
    (b : Fin n → ℝ)
    (BU BL : Matrix (Fin n) (Fin n) ℝ)
    (c u : ℝ) (hu : 0 ≤ u)
    (hn : gammaValid fp n)
    (hC : higham9_2_RectDoolittleDenseLoopAbsBudgetCertificate
      (Nat.le_refl n) A L_hat U_hat fp BU BL)
    (hγ_le_u : gamma fp n ≤ u)
    (hU_diag : ∀ i : Fin n, U_hat i i ≠ 0)
    (hAbsLU_le : ∀ i j : Fin n,
      ∑ k : Fin n, |L_hat i k| * |U_hat k j| ≤ c * |A i j|) :
    let y_hat := fl_forwardSub fp n L_hat b
    let x_hat := fl_backSub fp n U_hat y_hat
    ∃ DeltaA : Matrix (Fin n) (Fin n) ℝ,
      (∀ i j, |DeltaA i j| ≤ c * higham9_14_f u * |A i j|) ∧
      Matrix.mulVec (fun i j => A i j + DeltaA i j) x_hat = b :=
  higham9_14_matrix_source_f_bound_of_DoolittleDenseLoopAbsBudgetCertificate_fl_triangular_solves_gamma_le
    fp n A L_hat U_hat b BU BL c u hu hn
    (higham9_2_rectAbsBudgetCertificate_to_squareAbsBudgetCertificate hC)
    hγ_le_u hU_diag hAbsLU_le

/-- **Theorem 9.14**, Matrix-facing square-specialized rectangular dense
Doolittle certificate with final `h(u)` coefficient. -/
theorem higham9_14_matrix_source_h_bound_of_RectDoolittleDenseLoopCertificate_square_fl_triangular_solves_gamma_le
    (fp : FPModel) (n : ℕ)
    (A L_hat U_hat : Matrix (Fin n) (Fin n) ℝ)
    (b : Fin n → ℝ)
    (u : ℝ) (hu : 0 ≤ u) (hu_lt_one : u < 1)
    (hn : gammaValid fp n)
    (hC : higham9_2_RectDoolittleDenseLoopCertificate
      (Nat.le_refl n) A L_hat U_hat fp)
    (hγ_le_u : gamma fp n ≤ u)
    (hU_diag : ∀ i : Fin n, U_hat i i ≠ 0)
    (hAbsLU_le : ∀ i j : Fin n,
      ∑ k : Fin n, |L_hat i k| * |U_hat k j| ≤ |A i j|) :
    let y_hat := fl_forwardSub fp n L_hat b
    let x_hat := fl_backSub fp n U_hat y_hat
    ∃ DeltaA : Matrix (Fin n) (Fin n) ℝ,
      (∀ i j, |DeltaA i j| ≤ higham9_14_h u * |A i j|) ∧
      Matrix.mulVec (fun i j => A i j + DeltaA i j) x_hat = b :=
  higham9_14_matrix_source_h_bound_of_DoolittleDenseLoopCertificate_fl_triangular_solves_gamma_le
    fp n A L_hat U_hat b u hu hu_lt_one hn
    (higham9_2_rectDenseLoopCertificate_to_squareDenseLoopCertificate hC)
    hγ_le_u hU_diag hAbsLU_le

/-- **Theorem 9.14**, Matrix-facing square-specialized rectangular
absolute-budget Doolittle certificate with final `h(u)` coefficient. -/
theorem higham9_14_matrix_source_h_bound_of_RectDoolittleDenseLoopAbsBudgetCertificate_square_fl_triangular_solves_gamma_le
    (fp : FPModel) (n : ℕ)
    (A L_hat U_hat : Matrix (Fin n) (Fin n) ℝ)
    (b : Fin n → ℝ)
    (BU BL : Matrix (Fin n) (Fin n) ℝ)
    (u : ℝ) (hu : 0 ≤ u) (hu_lt_one : u < 1)
    (hn : gammaValid fp n)
    (hC : higham9_2_RectDoolittleDenseLoopAbsBudgetCertificate
      (Nat.le_refl n) A L_hat U_hat fp BU BL)
    (hγ_le_u : gamma fp n ≤ u)
    (hU_diag : ∀ i : Fin n, U_hat i i ≠ 0)
    (hAbsLU_le : ∀ i j : Fin n,
      ∑ k : Fin n, |L_hat i k| * |U_hat k j| ≤ |A i j|) :
    let y_hat := fl_forwardSub fp n L_hat b
    let x_hat := fl_backSub fp n U_hat y_hat
    ∃ DeltaA : Matrix (Fin n) (Fin n) ℝ,
      (∀ i j, |DeltaA i j| ≤ higham9_14_h u * |A i j|) ∧
      Matrix.mulVec (fun i j => A i j + DeltaA i j) x_hat = b :=
  higham9_14_matrix_source_h_bound_of_DoolittleDenseLoopAbsBudgetCertificate_fl_triangular_solves_gamma_le
    fp n A L_hat U_hat b BU BL u hu hu_lt_one hn
    (higham9_2_rectAbsBudgetCertificate_to_squareAbsBudgetCertificate hC)
    hγ_le_u hU_diag hAbsLU_le

/-- **Theorem 9.14**, Matrix-facing square-specialized rectangular dense
Doolittle certificate with a constant-growth final `h(u)` bound. -/
theorem higham9_14_matrix_source_h_bound_of_RectDoolittleDenseLoopCertificate_square_fl_triangular_solves_const_gamma_le
    (fp : FPModel) (n : ℕ)
    (A L_hat U_hat : Matrix (Fin n) (Fin n) ℝ)
    (b : Fin n → ℝ)
    (c u : ℝ) (hc : 0 ≤ c) (hu : 0 ≤ u) (hu_lt_one : u < 1)
    (hn : gammaValid fp n)
    (hC : higham9_2_RectDoolittleDenseLoopCertificate
      (Nat.le_refl n) A L_hat U_hat fp)
    (hγ_le_u : gamma fp n ≤ u)
    (hU_diag : ∀ i : Fin n, U_hat i i ≠ 0)
    (hAbsLU_le : ∀ i j : Fin n,
      ∑ k : Fin n, |L_hat i k| * |U_hat k j| ≤ c * |A i j|) :
    let y_hat := fl_forwardSub fp n L_hat b
    let x_hat := fl_backSub fp n U_hat y_hat
    ∃ DeltaA : Matrix (Fin n) (Fin n) ℝ,
      (∀ i j, |DeltaA i j| ≤ c * higham9_14_h u * |A i j|) ∧
      Matrix.mulVec (fun i j => A i j + DeltaA i j) x_hat = b :=
  higham9_14_matrix_source_h_bound_of_DoolittleDenseLoopCertificate_fl_triangular_solves_const_gamma_le
    fp n A L_hat U_hat b c u hc hu hu_lt_one hn
    (higham9_2_rectDenseLoopCertificate_to_squareDenseLoopCertificate hC)
    hγ_le_u hU_diag hAbsLU_le

/-- **Theorem 9.14**, Matrix-facing square-specialized rectangular
absolute-budget Doolittle certificate with a constant-growth final `h(u)`
bound. -/
theorem higham9_14_matrix_source_h_bound_of_RectDoolittleDenseLoopAbsBudgetCertificate_square_fl_triangular_solves_const_gamma_le
    (fp : FPModel) (n : ℕ)
    (A L_hat U_hat : Matrix (Fin n) (Fin n) ℝ)
    (b : Fin n → ℝ)
    (BU BL : Matrix (Fin n) (Fin n) ℝ)
    (c u : ℝ) (hc : 0 ≤ c) (hu : 0 ≤ u) (hu_lt_one : u < 1)
    (hn : gammaValid fp n)
    (hC : higham9_2_RectDoolittleDenseLoopAbsBudgetCertificate
      (Nat.le_refl n) A L_hat U_hat fp BU BL)
    (hγ_le_u : gamma fp n ≤ u)
    (hU_diag : ∀ i : Fin n, U_hat i i ≠ 0)
    (hAbsLU_le : ∀ i j : Fin n,
      ∑ k : Fin n, |L_hat i k| * |U_hat k j| ≤ c * |A i j|) :
    let y_hat := fl_forwardSub fp n L_hat b
    let x_hat := fl_backSub fp n U_hat y_hat
    ∃ DeltaA : Matrix (Fin n) (Fin n) ℝ,
      (∀ i j, |DeltaA i j| ≤ c * higham9_14_h u * |A i j|) ∧
      Matrix.mulVec (fun i j => A i j + DeltaA i j) x_hat = b :=
  higham9_14_matrix_source_h_bound_of_DoolittleDenseLoopAbsBudgetCertificate_fl_triangular_solves_const_gamma_le
    fp n A L_hat U_hat b BU BL c u hc hu hu_lt_one hn
    (higham9_2_rectAbsBudgetCertificate_to_squareAbsBudgetCertificate hC)
    hγ_le_u hU_diag hAbsLU_le

/-- **Theorem 9.14**, Matrix-facing square-specialized rectangular dense
Doolittle certificate with a constant-growth final `h(γ_n)` coefficient. -/
theorem higham9_14_matrix_source_h_bound_of_RectDoolittleDenseLoopCertificate_square_fl_triangular_solves_const_gamma
    (fp : FPModel) (n : ℕ)
    (A L_hat U_hat : Matrix (Fin n) (Fin n) ℝ)
    (b : Fin n → ℝ)
    (c : ℝ) (hc : 0 ≤ c)
    (hn : gammaValid fp n)
    (hγ_lt_one : gamma fp n < 1)
    (hC : higham9_2_RectDoolittleDenseLoopCertificate
      (Nat.le_refl n) A L_hat U_hat fp)
    (hU_diag : ∀ i : Fin n, U_hat i i ≠ 0)
    (hAbsLU_le : ∀ i j : Fin n,
      ∑ k : Fin n, |L_hat i k| * |U_hat k j| ≤ c * |A i j|) :
    let y_hat := fl_forwardSub fp n L_hat b
    let x_hat := fl_backSub fp n U_hat y_hat
    ∃ DeltaA : Matrix (Fin n) (Fin n) ℝ,
      (∀ i j, |DeltaA i j| ≤
        c * higham9_14_h (gamma fp n) * |A i j|) ∧
      Matrix.mulVec (fun i j => A i j + DeltaA i j) x_hat = b :=
  higham9_14_matrix_source_h_bound_of_RectDoolittleDenseLoopCertificate_square_fl_triangular_solves_const_gamma_le
    fp n A L_hat U_hat b c (gamma fp n) hc (gamma_nonneg fp hn)
    hγ_lt_one hn hC le_rfl hU_diag hAbsLU_le

/-- **Theorem 9.14**, Matrix-facing square-specialized rectangular
absolute-budget Doolittle certificate with a constant-growth final `h(γ_n)`
coefficient. -/
theorem higham9_14_matrix_source_h_bound_of_RectDoolittleDenseLoopAbsBudgetCertificate_square_fl_triangular_solves_const_gamma
    (fp : FPModel) (n : ℕ)
    (A L_hat U_hat : Matrix (Fin n) (Fin n) ℝ)
    (b : Fin n → ℝ)
    (BU BL : Matrix (Fin n) (Fin n) ℝ)
    (c : ℝ) (hc : 0 ≤ c)
    (hn : gammaValid fp n)
    (hγ_lt_one : gamma fp n < 1)
    (hC : higham9_2_RectDoolittleDenseLoopAbsBudgetCertificate
      (Nat.le_refl n) A L_hat U_hat fp BU BL)
    (hU_diag : ∀ i : Fin n, U_hat i i ≠ 0)
    (hAbsLU_le : ∀ i j : Fin n,
      ∑ k : Fin n, |L_hat i k| * |U_hat k j| ≤ c * |A i j|) :
    let y_hat := fl_forwardSub fp n L_hat b
    let x_hat := fl_backSub fp n U_hat y_hat
    ∃ DeltaA : Matrix (Fin n) (Fin n) ℝ,
      (∀ i j, |DeltaA i j| ≤
        c * higham9_14_h (gamma fp n) * |A i j|) ∧
      Matrix.mulVec (fun i j => A i j + DeltaA i j) x_hat = b :=
  higham9_14_matrix_source_h_bound_of_RectDoolittleDenseLoopAbsBudgetCertificate_square_fl_triangular_solves_const_gamma_le
    fp n A L_hat U_hat b BU BL c (gamma fp n) hc
    (gamma_nonneg fp hn) hγ_lt_one hn hC le_rfl hU_diag hAbsLU_le

/-- **Theorem 9.14**, Matrix-facing square-specialized rectangular dense
Doolittle certificate plus actual triangular solves with the natural `γ_n`
coefficient. -/
theorem higham9_14_matrix_source_f_bound_of_RectDoolittleDenseLoopCertificate_square_fl_triangular_solves_gamma
    (fp : FPModel) (n : ℕ)
    (A L_hat U_hat : Matrix (Fin n) (Fin n) ℝ)
    (b : Fin n → ℝ)
    (c : ℝ)
    (hn : gammaValid fp n)
    (hC : higham9_2_RectDoolittleDenseLoopCertificate
      (Nat.le_refl n) A L_hat U_hat fp)
    (hU_diag : ∀ i : Fin n, U_hat i i ≠ 0)
    (hAbsLU_le : ∀ i j : Fin n,
      ∑ k : Fin n, |L_hat i k| * |U_hat k j| ≤ c * |A i j|) :
    let y_hat := fl_forwardSub fp n L_hat b
    let x_hat := fl_backSub fp n U_hat y_hat
    ∃ DeltaA : Matrix (Fin n) (Fin n) ℝ,
      (∀ i j, |DeltaA i j| ≤
        c * higham9_14_f (gamma fp n) * |A i j|) ∧
      Matrix.mulVec (fun i j => A i j + DeltaA i j) x_hat = b :=
  higham9_14_matrix_source_f_bound_of_RectDoolittleDenseLoopCertificate_square_fl_triangular_solves_gamma_le
    fp n A L_hat U_hat b c (gamma fp n) (gamma_nonneg fp hn)
    hn hC le_rfl hU_diag hAbsLU_le

/-- **Theorem 9.14**, Matrix-facing square-specialized rectangular
absolute-budget Doolittle certificate plus actual triangular solves with the
natural `γ_n` coefficient. -/
theorem higham9_14_matrix_source_f_bound_of_RectDoolittleDenseLoopAbsBudgetCertificate_square_fl_triangular_solves_gamma
    (fp : FPModel) (n : ℕ)
    (A L_hat U_hat : Matrix (Fin n) (Fin n) ℝ)
    (b : Fin n → ℝ)
    (BU BL : Matrix (Fin n) (Fin n) ℝ)
    (c : ℝ)
    (hn : gammaValid fp n)
    (hC : higham9_2_RectDoolittleDenseLoopAbsBudgetCertificate
      (Nat.le_refl n) A L_hat U_hat fp BU BL)
    (hU_diag : ∀ i : Fin n, U_hat i i ≠ 0)
    (hAbsLU_le : ∀ i j : Fin n,
      ∑ k : Fin n, |L_hat i k| * |U_hat k j| ≤ c * |A i j|) :
    let y_hat := fl_forwardSub fp n L_hat b
    let x_hat := fl_backSub fp n U_hat y_hat
    ∃ DeltaA : Matrix (Fin n) (Fin n) ℝ,
      (∀ i j, |DeltaA i j| ≤
        c * higham9_14_f (gamma fp n) * |A i j|) ∧
      Matrix.mulVec (fun i j => A i j + DeltaA i j) x_hat = b :=
  higham9_14_matrix_source_f_bound_of_RectDoolittleDenseLoopAbsBudgetCertificate_square_fl_triangular_solves_gamma_le
    fp n A L_hat U_hat b BU BL c (gamma fp n)
    (gamma_nonneg fp hn) hn hC le_rfl hU_diag hAbsLU_le

/-- **Theorem 9.14**, Matrix-facing square-specialized rectangular dense
Doolittle certificate with Higham's final `h(γ_n)` coefficient. -/
theorem higham9_14_matrix_source_h_bound_of_RectDoolittleDenseLoopCertificate_square_fl_triangular_solves_gamma
    (fp : FPModel) (n : ℕ)
    (A L_hat U_hat : Matrix (Fin n) (Fin n) ℝ)
    (b : Fin n → ℝ)
    (hn : gammaValid fp n)
    (hγ_lt_one : gamma fp n < 1)
    (hC : higham9_2_RectDoolittleDenseLoopCertificate
      (Nat.le_refl n) A L_hat U_hat fp)
    (hU_diag : ∀ i : Fin n, U_hat i i ≠ 0)
    (hAbsLU_le : ∀ i j : Fin n,
      ∑ k : Fin n, |L_hat i k| * |U_hat k j| ≤ |A i j|) :
    let y_hat := fl_forwardSub fp n L_hat b
    let x_hat := fl_backSub fp n U_hat y_hat
    ∃ DeltaA : Matrix (Fin n) (Fin n) ℝ,
      (∀ i j, |DeltaA i j| ≤
        higham9_14_h (gamma fp n) * |A i j|) ∧
      Matrix.mulVec (fun i j => A i j + DeltaA i j) x_hat = b :=
  higham9_14_matrix_source_h_bound_of_RectDoolittleDenseLoopCertificate_square_fl_triangular_solves_gamma_le
    fp n A L_hat U_hat b (gamma fp n) (gamma_nonneg fp hn)
    hγ_lt_one hn hC le_rfl hU_diag hAbsLU_le

/-- **Theorem 9.14**, Matrix-facing square-specialized rectangular
absolute-budget Doolittle certificate with Higham's final `h(γ_n)`
coefficient. -/
theorem higham9_14_matrix_source_h_bound_of_RectDoolittleDenseLoopAbsBudgetCertificate_square_fl_triangular_solves_gamma
    (fp : FPModel) (n : ℕ)
    (A L_hat U_hat : Matrix (Fin n) (Fin n) ℝ)
    (b : Fin n → ℝ)
    (BU BL : Matrix (Fin n) (Fin n) ℝ)
    (hn : gammaValid fp n)
    (hγ_lt_one : gamma fp n < 1)
    (hC : higham9_2_RectDoolittleDenseLoopAbsBudgetCertificate
      (Nat.le_refl n) A L_hat U_hat fp BU BL)
    (hU_diag : ∀ i : Fin n, U_hat i i ≠ 0)
    (hAbsLU_le : ∀ i j : Fin n,
      ∑ k : Fin n, |L_hat i k| * |U_hat k j| ≤ |A i j|) :
    let y_hat := fl_forwardSub fp n L_hat b
    let x_hat := fl_backSub fp n U_hat y_hat
    ∃ DeltaA : Matrix (Fin n) (Fin n) ℝ,
      (∀ i j, |DeltaA i j| ≤
        higham9_14_h (gamma fp n) * |A i j|) ∧
      Matrix.mulVec (fun i j => A i j + DeltaA i j) x_hat = b :=
  higham9_14_matrix_source_h_bound_of_RectDoolittleDenseLoopAbsBudgetCertificate_square_fl_triangular_solves_gamma_le
    fp n A L_hat U_hat b BU BL (gamma fp n)
    (gamma_nonneg fp hn) hγ_lt_one hn hC le_rfl hU_diag hAbsLU_le

/-- **Theorem 9.14**, Matrix-facing square-specialized rectangular dense
Doolittle certificate plus actual triangular solves with optimal growth and
source `f(u)` coefficient. -/
theorem higham9_14_matrix_source_f_bound_of_RectDoolittleDenseLoopCertificate_square_fl_triangular_solves_absLU_le_absA_gamma_le
    (fp : FPModel) (n : ℕ)
    (A L_hat U_hat : Matrix (Fin n) (Fin n) ℝ)
    (b : Fin n → ℝ)
    (u : ℝ) (hu : 0 ≤ u)
    (hn : gammaValid fp n)
    (hC : higham9_2_RectDoolittleDenseLoopCertificate
      (Nat.le_refl n) A L_hat U_hat fp)
    (hγ_le_u : gamma fp n ≤ u)
    (hU_diag : ∀ i : Fin n, U_hat i i ≠ 0)
    (hAbsLU_le : ∀ i j : Fin n,
      ∑ k : Fin n, |L_hat i k| * |U_hat k j| ≤ |A i j|) :
    let y_hat := fl_forwardSub fp n L_hat b
    let x_hat := fl_backSub fp n U_hat y_hat
    ∃ DeltaA : Matrix (Fin n) (Fin n) ℝ,
      (∀ i j, |DeltaA i j| ≤ higham9_14_f u * |A i j|) ∧
      Matrix.mulVec (fun i j => A i j + DeltaA i j) x_hat = b := by
  simpa [one_mul] using
    (higham9_14_matrix_source_f_bound_of_RectDoolittleDenseLoopCertificate_square_fl_triangular_solves_gamma_le
      fp n A L_hat U_hat b 1 u hu hn hC hγ_le_u hU_diag
      (fun i j => by simpa [one_mul] using hAbsLU_le i j))

/-- **Theorem 9.14**, Matrix-facing square-specialized rectangular
absolute-budget Doolittle certificate plus actual triangular solves with
optimal growth and source `f(u)` coefficient. -/
theorem higham9_14_matrix_source_f_bound_of_RectDoolittleDenseLoopAbsBudgetCertificate_square_fl_triangular_solves_absLU_le_absA_gamma_le
    (fp : FPModel) (n : ℕ)
    (A L_hat U_hat : Matrix (Fin n) (Fin n) ℝ)
    (b : Fin n → ℝ)
    (BU BL : Matrix (Fin n) (Fin n) ℝ)
    (u : ℝ) (hu : 0 ≤ u)
    (hn : gammaValid fp n)
    (hC : higham9_2_RectDoolittleDenseLoopAbsBudgetCertificate
      (Nat.le_refl n) A L_hat U_hat fp BU BL)
    (hγ_le_u : gamma fp n ≤ u)
    (hU_diag : ∀ i : Fin n, U_hat i i ≠ 0)
    (hAbsLU_le : ∀ i j : Fin n,
      ∑ k : Fin n, |L_hat i k| * |U_hat k j| ≤ |A i j|) :
    let y_hat := fl_forwardSub fp n L_hat b
    let x_hat := fl_backSub fp n U_hat y_hat
    ∃ DeltaA : Matrix (Fin n) (Fin n) ℝ,
      (∀ i j, |DeltaA i j| ≤ higham9_14_f u * |A i j|) ∧
      Matrix.mulVec (fun i j => A i j + DeltaA i j) x_hat = b := by
  simpa [one_mul] using
    (higham9_14_matrix_source_f_bound_of_RectDoolittleDenseLoopAbsBudgetCertificate_square_fl_triangular_solves_gamma_le
      fp n A L_hat U_hat b BU BL 1 u hu hn hC hγ_le_u hU_diag
      (fun i j => by simpa [one_mul] using hAbsLU_le i j))

/-- **Theorem 9.14**, Matrix-facing square-specialized rectangular dense
Doolittle certificate plus actual triangular solves with optimal growth and the
natural source `f(γ_n)` coefficient. -/
theorem higham9_14_matrix_source_f_bound_of_RectDoolittleDenseLoopCertificate_square_fl_triangular_solves_absLU_le_absA_gamma
    (fp : FPModel) (n : ℕ)
    (A L_hat U_hat : Matrix (Fin n) (Fin n) ℝ)
    (b : Fin n → ℝ)
    (hn : gammaValid fp n)
    (hC : higham9_2_RectDoolittleDenseLoopCertificate
      (Nat.le_refl n) A L_hat U_hat fp)
    (hU_diag : ∀ i : Fin n, U_hat i i ≠ 0)
    (hAbsLU_le : ∀ i j : Fin n,
      ∑ k : Fin n, |L_hat i k| * |U_hat k j| ≤ |A i j|) :
    let y_hat := fl_forwardSub fp n L_hat b
    let x_hat := fl_backSub fp n U_hat y_hat
    ∃ DeltaA : Matrix (Fin n) (Fin n) ℝ,
      (∀ i j, |DeltaA i j| ≤
        higham9_14_f (gamma fp n) * |A i j|) ∧
      Matrix.mulVec (fun i j => A i j + DeltaA i j) x_hat = b := by
  simpa [one_mul] using
    (higham9_14_matrix_source_f_bound_of_RectDoolittleDenseLoopCertificate_square_fl_triangular_solves_gamma
      fp n A L_hat U_hat b 1 hn hC hU_diag
      (fun i j => by simpa [one_mul] using hAbsLU_le i j))

/-- **Theorem 9.14**, Matrix-facing square-specialized rectangular
absolute-budget Doolittle certificate plus actual triangular solves with
optimal growth and the natural source `f(γ_n)` coefficient. -/
theorem higham9_14_matrix_source_f_bound_of_RectDoolittleDenseLoopAbsBudgetCertificate_square_fl_triangular_solves_absLU_le_absA_gamma
    (fp : FPModel) (n : ℕ)
    (A L_hat U_hat : Matrix (Fin n) (Fin n) ℝ)
    (b : Fin n → ℝ)
    (BU BL : Matrix (Fin n) (Fin n) ℝ)
    (hn : gammaValid fp n)
    (hC : higham9_2_RectDoolittleDenseLoopAbsBudgetCertificate
      (Nat.le_refl n) A L_hat U_hat fp BU BL)
    (hU_diag : ∀ i : Fin n, U_hat i i ≠ 0)
    (hAbsLU_le : ∀ i j : Fin n,
      ∑ k : Fin n, |L_hat i k| * |U_hat k j| ≤ |A i j|) :
    let y_hat := fl_forwardSub fp n L_hat b
    let x_hat := fl_backSub fp n U_hat y_hat
    ∃ DeltaA : Matrix (Fin n) (Fin n) ℝ,
      (∀ i j, |DeltaA i j| ≤
        higham9_14_f (gamma fp n) * |A i j|) ∧
      Matrix.mulVec (fun i j => A i j + DeltaA i j) x_hat = b := by
  simpa [one_mul] using
    (higham9_14_matrix_source_f_bound_of_RectDoolittleDenseLoopAbsBudgetCertificate_square_fl_triangular_solves_gamma
      fp n A L_hat U_hat b BU BL 1 hn hC hU_diag
      (fun i j => by simpa [one_mul] using hAbsLU_le i j))

/-- **Theorem 9.14**, Matrix-facing square-specialized rectangular dense
Doolittle certificate plus actual triangular solves with optimal growth and
final `h(u)` coefficient. -/
theorem higham9_14_matrix_source_h_bound_of_RectDoolittleDenseLoopCertificate_square_fl_triangular_solves_absLU_le_absA_gamma_le
    (fp : FPModel) (n : ℕ)
    (A L_hat U_hat : Matrix (Fin n) (Fin n) ℝ)
    (b : Fin n → ℝ)
    (u : ℝ) (hu : 0 ≤ u) (hu_lt_one : u < 1)
    (hn : gammaValid fp n)
    (hC : higham9_2_RectDoolittleDenseLoopCertificate
      (Nat.le_refl n) A L_hat U_hat fp)
    (hγ_le_u : gamma fp n ≤ u)
    (hU_diag : ∀ i : Fin n, U_hat i i ≠ 0)
    (hAbsLU_le : ∀ i j : Fin n,
      ∑ k : Fin n, |L_hat i k| * |U_hat k j| ≤ |A i j|) :
    let y_hat := fl_forwardSub fp n L_hat b
    let x_hat := fl_backSub fp n U_hat y_hat
    ∃ DeltaA : Matrix (Fin n) (Fin n) ℝ,
      (∀ i j, |DeltaA i j| ≤ higham9_14_h u * |A i j|) ∧
      Matrix.mulVec (fun i j => A i j + DeltaA i j) x_hat = b :=
  higham9_14_matrix_source_h_bound_of_RectDoolittleDenseLoopCertificate_square_fl_triangular_solves_gamma_le
    fp n A L_hat U_hat b u hu hu_lt_one hn hC hγ_le_u hU_diag hAbsLU_le

/-- **Theorem 9.14**, Matrix-facing square-specialized rectangular
absolute-budget Doolittle certificate plus actual triangular solves with
optimal growth and final `h(u)` coefficient. -/
theorem higham9_14_matrix_source_h_bound_of_RectDoolittleDenseLoopAbsBudgetCertificate_square_fl_triangular_solves_absLU_le_absA_gamma_le
    (fp : FPModel) (n : ℕ)
    (A L_hat U_hat : Matrix (Fin n) (Fin n) ℝ)
    (b : Fin n → ℝ)
    (BU BL : Matrix (Fin n) (Fin n) ℝ)
    (u : ℝ) (hu : 0 ≤ u) (hu_lt_one : u < 1)
    (hn : gammaValid fp n)
    (hC : higham9_2_RectDoolittleDenseLoopAbsBudgetCertificate
      (Nat.le_refl n) A L_hat U_hat fp BU BL)
    (hγ_le_u : gamma fp n ≤ u)
    (hU_diag : ∀ i : Fin n, U_hat i i ≠ 0)
    (hAbsLU_le : ∀ i j : Fin n,
      ∑ k : Fin n, |L_hat i k| * |U_hat k j| ≤ |A i j|) :
    let y_hat := fl_forwardSub fp n L_hat b
    let x_hat := fl_backSub fp n U_hat y_hat
    ∃ DeltaA : Matrix (Fin n) (Fin n) ℝ,
      (∀ i j, |DeltaA i j| ≤ higham9_14_h u * |A i j|) ∧
      Matrix.mulVec (fun i j => A i j + DeltaA i j) x_hat = b :=
  higham9_14_matrix_source_h_bound_of_RectDoolittleDenseLoopAbsBudgetCertificate_square_fl_triangular_solves_gamma_le
    fp n A L_hat U_hat b BU BL u hu hu_lt_one hn hC hγ_le_u hU_diag hAbsLU_le

/-- **Theorem 9.14**, Matrix-facing square-specialized rectangular dense
Doolittle certificate plus actual triangular solves with optimal growth and
final `h(γ_n)` coefficient. -/
theorem higham9_14_matrix_source_h_bound_of_RectDoolittleDenseLoopCertificate_square_fl_triangular_solves_absLU_le_absA_gamma
    (fp : FPModel) (n : ℕ)
    (A L_hat U_hat : Matrix (Fin n) (Fin n) ℝ)
    (b : Fin n → ℝ)
    (hn : gammaValid fp n)
    (hγ_lt_one : gamma fp n < 1)
    (hC : higham9_2_RectDoolittleDenseLoopCertificate
      (Nat.le_refl n) A L_hat U_hat fp)
    (hU_diag : ∀ i : Fin n, U_hat i i ≠ 0)
    (hAbsLU_le : ∀ i j : Fin n,
      ∑ k : Fin n, |L_hat i k| * |U_hat k j| ≤ |A i j|) :
    let y_hat := fl_forwardSub fp n L_hat b
    let x_hat := fl_backSub fp n U_hat y_hat
    ∃ DeltaA : Matrix (Fin n) (Fin n) ℝ,
      (∀ i j, |DeltaA i j| ≤
        higham9_14_h (gamma fp n) * |A i j|) ∧
      Matrix.mulVec (fun i j => A i j + DeltaA i j) x_hat = b :=
  higham9_14_matrix_source_h_bound_of_RectDoolittleDenseLoopCertificate_square_fl_triangular_solves_gamma
    fp n A L_hat U_hat b hn hγ_lt_one hC hU_diag hAbsLU_le

/-- **Theorem 9.14**, Matrix-facing square-specialized rectangular
absolute-budget Doolittle certificate plus actual triangular solves with
optimal growth and final `h(γ_n)` coefficient. -/
theorem higham9_14_matrix_source_h_bound_of_RectDoolittleDenseLoopAbsBudgetCertificate_square_fl_triangular_solves_absLU_le_absA_gamma
    (fp : FPModel) (n : ℕ)
    (A L_hat U_hat : Matrix (Fin n) (Fin n) ℝ)
    (b : Fin n → ℝ)
    (BU BL : Matrix (Fin n) (Fin n) ℝ)
    (hn : gammaValid fp n)
    (hγ_lt_one : gamma fp n < 1)
    (hC : higham9_2_RectDoolittleDenseLoopAbsBudgetCertificate
      (Nat.le_refl n) A L_hat U_hat fp BU BL)
    (hU_diag : ∀ i : Fin n, U_hat i i ≠ 0)
    (hAbsLU_le : ∀ i j : Fin n,
      ∑ k : Fin n, |L_hat i k| * |U_hat k j| ≤ |A i j|) :
    let y_hat := fl_forwardSub fp n L_hat b
    let x_hat := fl_backSub fp n U_hat y_hat
    ∃ DeltaA : Matrix (Fin n) (Fin n) ℝ,
      (∀ i j, |DeltaA i j| ≤
        higham9_14_h (gamma fp n) * |A i j|) ∧
      Matrix.mulVec (fun i j => A i j + DeltaA i j) x_hat = b :=
  higham9_14_matrix_source_h_bound_of_RectDoolittleDenseLoopAbsBudgetCertificate_square_fl_triangular_solves_gamma
    fp n A L_hat U_hat b BU BL hn hγ_lt_one hC hU_diag hAbsLU_le

/-- **Theorem 9.14**, square-specialized rectangular dense Doolittle
certificate with a constant-growth final `h(u)` bound. -/
theorem higham9_14_source_h_bound_of_RectDoolittleDenseLoopCertificate_square_fl_triangular_solves_const_gamma_le
    (fp : FPModel) (n : ℕ)
    (A L_hat U_hat : Fin n → Fin n → ℝ)
    (b : Fin n → ℝ)
    (c u : ℝ) (hc : 0 ≤ c) (hu : 0 ≤ u) (hu_lt_one : u < 1)
    (hn : gammaValid fp n)
    (hC : higham9_2_RectDoolittleDenseLoopCertificate
      (Nat.le_refl n) A L_hat U_hat fp)
    (hγ_le_u : gamma fp n ≤ u)
    (hU_diag : ∀ i : Fin n, U_hat i i ≠ 0)
    (hAbsLU_le : ∀ i j : Fin n,
      ∑ k : Fin n, |L_hat i k| * |U_hat k j| ≤ c * |A i j|) :
    let y_hat := fl_forwardSub fp n L_hat b
    let x_hat := fl_backSub fp n U_hat y_hat
    ∃ DeltaA : Fin n → Fin n → ℝ,
      (∀ i j, |DeltaA i j| ≤ c * higham9_14_h u * |A i j|) ∧
      (∀ i, ∑ j : Fin n, (A i j + DeltaA i j) * x_hat j = b i) :=
  higham9_14_source_h_bound_of_DoolittleDenseLoopCertificate_fl_triangular_solves_const_gamma_le
    fp n A L_hat U_hat b c u hc hu hu_lt_one hn
    (higham9_2_rectDenseLoopCertificate_to_squareDenseLoopCertificate hC)
    hγ_le_u hU_diag hAbsLU_le

/-- **Theorem 9.14**, square-specialized rectangular absolute-budget
Doolittle certificate with a constant-growth final `h(u)` bound. -/
theorem higham9_14_source_h_bound_of_RectDoolittleDenseLoopAbsBudgetCertificate_square_fl_triangular_solves_const_gamma_le
    (fp : FPModel) (n : ℕ)
    (A L_hat U_hat : Fin n → Fin n → ℝ)
    (b : Fin n → ℝ)
    (BU BL : Fin n → Fin n → ℝ)
    (c u : ℝ) (hc : 0 ≤ c) (hu : 0 ≤ u) (hu_lt_one : u < 1)
    (hn : gammaValid fp n)
    (hC : higham9_2_RectDoolittleDenseLoopAbsBudgetCertificate
      (Nat.le_refl n) A L_hat U_hat fp BU BL)
    (hγ_le_u : gamma fp n ≤ u)
    (hU_diag : ∀ i : Fin n, U_hat i i ≠ 0)
    (hAbsLU_le : ∀ i j : Fin n,
      ∑ k : Fin n, |L_hat i k| * |U_hat k j| ≤ c * |A i j|) :
    let y_hat := fl_forwardSub fp n L_hat b
    let x_hat := fl_backSub fp n U_hat y_hat
    ∃ DeltaA : Fin n → Fin n → ℝ,
      (∀ i j, |DeltaA i j| ≤ c * higham9_14_h u * |A i j|) ∧
      (∀ i, ∑ j : Fin n, (A i j + DeltaA i j) * x_hat j = b i) :=
  higham9_14_source_h_bound_of_DoolittleDenseLoopAbsBudgetCertificate_fl_triangular_solves_const_gamma_le
    fp n A L_hat U_hat b BU BL c u hc hu hu_lt_one hn
    (higham9_2_rectAbsBudgetCertificate_to_squareAbsBudgetCertificate hC)
    hγ_le_u hU_diag hAbsLU_le

/-- **Theorem 9.14**, square-specialized rectangular dense Doolittle
certificate plus actual triangular solves with the natural `γ_n` coefficient. -/
theorem higham9_14_source_f_bound_of_RectDoolittleDenseLoopCertificate_square_fl_triangular_solves_gamma
    (fp : FPModel) (n : ℕ)
    (A L_hat U_hat : Fin n → Fin n → ℝ)
    (b : Fin n → ℝ)
    (c : ℝ)
    (hn : gammaValid fp n)
    (hC : higham9_2_RectDoolittleDenseLoopCertificate
      (Nat.le_refl n) A L_hat U_hat fp)
    (hU_diag : ∀ i : Fin n, U_hat i i ≠ 0)
    (hAbsLU_le : ∀ i j : Fin n,
      ∑ k : Fin n, |L_hat i k| * |U_hat k j| ≤ c * |A i j|) :
    let y_hat := fl_forwardSub fp n L_hat b
    let x_hat := fl_backSub fp n U_hat y_hat
    ∃ DeltaA : Fin n → Fin n → ℝ,
      (∀ i j, |DeltaA i j| ≤
        c * higham9_14_f (gamma fp n) * |A i j|) ∧
      (∀ i, ∑ j : Fin n, (A i j + DeltaA i j) * x_hat j = b i) :=
  higham9_14_source_f_bound_of_RectDoolittleDenseLoopCertificate_square_fl_triangular_solves_gamma_le
    fp n A L_hat U_hat b c (gamma fp n) (gamma_nonneg fp hn)
    hn hC le_rfl hU_diag hAbsLU_le

/-- **Theorem 9.14**, square-specialized rectangular absolute-budget
Doolittle certificate plus actual triangular solves with the natural `γ_n`
coefficient. -/
theorem higham9_14_source_f_bound_of_RectDoolittleDenseLoopAbsBudgetCertificate_square_fl_triangular_solves_gamma
    (fp : FPModel) (n : ℕ)
    (A L_hat U_hat : Fin n → Fin n → ℝ)
    (b : Fin n → ℝ)
    (BU BL : Fin n → Fin n → ℝ)
    (c : ℝ)
    (hn : gammaValid fp n)
    (hC : higham9_2_RectDoolittleDenseLoopAbsBudgetCertificate
      (Nat.le_refl n) A L_hat U_hat fp BU BL)
    (hU_diag : ∀ i : Fin n, U_hat i i ≠ 0)
    (hAbsLU_le : ∀ i j : Fin n,
      ∑ k : Fin n, |L_hat i k| * |U_hat k j| ≤ c * |A i j|) :
    let y_hat := fl_forwardSub fp n L_hat b
    let x_hat := fl_backSub fp n U_hat y_hat
    ∃ DeltaA : Fin n → Fin n → ℝ,
      (∀ i j, |DeltaA i j| ≤
        c * higham9_14_f (gamma fp n) * |A i j|) ∧
      (∀ i, ∑ j : Fin n, (A i j + DeltaA i j) * x_hat j = b i) :=
  higham9_14_source_f_bound_of_RectDoolittleDenseLoopAbsBudgetCertificate_square_fl_triangular_solves_gamma_le
    fp n A L_hat U_hat b BU BL c (gamma fp n)
    (gamma_nonneg fp hn) hn hC le_rfl hU_diag hAbsLU_le

/-- **Theorem 9.14**, square-specialized rectangular dense Doolittle
certificate plus actual triangular solves with optimal growth and source
`f(u)` coefficient. -/
theorem higham9_14_source_f_bound_of_RectDoolittleDenseLoopCertificate_square_fl_triangular_solves_absLU_le_absA_gamma_le
    (fp : FPModel) (n : ℕ)
    (A L_hat U_hat : Fin n → Fin n → ℝ)
    (b : Fin n → ℝ)
    (u : ℝ) (hu : 0 ≤ u)
    (hn : gammaValid fp n)
    (hC : higham9_2_RectDoolittleDenseLoopCertificate
      (Nat.le_refl n) A L_hat U_hat fp)
    (hγ_le_u : gamma fp n ≤ u)
    (hU_diag : ∀ i : Fin n, U_hat i i ≠ 0)
    (hAbsLU_le : ∀ i j : Fin n,
      ∑ k : Fin n, |L_hat i k| * |U_hat k j| ≤ |A i j|) :
    let y_hat := fl_forwardSub fp n L_hat b
    let x_hat := fl_backSub fp n U_hat y_hat
    ∃ DeltaA : Fin n → Fin n → ℝ,
      (∀ i j, |DeltaA i j| ≤ higham9_14_f u * |A i j|) ∧
      (∀ i, ∑ j : Fin n, (A i j + DeltaA i j) * x_hat j = b i) := by
  simpa [one_mul] using
    (higham9_14_source_f_bound_of_RectDoolittleDenseLoopCertificate_square_fl_triangular_solves_gamma_le
      fp n A L_hat U_hat b 1 u hu hn hC hγ_le_u hU_diag
      (fun i j => by simpa [one_mul] using hAbsLU_le i j))

/-- **Theorem 9.14**, square-specialized rectangular absolute-budget
Doolittle certificate plus actual triangular solves with optimal growth and
source `f(u)` coefficient. -/
theorem higham9_14_source_f_bound_of_RectDoolittleDenseLoopAbsBudgetCertificate_square_fl_triangular_solves_absLU_le_absA_gamma_le
    (fp : FPModel) (n : ℕ)
    (A L_hat U_hat : Fin n → Fin n → ℝ)
    (b : Fin n → ℝ)
    (BU BL : Fin n → Fin n → ℝ)
    (u : ℝ) (hu : 0 ≤ u)
    (hn : gammaValid fp n)
    (hC : higham9_2_RectDoolittleDenseLoopAbsBudgetCertificate
      (Nat.le_refl n) A L_hat U_hat fp BU BL)
    (hγ_le_u : gamma fp n ≤ u)
    (hU_diag : ∀ i : Fin n, U_hat i i ≠ 0)
    (hAbsLU_le : ∀ i j : Fin n,
      ∑ k : Fin n, |L_hat i k| * |U_hat k j| ≤ |A i j|) :
    let y_hat := fl_forwardSub fp n L_hat b
    let x_hat := fl_backSub fp n U_hat y_hat
    ∃ DeltaA : Fin n → Fin n → ℝ,
      (∀ i j, |DeltaA i j| ≤ higham9_14_f u * |A i j|) ∧
      (∀ i, ∑ j : Fin n, (A i j + DeltaA i j) * x_hat j = b i) := by
  simpa [one_mul] using
    (higham9_14_source_f_bound_of_RectDoolittleDenseLoopAbsBudgetCertificate_square_fl_triangular_solves_gamma_le
      fp n A L_hat U_hat b BU BL 1 u hu hn hC hγ_le_u hU_diag
      (fun i j => by simpa [one_mul] using hAbsLU_le i j))

/-- **Theorem 9.14**, square-specialized rectangular dense Doolittle
certificate plus actual triangular solves with optimal growth and the natural
source `f(γ_n)` coefficient. -/
theorem higham9_14_source_f_bound_of_RectDoolittleDenseLoopCertificate_square_fl_triangular_solves_absLU_le_absA_gamma
    (fp : FPModel) (n : ℕ)
    (A L_hat U_hat : Fin n → Fin n → ℝ)
    (b : Fin n → ℝ)
    (hn : gammaValid fp n)
    (hC : higham9_2_RectDoolittleDenseLoopCertificate
      (Nat.le_refl n) A L_hat U_hat fp)
    (hU_diag : ∀ i : Fin n, U_hat i i ≠ 0)
    (hAbsLU_le : ∀ i j : Fin n,
      ∑ k : Fin n, |L_hat i k| * |U_hat k j| ≤ |A i j|) :
    let y_hat := fl_forwardSub fp n L_hat b
    let x_hat := fl_backSub fp n U_hat y_hat
    ∃ DeltaA : Fin n → Fin n → ℝ,
      (∀ i j, |DeltaA i j| ≤
        higham9_14_f (gamma fp n) * |A i j|) ∧
      (∀ i, ∑ j : Fin n, (A i j + DeltaA i j) * x_hat j = b i) := by
  simpa [one_mul] using
    (higham9_14_source_f_bound_of_RectDoolittleDenseLoopCertificate_square_fl_triangular_solves_gamma
      fp n A L_hat U_hat b 1 hn hC hU_diag
      (fun i j => by simpa [one_mul] using hAbsLU_le i j))

/-- **Theorem 9.14**, square-specialized rectangular absolute-budget
Doolittle certificate plus actual triangular solves with optimal growth and
the natural source `f(γ_n)` coefficient. -/
theorem higham9_14_source_f_bound_of_RectDoolittleDenseLoopAbsBudgetCertificate_square_fl_triangular_solves_absLU_le_absA_gamma
    (fp : FPModel) (n : ℕ)
    (A L_hat U_hat : Fin n → Fin n → ℝ)
    (b : Fin n → ℝ)
    (BU BL : Fin n → Fin n → ℝ)
    (hn : gammaValid fp n)
    (hC : higham9_2_RectDoolittleDenseLoopAbsBudgetCertificate
      (Nat.le_refl n) A L_hat U_hat fp BU BL)
    (hU_diag : ∀ i : Fin n, U_hat i i ≠ 0)
    (hAbsLU_le : ∀ i j : Fin n,
      ∑ k : Fin n, |L_hat i k| * |U_hat k j| ≤ |A i j|) :
    let y_hat := fl_forwardSub fp n L_hat b
    let x_hat := fl_backSub fp n U_hat y_hat
    ∃ DeltaA : Fin n → Fin n → ℝ,
      (∀ i j, |DeltaA i j| ≤
        higham9_14_f (gamma fp n) * |A i j|) ∧
      (∀ i, ∑ j : Fin n, (A i j + DeltaA i j) * x_hat j = b i) := by
  simpa [one_mul] using
    (higham9_14_source_f_bound_of_RectDoolittleDenseLoopAbsBudgetCertificate_square_fl_triangular_solves_gamma
      fp n A L_hat U_hat b BU BL 1 hn hC hU_diag
      (fun i j => by simpa [one_mul] using hAbsLU_le i j))

/-- **Theorem 9.14**, square-specialized rectangular dense Doolittle
certificate with Higham's final `h(γ_n)` coefficient. -/
theorem higham9_14_source_h_bound_of_RectDoolittleDenseLoopCertificate_square_fl_triangular_solves_gamma
    (fp : FPModel) (n : ℕ)
    (A L_hat U_hat : Fin n → Fin n → ℝ)
    (b : Fin n → ℝ)
    (hn : gammaValid fp n)
    (hγ_lt_one : gamma fp n < 1)
    (hC : higham9_2_RectDoolittleDenseLoopCertificate
      (Nat.le_refl n) A L_hat U_hat fp)
    (hU_diag : ∀ i : Fin n, U_hat i i ≠ 0)
    (hAbsLU_le : ∀ i j : Fin n,
      ∑ k : Fin n, |L_hat i k| * |U_hat k j| ≤ |A i j|) :
    let y_hat := fl_forwardSub fp n L_hat b
    let x_hat := fl_backSub fp n U_hat y_hat
    ∃ DeltaA : Fin n → Fin n → ℝ,
      (∀ i j, |DeltaA i j| ≤
        higham9_14_h (gamma fp n) * |A i j|) ∧
      (∀ i, ∑ j : Fin n, (A i j + DeltaA i j) * x_hat j = b i) :=
  higham9_14_source_h_bound_of_RectDoolittleDenseLoopCertificate_square_fl_triangular_solves_gamma_le
    fp n A L_hat U_hat b (gamma fp n) (gamma_nonneg fp hn)
    hγ_lt_one hn hC le_rfl hU_diag hAbsLU_le

/-- **Theorem 9.14**, square-specialized rectangular absolute-budget
Doolittle certificate with Higham's final `h(γ_n)` coefficient. -/
theorem higham9_14_source_h_bound_of_RectDoolittleDenseLoopAbsBudgetCertificate_square_fl_triangular_solves_gamma
    (fp : FPModel) (n : ℕ)
    (A L_hat U_hat : Fin n → Fin n → ℝ)
    (b : Fin n → ℝ)
    (BU BL : Fin n → Fin n → ℝ)
    (hn : gammaValid fp n)
    (hγ_lt_one : gamma fp n < 1)
    (hC : higham9_2_RectDoolittleDenseLoopAbsBudgetCertificate
      (Nat.le_refl n) A L_hat U_hat fp BU BL)
    (hU_diag : ∀ i : Fin n, U_hat i i ≠ 0)
    (hAbsLU_le : ∀ i j : Fin n,
      ∑ k : Fin n, |L_hat i k| * |U_hat k j| ≤ |A i j|) :
    let y_hat := fl_forwardSub fp n L_hat b
    let x_hat := fl_backSub fp n U_hat y_hat
    ∃ DeltaA : Fin n → Fin n → ℝ,
      (∀ i j, |DeltaA i j| ≤
        higham9_14_h (gamma fp n) * |A i j|) ∧
      (∀ i, ∑ j : Fin n, (A i j + DeltaA i j) * x_hat j = b i) :=
  higham9_14_source_h_bound_of_RectDoolittleDenseLoopAbsBudgetCertificate_square_fl_triangular_solves_gamma_le
    fp n A L_hat U_hat b BU BL (gamma fp n)
    (gamma_nonneg fp hn) hγ_lt_one hn hC le_rfl hU_diag hAbsLU_le

/-- **Theorem 9.14**, square-specialized rectangular dense Doolittle
certificate plus actual triangular solves with optimal growth and final
`h(u)` coefficient. -/
theorem higham9_14_source_h_bound_of_RectDoolittleDenseLoopCertificate_square_fl_triangular_solves_absLU_le_absA_gamma_le
    (fp : FPModel) (n : ℕ)
    (A L_hat U_hat : Fin n → Fin n → ℝ)
    (b : Fin n → ℝ)
    (u : ℝ) (hu : 0 ≤ u) (hu_lt_one : u < 1)
    (hn : gammaValid fp n)
    (hC : higham9_2_RectDoolittleDenseLoopCertificate
      (Nat.le_refl n) A L_hat U_hat fp)
    (hγ_le_u : gamma fp n ≤ u)
    (hU_diag : ∀ i : Fin n, U_hat i i ≠ 0)
    (hAbsLU_le : ∀ i j : Fin n,
      ∑ k : Fin n, |L_hat i k| * |U_hat k j| ≤ |A i j|) :
    let y_hat := fl_forwardSub fp n L_hat b
    let x_hat := fl_backSub fp n U_hat y_hat
    ∃ DeltaA : Fin n → Fin n → ℝ,
      (∀ i j, |DeltaA i j| ≤ higham9_14_h u * |A i j|) ∧
      (∀ i, ∑ j : Fin n, (A i j + DeltaA i j) * x_hat j = b i) :=
  higham9_14_source_h_bound_of_RectDoolittleDenseLoopCertificate_square_fl_triangular_solves_gamma_le
    fp n A L_hat U_hat b u hu hu_lt_one hn hC hγ_le_u hU_diag hAbsLU_le

/-- **Theorem 9.14**, square-specialized rectangular absolute-budget
Doolittle certificate plus actual triangular solves with optimal growth and
final `h(u)` coefficient. -/
theorem higham9_14_source_h_bound_of_RectDoolittleDenseLoopAbsBudgetCertificate_square_fl_triangular_solves_absLU_le_absA_gamma_le
    (fp : FPModel) (n : ℕ)
    (A L_hat U_hat : Fin n → Fin n → ℝ)
    (b : Fin n → ℝ)
    (BU BL : Fin n → Fin n → ℝ)
    (u : ℝ) (hu : 0 ≤ u) (hu_lt_one : u < 1)
    (hn : gammaValid fp n)
    (hC : higham9_2_RectDoolittleDenseLoopAbsBudgetCertificate
      (Nat.le_refl n) A L_hat U_hat fp BU BL)
    (hγ_le_u : gamma fp n ≤ u)
    (hU_diag : ∀ i : Fin n, U_hat i i ≠ 0)
    (hAbsLU_le : ∀ i j : Fin n,
      ∑ k : Fin n, |L_hat i k| * |U_hat k j| ≤ |A i j|) :
    let y_hat := fl_forwardSub fp n L_hat b
    let x_hat := fl_backSub fp n U_hat y_hat
    ∃ DeltaA : Fin n → Fin n → ℝ,
      (∀ i j, |DeltaA i j| ≤ higham9_14_h u * |A i j|) ∧
      (∀ i, ∑ j : Fin n, (A i j + DeltaA i j) * x_hat j = b i) :=
  higham9_14_source_h_bound_of_RectDoolittleDenseLoopAbsBudgetCertificate_square_fl_triangular_solves_gamma_le
    fp n A L_hat U_hat b BU BL u hu hu_lt_one hn hC hγ_le_u hU_diag hAbsLU_le

/-- **Theorem 9.14**, square-specialized rectangular dense Doolittle
certificate plus actual triangular solves with optimal growth and final
`h(γ_n)` coefficient. -/
theorem higham9_14_source_h_bound_of_RectDoolittleDenseLoopCertificate_square_fl_triangular_solves_absLU_le_absA_gamma
    (fp : FPModel) (n : ℕ)
    (A L_hat U_hat : Fin n → Fin n → ℝ)
    (b : Fin n → ℝ)
    (hn : gammaValid fp n)
    (hγ_lt_one : gamma fp n < 1)
    (hC : higham9_2_RectDoolittleDenseLoopCertificate
      (Nat.le_refl n) A L_hat U_hat fp)
    (hU_diag : ∀ i : Fin n, U_hat i i ≠ 0)
    (hAbsLU_le : ∀ i j : Fin n,
      ∑ k : Fin n, |L_hat i k| * |U_hat k j| ≤ |A i j|) :
    let y_hat := fl_forwardSub fp n L_hat b
    let x_hat := fl_backSub fp n U_hat y_hat
    ∃ DeltaA : Fin n → Fin n → ℝ,
      (∀ i j, |DeltaA i j| ≤
        higham9_14_h (gamma fp n) * |A i j|) ∧
      (∀ i, ∑ j : Fin n, (A i j + DeltaA i j) * x_hat j = b i) :=
  higham9_14_source_h_bound_of_RectDoolittleDenseLoopCertificate_square_fl_triangular_solves_gamma
    fp n A L_hat U_hat b hn hγ_lt_one hC hU_diag hAbsLU_le

/-- **Theorem 9.14**, square-specialized rectangular absolute-budget
Doolittle certificate plus actual triangular solves with optimal growth and
final `h(γ_n)` coefficient. -/
theorem higham9_14_source_h_bound_of_RectDoolittleDenseLoopAbsBudgetCertificate_square_fl_triangular_solves_absLU_le_absA_gamma
    (fp : FPModel) (n : ℕ)
    (A L_hat U_hat : Fin n → Fin n → ℝ)
    (b : Fin n → ℝ)
    (BU BL : Fin n → Fin n → ℝ)
    (hn : gammaValid fp n)
    (hγ_lt_one : gamma fp n < 1)
    (hC : higham9_2_RectDoolittleDenseLoopAbsBudgetCertificate
      (Nat.le_refl n) A L_hat U_hat fp BU BL)
    (hU_diag : ∀ i : Fin n, U_hat i i ≠ 0)
    (hAbsLU_le : ∀ i j : Fin n,
      ∑ k : Fin n, |L_hat i k| * |U_hat k j| ≤ |A i j|) :
    let y_hat := fl_forwardSub fp n L_hat b
    let x_hat := fl_backSub fp n U_hat y_hat
    ∃ DeltaA : Fin n → Fin n → ℝ,
      (∀ i j, |DeltaA i j| ≤
        higham9_14_h (gamma fp n) * |A i j|) ∧
      (∀ i, ∑ j : Fin n, (A i j + DeltaA i j) * x_hat j = b i) :=
  higham9_14_source_h_bound_of_RectDoolittleDenseLoopAbsBudgetCertificate_square_fl_triangular_solves_gamma
    fp n A L_hat U_hat b BU BL hn hγ_lt_one hC hU_diag hAbsLU_le

/-- **Theorem 9.14**, square-specialized rectangular dense Doolittle
certificate with a constant-growth final `h(γ_n)` coefficient. -/
theorem higham9_14_source_h_bound_of_RectDoolittleDenseLoopCertificate_square_fl_triangular_solves_const_gamma
    (fp : FPModel) (n : ℕ)
    (A L_hat U_hat : Fin n → Fin n → ℝ)
    (b : Fin n → ℝ)
    (c : ℝ) (hc : 0 ≤ c)
    (hn : gammaValid fp n)
    (hγ_lt_one : gamma fp n < 1)
    (hC : higham9_2_RectDoolittleDenseLoopCertificate
      (Nat.le_refl n) A L_hat U_hat fp)
    (hU_diag : ∀ i : Fin n, U_hat i i ≠ 0)
    (hAbsLU_le : ∀ i j : Fin n,
      ∑ k : Fin n, |L_hat i k| * |U_hat k j| ≤ c * |A i j|) :
    let y_hat := fl_forwardSub fp n L_hat b
    let x_hat := fl_backSub fp n U_hat y_hat
    ∃ DeltaA : Fin n → Fin n → ℝ,
      (∀ i j, |DeltaA i j| ≤
        c * higham9_14_h (gamma fp n) * |A i j|) ∧
      (∀ i, ∑ j : Fin n, (A i j + DeltaA i j) * x_hat j = b i) :=
  higham9_14_source_h_bound_of_RectDoolittleDenseLoopCertificate_square_fl_triangular_solves_const_gamma_le
    fp n A L_hat U_hat b c (gamma fp n) hc (gamma_nonneg fp hn)
    hγ_lt_one hn hC le_rfl hU_diag hAbsLU_le

/-- **Theorem 9.14**, square-specialized rectangular absolute-budget
Doolittle certificate with a constant-growth final `h(γ_n)` coefficient. -/
theorem higham9_14_source_h_bound_of_RectDoolittleDenseLoopAbsBudgetCertificate_square_fl_triangular_solves_const_gamma
    (fp : FPModel) (n : ℕ)
    (A L_hat U_hat : Fin n → Fin n → ℝ)
    (b : Fin n → ℝ)
    (BU BL : Fin n → Fin n → ℝ)
    (c : ℝ) (hc : 0 ≤ c)
    (hn : gammaValid fp n)
    (hγ_lt_one : gamma fp n < 1)
    (hC : higham9_2_RectDoolittleDenseLoopAbsBudgetCertificate
      (Nat.le_refl n) A L_hat U_hat fp BU BL)
    (hU_diag : ∀ i : Fin n, U_hat i i ≠ 0)
    (hAbsLU_le : ∀ i j : Fin n,
      ∑ k : Fin n, |L_hat i k| * |U_hat k j| ≤ c * |A i j|) :
    let y_hat := fl_forwardSub fp n L_hat b
    let x_hat := fl_backSub fp n U_hat y_hat
    ∃ DeltaA : Fin n → Fin n → ℝ,
      (∀ i j, |DeltaA i j| ≤
        c * higham9_14_h (gamma fp n) * |A i j|) ∧
      (∀ i, ∑ j : Fin n, (A i j + DeltaA i j) * x_hat j = b i) :=
  higham9_14_source_h_bound_of_RectDoolittleDenseLoopAbsBudgetCertificate_square_fl_triangular_solves_const_gamma_le
    fp n A L_hat U_hat b BU BL c (gamma fp n) hc
    (gamma_nonneg fp hn) hγ_lt_one hn hC le_rfl hU_diag hAbsLU_le

/-- **Theorem 9.14**, square-specialized rectangular rounded-stage trace plus
actual triangular solves.

The rounded-stage trace first supplies the rectangular dense-loop certificate,
then the existing rectangular dense-loop source wrapper gives the source-facing
`f(u)` bound. -/
theorem higham9_14_source_f_bound_of_RectDoolittleRoundedStageTrace_square_fl_triangular_solves_gamma_le
    (fp : FPModel) (n : ℕ)
    (A L_hat U_hat : Fin n → Fin n → ℝ)
    (b : Fin n → ℝ)
    (c u : ℝ) (hu : 0 ≤ u)
    (hn : gammaValid fp n)
    (hT : higham9_2_RectDoolittleRoundedStageTrace
      (Nat.le_refl n) A L_hat U_hat fp)
    (hU_diag : ∀ i : Fin n, U_hat i i ≠ 0)
    (hU_budget_le : ∀ k j : Fin n, k.val ≤ j.val →
      higham9_2_rectDoolittleUAbsBudget fp (Nat.le_refl n)
          A L_hat U_hat k j ≤ gamma fp n * |U_hat k j|)
    (hL_budget_le : ∀ i k : Fin n, k.val < i.val →
      higham9_2_rectDoolittleLAbsBudget fp A L_hat U_hat i k ≤
        gamma fp n * |L_hat i k * U_hat k k|)
    (hγ_le_u : gamma fp n ≤ u)
    (hAbsLU_le : ∀ i j : Fin n,
      ∑ k : Fin n, |L_hat i k| * |U_hat k j| ≤ c * |A i j|) :
    let y_hat := fl_forwardSub fp n L_hat b
    let x_hat := fl_backSub fp n U_hat y_hat
    ∃ DeltaA : Fin n → Fin n → ℝ,
      (∀ i j, |DeltaA i j| ≤ c * higham9_14_f u * |A i j|) ∧
      (∀ i, ∑ j : Fin n, (A i j + DeltaA i j) * x_hat j = b i) :=
  higham9_14_source_f_bound_of_RectDoolittleDenseLoopCertificate_square_fl_triangular_solves_gamma_le
    fp n A L_hat U_hat b c u hu hn
    (higham9_2_rectRoundedStageTrace_to_rectDenseLoopCertificate
      hT hU_diag hn hU_budget_le hL_budget_le)
    hγ_le_u hU_diag hAbsLU_le

/-- **Theorem 9.14**, square-specialized rectangular rounded-stage trace with
the final exact-growth `h(u)` bound. -/
theorem higham9_14_source_h_bound_of_RectDoolittleRoundedStageTrace_square_fl_triangular_solves_gamma_le
    (fp : FPModel) (n : ℕ)
    (A L_hat U_hat : Fin n → Fin n → ℝ)
    (b : Fin n → ℝ)
    (u : ℝ) (hu : 0 ≤ u) (hu_lt_one : u < 1)
    (hn : gammaValid fp n)
    (hT : higham9_2_RectDoolittleRoundedStageTrace
      (Nat.le_refl n) A L_hat U_hat fp)
    (hU_diag : ∀ i : Fin n, U_hat i i ≠ 0)
    (hU_budget_le : ∀ k j : Fin n, k.val ≤ j.val →
      higham9_2_rectDoolittleUAbsBudget fp (Nat.le_refl n)
          A L_hat U_hat k j ≤ gamma fp n * |U_hat k j|)
    (hL_budget_le : ∀ i k : Fin n, k.val < i.val →
      higham9_2_rectDoolittleLAbsBudget fp A L_hat U_hat i k ≤
        gamma fp n * |L_hat i k * U_hat k k|)
    (hγ_le_u : gamma fp n ≤ u)
    (hAbsLU_le : ∀ i j : Fin n,
      ∑ k : Fin n, |L_hat i k| * |U_hat k j| ≤ |A i j|) :
    let y_hat := fl_forwardSub fp n L_hat b
    let x_hat := fl_backSub fp n U_hat y_hat
    ∃ DeltaA : Fin n → Fin n → ℝ,
      (∀ i j, |DeltaA i j| ≤ higham9_14_h u * |A i j|) ∧
      (∀ i, ∑ j : Fin n, (A i j + DeltaA i j) * x_hat j = b i) :=
  higham9_14_source_h_bound_of_RectDoolittleDenseLoopCertificate_square_fl_triangular_solves_gamma_le
    fp n A L_hat U_hat b u hu hu_lt_one hn
    (higham9_2_rectRoundedStageTrace_to_rectDenseLoopCertificate
      hT hU_diag hn hU_budget_le hL_budget_le)
    hγ_le_u hU_diag hAbsLU_le

/-- **Theorem 9.14**, square-specialized rectangular rounded-stage trace with
a supplied constant-growth final `h(u)` bound. -/
theorem higham9_14_source_h_bound_of_RectDoolittleRoundedStageTrace_square_fl_triangular_solves_const_gamma_le
    (fp : FPModel) (n : ℕ)
    (A L_hat U_hat : Fin n → Fin n → ℝ)
    (b : Fin n → ℝ)
    (c u : ℝ) (hc : 0 ≤ c) (hu : 0 ≤ u) (hu_lt_one : u < 1)
    (hn : gammaValid fp n)
    (hT : higham9_2_RectDoolittleRoundedStageTrace
      (Nat.le_refl n) A L_hat U_hat fp)
    (hU_diag : ∀ i : Fin n, U_hat i i ≠ 0)
    (hU_budget_le : ∀ k j : Fin n, k.val ≤ j.val →
      higham9_2_rectDoolittleUAbsBudget fp (Nat.le_refl n)
          A L_hat U_hat k j ≤ gamma fp n * |U_hat k j|)
    (hL_budget_le : ∀ i k : Fin n, k.val < i.val →
      higham9_2_rectDoolittleLAbsBudget fp A L_hat U_hat i k ≤
        gamma fp n * |L_hat i k * U_hat k k|)
    (hγ_le_u : gamma fp n ≤ u)
    (hAbsLU_le : ∀ i j : Fin n,
      ∑ k : Fin n, |L_hat i k| * |U_hat k j| ≤ c * |A i j|) :
    let y_hat := fl_forwardSub fp n L_hat b
    let x_hat := fl_backSub fp n U_hat y_hat
    ∃ DeltaA : Fin n → Fin n → ℝ,
      (∀ i j, |DeltaA i j| ≤ c * higham9_14_h u * |A i j|) ∧
      (∀ i, ∑ j : Fin n, (A i j + DeltaA i j) * x_hat j = b i) :=
  higham9_14_source_h_bound_of_RectDoolittleDenseLoopCertificate_square_fl_triangular_solves_const_gamma_le
    fp n A L_hat U_hat b c u hc hu hu_lt_one hn
    (higham9_2_rectRoundedStageTrace_to_rectDenseLoopCertificate
      hT hU_diag hn hU_budget_le hL_budget_le)
    hγ_le_u hU_diag hAbsLU_le

/-- **Theorem 9.14**, square-specialized rectangular rounded-stage trace with
the natural `γ_n` source coefficient. -/
theorem higham9_14_source_f_bound_of_RectDoolittleRoundedStageTrace_square_fl_triangular_solves_gamma
    (fp : FPModel) (n : ℕ)
    (A L_hat U_hat : Fin n → Fin n → ℝ)
    (b : Fin n → ℝ)
    (c : ℝ)
    (hn : gammaValid fp n)
    (hT : higham9_2_RectDoolittleRoundedStageTrace
      (Nat.le_refl n) A L_hat U_hat fp)
    (hU_diag : ∀ i : Fin n, U_hat i i ≠ 0)
    (hU_budget_le : ∀ k j : Fin n, k.val ≤ j.val →
      higham9_2_rectDoolittleUAbsBudget fp (Nat.le_refl n)
          A L_hat U_hat k j ≤ gamma fp n * |U_hat k j|)
    (hL_budget_le : ∀ i k : Fin n, k.val < i.val →
      higham9_2_rectDoolittleLAbsBudget fp A L_hat U_hat i k ≤
        gamma fp n * |L_hat i k * U_hat k k|)
    (hAbsLU_le : ∀ i j : Fin n,
      ∑ k : Fin n, |L_hat i k| * |U_hat k j| ≤ c * |A i j|) :
    let y_hat := fl_forwardSub fp n L_hat b
    let x_hat := fl_backSub fp n U_hat y_hat
    ∃ DeltaA : Fin n → Fin n → ℝ,
      (∀ i j, |DeltaA i j| ≤
        c * higham9_14_f (gamma fp n) * |A i j|) ∧
      (∀ i, ∑ j : Fin n, (A i j + DeltaA i j) * x_hat j = b i) :=
  higham9_14_source_f_bound_of_RectDoolittleRoundedStageTrace_square_fl_triangular_solves_gamma_le
    fp n A L_hat U_hat b c (gamma fp n) (gamma_nonneg fp hn)
    hn hT hU_diag hU_budget_le hL_budget_le le_rfl hAbsLU_le

/-- **Theorem 9.14**, square-specialized rectangular rounded-stage trace with
optimal growth and source `f(u)` coefficient. -/
theorem higham9_14_source_f_bound_of_RectDoolittleRoundedStageTrace_square_fl_triangular_solves_absLU_le_absA_gamma_le
    (fp : FPModel) (n : ℕ)
    (A L_hat U_hat : Fin n → Fin n → ℝ)
    (b : Fin n → ℝ)
    (u : ℝ) (hu : 0 ≤ u)
    (hn : gammaValid fp n)
    (hT : higham9_2_RectDoolittleRoundedStageTrace
      (Nat.le_refl n) A L_hat U_hat fp)
    (hU_diag : ∀ i : Fin n, U_hat i i ≠ 0)
    (hU_budget_le : ∀ k j : Fin n, k.val ≤ j.val →
      higham9_2_rectDoolittleUAbsBudget fp (Nat.le_refl n)
          A L_hat U_hat k j ≤ gamma fp n * |U_hat k j|)
    (hL_budget_le : ∀ i k : Fin n, k.val < i.val →
      higham9_2_rectDoolittleLAbsBudget fp A L_hat U_hat i k ≤
        gamma fp n * |L_hat i k * U_hat k k|)
    (hγ_le_u : gamma fp n ≤ u)
    (hAbsLU_le : ∀ i j : Fin n,
      ∑ k : Fin n, |L_hat i k| * |U_hat k j| ≤ |A i j|) :
    let y_hat := fl_forwardSub fp n L_hat b
    let x_hat := fl_backSub fp n U_hat y_hat
    ∃ DeltaA : Fin n → Fin n → ℝ,
      (∀ i j, |DeltaA i j| ≤ higham9_14_f u * |A i j|) ∧
      (∀ i, ∑ j : Fin n, (A i j + DeltaA i j) * x_hat j = b i) := by
  simpa [one_mul] using
    (higham9_14_source_f_bound_of_RectDoolittleRoundedStageTrace_square_fl_triangular_solves_gamma_le
      fp n A L_hat U_hat b 1 u hu hn hT hU_diag hU_budget_le
      hL_budget_le hγ_le_u
      (fun i j => by simpa [one_mul] using hAbsLU_le i j))

/-- **Theorem 9.14**, square-specialized rectangular rounded-stage trace with
optimal growth and the natural source `f(γ_n)` coefficient. -/
theorem higham9_14_source_f_bound_of_RectDoolittleRoundedStageTrace_square_fl_triangular_solves_absLU_le_absA_gamma
    (fp : FPModel) (n : ℕ)
    (A L_hat U_hat : Fin n → Fin n → ℝ)
    (b : Fin n → ℝ)
    (hn : gammaValid fp n)
    (hT : higham9_2_RectDoolittleRoundedStageTrace
      (Nat.le_refl n) A L_hat U_hat fp)
    (hU_diag : ∀ i : Fin n, U_hat i i ≠ 0)
    (hU_budget_le : ∀ k j : Fin n, k.val ≤ j.val →
      higham9_2_rectDoolittleUAbsBudget fp (Nat.le_refl n)
          A L_hat U_hat k j ≤ gamma fp n * |U_hat k j|)
    (hL_budget_le : ∀ i k : Fin n, k.val < i.val →
      higham9_2_rectDoolittleLAbsBudget fp A L_hat U_hat i k ≤
        gamma fp n * |L_hat i k * U_hat k k|)
    (hAbsLU_le : ∀ i j : Fin n,
      ∑ k : Fin n, |L_hat i k| * |U_hat k j| ≤ |A i j|) :
    let y_hat := fl_forwardSub fp n L_hat b
    let x_hat := fl_backSub fp n U_hat y_hat
    ∃ DeltaA : Fin n → Fin n → ℝ,
      (∀ i j, |DeltaA i j| ≤
        higham9_14_f (gamma fp n) * |A i j|) ∧
      (∀ i, ∑ j : Fin n, (A i j + DeltaA i j) * x_hat j = b i) := by
  simpa [one_mul] using
    (higham9_14_source_f_bound_of_RectDoolittleRoundedStageTrace_square_fl_triangular_solves_gamma
      fp n A L_hat U_hat b 1 hn hT hU_diag hU_budget_le hL_budget_le
      (fun i j => by simpa [one_mul] using hAbsLU_le i j))

/-- **Theorem 9.14**, square-specialized rectangular rounded-stage trace with
Higham's final `h(γ_n)` coefficient. -/
theorem higham9_14_source_h_bound_of_RectDoolittleRoundedStageTrace_square_fl_triangular_solves_gamma
    (fp : FPModel) (n : ℕ)
    (A L_hat U_hat : Fin n → Fin n → ℝ)
    (b : Fin n → ℝ)
    (hn : gammaValid fp n)
    (hγ_lt_one : gamma fp n < 1)
    (hT : higham9_2_RectDoolittleRoundedStageTrace
      (Nat.le_refl n) A L_hat U_hat fp)
    (hU_diag : ∀ i : Fin n, U_hat i i ≠ 0)
    (hU_budget_le : ∀ k j : Fin n, k.val ≤ j.val →
      higham9_2_rectDoolittleUAbsBudget fp (Nat.le_refl n)
          A L_hat U_hat k j ≤ gamma fp n * |U_hat k j|)
    (hL_budget_le : ∀ i k : Fin n, k.val < i.val →
      higham9_2_rectDoolittleLAbsBudget fp A L_hat U_hat i k ≤
        gamma fp n * |L_hat i k * U_hat k k|)
    (hAbsLU_le : ∀ i j : Fin n,
      ∑ k : Fin n, |L_hat i k| * |U_hat k j| ≤ |A i j|) :
    let y_hat := fl_forwardSub fp n L_hat b
    let x_hat := fl_backSub fp n U_hat y_hat
    ∃ DeltaA : Fin n → Fin n → ℝ,
      (∀ i j, |DeltaA i j| ≤
        higham9_14_h (gamma fp n) * |A i j|) ∧
      (∀ i, ∑ j : Fin n, (A i j + DeltaA i j) * x_hat j = b i) :=
  higham9_14_source_h_bound_of_RectDoolittleRoundedStageTrace_square_fl_triangular_solves_gamma_le
    fp n A L_hat U_hat b (gamma fp n) (gamma_nonneg fp hn)
    hγ_lt_one hn hT hU_diag hU_budget_le hL_budget_le le_rfl hAbsLU_le

/-- **Theorem 9.14**, square-specialized rectangular rounded-stage trace with
optimal growth and final `h(u)` coefficient. -/
theorem higham9_14_source_h_bound_of_RectDoolittleRoundedStageTrace_square_fl_triangular_solves_absLU_le_absA_gamma_le
    (fp : FPModel) (n : ℕ)
    (A L_hat U_hat : Fin n → Fin n → ℝ)
    (b : Fin n → ℝ)
    (u : ℝ) (hu : 0 ≤ u) (hu_lt_one : u < 1)
    (hn : gammaValid fp n)
    (hT : higham9_2_RectDoolittleRoundedStageTrace
      (Nat.le_refl n) A L_hat U_hat fp)
    (hU_diag : ∀ i : Fin n, U_hat i i ≠ 0)
    (hU_budget_le : ∀ k j : Fin n, k.val ≤ j.val →
      higham9_2_rectDoolittleUAbsBudget fp (Nat.le_refl n)
          A L_hat U_hat k j ≤ gamma fp n * |U_hat k j|)
    (hL_budget_le : ∀ i k : Fin n, k.val < i.val →
      higham9_2_rectDoolittleLAbsBudget fp A L_hat U_hat i k ≤
        gamma fp n * |L_hat i k * U_hat k k|)
    (hγ_le_u : gamma fp n ≤ u)
    (hAbsLU_le : ∀ i j : Fin n,
      ∑ k : Fin n, |L_hat i k| * |U_hat k j| ≤ |A i j|) :
    let y_hat := fl_forwardSub fp n L_hat b
    let x_hat := fl_backSub fp n U_hat y_hat
    ∃ DeltaA : Fin n → Fin n → ℝ,
      (∀ i j, |DeltaA i j| ≤ higham9_14_h u * |A i j|) ∧
      (∀ i, ∑ j : Fin n, (A i j + DeltaA i j) * x_hat j = b i) :=
  higham9_14_source_h_bound_of_RectDoolittleRoundedStageTrace_square_fl_triangular_solves_gamma_le
    fp n A L_hat U_hat b u hu hu_lt_one hn hT hU_diag hU_budget_le
    hL_budget_le hγ_le_u hAbsLU_le

/-- **Theorem 9.14**, square-specialized rectangular rounded-stage trace with
optimal growth and final `h(γ_n)` coefficient. -/
theorem higham9_14_source_h_bound_of_RectDoolittleRoundedStageTrace_square_fl_triangular_solves_absLU_le_absA_gamma
    (fp : FPModel) (n : ℕ)
    (A L_hat U_hat : Fin n → Fin n → ℝ)
    (b : Fin n → ℝ)
    (hn : gammaValid fp n)
    (hγ_lt_one : gamma fp n < 1)
    (hT : higham9_2_RectDoolittleRoundedStageTrace
      (Nat.le_refl n) A L_hat U_hat fp)
    (hU_diag : ∀ i : Fin n, U_hat i i ≠ 0)
    (hU_budget_le : ∀ k j : Fin n, k.val ≤ j.val →
      higham9_2_rectDoolittleUAbsBudget fp (Nat.le_refl n)
          A L_hat U_hat k j ≤ gamma fp n * |U_hat k j|)
    (hL_budget_le : ∀ i k : Fin n, k.val < i.val →
      higham9_2_rectDoolittleLAbsBudget fp A L_hat U_hat i k ≤
        gamma fp n * |L_hat i k * U_hat k k|)
    (hAbsLU_le : ∀ i j : Fin n,
      ∑ k : Fin n, |L_hat i k| * |U_hat k j| ≤ |A i j|) :
    let y_hat := fl_forwardSub fp n L_hat b
    let x_hat := fl_backSub fp n U_hat y_hat
    ∃ DeltaA : Fin n → Fin n → ℝ,
      (∀ i j, |DeltaA i j| ≤
        higham9_14_h (gamma fp n) * |A i j|) ∧
      (∀ i, ∑ j : Fin n, (A i j + DeltaA i j) * x_hat j = b i) :=
  higham9_14_source_h_bound_of_RectDoolittleRoundedStageTrace_square_fl_triangular_solves_gamma
    fp n A L_hat U_hat b hn hγ_lt_one hT hU_diag hU_budget_le
    hL_budget_le hAbsLU_le

/-- **Theorem 9.14**, square-specialized rectangular rounded-stage trace with
a constant-growth final `h(γ_n)` coefficient. -/
theorem higham9_14_source_h_bound_of_RectDoolittleRoundedStageTrace_square_fl_triangular_solves_const_gamma
    (fp : FPModel) (n : ℕ)
    (A L_hat U_hat : Fin n → Fin n → ℝ)
    (b : Fin n → ℝ)
    (c : ℝ) (hc : 0 ≤ c)
    (hn : gammaValid fp n)
    (hγ_lt_one : gamma fp n < 1)
    (hT : higham9_2_RectDoolittleRoundedStageTrace
      (Nat.le_refl n) A L_hat U_hat fp)
    (hU_diag : ∀ i : Fin n, U_hat i i ≠ 0)
    (hU_budget_le : ∀ k j : Fin n, k.val ≤ j.val →
      higham9_2_rectDoolittleUAbsBudget fp (Nat.le_refl n)
          A L_hat U_hat k j ≤ gamma fp n * |U_hat k j|)
    (hL_budget_le : ∀ i k : Fin n, k.val < i.val →
      higham9_2_rectDoolittleLAbsBudget fp A L_hat U_hat i k ≤
        gamma fp n * |L_hat i k * U_hat k k|)
    (hAbsLU_le : ∀ i j : Fin n,
      ∑ k : Fin n, |L_hat i k| * |U_hat k j| ≤ c * |A i j|) :
    let y_hat := fl_forwardSub fp n L_hat b
    let x_hat := fl_backSub fp n U_hat y_hat
    ∃ DeltaA : Fin n → Fin n → ℝ,
      (∀ i j, |DeltaA i j| ≤
        c * higham9_14_h (gamma fp n) * |A i j|) ∧
      (∀ i, ∑ j : Fin n, (A i j + DeltaA i j) * x_hat j = b i) :=
  higham9_14_source_h_bound_of_RectDoolittleRoundedStageTrace_square_fl_triangular_solves_const_gamma_le
    fp n A L_hat U_hat b c (gamma fp n) hc (gamma_nonneg fp hn)
    hγ_lt_one hn hT hU_diag hU_budget_le hL_budget_le le_rfl hAbsLU_le

/-- **Theorem 9.14**, Matrix-facing square-specialized rectangular
rounded-stage trace plus actual triangular solves with source `f(u)`
coefficient. -/
theorem higham9_14_matrix_source_f_bound_of_RectDoolittleRoundedStageTrace_square_fl_triangular_solves_gamma_le
    (fp : FPModel) (n : ℕ)
    (A L_hat U_hat : Matrix (Fin n) (Fin n) ℝ)
    (b : Fin n → ℝ)
    (c u : ℝ) (hu : 0 ≤ u)
    (hn : gammaValid fp n)
    (hT : higham9_2_RectDoolittleRoundedStageTrace
      (Nat.le_refl n) A L_hat U_hat fp)
    (hU_diag : ∀ i : Fin n, U_hat i i ≠ 0)
    (hU_budget_le : ∀ k j : Fin n, k.val ≤ j.val →
      higham9_2_rectDoolittleUAbsBudget fp (Nat.le_refl n)
          A L_hat U_hat k j ≤ gamma fp n * |U_hat k j|)
    (hL_budget_le : ∀ i k : Fin n, k.val < i.val →
      higham9_2_rectDoolittleLAbsBudget fp A L_hat U_hat i k ≤
        gamma fp n * |L_hat i k * U_hat k k|)
    (hγ_le_u : gamma fp n ≤ u)
    (hAbsLU_le : ∀ i j : Fin n,
      ∑ k : Fin n, |L_hat i k| * |U_hat k j| ≤ c * |A i j|) :
    let y_hat := fl_forwardSub fp n L_hat b
    let x_hat := fl_backSub fp n U_hat y_hat
    ∃ DeltaA : Matrix (Fin n) (Fin n) ℝ,
      (∀ i j, |DeltaA i j| ≤ c * higham9_14_f u * |A i j|) ∧
      Matrix.mulVec (fun i j => A i j + DeltaA i j) x_hat = b :=
  higham9_14_matrix_source_f_bound_of_RectDoolittleDenseLoopCertificate_square_fl_triangular_solves_gamma_le
    fp n A L_hat U_hat b c u hu hn
    (higham9_2_rectRoundedStageTrace_to_rectDenseLoopCertificate
      hT hU_diag hn hU_budget_le hL_budget_le)
    hγ_le_u hU_diag hAbsLU_le

/-- **Theorem 9.14**, Matrix-facing square-specialized rectangular
rounded-stage trace with the final exact-growth `h(u)` bound. -/
theorem higham9_14_matrix_source_h_bound_of_RectDoolittleRoundedStageTrace_square_fl_triangular_solves_gamma_le
    (fp : FPModel) (n : ℕ)
    (A L_hat U_hat : Matrix (Fin n) (Fin n) ℝ)
    (b : Fin n → ℝ)
    (u : ℝ) (hu : 0 ≤ u) (hu_lt_one : u < 1)
    (hn : gammaValid fp n)
    (hT : higham9_2_RectDoolittleRoundedStageTrace
      (Nat.le_refl n) A L_hat U_hat fp)
    (hU_diag : ∀ i : Fin n, U_hat i i ≠ 0)
    (hU_budget_le : ∀ k j : Fin n, k.val ≤ j.val →
      higham9_2_rectDoolittleUAbsBudget fp (Nat.le_refl n)
          A L_hat U_hat k j ≤ gamma fp n * |U_hat k j|)
    (hL_budget_le : ∀ i k : Fin n, k.val < i.val →
      higham9_2_rectDoolittleLAbsBudget fp A L_hat U_hat i k ≤
        gamma fp n * |L_hat i k * U_hat k k|)
    (hγ_le_u : gamma fp n ≤ u)
    (hAbsLU_le : ∀ i j : Fin n,
      ∑ k : Fin n, |L_hat i k| * |U_hat k j| ≤ |A i j|) :
    let y_hat := fl_forwardSub fp n L_hat b
    let x_hat := fl_backSub fp n U_hat y_hat
    ∃ DeltaA : Matrix (Fin n) (Fin n) ℝ,
      (∀ i j, |DeltaA i j| ≤ higham9_14_h u * |A i j|) ∧
      Matrix.mulVec (fun i j => A i j + DeltaA i j) x_hat = b :=
  higham9_14_matrix_source_h_bound_of_RectDoolittleDenseLoopCertificate_square_fl_triangular_solves_gamma_le
    fp n A L_hat U_hat b u hu hu_lt_one hn
    (higham9_2_rectRoundedStageTrace_to_rectDenseLoopCertificate
      hT hU_diag hn hU_budget_le hL_budget_le)
    hγ_le_u hU_diag hAbsLU_le

/-- **Theorem 9.14**, Matrix-facing square-specialized rectangular
rounded-stage trace with a supplied constant-growth final `h(u)` bound. -/
theorem higham9_14_matrix_source_h_bound_of_RectDoolittleRoundedStageTrace_square_fl_triangular_solves_const_gamma_le
    (fp : FPModel) (n : ℕ)
    (A L_hat U_hat : Matrix (Fin n) (Fin n) ℝ)
    (b : Fin n → ℝ)
    (c u : ℝ) (hc : 0 ≤ c) (hu : 0 ≤ u) (hu_lt_one : u < 1)
    (hn : gammaValid fp n)
    (hT : higham9_2_RectDoolittleRoundedStageTrace
      (Nat.le_refl n) A L_hat U_hat fp)
    (hU_diag : ∀ i : Fin n, U_hat i i ≠ 0)
    (hU_budget_le : ∀ k j : Fin n, k.val ≤ j.val →
      higham9_2_rectDoolittleUAbsBudget fp (Nat.le_refl n)
          A L_hat U_hat k j ≤ gamma fp n * |U_hat k j|)
    (hL_budget_le : ∀ i k : Fin n, k.val < i.val →
      higham9_2_rectDoolittleLAbsBudget fp A L_hat U_hat i k ≤
        gamma fp n * |L_hat i k * U_hat k k|)
    (hγ_le_u : gamma fp n ≤ u)
    (hAbsLU_le : ∀ i j : Fin n,
      ∑ k : Fin n, |L_hat i k| * |U_hat k j| ≤ c * |A i j|) :
    let y_hat := fl_forwardSub fp n L_hat b
    let x_hat := fl_backSub fp n U_hat y_hat
    ∃ DeltaA : Matrix (Fin n) (Fin n) ℝ,
      (∀ i j, |DeltaA i j| ≤ c * higham9_14_h u * |A i j|) ∧
      Matrix.mulVec (fun i j => A i j + DeltaA i j) x_hat = b :=
  higham9_14_matrix_source_h_bound_of_RectDoolittleDenseLoopCertificate_square_fl_triangular_solves_const_gamma_le
    fp n A L_hat U_hat b c u hc hu hu_lt_one hn
    (higham9_2_rectRoundedStageTrace_to_rectDenseLoopCertificate
      hT hU_diag hn hU_budget_le hL_budget_le)
    hγ_le_u hU_diag hAbsLU_le

/-- **Theorem 9.14**, Matrix-facing square-specialized rectangular
rounded-stage trace with the natural `γ_n` source coefficient. -/
theorem higham9_14_matrix_source_f_bound_of_RectDoolittleRoundedStageTrace_square_fl_triangular_solves_gamma
    (fp : FPModel) (n : ℕ)
    (A L_hat U_hat : Matrix (Fin n) (Fin n) ℝ)
    (b : Fin n → ℝ)
    (c : ℝ)
    (hn : gammaValid fp n)
    (hT : higham9_2_RectDoolittleRoundedStageTrace
      (Nat.le_refl n) A L_hat U_hat fp)
    (hU_diag : ∀ i : Fin n, U_hat i i ≠ 0)
    (hU_budget_le : ∀ k j : Fin n, k.val ≤ j.val →
      higham9_2_rectDoolittleUAbsBudget fp (Nat.le_refl n)
          A L_hat U_hat k j ≤ gamma fp n * |U_hat k j|)
    (hL_budget_le : ∀ i k : Fin n, k.val < i.val →
      higham9_2_rectDoolittleLAbsBudget fp A L_hat U_hat i k ≤
        gamma fp n * |L_hat i k * U_hat k k|)
    (hAbsLU_le : ∀ i j : Fin n,
      ∑ k : Fin n, |L_hat i k| * |U_hat k j| ≤ c * |A i j|) :
    let y_hat := fl_forwardSub fp n L_hat b
    let x_hat := fl_backSub fp n U_hat y_hat
    ∃ DeltaA : Matrix (Fin n) (Fin n) ℝ,
      (∀ i j, |DeltaA i j| ≤
        c * higham9_14_f (gamma fp n) * |A i j|) ∧
      Matrix.mulVec (fun i j => A i j + DeltaA i j) x_hat = b :=
  higham9_14_matrix_source_f_bound_of_RectDoolittleRoundedStageTrace_square_fl_triangular_solves_gamma_le
    fp n A L_hat U_hat b c (gamma fp n) (gamma_nonneg fp hn)
    hn hT hU_diag hU_budget_le hL_budget_le le_rfl hAbsLU_le

/-- **Theorem 9.14**, Matrix-facing square-specialized rectangular
rounded-stage trace with optimal growth and source `f(u)` coefficient. -/
theorem higham9_14_matrix_source_f_bound_of_RectDoolittleRoundedStageTrace_square_fl_triangular_solves_absLU_le_absA_gamma_le
    (fp : FPModel) (n : ℕ)
    (A L_hat U_hat : Matrix (Fin n) (Fin n) ℝ)
    (b : Fin n → ℝ)
    (u : ℝ) (hu : 0 ≤ u)
    (hn : gammaValid fp n)
    (hT : higham9_2_RectDoolittleRoundedStageTrace
      (Nat.le_refl n) A L_hat U_hat fp)
    (hU_diag : ∀ i : Fin n, U_hat i i ≠ 0)
    (hU_budget_le : ∀ k j : Fin n, k.val ≤ j.val →
      higham9_2_rectDoolittleUAbsBudget fp (Nat.le_refl n)
          A L_hat U_hat k j ≤ gamma fp n * |U_hat k j|)
    (hL_budget_le : ∀ i k : Fin n, k.val < i.val →
      higham9_2_rectDoolittleLAbsBudget fp A L_hat U_hat i k ≤
        gamma fp n * |L_hat i k * U_hat k k|)
    (hγ_le_u : gamma fp n ≤ u)
    (hAbsLU_le : ∀ i j : Fin n,
      ∑ k : Fin n, |L_hat i k| * |U_hat k j| ≤ |A i j|) :
    let y_hat := fl_forwardSub fp n L_hat b
    let x_hat := fl_backSub fp n U_hat y_hat
    ∃ DeltaA : Matrix (Fin n) (Fin n) ℝ,
      (∀ i j, |DeltaA i j| ≤ higham9_14_f u * |A i j|) ∧
      Matrix.mulVec (fun i j => A i j + DeltaA i j) x_hat = b := by
  simpa [one_mul] using
    (higham9_14_matrix_source_f_bound_of_RectDoolittleRoundedStageTrace_square_fl_triangular_solves_gamma_le
      fp n A L_hat U_hat b 1 u hu hn hT hU_diag hU_budget_le
      hL_budget_le hγ_le_u
      (fun i j => by simpa [one_mul] using hAbsLU_le i j))

/-- **Theorem 9.14**, Matrix-facing square-specialized rectangular
rounded-stage trace with optimal growth and the natural source `f(γ_n)`
coefficient. -/
theorem higham9_14_matrix_source_f_bound_of_RectDoolittleRoundedStageTrace_square_fl_triangular_solves_absLU_le_absA_gamma
    (fp : FPModel) (n : ℕ)
    (A L_hat U_hat : Matrix (Fin n) (Fin n) ℝ)
    (b : Fin n → ℝ)
    (hn : gammaValid fp n)
    (hT : higham9_2_RectDoolittleRoundedStageTrace
      (Nat.le_refl n) A L_hat U_hat fp)
    (hU_diag : ∀ i : Fin n, U_hat i i ≠ 0)
    (hU_budget_le : ∀ k j : Fin n, k.val ≤ j.val →
      higham9_2_rectDoolittleUAbsBudget fp (Nat.le_refl n)
          A L_hat U_hat k j ≤ gamma fp n * |U_hat k j|)
    (hL_budget_le : ∀ i k : Fin n, k.val < i.val →
      higham9_2_rectDoolittleLAbsBudget fp A L_hat U_hat i k ≤
        gamma fp n * |L_hat i k * U_hat k k|)
    (hAbsLU_le : ∀ i j : Fin n,
      ∑ k : Fin n, |L_hat i k| * |U_hat k j| ≤ |A i j|) :
    let y_hat := fl_forwardSub fp n L_hat b
    let x_hat := fl_backSub fp n U_hat y_hat
    ∃ DeltaA : Matrix (Fin n) (Fin n) ℝ,
      (∀ i j, |DeltaA i j| ≤
        higham9_14_f (gamma fp n) * |A i j|) ∧
      Matrix.mulVec (fun i j => A i j + DeltaA i j) x_hat = b := by
  simpa [one_mul] using
    (higham9_14_matrix_source_f_bound_of_RectDoolittleRoundedStageTrace_square_fl_triangular_solves_gamma
      fp n A L_hat U_hat b 1 hn hT hU_diag hU_budget_le hL_budget_le
      (fun i j => by simpa [one_mul] using hAbsLU_le i j))

/-- **Theorem 9.14**, Matrix-facing square-specialized rectangular
rounded-stage trace with Higham's final `h(γ_n)` coefficient. -/
theorem higham9_14_matrix_source_h_bound_of_RectDoolittleRoundedStageTrace_square_fl_triangular_solves_gamma
    (fp : FPModel) (n : ℕ)
    (A L_hat U_hat : Matrix (Fin n) (Fin n) ℝ)
    (b : Fin n → ℝ)
    (hn : gammaValid fp n)
    (hγ_lt_one : gamma fp n < 1)
    (hT : higham9_2_RectDoolittleRoundedStageTrace
      (Nat.le_refl n) A L_hat U_hat fp)
    (hU_diag : ∀ i : Fin n, U_hat i i ≠ 0)
    (hU_budget_le : ∀ k j : Fin n, k.val ≤ j.val →
      higham9_2_rectDoolittleUAbsBudget fp (Nat.le_refl n)
          A L_hat U_hat k j ≤ gamma fp n * |U_hat k j|)
    (hL_budget_le : ∀ i k : Fin n, k.val < i.val →
      higham9_2_rectDoolittleLAbsBudget fp A L_hat U_hat i k ≤
        gamma fp n * |L_hat i k * U_hat k k|)
    (hAbsLU_le : ∀ i j : Fin n,
      ∑ k : Fin n, |L_hat i k| * |U_hat k j| ≤ |A i j|) :
    let y_hat := fl_forwardSub fp n L_hat b
    let x_hat := fl_backSub fp n U_hat y_hat
    ∃ DeltaA : Matrix (Fin n) (Fin n) ℝ,
      (∀ i j, |DeltaA i j| ≤
        higham9_14_h (gamma fp n) * |A i j|) ∧
      Matrix.mulVec (fun i j => A i j + DeltaA i j) x_hat = b :=
  higham9_14_matrix_source_h_bound_of_RectDoolittleRoundedStageTrace_square_fl_triangular_solves_gamma_le
    fp n A L_hat U_hat b (gamma fp n) (gamma_nonneg fp hn)
    hγ_lt_one hn hT hU_diag hU_budget_le hL_budget_le le_rfl hAbsLU_le

/-- **Theorem 9.14**, Matrix-facing square-specialized rectangular
rounded-stage trace with optimal growth and final `h(u)` coefficient. -/
theorem higham9_14_matrix_source_h_bound_of_RectDoolittleRoundedStageTrace_square_fl_triangular_solves_absLU_le_absA_gamma_le
    (fp : FPModel) (n : ℕ)
    (A L_hat U_hat : Matrix (Fin n) (Fin n) ℝ)
    (b : Fin n → ℝ)
    (u : ℝ) (hu : 0 ≤ u) (hu_lt_one : u < 1)
    (hn : gammaValid fp n)
    (hT : higham9_2_RectDoolittleRoundedStageTrace
      (Nat.le_refl n) A L_hat U_hat fp)
    (hU_diag : ∀ i : Fin n, U_hat i i ≠ 0)
    (hU_budget_le : ∀ k j : Fin n, k.val ≤ j.val →
      higham9_2_rectDoolittleUAbsBudget fp (Nat.le_refl n)
          A L_hat U_hat k j ≤ gamma fp n * |U_hat k j|)
    (hL_budget_le : ∀ i k : Fin n, k.val < i.val →
      higham9_2_rectDoolittleLAbsBudget fp A L_hat U_hat i k ≤
        gamma fp n * |L_hat i k * U_hat k k|)
    (hγ_le_u : gamma fp n ≤ u)
    (hAbsLU_le : ∀ i j : Fin n,
      ∑ k : Fin n, |L_hat i k| * |U_hat k j| ≤ |A i j|) :
    let y_hat := fl_forwardSub fp n L_hat b
    let x_hat := fl_backSub fp n U_hat y_hat
    ∃ DeltaA : Matrix (Fin n) (Fin n) ℝ,
      (∀ i j, |DeltaA i j| ≤ higham9_14_h u * |A i j|) ∧
      Matrix.mulVec (fun i j => A i j + DeltaA i j) x_hat = b :=
  higham9_14_matrix_source_h_bound_of_RectDoolittleRoundedStageTrace_square_fl_triangular_solves_gamma_le
    fp n A L_hat U_hat b u hu hu_lt_one hn hT hU_diag hU_budget_le
    hL_budget_le hγ_le_u hAbsLU_le

/-- **Theorem 9.14**, Matrix-facing square-specialized rectangular
rounded-stage trace with optimal growth and final `h(γ_n)` coefficient. -/
theorem higham9_14_matrix_source_h_bound_of_RectDoolittleRoundedStageTrace_square_fl_triangular_solves_absLU_le_absA_gamma
    (fp : FPModel) (n : ℕ)
    (A L_hat U_hat : Matrix (Fin n) (Fin n) ℝ)
    (b : Fin n → ℝ)
    (hn : gammaValid fp n)
    (hγ_lt_one : gamma fp n < 1)
    (hT : higham9_2_RectDoolittleRoundedStageTrace
      (Nat.le_refl n) A L_hat U_hat fp)
    (hU_diag : ∀ i : Fin n, U_hat i i ≠ 0)
    (hU_budget_le : ∀ k j : Fin n, k.val ≤ j.val →
      higham9_2_rectDoolittleUAbsBudget fp (Nat.le_refl n)
          A L_hat U_hat k j ≤ gamma fp n * |U_hat k j|)
    (hL_budget_le : ∀ i k : Fin n, k.val < i.val →
      higham9_2_rectDoolittleLAbsBudget fp A L_hat U_hat i k ≤
        gamma fp n * |L_hat i k * U_hat k k|)
    (hAbsLU_le : ∀ i j : Fin n,
      ∑ k : Fin n, |L_hat i k| * |U_hat k j| ≤ |A i j|) :
    let y_hat := fl_forwardSub fp n L_hat b
    let x_hat := fl_backSub fp n U_hat y_hat
    ∃ DeltaA : Matrix (Fin n) (Fin n) ℝ,
      (∀ i j, |DeltaA i j| ≤
        higham9_14_h (gamma fp n) * |A i j|) ∧
      Matrix.mulVec (fun i j => A i j + DeltaA i j) x_hat = b :=
  higham9_14_matrix_source_h_bound_of_RectDoolittleRoundedStageTrace_square_fl_triangular_solves_gamma
    fp n A L_hat U_hat b hn hγ_lt_one hT hU_diag hU_budget_le
    hL_budget_le hAbsLU_le

/-- **Theorem 9.14**, Matrix-facing square-specialized rectangular
rounded-stage trace with a constant-growth final `h(γ_n)` coefficient. -/
theorem higham9_14_matrix_source_h_bound_of_RectDoolittleRoundedStageTrace_square_fl_triangular_solves_const_gamma
    (fp : FPModel) (n : ℕ)
    (A L_hat U_hat : Matrix (Fin n) (Fin n) ℝ)
    (b : Fin n → ℝ)
    (c : ℝ) (hc : 0 ≤ c)
    (hn : gammaValid fp n)
    (hγ_lt_one : gamma fp n < 1)
    (hT : higham9_2_RectDoolittleRoundedStageTrace
      (Nat.le_refl n) A L_hat U_hat fp)
    (hU_diag : ∀ i : Fin n, U_hat i i ≠ 0)
    (hU_budget_le : ∀ k j : Fin n, k.val ≤ j.val →
      higham9_2_rectDoolittleUAbsBudget fp (Nat.le_refl n)
          A L_hat U_hat k j ≤ gamma fp n * |U_hat k j|)
    (hL_budget_le : ∀ i k : Fin n, k.val < i.val →
      higham9_2_rectDoolittleLAbsBudget fp A L_hat U_hat i k ≤
        gamma fp n * |L_hat i k * U_hat k k|)
    (hAbsLU_le : ∀ i j : Fin n,
      ∑ k : Fin n, |L_hat i k| * |U_hat k j| ≤ c * |A i j|) :
    let y_hat := fl_forwardSub fp n L_hat b
    let x_hat := fl_backSub fp n U_hat y_hat
    ∃ DeltaA : Matrix (Fin n) (Fin n) ℝ,
      (∀ i j, |DeltaA i j| ≤
        c * higham9_14_h (gamma fp n) * |A i j|) ∧
      Matrix.mulVec (fun i j => A i j + DeltaA i j) x_hat = b :=
  higham9_14_matrix_source_h_bound_of_RectDoolittleRoundedStageTrace_square_fl_triangular_solves_const_gamma_le
    fp n A L_hat U_hat b c (gamma fp n) hc (gamma_nonneg fp hn)
    hγ_lt_one hn hT hU_diag hU_budget_le hL_budget_le le_rfl hAbsLU_le

/-- **Theorem 9.14**, column-dominant tridiagonal rounded-stage source
`f(u)` bound.

The rounded-stage trace supplies the Algorithm 9.2 floating-point certificate;
an exact `LUFactSpec` for those stage factors plus Theorem 9.13 supplies the
structural `|Lhat||Uhat| <= 3|A|` comparison. -/
theorem higham9_14_tridiag_colDiagDom_source_f_bound_of_RectDoolittleRoundedStageTrace_square_fl_triangular_solves_gamma_le
    (fp : FPModel) (n : ℕ)
    (A L_hat U_hat : Fin n → Fin n → ℝ)
    (b : Fin n → ℝ)
    (u : ℝ) (hu : 0 ≤ u)
    (hn : gammaValid fp n)
    (hT : higham9_2_RectDoolittleRoundedStageTrace
      (Nat.le_refl n) A L_hat U_hat fp)
    (hLU : LUFactSpec n A L_hat U_hat)
    (hdetA : Matrix.det (Matrix.of A : Matrix (Fin n) (Fin n) ℝ) ≠ 0)
    (hA_tridiag : IsTridiagonal n A)
    (hColDom : IsDiagDominant n A)
    (hU_budget_le : ∀ k j : Fin n, k.val ≤ j.val →
      higham9_2_rectDoolittleUAbsBudget fp (Nat.le_refl n)
          A L_hat U_hat k j ≤ gamma fp n * |U_hat k j|)
    (hL_budget_le : ∀ i k : Fin n, k.val < i.val →
      higham9_2_rectDoolittleLAbsBudget fp A L_hat U_hat i k ≤
        gamma fp n * |L_hat i k * U_hat k k|)
    (hγ_le_u : gamma fp n ≤ u) :
    let y_hat := fl_forwardSub fp n L_hat b
    let x_hat := fl_backSub fp n U_hat y_hat
    ∃ DeltaA : Fin n → Fin n → ℝ,
      (∀ i j, |DeltaA i j| ≤ 3 * higham9_14_f u * |A i j|) ∧
      (∀ i, ∑ j : Fin n, (A i j + DeltaA i j) * x_hat j = b i) :=
  higham9_14_source_f_bound_of_RectDoolittleRoundedStageTrace_square_fl_triangular_solves_gamma_le
    fp n A L_hat U_hat b 3 u hu hn hT
    (hLU.det_ne_zero_iff_U_diag_ne_zero.mp hdetA)
    hU_budget_le hL_budget_le hγ_le_u
    (higham9_13_colDiagDom_tridiag_growth_bound_3_of_LUFactSpec
      A L_hat U_hat hLU hdetA hA_tridiag hColDom)

/-- **Theorem 9.14**, row-dominant tridiagonal rounded-stage source `f(u)`
bound. -/
theorem higham9_14_tridiag_rowDiagDom_source_f_bound_of_RectDoolittleRoundedStageTrace_square_fl_triangular_solves_gamma_le
    (fp : FPModel) (n : ℕ)
    (A L_hat U_hat : Fin n → Fin n → ℝ)
    (b : Fin n → ℝ)
    (u : ℝ) (hu : 0 ≤ u)
    (hn : gammaValid fp n)
    (hT : higham9_2_RectDoolittleRoundedStageTrace
      (Nat.le_refl n) A L_hat U_hat fp)
    (hLU : LUFactSpec n A L_hat U_hat)
    (hdetA : Matrix.det (Matrix.of A : Matrix (Fin n) (Fin n) ℝ) ≠ 0)
    (hA_tridiag : IsTridiagonal n A)
    (hRowDom : IsRowDiagDominant n A)
    (hU_budget_le : ∀ k j : Fin n, k.val ≤ j.val →
      higham9_2_rectDoolittleUAbsBudget fp (Nat.le_refl n)
          A L_hat U_hat k j ≤ gamma fp n * |U_hat k j|)
    (hL_budget_le : ∀ i k : Fin n, k.val < i.val →
      higham9_2_rectDoolittleLAbsBudget fp A L_hat U_hat i k ≤
        gamma fp n * |L_hat i k * U_hat k k|)
    (hγ_le_u : gamma fp n ≤ u) :
    let y_hat := fl_forwardSub fp n L_hat b
    let x_hat := fl_backSub fp n U_hat y_hat
    ∃ DeltaA : Fin n → Fin n → ℝ,
      (∀ i j, |DeltaA i j| ≤ 3 * higham9_14_f u * |A i j|) ∧
      (∀ i, ∑ j : Fin n, (A i j + DeltaA i j) * x_hat j = b i) :=
  higham9_14_source_f_bound_of_RectDoolittleRoundedStageTrace_square_fl_triangular_solves_gamma_le
    fp n A L_hat U_hat b 3 u hu hn hT
    (hLU.det_ne_zero_iff_U_diag_ne_zero.mp hdetA)
    hU_budget_le hL_budget_le hγ_le_u
    (higham9_13_rowDiagDom_tridiag_growth_bound_3_of_LUFactSpec
      A L_hat U_hat hLU hdetA hA_tridiag hRowDom)

/-- **Theorem 9.14**, column-dominant tridiagonal rounded-stage source
`f(γ_n)` bound. -/
theorem higham9_14_tridiag_colDiagDom_source_f_bound_of_RectDoolittleRoundedStageTrace_square_fl_triangular_solves_gamma
    (fp : FPModel) (n : ℕ)
    (A L_hat U_hat : Fin n → Fin n → ℝ)
    (b : Fin n → ℝ)
    (hn : gammaValid fp n)
    (hT : higham9_2_RectDoolittleRoundedStageTrace
      (Nat.le_refl n) A L_hat U_hat fp)
    (hLU : LUFactSpec n A L_hat U_hat)
    (hdetA : Matrix.det (Matrix.of A : Matrix (Fin n) (Fin n) ℝ) ≠ 0)
    (hA_tridiag : IsTridiagonal n A)
    (hColDom : IsDiagDominant n A)
    (hU_budget_le : ∀ k j : Fin n, k.val ≤ j.val →
      higham9_2_rectDoolittleUAbsBudget fp (Nat.le_refl n)
          A L_hat U_hat k j ≤ gamma fp n * |U_hat k j|)
    (hL_budget_le : ∀ i k : Fin n, k.val < i.val →
      higham9_2_rectDoolittleLAbsBudget fp A L_hat U_hat i k ≤
        gamma fp n * |L_hat i k * U_hat k k|) :
    let y_hat := fl_forwardSub fp n L_hat b
    let x_hat := fl_backSub fp n U_hat y_hat
    ∃ DeltaA : Fin n → Fin n → ℝ,
      (∀ i j, |DeltaA i j| ≤
        3 * higham9_14_f (gamma fp n) * |A i j|) ∧
      (∀ i, ∑ j : Fin n, (A i j + DeltaA i j) * x_hat j = b i) :=
  higham9_14_tridiag_colDiagDom_source_f_bound_of_RectDoolittleRoundedStageTrace_square_fl_triangular_solves_gamma_le
    fp n A L_hat U_hat b (gamma fp n) (gamma_nonneg fp hn) hn
    hT hLU hdetA hA_tridiag hColDom hU_budget_le hL_budget_le le_rfl

/-- **Theorem 9.14**, row-dominant tridiagonal rounded-stage source
`f(γ_n)` bound. -/
theorem higham9_14_tridiag_rowDiagDom_source_f_bound_of_RectDoolittleRoundedStageTrace_square_fl_triangular_solves_gamma
    (fp : FPModel) (n : ℕ)
    (A L_hat U_hat : Fin n → Fin n → ℝ)
    (b : Fin n → ℝ)
    (hn : gammaValid fp n)
    (hT : higham9_2_RectDoolittleRoundedStageTrace
      (Nat.le_refl n) A L_hat U_hat fp)
    (hLU : LUFactSpec n A L_hat U_hat)
    (hdetA : Matrix.det (Matrix.of A : Matrix (Fin n) (Fin n) ℝ) ≠ 0)
    (hA_tridiag : IsTridiagonal n A)
    (hRowDom : IsRowDiagDominant n A)
    (hU_budget_le : ∀ k j : Fin n, k.val ≤ j.val →
      higham9_2_rectDoolittleUAbsBudget fp (Nat.le_refl n)
          A L_hat U_hat k j ≤ gamma fp n * |U_hat k j|)
    (hL_budget_le : ∀ i k : Fin n, k.val < i.val →
      higham9_2_rectDoolittleLAbsBudget fp A L_hat U_hat i k ≤
        gamma fp n * |L_hat i k * U_hat k k|) :
    let y_hat := fl_forwardSub fp n L_hat b
    let x_hat := fl_backSub fp n U_hat y_hat
    ∃ DeltaA : Fin n → Fin n → ℝ,
      (∀ i j, |DeltaA i j| ≤
        3 * higham9_14_f (gamma fp n) * |A i j|) ∧
      (∀ i, ∑ j : Fin n, (A i j + DeltaA i j) * x_hat j = b i) :=
  higham9_14_tridiag_rowDiagDom_source_f_bound_of_RectDoolittleRoundedStageTrace_square_fl_triangular_solves_gamma_le
    fp n A L_hat U_hat b (gamma fp n) (gamma_nonneg fp hn) hn
    hT hLU hdetA hA_tridiag hRowDom hU_budget_le hL_budget_le le_rfl

/-- **Theorem 9.14**, column-dominant tridiagonal rounded-stage final `h(u)`
bound with structural growth constant `3`. -/
theorem higham9_14_tridiag_colDiagDom_source_h_bound_of_RectDoolittleRoundedStageTrace_square_fl_triangular_solves_const_gamma_le
    (fp : FPModel) (n : ℕ)
    (A L_hat U_hat : Fin n → Fin n → ℝ)
    (b : Fin n → ℝ)
    (u : ℝ) (hu : 0 ≤ u) (hu_lt_one : u < 1)
    (hn : gammaValid fp n)
    (hT : higham9_2_RectDoolittleRoundedStageTrace
      (Nat.le_refl n) A L_hat U_hat fp)
    (hLU : LUFactSpec n A L_hat U_hat)
    (hdetA : Matrix.det (Matrix.of A : Matrix (Fin n) (Fin n) ℝ) ≠ 0)
    (hA_tridiag : IsTridiagonal n A)
    (hColDom : IsDiagDominant n A)
    (hU_budget_le : ∀ k j : Fin n, k.val ≤ j.val →
      higham9_2_rectDoolittleUAbsBudget fp (Nat.le_refl n)
          A L_hat U_hat k j ≤ gamma fp n * |U_hat k j|)
    (hL_budget_le : ∀ i k : Fin n, k.val < i.val →
      higham9_2_rectDoolittleLAbsBudget fp A L_hat U_hat i k ≤
        gamma fp n * |L_hat i k * U_hat k k|)
    (hγ_le_u : gamma fp n ≤ u) :
    let y_hat := fl_forwardSub fp n L_hat b
    let x_hat := fl_backSub fp n U_hat y_hat
    ∃ DeltaA : Fin n → Fin n → ℝ,
      (∀ i j, |DeltaA i j| ≤ 3 * higham9_14_h u * |A i j|) ∧
      (∀ i, ∑ j : Fin n, (A i j + DeltaA i j) * x_hat j = b i) :=
  higham9_14_source_h_bound_of_RectDoolittleRoundedStageTrace_square_fl_triangular_solves_const_gamma_le
    fp n A L_hat U_hat b 3 u (by norm_num) hu hu_lt_one hn hT
    (hLU.det_ne_zero_iff_U_diag_ne_zero.mp hdetA)
    hU_budget_le hL_budget_le hγ_le_u
    (higham9_13_colDiagDom_tridiag_growth_bound_3_of_LUFactSpec
      A L_hat U_hat hLU hdetA hA_tridiag hColDom)

/-- **Theorem 9.14**, row-dominant tridiagonal rounded-stage final `h(u)`
bound with structural growth constant `3`. -/
theorem higham9_14_tridiag_rowDiagDom_source_h_bound_of_RectDoolittleRoundedStageTrace_square_fl_triangular_solves_const_gamma_le
    (fp : FPModel) (n : ℕ)
    (A L_hat U_hat : Fin n → Fin n → ℝ)
    (b : Fin n → ℝ)
    (u : ℝ) (hu : 0 ≤ u) (hu_lt_one : u < 1)
    (hn : gammaValid fp n)
    (hT : higham9_2_RectDoolittleRoundedStageTrace
      (Nat.le_refl n) A L_hat U_hat fp)
    (hLU : LUFactSpec n A L_hat U_hat)
    (hdetA : Matrix.det (Matrix.of A : Matrix (Fin n) (Fin n) ℝ) ≠ 0)
    (hA_tridiag : IsTridiagonal n A)
    (hRowDom : IsRowDiagDominant n A)
    (hU_budget_le : ∀ k j : Fin n, k.val ≤ j.val →
      higham9_2_rectDoolittleUAbsBudget fp (Nat.le_refl n)
          A L_hat U_hat k j ≤ gamma fp n * |U_hat k j|)
    (hL_budget_le : ∀ i k : Fin n, k.val < i.val →
      higham9_2_rectDoolittleLAbsBudget fp A L_hat U_hat i k ≤
        gamma fp n * |L_hat i k * U_hat k k|)
    (hγ_le_u : gamma fp n ≤ u) :
    let y_hat := fl_forwardSub fp n L_hat b
    let x_hat := fl_backSub fp n U_hat y_hat
    ∃ DeltaA : Fin n → Fin n → ℝ,
      (∀ i j, |DeltaA i j| ≤ 3 * higham9_14_h u * |A i j|) ∧
      (∀ i, ∑ j : Fin n, (A i j + DeltaA i j) * x_hat j = b i) :=
  higham9_14_source_h_bound_of_RectDoolittleRoundedStageTrace_square_fl_triangular_solves_const_gamma_le
    fp n A L_hat U_hat b 3 u (by norm_num) hu hu_lt_one hn hT
    (hLU.det_ne_zero_iff_U_diag_ne_zero.mp hdetA)
    hU_budget_le hL_budget_le hγ_le_u
    (higham9_13_rowDiagDom_tridiag_growth_bound_3_of_LUFactSpec
      A L_hat U_hat hLU hdetA hA_tridiag hRowDom)

/-- **Theorem 9.14**, column-dominant tridiagonal rounded-stage final
`h(γ_n)` bound with structural growth constant `3`. -/
theorem higham9_14_tridiag_colDiagDom_source_h_bound_of_RectDoolittleRoundedStageTrace_square_fl_triangular_solves_const_gamma
    (fp : FPModel) (n : ℕ)
    (A L_hat U_hat : Fin n → Fin n → ℝ)
    (b : Fin n → ℝ)
    (hn : gammaValid fp n)
    (hγ_lt_one : gamma fp n < 1)
    (hT : higham9_2_RectDoolittleRoundedStageTrace
      (Nat.le_refl n) A L_hat U_hat fp)
    (hLU : LUFactSpec n A L_hat U_hat)
    (hdetA : Matrix.det (Matrix.of A : Matrix (Fin n) (Fin n) ℝ) ≠ 0)
    (hA_tridiag : IsTridiagonal n A)
    (hColDom : IsDiagDominant n A)
    (hU_budget_le : ∀ k j : Fin n, k.val ≤ j.val →
      higham9_2_rectDoolittleUAbsBudget fp (Nat.le_refl n)
          A L_hat U_hat k j ≤ gamma fp n * |U_hat k j|)
    (hL_budget_le : ∀ i k : Fin n, k.val < i.val →
      higham9_2_rectDoolittleLAbsBudget fp A L_hat U_hat i k ≤
        gamma fp n * |L_hat i k * U_hat k k|) :
    let y_hat := fl_forwardSub fp n L_hat b
    let x_hat := fl_backSub fp n U_hat y_hat
    ∃ DeltaA : Fin n → Fin n → ℝ,
      (∀ i j, |DeltaA i j| ≤
        3 * higham9_14_h (gamma fp n) * |A i j|) ∧
      (∀ i, ∑ j : Fin n, (A i j + DeltaA i j) * x_hat j = b i) :=
  higham9_14_tridiag_colDiagDom_source_h_bound_of_RectDoolittleRoundedStageTrace_square_fl_triangular_solves_const_gamma_le
    fp n A L_hat U_hat b (gamma fp n) (gamma_nonneg fp hn) hγ_lt_one
    hn hT hLU hdetA hA_tridiag hColDom hU_budget_le hL_budget_le le_rfl

/-- **Theorem 9.14**, row-dominant tridiagonal rounded-stage final `h(γ_n)`
bound with structural growth constant `3`. -/
theorem higham9_14_tridiag_rowDiagDom_source_h_bound_of_RectDoolittleRoundedStageTrace_square_fl_triangular_solves_const_gamma
    (fp : FPModel) (n : ℕ)
    (A L_hat U_hat : Fin n → Fin n → ℝ)
    (b : Fin n → ℝ)
    (hn : gammaValid fp n)
    (hγ_lt_one : gamma fp n < 1)
    (hT : higham9_2_RectDoolittleRoundedStageTrace
      (Nat.le_refl n) A L_hat U_hat fp)
    (hLU : LUFactSpec n A L_hat U_hat)
    (hdetA : Matrix.det (Matrix.of A : Matrix (Fin n) (Fin n) ℝ) ≠ 0)
    (hA_tridiag : IsTridiagonal n A)
    (hRowDom : IsRowDiagDominant n A)
    (hU_budget_le : ∀ k j : Fin n, k.val ≤ j.val →
      higham9_2_rectDoolittleUAbsBudget fp (Nat.le_refl n)
          A L_hat U_hat k j ≤ gamma fp n * |U_hat k j|)
    (hL_budget_le : ∀ i k : Fin n, k.val < i.val →
      higham9_2_rectDoolittleLAbsBudget fp A L_hat U_hat i k ≤
        gamma fp n * |L_hat i k * U_hat k k|) :
    let y_hat := fl_forwardSub fp n L_hat b
    let x_hat := fl_backSub fp n U_hat y_hat
    ∃ DeltaA : Fin n → Fin n → ℝ,
      (∀ i j, |DeltaA i j| ≤
        3 * higham9_14_h (gamma fp n) * |A i j|) ∧
      (∀ i, ∑ j : Fin n, (A i j + DeltaA i j) * x_hat j = b i) :=
  higham9_14_tridiag_rowDiagDom_source_h_bound_of_RectDoolittleRoundedStageTrace_square_fl_triangular_solves_const_gamma_le
    fp n A L_hat U_hat b (gamma fp n) (gamma_nonneg fp hn) hγ_lt_one
    hn hT hLU hdetA hA_tridiag hRowDom hU_budget_le hL_budget_le le_rfl

/-- **Theorem 9.14**, column-dominant tridiagonal rounded-stage
model-consuming `f(γ_n)` bound.

The rounded-stage trace supplies equation (9.20) at the natural coefficient,
while the caller supplies the explicit equation (9.21) triangular-solve model.
This keeps solve correctness visible but discharges the tridiagonal
`3|A|` growth comparison from the existing exact `LUFactSpec`. -/
theorem higham9_14_tridiag_colDiagDom_source_f_bound_of_RectDoolittleRoundedStageTrace_square_models_gamma
    (fp : FPModel) (n : ℕ)
    (A L_hat U_hat : Fin n → Fin n → ℝ)
    (y_hat x_hat b : Fin n → ℝ)
    (DeltaL DeltaU : Fin n → Fin n → ℝ)
    (hn : gammaValid fp n)
    (hT : higham9_2_RectDoolittleRoundedStageTrace
      (Nat.le_refl n) A L_hat U_hat fp)
    (hLU : LUFactSpec n A L_hat U_hat)
    (hdetA : Matrix.det (Matrix.of A : Matrix (Fin n) (Fin n) ℝ) ≠ 0)
    (hA_tridiag : IsTridiagonal n A)
    (hColDom : IsDiagDominant n A)
    (hU_budget_le : ∀ k j : Fin n, k.val ≤ j.val →
      higham9_2_rectDoolittleUAbsBudget fp (Nat.le_refl n)
          A L_hat U_hat k j ≤ gamma fp n * |U_hat k j|)
    (hL_budget_le : ∀ i k : Fin n, k.val < i.val →
      higham9_2_rectDoolittleLAbsBudget fp A L_hat U_hat i k ≤
        gamma fp n * |L_hat i k * U_hat k k|)
    (h21 : higham9_21_tridiag_solve_perturbation_model n L_hat U_hat
      y_hat x_hat b DeltaL DeltaU (gamma fp n)) :
    ∃ DeltaA : Fin n → Fin n → ℝ,
      (∀ i j, |DeltaA i j| ≤
        3 * higham9_14_f (gamma fp n) * |A i j|) ∧
      (∀ i, ∑ j : Fin n, (A i j + DeltaA i j) * x_hat j = b i) := by
  rcases
      higham9_20_tridiag_lu_perturbation_model_of_RectDoolittleRoundedStageTrace_square_gamma
        fp n A L_hat U_hat hn hT
        (hLU.det_ne_zero_iff_U_diag_ne_zero.mp hdetA)
        hU_budget_le hL_budget_le with
    ⟨DeltaA_LU, h20⟩
  exact
    higham9_14_source_f_bound_of_absLU_le_const_absA_and_9_20_9_21_models
      n A L_hat U_hat y_hat x_hat b 3 (gamma fp n)
      (gamma_nonneg fp hn)
      (higham9_13_colDiagDom_tridiag_growth_bound_3_of_LUFactSpec
        A L_hat U_hat hLU hdetA hA_tridiag hColDom)
      DeltaA_LU DeltaL DeltaU h20 h21

/-- **Theorem 9.14**, row-dominant tridiagonal rounded-stage
model-consuming `f(γ_n)` bound. -/
theorem higham9_14_tridiag_rowDiagDom_source_f_bound_of_RectDoolittleRoundedStageTrace_square_models_gamma
    (fp : FPModel) (n : ℕ)
    (A L_hat U_hat : Fin n → Fin n → ℝ)
    (y_hat x_hat b : Fin n → ℝ)
    (DeltaL DeltaU : Fin n → Fin n → ℝ)
    (hn : gammaValid fp n)
    (hT : higham9_2_RectDoolittleRoundedStageTrace
      (Nat.le_refl n) A L_hat U_hat fp)
    (hLU : LUFactSpec n A L_hat U_hat)
    (hdetA : Matrix.det (Matrix.of A : Matrix (Fin n) (Fin n) ℝ) ≠ 0)
    (hA_tridiag : IsTridiagonal n A)
    (hRowDom : IsRowDiagDominant n A)
    (hU_budget_le : ∀ k j : Fin n, k.val ≤ j.val →
      higham9_2_rectDoolittleUAbsBudget fp (Nat.le_refl n)
          A L_hat U_hat k j ≤ gamma fp n * |U_hat k j|)
    (hL_budget_le : ∀ i k : Fin n, k.val < i.val →
      higham9_2_rectDoolittleLAbsBudget fp A L_hat U_hat i k ≤
        gamma fp n * |L_hat i k * U_hat k k|)
    (h21 : higham9_21_tridiag_solve_perturbation_model n L_hat U_hat
      y_hat x_hat b DeltaL DeltaU (gamma fp n)) :
    ∃ DeltaA : Fin n → Fin n → ℝ,
      (∀ i j, |DeltaA i j| ≤
        3 * higham9_14_f (gamma fp n) * |A i j|) ∧
      (∀ i, ∑ j : Fin n, (A i j + DeltaA i j) * x_hat j = b i) := by
  rcases
      higham9_20_tridiag_lu_perturbation_model_of_RectDoolittleRoundedStageTrace_square_gamma
        fp n A L_hat U_hat hn hT
        (hLU.det_ne_zero_iff_U_diag_ne_zero.mp hdetA)
        hU_budget_le hL_budget_le with
    ⟨DeltaA_LU, h20⟩
  exact
    higham9_14_source_f_bound_of_absLU_le_const_absA_and_9_20_9_21_models
      n A L_hat U_hat y_hat x_hat b 3 (gamma fp n)
      (gamma_nonneg fp hn)
      (higham9_13_rowDiagDom_tridiag_growth_bound_3_of_LUFactSpec
        A L_hat U_hat hLU hdetA hA_tridiag hRowDom)
      DeltaA_LU DeltaL DeltaU h20 h21

/-- **Theorem 9.14**, column-dominant tridiagonal rounded-stage
model-consuming final `h(γ_n)` bound. -/
theorem higham9_14_tridiag_colDiagDom_source_h_bound_of_RectDoolittleRoundedStageTrace_square_models_gamma
    (fp : FPModel) (n : ℕ)
    (A L_hat U_hat : Fin n → Fin n → ℝ)
    (y_hat x_hat b : Fin n → ℝ)
    (DeltaL DeltaU : Fin n → Fin n → ℝ)
    (hn : gammaValid fp n)
    (hγ_lt_one : gamma fp n < 1)
    (hT : higham9_2_RectDoolittleRoundedStageTrace
      (Nat.le_refl n) A L_hat U_hat fp)
    (hLU : LUFactSpec n A L_hat U_hat)
    (hdetA : Matrix.det (Matrix.of A : Matrix (Fin n) (Fin n) ℝ) ≠ 0)
    (hA_tridiag : IsTridiagonal n A)
    (hColDom : IsDiagDominant n A)
    (hU_budget_le : ∀ k j : Fin n, k.val ≤ j.val →
      higham9_2_rectDoolittleUAbsBudget fp (Nat.le_refl n)
          A L_hat U_hat k j ≤ gamma fp n * |U_hat k j|)
    (hL_budget_le : ∀ i k : Fin n, k.val < i.val →
      higham9_2_rectDoolittleLAbsBudget fp A L_hat U_hat i k ≤
        gamma fp n * |L_hat i k * U_hat k k|)
    (h21 : higham9_21_tridiag_solve_perturbation_model n L_hat U_hat
      y_hat x_hat b DeltaL DeltaU (gamma fp n)) :
    ∃ DeltaA : Fin n → Fin n → ℝ,
      (∀ i j, |DeltaA i j| ≤
        3 * higham9_14_h (gamma fp n) * |A i j|) ∧
      (∀ i, ∑ j : Fin n, (A i j + DeltaA i j) * x_hat j = b i) := by
  rcases
      higham9_20_tridiag_lu_perturbation_model_of_RectDoolittleRoundedStageTrace_square_gamma
        fp n A L_hat U_hat hn hT
        (hLU.det_ne_zero_iff_U_diag_ne_zero.mp hdetA)
        hU_budget_le hL_budget_le with
    ⟨DeltaA_LU, h20⟩
  exact
    higham9_14_source_h_bound_of_absLU_le_const_absA_and_9_20_9_21_models
      n A L_hat U_hat y_hat x_hat b 3 (gamma fp n) (by norm_num)
      (gamma_nonneg fp hn) hγ_lt_one
      (higham9_13_colDiagDom_tridiag_growth_bound_3_of_LUFactSpec
        A L_hat U_hat hLU hdetA hA_tridiag hColDom)
      DeltaA_LU DeltaL DeltaU h20 h21

/-- **Theorem 9.14**, row-dominant tridiagonal rounded-stage
model-consuming final `h(γ_n)` bound. -/
theorem higham9_14_tridiag_rowDiagDom_source_h_bound_of_RectDoolittleRoundedStageTrace_square_models_gamma
    (fp : FPModel) (n : ℕ)
    (A L_hat U_hat : Fin n → Fin n → ℝ)
    (y_hat x_hat b : Fin n → ℝ)
    (DeltaL DeltaU : Fin n → Fin n → ℝ)
    (hn : gammaValid fp n)
    (hγ_lt_one : gamma fp n < 1)
    (hT : higham9_2_RectDoolittleRoundedStageTrace
      (Nat.le_refl n) A L_hat U_hat fp)
    (hLU : LUFactSpec n A L_hat U_hat)
    (hdetA : Matrix.det (Matrix.of A : Matrix (Fin n) (Fin n) ℝ) ≠ 0)
    (hA_tridiag : IsTridiagonal n A)
    (hRowDom : IsRowDiagDominant n A)
    (hU_budget_le : ∀ k j : Fin n, k.val ≤ j.val →
      higham9_2_rectDoolittleUAbsBudget fp (Nat.le_refl n)
          A L_hat U_hat k j ≤ gamma fp n * |U_hat k j|)
    (hL_budget_le : ∀ i k : Fin n, k.val < i.val →
      higham9_2_rectDoolittleLAbsBudget fp A L_hat U_hat i k ≤
        gamma fp n * |L_hat i k * U_hat k k|)
    (h21 : higham9_21_tridiag_solve_perturbation_model n L_hat U_hat
      y_hat x_hat b DeltaL DeltaU (gamma fp n)) :
    ∃ DeltaA : Fin n → Fin n → ℝ,
      (∀ i j, |DeltaA i j| ≤
        3 * higham9_14_h (gamma fp n) * |A i j|) ∧
      (∀ i, ∑ j : Fin n, (A i j + DeltaA i j) * x_hat j = b i) := by
  rcases
      higham9_20_tridiag_lu_perturbation_model_of_RectDoolittleRoundedStageTrace_square_gamma
        fp n A L_hat U_hat hn hT
        (hLU.det_ne_zero_iff_U_diag_ne_zero.mp hdetA)
        hU_budget_le hL_budget_le with
    ⟨DeltaA_LU, h20⟩
  exact
    higham9_14_source_h_bound_of_absLU_le_const_absA_and_9_20_9_21_models
      n A L_hat U_hat y_hat x_hat b 3 (gamma fp n) (by norm_num)
      (gamma_nonneg fp hn) hγ_lt_one
      (higham9_13_rowDiagDom_tridiag_growth_bound_3_of_LUFactSpec
        A L_hat U_hat hLU hdetA hA_tridiag hRowDom)
      DeltaA_LU DeltaL DeltaU h20 h21

/-- **Theorem 9.14**, SPD positive-`D L^T` rounded-stage source `f(u)` bound.

The rounded-stage trace supplies the Algorithm 9.2 source certificate, while
the positive-`D L^T` exact-factor certificate supplies the optimal
`|Lhat||Uhat| = |A|` comparison from Theorem 9.12. -/
theorem higham9_14_spd_tridiag_positive_DLT_source_f_bound_of_RectDoolittleRoundedStageTrace_square_fl_triangular_solves_gamma_le
    (fp : FPModel) (n : ℕ)
    (A L_hat U_hat : Fin n → Fin n → ℝ)
    (d b : Fin n → ℝ)
    (u : ℝ) (hu : 0 ≤ u)
    (hn : gammaValid fp n)
    (hT : higham9_2_RectDoolittleRoundedStageTrace
      (Nat.le_refl n) A L_hat U_hat fp)
    (hStruct : IsTridiagLU n L_hat U_hat)
    (hLU_eq : ∀ i j : Fin n,
      ∑ k : Fin n, L_hat i k * U_hat k j = A i j)
    (hdetA : Matrix.det (Matrix.of A : Matrix (Fin n) (Fin n) ℝ) ≠ 0)
    (hd_pos : ∀ k : Fin n, 0 < d k)
    (hDLT : ∀ k j : Fin n, U_hat k j = d k * L_hat j k)
    (hU_budget_le : ∀ k j : Fin n, k.val ≤ j.val →
      higham9_2_rectDoolittleUAbsBudget fp (Nat.le_refl n)
          A L_hat U_hat k j ≤ gamma fp n * |U_hat k j|)
    (hL_budget_le : ∀ i k : Fin n, k.val < i.val →
      higham9_2_rectDoolittleLAbsBudget fp A L_hat U_hat i k ≤
        gamma fp n * |L_hat i k * U_hat k k|)
    (hγ_le_u : gamma fp n ≤ u) :
    let y_hat := fl_forwardSub fp n L_hat b
    let x_hat := fl_backSub fp n U_hat y_hat
    ∃ DeltaA : Fin n → Fin n → ℝ,
      (∀ i j, |DeltaA i j| ≤ higham9_14_f u * |A i j|) ∧
      (∀ i, ∑ j : Fin n, (A i j + DeltaA i j) * x_hat j = b i) := by
  let hLU : LUFactSpec n A L_hat U_hat :=
    { L_diag := hStruct.L_diag
      L_upper_zero := hStruct.L_upper_zero
      U_lower_zero := hStruct.U_lower_zero
      product_eq := hLU_eq }
  simpa [one_mul] using
    (higham9_14_source_f_bound_of_RectDoolittleRoundedStageTrace_square_fl_triangular_solves_gamma_le
      fp n A L_hat U_hat b 1 u hu hn hT
      (hLU.det_ne_zero_iff_U_diag_ne_zero.mp hdetA)
      hU_budget_le hL_budget_le hγ_le_u
      (fun i j => by
        simpa [one_mul] using
          le_of_eq
            (higham9_12_spd_tridiag_absLU_eq_of_positive_DLT
              A L_hat U_hat d hStruct hLU_eq hd_pos hDLT i j)))

/-- **Theorem 9.14**, SPD positive-`D L^T` rounded-stage final `h(u)` bound. -/
theorem higham9_14_spd_tridiag_positive_DLT_source_h_bound_of_RectDoolittleRoundedStageTrace_square_fl_triangular_solves_gamma_le
    (fp : FPModel) (n : ℕ)
    (A L_hat U_hat : Fin n → Fin n → ℝ)
    (d b : Fin n → ℝ)
    (u : ℝ) (hu : 0 ≤ u) (hu_lt_one : u < 1)
    (hn : gammaValid fp n)
    (hT : higham9_2_RectDoolittleRoundedStageTrace
      (Nat.le_refl n) A L_hat U_hat fp)
    (hStruct : IsTridiagLU n L_hat U_hat)
    (hLU_eq : ∀ i j : Fin n,
      ∑ k : Fin n, L_hat i k * U_hat k j = A i j)
    (hdetA : Matrix.det (Matrix.of A : Matrix (Fin n) (Fin n) ℝ) ≠ 0)
    (hd_pos : ∀ k : Fin n, 0 < d k)
    (hDLT : ∀ k j : Fin n, U_hat k j = d k * L_hat j k)
    (hU_budget_le : ∀ k j : Fin n, k.val ≤ j.val →
      higham9_2_rectDoolittleUAbsBudget fp (Nat.le_refl n)
          A L_hat U_hat k j ≤ gamma fp n * |U_hat k j|)
    (hL_budget_le : ∀ i k : Fin n, k.val < i.val →
      higham9_2_rectDoolittleLAbsBudget fp A L_hat U_hat i k ≤
        gamma fp n * |L_hat i k * U_hat k k|)
    (hγ_le_u : gamma fp n ≤ u) :
    let y_hat := fl_forwardSub fp n L_hat b
    let x_hat := fl_backSub fp n U_hat y_hat
    ∃ DeltaA : Fin n → Fin n → ℝ,
      (∀ i j, |DeltaA i j| ≤ higham9_14_h u * |A i j|) ∧
      (∀ i, ∑ j : Fin n, (A i j + DeltaA i j) * x_hat j = b i) := by
  let hLU : LUFactSpec n A L_hat U_hat :=
    { L_diag := hStruct.L_diag
      L_upper_zero := hStruct.L_upper_zero
      U_lower_zero := hStruct.U_lower_zero
      product_eq := hLU_eq }
  exact
    higham9_14_source_h_bound_of_RectDoolittleRoundedStageTrace_square_fl_triangular_solves_gamma_le
      fp n A L_hat U_hat b u hu hu_lt_one hn hT
      (hLU.det_ne_zero_iff_U_diag_ne_zero.mp hdetA)
      hU_budget_le hL_budget_le hγ_le_u
      (fun i j => by
        exact le_of_eq
          (higham9_12_spd_tridiag_absLU_eq_of_positive_DLT
            A L_hat U_hat d hStruct hLU_eq hd_pos hDLT i j))

/-- **Theorem 9.14**, SPD positive-`D L^T` rounded-stage source `f(γ_n)` bound. -/
theorem higham9_14_spd_tridiag_positive_DLT_source_f_bound_of_RectDoolittleRoundedStageTrace_square_fl_triangular_solves_gamma
    (fp : FPModel) (n : ℕ)
    (A L_hat U_hat : Fin n → Fin n → ℝ)
    (d b : Fin n → ℝ)
    (hn : gammaValid fp n)
    (hT : higham9_2_RectDoolittleRoundedStageTrace
      (Nat.le_refl n) A L_hat U_hat fp)
    (hStruct : IsTridiagLU n L_hat U_hat)
    (hLU_eq : ∀ i j : Fin n,
      ∑ k : Fin n, L_hat i k * U_hat k j = A i j)
    (hdetA : Matrix.det (Matrix.of A : Matrix (Fin n) (Fin n) ℝ) ≠ 0)
    (hd_pos : ∀ k : Fin n, 0 < d k)
    (hDLT : ∀ k j : Fin n, U_hat k j = d k * L_hat j k)
    (hU_budget_le : ∀ k j : Fin n, k.val ≤ j.val →
      higham9_2_rectDoolittleUAbsBudget fp (Nat.le_refl n)
          A L_hat U_hat k j ≤ gamma fp n * |U_hat k j|)
    (hL_budget_le : ∀ i k : Fin n, k.val < i.val →
      higham9_2_rectDoolittleLAbsBudget fp A L_hat U_hat i k ≤
        gamma fp n * |L_hat i k * U_hat k k|) :
    let y_hat := fl_forwardSub fp n L_hat b
    let x_hat := fl_backSub fp n U_hat y_hat
    ∃ DeltaA : Fin n → Fin n → ℝ,
      (∀ i j, |DeltaA i j| ≤
        higham9_14_f (gamma fp n) * |A i j|) ∧
      (∀ i, ∑ j : Fin n, (A i j + DeltaA i j) * x_hat j = b i) :=
  higham9_14_spd_tridiag_positive_DLT_source_f_bound_of_RectDoolittleRoundedStageTrace_square_fl_triangular_solves_gamma_le
    fp n A L_hat U_hat d b (gamma fp n) (gamma_nonneg fp hn) hn
    hT hStruct hLU_eq hdetA hd_pos hDLT hU_budget_le hL_budget_le le_rfl

/-- **Theorem 9.14**, SPD positive-`D L^T` rounded-stage final `h(γ_n)` bound. -/
theorem higham9_14_spd_tridiag_positive_DLT_source_h_bound_of_RectDoolittleRoundedStageTrace_square_fl_triangular_solves_gamma
    (fp : FPModel) (n : ℕ)
    (A L_hat U_hat : Fin n → Fin n → ℝ)
    (d b : Fin n → ℝ)
    (hn : gammaValid fp n)
    (hγ_lt_one : gamma fp n < 1)
    (hT : higham9_2_RectDoolittleRoundedStageTrace
      (Nat.le_refl n) A L_hat U_hat fp)
    (hStruct : IsTridiagLU n L_hat U_hat)
    (hLU_eq : ∀ i j : Fin n,
      ∑ k : Fin n, L_hat i k * U_hat k j = A i j)
    (hdetA : Matrix.det (Matrix.of A : Matrix (Fin n) (Fin n) ℝ) ≠ 0)
    (hd_pos : ∀ k : Fin n, 0 < d k)
    (hDLT : ∀ k j : Fin n, U_hat k j = d k * L_hat j k)
    (hU_budget_le : ∀ k j : Fin n, k.val ≤ j.val →
      higham9_2_rectDoolittleUAbsBudget fp (Nat.le_refl n)
          A L_hat U_hat k j ≤ gamma fp n * |U_hat k j|)
    (hL_budget_le : ∀ i k : Fin n, k.val < i.val →
      higham9_2_rectDoolittleLAbsBudget fp A L_hat U_hat i k ≤
        gamma fp n * |L_hat i k * U_hat k k|) :
    let y_hat := fl_forwardSub fp n L_hat b
    let x_hat := fl_backSub fp n U_hat y_hat
    ∃ DeltaA : Fin n → Fin n → ℝ,
      (∀ i j, |DeltaA i j| ≤
        higham9_14_h (gamma fp n) * |A i j|) ∧
      (∀ i, ∑ j : Fin n, (A i j + DeltaA i j) * x_hat j = b i) :=
  higham9_14_spd_tridiag_positive_DLT_source_h_bound_of_RectDoolittleRoundedStageTrace_square_fl_triangular_solves_gamma_le
    fp n A L_hat U_hat d b (gamma fp n) (gamma_nonneg fp hn)
    hγ_lt_one hn hT hStruct hLU_eq hdetA hd_pos hDLT
    hU_budget_le hL_budget_le le_rfl

/-- **Theorem 9.14**, SPD positive-`D L^T` rounded-stage source `f(u)`
bound, deriving nonsingularity from the source SPD hypothesis. -/
theorem higham9_14_spd_tridiag_positive_DLT_source_f_bound_of_spd_RectDoolittleRoundedStageTrace_square_fl_triangular_solves_gamma_le
    (fp : FPModel) (n : ℕ)
    (A L_hat U_hat : Fin n → Fin n → ℝ)
    (d b : Fin n → ℝ)
    (u : ℝ) (hu : 0 ≤ u)
    (hn : gammaValid fp n)
    (hSPD : IsSymPosDef n A)
    (hT : higham9_2_RectDoolittleRoundedStageTrace
      (Nat.le_refl n) A L_hat U_hat fp)
    (hStruct : IsTridiagLU n L_hat U_hat)
    (hLU_eq : ∀ i j : Fin n,
      ∑ k : Fin n, L_hat i k * U_hat k j = A i j)
    (hd_pos : ∀ k : Fin n, 0 < d k)
    (hDLT : ∀ k j : Fin n, U_hat k j = d k * L_hat j k)
    (hU_budget_le : ∀ k j : Fin n, k.val ≤ j.val →
      higham9_2_rectDoolittleUAbsBudget fp (Nat.le_refl n)
          A L_hat U_hat k j ≤ gamma fp n * |U_hat k j|)
    (hL_budget_le : ∀ i k : Fin n, k.val < i.val →
      higham9_2_rectDoolittleLAbsBudget fp A L_hat U_hat i k ≤
        gamma fp n * |L_hat i k * U_hat k k|)
    (hγ_le_u : gamma fp n ≤ u) :
    let y_hat := fl_forwardSub fp n L_hat b
    let x_hat := fl_backSub fp n U_hat y_hat
    ∃ DeltaA : Fin n → Fin n → ℝ,
      (∀ i j, |DeltaA i j| ≤ higham9_14_f u * |A i j|) ∧
      (∀ i, ∑ j : Fin n, (A i j + DeltaA i j) * x_hat j = b i) :=
  higham9_14_spd_tridiag_positive_DLT_source_f_bound_of_RectDoolittleRoundedStageTrace_square_fl_triangular_solves_gamma_le
    fp n A L_hat U_hat d b u hu hn hT hStruct hLU_eq
    (by simpa using isSymPosDef_det_ne_zero A hSPD)
    hd_pos hDLT hU_budget_le hL_budget_le hγ_le_u

/-- **Theorem 9.14**, SPD positive-`D L^T` rounded-stage final `h(u)` bound,
deriving nonsingularity from the source SPD hypothesis. -/
theorem higham9_14_spd_tridiag_positive_DLT_source_h_bound_of_spd_RectDoolittleRoundedStageTrace_square_fl_triangular_solves_gamma_le
    (fp : FPModel) (n : ℕ)
    (A L_hat U_hat : Fin n → Fin n → ℝ)
    (d b : Fin n → ℝ)
    (u : ℝ) (hu : 0 ≤ u) (hu_lt_one : u < 1)
    (hn : gammaValid fp n)
    (hSPD : IsSymPosDef n A)
    (hT : higham9_2_RectDoolittleRoundedStageTrace
      (Nat.le_refl n) A L_hat U_hat fp)
    (hStruct : IsTridiagLU n L_hat U_hat)
    (hLU_eq : ∀ i j : Fin n,
      ∑ k : Fin n, L_hat i k * U_hat k j = A i j)
    (hd_pos : ∀ k : Fin n, 0 < d k)
    (hDLT : ∀ k j : Fin n, U_hat k j = d k * L_hat j k)
    (hU_budget_le : ∀ k j : Fin n, k.val ≤ j.val →
      higham9_2_rectDoolittleUAbsBudget fp (Nat.le_refl n)
          A L_hat U_hat k j ≤ gamma fp n * |U_hat k j|)
    (hL_budget_le : ∀ i k : Fin n, k.val < i.val →
      higham9_2_rectDoolittleLAbsBudget fp A L_hat U_hat i k ≤
        gamma fp n * |L_hat i k * U_hat k k|)
    (hγ_le_u : gamma fp n ≤ u) :
    let y_hat := fl_forwardSub fp n L_hat b
    let x_hat := fl_backSub fp n U_hat y_hat
    ∃ DeltaA : Fin n → Fin n → ℝ,
      (∀ i j, |DeltaA i j| ≤ higham9_14_h u * |A i j|) ∧
      (∀ i, ∑ j : Fin n, (A i j + DeltaA i j) * x_hat j = b i) :=
  higham9_14_spd_tridiag_positive_DLT_source_h_bound_of_RectDoolittleRoundedStageTrace_square_fl_triangular_solves_gamma_le
    fp n A L_hat U_hat d b u hu hu_lt_one hn hT hStruct hLU_eq
    (by simpa using isSymPosDef_det_ne_zero A hSPD)
    hd_pos hDLT hU_budget_le hL_budget_le hγ_le_u

/-- **Theorem 9.14**, SPD positive-`D L^T` rounded-stage source
`f(γ_n)` bound, deriving nonsingularity from SPD. -/
theorem higham9_14_spd_tridiag_positive_DLT_source_f_bound_of_spd_RectDoolittleRoundedStageTrace_square_fl_triangular_solves_gamma
    (fp : FPModel) (n : ℕ)
    (A L_hat U_hat : Fin n → Fin n → ℝ)
    (d b : Fin n → ℝ)
    (hn : gammaValid fp n)
    (hSPD : IsSymPosDef n A)
    (hT : higham9_2_RectDoolittleRoundedStageTrace
      (Nat.le_refl n) A L_hat U_hat fp)
    (hStruct : IsTridiagLU n L_hat U_hat)
    (hLU_eq : ∀ i j : Fin n,
      ∑ k : Fin n, L_hat i k * U_hat k j = A i j)
    (hd_pos : ∀ k : Fin n, 0 < d k)
    (hDLT : ∀ k j : Fin n, U_hat k j = d k * L_hat j k)
    (hU_budget_le : ∀ k j : Fin n, k.val ≤ j.val →
      higham9_2_rectDoolittleUAbsBudget fp (Nat.le_refl n)
          A L_hat U_hat k j ≤ gamma fp n * |U_hat k j|)
    (hL_budget_le : ∀ i k : Fin n, k.val < i.val →
      higham9_2_rectDoolittleLAbsBudget fp A L_hat U_hat i k ≤
        gamma fp n * |L_hat i k * U_hat k k|) :
    let y_hat := fl_forwardSub fp n L_hat b
    let x_hat := fl_backSub fp n U_hat y_hat
    ∃ DeltaA : Fin n → Fin n → ℝ,
      (∀ i j, |DeltaA i j| ≤
        higham9_14_f (gamma fp n) * |A i j|) ∧
      (∀ i, ∑ j : Fin n, (A i j + DeltaA i j) * x_hat j = b i) :=
  higham9_14_spd_tridiag_positive_DLT_source_f_bound_of_RectDoolittleRoundedStageTrace_square_fl_triangular_solves_gamma
    fp n A L_hat U_hat d b hn hT hStruct hLU_eq
    (by simpa using isSymPosDef_det_ne_zero A hSPD)
    hd_pos hDLT hU_budget_le hL_budget_le

/-- **Theorem 9.14**, SPD positive-`D L^T` rounded-stage final `h(γ_n)`
bound, deriving nonsingularity from SPD. -/
theorem higham9_14_spd_tridiag_positive_DLT_source_h_bound_of_spd_RectDoolittleRoundedStageTrace_square_fl_triangular_solves_gamma
    (fp : FPModel) (n : ℕ)
    (A L_hat U_hat : Fin n → Fin n → ℝ)
    (d b : Fin n → ℝ)
    (hn : gammaValid fp n)
    (hγ_lt_one : gamma fp n < 1)
    (hSPD : IsSymPosDef n A)
    (hT : higham9_2_RectDoolittleRoundedStageTrace
      (Nat.le_refl n) A L_hat U_hat fp)
    (hStruct : IsTridiagLU n L_hat U_hat)
    (hLU_eq : ∀ i j : Fin n,
      ∑ k : Fin n, L_hat i k * U_hat k j = A i j)
    (hd_pos : ∀ k : Fin n, 0 < d k)
    (hDLT : ∀ k j : Fin n, U_hat k j = d k * L_hat j k)
    (hU_budget_le : ∀ k j : Fin n, k.val ≤ j.val →
      higham9_2_rectDoolittleUAbsBudget fp (Nat.le_refl n)
          A L_hat U_hat k j ≤ gamma fp n * |U_hat k j|)
    (hL_budget_le : ∀ i k : Fin n, k.val < i.val →
      higham9_2_rectDoolittleLAbsBudget fp A L_hat U_hat i k ≤
        gamma fp n * |L_hat i k * U_hat k k|) :
    let y_hat := fl_forwardSub fp n L_hat b
    let x_hat := fl_backSub fp n U_hat y_hat
    ∃ DeltaA : Fin n → Fin n → ℝ,
      (∀ i j, |DeltaA i j| ≤
        higham9_14_h (gamma fp n) * |A i j|) ∧
      (∀ i, ∑ j : Fin n, (A i j + DeltaA i j) * x_hat j = b i) :=
  higham9_14_spd_tridiag_positive_DLT_source_h_bound_of_RectDoolittleRoundedStageTrace_square_fl_triangular_solves_gamma
    fp n A L_hat U_hat d b hn hγ_lt_one hT hStruct hLU_eq
    (by simpa using isSymPosDef_det_ne_zero A hSPD)
    hd_pos hDLT hU_budget_le hL_budget_le

/-- **Theorem 9.14**, nonnegative-LU rounded-stage source `f(u)` bound.

The rounded-stage trace supplies the Algorithm 9.2 source certificate, while
Theorem 9.12 supplies the optimal `|Lhat||Uhat| = |A|` comparison for
nonnegative LU factors. -/
theorem higham9_14_nonnegative_lu_source_f_bound_of_RectDoolittleRoundedStageTrace_square_fl_triangular_solves_gamma_le
    (fp : FPModel) (n : ℕ)
    (A L_hat U_hat : Fin n → Fin n → ℝ)
    (b : Fin n → ℝ)
    (u : ℝ) (hu : 0 ≤ u)
    (hn : gammaValid fp n)
    (hT : higham9_2_RectDoolittleRoundedStageTrace
      (Nat.le_refl n) A L_hat U_hat fp)
    (hNonneg : HasNonnegLUFactors n A L_hat U_hat)
    (hdetA : Matrix.det (Matrix.of A : Matrix (Fin n) (Fin n) ℝ) ≠ 0)
    (hU_budget_le : ∀ k j : Fin n, k.val ≤ j.val →
      higham9_2_rectDoolittleUAbsBudget fp (Nat.le_refl n)
          A L_hat U_hat k j ≤ gamma fp n * |U_hat k j|)
    (hL_budget_le : ∀ i k : Fin n, k.val < i.val →
      higham9_2_rectDoolittleLAbsBudget fp A L_hat U_hat i k ≤
        gamma fp n * |L_hat i k * U_hat k k|)
    (hγ_le_u : gamma fp n ≤ u) :
    let y_hat := fl_forwardSub fp n L_hat b
    let x_hat := fl_backSub fp n U_hat y_hat
    ∃ DeltaA : Fin n → Fin n → ℝ,
      (∀ i j, |DeltaA i j| ≤ higham9_14_f u * |A i j|) ∧
      (∀ i, ∑ j : Fin n, (A i j + DeltaA i j) * x_hat j = b i) := by
  simpa [one_mul] using
    (higham9_14_source_f_bound_of_RectDoolittleRoundedStageTrace_square_fl_triangular_solves_gamma_le
      fp n A L_hat U_hat b 1 u hu hn hT
      (hNonneg.1.det_ne_zero_iff_U_diag_ne_zero.mp hdetA)
      hU_budget_le hL_budget_le hγ_le_u
      (fun i j => by
        simpa [one_mul] using
          le_of_eq
            (higham9_12_nonneg_lu_optimal_growth n A L_hat U_hat
              hNonneg i j)))

/-- **Theorem 9.14**, nonnegative-LU rounded-stage final `h(u)` bound. -/
theorem higham9_14_nonnegative_lu_source_h_bound_of_RectDoolittleRoundedStageTrace_square_fl_triangular_solves_gamma_le
    (fp : FPModel) (n : ℕ)
    (A L_hat U_hat : Fin n → Fin n → ℝ)
    (b : Fin n → ℝ)
    (u : ℝ) (hu : 0 ≤ u) (hu_lt_one : u < 1)
    (hn : gammaValid fp n)
    (hT : higham9_2_RectDoolittleRoundedStageTrace
      (Nat.le_refl n) A L_hat U_hat fp)
    (hNonneg : HasNonnegLUFactors n A L_hat U_hat)
    (hdetA : Matrix.det (Matrix.of A : Matrix (Fin n) (Fin n) ℝ) ≠ 0)
    (hU_budget_le : ∀ k j : Fin n, k.val ≤ j.val →
      higham9_2_rectDoolittleUAbsBudget fp (Nat.le_refl n)
          A L_hat U_hat k j ≤ gamma fp n * |U_hat k j|)
    (hL_budget_le : ∀ i k : Fin n, k.val < i.val →
      higham9_2_rectDoolittleLAbsBudget fp A L_hat U_hat i k ≤
        gamma fp n * |L_hat i k * U_hat k k|)
    (hγ_le_u : gamma fp n ≤ u) :
    let y_hat := fl_forwardSub fp n L_hat b
    let x_hat := fl_backSub fp n U_hat y_hat
    ∃ DeltaA : Fin n → Fin n → ℝ,
      (∀ i j, |DeltaA i j| ≤ higham9_14_h u * |A i j|) ∧
      (∀ i, ∑ j : Fin n, (A i j + DeltaA i j) * x_hat j = b i) :=
  higham9_14_source_h_bound_of_RectDoolittleRoundedStageTrace_square_fl_triangular_solves_gamma_le
    fp n A L_hat U_hat b u hu hu_lt_one hn hT
    (hNonneg.1.det_ne_zero_iff_U_diag_ne_zero.mp hdetA)
    hU_budget_le hL_budget_le hγ_le_u
    (fun i j => by
      exact le_of_eq
        (higham9_12_nonneg_lu_optimal_growth n A L_hat U_hat
          hNonneg i j))

/-- **Theorem 9.14**, nonnegative-LU rounded-stage source `f(γ_n)` bound. -/
theorem higham9_14_nonnegative_lu_source_f_bound_of_RectDoolittleRoundedStageTrace_square_fl_triangular_solves_gamma
    (fp : FPModel) (n : ℕ)
    (A L_hat U_hat : Fin n → Fin n → ℝ)
    (b : Fin n → ℝ)
    (hn : gammaValid fp n)
    (hT : higham9_2_RectDoolittleRoundedStageTrace
      (Nat.le_refl n) A L_hat U_hat fp)
    (hNonneg : HasNonnegLUFactors n A L_hat U_hat)
    (hdetA : Matrix.det (Matrix.of A : Matrix (Fin n) (Fin n) ℝ) ≠ 0)
    (hU_budget_le : ∀ k j : Fin n, k.val ≤ j.val →
      higham9_2_rectDoolittleUAbsBudget fp (Nat.le_refl n)
          A L_hat U_hat k j ≤ gamma fp n * |U_hat k j|)
    (hL_budget_le : ∀ i k : Fin n, k.val < i.val →
      higham9_2_rectDoolittleLAbsBudget fp A L_hat U_hat i k ≤
        gamma fp n * |L_hat i k * U_hat k k|) :
    let y_hat := fl_forwardSub fp n L_hat b
    let x_hat := fl_backSub fp n U_hat y_hat
    ∃ DeltaA : Fin n → Fin n → ℝ,
      (∀ i j, |DeltaA i j| ≤
        higham9_14_f (gamma fp n) * |A i j|) ∧
      (∀ i, ∑ j : Fin n, (A i j + DeltaA i j) * x_hat j = b i) :=
  higham9_14_nonnegative_lu_source_f_bound_of_RectDoolittleRoundedStageTrace_square_fl_triangular_solves_gamma_le
    fp n A L_hat U_hat b (gamma fp n) (gamma_nonneg fp hn) hn hT
    hNonneg hdetA hU_budget_le hL_budget_le le_rfl

/-- **Theorem 9.14**, nonnegative-LU rounded-stage final `h(γ_n)` bound. -/
theorem higham9_14_nonnegative_lu_source_h_bound_of_RectDoolittleRoundedStageTrace_square_fl_triangular_solves_gamma
    (fp : FPModel) (n : ℕ)
    (A L_hat U_hat : Fin n → Fin n → ℝ)
    (b : Fin n → ℝ)
    (hn : gammaValid fp n)
    (hγ_lt_one : gamma fp n < 1)
    (hT : higham9_2_RectDoolittleRoundedStageTrace
      (Nat.le_refl n) A L_hat U_hat fp)
    (hNonneg : HasNonnegLUFactors n A L_hat U_hat)
    (hdetA : Matrix.det (Matrix.of A : Matrix (Fin n) (Fin n) ℝ) ≠ 0)
    (hU_budget_le : ∀ k j : Fin n, k.val ≤ j.val →
      higham9_2_rectDoolittleUAbsBudget fp (Nat.le_refl n)
          A L_hat U_hat k j ≤ gamma fp n * |U_hat k j|)
    (hL_budget_le : ∀ i k : Fin n, k.val < i.val →
      higham9_2_rectDoolittleLAbsBudget fp A L_hat U_hat i k ≤
        gamma fp n * |L_hat i k * U_hat k k|) :
    let y_hat := fl_forwardSub fp n L_hat b
    let x_hat := fl_backSub fp n U_hat y_hat
    ∃ DeltaA : Fin n → Fin n → ℝ,
      (∀ i j, |DeltaA i j| ≤
        higham9_14_h (gamma fp n) * |A i j|) ∧
      (∀ i, ∑ j : Fin n, (A i j + DeltaA i j) * x_hat j = b i) :=
  higham9_14_nonnegative_lu_source_h_bound_of_RectDoolittleRoundedStageTrace_square_fl_triangular_solves_gamma_le
    fp n A L_hat U_hat b (gamma fp n) (gamma_nonneg fp hn) hγ_lt_one
    hn hT hNonneg hdetA hU_budget_le hL_budget_le le_rfl

/-- **Theorem 9.14**, Matrix-facing nonnegative-LU rounded-stage source
`f(u)` bound. -/
theorem higham9_14_matrix_nonnegative_lu_source_f_bound_of_RectDoolittleRoundedStageTrace_square_fl_triangular_solves_gamma_le
    (fp : FPModel) (n : ℕ)
    (A L_hat U_hat : Matrix (Fin n) (Fin n) ℝ)
    (b : Fin n → ℝ)
    (u : ℝ) (hu : 0 ≤ u)
    (hn : gammaValid fp n)
    (hT : higham9_2_RectDoolittleRoundedStageTrace
      (Nat.le_refl n) A L_hat U_hat fp)
    (hNonneg : HasNonnegLUFactors n A L_hat U_hat)
    (hdetA : Matrix.det A ≠ 0)
    (hU_budget_le : ∀ k j : Fin n, k.val ≤ j.val →
      higham9_2_rectDoolittleUAbsBudget fp (Nat.le_refl n)
          A L_hat U_hat k j ≤ gamma fp n * |U_hat k j|)
    (hL_budget_le : ∀ i k : Fin n, k.val < i.val →
      higham9_2_rectDoolittleLAbsBudget fp A L_hat U_hat i k ≤
        gamma fp n * |L_hat i k * U_hat k k|)
    (hγ_le_u : gamma fp n ≤ u) :
    let y_hat := fl_forwardSub fp n L_hat b
    let x_hat := fl_backSub fp n U_hat y_hat
    ∃ DeltaA : Matrix (Fin n) (Fin n) ℝ,
      (∀ i j, |DeltaA i j| ≤ higham9_14_f u * |A i j|) ∧
      Matrix.mulVec (fun i j => A i j + DeltaA i j) x_hat = b :=
  higham9_14_matrix_source_f_bound_of_RectDoolittleRoundedStageTrace_square_fl_triangular_solves_absLU_le_absA_gamma_le
    fp n A L_hat U_hat b u hu hn hT
    (hNonneg.1.det_ne_zero_iff_U_diag_ne_zero.mp hdetA)
    hU_budget_le hL_budget_le hγ_le_u
    (fun i j =>
      le_of_eq
        (higham9_12_nonneg_lu_optimal_growth n A L_hat U_hat
          hNonneg i j))

/-- **Theorem 9.14**, Matrix-facing nonnegative-LU rounded-stage final
`h(u)` bound. -/
theorem higham9_14_matrix_nonnegative_lu_source_h_bound_of_RectDoolittleRoundedStageTrace_square_fl_triangular_solves_gamma_le
    (fp : FPModel) (n : ℕ)
    (A L_hat U_hat : Matrix (Fin n) (Fin n) ℝ)
    (b : Fin n → ℝ)
    (u : ℝ) (hu : 0 ≤ u) (hu_lt_one : u < 1)
    (hn : gammaValid fp n)
    (hT : higham9_2_RectDoolittleRoundedStageTrace
      (Nat.le_refl n) A L_hat U_hat fp)
    (hNonneg : HasNonnegLUFactors n A L_hat U_hat)
    (hdetA : Matrix.det A ≠ 0)
    (hU_budget_le : ∀ k j : Fin n, k.val ≤ j.val →
      higham9_2_rectDoolittleUAbsBudget fp (Nat.le_refl n)
          A L_hat U_hat k j ≤ gamma fp n * |U_hat k j|)
    (hL_budget_le : ∀ i k : Fin n, k.val < i.val →
      higham9_2_rectDoolittleLAbsBudget fp A L_hat U_hat i k ≤
        gamma fp n * |L_hat i k * U_hat k k|)
    (hγ_le_u : gamma fp n ≤ u) :
    let y_hat := fl_forwardSub fp n L_hat b
    let x_hat := fl_backSub fp n U_hat y_hat
    ∃ DeltaA : Matrix (Fin n) (Fin n) ℝ,
      (∀ i j, |DeltaA i j| ≤ higham9_14_h u * |A i j|) ∧
      Matrix.mulVec (fun i j => A i j + DeltaA i j) x_hat = b :=
  higham9_14_matrix_source_h_bound_of_RectDoolittleRoundedStageTrace_square_fl_triangular_solves_absLU_le_absA_gamma_le
    fp n A L_hat U_hat b u hu hu_lt_one hn hT
    (hNonneg.1.det_ne_zero_iff_U_diag_ne_zero.mp hdetA)
    hU_budget_le hL_budget_le hγ_le_u
    (fun i j =>
      le_of_eq
        (higham9_12_nonneg_lu_optimal_growth n A L_hat U_hat
          hNonneg i j))

/-- **Theorem 9.14**, Matrix-facing nonnegative-LU rounded-stage source
`f(γ_n)` bound. -/
theorem higham9_14_matrix_nonnegative_lu_source_f_bound_of_RectDoolittleRoundedStageTrace_square_fl_triangular_solves_gamma
    (fp : FPModel) (n : ℕ)
    (A L_hat U_hat : Matrix (Fin n) (Fin n) ℝ)
    (b : Fin n → ℝ)
    (hn : gammaValid fp n)
    (hT : higham9_2_RectDoolittleRoundedStageTrace
      (Nat.le_refl n) A L_hat U_hat fp)
    (hNonneg : HasNonnegLUFactors n A L_hat U_hat)
    (hdetA : Matrix.det A ≠ 0)
    (hU_budget_le : ∀ k j : Fin n, k.val ≤ j.val →
      higham9_2_rectDoolittleUAbsBudget fp (Nat.le_refl n)
          A L_hat U_hat k j ≤ gamma fp n * |U_hat k j|)
    (hL_budget_le : ∀ i k : Fin n, k.val < i.val →
      higham9_2_rectDoolittleLAbsBudget fp A L_hat U_hat i k ≤
        gamma fp n * |L_hat i k * U_hat k k|) :
    let y_hat := fl_forwardSub fp n L_hat b
    let x_hat := fl_backSub fp n U_hat y_hat
    ∃ DeltaA : Matrix (Fin n) (Fin n) ℝ,
      (∀ i j, |DeltaA i j| ≤
        higham9_14_f (gamma fp n) * |A i j|) ∧
      Matrix.mulVec (fun i j => A i j + DeltaA i j) x_hat = b :=
  higham9_14_matrix_nonnegative_lu_source_f_bound_of_RectDoolittleRoundedStageTrace_square_fl_triangular_solves_gamma_le
    fp n A L_hat U_hat b (gamma fp n) (gamma_nonneg fp hn) hn hT
    hNonneg hdetA hU_budget_le hL_budget_le le_rfl

/-- **Theorem 9.14**, Matrix-facing nonnegative-LU rounded-stage final
`h(γ_n)` bound. -/
theorem higham9_14_matrix_nonnegative_lu_source_h_bound_of_RectDoolittleRoundedStageTrace_square_fl_triangular_solves_gamma
    (fp : FPModel) (n : ℕ)
    (A L_hat U_hat : Matrix (Fin n) (Fin n) ℝ)
    (b : Fin n → ℝ)
    (hn : gammaValid fp n)
    (hγ_lt_one : gamma fp n < 1)
    (hT : higham9_2_RectDoolittleRoundedStageTrace
      (Nat.le_refl n) A L_hat U_hat fp)
    (hNonneg : HasNonnegLUFactors n A L_hat U_hat)
    (hdetA : Matrix.det A ≠ 0)
    (hU_budget_le : ∀ k j : Fin n, k.val ≤ j.val →
      higham9_2_rectDoolittleUAbsBudget fp (Nat.le_refl n)
          A L_hat U_hat k j ≤ gamma fp n * |U_hat k j|)
    (hL_budget_le : ∀ i k : Fin n, k.val < i.val →
      higham9_2_rectDoolittleLAbsBudget fp A L_hat U_hat i k ≤
        gamma fp n * |L_hat i k * U_hat k k|) :
    let y_hat := fl_forwardSub fp n L_hat b
    let x_hat := fl_backSub fp n U_hat y_hat
    ∃ DeltaA : Matrix (Fin n) (Fin n) ℝ,
      (∀ i j, |DeltaA i j| ≤
        higham9_14_h (gamma fp n) * |A i j|) ∧
      Matrix.mulVec (fun i j => A i j + DeltaA i j) x_hat = b :=
  higham9_14_matrix_nonnegative_lu_source_h_bound_of_RectDoolittleRoundedStageTrace_square_fl_triangular_solves_gamma_le
    fp n A L_hat U_hat b (gamma fp n) (gamma_nonneg fp hn) hγ_lt_one
    hn hT hNonneg hdetA hU_budget_le hL_budget_le le_rfl

/-- **Theorem 9.14**, M-matrix rounded-stage source `f(u)` bound. -/
theorem higham9_14_mmatrix_lu_source_f_bound_of_RectDoolittleRoundedStageTrace_square_fl_triangular_solves_gamma_le
    (fp : FPModel) (n : ℕ)
    (A L_hat U_hat : Fin n → Fin n → ℝ)
    (b : Fin n → ℝ)
    (u : ℝ) (hu : 0 ≤ u)
    (hn : gammaValid fp n)
    (hT : higham9_2_RectDoolittleRoundedStageTrace
      (Nat.le_refl n) A L_hat U_hat fp)
    (hM : IsMMatrix n A)
    (hLU : LUFactSpec n A L_hat U_hat)
    (hdetA : Matrix.det (Matrix.of A : Matrix (Fin n) (Fin n) ℝ) ≠ 0)
    (hL_nn : ∀ i k : Fin n, 0 ≤ L_hat i k)
    (hU_nn : ∀ k j : Fin n, 0 ≤ U_hat k j)
    (hU_budget_le : ∀ k j : Fin n, k.val ≤ j.val →
      higham9_2_rectDoolittleUAbsBudget fp (Nat.le_refl n)
          A L_hat U_hat k j ≤ gamma fp n * |U_hat k j|)
    (hL_budget_le : ∀ i k : Fin n, k.val < i.val →
      higham9_2_rectDoolittleLAbsBudget fp A L_hat U_hat i k ≤
        gamma fp n * |L_hat i k * U_hat k k|)
    (hγ_le_u : gamma fp n ≤ u) :
    let y_hat := fl_forwardSub fp n L_hat b
    let x_hat := fl_backSub fp n U_hat y_hat
    ∃ DeltaA : Fin n → Fin n → ℝ,
      (∀ i j, |DeltaA i j| ≤ higham9_14_f u * |A i j|) ∧
      (∀ i, ∑ j : Fin n, (A i j + DeltaA i j) * x_hat j = b i) := by
  simpa [one_mul] using
    (higham9_14_source_f_bound_of_RectDoolittleRoundedStageTrace_square_fl_triangular_solves_gamma_le
      fp n A L_hat U_hat b 1 u hu hn hT
      (hLU.det_ne_zero_iff_U_diag_ne_zero.mp hdetA)
      hU_budget_le hL_budget_le hγ_le_u
      (fun i j => by
        simpa [one_mul] using
          le_of_eq
            (higham9_12_mmatrix_lu_optimal_growth n A L_hat U_hat
              hM hLU hL_nn hU_nn i j)))

/-- **Theorem 9.14**, M-matrix rounded-stage final `h(u)` bound. -/
theorem higham9_14_mmatrix_lu_source_h_bound_of_RectDoolittleRoundedStageTrace_square_fl_triangular_solves_gamma_le
    (fp : FPModel) (n : ℕ)
    (A L_hat U_hat : Fin n → Fin n → ℝ)
    (b : Fin n → ℝ)
    (u : ℝ) (hu : 0 ≤ u) (hu_lt_one : u < 1)
    (hn : gammaValid fp n)
    (hT : higham9_2_RectDoolittleRoundedStageTrace
      (Nat.le_refl n) A L_hat U_hat fp)
    (hM : IsMMatrix n A)
    (hLU : LUFactSpec n A L_hat U_hat)
    (hdetA : Matrix.det (Matrix.of A : Matrix (Fin n) (Fin n) ℝ) ≠ 0)
    (hL_nn : ∀ i k : Fin n, 0 ≤ L_hat i k)
    (hU_nn : ∀ k j : Fin n, 0 ≤ U_hat k j)
    (hU_budget_le : ∀ k j : Fin n, k.val ≤ j.val →
      higham9_2_rectDoolittleUAbsBudget fp (Nat.le_refl n)
          A L_hat U_hat k j ≤ gamma fp n * |U_hat k j|)
    (hL_budget_le : ∀ i k : Fin n, k.val < i.val →
      higham9_2_rectDoolittleLAbsBudget fp A L_hat U_hat i k ≤
        gamma fp n * |L_hat i k * U_hat k k|)
    (hγ_le_u : gamma fp n ≤ u) :
    let y_hat := fl_forwardSub fp n L_hat b
    let x_hat := fl_backSub fp n U_hat y_hat
    ∃ DeltaA : Fin n → Fin n → ℝ,
      (∀ i j, |DeltaA i j| ≤ higham9_14_h u * |A i j|) ∧
      (∀ i, ∑ j : Fin n, (A i j + DeltaA i j) * x_hat j = b i) :=
  higham9_14_source_h_bound_of_RectDoolittleRoundedStageTrace_square_fl_triangular_solves_gamma_le
    fp n A L_hat U_hat b u hu hu_lt_one hn hT
    (hLU.det_ne_zero_iff_U_diag_ne_zero.mp hdetA)
    hU_budget_le hL_budget_le hγ_le_u
    (fun i j => by
      exact le_of_eq
        (higham9_12_mmatrix_lu_optimal_growth n A L_hat U_hat
          hM hLU hL_nn hU_nn i j))

/-- **Theorem 9.14**, M-matrix rounded-stage source `f(γ_n)` bound. -/
theorem higham9_14_mmatrix_lu_source_f_bound_of_RectDoolittleRoundedStageTrace_square_fl_triangular_solves_gamma
    (fp : FPModel) (n : ℕ)
    (A L_hat U_hat : Fin n → Fin n → ℝ)
    (b : Fin n → ℝ)
    (hn : gammaValid fp n)
    (hT : higham9_2_RectDoolittleRoundedStageTrace
      (Nat.le_refl n) A L_hat U_hat fp)
    (hM : IsMMatrix n A)
    (hLU : LUFactSpec n A L_hat U_hat)
    (hdetA : Matrix.det (Matrix.of A : Matrix (Fin n) (Fin n) ℝ) ≠ 0)
    (hL_nn : ∀ i k : Fin n, 0 ≤ L_hat i k)
    (hU_nn : ∀ k j : Fin n, 0 ≤ U_hat k j)
    (hU_budget_le : ∀ k j : Fin n, k.val ≤ j.val →
      higham9_2_rectDoolittleUAbsBudget fp (Nat.le_refl n)
          A L_hat U_hat k j ≤ gamma fp n * |U_hat k j|)
    (hL_budget_le : ∀ i k : Fin n, k.val < i.val →
      higham9_2_rectDoolittleLAbsBudget fp A L_hat U_hat i k ≤
        gamma fp n * |L_hat i k * U_hat k k|) :
    let y_hat := fl_forwardSub fp n L_hat b
    let x_hat := fl_backSub fp n U_hat y_hat
    ∃ DeltaA : Fin n → Fin n → ℝ,
      (∀ i j, |DeltaA i j| ≤
        higham9_14_f (gamma fp n) * |A i j|) ∧
      (∀ i, ∑ j : Fin n, (A i j + DeltaA i j) * x_hat j = b i) :=
  higham9_14_mmatrix_lu_source_f_bound_of_RectDoolittleRoundedStageTrace_square_fl_triangular_solves_gamma_le
    fp n A L_hat U_hat b (gamma fp n) (gamma_nonneg fp hn) hn hT
    hM hLU hdetA hL_nn hU_nn hU_budget_le hL_budget_le le_rfl

/-- **Theorem 9.14**, M-matrix rounded-stage final `h(γ_n)` bound. -/
theorem higham9_14_mmatrix_lu_source_h_bound_of_RectDoolittleRoundedStageTrace_square_fl_triangular_solves_gamma
    (fp : FPModel) (n : ℕ)
    (A L_hat U_hat : Fin n → Fin n → ℝ)
    (b : Fin n → ℝ)
    (hn : gammaValid fp n)
    (hγ_lt_one : gamma fp n < 1)
    (hT : higham9_2_RectDoolittleRoundedStageTrace
      (Nat.le_refl n) A L_hat U_hat fp)
    (hM : IsMMatrix n A)
    (hLU : LUFactSpec n A L_hat U_hat)
    (hdetA : Matrix.det (Matrix.of A : Matrix (Fin n) (Fin n) ℝ) ≠ 0)
    (hL_nn : ∀ i k : Fin n, 0 ≤ L_hat i k)
    (hU_nn : ∀ k j : Fin n, 0 ≤ U_hat k j)
    (hU_budget_le : ∀ k j : Fin n, k.val ≤ j.val →
      higham9_2_rectDoolittleUAbsBudget fp (Nat.le_refl n)
          A L_hat U_hat k j ≤ gamma fp n * |U_hat k j|)
    (hL_budget_le : ∀ i k : Fin n, k.val < i.val →
      higham9_2_rectDoolittleLAbsBudget fp A L_hat U_hat i k ≤
        gamma fp n * |L_hat i k * U_hat k k|) :
    let y_hat := fl_forwardSub fp n L_hat b
    let x_hat := fl_backSub fp n U_hat y_hat
    ∃ DeltaA : Fin n → Fin n → ℝ,
      (∀ i j, |DeltaA i j| ≤
        higham9_14_h (gamma fp n) * |A i j|) ∧
      (∀ i, ∑ j : Fin n, (A i j + DeltaA i j) * x_hat j = b i) :=
  higham9_14_mmatrix_lu_source_h_bound_of_RectDoolittleRoundedStageTrace_square_fl_triangular_solves_gamma_le
    fp n A L_hat U_hat b (gamma fp n) (gamma_nonneg fp hn) hγ_lt_one
    hn hT hM hLU hdetA hL_nn hU_nn hU_budget_le hL_budget_le le_rfl

/-- **Theorem 9.14**, Matrix-facing M-matrix rounded-stage source `f(u)`
bound. -/
theorem higham9_14_matrix_mmatrix_lu_source_f_bound_of_RectDoolittleRoundedStageTrace_square_fl_triangular_solves_gamma_le
    (fp : FPModel) (n : ℕ)
    (A L_hat U_hat : Matrix (Fin n) (Fin n) ℝ)
    (b : Fin n → ℝ)
    (u : ℝ) (hu : 0 ≤ u)
    (hn : gammaValid fp n)
    (hT : higham9_2_RectDoolittleRoundedStageTrace
      (Nat.le_refl n) A L_hat U_hat fp)
    (hM : IsMMatrix n A)
    (hLU : LUFactSpec n A L_hat U_hat)
    (hdetA : Matrix.det A ≠ 0)
    (hL_nn : ∀ i k : Fin n, 0 ≤ L_hat i k)
    (hU_nn : ∀ k j : Fin n, 0 ≤ U_hat k j)
    (hU_budget_le : ∀ k j : Fin n, k.val ≤ j.val →
      higham9_2_rectDoolittleUAbsBudget fp (Nat.le_refl n)
          A L_hat U_hat k j ≤ gamma fp n * |U_hat k j|)
    (hL_budget_le : ∀ i k : Fin n, k.val < i.val →
      higham9_2_rectDoolittleLAbsBudget fp A L_hat U_hat i k ≤
        gamma fp n * |L_hat i k * U_hat k k|)
    (hγ_le_u : gamma fp n ≤ u) :
    let y_hat := fl_forwardSub fp n L_hat b
    let x_hat := fl_backSub fp n U_hat y_hat
    ∃ DeltaA : Matrix (Fin n) (Fin n) ℝ,
      (∀ i j, |DeltaA i j| ≤ higham9_14_f u * |A i j|) ∧
      Matrix.mulVec (fun i j => A i j + DeltaA i j) x_hat = b :=
  higham9_14_matrix_source_f_bound_of_RectDoolittleRoundedStageTrace_square_fl_triangular_solves_absLU_le_absA_gamma_le
    fp n A L_hat U_hat b u hu hn hT
    (hLU.det_ne_zero_iff_U_diag_ne_zero.mp hdetA)
    hU_budget_le hL_budget_le hγ_le_u
    (fun i j =>
      le_of_eq
        (higham9_12_mmatrix_lu_optimal_growth n A L_hat U_hat
          hM hLU hL_nn hU_nn i j))

/-- **Theorem 9.14**, Matrix-facing M-matrix rounded-stage final `h(u)`
bound. -/
theorem higham9_14_matrix_mmatrix_lu_source_h_bound_of_RectDoolittleRoundedStageTrace_square_fl_triangular_solves_gamma_le
    (fp : FPModel) (n : ℕ)
    (A L_hat U_hat : Matrix (Fin n) (Fin n) ℝ)
    (b : Fin n → ℝ)
    (u : ℝ) (hu : 0 ≤ u) (hu_lt_one : u < 1)
    (hn : gammaValid fp n)
    (hT : higham9_2_RectDoolittleRoundedStageTrace
      (Nat.le_refl n) A L_hat U_hat fp)
    (hM : IsMMatrix n A)
    (hLU : LUFactSpec n A L_hat U_hat)
    (hdetA : Matrix.det A ≠ 0)
    (hL_nn : ∀ i k : Fin n, 0 ≤ L_hat i k)
    (hU_nn : ∀ k j : Fin n, 0 ≤ U_hat k j)
    (hU_budget_le : ∀ k j : Fin n, k.val ≤ j.val →
      higham9_2_rectDoolittleUAbsBudget fp (Nat.le_refl n)
          A L_hat U_hat k j ≤ gamma fp n * |U_hat k j|)
    (hL_budget_le : ∀ i k : Fin n, k.val < i.val →
      higham9_2_rectDoolittleLAbsBudget fp A L_hat U_hat i k ≤
        gamma fp n * |L_hat i k * U_hat k k|)
    (hγ_le_u : gamma fp n ≤ u) :
    let y_hat := fl_forwardSub fp n L_hat b
    let x_hat := fl_backSub fp n U_hat y_hat
    ∃ DeltaA : Matrix (Fin n) (Fin n) ℝ,
      (∀ i j, |DeltaA i j| ≤ higham9_14_h u * |A i j|) ∧
      Matrix.mulVec (fun i j => A i j + DeltaA i j) x_hat = b :=
  higham9_14_matrix_source_h_bound_of_RectDoolittleRoundedStageTrace_square_fl_triangular_solves_absLU_le_absA_gamma_le
    fp n A L_hat U_hat b u hu hu_lt_one hn hT
    (hLU.det_ne_zero_iff_U_diag_ne_zero.mp hdetA)
    hU_budget_le hL_budget_le hγ_le_u
    (fun i j =>
      le_of_eq
        (higham9_12_mmatrix_lu_optimal_growth n A L_hat U_hat
          hM hLU hL_nn hU_nn i j))

/-- **Theorem 9.14**, Matrix-facing M-matrix rounded-stage source `f(γ_n)`
bound. -/
theorem higham9_14_matrix_mmatrix_lu_source_f_bound_of_RectDoolittleRoundedStageTrace_square_fl_triangular_solves_gamma
    (fp : FPModel) (n : ℕ)
    (A L_hat U_hat : Matrix (Fin n) (Fin n) ℝ)
    (b : Fin n → ℝ)
    (hn : gammaValid fp n)
    (hT : higham9_2_RectDoolittleRoundedStageTrace
      (Nat.le_refl n) A L_hat U_hat fp)
    (hM : IsMMatrix n A)
    (hLU : LUFactSpec n A L_hat U_hat)
    (hdetA : Matrix.det A ≠ 0)
    (hL_nn : ∀ i k : Fin n, 0 ≤ L_hat i k)
    (hU_nn : ∀ k j : Fin n, 0 ≤ U_hat k j)
    (hU_budget_le : ∀ k j : Fin n, k.val ≤ j.val →
      higham9_2_rectDoolittleUAbsBudget fp (Nat.le_refl n)
          A L_hat U_hat k j ≤ gamma fp n * |U_hat k j|)
    (hL_budget_le : ∀ i k : Fin n, k.val < i.val →
      higham9_2_rectDoolittleLAbsBudget fp A L_hat U_hat i k ≤
        gamma fp n * |L_hat i k * U_hat k k|) :
    let y_hat := fl_forwardSub fp n L_hat b
    let x_hat := fl_backSub fp n U_hat y_hat
    ∃ DeltaA : Matrix (Fin n) (Fin n) ℝ,
      (∀ i j, |DeltaA i j| ≤
        higham9_14_f (gamma fp n) * |A i j|) ∧
      Matrix.mulVec (fun i j => A i j + DeltaA i j) x_hat = b :=
  higham9_14_matrix_mmatrix_lu_source_f_bound_of_RectDoolittleRoundedStageTrace_square_fl_triangular_solves_gamma_le
    fp n A L_hat U_hat b (gamma fp n) (gamma_nonneg fp hn) hn hT
    hM hLU hdetA hL_nn hU_nn hU_budget_le hL_budget_le le_rfl

/-- **Theorem 9.14**, Matrix-facing M-matrix rounded-stage final `h(γ_n)`
bound. -/
theorem higham9_14_matrix_mmatrix_lu_source_h_bound_of_RectDoolittleRoundedStageTrace_square_fl_triangular_solves_gamma
    (fp : FPModel) (n : ℕ)
    (A L_hat U_hat : Matrix (Fin n) (Fin n) ℝ)
    (b : Fin n → ℝ)
    (hn : gammaValid fp n)
    (hγ_lt_one : gamma fp n < 1)
    (hT : higham9_2_RectDoolittleRoundedStageTrace
      (Nat.le_refl n) A L_hat U_hat fp)
    (hM : IsMMatrix n A)
    (hLU : LUFactSpec n A L_hat U_hat)
    (hdetA : Matrix.det A ≠ 0)
    (hL_nn : ∀ i k : Fin n, 0 ≤ L_hat i k)
    (hU_nn : ∀ k j : Fin n, 0 ≤ U_hat k j)
    (hU_budget_le : ∀ k j : Fin n, k.val ≤ j.val →
      higham9_2_rectDoolittleUAbsBudget fp (Nat.le_refl n)
          A L_hat U_hat k j ≤ gamma fp n * |U_hat k j|)
    (hL_budget_le : ∀ i k : Fin n, k.val < i.val →
      higham9_2_rectDoolittleLAbsBudget fp A L_hat U_hat i k ≤
        gamma fp n * |L_hat i k * U_hat k k|) :
    let y_hat := fl_forwardSub fp n L_hat b
    let x_hat := fl_backSub fp n U_hat y_hat
    ∃ DeltaA : Matrix (Fin n) (Fin n) ℝ,
      (∀ i j, |DeltaA i j| ≤
        higham9_14_h (gamma fp n) * |A i j|) ∧
      Matrix.mulVec (fun i j => A i j + DeltaA i j) x_hat = b :=
  higham9_14_matrix_mmatrix_lu_source_h_bound_of_RectDoolittleRoundedStageTrace_square_fl_triangular_solves_gamma_le
    fp n A L_hat U_hat b (gamma fp n) (gamma_nonneg fp hn) hγ_lt_one
    hn hT hM hLU hdetA hL_nn hU_nn hU_budget_le hL_budget_le le_rfl

/-- **Theorem 9.14**, source-predicate sign-equivalent rounded-stage
`f(u)` bound. -/
theorem higham9_14_sign_equiv_source_f_bound_of_IsSignEquiv_RectDoolittleRoundedStageTrace_square_fl_triangular_solves_gamma_le
    (fp : FPModel) (n : ℕ)
    (A B L_B U_B L_hat U_hat : Fin n → Fin n → ℝ)
    (b : Fin n → ℝ)
    (u : ℝ) (hu : 0 ≤ u)
    (hn : gammaValid fp n)
    (hT : higham9_2_RectDoolittleRoundedStageTrace
      (Nat.le_refl n) A L_hat U_hat fp)
    (hAB : IsSignEquiv n A B)
    (hB_growth : ∀ i j : Fin n,
      ∑ k : Fin n, |L_B i k| * |U_B k j| = |B i j|)
    (hL_abs : ∀ i k : Fin n, |L_hat i k| = |L_B i k|)
    (hU_abs : ∀ k j : Fin n, |U_hat k j| = |U_B k j|)
    (hLU : LUFactSpec n A L_hat U_hat)
    (hdetA : Matrix.det (Matrix.of A : Matrix (Fin n) (Fin n) ℝ) ≠ 0)
    (hU_budget_le : ∀ k j : Fin n, k.val ≤ j.val →
      higham9_2_rectDoolittleUAbsBudget fp (Nat.le_refl n)
          A L_hat U_hat k j ≤ gamma fp n * |U_hat k j|)
    (hL_budget_le : ∀ i k : Fin n, k.val < i.val →
      higham9_2_rectDoolittleLAbsBudget fp A L_hat U_hat i k ≤
        gamma fp n * |L_hat i k * U_hat k k|)
    (hγ_le_u : gamma fp n ≤ u) :
    let y_hat := fl_forwardSub fp n L_hat b
    let x_hat := fl_backSub fp n U_hat y_hat
    ∃ DeltaA : Fin n → Fin n → ℝ,
      (∀ i j, |DeltaA i j| ≤ higham9_14_f u * |A i j|) ∧
      (∀ i, ∑ j : Fin n, (A i j + DeltaA i j) * x_hat j = b i) := by
  simpa [one_mul] using
    (higham9_14_source_f_bound_of_RectDoolittleRoundedStageTrace_square_fl_triangular_solves_gamma_le
      fp n A L_hat U_hat b 1 u hu hn hT
      (hLU.det_ne_zero_iff_U_diag_ne_zero.mp hdetA)
      hU_budget_le hL_budget_le hγ_le_u
      (fun i j => by
        simpa [one_mul] using
          le_of_eq
            (higham9_12_sign_equiv_optimal_growth_of_IsSignEquiv
              n A B L_B U_B L_hat U_hat hAB hB_growth
              hL_abs hU_abs i j)))

/-- **Theorem 9.14**, source-predicate sign-equivalent rounded-stage final
`h(u)` bound. -/
theorem higham9_14_sign_equiv_source_h_bound_of_IsSignEquiv_RectDoolittleRoundedStageTrace_square_fl_triangular_solves_gamma_le
    (fp : FPModel) (n : ℕ)
    (A B L_B U_B L_hat U_hat : Fin n → Fin n → ℝ)
    (b : Fin n → ℝ)
    (u : ℝ) (hu : 0 ≤ u) (hu_lt_one : u < 1)
    (hn : gammaValid fp n)
    (hT : higham9_2_RectDoolittleRoundedStageTrace
      (Nat.le_refl n) A L_hat U_hat fp)
    (hAB : IsSignEquiv n A B)
    (hB_growth : ∀ i j : Fin n,
      ∑ k : Fin n, |L_B i k| * |U_B k j| = |B i j|)
    (hL_abs : ∀ i k : Fin n, |L_hat i k| = |L_B i k|)
    (hU_abs : ∀ k j : Fin n, |U_hat k j| = |U_B k j|)
    (hLU : LUFactSpec n A L_hat U_hat)
    (hdetA : Matrix.det (Matrix.of A : Matrix (Fin n) (Fin n) ℝ) ≠ 0)
    (hU_budget_le : ∀ k j : Fin n, k.val ≤ j.val →
      higham9_2_rectDoolittleUAbsBudget fp (Nat.le_refl n)
          A L_hat U_hat k j ≤ gamma fp n * |U_hat k j|)
    (hL_budget_le : ∀ i k : Fin n, k.val < i.val →
      higham9_2_rectDoolittleLAbsBudget fp A L_hat U_hat i k ≤
        gamma fp n * |L_hat i k * U_hat k k|)
    (hγ_le_u : gamma fp n ≤ u) :
    let y_hat := fl_forwardSub fp n L_hat b
    let x_hat := fl_backSub fp n U_hat y_hat
    ∃ DeltaA : Fin n → Fin n → ℝ,
      (∀ i j, |DeltaA i j| ≤ higham9_14_h u * |A i j|) ∧
      (∀ i, ∑ j : Fin n, (A i j + DeltaA i j) * x_hat j = b i) :=
  higham9_14_source_h_bound_of_RectDoolittleRoundedStageTrace_square_fl_triangular_solves_gamma_le
    fp n A L_hat U_hat b u hu hu_lt_one hn hT
    (hLU.det_ne_zero_iff_U_diag_ne_zero.mp hdetA)
    hU_budget_le hL_budget_le hγ_le_u
    (fun i j => by
      exact le_of_eq
        (higham9_12_sign_equiv_optimal_growth_of_IsSignEquiv
          n A B L_B U_B L_hat U_hat hAB hB_growth
          hL_abs hU_abs i j))

/-- **Theorem 9.14**, source-predicate sign-equivalent rounded-stage
`f(γ_n)` bound. -/
theorem higham9_14_sign_equiv_source_f_bound_of_IsSignEquiv_RectDoolittleRoundedStageTrace_square_fl_triangular_solves_gamma
    (fp : FPModel) (n : ℕ)
    (A B L_B U_B L_hat U_hat : Fin n → Fin n → ℝ)
    (b : Fin n → ℝ)
    (hn : gammaValid fp n)
    (hT : higham9_2_RectDoolittleRoundedStageTrace
      (Nat.le_refl n) A L_hat U_hat fp)
    (hAB : IsSignEquiv n A B)
    (hB_growth : ∀ i j : Fin n,
      ∑ k : Fin n, |L_B i k| * |U_B k j| = |B i j|)
    (hL_abs : ∀ i k : Fin n, |L_hat i k| = |L_B i k|)
    (hU_abs : ∀ k j : Fin n, |U_hat k j| = |U_B k j|)
    (hLU : LUFactSpec n A L_hat U_hat)
    (hdetA : Matrix.det (Matrix.of A : Matrix (Fin n) (Fin n) ℝ) ≠ 0)
    (hU_budget_le : ∀ k j : Fin n, k.val ≤ j.val →
      higham9_2_rectDoolittleUAbsBudget fp (Nat.le_refl n)
          A L_hat U_hat k j ≤ gamma fp n * |U_hat k j|)
    (hL_budget_le : ∀ i k : Fin n, k.val < i.val →
      higham9_2_rectDoolittleLAbsBudget fp A L_hat U_hat i k ≤
        gamma fp n * |L_hat i k * U_hat k k|) :
    let y_hat := fl_forwardSub fp n L_hat b
    let x_hat := fl_backSub fp n U_hat y_hat
    ∃ DeltaA : Fin n → Fin n → ℝ,
      (∀ i j, |DeltaA i j| ≤
        higham9_14_f (gamma fp n) * |A i j|) ∧
      (∀ i, ∑ j : Fin n, (A i j + DeltaA i j) * x_hat j = b i) :=
  higham9_14_sign_equiv_source_f_bound_of_IsSignEquiv_RectDoolittleRoundedStageTrace_square_fl_triangular_solves_gamma_le
    fp n A B L_B U_B L_hat U_hat b (gamma fp n)
    (gamma_nonneg fp hn) hn hT hAB hB_growth hL_abs hU_abs
    hLU hdetA hU_budget_le hL_budget_le le_rfl

/-- **Theorem 9.14**, source-predicate sign-equivalent rounded-stage final
`h(γ_n)` bound. -/
theorem higham9_14_sign_equiv_source_h_bound_of_IsSignEquiv_RectDoolittleRoundedStageTrace_square_fl_triangular_solves_gamma
    (fp : FPModel) (n : ℕ)
    (A B L_B U_B L_hat U_hat : Fin n → Fin n → ℝ)
    (b : Fin n → ℝ)
    (hn : gammaValid fp n)
    (hγ_lt_one : gamma fp n < 1)
    (hT : higham9_2_RectDoolittleRoundedStageTrace
      (Nat.le_refl n) A L_hat U_hat fp)
    (hAB : IsSignEquiv n A B)
    (hB_growth : ∀ i j : Fin n,
      ∑ k : Fin n, |L_B i k| * |U_B k j| = |B i j|)
    (hL_abs : ∀ i k : Fin n, |L_hat i k| = |L_B i k|)
    (hU_abs : ∀ k j : Fin n, |U_hat k j| = |U_B k j|)
    (hLU : LUFactSpec n A L_hat U_hat)
    (hdetA : Matrix.det (Matrix.of A : Matrix (Fin n) (Fin n) ℝ) ≠ 0)
    (hU_budget_le : ∀ k j : Fin n, k.val ≤ j.val →
      higham9_2_rectDoolittleUAbsBudget fp (Nat.le_refl n)
          A L_hat U_hat k j ≤ gamma fp n * |U_hat k j|)
    (hL_budget_le : ∀ i k : Fin n, k.val < i.val →
      higham9_2_rectDoolittleLAbsBudget fp A L_hat U_hat i k ≤
        gamma fp n * |L_hat i k * U_hat k k|) :
    let y_hat := fl_forwardSub fp n L_hat b
    let x_hat := fl_backSub fp n U_hat y_hat
    ∃ DeltaA : Fin n → Fin n → ℝ,
      (∀ i j, |DeltaA i j| ≤
        higham9_14_h (gamma fp n) * |A i j|) ∧
      (∀ i, ∑ j : Fin n, (A i j + DeltaA i j) * x_hat j = b i) :=
  higham9_14_sign_equiv_source_h_bound_of_IsSignEquiv_RectDoolittleRoundedStageTrace_square_fl_triangular_solves_gamma_le
    fp n A B L_B U_B L_hat U_hat b (gamma fp n)
    (gamma_nonneg fp hn) hγ_lt_one hn hT hAB hB_growth hL_abs hU_abs
    hLU hdetA hU_budget_le hL_budget_le le_rfl

/-- **Theorem 9.14**, Matrix-facing sign-equivalent rounded-stage source
`f(u)` bound. -/
theorem higham9_14_matrix_sign_equiv_source_f_bound_of_IsSignEquiv_RectDoolittleRoundedStageTrace_square_fl_triangular_solves_gamma_le
    (fp : FPModel) (n : ℕ)
    (A B L_B U_B L_hat U_hat : Matrix (Fin n) (Fin n) ℝ)
    (b : Fin n → ℝ)
    (u : ℝ) (hu : 0 ≤ u)
    (hn : gammaValid fp n)
    (hT : higham9_2_RectDoolittleRoundedStageTrace
      (Nat.le_refl n) A L_hat U_hat fp)
    (hAB : IsSignEquiv n A B)
    (hB_growth : ∀ i j : Fin n,
      ∑ k : Fin n, |L_B i k| * |U_B k j| = |B i j|)
    (hL_abs : ∀ i k : Fin n, |L_hat i k| = |L_B i k|)
    (hU_abs : ∀ k j : Fin n, |U_hat k j| = |U_B k j|)
    (hLU : LUFactSpec n A L_hat U_hat)
    (hdetA : Matrix.det A ≠ 0)
    (hU_budget_le : ∀ k j : Fin n, k.val ≤ j.val →
      higham9_2_rectDoolittleUAbsBudget fp (Nat.le_refl n)
          A L_hat U_hat k j ≤ gamma fp n * |U_hat k j|)
    (hL_budget_le : ∀ i k : Fin n, k.val < i.val →
      higham9_2_rectDoolittleLAbsBudget fp A L_hat U_hat i k ≤
        gamma fp n * |L_hat i k * U_hat k k|)
    (hγ_le_u : gamma fp n ≤ u) :
    let y_hat := fl_forwardSub fp n L_hat b
    let x_hat := fl_backSub fp n U_hat y_hat
    ∃ DeltaA : Matrix (Fin n) (Fin n) ℝ,
      (∀ i j, |DeltaA i j| ≤ higham9_14_f u * |A i j|) ∧
      Matrix.mulVec (fun i j => A i j + DeltaA i j) x_hat = b :=
  higham9_14_matrix_source_f_bound_of_RectDoolittleRoundedStageTrace_square_fl_triangular_solves_absLU_le_absA_gamma_le
    fp n A L_hat U_hat b u hu hn hT
    (hLU.det_ne_zero_iff_U_diag_ne_zero.mp hdetA)
    hU_budget_le hL_budget_le hγ_le_u
    (fun i j =>
      le_of_eq
        (higham9_12_sign_equiv_optimal_growth_of_IsSignEquiv
          n A B L_B U_B L_hat U_hat hAB hB_growth hL_abs hU_abs i j))

/-- **Theorem 9.14**, Matrix-facing sign-equivalent rounded-stage final
`h(u)` bound. -/
theorem higham9_14_matrix_sign_equiv_source_h_bound_of_IsSignEquiv_RectDoolittleRoundedStageTrace_square_fl_triangular_solves_gamma_le
    (fp : FPModel) (n : ℕ)
    (A B L_B U_B L_hat U_hat : Matrix (Fin n) (Fin n) ℝ)
    (b : Fin n → ℝ)
    (u : ℝ) (hu : 0 ≤ u) (hu_lt_one : u < 1)
    (hn : gammaValid fp n)
    (hT : higham9_2_RectDoolittleRoundedStageTrace
      (Nat.le_refl n) A L_hat U_hat fp)
    (hAB : IsSignEquiv n A B)
    (hB_growth : ∀ i j : Fin n,
      ∑ k : Fin n, |L_B i k| * |U_B k j| = |B i j|)
    (hL_abs : ∀ i k : Fin n, |L_hat i k| = |L_B i k|)
    (hU_abs : ∀ k j : Fin n, |U_hat k j| = |U_B k j|)
    (hLU : LUFactSpec n A L_hat U_hat)
    (hdetA : Matrix.det A ≠ 0)
    (hU_budget_le : ∀ k j : Fin n, k.val ≤ j.val →
      higham9_2_rectDoolittleUAbsBudget fp (Nat.le_refl n)
          A L_hat U_hat k j ≤ gamma fp n * |U_hat k j|)
    (hL_budget_le : ∀ i k : Fin n, k.val < i.val →
      higham9_2_rectDoolittleLAbsBudget fp A L_hat U_hat i k ≤
        gamma fp n * |L_hat i k * U_hat k k|)
    (hγ_le_u : gamma fp n ≤ u) :
    let y_hat := fl_forwardSub fp n L_hat b
    let x_hat := fl_backSub fp n U_hat y_hat
    ∃ DeltaA : Matrix (Fin n) (Fin n) ℝ,
      (∀ i j, |DeltaA i j| ≤ higham9_14_h u * |A i j|) ∧
      Matrix.mulVec (fun i j => A i j + DeltaA i j) x_hat = b :=
  higham9_14_matrix_source_h_bound_of_RectDoolittleRoundedStageTrace_square_fl_triangular_solves_absLU_le_absA_gamma_le
    fp n A L_hat U_hat b u hu hu_lt_one hn hT
    (hLU.det_ne_zero_iff_U_diag_ne_zero.mp hdetA)
    hU_budget_le hL_budget_le hγ_le_u
    (fun i j =>
      le_of_eq
        (higham9_12_sign_equiv_optimal_growth_of_IsSignEquiv
          n A B L_B U_B L_hat U_hat hAB hB_growth hL_abs hU_abs i j))

/-- **Theorem 9.14**, Matrix-facing sign-equivalent rounded-stage source
`f(γ_n)` bound. -/
theorem higham9_14_matrix_sign_equiv_source_f_bound_of_IsSignEquiv_RectDoolittleRoundedStageTrace_square_fl_triangular_solves_gamma
    (fp : FPModel) (n : ℕ)
    (A B L_B U_B L_hat U_hat : Matrix (Fin n) (Fin n) ℝ)
    (b : Fin n → ℝ)
    (hn : gammaValid fp n)
    (hT : higham9_2_RectDoolittleRoundedStageTrace
      (Nat.le_refl n) A L_hat U_hat fp)
    (hAB : IsSignEquiv n A B)
    (hB_growth : ∀ i j : Fin n,
      ∑ k : Fin n, |L_B i k| * |U_B k j| = |B i j|)
    (hL_abs : ∀ i k : Fin n, |L_hat i k| = |L_B i k|)
    (hU_abs : ∀ k j : Fin n, |U_hat k j| = |U_B k j|)
    (hLU : LUFactSpec n A L_hat U_hat)
    (hdetA : Matrix.det A ≠ 0)
    (hU_budget_le : ∀ k j : Fin n, k.val ≤ j.val →
      higham9_2_rectDoolittleUAbsBudget fp (Nat.le_refl n)
          A L_hat U_hat k j ≤ gamma fp n * |U_hat k j|)
    (hL_budget_le : ∀ i k : Fin n, k.val < i.val →
      higham9_2_rectDoolittleLAbsBudget fp A L_hat U_hat i k ≤
        gamma fp n * |L_hat i k * U_hat k k|) :
    let y_hat := fl_forwardSub fp n L_hat b
    let x_hat := fl_backSub fp n U_hat y_hat
    ∃ DeltaA : Matrix (Fin n) (Fin n) ℝ,
      (∀ i j, |DeltaA i j| ≤
        higham9_14_f (gamma fp n) * |A i j|) ∧
      Matrix.mulVec (fun i j => A i j + DeltaA i j) x_hat = b :=
  higham9_14_matrix_sign_equiv_source_f_bound_of_IsSignEquiv_RectDoolittleRoundedStageTrace_square_fl_triangular_solves_gamma_le
    fp n A B L_B U_B L_hat U_hat b (gamma fp n)
    (gamma_nonneg fp hn) hn hT hAB hB_growth hL_abs hU_abs
    hLU hdetA hU_budget_le hL_budget_le le_rfl

/-- **Theorem 9.14**, Matrix-facing sign-equivalent rounded-stage final
`h(γ_n)` bound. -/
theorem higham9_14_matrix_sign_equiv_source_h_bound_of_IsSignEquiv_RectDoolittleRoundedStageTrace_square_fl_triangular_solves_gamma
    (fp : FPModel) (n : ℕ)
    (A B L_B U_B L_hat U_hat : Matrix (Fin n) (Fin n) ℝ)
    (b : Fin n → ℝ)
    (hn : gammaValid fp n)
    (hγ_lt_one : gamma fp n < 1)
    (hT : higham9_2_RectDoolittleRoundedStageTrace
      (Nat.le_refl n) A L_hat U_hat fp)
    (hAB : IsSignEquiv n A B)
    (hB_growth : ∀ i j : Fin n,
      ∑ k : Fin n, |L_B i k| * |U_B k j| = |B i j|)
    (hL_abs : ∀ i k : Fin n, |L_hat i k| = |L_B i k|)
    (hU_abs : ∀ k j : Fin n, |U_hat k j| = |U_B k j|)
    (hLU : LUFactSpec n A L_hat U_hat)
    (hdetA : Matrix.det A ≠ 0)
    (hU_budget_le : ∀ k j : Fin n, k.val ≤ j.val →
      higham9_2_rectDoolittleUAbsBudget fp (Nat.le_refl n)
          A L_hat U_hat k j ≤ gamma fp n * |U_hat k j|)
    (hL_budget_le : ∀ i k : Fin n, k.val < i.val →
      higham9_2_rectDoolittleLAbsBudget fp A L_hat U_hat i k ≤
        gamma fp n * |L_hat i k * U_hat k k|) :
    let y_hat := fl_forwardSub fp n L_hat b
    let x_hat := fl_backSub fp n U_hat y_hat
    ∃ DeltaA : Matrix (Fin n) (Fin n) ℝ,
      (∀ i j, |DeltaA i j| ≤
        higham9_14_h (gamma fp n) * |A i j|) ∧
      Matrix.mulVec (fun i j => A i j + DeltaA i j) x_hat = b :=
  higham9_14_matrix_sign_equiv_source_h_bound_of_IsSignEquiv_RectDoolittleRoundedStageTrace_square_fl_triangular_solves_gamma_le
    fp n A B L_B U_B L_hat U_hat b (gamma fp n)
    (gamma_nonneg fp hn) hγ_lt_one hn hT hAB hB_growth hL_abs hU_abs
    hLU hdetA hU_budget_le hL_budget_le le_rfl

/-- **Theorem 9.14**, nonnegative-LU rounded-stage model-consuming
`f(γ_n)` bound.  The rounded-stage trace supplies equation (9.20), while the
caller keeps the explicit triangular-solve equation (9.21) visible. -/
theorem higham9_14_nonnegative_lu_source_f_bound_of_RectDoolittleRoundedStageTrace_square_models_gamma
    (fp : FPModel) (n : ℕ)
    (A L_hat U_hat : Fin n → Fin n → ℝ)
    (y_hat x_hat b : Fin n → ℝ)
    (DeltaL DeltaU : Fin n → Fin n → ℝ)
    (hn : gammaValid fp n)
    (hT : higham9_2_RectDoolittleRoundedStageTrace
      (Nat.le_refl n) A L_hat U_hat fp)
    (hNonneg : HasNonnegLUFactors n A L_hat U_hat)
    (hdetA : Matrix.det (Matrix.of A : Matrix (Fin n) (Fin n) ℝ) ≠ 0)
    (hU_budget_le : ∀ k j : Fin n, k.val ≤ j.val →
      higham9_2_rectDoolittleUAbsBudget fp (Nat.le_refl n)
          A L_hat U_hat k j ≤ gamma fp n * |U_hat k j|)
    (hL_budget_le : ∀ i k : Fin n, k.val < i.val →
      higham9_2_rectDoolittleLAbsBudget fp A L_hat U_hat i k ≤
        gamma fp n * |L_hat i k * U_hat k k|)
    (h21 : higham9_21_tridiag_solve_perturbation_model n L_hat U_hat
      y_hat x_hat b DeltaL DeltaU (gamma fp n)) :
    ∃ DeltaA : Fin n → Fin n → ℝ,
      (∀ i j, |DeltaA i j| ≤
        higham9_14_f (gamma fp n) * |A i j|) ∧
      (∀ i, ∑ j : Fin n, (A i j + DeltaA i j) * x_hat j = b i) := by
  rcases
      higham9_20_tridiag_lu_perturbation_model_of_RectDoolittleRoundedStageTrace_square_gamma
        fp n A L_hat U_hat hn hT
        (hNonneg.1.det_ne_zero_iff_U_diag_ne_zero.mp hdetA)
        hU_budget_le hL_budget_le with
    ⟨DeltaA_LU, h20⟩
  simpa [one_mul] using
    (higham9_14_source_f_bound_of_absLU_le_const_absA_and_9_20_9_21_models
      n A L_hat U_hat y_hat x_hat b 1 (gamma fp n)
      (gamma_nonneg fp hn)
      (fun i j => by
        simpa [one_mul] using
          le_of_eq
            (higham9_12_nonneg_lu_optimal_growth n A L_hat U_hat
              hNonneg i j))
      DeltaA_LU DeltaL DeltaU h20 h21)

/-- **Theorem 9.14**, nonnegative-LU rounded-stage model-consuming final
`h(γ_n)` bound. -/
theorem higham9_14_nonnegative_lu_source_h_bound_of_RectDoolittleRoundedStageTrace_square_models_gamma
    (fp : FPModel) (n : ℕ)
    (A L_hat U_hat : Fin n → Fin n → ℝ)
    (y_hat x_hat b : Fin n → ℝ)
    (DeltaL DeltaU : Fin n → Fin n → ℝ)
    (hn : gammaValid fp n)
    (hγ_lt_one : gamma fp n < 1)
    (hT : higham9_2_RectDoolittleRoundedStageTrace
      (Nat.le_refl n) A L_hat U_hat fp)
    (hNonneg : HasNonnegLUFactors n A L_hat U_hat)
    (hdetA : Matrix.det (Matrix.of A : Matrix (Fin n) (Fin n) ℝ) ≠ 0)
    (hU_budget_le : ∀ k j : Fin n, k.val ≤ j.val →
      higham9_2_rectDoolittleUAbsBudget fp (Nat.le_refl n)
          A L_hat U_hat k j ≤ gamma fp n * |U_hat k j|)
    (hL_budget_le : ∀ i k : Fin n, k.val < i.val →
      higham9_2_rectDoolittleLAbsBudget fp A L_hat U_hat i k ≤
        gamma fp n * |L_hat i k * U_hat k k|)
    (h21 : higham9_21_tridiag_solve_perturbation_model n L_hat U_hat
      y_hat x_hat b DeltaL DeltaU (gamma fp n)) :
    ∃ DeltaA : Fin n → Fin n → ℝ,
      (∀ i j, |DeltaA i j| ≤
        higham9_14_h (gamma fp n) * |A i j|) ∧
      (∀ i, ∑ j : Fin n, (A i j + DeltaA i j) * x_hat j = b i) := by
  rcases
      higham9_20_tridiag_lu_perturbation_model_of_RectDoolittleRoundedStageTrace_square_gamma
        fp n A L_hat U_hat hn hT
        (hNonneg.1.det_ne_zero_iff_U_diag_ne_zero.mp hdetA)
        hU_budget_le hL_budget_le with
    ⟨DeltaA_LU, h20⟩
  simpa [one_mul] using
    (higham9_14_source_h_bound_of_absLU_le_const_absA_and_9_20_9_21_models
      n A L_hat U_hat y_hat x_hat b 1 (gamma fp n)
      (by norm_num) (gamma_nonneg fp hn) hγ_lt_one
      (fun i j => by
        simpa [one_mul] using
          le_of_eq
            (higham9_12_nonneg_lu_optimal_growth n A L_hat U_hat
              hNonneg i j))
      DeltaA_LU DeltaL DeltaU h20 h21)

/-- **Theorem 9.14**, M-matrix LU rounded-stage model-consuming
`f(γ_n)` bound. -/
theorem higham9_14_mmatrix_lu_source_f_bound_of_RectDoolittleRoundedStageTrace_square_models_gamma
    (fp : FPModel) (n : ℕ)
    (A L_hat U_hat : Fin n → Fin n → ℝ)
    (y_hat x_hat b : Fin n → ℝ)
    (DeltaL DeltaU : Fin n → Fin n → ℝ)
    (hn : gammaValid fp n)
    (hT : higham9_2_RectDoolittleRoundedStageTrace
      (Nat.le_refl n) A L_hat U_hat fp)
    (hM : IsMMatrix n A)
    (hLU : LUFactSpec n A L_hat U_hat)
    (hdetA : Matrix.det (Matrix.of A : Matrix (Fin n) (Fin n) ℝ) ≠ 0)
    (hL_nn : ∀ i k : Fin n, 0 ≤ L_hat i k)
    (hU_nn : ∀ k j : Fin n, 0 ≤ U_hat k j)
    (hU_budget_le : ∀ k j : Fin n, k.val ≤ j.val →
      higham9_2_rectDoolittleUAbsBudget fp (Nat.le_refl n)
          A L_hat U_hat k j ≤ gamma fp n * |U_hat k j|)
    (hL_budget_le : ∀ i k : Fin n, k.val < i.val →
      higham9_2_rectDoolittleLAbsBudget fp A L_hat U_hat i k ≤
        gamma fp n * |L_hat i k * U_hat k k|)
    (h21 : higham9_21_tridiag_solve_perturbation_model n L_hat U_hat
      y_hat x_hat b DeltaL DeltaU (gamma fp n)) :
    ∃ DeltaA : Fin n → Fin n → ℝ,
      (∀ i j, |DeltaA i j| ≤
        higham9_14_f (gamma fp n) * |A i j|) ∧
      (∀ i, ∑ j : Fin n, (A i j + DeltaA i j) * x_hat j = b i) := by
  rcases
      higham9_20_tridiag_lu_perturbation_model_of_RectDoolittleRoundedStageTrace_square_gamma
        fp n A L_hat U_hat hn hT
        (hLU.det_ne_zero_iff_U_diag_ne_zero.mp hdetA)
        hU_budget_le hL_budget_le with
    ⟨DeltaA_LU, h20⟩
  simpa [one_mul] using
    (higham9_14_source_f_bound_of_absLU_le_const_absA_and_9_20_9_21_models
      n A L_hat U_hat y_hat x_hat b 1 (gamma fp n)
      (gamma_nonneg fp hn)
      (fun i j => by
        simpa [one_mul] using
          le_of_eq
            (higham9_12_mmatrix_lu_optimal_growth n A L_hat U_hat
              hM hLU hL_nn hU_nn i j))
      DeltaA_LU DeltaL DeltaU h20 h21)

/-- **Theorem 9.14**, M-matrix LU rounded-stage model-consuming final
`h(γ_n)` bound. -/
theorem higham9_14_mmatrix_lu_source_h_bound_of_RectDoolittleRoundedStageTrace_square_models_gamma
    (fp : FPModel) (n : ℕ)
    (A L_hat U_hat : Fin n → Fin n → ℝ)
    (y_hat x_hat b : Fin n → ℝ)
    (DeltaL DeltaU : Fin n → Fin n → ℝ)
    (hn : gammaValid fp n)
    (hγ_lt_one : gamma fp n < 1)
    (hT : higham9_2_RectDoolittleRoundedStageTrace
      (Nat.le_refl n) A L_hat U_hat fp)
    (hM : IsMMatrix n A)
    (hLU : LUFactSpec n A L_hat U_hat)
    (hdetA : Matrix.det (Matrix.of A : Matrix (Fin n) (Fin n) ℝ) ≠ 0)
    (hL_nn : ∀ i k : Fin n, 0 ≤ L_hat i k)
    (hU_nn : ∀ k j : Fin n, 0 ≤ U_hat k j)
    (hU_budget_le : ∀ k j : Fin n, k.val ≤ j.val →
      higham9_2_rectDoolittleUAbsBudget fp (Nat.le_refl n)
          A L_hat U_hat k j ≤ gamma fp n * |U_hat k j|)
    (hL_budget_le : ∀ i k : Fin n, k.val < i.val →
      higham9_2_rectDoolittleLAbsBudget fp A L_hat U_hat i k ≤
        gamma fp n * |L_hat i k * U_hat k k|)
    (h21 : higham9_21_tridiag_solve_perturbation_model n L_hat U_hat
      y_hat x_hat b DeltaL DeltaU (gamma fp n)) :
    ∃ DeltaA : Fin n → Fin n → ℝ,
      (∀ i j, |DeltaA i j| ≤
        higham9_14_h (gamma fp n) * |A i j|) ∧
      (∀ i, ∑ j : Fin n, (A i j + DeltaA i j) * x_hat j = b i) := by
  rcases
      higham9_20_tridiag_lu_perturbation_model_of_RectDoolittleRoundedStageTrace_square_gamma
        fp n A L_hat U_hat hn hT
        (hLU.det_ne_zero_iff_U_diag_ne_zero.mp hdetA)
        hU_budget_le hL_budget_le with
    ⟨DeltaA_LU, h20⟩
  simpa [one_mul] using
    (higham9_14_source_h_bound_of_absLU_le_const_absA_and_9_20_9_21_models
      n A L_hat U_hat y_hat x_hat b 1 (gamma fp n)
      (by norm_num) (gamma_nonneg fp hn) hγ_lt_one
      (fun i j => by
        simpa [one_mul] using
          le_of_eq
            (higham9_12_mmatrix_lu_optimal_growth n A L_hat U_hat
              hM hLU hL_nn hU_nn i j))
      DeltaA_LU DeltaL DeltaU h20 h21)

/-- **Theorem 9.14**, source-predicate sign-equivalent rounded-stage
model-consuming `f(γ_n)` bound. -/
theorem higham9_14_sign_equiv_source_f_bound_of_IsSignEquiv_RectDoolittleRoundedStageTrace_square_models_gamma
    (fp : FPModel) (n : ℕ)
    (A B L_B U_B L_hat U_hat : Fin n → Fin n → ℝ)
    (y_hat x_hat b : Fin n → ℝ)
    (DeltaL DeltaU : Fin n → Fin n → ℝ)
    (hn : gammaValid fp n)
    (hT : higham9_2_RectDoolittleRoundedStageTrace
      (Nat.le_refl n) A L_hat U_hat fp)
    (hAB : IsSignEquiv n A B)
    (hB_growth : ∀ i j : Fin n,
      ∑ k : Fin n, |L_B i k| * |U_B k j| = |B i j|)
    (hL_abs : ∀ i k : Fin n, |L_hat i k| = |L_B i k|)
    (hU_abs : ∀ k j : Fin n, |U_hat k j| = |U_B k j|)
    (hLU : LUFactSpec n A L_hat U_hat)
    (hdetA : Matrix.det (Matrix.of A : Matrix (Fin n) (Fin n) ℝ) ≠ 0)
    (hU_budget_le : ∀ k j : Fin n, k.val ≤ j.val →
      higham9_2_rectDoolittleUAbsBudget fp (Nat.le_refl n)
          A L_hat U_hat k j ≤ gamma fp n * |U_hat k j|)
    (hL_budget_le : ∀ i k : Fin n, k.val < i.val →
      higham9_2_rectDoolittleLAbsBudget fp A L_hat U_hat i k ≤
        gamma fp n * |L_hat i k * U_hat k k|)
    (h21 : higham9_21_tridiag_solve_perturbation_model n L_hat U_hat
      y_hat x_hat b DeltaL DeltaU (gamma fp n)) :
    ∃ DeltaA : Fin n → Fin n → ℝ,
      (∀ i j, |DeltaA i j| ≤
        higham9_14_f (gamma fp n) * |A i j|) ∧
      (∀ i, ∑ j : Fin n, (A i j + DeltaA i j) * x_hat j = b i) := by
  rcases
      higham9_20_tridiag_lu_perturbation_model_of_RectDoolittleRoundedStageTrace_square_gamma
        fp n A L_hat U_hat hn hT
        (hLU.det_ne_zero_iff_U_diag_ne_zero.mp hdetA)
        hU_budget_le hL_budget_le with
    ⟨DeltaA_LU, h20⟩
  simpa [one_mul] using
    (higham9_14_source_f_bound_of_absLU_le_const_absA_and_9_20_9_21_models
      n A L_hat U_hat y_hat x_hat b 1 (gamma fp n)
      (gamma_nonneg fp hn)
      (fun i j => by
        simpa [one_mul] using
          le_of_eq
            (higham9_12_sign_equiv_optimal_growth_of_IsSignEquiv
              n A B L_B U_B L_hat U_hat hAB hB_growth hL_abs hU_abs
              i j))
      DeltaA_LU DeltaL DeltaU h20 h21)

/-- **Theorem 9.14**, source-predicate sign-equivalent rounded-stage
model-consuming final `h(γ_n)` bound. -/
theorem higham9_14_sign_equiv_source_h_bound_of_IsSignEquiv_RectDoolittleRoundedStageTrace_square_models_gamma
    (fp : FPModel) (n : ℕ)
    (A B L_B U_B L_hat U_hat : Fin n → Fin n → ℝ)
    (y_hat x_hat b : Fin n → ℝ)
    (DeltaL DeltaU : Fin n → Fin n → ℝ)
    (hn : gammaValid fp n)
    (hγ_lt_one : gamma fp n < 1)
    (hT : higham9_2_RectDoolittleRoundedStageTrace
      (Nat.le_refl n) A L_hat U_hat fp)
    (hAB : IsSignEquiv n A B)
    (hB_growth : ∀ i j : Fin n,
      ∑ k : Fin n, |L_B i k| * |U_B k j| = |B i j|)
    (hL_abs : ∀ i k : Fin n, |L_hat i k| = |L_B i k|)
    (hU_abs : ∀ k j : Fin n, |U_hat k j| = |U_B k j|)
    (hLU : LUFactSpec n A L_hat U_hat)
    (hdetA : Matrix.det (Matrix.of A : Matrix (Fin n) (Fin n) ℝ) ≠ 0)
    (hU_budget_le : ∀ k j : Fin n, k.val ≤ j.val →
      higham9_2_rectDoolittleUAbsBudget fp (Nat.le_refl n)
          A L_hat U_hat k j ≤ gamma fp n * |U_hat k j|)
    (hL_budget_le : ∀ i k : Fin n, k.val < i.val →
      higham9_2_rectDoolittleLAbsBudget fp A L_hat U_hat i k ≤
        gamma fp n * |L_hat i k * U_hat k k|)
    (h21 : higham9_21_tridiag_solve_perturbation_model n L_hat U_hat
      y_hat x_hat b DeltaL DeltaU (gamma fp n)) :
    ∃ DeltaA : Fin n → Fin n → ℝ,
      (∀ i j, |DeltaA i j| ≤
        higham9_14_h (gamma fp n) * |A i j|) ∧
      (∀ i, ∑ j : Fin n, (A i j + DeltaA i j) * x_hat j = b i) := by
  rcases
      higham9_20_tridiag_lu_perturbation_model_of_RectDoolittleRoundedStageTrace_square_gamma
        fp n A L_hat U_hat hn hT
        (hLU.det_ne_zero_iff_U_diag_ne_zero.mp hdetA)
        hU_budget_le hL_budget_le with
    ⟨DeltaA_LU, h20⟩
  simpa [one_mul] using
    (higham9_14_source_h_bound_of_absLU_le_const_absA_and_9_20_9_21_models
      n A L_hat U_hat y_hat x_hat b 1 (gamma fp n)
      (by norm_num) (gamma_nonneg fp hn) hγ_lt_one
      (fun i j => by
        simpa [one_mul] using
          le_of_eq
            (higham9_12_sign_equiv_optimal_growth_of_IsSignEquiv
              n A B L_B U_B L_hat U_hat hAB hB_growth hL_abs hU_abs
              i j))
      DeltaA_LU DeltaL DeltaU h20 h21)

/-- **Theorem 9.14**, square-specialized rectangular literal exact-target
gap form for the source-facing `f(u)` bound.

This is the direct source entry point from the strongest rectangular literal
Algorithm 9.2 target-gap hypotheses into the existing square-specialized
rectangular Theorem 9.14 source wrapper.  It still assumes the displayed
literal rounded entries and target gaps; it does not construct the missing
executable loop schedule. -/
theorem higham9_14_source_f_bound_of_rectLiteralDoolittle_exactTargetGaps_square_fl_triangular_solves_gamma_le
    (fp : FPModel) (n : ℕ)
    (A L_hat U_hat : Fin n → Fin n → ℝ)
    (b : Fin n → ℝ)
    (c u : ℝ) (hu : 0 ≤ u)
    (hL_diag : ∀ k : Fin n, L_hat (higham9_2_rectRow (Nat.le_refl n) k) k = 1)
    (hL_upper_zero : ∀ i j : Fin n, i.val < j.val → L_hat i j = 0)
    (hU_lower_zero : ∀ i j : Fin n, j.val < i.val → U_hat i j = 0)
    (hU_entry_eq : ∀ k j : Fin n, k.val ≤ j.val →
      U_hat k j =
        higham9_2_rectFlDoolittleUEntry fp (Nat.le_refl n)
          A L_hat U_hat k j)
    (hL_entry_eq : ∀ i k : Fin n, k.val < i.val →
      L_hat i k = higham9_2_rectFlDoolittleLEntry fp A L_hat U_hat i k)
    (hU_diag : ∀ k : Fin n, U_hat k k ≠ 0)
    (hn : gammaValid fp n)
    (hL_coeff : ∀ i k : Fin n, k.val < i.val →
      gamma fp k.val + fp.u + fp.u ≤ gamma fp n)
    (hU_gap : ∀ k j : Fin n, k.val ≤ j.val →
      |A (higham9_2_rectRow (Nat.le_refl n) k) j| + (1 + fp.u) *
          higham9_2_rectDoolittleUProductAbs fp (Nat.le_refl n)
            A L_hat U_hat k j +
        higham9_2_rectDoolittleUExactTargetResidualBudget fp
          (Nat.le_refl n) A L_hat U_hat k j ≤
        |higham9_2_rectDoolittleUExactTarget (Nat.le_refl n)
          A L_hat U_hat k j|)
    (hL_gap : ∀ i k : Fin n, k.val < i.val →
      |A i k| + (1 + fp.u) *
          higham9_2_rectDoolittleLProductAbs fp A L_hat U_hat i k +
        higham9_2_rectDoolittleLExactTargetEntryResidualBudget fp
          A L_hat U_hat i k ≤
        |higham9_2_rectDoolittleLExactTarget A L_hat U_hat i k|)
    (hL_num_gap : ∀ i k : Fin n, k.val < i.val →
      ((|A i k| + higham9_2_rectDoolittleLProductAbs fp A L_hat U_hat i k) +
        higham9_2_rectDoolittleLExactTargetNumeratorResidualBudget
          fp A L_hat U_hat i k) +
        higham9_2_rectDoolittleLExactTargetEntryResidualBudget
          fp A L_hat U_hat i k ≤
        |higham9_2_rectDoolittleLExactTarget A L_hat U_hat i k|)
    (hγ_le_u : gamma fp n ≤ u)
    (hAbsLU_le : ∀ i j : Fin n,
      ∑ k : Fin n, |L_hat i k| * |U_hat k j| ≤ c * |A i j|) :
    let y_hat := fl_forwardSub fp n L_hat b
    let x_hat := fl_backSub fp n U_hat y_hat
    ∃ DeltaA : Fin n → Fin n → ℝ,
      (∀ i j, |DeltaA i j| ≤ c * higham9_14_f u * |A i j|) ∧
      (∀ i, ∑ j : Fin n, (A i j + DeltaA i j) * x_hat j = b i) :=
  higham9_14_source_f_bound_of_RectDoolittleDenseLoopAbsBudgetCertificate_square_fl_triangular_solves_gamma_le
    fp n A L_hat U_hat b
    (higham9_2_rectDoolittleUAbsBudget fp (Nat.le_refl n) A L_hat U_hat)
    (higham9_2_rectDoolittleLAbsBudget fp A L_hat U_hat)
    c u hu hn
    (higham9_2_rectAbsBudgetCertificate_of_literal_doolittle_exact_target_gaps
      (hmn := Nat.le_refl n) (A := A) (L := L_hat) (U := U_hat)
      hL_diag hL_upper_zero hU_lower_zero hU_entry_eq hL_entry_eq
      hU_diag hn hL_coeff hU_gap hL_gap hL_num_gap)
    hγ_le_u hU_diag hAbsLU_le

/-- **Theorem 9.14**, square-specialized rectangular literal exact-target
gap form for the final exact-growth `h(u)` bound. -/
theorem higham9_14_source_h_bound_of_rectLiteralDoolittle_exactTargetGaps_square_fl_triangular_solves_gamma_le
    (fp : FPModel) (n : ℕ)
    (A L_hat U_hat : Fin n → Fin n → ℝ)
    (b : Fin n → ℝ)
    (u : ℝ) (hu : 0 ≤ u) (hu_lt_one : u < 1)
    (hL_diag : ∀ k : Fin n, L_hat (higham9_2_rectRow (Nat.le_refl n) k) k = 1)
    (hL_upper_zero : ∀ i j : Fin n, i.val < j.val → L_hat i j = 0)
    (hU_lower_zero : ∀ i j : Fin n, j.val < i.val → U_hat i j = 0)
    (hU_entry_eq : ∀ k j : Fin n, k.val ≤ j.val →
      U_hat k j =
        higham9_2_rectFlDoolittleUEntry fp (Nat.le_refl n)
          A L_hat U_hat k j)
    (hL_entry_eq : ∀ i k : Fin n, k.val < i.val →
      L_hat i k = higham9_2_rectFlDoolittleLEntry fp A L_hat U_hat i k)
    (hU_diag : ∀ k : Fin n, U_hat k k ≠ 0)
    (hn : gammaValid fp n)
    (hL_coeff : ∀ i k : Fin n, k.val < i.val →
      gamma fp k.val + fp.u + fp.u ≤ gamma fp n)
    (hU_gap : ∀ k j : Fin n, k.val ≤ j.val →
      |A (higham9_2_rectRow (Nat.le_refl n) k) j| + (1 + fp.u) *
          higham9_2_rectDoolittleUProductAbs fp (Nat.le_refl n)
            A L_hat U_hat k j +
        higham9_2_rectDoolittleUExactTargetResidualBudget fp
          (Nat.le_refl n) A L_hat U_hat k j ≤
        |higham9_2_rectDoolittleUExactTarget (Nat.le_refl n)
          A L_hat U_hat k j|)
    (hL_gap : ∀ i k : Fin n, k.val < i.val →
      |A i k| + (1 + fp.u) *
          higham9_2_rectDoolittleLProductAbs fp A L_hat U_hat i k +
        higham9_2_rectDoolittleLExactTargetEntryResidualBudget fp
          A L_hat U_hat i k ≤
        |higham9_2_rectDoolittleLExactTarget A L_hat U_hat i k|)
    (hL_num_gap : ∀ i k : Fin n, k.val < i.val →
      ((|A i k| + higham9_2_rectDoolittleLProductAbs fp A L_hat U_hat i k) +
        higham9_2_rectDoolittleLExactTargetNumeratorResidualBudget
          fp A L_hat U_hat i k) +
        higham9_2_rectDoolittleLExactTargetEntryResidualBudget
          fp A L_hat U_hat i k ≤
        |higham9_2_rectDoolittleLExactTarget A L_hat U_hat i k|)
    (hγ_le_u : gamma fp n ≤ u)
    (hAbsLU_le : ∀ i j : Fin n,
      ∑ k : Fin n, |L_hat i k| * |U_hat k j| ≤ |A i j|) :
    let y_hat := fl_forwardSub fp n L_hat b
    let x_hat := fl_backSub fp n U_hat y_hat
    ∃ DeltaA : Fin n → Fin n → ℝ,
      (∀ i j, |DeltaA i j| ≤ higham9_14_h u * |A i j|) ∧
      (∀ i, ∑ j : Fin n, (A i j + DeltaA i j) * x_hat j = b i) :=
  higham9_14_source_h_bound_of_RectDoolittleDenseLoopAbsBudgetCertificate_square_fl_triangular_solves_gamma_le
    fp n A L_hat U_hat b
    (higham9_2_rectDoolittleUAbsBudget fp (Nat.le_refl n) A L_hat U_hat)
    (higham9_2_rectDoolittleLAbsBudget fp A L_hat U_hat)
    u hu hu_lt_one hn
    (higham9_2_rectAbsBudgetCertificate_of_literal_doolittle_exact_target_gaps
      (hmn := Nat.le_refl n) (A := A) (L := L_hat) (U := U_hat)
      hL_diag hL_upper_zero hU_lower_zero hU_entry_eq hL_entry_eq
      hU_diag hn hL_coeff hU_gap hL_gap hL_num_gap)
    hγ_le_u hU_diag hAbsLU_le

/-- **Theorem 9.14**, square-specialized rectangular literal exact-target
gap form for the final constant-growth `h(u)` bound. -/
theorem higham9_14_source_h_bound_of_rectLiteralDoolittle_exactTargetGaps_square_fl_triangular_solves_const_gamma_le
    (fp : FPModel) (n : ℕ)
    (A L_hat U_hat : Fin n → Fin n → ℝ)
    (b : Fin n → ℝ)
    (c u : ℝ) (hc : 0 ≤ c) (hu : 0 ≤ u) (hu_lt_one : u < 1)
    (hL_diag : ∀ k : Fin n, L_hat (higham9_2_rectRow (Nat.le_refl n) k) k = 1)
    (hL_upper_zero : ∀ i j : Fin n, i.val < j.val → L_hat i j = 0)
    (hU_lower_zero : ∀ i j : Fin n, j.val < i.val → U_hat i j = 0)
    (hU_entry_eq : ∀ k j : Fin n, k.val ≤ j.val →
      U_hat k j =
        higham9_2_rectFlDoolittleUEntry fp (Nat.le_refl n)
          A L_hat U_hat k j)
    (hL_entry_eq : ∀ i k : Fin n, k.val < i.val →
      L_hat i k = higham9_2_rectFlDoolittleLEntry fp A L_hat U_hat i k)
    (hU_diag : ∀ k : Fin n, U_hat k k ≠ 0)
    (hn : gammaValid fp n)
    (hL_coeff : ∀ i k : Fin n, k.val < i.val →
      gamma fp k.val + fp.u + fp.u ≤ gamma fp n)
    (hU_gap : ∀ k j : Fin n, k.val ≤ j.val →
      |A (higham9_2_rectRow (Nat.le_refl n) k) j| + (1 + fp.u) *
          higham9_2_rectDoolittleUProductAbs fp (Nat.le_refl n)
            A L_hat U_hat k j +
        higham9_2_rectDoolittleUExactTargetResidualBudget fp
          (Nat.le_refl n) A L_hat U_hat k j ≤
        |higham9_2_rectDoolittleUExactTarget (Nat.le_refl n)
          A L_hat U_hat k j|)
    (hL_gap : ∀ i k : Fin n, k.val < i.val →
      |A i k| + (1 + fp.u) *
          higham9_2_rectDoolittleLProductAbs fp A L_hat U_hat i k +
        higham9_2_rectDoolittleLExactTargetEntryResidualBudget fp
          A L_hat U_hat i k ≤
        |higham9_2_rectDoolittleLExactTarget A L_hat U_hat i k|)
    (hL_num_gap : ∀ i k : Fin n, k.val < i.val →
      ((|A i k| + higham9_2_rectDoolittleLProductAbs fp A L_hat U_hat i k) +
        higham9_2_rectDoolittleLExactTargetNumeratorResidualBudget
          fp A L_hat U_hat i k) +
        higham9_2_rectDoolittleLExactTargetEntryResidualBudget
          fp A L_hat U_hat i k ≤
        |higham9_2_rectDoolittleLExactTarget A L_hat U_hat i k|)
    (hγ_le_u : gamma fp n ≤ u)
    (hAbsLU_le : ∀ i j : Fin n,
      ∑ k : Fin n, |L_hat i k| * |U_hat k j| ≤ c * |A i j|) :
    let y_hat := fl_forwardSub fp n L_hat b
    let x_hat := fl_backSub fp n U_hat y_hat
    ∃ DeltaA : Fin n → Fin n → ℝ,
      (∀ i j, |DeltaA i j| ≤ c * higham9_14_h u * |A i j|) ∧
      (∀ i, ∑ j : Fin n, (A i j + DeltaA i j) * x_hat j = b i) :=
  higham9_14_source_h_bound_of_RectDoolittleDenseLoopAbsBudgetCertificate_square_fl_triangular_solves_const_gamma_le
    fp n A L_hat U_hat b
    (higham9_2_rectDoolittleUAbsBudget fp (Nat.le_refl n) A L_hat U_hat)
    (higham9_2_rectDoolittleLAbsBudget fp A L_hat U_hat)
    c u hc hu hu_lt_one hn
    (higham9_2_rectAbsBudgetCertificate_of_literal_doolittle_exact_target_gaps
      (hmn := Nat.le_refl n) (A := A) (L := L_hat) (U := U_hat)
      hL_diag hL_upper_zero hU_lower_zero hU_entry_eq hL_entry_eq
      hU_diag hn hL_coeff hU_gap hL_gap hL_num_gap)
    hγ_le_u hU_diag hAbsLU_le

/-- **Theorem 9.14**, square-specialized rectangular literal exact-target
gap form for the source-facing `f(γ_n)` bound. -/
theorem higham9_14_source_f_bound_of_rectLiteralDoolittle_exactTargetGaps_square_fl_triangular_solves_gamma
    (fp : FPModel) (n : ℕ)
    (A L_hat U_hat : Fin n → Fin n → ℝ)
    (b : Fin n → ℝ)
    (c : ℝ)
    (hL_diag : ∀ k : Fin n, L_hat (higham9_2_rectRow (Nat.le_refl n) k) k = 1)
    (hL_upper_zero : ∀ i j : Fin n, i.val < j.val → L_hat i j = 0)
    (hU_lower_zero : ∀ i j : Fin n, j.val < i.val → U_hat i j = 0)
    (hU_entry_eq : ∀ k j : Fin n, k.val ≤ j.val →
      U_hat k j =
        higham9_2_rectFlDoolittleUEntry fp (Nat.le_refl n)
          A L_hat U_hat k j)
    (hL_entry_eq : ∀ i k : Fin n, k.val < i.val →
      L_hat i k = higham9_2_rectFlDoolittleLEntry fp A L_hat U_hat i k)
    (hU_diag : ∀ k : Fin n, U_hat k k ≠ 0)
    (hn : gammaValid fp n)
    (hL_coeff : ∀ i k : Fin n, k.val < i.val →
      gamma fp k.val + fp.u + fp.u ≤ gamma fp n)
    (hU_gap : ∀ k j : Fin n, k.val ≤ j.val →
      |A (higham9_2_rectRow (Nat.le_refl n) k) j| + (1 + fp.u) *
          higham9_2_rectDoolittleUProductAbs fp (Nat.le_refl n)
            A L_hat U_hat k j +
        higham9_2_rectDoolittleUExactTargetResidualBudget fp
          (Nat.le_refl n) A L_hat U_hat k j ≤
        |higham9_2_rectDoolittleUExactTarget (Nat.le_refl n)
          A L_hat U_hat k j|)
    (hL_gap : ∀ i k : Fin n, k.val < i.val →
      |A i k| + (1 + fp.u) *
          higham9_2_rectDoolittleLProductAbs fp A L_hat U_hat i k +
        higham9_2_rectDoolittleLExactTargetEntryResidualBudget fp
          A L_hat U_hat i k ≤
        |higham9_2_rectDoolittleLExactTarget A L_hat U_hat i k|)
    (hL_num_gap : ∀ i k : Fin n, k.val < i.val →
      ((|A i k| + higham9_2_rectDoolittleLProductAbs fp A L_hat U_hat i k) +
        higham9_2_rectDoolittleLExactTargetNumeratorResidualBudget
          fp A L_hat U_hat i k) +
        higham9_2_rectDoolittleLExactTargetEntryResidualBudget
          fp A L_hat U_hat i k ≤
        |higham9_2_rectDoolittleLExactTarget A L_hat U_hat i k|)
    (hAbsLU_le : ∀ i j : Fin n,
      ∑ k : Fin n, |L_hat i k| * |U_hat k j| ≤ c * |A i j|) :
    let y_hat := fl_forwardSub fp n L_hat b
    let x_hat := fl_backSub fp n U_hat y_hat
    ∃ DeltaA : Fin n → Fin n → ℝ,
      (∀ i j, |DeltaA i j| ≤
        c * higham9_14_f (gamma fp n) * |A i j|) ∧
      (∀ i, ∑ j : Fin n, (A i j + DeltaA i j) * x_hat j = b i) :=
  higham9_14_source_f_bound_of_rectLiteralDoolittle_exactTargetGaps_square_fl_triangular_solves_gamma_le
    fp n A L_hat U_hat b c (gamma fp n) (gamma_nonneg fp hn)
    hL_diag hL_upper_zero hU_lower_zero hU_entry_eq hL_entry_eq hU_diag
    hn hL_coeff hU_gap hL_gap hL_num_gap le_rfl hAbsLU_le

/-- **Theorem 9.14**, square-specialized rectangular literal exact-target
gap form for the final exact-growth `h(γ_n)` bound. -/
theorem higham9_14_source_h_bound_of_rectLiteralDoolittle_exactTargetGaps_square_fl_triangular_solves_gamma
    (fp : FPModel) (n : ℕ)
    (A L_hat U_hat : Fin n → Fin n → ℝ)
    (b : Fin n → ℝ)
    (hγ_lt_one : gamma fp n < 1)
    (hL_diag : ∀ k : Fin n, L_hat (higham9_2_rectRow (Nat.le_refl n) k) k = 1)
    (hL_upper_zero : ∀ i j : Fin n, i.val < j.val → L_hat i j = 0)
    (hU_lower_zero : ∀ i j : Fin n, j.val < i.val → U_hat i j = 0)
    (hU_entry_eq : ∀ k j : Fin n, k.val ≤ j.val →
      U_hat k j =
        higham9_2_rectFlDoolittleUEntry fp (Nat.le_refl n)
          A L_hat U_hat k j)
    (hL_entry_eq : ∀ i k : Fin n, k.val < i.val →
      L_hat i k = higham9_2_rectFlDoolittleLEntry fp A L_hat U_hat i k)
    (hU_diag : ∀ k : Fin n, U_hat k k ≠ 0)
    (hn : gammaValid fp n)
    (hL_coeff : ∀ i k : Fin n, k.val < i.val →
      gamma fp k.val + fp.u + fp.u ≤ gamma fp n)
    (hU_gap : ∀ k j : Fin n, k.val ≤ j.val →
      |A (higham9_2_rectRow (Nat.le_refl n) k) j| + (1 + fp.u) *
          higham9_2_rectDoolittleUProductAbs fp (Nat.le_refl n)
            A L_hat U_hat k j +
        higham9_2_rectDoolittleUExactTargetResidualBudget fp
          (Nat.le_refl n) A L_hat U_hat k j ≤
        |higham9_2_rectDoolittleUExactTarget (Nat.le_refl n)
          A L_hat U_hat k j|)
    (hL_gap : ∀ i k : Fin n, k.val < i.val →
      |A i k| + (1 + fp.u) *
          higham9_2_rectDoolittleLProductAbs fp A L_hat U_hat i k +
        higham9_2_rectDoolittleLExactTargetEntryResidualBudget fp
          A L_hat U_hat i k ≤
        |higham9_2_rectDoolittleLExactTarget A L_hat U_hat i k|)
    (hL_num_gap : ∀ i k : Fin n, k.val < i.val →
      ((|A i k| + higham9_2_rectDoolittleLProductAbs fp A L_hat U_hat i k) +
        higham9_2_rectDoolittleLExactTargetNumeratorResidualBudget
          fp A L_hat U_hat i k) +
        higham9_2_rectDoolittleLExactTargetEntryResidualBudget
          fp A L_hat U_hat i k ≤
        |higham9_2_rectDoolittleLExactTarget A L_hat U_hat i k|)
    (hAbsLU_le : ∀ i j : Fin n,
      ∑ k : Fin n, |L_hat i k| * |U_hat k j| ≤ |A i j|) :
    let y_hat := fl_forwardSub fp n L_hat b
    let x_hat := fl_backSub fp n U_hat y_hat
    ∃ DeltaA : Fin n → Fin n → ℝ,
      (∀ i j, |DeltaA i j| ≤
        higham9_14_h (gamma fp n) * |A i j|) ∧
      (∀ i, ∑ j : Fin n, (A i j + DeltaA i j) * x_hat j = b i) :=
  higham9_14_source_h_bound_of_rectLiteralDoolittle_exactTargetGaps_square_fl_triangular_solves_gamma_le
    fp n A L_hat U_hat b (gamma fp n) (gamma_nonneg fp hn)
    hγ_lt_one hL_diag hL_upper_zero hU_lower_zero hU_entry_eq hL_entry_eq
    hU_diag hn hL_coeff hU_gap hL_gap hL_num_gap le_rfl hAbsLU_le

/-- **Theorem 9.14**, square-specialized rectangular literal exact-target
gap form for the final constant-growth `h(γ_n)` bound. -/
theorem higham9_14_source_h_bound_of_rectLiteralDoolittle_exactTargetGaps_square_fl_triangular_solves_const_gamma
    (fp : FPModel) (n : ℕ)
    (A L_hat U_hat : Fin n → Fin n → ℝ)
    (b : Fin n → ℝ)
    (c : ℝ) (hc : 0 ≤ c)
    (hγ_lt_one : gamma fp n < 1)
    (hL_diag : ∀ k : Fin n, L_hat (higham9_2_rectRow (Nat.le_refl n) k) k = 1)
    (hL_upper_zero : ∀ i j : Fin n, i.val < j.val → L_hat i j = 0)
    (hU_lower_zero : ∀ i j : Fin n, j.val < i.val → U_hat i j = 0)
    (hU_entry_eq : ∀ k j : Fin n, k.val ≤ j.val →
      U_hat k j =
        higham9_2_rectFlDoolittleUEntry fp (Nat.le_refl n)
          A L_hat U_hat k j)
    (hL_entry_eq : ∀ i k : Fin n, k.val < i.val →
      L_hat i k = higham9_2_rectFlDoolittleLEntry fp A L_hat U_hat i k)
    (hU_diag : ∀ k : Fin n, U_hat k k ≠ 0)
    (hn : gammaValid fp n)
    (hL_coeff : ∀ i k : Fin n, k.val < i.val →
      gamma fp k.val + fp.u + fp.u ≤ gamma fp n)
    (hU_gap : ∀ k j : Fin n, k.val ≤ j.val →
      |A (higham9_2_rectRow (Nat.le_refl n) k) j| + (1 + fp.u) *
          higham9_2_rectDoolittleUProductAbs fp (Nat.le_refl n)
            A L_hat U_hat k j +
        higham9_2_rectDoolittleUExactTargetResidualBudget fp
          (Nat.le_refl n) A L_hat U_hat k j ≤
        |higham9_2_rectDoolittleUExactTarget (Nat.le_refl n)
          A L_hat U_hat k j|)
    (hL_gap : ∀ i k : Fin n, k.val < i.val →
      |A i k| + (1 + fp.u) *
          higham9_2_rectDoolittleLProductAbs fp A L_hat U_hat i k +
        higham9_2_rectDoolittleLExactTargetEntryResidualBudget fp
          A L_hat U_hat i k ≤
        |higham9_2_rectDoolittleLExactTarget A L_hat U_hat i k|)
    (hL_num_gap : ∀ i k : Fin n, k.val < i.val →
      ((|A i k| + higham9_2_rectDoolittleLProductAbs fp A L_hat U_hat i k) +
        higham9_2_rectDoolittleLExactTargetNumeratorResidualBudget
          fp A L_hat U_hat i k) +
        higham9_2_rectDoolittleLExactTargetEntryResidualBudget
          fp A L_hat U_hat i k ≤
        |higham9_2_rectDoolittleLExactTarget A L_hat U_hat i k|)
    (hAbsLU_le : ∀ i j : Fin n,
      ∑ k : Fin n, |L_hat i k| * |U_hat k j| ≤ c * |A i j|) :
    let y_hat := fl_forwardSub fp n L_hat b
    let x_hat := fl_backSub fp n U_hat y_hat
    ∃ DeltaA : Fin n → Fin n → ℝ,
      (∀ i j, |DeltaA i j| ≤
        c * higham9_14_h (gamma fp n) * |A i j|) ∧
      (∀ i, ∑ j : Fin n, (A i j + DeltaA i j) * x_hat j = b i) :=
  higham9_14_source_h_bound_of_rectLiteralDoolittle_exactTargetGaps_square_fl_triangular_solves_const_gamma_le
    fp n A L_hat U_hat b c (gamma fp n) hc (gamma_nonneg fp hn)
    hγ_lt_one hL_diag hL_upper_zero hU_lower_zero hU_entry_eq hL_entry_eq
    hU_diag hn hL_coeff hU_gap hL_gap hL_num_gap le_rfl hAbsLU_le

/-- **Theorem 9.14**, Matrix-facing square-specialized rectangular literal
exact-target gap form for the source `f(u)` bound. -/
theorem higham9_14_matrix_source_f_bound_of_rectLiteralDoolittle_exactTargetGaps_square_fl_triangular_solves_gamma_le
    (fp : FPModel) (n : ℕ)
    (A L_hat U_hat : Matrix (Fin n) (Fin n) ℝ)
    (b : Fin n → ℝ)
    (c u : ℝ) (hu : 0 ≤ u)
    (hL_diag : ∀ k : Fin n, L_hat (higham9_2_rectRow (Nat.le_refl n) k) k = 1)
    (hL_upper_zero : ∀ i j : Fin n, i.val < j.val → L_hat i j = 0)
    (hU_lower_zero : ∀ i j : Fin n, j.val < i.val → U_hat i j = 0)
    (hU_entry_eq : ∀ k j : Fin n, k.val ≤ j.val →
      U_hat k j =
        higham9_2_rectFlDoolittleUEntry fp (Nat.le_refl n)
          A L_hat U_hat k j)
    (hL_entry_eq : ∀ i k : Fin n, k.val < i.val →
      L_hat i k = higham9_2_rectFlDoolittleLEntry fp A L_hat U_hat i k)
    (hU_diag : ∀ k : Fin n, U_hat k k ≠ 0)
    (hn : gammaValid fp n)
    (hL_coeff : ∀ i k : Fin n, k.val < i.val →
      gamma fp k.val + fp.u + fp.u ≤ gamma fp n)
    (hU_gap : ∀ k j : Fin n, k.val ≤ j.val →
      |A (higham9_2_rectRow (Nat.le_refl n) k) j| + (1 + fp.u) *
          higham9_2_rectDoolittleUProductAbs fp (Nat.le_refl n)
            A L_hat U_hat k j +
        higham9_2_rectDoolittleUExactTargetResidualBudget fp
          (Nat.le_refl n) A L_hat U_hat k j ≤
        |higham9_2_rectDoolittleUExactTarget (Nat.le_refl n)
          A L_hat U_hat k j|)
    (hL_gap : ∀ i k : Fin n, k.val < i.val →
      |A i k| + (1 + fp.u) *
          higham9_2_rectDoolittleLProductAbs fp A L_hat U_hat i k +
        higham9_2_rectDoolittleLExactTargetEntryResidualBudget fp
          A L_hat U_hat i k ≤
        |higham9_2_rectDoolittleLExactTarget A L_hat U_hat i k|)
    (hL_num_gap : ∀ i k : Fin n, k.val < i.val →
      ((|A i k| + higham9_2_rectDoolittleLProductAbs fp A L_hat U_hat i k) +
        higham9_2_rectDoolittleLExactTargetNumeratorResidualBudget
          fp A L_hat U_hat i k) +
        higham9_2_rectDoolittleLExactTargetEntryResidualBudget
          fp A L_hat U_hat i k ≤
        |higham9_2_rectDoolittleLExactTarget A L_hat U_hat i k|)
    (hγ_le_u : gamma fp n ≤ u)
    (hAbsLU_le : ∀ i j : Fin n,
      ∑ k : Fin n, |L_hat i k| * |U_hat k j| ≤ c * |A i j|) :
    let y_hat := fl_forwardSub fp n L_hat b
    let x_hat := fl_backSub fp n U_hat y_hat
    ∃ DeltaA : Matrix (Fin n) (Fin n) ℝ,
      (∀ i j, |DeltaA i j| ≤ c * higham9_14_f u * |A i j|) ∧
      Matrix.mulVec (fun i j => A i j + DeltaA i j) x_hat = b :=
  higham9_14_matrix_source_f_bound_of_RectDoolittleDenseLoopAbsBudgetCertificate_square_fl_triangular_solves_gamma_le
    fp n A L_hat U_hat b
    (higham9_2_rectDoolittleUAbsBudget fp (Nat.le_refl n) A L_hat U_hat)
    (higham9_2_rectDoolittleLAbsBudget fp A L_hat U_hat)
    c u hu hn
    (higham9_2_rectAbsBudgetCertificate_of_literal_doolittle_exact_target_gaps
      (hmn := Nat.le_refl n) (A := A) (L := L_hat) (U := U_hat)
      hL_diag hL_upper_zero hU_lower_zero hU_entry_eq hL_entry_eq
      hU_diag hn hL_coeff hU_gap hL_gap hL_num_gap)
    hγ_le_u hU_diag hAbsLU_le

/-- **Theorem 9.14**, Matrix-facing square-specialized rectangular literal
exact-target gap form for the final exact-growth `h(u)` bound. -/
theorem higham9_14_matrix_source_h_bound_of_rectLiteralDoolittle_exactTargetGaps_square_fl_triangular_solves_gamma_le
    (fp : FPModel) (n : ℕ)
    (A L_hat U_hat : Matrix (Fin n) (Fin n) ℝ)
    (b : Fin n → ℝ)
    (u : ℝ) (hu : 0 ≤ u) (hu_lt_one : u < 1)
    (hL_diag : ∀ k : Fin n, L_hat (higham9_2_rectRow (Nat.le_refl n) k) k = 1)
    (hL_upper_zero : ∀ i j : Fin n, i.val < j.val → L_hat i j = 0)
    (hU_lower_zero : ∀ i j : Fin n, j.val < i.val → U_hat i j = 0)
    (hU_entry_eq : ∀ k j : Fin n, k.val ≤ j.val →
      U_hat k j =
        higham9_2_rectFlDoolittleUEntry fp (Nat.le_refl n)
          A L_hat U_hat k j)
    (hL_entry_eq : ∀ i k : Fin n, k.val < i.val →
      L_hat i k = higham9_2_rectFlDoolittleLEntry fp A L_hat U_hat i k)
    (hU_diag : ∀ k : Fin n, U_hat k k ≠ 0)
    (hn : gammaValid fp n)
    (hL_coeff : ∀ i k : Fin n, k.val < i.val →
      gamma fp k.val + fp.u + fp.u ≤ gamma fp n)
    (hU_gap : ∀ k j : Fin n, k.val ≤ j.val →
      |A (higham9_2_rectRow (Nat.le_refl n) k) j| + (1 + fp.u) *
          higham9_2_rectDoolittleUProductAbs fp (Nat.le_refl n)
            A L_hat U_hat k j +
        higham9_2_rectDoolittleUExactTargetResidualBudget fp
          (Nat.le_refl n) A L_hat U_hat k j ≤
        |higham9_2_rectDoolittleUExactTarget (Nat.le_refl n)
          A L_hat U_hat k j|)
    (hL_gap : ∀ i k : Fin n, k.val < i.val →
      |A i k| + (1 + fp.u) *
          higham9_2_rectDoolittleLProductAbs fp A L_hat U_hat i k +
        higham9_2_rectDoolittleLExactTargetEntryResidualBudget fp
          A L_hat U_hat i k ≤
        |higham9_2_rectDoolittleLExactTarget A L_hat U_hat i k|)
    (hL_num_gap : ∀ i k : Fin n, k.val < i.val →
      ((|A i k| + higham9_2_rectDoolittleLProductAbs fp A L_hat U_hat i k) +
        higham9_2_rectDoolittleLExactTargetNumeratorResidualBudget
          fp A L_hat U_hat i k) +
        higham9_2_rectDoolittleLExactTargetEntryResidualBudget
          fp A L_hat U_hat i k ≤
        |higham9_2_rectDoolittleLExactTarget A L_hat U_hat i k|)
    (hγ_le_u : gamma fp n ≤ u)
    (hAbsLU_le : ∀ i j : Fin n,
      ∑ k : Fin n, |L_hat i k| * |U_hat k j| ≤ |A i j|) :
    let y_hat := fl_forwardSub fp n L_hat b
    let x_hat := fl_backSub fp n U_hat y_hat
    ∃ DeltaA : Matrix (Fin n) (Fin n) ℝ,
      (∀ i j, |DeltaA i j| ≤ higham9_14_h u * |A i j|) ∧
      Matrix.mulVec (fun i j => A i j + DeltaA i j) x_hat = b :=
  higham9_14_matrix_source_h_bound_of_RectDoolittleDenseLoopAbsBudgetCertificate_square_fl_triangular_solves_gamma_le
    fp n A L_hat U_hat b
    (higham9_2_rectDoolittleUAbsBudget fp (Nat.le_refl n) A L_hat U_hat)
    (higham9_2_rectDoolittleLAbsBudget fp A L_hat U_hat)
    u hu hu_lt_one hn
    (higham9_2_rectAbsBudgetCertificate_of_literal_doolittle_exact_target_gaps
      (hmn := Nat.le_refl n) (A := A) (L := L_hat) (U := U_hat)
      hL_diag hL_upper_zero hU_lower_zero hU_entry_eq hL_entry_eq
      hU_diag hn hL_coeff hU_gap hL_gap hL_num_gap)
    hγ_le_u hU_diag hAbsLU_le

/-- **Theorem 9.14**, Matrix-facing square-specialized rectangular literal
exact-target gap form for the final constant-growth `h(u)` bound. -/
theorem higham9_14_matrix_source_h_bound_of_rectLiteralDoolittle_exactTargetGaps_square_fl_triangular_solves_const_gamma_le
    (fp : FPModel) (n : ℕ)
    (A L_hat U_hat : Matrix (Fin n) (Fin n) ℝ)
    (b : Fin n → ℝ)
    (c u : ℝ) (hc : 0 ≤ c) (hu : 0 ≤ u) (hu_lt_one : u < 1)
    (hL_diag : ∀ k : Fin n, L_hat (higham9_2_rectRow (Nat.le_refl n) k) k = 1)
    (hL_upper_zero : ∀ i j : Fin n, i.val < j.val → L_hat i j = 0)
    (hU_lower_zero : ∀ i j : Fin n, j.val < i.val → U_hat i j = 0)
    (hU_entry_eq : ∀ k j : Fin n, k.val ≤ j.val →
      U_hat k j =
        higham9_2_rectFlDoolittleUEntry fp (Nat.le_refl n)
          A L_hat U_hat k j)
    (hL_entry_eq : ∀ i k : Fin n, k.val < i.val →
      L_hat i k = higham9_2_rectFlDoolittleLEntry fp A L_hat U_hat i k)
    (hU_diag : ∀ k : Fin n, U_hat k k ≠ 0)
    (hn : gammaValid fp n)
    (hL_coeff : ∀ i k : Fin n, k.val < i.val →
      gamma fp k.val + fp.u + fp.u ≤ gamma fp n)
    (hU_gap : ∀ k j : Fin n, k.val ≤ j.val →
      |A (higham9_2_rectRow (Nat.le_refl n) k) j| + (1 + fp.u) *
          higham9_2_rectDoolittleUProductAbs fp (Nat.le_refl n)
            A L_hat U_hat k j +
        higham9_2_rectDoolittleUExactTargetResidualBudget fp
          (Nat.le_refl n) A L_hat U_hat k j ≤
        |higham9_2_rectDoolittleUExactTarget (Nat.le_refl n)
          A L_hat U_hat k j|)
    (hL_gap : ∀ i k : Fin n, k.val < i.val →
      |A i k| + (1 + fp.u) *
          higham9_2_rectDoolittleLProductAbs fp A L_hat U_hat i k +
        higham9_2_rectDoolittleLExactTargetEntryResidualBudget fp
          A L_hat U_hat i k ≤
        |higham9_2_rectDoolittleLExactTarget A L_hat U_hat i k|)
    (hL_num_gap : ∀ i k : Fin n, k.val < i.val →
      ((|A i k| + higham9_2_rectDoolittleLProductAbs fp A L_hat U_hat i k) +
        higham9_2_rectDoolittleLExactTargetNumeratorResidualBudget
          fp A L_hat U_hat i k) +
        higham9_2_rectDoolittleLExactTargetEntryResidualBudget
          fp A L_hat U_hat i k ≤
        |higham9_2_rectDoolittleLExactTarget A L_hat U_hat i k|)
    (hγ_le_u : gamma fp n ≤ u)
    (hAbsLU_le : ∀ i j : Fin n,
      ∑ k : Fin n, |L_hat i k| * |U_hat k j| ≤ c * |A i j|) :
    let y_hat := fl_forwardSub fp n L_hat b
    let x_hat := fl_backSub fp n U_hat y_hat
    ∃ DeltaA : Matrix (Fin n) (Fin n) ℝ,
      (∀ i j, |DeltaA i j| ≤ c * higham9_14_h u * |A i j|) ∧
      Matrix.mulVec (fun i j => A i j + DeltaA i j) x_hat = b :=
  higham9_14_matrix_source_h_bound_of_RectDoolittleDenseLoopAbsBudgetCertificate_square_fl_triangular_solves_const_gamma_le
    fp n A L_hat U_hat b
    (higham9_2_rectDoolittleUAbsBudget fp (Nat.le_refl n) A L_hat U_hat)
    (higham9_2_rectDoolittleLAbsBudget fp A L_hat U_hat)
    c u hc hu hu_lt_one hn
    (higham9_2_rectAbsBudgetCertificate_of_literal_doolittle_exact_target_gaps
      (hmn := Nat.le_refl n) (A := A) (L := L_hat) (U := U_hat)
      hL_diag hL_upper_zero hU_lower_zero hU_entry_eq hL_entry_eq
      hU_diag hn hL_coeff hU_gap hL_gap hL_num_gap)
    hγ_le_u hU_diag hAbsLU_le

/-- **Theorem 9.14**, Matrix-facing square-specialized rectangular literal
exact-target gap form for the source `f(γ_n)` bound. -/
theorem higham9_14_matrix_source_f_bound_of_rectLiteralDoolittle_exactTargetGaps_square_fl_triangular_solves_gamma
    (fp : FPModel) (n : ℕ)
    (A L_hat U_hat : Matrix (Fin n) (Fin n) ℝ)
    (b : Fin n → ℝ)
    (c : ℝ)
    (hL_diag : ∀ k : Fin n, L_hat (higham9_2_rectRow (Nat.le_refl n) k) k = 1)
    (hL_upper_zero : ∀ i j : Fin n, i.val < j.val → L_hat i j = 0)
    (hU_lower_zero : ∀ i j : Fin n, j.val < i.val → U_hat i j = 0)
    (hU_entry_eq : ∀ k j : Fin n, k.val ≤ j.val →
      U_hat k j =
        higham9_2_rectFlDoolittleUEntry fp (Nat.le_refl n)
          A L_hat U_hat k j)
    (hL_entry_eq : ∀ i k : Fin n, k.val < i.val →
      L_hat i k = higham9_2_rectFlDoolittleLEntry fp A L_hat U_hat i k)
    (hU_diag : ∀ k : Fin n, U_hat k k ≠ 0)
    (hn : gammaValid fp n)
    (hL_coeff : ∀ i k : Fin n, k.val < i.val →
      gamma fp k.val + fp.u + fp.u ≤ gamma fp n)
    (hU_gap : ∀ k j : Fin n, k.val ≤ j.val →
      |A (higham9_2_rectRow (Nat.le_refl n) k) j| + (1 + fp.u) *
          higham9_2_rectDoolittleUProductAbs fp (Nat.le_refl n)
            A L_hat U_hat k j +
        higham9_2_rectDoolittleUExactTargetResidualBudget fp
          (Nat.le_refl n) A L_hat U_hat k j ≤
        |higham9_2_rectDoolittleUExactTarget (Nat.le_refl n)
          A L_hat U_hat k j|)
    (hL_gap : ∀ i k : Fin n, k.val < i.val →
      |A i k| + (1 + fp.u) *
          higham9_2_rectDoolittleLProductAbs fp A L_hat U_hat i k +
        higham9_2_rectDoolittleLExactTargetEntryResidualBudget fp
          A L_hat U_hat i k ≤
        |higham9_2_rectDoolittleLExactTarget A L_hat U_hat i k|)
    (hL_num_gap : ∀ i k : Fin n, k.val < i.val →
      ((|A i k| + higham9_2_rectDoolittleLProductAbs fp A L_hat U_hat i k) +
        higham9_2_rectDoolittleLExactTargetNumeratorResidualBudget
          fp A L_hat U_hat i k) +
        higham9_2_rectDoolittleLExactTargetEntryResidualBudget
          fp A L_hat U_hat i k ≤
        |higham9_2_rectDoolittleLExactTarget A L_hat U_hat i k|)
    (hAbsLU_le : ∀ i j : Fin n,
      ∑ k : Fin n, |L_hat i k| * |U_hat k j| ≤ c * |A i j|) :
    let y_hat := fl_forwardSub fp n L_hat b
    let x_hat := fl_backSub fp n U_hat y_hat
    ∃ DeltaA : Matrix (Fin n) (Fin n) ℝ,
      (∀ i j, |DeltaA i j| ≤
        c * higham9_14_f (gamma fp n) * |A i j|) ∧
      Matrix.mulVec (fun i j => A i j + DeltaA i j) x_hat = b :=
  higham9_14_matrix_source_f_bound_of_rectLiteralDoolittle_exactTargetGaps_square_fl_triangular_solves_gamma_le
    fp n A L_hat U_hat b c (gamma fp n) (gamma_nonneg fp hn)
    hL_diag hL_upper_zero hU_lower_zero hU_entry_eq hL_entry_eq hU_diag
    hn hL_coeff hU_gap hL_gap hL_num_gap le_rfl hAbsLU_le

/-- **Theorem 9.14**, Matrix-facing square-specialized rectangular literal
exact-target gap form for the final exact-growth `h(γ_n)` bound. -/
theorem higham9_14_matrix_source_h_bound_of_rectLiteralDoolittle_exactTargetGaps_square_fl_triangular_solves_gamma
    (fp : FPModel) (n : ℕ)
    (A L_hat U_hat : Matrix (Fin n) (Fin n) ℝ)
    (b : Fin n → ℝ)
    (hγ_lt_one : gamma fp n < 1)
    (hL_diag : ∀ k : Fin n, L_hat (higham9_2_rectRow (Nat.le_refl n) k) k = 1)
    (hL_upper_zero : ∀ i j : Fin n, i.val < j.val → L_hat i j = 0)
    (hU_lower_zero : ∀ i j : Fin n, j.val < i.val → U_hat i j = 0)
    (hU_entry_eq : ∀ k j : Fin n, k.val ≤ j.val →
      U_hat k j =
        higham9_2_rectFlDoolittleUEntry fp (Nat.le_refl n)
          A L_hat U_hat k j)
    (hL_entry_eq : ∀ i k : Fin n, k.val < i.val →
      L_hat i k = higham9_2_rectFlDoolittleLEntry fp A L_hat U_hat i k)
    (hU_diag : ∀ k : Fin n, U_hat k k ≠ 0)
    (hn : gammaValid fp n)
    (hL_coeff : ∀ i k : Fin n, k.val < i.val →
      gamma fp k.val + fp.u + fp.u ≤ gamma fp n)
    (hU_gap : ∀ k j : Fin n, k.val ≤ j.val →
      |A (higham9_2_rectRow (Nat.le_refl n) k) j| + (1 + fp.u) *
          higham9_2_rectDoolittleUProductAbs fp (Nat.le_refl n)
            A L_hat U_hat k j +
        higham9_2_rectDoolittleUExactTargetResidualBudget fp
          (Nat.le_refl n) A L_hat U_hat k j ≤
        |higham9_2_rectDoolittleUExactTarget (Nat.le_refl n)
          A L_hat U_hat k j|)
    (hL_gap : ∀ i k : Fin n, k.val < i.val →
      |A i k| + (1 + fp.u) *
          higham9_2_rectDoolittleLProductAbs fp A L_hat U_hat i k +
        higham9_2_rectDoolittleLExactTargetEntryResidualBudget fp
          A L_hat U_hat i k ≤
        |higham9_2_rectDoolittleLExactTarget A L_hat U_hat i k|)
    (hL_num_gap : ∀ i k : Fin n, k.val < i.val →
      ((|A i k| + higham9_2_rectDoolittleLProductAbs fp A L_hat U_hat i k) +
        higham9_2_rectDoolittleLExactTargetNumeratorResidualBudget
          fp A L_hat U_hat i k) +
        higham9_2_rectDoolittleLExactTargetEntryResidualBudget
          fp A L_hat U_hat i k ≤
        |higham9_2_rectDoolittleLExactTarget A L_hat U_hat i k|)
    (hAbsLU_le : ∀ i j : Fin n,
      ∑ k : Fin n, |L_hat i k| * |U_hat k j| ≤ |A i j|) :
    let y_hat := fl_forwardSub fp n L_hat b
    let x_hat := fl_backSub fp n U_hat y_hat
    ∃ DeltaA : Matrix (Fin n) (Fin n) ℝ,
      (∀ i j, |DeltaA i j| ≤
        higham9_14_h (gamma fp n) * |A i j|) ∧
      Matrix.mulVec (fun i j => A i j + DeltaA i j) x_hat = b :=
  higham9_14_matrix_source_h_bound_of_rectLiteralDoolittle_exactTargetGaps_square_fl_triangular_solves_gamma_le
    fp n A L_hat U_hat b (gamma fp n) (gamma_nonneg fp hn)
    hγ_lt_one hL_diag hL_upper_zero hU_lower_zero hU_entry_eq hL_entry_eq
    hU_diag hn hL_coeff hU_gap hL_gap hL_num_gap le_rfl hAbsLU_le

/-- **Theorem 9.14**, Matrix-facing square-specialized rectangular literal
exact-target gap form for the final constant-growth `h(γ_n)` bound. -/
theorem higham9_14_matrix_source_h_bound_of_rectLiteralDoolittle_exactTargetGaps_square_fl_triangular_solves_const_gamma
    (fp : FPModel) (n : ℕ)
    (A L_hat U_hat : Matrix (Fin n) (Fin n) ℝ)
    (b : Fin n → ℝ)
    (c : ℝ) (hc : 0 ≤ c)
    (hγ_lt_one : gamma fp n < 1)
    (hL_diag : ∀ k : Fin n, L_hat (higham9_2_rectRow (Nat.le_refl n) k) k = 1)
    (hL_upper_zero : ∀ i j : Fin n, i.val < j.val → L_hat i j = 0)
    (hU_lower_zero : ∀ i j : Fin n, j.val < i.val → U_hat i j = 0)
    (hU_entry_eq : ∀ k j : Fin n, k.val ≤ j.val →
      U_hat k j =
        higham9_2_rectFlDoolittleUEntry fp (Nat.le_refl n)
          A L_hat U_hat k j)
    (hL_entry_eq : ∀ i k : Fin n, k.val < i.val →
      L_hat i k = higham9_2_rectFlDoolittleLEntry fp A L_hat U_hat i k)
    (hU_diag : ∀ k : Fin n, U_hat k k ≠ 0)
    (hn : gammaValid fp n)
    (hL_coeff : ∀ i k : Fin n, k.val < i.val →
      gamma fp k.val + fp.u + fp.u ≤ gamma fp n)
    (hU_gap : ∀ k j : Fin n, k.val ≤ j.val →
      |A (higham9_2_rectRow (Nat.le_refl n) k) j| + (1 + fp.u) *
          higham9_2_rectDoolittleUProductAbs fp (Nat.le_refl n)
            A L_hat U_hat k j +
        higham9_2_rectDoolittleUExactTargetResidualBudget fp
          (Nat.le_refl n) A L_hat U_hat k j ≤
        |higham9_2_rectDoolittleUExactTarget (Nat.le_refl n)
          A L_hat U_hat k j|)
    (hL_gap : ∀ i k : Fin n, k.val < i.val →
      |A i k| + (1 + fp.u) *
          higham9_2_rectDoolittleLProductAbs fp A L_hat U_hat i k +
        higham9_2_rectDoolittleLExactTargetEntryResidualBudget fp
          A L_hat U_hat i k ≤
        |higham9_2_rectDoolittleLExactTarget A L_hat U_hat i k|)
    (hL_num_gap : ∀ i k : Fin n, k.val < i.val →
      ((|A i k| + higham9_2_rectDoolittleLProductAbs fp A L_hat U_hat i k) +
        higham9_2_rectDoolittleLExactTargetNumeratorResidualBudget
          fp A L_hat U_hat i k) +
        higham9_2_rectDoolittleLExactTargetEntryResidualBudget
          fp A L_hat U_hat i k ≤
        |higham9_2_rectDoolittleLExactTarget A L_hat U_hat i k|)
    (hAbsLU_le : ∀ i j : Fin n,
      ∑ k : Fin n, |L_hat i k| * |U_hat k j| ≤ c * |A i j|) :
    let y_hat := fl_forwardSub fp n L_hat b
    let x_hat := fl_backSub fp n U_hat y_hat
    ∃ DeltaA : Matrix (Fin n) (Fin n) ℝ,
      (∀ i j, |DeltaA i j| ≤
        c * higham9_14_h (gamma fp n) * |A i j|) ∧
      Matrix.mulVec (fun i j => A i j + DeltaA i j) x_hat = b :=
  higham9_14_matrix_source_h_bound_of_rectLiteralDoolittle_exactTargetGaps_square_fl_triangular_solves_const_gamma_le
    fp n A L_hat U_hat b c (gamma fp n) hc (gamma_nonneg fp hn)
    hγ_lt_one hL_diag hL_upper_zero hU_lower_zero hU_entry_eq hL_entry_eq
    hU_diag hn hL_coeff hU_gap hL_gap hL_num_gap le_rfl hAbsLU_le

/-- **Theorem 9.14**, executable rectangular rounded loop source `f(u)` bound.

This is the square executable-loop entry point for the source-facing Theorem
9.14 `f(u)` surface.  The concrete loop supplies the rectangular
absolute-budget certificate; callers still supply the nonzero pivot,
budget-dominance, and structural `|Lhat||Uhat|` comparison hypotheses. -/
theorem higham9_14_source_f_bound_of_rectRoundedLoop_square_fl_triangular_solves_gamma_le
    (fp : FPModel) (n : ℕ)
    (A : Fin n → Fin n → ℝ)
    (b : Fin n → ℝ)
    (c u : ℝ) (hu : 0 ≤ u)
    (hn : gammaValid fp n)
    (hU_diag : ∀ k : Fin n,
      higham9_2_rectRoundedLoopU fp (Nat.le_refl n) A k k ≠ 0)
    (hU_budget_le : ∀ k j : Fin n, k.val ≤ j.val →
      higham9_2_rectDoolittleUAbsBudget fp (Nat.le_refl n) A
          (higham9_2_rectRoundedLoopL fp (Nat.le_refl n) A)
          (higham9_2_rectRoundedLoopU fp (Nat.le_refl n) A) k j ≤
        gamma fp n *
          |higham9_2_rectRoundedLoopU fp (Nat.le_refl n) A k j|)
    (hL_budget_le : ∀ i k : Fin n, k.val < i.val →
      higham9_2_rectDoolittleLAbsBudget fp A
          (higham9_2_rectRoundedLoopL fp (Nat.le_refl n) A)
          (higham9_2_rectRoundedLoopU fp (Nat.le_refl n) A) i k ≤
        gamma fp n *
          |higham9_2_rectRoundedLoopL fp (Nat.le_refl n) A i k *
            higham9_2_rectRoundedLoopU fp (Nat.le_refl n) A k k|)
    (hγ_le_u : gamma fp n ≤ u)
    (hAbsLU_le : ∀ i j : Fin n,
      ∑ k : Fin n,
          |higham9_2_rectRoundedLoopL fp (Nat.le_refl n) A i k| *
            |higham9_2_rectRoundedLoopU fp (Nat.le_refl n) A k j| ≤
        c * |A i j|) :
    let L_hat := higham9_2_rectRoundedLoopL fp (Nat.le_refl n) A
    let U_hat := higham9_2_rectRoundedLoopU fp (Nat.le_refl n) A
    let y_hat := fl_forwardSub fp n L_hat b
    let x_hat := fl_backSub fp n U_hat y_hat
    ∃ DeltaA : Fin n → Fin n → ℝ,
      (∀ i j, |DeltaA i j| ≤ c * higham9_14_f u * |A i j|) ∧
      (∀ i, ∑ j : Fin n, (A i j + DeltaA i j) * x_hat j = b i) := by
  dsimp only
  exact
    higham9_14_source_f_bound_of_RectDoolittleDenseLoopAbsBudgetCertificate_square_fl_triangular_solves_gamma_le
      fp n A
      (higham9_2_rectRoundedLoopL fp (Nat.le_refl n) A)
      (higham9_2_rectRoundedLoopU fp (Nat.le_refl n) A)
      b
      (higham9_2_rectDoolittleUAbsBudget fp (Nat.le_refl n) A
        (higham9_2_rectRoundedLoopL fp (Nat.le_refl n) A)
        (higham9_2_rectRoundedLoopU fp (Nat.le_refl n) A))
      (higham9_2_rectDoolittleLAbsBudget fp A
        (higham9_2_rectRoundedLoopL fp (Nat.le_refl n) A)
        (higham9_2_rectRoundedLoopU fp (Nat.le_refl n) A))
      c u hu hn
      (higham9_2_rectRoundedLoop_to_rectAbsBudgetCertificate fp
        (Nat.le_refl n) A hU_diag hn hU_budget_le hL_budget_le)
      hγ_le_u hU_diag hAbsLU_le

/-- **Theorem 9.14**, executable rectangular rounded loop source `f(γ_n)`
bound. -/
theorem higham9_14_source_f_bound_of_rectRoundedLoop_square_fl_triangular_solves_gamma
    (fp : FPModel) (n : ℕ)
    (A : Fin n → Fin n → ℝ)
    (b : Fin n → ℝ)
    (c : ℝ)
    (hn : gammaValid fp n)
    (hU_diag : ∀ k : Fin n,
      higham9_2_rectRoundedLoopU fp (Nat.le_refl n) A k k ≠ 0)
    (hU_budget_le : ∀ k j : Fin n, k.val ≤ j.val →
      higham9_2_rectDoolittleUAbsBudget fp (Nat.le_refl n) A
          (higham9_2_rectRoundedLoopL fp (Nat.le_refl n) A)
          (higham9_2_rectRoundedLoopU fp (Nat.le_refl n) A) k j ≤
        gamma fp n *
          |higham9_2_rectRoundedLoopU fp (Nat.le_refl n) A k j|)
    (hL_budget_le : ∀ i k : Fin n, k.val < i.val →
      higham9_2_rectDoolittleLAbsBudget fp A
          (higham9_2_rectRoundedLoopL fp (Nat.le_refl n) A)
          (higham9_2_rectRoundedLoopU fp (Nat.le_refl n) A) i k ≤
        gamma fp n *
          |higham9_2_rectRoundedLoopL fp (Nat.le_refl n) A i k *
            higham9_2_rectRoundedLoopU fp (Nat.le_refl n) A k k|)
    (hAbsLU_le : ∀ i j : Fin n,
      ∑ k : Fin n,
          |higham9_2_rectRoundedLoopL fp (Nat.le_refl n) A i k| *
            |higham9_2_rectRoundedLoopU fp (Nat.le_refl n) A k j| ≤
        c * |A i j|) :
    let L_hat := higham9_2_rectRoundedLoopL fp (Nat.le_refl n) A
    let U_hat := higham9_2_rectRoundedLoopU fp (Nat.le_refl n) A
    let y_hat := fl_forwardSub fp n L_hat b
    let x_hat := fl_backSub fp n U_hat y_hat
    ∃ DeltaA : Fin n → Fin n → ℝ,
      (∀ i j, |DeltaA i j| ≤
        c * higham9_14_f (gamma fp n) * |A i j|) ∧
      (∀ i, ∑ j : Fin n, (A i j + DeltaA i j) * x_hat j = b i) := by
  dsimp only
  exact
    higham9_14_source_f_bound_of_rectRoundedLoop_square_fl_triangular_solves_gamma_le
      fp n A b c (gamma fp n) (gamma_nonneg fp hn)
      hn hU_diag hU_budget_le hL_budget_le le_rfl hAbsLU_le

/-- **Theorem 9.14**, executable rectangular rounded loop source `f(u)` bound
with optimal growth `|Lhat||Uhat| <= |A|`. -/
theorem higham9_14_source_f_bound_of_rectRoundedLoop_square_fl_triangular_solves_absLU_le_absA_gamma_le
    (fp : FPModel) (n : ℕ)
    (A : Fin n → Fin n → ℝ)
    (b : Fin n → ℝ)
    (u : ℝ) (hu : 0 ≤ u)
    (hn : gammaValid fp n)
    (hU_diag : ∀ k : Fin n,
      higham9_2_rectRoundedLoopU fp (Nat.le_refl n) A k k ≠ 0)
    (hU_budget_le : ∀ k j : Fin n, k.val ≤ j.val →
      higham9_2_rectDoolittleUAbsBudget fp (Nat.le_refl n) A
          (higham9_2_rectRoundedLoopL fp (Nat.le_refl n) A)
          (higham9_2_rectRoundedLoopU fp (Nat.le_refl n) A) k j ≤
        gamma fp n *
          |higham9_2_rectRoundedLoopU fp (Nat.le_refl n) A k j|)
    (hL_budget_le : ∀ i k : Fin n, k.val < i.val →
      higham9_2_rectDoolittleLAbsBudget fp A
          (higham9_2_rectRoundedLoopL fp (Nat.le_refl n) A)
          (higham9_2_rectRoundedLoopU fp (Nat.le_refl n) A) i k ≤
        gamma fp n *
          |higham9_2_rectRoundedLoopL fp (Nat.le_refl n) A i k *
            higham9_2_rectRoundedLoopU fp (Nat.le_refl n) A k k|)
    (hγ_le_u : gamma fp n ≤ u)
    (hAbsLU_le : ∀ i j : Fin n,
      ∑ k : Fin n,
          |higham9_2_rectRoundedLoopL fp (Nat.le_refl n) A i k| *
            |higham9_2_rectRoundedLoopU fp (Nat.le_refl n) A k j| ≤
        |A i j|) :
    let L_hat := higham9_2_rectRoundedLoopL fp (Nat.le_refl n) A
    let U_hat := higham9_2_rectRoundedLoopU fp (Nat.le_refl n) A
    let y_hat := fl_forwardSub fp n L_hat b
    let x_hat := fl_backSub fp n U_hat y_hat
    ∃ DeltaA : Fin n → Fin n → ℝ,
      (∀ i j, |DeltaA i j| ≤ higham9_14_f u * |A i j|) ∧
      (∀ i, ∑ j : Fin n, (A i j + DeltaA i j) * x_hat j = b i) := by
  simpa [one_mul] using
    (higham9_14_source_f_bound_of_rectRoundedLoop_square_fl_triangular_solves_gamma_le
      fp n A b 1 u hu hn hU_diag hU_budget_le hL_budget_le hγ_le_u
      (fun i j => by simpa [one_mul] using hAbsLU_le i j))

/-- **Theorem 9.14**, executable rectangular rounded loop source `f(γ_n)`
bound with optimal growth `|Lhat||Uhat| <= |A|`. -/
theorem higham9_14_source_f_bound_of_rectRoundedLoop_square_fl_triangular_solves_absLU_le_absA_gamma
    (fp : FPModel) (n : ℕ)
    (A : Fin n → Fin n → ℝ)
    (b : Fin n → ℝ)
    (hn : gammaValid fp n)
    (hU_diag : ∀ k : Fin n,
      higham9_2_rectRoundedLoopU fp (Nat.le_refl n) A k k ≠ 0)
    (hU_budget_le : ∀ k j : Fin n, k.val ≤ j.val →
      higham9_2_rectDoolittleUAbsBudget fp (Nat.le_refl n) A
          (higham9_2_rectRoundedLoopL fp (Nat.le_refl n) A)
          (higham9_2_rectRoundedLoopU fp (Nat.le_refl n) A) k j ≤
        gamma fp n *
          |higham9_2_rectRoundedLoopU fp (Nat.le_refl n) A k j|)
    (hL_budget_le : ∀ i k : Fin n, k.val < i.val →
      higham9_2_rectDoolittleLAbsBudget fp A
          (higham9_2_rectRoundedLoopL fp (Nat.le_refl n) A)
          (higham9_2_rectRoundedLoopU fp (Nat.le_refl n) A) i k ≤
        gamma fp n *
          |higham9_2_rectRoundedLoopL fp (Nat.le_refl n) A i k *
            higham9_2_rectRoundedLoopU fp (Nat.le_refl n) A k k|)
    (hAbsLU_le : ∀ i j : Fin n,
      ∑ k : Fin n,
          |higham9_2_rectRoundedLoopL fp (Nat.le_refl n) A i k| *
            |higham9_2_rectRoundedLoopU fp (Nat.le_refl n) A k j| ≤
        |A i j|) :
    let L_hat := higham9_2_rectRoundedLoopL fp (Nat.le_refl n) A
    let U_hat := higham9_2_rectRoundedLoopU fp (Nat.le_refl n) A
    let y_hat := fl_forwardSub fp n L_hat b
    let x_hat := fl_backSub fp n U_hat y_hat
    ∃ DeltaA : Fin n → Fin n → ℝ,
      (∀ i j, |DeltaA i j| ≤
        higham9_14_f (gamma fp n) * |A i j|) ∧
      (∀ i, ∑ j : Fin n, (A i j + DeltaA i j) * x_hat j = b i) := by
  simpa [one_mul] using
    (higham9_14_source_f_bound_of_rectRoundedLoop_square_fl_triangular_solves_gamma
      fp n A b 1 hn hU_diag hU_budget_le hL_budget_le
      (fun i j => by simpa [one_mul] using hAbsLU_le i j))

/-- **Theorem 9.14**, executable rectangular rounded loop source `h(u)` bound
with the exact-growth comparison `|Lhat||Uhat| <= |A|`. -/
theorem higham9_14_source_h_bound_of_rectRoundedLoop_square_fl_triangular_solves_gamma_le
    (fp : FPModel) (n : ℕ)
    (A : Fin n → Fin n → ℝ)
    (b : Fin n → ℝ)
    (u : ℝ) (hu : 0 ≤ u) (hu_lt_one : u < 1)
    (hn : gammaValid fp n)
    (hU_diag : ∀ k : Fin n,
      higham9_2_rectRoundedLoopU fp (Nat.le_refl n) A k k ≠ 0)
    (hU_budget_le : ∀ k j : Fin n, k.val ≤ j.val →
      higham9_2_rectDoolittleUAbsBudget fp (Nat.le_refl n) A
          (higham9_2_rectRoundedLoopL fp (Nat.le_refl n) A)
          (higham9_2_rectRoundedLoopU fp (Nat.le_refl n) A) k j ≤
        gamma fp n *
          |higham9_2_rectRoundedLoopU fp (Nat.le_refl n) A k j|)
    (hL_budget_le : ∀ i k : Fin n, k.val < i.val →
      higham9_2_rectDoolittleLAbsBudget fp A
          (higham9_2_rectRoundedLoopL fp (Nat.le_refl n) A)
          (higham9_2_rectRoundedLoopU fp (Nat.le_refl n) A) i k ≤
        gamma fp n *
          |higham9_2_rectRoundedLoopL fp (Nat.le_refl n) A i k *
            higham9_2_rectRoundedLoopU fp (Nat.le_refl n) A k k|)
    (hγ_le_u : gamma fp n ≤ u)
    (hAbsLU_le : ∀ i j : Fin n,
      ∑ k : Fin n,
          |higham9_2_rectRoundedLoopL fp (Nat.le_refl n) A i k| *
            |higham9_2_rectRoundedLoopU fp (Nat.le_refl n) A k j| ≤
        |A i j|) :
    let L_hat := higham9_2_rectRoundedLoopL fp (Nat.le_refl n) A
    let U_hat := higham9_2_rectRoundedLoopU fp (Nat.le_refl n) A
    let y_hat := fl_forwardSub fp n L_hat b
    let x_hat := fl_backSub fp n U_hat y_hat
    ∃ DeltaA : Fin n → Fin n → ℝ,
      (∀ i j, |DeltaA i j| ≤ higham9_14_h u * |A i j|) ∧
      (∀ i, ∑ j : Fin n, (A i j + DeltaA i j) * x_hat j = b i) := by
  dsimp only
  exact
    higham9_14_source_h_bound_of_RectDoolittleDenseLoopAbsBudgetCertificate_square_fl_triangular_solves_gamma_le
      fp n A
      (higham9_2_rectRoundedLoopL fp (Nat.le_refl n) A)
      (higham9_2_rectRoundedLoopU fp (Nat.le_refl n) A)
      b
      (higham9_2_rectDoolittleUAbsBudget fp (Nat.le_refl n) A
        (higham9_2_rectRoundedLoopL fp (Nat.le_refl n) A)
        (higham9_2_rectRoundedLoopU fp (Nat.le_refl n) A))
      (higham9_2_rectDoolittleLAbsBudget fp A
        (higham9_2_rectRoundedLoopL fp (Nat.le_refl n) A)
        (higham9_2_rectRoundedLoopU fp (Nat.le_refl n) A))
      u hu hu_lt_one hn
      (higham9_2_rectRoundedLoop_to_rectAbsBudgetCertificate fp
        (Nat.le_refl n) A hU_diag hn hU_budget_le hL_budget_le)
      hγ_le_u hU_diag hAbsLU_le

/-- **Theorem 9.14**, executable rectangular rounded loop source `h(γ_n)`
bound with the exact-growth comparison `|Lhat||Uhat| <= |A|`. -/
theorem higham9_14_source_h_bound_of_rectRoundedLoop_square_fl_triangular_solves_gamma
    (fp : FPModel) (n : ℕ)
    (A : Fin n → Fin n → ℝ)
    (b : Fin n → ℝ)
    (hn : gammaValid fp n)
    (hγ_lt_one : gamma fp n < 1)
    (hU_diag : ∀ k : Fin n,
      higham9_2_rectRoundedLoopU fp (Nat.le_refl n) A k k ≠ 0)
    (hU_budget_le : ∀ k j : Fin n, k.val ≤ j.val →
      higham9_2_rectDoolittleUAbsBudget fp (Nat.le_refl n) A
          (higham9_2_rectRoundedLoopL fp (Nat.le_refl n) A)
          (higham9_2_rectRoundedLoopU fp (Nat.le_refl n) A) k j ≤
        gamma fp n *
          |higham9_2_rectRoundedLoopU fp (Nat.le_refl n) A k j|)
    (hL_budget_le : ∀ i k : Fin n, k.val < i.val →
      higham9_2_rectDoolittleLAbsBudget fp A
          (higham9_2_rectRoundedLoopL fp (Nat.le_refl n) A)
          (higham9_2_rectRoundedLoopU fp (Nat.le_refl n) A) i k ≤
        gamma fp n *
          |higham9_2_rectRoundedLoopL fp (Nat.le_refl n) A i k *
            higham9_2_rectRoundedLoopU fp (Nat.le_refl n) A k k|)
    (hAbsLU_le : ∀ i j : Fin n,
      ∑ k : Fin n,
          |higham9_2_rectRoundedLoopL fp (Nat.le_refl n) A i k| *
            |higham9_2_rectRoundedLoopU fp (Nat.le_refl n) A k j| ≤
        |A i j|) :
    let L_hat := higham9_2_rectRoundedLoopL fp (Nat.le_refl n) A
    let U_hat := higham9_2_rectRoundedLoopU fp (Nat.le_refl n) A
    let y_hat := fl_forwardSub fp n L_hat b
    let x_hat := fl_backSub fp n U_hat y_hat
    ∃ DeltaA : Fin n → Fin n → ℝ,
      (∀ i j, |DeltaA i j| ≤
        higham9_14_h (gamma fp n) * |A i j|) ∧
      (∀ i, ∑ j : Fin n, (A i j + DeltaA i j) * x_hat j = b i) := by
  dsimp only
  exact
    higham9_14_source_h_bound_of_rectRoundedLoop_square_fl_triangular_solves_gamma_le
      fp n A b (gamma fp n) (gamma_nonneg fp hn) hγ_lt_one
      hn hU_diag hU_budget_le hL_budget_le le_rfl hAbsLU_le

/-- **Theorem 9.14**, executable rectangular rounded loop source `h(u)` bound
with optimal growth `|Lhat||Uhat| <= |A|`. -/
theorem higham9_14_source_h_bound_of_rectRoundedLoop_square_fl_triangular_solves_absLU_le_absA_gamma_le
    (fp : FPModel) (n : ℕ)
    (A : Fin n → Fin n → ℝ)
    (b : Fin n → ℝ)
    (u : ℝ) (hu : 0 ≤ u) (hu_lt_one : u < 1)
    (hn : gammaValid fp n)
    (hU_diag : ∀ k : Fin n,
      higham9_2_rectRoundedLoopU fp (Nat.le_refl n) A k k ≠ 0)
    (hU_budget_le : ∀ k j : Fin n, k.val ≤ j.val →
      higham9_2_rectDoolittleUAbsBudget fp (Nat.le_refl n) A
          (higham9_2_rectRoundedLoopL fp (Nat.le_refl n) A)
          (higham9_2_rectRoundedLoopU fp (Nat.le_refl n) A) k j ≤
        gamma fp n *
          |higham9_2_rectRoundedLoopU fp (Nat.le_refl n) A k j|)
    (hL_budget_le : ∀ i k : Fin n, k.val < i.val →
      higham9_2_rectDoolittleLAbsBudget fp A
          (higham9_2_rectRoundedLoopL fp (Nat.le_refl n) A)
          (higham9_2_rectRoundedLoopU fp (Nat.le_refl n) A) i k ≤
        gamma fp n *
          |higham9_2_rectRoundedLoopL fp (Nat.le_refl n) A i k *
            higham9_2_rectRoundedLoopU fp (Nat.le_refl n) A k k|)
    (hγ_le_u : gamma fp n ≤ u)
    (hAbsLU_le : ∀ i j : Fin n,
      ∑ k : Fin n,
          |higham9_2_rectRoundedLoopL fp (Nat.le_refl n) A i k| *
            |higham9_2_rectRoundedLoopU fp (Nat.le_refl n) A k j| ≤
        |A i j|) :
    let L_hat := higham9_2_rectRoundedLoopL fp (Nat.le_refl n) A
    let U_hat := higham9_2_rectRoundedLoopU fp (Nat.le_refl n) A
    let y_hat := fl_forwardSub fp n L_hat b
    let x_hat := fl_backSub fp n U_hat y_hat
    ∃ DeltaA : Fin n → Fin n → ℝ,
      (∀ i j, |DeltaA i j| ≤ higham9_14_h u * |A i j|) ∧
      (∀ i, ∑ j : Fin n, (A i j + DeltaA i j) * x_hat j = b i) :=
  higham9_14_source_h_bound_of_rectRoundedLoop_square_fl_triangular_solves_gamma_le
    fp n A b u hu hu_lt_one hn hU_diag hU_budget_le hL_budget_le
    hγ_le_u hAbsLU_le

/-- **Theorem 9.14**, executable rectangular rounded loop source `h(γ_n)`
bound with optimal growth `|Lhat||Uhat| <= |A|`. -/
theorem higham9_14_source_h_bound_of_rectRoundedLoop_square_fl_triangular_solves_absLU_le_absA_gamma
    (fp : FPModel) (n : ℕ)
    (A : Fin n → Fin n → ℝ)
    (b : Fin n → ℝ)
    (hn : gammaValid fp n)
    (hγ_lt_one : gamma fp n < 1)
    (hU_diag : ∀ k : Fin n,
      higham9_2_rectRoundedLoopU fp (Nat.le_refl n) A k k ≠ 0)
    (hU_budget_le : ∀ k j : Fin n, k.val ≤ j.val →
      higham9_2_rectDoolittleUAbsBudget fp (Nat.le_refl n) A
          (higham9_2_rectRoundedLoopL fp (Nat.le_refl n) A)
          (higham9_2_rectRoundedLoopU fp (Nat.le_refl n) A) k j ≤
        gamma fp n *
          |higham9_2_rectRoundedLoopU fp (Nat.le_refl n) A k j|)
    (hL_budget_le : ∀ i k : Fin n, k.val < i.val →
      higham9_2_rectDoolittleLAbsBudget fp A
          (higham9_2_rectRoundedLoopL fp (Nat.le_refl n) A)
          (higham9_2_rectRoundedLoopU fp (Nat.le_refl n) A) i k ≤
        gamma fp n *
          |higham9_2_rectRoundedLoopL fp (Nat.le_refl n) A i k *
            higham9_2_rectRoundedLoopU fp (Nat.le_refl n) A k k|)
    (hAbsLU_le : ∀ i j : Fin n,
      ∑ k : Fin n,
          |higham9_2_rectRoundedLoopL fp (Nat.le_refl n) A i k| *
            |higham9_2_rectRoundedLoopU fp (Nat.le_refl n) A k j| ≤
        |A i j|) :
    let L_hat := higham9_2_rectRoundedLoopL fp (Nat.le_refl n) A
    let U_hat := higham9_2_rectRoundedLoopU fp (Nat.le_refl n) A
    let y_hat := fl_forwardSub fp n L_hat b
    let x_hat := fl_backSub fp n U_hat y_hat
    ∃ DeltaA : Fin n → Fin n → ℝ,
      (∀ i j, |DeltaA i j| ≤
        higham9_14_h (gamma fp n) * |A i j|) ∧
      (∀ i, ∑ j : Fin n, (A i j + DeltaA i j) * x_hat j = b i) :=
  higham9_14_source_h_bound_of_rectRoundedLoop_square_fl_triangular_solves_gamma
    fp n A b hn hγ_lt_one hU_diag hU_budget_le hL_budget_le hAbsLU_le

/-- **Theorem 9.14**, executable rectangular rounded loop source `h(u)` bound
with a supplied constant-growth comparison. -/
theorem higham9_14_source_h_bound_of_rectRoundedLoop_square_fl_triangular_solves_const_gamma_le
    (fp : FPModel) (n : ℕ)
    (A : Fin n → Fin n → ℝ)
    (b : Fin n → ℝ)
    (c u : ℝ) (hc : 0 ≤ c) (hu : 0 ≤ u) (hu_lt_one : u < 1)
    (hn : gammaValid fp n)
    (hU_diag : ∀ k : Fin n,
      higham9_2_rectRoundedLoopU fp (Nat.le_refl n) A k k ≠ 0)
    (hU_budget_le : ∀ k j : Fin n, k.val ≤ j.val →
      higham9_2_rectDoolittleUAbsBudget fp (Nat.le_refl n) A
          (higham9_2_rectRoundedLoopL fp (Nat.le_refl n) A)
          (higham9_2_rectRoundedLoopU fp (Nat.le_refl n) A) k j ≤
        gamma fp n *
          |higham9_2_rectRoundedLoopU fp (Nat.le_refl n) A k j|)
    (hL_budget_le : ∀ i k : Fin n, k.val < i.val →
      higham9_2_rectDoolittleLAbsBudget fp A
          (higham9_2_rectRoundedLoopL fp (Nat.le_refl n) A)
          (higham9_2_rectRoundedLoopU fp (Nat.le_refl n) A) i k ≤
        gamma fp n *
          |higham9_2_rectRoundedLoopL fp (Nat.le_refl n) A i k *
            higham9_2_rectRoundedLoopU fp (Nat.le_refl n) A k k|)
    (hγ_le_u : gamma fp n ≤ u)
    (hAbsLU_le : ∀ i j : Fin n,
      ∑ k : Fin n,
          |higham9_2_rectRoundedLoopL fp (Nat.le_refl n) A i k| *
            |higham9_2_rectRoundedLoopU fp (Nat.le_refl n) A k j| ≤
        c * |A i j|) :
    let L_hat := higham9_2_rectRoundedLoopL fp (Nat.le_refl n) A
    let U_hat := higham9_2_rectRoundedLoopU fp (Nat.le_refl n) A
    let y_hat := fl_forwardSub fp n L_hat b
    let x_hat := fl_backSub fp n U_hat y_hat
    ∃ DeltaA : Fin n → Fin n → ℝ,
      (∀ i j, |DeltaA i j| ≤ c * higham9_14_h u * |A i j|) ∧
      (∀ i, ∑ j : Fin n, (A i j + DeltaA i j) * x_hat j = b i) := by
  dsimp only
  exact
    higham9_14_source_h_bound_of_RectDoolittleDenseLoopAbsBudgetCertificate_square_fl_triangular_solves_const_gamma_le
      fp n A
      (higham9_2_rectRoundedLoopL fp (Nat.le_refl n) A)
      (higham9_2_rectRoundedLoopU fp (Nat.le_refl n) A)
      b
      (higham9_2_rectDoolittleUAbsBudget fp (Nat.le_refl n) A
        (higham9_2_rectRoundedLoopL fp (Nat.le_refl n) A)
        (higham9_2_rectRoundedLoopU fp (Nat.le_refl n) A))
      (higham9_2_rectDoolittleLAbsBudget fp A
        (higham9_2_rectRoundedLoopL fp (Nat.le_refl n) A)
        (higham9_2_rectRoundedLoopU fp (Nat.le_refl n) A))
      c u hc hu hu_lt_one hn
      (higham9_2_rectRoundedLoop_to_rectAbsBudgetCertificate fp
        (Nat.le_refl n) A hU_diag hn hU_budget_le hL_budget_le)
      hγ_le_u hU_diag hAbsLU_le

/-- **Theorem 9.14**, executable rectangular rounded loop source `h(γ_n)`
bound with a supplied constant-growth comparison. -/
theorem higham9_14_source_h_bound_of_rectRoundedLoop_square_fl_triangular_solves_const_gamma
    (fp : FPModel) (n : ℕ)
    (A : Fin n → Fin n → ℝ)
    (b : Fin n → ℝ)
    (c : ℝ) (hc : 0 ≤ c)
    (hn : gammaValid fp n)
    (hγ_lt_one : gamma fp n < 1)
    (hU_diag : ∀ k : Fin n,
      higham9_2_rectRoundedLoopU fp (Nat.le_refl n) A k k ≠ 0)
    (hU_budget_le : ∀ k j : Fin n, k.val ≤ j.val →
      higham9_2_rectDoolittleUAbsBudget fp (Nat.le_refl n) A
          (higham9_2_rectRoundedLoopL fp (Nat.le_refl n) A)
          (higham9_2_rectRoundedLoopU fp (Nat.le_refl n) A) k j ≤
        gamma fp n *
          |higham9_2_rectRoundedLoopU fp (Nat.le_refl n) A k j|)
    (hL_budget_le : ∀ i k : Fin n, k.val < i.val →
      higham9_2_rectDoolittleLAbsBudget fp A
          (higham9_2_rectRoundedLoopL fp (Nat.le_refl n) A)
          (higham9_2_rectRoundedLoopU fp (Nat.le_refl n) A) i k ≤
        gamma fp n *
          |higham9_2_rectRoundedLoopL fp (Nat.le_refl n) A i k *
            higham9_2_rectRoundedLoopU fp (Nat.le_refl n) A k k|)
    (hAbsLU_le : ∀ i j : Fin n,
      ∑ k : Fin n,
          |higham9_2_rectRoundedLoopL fp (Nat.le_refl n) A i k| *
            |higham9_2_rectRoundedLoopU fp (Nat.le_refl n) A k j| ≤
        c * |A i j|) :
    let L_hat := higham9_2_rectRoundedLoopL fp (Nat.le_refl n) A
    let U_hat := higham9_2_rectRoundedLoopU fp (Nat.le_refl n) A
    let y_hat := fl_forwardSub fp n L_hat b
    let x_hat := fl_backSub fp n U_hat y_hat
    ∃ DeltaA : Fin n → Fin n → ℝ,
      (∀ i j, |DeltaA i j| ≤
        c * higham9_14_h (gamma fp n) * |A i j|) ∧
      (∀ i, ∑ j : Fin n, (A i j + DeltaA i j) * x_hat j = b i) := by
  dsimp only
  exact
    higham9_14_source_h_bound_of_rectRoundedLoop_square_fl_triangular_solves_const_gamma_le
      fp n A b c (gamma fp n) hc (gamma_nonneg fp hn)
      hγ_lt_one hn hU_diag hU_budget_le hL_budget_le le_rfl hAbsLU_le

/-- **Theorem 9.14**, Matrix-facing executable rectangular rounded loop
source `f(u)` bound. -/
theorem higham9_14_matrix_source_f_bound_of_rectRoundedLoop_square_fl_triangular_solves_gamma_le
    (fp : FPModel) (n : ℕ)
    (A : Matrix (Fin n) (Fin n) ℝ)
    (b : Fin n → ℝ)
    (c u : ℝ) (hu : 0 ≤ u)
    (hn : gammaValid fp n)
    (hU_diag : ∀ k : Fin n,
      higham9_2_rectRoundedLoopU fp (Nat.le_refl n) A k k ≠ 0)
    (hU_budget_le : ∀ k j : Fin n, k.val ≤ j.val →
      higham9_2_rectDoolittleUAbsBudget fp (Nat.le_refl n) A
          (higham9_2_rectRoundedLoopL fp (Nat.le_refl n) A)
          (higham9_2_rectRoundedLoopU fp (Nat.le_refl n) A) k j ≤
        gamma fp n *
          |higham9_2_rectRoundedLoopU fp (Nat.le_refl n) A k j|)
    (hL_budget_le : ∀ i k : Fin n, k.val < i.val →
      higham9_2_rectDoolittleLAbsBudget fp A
          (higham9_2_rectRoundedLoopL fp (Nat.le_refl n) A)
          (higham9_2_rectRoundedLoopU fp (Nat.le_refl n) A) i k ≤
        gamma fp n *
          |higham9_2_rectRoundedLoopL fp (Nat.le_refl n) A i k *
            higham9_2_rectRoundedLoopU fp (Nat.le_refl n) A k k|)
    (hγ_le_u : gamma fp n ≤ u)
    (hAbsLU_le : ∀ i j : Fin n,
      ∑ k : Fin n,
          |higham9_2_rectRoundedLoopL fp (Nat.le_refl n) A i k| *
            |higham9_2_rectRoundedLoopU fp (Nat.le_refl n) A k j| ≤
        c * |A i j|) :
    let L_hat := higham9_2_rectRoundedLoopL fp (Nat.le_refl n) A
    let U_hat := higham9_2_rectRoundedLoopU fp (Nat.le_refl n) A
    let y_hat := fl_forwardSub fp n L_hat b
    let x_hat := fl_backSub fp n U_hat y_hat
    ∃ DeltaA : Matrix (Fin n) (Fin n) ℝ,
      (∀ i j, |DeltaA i j| ≤ c * higham9_14_f u * |A i j|) ∧
      Matrix.mulVec (fun i j => A i j + DeltaA i j) x_hat = b := by
  dsimp only
  exact
    higham9_14_matrix_source_f_bound_of_RectDoolittleDenseLoopAbsBudgetCertificate_square_fl_triangular_solves_gamma_le
      fp n A
      (higham9_2_rectRoundedLoopL fp (Nat.le_refl n) A)
      (higham9_2_rectRoundedLoopU fp (Nat.le_refl n) A)
      b
      (higham9_2_rectDoolittleUAbsBudget fp (Nat.le_refl n) A
        (higham9_2_rectRoundedLoopL fp (Nat.le_refl n) A)
        (higham9_2_rectRoundedLoopU fp (Nat.le_refl n) A))
      (higham9_2_rectDoolittleLAbsBudget fp A
        (higham9_2_rectRoundedLoopL fp (Nat.le_refl n) A)
        (higham9_2_rectRoundedLoopU fp (Nat.le_refl n) A))
      c u hu hn
      (higham9_2_rectRoundedLoop_to_rectAbsBudgetCertificate fp
        (Nat.le_refl n) A hU_diag hn hU_budget_le hL_budget_le)
      hγ_le_u hU_diag hAbsLU_le

/-- **Theorem 9.14**, Matrix-facing executable rectangular rounded loop
source `f(γ_n)` bound. -/
theorem higham9_14_matrix_source_f_bound_of_rectRoundedLoop_square_fl_triangular_solves_gamma
    (fp : FPModel) (n : ℕ)
    (A : Matrix (Fin n) (Fin n) ℝ)
    (b : Fin n → ℝ)
    (c : ℝ)
    (hn : gammaValid fp n)
    (hU_diag : ∀ k : Fin n,
      higham9_2_rectRoundedLoopU fp (Nat.le_refl n) A k k ≠ 0)
    (hU_budget_le : ∀ k j : Fin n, k.val ≤ j.val →
      higham9_2_rectDoolittleUAbsBudget fp (Nat.le_refl n) A
          (higham9_2_rectRoundedLoopL fp (Nat.le_refl n) A)
          (higham9_2_rectRoundedLoopU fp (Nat.le_refl n) A) k j ≤
        gamma fp n *
          |higham9_2_rectRoundedLoopU fp (Nat.le_refl n) A k j|)
    (hL_budget_le : ∀ i k : Fin n, k.val < i.val →
      higham9_2_rectDoolittleLAbsBudget fp A
          (higham9_2_rectRoundedLoopL fp (Nat.le_refl n) A)
          (higham9_2_rectRoundedLoopU fp (Nat.le_refl n) A) i k ≤
        gamma fp n *
          |higham9_2_rectRoundedLoopL fp (Nat.le_refl n) A i k *
            higham9_2_rectRoundedLoopU fp (Nat.le_refl n) A k k|)
    (hAbsLU_le : ∀ i j : Fin n,
      ∑ k : Fin n,
          |higham9_2_rectRoundedLoopL fp (Nat.le_refl n) A i k| *
            |higham9_2_rectRoundedLoopU fp (Nat.le_refl n) A k j| ≤
        c * |A i j|) :
    let L_hat := higham9_2_rectRoundedLoopL fp (Nat.le_refl n) A
    let U_hat := higham9_2_rectRoundedLoopU fp (Nat.le_refl n) A
    let y_hat := fl_forwardSub fp n L_hat b
    let x_hat := fl_backSub fp n U_hat y_hat
    ∃ DeltaA : Matrix (Fin n) (Fin n) ℝ,
      (∀ i j, |DeltaA i j| ≤
        c * higham9_14_f (gamma fp n) * |A i j|) ∧
      Matrix.mulVec (fun i j => A i j + DeltaA i j) x_hat = b := by
  dsimp only
  exact
    higham9_14_matrix_source_f_bound_of_rectRoundedLoop_square_fl_triangular_solves_gamma_le
      fp n A b c (gamma fp n) (gamma_nonneg fp hn)
      hn hU_diag hU_budget_le hL_budget_le le_rfl hAbsLU_le

/-- **Theorem 9.14**, Matrix-facing executable rectangular rounded loop
source `f(u)` bound with optimal growth `|Lhat||Uhat| <= |A|`. -/
theorem higham9_14_matrix_source_f_bound_of_rectRoundedLoop_square_fl_triangular_solves_absLU_le_absA_gamma_le
    (fp : FPModel) (n : ℕ)
    (A : Matrix (Fin n) (Fin n) ℝ)
    (b : Fin n → ℝ)
    (u : ℝ) (hu : 0 ≤ u)
    (hn : gammaValid fp n)
    (hU_diag : ∀ k : Fin n,
      higham9_2_rectRoundedLoopU fp (Nat.le_refl n) A k k ≠ 0)
    (hU_budget_le : ∀ k j : Fin n, k.val ≤ j.val →
      higham9_2_rectDoolittleUAbsBudget fp (Nat.le_refl n) A
          (higham9_2_rectRoundedLoopL fp (Nat.le_refl n) A)
          (higham9_2_rectRoundedLoopU fp (Nat.le_refl n) A) k j ≤
        gamma fp n *
          |higham9_2_rectRoundedLoopU fp (Nat.le_refl n) A k j|)
    (hL_budget_le : ∀ i k : Fin n, k.val < i.val →
      higham9_2_rectDoolittleLAbsBudget fp A
          (higham9_2_rectRoundedLoopL fp (Nat.le_refl n) A)
          (higham9_2_rectRoundedLoopU fp (Nat.le_refl n) A) i k ≤
        gamma fp n *
          |higham9_2_rectRoundedLoopL fp (Nat.le_refl n) A i k *
            higham9_2_rectRoundedLoopU fp (Nat.le_refl n) A k k|)
    (hγ_le_u : gamma fp n ≤ u)
    (hAbsLU_le : ∀ i j : Fin n,
      ∑ k : Fin n,
          |higham9_2_rectRoundedLoopL fp (Nat.le_refl n) A i k| *
            |higham9_2_rectRoundedLoopU fp (Nat.le_refl n) A k j| ≤
        |A i j|) :
    let L_hat := higham9_2_rectRoundedLoopL fp (Nat.le_refl n) A
    let U_hat := higham9_2_rectRoundedLoopU fp (Nat.le_refl n) A
    let y_hat := fl_forwardSub fp n L_hat b
    let x_hat := fl_backSub fp n U_hat y_hat
    ∃ DeltaA : Matrix (Fin n) (Fin n) ℝ,
      (∀ i j, |DeltaA i j| ≤ higham9_14_f u * |A i j|) ∧
      Matrix.mulVec (fun i j => A i j + DeltaA i j) x_hat = b := by
  simpa [one_mul] using
    (higham9_14_matrix_source_f_bound_of_rectRoundedLoop_square_fl_triangular_solves_gamma_le
      fp n A b 1 u hu hn hU_diag hU_budget_le hL_budget_le hγ_le_u
      (fun i j => by simpa [one_mul] using hAbsLU_le i j))

/-- **Theorem 9.14**, Matrix-facing executable rectangular rounded loop
source `f(γ_n)` bound with optimal growth `|Lhat||Uhat| <= |A|`. -/
theorem higham9_14_matrix_source_f_bound_of_rectRoundedLoop_square_fl_triangular_solves_absLU_le_absA_gamma
    (fp : FPModel) (n : ℕ)
    (A : Matrix (Fin n) (Fin n) ℝ)
    (b : Fin n → ℝ)
    (hn : gammaValid fp n)
    (hU_diag : ∀ k : Fin n,
      higham9_2_rectRoundedLoopU fp (Nat.le_refl n) A k k ≠ 0)
    (hU_budget_le : ∀ k j : Fin n, k.val ≤ j.val →
      higham9_2_rectDoolittleUAbsBudget fp (Nat.le_refl n) A
          (higham9_2_rectRoundedLoopL fp (Nat.le_refl n) A)
          (higham9_2_rectRoundedLoopU fp (Nat.le_refl n) A) k j ≤
        gamma fp n *
          |higham9_2_rectRoundedLoopU fp (Nat.le_refl n) A k j|)
    (hL_budget_le : ∀ i k : Fin n, k.val < i.val →
      higham9_2_rectDoolittleLAbsBudget fp A
          (higham9_2_rectRoundedLoopL fp (Nat.le_refl n) A)
          (higham9_2_rectRoundedLoopU fp (Nat.le_refl n) A) i k ≤
        gamma fp n *
          |higham9_2_rectRoundedLoopL fp (Nat.le_refl n) A i k *
            higham9_2_rectRoundedLoopU fp (Nat.le_refl n) A k k|)
    (hAbsLU_le : ∀ i j : Fin n,
      ∑ k : Fin n,
          |higham9_2_rectRoundedLoopL fp (Nat.le_refl n) A i k| *
            |higham9_2_rectRoundedLoopU fp (Nat.le_refl n) A k j| ≤
        |A i j|) :
    let L_hat := higham9_2_rectRoundedLoopL fp (Nat.le_refl n) A
    let U_hat := higham9_2_rectRoundedLoopU fp (Nat.le_refl n) A
    let y_hat := fl_forwardSub fp n L_hat b
    let x_hat := fl_backSub fp n U_hat y_hat
    ∃ DeltaA : Matrix (Fin n) (Fin n) ℝ,
      (∀ i j, |DeltaA i j| ≤
        higham9_14_f (gamma fp n) * |A i j|) ∧
      Matrix.mulVec (fun i j => A i j + DeltaA i j) x_hat = b := by
  simpa [one_mul] using
    (higham9_14_matrix_source_f_bound_of_rectRoundedLoop_square_fl_triangular_solves_gamma
      fp n A b 1 hn hU_diag hU_budget_le hL_budget_le
      (fun i j => by simpa [one_mul] using hAbsLU_le i j))

/-- **Theorem 9.14**, Matrix-facing executable rectangular rounded loop
`h(u)` bound with the exact-growth comparison `|Lhat||Uhat| <= |A|`. -/
theorem higham9_14_matrix_source_h_bound_of_rectRoundedLoop_square_fl_triangular_solves_gamma_le
    (fp : FPModel) (n : ℕ)
    (A : Matrix (Fin n) (Fin n) ℝ)
    (b : Fin n → ℝ)
    (u : ℝ) (hu : 0 ≤ u) (hu_lt_one : u < 1)
    (hn : gammaValid fp n)
    (hU_diag : ∀ k : Fin n,
      higham9_2_rectRoundedLoopU fp (Nat.le_refl n) A k k ≠ 0)
    (hU_budget_le : ∀ k j : Fin n, k.val ≤ j.val →
      higham9_2_rectDoolittleUAbsBudget fp (Nat.le_refl n) A
          (higham9_2_rectRoundedLoopL fp (Nat.le_refl n) A)
          (higham9_2_rectRoundedLoopU fp (Nat.le_refl n) A) k j ≤
        gamma fp n *
          |higham9_2_rectRoundedLoopU fp (Nat.le_refl n) A k j|)
    (hL_budget_le : ∀ i k : Fin n, k.val < i.val →
      higham9_2_rectDoolittleLAbsBudget fp A
          (higham9_2_rectRoundedLoopL fp (Nat.le_refl n) A)
          (higham9_2_rectRoundedLoopU fp (Nat.le_refl n) A) i k ≤
        gamma fp n *
          |higham9_2_rectRoundedLoopL fp (Nat.le_refl n) A i k *
            higham9_2_rectRoundedLoopU fp (Nat.le_refl n) A k k|)
    (hγ_le_u : gamma fp n ≤ u)
    (hAbsLU_le : ∀ i j : Fin n,
      ∑ k : Fin n,
          |higham9_2_rectRoundedLoopL fp (Nat.le_refl n) A i k| *
            |higham9_2_rectRoundedLoopU fp (Nat.le_refl n) A k j| ≤
        |A i j|) :
    let L_hat := higham9_2_rectRoundedLoopL fp (Nat.le_refl n) A
    let U_hat := higham9_2_rectRoundedLoopU fp (Nat.le_refl n) A
    let y_hat := fl_forwardSub fp n L_hat b
    let x_hat := fl_backSub fp n U_hat y_hat
    ∃ DeltaA : Matrix (Fin n) (Fin n) ℝ,
      (∀ i j, |DeltaA i j| ≤ higham9_14_h u * |A i j|) ∧
      Matrix.mulVec (fun i j => A i j + DeltaA i j) x_hat = b := by
  dsimp only
  exact
    higham9_14_matrix_source_h_bound_of_RectDoolittleDenseLoopAbsBudgetCertificate_square_fl_triangular_solves_gamma_le
      fp n A
      (higham9_2_rectRoundedLoopL fp (Nat.le_refl n) A)
      (higham9_2_rectRoundedLoopU fp (Nat.le_refl n) A)
      b
      (higham9_2_rectDoolittleUAbsBudget fp (Nat.le_refl n) A
        (higham9_2_rectRoundedLoopL fp (Nat.le_refl n) A)
        (higham9_2_rectRoundedLoopU fp (Nat.le_refl n) A))
      (higham9_2_rectDoolittleLAbsBudget fp A
        (higham9_2_rectRoundedLoopL fp (Nat.le_refl n) A)
        (higham9_2_rectRoundedLoopU fp (Nat.le_refl n) A))
      u hu hu_lt_one hn
      (higham9_2_rectRoundedLoop_to_rectAbsBudgetCertificate fp
        (Nat.le_refl n) A hU_diag hn hU_budget_le hL_budget_le)
      hγ_le_u hU_diag hAbsLU_le

/-- **Theorem 9.14**, Matrix-facing executable rectangular rounded loop
`h(γ_n)` bound with the exact-growth comparison `|Lhat||Uhat| <= |A|`. -/
theorem higham9_14_matrix_source_h_bound_of_rectRoundedLoop_square_fl_triangular_solves_gamma
    (fp : FPModel) (n : ℕ)
    (A : Matrix (Fin n) (Fin n) ℝ)
    (b : Fin n → ℝ)
    (hn : gammaValid fp n)
    (hγ_lt_one : gamma fp n < 1)
    (hU_diag : ∀ k : Fin n,
      higham9_2_rectRoundedLoopU fp (Nat.le_refl n) A k k ≠ 0)
    (hU_budget_le : ∀ k j : Fin n, k.val ≤ j.val →
      higham9_2_rectDoolittleUAbsBudget fp (Nat.le_refl n) A
          (higham9_2_rectRoundedLoopL fp (Nat.le_refl n) A)
          (higham9_2_rectRoundedLoopU fp (Nat.le_refl n) A) k j ≤
        gamma fp n *
          |higham9_2_rectRoundedLoopU fp (Nat.le_refl n) A k j|)
    (hL_budget_le : ∀ i k : Fin n, k.val < i.val →
      higham9_2_rectDoolittleLAbsBudget fp A
          (higham9_2_rectRoundedLoopL fp (Nat.le_refl n) A)
          (higham9_2_rectRoundedLoopU fp (Nat.le_refl n) A) i k ≤
        gamma fp n *
          |higham9_2_rectRoundedLoopL fp (Nat.le_refl n) A i k *
            higham9_2_rectRoundedLoopU fp (Nat.le_refl n) A k k|)
    (hAbsLU_le : ∀ i j : Fin n,
      ∑ k : Fin n,
          |higham9_2_rectRoundedLoopL fp (Nat.le_refl n) A i k| *
            |higham9_2_rectRoundedLoopU fp (Nat.le_refl n) A k j| ≤
        |A i j|) :
    let L_hat := higham9_2_rectRoundedLoopL fp (Nat.le_refl n) A
    let U_hat := higham9_2_rectRoundedLoopU fp (Nat.le_refl n) A
    let y_hat := fl_forwardSub fp n L_hat b
    let x_hat := fl_backSub fp n U_hat y_hat
    ∃ DeltaA : Matrix (Fin n) (Fin n) ℝ,
      (∀ i j, |DeltaA i j| ≤
        higham9_14_h (gamma fp n) * |A i j|) ∧
      Matrix.mulVec (fun i j => A i j + DeltaA i j) x_hat = b := by
  dsimp only
  exact
    higham9_14_matrix_source_h_bound_of_rectRoundedLoop_square_fl_triangular_solves_gamma_le
      fp n A b (gamma fp n) (gamma_nonneg fp hn) hγ_lt_one
      hn hU_diag hU_budget_le hL_budget_le le_rfl hAbsLU_le

/-- **Theorem 9.14**, Matrix-facing executable rectangular rounded loop
`h(u)` bound with optimal growth `|Lhat||Uhat| <= |A|`. -/
theorem higham9_14_matrix_source_h_bound_of_rectRoundedLoop_square_fl_triangular_solves_absLU_le_absA_gamma_le
    (fp : FPModel) (n : ℕ)
    (A : Matrix (Fin n) (Fin n) ℝ)
    (b : Fin n → ℝ)
    (u : ℝ) (hu : 0 ≤ u) (hu_lt_one : u < 1)
    (hn : gammaValid fp n)
    (hU_diag : ∀ k : Fin n,
      higham9_2_rectRoundedLoopU fp (Nat.le_refl n) A k k ≠ 0)
    (hU_budget_le : ∀ k j : Fin n, k.val ≤ j.val →
      higham9_2_rectDoolittleUAbsBudget fp (Nat.le_refl n) A
          (higham9_2_rectRoundedLoopL fp (Nat.le_refl n) A)
          (higham9_2_rectRoundedLoopU fp (Nat.le_refl n) A) k j ≤
        gamma fp n *
          |higham9_2_rectRoundedLoopU fp (Nat.le_refl n) A k j|)
    (hL_budget_le : ∀ i k : Fin n, k.val < i.val →
      higham9_2_rectDoolittleLAbsBudget fp A
          (higham9_2_rectRoundedLoopL fp (Nat.le_refl n) A)
          (higham9_2_rectRoundedLoopU fp (Nat.le_refl n) A) i k ≤
        gamma fp n *
          |higham9_2_rectRoundedLoopL fp (Nat.le_refl n) A i k *
            higham9_2_rectRoundedLoopU fp (Nat.le_refl n) A k k|)
    (hγ_le_u : gamma fp n ≤ u)
    (hAbsLU_le : ∀ i j : Fin n,
      ∑ k : Fin n,
          |higham9_2_rectRoundedLoopL fp (Nat.le_refl n) A i k| *
            |higham9_2_rectRoundedLoopU fp (Nat.le_refl n) A k j| ≤
        |A i j|) :
    let L_hat := higham9_2_rectRoundedLoopL fp (Nat.le_refl n) A
    let U_hat := higham9_2_rectRoundedLoopU fp (Nat.le_refl n) A
    let y_hat := fl_forwardSub fp n L_hat b
    let x_hat := fl_backSub fp n U_hat y_hat
    ∃ DeltaA : Matrix (Fin n) (Fin n) ℝ,
      (∀ i j, |DeltaA i j| ≤ higham9_14_h u * |A i j|) ∧
      Matrix.mulVec (fun i j => A i j + DeltaA i j) x_hat = b :=
  higham9_14_matrix_source_h_bound_of_rectRoundedLoop_square_fl_triangular_solves_gamma_le
    fp n A b u hu hu_lt_one hn hU_diag hU_budget_le hL_budget_le
    hγ_le_u hAbsLU_le

/-- **Theorem 9.14**, Matrix-facing executable rectangular rounded loop
`h(γ_n)` bound with optimal growth `|Lhat||Uhat| <= |A|`. -/
theorem higham9_14_matrix_source_h_bound_of_rectRoundedLoop_square_fl_triangular_solves_absLU_le_absA_gamma
    (fp : FPModel) (n : ℕ)
    (A : Matrix (Fin n) (Fin n) ℝ)
    (b : Fin n → ℝ)
    (hn : gammaValid fp n)
    (hγ_lt_one : gamma fp n < 1)
    (hU_diag : ∀ k : Fin n,
      higham9_2_rectRoundedLoopU fp (Nat.le_refl n) A k k ≠ 0)
    (hU_budget_le : ∀ k j : Fin n, k.val ≤ j.val →
      higham9_2_rectDoolittleUAbsBudget fp (Nat.le_refl n) A
          (higham9_2_rectRoundedLoopL fp (Nat.le_refl n) A)
          (higham9_2_rectRoundedLoopU fp (Nat.le_refl n) A) k j ≤
        gamma fp n *
          |higham9_2_rectRoundedLoopU fp (Nat.le_refl n) A k j|)
    (hL_budget_le : ∀ i k : Fin n, k.val < i.val →
      higham9_2_rectDoolittleLAbsBudget fp A
          (higham9_2_rectRoundedLoopL fp (Nat.le_refl n) A)
          (higham9_2_rectRoundedLoopU fp (Nat.le_refl n) A) i k ≤
        gamma fp n *
          |higham9_2_rectRoundedLoopL fp (Nat.le_refl n) A i k *
            higham9_2_rectRoundedLoopU fp (Nat.le_refl n) A k k|)
    (hAbsLU_le : ∀ i j : Fin n,
      ∑ k : Fin n,
          |higham9_2_rectRoundedLoopL fp (Nat.le_refl n) A i k| *
            |higham9_2_rectRoundedLoopU fp (Nat.le_refl n) A k j| ≤
        |A i j|) :
    let L_hat := higham9_2_rectRoundedLoopL fp (Nat.le_refl n) A
    let U_hat := higham9_2_rectRoundedLoopU fp (Nat.le_refl n) A
    let y_hat := fl_forwardSub fp n L_hat b
    let x_hat := fl_backSub fp n U_hat y_hat
    ∃ DeltaA : Matrix (Fin n) (Fin n) ℝ,
      (∀ i j, |DeltaA i j| ≤
        higham9_14_h (gamma fp n) * |A i j|) ∧
      Matrix.mulVec (fun i j => A i j + DeltaA i j) x_hat = b :=
  higham9_14_matrix_source_h_bound_of_rectRoundedLoop_square_fl_triangular_solves_gamma
    fp n A b hn hγ_lt_one hU_diag hU_budget_le hL_budget_le hAbsLU_le

/-- **Theorem 9.14**, Matrix-facing executable rectangular rounded loop
`h(u)` bound with a supplied constant-growth comparison. -/
theorem higham9_14_matrix_source_h_bound_of_rectRoundedLoop_square_fl_triangular_solves_const_gamma_le
    (fp : FPModel) (n : ℕ)
    (A : Matrix (Fin n) (Fin n) ℝ)
    (b : Fin n → ℝ)
    (c u : ℝ) (hc : 0 ≤ c) (hu : 0 ≤ u) (hu_lt_one : u < 1)
    (hn : gammaValid fp n)
    (hU_diag : ∀ k : Fin n,
      higham9_2_rectRoundedLoopU fp (Nat.le_refl n) A k k ≠ 0)
    (hU_budget_le : ∀ k j : Fin n, k.val ≤ j.val →
      higham9_2_rectDoolittleUAbsBudget fp (Nat.le_refl n) A
          (higham9_2_rectRoundedLoopL fp (Nat.le_refl n) A)
          (higham9_2_rectRoundedLoopU fp (Nat.le_refl n) A) k j ≤
        gamma fp n *
          |higham9_2_rectRoundedLoopU fp (Nat.le_refl n) A k j|)
    (hL_budget_le : ∀ i k : Fin n, k.val < i.val →
      higham9_2_rectDoolittleLAbsBudget fp A
          (higham9_2_rectRoundedLoopL fp (Nat.le_refl n) A)
          (higham9_2_rectRoundedLoopU fp (Nat.le_refl n) A) i k ≤
        gamma fp n *
          |higham9_2_rectRoundedLoopL fp (Nat.le_refl n) A i k *
            higham9_2_rectRoundedLoopU fp (Nat.le_refl n) A k k|)
    (hγ_le_u : gamma fp n ≤ u)
    (hAbsLU_le : ∀ i j : Fin n,
      ∑ k : Fin n,
          |higham9_2_rectRoundedLoopL fp (Nat.le_refl n) A i k| *
            |higham9_2_rectRoundedLoopU fp (Nat.le_refl n) A k j| ≤
        c * |A i j|) :
    let L_hat := higham9_2_rectRoundedLoopL fp (Nat.le_refl n) A
    let U_hat := higham9_2_rectRoundedLoopU fp (Nat.le_refl n) A
    let y_hat := fl_forwardSub fp n L_hat b
    let x_hat := fl_backSub fp n U_hat y_hat
    ∃ DeltaA : Matrix (Fin n) (Fin n) ℝ,
      (∀ i j, |DeltaA i j| ≤ c * higham9_14_h u * |A i j|) ∧
      Matrix.mulVec (fun i j => A i j + DeltaA i j) x_hat = b := by
  dsimp only
  exact
    higham9_14_matrix_source_h_bound_of_RectDoolittleDenseLoopAbsBudgetCertificate_square_fl_triangular_solves_const_gamma_le
      fp n A
      (higham9_2_rectRoundedLoopL fp (Nat.le_refl n) A)
      (higham9_2_rectRoundedLoopU fp (Nat.le_refl n) A)
      b
      (higham9_2_rectDoolittleUAbsBudget fp (Nat.le_refl n) A
        (higham9_2_rectRoundedLoopL fp (Nat.le_refl n) A)
        (higham9_2_rectRoundedLoopU fp (Nat.le_refl n) A))
      (higham9_2_rectDoolittleLAbsBudget fp A
        (higham9_2_rectRoundedLoopL fp (Nat.le_refl n) A)
        (higham9_2_rectRoundedLoopU fp (Nat.le_refl n) A))
      c u hc hu hu_lt_one hn
      (higham9_2_rectRoundedLoop_to_rectAbsBudgetCertificate fp
        (Nat.le_refl n) A hU_diag hn hU_budget_le hL_budget_le)
      hγ_le_u hU_diag hAbsLU_le

/-- **Theorem 9.14**, Matrix-facing executable rectangular rounded loop
`h(γ_n)` bound with a supplied constant-growth comparison. -/
theorem higham9_14_matrix_source_h_bound_of_rectRoundedLoop_square_fl_triangular_solves_const_gamma
    (fp : FPModel) (n : ℕ)
    (A : Matrix (Fin n) (Fin n) ℝ)
    (b : Fin n → ℝ)
    (c : ℝ) (hc : 0 ≤ c)
    (hn : gammaValid fp n)
    (hγ_lt_one : gamma fp n < 1)
    (hU_diag : ∀ k : Fin n,
      higham9_2_rectRoundedLoopU fp (Nat.le_refl n) A k k ≠ 0)
    (hU_budget_le : ∀ k j : Fin n, k.val ≤ j.val →
      higham9_2_rectDoolittleUAbsBudget fp (Nat.le_refl n) A
          (higham9_2_rectRoundedLoopL fp (Nat.le_refl n) A)
          (higham9_2_rectRoundedLoopU fp (Nat.le_refl n) A) k j ≤
        gamma fp n *
          |higham9_2_rectRoundedLoopU fp (Nat.le_refl n) A k j|)
    (hL_budget_le : ∀ i k : Fin n, k.val < i.val →
      higham9_2_rectDoolittleLAbsBudget fp A
          (higham9_2_rectRoundedLoopL fp (Nat.le_refl n) A)
          (higham9_2_rectRoundedLoopU fp (Nat.le_refl n) A) i k ≤
        gamma fp n *
          |higham9_2_rectRoundedLoopL fp (Nat.le_refl n) A i k *
            higham9_2_rectRoundedLoopU fp (Nat.le_refl n) A k k|)
    (hAbsLU_le : ∀ i j : Fin n,
      ∑ k : Fin n,
          |higham9_2_rectRoundedLoopL fp (Nat.le_refl n) A i k| *
            |higham9_2_rectRoundedLoopU fp (Nat.le_refl n) A k j| ≤
        c * |A i j|) :
    let L_hat := higham9_2_rectRoundedLoopL fp (Nat.le_refl n) A
    let U_hat := higham9_2_rectRoundedLoopU fp (Nat.le_refl n) A
    let y_hat := fl_forwardSub fp n L_hat b
    let x_hat := fl_backSub fp n U_hat y_hat
    ∃ DeltaA : Matrix (Fin n) (Fin n) ℝ,
      (∀ i j, |DeltaA i j| ≤
        c * higham9_14_h (gamma fp n) * |A i j|) ∧
      Matrix.mulVec (fun i j => A i j + DeltaA i j) x_hat = b := by
  dsimp only
  exact
    higham9_14_matrix_source_h_bound_of_rectRoundedLoop_square_fl_triangular_solves_const_gamma_le
      fp n A b c (gamma fp n) hc (gamma_nonneg fp hn)
      hγ_lt_one hn hU_diag hU_budget_le hL_budget_le le_rfl hAbsLU_le

/-- **Theorem 9.14**, column-dominant tridiagonal rounded-loop source `f(u)`
bound.

The rectangular rounded loop supplies the concrete factors and certificate
budgets; an exact `LUFactSpec` for those factors plus Theorem 9.13 discharges
the structural `|Lhat||Uhat| <= 3|A|` comparison. -/
theorem higham9_14_tridiag_colDiagDom_source_f_bound_of_rectRoundedLoop_square_fl_triangular_solves_gamma_le
    (fp : FPModel) (n : ℕ)
    (A : Fin n → Fin n → ℝ)
    (b : Fin n → ℝ)
    (u : ℝ) (hu : 0 ≤ u)
    (hn : gammaValid fp n)
    (hLU : LUFactSpec n A
      (higham9_2_rectRoundedLoopL fp (Nat.le_refl n) A)
      (higham9_2_rectRoundedLoopU fp (Nat.le_refl n) A))
    (hdetA : Matrix.det (Matrix.of A : Matrix (Fin n) (Fin n) ℝ) ≠ 0)
    (hA_tridiag : IsTridiagonal n A)
    (hColDom : IsDiagDominant n A)
    (hU_budget_le : ∀ k j : Fin n, k.val ≤ j.val →
      higham9_2_rectDoolittleUAbsBudget fp (Nat.le_refl n) A
          (higham9_2_rectRoundedLoopL fp (Nat.le_refl n) A)
          (higham9_2_rectRoundedLoopU fp (Nat.le_refl n) A) k j ≤
        gamma fp n *
          |higham9_2_rectRoundedLoopU fp (Nat.le_refl n) A k j|)
    (hL_budget_le : ∀ i k : Fin n, k.val < i.val →
      higham9_2_rectDoolittleLAbsBudget fp A
          (higham9_2_rectRoundedLoopL fp (Nat.le_refl n) A)
          (higham9_2_rectRoundedLoopU fp (Nat.le_refl n) A) i k ≤
        gamma fp n *
          |higham9_2_rectRoundedLoopL fp (Nat.le_refl n) A i k *
            higham9_2_rectRoundedLoopU fp (Nat.le_refl n) A k k|)
    (hγ_le_u : gamma fp n ≤ u) :
    let L_hat := higham9_2_rectRoundedLoopL fp (Nat.le_refl n) A
    let U_hat := higham9_2_rectRoundedLoopU fp (Nat.le_refl n) A
    let y_hat := fl_forwardSub fp n L_hat b
    let x_hat := fl_backSub fp n U_hat y_hat
    ∃ DeltaA : Fin n → Fin n → ℝ,
      (∀ i j, |DeltaA i j| ≤ 3 * higham9_14_f u * |A i j|) ∧
      (∀ i, ∑ j : Fin n, (A i j + DeltaA i j) * x_hat j = b i) := by
  dsimp only
  exact
    higham9_14_source_f_bound_of_rectRoundedLoop_square_fl_triangular_solves_gamma_le
      fp n A b 3 u hu hn
      (hLU.det_ne_zero_iff_U_diag_ne_zero.mp hdetA)
      hU_budget_le hL_budget_le hγ_le_u
      (higham9_13_colDiagDom_tridiag_growth_bound_3_of_LUFactSpec
        A
        (higham9_2_rectRoundedLoopL fp (Nat.le_refl n) A)
        (higham9_2_rectRoundedLoopU fp (Nat.le_refl n) A)
        hLU hdetA hA_tridiag hColDom)

/-- **Theorem 9.14**, row-dominant tridiagonal rounded-loop source `f(u)`
bound. -/
theorem higham9_14_tridiag_rowDiagDom_source_f_bound_of_rectRoundedLoop_square_fl_triangular_solves_gamma_le
    (fp : FPModel) (n : ℕ)
    (A : Fin n → Fin n → ℝ)
    (b : Fin n → ℝ)
    (u : ℝ) (hu : 0 ≤ u)
    (hn : gammaValid fp n)
    (hLU : LUFactSpec n A
      (higham9_2_rectRoundedLoopL fp (Nat.le_refl n) A)
      (higham9_2_rectRoundedLoopU fp (Nat.le_refl n) A))
    (hdetA : Matrix.det (Matrix.of A : Matrix (Fin n) (Fin n) ℝ) ≠ 0)
    (hA_tridiag : IsTridiagonal n A)
    (hRowDom : IsRowDiagDominant n A)
    (hU_budget_le : ∀ k j : Fin n, k.val ≤ j.val →
      higham9_2_rectDoolittleUAbsBudget fp (Nat.le_refl n) A
          (higham9_2_rectRoundedLoopL fp (Nat.le_refl n) A)
          (higham9_2_rectRoundedLoopU fp (Nat.le_refl n) A) k j ≤
        gamma fp n *
          |higham9_2_rectRoundedLoopU fp (Nat.le_refl n) A k j|)
    (hL_budget_le : ∀ i k : Fin n, k.val < i.val →
      higham9_2_rectDoolittleLAbsBudget fp A
          (higham9_2_rectRoundedLoopL fp (Nat.le_refl n) A)
          (higham9_2_rectRoundedLoopU fp (Nat.le_refl n) A) i k ≤
        gamma fp n *
          |higham9_2_rectRoundedLoopL fp (Nat.le_refl n) A i k *
            higham9_2_rectRoundedLoopU fp (Nat.le_refl n) A k k|)
    (hγ_le_u : gamma fp n ≤ u) :
    let L_hat := higham9_2_rectRoundedLoopL fp (Nat.le_refl n) A
    let U_hat := higham9_2_rectRoundedLoopU fp (Nat.le_refl n) A
    let y_hat := fl_forwardSub fp n L_hat b
    let x_hat := fl_backSub fp n U_hat y_hat
    ∃ DeltaA : Fin n → Fin n → ℝ,
      (∀ i j, |DeltaA i j| ≤ 3 * higham9_14_f u * |A i j|) ∧
      (∀ i, ∑ j : Fin n, (A i j + DeltaA i j) * x_hat j = b i) := by
  dsimp only
  exact
    higham9_14_source_f_bound_of_rectRoundedLoop_square_fl_triangular_solves_gamma_le
      fp n A b 3 u hu hn
      (hLU.det_ne_zero_iff_U_diag_ne_zero.mp hdetA)
      hU_budget_le hL_budget_le hγ_le_u
      (higham9_13_rowDiagDom_tridiag_growth_bound_3_of_LUFactSpec
        A
        (higham9_2_rectRoundedLoopL fp (Nat.le_refl n) A)
        (higham9_2_rectRoundedLoopU fp (Nat.le_refl n) A)
        hLU hdetA hA_tridiag hRowDom)

/-- **Theorem 9.14**, column-dominant tridiagonal rounded-loop source
`f(γ_n)` bound. -/
theorem higham9_14_tridiag_colDiagDom_source_f_bound_of_rectRoundedLoop_square_fl_triangular_solves_gamma
    (fp : FPModel) (n : ℕ)
    (A : Fin n → Fin n → ℝ)
    (b : Fin n → ℝ)
    (hn : gammaValid fp n)
    (hLU : LUFactSpec n A
      (higham9_2_rectRoundedLoopL fp (Nat.le_refl n) A)
      (higham9_2_rectRoundedLoopU fp (Nat.le_refl n) A))
    (hdetA : Matrix.det (Matrix.of A : Matrix (Fin n) (Fin n) ℝ) ≠ 0)
    (hA_tridiag : IsTridiagonal n A)
    (hColDom : IsDiagDominant n A)
    (hU_budget_le : ∀ k j : Fin n, k.val ≤ j.val →
      higham9_2_rectDoolittleUAbsBudget fp (Nat.le_refl n) A
          (higham9_2_rectRoundedLoopL fp (Nat.le_refl n) A)
          (higham9_2_rectRoundedLoopU fp (Nat.le_refl n) A) k j ≤
        gamma fp n *
          |higham9_2_rectRoundedLoopU fp (Nat.le_refl n) A k j|)
    (hL_budget_le : ∀ i k : Fin n, k.val < i.val →
      higham9_2_rectDoolittleLAbsBudget fp A
          (higham9_2_rectRoundedLoopL fp (Nat.le_refl n) A)
          (higham9_2_rectRoundedLoopU fp (Nat.le_refl n) A) i k ≤
        gamma fp n *
          |higham9_2_rectRoundedLoopL fp (Nat.le_refl n) A i k *
            higham9_2_rectRoundedLoopU fp (Nat.le_refl n) A k k|) :
    let L_hat := higham9_2_rectRoundedLoopL fp (Nat.le_refl n) A
    let U_hat := higham9_2_rectRoundedLoopU fp (Nat.le_refl n) A
    let y_hat := fl_forwardSub fp n L_hat b
    let x_hat := fl_backSub fp n U_hat y_hat
    ∃ DeltaA : Fin n → Fin n → ℝ,
      (∀ i j, |DeltaA i j| ≤
        3 * higham9_14_f (gamma fp n) * |A i j|) ∧
      (∀ i, ∑ j : Fin n, (A i j + DeltaA i j) * x_hat j = b i) := by
  dsimp only
  exact
    higham9_14_tridiag_colDiagDom_source_f_bound_of_rectRoundedLoop_square_fl_triangular_solves_gamma_le
      fp n A b (gamma fp n) (gamma_nonneg fp hn) hn hLU hdetA
      hA_tridiag hColDom hU_budget_le hL_budget_le le_rfl

/-- **Theorem 9.14**, row-dominant tridiagonal rounded-loop source
`f(γ_n)` bound. -/
theorem higham9_14_tridiag_rowDiagDom_source_f_bound_of_rectRoundedLoop_square_fl_triangular_solves_gamma
    (fp : FPModel) (n : ℕ)
    (A : Fin n → Fin n → ℝ)
    (b : Fin n → ℝ)
    (hn : gammaValid fp n)
    (hLU : LUFactSpec n A
      (higham9_2_rectRoundedLoopL fp (Nat.le_refl n) A)
      (higham9_2_rectRoundedLoopU fp (Nat.le_refl n) A))
    (hdetA : Matrix.det (Matrix.of A : Matrix (Fin n) (Fin n) ℝ) ≠ 0)
    (hA_tridiag : IsTridiagonal n A)
    (hRowDom : IsRowDiagDominant n A)
    (hU_budget_le : ∀ k j : Fin n, k.val ≤ j.val →
      higham9_2_rectDoolittleUAbsBudget fp (Nat.le_refl n) A
          (higham9_2_rectRoundedLoopL fp (Nat.le_refl n) A)
          (higham9_2_rectRoundedLoopU fp (Nat.le_refl n) A) k j ≤
        gamma fp n *
          |higham9_2_rectRoundedLoopU fp (Nat.le_refl n) A k j|)
    (hL_budget_le : ∀ i k : Fin n, k.val < i.val →
      higham9_2_rectDoolittleLAbsBudget fp A
          (higham9_2_rectRoundedLoopL fp (Nat.le_refl n) A)
          (higham9_2_rectRoundedLoopU fp (Nat.le_refl n) A) i k ≤
        gamma fp n *
          |higham9_2_rectRoundedLoopL fp (Nat.le_refl n) A i k *
            higham9_2_rectRoundedLoopU fp (Nat.le_refl n) A k k|) :
    let L_hat := higham9_2_rectRoundedLoopL fp (Nat.le_refl n) A
    let U_hat := higham9_2_rectRoundedLoopU fp (Nat.le_refl n) A
    let y_hat := fl_forwardSub fp n L_hat b
    let x_hat := fl_backSub fp n U_hat y_hat
    ∃ DeltaA : Fin n → Fin n → ℝ,
      (∀ i j, |DeltaA i j| ≤
        3 * higham9_14_f (gamma fp n) * |A i j|) ∧
      (∀ i, ∑ j : Fin n, (A i j + DeltaA i j) * x_hat j = b i) := by
  dsimp only
  exact
    higham9_14_tridiag_rowDiagDom_source_f_bound_of_rectRoundedLoop_square_fl_triangular_solves_gamma_le
      fp n A b (gamma fp n) (gamma_nonneg fp hn) hn hLU hdetA
      hA_tridiag hRowDom hU_budget_le hL_budget_le le_rfl

/-- **Theorem 9.14**, column-dominant tridiagonal rounded-loop final `h(u)`
bound. -/
theorem higham9_14_tridiag_colDiagDom_source_h_bound_of_rectRoundedLoop_square_fl_triangular_solves_const_gamma_le
    (fp : FPModel) (n : ℕ)
    (A : Fin n → Fin n → ℝ)
    (b : Fin n → ℝ)
    (u : ℝ) (hu : 0 ≤ u) (hu_lt_one : u < 1)
    (hn : gammaValid fp n)
    (hLU : LUFactSpec n A
      (higham9_2_rectRoundedLoopL fp (Nat.le_refl n) A)
      (higham9_2_rectRoundedLoopU fp (Nat.le_refl n) A))
    (hdetA : Matrix.det (Matrix.of A : Matrix (Fin n) (Fin n) ℝ) ≠ 0)
    (hA_tridiag : IsTridiagonal n A)
    (hColDom : IsDiagDominant n A)
    (hU_budget_le : ∀ k j : Fin n, k.val ≤ j.val →
      higham9_2_rectDoolittleUAbsBudget fp (Nat.le_refl n) A
          (higham9_2_rectRoundedLoopL fp (Nat.le_refl n) A)
          (higham9_2_rectRoundedLoopU fp (Nat.le_refl n) A) k j ≤
        gamma fp n *
          |higham9_2_rectRoundedLoopU fp (Nat.le_refl n) A k j|)
    (hL_budget_le : ∀ i k : Fin n, k.val < i.val →
      higham9_2_rectDoolittleLAbsBudget fp A
          (higham9_2_rectRoundedLoopL fp (Nat.le_refl n) A)
          (higham9_2_rectRoundedLoopU fp (Nat.le_refl n) A) i k ≤
        gamma fp n *
          |higham9_2_rectRoundedLoopL fp (Nat.le_refl n) A i k *
            higham9_2_rectRoundedLoopU fp (Nat.le_refl n) A k k|)
    (hγ_le_u : gamma fp n ≤ u) :
    let L_hat := higham9_2_rectRoundedLoopL fp (Nat.le_refl n) A
    let U_hat := higham9_2_rectRoundedLoopU fp (Nat.le_refl n) A
    let y_hat := fl_forwardSub fp n L_hat b
    let x_hat := fl_backSub fp n U_hat y_hat
    ∃ DeltaA : Fin n → Fin n → ℝ,
      (∀ i j, |DeltaA i j| ≤ 3 * higham9_14_h u * |A i j|) ∧
      (∀ i, ∑ j : Fin n, (A i j + DeltaA i j) * x_hat j = b i) := by
  dsimp only
  exact
    higham9_14_source_h_bound_of_rectRoundedLoop_square_fl_triangular_solves_const_gamma_le
      fp n A b 3 u (by norm_num) hu hu_lt_one hn
      (hLU.det_ne_zero_iff_U_diag_ne_zero.mp hdetA)
      hU_budget_le hL_budget_le hγ_le_u
      (higham9_13_colDiagDom_tridiag_growth_bound_3_of_LUFactSpec
        A
        (higham9_2_rectRoundedLoopL fp (Nat.le_refl n) A)
        (higham9_2_rectRoundedLoopU fp (Nat.le_refl n) A)
        hLU hdetA hA_tridiag hColDom)

/-- **Theorem 9.14**, row-dominant tridiagonal rounded-loop final `h(u)`
bound. -/
theorem higham9_14_tridiag_rowDiagDom_source_h_bound_of_rectRoundedLoop_square_fl_triangular_solves_const_gamma_le
    (fp : FPModel) (n : ℕ)
    (A : Fin n → Fin n → ℝ)
    (b : Fin n → ℝ)
    (u : ℝ) (hu : 0 ≤ u) (hu_lt_one : u < 1)
    (hn : gammaValid fp n)
    (hLU : LUFactSpec n A
      (higham9_2_rectRoundedLoopL fp (Nat.le_refl n) A)
      (higham9_2_rectRoundedLoopU fp (Nat.le_refl n) A))
    (hdetA : Matrix.det (Matrix.of A : Matrix (Fin n) (Fin n) ℝ) ≠ 0)
    (hA_tridiag : IsTridiagonal n A)
    (hRowDom : IsRowDiagDominant n A)
    (hU_budget_le : ∀ k j : Fin n, k.val ≤ j.val →
      higham9_2_rectDoolittleUAbsBudget fp (Nat.le_refl n) A
          (higham9_2_rectRoundedLoopL fp (Nat.le_refl n) A)
          (higham9_2_rectRoundedLoopU fp (Nat.le_refl n) A) k j ≤
        gamma fp n *
          |higham9_2_rectRoundedLoopU fp (Nat.le_refl n) A k j|)
    (hL_budget_le : ∀ i k : Fin n, k.val < i.val →
      higham9_2_rectDoolittleLAbsBudget fp A
          (higham9_2_rectRoundedLoopL fp (Nat.le_refl n) A)
          (higham9_2_rectRoundedLoopU fp (Nat.le_refl n) A) i k ≤
        gamma fp n *
          |higham9_2_rectRoundedLoopL fp (Nat.le_refl n) A i k *
            higham9_2_rectRoundedLoopU fp (Nat.le_refl n) A k k|)
    (hγ_le_u : gamma fp n ≤ u) :
    let L_hat := higham9_2_rectRoundedLoopL fp (Nat.le_refl n) A
    let U_hat := higham9_2_rectRoundedLoopU fp (Nat.le_refl n) A
    let y_hat := fl_forwardSub fp n L_hat b
    let x_hat := fl_backSub fp n U_hat y_hat
    ∃ DeltaA : Fin n → Fin n → ℝ,
      (∀ i j, |DeltaA i j| ≤ 3 * higham9_14_h u * |A i j|) ∧
      (∀ i, ∑ j : Fin n, (A i j + DeltaA i j) * x_hat j = b i) := by
  dsimp only
  exact
    higham9_14_source_h_bound_of_rectRoundedLoop_square_fl_triangular_solves_const_gamma_le
      fp n A b 3 u (by norm_num) hu hu_lt_one hn
      (hLU.det_ne_zero_iff_U_diag_ne_zero.mp hdetA)
      hU_budget_le hL_budget_le hγ_le_u
      (higham9_13_rowDiagDom_tridiag_growth_bound_3_of_LUFactSpec
        A
        (higham9_2_rectRoundedLoopL fp (Nat.le_refl n) A)
        (higham9_2_rectRoundedLoopU fp (Nat.le_refl n) A)
        hLU hdetA hA_tridiag hRowDom)

/-- **Theorem 9.14**, column-dominant tridiagonal rounded-loop final
`h(γ_n)` bound. -/
theorem higham9_14_tridiag_colDiagDom_source_h_bound_of_rectRoundedLoop_square_fl_triangular_solves_const_gamma
    (fp : FPModel) (n : ℕ)
    (A : Fin n → Fin n → ℝ)
    (b : Fin n → ℝ)
    (hn : gammaValid fp n)
    (hγ_lt_one : gamma fp n < 1)
    (hLU : LUFactSpec n A
      (higham9_2_rectRoundedLoopL fp (Nat.le_refl n) A)
      (higham9_2_rectRoundedLoopU fp (Nat.le_refl n) A))
    (hdetA : Matrix.det (Matrix.of A : Matrix (Fin n) (Fin n) ℝ) ≠ 0)
    (hA_tridiag : IsTridiagonal n A)
    (hColDom : IsDiagDominant n A)
    (hU_budget_le : ∀ k j : Fin n, k.val ≤ j.val →
      higham9_2_rectDoolittleUAbsBudget fp (Nat.le_refl n) A
          (higham9_2_rectRoundedLoopL fp (Nat.le_refl n) A)
          (higham9_2_rectRoundedLoopU fp (Nat.le_refl n) A) k j ≤
        gamma fp n *
          |higham9_2_rectRoundedLoopU fp (Nat.le_refl n) A k j|)
    (hL_budget_le : ∀ i k : Fin n, k.val < i.val →
      higham9_2_rectDoolittleLAbsBudget fp A
          (higham9_2_rectRoundedLoopL fp (Nat.le_refl n) A)
          (higham9_2_rectRoundedLoopU fp (Nat.le_refl n) A) i k ≤
        gamma fp n *
          |higham9_2_rectRoundedLoopL fp (Nat.le_refl n) A i k *
            higham9_2_rectRoundedLoopU fp (Nat.le_refl n) A k k|) :
    let L_hat := higham9_2_rectRoundedLoopL fp (Nat.le_refl n) A
    let U_hat := higham9_2_rectRoundedLoopU fp (Nat.le_refl n) A
    let y_hat := fl_forwardSub fp n L_hat b
    let x_hat := fl_backSub fp n U_hat y_hat
    ∃ DeltaA : Fin n → Fin n → ℝ,
      (∀ i j, |DeltaA i j| ≤
        3 * higham9_14_h (gamma fp n) * |A i j|) ∧
      (∀ i, ∑ j : Fin n, (A i j + DeltaA i j) * x_hat j = b i) := by
  dsimp only
  exact
    higham9_14_tridiag_colDiagDom_source_h_bound_of_rectRoundedLoop_square_fl_triangular_solves_const_gamma_le
      fp n A b (gamma fp n) (gamma_nonneg fp hn) hγ_lt_one hn
      hLU hdetA hA_tridiag hColDom hU_budget_le hL_budget_le le_rfl

/-- **Theorem 9.14**, row-dominant tridiagonal rounded-loop final `h(γ_n)`
bound. -/
theorem higham9_14_tridiag_rowDiagDom_source_h_bound_of_rectRoundedLoop_square_fl_triangular_solves_const_gamma
    (fp : FPModel) (n : ℕ)
    (A : Fin n → Fin n → ℝ)
    (b : Fin n → ℝ)
    (hn : gammaValid fp n)
    (hγ_lt_one : gamma fp n < 1)
    (hLU : LUFactSpec n A
      (higham9_2_rectRoundedLoopL fp (Nat.le_refl n) A)
      (higham9_2_rectRoundedLoopU fp (Nat.le_refl n) A))
    (hdetA : Matrix.det (Matrix.of A : Matrix (Fin n) (Fin n) ℝ) ≠ 0)
    (hA_tridiag : IsTridiagonal n A)
    (hRowDom : IsRowDiagDominant n A)
    (hU_budget_le : ∀ k j : Fin n, k.val ≤ j.val →
      higham9_2_rectDoolittleUAbsBudget fp (Nat.le_refl n) A
          (higham9_2_rectRoundedLoopL fp (Nat.le_refl n) A)
          (higham9_2_rectRoundedLoopU fp (Nat.le_refl n) A) k j ≤
        gamma fp n *
          |higham9_2_rectRoundedLoopU fp (Nat.le_refl n) A k j|)
    (hL_budget_le : ∀ i k : Fin n, k.val < i.val →
      higham9_2_rectDoolittleLAbsBudget fp A
          (higham9_2_rectRoundedLoopL fp (Nat.le_refl n) A)
          (higham9_2_rectRoundedLoopU fp (Nat.le_refl n) A) i k ≤
        gamma fp n *
          |higham9_2_rectRoundedLoopL fp (Nat.le_refl n) A i k *
            higham9_2_rectRoundedLoopU fp (Nat.le_refl n) A k k|) :
    let L_hat := higham9_2_rectRoundedLoopL fp (Nat.le_refl n) A
    let U_hat := higham9_2_rectRoundedLoopU fp (Nat.le_refl n) A
    let y_hat := fl_forwardSub fp n L_hat b
    let x_hat := fl_backSub fp n U_hat y_hat
    ∃ DeltaA : Fin n → Fin n → ℝ,
      (∀ i j, |DeltaA i j| ≤
        3 * higham9_14_h (gamma fp n) * |A i j|) ∧
      (∀ i, ∑ j : Fin n, (A i j + DeltaA i j) * x_hat j = b i) := by
  dsimp only
  exact
  higham9_14_tridiag_rowDiagDom_source_h_bound_of_rectRoundedLoop_square_fl_triangular_solves_const_gamma_le
    fp n A b (gamma fp n) (gamma_nonneg fp hn) hγ_lt_one hn
    hLU hdetA hA_tridiag hRowDom hU_budget_le hL_budget_le le_rfl

/-- **Theorem 9.14**, column-dominant executable rounded-loop
model-consuming `f(γ_n)` bound.

The concrete rectangular rounded loop supplies equation (9.20) at the natural
coefficient, while the caller supplies the explicit equation (9.21)
triangular-solve model.  This is the model-consuming counterpart of the
actual-solve rounded-loop source wrapper above. -/
theorem higham9_14_tridiag_colDiagDom_source_f_bound_of_rectRoundedLoop_square_models_gamma
    (fp : FPModel) (n : ℕ)
    (A : Fin n → Fin n → ℝ)
    (y_hat x_hat b : Fin n → ℝ)
    (DeltaL DeltaU : Fin n → Fin n → ℝ)
    (hn : gammaValid fp n)
    (hLU : LUFactSpec n A
      (higham9_2_rectRoundedLoopL fp (Nat.le_refl n) A)
      (higham9_2_rectRoundedLoopU fp (Nat.le_refl n) A))
    (hdetA : Matrix.det (Matrix.of A : Matrix (Fin n) (Fin n) ℝ) ≠ 0)
    (hA_tridiag : IsTridiagonal n A)
    (hColDom : IsDiagDominant n A)
    (hU_budget_le : ∀ k j : Fin n, k.val ≤ j.val →
      higham9_2_rectDoolittleUAbsBudget fp (Nat.le_refl n) A
          (higham9_2_rectRoundedLoopL fp (Nat.le_refl n) A)
          (higham9_2_rectRoundedLoopU fp (Nat.le_refl n) A) k j ≤
        gamma fp n *
          |higham9_2_rectRoundedLoopU fp (Nat.le_refl n) A k j|)
    (hL_budget_le : ∀ i k : Fin n, k.val < i.val →
      higham9_2_rectDoolittleLAbsBudget fp A
          (higham9_2_rectRoundedLoopL fp (Nat.le_refl n) A)
          (higham9_2_rectRoundedLoopU fp (Nat.le_refl n) A) i k ≤
        gamma fp n *
          |higham9_2_rectRoundedLoopL fp (Nat.le_refl n) A i k *
            higham9_2_rectRoundedLoopU fp (Nat.le_refl n) A k k|)
    (h21 : higham9_21_tridiag_solve_perturbation_model n
      (higham9_2_rectRoundedLoopL fp (Nat.le_refl n) A)
      (higham9_2_rectRoundedLoopU fp (Nat.le_refl n) A)
      y_hat x_hat b DeltaL DeltaU (gamma fp n)) :
    ∃ DeltaA : Fin n → Fin n → ℝ,
      (∀ i j, |DeltaA i j| ≤
        3 * higham9_14_f (gamma fp n) * |A i j|) ∧
      (∀ i, ∑ j : Fin n, (A i j + DeltaA i j) * x_hat j = b i) := by
  rcases
      higham9_20_tridiag_lu_perturbation_model_of_rectRoundedLoop_square_gamma
        fp n A hn
        (hLU.det_ne_zero_iff_U_diag_ne_zero.mp hdetA)
        hU_budget_le hL_budget_le with
    ⟨DeltaA_LU, h20⟩
  exact
    higham9_14_source_f_bound_of_absLU_le_const_absA_and_9_20_9_21_models
      n A
      (higham9_2_rectRoundedLoopL fp (Nat.le_refl n) A)
      (higham9_2_rectRoundedLoopU fp (Nat.le_refl n) A)
      y_hat x_hat b 3 (gamma fp n) (gamma_nonneg fp hn)
      (higham9_13_colDiagDom_tridiag_growth_bound_3_of_LUFactSpec
        A
        (higham9_2_rectRoundedLoopL fp (Nat.le_refl n) A)
        (higham9_2_rectRoundedLoopU fp (Nat.le_refl n) A)
        hLU hdetA hA_tridiag hColDom)
      DeltaA_LU DeltaL DeltaU h20 h21

/-- **Theorem 9.14**, row-dominant executable rounded-loop model-consuming
`f(γ_n)` bound. -/
theorem higham9_14_tridiag_rowDiagDom_source_f_bound_of_rectRoundedLoop_square_models_gamma
    (fp : FPModel) (n : ℕ)
    (A : Fin n → Fin n → ℝ)
    (y_hat x_hat b : Fin n → ℝ)
    (DeltaL DeltaU : Fin n → Fin n → ℝ)
    (hn : gammaValid fp n)
    (hLU : LUFactSpec n A
      (higham9_2_rectRoundedLoopL fp (Nat.le_refl n) A)
      (higham9_2_rectRoundedLoopU fp (Nat.le_refl n) A))
    (hdetA : Matrix.det (Matrix.of A : Matrix (Fin n) (Fin n) ℝ) ≠ 0)
    (hA_tridiag : IsTridiagonal n A)
    (hRowDom : IsRowDiagDominant n A)
    (hU_budget_le : ∀ k j : Fin n, k.val ≤ j.val →
      higham9_2_rectDoolittleUAbsBudget fp (Nat.le_refl n) A
          (higham9_2_rectRoundedLoopL fp (Nat.le_refl n) A)
          (higham9_2_rectRoundedLoopU fp (Nat.le_refl n) A) k j ≤
        gamma fp n *
          |higham9_2_rectRoundedLoopU fp (Nat.le_refl n) A k j|)
    (hL_budget_le : ∀ i k : Fin n, k.val < i.val →
      higham9_2_rectDoolittleLAbsBudget fp A
          (higham9_2_rectRoundedLoopL fp (Nat.le_refl n) A)
          (higham9_2_rectRoundedLoopU fp (Nat.le_refl n) A) i k ≤
        gamma fp n *
          |higham9_2_rectRoundedLoopL fp (Nat.le_refl n) A i k *
            higham9_2_rectRoundedLoopU fp (Nat.le_refl n) A k k|)
    (h21 : higham9_21_tridiag_solve_perturbation_model n
      (higham9_2_rectRoundedLoopL fp (Nat.le_refl n) A)
      (higham9_2_rectRoundedLoopU fp (Nat.le_refl n) A)
      y_hat x_hat b DeltaL DeltaU (gamma fp n)) :
    ∃ DeltaA : Fin n → Fin n → ℝ,
      (∀ i j, |DeltaA i j| ≤
        3 * higham9_14_f (gamma fp n) * |A i j|) ∧
      (∀ i, ∑ j : Fin n, (A i j + DeltaA i j) * x_hat j = b i) := by
  rcases
      higham9_20_tridiag_lu_perturbation_model_of_rectRoundedLoop_square_gamma
        fp n A hn
        (hLU.det_ne_zero_iff_U_diag_ne_zero.mp hdetA)
        hU_budget_le hL_budget_le with
    ⟨DeltaA_LU, h20⟩
  exact
    higham9_14_source_f_bound_of_absLU_le_const_absA_and_9_20_9_21_models
      n A
      (higham9_2_rectRoundedLoopL fp (Nat.le_refl n) A)
      (higham9_2_rectRoundedLoopU fp (Nat.le_refl n) A)
      y_hat x_hat b 3 (gamma fp n) (gamma_nonneg fp hn)
      (higham9_13_rowDiagDom_tridiag_growth_bound_3_of_LUFactSpec
        A
        (higham9_2_rectRoundedLoopL fp (Nat.le_refl n) A)
        (higham9_2_rectRoundedLoopU fp (Nat.le_refl n) A)
        hLU hdetA hA_tridiag hRowDom)
      DeltaA_LU DeltaL DeltaU h20 h21

/-- **Theorem 9.14**, column-dominant executable rounded-loop
model-consuming final `h(γ_n)` bound. -/
theorem higham9_14_tridiag_colDiagDom_source_h_bound_of_rectRoundedLoop_square_models_gamma
    (fp : FPModel) (n : ℕ)
    (A : Fin n → Fin n → ℝ)
    (y_hat x_hat b : Fin n → ℝ)
    (DeltaL DeltaU : Fin n → Fin n → ℝ)
    (hn : gammaValid fp n)
    (hγ_lt_one : gamma fp n < 1)
    (hLU : LUFactSpec n A
      (higham9_2_rectRoundedLoopL fp (Nat.le_refl n) A)
      (higham9_2_rectRoundedLoopU fp (Nat.le_refl n) A))
    (hdetA : Matrix.det (Matrix.of A : Matrix (Fin n) (Fin n) ℝ) ≠ 0)
    (hA_tridiag : IsTridiagonal n A)
    (hColDom : IsDiagDominant n A)
    (hU_budget_le : ∀ k j : Fin n, k.val ≤ j.val →
      higham9_2_rectDoolittleUAbsBudget fp (Nat.le_refl n) A
          (higham9_2_rectRoundedLoopL fp (Nat.le_refl n) A)
          (higham9_2_rectRoundedLoopU fp (Nat.le_refl n) A) k j ≤
        gamma fp n *
          |higham9_2_rectRoundedLoopU fp (Nat.le_refl n) A k j|)
    (hL_budget_le : ∀ i k : Fin n, k.val < i.val →
      higham9_2_rectDoolittleLAbsBudget fp A
          (higham9_2_rectRoundedLoopL fp (Nat.le_refl n) A)
          (higham9_2_rectRoundedLoopU fp (Nat.le_refl n) A) i k ≤
        gamma fp n *
          |higham9_2_rectRoundedLoopL fp (Nat.le_refl n) A i k *
            higham9_2_rectRoundedLoopU fp (Nat.le_refl n) A k k|)
    (h21 : higham9_21_tridiag_solve_perturbation_model n
      (higham9_2_rectRoundedLoopL fp (Nat.le_refl n) A)
      (higham9_2_rectRoundedLoopU fp (Nat.le_refl n) A)
      y_hat x_hat b DeltaL DeltaU (gamma fp n)) :
    ∃ DeltaA : Fin n → Fin n → ℝ,
      (∀ i j, |DeltaA i j| ≤
        3 * higham9_14_h (gamma fp n) * |A i j|) ∧
      (∀ i, ∑ j : Fin n, (A i j + DeltaA i j) * x_hat j = b i) := by
  rcases
      higham9_20_tridiag_lu_perturbation_model_of_rectRoundedLoop_square_gamma
        fp n A hn
        (hLU.det_ne_zero_iff_U_diag_ne_zero.mp hdetA)
        hU_budget_le hL_budget_le with
    ⟨DeltaA_LU, h20⟩
  exact
    higham9_14_source_h_bound_of_absLU_le_const_absA_and_9_20_9_21_models
      n A
      (higham9_2_rectRoundedLoopL fp (Nat.le_refl n) A)
      (higham9_2_rectRoundedLoopU fp (Nat.le_refl n) A)
      y_hat x_hat b 3 (gamma fp n) (by norm_num)
      (gamma_nonneg fp hn) hγ_lt_one
      (higham9_13_colDiagDom_tridiag_growth_bound_3_of_LUFactSpec
        A
        (higham9_2_rectRoundedLoopL fp (Nat.le_refl n) A)
        (higham9_2_rectRoundedLoopU fp (Nat.le_refl n) A)
        hLU hdetA hA_tridiag hColDom)
      DeltaA_LU DeltaL DeltaU h20 h21

/-- **Theorem 9.14**, row-dominant executable rounded-loop model-consuming
final `h(γ_n)` bound. -/
theorem higham9_14_tridiag_rowDiagDom_source_h_bound_of_rectRoundedLoop_square_models_gamma
    (fp : FPModel) (n : ℕ)
    (A : Fin n → Fin n → ℝ)
    (y_hat x_hat b : Fin n → ℝ)
    (DeltaL DeltaU : Fin n → Fin n → ℝ)
    (hn : gammaValid fp n)
    (hγ_lt_one : gamma fp n < 1)
    (hLU : LUFactSpec n A
      (higham9_2_rectRoundedLoopL fp (Nat.le_refl n) A)
      (higham9_2_rectRoundedLoopU fp (Nat.le_refl n) A))
    (hdetA : Matrix.det (Matrix.of A : Matrix (Fin n) (Fin n) ℝ) ≠ 0)
    (hA_tridiag : IsTridiagonal n A)
    (hRowDom : IsRowDiagDominant n A)
    (hU_budget_le : ∀ k j : Fin n, k.val ≤ j.val →
      higham9_2_rectDoolittleUAbsBudget fp (Nat.le_refl n) A
          (higham9_2_rectRoundedLoopL fp (Nat.le_refl n) A)
          (higham9_2_rectRoundedLoopU fp (Nat.le_refl n) A) k j ≤
        gamma fp n *
          |higham9_2_rectRoundedLoopU fp (Nat.le_refl n) A k j|)
    (hL_budget_le : ∀ i k : Fin n, k.val < i.val →
      higham9_2_rectDoolittleLAbsBudget fp A
          (higham9_2_rectRoundedLoopL fp (Nat.le_refl n) A)
          (higham9_2_rectRoundedLoopU fp (Nat.le_refl n) A) i k ≤
        gamma fp n *
          |higham9_2_rectRoundedLoopL fp (Nat.le_refl n) A i k *
            higham9_2_rectRoundedLoopU fp (Nat.le_refl n) A k k|)
    (h21 : higham9_21_tridiag_solve_perturbation_model n
      (higham9_2_rectRoundedLoopL fp (Nat.le_refl n) A)
      (higham9_2_rectRoundedLoopU fp (Nat.le_refl n) A)
      y_hat x_hat b DeltaL DeltaU (gamma fp n)) :
    ∃ DeltaA : Fin n → Fin n → ℝ,
      (∀ i j, |DeltaA i j| ≤
        3 * higham9_14_h (gamma fp n) * |A i j|) ∧
      (∀ i, ∑ j : Fin n, (A i j + DeltaA i j) * x_hat j = b i) := by
  rcases
      higham9_20_tridiag_lu_perturbation_model_of_rectRoundedLoop_square_gamma
        fp n A hn
        (hLU.det_ne_zero_iff_U_diag_ne_zero.mp hdetA)
        hU_budget_le hL_budget_le with
    ⟨DeltaA_LU, h20⟩
  exact
    higham9_14_source_h_bound_of_absLU_le_const_absA_and_9_20_9_21_models
      n A
      (higham9_2_rectRoundedLoopL fp (Nat.le_refl n) A)
      (higham9_2_rectRoundedLoopU fp (Nat.le_refl n) A)
      y_hat x_hat b 3 (gamma fp n) (by norm_num)
      (gamma_nonneg fp hn) hγ_lt_one
      (higham9_13_rowDiagDom_tridiag_growth_bound_3_of_LUFactSpec
        A
        (higham9_2_rectRoundedLoopL fp (Nat.le_refl n) A)
        (higham9_2_rectRoundedLoopU fp (Nat.le_refl n) A)
        hLU hdetA hA_tridiag hRowDom)
      DeltaA_LU DeltaL DeltaU h20 h21

/-- **Theorem 9.14**, SPD positive-`D L^T` executable rounded-loop source
`f(u)` bound.

This is the concrete-loop counterpart of the rounded-stage SPD positive-`D L^T`
wrapper.  The loop supplies the factors and budgets, while the exact
positive-`D L^T` certificate supplies `|Lhat||Uhat| = |A|`. -/
theorem higham9_14_spd_tridiag_positive_DLT_source_f_bound_of_rectRoundedLoop_square_fl_triangular_solves_gamma_le
    (fp : FPModel) (n : ℕ)
    (A : Fin n → Fin n → ℝ)
    (d b : Fin n → ℝ)
    (u : ℝ) (hu : 0 ≤ u)
    (hn : gammaValid fp n)
    (hStruct : IsTridiagLU n
      (higham9_2_rectRoundedLoopL fp (Nat.le_refl n) A)
      (higham9_2_rectRoundedLoopU fp (Nat.le_refl n) A))
    (hLU_eq : ∀ i j : Fin n,
      ∑ k : Fin n,
          higham9_2_rectRoundedLoopL fp (Nat.le_refl n) A i k *
            higham9_2_rectRoundedLoopU fp (Nat.le_refl n) A k j =
        A i j)
    (hdetA : Matrix.det (Matrix.of A : Matrix (Fin n) (Fin n) ℝ) ≠ 0)
    (hd_pos : ∀ k : Fin n, 0 < d k)
    (hDLT : ∀ k j : Fin n,
      higham9_2_rectRoundedLoopU fp (Nat.le_refl n) A k j =
        d k * higham9_2_rectRoundedLoopL fp (Nat.le_refl n) A j k)
    (hU_budget_le : ∀ k j : Fin n, k.val ≤ j.val →
      higham9_2_rectDoolittleUAbsBudget fp (Nat.le_refl n) A
          (higham9_2_rectRoundedLoopL fp (Nat.le_refl n) A)
          (higham9_2_rectRoundedLoopU fp (Nat.le_refl n) A) k j ≤
        gamma fp n *
          |higham9_2_rectRoundedLoopU fp (Nat.le_refl n) A k j|)
    (hL_budget_le : ∀ i k : Fin n, k.val < i.val →
      higham9_2_rectDoolittleLAbsBudget fp A
          (higham9_2_rectRoundedLoopL fp (Nat.le_refl n) A)
          (higham9_2_rectRoundedLoopU fp (Nat.le_refl n) A) i k ≤
        gamma fp n *
          |higham9_2_rectRoundedLoopL fp (Nat.le_refl n) A i k *
            higham9_2_rectRoundedLoopU fp (Nat.le_refl n) A k k|)
    (hγ_le_u : gamma fp n ≤ u) :
    let L_hat := higham9_2_rectRoundedLoopL fp (Nat.le_refl n) A
    let U_hat := higham9_2_rectRoundedLoopU fp (Nat.le_refl n) A
    let y_hat := fl_forwardSub fp n L_hat b
    let x_hat := fl_backSub fp n U_hat y_hat
    ∃ DeltaA : Fin n → Fin n → ℝ,
      (∀ i j, |DeltaA i j| ≤ higham9_14_f u * |A i j|) ∧
      (∀ i, ∑ j : Fin n, (A i j + DeltaA i j) * x_hat j = b i) := by
  dsimp only
  let hLU : LUFactSpec n A
      (higham9_2_rectRoundedLoopL fp (Nat.le_refl n) A)
      (higham9_2_rectRoundedLoopU fp (Nat.le_refl n) A) :=
    { L_diag := hStruct.L_diag
      L_upper_zero := hStruct.L_upper_zero
      U_lower_zero := hStruct.U_lower_zero
      product_eq := hLU_eq }
  simpa [one_mul] using
    (higham9_14_source_f_bound_of_rectRoundedLoop_square_fl_triangular_solves_gamma_le
      fp n A b 1 u hu hn
      (hLU.det_ne_zero_iff_U_diag_ne_zero.mp hdetA)
      hU_budget_le hL_budget_le hγ_le_u
      (fun i j => by
        simpa [one_mul] using
          le_of_eq
            (higham9_12_spd_tridiag_absLU_eq_of_positive_DLT
              A
              (higham9_2_rectRoundedLoopL fp (Nat.le_refl n) A)
              (higham9_2_rectRoundedLoopU fp (Nat.le_refl n) A)
              d hStruct hLU_eq hd_pos hDLT i j)))

/-- **Theorem 9.14**, SPD positive-`D L^T` executable rounded-loop final
`h(u)` bound. -/
theorem higham9_14_spd_tridiag_positive_DLT_source_h_bound_of_rectRoundedLoop_square_fl_triangular_solves_gamma_le
    (fp : FPModel) (n : ℕ)
    (A : Fin n → Fin n → ℝ)
    (d b : Fin n → ℝ)
    (u : ℝ) (hu : 0 ≤ u) (hu_lt_one : u < 1)
    (hn : gammaValid fp n)
    (hStruct : IsTridiagLU n
      (higham9_2_rectRoundedLoopL fp (Nat.le_refl n) A)
      (higham9_2_rectRoundedLoopU fp (Nat.le_refl n) A))
    (hLU_eq : ∀ i j : Fin n,
      ∑ k : Fin n,
          higham9_2_rectRoundedLoopL fp (Nat.le_refl n) A i k *
            higham9_2_rectRoundedLoopU fp (Nat.le_refl n) A k j =
        A i j)
    (hdetA : Matrix.det (Matrix.of A : Matrix (Fin n) (Fin n) ℝ) ≠ 0)
    (hd_pos : ∀ k : Fin n, 0 < d k)
    (hDLT : ∀ k j : Fin n,
      higham9_2_rectRoundedLoopU fp (Nat.le_refl n) A k j =
        d k * higham9_2_rectRoundedLoopL fp (Nat.le_refl n) A j k)
    (hU_budget_le : ∀ k j : Fin n, k.val ≤ j.val →
      higham9_2_rectDoolittleUAbsBudget fp (Nat.le_refl n) A
          (higham9_2_rectRoundedLoopL fp (Nat.le_refl n) A)
          (higham9_2_rectRoundedLoopU fp (Nat.le_refl n) A) k j ≤
        gamma fp n *
          |higham9_2_rectRoundedLoopU fp (Nat.le_refl n) A k j|)
    (hL_budget_le : ∀ i k : Fin n, k.val < i.val →
      higham9_2_rectDoolittleLAbsBudget fp A
          (higham9_2_rectRoundedLoopL fp (Nat.le_refl n) A)
          (higham9_2_rectRoundedLoopU fp (Nat.le_refl n) A) i k ≤
        gamma fp n *
          |higham9_2_rectRoundedLoopL fp (Nat.le_refl n) A i k *
            higham9_2_rectRoundedLoopU fp (Nat.le_refl n) A k k|)
    (hγ_le_u : gamma fp n ≤ u) :
    let L_hat := higham9_2_rectRoundedLoopL fp (Nat.le_refl n) A
    let U_hat := higham9_2_rectRoundedLoopU fp (Nat.le_refl n) A
    let y_hat := fl_forwardSub fp n L_hat b
    let x_hat := fl_backSub fp n U_hat y_hat
    ∃ DeltaA : Fin n → Fin n → ℝ,
      (∀ i j, |DeltaA i j| ≤ higham9_14_h u * |A i j|) ∧
      (∀ i, ∑ j : Fin n, (A i j + DeltaA i j) * x_hat j = b i) := by
  dsimp only
  let hLU : LUFactSpec n A
      (higham9_2_rectRoundedLoopL fp (Nat.le_refl n) A)
      (higham9_2_rectRoundedLoopU fp (Nat.le_refl n) A) :=
    { L_diag := hStruct.L_diag
      L_upper_zero := hStruct.L_upper_zero
      U_lower_zero := hStruct.U_lower_zero
      product_eq := hLU_eq }
  exact
    higham9_14_source_h_bound_of_rectRoundedLoop_square_fl_triangular_solves_gamma_le
      fp n A b u hu hu_lt_one hn
      (hLU.det_ne_zero_iff_U_diag_ne_zero.mp hdetA)
      hU_budget_le hL_budget_le hγ_le_u
      (fun i j => by
        exact le_of_eq
          (higham9_12_spd_tridiag_absLU_eq_of_positive_DLT
            A
            (higham9_2_rectRoundedLoopL fp (Nat.le_refl n) A)
            (higham9_2_rectRoundedLoopU fp (Nat.le_refl n) A)
            d hStruct hLU_eq hd_pos hDLT i j))

/-- **Theorem 9.14**, SPD positive-`D L^T` executable rounded-loop source
`f(γ_n)` bound. -/
theorem higham9_14_spd_tridiag_positive_DLT_source_f_bound_of_rectRoundedLoop_square_fl_triangular_solves_gamma
    (fp : FPModel) (n : ℕ)
    (A : Fin n → Fin n → ℝ)
    (d b : Fin n → ℝ)
    (hn : gammaValid fp n)
    (hStruct : IsTridiagLU n
      (higham9_2_rectRoundedLoopL fp (Nat.le_refl n) A)
      (higham9_2_rectRoundedLoopU fp (Nat.le_refl n) A))
    (hLU_eq : ∀ i j : Fin n,
      ∑ k : Fin n,
          higham9_2_rectRoundedLoopL fp (Nat.le_refl n) A i k *
            higham9_2_rectRoundedLoopU fp (Nat.le_refl n) A k j =
        A i j)
    (hdetA : Matrix.det (Matrix.of A : Matrix (Fin n) (Fin n) ℝ) ≠ 0)
    (hd_pos : ∀ k : Fin n, 0 < d k)
    (hDLT : ∀ k j : Fin n,
      higham9_2_rectRoundedLoopU fp (Nat.le_refl n) A k j =
        d k * higham9_2_rectRoundedLoopL fp (Nat.le_refl n) A j k)
    (hU_budget_le : ∀ k j : Fin n, k.val ≤ j.val →
      higham9_2_rectDoolittleUAbsBudget fp (Nat.le_refl n) A
          (higham9_2_rectRoundedLoopL fp (Nat.le_refl n) A)
          (higham9_2_rectRoundedLoopU fp (Nat.le_refl n) A) k j ≤
        gamma fp n *
          |higham9_2_rectRoundedLoopU fp (Nat.le_refl n) A k j|)
    (hL_budget_le : ∀ i k : Fin n, k.val < i.val →
      higham9_2_rectDoolittleLAbsBudget fp A
          (higham9_2_rectRoundedLoopL fp (Nat.le_refl n) A)
          (higham9_2_rectRoundedLoopU fp (Nat.le_refl n) A) i k ≤
        gamma fp n *
          |higham9_2_rectRoundedLoopL fp (Nat.le_refl n) A i k *
            higham9_2_rectRoundedLoopU fp (Nat.le_refl n) A k k|) :
    let L_hat := higham9_2_rectRoundedLoopL fp (Nat.le_refl n) A
    let U_hat := higham9_2_rectRoundedLoopU fp (Nat.le_refl n) A
    let y_hat := fl_forwardSub fp n L_hat b
    let x_hat := fl_backSub fp n U_hat y_hat
    ∃ DeltaA : Fin n → Fin n → ℝ,
      (∀ i j, |DeltaA i j| ≤
        higham9_14_f (gamma fp n) * |A i j|) ∧
      (∀ i, ∑ j : Fin n, (A i j + DeltaA i j) * x_hat j = b i) :=
  higham9_14_spd_tridiag_positive_DLT_source_f_bound_of_rectRoundedLoop_square_fl_triangular_solves_gamma_le
    fp n A d b (gamma fp n) (gamma_nonneg fp hn) hn
    hStruct hLU_eq hdetA hd_pos hDLT hU_budget_le hL_budget_le le_rfl

/-- **Theorem 9.14**, SPD positive-`D L^T` executable rounded-loop final
`h(γ_n)` bound. -/
theorem higham9_14_spd_tridiag_positive_DLT_source_h_bound_of_rectRoundedLoop_square_fl_triangular_solves_gamma
    (fp : FPModel) (n : ℕ)
    (A : Fin n → Fin n → ℝ)
    (d b : Fin n → ℝ)
    (hn : gammaValid fp n)
    (hγ_lt_one : gamma fp n < 1)
    (hStruct : IsTridiagLU n
      (higham9_2_rectRoundedLoopL fp (Nat.le_refl n) A)
      (higham9_2_rectRoundedLoopU fp (Nat.le_refl n) A))
    (hLU_eq : ∀ i j : Fin n,
      ∑ k : Fin n,
          higham9_2_rectRoundedLoopL fp (Nat.le_refl n) A i k *
            higham9_2_rectRoundedLoopU fp (Nat.le_refl n) A k j =
        A i j)
    (hdetA : Matrix.det (Matrix.of A : Matrix (Fin n) (Fin n) ℝ) ≠ 0)
    (hd_pos : ∀ k : Fin n, 0 < d k)
    (hDLT : ∀ k j : Fin n,
      higham9_2_rectRoundedLoopU fp (Nat.le_refl n) A k j =
        d k * higham9_2_rectRoundedLoopL fp (Nat.le_refl n) A j k)
    (hU_budget_le : ∀ k j : Fin n, k.val ≤ j.val →
      higham9_2_rectDoolittleUAbsBudget fp (Nat.le_refl n) A
          (higham9_2_rectRoundedLoopL fp (Nat.le_refl n) A)
          (higham9_2_rectRoundedLoopU fp (Nat.le_refl n) A) k j ≤
        gamma fp n *
          |higham9_2_rectRoundedLoopU fp (Nat.le_refl n) A k j|)
    (hL_budget_le : ∀ i k : Fin n, k.val < i.val →
      higham9_2_rectDoolittleLAbsBudget fp A
          (higham9_2_rectRoundedLoopL fp (Nat.le_refl n) A)
          (higham9_2_rectRoundedLoopU fp (Nat.le_refl n) A) i k ≤
        gamma fp n *
          |higham9_2_rectRoundedLoopL fp (Nat.le_refl n) A i k *
            higham9_2_rectRoundedLoopU fp (Nat.le_refl n) A k k|) :
    let L_hat := higham9_2_rectRoundedLoopL fp (Nat.le_refl n) A
    let U_hat := higham9_2_rectRoundedLoopU fp (Nat.le_refl n) A
    let y_hat := fl_forwardSub fp n L_hat b
    let x_hat := fl_backSub fp n U_hat y_hat
    ∃ DeltaA : Fin n → Fin n → ℝ,
      (∀ i j, |DeltaA i j| ≤
        higham9_14_h (gamma fp n) * |A i j|) ∧
      (∀ i, ∑ j : Fin n, (A i j + DeltaA i j) * x_hat j = b i) :=
  higham9_14_spd_tridiag_positive_DLT_source_h_bound_of_rectRoundedLoop_square_fl_triangular_solves_gamma_le
    fp n A d b (gamma fp n) (gamma_nonneg fp hn) hγ_lt_one hn
    hStruct hLU_eq hdetA hd_pos hDLT hU_budget_le hL_budget_le le_rfl

/-- **Theorem 9.14**, SPD positive-`D L^T` executable rounded-loop source
`f(u)` bound, deriving nonsingularity from the source SPD hypothesis. -/
theorem higham9_14_spd_tridiag_positive_DLT_source_f_bound_of_spd_rectRoundedLoop_square_fl_triangular_solves_gamma_le
    (fp : FPModel) (n : ℕ)
    (A : Fin n → Fin n → ℝ)
    (d b : Fin n → ℝ)
    (u : ℝ) (hu : 0 ≤ u)
    (hn : gammaValid fp n)
    (hSPD : IsSymPosDef n A)
    (hStruct : IsTridiagLU n
      (higham9_2_rectRoundedLoopL fp (Nat.le_refl n) A)
      (higham9_2_rectRoundedLoopU fp (Nat.le_refl n) A))
    (hLU_eq : ∀ i j : Fin n,
      ∑ k : Fin n,
          higham9_2_rectRoundedLoopL fp (Nat.le_refl n) A i k *
            higham9_2_rectRoundedLoopU fp (Nat.le_refl n) A k j =
        A i j)
    (hd_pos : ∀ k : Fin n, 0 < d k)
    (hDLT : ∀ k j : Fin n,
      higham9_2_rectRoundedLoopU fp (Nat.le_refl n) A k j =
        d k * higham9_2_rectRoundedLoopL fp (Nat.le_refl n) A j k)
    (hU_budget_le : ∀ k j : Fin n, k.val ≤ j.val →
      higham9_2_rectDoolittleUAbsBudget fp (Nat.le_refl n) A
          (higham9_2_rectRoundedLoopL fp (Nat.le_refl n) A)
          (higham9_2_rectRoundedLoopU fp (Nat.le_refl n) A) k j ≤
        gamma fp n *
          |higham9_2_rectRoundedLoopU fp (Nat.le_refl n) A k j|)
    (hL_budget_le : ∀ i k : Fin n, k.val < i.val →
      higham9_2_rectDoolittleLAbsBudget fp A
          (higham9_2_rectRoundedLoopL fp (Nat.le_refl n) A)
          (higham9_2_rectRoundedLoopU fp (Nat.le_refl n) A) i k ≤
        gamma fp n *
          |higham9_2_rectRoundedLoopL fp (Nat.le_refl n) A i k *
            higham9_2_rectRoundedLoopU fp (Nat.le_refl n) A k k|)
    (hγ_le_u : gamma fp n ≤ u) :
    let L_hat := higham9_2_rectRoundedLoopL fp (Nat.le_refl n) A
    let U_hat := higham9_2_rectRoundedLoopU fp (Nat.le_refl n) A
    let y_hat := fl_forwardSub fp n L_hat b
    let x_hat := fl_backSub fp n U_hat y_hat
    ∃ DeltaA : Fin n → Fin n → ℝ,
      (∀ i j, |DeltaA i j| ≤ higham9_14_f u * |A i j|) ∧
      (∀ i, ∑ j : Fin n, (A i j + DeltaA i j) * x_hat j = b i) :=
  higham9_14_spd_tridiag_positive_DLT_source_f_bound_of_rectRoundedLoop_square_fl_triangular_solves_gamma_le
    fp n A d b u hu hn hStruct hLU_eq
    (by simpa using isSymPosDef_det_ne_zero A hSPD)
    hd_pos hDLT hU_budget_le hL_budget_le hγ_le_u

/-- **Theorem 9.14**, SPD positive-`D L^T` executable rounded-loop final
`h(u)` bound, deriving nonsingularity from the source SPD hypothesis. -/
theorem higham9_14_spd_tridiag_positive_DLT_source_h_bound_of_spd_rectRoundedLoop_square_fl_triangular_solves_gamma_le
    (fp : FPModel) (n : ℕ)
    (A : Fin n → Fin n → ℝ)
    (d b : Fin n → ℝ)
    (u : ℝ) (hu : 0 ≤ u) (hu_lt_one : u < 1)
    (hn : gammaValid fp n)
    (hSPD : IsSymPosDef n A)
    (hStruct : IsTridiagLU n
      (higham9_2_rectRoundedLoopL fp (Nat.le_refl n) A)
      (higham9_2_rectRoundedLoopU fp (Nat.le_refl n) A))
    (hLU_eq : ∀ i j : Fin n,
      ∑ k : Fin n,
          higham9_2_rectRoundedLoopL fp (Nat.le_refl n) A i k *
            higham9_2_rectRoundedLoopU fp (Nat.le_refl n) A k j =
        A i j)
    (hd_pos : ∀ k : Fin n, 0 < d k)
    (hDLT : ∀ k j : Fin n,
      higham9_2_rectRoundedLoopU fp (Nat.le_refl n) A k j =
        d k * higham9_2_rectRoundedLoopL fp (Nat.le_refl n) A j k)
    (hU_budget_le : ∀ k j : Fin n, k.val ≤ j.val →
      higham9_2_rectDoolittleUAbsBudget fp (Nat.le_refl n) A
          (higham9_2_rectRoundedLoopL fp (Nat.le_refl n) A)
          (higham9_2_rectRoundedLoopU fp (Nat.le_refl n) A) k j ≤
        gamma fp n *
          |higham9_2_rectRoundedLoopU fp (Nat.le_refl n) A k j|)
    (hL_budget_le : ∀ i k : Fin n, k.val < i.val →
      higham9_2_rectDoolittleLAbsBudget fp A
          (higham9_2_rectRoundedLoopL fp (Nat.le_refl n) A)
          (higham9_2_rectRoundedLoopU fp (Nat.le_refl n) A) i k ≤
        gamma fp n *
          |higham9_2_rectRoundedLoopL fp (Nat.le_refl n) A i k *
            higham9_2_rectRoundedLoopU fp (Nat.le_refl n) A k k|)
    (hγ_le_u : gamma fp n ≤ u) :
    let L_hat := higham9_2_rectRoundedLoopL fp (Nat.le_refl n) A
    let U_hat := higham9_2_rectRoundedLoopU fp (Nat.le_refl n) A
    let y_hat := fl_forwardSub fp n L_hat b
    let x_hat := fl_backSub fp n U_hat y_hat
    ∃ DeltaA : Fin n → Fin n → ℝ,
      (∀ i j, |DeltaA i j| ≤ higham9_14_h u * |A i j|) ∧
      (∀ i, ∑ j : Fin n, (A i j + DeltaA i j) * x_hat j = b i) :=
  higham9_14_spd_tridiag_positive_DLT_source_h_bound_of_rectRoundedLoop_square_fl_triangular_solves_gamma_le
    fp n A d b u hu hu_lt_one hn hStruct hLU_eq
    (by simpa using isSymPosDef_det_ne_zero A hSPD)
    hd_pos hDLT hU_budget_le hL_budget_le hγ_le_u

/-- **Theorem 9.14**, SPD positive-`D L^T` executable rounded-loop source
`f(γ_n)` bound, deriving nonsingularity from SPD. -/
theorem higham9_14_spd_tridiag_positive_DLT_source_f_bound_of_spd_rectRoundedLoop_square_fl_triangular_solves_gamma
    (fp : FPModel) (n : ℕ)
    (A : Fin n → Fin n → ℝ)
    (d b : Fin n → ℝ)
    (hn : gammaValid fp n)
    (hSPD : IsSymPosDef n A)
    (hStruct : IsTridiagLU n
      (higham9_2_rectRoundedLoopL fp (Nat.le_refl n) A)
      (higham9_2_rectRoundedLoopU fp (Nat.le_refl n) A))
    (hLU_eq : ∀ i j : Fin n,
      ∑ k : Fin n,
          higham9_2_rectRoundedLoopL fp (Nat.le_refl n) A i k *
            higham9_2_rectRoundedLoopU fp (Nat.le_refl n) A k j =
        A i j)
    (hd_pos : ∀ k : Fin n, 0 < d k)
    (hDLT : ∀ k j : Fin n,
      higham9_2_rectRoundedLoopU fp (Nat.le_refl n) A k j =
        d k * higham9_2_rectRoundedLoopL fp (Nat.le_refl n) A j k)
    (hU_budget_le : ∀ k j : Fin n, k.val ≤ j.val →
      higham9_2_rectDoolittleUAbsBudget fp (Nat.le_refl n) A
          (higham9_2_rectRoundedLoopL fp (Nat.le_refl n) A)
          (higham9_2_rectRoundedLoopU fp (Nat.le_refl n) A) k j ≤
        gamma fp n *
          |higham9_2_rectRoundedLoopU fp (Nat.le_refl n) A k j|)
    (hL_budget_le : ∀ i k : Fin n, k.val < i.val →
      higham9_2_rectDoolittleLAbsBudget fp A
          (higham9_2_rectRoundedLoopL fp (Nat.le_refl n) A)
          (higham9_2_rectRoundedLoopU fp (Nat.le_refl n) A) i k ≤
        gamma fp n *
          |higham9_2_rectRoundedLoopL fp (Nat.le_refl n) A i k *
            higham9_2_rectRoundedLoopU fp (Nat.le_refl n) A k k|) :
    let L_hat := higham9_2_rectRoundedLoopL fp (Nat.le_refl n) A
    let U_hat := higham9_2_rectRoundedLoopU fp (Nat.le_refl n) A
    let y_hat := fl_forwardSub fp n L_hat b
    let x_hat := fl_backSub fp n U_hat y_hat
    ∃ DeltaA : Fin n → Fin n → ℝ,
      (∀ i j, |DeltaA i j| ≤
        higham9_14_f (gamma fp n) * |A i j|) ∧
      (∀ i, ∑ j : Fin n, (A i j + DeltaA i j) * x_hat j = b i) :=
  higham9_14_spd_tridiag_positive_DLT_source_f_bound_of_rectRoundedLoop_square_fl_triangular_solves_gamma
    fp n A d b hn hStruct hLU_eq
    (by simpa using isSymPosDef_det_ne_zero A hSPD)
    hd_pos hDLT hU_budget_le hL_budget_le

/-- **Theorem 9.14**, SPD positive-`D L^T` executable rounded-loop final
`h(γ_n)` bound, deriving nonsingularity from SPD. -/
theorem higham9_14_spd_tridiag_positive_DLT_source_h_bound_of_spd_rectRoundedLoop_square_fl_triangular_solves_gamma
    (fp : FPModel) (n : ℕ)
    (A : Fin n → Fin n → ℝ)
    (d b : Fin n → ℝ)
    (hn : gammaValid fp n)
    (hγ_lt_one : gamma fp n < 1)
    (hSPD : IsSymPosDef n A)
    (hStruct : IsTridiagLU n
      (higham9_2_rectRoundedLoopL fp (Nat.le_refl n) A)
      (higham9_2_rectRoundedLoopU fp (Nat.le_refl n) A))
    (hLU_eq : ∀ i j : Fin n,
      ∑ k : Fin n,
          higham9_2_rectRoundedLoopL fp (Nat.le_refl n) A i k *
            higham9_2_rectRoundedLoopU fp (Nat.le_refl n) A k j =
        A i j)
    (hd_pos : ∀ k : Fin n, 0 < d k)
    (hDLT : ∀ k j : Fin n,
      higham9_2_rectRoundedLoopU fp (Nat.le_refl n) A k j =
        d k * higham9_2_rectRoundedLoopL fp (Nat.le_refl n) A j k)
    (hU_budget_le : ∀ k j : Fin n, k.val ≤ j.val →
      higham9_2_rectDoolittleUAbsBudget fp (Nat.le_refl n) A
          (higham9_2_rectRoundedLoopL fp (Nat.le_refl n) A)
          (higham9_2_rectRoundedLoopU fp (Nat.le_refl n) A) k j ≤
        gamma fp n *
          |higham9_2_rectRoundedLoopU fp (Nat.le_refl n) A k j|)
    (hL_budget_le : ∀ i k : Fin n, k.val < i.val →
      higham9_2_rectDoolittleLAbsBudget fp A
          (higham9_2_rectRoundedLoopL fp (Nat.le_refl n) A)
          (higham9_2_rectRoundedLoopU fp (Nat.le_refl n) A) i k ≤
        gamma fp n *
          |higham9_2_rectRoundedLoopL fp (Nat.le_refl n) A i k *
            higham9_2_rectRoundedLoopU fp (Nat.le_refl n) A k k|) :
    let L_hat := higham9_2_rectRoundedLoopL fp (Nat.le_refl n) A
    let U_hat := higham9_2_rectRoundedLoopU fp (Nat.le_refl n) A
    let y_hat := fl_forwardSub fp n L_hat b
    let x_hat := fl_backSub fp n U_hat y_hat
    ∃ DeltaA : Fin n → Fin n → ℝ,
      (∀ i j, |DeltaA i j| ≤
        higham9_14_h (gamma fp n) * |A i j|) ∧
      (∀ i, ∑ j : Fin n, (A i j + DeltaA i j) * x_hat j = b i) :=
  higham9_14_spd_tridiag_positive_DLT_source_h_bound_of_rectRoundedLoop_square_fl_triangular_solves_gamma
    fp n A d b hn hγ_lt_one hStruct hLU_eq
    (by simpa using isSymPosDef_det_ne_zero A hSPD)
    hd_pos hDLT hU_budget_le hL_budget_le

/-- **Theorem 9.14**, nonnegative-LU executable rounded-loop source `f(u)`
bound.

This is the concrete-loop counterpart of the rounded-stage nonnegative-LU
wrapper: the loop supplies the factors, and Theorem 9.12 supplies
`|Lhat||Uhat| = |A|`. -/
theorem higham9_14_nonnegative_lu_source_f_bound_of_rectRoundedLoop_square_fl_triangular_solves_gamma_le
    (fp : FPModel) (n : ℕ)
    (A : Fin n → Fin n → ℝ)
    (b : Fin n → ℝ)
    (u : ℝ) (hu : 0 ≤ u)
    (hn : gammaValid fp n)
    (hNonneg : HasNonnegLUFactors n A
      (higham9_2_rectRoundedLoopL fp (Nat.le_refl n) A)
      (higham9_2_rectRoundedLoopU fp (Nat.le_refl n) A))
    (hdetA : Matrix.det (Matrix.of A : Matrix (Fin n) (Fin n) ℝ) ≠ 0)
    (hU_budget_le : ∀ k j : Fin n, k.val ≤ j.val →
      higham9_2_rectDoolittleUAbsBudget fp (Nat.le_refl n) A
          (higham9_2_rectRoundedLoopL fp (Nat.le_refl n) A)
          (higham9_2_rectRoundedLoopU fp (Nat.le_refl n) A) k j ≤
        gamma fp n *
          |higham9_2_rectRoundedLoopU fp (Nat.le_refl n) A k j|)
    (hL_budget_le : ∀ i k : Fin n, k.val < i.val →
      higham9_2_rectDoolittleLAbsBudget fp A
          (higham9_2_rectRoundedLoopL fp (Nat.le_refl n) A)
          (higham9_2_rectRoundedLoopU fp (Nat.le_refl n) A) i k ≤
        gamma fp n *
          |higham9_2_rectRoundedLoopL fp (Nat.le_refl n) A i k *
            higham9_2_rectRoundedLoopU fp (Nat.le_refl n) A k k|)
    (hγ_le_u : gamma fp n ≤ u) :
    let L_hat := higham9_2_rectRoundedLoopL fp (Nat.le_refl n) A
    let U_hat := higham9_2_rectRoundedLoopU fp (Nat.le_refl n) A
    let y_hat := fl_forwardSub fp n L_hat b
    let x_hat := fl_backSub fp n U_hat y_hat
    ∃ DeltaA : Fin n → Fin n → ℝ,
      (∀ i j, |DeltaA i j| ≤ higham9_14_f u * |A i j|) ∧
      (∀ i, ∑ j : Fin n, (A i j + DeltaA i j) * x_hat j = b i) := by
  dsimp only
  simpa [one_mul] using
    (higham9_14_source_f_bound_of_rectRoundedLoop_square_fl_triangular_solves_gamma_le
      fp n A b 1 u hu hn
      (hNonneg.1.det_ne_zero_iff_U_diag_ne_zero.mp hdetA)
      hU_budget_le hL_budget_le hγ_le_u
      (fun i j => by
        simpa [one_mul] using
          le_of_eq
            (higham9_12_nonneg_lu_optimal_growth n A
              (higham9_2_rectRoundedLoopL fp (Nat.le_refl n) A)
              (higham9_2_rectRoundedLoopU fp (Nat.le_refl n) A)
              hNonneg i j)))

/-- **Theorem 9.14**, nonnegative-LU executable rounded-loop final `h(u)`
bound. -/
theorem higham9_14_nonnegative_lu_source_h_bound_of_rectRoundedLoop_square_fl_triangular_solves_gamma_le
    (fp : FPModel) (n : ℕ)
    (A : Fin n → Fin n → ℝ)
    (b : Fin n → ℝ)
    (u : ℝ) (hu : 0 ≤ u) (hu_lt_one : u < 1)
    (hn : gammaValid fp n)
    (hNonneg : HasNonnegLUFactors n A
      (higham9_2_rectRoundedLoopL fp (Nat.le_refl n) A)
      (higham9_2_rectRoundedLoopU fp (Nat.le_refl n) A))
    (hdetA : Matrix.det (Matrix.of A : Matrix (Fin n) (Fin n) ℝ) ≠ 0)
    (hU_budget_le : ∀ k j : Fin n, k.val ≤ j.val →
      higham9_2_rectDoolittleUAbsBudget fp (Nat.le_refl n) A
          (higham9_2_rectRoundedLoopL fp (Nat.le_refl n) A)
          (higham9_2_rectRoundedLoopU fp (Nat.le_refl n) A) k j ≤
        gamma fp n *
          |higham9_2_rectRoundedLoopU fp (Nat.le_refl n) A k j|)
    (hL_budget_le : ∀ i k : Fin n, k.val < i.val →
      higham9_2_rectDoolittleLAbsBudget fp A
          (higham9_2_rectRoundedLoopL fp (Nat.le_refl n) A)
          (higham9_2_rectRoundedLoopU fp (Nat.le_refl n) A) i k ≤
        gamma fp n *
          |higham9_2_rectRoundedLoopL fp (Nat.le_refl n) A i k *
            higham9_2_rectRoundedLoopU fp (Nat.le_refl n) A k k|)
    (hγ_le_u : gamma fp n ≤ u) :
    let L_hat := higham9_2_rectRoundedLoopL fp (Nat.le_refl n) A
    let U_hat := higham9_2_rectRoundedLoopU fp (Nat.le_refl n) A
    let y_hat := fl_forwardSub fp n L_hat b
    let x_hat := fl_backSub fp n U_hat y_hat
    ∃ DeltaA : Fin n → Fin n → ℝ,
      (∀ i j, |DeltaA i j| ≤ higham9_14_h u * |A i j|) ∧
      (∀ i, ∑ j : Fin n, (A i j + DeltaA i j) * x_hat j = b i) := by
  dsimp only
  exact
    higham9_14_source_h_bound_of_rectRoundedLoop_square_fl_triangular_solves_gamma_le
      fp n A b u hu hu_lt_one hn
      (hNonneg.1.det_ne_zero_iff_U_diag_ne_zero.mp hdetA)
      hU_budget_le hL_budget_le hγ_le_u
      (fun i j => by
        exact le_of_eq
          (higham9_12_nonneg_lu_optimal_growth n A
            (higham9_2_rectRoundedLoopL fp (Nat.le_refl n) A)
            (higham9_2_rectRoundedLoopU fp (Nat.le_refl n) A)
            hNonneg i j))

/-- **Theorem 9.14**, nonnegative-LU executable rounded-loop source
`f(γ_n)` bound. -/
theorem higham9_14_nonnegative_lu_source_f_bound_of_rectRoundedLoop_square_fl_triangular_solves_gamma
    (fp : FPModel) (n : ℕ)
    (A : Fin n → Fin n → ℝ)
    (b : Fin n → ℝ)
    (hn : gammaValid fp n)
    (hNonneg : HasNonnegLUFactors n A
      (higham9_2_rectRoundedLoopL fp (Nat.le_refl n) A)
      (higham9_2_rectRoundedLoopU fp (Nat.le_refl n) A))
    (hdetA : Matrix.det (Matrix.of A : Matrix (Fin n) (Fin n) ℝ) ≠ 0)
    (hU_budget_le : ∀ k j : Fin n, k.val ≤ j.val →
      higham9_2_rectDoolittleUAbsBudget fp (Nat.le_refl n) A
          (higham9_2_rectRoundedLoopL fp (Nat.le_refl n) A)
          (higham9_2_rectRoundedLoopU fp (Nat.le_refl n) A) k j ≤
        gamma fp n *
          |higham9_2_rectRoundedLoopU fp (Nat.le_refl n) A k j|)
    (hL_budget_le : ∀ i k : Fin n, k.val < i.val →
      higham9_2_rectDoolittleLAbsBudget fp A
          (higham9_2_rectRoundedLoopL fp (Nat.le_refl n) A)
          (higham9_2_rectRoundedLoopU fp (Nat.le_refl n) A) i k ≤
        gamma fp n *
          |higham9_2_rectRoundedLoopL fp (Nat.le_refl n) A i k *
            higham9_2_rectRoundedLoopU fp (Nat.le_refl n) A k k|) :
    let L_hat := higham9_2_rectRoundedLoopL fp (Nat.le_refl n) A
    let U_hat := higham9_2_rectRoundedLoopU fp (Nat.le_refl n) A
    let y_hat := fl_forwardSub fp n L_hat b
    let x_hat := fl_backSub fp n U_hat y_hat
    ∃ DeltaA : Fin n → Fin n → ℝ,
      (∀ i j, |DeltaA i j| ≤
        higham9_14_f (gamma fp n) * |A i j|) ∧
      (∀ i, ∑ j : Fin n, (A i j + DeltaA i j) * x_hat j = b i) :=
  higham9_14_nonnegative_lu_source_f_bound_of_rectRoundedLoop_square_fl_triangular_solves_gamma_le
    fp n A b (gamma fp n) (gamma_nonneg fp hn) hn
    hNonneg hdetA hU_budget_le hL_budget_le le_rfl

/-- **Theorem 9.14**, nonnegative-LU executable rounded-loop final
`h(γ_n)` bound. -/
theorem higham9_14_nonnegative_lu_source_h_bound_of_rectRoundedLoop_square_fl_triangular_solves_gamma
    (fp : FPModel) (n : ℕ)
    (A : Fin n → Fin n → ℝ)
    (b : Fin n → ℝ)
    (hn : gammaValid fp n)
    (hγ_lt_one : gamma fp n < 1)
    (hNonneg : HasNonnegLUFactors n A
      (higham9_2_rectRoundedLoopL fp (Nat.le_refl n) A)
      (higham9_2_rectRoundedLoopU fp (Nat.le_refl n) A))
    (hdetA : Matrix.det (Matrix.of A : Matrix (Fin n) (Fin n) ℝ) ≠ 0)
    (hU_budget_le : ∀ k j : Fin n, k.val ≤ j.val →
      higham9_2_rectDoolittleUAbsBudget fp (Nat.le_refl n) A
          (higham9_2_rectRoundedLoopL fp (Nat.le_refl n) A)
          (higham9_2_rectRoundedLoopU fp (Nat.le_refl n) A) k j ≤
        gamma fp n *
          |higham9_2_rectRoundedLoopU fp (Nat.le_refl n) A k j|)
    (hL_budget_le : ∀ i k : Fin n, k.val < i.val →
      higham9_2_rectDoolittleLAbsBudget fp A
          (higham9_2_rectRoundedLoopL fp (Nat.le_refl n) A)
          (higham9_2_rectRoundedLoopU fp (Nat.le_refl n) A) i k ≤
        gamma fp n *
          |higham9_2_rectRoundedLoopL fp (Nat.le_refl n) A i k *
            higham9_2_rectRoundedLoopU fp (Nat.le_refl n) A k k|) :
    let L_hat := higham9_2_rectRoundedLoopL fp (Nat.le_refl n) A
    let U_hat := higham9_2_rectRoundedLoopU fp (Nat.le_refl n) A
    let y_hat := fl_forwardSub fp n L_hat b
    let x_hat := fl_backSub fp n U_hat y_hat
    ∃ DeltaA : Fin n → Fin n → ℝ,
      (∀ i j, |DeltaA i j| ≤
        higham9_14_h (gamma fp n) * |A i j|) ∧
      (∀ i, ∑ j : Fin n, (A i j + DeltaA i j) * x_hat j = b i) :=
  higham9_14_nonnegative_lu_source_h_bound_of_rectRoundedLoop_square_fl_triangular_solves_gamma_le
    fp n A b (gamma fp n) (gamma_nonneg fp hn) hγ_lt_one hn
    hNonneg hdetA hU_budget_le hL_budget_le le_rfl

/-- **Theorem 9.14**, Matrix-facing nonnegative-LU executable rounded-loop
source `f(u)` bound. -/
theorem higham9_14_matrix_nonnegative_lu_source_f_bound_of_rectRoundedLoop_square_fl_triangular_solves_gamma_le
    (fp : FPModel) (n : ℕ)
    (A : Matrix (Fin n) (Fin n) ℝ)
    (b : Fin n → ℝ)
    (u : ℝ) (hu : 0 ≤ u)
    (hn : gammaValid fp n)
    (hNonneg : HasNonnegLUFactors n A
      (higham9_2_rectRoundedLoopL fp (Nat.le_refl n) A)
      (higham9_2_rectRoundedLoopU fp (Nat.le_refl n) A))
    (hdetA : Matrix.det A ≠ 0)
    (hU_budget_le : ∀ k j : Fin n, k.val ≤ j.val →
      higham9_2_rectDoolittleUAbsBudget fp (Nat.le_refl n) A
          (higham9_2_rectRoundedLoopL fp (Nat.le_refl n) A)
          (higham9_2_rectRoundedLoopU fp (Nat.le_refl n) A) k j ≤
        gamma fp n *
          |higham9_2_rectRoundedLoopU fp (Nat.le_refl n) A k j|)
    (hL_budget_le : ∀ i k : Fin n, k.val < i.val →
      higham9_2_rectDoolittleLAbsBudget fp A
          (higham9_2_rectRoundedLoopL fp (Nat.le_refl n) A)
          (higham9_2_rectRoundedLoopU fp (Nat.le_refl n) A) i k ≤
        gamma fp n *
          |higham9_2_rectRoundedLoopL fp (Nat.le_refl n) A i k *
            higham9_2_rectRoundedLoopU fp (Nat.le_refl n) A k k|)
    (hγ_le_u : gamma fp n ≤ u) :
    let L_hat := higham9_2_rectRoundedLoopL fp (Nat.le_refl n) A
    let U_hat := higham9_2_rectRoundedLoopU fp (Nat.le_refl n) A
    let y_hat := fl_forwardSub fp n L_hat b
    let x_hat := fl_backSub fp n U_hat y_hat
    ∃ DeltaA : Matrix (Fin n) (Fin n) ℝ,
      (∀ i j, |DeltaA i j| ≤ higham9_14_f u * |A i j|) ∧
      Matrix.mulVec (fun i j => A i j + DeltaA i j) x_hat = b := by
  dsimp only
  exact
    higham9_14_matrix_source_f_bound_of_rectRoundedLoop_square_fl_triangular_solves_absLU_le_absA_gamma_le
      fp n A b u hu hn
      (hNonneg.1.det_ne_zero_iff_U_diag_ne_zero.mp hdetA)
      hU_budget_le hL_budget_le hγ_le_u
      (fun i j =>
        le_of_eq
          (higham9_12_nonneg_lu_optimal_growth n A
            (higham9_2_rectRoundedLoopL fp (Nat.le_refl n) A)
            (higham9_2_rectRoundedLoopU fp (Nat.le_refl n) A)
            hNonneg i j))

/-- **Theorem 9.14**, Matrix-facing nonnegative-LU executable rounded-loop
final `h(u)` bound. -/
theorem higham9_14_matrix_nonnegative_lu_source_h_bound_of_rectRoundedLoop_square_fl_triangular_solves_gamma_le
    (fp : FPModel) (n : ℕ)
    (A : Matrix (Fin n) (Fin n) ℝ)
    (b : Fin n → ℝ)
    (u : ℝ) (hu : 0 ≤ u) (hu_lt_one : u < 1)
    (hn : gammaValid fp n)
    (hNonneg : HasNonnegLUFactors n A
      (higham9_2_rectRoundedLoopL fp (Nat.le_refl n) A)
      (higham9_2_rectRoundedLoopU fp (Nat.le_refl n) A))
    (hdetA : Matrix.det A ≠ 0)
    (hU_budget_le : ∀ k j : Fin n, k.val ≤ j.val →
      higham9_2_rectDoolittleUAbsBudget fp (Nat.le_refl n) A
          (higham9_2_rectRoundedLoopL fp (Nat.le_refl n) A)
          (higham9_2_rectRoundedLoopU fp (Nat.le_refl n) A) k j ≤
        gamma fp n *
          |higham9_2_rectRoundedLoopU fp (Nat.le_refl n) A k j|)
    (hL_budget_le : ∀ i k : Fin n, k.val < i.val →
      higham9_2_rectDoolittleLAbsBudget fp A
          (higham9_2_rectRoundedLoopL fp (Nat.le_refl n) A)
          (higham9_2_rectRoundedLoopU fp (Nat.le_refl n) A) i k ≤
        gamma fp n *
          |higham9_2_rectRoundedLoopL fp (Nat.le_refl n) A i k *
            higham9_2_rectRoundedLoopU fp (Nat.le_refl n) A k k|)
    (hγ_le_u : gamma fp n ≤ u) :
    let L_hat := higham9_2_rectRoundedLoopL fp (Nat.le_refl n) A
    let U_hat := higham9_2_rectRoundedLoopU fp (Nat.le_refl n) A
    let y_hat := fl_forwardSub fp n L_hat b
    let x_hat := fl_backSub fp n U_hat y_hat
    ∃ DeltaA : Matrix (Fin n) (Fin n) ℝ,
      (∀ i j, |DeltaA i j| ≤ higham9_14_h u * |A i j|) ∧
      Matrix.mulVec (fun i j => A i j + DeltaA i j) x_hat = b := by
  dsimp only
  exact
    higham9_14_matrix_source_h_bound_of_rectRoundedLoop_square_fl_triangular_solves_absLU_le_absA_gamma_le
      fp n A b u hu hu_lt_one hn
      (hNonneg.1.det_ne_zero_iff_U_diag_ne_zero.mp hdetA)
      hU_budget_le hL_budget_le hγ_le_u
      (fun i j =>
        le_of_eq
          (higham9_12_nonneg_lu_optimal_growth n A
            (higham9_2_rectRoundedLoopL fp (Nat.le_refl n) A)
            (higham9_2_rectRoundedLoopU fp (Nat.le_refl n) A)
            hNonneg i j))

/-- **Theorem 9.14**, Matrix-facing nonnegative-LU executable rounded-loop
source `f(γ_n)` bound. -/
theorem higham9_14_matrix_nonnegative_lu_source_f_bound_of_rectRoundedLoop_square_fl_triangular_solves_gamma
    (fp : FPModel) (n : ℕ)
    (A : Matrix (Fin n) (Fin n) ℝ)
    (b : Fin n → ℝ)
    (hn : gammaValid fp n)
    (hNonneg : HasNonnegLUFactors n A
      (higham9_2_rectRoundedLoopL fp (Nat.le_refl n) A)
      (higham9_2_rectRoundedLoopU fp (Nat.le_refl n) A))
    (hdetA : Matrix.det A ≠ 0)
    (hU_budget_le : ∀ k j : Fin n, k.val ≤ j.val →
      higham9_2_rectDoolittleUAbsBudget fp (Nat.le_refl n) A
          (higham9_2_rectRoundedLoopL fp (Nat.le_refl n) A)
          (higham9_2_rectRoundedLoopU fp (Nat.le_refl n) A) k j ≤
        gamma fp n *
          |higham9_2_rectRoundedLoopU fp (Nat.le_refl n) A k j|)
    (hL_budget_le : ∀ i k : Fin n, k.val < i.val →
      higham9_2_rectDoolittleLAbsBudget fp A
          (higham9_2_rectRoundedLoopL fp (Nat.le_refl n) A)
          (higham9_2_rectRoundedLoopU fp (Nat.le_refl n) A) i k ≤
        gamma fp n *
          |higham9_2_rectRoundedLoopL fp (Nat.le_refl n) A i k *
            higham9_2_rectRoundedLoopU fp (Nat.le_refl n) A k k|) :
    let L_hat := higham9_2_rectRoundedLoopL fp (Nat.le_refl n) A
    let U_hat := higham9_2_rectRoundedLoopU fp (Nat.le_refl n) A
    let y_hat := fl_forwardSub fp n L_hat b
    let x_hat := fl_backSub fp n U_hat y_hat
    ∃ DeltaA : Matrix (Fin n) (Fin n) ℝ,
      (∀ i j, |DeltaA i j| ≤
        higham9_14_f (gamma fp n) * |A i j|) ∧
      Matrix.mulVec (fun i j => A i j + DeltaA i j) x_hat = b :=
  higham9_14_matrix_nonnegative_lu_source_f_bound_of_rectRoundedLoop_square_fl_triangular_solves_gamma_le
    fp n A b (gamma fp n) (gamma_nonneg fp hn) hn
    hNonneg hdetA hU_budget_le hL_budget_le le_rfl

/-- **Theorem 9.14**, Matrix-facing nonnegative-LU executable rounded-loop
final `h(γ_n)` bound. -/
theorem higham9_14_matrix_nonnegative_lu_source_h_bound_of_rectRoundedLoop_square_fl_triangular_solves_gamma
    (fp : FPModel) (n : ℕ)
    (A : Matrix (Fin n) (Fin n) ℝ)
    (b : Fin n → ℝ)
    (hn : gammaValid fp n)
    (hγ_lt_one : gamma fp n < 1)
    (hNonneg : HasNonnegLUFactors n A
      (higham9_2_rectRoundedLoopL fp (Nat.le_refl n) A)
      (higham9_2_rectRoundedLoopU fp (Nat.le_refl n) A))
    (hdetA : Matrix.det A ≠ 0)
    (hU_budget_le : ∀ k j : Fin n, k.val ≤ j.val →
      higham9_2_rectDoolittleUAbsBudget fp (Nat.le_refl n) A
          (higham9_2_rectRoundedLoopL fp (Nat.le_refl n) A)
          (higham9_2_rectRoundedLoopU fp (Nat.le_refl n) A) k j ≤
        gamma fp n *
          |higham9_2_rectRoundedLoopU fp (Nat.le_refl n) A k j|)
    (hL_budget_le : ∀ i k : Fin n, k.val < i.val →
      higham9_2_rectDoolittleLAbsBudget fp A
          (higham9_2_rectRoundedLoopL fp (Nat.le_refl n) A)
          (higham9_2_rectRoundedLoopU fp (Nat.le_refl n) A) i k ≤
        gamma fp n *
          |higham9_2_rectRoundedLoopL fp (Nat.le_refl n) A i k *
            higham9_2_rectRoundedLoopU fp (Nat.le_refl n) A k k|) :
    let L_hat := higham9_2_rectRoundedLoopL fp (Nat.le_refl n) A
    let U_hat := higham9_2_rectRoundedLoopU fp (Nat.le_refl n) A
    let y_hat := fl_forwardSub fp n L_hat b
    let x_hat := fl_backSub fp n U_hat y_hat
    ∃ DeltaA : Matrix (Fin n) (Fin n) ℝ,
      (∀ i j, |DeltaA i j| ≤
        higham9_14_h (gamma fp n) * |A i j|) ∧
      Matrix.mulVec (fun i j => A i j + DeltaA i j) x_hat = b :=
  higham9_14_matrix_nonnegative_lu_source_h_bound_of_rectRoundedLoop_square_fl_triangular_solves_gamma_le
    fp n A b (gamma fp n) (gamma_nonneg fp hn) hγ_lt_one hn
    hNonneg hdetA hU_budget_le hL_budget_le le_rfl

/-- **Theorem 9.14**, M-matrix executable rounded-loop source `f(u)` bound. -/
theorem higham9_14_mmatrix_lu_source_f_bound_of_rectRoundedLoop_square_fl_triangular_solves_gamma_le
    (fp : FPModel) (n : ℕ)
    (A : Fin n → Fin n → ℝ)
    (b : Fin n → ℝ)
    (u : ℝ) (hu : 0 ≤ u)
    (hn : gammaValid fp n)
    (hM : IsMMatrix n A)
    (hLU : LUFactSpec n A
      (higham9_2_rectRoundedLoopL fp (Nat.le_refl n) A)
      (higham9_2_rectRoundedLoopU fp (Nat.le_refl n) A))
    (hdetA : Matrix.det (Matrix.of A : Matrix (Fin n) (Fin n) ℝ) ≠ 0)
    (hL_nn : ∀ i k : Fin n,
      0 ≤ higham9_2_rectRoundedLoopL fp (Nat.le_refl n) A i k)
    (hU_nn : ∀ k j : Fin n,
      0 ≤ higham9_2_rectRoundedLoopU fp (Nat.le_refl n) A k j)
    (hU_budget_le : ∀ k j : Fin n, k.val ≤ j.val →
      higham9_2_rectDoolittleUAbsBudget fp (Nat.le_refl n) A
          (higham9_2_rectRoundedLoopL fp (Nat.le_refl n) A)
          (higham9_2_rectRoundedLoopU fp (Nat.le_refl n) A) k j ≤
        gamma fp n *
          |higham9_2_rectRoundedLoopU fp (Nat.le_refl n) A k j|)
    (hL_budget_le : ∀ i k : Fin n, k.val < i.val →
      higham9_2_rectDoolittleLAbsBudget fp A
          (higham9_2_rectRoundedLoopL fp (Nat.le_refl n) A)
          (higham9_2_rectRoundedLoopU fp (Nat.le_refl n) A) i k ≤
        gamma fp n *
          |higham9_2_rectRoundedLoopL fp (Nat.le_refl n) A i k *
            higham9_2_rectRoundedLoopU fp (Nat.le_refl n) A k k|)
    (hγ_le_u : gamma fp n ≤ u) :
    let L_hat := higham9_2_rectRoundedLoopL fp (Nat.le_refl n) A
    let U_hat := higham9_2_rectRoundedLoopU fp (Nat.le_refl n) A
    let y_hat := fl_forwardSub fp n L_hat b
    let x_hat := fl_backSub fp n U_hat y_hat
    ∃ DeltaA : Fin n → Fin n → ℝ,
      (∀ i j, |DeltaA i j| ≤ higham9_14_f u * |A i j|) ∧
      (∀ i, ∑ j : Fin n, (A i j + DeltaA i j) * x_hat j = b i) := by
  dsimp only
  simpa [one_mul] using
    (higham9_14_source_f_bound_of_rectRoundedLoop_square_fl_triangular_solves_gamma_le
      fp n A b 1 u hu hn
      (hLU.det_ne_zero_iff_U_diag_ne_zero.mp hdetA)
      hU_budget_le hL_budget_le hγ_le_u
      (fun i j => by
        simpa [one_mul] using
          le_of_eq
            (higham9_12_mmatrix_lu_optimal_growth n A
              (higham9_2_rectRoundedLoopL fp (Nat.le_refl n) A)
              (higham9_2_rectRoundedLoopU fp (Nat.le_refl n) A)
              hM hLU hL_nn hU_nn i j)))

/-- **Theorem 9.14**, M-matrix executable rounded-loop final `h(u)` bound. -/
theorem higham9_14_mmatrix_lu_source_h_bound_of_rectRoundedLoop_square_fl_triangular_solves_gamma_le
    (fp : FPModel) (n : ℕ)
    (A : Fin n → Fin n → ℝ)
    (b : Fin n → ℝ)
    (u : ℝ) (hu : 0 ≤ u) (hu_lt_one : u < 1)
    (hn : gammaValid fp n)
    (hM : IsMMatrix n A)
    (hLU : LUFactSpec n A
      (higham9_2_rectRoundedLoopL fp (Nat.le_refl n) A)
      (higham9_2_rectRoundedLoopU fp (Nat.le_refl n) A))
    (hdetA : Matrix.det (Matrix.of A : Matrix (Fin n) (Fin n) ℝ) ≠ 0)
    (hL_nn : ∀ i k : Fin n,
      0 ≤ higham9_2_rectRoundedLoopL fp (Nat.le_refl n) A i k)
    (hU_nn : ∀ k j : Fin n,
      0 ≤ higham9_2_rectRoundedLoopU fp (Nat.le_refl n) A k j)
    (hU_budget_le : ∀ k j : Fin n, k.val ≤ j.val →
      higham9_2_rectDoolittleUAbsBudget fp (Nat.le_refl n) A
          (higham9_2_rectRoundedLoopL fp (Nat.le_refl n) A)
          (higham9_2_rectRoundedLoopU fp (Nat.le_refl n) A) k j ≤
        gamma fp n *
          |higham9_2_rectRoundedLoopU fp (Nat.le_refl n) A k j|)
    (hL_budget_le : ∀ i k : Fin n, k.val < i.val →
      higham9_2_rectDoolittleLAbsBudget fp A
          (higham9_2_rectRoundedLoopL fp (Nat.le_refl n) A)
          (higham9_2_rectRoundedLoopU fp (Nat.le_refl n) A) i k ≤
        gamma fp n *
          |higham9_2_rectRoundedLoopL fp (Nat.le_refl n) A i k *
            higham9_2_rectRoundedLoopU fp (Nat.le_refl n) A k k|)
    (hγ_le_u : gamma fp n ≤ u) :
    let L_hat := higham9_2_rectRoundedLoopL fp (Nat.le_refl n) A
    let U_hat := higham9_2_rectRoundedLoopU fp (Nat.le_refl n) A
    let y_hat := fl_forwardSub fp n L_hat b
    let x_hat := fl_backSub fp n U_hat y_hat
    ∃ DeltaA : Fin n → Fin n → ℝ,
      (∀ i j, |DeltaA i j| ≤ higham9_14_h u * |A i j|) ∧
      (∀ i, ∑ j : Fin n, (A i j + DeltaA i j) * x_hat j = b i) := by
  dsimp only
  exact
    higham9_14_source_h_bound_of_rectRoundedLoop_square_fl_triangular_solves_gamma_le
      fp n A b u hu hu_lt_one hn
      (hLU.det_ne_zero_iff_U_diag_ne_zero.mp hdetA)
      hU_budget_le hL_budget_le hγ_le_u
      (fun i j => by
        exact le_of_eq
          (higham9_12_mmatrix_lu_optimal_growth n A
            (higham9_2_rectRoundedLoopL fp (Nat.le_refl n) A)
            (higham9_2_rectRoundedLoopU fp (Nat.le_refl n) A)
            hM hLU hL_nn hU_nn i j))

/-- **Theorem 9.14**, M-matrix executable rounded-loop source `f(γ_n)` bound. -/
theorem higham9_14_mmatrix_lu_source_f_bound_of_rectRoundedLoop_square_fl_triangular_solves_gamma
    (fp : FPModel) (n : ℕ)
    (A : Fin n → Fin n → ℝ)
    (b : Fin n → ℝ)
    (hn : gammaValid fp n)
    (hM : IsMMatrix n A)
    (hLU : LUFactSpec n A
      (higham9_2_rectRoundedLoopL fp (Nat.le_refl n) A)
      (higham9_2_rectRoundedLoopU fp (Nat.le_refl n) A))
    (hdetA : Matrix.det (Matrix.of A : Matrix (Fin n) (Fin n) ℝ) ≠ 0)
    (hL_nn : ∀ i k : Fin n,
      0 ≤ higham9_2_rectRoundedLoopL fp (Nat.le_refl n) A i k)
    (hU_nn : ∀ k j : Fin n,
      0 ≤ higham9_2_rectRoundedLoopU fp (Nat.le_refl n) A k j)
    (hU_budget_le : ∀ k j : Fin n, k.val ≤ j.val →
      higham9_2_rectDoolittleUAbsBudget fp (Nat.le_refl n) A
          (higham9_2_rectRoundedLoopL fp (Nat.le_refl n) A)
          (higham9_2_rectRoundedLoopU fp (Nat.le_refl n) A) k j ≤
        gamma fp n *
          |higham9_2_rectRoundedLoopU fp (Nat.le_refl n) A k j|)
    (hL_budget_le : ∀ i k : Fin n, k.val < i.val →
      higham9_2_rectDoolittleLAbsBudget fp A
          (higham9_2_rectRoundedLoopL fp (Nat.le_refl n) A)
          (higham9_2_rectRoundedLoopU fp (Nat.le_refl n) A) i k ≤
        gamma fp n *
          |higham9_2_rectRoundedLoopL fp (Nat.le_refl n) A i k *
            higham9_2_rectRoundedLoopU fp (Nat.le_refl n) A k k|) :
    let L_hat := higham9_2_rectRoundedLoopL fp (Nat.le_refl n) A
    let U_hat := higham9_2_rectRoundedLoopU fp (Nat.le_refl n) A
    let y_hat := fl_forwardSub fp n L_hat b
    let x_hat := fl_backSub fp n U_hat y_hat
    ∃ DeltaA : Fin n → Fin n → ℝ,
      (∀ i j, |DeltaA i j| ≤
        higham9_14_f (gamma fp n) * |A i j|) ∧
      (∀ i, ∑ j : Fin n, (A i j + DeltaA i j) * x_hat j = b i) :=
  higham9_14_mmatrix_lu_source_f_bound_of_rectRoundedLoop_square_fl_triangular_solves_gamma_le
    fp n A b (gamma fp n) (gamma_nonneg fp hn) hn hM hLU hdetA
    hL_nn hU_nn hU_budget_le hL_budget_le le_rfl

/-- **Theorem 9.14**, M-matrix executable rounded-loop final `h(γ_n)` bound. -/
theorem higham9_14_mmatrix_lu_source_h_bound_of_rectRoundedLoop_square_fl_triangular_solves_gamma
    (fp : FPModel) (n : ℕ)
    (A : Fin n → Fin n → ℝ)
    (b : Fin n → ℝ)
    (hn : gammaValid fp n)
    (hγ_lt_one : gamma fp n < 1)
    (hM : IsMMatrix n A)
    (hLU : LUFactSpec n A
      (higham9_2_rectRoundedLoopL fp (Nat.le_refl n) A)
      (higham9_2_rectRoundedLoopU fp (Nat.le_refl n) A))
    (hdetA : Matrix.det (Matrix.of A : Matrix (Fin n) (Fin n) ℝ) ≠ 0)
    (hL_nn : ∀ i k : Fin n,
      0 ≤ higham9_2_rectRoundedLoopL fp (Nat.le_refl n) A i k)
    (hU_nn : ∀ k j : Fin n,
      0 ≤ higham9_2_rectRoundedLoopU fp (Nat.le_refl n) A k j)
    (hU_budget_le : ∀ k j : Fin n, k.val ≤ j.val →
      higham9_2_rectDoolittleUAbsBudget fp (Nat.le_refl n) A
          (higham9_2_rectRoundedLoopL fp (Nat.le_refl n) A)
          (higham9_2_rectRoundedLoopU fp (Nat.le_refl n) A) k j ≤
        gamma fp n *
          |higham9_2_rectRoundedLoopU fp (Nat.le_refl n) A k j|)
    (hL_budget_le : ∀ i k : Fin n, k.val < i.val →
      higham9_2_rectDoolittleLAbsBudget fp A
          (higham9_2_rectRoundedLoopL fp (Nat.le_refl n) A)
          (higham9_2_rectRoundedLoopU fp (Nat.le_refl n) A) i k ≤
        gamma fp n *
          |higham9_2_rectRoundedLoopL fp (Nat.le_refl n) A i k *
            higham9_2_rectRoundedLoopU fp (Nat.le_refl n) A k k|) :
    let L_hat := higham9_2_rectRoundedLoopL fp (Nat.le_refl n) A
    let U_hat := higham9_2_rectRoundedLoopU fp (Nat.le_refl n) A
    let y_hat := fl_forwardSub fp n L_hat b
    let x_hat := fl_backSub fp n U_hat y_hat
    ∃ DeltaA : Fin n → Fin n → ℝ,
      (∀ i j, |DeltaA i j| ≤
        higham9_14_h (gamma fp n) * |A i j|) ∧
      (∀ i, ∑ j : Fin n, (A i j + DeltaA i j) * x_hat j = b i) :=
  higham9_14_mmatrix_lu_source_h_bound_of_rectRoundedLoop_square_fl_triangular_solves_gamma_le
    fp n A b (gamma fp n) (gamma_nonneg fp hn) hγ_lt_one hn hM
    hLU hdetA hL_nn hU_nn hU_budget_le hL_budget_le le_rfl

/-- **Theorem 9.14**, Matrix-facing M-matrix executable rounded-loop source
`f(u)` bound. -/
theorem higham9_14_matrix_mmatrix_lu_source_f_bound_of_rectRoundedLoop_square_fl_triangular_solves_gamma_le
    (fp : FPModel) (n : ℕ)
    (A : Matrix (Fin n) (Fin n) ℝ)
    (b : Fin n → ℝ)
    (u : ℝ) (hu : 0 ≤ u)
    (hn : gammaValid fp n)
    (hM : IsMMatrix n A)
    (hLU : LUFactSpec n A
      (higham9_2_rectRoundedLoopL fp (Nat.le_refl n) A)
      (higham9_2_rectRoundedLoopU fp (Nat.le_refl n) A))
    (hdetA : Matrix.det A ≠ 0)
    (hL_nn : ∀ i k : Fin n,
      0 ≤ higham9_2_rectRoundedLoopL fp (Nat.le_refl n) A i k)
    (hU_nn : ∀ k j : Fin n,
      0 ≤ higham9_2_rectRoundedLoopU fp (Nat.le_refl n) A k j)
    (hU_budget_le : ∀ k j : Fin n, k.val ≤ j.val →
      higham9_2_rectDoolittleUAbsBudget fp (Nat.le_refl n) A
          (higham9_2_rectRoundedLoopL fp (Nat.le_refl n) A)
          (higham9_2_rectRoundedLoopU fp (Nat.le_refl n) A) k j ≤
        gamma fp n *
          |higham9_2_rectRoundedLoopU fp (Nat.le_refl n) A k j|)
    (hL_budget_le : ∀ i k : Fin n, k.val < i.val →
      higham9_2_rectDoolittleLAbsBudget fp A
          (higham9_2_rectRoundedLoopL fp (Nat.le_refl n) A)
          (higham9_2_rectRoundedLoopU fp (Nat.le_refl n) A) i k ≤
        gamma fp n *
          |higham9_2_rectRoundedLoopL fp (Nat.le_refl n) A i k *
            higham9_2_rectRoundedLoopU fp (Nat.le_refl n) A k k|)
    (hγ_le_u : gamma fp n ≤ u) :
    let L_hat := higham9_2_rectRoundedLoopL fp (Nat.le_refl n) A
    let U_hat := higham9_2_rectRoundedLoopU fp (Nat.le_refl n) A
    let y_hat := fl_forwardSub fp n L_hat b
    let x_hat := fl_backSub fp n U_hat y_hat
    ∃ DeltaA : Matrix (Fin n) (Fin n) ℝ,
      (∀ i j, |DeltaA i j| ≤ higham9_14_f u * |A i j|) ∧
      Matrix.mulVec (fun i j => A i j + DeltaA i j) x_hat = b := by
  dsimp only
  exact
    higham9_14_matrix_source_f_bound_of_rectRoundedLoop_square_fl_triangular_solves_absLU_le_absA_gamma_le
      fp n A b u hu hn
      (hLU.det_ne_zero_iff_U_diag_ne_zero.mp hdetA)
      hU_budget_le hL_budget_le hγ_le_u
      (fun i j =>
        le_of_eq
          (higham9_12_mmatrix_lu_optimal_growth n A
            (higham9_2_rectRoundedLoopL fp (Nat.le_refl n) A)
            (higham9_2_rectRoundedLoopU fp (Nat.le_refl n) A)
            hM hLU hL_nn hU_nn i j))

/-- **Theorem 9.14**, Matrix-facing M-matrix executable rounded-loop final
`h(u)` bound. -/
theorem higham9_14_matrix_mmatrix_lu_source_h_bound_of_rectRoundedLoop_square_fl_triangular_solves_gamma_le
    (fp : FPModel) (n : ℕ)
    (A : Matrix (Fin n) (Fin n) ℝ)
    (b : Fin n → ℝ)
    (u : ℝ) (hu : 0 ≤ u) (hu_lt_one : u < 1)
    (hn : gammaValid fp n)
    (hM : IsMMatrix n A)
    (hLU : LUFactSpec n A
      (higham9_2_rectRoundedLoopL fp (Nat.le_refl n) A)
      (higham9_2_rectRoundedLoopU fp (Nat.le_refl n) A))
    (hdetA : Matrix.det A ≠ 0)
    (hL_nn : ∀ i k : Fin n,
      0 ≤ higham9_2_rectRoundedLoopL fp (Nat.le_refl n) A i k)
    (hU_nn : ∀ k j : Fin n,
      0 ≤ higham9_2_rectRoundedLoopU fp (Nat.le_refl n) A k j)
    (hU_budget_le : ∀ k j : Fin n, k.val ≤ j.val →
      higham9_2_rectDoolittleUAbsBudget fp (Nat.le_refl n) A
          (higham9_2_rectRoundedLoopL fp (Nat.le_refl n) A)
          (higham9_2_rectRoundedLoopU fp (Nat.le_refl n) A) k j ≤
        gamma fp n *
          |higham9_2_rectRoundedLoopU fp (Nat.le_refl n) A k j|)
    (hL_budget_le : ∀ i k : Fin n, k.val < i.val →
      higham9_2_rectDoolittleLAbsBudget fp A
          (higham9_2_rectRoundedLoopL fp (Nat.le_refl n) A)
          (higham9_2_rectRoundedLoopU fp (Nat.le_refl n) A) i k ≤
        gamma fp n *
          |higham9_2_rectRoundedLoopL fp (Nat.le_refl n) A i k *
            higham9_2_rectRoundedLoopU fp (Nat.le_refl n) A k k|)
    (hγ_le_u : gamma fp n ≤ u) :
    let L_hat := higham9_2_rectRoundedLoopL fp (Nat.le_refl n) A
    let U_hat := higham9_2_rectRoundedLoopU fp (Nat.le_refl n) A
    let y_hat := fl_forwardSub fp n L_hat b
    let x_hat := fl_backSub fp n U_hat y_hat
    ∃ DeltaA : Matrix (Fin n) (Fin n) ℝ,
      (∀ i j, |DeltaA i j| ≤ higham9_14_h u * |A i j|) ∧
      Matrix.mulVec (fun i j => A i j + DeltaA i j) x_hat = b := by
  dsimp only
  exact
    higham9_14_matrix_source_h_bound_of_rectRoundedLoop_square_fl_triangular_solves_absLU_le_absA_gamma_le
      fp n A b u hu hu_lt_one hn
      (hLU.det_ne_zero_iff_U_diag_ne_zero.mp hdetA)
      hU_budget_le hL_budget_le hγ_le_u
      (fun i j =>
        le_of_eq
          (higham9_12_mmatrix_lu_optimal_growth n A
            (higham9_2_rectRoundedLoopL fp (Nat.le_refl n) A)
            (higham9_2_rectRoundedLoopU fp (Nat.le_refl n) A)
            hM hLU hL_nn hU_nn i j))

/-- **Theorem 9.14**, Matrix-facing M-matrix executable rounded-loop source
`f(γ_n)` bound. -/
theorem higham9_14_matrix_mmatrix_lu_source_f_bound_of_rectRoundedLoop_square_fl_triangular_solves_gamma
    (fp : FPModel) (n : ℕ)
    (A : Matrix (Fin n) (Fin n) ℝ)
    (b : Fin n → ℝ)
    (hn : gammaValid fp n)
    (hM : IsMMatrix n A)
    (hLU : LUFactSpec n A
      (higham9_2_rectRoundedLoopL fp (Nat.le_refl n) A)
      (higham9_2_rectRoundedLoopU fp (Nat.le_refl n) A))
    (hdetA : Matrix.det A ≠ 0)
    (hL_nn : ∀ i k : Fin n,
      0 ≤ higham9_2_rectRoundedLoopL fp (Nat.le_refl n) A i k)
    (hU_nn : ∀ k j : Fin n,
      0 ≤ higham9_2_rectRoundedLoopU fp (Nat.le_refl n) A k j)
    (hU_budget_le : ∀ k j : Fin n, k.val ≤ j.val →
      higham9_2_rectDoolittleUAbsBudget fp (Nat.le_refl n) A
          (higham9_2_rectRoundedLoopL fp (Nat.le_refl n) A)
          (higham9_2_rectRoundedLoopU fp (Nat.le_refl n) A) k j ≤
        gamma fp n *
          |higham9_2_rectRoundedLoopU fp (Nat.le_refl n) A k j|)
    (hL_budget_le : ∀ i k : Fin n, k.val < i.val →
      higham9_2_rectDoolittleLAbsBudget fp A
          (higham9_2_rectRoundedLoopL fp (Nat.le_refl n) A)
          (higham9_2_rectRoundedLoopU fp (Nat.le_refl n) A) i k ≤
        gamma fp n *
          |higham9_2_rectRoundedLoopL fp (Nat.le_refl n) A i k *
            higham9_2_rectRoundedLoopU fp (Nat.le_refl n) A k k|) :
    let L_hat := higham9_2_rectRoundedLoopL fp (Nat.le_refl n) A
    let U_hat := higham9_2_rectRoundedLoopU fp (Nat.le_refl n) A
    let y_hat := fl_forwardSub fp n L_hat b
    let x_hat := fl_backSub fp n U_hat y_hat
    ∃ DeltaA : Matrix (Fin n) (Fin n) ℝ,
      (∀ i j, |DeltaA i j| ≤
        higham9_14_f (gamma fp n) * |A i j|) ∧
      Matrix.mulVec (fun i j => A i j + DeltaA i j) x_hat = b :=
  higham9_14_matrix_mmatrix_lu_source_f_bound_of_rectRoundedLoop_square_fl_triangular_solves_gamma_le
    fp n A b (gamma fp n) (gamma_nonneg fp hn) hn hM hLU hdetA
    hL_nn hU_nn hU_budget_le hL_budget_le le_rfl

/-- **Theorem 9.14**, Matrix-facing M-matrix executable rounded-loop final
`h(γ_n)` bound. -/
theorem higham9_14_matrix_mmatrix_lu_source_h_bound_of_rectRoundedLoop_square_fl_triangular_solves_gamma
    (fp : FPModel) (n : ℕ)
    (A : Matrix (Fin n) (Fin n) ℝ)
    (b : Fin n → ℝ)
    (hn : gammaValid fp n)
    (hγ_lt_one : gamma fp n < 1)
    (hM : IsMMatrix n A)
    (hLU : LUFactSpec n A
      (higham9_2_rectRoundedLoopL fp (Nat.le_refl n) A)
      (higham9_2_rectRoundedLoopU fp (Nat.le_refl n) A))
    (hdetA : Matrix.det A ≠ 0)
    (hL_nn : ∀ i k : Fin n,
      0 ≤ higham9_2_rectRoundedLoopL fp (Nat.le_refl n) A i k)
    (hU_nn : ∀ k j : Fin n,
      0 ≤ higham9_2_rectRoundedLoopU fp (Nat.le_refl n) A k j)
    (hU_budget_le : ∀ k j : Fin n, k.val ≤ j.val →
      higham9_2_rectDoolittleUAbsBudget fp (Nat.le_refl n) A
          (higham9_2_rectRoundedLoopL fp (Nat.le_refl n) A)
          (higham9_2_rectRoundedLoopU fp (Nat.le_refl n) A) k j ≤
        gamma fp n *
          |higham9_2_rectRoundedLoopU fp (Nat.le_refl n) A k j|)
    (hL_budget_le : ∀ i k : Fin n, k.val < i.val →
      higham9_2_rectDoolittleLAbsBudget fp A
          (higham9_2_rectRoundedLoopL fp (Nat.le_refl n) A)
          (higham9_2_rectRoundedLoopU fp (Nat.le_refl n) A) i k ≤
        gamma fp n *
          |higham9_2_rectRoundedLoopL fp (Nat.le_refl n) A i k *
            higham9_2_rectRoundedLoopU fp (Nat.le_refl n) A k k|) :
    let L_hat := higham9_2_rectRoundedLoopL fp (Nat.le_refl n) A
    let U_hat := higham9_2_rectRoundedLoopU fp (Nat.le_refl n) A
    let y_hat := fl_forwardSub fp n L_hat b
    let x_hat := fl_backSub fp n U_hat y_hat
    ∃ DeltaA : Matrix (Fin n) (Fin n) ℝ,
      (∀ i j, |DeltaA i j| ≤
        higham9_14_h (gamma fp n) * |A i j|) ∧
      Matrix.mulVec (fun i j => A i j + DeltaA i j) x_hat = b :=
  higham9_14_matrix_mmatrix_lu_source_h_bound_of_rectRoundedLoop_square_fl_triangular_solves_gamma_le
    fp n A b (gamma fp n) (gamma_nonneg fp hn) hγ_lt_one hn hM
    hLU hdetA hL_nn hU_nn hU_budget_le hL_budget_le le_rfl

/-- **Theorem 9.14**, source-predicate sign-equivalent executable
rounded-loop source `f(u)` bound. -/
theorem higham9_14_sign_equiv_source_f_bound_of_IsSignEquiv_rectRoundedLoop_square_fl_triangular_solves_gamma_le
    (fp : FPModel) (n : ℕ)
    (A B L_B U_B : Fin n → Fin n → ℝ)
    (b : Fin n → ℝ)
    (u : ℝ) (hu : 0 ≤ u)
    (hn : gammaValid fp n)
    (hAB : IsSignEquiv n A B)
    (hB_growth : ∀ i j : Fin n,
      ∑ k : Fin n, |L_B i k| * |U_B k j| = |B i j|)
    (hL_abs : ∀ i k : Fin n,
      |higham9_2_rectRoundedLoopL fp (Nat.le_refl n) A i k| = |L_B i k|)
    (hU_abs : ∀ k j : Fin n,
      |higham9_2_rectRoundedLoopU fp (Nat.le_refl n) A k j| = |U_B k j|)
    (hLU : LUFactSpec n A
      (higham9_2_rectRoundedLoopL fp (Nat.le_refl n) A)
      (higham9_2_rectRoundedLoopU fp (Nat.le_refl n) A))
    (hdetA : Matrix.det (Matrix.of A : Matrix (Fin n) (Fin n) ℝ) ≠ 0)
    (hU_budget_le : ∀ k j : Fin n, k.val ≤ j.val →
      higham9_2_rectDoolittleUAbsBudget fp (Nat.le_refl n) A
          (higham9_2_rectRoundedLoopL fp (Nat.le_refl n) A)
          (higham9_2_rectRoundedLoopU fp (Nat.le_refl n) A) k j ≤
        gamma fp n *
          |higham9_2_rectRoundedLoopU fp (Nat.le_refl n) A k j|)
    (hL_budget_le : ∀ i k : Fin n, k.val < i.val →
      higham9_2_rectDoolittleLAbsBudget fp A
          (higham9_2_rectRoundedLoopL fp (Nat.le_refl n) A)
          (higham9_2_rectRoundedLoopU fp (Nat.le_refl n) A) i k ≤
        gamma fp n *
          |higham9_2_rectRoundedLoopL fp (Nat.le_refl n) A i k *
            higham9_2_rectRoundedLoopU fp (Nat.le_refl n) A k k|)
    (hγ_le_u : gamma fp n ≤ u) :
    let L_hat := higham9_2_rectRoundedLoopL fp (Nat.le_refl n) A
    let U_hat := higham9_2_rectRoundedLoopU fp (Nat.le_refl n) A
    let y_hat := fl_forwardSub fp n L_hat b
    let x_hat := fl_backSub fp n U_hat y_hat
    ∃ DeltaA : Fin n → Fin n → ℝ,
      (∀ i j, |DeltaA i j| ≤ higham9_14_f u * |A i j|) ∧
      (∀ i, ∑ j : Fin n, (A i j + DeltaA i j) * x_hat j = b i) := by
  dsimp only
  simpa [one_mul] using
    (higham9_14_source_f_bound_of_rectRoundedLoop_square_fl_triangular_solves_gamma_le
      fp n A b 1 u hu hn
      (hLU.det_ne_zero_iff_U_diag_ne_zero.mp hdetA)
      hU_budget_le hL_budget_le hγ_le_u
      (fun i j => by
        simpa [one_mul] using
          le_of_eq
            (higham9_12_sign_equiv_optimal_growth_of_IsSignEquiv
              n A B L_B U_B
              (higham9_2_rectRoundedLoopL fp (Nat.le_refl n) A)
              (higham9_2_rectRoundedLoopU fp (Nat.le_refl n) A)
              hAB hB_growth hL_abs hU_abs i j)))

/-- **Theorem 9.14**, source-predicate sign-equivalent executable
rounded-loop final `h(u)` bound. -/
theorem higham9_14_sign_equiv_source_h_bound_of_IsSignEquiv_rectRoundedLoop_square_fl_triangular_solves_gamma_le
    (fp : FPModel) (n : ℕ)
    (A B L_B U_B : Fin n → Fin n → ℝ)
    (b : Fin n → ℝ)
    (u : ℝ) (hu : 0 ≤ u) (hu_lt_one : u < 1)
    (hn : gammaValid fp n)
    (hAB : IsSignEquiv n A B)
    (hB_growth : ∀ i j : Fin n,
      ∑ k : Fin n, |L_B i k| * |U_B k j| = |B i j|)
    (hL_abs : ∀ i k : Fin n,
      |higham9_2_rectRoundedLoopL fp (Nat.le_refl n) A i k| = |L_B i k|)
    (hU_abs : ∀ k j : Fin n,
      |higham9_2_rectRoundedLoopU fp (Nat.le_refl n) A k j| = |U_B k j|)
    (hLU : LUFactSpec n A
      (higham9_2_rectRoundedLoopL fp (Nat.le_refl n) A)
      (higham9_2_rectRoundedLoopU fp (Nat.le_refl n) A))
    (hdetA : Matrix.det (Matrix.of A : Matrix (Fin n) (Fin n) ℝ) ≠ 0)
    (hU_budget_le : ∀ k j : Fin n, k.val ≤ j.val →
      higham9_2_rectDoolittleUAbsBudget fp (Nat.le_refl n) A
          (higham9_2_rectRoundedLoopL fp (Nat.le_refl n) A)
          (higham9_2_rectRoundedLoopU fp (Nat.le_refl n) A) k j ≤
        gamma fp n *
          |higham9_2_rectRoundedLoopU fp (Nat.le_refl n) A k j|)
    (hL_budget_le : ∀ i k : Fin n, k.val < i.val →
      higham9_2_rectDoolittleLAbsBudget fp A
          (higham9_2_rectRoundedLoopL fp (Nat.le_refl n) A)
          (higham9_2_rectRoundedLoopU fp (Nat.le_refl n) A) i k ≤
        gamma fp n *
          |higham9_2_rectRoundedLoopL fp (Nat.le_refl n) A i k *
            higham9_2_rectRoundedLoopU fp (Nat.le_refl n) A k k|)
    (hγ_le_u : gamma fp n ≤ u) :
    let L_hat := higham9_2_rectRoundedLoopL fp (Nat.le_refl n) A
    let U_hat := higham9_2_rectRoundedLoopU fp (Nat.le_refl n) A
    let y_hat := fl_forwardSub fp n L_hat b
    let x_hat := fl_backSub fp n U_hat y_hat
    ∃ DeltaA : Fin n → Fin n → ℝ,
      (∀ i j, |DeltaA i j| ≤ higham9_14_h u * |A i j|) ∧
      (∀ i, ∑ j : Fin n, (A i j + DeltaA i j) * x_hat j = b i) := by
  dsimp only
  exact
    higham9_14_source_h_bound_of_rectRoundedLoop_square_fl_triangular_solves_gamma_le
      fp n A b u hu hu_lt_one hn
      (hLU.det_ne_zero_iff_U_diag_ne_zero.mp hdetA)
      hU_budget_le hL_budget_le hγ_le_u
      (fun i j => by
        exact le_of_eq
          (higham9_12_sign_equiv_optimal_growth_of_IsSignEquiv
            n A B L_B U_B
            (higham9_2_rectRoundedLoopL fp (Nat.le_refl n) A)
            (higham9_2_rectRoundedLoopU fp (Nat.le_refl n) A)
            hAB hB_growth hL_abs hU_abs i j))

/-- **Theorem 9.14**, source-predicate sign-equivalent executable
rounded-loop source `f(γ_n)` bound. -/
theorem higham9_14_sign_equiv_source_f_bound_of_IsSignEquiv_rectRoundedLoop_square_fl_triangular_solves_gamma
    (fp : FPModel) (n : ℕ)
    (A B L_B U_B : Fin n → Fin n → ℝ)
    (b : Fin n → ℝ)
    (hn : gammaValid fp n)
    (hAB : IsSignEquiv n A B)
    (hB_growth : ∀ i j : Fin n,
      ∑ k : Fin n, |L_B i k| * |U_B k j| = |B i j|)
    (hL_abs : ∀ i k : Fin n,
      |higham9_2_rectRoundedLoopL fp (Nat.le_refl n) A i k| = |L_B i k|)
    (hU_abs : ∀ k j : Fin n,
      |higham9_2_rectRoundedLoopU fp (Nat.le_refl n) A k j| = |U_B k j|)
    (hLU : LUFactSpec n A
      (higham9_2_rectRoundedLoopL fp (Nat.le_refl n) A)
      (higham9_2_rectRoundedLoopU fp (Nat.le_refl n) A))
    (hdetA : Matrix.det (Matrix.of A : Matrix (Fin n) (Fin n) ℝ) ≠ 0)
    (hU_budget_le : ∀ k j : Fin n, k.val ≤ j.val →
      higham9_2_rectDoolittleUAbsBudget fp (Nat.le_refl n) A
          (higham9_2_rectRoundedLoopL fp (Nat.le_refl n) A)
          (higham9_2_rectRoundedLoopU fp (Nat.le_refl n) A) k j ≤
        gamma fp n *
          |higham9_2_rectRoundedLoopU fp (Nat.le_refl n) A k j|)
    (hL_budget_le : ∀ i k : Fin n, k.val < i.val →
      higham9_2_rectDoolittleLAbsBudget fp A
          (higham9_2_rectRoundedLoopL fp (Nat.le_refl n) A)
          (higham9_2_rectRoundedLoopU fp (Nat.le_refl n) A) i k ≤
        gamma fp n *
          |higham9_2_rectRoundedLoopL fp (Nat.le_refl n) A i k *
            higham9_2_rectRoundedLoopU fp (Nat.le_refl n) A k k|) :
    let L_hat := higham9_2_rectRoundedLoopL fp (Nat.le_refl n) A
    let U_hat := higham9_2_rectRoundedLoopU fp (Nat.le_refl n) A
    let y_hat := fl_forwardSub fp n L_hat b
    let x_hat := fl_backSub fp n U_hat y_hat
    ∃ DeltaA : Fin n → Fin n → ℝ,
      (∀ i j, |DeltaA i j| ≤
        higham9_14_f (gamma fp n) * |A i j|) ∧
      (∀ i, ∑ j : Fin n, (A i j + DeltaA i j) * x_hat j = b i) :=
  higham9_14_sign_equiv_source_f_bound_of_IsSignEquiv_rectRoundedLoop_square_fl_triangular_solves_gamma_le
    fp n A B L_B U_B b (gamma fp n) (gamma_nonneg fp hn) hn
    hAB hB_growth hL_abs hU_abs hLU hdetA hU_budget_le hL_budget_le
    le_rfl

/-- **Theorem 9.14**, source-predicate sign-equivalent executable
rounded-loop final `h(γ_n)` bound. -/
theorem higham9_14_sign_equiv_source_h_bound_of_IsSignEquiv_rectRoundedLoop_square_fl_triangular_solves_gamma
    (fp : FPModel) (n : ℕ)
    (A B L_B U_B : Fin n → Fin n → ℝ)
    (b : Fin n → ℝ)
    (hn : gammaValid fp n)
    (hγ_lt_one : gamma fp n < 1)
    (hAB : IsSignEquiv n A B)
    (hB_growth : ∀ i j : Fin n,
      ∑ k : Fin n, |L_B i k| * |U_B k j| = |B i j|)
    (hL_abs : ∀ i k : Fin n,
      |higham9_2_rectRoundedLoopL fp (Nat.le_refl n) A i k| = |L_B i k|)
    (hU_abs : ∀ k j : Fin n,
      |higham9_2_rectRoundedLoopU fp (Nat.le_refl n) A k j| = |U_B k j|)
    (hLU : LUFactSpec n A
      (higham9_2_rectRoundedLoopL fp (Nat.le_refl n) A)
      (higham9_2_rectRoundedLoopU fp (Nat.le_refl n) A))
    (hdetA : Matrix.det (Matrix.of A : Matrix (Fin n) (Fin n) ℝ) ≠ 0)
    (hU_budget_le : ∀ k j : Fin n, k.val ≤ j.val →
      higham9_2_rectDoolittleUAbsBudget fp (Nat.le_refl n) A
          (higham9_2_rectRoundedLoopL fp (Nat.le_refl n) A)
          (higham9_2_rectRoundedLoopU fp (Nat.le_refl n) A) k j ≤
        gamma fp n *
          |higham9_2_rectRoundedLoopU fp (Nat.le_refl n) A k j|)
    (hL_budget_le : ∀ i k : Fin n, k.val < i.val →
      higham9_2_rectDoolittleLAbsBudget fp A
          (higham9_2_rectRoundedLoopL fp (Nat.le_refl n) A)
          (higham9_2_rectRoundedLoopU fp (Nat.le_refl n) A) i k ≤
        gamma fp n *
          |higham9_2_rectRoundedLoopL fp (Nat.le_refl n) A i k *
            higham9_2_rectRoundedLoopU fp (Nat.le_refl n) A k k|) :
    let L_hat := higham9_2_rectRoundedLoopL fp (Nat.le_refl n) A
    let U_hat := higham9_2_rectRoundedLoopU fp (Nat.le_refl n) A
    let y_hat := fl_forwardSub fp n L_hat b
    let x_hat := fl_backSub fp n U_hat y_hat
    ∃ DeltaA : Fin n → Fin n → ℝ,
      (∀ i j, |DeltaA i j| ≤
        higham9_14_h (gamma fp n) * |A i j|) ∧
      (∀ i, ∑ j : Fin n, (A i j + DeltaA i j) * x_hat j = b i) :=
  higham9_14_sign_equiv_source_h_bound_of_IsSignEquiv_rectRoundedLoop_square_fl_triangular_solves_gamma_le
    fp n A B L_B U_B b (gamma fp n) (gamma_nonneg fp hn)
    hγ_lt_one hn hAB hB_growth hL_abs hU_abs hLU hdetA
    hU_budget_le hL_budget_le le_rfl

/-- **Theorem 9.14**, Matrix-facing sign-equivalent executable rounded-loop
source `f(u)` bound. -/
theorem higham9_14_matrix_sign_equiv_source_f_bound_of_IsSignEquiv_rectRoundedLoop_square_fl_triangular_solves_gamma_le
    (fp : FPModel) (n : ℕ)
    (A B L_B U_B : Matrix (Fin n) (Fin n) ℝ)
    (b : Fin n → ℝ)
    (u : ℝ) (hu : 0 ≤ u)
    (hn : gammaValid fp n)
    (hAB : IsSignEquiv n A B)
    (hB_growth : ∀ i j : Fin n,
      ∑ k : Fin n, |L_B i k| * |U_B k j| = |B i j|)
    (hL_abs : ∀ i k : Fin n,
      |higham9_2_rectRoundedLoopL fp (Nat.le_refl n) A i k| = |L_B i k|)
    (hU_abs : ∀ k j : Fin n,
      |higham9_2_rectRoundedLoopU fp (Nat.le_refl n) A k j| = |U_B k j|)
    (hLU : LUFactSpec n A
      (higham9_2_rectRoundedLoopL fp (Nat.le_refl n) A)
      (higham9_2_rectRoundedLoopU fp (Nat.le_refl n) A))
    (hdetA : Matrix.det A ≠ 0)
    (hU_budget_le : ∀ k j : Fin n, k.val ≤ j.val →
      higham9_2_rectDoolittleUAbsBudget fp (Nat.le_refl n) A
          (higham9_2_rectRoundedLoopL fp (Nat.le_refl n) A)
          (higham9_2_rectRoundedLoopU fp (Nat.le_refl n) A) k j ≤
        gamma fp n *
          |higham9_2_rectRoundedLoopU fp (Nat.le_refl n) A k j|)
    (hL_budget_le : ∀ i k : Fin n, k.val < i.val →
      higham9_2_rectDoolittleLAbsBudget fp A
          (higham9_2_rectRoundedLoopL fp (Nat.le_refl n) A)
          (higham9_2_rectRoundedLoopU fp (Nat.le_refl n) A) i k ≤
        gamma fp n *
          |higham9_2_rectRoundedLoopL fp (Nat.le_refl n) A i k *
            higham9_2_rectRoundedLoopU fp (Nat.le_refl n) A k k|)
    (hγ_le_u : gamma fp n ≤ u) :
    let L_hat := higham9_2_rectRoundedLoopL fp (Nat.le_refl n) A
    let U_hat := higham9_2_rectRoundedLoopU fp (Nat.le_refl n) A
    let y_hat := fl_forwardSub fp n L_hat b
    let x_hat := fl_backSub fp n U_hat y_hat
    ∃ DeltaA : Matrix (Fin n) (Fin n) ℝ,
      (∀ i j, |DeltaA i j| ≤ higham9_14_f u * |A i j|) ∧
      Matrix.mulVec (fun i j => A i j + DeltaA i j) x_hat = b := by
  dsimp only
  exact
    higham9_14_matrix_source_f_bound_of_rectRoundedLoop_square_fl_triangular_solves_absLU_le_absA_gamma_le
      fp n A b u hu hn
      (hLU.det_ne_zero_iff_U_diag_ne_zero.mp hdetA)
      hU_budget_le hL_budget_le hγ_le_u
      (fun i j =>
        le_of_eq
          (higham9_12_sign_equiv_optimal_growth_of_IsSignEquiv
            n A B L_B U_B
            (higham9_2_rectRoundedLoopL fp (Nat.le_refl n) A)
            (higham9_2_rectRoundedLoopU fp (Nat.le_refl n) A)
            hAB hB_growth hL_abs hU_abs i j))

/-- **Theorem 9.14**, Matrix-facing sign-equivalent executable rounded-loop
final `h(u)` bound. -/
theorem higham9_14_matrix_sign_equiv_source_h_bound_of_IsSignEquiv_rectRoundedLoop_square_fl_triangular_solves_gamma_le
    (fp : FPModel) (n : ℕ)
    (A B L_B U_B : Matrix (Fin n) (Fin n) ℝ)
    (b : Fin n → ℝ)
    (u : ℝ) (hu : 0 ≤ u) (hu_lt_one : u < 1)
    (hn : gammaValid fp n)
    (hAB : IsSignEquiv n A B)
    (hB_growth : ∀ i j : Fin n,
      ∑ k : Fin n, |L_B i k| * |U_B k j| = |B i j|)
    (hL_abs : ∀ i k : Fin n,
      |higham9_2_rectRoundedLoopL fp (Nat.le_refl n) A i k| = |L_B i k|)
    (hU_abs : ∀ k j : Fin n,
      |higham9_2_rectRoundedLoopU fp (Nat.le_refl n) A k j| = |U_B k j|)
    (hLU : LUFactSpec n A
      (higham9_2_rectRoundedLoopL fp (Nat.le_refl n) A)
      (higham9_2_rectRoundedLoopU fp (Nat.le_refl n) A))
    (hdetA : Matrix.det A ≠ 0)
    (hU_budget_le : ∀ k j : Fin n, k.val ≤ j.val →
      higham9_2_rectDoolittleUAbsBudget fp (Nat.le_refl n) A
          (higham9_2_rectRoundedLoopL fp (Nat.le_refl n) A)
          (higham9_2_rectRoundedLoopU fp (Nat.le_refl n) A) k j ≤
        gamma fp n *
          |higham9_2_rectRoundedLoopU fp (Nat.le_refl n) A k j|)
    (hL_budget_le : ∀ i k : Fin n, k.val < i.val →
      higham9_2_rectDoolittleLAbsBudget fp A
          (higham9_2_rectRoundedLoopL fp (Nat.le_refl n) A)
          (higham9_2_rectRoundedLoopU fp (Nat.le_refl n) A) i k ≤
        gamma fp n *
          |higham9_2_rectRoundedLoopL fp (Nat.le_refl n) A i k *
            higham9_2_rectRoundedLoopU fp (Nat.le_refl n) A k k|)
    (hγ_le_u : gamma fp n ≤ u) :
    let L_hat := higham9_2_rectRoundedLoopL fp (Nat.le_refl n) A
    let U_hat := higham9_2_rectRoundedLoopU fp (Nat.le_refl n) A
    let y_hat := fl_forwardSub fp n L_hat b
    let x_hat := fl_backSub fp n U_hat y_hat
    ∃ DeltaA : Matrix (Fin n) (Fin n) ℝ,
      (∀ i j, |DeltaA i j| ≤ higham9_14_h u * |A i j|) ∧
      Matrix.mulVec (fun i j => A i j + DeltaA i j) x_hat = b := by
  dsimp only
  exact
    higham9_14_matrix_source_h_bound_of_rectRoundedLoop_square_fl_triangular_solves_absLU_le_absA_gamma_le
      fp n A b u hu hu_lt_one hn
      (hLU.det_ne_zero_iff_U_diag_ne_zero.mp hdetA)
      hU_budget_le hL_budget_le hγ_le_u
      (fun i j =>
        le_of_eq
          (higham9_12_sign_equiv_optimal_growth_of_IsSignEquiv
            n A B L_B U_B
            (higham9_2_rectRoundedLoopL fp (Nat.le_refl n) A)
            (higham9_2_rectRoundedLoopU fp (Nat.le_refl n) A)
            hAB hB_growth hL_abs hU_abs i j))

/-- **Theorem 9.14**, Matrix-facing sign-equivalent executable rounded-loop
source `f(γ_n)` bound. -/
theorem higham9_14_matrix_sign_equiv_source_f_bound_of_IsSignEquiv_rectRoundedLoop_square_fl_triangular_solves_gamma
    (fp : FPModel) (n : ℕ)
    (A B L_B U_B : Matrix (Fin n) (Fin n) ℝ)
    (b : Fin n → ℝ)
    (hn : gammaValid fp n)
    (hAB : IsSignEquiv n A B)
    (hB_growth : ∀ i j : Fin n,
      ∑ k : Fin n, |L_B i k| * |U_B k j| = |B i j|)
    (hL_abs : ∀ i k : Fin n,
      |higham9_2_rectRoundedLoopL fp (Nat.le_refl n) A i k| = |L_B i k|)
    (hU_abs : ∀ k j : Fin n,
      |higham9_2_rectRoundedLoopU fp (Nat.le_refl n) A k j| = |U_B k j|)
    (hLU : LUFactSpec n A
      (higham9_2_rectRoundedLoopL fp (Nat.le_refl n) A)
      (higham9_2_rectRoundedLoopU fp (Nat.le_refl n) A))
    (hdetA : Matrix.det A ≠ 0)
    (hU_budget_le : ∀ k j : Fin n, k.val ≤ j.val →
      higham9_2_rectDoolittleUAbsBudget fp (Nat.le_refl n) A
          (higham9_2_rectRoundedLoopL fp (Nat.le_refl n) A)
          (higham9_2_rectRoundedLoopU fp (Nat.le_refl n) A) k j ≤
        gamma fp n *
          |higham9_2_rectRoundedLoopU fp (Nat.le_refl n) A k j|)
    (hL_budget_le : ∀ i k : Fin n, k.val < i.val →
      higham9_2_rectDoolittleLAbsBudget fp A
          (higham9_2_rectRoundedLoopL fp (Nat.le_refl n) A)
          (higham9_2_rectRoundedLoopU fp (Nat.le_refl n) A) i k ≤
        gamma fp n *
          |higham9_2_rectRoundedLoopL fp (Nat.le_refl n) A i k *
            higham9_2_rectRoundedLoopU fp (Nat.le_refl n) A k k|) :
    let L_hat := higham9_2_rectRoundedLoopL fp (Nat.le_refl n) A
    let U_hat := higham9_2_rectRoundedLoopU fp (Nat.le_refl n) A
    let y_hat := fl_forwardSub fp n L_hat b
    let x_hat := fl_backSub fp n U_hat y_hat
    ∃ DeltaA : Matrix (Fin n) (Fin n) ℝ,
      (∀ i j, |DeltaA i j| ≤
        higham9_14_f (gamma fp n) * |A i j|) ∧
      Matrix.mulVec (fun i j => A i j + DeltaA i j) x_hat = b :=
  higham9_14_matrix_sign_equiv_source_f_bound_of_IsSignEquiv_rectRoundedLoop_square_fl_triangular_solves_gamma_le
    fp n A B L_B U_B b (gamma fp n) (gamma_nonneg fp hn) hn
    hAB hB_growth hL_abs hU_abs hLU hdetA hU_budget_le hL_budget_le
    le_rfl

/-- **Theorem 9.14**, Matrix-facing sign-equivalent executable rounded-loop
final `h(γ_n)` bound. -/
theorem higham9_14_matrix_sign_equiv_source_h_bound_of_IsSignEquiv_rectRoundedLoop_square_fl_triangular_solves_gamma
    (fp : FPModel) (n : ℕ)
    (A B L_B U_B : Matrix (Fin n) (Fin n) ℝ)
    (b : Fin n → ℝ)
    (hn : gammaValid fp n)
    (hγ_lt_one : gamma fp n < 1)
    (hAB : IsSignEquiv n A B)
    (hB_growth : ∀ i j : Fin n,
      ∑ k : Fin n, |L_B i k| * |U_B k j| = |B i j|)
    (hL_abs : ∀ i k : Fin n,
      |higham9_2_rectRoundedLoopL fp (Nat.le_refl n) A i k| = |L_B i k|)
    (hU_abs : ∀ k j : Fin n,
      |higham9_2_rectRoundedLoopU fp (Nat.le_refl n) A k j| = |U_B k j|)
    (hLU : LUFactSpec n A
      (higham9_2_rectRoundedLoopL fp (Nat.le_refl n) A)
      (higham9_2_rectRoundedLoopU fp (Nat.le_refl n) A))
    (hdetA : Matrix.det A ≠ 0)
    (hU_budget_le : ∀ k j : Fin n, k.val ≤ j.val →
      higham9_2_rectDoolittleUAbsBudget fp (Nat.le_refl n) A
          (higham9_2_rectRoundedLoopL fp (Nat.le_refl n) A)
          (higham9_2_rectRoundedLoopU fp (Nat.le_refl n) A) k j ≤
        gamma fp n *
          |higham9_2_rectRoundedLoopU fp (Nat.le_refl n) A k j|)
    (hL_budget_le : ∀ i k : Fin n, k.val < i.val →
      higham9_2_rectDoolittleLAbsBudget fp A
          (higham9_2_rectRoundedLoopL fp (Nat.le_refl n) A)
          (higham9_2_rectRoundedLoopU fp (Nat.le_refl n) A) i k ≤
        gamma fp n *
          |higham9_2_rectRoundedLoopL fp (Nat.le_refl n) A i k *
            higham9_2_rectRoundedLoopU fp (Nat.le_refl n) A k k|) :
    let L_hat := higham9_2_rectRoundedLoopL fp (Nat.le_refl n) A
    let U_hat := higham9_2_rectRoundedLoopU fp (Nat.le_refl n) A
    let y_hat := fl_forwardSub fp n L_hat b
    let x_hat := fl_backSub fp n U_hat y_hat
    ∃ DeltaA : Matrix (Fin n) (Fin n) ℝ,
      (∀ i j, |DeltaA i j| ≤
        higham9_14_h (gamma fp n) * |A i j|) ∧
      Matrix.mulVec (fun i j => A i j + DeltaA i j) x_hat = b :=
  higham9_14_matrix_sign_equiv_source_h_bound_of_IsSignEquiv_rectRoundedLoop_square_fl_triangular_solves_gamma_le
    fp n A B L_B U_B b (gamma fp n) (gamma_nonneg fp hn)
    hγ_lt_one hn hAB hB_growth hL_abs hU_abs hLU hdetA
    hU_budget_le hL_budget_le le_rfl

/-- **Theorem 9.14**, nonnegative-LU executable rounded-loop
model-consuming `f(γ_n)` bound.  The concrete loop supplies equation (9.20),
while the caller supplies the explicit triangular-solve equation (9.21). -/
theorem higham9_14_nonnegative_lu_source_f_bound_of_rectRoundedLoop_square_models_gamma
    (fp : FPModel) (n : ℕ)
    (A : Fin n → Fin n → ℝ)
    (y_hat x_hat b : Fin n → ℝ)
    (DeltaL DeltaU : Fin n → Fin n → ℝ)
    (hn : gammaValid fp n)
    (hNonneg : HasNonnegLUFactors n A
      (higham9_2_rectRoundedLoopL fp (Nat.le_refl n) A)
      (higham9_2_rectRoundedLoopU fp (Nat.le_refl n) A))
    (hdetA : Matrix.det (Matrix.of A : Matrix (Fin n) (Fin n) ℝ) ≠ 0)
    (hU_budget_le : ∀ k j : Fin n, k.val ≤ j.val →
      higham9_2_rectDoolittleUAbsBudget fp (Nat.le_refl n) A
          (higham9_2_rectRoundedLoopL fp (Nat.le_refl n) A)
          (higham9_2_rectRoundedLoopU fp (Nat.le_refl n) A) k j ≤
        gamma fp n *
          |higham9_2_rectRoundedLoopU fp (Nat.le_refl n) A k j|)
    (hL_budget_le : ∀ i k : Fin n, k.val < i.val →
      higham9_2_rectDoolittleLAbsBudget fp A
          (higham9_2_rectRoundedLoopL fp (Nat.le_refl n) A)
          (higham9_2_rectRoundedLoopU fp (Nat.le_refl n) A) i k ≤
        gamma fp n *
          |higham9_2_rectRoundedLoopL fp (Nat.le_refl n) A i k *
            higham9_2_rectRoundedLoopU fp (Nat.le_refl n) A k k|)
    (h21 : higham9_21_tridiag_solve_perturbation_model n
      (higham9_2_rectRoundedLoopL fp (Nat.le_refl n) A)
      (higham9_2_rectRoundedLoopU fp (Nat.le_refl n) A)
      y_hat x_hat b DeltaL DeltaU (gamma fp n)) :
    ∃ DeltaA : Fin n → Fin n → ℝ,
      (∀ i j, |DeltaA i j| ≤
        higham9_14_f (gamma fp n) * |A i j|) ∧
      (∀ i, ∑ j : Fin n, (A i j + DeltaA i j) * x_hat j = b i) := by
  rcases
      higham9_20_tridiag_lu_perturbation_model_of_rectRoundedLoop_square_gamma
        fp n A hn (hNonneg.1.det_ne_zero_iff_U_diag_ne_zero.mp hdetA)
        hU_budget_le hL_budget_le with
    ⟨DeltaA_LU, h20⟩
  simpa [one_mul] using
    (higham9_14_source_f_bound_of_absLU_le_const_absA_and_9_20_9_21_models
      n A
      (higham9_2_rectRoundedLoopL fp (Nat.le_refl n) A)
      (higham9_2_rectRoundedLoopU fp (Nat.le_refl n) A)
      y_hat x_hat b 1 (gamma fp n) (gamma_nonneg fp hn)
      (fun i j => by
        simpa [one_mul] using
          le_of_eq
            (higham9_12_nonneg_lu_optimal_growth n A
              (higham9_2_rectRoundedLoopL fp (Nat.le_refl n) A)
              (higham9_2_rectRoundedLoopU fp (Nat.le_refl n) A)
              hNonneg i j))
      DeltaA_LU DeltaL DeltaU h20 h21)

/-- **Theorem 9.14**, nonnegative-LU executable rounded-loop
model-consuming final `h(γ_n)` bound. -/
theorem higham9_14_nonnegative_lu_source_h_bound_of_rectRoundedLoop_square_models_gamma
    (fp : FPModel) (n : ℕ)
    (A : Fin n → Fin n → ℝ)
    (y_hat x_hat b : Fin n → ℝ)
    (DeltaL DeltaU : Fin n → Fin n → ℝ)
    (hn : gammaValid fp n)
    (hγ_lt_one : gamma fp n < 1)
    (hNonneg : HasNonnegLUFactors n A
      (higham9_2_rectRoundedLoopL fp (Nat.le_refl n) A)
      (higham9_2_rectRoundedLoopU fp (Nat.le_refl n) A))
    (hdetA : Matrix.det (Matrix.of A : Matrix (Fin n) (Fin n) ℝ) ≠ 0)
    (hU_budget_le : ∀ k j : Fin n, k.val ≤ j.val →
      higham9_2_rectDoolittleUAbsBudget fp (Nat.le_refl n) A
          (higham9_2_rectRoundedLoopL fp (Nat.le_refl n) A)
          (higham9_2_rectRoundedLoopU fp (Nat.le_refl n) A) k j ≤
        gamma fp n *
          |higham9_2_rectRoundedLoopU fp (Nat.le_refl n) A k j|)
    (hL_budget_le : ∀ i k : Fin n, k.val < i.val →
      higham9_2_rectDoolittleLAbsBudget fp A
          (higham9_2_rectRoundedLoopL fp (Nat.le_refl n) A)
          (higham9_2_rectRoundedLoopU fp (Nat.le_refl n) A) i k ≤
        gamma fp n *
          |higham9_2_rectRoundedLoopL fp (Nat.le_refl n) A i k *
            higham9_2_rectRoundedLoopU fp (Nat.le_refl n) A k k|)
    (h21 : higham9_21_tridiag_solve_perturbation_model n
      (higham9_2_rectRoundedLoopL fp (Nat.le_refl n) A)
      (higham9_2_rectRoundedLoopU fp (Nat.le_refl n) A)
      y_hat x_hat b DeltaL DeltaU (gamma fp n)) :
    ∃ DeltaA : Fin n → Fin n → ℝ,
      (∀ i j, |DeltaA i j| ≤
        higham9_14_h (gamma fp n) * |A i j|) ∧
      (∀ i, ∑ j : Fin n, (A i j + DeltaA i j) * x_hat j = b i) := by
  rcases
      higham9_20_tridiag_lu_perturbation_model_of_rectRoundedLoop_square_gamma
        fp n A hn (hNonneg.1.det_ne_zero_iff_U_diag_ne_zero.mp hdetA)
        hU_budget_le hL_budget_le with
    ⟨DeltaA_LU, h20⟩
  simpa [one_mul] using
    (higham9_14_source_h_bound_of_absLU_le_const_absA_and_9_20_9_21_models
      n A
      (higham9_2_rectRoundedLoopL fp (Nat.le_refl n) A)
      (higham9_2_rectRoundedLoopU fp (Nat.le_refl n) A)
      y_hat x_hat b 1 (gamma fp n)
      (by norm_num) (gamma_nonneg fp hn) hγ_lt_one
      (fun i j => by
        simpa [one_mul] using
          le_of_eq
            (higham9_12_nonneg_lu_optimal_growth n A
              (higham9_2_rectRoundedLoopL fp (Nat.le_refl n) A)
              (higham9_2_rectRoundedLoopU fp (Nat.le_refl n) A)
              hNonneg i j))
      DeltaA_LU DeltaL DeltaU h20 h21)

/-- **Theorem 9.14**, M-matrix LU executable rounded-loop
model-consuming `f(γ_n)` bound. -/
theorem higham9_14_mmatrix_lu_source_f_bound_of_rectRoundedLoop_square_models_gamma
    (fp : FPModel) (n : ℕ)
    (A : Fin n → Fin n → ℝ)
    (y_hat x_hat b : Fin n → ℝ)
    (DeltaL DeltaU : Fin n → Fin n → ℝ)
    (hn : gammaValid fp n)
    (hM : IsMMatrix n A)
    (hLU : LUFactSpec n A
      (higham9_2_rectRoundedLoopL fp (Nat.le_refl n) A)
      (higham9_2_rectRoundedLoopU fp (Nat.le_refl n) A))
    (hdetA : Matrix.det (Matrix.of A : Matrix (Fin n) (Fin n) ℝ) ≠ 0)
    (hL_nn : ∀ i k : Fin n,
      0 ≤ higham9_2_rectRoundedLoopL fp (Nat.le_refl n) A i k)
    (hU_nn : ∀ k j : Fin n,
      0 ≤ higham9_2_rectRoundedLoopU fp (Nat.le_refl n) A k j)
    (hU_budget_le : ∀ k j : Fin n, k.val ≤ j.val →
      higham9_2_rectDoolittleUAbsBudget fp (Nat.le_refl n) A
          (higham9_2_rectRoundedLoopL fp (Nat.le_refl n) A)
          (higham9_2_rectRoundedLoopU fp (Nat.le_refl n) A) k j ≤
        gamma fp n *
          |higham9_2_rectRoundedLoopU fp (Nat.le_refl n) A k j|)
    (hL_budget_le : ∀ i k : Fin n, k.val < i.val →
      higham9_2_rectDoolittleLAbsBudget fp A
          (higham9_2_rectRoundedLoopL fp (Nat.le_refl n) A)
          (higham9_2_rectRoundedLoopU fp (Nat.le_refl n) A) i k ≤
        gamma fp n *
          |higham9_2_rectRoundedLoopL fp (Nat.le_refl n) A i k *
            higham9_2_rectRoundedLoopU fp (Nat.le_refl n) A k k|)
    (h21 : higham9_21_tridiag_solve_perturbation_model n
      (higham9_2_rectRoundedLoopL fp (Nat.le_refl n) A)
      (higham9_2_rectRoundedLoopU fp (Nat.le_refl n) A)
      y_hat x_hat b DeltaL DeltaU (gamma fp n)) :
    ∃ DeltaA : Fin n → Fin n → ℝ,
      (∀ i j, |DeltaA i j| ≤
        higham9_14_f (gamma fp n) * |A i j|) ∧
      (∀ i, ∑ j : Fin n, (A i j + DeltaA i j) * x_hat j = b i) := by
  rcases
      higham9_20_tridiag_lu_perturbation_model_of_rectRoundedLoop_square_gamma
        fp n A hn (hLU.det_ne_zero_iff_U_diag_ne_zero.mp hdetA)
        hU_budget_le hL_budget_le with
    ⟨DeltaA_LU, h20⟩
  simpa [one_mul] using
    (higham9_14_source_f_bound_of_absLU_le_const_absA_and_9_20_9_21_models
      n A
      (higham9_2_rectRoundedLoopL fp (Nat.le_refl n) A)
      (higham9_2_rectRoundedLoopU fp (Nat.le_refl n) A)
      y_hat x_hat b 1 (gamma fp n) (gamma_nonneg fp hn)
      (fun i j => by
        simpa [one_mul] using
          le_of_eq
            (higham9_12_mmatrix_lu_optimal_growth n A
              (higham9_2_rectRoundedLoopL fp (Nat.le_refl n) A)
              (higham9_2_rectRoundedLoopU fp (Nat.le_refl n) A)
              hM hLU hL_nn hU_nn i j))
      DeltaA_LU DeltaL DeltaU h20 h21)

/-- **Theorem 9.14**, M-matrix LU executable rounded-loop
model-consuming final `h(γ_n)` bound. -/
theorem higham9_14_mmatrix_lu_source_h_bound_of_rectRoundedLoop_square_models_gamma
    (fp : FPModel) (n : ℕ)
    (A : Fin n → Fin n → ℝ)
    (y_hat x_hat b : Fin n → ℝ)
    (DeltaL DeltaU : Fin n → Fin n → ℝ)
    (hn : gammaValid fp n)
    (hγ_lt_one : gamma fp n < 1)
    (hM : IsMMatrix n A)
    (hLU : LUFactSpec n A
      (higham9_2_rectRoundedLoopL fp (Nat.le_refl n) A)
      (higham9_2_rectRoundedLoopU fp (Nat.le_refl n) A))
    (hdetA : Matrix.det (Matrix.of A : Matrix (Fin n) (Fin n) ℝ) ≠ 0)
    (hL_nn : ∀ i k : Fin n,
      0 ≤ higham9_2_rectRoundedLoopL fp (Nat.le_refl n) A i k)
    (hU_nn : ∀ k j : Fin n,
      0 ≤ higham9_2_rectRoundedLoopU fp (Nat.le_refl n) A k j)
    (hU_budget_le : ∀ k j : Fin n, k.val ≤ j.val →
      higham9_2_rectDoolittleUAbsBudget fp (Nat.le_refl n) A
          (higham9_2_rectRoundedLoopL fp (Nat.le_refl n) A)
          (higham9_2_rectRoundedLoopU fp (Nat.le_refl n) A) k j ≤
        gamma fp n *
          |higham9_2_rectRoundedLoopU fp (Nat.le_refl n) A k j|)
    (hL_budget_le : ∀ i k : Fin n, k.val < i.val →
      higham9_2_rectDoolittleLAbsBudget fp A
          (higham9_2_rectRoundedLoopL fp (Nat.le_refl n) A)
          (higham9_2_rectRoundedLoopU fp (Nat.le_refl n) A) i k ≤
        gamma fp n *
          |higham9_2_rectRoundedLoopL fp (Nat.le_refl n) A i k *
            higham9_2_rectRoundedLoopU fp (Nat.le_refl n) A k k|)
    (h21 : higham9_21_tridiag_solve_perturbation_model n
      (higham9_2_rectRoundedLoopL fp (Nat.le_refl n) A)
      (higham9_2_rectRoundedLoopU fp (Nat.le_refl n) A)
      y_hat x_hat b DeltaL DeltaU (gamma fp n)) :
    ∃ DeltaA : Fin n → Fin n → ℝ,
      (∀ i j, |DeltaA i j| ≤
        higham9_14_h (gamma fp n) * |A i j|) ∧
      (∀ i, ∑ j : Fin n, (A i j + DeltaA i j) * x_hat j = b i) := by
  rcases
      higham9_20_tridiag_lu_perturbation_model_of_rectRoundedLoop_square_gamma
        fp n A hn (hLU.det_ne_zero_iff_U_diag_ne_zero.mp hdetA)
        hU_budget_le hL_budget_le with
    ⟨DeltaA_LU, h20⟩
  simpa [one_mul] using
    (higham9_14_source_h_bound_of_absLU_le_const_absA_and_9_20_9_21_models
      n A
      (higham9_2_rectRoundedLoopL fp (Nat.le_refl n) A)
      (higham9_2_rectRoundedLoopU fp (Nat.le_refl n) A)
      y_hat x_hat b 1 (gamma fp n)
      (by norm_num) (gamma_nonneg fp hn) hγ_lt_one
      (fun i j => by
        simpa [one_mul] using
          le_of_eq
            (higham9_12_mmatrix_lu_optimal_growth n A
              (higham9_2_rectRoundedLoopL fp (Nat.le_refl n) A)
              (higham9_2_rectRoundedLoopU fp (Nat.le_refl n) A)
              hM hLU hL_nn hU_nn i j))
      DeltaA_LU DeltaL DeltaU h20 h21)

/-- **Theorem 9.14**, source-predicate sign-equivalent executable
rounded-loop model-consuming `f(γ_n)` bound. -/
theorem higham9_14_sign_equiv_source_f_bound_of_IsSignEquiv_rectRoundedLoop_square_models_gamma
    (fp : FPModel) (n : ℕ)
    (A B L_B U_B : Fin n → Fin n → ℝ)
    (y_hat x_hat b : Fin n → ℝ)
    (DeltaL DeltaU : Fin n → Fin n → ℝ)
    (hn : gammaValid fp n)
    (hAB : IsSignEquiv n A B)
    (hB_growth : ∀ i j : Fin n,
      ∑ k : Fin n, |L_B i k| * |U_B k j| = |B i j|)
    (hL_abs : ∀ i k : Fin n,
      |higham9_2_rectRoundedLoopL fp (Nat.le_refl n) A i k| = |L_B i k|)
    (hU_abs : ∀ k j : Fin n,
      |higham9_2_rectRoundedLoopU fp (Nat.le_refl n) A k j| = |U_B k j|)
    (hLU : LUFactSpec n A
      (higham9_2_rectRoundedLoopL fp (Nat.le_refl n) A)
      (higham9_2_rectRoundedLoopU fp (Nat.le_refl n) A))
    (hdetA : Matrix.det (Matrix.of A : Matrix (Fin n) (Fin n) ℝ) ≠ 0)
    (hU_budget_le : ∀ k j : Fin n, k.val ≤ j.val →
      higham9_2_rectDoolittleUAbsBudget fp (Nat.le_refl n) A
          (higham9_2_rectRoundedLoopL fp (Nat.le_refl n) A)
          (higham9_2_rectRoundedLoopU fp (Nat.le_refl n) A) k j ≤
        gamma fp n *
          |higham9_2_rectRoundedLoopU fp (Nat.le_refl n) A k j|)
    (hL_budget_le : ∀ i k : Fin n, k.val < i.val →
      higham9_2_rectDoolittleLAbsBudget fp A
          (higham9_2_rectRoundedLoopL fp (Nat.le_refl n) A)
          (higham9_2_rectRoundedLoopU fp (Nat.le_refl n) A) i k ≤
        gamma fp n *
          |higham9_2_rectRoundedLoopL fp (Nat.le_refl n) A i k *
            higham9_2_rectRoundedLoopU fp (Nat.le_refl n) A k k|)
    (h21 : higham9_21_tridiag_solve_perturbation_model n
      (higham9_2_rectRoundedLoopL fp (Nat.le_refl n) A)
      (higham9_2_rectRoundedLoopU fp (Nat.le_refl n) A)
      y_hat x_hat b DeltaL DeltaU (gamma fp n)) :
    ∃ DeltaA : Fin n → Fin n → ℝ,
      (∀ i j, |DeltaA i j| ≤
        higham9_14_f (gamma fp n) * |A i j|) ∧
      (∀ i, ∑ j : Fin n, (A i j + DeltaA i j) * x_hat j = b i) := by
  rcases
      higham9_20_tridiag_lu_perturbation_model_of_rectRoundedLoop_square_gamma
        fp n A hn (hLU.det_ne_zero_iff_U_diag_ne_zero.mp hdetA)
        hU_budget_le hL_budget_le with
    ⟨DeltaA_LU, h20⟩
  simpa [one_mul] using
    (higham9_14_source_f_bound_of_absLU_le_const_absA_and_9_20_9_21_models
      n A
      (higham9_2_rectRoundedLoopL fp (Nat.le_refl n) A)
      (higham9_2_rectRoundedLoopU fp (Nat.le_refl n) A)
      y_hat x_hat b 1 (gamma fp n) (gamma_nonneg fp hn)
      (fun i j => by
        simpa [one_mul] using
          le_of_eq
            (higham9_12_sign_equiv_optimal_growth_of_IsSignEquiv
              n A B L_B U_B
              (higham9_2_rectRoundedLoopL fp (Nat.le_refl n) A)
              (higham9_2_rectRoundedLoopU fp (Nat.le_refl n) A)
              hAB hB_growth hL_abs hU_abs i j))
      DeltaA_LU DeltaL DeltaU h20 h21)

/-- **Theorem 9.14**, source-predicate sign-equivalent executable
rounded-loop model-consuming final `h(γ_n)` bound. -/
theorem higham9_14_sign_equiv_source_h_bound_of_IsSignEquiv_rectRoundedLoop_square_models_gamma
    (fp : FPModel) (n : ℕ)
    (A B L_B U_B : Fin n → Fin n → ℝ)
    (y_hat x_hat b : Fin n → ℝ)
    (DeltaL DeltaU : Fin n → Fin n → ℝ)
    (hn : gammaValid fp n)
    (hγ_lt_one : gamma fp n < 1)
    (hAB : IsSignEquiv n A B)
    (hB_growth : ∀ i j : Fin n,
      ∑ k : Fin n, |L_B i k| * |U_B k j| = |B i j|)
    (hL_abs : ∀ i k : Fin n,
      |higham9_2_rectRoundedLoopL fp (Nat.le_refl n) A i k| = |L_B i k|)
    (hU_abs : ∀ k j : Fin n,
      |higham9_2_rectRoundedLoopU fp (Nat.le_refl n) A k j| = |U_B k j|)
    (hLU : LUFactSpec n A
      (higham9_2_rectRoundedLoopL fp (Nat.le_refl n) A)
      (higham9_2_rectRoundedLoopU fp (Nat.le_refl n) A))
    (hdetA : Matrix.det (Matrix.of A : Matrix (Fin n) (Fin n) ℝ) ≠ 0)
    (hU_budget_le : ∀ k j : Fin n, k.val ≤ j.val →
      higham9_2_rectDoolittleUAbsBudget fp (Nat.le_refl n) A
          (higham9_2_rectRoundedLoopL fp (Nat.le_refl n) A)
          (higham9_2_rectRoundedLoopU fp (Nat.le_refl n) A) k j ≤
        gamma fp n *
          |higham9_2_rectRoundedLoopU fp (Nat.le_refl n) A k j|)
    (hL_budget_le : ∀ i k : Fin n, k.val < i.val →
      higham9_2_rectDoolittleLAbsBudget fp A
          (higham9_2_rectRoundedLoopL fp (Nat.le_refl n) A)
          (higham9_2_rectRoundedLoopU fp (Nat.le_refl n) A) i k ≤
        gamma fp n *
          |higham9_2_rectRoundedLoopL fp (Nat.le_refl n) A i k *
            higham9_2_rectRoundedLoopU fp (Nat.le_refl n) A k k|)
    (h21 : higham9_21_tridiag_solve_perturbation_model n
      (higham9_2_rectRoundedLoopL fp (Nat.le_refl n) A)
      (higham9_2_rectRoundedLoopU fp (Nat.le_refl n) A)
      y_hat x_hat b DeltaL DeltaU (gamma fp n)) :
    ∃ DeltaA : Fin n → Fin n → ℝ,
      (∀ i j, |DeltaA i j| ≤
        higham9_14_h (gamma fp n) * |A i j|) ∧
      (∀ i, ∑ j : Fin n, (A i j + DeltaA i j) * x_hat j = b i) := by
  rcases
      higham9_20_tridiag_lu_perturbation_model_of_rectRoundedLoop_square_gamma
        fp n A hn (hLU.det_ne_zero_iff_U_diag_ne_zero.mp hdetA)
        hU_budget_le hL_budget_le with
    ⟨DeltaA_LU, h20⟩
  simpa [one_mul] using
    (higham9_14_source_h_bound_of_absLU_le_const_absA_and_9_20_9_21_models
      n A
      (higham9_2_rectRoundedLoopL fp (Nat.le_refl n) A)
      (higham9_2_rectRoundedLoopU fp (Nat.le_refl n) A)
      y_hat x_hat b 1 (gamma fp n)
      (by norm_num) (gamma_nonneg fp hn) hγ_lt_one
      (fun i j => by
        simpa [one_mul] using
          le_of_eq
            (higham9_12_sign_equiv_optimal_growth_of_IsSignEquiv
              n A B L_B U_B
              (higham9_2_rectRoundedLoopL fp (Nat.le_refl n) A)
              (higham9_2_rectRoundedLoopU fp (Nat.le_refl n) A)
              hAB hB_growth hL_abs hU_abs i j))
      DeltaA_LU DeltaL DeltaU h20 h21)

/-- **Theorem 9.14**, column-dominant builder source-model `f(u)` bound.

This is the equation-(9.22) analogue of
`higham9_14_tridiag_colDiagDom_fu_bound_from_builders`: the explicit
`TridiagData` builders supply the structural growth factor `3`, while the
equation (9.20)/(9.21) source perturbation models remain visible hypotheses. -/
theorem higham9_14_tridiag_colDiagDom_source_f_bound_from_builders (n : ℕ)
    (T : higham9_18_TridiagData n)
    (l_hat u_hat : Fin n → ℝ)
    (y_hat x_hat b : Fin n → ℝ)
    (u : ℝ) (hu : 0 ≤ u)
    (hLU_exact : ∀ i j : Fin n,
      ∑ k : Fin n, tridiag_L_matrix l_hat i k *
        tridiag_U_matrix u_hat T.c k j =
        higham9_18_tridiag_to_matrix T i j)
    (hl : ∀ i : Fin n, |l_hat i| ≤ 1)
    (hColDom : IsDiagDominant n (higham9_18_tridiag_to_matrix T))
    (DeltaA_LU DeltaL DeltaU : Fin n → Fin n → ℝ)
    (h20 : higham9_20_tridiag_lu_perturbation_model n
      (higham9_18_tridiag_to_matrix T)
      (tridiag_L_matrix l_hat) (tridiag_U_matrix u_hat T.c)
      DeltaA_LU u)
    (h21 : higham9_21_tridiag_solve_perturbation_model n
      (tridiag_L_matrix l_hat) (tridiag_U_matrix u_hat T.c)
      y_hat x_hat b DeltaL DeltaU u) :
    ∃ DeltaA : Fin n → Fin n → ℝ,
      (∀ i j, |DeltaA i j| ≤
        3 * higham9_14_f u * |higham9_18_tridiag_to_matrix T i j|) ∧
      (∀ i, ∑ j : Fin n,
        (higham9_18_tridiag_to_matrix T i j + DeltaA i j) * x_hat j =
          b i) :=
  higham9_14_source_f_bound_of_absLU_le_const_absA_and_9_20_9_21_models
    n (higham9_18_tridiag_to_matrix T)
    (tridiag_L_matrix l_hat) (tridiag_U_matrix u_hat T.c)
    y_hat x_hat b 3 u hu
    (higham9_13_tridiag_builder_growth_bound_3 T l_hat u_hat
      hLU_exact hl hColDom)
    DeltaA_LU DeltaL DeltaU h20 h21

/-- **Theorem 9.14**, row-dominant builder source-model `f(u)` bound. -/
theorem higham9_14_tridiag_rowDiagDom_source_f_bound_from_builders (n : ℕ)
    (T : higham9_18_TridiagData n)
    (l_hat u_hat : Fin n → ℝ)
    (y_hat x_hat b : Fin n → ℝ)
    (u : ℝ) (hu : 0 ≤ u)
    (hLU_exact : ∀ i j : Fin n,
      ∑ k : Fin n, tridiag_L_matrix l_hat i k *
        tridiag_U_matrix u_hat T.c k j =
        higham9_18_tridiag_to_matrix T i j)
    (hRowDom : IsRowDiagDominant n (higham9_18_tridiag_to_matrix T))
    (DeltaA_LU DeltaL DeltaU : Fin n → Fin n → ℝ)
    (h20 : higham9_20_tridiag_lu_perturbation_model n
      (higham9_18_tridiag_to_matrix T)
      (tridiag_L_matrix l_hat) (tridiag_U_matrix u_hat T.c)
      DeltaA_LU u)
    (h21 : higham9_21_tridiag_solve_perturbation_model n
      (tridiag_L_matrix l_hat) (tridiag_U_matrix u_hat T.c)
      y_hat x_hat b DeltaL DeltaU u) :
    ∃ DeltaA : Fin n → Fin n → ℝ,
      (∀ i j, |DeltaA i j| ≤
        3 * higham9_14_f u * |higham9_18_tridiag_to_matrix T i j|) ∧
      (∀ i, ∑ j : Fin n,
        (higham9_18_tridiag_to_matrix T i j + DeltaA i j) * x_hat j =
          b i) :=
  higham9_14_source_f_bound_of_absLU_le_const_absA_and_9_20_9_21_models
    n (higham9_18_tridiag_to_matrix T)
    (tridiag_L_matrix l_hat) (tridiag_U_matrix u_hat T.c)
    y_hat x_hat b 3 u hu
    (higham9_13_rowDiagDom_tridiag_builder_growth_bound_3 T l_hat u_hat
      hLU_exact hRowDom)
    DeltaA_LU DeltaL DeltaU h20 h21

/-- **Theorem 9.14**, column-dominant recurrence source-model `f(u)` bound.

This discharges the exact-product certificate in the builder source-model
wrapper from the exact tridiagonal recurrence (9.19). -/
theorem higham9_14_tridiag_colDiagDom_source_f_bound_from_recurrence (n : ℕ)
    (T : higham9_18_TridiagData n)
    (l_hat u_hat : Fin n → ℝ)
    (y_hat x_hat b : Fin n → ℝ)
    (u : ℝ) (hu : 0 ≤ u)
    (hrec : higham9_19_TridiagExactLURecurrence T l_hat u_hat)
    (hl : ∀ i : Fin n, |l_hat i| ≤ 1)
    (hColDom : IsDiagDominant n (higham9_18_tridiag_to_matrix T))
    (DeltaA_LU DeltaL DeltaU : Fin n → Fin n → ℝ)
    (h20 : higham9_20_tridiag_lu_perturbation_model n
      (higham9_18_tridiag_to_matrix T)
      (tridiag_L_matrix l_hat) (tridiag_U_matrix u_hat T.c)
      DeltaA_LU u)
    (h21 : higham9_21_tridiag_solve_perturbation_model n
      (tridiag_L_matrix l_hat) (tridiag_U_matrix u_hat T.c)
      y_hat x_hat b DeltaL DeltaU u) :
    ∃ DeltaA : Fin n → Fin n → ℝ,
      (∀ i j, |DeltaA i j| ≤
        3 * higham9_14_f u * |higham9_18_tridiag_to_matrix T i j|) ∧
      (∀ i, ∑ j : Fin n,
        (higham9_18_tridiag_to_matrix T i j + DeltaA i j) * x_hat j =
          b i) :=
  higham9_14_tridiag_colDiagDom_source_f_bound_from_builders n
    T l_hat u_hat y_hat x_hat b u hu
    (higham9_19_tridiag_exact_product_of_recurrence T l_hat u_hat hrec)
    hl hColDom DeltaA_LU DeltaL DeltaU h20 h21

/-- **Theorem 9.14**, row-dominant recurrence source-model `f(u)` bound. -/
theorem higham9_14_tridiag_rowDiagDom_source_f_bound_from_recurrence (n : ℕ)
    (T : higham9_18_TridiagData n)
    (l_hat u_hat : Fin n → ℝ)
    (y_hat x_hat b : Fin n → ℝ)
    (u : ℝ) (hu : 0 ≤ u)
    (hrec : higham9_19_TridiagExactLURecurrence T l_hat u_hat)
    (hRowDom : IsRowDiagDominant n (higham9_18_tridiag_to_matrix T))
    (DeltaA_LU DeltaL DeltaU : Fin n → Fin n → ℝ)
    (h20 : higham9_20_tridiag_lu_perturbation_model n
      (higham9_18_tridiag_to_matrix T)
      (tridiag_L_matrix l_hat) (tridiag_U_matrix u_hat T.c)
      DeltaA_LU u)
    (h21 : higham9_21_tridiag_solve_perturbation_model n
      (tridiag_L_matrix l_hat) (tridiag_U_matrix u_hat T.c)
      y_hat x_hat b DeltaL DeltaU u) :
    ∃ DeltaA : Fin n → Fin n → ℝ,
      (∀ i j, |DeltaA i j| ≤
        3 * higham9_14_f u * |higham9_18_tridiag_to_matrix T i j|) ∧
      (∀ i, ∑ j : Fin n,
        (higham9_18_tridiag_to_matrix T i j + DeltaA i j) * x_hat j =
          b i) :=
  higham9_14_tridiag_rowDiagDom_source_f_bound_from_builders n
    T l_hat u_hat y_hat x_hat b u hu
    (higham9_19_tridiag_exact_product_of_recurrence T l_hat u_hat hrec)
    hRowDom DeltaA_LU DeltaL DeltaU h20 h21

/-- **Theorem 9.14**, column-dominant builder source-model final `h(u)`
bound.

This is the final-coefficient counterpart of
`higham9_14_tridiag_colDiagDom_source_f_bound_from_builders`: the explicit
builders supply the structural `3|A|` comparison and the equation
(9.20)/(9.21) models supply the rounded source perturbations. -/
theorem higham9_14_tridiag_colDiagDom_source_h_bound_from_builders (n : ℕ)
    (T : higham9_18_TridiagData n)
    (l_hat u_hat : Fin n → ℝ)
    (y_hat x_hat b : Fin n → ℝ)
    (u : ℝ) (hu : 0 ≤ u) (hu_lt_one : u < 1)
    (hLU_exact : ∀ i j : Fin n,
      ∑ k : Fin n, tridiag_L_matrix l_hat i k *
        tridiag_U_matrix u_hat T.c k j =
        higham9_18_tridiag_to_matrix T i j)
    (hl : ∀ i : Fin n, |l_hat i| ≤ 1)
    (hColDom : IsDiagDominant n (higham9_18_tridiag_to_matrix T))
    (DeltaA_LU DeltaL DeltaU : Fin n → Fin n → ℝ)
    (h20 : higham9_20_tridiag_lu_perturbation_model n
      (higham9_18_tridiag_to_matrix T)
      (tridiag_L_matrix l_hat) (tridiag_U_matrix u_hat T.c)
      DeltaA_LU u)
    (h21 : higham9_21_tridiag_solve_perturbation_model n
      (tridiag_L_matrix l_hat) (tridiag_U_matrix u_hat T.c)
      y_hat x_hat b DeltaL DeltaU u) :
    ∃ DeltaA : Fin n → Fin n → ℝ,
      (∀ i j, |DeltaA i j| ≤
        3 * higham9_14_h u * |higham9_18_tridiag_to_matrix T i j|) ∧
      (∀ i, ∑ j : Fin n,
        (higham9_18_tridiag_to_matrix T i j + DeltaA i j) * x_hat j =
          b i) :=
  higham9_14_source_h_bound_of_absLU_le_const_absA_and_9_20_9_21_models
    n (higham9_18_tridiag_to_matrix T)
    (tridiag_L_matrix l_hat) (tridiag_U_matrix u_hat T.c)
    y_hat x_hat b 3 u (by norm_num) hu hu_lt_one
    (higham9_13_tridiag_builder_growth_bound_3 T l_hat u_hat
      hLU_exact hl hColDom)
    DeltaA_LU DeltaL DeltaU h20 h21

/-- **Theorem 9.14**, row-dominant builder source-model final `h(u)` bound. -/
theorem higham9_14_tridiag_rowDiagDom_source_h_bound_from_builders (n : ℕ)
    (T : higham9_18_TridiagData n)
    (l_hat u_hat : Fin n → ℝ)
    (y_hat x_hat b : Fin n → ℝ)
    (u : ℝ) (hu : 0 ≤ u) (hu_lt_one : u < 1)
    (hLU_exact : ∀ i j : Fin n,
      ∑ k : Fin n, tridiag_L_matrix l_hat i k *
        tridiag_U_matrix u_hat T.c k j =
        higham9_18_tridiag_to_matrix T i j)
    (hRowDom : IsRowDiagDominant n (higham9_18_tridiag_to_matrix T))
    (DeltaA_LU DeltaL DeltaU : Fin n → Fin n → ℝ)
    (h20 : higham9_20_tridiag_lu_perturbation_model n
      (higham9_18_tridiag_to_matrix T)
      (tridiag_L_matrix l_hat) (tridiag_U_matrix u_hat T.c)
      DeltaA_LU u)
    (h21 : higham9_21_tridiag_solve_perturbation_model n
      (tridiag_L_matrix l_hat) (tridiag_U_matrix u_hat T.c)
      y_hat x_hat b DeltaL DeltaU u) :
    ∃ DeltaA : Fin n → Fin n → ℝ,
      (∀ i j, |DeltaA i j| ≤
        3 * higham9_14_h u * |higham9_18_tridiag_to_matrix T i j|) ∧
      (∀ i, ∑ j : Fin n,
        (higham9_18_tridiag_to_matrix T i j + DeltaA i j) * x_hat j =
          b i) :=
  higham9_14_source_h_bound_of_absLU_le_const_absA_and_9_20_9_21_models
    n (higham9_18_tridiag_to_matrix T)
    (tridiag_L_matrix l_hat) (tridiag_U_matrix u_hat T.c)
    y_hat x_hat b 3 u (by norm_num) hu hu_lt_one
    (higham9_13_rowDiagDom_tridiag_builder_growth_bound_3
      T l_hat u_hat hLU_exact hRowDom)
    DeltaA_LU DeltaL DeltaU h20 h21

/-- **Theorem 9.14**, column-dominant recurrence source-model final `h(u)`
bound. -/
theorem higham9_14_tridiag_colDiagDom_source_h_bound_from_recurrence (n : ℕ)
    (T : higham9_18_TridiagData n)
    (l_hat u_hat : Fin n → ℝ)
    (y_hat x_hat b : Fin n → ℝ)
    (u : ℝ) (hu : 0 ≤ u) (hu_lt_one : u < 1)
    (hrec : higham9_19_TridiagExactLURecurrence T l_hat u_hat)
    (hl : ∀ i : Fin n, |l_hat i| ≤ 1)
    (hColDom : IsDiagDominant n (higham9_18_tridiag_to_matrix T))
    (DeltaA_LU DeltaL DeltaU : Fin n → Fin n → ℝ)
    (h20 : higham9_20_tridiag_lu_perturbation_model n
      (higham9_18_tridiag_to_matrix T)
      (tridiag_L_matrix l_hat) (tridiag_U_matrix u_hat T.c)
      DeltaA_LU u)
    (h21 : higham9_21_tridiag_solve_perturbation_model n
      (tridiag_L_matrix l_hat) (tridiag_U_matrix u_hat T.c)
      y_hat x_hat b DeltaL DeltaU u) :
    ∃ DeltaA : Fin n → Fin n → ℝ,
      (∀ i j, |DeltaA i j| ≤
        3 * higham9_14_h u * |higham9_18_tridiag_to_matrix T i j|) ∧
      (∀ i, ∑ j : Fin n,
        (higham9_18_tridiag_to_matrix T i j + DeltaA i j) * x_hat j =
          b i) :=
  higham9_14_tridiag_colDiagDom_source_h_bound_from_builders n
    T l_hat u_hat y_hat x_hat b u hu hu_lt_one
    (higham9_19_tridiag_exact_product_of_recurrence T l_hat u_hat hrec)
    hl hColDom DeltaA_LU DeltaL DeltaU h20 h21

/-- **Theorem 9.14**, row-dominant recurrence source-model final `h(u)`
bound. -/
theorem higham9_14_tridiag_rowDiagDom_source_h_bound_from_recurrence (n : ℕ)
    (T : higham9_18_TridiagData n)
    (l_hat u_hat : Fin n → ℝ)
    (y_hat x_hat b : Fin n → ℝ)
    (u : ℝ) (hu : 0 ≤ u) (hu_lt_one : u < 1)
    (hrec : higham9_19_TridiagExactLURecurrence T l_hat u_hat)
    (hRowDom : IsRowDiagDominant n (higham9_18_tridiag_to_matrix T))
    (DeltaA_LU DeltaL DeltaU : Fin n → Fin n → ℝ)
    (h20 : higham9_20_tridiag_lu_perturbation_model n
      (higham9_18_tridiag_to_matrix T)
      (tridiag_L_matrix l_hat) (tridiag_U_matrix u_hat T.c)
      DeltaA_LU u)
    (h21 : higham9_21_tridiag_solve_perturbation_model n
      (tridiag_L_matrix l_hat) (tridiag_U_matrix u_hat T.c)
      y_hat x_hat b DeltaL DeltaU u) :
    ∃ DeltaA : Fin n → Fin n → ℝ,
      (∀ i j, |DeltaA i j| ≤
        3 * higham9_14_h u * |higham9_18_tridiag_to_matrix T i j|) ∧
      (∀ i, ∑ j : Fin n,
        (higham9_18_tridiag_to_matrix T i j + DeltaA i j) * x_hat j =
          b i) :=
  higham9_14_tridiag_rowDiagDom_source_h_bound_from_builders n
    T l_hat u_hat y_hat x_hat b u hu hu_lt_one
    (higham9_19_tridiag_exact_product_of_recurrence T l_hat u_hat hrec)
    hRowDom DeltaA_LU DeltaL DeltaU h20 h21

/-- **Theorem 9.14**, column-dominant builder source-model `f(gamma_n)`
bound. -/
theorem higham9_14_tridiag_colDiagDom_source_f_bound_from_builders_gamma
    (fp : FPModel) (n : ℕ)
    (T : higham9_18_TridiagData n)
    (l_hat u_hat : Fin n → ℝ)
    (y_hat x_hat b : Fin n → ℝ)
    (hn : gammaValid fp n)
    (hLU_exact : ∀ i j : Fin n,
      ∑ k : Fin n, tridiag_L_matrix l_hat i k *
        tridiag_U_matrix u_hat T.c k j =
        higham9_18_tridiag_to_matrix T i j)
    (hl : ∀ i : Fin n, |l_hat i| ≤ 1)
    (hColDom : IsDiagDominant n (higham9_18_tridiag_to_matrix T))
    (DeltaA_LU DeltaL DeltaU : Fin n → Fin n → ℝ)
    (h20 : higham9_20_tridiag_lu_perturbation_model n
      (higham9_18_tridiag_to_matrix T)
      (tridiag_L_matrix l_hat) (tridiag_U_matrix u_hat T.c)
      DeltaA_LU (gamma fp n))
    (h21 : higham9_21_tridiag_solve_perturbation_model n
      (tridiag_L_matrix l_hat) (tridiag_U_matrix u_hat T.c)
      y_hat x_hat b DeltaL DeltaU (gamma fp n)) :
    ∃ DeltaA : Fin n → Fin n → ℝ,
      (∀ i j, |DeltaA i j| ≤
        3 * higham9_14_f (gamma fp n) *
          |higham9_18_tridiag_to_matrix T i j|) ∧
      (∀ i, ∑ j : Fin n,
        (higham9_18_tridiag_to_matrix T i j + DeltaA i j) * x_hat j =
          b i) :=
  higham9_14_tridiag_colDiagDom_source_f_bound_from_builders n
    T l_hat u_hat y_hat x_hat b (gamma fp n) (gamma_nonneg fp hn)
    hLU_exact hl hColDom DeltaA_LU DeltaL DeltaU h20 h21

/-- **Theorem 9.14**, row-dominant builder source-model `f(gamma_n)`
bound. -/
theorem higham9_14_tridiag_rowDiagDom_source_f_bound_from_builders_gamma
    (fp : FPModel) (n : ℕ)
    (T : higham9_18_TridiagData n)
    (l_hat u_hat : Fin n → ℝ)
    (y_hat x_hat b : Fin n → ℝ)
    (hn : gammaValid fp n)
    (hLU_exact : ∀ i j : Fin n,
      ∑ k : Fin n, tridiag_L_matrix l_hat i k *
        tridiag_U_matrix u_hat T.c k j =
        higham9_18_tridiag_to_matrix T i j)
    (hRowDom : IsRowDiagDominant n (higham9_18_tridiag_to_matrix T))
    (DeltaA_LU DeltaL DeltaU : Fin n → Fin n → ℝ)
    (h20 : higham9_20_tridiag_lu_perturbation_model n
      (higham9_18_tridiag_to_matrix T)
      (tridiag_L_matrix l_hat) (tridiag_U_matrix u_hat T.c)
      DeltaA_LU (gamma fp n))
    (h21 : higham9_21_tridiag_solve_perturbation_model n
      (tridiag_L_matrix l_hat) (tridiag_U_matrix u_hat T.c)
      y_hat x_hat b DeltaL DeltaU (gamma fp n)) :
    ∃ DeltaA : Fin n → Fin n → ℝ,
      (∀ i j, |DeltaA i j| ≤
        3 * higham9_14_f (gamma fp n) *
          |higham9_18_tridiag_to_matrix T i j|) ∧
      (∀ i, ∑ j : Fin n,
        (higham9_18_tridiag_to_matrix T i j + DeltaA i j) * x_hat j =
          b i) :=
  higham9_14_tridiag_rowDiagDom_source_f_bound_from_builders n
    T l_hat u_hat y_hat x_hat b (gamma fp n) (gamma_nonneg fp hn)
    hLU_exact hRowDom DeltaA_LU DeltaL DeltaU h20 h21

/-- **Theorem 9.14**, column-dominant recurrence source-model `f(gamma_n)`
bound. -/
theorem higham9_14_tridiag_colDiagDom_source_f_bound_from_recurrence_gamma
    (fp : FPModel) (n : ℕ)
    (T : higham9_18_TridiagData n)
    (l_hat u_hat : Fin n → ℝ)
    (y_hat x_hat b : Fin n → ℝ)
    (hn : gammaValid fp n)
    (hrec : higham9_19_TridiagExactLURecurrence T l_hat u_hat)
    (hl : ∀ i : Fin n, |l_hat i| ≤ 1)
    (hColDom : IsDiagDominant n (higham9_18_tridiag_to_matrix T))
    (DeltaA_LU DeltaL DeltaU : Fin n → Fin n → ℝ)
    (h20 : higham9_20_tridiag_lu_perturbation_model n
      (higham9_18_tridiag_to_matrix T)
      (tridiag_L_matrix l_hat) (tridiag_U_matrix u_hat T.c)
      DeltaA_LU (gamma fp n))
    (h21 : higham9_21_tridiag_solve_perturbation_model n
      (tridiag_L_matrix l_hat) (tridiag_U_matrix u_hat T.c)
      y_hat x_hat b DeltaL DeltaU (gamma fp n)) :
    ∃ DeltaA : Fin n → Fin n → ℝ,
      (∀ i j, |DeltaA i j| ≤
        3 * higham9_14_f (gamma fp n) *
          |higham9_18_tridiag_to_matrix T i j|) ∧
      (∀ i, ∑ j : Fin n,
        (higham9_18_tridiag_to_matrix T i j + DeltaA i j) * x_hat j =
          b i) :=
  higham9_14_tridiag_colDiagDom_source_f_bound_from_recurrence n
    T l_hat u_hat y_hat x_hat b (gamma fp n) (gamma_nonneg fp hn)
    hrec hl hColDom DeltaA_LU DeltaL DeltaU h20 h21

/-- **Theorem 9.14**, row-dominant recurrence source-model `f(gamma_n)`
bound. -/
theorem higham9_14_tridiag_rowDiagDom_source_f_bound_from_recurrence_gamma
    (fp : FPModel) (n : ℕ)
    (T : higham9_18_TridiagData n)
    (l_hat u_hat : Fin n → ℝ)
    (y_hat x_hat b : Fin n → ℝ)
    (hn : gammaValid fp n)
    (hrec : higham9_19_TridiagExactLURecurrence T l_hat u_hat)
    (hRowDom : IsRowDiagDominant n (higham9_18_tridiag_to_matrix T))
    (DeltaA_LU DeltaL DeltaU : Fin n → Fin n → ℝ)
    (h20 : higham9_20_tridiag_lu_perturbation_model n
      (higham9_18_tridiag_to_matrix T)
      (tridiag_L_matrix l_hat) (tridiag_U_matrix u_hat T.c)
      DeltaA_LU (gamma fp n))
    (h21 : higham9_21_tridiag_solve_perturbation_model n
      (tridiag_L_matrix l_hat) (tridiag_U_matrix u_hat T.c)
      y_hat x_hat b DeltaL DeltaU (gamma fp n)) :
    ∃ DeltaA : Fin n → Fin n → ℝ,
      (∀ i j, |DeltaA i j| ≤
        3 * higham9_14_f (gamma fp n) *
          |higham9_18_tridiag_to_matrix T i j|) ∧
      (∀ i, ∑ j : Fin n,
        (higham9_18_tridiag_to_matrix T i j + DeltaA i j) * x_hat j =
          b i) :=
  higham9_14_tridiag_rowDiagDom_source_f_bound_from_recurrence n
    T l_hat u_hat y_hat x_hat b (gamma fp n) (gamma_nonneg fp hn)
    hrec hRowDom DeltaA_LU DeltaL DeltaU h20 h21

/-- **Theorem 9.14**, column-dominant builder source-model `h(gamma_n)`
bound. -/
theorem higham9_14_tridiag_colDiagDom_source_h_bound_from_builders_gamma
    (fp : FPModel) (n : ℕ)
    (T : higham9_18_TridiagData n)
    (l_hat u_hat : Fin n → ℝ)
    (y_hat x_hat b : Fin n → ℝ)
    (hn : gammaValid fp n) (hgamma_lt_one : gamma fp n < 1)
    (hLU_exact : ∀ i j : Fin n,
      ∑ k : Fin n, tridiag_L_matrix l_hat i k *
        tridiag_U_matrix u_hat T.c k j =
        higham9_18_tridiag_to_matrix T i j)
    (hl : ∀ i : Fin n, |l_hat i| ≤ 1)
    (hColDom : IsDiagDominant n (higham9_18_tridiag_to_matrix T))
    (DeltaA_LU DeltaL DeltaU : Fin n → Fin n → ℝ)
    (h20 : higham9_20_tridiag_lu_perturbation_model n
      (higham9_18_tridiag_to_matrix T)
      (tridiag_L_matrix l_hat) (tridiag_U_matrix u_hat T.c)
      DeltaA_LU (gamma fp n))
    (h21 : higham9_21_tridiag_solve_perturbation_model n
      (tridiag_L_matrix l_hat) (tridiag_U_matrix u_hat T.c)
      y_hat x_hat b DeltaL DeltaU (gamma fp n)) :
    ∃ DeltaA : Fin n → Fin n → ℝ,
      (∀ i j, |DeltaA i j| ≤
        3 * higham9_14_h (gamma fp n) *
          |higham9_18_tridiag_to_matrix T i j|) ∧
      (∀ i, ∑ j : Fin n,
        (higham9_18_tridiag_to_matrix T i j + DeltaA i j) * x_hat j =
          b i) :=
  higham9_14_tridiag_colDiagDom_source_h_bound_from_builders n
    T l_hat u_hat y_hat x_hat b (gamma fp n) (gamma_nonneg fp hn)
    hgamma_lt_one hLU_exact hl hColDom DeltaA_LU DeltaL DeltaU h20 h21

/-- **Theorem 9.14**, row-dominant builder source-model `h(gamma_n)`
bound. -/
theorem higham9_14_tridiag_rowDiagDom_source_h_bound_from_builders_gamma
    (fp : FPModel) (n : ℕ)
    (T : higham9_18_TridiagData n)
    (l_hat u_hat : Fin n → ℝ)
    (y_hat x_hat b : Fin n → ℝ)
    (hn : gammaValid fp n) (hgamma_lt_one : gamma fp n < 1)
    (hLU_exact : ∀ i j : Fin n,
      ∑ k : Fin n, tridiag_L_matrix l_hat i k *
        tridiag_U_matrix u_hat T.c k j =
        higham9_18_tridiag_to_matrix T i j)
    (hRowDom : IsRowDiagDominant n (higham9_18_tridiag_to_matrix T))
    (DeltaA_LU DeltaL DeltaU : Fin n → Fin n → ℝ)
    (h20 : higham9_20_tridiag_lu_perturbation_model n
      (higham9_18_tridiag_to_matrix T)
      (tridiag_L_matrix l_hat) (tridiag_U_matrix u_hat T.c)
      DeltaA_LU (gamma fp n))
    (h21 : higham9_21_tridiag_solve_perturbation_model n
      (tridiag_L_matrix l_hat) (tridiag_U_matrix u_hat T.c)
      y_hat x_hat b DeltaL DeltaU (gamma fp n)) :
    ∃ DeltaA : Fin n → Fin n → ℝ,
      (∀ i j, |DeltaA i j| ≤
        3 * higham9_14_h (gamma fp n) *
          |higham9_18_tridiag_to_matrix T i j|) ∧
      (∀ i, ∑ j : Fin n,
        (higham9_18_tridiag_to_matrix T i j + DeltaA i j) * x_hat j =
          b i) :=
  higham9_14_tridiag_rowDiagDom_source_h_bound_from_builders n
    T l_hat u_hat y_hat x_hat b (gamma fp n) (gamma_nonneg fp hn)
    hgamma_lt_one hLU_exact hRowDom DeltaA_LU DeltaL DeltaU h20 h21

/-- **Theorem 9.14**, column-dominant recurrence source-model `h(gamma_n)`
bound. -/
theorem higham9_14_tridiag_colDiagDom_source_h_bound_from_recurrence_gamma
    (fp : FPModel) (n : ℕ)
    (T : higham9_18_TridiagData n)
    (l_hat u_hat : Fin n → ℝ)
    (y_hat x_hat b : Fin n → ℝ)
    (hn : gammaValid fp n) (hgamma_lt_one : gamma fp n < 1)
    (hrec : higham9_19_TridiagExactLURecurrence T l_hat u_hat)
    (hl : ∀ i : Fin n, |l_hat i| ≤ 1)
    (hColDom : IsDiagDominant n (higham9_18_tridiag_to_matrix T))
    (DeltaA_LU DeltaL DeltaU : Fin n → Fin n → ℝ)
    (h20 : higham9_20_tridiag_lu_perturbation_model n
      (higham9_18_tridiag_to_matrix T)
      (tridiag_L_matrix l_hat) (tridiag_U_matrix u_hat T.c)
      DeltaA_LU (gamma fp n))
    (h21 : higham9_21_tridiag_solve_perturbation_model n
      (tridiag_L_matrix l_hat) (tridiag_U_matrix u_hat T.c)
      y_hat x_hat b DeltaL DeltaU (gamma fp n)) :
    ∃ DeltaA : Fin n → Fin n → ℝ,
      (∀ i j, |DeltaA i j| ≤
        3 * higham9_14_h (gamma fp n) *
          |higham9_18_tridiag_to_matrix T i j|) ∧
      (∀ i, ∑ j : Fin n,
        (higham9_18_tridiag_to_matrix T i j + DeltaA i j) * x_hat j =
          b i) :=
  higham9_14_tridiag_colDiagDom_source_h_bound_from_recurrence n
    T l_hat u_hat y_hat x_hat b (gamma fp n) (gamma_nonneg fp hn)
    hgamma_lt_one hrec hl hColDom DeltaA_LU DeltaL DeltaU h20 h21

/-- **Theorem 9.14**, row-dominant recurrence source-model `h(gamma_n)`
bound. -/
theorem higham9_14_tridiag_rowDiagDom_source_h_bound_from_recurrence_gamma
    (fp : FPModel) (n : ℕ)
    (T : higham9_18_TridiagData n)
    (l_hat u_hat : Fin n → ℝ)
    (y_hat x_hat b : Fin n → ℝ)
    (hn : gammaValid fp n) (hgamma_lt_one : gamma fp n < 1)
    (hrec : higham9_19_TridiagExactLURecurrence T l_hat u_hat)
    (hRowDom : IsRowDiagDominant n (higham9_18_tridiag_to_matrix T))
    (DeltaA_LU DeltaL DeltaU : Fin n → Fin n → ℝ)
    (h20 : higham9_20_tridiag_lu_perturbation_model n
      (higham9_18_tridiag_to_matrix T)
      (tridiag_L_matrix l_hat) (tridiag_U_matrix u_hat T.c)
      DeltaA_LU (gamma fp n))
    (h21 : higham9_21_tridiag_solve_perturbation_model n
      (tridiag_L_matrix l_hat) (tridiag_U_matrix u_hat T.c)
      y_hat x_hat b DeltaL DeltaU (gamma fp n)) :
    ∃ DeltaA : Fin n → Fin n → ℝ,
      (∀ i j, |DeltaA i j| ≤
        3 * higham9_14_h (gamma fp n) *
          |higham9_18_tridiag_to_matrix T i j|) ∧
      (∀ i, ∑ j : Fin n,
        (higham9_18_tridiag_to_matrix T i j + DeltaA i j) * x_hat j =
          b i) :=
  higham9_14_tridiag_rowDiagDom_source_h_bound_from_recurrence n
    T l_hat u_hat y_hat x_hat b (gamma fp n) (gamma_nonneg fp hn)
    hgamma_lt_one hrec hRowDom DeltaA_LU DeltaL DeltaU h20 h21

/-- **Theorem 9.14**, column-dominant builder source-model production from
certificates and actual triangular solves. -/
theorem higham9_14_tridiag_colDiagDom_source_f_bound_from_builders_LUBackwardError_fl_triangular_solves
    (fp : FPModel) (n : ℕ)
    (T : higham9_18_TridiagData n)
    (l_hat u_hat : Fin n → ℝ)
    (b : Fin n → ℝ)
    (ε u : ℝ) (hu : 0 ≤ u)
    (hn : gammaValid fp n)
    (hBE : LUBackwardError n (higham9_18_tridiag_to_matrix T)
      (tridiag_L_matrix l_hat) (tridiag_U_matrix u_hat T.c) ε)
    (hε_le_u : ε ≤ u)
    (hγ_le_u : gamma fp n ≤ u)
    (hU_diag : ∀ i : Fin n, tridiag_U_matrix u_hat T.c i i ≠ 0)
    (hLU_exact : ∀ i j : Fin n,
      ∑ k : Fin n, tridiag_L_matrix l_hat i k *
        tridiag_U_matrix u_hat T.c k j =
        higham9_18_tridiag_to_matrix T i j)
    (hl : ∀ i : Fin n, |l_hat i| ≤ 1)
    (hColDom : IsDiagDominant n (higham9_18_tridiag_to_matrix T)) :
    let y_hat := fl_forwardSub fp n (tridiag_L_matrix l_hat) b
    let x_hat := fl_backSub fp n (tridiag_U_matrix u_hat T.c) y_hat
    ∃ DeltaA : Fin n → Fin n → ℝ,
      (∀ i j, |DeltaA i j| ≤
        3 * higham9_14_f u * |higham9_18_tridiag_to_matrix T i j|) ∧
      (∀ i, ∑ j : Fin n,
        (higham9_18_tridiag_to_matrix T i j + DeltaA i j) * x_hat j =
          b i) :=
  higham9_14_source_f_bound_of_LUBackwardError_fl_triangular_solves_gamma_le
    fp n (higham9_18_tridiag_to_matrix T)
    (tridiag_L_matrix l_hat) (tridiag_U_matrix u_hat T.c)
    b 3 ε u hu hn hBE hε_le_u hγ_le_u hU_diag
    (higham9_13_tridiag_builder_growth_bound_3 T l_hat u_hat
      hLU_exact hl hColDom)

/-- **Theorem 9.14**, row-dominant builder source-model production from
certificates and actual triangular solves. -/
theorem higham9_14_tridiag_rowDiagDom_source_f_bound_from_builders_LUBackwardError_fl_triangular_solves
    (fp : FPModel) (n : ℕ)
    (T : higham9_18_TridiagData n)
    (l_hat u_hat : Fin n → ℝ)
    (b : Fin n → ℝ)
    (ε u : ℝ) (hu : 0 ≤ u)
    (hn : gammaValid fp n)
    (hBE : LUBackwardError n (higham9_18_tridiag_to_matrix T)
      (tridiag_L_matrix l_hat) (tridiag_U_matrix u_hat T.c) ε)
    (hε_le_u : ε ≤ u)
    (hγ_le_u : gamma fp n ≤ u)
    (hU_diag : ∀ i : Fin n, tridiag_U_matrix u_hat T.c i i ≠ 0)
    (hLU_exact : ∀ i j : Fin n,
      ∑ k : Fin n, tridiag_L_matrix l_hat i k *
        tridiag_U_matrix u_hat T.c k j =
        higham9_18_tridiag_to_matrix T i j)
    (hRowDom : IsRowDiagDominant n (higham9_18_tridiag_to_matrix T)) :
    let y_hat := fl_forwardSub fp n (tridiag_L_matrix l_hat) b
    let x_hat := fl_backSub fp n (tridiag_U_matrix u_hat T.c) y_hat
    ∃ DeltaA : Fin n → Fin n → ℝ,
      (∀ i j, |DeltaA i j| ≤
        3 * higham9_14_f u * |higham9_18_tridiag_to_matrix T i j|) ∧
      (∀ i, ∑ j : Fin n,
        (higham9_18_tridiag_to_matrix T i j + DeltaA i j) * x_hat j =
          b i) :=
  higham9_14_source_f_bound_of_LUBackwardError_fl_triangular_solves_gamma_le
    fp n (higham9_18_tridiag_to_matrix T)
    (tridiag_L_matrix l_hat) (tridiag_U_matrix u_hat T.c)
    b 3 ε u hu hn hBE hε_le_u hγ_le_u hU_diag
    (higham9_13_rowDiagDom_tridiag_builder_growth_bound_3
      T l_hat u_hat hLU_exact hRowDom)

/-- **Theorem 9.14**, column-dominant recurrence source-model production from
certificates and actual triangular solves. -/
theorem higham9_14_tridiag_colDiagDom_source_f_bound_from_recurrence_LUBackwardError_fl_triangular_solves
    (fp : FPModel) (n : ℕ)
    (T : higham9_18_TridiagData n)
    (l_hat u_hat : Fin n → ℝ)
    (b : Fin n → ℝ)
    (ε u : ℝ) (hu : 0 ≤ u)
    (hn : gammaValid fp n)
    (hBE : LUBackwardError n (higham9_18_tridiag_to_matrix T)
      (tridiag_L_matrix l_hat) (tridiag_U_matrix u_hat T.c) ε)
    (hε_le_u : ε ≤ u)
    (hγ_le_u : gamma fp n ≤ u)
    (hU_diag : ∀ i : Fin n, tridiag_U_matrix u_hat T.c i i ≠ 0)
    (hrec : higham9_19_TridiagExactLURecurrence T l_hat u_hat)
    (hl : ∀ i : Fin n, |l_hat i| ≤ 1)
    (hColDom : IsDiagDominant n (higham9_18_tridiag_to_matrix T)) :
    let y_hat := fl_forwardSub fp n (tridiag_L_matrix l_hat) b
    let x_hat := fl_backSub fp n (tridiag_U_matrix u_hat T.c) y_hat
    ∃ DeltaA : Fin n → Fin n → ℝ,
      (∀ i j, |DeltaA i j| ≤
        3 * higham9_14_f u * |higham9_18_tridiag_to_matrix T i j|) ∧
      (∀ i, ∑ j : Fin n,
        (higham9_18_tridiag_to_matrix T i j + DeltaA i j) * x_hat j =
          b i) :=
  higham9_14_tridiag_colDiagDom_source_f_bound_from_builders_LUBackwardError_fl_triangular_solves
    fp n T l_hat u_hat b ε u hu hn hBE hε_le_u hγ_le_u hU_diag
    (higham9_19_tridiag_exact_product_of_recurrence T l_hat u_hat hrec)
    hl hColDom

/-- **Theorem 9.14**, row-dominant recurrence source-model production from
certificates and actual triangular solves. -/
theorem higham9_14_tridiag_rowDiagDom_source_f_bound_from_recurrence_LUBackwardError_fl_triangular_solves
    (fp : FPModel) (n : ℕ)
    (T : higham9_18_TridiagData n)
    (l_hat u_hat : Fin n → ℝ)
    (b : Fin n → ℝ)
    (ε u : ℝ) (hu : 0 ≤ u)
    (hn : gammaValid fp n)
    (hBE : LUBackwardError n (higham9_18_tridiag_to_matrix T)
      (tridiag_L_matrix l_hat) (tridiag_U_matrix u_hat T.c) ε)
    (hε_le_u : ε ≤ u)
    (hγ_le_u : gamma fp n ≤ u)
    (hU_diag : ∀ i : Fin n, tridiag_U_matrix u_hat T.c i i ≠ 0)
    (hrec : higham9_19_TridiagExactLURecurrence T l_hat u_hat)
    (hRowDom : IsRowDiagDominant n (higham9_18_tridiag_to_matrix T)) :
    let y_hat := fl_forwardSub fp n (tridiag_L_matrix l_hat) b
    let x_hat := fl_backSub fp n (tridiag_U_matrix u_hat T.c) y_hat
    ∃ DeltaA : Fin n → Fin n → ℝ,
      (∀ i j, |DeltaA i j| ≤
        3 * higham9_14_f u * |higham9_18_tridiag_to_matrix T i j|) ∧
      (∀ i, ∑ j : Fin n,
        (higham9_18_tridiag_to_matrix T i j + DeltaA i j) * x_hat j =
          b i) :=
  higham9_14_tridiag_rowDiagDom_source_f_bound_from_builders_LUBackwardError_fl_triangular_solves
    fp n T l_hat u_hat b ε u hu hn hBE hε_le_u hγ_le_u hU_diag
    (higham9_19_tridiag_exact_product_of_recurrence T l_hat u_hat hrec)
    hRowDom

/-- **Theorem 9.14**, column-dominant builder source-model production from
certificates and actual triangular solves with final `h(u)` coefficient. -/
theorem higham9_14_tridiag_colDiagDom_source_h_bound_from_builders_LUBackwardError_fl_triangular_solves
    (fp : FPModel) (n : ℕ)
    (T : higham9_18_TridiagData n)
    (l_hat u_hat : Fin n → ℝ)
    (b : Fin n → ℝ)
    (ε u : ℝ) (hu : 0 ≤ u) (hu_lt_one : u < 1)
    (hn : gammaValid fp n)
    (hBE : LUBackwardError n (higham9_18_tridiag_to_matrix T)
      (tridiag_L_matrix l_hat) (tridiag_U_matrix u_hat T.c) ε)
    (hε_le_u : ε ≤ u)
    (hγ_le_u : gamma fp n ≤ u)
    (hU_diag : ∀ i : Fin n, tridiag_U_matrix u_hat T.c i i ≠ 0)
    (hLU_exact : ∀ i j : Fin n,
      ∑ k : Fin n, tridiag_L_matrix l_hat i k *
        tridiag_U_matrix u_hat T.c k j =
        higham9_18_tridiag_to_matrix T i j)
    (hl : ∀ i : Fin n, |l_hat i| ≤ 1)
    (hColDom : IsDiagDominant n (higham9_18_tridiag_to_matrix T)) :
    let y_hat := fl_forwardSub fp n (tridiag_L_matrix l_hat) b
    let x_hat := fl_backSub fp n (tridiag_U_matrix u_hat T.c) y_hat
    ∃ DeltaA : Fin n → Fin n → ℝ,
      (∀ i j, |DeltaA i j| ≤
        3 * higham9_14_h u * |higham9_18_tridiag_to_matrix T i j|) ∧
      (∀ i, ∑ j : Fin n,
        (higham9_18_tridiag_to_matrix T i j + DeltaA i j) * x_hat j =
          b i) :=
  higham9_14_source_h_bound_of_LUBackwardError_fl_triangular_solves_const_gamma_le
    fp n (higham9_18_tridiag_to_matrix T)
    (tridiag_L_matrix l_hat) (tridiag_U_matrix u_hat T.c)
    b 3 ε u (by norm_num) hu hu_lt_one hn hBE hε_le_u hγ_le_u hU_diag
    (higham9_13_tridiag_builder_growth_bound_3 T l_hat u_hat
      hLU_exact hl hColDom)

/-- **Theorem 9.14**, row-dominant builder source-model production from
certificates and actual triangular solves with final `h(u)` coefficient. -/
theorem higham9_14_tridiag_rowDiagDom_source_h_bound_from_builders_LUBackwardError_fl_triangular_solves
    (fp : FPModel) (n : ℕ)
    (T : higham9_18_TridiagData n)
    (l_hat u_hat : Fin n → ℝ)
    (b : Fin n → ℝ)
    (ε u : ℝ) (hu : 0 ≤ u) (hu_lt_one : u < 1)
    (hn : gammaValid fp n)
    (hBE : LUBackwardError n (higham9_18_tridiag_to_matrix T)
      (tridiag_L_matrix l_hat) (tridiag_U_matrix u_hat T.c) ε)
    (hε_le_u : ε ≤ u)
    (hγ_le_u : gamma fp n ≤ u)
    (hU_diag : ∀ i : Fin n, tridiag_U_matrix u_hat T.c i i ≠ 0)
    (hLU_exact : ∀ i j : Fin n,
      ∑ k : Fin n, tridiag_L_matrix l_hat i k *
        tridiag_U_matrix u_hat T.c k j =
        higham9_18_tridiag_to_matrix T i j)
    (hRowDom : IsRowDiagDominant n (higham9_18_tridiag_to_matrix T)) :
    let y_hat := fl_forwardSub fp n (tridiag_L_matrix l_hat) b
    let x_hat := fl_backSub fp n (tridiag_U_matrix u_hat T.c) y_hat
    ∃ DeltaA : Fin n → Fin n → ℝ,
      (∀ i j, |DeltaA i j| ≤
        3 * higham9_14_h u * |higham9_18_tridiag_to_matrix T i j|) ∧
      (∀ i, ∑ j : Fin n,
        (higham9_18_tridiag_to_matrix T i j + DeltaA i j) * x_hat j =
          b i) :=
  higham9_14_source_h_bound_of_LUBackwardError_fl_triangular_solves_const_gamma_le
    fp n (higham9_18_tridiag_to_matrix T)
    (tridiag_L_matrix l_hat) (tridiag_U_matrix u_hat T.c)
    b 3 ε u (by norm_num) hu hu_lt_one hn hBE hε_le_u hγ_le_u hU_diag
    (higham9_13_rowDiagDom_tridiag_builder_growth_bound_3
      T l_hat u_hat hLU_exact hRowDom)

/-- **Theorem 9.14**, column-dominant recurrence source-model production from
certificates and actual triangular solves with final `h(u)` coefficient. -/
theorem higham9_14_tridiag_colDiagDom_source_h_bound_from_recurrence_LUBackwardError_fl_triangular_solves
    (fp : FPModel) (n : ℕ)
    (T : higham9_18_TridiagData n)
    (l_hat u_hat : Fin n → ℝ)
    (b : Fin n → ℝ)
    (ε u : ℝ) (hu : 0 ≤ u) (hu_lt_one : u < 1)
    (hn : gammaValid fp n)
    (hBE : LUBackwardError n (higham9_18_tridiag_to_matrix T)
      (tridiag_L_matrix l_hat) (tridiag_U_matrix u_hat T.c) ε)
    (hε_le_u : ε ≤ u)
    (hγ_le_u : gamma fp n ≤ u)
    (hU_diag : ∀ i : Fin n, tridiag_U_matrix u_hat T.c i i ≠ 0)
    (hrec : higham9_19_TridiagExactLURecurrence T l_hat u_hat)
    (hl : ∀ i : Fin n, |l_hat i| ≤ 1)
    (hColDom : IsDiagDominant n (higham9_18_tridiag_to_matrix T)) :
    let y_hat := fl_forwardSub fp n (tridiag_L_matrix l_hat) b
    let x_hat := fl_backSub fp n (tridiag_U_matrix u_hat T.c) y_hat
    ∃ DeltaA : Fin n → Fin n → ℝ,
      (∀ i j, |DeltaA i j| ≤
        3 * higham9_14_h u * |higham9_18_tridiag_to_matrix T i j|) ∧
      (∀ i, ∑ j : Fin n,
        (higham9_18_tridiag_to_matrix T i j + DeltaA i j) * x_hat j =
          b i) :=
  higham9_14_tridiag_colDiagDom_source_h_bound_from_builders_LUBackwardError_fl_triangular_solves
    fp n T l_hat u_hat b ε u hu hu_lt_one hn hBE hε_le_u hγ_le_u hU_diag
    (higham9_19_tridiag_exact_product_of_recurrence T l_hat u_hat hrec)
    hl hColDom

/-- **Theorem 9.14**, row-dominant recurrence source-model production from
certificates and actual triangular solves with final `h(u)` coefficient. -/
theorem higham9_14_tridiag_rowDiagDom_source_h_bound_from_recurrence_LUBackwardError_fl_triangular_solves
    (fp : FPModel) (n : ℕ)
    (T : higham9_18_TridiagData n)
    (l_hat u_hat : Fin n → ℝ)
    (b : Fin n → ℝ)
    (ε u : ℝ) (hu : 0 ≤ u) (hu_lt_one : u < 1)
    (hn : gammaValid fp n)
    (hBE : LUBackwardError n (higham9_18_tridiag_to_matrix T)
      (tridiag_L_matrix l_hat) (tridiag_U_matrix u_hat T.c) ε)
    (hε_le_u : ε ≤ u)
    (hγ_le_u : gamma fp n ≤ u)
    (hU_diag : ∀ i : Fin n, tridiag_U_matrix u_hat T.c i i ≠ 0)
    (hrec : higham9_19_TridiagExactLURecurrence T l_hat u_hat)
    (hRowDom : IsRowDiagDominant n (higham9_18_tridiag_to_matrix T)) :
    let y_hat := fl_forwardSub fp n (tridiag_L_matrix l_hat) b
    let x_hat := fl_backSub fp n (tridiag_U_matrix u_hat T.c) y_hat
    ∃ DeltaA : Fin n → Fin n → ℝ,
      (∀ i j, |DeltaA i j| ≤
        3 * higham9_14_h u * |higham9_18_tridiag_to_matrix T i j|) ∧
      (∀ i, ∑ j : Fin n,
        (higham9_18_tridiag_to_matrix T i j + DeltaA i j) * x_hat j =
          b i) :=
  higham9_14_tridiag_rowDiagDom_source_h_bound_from_builders_LUBackwardError_fl_triangular_solves
    fp n T l_hat u_hat b ε u hu hu_lt_one hn hBE hε_le_u hγ_le_u hU_diag
    (higham9_19_tridiag_exact_product_of_recurrence T l_hat u_hat hrec)
    hRowDom

/-- **Theorem 9.14**, column-dominant exact builder factors with actual
triangular solves.

The explicit tridiagonal builder product is converted to `LUFactSpec`, giving
equation (9.20) with zero LU-factorization coefficient; the actual
`fl_forwardSub`/`fl_backSub` calls supply equation (9.21). -/
theorem higham9_14_tridiag_colDiagDom_source_f_bound_from_builders_LUFactSpec_fl_triangular_solves
    (fp : FPModel) (n : ℕ)
    (T : higham9_18_TridiagData n)
    (l_hat u_hat : Fin n → ℝ)
    (b : Fin n → ℝ)
    (u : ℝ) (hu : 0 ≤ u)
    (hn : gammaValid fp n)
    (hγ_le_u : gamma fp n ≤ u)
    (hU_diag : ∀ i : Fin n, tridiag_U_matrix u_hat T.c i i ≠ 0)
    (hLU_exact : ∀ i j : Fin n,
      ∑ k : Fin n, tridiag_L_matrix l_hat i k *
        tridiag_U_matrix u_hat T.c k j =
        higham9_18_tridiag_to_matrix T i j)
    (hl : ∀ i : Fin n, |l_hat i| ≤ 1)
    (hColDom : IsDiagDominant n (higham9_18_tridiag_to_matrix T)) :
    let y_hat := fl_forwardSub fp n (tridiag_L_matrix l_hat) b
    let x_hat := fl_backSub fp n (tridiag_U_matrix u_hat T.c) y_hat
    ∃ DeltaA : Fin n → Fin n → ℝ,
      (∀ i j, |DeltaA i j| ≤
        3 * higham9_14_f u * |higham9_18_tridiag_to_matrix T i j|) ∧
      (∀ i, ∑ j : Fin n,
        (higham9_18_tridiag_to_matrix T i j + DeltaA i j) * x_hat j =
          b i) :=
  higham9_14_source_f_bound_of_LUFactSpec_fl_triangular_solves_gamma_le
    fp n (higham9_18_tridiag_to_matrix T)
    (tridiag_L_matrix l_hat) (tridiag_U_matrix u_hat T.c)
    b 3 u hu hn
    (higham9_19_tridiag_LUFactSpec_of_exact_product T l_hat u_hat hLU_exact)
    hγ_le_u hU_diag
    (higham9_13_tridiag_builder_growth_bound_3 T l_hat u_hat
      hLU_exact hl hColDom)

/-- **Theorem 9.14**, row-dominant exact builder factors with actual
triangular solves. -/
theorem higham9_14_tridiag_rowDiagDom_source_f_bound_from_builders_LUFactSpec_fl_triangular_solves
    (fp : FPModel) (n : ℕ)
    (T : higham9_18_TridiagData n)
    (l_hat u_hat : Fin n → ℝ)
    (b : Fin n → ℝ)
    (u : ℝ) (hu : 0 ≤ u)
    (hn : gammaValid fp n)
    (hγ_le_u : gamma fp n ≤ u)
    (hU_diag : ∀ i : Fin n, tridiag_U_matrix u_hat T.c i i ≠ 0)
    (hLU_exact : ∀ i j : Fin n,
      ∑ k : Fin n, tridiag_L_matrix l_hat i k *
        tridiag_U_matrix u_hat T.c k j =
        higham9_18_tridiag_to_matrix T i j)
    (hRowDom : IsRowDiagDominant n (higham9_18_tridiag_to_matrix T)) :
    let y_hat := fl_forwardSub fp n (tridiag_L_matrix l_hat) b
    let x_hat := fl_backSub fp n (tridiag_U_matrix u_hat T.c) y_hat
    ∃ DeltaA : Fin n → Fin n → ℝ,
      (∀ i j, |DeltaA i j| ≤
        3 * higham9_14_f u * |higham9_18_tridiag_to_matrix T i j|) ∧
      (∀ i, ∑ j : Fin n,
        (higham9_18_tridiag_to_matrix T i j + DeltaA i j) * x_hat j =
          b i) :=
  higham9_14_source_f_bound_of_LUFactSpec_fl_triangular_solves_gamma_le
    fp n (higham9_18_tridiag_to_matrix T)
    (tridiag_L_matrix l_hat) (tridiag_U_matrix u_hat T.c)
    b 3 u hu hn
    (higham9_19_tridiag_LUFactSpec_of_exact_product T l_hat u_hat hLU_exact)
    hγ_le_u hU_diag
    (higham9_13_rowDiagDom_tridiag_builder_growth_bound_3
      T l_hat u_hat hLU_exact hRowDom)

/-- **Theorem 9.14**, column-dominant exact recurrence factors with actual
triangular solves. -/
theorem higham9_14_tridiag_colDiagDom_source_f_bound_from_recurrence_LUFactSpec_fl_triangular_solves
    (fp : FPModel) (n : ℕ)
    (T : higham9_18_TridiagData n)
    (l_hat u_hat : Fin n → ℝ)
    (b : Fin n → ℝ)
    (u : ℝ) (hu : 0 ≤ u)
    (hn : gammaValid fp n)
    (hγ_le_u : gamma fp n ≤ u)
    (hU_diag : ∀ i : Fin n, tridiag_U_matrix u_hat T.c i i ≠ 0)
    (hrec : higham9_19_TridiagExactLURecurrence T l_hat u_hat)
    (hl : ∀ i : Fin n, |l_hat i| ≤ 1)
    (hColDom : IsDiagDominant n (higham9_18_tridiag_to_matrix T)) :
    let y_hat := fl_forwardSub fp n (tridiag_L_matrix l_hat) b
    let x_hat := fl_backSub fp n (tridiag_U_matrix u_hat T.c) y_hat
    ∃ DeltaA : Fin n → Fin n → ℝ,
      (∀ i j, |DeltaA i j| ≤
        3 * higham9_14_f u * |higham9_18_tridiag_to_matrix T i j|) ∧
      (∀ i, ∑ j : Fin n,
        (higham9_18_tridiag_to_matrix T i j + DeltaA i j) * x_hat j =
          b i) :=
  higham9_14_tridiag_colDiagDom_source_f_bound_from_builders_LUFactSpec_fl_triangular_solves
    fp n T l_hat u_hat b u hu hn hγ_le_u hU_diag
    (higham9_19_tridiag_exact_product_of_recurrence T l_hat u_hat hrec)
    hl hColDom

/-- **Theorem 9.14**, row-dominant exact recurrence factors with actual
triangular solves. -/
theorem higham9_14_tridiag_rowDiagDom_source_f_bound_from_recurrence_LUFactSpec_fl_triangular_solves
    (fp : FPModel) (n : ℕ)
    (T : higham9_18_TridiagData n)
    (l_hat u_hat : Fin n → ℝ)
    (b : Fin n → ℝ)
    (u : ℝ) (hu : 0 ≤ u)
    (hn : gammaValid fp n)
    (hγ_le_u : gamma fp n ≤ u)
    (hU_diag : ∀ i : Fin n, tridiag_U_matrix u_hat T.c i i ≠ 0)
    (hrec : higham9_19_TridiagExactLURecurrence T l_hat u_hat)
    (hRowDom : IsRowDiagDominant n (higham9_18_tridiag_to_matrix T)) :
    let y_hat := fl_forwardSub fp n (tridiag_L_matrix l_hat) b
    let x_hat := fl_backSub fp n (tridiag_U_matrix u_hat T.c) y_hat
    ∃ DeltaA : Fin n → Fin n → ℝ,
      (∀ i j, |DeltaA i j| ≤
        3 * higham9_14_f u * |higham9_18_tridiag_to_matrix T i j|) ∧
      (∀ i, ∑ j : Fin n,
        (higham9_18_tridiag_to_matrix T i j + DeltaA i j) * x_hat j =
          b i) :=
  higham9_14_tridiag_rowDiagDom_source_f_bound_from_builders_LUFactSpec_fl_triangular_solves
    fp n T l_hat u_hat b u hu hn hγ_le_u hU_diag
    (higham9_19_tridiag_exact_product_of_recurrence T l_hat u_hat hrec)
    hRowDom

/-- **Theorem 9.14**, column-dominant exact builder factors with actual
triangular solves and final `h(u)` coefficient. -/
theorem higham9_14_tridiag_colDiagDom_source_h_bound_from_builders_LUFactSpec_fl_triangular_solves
    (fp : FPModel) (n : ℕ)
    (T : higham9_18_TridiagData n)
    (l_hat u_hat : Fin n → ℝ)
    (b : Fin n → ℝ)
    (u : ℝ) (hu : 0 ≤ u) (hu_lt_one : u < 1)
    (hn : gammaValid fp n)
    (hγ_le_u : gamma fp n ≤ u)
    (hU_diag : ∀ i : Fin n, tridiag_U_matrix u_hat T.c i i ≠ 0)
    (hLU_exact : ∀ i j : Fin n,
      ∑ k : Fin n, tridiag_L_matrix l_hat i k *
        tridiag_U_matrix u_hat T.c k j =
        higham9_18_tridiag_to_matrix T i j)
    (hl : ∀ i : Fin n, |l_hat i| ≤ 1)
    (hColDom : IsDiagDominant n (higham9_18_tridiag_to_matrix T)) :
    let y_hat := fl_forwardSub fp n (tridiag_L_matrix l_hat) b
    let x_hat := fl_backSub fp n (tridiag_U_matrix u_hat T.c) y_hat
    ∃ DeltaA : Fin n → Fin n → ℝ,
      (∀ i j, |DeltaA i j| ≤
        3 * higham9_14_h u * |higham9_18_tridiag_to_matrix T i j|) ∧
      (∀ i, ∑ j : Fin n,
        (higham9_18_tridiag_to_matrix T i j + DeltaA i j) * x_hat j =
          b i) :=
  higham9_14_source_h_bound_of_LUFactSpec_fl_triangular_solves_const_gamma_le
    fp n (higham9_18_tridiag_to_matrix T)
    (tridiag_L_matrix l_hat) (tridiag_U_matrix u_hat T.c)
    b 3 u (by norm_num) hu hu_lt_one hn
    (higham9_19_tridiag_LUFactSpec_of_exact_product T l_hat u_hat hLU_exact)
    hγ_le_u hU_diag
    (higham9_13_tridiag_builder_growth_bound_3 T l_hat u_hat
      hLU_exact hl hColDom)

/-- **Theorem 9.14**, row-dominant exact builder factors with actual
triangular solves and final `h(u)` coefficient. -/
theorem higham9_14_tridiag_rowDiagDom_source_h_bound_from_builders_LUFactSpec_fl_triangular_solves
    (fp : FPModel) (n : ℕ)
    (T : higham9_18_TridiagData n)
    (l_hat u_hat : Fin n → ℝ)
    (b : Fin n → ℝ)
    (u : ℝ) (hu : 0 ≤ u) (hu_lt_one : u < 1)
    (hn : gammaValid fp n)
    (hγ_le_u : gamma fp n ≤ u)
    (hU_diag : ∀ i : Fin n, tridiag_U_matrix u_hat T.c i i ≠ 0)
    (hLU_exact : ∀ i j : Fin n,
      ∑ k : Fin n, tridiag_L_matrix l_hat i k *
        tridiag_U_matrix u_hat T.c k j =
        higham9_18_tridiag_to_matrix T i j)
    (hRowDom : IsRowDiagDominant n (higham9_18_tridiag_to_matrix T)) :
    let y_hat := fl_forwardSub fp n (tridiag_L_matrix l_hat) b
    let x_hat := fl_backSub fp n (tridiag_U_matrix u_hat T.c) y_hat
    ∃ DeltaA : Fin n → Fin n → ℝ,
      (∀ i j, |DeltaA i j| ≤
        3 * higham9_14_h u * |higham9_18_tridiag_to_matrix T i j|) ∧
      (∀ i, ∑ j : Fin n,
        (higham9_18_tridiag_to_matrix T i j + DeltaA i j) * x_hat j =
          b i) :=
  higham9_14_source_h_bound_of_LUFactSpec_fl_triangular_solves_const_gamma_le
    fp n (higham9_18_tridiag_to_matrix T)
    (tridiag_L_matrix l_hat) (tridiag_U_matrix u_hat T.c)
    b 3 u (by norm_num) hu hu_lt_one hn
    (higham9_19_tridiag_LUFactSpec_of_exact_product T l_hat u_hat hLU_exact)
    hγ_le_u hU_diag
    (higham9_13_rowDiagDom_tridiag_builder_growth_bound_3
      T l_hat u_hat hLU_exact hRowDom)

/-- **Theorem 9.14**, column-dominant exact recurrence factors with actual
triangular solves and final `h(u)` coefficient. -/
theorem higham9_14_tridiag_colDiagDom_source_h_bound_from_recurrence_LUFactSpec_fl_triangular_solves
    (fp : FPModel) (n : ℕ)
    (T : higham9_18_TridiagData n)
    (l_hat u_hat : Fin n → ℝ)
    (b : Fin n → ℝ)
    (u : ℝ) (hu : 0 ≤ u) (hu_lt_one : u < 1)
    (hn : gammaValid fp n)
    (hγ_le_u : gamma fp n ≤ u)
    (hU_diag : ∀ i : Fin n, tridiag_U_matrix u_hat T.c i i ≠ 0)
    (hrec : higham9_19_TridiagExactLURecurrence T l_hat u_hat)
    (hl : ∀ i : Fin n, |l_hat i| ≤ 1)
    (hColDom : IsDiagDominant n (higham9_18_tridiag_to_matrix T)) :
    let y_hat := fl_forwardSub fp n (tridiag_L_matrix l_hat) b
    let x_hat := fl_backSub fp n (tridiag_U_matrix u_hat T.c) y_hat
    ∃ DeltaA : Fin n → Fin n → ℝ,
      (∀ i j, |DeltaA i j| ≤
        3 * higham9_14_h u * |higham9_18_tridiag_to_matrix T i j|) ∧
      (∀ i, ∑ j : Fin n,
        (higham9_18_tridiag_to_matrix T i j + DeltaA i j) * x_hat j =
          b i) :=
  higham9_14_tridiag_colDiagDom_source_h_bound_from_builders_LUFactSpec_fl_triangular_solves
    fp n T l_hat u_hat b u hu hu_lt_one hn hγ_le_u hU_diag
    (higham9_19_tridiag_exact_product_of_recurrence T l_hat u_hat hrec)
    hl hColDom

/-- **Theorem 9.14**, row-dominant exact recurrence factors with actual
triangular solves and final `h(u)` coefficient. -/
theorem higham9_14_tridiag_rowDiagDom_source_h_bound_from_recurrence_LUFactSpec_fl_triangular_solves
    (fp : FPModel) (n : ℕ)
    (T : higham9_18_TridiagData n)
    (l_hat u_hat : Fin n → ℝ)
    (b : Fin n → ℝ)
    (u : ℝ) (hu : 0 ≤ u) (hu_lt_one : u < 1)
    (hn : gammaValid fp n)
    (hγ_le_u : gamma fp n ≤ u)
    (hU_diag : ∀ i : Fin n, tridiag_U_matrix u_hat T.c i i ≠ 0)
    (hrec : higham9_19_TridiagExactLURecurrence T l_hat u_hat)
    (hRowDom : IsRowDiagDominant n (higham9_18_tridiag_to_matrix T)) :
    let y_hat := fl_forwardSub fp n (tridiag_L_matrix l_hat) b
    let x_hat := fl_backSub fp n (tridiag_U_matrix u_hat T.c) y_hat
    ∃ DeltaA : Fin n → Fin n → ℝ,
      (∀ i j, |DeltaA i j| ≤
        3 * higham9_14_h u * |higham9_18_tridiag_to_matrix T i j|) ∧
      (∀ i, ∑ j : Fin n,
        (higham9_18_tridiag_to_matrix T i j + DeltaA i j) * x_hat j =
          b i) :=
  higham9_14_tridiag_rowDiagDom_source_h_bound_from_builders_LUFactSpec_fl_triangular_solves
    fp n T l_hat u_hat b u hu hu_lt_one hn hγ_le_u hU_diag
    (higham9_19_tridiag_exact_product_of_recurrence T l_hat u_hat hrec)
    hRowDom

/-- **Theorem 9.14**, column-dominant exact-LU source-model `f(u)` bound.

This is the equation-(9.22) source-model analogue of
`higham9_14_tridiag_colDiagDom_fu_bound_from_LUFactSpec`: an ordinary exact
`LUFactSpec` plus tridiagonality, nonsingularity, and column diagonal dominance
supplies `|Lhat||Uhat| <= 3|A|`; the perturbation models remain explicit. -/
theorem higham9_14_tridiag_colDiagDom_source_f_bound_from_LUFactSpec (n : ℕ)
    (A L_hat U_hat : Fin n → Fin n → ℝ)
    (y_hat x_hat b : Fin n → ℝ)
    (u : ℝ) (hu : 0 ≤ u)
    (hLU : LUFactSpec n A L_hat U_hat)
    (hdetA : Matrix.det (Matrix.of A : Matrix (Fin n) (Fin n) ℝ) ≠ 0)
    (hA_tridiag : IsTridiagonal n A)
    (hColDom : IsDiagDominant n A)
    (DeltaA_LU DeltaL DeltaU : Fin n → Fin n → ℝ)
    (h20 : higham9_20_tridiag_lu_perturbation_model n A L_hat U_hat
      DeltaA_LU u)
    (h21 : higham9_21_tridiag_solve_perturbation_model n L_hat U_hat
      y_hat x_hat b DeltaL DeltaU u) :
    ∃ DeltaA : Fin n → Fin n → ℝ,
      (∀ i j, |DeltaA i j| ≤ 3 * higham9_14_f u * |A i j|) ∧
      (∀ i, ∑ j : Fin n, (A i j + DeltaA i j) * x_hat j = b i) :=
  higham9_14_source_f_bound_of_absLU_le_const_absA_and_9_20_9_21_models
    n A L_hat U_hat y_hat x_hat b 3 u hu
    (higham9_13_colDiagDom_tridiag_growth_bound_3_of_LUFactSpec
      A L_hat U_hat hLU hdetA hA_tridiag hColDom)
    DeltaA_LU DeltaL DeltaU h20 h21

/-- **Theorem 9.14**, row-dominant exact-LU source-model `f(u)` bound. -/
theorem higham9_14_tridiag_rowDiagDom_source_f_bound_from_LUFactSpec (n : ℕ)
    (A L_hat U_hat : Fin n → Fin n → ℝ)
    (y_hat x_hat b : Fin n → ℝ)
    (u : ℝ) (hu : 0 ≤ u)
    (hLU : LUFactSpec n A L_hat U_hat)
    (hdetA : Matrix.det (Matrix.of A : Matrix (Fin n) (Fin n) ℝ) ≠ 0)
    (hA_tridiag : IsTridiagonal n A)
    (hRowDom : IsRowDiagDominant n A)
    (DeltaA_LU DeltaL DeltaU : Fin n → Fin n → ℝ)
    (h20 : higham9_20_tridiag_lu_perturbation_model n A L_hat U_hat
      DeltaA_LU u)
    (h21 : higham9_21_tridiag_solve_perturbation_model n L_hat U_hat
      y_hat x_hat b DeltaL DeltaU u) :
    ∃ DeltaA : Fin n → Fin n → ℝ,
      (∀ i j, |DeltaA i j| ≤ 3 * higham9_14_f u * |A i j|) ∧
      (∀ i, ∑ j : Fin n, (A i j + DeltaA i j) * x_hat j = b i) :=
  higham9_14_source_f_bound_of_absLU_le_const_absA_and_9_20_9_21_models
    n A L_hat U_hat y_hat x_hat b 3 u hu
    (higham9_13_rowDiagDom_tridiag_growth_bound_3_of_LUFactSpec
      A L_hat U_hat hLU hdetA hA_tridiag hRowDom)
    DeltaA_LU DeltaL DeltaU h20 h21

/-- **Theorem 9.14**, column-dominant exact-LU source-model final `h(u)`
bound.

This is the final-coefficient counterpart of
`higham9_14_tridiag_colDiagDom_source_f_bound_from_LUFactSpec`. -/
theorem higham9_14_tridiag_colDiagDom_source_h_bound_from_LUFactSpec (n : ℕ)
    (A L_hat U_hat : Fin n → Fin n → ℝ)
    (y_hat x_hat b : Fin n → ℝ)
    (u : ℝ) (hu : 0 ≤ u) (hu_lt_one : u < 1)
    (hLU : LUFactSpec n A L_hat U_hat)
    (hdetA : Matrix.det (Matrix.of A : Matrix (Fin n) (Fin n) ℝ) ≠ 0)
    (hA_tridiag : IsTridiagonal n A)
    (hColDom : IsDiagDominant n A)
    (DeltaA_LU DeltaL DeltaU : Fin n → Fin n → ℝ)
    (h20 : higham9_20_tridiag_lu_perturbation_model n A L_hat U_hat
      DeltaA_LU u)
    (h21 : higham9_21_tridiag_solve_perturbation_model n L_hat U_hat
      y_hat x_hat b DeltaL DeltaU u) :
    ∃ DeltaA : Fin n → Fin n → ℝ,
      (∀ i j, |DeltaA i j| ≤ 3 * higham9_14_h u * |A i j|) ∧
      (∀ i, ∑ j : Fin n, (A i j + DeltaA i j) * x_hat j = b i) :=
  higham9_14_source_h_bound_of_absLU_le_const_absA_and_9_20_9_21_models
    n A L_hat U_hat y_hat x_hat b 3 u (by norm_num) hu hu_lt_one
    (higham9_13_colDiagDom_tridiag_growth_bound_3_of_LUFactSpec
      A L_hat U_hat hLU hdetA hA_tridiag hColDom)
    DeltaA_LU DeltaL DeltaU h20 h21

/-- **Theorem 9.14**, row-dominant exact-LU source-model final `h(u)` bound. -/
theorem higham9_14_tridiag_rowDiagDom_source_h_bound_from_LUFactSpec (n : ℕ)
    (A L_hat U_hat : Fin n → Fin n → ℝ)
    (y_hat x_hat b : Fin n → ℝ)
    (u : ℝ) (hu : 0 ≤ u) (hu_lt_one : u < 1)
    (hLU : LUFactSpec n A L_hat U_hat)
    (hdetA : Matrix.det (Matrix.of A : Matrix (Fin n) (Fin n) ℝ) ≠ 0)
    (hA_tridiag : IsTridiagonal n A)
    (hRowDom : IsRowDiagDominant n A)
    (DeltaA_LU DeltaL DeltaU : Fin n → Fin n → ℝ)
    (h20 : higham9_20_tridiag_lu_perturbation_model n A L_hat U_hat
      DeltaA_LU u)
    (h21 : higham9_21_tridiag_solve_perturbation_model n L_hat U_hat
      y_hat x_hat b DeltaL DeltaU u) :
    ∃ DeltaA : Fin n → Fin n → ℝ,
      (∀ i j, |DeltaA i j| ≤ 3 * higham9_14_h u * |A i j|) ∧
      (∀ i, ∑ j : Fin n, (A i j + DeltaA i j) * x_hat j = b i) :=
  higham9_14_source_h_bound_of_absLU_le_const_absA_and_9_20_9_21_models
    n A L_hat U_hat y_hat x_hat b 3 u (by norm_num) hu hu_lt_one
    (higham9_13_rowDiagDom_tridiag_growth_bound_3_of_LUFactSpec
      A L_hat U_hat hLU hdetA hA_tridiag hRowDom)
    DeltaA_LU DeltaL DeltaU h20 h21

/-- **Theorem 9.14**, `TridiagData` column-dominant exact-LU source-model
`f(u)` bound. -/
theorem higham9_14_tridiag_data_colDiagDom_source_f_bound_from_LUFactSpec
    {n : ℕ}
    (T : higham9_18_TridiagData n)
    (L_hat U_hat : Fin n → Fin n → ℝ)
    (y_hat x_hat b : Fin n → ℝ)
    (u : ℝ) (hu : 0 ≤ u)
    (hLU : LUFactSpec n (higham9_18_tridiag_to_matrix T) L_hat U_hat)
    (hdetA :
      Matrix.det
        (Matrix.of (higham9_18_tridiag_to_matrix T) :
          Matrix (Fin n) (Fin n) ℝ) ≠ 0)
    (hColDom : IsDiagDominant n (higham9_18_tridiag_to_matrix T))
    (DeltaA_LU DeltaL DeltaU : Fin n → Fin n → ℝ)
    (h20 : higham9_20_tridiag_lu_perturbation_model n
      (higham9_18_tridiag_to_matrix T) L_hat U_hat DeltaA_LU u)
    (h21 : higham9_21_tridiag_solve_perturbation_model n L_hat U_hat
      y_hat x_hat b DeltaL DeltaU u) :
    ∃ DeltaA : Fin n → Fin n → ℝ,
      (∀ i j, |DeltaA i j| ≤
        3 * higham9_14_f u * |higham9_18_tridiag_to_matrix T i j|) ∧
      (∀ i, ∑ j : Fin n,
        (higham9_18_tridiag_to_matrix T i j + DeltaA i j) * x_hat j =
          b i) :=
  higham9_14_tridiag_colDiagDom_source_f_bound_from_LUFactSpec n
    (higham9_18_tridiag_to_matrix T) L_hat U_hat y_hat x_hat b u hu
    hLU hdetA (higham9_18_tridiag_to_matrix_isTridiagonal T) hColDom
    DeltaA_LU DeltaL DeltaU h20 h21

/-- **Theorem 9.14**, `TridiagData` row-dominant exact-LU source-model
`f(u)` bound. -/
theorem higham9_14_tridiag_data_rowDiagDom_source_f_bound_from_LUFactSpec
    {n : ℕ}
    (T : higham9_18_TridiagData n)
    (L_hat U_hat : Fin n → Fin n → ℝ)
    (y_hat x_hat b : Fin n → ℝ)
    (u : ℝ) (hu : 0 ≤ u)
    (hLU : LUFactSpec n (higham9_18_tridiag_to_matrix T) L_hat U_hat)
    (hdetA :
      Matrix.det
        (Matrix.of (higham9_18_tridiag_to_matrix T) :
          Matrix (Fin n) (Fin n) ℝ) ≠ 0)
    (hRowDom : IsRowDiagDominant n (higham9_18_tridiag_to_matrix T))
    (DeltaA_LU DeltaL DeltaU : Fin n → Fin n → ℝ)
    (h20 : higham9_20_tridiag_lu_perturbation_model n
      (higham9_18_tridiag_to_matrix T) L_hat U_hat DeltaA_LU u)
    (h21 : higham9_21_tridiag_solve_perturbation_model n L_hat U_hat
      y_hat x_hat b DeltaL DeltaU u) :
    ∃ DeltaA : Fin n → Fin n → ℝ,
      (∀ i j, |DeltaA i j| ≤
        3 * higham9_14_f u * |higham9_18_tridiag_to_matrix T i j|) ∧
      (∀ i, ∑ j : Fin n,
        (higham9_18_tridiag_to_matrix T i j + DeltaA i j) * x_hat j =
          b i) :=
  higham9_14_tridiag_rowDiagDom_source_f_bound_from_LUFactSpec n
    (higham9_18_tridiag_to_matrix T) L_hat U_hat y_hat x_hat b u hu
    hLU hdetA (higham9_18_tridiag_to_matrix_isTridiagonal T) hRowDom
    DeltaA_LU DeltaL DeltaU h20 h21

/-- **Theorem 9.14**, `TridiagData` column-dominant exact-LU source-model
final `h(u)` bound. -/
theorem higham9_14_tridiag_data_colDiagDom_source_h_bound_from_LUFactSpec
    {n : ℕ}
    (T : higham9_18_TridiagData n)
    (L_hat U_hat : Fin n → Fin n → ℝ)
    (y_hat x_hat b : Fin n → ℝ)
    (u : ℝ) (hu : 0 ≤ u) (hu_lt_one : u < 1)
    (hLU : LUFactSpec n (higham9_18_tridiag_to_matrix T) L_hat U_hat)
    (hdetA :
      Matrix.det
        (Matrix.of (higham9_18_tridiag_to_matrix T) :
          Matrix (Fin n) (Fin n) ℝ) ≠ 0)
    (hColDom : IsDiagDominant n (higham9_18_tridiag_to_matrix T))
    (DeltaA_LU DeltaL DeltaU : Fin n → Fin n → ℝ)
    (h20 : higham9_20_tridiag_lu_perturbation_model n
      (higham9_18_tridiag_to_matrix T) L_hat U_hat DeltaA_LU u)
    (h21 : higham9_21_tridiag_solve_perturbation_model n L_hat U_hat
      y_hat x_hat b DeltaL DeltaU u) :
    ∃ DeltaA : Fin n → Fin n → ℝ,
      (∀ i j, |DeltaA i j| ≤
        3 * higham9_14_h u * |higham9_18_tridiag_to_matrix T i j|) ∧
      (∀ i, ∑ j : Fin n,
        (higham9_18_tridiag_to_matrix T i j + DeltaA i j) * x_hat j =
          b i) :=
  higham9_14_tridiag_colDiagDom_source_h_bound_from_LUFactSpec n
    (higham9_18_tridiag_to_matrix T) L_hat U_hat y_hat x_hat b u hu
    hu_lt_one hLU hdetA (higham9_18_tridiag_to_matrix_isTridiagonal T)
    hColDom DeltaA_LU DeltaL DeltaU h20 h21

/-- **Theorem 9.14**, `TridiagData` row-dominant exact-LU source-model final
`h(u)` bound. -/
theorem higham9_14_tridiag_data_rowDiagDom_source_h_bound_from_LUFactSpec
    {n : ℕ}
    (T : higham9_18_TridiagData n)
    (L_hat U_hat : Fin n → Fin n → ℝ)
    (y_hat x_hat b : Fin n → ℝ)
    (u : ℝ) (hu : 0 ≤ u) (hu_lt_one : u < 1)
    (hLU : LUFactSpec n (higham9_18_tridiag_to_matrix T) L_hat U_hat)
    (hdetA :
      Matrix.det
        (Matrix.of (higham9_18_tridiag_to_matrix T) :
          Matrix (Fin n) (Fin n) ℝ) ≠ 0)
    (hRowDom : IsRowDiagDominant n (higham9_18_tridiag_to_matrix T))
    (DeltaA_LU DeltaL DeltaU : Fin n → Fin n → ℝ)
    (h20 : higham9_20_tridiag_lu_perturbation_model n
      (higham9_18_tridiag_to_matrix T) L_hat U_hat DeltaA_LU u)
    (h21 : higham9_21_tridiag_solve_perturbation_model n L_hat U_hat
      y_hat x_hat b DeltaL DeltaU u) :
    ∃ DeltaA : Fin n → Fin n → ℝ,
      (∀ i j, |DeltaA i j| ≤
        3 * higham9_14_h u * |higham9_18_tridiag_to_matrix T i j|) ∧
      (∀ i, ∑ j : Fin n,
        (higham9_18_tridiag_to_matrix T i j + DeltaA i j) * x_hat j =
          b i) :=
  higham9_14_tridiag_rowDiagDom_source_h_bound_from_LUFactSpec n
    (higham9_18_tridiag_to_matrix T) L_hat U_hat y_hat x_hat b u hu
    hu_lt_one hLU hdetA (higham9_18_tridiag_to_matrix_isTridiagonal T)
    hRowDom DeltaA_LU DeltaL DeltaU h20 h21

/-- **Theorem 9.14**, `TridiagData` column-dominant exact-LU source-model
`f(γ_n)` bound. -/
theorem higham9_14_tridiag_data_colDiagDom_source_f_bound_from_LUFactSpec_gamma
    (fp : FPModel) {n : ℕ}
    (T : higham9_18_TridiagData n)
    (L_hat U_hat : Fin n → Fin n → ℝ)
    (y_hat x_hat b : Fin n → ℝ)
    (hn : gammaValid fp n)
    (hLU : LUFactSpec n (higham9_18_tridiag_to_matrix T) L_hat U_hat)
    (hdetA :
      Matrix.det
        (Matrix.of (higham9_18_tridiag_to_matrix T) :
          Matrix (Fin n) (Fin n) ℝ) ≠ 0)
    (hColDom : IsDiagDominant n (higham9_18_tridiag_to_matrix T))
    (DeltaA_LU DeltaL DeltaU : Fin n → Fin n → ℝ)
    (h20 : higham9_20_tridiag_lu_perturbation_model n
      (higham9_18_tridiag_to_matrix T) L_hat U_hat DeltaA_LU (gamma fp n))
    (h21 : higham9_21_tridiag_solve_perturbation_model n L_hat U_hat
      y_hat x_hat b DeltaL DeltaU (gamma fp n)) :
    ∃ DeltaA : Fin n → Fin n → ℝ,
      (∀ i j, |DeltaA i j| ≤
        3 * higham9_14_f (gamma fp n) *
          |higham9_18_tridiag_to_matrix T i j|) ∧
      (∀ i, ∑ j : Fin n,
        (higham9_18_tridiag_to_matrix T i j + DeltaA i j) * x_hat j =
          b i) :=
  higham9_14_tridiag_data_colDiagDom_source_f_bound_from_LUFactSpec
    T L_hat U_hat y_hat x_hat b (gamma fp n) (gamma_nonneg fp hn)
    hLU hdetA hColDom
    DeltaA_LU DeltaL DeltaU h20 h21

/-- **Theorem 9.14**, `TridiagData` row-dominant exact-LU source-model
`f(γ_n)` bound. -/
theorem higham9_14_tridiag_data_rowDiagDom_source_f_bound_from_LUFactSpec_gamma
    (fp : FPModel) {n : ℕ}
    (T : higham9_18_TridiagData n)
    (L_hat U_hat : Fin n → Fin n → ℝ)
    (y_hat x_hat b : Fin n → ℝ)
    (hn : gammaValid fp n)
    (hLU : LUFactSpec n (higham9_18_tridiag_to_matrix T) L_hat U_hat)
    (hdetA :
      Matrix.det
        (Matrix.of (higham9_18_tridiag_to_matrix T) :
          Matrix (Fin n) (Fin n) ℝ) ≠ 0)
    (hRowDom : IsRowDiagDominant n (higham9_18_tridiag_to_matrix T))
    (DeltaA_LU DeltaL DeltaU : Fin n → Fin n → ℝ)
    (h20 : higham9_20_tridiag_lu_perturbation_model n
      (higham9_18_tridiag_to_matrix T) L_hat U_hat DeltaA_LU (gamma fp n))
    (h21 : higham9_21_tridiag_solve_perturbation_model n L_hat U_hat
      y_hat x_hat b DeltaL DeltaU (gamma fp n)) :
    ∃ DeltaA : Fin n → Fin n → ℝ,
      (∀ i j, |DeltaA i j| ≤
        3 * higham9_14_f (gamma fp n) *
          |higham9_18_tridiag_to_matrix T i j|) ∧
      (∀ i, ∑ j : Fin n,
        (higham9_18_tridiag_to_matrix T i j + DeltaA i j) * x_hat j =
          b i) :=
  higham9_14_tridiag_data_rowDiagDom_source_f_bound_from_LUFactSpec
    T L_hat U_hat y_hat x_hat b (gamma fp n) (gamma_nonneg fp hn)
    hLU hdetA hRowDom
    DeltaA_LU DeltaL DeltaU h20 h21

/-- **Theorem 9.14**, `TridiagData` column-dominant exact-LU source-model
final `h(γ_n)` bound. -/
theorem higham9_14_tridiag_data_colDiagDom_source_h_bound_from_LUFactSpec_gamma
    (fp : FPModel) {n : ℕ}
    (T : higham9_18_TridiagData n)
    (L_hat U_hat : Fin n → Fin n → ℝ)
    (y_hat x_hat b : Fin n → ℝ)
    (hn : gammaValid fp n) (hgamma_lt_one : gamma fp n < 1)
    (hLU : LUFactSpec n (higham9_18_tridiag_to_matrix T) L_hat U_hat)
    (hdetA :
      Matrix.det
        (Matrix.of (higham9_18_tridiag_to_matrix T) :
          Matrix (Fin n) (Fin n) ℝ) ≠ 0)
    (hColDom : IsDiagDominant n (higham9_18_tridiag_to_matrix T))
    (DeltaA_LU DeltaL DeltaU : Fin n → Fin n → ℝ)
    (h20 : higham9_20_tridiag_lu_perturbation_model n
      (higham9_18_tridiag_to_matrix T) L_hat U_hat DeltaA_LU (gamma fp n))
    (h21 : higham9_21_tridiag_solve_perturbation_model n L_hat U_hat
      y_hat x_hat b DeltaL DeltaU (gamma fp n)) :
    ∃ DeltaA : Fin n → Fin n → ℝ,
      (∀ i j, |DeltaA i j| ≤
        3 * higham9_14_h (gamma fp n) *
          |higham9_18_tridiag_to_matrix T i j|) ∧
      (∀ i, ∑ j : Fin n,
        (higham9_18_tridiag_to_matrix T i j + DeltaA i j) * x_hat j =
          b i) :=
  higham9_14_tridiag_data_colDiagDom_source_h_bound_from_LUFactSpec
    T L_hat U_hat y_hat x_hat b (gamma fp n) (gamma_nonneg fp hn)
    hgamma_lt_one hLU hdetA hColDom
    DeltaA_LU DeltaL DeltaU h20 h21

/-- **Theorem 9.14**, `TridiagData` row-dominant exact-LU source-model final
`h(γ_n)` bound. -/
theorem higham9_14_tridiag_data_rowDiagDom_source_h_bound_from_LUFactSpec_gamma
    (fp : FPModel) {n : ℕ}
    (T : higham9_18_TridiagData n)
    (L_hat U_hat : Fin n → Fin n → ℝ)
    (y_hat x_hat b : Fin n → ℝ)
    (hn : gammaValid fp n) (hgamma_lt_one : gamma fp n < 1)
    (hLU : LUFactSpec n (higham9_18_tridiag_to_matrix T) L_hat U_hat)
    (hdetA :
      Matrix.det
        (Matrix.of (higham9_18_tridiag_to_matrix T) :
          Matrix (Fin n) (Fin n) ℝ) ≠ 0)
    (hRowDom : IsRowDiagDominant n (higham9_18_tridiag_to_matrix T))
    (DeltaA_LU DeltaL DeltaU : Fin n → Fin n → ℝ)
    (h20 : higham9_20_tridiag_lu_perturbation_model n
      (higham9_18_tridiag_to_matrix T) L_hat U_hat DeltaA_LU (gamma fp n))
    (h21 : higham9_21_tridiag_solve_perturbation_model n L_hat U_hat
      y_hat x_hat b DeltaL DeltaU (gamma fp n)) :
    ∃ DeltaA : Fin n → Fin n → ℝ,
      (∀ i j, |DeltaA i j| ≤
        3 * higham9_14_h (gamma fp n) *
          |higham9_18_tridiag_to_matrix T i j|) ∧
      (∀ i, ∑ j : Fin n,
        (higham9_18_tridiag_to_matrix T i j + DeltaA i j) * x_hat j =
          b i) :=
  higham9_14_tridiag_data_rowDiagDom_source_h_bound_from_LUFactSpec
    T L_hat U_hat y_hat x_hat b (gamma fp n) (gamma_nonneg fp hn)
    hgamma_lt_one hLU hdetA hRowDom
    DeltaA_LU DeltaL DeltaU h20 h21

/-- **Theorem 9.14**, column-dominant exact-LU source-model `f(gamma_n)`
bound. -/
theorem higham9_14_tridiag_colDiagDom_source_f_bound_from_LUFactSpec_gamma
    (fp : FPModel) (n : ℕ)
    (A L_hat U_hat : Fin n → Fin n → ℝ)
    (y_hat x_hat b : Fin n → ℝ)
    (hn : gammaValid fp n)
    (hLU : LUFactSpec n A L_hat U_hat)
    (hdetA : Matrix.det (Matrix.of A : Matrix (Fin n) (Fin n) ℝ) ≠ 0)
    (hA_tridiag : IsTridiagonal n A)
    (hColDom : IsDiagDominant n A)
    (DeltaA_LU DeltaL DeltaU : Fin n → Fin n → ℝ)
    (h20 : higham9_20_tridiag_lu_perturbation_model n A L_hat U_hat
      DeltaA_LU (gamma fp n))
    (h21 : higham9_21_tridiag_solve_perturbation_model n L_hat U_hat
      y_hat x_hat b DeltaL DeltaU (gamma fp n)) :
    ∃ DeltaA : Fin n → Fin n → ℝ,
      (∀ i j, |DeltaA i j| ≤
        3 * higham9_14_f (gamma fp n) * |A i j|) ∧
      (∀ i, ∑ j : Fin n, (A i j + DeltaA i j) * x_hat j = b i) :=
  higham9_14_tridiag_colDiagDom_source_f_bound_from_LUFactSpec n
    A L_hat U_hat y_hat x_hat b (gamma fp n) (gamma_nonneg fp hn)
    hLU hdetA hA_tridiag hColDom DeltaA_LU DeltaL DeltaU h20 h21

/-- **Theorem 9.14**, row-dominant exact-LU source-model `f(gamma_n)` bound. -/
theorem higham9_14_tridiag_rowDiagDom_source_f_bound_from_LUFactSpec_gamma
    (fp : FPModel) (n : ℕ)
    (A L_hat U_hat : Fin n → Fin n → ℝ)
    (y_hat x_hat b : Fin n → ℝ)
    (hn : gammaValid fp n)
    (hLU : LUFactSpec n A L_hat U_hat)
    (hdetA : Matrix.det (Matrix.of A : Matrix (Fin n) (Fin n) ℝ) ≠ 0)
    (hA_tridiag : IsTridiagonal n A)
    (hRowDom : IsRowDiagDominant n A)
    (DeltaA_LU DeltaL DeltaU : Fin n → Fin n → ℝ)
    (h20 : higham9_20_tridiag_lu_perturbation_model n A L_hat U_hat
      DeltaA_LU (gamma fp n))
    (h21 : higham9_21_tridiag_solve_perturbation_model n L_hat U_hat
      y_hat x_hat b DeltaL DeltaU (gamma fp n)) :
    ∃ DeltaA : Fin n → Fin n → ℝ,
      (∀ i j, |DeltaA i j| ≤
        3 * higham9_14_f (gamma fp n) * |A i j|) ∧
      (∀ i, ∑ j : Fin n, (A i j + DeltaA i j) * x_hat j = b i) :=
  higham9_14_tridiag_rowDiagDom_source_f_bound_from_LUFactSpec n
    A L_hat U_hat y_hat x_hat b (gamma fp n) (gamma_nonneg fp hn)
    hLU hdetA hA_tridiag hRowDom DeltaA_LU DeltaL DeltaU h20 h21

/-- **Theorem 9.14**, column-dominant exact-LU source-model `h(gamma_n)`
bound. -/
theorem higham9_14_tridiag_colDiagDom_source_h_bound_from_LUFactSpec_gamma
    (fp : FPModel) (n : ℕ)
    (A L_hat U_hat : Fin n → Fin n → ℝ)
    (y_hat x_hat b : Fin n → ℝ)
    (hn : gammaValid fp n) (hgamma_lt_one : gamma fp n < 1)
    (hLU : LUFactSpec n A L_hat U_hat)
    (hdetA : Matrix.det (Matrix.of A : Matrix (Fin n) (Fin n) ℝ) ≠ 0)
    (hA_tridiag : IsTridiagonal n A)
    (hColDom : IsDiagDominant n A)
    (DeltaA_LU DeltaL DeltaU : Fin n → Fin n → ℝ)
    (h20 : higham9_20_tridiag_lu_perturbation_model n A L_hat U_hat
      DeltaA_LU (gamma fp n))
    (h21 : higham9_21_tridiag_solve_perturbation_model n L_hat U_hat
      y_hat x_hat b DeltaL DeltaU (gamma fp n)) :
    ∃ DeltaA : Fin n → Fin n → ℝ,
      (∀ i j, |DeltaA i j| ≤
        3 * higham9_14_h (gamma fp n) * |A i j|) ∧
      (∀ i, ∑ j : Fin n, (A i j + DeltaA i j) * x_hat j = b i) :=
  higham9_14_tridiag_colDiagDom_source_h_bound_from_LUFactSpec n
    A L_hat U_hat y_hat x_hat b (gamma fp n) (gamma_nonneg fp hn)
    hgamma_lt_one hLU hdetA hA_tridiag hColDom
    DeltaA_LU DeltaL DeltaU h20 h21

/-- **Theorem 9.14**, row-dominant exact-LU source-model `h(gamma_n)` bound. -/
theorem higham9_14_tridiag_rowDiagDom_source_h_bound_from_LUFactSpec_gamma
    (fp : FPModel) (n : ℕ)
    (A L_hat U_hat : Fin n → Fin n → ℝ)
    (y_hat x_hat b : Fin n → ℝ)
    (hn : gammaValid fp n) (hgamma_lt_one : gamma fp n < 1)
    (hLU : LUFactSpec n A L_hat U_hat)
    (hdetA : Matrix.det (Matrix.of A : Matrix (Fin n) (Fin n) ℝ) ≠ 0)
    (hA_tridiag : IsTridiagonal n A)
    (hRowDom : IsRowDiagDominant n A)
    (DeltaA_LU DeltaL DeltaU : Fin n → Fin n → ℝ)
    (h20 : higham9_20_tridiag_lu_perturbation_model n A L_hat U_hat
      DeltaA_LU (gamma fp n))
    (h21 : higham9_21_tridiag_solve_perturbation_model n L_hat U_hat
      y_hat x_hat b DeltaL DeltaU (gamma fp n)) :
    ∃ DeltaA : Fin n → Fin n → ℝ,
      (∀ i j, |DeltaA i j| ≤
        3 * higham9_14_h (gamma fp n) * |A i j|) ∧
      (∀ i, ∑ j : Fin n, (A i j + DeltaA i j) * x_hat j = b i) :=
  higham9_14_tridiag_rowDiagDom_source_h_bound_from_LUFactSpec n
    A L_hat U_hat y_hat x_hat b (gamma fp n) (gamma_nonneg fp hn)
    hgamma_lt_one hLU hdetA hA_tridiag hRowDom
    DeltaA_LU DeltaL DeltaU h20 h21

/-- **Theorem 9.14**, column-dominant exact-LU source-model production from
certificates and actual triangular solves.

This is the certificate-producing analogue of
`higham9_14_tridiag_colDiagDom_source_f_bound_from_LUFactSpec`: an existing
`LUBackwardError` certificate supplies equation (9.20), the actual
`fl_forwardSub`/`fl_backSub` calls supply equation (9.21), and the exact
`LUFactSpec` plus Theorem 9.13 supplies the structural `3|A|` comparison. -/
theorem higham9_14_tridiag_colDiagDom_source_f_bound_from_LUBackwardError_fl_triangular_solves
    (fp : FPModel) (n : ℕ)
    (A L_hat U_hat : Fin n → Fin n → ℝ)
    (b : Fin n → ℝ)
    (ε u : ℝ) (hu : 0 ≤ u)
    (hn : gammaValid fp n)
    (hBE : LUBackwardError n A L_hat U_hat ε)
    (hε_le_u : ε ≤ u)
    (hγ_le_u : gamma fp n ≤ u)
    (hLU : LUFactSpec n A L_hat U_hat)
    (hdetA : Matrix.det (Matrix.of A : Matrix (Fin n) (Fin n) ℝ) ≠ 0)
    (hA_tridiag : IsTridiagonal n A)
    (hColDom : IsDiagDominant n A) :
    let y_hat := fl_forwardSub fp n L_hat b
    let x_hat := fl_backSub fp n U_hat y_hat
    ∃ DeltaA : Fin n → Fin n → ℝ,
      (∀ i j, |DeltaA i j| ≤ 3 * higham9_14_f u * |A i j|) ∧
      (∀ i, ∑ j : Fin n, (A i j + DeltaA i j) * x_hat j = b i) :=
  higham9_14_source_f_bound_of_LUBackwardError_fl_triangular_solves_gamma_le
    fp n A L_hat U_hat b 3 ε u hu hn hBE hε_le_u hγ_le_u
    (hLU.det_ne_zero_iff_U_diag_ne_zero.mp hdetA)
    (higham9_13_colDiagDom_tridiag_growth_bound_3_of_LUFactSpec
      A L_hat U_hat hLU hdetA hA_tridiag hColDom)

/-- **Theorem 9.14**, row-dominant exact-LU source-model production from
certificates and actual triangular solves. -/
theorem higham9_14_tridiag_rowDiagDom_source_f_bound_from_LUBackwardError_fl_triangular_solves
    (fp : FPModel) (n : ℕ)
    (A L_hat U_hat : Fin n → Fin n → ℝ)
    (b : Fin n → ℝ)
    (ε u : ℝ) (hu : 0 ≤ u)
    (hn : gammaValid fp n)
    (hBE : LUBackwardError n A L_hat U_hat ε)
    (hε_le_u : ε ≤ u)
    (hγ_le_u : gamma fp n ≤ u)
    (hLU : LUFactSpec n A L_hat U_hat)
    (hdetA : Matrix.det (Matrix.of A : Matrix (Fin n) (Fin n) ℝ) ≠ 0)
    (hA_tridiag : IsTridiagonal n A)
    (hRowDom : IsRowDiagDominant n A) :
    let y_hat := fl_forwardSub fp n L_hat b
    let x_hat := fl_backSub fp n U_hat y_hat
    ∃ DeltaA : Fin n → Fin n → ℝ,
      (∀ i j, |DeltaA i j| ≤ 3 * higham9_14_f u * |A i j|) ∧
      (∀ i, ∑ j : Fin n, (A i j + DeltaA i j) * x_hat j = b i) :=
  higham9_14_source_f_bound_of_LUBackwardError_fl_triangular_solves_gamma_le
    fp n A L_hat U_hat b 3 ε u hu hn hBE hε_le_u hγ_le_u
    (hLU.det_ne_zero_iff_U_diag_ne_zero.mp hdetA)
    (higham9_13_rowDiagDom_tridiag_growth_bound_3_of_LUFactSpec
      A L_hat U_hat hLU hdetA hA_tridiag hRowDom)

/-- **Theorem 9.14**, column-dominant exact-LU source-model production from
certificates and actual triangular solves with final `h(u)` coefficient. -/
theorem higham9_14_tridiag_colDiagDom_source_h_bound_from_LUBackwardError_fl_triangular_solves
    (fp : FPModel) (n : ℕ)
    (A L_hat U_hat : Fin n → Fin n → ℝ)
    (b : Fin n → ℝ)
    (ε u : ℝ) (hu : 0 ≤ u) (hu_lt_one : u < 1)
    (hn : gammaValid fp n)
    (hBE : LUBackwardError n A L_hat U_hat ε)
    (hε_le_u : ε ≤ u)
    (hγ_le_u : gamma fp n ≤ u)
    (hLU : LUFactSpec n A L_hat U_hat)
    (hdetA : Matrix.det (Matrix.of A : Matrix (Fin n) (Fin n) ℝ) ≠ 0)
    (hA_tridiag : IsTridiagonal n A)
    (hColDom : IsDiagDominant n A) :
    let y_hat := fl_forwardSub fp n L_hat b
    let x_hat := fl_backSub fp n U_hat y_hat
    ∃ DeltaA : Fin n → Fin n → ℝ,
      (∀ i j, |DeltaA i j| ≤ 3 * higham9_14_h u * |A i j|) ∧
      (∀ i, ∑ j : Fin n, (A i j + DeltaA i j) * x_hat j = b i) :=
  higham9_14_source_h_bound_of_LUBackwardError_fl_triangular_solves_const_gamma_le
    fp n A L_hat U_hat b 3 ε u (by norm_num) hu hu_lt_one hn hBE hε_le_u
    hγ_le_u (hLU.det_ne_zero_iff_U_diag_ne_zero.mp hdetA)
    (higham9_13_colDiagDom_tridiag_growth_bound_3_of_LUFactSpec
      A L_hat U_hat hLU hdetA hA_tridiag hColDom)

/-- **Theorem 9.14**, row-dominant exact-LU source-model production from
certificates and actual triangular solves with final `h(u)` coefficient. -/
theorem higham9_14_tridiag_rowDiagDom_source_h_bound_from_LUBackwardError_fl_triangular_solves
    (fp : FPModel) (n : ℕ)
    (A L_hat U_hat : Fin n → Fin n → ℝ)
    (b : Fin n → ℝ)
    (ε u : ℝ) (hu : 0 ≤ u) (hu_lt_one : u < 1)
    (hn : gammaValid fp n)
    (hBE : LUBackwardError n A L_hat U_hat ε)
    (hε_le_u : ε ≤ u)
    (hγ_le_u : gamma fp n ≤ u)
    (hLU : LUFactSpec n A L_hat U_hat)
    (hdetA : Matrix.det (Matrix.of A : Matrix (Fin n) (Fin n) ℝ) ≠ 0)
    (hA_tridiag : IsTridiagonal n A)
    (hRowDom : IsRowDiagDominant n A) :
    let y_hat := fl_forwardSub fp n L_hat b
    let x_hat := fl_backSub fp n U_hat y_hat
    ∃ DeltaA : Fin n → Fin n → ℝ,
      (∀ i j, |DeltaA i j| ≤ 3 * higham9_14_h u * |A i j|) ∧
      (∀ i, ∑ j : Fin n, (A i j + DeltaA i j) * x_hat j = b i) :=
  higham9_14_source_h_bound_of_LUBackwardError_fl_triangular_solves_const_gamma_le
    fp n A L_hat U_hat b 3 ε u (by norm_num) hu hu_lt_one hn hBE hε_le_u
    hγ_le_u (hLU.det_ne_zero_iff_U_diag_ne_zero.mp hdetA)
    (higham9_13_rowDiagDom_tridiag_growth_bound_3_of_LUFactSpec
      A L_hat U_hat hLU hdetA hA_tridiag hRowDom)

/-- **Theorem 9.14**, column-dominant exact tridiagonal LU source-model
production from an `LUFactSpec` and actual triangular solves. -/
theorem higham9_14_tridiag_colDiagDom_source_f_bound_from_LUFactSpec_fl_triangular_solves
    (fp : FPModel) (n : ℕ)
    (A L_hat U_hat : Fin n → Fin n → ℝ)
    (b : Fin n → ℝ)
    (u : ℝ) (hu : 0 ≤ u)
    (hn : gammaValid fp n)
    (hγ_le_u : gamma fp n ≤ u)
    (hLU : LUFactSpec n A L_hat U_hat)
    (hdetA : Matrix.det (Matrix.of A : Matrix (Fin n) (Fin n) ℝ) ≠ 0)
    (hA_tridiag : IsTridiagonal n A)
    (hColDom : IsDiagDominant n A) :
    let y_hat := fl_forwardSub fp n L_hat b
    let x_hat := fl_backSub fp n U_hat y_hat
    ∃ DeltaA : Fin n → Fin n → ℝ,
      (∀ i j, |DeltaA i j| ≤ 3 * higham9_14_f u * |A i j|) ∧
      (∀ i, ∑ j : Fin n, (A i j + DeltaA i j) * x_hat j = b i) :=
  higham9_14_tridiag_colDiagDom_source_f_bound_from_LUBackwardError_fl_triangular_solves
    fp n A L_hat U_hat b 0 u hu hn (LUFactSpec.to_LUBackwardError_zero hLU)
    hu hγ_le_u hLU hdetA hA_tridiag hColDom

/-- **Theorem 9.14**, row-dominant exact tridiagonal LU source-model production
from an `LUFactSpec` and actual triangular solves. -/
theorem higham9_14_tridiag_rowDiagDom_source_f_bound_from_LUFactSpec_fl_triangular_solves
    (fp : FPModel) (n : ℕ)
    (A L_hat U_hat : Fin n → Fin n → ℝ)
    (b : Fin n → ℝ)
    (u : ℝ) (hu : 0 ≤ u)
    (hn : gammaValid fp n)
    (hγ_le_u : gamma fp n ≤ u)
    (hLU : LUFactSpec n A L_hat U_hat)
    (hdetA : Matrix.det (Matrix.of A : Matrix (Fin n) (Fin n) ℝ) ≠ 0)
    (hA_tridiag : IsTridiagonal n A)
    (hRowDom : IsRowDiagDominant n A) :
    let y_hat := fl_forwardSub fp n L_hat b
    let x_hat := fl_backSub fp n U_hat y_hat
    ∃ DeltaA : Fin n → Fin n → ℝ,
      (∀ i j, |DeltaA i j| ≤ 3 * higham9_14_f u * |A i j|) ∧
      (∀ i, ∑ j : Fin n, (A i j + DeltaA i j) * x_hat j = b i) :=
  higham9_14_tridiag_rowDiagDom_source_f_bound_from_LUBackwardError_fl_triangular_solves
    fp n A L_hat U_hat b 0 u hu hn (LUFactSpec.to_LUBackwardError_zero hLU)
    hu hγ_le_u hLU hdetA hA_tridiag hRowDom

/-- **Theorem 9.14**, column-dominant exact tridiagonal LU actual-solve source
model with final `h(u)` coefficient from an `LUFactSpec`. -/
theorem higham9_14_tridiag_colDiagDom_source_h_bound_from_LUFactSpec_fl_triangular_solves
    (fp : FPModel) (n : ℕ)
    (A L_hat U_hat : Fin n → Fin n → ℝ)
    (b : Fin n → ℝ)
    (u : ℝ) (hu : 0 ≤ u) (hu_lt_one : u < 1)
    (hn : gammaValid fp n)
    (hγ_le_u : gamma fp n ≤ u)
    (hLU : LUFactSpec n A L_hat U_hat)
    (hdetA : Matrix.det (Matrix.of A : Matrix (Fin n) (Fin n) ℝ) ≠ 0)
    (hA_tridiag : IsTridiagonal n A)
    (hColDom : IsDiagDominant n A) :
    let y_hat := fl_forwardSub fp n L_hat b
    let x_hat := fl_backSub fp n U_hat y_hat
    ∃ DeltaA : Fin n → Fin n → ℝ,
      (∀ i j, |DeltaA i j| ≤ 3 * higham9_14_h u * |A i j|) ∧
      (∀ i, ∑ j : Fin n, (A i j + DeltaA i j) * x_hat j = b i) :=
  higham9_14_tridiag_colDiagDom_source_h_bound_from_LUBackwardError_fl_triangular_solves
    fp n A L_hat U_hat b 0 u hu hu_lt_one hn
    (LUFactSpec.to_LUBackwardError_zero hLU) hu hγ_le_u hLU hdetA
    hA_tridiag hColDom

/-- **Theorem 9.14**, row-dominant exact tridiagonal LU actual-solve source
model with final `h(u)` coefficient from an `LUFactSpec`. -/
theorem higham9_14_tridiag_rowDiagDom_source_h_bound_from_LUFactSpec_fl_triangular_solves
    (fp : FPModel) (n : ℕ)
    (A L_hat U_hat : Fin n → Fin n → ℝ)
    (b : Fin n → ℝ)
    (u : ℝ) (hu : 0 ≤ u) (hu_lt_one : u < 1)
    (hn : gammaValid fp n)
    (hγ_le_u : gamma fp n ≤ u)
    (hLU : LUFactSpec n A L_hat U_hat)
    (hdetA : Matrix.det (Matrix.of A : Matrix (Fin n) (Fin n) ℝ) ≠ 0)
    (hA_tridiag : IsTridiagonal n A)
    (hRowDom : IsRowDiagDominant n A) :
    let y_hat := fl_forwardSub fp n L_hat b
    let x_hat := fl_backSub fp n U_hat y_hat
    ∃ DeltaA : Fin n → Fin n → ℝ,
      (∀ i j, |DeltaA i j| ≤ 3 * higham9_14_h u * |A i j|) ∧
      (∀ i, ∑ j : Fin n, (A i j + DeltaA i j) * x_hat j = b i) :=
  higham9_14_tridiag_rowDiagDom_source_h_bound_from_LUBackwardError_fl_triangular_solves
    fp n A L_hat U_hat b 0 u hu hu_lt_one hn
    (LUFactSpec.to_LUBackwardError_zero hLU) hu hγ_le_u hLU hdetA
    hA_tridiag hRowDom

/-- **Theorem 9.14**, `TridiagData` column-dominant exact-LU actual-solve
source model from an `LUBackwardError` certificate. -/
theorem higham9_14_tridiag_data_colDiagDom_source_f_bound_from_LUBackwardError_fl_triangular_solves
    (fp : FPModel) {n : ℕ}
    (T : higham9_18_TridiagData n)
    (L_hat U_hat : Fin n → Fin n → ℝ)
    (b : Fin n → ℝ)
    (ε u : ℝ) (hu : 0 ≤ u)
    (hn : gammaValid fp n)
    (hBE : LUBackwardError n (higham9_18_tridiag_to_matrix T) L_hat U_hat ε)
    (hε_le_u : ε ≤ u)
    (hγ_le_u : gamma fp n ≤ u)
    (hLU : LUFactSpec n (higham9_18_tridiag_to_matrix T) L_hat U_hat)
    (hdetA :
      Matrix.det
        (Matrix.of (higham9_18_tridiag_to_matrix T) :
          Matrix (Fin n) (Fin n) ℝ) ≠ 0)
    (hColDom : IsDiagDominant n (higham9_18_tridiag_to_matrix T)) :
    let y_hat := fl_forwardSub fp n L_hat b
    let x_hat := fl_backSub fp n U_hat y_hat
    ∃ DeltaA : Fin n → Fin n → ℝ,
      (∀ i j, |DeltaA i j| ≤
        3 * higham9_14_f u * |higham9_18_tridiag_to_matrix T i j|) ∧
      (∀ i, ∑ j : Fin n,
        (higham9_18_tridiag_to_matrix T i j + DeltaA i j) * x_hat j =
          b i) :=
  higham9_14_tridiag_colDiagDom_source_f_bound_from_LUBackwardError_fl_triangular_solves
    fp n (higham9_18_tridiag_to_matrix T) L_hat U_hat b ε u hu hn
    hBE hε_le_u hγ_le_u hLU hdetA
    (higham9_18_tridiag_to_matrix_isTridiagonal T) hColDom

/-- **Theorem 9.14**, `TridiagData` row-dominant exact-LU actual-solve source
model from an `LUBackwardError` certificate. -/
theorem higham9_14_tridiag_data_rowDiagDom_source_f_bound_from_LUBackwardError_fl_triangular_solves
    (fp : FPModel) {n : ℕ}
    (T : higham9_18_TridiagData n)
    (L_hat U_hat : Fin n → Fin n → ℝ)
    (b : Fin n → ℝ)
    (ε u : ℝ) (hu : 0 ≤ u)
    (hn : gammaValid fp n)
    (hBE : LUBackwardError n (higham9_18_tridiag_to_matrix T) L_hat U_hat ε)
    (hε_le_u : ε ≤ u)
    (hγ_le_u : gamma fp n ≤ u)
    (hLU : LUFactSpec n (higham9_18_tridiag_to_matrix T) L_hat U_hat)
    (hdetA :
      Matrix.det
        (Matrix.of (higham9_18_tridiag_to_matrix T) :
          Matrix (Fin n) (Fin n) ℝ) ≠ 0)
    (hRowDom : IsRowDiagDominant n (higham9_18_tridiag_to_matrix T)) :
    let y_hat := fl_forwardSub fp n L_hat b
    let x_hat := fl_backSub fp n U_hat y_hat
    ∃ DeltaA : Fin n → Fin n → ℝ,
      (∀ i j, |DeltaA i j| ≤
        3 * higham9_14_f u * |higham9_18_tridiag_to_matrix T i j|) ∧
      (∀ i, ∑ j : Fin n,
        (higham9_18_tridiag_to_matrix T i j + DeltaA i j) * x_hat j =
          b i) :=
  higham9_14_tridiag_rowDiagDom_source_f_bound_from_LUBackwardError_fl_triangular_solves
    fp n (higham9_18_tridiag_to_matrix T) L_hat U_hat b ε u hu hn
    hBE hε_le_u hγ_le_u hLU hdetA
    (higham9_18_tridiag_to_matrix_isTridiagonal T) hRowDom

/-- **Theorem 9.14**, `TridiagData` column-dominant exact-LU actual-solve
source model with final `h(u)` coefficient from an `LUBackwardError`
certificate. -/
theorem higham9_14_tridiag_data_colDiagDom_source_h_bound_from_LUBackwardError_fl_triangular_solves
    (fp : FPModel) {n : ℕ}
    (T : higham9_18_TridiagData n)
    (L_hat U_hat : Fin n → Fin n → ℝ)
    (b : Fin n → ℝ)
    (ε u : ℝ) (hu : 0 ≤ u) (hu_lt_one : u < 1)
    (hn : gammaValid fp n)
    (hBE : LUBackwardError n (higham9_18_tridiag_to_matrix T) L_hat U_hat ε)
    (hε_le_u : ε ≤ u)
    (hγ_le_u : gamma fp n ≤ u)
    (hLU : LUFactSpec n (higham9_18_tridiag_to_matrix T) L_hat U_hat)
    (hdetA :
      Matrix.det
        (Matrix.of (higham9_18_tridiag_to_matrix T) :
          Matrix (Fin n) (Fin n) ℝ) ≠ 0)
    (hColDom : IsDiagDominant n (higham9_18_tridiag_to_matrix T)) :
    let y_hat := fl_forwardSub fp n L_hat b
    let x_hat := fl_backSub fp n U_hat y_hat
    ∃ DeltaA : Fin n → Fin n → ℝ,
      (∀ i j, |DeltaA i j| ≤
        3 * higham9_14_h u * |higham9_18_tridiag_to_matrix T i j|) ∧
      (∀ i, ∑ j : Fin n,
        (higham9_18_tridiag_to_matrix T i j + DeltaA i j) * x_hat j =
          b i) :=
  higham9_14_tridiag_colDiagDom_source_h_bound_from_LUBackwardError_fl_triangular_solves
    fp n (higham9_18_tridiag_to_matrix T) L_hat U_hat b ε u hu
    hu_lt_one hn hBE hε_le_u hγ_le_u hLU hdetA
    (higham9_18_tridiag_to_matrix_isTridiagonal T) hColDom

/-- **Theorem 9.14**, `TridiagData` row-dominant exact-LU actual-solve source
model with final `h(u)` coefficient from an `LUBackwardError` certificate. -/
theorem higham9_14_tridiag_data_rowDiagDom_source_h_bound_from_LUBackwardError_fl_triangular_solves
    (fp : FPModel) {n : ℕ}
    (T : higham9_18_TridiagData n)
    (L_hat U_hat : Fin n → Fin n → ℝ)
    (b : Fin n → ℝ)
    (ε u : ℝ) (hu : 0 ≤ u) (hu_lt_one : u < 1)
    (hn : gammaValid fp n)
    (hBE : LUBackwardError n (higham9_18_tridiag_to_matrix T) L_hat U_hat ε)
    (hε_le_u : ε ≤ u)
    (hγ_le_u : gamma fp n ≤ u)
    (hLU : LUFactSpec n (higham9_18_tridiag_to_matrix T) L_hat U_hat)
    (hdetA :
      Matrix.det
        (Matrix.of (higham9_18_tridiag_to_matrix T) :
          Matrix (Fin n) (Fin n) ℝ) ≠ 0)
    (hRowDom : IsRowDiagDominant n (higham9_18_tridiag_to_matrix T)) :
    let y_hat := fl_forwardSub fp n L_hat b
    let x_hat := fl_backSub fp n U_hat y_hat
    ∃ DeltaA : Fin n → Fin n → ℝ,
      (∀ i j, |DeltaA i j| ≤
        3 * higham9_14_h u * |higham9_18_tridiag_to_matrix T i j|) ∧
      (∀ i, ∑ j : Fin n,
        (higham9_18_tridiag_to_matrix T i j + DeltaA i j) * x_hat j =
          b i) :=
  higham9_14_tridiag_rowDiagDom_source_h_bound_from_LUBackwardError_fl_triangular_solves
    fp n (higham9_18_tridiag_to_matrix T) L_hat U_hat b ε u hu
    hu_lt_one hn hBE hε_le_u hγ_le_u hLU hdetA
    (higham9_18_tridiag_to_matrix_isTridiagonal T) hRowDom

/-- **Theorem 9.14**, `TridiagData` column-dominant exact-LU actual-solve
source model at the natural `γ_n` coefficient from an `LUBackwardError`
certificate. -/
theorem higham9_14_tridiag_data_colDiagDom_source_f_bound_from_LUBackwardError_fl_triangular_solves_gamma
    (fp : FPModel) {n : ℕ}
    (T : higham9_18_TridiagData n)
    (L_hat U_hat : Fin n → Fin n → ℝ)
    (b : Fin n → ℝ)
    (ε : ℝ)
    (hn : gammaValid fp n)
    (hBE : LUBackwardError n (higham9_18_tridiag_to_matrix T) L_hat U_hat ε)
    (hε_le_gamma : ε ≤ gamma fp n)
    (hLU : LUFactSpec n (higham9_18_tridiag_to_matrix T) L_hat U_hat)
    (hdetA :
      Matrix.det
        (Matrix.of (higham9_18_tridiag_to_matrix T) :
          Matrix (Fin n) (Fin n) ℝ) ≠ 0)
    (hColDom : IsDiagDominant n (higham9_18_tridiag_to_matrix T)) :
    let y_hat := fl_forwardSub fp n L_hat b
    let x_hat := fl_backSub fp n U_hat y_hat
    ∃ DeltaA : Fin n → Fin n → ℝ,
      (∀ i j, |DeltaA i j| ≤
        3 * higham9_14_f (gamma fp n) *
          |higham9_18_tridiag_to_matrix T i j|) ∧
      (∀ i, ∑ j : Fin n,
        (higham9_18_tridiag_to_matrix T i j + DeltaA i j) * x_hat j =
          b i) :=
  higham9_14_tridiag_data_colDiagDom_source_f_bound_from_LUBackwardError_fl_triangular_solves
    fp T L_hat U_hat b ε (gamma fp n) (gamma_nonneg fp hn) hn hBE
    hε_le_gamma le_rfl hLU hdetA hColDom

/-- **Theorem 9.14**, `TridiagData` row-dominant exact-LU actual-solve source
model at the natural `γ_n` coefficient from an `LUBackwardError` certificate. -/
theorem higham9_14_tridiag_data_rowDiagDom_source_f_bound_from_LUBackwardError_fl_triangular_solves_gamma
    (fp : FPModel) {n : ℕ}
    (T : higham9_18_TridiagData n)
    (L_hat U_hat : Fin n → Fin n → ℝ)
    (b : Fin n → ℝ)
    (ε : ℝ)
    (hn : gammaValid fp n)
    (hBE : LUBackwardError n (higham9_18_tridiag_to_matrix T) L_hat U_hat ε)
    (hε_le_gamma : ε ≤ gamma fp n)
    (hLU : LUFactSpec n (higham9_18_tridiag_to_matrix T) L_hat U_hat)
    (hdetA :
      Matrix.det
        (Matrix.of (higham9_18_tridiag_to_matrix T) :
          Matrix (Fin n) (Fin n) ℝ) ≠ 0)
    (hRowDom : IsRowDiagDominant n (higham9_18_tridiag_to_matrix T)) :
    let y_hat := fl_forwardSub fp n L_hat b
    let x_hat := fl_backSub fp n U_hat y_hat
    ∃ DeltaA : Fin n → Fin n → ℝ,
      (∀ i j, |DeltaA i j| ≤
        3 * higham9_14_f (gamma fp n) *
          |higham9_18_tridiag_to_matrix T i j|) ∧
      (∀ i, ∑ j : Fin n,
        (higham9_18_tridiag_to_matrix T i j + DeltaA i j) * x_hat j =
          b i) :=
  higham9_14_tridiag_data_rowDiagDom_source_f_bound_from_LUBackwardError_fl_triangular_solves
    fp T L_hat U_hat b ε (gamma fp n) (gamma_nonneg fp hn) hn hBE
    hε_le_gamma le_rfl hLU hdetA hRowDom

/-- **Theorem 9.14**, `TridiagData` column-dominant exact-LU actual-solve
final `h(γ_n)` source model from an `LUBackwardError` certificate. -/
theorem higham9_14_tridiag_data_colDiagDom_source_h_bound_from_LUBackwardError_fl_triangular_solves_gamma
    (fp : FPModel) {n : ℕ}
    (T : higham9_18_TridiagData n)
    (L_hat U_hat : Fin n → Fin n → ℝ)
    (b : Fin n → ℝ)
    (ε : ℝ)
    (hn : gammaValid fp n)
    (hγ_lt_one : gamma fp n < 1)
    (hBE : LUBackwardError n (higham9_18_tridiag_to_matrix T) L_hat U_hat ε)
    (hε_le_gamma : ε ≤ gamma fp n)
    (hLU : LUFactSpec n (higham9_18_tridiag_to_matrix T) L_hat U_hat)
    (hdetA :
      Matrix.det
        (Matrix.of (higham9_18_tridiag_to_matrix T) :
          Matrix (Fin n) (Fin n) ℝ) ≠ 0)
    (hColDom : IsDiagDominant n (higham9_18_tridiag_to_matrix T)) :
    let y_hat := fl_forwardSub fp n L_hat b
    let x_hat := fl_backSub fp n U_hat y_hat
    ∃ DeltaA : Fin n → Fin n → ℝ,
      (∀ i j, |DeltaA i j| ≤
        3 * higham9_14_h (gamma fp n) *
          |higham9_18_tridiag_to_matrix T i j|) ∧
      (∀ i, ∑ j : Fin n,
        (higham9_18_tridiag_to_matrix T i j + DeltaA i j) * x_hat j =
          b i) :=
  higham9_14_tridiag_data_colDiagDom_source_h_bound_from_LUBackwardError_fl_triangular_solves
    fp T L_hat U_hat b ε (gamma fp n) (gamma_nonneg fp hn) hγ_lt_one
    hn hBE hε_le_gamma le_rfl hLU hdetA hColDom

/-- **Theorem 9.14**, `TridiagData` row-dominant exact-LU actual-solve final
`h(γ_n)` source model from an `LUBackwardError` certificate. -/
theorem higham9_14_tridiag_data_rowDiagDom_source_h_bound_from_LUBackwardError_fl_triangular_solves_gamma
    (fp : FPModel) {n : ℕ}
    (T : higham9_18_TridiagData n)
    (L_hat U_hat : Fin n → Fin n → ℝ)
    (b : Fin n → ℝ)
    (ε : ℝ)
    (hn : gammaValid fp n)
    (hγ_lt_one : gamma fp n < 1)
    (hBE : LUBackwardError n (higham9_18_tridiag_to_matrix T) L_hat U_hat ε)
    (hε_le_gamma : ε ≤ gamma fp n)
    (hLU : LUFactSpec n (higham9_18_tridiag_to_matrix T) L_hat U_hat)
    (hdetA :
      Matrix.det
        (Matrix.of (higham9_18_tridiag_to_matrix T) :
          Matrix (Fin n) (Fin n) ℝ) ≠ 0)
    (hRowDom : IsRowDiagDominant n (higham9_18_tridiag_to_matrix T)) :
    let y_hat := fl_forwardSub fp n L_hat b
    let x_hat := fl_backSub fp n U_hat y_hat
    ∃ DeltaA : Fin n → Fin n → ℝ,
      (∀ i j, |DeltaA i j| ≤
        3 * higham9_14_h (gamma fp n) *
          |higham9_18_tridiag_to_matrix T i j|) ∧
      (∀ i, ∑ j : Fin n,
        (higham9_18_tridiag_to_matrix T i j + DeltaA i j) * x_hat j =
          b i) :=
  higham9_14_tridiag_data_rowDiagDom_source_h_bound_from_LUBackwardError_fl_triangular_solves
    fp T L_hat U_hat b ε (gamma fp n) (gamma_nonneg fp hn) hγ_lt_one
    hn hBE hε_le_gamma le_rfl hLU hdetA hRowDom

/-- **Theorem 9.14**, `TridiagData` column-dominant exact-LU actual-solve
source model from an `LUFactSpec`. -/
theorem higham9_14_tridiag_data_colDiagDom_source_f_bound_from_LUFactSpec_fl_triangular_solves
    (fp : FPModel) {n : ℕ}
    (T : higham9_18_TridiagData n)
    (L_hat U_hat : Fin n → Fin n → ℝ)
    (b : Fin n → ℝ)
    (u : ℝ) (hu : 0 ≤ u)
    (hn : gammaValid fp n)
    (hγ_le_u : gamma fp n ≤ u)
    (hLU : LUFactSpec n (higham9_18_tridiag_to_matrix T) L_hat U_hat)
    (hdetA :
      Matrix.det
        (Matrix.of (higham9_18_tridiag_to_matrix T) :
          Matrix (Fin n) (Fin n) ℝ) ≠ 0)
    (hColDom : IsDiagDominant n (higham9_18_tridiag_to_matrix T)) :
    let y_hat := fl_forwardSub fp n L_hat b
    let x_hat := fl_backSub fp n U_hat y_hat
    ∃ DeltaA : Fin n → Fin n → ℝ,
      (∀ i j, |DeltaA i j| ≤
        3 * higham9_14_f u * |higham9_18_tridiag_to_matrix T i j|) ∧
      (∀ i, ∑ j : Fin n,
        (higham9_18_tridiag_to_matrix T i j + DeltaA i j) * x_hat j =
          b i) :=
  higham9_14_tridiag_data_colDiagDom_source_f_bound_from_LUBackwardError_fl_triangular_solves
    fp T L_hat U_hat b 0 u hu hn (LUFactSpec.to_LUBackwardError_zero hLU)
    hu hγ_le_u hLU hdetA hColDom

/-- **Theorem 9.14**, `TridiagData` row-dominant exact-LU actual-solve source
model from an `LUFactSpec`. -/
theorem higham9_14_tridiag_data_rowDiagDom_source_f_bound_from_LUFactSpec_fl_triangular_solves
    (fp : FPModel) {n : ℕ}
    (T : higham9_18_TridiagData n)
    (L_hat U_hat : Fin n → Fin n → ℝ)
    (b : Fin n → ℝ)
    (u : ℝ) (hu : 0 ≤ u)
    (hn : gammaValid fp n)
    (hγ_le_u : gamma fp n ≤ u)
    (hLU : LUFactSpec n (higham9_18_tridiag_to_matrix T) L_hat U_hat)
    (hdetA :
      Matrix.det
        (Matrix.of (higham9_18_tridiag_to_matrix T) :
          Matrix (Fin n) (Fin n) ℝ) ≠ 0)
    (hRowDom : IsRowDiagDominant n (higham9_18_tridiag_to_matrix T)) :
    let y_hat := fl_forwardSub fp n L_hat b
    let x_hat := fl_backSub fp n U_hat y_hat
    ∃ DeltaA : Fin n → Fin n → ℝ,
      (∀ i j, |DeltaA i j| ≤
        3 * higham9_14_f u * |higham9_18_tridiag_to_matrix T i j|) ∧
      (∀ i, ∑ j : Fin n,
        (higham9_18_tridiag_to_matrix T i j + DeltaA i j) * x_hat j =
          b i) :=
  higham9_14_tridiag_data_rowDiagDom_source_f_bound_from_LUBackwardError_fl_triangular_solves
    fp T L_hat U_hat b 0 u hu hn (LUFactSpec.to_LUBackwardError_zero hLU)
    hu hγ_le_u hLU hdetA hRowDom

/-- **Theorem 9.14**, `TridiagData` column-dominant exact-LU actual-solve
final source model from an `LUFactSpec`. -/
theorem higham9_14_tridiag_data_colDiagDom_source_h_bound_from_LUFactSpec_fl_triangular_solves
    (fp : FPModel) {n : ℕ}
    (T : higham9_18_TridiagData n)
    (L_hat U_hat : Fin n → Fin n → ℝ)
    (b : Fin n → ℝ)
    (u : ℝ) (hu : 0 ≤ u) (hu_lt_one : u < 1)
    (hn : gammaValid fp n)
    (hγ_le_u : gamma fp n ≤ u)
    (hLU : LUFactSpec n (higham9_18_tridiag_to_matrix T) L_hat U_hat)
    (hdetA :
      Matrix.det
        (Matrix.of (higham9_18_tridiag_to_matrix T) :
          Matrix (Fin n) (Fin n) ℝ) ≠ 0)
    (hColDom : IsDiagDominant n (higham9_18_tridiag_to_matrix T)) :
    let y_hat := fl_forwardSub fp n L_hat b
    let x_hat := fl_backSub fp n U_hat y_hat
    ∃ DeltaA : Fin n → Fin n → ℝ,
      (∀ i j, |DeltaA i j| ≤
        3 * higham9_14_h u * |higham9_18_tridiag_to_matrix T i j|) ∧
      (∀ i, ∑ j : Fin n,
        (higham9_18_tridiag_to_matrix T i j + DeltaA i j) * x_hat j =
          b i) :=
  higham9_14_tridiag_data_colDiagDom_source_h_bound_from_LUBackwardError_fl_triangular_solves
    fp T L_hat U_hat b 0 u hu hu_lt_one hn
    (LUFactSpec.to_LUBackwardError_zero hLU) hu hγ_le_u hLU hdetA hColDom

/-- **Theorem 9.14**, `TridiagData` row-dominant exact-LU actual-solve final
source model from an `LUFactSpec`. -/
theorem higham9_14_tridiag_data_rowDiagDom_source_h_bound_from_LUFactSpec_fl_triangular_solves
    (fp : FPModel) {n : ℕ}
    (T : higham9_18_TridiagData n)
    (L_hat U_hat : Fin n → Fin n → ℝ)
    (b : Fin n → ℝ)
    (u : ℝ) (hu : 0 ≤ u) (hu_lt_one : u < 1)
    (hn : gammaValid fp n)
    (hγ_le_u : gamma fp n ≤ u)
    (hLU : LUFactSpec n (higham9_18_tridiag_to_matrix T) L_hat U_hat)
    (hdetA :
      Matrix.det
        (Matrix.of (higham9_18_tridiag_to_matrix T) :
          Matrix (Fin n) (Fin n) ℝ) ≠ 0)
    (hRowDom : IsRowDiagDominant n (higham9_18_tridiag_to_matrix T)) :
    let y_hat := fl_forwardSub fp n L_hat b
    let x_hat := fl_backSub fp n U_hat y_hat
    ∃ DeltaA : Fin n → Fin n → ℝ,
      (∀ i j, |DeltaA i j| ≤
        3 * higham9_14_h u * |higham9_18_tridiag_to_matrix T i j|) ∧
      (∀ i, ∑ j : Fin n,
        (higham9_18_tridiag_to_matrix T i j + DeltaA i j) * x_hat j =
          b i) :=
  higham9_14_tridiag_data_rowDiagDom_source_h_bound_from_LUBackwardError_fl_triangular_solves
    fp T L_hat U_hat b 0 u hu hu_lt_one hn
    (LUFactSpec.to_LUBackwardError_zero hLU) hu hγ_le_u hLU hdetA hRowDom

/-- **Theorem 9.14**, column-dominant builder actual-solve source model at
the natural `γ_n` coefficient. -/
theorem higham9_14_tridiag_colDiagDom_source_f_bound_from_builders_LUBackwardError_fl_triangular_solves_gamma
    (fp : FPModel) (n : ℕ)
    (T : higham9_18_TridiagData n)
    (l_hat u_hat : Fin n → ℝ)
    (b : Fin n → ℝ)
    (ε : ℝ)
    (hn : gammaValid fp n)
    (hBE : LUBackwardError n (higham9_18_tridiag_to_matrix T)
      (tridiag_L_matrix l_hat) (tridiag_U_matrix u_hat T.c) ε)
    (hε_le_gamma : ε ≤ gamma fp n)
    (hU_diag : ∀ i : Fin n, tridiag_U_matrix u_hat T.c i i ≠ 0)
    (hLU_exact : ∀ i j : Fin n,
      ∑ k : Fin n, tridiag_L_matrix l_hat i k *
        tridiag_U_matrix u_hat T.c k j =
        higham9_18_tridiag_to_matrix T i j)
    (hl : ∀ i : Fin n, |l_hat i| ≤ 1)
    (hColDom : IsDiagDominant n (higham9_18_tridiag_to_matrix T)) :
    let y_hat := fl_forwardSub fp n (tridiag_L_matrix l_hat) b
    let x_hat := fl_backSub fp n (tridiag_U_matrix u_hat T.c) y_hat
    ∃ DeltaA : Fin n → Fin n → ℝ,
      (∀ i j, |DeltaA i j| ≤
        3 * higham9_14_f (gamma fp n) *
          |higham9_18_tridiag_to_matrix T i j|) ∧
      (∀ i, ∑ j : Fin n,
        (higham9_18_tridiag_to_matrix T i j + DeltaA i j) * x_hat j =
          b i) :=
  higham9_14_tridiag_colDiagDom_source_f_bound_from_builders_LUBackwardError_fl_triangular_solves
    fp n T l_hat u_hat b ε (gamma fp n) (gamma_nonneg fp hn) hn hBE
    hε_le_gamma le_rfl hU_diag hLU_exact hl hColDom

/-- **Theorem 9.14**, row-dominant builder actual-solve source model at the
natural `γ_n` coefficient. -/
theorem higham9_14_tridiag_rowDiagDom_source_f_bound_from_builders_LUBackwardError_fl_triangular_solves_gamma
    (fp : FPModel) (n : ℕ)
    (T : higham9_18_TridiagData n)
    (l_hat u_hat : Fin n → ℝ)
    (b : Fin n → ℝ)
    (ε : ℝ)
    (hn : gammaValid fp n)
    (hBE : LUBackwardError n (higham9_18_tridiag_to_matrix T)
      (tridiag_L_matrix l_hat) (tridiag_U_matrix u_hat T.c) ε)
    (hε_le_gamma : ε ≤ gamma fp n)
    (hU_diag : ∀ i : Fin n, tridiag_U_matrix u_hat T.c i i ≠ 0)
    (hLU_exact : ∀ i j : Fin n,
      ∑ k : Fin n, tridiag_L_matrix l_hat i k *
        tridiag_U_matrix u_hat T.c k j =
        higham9_18_tridiag_to_matrix T i j)
    (hRowDom : IsRowDiagDominant n (higham9_18_tridiag_to_matrix T)) :
    let y_hat := fl_forwardSub fp n (tridiag_L_matrix l_hat) b
    let x_hat := fl_backSub fp n (tridiag_U_matrix u_hat T.c) y_hat
    ∃ DeltaA : Fin n → Fin n → ℝ,
      (∀ i j, |DeltaA i j| ≤
        3 * higham9_14_f (gamma fp n) *
          |higham9_18_tridiag_to_matrix T i j|) ∧
      (∀ i, ∑ j : Fin n,
        (higham9_18_tridiag_to_matrix T i j + DeltaA i j) * x_hat j =
          b i) :=
  higham9_14_tridiag_rowDiagDom_source_f_bound_from_builders_LUBackwardError_fl_triangular_solves
    fp n T l_hat u_hat b ε (gamma fp n) (gamma_nonneg fp hn) hn hBE
    hε_le_gamma le_rfl hU_diag hLU_exact hRowDom

/-- **Theorem 9.14**, column-dominant recurrence actual-solve source model at
the natural `γ_n` coefficient. -/
theorem higham9_14_tridiag_colDiagDom_source_f_bound_from_recurrence_LUBackwardError_fl_triangular_solves_gamma
    (fp : FPModel) (n : ℕ)
    (T : higham9_18_TridiagData n)
    (l_hat u_hat : Fin n → ℝ)
    (b : Fin n → ℝ)
    (ε : ℝ)
    (hn : gammaValid fp n)
    (hBE : LUBackwardError n (higham9_18_tridiag_to_matrix T)
      (tridiag_L_matrix l_hat) (tridiag_U_matrix u_hat T.c) ε)
    (hε_le_gamma : ε ≤ gamma fp n)
    (hU_diag : ∀ i : Fin n, tridiag_U_matrix u_hat T.c i i ≠ 0)
    (hrec : higham9_19_TridiagExactLURecurrence T l_hat u_hat)
    (hl : ∀ i : Fin n, |l_hat i| ≤ 1)
    (hColDom : IsDiagDominant n (higham9_18_tridiag_to_matrix T)) :
    let y_hat := fl_forwardSub fp n (tridiag_L_matrix l_hat) b
    let x_hat := fl_backSub fp n (tridiag_U_matrix u_hat T.c) y_hat
    ∃ DeltaA : Fin n → Fin n → ℝ,
      (∀ i j, |DeltaA i j| ≤
        3 * higham9_14_f (gamma fp n) *
          |higham9_18_tridiag_to_matrix T i j|) ∧
      (∀ i, ∑ j : Fin n,
        (higham9_18_tridiag_to_matrix T i j + DeltaA i j) * x_hat j =
          b i) :=
  higham9_14_tridiag_colDiagDom_source_f_bound_from_recurrence_LUBackwardError_fl_triangular_solves
    fp n T l_hat u_hat b ε (gamma fp n) (gamma_nonneg fp hn) hn hBE
    hε_le_gamma le_rfl hU_diag hrec hl hColDom

/-- **Theorem 9.14**, row-dominant recurrence actual-solve source model at the
natural `γ_n` coefficient. -/
theorem higham9_14_tridiag_rowDiagDom_source_f_bound_from_recurrence_LUBackwardError_fl_triangular_solves_gamma
    (fp : FPModel) (n : ℕ)
    (T : higham9_18_TridiagData n)
    (l_hat u_hat : Fin n → ℝ)
    (b : Fin n → ℝ)
    (ε : ℝ)
    (hn : gammaValid fp n)
    (hBE : LUBackwardError n (higham9_18_tridiag_to_matrix T)
      (tridiag_L_matrix l_hat) (tridiag_U_matrix u_hat T.c) ε)
    (hε_le_gamma : ε ≤ gamma fp n)
    (hU_diag : ∀ i : Fin n, tridiag_U_matrix u_hat T.c i i ≠ 0)
    (hrec : higham9_19_TridiagExactLURecurrence T l_hat u_hat)
    (hRowDom : IsRowDiagDominant n (higham9_18_tridiag_to_matrix T)) :
    let y_hat := fl_forwardSub fp n (tridiag_L_matrix l_hat) b
    let x_hat := fl_backSub fp n (tridiag_U_matrix u_hat T.c) y_hat
    ∃ DeltaA : Fin n → Fin n → ℝ,
      (∀ i j, |DeltaA i j| ≤
        3 * higham9_14_f (gamma fp n) *
          |higham9_18_tridiag_to_matrix T i j|) ∧
      (∀ i, ∑ j : Fin n,
        (higham9_18_tridiag_to_matrix T i j + DeltaA i j) * x_hat j =
          b i) :=
  higham9_14_tridiag_rowDiagDom_source_f_bound_from_recurrence_LUBackwardError_fl_triangular_solves
    fp n T l_hat u_hat b ε (gamma fp n) (gamma_nonneg fp hn) hn hBE
    hε_le_gamma le_rfl hU_diag hrec hRowDom

/-- **Theorem 9.14**, column-dominant builder actual-solve final `h(γ_n)`
bound. -/
theorem higham9_14_tridiag_colDiagDom_source_h_bound_from_builders_LUBackwardError_fl_triangular_solves_gamma
    (fp : FPModel) (n : ℕ)
    (T : higham9_18_TridiagData n)
    (l_hat u_hat : Fin n → ℝ)
    (b : Fin n → ℝ)
    (ε : ℝ)
    (hn : gammaValid fp n)
    (hγ_lt_one : gamma fp n < 1)
    (hBE : LUBackwardError n (higham9_18_tridiag_to_matrix T)
      (tridiag_L_matrix l_hat) (tridiag_U_matrix u_hat T.c) ε)
    (hε_le_gamma : ε ≤ gamma fp n)
    (hU_diag : ∀ i : Fin n, tridiag_U_matrix u_hat T.c i i ≠ 0)
    (hLU_exact : ∀ i j : Fin n,
      ∑ k : Fin n, tridiag_L_matrix l_hat i k *
        tridiag_U_matrix u_hat T.c k j =
        higham9_18_tridiag_to_matrix T i j)
    (hl : ∀ i : Fin n, |l_hat i| ≤ 1)
    (hColDom : IsDiagDominant n (higham9_18_tridiag_to_matrix T)) :
    let y_hat := fl_forwardSub fp n (tridiag_L_matrix l_hat) b
    let x_hat := fl_backSub fp n (tridiag_U_matrix u_hat T.c) y_hat
    ∃ DeltaA : Fin n → Fin n → ℝ,
      (∀ i j, |DeltaA i j| ≤
        3 * higham9_14_h (gamma fp n) *
          |higham9_18_tridiag_to_matrix T i j|) ∧
      (∀ i, ∑ j : Fin n,
        (higham9_18_tridiag_to_matrix T i j + DeltaA i j) * x_hat j =
          b i) :=
  higham9_14_tridiag_colDiagDom_source_h_bound_from_builders_LUBackwardError_fl_triangular_solves
    fp n T l_hat u_hat b ε (gamma fp n) (gamma_nonneg fp hn) hγ_lt_one
    hn hBE hε_le_gamma le_rfl hU_diag hLU_exact hl hColDom

/-- **Theorem 9.14**, row-dominant builder actual-solve final `h(γ_n)` bound. -/
theorem higham9_14_tridiag_rowDiagDom_source_h_bound_from_builders_LUBackwardError_fl_triangular_solves_gamma
    (fp : FPModel) (n : ℕ)
    (T : higham9_18_TridiagData n)
    (l_hat u_hat : Fin n → ℝ)
    (b : Fin n → ℝ)
    (ε : ℝ)
    (hn : gammaValid fp n)
    (hγ_lt_one : gamma fp n < 1)
    (hBE : LUBackwardError n (higham9_18_tridiag_to_matrix T)
      (tridiag_L_matrix l_hat) (tridiag_U_matrix u_hat T.c) ε)
    (hε_le_gamma : ε ≤ gamma fp n)
    (hU_diag : ∀ i : Fin n, tridiag_U_matrix u_hat T.c i i ≠ 0)
    (hLU_exact : ∀ i j : Fin n,
      ∑ k : Fin n, tridiag_L_matrix l_hat i k *
        tridiag_U_matrix u_hat T.c k j =
        higham9_18_tridiag_to_matrix T i j)
    (hRowDom : IsRowDiagDominant n (higham9_18_tridiag_to_matrix T)) :
    let y_hat := fl_forwardSub fp n (tridiag_L_matrix l_hat) b
    let x_hat := fl_backSub fp n (tridiag_U_matrix u_hat T.c) y_hat
    ∃ DeltaA : Fin n → Fin n → ℝ,
      (∀ i j, |DeltaA i j| ≤
        3 * higham9_14_h (gamma fp n) *
          |higham9_18_tridiag_to_matrix T i j|) ∧
      (∀ i, ∑ j : Fin n,
        (higham9_18_tridiag_to_matrix T i j + DeltaA i j) * x_hat j =
          b i) :=
  higham9_14_tridiag_rowDiagDom_source_h_bound_from_builders_LUBackwardError_fl_triangular_solves
    fp n T l_hat u_hat b ε (gamma fp n) (gamma_nonneg fp hn) hγ_lt_one
    hn hBE hε_le_gamma le_rfl hU_diag hLU_exact hRowDom

/-- **Theorem 9.14**, column-dominant recurrence actual-solve final `h(γ_n)`
bound. -/
theorem higham9_14_tridiag_colDiagDom_source_h_bound_from_recurrence_LUBackwardError_fl_triangular_solves_gamma
    (fp : FPModel) (n : ℕ)
    (T : higham9_18_TridiagData n)
    (l_hat u_hat : Fin n → ℝ)
    (b : Fin n → ℝ)
    (ε : ℝ)
    (hn : gammaValid fp n)
    (hγ_lt_one : gamma fp n < 1)
    (hBE : LUBackwardError n (higham9_18_tridiag_to_matrix T)
      (tridiag_L_matrix l_hat) (tridiag_U_matrix u_hat T.c) ε)
    (hε_le_gamma : ε ≤ gamma fp n)
    (hU_diag : ∀ i : Fin n, tridiag_U_matrix u_hat T.c i i ≠ 0)
    (hrec : higham9_19_TridiagExactLURecurrence T l_hat u_hat)
    (hl : ∀ i : Fin n, |l_hat i| ≤ 1)
    (hColDom : IsDiagDominant n (higham9_18_tridiag_to_matrix T)) :
    let y_hat := fl_forwardSub fp n (tridiag_L_matrix l_hat) b
    let x_hat := fl_backSub fp n (tridiag_U_matrix u_hat T.c) y_hat
    ∃ DeltaA : Fin n → Fin n → ℝ,
      (∀ i j, |DeltaA i j| ≤
        3 * higham9_14_h (gamma fp n) *
          |higham9_18_tridiag_to_matrix T i j|) ∧
      (∀ i, ∑ j : Fin n,
        (higham9_18_tridiag_to_matrix T i j + DeltaA i j) * x_hat j =
          b i) :=
  higham9_14_tridiag_colDiagDom_source_h_bound_from_recurrence_LUBackwardError_fl_triangular_solves
    fp n T l_hat u_hat b ε (gamma fp n) (gamma_nonneg fp hn) hγ_lt_one
    hn hBE hε_le_gamma le_rfl hU_diag hrec hl hColDom

/-- **Theorem 9.14**, row-dominant recurrence actual-solve final `h(γ_n)`
bound. -/
theorem higham9_14_tridiag_rowDiagDom_source_h_bound_from_recurrence_LUBackwardError_fl_triangular_solves_gamma
    (fp : FPModel) (n : ℕ)
    (T : higham9_18_TridiagData n)
    (l_hat u_hat : Fin n → ℝ)
    (b : Fin n → ℝ)
    (ε : ℝ)
    (hn : gammaValid fp n)
    (hγ_lt_one : gamma fp n < 1)
    (hBE : LUBackwardError n (higham9_18_tridiag_to_matrix T)
      (tridiag_L_matrix l_hat) (tridiag_U_matrix u_hat T.c) ε)
    (hε_le_gamma : ε ≤ gamma fp n)
    (hU_diag : ∀ i : Fin n, tridiag_U_matrix u_hat T.c i i ≠ 0)
    (hrec : higham9_19_TridiagExactLURecurrence T l_hat u_hat)
    (hRowDom : IsRowDiagDominant n (higham9_18_tridiag_to_matrix T)) :
    let y_hat := fl_forwardSub fp n (tridiag_L_matrix l_hat) b
    let x_hat := fl_backSub fp n (tridiag_U_matrix u_hat T.c) y_hat
    ∃ DeltaA : Fin n → Fin n → ℝ,
      (∀ i j, |DeltaA i j| ≤
        3 * higham9_14_h (gamma fp n) *
          |higham9_18_tridiag_to_matrix T i j|) ∧
      (∀ i, ∑ j : Fin n,
        (higham9_18_tridiag_to_matrix T i j + DeltaA i j) * x_hat j =
          b i) :=
  higham9_14_tridiag_rowDiagDom_source_h_bound_from_recurrence_LUBackwardError_fl_triangular_solves
    fp n T l_hat u_hat b ε (gamma fp n) (gamma_nonneg fp hn) hγ_lt_one
    hn hBE hε_le_gamma le_rfl hU_diag hrec hRowDom

/-- **Theorem 9.14**, column-dominant exact builder factors with actual solves
at the natural `γ_n` coefficient. -/
theorem higham9_14_tridiag_colDiagDom_source_f_bound_from_builders_LUFactSpec_fl_triangular_solves_gamma
    (fp : FPModel) (n : ℕ)
    (T : higham9_18_TridiagData n)
    (l_hat u_hat : Fin n → ℝ)
    (b : Fin n → ℝ)
    (hn : gammaValid fp n)
    (hU_diag : ∀ i : Fin n, tridiag_U_matrix u_hat T.c i i ≠ 0)
    (hLU_exact : ∀ i j : Fin n,
      ∑ k : Fin n, tridiag_L_matrix l_hat i k *
        tridiag_U_matrix u_hat T.c k j =
        higham9_18_tridiag_to_matrix T i j)
    (hl : ∀ i : Fin n, |l_hat i| ≤ 1)
    (hColDom : IsDiagDominant n (higham9_18_tridiag_to_matrix T)) :
    let y_hat := fl_forwardSub fp n (tridiag_L_matrix l_hat) b
    let x_hat := fl_backSub fp n (tridiag_U_matrix u_hat T.c) y_hat
    ∃ DeltaA : Fin n → Fin n → ℝ,
      (∀ i j, |DeltaA i j| ≤
        3 * higham9_14_f (gamma fp n) *
          |higham9_18_tridiag_to_matrix T i j|) ∧
      (∀ i, ∑ j : Fin n,
        (higham9_18_tridiag_to_matrix T i j + DeltaA i j) * x_hat j =
          b i) :=
  higham9_14_tridiag_colDiagDom_source_f_bound_from_builders_LUFactSpec_fl_triangular_solves
    fp n T l_hat u_hat b (gamma fp n) (gamma_nonneg fp hn) hn le_rfl
    hU_diag hLU_exact hl hColDom

/-- **Theorem 9.14**, row-dominant exact builder factors with actual solves at
the natural `γ_n` coefficient. -/
theorem higham9_14_tridiag_rowDiagDom_source_f_bound_from_builders_LUFactSpec_fl_triangular_solves_gamma
    (fp : FPModel) (n : ℕ)
    (T : higham9_18_TridiagData n)
    (l_hat u_hat : Fin n → ℝ)
    (b : Fin n → ℝ)
    (hn : gammaValid fp n)
    (hU_diag : ∀ i : Fin n, tridiag_U_matrix u_hat T.c i i ≠ 0)
    (hLU_exact : ∀ i j : Fin n,
      ∑ k : Fin n, tridiag_L_matrix l_hat i k *
        tridiag_U_matrix u_hat T.c k j =
        higham9_18_tridiag_to_matrix T i j)
    (hRowDom : IsRowDiagDominant n (higham9_18_tridiag_to_matrix T)) :
    let y_hat := fl_forwardSub fp n (tridiag_L_matrix l_hat) b
    let x_hat := fl_backSub fp n (tridiag_U_matrix u_hat T.c) y_hat
    ∃ DeltaA : Fin n → Fin n → ℝ,
      (∀ i j, |DeltaA i j| ≤
        3 * higham9_14_f (gamma fp n) *
          |higham9_18_tridiag_to_matrix T i j|) ∧
      (∀ i, ∑ j : Fin n,
        (higham9_18_tridiag_to_matrix T i j + DeltaA i j) * x_hat j =
          b i) :=
  higham9_14_tridiag_rowDiagDom_source_f_bound_from_builders_LUFactSpec_fl_triangular_solves
    fp n T l_hat u_hat b (gamma fp n) (gamma_nonneg fp hn) hn le_rfl
    hU_diag hLU_exact hRowDom

/-- **Theorem 9.14**, column-dominant exact recurrence factors with actual
solves at the natural `γ_n` coefficient. -/
theorem higham9_14_tridiag_colDiagDom_source_f_bound_from_recurrence_LUFactSpec_fl_triangular_solves_gamma
    (fp : FPModel) (n : ℕ)
    (T : higham9_18_TridiagData n)
    (l_hat u_hat : Fin n → ℝ)
    (b : Fin n → ℝ)
    (hn : gammaValid fp n)
    (hU_diag : ∀ i : Fin n, tridiag_U_matrix u_hat T.c i i ≠ 0)
    (hrec : higham9_19_TridiagExactLURecurrence T l_hat u_hat)
    (hl : ∀ i : Fin n, |l_hat i| ≤ 1)
    (hColDom : IsDiagDominant n (higham9_18_tridiag_to_matrix T)) :
    let y_hat := fl_forwardSub fp n (tridiag_L_matrix l_hat) b
    let x_hat := fl_backSub fp n (tridiag_U_matrix u_hat T.c) y_hat
    ∃ DeltaA : Fin n → Fin n → ℝ,
      (∀ i j, |DeltaA i j| ≤
        3 * higham9_14_f (gamma fp n) *
          |higham9_18_tridiag_to_matrix T i j|) ∧
      (∀ i, ∑ j : Fin n,
        (higham9_18_tridiag_to_matrix T i j + DeltaA i j) * x_hat j =
          b i) :=
  higham9_14_tridiag_colDiagDom_source_f_bound_from_recurrence_LUFactSpec_fl_triangular_solves
    fp n T l_hat u_hat b (gamma fp n) (gamma_nonneg fp hn) hn le_rfl
    hU_diag hrec hl hColDom

/-- **Theorem 9.14**, row-dominant exact recurrence factors with actual solves
at the natural `γ_n` coefficient. -/
theorem higham9_14_tridiag_rowDiagDom_source_f_bound_from_recurrence_LUFactSpec_fl_triangular_solves_gamma
    (fp : FPModel) (n : ℕ)
    (T : higham9_18_TridiagData n)
    (l_hat u_hat : Fin n → ℝ)
    (b : Fin n → ℝ)
    (hn : gammaValid fp n)
    (hU_diag : ∀ i : Fin n, tridiag_U_matrix u_hat T.c i i ≠ 0)
    (hrec : higham9_19_TridiagExactLURecurrence T l_hat u_hat)
    (hRowDom : IsRowDiagDominant n (higham9_18_tridiag_to_matrix T)) :
    let y_hat := fl_forwardSub fp n (tridiag_L_matrix l_hat) b
    let x_hat := fl_backSub fp n (tridiag_U_matrix u_hat T.c) y_hat
    ∃ DeltaA : Fin n → Fin n → ℝ,
      (∀ i j, |DeltaA i j| ≤
        3 * higham9_14_f (gamma fp n) *
          |higham9_18_tridiag_to_matrix T i j|) ∧
      (∀ i, ∑ j : Fin n,
        (higham9_18_tridiag_to_matrix T i j + DeltaA i j) * x_hat j =
          b i) :=
  higham9_14_tridiag_rowDiagDom_source_f_bound_from_recurrence_LUFactSpec_fl_triangular_solves
    fp n T l_hat u_hat b (gamma fp n) (gamma_nonneg fp hn) hn le_rfl
    hU_diag hrec hRowDom

/-- **Theorem 9.14**, column-dominant exact builder factors with actual solves
and final `h(γ_n)` coefficient. -/
theorem higham9_14_tridiag_colDiagDom_source_h_bound_from_builders_LUFactSpec_fl_triangular_solves_gamma
    (fp : FPModel) (n : ℕ)
    (T : higham9_18_TridiagData n)
    (l_hat u_hat : Fin n → ℝ)
    (b : Fin n → ℝ)
    (hn : gammaValid fp n)
    (hγ_lt_one : gamma fp n < 1)
    (hU_diag : ∀ i : Fin n, tridiag_U_matrix u_hat T.c i i ≠ 0)
    (hLU_exact : ∀ i j : Fin n,
      ∑ k : Fin n, tridiag_L_matrix l_hat i k *
        tridiag_U_matrix u_hat T.c k j =
        higham9_18_tridiag_to_matrix T i j)
    (hl : ∀ i : Fin n, |l_hat i| ≤ 1)
    (hColDom : IsDiagDominant n (higham9_18_tridiag_to_matrix T)) :
    let y_hat := fl_forwardSub fp n (tridiag_L_matrix l_hat) b
    let x_hat := fl_backSub fp n (tridiag_U_matrix u_hat T.c) y_hat
    ∃ DeltaA : Fin n → Fin n → ℝ,
      (∀ i j, |DeltaA i j| ≤
        3 * higham9_14_h (gamma fp n) *
          |higham9_18_tridiag_to_matrix T i j|) ∧
      (∀ i, ∑ j : Fin n,
        (higham9_18_tridiag_to_matrix T i j + DeltaA i j) * x_hat j =
          b i) :=
  higham9_14_tridiag_colDiagDom_source_h_bound_from_builders_LUFactSpec_fl_triangular_solves
    fp n T l_hat u_hat b (gamma fp n) (gamma_nonneg fp hn) hγ_lt_one
    hn le_rfl hU_diag hLU_exact hl hColDom

/-- **Theorem 9.14**, row-dominant exact builder factors with actual solves and
final `h(γ_n)` coefficient. -/
theorem higham9_14_tridiag_rowDiagDom_source_h_bound_from_builders_LUFactSpec_fl_triangular_solves_gamma
    (fp : FPModel) (n : ℕ)
    (T : higham9_18_TridiagData n)
    (l_hat u_hat : Fin n → ℝ)
    (b : Fin n → ℝ)
    (hn : gammaValid fp n)
    (hγ_lt_one : gamma fp n < 1)
    (hU_diag : ∀ i : Fin n, tridiag_U_matrix u_hat T.c i i ≠ 0)
    (hLU_exact : ∀ i j : Fin n,
      ∑ k : Fin n, tridiag_L_matrix l_hat i k *
        tridiag_U_matrix u_hat T.c k j =
        higham9_18_tridiag_to_matrix T i j)
    (hRowDom : IsRowDiagDominant n (higham9_18_tridiag_to_matrix T)) :
    let y_hat := fl_forwardSub fp n (tridiag_L_matrix l_hat) b
    let x_hat := fl_backSub fp n (tridiag_U_matrix u_hat T.c) y_hat
    ∃ DeltaA : Fin n → Fin n → ℝ,
      (∀ i j, |DeltaA i j| ≤
        3 * higham9_14_h (gamma fp n) *
          |higham9_18_tridiag_to_matrix T i j|) ∧
      (∀ i, ∑ j : Fin n,
        (higham9_18_tridiag_to_matrix T i j + DeltaA i j) * x_hat j =
          b i) :=
  higham9_14_tridiag_rowDiagDom_source_h_bound_from_builders_LUFactSpec_fl_triangular_solves
    fp n T l_hat u_hat b (gamma fp n) (gamma_nonneg fp hn) hγ_lt_one
    hn le_rfl hU_diag hLU_exact hRowDom

/-- **Theorem 9.14**, column-dominant exact recurrence factors with actual
solves and final `h(γ_n)` coefficient. -/
theorem higham9_14_tridiag_colDiagDom_source_h_bound_from_recurrence_LUFactSpec_fl_triangular_solves_gamma
    (fp : FPModel) (n : ℕ)
    (T : higham9_18_TridiagData n)
    (l_hat u_hat : Fin n → ℝ)
    (b : Fin n → ℝ)
    (hn : gammaValid fp n)
    (hγ_lt_one : gamma fp n < 1)
    (hU_diag : ∀ i : Fin n, tridiag_U_matrix u_hat T.c i i ≠ 0)
    (hrec : higham9_19_TridiagExactLURecurrence T l_hat u_hat)
    (hl : ∀ i : Fin n, |l_hat i| ≤ 1)
    (hColDom : IsDiagDominant n (higham9_18_tridiag_to_matrix T)) :
    let y_hat := fl_forwardSub fp n (tridiag_L_matrix l_hat) b
    let x_hat := fl_backSub fp n (tridiag_U_matrix u_hat T.c) y_hat
    ∃ DeltaA : Fin n → Fin n → ℝ,
      (∀ i j, |DeltaA i j| ≤
        3 * higham9_14_h (gamma fp n) *
          |higham9_18_tridiag_to_matrix T i j|) ∧
      (∀ i, ∑ j : Fin n,
        (higham9_18_tridiag_to_matrix T i j + DeltaA i j) * x_hat j =
          b i) :=
  higham9_14_tridiag_colDiagDom_source_h_bound_from_recurrence_LUFactSpec_fl_triangular_solves
    fp n T l_hat u_hat b (gamma fp n) (gamma_nonneg fp hn) hγ_lt_one
    hn le_rfl hU_diag hrec hl hColDom

/-- **Theorem 9.14**, row-dominant exact recurrence factors with actual solves
and final `h(γ_n)` coefficient. -/
theorem higham9_14_tridiag_rowDiagDom_source_h_bound_from_recurrence_LUFactSpec_fl_triangular_solves_gamma
    (fp : FPModel) (n : ℕ)
    (T : higham9_18_TridiagData n)
    (l_hat u_hat : Fin n → ℝ)
    (b : Fin n → ℝ)
    (hn : gammaValid fp n)
    (hγ_lt_one : gamma fp n < 1)
    (hU_diag : ∀ i : Fin n, tridiag_U_matrix u_hat T.c i i ≠ 0)
    (hrec : higham9_19_TridiagExactLURecurrence T l_hat u_hat)
    (hRowDom : IsRowDiagDominant n (higham9_18_tridiag_to_matrix T)) :
    let y_hat := fl_forwardSub fp n (tridiag_L_matrix l_hat) b
    let x_hat := fl_backSub fp n (tridiag_U_matrix u_hat T.c) y_hat
    ∃ DeltaA : Fin n → Fin n → ℝ,
      (∀ i j, |DeltaA i j| ≤
        3 * higham9_14_h (gamma fp n) *
          |higham9_18_tridiag_to_matrix T i j|) ∧
      (∀ i, ∑ j : Fin n,
        (higham9_18_tridiag_to_matrix T i j + DeltaA i j) * x_hat j =
          b i) :=
  higham9_14_tridiag_rowDiagDom_source_h_bound_from_recurrence_LUFactSpec_fl_triangular_solves
    fp n T l_hat u_hat b (gamma fp n) (gamma_nonneg fp hn) hγ_lt_one
    hn le_rfl hU_diag hrec hRowDom

/-- **Theorem 9.14**, column-dominant exact-LU actual-solve source model at the
natural `γ_n` coefficient. -/
theorem higham9_14_tridiag_colDiagDom_source_f_bound_from_LUBackwardError_fl_triangular_solves_gamma
    (fp : FPModel) (n : ℕ)
    (A L_hat U_hat : Fin n → Fin n → ℝ)
    (b : Fin n → ℝ)
    (ε : ℝ)
    (hn : gammaValid fp n)
    (hBE : LUBackwardError n A L_hat U_hat ε)
    (hε_le_gamma : ε ≤ gamma fp n)
    (hLU : LUFactSpec n A L_hat U_hat)
    (hdetA : Matrix.det (Matrix.of A : Matrix (Fin n) (Fin n) ℝ) ≠ 0)
    (hA_tridiag : IsTridiagonal n A)
    (hColDom : IsDiagDominant n A) :
    let y_hat := fl_forwardSub fp n L_hat b
    let x_hat := fl_backSub fp n U_hat y_hat
    ∃ DeltaA : Fin n → Fin n → ℝ,
      (∀ i j, |DeltaA i j| ≤
        3 * higham9_14_f (gamma fp n) * |A i j|) ∧
      (∀ i, ∑ j : Fin n, (A i j + DeltaA i j) * x_hat j = b i) :=
  higham9_14_tridiag_colDiagDom_source_f_bound_from_LUBackwardError_fl_triangular_solves
    fp n A L_hat U_hat b ε (gamma fp n) (gamma_nonneg fp hn) hn hBE
    hε_le_gamma le_rfl hLU hdetA hA_tridiag hColDom

/-- **Theorem 9.14**, row-dominant exact-LU actual-solve source model at the
natural `γ_n` coefficient. -/
theorem higham9_14_tridiag_rowDiagDom_source_f_bound_from_LUBackwardError_fl_triangular_solves_gamma
    (fp : FPModel) (n : ℕ)
    (A L_hat U_hat : Fin n → Fin n → ℝ)
    (b : Fin n → ℝ)
    (ε : ℝ)
    (hn : gammaValid fp n)
    (hBE : LUBackwardError n A L_hat U_hat ε)
    (hε_le_gamma : ε ≤ gamma fp n)
    (hLU : LUFactSpec n A L_hat U_hat)
    (hdetA : Matrix.det (Matrix.of A : Matrix (Fin n) (Fin n) ℝ) ≠ 0)
    (hA_tridiag : IsTridiagonal n A)
    (hRowDom : IsRowDiagDominant n A) :
    let y_hat := fl_forwardSub fp n L_hat b
    let x_hat := fl_backSub fp n U_hat y_hat
    ∃ DeltaA : Fin n → Fin n → ℝ,
      (∀ i j, |DeltaA i j| ≤
        3 * higham9_14_f (gamma fp n) * |A i j|) ∧
      (∀ i, ∑ j : Fin n, (A i j + DeltaA i j) * x_hat j = b i) :=
  higham9_14_tridiag_rowDiagDom_source_f_bound_from_LUBackwardError_fl_triangular_solves
    fp n A L_hat U_hat b ε (gamma fp n) (gamma_nonneg fp hn) hn hBE
    hε_le_gamma le_rfl hLU hdetA hA_tridiag hRowDom

/-- **Theorem 9.14**, column-dominant exact-LU actual-solve final `h(γ_n)`
bound. -/
theorem higham9_14_tridiag_colDiagDom_source_h_bound_from_LUBackwardError_fl_triangular_solves_gamma
    (fp : FPModel) (n : ℕ)
    (A L_hat U_hat : Fin n → Fin n → ℝ)
    (b : Fin n → ℝ)
    (ε : ℝ)
    (hn : gammaValid fp n)
    (hγ_lt_one : gamma fp n < 1)
    (hBE : LUBackwardError n A L_hat U_hat ε)
    (hε_le_gamma : ε ≤ gamma fp n)
    (hLU : LUFactSpec n A L_hat U_hat)
    (hdetA : Matrix.det (Matrix.of A : Matrix (Fin n) (Fin n) ℝ) ≠ 0)
    (hA_tridiag : IsTridiagonal n A)
    (hColDom : IsDiagDominant n A) :
    let y_hat := fl_forwardSub fp n L_hat b
    let x_hat := fl_backSub fp n U_hat y_hat
    ∃ DeltaA : Fin n → Fin n → ℝ,
      (∀ i j, |DeltaA i j| ≤
        3 * higham9_14_h (gamma fp n) * |A i j|) ∧
      (∀ i, ∑ j : Fin n, (A i j + DeltaA i j) * x_hat j = b i) :=
  higham9_14_tridiag_colDiagDom_source_h_bound_from_LUBackwardError_fl_triangular_solves
    fp n A L_hat U_hat b ε (gamma fp n) (gamma_nonneg fp hn) hγ_lt_one
    hn hBE hε_le_gamma le_rfl hLU hdetA hA_tridiag hColDom

/-- **Theorem 9.14**, row-dominant exact-LU actual-solve final `h(γ_n)`
bound. -/
theorem higham9_14_tridiag_rowDiagDom_source_h_bound_from_LUBackwardError_fl_triangular_solves_gamma
    (fp : FPModel) (n : ℕ)
    (A L_hat U_hat : Fin n → Fin n → ℝ)
    (b : Fin n → ℝ)
    (ε : ℝ)
    (hn : gammaValid fp n)
    (hγ_lt_one : gamma fp n < 1)
    (hBE : LUBackwardError n A L_hat U_hat ε)
    (hε_le_gamma : ε ≤ gamma fp n)
    (hLU : LUFactSpec n A L_hat U_hat)
    (hdetA : Matrix.det (Matrix.of A : Matrix (Fin n) (Fin n) ℝ) ≠ 0)
    (hA_tridiag : IsTridiagonal n A)
    (hRowDom : IsRowDiagDominant n A) :
    let y_hat := fl_forwardSub fp n L_hat b
    let x_hat := fl_backSub fp n U_hat y_hat
    ∃ DeltaA : Fin n → Fin n → ℝ,
      (∀ i j, |DeltaA i j| ≤
        3 * higham9_14_h (gamma fp n) * |A i j|) ∧
      (∀ i, ∑ j : Fin n, (A i j + DeltaA i j) * x_hat j = b i) :=
  higham9_14_tridiag_rowDiagDom_source_h_bound_from_LUBackwardError_fl_triangular_solves
    fp n A L_hat U_hat b ε (gamma fp n) (gamma_nonneg fp hn) hγ_lt_one
    hn hBE hε_le_gamma le_rfl hLU hdetA hA_tridiag hRowDom

/-- **Theorem 9.14**, column-dominant exact tridiagonal LU actual-solve source
model at the natural `γ_n` coefficient from an `LUFactSpec`. -/
theorem higham9_14_tridiag_colDiagDom_source_f_bound_from_LUFactSpec_fl_triangular_solves_gamma
    (fp : FPModel) (n : ℕ)
    (A L_hat U_hat : Fin n → Fin n → ℝ)
    (b : Fin n → ℝ)
    (hn : gammaValid fp n)
    (hLU : LUFactSpec n A L_hat U_hat)
    (hdetA : Matrix.det (Matrix.of A : Matrix (Fin n) (Fin n) ℝ) ≠ 0)
    (hA_tridiag : IsTridiagonal n A)
    (hColDom : IsDiagDominant n A) :
    let y_hat := fl_forwardSub fp n L_hat b
    let x_hat := fl_backSub fp n U_hat y_hat
    ∃ DeltaA : Fin n → Fin n → ℝ,
      (∀ i j, |DeltaA i j| ≤
        3 * higham9_14_f (gamma fp n) * |A i j|) ∧
      (∀ i, ∑ j : Fin n, (A i j + DeltaA i j) * x_hat j = b i) :=
  higham9_14_tridiag_colDiagDom_source_f_bound_from_LUFactSpec_fl_triangular_solves
    fp n A L_hat U_hat b (gamma fp n) (gamma_nonneg fp hn) hn le_rfl
    hLU hdetA hA_tridiag hColDom

/-- **Theorem 9.14**, row-dominant exact tridiagonal LU actual-solve source
model at the natural `γ_n` coefficient from an `LUFactSpec`. -/
theorem higham9_14_tridiag_rowDiagDom_source_f_bound_from_LUFactSpec_fl_triangular_solves_gamma
    (fp : FPModel) (n : ℕ)
    (A L_hat U_hat : Fin n → Fin n → ℝ)
    (b : Fin n → ℝ)
    (hn : gammaValid fp n)
    (hLU : LUFactSpec n A L_hat U_hat)
    (hdetA : Matrix.det (Matrix.of A : Matrix (Fin n) (Fin n) ℝ) ≠ 0)
    (hA_tridiag : IsTridiagonal n A)
    (hRowDom : IsRowDiagDominant n A) :
    let y_hat := fl_forwardSub fp n L_hat b
    let x_hat := fl_backSub fp n U_hat y_hat
    ∃ DeltaA : Fin n → Fin n → ℝ,
      (∀ i j, |DeltaA i j| ≤
        3 * higham9_14_f (gamma fp n) * |A i j|) ∧
      (∀ i, ∑ j : Fin n, (A i j + DeltaA i j) * x_hat j = b i) :=
  higham9_14_tridiag_rowDiagDom_source_f_bound_from_LUFactSpec_fl_triangular_solves
    fp n A L_hat U_hat b (gamma fp n) (gamma_nonneg fp hn) hn le_rfl
    hLU hdetA hA_tridiag hRowDom

/-- **Theorem 9.14**, column-dominant exact tridiagonal LU actual-solve final
source model at the natural `γ_n` coefficient from an `LUFactSpec`. -/
theorem higham9_14_tridiag_colDiagDom_source_h_bound_from_LUFactSpec_fl_triangular_solves_gamma
    (fp : FPModel) (n : ℕ)
    (A L_hat U_hat : Fin n → Fin n → ℝ)
    (b : Fin n → ℝ)
    (hn : gammaValid fp n)
    (hγ_lt_one : gamma fp n < 1)
    (hLU : LUFactSpec n A L_hat U_hat)
    (hdetA : Matrix.det (Matrix.of A : Matrix (Fin n) (Fin n) ℝ) ≠ 0)
    (hA_tridiag : IsTridiagonal n A)
    (hColDom : IsDiagDominant n A) :
    let y_hat := fl_forwardSub fp n L_hat b
    let x_hat := fl_backSub fp n U_hat y_hat
    ∃ DeltaA : Fin n → Fin n → ℝ,
      (∀ i j, |DeltaA i j| ≤
        3 * higham9_14_h (gamma fp n) * |A i j|) ∧
      (∀ i, ∑ j : Fin n, (A i j + DeltaA i j) * x_hat j = b i) :=
  higham9_14_tridiag_colDiagDom_source_h_bound_from_LUFactSpec_fl_triangular_solves
    fp n A L_hat U_hat b (gamma fp n) (gamma_nonneg fp hn) hγ_lt_one
    hn le_rfl hLU hdetA hA_tridiag hColDom

/-- **Theorem 9.14**, row-dominant exact tridiagonal LU actual-solve final
source model at the natural `γ_n` coefficient from an `LUFactSpec`. -/
theorem higham9_14_tridiag_rowDiagDom_source_h_bound_from_LUFactSpec_fl_triangular_solves_gamma
    (fp : FPModel) (n : ℕ)
    (A L_hat U_hat : Fin n → Fin n → ℝ)
    (b : Fin n → ℝ)
    (hn : gammaValid fp n)
    (hγ_lt_one : gamma fp n < 1)
    (hLU : LUFactSpec n A L_hat U_hat)
    (hdetA : Matrix.det (Matrix.of A : Matrix (Fin n) (Fin n) ℝ) ≠ 0)
    (hA_tridiag : IsTridiagonal n A)
    (hRowDom : IsRowDiagDominant n A) :
    let y_hat := fl_forwardSub fp n L_hat b
    let x_hat := fl_backSub fp n U_hat y_hat
    ∃ DeltaA : Fin n → Fin n → ℝ,
      (∀ i j, |DeltaA i j| ≤
        3 * higham9_14_h (gamma fp n) * |A i j|) ∧
      (∀ i, ∑ j : Fin n, (A i j + DeltaA i j) * x_hat j = b i) :=
  higham9_14_tridiag_rowDiagDom_source_h_bound_from_LUFactSpec_fl_triangular_solves
    fp n A L_hat U_hat b (gamma fp n) (gamma_nonneg fp hn) hγ_lt_one
    hn le_rfl hLU hdetA hA_tridiag hRowDom

/-- **Theorem 9.14**, `TridiagData` column-dominant exact-LU actual-solve
source model at the natural `γ_n` coefficient from an `LUFactSpec`. -/
theorem higham9_14_tridiag_data_colDiagDom_source_f_bound_from_LUFactSpec_fl_triangular_solves_gamma
    (fp : FPModel) {n : ℕ}
    (T : higham9_18_TridiagData n)
    (L_hat U_hat : Fin n → Fin n → ℝ)
    (b : Fin n → ℝ)
    (hn : gammaValid fp n)
    (hLU : LUFactSpec n (higham9_18_tridiag_to_matrix T) L_hat U_hat)
    (hdetA :
      Matrix.det
        (Matrix.of (higham9_18_tridiag_to_matrix T) :
          Matrix (Fin n) (Fin n) ℝ) ≠ 0)
    (hColDom : IsDiagDominant n (higham9_18_tridiag_to_matrix T)) :
    let y_hat := fl_forwardSub fp n L_hat b
    let x_hat := fl_backSub fp n U_hat y_hat
    ∃ DeltaA : Fin n → Fin n → ℝ,
      (∀ i j, |DeltaA i j| ≤
        3 * higham9_14_f (gamma fp n) *
          |higham9_18_tridiag_to_matrix T i j|) ∧
      (∀ i, ∑ j : Fin n,
        (higham9_18_tridiag_to_matrix T i j + DeltaA i j) * x_hat j =
          b i) :=
  higham9_14_tridiag_data_colDiagDom_source_f_bound_from_LUFactSpec_fl_triangular_solves
    fp T L_hat U_hat b (gamma fp n) (gamma_nonneg fp hn) hn le_rfl
    hLU hdetA hColDom

/-- **Theorem 9.14**, `TridiagData` row-dominant exact-LU actual-solve source
model at the natural `γ_n` coefficient from an `LUFactSpec`. -/
theorem higham9_14_tridiag_data_rowDiagDom_source_f_bound_from_LUFactSpec_fl_triangular_solves_gamma
    (fp : FPModel) {n : ℕ}
    (T : higham9_18_TridiagData n)
    (L_hat U_hat : Fin n → Fin n → ℝ)
    (b : Fin n → ℝ)
    (hn : gammaValid fp n)
    (hLU : LUFactSpec n (higham9_18_tridiag_to_matrix T) L_hat U_hat)
    (hdetA :
      Matrix.det
        (Matrix.of (higham9_18_tridiag_to_matrix T) :
          Matrix (Fin n) (Fin n) ℝ) ≠ 0)
    (hRowDom : IsRowDiagDominant n (higham9_18_tridiag_to_matrix T)) :
    let y_hat := fl_forwardSub fp n L_hat b
    let x_hat := fl_backSub fp n U_hat y_hat
    ∃ DeltaA : Fin n → Fin n → ℝ,
      (∀ i j, |DeltaA i j| ≤
        3 * higham9_14_f (gamma fp n) *
          |higham9_18_tridiag_to_matrix T i j|) ∧
      (∀ i, ∑ j : Fin n,
        (higham9_18_tridiag_to_matrix T i j + DeltaA i j) * x_hat j =
          b i) :=
  higham9_14_tridiag_data_rowDiagDom_source_f_bound_from_LUFactSpec_fl_triangular_solves
    fp T L_hat U_hat b (gamma fp n) (gamma_nonneg fp hn) hn le_rfl
    hLU hdetA hRowDom

/-- **Theorem 9.14**, `TridiagData` column-dominant exact-LU actual-solve
final source model at the natural `γ_n` coefficient from an `LUFactSpec`. -/
theorem higham9_14_tridiag_data_colDiagDom_source_h_bound_from_LUFactSpec_fl_triangular_solves_gamma
    (fp : FPModel) {n : ℕ}
    (T : higham9_18_TridiagData n)
    (L_hat U_hat : Fin n → Fin n → ℝ)
    (b : Fin n → ℝ)
    (hn : gammaValid fp n)
    (hγ_lt_one : gamma fp n < 1)
    (hLU : LUFactSpec n (higham9_18_tridiag_to_matrix T) L_hat U_hat)
    (hdetA :
      Matrix.det
        (Matrix.of (higham9_18_tridiag_to_matrix T) :
          Matrix (Fin n) (Fin n) ℝ) ≠ 0)
    (hColDom : IsDiagDominant n (higham9_18_tridiag_to_matrix T)) :
    let y_hat := fl_forwardSub fp n L_hat b
    let x_hat := fl_backSub fp n U_hat y_hat
    ∃ DeltaA : Fin n → Fin n → ℝ,
      (∀ i j, |DeltaA i j| ≤
        3 * higham9_14_h (gamma fp n) *
          |higham9_18_tridiag_to_matrix T i j|) ∧
      (∀ i, ∑ j : Fin n,
        (higham9_18_tridiag_to_matrix T i j + DeltaA i j) * x_hat j =
          b i) :=
  higham9_14_tridiag_data_colDiagDom_source_h_bound_from_LUFactSpec_fl_triangular_solves
    fp T L_hat U_hat b (gamma fp n) (gamma_nonneg fp hn) hγ_lt_one
    hn le_rfl hLU hdetA hColDom

/-- **Theorem 9.14**, `TridiagData` row-dominant exact-LU actual-solve final
source model at the natural `γ_n` coefficient from an `LUFactSpec`. -/
theorem higham9_14_tridiag_data_rowDiagDom_source_h_bound_from_LUFactSpec_fl_triangular_solves_gamma
    (fp : FPModel) {n : ℕ}
    (T : higham9_18_TridiagData n)
    (L_hat U_hat : Fin n → Fin n → ℝ)
    (b : Fin n → ℝ)
    (hn : gammaValid fp n)
    (hγ_lt_one : gamma fp n < 1)
    (hLU : LUFactSpec n (higham9_18_tridiag_to_matrix T) L_hat U_hat)
    (hdetA :
      Matrix.det
        (Matrix.of (higham9_18_tridiag_to_matrix T) :
          Matrix (Fin n) (Fin n) ℝ) ≠ 0)
    (hRowDom : IsRowDiagDominant n (higham9_18_tridiag_to_matrix T)) :
    let y_hat := fl_forwardSub fp n L_hat b
    let x_hat := fl_backSub fp n U_hat y_hat
    ∃ DeltaA : Fin n → Fin n → ℝ,
      (∀ i j, |DeltaA i j| ≤
        3 * higham9_14_h (gamma fp n) *
          |higham9_18_tridiag_to_matrix T i j|) ∧
      (∀ i, ∑ j : Fin n,
        (higham9_18_tridiag_to_matrix T i j + DeltaA i j) * x_hat j =
          b i) :=
  higham9_14_tridiag_data_rowDiagDom_source_h_bound_from_LUFactSpec_fl_triangular_solves
    fp T L_hat U_hat b (gamma fp n) (gamma_nonneg fp hn) hγ_lt_one
    hn le_rfl hLU hdetA hRowDom

/-- **Theorem 9.14**, SPD positive-`D L^T` model-consuming final bound.

The SPD tridiagonal algebraic core gives `|Lhat||Uhat| = |A|`; with the source
equation (9.20)/(9.21) perturbation models, this yields Higham's final
`h(u)|A|` bound. -/
theorem higham9_14_spd_tridiag_positive_DLT_source_h_bound_of_models
    (n : ℕ)
    (A L_hat U_hat : Fin n → Fin n → ℝ)
    (d : Fin n → ℝ)
    (y_hat x_hat b : Fin n → ℝ)
    (u : ℝ) (hu : 0 ≤ u) (hu_lt_one : u < 1)
    (hStruct : IsTridiagLU n L_hat U_hat)
    (hLU_eq : ∀ i j : Fin n,
      ∑ k : Fin n, L_hat i k * U_hat k j = A i j)
    (hd_pos : ∀ k : Fin n, 0 < d k)
    (hDLT : ∀ k j : Fin n, U_hat k j = d k * L_hat j k)
    (DeltaA_LU DeltaL DeltaU : Fin n → Fin n → ℝ)
    (h20 : higham9_20_tridiag_lu_perturbation_model n A L_hat U_hat
      DeltaA_LU u)
    (h21 : higham9_21_tridiag_solve_perturbation_model n L_hat U_hat
      y_hat x_hat b DeltaL DeltaU u) :
    ∃ DeltaA : Fin n → Fin n → ℝ,
      (∀ i j, |DeltaA i j| ≤ higham9_14_h u * |A i j|) ∧
      (∀ i, ∑ j : Fin n, (A i j + DeltaA i j) * x_hat j = b i) :=
  higham9_14_source_h_bound_of_absLU_le_absA_and_9_20_9_21_models
    n A L_hat U_hat y_hat x_hat b u hu hu_lt_one
    (fun i j => le_of_eq
      (higham9_12_spd_tridiag_absLU_eq_of_positive_DLT A L_hat U_hat d
        hStruct hLU_eq hd_pos hDLT i j))
    DeltaA_LU DeltaL DeltaU h20 h21

/-- **Theorem 9.14**, SPD positive-`D L^T` model-consuming final bound from
the explicit tridiagonal recurrence.

This specializes `higham9_14_spd_tridiag_positive_DLT_source_h_bound_of_models`
to source tridiagonal data and the exact recurrence (9.19), removing the need
for callers to manually assemble the builder matrices and exact product
identity. -/
theorem higham9_14_spd_tridiag_positive_DLT_source_h_bound_of_recurrence
    (n : ℕ)
    (T : higham9_18_TridiagData n)
    (l_hat u_hat d y_hat x_hat b : Fin n → ℝ)
    (u : ℝ) (hu : 0 ≤ u) (hu_lt_one : u < 1)
    (hrec : higham9_19_TridiagExactLURecurrence T l_hat u_hat)
    (hd_pos : ∀ k : Fin n, 0 < d k)
    (hDLT : ∀ k j : Fin n,
      tridiag_U_matrix u_hat T.c k j =
        d k * tridiag_L_matrix l_hat j k)
    (DeltaA_LU DeltaL DeltaU : Fin n → Fin n → ℝ)
    (h20 : higham9_20_tridiag_lu_perturbation_model n
      (higham9_18_tridiag_to_matrix T)
      (tridiag_L_matrix l_hat) (tridiag_U_matrix u_hat T.c)
      DeltaA_LU u)
    (h21 : higham9_21_tridiag_solve_perturbation_model n
      (tridiag_L_matrix l_hat) (tridiag_U_matrix u_hat T.c)
      y_hat x_hat b DeltaL DeltaU u) :
    ∃ DeltaA : Fin n → Fin n → ℝ,
      (∀ i j,
        |DeltaA i j| ≤
          higham9_14_h u * |higham9_18_tridiag_to_matrix T i j|) ∧
      (∀ i,
        ∑ j : Fin n,
          (higham9_18_tridiag_to_matrix T i j + DeltaA i j) * x_hat j =
        b i) :=
  higham9_14_spd_tridiag_positive_DLT_source_h_bound_of_models
    n (higham9_18_tridiag_to_matrix T)
    (tridiag_L_matrix l_hat) (tridiag_U_matrix u_hat T.c)
    d y_hat x_hat b u hu hu_lt_one
    (tridiag_matrices_isTridiagLU l_hat u_hat T.c)
    (higham9_19_tridiag_exact_product_of_recurrence T l_hat u_hat hrec)
    hd_pos hDLT DeltaA_LU DeltaL DeltaU h20 h21

/-- **Theorem 9.14**, nonnegative-LU model-consuming final bound.

Nonnegative LU factors give `|Lhat||Uhat| = |A|`; with the source equation
(9.20)/(9.21) perturbation models, this yields the final `h(u)|A|` bound. -/
theorem higham9_14_nonnegative_lu_source_h_bound_of_models
    (n : ℕ)
    (A L_hat U_hat : Fin n → Fin n → ℝ)
    (y_hat x_hat b : Fin n → ℝ)
    (u : ℝ) (hu : 0 ≤ u) (hu_lt_one : u < 1)
    (hNonneg : HasNonnegLUFactors n A L_hat U_hat)
    (DeltaA_LU DeltaL DeltaU : Fin n → Fin n → ℝ)
    (h20 : higham9_20_tridiag_lu_perturbation_model n A L_hat U_hat
      DeltaA_LU u)
    (h21 : higham9_21_tridiag_solve_perturbation_model n L_hat U_hat
      y_hat x_hat b DeltaL DeltaU u) :
    ∃ DeltaA : Fin n → Fin n → ℝ,
      (∀ i j, |DeltaA i j| ≤ higham9_14_h u * |A i j|) ∧
      (∀ i, ∑ j : Fin n, (A i j + DeltaA i j) * x_hat j = b i) :=
  higham9_14_source_h_bound_of_absLU_le_absA_and_9_20_9_21_models
    n A L_hat U_hat y_hat x_hat b u hu hu_lt_one
    (fun i j => le_of_eq
      (higham9_12_nonneg_lu_optimal_growth n A L_hat U_hat hNonneg i j))
    DeltaA_LU DeltaL DeltaU h20 h21

/-- **Theorem 9.14**, M-matrix LU model-consuming final bound.

The M-matrix optimal-growth theorem supplies `|Lhat||Uhat| = |A|`; with the
source equation (9.20)/(9.21) perturbation models, this yields the final
`h(u)|A|` bound. -/
theorem higham9_14_mmatrix_lu_source_h_bound_of_models
    (n : ℕ)
    (A L_hat U_hat : Fin n → Fin n → ℝ)
    (y_hat x_hat b : Fin n → ℝ)
    (u : ℝ) (hu : 0 ≤ u) (hu_lt_one : u < 1)
    (hM : IsMMatrix n A)
    (hLU : LUFactSpec n A L_hat U_hat)
    (hL_nn : ∀ i k : Fin n, 0 ≤ L_hat i k)
    (hU_nn : ∀ k j : Fin n, 0 ≤ U_hat k j)
    (DeltaA_LU DeltaL DeltaU : Fin n → Fin n → ℝ)
    (h20 : higham9_20_tridiag_lu_perturbation_model n A L_hat U_hat
      DeltaA_LU u)
    (h21 : higham9_21_tridiag_solve_perturbation_model n L_hat U_hat
      y_hat x_hat b DeltaL DeltaU u) :
    ∃ DeltaA : Fin n → Fin n → ℝ,
      (∀ i j, |DeltaA i j| ≤ higham9_14_h u * |A i j|) ∧
      (∀ i, ∑ j : Fin n, (A i j + DeltaA i j) * x_hat j = b i) :=
  higham9_14_source_h_bound_of_absLU_le_absA_and_9_20_9_21_models
    n A L_hat U_hat y_hat x_hat b u hu hu_lt_one
    (fun i j => le_of_eq
      (higham9_12_mmatrix_lu_optimal_growth n A L_hat U_hat hM hLU
        hL_nn hU_nn i j))
    DeltaA_LU DeltaL DeltaU h20 h21

/-- **Theorem 9.14**, sign-equivalent optimal-growth model-consuming final
bound.

The sign-equivalence optimal-growth theorem supplies `|Lhat||Uhat| = |A|`;
with the source equation (9.20)/(9.21) perturbation models, this yields the
final `h(u)|A|` bound. -/
theorem higham9_14_sign_equiv_source_h_bound_of_models
    (n : ℕ)
    (B L_B U_B : Fin n → Fin n → ℝ)
    (D₁ D₂ : Fin n → Fin n → ℝ)
    (hD₁ : IsSignDiag n D₁) (hD₂ : IsSignDiag n D₂)
    (hB_growth : ∀ i j : Fin n,
      ∑ k : Fin n, |L_B i k| * |U_B k j| = |B i j|)
    (A L_hat U_hat : Fin n → Fin n → ℝ)
    (hA_eq : ∀ i j : Fin n,
      A i j = ∑ k₁ : Fin n, D₁ i k₁ * (∑ k₂ : Fin n, B k₁ k₂ * D₂ k₂ j))
    (hL_abs : ∀ i k : Fin n, |L_hat i k| = |L_B i k|)
    (hU_abs : ∀ k j : Fin n, |U_hat k j| = |U_B k j|)
    (y_hat x_hat b : Fin n → ℝ)
    (u : ℝ) (hu : 0 ≤ u) (hu_lt_one : u < 1)
    (DeltaA_LU DeltaL DeltaU : Fin n → Fin n → ℝ)
    (h20 : higham9_20_tridiag_lu_perturbation_model n A L_hat U_hat
      DeltaA_LU u)
    (h21 : higham9_21_tridiag_solve_perturbation_model n L_hat U_hat
      y_hat x_hat b DeltaL DeltaU u) :
    ∃ DeltaA : Fin n → Fin n → ℝ,
      (∀ i j, |DeltaA i j| ≤ higham9_14_h u * |A i j|) ∧
      (∀ i, ∑ j : Fin n, (A i j + DeltaA i j) * x_hat j = b i) :=
  higham9_14_source_h_bound_of_absLU_le_absA_and_9_20_9_21_models
    n A L_hat U_hat y_hat x_hat b u hu hu_lt_one
    (fun i j => le_of_eq
      (higham9_12_sign_equiv_optimal_growth n B L_B U_B D₁ D₂
        hD₁ hD₂ hB_growth A hA_eq L_hat U_hat hL_abs hU_abs i j))
    DeltaA_LU DeltaL DeltaU h20 h21

/-- **Theorem 9.14**, SPD positive-`D L^T` model-consuming `f(u)` bound.

This is the equation-(9.22) counterpart of
`higham9_14_spd_tridiag_positive_DLT_source_h_bound_of_models`: the same
exact SPD tridiagonal growth equality feeds the direct `f(u)|A|` bound without
the final `1/(1-u)` denominator step. -/
theorem higham9_14_spd_tridiag_positive_DLT_source_f_bound_of_models
    (n : ℕ)
    (A L_hat U_hat : Fin n → Fin n → ℝ)
    (d : Fin n → ℝ)
    (y_hat x_hat b : Fin n → ℝ)
    (u : ℝ) (hu : 0 ≤ u)
    (hStruct : IsTridiagLU n L_hat U_hat)
    (hLU_eq : ∀ i j : Fin n,
      ∑ k : Fin n, L_hat i k * U_hat k j = A i j)
    (hd_pos : ∀ k : Fin n, 0 < d k)
    (hDLT : ∀ k j : Fin n, U_hat k j = d k * L_hat j k)
    (DeltaA_LU DeltaL DeltaU : Fin n → Fin n → ℝ)
    (h20 : higham9_20_tridiag_lu_perturbation_model n A L_hat U_hat
      DeltaA_LU u)
    (h21 : higham9_21_tridiag_solve_perturbation_model n L_hat U_hat
      y_hat x_hat b DeltaL DeltaU u) :
    ∃ DeltaA : Fin n → Fin n → ℝ,
      (∀ i j, |DeltaA i j| ≤ higham9_14_f u * |A i j|) ∧
      (∀ i, ∑ j : Fin n, (A i j + DeltaA i j) * x_hat j = b i) := by
  obtain ⟨DeltaA, hDeltaA, hBackward⟩ :=
    higham9_14_source_f_bound_of_absLU_le_const_absA_and_9_20_9_21_models
      n A L_hat U_hat y_hat x_hat b 1 u hu
      (fun i j => by
        simpa [one_mul] using le_of_eq
          (higham9_12_spd_tridiag_absLU_eq_of_positive_DLT
            A L_hat U_hat d hStruct hLU_eq hd_pos hDLT i j))
      DeltaA_LU DeltaL DeltaU h20 h21
  refine ⟨DeltaA, ?_, hBackward⟩
  intro i j
  simpa [one_mul] using hDeltaA i j

/-- **Theorem 9.14**, SPD positive-`D L^T` model-consuming `f(u)` bound from
the explicit tridiagonal recurrence. -/
theorem higham9_14_spd_tridiag_positive_DLT_source_f_bound_of_recurrence
    (n : ℕ)
    (T : higham9_18_TridiagData n)
    (l_hat u_hat d y_hat x_hat b : Fin n → ℝ)
    (u : ℝ) (hu : 0 ≤ u)
    (hrec : higham9_19_TridiagExactLURecurrence T l_hat u_hat)
    (hd_pos : ∀ k : Fin n, 0 < d k)
    (hDLT : ∀ k j : Fin n,
      tridiag_U_matrix u_hat T.c k j =
        d k * tridiag_L_matrix l_hat j k)
    (DeltaA_LU DeltaL DeltaU : Fin n → Fin n → ℝ)
    (h20 : higham9_20_tridiag_lu_perturbation_model n
      (higham9_18_tridiag_to_matrix T)
      (tridiag_L_matrix l_hat) (tridiag_U_matrix u_hat T.c)
      DeltaA_LU u)
    (h21 : higham9_21_tridiag_solve_perturbation_model n
      (tridiag_L_matrix l_hat) (tridiag_U_matrix u_hat T.c)
      y_hat x_hat b DeltaL DeltaU u) :
    ∃ DeltaA : Fin n → Fin n → ℝ,
      (∀ i j,
        |DeltaA i j| ≤
          higham9_14_f u * |higham9_18_tridiag_to_matrix T i j|) ∧
      (∀ i,
        ∑ j : Fin n,
          (higham9_18_tridiag_to_matrix T i j + DeltaA i j) * x_hat j =
        b i) :=
  higham9_14_spd_tridiag_positive_DLT_source_f_bound_of_models
    n (higham9_18_tridiag_to_matrix T)
    (tridiag_L_matrix l_hat) (tridiag_U_matrix u_hat T.c)
    d y_hat x_hat b u hu
    (tridiag_matrices_isTridiagLU l_hat u_hat T.c)
    (higham9_19_tridiag_exact_product_of_recurrence T l_hat u_hat hrec)
    hd_pos hDLT DeltaA_LU DeltaL DeltaU h20 h21

/-- **Theorem 9.14**, nonnegative-LU model-consuming `f(u)` bound. -/
theorem higham9_14_nonnegative_lu_source_f_bound_of_models
    (n : ℕ)
    (A L_hat U_hat : Fin n → Fin n → ℝ)
    (y_hat x_hat b : Fin n → ℝ)
    (u : ℝ) (hu : 0 ≤ u)
    (hNonneg : HasNonnegLUFactors n A L_hat U_hat)
    (DeltaA_LU DeltaL DeltaU : Fin n → Fin n → ℝ)
    (h20 : higham9_20_tridiag_lu_perturbation_model n A L_hat U_hat
      DeltaA_LU u)
    (h21 : higham9_21_tridiag_solve_perturbation_model n L_hat U_hat
      y_hat x_hat b DeltaL DeltaU u) :
    ∃ DeltaA : Fin n → Fin n → ℝ,
      (∀ i j, |DeltaA i j| ≤ higham9_14_f u * |A i j|) ∧
      (∀ i, ∑ j : Fin n, (A i j + DeltaA i j) * x_hat j = b i) := by
  obtain ⟨DeltaA, hDeltaA, hBackward⟩ :=
    higham9_14_source_f_bound_of_absLU_le_const_absA_and_9_20_9_21_models
      n A L_hat U_hat y_hat x_hat b 1 u hu
      (fun i j => by
        simpa [one_mul] using le_of_eq
          (higham9_12_nonneg_lu_optimal_growth n A L_hat U_hat
            hNonneg i j))
      DeltaA_LU DeltaL DeltaU h20 h21
  refine ⟨DeltaA, ?_, hBackward⟩
  intro i j
  simpa [one_mul] using hDeltaA i j

/-- **Theorem 9.14**, M-matrix LU model-consuming `f(u)` bound. -/
theorem higham9_14_mmatrix_lu_source_f_bound_of_models
    (n : ℕ)
    (A L_hat U_hat : Fin n → Fin n → ℝ)
    (y_hat x_hat b : Fin n → ℝ)
    (u : ℝ) (hu : 0 ≤ u)
    (hM : IsMMatrix n A)
    (hLU : LUFactSpec n A L_hat U_hat)
    (hL_nn : ∀ i k : Fin n, 0 ≤ L_hat i k)
    (hU_nn : ∀ k j : Fin n, 0 ≤ U_hat k j)
    (DeltaA_LU DeltaL DeltaU : Fin n → Fin n → ℝ)
    (h20 : higham9_20_tridiag_lu_perturbation_model n A L_hat U_hat
      DeltaA_LU u)
    (h21 : higham9_21_tridiag_solve_perturbation_model n L_hat U_hat
      y_hat x_hat b DeltaL DeltaU u) :
    ∃ DeltaA : Fin n → Fin n → ℝ,
      (∀ i j, |DeltaA i j| ≤ higham9_14_f u * |A i j|) ∧
      (∀ i, ∑ j : Fin n, (A i j + DeltaA i j) * x_hat j = b i) := by
  obtain ⟨DeltaA, hDeltaA, hBackward⟩ :=
    higham9_14_source_f_bound_of_absLU_le_const_absA_and_9_20_9_21_models
      n A L_hat U_hat y_hat x_hat b 1 u hu
      (fun i j => by
        simpa [one_mul] using le_of_eq
          (higham9_12_mmatrix_lu_optimal_growth n A L_hat U_hat hM hLU
            hL_nn hU_nn i j))
      DeltaA_LU DeltaL DeltaU h20 h21
  refine ⟨DeltaA, ?_, hBackward⟩
  intro i j
  simpa [one_mul] using hDeltaA i j

/-- **Theorem 9.14**, sign-equivalent optimal-growth model-consuming
`f(u)` bound. -/
theorem higham9_14_sign_equiv_source_f_bound_of_models
    (n : ℕ)
    (B L_B U_B : Fin n → Fin n → ℝ)
    (D₁ D₂ : Fin n → Fin n → ℝ)
    (hD₁ : IsSignDiag n D₁) (hD₂ : IsSignDiag n D₂)
    (hB_growth : ∀ i j : Fin n,
      ∑ k : Fin n, |L_B i k| * |U_B k j| = |B i j|)
    (A L_hat U_hat : Fin n → Fin n → ℝ)
    (hA_eq : ∀ i j : Fin n,
      A i j = ∑ k₁ : Fin n, D₁ i k₁ * (∑ k₂ : Fin n, B k₁ k₂ * D₂ k₂ j))
    (hL_abs : ∀ i k : Fin n, |L_hat i k| = |L_B i k|)
    (hU_abs : ∀ k j : Fin n, |U_hat k j| = |U_B k j|)
    (y_hat x_hat b : Fin n → ℝ)
    (u : ℝ) (hu : 0 ≤ u)
    (DeltaA_LU DeltaL DeltaU : Fin n → Fin n → ℝ)
    (h20 : higham9_20_tridiag_lu_perturbation_model n A L_hat U_hat
      DeltaA_LU u)
    (h21 : higham9_21_tridiag_solve_perturbation_model n L_hat U_hat
      y_hat x_hat b DeltaL DeltaU u) :
    ∃ DeltaA : Fin n → Fin n → ℝ,
      (∀ i j, |DeltaA i j| ≤ higham9_14_f u * |A i j|) ∧
      (∀ i, ∑ j : Fin n, (A i j + DeltaA i j) * x_hat j = b i) := by
  obtain ⟨DeltaA, hDeltaA, hBackward⟩ :=
    higham9_14_source_f_bound_of_absLU_le_const_absA_and_9_20_9_21_models
      n A L_hat U_hat y_hat x_hat b 1 u hu
      (fun i j => by
        simpa [one_mul] using le_of_eq
          (higham9_12_sign_equiv_optimal_growth n B L_B U_B D₁ D₂
            hD₁ hD₂ hB_growth A hA_eq L_hat U_hat hL_abs hU_abs i j))
      DeltaA_LU DeltaL DeltaU h20 h21
  refine ⟨DeltaA, ?_, hBackward⟩
  intro i j
  simpa [one_mul] using hDeltaA i j

/-- **Theorem 9.14**, SPD positive-`D L^T` model-consuming final bound
specialized to the natural `γ_n` coefficient. -/
theorem higham9_14_spd_tridiag_positive_DLT_source_h_bound_of_models_gamma
    (fp : FPModel) (n : ℕ)
    (A L_hat U_hat : Fin n → Fin n → ℝ)
    (d : Fin n → ℝ)
    (y_hat x_hat b : Fin n → ℝ)
    (hn : gammaValid fp n)
    (hγ_lt_one : gamma fp n < 1)
    (hStruct : IsTridiagLU n L_hat U_hat)
    (hLU_eq : ∀ i j : Fin n,
      ∑ k : Fin n, L_hat i k * U_hat k j = A i j)
    (hd_pos : ∀ k : Fin n, 0 < d k)
    (hDLT : ∀ k j : Fin n, U_hat k j = d k * L_hat j k)
    (DeltaA_LU DeltaL DeltaU : Fin n → Fin n → ℝ)
    (h20 : higham9_20_tridiag_lu_perturbation_model n A L_hat U_hat
      DeltaA_LU (gamma fp n))
    (h21 : higham9_21_tridiag_solve_perturbation_model n L_hat U_hat
      y_hat x_hat b DeltaL DeltaU (gamma fp n)) :
    ∃ DeltaA : Fin n → Fin n → ℝ,
      (∀ i j, |DeltaA i j| ≤
        higham9_14_h (gamma fp n) * |A i j|) ∧
      (∀ i, ∑ j : Fin n, (A i j + DeltaA i j) * x_hat j = b i) :=
  higham9_14_spd_tridiag_positive_DLT_source_h_bound_of_models
    n A L_hat U_hat d y_hat x_hat b (gamma fp n) (gamma_nonneg fp hn)
    hγ_lt_one hStruct hLU_eq hd_pos hDLT DeltaA_LU DeltaL DeltaU h20 h21

/-- **Theorem 9.14**, SPD positive-`D L^T` model-consuming final bound from
the tridiagonal recurrence, specialized to `γ_n`. -/
theorem higham9_14_spd_tridiag_positive_DLT_source_h_bound_of_recurrence_gamma
    (fp : FPModel) (n : ℕ)
    (T : higham9_18_TridiagData n)
    (l_hat u_hat d y_hat x_hat b : Fin n → ℝ)
    (hn : gammaValid fp n)
    (hγ_lt_one : gamma fp n < 1)
    (hrec : higham9_19_TridiagExactLURecurrence T l_hat u_hat)
    (hd_pos : ∀ k : Fin n, 0 < d k)
    (hDLT : ∀ k j : Fin n,
      tridiag_U_matrix u_hat T.c k j =
        d k * tridiag_L_matrix l_hat j k)
    (DeltaA_LU DeltaL DeltaU : Fin n → Fin n → ℝ)
    (h20 : higham9_20_tridiag_lu_perturbation_model n
      (higham9_18_tridiag_to_matrix T)
      (tridiag_L_matrix l_hat) (tridiag_U_matrix u_hat T.c)
      DeltaA_LU (gamma fp n))
    (h21 : higham9_21_tridiag_solve_perturbation_model n
      (tridiag_L_matrix l_hat) (tridiag_U_matrix u_hat T.c)
      y_hat x_hat b DeltaL DeltaU (gamma fp n)) :
    ∃ DeltaA : Fin n → Fin n → ℝ,
      (∀ i j,
        |DeltaA i j| ≤
          higham9_14_h (gamma fp n) *
            |higham9_18_tridiag_to_matrix T i j|) ∧
      (∀ i,
        ∑ j : Fin n,
          (higham9_18_tridiag_to_matrix T i j + DeltaA i j) * x_hat j =
        b i) :=
  higham9_14_spd_tridiag_positive_DLT_source_h_bound_of_recurrence
    n T l_hat u_hat d y_hat x_hat b (gamma fp n) (gamma_nonneg fp hn)
    hγ_lt_one hrec hd_pos hDLT DeltaA_LU DeltaL DeltaU h20 h21

/-- **Theorem 9.14**, nonnegative-LU model-consuming final bound specialized
to the natural `γ_n` coefficient. -/
theorem higham9_14_nonnegative_lu_source_h_bound_of_models_gamma
    (fp : FPModel) (n : ℕ)
    (A L_hat U_hat : Fin n → Fin n → ℝ)
    (y_hat x_hat b : Fin n → ℝ)
    (hn : gammaValid fp n)
    (hγ_lt_one : gamma fp n < 1)
    (hNonneg : HasNonnegLUFactors n A L_hat U_hat)
    (DeltaA_LU DeltaL DeltaU : Fin n → Fin n → ℝ)
    (h20 : higham9_20_tridiag_lu_perturbation_model n A L_hat U_hat
      DeltaA_LU (gamma fp n))
    (h21 : higham9_21_tridiag_solve_perturbation_model n L_hat U_hat
      y_hat x_hat b DeltaL DeltaU (gamma fp n)) :
    ∃ DeltaA : Fin n → Fin n → ℝ,
      (∀ i j, |DeltaA i j| ≤
        higham9_14_h (gamma fp n) * |A i j|) ∧
      (∀ i, ∑ j : Fin n, (A i j + DeltaA i j) * x_hat j = b i) :=
  higham9_14_nonnegative_lu_source_h_bound_of_models
    n A L_hat U_hat y_hat x_hat b (gamma fp n) (gamma_nonneg fp hn)
    hγ_lt_one hNonneg DeltaA_LU DeltaL DeltaU h20 h21

/-- **Theorem 9.14**, M-matrix LU model-consuming final bound specialized to
the natural `γ_n` coefficient. -/
theorem higham9_14_mmatrix_lu_source_h_bound_of_models_gamma
    (fp : FPModel) (n : ℕ)
    (A L_hat U_hat : Fin n → Fin n → ℝ)
    (y_hat x_hat b : Fin n → ℝ)
    (hn : gammaValid fp n)
    (hγ_lt_one : gamma fp n < 1)
    (hM : IsMMatrix n A)
    (hLU : LUFactSpec n A L_hat U_hat)
    (hL_nn : ∀ i k : Fin n, 0 ≤ L_hat i k)
    (hU_nn : ∀ k j : Fin n, 0 ≤ U_hat k j)
    (DeltaA_LU DeltaL DeltaU : Fin n → Fin n → ℝ)
    (h20 : higham9_20_tridiag_lu_perturbation_model n A L_hat U_hat
      DeltaA_LU (gamma fp n))
    (h21 : higham9_21_tridiag_solve_perturbation_model n L_hat U_hat
      y_hat x_hat b DeltaL DeltaU (gamma fp n)) :
    ∃ DeltaA : Fin n → Fin n → ℝ,
      (∀ i j, |DeltaA i j| ≤
        higham9_14_h (gamma fp n) * |A i j|) ∧
      (∀ i, ∑ j : Fin n, (A i j + DeltaA i j) * x_hat j = b i) :=
  higham9_14_mmatrix_lu_source_h_bound_of_models
    n A L_hat U_hat y_hat x_hat b (gamma fp n) (gamma_nonneg fp hn)
    hγ_lt_one hM hLU hL_nn hU_nn DeltaA_LU DeltaL DeltaU h20 h21

/-- **Theorem 9.14**, sign-equivalent optimal-growth model-consuming final
bound specialized to the natural `γ_n` coefficient. -/
theorem higham9_14_sign_equiv_source_h_bound_of_models_gamma
    (fp : FPModel) (n : ℕ)
    (B L_B U_B : Fin n → Fin n → ℝ)
    (D₁ D₂ : Fin n → Fin n → ℝ)
    (hD₁ : IsSignDiag n D₁) (hD₂ : IsSignDiag n D₂)
    (hB_growth : ∀ i j : Fin n,
      ∑ k : Fin n, |L_B i k| * |U_B k j| = |B i j|)
    (A L_hat U_hat : Fin n → Fin n → ℝ)
    (hA_eq : ∀ i j : Fin n,
      A i j = ∑ k₁ : Fin n, D₁ i k₁ * (∑ k₂ : Fin n, B k₁ k₂ * D₂ k₂ j))
    (hL_abs : ∀ i k : Fin n, |L_hat i k| = |L_B i k|)
    (hU_abs : ∀ k j : Fin n, |U_hat k j| = |U_B k j|)
    (y_hat x_hat b : Fin n → ℝ)
    (hn : gammaValid fp n)
    (hγ_lt_one : gamma fp n < 1)
    (DeltaA_LU DeltaL DeltaU : Fin n → Fin n → ℝ)
    (h20 : higham9_20_tridiag_lu_perturbation_model n A L_hat U_hat
      DeltaA_LU (gamma fp n))
    (h21 : higham9_21_tridiag_solve_perturbation_model n L_hat U_hat
      y_hat x_hat b DeltaL DeltaU (gamma fp n)) :
    ∃ DeltaA : Fin n → Fin n → ℝ,
      (∀ i j, |DeltaA i j| ≤
        higham9_14_h (gamma fp n) * |A i j|) ∧
      (∀ i, ∑ j : Fin n, (A i j + DeltaA i j) * x_hat j = b i) :=
  higham9_14_sign_equiv_source_h_bound_of_models
    n B L_B U_B D₁ D₂ hD₁ hD₂ hB_growth
    A L_hat U_hat hA_eq hL_abs hU_abs y_hat x_hat b
    (gamma fp n) (gamma_nonneg fp hn) hγ_lt_one
    DeltaA_LU DeltaL DeltaU h20 h21

/-- **Theorem 9.14**, SPD positive-`D L^T` model-consuming `f(γ_n)` bound. -/
theorem higham9_14_spd_tridiag_positive_DLT_source_f_bound_of_models_gamma
    (fp : FPModel) (n : ℕ)
    (A L_hat U_hat : Fin n → Fin n → ℝ)
    (d : Fin n → ℝ)
    (y_hat x_hat b : Fin n → ℝ)
    (hn : gammaValid fp n)
    (hStruct : IsTridiagLU n L_hat U_hat)
    (hLU_eq : ∀ i j : Fin n,
      ∑ k : Fin n, L_hat i k * U_hat k j = A i j)
    (hd_pos : ∀ k : Fin n, 0 < d k)
    (hDLT : ∀ k j : Fin n, U_hat k j = d k * L_hat j k)
    (DeltaA_LU DeltaL DeltaU : Fin n → Fin n → ℝ)
    (h20 : higham9_20_tridiag_lu_perturbation_model n A L_hat U_hat
      DeltaA_LU (gamma fp n))
    (h21 : higham9_21_tridiag_solve_perturbation_model n L_hat U_hat
      y_hat x_hat b DeltaL DeltaU (gamma fp n)) :
    ∃ DeltaA : Fin n → Fin n → ℝ,
      (∀ i j, |DeltaA i j| ≤
        higham9_14_f (gamma fp n) * |A i j|) ∧
      (∀ i, ∑ j : Fin n, (A i j + DeltaA i j) * x_hat j = b i) :=
  higham9_14_spd_tridiag_positive_DLT_source_f_bound_of_models
    n A L_hat U_hat d y_hat x_hat b (gamma fp n) (gamma_nonneg fp hn)
    hStruct hLU_eq hd_pos hDLT DeltaA_LU DeltaL DeltaU h20 h21

/-- **Theorem 9.14**, SPD positive-`D L^T` model-consuming `f(γ_n)` bound
from the explicit tridiagonal recurrence. -/
theorem higham9_14_spd_tridiag_positive_DLT_source_f_bound_of_recurrence_gamma
    (fp : FPModel) (n : ℕ)
    (T : higham9_18_TridiagData n)
    (l_hat u_hat d y_hat x_hat b : Fin n → ℝ)
    (hn : gammaValid fp n)
    (hrec : higham9_19_TridiagExactLURecurrence T l_hat u_hat)
    (hd_pos : ∀ k : Fin n, 0 < d k)
    (hDLT : ∀ k j : Fin n,
      tridiag_U_matrix u_hat T.c k j =
        d k * tridiag_L_matrix l_hat j k)
    (DeltaA_LU DeltaL DeltaU : Fin n → Fin n → ℝ)
    (h20 : higham9_20_tridiag_lu_perturbation_model n
      (higham9_18_tridiag_to_matrix T)
      (tridiag_L_matrix l_hat) (tridiag_U_matrix u_hat T.c)
      DeltaA_LU (gamma fp n))
    (h21 : higham9_21_tridiag_solve_perturbation_model n
      (tridiag_L_matrix l_hat) (tridiag_U_matrix u_hat T.c)
      y_hat x_hat b DeltaL DeltaU (gamma fp n)) :
    ∃ DeltaA : Fin n → Fin n → ℝ,
      (∀ i j,
        |DeltaA i j| ≤
          higham9_14_f (gamma fp n) *
            |higham9_18_tridiag_to_matrix T i j|) ∧
      (∀ i,
        ∑ j : Fin n,
          (higham9_18_tridiag_to_matrix T i j + DeltaA i j) * x_hat j =
        b i) :=
  higham9_14_spd_tridiag_positive_DLT_source_f_bound_of_recurrence
    n T l_hat u_hat d y_hat x_hat b (gamma fp n) (gamma_nonneg fp hn)
    hrec hd_pos hDLT DeltaA_LU DeltaL DeltaU h20 h21

/-- **Theorem 9.14**, nonnegative-LU model-consuming `f(γ_n)` bound. -/
theorem higham9_14_nonnegative_lu_source_f_bound_of_models_gamma
    (fp : FPModel) (n : ℕ)
    (A L_hat U_hat : Fin n → Fin n → ℝ)
    (y_hat x_hat b : Fin n → ℝ)
    (hn : gammaValid fp n)
    (hNonneg : HasNonnegLUFactors n A L_hat U_hat)
    (DeltaA_LU DeltaL DeltaU : Fin n → Fin n → ℝ)
    (h20 : higham9_20_tridiag_lu_perturbation_model n A L_hat U_hat
      DeltaA_LU (gamma fp n))
    (h21 : higham9_21_tridiag_solve_perturbation_model n L_hat U_hat
      y_hat x_hat b DeltaL DeltaU (gamma fp n)) :
    ∃ DeltaA : Fin n → Fin n → ℝ,
      (∀ i j, |DeltaA i j| ≤
        higham9_14_f (gamma fp n) * |A i j|) ∧
      (∀ i, ∑ j : Fin n, (A i j + DeltaA i j) * x_hat j = b i) :=
  higham9_14_nonnegative_lu_source_f_bound_of_models
    n A L_hat U_hat y_hat x_hat b (gamma fp n) (gamma_nonneg fp hn)
    hNonneg DeltaA_LU DeltaL DeltaU h20 h21

/-- **Theorem 9.14**, Matrix-facing nonnegative-LU model-consuming final
bound. -/
theorem higham9_14_matrix_nonnegative_lu_source_h_bound_of_models
    (n : ℕ)
    (A L_hat U_hat : Matrix (Fin n) (Fin n) ℝ)
    (y_hat x_hat b : Fin n → ℝ)
    (u : ℝ) (hu : 0 ≤ u) (hu_lt_one : u < 1)
    (hNonneg : HasNonnegLUFactors n A L_hat U_hat)
    (DeltaA_LU DeltaL DeltaU : Matrix (Fin n) (Fin n) ℝ)
    (h20 :
      (L_hat * U_hat = fun i j => A i j + DeltaA_LU i j) ∧
        ∀ i j : Fin n,
          |DeltaA_LU i j| ≤
            u * ∑ k : Fin n, |L_hat i k| * |U_hat k j|)
    (h21 :
      Matrix.mulVec (fun i j => L_hat i j + DeltaL i j) y_hat = b ∧
        (∀ i j : Fin n, |DeltaL i j| ≤ u * |L_hat i j|) ∧
        Matrix.mulVec (fun i j => U_hat i j + DeltaU i j) x_hat = y_hat ∧
        ∀ i j : Fin n,
          |DeltaU i j| ≤ (2 * u + u ^ 2) * |U_hat i j|) :
    ∃ DeltaA : Matrix (Fin n) (Fin n) ℝ,
      (∀ i j, |DeltaA i j| ≤ higham9_14_h u * |A i j|) ∧
      Matrix.mulVec (fun i j => A i j + DeltaA i j) x_hat = b :=
  higham9_14_matrix_source_h_bound_of_absLU_le_absA_and_matrix_models
    n A L_hat U_hat y_hat x_hat b u hu hu_lt_one
    (fun i j =>
      le_of_eq
        (higham9_12_nonneg_lu_optimal_growth n A L_hat U_hat
          hNonneg i j))
    DeltaA_LU DeltaL DeltaU h20 h21

/-- **Theorem 9.14**, Matrix-facing nonnegative-LU model-consuming
`f(u)` bound. -/
theorem higham9_14_matrix_nonnegative_lu_source_f_bound_of_models
    (n : ℕ)
    (A L_hat U_hat : Matrix (Fin n) (Fin n) ℝ)
    (y_hat x_hat b : Fin n → ℝ)
    (u : ℝ) (hu : 0 ≤ u)
    (hNonneg : HasNonnegLUFactors n A L_hat U_hat)
    (DeltaA_LU DeltaL DeltaU : Matrix (Fin n) (Fin n) ℝ)
    (h20 :
      (L_hat * U_hat = fun i j => A i j + DeltaA_LU i j) ∧
        ∀ i j : Fin n,
          |DeltaA_LU i j| ≤
            u * ∑ k : Fin n, |L_hat i k| * |U_hat k j|)
    (h21 :
      Matrix.mulVec (fun i j => L_hat i j + DeltaL i j) y_hat = b ∧
        (∀ i j : Fin n, |DeltaL i j| ≤ u * |L_hat i j|) ∧
        Matrix.mulVec (fun i j => U_hat i j + DeltaU i j) x_hat = y_hat ∧
        ∀ i j : Fin n,
          |DeltaU i j| ≤ (2 * u + u ^ 2) * |U_hat i j|) :
    ∃ DeltaA : Matrix (Fin n) (Fin n) ℝ,
      (∀ i j, |DeltaA i j| ≤ higham9_14_f u * |A i j|) ∧
      Matrix.mulVec (fun i j => A i j + DeltaA i j) x_hat = b :=
  higham9_14_matrix_source_f_bound_of_absLU_le_absA_and_matrix_models
    n A L_hat U_hat y_hat x_hat b u hu
    (fun i j =>
      le_of_eq
        (higham9_12_nonneg_lu_optimal_growth n A L_hat U_hat
          hNonneg i j))
    DeltaA_LU DeltaL DeltaU h20 h21

/-- **Theorem 9.14**, Matrix-facing nonnegative-LU model-consuming final
bound specialized to the natural `γ_n` coefficient. -/
theorem higham9_14_matrix_nonnegative_lu_source_h_bound_of_models_gamma
    (fp : FPModel) (n : ℕ)
    (A L_hat U_hat : Matrix (Fin n) (Fin n) ℝ)
    (y_hat x_hat b : Fin n → ℝ)
    (hn : gammaValid fp n)
    (hγ_lt_one : gamma fp n < 1)
    (hNonneg : HasNonnegLUFactors n A L_hat U_hat)
    (DeltaA_LU DeltaL DeltaU : Matrix (Fin n) (Fin n) ℝ)
    (h20 :
      (L_hat * U_hat = fun i j => A i j + DeltaA_LU i j) ∧
        ∀ i j : Fin n,
          |DeltaA_LU i j| ≤
            gamma fp n * ∑ k : Fin n, |L_hat i k| * |U_hat k j|)
    (h21 :
      Matrix.mulVec (fun i j => L_hat i j + DeltaL i j) y_hat = b ∧
        (∀ i j : Fin n, |DeltaL i j| ≤ gamma fp n * |L_hat i j|) ∧
        Matrix.mulVec (fun i j => U_hat i j + DeltaU i j) x_hat = y_hat ∧
        ∀ i j : Fin n,
          |DeltaU i j| ≤
            (2 * gamma fp n + (gamma fp n) ^ 2) * |U_hat i j|) :
    ∃ DeltaA : Matrix (Fin n) (Fin n) ℝ,
      (∀ i j, |DeltaA i j| ≤
        higham9_14_h (gamma fp n) * |A i j|) ∧
      Matrix.mulVec (fun i j => A i j + DeltaA i j) x_hat = b :=
  higham9_14_matrix_nonnegative_lu_source_h_bound_of_models
    n A L_hat U_hat y_hat x_hat b (gamma fp n) (gamma_nonneg fp hn)
    hγ_lt_one hNonneg DeltaA_LU DeltaL DeltaU h20 h21

/-- **Theorem 9.14**, Matrix-facing nonnegative-LU model-consuming
`f(γ_n)` bound. -/
theorem higham9_14_matrix_nonnegative_lu_source_f_bound_of_models_gamma
    (fp : FPModel) (n : ℕ)
    (A L_hat U_hat : Matrix (Fin n) (Fin n) ℝ)
    (y_hat x_hat b : Fin n → ℝ)
    (hn : gammaValid fp n)
    (hNonneg : HasNonnegLUFactors n A L_hat U_hat)
    (DeltaA_LU DeltaL DeltaU : Matrix (Fin n) (Fin n) ℝ)
    (h20 :
      (L_hat * U_hat = fun i j => A i j + DeltaA_LU i j) ∧
        ∀ i j : Fin n,
          |DeltaA_LU i j| ≤
            gamma fp n * ∑ k : Fin n, |L_hat i k| * |U_hat k j|)
    (h21 :
      Matrix.mulVec (fun i j => L_hat i j + DeltaL i j) y_hat = b ∧
        (∀ i j : Fin n, |DeltaL i j| ≤ gamma fp n * |L_hat i j|) ∧
        Matrix.mulVec (fun i j => U_hat i j + DeltaU i j) x_hat = y_hat ∧
        ∀ i j : Fin n,
          |DeltaU i j| ≤
            (2 * gamma fp n + (gamma fp n) ^ 2) * |U_hat i j|) :
    ∃ DeltaA : Matrix (Fin n) (Fin n) ℝ,
      (∀ i j, |DeltaA i j| ≤
        higham9_14_f (gamma fp n) * |A i j|) ∧
      Matrix.mulVec (fun i j => A i j + DeltaA i j) x_hat = b :=
  higham9_14_matrix_nonnegative_lu_source_f_bound_of_models
    n A L_hat U_hat y_hat x_hat b (gamma fp n) (gamma_nonneg fp hn)
    hNonneg DeltaA_LU DeltaL DeltaU h20 h21

/-- **Theorem 9.14**, Matrix-facing M-matrix LU model-consuming final
bound. -/
theorem higham9_14_matrix_mmatrix_lu_source_h_bound_of_models
    (n : ℕ)
    (A L_hat U_hat : Matrix (Fin n) (Fin n) ℝ)
    (y_hat x_hat b : Fin n → ℝ)
    (u : ℝ) (hu : 0 ≤ u) (hu_lt_one : u < 1)
    (hM : IsMMatrix n A)
    (hLU : LUFactSpec n A L_hat U_hat)
    (hL_nn : ∀ i k : Fin n, 0 ≤ L_hat i k)
    (hU_nn : ∀ k j : Fin n, 0 ≤ U_hat k j)
    (DeltaA_LU DeltaL DeltaU : Matrix (Fin n) (Fin n) ℝ)
    (h20 :
      (L_hat * U_hat = fun i j => A i j + DeltaA_LU i j) ∧
        ∀ i j : Fin n,
          |DeltaA_LU i j| ≤
            u * ∑ k : Fin n, |L_hat i k| * |U_hat k j|)
    (h21 :
      Matrix.mulVec (fun i j => L_hat i j + DeltaL i j) y_hat = b ∧
        (∀ i j : Fin n, |DeltaL i j| ≤ u * |L_hat i j|) ∧
        Matrix.mulVec (fun i j => U_hat i j + DeltaU i j) x_hat = y_hat ∧
        ∀ i j : Fin n,
          |DeltaU i j| ≤ (2 * u + u ^ 2) * |U_hat i j|) :
    ∃ DeltaA : Matrix (Fin n) (Fin n) ℝ,
      (∀ i j, |DeltaA i j| ≤ higham9_14_h u * |A i j|) ∧
      Matrix.mulVec (fun i j => A i j + DeltaA i j) x_hat = b :=
  higham9_14_matrix_source_h_bound_of_absLU_le_absA_and_matrix_models
    n A L_hat U_hat y_hat x_hat b u hu hu_lt_one
    (fun i j =>
      le_of_eq
        (higham9_12_mmatrix_lu_optimal_growth n A L_hat U_hat
          hM hLU hL_nn hU_nn i j))
    DeltaA_LU DeltaL DeltaU h20 h21

/-- **Theorem 9.14**, Matrix-facing M-matrix LU model-consuming
`f(u)` bound. -/
theorem higham9_14_matrix_mmatrix_lu_source_f_bound_of_models
    (n : ℕ)
    (A L_hat U_hat : Matrix (Fin n) (Fin n) ℝ)
    (y_hat x_hat b : Fin n → ℝ)
    (u : ℝ) (hu : 0 ≤ u)
    (hM : IsMMatrix n A)
    (hLU : LUFactSpec n A L_hat U_hat)
    (hL_nn : ∀ i k : Fin n, 0 ≤ L_hat i k)
    (hU_nn : ∀ k j : Fin n, 0 ≤ U_hat k j)
    (DeltaA_LU DeltaL DeltaU : Matrix (Fin n) (Fin n) ℝ)
    (h20 :
      (L_hat * U_hat = fun i j => A i j + DeltaA_LU i j) ∧
        ∀ i j : Fin n,
          |DeltaA_LU i j| ≤
            u * ∑ k : Fin n, |L_hat i k| * |U_hat k j|)
    (h21 :
      Matrix.mulVec (fun i j => L_hat i j + DeltaL i j) y_hat = b ∧
        (∀ i j : Fin n, |DeltaL i j| ≤ u * |L_hat i j|) ∧
        Matrix.mulVec (fun i j => U_hat i j + DeltaU i j) x_hat = y_hat ∧
        ∀ i j : Fin n,
          |DeltaU i j| ≤ (2 * u + u ^ 2) * |U_hat i j|) :
    ∃ DeltaA : Matrix (Fin n) (Fin n) ℝ,
      (∀ i j, |DeltaA i j| ≤ higham9_14_f u * |A i j|) ∧
      Matrix.mulVec (fun i j => A i j + DeltaA i j) x_hat = b :=
  higham9_14_matrix_source_f_bound_of_absLU_le_absA_and_matrix_models
    n A L_hat U_hat y_hat x_hat b u hu
    (fun i j =>
      le_of_eq
        (higham9_12_mmatrix_lu_optimal_growth n A L_hat U_hat
          hM hLU hL_nn hU_nn i j))
    DeltaA_LU DeltaL DeltaU h20 h21

/-- **Theorem 9.14**, Matrix-facing M-matrix LU model-consuming final bound
specialized to the natural `γ_n` coefficient. -/
theorem higham9_14_matrix_mmatrix_lu_source_h_bound_of_models_gamma
    (fp : FPModel) (n : ℕ)
    (A L_hat U_hat : Matrix (Fin n) (Fin n) ℝ)
    (y_hat x_hat b : Fin n → ℝ)
    (hn : gammaValid fp n)
    (hγ_lt_one : gamma fp n < 1)
    (hM : IsMMatrix n A)
    (hLU : LUFactSpec n A L_hat U_hat)
    (hL_nn : ∀ i k : Fin n, 0 ≤ L_hat i k)
    (hU_nn : ∀ k j : Fin n, 0 ≤ U_hat k j)
    (DeltaA_LU DeltaL DeltaU : Matrix (Fin n) (Fin n) ℝ)
    (h20 :
      (L_hat * U_hat = fun i j => A i j + DeltaA_LU i j) ∧
        ∀ i j : Fin n,
          |DeltaA_LU i j| ≤
            gamma fp n * ∑ k : Fin n, |L_hat i k| * |U_hat k j|)
    (h21 :
      Matrix.mulVec (fun i j => L_hat i j + DeltaL i j) y_hat = b ∧
        (∀ i j : Fin n, |DeltaL i j| ≤ gamma fp n * |L_hat i j|) ∧
        Matrix.mulVec (fun i j => U_hat i j + DeltaU i j) x_hat = y_hat ∧
        ∀ i j : Fin n,
          |DeltaU i j| ≤
            (2 * gamma fp n + (gamma fp n) ^ 2) * |U_hat i j|) :
    ∃ DeltaA : Matrix (Fin n) (Fin n) ℝ,
      (∀ i j, |DeltaA i j| ≤
        higham9_14_h (gamma fp n) * |A i j|) ∧
      Matrix.mulVec (fun i j => A i j + DeltaA i j) x_hat = b :=
  higham9_14_matrix_mmatrix_lu_source_h_bound_of_models
    n A L_hat U_hat y_hat x_hat b (gamma fp n) (gamma_nonneg fp hn)
    hγ_lt_one hM hLU hL_nn hU_nn DeltaA_LU DeltaL DeltaU h20 h21

/-- **Theorem 9.14**, Matrix-facing M-matrix LU model-consuming
`f(γ_n)` bound. -/
theorem higham9_14_matrix_mmatrix_lu_source_f_bound_of_models_gamma
    (fp : FPModel) (n : ℕ)
    (A L_hat U_hat : Matrix (Fin n) (Fin n) ℝ)
    (y_hat x_hat b : Fin n → ℝ)
    (hn : gammaValid fp n)
    (hM : IsMMatrix n A)
    (hLU : LUFactSpec n A L_hat U_hat)
    (hL_nn : ∀ i k : Fin n, 0 ≤ L_hat i k)
    (hU_nn : ∀ k j : Fin n, 0 ≤ U_hat k j)
    (DeltaA_LU DeltaL DeltaU : Matrix (Fin n) (Fin n) ℝ)
    (h20 :
      (L_hat * U_hat = fun i j => A i j + DeltaA_LU i j) ∧
        ∀ i j : Fin n,
          |DeltaA_LU i j| ≤
            gamma fp n * ∑ k : Fin n, |L_hat i k| * |U_hat k j|)
    (h21 :
      Matrix.mulVec (fun i j => L_hat i j + DeltaL i j) y_hat = b ∧
        (∀ i j : Fin n, |DeltaL i j| ≤ gamma fp n * |L_hat i j|) ∧
        Matrix.mulVec (fun i j => U_hat i j + DeltaU i j) x_hat = y_hat ∧
        ∀ i j : Fin n,
          |DeltaU i j| ≤
            (2 * gamma fp n + (gamma fp n) ^ 2) * |U_hat i j|) :
    ∃ DeltaA : Matrix (Fin n) (Fin n) ℝ,
      (∀ i j, |DeltaA i j| ≤
        higham9_14_f (gamma fp n) * |A i j|) ∧
      Matrix.mulVec (fun i j => A i j + DeltaA i j) x_hat = b :=
  higham9_14_matrix_mmatrix_lu_source_f_bound_of_models
    n A L_hat U_hat y_hat x_hat b (gamma fp n) (gamma_nonneg fp hn)
    hM hLU hL_nn hU_nn DeltaA_LU DeltaL DeltaU h20 h21

/-- **Theorem 9.14**, Matrix-facing sign-equivalent model-consuming final
bound from the source sign-equivalence predicate. -/
theorem higham9_14_matrix_sign_equiv_source_h_bound_of_IsSignEquiv_models
    (n : ℕ)
    (A B L_B U_B L_hat U_hat : Matrix (Fin n) (Fin n) ℝ)
    (hAB : IsSignEquiv n A B)
    (hB_growth : ∀ i j : Fin n,
      ∑ k : Fin n, |L_B i k| * |U_B k j| = |B i j|)
    (hL_abs : ∀ i k : Fin n, |L_hat i k| = |L_B i k|)
    (hU_abs : ∀ k j : Fin n, |U_hat k j| = |U_B k j|)
    (y_hat x_hat b : Fin n → ℝ)
    (u : ℝ) (hu : 0 ≤ u) (hu_lt_one : u < 1)
    (DeltaA_LU DeltaL DeltaU : Matrix (Fin n) (Fin n) ℝ)
    (h20 :
      (L_hat * U_hat = fun i j => A i j + DeltaA_LU i j) ∧
        ∀ i j : Fin n,
          |DeltaA_LU i j| ≤
            u * ∑ k : Fin n, |L_hat i k| * |U_hat k j|)
    (h21 :
      Matrix.mulVec (fun i j => L_hat i j + DeltaL i j) y_hat = b ∧
        (∀ i j : Fin n, |DeltaL i j| ≤ u * |L_hat i j|) ∧
        Matrix.mulVec (fun i j => U_hat i j + DeltaU i j) x_hat = y_hat ∧
        ∀ i j : Fin n,
          |DeltaU i j| ≤ (2 * u + u ^ 2) * |U_hat i j|) :
    ∃ DeltaA : Matrix (Fin n) (Fin n) ℝ,
      (∀ i j, |DeltaA i j| ≤ higham9_14_h u * |A i j|) ∧
      Matrix.mulVec (fun i j => A i j + DeltaA i j) x_hat = b :=
  higham9_14_matrix_source_h_bound_of_absLU_le_absA_and_matrix_models
    n A L_hat U_hat y_hat x_hat b u hu hu_lt_one
    (fun i j =>
      le_of_eq
        (higham9_12_sign_equiv_optimal_growth_of_IsSignEquiv
          n A B L_B U_B L_hat U_hat hAB hB_growth hL_abs hU_abs i j))
    DeltaA_LU DeltaL DeltaU h20 h21

/-- **Theorem 9.14**, Matrix-facing sign-equivalent model-consuming
`f(u)` bound from the source sign-equivalence predicate. -/
theorem higham9_14_matrix_sign_equiv_source_f_bound_of_IsSignEquiv_models
    (n : ℕ)
    (A B L_B U_B L_hat U_hat : Matrix (Fin n) (Fin n) ℝ)
    (hAB : IsSignEquiv n A B)
    (hB_growth : ∀ i j : Fin n,
      ∑ k : Fin n, |L_B i k| * |U_B k j| = |B i j|)
    (hL_abs : ∀ i k : Fin n, |L_hat i k| = |L_B i k|)
    (hU_abs : ∀ k j : Fin n, |U_hat k j| = |U_B k j|)
    (y_hat x_hat b : Fin n → ℝ)
    (u : ℝ) (hu : 0 ≤ u)
    (DeltaA_LU DeltaL DeltaU : Matrix (Fin n) (Fin n) ℝ)
    (h20 :
      (L_hat * U_hat = fun i j => A i j + DeltaA_LU i j) ∧
        ∀ i j : Fin n,
          |DeltaA_LU i j| ≤
            u * ∑ k : Fin n, |L_hat i k| * |U_hat k j|)
    (h21 :
      Matrix.mulVec (fun i j => L_hat i j + DeltaL i j) y_hat = b ∧
        (∀ i j : Fin n, |DeltaL i j| ≤ u * |L_hat i j|) ∧
        Matrix.mulVec (fun i j => U_hat i j + DeltaU i j) x_hat = y_hat ∧
        ∀ i j : Fin n,
          |DeltaU i j| ≤ (2 * u + u ^ 2) * |U_hat i j|) :
    ∃ DeltaA : Matrix (Fin n) (Fin n) ℝ,
      (∀ i j, |DeltaA i j| ≤ higham9_14_f u * |A i j|) ∧
      Matrix.mulVec (fun i j => A i j + DeltaA i j) x_hat = b :=
  higham9_14_matrix_source_f_bound_of_absLU_le_absA_and_matrix_models
    n A L_hat U_hat y_hat x_hat b u hu
    (fun i j =>
      le_of_eq
        (higham9_12_sign_equiv_optimal_growth_of_IsSignEquiv
          n A B L_B U_B L_hat U_hat hAB hB_growth hL_abs hU_abs i j))
    DeltaA_LU DeltaL DeltaU h20 h21

/-- **Theorem 9.14**, Matrix-facing sign-equivalent model-consuming final
bound specialized to the natural `γ_n` coefficient. -/
theorem higham9_14_matrix_sign_equiv_source_h_bound_of_IsSignEquiv_models_gamma
    (fp : FPModel) (n : ℕ)
    (A B L_B U_B L_hat U_hat : Matrix (Fin n) (Fin n) ℝ)
    (hAB : IsSignEquiv n A B)
    (hB_growth : ∀ i j : Fin n,
      ∑ k : Fin n, |L_B i k| * |U_B k j| = |B i j|)
    (hL_abs : ∀ i k : Fin n, |L_hat i k| = |L_B i k|)
    (hU_abs : ∀ k j : Fin n, |U_hat k j| = |U_B k j|)
    (y_hat x_hat b : Fin n → ℝ)
    (hn : gammaValid fp n)
    (hγ_lt_one : gamma fp n < 1)
    (DeltaA_LU DeltaL DeltaU : Matrix (Fin n) (Fin n) ℝ)
    (h20 :
      (L_hat * U_hat = fun i j => A i j + DeltaA_LU i j) ∧
        ∀ i j : Fin n,
          |DeltaA_LU i j| ≤
            gamma fp n * ∑ k : Fin n, |L_hat i k| * |U_hat k j|)
    (h21 :
      Matrix.mulVec (fun i j => L_hat i j + DeltaL i j) y_hat = b ∧
        (∀ i j : Fin n, |DeltaL i j| ≤ gamma fp n * |L_hat i j|) ∧
        Matrix.mulVec (fun i j => U_hat i j + DeltaU i j) x_hat = y_hat ∧
        ∀ i j : Fin n,
          |DeltaU i j| ≤
            (2 * gamma fp n + (gamma fp n) ^ 2) * |U_hat i j|) :
    ∃ DeltaA : Matrix (Fin n) (Fin n) ℝ,
      (∀ i j, |DeltaA i j| ≤
        higham9_14_h (gamma fp n) * |A i j|) ∧
      Matrix.mulVec (fun i j => A i j + DeltaA i j) x_hat = b :=
  higham9_14_matrix_sign_equiv_source_h_bound_of_IsSignEquiv_models
    n A B L_B U_B L_hat U_hat hAB hB_growth hL_abs hU_abs
    y_hat x_hat b (gamma fp n) (gamma_nonneg fp hn) hγ_lt_one
    DeltaA_LU DeltaL DeltaU h20 h21

/-- **Theorem 9.14**, Matrix-facing sign-equivalent model-consuming
`f(γ_n)` bound. -/
theorem higham9_14_matrix_sign_equiv_source_f_bound_of_IsSignEquiv_models_gamma
    (fp : FPModel) (n : ℕ)
    (A B L_B U_B L_hat U_hat : Matrix (Fin n) (Fin n) ℝ)
    (hAB : IsSignEquiv n A B)
    (hB_growth : ∀ i j : Fin n,
      ∑ k : Fin n, |L_B i k| * |U_B k j| = |B i j|)
    (hL_abs : ∀ i k : Fin n, |L_hat i k| = |L_B i k|)
    (hU_abs : ∀ k j : Fin n, |U_hat k j| = |U_B k j|)
    (y_hat x_hat b : Fin n → ℝ)
    (hn : gammaValid fp n)
    (DeltaA_LU DeltaL DeltaU : Matrix (Fin n) (Fin n) ℝ)
    (h20 :
      (L_hat * U_hat = fun i j => A i j + DeltaA_LU i j) ∧
        ∀ i j : Fin n,
          |DeltaA_LU i j| ≤
            gamma fp n * ∑ k : Fin n, |L_hat i k| * |U_hat k j|)
    (h21 :
      Matrix.mulVec (fun i j => L_hat i j + DeltaL i j) y_hat = b ∧
        (∀ i j : Fin n, |DeltaL i j| ≤ gamma fp n * |L_hat i j|) ∧
        Matrix.mulVec (fun i j => U_hat i j + DeltaU i j) x_hat = y_hat ∧
        ∀ i j : Fin n,
          |DeltaU i j| ≤
            (2 * gamma fp n + (gamma fp n) ^ 2) * |U_hat i j|) :
    ∃ DeltaA : Matrix (Fin n) (Fin n) ℝ,
      (∀ i j, |DeltaA i j| ≤
        higham9_14_f (gamma fp n) * |A i j|) ∧
      Matrix.mulVec (fun i j => A i j + DeltaA i j) x_hat = b :=
  higham9_14_matrix_sign_equiv_source_f_bound_of_IsSignEquiv_models
    n A B L_B U_B L_hat U_hat hAB hB_growth hL_abs hU_abs
    y_hat x_hat b (gamma fp n) (gamma_nonneg fp hn)
    DeltaA_LU DeltaL DeltaU h20 h21

/-- **Theorem 9.14**, M-matrix LU model-consuming `f(γ_n)` bound. -/
theorem higham9_14_mmatrix_lu_source_f_bound_of_models_gamma
    (fp : FPModel) (n : ℕ)
    (A L_hat U_hat : Fin n → Fin n → ℝ)
    (y_hat x_hat b : Fin n → ℝ)
    (hn : gammaValid fp n)
    (hM : IsMMatrix n A)
    (hLU : LUFactSpec n A L_hat U_hat)
    (hL_nn : ∀ i k : Fin n, 0 ≤ L_hat i k)
    (hU_nn : ∀ k j : Fin n, 0 ≤ U_hat k j)
    (DeltaA_LU DeltaL DeltaU : Fin n → Fin n → ℝ)
    (h20 : higham9_20_tridiag_lu_perturbation_model n A L_hat U_hat
      DeltaA_LU (gamma fp n))
    (h21 : higham9_21_tridiag_solve_perturbation_model n L_hat U_hat
      y_hat x_hat b DeltaL DeltaU (gamma fp n)) :
    ∃ DeltaA : Fin n → Fin n → ℝ,
      (∀ i j, |DeltaA i j| ≤
        higham9_14_f (gamma fp n) * |A i j|) ∧
      (∀ i, ∑ j : Fin n, (A i j + DeltaA i j) * x_hat j = b i) :=
  higham9_14_mmatrix_lu_source_f_bound_of_models
    n A L_hat U_hat y_hat x_hat b (gamma fp n) (gamma_nonneg fp hn)
    hM hLU hL_nn hU_nn DeltaA_LU DeltaL DeltaU h20 h21

/-- **Theorem 9.14**, sign-equivalent optimal-growth model-consuming
`f(γ_n)` bound. -/
theorem higham9_14_sign_equiv_source_f_bound_of_models_gamma
    (fp : FPModel) (n : ℕ)
    (B L_B U_B : Fin n → Fin n → ℝ)
    (D₁ D₂ : Fin n → Fin n → ℝ)
    (hD₁ : IsSignDiag n D₁) (hD₂ : IsSignDiag n D₂)
    (hB_growth : ∀ i j : Fin n,
      ∑ k : Fin n, |L_B i k| * |U_B k j| = |B i j|)
    (A L_hat U_hat : Fin n → Fin n → ℝ)
    (hA_eq : ∀ i j : Fin n,
      A i j = ∑ k₁ : Fin n, D₁ i k₁ * (∑ k₂ : Fin n, B k₁ k₂ * D₂ k₂ j))
    (hL_abs : ∀ i k : Fin n, |L_hat i k| = |L_B i k|)
    (hU_abs : ∀ k j : Fin n, |U_hat k j| = |U_B k j|)
    (y_hat x_hat b : Fin n → ℝ)
    (hn : gammaValid fp n)
    (DeltaA_LU DeltaL DeltaU : Fin n → Fin n → ℝ)
    (h20 : higham9_20_tridiag_lu_perturbation_model n A L_hat U_hat
      DeltaA_LU (gamma fp n))
    (h21 : higham9_21_tridiag_solve_perturbation_model n L_hat U_hat
      y_hat x_hat b DeltaL DeltaU (gamma fp n)) :
    ∃ DeltaA : Fin n → Fin n → ℝ,
      (∀ i j, |DeltaA i j| ≤
        higham9_14_f (gamma fp n) * |A i j|) ∧
      (∀ i, ∑ j : Fin n, (A i j + DeltaA i j) * x_hat j = b i) :=
  higham9_14_sign_equiv_source_f_bound_of_models
    n B L_B U_B D₁ D₂ hD₁ hD₂ hB_growth
    A L_hat U_hat hA_eq hL_abs hU_abs y_hat x_hat b
    (gamma fp n) (gamma_nonneg fp hn) DeltaA_LU DeltaL DeltaU h20 h21

/-- **Theorem 9.14**, SPD positive-`D L^T` exact-factor package with actual
triangular solves.

The visible tridiagonal `D L^T` certificate gives exact LU factors and
`|Lhat||Uhat| = |A|`; exact factors give the zero-coefficient LU model, and the
actual triangular solves supply the solve model. -/
theorem higham9_14_spd_tridiag_positive_DLT_source_f_bound_actual_triangular_solves
    (fp : FPModel) (n : ℕ)
    (A L_hat U_hat : Fin n → Fin n → ℝ)
    (d : Fin n → ℝ)
    (b : Fin n → ℝ)
    (u : ℝ) (hu : 0 ≤ u)
    (hn : gammaValid fp n)
    (hγ_le_u : gamma fp n ≤ u)
    (hStruct : IsTridiagLU n L_hat U_hat)
    (hLU_eq : ∀ i j : Fin n,
      ∑ k : Fin n, L_hat i k * U_hat k j = A i j)
    (hdetA : Matrix.det (Matrix.of A : Matrix (Fin n) (Fin n) ℝ) ≠ 0)
    (hd_pos : ∀ k : Fin n, 0 < d k)
    (hDLT : ∀ k j : Fin n, U_hat k j = d k * L_hat j k) :
    let y_hat := fl_forwardSub fp n L_hat b
    let x_hat := fl_backSub fp n U_hat y_hat
    ∃ DeltaA : Fin n → Fin n → ℝ,
      (∀ i j, |DeltaA i j| ≤ higham9_14_f u * |A i j|) ∧
      (∀ i, ∑ j : Fin n, (A i j + DeltaA i j) * x_hat j = b i) := by
  let hLU : LUFactSpec n A L_hat U_hat :=
    { L_diag := hStruct.L_diag
      L_upper_zero := hStruct.L_upper_zero
      U_lower_zero := hStruct.U_lower_zero
      product_eq := hLU_eq }
  obtain ⟨DeltaA, hDeltaA, hBackward⟩ :=
    higham9_14_source_f_bound_of_LUFactSpec_fl_triangular_solves_gamma_le
      fp n A L_hat U_hat b 1 u hu hn hLU hγ_le_u
      (hLU.det_ne_zero_iff_U_diag_ne_zero.mp hdetA)
      (fun i j => by
        simpa [one_mul] using le_of_eq
          (higham9_12_spd_tridiag_absLU_eq_of_positive_DLT
            A L_hat U_hat d hStruct hLU_eq hd_pos hDLT i j))
  refine ⟨DeltaA, ?_, hBackward⟩
  intro i j
  simpa [one_mul] using hDeltaA i j

/-- **Theorem 9.14**, SPD positive-`D L^T` exact-factor package with actual
triangular solves, deriving nonsingularity from the source SPD hypothesis.

This is the source-facing variant of
`higham9_14_spd_tridiag_positive_DLT_source_f_bound_actual_triangular_solves`:
the determinant side condition is discharged by the repository SPD
nonsingularity theorem.  The positive-`D L^T` exact-factor certificate remains
an explicit hypothesis. -/
theorem higham9_14_spd_tridiag_positive_DLT_source_f_bound_actual_triangular_solves_of_spd
    (fp : FPModel) (n : ℕ)
    (A L_hat U_hat : Fin n → Fin n → ℝ)
    (d : Fin n → ℝ)
    (b : Fin n → ℝ)
    (u : ℝ) (hu : 0 ≤ u)
    (hn : gammaValid fp n)
    (hγ_le_u : gamma fp n ≤ u)
    (hSPD : IsSymPosDef n A)
    (hStruct : IsTridiagLU n L_hat U_hat)
    (hLU_eq : ∀ i j : Fin n,
      ∑ k : Fin n, L_hat i k * U_hat k j = A i j)
    (hd_pos : ∀ k : Fin n, 0 < d k)
    (hDLT : ∀ k j : Fin n, U_hat k j = d k * L_hat j k) :
    let y_hat := fl_forwardSub fp n L_hat b
    let x_hat := fl_backSub fp n U_hat y_hat
    ∃ DeltaA : Fin n → Fin n → ℝ,
      (∀ i j, |DeltaA i j| ≤ higham9_14_f u * |A i j|) ∧
      (∀ i, ∑ j : Fin n, (A i j + DeltaA i j) * x_hat j = b i) :=
  higham9_14_spd_tridiag_positive_DLT_source_f_bound_actual_triangular_solves
    fp n A L_hat U_hat d b u hu hn hγ_le_u hStruct hLU_eq
    (by simpa using isSymPosDef_det_ne_zero A hSPD)
    hd_pos hDLT

/-- **Theorem 9.14**, SPD positive-`D L^T` exact-recurrence package with
actual triangular solves.

The explicit tridiagonal recurrence supplies exact LU factors for the
source-data matrix.  Together with a visible positive-`D L^T` certificate and
nonsingularity, the actual forward/back substitution routines satisfy the
standard `f(u)|A|` componentwise source bound. -/
theorem higham9_14_spd_tridiag_positive_DLT_source_f_bound_actual_triangular_solves_of_recurrence
    (fp : FPModel) (n : ℕ)
    (T : higham9_18_TridiagData n)
    (l_hat u_hat d b : Fin n → ℝ)
    (u : ℝ) (hu : 0 ≤ u)
    (hn : gammaValid fp n)
    (hγ_le_u : gamma fp n ≤ u)
    (hrec : higham9_19_TridiagExactLURecurrence T l_hat u_hat)
    (hdetA :
      Matrix.det
        (Matrix.of (higham9_18_tridiag_to_matrix T) :
          Matrix (Fin n) (Fin n) ℝ) ≠ 0)
    (hd_pos : ∀ k : Fin n, 0 < d k)
    (hDLT : ∀ k j : Fin n,
      tridiag_U_matrix u_hat T.c k j =
        d k * tridiag_L_matrix l_hat j k) :
    let y_hat := fl_forwardSub fp n (tridiag_L_matrix l_hat) b
    let x_hat := fl_backSub fp n (tridiag_U_matrix u_hat T.c) y_hat
    ∃ DeltaA : Fin n → Fin n → ℝ,
      (∀ i j,
        |DeltaA i j| ≤
          higham9_14_f u * |higham9_18_tridiag_to_matrix T i j|) ∧
      (∀ i,
        ∑ j : Fin n,
          (higham9_18_tridiag_to_matrix T i j + DeltaA i j) * x_hat j =
        b i) :=
  higham9_14_spd_tridiag_positive_DLT_source_f_bound_actual_triangular_solves
    fp n (higham9_18_tridiag_to_matrix T)
    (tridiag_L_matrix l_hat) (tridiag_U_matrix u_hat T.c)
    d b u hu hn hγ_le_u
    (tridiag_matrices_isTridiagLU l_hat u_hat T.c)
    (higham9_19_tridiag_exact_product_of_recurrence T l_hat u_hat hrec)
    hdetA hd_pos hDLT

/-- **Theorem 9.14**, SPD positive-`D L^T` exact-recurrence package with
actual triangular solves, deriving nonsingularity from the source SPD
hypothesis. -/
theorem higham9_14_spd_tridiag_positive_DLT_source_f_bound_actual_triangular_solves_of_spd_recurrence
    (fp : FPModel) (n : ℕ)
    (T : higham9_18_TridiagData n)
    (l_hat u_hat d b : Fin n → ℝ)
    (u : ℝ) (hu : 0 ≤ u)
    (hn : gammaValid fp n)
    (hγ_le_u : gamma fp n ≤ u)
    (hSPD : IsSymPosDef n (higham9_18_tridiag_to_matrix T))
    (hrec : higham9_19_TridiagExactLURecurrence T l_hat u_hat)
    (hd_pos : ∀ k : Fin n, 0 < d k)
    (hDLT : ∀ k j : Fin n,
      tridiag_U_matrix u_hat T.c k j =
        d k * tridiag_L_matrix l_hat j k) :
    let y_hat := fl_forwardSub fp n (tridiag_L_matrix l_hat) b
    let x_hat := fl_backSub fp n (tridiag_U_matrix u_hat T.c) y_hat
    ∃ DeltaA : Fin n → Fin n → ℝ,
      (∀ i j,
        |DeltaA i j| ≤
          higham9_14_f u * |higham9_18_tridiag_to_matrix T i j|) ∧
      (∀ i,
        ∑ j : Fin n,
          (higham9_18_tridiag_to_matrix T i j + DeltaA i j) * x_hat j =
        b i) :=
  higham9_14_spd_tridiag_positive_DLT_source_f_bound_actual_triangular_solves_of_recurrence
    fp n T l_hat u_hat d b u hu hn hγ_le_u hrec
    (by
      simpa using
        isSymPosDef_det_ne_zero (higham9_18_tridiag_to_matrix T) hSPD)
    hd_pos hDLT

/-- **Theorem 9.14**, SPD positive-`D L^T` exact-factor actual solves with
the natural `γ_n` coefficient. -/
theorem higham9_14_spd_tridiag_positive_DLT_source_f_bound_actual_triangular_solves_gamma
    (fp : FPModel) (n : ℕ)
    (A L_hat U_hat : Fin n → Fin n → ℝ)
    (d : Fin n → ℝ)
    (b : Fin n → ℝ)
    (hn : gammaValid fp n)
    (hStruct : IsTridiagLU n L_hat U_hat)
    (hLU_eq : ∀ i j : Fin n,
      ∑ k : Fin n, L_hat i k * U_hat k j = A i j)
    (hdetA : Matrix.det (Matrix.of A : Matrix (Fin n) (Fin n) ℝ) ≠ 0)
    (hd_pos : ∀ k : Fin n, 0 < d k)
    (hDLT : ∀ k j : Fin n, U_hat k j = d k * L_hat j k) :
    let y_hat := fl_forwardSub fp n L_hat b
    let x_hat := fl_backSub fp n U_hat y_hat
    ∃ DeltaA : Fin n → Fin n → ℝ,
      (∀ i j, |DeltaA i j| ≤ higham9_14_f (gamma fp n) * |A i j|) ∧
      (∀ i, ∑ j : Fin n, (A i j + DeltaA i j) * x_hat j = b i) :=
  higham9_14_spd_tridiag_positive_DLT_source_f_bound_actual_triangular_solves
    fp n A L_hat U_hat d b (gamma fp n) (gamma_nonneg fp hn)
    hn le_rfl hStruct hLU_eq hdetA hd_pos hDLT

/-- **Theorem 9.14**, SPD positive-`D L^T` exact-factor actual solves with
the source SPD hypothesis discharging nonsingularity and coefficient `γ_n`. -/
theorem higham9_14_spd_tridiag_positive_DLT_source_f_bound_actual_triangular_solves_of_spd_gamma
    (fp : FPModel) (n : ℕ)
    (A L_hat U_hat : Fin n → Fin n → ℝ)
    (d : Fin n → ℝ)
    (b : Fin n → ℝ)
    (hn : gammaValid fp n)
    (hSPD : IsSymPosDef n A)
    (hStruct : IsTridiagLU n L_hat U_hat)
    (hLU_eq : ∀ i j : Fin n,
      ∑ k : Fin n, L_hat i k * U_hat k j = A i j)
    (hd_pos : ∀ k : Fin n, 0 < d k)
    (hDLT : ∀ k j : Fin n, U_hat k j = d k * L_hat j k) :
    let y_hat := fl_forwardSub fp n L_hat b
    let x_hat := fl_backSub fp n U_hat y_hat
    ∃ DeltaA : Fin n → Fin n → ℝ,
      (∀ i j, |DeltaA i j| ≤ higham9_14_f (gamma fp n) * |A i j|) ∧
      (∀ i, ∑ j : Fin n, (A i j + DeltaA i j) * x_hat j = b i) :=
  higham9_14_spd_tridiag_positive_DLT_source_f_bound_actual_triangular_solves_of_spd
    fp n A L_hat U_hat d b (gamma fp n) (gamma_nonneg fp hn)
    hn le_rfl hSPD hStruct hLU_eq hd_pos hDLT

/-- **Theorem 9.14**, SPD positive-`D L^T` recurrence actual solves with
the natural `γ_n` coefficient. -/
theorem higham9_14_spd_tridiag_positive_DLT_source_f_bound_actual_triangular_solves_of_recurrence_gamma
    (fp : FPModel) (n : ℕ)
    (T : higham9_18_TridiagData n)
    (l_hat u_hat d b : Fin n → ℝ)
    (hn : gammaValid fp n)
    (hrec : higham9_19_TridiagExactLURecurrence T l_hat u_hat)
    (hdetA :
      Matrix.det
        (Matrix.of (higham9_18_tridiag_to_matrix T) :
          Matrix (Fin n) (Fin n) ℝ) ≠ 0)
    (hd_pos : ∀ k : Fin n, 0 < d k)
    (hDLT : ∀ k j : Fin n,
      tridiag_U_matrix u_hat T.c k j =
        d k * tridiag_L_matrix l_hat j k) :
    let y_hat := fl_forwardSub fp n (tridiag_L_matrix l_hat) b
    let x_hat := fl_backSub fp n (tridiag_U_matrix u_hat T.c) y_hat
    ∃ DeltaA : Fin n → Fin n → ℝ,
      (∀ i j,
        |DeltaA i j| ≤
          higham9_14_f (gamma fp n) *
            |higham9_18_tridiag_to_matrix T i j|) ∧
      (∀ i,
        ∑ j : Fin n,
          (higham9_18_tridiag_to_matrix T i j + DeltaA i j) * x_hat j =
        b i) :=
  higham9_14_spd_tridiag_positive_DLT_source_f_bound_actual_triangular_solves_of_recurrence
    fp n T l_hat u_hat d b (gamma fp n) (gamma_nonneg fp hn)
    hn le_rfl hrec hdetA hd_pos hDLT

/-- **Theorem 9.14**, SPD positive-`D L^T` recurrence actual solves with
source SPD nonsingularity discharge and coefficient `γ_n`. -/
theorem higham9_14_spd_tridiag_positive_DLT_source_f_bound_actual_triangular_solves_of_spd_recurrence_gamma
    (fp : FPModel) (n : ℕ)
    (T : higham9_18_TridiagData n)
    (l_hat u_hat d b : Fin n → ℝ)
    (hn : gammaValid fp n)
    (hSPD : IsSymPosDef n (higham9_18_tridiag_to_matrix T))
    (hrec : higham9_19_TridiagExactLURecurrence T l_hat u_hat)
    (hd_pos : ∀ k : Fin n, 0 < d k)
    (hDLT : ∀ k j : Fin n,
      tridiag_U_matrix u_hat T.c k j =
        d k * tridiag_L_matrix l_hat j k) :
    let y_hat := fl_forwardSub fp n (tridiag_L_matrix l_hat) b
    let x_hat := fl_backSub fp n (tridiag_U_matrix u_hat T.c) y_hat
    ∃ DeltaA : Fin n → Fin n → ℝ,
      (∀ i j,
        |DeltaA i j| ≤
          higham9_14_f (gamma fp n) *
            |higham9_18_tridiag_to_matrix T i j|) ∧
      (∀ i,
        ∑ j : Fin n,
          (higham9_18_tridiag_to_matrix T i j + DeltaA i j) * x_hat j =
        b i) :=
  higham9_14_spd_tridiag_positive_DLT_source_f_bound_actual_triangular_solves_of_spd_recurrence
    fp n T l_hat u_hat d b (gamma fp n) (gamma_nonneg fp hn)
    hn le_rfl hSPD hrec hd_pos hDLT

/-- **Theorem 9.14**, nonnegative-LU exact-factor package with actual
triangular solves. -/
theorem higham9_14_nonnegative_lu_source_f_bound_actual_triangular_solves
    (fp : FPModel) (n : ℕ)
    (A L_hat U_hat : Fin n → Fin n → ℝ)
    (b : Fin n → ℝ)
    (u : ℝ) (hu : 0 ≤ u)
    (hn : gammaValid fp n)
    (hγ_le_u : gamma fp n ≤ u)
    (hNonneg : HasNonnegLUFactors n A L_hat U_hat)
    (hdetA : Matrix.det (Matrix.of A : Matrix (Fin n) (Fin n) ℝ) ≠ 0) :
    let y_hat := fl_forwardSub fp n L_hat b
    let x_hat := fl_backSub fp n U_hat y_hat
    ∃ DeltaA : Fin n → Fin n → ℝ,
      (∀ i j, |DeltaA i j| ≤ higham9_14_f u * |A i j|) ∧
      (∀ i, ∑ j : Fin n, (A i j + DeltaA i j) * x_hat j = b i) := by
  obtain ⟨DeltaA, hDeltaA, hBackward⟩ :=
    higham9_14_source_f_bound_of_LUFactSpec_fl_triangular_solves_gamma_le
      fp n A L_hat U_hat b 1 u hu hn hNonneg.1 hγ_le_u
      (hNonneg.1.det_ne_zero_iff_U_diag_ne_zero.mp hdetA)
      (fun i j => by
        simpa [one_mul] using le_of_eq
          (higham9_12_nonneg_lu_optimal_growth n A L_hat U_hat hNonneg i j))
  refine ⟨DeltaA, ?_, hBackward⟩
  intro i j
  simpa [one_mul] using hDeltaA i j

/-- **Theorem 9.14**, M-matrix LU exact-factor package with actual triangular
solves. -/
theorem higham9_14_mmatrix_lu_source_f_bound_actual_triangular_solves
    (fp : FPModel) (n : ℕ)
    (A L_hat U_hat : Fin n → Fin n → ℝ)
    (b : Fin n → ℝ)
    (u : ℝ) (hu : 0 ≤ u)
    (hn : gammaValid fp n)
    (hγ_le_u : gamma fp n ≤ u)
    (hM : IsMMatrix n A)
    (hLU : LUFactSpec n A L_hat U_hat)
    (hdetA : Matrix.det (Matrix.of A : Matrix (Fin n) (Fin n) ℝ) ≠ 0)
    (hL_nn : ∀ i k : Fin n, 0 ≤ L_hat i k)
    (hU_nn : ∀ k j : Fin n, 0 ≤ U_hat k j) :
    let y_hat := fl_forwardSub fp n L_hat b
    let x_hat := fl_backSub fp n U_hat y_hat
    ∃ DeltaA : Fin n → Fin n → ℝ,
      (∀ i j, |DeltaA i j| ≤ higham9_14_f u * |A i j|) ∧
      (∀ i, ∑ j : Fin n, (A i j + DeltaA i j) * x_hat j = b i) := by
  obtain ⟨DeltaA, hDeltaA, hBackward⟩ :=
    higham9_14_source_f_bound_of_LUFactSpec_fl_triangular_solves_gamma_le
      fp n A L_hat U_hat b 1 u hu hn hLU hγ_le_u
      (hLU.det_ne_zero_iff_U_diag_ne_zero.mp hdetA)
      (fun i j => by
        simpa [one_mul] using le_of_eq
          (higham9_12_mmatrix_lu_optimal_growth n A L_hat U_hat hM hLU
            hL_nn hU_nn i j))
  refine ⟨DeltaA, ?_, hBackward⟩
  intro i j
  simpa [one_mul] using hDeltaA i j

/-- **Theorem 9.14**, sign-equivalent optimal-growth exact-factor package
with actual triangular solves. -/
theorem higham9_14_sign_equiv_source_f_bound_actual_triangular_solves
    (fp : FPModel) (n : ℕ)
    (B L_B U_B : Fin n → Fin n → ℝ)
    (D₁ D₂ : Fin n → Fin n → ℝ)
    (hD₁ : IsSignDiag n D₁) (hD₂ : IsSignDiag n D₂)
    (hB_growth : ∀ i j : Fin n,
      ∑ k : Fin n, |L_B i k| * |U_B k j| = |B i j|)
    (A L_hat U_hat : Fin n → Fin n → ℝ)
    (hA_eq : ∀ i j : Fin n,
      A i j = ∑ k₁ : Fin n, D₁ i k₁ * (∑ k₂ : Fin n, B k₁ k₂ * D₂ k₂ j))
    (hL_abs : ∀ i k : Fin n, |L_hat i k| = |L_B i k|)
    (hU_abs : ∀ k j : Fin n, |U_hat k j| = |U_B k j|)
    (b : Fin n → ℝ)
    (u : ℝ) (hu : 0 ≤ u)
    (hn : gammaValid fp n)
    (hγ_le_u : gamma fp n ≤ u)
    (hLU : LUFactSpec n A L_hat U_hat)
    (hdetA : Matrix.det (Matrix.of A : Matrix (Fin n) (Fin n) ℝ) ≠ 0) :
    let y_hat := fl_forwardSub fp n L_hat b
    let x_hat := fl_backSub fp n U_hat y_hat
    ∃ DeltaA : Fin n → Fin n → ℝ,
      (∀ i j, |DeltaA i j| ≤ higham9_14_f u * |A i j|) ∧
      (∀ i, ∑ j : Fin n, (A i j + DeltaA i j) * x_hat j = b i) := by
  obtain ⟨DeltaA, hDeltaA, hBackward⟩ :=
    higham9_14_source_f_bound_of_LUFactSpec_fl_triangular_solves_gamma_le
      fp n A L_hat U_hat b 1 u hu hn hLU hγ_le_u
      (hLU.det_ne_zero_iff_U_diag_ne_zero.mp hdetA)
      (fun i j => by
        simpa [one_mul] using le_of_eq
          (higham9_12_sign_equiv_optimal_growth n B L_B U_B D₁ D₂
            hD₁ hD₂ hB_growth A hA_eq L_hat U_hat hL_abs hU_abs i j))
  refine ⟨DeltaA, ?_, hBackward⟩
  intro i j
  simpa [one_mul] using hDeltaA i j

/-- **Theorem 9.14**, nonnegative-LU exact-factor actual solves with the
natural `γ_n` coefficient. -/
theorem higham9_14_nonnegative_lu_source_f_bound_actual_triangular_solves_gamma
    (fp : FPModel) (n : ℕ)
    (A L_hat U_hat : Fin n → Fin n → ℝ)
    (b : Fin n → ℝ)
    (hn : gammaValid fp n)
    (hNonneg : HasNonnegLUFactors n A L_hat U_hat)
    (hdetA : Matrix.det (Matrix.of A : Matrix (Fin n) (Fin n) ℝ) ≠ 0) :
    let y_hat := fl_forwardSub fp n L_hat b
    let x_hat := fl_backSub fp n U_hat y_hat
    ∃ DeltaA : Fin n → Fin n → ℝ,
      (∀ i j, |DeltaA i j| ≤ higham9_14_f (gamma fp n) * |A i j|) ∧
      (∀ i, ∑ j : Fin n, (A i j + DeltaA i j) * x_hat j = b i) :=
  higham9_14_nonnegative_lu_source_f_bound_actual_triangular_solves
    fp n A L_hat U_hat b (gamma fp n) (gamma_nonneg fp hn)
    hn le_rfl hNonneg hdetA

/-- **Theorem 9.14**, M-matrix LU exact-factor actual solves with the natural
`γ_n` coefficient. -/
theorem higham9_14_mmatrix_lu_source_f_bound_actual_triangular_solves_gamma
    (fp : FPModel) (n : ℕ)
    (A L_hat U_hat : Fin n → Fin n → ℝ)
    (b : Fin n → ℝ)
    (hn : gammaValid fp n)
    (hM : IsMMatrix n A)
    (hLU : LUFactSpec n A L_hat U_hat)
    (hdetA : Matrix.det (Matrix.of A : Matrix (Fin n) (Fin n) ℝ) ≠ 0)
    (hL_nn : ∀ i k : Fin n, 0 ≤ L_hat i k)
    (hU_nn : ∀ k j : Fin n, 0 ≤ U_hat k j) :
    let y_hat := fl_forwardSub fp n L_hat b
    let x_hat := fl_backSub fp n U_hat y_hat
    ∃ DeltaA : Fin n → Fin n → ℝ,
      (∀ i j, |DeltaA i j| ≤ higham9_14_f (gamma fp n) * |A i j|) ∧
      (∀ i, ∑ j : Fin n, (A i j + DeltaA i j) * x_hat j = b i) :=
  higham9_14_mmatrix_lu_source_f_bound_actual_triangular_solves
    fp n A L_hat U_hat b (gamma fp n) (gamma_nonneg fp hn)
    hn le_rfl hM hLU hdetA hL_nn hU_nn

/-- **Theorem 9.14**, sign-equivalent optimal-growth exact-factor actual
solves with the natural `γ_n` coefficient. -/
theorem higham9_14_sign_equiv_source_f_bound_actual_triangular_solves_gamma
    (fp : FPModel) (n : ℕ)
    (B L_B U_B : Fin n → Fin n → ℝ)
    (D₁ D₂ : Fin n → Fin n → ℝ)
    (hD₁ : IsSignDiag n D₁) (hD₂ : IsSignDiag n D₂)
    (hB_growth : ∀ i j : Fin n,
      ∑ k : Fin n, |L_B i k| * |U_B k j| = |B i j|)
    (A L_hat U_hat : Fin n → Fin n → ℝ)
    (hA_eq : ∀ i j : Fin n,
      A i j = ∑ k₁ : Fin n, D₁ i k₁ * (∑ k₂ : Fin n, B k₁ k₂ * D₂ k₂ j))
    (hL_abs : ∀ i k : Fin n, |L_hat i k| = |L_B i k|)
    (hU_abs : ∀ k j : Fin n, |U_hat k j| = |U_B k j|)
    (b : Fin n → ℝ)
    (hn : gammaValid fp n)
    (hLU : LUFactSpec n A L_hat U_hat)
    (hdetA : Matrix.det (Matrix.of A : Matrix (Fin n) (Fin n) ℝ) ≠ 0) :
    let y_hat := fl_forwardSub fp n L_hat b
    let x_hat := fl_backSub fp n U_hat y_hat
    ∃ DeltaA : Fin n → Fin n → ℝ,
      (∀ i j, |DeltaA i j| ≤ higham9_14_f (gamma fp n) * |A i j|) ∧
      (∀ i, ∑ j : Fin n, (A i j + DeltaA i j) * x_hat j = b i) :=
  higham9_14_sign_equiv_source_f_bound_actual_triangular_solves
    fp n B L_B U_B D₁ D₂ hD₁ hD₂ hB_growth A L_hat U_hat
    hA_eq hL_abs hU_abs b (gamma fp n) (gamma_nonneg fp hn)
    hn le_rfl hLU hdetA

/-- **Theorem 9.14**, SPD positive-`D L^T` exact-factor package with actual
triangular solves and final `h(u)` bound.

This is the `h(u)` counterpart of
`higham9_14_spd_tridiag_positive_DLT_source_f_bound_actual_triangular_solves`:
the exact positive-`D L^T` factor certificate gives `|Lhat||Uhat| = |A|`,
while the actual triangular solves supply equation (9.21). -/
theorem higham9_14_spd_tridiag_positive_DLT_source_h_bound_actual_triangular_solves
    (fp : FPModel) (n : ℕ)
    (A L_hat U_hat : Fin n → Fin n → ℝ)
    (d : Fin n → ℝ)
    (b : Fin n → ℝ)
    (u : ℝ) (hu : 0 ≤ u) (hu_lt_one : u < 1)
    (hn : gammaValid fp n)
    (hγ_le_u : gamma fp n ≤ u)
    (hStruct : IsTridiagLU n L_hat U_hat)
    (hLU_eq : ∀ i j : Fin n,
      ∑ k : Fin n, L_hat i k * U_hat k j = A i j)
    (hdetA : Matrix.det (Matrix.of A : Matrix (Fin n) (Fin n) ℝ) ≠ 0)
    (hd_pos : ∀ k : Fin n, 0 < d k)
    (hDLT : ∀ k j : Fin n, U_hat k j = d k * L_hat j k) :
    let y_hat := fl_forwardSub fp n L_hat b
    let x_hat := fl_backSub fp n U_hat y_hat
    ∃ DeltaA : Fin n → Fin n → ℝ,
      (∀ i j, |DeltaA i j| ≤ higham9_14_h u * |A i j|) ∧
      (∀ i, ∑ j : Fin n, (A i j + DeltaA i j) * x_hat j = b i) := by
  let hLU : LUFactSpec n A L_hat U_hat :=
    { L_diag := hStruct.L_diag
      L_upper_zero := hStruct.L_upper_zero
      U_lower_zero := hStruct.U_lower_zero
      product_eq := hLU_eq }
  exact higham9_14_source_h_bound_of_LUFactSpec_fl_triangular_solves_gamma_le
    fp n A L_hat U_hat b u hu hu_lt_one hn hLU hγ_le_u
    (hLU.det_ne_zero_iff_U_diag_ne_zero.mp hdetA)
    (fun i j => le_of_eq
      (higham9_12_spd_tridiag_absLU_eq_of_positive_DLT
        A L_hat U_hat d hStruct hLU_eq hd_pos hDLT i j))

/-- **Theorem 9.14**, SPD positive-`D L^T` actual-solve final bound,
deriving nonsingularity from the source SPD hypothesis. -/
theorem higham9_14_spd_tridiag_positive_DLT_source_h_bound_actual_triangular_solves_of_spd
    (fp : FPModel) (n : ℕ)
    (A L_hat U_hat : Fin n → Fin n → ℝ)
    (d : Fin n → ℝ)
    (b : Fin n → ℝ)
    (u : ℝ) (hu : 0 ≤ u) (hu_lt_one : u < 1)
    (hn : gammaValid fp n)
    (hγ_le_u : gamma fp n ≤ u)
    (hSPD : IsSymPosDef n A)
    (hStruct : IsTridiagLU n L_hat U_hat)
    (hLU_eq : ∀ i j : Fin n,
      ∑ k : Fin n, L_hat i k * U_hat k j = A i j)
    (hd_pos : ∀ k : Fin n, 0 < d k)
    (hDLT : ∀ k j : Fin n, U_hat k j = d k * L_hat j k) :
    let y_hat := fl_forwardSub fp n L_hat b
    let x_hat := fl_backSub fp n U_hat y_hat
    ∃ DeltaA : Fin n → Fin n → ℝ,
      (∀ i j, |DeltaA i j| ≤ higham9_14_h u * |A i j|) ∧
      (∀ i, ∑ j : Fin n, (A i j + DeltaA i j) * x_hat j = b i) :=
  higham9_14_spd_tridiag_positive_DLT_source_h_bound_actual_triangular_solves
    fp n A L_hat U_hat d b u hu hu_lt_one hn hγ_le_u hStruct hLU_eq
    (by simpa using isSymPosDef_det_ne_zero A hSPD)
    hd_pos hDLT

/-- **Theorem 9.14**, SPD positive-`D L^T` exact-recurrence package with
actual triangular solves and final `h(u)` bound. -/
theorem higham9_14_spd_tridiag_positive_DLT_source_h_bound_actual_triangular_solves_of_recurrence
    (fp : FPModel) (n : ℕ)
    (T : higham9_18_TridiagData n)
    (l_hat u_hat d b : Fin n → ℝ)
    (u : ℝ) (hu : 0 ≤ u) (hu_lt_one : u < 1)
    (hn : gammaValid fp n)
    (hγ_le_u : gamma fp n ≤ u)
    (hrec : higham9_19_TridiagExactLURecurrence T l_hat u_hat)
    (hdetA :
      Matrix.det
        (Matrix.of (higham9_18_tridiag_to_matrix T) :
          Matrix (Fin n) (Fin n) ℝ) ≠ 0)
    (hd_pos : ∀ k : Fin n, 0 < d k)
    (hDLT : ∀ k j : Fin n,
      tridiag_U_matrix u_hat T.c k j =
        d k * tridiag_L_matrix l_hat j k) :
    let y_hat := fl_forwardSub fp n (tridiag_L_matrix l_hat) b
    let x_hat := fl_backSub fp n (tridiag_U_matrix u_hat T.c) y_hat
    ∃ DeltaA : Fin n → Fin n → ℝ,
      (∀ i j,
        |DeltaA i j| ≤
          higham9_14_h u * |higham9_18_tridiag_to_matrix T i j|) ∧
      (∀ i,
        ∑ j : Fin n,
          (higham9_18_tridiag_to_matrix T i j + DeltaA i j) * x_hat j =
        b i) :=
  higham9_14_spd_tridiag_positive_DLT_source_h_bound_actual_triangular_solves
    fp n (higham9_18_tridiag_to_matrix T)
    (tridiag_L_matrix l_hat) (tridiag_U_matrix u_hat T.c)
    d b u hu hu_lt_one hn hγ_le_u
    (tridiag_matrices_isTridiagLU l_hat u_hat T.c)
    (higham9_19_tridiag_exact_product_of_recurrence T l_hat u_hat hrec)
    hdetA hd_pos hDLT

/-- **Theorem 9.14**, SPD positive-`D L^T` exact-recurrence actual-solve final
bound, deriving nonsingularity from the source SPD hypothesis. -/
theorem higham9_14_spd_tridiag_positive_DLT_source_h_bound_actual_triangular_solves_of_spd_recurrence
    (fp : FPModel) (n : ℕ)
    (T : higham9_18_TridiagData n)
    (l_hat u_hat d b : Fin n → ℝ)
    (u : ℝ) (hu : 0 ≤ u) (hu_lt_one : u < 1)
    (hn : gammaValid fp n)
    (hγ_le_u : gamma fp n ≤ u)
    (hSPD : IsSymPosDef n (higham9_18_tridiag_to_matrix T))
    (hrec : higham9_19_TridiagExactLURecurrence T l_hat u_hat)
    (hd_pos : ∀ k : Fin n, 0 < d k)
    (hDLT : ∀ k j : Fin n,
      tridiag_U_matrix u_hat T.c k j =
        d k * tridiag_L_matrix l_hat j k) :
    let y_hat := fl_forwardSub fp n (tridiag_L_matrix l_hat) b
    let x_hat := fl_backSub fp n (tridiag_U_matrix u_hat T.c) y_hat
    ∃ DeltaA : Fin n → Fin n → ℝ,
      (∀ i j,
        |DeltaA i j| ≤
          higham9_14_h u * |higham9_18_tridiag_to_matrix T i j|) ∧
      (∀ i,
        ∑ j : Fin n,
          (higham9_18_tridiag_to_matrix T i j + DeltaA i j) * x_hat j =
        b i) :=
  higham9_14_spd_tridiag_positive_DLT_source_h_bound_actual_triangular_solves_of_recurrence
    fp n T l_hat u_hat d b u hu hu_lt_one hn hγ_le_u hrec
    (by
      simpa using
        isSymPosDef_det_ne_zero (higham9_18_tridiag_to_matrix T) hSPD)
    hd_pos hDLT

/-- **Theorem 9.14**, SPD positive-`D L^T` exact-factor actual solves with
Higham's final `h(γ_n)` coefficient. -/
theorem higham9_14_spd_tridiag_positive_DLT_source_h_bound_actual_triangular_solves_gamma
    (fp : FPModel) (n : ℕ)
    (A L_hat U_hat : Fin n → Fin n → ℝ)
    (d : Fin n → ℝ)
    (b : Fin n → ℝ)
    (hn : gammaValid fp n)
    (hγ_lt_one : gamma fp n < 1)
    (hStruct : IsTridiagLU n L_hat U_hat)
    (hLU_eq : ∀ i j : Fin n,
      ∑ k : Fin n, L_hat i k * U_hat k j = A i j)
    (hdetA : Matrix.det (Matrix.of A : Matrix (Fin n) (Fin n) ℝ) ≠ 0)
    (hd_pos : ∀ k : Fin n, 0 < d k)
    (hDLT : ∀ k j : Fin n, U_hat k j = d k * L_hat j k) :
    let y_hat := fl_forwardSub fp n L_hat b
    let x_hat := fl_backSub fp n U_hat y_hat
    ∃ DeltaA : Fin n → Fin n → ℝ,
      (∀ i j, |DeltaA i j| ≤ higham9_14_h (gamma fp n) * |A i j|) ∧
      (∀ i, ∑ j : Fin n, (A i j + DeltaA i j) * x_hat j = b i) :=
  higham9_14_spd_tridiag_positive_DLT_source_h_bound_actual_triangular_solves
    fp n A L_hat U_hat d b (gamma fp n) (gamma_nonneg fp hn)
    hγ_lt_one hn le_rfl hStruct hLU_eq hdetA hd_pos hDLT

/-- **Theorem 9.14**, SPD positive-`D L^T` exact-factor actual solves with
source SPD nonsingularity discharge and final `h(γ_n)` coefficient. -/
theorem higham9_14_spd_tridiag_positive_DLT_source_h_bound_actual_triangular_solves_of_spd_gamma
    (fp : FPModel) (n : ℕ)
    (A L_hat U_hat : Fin n → Fin n → ℝ)
    (d : Fin n → ℝ)
    (b : Fin n → ℝ)
    (hn : gammaValid fp n)
    (hγ_lt_one : gamma fp n < 1)
    (hSPD : IsSymPosDef n A)
    (hStruct : IsTridiagLU n L_hat U_hat)
    (hLU_eq : ∀ i j : Fin n,
      ∑ k : Fin n, L_hat i k * U_hat k j = A i j)
    (hd_pos : ∀ k : Fin n, 0 < d k)
    (hDLT : ∀ k j : Fin n, U_hat k j = d k * L_hat j k) :
    let y_hat := fl_forwardSub fp n L_hat b
    let x_hat := fl_backSub fp n U_hat y_hat
    ∃ DeltaA : Fin n → Fin n → ℝ,
      (∀ i j, |DeltaA i j| ≤ higham9_14_h (gamma fp n) * |A i j|) ∧
      (∀ i, ∑ j : Fin n, (A i j + DeltaA i j) * x_hat j = b i) :=
  higham9_14_spd_tridiag_positive_DLT_source_h_bound_actual_triangular_solves_of_spd
    fp n A L_hat U_hat d b (gamma fp n) (gamma_nonneg fp hn)
    hγ_lt_one hn le_rfl hSPD hStruct hLU_eq hd_pos hDLT

/-- **Theorem 9.14**, SPD positive-`D L^T` recurrence actual solves with
Higham's final `h(γ_n)` coefficient. -/
theorem higham9_14_spd_tridiag_positive_DLT_source_h_bound_actual_triangular_solves_of_recurrence_gamma
    (fp : FPModel) (n : ℕ)
    (T : higham9_18_TridiagData n)
    (l_hat u_hat d b : Fin n → ℝ)
    (hn : gammaValid fp n)
    (hγ_lt_one : gamma fp n < 1)
    (hrec : higham9_19_TridiagExactLURecurrence T l_hat u_hat)
    (hdetA :
      Matrix.det
        (Matrix.of (higham9_18_tridiag_to_matrix T) :
          Matrix (Fin n) (Fin n) ℝ) ≠ 0)
    (hd_pos : ∀ k : Fin n, 0 < d k)
    (hDLT : ∀ k j : Fin n,
      tridiag_U_matrix u_hat T.c k j =
        d k * tridiag_L_matrix l_hat j k) :
    let y_hat := fl_forwardSub fp n (tridiag_L_matrix l_hat) b
    let x_hat := fl_backSub fp n (tridiag_U_matrix u_hat T.c) y_hat
    ∃ DeltaA : Fin n → Fin n → ℝ,
      (∀ i j,
        |DeltaA i j| ≤
          higham9_14_h (gamma fp n) *
            |higham9_18_tridiag_to_matrix T i j|) ∧
      (∀ i,
        ∑ j : Fin n,
          (higham9_18_tridiag_to_matrix T i j + DeltaA i j) * x_hat j =
        b i) :=
  higham9_14_spd_tridiag_positive_DLT_source_h_bound_actual_triangular_solves_of_recurrence
    fp n T l_hat u_hat d b (gamma fp n) (gamma_nonneg fp hn)
    hγ_lt_one hn le_rfl hrec hdetA hd_pos hDLT

/-- **Theorem 9.14**, SPD positive-`D L^T` recurrence actual solves with
source SPD nonsingularity discharge and final `h(γ_n)` coefficient. -/
theorem higham9_14_spd_tridiag_positive_DLT_source_h_bound_actual_triangular_solves_of_spd_recurrence_gamma
    (fp : FPModel) (n : ℕ)
    (T : higham9_18_TridiagData n)
    (l_hat u_hat d b : Fin n → ℝ)
    (hn : gammaValid fp n)
    (hγ_lt_one : gamma fp n < 1)
    (hSPD : IsSymPosDef n (higham9_18_tridiag_to_matrix T))
    (hrec : higham9_19_TridiagExactLURecurrence T l_hat u_hat)
    (hd_pos : ∀ k : Fin n, 0 < d k)
    (hDLT : ∀ k j : Fin n,
      tridiag_U_matrix u_hat T.c k j =
        d k * tridiag_L_matrix l_hat j k) :
    let y_hat := fl_forwardSub fp n (tridiag_L_matrix l_hat) b
    let x_hat := fl_backSub fp n (tridiag_U_matrix u_hat T.c) y_hat
    ∃ DeltaA : Fin n → Fin n → ℝ,
      (∀ i j,
        |DeltaA i j| ≤
          higham9_14_h (gamma fp n) *
            |higham9_18_tridiag_to_matrix T i j|) ∧
      (∀ i,
        ∑ j : Fin n,
          (higham9_18_tridiag_to_matrix T i j + DeltaA i j) * x_hat j =
        b i) :=
  higham9_14_spd_tridiag_positive_DLT_source_h_bound_actual_triangular_solves_of_spd_recurrence
    fp n T l_hat u_hat d b (gamma fp n) (gamma_nonneg fp hn)
    hγ_lt_one hn le_rfl hSPD hrec hd_pos hDLT

/-- **Theorem 9.14**, nonnegative-LU exact-factor package with actual
triangular solves and final `h(u)` bound. -/
theorem higham9_14_nonnegative_lu_source_h_bound_actual_triangular_solves
    (fp : FPModel) (n : ℕ)
    (A L_hat U_hat : Fin n → Fin n → ℝ)
    (b : Fin n → ℝ)
    (u : ℝ) (hu : 0 ≤ u) (hu_lt_one : u < 1)
    (hn : gammaValid fp n)
    (hγ_le_u : gamma fp n ≤ u)
    (hNonneg : HasNonnegLUFactors n A L_hat U_hat)
    (hdetA : Matrix.det (Matrix.of A : Matrix (Fin n) (Fin n) ℝ) ≠ 0) :
    let y_hat := fl_forwardSub fp n L_hat b
    let x_hat := fl_backSub fp n U_hat y_hat
    ∃ DeltaA : Fin n → Fin n → ℝ,
      (∀ i j, |DeltaA i j| ≤ higham9_14_h u * |A i j|) ∧
      (∀ i, ∑ j : Fin n, (A i j + DeltaA i j) * x_hat j = b i) :=
  higham9_14_source_h_bound_of_LUFactSpec_fl_triangular_solves_gamma_le
    fp n A L_hat U_hat b u hu hu_lt_one hn hNonneg.1 hγ_le_u
    (hNonneg.1.det_ne_zero_iff_U_diag_ne_zero.mp hdetA)
    (fun i j => le_of_eq
      (higham9_12_nonneg_lu_optimal_growth n A L_hat U_hat hNonneg i j))

/-- **Theorem 9.14**, M-matrix LU exact-factor package with actual triangular
solves and final `h(u)` bound. -/
theorem higham9_14_mmatrix_lu_source_h_bound_actual_triangular_solves
    (fp : FPModel) (n : ℕ)
    (A L_hat U_hat : Fin n → Fin n → ℝ)
    (b : Fin n → ℝ)
    (u : ℝ) (hu : 0 ≤ u) (hu_lt_one : u < 1)
    (hn : gammaValid fp n)
    (hγ_le_u : gamma fp n ≤ u)
    (hM : IsMMatrix n A)
    (hLU : LUFactSpec n A L_hat U_hat)
    (hdetA : Matrix.det (Matrix.of A : Matrix (Fin n) (Fin n) ℝ) ≠ 0)
    (hL_nn : ∀ i k : Fin n, 0 ≤ L_hat i k)
    (hU_nn : ∀ k j : Fin n, 0 ≤ U_hat k j) :
    let y_hat := fl_forwardSub fp n L_hat b
    let x_hat := fl_backSub fp n U_hat y_hat
    ∃ DeltaA : Fin n → Fin n → ℝ,
      (∀ i j, |DeltaA i j| ≤ higham9_14_h u * |A i j|) ∧
      (∀ i, ∑ j : Fin n, (A i j + DeltaA i j) * x_hat j = b i) :=
  higham9_14_source_h_bound_of_LUFactSpec_fl_triangular_solves_gamma_le
    fp n A L_hat U_hat b u hu hu_lt_one hn hLU hγ_le_u
    (hLU.det_ne_zero_iff_U_diag_ne_zero.mp hdetA)
    (fun i j => le_of_eq
      (higham9_12_mmatrix_lu_optimal_growth n A L_hat U_hat hM hLU
        hL_nn hU_nn i j))

/-- **Theorem 9.14**, sign-equivalent optimal-growth exact-factor package with
actual triangular solves and final `h(u)` bound. -/
theorem higham9_14_sign_equiv_source_h_bound_actual_triangular_solves
    (fp : FPModel) (n : ℕ)
    (B L_B U_B : Fin n → Fin n → ℝ)
    (D₁ D₂ : Fin n → Fin n → ℝ)
    (hD₁ : IsSignDiag n D₁) (hD₂ : IsSignDiag n D₂)
    (hB_growth : ∀ i j : Fin n,
      ∑ k : Fin n, |L_B i k| * |U_B k j| = |B i j|)
    (A L_hat U_hat : Fin n → Fin n → ℝ)
    (hA_eq : ∀ i j : Fin n,
      A i j = ∑ k₁ : Fin n, D₁ i k₁ * (∑ k₂ : Fin n, B k₁ k₂ * D₂ k₂ j))
    (hL_abs : ∀ i k : Fin n, |L_hat i k| = |L_B i k|)
    (hU_abs : ∀ k j : Fin n, |U_hat k j| = |U_B k j|)
    (b : Fin n → ℝ)
    (u : ℝ) (hu : 0 ≤ u) (hu_lt_one : u < 1)
    (hn : gammaValid fp n)
    (hγ_le_u : gamma fp n ≤ u)
    (hLU : LUFactSpec n A L_hat U_hat)
    (hdetA : Matrix.det (Matrix.of A : Matrix (Fin n) (Fin n) ℝ) ≠ 0) :
    let y_hat := fl_forwardSub fp n L_hat b
    let x_hat := fl_backSub fp n U_hat y_hat
    ∃ DeltaA : Fin n → Fin n → ℝ,
      (∀ i j, |DeltaA i j| ≤ higham9_14_h u * |A i j|) ∧
      (∀ i, ∑ j : Fin n, (A i j + DeltaA i j) * x_hat j = b i) :=
  higham9_14_source_h_bound_of_LUFactSpec_fl_triangular_solves_gamma_le
    fp n A L_hat U_hat b u hu hu_lt_one hn hLU hγ_le_u
    (hLU.det_ne_zero_iff_U_diag_ne_zero.mp hdetA)
    (fun i j => le_of_eq
      (higham9_12_sign_equiv_optimal_growth n B L_B U_B D₁ D₂
        hD₁ hD₂ hB_growth A hA_eq L_hat U_hat hL_abs hU_abs i j))

/-- **Theorem 9.14**, nonnegative-LU exact-factor actual solves with Higham's
final `h(γ_n)` coefficient. -/
theorem higham9_14_nonnegative_lu_source_h_bound_actual_triangular_solves_gamma
    (fp : FPModel) (n : ℕ)
    (A L_hat U_hat : Fin n → Fin n → ℝ)
    (b : Fin n → ℝ)
    (hn : gammaValid fp n)
    (hγ_lt_one : gamma fp n < 1)
    (hNonneg : HasNonnegLUFactors n A L_hat U_hat)
    (hdetA : Matrix.det (Matrix.of A : Matrix (Fin n) (Fin n) ℝ) ≠ 0) :
    let y_hat := fl_forwardSub fp n L_hat b
    let x_hat := fl_backSub fp n U_hat y_hat
    ∃ DeltaA : Fin n → Fin n → ℝ,
      (∀ i j, |DeltaA i j| ≤ higham9_14_h (gamma fp n) * |A i j|) ∧
      (∀ i, ∑ j : Fin n, (A i j + DeltaA i j) * x_hat j = b i) :=
  higham9_14_nonnegative_lu_source_h_bound_actual_triangular_solves
    fp n A L_hat U_hat b (gamma fp n) (gamma_nonneg fp hn)
    hγ_lt_one hn le_rfl hNonneg hdetA

/-- **Theorem 9.14**, M-matrix LU exact-factor actual solves with Higham's
final `h(γ_n)` coefficient. -/
theorem higham9_14_mmatrix_lu_source_h_bound_actual_triangular_solves_gamma
    (fp : FPModel) (n : ℕ)
    (A L_hat U_hat : Fin n → Fin n → ℝ)
    (b : Fin n → ℝ)
    (hn : gammaValid fp n)
    (hγ_lt_one : gamma fp n < 1)
    (hM : IsMMatrix n A)
    (hLU : LUFactSpec n A L_hat U_hat)
    (hdetA : Matrix.det (Matrix.of A : Matrix (Fin n) (Fin n) ℝ) ≠ 0)
    (hL_nn : ∀ i k : Fin n, 0 ≤ L_hat i k)
    (hU_nn : ∀ k j : Fin n, 0 ≤ U_hat k j) :
    let y_hat := fl_forwardSub fp n L_hat b
    let x_hat := fl_backSub fp n U_hat y_hat
    ∃ DeltaA : Fin n → Fin n → ℝ,
      (∀ i j, |DeltaA i j| ≤ higham9_14_h (gamma fp n) * |A i j|) ∧
      (∀ i, ∑ j : Fin n, (A i j + DeltaA i j) * x_hat j = b i) :=
  higham9_14_mmatrix_lu_source_h_bound_actual_triangular_solves
    fp n A L_hat U_hat b (gamma fp n) (gamma_nonneg fp hn)
    hγ_lt_one hn le_rfl hM hLU hdetA hL_nn hU_nn

/-- **Theorem 9.14**, sign-equivalent optimal-growth exact-factor actual
solves with Higham's final `h(γ_n)` coefficient. -/
theorem higham9_14_sign_equiv_source_h_bound_actual_triangular_solves_gamma
    (fp : FPModel) (n : ℕ)
    (B L_B U_B : Fin n → Fin n → ℝ)
    (D₁ D₂ : Fin n → Fin n → ℝ)
    (hD₁ : IsSignDiag n D₁) (hD₂ : IsSignDiag n D₂)
    (hB_growth : ∀ i j : Fin n,
      ∑ k : Fin n, |L_B i k| * |U_B k j| = |B i j|)
    (A L_hat U_hat : Fin n → Fin n → ℝ)
    (hA_eq : ∀ i j : Fin n,
      A i j = ∑ k₁ : Fin n, D₁ i k₁ * (∑ k₂ : Fin n, B k₁ k₂ * D₂ k₂ j))
    (hL_abs : ∀ i k : Fin n, |L_hat i k| = |L_B i k|)
    (hU_abs : ∀ k j : Fin n, |U_hat k j| = |U_B k j|)
    (b : Fin n → ℝ)
    (hn : gammaValid fp n)
    (hγ_lt_one : gamma fp n < 1)
    (hLU : LUFactSpec n A L_hat U_hat)
    (hdetA : Matrix.det (Matrix.of A : Matrix (Fin n) (Fin n) ℝ) ≠ 0) :
    let y_hat := fl_forwardSub fp n L_hat b
    let x_hat := fl_backSub fp n U_hat y_hat
    ∃ DeltaA : Fin n → Fin n → ℝ,
      (∀ i j, |DeltaA i j| ≤ higham9_14_h (gamma fp n) * |A i j|) ∧
      (∀ i, ∑ j : Fin n, (A i j + DeltaA i j) * x_hat j = b i) :=
  higham9_14_sign_equiv_source_h_bound_actual_triangular_solves
    fp n B L_B U_B D₁ D₂ hD₁ hD₂ hB_growth A L_hat U_hat
    hA_eq hL_abs hU_abs b (gamma fp n) (gamma_nonneg fp hn)
    hγ_lt_one hn le_rfl hLU hdetA

/-- **Theorem 9.14**, source-predicate sign-equivalent model-consuming final
bound.

This is the `IsSignEquiv` wrapper around
`higham9_14_sign_equiv_source_h_bound_of_models`: the source sign-equivalence
predicate supplies the explicit sign-diagonal matrices, while the
factor-absolute-value and perturbation-model hypotheses remain visible. -/
theorem higham9_14_sign_equiv_source_h_bound_of_IsSignEquiv_models
    (n : ℕ)
    (A B L_B U_B L_hat U_hat : Fin n → Fin n → ℝ)
    (hAB : IsSignEquiv n A B)
    (hB_growth : ∀ i j : Fin n,
      ∑ k : Fin n, |L_B i k| * |U_B k j| = |B i j|)
    (hL_abs : ∀ i k : Fin n, |L_hat i k| = |L_B i k|)
    (hU_abs : ∀ k j : Fin n, |U_hat k j| = |U_B k j|)
    (y_hat x_hat b : Fin n → ℝ)
    (u : ℝ) (hu : 0 ≤ u) (hu_lt_one : u < 1)
    (DeltaA_LU DeltaL DeltaU : Fin n → Fin n → ℝ)
    (h20 : higham9_20_tridiag_lu_perturbation_model n A L_hat U_hat
      DeltaA_LU u)
    (h21 : higham9_21_tridiag_solve_perturbation_model n L_hat U_hat
      y_hat x_hat b DeltaL DeltaU u) :
    ∃ DeltaA : Fin n → Fin n → ℝ,
      (∀ i j, |DeltaA i j| ≤ higham9_14_h u * |A i j|) ∧
      (∀ i, ∑ j : Fin n, (A i j + DeltaA i j) * x_hat j = b i) := by
  obtain ⟨D₁, D₂, hD₁, hD₂, hA_eq⟩ :=
    higham9_12_sign_equiv_signDiag_witnesses hAB
  exact higham9_14_sign_equiv_source_h_bound_of_models
    n B L_B U_B D₁ D₂ hD₁ hD₂ hB_growth
    A L_hat U_hat hA_eq hL_abs hU_abs
    y_hat x_hat b u hu hu_lt_one DeltaA_LU DeltaL DeltaU h20 h21

/-- **Theorem 9.14**, source-predicate sign-equivalent model-consuming
`f(u)` bound. -/
theorem higham9_14_sign_equiv_source_f_bound_of_IsSignEquiv_models
    (n : ℕ)
    (A B L_B U_B L_hat U_hat : Fin n → Fin n → ℝ)
    (hAB : IsSignEquiv n A B)
    (hB_growth : ∀ i j : Fin n,
      ∑ k : Fin n, |L_B i k| * |U_B k j| = |B i j|)
    (hL_abs : ∀ i k : Fin n, |L_hat i k| = |L_B i k|)
    (hU_abs : ∀ k j : Fin n, |U_hat k j| = |U_B k j|)
    (y_hat x_hat b : Fin n → ℝ)
    (u : ℝ) (hu : 0 ≤ u)
    (DeltaA_LU DeltaL DeltaU : Fin n → Fin n → ℝ)
    (h20 : higham9_20_tridiag_lu_perturbation_model n A L_hat U_hat
      DeltaA_LU u)
    (h21 : higham9_21_tridiag_solve_perturbation_model n L_hat U_hat
      y_hat x_hat b DeltaL DeltaU u) :
    ∃ DeltaA : Fin n → Fin n → ℝ,
      (∀ i j, |DeltaA i j| ≤ higham9_14_f u * |A i j|) ∧
      (∀ i, ∑ j : Fin n, (A i j + DeltaA i j) * x_hat j = b i) := by
  obtain ⟨D₁, D₂, hD₁, hD₂, hA_eq⟩ :=
    higham9_12_sign_equiv_signDiag_witnesses hAB
  exact higham9_14_sign_equiv_source_f_bound_of_models
    n B L_B U_B D₁ D₂ hD₁ hD₂ hB_growth
    A L_hat U_hat hA_eq hL_abs hU_abs
    y_hat x_hat b u hu DeltaA_LU DeltaL DeltaU h20 h21

/-- **Theorem 9.14**, source-predicate sign-equivalent model-consuming final
bound specialized to the natural `γ_n` coefficient. -/
theorem higham9_14_sign_equiv_source_h_bound_of_IsSignEquiv_models_gamma
    (fp : FPModel) (n : ℕ)
    (A B L_B U_B L_hat U_hat : Fin n → Fin n → ℝ)
    (hAB : IsSignEquiv n A B)
    (hB_growth : ∀ i j : Fin n,
      ∑ k : Fin n, |L_B i k| * |U_B k j| = |B i j|)
    (hL_abs : ∀ i k : Fin n, |L_hat i k| = |L_B i k|)
    (hU_abs : ∀ k j : Fin n, |U_hat k j| = |U_B k j|)
    (y_hat x_hat b : Fin n → ℝ)
    (hn : gammaValid fp n)
    (hγ_lt_one : gamma fp n < 1)
    (DeltaA_LU DeltaL DeltaU : Fin n → Fin n → ℝ)
    (h20 : higham9_20_tridiag_lu_perturbation_model n A L_hat U_hat
      DeltaA_LU (gamma fp n))
    (h21 : higham9_21_tridiag_solve_perturbation_model n L_hat U_hat
      y_hat x_hat b DeltaL DeltaU (gamma fp n)) :
    ∃ DeltaA : Fin n → Fin n → ℝ,
      (∀ i j, |DeltaA i j| ≤
        higham9_14_h (gamma fp n) * |A i j|) ∧
      (∀ i, ∑ j : Fin n, (A i j + DeltaA i j) * x_hat j = b i) :=
  higham9_14_sign_equiv_source_h_bound_of_IsSignEquiv_models
    n A B L_B U_B L_hat U_hat hAB hB_growth hL_abs hU_abs
    y_hat x_hat b (gamma fp n) (gamma_nonneg fp hn) hγ_lt_one
    DeltaA_LU DeltaL DeltaU h20 h21

/-- **Theorem 9.14**, source-predicate sign-equivalent model-consuming
`f(γ_n)` bound. -/
theorem higham9_14_sign_equiv_source_f_bound_of_IsSignEquiv_models_gamma
    (fp : FPModel) (n : ℕ)
    (A B L_B U_B L_hat U_hat : Fin n → Fin n → ℝ)
    (hAB : IsSignEquiv n A B)
    (hB_growth : ∀ i j : Fin n,
      ∑ k : Fin n, |L_B i k| * |U_B k j| = |B i j|)
    (hL_abs : ∀ i k : Fin n, |L_hat i k| = |L_B i k|)
    (hU_abs : ∀ k j : Fin n, |U_hat k j| = |U_B k j|)
    (y_hat x_hat b : Fin n → ℝ)
    (hn : gammaValid fp n)
    (DeltaA_LU DeltaL DeltaU : Fin n → Fin n → ℝ)
    (h20 : higham9_20_tridiag_lu_perturbation_model n A L_hat U_hat
      DeltaA_LU (gamma fp n))
    (h21 : higham9_21_tridiag_solve_perturbation_model n L_hat U_hat
      y_hat x_hat b DeltaL DeltaU (gamma fp n)) :
    ∃ DeltaA : Fin n → Fin n → ℝ,
      (∀ i j, |DeltaA i j| ≤
        higham9_14_f (gamma fp n) * |A i j|) ∧
      (∀ i, ∑ j : Fin n, (A i j + DeltaA i j) * x_hat j = b i) :=
  higham9_14_sign_equiv_source_f_bound_of_IsSignEquiv_models
    n A B L_B U_B L_hat U_hat hAB hB_growth hL_abs hU_abs
    y_hat x_hat b (gamma fp n) (gamma_nonneg fp hn)
    DeltaA_LU DeltaL DeltaU h20 h21

/-- **Theorem 9.14**, source-predicate sign-equivalent exact-factor package
with actual triangular solves. -/
theorem higham9_14_sign_equiv_source_f_bound_actual_triangular_solves_of_IsSignEquiv
    (fp : FPModel) (n : ℕ)
    (A B L_B U_B L_hat U_hat : Fin n → Fin n → ℝ)
    (hAB : IsSignEquiv n A B)
    (hB_growth : ∀ i j : Fin n,
      ∑ k : Fin n, |L_B i k| * |U_B k j| = |B i j|)
    (hL_abs : ∀ i k : Fin n, |L_hat i k| = |L_B i k|)
    (hU_abs : ∀ k j : Fin n, |U_hat k j| = |U_B k j|)
    (b : Fin n → ℝ)
    (u : ℝ) (hu : 0 ≤ u)
    (hn : gammaValid fp n)
    (hγ_le_u : gamma fp n ≤ u)
    (hLU : LUFactSpec n A L_hat U_hat)
    (hdetA : Matrix.det (Matrix.of A : Matrix (Fin n) (Fin n) ℝ) ≠ 0) :
    let y_hat := fl_forwardSub fp n L_hat b
    let x_hat := fl_backSub fp n U_hat y_hat
    ∃ DeltaA : Fin n → Fin n → ℝ,
      (∀ i j, |DeltaA i j| ≤ higham9_14_f u * |A i j|) ∧
      (∀ i, ∑ j : Fin n, (A i j + DeltaA i j) * x_hat j = b i) := by
  obtain ⟨D₁, D₂, hD₁, hD₂, hA_eq⟩ :=
    higham9_12_sign_equiv_signDiag_witnesses hAB
  exact higham9_14_sign_equiv_source_f_bound_actual_triangular_solves
    fp n B L_B U_B D₁ D₂ hD₁ hD₂ hB_growth
    A L_hat U_hat hA_eq hL_abs hU_abs b u hu hn hγ_le_u hLU hdetA

/-- **Theorem 9.14**, source-predicate sign-equivalent exact-factor actual
solves with the natural `γ_n` coefficient. -/
theorem higham9_14_sign_equiv_source_f_bound_actual_triangular_solves_of_IsSignEquiv_gamma
    (fp : FPModel) (n : ℕ)
    (A B L_B U_B L_hat U_hat : Fin n → Fin n → ℝ)
    (hAB : IsSignEquiv n A B)
    (hB_growth : ∀ i j : Fin n,
      ∑ k : Fin n, |L_B i k| * |U_B k j| = |B i j|)
    (hL_abs : ∀ i k : Fin n, |L_hat i k| = |L_B i k|)
    (hU_abs : ∀ k j : Fin n, |U_hat k j| = |U_B k j|)
    (b : Fin n → ℝ)
    (hn : gammaValid fp n)
    (hLU : LUFactSpec n A L_hat U_hat)
    (hdetA : Matrix.det (Matrix.of A : Matrix (Fin n) (Fin n) ℝ) ≠ 0) :
    let y_hat := fl_forwardSub fp n L_hat b
    let x_hat := fl_backSub fp n U_hat y_hat
    ∃ DeltaA : Fin n → Fin n → ℝ,
      (∀ i j, |DeltaA i j| ≤ higham9_14_f (gamma fp n) * |A i j|) ∧
      (∀ i, ∑ j : Fin n, (A i j + DeltaA i j) * x_hat j = b i) :=
  higham9_14_sign_equiv_source_f_bound_actual_triangular_solves_of_IsSignEquiv
    fp n A B L_B U_B L_hat U_hat hAB hB_growth hL_abs hU_abs b
    (gamma fp n) (gamma_nonneg fp hn) hn le_rfl hLU hdetA

/-- **Theorem 9.14**, source-predicate sign-equivalent exact-factor package
with actual triangular solves and final `h(u)` bound. -/
theorem higham9_14_sign_equiv_source_h_bound_actual_triangular_solves_of_IsSignEquiv
    (fp : FPModel) (n : ℕ)
    (A B L_B U_B L_hat U_hat : Fin n → Fin n → ℝ)
    (hAB : IsSignEquiv n A B)
    (hB_growth : ∀ i j : Fin n,
      ∑ k : Fin n, |L_B i k| * |U_B k j| = |B i j|)
    (hL_abs : ∀ i k : Fin n, |L_hat i k| = |L_B i k|)
    (hU_abs : ∀ k j : Fin n, |U_hat k j| = |U_B k j|)
    (b : Fin n → ℝ)
    (u : ℝ) (hu : 0 ≤ u) (hu_lt_one : u < 1)
    (hn : gammaValid fp n)
    (hγ_le_u : gamma fp n ≤ u)
    (hLU : LUFactSpec n A L_hat U_hat)
    (hdetA : Matrix.det (Matrix.of A : Matrix (Fin n) (Fin n) ℝ) ≠ 0) :
    let y_hat := fl_forwardSub fp n L_hat b
    let x_hat := fl_backSub fp n U_hat y_hat
    ∃ DeltaA : Fin n → Fin n → ℝ,
      (∀ i j, |DeltaA i j| ≤ higham9_14_h u * |A i j|) ∧
      (∀ i, ∑ j : Fin n, (A i j + DeltaA i j) * x_hat j = b i) := by
  obtain ⟨D₁, D₂, hD₁, hD₂, hA_eq⟩ :=
    higham9_12_sign_equiv_signDiag_witnesses hAB
  exact higham9_14_sign_equiv_source_h_bound_actual_triangular_solves
    fp n B L_B U_B D₁ D₂ hD₁ hD₂ hB_growth
    A L_hat U_hat hA_eq hL_abs hU_abs b u hu hu_lt_one
    hn hγ_le_u hLU hdetA

/-- **Theorem 9.14**, source-predicate sign-equivalent exact-factor actual
solves with Higham's final `h(γ_n)` coefficient. -/
theorem higham9_14_sign_equiv_source_h_bound_actual_triangular_solves_of_IsSignEquiv_gamma
    (fp : FPModel) (n : ℕ)
    (A B L_B U_B L_hat U_hat : Fin n → Fin n → ℝ)
    (hAB : IsSignEquiv n A B)
    (hB_growth : ∀ i j : Fin n,
      ∑ k : Fin n, |L_B i k| * |U_B k j| = |B i j|)
    (hL_abs : ∀ i k : Fin n, |L_hat i k| = |L_B i k|)
    (hU_abs : ∀ k j : Fin n, |U_hat k j| = |U_B k j|)
    (b : Fin n → ℝ)
    (hn : gammaValid fp n)
    (hγ_lt_one : gamma fp n < 1)
    (hLU : LUFactSpec n A L_hat U_hat)
    (hdetA : Matrix.det (Matrix.of A : Matrix (Fin n) (Fin n) ℝ) ≠ 0) :
    let y_hat := fl_forwardSub fp n L_hat b
    let x_hat := fl_backSub fp n U_hat y_hat
    ∃ DeltaA : Fin n → Fin n → ℝ,
      (∀ i j, |DeltaA i j| ≤ higham9_14_h (gamma fp n) * |A i j|) ∧
      (∀ i, ∑ j : Fin n, (A i j + DeltaA i j) * x_hat j = b i) :=
  higham9_14_sign_equiv_source_h_bound_actual_triangular_solves_of_IsSignEquiv
    fp n A B L_B U_B L_hat U_hat hAB hB_growth hL_abs hU_abs b
    (gamma fp n) (gamma_nonneg fp hn) hγ_lt_one hn le_rfl hLU hdetA

/-- **Equation (9.23)**, nonnegativity of the Skeel condition number used as
Higham's `cond(A)` in the componentwise/row-wise forward-error route. -/
theorem higham9_23_condSkeel_nonneg (n : ℕ) (hn : 0 < n)
    (A A_inv : Fin n → Fin n → ℝ) :
    0 ≤ condSkeel n hn A A_inv := by
  let i0 : Fin n := ⟨0, hn⟩
  have hrow0 :
      0 ≤ ∑ j : Fin n, |A_inv i0 j| * (∑ k : Fin n, |A j k|) := by
    exact Finset.sum_nonneg fun j _ =>
      mul_nonneg (abs_nonneg _) (Finset.sum_nonneg fun k _ => abs_nonneg _)
  exact le_trans hrow0
    (by
      unfold condSkeel
      exact Finset.le_sup'
        (fun i => ∑ j : Fin n, |A_inv i j| * ∑ k : Fin n, |A j k|)
        (Finset.mem_univ i0))

/-- **Equation (9.23)**, exact denominator form of the forward-error bound
behind the displayed first-order estimate.

If the computed solution `x_hat` solves `(A + ΔA)x_hat = b` and the row-wise
backward error has already been converted to an entrywise source bound
`|ΔA| <= η |A|`, then the Chapter 7 relative infinity-norm theorem gives the
denominator form with Higham's `cond(A) = ‖|A⁻¹||A|‖∞`. -/
theorem higham9_23_forward_error_exact_condSkeel {n : ℕ} (hn : 0 < n)
    (A A_inv : Fin n → Fin n → ℝ) (x x_hat b : Fin n → ℝ)
    (ΔA : Fin n → Fin n → ℝ) (η : ℝ)
    (hη : 0 ≤ η)
    (hΔA : ∀ i j : Fin n, |ΔA i j| ≤ η * |A i j|)
    (hInv : IsLeftInverse n A A_inv)
    (hAx : ∀ i : Fin n, ∑ j : Fin n, A i j * x j = b i)
    (hPerturbed : ∀ i : Fin n,
      ∑ j : Fin n, (A i j + ΔA i j) * x_hat j = b i)
    (hηcond : η * condSkeel n hn A A_inv < 1)
    (hx : 0 < infNormVec x) :
    infNormVec (fun i => x i - x_hat i) / infNormVec x ≤
      η / (1 - η * condSkeel n hn A A_inv) *
        condSkeel n hn A A_inv := by
  have hM :
      ∀ i : Fin n,
        ∑ j : Fin n, |A_inv i j| * (∑ k : Fin n, |A j k|) ≤
          condSkeel n hn A A_inv := by
    intro i
    unfold condSkeel
    exact Finset.le_sup'
      (fun i' => ∑ j : Fin n, |A_inv i' j| * ∑ k : Fin n, |A j k|)
      (Finset.mem_univ i)
  have hmain :=
    componentwise_forward_error_exact_relative_infNorm n hn A A_inv x x_hat b
      ΔA (fun _ => 0) (fun i j => |A i j|) (fun _ => 0) η hη hΔA
      (by intro i; simp)
      (by intro i j; exact abs_nonneg _)
      (by intro i; simp)
      hInv hAx
      (by intro i; simpa using hPerturbed i)
      (condSkeel n hn A A_inv) hM hηcond hx
  have hsolution_cond :
      ch7ForwardBoundEF n hn A_inv (fun i j => |A i j|) (fun _ => 0) x /
          infNormVec x ≤ condSkeel n hn A A_inv := by
    simpa [ch7SkeelCondAtSolutionInf] using
      ch7SkeelCondAtSolutionInf_le_condSkeel n hn A A_inv x hx
  have hden_pos : 0 < 1 - η * condSkeel n hn A A_inv := by linarith
  have hcoef_nonneg :
      0 ≤ η / (1 - η * condSkeel n hn A A_inv) :=
    div_nonneg hη (le_of_lt hden_pos)
  exact hmain.trans (mul_le_mul_of_nonneg_left hsolution_cond hcoef_nonneg)

/-- **Equation (9.23)**, scalar first-order denominator expansion.

This is the algebraic meaning of the source's `+ O(u^2)` term: if the
effective row-wise backward-error coefficient satisfies
`η <= 3 n u cond(U)`, then the exact denominator form is bounded by
`3 n u cond(A) cond(U)` plus an explicit nonnegative multiple of `u^2`. -/
theorem higham9_23_firstOrderLe_of_backward_error_coeff {n : ℕ}
    {u η condA condU value : ℝ}
    (hu : 0 ≤ u) (hη : 0 ≤ η) (hcondA : 0 ≤ condA) (hcondU : 0 ≤ condU)
    (hη_le : η ≤ 3 * (n : ℝ) * u * condU)
    (hηcond : η * condA < 1)
    (hvalue : value ≤ η / (1 - η * condA) * condA) :
    FirstOrderLe u (3 * (n : ℝ) * u * condA * condU) value := by
  let C : ℝ := 3 * (n : ℝ) * condU
  have hC_nonneg : 0 ≤ C := by
    dsimp [C]
    positivity
  have hCu_nonneg : 0 ≤ C * u := mul_nonneg hC_nonneg hu
  have hη_le_Cu : η ≤ C * u := by
    dsimp [C]
    nlinarith
  let a : ℝ := η * condA
  let b : ℝ := C * u * condA
  have ha_nonneg : 0 ≤ a := mul_nonneg hη hcondA
  have hb_nonneg : 0 ≤ b := mul_nonneg hCu_nonneg hcondA
  have hab : a ≤ b := by
    dsimp [a, b]
    exact mul_le_mul_of_nonneg_right hη_le_Cu hcondA
  have hden_pos : 0 < 1 - a := by
    dsimp [a]
    linarith
  let K : ℝ := C ^ 2 * condA ^ 2 / (1 - a)
  refine ⟨K, ?_, ?_⟩
  · dsimp [K]
    exact div_nonneg (mul_nonneg (sq_nonneg C) (sq_nonneg condA))
      (le_of_lt hden_pos)
  · have hden_bound :
        η / (1 - η * condA) * condA ≤
          3 * (n : ℝ) * u * condA * condU + K * u ^ 2 := by
      calc
        η / (1 - η * condA) * condA
            = a / (1 - a) := by
              dsimp [a]
              ring
        _ ≤ b / (1 - a) :=
              div_le_div_of_nonneg_right hab (le_of_lt hden_pos)
        _ = b + a * b / (1 - a) := by
              field_simp [ne_of_gt hden_pos]
              ring
        _ ≤ b + b * b / (1 - a) := by
              apply add_le_add le_rfl
              exact div_le_div_of_nonneg_right
                (mul_le_mul_of_nonneg_right hab hb_nonneg)
                (le_of_lt hden_pos)
        _ = 3 * (n : ℝ) * u * condA * condU + K * u ^ 2 := by
              dsimp [a, b, C, K]
              field_simp [ne_of_gt hden_pos]
    exact hvalue.trans hden_bound

/-- **Equation (9.23)**, source-shaped first-order forward-error wrapper.

The theorem combines the exact Chapter 7 denominator bound with the source
row-wise backward-error estimate `η <= 3 n u cond(U)`, producing the displayed
`3 n u cond(A) cond(U) + O(u^2)` shape through `FirstOrderLe`. -/
theorem higham9_23_forward_error_firstOrder_cond_product {n : ℕ} (hn : 0 < n)
    (A A_inv : Fin n → Fin n → ℝ) (x x_hat b : Fin n → ℝ)
    (ΔA : Fin n → Fin n → ℝ) (η condU u : ℝ)
    (hu : 0 ≤ u) (hη : 0 ≤ η) (hcondU : 0 ≤ condU)
    (hη_le : η ≤ 3 * (n : ℝ) * u * condU)
    (hΔA : ∀ i j : Fin n, |ΔA i j| ≤ η * |A i j|)
    (hInv : IsLeftInverse n A A_inv)
    (hAx : ∀ i : Fin n, ∑ j : Fin n, A i j * x j = b i)
    (hPerturbed : ∀ i : Fin n,
      ∑ j : Fin n, (A i j + ΔA i j) * x_hat j = b i)
    (hηcond : η * condSkeel n hn A A_inv < 1)
    (hx : 0 < infNormVec x) :
    FirstOrderLe u
      (3 * (n : ℝ) * u * condSkeel n hn A A_inv * condU)
      (infNormVec (fun i => x i - x_hat i) / infNormVec x) := by
  exact higham9_23_firstOrderLe_of_backward_error_coeff
    (n := n) hu hη (higham9_23_condSkeel_nonneg n hn A A_inv) hcondU
    hη_le hηcond
    (higham9_23_forward_error_exact_condSkeel hn A A_inv x x_hat b
      ΔA η hη hΔA hInv hAx hPerturbed hηcond hx)

/-- **Equation (9.23)**, exact denominator form from an already established
row-wise backward-error certificate.

This source-facing wrapper consumes the existential perturbation package
produced by Chapter 9 backward-error theorems, so callers do not have to expose
the witness `ΔA` at the final forward-error surface. -/
theorem higham9_23_forward_error_exact_condSkeel_of_backward_error {n : ℕ}
    (hn : 0 < n)
    (A A_inv : Fin n → Fin n → ℝ) (x x_hat b : Fin n → ℝ) (η : ℝ)
    (hη : 0 ≤ η)
    (hBackward :
      ∃ ΔA : Fin n → Fin n → ℝ,
        (∀ i j : Fin n, |ΔA i j| ≤ η * |A i j|) ∧
        (∀ i : Fin n, ∑ j : Fin n, (A i j + ΔA i j) * x_hat j = b i))
    (hInv : IsLeftInverse n A A_inv)
    (hAx : ∀ i : Fin n, ∑ j : Fin n, A i j * x j = b i)
    (hηcond : η * condSkeel n hn A A_inv < 1)
    (hx : 0 < infNormVec x) :
    infNormVec (fun i => x i - x_hat i) / infNormVec x ≤
      η / (1 - η * condSkeel n hn A A_inv) *
        condSkeel n hn A A_inv := by
  obtain ⟨ΔA, hΔA, hPerturbed⟩ := hBackward
  exact higham9_23_forward_error_exact_condSkeel hn A A_inv x x_hat b
    ΔA η hη hΔA hInv hAx hPerturbed hηcond hx

/-- **Equation (9.23)**, source-shaped first-order forward-error wrapper from
an existential row-wise backward-error certificate. -/
theorem higham9_23_forward_error_firstOrder_cond_product_of_backward_error
    {n : ℕ} (hn : 0 < n)
    (A A_inv : Fin n → Fin n → ℝ) (x x_hat b : Fin n → ℝ)
    (η condU u : ℝ)
    (hu : 0 ≤ u) (hη : 0 ≤ η) (hcondU : 0 ≤ condU)
    (hη_le : η ≤ 3 * (n : ℝ) * u * condU)
    (hBackward :
      ∃ ΔA : Fin n → Fin n → ℝ,
        (∀ i j : Fin n, |ΔA i j| ≤ η * |A i j|) ∧
        (∀ i : Fin n, ∑ j : Fin n, (A i j + ΔA i j) * x_hat j = b i))
    (hInv : IsLeftInverse n A A_inv)
    (hAx : ∀ i : Fin n, ∑ j : Fin n, A i j * x j = b i)
    (hηcond : η * condSkeel n hn A A_inv < 1)
    (hx : 0 < infNormVec x) :
    FirstOrderLe u
      (3 * (n : ℝ) * u * condSkeel n hn A A_inv * condU)
      (infNormVec (fun i => x i - x_hat i) / infNormVec x) := by
  obtain ⟨ΔA, hΔA, hPerturbed⟩ := hBackward
  exact higham9_23_forward_error_firstOrder_cond_product hn A A_inv x x_hat b
    ΔA η condU u hu hη hcondU hη_le hΔA hInv hAx hPerturbed hηcond hx

/-- **Equation (9.23)**, Matrix-vector form of the exact denominator forward
error bound. -/
theorem higham9_23_matrix_forward_error_exact_condSkeel {n : ℕ} (hn : 0 < n)
    (A A_inv : Matrix (Fin n) (Fin n) ℝ) (x x_hat b : Fin n → ℝ)
    (ΔA : Matrix (Fin n) (Fin n) ℝ) (η : ℝ)
    (hη : 0 ≤ η)
    (hΔA : ∀ i j : Fin n, |ΔA i j| ≤ η * |A i j|)
    (hInv : IsLeftInverse n A A_inv)
    (hAx : Matrix.mulVec A x = b)
    (hPerturbed : Matrix.mulVec (fun i j => A i j + ΔA i j) x_hat = b)
    (hηcond : η * condSkeel n hn A A_inv < 1)
    (hx : 0 < infNormVec x) :
    infNormVec (fun i => x i - x_hat i) / infNormVec x ≤
      η / (1 - η * condSkeel n hn A A_inv) *
        condSkeel n hn A A_inv := by
  have hAx_entries : ∀ i : Fin n, ∑ j : Fin n, A i j * x j = b i := by
    intro i
    simpa [Matrix.mulVec, dotProduct] using congrFun hAx i
  have hPerturbed_entries :
      ∀ i : Fin n, ∑ j : Fin n, (A i j + ΔA i j) * x_hat j = b i := by
    intro i
    simpa [Matrix.mulVec, dotProduct] using congrFun hPerturbed i
  exact higham9_23_forward_error_exact_condSkeel hn A A_inv x x_hat b
    ΔA η hη hΔA hInv hAx_entries hPerturbed_entries hηcond hx

/-- **Equation (9.23)**, Matrix-vector form of the first-order forward-error
wrapper. -/
theorem higham9_23_matrix_forward_error_firstOrder_cond_product {n : ℕ}
    (hn : 0 < n)
    (A A_inv : Matrix (Fin n) (Fin n) ℝ) (x x_hat b : Fin n → ℝ)
    (ΔA : Matrix (Fin n) (Fin n) ℝ) (η condU u : ℝ)
    (hu : 0 ≤ u) (hη : 0 ≤ η) (hcondU : 0 ≤ condU)
    (hη_le : η ≤ 3 * (n : ℝ) * u * condU)
    (hΔA : ∀ i j : Fin n, |ΔA i j| ≤ η * |A i j|)
    (hInv : IsLeftInverse n A A_inv)
    (hAx : Matrix.mulVec A x = b)
    (hPerturbed : Matrix.mulVec (fun i j => A i j + ΔA i j) x_hat = b)
    (hηcond : η * condSkeel n hn A A_inv < 1)
    (hx : 0 < infNormVec x) :
    FirstOrderLe u
      (3 * (n : ℝ) * u * condSkeel n hn A A_inv * condU)
      (infNormVec (fun i => x i - x_hat i) / infNormVec x) := by
  have hAx_entries : ∀ i : Fin n, ∑ j : Fin n, A i j * x j = b i := by
    intro i
    simpa [Matrix.mulVec, dotProduct] using congrFun hAx i
  have hPerturbed_entries :
      ∀ i : Fin n, ∑ j : Fin n, (A i j + ΔA i j) * x_hat j = b i := by
    intro i
    simpa [Matrix.mulVec, dotProduct] using congrFun hPerturbed i
  exact higham9_23_forward_error_firstOrder_cond_product hn A A_inv x x_hat b
    ΔA η condU u hu hη hcondU hη_le hΔA hInv hAx_entries
    hPerturbed_entries hηcond hx

/-- **Equation (9.23)**, Matrix-vector exact denominator form from an
existential row-wise backward-error certificate. -/
theorem higham9_23_matrix_forward_error_exact_condSkeel_of_backward_error
    {n : ℕ} (hn : 0 < n)
    (A A_inv : Matrix (Fin n) (Fin n) ℝ) (x x_hat b : Fin n → ℝ) (η : ℝ)
    (hη : 0 ≤ η)
    (hBackward :
      ∃ ΔA : Matrix (Fin n) (Fin n) ℝ,
        (∀ i j : Fin n, |ΔA i j| ≤ η * |A i j|) ∧
        Matrix.mulVec (fun i j => A i j + ΔA i j) x_hat = b)
    (hInv : IsLeftInverse n A A_inv)
    (hAx : Matrix.mulVec A x = b)
    (hηcond : η * condSkeel n hn A A_inv < 1)
    (hx : 0 < infNormVec x) :
    infNormVec (fun i => x i - x_hat i) / infNormVec x ≤
      η / (1 - η * condSkeel n hn A A_inv) *
        condSkeel n hn A A_inv := by
  obtain ⟨ΔA, hΔA, hPerturbed⟩ := hBackward
  exact higham9_23_matrix_forward_error_exact_condSkeel hn A A_inv x x_hat b
    ΔA η hη hΔA hInv hAx hPerturbed hηcond hx

/-- **Equation (9.23)**, Matrix-vector first-order wrapper from an existential
row-wise backward-error certificate. -/
theorem higham9_23_matrix_forward_error_firstOrder_cond_product_of_backward_error
    {n : ℕ} (hn : 0 < n)
    (A A_inv : Matrix (Fin n) (Fin n) ℝ) (x x_hat b : Fin n → ℝ)
    (η condU u : ℝ)
    (hu : 0 ≤ u) (hη : 0 ≤ η) (hcondU : 0 ≤ condU)
    (hη_le : η ≤ 3 * (n : ℝ) * u * condU)
    (hBackward :
      ∃ ΔA : Matrix (Fin n) (Fin n) ℝ,
        (∀ i j : Fin n, |ΔA i j| ≤ η * |A i j|) ∧
        Matrix.mulVec (fun i j => A i j + ΔA i j) x_hat = b)
    (hInv : IsLeftInverse n A A_inv)
    (hAx : Matrix.mulVec A x = b)
    (hηcond : η * condSkeel n hn A A_inv < 1)
    (hx : 0 < infNormVec x) :
    FirstOrderLe u
      (3 * (n : ℝ) * u * condSkeel n hn A A_inv * condU)
      (infNormVec (fun i => x i - x_hat i) / infNormVec x) := by
  obtain ⟨ΔA, hΔA, hPerturbed⟩ := hBackward
  exact higham9_23_matrix_forward_error_firstOrder_cond_product
    hn A A_inv x x_hat b ΔA η condU u hu hη hcondU hη_le hΔA
    hInv hAx hPerturbed hηcond hx

/-- **Equation (9.24)**: two-sided diagonal scaling of the coefficient matrix. -/
noncomputable def higham9_24_scaledMatrix {n : ℕ}
    (D1 D2 : Fin n → ℝ) (A : Fin n → Fin n → ℝ) : Fin n → Fin n → ℝ :=
  fun i j => D1 i * A i j * D2 j

end NumStability
