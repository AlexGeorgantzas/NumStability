import Mathlib.Data.Real.Basic
import Mathlib.Tactic
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Ring
import NumStability.Algorithms.MatMul
import NumStability.Analysis.ForwardError
import NumStability.Analysis.MatrixAlgebra
import NumStability.Analysis.Rounding
import NumStability.FloatingPoint.Model

/-!
# NumStability Algorithms PolynomialEvaluation MatrixNorms

Canonical destination for material split out of
`NumStability.Algorithms.Horner` by wave W12 of the August 2026 repository reorganization.
Declaration names, statements and proofs are unchanged; only the
module they live in has changed. The historical module still
resolves and re-exports this one.
-/

open scoped BigOperators

namespace NumStability

/-- Zero square matrix in the repository's function-shaped matrix
representation. -/
noncomputable def zeroMatrix (n : ℕ) : Fin n → Fin n → ℝ :=
  fun _ _ => 0

/-- Pointwise matrix addition in the repository's function-shaped matrix
representation. -/
noncomputable def matAdd (n : ℕ)
    (A B : Fin n → Fin n → ℝ) : Fin n → Fin n → ℝ :=
  fun i j => A i j + B i j

lemma infNorm_zeroMatrix (n : ℕ) :
    infNorm (zeroMatrix n) = 0 := by
  apply le_antisymm
  · apply infNorm_le_of_row_sum_le
    · intro i
      simp [zeroMatrix]
    · norm_num
  · exact infNorm_nonneg _

lemma infNorm_add_le {n : ℕ}
    (A B : Fin n → Fin n → ℝ) :
    infNorm (fun i j => A i j + B i j) ≤ infNorm A + infNorm B := by
  apply infNorm_le_of_row_sum_le
  · intro i
    calc
      (∑ j : Fin n, |A i j + B i j|)
          ≤ ∑ j : Fin n, (|A i j| + |B i j|) :=
            Finset.sum_le_sum (fun j _ => abs_add_le (A i j) (B i j))
      _ = (∑ j : Fin n, |A i j|) + ∑ j : Fin n, |B i j| := by
            rw [Finset.sum_add_distrib]
      _ ≤ infNorm A + infNorm B :=
            add_le_add (row_sum_le_infNorm A i) (row_sum_le_infNorm B i)
  · exact add_nonneg (infNorm_nonneg A) (infNorm_nonneg B)

lemma oneNorm_add_le {n : ℕ}
    (A B : Fin n → Fin n → ℝ) :
    oneNorm (fun i j => A i j + B i j) ≤ oneNorm A + oneNorm B := by
  apply oneNorm_le_of_col_sum_le
  · intro j
    calc
      (∑ i : Fin n, |A i j + B i j|)
          ≤ ∑ i : Fin n, (|A i j| + |B i j|) :=
            Finset.sum_le_sum (fun i _ => abs_add_le (A i j) (B i j))
      _ = (∑ i : Fin n, |A i j|) + ∑ i : Fin n, |B i j| := by
            rw [Finset.sum_add_distrib]
      _ ≤ oneNorm A + oneNorm B :=
            add_le_add (col_sum_le_oneNorm A j) (col_sum_le_oneNorm B j)
  · exact add_nonneg (oneNorm_nonneg A) (oneNorm_nonneg B)

lemma fl_matAdd_infNorm_error_bound
    (fp : FPModel) (n : ℕ)
    (A B : Fin n → Fin n → ℝ) :
    infNorm
        (fun i j => fp.fl_add (A i j) (B i j) - matAdd n A B i j) ≤
      fp.u * infNorm (matAdd n A B) := by
  apply infNorm_le_of_row_sum_le
  · intro i
    have hentry : ∀ j : Fin n,
        |fp.fl_add (A i j) (B i j) - matAdd n A B i j| ≤
          fp.u * |matAdd n A B i j| := by
      intro j
      obtain ⟨δ, hδ, hadd⟩ := fp.model_add (A i j) (B i j)
      have hdiff :
          fp.fl_add (A i j) (B i j) - matAdd n A B i j =
            matAdd n A B i j * δ := by
        rw [hadd]
        simp [matAdd]
        ring
      calc
        |fp.fl_add (A i j) (B i j) - matAdd n A B i j|
            = |matAdd n A B i j| * |δ| := by
              rw [hdiff, abs_mul]
        _ ≤ |matAdd n A B i j| * fp.u :=
              mul_le_mul_of_nonneg_left hδ (abs_nonneg _)
        _ = fp.u * |matAdd n A B i j| := by ring
    calc
      (∑ j : Fin n,
          |fp.fl_add (A i j) (B i j) - matAdd n A B i j|)
          ≤ ∑ j : Fin n, fp.u * |matAdd n A B i j| :=
            Finset.sum_le_sum (fun j _ => hentry j)
      _ = fp.u * ∑ j : Fin n, |matAdd n A B i j| := by
            rw [Finset.mul_sum]
      _ ≤ fp.u * infNorm (matAdd n A B) :=
            mul_le_mul_of_nonneg_left
              (row_sum_le_infNorm (matAdd n A B) i) fp.u_nonneg
  · exact mul_nonneg fp.u_nonneg (infNorm_nonneg _)

lemma fl_matAdd_oneNorm_error_bound
    (fp : FPModel) (n : ℕ)
    (A B : Fin n → Fin n → ℝ) :
    oneNorm
        (fun i j => fp.fl_add (A i j) (B i j) - matAdd n A B i j) ≤
      fp.u * oneNorm (matAdd n A B) := by
  apply oneNorm_le_of_col_sum_le
  · intro j
    have hentry : ∀ i : Fin n,
        |fp.fl_add (A i j) (B i j) - matAdd n A B i j| ≤
          fp.u * |matAdd n A B i j| := by
      intro i
      obtain ⟨δ, hδ, hadd⟩ := fp.model_add (A i j) (B i j)
      have hdiff :
          fp.fl_add (A i j) (B i j) - matAdd n A B i j =
            matAdd n A B i j * δ := by
        rw [hadd]
        simp [matAdd]
        ring
      calc
        |fp.fl_add (A i j) (B i j) - matAdd n A B i j|
            = |matAdd n A B i j| * |δ| := by
              rw [hdiff, abs_mul]
        _ ≤ |matAdd n A B i j| * fp.u :=
              mul_le_mul_of_nonneg_left hδ (abs_nonneg _)
        _ = fp.u * |matAdd n A B i j| := by ring
    calc
      (∑ i : Fin n,
          |fp.fl_add (A i j) (B i j) - matAdd n A B i j|)
          ≤ ∑ i : Fin n, fp.u * |matAdd n A B i j| :=
            Finset.sum_le_sum (fun i _ => hentry i)
      _ = fp.u * ∑ i : Fin n, |matAdd n A B i j| := by
            rw [Finset.mul_sum]
      _ ≤ fp.u * oneNorm (matAdd n A B) :=
            mul_le_mul_of_nonneg_left
              (col_sum_le_oneNorm (matAdd n A B) j) fp.u_nonneg
  · exact mul_nonneg fp.u_nonneg (oneNorm_nonneg _)

theorem fl_matMul_infNorm_error_bound
    (fp : FPModel) (n : ℕ)
    (A B : Fin n → Fin n → ℝ)
    (hn : gammaValid fp n) :
    infNorm
        (fun i j =>
          fl_matMul fp n n n A B i j - matMul n A B i j) ≤
      gamma fp n * infNorm A * infNorm B := by
  have hγ : 0 ≤ gamma fp n := gamma_nonneg fp hn
  have hA : 0 ≤ infNorm A := infNorm_nonneg A
  have hB : 0 ≤ infNorm B := infNorm_nonneg B
  apply infNorm_le_of_row_sum_le
  · intro i
    have hcomp_sum :
        (∑ j : Fin n,
          |fl_matMul fp n n n A B i j - matMul n A B i j|) ≤
          ∑ j : Fin n, gamma fp n * ∑ k : Fin n, |A i k| * |B k j| := by
      apply Finset.sum_le_sum
      intro j _
      simpa [matMul] using matMul_error_bound fp n n n A B hn i j
    have hdouble :
        (∑ j : Fin n, ∑ k : Fin n, |A i k| * |B k j|) =
          ∑ k : Fin n, |A i k| * ∑ j : Fin n, |B k j| := by
      rw [Finset.sum_comm]
      apply Finset.sum_congr rfl
      intro k _
      rw [Finset.mul_sum]
    have hdouble_bound :
        (∑ j : Fin n, ∑ k : Fin n, |A i k| * |B k j|) ≤
          (∑ k : Fin n, |A i k|) * infNorm B := by
      rw [hdouble]
      calc
        ∑ k : Fin n, |A i k| * ∑ j : Fin n, |B k j|
            ≤ ∑ k : Fin n, |A i k| * infNorm B :=
                Finset.sum_le_sum (fun k _ =>
                  mul_le_mul_of_nonneg_left
                    (row_sum_le_infNorm B k) (abs_nonneg _))
        _ = (∑ k : Fin n, |A i k|) * infNorm B := by
                rw [Finset.sum_mul]
    calc
      (∑ j : Fin n,
          |fl_matMul fp n n n A B i j - matMul n A B i j|)
          ≤ ∑ j : Fin n, gamma fp n * ∑ k : Fin n, |A i k| * |B k j| :=
            hcomp_sum
      _ = gamma fp n * (∑ j : Fin n, ∑ k : Fin n, |A i k| * |B k j|) := by
            rw [← Finset.mul_sum]
      _ ≤ gamma fp n * ((∑ k : Fin n, |A i k|) * infNorm B) :=
            mul_le_mul_of_nonneg_left hdouble_bound hγ
      _ ≤ gamma fp n * (infNorm A * infNorm B) := by
            have hrowA : ∑ k : Fin n, |A i k| ≤ infNorm A :=
              row_sum_le_infNorm A i
            have hprod : (∑ k : Fin n, |A i k|) * infNorm B ≤
                infNorm A * infNorm B :=
              mul_le_mul_of_nonneg_right hrowA hB
            exact mul_le_mul_of_nonneg_left hprod hγ
      _ = gamma fp n * infNorm A * infNorm B := by ring
  · exact mul_nonneg (mul_nonneg hγ hA) hB

theorem fl_matMul_oneNorm_error_bound
    (fp : FPModel) (n : ℕ)
    (A B : Fin n → Fin n → ℝ)
    (hn : gammaValid fp n) :
    oneNorm
        (fun i j =>
          fl_matMul fp n n n A B i j - matMul n A B i j) ≤
      gamma fp n * oneNorm A * oneNorm B := by
  simpa [matMul] using matMul_error_bound_oneNorm fp n A B hn

lemma oneNorm_matMul_le {n : ℕ}
    (A B : Fin n → Fin n → ℝ) :
    oneNorm (matMul n A B) ≤ oneNorm A * oneNorm B := by
  apply oneNorm_le_of_col_sum_le
  · intro j
    have hsum :
        (∑ i : Fin n, |matMul n A B i j|) ≤
          ∑ i : Fin n, ∑ k : Fin n, |A i k| * |B k j| := by
      apply Finset.sum_le_sum
      intro i _
      calc
        |matMul n A B i j|
            = |∑ k : Fin n, A i k * B k j| := by rfl
        _ ≤ ∑ k : Fin n, |A i k * B k j| :=
            Finset.abs_sum_le_sum_abs _ _
        _ = ∑ k : Fin n, |A i k| * |B k j| := by
            apply Finset.sum_congr rfl
            intro k _
            rw [abs_mul]
    have hdouble :
        (∑ i : Fin n, ∑ k : Fin n, |A i k| * |B k j|) =
          ∑ k : Fin n, |B k j| * ∑ i : Fin n, |A i k| := by
      rw [Finset.sum_comm]
      apply Finset.sum_congr rfl
      intro k _
      rw [← Finset.sum_mul]
      ring
    have hdouble_bound :
        (∑ i : Fin n, ∑ k : Fin n, |A i k| * |B k j|) ≤
          oneNorm A * ∑ k : Fin n, |B k j| := by
      rw [hdouble]
      calc
        ∑ k : Fin n, |B k j| * ∑ i : Fin n, |A i k|
            ≤ ∑ k : Fin n, |B k j| * oneNorm A :=
                Finset.sum_le_sum (fun k _ =>
                  mul_le_mul_of_nonneg_left
                    (col_sum_le_oneNorm A k) (abs_nonneg _))
        _ = oneNorm A * ∑ k : Fin n, |B k j| := by
                rw [← Finset.sum_mul]
                ring
    calc
      (∑ i : Fin n, |matMul n A B i j|)
          ≤ ∑ i : Fin n, ∑ k : Fin n, |A i k| * |B k j| := hsum
      _ ≤ oneNorm A * ∑ k : Fin n, |B k j| := hdouble_bound
      _ ≤ oneNorm A * oneNorm B :=
            mul_le_mul_of_nonneg_left
              (col_sum_le_oneNorm B j) (oneNorm_nonneg A)
  · exact mul_nonneg (oneNorm_nonneg A) (oneNorm_nonneg B)

lemma oneNorm_matPow_le {n : ℕ}
    (M : Fin n → Fin n → ℝ) (k : ℕ) :
    oneNorm (matPow n M k) ≤ oneNorm M ^ k := by
  induction k with
  | zero =>
      simp only [matPow, pow_zero]
      apply oneNorm_le_of_col_sum_le
      · intro j
        unfold idMatrix
        have hentry : ∀ i : Fin n,
            |if i = j then (1 : ℝ) else 0| =
              if i = j then 1 else 0 := by
          intro i
          split <;> simp
        simp_rw [hentry]
        calc
          (∑ i : Fin n, if i = j then (1 : ℝ) else 0) = 1 := by
            rw [Finset.sum_eq_single j]
            · simp
            · intro i _ hij
              simp [hij]
            · intro hj
              exact False.elim (hj (Finset.mem_univ j))
          _ ≤ 1 := le_rfl
      · norm_num
  | succ k ih =>
      have hM : 0 ≤ oneNorm M := oneNorm_nonneg M
      calc
        oneNorm (matPow n M (k + 1))
            = oneNorm (matMul n M (matPow n M k)) := by
              rw [matPow_succ]
        _ ≤ oneNorm M * oneNorm (matPow n M k) :=
              oneNorm_matMul_le M (matPow n M k)
        _ ≤ oneNorm M * oneNorm M ^ k :=
              mul_le_mul_of_nonneg_left ih hM
        _ = oneNorm M ^ (k + 1) := by ring

lemma infNorm_le_sub_add {n : ℕ}
    (A B : Fin n → Fin n → ℝ) :
    infNorm A ≤ infNorm (fun i j => A i j - B i j) + infNorm B := by
  calc
    infNorm A =
        infNorm (fun i j => (A i j - B i j) + B i j) := by
          congr 1
          ext i j
          ring
    _ ≤ infNorm (fun i j => A i j - B i j) + infNorm B :=
        infNorm_add_le (fun i j => A i j - B i j) B

lemma oneNorm_le_sub_add {n : ℕ}
    (A B : Fin n → Fin n → ℝ) :
    oneNorm A ≤ oneNorm (fun i j => A i j - B i j) + oneNorm B := by
  calc
    oneNorm A =
        oneNorm (fun i j => (A i j - B i j) + B i j) := by
          congr 1
          ext i j
          ring
    _ ≤ oneNorm (fun i j => A i j - B i j) + oneNorm B :=
        oneNorm_add_le (fun i j => A i j - B i j) B

/-- Rounded matrix addition, entry by entry. -/
noncomputable def fl_matAdd (fp : FPModel) (n : ℕ)
    (A B : Fin n → Fin n → ℝ) : Fin n → Fin n → ℝ :=
  fun i j => fp.fl_add (A i j) (B i j)

end NumStability
