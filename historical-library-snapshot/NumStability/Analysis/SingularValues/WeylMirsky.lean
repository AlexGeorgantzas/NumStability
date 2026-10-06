/-
SPDX-License-Identifier: MIT
-/

import Mathlib.Analysis.CStarAlgebra.Module.Constructions
import Mathlib.LinearAlgebra.Dimension.Constructions
import Mathlib.LinearAlgebra.FiniteDimensional.Lemmas
import Mathlib.Order.Interval.Finset.Fin
import NumStability.Analysis.SingularValues.Basic

/-!
# Weyl--Mirsky singular-value perturbation

This reusable analysis module proves all-index perturbation bounds for ordered
singular values of finite complex matrices. It develops the required
Courant--Fischer leading- and trailing-subspace estimates directly from the
repository's Gram eigenbasis, then derives one-sided and absolute Weyl--Mirsky
bounds from a pointwise Euclidean-operator perturbation estimate.

The historical `ch14ext_` declaration names and the
`NumStability.Ch14Ext` namespace are retained for compatibility. Source-
specific real-matrix and determinant consequences live in
`NumStability.Source.Higham.Chapter14.Problem15`.
-/

open scoped BigOperators

namespace NumStability.Ch14Ext

/-- Elementary square-root monotonicity used to pass from squared to unsquared
    norm inequalities. -/
private theorem ch14ext_le_of_sq_le_sq {a b : ℝ} (ha : 0 ≤ a) (hb : 0 ≤ b)
    (h : a ^ 2 ≤ b ^ 2) : a ≤ b := by
  have hsqrt := Real.sqrt_le_sqrt h
  rwa [Real.sqrt_sq ha, Real.sqrt_sq hb] at hsqrt

/-- If `x` lies in the span of an orthonormal-basis subfamily indexed by `s`,
    then its inner product with any basis vector outside `s` vanishes. -/
private theorem ch14ext_inner_eq_zero_of_mem_span {n : ℕ}
    (b : OrthonormalBasis (Fin n) ℂ (EuclideanSpace ℂ (Fin n)))
    (s : Set (Fin n)) {x : EuclideanSpace ℂ (Fin n)}
    (hx : x ∈ Submodule.span ℂ (b '' s)) {j : Fin n} (hj : j ∉ s) :
    inner ℂ (b j) x = 0 := by
  classical
  refine Submodule.span_induction (p := fun y _ => inner ℂ (b j) y = 0) ?_ ?_ ?_ ?_ hx
  · rintro y ⟨l, hl, rfl⟩
    have hjl : j ≠ l := by rintro rfl; exact hj hl
    rw [orthonormal_iff_ite.mp b.orthonormal j l]
    simp [hjl]
  · simp
  · intro u v _ _ ihu ihv
    simp [ihu, ihv]
  · intro a u _ ih
    simp [ih]

/-- Coordinate form of the previous lemma: the eigenbasis coordinate of `x`
    at any index outside the spanning set is `0`. -/
private theorem ch14ext_repr_eq_zero_of_mem_span {n : ℕ}
    (b : OrthonormalBasis (Fin n) ℂ (EuclideanSpace ℂ (Fin n)))
    (s : Set (Fin n)) {x : EuclideanSpace ℂ (Fin n)}
    (hx : x ∈ Submodule.span ℂ (b '' s)) {j : Fin n} (hj : j ∉ s) :
    b.repr x j = 0 := by
  rw [OrthonormalBasis.repr_apply_apply]
  exact ch14ext_inner_eq_zero_of_mem_span b s hx hj

/-- Parseval identity for an orthonormal basis. -/
private theorem ch14ext_sum_repr_norm_sq {n : ℕ}
    (b : OrthonormalBasis (Fin n) ℂ (EuclideanSpace ℂ (Fin n)))
    (x : EuclideanSpace ℂ (Fin n)) :
    ∑ j : Fin n, ‖b.repr x j‖ ^ 2 = ‖x‖ ^ 2 := by
  simpa [OrthonormalBasis.repr_apply_apply] using b.sum_sq_norm_inner_right x

/-- **Courant–Fischer, leading half.** On the span of the first `i+1` Gram
    eigenvectors of `A`, the Euclidean action of `A` is bounded below by
    `σ_i(A)·‖x‖`.  Higham, 2nd ed., Problem 14.15 (min–max input). -/
theorem ch14ext_singularValue_mul_norm_le_norm_euclideanLin_of_mem_leadSpan
    {m n : ℕ} (A : CMatrix m n) (i : Fin n) {x : EuclideanSpace ℂ (Fin n)}
    (hx : x ∈ Submodule.span ℂ
      (⇑(complexMatrixGramEigenvectorBasis A) '' (↑(Finset.Iic i) : Set (Fin n)))) :
    complexMatrixSingularValue A i * ‖x‖ ≤ ‖complexMatrixEuclideanLin A x‖ := by
  have hzero : ∀ j : Fin n, ¬ (j ≤ i) →
      (complexMatrixGramEigenvectorBasis A).repr x j = 0 := by
    intro j hji
    refine ch14ext_repr_eq_zero_of_mem_span (complexMatrixGramEigenvectorBasis A) _ hx ?_
    simp only [Finset.coe_Iic, Set.mem_Iic]
    exact hji
  have hterm : ∀ j : Fin n,
      complexMatrixGramEigenvalues A i *
          ‖(complexMatrixGramEigenvectorBasis A).repr x j‖ ^ 2 ≤
        complexMatrixGramEigenvalues A j *
          ‖(complexMatrixGramEigenvectorBasis A).repr x j‖ ^ 2 := by
    intro j
    by_cases hji : j ≤ i
    · exact mul_le_mul_of_nonneg_right
        (complexMatrixGramEigenvalues_antitone A hji) (sq_nonneg _)
    · rw [hzero j hji]; simp
  have hsq : (complexMatrixSingularValue A i * ‖x‖) ^ 2 ≤
      ‖complexMatrixEuclideanLin A x‖ ^ 2 := by
    rw [complexMatrixEuclideanLin_norm_sq_eq_sum_gramEigenvalues_mul_repr_norm_sq,
      mul_pow, complexMatrixSingularValue_sq]
    calc
      complexMatrixGramEigenvalues A i * ‖x‖ ^ 2
          = complexMatrixGramEigenvalues A i *
              ∑ j : Fin n, ‖(complexMatrixGramEigenvectorBasis A).repr x j‖ ^ 2 := by
            rw [ch14ext_sum_repr_norm_sq]
      _ = ∑ j : Fin n, complexMatrixGramEigenvalues A i *
              ‖(complexMatrixGramEigenvectorBasis A).repr x j‖ ^ 2 := by
            rw [Finset.mul_sum]
      _ ≤ ∑ j : Fin n, complexMatrixGramEigenvalues A j *
              ‖(complexMatrixGramEigenvectorBasis A).repr x j‖ ^ 2 :=
            Finset.sum_le_sum (fun j _ => hterm j)
  exact ch14ext_le_of_sq_le_sq
    (mul_nonneg (complexMatrixSingularValue_nonneg A i) (norm_nonneg x))
    (norm_nonneg _) hsq

/-- **Courant–Fischer, trailing half.** On the span of the last `n−i` Gram
    eigenvectors of `A`, the Euclidean action of `A` is bounded above by
    `σ_i(A)·‖x‖`.  Higham, 2nd ed., Problem 14.15 (min–max input). -/
theorem ch14ext_norm_le_singularValue_mul_norm_of_mem_trailSpan
    {m n : ℕ} (A : CMatrix m n) (i : Fin n) {x : EuclideanSpace ℂ (Fin n)}
    (hx : x ∈ Submodule.span ℂ
      (⇑(complexMatrixGramEigenvectorBasis A) '' (↑(Finset.Ici i) : Set (Fin n)))) :
    ‖complexMatrixEuclideanLin A x‖ ≤ complexMatrixSingularValue A i * ‖x‖ := by
  have hzero : ∀ j : Fin n, ¬ (i ≤ j) →
      (complexMatrixGramEigenvectorBasis A).repr x j = 0 := by
    intro j hji
    refine ch14ext_repr_eq_zero_of_mem_span (complexMatrixGramEigenvectorBasis A) _ hx ?_
    simp only [Finset.coe_Ici, Set.mem_Ici]
    exact hji
  have hterm : ∀ j : Fin n,
      complexMatrixGramEigenvalues A j *
          ‖(complexMatrixGramEigenvectorBasis A).repr x j‖ ^ 2 ≤
        complexMatrixGramEigenvalues A i *
          ‖(complexMatrixGramEigenvectorBasis A).repr x j‖ ^ 2 := by
    intro j
    by_cases hij : i ≤ j
    · exact mul_le_mul_of_nonneg_right
        (complexMatrixGramEigenvalues_antitone A hij) (sq_nonneg _)
    · rw [hzero j hij]; simp
  have hsq : ‖complexMatrixEuclideanLin A x‖ ^ 2 ≤
      (complexMatrixSingularValue A i * ‖x‖) ^ 2 := by
    rw [complexMatrixEuclideanLin_norm_sq_eq_sum_gramEigenvalues_mul_repr_norm_sq,
      mul_pow, complexMatrixSingularValue_sq]
    calc
      ∑ j : Fin n, complexMatrixGramEigenvalues A j *
            ‖(complexMatrixGramEigenvectorBasis A).repr x j‖ ^ 2
          ≤ ∑ j : Fin n, complexMatrixGramEigenvalues A i *
              ‖(complexMatrixGramEigenvectorBasis A).repr x j‖ ^ 2 :=
            Finset.sum_le_sum (fun j _ => hterm j)
      _ = complexMatrixGramEigenvalues A i *
              ∑ j : Fin n, ‖(complexMatrixGramEigenvectorBasis A).repr x j‖ ^ 2 := by
            rw [Finset.mul_sum]
      _ = complexMatrixGramEigenvalues A i * ‖x‖ ^ 2 := by
            rw [ch14ext_sum_repr_norm_sq]
  exact ch14ext_le_of_sq_le_sq (norm_nonneg _)
    (mul_nonneg (complexMatrixSingularValue_nonneg A i) (norm_nonneg x)) hsq

/-- Dimension of the span of an eigenbasis subfamily indexed by a finite set of
    indices equals the cardinality of that set. -/
private theorem ch14ext_finrank_span_image_finset {n : ℕ}
    (b : OrthonormalBasis (Fin n) ℂ (EuclideanSpace ℂ (Fin n)))
    (s : Finset (Fin n)) :
    Module.finrank ℂ (Submodule.span ℂ (⇑b '' (↑s : Set (Fin n)))) = s.card := by
  classical
  have hli : LinearIndependent ℂ (fun k : {j // j ∈ s} => b (k : Fin n)) :=
    (b.orthonormal.comp (fun k : {j // j ∈ s} => (k : Fin n))
      Subtype.val_injective).linearIndependent
  have hrange : Set.range (fun k : {j // j ∈ s} => b (k : Fin n))
      = ⇑b '' (↑s : Set (Fin n)) := by
    ext y
    constructor
    · rintro ⟨⟨l, hl⟩, rfl⟩
      exact ⟨l, Finset.mem_coe.mpr hl, rfl⟩
    · rintro ⟨l, hl, rfl⟩
      exact ⟨⟨l, Finset.mem_coe.mp hl⟩, rfl⟩
  rw [← hrange, finrank_span_eq_card hli]
  exact Fintype.card_coe s

/-- Cardinality bookkeeping: `#(Iic i) + #(Ici i) = n + 1` in `Fin n`. -/
private theorem ch14ext_card_Iic_add_card_Ici {n : ℕ} (i : Fin n) :
    (Finset.Iic i).card + (Finset.Ici i).card = n + 1 := by
  haveI : NeZero n := ⟨by have := i.isLt; omega⟩
  rw [Fin.card_Iic, Fin.card_Ici]
  have := i.isLt
  omega

/-- Two subspaces of `EuclideanSpace ℂ (Fin n)` whose dimensions sum to more
    than `n` share a nonzero vector. -/
private theorem ch14ext_exists_nonzero_mem_inf {n : ℕ}
    (V W : Submodule ℂ (EuclideanSpace ℂ (Fin n)))
    (h : n < Module.finrank ℂ V + Module.finrank ℂ W) :
    ∃ x : EuclideanSpace ℂ (Fin n), x ≠ 0 ∧ x ∈ V ∧ x ∈ W := by
  have heq := Submodule.finrank_sup_add_finrank_inf_eq V W
  have hle := Submodule.finrank_le (V ⊔ W)
  rw [finrank_euclideanSpace_fin] at hle
  have hne : V ⊓ W ≠ ⊥ := by
    intro hbot
    rw [hbot, finrank_bot] at heq
    omega
  obtain ⟨x, hxmem, hxne⟩ := Submodule.exists_mem_ne_zero_of_ne_bot hne
  rw [Submodule.mem_inf] at hxmem
  exact ⟨x, hxne, hxmem.1, hxmem.2⟩

/-- **Weyl/Mirsky one-sided bound, operator form.**  If the Euclidean actions of
    `B` and `A` differ by at most `M·‖x‖` pointwise, then every ordered singular
    value satisfies `σ_i(B) ≤ σ_i(A) + M`.  Higham, 2nd ed., Problem 14.15. -/
theorem ch14ext_singularValue_le_of_euclideanLin_diff_bound
    {m n : ℕ} (A B : CMatrix m n) {M : ℝ}
    (hdiff : ∀ x : EuclideanSpace ℂ (Fin n),
      ‖complexMatrixEuclideanLin B x - complexMatrixEuclideanLin A x‖ ≤ M * ‖x‖)
    (i : Fin n) :
    complexMatrixSingularValue B i ≤ complexMatrixSingularValue A i + M := by
  obtain ⟨x, hxne, hxB, hxA⟩ :=
    ch14ext_exists_nonzero_mem_inf
      (Submodule.span ℂ
        (⇑(complexMatrixGramEigenvectorBasis B) '' (↑(Finset.Iic i) : Set (Fin n))))
      (Submodule.span ℂ
        (⇑(complexMatrixGramEigenvectorBasis A) '' (↑(Finset.Ici i) : Set (Fin n))))
      (by
        rw [ch14ext_finrank_span_image_finset, ch14ext_finrank_span_image_finset]
        have := ch14ext_card_Iic_add_card_Ici i
        omega)
  have hxpos : 0 < ‖x‖ := norm_pos_iff.mpr hxne
  have h1 : complexMatrixSingularValue B i * ‖x‖ ≤ ‖complexMatrixEuclideanLin B x‖ :=
    ch14ext_singularValue_mul_norm_le_norm_euclideanLin_of_mem_leadSpan B i hxB
  have h2 : ‖complexMatrixEuclideanLin A x‖ ≤ complexMatrixSingularValue A i * ‖x‖ :=
    ch14ext_norm_le_singularValue_mul_norm_of_mem_trailSpan A i hxA
  have h3 : ‖complexMatrixEuclideanLin B x‖ ≤
      ‖complexMatrixEuclideanLin A x‖ + M * ‖x‖ := by
    have hsplit : complexMatrixEuclideanLin B x =
        (complexMatrixEuclideanLin B x - complexMatrixEuclideanLin A x)
          + complexMatrixEuclideanLin A x := by abel
    calc
      ‖complexMatrixEuclideanLin B x‖
          = ‖(complexMatrixEuclideanLin B x - complexMatrixEuclideanLin A x)
              + complexMatrixEuclideanLin A x‖ := by rw [← hsplit]
      _ ≤ ‖complexMatrixEuclideanLin B x - complexMatrixEuclideanLin A x‖
              + ‖complexMatrixEuclideanLin A x‖ := norm_add_le _ _
      _ ≤ ‖complexMatrixEuclideanLin A x‖ + M * ‖x‖ := by linarith [hdiff x]
  have hchain : complexMatrixSingularValue B i * ‖x‖ ≤
      (complexMatrixSingularValue A i + M) * ‖x‖ := by
    rw [add_mul]
    calc
      complexMatrixSingularValue B i * ‖x‖
          ≤ ‖complexMatrixEuclideanLin B x‖ := h1
      _ ≤ ‖complexMatrixEuclideanLin A x‖ + M * ‖x‖ := h3
      _ ≤ complexMatrixSingularValue A i * ‖x‖ + M * ‖x‖ := by linarith [h2]
  exact le_of_mul_le_mul_right hchain hxpos

/-- **Weyl/Mirsky all-index bound, operator form.**  The strongest honest
    reusable statement: the ordered singular values of `A` and `B` differ by at
    most any pointwise operator-difference bound `M`.  The printed norm appears
    in the conclusion, derived, not assumed.  Higham, 2nd ed., Problem 14.15. -/
theorem ch14ext_singularValue_abs_sub_le_of_euclideanLin_diff_bound
    {m n : ℕ} (A B : CMatrix m n) {M : ℝ}
    (hdiff : ∀ x : EuclideanSpace ℂ (Fin n),
      ‖complexMatrixEuclideanLin B x - complexMatrixEuclideanLin A x‖ ≤ M * ‖x‖)
    (i : Fin n) :
    |complexMatrixSingularValue B i - complexMatrixSingularValue A i| ≤ M := by
  have hBA := ch14ext_singularValue_le_of_euclideanLin_diff_bound A B hdiff i
  have hdiff' : ∀ x : EuclideanSpace ℂ (Fin n),
      ‖complexMatrixEuclideanLin A x - complexMatrixEuclideanLin B x‖ ≤ M * ‖x‖ := by
    intro x
    rw [norm_sub_rev]
    exact hdiff x
  have hAB := ch14ext_singularValue_le_of_euclideanLin_diff_bound B A hdiff' i
  rw [abs_le]
  constructor <;> linarith

end NumStability.Ch14Ext
