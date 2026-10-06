import Mathlib.LinearAlgebra.FiniteDimensional.Lemmas
import Mathlib.LinearAlgebra.Dimension.Constructions
import Mathlib.Order.Interval.Finset.Fin
import NumStability.Analysis.Norms
import NumStability.Algorithms.MatrixInversion

/-!
# Higham, 2nd ed., Chapter 14, Problem 14.15 — determinant perturbation bound

This import-only file repairs the singular-value argument of **Problem 14.15**
(Higham, *Accuracy and Stability of Numerical Algorithms*, 2nd ed., p. 285).
The printed hypothesis only requires `κ₂(A)‖ΔA‖₂/‖A‖₂ < 1`, but the displayed
right-hand side has denominator `1 - n κ₂(A)‖ΔA‖₂/‖A‖₂` and is false when that
denominator is negative.  Under the necessary positive-denominator guard
`κ₂(A)‖ΔA‖₂/‖A‖₂ < 1/n`, this file proves the mathematically valid form
`||det(A+ΔA)| / |det(A)| - 1| ≤ n κ₂(A)(‖ΔA‖₂/‖A‖₂) /
  (1 − n κ₂(A)‖ΔA‖₂/‖A‖₂)`.

The book and Appendix A write `det(A) = ∏ᵢ σᵢ(A)`; the identity justified by
singular values is `|det(A)| = ∏ᵢ σᵢ(A)`.  The literal signed form is recovered
without sign hypotheses by proving that the whole path `A + tΔA`, `0 ≤ t ≤ 1`,
is nonsingular, so its determinant cannot change sign.

The determinant argument was already assembled in `MatrixInversion.lean`
(`higham14_problem14_15_..._inv_card_guard`), *conditional* on the all-index
Weyl/Mirsky singular-value perturbation inequality
`|σ_i(A+ΔA) − σ_i(A)| ≤ ‖ΔA‖₂` for **every** index `i`.  That inequality was the
missing spectral foundation: `MatrixInversion.lean` only carried the top-index
(`opNorm2`) and bottom-index (Wedin `σ_min`) extremal cases, which do not need a
min–max / Grassmannian argument.

Here the full all-index bound is proved **from scratch** through a
Courant–Fischer intersection argument built on the repository's SVD/Gram
eigenbasis (`complexMatrixGramEigenvectorBasis`, orthonormal, sorted).  Mathlib
does not provide a Courant–Fischer min–max characterisation nor a Weyl
eigenvalue-perturbation theorem, so the min–max content is developed directly:

* `ch14ext_singularValue_mul_norm_le_norm_euclideanLin_of_mem_leadSpan`:
  on `span{v₀,…,vᵢ}` the action is bounded **below** by `σᵢ·‖x‖`;
* `ch14ext_norm_le_singularValue_mul_norm_of_mem_trailSpan`:
  on `span{vᵢ,…,v_{n−1}}` the action is bounded **above** by `σᵢ·‖x‖`;
* a dimension count `(i+1)+(n−i) = n+1 > n` forces the leading eigenspace of
  `B` to meet the trailing eigenspace of `A`, and the triangle inequality on the
  common vector gives `σᵢ(B) ≤ σᵢ(A) + ‖B−A‖₂`.

The resulting abstract bound
`ch14ext_singularValue_abs_sub_le_of_euclideanLin_diff_bound` is honest and
reusable (it takes the perturbation only as an operator-difference bound and
concludes with `‖·‖₂` in the *conclusion*, not in a hypothesis).  Its
specialisation `ch14ext_problem14_15_all_index_singularValue_abs_sub_le_opNorm2`
is exactly the `habs` premise of the existing determinant wrapper, so
`ch14ext_problem14_15_abs_det_add_rel_le_of_kappa2_opNorm2_inv_card_guard`
discharges Problem 14.15 with no residual spectral hypothesis.

All declarations use the fresh namespace `NumStability.Ch14Ext` and the
`ch14ext_` prefix; the file never edits `MatrixInversion.lean` and only reuses
its public declarations.
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

/-- Complexification of a real matrix is additive as a Euclidean linear map. -/
private theorem ch14ext_complexMatrixEuclideanLin_add {m n : ℕ} (P Q : CMatrix m n) :
    complexMatrixEuclideanLin (P + Q)
      = complexMatrixEuclideanLin P + complexMatrixEuclideanLin Q :=
  map_add (Matrix.toEuclideanLin (𝕜 := ℂ) (m := Fin m) (n := Fin n)) P Q

/-- The perturbation certificate needed to instantiate the Weyl bound for real
    matrices: the Euclidean-action difference of the complexified perturbed and
    unperturbed matrices is bounded by `‖ΔA‖₂·‖x‖`. -/
theorem ch14ext_euclideanLin_realRect_diff_bound {n : ℕ}
    (A Delta : Fin n → Fin n → ℝ) (x : EuclideanSpace ℂ (Fin n)) :
    ‖complexMatrixEuclideanLin (realRectToCMatrix (fun r c => A r c + Delta r c)) x
        - complexMatrixEuclideanLin (realRectToCMatrix A) x‖
      ≤ opNorm2 Delta * ‖x‖ := by
  have hM : realRectToCMatrix (fun r c => A r c + Delta r c)
      = realRectToCMatrix A + realRectToCMatrix Delta := by
    ext r c
    simp only [realRectToCMatrix, Pi.add_apply]
    push_cast
    ring
  have hdiff_eq :
      complexMatrixEuclideanLin (realRectToCMatrix (fun r c => A r c + Delta r c)) x
        - complexMatrixEuclideanLin (realRectToCMatrix A) x
      = complexMatrixEuclideanLin (realRectToCMatrix Delta) x := by
    rw [hM, ch14ext_complexMatrixEuclideanLin_add]
    simp [LinearMap.add_apply]
  rw [hdiff_eq]
  have hop : ‖complexMatrixEuclideanLin (realRectToCMatrix Delta) x‖
      ≤ complexMatrixOp2 (realRectToCMatrix Delta) * ‖x‖ := by
    rw [complexMatrixOp2_eq_norm_euclideanLin]
    exact ContinuousLinearMap.le_opNorm
      (complexMatrixEuclideanLin (realRectToCMatrix Delta)).toContinuousLinearMap x
  rwa [← higham14_problem14_13_opNorm2_eq_complexMatrixOp2_realRectToCMatrix Delta] at hop

/-- **Weyl/Mirsky all-index singular-value perturbation inequality for a real
    square matrix.**  This is the missing spectral foundation of Problem 14.15:
    `|σ_i(A+ΔA) − σ_i(A)| ≤ ‖ΔA‖₂` for *every* ordered index `i`.  Higham, 2nd
    ed., Problem 14.15 (p. 285). -/
theorem ch14ext_problem14_15_all_index_singularValue_abs_sub_le_opNorm2 {n : ℕ}
    (A Delta : Fin n → Fin n → ℝ) (i : Fin n) :
    |complexMatrixSingularValue
        (realRectToCMatrix (fun r c => A r c + Delta r c)) i
      - complexMatrixSingularValue (realRectToCMatrix A) i| ≤ opNorm2 Delta :=
  ch14ext_singularValue_abs_sub_le_of_euclideanLin_diff_bound
    (realRectToCMatrix A) (realRectToCMatrix (fun r c => A r c + Delta r c))
    (fun x => ch14ext_euclideanLin_realRect_diff_bound A Delta x) i

/-- **Higham, 2nd ed., Chapter 14, Problem 14.15 — FULL determinant perturbation
    bound.**  For `A ∈ ℝ^{(k+1)×(k+1)}` with a certified right inverse and
    `κ₂(A)‖ΔA‖₂/‖A‖₂ < 1/(k+1)`,
    `|det(A+ΔA)| / |det(A)|` differs from `1` by at most
    `(k+1)κ₂(A)(‖ΔA‖₂/‖A‖₂) / (1 − (k+1)κ₂(A)‖ΔA‖₂/‖A‖₂)`.

    This composes the determinant-product wrapper of `MatrixInversion.lean` with
    the all-index Weyl bound proved above; there is no residual spectral
    hypothesis.  Higham prints only
    `κ₂(A)‖ΔA‖₂/‖A‖₂ < 1`; for dimension `n = k+1`, the stronger displayed
    `< 1/(k+1)` hypothesis repairs the denominator side condition required by
    the stated bound. -/
theorem ch14ext_problem14_15_abs_det_add_rel_le_of_kappa2_opNorm2_inv_card_guard
    {k : ℕ} (A Ainv Delta : Fin (k + 1) → Fin (k + 1) → ℝ)
    (hRight : IsRightInverse (k + 1) A Ainv)
    (hsmall :
      kappa2 A Ainv * opNorm2 Delta / opNorm2 A < (((k + 1 : ℕ) : ℝ)⁻¹)) :
    |(|Matrix.det
          ((fun r c => A r c + Delta r c) :
            Matrix (Fin (k + 1)) (Fin (k + 1)) ℝ)| /
        |Matrix.det (A : Matrix (Fin (k + 1)) (Fin (k + 1)) ℝ)|) - 1| ≤
      (((k + 1 : ℕ) : ℝ) *
          (kappa2 A Ainv * opNorm2 Delta / opNorm2 A)) /
        (1 - ((k + 1 : ℕ) : ℝ) *
          (kappa2 A Ainv * opNorm2 Delta / opNorm2 A)) :=
  higham14_problem14_15_abs_det_add_rel_le_of_kappa2_opNorm2_singularValue_abs_sub_bound_inv_card_guard
    A Ainv Delta hRight hsmall
    (fun i => ch14ext_problem14_15_all_index_singularValue_abs_sub_le_opNorm2 A Delta i)

/-- Exact homogeneity of the repository's operator `2`-norm under real scalar
    multiplication. -/
private theorem ch14ext_opNorm2_smul {n : ℕ}
    (D : Fin n → Fin n → ℝ) (t : ℝ) :
    opNorm2 (fun i j => t * D i j) = |t| * opNorm2 D := by
  letI : NormedAddCommGroup (Matrix (Fin n) (Fin n) ℝ) :=
    Matrix.instL2OpNormedAddCommGroup
  letI : NormedSpace ℝ (Matrix (Fin n) (Fin n) ℝ) :=
    Matrix.instL2OpNormedSpace
  unfold opNorm2
  change
    norm (show Matrix (Fin n) (Fin n) ℝ from fun i j => t * D i j) =
      |t| * norm (show Matrix (Fin n) (Fin n) ℝ from D)
  rw [show (fun i j => t * D i j) =
      t • (show Matrix (Fin n) (Fin n) ℝ from D) by rfl]
  simpa [Real.norm_eq_abs] using
    (norm_smul t (show Matrix (Fin n) (Fin n) ℝ from D))

/-- A perturbation strictly smaller than the last singular value leaves the
    perturbed determinant nonzero. -/
private theorem ch14ext_det_add_ne_zero_of_opNorm2_lt_last_singularValue
    {k : ℕ} (A E : Fin (k + 1) → Fin (k + 1) → ℝ)
    (hsmall : opNorm2 E <
      complexMatrixSingularValue (realRectToCMatrix A) (Fin.last k)) :
    Matrix.det
      ((fun i j => A i j + E i j) :
        Matrix (Fin (k + 1)) (Fin (k + 1)) ℝ) ≠ 0 := by
  have hlast_pos : 0 <
      complexMatrixSingularValue
        (realRectToCMatrix (fun i j => A i j + E i j)) (Fin.last k) :=
    higham14_problem14_15_sigmaMin_add_pos_of_rectOpNorm2Le_lt A E
      (opNorm2Le_to_rectOpNorm2Le (opNorm2Le_opNorm2 E)) hsmall
  have hprod_pos : 0 < ∏ i : Fin (k + 1),
      complexMatrixSingularValue
        (realRectToCMatrix (fun r c => A r c + E r c)) i := by
    refine Finset.prod_pos ?_
    intro i _
    exact lt_of_lt_of_le hlast_pos
      (higham14_problem14_15_last_singularValue_le_singularValue
        (fun r c => A r c + E r c) i)
  have hdet_prod :=
    higham14_problem14_13_abs_det_eq_prod_complex_singularValue
      (fun i j => A i j + E i j)
  exact abs_pos.mp (by rw [hdet_prod]; exact hprod_pos)

/-- **Problem 14.15 determinant-sign preservation.**  Under the corrected guard,
    `A + ΔA` has the same determinant sign as `A`.  Indeed, the guard gives
    `‖ΔA‖₂ < σ_min(A)`; hence every point of the path `A + tΔA`, `0 ≤ t ≤ 1`,
    is nonsingular, and determinant continuity rules out a sign crossing. -/
theorem ch14ext_problem14_15_det_add_same_sign_of_kappa2_opNorm2_inv_card_guard
    {k : ℕ} (A Ainv Delta : Fin (k + 1) → Fin (k + 1) → ℝ)
    (hRight : IsRightInverse (k + 1) A Ainv)
    (hsmall :
      kappa2 A Ainv * opNorm2 Delta / opNorm2 A < (((k + 1 : ℕ) : ℝ)⁻¹)) :
    (0 < Matrix.det (A : Matrix (Fin (k + 1)) (Fin (k + 1)) ℝ) ∧
      0 < Matrix.det
        ((fun i j => A i j + Delta i j) :
          Matrix (Fin (k + 1)) (Fin (k + 1)) ℝ)) ∨
    (Matrix.det (A : Matrix (Fin (k + 1)) (Fin (k + 1)) ℝ) < 0 ∧
      Matrix.det
        ((fun i j => A i j + Delta i j) :
          Matrix (Fin (k + 1)) (Fin (k + 1)) ℝ) < 0) := by
  let sigmaMinA : ℝ :=
    complexMatrixSingularValue (realRectToCMatrix A) (Fin.last k)
  let eps : ℝ := kappa2 A Ainv * opNorm2 Delta / opNorm2 A
  have hsigma_pos : 0 < sigmaMinA := by
    simpa [sigmaMinA] using
      higham14_problem14_15_last_singularValue_pos_of_isRightInverse A Ainv hRight
  have hinv_le_one : (((k + 1 : ℕ) : ℝ)⁻¹) ≤ 1 :=
    Nat.cast_inv_le_one (k + 1)
  have heps_lt_one : eps < 1 :=
    lt_of_lt_of_le (by simpa [eps] using hsmall) hinv_le_one
  have hDelta_lt : opNorm2 Delta < sigmaMinA := by
    calc
      opNorm2 Delta ≤ eps * sigmaMinA := by
        simpa [eps, sigmaMinA] using
          higham14_problem14_15_opNorm2_le_kappa2_scaled_last_singularValue
            A Ainv Delta hRight
      _ < 1 * sigmaMinA := mul_lt_mul_of_pos_right heps_lt_one hsigma_pos
      _ = sigmaMinA := one_mul _
  let f : ℝ → ℝ := fun t =>
    Matrix.det
      ((fun i j => A i j + t * Delta i j) :
        Matrix (Fin (k + 1)) (Fin (k + 1)) ℝ)
  have hf : Continuous f := by
    dsimp [f]
    fun_prop
  have hpath : ∀ t : ℝ, t ∈ Set.Icc (0 : ℝ) 1 → f t ≠ 0 := by
    intro t ht
    let E : Fin (k + 1) → Fin (k + 1) → ℝ :=
      fun i j => t * Delta i j
    have hopE : opNorm2 E ≤ opNorm2 Delta := by
      rw [show opNorm2 E = |t| * opNorm2 Delta by
        simpa [E] using ch14ext_opNorm2_smul Delta t,
        abs_of_nonneg ht.1]
      exact mul_le_of_le_one_left (opNorm2_nonneg Delta) ht.2
    have hdetE := ch14ext_det_add_ne_zero_of_opNorm2_lt_last_singularValue A E
      (lt_of_le_of_lt hopE hDelta_lt)
    simpa [f, E] using hdetE
  have hf0 : f 0 =
      Matrix.det (A : Matrix (Fin (k + 1)) (Fin (k + 1)) ℝ) := by
    simp [f]
  have hf1 : f 1 =
      Matrix.det
        ((fun i j => A i j + Delta i j) :
          Matrix (Fin (k + 1)) (Fin (k + 1)) ℝ) := by
    simp [f]
  have hdetA_ne :
      Matrix.det (A : Matrix (Fin (k + 1)) (Fin (k + 1)) ℝ) ≠ 0 :=
    abs_pos.mp
      (higham14_problem14_13_abs_det_pos_of_isRightInverse A Ainv hRight)
  have hdetB_ne :
      Matrix.det
        ((fun i j => A i j + Delta i j) :
          Matrix (Fin (k + 1)) (Fin (k + 1)) ℝ) ≠ 0 := by
    rw [← hf1]
    exact hpath 1 ⟨by norm_num, le_rfl⟩
  rcases lt_or_gt_of_ne hdetA_ne with hAneg | hApos
  · rcases lt_or_gt_of_ne hdetB_ne with hBneg | hBpos
    · exact Or.inr ⟨hAneg, hBneg⟩
    · exfalso
      have hzmem : (0 : ℝ) ∈ Set.Icc (f 0) (f 1) := by
        rw [hf0, hf1]
        exact ⟨hAneg.le, hBpos.le⟩
      obtain ⟨t, ht, hft⟩ :=
        intermediate_value_Icc (show (0 : ℝ) ≤ 1 by norm_num)
          hf.continuousOn hzmem
      exact hpath t ht hft
  · rcases lt_or_gt_of_ne hdetB_ne with hBneg | hBpos
    · exfalso
      have hzmem : (0 : ℝ) ∈ Set.Icc (f 1) (f 0) := by
        rw [hf0, hf1]
        exact ⟨hBneg.le, hApos.le⟩
      obtain ⟨t, ht, hft⟩ :=
        intermediate_value_Icc' (show (0 : ℝ) ≤ 1 by norm_num)
          hf.continuousOn hzmem
      exact hpath t ht hft
    · exact Or.inl ⟨hApos, hBpos⟩

/-- **Higham, 2nd ed., Chapter 14, Problem 14.15 — signed determinant form.**
    The source relative-change bound, with no determinant-sign assumptions. -/
theorem ch14ext_problem14_15_det_add_rel_le_of_kappa2_opNorm2_inv_card_guard
    {k : ℕ} (A Ainv Delta : Fin (k + 1) → Fin (k + 1) → ℝ)
    (hRight : IsRightInverse (k + 1) A Ainv)
    (hsmall :
      kappa2 A Ainv * opNorm2 Delta / opNorm2 A < (((k + 1 : ℕ) : ℝ)⁻¹)) :
    |(Matrix.det
          ((fun r c => A r c + Delta r c) :
            Matrix (Fin (k + 1)) (Fin (k + 1)) ℝ) /
        Matrix.det (A : Matrix (Fin (k + 1)) (Fin (k + 1)) ℝ)) - 1| ≤
      (((k + 1 : ℕ) : ℝ) *
          (kappa2 A Ainv * opNorm2 Delta / opNorm2 A)) /
        (1 - ((k + 1 : ℕ) : ℝ) *
          (kappa2 A Ainv * opNorm2 Delta / opNorm2 A)) := by
  have hAbs :=
    ch14ext_problem14_15_abs_det_add_rel_le_of_kappa2_opNorm2_inv_card_guard
      A Ainv Delta hRight hsmall
  rcases
      ch14ext_problem14_15_det_add_same_sign_of_kappa2_opNorm2_inv_card_guard
        A Ainv Delta hRight hsmall with hpos | hneg
  · simpa [abs_of_pos hpos.1, abs_of_pos hpos.2] using hAbs
  · simpa [abs_of_neg hneg.1, abs_of_neg hneg.2] using hAbs

/-- **Higham, 2nd ed., Chapter 14, Problem 14.15 — signed determinant form.**
    The same closure as above in the signed relative-change form, under positive
    determinant signs. -/
theorem ch14ext_problem14_15_det_add_rel_le_of_kappa2_opNorm2_inv_card_guard_of_det_pos
    {k : ℕ} (A Ainv Delta : Fin (k + 1) → Fin (k + 1) → ℝ)
    (hRight : IsRightInverse (k + 1) A Ainv)
    (hsmall :
      kappa2 A Ainv * opNorm2 Delta / opNorm2 A < (((k + 1 : ℕ) : ℝ)⁻¹))
    (hdetA_pos : 0 < Matrix.det (A : Matrix (Fin (k + 1)) (Fin (k + 1)) ℝ))
    (hdetB_pos :
      0 < Matrix.det
        ((fun r c => A r c + Delta r c) :
          Matrix (Fin (k + 1)) (Fin (k + 1)) ℝ)) :
    |(Matrix.det
          ((fun r c => A r c + Delta r c) :
            Matrix (Fin (k + 1)) (Fin (k + 1)) ℝ) /
        Matrix.det (A : Matrix (Fin (k + 1)) (Fin (k + 1)) ℝ)) - 1| ≤
      (((k + 1 : ℕ) : ℝ) *
          (kappa2 A Ainv * opNorm2 Delta / opNorm2 A)) /
        (1 - ((k + 1 : ℕ) : ℝ) *
          (kappa2 A Ainv * opNorm2 Delta / opNorm2 A)) :=
  higham14_problem14_15_det_add_rel_le_of_kappa2_opNorm2_singularValue_abs_sub_bound_inv_card_guard_of_det_pos
    A Ainv Delta hRight hsmall
    (fun i => ch14ext_problem14_15_all_index_singularValue_abs_sub_le_opNorm2 A Delta i)
    hdetA_pos hdetB_pos

/-- The guard printed in Problem 14.15 does not by itself make the displayed
    denominator positive.  This is the scalar shape obtained from the
    two-dimensional specialization `A = I`, `Delta = (3/4) I`: the printed
    hypothesis has `x < 1`, but its claimed nonnegative absolute value would
    have to be bounded by a negative right-hand side. -/
theorem ch14ext_problem14_15_printed_guard_scalar_counterexample :
    let n : ℝ := 2
    let x : ℝ := 3 / 4
    x < 1 ∧
      ¬ (|((1 + x) ^ 2) - 1| ≤ (n * x) / (1 - n * x)) := by
  norm_num

end NumStability.Ch14Ext
