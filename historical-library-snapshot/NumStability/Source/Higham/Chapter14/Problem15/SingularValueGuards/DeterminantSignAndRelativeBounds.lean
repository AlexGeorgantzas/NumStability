import NumStability.Analysis.MatrixAlgebra
import NumStability.Analysis.MatrixNorms.Basic
import NumStability.Analysis.SingularValues.Basic
import NumStability.Analysis.SingularValues.Realification
import NumStability.Analysis.SingularValues.WeylMirsky
import NumStability.Source.Higham.Chapter14.Problem13.ConditionNumberBounds.UnitRowAndScalarCase
import NumStability.Source.Higham.Chapter14.Problem13.GEJBound.MatrixInversion
import NumStability.Source.Higham.Chapter14.Problem15.DeterminantPerturbation.MatrixInversion

/-!
# DeterminantSignAndRelativeBounds

Canonical destination for the Chapter14.Problem15 declarations relocated from the
historical path `NumStability.Source.Higham.Chapter14.Problem15` during wave R08.
Holds 10 declaration(s): 7 public and 3 authored-private.

Declaration names, kinds, signatures and visibilities are unchanged; the
authored-private declarations keep their names and change only their
mangled module owner, per the reviewed R08 private-normalization map.
-/

open scoped BigOperators

namespace NumStability.Ch14Ext

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
