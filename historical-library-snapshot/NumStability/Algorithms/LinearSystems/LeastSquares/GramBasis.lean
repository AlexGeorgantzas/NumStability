import Mathlib.Algebra.BigOperators.Group.Finset.Basic
import Mathlib.Algebra.Order.BigOperators.Group.Finset
import Mathlib.Analysis.Matrix.Spectrum
import Mathlib.Data.Real.Basic
import Mathlib.LinearAlgebra.Matrix.Rank
import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Ring
import NumStability.Algorithms.LinearSystems.LeastSquares.AugmentedSystem
import NumStability.Algorithms.LinearSystems.LeastSquares.Basic
import NumStability.Analysis.SingularValues.RectangularGram
import NumStability.Analysis.MatrixAlgebra

namespace NumStability

open scoped BigOperators Matrix.Norms.Frobenius

/-!
# GramBasis

Canonical reusable module extracted without change from LSQRSolve.
-/

/-- Equivalence from a right-Gram basis index to the ordered singular-value
    coordinate selected by the same mathlib Hermitian reindexing. -/
noncomputable def rectRightGramBasisOrderedEquiv (n : ℕ) : Fin n ≃ Fin n where
  toFun := rectRightGramBasisOrderedIndex n
  invFun i := rectRightGramOrderedEigenbasisEquiv n (finCardIndex n i)
  left_inv := by
    intro b
    change rectRightGramOrderedEigenbasisEquiv n
        (finCardIndex n (rectRightGramBasisOrderedIndex n b)) = b
    rw [finCardIndex_rectRightGramBasisOrderedIndex]
    exact (rectRightGramOrderedEigenbasisEquiv n).apply_symm_apply b
  right_inv := by
    intro i
    apply Fin.ext
    have h :=
      finCardIndex_rectRightGramBasisOrderedIndex n
        (rectRightGramOrderedEigenbasisEquiv n (finCardIndex n i))
    rw [(rectRightGramOrderedEigenbasisEquiv n).symm_apply_apply] at h
    simpa [finCardIndex] using congrArg Fin.val h
/-- The finite minimum of the basis-indexed right-Gram singular values is the
    finite minimum of the ordered real right-Gram singular values. -/
theorem lsScaledAugmentedBranchSigmaMin_rectRightGramBasis_eq_rectSingularValue
    {m n : ℕ} [Nonempty (Fin n)] (A : Fin m → Fin n → ℝ) :
    lsScaledAugmentedBranchSigmaMin (rectRightGramBasisSingularValue A) =
      lsScaledAugmentedBranchSigmaMin (rectSingularValue A) := by
  exact
    lsScaledAugmentedBranchSigmaMin_eq_of_equiv
      (rectRightGramBasisSingularValue A) (rectSingularValue A)
      (rectRightGramBasisOrderedEquiv n)
      (fun b => rectRightGramBasisSingularValue_eq_orderedIndex A b)
/-- The finite maximum of the basis-indexed right-Gram singular values is the
    finite maximum of the ordered real right-Gram singular values. -/
theorem lsScaledAugmentedBranchSigmaMax_rectRightGramBasis_eq_rectSingularValue
    {m n : ℕ} [Nonempty (Fin n)] (A : Fin m → Fin n → ℝ) :
    lsScaledAugmentedBranchSigmaMax (rectRightGramBasisSingularValue A) =
      lsScaledAugmentedBranchSigmaMax (rectSingularValue A) := by
  exact
    lsScaledAugmentedBranchSigmaMax_eq_of_equiv
      (rectRightGramBasisSingularValue A) (rectSingularValue A)
      (rectRightGramBasisOrderedEquiv n)
      (fun b => rectRightGramBasisSingularValue_eq_orderedIndex A b)
/-- Positive right-Gram singular branches give the transpose-side singular-pair
    equation for the real basis-indexed SVD candidates.  This is the missing
    algebraic half of `u_a = A v_a / sigma_a`, specialized to the finite
    real-Gram infrastructure already used elsewhere in the repository. -/
theorem rectRightGramLeftSingularFromEigenbasis_transpose_action_of_pos
    {m n : ℕ}
    (A : Fin m → Fin n → ℝ)
    (hpos : ∀ a : Fin n, 0 < rectRightGramBasisSingularValue A a)
    (a : Fin n) :
    (fun j : Fin n => ∑ i : Fin m,
      A i j * rectRightGramLeftSingularFromEigenbasis A i a) =
        fun j => rectRightGramBasisSingularValue A a *
          rectRightGramEigenbasis A j a := by
  ext j
  let τ := rectRightGramBasisSingularValue A a
  have hτ : τ ≠ 0 := ne_of_gt (hpos a)
  have heig := rectRightGramEigenbasis_eigenvector A a j
  have hsq := rectRightGramBasisSingularValue_sq_eq A a
  calc
    ∑ i : Fin m, A i j * rectRightGramLeftSingularFromEigenbasis A i a
        = (1 / τ) * ∑ i : Fin m,
            A i j * rectRightGramProjectedColumn A i a := by
          unfold rectRightGramLeftSingularFromEigenbasis
          rw [Finset.mul_sum]
          apply Finset.sum_congr rfl
          intro i _
          ring
    _ = (1 / τ) * ∑ k : Fin n,
          rectRightGram A j k * rectRightGramEigenbasis A k a := by
          congr 1
          unfold rectRightGramProjectedColumn rectRightGram
          calc
            ∑ i : Fin m,
                A i j * (∑ k : Fin n,
                  A i k * rectRightGramEigenbasis A k a)
                = ∑ i : Fin m, ∑ k : Fin n,
                    A i j * (A i k * rectRightGramEigenbasis A k a) := by
                    apply Finset.sum_congr rfl
                    intro i _
                    rw [Finset.mul_sum]
            _ = ∑ k : Fin n, ∑ i : Fin m,
                    A i j * (A i k * rectRightGramEigenbasis A k a) := by
                    rw [Finset.sum_comm]
            _ = ∑ k : Fin n, (∑ i : Fin m, A i j * A i k) *
                    rectRightGramEigenbasis A k a := by
                    apply Finset.sum_congr rfl
                    intro k _
                    rw [Finset.sum_mul]
                    apply Finset.sum_congr rfl
                    intro i _
                    ring
    _ = (1 / τ) *
          (rectRightGramEigenvalue A a * rectRightGramEigenbasis A j a) := by
          rw [heig]
    _ = τ * rectRightGramEigenbasis A j a := by
          have hτsq : τ ^ 2 = rectRightGramEigenvalue A a := by
            simpa [τ] using hsq
          rw [← hτsq]
          field_simp [hτ]
/-- Full column rank in the real column-map sense forces every basis-indexed
    right-Gram singular value to be positive.  A zero branch would make the
    corresponding orthonormal right-Gram eigenvector lie in the kernel of `A`. -/
theorem rectRightGramBasisSingularValue_pos_of_rectMatMulVec_injective
    {m n : ℕ} {A : Fin m → Fin n → ℝ}
    (hinj : Function.Injective (rectMatMulVec A)) (a : Fin n) :
    0 < rectRightGramBasisSingularValue A a := by
  refine lt_of_le_of_ne' (rectRightGramBasisSingularValue_nonneg A a) ?_
  intro hzero
  let v : Fin n → ℝ := fun j => rectRightGramEigenbasis A j a
  have hAv_zero : rectMatMulVec A v = 0 := by
    ext i
    have hp :=
      rectRightGramProjectedColumn_eq_zero_of_singularValue_eq_zero
        A a hzero i
    simpa [v, rectMatMulVec, rectRightGramProjectedColumn] using hp
  have hv_zero : v = 0 := by
    apply hinj
    rw [hAv_zero]
    ext i
    simp [rectMatMulVec]
  have hnorm_one : (∑ j : Fin n, v j * v j) = 1 := by
    have h := rectRightGramEigenbasis_col_orthonormal A a a
    simpa [v, idMatrix] using h
  have hnorm_zero : (∑ j : Fin n, v j * v j) = 0 := by
    simp [hv_zero]
  linarith
/-- Higham, 2nd ed., Chapter 20, equations (20.18)-(20.19):
    construction of the `m-n` left-nullspace branch family for the real
    right-Gram route.  Under `n <= m` and real full-column-rank injectivity,
    the constructed left singular vectors can be completed to an orthonormal
    `m`-column table; the added tail columns are orthonormal and annihilated by
    `A^T`. -/
theorem exists_rightGram_leftNull_branch_data_of_rectMatMulVec_injective
    {m n : ℕ} (hmn : n ≤ m) {A : Fin m → Fin n → ℝ}
    (hinj : Function.Injective (rectMatMulVec A)) :
    ∃ w : Fin (m - n) → Fin m → ℝ,
      (∀ k : Fin (m - n), vecNorm2Sq (w k) = 1) ∧
        (∀ k l : Fin (m - n),
          k ≠ l → (∑ r : Fin m, w k r * w l r) = 0) ∧
        (∀ k : Fin (m - n), ∀ j : Fin n,
          ∑ r : Fin m, A r j * w k r = 0) := by
  classical
  let U : Fin m → Fin n → ℝ :=
    fun r a => rectRightGramLeftSingularFromEigenbasis A r a
  let Utail₀ : Fin m → Fin (m - n) → ℝ := fun _ _ => 0
  let s : Set (Fin n ⊕ Fin (m - n)) := fun bc =>
    match bc with
    | Sum.inl _ => True
    | Sum.inr _ => False
  have hpos : ∀ a : Fin n, 0 < rectRightGramBasisSingularValue A a :=
    fun a => rectRightGramBasisSingularValue_pos_of_rectMatMulVec_injective
      (A := A) hinj a
  have hhead : ∀ a : Fin n, Sum.inl a ∈ s := by
    intro a
    exact True.intro
  have hpartial : ∀ a b : s,
      (∑ i : Fin m,
        leftBasisBlock U Utail₀ i a *
          leftBasisBlock U Utail₀ i b) =
        if a = b then 1 else 0 := by
    intro a b
    rcases a with ⟨bc, hbc⟩
    rcases b with ⟨bd, hbd⟩
    cases bc with
    | inl ca =>
        cases bd with
        | inl db =>
            have horth :=
              rectRightGramLeftSingularFromEigenbasis_col_orthonormal_of_pos
                A hpos ca db
            have hite :
                idMatrix n ca db =
                  if (⟨Sum.inl ca, hbc⟩ : s) = ⟨Sum.inl db, hbd⟩ then
                    1
                  else
                    0 := by
              by_cases hcd : ca = db
              · subst db
                simp [idMatrix]
              · have hsub :
                    (⟨Sum.inl ca, hbc⟩ : s) ≠ ⟨Sum.inl db, hbd⟩ := by
                  intro hEq
                  have hval :
                      (Sum.inl ca : Fin n ⊕ Fin (m - n)) = Sum.inl db :=
                    congrArg Subtype.val hEq
                  exact hcd (Sum.inl.inj hval)
                simp [idMatrix, hcd, hsub]
            calc
              (∑ i : Fin m,
                leftBasisBlock U Utail₀ i (Sum.inl ca) *
                  leftBasisBlock U Utail₀ i (Sum.inl db))
                  = idMatrix n ca db := by
                    simpa [U, Utail₀, leftBasisBlock] using horth
              _ = if (⟨Sum.inl ca, hbc⟩ : s) = ⟨Sum.inl db, hbd⟩ then
                    1
                  else
                    0 := hite
        | inr db =>
            cases hbd
    | inr ca =>
        cases hbc
  obtain ⟨Utail, _hpreserve, hcols⟩ :=
    partialLeftBasisBlock_exists_replacement_tail
      (lsSourceLeftCompletionEmbedding hmn) U Utail₀ s hhead hpartial
  let w : Fin (m - n) → Fin m → ℝ := fun k r => Utail r k
  have hfields :=
    leftBasisBlock_component_orthonormal_fields_of_col_orthonormal
      U Utail hcols
  have hw : ∀ k : Fin (m - n), vecNorm2Sq (w k) = 1 := by
    intro k
    have h := hfields.2.2 k k
    simpa [w, vecNorm2Sq, idMatrix, pow_two] using h
  have hnull : ∀ k l : Fin (m - n),
      k ≠ l → (∑ r : Fin m, w k r * w l r) = 0 := by
    intro k l hkl
    have h := hfields.2.2 k l
    simpa [w, idMatrix, hkl] using h
  have hATw : ∀ k : Fin (m - n), ∀ j : Fin n,
      ∑ r : Fin m, A r j * w k r = 0 := by
    intro k j
    have hcross := hfields.2.1
    calc
      ∑ r : Fin m, A r j * w k r
          = ∑ r : Fin m,
              (∑ a : Fin n,
                U r a * rectRightGramBasisSingularValue A a *
                  rectRightGramEigenbasis A j a) * w k r := by
              apply Finset.sum_congr rfl
              intro r _
              rw [rectRightGram_fullPositive_basisSVD_representation A hpos r j]
      _ = ∑ r : Fin m, ∑ a : Fin n,
              (U r a * w k r) *
                (rectRightGramBasisSingularValue A a *
                  rectRightGramEigenbasis A j a) := by
              apply Finset.sum_congr rfl
              intro r _
              rw [Finset.sum_mul]
              apply Finset.sum_congr rfl
              intro a _
              ring
      _ = ∑ a : Fin n, ∑ r : Fin m,
              (U r a * w k r) *
                (rectRightGramBasisSingularValue A a *
                  rectRightGramEigenbasis A j a) := by
              rw [Finset.sum_comm]
      _ = ∑ a : Fin n,
              (rectRightGramBasisSingularValue A a *
                rectRightGramEigenbasis A j a) *
                (∑ r : Fin m, U r a * w k r) := by
              apply Finset.sum_congr rfl
              intro a _
              rw [Finset.mul_sum]
              apply Finset.sum_congr rfl
              intro r _
              ring
      _ = 0 := by
              apply Finset.sum_eq_zero
              intro a _
              rw [hcross a k]
              ring
  exact ⟨w, hw, hnull, hATw⟩

end NumStability
