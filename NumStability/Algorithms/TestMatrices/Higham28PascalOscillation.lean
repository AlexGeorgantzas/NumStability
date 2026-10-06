import NumStability.Algorithms.TestMatrices.Higham28PascalTotalPositivity
import NumStability.Algorithms.TestMatrices.Higham28PascalSpectral
import NumStability.Analysis.HighamChapter7

namespace NumStability

open scoped BigOperators
open Set

/-! # Higham Chapter 28: Pascal spectral oscillation -/

/-- The rank index used by Mathlib's decreasingly sorted Hermitian spectrum. -/
noncomputable def pascalSortedRankIndex (n : ℕ) (i : Fin n) :
    Fin (Fintype.card (Fin n)) :=
  Fin.cast (by simp) i

/-- The eigenvector-basis label corresponding to sorted rank `i`. -/
noncomputable def pascalSortedEigenIndex (n : ℕ) (i : Fin n) : Fin n :=
  (Fintype.equivOfCardEq
    (Fintype.card_fin (Fintype.card (Fin n))))
      (pascalSortedRankIndex n i)

/-- Equivalence from sorted rank to Mathlib's eigenvector-basis label. -/
noncomputable def pascalSortedEigenEquiv (n : ℕ) : Fin n ≃ Fin n :=
  (Fin.castOrderIso (by simp : n = Fintype.card (Fin n))).toEquiv.trans
    (Fintype.equivOfCardEq
      (Fintype.card_fin (Fintype.card (Fin n))))

@[simp]
theorem pascalSortedEigenEquiv_apply (n : ℕ) (i : Fin n) :
    pascalSortedEigenEquiv n i = pascalSortedEigenIndex n i := rfl

/-- The `i`th largest eigenvalue of the order-`n` symmetric Pascal matrix. -/
noncomputable def pascalSortedEigenvalue (n : ℕ) (i : Fin n) : ℝ :=
  (IsSymmetricFiniteMatrix.to_matrix_isHermitian
    (pascalMatrix n) (pascalMatrix_isSymmetricFiniteMatrix n)).eigenvalues₀
      (pascalSortedRankIndex n i)

/-- A canonical unit eigenvector belonging to the `i`th largest Pascal
eigenvalue. -/
noncomputable def pascalSortedEigenvector (n : ℕ) (i : Fin n) : RVec n :=
  ⇑((IsSymmetricFiniteMatrix.to_matrix_isHermitian
    (pascalMatrix n) (pascalMatrix_isSymmetricFiniteMatrix n)).eigenvectorBasis
      (pascalSortedEigenIndex n i))

/-- The Hermitian eigenbasis reindexed directly by decreasing spectral rank. -/
noncomputable def pascalSortedEigenbasis (n : ℕ) :
    OrthonormalBasis (Fin n) ℝ (EuclideanSpace ℝ (Fin n)) :=
  (IsSymmetricFiniteMatrix.to_matrix_isHermitian
    (pascalMatrix n) (pascalMatrix_isSymmetricFiniteMatrix n)).eigenvectorBasis.reindex
      (pascalSortedEigenEquiv n).symm

@[simp]
theorem pascalSortedEigenbasis_apply (n : ℕ) (i : Fin n) :
    ⇑(pascalSortedEigenbasis n i) = pascalSortedEigenvector n i := by
  let hP := IsSymmetricFiniteMatrix.to_matrix_isHermitian
    (pascalMatrix n) (pascalMatrix_isSymmetricFiniteMatrix n)
  have h := OrthonormalBasis.reindex_apply hP.eigenvectorBasis
    (pascalSortedEigenEquiv n).symm i
  change ⇑((hP.eigenvectorBasis.reindex
    (pascalSortedEigenEquiv n).symm) i) =
      ⇑(hP.eigenvectorBasis (pascalSortedEigenIndex n i))
  have h' : (hP.eigenvectorBasis.reindex
      (pascalSortedEigenEquiv n).symm) i =
      hP.eigenvectorBasis (pascalSortedEigenIndex n i) := by
    simpa using h
  exact congrArg (fun x : EuclideanSpace ℝ (Fin n) => ⇑x) h'

/-- Orthogonal eigenvector matrix with columns in decreasing eigenvalue order. -/
noncomputable def pascalSortedEigenvectorMatrix (n : ℕ) : RSqMat n :=
  (EuclideanSpace.basisFun (Fin n) ℝ).toBasis.toMatrix
    (pascalSortedEigenbasis n).toBasis

@[simp]
theorem pascalSortedEigenvectorMatrix_apply (n : ℕ) (i j : Fin n) :
    pascalSortedEigenvectorMatrix n i j = pascalSortedEigenvector n j i := by
  change (EuclideanSpace.basisFun (Fin n) ℝ).repr
      ((pascalSortedEigenbasis n).toBasis j) i = _
  rw [EuclideanSpace.basisFun_repr]
  exact congrFun (pascalSortedEigenbasis_apply n j) i

/-- Diagonal matrix of decreasingly sorted Pascal eigenvalues. -/
noncomputable def pascalSortedEigenvalueDiagonal (n : ℕ) : RSqMat n :=
  Matrix.diagonal (pascalSortedEigenvalue n)

theorem pascalSortedEigenvalue_antitone {n : ℕ} :
    Antitone (pascalSortedEigenvalue n) := by
  intro i j hij
  have hanti :=
    (IsSymmetricFiniteMatrix.to_matrix_isHermitian
      (pascalMatrix n) (pascalMatrix_isSymmetricFiniteMatrix n)).eigenvalues₀_antitone
      (show pascalSortedRankIndex n i ≤ pascalSortedRankIndex n j by
        simpa [pascalSortedRankIndex] using hij)
  simpa [pascalSortedEigenvalue] using hanti

theorem pascalMatrix_mulVec_sortedEigenvector {n : ℕ} (i : Fin n) :
    Matrix.mulVec (pascalMatrix n) (pascalSortedEigenvector n i) =
      pascalSortedEigenvalue n i • pascalSortedEigenvector n i := by
  let hP := IsSymmetricFiniteMatrix.to_matrix_isHermitian
    (pascalMatrix n) (pascalMatrix_isSymmetricFiniteMatrix n)
  have h := hP.mulVec_eigenvectorBasis (pascalSortedEigenIndex n i)
  simpa [pascalSortedEigenvector, pascalSortedEigenvalue,
    pascalSortedEigenIndex, pascalSortedRankIndex,
    Matrix.IsHermitian.eigenvalues, hP] using h

theorem pascalSortedEigenvector_normSq {n : ℕ} (i : Fin n) :
    ∑ j : Fin n, pascalSortedEigenvector n i j ^ 2 = 1 := by
  have h := finiteVecNorm2Sq_finiteHermitianEigenvector_eq_one
    (pascalMatrix n) (pascalMatrix_isSymmetricFiniteMatrix n)
    (pascalSortedEigenIndex n i)
  simpa [finiteVecNorm2Sq, pascalSortedEigenvector] using h

theorem pascalSortedEigenvector_ne_zero {n : ℕ} (i : Fin n) :
    pascalSortedEigenvector n i ≠ 0 := by
  intro hzero
  have h := pascalSortedEigenvector_normSq i
  simp [hzero] at h

theorem pascalSortedEigenvalue_pos {n : ℕ} (i : Fin n) :
    0 < pascalSortedEigenvalue n i := by
  let v := pascalSortedEigenvector n i
  have hv : ∃ j, v j ≠ 0 := by
    by_contra h
    push_neg at h
    exact pascalSortedEigenvector_ne_zero i (funext h)
  have hq := pascalMatrix_quadratic_pos n v hv
  have heig := pascalMatrix_mulVec_sortedEigenvector i
  have hnorm := pascalSortedEigenvector_normSq i
  have hq' : 0 < ∑ a : Fin n, ∑ b : Fin n,
      v a * pascalMatrix n a b * v b := by
    simpa using hq
  have heq : (∑ a : Fin n, ∑ b : Fin n,
      v a * pascalMatrix n a b * v b) =
      pascalSortedEigenvalue n i * (∑ a : Fin n, v a ^ 2) := by
    calc
      (∑ a : Fin n, ∑ b : Fin n, v a * pascalMatrix n a b * v b) =
          ∑ a : Fin n, v a * Matrix.mulVec (pascalMatrix n) v a := by
            apply Finset.sum_congr rfl
            intro a _
            simp only [Matrix.mulVec, dotProduct]
            rw [Finset.mul_sum]
            apply Finset.sum_congr rfl
            intro b _
            ring
      _ = ∑ a : Fin n, v a *
          (pascalSortedEigenvalue n i • v) a := by rw [heig]
      _ = pascalSortedEigenvalue n i * ∑ a : Fin n, v a ^ 2 := by
        simp only [Pi.smul_apply, smul_eq_mul]
        rw [Finset.mul_sum]
        apply Finset.sum_congr rfl
        intro a _
        ring
  rw [heq, show (∑ a : Fin n, v a ^ 2) = 1 by simpa [v] using hnorm,
    mul_one] at hq'
  exact hq'

theorem pascalSortedEigenvectorMatrix_transpose_mul_self (n : ℕ) :
    (pascalSortedEigenvectorMatrix n).transpose *
        pascalSortedEigenvectorMatrix n = 1 := by
  simpa [pascalSortedEigenvectorMatrix, Matrix.conjTranspose_apply] using
    (OrthonormalBasis.toMatrix_orthonormalBasis_conjTranspose_mul_self
      (EuclideanSpace.basisFun (Fin n) ℝ) (pascalSortedEigenbasis n))

theorem pascalSortedEigenvectorMatrix_mul_transpose (n : ℕ) :
    pascalSortedEigenvectorMatrix n *
        (pascalSortedEigenvectorMatrix n).transpose = 1 := by
  simpa [pascalSortedEigenvectorMatrix, Matrix.conjTranspose_apply] using
    (OrthonormalBasis.toMatrix_orthonormalBasis_self_mul_conjTranspose
      (EuclideanSpace.basisFun (Fin n) ℝ) (pascalSortedEigenbasis n))

theorem pascalMatrix_mul_sortedEigenvectorMatrix (n : ℕ) :
    pascalMatrix n * pascalSortedEigenvectorMatrix n =
      pascalSortedEigenvectorMatrix n * pascalSortedEigenvalueDiagonal n := by
  ext i j
  have heig := congrFun (pascalMatrix_mulVec_sortedEigenvector j) i
  rw [Matrix.mul_apply]
  have hrhs :
      (pascalSortedEigenvectorMatrix n *
        pascalSortedEigenvalueDiagonal n) i j =
          pascalSortedEigenvector n j i * pascalSortedEigenvalue n j := by
    rw [Matrix.mul_apply]
    simp [pascalSortedEigenvalueDiagonal,
      Matrix.diagonal_apply, pascalSortedEigenvectorMatrix_apply]
  rw [hrhs]
  simpa [Matrix.mulVec, dotProduct,
    pascalSortedEigenvectorMatrix_apply, mul_comm] using heig

/-- For an entrywise-positive finite matrix, an eigenvector belonging to the
eigenvalue of a strictly positive eigenvector is unique up to scale.  This is
the elementary ratio argument underlying the simple Perron root. -/
theorem positiveMatrix_eigenvector_unique_up_to_smul
    {n : ℕ} (hn : 0 < n) (A : RSqMat n) (rho : ℝ)
    (p : RVec n) (hp : ∀ i, 0 < p i)
    (hA : ∀ i j, 0 < A i j)
    (heigp : Matrix.mulVec A p = rho • p)
    (x : RVec n) (heigx : Matrix.mulVec A x = rho • x) :
    ∃ t : ℝ, x = t • p := by
  letI : Nonempty (Fin n) := ⟨⟨0, hn⟩⟩
  let ratio : Fin n → ℝ := fun i => x i / p i
  obtain ⟨i₀, hi₀⟩ := Finite.exists_max ratio
  let t := ratio i₀
  let z : RVec n := t • p - x
  have hz_nonneg : ∀ i, 0 ≤ z i := by
    intro i
    change 0 ≤ t * p i - x i
    rw [sub_nonneg]
    apply (div_le_iff₀ (hp i)).mp
    exact hi₀ i
  have hz_i₀ : z i₀ = 0 := by
    change t * p i₀ - x i₀ = 0
    dsimp [t, ratio]
    rw [div_mul_cancel₀ _ (hp i₀).ne']
    ring
  have heigz : Matrix.mulVec A z = rho • z := by
    rw [show z = t • p - x by rfl, Matrix.mulVec_sub,
      Matrix.mulVec_smul, heigp, heigx]
    module
  have hz_zero : z = 0 := by
    by_contra hz
    have hex : ∃ j, z j ≠ 0 := by
      by_contra h
      push_neg at h
      exact hz (funext h)
    obtain ⟨j, hj⟩ := hex
    have hzj : 0 < z j := lt_of_le_of_ne (hz_nonneg j) (Ne.symm hj)
    have hAz : 0 < Matrix.mulVec A z i₀ := by
      simp only [Matrix.mulVec, dotProduct]
      apply Finset.sum_pos'
      · intro q _
        exact mul_nonneg (le_of_lt (hA i₀ q)) (hz_nonneg q)
      · exact ⟨j, Finset.mem_univ j, mul_pos (hA i₀ j) hzj⟩
    have heigz_i := congrFun heigz i₀
    simp only [Pi.smul_apply, smul_eq_mul, hz_i₀, mul_zero] at heigz_i
    exact (ne_of_gt hAz) heigz_i
  refine ⟨t, ?_⟩
  have := sub_eq_zero.mp hz_zero
  exact this.symm

theorem compoundMatrix_transpose (n k : ℕ) (A : RSqMat n) :
    compoundMatrix n k A.transpose = (compoundMatrix n k A).transpose := by
  ext s t
  simp only [Matrix.transpose_apply]
  rw [compoundMatrix_apply, compoundMatrix_apply]
  change Matrix.det (fun i j =>
      A (Set.powersetCard.ofFinEmbEquiv.symm t j)
        (Set.powersetCard.ofFinEmbEquiv.symm s i)) = _
  rw [← Matrix.det_transpose]
  rfl

theorem compoundMatrix_one (n k : ℕ) :
    compoundMatrix n k (1 : RSqMat n) = 1 := by
  unfold compoundMatrix
  rw [Matrix.toLin'_one, exteriorPower.map_id]
  exact LinearMap.toMatrix_id
    ((Pi.basisFun ℝ (Fin n)).exteriorPower k)

theorem compoundMatrix_pascal_pos
    {n k : ℕ} (hk : 0 < k)
    (s t : Set.powersetCard (Fin n) k) :
    0 < compoundMatrix n k (pascalMatrix n) s t := by
  rw [compoundMatrix_apply]
  exact pascalMatrix_isStrictlyTotallyPositive n k hk
    (Set.powersetCard.ofFinEmbEquiv.symm s)
    (Set.powersetCard.ofFinEmbEquiv.symm t)
    (Set.powersetCard.ofFinEmbEquiv.symm s).strictMono
    (Set.powersetCard.ofFinEmbEquiv.symm t).strictMono

theorem compoundMatrix_sortedEigenvectorMatrix_transpose_mul_self
    (n k : ℕ) :
    (compoundMatrix n k (pascalSortedEigenvectorMatrix n)).transpose *
        compoundMatrix n k (pascalSortedEigenvectorMatrix n) = 1 := by
  rw [← compoundMatrix_transpose, ← compoundMatrix_mul,
    pascalSortedEigenvectorMatrix_transpose_mul_self, compoundMatrix_one]

theorem compoundMatrix_sortedEigenvectorMatrix_mul_transpose
    (n k : ℕ) :
    compoundMatrix n k (pascalSortedEigenvectorMatrix n) *
        (compoundMatrix n k (pascalSortedEigenvectorMatrix n)).transpose = 1 := by
  rw [← compoundMatrix_transpose, ← compoundMatrix_mul,
    pascalSortedEigenvectorMatrix_mul_transpose, compoundMatrix_one]

/-- The subset of the first `k` indices inside `Fin n`. -/
noncomputable def initialPowerset {n k : ℕ} (hkn : k ≤ n) :
    Set.powersetCard (Fin n) k :=
  Set.powersetCard.ofFinEmbEquiv
    (OrderEmbedding.ofStrictMono (Fin.castLE hkn)
      (Fin.strictMono_castLE hkn))

/-- Product of the first `k` decreasingly sorted Pascal eigenvalues. -/
noncomputable def pascalLeadingEigenvalueProduct
    (n k : ℕ) (hkn : k ≤ n) : ℝ :=
  ∏ j : Fin k, pascalSortedEigenvalue n (Fin.castLE hkn j)

/-- Plücker coordinate vector of the leading `k`-dimensional Pascal spectral
subspace. -/
noncomputable def pascalLeadingPlucker
    (n k : ℕ) (hkn : k ≤ n) :
    Set.powersetCard (Fin n) k → ℝ :=
  fun s => compoundMatrix n k (pascalSortedEigenvectorMatrix n) s
    (initialPowerset hkn)

theorem compoundMatrix_sortedEigenvalueDiagonal_initial_column
    {n k : ℕ} (hkn : k ≤ n)
    (s : Set.powersetCard (Fin n) k) :
    compoundMatrix n k (pascalSortedEigenvalueDiagonal n) s
        (initialPowerset hkn) =
      if s = initialPowerset hkn then
        pascalLeadingEigenvalueProduct n k hkn
      else 0 := by
  classical
  split
  · next hs =>
    subst s
    rw [compoundMatrix_apply]
    have hmatrix : (fun i j : Fin k =>
        pascalSortedEigenvalueDiagonal n
          (Set.powersetCard.ofFinEmbEquiv.symm
            (initialPowerset hkn) i)
          (Set.powersetCard.ofFinEmbEquiv.symm
            (initialPowerset hkn) j)) =
        Matrix.diagonal (fun j : Fin k =>
          pascalSortedEigenvalue n (Fin.castLE hkn j)) := by
      ext i j
      simp [initialPowerset, pascalSortedEigenvalueDiagonal,
        Matrix.diagonal_apply]
    rw [hmatrix, Matrix.det_diagonal]
    rfl
  · next hs =>
    rw [compoundMatrix_apply]
    obtain ⟨a, ha0, ha1⟩ :=
      (Set.powersetCard.exists_mem_notMem_iff_ne
        (initialPowerset hkn) s).mp (Ne.symm hs)
    obtain ⟨j, rfl⟩ :=
      (Set.powersetCard.mem_range_ofFinEmbEquiv_symm_iff_mem
        (initialPowerset hkn) a).mpr ha0
    apply Matrix.det_eq_zero_of_column_eq_zero j
    intro i
    simp only [pascalSortedEigenvalueDiagonal, Matrix.diagonal_apply]
    split
    · next hij =>
      exfalso
      apply ha1
      rw [← hij]
      apply (Set.powersetCard.mem_range_ofFinEmbEquiv_symm_iff_mem
        s _).mp
      exact ⟨i, rfl⟩
    · rfl

theorem compoundMatrix_pascal_mul_leadingPlucker
    {n k : ℕ} (hkn : k ≤ n) :
    Matrix.mulVec (compoundMatrix n k (pascalMatrix n))
        (pascalLeadingPlucker n k hkn) =
      pascalLeadingEigenvalueProduct n k hkn •
        pascalLeadingPlucker n k hkn := by
  have hmat :
      compoundMatrix n k (pascalMatrix n) *
          compoundMatrix n k (pascalSortedEigenvectorMatrix n) =
        compoundMatrix n k (pascalSortedEigenvectorMatrix n) *
          compoundMatrix n k (pascalSortedEigenvalueDiagonal n) := by
    calc
      compoundMatrix n k (pascalMatrix n) *
          compoundMatrix n k (pascalSortedEigenvectorMatrix n) =
        compoundMatrix n k
          (pascalMatrix n * pascalSortedEigenvectorMatrix n) := by
            rw [compoundMatrix_mul]
      _ = compoundMatrix n k
          (pascalSortedEigenvectorMatrix n *
            pascalSortedEigenvalueDiagonal n) := by
              rw [pascalMatrix_mul_sortedEigenvectorMatrix]
      _ = compoundMatrix n k (pascalSortedEigenvectorMatrix n) *
          compoundMatrix n k (pascalSortedEigenvalueDiagonal n) := by
            rw [compoundMatrix_mul]
  funext s
  have hs := congrArg
    (fun M : Matrix (Set.powersetCard (Fin n) k)
      (Set.powersetCard (Fin n) k) ℝ => M s (initialPowerset hkn)) hmat
  simp only [Matrix.mul_apply] at hs
  simpa [Matrix.mulVec, dotProduct, pascalLeadingPlucker,
    compoundMatrix_sortedEigenvalueDiagonal_initial_column,
    Pi.smul_apply, smul_eq_mul, mul_comm] using hs

/-- A Boolean sign choice is compatible with `x` when it records `true` on
positive entries and `false` on negative entries; zero entries may receive
either sign. -/
def IsSignCompletion {n : ℕ} (x : RVec n) (s : Fin n → Bool) : Prop :=
  ∀ i, (0 < x i → s i = true) ∧ (x i < 0 → s i = false)

/-- Adjacent sign changes of a Boolean sign word.  The recursive form is
equivalent to counting the filtered adjacent pairs and supports induction on
zero-compatible sign completions. -/
def boolSignChangeCount : {n : ℕ} → (Fin (n + 1) → Bool) → ℕ
  | 0, _ => 0
  | n + 1, s =>
      (if s 0 ≠ s 1 then 1 else 0) +
        boolSignChangeCount (fun i : Fin (n + 1) => s i.succ)

/-- Maximum zero-compatible sign changes, expressed without choosing a
particular maximizing completion. -/
def HasAtLeastSignChanges {n : ℕ} (x : RVec (n + 1)) (k : ℕ) : Prop :=
  ∃ s : Fin (n + 1) → Bool,
    IsSignCompletion x s ∧ k ≤ boolSignChangeCount s

/-- `x` has exactly `k` sign changes in the standard convention that a zero
component may be assigned either neighboring sign. -/
def HasExactlySignChanges {n : ℕ} (x : RVec (n + 1)) (k : ℕ) : Prop :=
  HasAtLeastSignChanges x k ∧ ¬ HasAtLeastSignChanges x (k + 1)

end NumStability
