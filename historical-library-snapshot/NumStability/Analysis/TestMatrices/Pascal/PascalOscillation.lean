import Mathlib.Algebra.BigOperators.Fin
import Mathlib.Algebra.BigOperators.Group.Finset.Basic
import Mathlib.Algebra.BigOperators.Intervals
import Mathlib.Algebra.BigOperators.Ring.Finset
import Mathlib.Algebra.Field.GeomSum
import Mathlib.Algebra.Module.TransferInstance
import Mathlib.Algebra.Order.BigOperators.Group.Finset
import Mathlib.Algebra.Order.BigOperators.Ring.Finset
import Mathlib.Algebra.Order.GroupWithZero.Finset
import Mathlib.Algebra.Order.Ring.Pow
import Mathlib.Algebra.Polynomial.Basic
import Mathlib.Algebra.Polynomial.Roots
import Mathlib.Analysis.CStarAlgebra.CStarMatrix
import Mathlib.Analysis.CStarAlgebra.Classes
import Mathlib.Analysis.CStarAlgebra.ContinuousFunctionalCalculus.Integral
import Mathlib.Analysis.CStarAlgebra.ContinuousFunctionalCalculus.Order
import Mathlib.Analysis.CStarAlgebra.ContinuousFunctionalCalculus.Pi
import Mathlib.Analysis.CStarAlgebra.Matrix
import Mathlib.Analysis.Calculus.DSlope
import Mathlib.Analysis.Calculus.Deriv.MeanValue
import Mathlib.Analysis.Calculus.DiffContOnCl
import Mathlib.Analysis.Complex.ExponentialBounds
import Mathlib.Analysis.Complex.Hadamard
import Mathlib.Analysis.Complex.Polynomial.Basic
import Mathlib.Analysis.Complex.Trigonometric
import Mathlib.Analysis.Convex.Basic
import Mathlib.Analysis.Convex.Jensen
import Mathlib.Analysis.InnerProductSpace.Positive
import Mathlib.Analysis.InnerProductSpace.Trace
import Mathlib.Analysis.Matrix.HermitianFunctionalCalculus
import Mathlib.Analysis.Matrix.Normed
import Mathlib.Analysis.Matrix.Order
import Mathlib.Analysis.Matrix.PosDef
import Mathlib.Analysis.Matrix.Spectrum
import Mathlib.Analysis.MeanInequalitiesPow
import Mathlib.Analysis.Normed.Algebra.MatrixExponential
import Mathlib.Analysis.Normed.Module.Basic
import Mathlib.Analysis.Normed.Module.HahnBanach
import Mathlib.Analysis.SpecialFunctions.ContinuousFunctionalCalculus.ExpLog.Basic
import Mathlib.Analysis.SpecialFunctions.ContinuousFunctionalCalculus.ExpLog.Order
import Mathlib.Analysis.SpecialFunctions.ExpDeriv
import Mathlib.Analysis.SpecialFunctions.Exponential
import Mathlib.Analysis.SpecialFunctions.Integrals.Basic
import Mathlib.Analysis.SpecialFunctions.Log.Basic
import Mathlib.Analysis.SpecialFunctions.Log.Deriv
import Mathlib.Analysis.SpecialFunctions.Log.NegMulLog
import Mathlib.Analysis.SpecialFunctions.Pow.Real
import Mathlib.Analysis.SpecialFunctions.Stirling
import Mathlib.Analysis.SpecialFunctions.Trigonometric.Basic
import Mathlib.Data.Fin.Tuple.Sort
import Mathlib.Data.Finset.Max
import Mathlib.Data.Fintype.Basic
import Mathlib.Data.Fintype.BigOperators
import Mathlib.Data.Fintype.Sort
import Mathlib.Data.Matrix.Basic
import Mathlib.Data.Matrix.Basis
import Mathlib.Data.Matrix.Block
import Mathlib.Data.Nat.Choose.Cast
import Mathlib.Data.Nat.Choose.Sum
import Mathlib.Data.Nat.Choose.Vandermonde
import Mathlib.Data.Nat.Digits.Lemmas
import Mathlib.Data.Real.Basic
import Mathlib.Data.Real.Sqrt
import Mathlib.Data.Sign.Basic
import Mathlib.LinearAlgebra.Basis.Flag
import Mathlib.LinearAlgebra.Basis.VectorSpace
import Mathlib.LinearAlgebra.Charpoly.ToMatrix
import Mathlib.LinearAlgebra.Eigenspace.Charpoly
import Mathlib.LinearAlgebra.Eigenspace.Triangularizable
import Mathlib.LinearAlgebra.ExteriorPower.Basis
import Mathlib.LinearAlgebra.Finsupp.Pi
import Mathlib.LinearAlgebra.Matrix.Block
import Mathlib.LinearAlgebra.Matrix.Charpoly.Coeff
import Mathlib.LinearAlgebra.Matrix.FiniteDimensional
import Mathlib.LinearAlgebra.Matrix.Irreducible.Defs
import Mathlib.LinearAlgebra.Matrix.NonsingularInverse
import Mathlib.LinearAlgebra.Matrix.PosDef
import Mathlib.LinearAlgebra.Matrix.Rank
import Mathlib.LinearAlgebra.Matrix.SchurComplement
import Mathlib.LinearAlgebra.Matrix.Symmetric
import Mathlib.LinearAlgebra.Matrix.ToLinearEquiv
import Mathlib.LinearAlgebra.UnitaryGroup
import Mathlib.LinearAlgebra.Vandermonde
import Mathlib.Logic.Equiv.Fin.Basic
import Mathlib.MeasureTheory.Constructions.Pi
import Mathlib.MeasureTheory.Integral.Bochner.Basic
import Mathlib.MeasureTheory.Measure.Haar.Basic
import Mathlib.Order.Interval.Finset.Fin
import Mathlib.Order.Interval.Finset.Nat
import Mathlib.Probability.Distributions.Gaussian.Real
import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.FinCases
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.NormNum
import Mathlib.Tactic.Push
import Mathlib.Tactic.Ring
import Mathlib.Topology.Algebra.Polynomial
import Mathlib.Topology.ContinuousMap.Weierstrass
import Mathlib.Topology.Instances.Matrix
import Mathlib.Topology.MetricSpace.ProperSpace
import NumStability.Algorithms.LinearSystems.QR.HouseholderReflector
import NumStability.Algorithms.LinearSystems.QR.Householder.TrailingPanels
import NumStability.Analysis.Conditioning.LinearSystems.PerronFrobenius
import NumStability.Analysis.MatrixAlgebra
import NumStability.Analysis.MatrixSpectral
import NumStability.Analysis.PerturbationTheory
import NumStability.Analysis.TestMatrices.Pascal.Basic
import NumStability.Analysis.TestMatrices.Pascal.Exact
import NumStability.Analysis.TestMatrices.Pascal.PascalSpectral
import NumStability.Analysis.TestMatrices.Pascal.PascalTotalPositivity

/-!
# NumStability Analysis TestMatrices Pascal PascalOscillation

Canonical destination for material split out of
`NumStability.Algorithms.TestMatrices.Higham28PascalOscillation` by wave W09 of the August 2026 repository reorganization.
Declaration names, statements and proofs are unchanged; only the
module they live in has changed. The historical module still
resolves and re-exports this one.
-/

namespace NumStability

open scoped BigOperators

open Set

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

/-- Orthogonal eigenvector matrix with columns in decreasing eigenvalue order. -/
noncomputable def pascalSortedEigenvectorMatrix (n : ℕ) : RSqMat n :=
  (EuclideanSpace.basisFun (Fin n) ℝ).toBasis.toMatrix
    (pascalSortedEigenbasis n).toBasis

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
