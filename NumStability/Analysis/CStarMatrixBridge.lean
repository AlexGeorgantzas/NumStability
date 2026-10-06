-- Analysis/CStarMatrixBridge.lean
--
-- Bridges from repository-native finite real matrices to complex C⋆-matrices.

import NumStability.Analysis.MatrixAlgebra
import Mathlib.Analysis.CStarAlgebra.CStarMatrix
import Mathlib.Analysis.CStarAlgebra.ContinuousFunctionalCalculus.Order
import Mathlib.Analysis.Matrix.Order
import Mathlib.Data.Matrix.Block

namespace NumStability

open scoped ComplexOrder MatrixOrder

/-!
## Real finite matrices as complex C⋆-matrices

The trace-MGF route for matrix concentration eventually needs mathlib's
complex `CStarMatrix` continuous-functional-calculus API.  This file records
the algebraic bridge from the repository's finite real matrix convention to
that type.

These lemmas prove the entrywise, self-adjointness, local PSD/Loewner-order,
and positive-identity regularization parts of the finite-real-to-complex-C⋆
bridge.  They do not prove trace-MGF domination or a matrix
Bernstein/Khintchine theorem.
-/

/-- Embed a repository-native finite real square matrix into the complex
`CStarMatrix` type used by mathlib's C⋆-algebraic functional calculus. -/
noncomputable def finiteComplexCStarMatrix {ι : Type*}
    (M : ι → ι → ℝ) : CStarMatrix ι ι ℂ :=
  CStarMatrix.ofMatrix (fun i j => (M i j : ℂ))

@[simp]
theorem finiteComplexCStarMatrix_apply {ι : Type*}
    (M : ι → ι → ℝ) (i j : ι) :
    finiteComplexCStarMatrix M i j = (M i j : ℂ) := rfl

/-- The complex C⋆-matrix embedding preserves zero. -/
@[simp]
theorem finiteComplexCStarMatrix_zero {ι : Type*} :
    finiteComplexCStarMatrix (fun _ _ : ι => 0) =
      (0 : CStarMatrix ι ι ℂ) := by
  ext i j
  simp

/-- The complex C⋆-matrix embedding preserves addition. -/
theorem finiteComplexCStarMatrix_add
    {ι : Type*} (M N : ι → ι → ℝ) :
    finiteComplexCStarMatrix (fun i j => M i j + N i j) =
      finiteComplexCStarMatrix M + finiteComplexCStarMatrix N := by
  ext i j
  simp

/-- The complex C⋆-matrix embedding preserves real scalar multiplication. -/
theorem finiteComplexCStarMatrix_smul
    {ι : Type*} (a : ℝ) (M : ι → ι → ℝ) :
    finiteComplexCStarMatrix (fun i j => a * M i j) =
      (a : ℂ) • finiteComplexCStarMatrix M := by
  ext i j
  simp

/-- The complex C⋆-matrix embedding preserves finite real matrix
multiplication. -/
theorem finiteComplexCStarMatrix_mul
    {ι : Type*} [Fintype ι] (M N : ι → ι → ℝ) :
    finiteComplexCStarMatrix (finiteMatMul M N) =
      finiteComplexCStarMatrix M * finiteComplexCStarMatrix N := by
  ext i j
  simp [finiteMatMul, CStarMatrix.mul_apply]

/-- Symmetric real finite matrices embed as self-adjoint complex C⋆-matrices. -/
theorem finiteComplexCStarMatrix_isSelfAdjoint_of_symmetric
    {ι : Type*} (M : ι → ι → ℝ) (hM : IsSymmetricFiniteMatrix M) :
    IsSelfAdjoint (finiteComplexCStarMatrix M) := by
  rw [isSelfAdjoint_iff]
  ext i j
  rw [CStarMatrix.star_apply]
  simp [hM j i]

/-- The complex C⋆-matrix embedding preserves finite real matrix subtraction. -/
theorem finiteComplexCStarMatrix_sub
    {ι : Type*} (M N : ι → ι → ℝ) :
    finiteComplexCStarMatrix (fun i j => M i j - N i j) =
      finiteComplexCStarMatrix M - finiteComplexCStarMatrix N := by
  ext i j
  simp

/-- The complex C⋆-matrix embedding preserves negation. -/
theorem finiteComplexCStarMatrix_neg
    {ι : Type*} (M : ι → ι → ℝ) :
    finiteComplexCStarMatrix (fun i j => -M i j) =
      -finiteComplexCStarMatrix M := by
  ext i j
  simp

/-- The complex C⋆-matrix embedding preserves finite sums. -/
theorem finiteComplexCStarMatrix_finset_sum
    {α ι : Type*} [DecidableEq α]
    (s : Finset α) (F : α → ι → ι → ℝ) :
    finiteComplexCStarMatrix (fun i j => s.sum (fun a => F a i j)) =
      s.sum (fun a => finiteComplexCStarMatrix (F a)) := by
  classical
  ext i j
  change ((s.sum fun a => F a i j : ℝ) : ℂ) =
    (s.sum fun a => finiteComplexCStarMatrix (F a)) i j
  revert i j
  refine Finset.induction_on s ?base ?step
  · intro i j
    simp
  · intro a s ha ih i j
    rw [Finset.sum_insert ha]
    rw [Finset.sum_insert ha]
    simp [ih i j]

/-- The finite real identity embeds as the complex C⋆-matrix identity. -/
theorem finiteComplexCStarMatrix_finiteIdMatrix
    {ι : Type*} [DecidableEq ι] :
    finiteComplexCStarMatrix (finiteIdMatrix : ι → ι → ℝ) =
      (1 : CStarMatrix ι ι ℂ) := by
  ext i j
  by_cases hij : i = j
  · subst hij
    simp [finiteIdMatrix]
  · simp [finiteIdMatrix, hij]

/-- Scalar multiples of the finite real identity embed as scalar multiples of
the complex C⋆-matrix identity. -/
theorem finiteComplexCStarMatrix_smul_finiteIdMatrix
    {ι : Type*} [DecidableEq ι] (a : ℝ) :
    finiteComplexCStarMatrix (fun i j : ι => a * finiteIdMatrix i j) =
      (a : ℂ) • (1 : CStarMatrix ι ι ℂ) := by
  ext i j
  by_cases hij : i = j
  · subst hij
    simp [finiteIdMatrix]
  · simp [finiteIdMatrix, hij]

/-- Finite complex `CStarMatrix` spaces are finite-dimensional complex vector
spaces.  The proof unfolds the type synonym to the finite Pi-space
`m → n → ℂ`. -/
noncomputable instance cstarMatrix_complex_finiteDimensional
    {m n : Type*} [Fintype m] [Fintype n] :
    FiniteDimensional ℂ (CStarMatrix m n ℂ) := by
  change FiniteDimensional ℂ (m → n → ℂ)
  infer_instance

/-- A locally PSD real finite matrix embeds as a nonnegative complex
C⋆-matrix. -/
theorem finiteComplexCStarMatrix_nonneg_of_finitePSD
    {ι : Type*} [Fintype ι] [DecidableEq ι]
    (M : ι → ι → ℝ) (hM : IsSymmetricFiniteMatrix M) (hPSD : finitePSD M) :
    0 ≤ finiteComplexCStarMatrix M := by
  have hmat : Matrix.PosSemidef (M : Matrix ι ι ℝ) :=
    finitePSD.to_matrix_posSemidef M hM hPSD
  set_option linter.deprecated false in
  rw [Matrix.posSemidef_iff_eq_conjTranspose_mul_self] at hmat
  rcases hmat with ⟨B, hB⟩
  let C : CStarMatrix ι ι ℂ := finiteComplexCStarMatrix (fun i j => B i j)
  have h_eq : finiteComplexCStarMatrix M = star C * C := by
    ext i j
    have hij := congrArg (fun A : Matrix ι ι ℝ => A i j) hB
    rw [CStarMatrix.mul_apply]
    simp_rw [CStarMatrix.star_apply]
    simp [C, finiteComplexCStarMatrix, Matrix.mul_apply] at hij ⊢
    rw [hij]
    simp
  rw [h_eq, StarOrderedRing.nonneg_iff]
  exact AddSubmonoid.subset_closure ⟨C, rfl⟩

/-- Plain finite-matrix positive semidefiniteness gives spectral-order
nonnegativity of the corresponding complex `CStarMatrix`.

This is the complex counterpart of
`finiteComplexCStarMatrix_nonneg_of_finitePSD`.  It is a bridge lemma for
routes that prove a Loewner inequality by ordinary finite matrix arguments
and then need to return to the C⋆-matrix order used by functional calculus. -/
theorem cstarMatrix_nonneg_of_matrix_posSemidef
    {ι : Type*} [Fintype ι] [DecidableEq ι]
    {M : CStarMatrix ι ι ℂ}
    (hM : Matrix.PosSemidef (CStarMatrix.ofMatrix.symm M : Matrix ι ι ℂ)) :
    0 ≤ M := by
  set_option linter.deprecated false in
  rw [Matrix.posSemidef_iff_eq_conjTranspose_mul_self] at hM
  rcases hM with ⟨B, hB⟩
  let C : CStarMatrix ι ι ℂ := CStarMatrix.ofMatrix B
  have h_eq : M = star C * C := by
    apply CStarMatrix.ofMatrix.symm.injective
    simpa [C, CStarMatrix.mul_apply, CStarMatrix.conjTranspose_apply] using hB
  rw [h_eq, StarOrderedRing.nonneg_iff]
  exact AddSubmonoid.subset_closure ⟨C, rfl⟩

/-- Plain finite-matrix Loewner inequalities lift to spectral-order
inequalities of the corresponding complex `CStarMatrix` objects. -/
theorem cstarMatrix_le_of_matrix_le
    {ι : Type*} [Fintype ι] [DecidableEq ι]
    {A B : CStarMatrix ι ι ℂ}
    (hAB : (CStarMatrix.ofMatrix.symm A : Matrix ι ι ℂ) ≤
      CStarMatrix.ofMatrix.symm B) :
    A ≤ B := by
  have hpsd :
      Matrix.PosSemidef (CStarMatrix.ofMatrix.symm (B - A) : Matrix ι ι ℂ) := by
    have hmat := Matrix.le_iff.mp hAB
    simpa using hmat
  have hnon : 0 ≤ B - A := cstarMatrix_nonneg_of_matrix_posSemidef hpsd
  exact sub_nonneg.mp hnon

/-- A local finite Loewner inequality between symmetric real finite matrices
embeds as the complex C⋆-matrix spectral-order inequality. -/
theorem finiteComplexCStarMatrix_le_of_finiteLoewnerLe
    {ι : Type*} [Fintype ι] [DecidableEq ι]
    (M N : ι → ι → ℝ)
    (hM : IsSymmetricFiniteMatrix M) (hN : IsSymmetricFiniteMatrix N)
    (hLe : finiteLoewnerLe M N) :
    finiteComplexCStarMatrix M ≤ finiteComplexCStarMatrix N := by
  have hDsym : IsSymmetricFiniteMatrix (fun i j => N i j - M i j) := by
    intro i j
    change N i j - M i j = N j i - M j i
    rw [hN i j, hM i j]
  have hDpsd : finitePSD (fun i j => N i j - M i j) :=
    (finiteLoewnerLe_iff_sub_finitePSD M N).mp hLe
  have hnonneg :=
    finiteComplexCStarMatrix_nonneg_of_finitePSD
      (fun i j => N i j - M i j) hDsym hDpsd
  rw [finiteComplexCStarMatrix_sub N M] at hnonneg
  exact sub_nonneg.mp hnonneg

/-- A strictly positive real scalar multiple of the complex C⋆-matrix identity
is strictly positive.  This is the regularizing identity term used before
applying operator logarithms. -/
theorem cstarMatrix_pos_real_smul_one_isStrictlyPositive
    {ι : Type*} [Fintype ι] [DecidableEq ι] {eps : ℝ} (heps : 0 < eps) :
    IsStrictlyPositive ((eps : ℂ) • (1 : CStarMatrix ι ι ℂ)) := by
  have hunit : IsUnit ((eps : ℂ) • (1 : CStarMatrix ι ι ℂ)) := by
    refine isUnit_iff_exists.mpr
      ⟨((eps : ℂ)⁻¹) • (1 : CStarMatrix ι ι ℂ), ?_⟩
    constructor
    · simp [Algebra.mul_smul_comm, smul_smul, heps.ne']
    · simp [Algebra.mul_smul_comm, smul_smul, heps.ne']
  have hnonneg : 0 ≤ ((eps : ℂ) • (1 : CStarMatrix ι ι ℂ)) := by
    rw [StarOrderedRing.nonneg_iff]
    refine AddSubmonoid.subset_closure
      ⟨((Real.sqrt eps : ℂ) • (1 : CStarMatrix ι ι ℂ)), ?_⟩
    have hsqrt :
        ((Real.sqrt eps : ℂ) * (Real.sqrt eps : ℂ)) = (eps : ℂ) := by
      rw [← sq]
      exact_mod_cast Real.sq_sqrt (le_of_lt heps)
    simp [Algebra.mul_smul_comm, smul_smul, hsqrt]
  exact hunit.isStrictlyPositive hnonneg

/-- Adding a strictly positive scalar identity regularization to an embedded
local PSD matrix gives a strictly positive complex C⋆-matrix. -/
theorem finiteComplexCStarMatrix_add_pos_smul_one_isStrictlyPositive_of_finitePSD
    {ι : Type*} [Fintype ι] [DecidableEq ι]
    (M : ι → ι → ℝ) (hM : IsSymmetricFiniteMatrix M) (hPSD : finitePSD M)
    {eps : ℝ} (heps : 0 < eps) :
    IsStrictlyPositive
      (finiteComplexCStarMatrix M + (eps : ℂ) • (1 : CStarMatrix ι ι ℂ)) := by
  have hnonneg : 0 ≤ finiteComplexCStarMatrix M :=
    finiteComplexCStarMatrix_nonneg_of_finitePSD M hM hPSD
  have hstrict :
      IsStrictlyPositive ((eps : ℂ) • (1 : CStarMatrix ι ι ℂ)) :=
    cstarMatrix_pos_real_smul_one_isStrictlyPositive heps
  exact IsStrictlyPositive.nonneg_add hnonneg hstrict

/-- Adding the same scalar identity regularization preserves an embedded local
finite Loewner inequality. -/
theorem finiteComplexCStarMatrix_add_smul_one_le_of_finiteLoewnerLe
    {ι : Type*} [Fintype ι] [DecidableEq ι]
    (M N : ι → ι → ℝ)
    (hM : IsSymmetricFiniteMatrix M) (hN : IsSymmetricFiniteMatrix N)
    (hLe : finiteLoewnerLe M N) (eps : ℝ) :
    finiteComplexCStarMatrix M + (eps : ℂ) • (1 : CStarMatrix ι ι ℂ) ≤
      finiteComplexCStarMatrix N + (eps : ℂ) • (1 : CStarMatrix ι ι ℂ) := by
  simpa [add_comm, add_left_comm, add_assoc] using
    add_le_add_right
      (finiteComplexCStarMatrix_le_of_finiteLoewnerLe M N hM hN hLe)
      ((eps : ℂ) • (1 : CStarMatrix ι ι ℂ))

/-!
## Block C⋆-matrix algebra

The Hansen--Pedersen route to matrix Jensen uses a block diagonal matrix
`diag(T₁,T₂)` and a vertical isometry `[A;B]`.  The lemmas below record the
entrywise block algebra needed before any functional-calculus argument can be
applied.
-/

/-- Rectangular associativity for `CStarMatrix` multiplication.  Mathlib's
square semiring associativity does not fire reliably for rectangular products,
so this entrywise wrapper is useful for block-column compression algebra. -/
theorem cstarMatrix_mul_assoc_rect {α β γ δ : Type*}
    [Fintype β] [Fintype γ] [DecidableEq γ] [DecidableEq δ]
    (A : CStarMatrix α β ℂ) (B : CStarMatrix β γ ℂ)
    (C : CStarMatrix γ δ ℂ) :
    (A * B) * C = A * (B * C) := by
  ext i j
  simp [CStarMatrix.mul_apply, Finset.sum_mul, Finset.mul_sum, mul_assoc]
  rw [Finset.sum_comm]

/-- Right distributivity for rectangular `CStarMatrix` multiplication. -/
theorem cstarMatrix_mul_add_rect {α β γ : Type*}
    [Fintype β] (A : CStarMatrix α β ℂ)
    (B C : CStarMatrix β γ ℂ) :
    A * (B + C) = A * B + A * C := by
  ext i j
  simp [CStarMatrix.mul_apply, mul_add, Finset.sum_add_distrib]

/-- Left distributivity for rectangular `CStarMatrix` multiplication. -/
theorem cstarMatrix_add_mul_rect {α β γ : Type*}
    [Fintype β] (A B : CStarMatrix α β ℂ)
    (C : CStarMatrix β γ ℂ) :
    (A + B) * C = A * C + B * C := by
  ext i j
  simp [CStarMatrix.mul_apply, add_mul, Finset.sum_add_distrib]

/-- Pull a scalar through the right factor of a rectangular multiplication. -/
theorem cstarMatrix_mul_smul_rect {α β γ : Type*}
    [Fintype β] (a : ℂ) (A : CStarMatrix α β ℂ)
    (B : CStarMatrix β γ ℂ) :
    A * (a • B) = a • (A * B) := by
  ext i j
  simp [CStarMatrix.mul_apply]
  calc
    (∑ x, A i x * (a * B x j))
        = ∑ x, a * (A i x * B x j) := by
          apply Finset.sum_congr rfl
          intro x _
          ring
    _ = a * ∑ x, A i x * B x j := by
          rw [Finset.mul_sum]

/-- Pull a scalar through the left factor of a rectangular multiplication. -/
theorem cstarMatrix_smul_mul_rect {α β γ : Type*}
    [Fintype β] (a : ℂ) (A : CStarMatrix α β ℂ)
    (B : CStarMatrix β γ ℂ) :
    (a • A) * B = a • (A * B) := by
  ext i j
  simp [CStarMatrix.mul_apply]
  calc
    (∑ x, (a * A i x) * B x j)
        = ∑ x, a * (A i x * B x j) := by
          apply Finset.sum_congr rfl
          intro x _
          ring
    _ = a * ∑ x, A i x * B x j := by
          rw [Finset.mul_sum]

/-- Right identity for rectangular `CStarMatrix` multiplication. -/
theorem cstarMatrix_mul_one_rect {α β : Type*}
    [Fintype β] [DecidableEq β] (A : CStarMatrix α β ℂ) :
    A * (1 : CStarMatrix β β ℂ) = A := by
  ext i j
  simp [CStarMatrix.mul_apply, CStarMatrix.one_apply]

/-- Left identity for rectangular `CStarMatrix` multiplication. -/
theorem cstarMatrix_one_mul_rect {α β : Type*}
    [Fintype α] [DecidableEq α] [DecidableEq β]
    (A : CStarMatrix α β ℂ) :
    (1 : CStarMatrix α α ℂ) * A = A := by
  ext i j
  simp [CStarMatrix.mul_apply, CStarMatrix.one_apply]

/-- Compression by a rectangular `CStarMatrix` distributes over addition. -/
theorem cstarMatrix_compression_add
    {α β : Type*} [Fintype α] [Fintype β]
    (V : CStarMatrix α β ℂ) (M N : CStarMatrix α α ℂ) :
    CStarMatrix.conjTranspose V * (M + N) * V =
      CStarMatrix.conjTranspose V * M * V +
        CStarMatrix.conjTranspose V * N * V := by
  rw [cstarMatrix_mul_add_rect, cstarMatrix_add_mul_rect]

/-- Compression by a rectangular `CStarMatrix` distributes over subtraction. -/
theorem cstarMatrix_compression_sub
    {α β : Type*} [Fintype α] [Fintype β]
    (V : CStarMatrix α β ℂ) (M N : CStarMatrix α α ℂ) :
    CStarMatrix.conjTranspose V * (M - N) * V =
      CStarMatrix.conjTranspose V * M * V -
        CStarMatrix.conjTranspose V * N * V := by
  rw [sub_eq_add_neg, cstarMatrix_mul_add_rect, cstarMatrix_add_mul_rect]
  have hneg :
      CStarMatrix.conjTranspose V * (-N) * V =
        -(CStarMatrix.conjTranspose V * N * V) := by
    ext i j
    simp [CStarMatrix.mul_apply]
  rw [hneg]
  rfl

/-- Compression by a rectangular `CStarMatrix` commutes with scalar
multiplication. -/
theorem cstarMatrix_compression_smul
    {α β : Type*} [Fintype α] [Fintype β]
    (V : CStarMatrix α β ℂ) (a : ℂ) (M : CStarMatrix α α ℂ) :
    CStarMatrix.conjTranspose V * (a • M) * V =
      a • (CStarMatrix.conjTranspose V * M * V) := by
  rw [cstarMatrix_mul_smul_rect, cstarMatrix_smul_mul_rect]

/-- Compression by a rectangular `CStarMatrix` commutes with real scalar
multiplication. -/
theorem cstarMatrix_compression_real_smul
    {α β : Type*} [Fintype α] [Fintype β]
    (V : CStarMatrix α β ℂ) (a : ℝ) (M : CStarMatrix α α ℂ) :
    CStarMatrix.conjTranspose V * (a • M) * V =
      a • (CStarMatrix.conjTranspose V * M * V) := by
  change CStarMatrix.conjTranspose V * ((a : ℂ) • M) * V =
    (a : ℂ) • (CStarMatrix.conjTranspose V * M * V)
  exact cstarMatrix_compression_smul V (a : ℂ) M

/-- Compression by a fixed rectangular `CStarMatrix` as a continuous complex
linear map. -/
noncomputable def cstarMatrixCompressionCLM
    {α β : Type*} [Fintype α] [Fintype β]
    (V : CStarMatrix α β ℂ) :
    CStarMatrix α α ℂ →L[ℂ] CStarMatrix β β ℂ :=
  LinearMap.toContinuousLinearMap
    { toFun := fun M => CStarMatrix.conjTranspose V * M * V
      map_add' := by
        intro M N
        exact cstarMatrix_compression_add V M N
      map_smul' := by
        intro c M
        exact cstarMatrix_compression_smul V c M }

@[simp]
theorem cstarMatrixCompressionCLM_apply
    {α β : Type*} [Fintype α] [Fintype β]
    (V : CStarMatrix α β ℂ) (M : CStarMatrix α α ℂ) :
    cstarMatrixCompressionCLM V M =
      CStarMatrix.conjTranspose V * M * V := rfl

/-- Compressing the identity by an isometry gives the identity. -/
theorem cstarMatrix_compression_one_of_conjTranspose_mul_self_eq_one
    {α β : Type*} [Fintype α] [Fintype β] [DecidableEq α] [DecidableEq β]
    (V : CStarMatrix α β ℂ)
    (hVV : CStarMatrix.conjTranspose V * V = (1 : CStarMatrix β β ℂ)) :
    CStarMatrix.conjTranspose V * (1 : CStarMatrix α α ℂ) * V =
      (1 : CStarMatrix β β ℂ) := by
  calc
    CStarMatrix.conjTranspose V * (1 : CStarMatrix α α ℂ) * V =
        CStarMatrix.conjTranspose V * V := by
          rw [cstarMatrix_mul_one_rect]
    _ = 1 := hVV

/-- If two square unit C⋆-matrices intertwine a rectangular matrix, then their
inverses intertwine the same rectangular matrix in the opposite direction.

This is a rectangular algebra adapter used by shifted-resolvent corner
arguments: from \(U V = V W\) we get \(U^{-1} V = V W^{-1}\). -/
theorem cstarMatrix_units_inv_mul_rect_eq_mul_units_inv_of_mul_eq
    {α β : Type*} [Fintype α] [DecidableEq α] [Fintype β] [DecidableEq β]
    (U : (CStarMatrix α α ℂ)ˣ) (W : (CStarMatrix β β ℂ)ˣ)
    (V : CStarMatrix α β ℂ)
    (hUV : (U : CStarMatrix α α ℂ) * V =
      V * (W : CStarMatrix β β ℂ)) :
    (↑U⁻¹ : CStarMatrix α α ℂ) * V =
      V * (↑W⁻¹ : CStarMatrix β β ℂ) := by
  have hleft :
      (↑U⁻¹ : CStarMatrix α α ℂ) * ((U : CStarMatrix α α ℂ) * V) =
        V := by
    have hUinv :
        (↑U⁻¹ : CStarMatrix α α ℂ) * (U : CStarMatrix α α ℂ) = 1 :=
      Units.inv_mul U
    calc
      (↑U⁻¹ : CStarMatrix α α ℂ) * ((U : CStarMatrix α α ℂ) * V) =
          ((↑U⁻¹ : CStarMatrix α α ℂ) * (U : CStarMatrix α α ℂ)) * V := by
            rw [← cstarMatrix_mul_assoc_rect]
      _ = (1 : CStarMatrix α α ℂ) * V := by
            rw [hUinv]
      _ = V := cstarMatrix_one_mul_rect V
  have hmid :
      V = ((↑U⁻¹ : CStarMatrix α α ℂ) * V) *
          (W : CStarMatrix β β ℂ) := by
    calc
      V = (↑U⁻¹ : CStarMatrix α α ℂ) *
          ((U : CStarMatrix α α ℂ) * V) := hleft.symm
      _ = (↑U⁻¹ : CStarMatrix α α ℂ) *
          (V * (W : CStarMatrix β β ℂ)) := by
            rw [hUV]
      _ = ((↑U⁻¹ : CStarMatrix α α ℂ) * V) *
          (W : CStarMatrix β β ℂ) := by
            rw [← cstarMatrix_mul_assoc_rect]
  have hWinv :
      (W : CStarMatrix β β ℂ) * (↑W⁻¹ : CStarMatrix β β ℂ) = 1 :=
    Units.mul_inv W
  calc
    (↑U⁻¹ : CStarMatrix α α ℂ) * V =
        ((↑U⁻¹ : CStarMatrix α α ℂ) * V) *
          (1 : CStarMatrix β β ℂ) := by
            rw [cstarMatrix_mul_one_rect]
    _ = ((↑U⁻¹ : CStarMatrix α α ℂ) * V) *
          ((W : CStarMatrix β β ℂ) *
            (↑W⁻¹ : CStarMatrix β β ℂ)) := by
            rw [hWinv]
    _ = (((↑U⁻¹ : CStarMatrix α α ℂ) * V) *
          (W : CStarMatrix β β ℂ)) *
            (↑W⁻¹ : CStarMatrix β β ℂ) := by
            exact (cstarMatrix_mul_assoc_rect
              ((↑U⁻¹ : CStarMatrix α α ℂ) * V)
              (W : CStarMatrix β β ℂ)
              (↑W⁻¹ : CStarMatrix β β ℂ)).symm
    _ = V * (↑W⁻¹ : CStarMatrix β β ℂ) := by
            rw [← hmid]

/-- Block diagonal C⋆-matrix over the sum index. -/
def cstarMatrixBlockDiagonal {ι : Type*}
    (A B : CStarMatrix ι ι ℂ) : CStarMatrix (ι ⊕ ι) (ι ⊕ ι) ℂ :=
  CStarMatrix.ofMatrix
    (Matrix.fromBlocks (CStarMatrix.ofMatrix.symm A) 0 0
      (CStarMatrix.ofMatrix.symm B))

@[simp]
theorem cstarMatrixBlockDiagonal_inl_inl {ι : Type*}
    (A B : CStarMatrix ι ι ℂ) (i j : ι) :
    cstarMatrixBlockDiagonal A B (Sum.inl i) (Sum.inl j) = A i j := by
  rfl

@[simp]
theorem cstarMatrixBlockDiagonal_inl_inr {ι : Type*}
    (A B : CStarMatrix ι ι ℂ) (i j : ι) :
    cstarMatrixBlockDiagonal A B (Sum.inl i) (Sum.inr j) = 0 := by
  rfl

@[simp]
theorem cstarMatrixBlockDiagonal_inr_inl {ι : Type*}
    (A B : CStarMatrix ι ι ℂ) (i j : ι) :
    cstarMatrixBlockDiagonal A B (Sum.inr i) (Sum.inl j) = 0 := by
  rfl

@[simp]
theorem cstarMatrixBlockDiagonal_inr_inr {ι : Type*}
    (A B : CStarMatrix ι ι ℂ) (i j : ι) :
    cstarMatrixBlockDiagonal A B (Sum.inr i) (Sum.inr j) = B i j := by
  rfl

@[simp]
theorem cstarMatrixBlockDiagonal_zero_zero {ι : Type*} :
    cstarMatrixBlockDiagonal
        (0 : CStarMatrix ι ι ℂ) (0 : CStarMatrix ι ι ℂ) = 0 := by
  ext r c
  cases r <;> cases c <;> simp

@[simp]
theorem cstarMatrixBlockDiagonal_one_one {ι : Type*} [DecidableEq ι] :
    cstarMatrixBlockDiagonal
        (1 : CStarMatrix ι ι ℂ) (1 : CStarMatrix ι ι ℂ) = 1 := by
  ext r c
  cases r <;> cases c <;> simp [CStarMatrix.one_apply]

theorem cstarMatrixBlockDiagonal_add {ι : Type*}
    (A B C D : CStarMatrix ι ι ℂ) :
    cstarMatrixBlockDiagonal (A + C) (B + D) =
      cstarMatrixBlockDiagonal A B + cstarMatrixBlockDiagonal C D := by
  ext r c
  cases r <;> cases c <;> simp

theorem cstarMatrixBlockDiagonal_neg {ι : Type*}
    (A B : CStarMatrix ι ι ℂ) :
    cstarMatrixBlockDiagonal (-A) (-B) =
      -cstarMatrixBlockDiagonal A B := by
  ext r c
  cases r <;> cases c <;> simp

theorem cstarMatrixBlockDiagonal_sub {ι : Type*}
    (A B C D : CStarMatrix ι ι ℂ) :
    cstarMatrixBlockDiagonal (A - C) (B - D) =
      cstarMatrixBlockDiagonal A B - cstarMatrixBlockDiagonal C D := by
  ext r c
  cases r <;> cases c <;> simp

theorem cstarMatrixBlockDiagonal_star {ι : Type*}
    (A B : CStarMatrix ι ι ℂ) :
    star (cstarMatrixBlockDiagonal A B) =
      cstarMatrixBlockDiagonal (star A) (star B) := by
  ext r c
  cases r <;> cases c <;> simp [CStarMatrix.star_apply]

theorem cstarMatrixBlockDiagonal_isSelfAdjoint {ι : Type*}
    {A B : CStarMatrix ι ι ℂ}
    (hA : IsSelfAdjoint A) (hB : IsSelfAdjoint B) :
    IsSelfAdjoint (cstarMatrixBlockDiagonal A B) := by
  rw [isSelfAdjoint_iff] at hA hB ⊢
  rw [cstarMatrixBlockDiagonal_star, hA, hB]

theorem cstarMatrixBlockDiagonal_mul {ι : Type*} [Fintype ι]
    (A B C D : CStarMatrix ι ι ℂ) :
    cstarMatrixBlockDiagonal A B * cstarMatrixBlockDiagonal C D =
      cstarMatrixBlockDiagonal (A * C) (B * D) := by
  ext r c
  cases r <;> cases c <;>
    simp [CStarMatrix.mul_apply, Fintype.sum_sum_type]

theorem cstarMatrixBlockDiagonal_isUnit {ι : Type*} [Fintype ι] [DecidableEq ι]
    {A B : CStarMatrix ι ι ℂ} (hA : IsUnit A) (hB : IsUnit B) :
    IsUnit (cstarMatrixBlockDiagonal A B) := by
  rw [isUnit_iff_exists] at hA hB ⊢
  rcases hA with ⟨Ainv, hA1, hA2⟩
  rcases hB with ⟨Binv, hB1, hB2⟩
  refine ⟨cstarMatrixBlockDiagonal Ainv Binv, ?_, ?_⟩
  · calc
      cstarMatrixBlockDiagonal A B * cstarMatrixBlockDiagonal Ainv Binv =
          cstarMatrixBlockDiagonal (A * Ainv) (B * Binv) :=
        cstarMatrixBlockDiagonal_mul A B Ainv Binv
      _ = cstarMatrixBlockDiagonal 1 1 := by
        ext r c
        cases r with
        | inl i =>
            cases c with
            | inl j => simpa using congr_fun (congr_fun hA1 i) j
            | inr j => simp
        | inr i =>
            cases c with
            | inl j => simp
            | inr j => simpa using congr_fun (congr_fun hB1 i) j
      _ = 1 := cstarMatrixBlockDiagonal_one_one
  · calc
      cstarMatrixBlockDiagonal Ainv Binv * cstarMatrixBlockDiagonal A B =
          cstarMatrixBlockDiagonal (Ainv * A) (Binv * B) :=
        cstarMatrixBlockDiagonal_mul Ainv Binv A B
      _ = cstarMatrixBlockDiagonal 1 1 := by
        ext r c
        cases r with
        | inl i =>
            cases c with
            | inl j => simpa using congr_fun (congr_fun hA2 i) j
            | inr j => simp
        | inr i =>
            cases c with
            | inl j => simp
            | inr j => simpa using congr_fun (congr_fun hB2 i) j
      _ = 1 := cstarMatrixBlockDiagonal_one_one

theorem cstarMatrixBlockDiagonal_left_nonneg {ι : Type*} [Fintype ι]
    {A : CStarMatrix ι ι ℂ} (hA : 0 ≤ A) :
    0 ≤ cstarMatrixBlockDiagonal A (0 : CStarMatrix ι ι ℂ) := by
  rw [StarOrderedRing.nonneg_iff] at hA ⊢
  refine AddSubmonoid.closure_induction
    (s := Set.range fun S : CStarMatrix ι ι ℂ => star S * S)
    (motive := fun X _ =>
      cstarMatrixBlockDiagonal X (0 : CStarMatrix ι ι ℂ) ∈
        AddSubmonoid.closure
          (Set.range fun S : CStarMatrix (ι ⊕ ι) (ι ⊕ ι) ℂ => star S * S))
    ?mem ?zero ?add hA
  · intro X hX
    rcases hX with ⟨S, rfl⟩
    apply AddSubmonoid.subset_closure
    refine ⟨cstarMatrixBlockDiagonal S (0 : CStarMatrix ι ι ℂ), ?_⟩
    simp [cstarMatrixBlockDiagonal_star, cstarMatrixBlockDiagonal_mul]
  · simp
  · intro X Y _ _ hX hY
    have hEq :
        cstarMatrixBlockDiagonal (X + Y) (0 : CStarMatrix ι ι ℂ) =
          cstarMatrixBlockDiagonal X (0 : CStarMatrix ι ι ℂ) +
            cstarMatrixBlockDiagonal Y (0 : CStarMatrix ι ι ℂ) := by
      simpa using
        (cstarMatrixBlockDiagonal_add X (0 : CStarMatrix ι ι ℂ) Y
          (0 : CStarMatrix ι ι ℂ))
    rw [hEq]
    exact AddSubmonoid.add_mem
      (AddSubmonoid.closure
        (Set.range fun S : CStarMatrix (ι ⊕ ι) (ι ⊕ ι) ℂ => star S * S))
      hX hY

theorem cstarMatrixBlockDiagonal_right_nonneg {ι : Type*} [Fintype ι]
    {B : CStarMatrix ι ι ℂ} (hB : 0 ≤ B) :
    0 ≤ cstarMatrixBlockDiagonal (0 : CStarMatrix ι ι ℂ) B := by
  rw [StarOrderedRing.nonneg_iff] at hB ⊢
  refine AddSubmonoid.closure_induction
    (s := Set.range fun S : CStarMatrix ι ι ℂ => star S * S)
    (motive := fun X _ =>
      cstarMatrixBlockDiagonal (0 : CStarMatrix ι ι ℂ) X ∈
        AddSubmonoid.closure
          (Set.range fun S : CStarMatrix (ι ⊕ ι) (ι ⊕ ι) ℂ => star S * S))
    ?mem ?zero ?add hB
  · intro X hX
    rcases hX with ⟨S, rfl⟩
    apply AddSubmonoid.subset_closure
    refine ⟨cstarMatrixBlockDiagonal (0 : CStarMatrix ι ι ℂ) S, ?_⟩
    simp [cstarMatrixBlockDiagonal_star, cstarMatrixBlockDiagonal_mul]
  · simp
  · intro X Y _ _ hX hY
    have hEq :
        cstarMatrixBlockDiagonal (0 : CStarMatrix ι ι ℂ) (X + Y) =
          cstarMatrixBlockDiagonal (0 : CStarMatrix ι ι ℂ) X +
            cstarMatrixBlockDiagonal (0 : CStarMatrix ι ι ℂ) Y := by
      simpa using
        (cstarMatrixBlockDiagonal_add (0 : CStarMatrix ι ι ℂ) X
          (0 : CStarMatrix ι ι ℂ) Y)
    rw [hEq]
    exact AddSubmonoid.add_mem
      (AddSubmonoid.closure
        (Set.range fun S : CStarMatrix (ι ⊕ ι) (ι ⊕ ι) ℂ => star S * S))
      hX hY

theorem cstarMatrixBlockDiagonal_nonneg {ι : Type*} [Fintype ι]
    {A B : CStarMatrix ι ι ℂ} (hA : 0 ≤ A) (hB : 0 ≤ B) :
    0 ≤ cstarMatrixBlockDiagonal A B := by
  have hsum :
      0 ≤ cstarMatrixBlockDiagonal A (0 : CStarMatrix ι ι ℂ) +
        cstarMatrixBlockDiagonal (0 : CStarMatrix ι ι ℂ) B :=
    add_nonneg (cstarMatrixBlockDiagonal_left_nonneg hA)
      (cstarMatrixBlockDiagonal_right_nonneg hB)
  have hEq :
      cstarMatrixBlockDiagonal A B =
        cstarMatrixBlockDiagonal A (0 : CStarMatrix ι ι ℂ) +
          cstarMatrixBlockDiagonal (0 : CStarMatrix ι ι ℂ) B := by
    simpa using
      (cstarMatrixBlockDiagonal_add A (0 : CStarMatrix ι ι ℂ)
        (0 : CStarMatrix ι ι ℂ) B)
  rwa [hEq]

theorem cstarMatrixBlockDiagonal_isStrictlyPositive
    {ι : Type*} [Fintype ι] [DecidableEq ι]
    {A B : CStarMatrix ι ι ℂ}
    (hA : IsStrictlyPositive A) (hB : IsStrictlyPositive B) :
    IsStrictlyPositive (cstarMatrixBlockDiagonal A B) :=
  (cstarMatrixBlockDiagonal_isUnit hA.isUnit hB.isUnit).isStrictlyPositive
    (cstarMatrixBlockDiagonal_nonneg hA.nonneg hB.nonneg)

/-- Block diagonal embedding as a real star-algebra homomorphism from a pair of
finite C⋆-matrices into the doubled-index finite C⋆-matrix algebra. -/
noncomputable def cstarMatrixBlockDiagonalStarAlgHom
    (ι : Type*) [Fintype ι] [DecidableEq ι] :
    (CStarMatrix ι ι ℂ × CStarMatrix ι ι ℂ) →⋆ₐ[ℝ]
      CStarMatrix (ι ⊕ ι) (ι ⊕ ι) ℂ where
  toFun p := cstarMatrixBlockDiagonal p.1 p.2
  map_zero' := cstarMatrixBlockDiagonal_zero_zero
  map_one' := cstarMatrixBlockDiagonal_one_one
  map_add' p q := cstarMatrixBlockDiagonal_add p.1 p.2 q.1 q.2
  map_mul' p q := by
    simpa using (cstarMatrixBlockDiagonal_mul p.1 p.2 q.1 q.2).symm
  commutes' r := by
    ext row col
    cases row <;> cases col <;>
      simp [Algebra.algebraMap_eq_smul_one, CStarMatrix.one_apply]
  map_star' p := (cstarMatrixBlockDiagonal_star p.1 p.2).symm

@[simp]
theorem cstarMatrixBlockDiagonalStarAlgHom_apply
    {ι : Type*} [Fintype ι] [DecidableEq ι]
    (A B : CStarMatrix ι ι ℂ) :
    cstarMatrixBlockDiagonalStarAlgHom ι (A, B) =
      cstarMatrixBlockDiagonal A B := rfl

/-- The block diagonal star-algebra homomorphism is continuous. -/
theorem cstarMatrixBlockDiagonalStarAlgHom_continuous
    {ι : Type*} [Fintype ι] [DecidableEq ι] :
    Continuous
      (cstarMatrixBlockDiagonalStarAlgHom ι :
        CStarMatrix ι ι ℂ × CStarMatrix ι ι ℂ →
          CStarMatrix (ι ⊕ ι) (ι ⊕ ι) ℂ) := by
  have hmat :
      Continuous
        (fun p : CStarMatrix ι ι ℂ × CStarMatrix ι ι ℂ =>
          (Matrix.fromBlocks (CStarMatrix.ofMatrix.symm p.1) 0 0
            (CStarMatrix.ofMatrix.symm p.2) :
            Matrix (ι ⊕ ι) (ι ⊕ ι) ℂ)) := by
    apply continuous_pi
    intro row
    apply continuous_pi
    intro col
    cases row with
    | inl i =>
        cases col with
        | inl j =>
            simpa using
              ((continuous_apply j).comp
                ((continuous_apply i).comp continuous_fst))
        | inr j => exact continuous_const
    | inr i =>
        cases col with
        | inl j => exact continuous_const
        | inr j =>
            simpa using
              ((continuous_apply j).comp
                ((continuous_apply i).comp continuous_snd))
  simpa [cstarMatrixBlockDiagonalStarAlgHom, cstarMatrixBlockDiagonal] using
    ((CStarMatrix.ofMatrixL
      (m := ι ⊕ ι) (n := ι ⊕ ι) (A := ℂ)).continuous.comp hmat)

/-- Vertical pairing of two square C⋆-matrices, the block column `[A;B]`. -/
def cstarMatrixColumnPair {ι : Type*}
    (A B : CStarMatrix ι ι ℂ) : CStarMatrix (ι ⊕ ι) ι ℂ :=
  CStarMatrix.ofMatrix fun r j =>
    match r with
    | Sum.inl i => A i j
    | Sum.inr i => B i j

@[simp]
theorem cstarMatrixColumnPair_inl {ι : Type*}
    (A B : CStarMatrix ι ι ℂ) (i j : ι) :
    cstarMatrixColumnPair A B (Sum.inl i) j = A i j := by
  rfl

@[simp]
theorem cstarMatrixColumnPair_inr {ι : Type*}
    (A B : CStarMatrix ι ι ℂ) (i j : ι) :
    cstarMatrixColumnPair A B (Sum.inr i) j = B i j := by
  rfl

/-- Multiplying two block columns gives the sum of the two block products. -/
theorem cstarMatrixColumnPair_conjTranspose_mul_columnPair
    {ι : Type*} [Fintype ι]
    (A B C D : CStarMatrix ι ι ℂ) :
    CStarMatrix.conjTranspose (cstarMatrixColumnPair A B) *
        cstarMatrixColumnPair C D =
      star A * C + star B * D := by
  ext i j
  simp [CStarMatrix.mul_apply, CStarMatrix.star_apply,
    Fintype.sum_sum_type]

/-- The normalization of the block column `[A;B]` is `AᴴA + BᴴB`. -/
theorem cstarMatrixColumnPair_conjTranspose_mul_self
    {ι : Type*} [Fintype ι]
    (A B : CStarMatrix ι ι ℂ) :
    CStarMatrix.conjTranspose (cstarMatrixColumnPair A B) *
        cstarMatrixColumnPair A B =
      star A * A + star B * B := by
  simpa using cstarMatrixColumnPair_conjTranspose_mul_columnPair A B A B

/-- Multiplying `diag(T₁,T₂)` by `[A;B]` acts blockwise. -/
theorem cstarMatrixBlockDiagonal_mul_columnPair
    {ι : Type*} [Fintype ι]
    (T1 T2 A B : CStarMatrix ι ι ℂ) :
    cstarMatrixBlockDiagonal T1 T2 * cstarMatrixColumnPair A B =
      cstarMatrixColumnPair (T1 * A) (T2 * B) := by
  ext r j
  cases r with
  | inl i => simp [CStarMatrix.mul_apply, Fintype.sum_sum_type]
  | inr i => simp [CStarMatrix.mul_apply, Fintype.sum_sum_type]

/-- Compression of a block diagonal matrix by the block column `[A;B]`. -/
theorem cstarMatrixColumnPair_conjTranspose_mul_blockDiagonal_mul_columnPair
    {ι : Type*} [Fintype ι]
    (A B T1 T2 : CStarMatrix ι ι ℂ) :
    CStarMatrix.conjTranspose (cstarMatrixColumnPair A B) *
        cstarMatrixBlockDiagonal T1 T2 * cstarMatrixColumnPair A B =
      star A * T1 * A + star B * T2 * B := by
  ext i j
  simp [CStarMatrix.mul_apply, CStarMatrix.star_apply,
    Fintype.sum_sum_type, Finset.sum_mul]

/-- If `AᴴA + BᴴB = I`, then the block column `[A;B]` is an isometry. -/
theorem cstarMatrixColumnPair_conjTranspose_mul_self_eq_one_of_sum
    {ι : Type*} [Fintype ι] [DecidableEq ι]
    {A B : CStarMatrix ι ι ℂ}
    (hAB : star A * A + star B * B = 1) :
    CStarMatrix.conjTranspose (cstarMatrixColumnPair A B) *
      cstarMatrixColumnPair A B = 1 := by
  rw [cstarMatrixColumnPair_conjTranspose_mul_self, hAB]

/-- The range projection `VVᴴ` of the block column `V = [A;B]`. -/
noncomputable def cstarMatrixColumnPairRangeProjection
    {ι : Type*} [Fintype ι] [DecidableEq ι]
    (A B : CStarMatrix ι ι ℂ) : CStarMatrix (ι ⊕ ι) (ι ⊕ ι) ℂ :=
  cstarMatrixColumnPair A B *
    CStarMatrix.conjTranspose (cstarMatrixColumnPair A B)

/-- The range projection `VVᴴ` is self-adjoint. -/
theorem cstarMatrixColumnPairRangeProjection_isSelfAdjoint
    {ι : Type*} [Fintype ι] [DecidableEq ι]
    (A B : CStarMatrix ι ι ℂ) :
    IsSelfAdjoint (cstarMatrixColumnPairRangeProjection A B) := by
  rw [isSelfAdjoint_iff]
  ext r c
  simp [cstarMatrixColumnPairRangeProjection, CStarMatrix.mul_apply,
    CStarMatrix.star_apply, CStarMatrix.conjTranspose_apply, mul_comm]

/-- If `VᴴV = I`, then the range matrix `VVᴴ` is idempotent. -/
theorem cstarMatrixColumnPairRangeProjection_mul_self_of_sum
    {ι : Type*} [Fintype ι] [DecidableEq ι]
    {A B : CStarMatrix ι ι ℂ}
    (hAB : star A * A + star B * B = 1) :
    cstarMatrixColumnPairRangeProjection A B *
        cstarMatrixColumnPairRangeProjection A B =
      cstarMatrixColumnPairRangeProjection A B := by
  let V := cstarMatrixColumnPair A B
  have hV : CStarMatrix.conjTranspose V * V = 1 := by
    dsimp [V]
    exact cstarMatrixColumnPair_conjTranspose_mul_self_eq_one_of_sum hAB
  calc
    cstarMatrixColumnPairRangeProjection A B *
        cstarMatrixColumnPairRangeProjection A B =
        (V * CStarMatrix.conjTranspose V) *
          (V * CStarMatrix.conjTranspose V) := rfl
    _ = V * (CStarMatrix.conjTranspose V * V) *
          CStarMatrix.conjTranspose V := by
      rw [cstarMatrix_mul_assoc_rect V (CStarMatrix.conjTranspose V)
        (V * CStarMatrix.conjTranspose V)]
      rw [← cstarMatrix_mul_assoc_rect (CStarMatrix.conjTranspose V) V
        (CStarMatrix.conjTranspose V)]
      rw [← cstarMatrix_mul_assoc_rect V
        (CStarMatrix.conjTranspose V * V) (CStarMatrix.conjTranspose V)]
    _ = V * CStarMatrix.conjTranspose V := by
      rw [hV]
      rw [cstarMatrix_mul_one_rect V]
    _ = cstarMatrixColumnPairRangeProjection A B := rfl

/-- If `VᴴV = I`, then the range projection absorbs the block column:
`(VVᴴ)V = V`. -/
theorem cstarMatrixColumnPairRangeProjection_mul_columnPair_of_sum
    {ι : Type*} [Fintype ι] [DecidableEq ι]
    {A B : CStarMatrix ι ι ℂ}
    (hAB : star A * A + star B * B = 1) :
    cstarMatrixColumnPairRangeProjection A B *
        cstarMatrixColumnPair A B =
      cstarMatrixColumnPair A B := by
  let V := cstarMatrixColumnPair A B
  have hV : CStarMatrix.conjTranspose V * V = 1 := by
    dsimp [V]
    exact cstarMatrixColumnPair_conjTranspose_mul_self_eq_one_of_sum hAB
  calc
    cstarMatrixColumnPairRangeProjection A B * cstarMatrixColumnPair A B =
        (V * CStarMatrix.conjTranspose V) * V := rfl
    _ = V * (CStarMatrix.conjTranspose V * V) := by
      rw [cstarMatrix_mul_assoc_rect V (CStarMatrix.conjTranspose V) V]
    _ = V := by
      rw [hV]
      exact cstarMatrix_mul_one_rect V

/-- If `VᴴV = I`, then the range projection absorbs the adjoint block column:
`Vᴴ(VVᴴ) = Vᴴ`. -/
theorem cstarMatrixColumnPair_conjTranspose_mul_rangeProjection_of_sum
    {ι : Type*} [Fintype ι] [DecidableEq ι]
    {A B : CStarMatrix ι ι ℂ}
    (hAB : star A * A + star B * B = 1) :
    CStarMatrix.conjTranspose (cstarMatrixColumnPair A B) *
        cstarMatrixColumnPairRangeProjection A B =
      CStarMatrix.conjTranspose (cstarMatrixColumnPair A B) := by
  let V := cstarMatrixColumnPair A B
  have hV : CStarMatrix.conjTranspose V * V = 1 := by
    dsimp [V]
    exact cstarMatrixColumnPair_conjTranspose_mul_self_eq_one_of_sum hAB
  calc
    CStarMatrix.conjTranspose (cstarMatrixColumnPair A B) *
        cstarMatrixColumnPairRangeProjection A B =
        CStarMatrix.conjTranspose V * (V * CStarMatrix.conjTranspose V) := rfl
    _ = (CStarMatrix.conjTranspose V * V) *
          CStarMatrix.conjTranspose V := by
      rw [← cstarMatrix_mul_assoc_rect (CStarMatrix.conjTranspose V) V
        (CStarMatrix.conjTranspose V)]
    _ = CStarMatrix.conjTranspose V := by
      rw [hV]
      exact cstarMatrix_one_mul_rect (CStarMatrix.conjTranspose V)

/-- The reflection `2P - I` associated to a square C⋆-matrix `P`.  For an
idempotent self-adjoint `P`, this is the usual symmetry across the range of
`P`; it is the algebraic reflection used in block pinching arguments. -/
noncomputable def cstarMatrixProjectionReflection
    {ι : Type*} [DecidableEq ι] (P : CStarMatrix ι ι ℂ) :
    CStarMatrix ι ι ℂ :=
  (2 : ℂ) • P - 1

/-- If `P` is self-adjoint, then its reflection `2P - I` is self-adjoint. -/
theorem cstarMatrixProjectionReflection_isSelfAdjoint_of_isSelfAdjoint
    {ι : Type*} [Fintype ι] [DecidableEq ι]
    (P : CStarMatrix ι ι ℂ) (hP : IsSelfAdjoint P) :
    IsSelfAdjoint (cstarMatrixProjectionReflection P) := by
  rw [isSelfAdjoint_iff] at hP ⊢
  ext i j
  have hPij := congrArg (fun M : CStarMatrix ι ι ℂ => M i j) hP
  simp [cstarMatrixProjectionReflection, CStarMatrix.star_apply] at hPij ⊢
  rw [hPij]
  by_cases hij : i = j
  · subst hij
    simp
  · simp [hij, Ne.symm hij]

/-- If `P` is idempotent, then the reflection `2P - I` squares to the
identity. -/
theorem cstarMatrixProjectionReflection_mul_self_of_idempotent
    {ι : Type*} [Fintype ι] [DecidableEq ι]
    (P : CStarMatrix ι ι ℂ) (hP : P * P = P) :
    cstarMatrixProjectionReflection P * cstarMatrixProjectionReflection P =
      (1 : CStarMatrix ι ι ℂ) := by
  ext i j
  have hPij := congrArg (fun M : CStarMatrix ι ι ℂ => M i j) hP
  simp [cstarMatrixProjectionReflection, CStarMatrix.mul_apply,
    CStarMatrix.one_apply] at hPij ⊢
  simp [mul_sub, sub_mul, Finset.sum_sub_distrib] at hPij ⊢
  have hdouble :
      (∑ x, 2 * P i x * (2 * P x j)) =
        4 * ∑ x, P i x * P x j := by
    calc
      (∑ x, 2 * P i x * (2 * P x j))
          = ∑ x, 4 * (P i x * P x j) := by
            apply Finset.sum_congr rfl
            intro x _
            ring
      _ = 4 * ∑ x, P i x * P x j := by
            rw [Finset.mul_sum]
  rw [hdouble, hPij]
  by_cases hij : i = j
  · subst hij
    ring
  · simp [hij]
    ring

/-- If `P` is idempotent, then the reflection `2P - I` is a unit with itself
as inverse. -/
theorem cstarMatrixProjectionReflection_isUnit_of_idempotent
    {ι : Type*} [Fintype ι] [DecidableEq ι]
    (P : CStarMatrix ι ι ℂ) (hP : P * P = P) :
    IsUnit (cstarMatrixProjectionReflection P) := by
  have hsq := cstarMatrixProjectionReflection_mul_self_of_idempotent P hP
  refine isUnit_iff_exists.mpr
    ⟨cstarMatrixProjectionReflection P, ?_⟩
  exact ⟨hsq, hsq⟩

/-- If `P` is self-adjoint and idempotent, then the reflection `2P - I` is
unitary in the star-monoid sense. -/
theorem cstarMatrixProjectionReflection_mem_unitary_of_isSelfAdjoint_of_idempotent
    {ι : Type*} [Fintype ι] [DecidableEq ι]
    (P : CStarMatrix ι ι ℂ) (hself : IsSelfAdjoint P) (hid : P * P = P) :
    cstarMatrixProjectionReflection P ∈
      unitary (CStarMatrix ι ι ℂ) := by
  have hRself :
      IsSelfAdjoint (cstarMatrixProjectionReflection P) :=
    cstarMatrixProjectionReflection_isSelfAdjoint_of_isSelfAdjoint P hself
  have hstar :
      star (cstarMatrixProjectionReflection P) =
        cstarMatrixProjectionReflection P := by
    simpa [isSelfAdjoint_iff] using hRself
  have hsq := cstarMatrixProjectionReflection_mul_self_of_idempotent P hid
  rw [Unitary.mem_iff]
  constructor
  · calc
      star (cstarMatrixProjectionReflection P) *
          cstarMatrixProjectionReflection P =
          cstarMatrixProjectionReflection P *
            cstarMatrixProjectionReflection P := by
            rw [hstar]
      _ = 1 := hsq
  · calc
      cstarMatrixProjectionReflection P *
          star (cstarMatrixProjectionReflection P) =
          cstarMatrixProjectionReflection P *
            cstarMatrixProjectionReflection P := by
            rw [hstar]
      _ = 1 := hsq

/-- If `P` fixes a rectangular matrix `V`, then the reflection `2P - I`
also fixes `V`. -/
theorem cstarMatrixProjectionReflection_mul_of_mul_eq_self
    {α β : Type*} [Fintype α] [DecidableEq α] [DecidableEq β]
    (P : CStarMatrix α α ℂ) (V : CStarMatrix α β ℂ)
    (hPV : P * V = V) :
    cstarMatrixProjectionReflection P * V = V := by
  ext i j
  have hPVij := congrArg (fun M : CStarMatrix α β ℂ => M i j) hPV
  simp [cstarMatrixProjectionReflection, CStarMatrix.mul_apply,
    CStarMatrix.one_apply, sub_mul, Finset.sum_sub_distrib] at hPVij ⊢
  have hdouble :
      (∑ x, 2 * P i x * V x j) =
        2 * ∑ x, P i x * V x j := by
    calc
      (∑ x, 2 * P i x * V x j)
          = ∑ x, 2 * (P i x * V x j) := by
            apply Finset.sum_congr rfl
            intro x _
            ring
      _ = 2 * ∑ x, P i x * V x j := by
            rw [Finset.mul_sum]
  rw [hdouble, hPVij]
  ring

/-- If a rectangular matrix `W` is fixed by right multiplication by `P`, then
it is also fixed by right multiplication by the reflection `2P - I`. -/
theorem cstarMatrix_mul_projectionReflection_of_mul_eq_self
    {α β : Type*} [Fintype β] [DecidableEq α] [DecidableEq β]
    (W : CStarMatrix α β ℂ) (P : CStarMatrix β β ℂ)
    (hWP : W * P = W) :
    W * cstarMatrixProjectionReflection P = W := by
  ext i j
  have hWPij := congrArg (fun M : CStarMatrix α β ℂ => M i j) hWP
  simp [cstarMatrixProjectionReflection, CStarMatrix.mul_apply,
    CStarMatrix.one_apply, mul_sub, Finset.sum_sub_distrib] at hWPij ⊢
  have hdouble :
      (∑ x, W i x * (2 * P x j)) =
        2 * ∑ x, W i x * P x j := by
    calc
      (∑ x, W i x * (2 * P x j))
          = ∑ x, 2 * (W i x * P x j) := by
            apply Finset.sum_congr rfl
            intro x _
            ring
      _ = 2 * ∑ x, W i x * P x j := by
            rw [Finset.mul_sum]
  rw [hdouble, hWPij]
  ring

/-- If a square matrix `R` fixes the compression column on the left and the
compression row on the right, then replacing `D` by the reflection average
`(D + RDR)/2` does not change the compressed matrix. -/
theorem cstarMatrix_reflectionAverage_compression_of_fixed
    {α β : Type*} [Fintype α] [DecidableEq α] [DecidableEq β]
    (W : CStarMatrix β α ℂ) (R D : CStarMatrix α α ℂ)
    (V : CStarMatrix α β ℂ)
    (hWR : W * R = W) (hRV : R * V = V) :
    W * ((1 / 2 : ℂ) • (D + R * D * R)) * V =
      W * D * V := by
  have hRDR_compress :
      W * (R * D * R) * V = W * D * V := by
    calc
      W * (R * D * R) * V =
          W * ((R * D * R) * V) := by
            rw [cstarMatrix_mul_assoc_rect W (R * D * R) V]
      _ = W * ((R * D) * (R * V)) := by
            rw [cstarMatrix_mul_assoc_rect (R * D) R V]
      _ = W * ((R * D) * V) := by
            rw [hRV]
      _ = W * (R * (D * V)) := by
            rw [cstarMatrix_mul_assoc_rect R D V]
      _ = (W * R) * (D * V) := by
            rw [← cstarMatrix_mul_assoc_rect W R (D * V)]
      _ = W * (D * V) := by
            rw [hWR]
      _ = W * D * V := by
            rw [← cstarMatrix_mul_assoc_rect W D V]
  have hsum :
      W * (D + R * D * R) * V =
        W * D * V + W * D * V := by
    calc
      W * (D + R * D * R) * V =
          (W * D + W * (R * D * R)) * V := by
            rw [cstarMatrix_mul_add_rect W D (R * D * R)]
      _ = W * D * V + W * (R * D * R) * V := by
            rw [cstarMatrix_add_mul_rect (W * D) (W * (R * D * R)) V]
      _ = W * D * V + W * D * V := by
            rw [hRDR_compress]
  calc
    W * ((1 / 2 : ℂ) • (D + R * D * R)) * V =
        ((1 / 2 : ℂ) • (W * (D + R * D * R))) * V := by
          rw [cstarMatrix_mul_smul_rect (1 / 2 : ℂ) W (D + R * D * R)]
    _ = (1 / 2 : ℂ) • (W * (D + R * D * R) * V) := by
          rw [cstarMatrix_smul_mul_rect (1 / 2 : ℂ)
            (W * (D + R * D * R)) V]
    _ = (1 / 2 : ℂ) • (W * D * V + W * D * V) := by
          rw [hsum]
    _ = W * D * V := by
          ext i j
          simp
          ring

/-- The reflection average `(D + RDR)/2` is fixed by conjugation with `R`
whenever `R^2 = I`. -/
theorem cstarMatrix_reflectionAverage_conj_of_involutive
    {ι : Type*} [Fintype ι] [DecidableEq ι]
    (R D : CStarMatrix ι ι ℂ) (hR : R * R = 1) :
    R * ((1 / 2 : ℂ) • (D + R * D * R)) * R =
      (1 / 2 : ℂ) • (D + R * D * R) := by
  have hsecond :
      R * (R * D * R) * R = D := by
    calc
      R * (R * D * R) * R =
          R * ((R * D * R) * R) := by
            rw [cstarMatrix_mul_assoc_rect R (R * D * R) R]
      _ = R * ((R * D) * (R * R)) := by
            rw [cstarMatrix_mul_assoc_rect (R * D) R R]
      _ = R * ((R * D) * 1) := by
            rw [hR]
      _ = R * (R * D) := by
            rw [cstarMatrix_mul_one_rect (R * D)]
      _ = (R * R) * D := by
            rw [← cstarMatrix_mul_assoc_rect R R D]
      _ = 1 * D := by
            rw [hR]
      _ = D := by
            rw [cstarMatrix_one_mul_rect D]
  have hsum :
      R * (D + R * D * R) * R = R * D * R + D := by
    calc
      R * (D + R * D * R) * R =
          (R * D + R * (R * D * R)) * R := by
            rw [cstarMatrix_mul_add_rect R D (R * D * R)]
      _ = R * D * R + R * (R * D * R) * R := by
            rw [cstarMatrix_add_mul_rect (R * D) (R * (R * D * R)) R]
      _ = R * D * R + D := by
            rw [hsecond]
  calc
    R * ((1 / 2 : ℂ) • (D + R * D * R)) * R =
        ((1 / 2 : ℂ) • (R * (D + R * D * R))) * R := by
          rw [cstarMatrix_mul_smul_rect (1 / 2 : ℂ) R (D + R * D * R)]
    _ = (1 / 2 : ℂ) • (R * (D + R * D * R) * R) := by
          rw [cstarMatrix_smul_mul_rect (1 / 2 : ℂ)
            (R * (D + R * D * R)) R]
    _ = (1 / 2 : ℂ) • (R * D * R + D) := by
          rw [hsum]
    _ = (1 / 2 : ℂ) • (D + R * D * R) := by
          ext i j
          simp [add_comm]

/-- The reflection average `(D + RDR)/2` commutes with `R` whenever
`R^2 = I`. -/
theorem cstarMatrix_reflectionAverage_commute_of_involutive
    {ι : Type*} [Fintype ι] [DecidableEq ι]
    (R D : CStarMatrix ι ι ℂ) (hR : R * R = 1) :
    R * ((1 / 2 : ℂ) • (D + R * D * R)) =
      ((1 / 2 : ℂ) • (D + R * D * R)) * R := by
  let E : CStarMatrix ι ι ℂ := (1 / 2 : ℂ) • (D + R * D * R)
  have hconj : R * E * R = E := by
    dsimp [E]
    exact cstarMatrix_reflectionAverage_conj_of_involutive R D hR
  have hleft : (R * E * R) * R = R * E := by
    calc
      (R * E * R) * R = (R * E) * (R * R) := by
        rw [cstarMatrix_mul_assoc_rect (R * E) R R]
      _ = (R * E) * 1 := by
        rw [hR]
      _ = R * E := by
        rw [cstarMatrix_mul_one_rect (R * E)]
  have hmul := congrArg (fun X : CStarMatrix ι ι ℂ => X * R) hconj
  calc
    R * E = (R * E * R) * R := by
      rw [hleft]
    _ = E * R := hmul

/-- Commutation with the reflection `2P - I` implies commutation with the
projection `P`. -/
theorem cstarMatrix_commute_projection_of_commute_reflection
    {ι : Type*} [Fintype ι] [DecidableEq ι]
    (P E : CStarMatrix ι ι ℂ)
    (hRE :
      cstarMatrixProjectionReflection P * E =
        E * cstarMatrixProjectionReflection P) :
    P * E = E * P := by
  ext i j
  have hREij := congrArg (fun M : CStarMatrix ι ι ℂ => M i j) hRE
  simp [cstarMatrixProjectionReflection, CStarMatrix.mul_apply,
    CStarMatrix.one_apply, sub_mul, mul_sub, Finset.sum_sub_distrib] at hREij
  have hcancel := congrArg (fun z : ℂ => z + E i j) hREij
  ring_nf at hcancel
  have hsum_cancel :
      (∑ x, P i x * E x j * 2) =
        (∑ x, E i x * P x j * 2) := by
    have htmp :
        (∑ x, P i x * E x j * 2) + E i j =
          (∑ x, E i x * P x j * 2) + E i j := by
      calc
        (∑ x, P i x * E x j * 2) + E i j =
            E i j + ∑ x, E i x * P x j * 2 := hcancel
        _ = (∑ x, E i x * P x j * 2) + E i j := by
            rw [add_comm]
    exact add_right_cancel htmp
  have hcancel' : (2 : ℂ) * (P * E) i j = (2 : ℂ) * (E * P) i j := by
    simpa [CStarMatrix.mul_apply, Finset.mul_sum, mul_comm, mul_left_comm,
      mul_assoc] using hsum_cancel
  have htwo : (2 : ℂ) ≠ 0 := by norm_num
  exact mul_left_cancel₀ htwo hcancel'

/-- The range reflection `2VVᴴ - I` of the block column `V = [A;B]`. -/
noncomputable def cstarMatrixColumnPairRangeReflection
    {ι : Type*} [Fintype ι] [DecidableEq ι]
    (A B : CStarMatrix ι ι ℂ) : CStarMatrix (ι ⊕ ι) (ι ⊕ ι) ℂ :=
  cstarMatrixProjectionReflection (cstarMatrixColumnPairRangeProjection A B)

/-- The block-column range reflection is self-adjoint. -/
theorem cstarMatrixColumnPairRangeReflection_isSelfAdjoint
    {ι : Type*} [Fintype ι] [DecidableEq ι]
    (A B : CStarMatrix ι ι ℂ) :
    IsSelfAdjoint (cstarMatrixColumnPairRangeReflection A B) := by
  exact cstarMatrixProjectionReflection_isSelfAdjoint_of_isSelfAdjoint
    (cstarMatrixColumnPairRangeProjection A B)
    (cstarMatrixColumnPairRangeProjection_isSelfAdjoint A B)

/-- If `VᴴV = I`, then the range reflection `2VVᴴ - I` squares to identity. -/
theorem cstarMatrixColumnPairRangeReflection_mul_self_of_sum
    {ι : Type*} [Fintype ι] [DecidableEq ι]
    {A B : CStarMatrix ι ι ℂ}
    (hAB : star A * A + star B * B = 1) :
    cstarMatrixColumnPairRangeReflection A B *
        cstarMatrixColumnPairRangeReflection A B =
      (1 : CStarMatrix (ι ⊕ ι) (ι ⊕ ι) ℂ) := by
  exact cstarMatrixProjectionReflection_mul_self_of_idempotent
    (cstarMatrixColumnPairRangeProjection A B)
    (cstarMatrixColumnPairRangeProjection_mul_self_of_sum hAB)

/-- If `VᴴV = I`, then the block-column range reflection is a unit. -/
theorem cstarMatrixColumnPairRangeReflection_isUnit_of_sum
    {ι : Type*} [Fintype ι] [DecidableEq ι]
    {A B : CStarMatrix ι ι ℂ}
    (hAB : star A * A + star B * B = 1) :
    IsUnit (cstarMatrixColumnPairRangeReflection A B) := by
  exact cstarMatrixProjectionReflection_isUnit_of_idempotent
    (cstarMatrixColumnPairRangeProjection A B)
    (cstarMatrixColumnPairRangeProjection_mul_self_of_sum hAB)

/-- If `VᴴV = I`, then the block-column range reflection is unitary. -/
theorem cstarMatrixColumnPairRangeReflection_mem_unitary_of_sum
    {ι : Type*} [Fintype ι] [DecidableEq ι]
    {A B : CStarMatrix ι ι ℂ}
    (hAB : star A * A + star B * B = 1) :
    cstarMatrixColumnPairRangeReflection A B ∈
      unitary (CStarMatrix (ι ⊕ ι) (ι ⊕ ι) ℂ) := by
  exact
    cstarMatrixProjectionReflection_mem_unitary_of_isSelfAdjoint_of_idempotent
      (cstarMatrixColumnPairRangeProjection A B)
      (cstarMatrixColumnPairRangeProjection_isSelfAdjoint A B)
      (cstarMatrixColumnPairRangeProjection_mul_self_of_sum hAB)

/-- If `VᴴV = I`, then the block-column range reflection fixes the block
column: `(2VVᴴ - I)V = V`. -/
theorem cstarMatrixColumnPairRangeReflection_mul_columnPair_of_sum
    {ι : Type*} [Fintype ι] [DecidableEq ι]
    {A B : CStarMatrix ι ι ℂ}
    (hAB : star A * A + star B * B = 1) :
    cstarMatrixColumnPairRangeReflection A B *
        cstarMatrixColumnPair A B =
      cstarMatrixColumnPair A B := by
  exact cstarMatrixProjectionReflection_mul_of_mul_eq_self
    (cstarMatrixColumnPairRangeProjection A B)
    (cstarMatrixColumnPair A B)
    (cstarMatrixColumnPairRangeProjection_mul_columnPair_of_sum hAB)

/-- If `VᴴV = I`, then the block-column range reflection fixes the adjoint
block column on the right: `Vᴴ(2VVᴴ - I) = Vᴄ`. -/
theorem cstarMatrixColumnPair_conjTranspose_mul_rangeReflection_of_sum
    {ι : Type*} [Fintype ι] [DecidableEq ι]
    {A B : CStarMatrix ι ι ℂ}
    (hAB : star A * A + star B * B = 1) :
    CStarMatrix.conjTranspose (cstarMatrixColumnPair A B) *
        cstarMatrixColumnPairRangeReflection A B =
      CStarMatrix.conjTranspose (cstarMatrixColumnPair A B) := by
  exact cstarMatrix_mul_projectionReflection_of_mul_eq_self
    (CStarMatrix.conjTranspose (cstarMatrixColumnPair A B))
    (cstarMatrixColumnPairRangeProjection A B)
    (cstarMatrixColumnPair_conjTranspose_mul_rangeProjection_of_sum hAB)

/-- Compressing the block-column reflection average gives the same matrix as
compressing the original block matrix.  This is the algebraic pinching
identity used before the nonlinear Jensen step. -/
theorem cstarMatrixColumnPair_reflectionAverage_compression_of_sum
    {ι : Type*} [Fintype ι] [DecidableEq ι]
    {A B : CStarMatrix ι ι ℂ}
    (hAB : star A * A + star B * B = 1)
    (D : CStarMatrix (ι ⊕ ι) (ι ⊕ ι) ℂ) :
    CStarMatrix.conjTranspose (cstarMatrixColumnPair A B) *
        ((1 / 2 : ℂ) •
          (D + cstarMatrixColumnPairRangeReflection A B * D *
            cstarMatrixColumnPairRangeReflection A B)) *
        cstarMatrixColumnPair A B =
      CStarMatrix.conjTranspose (cstarMatrixColumnPair A B) *
        D * cstarMatrixColumnPair A B := by
  exact cstarMatrix_reflectionAverage_compression_of_fixed
    (CStarMatrix.conjTranspose (cstarMatrixColumnPair A B))
    (cstarMatrixColumnPairRangeReflection A B) D
    (cstarMatrixColumnPair A B)
    (cstarMatrixColumnPair_conjTranspose_mul_rangeReflection_of_sum hAB)
    (cstarMatrixColumnPairRangeReflection_mul_columnPair_of_sum hAB)

/-- The block-column reflection average is invariant under conjugation by the
range reflection. -/
theorem cstarMatrixColumnPair_reflectionAverage_conj_rangeReflection_of_sum
    {ι : Type*} [Fintype ι] [DecidableEq ι]
    {A B : CStarMatrix ι ι ℂ}
    (hAB : star A * A + star B * B = 1)
    (D : CStarMatrix (ι ⊕ ι) (ι ⊕ ι) ℂ) :
    cstarMatrixColumnPairRangeReflection A B *
        ((1 / 2 : ℂ) •
          (D + cstarMatrixColumnPairRangeReflection A B * D *
            cstarMatrixColumnPairRangeReflection A B)) *
        cstarMatrixColumnPairRangeReflection A B =
      (1 / 2 : ℂ) •
        (D + cstarMatrixColumnPairRangeReflection A B * D *
          cstarMatrixColumnPairRangeReflection A B) := by
  exact cstarMatrix_reflectionAverage_conj_of_involutive
    (cstarMatrixColumnPairRangeReflection A B) D
    (cstarMatrixColumnPairRangeReflection_mul_self_of_sum hAB)

/-- The block-column reflection average commutes with the range reflection. -/
theorem cstarMatrixColumnPair_reflectionAverage_commute_rangeReflection_of_sum
    {ι : Type*} [Fintype ι] [DecidableEq ι]
    {A B : CStarMatrix ι ι ℂ}
    (hAB : star A * A + star B * B = 1)
    (D : CStarMatrix (ι ⊕ ι) (ι ⊕ ι) ℂ) :
    cstarMatrixColumnPairRangeReflection A B *
        ((1 / 2 : ℂ) •
          (D + cstarMatrixColumnPairRangeReflection A B * D *
            cstarMatrixColumnPairRangeReflection A B)) =
      ((1 / 2 : ℂ) •
          (D + cstarMatrixColumnPairRangeReflection A B * D *
            cstarMatrixColumnPairRangeReflection A B)) *
        cstarMatrixColumnPairRangeReflection A B := by
  exact cstarMatrix_reflectionAverage_commute_of_involutive
    (cstarMatrixColumnPairRangeReflection A B) D
    (cstarMatrixColumnPairRangeReflection_mul_self_of_sum hAB)

/-- The block-column reflection average commutes with the range projection
`VVᴴ`. -/
theorem cstarMatrixColumnPair_reflectionAverage_commute_rangeProjection_of_sum
    {ι : Type*} [Fintype ι] [DecidableEq ι]
    {A B : CStarMatrix ι ι ℂ}
    (hAB : star A * A + star B * B = 1)
    (D : CStarMatrix (ι ⊕ ι) (ι ⊕ ι) ℂ) :
    cstarMatrixColumnPairRangeProjection A B *
        ((1 / 2 : ℂ) •
          (D + cstarMatrixColumnPairRangeReflection A B * D *
            cstarMatrixColumnPairRangeReflection A B)) =
      ((1 / 2 : ℂ) •
          (D + cstarMatrixColumnPairRangeReflection A B * D *
            cstarMatrixColumnPairRangeReflection A B)) *
        cstarMatrixColumnPairRangeProjection A B := by
  exact cstarMatrix_commute_projection_of_commute_reflection
    (cstarMatrixColumnPairRangeProjection A B)
    ((1 / 2 : ℂ) •
      (D + cstarMatrixColumnPairRangeReflection A B * D *
        cstarMatrixColumnPairRangeReflection A B))
    (cstarMatrixColumnPair_reflectionAverage_commute_rangeReflection_of_sum
      hAB D)

/-- If a block matrix commutes with the range projection \(VV^*\), then its
action on the block column factors through the compressed corner
`Vᴴ E V`. -/
theorem cstarMatrixColumnPair_mul_columnPair_eq_columnPair_compression_of_commute
    {ι : Type*} [Fintype ι] [DecidableEq ι]
    {A B : CStarMatrix ι ι ℂ}
    (hAB : star A * A + star B * B = 1)
    {E : CStarMatrix (ι ⊕ ι) (ι ⊕ ι) ℂ}
    (hcomm :
      cstarMatrixColumnPairRangeProjection A B * E =
        E * cstarMatrixColumnPairRangeProjection A B) :
    E * cstarMatrixColumnPair A B =
      cstarMatrixColumnPair A B *
        (CStarMatrix.conjTranspose (cstarMatrixColumnPair A B) *
          E * cstarMatrixColumnPair A B) := by
  let V := cstarMatrixColumnPair A B
  let Vh := CStarMatrix.conjTranspose V
  let P := cstarMatrixColumnPairRangeProjection A B
  have hPV : P * V = V := by
    dsimp [P, V]
    exact cstarMatrixColumnPairRangeProjection_mul_columnPair_of_sum hAB
  calc
    E * cstarMatrixColumnPair A B = E * V := rfl
    _ = E * (P * V) := by
          rw [hPV]
    _ = (E * P) * V := by
          rw [← cstarMatrix_mul_assoc_rect E P V]
    _ = (P * E) * V := by
          rw [← hcomm]
    _ = ((V * Vh) * E) * V := rfl
    _ = (V * Vh) * (E * V) := by
          rw [cstarMatrix_mul_assoc_rect (V * Vh) E V]
    _ = V * (Vh * (E * V)) := by
          rw [← cstarMatrix_mul_assoc_rect V Vh (E * V)]
    _ = V * ((Vh * E) * V) := by
          rw [← cstarMatrix_mul_assoc_rect Vh E V]
    _ = cstarMatrixColumnPair A B *
          (CStarMatrix.conjTranspose (cstarMatrixColumnPair A B) *
            E * cstarMatrixColumnPair A B) := rfl

/-- If a block matrix commutes with the range projection \(VV^*\), then the
adjoint block row also factors through the compressed corner. -/
theorem cstarMatrixColumnPair_conjTranspose_mul_eq_compression_mul_conjTranspose_of_commute
    {ι : Type*} [Fintype ι] [DecidableEq ι]
    {A B : CStarMatrix ι ι ℂ}
    (hAB : star A * A + star B * B = 1)
    {E : CStarMatrix (ι ⊕ ι) (ι ⊕ ι) ℂ}
    (hcomm :
      cstarMatrixColumnPairRangeProjection A B * E =
        E * cstarMatrixColumnPairRangeProjection A B) :
    CStarMatrix.conjTranspose (cstarMatrixColumnPair A B) * E =
      (CStarMatrix.conjTranspose (cstarMatrixColumnPair A B) *
          E * cstarMatrixColumnPair A B) *
        CStarMatrix.conjTranspose (cstarMatrixColumnPair A B) := by
  let V := cstarMatrixColumnPair A B
  let Vh := CStarMatrix.conjTranspose V
  let P := cstarMatrixColumnPairRangeProjection A B
  have hVhP : Vh * P = Vh := by
    dsimp [P, V, Vh]
    exact cstarMatrixColumnPair_conjTranspose_mul_rangeProjection_of_sum hAB
  calc
    CStarMatrix.conjTranspose (cstarMatrixColumnPair A B) * E = Vh * E := rfl
    _ = (Vh * P) * E := by
          rw [hVhP]
    _ = Vh * (P * E) := by
          rw [cstarMatrix_mul_assoc_rect Vh P E]
    _ = Vh * (E * P) := by
          rw [hcomm]
    _ = (Vh * E) * P := by
          rw [← cstarMatrix_mul_assoc_rect Vh E P]
    _ = (Vh * E) * (V * Vh) := rfl
    _ = ((Vh * E) * V) * Vh := by
          rw [cstarMatrix_mul_assoc_rect (Vh * E) V Vh]
    _ = (CStarMatrix.conjTranspose (cstarMatrixColumnPair A B) *
          E * cstarMatrixColumnPair A B) *
        CStarMatrix.conjTranspose (cstarMatrixColumnPair A B) := rfl

/-- The reflected block average acts on the block column through the same
compressed corner as the original block matrix. -/
theorem cstarMatrixColumnPair_reflectionAverage_mul_columnPair_of_sum
    {ι : Type*} [Fintype ι] [DecidableEq ι]
    {A B : CStarMatrix ι ι ℂ}
    (hAB : star A * A + star B * B = 1)
    (D : CStarMatrix (ι ⊕ ι) (ι ⊕ ι) ℂ) :
    ((1 / 2 : ℂ) •
          (D + cstarMatrixColumnPairRangeReflection A B * D *
            cstarMatrixColumnPairRangeReflection A B)) *
        cstarMatrixColumnPair A B =
      cstarMatrixColumnPair A B *
        (CStarMatrix.conjTranspose (cstarMatrixColumnPair A B) *
          D * cstarMatrixColumnPair A B) := by
  let E : CStarMatrix (ι ⊕ ι) (ι ⊕ ι) ℂ :=
    (1 / 2 : ℂ) •
      (D + cstarMatrixColumnPairRangeReflection A B * D *
        cstarMatrixColumnPairRangeReflection A B)
  have hfactor :
      E * cstarMatrixColumnPair A B =
        cstarMatrixColumnPair A B *
          (CStarMatrix.conjTranspose (cstarMatrixColumnPair A B) *
            E * cstarMatrixColumnPair A B) := by
    exact cstarMatrixColumnPair_mul_columnPair_eq_columnPair_compression_of_commute
      hAB (cstarMatrixColumnPair_reflectionAverage_commute_rangeProjection_of_sum
        hAB D)
  have hcomp :=
    cstarMatrixColumnPair_reflectionAverage_compression_of_sum hAB D
  calc
    ((1 / 2 : ℂ) •
          (D + cstarMatrixColumnPairRangeReflection A B * D *
            cstarMatrixColumnPairRangeReflection A B)) *
        cstarMatrixColumnPair A B =
        E * cstarMatrixColumnPair A B := rfl
    _ = cstarMatrixColumnPair A B *
        (CStarMatrix.conjTranspose (cstarMatrixColumnPair A B) *
          E * cstarMatrixColumnPair A B) := hfactor
    _ = cstarMatrixColumnPair A B *
        (CStarMatrix.conjTranspose (cstarMatrixColumnPair A B) *
          D * cstarMatrixColumnPair A B) := by
          rw [hcomp]

/-- The reflected block average acts on the adjoint block row through the same
compressed corner as the original block matrix. -/
theorem cstarMatrixColumnPair_conjTranspose_mul_reflectionAverage_of_sum
    {ι : Type*} [Fintype ι] [DecidableEq ι]
    {A B : CStarMatrix ι ι ℂ}
    (hAB : star A * A + star B * B = 1)
    (D : CStarMatrix (ι ⊕ ι) (ι ⊕ ι) ℂ) :
    CStarMatrix.conjTranspose (cstarMatrixColumnPair A B) *
        ((1 / 2 : ℂ) •
          (D + cstarMatrixColumnPairRangeReflection A B * D *
            cstarMatrixColumnPairRangeReflection A B)) =
      (CStarMatrix.conjTranspose (cstarMatrixColumnPair A B) *
          D * cstarMatrixColumnPair A B) *
        CStarMatrix.conjTranspose (cstarMatrixColumnPair A B) := by
  let E : CStarMatrix (ι ⊕ ι) (ι ⊕ ι) ℂ :=
    (1 / 2 : ℂ) •
      (D + cstarMatrixColumnPairRangeReflection A B * D *
        cstarMatrixColumnPairRangeReflection A B)
  have hfactor :
      CStarMatrix.conjTranspose (cstarMatrixColumnPair A B) * E =
        (CStarMatrix.conjTranspose (cstarMatrixColumnPair A B) *
            E * cstarMatrixColumnPair A B) *
          CStarMatrix.conjTranspose (cstarMatrixColumnPair A B) := by
    exact cstarMatrixColumnPair_conjTranspose_mul_eq_compression_mul_conjTranspose_of_commute
      hAB (cstarMatrixColumnPair_reflectionAverage_commute_rangeProjection_of_sum
        hAB D)
  have hcomp :=
    cstarMatrixColumnPair_reflectionAverage_compression_of_sum hAB D
  calc
    CStarMatrix.conjTranspose (cstarMatrixColumnPair A B) *
        ((1 / 2 : ℂ) •
          (D + cstarMatrixColumnPairRangeReflection A B * D *
            cstarMatrixColumnPairRangeReflection A B)) =
        CStarMatrix.conjTranspose (cstarMatrixColumnPair A B) * E := rfl
    _ = (CStarMatrix.conjTranspose (cstarMatrixColumnPair A B) *
            E * cstarMatrixColumnPair A B) *
          CStarMatrix.conjTranspose (cstarMatrixColumnPair A B) := hfactor
    _ = (CStarMatrix.conjTranspose (cstarMatrixColumnPair A B) *
          D * cstarMatrixColumnPair A B) *
        CStarMatrix.conjTranspose (cstarMatrixColumnPair A B) := by
          rw [hcomp]

/-- Conjugation by a unitary finite C⋆-matrix preserves strict positivity. -/
theorem cstarMatrix_unitary_conj_isStrictlyPositive
    {ι : Type*} [Fintype ι] [DecidableEq ι]
    (u : unitary (CStarMatrix ι ι ℂ)) {T : CStarMatrix ι ι ℂ}
    (hT : IsStrictlyPositive T) :
    IsStrictlyPositive
      ((u : CStarMatrix ι ι ℂ) * T * star (u : CStarMatrix ι ι ℂ)) := by
  exact (Unitary.isUnit_coe (U := u)).isStrictlyPositive_star_right_conjugate_iff.mpr hT

/-- The block-column range reflection preserves strict positivity by
conjugation whenever `VᴴV = I`. -/
theorem cstarMatrixColumnPairRangeReflection_conj_isStrictlyPositive_of_sum
    {ι : Type*} [Fintype ι] [DecidableEq ι]
    {A B : CStarMatrix ι ι ℂ}
    (hAB : star A * A + star B * B = 1)
    {T : CStarMatrix (ι ⊕ ι) (ι ⊕ ι) ℂ}
    (hT : IsStrictlyPositive T) :
    IsStrictlyPositive
      (cstarMatrixColumnPairRangeReflection A B * T *
        star (cstarMatrixColumnPairRangeReflection A B)) := by
  let u : unitary (CStarMatrix (ι ⊕ ι) (ι ⊕ ι) ℂ) :=
    ⟨cstarMatrixColumnPairRangeReflection A B,
      cstarMatrixColumnPairRangeReflection_mem_unitary_of_sum hAB⟩
  exact cstarMatrix_unitary_conj_isStrictlyPositive u hT

end NumStability
