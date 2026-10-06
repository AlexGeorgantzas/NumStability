import Mathlib.Tactic.Linarith
import Mathlib.Tactic.NormNum
import Mathlib.Tactic.Positivity
import Mathlib.Tactic.Ring
import NumStability.Algorithms.LinearSystems.LU.BlockLU.BlockMatrices
import NumStability.Algorithms.LinearSystems.LU.BlockLU.Factorization
import NumStability.Algorithms.LinearSystems.LU.BlockLU.PositiveDefinite
import NumStability.Algorithms.LinearSystems.LU.BlockLU.RecursiveFactorization
import NumStability.Algorithms.LU.GaussianElimination
import NumStability.Analysis.MatrixAlgebra

/-!
# Reusable positive-definite block-factor bounds

Reusable operator-norm and block-assembly certificates for positive-definite
block LU factors.
-/

namespace NumStability

/-- Operator-2 certificates add under pointwise matrix addition. -/
theorem finiteOpNorm2Le_add {ι : Type*} [Fintype ι]
    (M N : ι → ι → ℝ) {a b : ℝ}
    (hM : finiteOpNorm2Le M a) (hN : finiteOpNorm2Le N b) :
    finiteOpNorm2Le (fun i j => M i j + N i j) (a + b) := by
  intro x
  have hact :
      finiteMatVec (fun i j => M i j + N i j) x =
        fun i => finiteMatVec M x i + finiteMatVec N x i := by
    ext i
    simp [finiteMatVec, Finset.sum_add_distrib, add_mul]
  calc
    finiteVecNorm2 (finiteMatVec (fun i j => M i j + N i j) x)
        = finiteVecNorm2
            (fun i => finiteMatVec M x i + finiteMatVec N x i) := by rw [hact]
    _ ≤ finiteVecNorm2 (finiteMatVec M x) +
          finiteVecNorm2 (finiteMatVec N x) :=
        finiteVecNorm2_add_le _ _
    _ ≤ a * finiteVecNorm2 x + b * finiteVecNorm2 x :=
        add_le_add (hM x) (hN x)
    _ = (a + b) * finiteVecNorm2 x := by ring

/-- Enlarge the radius of a finite operator-2 certificate. -/
theorem finiteOpNorm2Le_mono {ι : Type*} [Fintype ι]
    (M : ι → ι → ℝ) {a b : ℝ} (hab : a ≤ b)
    (hM : finiteOpNorm2Le M a) : finiteOpNorm2Le M b := by
  intro x
  exact (hM x).trans
    (mul_le_mul_of_nonneg_right hab (finiteVecNorm2_nonneg x))

/-- A rectangular operator placed in the lower-left corner of an otherwise
    zero sum-indexed square matrix keeps the same operator-2 bound. -/
theorem finiteOpNorm2Le_fromBlocks_lowerLeft
    {α β : Type*} [Fintype α] [Fintype β]
    (M : β → α → ℝ) {c : ℝ} (hc : 0 ≤ c)
    (hM : ∀ x : α → ℝ,
      finiteVecNorm2 (finiteMatVec M x) ≤ c * finiteVecNorm2 x) :
    finiteOpNorm2Le
      (fun i j : α ⊕ β =>
        (Matrix.fromBlocks (0 : Matrix α α ℝ) 0 M 0) i j) c := by
  intro z
  let x : α → ℝ := fun i => z (Sum.inl i)
  have hact :
      finiteMatVec
          (fun i j : α ⊕ β =>
            (Matrix.fromBlocks (0 : Matrix α α ℝ) 0 M 0) i j) z =
        sumInrVec (finiteMatVec M x) := by
    ext i
    cases i with
    | inl i =>
        simp [finiteMatVec, Matrix.fromBlocks, sumInrVec]
    | inr i =>
        simp [finiteMatVec, Matrix.fromBlocks, sumInrVec, x,
          Fintype.sum_sum_type]
  calc
    finiteVecNorm2
        (finiteMatVec
          (fun i j : α ⊕ β =>
            (Matrix.fromBlocks (0 : Matrix α α ℝ) 0 M 0) i j) z)
        = finiteVecNorm2 (finiteMatVec M x) := by
            rw [hact, finiteVecNorm2_sumInrVec]
    _ ≤ c * finiteVecNorm2 x := hM x
    _ ≤ c * finiteVecNorm2 z :=
      mul_le_mul_of_nonneg_left (finiteVecNorm2_sumInl_restrict_le z) hc

/-- A block diagonal matrix with identity on the first summand inherits a
    common bound `d` from its trailing block whenever `1 ≤ d`. -/
theorem finiteOpNorm2Le_fromBlocks_id_diag
    {α β : Type*} [Fintype α] [Fintype β] [DecidableEq α]
    (T : β → β → ℝ) {d : ℝ} (hd : 1 ≤ d)
    (hT : finiteOpNorm2Le T d) :
    finiteOpNorm2Le
      (fun i j : α ⊕ β =>
        (Matrix.fromBlocks (1 : Matrix α α ℝ) 0 0 T) i j) d := by
  classical
  intro z
  let x : α → ℝ := fun i => z (Sum.inl i)
  let y : β → ℝ := fun i => z (Sum.inr i)
  have hz : z = sumBothVec x y := by
    ext i
    cases i <;> rfl
  have hact :
      finiteMatVec
          (fun i j : α ⊕ β =>
            (Matrix.fromBlocks (1 : Matrix α α ℝ) 0 0 T) i j) z =
        sumBothVec x (finiteMatVec T y) := by
    ext i
    cases i with
    | inl i =>
        simp [finiteMatVec, Matrix.fromBlocks, Matrix.one_apply, sumBothVec, x,
          Fintype.sum_sum_type]
    | inr i =>
        simp [finiteMatVec, Matrix.fromBlocks, sumBothVec, y,
          Fintype.sum_sum_type]
  have hd0 : 0 ≤ d := le_trans zero_le_one hd
  have hTy := hT y
  have hTy0 := finiteVecNorm2_nonneg (finiteMatVec T y)
  have hy0 := finiteVecNorm2_nonneg y
  have hx0 := finiteVecNorm2_nonneg x
  have hz0 := finiteVecNorm2_nonneg z
  have hdsq : 1 ≤ d ^ 2 := by nlinarith
  have hTySq : finiteVecNorm2 (finiteMatVec T y) ^ 2 ≤
      (d * finiteVecNorm2 y) ^ 2 := by nlinarith
  have hxSq : finiteVecNorm2 x ^ 2 ≤ d ^ 2 * finiteVecNorm2 x ^ 2 := by
    simpa only [one_mul] using
      mul_le_mul_of_nonneg_right hdsq (sq_nonneg (finiteVecNorm2 x))
  have hzSq : finiteVecNorm2 z ^ 2 =
      finiteVecNorm2 x ^ 2 + finiteVecNorm2 y ^ 2 := by
    rw [finiteVecNorm2_sq, hz, finiteVecNorm2Sq_sumBothVec,
      ← finiteVecNorm2_sq, ← finiteVecNorm2_sq]
  have houtSq :
      finiteVecNorm2
          (finiteMatVec
            (fun i j : α ⊕ β =>
              (Matrix.fromBlocks (1 : Matrix α α ℝ) 0 0 T) i j) z) ^ 2 =
        finiteVecNorm2 x ^ 2 + finiteVecNorm2 (finiteMatVec T y) ^ 2 := by
    rw [hact, finiteVecNorm2_sq, finiteVecNorm2Sq_sumBothVec,
      ← finiteVecNorm2_sq, ← finiteVecNorm2_sq]
  have hsquare :
      finiteVecNorm2
          (finiteMatVec
            (fun i j : α ⊕ β =>
              (Matrix.fromBlocks (1 : Matrix α α ℝ) 0 0 T) i j) z) ^ 2 ≤
        (d * finiteVecNorm2 z) ^ 2 := by
    rw [houtSq, show (d * finiteVecNorm2 z) ^ 2 =
      d ^ 2 * finiteVecNorm2 z ^ 2 by ring, hzSq]
    nlinarith
  have hout0 := finiteVecNorm2_nonneg
    (finiteMatVec
      (fun i j : α ⊕ β =>
        (Matrix.fromBlocks (1 : Matrix α α ℝ) 0 0 T) i j) z)
  have hright0 : 0 ≤ d * finiteVecNorm2 z := mul_nonneg hd0 hz0
  nlinarith

/-- One SPD block-elimination step for the lower factor: a trailing lower
    certificate of radius `d` and a multiplier-column certificate of radius
    `c` give radius `d + c` for `[[I,0],[M,T]]`. -/
theorem finiteOpNorm2Le_fromBlocks_unitLower
    {α β : Type*} [Fintype α] [Fintype β] [DecidableEq α]
    (M : β → α → ℝ) (T : β → β → ℝ) {c d : ℝ}
    (hc : 0 ≤ c) (hd : 1 ≤ d)
    (hM : ∀ x : α → ℝ,
      finiteVecNorm2 (finiteMatVec M x) ≤ c * finiteVecNorm2 x)
    (hT : finiteOpNorm2Le T d) :
    finiteOpNorm2Le
      (fun i j : α ⊕ β =>
        (Matrix.fromBlocks (1 : Matrix α α ℝ) 0 M T) i j) (d + c) := by
  have hdiag := finiteOpNorm2Le_fromBlocks_id_diag
    (α := α) (β := β) T hd hT
  have hoff := finiteOpNorm2Le_fromBlocks_lowerLeft
    (α := α) (β := β) M hc hM
  have hadd := finiteOpNorm2Le_add
    (fun i j : α ⊕ β =>
      (Matrix.fromBlocks (1 : Matrix α α ℝ) 0 0 T) i j)
    (fun i j : α ⊕ β =>
      (Matrix.fromBlocks (0 : Matrix α α ℝ) 0 M 0) i j)
    hdiag hoff
  have heq :
      (fun i j : α ⊕ β =>
        (Matrix.fromBlocks (1 : Matrix α α ℝ) 0 M T) i j) =
      (fun i j : α ⊕ β =>
        (Matrix.fromBlocks (1 : Matrix α α ℝ) 0 0 T) i j +
          (Matrix.fromBlocks (0 : Matrix α α ℝ) 0 M 0) i j) := by
    ext i j
    cases i <;> cases j <;> simp [Matrix.fromBlocks]
  rw [heq]
  exact hadd

/-- One SPD block-elimination step for the upper factor.  The first block row
    is a row restriction of the current SPD matrix, while the remaining rows
    are the recursive upper factor.  Their squared Euclidean norms combine to
    change `sqrt m * a` into `sqrt (m+1) * a`. -/
theorem finiteOpNorm2Le_fromBlocks_upper_step
    {α β : Type*} [Fintype α] [Fintype β]
    (A11 : α → α → ℝ) (A12 : α → β → ℝ)
    (A21 : β → α → ℝ) (A22 T : β → β → ℝ)
    (m : ℕ) {a : ℝ} (ha : 0 ≤ a)
    (hA : finiteOpNorm2Le
      (fun i j : α ⊕ β =>
        (Matrix.fromBlocks A11 A12 A21 A22) i j) a)
    (hT : finiteOpNorm2Le T (Real.sqrt (m : ℝ) * a)) :
    finiteOpNorm2Le
      (fun i j : α ⊕ β =>
        (Matrix.fromBlocks A11 A12 0 T) i j)
      (Real.sqrt ((m + 1 : ℕ) : ℝ) * a) := by
  intro z
  let y : β → ℝ := fun i => z (Sum.inr i)
  let top : α → ℝ := fun i =>
    finiteMatVec
      (fun p q : α ⊕ β => (Matrix.fromBlocks A11 A12 A21 A22) p q)
      z (Sum.inl i)
  have hact :
      finiteMatVec
          (fun i j : α ⊕ β =>
            (Matrix.fromBlocks A11 A12 0 T) i j) z =
        sumBothVec top (finiteMatVec T y) := by
    ext i
    cases i with
    | inl i =>
        simp [finiteMatVec, Matrix.fromBlocks, sumBothVec, top,
          Fintype.sum_sum_type]
    | inr i =>
        simp [finiteMatVec, Matrix.fromBlocks, sumBothVec, y,
          Fintype.sum_sum_type]
  have htop : finiteVecNorm2 top ≤ a * finiteVecNorm2 z := by
    calc
      finiteVecNorm2 top ≤
          finiteVecNorm2
            (finiteMatVec
              (fun p q : α ⊕ β =>
                (Matrix.fromBlocks A11 A12 A21 A22) p q) z) :=
        finiteVecNorm2_sumInl_restrict_le _
      _ ≤ a * finiteVecNorm2 z := hA z
  have htail0 := finiteVecNorm2_nonneg (finiteMatVec T y)
  have htop0 := finiteVecNorm2_nonneg top
  have hz0 := finiteVecNorm2_nonneg z
  have hy0 := finiteVecNorm2_nonneg y
  have hsqrt0 : 0 ≤ Real.sqrt (m : ℝ) := Real.sqrt_nonneg _
  have hcoef0 : 0 ≤ Real.sqrt (m : ℝ) * a := mul_nonneg hsqrt0 ha
  have hy_le : finiteVecNorm2 y ≤ finiteVecNorm2 z :=
    finiteVecNorm2_sumInr_restrict_le z
  have htail : finiteVecNorm2 (finiteMatVec T y) ≤
      (Real.sqrt (m : ℝ) * a) * finiteVecNorm2 z :=
    (hT y).trans (mul_le_mul_of_nonneg_left hy_le hcoef0)
  have htopSq : finiteVecNorm2 top ^ 2 ≤
      (a * finiteVecNorm2 z) ^ 2 := by nlinarith
  have htailSq : finiteVecNorm2 (finiteMatVec T y) ^ 2 ≤
      ((Real.sqrt (m : ℝ) * a) * finiteVecNorm2 z) ^ 2 := by
    nlinarith
  have houtSq :
      finiteVecNorm2
          (finiteMatVec
            (fun i j : α ⊕ β =>
              (Matrix.fromBlocks A11 A12 0 T) i j) z) ^ 2 =
        finiteVecNorm2 top ^ 2 + finiteVecNorm2 (finiteMatVec T y) ^ 2 := by
    rw [hact, finiteVecNorm2_sq, finiteVecNorm2Sq_sumBothVec,
      ← finiteVecNorm2_sq, ← finiteVecNorm2_sq]
  have hmsqrt : Real.sqrt (m : ℝ) ^ 2 = (m : ℝ) :=
    Real.sq_sqrt (Nat.cast_nonneg m)
  have hsuccsqrt : Real.sqrt ((m + 1 : ℕ) : ℝ) ^ 2 = ((m + 1 : ℕ) : ℝ) :=
    Real.sq_sqrt (Nat.cast_nonneg (m + 1))
  have hsquare :
      finiteVecNorm2
          (finiteMatVec
            (fun i j : α ⊕ β =>
              (Matrix.fromBlocks A11 A12 0 T) i j) z) ^ 2 ≤
        ((Real.sqrt ((m + 1 : ℕ) : ℝ) * a) * finiteVecNorm2 z) ^ 2 := by
    rw [houtSq]
    calc
      finiteVecNorm2 top ^ 2 + finiteVecNorm2 (finiteMatVec T y) ^ 2
          ≤ (a * finiteVecNorm2 z) ^ 2 +
              ((Real.sqrt (m : ℝ) * a) * finiteVecNorm2 z) ^ 2 :=
        add_le_add htopSq htailSq
      _ = ((Real.sqrt ((m + 1 : ℕ) : ℝ) * a) * finiteVecNorm2 z) ^ 2 := by
        rw [show ((m + 1 : ℕ) : ℝ) = (m : ℝ) + 1 by norm_num]
        have hs : Real.sqrt ((m : ℝ) + 1) ^ 2 = (m : ℝ) + 1 := by
          simpa using hsuccsqrt
        nlinarith [hmsqrt, hs]
  have hout0 := finiteVecNorm2_nonneg
    (finiteMatVec
      (fun i j : α ⊕ β => (Matrix.fromBlocks A11 A12 0 T) i j) z)
  have hright0 :
      0 ≤ (Real.sqrt ((m + 1 : ℕ) : ℝ) * a) * finiteVecNorm2 z :=
    mul_nonneg (mul_nonneg (Real.sqrt_nonneg _) ha) hz0
  nlinarith

/-- Transport an operator-2 certificate from the uniform block flattening to
    the scalar first-block split. -/
theorem finiteOpNorm2Le_blockMatrixFirstSplitFlat_of_blockMatrixFlatFin
    {m r : ℕ}
    (A : Fin (m + 1) → Fin (m + 1) → Matrix (Fin r) (Fin r) ℝ)
    {c : ℝ}
    (hA : finiteOpNorm2Le (blockMatrixFlatFin A) c) :
    finiteOpNorm2Le (blockMatrixFirstSplitFlat A) c := by
  rw [blockMatrixFirstSplitFlat_eq_blockMatrixFlatFin_reindex]
  exact finiteOpNorm2Le_reindex_equiv
    blockMatrixFirstSplitToFlatFinEquiv (blockMatrixFlatFin A) hA

/-- Transport an operator-2 certificate from the scalar first-block split
    back to the uniform block flattening. -/
theorem finiteOpNorm2Le_blockMatrixFlatFin_of_blockMatrixFirstSplitFlat
    {m r : ℕ}
    (A : Fin (m + 1) → Fin (m + 1) → Matrix (Fin r) (Fin r) ℝ)
    {c : ℝ}
    (hA : finiteOpNorm2Le (blockMatrixFirstSplitFlat A) c) :
    finiteOpNorm2Le (blockMatrixFlatFin A) c := by
  have h := finiteOpNorm2Le_reindex_equiv
    blockMatrixFirstSplitToFlatFinEquiv.symm (blockMatrixFirstSplitFlat A) hA
  convert h using 1
  ext p q
  rw [blockMatrixFirstSplitFlat_eq_blockMatrixFlatFin_reindex]
  simp

/-- The sum-indexed first-block partition is exactly the standard four-block
    `Matrix.fromBlocks` display. -/
theorem blockMatrixFirstSplit_fromBlocks_eq {m r : ℕ}
    (A : Fin (m + 1) → Fin (m + 1) → Matrix (Fin r) (Fin r) ℝ) :
    (fun i j : Fin r ⊕ Fin (m * r) =>
      blockMatrixFirstSplitFlat A (finSumFinEquiv i) (finSumFinEquiv j)) =
      fun i j =>
        (Matrix.fromBlocks (blockMatrixFirstSplitA11 A)
          (blockMatrixFirstSplitA12 A) (blockMatrixFirstSplitA21 A)
          (blockMatrixFirstSplitA22 A)) i j := by
  ext i j
  cases i with
  | inl s =>
      cases j with
      | inl t =>
          simpa [Matrix.fromBlocks, blockMatrixFirstSplitA11] using
            (blockMatrixFirstSplitFlat_11 A s t)
      | inr q =>
          let jq := finProdFinEquiv.symm q
          have hq : finProdFinEquiv jq = q := finProdFinEquiv.apply_symm_apply q
          have hsplit := blockMatrixFirstSplitFlat_12 A s jq.1 jq.2
          rw [hq] at hsplit
          simpa [Matrix.fromBlocks, blockMatrixFirstSplitA12, jq] using hsplit
  | inr p =>
      let ip := finProdFinEquiv.symm p
      have hp : finProdFinEquiv ip = p := finProdFinEquiv.apply_symm_apply p
      cases j with
      | inl t =>
          have hsplit := blockMatrixFirstSplitFlat_21 A ip.1 ip.2 t
          rw [hp] at hsplit
          simpa [Matrix.fromBlocks, blockMatrixFirstSplitA21, ip] using hsplit
      | inr q =>
          let jq := finProdFinEquiv.symm q
          have hq : finProdFinEquiv jq = q := finProdFinEquiv.apply_symm_apply q
          have hsplit := blockMatrixFirstSplitFlat_22 A ip.1 jq.1 ip.2 jq.2
          rw [hp, hq] at hsplit
          simpa [Matrix.fromBlocks, blockMatrixFirstSplitA22,
            blockMatrixFlatFin, ip, jq] using hsplit

/-- SPD of the uniformly flattened block matrix gives positive definiteness
    of its standard first-block `fromBlocks` partition. -/
theorem blockMatrixFirstSplit_fromBlocks_posDef_of_isSymPosDef_flatFin
    {m r : ℕ}
    (A : Fin (m + 1) → Fin (m + 1) → Matrix (Fin r) (Fin r) ℝ)
    (hSPD : IsSymPosDef ((m + 1) * r) (blockMatrixFlatFin A)) :
    (Matrix.fromBlocks (blockMatrixFirstSplitA11 A)
      (blockMatrixFirstSplitA12 A) (blockMatrixFirstSplitA21 A)
      (blockMatrixFirstSplitA22 A)).PosDef := by
  have hUniform := isSymPosDef_to_matrix_posDef (blockMatrixFlatFin A) hSPD
  have hFirst : Matrix.PosDef (blockMatrixFirstSplitFlat A) := by
    rw [blockMatrixFirstSplitFlat_eq_blockMatrixFlatFin_reindex]
    exact matrix_posDef_submatrix_of_injective hUniform
      blockMatrixFirstSplitToFlatFinEquiv
      blockMatrixFirstSplitToFlatFinEquiv.injective
  have hSum := matrix_posDef_submatrix_of_injective hFirst
    (finSumFinEquiv : (Fin r ⊕ Fin (m * r)) → Fin (r + m * r))
    finSumFinEquiv.injective
  have heq :
      (blockMatrixFirstSplitFlat A).submatrix finSumFinEquiv finSumFinEquiv =
        Matrix.fromBlocks (blockMatrixFirstSplitA11 A)
          (blockMatrixFirstSplitA12 A) (blockMatrixFirstSplitA21 A)
          (blockMatrixFirstSplitA22 A) := by
    simpa [Matrix.submatrix] using blockMatrixFirstSplit_fromBlocks_eq A
  rw [heq] at hSum
  exact hSum

/-- In a positive-definite first-block partition, the top-right block is the
    transpose of the bottom-left block. -/
theorem blockMatrixFirstSplitA12_eq_transpose_A21_of_posDef {m r : ℕ}
    (A : Fin (m + 1) → Fin (m + 1) → Matrix (Fin r) (Fin r) ℝ)
    (hFull : (Matrix.fromBlocks (blockMatrixFirstSplitA11 A)
      (blockMatrixFirstSplitA12 A) (blockMatrixFirstSplitA21 A)
      (blockMatrixFirstSplitA22 A)).PosDef) :
    blockMatrixFirstSplitA12 A = (blockMatrixFirstSplitA21 A).transpose := by
  ext i j
  have hherm := hFull.1.eq
  have hentry := congrArg
    (fun M : Matrix (Fin r ⊕ Fin (m * r)) (Fin r ⊕ Fin (m * r)) ℝ =>
      M (Sum.inr j) (Sum.inl i)) hherm
  simpa [Matrix.fromBlocks] using hentry

/-- The first-split scalar view of the explicit one-step lower factor is the
    standard `[[I,0],[A21*A11inv,L_S]]` matrix. -/
theorem blockLUOneStepL_firstSplit_fromBlocks {m r : ℕ}
    (A : Fin (m + 1) → Fin (m + 1) → Matrix (Fin r) (Fin r) ℝ)
    (A11_inv : Matrix (Fin r) (Fin r) ℝ)
    (L_S : Fin m → Fin m → Matrix (Fin r) (Fin r) ℝ) :
    (fun i j : Fin r ⊕ Fin (m * r) =>
      blockMatrixFirstSplitFlat (blockLUOneStepL A A11_inv L_S)
        (finSumFinEquiv i) (finSumFinEquiv j)) =
      fun i j =>
        (Matrix.fromBlocks (1 : Matrix (Fin r) (Fin r) ℝ) 0
          (blockMatrixFirstSplitA21 A * A11_inv)
          (blockMatrixFlatFin L_S)) i j := by
  ext i j
  cases i with
  | inl s =>
      cases j with
      | inl t =>
          simp [blockMatrixFirstSplitFlat, blockLUOneStepL,
            Matrix.fromBlocks, idBlock, Matrix.one_apply]
      | inr q =>
          let jq := finProdFinEquiv.symm q
          have hq : finProdFinEquiv jq = q := finProdFinEquiv.apply_symm_apply q
          rw [← hq]
          simp [blockMatrixFirstSplitFlat, blockLUOneStepL,
            Matrix.fromBlocks, zeroBlock]
  | inr p =>
      let ip := finProdFinEquiv.symm p
      have hp : finProdFinEquiv ip = p := finProdFinEquiv.apply_symm_apply p
      rw [← hp]
      cases j with
      | inl t =>
          simp [blockMatrixFirstSplitFlat, blockLUOneStepL,
            Matrix.fromBlocks, blockMatrixFirstSplitA21, Matrix.mul_apply]
      | inr q =>
          let jq := finProdFinEquiv.symm q
          have hq : finProdFinEquiv jq = q := finProdFinEquiv.apply_symm_apply q
          rw [← hq]
          simp [blockMatrixFirstSplitFlat, blockLUOneStepL,
            Matrix.fromBlocks, blockMatrixFlatFin]

/-- The first-split scalar view of the explicit one-step upper factor is the
    standard `[[A11,A12],[0,U_S]]` matrix. -/
theorem blockLUOneStepU_firstSplit_fromBlocks {m r : ℕ}
    (A : Fin (m + 1) → Fin (m + 1) → Matrix (Fin r) (Fin r) ℝ)
    (U_S : Fin m → Fin m → Matrix (Fin r) (Fin r) ℝ) :
    (fun i j : Fin r ⊕ Fin (m * r) =>
      blockMatrixFirstSplitFlat (blockLUOneStepU A U_S)
        (finSumFinEquiv i) (finSumFinEquiv j)) =
      fun i j =>
        (Matrix.fromBlocks (blockMatrixFirstSplitA11 A)
          (blockMatrixFirstSplitA12 A) 0 (blockMatrixFlatFin U_S)) i j := by
  ext i j
  cases i with
  | inl s =>
      cases j with
      | inl t =>
          simp [blockMatrixFirstSplitFlat, blockLUOneStepU,
            Matrix.fromBlocks, blockMatrixFirstSplitA11]
      | inr q =>
          let jq := finProdFinEquiv.symm q
          have hq : finProdFinEquiv jq = q := finProdFinEquiv.apply_symm_apply q
          rw [← hq]
          simp [blockMatrixFirstSplitFlat, blockLUOneStepU,
            Matrix.fromBlocks, blockMatrixFirstSplitA12]
  | inr p =>
      let ip := finProdFinEquiv.symm p
      have hp : finProdFinEquiv ip = p := finProdFinEquiv.apply_symm_apply p
      rw [← hp]
      cases j with
      | inl t =>
          simp [blockMatrixFirstSplitFlat, blockLUOneStepU,
            Matrix.fromBlocks, zeroBlock]
      | inr q =>
          let jq := finProdFinEquiv.symm q
          have hq : finProdFinEquiv jq = q := finProdFinEquiv.apply_symm_apply q
          rw [← hq]
          simp [blockMatrixFirstSplitFlat, blockLUOneStepU,
            Matrix.fromBlocks, blockMatrixFlatFin]

/-- Global lower-factor norm propagation for one explicit block-LU step. -/
theorem finiteOpNorm2Le_blockLUOneStepL {m r : ℕ}
    (A : Fin (m + 1) → Fin (m + 1) → Matrix (Fin r) (Fin r) ℝ)
    (A11_inv : Matrix (Fin r) (Fin r) ℝ)
    (L_S : Fin m → Fin m → Matrix (Fin r) (Fin r) ℝ)
    {c d : ℝ} (hc : 0 ≤ c) (hd : 1 ≤ d)
    (hL21 : rectOpNorm2Le
      (blockMatrixFirstSplitA21 A * A11_inv) c)
    (hTail : finiteOpNorm2Le (blockMatrixFlatFin L_S) d) :
    finiteOpNorm2Le
      (blockMatrixFlatFin (blockLUOneStepL A A11_inv L_S)) (d + c) := by
  let F : (Fin r ⊕ Fin (m * r)) → (Fin r ⊕ Fin (m * r)) → ℝ :=
    fun i j =>
      (Matrix.fromBlocks (1 : Matrix (Fin r) (Fin r) ℝ) 0
        (blockMatrixFirstSplitA21 A * A11_inv)
        (blockMatrixFlatFin L_S)) i j
  have hF : finiteOpNorm2Le F (d + c) := by
    simpa [F] using
      (finiteOpNorm2Le_fromBlocks_unitLower
        (blockMatrixFirstSplitA21 A * A11_inv)
        (blockMatrixFlatFin L_S) hc hd hL21 hTail)
  have hfirst : finiteOpNorm2Le
      (blockMatrixFirstSplitFlat (blockLUOneStepL A A11_inv L_S))
      (d + c) := by
    have hreindex := finiteOpNorm2Le_reindex_equiv
      (finSumFinEquiv.symm : Fin (r + m * r) ≃ (Fin r ⊕ Fin (m * r))) F hF
    convert hreindex using 1
    ext p q
    have heq := congr_fun
      (congr_fun (blockLUOneStepL_firstSplit_fromBlocks A A11_inv L_S)
        (finSumFinEquiv.symm p)) (finSumFinEquiv.symm q)
    simpa [F] using heq
  exact finiteOpNorm2Le_blockMatrixFlatFin_of_blockMatrixFirstSplitFlat
    (blockLUOneStepL A A11_inv L_S) hfirst

/-- Global upper-factor norm propagation for one explicit SPD block-LU step. -/
theorem finiteOpNorm2Le_blockLUOneStepU {m r : ℕ}
    (A : Fin (m + 1) → Fin (m + 1) → Matrix (Fin r) (Fin r) ℝ)
    (U_S : Fin m → Fin m → Matrix (Fin r) (Fin r) ℝ)
    (mStages : ℕ) {a : ℝ} (ha : 0 ≤ a)
    (hA : finiteOpNorm2Le (blockMatrixFlatFin A) a)
    (hTail : finiteOpNorm2Le (blockMatrixFlatFin U_S)
      (Real.sqrt (mStages : ℝ) * a)) :
    finiteOpNorm2Le (blockMatrixFlatFin (blockLUOneStepU A U_S))
      (Real.sqrt ((mStages + 1 : ℕ) : ℝ) * a) := by
  have hAfirst :=
    finiteOpNorm2Le_blockMatrixFirstSplitFlat_of_blockMatrixFlatFin A hA
  let Afull : (Fin r ⊕ Fin (m * r)) → (Fin r ⊕ Fin (m * r)) → ℝ :=
    fun i j => blockMatrixFirstSplitFlat A (finSumFinEquiv i) (finSumFinEquiv j)
  have hAfull : finiteOpNorm2Le Afull a := by
    exact finiteOpNorm2Le_reindex_equiv
      (finSumFinEquiv : (Fin r ⊕ Fin (m * r)) ≃ Fin (r + m * r))
      (blockMatrixFirstSplitFlat A) hAfirst
  have hAeq : Afull = fun i j =>
      (Matrix.fromBlocks (blockMatrixFirstSplitA11 A)
        (blockMatrixFirstSplitA12 A) (blockMatrixFirstSplitA21 A)
        (blockMatrixFirstSplitA22 A)) i j := by
    ext i j
    cases i with
    | inl s =>
        cases j with
        | inl t => simp [Afull, Matrix.fromBlocks, blockMatrixFirstSplitA11]
        | inr q =>
            let jq := finProdFinEquiv.symm q
            have hq : finProdFinEquiv jq = q := finProdFinEquiv.apply_symm_apply q
            have hsplit := blockMatrixFirstSplitFlat_12 A s jq.1 jq.2
            rw [hq] at hsplit
            simpa [Afull, Matrix.fromBlocks, blockMatrixFirstSplitA12, jq] using
              hsplit
    | inr p =>
        let ip := finProdFinEquiv.symm p
        have hp : finProdFinEquiv ip = p := finProdFinEquiv.apply_symm_apply p
        cases j with
        | inl t =>
            have hsplit := blockMatrixFirstSplitFlat_21 A ip.1 ip.2 t
            rw [hp] at hsplit
            simpa [Afull, Matrix.fromBlocks, blockMatrixFirstSplitA21, ip] using
              hsplit
        | inr q =>
            let jq := finProdFinEquiv.symm q
            have hq : finProdFinEquiv jq = q := finProdFinEquiv.apply_symm_apply q
            have hsplit := blockMatrixFirstSplitFlat_22 A ip.1 jq.1 ip.2 jq.2
            rw [hp, hq] at hsplit
            simpa [Afull, Matrix.fromBlocks, blockMatrixFirstSplitA22,
              blockMatrixFlatFin, ip, jq] using hsplit
  have hsum : finiteOpNorm2Le
      (fun i j : Fin r ⊕ Fin (m * r) =>
        (Matrix.fromBlocks (blockMatrixFirstSplitA11 A)
          (blockMatrixFirstSplitA12 A) 0 (blockMatrixFlatFin U_S)) i j)
      (Real.sqrt ((mStages + 1 : ℕ) : ℝ) * a) := by
    apply finiteOpNorm2Le_fromBlocks_upper_step
      (blockMatrixFirstSplitA11 A) (blockMatrixFirstSplitA12 A)
      (blockMatrixFirstSplitA21 A) (blockMatrixFirstSplitA22 A)
      (blockMatrixFlatFin U_S) mStages ha
    · simpa [← hAeq] using hAfull
    · exact hTail
  have hfirst : finiteOpNorm2Le
      (blockMatrixFirstSplitFlat (blockLUOneStepU A U_S))
      (Real.sqrt ((mStages + 1 : ℕ) : ℝ) * a) := by
    have hreindex := finiteOpNorm2Le_reindex_equiv
      (finSumFinEquiv.symm : Fin (r + m * r) ≃ (Fin r ⊕ Fin (m * r)))
      (fun i j : Fin r ⊕ Fin (m * r) =>
        (Matrix.fromBlocks (blockMatrixFirstSplitA11 A)
          (blockMatrixFirstSplitA12 A) 0 (blockMatrixFlatFin U_S)) i j)
      hsum
    convert hreindex using 1
    ext p q
    have heq := congr_fun
      (congr_fun (blockLUOneStepU_firstSplit_fromBlocks A U_S)
        (finSumFinEquiv.symm p)) (finSumFinEquiv.symm q)
    simpa using heq
  exact finiteOpNorm2Le_blockMatrixFlatFin_of_blockMatrixFirstSplitFlat
    (blockLUOneStepU A U_S) hfirst

/-- Every uniformly flattened zero-block matrix has any nonnegative
    operator-2 radius. -/
theorem finiteOpNorm2Le_blockMatrixFlatFin_zero {r : ℕ}
    (B : Fin 0 → Fin 0 → Matrix (Fin r) (Fin r) ℝ)
    {c : ℝ} (hc : 0 ≤ c) :
    finiteOpNorm2Le (blockMatrixFlatFin B) c := by
  apply finiteOpNorm2Le_of_finiteFrobNormSq_le_sq _ hc
  have hempty : (Finset.univ : Finset (Fin (0 * r))) = ∅ := by
    apply Finset.eq_empty_iff_forall_notMem.mpr
    intro i _hi
    exact (Nat.not_lt_zero i.val) (by simpa using i.isLt)
  unfold finiteFrobNormSq
  rw [hempty]
  positivity

end NumStability
