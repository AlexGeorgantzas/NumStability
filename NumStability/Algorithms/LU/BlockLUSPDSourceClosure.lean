/-
  Algorithms/LU/BlockLUSPDSourceClosure.lean

  Source-level SPD closure for Higham, Chapter 13, equations (13.24) and
  (13.25).  This module connects the proved Lemmas 13.9--13.10 to the
  concrete recursively assembled block-LU factors and their global
  Euclidean operator-norm bounds.
-/

import NumStability.Algorithms.LU.BlockLURowSourceClosure

namespace NumStability

/-- Mathlib positive definiteness implies the repository's finite real SPD
    predicate. -/
theorem matrix_posDef_to_isSymPosDef {n : ℕ}
    (A : Fin n → Fin n → ℝ)
    (hA : Matrix.PosDef (A : Matrix (Fin n) (Fin n) ℝ)) :
    IsSymPosDef n A := by
  constructor
  · intro i j
    have hherm := hA.1.eq
    have hij := congrArg (fun M : Matrix (Fin n) (Fin n) ℝ => M i j) hherm
    simpa using hij.symm
  · intro x hx
    have hxne : x ≠ 0 := by
      intro hzero
      obtain ⟨i, hi⟩ := hx
      exact hi (congr_fun hzero i)
    have hpos := hA.dotProduct_mulVec_pos hxne
    simpa [dotProduct, Matrix.mulVec, Finset.mul_sum,
      Finset.sum_mul, mul_assoc] using hpos

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

/-- One source SPD elimination step, with all data needed by the recursive
    Eq. (13.24) proof.  Lemma 13.9 bounds the whole multiplier block-column;
    the SPD Schur facts and Lemma 13.10's two operator halves propagate the
    common `A` and `A⁻¹` radii to the tail. -/
theorem higham13_spd_first_step_source_certificates
    {m r : ℕ} (hr : 0 < r)
    (A : Fin (m + 1) → Fin (m + 1) → Matrix (Fin r) (Fin r) ℝ)
    (normA normAinv : ℝ) (hNormA : 0 ≤ normA) (hNormAinv : 0 ≤ normAinv)
    (hSPD : IsSymPosDef ((m + 1) * r) (blockMatrixFlatFin A))
    (hAop : finiteOpNorm2Le (blockMatrixFlatFin A) normA)
    (hAinvop : finiteOpNorm2Le
      (nonsingInv ((m + 1) * r) (blockMatrixFlatFin A)) normAinv) :
    IsInverse r (A 0 0) (nonsingInv r (A 0 0)) ∧
      IsSymPosDef (m * r)
        (blockMatrixFlatFin (blockSchur A (nonsingInv r (A 0 0)))) ∧
      rectOpNorm2Le
        (rectMatMul (blockMatrixFirstSplitA21 A) (nonsingInv r (A 0 0)))
        (Real.sqrt (normA * normAinv)) ∧
      finiteOpNorm2Le
        (blockMatrixFlatFin (blockSchur A (nonsingInv r (A 0 0)))) normA ∧
      finiteOpNorm2Le
        (nonsingInv (m * r)
          (blockMatrixFlatFin (blockSchur A (nonsingInv r (A 0 0)))))
        normAinv := by
  classical
  letI : Nonempty (Fin r) := ⟨⟨0, hr⟩⟩
  let F : Matrix (Fin (r + m * r)) (Fin (r + m * r)) ℝ :=
    blockMatrixFirstSplitFlat A
  let A11 : Matrix (Fin r) (Fin r) ℝ := blockMatrixFirstSplitA11 A
  let A12 : Matrix (Fin r) (Fin (m * r)) ℝ := blockMatrixFirstSplitA12 A
  let A21 : Matrix (Fin (m * r)) (Fin r) ℝ := blockMatrixFirstSplitA21 A
  let A22 : Matrix (Fin (m * r)) (Fin (m * r)) ℝ := blockMatrixFirstSplitA22 A
  let P : Matrix (Fin r) (Fin r) ℝ := nonsingInv r (A 0 0)
  let S : Fin m → Fin m → Matrix (Fin r) (Fin r) ℝ := blockSchur A P
  have hFullGeneral : (Matrix.fromBlocks A11 A12 A21 A22).PosDef := by
    simpa [A11, A12, A21, A22] using
      blockMatrixFirstSplit_fromBlocks_posDef_of_isSymPosDef_flatFin A hSPD
  have hA12 : A12 = A21.transpose := by
    simpa [A11, A12, A21, A22] using
      blockMatrixFirstSplitA12_eq_transpose_A21_of_posDef A
        (by simpa [A11, A12, A21, A22] using hFullGeneral)
  have hFull : (Matrix.fromBlocks A11 A21.transpose A21 A22).PosDef := by
    simpa [hA12] using hFullGeneral
  have hA11pos : A11.PosDef := by
    have hHerm :
        (Matrix.fromBlocks A11 A21.transpose
          (A21.transpose).conjTranspose A22).PosDef := by
      simpa [Matrix.conjTranspose_eq_transpose_of_trivial] using hFull
    exact higham13_spd_leadingBlock_posDef A11 A21.transpose A22 hHerm
  have hA11det : Matrix.det A11 ≠ 0 :=
    ne_of_gt (Matrix.PosDef.det_pos hA11pos)
  have hA00 : A11 = A 0 0 := rfl
  have hPInv : IsInverse r (A 0 0) P := by
    simpa [P, hA00] using isInverse_nonsingInv_of_det_ne_zero r A11 hA11det
  have hFpos : Matrix.PosDef (F : Matrix (Fin (r + m * r)) (Fin (r + m * r)) ℝ) := by
    have hUniform := isSymPosDef_to_matrix_posDef (blockMatrixFlatFin A) hSPD
    change Matrix.PosDef (blockMatrixFirstSplitFlat A)
    rw [blockMatrixFirstSplitFlat_eq_blockMatrixFlatFin_reindex]
    exact matrix_posDef_submatrix_of_injective hUniform
      blockMatrixFirstSplitToFlatFinEquiv
      blockMatrixFirstSplitToFlatFinEquiv.injective
  have hFspd : IsSymPosDef (r + m * r) F :=
    matrix_posDef_to_isSymPosDef F hFpos
  have hPartition := blockMatrixFirstSplit_fromBlocks_eq A
  have hA11block : A11 = fun i j : Fin r =>
      F (finSumFinEquiv (Sum.inl i : Fin r ⊕ Fin (m * r)))
        (finSumFinEquiv (Sum.inl j : Fin r ⊕ Fin (m * r))) := by
    ext i j
    have h := congr_fun (congr_fun hPartition (Sum.inl i)) (Sum.inl j)
    simpa [F, A11, A12, A21, A22, Matrix.fromBlocks] using h.symm
  have hA12block : A21.transpose = fun (i : Fin r) (j : Fin (m * r)) =>
      F (finSumFinEquiv (Sum.inl i : Fin r ⊕ Fin (m * r)))
        (finSumFinEquiv (Sum.inr j : Fin r ⊕ Fin (m * r))) := by
    ext i j
    have h := congr_fun (congr_fun hPartition (Sum.inl i)) (Sum.inr j)
    simpa [F, A11, A12, A21, A22, Matrix.fromBlocks, hA12] using h.symm
  have hA21block : A21 = fun (i : Fin (m * r)) (j : Fin r) =>
      F (finSumFinEquiv (Sum.inr i : Fin r ⊕ Fin (m * r)))
        (finSumFinEquiv (Sum.inl j : Fin r ⊕ Fin (m * r))) := by
    ext i j
    have h := congr_fun (congr_fun hPartition (Sum.inr i)) (Sum.inl j)
    simpa [F, A11, A12, A21, A22, Matrix.fromBlocks] using h.symm
  have hA22block : A22 = fun i j : Fin (m * r) =>
      F (finSumFinEquiv (Sum.inr i : Fin r ⊕ Fin (m * r)))
        (finSumFinEquiv (Sum.inr j : Fin r ⊕ Fin (m * r))) := by
    ext i j
    have h := congr_fun (congr_fun hPartition (Sum.inr i)) (Sum.inr j)
    simpa [F, A11, A12, A21, A22, Matrix.fromBlocks] using h.symm
  have hFirstOp : finiteOpNorm2Le F normA := by
    simpa [F] using
      finiteOpNorm2Le_blockMatrixFirstSplitFlat_of_blockMatrixFlatFin A hAop
  letI : Invertible (F : Matrix (Fin (r + m * r)) (Fin (r + m * r)) ℝ) :=
    hFpos.isUnit.invertible
  have hFinvExact : finiteOpNorm2Le (nonsingInv (r + m * r) F)
      (opNorm2 (nonsingInv ((m + 1) * r) (blockMatrixFlatFin A))) := by
    have hInvOf := finiteOpNorm2Le_invOf_reindex_equiv_nonsingInv
      (e := blockMatrixFirstSplitToFlatFinEquiv)
      (blockMatrixFlatFin A) (F : Matrix (Fin (r + m * r)) (Fin (r + m * r)) ℝ)
      (by simpa [F] using blockMatrixFirstSplitFlat_eq_blockMatrixFlatFin_reindex A)
    have hRight : IsRightInverse (r + m * r) F
        (⅟F : Matrix (Fin (r + m * r)) (Fin (r + m * r)) ℝ) :=
      isRightInverse_of_eq_invOf F (⅟F) rfl
    have heq := nonsingInv_eq_of_isRightInverse F _ hRight
    simpa [heq] using hInvOf
  have hInvRadius :
      opNorm2 (nonsingInv ((m + 1) * r) (blockMatrixFlatFin A)) ≤ normAinv :=
    opNorm2_le_of_finiteOpNorm2Le _ hNormAinv hAinvop
  have hFinvOp : finiteOpNorm2Le (nonsingInv (r + m * r) F) normAinv :=
    finiteOpNorm2Le_mono _ hInvRadius hFinvExact
  have hFRadius : opNorm2 F ≤ normA :=
    opNorm2_le_of_finiteOpNorm2Le F hNormA hFirstOp
  have hFinvRadius : opNorm2 (nonsingInv (r + m * r) F) ≤ normAinv :=
    opNorm2_le_of_finiteOpNorm2Le _ hNormAinv hFinvOp
  have hkappa : kappa2 F (nonsingInv (r + m * r) F) ≤ normA * normAinv := by
    change opNorm2 F * opNorm2 (nonsingInv (r + m * r) F) ≤ normA * normAinv
    exact mul_le_mul hFRadius hFinvRadius
      (opNorm2_nonneg _) hNormA
  have hmultExact : rectOpNorm2Le
      (rectMatMul A21 (nonsingInv r A11))
      (Real.sqrt (kappa2 F (nonsingInv (r + m * r) F))) :=
    by
      have h :=
        higham13_lemma13_9_cholesky_route_rectOpNorm2Le_from_spd_leading_nonsingInv_kappa2
          F A22 A21 hA22block hA21block hFspd
      rw [← hA11block] at h
      exact h
  have hmult : rectOpNorm2Le (rectMatMul A21 P)
      (Real.sqrt (normA * normAinv)) := by
    have hsqrt := Real.sqrt_le_sqrt hkappa
    exact rectOpNorm2Le_mono hsqrt
      (by simpa [P, A11, hA00] using hmultExact)
  have hPeq : P = A11⁻¹ := by rfl
  have hSeq : blockMatrixFlatFin S =
      A22 - A21 * A11⁻¹ * A21.transpose := by
    have hschur := blockMatrixFirstSplit_schur_eq_blockMatrixFlatFin_blockSchur A P
    simpa [S, A12, A21, A22, P, hA12, hPeq] using hschur.symm
  have hSpos : Matrix.PosDef (blockMatrixFlatFin S) := by
    rw [hSeq]
    exact higham13_spd_schurComplement_source_posDef A11 A21 A22 hFull
  have hSspd : IsSymPosDef (m * r) (blockMatrixFlatFin S) :=
    matrix_posDef_to_isSymPosDef _ hSpos
  have hSumOp : finiteOpNorm2Le
      (fun i j : Fin r ⊕ Fin (m * r) =>
        (Matrix.fromBlocks A11 A21.transpose A21 A22) i j) normA := by
    have hRe := finiteOpNorm2Le_reindex_equiv
      (finSumFinEquiv : (Fin r ⊕ Fin (m * r)) ≃ Fin (r + m * r)) F hFirstOp
    have heq : (fun i j : Fin r ⊕ Fin (m * r) =>
        F (finSumFinEquiv i) (finSumFinEquiv j)) =
        fun i j => (Matrix.fromBlocks A11 A21.transpose A21 A22) i j := by
      simpa [F, A11, A12, A21, A22, hA12] using hPartition
    simpa [heq] using hRe
  have hSop : finiteOpNorm2Le (blockMatrixFlatFin S) normA := by
    cases m with
    | zero =>
        apply finiteOpNorm2Le_of_finiteFrobNormSq_le_sq _ hNormA
        have hempty : (Finset.univ : Finset (Fin (0 * r))) = ∅ := by
          apply Finset.eq_empty_iff_forall_notMem.mpr
          intro i _hi
          exact (Nat.not_lt_zero i.val) (by simpa using i.isLt)
        unfold finiteFrobNormSq
        rw [hempty]
        positivity
    | succ m =>
        haveI : Nonempty (Fin ((m + 1) * r)) :=
          ⟨⟨0, Nat.mul_pos (Nat.succ_pos m) hr⟩⟩
        have h := higham13_lemma13_10_schur_opNorm2Le_of_full_operator_bound
          A11 A21 A22 hFull hSumOp
        simpa [hSeq] using h
  have hSinvExact : finiteOpNorm2Le
      (nonsingInv (m * r) (blockMatrixFlatFin S))
      (opNorm2 (nonsingInv (r + m * r) F)) := by
    have h := higham13_problem13_4_Sinv_finiteOpNorm2Le_from_source_posDef_block_inverse
      F A11 A21 A22 hFull hA11block hA12block hA21block hA22block
    rw [← hSeq] at h
    simpa [nonsingInv] using h
  have hSinv : finiteOpNorm2Le
      (nonsingInv (m * r) (blockMatrixFlatFin S)) normAinv :=
    finiteOpNorm2Le_mono _ hFinvRadius hSinvExact
  simpa [P, S, A21] using ⟨hPInv, hSspd, hmult, hSop, hSinv⟩

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

/-- Recursive source-facing SPD factor certificate for Algorithm 13.3.

    From SPD and operator certificates for the original matrix and its
    canonical inverse, this constructs every active pivot, the concrete block
    LU factors, and the two global bounds used in equation (13.24):
    `||L||₂ ≤ 1 + m sqrt(normA*normAinv)` and
    `||U||₂ ≤ sqrt(m) normA`. -/
theorem higham13_algorithm13_3_spd_factor_norm_certificates
    {r : ℕ} (hr : 0 < r) :
    ∀ {m : ℕ}
      (A : Fin m → Fin m → Matrix (Fin r) (Fin r) ℝ)
      (normA normAinv : ℝ),
      0 ≤ normA → 0 ≤ normAinv →
      IsSymPosDef (m * r) (blockMatrixFlatFin A) →
      finiteOpNorm2Le (blockMatrixFlatFin A) normA →
      finiteOpNorm2Le (nonsingInv (m * r) (blockMatrixFlatFin A)) normAinv →
      ∃ pivotInv : ℕ → Matrix (Fin r) (Fin r) ℝ,
        (∀ k : ℕ, ∀ hk : k < m,
          IsRightInverse r
            (higham13_algorithm13_3_schurStageMatrixBlock A pivotInv k
              ⟨k, hk⟩ ⟨k, hk⟩)
            (pivotInv k)) ∧
        BlockLUFactSpec m r A
          (higham13_algorithm13_3_lowerFromMatrixStages A pivotInv)
          (higham13_algorithm13_3_upperFromMatrixStages A pivotInv) ∧
        finiteOpNorm2Le
          (blockMatrixFlatFin
            (higham13_algorithm13_3_lowerFromMatrixStages A pivotInv))
          (1 + (m : ℝ) * Real.sqrt (normA * normAinv)) ∧
        finiteOpNorm2Le
          (blockMatrixFlatFin
            (higham13_algorithm13_3_upperFromMatrixStages A pivotInv))
          (Real.sqrt (m : ℝ) * normA) := by
  intro m
  induction m with
  | zero =>
      intro A normA normAinv hNormA hNormAinv _hSPD _hAop _hAinvop
      let pivotInv : ℕ → Matrix (Fin r) (Fin r) ℝ := fun _ => 0
      have hPivot : ∀ k : ℕ, ∀ hk : k < 0,
          IsRightInverse r
            (higham13_algorithm13_3_schurStageMatrixBlock A pivotInv k
              ⟨k, hk⟩ ⟨k, hk⟩) (pivotInv k) := by
        intro k hk
        omega
      have hFact : BlockLUFactSpec 0 r A
          (higham13_algorithm13_3_lowerFromMatrixStages A pivotInv)
          (higham13_algorithm13_3_upperFromMatrixStages A pivotInv) := by
        exact
          higham13_algorithm13_3_matrixStages_blockLUFactSpec_of_pivot_left_inverse
            A pivotInv (by intro k hk; omega)
      refine ⟨pivotInv, hPivot, hFact, ?_, ?_⟩
      · apply finiteOpNorm2Le_blockMatrixFlatFin_zero
        norm_num
      · apply finiteOpNorm2Le_blockMatrixFlatFin_zero
        simp
  | succ m ih =>
      intro A normA normAinv hNormA hNormAinv hSPD hAop hAinvop
      obtain ⟨hPInv, hSspd, hMult, hSop, hSinvop⟩ :=
        higham13_spd_first_step_source_certificates
          hr A normA normAinv hNormA hNormAinv hSPD hAop hAinvop
      let P : Matrix (Fin r) (Fin r) ℝ := nonsingInv r (A 0 0)
      let S : Fin m → Fin m → Matrix (Fin r) (Fin r) ℝ := blockSchur A P
      rcases ih S normA normAinv hNormA hNormAinv
          (by simpa [S, P] using hSspd)
          (by simpa [S, P] using hSop)
          (by simpa [S, P] using hSinvop) with
        ⟨tailInv, hTailPivot, hTailFact, hTailL, hTailU⟩
      let pivotInv : ℕ → Matrix (Fin r) (Fin r) ℝ
        | 0 => P
        | k + 1 => tailInv k
      have hPivot : ∀ k : ℕ, ∀ hk : k < m + 1,
          IsRightInverse r
            (higham13_algorithm13_3_schurStageMatrixBlock A pivotInv k
              ⟨k, hk⟩ ⟨k, hk⟩) (pivotInv k) := by
        apply
          higham13_algorithm13_3_pivot_right_inverse_of_initial_pivot_and_first_schur_tail_pivot_right_inverse
        · simpa [pivotInv, P, higham13_algorithm13_3_schurStageMatrixBlock,
            higham13_algorithm13_3_schurStageBlock] using hPInv.2
        · intro k hk
          simpa [S, P, pivotInv] using hTailPivot k hk
      have hFact : BlockLUFactSpec (m + 1) r A
          (higham13_algorithm13_3_lowerFromMatrixStages A pivotInv)
          (higham13_algorithm13_3_upperFromMatrixStages A pivotInv) := by
        exact
          higham13_algorithm13_3_matrixStages_blockLUFactSpec_of_pivot_left_inverse
            A pivotInv
            (higham13_algorithm13_3_pivot_left_inverse_of_pivot_right_inverse
              A pivotInv hPivot)
      have hLowerEq :
          higham13_algorithm13_3_lowerFromMatrixStages A pivotInv =
            blockLUOneStepL A P
              (higham13_algorithm13_3_lowerFromMatrixStages S tailInv) := by
        simpa [P, S, pivotInv] using
          higham13_algorithm13_3_lowerFromMatrixStages_succ_eq_blockLUOneStepL
            A pivotInv
      have hUpperEq :
          higham13_algorithm13_3_upperFromMatrixStages A pivotInv =
            blockLUOneStepU A
              (higham13_algorithm13_3_upperFromMatrixStages S tailInv) := by
        simpa [P, S, pivotInv] using
          higham13_algorithm13_3_upperFromMatrixStages_succ_eq_blockLUOneStepU
            A pivotInv
      let c : ℝ := Real.sqrt (normA * normAinv)
      have hc : 0 ≤ c := Real.sqrt_nonneg _
      have hLstep : finiteOpNorm2Le
          (blockMatrixFlatFin
            (blockLUOneStepL A P
              (higham13_algorithm13_3_lowerFromMatrixStages S tailInv)))
          ((1 + (m : ℝ) * c) + c) := by
        apply finiteOpNorm2Le_blockLUOneStepL
          A P (higham13_algorithm13_3_lowerFromMatrixStages S tailInv)
          hc
          (by nlinarith [mul_nonneg (Nat.cast_nonneg m) hc])
        · simpa [P, c, rectMatMul, Matrix.mul_apply] using hMult
        · simpa [S, P, c] using hTailL
      have hL : finiteOpNorm2Le
          (blockMatrixFlatFin
            (higham13_algorithm13_3_lowerFromMatrixStages A pivotInv))
          (1 + ((m + 1 : ℕ) : ℝ) * c) := by
        rw [hLowerEq]
        convert hLstep using 1
        push_cast
        ring
      have hUstep : finiteOpNorm2Le
          (blockMatrixFlatFin
            (blockLUOneStepU A
              (higham13_algorithm13_3_upperFromMatrixStages S tailInv)))
          (Real.sqrt ((m + 1 : ℕ) : ℝ) * normA) :=
        finiteOpNorm2Le_blockLUOneStepU A
          (higham13_algorithm13_3_upperFromMatrixStages S tailInv)
          m hNormA hAop (by simpa [S, P] using hTailU)
      have hU : finiteOpNorm2Le
          (blockMatrixFlatFin
            (higham13_algorithm13_3_upperFromMatrixStages A pivotInv))
          (Real.sqrt ((m + 1 : ℕ) : ℝ) * normA) := by
        rw [hUpperEq]
        exact hUstep
      refine ⟨pivotInv, hPivot, hFact, ?_, ?_⟩
      · simpa [c] using hL
      · exact hU

/-- Higham, Chapter 13, equation (13.24), for the concrete Algorithm 13.3
    factors of an SPD block matrix.  No factor-norm premises are assumed: the
    two bounds and their printed product consequence are derived from SPD via
    Lemmas 13.9--13.10. -/
theorem higham13_eq13_24_algorithm13_3_spd
    {m r : ℕ} (hr : 0 < r)
    (A : Fin m → Fin m → Matrix (Fin r) (Fin r) ℝ)
    (hSPD : IsSymPosDef (m * r) (blockMatrixFlatFin A)) :
    ∃ pivotInv : ℕ → Matrix (Fin r) (Fin r) ℝ,
      (∀ k : ℕ, ∀ hk : k < m,
        IsRightInverse r
          (higham13_algorithm13_3_schurStageMatrixBlock A pivotInv k
            ⟨k, hk⟩ ⟨k, hk⟩)
          (pivotInv k)) ∧
      BlockLUFactSpec m r A
        (higham13_algorithm13_3_lowerFromMatrixStages A pivotInv)
        (higham13_algorithm13_3_upperFromMatrixStages A pivotInv) ∧
      opNorm2
          (blockMatrixFlatFin
            (higham13_algorithm13_3_lowerFromMatrixStages A pivotInv)) ≤
        1 + (m : ℝ) *
          Real.sqrt (kappa2 (blockMatrixFlatFin A)
            (nonsingInv (m * r) (blockMatrixFlatFin A))) ∧
      opNorm2
          (blockMatrixFlatFin
            (higham13_algorithm13_3_upperFromMatrixStages A pivotInv)) ≤
        Real.sqrt (m : ℝ) * opNorm2 (blockMatrixFlatFin A) ∧
      opNorm2
          (blockMatrixFlatFin
            (higham13_algorithm13_3_lowerFromMatrixStages A pivotInv)) *
        opNorm2
          (blockMatrixFlatFin
            (higham13_algorithm13_3_upperFromMatrixStages A pivotInv)) ≤
        Real.sqrt (m : ℝ) *
          (1 + (m : ℝ) *
            Real.sqrt (kappa2 (blockMatrixFlatFin A)
              (nonsingInv (m * r) (blockMatrixFlatFin A)))) *
          opNorm2 (blockMatrixFlatFin A) := by
  let normA : ℝ := opNorm2 (blockMatrixFlatFin A)
  let normAinv : ℝ := opNorm2 (nonsingInv (m * r) (blockMatrixFlatFin A))
  have hAop : finiteOpNorm2Le (blockMatrixFlatFin A) normA :=
    finiteOpNorm2Le_of_opNorm2Le _ (opNorm2Le_opNorm2 _)
  have hAinvop : finiteOpNorm2Le
      (nonsingInv (m * r) (blockMatrixFlatFin A)) normAinv :=
    finiteOpNorm2Le_of_opNorm2Le _ (opNorm2Le_opNorm2 _)
  rcases higham13_algorithm13_3_spd_factor_norm_certificates hr
      A normA normAinv (opNorm2_nonneg _) (opNorm2_nonneg _)
      hSPD hAop hAinvop with
    ⟨pivotInv, hPivot, hFact, hLcert, hUcert⟩
  let Lflat := blockMatrixFlatFin
    (higham13_algorithm13_3_lowerFromMatrixStages A pivotInv)
  let Uflat := blockMatrixFlatFin
    (higham13_algorithm13_3_upperFromMatrixStages A pivotInv)
  let kappaA : ℝ := kappa2 (blockMatrixFlatFin A)
    (nonsingInv (m * r) (blockMatrixFlatFin A))
  have hkappa : kappaA = normA * normAinv := by
    rfl
  have hLradius : 0 ≤ 1 + (m : ℝ) * Real.sqrt kappaA := by
    positivity
  have hUradius : 0 ≤ Real.sqrt (m : ℝ) * normA := by
    exact mul_nonneg (Real.sqrt_nonneg _) (opNorm2_nonneg _)
  have hL : opNorm2 Lflat ≤ 1 + (m : ℝ) * Real.sqrt kappaA := by
    apply opNorm2_le_of_finiteOpNorm2Le Lflat hLradius
    simpa [Lflat, kappaA, hkappa, normA, normAinv] using hLcert
  have hU : opNorm2 Uflat ≤ Real.sqrt (m : ℝ) * normA := by
    apply opNorm2_le_of_finiteOpNorm2Le Uflat hUradius
    simpa [Uflat, normA] using hUcert
  have hProd : opNorm2 Lflat * opNorm2 Uflat ≤
      Real.sqrt (m : ℝ) * (1 + (m : ℝ) * Real.sqrt kappaA) * normA :=
    higham13_eq13_24_spd_scalar_bound
      (opNorm2 Lflat) (opNorm2 Uflat) normA kappaA m
      (opNorm2_nonneg Uflat) hL hU
  refine ⟨pivotInv, hPivot, hFact, ?_, ?_, ?_⟩
  · simpa [Lflat, kappaA] using hL
  · simpa [Uflat, normA] using hU
  · simpa [Lflat, Uflat, kappaA, normA] using hProd

/-- Higham, Chapter 13, equation (13.25), as the exact first-order
    composition of Theorem 13.6 with equation (13.24). -/
theorem higham13_eq13_25_spd_firstOrder_from_eq13_24
    (err u c_n normA normLU kappa : ℝ) (m : ℕ)
    (hm : 0 < m) (hu : 0 ≤ u) (hc : 0 ≤ c_n) (hA : 0 ≤ normA)
    (hErr : FirstOrderLe u (c_n * u * (normA + normLU)) err)
    (hLU : normLU ≤
      Real.sqrt (m : ℝ) * (1 + (m : ℝ) * Real.sqrt kappa) * normA) :
    FirstOrderLe u
      (c_n * Real.sqrt (m : ℝ) * u * normA *
        (2 + (m : ℝ) * Real.sqrt kappa)) err := by
  have hIntermediate := higham13_table13_1_backward_error_from_product_bound
    err u c_n normA normLU
      (Real.sqrt (m : ℝ) * (1 + (m : ℝ) * Real.sqrt kappa))
      hu hc hErr hLU
  apply hIntermediate.mono_leading
  have hmone : (1 : ℝ) ≤ (m : ℝ) := by exact_mod_cast hm
  have hsqrt : 1 ≤ Real.sqrt (m : ℝ) := by
    nlinarith [Real.sqrt_nonneg (m : ℝ),
      Real.sq_sqrt (Nat.cast_nonneg m)]
  have hfactor :
      1 + Real.sqrt (m : ℝ) * (1 + (m : ℝ) * Real.sqrt kappa) ≤
        Real.sqrt (m : ℝ) * (2 + (m : ℝ) * Real.sqrt kappa) := by
    nlinarith [mul_nonneg (Nat.cast_nonneg m) (Real.sqrt_nonneg kappa)]
  have hscale : 0 ≤ c_n * u * normA := by positivity
  calc
    c_n * u *
          ((1 + Real.sqrt (m : ℝ) *
            (1 + (m : ℝ) * Real.sqrt kappa)) * normA)
        = (c_n * u * normA) *
            (1 + Real.sqrt (m : ℝ) *
              (1 + (m : ℝ) * Real.sqrt kappa)) := by ring
    _ ≤ (c_n * u * normA) *
          (Real.sqrt (m : ℝ) *
            (2 + (m : ℝ) * Real.sqrt kappa)) :=
      mul_le_mul_of_nonneg_left hfactor hscale
    _ = c_n * Real.sqrt (m : ℝ) * u * normA *
          (2 + (m : ℝ) * Real.sqrt kappa) := by ring

/-- Higham, Chapter 13, equation (13.25), packaged with the concrete
    Algorithm 13.3 factors supplied by the SPD equation (13.24) theorem.

    The implication's premise is exactly the Theorem 13.6/Table 13.1
    first-order perturbation bound for those factors.  Its conclusion is the
    printed SPD coefficient, with no factor-norm certificate left for the
    caller to provide. -/
theorem higham13_eq13_25_algorithm13_3_spd
    {m r : ℕ} (hm : 0 < m) (hr : 0 < r)
    (A : Fin m → Fin m → Matrix (Fin r) (Fin r) ℝ)
    (hSPD : IsSymPosDef (m * r) (blockMatrixFlatFin A))
    (err u c_n : ℝ) (hu : 0 ≤ u) (hc : 0 ≤ c_n) :
    ∃ pivotInv : ℕ → Matrix (Fin r) (Fin r) ℝ,
      (∀ k : ℕ, ∀ hk : k < m,
        IsRightInverse r
          (higham13_algorithm13_3_schurStageMatrixBlock A pivotInv k
            ⟨k, hk⟩ ⟨k, hk⟩)
          (pivotInv k)) ∧
      BlockLUFactSpec m r A
        (higham13_algorithm13_3_lowerFromMatrixStages A pivotInv)
        (higham13_algorithm13_3_upperFromMatrixStages A pivotInv) ∧
      (FirstOrderLe u
          (c_n * u *
            (opNorm2 (blockMatrixFlatFin A) +
              opNorm2
                  (blockMatrixFlatFin
                    (higham13_algorithm13_3_lowerFromMatrixStages A pivotInv)) *
                opNorm2
                  (blockMatrixFlatFin
                    (higham13_algorithm13_3_upperFromMatrixStages A pivotInv))))
          err →
        FirstOrderLe u
          (c_n * Real.sqrt (m : ℝ) * u * opNorm2 (blockMatrixFlatFin A) *
            (2 + (m : ℝ) *
              Real.sqrt
                (kappa2 (blockMatrixFlatFin A)
                  (nonsingInv (m * r) (blockMatrixFlatFin A)))))
          err) := by
  rcases higham13_eq13_24_algorithm13_3_spd hr A hSPD with
    ⟨pivotInv, hPivot, hFact, _hL, _hU, hProduct⟩
  refine ⟨pivotInv, hPivot, hFact, ?_⟩
  intro hErr
  exact higham13_eq13_25_spd_firstOrder_from_eq13_24
    err u c_n (opNorm2 (blockMatrixFlatFin A))
      (opNorm2
          (blockMatrixFlatFin
            (higham13_algorithm13_3_lowerFromMatrixStages A pivotInv)) *
        opNorm2
          (blockMatrixFlatFin
            (higham13_algorithm13_3_upperFromMatrixStages A pivotInv)))
      (kappa2 (blockMatrixFlatFin A)
        (nonsingInv (m * r) (blockMatrixFlatFin A)))
      m hm hu hc (opNorm2_nonneg _) hErr hProduct

end NumStability
