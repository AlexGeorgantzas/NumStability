import NumStability.Algorithms.Ch10KahanSharpness

namespace NumStability

open scoped BigOperators Topology

/-!
# Source-facing packaging for Higham Lemma 10.13

This file packages the explicit Kahan solve into the literal Gram family
`A(theta) = R(theta)^T R(theta)`, proves that the identity ordering is a
complete-pivoting ordering of rank `r`, identifies the displayed matrix `W`,
and supplies both norms in Higham's `2,F` sharpness statement.
-/

/-- Embed the rectangular Kahan factor in the square zero-padded Cholesky
factor used by `PivotedCholeskySpec`. -/
noncomputable def higham10KahanFullR (r m : ℕ) (c s : ℝ) :
    Fin (r + m) → Fin (r + m) → ℝ :=
  fun i j => if hi : i.val < r then
    kahanR r (r + m) c s ⟨i.val, hi⟩ j
  else 0

/-- The literal rank-`r` Kahan Gram family from display (10.20). -/
noncomputable def higham10KahanA (r m : ℕ) (c s : ℝ) :
    Fin (r + m) → Fin (r + m) → ℝ :=
  fun i j => ∑ k : Fin (r + m),
    higham10KahanFullR r m c s k i * higham10KahanFullR r m c s k j

theorem higham10KahanFullR_pivotedCholeskySpec
    (r m : ℕ) (c s : ℝ) (hs : 0 < s) :
    PivotedCholeskySpec (r + m)
      (higham10KahanA r m c s) (higham10KahanFullR r m c s) id r := by
  refine
    { perm := Function.bijective_id
      R_upper := ?_
      R_diag_pos := ?_
      R_rank_zero := ?_
      product_eq := ?_ }
  · intro i j hji
    by_cases hi : i.val < r
    · rw [higham10KahanFullR, dif_pos hi]
      exact kahanR_below c s hji
    · simp [higham10KahanFullR, hi]
  · intro i hi
    rw [higham10KahanFullR, dif_pos hi]
    simp only [kahanR]
    exact pow_pos hs _
  · intro i j hi
    simp [higham10KahanFullR, Nat.not_lt.mpr hi]
  · intro i j
    rfl

theorem higham10KahanA_rank
    (r m : ℕ) (c s : ℝ) (hs : 0 < s) :
    (Matrix.of (higham10KahanA r m c s)).rank = r :=
  pivoted_spec_rank_eq_r
    (higham10KahanFullR_pivotedCholeskySpec r m c s hs)
    (Nat.le_add_right r m)

private theorem higham10Kahan_geometric_segment
    (c s : ℝ) (hcs : c ^ 2 + s ^ 2 = 1) (k q : ℕ) :
    ∑ t ∈ Finset.range q, c ^ 2 * s ^ (2 * (k + t)) =
      s ^ (2 * k) - s ^ (2 * (k + q)) := by
  induction q with
  | zero => simp
  | succ q ih =>
    rw [Finset.sum_range_succ, ih]
    have hc : c ^ 2 = 1 - s ^ 2 := by linarith
    have hs : s ^ (2 * (k + (q + 1))) =
        s ^ (2 * (k + q)) * s ^ 2 := by
      rw [show 2 * (k + (q + 1)) = 2 * (k + q) + 2 by ring, pow_add]
    rw [hc, hs]
    ring

/-- The Kahan factor satisfies the full complete-pivoting column-tail
inequality, including the border columns omitted by the square-part equality
lemma. -/
theorem higham10KahanR_tail_le
    (r m : ℕ) (c s : ℝ) (hcs : c ^ 2 + s ^ 2 = 1)
    (k : Fin r) (j : Fin (r + m)) (hkj : k.val ≤ j.val) :
    (∑ i ∈ Finset.univ.filter (fun i : Fin r => k.val ≤ i.val),
      kahanR r (r + m) c s i j ^ 2) ≤
      kahanR r (r + m) c s k ⟨k.val, by omega⟩ ^ 2 := by
  by_cases hj : j.val < r
  · rw [kahanR_tail_eq r (r + m) c s hcs (Nat.le_add_right r m)
      k j hkj hj]
  · have hjr : r ≤ j.val := Nat.le_of_not_gt hj
    have hentry : ∀ i : Fin r,
        kahanR r (r + m) c s i j ^ 2 =
          c ^ 2 * s ^ (2 * i.val) := by
      intro i
      rw [kahanR_above c s (lt_of_lt_of_le i.isLt hjr)]
      rw [mul_pow, neg_sq, ← pow_mul]
      ring
    have hsum :
        (∑ i ∈ Finset.univ.filter (fun i : Fin r => k.val ≤ i.val),
          c ^ 2 * s ^ (2 * i.val)) =
        ∑ t ∈ Finset.Ico 0 (r - k.val),
          c ^ 2 * s ^ (2 * (k.val + t)) := by
      rw [Finset.sum_filter]
      rw [Fin.sum_univ_eq_sum_range
        (fun v => if k.val ≤ v then c ^ 2 * s ^ (2 * v) else 0) r]
      rw [Finset.range_eq_Ico,
        ← Finset.sum_Ico_consecutive _ (Nat.zero_le k.val) k.isLt.le]
      have hzero :
          ∑ v ∈ Finset.Ico 0 k.val,
            (if k.val ≤ v then c ^ 2 * s ^ (2 * v) else 0) = 0 :=
        Finset.sum_eq_zero fun v hv => by
          rw [if_neg (by
            simp only [Finset.mem_Ico] at hv
            omega)]
      rw [hzero, zero_add]
      conv_lhs => rw [Finset.sum_Ico_eq_sum_range]
      conv_rhs => rw [← Finset.range_eq_Ico]
      apply Finset.sum_congr rfl
      intro t ht
      simp only [Finset.mem_range] at ht
      rw [if_pos (by omega)]
    rw [Finset.sum_congr rfl (fun i _ => hentry i), hsum,
      ← Finset.range_eq_Ico,
      higham10Kahan_geometric_segment c s hcs]
    have hdiag :
        kahanR r (r + m) c s k ⟨k.val, by omega⟩ ^ 2 =
          s ^ (2 * k.val) := by
      unfold kahanR
      rw [if_pos rfl, ← pow_mul]
      congr 1
      omega
    rw [hdiag]
    rw [show k.val + (r - k.val) = r by omega]
    have hnonneg : 0 ≤ s ^ (2 * r) := by
      rw [show 2 * r = r + r by omega, pow_add]
      exact mul_self_nonneg _
    exact sub_le_self _ hnonneg

/-- Identity-order complete-pivoting certificate for the square zero-padded
Kahan factor. -/
theorem higham10KahanFullR_tail_le
    (r m : ℕ) (c s : ℝ) (hcs : c ^ 2 + s ^ 2 = 1) :
    ∀ k j : Fin (r + m), k.val ≤ j.val →
      (∑ i ∈ Finset.univ.filter
        (fun i : Fin (r + m) => k.val ≤ i.val),
          higham10KahanFullR r m c s i j ^ 2) ≤
        higham10KahanFullR r m c s k k ^ 2 := by
  intro k j hkj
  by_cases hk : k.val < r
  · let k₀ : Fin r := ⟨k.val, hk⟩
    have hsum :
        (∑ i ∈ Finset.univ.filter
          (fun i : Fin (r + m) => k.val ≤ i.val),
            higham10KahanFullR r m c s i j ^ 2) =
          ∑ i ∈ Finset.univ.filter
            (fun i : Fin r => k₀.val ≤ i.val),
              kahanR r (r + m) c s i j ^ 2 := by
      have hbottom :
          ∑ i : Fin m,
            (if k.val ≤ (Fin.natAdd r i).val then
              higham10KahanFullR r m c s (Fin.natAdd r i) j ^ 2
            else 0) = 0 := by
        apply Finset.sum_eq_zero
        intro i _
        simp [higham10KahanFullR]
      rw [Finset.sum_filter, Fin.sum_univ_add, hbottom, add_zero,
        Finset.sum_filter]
      apply Finset.sum_congr rfl
      intro i _
      simp [k₀, higham10KahanFullR]
    rw [hsum]
    have htail := higham10KahanR_tail_le r m c s hcs k₀ j hkj
    simpa [k₀, higham10KahanFullR, hk] using htail
  · have hkr : r ≤ k.val := Nat.le_of_not_gt hk
    have hsumzero :
        (∑ i ∈ Finset.univ.filter
          (fun i : Fin (r + m) => k.val ≤ i.val),
            higham10KahanFullR r m c s i j ^ 2) = 0 := by
      apply Finset.sum_eq_zero
      intro i hi
      have hki := (Finset.mem_filter.mp hi).2
      simp [higham10KahanFullR, Nat.not_lt.mpr (hkr.trans hki)]
    rw [hsumzero]
    simp [higham10KahanFullR, hk]

/-- Leading triangular block `R₁₁` of the Kahan factor. -/
noncomputable def higham10KahanU (r m : ℕ) (c s : ℝ) :
    Fin r → Fin r → ℝ :=
  fun i j => kahanR r (r + m) c s i
    (higham10KahanLeadCol (r := r) (m := m) j)

/-- Border block `R₁₂` of the Kahan factor. -/
noncomputable def higham10KahanB (r m : ℕ) (c s : ℝ) :
    Fin r → Fin m → ℝ :=
  fun i j => kahanR r (r + m) c s i ⟨r + j.val, by omega⟩

/-- The leading Gram block `A₁₁ = R₁₁ᵀR₁₁`. -/
noncomputable def higham10KahanA11 (r m : ℕ) (c s : ℝ) :
    Fin r → Fin r → ℝ :=
  rectMatMul (finiteTranspose (higham10KahanU r m c s))
    (higham10KahanU r m c s)

/-- The Gram border block `A₁₂ = R₁₁ᵀR₁₂`. -/
noncomputable def higham10KahanA12 (r m : ℕ) (c s : ℝ) :
    Fin r → Fin m → ℝ :=
  rectMatMul (finiteTranspose (higham10KahanU r m c s))
    (higham10KahanB r m c s)

theorem higham10KahanA11_eq_source_block
    (r m : ℕ) (c s : ℝ) (i j : Fin r) :
    higham10KahanA11 r m c s i j =
      higham10KahanA r m c s
        (higham10KahanLeadCol (r := r) (m := m) i)
        (higham10KahanLeadCol (r := r) (m := m) j) := by
  unfold higham10KahanA11 higham10KahanA rectMatMul finiteTranspose
  rw [Fin.sum_univ_add]
  have hzero :
      (∑ q : Fin m,
        higham10KahanFullR r m c s (Fin.natAdd r q)
            (higham10KahanLeadCol (r := r) (m := m) i) *
          higham10KahanFullR r m c s (Fin.natAdd r q)
            (higham10KahanLeadCol (r := r) (m := m) j)) = 0 := by
    apply Finset.sum_eq_zero
    intro q _
    simp [higham10KahanFullR]
  rw [hzero, add_zero]
  apply Finset.sum_congr rfl
  intro q _
  simp [higham10KahanU, higham10KahanFullR,
    higham10KahanLeadCol]

theorem higham10KahanA12_eq_source_block
    (r m : ℕ) (c s : ℝ) (i : Fin r) (j : Fin m) :
    higham10KahanA12 r m c s i j =
      higham10KahanA r m c s
        (higham10KahanLeadCol (r := r) (m := m) i)
        ⟨r + j.val, by omega⟩ := by
  unfold higham10KahanA12 higham10KahanA rectMatMul finiteTranspose
  rw [Fin.sum_univ_add]
  have hzero :
      (∑ q : Fin m,
        higham10KahanFullR r m c s (Fin.natAdd r q)
            (higham10KahanLeadCol (r := r) (m := m) i) *
          higham10KahanFullR r m c s (Fin.natAdd r q)
            ⟨r + j.val, by omega⟩) = 0 := by
    apply Finset.sum_eq_zero
    intro q _
    simp [higham10KahanFullR]
  rw [hzero, add_zero]
  apply Finset.sum_congr rfl
  intro q _
  simp [higham10KahanU, higham10KahanB, higham10KahanFullR,
    higham10KahanLeadCol]

theorem higham10KahanU_mul_W
    (r m : ℕ) (c s : ℝ) :
    rectMatMul (higham10KahanU r m c s) (higham10KahanW r m c) =
      higham10KahanB r m c s := by
  funext i j
  simpa [rectMatMul, higham10KahanU, higham10KahanB] using
    higham10KahanW_solve r m c s i j

theorem higham10KahanA11_mul_W
    (r m : ℕ) (c s : ℝ) :
    rectMatMul (higham10KahanA11 r m c s) (higham10KahanW r m c) =
      higham10KahanA12 r m c s := by
  unfold higham10KahanA11 higham10KahanA12
  rw [rectMatMul_assoc, higham10KahanU_mul_W]

theorem higham10KahanA11_det_isUnit
    (r m : ℕ) (c s : ℝ) (hs : 0 < s) :
    IsUnit (Matrix.of (higham10KahanA11 r m c s)).det := by
  let spec := higham10KahanFullR_pivotedCholeskySpec r m c s hs
  have hlead := pivoted_leading_block_isUnit_det spec
    (Nat.le_add_right r m)
  have hU :
      Matrix.of (higham10KahanU r m c s) =
        Matrix.of (fun i j : Fin r =>
          higham10KahanFullR r m c s
            ⟨i.val, by omega⟩ ⟨j.val, by omega⟩) := by
    ext i j
    change kahanR r (r + m) c s i
        (higham10KahanLeadCol (r := r) (m := m) j) =
      higham10KahanFullR r m c s
        ⟨i.val, by omega⟩ ⟨j.val, by omega⟩
    rw [higham10KahanFullR, dif_pos i.isLt]
    apply congrArg (kahanR r (r + m) c s i)
    apply Fin.ext
    rfl
  have hUdet : IsUnit (Matrix.of (higham10KahanU r m c s)).det := by
    rw [hU]
    exact hlead
  have hA : Matrix.of (higham10KahanA11 r m c s) =
      (Matrix.of (higham10KahanU r m c s)).transpose *
        Matrix.of (higham10KahanU r m c s) := by
    ext i j
    simp [higham10KahanA11, rectMatMul, finiteTranspose,
      Matrix.mul_apply]
  rw [hA, Matrix.det_mul, Matrix.det_transpose]
  exact hUdet.mul hUdet

/-- Literal identification `W = A₁₁⁻¹A₁₂`, using the repository's
Mathlib-backed nonsingular inverse. -/
theorem higham10KahanW_eq_A11_inv_mul_A12
    (r m : ℕ) (c s : ℝ) (hs : 0 < s) :
    higham10KahanW r m c =
      rectMatMul (nonsingInv r (higham10KahanA11 r m c s))
        (higham10KahanA12 r m c s) := by
  let A11 := higham10KahanA11 r m c s
  let A12 := higham10KahanA12 r m c s
  let W := higham10KahanW r m c
  let A11inv := nonsingInv r A11
  have hdet : IsUnit (Matrix.of A11).det := by
    simpa [A11] using higham10KahanA11_det_isUnit r m c s hs
  have hleft : rectMatMul A11inv A11 = idMatrix r := by
    funext i j
    exact isLeftInverse_nonsingInv_of_det_isUnit r A11 hdet i j
  have hnormal : rectMatMul A11 W = A12 := by
    simpa [A11, A12, W] using higham10KahanA11_mul_W r m c s
  calc
    W = rectMatMul (idMatrix r) W := (rectMatMul_id_left W).symm
    _ = rectMatMul (rectMatMul A11inv A11) W := by rw [hleft]
    _ = rectMatMul A11inv (rectMatMul A11 W) :=
      rectMatMul_assoc A11inv A11 W
    _ = rectMatMul A11inv A12 := by rw [hnormal]

private theorem complexMatrixOp2_vecMulVec
    {p q : ℕ} (a : Fin p → ℂ) (b : Fin q → ℂ) :
    complexMatrixOp2
        ((Matrix.vecMulVec a (star b) : Matrix (Fin p) (Fin q) ℂ) :
          CMatrix p q) =
      ‖(WithLp.toLp 2 a : EuclideanSpace ℂ (Fin p))‖ *
        ‖(WithLp.toLp 2 b : EuclideanSpace ℂ (Fin q))‖ := by
  let aE : EuclideanSpace ℂ (Fin p) := WithLp.toLp 2 a
  let bE : EuclideanSpace ℂ (Fin q) := WithLp.toLp 2 b
  have hrank := InnerProductSpace.symm_toEuclideanLin_rankOne aE bE
  rw [complexMatrixOp2, ← Matrix.l2_opNorm_def]
  rw [← hrank, Matrix.l2_opNorm_def]
  rw [LinearEquiv.trans_apply, LinearEquiv.apply_symm_apply]
  have hclm :
      LinearMap.toContinuousLinearMap
          (InnerProductSpace.rankOne ℂ aE bE).toLinearMap =
        InnerProductSpace.rankOne ℂ aE bE := by
    ext z
    rfl
  rw [hclm]
  simp [aE, bE]

theorem higham10KahanW_op2_eq_product
    (r m : ℕ) (c : ℝ) :
    complexMatrixOp2 (realRectToCMatrix (higham10KahanW r m c)) =
      ‖(WithLp.toLp 2
          (fun i : Fin r =>
            ((-c * (1 + c) ^ (r - 1 - i.val) : ℝ) : ℂ)) :
          EuclideanSpace ℂ (Fin r))‖ *
        ‖(WithLp.toLp 2 (fun _ : Fin m => (1 : ℂ)) :
          EuclideanSpace ℂ (Fin m))‖ := by
  let a : Fin r → ℂ := fun i =>
    ((-c * (1 + c) ^ (r - 1 - i.val) : ℝ) : ℂ)
  let b : Fin m → ℂ := fun _ => 1
  have hmatrix :
      realRectToCMatrix (higham10KahanW r m c) =
        ((Matrix.vecMulVec a (star b) : Matrix (Fin r) (Fin m) ℂ) :
          CMatrix r m) := by
    ext i j
    simp [realRectToCMatrix, higham10KahanW, Matrix.vecMulVec, a, b]
  rw [hmatrix, complexMatrixOp2_vecMulVec a b]

theorem higham10KahanW_op2_sq
    (r m : ℕ) (c : ℝ) :
    complexMatrixOp2 (realRectToCMatrix (higham10KahanW r m c)) ^ 2 =
      higham10KahanWFrobSq r m c := by
  rw [higham10KahanW_op2_eq_product, mul_pow,
    EuclideanSpace.norm_sq_eq, EuclideanSpace.norm_sq_eq]
  unfold higham10KahanWFrobSq higham10KahanW
  simp only [Complex.norm_real, Real.norm_eq_abs, sq_abs, norm_one,
    one_pow]
  rw [Finset.sum_const, Finset.card_univ, Fintype.card_fin,
    nsmul_eq_mul]
  rw [Finset.sum_const]
  simp only [Finset.card_univ, Fintype.card_fin]
  ring

theorem higham10KahanWFrobSq_nonneg
    (r m : ℕ) (c : ℝ) :
    0 ≤ higham10KahanWFrobSq r m c := by
  unfold higham10KahanWFrobSq
  exact Finset.sum_nonneg fun j _ =>
    Finset.sum_nonneg fun i _ => sq_nonneg _

theorem higham10KahanW_op2_eq_frobenius
    (r m : ℕ) (c : ℝ) :
    complexMatrixOp2 (realRectToCMatrix (higham10KahanW r m c)) =
      Real.sqrt (higham10KahanWFrobSq r m c) := by
  apply (sq_eq_sq₀
    (complexMatrixOp2_nonneg _)
    (Real.sqrt_nonneg _)).mp
  rw [higham10KahanW_op2_sq,
    Real.sq_sqrt (higham10KahanWFrobSq_nonneg r m c)]

theorem higham10KahanW_complexFrobenius_eq
    (r m : ℕ) (c : ℝ) :
    complexMatrixFrobenius
        (realRectToCMatrix (higham10KahanW r m c)) =
      Real.sqrt (higham10KahanWFrobSq r m c) := by
  unfold complexMatrixFrobenius complexMatrixFrobeniusSq
  congr 1
  unfold higham10KahanWFrobSq higham10KahanW realRectToCMatrix
  rw [Finset.sum_comm]
  apply Finset.sum_congr rfl
  intro j _
  apply Finset.sum_congr rfl
  intro i _
  simp only [Complex.norm_real, Real.norm_eq_abs, sq_abs]

theorem higham10_13_kahan_theta_op2_tendsto (r m : ℕ) :
    Filter.Tendsto
      (fun θ : ℝ => complexMatrixOp2
        (realRectToCMatrix (higham10KahanW r m (Real.cos θ))))
      (nhds 0)
      (nhds (Real.sqrt ((m : ℝ) * (((4 : ℝ) ^ r - 1) / 3)))) := by
  simpa only [higham10KahanW_op2_eq_frobenius] using
    higham10_13_kahan_theta_frobenius_tendsto r m

theorem higham10_13_kahan_theta_complexFrobenius_tendsto (r m : ℕ) :
    Filter.Tendsto
      (fun θ : ℝ => complexMatrixFrobenius
        (realRectToCMatrix (higham10KahanW r m (Real.cos θ))))
      (nhds 0)
      (nhds (Real.sqrt ((m : ℝ) * (((4 : ℝ) ^ r - 1) / 3)))) := by
  simpa only [higham10KahanW_complexFrobenius_eq] using
    higham10_13_kahan_theta_frobenius_tendsto r m

/-- Complete source certificate for the Kahan sharpness family in Lemma
10.13.  `m` is the source's `n-r`. -/
structure Higham10KahanSharpnessSourceCertificate
    (r m : ℕ) (θ : ℝ) : Prop where
  factor : PivotedCholeskySpec (r + m)
    (higham10KahanA r m (Real.cos θ) (Real.sin θ))
    (higham10KahanFullR r m (Real.cos θ) (Real.sin θ)) id r
  rank_eq :
    (Matrix.of
      (higham10KahanA r m (Real.cos θ) (Real.sin θ))).rank = r
  complete_pivot_tail :
    ∀ k j : Fin (r + m), k.val ≤ j.val →
      (∑ i ∈ Finset.univ.filter
        (fun i : Fin (r + m) => k.val ≤ i.val),
          higham10KahanFullR r m (Real.cos θ) (Real.sin θ) i j ^ 2) ≤
        higham10KahanFullR r m (Real.cos θ) (Real.sin θ) k k ^ 2
  w_eq_A11_inv_A12 :
    higham10KahanW r m (Real.cos θ) =
      rectMatMul
        (nonsingInv r
          (higham10KahanA11 r m (Real.cos θ) (Real.sin θ)))
        (higham10KahanA12 r m (Real.cos θ) (Real.sin θ))

theorem Higham10KahanSharpnessSourceCertificate.of_theta
    (r m : ℕ) (θ : ℝ) (hθ0 : 0 < θ) (hθhalf : θ ≤ Real.pi / 2) :
    Higham10KahanSharpnessSourceCertificate r m θ := by
  have hθpi : θ < Real.pi := by
    have hhalfpi : Real.pi / 2 < Real.pi := by nlinarith [Real.pi_pos]
    exact lt_of_le_of_lt hθhalf hhalfpi
  have hs : 0 < Real.sin θ :=
    Real.sin_pos_of_pos_of_lt_pi hθ0 hθpi
  have hcs : Real.cos θ ^ 2 + Real.sin θ ^ 2 = 1 :=
    Real.cos_sq_add_sin_sq θ
  exact
    { factor := higham10KahanFullR_pivotedCholeskySpec
        r m (Real.cos θ) (Real.sin θ) hs
      rank_eq := higham10KahanA_rank
        r m (Real.cos θ) (Real.sin θ) hs
      complete_pivot_tail := higham10KahanFullR_tail_le
        r m (Real.cos θ) (Real.sin θ) hcs
      w_eq_A11_inv_A12 := higham10KahanW_eq_A11_inv_mul_A12
        r m (Real.cos θ) (Real.sin θ) hs }

/-- Literal source-facing Lemma 10.13 sharpness package: the upper bound is
attained in the limit by rank-`r`, identity-complete-pivoted Gram matrices, in
both the operator `2`-norm and Frobenius norm. -/
theorem higham10_13_kahan_source_closed (r m : ℕ) :
    (∀ θ : ℝ, 0 < θ → θ ≤ Real.pi / 2 →
      Higham10KahanSharpnessSourceCertificate r m θ) ∧
    Filter.Tendsto
      (fun θ : ℝ => complexMatrixOp2
        (realRectToCMatrix (higham10KahanW r m (Real.cos θ))))
      (nhds 0)
      (nhds (Real.sqrt ((m : ℝ) * (((4 : ℝ) ^ r - 1) / 3)))) ∧
    Filter.Tendsto
      (fun θ : ℝ => complexMatrixFrobenius
        (realRectToCMatrix (higham10KahanW r m (Real.cos θ))))
      (nhds 0)
      (nhds (Real.sqrt ((m : ℝ) * (((4 : ℝ) ^ r - 1) / 3)))) := by
  exact ⟨fun θ hθ0 hθhalf =>
      Higham10KahanSharpnessSourceCertificate.of_theta r m θ hθ0 hθhalf,
    higham10_13_kahan_theta_op2_tendsto r m,
    higham10_13_kahan_theta_complexFrobenius_tendsto r m⟩

end NumStability
