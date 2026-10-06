/-
Copyright (c) 2026 QED. All rights reserved.
Released under Apache 2.0 license as described in LICENSES/Apache-2.0.txt.
SPDX-License-Identifier: Apache-2.0
See LICENSES/Apache-2.0.txt.
Authors: QED
-/
import NumStability.Algorithms.TestMatrices.Higham28Stewart
import NumStability.Algorithms.TestMatrices.Higham28OrthogonalCoordinates

namespace NumStability

open MeasureTheory
open scoped RealInnerProductSpace

/-! # Block stabilizers and measurable first-row sections of `O(n)` -/

/-- Embed a `d × d` matrix as the lower-right block of
`diag(1, K)`. -/
def orthogonalTailBlockMatrix (d : ℕ)
    (K : Matrix (Fin d) (Fin d) ℝ) :
    Matrix (Fin (d + 1)) (Fin (d + 1)) ℝ :=
  fun i j => Fin.cases (Fin.cases 1 (fun _ => 0) j)
    (fun ii => Fin.cases 0 (fun jj => K ii jj) j) i

@[simp] theorem orthogonalTailBlockMatrix_zero_zero (d : ℕ)
    (K : Matrix (Fin d) (Fin d) ℝ) :
    orthogonalTailBlockMatrix d K 0 0 = 1 := rfl

@[simp] theorem orthogonalTailBlockMatrix_zero_succ (d : ℕ)
    (K : Matrix (Fin d) (Fin d) ℝ) (j : Fin d) :
    orthogonalTailBlockMatrix d K 0 j.succ = 0 := rfl

@[simp] theorem orthogonalTailBlockMatrix_succ_zero (d : ℕ)
    (K : Matrix (Fin d) (Fin d) ℝ) (i : Fin d) :
    orthogonalTailBlockMatrix d K i.succ 0 = 0 := rfl

@[simp] theorem orthogonalTailBlockMatrix_succ_succ (d : ℕ)
    (K : Matrix (Fin d) (Fin d) ℝ) (i j : Fin d) :
    orthogonalTailBlockMatrix d K i.succ j.succ = K i j := rfl

theorem orthogonalTailBlockMatrix_one (d : ℕ) :
    orthogonalTailBlockMatrix d (1 : Matrix (Fin d) (Fin d) ℝ) = 1 := by
  ext i j
  refine Fin.cases ?_ (fun ii => ?_) i
  · refine Fin.cases ?_ (fun jj => ?_) j
    · simp [orthogonalTailBlockMatrix, Matrix.one_apply]
    · have h : (0 : Fin (d + 1)) ≠ jj.succ := by
        intro hEq
        simpa using congrArg Fin.val hEq
      simp [orthogonalTailBlockMatrix, Matrix.one_apply, h]
  · refine Fin.cases ?_ (fun jj => ?_) j
    · have h : ii.succ ≠ (0 : Fin (d + 1)) := by
        intro hEq
        simpa using congrArg Fin.val hEq
      simp [orthogonalTailBlockMatrix, Matrix.one_apply, h]
    · simp [orthogonalTailBlockMatrix, Matrix.one_apply]

theorem orthogonalTailBlockMatrix_mul (d : ℕ)
    (K L : Matrix (Fin d) (Fin d) ℝ) :
    orthogonalTailBlockMatrix d (K * L) =
      orthogonalTailBlockMatrix d K * orthogonalTailBlockMatrix d L := by
  ext i j
  refine Fin.cases ?_ (fun ii => ?_) i <;>
    refine Fin.cases ?_ (fun jj => ?_) j <;>
    simp [orthogonalTailBlockMatrix, Matrix.mul_apply, Fin.sum_univ_succ]

theorem orthogonalTailBlockMatrix_transpose (d : ℕ)
    (K : Matrix (Fin d) (Fin d) ℝ) :
    (orthogonalTailBlockMatrix d K).transpose =
      orthogonalTailBlockMatrix d K.transpose := by
  ext i j
  refine Fin.cases ?_ (fun ii => ?_) i <;>
    refine Fin.cases ?_ (fun jj => ?_) j <;>
    rfl

theorem orthogonalTailBlockMatrix_mem (d : ℕ)
    (K : RealOrthogonalGroup d) :
    orthogonalTailBlockMatrix d
      (K : Matrix (Fin d) (Fin d) ℝ) ∈
      Matrix.orthogonalGroup (Fin (d + 1)) ℝ := by
  rw [Matrix.mem_orthogonalGroup_iff]
  rw [orthogonalTailBlockMatrix_transpose,
    ← orthogonalTailBlockMatrix_mul]
  have hK : (K : Matrix (Fin d) (Fin d) ℝ) *
      (K : Matrix (Fin d) (Fin d) ℝ).transpose = 1 :=
    (Matrix.mem_orthogonalGroup_iff (Fin d) ℝ).mp K.property
  rw [hK, orthogonalTailBlockMatrix_one]

/-- The block embedding `O(d) → O(d+1)` fixing the first coordinate. -/
noncomputable def orthogonalTailEmbedding (d : ℕ) :
    RealOrthogonalGroup d →* RealOrthogonalGroup (d + 1) where
  toFun K := ⟨orthogonalTailBlockMatrix d K,
    orthogonalTailBlockMatrix_mem d K⟩
  map_one' := Subtype.ext (orthogonalTailBlockMatrix_one d)
  map_mul' K L := Subtype.ext (orthogonalTailBlockMatrix_mul d K L)

theorem continuous_orthogonalTailEmbedding (d : ℕ) :
    Continuous (orthogonalTailEmbedding d) := by
  apply Continuous.subtype_mk
  apply continuous_matrix
  intro i j
  refine Fin.cases ?_ (fun ii => ?_) i <;>
    refine Fin.cases ?_ (fun jj => ?_) j
  · exact continuous_const
  · exact continuous_const
  · exact continuous_const
  · exact continuous_subtype_val.matrix_elem ii jj

/-- A matrix in `O(d+1)` fixes the first coordinate on the left exactly when
its first row is the first coordinate row. -/
def OrthogonalFixesFirstRow {d : ℕ}
    (Q : RealOrthogonalGroup (d + 1)) : Prop :=
  ∀ j, (Q : Matrix (Fin (d + 1)) (Fin (d + 1)) ℝ) 0 j =
    if j = 0 then 1 else 0

theorem orthogonalTailEmbedding_fixesFirstRow (d : ℕ)
    (K : RealOrthogonalGroup d) :
    OrthogonalFixesFirstRow (orthogonalTailEmbedding d K) := by
  intro j
  refine Fin.cases ?_ (fun jj => ?_) j
  · simp [OrthogonalFixesFirstRow, orthogonalTailEmbedding]
  · have h : (jj.succ : Fin (d + 1)) ≠ 0 := by
      intro hEq
      simpa using congrArg Fin.val hEq
    simp [OrthogonalFixesFirstRow, orthogonalTailEmbedding, h]

/-- For an orthogonal matrix, fixing the first row forces the first column to
be fixed as well. -/
theorem orthogonalFixesFirstColumn_of_firstRow {d : ℕ}
    (Q : RealOrthogonalGroup (d + 1))
    (hrow : OrthogonalFixesFirstRow Q) :
    ∀ i, (Q : Matrix (Fin (d + 1)) (Fin (d + 1)) ℝ) i 0 =
      if i = 0 then 1 else 0 := by
  intro i
  refine Fin.cases ?_ (fun ii => ?_) i
  · simpa using hrow 0
  · have horth : (Q : Matrix (Fin (d + 1)) (Fin (d + 1)) ℝ) *
        (Q : Matrix (Fin (d + 1)) (Fin (d + 1)) ℝ).transpose = 1 :=
      (Matrix.mem_orthogonalGroup_iff (Fin (d + 1)) ℝ).mp Q.property
    have hentry := congrFun (congrFun horth ii.succ) (0 : Fin (d + 1))
    have hi : ii.succ ≠ (0 : Fin (d + 1)) := by
      intro hEq
      simpa using congrArg Fin.val hEq
    simp only [Matrix.mul_apply, Matrix.transpose_apply] at hentry
    rw [Fin.sum_univ_succ] at hentry
    have h00 : (Q : Matrix (Fin (d + 1)) (Fin (d + 1)) ℝ) 0 0 = 1 := by
      simpa using hrow 0
    have h0succ : ∀ k : Fin d,
        (Q : Matrix (Fin (d + 1)) (Fin (d + 1)) ℝ) 0 k.succ = 0 := by
      intro k
      have hk := hrow k.succ
      have hk0 : (k.succ : Fin (d + 1)) ≠ 0 := by
        intro hEq
        simpa using congrArg Fin.val hEq
      simpa [hk0] using hk
    rw [h00] at hentry
    simp_rw [h0succ] at hentry
    simpa [Matrix.one_apply, hi] using hentry

/-- Lower-right block extraction. -/
def orthogonalTailExtractMatrix {d : ℕ}
    (Q : RealOrthogonalGroup (d + 1)) : Matrix (Fin d) (Fin d) ℝ :=
  fun i j => (Q : Matrix (Fin (d + 1)) (Fin (d + 1)) ℝ) i.succ j.succ

theorem orthogonalTailExtractMatrix_mem {d : ℕ}
    (Q : RealOrthogonalGroup (d + 1))
    (hrow : OrthogonalFixesFirstRow Q) :
    orthogonalTailExtractMatrix Q ∈
      Matrix.orthogonalGroup (Fin d) ℝ := by
  rw [Matrix.mem_orthogonalGroup_iff]
  ext i j
  have horth : (Q : Matrix (Fin (d + 1)) (Fin (d + 1)) ℝ) *
      (Q : Matrix (Fin (d + 1)) (Fin (d + 1)) ℝ).transpose = 1 :=
    (Matrix.mem_orthogonalGroup_iff (Fin (d + 1)) ℝ).mp Q.property
  have hentry := congrFun (congrFun horth i.succ) j.succ
  have hcol := orthogonalFixesFirstColumn_of_firstRow Q hrow
  simp only [Matrix.mul_apply, Matrix.transpose_apply] at hentry ⊢
  rw [Fin.sum_univ_succ] at hentry
  simp [hcol, orthogonalTailExtractMatrix, Matrix.one_apply] at hentry ⊢
  exact hentry

/-- Extract the orthogonal tail block from a matrix fixing its first row. -/
noncomputable def orthogonalTailExtract {d : ℕ}
    (Q : RealOrthogonalGroup (d + 1))
    (hrow : OrthogonalFixesFirstRow Q) : RealOrthogonalGroup d :=
  ⟨orthogonalTailExtractMatrix Q,
    orthogonalTailExtractMatrix_mem Q hrow⟩

theorem orthogonalTailEmbedding_extract {d : ℕ}
    (Q : RealOrthogonalGroup (d + 1))
    (hrow : OrthogonalFixesFirstRow Q) :
    orthogonalTailEmbedding d (orthogonalTailExtract Q hrow) = Q := by
  apply Subtype.ext
  ext i j
  refine Fin.cases ?_ (fun ii => ?_) i
  · refine Fin.cases ?_ (fun jj => ?_) j
    · simpa [orthogonalTailEmbedding] using (hrow 0).symm
    · have h : (jj.succ : Fin (d + 1)) ≠ 0 := by
        intro hEq
        simpa using congrArg Fin.val hEq
      simpa [orthogonalTailEmbedding, h] using (hrow jj.succ).symm
  · refine Fin.cases ?_ (fun jj => ?_) j
    · have hcol := orthogonalFixesFirstColumn_of_firstRow Q hrow ii.succ
      have h : (ii.succ : Fin (d + 1)) ≠ 0 := by
        intro hEq
        simpa using congrArg Fin.val hEq
      simpa [orthogonalTailEmbedding, h] using hcol.symm
    · rfl

/-! ## A measurable section of the first-row quotient -/

/-- The one-coordinate sign correction used in the first Stewart stage. -/
noncomputable def stewartFirstSignMatrix (d : ℕ)
    (x : Fin (d + 1) → ℝ) : Matrix (Fin (d + 1)) (Fin (d + 1)) ℝ :=
  diagMatrix (Fin.cases
    (householderSign (householderAlpha (by omega : 0 < d + 1) x))
    (fun _ => 1))

theorem stewartFirstSignMatrix_orthogonal (d : ℕ)
    (x : Fin (d + 1) → ℝ) :
    IsOrthogonal (d + 1) (stewartFirstSignMatrix d x) := by
  apply IsOrthogonal.diagMatrix_of_sq_eq_one
  intro i
  refine Fin.cases ?_ (fun _ => ?_) i
  · change householderSign
        (householderAlpha (by omega : 0 < d + 1) x) ^ 2 = 1
    unfold householderSign
    split_ifs <;> norm_num
  · norm_num

/-- The full first-stage sign-corrected Householder section. -/
noncomputable def stewartFirstSectionMatrix (d : ℕ)
    (x : Fin (d + 1) → ℝ) : Matrix (Fin (d + 1)) (Fin (d + 1)) ℝ :=
  matMul (d + 1) (stewartFirstSignMatrix d x)
    (householder (d + 1) (householderVector (by omega : 0 < d + 1) x)
      (stewartHouseholderBeta
        (householderVector (by omega : 0 < d + 1) x)))

theorem stewartFirstSectionMatrix_orthogonal (d : ℕ)
    (x : Fin (d + 1) → ℝ) :
    IsOrthogonal (d + 1) (stewartFirstSectionMatrix d x) := by
  exact (stewartFirstSignMatrix_orthogonal d x).mul
    (stewartHouseholder_orthogonal
      (householderVector (by omega : 0 < d + 1) x))

/-- Group-valued first-stage section. -/
noncomputable def stewartFirstSection (d : ℕ)
    (x : Fin (d + 1) → ℝ) : RealOrthogonalGroup (d + 1) :=
  ⟨stewartFirstSectionMatrix d x, by
    rw [Matrix.mem_orthogonalGroup_iff]
    ext i j
    simpa [Matrix.mul_apply, Matrix.transpose_apply, Matrix.one_apply,
      matMul, matTranspose, idMatrix] using
      (stewartFirstSectionMatrix_orthogonal d x).right_inv i j⟩

theorem measurable_stewartFirstSignMatrix (d : ℕ) :
    Measurable (stewartFirstSignMatrix d) := by
  refine measurable_pi_lambda _ fun i => measurable_pi_lambda _ fun j => ?_
  by_cases hij : i = j
  · subst j
    refine Fin.cases ?_ (fun _ => ?_) i
    · simp only [stewartFirstSignMatrix, diagMatrix, ↓reduceIte]
      exact measurable_householderSign.comp
        (measurable_householderAlpha (by omega : 0 < d + 1))
    · simp [stewartFirstSignMatrix, diagMatrix]
  · simp [stewartFirstSignMatrix, diagMatrix, hij]

theorem measurable_stewartFirstSectionMatrix (d : ℕ) :
    Measurable (stewartFirstSectionMatrix d) := by
  unfold stewartFirstSectionMatrix
  exact measurable_matMul_of_measurable
    (measurable_stewartFirstSignMatrix d)
    (measurable_stewartHouseholder.comp
      (measurable_householderVector (by omega : 0 < d + 1)))

theorem measurable_stewartFirstSection (d : ℕ) :
    Measurable (stewartFirstSection d) := by
  exact (measurable_stewartFirstSectionMatrix d).subtype_mk

theorem abs_householderAlpha_eq_euclideanNorm (d : ℕ)
    (x : Fin (d + 1) → ℝ) :
    |householderAlpha (by omega : 0 < d + 1) x| =
      ‖WithLp.toLp 2 x‖ := by
  rw [EuclideanSpace.norm_eq]
  unfold householderAlpha householderScale
  rw [abs_neg, abs_mul, abs_householderSign, one_mul,
    abs_of_nonneg (Real.sqrt_nonneg _)]
  congr 1
  apply Finset.sum_congr rfl
  intro i _
  simp [Real.norm_eq_abs, sq_abs, pow_two]

/-- Away from the null zero input, the first row of the sign-corrected
Householder section is radial normalization of its input. -/
theorem stewartFirstSection_firstRow_of_ne_zero (d : ℕ)
    (x : Fin (d + 1) → ℝ) (hx : x ≠ 0) (j : Fin (d + 1)) :
    (stewartFirstSection d x :
      Matrix (Fin (d + 1)) (Fin (d + 1)) ℝ) 0 j =
      ‖WithLp.toLp 2 x‖⁻¹ * x j := by
  let H : Matrix (Fin (d + 1)) (Fin (d + 1)) ℝ :=
    householder (d + 1)
      (householderVector (by omega : 0 < d + 1) x)
      (stewartHouseholderBeta
        (householderVector (by omega : 0 < d + 1) x))
  let α : ℝ := householderAlpha (by omega : 0 < d + 1) x
  have hHorth : IsOrthogonal (d + 1) H :=
    stewartHouseholder_orthogonal
      (householderVector (by omega : 0 < d + 1) x)
  have hred : ∀ k : Fin (d + 1), Matrix.mulVec H x k =
      if k = 0 then α else 0 := by
    intro k
    exact stewartLocalHouseholder_reduces (by omega : 0 < d + 1) x k
  have hsymM : H.transpose = H := by
    ext i k
    simpa [H, Matrix.transpose_apply, matTranspose] using
      congrFun (congrFun
        (householder_symmetric (d + 1)
          (householderVector (by omega : 0 < d + 1) x)
          (stewartHouseholderBeta
            (householderVector (by omega : 0 < d + 1) x))) i) k
  have hright : H * H.transpose = 1 := by
    ext i k
    simpa [Matrix.mul_apply, Matrix.transpose_apply, Matrix.one_apply,
      matMul, matTranspose, idMatrix] using hHorth.right_inv i k
  have hHH : H * H = 1 := by simpa [hsymM] using hright
  have hxrec : Matrix.mulVec H (Matrix.mulVec H x) = x := by
    rw [Matrix.mulVec_mulVec, hHH, Matrix.one_mulVec]
  have hxj : x j = α * H 0 j := by
    have hj := congrFun hxrec j
    rw [Matrix.mulVec, dotProduct, Fin.sum_univ_succ] at hj
    simp_rw [hred] at hj
    have hsym : H j 0 = H 0 j := by
      dsimp [H]
      simpa [Matrix.transpose_apply] using
        (congrFun (congrFun
          (householder_symmetric (d + 1)
            (householderVector (by omega : 0 < d + 1) x)
            (stewartHouseholderBeta
              (householderVector (by omega : 0 < d + 1) x))) j) 0).symm
    simpa [hsym, mul_comm] using hj.symm
  have hnorm_ne : ‖WithLp.toLp 2 x‖ ≠ 0 := by
    exact norm_ne_zero_iff.mpr (by
      intro h
      apply hx
      simpa using congrArg WithLp.ofLp h)
  have habs : |α| = ‖WithLp.toLp 2 x‖ :=
    abs_householderAlpha_eq_euclideanNorm d x
  have hα : α ≠ 0 := by
    intro h
    apply hnorm_ne
    rw [← habs, h, abs_zero]
  change stewartFirstSectionMatrix d x 0 j =
    ‖WithLp.toLp 2 x‖⁻¹ * x j
  have hsection : stewartFirstSectionMatrix d x 0 j =
      householderSign α * H 0 j := by
    simp [stewartFirstSectionMatrix, stewartFirstSignMatrix, matMul,
      Fin.sum_univ_succ, H, α, diagMatrix]
  rw [hsection]
  rw [← habs, hxj]
  by_cases hneg : α < 0
  · simp [householderSign, hneg, abs_of_neg hneg, hα]
  · have hpos : 0 < α := lt_of_le_of_ne (le_of_not_gt hneg) (Ne.symm hα)
    simp [householderSign, hneg, abs_of_pos hpos, hα]

/-- Restrict the vector section to the unit sphere. -/
noncomputable def stewartSphereSection (d : ℕ)
    (v : OrthogonalSphere (d + 1)) : RealOrthogonalGroup (d + 1) :=
  stewartFirstSection d (WithLp.ofLp (v : EuclideanSpace ℝ (Fin (d + 1))))

theorem measurable_stewartSphereSection (d : ℕ) :
    Measurable (stewartSphereSection d) := by
  apply (measurable_stewartFirstSection d).comp
  exact ((PiLp.continuous_ofLp 2 (fun _ : Fin (d + 1) => ℝ)).comp
    continuous_subtype_val).measurable

theorem orthogonalFirstRow_stewartSphereSection (d : ℕ)
    (v : OrthogonalSphere (d + 1)) :
    orthogonalFirstRow d (stewartSphereSection d v) = v := by
  have hvnorm : ‖(v : EuclideanSpace ℝ (Fin (d + 1)))‖ = 1 := by
    simpa [Metric.mem_sphere, dist_zero_right] using v.property
  have hvne : WithLp.ofLp (v : EuclideanSpace ℝ (Fin (d + 1))) ≠ 0 := by
    intro h
    have : (v : EuclideanSpace ℝ (Fin (d + 1))) = 0 := by
      apply WithLp.ofLp_injective
      simpa using h
    rw [this, norm_zero] at hvnorm
    norm_num at hvnorm
  apply Subtype.ext
  apply WithLp.ofLp_injective
  funext j
  change (stewartFirstSection d
      (WithLp.ofLp (v : EuclideanSpace ℝ (Fin (d + 1)))) :
      Matrix (Fin (d + 1)) (Fin (d + 1)) ℝ) 0 j =
    WithLp.ofLp (v : EuclideanSpace ℝ (Fin (d + 1))) j
  rw [stewartFirstSection_firstRow_of_ne_zero d _ hvne j]
  rw [hvnorm]
  simp

theorem orthogonal_mul_inv_fixesFirstRow_of_firstRow_eq {d : ℕ}
    (Q S : RealOrthogonalGroup (d + 1))
    (hrow : orthogonalFirstRow d Q = orthogonalFirstRow d S) :
    OrthogonalFixesFirstRow (Q * S⁻¹) := by
  have hentries : ∀ k : Fin (d + 1),
      (Q : Matrix (Fin (d + 1)) (Fin (d + 1)) ℝ) 0 k =
        (S : Matrix (Fin (d + 1)) (Fin (d + 1)) ℝ) 0 k := by
    intro k
    have hval := congrArg Subtype.val hrow
    have hlp := congrArg WithLp.ofLp hval
    exact congrFun hlp k
  intro j
  change (((Q : Matrix (Fin (d + 1)) (Fin (d + 1)) ℝ) *
      ((S⁻¹ : RealOrthogonalGroup (d + 1)) :
        Matrix (Fin (d + 1)) (Fin (d + 1)) ℝ)) 0 j) =
    if j = 0 then 1 else 0
  rw [Matrix.mul_apply]
  change (∑ k : Fin (d + 1),
      (Q : Matrix (Fin (d + 1)) (Fin (d + 1)) ℝ) 0 k *
        ((S⁻¹ : RealOrthogonalGroup (d + 1)) :
          Matrix (Fin (d + 1)) (Fin (d + 1)) ℝ) k j) =
    if j = 0 then 1 else 0
  calc
    _ = ∑ k : Fin (d + 1),
        (S : Matrix (Fin (d + 1)) (Fin (d + 1)) ℝ) 0 k *
          ((S⁻¹ : RealOrthogonalGroup (d + 1)) :
            Matrix (Fin (d + 1)) (Fin (d + 1)) ℝ) k j := by
      apply Finset.sum_congr rfl
      intro k _
      rw [hentries k]
    _ = ((S * S⁻¹ : RealOrthogonalGroup (d + 1)) :
        Matrix (Fin (d + 1)) (Fin (d + 1)) ℝ) 0 j := rfl
    _ = if j = 0 then 1 else 0 := by
      rw [mul_inv_cancel]
      simp [Matrix.one_apply, eq_comm]

/-- Every orthogonal matrix factors into its lower-right stabilizer block and
the measurable first-row section. -/
theorem orthogonal_firstRow_fiber_factorization (d : ℕ)
    (Q : RealOrthogonalGroup (d + 1)) :
    ∃ K : RealOrthogonalGroup d,
      Q = orthogonalTailEmbedding d K *
        stewartSphereSection d (orthogonalFirstRow d Q) := by
  let S := stewartSphereSection d (orthogonalFirstRow d Q)
  let R := Q * S⁻¹
  have hrowQS : orthogonalFirstRow d Q = orthogonalFirstRow d S := by
    dsimp [S]
    rw [orthogonalFirstRow_stewartSphereSection]
  have hfix : OrthogonalFixesFirstRow R :=
    orthogonal_mul_inv_fixesFirstRow_of_firstRow_eq Q S hrowQS
  let K := orthogonalTailExtract R hfix
  refine ⟨K, ?_⟩
  have hembed : orthogonalTailEmbedding d K = R :=
    orthogonalTailEmbedding_extract R hfix
  rw [hembed]
  dsimp [R]
  rw [mul_assoc, inv_mul_cancel, mul_one]

theorem orthogonalFirstRow_mul_of_fixesFirstRow {d : ℕ}
    (R Q : RealOrthogonalGroup (d + 1))
    (hR : OrthogonalFixesFirstRow R) :
    orthogonalFirstRow d (R * Q) = orthogonalFirstRow d Q := by
  apply Subtype.ext
  apply WithLp.ofLp_injective
  funext j
  change (∑ k : Fin (d + 1),
      (R : Matrix (Fin (d + 1)) (Fin (d + 1)) ℝ) 0 k *
        (Q : Matrix (Fin (d + 1)) (Fin (d + 1)) ℝ) k j) =
    (Q : Matrix (Fin (d + 1)) (Fin (d + 1)) ℝ) 0 j
  rw [Fin.sum_univ_succ]
  have h00 : (R : Matrix (Fin (d + 1)) (Fin (d + 1)) ℝ) 0 0 = 1 := by
    simpa using hR 0
  have h0succ : ∀ k : Fin d,
      (R : Matrix (Fin (d + 1)) (Fin (d + 1)) ℝ) 0 k.succ = 0 := by
    intro k
    have hk := hR k.succ
    have hk0 : (k.succ : Fin (d + 1)) ≠ 0 := by
      intro hEq
      simpa using congrArg Fin.val hEq
    simpa [hk0] using hk
  rw [h00]
  simp_rw [h0succ]
  simp

/-! ## Reconstruction of normalized Haar probability from one sphere fiber -/

/-- Product of a Haar-distributed tail block and a unit-vector section. -/
noncomputable def orthogonalHaarFiberProducer (d : ℕ)
    (p : RealOrthogonalGroup d × OrthogonalSphere (d + 1)) :
    RealOrthogonalGroup (d + 1) :=
  orthogonalTailEmbedding d p.1 * stewartSphereSection d p.2

theorem measurable_orthogonalHaarFiberProducer (d : ℕ) :
    Measurable (orthogonalHaarFiberProducer d) := by
  exact ((continuous_orthogonalTailEmbedding d).measurable.comp measurable_fst).mul
    ((measurable_stewartSphereSection d).comp measurable_snd)

noncomputable def orthogonalHaarFiberMeasure (d : ℕ) :
    Measure (RealOrthogonalGroup (d + 1)) :=
  Measure.map (orthogonalHaarFiberProducer d)
    ((normalizedOrthogonalHaar d).prod
      (standardGaussianDirectionMeasure d))

instance orthogonalHaarFiberMeasure_isProbabilityMeasure (d : ℕ) :
    IsProbabilityMeasure (orthogonalHaarFiberMeasure d) :=
  Measure.isProbabilityMeasure_map
    (measurable_orthogonalHaarFiberProducer d).aemeasurable

theorem orthogonalFirstRow_orthogonalHaarFiberProducer (d : ℕ)
    (p : RealOrthogonalGroup d × OrthogonalSphere (d + 1)) :
    orthogonalFirstRow d (orthogonalHaarFiberProducer d p) = p.2 := by
  rw [orthogonalHaarFiberProducer,
    orthogonalFirstRow_mul_of_fixesFirstRow _ _
      (orthogonalTailEmbedding_fixesFirstRow d p.1),
    orthogonalFirstRow_stewartSphereSection]

theorem orthogonalHaarFiberMeasure_firstRow (d : ℕ) :
    Measure.map (orthogonalFirstRow d) (orthogonalHaarFiberMeasure d) =
      standardGaussianDirectionMeasure d := by
  rw [orthogonalHaarFiberMeasure,
    Measure.map_map (continuous_orthogonalFirstRow d).measurable
      (measurable_orthogonalHaarFiberProducer d)]
  have hcomp : orthogonalFirstRow d ∘ orthogonalHaarFiberProducer d =
      Prod.snd := by
    funext p
    exact orthogonalFirstRow_orthogonalHaarFiberProducer d p
  rw [hcomp, Measure.map_snd_prod, normalizedOrthogonalHaar_univ, one_smul]

theorem orthogonalHaarFiberMeasure_left_invariant (d : ℕ)
    (H : RealOrthogonalGroup d) :
    Measure.map (fun Q : RealOrthogonalGroup (d + 1) =>
        orthogonalTailEmbedding d H * Q)
        (orthogonalHaarFiberMeasure d) =
      orthogonalHaarFiberMeasure d := by
  let T : RealOrthogonalGroup d × OrthogonalSphere (d + 1) →
      RealOrthogonalGroup d × OrthogonalSphere (d + 1) :=
    Prod.map (fun K => H * K) id
  have hT : Measurable T :=
    ((continuous_const.mul continuous_id).measurable).prodMap measurable_id
  have hprod : Measure.map T
      ((normalizedOrthogonalHaar d).prod
        (standardGaussianDirectionMeasure d)) =
      (normalizedOrthogonalHaar d).prod
        (standardGaussianDirectionMeasure d) := by
    rw [← Measure.map_prod_map]
    · rw [MeasureTheory.map_mul_left_eq_self, Measure.map_id]
    · exact (continuous_const.mul continuous_id).measurable
    · exact measurable_id
  have hleft : Measurable (fun Q : RealOrthogonalGroup (d + 1) =>
      orthogonalTailEmbedding d H * Q) :=
    measurable_const.mul measurable_id
  rw [orthogonalHaarFiberMeasure,
    Measure.map_map hleft
      (measurable_orthogonalHaarFiberProducer d)]
  have hcomp : (fun Q : RealOrthogonalGroup (d + 1) =>
      orthogonalTailEmbedding d H * Q) ∘ orthogonalHaarFiberProducer d =
      orthogonalHaarFiberProducer d ∘ T := by
    funext p
    simp [orthogonalHaarFiberProducer, T, mul_assoc]
  rw [hcomp, ← Measure.map_map
    (measurable_orthogonalHaarFiberProducer d) hT, hprod]

/-- Normalized Haar probability on `O(d+1)` is reconstructed exactly from
normalized Haar on the stabilizer `O(d)` and one invariant sphere direction. -/
theorem orthogonalHaarFiberMeasure_eq_normalizedHaar (d : ℕ) :
    orthogonalHaarFiberMeasure d = normalizedOrthogonalHaar (d + 1) := by
  apply MeasureTheory.measure_eq_of_left_fiber_average
    (orthogonalTailEmbedding d)
    (continuous_orthogonalTailEmbedding d).measurable
    (orthogonalFirstRow d)
    (continuous_orthogonalFirstRow d).measurable
    (stewartSphereSection d)
    (measurable_stewartSphereSection d)
    (orthogonal_firstRow_fiber_factorization d)
    (normalizedOrthogonalHaar d)
  · exact orthogonalHaarFiberMeasure_left_invariant d
  · intro K
    exact MeasureTheory.map_mul_left_eq_self
      (normalizedOrthogonalHaar (d + 1)) (orthogonalTailEmbedding d K)
  · rw [orthogonalHaarFiberMeasure_firstRow,
      orthogonalHaarFirstRowMeasure_eq_standardGaussianDirection]

end NumStability
