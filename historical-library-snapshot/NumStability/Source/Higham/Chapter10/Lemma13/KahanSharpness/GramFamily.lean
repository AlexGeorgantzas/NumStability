import Mathlib.Algebra.BigOperators.Field
import Mathlib.Algebra.BigOperators.Group.Finset.Basic
import Mathlib.Algebra.Order.BigOperators.Group.Finset
import Mathlib.Analysis.SpecialFunctions.Pow.Real
import Mathlib.Data.Complex.Basic
import Mathlib.Data.Real.Basic
import Mathlib.Data.Real.Sqrt
import Mathlib.LinearAlgebra.Matrix.Block
import Mathlib.LinearAlgebra.Matrix.NonsingularInverse
import Mathlib.LinearAlgebra.Matrix.Rank
import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Ring
import NumStability.Algorithms.LU.GaussianElimination
import NumStability.Algorithms.LU.GrowthFactor
import NumStability.Algorithms.LU.LUSolve
import NumStability.Algorithms.LinearSystems.Cholesky.PositiveSemidefinite.Basic
import NumStability.Algorithms.LinearSystems.Cholesky.PositiveSemidefinite.KahanMatrix
import NumStability.Algorithms.LinearSystems.Triangular.BackSubstitution
import NumStability.Algorithms.LinearSystems.Triangular.ForwardSubstitution
import NumStability.Analysis.MatrixSpectral
import NumStability.Analysis.Rounding
import NumStability.Analysis.SubtractionFold
import NumStability.Analysis.Summation.ErrorBounds
import NumStability.FloatingPoint.Model
import NumStability.Source.Higham.Chapter09.Problems
import NumStability.Source.Higham.Chapter09.Section01
import NumStability.Source.Higham.Chapter09.Section02
import NumStability.Source.Higham.Chapter09.Section03
import NumStability.Source.Higham.Chapter09.Section04
import NumStability.Source.Higham.Chapter09.Section05
import NumStability.Source.Higham.Chapter09.Section06
import NumStability.Source.Higham.Chapter09.Section08
import NumStability.Source.Higham.Chapter09.Section10
import NumStability.Source.Higham.Chapter09.Section11
import NumStability.Source.Higham.Chapter10.Lemma13.KahanSharpness.Limit
import NumStability.Source.Higham.Chapter10.Section03.PositiveSemidefinite.Existence

/-!
# Chapter10 Lemma13 KahanSharpness GramFamily

Canonical destination for material split out of
`NumStability.Algorithms.Ch10KahanSharpnessSource` by wave W03 of the August 2026 repository reorganization.
Declaration names, statements and proofs are unchanged; only the
module they live in has changed. The historical module still
resolves and re-exports this one.
-/

open scoped BigOperators Topology

namespace NumStability

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

theorem higham10KahanWFrobSq_nonneg
    (r m : ℕ) (c : ℝ) :
    0 ≤ higham10KahanWFrobSq r m c := by
  unfold higham10KahanWFrobSq
  exact Finset.sum_nonneg fun j _ =>
    Finset.sum_nonneg fun i _ => sq_nonneg _

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

end NumStability
