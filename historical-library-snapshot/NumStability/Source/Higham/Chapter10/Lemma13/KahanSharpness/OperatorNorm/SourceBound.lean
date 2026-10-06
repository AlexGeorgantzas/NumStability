import Mathlib.Algebra.BigOperators.Field
import Mathlib.Algebra.BigOperators.Group.Finset.Basic
import Mathlib.Algebra.Order.BigOperators.Group.Finset
import Mathlib.Data.Complex.Basic
import Mathlib.Data.Real.Basic
import Mathlib.Data.Real.Sqrt
import Mathlib.LinearAlgebra.Matrix.Block
import Mathlib.LinearAlgebra.Matrix.NonsingularInverse
import Mathlib.LinearAlgebra.Matrix.Rank
import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Ring
import NumStability.Algorithms.Cholesky.CholeskyDemmel
import NumStability.Algorithms.Cholesky.CholeskyFl
import NumStability.Algorithms.Cholesky.CholeskyNonsym
import NumStability.Algorithms.Cholesky.CholeskySpec
import NumStability.Algorithms.LU.GaussianElimination
import NumStability.Algorithms.LinearSystems.Cholesky.ErrorAnalysis.Certificates
import NumStability.Algorithms.LinearSystems.Cholesky.Perturbation.Basic
import NumStability.Algorithms.LinearSystems.Cholesky.PositiveSemidefinite.Basic
import NumStability.Algorithms.LinearSystems.Cholesky.PositiveSemidefinite.KahanMatrix
import NumStability.Algorithms.LinearSystems.Cholesky.PositiveSemidefinite.KahanTelescope.Identity
import NumStability.Algorithms.LinearSystems.Cholesky.PositiveSemidefinite.ScaledStage
import NumStability.Analysis.MatrixNorms.EntrywiseAbsolute.Basic
import NumStability.Analysis.MatrixNorms.SpectralExtrema.Basic
import NumStability.Analysis.MatrixSpectral
import NumStability.Analysis.Rounding
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
import NumStability.Source.Higham.Chapter10.Equation07.AbsoluteFactorNorm.Endpoints
import NumStability.Source.Higham.Chapter10.Equation29.Mathias.Endpoints
import NumStability.Source.Higham.Chapter10.Equation30.ComplexPositiveDefinite.Endpoints
import NumStability.Source.Higham.Chapter10.Lemma11.PivotSequenceStability.Endpoints
import NumStability.Source.Higham.Chapter10.Lemma13.KahanSharpness.CompletePivotingBound
import NumStability.Source.Higham.Chapter10.Lemma13.KahanSharpness.Endpoints
import NumStability.Source.Higham.Chapter10.Lemma13.KahanSharpness.GramFamily
import NumStability.Source.Higham.Chapter10.Lemma13.KahanSharpness.Limit
import NumStability.Source.Higham.Chapter10.Problem01.PositiveSemidefiniteEntries.Basic
import NumStability.Source.Higham.Chapter10.Problem04.UnpivotedGrowth.Basic
import NumStability.Source.Higham.Chapter10.Problem08.LeadingMinorsCounterexample.Basic
import NumStability.Source.Higham.Chapter10.Section01.Factorization.Basic
import NumStability.Source.Higham.Chapter10.Section02.ErrorAnalysis.Basic
import NumStability.Source.Higham.Chapter10.Section03.PositiveSemidefinite.Endpoints
import NumStability.Source.Higham.Chapter10.Section03.PositiveSemidefinite.Existence
import NumStability.Source.Higham.Chapter10.Section03.PositiveSemidefinite.SchurComplement
import NumStability.Source.Higham.Chapter10.Section03.PositiveSemidefinite.Termination
import NumStability.Source.Higham.Chapter10.Section03.PositiveSemidefinite.WNormBound
import NumStability.Source.Higham.Chapter10.Section04.PositiveDefiniteSymmetricPart.Endpoints
import NumStability.Source.Higham.Chapter10.Theorem06.RoundedCholesky.Endpoints
import NumStability.Source.Higham.Chapter10.Theorem07.FailureVacuity.Endpoints
import NumStability.Source.Higham.Chapter10.Theorem08.ComponentwisePerturbation.Endpoints
import NumStability.Source.Higham.Chapter10.Theorem08.NormwiseDiscrepancy.Endpoints
import NumStability.Source.Higham.Chapter10.Theorem14.CompletePivotedPSD.Endpoints
import NumStability.Source.Higham.Chapter10.Theorem14.CompletePivotedPSD.PsdErrorAnalysis

/-!
# SourceBound

Canonical destination for 10 declaration(s) relocated from
`NumStability.Algorithms.Ch10KahanSharpnessSource` during wave R04. Declaration names, kinds, signatures and
visibilities are unchanged; authored-private declarations keep their
names and change only their mangled module owner, per the reviewed
B0008 private-normalization map.
-/

/-!
# Ch10KahanSharpnessSource (compatibility module)

Historical path, retained so existing imports of `NumStability.Algorithms.Ch10KahanSharpnessSource`
keep resolving. Most of its declarations moved unchanged to the
canonical modules imported above.

The declarations still defined below are private declarations and
their users. Lean mangles a private name to
`_private.<module>.<n>.<name>`, so relocating one renames it and
breaks the frozen declaration graph; anything referring to one must
therefore stay with it. This module is a declaration-bearing facade,
not a pure import shim.
-/

open scoped BigOperators Topology

namespace NumStability

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

theorem higham10KahanW_op2_eq_frobenius
    (r m : ℕ) (c : ℝ) :
    complexMatrixOp2 (realRectToCMatrix (higham10KahanW r m c)) =
      Real.sqrt (higham10KahanWFrobSq r m c) := by
  apply (sq_eq_sq₀
    (complexMatrixOp2_nonneg _)
    (Real.sqrt_nonneg _)).mp
  rw [higham10KahanW_op2_sq,
    Real.sq_sqrt (higham10KahanWFrobSq_nonneg r m c)]

theorem higham10_13_kahan_theta_op2_tendsto (r m : ℕ) :
    Filter.Tendsto
      (fun θ : ℝ => complexMatrixOp2
        (realRectToCMatrix (higham10KahanW r m (Real.cos θ))))
      (nhds 0)
      (nhds (Real.sqrt ((m : ℝ) * (((4 : ℝ) ^ r - 1) / 3)))) := by
  simpa only [higham10KahanW_op2_eq_frobenius] using
    higham10_13_kahan_theta_frobenius_tendsto r m

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
