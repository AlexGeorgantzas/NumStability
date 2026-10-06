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
import NumStability.Algorithms.LinearSystems.Cholesky.Factorization.Spec
import NumStability.Algorithms.LinearSystems.Cholesky.PositiveSemidefinite.Basic
import NumStability.Algorithms.LinearSystems.Triangular.BackSubstitution
import NumStability.Algorithms.LinearSystems.Triangular.ForwardSubstitution
import NumStability.Analysis.MatrixNorms.EntrywiseAbsolute.Basic
import NumStability.Analysis.MatrixSpectral
import NumStability.Analysis.Rounding
import NumStability.Analysis.SubtractionFold
import NumStability.Analysis.Summation.ErrorBounds
import NumStability.FloatingPoint.Model

/-!
# NumStability Algorithms LinearSystems Cholesky ErrorAnalysis Certificates

Canonical destination for material split out of
`NumStability.Algorithms.HighamChapter10` by wave W03 of the August 2026 repository reorganization.
Declaration names, statements and proofs are unchanged; only the
module they live in has changed. The historical module still
resolves and re-exports this one.
-/

open scoped BigOperators

namespace NumStability

/-- **Certificate diagonal control** (Higham p. 198, the `‖r̂_i‖₂²` step in
the proof of Theorem 10.5): the backward-error certificate bounds each
computed column's squared norm by `(1−ε)⁻¹ a_ii`. -/
theorem chol_cert_colNormSq_le (n : ℕ) (A R : Fin n → Fin n → ℝ)
    (ε : ℝ) (hChol : CholeskyBackwardError n A R ε) (i : Fin n) :
    (1 - ε) * ∑ k : Fin n, R k i ^ 2 ≤ A i i := by
  have hcert := hChol.backward_bound i i
  rw [show ∑ k : Fin n, R k i * R k i = ∑ k : Fin n, R k i ^ 2 from
      Finset.sum_congr rfl fun k _ => by ring,
    show ∑ k : Fin n, |R k i| * |R k i| = ∑ k : Fin n, R k i ^ 2 from
      Finset.sum_congr rfl fun k _ => by
        rw [← abs_mul, abs_of_nonneg (mul_self_nonneg _)]; ring] at hcert
  have := abs_le.mp hcert
  linarith [this.1]

/-- **Scaled entrywise backward-error bound** (Theorem 10.7 induction,
Higham p. 200): the Theorem 10.3 certificate implies the perturbation of
the diagonally scaled matrix is uniformly small entrywise,
`|ΔA_ij| ≤ ε/(1−ε) · √a_ii √a_jj`. -/
theorem chol_cert_scaled_entrywise_le (n : ℕ) (A R : Fin n → Fin n → ℝ)
    (ε : ℝ) (hε0 : 0 ≤ ε) (hε1 : ε < 1)
    (hChol : CholeskyBackwardError n A R ε)
    (hAnn : ∀ l : Fin n, 0 ≤ A l l) (i j : Fin n) :
    |(∑ k : Fin n, R k i * R k j) - A i j| ≤
      ε / (1 - ε) * (Real.sqrt (A i i) * Real.sqrt (A j j)) := by
  have h1ε : (0:ℝ) < 1 - ε := by linarith
  have hcert := hChol.backward_bound i j
  have hcs : ∑ k : Fin n, |R k i| * |R k j| ≤
      Real.sqrt (∑ k : Fin n, R k i ^ 2) *
      Real.sqrt (∑ k : Fin n, R k j ^ 2) := by
    have h := abs_vecInnerProduct_le_vecNorm2_mul
      (fun k => |R k i|) (fun k => |R k j|)
    have hnn : 0 ≤ ∑ k : Fin n, |R k i| * |R k j| :=
      Finset.sum_nonneg fun k _ =>
        mul_nonneg (abs_nonneg _) (abs_nonneg _)
    rw [abs_of_nonneg hnn] at h
    calc ∑ k : Fin n, |R k i| * |R k j|
        ≤ vecNorm2 (fun k => |R k i|) * vecNorm2 (fun k => |R k j|) := h
      _ = Real.sqrt (∑ k : Fin n, R k i ^ 2) *
          Real.sqrt (∑ k : Fin n, R k j ^ 2) := by
          unfold vecNorm2 vecNorm2Sq
          congr 2 <;> exact Finset.sum_congr rfl fun k _ => sq_abs _
  have hcol : ∀ l : Fin n, Real.sqrt (∑ k : Fin n, R k l ^ 2) ≤
      Real.sqrt (A l l) / Real.sqrt (1 - ε) := by
    intro l
    rw [show Real.sqrt (A l l) / Real.sqrt (1 - ε) =
        Real.sqrt (A l l / (1 - ε)) from
      (Real.sqrt_div (hAnn l) _).symm]
    apply Real.sqrt_le_sqrt
    rw [le_div_iff₀ h1ε]
    linarith [chol_cert_colNormSq_le n A R ε hChol l]
  have hmulself : Real.sqrt (1 - ε) * Real.sqrt (1 - ε) = 1 - ε :=
    Real.mul_self_sqrt h1ε.le
  have hsne : Real.sqrt (1 - ε) ≠ 0 := by
    intro h0
    rw [h0, mul_zero] at hmulself
    linarith
  calc |(∑ k : Fin n, R k i * R k j) - A i j|
      ≤ ε * ∑ k : Fin n, |R k i| * |R k j| := hcert
    _ ≤ ε * (Real.sqrt (∑ k : Fin n, R k i ^ 2) *
        Real.sqrt (∑ k : Fin n, R k j ^ 2)) :=
        mul_le_mul_of_nonneg_left hcs hε0
    _ ≤ ε * ((Real.sqrt (A i i) / Real.sqrt (1 - ε)) *
        (Real.sqrt (A j j) / Real.sqrt (1 - ε))) := by
        apply mul_le_mul_of_nonneg_left _ hε0
        exact mul_le_mul (hcol i) (hcol j) (Real.sqrt_nonneg _)
          (div_nonneg (Real.sqrt_nonneg _) (Real.sqrt_nonneg _))
    _ = ε / (1 - ε) * (Real.sqrt (A i i) * Real.sqrt (A j j)) := by
        field_simp
        linear_combination
          (-(ε * Real.sqrt (A i i) * Real.sqrt (A j j))) *
            (Real.sq_sqrt h1ε.le)

/-- **Scaled operator-norm certificate for factor-shaped perturbations**
(Theorem 10.6 assembly, steps 1–2): any perturbation bounded
componentwise by `ε_tot·|R̂ᵀ||R̂|`, with `R̂` carrying the Theorem 10.3
certificate at `γ`, has a `D⁻¹·D⁻¹`-scaled operator-2-norm certificate
`n·ε_tot/(1−γ)` — via the certificate's column-norm control,
Cauchy–Schwarz, and the ones-matrix bound. -/
theorem scaled_opNorm2Le_of_factor_bound (fp : FPModel) (n : ℕ)
    (A R : Fin n → Fin n → ℝ)
    (hAdiag : ∀ i : Fin n, 0 < A i i)
    (hγ1 : gamma fp (n + 1) < 1)
    (hChol : CholeskyBackwardError n A R (gamma fp (n + 1)))
    (M : Fin n → Fin n → ℝ) (εtot : ℝ) (hε : 0 ≤ εtot)
    (hM : ∀ i j : Fin n, |M i j| ≤
      εtot * ∑ k : Fin n, |R k i| * |R k j|) :
    opNorm2Le (fun i j =>
      M i j / (Real.sqrt (A i i) * Real.sqrt (A j j)))
      ((n : ℝ) * (εtot / (1 - gamma fp (n + 1)))) := by
  set γ : ℝ := gamma fp (n + 1) with hγdef
  have h1γ : (0:ℝ) < 1 - γ := by linarith
  -- uniform entrywise bound on the scaled perturbation
  have hcol : ∀ l : Fin n, Real.sqrt (∑ k : Fin n, R k l ^ 2) ≤
      Real.sqrt (A l l) / Real.sqrt (1 - γ) := by
    intro l
    rw [show Real.sqrt (A l l) / Real.sqrt (1 - γ) =
        Real.sqrt (A l l / (1 - γ)) from
      (Real.sqrt_div (hAdiag l).le _).symm]
    apply Real.sqrt_le_sqrt
    rw [le_div_iff₀ h1γ]
    linarith [chol_cert_colNormSq_le n A R γ hChol l]
  have hcs : ∀ i j : Fin n, ∑ k : Fin n, |R k i| * |R k j| ≤
      Real.sqrt (∑ k : Fin n, R k i ^ 2) *
      Real.sqrt (∑ k : Fin n, R k j ^ 2) := by
    intro i j
    have h := abs_vecInnerProduct_le_vecNorm2_mul
      (fun k => |R k i|) (fun k => |R k j|)
    have hnn : 0 ≤ ∑ k : Fin n, |R k i| * |R k j| :=
      Finset.sum_nonneg fun k _ =>
        mul_nonneg (abs_nonneg _) (abs_nonneg _)
    rw [abs_of_nonneg hnn] at h
    calc ∑ k : Fin n, |R k i| * |R k j|
        ≤ vecNorm2 (fun k => |R k i|) * vecNorm2 (fun k => |R k j|) := h
      _ = Real.sqrt (∑ k : Fin n, R k i ^ 2) *
          Real.sqrt (∑ k : Fin n, R k j ^ 2) := by
          unfold vecNorm2 vecNorm2Sq
          congr 2 <;> exact Finset.sum_congr rfl fun k _ => sq_abs _
  have hsqrt1γ : Real.sqrt (1 - γ) * Real.sqrt (1 - γ) = 1 - γ :=
    Real.mul_self_sqrt h1γ.le
  have hentry : ∀ i j : Fin n,
      |M i j / (Real.sqrt (A i i) * Real.sqrt (A j j))| ≤
      εtot / (1 - γ) := by
    intro i j
    have hsi := Real.sqrt_pos.mpr (hAdiag i)
    have hsj := Real.sqrt_pos.mpr (hAdiag j)
    rw [abs_div, abs_of_pos (mul_pos hsi hsj),
      div_le_iff₀ (mul_pos hsi hsj)]
    calc |M i j|
        ≤ εtot * ∑ k : Fin n, |R k i| * |R k j| := hM i j
      _ ≤ εtot * (Real.sqrt (∑ k : Fin n, R k i ^ 2) *
          Real.sqrt (∑ k : Fin n, R k j ^ 2)) :=
          mul_le_mul_of_nonneg_left (hcs i j) hε
      _ ≤ εtot * ((Real.sqrt (A i i) / Real.sqrt (1 - γ)) *
          (Real.sqrt (A j j) / Real.sqrt (1 - γ))) := by
          apply mul_le_mul_of_nonneg_left _ hε
          exact mul_le_mul (hcol i) (hcol j) (Real.sqrt_nonneg _)
            (div_nonneg (Real.sqrt_nonneg _) (Real.sqrt_nonneg _))
      _ = εtot / (1 - γ) * (Real.sqrt (A i i) * Real.sqrt (A j j)) := by
          field_simp
          linear_combination (-εtot) * (Real.sq_sqrt h1γ.le)
  -- entrywise → operator certificate through the ones matrix
  have hones := opNorm2Le_smul n (fun _ _ : Fin n => (1:ℝ)) n
    (εtot / (1 - γ)) (div_nonneg hε h1γ.le)
    (higham10_7_onesMatrix_opNorm2Le n)
  have habs := opNorm2Le_of_abs_le n
    (fun i j => M i j / (Real.sqrt (A i i) * Real.sqrt (A j j)))
    (fun _ _ : Fin n => εtot / (1 - γ) * 1)
    (fun i j => by rw [mul_one]; exact hentry i j)
    (εtot / (1 - γ) * n) hones
  intro x
  calc vecNorm2 (matMulVec n (fun i j =>
      M i j / (Real.sqrt (A i i) * Real.sqrt (A j j))) x)
      ≤ εtot / (1 - γ) * n * vecNorm2 x := habs x
    _ = (n : ℝ) * (εtot / (1 - γ)) * vecNorm2 x := by ring

/-- **Absorption of the solve-chain constant into `γ_{3n+1}`**
    (Higham §10.1, proof of Theorem 10.6):
    `γ_{n+1} + 2γ_n + γ_n² ≤ γ_{3n+1}`, via
    `2γ_n + γ_n² ≤ γ_{2n}` and `γ_{n+1} + γ_{2n} ≤ γ_{3n+1}`. -/
lemma eps_tot_le_gamma_3n1 (fp : FPModel) (n : ℕ)
    (hn3 : gammaValid fp (3 * n + 1)) :
    gamma fp (n + 1) + 2 * gamma fp n + gamma fp n ^ 2 ≤
      gamma fp (3 * n + 1) := by
  have hn1 : gammaValid fp (n + 1) := gammaValid_mono fp (by omega) hn3
  have hstep1 : gamma fp n + gamma fp n + gamma fp n * gamma fp n ≤
      gamma fp (2 * n) := by
    have heq : n + n = 2 * n := by omega
    have h := gamma_sum_le fp n n (gammaValid_mono fp (by omega) hn3)
    rw [heq] at h; exact h
  have hstep2 : gamma fp (n + 1) + gamma fp (2 * n) ≤
      gamma fp (3 * n + 1) := by
    have heq : (n + 1) + 2 * n = 3 * n + 1 := by omega
    have h := gamma_sum_le fp (n + 1) (2 * n) (heq ▸ hn3)
    have hnn1 : 0 ≤ gamma fp (n + 1) := gamma_nonneg fp hn1
    have hnn2 : 0 ≤ gamma fp (2 * n) :=
      gamma_nonneg fp (gammaValid_mono fp (by omega) hn3)
    rw [heq] at h
    linarith [mul_nonneg hnn1 hnn2]
  nlinarith [hstep1, hstep2]

/-- The trailing block of a PSD matrix is PSD (zero-padded test
    vectors through the block split). -/
lemma isPosSemiDef_trailing_block {k m : ℕ}
    (A : Fin (k + m) → Fin (k + m) → ℝ)
    (hPSD : IsPosSemiDef (k + m) A) :
    IsPosSemiDef m
      (fun i j : Fin m => A (Fin.natAdd k i) (Fin.natAdd k j)) := by
  constructor
  · intro i j
    exact hPSD.1 _ _
  · intro x
    have h := hPSD.2 (Fin.append (fun _ : Fin k => (0:ℝ)) x)
    rw [quadForm_append_split A (fun _ : Fin k => (0:ℝ)) x] at h
    simpa using h

/-- **Inverse of an SPD matrix has a nonnegative quadratic form** (Higham
    §10.4, the positive-semidefiniteness fact `hZinv_psd_k` of
    `schur_gram_stage_le` needs on the Schur-complement inverse).  Writing the
    test vector as `u = Z w` (`w = Z⁻¹u`, using the right inverse), the inverse
    quadratic form `uᵀZ⁻¹u = wᵀZw ≥ 0` reduces to positive definiteness of the
    forward matrix `Z`. -/
theorem spd_inv_quadForm_nonneg {n : ℕ} (Z Zinv : Fin n → Fin n → ℝ)
    (hZpd : IsSymPosDef n Z) (hright : IsRightInverse n Z Zinv)
    (u : Fin n → ℝ) :
    0 ≤ ∑ i : Fin n, u i * matMulVec n Zinv u i := by
  have hu : matMulVec n Z (matMulVec n Zinv u) = u :=
    matMulVec_of_isRightInverse Z Zinv hright u
  have huval : ∀ i, u i = ∑ j : Fin n, Z i j * matMulVec n Zinv u j := by
    intro i
    calc u i = matMulVec n Z (matMulVec n Zinv u) i := (congrFun hu i).symm
      _ = ∑ j : Fin n, Z i j * matMulVec n Zinv u j := rfl
  have hquad : (∑ i : Fin n, u i * matMulVec n Zinv u i) =
      ∑ i : Fin n, ∑ j : Fin n,
        matMulVec n Zinv u i * Z i j * matMulVec n Zinv u j := by
    calc (∑ i : Fin n, u i * matMulVec n Zinv u i)
        = ∑ i : Fin n, (∑ j : Fin n, Z i j * matMulVec n Zinv u j)
            * matMulVec n Zinv u i := by
          refine Finset.sum_congr rfl fun i _ => ?_
          rw [huval i]
      _ = ∑ i : Fin n, ∑ j : Fin n,
            matMulVec n Zinv u i * Z i j * matMulVec n Zinv u j := by
          refine Finset.sum_congr rfl fun i _ => ?_
          rw [Finset.sum_mul]
          exact Finset.sum_congr rfl fun j _ => by ring
  rw [hquad]
  by_cases hz : ∃ i, matMulVec n Zinv u i ≠ 0
  · exact (hZpd.2 (matMulVec n Zinv u) hz).le
  · push_neg at hz
    simp only [hz, zero_mul, mul_zero, Finset.sum_const_zero, le_refl]

end NumStability
