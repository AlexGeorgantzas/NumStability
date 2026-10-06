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
import NumStability.Algorithms.LinearSystems.Cholesky.PositiveSemidefinite.PivotedFactorization.Existence
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
import NumStability.Source.Higham.Chapter10.Problem01.PositiveSemidefiniteEntries.Basic
import NumStability.Source.Higham.Chapter10.Problem04.UnpivotedGrowth.Basic
import NumStability.Source.Higham.Chapter10.Problem08.LeadingMinorsCounterexample.Basic
import NumStability.Source.Higham.Chapter10.Section01.Factorization.Basic
import NumStability.Source.Higham.Chapter10.Section02.ErrorAnalysis.Basic
import NumStability.Source.Higham.Chapter10.Section03.PositiveSemidefinite.ConstructiveFactorization.Existence
import NumStability.Source.Higham.Chapter10.Section03.PositiveSemidefinite.Endpoints
import NumStability.Source.Higham.Chapter10.Section03.PositiveSemidefinite.Existence
import NumStability.Source.Higham.Chapter10.Section03.PositiveSemidefinite.QuadraticFormBounds.WeightedNorm
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
# Results

Canonical destination for 11 declaration(s) relocated from
`NumStability.Algorithms.HighamChapter10` during wave R04. Declaration names, kinds, signatures and
visibilities are unchanged; authored-private declarations keep their
names and change only their mangled module owner, per the reviewed
B0008 private-normalization map.
-/

open scoped BigOperators

namespace NumStability

/-- **Theorem 10.9(a)**: every real PSD matrix has an upper-triangular
`R` with nonnegative diagonal and `A = R^T R`. -/
theorem higham10_9_psd_cholesky_existence (n : ℕ)
    (A : Fin n → Fin n → ℝ) (hPSD : IsPosSemiDef n A) :
    ∃ R : Fin n → Fin n → ℝ,
      (∀ i j : Fin n, j.val < i.val → R i j = 0) ∧
      (∀ i : Fin n, 0 ≤ R i i) ∧
      (∀ i j : Fin n, ∑ k : Fin n, R k i * R k j = A i j) :=
  psd_cholesky_existence n A hPSD

/-- **Theorem 10.9(b)**, full-rank/SPD specialization of the pivoted form
with identity permutation. -/
theorem higham10_9_spd_pivoted_cholesky_full_rank (n : ℕ)
    (A : Fin n → Fin n → ℝ) (hSPD : IsSymPosDef n A) :
    ∃ R : Fin n → Fin n → ℝ,
      higham10_9_PivotedCholeskySpec n A R id n :=
  spd_pivoted_cholesky n A hSPD

/-- **Theorem 10.9(b), pivoted PSD existence with the rank identified**:
    every real positive-semidefinite matrix admits a permutation and a
    rank-truncated upper-triangular factor of the displayed form (10.11), and
    the truncation index is exactly the matrix rank.  The greedy constructive
    proof and the two rank inequalities live in `CholeskyPSD`; this theorem is
    the missing chapter-facing assembly. -/
theorem higham10_9_psd_pivoted_cholesky_rank (n : ℕ)
    (A : Fin n → Fin n → ℝ) (hPSD : IsPosSemiDef n A) :
    ∃ (r : ℕ) (σ : Fin n → Fin n) (R : Fin n → Fin n → ℝ),
      r ≤ n ∧
      higham10_9_PivotedCholeskySpec n A R σ r ∧
      (Matrix.of A).rank = r := by
  obtain ⟨r₀, σ, R, hspec₀⟩ := psd_pivoted_cholesky_exists n A hPSD
  let r := min r₀ n
  have hr : r ≤ n := by
    exact Nat.min_le_right r₀ n
  have hspec : higham10_9_PivotedCholeskySpec n A R σ r :=
    higham10_9_pivotedCholeskySpec_min_rank hspec₀
  exact ⟨r, σ, R, hr, hspec, pivoted_spec_rank_eq_r hspec hr⟩

/-- Split an upper-triangular Gram-product sum at its diagonal row. -/
private lemma higham10_9_upper_product_sum_split {n : ℕ}
    (R : Fin n → Fin n → ℝ)
    (hupper : ∀ i j : Fin n, j.val < i.val → R i j = 0)
    (i j : Fin n) :
    (∑ p : Fin n, R p i * R p j) =
      (∑ p ∈ Finset.univ.filter (fun p : Fin n => p.val < i.val),
        R p i * R p j) + R i i * R i j := by
  rw [← Finset.sum_filter_add_sum_filter_not Finset.univ
    (fun p : Fin n => p.val < i.val) (fun p => R p i * R p j)]
  congr 1
  apply Finset.sum_eq_single i
  · intro p hp hpi
    simp only [Finset.mem_filter, Finset.mem_univ, true_and, not_lt] at hp
    have hip : i.val < p.val := by
      have hne : i.val ≠ p.val := fun h => hpi (Fin.ext h.symm)
      omega
    rw [hupper p i hip, zero_mul]
  · simp

/-- **Theorem 10.9(b), uniqueness for the selected permutation.**  Two
    rank-truncated pivoted Cholesky factors with the same permutation and rank
    are equal.  Induction over the positive leading rows first identifies the
    diagonal from the Gram product and positivity, then cancels that pivot to
    identify the rest of the row; all rows at or beyond `r` vanish by the
    displayed block structure. -/
theorem higham10_9_pivoted_cholesky_unique {n : ℕ}
    {A R₁ R₂ : Fin n → Fin n → ℝ} {σ : Fin n → Fin n} {r : ℕ}
    (h₁ : higham10_9_PivotedCholeskySpec n A R₁ σ r)
    (h₂ : higham10_9_PivotedCholeskySpec n A R₂ σ r) :
    R₁ = R₂ := by
  have hrows : ∀ k : ℕ, k < r → ∀ i : Fin n, i.val = k →
      ∀ j : Fin n, R₁ i j = R₂ i j := by
    intro k
    induction k using Nat.strong_induction_on with
    | h k ih =>
      intro hkr i hik
      have hprior : ∀ p : Fin n, p.val < i.val →
          ∀ j : Fin n, R₁ p j = R₂ p j := by
        intro p hpi j
        exact ih p.val (by omega) (by omega) p rfl j
      have hdiag : R₁ i i = R₂ i i := by
        have hp : (∑ p : Fin n, R₁ p i * R₁ p i) =
            ∑ p : Fin n, R₂ p i * R₂ p i := by
          rw [h₁.product_eq i i, h₂.product_eq i i]
        rw [higham10_9_upper_product_sum_split R₁ h₁.R_upper i i,
          higham10_9_upper_product_sum_split R₂ h₂.R_upper i i] at hp
        have hhead :
            (∑ p ∈ Finset.univ.filter (fun p : Fin n => p.val < i.val),
                R₁ p i * R₁ p i) =
              ∑ p ∈ Finset.univ.filter (fun p : Fin n => p.val < i.val),
                R₂ p i * R₂ p i := by
          apply Finset.sum_congr rfl
          intro p hp
          simp only [Finset.mem_filter, Finset.mem_univ, true_and] at hp
          rw [hprior p hp i]
        rw [hhead] at hp
        have hpos₁ := h₁.R_diag_pos i (by omega)
        have hpos₂ := h₂.R_diag_pos i (by omega)
        nlinarith
      intro j
      have hp : (∑ p : Fin n, R₁ p i * R₁ p j) =
          ∑ p : Fin n, R₂ p i * R₂ p j := by
        rw [h₁.product_eq i j, h₂.product_eq i j]
      rw [higham10_9_upper_product_sum_split R₁ h₁.R_upper i j,
        higham10_9_upper_product_sum_split R₂ h₂.R_upper i j] at hp
      have hhead :
          (∑ p ∈ Finset.univ.filter (fun p : Fin n => p.val < i.val),
              R₁ p i * R₁ p j) =
            ∑ p ∈ Finset.univ.filter (fun p : Fin n => p.val < i.val),
              R₂ p i * R₂ p j := by
        apply Finset.sum_congr rfl
        intro p hp
        simp only [Finset.mem_filter, Finset.mem_univ, true_and] at hp
        rw [hprior p hp i, hprior p hp j]
      rw [hhead, hdiag] at hp
      have hmul : R₂ i i * R₁ i j = R₂ i i * R₂ i j := by
        linarith
      exact mul_left_cancel₀ (h₂.R_diag_pos i (by omega)).ne' hmul
  funext i j
  by_cases hi : i.val < r
  · exact hrows i.val hi i rfl j
  · rw [h₁.R_rank_zero i j (by omega), h₂.R_rank_zero i j (by omega)]

/-- **Theorem 10.9(b), full source-facing assembly**: a PSD matrix admits a
    permutation and a unique rank-truncated Cholesky factor of the form
    `(10.11)`, and the truncation index is the matrix rank. -/
theorem higham10_9_psd_pivoted_cholesky_rank_unique (n : ℕ)
    (A : Fin n → Fin n → ℝ) (hPSD : IsPosSemiDef n A) :
    ∃ (r : ℕ) (σ : Fin n → Fin n) (R : Fin n → Fin n → ℝ),
      r ≤ n ∧
      higham10_9_PivotedCholeskySpec n A R σ r ∧
      (Matrix.of A).rank = r ∧
      ∀ R' : Fin n → Fin n → ℝ,
        higham10_9_PivotedCholeskySpec n A R' σ r → R' = R := by
  obtain ⟨r, σ, R, hr, hspec, hrank⟩ :=
    higham10_9_psd_pivoted_cholesky_rank n A hPSD
  exact ⟨r, σ, R, hr, hspec, hrank,
    fun R' hspec' => higham10_9_pivoted_cholesky_unique hspec' hspec⟩

/-- **Lemma 10.12, trace form** (fully computable certificate): the
    solve action `Wv = M A₁₂ v` of a PSD block matrix satisfies
    `‖Wv‖₂² ≤ (tr A₂₂ / λ_min(A₁₁)) ‖v‖₂²` — the `c₂₂` certificate of
    `higham10_12_w_action_norm_bound` discharged by
    `psd_quadForm_le_trace` on the trailing block. -/
theorem higham10_12_w_action_trace_bound {k m : ℕ} (hk : 0 < k)
    (A : Fin (k + m) → Fin (k + m) → ℝ)
    (hPSD : IsPosSemiDef (k + m) A)
    (M : Fin k → Fin k → ℝ)
    (hSym : IsSymmetricFiniteMatrix
      (fun i j : Fin k => A (Fin.castAdd m i) (Fin.castAdd m j)))
    (hMinv : ∀ (w : Fin k → ℝ) (i : Fin k),
      ∑ j : Fin k, A (Fin.castAdd m i) (Fin.castAdd m j) *
        (∑ t : Fin k, M j t * w t) = w i)
    (hlampos : 0 < finiteMinEigenvalue hk
      (fun i j : Fin k => A (Fin.castAdd m i) (Fin.castAdd m j)) hSym)
    (v : Fin m → ℝ) :
    vecNorm2Sq (fun i : Fin k => ∑ t : Fin k, M i t *
      (∑ j : Fin m, A (Fin.castAdd m t) (Fin.natAdd k j) * v j)) ≤
    ((∑ j : Fin m, A (Fin.natAdd k j) (Fin.natAdd k j)) /
        finiteMinEigenvalue hk
          (fun i j : Fin k => A (Fin.castAdd m i) (Fin.castAdd m j))
          hSym)
      * vecNorm2Sq v := by
  refine higham10_12_w_action_norm_bound hk A hPSD M hSym hMinv
    hlampos _ (fun w => ?_) v
  have h := psd_quadForm_le_trace
    (fun i j : Fin m => A (Fin.natAdd k i) (Fin.natAdd k j))
    (isPosSemiDef_trailing_block A hPSD) w
  simpa [vecNorm2Sq] using h

/-- **Spectral bounds for unit-diagonal PSD matrices** (the van der
    Sluis (10.9) route ingredient): the scaled matrix `H = D⁻¹AD⁻¹`
    with `D = diag(√a_ii)` has unit diagonal, and any unit-diagonal PSD
    matrix has `1 ≤ λ_max ≤ n` — the upper bound from the trace, the
    lower from the Rayleigh quotient at a coordinate vector. -/
theorem unit_diag_psd_maxEigenvalue_bounds {n : ℕ} (hn : 0 < n)
    (H : Fin n → Fin n → ℝ) (hPSD : IsPosSemiDef n H)
    (hdiag : ∀ i : Fin n, H i i = 1)
    (hSym : IsSymmetricFiniteMatrix H) :
    1 ≤ finiteMaxEigenvalue hn H hSym ∧
      finiteMaxEigenvalue hn H hSym ≤ (n : ℝ) := by
  constructor
  · -- Rayleigh at a coordinate vector
    set e : Fin n → ℝ := fun k => if k = ⟨0, hn⟩ then 1 else 0 with he
    have hray := finiteMaxEigenvalue_rayleigh hn H hSym e
    have hquad : ∑ i : Fin n, ∑ j : Fin n, e i * H i j * e j =
        H ⟨0, hn⟩ ⟨0, hn⟩ := by
      simp [he, Finset.sum_ite_eq', Finset.mul_sum]
    have hnorm : ∑ i : Fin n, e i ^ 2 = 1 := by
      simp [he, Finset.sum_ite_eq']
    rw [hquad, hnorm, mul_one, hdiag] at hray
    exact hray
  · -- trace bound at the top eigenvector
    obtain ⟨a, ha⟩ := exists_finiteMaxEigenvalue_eq hn H hSym
    have hnorm := finiteVecNorm2Sq_finiteHermitianEigenvector_eq_one
      H hSym a
    have hq :=
      finiteQuadraticForm_finiteHermitianEigenvector_eq_eigenvalue_mul_norm_sq
        H hSym a
    rw [hnorm, mul_one] at hq
    set v : Fin n → ℝ :=
      ⇑((IsSymmetricFiniteMatrix.to_matrix_isHermitian H
        hSym).eigenvectorBasis a) with hv
    have hvsq : ∑ i : Fin n, v i ^ 2 = 1 := by
      have := hnorm
      unfold finiteVecNorm2Sq at this
      exact this
    have hqv : ∑ i : Fin n, ∑ j : Fin n, v i * H i j * v j =
        finiteMaxEigenvalue hn H hSym := by
      rw [← ha, ← hq, finiteQuadraticForm_eq_sum_sum]
    have htr := psd_quadForm_le_trace H hPSD v
    have htrace : ∑ i : Fin n, H i i = (n : ℝ) := by
      simp [hdiag]
    rw [hqv, htrace, hvsq, mul_one] at htr
    exact htr

/-- **Condition-number certificate for the scaled matrix** (van der
    Sluis route, display (10.9) fragment): a unit-diagonal PSD matrix
    with positive smallest eigenvalue has
    `κ₂(H) = λ_max/λ_min ≤ n/λ_min`. -/
theorem higham10_9_unit_diag_cond_bound {n : ℕ} (hn : 0 < n)
    (H : Fin n → Fin n → ℝ) (hPSD : IsPosSemiDef n H)
    (hdiag : ∀ i : Fin n, H i i = 1)
    (hSym : IsSymmetricFiniteMatrix H)
    (hmin : 0 < finiteMinEigenvalue hn H hSym) :
    finiteMaxEigenvalue hn H hSym / finiteMinEigenvalue hn H hSym ≤
      (n : ℝ) / finiteMinEigenvalue hn H hSym := by
  have h := (unit_diag_psd_maxEigenvalue_bounds hn H hPSD hdiag
    hSym).2
  gcongr

/-- **Display (10.9) fragment for the concrete scaled matrix**: for SPD
    data (`A` PSD with positive diagonal), the van der Sluis scaling
    `H = D⁻¹AD⁻¹` satisfies `κ₂(H) ≤ n/λ_min(H)`. -/
theorem higham10_9_scaled_cond_bound {n : ℕ} (hn : 0 < n)
    (A : Fin n → Fin n → ℝ) (hPSD : IsPosSemiDef n A)
    (hAdiag : ∀ i : Fin n, 0 < A i i)
    (hSym : IsSymmetricFiniteMatrix
      (fun i l : Fin n => A i l /
        (Real.sqrt (A i i) * Real.sqrt (A l l))))
    (hmin : 0 < finiteMinEigenvalue hn
      (fun i l : Fin n => A i l /
        (Real.sqrt (A i i) * Real.sqrt (A l l))) hSym) :
    finiteMaxEigenvalue hn
        (fun i l : Fin n => A i l /
          (Real.sqrt (A i i) * Real.sqrt (A l l))) hSym /
      finiteMinEigenvalue hn
        (fun i l : Fin n => A i l /
          (Real.sqrt (A i i) * Real.sqrt (A l l))) hSym ≤
    (n : ℝ) / finiteMinEigenvalue hn
      (fun i l : Fin n => A i l /
        (Real.sqrt (A i i) * Real.sqrt (A l l))) hSym :=
  higham10_9_unit_diag_cond_bound hn _
    (scaled_matrix_isPosSemiDef A hPSD hAdiag)
    (fun i => scaled_matrix_unit_diag A hAdiag i) hSym hmin

/-- **van der Sluis / display (10.9)**: the √-scaling is within a
    factor `n` of every diagonal scaling —
    `κ₂(H) ≤ n·κ₂(DAD)` for every positive diagonal `D`, hence
    `κ₂(H) ≤ n·min_D κ₂(DAD)`. `B` names the largest `d_i²a_ii`
    (supplied with its attainment witness). Chain:
    `λ_max(H) ≤ n` (unit diagonal), `λ_min(H) ≥ λ_min(DAD)/B`
    (diagonal congruence `H = E(DAD)E`, `e_i = 1/(d_i√a_ii)`), and
    `B ≤ λ_max(DAD)` (a diagonal Rayleigh value). -/
theorem higham10_9_van_der_sluis {n : ℕ} (hn : 0 < n)
    (A : Fin n → Fin n → ℝ) (hPSD : IsPosSemiDef n A)
    (hAdiag : ∀ i : Fin n, 0 < A i i)
    (d : Fin n → ℝ) (hd : ∀ i : Fin n, 0 < d i)
    (hSymH : IsSymmetricFiniteMatrix
      (fun i l : Fin n => A i l /
        (Real.sqrt (A i i) * Real.sqrt (A l l))))
    (hSymM : IsSymmetricFiniteMatrix
      (fun i j : Fin n => d i * A i j * d j))
    (hminM : 0 < finiteMinEigenvalue hn
      (fun i j : Fin n => d i * A i j * d j) hSymM)
    (B : ℝ) (hB : ∀ i : Fin n, d i ^ 2 * A i i ≤ B)
    (hattain : ∃ k : Fin n, d k ^ 2 * A k k = B) :
    finiteMaxEigenvalue hn
        (fun i l : Fin n => A i l /
          (Real.sqrt (A i i) * Real.sqrt (A l l))) hSymH /
      finiteMinEigenvalue hn
        (fun i l : Fin n => A i l /
          (Real.sqrt (A i i) * Real.sqrt (A l l))) hSymH ≤
    (n : ℝ) * finiteMaxEigenvalue hn
        (fun i j : Fin n => d i * A i j * d j) hSymM /
      finiteMinEigenvalue hn
        (fun i j : Fin n => d i * A i j * d j) hSymM := by
  obtain ⟨k, hk⟩ := hattain
  have hB0 : (0:ℝ) < B := by
    rw [← hk]
    have hdk := hd k
    have hak := hAdiag k
    positivity
  -- B is a Rayleigh value of M
  have hBmax : B ≤ finiteMaxEigenvalue hn
      (fun i j : Fin n => d i * A i j * d j) hSymM := by
    have h := finiteMaxEigenvalue_ge_diag hn
      (fun i j : Fin n => d i * A i j * d j) hSymM k
    have h2 : d k * A k k * d k = B := by rw [← hk]; ring
    calc B = d k * A k k * d k := h2.symm
      _ ≤ _ := h
  -- H is the diagonal congruence of M by e = 1/(d√a)
  have hHM : (fun i j : Fin n =>
      (1 / (d i * Real.sqrt (A i i))) *
        (d i * A i j * d j) *
        (1 / (d j * Real.sqrt (A j j)))) =
      (fun i l : Fin n => A i l /
        (Real.sqrt (A i i) * Real.sqrt (A l l))) := by
    funext i j
    have hi := Real.sqrt_pos.mpr (hAdiag i)
    have hj := Real.sqrt_pos.mpr (hAdiag j)
    have hdi := hd i
    have hdj := hd j
    field_simp
  -- the congruence floor for λ_min(H)
  have hmfloor : ∀ i : Fin n,
      1 / B ≤ (1 / (d i * Real.sqrt (A i i))) ^ 2 := by
    intro i
    have hi := Real.sqrt_pos.mpr (hAdiag i)
    have hdi := hd i
    rw [div_pow, one_pow]
    have hsq : (d i * Real.sqrt (A i i)) ^ 2 = d i ^ 2 * A i i := by
      rw [mul_pow, Real.sq_sqrt (hAdiag i).le]
    rw [hsq]
    have hai := hAdiag i
    have h1 : (0:ℝ) < d i ^ 2 * A i i := by positivity
    exact one_div_le_one_div_of_le h1 (hB i)
  have hSymH' : IsSymmetricFiniteMatrix
      (fun i j : Fin n =>
        (1 / (d i * Real.sqrt (A i i))) *
          (d i * A i j * d j) *
          (1 / (d j * Real.sqrt (A j j)))) := by
    rw [hHM]; exact hSymH
  have hcong := diag_congruence_minEigenvalue_ge hn
    (fun i j : Fin n => d i * A i j * d j) hSymM
    (fun i => 1 / (d i * Real.sqrt (A i i))) (1 / B)
    (one_div_pos.mpr hB0).le hmfloor hSymH' hminM.le
  -- transport across the congruence identity
  have hminH_ge : (1 / B) * finiteMinEigenvalue hn
      (fun i j : Fin n => d i * A i j * d j) hSymM ≤
      finiteMinEigenvalue hn
        (fun i l : Fin n => A i l /
          (Real.sqrt (A i i) * Real.sqrt (A l l))) hSymH := by
    refine hcong.trans_eq ?_
    congr 1
  have hminH0 : 0 < finiteMinEigenvalue hn
      (fun i l : Fin n => A i l /
        (Real.sqrt (A i i) * Real.sqrt (A l l))) hSymH := by
    have : (0:ℝ) < (1 / B) * finiteMinEigenvalue hn
        (fun i j : Fin n => d i * A i j * d j) hSymM :=
      mul_pos (one_div_pos.mpr hB0) hminM
    linarith [hminH_ge]
  -- assemble the condition-number comparison
  have hmaxH : finiteMaxEigenvalue hn
      (fun i l : Fin n => A i l /
        (Real.sqrt (A i i) * Real.sqrt (A l l))) hSymH ≤ (n : ℝ) :=
    (unit_diag_psd_maxEigenvalue_bounds hn _
      (scaled_matrix_isPosSemiDef A hPSD hAdiag)
      (fun i => scaled_matrix_unit_diag A hAdiag i) hSymH).2
  rw [div_le_div_iff₀ hminH0 hminM]
  have h1 : finiteMaxEigenvalue hn
      (fun i l : Fin n => A i l /
        (Real.sqrt (A i i) * Real.sqrt (A l l))) hSymH *
      finiteMinEigenvalue hn
        (fun i j : Fin n => d i * A i j * d j) hSymM ≤
      (n : ℝ) * finiteMinEigenvalue hn
        (fun i j : Fin n => d i * A i j * d j) hSymM :=
    mul_le_mul_of_nonneg_right hmaxH hminM.le
  have h2 : finiteMinEigenvalue hn
      (fun i j : Fin n => d i * A i j * d j) hSymM ≤
      B * finiteMinEigenvalue hn
        (fun i l : Fin n => A i l /
          (Real.sqrt (A i i) * Real.sqrt (A l l))) hSymH := by
    have := mul_le_mul_of_nonneg_left hminH_ge hB0.le
    calc finiteMinEigenvalue hn
          (fun i j : Fin n => d i * A i j * d j) hSymM
        = B * ((1 / B) * finiteMinEigenvalue hn
            (fun i j : Fin n => d i * A i j * d j) hSymM) := by
          field_simp
      _ ≤ B * finiteMinEigenvalue hn
            (fun i l : Fin n => A i l /
              (Real.sqrt (A i i) * Real.sqrt (A l l))) hSymH := this
  have h3 : (n : ℝ) * B ≤ (n : ℝ) *
      finiteMaxEigenvalue hn
        (fun i j : Fin n => d i * A i j * d j) hSymM :=
    mul_le_mul_of_nonneg_left hBmax (Nat.cast_nonneg n)
  have h4 : (n : ℝ) * finiteMinEigenvalue hn
      (fun i j : Fin n => d i * A i j * d j) hSymM ≤
      (n : ℝ) * (B * finiteMinEigenvalue hn
        (fun i l : Fin n => A i l /
          (Real.sqrt (A i i) * Real.sqrt (A l l))) hSymH) :=
    mul_le_mul_of_nonneg_left h2 (Nat.cast_nonneg n)
  have h5 : ((n : ℝ) * B) * finiteMinEigenvalue hn
      (fun i l : Fin n => A i l /
        (Real.sqrt (A i i) * Real.sqrt (A l l))) hSymH ≤
      ((n : ℝ) * finiteMaxEigenvalue hn
        (fun i j : Fin n => d i * A i j * d j) hSymM) *
      finiteMinEigenvalue hn
        (fun i l : Fin n => A i l /
          (Real.sqrt (A i i) * Real.sqrt (A l l))) hSymH :=
    mul_le_mul_of_nonneg_right h3 hminH0.le
  nlinarith [h1, h4, h5]

end NumStability
