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
import NumStability.Algorithms.LinearSystems.Cholesky.PositiveSemidefinite.ScaledStage
import NumStability.Analysis.MatrixNorms.EntrywiseAbsolute.Basic
import NumStability.Analysis.MatrixNorms.SpectralExtrema.Basic
import NumStability.Analysis.MatrixNorms.SpectralExtrema.PrincipalSubmatrices.Bounds
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
# StageBounds

Canonical destination for 4 declaration(s) relocated from
`NumStability.Algorithms.HighamChapter10` during wave R04. Declaration names, kinds, signatures and
visibilities are unchanged; authored-private declarations keep their
names and change only their mangled module owner, per the reviewed
B0008 private-normalization map.
-/

open scoped BigOperators

namespace NumStability

/-- **Display (10.21) stage interior mass** (Higham p. 206): under the
    running induction hypothesis, the stage-`j` interior Gram defect
    carries the quadratic-form mass `r·γ_{r+1}/(1−γ_{r+1})` against the
    `A`-diagonal weights, for every stage `j < r` — the Theorem 10.3
    block certificate, the Demmel scaled entrywise bound, and the
    ones-vector Cauchy–Schwarz engine, composed. -/
theorem higham10_21_stage_interior_mass (fp : FPModel) {n : ℕ}
    (A : Fin n → Fin n → ℝ)
    (hsym : ∀ i j : Fin n, A i j = A j i)
    (hAdiag : ∀ i : Fin n, 0 < A i i)
    (hn1 : gammaValid fp (n + 1))
    (hγ1 : gamma fp (n + 1) < 1)
    (r : ℕ) (hrn : r ≤ n)
    (j : Fin n) (hjr : j.val < r)
    (IH : ∀ l : Fin n, l.val < j.val → 0 < fl_cholPivot fp n A l)
    (y : Fin j.val → ℝ) :
    |∑ i : Fin j.val, ∑ l : Fin j.val, y i *
      ((∑ p : Fin j.val,
        fl_cholesky fp n A ⟨p.val, by omega⟩ ⟨i.val, by omega⟩ *
        fl_cholesky fp n A ⟨p.val, by omega⟩ ⟨l.val, by omega⟩) -
        A ⟨i.val, by omega⟩ ⟨l.val, by omega⟩) * y l| ≤
      (r : ℝ) * (gamma fp (r + 1) / (1 - gamma fp (r + 1))) *
      ∑ i : Fin j.val,
        A ⟨i.val, by omega⟩ ⟨i.val, by omega⟩ * y i ^ 2 := by
  -- gamma bookkeeping
  have hrvalid : gammaValid fp (r + 1) :=
    gammaValid_mono fp (by omega) hn1
  have hG0 : 0 ≤ gamma fp (r + 1) := gamma_nonneg fp hrvalid
  have hG1 : gamma fp (r + 1) < 1 :=
    lt_of_le_of_lt (gamma_mono fp (by omega) hn1) hγ1
  have hD : (0:ℝ) < 1 - gamma fp (r + 1) := by linarith
  have hm1valid : gammaValid fp (j.val + 1) :=
    gammaValid_mono fp (by omega) hn1
  have hγm0 : 0 ≤ gamma fp (j.val + 1) := gamma_nonneg fp hm1valid
  have hγmG : gamma fp (j.val + 1) ≤ gamma fp (r + 1) :=
    gamma_mono fp (by omega) hrvalid
  have hγm1 : gamma fp (j.val + 1) < 1 := lt_of_le_of_lt hγmG hG1
  have h1γm : (0:ℝ) < 1 - gamma fp (j.val + 1) := by linarith
  have hu : fp.u < 1 := by
    have h := hn1
    unfold gammaValid at h
    push_cast at h
    nlinarith [mul_nonneg (Nat.cast_nonneg n : (0:ℝ) ≤ (n:ℝ)) fp.u_nonneg]
  -- the stage-j Theorem 10.3 block certificate from the running IH
  set Am : Fin j.val → Fin j.val → ℝ :=
    fun i' l' => A ⟨i'.val, by omega⟩ ⟨l'.val, by omega⟩ with hAm
  have hcert : CholeskyBackwardError j.val Am
      (fl_cholesky fp j.val Am) (gamma fp (j.val + 1)) :=
    fl_cholesky_block_certificate fp j.isLt.le A hsym hu hm1valid IH
  have hloc : ∀ p q : Fin j.val,
      fl_cholesky fp j.val Am p q =
      fl_cholesky fp n A ⟨p.val, by omega⟩ ⟨q.val, by omega⟩ :=
    fun p q => fl_cholesky_leading_principal fp j.isLt.le A p q
  -- Demmel scaled entrywise bound for the stage block, full-run form
  have hentry : ∀ i l : Fin j.val,
      |(∑ p : Fin j.val,
          fl_cholesky fp n A ⟨p.val, by omega⟩ ⟨i.val, by omega⟩ *
          fl_cholesky fp n A ⟨p.val, by omega⟩ ⟨l.val, by omega⟩) -
        A ⟨i.val, by omega⟩ ⟨l.val, by omega⟩| ≤
      gamma fp (j.val + 1) / (1 - gamma fp (j.val + 1)) *
        (Real.sqrt (A ⟨i.val, by omega⟩ ⟨i.val, by omega⟩) *
         Real.sqrt (A ⟨l.val, by omega⟩ ⟨l.val, by omega⟩)) := by
    intro i l
    have h := chol_cert_scaled_entrywise_le j.val Am
      (fl_cholesky fp j.val Am) (gamma fp (j.val + 1)) hγm0 hγm1 hcert
      (fun l' => (hAdiag _).le) i l
    simp only [hloc] at h
    exact h
  -- entrywise bound on the scaled defect, then the quadratic-form engine
  have hc0 : 0 ≤ gamma fp (j.val + 1) / (1 - gamma fp (j.val + 1)) :=
    div_nonneg hγm0 h1γm.le
  have hE : ∀ i l : Fin j.val,
      |((∑ p : Fin j.val,
          fl_cholesky fp n A ⟨p.val, by omega⟩ ⟨i.val, by omega⟩ *
          fl_cholesky fp n A ⟨p.val, by omega⟩ ⟨l.val, by omega⟩) -
          A ⟨i.val, by omega⟩ ⟨l.val, by omega⟩) /
        (Real.sqrt (A ⟨i.val, by omega⟩ ⟨i.val, by omega⟩) *
         Real.sqrt (A ⟨l.val, by omega⟩ ⟨l.val, by omega⟩))| ≤
      gamma fp (j.val + 1) / (1 - gamma fp (j.val + 1)) := by
    intro i l
    have hsi := Real.sqrt_pos.mpr (hAdiag (⟨i.val, by omega⟩ : Fin n))
    have hsl := Real.sqrt_pos.mpr (hAdiag (⟨l.val, by omega⟩ : Fin n))
    rw [abs_div, abs_of_pos (mul_pos hsi hsl),
      div_le_iff₀ (mul_pos hsi hsl)]
    exact hentry i l
  have hquad := quadForm_cert_of_entrywise
    (fun i l : Fin j.val =>
      ((∑ p : Fin j.val,
        fl_cholesky fp n A ⟨p.val, by omega⟩ ⟨i.val, by omega⟩ *
        fl_cholesky fp n A ⟨p.val, by omega⟩ ⟨l.val, by omega⟩) -
        A ⟨i.val, by omega⟩ ⟨l.val, by omega⟩) /
      (Real.sqrt (A ⟨i.val, by omega⟩ ⟨i.val, by omega⟩) *
       Real.sqrt (A ⟨l.val, by omega⟩ ⟨l.val, by omega⟩)))
    (gamma fp (j.val + 1) / (1 - gamma fp (j.val + 1))) hc0 hE
  have hmass := scaled_interior_mass_normwise_quad
    (fun i l : Fin j.val =>
      (∑ p : Fin j.val,
        fl_cholesky fp n A ⟨p.val, by omega⟩ ⟨i.val, by omega⟩ *
        fl_cholesky fp n A ⟨p.val, by omega⟩ ⟨l.val, by omega⟩) -
        A ⟨i.val, by omega⟩ ⟨l.val, by omega⟩)
    (fun i : Fin j.val => A ⟨i.val, by omega⟩ ⟨i.val, by omega⟩)
    (fun i => (hAdiag _).le)
    (gamma fp (j.val + 1) / (1 - gamma fp (j.val + 1)) * (j.val : ℝ))
    hquad y
    (fun i l h => h.elim
      (fun h0 => absurd h0 (hAdiag _).ne')
      (fun h0 => absurd h0 (hAdiag _).ne'))
  -- lift the stage constant to the display's r-shaped constant
  have hle : gamma fp (j.val + 1) / (1 - gamma fp (j.val + 1)) *
      (j.val : ℝ) ≤
      (r : ℝ) * (gamma fp (r + 1) / (1 - gamma fp (r + 1))) := by
    have hcG : gamma fp (j.val + 1) / (1 - gamma fp (j.val + 1)) ≤
        gamma fp (r + 1) / (1 - gamma fp (r + 1)) :=
      div_le_div₀ hG0 hγmG hD (by linarith)
    have hmr : (j.val : ℝ) ≤ (r : ℝ) := by exact_mod_cast hjr.le
    exact (mul_le_mul hcG hmr (Nat.cast_nonneg _)
      (div_nonneg hG0 hD.le)).trans_eq (mul_comm _ _)
  have hW0 : 0 ≤ ∑ i : Fin j.val,
      A ⟨i.val, by omega⟩ ⟨i.val, by omega⟩ * y i ^ 2 :=
    Finset.sum_nonneg fun i _ =>
      mul_nonneg (hAdiag _).le (sq_nonneg _)
  exact hmass.trans (mul_le_mul_of_nonneg_right hle hW0)

/-- **Display (10.21) stage border mass** (Higham p. 206): under the
    running induction hypothesis, the stage-`j` border-column Gram
    defect carries the scaled mass `r·γ_{r+1}/(1−γ_{r+1})` against the
    computed-column norm and the `A`-diagonal weights — the truncated
    border bound applied to the `(j+1)`-leading block (constant
    `γ_{j+2} ≤ γ_{r+1}`) plus the certificate column-norm control. -/
theorem higham10_21_stage_border_mass (fp : FPModel) {n : ℕ}
    (A : Fin n → Fin n → ℝ)
    (hsym : ∀ i j : Fin n, A i j = A j i)
    (hAdiag : ∀ i : Fin n, 0 < A i i)
    (hn1 : gammaValid fp (n + 1))
    (hγ1 : gamma fp (n + 1) < 1)
    (r : ℕ) (hrn : r ≤ n)
    (j : Fin n) (hjr : j.val < r)
    (IH : ∀ l : Fin n, l.val < j.val → 0 < fl_cholPivot fp n A l)
    (y : Fin j.val → ℝ) :
    |2 * ∑ i : Fin j.val, y i *
      ((∑ p : Fin j.val,
        fl_cholesky fp n A ⟨p.val, by omega⟩ ⟨i.val, by omega⟩ *
        fl_cholesky fp n A ⟨p.val, by omega⟩ j) -
        A ⟨i.val, by omega⟩ j)| ≤
      (r : ℝ) * (gamma fp (r + 1) / (1 - gamma fp (r + 1))) *
      ((∑ p : Fin j.val, fl_cholesky fp n A ⟨p.val, by omega⟩ j ^ 2) +
       ∑ i : Fin j.val,
         A ⟨i.val, by omega⟩ ⟨i.val, by omega⟩ * y i ^ 2) := by
  -- gamma bookkeeping
  have hrvalid : gammaValid fp (r + 1) :=
    gammaValid_mono fp (by omega) hn1
  have hG0 : 0 ≤ gamma fp (r + 1) := gamma_nonneg fp hrvalid
  have hG1 : gamma fp (r + 1) < 1 :=
    lt_of_le_of_lt (gamma_mono fp (by omega) hn1) hγ1
  have hD : (0:ℝ) < 1 - gamma fp (r + 1) := by linarith
  have hm1valid : gammaValid fp (j.val + 1) :=
    gammaValid_mono fp (by omega) hn1
  have hγmG : gamma fp (j.val + 1) ≤ gamma fp (r + 1) :=
    gamma_mono fp (by omega) hrvalid
  have hγm1 : gamma fp (j.val + 1) < 1 := lt_of_le_of_lt hγmG hG1
  have h1γm : (0:ℝ) < 1 - gamma fp (j.val + 1) := by linarith
  have hγ2valid : gammaValid fp (j.val + 2) :=
    gammaValid_mono fp (by omega) hn1
  have hγ20 : 0 ≤ gamma fp (j.val + 2) := gamma_nonneg fp hγ2valid
  have hγ2G : gamma fp (j.val + 2) ≤ gamma fp (r + 1) :=
    gamma_mono fp (by omega) hrvalid
  have hu : fp.u < 1 := by
    have h := hn1
    unfold gammaValid at h
    push_cast at h
    nlinarith [mul_nonneg (Nat.cast_nonneg n : (0:ℝ) ≤ (n:ℝ)) fp.u_nonneg]
  -- stage diagonals are nonzero from the IH
  have hdiag_ne : ∀ i : Fin j.val,
      fl_cholesky fp n A ⟨i.val, by omega⟩ ⟨i.val, by omega⟩ ≠ 0 := by
    intro i
    rw [fl_cholesky_diag_eq fp n A ⟨i.val, by omega⟩]
    exact (fl_sqrt_pos fp hu _ (IH ⟨i.val, by omega⟩ i.isLt)).ne'
  -- border entry bound at the (j+1)-leading block: constant γ_{j+2}
  set Am1 : Fin (j.val + 1) → Fin (j.val + 1) → ℝ :=
    fun i' l' => A ⟨i'.val, by omega⟩ ⟨l'.val, by omega⟩ with hAm1
  have hloc1 : ∀ p q : Fin (j.val + 1),
      fl_cholesky fp (j.val + 1) Am1 p q =
      fl_cholesky fp n A ⟨p.val, by omega⟩ ⟨q.val, by omega⟩ :=
    fun p q => fl_cholesky_leading_principal fp
      (by omega : j.val + 1 ≤ n) A p q
  have hbord : ∀ i : Fin j.val,
      |(∑ p : Fin j.val,
          fl_cholesky fp n A ⟨p.val, by omega⟩ ⟨i.val, by omega⟩ *
          fl_cholesky fp n A ⟨p.val, by omega⟩ j) -
        A ⟨i.val, by omega⟩ j| ≤
      gamma fp (j.val + 2) *
        (Real.sqrt (∑ p : Fin j.val,
          fl_cholesky fp n A ⟨p.val, by omega⟩ ⟨i.val, by omega⟩ ^ 2) *
         Real.sqrt (∑ p : Fin j.val,
          fl_cholesky fp n A ⟨p.val, by omega⟩ j ^ 2)) := by
    intro i
    have hdz : fl_cholesky fp (j.val + 1) Am1
        ⟨i.val, by omega⟩ ⟨i.val, by omega⟩ ≠ 0 := by
      rw [hloc1 ⟨i.val, by omega⟩ ⟨i.val, by omega⟩]
      exact hdiag_ne i
    have hb := fl_cholesky_border_bound fp (n := j.val + 1) Am1
      (gammaValid_mono fp (by omega) hn1) (Fin.last j.val) i hdz
    simp only [hloc1] at hb
    exact hb
  -- certificate column-norm control from the stage-j block certificate
  set Am : Fin j.val → Fin j.val → ℝ :=
    fun i' l' => A ⟨i'.val, by omega⟩ ⟨l'.val, by omega⟩ with hAm
  have hcert : CholeskyBackwardError j.val Am
      (fl_cholesky fp j.val Am) (gamma fp (j.val + 1)) :=
    fl_cholesky_block_certificate fp j.isLt.le A hsym hu hm1valid IH
  have hloc : ∀ p q : Fin j.val,
      fl_cholesky fp j.val Am p q =
      fl_cholesky fp n A ⟨p.val, by omega⟩ ⟨q.val, by omega⟩ :=
    fun p q => fl_cholesky_leading_principal fp j.isLt.le A p q
  have hcol : ∀ i : Fin j.val,
      (1 - gamma fp (j.val + 1)) *
        ∑ p : Fin j.val,
          fl_cholesky fp n A ⟨p.val, by omega⟩ ⟨i.val, by omega⟩ ^ 2 ≤
      A ⟨i.val, by omega⟩ ⟨i.val, by omega⟩ := by
    intro i
    have h := chol_cert_colNormSq_le j.val Am (fl_cholesky fp j.val Am)
      (gamma fp (j.val + 1)) hcert i
    simp only [hloc] at h
    exact h
  have hT0 : 0 ≤ ∑ p : Fin j.val,
      fl_cholesky fp n A ⟨p.val, by omega⟩ j ^ 2 :=
    Finset.sum_nonneg fun p _ => sq_nonneg _
  -- per-column scaled certificate at the display's r-shaped constant
  have hcertB : ∑ i : Fin j.val,
      (if A ⟨i.val, by omega⟩ ⟨i.val, by omega⟩ = 0 then 0 else
        ((∑ p : Fin j.val,
          fl_cholesky fp n A ⟨p.val, by omega⟩ ⟨i.val, by omega⟩ *
          fl_cholesky fp n A ⟨p.val, by omega⟩ j) -
          A ⟨i.val, by omega⟩ j) ^ 2 /
        A ⟨i.val, by omega⟩ ⟨i.val, by omega⟩) ≤
      ((r : ℝ) * (gamma fp (r + 1) / (1 - gamma fp (r + 1)))) ^ 2 *
      ∑ p : Fin j.val, fl_cholesky fp n A ⟨p.val, by omega⟩ j ^ 2 := by
    have hstep : ∀ i : Fin j.val,
        (if A ⟨i.val, by omega⟩ ⟨i.val, by omega⟩ = 0 then 0 else
          ((∑ p : Fin j.val,
            fl_cholesky fp n A ⟨p.val, by omega⟩ ⟨i.val, by omega⟩ *
            fl_cholesky fp n A ⟨p.val, by omega⟩ j) -
            A ⟨i.val, by omega⟩ j) ^ 2 /
          A ⟨i.val, by omega⟩ ⟨i.val, by omega⟩) ≤
        gamma fp (j.val + 2) ^ 2 *
          (∑ p : Fin j.val, fl_cholesky fp n A ⟨p.val, by omega⟩ j ^ 2) /
          (1 - gamma fp (j.val + 1)) := by
      intro i
      rw [if_neg (hAdiag _).ne']
      have hDsq0 : (0:ℝ) ≤ ∑ p : Fin j.val,
          fl_cholesky fp n A ⟨p.val, by omega⟩ ⟨i.val, by omega⟩ ^ 2 :=
        Finset.sum_nonneg fun p _ => sq_nonneg _
      have hδsq : ((∑ p : Fin j.val,
          fl_cholesky fp n A ⟨p.val, by omega⟩ ⟨i.val, by omega⟩ *
          fl_cholesky fp n A ⟨p.val, by omega⟩ j) -
          A ⟨i.val, by omega⟩ j) ^ 2 ≤
          gamma fp (j.val + 2) ^ 2 *
          (∑ p : Fin j.val,
            fl_cholesky fp n A ⟨p.val, by omega⟩ ⟨i.val, by omega⟩ ^ 2) *
          ∑ p : Fin j.val,
            fl_cholesky fp n A ⟨p.val, by omega⟩ j ^ 2 := by
        have h := mul_self_le_mul_self (abs_nonneg _) (hbord i)
        rw [abs_mul_abs_self] at h
        have hexp : (gamma fp (j.val + 2) *
            (Real.sqrt (∑ p : Fin j.val,
              fl_cholesky fp n A ⟨p.val, by omega⟩ ⟨i.val, by omega⟩ ^ 2) *
             Real.sqrt (∑ p : Fin j.val,
              fl_cholesky fp n A ⟨p.val, by omega⟩ j ^ 2))) *
            (gamma fp (j.val + 2) *
            (Real.sqrt (∑ p : Fin j.val,
              fl_cholesky fp n A ⟨p.val, by omega⟩ ⟨i.val, by omega⟩ ^ 2) *
             Real.sqrt (∑ p : Fin j.val,
              fl_cholesky fp n A ⟨p.val, by omega⟩ j ^ 2))) =
            gamma fp (j.val + 2) ^ 2 *
            (∑ p : Fin j.val,
              fl_cholesky fp n A ⟨p.val, by omega⟩ ⟨i.val, by omega⟩ ^ 2) *
            ∑ p : Fin j.val,
              fl_cholesky fp n A ⟨p.val, by omega⟩ j ^ 2 := by
          rw [show ∀ g a b : ℝ, g * (a * b) * (g * (a * b)) =
              g ^ 2 * (a * a) * (b * b) from fun g a b => by ring,
            Real.mul_self_sqrt hDsq0, Real.mul_self_sqrt hT0]
        rw [hexp] at h
        rw [pow_two]
        exact h
      rw [div_le_div_iff₀ (hAdiag _) h1γm]
      have h1 := mul_le_mul_of_nonneg_right hδsq h1γm.le
      have h2 := mul_le_mul_of_nonneg_left (hcol i)
        (mul_nonneg (sq_nonneg (gamma fp (j.val + 2))) hT0)
      nlinarith [h1, h2]
    calc ∑ i : Fin j.val,
        (if A ⟨i.val, by omega⟩ ⟨i.val, by omega⟩ = 0 then 0 else
          ((∑ p : Fin j.val,
            fl_cholesky fp n A ⟨p.val, by omega⟩ ⟨i.val, by omega⟩ *
            fl_cholesky fp n A ⟨p.val, by omega⟩ j) -
            A ⟨i.val, by omega⟩ j) ^ 2 /
          A ⟨i.val, by omega⟩ ⟨i.val, by omega⟩)
        ≤ ∑ _i : Fin j.val,
            gamma fp (j.val + 2) ^ 2 *
            (∑ p : Fin j.val,
              fl_cholesky fp n A ⟨p.val, by omega⟩ j ^ 2) /
            (1 - gamma fp (j.val + 1)) :=
          Finset.sum_le_sum fun i _ => hstep i
      _ = (j.val : ℝ) * (gamma fp (j.val + 2) ^ 2 *
            (∑ p : Fin j.val,
              fl_cholesky fp n A ⟨p.val, by omega⟩ j ^ 2) /
            (1 - gamma fp (j.val + 1))) := by
          rw [Finset.sum_const, Finset.card_univ, Fintype.card_fin,
            nsmul_eq_mul]
      _ ≤ ((r : ℝ) * (gamma fp (r + 1) / (1 - gamma fp (r + 1)))) ^ 2 *
            ∑ p : Fin j.val,
              fl_cholesky fp n A ⟨p.val, by omega⟩ j ^ 2 := by
          have hγ2sq : gamma fp (j.val + 2) ^ 2 ≤
              gamma fp (r + 1) ^ 2 := by nlinarith [hγ2G, hγ20]
          have hDsqle : (1 - gamma fp (r + 1)) ^ 2 ≤
              1 - gamma fp (j.val + 1) := by
            nlinarith [hD, hγmG, hG0, hG1]
          have hfrac : gamma fp (j.val + 2) ^ 2 /
              (1 - gamma fp (j.val + 1)) ≤
              gamma fp (r + 1) ^ 2 / (1 - gamma fp (r + 1)) ^ 2 :=
            div_le_div₀ (sq_nonneg _) hγ2sq (by positivity) hDsqle
          have hmr2 : (j.val : ℝ) ≤ (r : ℝ) ^ 2 := by
            have h1 : (j.val : ℝ) ≤ (r : ℝ) := by exact_mod_cast hjr.le
            have h2 : (1 : ℝ) ≤ (r : ℝ) := by
              have : 1 ≤ r := by omega
              exact_mod_cast this
            nlinarith
          calc (j.val : ℝ) * (gamma fp (j.val + 2) ^ 2 *
                (∑ p : Fin j.val,
                  fl_cholesky fp n A ⟨p.val, by omega⟩ j ^ 2) /
                (1 - gamma fp (j.val + 1)))
              = ((j.val : ℝ) * (gamma fp (j.val + 2) ^ 2 /
                  (1 - gamma fp (j.val + 1)))) *
                ∑ p : Fin j.val,
                  fl_cholesky fp n A ⟨p.val, by omega⟩ j ^ 2 := by
                ring
            _ ≤ ((r : ℝ) ^ 2 * (gamma fp (r + 1) ^ 2 /
                  (1 - gamma fp (r + 1)) ^ 2)) *
                ∑ p : Fin j.val,
                  fl_cholesky fp n A ⟨p.val, by omega⟩ j ^ 2 := by
                refine mul_le_mul_of_nonneg_right ?_ hT0
                exact mul_le_mul hmr2 hfrac
                  (div_nonneg (sq_nonneg _) h1γm.le) (sq_nonneg _)
            _ = ((r : ℝ) * (gamma fp (r + 1) /
                  (1 - gamma fp (r + 1)))) ^ 2 *
                ∑ p : Fin j.val,
                  fl_cholesky fp n A ⟨p.val, by omega⟩ j ^ 2 := by
                rw [mul_pow, div_pow]
  -- Cauchy–Schwarz + AM–GM assembly
  exact scaled_border_mass_normwise
    (fun i : Fin j.val =>
      (∑ p : Fin j.val,
        fl_cholesky fp n A ⟨p.val, by omega⟩ ⟨i.val, by omega⟩ *
        fl_cholesky fp n A ⟨p.val, by omega⟩ j) - A ⟨i.val, by omega⟩ j)
    (fun i : Fin j.val => A ⟨i.val, by omega⟩ ⟨i.val, by omega⟩)
    (fun i => (hAdiag _).le)
    ((r : ℝ) * (gamma fp (r + 1) / (1 - gamma fp (r + 1))))
    (∑ p : Fin j.val, fl_cholesky fp n A ⟨p.val, by omega⟩ j ^ 2)
    (mul_nonneg (Nat.cast_nonneg _) (div_nonneg hG0 hD.le)) hT0
    (fun i h0 => absurd h0 (hAdiag _).ne')
    hcertB y

/-- **Display (10.21), self-feeding leading-pivot positivity** (Higham
    §10.3.2, p. 206): with a bordered Rayleigh floor `lam` on the scaled
    leading blocks, every rounded pivot of stages `j < r` of the
    concrete Algorithm 10.2 run is positive at the source-shaped
    threshold `lam > r·γ_{r+1}/(1−γ_{r+1}) + 2γ_{n+1}` — no assumed
    run-level certificates: the stage masses are derived from the
    running induction hypothesis itself.  The `+2γ_{n+1}` additive is
    the recorded honest delta against the source's bare display. -/
theorem higham10_21_fl_cholesky_leading_pivots_pos (fp : FPModel) {n : ℕ}
    (A : Fin n → Fin n → ℝ)
    (hsym : ∀ i j : Fin n, A i j = A j i)
    (hAdiag : ∀ i : Fin n, 0 < A i i)
    (hn1 : gammaValid fp (n + 1))
    (hγ1 : gamma fp (n + 1) < 1)
    (r : ℕ) (hrn : r ≤ n) (lam : ℝ)
    (hfloor : ∀ j : Fin n, j.val < r → ∀ y : Fin j.val → ℝ,
      lam * ((∑ i : Fin j.val,
          A ⟨i.val, by omega⟩ ⟨i.val, by omega⟩ * y i ^ 2) + A j j) ≤
        (∑ i : Fin j.val, ∑ l : Fin j.val,
          y i * A ⟨i.val, by omega⟩ ⟨l.val, by omega⟩ * y l) +
        2 * (∑ i : Fin j.val, y i * A ⟨i.val, by omega⟩ j) + A j j)
    (hlam2ε : 2 * ((r : ℝ) *
      (gamma fp (r + 1) / (1 - gamma fp (r + 1)))) ≤ lam)
    (hthresh : (r : ℝ) * (gamma fp (r + 1) / (1 - gamma fp (r + 1))) +
      2 * gamma fp (n + 1) < lam) :
    ∀ j : Fin n, j.val < r → 0 < fl_cholPivot fp n A j := by
  have hrvalid : gammaValid fp (r + 1) :=
    gammaValid_mono fp (by omega) hn1
  have hG0 : 0 ≤ gamma fp (r + 1) := gamma_nonneg fp hrvalid
  have hG1 : gamma fp (r + 1) < 1 :=
    lt_of_le_of_lt (gamma_mono fp (by omega) hn1) hγ1
  have hε0 : 0 ≤ (r : ℝ) *
      (gamma fp (r + 1) / (1 - gamma fp (r + 1))) :=
    mul_nonneg (Nat.cast_nonneg _) (div_nonneg hG0 (by linarith))
  have H : ∀ k : ℕ, ∀ j : Fin n, j.val = k → j.val < r →
      0 < fl_cholPivot fp n A j := by
    intro k
    induction k using Nat.strong_induction_on with
    | _ k IHk =>
      intro j hj hjr
      have IH : ∀ l : Fin n, l.val < j.val → 0 < fl_cholPivot fp n A l :=
        fun l hl => IHk l.val (hj ▸ hl) l rfl (by omega)
      -- λ ≤ 1 from the floor at y = 0, so ε ≤ 1/2 < 1
      have hlam1 : lam ≤ 1 := by
        have h0 := hfloor j hjr (fun _ => (0 : ℝ))
        norm_num at h0
        exact le_of_mul_le_mul_right
          (by linarith : lam * A j j ≤ 1 * A j j) (hAdiag j)
      have hε1 : (r : ℝ) *
          (gamma fp (r + 1) / (1 - gamma fp (r + 1))) < 1 := by
        linarith
      exact fl_cholesky_pivot_pos_step_sharp fp A hAdiag hn1 hγ1 j IH lam
        ((r : ℝ) * (gamma fp (r + 1) / (1 - gamma fp (r + 1)))) hε0 hε1
        (hfloor j hjr)
        (fun y => higham10_21_stage_interior_mass fp A hsym hAdiag hn1 hγ1
          r hrn j hjr IH y)
        (fun y => higham10_21_stage_border_mass fp A hsym hAdiag hn1 hγ1
          r hrn j hjr IH y)
        hlam2ε hthresh
  exact fun j hjr => H j.val j rfl hjr

/-- **Display (10.21), source-facing `λ_min(H₁₁)` form** (Higham
    §10.3.2, p. 206, the hypothesis of Theorem 10.14): if the minimum
    eigenvalue of the scaled leading `r × r` block
    `H₁₁ = D₁⁻¹A₁₁D₁⁻¹` exceeds
    `r·γ_{r+1}/(1−γ_{r+1}) + 2γ_{n+1}` (and dominates twice the mass
    constant), the concrete Algorithm 10.2 run completes its first `r`
    stages: every rounded pivot below stage `r` is positive.  No
    run-level certificate is assumed; the `+2γ_{n+1}` additive is the
    recorded honest delta against the source's bare display. -/
theorem higham10_21_fl_cholesky_success (fp : FPModel) {n : ℕ}
    (A : Fin n → Fin n → ℝ)
    (hsym : ∀ i j : Fin n, A i j = A j i)
    (hAdiag : ∀ i : Fin n, 0 < A i i)
    (hn1 : gammaValid fp (n + 1))
    (hγ1 : gamma fp (n + 1) < 1)
    (r : ℕ) (hr0 : 0 < r) (hrn : r ≤ n)
    (hH_sym : IsSymmetricFiniteMatrix (fun i l : Fin r =>
      A ⟨i.val, by omega⟩ ⟨l.val, by omega⟩ /
        (Real.sqrt (A ⟨i.val, by omega⟩ ⟨i.val, by omega⟩) *
         Real.sqrt (A ⟨l.val, by omega⟩ ⟨l.val, by omega⟩))))
    (hlam2ε : 2 * ((r : ℝ) *
        (gamma fp (r + 1) / (1 - gamma fp (r + 1)))) ≤
      finiteMinEigenvalue hr0 (fun i l : Fin r =>
        A ⟨i.val, by omega⟩ ⟨l.val, by omega⟩ /
          (Real.sqrt (A ⟨i.val, by omega⟩ ⟨i.val, by omega⟩) *
           Real.sqrt (A ⟨l.val, by omega⟩ ⟨l.val, by omega⟩))) hH_sym)
    (hthresh : (r : ℝ) * (gamma fp (r + 1) / (1 - gamma fp (r + 1))) +
        2 * gamma fp (n + 1) <
      finiteMinEigenvalue hr0 (fun i l : Fin r =>
        A ⟨i.val, by omega⟩ ⟨l.val, by omega⟩ /
          (Real.sqrt (A ⟨i.val, by omega⟩ ⟨i.val, by omega⟩) *
           Real.sqrt (A ⟨l.val, by omega⟩ ⟨l.val, by omega⟩))) hH_sym) :
    ∀ j : Fin n, j.val < r → 0 < fl_cholPivot fp n A j := by
  refine higham10_21_fl_cholesky_leading_pivots_pos fp A hsym hAdiag hn1 hγ1
    r hrn _ ?_ hlam2ε hthresh
  intro j hjr y
  exact min_eig_scaled_bordered_floor r hr0
    (fun p q : Fin r => A ⟨p.val, by omega⟩ ⟨q.val, by omega⟩)
    (fun p q => hsym _ _) (fun p => hAdiag _) hH_sym ⟨j.val, hjr⟩ y

end NumStability
