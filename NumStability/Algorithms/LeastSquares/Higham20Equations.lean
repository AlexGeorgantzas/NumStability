-- Higham20Equations.lean
--
-- Finite, source-facing versions of Higham, 2nd ed., equations
-- (20.13a), (20.13b), (20.16), and (20.19).

import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Ring
import NumStability.Algorithms.LeastSquares.LSNormalEquations
import NumStability.Algorithms.LeastSquares.LSQRSolve
import NumStability.Source.Higham.Chapter12.IterativeRefinement

namespace NumStability

open scoped BigOperators

/-! ## The explicit remainder replacing `O(u^2)` -/

/-- The exact quadratic-and-higher part of `gamma fp k`.

This is a rational expression, not asymptotic notation.  Under
`gammaValid fp k`, `gamma fp k = k*u + higham20GammaRemainder fp k`. -/
noncomputable def higham20GammaRemainder (fp : FPModel) (k : ℕ) : ℝ :=
  (((k : ℝ) * fp.u) ^ 2) / (1 - (k : ℝ) * fp.u)

theorem higham20_gamma_eq_linear_add_remainder (fp : FPModel) (k : ℕ)
    (hk : gammaValid fp k) :
    gamma fp k = (k : ℝ) * fp.u + higham20GammaRemainder fp k := by
  simpa [higham20GammaRemainder] using
    gamma_eq_linear_plus_quadratic_remainder fp k hk

/-- The printed first-order coefficient in (20.13a). -/
noncomputable def higham20Eq20_13aLeading
    (fp : FPModel) (m n : ℕ) (A_norm : ℝ) : ℝ :=
  ((m : ℝ) * (n : ℝ) + 3 * (n : ℝ) ^ 2 + (n : ℝ)) * fp.u * A_norm ^ 2

/-- The complete finite remainder accompanying (20.13a).

It is exactly the two gamma remainders arising from
`n*gamma_m + n*gamma_(3n+1)`; no term is hidden in `O(u^2)`. -/
noncomputable def higham20Eq20_13aRemainder
    (fp : FPModel) (m n : ℕ) (A_norm : ℝ) : ℝ :=
  ((n : ℝ) * higham20GammaRemainder fp m +
      (n : ℝ) * higham20GammaRemainder fp (3 * n + 1)) * A_norm ^ 2

/-- The printed first-order coefficient in (20.13b). -/
noncomputable def higham20Eq20_13bLeading
    (fp : FPModel) (m n : ℕ) (A_norm b_norm : ℝ) : ℝ :=
  (m : ℝ) * Real.sqrt (n : ℝ) * fp.u * A_norm * b_norm

/-- The complete finite remainder accompanying (20.13b). -/
noncomputable def higham20Eq20_13bRemainder
    (fp : FPModel) (m n : ℕ) (A_norm b_norm : ℝ) : ℝ :=
  Real.sqrt (n : ℝ) * higham20GammaRemainder fp m * A_norm * b_norm

/-- Scalar bridge behind equation (20.13a): the exact finite gamma coefficient
has the printed first-order coefficient
`(m*n + 3*n^2 + n)u`, followed by the displayed rational remainder. -/
theorem higham20_eq20_13a_gamma_coefficient_exact
    (fp : FPModel) (m n : ℕ) (A_norm : ℝ)
    (hm : gammaValid fp m) (h3n1 : gammaValid fp (3 * n + 1)) :
    ((n : ℝ) * gamma fp m + (n : ℝ) * gamma fp (3 * n + 1)) * A_norm ^ 2 =
      higham20Eq20_13aLeading fp m n A_norm +
        higham20Eq20_13aRemainder fp m n A_norm := by
  rw [higham20_gamma_eq_linear_add_remainder fp m hm,
    higham20_gamma_eq_linear_add_remainder fp (3 * n + 1) h3n1]
  simp only [higham20Eq20_13aLeading, higham20Eq20_13aRemainder,
    Nat.cast_add, Nat.cast_mul, Nat.cast_ofNat]
  ring

/-- Scalar bridge behind equation (20.13b): the exact finite coefficient
`sqrt(n)*gamma_m` has printed first-order part `m*sqrt(n)*u`, followed by
the displayed rational remainder. -/
theorem higham20_eq20_13b_gamma_coefficient_exact
    (fp : FPModel) (m n : ℕ) (A_norm b_norm : ℝ)
    (hm : gammaValid fp m) :
    Real.sqrt (n : ℝ) * gamma fp m * A_norm * b_norm =
      higham20Eq20_13bLeading fp m n A_norm b_norm +
        higham20Eq20_13bRemainder fp m n A_norm b_norm := by
  rw [higham20_gamma_eq_linear_add_remainder fp m hm]
  simp only [higham20Eq20_13bLeading, higham20Eq20_13bRemainder]
  ring

/-! ## Equations (20.13a) and (20.13b) from the normal-equations analysis -/

/-- Absorb the expanded Cholesky-solve coefficient used by
`ls_normal_equations_backward` into `gamma_(3n+1)`. -/
private theorem higham20_cholesky_coefficient_le_gamma_3n1
    (fp : FPModel) (n : ℕ) (h3n1 : gammaValid fp (3 * n + 1)) :
    gamma fp (n + 1) + 2 * gamma fp n + gamma fp n ^ 2 ≤
      gamma fp (3 * n + 1) := by
  have hn1 : gammaValid fp (n + 1) :=
    gammaValid_mono fp (by omega) h3n1
  have hstep1 :
      gamma fp n + gamma fp n + gamma fp n * gamma fp n ≤
        gamma fp (2 * n) := by
    have h := gamma_sum_le fp n n (gammaValid_mono fp (by omega) h3n1)
    simpa [show n + n = 2 * n by omega] using h
  have hstep2 : gamma fp (n + 1) + gamma fp (2 * n) ≤
      gamma fp (3 * n + 1) := by
    have heq : (n + 1) + 2 * n = 3 * n + 1 := by omega
    have h := gamma_sum_le fp (n + 1) (2 * n) (heq ▸ h3n1)
    have hnn1 : 0 ≤ gamma fp (n + 1) := gamma_nonneg fp hn1
    have hnn2 : 0 ≤ gamma fp (2 * n) :=
      gamma_nonneg fp (gammaValid_mono fp (by omega) h3n1)
    rw [heq] at h
    linarith [mul_nonneg hnn1 hnn2]
  nlinarith [hstep1, hstep2]

/-- Equations (20.13a)-(20.13b), as a finite theorem built on the concrete
normal-equations backward-error result.

The two norm-envelope hypotheses are the norm estimates used in Higham's
passage from the componentwise bound (20.12) to (20.13):

* `absATA` and `|Rhat^T||Rhat|` each have Frobenius norm at most
  `n * ||A||_2^2`;
* `absATb` has Euclidean norm at most `sqrt(n) * ||A||_2 * ||b||_2`.

They are kept explicit because their validity depends on how the supplied
majorants and the computed Cholesky factor are related to the source data.
The conclusions contain the source's leading coefficients and the exact
rational higher-order remainders, rather than an unspecified `O(u^2)` term. -/
theorem higham20_eq20_13a_b_normal_equations_finite
    (fp : FPModel) (m n : ℕ)
    (ATA : Fin n → Fin n → ℝ) (ATb : Fin n → ℝ)
    (absATA : Fin n → Fin n → ℝ) (absATb : Fin n → ℝ)
    (C_hat : Fin n → Fin n → ℝ) (c_hat : Fin n → ℝ)
    (R_hat : Fin n → Fin n → ℝ)
    (A_norm b_norm : ℝ)
    (habsATA_nonneg : ∀ i j, 0 ≤ absATA i j)
    (hGram : GramProductError n C_hat ATA absATA (gamma fp m))
    (hGramVec : GramVecError n c_hat ATb absATb (gamma fp m))
    (hChol : CholeskyBackwardError n C_hat R_hat (gamma fp (n + 1)))
    (hR_diag : ∀ i : Fin n, R_hat i i ≠ 0)
    (hm : gammaValid fp m) (h3n1 : gammaValid fp (3 * n + 1))
    (habsATA_norm :
      frobNormRect absATA ≤ (n : ℝ) * A_norm ^ 2)
    (hRgram_norm :
      frobNormRect
          (fun i j : Fin n => ∑ k : Fin n, |R_hat k i| * |R_hat k j|) ≤
        (n : ℝ) * A_norm ^ 2)
    (habsATb_norm :
      vecNorm2 absATb ≤ Real.sqrt (n : ℝ) * A_norm * b_norm) :
    let R_hatT := fun i j : Fin n => R_hat j i
    let y_hat := fl_forwardSub fp n R_hatT c_hat
    let x_hat := fl_backSub fp n R_hat y_hat
    ∃ (DeltaA : Fin n → Fin n → ℝ) (Deltac : Fin n → ℝ),
      (∀ i, ∑ j : Fin n, (ATA i j + DeltaA i j) * x_hat j =
        ATb i + Deltac i) ∧
      complexMatrixOp2 (realRectToCMatrix DeltaA) ≤
        higham20Eq20_13aLeading fp m n A_norm +
          higham20Eq20_13aRemainder fp m n A_norm ∧
      vecNorm2 Deltac ≤
        higham20Eq20_13bLeading fp m n A_norm b_norm +
          higham20Eq20_13bRemainder fp m n A_norm b_norm := by
  dsimp
  have hn1 : gammaValid fp (n + 1) :=
    gammaValid_mono fp (by omega) h3n1
  obtain ⟨DeltaA, Deltac, hEq, hDeltaA, hDeltac⟩ :=
    ls_normal_equations_backward fp n ATA ATb absATA absATb C_hat c_hat
      R_hat hGram hGramVec hChol hR_diag hm hn1
  refine ⟨DeltaA, Deltac, hEq, ?_, ?_⟩
  · let Rgram : Fin n → Fin n → ℝ :=
      fun i j => ∑ k : Fin n, |R_hat k i| * |R_hat k j|
    let majorant : Fin n → Fin n → ℝ :=
      fun i j => gamma fp m * absATA i j + gamma fp (3 * n + 1) * Rgram i j
    have hgm : 0 ≤ gamma fp m := gamma_nonneg fp hm
    have hg3 : 0 ≤ gamma fp (3 * n + 1) := gamma_nonneg fp h3n1
    have hcholCoeff := higham20_cholesky_coefficient_le_gamma_3n1 fp n h3n1
    have hRgram_nonneg : ∀ i j, 0 ≤ Rgram i j := by
      intro i j
      exact Finset.sum_nonneg (fun k _ => mul_nonneg (abs_nonneg _) (abs_nonneg _))
    have hmajorant_nonneg : ∀ i j, 0 ≤ majorant i j := by
      intro i j
      exact add_nonneg (mul_nonneg hgm (habsATA_nonneg i j))
        (mul_nonneg hg3 (hRgram_nonneg i j))
    have hDeltaA_majorant : ∀ i j, |DeltaA i j| ≤ majorant i j := by
      intro i j
      calc
        |DeltaA i j| ≤
            gamma fp m * absATA i j +
              (gamma fp (n + 1) + 2 * gamma fp n + gamma fp n ^ 2) *
                Rgram i j := hDeltaA i j
        _ ≤ gamma fp m * absATA i j + gamma fp (3 * n + 1) * Rgram i j := by
          exact add_le_add_right
            (mul_le_mul_of_nonneg_right hcholCoeff (hRgram_nonneg i j)) _
        _ = majorant i j := rfl
    have hDeltaA_frob :
        frobNormRect DeltaA ≤
          ((n : ℝ) * gamma fp m + (n : ℝ) * gamma fp (3 * n + 1)) *
            A_norm ^ 2 := by
      calc
        frobNormRect DeltaA ≤ frobNormRect majorant :=
          frobNormRect_le_of_entry_abs_le DeltaA majorant hmajorant_nonneg
            hDeltaA_majorant
        _ ≤ frobNormRect (fun i j => gamma fp m * absATA i j) +
              frobNormRect (fun i j => gamma fp (3 * n + 1) * Rgram i j) := by
          exact frobNormRect_add_le _ _
        _ = gamma fp m * frobNormRect absATA +
              gamma fp (3 * n + 1) * frobNormRect Rgram := by
          rw [frobNormRect_smul, frobNormRect_smul,
            abs_of_nonneg hgm, abs_of_nonneg hg3]
        _ ≤ gamma fp m * ((n : ℝ) * A_norm ^ 2) +
              gamma fp (3 * n + 1) * ((n : ℝ) * A_norm ^ 2) := by
          exact add_le_add
            (mul_le_mul_of_nonneg_left habsATA_norm hgm)
            (mul_le_mul_of_nonneg_left hRgram_norm hg3)
        _ = ((n : ℝ) * gamma fp m + (n : ℝ) * gamma fp (3 * n + 1)) *
              A_norm ^ 2 := by ring
    have hfinite_nonneg :
        0 ≤ ((n : ℝ) * gamma fp m + (n : ℝ) * gamma fp (3 * n + 1)) *
          A_norm ^ 2 := by positivity
    have hop :
        complexMatrixOp2 (realRectToCMatrix DeltaA) ≤
          ((n : ℝ) * gamma fp m + (n : ℝ) * gamma fp (3 * n + 1)) *
            A_norm ^ 2 :=
      complexMatrixOp2_realRectToCMatrix_le_of_rectOpNorm2Le DeltaA
        hfinite_nonneg (rectOpNorm2Le_of_frobNormRect_le DeltaA hDeltaA_frob)
    rw [higham20_eq20_13a_gamma_coefficient_exact fp m n A_norm hm h3n1] at hop
    exact hop
  · have hgm : 0 ≤ gamma fp m := gamma_nonneg fp hm
    have hnormDeltac : vecNorm2 Deltac ≤ gamma fp m * vecNorm2 absATb := by
      calc
        vecNorm2 Deltac ≤ vecNorm2 (fun i => gamma fp m * absATb i) :=
          vecNorm2_le_of_abs_le Deltac (fun i => gamma fp m * absATb i) hDeltac
        _ = gamma fp m * vecNorm2 absATb := by
          rw [vecNorm2_smul, abs_of_nonneg hgm]
    have hfinite :
        vecNorm2 Deltac ≤
          Real.sqrt (n : ℝ) * gamma fp m * A_norm * b_norm := by
      calc
        vecNorm2 Deltac ≤ gamma fp m * vecNorm2 absATb := hnormDeltac
        _ ≤ gamma fp m * (Real.sqrt (n : ℝ) * A_norm * b_norm) :=
          mul_le_mul_of_nonneg_left habsATb_norm hgm
        _ = Real.sqrt (n : ℝ) * gamma fp m * A_norm * b_norm := by ring
    rw [higham20_eq20_13b_gamma_coefficient_exact fp m n A_norm b_norm hm] at hfinite
    exact hfinite

/-- Source-norm specialization of equations (20.13a)-(20.13b).

Unlike the reusable envelope theorem above, this surface writes the two
scales literally as `||A||_2 = complexMatrixOp2 (realRectToCMatrix A)` and
`||b||_2 = vecNorm2 b`, matching the printed equations. -/
theorem higham20_eq20_13a_b_normal_equations_source_norms_finite
    (fp : FPModel) (m n : ℕ)
    (A : Fin m → Fin n → ℝ) (b : Fin m → ℝ)
    (ATA : Fin n → Fin n → ℝ) (ATb : Fin n → ℝ)
    (absATA : Fin n → Fin n → ℝ) (absATb : Fin n → ℝ)
    (C_hat : Fin n → Fin n → ℝ) (c_hat : Fin n → ℝ)
    (R_hat : Fin n → Fin n → ℝ)
    (habsATA_nonneg : ∀ i j, 0 ≤ absATA i j)
    (hGram : GramProductError n C_hat ATA absATA (gamma fp m))
    (hGramVec : GramVecError n c_hat ATb absATb (gamma fp m))
    (hChol : CholeskyBackwardError n C_hat R_hat (gamma fp (n + 1)))
    (hR_diag : ∀ i : Fin n, R_hat i i ≠ 0)
    (hm : gammaValid fp m) (h3n1 : gammaValid fp (3 * n + 1))
    (habsATA_norm :
      frobNormRect absATA ≤
        (n : ℝ) * complexMatrixOp2 (realRectToCMatrix A) ^ 2)
    (hRgram_norm :
      frobNormRect
          (fun i j : Fin n => ∑ k : Fin n, |R_hat k i| * |R_hat k j|) ≤
        (n : ℝ) * complexMatrixOp2 (realRectToCMatrix A) ^ 2)
    (habsATb_norm :
      vecNorm2 absATb ≤ Real.sqrt (n : ℝ) *
        complexMatrixOp2 (realRectToCMatrix A) * vecNorm2 b) :
    let R_hatT := fun i j : Fin n => R_hat j i
    let y_hat := fl_forwardSub fp n R_hatT c_hat
    let x_hat := fl_backSub fp n R_hat y_hat
    ∃ (DeltaA : Fin n → Fin n → ℝ) (Deltac : Fin n → ℝ),
      (∀ i, ∑ j : Fin n, (ATA i j + DeltaA i j) * x_hat j =
        ATb i + Deltac i) ∧
      complexMatrixOp2 (realRectToCMatrix DeltaA) ≤
        higham20Eq20_13aLeading fp m n
            (complexMatrixOp2 (realRectToCMatrix A)) +
          higham20Eq20_13aRemainder fp m n
            (complexMatrixOp2 (realRectToCMatrix A)) ∧
      vecNorm2 Deltac ≤
        higham20Eq20_13bLeading fp m n
            (complexMatrixOp2 (realRectToCMatrix A)) (vecNorm2 b) +
          higham20Eq20_13bRemainder fp m n
            (complexMatrixOp2 (realRectToCMatrix A)) (vecNorm2 b) := by
  exact higham20_eq20_13a_b_normal_equations_finite fp m n ATA ATb
    absATA absATb C_hat c_hat R_hat
    (complexMatrixOp2 (realRectToCMatrix A)) (vecNorm2 b)
    habsATA_nonneg hGram hGramVec hChol hR_diag hm h3n1
    habsATA_norm hRgram_norm habsATb_norm

/-! ## Equation (20.16): one refinement step on the augmented system -/

/-- The source coefficient matrix in (20.16), literally
`[[I_m, A], [A^T, 0]]`, with total dimension `m+n`. -/
noncomputable def higham20Eq20_16Matrix {m n : ℕ}
    (A : Fin m → Fin n → ℝ) : Fin (m + n) → Fin (m + n) → ℝ :=
  Fin.append
    (fun i : Fin m => Fin.append (fun j : Fin m => idMatrix m i j) (A i))
    (fun j : Fin n => Fin.append (fun i : Fin m => A i j) (fun _ : Fin n => 0))

theorem higham20Eq20_16Matrix_eq_lsScaledAugmentedMatrix_one {m n : ℕ}
    (A : Fin m → Fin n → ℝ) :
    higham20Eq20_16Matrix A = lsScaledAugmentedMatrix 1 A := by
  ext i j
  refine Fin.addCases (motive := fun i : Fin (m + n) =>
    higham20Eq20_16Matrix A i j = lsScaledAugmentedMatrix 1 A i j) ?_ ?_ i
  · intro i
    refine Fin.addCases (motive := fun j : Fin (m + n) =>
      higham20Eq20_16Matrix A (Fin.castAdd n i) j =
        lsScaledAugmentedMatrix 1 A (Fin.castAdd n i) j) ?_ ?_ j
    · intro j
      simp [higham20Eq20_16Matrix, lsScaledAugmentedMatrix,
        Fin.append_left]
    · intro j
      simp [higham20Eq20_16Matrix, lsScaledAugmentedMatrix,
        Fin.append_left, Fin.append_right]
  · intro i
    refine Fin.addCases (motive := fun j : Fin (m + n) =>
      higham20Eq20_16Matrix A (Fin.natAdd m i) j =
        lsScaledAugmentedMatrix 1 A (Fin.natAdd m i) j) ?_ ?_ j
    · intro j
      simp [higham20Eq20_16Matrix, lsScaledAugmentedMatrix,
        Fin.append_left, Fin.append_right]
    · intro j
      simp [higham20Eq20_16Matrix, lsScaledAugmentedMatrix,
        Fin.append_right]

/-- The exact higher-order remainder in the finite form of (20.16).

The first term comes from the `m*n*gamma_m` augmented solver defect.  The
second comes from conventional residual computation in dimension `m+n`, whose
accumulator is `gamma_(m+n+1)`. -/
noncomputable def higham20Eq20_16Remainder {m n : ℕ}
    (fp : FPModel) (A : Fin m → Fin n → ℝ)
    (H : Fin (m + n) → Fin (m + n) → ℝ)
    (rhs oldResidual z : Fin (m + n) → ℝ) (p : Fin (m + n)) : ℝ :=
  ((m : ℝ) * (n : ℝ)) * higham20GammaRemainder fp m *
      (∑ q : Fin (m + n), H p q * |oldResidual q|) +
    higham20GammaRemainder fp (m + n + 1) *
      (|rhs p| + ∑ q : Fin (m + n),
        |higham20Eq20_16Matrix A p q| * |z q|)

/-- Higham equation (20.16), with every higher-order term displayed.

This is an adapter of the exact Chapter 12 one-step residual theorem to the
least-squares augmented matrix `[[I,A],[A^T,0]]`.  The primitive hypotheses are
the correction-solve defect, conventional residual-computation error, and
rounded-update error; the desired post-refinement residual inequality is not
assumed.

`H` is the nonnegative solver majorant supplied by the augmented-system solve
analysis (Theorem 20.4).  Expanding the two gammas gives a first-order term in
`u` plus `higham20Eq20_16Remainder`, an explicit rational replacement for the
book's `O(u^2)`. -/
theorem higham20_eq20_16_augmented_one_refinement_finite
    (fp : FPModel) (m n : ℕ)
    (A : Fin m → Fin n → ℝ)
    (H : Fin (m + n) → Fin (m + n) → ℝ)
    (z d oldResidual computedResidual updateError y rhs :
      Fin (m + n) → ℝ)
    (hm : gammaValid fp m)
    (hdim : gammaValid fp (m + n + 1))
    (holdResidual : ∀ p : Fin (m + n),
      oldResidual p = rhs p -
        ∑ q : Fin (m + n), higham20Eq20_16Matrix A p q * z q)
    (hy : ∀ p : Fin (m + n),
      y p = z p + d p + updateError p)
    (hsolveDefect : ∀ p : Fin (m + n),
      |computedResidual p -
          ∑ q : Fin (m + n), higham20Eq20_16Matrix A p q * d q| ≤
        ((m : ℝ) * (n : ℝ)) * gamma fp m *
          ∑ q : Fin (m + n), H p q * |oldResidual q|)
    (hresidualComputation : ∀ p : Fin (m + n),
      |computedResidual p - oldResidual p| ≤
        gamma fp (m + n + 1) *
          (|rhs p| + ∑ q : Fin (m + n),
            |higham20Eq20_16Matrix A p q| * |z q|))
    (hupdate : ∀ q : Fin (m + n),
      |updateError q| ≤ fp.u * (|z q| + |d q|)) :
    ∀ p : Fin (m + n),
      |rhs p - ∑ q : Fin (m + n),
          higham20Eq20_16Matrix A p q * y q| ≤
        fp.u *
          (((m : ℝ) * (n : ℝ) * (m : ℝ)) *
              (∑ q : Fin (m + n), H p q * |oldResidual q|) +
            ((m + n + 1 : ℕ) : ℝ) *
              (|rhs p| + ∑ q : Fin (m + n),
                |higham20Eq20_16Matrix A p q| * |z q|) +
            ∑ q : Fin (m + n),
              |higham20Eq20_16Matrix A p q| * (|z q| + |d q|)) +
          higham20Eq20_16Remainder fp A H rhs oldResidual z p := by
  intro p
  have hbase := higham12_14_residual_bound (m + n)
    (higham20Eq20_16Matrix A) z d rhs oldResidual computedResidual
    updateError y holdResidual hy p
  have hupdateSum :
      (∑ q : Fin (m + n),
          |higham20Eq20_16Matrix A p q| * |updateError q|) ≤
        fp.u * ∑ q : Fin (m + n),
          |higham20Eq20_16Matrix A p q| * (|z q| + |d q|) := by
    calc
      (∑ q : Fin (m + n),
          |higham20Eq20_16Matrix A p q| * |updateError q|) ≤
          ∑ q : Fin (m + n),
            |higham20Eq20_16Matrix A p q| *
              (fp.u * (|z q| + |d q|)) := by
        exact Finset.sum_le_sum (fun q _ =>
          mul_le_mul_of_nonneg_left (hupdate q) (abs_nonneg _))
      _ = fp.u * ∑ q : Fin (m + n),
          |higham20Eq20_16Matrix A p q| * (|z q| + |d q|) := by
        rw [Finset.mul_sum]
        apply Finset.sum_congr rfl
        intro q _
        ring
  calc
    |rhs p - ∑ q : Fin (m + n), higham20Eq20_16Matrix A p q * y q| ≤
        |computedResidual p -
          ∑ q : Fin (m + n), higham20Eq20_16Matrix A p q * d q| +
        |computedResidual p - oldResidual p| +
        ∑ q : Fin (m + n),
          |higham20Eq20_16Matrix A p q| * |updateError q| := hbase
    _ ≤ ((m : ℝ) * (n : ℝ)) * gamma fp m *
          (∑ q : Fin (m + n), H p q * |oldResidual q|) +
        gamma fp (m + n + 1) *
          (|rhs p| + ∑ q : Fin (m + n),
            |higham20Eq20_16Matrix A p q| * |z q|) +
        fp.u * ∑ q : Fin (m + n),
          |higham20Eq20_16Matrix A p q| * (|z q| + |d q|) := by
      exact add_le_add (add_le_add (hsolveDefect p) (hresidualComputation p))
        hupdateSum
    _ = fp.u *
          (((m : ℝ) * (n : ℝ) * (m : ℝ)) *
              (∑ q : Fin (m + n), H p q * |oldResidual q|) +
            ((m + n + 1 : ℕ) : ℝ) *
              (|rhs p| + ∑ q : Fin (m + n),
                |higham20Eq20_16Matrix A p q| * |z q|) +
            ∑ q : Fin (m + n),
              |higham20Eq20_16Matrix A p q| * (|z q| + |d q|)) +
          higham20Eq20_16Remainder fp A H rhs oldResidual z p := by
      rw [higham20_gamma_eq_linear_add_remainder fp m hm,
        higham20_gamma_eq_linear_add_remainder fp (m + n + 1) hdim]
      simp only [higham20Eq20_16Remainder, Nat.cast_add, Nat.cast_one]
      ring

/-! ## Executed residual and rounded-update specialization of (20.16) -/

/-- The residual supplied to the augmented correction solve in one executed
fixed-precision refinement step.  This is the conventional Chapter 12 kernel,
applied to the square augmented matrix `[[I,A],[A^T,0]]`. -/
noncomputable def higham20Eq20_16ComputedResidual {m n : ℕ}
    (fp : FPModel) (A : Fin m → Fin n → ℝ)
    (z rhs : Fin (m + n) → ℝ) : Fin (m + n) → ℝ :=
  fl_residual fp (m + n) (higham20Eq20_16Matrix A) z rhs

/-- The actual componentwise rounded update used after the correction solve. -/
noncomputable def higham20Eq20_16RoundedUpdate {m n : ℕ}
    (fp : FPModel) (z d : Fin (m + n) → ℝ) : Fin (m + n) → ℝ :=
  fun q => fp.fl_add (z q) (d q)

/-- The exact additive error committed by the executed rounded update. -/
noncomputable def higham20Eq20_16UpdateError {m n : ℕ}
    (fp : FPModel) (z d : Fin (m + n) → ℝ) : Fin (m + n) → ℝ :=
  fun q => higham20Eq20_16RoundedUpdate fp z d q - z q - d q

theorem higham20Eq20_16RoundedUpdate_eq {m n : ℕ}
    (fp : FPModel) (z d : Fin (m + n) → ℝ) :
    ∀ q : Fin (m + n),
      higham20Eq20_16RoundedUpdate fp z d q =
        z q + d q + higham20Eq20_16UpdateError fp z d q := by
  intro q
  simp only [higham20Eq20_16RoundedUpdate, higham20Eq20_16UpdateError]
  ring

theorem higham20Eq20_16UpdateError_abs_le {m n : ℕ}
    (fp : FPModel) (z d : Fin (m + n) → ℝ) :
    ∀ q : Fin (m + n),
      |higham20Eq20_16UpdateError fp z d q| ≤
        fp.u * (|z q| + |d q|) := by
  intro q
  obtain ⟨δ, hδ, hadd⟩ := fp.model_add (z q) (d q)
  have herr :
      higham20Eq20_16UpdateError fp z d q = (z q + d q) * δ := by
    simp only [higham20Eq20_16UpdateError, higham20Eq20_16RoundedUpdate, hadd]
    ring
  rw [herr, abs_mul]
  calc
    |z q + d q| * |δ| ≤ |z q + d q| * fp.u :=
      mul_le_mul_of_nonneg_left hδ (abs_nonneg _)
    _ ≤ (|z q| + |d q|) * fp.u :=
      mul_le_mul_of_nonneg_right (abs_add_le _ _) fp.u_nonneg
    _ = fp.u * (|z q| + |d q|) := by ring

/-- Equation (20.16) with its conventional residual formation and rounded
update instantiated by the repository's executable floating-point kernels.

Only the correction-solver defect remains as an input.  In particular, the
post-refinement residual, residual-computation error, and update error are no
longer assumed.  The theorem is the direct adapter used by the concrete
Theorem 20.4 correction-solve endpoint. -/
theorem higham20_eq20_16_augmented_one_refinement_actual_residual_update
    (fp : FPModel) (m n : ℕ)
    (A : Fin m → Fin n → ℝ)
    (H : Fin (m + n) → Fin (m + n) → ℝ)
    (z d rhs : Fin (m + n) → ℝ)
    (hm : gammaValid fp m)
    (hdim : gammaValid fp (m + n + 1))
    (hsolveDefect : ∀ p : Fin (m + n),
      |higham20Eq20_16ComputedResidual fp A z rhs p -
          ∑ q : Fin (m + n), higham20Eq20_16Matrix A p q * d q| ≤
        ((m : ℝ) * (n : ℝ)) * gamma fp m *
          ∑ q : Fin (m + n), H p q *
            |rhs q - ∑ t : Fin (m + n),
              higham20Eq20_16Matrix A q t * z t|) :
    ∀ p : Fin (m + n),
      |rhs p - ∑ q : Fin (m + n), higham20Eq20_16Matrix A p q *
          higham20Eq20_16RoundedUpdate fp z d q| ≤
        fp.u *
          (((m : ℝ) * (n : ℝ) * (m : ℝ)) *
              (∑ q : Fin (m + n), H p q *
                |rhs q - ∑ t : Fin (m + n),
                  higham20Eq20_16Matrix A q t * z t|) +
            ((m + n + 1 : ℕ) : ℝ) *
              (|rhs p| + ∑ q : Fin (m + n),
                |higham20Eq20_16Matrix A p q| * |z q|) +
            ∑ q : Fin (m + n),
              |higham20Eq20_16Matrix A p q| * (|z q| + |d q|)) +
          higham20Eq20_16Remainder fp A H rhs
            (fun q => rhs q - ∑ t : Fin (m + n),
              higham20Eq20_16Matrix A q t * z t) z p := by
  have hdim0 : gammaValid fp (m + n) :=
    gammaValid_mono fp (by omega) hdim
  exact higham20_eq20_16_augmented_one_refinement_finite
    fp m n A H z d
    (fun q => rhs q - ∑ t : Fin (m + n),
      higham20Eq20_16Matrix A q t * z t)
    (higham20Eq20_16ComputedResidual fp A z rhs)
    (higham20Eq20_16UpdateError fp z d)
    (higham20Eq20_16RoundedUpdate fp z d) rhs hm hdim
    (fun _ => rfl)
    (higham20Eq20_16RoundedUpdate_eq fp z d)
    hsolveDefect
    (higham12_9_conventional_residual_error fp (m + n)
      (higham20Eq20_16Matrix A) z rhs hdim0 hdim)
    (higham20Eq20_16UpdateError_abs_le fp z d)

/-! ## The scaled augmented-system extremum in Problem 20.7 -/

/-- The positive branch is monotone in the nonnegative scale parameter. -/
private theorem higham20Eq20_19_plus_mono_alpha
    {alpha beta sigma : ℝ} (halpha : 0 ≤ alpha) (hab : alpha ≤ beta) :
    lsScaledAugmentedEigenvaluePlus alpha sigma ≤
      lsScaledAugmentedEigenvaluePlus beta sigma := by
  have hsquares : alpha ^ 2 ≤ beta ^ 2 := by nlinarith
  have hsqrt :
      Real.sqrt (alpha ^ 2 / 4 + sigma ^ 2) ≤
        Real.sqrt (beta ^ 2 / 4 + sigma ^ 2) :=
    Real.sqrt_le_sqrt (by nlinarith)
  unfold lsScaledAugmentedEigenvaluePlus
  linarith

/-- Before the balancing point, the positive-branch quotient decreases as the
positive scale increases. -/
private theorem higham20Eq20_19_plus_div_antitone_until_balanced
    {alpha beta sigma : ℝ} (halpha : 0 < alpha) (hab : alpha ≤ beta) :
    lsScaledAugmentedEigenvaluePlus beta sigma / beta ≤
      lsScaledAugmentedEigenvaluePlus alpha sigma / alpha := by
  have hbeta : 0 < beta := lt_of_lt_of_le halpha hab
  let ra : ℝ := Real.sqrt (alpha ^ 2 / 4 + sigma ^ 2)
  let rb : ℝ := Real.sqrt (beta ^ 2 / 4 + sigma ^ 2)
  have hra_nonneg : 0 ≤ ra := Real.sqrt_nonneg _
  have hrb_nonneg : 0 ≤ rb := Real.sqrt_nonneg _
  have hra_sq : ra ^ 2 = alpha ^ 2 / 4 + sigma ^ 2 := by
    dsimp [ra]
    exact Real.sq_sqrt (by positivity)
  have hrb_sq : rb ^ 2 = beta ^ 2 / 4 + sigma ^ 2 := by
    dsimp [rb]
    exact Real.sq_sqrt (by positivity)
  have hab_sq : alpha ^ 2 ≤ beta ^ 2 := by nlinarith
  have hprod :
      sigma ^ 2 * (alpha ^ 2 - beta ^ 2) ≤ 0 :=
    mul_nonpos_of_nonneg_of_nonpos (sq_nonneg sigma)
      (sub_nonpos.mpr hab_sq)
  have hcross_sq : (alpha * rb) ^ 2 ≤ (beta * ra) ^ 2 := by
    nlinarith [hra_sq, hrb_sq, hprod]
  have hcross : alpha * rb ≤ beta * ra := by
    have hleft : 0 ≤ alpha * rb := mul_nonneg (le_of_lt halpha) hrb_nonneg
    have hright : 0 ≤ beta * ra := mul_nonneg (le_of_lt hbeta) hra_nonneg
    nlinarith
  apply (div_le_div_iff₀ hbeta halpha).2
  unfold lsScaledAugmentedEigenvaluePlus
  change (beta / 2 + rb) * alpha ≤ (alpha / 2 + ra) * beta
  nlinarith

/-- Scalar denominator comparison at the balancing value in (20.19).

For positive `sigma`, once `alpha` is at least `sigma / sqrt 2`, the
magnitude of the negative branch is no larger than that balancing value. -/
private theorem higham20Eq20_19_abs_minus_le_balanced_of_balanced_le_alpha
    {alpha sigma : ℝ} (hsigma : 0 < sigma)
    (hbalanced : sigma / Real.sqrt 2 ≤ alpha) :
    |lsScaledAugmentedEigenvalueMinus alpha sigma| ≤
      sigma / Real.sqrt 2 := by
  let s : ℝ := Real.sqrt 2
  let t : ℝ := sigma / s
  have hs_pos : 0 < s := by
    simpa [s] using Real.sqrt_pos.2 (by norm_num : (0 : ℝ) < 2)
  have hs_ne : s ≠ 0 := ne_of_gt hs_pos
  have hs_sq : s ^ 2 = (2 : ℝ) := by
    simpa [s] using Real.sq_sqrt (by norm_num : (0 : ℝ) ≤ 2)
  have ht_nonneg : 0 ≤ t := by
    dsimp [t]
    positivity
  have ht_le : t ≤ alpha := by
    simpa [s, t] using hbalanced
  have hs_mul_t : s * t = sigma := by
    dsimp [t]
    field_simp [hs_ne]
  have halpha_nonneg : 0 ≤ alpha := le_trans ht_nonneg ht_le
  have hminus_nonpos :
      lsScaledAugmentedEigenvalueMinus alpha sigma ≤ 0 :=
    lsScaledAugmentedEigenvalueMinus_nonpos halpha_nonneg
  rw [abs_of_nonpos hminus_nonpos]
  unfold lsScaledAugmentedEigenvalueMinus
  have hrhs_nonneg : 0 ≤ alpha / 2 + t := by positivity
  have hprod : 0 ≤ t * (alpha - t) :=
    mul_nonneg ht_nonneg (sub_nonneg.mpr ht_le)
  have hsq :
      alpha ^ 2 / 4 + sigma ^ 2 ≤ (alpha / 2 + t) ^ 2 := by
    rw [← hs_mul_t]
    nlinarith [hs_sq, hprod]
  have hsqrt_le :
      Real.sqrt (alpha ^ 2 / 4 + sigma ^ 2) ≤ alpha / 2 + t :=
    (Real.sqrt_le_iff).2 ⟨hrhs_nonneg, hsq⟩
  simpa [s, t] using (show
    -(alpha / 2 - Real.sqrt (alpha ^ 2 / 4 + sigma ^ 2)) ≤ t by
      linarith)

/-- Why Problem 20.7 is stated below for a strictly tall matrix: in the
square scalar branch model there is no left-null `alpha` eigenvalue.  Already
at the positive scale `alpha = 1/4`, `sigma = 1`, the plus/minus branch ratio
is strictly below the printed universal lower factor `sqrt 2`.

Thus the `sqrt 2 * kappa_2(A)` lower envelope in (20.19) uses the nonempty
left-null branch and does not extend unchanged to `m = n`. -/
theorem higham20_problem20_7_square_scalar_branch_discrepancy :
    lsScaledAugmentedEigenvaluePlus (1 / 4 : ℝ) 1 /
        |lsScaledAugmentedEigenvalueMinus (1 / 4 : ℝ) 1| <
      Real.sqrt 2 := by
  let t : ℝ := Real.sqrt (((1 / 4 : ℝ) ^ 2) / 4 + 1 ^ 2)
  have ht : 1 < t := by
    dsimp [t]
    rw [Real.lt_sqrt (by norm_num : (0 : ℝ) ≤ 1)]
    norm_num
  have hs_pos : 0 < Real.sqrt 2 := Real.sqrt_pos.2 (by norm_num)
  have hs_sq : (Real.sqrt 2) ^ 2 = (2 : ℝ) :=
    Real.sq_sqrt (by norm_num)
  have hs_gt_one : 1 < Real.sqrt 2 := by nlinarith
  have hs_gt_nine_sevenths : (9 / 7 : ℝ) < Real.sqrt 2 := by
    nlinarith
  have hmul :
      Real.sqrt 2 - 1 < (Real.sqrt 2 - 1) * t := by
    simpa using
      (mul_lt_mul_of_pos_left ht (sub_pos.mpr hs_gt_one))
  have hnum :
      (1 / 8 : ℝ) + t < Real.sqrt 2 * (t - 1 / 8) := by
    nlinarith
  have hden : 0 < t - 1 / 8 := by nlinarith
  have hplus :
      lsScaledAugmentedEigenvaluePlus (1 / 4 : ℝ) 1 = 1 / 8 + t := by
    simp only [lsScaledAugmentedEigenvaluePlus]
    change (1 / 4 : ℝ) / 2 + t = 1 / 8 + t
    ring
  have hminus :
      lsScaledAugmentedEigenvalueMinus (1 / 4 : ℝ) 1 = 1 / 8 - t := by
    simp only [lsScaledAugmentedEigenvalueMinus]
    change (1 / 4 : ℝ) / 2 - t = 1 / 8 - t
    ring
  rw [hplus, hminus, abs_of_neg (by linarith : (1 / 8 : ℝ) - t < 0)]
  simpa using (div_lt_iff₀ hden).2 hnum

/-- Higham, 2nd ed., Problem 20.7 and equation (20.19), as one
source-facing extremum certificate for a strictly overdetermined full-column-
rank least-squares problem.

The conclusion is the set-theoretic content of the printed minimum bounds:
every positive scale is at least `sqrt 2 * kappa_2(A)`, the displayed scale
`sigma_min / sqrt 2` is positive and realizes the printed `2 * kappa_2(A)`
upper witness, is a global minimizer over positive scales, and the positive
scale `sigma_max` gives a condition number strictly exceeding
`kappa_2(A)^2`.  The complete singular-vector and
left-nullspace equations determine the inverse candidate; no extremum or
condition-number conclusion is supplied as a hypothesis. -/
theorem higham20_problem20_7_scaled_augmented_condition_extremum
    {m n : ℕ} [Nonempty (Fin n)] (hlt : n < m)
    {A : Fin m → Fin n → ℝ}
    (hrank : Function.Injective (rectMatMulVec A))
    {sigma : Fin n → ℝ} {u : Fin n → Fin m → ℝ}
    {v : Fin n → Fin n → ℝ} {w : Fin (m - n) → Fin m → ℝ}
    (hu : ∀ i : Fin n, vecNorm2Sq (u i) = 1)
    (hv : ∀ i : Fin n, vecNorm2Sq (v i) = 1)
    (hw : ∀ k : Fin (m - n), vecNorm2Sq (w k) = 1)
    (hleft : ∀ i j : Fin n, i ≠ j →
      (∑ r : Fin m, u i r * u j r) = 0)
    (hright : ∀ i j : Fin n, i ≠ j →
      (∑ c : Fin n, v i c * v j c) = 0)
    (hnull : ∀ k l : Fin (m - n), k ≠ l →
      (∑ r : Fin m, w k r * w l r) = 0)
    (hAv : ∀ i : Fin n,
      rectMatMulVec A (v i) = fun r => sigma i * u i r)
    (hATu : ∀ i : Fin n,
      (fun j : Fin n => ∑ r : Fin m, A r j * u i r) =
        fun j => sigma i * v i j)
    (hATw : ∀ k : Fin (m - n), ∀ j : Fin n,
      ∑ r : Fin m, A r j * w k r = 0)
    (hsigma_pos : ∀ i : Fin n, 0 < sigma i) :
    let sigmaMin := lsScaledAugmentedBranchSigmaMin sigma
    let sigmaMax := lsScaledAugmentedBranchSigmaMax sigma
    let alphaStar := sigmaMin / Real.sqrt 2
    let kappaA := sigmaMax / sigmaMin
    let Cinv := fun alpha =>
      lsScaledAugmentedSourceBranchInverseCandidate
        (Nat.le_of_lt hlt) alpha sigma u v w
    let kappaC := fun alpha =>
      kappa2 (lsScaledAugmentedMatrix alpha A) (Cinv alpha)
    0 < alphaStar ∧
      (∀ alpha : ℝ, 0 < alpha →
        Real.sqrt 2 * kappaA ≤ kappaC alpha) ∧
      (∀ alpha : ℝ, 0 < alpha → kappaC alphaStar ≤ kappaC alpha) ∧
      kappaC alphaStar ≤ 2 * kappaA ∧
      ∃ alpha : ℝ, 0 < alpha ∧ kappaA ^ 2 < kappaC alpha := by
  classical
  let hmn : n ≤ m := Nat.le_of_lt hlt
  let sigmaMin : ℝ := lsScaledAugmentedBranchSigmaMin sigma
  let sigmaMax : ℝ := lsScaledAugmentedBranchSigmaMax sigma
  let iMin : Fin n := lsScaledAugmentedBranchSigmaMinIndex sigma
  let iMax : Fin n := lsScaledAugmentedBranchSigmaMaxIndex sigma
  let alphaStar : ℝ := sigmaMin / Real.sqrt 2
  let kappaA : ℝ := sigmaMax / sigmaMin
  let Cinv : ℝ → Fin (m + n) → Fin (m + n) → ℝ := fun alpha =>
    lsScaledAugmentedSourceBranchInverseCandidate hmn alpha sigma u v w
  let kappaC : ℝ → ℝ := fun alpha =>
    kappa2 (lsScaledAugmentedMatrix alpha A) (Cinv alpha)
  change 0 < alphaStar ∧
    (∀ alpha : ℝ, 0 < alpha → Real.sqrt 2 * kappaA ≤ kappaC alpha) ∧
    (∀ alpha : ℝ, 0 < alpha → kappaC alphaStar ≤ kappaC alpha) ∧
    kappaC alphaStar ≤ 2 * kappaA ∧
    ∃ alpha : ℝ, 0 < alpha ∧ kappaA ^ 2 < kappaC alpha
  have hsigmaMin_eq : sigma iMin = sigmaMin := by
    rfl
  have hsigmaMax_eq : sigma iMax = sigmaMax := by
    rfl
  have hsigmaMin_pos : 0 < sigmaMin := by
    simpa [sigmaMin, iMin, lsScaledAugmentedBranchSigmaMin] using
      hsigma_pos iMin
  have hsigmaMin_ne : sigmaMin ≠ 0 := ne_of_gt hsigmaMin_pos
  have hsigmaMin_le_max : sigmaMin ≤ sigmaMax := by
    exact le_trans
      (lsScaledAugmentedBranchSigmaMin_le sigma iMin)
      (lsScaledAugmentedBranchSigma_le_max sigma iMin)
  have hsigmaMax_pos : 0 < sigmaMax :=
    lt_of_lt_of_le hsigmaMin_pos hsigmaMin_le_max
  have hsigma_ne : ∀ i : Fin n, sigma i ≠ 0 :=
    fun i => ne_of_gt (hsigma_pos i)
  have hsqrt_two_pos : 0 < Real.sqrt 2 :=
    Real.sqrt_pos.2 (by norm_num)
  have halphaStar_pos : 0 < alphaStar := by
    dsimp [alphaStar]
    positivity
  have hvMax : v iMax ≠ 0 := by
    intro hzero
    have hsq_zero : vecNorm2Sq (v iMax) = 0 := by
      simp [hzero, vecNorm2Sq]
    linarith [hv iMax]
  have hvMin : v iMin ≠ 0 := by
    intro hzero
    have hsq_zero : vecNorm2Sq (v iMin) = 0 := by
      simp [hzero, vecNorm2Sq]
    linarith [hv iMin]
  have hAvMax :
      rectMatMulVec A (v iMax) = fun r => sigmaMax * u iMax r := by
    simpa [hsigmaMax_eq] using hAv iMax
  have hATuMax :
      (fun j : Fin n => ∑ r : Fin m, A r j * u iMax r) =
        fun j => sigmaMax * v iMax j := by
    simpa [hsigmaMax_eq] using hATu iMax
  have hAvMin :
      rectMatMulVec A (v iMin) = fun r => sigmaMin * u iMin r := by
    simpa [hsigmaMin_eq] using hAv iMin
  have hATuMin :
      (fun j : Fin n => ∑ r : Fin m, A r j * u iMin r) =
        fun j => sigmaMin * v iMin j := by
    simpa [hsigmaMin_eq] using hATu iMin
  have hInv : ∀ alpha : ℝ, 0 < alpha →
      IsInverse (m + n) (lsScaledAugmentedMatrix alpha A) (Cinv alpha) := by
    intro alpha halpha
    let Q : Fin (m + n) → Fin (m + n) → ℝ := fun r c =>
      lsScaledAugmentedMatrixBranchVector alpha sigma u v w
        (lsScaledAugmentedSourceBranchEquiv m n hmn c) r
    let d : Fin (m + n) → ℝ := fun c =>
      lsScaledAugmentedMatrixBranchEigenvalue alpha sigma
        (lsScaledAugmentedSourceBranchEquiv m n hmn c)
    have hQ : IsOrthogonal (m + n) Q := by
      simpa [Q] using
        lsScaledAugmentedMatrixBranchVector_isOrthogonal_of_complete_equiv
          (alpha := alpha) (sigma := sigma) (A := A)
          (u := u) (v := v) (w := w)
          (lsScaledAugmentedSourceBranchEquiv m n hmn)
          hu hv hw hleft hright hnull hAv hATu hATw
          (le_of_lt halpha) hsigma_ne
    have hdiag :
        lsScaledAugmentedMatrix alpha A =
          finiteMatMul Q
            (finiteMatMul (finiteDiagonal d) (matTranspose Q)) := by
      simpa [Q, d] using
        lsScaledAugmentedMatrix_branch_orthogonal_diagonalization_of_complete_equiv
          (alpha := alpha) (sigma := sigma) (A := A)
          (u := u) (v := v) (w := w)
          (lsScaledAugmentedSourceBranchEquiv m n hmn)
          hu hv hw hleft hright hnull hAv hATu hATw
          (le_of_lt halpha) hsigma_ne
    have hd : ∀ c : Fin (m + n), d c ≠ 0 := by
      intro c
      rcases hc : lsScaledAugmentedSourceBranchEquiv m n hmn c with
        ((i | i) | k)
      · simpa [d, lsScaledAugmentedMatrixBranchEigenvalue, hc] using
          lsScaledAugmentedEigenvaluePlus_ne_zero_of_sigma_ne_zero
            (alpha := alpha) (sigma := sigma i) (le_of_lt halpha) (hsigma_ne i)
      · simpa [d, lsScaledAugmentedMatrixBranchEigenvalue, hc] using
          lsScaledAugmentedEigenvalueMinus_ne_zero_of_sigma_ne_zero
            (alpha := alpha) (sigma := sigma i) (le_of_lt halpha) (hsigma_ne i)
      · simpa [d, lsScaledAugmentedMatrixBranchEigenvalue, hc] using
          ne_of_gt halpha
    simpa [Cinv, lsScaledAugmentedSourceBranchInverseCandidate,
      lsScaledAugmentedSourceBranchEquiv, Q, d] using
      lsScaledAugmentedMatrix_isInverse_of_orthogonal_diagonalization
        (hdiag := hdiag) (hQ := hQ) hd
  have hlower : ∀ alpha : ℝ, 0 < alpha →
      Real.sqrt 2 * kappaA ≤ kappaC alpha := by
    intro alpha halpha
    have halpha_nonneg : 0 ≤ alpha := le_of_lt halpha
    have hinv := hInv alpha halpha
    have hminusRatio :
        lsScaledAugmentedEigenvaluePlus alpha sigmaMax /
            |lsScaledAugmentedEigenvalueMinus alpha sigmaMin| ≤
          kappaC alpha := by
      have h :=
        lsScaledAugmentedMatrix_singularPair_plus_minus_abs_ratio_le_kappa2
          (Cinv := Cinv alpha) hinv hAvMax hATuMax hAvMin hATuMin
          halpha_nonneg (ne_of_gt hsigmaMax_pos) hvMax
          (ne_of_gt hsigmaMin_pos) hvMin
      simpa [kappaC, abs_of_nonneg
        (lsScaledAugmentedEigenvaluePlus_nonneg
          (alpha := alpha) (sigma := sigmaMax) halpha_nonneg)] using h
    let k0 : Fin (m - n) := ⟨0, Nat.sub_pos_of_lt hlt⟩
    have hw0_ne : w k0 ≠ 0 := by
      intro hzero
      have hsq_zero : vecNorm2Sq (w k0) = 0 := by
        simp [hzero, vecNorm2Sq]
      linarith [hw k0]
    let z : Fin (m + n) → ℝ := Fin.append (w k0) (0 : Fin n → ℝ)
    have heigRect :=
      lsScaledAugmentedMatrix_leftNull_eigenpair alpha A (w k0)
        (hATw k0) hw0_ne
    have heig :
        finiteMatVec (lsScaledAugmentedMatrix alpha A) z =
          fun r => alpha * z r := by
      simpa [z, finiteMatVec, rectMatMulVec] using heigRect.1
    have hCinv : finiteOpNorm2Le (Cinv alpha) (opNorm2 (Cinv alpha)) :=
      finiteOpNorm2Le_of_opNorm2Le (Cinv alpha)
        (opNorm2Le_opNorm2 (Cinv alpha))
    have halphaRecip : alpha⁻¹ ≤ opNorm2 (Cinv alpha) := by
      have h :=
        finiteOpNorm2Le_inverse_abs_recip_eigenvalue_le_of_isLeftInverse
          (M := lsScaledAugmentedMatrix alpha A) (Minv := Cinv alpha)
          (lambda := alpha) (c := opNorm2 (Cinv alpha)) (x := z)
          hCinv hinv.1 (ne_of_gt halpha) heigRect.2 heig
      simpa [abs_of_pos halpha] using h
    have hC :
        finiteOpNorm2Le (lsScaledAugmentedMatrix alpha A)
          (opNorm2 (lsScaledAugmentedMatrix alpha A)) :=
      finiteOpNorm2Le_of_opNorm2Le (lsScaledAugmentedMatrix alpha A)
        (opNorm2Le_opNorm2 (lsScaledAugmentedMatrix alpha A))
    have hplus :
        lsScaledAugmentedEigenvaluePlus alpha sigmaMax ≤
          opNorm2 (lsScaledAugmentedMatrix alpha A) :=
      lsScaledAugmentedMatrix_singularPair_plus_eigenvalue_le_of_finiteOpNorm2Le
        hC hAvMax hATuMax halpha_nonneg (ne_of_gt hsigmaMax_pos) hvMax
    have halphaRatio :
        lsScaledAugmentedEigenvaluePlus alpha sigmaMax / alpha ≤
          kappaC alpha := by
      have hprod := mul_le_mul hplus halphaRecip
        (inv_nonneg.mpr halpha_nonneg)
        (opNorm2_nonneg (lsScaledAugmentedMatrix alpha A))
      simpa [kappaC, kappa2, div_eq_mul_inv] using hprod
    have hplus_ge :
        sigmaMax ≤ lsScaledAugmentedEigenvaluePlus alpha sigmaMax :=
      lsScaledAugmentedEigenvaluePlus_ge_sigma halpha_nonneg
        (le_of_lt hsigmaMax_pos)
    by_cases hsmall : alpha ≤ alphaStar
    · have hscale : Real.sqrt 2 * alpha ≤ sigmaMin := by
        have h := (le_div_iff₀ hsqrt_two_pos).1 (by
          simpa [alphaStar] using hsmall)
        nlinarith
      have hfactor : Real.sqrt 2 * alpha / sigmaMin ≤ 1 :=
        (div_le_one hsigmaMin_pos).2 hscale
      have hscalar :
          Real.sqrt 2 * kappaA ≤
            lsScaledAugmentedEigenvaluePlus alpha sigmaMax / alpha := by
        apply (le_div_iff₀ halpha).2
        calc
          Real.sqrt 2 * kappaA * alpha =
              sigmaMax * (Real.sqrt 2 * alpha / sigmaMin) := by
                simp only [kappaA]
                ring
          _ ≤ sigmaMax * 1 :=
            mul_le_mul_of_nonneg_left hfactor (le_of_lt hsigmaMax_pos)
          _ = sigmaMax := by ring
          _ ≤ lsScaledAugmentedEigenvaluePlus alpha sigmaMax := hplus_ge
      exact hscalar.trans halphaRatio
    · have hlarge : alphaStar ≤ alpha := le_of_not_ge hsmall
      have hDle :
          |lsScaledAugmentedEigenvalueMinus alpha sigmaMin| ≤ alphaStar := by
        simpa [alphaStar] using
          higham20Eq20_19_abs_minus_le_balanced_of_balanced_le_alpha
            hsigmaMin_pos (by simpa [alphaStar] using hlarge)
      have hDpos :
          0 < |lsScaledAugmentedEigenvalueMinus alpha sigmaMin| :=
        abs_pos.mpr
          (lsScaledAugmentedEigenvalueMinus_ne_zero_of_sigma_ne_zero
            halpha_nonneg (ne_of_gt hsigmaMin_pos))
      have hscale :
          Real.sqrt 2 *
              |lsScaledAugmentedEigenvalueMinus alpha sigmaMin| ≤ sigmaMin := by
        have h := (le_div_iff₀ hsqrt_two_pos).1 (by
          simpa [alphaStar] using hDle)
        nlinarith
      have hfactor :
          Real.sqrt 2 *
              |lsScaledAugmentedEigenvalueMinus alpha sigmaMin| / sigmaMin ≤ 1 :=
        (div_le_one hsigmaMin_pos).2 hscale
      have hscalar :
          Real.sqrt 2 * kappaA ≤
            lsScaledAugmentedEigenvaluePlus alpha sigmaMax /
              |lsScaledAugmentedEigenvalueMinus alpha sigmaMin| := by
        apply (le_div_iff₀ hDpos).2
        calc
          Real.sqrt 2 * kappaA *
                |lsScaledAugmentedEigenvalueMinus alpha sigmaMin| =
              sigmaMax *
                (Real.sqrt 2 *
                  |lsScaledAugmentedEigenvalueMinus alpha sigmaMin| /
                    sigmaMin) := by
                      simp only [kappaA]
                      ring
          _ ≤ sigmaMax * 1 :=
            mul_le_mul_of_nonneg_left hfactor (le_of_lt hsigmaMax_pos)
          _ = sigmaMax := by ring
          _ ≤ lsScaledAugmentedEigenvaluePlus alpha sigmaMax := hplus_ge
      exact hscalar.trans hminusRatio
  let Qstar : Fin (m + n) → Fin (m + n) → ℝ := fun r c =>
    lsScaledAugmentedMatrixBranchVector alphaStar sigma u v w
      (lsScaledAugmentedSourceBranchEquiv m n hmn c) r
  let dstar : Fin (m + n) → ℝ := fun c =>
    lsScaledAugmentedMatrixBranchEigenvalue alphaStar sigma
      (lsScaledAugmentedSourceBranchEquiv m n hmn c)
  have hQstar : IsOrthogonal (m + n) Qstar := by
    simpa [Qstar] using
      lsScaledAugmentedMatrixBranchVector_isOrthogonal_of_complete_equiv
        (alpha := alphaStar) (sigma := sigma) (A := A)
        (u := u) (v := v) (w := w)
        (lsScaledAugmentedSourceBranchEquiv m n hmn)
        hu hv hw hleft hright hnull hAv hATu hATw
        (le_of_lt halphaStar_pos) hsigma_ne
  have hdiagStar :
      lsScaledAugmentedMatrix alphaStar A =
        finiteMatMul Qstar
          (finiteMatMul (finiteDiagonal dstar) (matTranspose Qstar)) := by
    simpa [Qstar, dstar] using
      lsScaledAugmentedMatrix_branch_orthogonal_diagonalization_of_complete_equiv
        (alpha := alphaStar) (sigma := sigma) (A := A)
        (u := u) (v := v) (w := w)
        (lsScaledAugmentedSourceBranchEquiv m n hmn)
        hu hv hw hleft hright hnull hAv hATu hATw
        (le_of_lt halphaStar_pos) hsigma_ne
  have hdstar : ∀ c : Fin (m + n),
      dstar c = alphaStar ∨
        ∃ sigma0 : ℝ, sigmaMin ≤ sigma0 ∧ sigma0 ≤ sigmaMax ∧
          (dstar c = lsScaledAugmentedEigenvaluePlus alphaStar sigma0 ∨
            dstar c = lsScaledAugmentedEigenvalueMinus alphaStar sigma0) := by
    intro c
    rcases hc : lsScaledAugmentedSourceBranchEquiv m n hmn c with
      ((i | i) | k)
    · right
      refine ⟨sigma i, ?_, ?_, Or.inl ?_⟩
      · simpa [sigmaMin] using lsScaledAugmentedBranchSigmaMin_le sigma i
      · simpa [sigmaMax] using lsScaledAugmentedBranchSigma_le_max sigma i
      · simp [dstar, lsScaledAugmentedMatrixBranchEigenvalue, hc]
    · right
      refine ⟨sigma i, ?_, ?_, Or.inr ?_⟩
      · simpa [sigmaMin] using lsScaledAugmentedBranchSigmaMin_le sigma i
      · simpa [sigmaMax] using lsScaledAugmentedBranchSigma_le_max sigma i
      · simp [dstar, lsScaledAugmentedMatrixBranchEigenvalue, hc]
    · left
      simp [dstar, lsScaledAugmentedMatrixBranchEigenvalue, hc]
  have hdstarUpper : ∀ c : Fin (m + n),
      |dstar c| ≤ lsScaledAugmentedEigenvaluePlus alphaStar sigmaMax :=
    lsScaledAugmentedDiagonalBranch_abs_le_max_of_alpha_eq_div_sqrt_two
      hsigmaMin_pos hsigmaMin_le_max (by simp [alphaStar]) hdstar
  have hdstarRecip : ∀ c : Fin (m + n),
      |(dstar c)⁻¹| ≤
        |lsScaledAugmentedEigenvalueMinus alphaStar sigmaMin|⁻¹ :=
    lsScaledAugmentedDiagonalBranch_recip_abs_le_of_alpha_eq_div_sqrt_two
      hsigmaMin_pos (by simp [alphaStar]) hdstar
  have hstarUpperRatio :
      kappaC alphaStar ≤
        lsScaledAugmentedEigenvaluePlus alphaStar sigmaMax / alphaStar := by
    have hkappa :
        kappa2 (lsScaledAugmentedMatrix alphaStar A)
            (finiteMatMul Qstar
              (finiteMatMul (finiteDiagonal fun c => (dstar c)⁻¹)
                (matTranspose Qstar))) ≤
          lsScaledAugmentedEigenvaluePlus alphaStar sigmaMax *
            |lsScaledAugmentedEigenvalueMinus alphaStar sigmaMin|⁻¹ :=
      lsScaledAugmentedMatrix_kappa2_le_mul_of_orthogonal_diagonalization_inverse_candidate
        hdiagStar hQstar
        (lsScaledAugmentedEigenvaluePlus_nonneg (le_of_lt halphaStar_pos))
        hdstarUpper (inv_nonneg.mpr (abs_nonneg _)) hdstarRecip
    have hkappa' :
        kappaC alphaStar ≤
          lsScaledAugmentedEigenvaluePlus alphaStar sigmaMax *
            |lsScaledAugmentedEigenvalueMinus alphaStar sigmaMin|⁻¹ := by
      simpa [kappaC, Cinv, Qstar, dstar,
        lsScaledAugmentedSourceBranchInverseCandidate,
        lsScaledAugmentedSourceBranchEquiv] using hkappa
    have hsqrt_two_ne : Real.sqrt 2 ≠ 0 := ne_of_gt hsqrt_two_pos
    have hsigma_scale : sigmaMin = Real.sqrt 2 * alphaStar := by
      dsimp [alphaStar]
      field_simp [hsqrt_two_ne]
    have hminusStar :
        |lsScaledAugmentedEigenvalueMinus alphaStar sigmaMin| = alphaStar :=
      lsScaledAugmentedEigenvalueMinus_abs_eq_alpha_of_sigma_eq_sqrt_two_mul
        (le_of_lt halphaStar_pos) hsigma_scale
    simpa [hminusStar, div_eq_mul_inv] using hkappa'
  have hminimum : ∀ alpha : ℝ, 0 < alpha →
      kappaC alphaStar ≤ kappaC alpha := by
    intro alpha halpha
    have halpha_nonneg : 0 ≤ alpha := le_of_lt halpha
    have hinv := hInv alpha halpha
    have hminusRatio :
        lsScaledAugmentedEigenvaluePlus alpha sigmaMax /
            |lsScaledAugmentedEigenvalueMinus alpha sigmaMin| ≤
          kappaC alpha := by
      have h :=
        lsScaledAugmentedMatrix_singularPair_plus_minus_abs_ratio_le_kappa2
          (Cinv := Cinv alpha) hinv hAvMax hATuMax hAvMin hATuMin
          halpha_nonneg (ne_of_gt hsigmaMax_pos) hvMax
          (ne_of_gt hsigmaMin_pos) hvMin
      simpa [kappaC, abs_of_nonneg
        (lsScaledAugmentedEigenvaluePlus_nonneg
          (alpha := alpha) (sigma := sigmaMax) halpha_nonneg)] using h
    let k0 : Fin (m - n) := ⟨0, Nat.sub_pos_of_lt hlt⟩
    have hw0_ne : w k0 ≠ 0 := by
      intro hzero
      have hsq_zero : vecNorm2Sq (w k0) = 0 := by
        simp [hzero, vecNorm2Sq]
      linarith [hw k0]
    let z : Fin (m + n) → ℝ := Fin.append (w k0) (0 : Fin n → ℝ)
    have heigRect :=
      lsScaledAugmentedMatrix_leftNull_eigenpair alpha A (w k0)
        (hATw k0) hw0_ne
    have heig :
        finiteMatVec (lsScaledAugmentedMatrix alpha A) z =
          fun r => alpha * z r := by
      simpa [z, finiteMatVec, rectMatMulVec] using heigRect.1
    have halphaRecip : alpha⁻¹ ≤ opNorm2 (Cinv alpha) := by
      have h :=
        finiteOpNorm2Le_inverse_abs_recip_eigenvalue_le_of_isLeftInverse
          (M := lsScaledAugmentedMatrix alpha A) (Minv := Cinv alpha)
          (lambda := alpha) (c := opNorm2 (Cinv alpha)) (x := z)
          (finiteOpNorm2Le_of_opNorm2Le (Cinv alpha)
            (opNorm2Le_opNorm2 (Cinv alpha)))
          hinv.1 (ne_of_gt halpha) heigRect.2 heig
      simpa [abs_of_pos halpha] using h
    have hplus :
        lsScaledAugmentedEigenvaluePlus alpha sigmaMax ≤
          opNorm2 (lsScaledAugmentedMatrix alpha A) :=
      lsScaledAugmentedMatrix_singularPair_plus_eigenvalue_le_of_finiteOpNorm2Le
        (finiteOpNorm2Le_of_opNorm2Le (lsScaledAugmentedMatrix alpha A)
          (opNorm2Le_opNorm2 (lsScaledAugmentedMatrix alpha A)))
        hAvMax hATuMax halpha_nonneg (ne_of_gt hsigmaMax_pos) hvMax
    have halphaRatio :
        lsScaledAugmentedEigenvaluePlus alpha sigmaMax / alpha ≤
          kappaC alpha := by
      have hprod := mul_le_mul hplus halphaRecip
        (inv_nonneg.mpr halpha_nonneg)
        (opNorm2_nonneg (lsScaledAugmentedMatrix alpha A))
      simpa [kappaC, kappa2, div_eq_mul_inv] using hprod
    by_cases hsmall : alpha ≤ alphaStar
    · have hbranch :
          lsScaledAugmentedEigenvaluePlus alphaStar sigmaMax / alphaStar ≤
            lsScaledAugmentedEigenvaluePlus alpha sigmaMax / alpha :=
        higham20Eq20_19_plus_div_antitone_until_balanced halpha hsmall
      exact hstarUpperRatio.trans (hbranch.trans halphaRatio)
    · have hlarge : alphaStar ≤ alpha := le_of_not_ge hsmall
      have hDle :
          |lsScaledAugmentedEigenvalueMinus alpha sigmaMin| ≤ alphaStar := by
        simpa [alphaStar] using
          higham20Eq20_19_abs_minus_le_balanced_of_balanced_le_alpha
            hsigmaMin_pos (by simpa [alphaStar] using hlarge)
      have hDpos :
          0 < |lsScaledAugmentedEigenvalueMinus alpha sigmaMin| :=
        abs_pos.mpr
          (lsScaledAugmentedEigenvalueMinus_ne_zero_of_sigma_ne_zero
            halpha_nonneg (ne_of_gt hsigmaMin_pos))
      have hplusMono :
          lsScaledAugmentedEigenvaluePlus alphaStar sigmaMax ≤
            lsScaledAugmentedEigenvaluePlus alpha sigmaMax :=
        higham20Eq20_19_plus_mono_alpha (le_of_lt halphaStar_pos) hlarge
      have hplusStarNonneg :
          0 ≤ lsScaledAugmentedEigenvaluePlus alphaStar sigmaMax :=
        lsScaledAugmentedEigenvaluePlus_nonneg (le_of_lt halphaStar_pos)
      have hbranch :
          lsScaledAugmentedEigenvaluePlus alphaStar sigmaMax / alphaStar ≤
            lsScaledAugmentedEigenvaluePlus alpha sigmaMax /
              |lsScaledAugmentedEigenvalueMinus alpha sigmaMin| := by
        apply (div_le_div_iff₀ halphaStar_pos hDpos).2
        calc
          lsScaledAugmentedEigenvaluePlus alphaStar sigmaMax *
                |lsScaledAugmentedEigenvalueMinus alpha sigmaMin| ≤
              lsScaledAugmentedEigenvaluePlus alphaStar sigmaMax * alphaStar :=
            mul_le_mul_of_nonneg_left hDle hplusStarNonneg
          _ ≤ lsScaledAugmentedEigenvaluePlus alpha sigmaMax * alphaStar :=
            mul_le_mul_of_nonneg_right hplusMono (le_of_lt halphaStar_pos)
      exact hstarUpperRatio.trans (hbranch.trans hminusRatio)
  have hbalanced :=
    lsScaledAugmentedMatrix_kappa2_bounds_of_source_dimension_branch_data
      (m := m) (n := n) (hmn := hmn) (alpha := alphaStar) (A := A)
      (sigma := sigma) (u := u) (v := v) (w := w)
      hu hv hw hleft hright hnull hAv hATu hATw hsigma_pos
      (by simp [alphaStar, sigmaMin])
  have hupper : kappaC alphaStar ≤ 2 * kappaA := by
    simpa [kappaC, Cinv, kappaA, sigmaMax, sigmaMin] using hbalanced.2
  have hbadScalar :
      kappaA ^ 2 <
        lsScaledAugmentedEigenvaluePlus sigmaMax sigmaMax /
          |lsScaledAugmentedEigenvalueMinus sigmaMax sigmaMin| := by
    simpa [kappaA] using
      lsScaledAugmentedBranchRatio_gt_sigma_ratio_sq_of_alpha_eq_sigmaMax
        hsigmaMin_pos hsigmaMin_le_max (rfl : sigmaMax = sigmaMax)
  have hbadBridge :
      lsScaledAugmentedEigenvaluePlus sigmaMax sigmaMax /
          |lsScaledAugmentedEigenvalueMinus sigmaMax sigmaMin| ≤
        kappaC sigmaMax := by
    have h :=
      lsScaledAugmentedMatrix_singularPair_plus_minus_abs_ratio_le_kappa2
        (Cinv := Cinv sigmaMax) (hInv sigmaMax hsigmaMax_pos)
        hAvMax hATuMax hAvMin hATuMin (le_of_lt hsigmaMax_pos)
        (ne_of_gt hsigmaMax_pos) hvMax (ne_of_gt hsigmaMin_pos) hvMin
    simpa [kappaC, abs_of_nonneg
      (lsScaledAugmentedEigenvaluePlus_nonneg
        (alpha := sigmaMax) (sigma := sigmaMax) (le_of_lt hsigmaMax_pos))] using h
  exact ⟨halphaStar_pos, hlower, hminimum, hupper,
    ⟨sigmaMax, hsigmaMax_pos, hbadScalar.trans_le hbadBridge⟩⟩

end NumStability
