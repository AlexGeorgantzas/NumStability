-- Analysis/ProblemDependentStability.lean
--
-- Exact examples from Higham Chapter 1, Section 1.16.

import Mathlib.Algebra.BigOperators.Fin
import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.FinCases
import Mathlib.Tactic.NormNum
import Mathlib.Tactic.Ring
import NumStability.Analysis.Error
import NumStability.Analysis.FloatingPointArithmetic
import NumStability.Analysis.MatrixAlgebra
import NumStability.Analysis.Rounding

namespace NumStability

open scoped BigOperators

/-!
# Stability Depends on the Problem

This file records exact algebra from the upper-Hessenberg example in Higham
Chapter 1, Section 1.16. The floating-point stability and instability claims are
not closed here; the theorems below expose the exact matrix shape, right-hand
side, no-pivot diagonal product, and large first multiplier used by the example.
-/

/-- Upper-Hessenberg shape for legacy square matrices. -/
def IsUpperHessenbergMatrix (n : ℕ) (A : Fin n → Fin n → ℝ) : Prop :=
  ∀ i j : Fin n, j.val + 1 < i.val → A i j = 0

/-- Scalar diagonal update for one no-pivot GE stage on an upper-Hessenberg
matrix.  The arguments are `a_kk`, `a_{k,k-1}`, the previous superdiagonal
entry, and the previous pivot. -/
noncomputable def hessenbergDiagExactStep
    (diag subdiag prevSuper prevPivot : ℝ) : ℝ :=
  diag - subdiag * prevSuper / prevPivot

/-- Source-shaped rounded diagonal update from Higham §1.16.  The three
`eps` parameters correspond to the division/multiplication/subtraction
rounding factors in the displayed formula. -/
noncomputable def hessenbergDiagRoundedStep
    (diag subdiag prevSuperHat prevPivotHat eps1 eps2 eps3 : ℝ) : ℝ :=
  (diag - (subdiag * prevSuperHat / prevPivotHat) * (1 + eps1) * (1 + eps2)) *
    (1 + eps3)

/-- A source-shaped trace of the rounded upper-Hessenberg diagonal updates:
every updated diagonal entry is computed from the original diagonal/subdiagonal
data and the local three rounding factors. The first pivot/diagonal is not an
updated entry and is therefore not constrained by this predicate. -/
def HessenbergRoundedDiagTraceOnOriginal (n : ℕ)
    (A : Fin n → Fin n → ℝ)
    (eps1 eps2 eps3 : Fin n → ℝ)
    (prevSuperHat prevPivotHat computedDiag : Fin n → ℝ) : Prop :=
  ∀ {k km1 : Fin n}, km1.val + 1 = k.val →
    computedDiag k =
      hessenbergDiagRoundedStep (A k k) (A k km1)
        (prevSuperHat k) (prevPivotHat k) (eps1 k) (eps2 k) (eps3 k)

/-- The rounded diagonal update is exactly the unrounded upper-Hessenberg
diagonal recurrence for data whose diagonal and subdiagonal entries have been
perturbed by the displayed Higham §1.16 factors. -/
theorem hessenbergDiagRoundedStep_eq_perturbed_exactStep
    (diag subdiag prevSuperHat prevPivotHat eps1 eps2 eps3 : ℝ) :
    hessenbergDiagRoundedStep diag subdiag prevSuperHat prevPivotHat eps1 eps2 eps3 =
      hessenbergDiagExactStep
        (diag * (1 + eps3))
        (subdiag * (1 + eps1) * (1 + eps2) * (1 + eps3))
        prevSuperHat prevPivotHat := by
  unfold hessenbergDiagRoundedStep hessenbergDiagExactStep
  ring_nf

/-- The source §1.16 nearby upper-Hessenberg data obtained by changing the
diagonal and first subdiagonal entries by the factors displayed after the
rounded diagonal update formula.  Other entries are left unchanged. -/
noncomputable def hessenbergEntrywisePerturbation (n : ℕ)
    (A : Fin n → Fin n → ℝ) (eps1 eps2 eps3 : Fin n → ℝ) :
    Fin n → Fin n → ℝ :=
  fun i j =>
    if i = j then
      A i j * (1 + eps3 i)
    else if j.val + 1 = i.val then
      A i j * (1 + eps1 i) * (1 + eps2 i) * (1 + eps3 i)
    else
      A i j

@[simp] theorem hessenbergEntrywisePerturbation_diag (n : ℕ)
    (A : Fin n → Fin n → ℝ) (eps1 eps2 eps3 : Fin n → ℝ)
    (i : Fin n) :
    hessenbergEntrywisePerturbation n A eps1 eps2 eps3 i i =
      A i i * (1 + eps3 i) := by
  simp [hessenbergEntrywisePerturbation]

theorem hessenbergEntrywisePerturbation_subdiag (n : ℕ)
    (A : Fin n → Fin n → ℝ) (eps1 eps2 eps3 : Fin n → ℝ)
    {i j : Fin n} (hij : j.val + 1 = i.val) :
    hessenbergEntrywisePerturbation n A eps1 eps2 eps3 i j =
      A i j * (1 + eps1 i) * (1 + eps2 i) * (1 + eps3 i) := by
  have hne : i ≠ j := by
    intro h
    have hval : j.val + 1 = j.val := by
      subst i
      exact hij
    exact Nat.succ_ne_self j.val hval
  simp [hessenbergEntrywisePerturbation, hne, hij]

/-- A trace of the updated diagonal entries as exact upper-Hessenberg diagonal
recurrences on the single nearby matrix
`hessenbergEntrywisePerturbation n A eps1 eps2 eps3`. -/
def HessenbergExactDiagTraceOnEntrywisePerturbation (n : ℕ)
    (A : Fin n → Fin n → ℝ)
    (eps1 eps2 eps3 : Fin n → ℝ)
    (prevSuperHat prevPivotHat computedDiag : Fin n → ℝ) : Prop :=
  ∀ {k km1 : Fin n}, km1.val + 1 = k.val →
    computedDiag k =
      hessenbergDiagExactStep
        (hessenbergEntrywisePerturbation n A eps1 eps2 eps3 k k)
        (hessenbergEntrywisePerturbation n A eps1 eps2 eps3 k km1)
        (prevSuperHat k) (prevPivotHat k)

/-- The three local factors applied to a first-subdiagonal entry in the
§1.16 nearby-matrix construction. -/
noncomputable def hessenbergSubdiagPerturbationFactors {n : ℕ}
    (eps1 eps2 eps3 : Fin n → ℝ) (i : Fin n) : Fin 3 → ℝ
  | ⟨0, _⟩ => eps1 i
  | ⟨1, _⟩ => eps2 i
  | _ => eps3 i

@[simp] theorem hessenbergSubdiagPerturbationFactors_prod {n : ℕ}
    (eps1 eps2 eps3 : Fin n → ℝ) (i : Fin n) :
    (∏ r : Fin 3,
        (1 + hessenbergSubdiagPerturbationFactors eps1 eps2 eps3 i r)) =
      (1 + eps1 i) * (1 + eps2 i) * (1 + eps3 i) := by
  rw [Fin.prod_univ_three]
  simp [hessenbergSubdiagPerturbationFactors]

/-- The entrywise nearby-matrix construction preserves the upper-Hessenberg
zero pattern. -/
theorem hessenbergEntrywisePerturbation_isUpperHessenberg (n : ℕ)
    (A : Fin n → Fin n → ℝ) (eps1 eps2 eps3 : Fin n → ℝ)
    (hA : IsUpperHessenbergMatrix n A) :
    IsUpperHessenbergMatrix n
      (hessenbergEntrywisePerturbation n A eps1 eps2 eps3) := by
  intro i j hij
  have hne : i ≠ j := by
    intro h
    subst i
    exact Nat.not_succ_le_self j.val (Nat.le_of_lt hij)
  have hnotSub : ¬ j.val + 1 = i.val := by
    intro hsub
    have hlt : i.val < i.val := by
      rw [hsub] at hij
      exact hij
    exact (lt_irrefl i.val hlt)
  simp [hessenbergEntrywisePerturbation, hne, hnotSub, hA i j hij]

/-- Diagonal entries of the nearby matrix carry the displayed one-factor
relative-error witness. -/
theorem hessenbergEntrywisePerturbation_diag_signedRelErrorWitness (n : ℕ)
    (A : Fin n → Fin n → ℝ) (eps1 eps2 eps3 : Fin n → ℝ)
    (i : Fin n) :
    signedRelErrorWitness
      (hessenbergEntrywisePerturbation n A eps1 eps2 eps3 i i)
      (A i i) (eps3 i) := by
  simp [signedRelErrorWitness]

/-- Diagonal entries of the nearby matrix differ from the original entries by
at most one unit-roundoff factor times the entry magnitude. -/
theorem hessenbergEntrywisePerturbation_diag_abs_error_le (fp : FPModel)
    (n : ℕ) (A : Fin n → Fin n → ℝ)
    (eps1 eps2 eps3 : Fin n → ℝ)
    (heps3 : ∀ i : Fin n, |eps3 i| ≤ fp.u) (i : Fin n) :
    |hessenbergEntrywisePerturbation n A eps1 eps2 eps3 i i - A i i| ≤
      fp.u * |A i i| := by
  have hdiff :
      hessenbergEntrywisePerturbation n A eps1 eps2 eps3 i i - A i i =
        A i i * eps3 i := by
    simp [hessenbergEntrywisePerturbation]
    ring
  calc
    |hessenbergEntrywisePerturbation n A eps1 eps2 eps3 i i - A i i|
        = |eps3 i| * |A i i| := by rw [hdiff, abs_mul, mul_comm]
    _ ≤ fp.u * |A i i| :=
        mul_le_mul_of_nonneg_right (heps3 i) (abs_nonneg _)

/-- First-subdiagonal entries of the nearby matrix carry a three-factor
relative-error witness bounded by `gamma fp 3`. -/
theorem hessenbergEntrywisePerturbation_subdiag_signedRelErrorWitness_exists
    (fp : FPModel) (n : ℕ) (A : Fin n → Fin n → ℝ)
    (eps1 eps2 eps3 : Fin n → ℝ)
    (heps1 : ∀ i : Fin n, |eps1 i| ≤ fp.u)
    (heps2 : ∀ i : Fin n, |eps2 i| ≤ fp.u)
    (heps3 : ∀ i : Fin n, |eps3 i| ≤ fp.u)
    (hgamma : gammaValid fp 3) {i j : Fin n} (hij : j.val + 1 = i.val) :
    ∃ theta : ℝ, |theta| ≤ gamma fp 3 ∧
      signedRelErrorWitness
        (hessenbergEntrywisePerturbation n A eps1 eps2 eps3 i j)
        (A i j) theta := by
  let δ : Fin 3 → ℝ := hessenbergSubdiagPerturbationFactors eps1 eps2 eps3 i
  have hδ : ∀ r : Fin 3, |δ r| ≤ fp.u := by
    intro r
    fin_cases r <;> simp [δ, hessenbergSubdiagPerturbationFactors,
      heps1 i, heps2 i, heps3 i]
  rcases prod_error_bound fp 3 δ hδ hgamma with ⟨theta, htheta, hprod⟩
  refine ⟨theta, htheta, ?_⟩
  rw [hessenbergEntrywisePerturbation_subdiag n A eps1 eps2 eps3 hij]
  unfold signedRelErrorWitness
  rw [← hprod]
  simp [δ]
  ring

/-- First-subdiagonal entries of the nearby matrix differ from the original
entries by at most `gamma fp 3` times the entry magnitude. -/
theorem hessenbergEntrywisePerturbation_subdiag_abs_error_le_gamma
    (fp : FPModel) (n : ℕ) (A : Fin n → Fin n → ℝ)
    (eps1 eps2 eps3 : Fin n → ℝ)
    (heps1 : ∀ i : Fin n, |eps1 i| ≤ fp.u)
    (heps2 : ∀ i : Fin n, |eps2 i| ≤ fp.u)
    (heps3 : ∀ i : Fin n, |eps3 i| ≤ fp.u)
    (hgamma : gammaValid fp 3) {i j : Fin n} (hij : j.val + 1 = i.val) :
    |hessenbergEntrywisePerturbation n A eps1 eps2 eps3 i j - A i j| ≤
      gamma fp 3 * |A i j| := by
  rcases hessenbergEntrywisePerturbation_subdiag_signedRelErrorWitness_exists
      fp n A eps1 eps2 eps3 heps1 heps2 heps3 hgamma hij with
    ⟨theta, htheta, hthetaWitness⟩
  have hdiff :
      hessenbergEntrywisePerturbation n A eps1 eps2 eps3 i j - A i j =
        A i j * theta := by
    unfold signedRelErrorWitness at hthetaWitness
    rw [hthetaWitness]
    ring
  calc
    |hessenbergEntrywisePerturbation n A eps1 eps2 eps3 i j - A i j|
        = |theta| * |A i j| := by rw [hdiff, abs_mul, mul_comm]
    _ ≤ gamma fp 3 * |A i j| :=
        mul_le_mul_of_nonneg_right htheta (abs_nonneg _)

/-- Every entry of the §1.16 nearby matrix differs from the original entry by
at most `gamma fp 3` times the original entry magnitude.  Diagonal entries use
`u <= gamma_3`; first-subdiagonal entries use the three-factor product lemma;
all other entries are unchanged. -/
theorem hessenbergEntrywisePerturbation_abs_error_le_gamma_three
    (fp : FPModel) (n : ℕ) (A : Fin n → Fin n → ℝ)
    (eps1 eps2 eps3 : Fin n → ℝ)
    (heps1 : ∀ i : Fin n, |eps1 i| ≤ fp.u)
    (heps2 : ∀ i : Fin n, |eps2 i| ≤ fp.u)
    (heps3 : ∀ i : Fin n, |eps3 i| ≤ fp.u)
    (hgamma : gammaValid fp 3) (i j : Fin n) :
    |hessenbergEntrywisePerturbation n A eps1 eps2 eps3 i j - A i j| ≤
      gamma fp 3 * |A i j| := by
  by_cases hdiag : i = j
  · subst j
    have hu_le : fp.u ≤ gamma fp 3 :=
      u_le_gamma fp (by norm_num) hgamma
    have hdiagBound :=
      hessenbergEntrywisePerturbation_diag_abs_error_le
        fp n A eps1 eps2 eps3 heps3 i
    exact hdiagBound.trans
      (mul_le_mul_of_nonneg_right hu_le (abs_nonneg _))
  · by_cases hsub : j.val + 1 = i.val
    · exact hessenbergEntrywisePerturbation_subdiag_abs_error_le_gamma
        fp n A eps1 eps2 eps3 heps1 heps2 heps3 hgamma hsub
    · have hsame :
          hessenbergEntrywisePerturbation n A eps1 eps2 eps3 i j = A i j := by
        simp [hessenbergEntrywisePerturbation, hdiag, hsub]
      have hnonneg : 0 ≤ gamma fp 3 * |A i j| :=
        mul_nonneg (gamma_nonneg fp hgamma) (abs_nonneg _)
      simpa [hsame] using hnonneg

/-- Matrix-level wrapper for the displayed §1.16 sentence: the rounded
diagonal update is exactly the unrounded update using the corresponding
diagonal and subdiagonal entries of the nearby entrywise-perturbed matrix. -/
theorem hessenbergDiagRoundedStep_eq_entrywisePerturbedExactStep (n : ℕ)
    (A : Fin n → Fin n → ℝ) (eps1 eps2 eps3 : Fin n → ℝ)
    {k km1 : Fin n} (hkm1 : km1.val + 1 = k.val)
    (prevSuperHat prevPivotHat : ℝ) :
    hessenbergDiagRoundedStep (A k k) (A k km1)
        prevSuperHat prevPivotHat (eps1 k) (eps2 k) (eps3 k) =
      hessenbergDiagExactStep
        (hessenbergEntrywisePerturbation n A eps1 eps2 eps3 k k)
        (hessenbergEntrywisePerturbation n A eps1 eps2 eps3 k km1)
        prevSuperHat prevPivotHat := by
  rw [hessenbergDiagRoundedStep_eq_perturbed_exactStep]
  rw [hessenbergEntrywisePerturbation_diag]
  rw [hessenbergEntrywisePerturbation_subdiag n A eps1 eps2 eps3 hkm1]

/-- All rounded upper-Hessenberg diagonal updates in a trace can be read as
exact diagonal recurrences on one global entrywise-perturbed matrix.  This is
the all-updated-diagonals wrapper around the pointwise §1.16 nearby-matrix
identity; it does not by itself prove a primitive floating-point GE trace or
the final determinant product. -/
theorem hessenbergRoundedDiagTraceOnOriginal_exactTraceOnEntrywisePerturbation
    (n : ℕ) (A : Fin n → Fin n → ℝ)
    (eps1 eps2 eps3 : Fin n → ℝ)
    (prevSuperHat prevPivotHat computedDiag : Fin n → ℝ)
    (htrace : HessenbergRoundedDiagTraceOnOriginal n A eps1 eps2 eps3
      prevSuperHat prevPivotHat computedDiag) :
    HessenbergExactDiagTraceOnEntrywisePerturbation n A eps1 eps2 eps3
      prevSuperHat prevPivotHat computedDiag := by
  intro k km1 hkm1
  rw [htrace hkm1]
  exact hessenbergDiagRoundedStep_eq_entrywisePerturbedExactStep
    n A eps1 eps2 eps3 hkm1 (prevSuperHat k) (prevPivotHat k)

/-- The determinant product obtained by multiplying computed upper-triangular
diagonal entries with one final relative factor per multiplication. -/
noncomputable def hessenbergDetRoundedProduct (n : ℕ)
    (diag eta : Fin n → ℝ) : ℝ :=
  (∏ i : Fin n, diag i) * ∏ i : Fin n, (1 + eta i)

/-- The final determinant-product formula in Higham §1.16 is a signed relative
error witness around the exact product of the computed diagonal entries. -/
theorem hessenbergDetRoundedProduct_signedRelError (n : ℕ)
    (diag eta : Fin n → ℝ) :
    signedRelErrorWitness
      (hessenbergDetRoundedProduct n diag eta)
      (∏ i : Fin n, diag i)
      ((∏ i : Fin n, (1 + eta i)) - 1) := by
  unfold hessenbergDetRoundedProduct signedRelErrorWitness
  ring

/-- If the computed diagonal product is nonzero, the determinant-product
relative error is exactly the magnitude of the accumulated final product
factor. -/
theorem hessenbergDetRoundedProduct_relError_eq (n : ℕ)
    (diag eta : Fin n → ℝ)
    (hdiag : (∏ i : Fin n, diag i) ≠ 0) :
    relError (hessenbergDetRoundedProduct n diag eta)
      (∏ i : Fin n, diag i) =
        |(∏ i : Fin n, (1 + eta i)) - 1| := by
  exact relError_eq_abs_of_signedRelErrorWitness hdiag
    (hessenbergDetRoundedProduct_signedRelError n diag eta)

/-- With the standard product model, the final determinant-product relative
error is bounded by `gamma fp n`.  This is the formal version of the §1.16
claim that the final product introduces only a tiny relative perturbation of
the determinant of the nearby matrix represented by the computed diagonal. -/
theorem hessenbergDetRoundedProduct_relError_le_gamma (fp : FPModel) (n : ℕ)
    (diag eta : Fin n → ℝ)
    (heta : ∀ i : Fin n, |eta i| ≤ fp.u)
    (hgamma : gammaValid fp n)
    (hdiag : (∏ i : Fin n, diag i) ≠ 0) :
    relError (hessenbergDetRoundedProduct n diag eta)
      (∏ i : Fin n, diag i) ≤ gamma fp n := by
  rcases prod_error_bound fp n eta heta hgamma with ⟨theta, htheta, hprod⟩
  rw [hessenbergDetRoundedProduct_relError_eq n diag eta hdiag]
  have htheta_eq : (∏ i : Fin n, (1 + eta i)) - 1 = theta := by
    rw [hprod]
    ring
  rw [htheta_eq]
  exact htheta

/-- If a no-pivot upper-Hessenberg elimination path has determinant equal to
the product of its computed diagonal entries, the final rounded determinant
product is within `gamma_n` of that determinant.  This packages the source
§1.16 mixed-stability sentence after the displayed product formula. -/
theorem hessenbergDetRoundedProduct_relError_le_gamma_of_det_eq_diag_prod
    (fp : FPModel) (n : ℕ) (A : Matrix (Fin n) (Fin n) ℝ)
    (diag eta : Fin n → ℝ)
    (hdet : Matrix.det A = ∏ i : Fin n, diag i)
    (heta : ∀ i : Fin n, |eta i| ≤ fp.u)
    (hgamma : gammaValid fp n)
    (hdiag : (∏ i : Fin n, diag i) ≠ 0) :
    relError (hessenbergDetRoundedProduct n diag eta)
      (Matrix.det A) ≤ gamma fp n := by
  rw [hdet]
  exact hessenbergDetRoundedProduct_relError_le_gamma
    fp n diag eta heta hgamma hdiag

/-- Source-shaped §1.16 determinant assembly bridge for one nearby matrix.  Once
the rounded diagonal trace on the original matrix is available and the
determinant-product invariant for the corresponding nearby matrix has been
proved, the final rounded determinant product is within `gamma_n` of the
determinant of that nearby matrix.  The determinant-product invariant is the
remaining Gaussian-elimination assembly obligation, exposed here as `hdet`. -/
theorem hessenbergRoundedDiagTraceOnOriginal_nearbyDet_relError_le_gamma
    (fp : FPModel) (n : ℕ) (A : Fin n → Fin n → ℝ)
    (eps1 eps2 eps3 : Fin n → ℝ)
    (prevSuperHat prevPivotHat computedDiag eta : Fin n → ℝ)
    (htrace : HessenbergRoundedDiagTraceOnOriginal n A eps1 eps2 eps3
      prevSuperHat prevPivotHat computedDiag)
    (hdet : Matrix.det
        (hessenbergEntrywisePerturbation n A eps1 eps2 eps3 :
          Matrix (Fin n) (Fin n) ℝ) = ∏ i : Fin n, computedDiag i)
    (heta : ∀ i : Fin n, |eta i| ≤ fp.u)
    (hgamma : gammaValid fp n)
    (hdiag : (∏ i : Fin n, computedDiag i) ≠ 0) :
    HessenbergExactDiagTraceOnEntrywisePerturbation n A eps1 eps2 eps3
        prevSuperHat prevPivotHat computedDiag ∧
      relError (hessenbergDetRoundedProduct n computedDiag eta)
        (Matrix.det
          (hessenbergEntrywisePerturbation n A eps1 eps2 eps3 :
            Matrix (Fin n) (Fin n) ℝ)) ≤ gamma fp n := by
  constructor
  · exact hessenbergRoundedDiagTraceOnOriginal_exactTraceOnEntrywisePerturbation
      n A eps1 eps2 eps3 prevSuperHat prevPivotHat computedDiag htrace
  · exact hessenbergDetRoundedProduct_relError_le_gamma_of_det_eq_diag_prod
      fp n
      (hessenbergEntrywisePerturbation n A eps1 eps2 eps3 :
        Matrix (Fin n) (Fin n) ℝ)
      computedDiag eta hdet heta hgamma hdiag

/-- First pivot in the generic 4-by-4 no-pivot upper-Hessenberg elimination
model. -/
noncomputable def hessenberg4NoPivotPivot0
    (A : Matrix (Fin 4) (Fin 4) ℝ) : ℝ :=
  A 0 0

/-- First multiplier in the generic 4-by-4 no-pivot upper-Hessenberg
elimination model. -/
noncomputable def hessenberg4NoPivotMultiplier10
    (A : Matrix (Fin 4) (Fin 4) ℝ) : ℝ :=
  A 1 0 / hessenberg4NoPivotPivot0 A

/-- Second pivot after the first no-pivot upper-Hessenberg elimination step. -/
noncomputable def hessenberg4NoPivotDiag1
    (A : Matrix (Fin 4) (Fin 4) ℝ) : ℝ :=
  A 1 1 - hessenberg4NoPivotMultiplier10 A * A 0 1

/-- Updated `(1,2)` superdiagonal entry after the first step. -/
noncomputable def hessenberg4NoPivotSuper12
    (A : Matrix (Fin 4) (Fin 4) ℝ) : ℝ :=
  A 1 2 - hessenberg4NoPivotMultiplier10 A * A 0 2

/-- Updated `(1,3)` superdiagonal entry after the first step. -/
noncomputable def hessenberg4NoPivotSuper13
    (A : Matrix (Fin 4) (Fin 4) ℝ) : ℝ :=
  A 1 3 - hessenberg4NoPivotMultiplier10 A * A 0 3

/-- Second multiplier in the generic 4-by-4 no-pivot upper-Hessenberg
elimination model. -/
noncomputable def hessenberg4NoPivotMultiplier21
    (A : Matrix (Fin 4) (Fin 4) ℝ) : ℝ :=
  A 2 1 / hessenberg4NoPivotDiag1 A

/-- Third pivot after the second no-pivot upper-Hessenberg elimination step. -/
noncomputable def hessenberg4NoPivotDiag2
    (A : Matrix (Fin 4) (Fin 4) ℝ) : ℝ :=
  A 2 2 - hessenberg4NoPivotMultiplier21 A * hessenberg4NoPivotSuper12 A

/-- Updated `(2,3)` superdiagonal entry after the second step. -/
noncomputable def hessenberg4NoPivotSuper23
    (A : Matrix (Fin 4) (Fin 4) ℝ) : ℝ :=
  A 2 3 - hessenberg4NoPivotMultiplier21 A * hessenberg4NoPivotSuper13 A

/-- Third multiplier in the generic 4-by-4 no-pivot upper-Hessenberg
elimination model. -/
noncomputable def hessenberg4NoPivotMultiplier32
    (A : Matrix (Fin 4) (Fin 4) ℝ) : ℝ :=
  A 3 2 / hessenberg4NoPivotDiag2 A

/-- Fourth pivot after the third no-pivot upper-Hessenberg elimination step. -/
noncomputable def hessenberg4NoPivotDiag3
    (A : Matrix (Fin 4) (Fin 4) ℝ) : ℝ :=
  A 3 3 - hessenberg4NoPivotMultiplier32 A * hessenberg4NoPivotSuper23 A

/-- Diagonal of the generic 4-by-4 no-pivot upper-Hessenberg endpoint. -/
noncomputable def hessenberg4NoPivotDiag
    (A : Matrix (Fin 4) (Fin 4) ℝ) : Fin 4 → ℝ
  | ⟨0, _⟩ => hessenberg4NoPivotPivot0 A
  | ⟨1, _⟩ => hessenberg4NoPivotDiag1 A
  | ⟨2, _⟩ => hessenberg4NoPivotDiag2 A
  | ⟨3, _⟩ => hessenberg4NoPivotDiag3 A

/-- Generic upper-triangular endpoint obtained by symbolic no-pivot elimination
on a 4-by-4 upper-Hessenberg matrix.  This definition records the endpoint
shape; determinant preservation from a source matrix to this endpoint is a
separate obligation. -/
noncomputable def hessenberg4NoPivotEndpoint
    (A : Matrix (Fin 4) (Fin 4) ℝ) : Matrix (Fin 4) (Fin 4) ℝ
  | ⟨0, _⟩, ⟨0, _⟩ => A 0 0
  | ⟨0, _⟩, ⟨1, _⟩ => A 0 1
  | ⟨0, _⟩, ⟨2, _⟩ => A 0 2
  | ⟨0, _⟩, ⟨3, _⟩ => A 0 3
  | ⟨1, _⟩, ⟨0, _⟩ => 0
  | ⟨1, _⟩, ⟨1, _⟩ => hessenberg4NoPivotDiag1 A
  | ⟨1, _⟩, ⟨2, _⟩ => hessenberg4NoPivotSuper12 A
  | ⟨1, _⟩, ⟨3, _⟩ => hessenberg4NoPivotSuper13 A
  | ⟨2, _⟩, ⟨0, _⟩ => 0
  | ⟨2, _⟩, ⟨1, _⟩ => 0
  | ⟨2, _⟩, ⟨2, _⟩ => hessenberg4NoPivotDiag2 A
  | ⟨2, _⟩, ⟨3, _⟩ => hessenberg4NoPivotSuper23 A
  | ⟨3, _⟩, ⟨0, _⟩ => 0
  | ⟨3, _⟩, ⟨1, _⟩ => 0
  | ⟨3, _⟩, ⟨2, _⟩ => 0
  | ⟨3, _⟩, ⟨3, _⟩ => hessenberg4NoPivotDiag3 A

/-- The generic 4-by-4 no-pivot endpoint is upper triangular. -/
theorem hessenberg4NoPivotEndpoint_blockTriangular
    (A : Matrix (Fin 4) (Fin 4) ℝ) :
    (hessenberg4NoPivotEndpoint A).BlockTriangular id := by
  intro i j hij
  fin_cases i <;> fin_cases j <;>
    simp [hessenberg4NoPivotEndpoint] at hij ⊢

/-- The determinant of the generic 4-by-4 no-pivot upper-Hessenberg endpoint
is the product of its symbolic diagonal entries. -/
theorem hessenberg4NoPivotEndpoint_det_eq_diag_prod
    (A : Matrix (Fin 4) (Fin 4) ℝ) :
    Matrix.det (hessenberg4NoPivotEndpoint A) =
      ∏ i : Fin 4, hessenberg4NoPivotDiag A i := by
  rw [Matrix.det_of_upperTriangular
    (hessenberg4NoPivotEndpoint_blockTriangular A)]
  rw [Fin.prod_univ_four]
  rw [Fin.prod_univ_four]
  simp [hessenberg4NoPivotEndpoint, hessenberg4NoPivotDiag,
    hessenberg4NoPivotPivot0]

/-- Previous superdiagonal entry used by the generic 4-by-4 no-pivot diagonal
recurrence. -/
noncomputable def hessenberg4NoPivotPrevSuper
    (A : Matrix (Fin 4) (Fin 4) ℝ) : Fin 4 → ℝ
  | ⟨0, _⟩ => 0
  | ⟨1, _⟩ => A 0 1
  | ⟨2, _⟩ => hessenberg4NoPivotSuper12 A
  | ⟨3, _⟩ => hessenberg4NoPivotSuper23 A

/-- Previous pivot used by the generic 4-by-4 no-pivot diagonal recurrence. -/
noncomputable def hessenberg4NoPivotPrevPivot
    (A : Matrix (Fin 4) (Fin 4) ℝ) : Fin 4 → ℝ
  | ⟨0, _⟩ => 1
  | ⟨1, _⟩ => hessenberg4NoPivotPivot0 A
  | ⟨2, _⟩ => hessenberg4NoPivotDiag1 A
  | ⟨3, _⟩ => hessenberg4NoPivotDiag2 A

/-- The diagonal of the generic 4-by-4 no-pivot endpoint follows the exact
upper-Hessenberg diagonal recurrence at each updated row. -/
theorem hessenberg4NoPivotDiag_exactTraceOnMatrix
    (A : Matrix (Fin 4) (Fin 4) ℝ) :
    ∀ {k km1 : Fin 4}, km1.val + 1 = k.val →
      hessenberg4NoPivotDiag A k =
        hessenbergDiagExactStep (A k k) (A k km1)
          (hessenberg4NoPivotPrevSuper A k)
          (hessenberg4NoPivotPrevPivot A k) := by
  intro k km1 hkm1
  fin_cases k <;> fin_cases km1 <;> norm_num at hkm1
  · simp [hessenberg4NoPivotDiag, hessenberg4NoPivotPrevSuper,
      hessenberg4NoPivotPrevPivot, hessenberg4NoPivotPivot0,
      hessenberg4NoPivotMultiplier10, hessenberg4NoPivotDiag1,
      hessenbergDiagExactStep]
    ring_nf
  · simp [hessenberg4NoPivotDiag, hessenberg4NoPivotPrevSuper,
      hessenberg4NoPivotPrevPivot, hessenberg4NoPivotMultiplier21,
      hessenberg4NoPivotDiag2, hessenbergDiagExactStep]
    ring_nf
  · simp [hessenberg4NoPivotDiag, hessenberg4NoPivotPrevSuper,
      hessenberg4NoPivotPrevPivot, hessenberg4NoPivotMultiplier32,
      hessenberg4NoPivotDiag3, hessenbergDiagExactStep]
    ring_nf

/-- The generic 4-by-4 no-pivot endpoint diagonal gives an exact trace for the
source-shaped entrywise perturbation matrix from Higham §1.16. -/
theorem hessenberg4NoPivotDiag_exactTraceOnEntrywisePerturbation
    (A : Fin 4 → Fin 4 → ℝ) (eps1 eps2 eps3 : Fin 4 → ℝ) :
    HessenbergExactDiagTraceOnEntrywisePerturbation 4 A eps1 eps2 eps3
      (hessenberg4NoPivotPrevSuper
        (hessenbergEntrywisePerturbation 4 A eps1 eps2 eps3 :
          Matrix (Fin 4) (Fin 4) ℝ))
      (hessenberg4NoPivotPrevPivot
        (hessenbergEntrywisePerturbation 4 A eps1 eps2 eps3 :
          Matrix (Fin 4) (Fin 4) ℝ))
      (hessenberg4NoPivotDiag
        (hessenbergEntrywisePerturbation 4 A eps1 eps2 eps3 :
          Matrix (Fin 4) (Fin 4) ℝ)) := by
  intro k km1 hkm1
  exact hessenberg4NoPivotDiag_exactTraceOnMatrix
    (hessenbergEntrywisePerturbation 4 A eps1 eps2 eps3 :
      Matrix (Fin 4) (Fin 4) ℝ) hkm1

/-- First symbolic no-pivot elimination stage for a generic 4-by-4
upper-Hessenberg matrix. -/
noncomputable def hessenberg4NoPivotStage1
    (A : Matrix (Fin 4) (Fin 4) ℝ) : Matrix (Fin 4) (Fin 4) ℝ :=
  A.updateRow 1 (A 1 - hessenberg4NoPivotMultiplier10 A • A 0)

/-- Second symbolic no-pivot elimination stage for a generic 4-by-4
upper-Hessenberg matrix. -/
noncomputable def hessenberg4NoPivotStage2
    (A : Matrix (Fin 4) (Fin 4) ℝ) : Matrix (Fin 4) (Fin 4) ℝ :=
  (hessenberg4NoPivotStage1 A).updateRow 2
    ((hessenberg4NoPivotStage1 A) 2 -
      hessenberg4NoPivotMultiplier21 A • (hessenberg4NoPivotStage1 A) 1)

/-- Third symbolic no-pivot elimination stage for a generic 4-by-4
upper-Hessenberg matrix. -/
noncomputable def hessenberg4NoPivotStage3
    (A : Matrix (Fin 4) (Fin 4) ℝ) : Matrix (Fin 4) (Fin 4) ℝ :=
  (hessenberg4NoPivotStage2 A).updateRow 3
    ((hessenberg4NoPivotStage2 A) 3 -
      hessenberg4NoPivotMultiplier32 A • (hessenberg4NoPivotStage2 A) 2)

/-- The first symbolic row-elimination stage preserves determinant. -/
theorem hessenberg4NoPivotStage1_det_eq
    (A : Matrix (Fin 4) (Fin 4) ℝ) :
    Matrix.det (hessenberg4NoPivotStage1 A) = Matrix.det A := by
  simpa [hessenberg4NoPivotStage1, sub_eq_add_neg, Pi.sub_apply]
    using Matrix.det_updateRow_add_smul_self A
      (i := (1 : Fin 4)) (j := (0 : Fin 4)) (by decide)
      (-hessenberg4NoPivotMultiplier10 A)

/-- The first two symbolic row-elimination stages preserve determinant. -/
theorem hessenberg4NoPivotStage2_det_eq
    (A : Matrix (Fin 4) (Fin 4) ℝ) :
    Matrix.det (hessenberg4NoPivotStage2 A) = Matrix.det A := by
  calc
    Matrix.det (hessenberg4NoPivotStage2 A) =
        Matrix.det (hessenberg4NoPivotStage1 A) := by
      simpa [hessenberg4NoPivotStage2, sub_eq_add_neg, Pi.sub_apply]
        using Matrix.det_updateRow_add_smul_self
          (hessenberg4NoPivotStage1 A)
          (i := (2 : Fin 4)) (j := (1 : Fin 4)) (by decide)
          (-hessenberg4NoPivotMultiplier21 A)
    _ = Matrix.det A := hessenberg4NoPivotStage1_det_eq A

/-- The three symbolic row-elimination stages preserve determinant. -/
theorem hessenberg4NoPivotStage3_det_eq
    (A : Matrix (Fin 4) (Fin 4) ℝ) :
    Matrix.det (hessenberg4NoPivotStage3 A) = Matrix.det A := by
  calc
    Matrix.det (hessenberg4NoPivotStage3 A) =
        Matrix.det (hessenberg4NoPivotStage2 A) := by
      simpa [hessenberg4NoPivotStage3, sub_eq_add_neg, Pi.sub_apply]
        using Matrix.det_updateRow_add_smul_self
          (hessenberg4NoPivotStage2 A)
          (i := (3 : Fin 4)) (j := (2 : Fin 4)) (by decide)
          (-hessenberg4NoPivotMultiplier32 A)
    _ = Matrix.det A := hessenberg4NoPivotStage2_det_eq A

/-- Under the upper-Hessenberg zero pattern and nonzero pivots, the three
symbolic row-elimination stages are exactly the generic no-pivot endpoint. -/
theorem hessenberg4NoPivotStage3_eq_endpoint
    (A : Matrix (Fin 4) (Fin 4) ℝ)
    (h20 : A 2 0 = 0) (h30 : A 3 0 = 0) (h31 : A 3 1 = 0)
    (hp0 : hessenberg4NoPivotPivot0 A ≠ 0)
    (hp1 : hessenberg4NoPivotDiag1 A ≠ 0)
    (hp2 : hessenberg4NoPivotDiag2 A ≠ 0) :
    hessenberg4NoPivotStage3 A = hessenberg4NoPivotEndpoint A := by
  have hp0' : A 0 0 ≠ 0 := by
    simpa [hessenberg4NoPivotPivot0] using hp0
  have hdiag1_scale :
      A 0 0 * hessenberg4NoPivotDiag1 A =
        A 0 0 * A 1 1 - A 1 0 * A 0 1 := by
    unfold hessenberg4NoPivotDiag1 hessenberg4NoPivotMultiplier10
      hessenberg4NoPivotPivot0
    field_simp [hp0']
  have hp1cross : A 0 0 * A 1 1 - A 1 0 * A 0 1 ≠ 0 := by
    intro h
    apply hp1
    have hmul : A 0 0 * hessenberg4NoPivotDiag1 A = 0 := by
      rw [hdiag1_scale, h]
    exact (mul_eq_zero.mp hmul).resolve_left hp0'
  have hdiag2_eq :
      hessenberg4NoPivotDiag2 A =
        A 2 2 - A 2 1 * A 0 0 * A 1 2 *
            (A 0 0 * A 1 1 - A 1 0 * A 0 1)⁻¹ +
          A 2 1 * A 1 0 * A 0 2 *
            (A 0 0 * A 1 1 - A 1 0 * A 0 1)⁻¹ := by
    unfold hessenberg4NoPivotDiag2 hessenberg4NoPivotMultiplier21
      hessenberg4NoPivotSuper12 hessenberg4NoPivotDiag1
      hessenberg4NoPivotMultiplier10 hessenberg4NoPivotPivot0
    field_simp [hp0', hp1cross]
    ring
  have hp2' :
      A 2 2 - A 2 1 * A 0 0 * A 1 2 *
            (A 0 0 * A 1 1 - A 1 0 * A 0 1)⁻¹ +
          A 2 1 * A 1 0 * A 0 2 *
            (A 0 0 * A 1 1 - A 1 0 * A 0 1)⁻¹ ≠ 0 := by
    intro h
    apply hp2
    rw [hdiag2_eq, h]
  have hcancel0 :
      A 1 0 - hessenberg4NoPivotMultiplier10 A * A 0 0 = 0 := by
    unfold hessenberg4NoPivotMultiplier10 hessenberg4NoPivotPivot0
    field_simp [hp0']
    ring
  have hcancel1 :
      A 2 1 - hessenberg4NoPivotMultiplier21 A *
        hessenberg4NoPivotDiag1 A = 0 := by
    unfold hessenberg4NoPivotMultiplier21
    field_simp [hp1]
    ring
  have hcancel2 :
      A 3 2 - hessenberg4NoPivotMultiplier32 A *
        hessenberg4NoPivotDiag2 A = 0 := by
    unfold hessenberg4NoPivotMultiplier32
    field_simp [hp2]
    ring
  have hcancel1_expanded :
      A 2 1 - hessenberg4NoPivotMultiplier21 A * A 1 1 +
          hessenberg4NoPivotMultiplier21 A *
            hessenberg4NoPivotMultiplier10 A * A 0 1 * (Nat.rawCast 1 : ℝ) =
        0 := by
    calc
      A 2 1 - hessenberg4NoPivotMultiplier21 A * A 1 1 +
          hessenberg4NoPivotMultiplier21 A *
            hessenberg4NoPivotMultiplier10 A * A 0 1 * (Nat.rawCast 1 : ℝ)
          = A 2 1 - hessenberg4NoPivotMultiplier21 A *
              hessenberg4NoPivotDiag1 A := by
            simp [hessenberg4NoPivotDiag1]
            ring
      _ = 0 := hcancel1
  have hcancel2_expanded :
      A 3 2 - hessenberg4NoPivotMultiplier32 A * A 2 2 +
          (hessenberg4NoPivotMultiplier32 A *
              hessenberg4NoPivotMultiplier21 A * A 1 2 * (Nat.rawCast 1 : ℝ) -
            hessenberg4NoPivotMultiplier32 A *
              hessenberg4NoPivotMultiplier21 A *
                hessenberg4NoPivotMultiplier10 A * A 0 2) =
        0 := by
    calc
      A 3 2 - hessenberg4NoPivotMultiplier32 A * A 2 2 +
          (hessenberg4NoPivotMultiplier32 A *
              hessenberg4NoPivotMultiplier21 A * A 1 2 * (Nat.rawCast 1 : ℝ) -
            hessenberg4NoPivotMultiplier32 A *
              hessenberg4NoPivotMultiplier21 A *
                hessenberg4NoPivotMultiplier10 A * A 0 2)
          = A 3 2 - hessenberg4NoPivotMultiplier32 A *
              hessenberg4NoPivotDiag2 A := by
            simp [hessenberg4NoPivotDiag2, hessenberg4NoPivotSuper12]
            ring
      _ = 0 := hcancel2
  ext i j
  fin_cases i <;> fin_cases j <;>
    simp [hessenberg4NoPivotStage3, hessenberg4NoPivotStage2,
      hessenberg4NoPivotStage1, hessenberg4NoPivotEndpoint,
      hessenberg4NoPivotDiag1, hessenberg4NoPivotSuper12,
      hessenberg4NoPivotSuper13, hessenberg4NoPivotDiag2,
      hessenberg4NoPivotSuper23, hessenberg4NoPivotDiag3,
      h20, h30, h31, hcancel0] <;>
    try ring_nf
  · simpa only [Nat.cast_one, mul_one] using hcancel1_expanded
  · right
    simpa only [Nat.cast_one, mul_one] using hcancel1_expanded
  · simpa only [Nat.cast_one, mul_one] using hcancel2_expanded

/-- For a generic 4-by-4 upper-Hessenberg no-pivot elimination path with
nonzero pivots, the symbolic endpoint has the same determinant as the source
matrix. -/
theorem hessenberg4NoPivotEndpoint_det_eq_of_upperHessenberg
    (A : Matrix (Fin 4) (Fin 4) ℝ)
    (h20 : A 2 0 = 0) (h30 : A 3 0 = 0) (h31 : A 3 1 = 0)
    (hp0 : hessenberg4NoPivotPivot0 A ≠ 0)
    (hp1 : hessenberg4NoPivotDiag1 A ≠ 0)
    (hp2 : hessenberg4NoPivotDiag2 A ≠ 0) :
    Matrix.det (hessenberg4NoPivotEndpoint A) = Matrix.det A := by
  rw [← hessenberg4NoPivotStage3_eq_endpoint A h20 h30 h31 hp0 hp1 hp2]
  exact hessenberg4NoPivotStage3_det_eq A

/-- For a generic 4-by-4 upper-Hessenberg no-pivot elimination path with
nonzero pivots, the source determinant equals the symbolic endpoint diagonal
product. -/
theorem hessenberg4NoPivot_det_eq_diag_prod_of_upperHessenberg
    (A : Matrix (Fin 4) (Fin 4) ℝ)
    (h20 : A 2 0 = 0) (h30 : A 3 0 = 0) (h31 : A 3 1 = 0)
    (hp0 : hessenberg4NoPivotPivot0 A ≠ 0)
    (hp1 : hessenberg4NoPivotDiag1 A ≠ 0)
    (hp2 : hessenberg4NoPivotDiag2 A ≠ 0) :
    Matrix.det A = ∏ i : Fin 4, hessenberg4NoPivotDiag A i := by
  rw [← hessenberg4NoPivotEndpoint_det_eq_of_upperHessenberg
    A h20 h30 h31 hp0 hp1 hp2]
  exact hessenberg4NoPivotEndpoint_det_eq_diag_prod A

/-- The nearby matrix from the source-shaped §1.16 entrywise perturbation has
the generic 4-by-4 no-pivot determinant-product certificate whenever the
original matrix is upper Hessenberg and the three symbolic pivots are nonzero. -/
theorem hessenberg4NoPivotEntrywisePerturbation_det_eq_diag_prod_of_upperHessenberg
    (A : Fin 4 → Fin 4 → ℝ) (eps1 eps2 eps3 : Fin 4 → ℝ)
    (hA : IsUpperHessenbergMatrix 4 A)
    (hp0 : hessenberg4NoPivotPivot0
        (hessenbergEntrywisePerturbation 4 A eps1 eps2 eps3 :
          Matrix (Fin 4) (Fin 4) ℝ) ≠ 0)
    (hp1 : hessenberg4NoPivotDiag1
        (hessenbergEntrywisePerturbation 4 A eps1 eps2 eps3 :
          Matrix (Fin 4) (Fin 4) ℝ) ≠ 0)
    (hp2 : hessenberg4NoPivotDiag2
        (hessenbergEntrywisePerturbation 4 A eps1 eps2 eps3 :
          Matrix (Fin 4) (Fin 4) ℝ) ≠ 0) :
    Matrix.det
        (hessenbergEntrywisePerturbation 4 A eps1 eps2 eps3 :
          Matrix (Fin 4) (Fin 4) ℝ) =
      ∏ i : Fin 4,
        hessenberg4NoPivotDiag
          (hessenbergEntrywisePerturbation 4 A eps1 eps2 eps3 :
            Matrix (Fin 4) (Fin 4) ℝ) i := by
  let A' : Matrix (Fin 4) (Fin 4) ℝ :=
    hessenbergEntrywisePerturbation 4 A eps1 eps2 eps3
  have hH : IsUpperHessenbergMatrix 4 A' :=
    hessenbergEntrywisePerturbation_isUpperHessenberg 4 A eps1 eps2 eps3 hA
  exact hessenberg4NoPivot_det_eq_diag_prod_of_upperHessenberg A'
    (hH 2 0 (by norm_num)) (hH 3 0 (by norm_num))
    (hH 3 1 (by norm_num)) hp0 hp1 hp2

/-- Specialization of the nearby-determinant mixed-stability bridge to the
generic 4-by-4 no-pivot endpoint diagonal.  The determinant-product certificate
is supplied by the symbolic GE path, not by an external assumption. -/
theorem hessenberg4NoPivotRoundedTrace_nearbyDet_relError_le_gamma
    (fp : FPModel) (A : Fin 4 → Fin 4 → ℝ)
    (eps1 eps2 eps3 eta : Fin 4 → ℝ)
    (prevSuperHat prevPivotHat : Fin 4 → ℝ)
    (hA : IsUpperHessenbergMatrix 4 A)
    (htrace : HessenbergRoundedDiagTraceOnOriginal 4 A eps1 eps2 eps3
      prevSuperHat prevPivotHat
      (hessenberg4NoPivotDiag
        (hessenbergEntrywisePerturbation 4 A eps1 eps2 eps3 :
          Matrix (Fin 4) (Fin 4) ℝ)))
    (hp0 : hessenberg4NoPivotPivot0
        (hessenbergEntrywisePerturbation 4 A eps1 eps2 eps3 :
          Matrix (Fin 4) (Fin 4) ℝ) ≠ 0)
    (hp1 : hessenberg4NoPivotDiag1
        (hessenbergEntrywisePerturbation 4 A eps1 eps2 eps3 :
          Matrix (Fin 4) (Fin 4) ℝ) ≠ 0)
    (hp2 : hessenberg4NoPivotDiag2
        (hessenbergEntrywisePerturbation 4 A eps1 eps2 eps3 :
          Matrix (Fin 4) (Fin 4) ℝ) ≠ 0)
    (heta : ∀ i : Fin 4, |eta i| ≤ fp.u)
    (hgamma : gammaValid fp 4)
    (hdiag : (∏ i : Fin 4,
        hessenberg4NoPivotDiag
          (hessenbergEntrywisePerturbation 4 A eps1 eps2 eps3 :
            Matrix (Fin 4) (Fin 4) ℝ) i) ≠ 0) :
    HessenbergExactDiagTraceOnEntrywisePerturbation 4 A eps1 eps2 eps3
        prevSuperHat prevPivotHat
        (hessenberg4NoPivotDiag
          (hessenbergEntrywisePerturbation 4 A eps1 eps2 eps3 :
            Matrix (Fin 4) (Fin 4) ℝ)) ∧
      relError
        (hessenbergDetRoundedProduct 4
          (hessenberg4NoPivotDiag
            (hessenbergEntrywisePerturbation 4 A eps1 eps2 eps3 :
              Matrix (Fin 4) (Fin 4) ℝ)) eta)
        (Matrix.det
          (hessenbergEntrywisePerturbation 4 A eps1 eps2 eps3 :
            Matrix (Fin 4) (Fin 4) ℝ)) ≤ gamma fp 4 := by
  exact hessenbergRoundedDiagTraceOnOriginal_nearbyDet_relError_le_gamma
    fp 4 A eps1 eps2 eps3 prevSuperHat prevPivotHat
    (hessenberg4NoPivotDiag
      (hessenbergEntrywisePerturbation 4 A eps1 eps2 eps3 :
        Matrix (Fin 4) (Fin 4) ℝ))
    eta htrace
    (hessenberg4NoPivotEntrywisePerturbation_det_eq_diag_prod_of_upperHessenberg
      A eps1 eps2 eps3 hA hp0 hp1 hp2)
    heta hgamma hdiag

/-- The 4-by-4 upper-Hessenberg example matrix from Section 1.16. -/
noncomputable def hessenbergDetExampleMatrix (alpha : ℝ) :
    Fin 4 → Fin 4 → ℝ
  | ⟨0, _⟩, ⟨0, _⟩ => alpha
  | ⟨0, _⟩, ⟨1, _⟩ => -1
  | ⟨0, _⟩, ⟨2, _⟩ => -1
  | ⟨0, _⟩, ⟨3, _⟩ => -1
  | ⟨1, _⟩, ⟨0, _⟩ => 1
  | ⟨1, _⟩, ⟨1, _⟩ => 1
  | ⟨1, _⟩, ⟨2, _⟩ => -1
  | ⟨1, _⟩, ⟨3, _⟩ => -1
  | ⟨2, _⟩, ⟨0, _⟩ => 0
  | ⟨2, _⟩, ⟨1, _⟩ => 1
  | ⟨2, _⟩, ⟨2, _⟩ => 1
  | ⟨2, _⟩, ⟨3, _⟩ => -1
  | ⟨3, _⟩, ⟨0, _⟩ => 0
  | ⟨3, _⟩, ⟨1, _⟩ => 0
  | ⟨3, _⟩, ⟨2, _⟩ => 1
  | ⟨3, _⟩, ⟨3, _⟩ => 1

/-- The vector `e = [1,1,1,1]^T` used in the Section 1.16 example. -/
noncomputable def hessenbergDetExampleOnes : Fin 4 → ℝ :=
  fun _ => 1

/-- The exact right-hand side `A*e` for the Section 1.16 example. -/
noncomputable def hessenbergDetExampleRhs (alpha : ℝ) : Fin 4 → ℝ
  | ⟨0, _⟩ => alpha - 3
  | ⟨1, _⟩ => 0
  | ⟨2, _⟩ => 1
  | ⟨3, _⟩ => 2

/-- The exact inverse of the Section 1.16 example matrix when `alpha + 1` is
nonzero. -/
noncomputable def hessenbergDetExampleMatrixInv (alpha : ℝ) :
    Fin 4 → Fin 4 → ℝ
  | ⟨0, _⟩, ⟨0, _⟩ => 1 / (alpha + 1)
  | ⟨0, _⟩, ⟨1, _⟩ => 1 / (alpha + 1)
  | ⟨0, _⟩, ⟨2, _⟩ => 0
  | ⟨0, _⟩, ⟨3, _⟩ => 2 / (alpha + 1)
  | ⟨1, _⟩, ⟨0, _⟩ => -1 / (alpha + 1)
  | ⟨1, _⟩, ⟨1, _⟩ => alpha / (alpha + 1)
  | ⟨1, _⟩, ⟨2, _⟩ => 0
  | ⟨1, _⟩, ⟨3, _⟩ => (alpha - 1) / (alpha + 1)
  | ⟨2, _⟩, ⟨0, _⟩ => 1 / (2 * (alpha + 1))
  | ⟨2, _⟩, ⟨1, _⟩ => -alpha / (2 * (alpha + 1))
  | ⟨2, _⟩, ⟨2, _⟩ => 1 / 2
  | ⟨2, _⟩, ⟨3, _⟩ => 1 / (alpha + 1)
  | ⟨3, _⟩, ⟨0, _⟩ => -1 / (2 * (alpha + 1))
  | ⟨3, _⟩, ⟨1, _⟩ => alpha / (2 * (alpha + 1))
  | ⟨3, _⟩, ⟨2, _⟩ => -1 / 2
  | ⟨3, _⟩, ⟨3, _⟩ => alpha / (alpha + 1)

/-- The displayed matrix is upper Hessenberg. -/
theorem hessenbergDetExample_isUpperHessenberg (alpha : ℝ) :
    IsUpperHessenbergMatrix 4 (hessenbergDetExampleMatrix alpha) := by
  intro i j hij
  fin_cases i <;> fin_cases j <;>
    simp [hessenbergDetExampleMatrix] at hij ⊢

/-- Multiplying the displayed matrix by `e=[1,1,1,1]^T` gives the displayed RHS. -/
theorem hessenbergDetExample_mul_ones (alpha : ℝ) :
    matMulVec 4 (hessenbergDetExampleMatrix alpha) hessenbergDetExampleOnes =
      hessenbergDetExampleRhs alpha := by
  ext i
  fin_cases i <;>
    unfold matMulVec <;>
    rw [Fin.sum_univ_four] <;>
    simp [hessenbergDetExampleMatrix, hessenbergDetExampleOnes,
      hessenbergDetExampleRhs] <;>
    ring

/-- Therefore the exact solution of `A*x = A*e` is `e`. -/
theorem hessenbergDetExample_ones_solves_rhs (alpha : ℝ) :
    matMulVec 4 (hessenbergDetExampleMatrix alpha) hessenbergDetExampleOnes =
      hessenbergDetExampleRhs alpha :=
  hessenbergDetExample_mul_ones alpha

/-- The displayed inverse is a two-sided inverse for the Section 1.16 example
at the source value `alpha = 10^-7`. -/
theorem hessenbergDetExampleMatrixInv_alpha_ten_pow_isInverse :
    IsInverse 4 (hessenbergDetExampleMatrix (1 / 10000000 : ℝ))
      (hessenbergDetExampleMatrixInv (1 / 10000000 : ℝ)) := by
  constructor
  · intro i j
    fin_cases i <;> fin_cases j <;>
      rw [Fin.sum_univ_four] <;>
      norm_num [hessenbergDetExampleMatrix, hessenbergDetExampleMatrixInv]
    · rfl
    · rfl
    · rfl
    · rfl
    · rfl
    · rfl
  · intro i j
    fin_cases i <;> fin_cases j <;>
      rw [Fin.sum_univ_four] <;>
      norm_num [hessenbergDetExampleMatrix, hessenbergDetExampleMatrixInv]
    · rfl
    · exact (by
        norm_num :
          (1 : ℝ) + -(10000000 / 10000001) + -(1 / 10000001) = 0)
    · rfl
    · exact (by
        norm_num :
          (1 : ℝ) + -(10000000 / 10000001) + -(1 / 10000001) = 0)
    · rfl
    · exact (by
        norm_num :
          (0 : ℝ) + 10000000 / 10000001 + 1 / 10000001 = 1)

/-- For the displayed `alpha = 10^-7`, the Section 1.16 example matrix has
infinity norm `4`. -/
theorem hessenbergDetExampleMatrix_alpha_ten_pow_infNorm_eq :
    infNorm (hessenbergDetExampleMatrix (1 / 10000000 : ℝ)) = 4 := by
  apply le_antisymm
  · apply infNorm_le_of_row_sum_le
    · intro i
      fin_cases i <;>
        rw [Fin.sum_univ_four] <;>
        norm_num [hessenbergDetExampleMatrix]
    · norm_num
  · have hrow :=
      row_sum_le_infNorm (hessenbergDetExampleMatrix (1 / 10000000 : ℝ)) (1 : Fin 4)
    rw [Fin.sum_univ_four] at hrow
    norm_num [hessenbergDetExampleMatrix] at hrow
    exact hrow

/-- For the displayed `alpha = 10^-7`, the displayed inverse has infinity norm
`40000000/10000001`. -/
theorem hessenbergDetExampleMatrixInv_alpha_ten_pow_infNorm_eq :
    infNorm (hessenbergDetExampleMatrixInv (1 / 10000000 : ℝ)) =
      40000000 / 10000001 := by
  apply le_antisymm
  · apply infNorm_le_of_row_sum_le
    · intro i
      fin_cases i
      · rw [Fin.sum_univ_four]
        norm_num [hessenbergDetExampleMatrixInv]
      · rw [Fin.sum_univ_four]
        norm_num [hessenbergDetExampleMatrixInv]
        exact (by
          norm_num :
            (1 + 9999999 / 10000001 : ℝ) ≤ 40000000 / 10000001)
      · rw [Fin.sum_univ_four]
        norm_num [hessenbergDetExampleMatrixInv]
      · rw [Fin.sum_univ_four]
        norm_num [hessenbergDetExampleMatrixInv]
    · norm_num
  · have hrow :=
      row_sum_le_infNorm
        (hessenbergDetExampleMatrixInv (1 / 10000000 : ℝ)) (0 : Fin 4)
    rw [Fin.sum_univ_four] at hrow
    norm_num [hessenbergDetExampleMatrixInv] at hrow
    exact hrow

/-- For the displayed `alpha = 10^-7`, the exact infinity-norm condition-number
product is the rational number that rounds to the source's displayed `16`. -/
theorem hessenbergDetExample_kappaInfProduct_alpha_ten_pow_eq :
    infNorm (hessenbergDetExampleMatrix (1 / 10000000 : ℝ)) *
        infNorm (hessenbergDetExampleMatrixInv (1 / 10000000 : ℝ)) =
      160000000 / 10000001 := by
  rw [hessenbergDetExampleMatrix_alpha_ten_pow_infNorm_eq,
    hessenbergDetExampleMatrixInv_alpha_ten_pow_infNorm_eq]
  norm_num

/-- The exact value behind the source's displayed `kappa_infty(A)=16` line is
within `2e-6` of `16`. -/
theorem hessenbergDetExample_kappaInfProduct_alpha_ten_pow_near_sixteen :
    |infNorm (hessenbergDetExampleMatrix (1 / 10000000 : ℝ)) *
          infNorm (hessenbergDetExampleMatrixInv (1 / 10000000 : ℝ)) - 16| <
      2 / (10 : ℝ) ^ 6 := by
  rw [hessenbergDetExample_kappaInfProduct_alpha_ten_pow_eq]
  norm_num

/-- Exact diagonal entries produced by no-pivot elimination on the example. -/
noncomputable def hessenbergDetExampleNoPivotUDiag (alpha : ℝ) : Fin 4 → ℝ
  | ⟨0, _⟩ => alpha
  | ⟨1, _⟩ => (alpha + 1) / alpha
  | ⟨2, _⟩ => (2 * alpha) / (alpha + 1)
  | ⟨3, _⟩ => (alpha + 1) / alpha

/-- The exact upper triangular matrix obtained by no-pivot GE on the Section
1.16 example when the displayed pivots are nonzero. -/
noncomputable def hessenbergDetExampleNoPivotU (alpha : ℝ) :
    Matrix (Fin 4) (Fin 4) ℝ
  | ⟨0, _⟩, ⟨0, _⟩ => alpha
  | ⟨0, _⟩, ⟨1, _⟩ => -1
  | ⟨0, _⟩, ⟨2, _⟩ => -1
  | ⟨0, _⟩, ⟨3, _⟩ => -1
  | ⟨1, _⟩, ⟨0, _⟩ => 0
  | ⟨1, _⟩, ⟨1, _⟩ => (alpha + 1) / alpha
  | ⟨1, _⟩, ⟨2, _⟩ => (1 - alpha) / alpha
  | ⟨1, _⟩, ⟨3, _⟩ => (1 - alpha) / alpha
  | ⟨2, _⟩, ⟨0, _⟩ => 0
  | ⟨2, _⟩, ⟨1, _⟩ => 0
  | ⟨2, _⟩, ⟨2, _⟩ => (2 * alpha) / (alpha + 1)
  | ⟨2, _⟩, ⟨3, _⟩ => -2 / (alpha + 1)
  | ⟨3, _⟩, ⟨0, _⟩ => 0
  | ⟨3, _⟩, ⟨1, _⟩ => 0
  | ⟨3, _⟩, ⟨2, _⟩ => 0
  | ⟨3, _⟩, ⟨3, _⟩ => (alpha + 1) / alpha

/-- The no-pivot GE endpoint is upper triangular. -/
theorem hessenbergDetExampleNoPivotU_blockTriangular (alpha : ℝ) :
    (hessenbergDetExampleNoPivotU alpha).BlockTriangular id := by
  intro i j hij
  fin_cases i <;> fin_cases j <;>
    simp [hessenbergDetExampleNoPivotU] at hij ⊢

/-- The determinant of the no-pivot GE endpoint is the product of the displayed
diagonal entries. -/
theorem hessenbergDetExampleNoPivotU_det_eq_diag_prod (alpha : ℝ) :
    Matrix.det (hessenbergDetExampleNoPivotU alpha) =
      ∏ i : Fin 4, hessenbergDetExampleNoPivotUDiag alpha i := by
  rw [Matrix.det_of_upperTriangular
    (hessenbergDetExampleNoPivotU_blockTriangular alpha)]
  rw [Fin.prod_univ_four]
  rw [Fin.prod_univ_four]
  simp [hessenbergDetExampleNoPivotU, hessenbergDetExampleNoPivotUDiag]

/-- The product of the exact no-pivot diagonal entries is `2*(alpha+1)`. -/
theorem hessenbergDetExampleNoPivotUDiag_prod_eq
    (alpha : ℝ) (halpha : alpha ≠ 0) (halpha1 : alpha + 1 ≠ 0) :
    (∏ i : Fin 4, hessenbergDetExampleNoPivotUDiag alpha i) =
      2 * (alpha + 1) := by
  rw [Fin.prod_univ_four]
  simp [hessenbergDetExampleNoPivotUDiag]
  field_simp [halpha, halpha1]

/-- No-pivot GE preserves the determinant of the displayed matrix and reaches
the displayed upper triangular endpoint. -/
theorem hessenbergDetExampleMatrix_det_eq_noPivotUDiag_prod
    (alpha : ℝ) (halpha : alpha ≠ 0) (halpha1 : alpha + 1 ≠ 0) :
    Matrix.det (hessenbergDetExampleMatrix alpha : Matrix (Fin 4) (Fin 4) ℝ) =
      ∏ i : Fin 4, hessenbergDetExampleNoPivotUDiag alpha i := by
  let A : Matrix (Fin 4) (Fin 4) ℝ := hessenbergDetExampleMatrix alpha
  let M1 : Matrix (Fin 4) (Fin 4) ℝ :=
    A.updateRow 1 (A 1 + (-(1 / alpha)) • A 0)
  let M2 : Matrix (Fin 4) (Fin 4) ℝ :=
    M1.updateRow 2 (M1 2 + (-(alpha / (alpha + 1))) • M1 1)
  let M3 : Matrix (Fin 4) (Fin 4) ℝ :=
    M2.updateRow 3 (M2 3 + (-((alpha + 1) / (2 * alpha))) • M2 2)
  have h1 : Matrix.det M1 = Matrix.det A := by
    simpa [M1] using
      (Matrix.det_updateRow_add_smul_self A (show (1 : Fin 4) ≠ 0 by decide)
        (-(1 / alpha)))
  have h2 : Matrix.det M2 = Matrix.det M1 := by
    simpa [M2] using
      (Matrix.det_updateRow_add_smul_self M1 (show (2 : Fin 4) ≠ 1 by decide)
        (-(alpha / (alpha + 1))))
  have h3 : Matrix.det M3 = Matrix.det M2 := by
    simpa [M3] using
      (Matrix.det_updateRow_add_smul_self M2 (show (3 : Fin 4) ≠ 2 by decide)
        (-((alpha + 1) / (2 * alpha))))
  have hM3 : M3 = hessenbergDetExampleNoPivotU alpha := by
    ext i j
    fin_cases i <;> fin_cases j <;>
      simp [M3, M2, M1, A, hessenbergDetExampleMatrix,
        hessenbergDetExampleNoPivotU] <;>
      field_simp [halpha, halpha1] <;>
      ring
  change Matrix.det A = ∏ i : Fin 4, hessenbergDetExampleNoPivotUDiag alpha i
  calc
    Matrix.det A = Matrix.det M1 := h1.symm
    _ = Matrix.det M2 := h2.symm
    _ = Matrix.det M3 := h3.symm
    _ = Matrix.det (hessenbergDetExampleNoPivotU alpha) := by rw [hM3]
    _ = ∏ i : Fin 4, hessenbergDetExampleNoPivotUDiag alpha i :=
      hessenbergDetExampleNoPivotU_det_eq_diag_prod alpha

/-- The actual determinant of the displayed matrix agrees with the no-pivot
diagonal product. -/
theorem hessenbergDetExampleMatrix_det_eq
    (alpha : ℝ) (halpha : alpha ≠ 0) (halpha1 : alpha + 1 ≠ 0) :
    Matrix.det (hessenbergDetExampleMatrix alpha : Matrix (Fin 4) (Fin 4) ℝ) =
      2 * (alpha + 1) := by
  rw [hessenbergDetExampleMatrix_det_eq_noPivotUDiag_prod alpha halpha halpha1,
    hessenbergDetExampleNoPivotUDiag_prod_eq alpha halpha halpha1]

/-- Mixed-stability determinant-product bridge for the displayed §1.16
upper-Hessenberg family.  Once the final determinant product is modeled by
relative factors `eta_i`, the computed determinant is within `gamma_4` of the
exact determinant of the displayed matrix. -/
theorem hessenbergDetExampleRoundedProduct_relError_le_gamma
    (fp : FPModel) (alpha : ℝ) (eta : Fin 4 → ℝ)
    (halpha : alpha ≠ 0) (halpha1 : alpha + 1 ≠ 0)
    (heta : ∀ i : Fin 4, |eta i| ≤ fp.u)
    (hgamma : gammaValid fp 4) :
    relError
        (hessenbergDetRoundedProduct 4
          (hessenbergDetExampleNoPivotUDiag alpha) eta)
        (Matrix.det (hessenbergDetExampleMatrix alpha :
          Matrix (Fin 4) (Fin 4) ℝ)) ≤ gamma fp 4 := by
  have hdiag :
      (∏ i : Fin 4, hessenbergDetExampleNoPivotUDiag alpha i) ≠ 0 := by
    rw [hessenbergDetExampleNoPivotUDiag_prod_eq alpha halpha halpha1]
    exact mul_ne_zero (by norm_num : (2 : ℝ) ≠ 0) halpha1
  exact
    hessenbergDetRoundedProduct_relError_le_gamma_of_det_eq_diag_prod
      fp 4 (hessenbergDetExampleMatrix alpha : Matrix (Fin 4) (Fin 4) ℝ)
      (hessenbergDetExampleNoPivotUDiag alpha) eta
      (hessenbergDetExampleMatrix_det_eq_noPivotUDiag_prod
        alpha halpha halpha1)
      heta hgamma hdiag

/-- At the source value `alpha = 10^-7`, the actual determinant is
`10000001/5000000`, agreeing with the exact no-pivot diagonal product. -/
theorem hessenbergDetExampleMatrix_alpha_ten_pow_det_eq :
    Matrix.det
        (hessenbergDetExampleMatrix (1 / 10000000 : ℝ) :
          Matrix (Fin 4) (Fin 4) ℝ) =
      10000001 / 5000000 := by
  rw [hessenbergDetExampleMatrix_det_eq]
  · norm_num
  · norm_num
  · norm_num

/-- At the source value `alpha = 10^-7`, the exact determinant is within
`1e-6` of the five-significant-figure table baseline `2`. -/
theorem hessenbergDetExampleMatrix_alpha_ten_pow_det_near_two :
    |Matrix.det
          (hessenbergDetExampleMatrix (1 / 10000000 : ℝ) :
            Matrix (Fin 4) (Fin 4) ℝ) - 2| <
      1 / (10 : ℝ) ^ 6 := by
  rw [hessenbergDetExampleMatrix_alpha_ten_pow_det_eq]
  norm_num

/-- Exact real-arithmetic baseline for the source-value row of Table 1.3:
the determinant is `10000001/5000000`, and the exact solution is
`e=[1,1,1,1]^T`. -/
theorem hessenbergDetExample_alpha_ten_pow_exact_table_baseline :
    Matrix.det
          (hessenbergDetExampleMatrix (1 / 10000000 : ℝ) :
            Matrix (Fin 4) (Fin 4) ℝ) =
        10000001 / 5000000 ∧
      matMulVec 4 (hessenbergDetExampleMatrix (1 / 10000000 : ℝ))
          hessenbergDetExampleOnes =
        hessenbergDetExampleRhs (1 / 10000000 : ℝ) ∧
      (∀ i : Fin 4, hessenbergDetExampleOnes i = 1) := by
  refine ⟨hessenbergDetExampleMatrix_alpha_ten_pow_det_eq, ?_, ?_⟩
  · exact hessenbergDetExample_ones_solves_rhs (1 / 10000000 : ℝ)
  · intro i
    rfl

/-! ## Table 1.3 displayed single-precision data -/

/-- The finite binary32 format used for the Table 1.3 primitive-input storage
audit.  It records Higham's finite-format parameters, not infinities, NaNs, or
exception flags. -/
abbrev hessenbergDetExampleTable13IeeeSingleFormat : FloatingPointFormat :=
  FloatingPointFormat.ieeeSingleFormat

/-- Source decimal parameter in the Table 1.3 example. -/
noncomputable def hessenbergDetExampleTable13SourceAlpha : ℝ :=
  1 / (10 : ℝ) ^ 7

/-- The binary32 stored value of the source decimal `alpha = 10^-7`.  This is
kept distinct from the source real number so later primitive traces do not
silently assume exact storage of `10^-7`. -/
noncomputable def hessenbergDetExampleTable13StoredAlpha : ℝ :=
  hessenbergDetExampleTable13IeeeSingleFormat.finiteRoundToEven
    hessenbergDetExampleTable13SourceAlpha

/-- The Table 1.3 input matrix after binary32 storage of each source entry. -/
noncomputable def hessenbergDetExampleTable13StoredMatrix :
    Fin 4 → Fin 4 → ℝ :=
  fun i j =>
    hessenbergDetExampleTable13IeeeSingleFormat.finiteRoundToEven
      (hessenbergDetExampleMatrix hessenbergDetExampleTable13SourceAlpha i j)

/-- The Table 1.3 right-hand side after binary32 storage of each source entry. -/
noncomputable def hessenbergDetExampleTable13StoredRhs : Fin 4 → ℝ :=
  fun i =>
    hessenbergDetExampleTable13IeeeSingleFormat.finiteRoundToEven
      (hessenbergDetExampleRhs hessenbergDetExampleTable13SourceAlpha i)

/-- The exact real number `1` is representable in the Table 1.3 binary32
format. -/
theorem hessenbergDetExampleTable13IeeeSingle_one_finiteSystem :
    hessenbergDetExampleTable13IeeeSingleFormat.finiteSystem (1 : ℝ) := by
  let fmt := hessenbergDetExampleTable13IeeeSingleFormat
  have hm : fmt.normalizedMantissa fmt.minNormalMantissa :=
    fmt.minNormalMantissa_normalized
  have he : fmt.exponentInRange (1 : ℤ) := by
    norm_num [fmt, hessenbergDetExampleTable13IeeeSingleFormat,
      FloatingPointFormat.ieeeSingleFormat,
      FloatingPointFormat.exponentInRange]
  refine Or.inr (Or.inl ⟨false, fmt.minNormalMantissa, (1 : ℤ), hm, he, ?_⟩)
  norm_num [fmt, hessenbergDetExampleTable13IeeeSingleFormat,
    FloatingPointFormat.ieeeSingleFormat, FloatingPointFormat.normalizedValue,
    FloatingPointFormat.signValue, FloatingPointFormat.minNormalMantissa,
    FloatingPointFormat.betaR, zpow_neg]
  rfl

/-- The exact real number `2` is representable in the Table 1.3 binary32
format. -/
theorem hessenbergDetExampleTable13IeeeSingle_two_finiteSystem :
    hessenbergDetExampleTable13IeeeSingleFormat.finiteSystem (2 : ℝ) := by
  let fmt := hessenbergDetExampleTable13IeeeSingleFormat
  have hm : fmt.normalizedMantissa fmt.minNormalMantissa :=
    fmt.minNormalMantissa_normalized
  have he : fmt.exponentInRange (2 : ℤ) := by
    norm_num [fmt, hessenbergDetExampleTable13IeeeSingleFormat,
      FloatingPointFormat.ieeeSingleFormat,
      FloatingPointFormat.exponentInRange]
  refine Or.inr (Or.inl ⟨false, fmt.minNormalMantissa, (2 : ℤ), hm, he, ?_⟩)
  norm_num [fmt, hessenbergDetExampleTable13IeeeSingleFormat,
    FloatingPointFormat.ieeeSingleFormat, FloatingPointFormat.normalizedValue,
    FloatingPointFormat.signValue, FloatingPointFormat.minNormalMantissa,
    FloatingPointFormat.betaR, zpow_neg]
  rfl

@[simp] theorem hessenbergDetExampleTable13IeeeSingle_round_zero :
    hessenbergDetExampleTable13IeeeSingleFormat.finiteRoundToEven (0 : ℝ) =
      0 := by
  let fmt := hessenbergDetExampleTable13IeeeSingleFormat
  simpa [fmt] using
    (fmt.finiteRoundToEven_eq_self_of_finiteSystem
      (x := (0 : ℝ)) fmt.finiteSystem_zero)

@[simp] theorem hessenbergDetExampleTable13IeeeSingle_round_one :
    hessenbergDetExampleTable13IeeeSingleFormat.finiteRoundToEven (1 : ℝ) =
      1 := by
  let fmt := hessenbergDetExampleTable13IeeeSingleFormat
  simpa [fmt] using
    (fmt.finiteRoundToEven_eq_self_of_finiteSystem
      hessenbergDetExampleTable13IeeeSingle_one_finiteSystem)

@[simp] theorem hessenbergDetExampleTable13IeeeSingle_round_neg_one :
    hessenbergDetExampleTable13IeeeSingleFormat.finiteRoundToEven (-1 : ℝ) =
      -1 := by
  let fmt := hessenbergDetExampleTable13IeeeSingleFormat
  have hfinite :
      fmt.finiteSystem (-(1 : ℝ)) :=
    fmt.finiteSystem_neg
      hessenbergDetExampleTable13IeeeSingle_one_finiteSystem
  simpa [fmt] using
    (fmt.finiteRoundToEven_eq_self_of_finiteSystem hfinite)

@[simp] theorem hessenbergDetExampleTable13IeeeSingle_round_two :
    hessenbergDetExampleTable13IeeeSingleFormat.finiteRoundToEven (2 : ℝ) =
      2 := by
  let fmt := hessenbergDetExampleTable13IeeeSingleFormat
  simpa [fmt] using
    (fmt.finiteRoundToEven_eq_self_of_finiteSystem
      hessenbergDetExampleTable13IeeeSingle_two_finiteSystem)

/-- The stored source decimal `alpha` is a finite binary32 value by construction. -/
theorem hessenbergDetExampleTable13StoredAlpha_finiteSystem :
    hessenbergDetExampleTable13IeeeSingleFormat.finiteSystem
      hessenbergDetExampleTable13StoredAlpha := by
  exact hessenbergDetExampleTable13IeeeSingleFormat.finiteRoundToEven_finiteSystem
    hessenbergDetExampleTable13SourceAlpha

/-- The source decimal `10^-7` rounds to the concrete binary32 normalized value
with mantissa `14073749` and exponent `-23`. -/
theorem hessenbergDetExampleTable13StoredAlpha_eq_normalizedValue :
    hessenbergDetExampleTable13StoredAlpha =
      hessenbergDetExampleTable13IeeeSingleFormat.normalizedValue
        false 14073749 (-23 : ℤ) := by
  let fmt := hessenbergDetExampleTable13IeeeSingleFormat
  let a : ℝ := fmt.normalizedValue false 14073748 (-23 : ℤ)
  let b : ℝ := fmt.normalizedValue false 14073749 (-23 : ℤ)
  let x : ℝ := hessenbergDetExampleTable13SourceAlpha
  have hm : fmt.normalizedMantissa 14073748 := by
    norm_num [fmt, hessenbergDetExampleTable13IeeeSingleFormat,
      FloatingPointFormat.ieeeSingleFormat,
      FloatingPointFormat.normalizedMantissa,
      FloatingPointFormat.mantissaInRange,
      FloatingPointFormat.minNormalMantissa]
  have hmnext : fmt.normalizedMantissa (14073748 + 1) := by
    norm_num [fmt, hessenbergDetExampleTable13IeeeSingleFormat,
      FloatingPointFormat.ieeeSingleFormat,
      FloatingPointFormat.normalizedMantissa,
      FloatingPointFormat.mantissaInRange,
      FloatingPointFormat.minNormalMantissa]
  have hadj : fmt.realOrderAdjacentNormalized a b :=
    fmt.realOrderAdjacentNormalized_of_sameExponentAdjacentNormalized
      ⟨false, 14073748, (-23 : ℤ), hm, hmnext, Or.inl ⟨rfl, rfl⟩⟩
  have ha_value : a = (14073748 : ℝ) * (2 : ℝ) ^ (-47 : ℤ) := by
    norm_num [a, fmt, hessenbergDetExampleTable13IeeeSingleFormat,
      FloatingPointFormat.ieeeSingleFormat, FloatingPointFormat.normalizedValue,
      FloatingPointFormat.signValue, FloatingPointFormat.betaR, zpow_neg]
  have hb_value : b = (14073749 : ℝ) * (2 : ℝ) ^ (-47 : ℤ) := by
    norm_num [b, fmt, hessenbergDetExampleTable13IeeeSingleFormat,
      FloatingPointFormat.ieeeSingleFormat, FloatingPointFormat.normalizedValue,
      FloatingPointFormat.signValue, FloatingPointFormat.betaR, zpow_neg]
  have hxrange : fmt.finiteNormalRange x := by
    rw [FloatingPointFormat.finiteNormalRange,
      abs_of_pos (by
        norm_num [x, hessenbergDetExampleTable13SourceAlpha])]
    constructor
    · norm_num [x, hessenbergDetExampleTable13SourceAlpha, fmt,
        hessenbergDetExampleTable13IeeeSingleFormat,
        FloatingPointFormat.ieeeSingleFormat,
        FloatingPointFormat.minNormalMagnitude, FloatingPointFormat.betaR,
        zpow_neg]
    · calc
        x = (1 / (10 : ℝ) ^ 7) := by
          rfl
        _ ≤ 1 := by
          norm_num
        _ ≤ fmt.maxFiniteMagnitude := by
          norm_num [fmt, hessenbergDetExampleTable13IeeeSingleFormat,
            FloatingPointFormat.ieeeSingleFormat,
            FloatingPointFormat.maxFiniteMagnitude, FloatingPointFormat.betaR,
            zpow_neg]
          change (1 : ℝ) ≤ 340282346638528859811704183484516925440
          norm_num
  have hstrict : a < x ∧ x < b := by
    rw [ha_value, hb_value]
    norm_num [x, hessenbergDetExampleTable13SourceAlpha, zpow_neg]
  have hpolicy :
      fmt.sourceRoundToEvenEvidence x (fmt.finiteRoundToEven x) :=
    fmt.finiteRoundToEven_sourceRoundToEvenEvidence_of_finiteNormalRange hxrange
  have hrightCloser : |x - b| < |x - a| := by
    rw [ha_value, hb_value]
    norm_num [x, hessenbergDetExampleTable13SourceAlpha, zpow_neg]
  have hround : fmt.finiteRoundToEven x = b :=
    fmt.sourceRoundToEvenEvidence_eq_right_of_realOrderAdjacent_strict_between_right_closer
      hpolicy hadj hstrict hrightCloser
  simpa [hessenbergDetExampleTable13StoredAlpha, x, b, fmt] using hround

/-- Closed rational form of the binary32 stored value of `10^-7`. -/
theorem hessenbergDetExampleTable13StoredAlpha_eq :
    hessenbergDetExampleTable13StoredAlpha =
      14073749 / (2 : ℝ) ^ 47 := by
  rw [hessenbergDetExampleTable13StoredAlpha_eq_normalizedValue]
  norm_num [hessenbergDetExampleTable13IeeeSingleFormat,
    FloatingPointFormat.ieeeSingleFormat, FloatingPointFormat.normalizedValue,
    FloatingPointFormat.signValue, FloatingPointFormat.betaR, zpow_neg]

/-- The stored Table 1.3 `alpha` is positive. -/
theorem hessenbergDetExampleTable13StoredAlpha_pos :
    0 < hessenbergDetExampleTable13StoredAlpha := by
  rw [hessenbergDetExampleTable13StoredAlpha_eq]
  norm_num

/-- The stored Table 1.3 `alpha` is nonzero, so the first no-pivot division has
a nonzero denominator. -/
theorem hessenbergDetExampleTable13StoredAlpha_ne_zero :
    hessenbergDetExampleTable13StoredAlpha ≠ 0 :=
  ne_of_gt hessenbergDetExampleTable13StoredAlpha_pos

/-- Every entry of the stored Table 1.3 matrix is a finite binary32 value. -/
theorem hessenbergDetExampleTable13StoredMatrix_finiteSystem
    (i j : Fin 4) :
    hessenbergDetExampleTable13IeeeSingleFormat.finiteSystem
      (hessenbergDetExampleTable13StoredMatrix i j) := by
  exact hessenbergDetExampleTable13IeeeSingleFormat.finiteRoundToEven_finiteSystem
    (hessenbergDetExampleMatrix hessenbergDetExampleTable13SourceAlpha i j)

/-- Every entry of the stored Table 1.3 right-hand side is a finite binary32
value. -/
theorem hessenbergDetExampleTable13StoredRhs_finiteSystem (i : Fin 4) :
    hessenbergDetExampleTable13IeeeSingleFormat.finiteSystem
      (hessenbergDetExampleTable13StoredRhs i) := by
  exact hessenbergDetExampleTable13IeeeSingleFormat.finiteRoundToEven_finiteSystem
    (hessenbergDetExampleRhs hessenbergDetExampleTable13SourceAlpha i)

/-- Binary32 storage of the Table 1.3 matrix changes only the non-representable
source decimal `alpha`; the `0`, `1`, and `-1` entries are stored exactly. -/
theorem hessenbergDetExampleTable13_storedMatrix_eq_storedAlpha_matrix :
    hessenbergDetExampleTable13StoredMatrix =
      hessenbergDetExampleMatrix hessenbergDetExampleTable13StoredAlpha := by
  funext i j
  fin_cases i <;> fin_cases j <;>
    simp [hessenbergDetExampleTable13StoredMatrix,
      hessenbergDetExampleTable13StoredAlpha,
      hessenbergDetExampleTable13SourceAlpha,
      hessenbergDetExampleMatrix]

/-- The stored Table 1.3 matrix remains upper Hessenberg. -/
theorem hessenbergDetExampleTable13StoredMatrix_isUpperHessenberg :
    IsUpperHessenbergMatrix 4 hessenbergDetExampleTable13StoredMatrix := by
  rw [hessenbergDetExampleTable13_storedMatrix_eq_storedAlpha_matrix]
  exact hessenbergDetExample_isUpperHessenberg
    hessenbergDetExampleTable13StoredAlpha

/-- The first stored no-pivot Table 1.3 matrix pivot is nonzero. -/
theorem hessenbergDetExampleTable13StoredMatrix_pivot0_ne_zero :
    hessenbergDetExampleTable13StoredMatrix 0 0 ≠ 0 := by
  rw [hessenbergDetExampleTable13_storedMatrix_eq_storedAlpha_matrix]
  simpa [hessenbergDetExampleMatrix] using
    hessenbergDetExampleTable13StoredAlpha_ne_zero

/-- Exact determinant of the stored-input Table 1.3 matrix. -/
theorem hessenbergDetExampleTable13StoredMatrix_det_eq :
    Matrix.det
        (hessenbergDetExampleTable13StoredMatrix :
          Matrix (Fin 4) (Fin 4) ℝ) =
      2 * (hessenbergDetExampleTable13StoredAlpha + 1) := by
  rw [hessenbergDetExampleTable13_storedMatrix_eq_storedAlpha_matrix]
  exact hessenbergDetExampleMatrix_det_eq
    hessenbergDetExampleTable13StoredAlpha
    hessenbergDetExampleTable13StoredAlpha_ne_zero
    (ne_of_gt (add_pos hessenbergDetExampleTable13StoredAlpha_pos zero_lt_one))

/-- The exact no-pivot determinant product theorem specialized to the stored
Table 1.3 input matrix. -/
theorem hessenbergDetExampleTable13StoredMatrix_det_eq_noPivotUDiag_prod :
    Matrix.det
        (hessenbergDetExampleTable13StoredMatrix :
          Matrix (Fin 4) (Fin 4) ℝ) =
      ∏ i : Fin 4,
        hessenbergDetExampleNoPivotUDiag
          hessenbergDetExampleTable13StoredAlpha i := by
  rw [hessenbergDetExampleTable13_storedMatrix_eq_storedAlpha_matrix]
  exact hessenbergDetExampleMatrix_det_eq_noPivotUDiag_prod
    hessenbergDetExampleTable13StoredAlpha
    hessenbergDetExampleTable13StoredAlpha_ne_zero
    (ne_of_gt (add_pos hessenbergDetExampleTable13StoredAlpha_pos zero_lt_one))

/-- The first primitive no-pivot GE division for the stored Table 1.3 input:
nearest/even binary32 rounds `1 / fl32(alpha)` to exactly `10^7`. -/
theorem hessenbergDetExampleTable13_round_one_div_storedAlpha :
    hessenbergDetExampleTable13IeeeSingleFormat.finiteRoundToEvenOp BasicOp.div
        (1 : ℝ) hessenbergDetExampleTable13StoredAlpha =
      (10 : ℝ) ^ 7 := by
  let fmt := hessenbergDetExampleTable13IeeeSingleFormat
  let a : ℝ := fmt.normalizedValue false 9999999 (24 : ℤ)
  let b : ℝ := fmt.normalizedValue false 10000000 (24 : ℤ)
  let x : ℝ := BasicOp.exact BasicOp.div (1 : ℝ)
    hessenbergDetExampleTable13StoredAlpha
  have hm : fmt.normalizedMantissa 9999999 := by
    norm_num [fmt, hessenbergDetExampleTable13IeeeSingleFormat,
      FloatingPointFormat.ieeeSingleFormat,
      FloatingPointFormat.normalizedMantissa,
      FloatingPointFormat.mantissaInRange,
      FloatingPointFormat.minNormalMantissa]
  have hmnext : fmt.normalizedMantissa (9999999 + 1) := by
    norm_num [fmt, hessenbergDetExampleTable13IeeeSingleFormat,
      FloatingPointFormat.ieeeSingleFormat,
      FloatingPointFormat.normalizedMantissa,
      FloatingPointFormat.mantissaInRange,
      FloatingPointFormat.minNormalMantissa]
  have hadj : fmt.realOrderAdjacentNormalized a b :=
    fmt.realOrderAdjacentNormalized_of_sameExponentAdjacentNormalized
      ⟨false, 9999999, (24 : ℤ), hm, hmnext, Or.inl ⟨rfl, rfl⟩⟩
  have ha_value : a = (9999999 : ℝ) := by
    norm_num [a, fmt, hessenbergDetExampleTable13IeeeSingleFormat,
      FloatingPointFormat.ieeeSingleFormat, FloatingPointFormat.normalizedValue,
      FloatingPointFormat.signValue, FloatingPointFormat.betaR, zpow_neg]
  have hb_value : b = (10000000 : ℝ) := by
    norm_num [b, fmt, hessenbergDetExampleTable13IeeeSingleFormat,
      FloatingPointFormat.ieeeSingleFormat, FloatingPointFormat.normalizedValue,
      FloatingPointFormat.signValue, FloatingPointFormat.betaR, zpow_neg]
  have hx_value : x = (2 : ℝ) ^ 47 / 14073749 := by
    simp [x, BasicOp.exact, hessenbergDetExampleTable13StoredAlpha_eq]
  have hxrange : fmt.finiteNormalRange x := by
    rw [FloatingPointFormat.finiteNormalRange]
    rw [hx_value, abs_of_pos (by norm_num)]
    constructor
    · norm_num [fmt, hessenbergDetExampleTable13IeeeSingleFormat,
        FloatingPointFormat.ieeeSingleFormat,
        FloatingPointFormat.minNormalMagnitude, FloatingPointFormat.betaR,
        zpow_neg]
    · calc
        (2 : ℝ) ^ 47 / 14073749 ≤ (10000000 : ℝ) := by
          norm_num
        _ ≤ fmt.maxFiniteMagnitude := by
          norm_num [fmt, hessenbergDetExampleTable13IeeeSingleFormat,
            FloatingPointFormat.ieeeSingleFormat,
            FloatingPointFormat.maxFiniteMagnitude, FloatingPointFormat.betaR,
            zpow_neg]
          change (10000000 : ℝ) ≤
            340282346638528859811704183484516925440
          norm_num
  have hstrict : a < x ∧ x < b := by
    rw [ha_value, hb_value, hx_value]
    norm_num
  have hpolicy :
      fmt.sourceRoundToEvenEvidence x (fmt.finiteRoundToEven x) :=
    fmt.finiteRoundToEven_sourceRoundToEvenEvidence_of_finiteNormalRange hxrange
  have hrightCloser : |x - b| < |x - a| := by
    rw [ha_value, hb_value, hx_value]
    norm_num
  have hround : fmt.finiteRoundToEven x = b :=
    fmt.sourceRoundToEvenEvidence_eq_right_of_realOrderAdjacent_strict_between_right_closer
      hpolicy hadj hstrict hrightCloser
  change fmt.finiteRoundToEven x = (10 : ℝ) ^ 7
  norm_num
  simpa [x, fmt, hb_value] using hround

/-- The first no-pivot multiplier division from the stored Table 1.3 matrix is
the concrete binary32 value `10^7`. -/
theorem hessenbergDetExampleTable13StoredMatrix_firstMultiplier_rounds_to_ten_pow_seven :
    hessenbergDetExampleTable13IeeeSingleFormat.finiteRoundToEvenOp BasicOp.div
        (hessenbergDetExampleTable13StoredMatrix 1 0)
        (hessenbergDetExampleTable13StoredMatrix 0 0) =
      (10 : ℝ) ^ 7 := by
  rw [hessenbergDetExampleTable13_storedMatrix_eq_storedAlpha_matrix]
  simpa [hessenbergDetExampleMatrix] using
    hessenbergDetExampleTable13_round_one_div_storedAlpha

/-- The first Table 1.3 multiplier value `10^7` is representable in binary32. -/
theorem hessenbergDetExampleTable13IeeeSingle_ten_pow_seven_finiteSystem :
    hessenbergDetExampleTable13IeeeSingleFormat.finiteSystem
      ((10 : ℝ) ^ 7) := by
  let fmt := hessenbergDetExampleTable13IeeeSingleFormat
  have hm : fmt.normalizedMantissa 10000000 := by
    norm_num [fmt, hessenbergDetExampleTable13IeeeSingleFormat,
      FloatingPointFormat.ieeeSingleFormat,
      FloatingPointFormat.normalizedMantissa,
      FloatingPointFormat.mantissaInRange,
      FloatingPointFormat.minNormalMantissa]
  have he : fmt.exponentInRange (24 : ℤ) := by
    norm_num [fmt, hessenbergDetExampleTable13IeeeSingleFormat,
      FloatingPointFormat.ieeeSingleFormat,
      FloatingPointFormat.exponentInRange]
  refine Or.inr (Or.inl ⟨false, 10000000, (24 : ℤ), hm, he, ?_⟩)
  norm_num [fmt, hessenbergDetExampleTable13IeeeSingleFormat,
    FloatingPointFormat.ieeeSingleFormat, FloatingPointFormat.normalizedValue,
    FloatingPointFormat.signValue, FloatingPointFormat.betaR, zpow_neg]

/-- The negated first Table 1.3 multiplier value is representable in binary32. -/
theorem hessenbergDetExampleTable13IeeeSingle_neg_ten_pow_seven_finiteSystem :
    hessenbergDetExampleTable13IeeeSingleFormat.finiteSystem
      (-((10 : ℝ) ^ 7)) := by
  let fmt := hessenbergDetExampleTable13IeeeSingleFormat
  simpa [fmt] using
    (fmt.finiteSystem_neg
      hessenbergDetExampleTable13IeeeSingle_ten_pow_seven_finiteSystem)

/-- The first updated diagonal value `10000001` is representable in binary32. -/
theorem hessenbergDetExampleTable13IeeeSingle_firstStageDiag_finiteSystem :
    hessenbergDetExampleTable13IeeeSingleFormat.finiteSystem
      (10000001 : ℝ) := by
  let fmt := hessenbergDetExampleTable13IeeeSingleFormat
  have hm : fmt.normalizedMantissa 10000001 := by
    norm_num [fmt, hessenbergDetExampleTable13IeeeSingleFormat,
      FloatingPointFormat.ieeeSingleFormat,
      FloatingPointFormat.normalizedMantissa,
      FloatingPointFormat.mantissaInRange,
      FloatingPointFormat.minNormalMantissa]
  have he : fmt.exponentInRange (24 : ℤ) := by
    norm_num [fmt, hessenbergDetExampleTable13IeeeSingleFormat,
      FloatingPointFormat.ieeeSingleFormat,
      FloatingPointFormat.exponentInRange]
  refine Or.inr (Or.inl ⟨false, 10000001, (24 : ℤ), hm, he, ?_⟩)
  norm_num [fmt, hessenbergDetExampleTable13IeeeSingleFormat,
    FloatingPointFormat.ieeeSingleFormat, FloatingPointFormat.normalizedValue,
    FloatingPointFormat.signValue, FloatingPointFormat.betaR, zpow_neg]

/-- The first updated superdiagonal value `9999999` is representable in binary32. -/
theorem hessenbergDetExampleTable13IeeeSingle_firstStageSuper_finiteSystem :
    hessenbergDetExampleTable13IeeeSingleFormat.finiteSystem
      (9999999 : ℝ) := by
  let fmt := hessenbergDetExampleTable13IeeeSingleFormat
  have hm : fmt.normalizedMantissa 9999999 := by
    norm_num [fmt, hessenbergDetExampleTable13IeeeSingleFormat,
      FloatingPointFormat.ieeeSingleFormat,
      FloatingPointFormat.normalizedMantissa,
      FloatingPointFormat.mantissaInRange,
      FloatingPointFormat.minNormalMantissa]
  have he : fmt.exponentInRange (24 : ℤ) := by
    norm_num [fmt, hessenbergDetExampleTable13IeeeSingleFormat,
      FloatingPointFormat.ieeeSingleFormat,
      FloatingPointFormat.exponentInRange]
  refine Or.inr (Or.inl ⟨false, 9999999, (24 : ℤ), hm, he, ?_⟩)
  norm_num [fmt, hessenbergDetExampleTable13IeeeSingleFormat,
    FloatingPointFormat.ieeeSingleFormat, FloatingPointFormat.normalizedValue,
    FloatingPointFormat.signValue, FloatingPointFormat.betaR, zpow_neg]

/-- The first-stage product `fl32(10^7*(-1))` is exact. -/
theorem hessenbergDetExampleTable13_round_ten_pow_seven_mul_neg_one :
    hessenbergDetExampleTable13IeeeSingleFormat.finiteRoundToEvenOp BasicOp.mul
        ((10 : ℝ) ^ 7) (-1) =
      -((10 : ℝ) ^ 7) := by
  let fmt := hessenbergDetExampleTable13IeeeSingleFormat
  have hfin :
      fmt.finiteSystem
        (BasicOp.exact BasicOp.mul ((10 : ℝ) ^ 7) (-1)) := by
    convert hessenbergDetExampleTable13IeeeSingle_neg_ten_pow_seven_finiteSystem using 1
    norm_num [BasicOp.exact]
  have hround :=
    (fmt.finiteRoundToEvenOp_eq_exact_of_finiteSystem
      (op := BasicOp.mul) (x := ((10 : ℝ) ^ 7)) (y := (-1 : ℝ)) hfin)
  rw [hround]
  norm_num [BasicOp.exact]

/-- The first-stage diagonal subtraction `fl32(1 - (-10^7))` is exact. -/
theorem hessenbergDetExampleTable13_round_one_sub_neg_ten_pow_seven :
    hessenbergDetExampleTable13IeeeSingleFormat.finiteRoundToEvenOp BasicOp.sub
        (1 : ℝ) (-((10 : ℝ) ^ 7)) =
      (10000001 : ℝ) := by
  let fmt := hessenbergDetExampleTable13IeeeSingleFormat
  have hfin :
      fmt.finiteSystem
        (BasicOp.exact BasicOp.sub (1 : ℝ) (-((10 : ℝ) ^ 7))) := by
    convert hessenbergDetExampleTable13IeeeSingle_firstStageDiag_finiteSystem using 1
    norm_num [BasicOp.exact]
    rfl
  have hround :=
    (fmt.finiteRoundToEvenOp_eq_exact_of_finiteSystem
      (op := BasicOp.sub) (x := (1 : ℝ)) (y := (-((10 : ℝ) ^ 7))) hfin)
  rw [hround]
  norm_num [BasicOp.exact]
  rfl

/-- The first-stage superdiagonal subtraction `fl32((-1) - (-10^7))` is exact. -/
theorem hessenbergDetExampleTable13_round_neg_one_sub_neg_ten_pow_seven :
    hessenbergDetExampleTable13IeeeSingleFormat.finiteRoundToEvenOp BasicOp.sub
        (-1 : ℝ) (-((10 : ℝ) ^ 7)) =
      (9999999 : ℝ) := by
  let fmt := hessenbergDetExampleTable13IeeeSingleFormat
  have hfin :
      fmt.finiteSystem
        (BasicOp.exact BasicOp.sub (-1 : ℝ) (-((10 : ℝ) ^ 7))) := by
    convert hessenbergDetExampleTable13IeeeSingle_firstStageSuper_finiteSystem using 1
    norm_num [BasicOp.exact]
    rfl
  have hround :=
    (fmt.finiteRoundToEvenOp_eq_exact_of_finiteSystem
      (op := BasicOp.sub) (x := (-1 : ℝ)) (y := (-((10 : ℝ) ^ 7))) hfin)
  rw [hround]
  norm_num [BasicOp.exact]
  rfl

/-- Fully nested primitive binary32 operation trace for the first stage diagonal
update `(1,1)` from the stored Table 1.3 matrix. -/
theorem hessenbergDetExampleTable13StoredMatrix_firstStage_diag11_rounds_to :
    hessenbergDetExampleTable13IeeeSingleFormat.finiteRoundToEvenOp BasicOp.sub
        (hessenbergDetExampleTable13StoredMatrix 1 1)
        (hessenbergDetExampleTable13IeeeSingleFormat.finiteRoundToEvenOp BasicOp.mul
          (hessenbergDetExampleTable13IeeeSingleFormat.finiteRoundToEvenOp BasicOp.div
            (hessenbergDetExampleTable13StoredMatrix 1 0)
            (hessenbergDetExampleTable13StoredMatrix 0 0))
          (hessenbergDetExampleTable13StoredMatrix 0 1)) =
      (10000001 : ℝ) := by
  rw [hessenbergDetExampleTable13StoredMatrix_firstMultiplier_rounds_to_ten_pow_seven]
  rw [hessenbergDetExampleTable13_storedMatrix_eq_storedAlpha_matrix]
  simp [hessenbergDetExampleMatrix,
    hessenbergDetExampleTable13_round_ten_pow_seven_mul_neg_one,
    hessenbergDetExampleTable13_round_one_sub_neg_ten_pow_seven]

/-- Fully nested primitive binary32 operation trace for the first stage
superdiagonal update `(1,2)` from the stored Table 1.3 matrix. -/
theorem hessenbergDetExampleTable13StoredMatrix_firstStage_super12_rounds_to :
    hessenbergDetExampleTable13IeeeSingleFormat.finiteRoundToEvenOp BasicOp.sub
        (hessenbergDetExampleTable13StoredMatrix 1 2)
        (hessenbergDetExampleTable13IeeeSingleFormat.finiteRoundToEvenOp BasicOp.mul
          (hessenbergDetExampleTable13IeeeSingleFormat.finiteRoundToEvenOp BasicOp.div
            (hessenbergDetExampleTable13StoredMatrix 1 0)
            (hessenbergDetExampleTable13StoredMatrix 0 0))
          (hessenbergDetExampleTable13StoredMatrix 0 2)) =
      (9999999 : ℝ) := by
  rw [hessenbergDetExampleTable13StoredMatrix_firstMultiplier_rounds_to_ten_pow_seven]
  rw [hessenbergDetExampleTable13_storedMatrix_eq_storedAlpha_matrix]
  simp [hessenbergDetExampleMatrix,
    hessenbergDetExampleTable13_round_ten_pow_seven_mul_neg_one,
    hessenbergDetExampleTable13_round_neg_one_sub_neg_ten_pow_seven]

/-- Fully nested primitive binary32 operation trace for the first stage
superdiagonal update `(1,3)` from the stored Table 1.3 matrix. -/
theorem hessenbergDetExampleTable13StoredMatrix_firstStage_super13_rounds_to :
    hessenbergDetExampleTable13IeeeSingleFormat.finiteRoundToEvenOp BasicOp.sub
        (hessenbergDetExampleTable13StoredMatrix 1 3)
        (hessenbergDetExampleTable13IeeeSingleFormat.finiteRoundToEvenOp BasicOp.mul
          (hessenbergDetExampleTable13IeeeSingleFormat.finiteRoundToEvenOp BasicOp.div
            (hessenbergDetExampleTable13StoredMatrix 1 0)
            (hessenbergDetExampleTable13StoredMatrix 0 0))
          (hessenbergDetExampleTable13StoredMatrix 0 3)) =
      (9999999 : ℝ) := by
  rw [hessenbergDetExampleTable13StoredMatrix_firstMultiplier_rounds_to_ten_pow_seven]
  rw [hessenbergDetExampleTable13_storedMatrix_eq_storedAlpha_matrix]
  simp [hessenbergDetExampleMatrix,
    hessenbergDetExampleTable13_round_ten_pow_seven_mul_neg_one,
    hessenbergDetExampleTable13_round_neg_one_sub_neg_ten_pow_seven]

/-- The second primitive no-pivot GE division for the stored Table 1.3 trace:
nearest/even binary32 rounds `1 / 10000001` to the lower adjacent value with
mantissa `14073747` and exponent `-23`. -/
theorem hessenbergDetExampleTable13_round_one_div_firstStageDiag_eq_normalizedValue :
    hessenbergDetExampleTable13IeeeSingleFormat.finiteRoundToEvenOp BasicOp.div
        (1 : ℝ) (10000001 : ℝ) =
      hessenbergDetExampleTable13IeeeSingleFormat.normalizedValue
        false 14073747 (-23 : ℤ) := by
  let fmt := hessenbergDetExampleTable13IeeeSingleFormat
  let a : ℝ := fmt.normalizedValue false 14073747 (-23 : ℤ)
  let b : ℝ := fmt.normalizedValue false 14073748 (-23 : ℤ)
  let x : ℝ := BasicOp.exact BasicOp.div (1 : ℝ) (10000001 : ℝ)
  have hm : fmt.normalizedMantissa 14073747 := by
    norm_num [fmt, hessenbergDetExampleTable13IeeeSingleFormat,
      FloatingPointFormat.ieeeSingleFormat,
      FloatingPointFormat.normalizedMantissa,
      FloatingPointFormat.mantissaInRange,
      FloatingPointFormat.minNormalMantissa]
  have hmnext : fmt.normalizedMantissa (14073747 + 1) := by
    norm_num [fmt, hessenbergDetExampleTable13IeeeSingleFormat,
      FloatingPointFormat.ieeeSingleFormat,
      FloatingPointFormat.normalizedMantissa,
      FloatingPointFormat.mantissaInRange,
      FloatingPointFormat.minNormalMantissa]
  have hadj : fmt.realOrderAdjacentNormalized a b :=
    fmt.realOrderAdjacentNormalized_of_sameExponentAdjacentNormalized
      ⟨false, 14073747, (-23 : ℤ), hm, hmnext, Or.inl ⟨rfl, rfl⟩⟩
  have ha_value : a = (14073747 : ℝ) * (2 : ℝ) ^ (-47 : ℤ) := by
    norm_num [a, fmt, hessenbergDetExampleTable13IeeeSingleFormat,
      FloatingPointFormat.ieeeSingleFormat, FloatingPointFormat.normalizedValue,
      FloatingPointFormat.signValue, FloatingPointFormat.betaR, zpow_neg]
  have hb_value : b = (14073748 : ℝ) * (2 : ℝ) ^ (-47 : ℤ) := by
    norm_num [b, fmt, hessenbergDetExampleTable13IeeeSingleFormat,
      FloatingPointFormat.ieeeSingleFormat, FloatingPointFormat.normalizedValue,
      FloatingPointFormat.signValue, FloatingPointFormat.betaR, zpow_neg]
  have hx_value : x = (1 : ℝ) / 10000001 := by
    norm_num [x, BasicOp.exact]
  have hxrange : fmt.finiteNormalRange x := by
    rw [FloatingPointFormat.finiteNormalRange]
    rw [hx_value, abs_of_pos (by norm_num)]
    constructor
    · norm_num [fmt, hessenbergDetExampleTable13IeeeSingleFormat,
        FloatingPointFormat.ieeeSingleFormat,
        FloatingPointFormat.minNormalMagnitude, FloatingPointFormat.betaR,
        zpow_neg]
    · calc
        (1 : ℝ) / 10000001 ≤ 1 := by
          norm_num
        _ ≤ fmt.maxFiniteMagnitude := by
          norm_num [fmt, hessenbergDetExampleTable13IeeeSingleFormat,
            FloatingPointFormat.ieeeSingleFormat,
            FloatingPointFormat.maxFiniteMagnitude, FloatingPointFormat.betaR,
            zpow_neg]
          change (1 : ℝ) ≤ 340282346638528859811704183484516925440
          norm_num
  have hstrict : a < x ∧ x < b := by
    rw [ha_value, hb_value, hx_value]
    norm_num
  have hpolicy :
      fmt.sourceRoundToEvenEvidence x (fmt.finiteRoundToEven x) :=
    fmt.finiteRoundToEven_sourceRoundToEvenEvidence_of_finiteNormalRange hxrange
  have hleftCloser : |x - a| < |x - b| := by
    rw [ha_value, hb_value, hx_value]
    norm_num
  have hround : fmt.finiteRoundToEven x = a :=
    fmt.sourceRoundToEvenEvidence_eq_left_of_realOrderAdjacent_strict_between_left_closer
      hpolicy hadj hstrict hleftCloser
  change fmt.finiteRoundToEven x =
    fmt.normalizedValue false 14073747 (-23 : ℤ)
  simpa [x, a, fmt] using hround

/-- Closed rational form of the second no-pivot multiplier division. -/
theorem hessenbergDetExampleTable13_round_one_div_firstStageDiag :
    hessenbergDetExampleTable13IeeeSingleFormat.finiteRoundToEvenOp BasicOp.div
        (1 : ℝ) (10000001 : ℝ) =
      14073747 / (2 : ℝ) ^ 47 := by
  rw [hessenbergDetExampleTable13_round_one_div_firstStageDiag_eq_normalizedValue]
  norm_num [hessenbergDetExampleTable13IeeeSingleFormat,
    FloatingPointFormat.ieeeSingleFormat, FloatingPointFormat.normalizedValue,
    FloatingPointFormat.signValue, FloatingPointFormat.betaR, zpow_neg]

/-- Fully nested primitive binary32 trace for the second no-pivot multiplier
division from the stored Table 1.3 matrix after the first-row update. -/
theorem hessenbergDetExampleTable13StoredMatrix_secondMultiplier_rounds_to :
    hessenbergDetExampleTable13IeeeSingleFormat.finiteRoundToEvenOp BasicOp.div
        (hessenbergDetExampleTable13StoredMatrix 2 1)
        (hessenbergDetExampleTable13IeeeSingleFormat.finiteRoundToEvenOp BasicOp.sub
          (hessenbergDetExampleTable13StoredMatrix 1 1)
          (hessenbergDetExampleTable13IeeeSingleFormat.finiteRoundToEvenOp BasicOp.mul
            (hessenbergDetExampleTable13IeeeSingleFormat.finiteRoundToEvenOp BasicOp.div
              (hessenbergDetExampleTable13StoredMatrix 1 0)
              (hessenbergDetExampleTable13StoredMatrix 0 0))
            (hessenbergDetExampleTable13StoredMatrix 0 1))) =
      14073747 / (2 : ℝ) ^ 47 := by
  rw [hessenbergDetExampleTable13StoredMatrix_firstStage_diag11_rounds_to]
  rw [hessenbergDetExampleTable13_storedMatrix_eq_storedAlpha_matrix]
  simpa [hessenbergDetExampleMatrix] using
    hessenbergDetExampleTable13_round_one_div_firstStageDiag

/-- The second-stage product value `4194303/4194304` is representable in
binary32. -/
theorem hessenbergDetExampleTable13IeeeSingle_secondStageProduct_finiteSystem :
    hessenbergDetExampleTable13IeeeSingleFormat.finiteSystem
      (4194303 / 4194304 : ℝ) := by
  let fmt := hessenbergDetExampleTable13IeeeSingleFormat
  have hm : fmt.normalizedMantissa 16777212 := by
    norm_num [fmt, hessenbergDetExampleTable13IeeeSingleFormat,
      FloatingPointFormat.ieeeSingleFormat,
      FloatingPointFormat.normalizedMantissa,
      FloatingPointFormat.mantissaInRange,
      FloatingPointFormat.minNormalMantissa]
  have he : fmt.exponentInRange (0 : ℤ) := by
    norm_num [fmt, hessenbergDetExampleTable13IeeeSingleFormat,
      FloatingPointFormat.ieeeSingleFormat,
      FloatingPointFormat.exponentInRange]
  refine Or.inr (Or.inl ⟨false, 16777212, (0 : ℤ), hm, he, ?_⟩)
  norm_num [fmt, hessenbergDetExampleTable13IeeeSingleFormat,
    FloatingPointFormat.ieeeSingleFormat, FloatingPointFormat.normalizedValue,
    FloatingPointFormat.signValue, FloatingPointFormat.betaR, zpow_neg]

/-- The second-stage diagonal update value `2^-22` is representable in
binary32. -/
theorem hessenbergDetExampleTable13IeeeSingle_secondStageDiag_finiteSystem :
    hessenbergDetExampleTable13IeeeSingleFormat.finiteSystem
      (1 / 4194304 : ℝ) := by
  let fmt := hessenbergDetExampleTable13IeeeSingleFormat
  have hm : fmt.normalizedMantissa 8388608 := by
    norm_num [fmt, hessenbergDetExampleTable13IeeeSingleFormat,
      FloatingPointFormat.ieeeSingleFormat,
      FloatingPointFormat.normalizedMantissa,
      FloatingPointFormat.mantissaInRange,
      FloatingPointFormat.minNormalMantissa]
  have he : fmt.exponentInRange (-21 : ℤ) := by
    norm_num [fmt, hessenbergDetExampleTable13IeeeSingleFormat,
      FloatingPointFormat.ieeeSingleFormat,
      FloatingPointFormat.exponentInRange]
  refine Or.inr (Or.inl ⟨false, 8388608, (-21 : ℤ), hm, he, ?_⟩)
  norm_num [fmt, hessenbergDetExampleTable13IeeeSingleFormat,
    FloatingPointFormat.ieeeSingleFormat, FloatingPointFormat.normalizedValue,
    FloatingPointFormat.signValue, FloatingPointFormat.betaR, zpow_neg]

/-- The second-stage superdiagonal update value `-8388607/4194304` is
representable in binary32. -/
theorem hessenbergDetExampleTable13IeeeSingle_secondStageSuper_finiteSystem :
    hessenbergDetExampleTable13IeeeSingleFormat.finiteSystem
      (-8388607 / 4194304 : ℝ) := by
  let fmt := hessenbergDetExampleTable13IeeeSingleFormat
  have hm : fmt.normalizedMantissa 16777214 := by
    norm_num [fmt, hessenbergDetExampleTable13IeeeSingleFormat,
      FloatingPointFormat.ieeeSingleFormat,
      FloatingPointFormat.normalizedMantissa,
      FloatingPointFormat.mantissaInRange,
      FloatingPointFormat.minNormalMantissa]
  have he : fmt.exponentInRange (1 : ℤ) := by
    norm_num [fmt, hessenbergDetExampleTable13IeeeSingleFormat,
      FloatingPointFormat.ieeeSingleFormat,
      FloatingPointFormat.exponentInRange]
  refine Or.inr (Or.inl ⟨true, 16777214, (1 : ℤ), hm, he, ?_⟩)
  norm_num [fmt, hessenbergDetExampleTable13IeeeSingleFormat,
    FloatingPointFormat.ieeeSingleFormat, FloatingPointFormat.normalizedValue,
    FloatingPointFormat.signValue, FloatingPointFormat.betaR, zpow_neg]

/-- The second-stage product in the stored Table 1.3 trace:
`fl32((14073747/2^47)*9999999)` rounds down to `4194303/4194304`. -/
theorem hessenbergDetExampleTable13_round_secondMultiplier_mul_firstStageSuper :
    hessenbergDetExampleTable13IeeeSingleFormat.finiteRoundToEvenOp BasicOp.mul
        (14073747 / (2 : ℝ) ^ 47) (9999999 : ℝ) =
      4194303 / 4194304 := by
  let fmt := hessenbergDetExampleTable13IeeeSingleFormat
  let a : ℝ := fmt.normalizedValue false 16777212 (0 : ℤ)
  let b : ℝ := fmt.normalizedValue false 16777213 (0 : ℤ)
  let x : ℝ := BasicOp.exact BasicOp.mul
    (14073747 / (2 : ℝ) ^ 47) (9999999 : ℝ)
  have hm : fmt.normalizedMantissa 16777212 := by
    norm_num [fmt, hessenbergDetExampleTable13IeeeSingleFormat,
      FloatingPointFormat.ieeeSingleFormat,
      FloatingPointFormat.normalizedMantissa,
      FloatingPointFormat.mantissaInRange,
      FloatingPointFormat.minNormalMantissa]
  have hmnext : fmt.normalizedMantissa (16777212 + 1) := by
    norm_num [fmt, hessenbergDetExampleTable13IeeeSingleFormat,
      FloatingPointFormat.ieeeSingleFormat,
      FloatingPointFormat.normalizedMantissa,
      FloatingPointFormat.mantissaInRange,
      FloatingPointFormat.minNormalMantissa]
  have hadj : fmt.realOrderAdjacentNormalized a b :=
    fmt.realOrderAdjacentNormalized_of_sameExponentAdjacentNormalized
      ⟨false, 16777212, (0 : ℤ), hm, hmnext, Or.inl ⟨rfl, rfl⟩⟩
  have ha_value : a = (4194303 : ℝ) / 4194304 := by
    norm_num [a, fmt, hessenbergDetExampleTable13IeeeSingleFormat,
      FloatingPointFormat.ieeeSingleFormat, FloatingPointFormat.normalizedValue,
      FloatingPointFormat.signValue, FloatingPointFormat.betaR, zpow_neg]
  have hb_value : b = (16777213 : ℝ) / 16777216 := by
    norm_num [b, fmt, hessenbergDetExampleTable13IeeeSingleFormat,
      FloatingPointFormat.ieeeSingleFormat, FloatingPointFormat.normalizedValue,
      FloatingPointFormat.signValue, FloatingPointFormat.betaR, zpow_neg]
  have hx_value : x = (140737455926253 : ℝ) / 140737488355328 := by
    norm_num [x, BasicOp.exact]
  have hxrange : fmt.finiteNormalRange x := by
    rw [FloatingPointFormat.finiteNormalRange]
    rw [hx_value, abs_of_pos (by norm_num)]
    constructor
    · norm_num [fmt, hessenbergDetExampleTable13IeeeSingleFormat,
        FloatingPointFormat.ieeeSingleFormat,
        FloatingPointFormat.minNormalMagnitude, FloatingPointFormat.betaR,
        zpow_neg]
    · calc
        (140737455926253 : ℝ) / 140737488355328 ≤ 1 := by
          norm_num
        _ ≤ fmt.maxFiniteMagnitude := by
          norm_num [fmt, hessenbergDetExampleTable13IeeeSingleFormat,
            FloatingPointFormat.ieeeSingleFormat,
            FloatingPointFormat.maxFiniteMagnitude, FloatingPointFormat.betaR,
            zpow_neg]
          change (1 : ℝ) ≤ 340282346638528859811704183484516925440
          norm_num
  have hstrict : a < x ∧ x < b := by
    rw [ha_value, hb_value, hx_value]
    norm_num
  have hpolicy :
      fmt.sourceRoundToEvenEvidence x (fmt.finiteRoundToEven x) :=
    fmt.finiteRoundToEven_sourceRoundToEvenEvidence_of_finiteNormalRange hxrange
  have hleftCloser : |x - a| < |x - b| := by
    rw [ha_value, hb_value, hx_value]
    norm_num
  have hround : fmt.finiteRoundToEven x = a :=
    fmt.sourceRoundToEvenEvidence_eq_left_of_realOrderAdjacent_strict_between_left_closer
      hpolicy hadj hstrict hleftCloser
  change fmt.finiteRoundToEven x = (4194303 : ℝ) / 4194304
  simpa [x, fmt, ha_value] using hround

/-- The second-stage diagonal subtraction `fl32(1 - 4194303/4194304)` is exact. -/
theorem hessenbergDetExampleTable13_round_one_sub_secondStageProduct :
    hessenbergDetExampleTable13IeeeSingleFormat.finiteRoundToEvenOp BasicOp.sub
        (1 : ℝ) (4194303 / 4194304 : ℝ) =
      1 / 4194304 := by
  let fmt := hessenbergDetExampleTable13IeeeSingleFormat
  have hfin :
      fmt.finiteSystem
        (BasicOp.exact BasicOp.sub (1 : ℝ) (4194303 / 4194304 : ℝ)) := by
    convert hessenbergDetExampleTable13IeeeSingle_secondStageDiag_finiteSystem using 1
    norm_num [BasicOp.exact]
  have hround :=
    (fmt.finiteRoundToEvenOp_eq_exact_of_finiteSystem
      (op := BasicOp.sub) (x := (1 : ℝ)) (y := (4194303 / 4194304 : ℝ)) hfin)
  rw [hround]
  norm_num [BasicOp.exact]

/-- The second-stage superdiagonal subtraction
`fl32((-1) - 4194303/4194304)` is exact. -/
theorem hessenbergDetExampleTable13_round_neg_one_sub_secondStageProduct :
    hessenbergDetExampleTable13IeeeSingleFormat.finiteRoundToEvenOp BasicOp.sub
        (-1 : ℝ) (4194303 / 4194304 : ℝ) =
      -8388607 / 4194304 := by
  let fmt := hessenbergDetExampleTable13IeeeSingleFormat
  have hfin :
      fmt.finiteSystem
        (BasicOp.exact BasicOp.sub (-1 : ℝ) (4194303 / 4194304 : ℝ)) := by
    convert hessenbergDetExampleTable13IeeeSingle_secondStageSuper_finiteSystem using 1
    norm_num [BasicOp.exact]
  have hround :=
    (fmt.finiteRoundToEvenOp_eq_exact_of_finiteSystem
      (op := BasicOp.sub) (x := (-1 : ℝ)) (y := (4194303 / 4194304 : ℝ)) hfin)
  rw [hround]
  norm_num [BasicOp.exact]

/-- Fully nested primitive binary32 trace for the second-stage diagonal update
`(2,2)` from the stored Table 1.3 matrix. -/
theorem hessenbergDetExampleTable13StoredMatrix_secondStage_diag22_rounds_to :
    hessenbergDetExampleTable13IeeeSingleFormat.finiteRoundToEvenOp BasicOp.sub
        (hessenbergDetExampleTable13StoredMatrix 2 2)
        (hessenbergDetExampleTable13IeeeSingleFormat.finiteRoundToEvenOp BasicOp.mul
          (hessenbergDetExampleTable13IeeeSingleFormat.finiteRoundToEvenOp BasicOp.div
            (hessenbergDetExampleTable13StoredMatrix 2 1)
            (hessenbergDetExampleTable13IeeeSingleFormat.finiteRoundToEvenOp BasicOp.sub
              (hessenbergDetExampleTable13StoredMatrix 1 1)
              (hessenbergDetExampleTable13IeeeSingleFormat.finiteRoundToEvenOp BasicOp.mul
                (hessenbergDetExampleTable13IeeeSingleFormat.finiteRoundToEvenOp BasicOp.div
                  (hessenbergDetExampleTable13StoredMatrix 1 0)
                  (hessenbergDetExampleTable13StoredMatrix 0 0))
                (hessenbergDetExampleTable13StoredMatrix 0 1))))
          (hessenbergDetExampleTable13IeeeSingleFormat.finiteRoundToEvenOp BasicOp.sub
            (hessenbergDetExampleTable13StoredMatrix 1 2)
            (hessenbergDetExampleTable13IeeeSingleFormat.finiteRoundToEvenOp BasicOp.mul
              (hessenbergDetExampleTable13IeeeSingleFormat.finiteRoundToEvenOp BasicOp.div
                (hessenbergDetExampleTable13StoredMatrix 1 0)
                (hessenbergDetExampleTable13StoredMatrix 0 0))
              (hessenbergDetExampleTable13StoredMatrix 0 2)))) =
      1 / 4194304 := by
  rw [hessenbergDetExampleTable13StoredMatrix_secondMultiplier_rounds_to]
  rw [hessenbergDetExampleTable13StoredMatrix_firstStage_super12_rounds_to]
  rw [hessenbergDetExampleTable13_storedMatrix_eq_storedAlpha_matrix]
  simp [hessenbergDetExampleMatrix,
    hessenbergDetExampleTable13_round_secondMultiplier_mul_firstStageSuper,
    hessenbergDetExampleTable13_round_one_sub_secondStageProduct]

/-- Fully nested primitive binary32 trace for the second-stage superdiagonal
update `(2,3)` from the stored Table 1.3 matrix. -/
theorem hessenbergDetExampleTable13StoredMatrix_secondStage_super23_rounds_to :
    hessenbergDetExampleTable13IeeeSingleFormat.finiteRoundToEvenOp BasicOp.sub
        (hessenbergDetExampleTable13StoredMatrix 2 3)
        (hessenbergDetExampleTable13IeeeSingleFormat.finiteRoundToEvenOp BasicOp.mul
          (hessenbergDetExampleTable13IeeeSingleFormat.finiteRoundToEvenOp BasicOp.div
            (hessenbergDetExampleTable13StoredMatrix 2 1)
            (hessenbergDetExampleTable13IeeeSingleFormat.finiteRoundToEvenOp BasicOp.sub
              (hessenbergDetExampleTable13StoredMatrix 1 1)
              (hessenbergDetExampleTable13IeeeSingleFormat.finiteRoundToEvenOp BasicOp.mul
                (hessenbergDetExampleTable13IeeeSingleFormat.finiteRoundToEvenOp BasicOp.div
                  (hessenbergDetExampleTable13StoredMatrix 1 0)
                  (hessenbergDetExampleTable13StoredMatrix 0 0))
                (hessenbergDetExampleTable13StoredMatrix 0 1))))
          (hessenbergDetExampleTable13IeeeSingleFormat.finiteRoundToEvenOp BasicOp.sub
            (hessenbergDetExampleTable13StoredMatrix 1 3)
            (hessenbergDetExampleTable13IeeeSingleFormat.finiteRoundToEvenOp BasicOp.mul
              (hessenbergDetExampleTable13IeeeSingleFormat.finiteRoundToEvenOp BasicOp.div
                (hessenbergDetExampleTable13StoredMatrix 1 0)
                (hessenbergDetExampleTable13StoredMatrix 0 0))
              (hessenbergDetExampleTable13StoredMatrix 0 3)))) =
      -8388607 / 4194304 := by
  rw [hessenbergDetExampleTable13StoredMatrix_secondMultiplier_rounds_to]
  rw [hessenbergDetExampleTable13StoredMatrix_firstStage_super13_rounds_to]
  rw [hessenbergDetExampleTable13_storedMatrix_eq_storedAlpha_matrix]
  simp [hessenbergDetExampleMatrix,
    hessenbergDetExampleTable13_round_secondMultiplier_mul_firstStageSuper,
    hessenbergDetExampleTable13_round_neg_one_sub_secondStageProduct]

/-- The final multiplier value `4194304 = 2^22` is representable in binary32. -/
theorem hessenbergDetExampleTable13IeeeSingle_thirdMultiplier_finiteSystem :
    hessenbergDetExampleTable13IeeeSingleFormat.finiteSystem
      (4194304 : ℝ) := by
  let fmt := hessenbergDetExampleTable13IeeeSingleFormat
  have hm : fmt.normalizedMantissa 8388608 := by
    norm_num [fmt, hessenbergDetExampleTable13IeeeSingleFormat,
      FloatingPointFormat.ieeeSingleFormat,
      FloatingPointFormat.normalizedMantissa,
      FloatingPointFormat.mantissaInRange,
      FloatingPointFormat.minNormalMantissa]
  have he : fmt.exponentInRange (23 : ℤ) := by
    norm_num [fmt, hessenbergDetExampleTable13IeeeSingleFormat,
      FloatingPointFormat.ieeeSingleFormat,
      FloatingPointFormat.exponentInRange]
  refine Or.inr (Or.inl ⟨false, 8388608, (23 : ℤ), hm, he, ?_⟩)
  norm_num [fmt, hessenbergDetExampleTable13IeeeSingleFormat,
    FloatingPointFormat.ieeeSingleFormat, FloatingPointFormat.normalizedValue,
    FloatingPointFormat.signValue, FloatingPointFormat.betaR, zpow_neg]
  rfl

/-- The final-stage product value `-8388607` is representable in binary32. -/
theorem hessenbergDetExampleTable13IeeeSingle_thirdStageProduct_finiteSystem :
    hessenbergDetExampleTable13IeeeSingleFormat.finiteSystem
      (-8388607 : ℝ) := by
  let fmt := hessenbergDetExampleTable13IeeeSingleFormat
  have hm : fmt.normalizedMantissa 16777214 := by
    norm_num [fmt, hessenbergDetExampleTable13IeeeSingleFormat,
      FloatingPointFormat.ieeeSingleFormat,
      FloatingPointFormat.normalizedMantissa,
      FloatingPointFormat.mantissaInRange,
      FloatingPointFormat.minNormalMantissa]
  have he : fmt.exponentInRange (23 : ℤ) := by
    norm_num [fmt, hessenbergDetExampleTable13IeeeSingleFormat,
      FloatingPointFormat.ieeeSingleFormat,
      FloatingPointFormat.exponentInRange]
  refine Or.inr (Or.inl ⟨true, 16777214, (23 : ℤ), hm, he, ?_⟩)
  norm_num [fmt, hessenbergDetExampleTable13IeeeSingleFormat,
    FloatingPointFormat.ieeeSingleFormat, FloatingPointFormat.normalizedValue,
    FloatingPointFormat.signValue, FloatingPointFormat.betaR, zpow_neg]

/-- The final diagonal value `8388608 = 2^23` is representable in binary32. -/
theorem hessenbergDetExampleTable13IeeeSingle_finalDiag_finiteSystem :
    hessenbergDetExampleTable13IeeeSingleFormat.finiteSystem
      (8388608 : ℝ) := by
  let fmt := hessenbergDetExampleTable13IeeeSingleFormat
  have hm : fmt.normalizedMantissa 8388608 := by
    norm_num [fmt, hessenbergDetExampleTable13IeeeSingleFormat,
      FloatingPointFormat.ieeeSingleFormat,
      FloatingPointFormat.normalizedMantissa,
      FloatingPointFormat.mantissaInRange,
      FloatingPointFormat.minNormalMantissa]
  have he : fmt.exponentInRange (24 : ℤ) := by
    norm_num [fmt, hessenbergDetExampleTable13IeeeSingleFormat,
      FloatingPointFormat.ieeeSingleFormat,
      FloatingPointFormat.exponentInRange]
  refine Or.inr (Or.inl ⟨false, 8388608, (24 : ℤ), hm, he, ?_⟩)
  norm_num [fmt, hessenbergDetExampleTable13IeeeSingleFormat,
    FloatingPointFormat.ieeeSingleFormat, FloatingPointFormat.normalizedValue,
    FloatingPointFormat.signValue, FloatingPointFormat.betaR, zpow_neg]

/-- The final no-pivot multiplier division is exact:
`fl32(1/(1/4194304)) = 4194304`. -/
theorem hessenbergDetExampleTable13_round_one_div_secondStageDiag :
    hessenbergDetExampleTable13IeeeSingleFormat.finiteRoundToEvenOp BasicOp.div
        (1 : ℝ) (1 / 4194304 : ℝ) =
      4194304 := by
  let fmt := hessenbergDetExampleTable13IeeeSingleFormat
  have hfin :
      fmt.finiteSystem
        (BasicOp.exact BasicOp.div (1 : ℝ) (1 / 4194304 : ℝ)) := by
    convert hessenbergDetExampleTable13IeeeSingle_thirdMultiplier_finiteSystem using 1
    norm_num [BasicOp.exact]
    rfl
  have hround :=
    (fmt.finiteRoundToEvenOp_eq_exact_of_finiteSystem
      (op := BasicOp.div) (x := (1 : ℝ)) (y := (1 / 4194304 : ℝ)) hfin)
  rw [hround]
  norm_num [BasicOp.exact]
  rfl

/-- The final-stage product `fl32(4194304*(-8388607/4194304))` is exact. -/
theorem hessenbergDetExampleTable13_round_thirdMultiplier_mul_secondStageSuper :
    hessenbergDetExampleTable13IeeeSingleFormat.finiteRoundToEvenOp BasicOp.mul
        (4194304 : ℝ) (-8388607 / 4194304 : ℝ) =
      -8388607 := by
  let fmt := hessenbergDetExampleTable13IeeeSingleFormat
  have hfin :
      fmt.finiteSystem
        (BasicOp.exact BasicOp.mul (4194304 : ℝ) (-8388607 / 4194304 : ℝ)) := by
    convert hessenbergDetExampleTable13IeeeSingle_thirdStageProduct_finiteSystem using 1
    norm_num [BasicOp.exact]
  have hround :=
    (fmt.finiteRoundToEvenOp_eq_exact_of_finiteSystem
      (op := BasicOp.mul) (x := (4194304 : ℝ)) (y := (-8388607 / 4194304 : ℝ)) hfin)
  rw [hround]
  norm_num [BasicOp.exact]

/-- The final diagonal subtraction `fl32(1 - (-8388607))` is exact. -/
theorem hessenbergDetExampleTable13_round_one_sub_thirdStageProduct :
    hessenbergDetExampleTable13IeeeSingleFormat.finiteRoundToEvenOp BasicOp.sub
        (1 : ℝ) (-8388607 : ℝ) =
      8388608 := by
  let fmt := hessenbergDetExampleTable13IeeeSingleFormat
  have hfin :
      fmt.finiteSystem
        (BasicOp.exact BasicOp.sub (1 : ℝ) (-8388607 : ℝ)) := by
    convert hessenbergDetExampleTable13IeeeSingle_finalDiag_finiteSystem using 1
    norm_num [BasicOp.exact]
    rfl
  have hround :=
    (fmt.finiteRoundToEvenOp_eq_exact_of_finiteSystem
      (op := BasicOp.sub) (x := (1 : ℝ)) (y := (-8388607 : ℝ)) hfin)
  rw [hround]
  norm_num [BasicOp.exact]
  rfl

/-- Fully nested primitive binary32 trace for the final no-pivot multiplier
division from the stored Table 1.3 matrix. -/
theorem hessenbergDetExampleTable13StoredMatrix_thirdMultiplier_rounds_to :
    hessenbergDetExampleTable13IeeeSingleFormat.finiteRoundToEvenOp BasicOp.div
        (hessenbergDetExampleTable13StoredMatrix 3 2)
        (hessenbergDetExampleTable13IeeeSingleFormat.finiteRoundToEvenOp BasicOp.sub
          (hessenbergDetExampleTable13StoredMatrix 2 2)
          (hessenbergDetExampleTable13IeeeSingleFormat.finiteRoundToEvenOp BasicOp.mul
            (hessenbergDetExampleTable13IeeeSingleFormat.finiteRoundToEvenOp BasicOp.div
              (hessenbergDetExampleTable13StoredMatrix 2 1)
              (hessenbergDetExampleTable13IeeeSingleFormat.finiteRoundToEvenOp BasicOp.sub
                (hessenbergDetExampleTable13StoredMatrix 1 1)
                (hessenbergDetExampleTable13IeeeSingleFormat.finiteRoundToEvenOp BasicOp.mul
                  (hessenbergDetExampleTable13IeeeSingleFormat.finiteRoundToEvenOp BasicOp.div
                    (hessenbergDetExampleTable13StoredMatrix 1 0)
                    (hessenbergDetExampleTable13StoredMatrix 0 0))
                  (hessenbergDetExampleTable13StoredMatrix 0 1))))
            (hessenbergDetExampleTable13IeeeSingleFormat.finiteRoundToEvenOp BasicOp.sub
              (hessenbergDetExampleTable13StoredMatrix 1 2)
              (hessenbergDetExampleTable13IeeeSingleFormat.finiteRoundToEvenOp BasicOp.mul
                (hessenbergDetExampleTable13IeeeSingleFormat.finiteRoundToEvenOp BasicOp.div
                  (hessenbergDetExampleTable13StoredMatrix 1 0)
                  (hessenbergDetExampleTable13StoredMatrix 0 0))
                (hessenbergDetExampleTable13StoredMatrix 0 2))))) =
      4194304 := by
  rw [hessenbergDetExampleTable13StoredMatrix_secondStage_diag22_rounds_to]
  rw [hessenbergDetExampleTable13_storedMatrix_eq_storedAlpha_matrix]
  simpa [hessenbergDetExampleMatrix] using
    hessenbergDetExampleTable13_round_one_div_secondStageDiag

/-- Fully nested primitive binary32 trace for the final diagonal update `(3,3)`
from the stored Table 1.3 matrix. -/
theorem hessenbergDetExampleTable13StoredMatrix_finalDiag_rounds_to :
    hessenbergDetExampleTable13IeeeSingleFormat.finiteRoundToEvenOp BasicOp.sub
        (hessenbergDetExampleTable13StoredMatrix 3 3)
        (hessenbergDetExampleTable13IeeeSingleFormat.finiteRoundToEvenOp BasicOp.mul
          (hessenbergDetExampleTable13IeeeSingleFormat.finiteRoundToEvenOp BasicOp.div
            (hessenbergDetExampleTable13StoredMatrix 3 2)
            (hessenbergDetExampleTable13IeeeSingleFormat.finiteRoundToEvenOp BasicOp.sub
              (hessenbergDetExampleTable13StoredMatrix 2 2)
              (hessenbergDetExampleTable13IeeeSingleFormat.finiteRoundToEvenOp BasicOp.mul
                (hessenbergDetExampleTable13IeeeSingleFormat.finiteRoundToEvenOp BasicOp.div
                  (hessenbergDetExampleTable13StoredMatrix 2 1)
                  (hessenbergDetExampleTable13IeeeSingleFormat.finiteRoundToEvenOp BasicOp.sub
                    (hessenbergDetExampleTable13StoredMatrix 1 1)
                    (hessenbergDetExampleTable13IeeeSingleFormat.finiteRoundToEvenOp BasicOp.mul
                      (hessenbergDetExampleTable13IeeeSingleFormat.finiteRoundToEvenOp BasicOp.div
                        (hessenbergDetExampleTable13StoredMatrix 1 0)
                        (hessenbergDetExampleTable13StoredMatrix 0 0))
                      (hessenbergDetExampleTable13StoredMatrix 0 1))))
                (hessenbergDetExampleTable13IeeeSingleFormat.finiteRoundToEvenOp BasicOp.sub
                  (hessenbergDetExampleTable13StoredMatrix 1 2)
                  (hessenbergDetExampleTable13IeeeSingleFormat.finiteRoundToEvenOp BasicOp.mul
                    (hessenbergDetExampleTable13IeeeSingleFormat.finiteRoundToEvenOp BasicOp.div
                      (hessenbergDetExampleTable13StoredMatrix 1 0)
                      (hessenbergDetExampleTable13StoredMatrix 0 0))
                    (hessenbergDetExampleTable13StoredMatrix 0 2))))))
          (hessenbergDetExampleTable13IeeeSingleFormat.finiteRoundToEvenOp BasicOp.sub
            (hessenbergDetExampleTable13StoredMatrix 2 3)
            (hessenbergDetExampleTable13IeeeSingleFormat.finiteRoundToEvenOp BasicOp.mul
              (hessenbergDetExampleTable13IeeeSingleFormat.finiteRoundToEvenOp BasicOp.div
                (hessenbergDetExampleTable13StoredMatrix 2 1)
                (hessenbergDetExampleTable13IeeeSingleFormat.finiteRoundToEvenOp BasicOp.sub
                  (hessenbergDetExampleTable13StoredMatrix 1 1)
                  (hessenbergDetExampleTable13IeeeSingleFormat.finiteRoundToEvenOp BasicOp.mul
                    (hessenbergDetExampleTable13IeeeSingleFormat.finiteRoundToEvenOp BasicOp.div
                      (hessenbergDetExampleTable13StoredMatrix 1 0)
                      (hessenbergDetExampleTable13StoredMatrix 0 0))
                    (hessenbergDetExampleTable13StoredMatrix 0 1))))
              (hessenbergDetExampleTable13IeeeSingleFormat.finiteRoundToEvenOp BasicOp.sub
                (hessenbergDetExampleTable13StoredMatrix 1 3)
                (hessenbergDetExampleTable13IeeeSingleFormat.finiteRoundToEvenOp BasicOp.mul
                  (hessenbergDetExampleTable13IeeeSingleFormat.finiteRoundToEvenOp BasicOp.div
                    (hessenbergDetExampleTable13StoredMatrix 1 0)
                    (hessenbergDetExampleTable13StoredMatrix 0 0))
                  (hessenbergDetExampleTable13StoredMatrix 0 3)))))) =
      8388608 := by
  rw [hessenbergDetExampleTable13StoredMatrix_thirdMultiplier_rounds_to]
  rw [hessenbergDetExampleTable13StoredMatrix_secondStage_super23_rounds_to]
  rw [hessenbergDetExampleTable13_storedMatrix_eq_storedAlpha_matrix]
  simp [hessenbergDetExampleMatrix,
    hessenbergDetExampleTable13_round_thirdMultiplier_mul_secondStageSuper,
    hessenbergDetExampleTable13_round_one_sub_thirdStageProduct]

/-- The first left-to-right determinant product prefix is representable in
binary32. -/
theorem hessenbergDetExampleTable13IeeeSingle_detProduct01_finiteSystem :
    hessenbergDetExampleTable13IeeeSingleFormat.finiteSystem
      (8388609 / 8388608 : ℝ) := by
  let fmt := hessenbergDetExampleTable13IeeeSingleFormat
  have hm : fmt.normalizedMantissa 8388609 := by
    norm_num [fmt, hessenbergDetExampleTable13IeeeSingleFormat,
      FloatingPointFormat.ieeeSingleFormat,
      FloatingPointFormat.normalizedMantissa,
      FloatingPointFormat.mantissaInRange,
      FloatingPointFormat.minNormalMantissa]
  have he : fmt.exponentInRange (1 : ℤ) := by
    norm_num [fmt, hessenbergDetExampleTable13IeeeSingleFormat,
      FloatingPointFormat.ieeeSingleFormat,
      FloatingPointFormat.exponentInRange]
  refine Or.inr (Or.inl ⟨false, 8388609, (1 : ℤ), hm, he, ?_⟩)
  norm_num [fmt, hessenbergDetExampleTable13IeeeSingleFormat,
    FloatingPointFormat.ieeeSingleFormat, FloatingPointFormat.normalizedValue,
    FloatingPointFormat.signValue, FloatingPointFormat.betaR, zpow_neg]

/-- The second left-to-right determinant product prefix is representable in
binary32. -/
theorem hessenbergDetExampleTable13IeeeSingle_detProduct012_finiteSystem :
    hessenbergDetExampleTable13IeeeSingleFormat.finiteSystem
      (8388609 / (2 : ℝ) ^ 45) := by
  let fmt := hessenbergDetExampleTable13IeeeSingleFormat
  have hm : fmt.normalizedMantissa 8388609 := by
    norm_num [fmt, hessenbergDetExampleTable13IeeeSingleFormat,
      FloatingPointFormat.ieeeSingleFormat,
      FloatingPointFormat.normalizedMantissa,
      FloatingPointFormat.mantissaInRange,
      FloatingPointFormat.minNormalMantissa]
  have he : fmt.exponentInRange (-21 : ℤ) := by
    norm_num [fmt, hessenbergDetExampleTable13IeeeSingleFormat,
      FloatingPointFormat.ieeeSingleFormat,
      FloatingPointFormat.exponentInRange]
  refine Or.inr (Or.inl ⟨false, 8388609, (-21 : ℤ), hm, he, ?_⟩)
  norm_num [fmt, hessenbergDetExampleTable13IeeeSingleFormat,
    FloatingPointFormat.ieeeSingleFormat, FloatingPointFormat.normalizedValue,
    FloatingPointFormat.signValue, FloatingPointFormat.betaR, zpow_neg]

/-- The final left-to-right determinant product value is representable in
binary32. -/
theorem hessenbergDetExampleTable13IeeeSingle_detProduct_finiteSystem :
    hessenbergDetExampleTable13IeeeSingleFormat.finiteSystem
      (8388609 / 4194304 : ℝ) := by
  let fmt := hessenbergDetExampleTable13IeeeSingleFormat
  have hm : fmt.normalizedMantissa 8388609 := by
    norm_num [fmt, hessenbergDetExampleTable13IeeeSingleFormat,
      FloatingPointFormat.ieeeSingleFormat,
      FloatingPointFormat.normalizedMantissa,
      FloatingPointFormat.mantissaInRange,
      FloatingPointFormat.minNormalMantissa]
  have he : fmt.exponentInRange (2 : ℤ) := by
    norm_num [fmt, hessenbergDetExampleTable13IeeeSingleFormat,
      FloatingPointFormat.ieeeSingleFormat,
      FloatingPointFormat.exponentInRange]
  refine Or.inr (Or.inl ⟨false, 8388609, (2 : ℤ), hm, he, ?_⟩)
  norm_num [fmt, hessenbergDetExampleTable13IeeeSingleFormat,
    FloatingPointFormat.ieeeSingleFormat, FloatingPointFormat.normalizedValue,
    FloatingPointFormat.signValue, FloatingPointFormat.betaR, zpow_neg]

/-- First left-to-right determinant product from the closed Table 1.3 no-pivot
diagonal trace: `fl32(fl32(alpha)*10000001)=8388609/8388608`. -/
theorem hessenbergDetExampleTable13_round_storedAlpha_mul_firstStageDiag :
    hessenbergDetExampleTable13IeeeSingleFormat.finiteRoundToEvenOp BasicOp.mul
        hessenbergDetExampleTable13StoredAlpha (10000001 : ℝ) =
      8388609 / 8388608 := by
  let fmt := hessenbergDetExampleTable13IeeeSingleFormat
  let a : ℝ := fmt.normalizedValue false 8388608 (1 : ℤ)
  let b : ℝ := fmt.normalizedValue false 8388609 (1 : ℤ)
  let x : ℝ := BasicOp.exact BasicOp.mul
    hessenbergDetExampleTable13StoredAlpha (10000001 : ℝ)
  have hm : fmt.normalizedMantissa 8388608 := by
    norm_num [fmt, hessenbergDetExampleTable13IeeeSingleFormat,
      FloatingPointFormat.ieeeSingleFormat,
      FloatingPointFormat.normalizedMantissa,
      FloatingPointFormat.mantissaInRange,
      FloatingPointFormat.minNormalMantissa]
  have hmnext : fmt.normalizedMantissa (8388608 + 1) := by
    norm_num [fmt, hessenbergDetExampleTable13IeeeSingleFormat,
      FloatingPointFormat.ieeeSingleFormat,
      FloatingPointFormat.normalizedMantissa,
      FloatingPointFormat.mantissaInRange,
      FloatingPointFormat.minNormalMantissa]
  have hadj : fmt.realOrderAdjacentNormalized a b :=
    fmt.realOrderAdjacentNormalized_of_sameExponentAdjacentNormalized
      ⟨false, 8388608, (1 : ℤ), hm, hmnext, Or.inl ⟨rfl, rfl⟩⟩
  have ha_value : a = (1 : ℝ) := by
    norm_num [a, fmt, hessenbergDetExampleTable13IeeeSingleFormat,
      FloatingPointFormat.ieeeSingleFormat, FloatingPointFormat.normalizedValue,
      FloatingPointFormat.signValue, FloatingPointFormat.betaR, zpow_neg]
    rfl
  have hb_value : b = (8388609 : ℝ) / 8388608 := by
    norm_num [b, fmt, hessenbergDetExampleTable13IeeeSingleFormat,
      FloatingPointFormat.ieeeSingleFormat, FloatingPointFormat.normalizedValue,
      FloatingPointFormat.signValue, FloatingPointFormat.betaR, zpow_neg]
  have hx_value : x = (140737504073749 : ℝ) / 140737488355328 := by
    norm_num [x, BasicOp.exact, hessenbergDetExampleTable13StoredAlpha_eq]
  have hxrange : fmt.finiteNormalRange x := by
    rw [FloatingPointFormat.finiteNormalRange]
    rw [hx_value, abs_of_pos (by norm_num)]
    constructor
    · norm_num [fmt, hessenbergDetExampleTable13IeeeSingleFormat,
        FloatingPointFormat.ieeeSingleFormat,
        FloatingPointFormat.minNormalMagnitude, FloatingPointFormat.betaR,
        zpow_neg]
    · calc
        (140737504073749 : ℝ) / 140737488355328 ≤ 2 := by
          norm_num
        _ ≤ fmt.maxFiniteMagnitude := by
          norm_num [fmt, hessenbergDetExampleTable13IeeeSingleFormat,
            FloatingPointFormat.ieeeSingleFormat,
            FloatingPointFormat.maxFiniteMagnitude, FloatingPointFormat.betaR,
            zpow_neg]
          change (2 : ℝ) ≤ 340282346638528859811704183484516925440
          norm_num
  have hstrict : a < x ∧ x < b := by
    rw [ha_value, hb_value, hx_value]
    norm_num
  have hpolicy :
      fmt.sourceRoundToEvenEvidence x (fmt.finiteRoundToEven x) :=
    fmt.finiteRoundToEven_sourceRoundToEvenEvidence_of_finiteNormalRange hxrange
  have hrightCloser : |x - b| < |x - a| := by
    rw [ha_value, hb_value, hx_value]
    norm_num
  have hround : fmt.finiteRoundToEven x = b :=
    fmt.sourceRoundToEvenEvidence_eq_right_of_realOrderAdjacent_strict_between_right_closer
      hpolicy hadj hstrict hrightCloser
  change fmt.finiteRoundToEven x = (8388609 : ℝ) / 8388608
  simpa [x, fmt, hb_value] using hround

/-- The second left-to-right determinant product is exact after the first
rounded product prefix. -/
theorem hessenbergDetExampleTable13_round_detProduct01_mul_secondStageDiag :
    hessenbergDetExampleTable13IeeeSingleFormat.finiteRoundToEvenOp BasicOp.mul
        (8388609 / 8388608 : ℝ) (1 / 4194304 : ℝ) =
      8388609 / (2 : ℝ) ^ 45 := by
  let fmt := hessenbergDetExampleTable13IeeeSingleFormat
  have hfin :
      fmt.finiteSystem
        (BasicOp.exact BasicOp.mul (8388609 / 8388608 : ℝ)
          (1 / 4194304 : ℝ)) := by
    convert hessenbergDetExampleTable13IeeeSingle_detProduct012_finiteSystem using 1
    norm_num [BasicOp.exact]
  have hround :=
    (fmt.finiteRoundToEvenOp_eq_exact_of_finiteSystem
      (op := BasicOp.mul) (x := (8388609 / 8388608 : ℝ))
      (y := (1 / 4194304 : ℝ)) hfin)
  rw [hround]
  norm_num [BasicOp.exact]

/-- The final left-to-right determinant product is exact after the second
product prefix. -/
theorem hessenbergDetExampleTable13_round_detProduct012_mul_finalDiag :
    hessenbergDetExampleTable13IeeeSingleFormat.finiteRoundToEvenOp BasicOp.mul
        (8388609 / (2 : ℝ) ^ 45) (8388608 : ℝ) =
      8388609 / 4194304 := by
  let fmt := hessenbergDetExampleTable13IeeeSingleFormat
  have hfin :
      fmt.finiteSystem
        (BasicOp.exact BasicOp.mul (8388609 / (2 : ℝ) ^ 45) (8388608 : ℝ)) := by
    convert hessenbergDetExampleTable13IeeeSingle_detProduct_finiteSystem using 1
    norm_num [BasicOp.exact]
  have hround :=
    (fmt.finiteRoundToEvenOp_eq_exact_of_finiteSystem
      (op := BasicOp.mul) (x := (8388609 / (2 : ℝ) ^ 45))
      (y := (8388608 : ℝ)) hfin)
  rw [hround]
  norm_num [BasicOp.exact]

/-- The left-to-right product of the closed Table 1.3 computed diagonal trace
gives the concrete primitive computed determinant value. -/
theorem hessenbergDetExampleTable13_detProduct_leftToRight_rounds_to :
    hessenbergDetExampleTable13IeeeSingleFormat.finiteRoundToEvenOp BasicOp.mul
        (hessenbergDetExampleTable13IeeeSingleFormat.finiteRoundToEvenOp BasicOp.mul
          (hessenbergDetExampleTable13IeeeSingleFormat.finiteRoundToEvenOp BasicOp.mul
            hessenbergDetExampleTable13StoredAlpha (10000001 : ℝ))
          (1 / 4194304 : ℝ))
        (8388608 : ℝ) =
      8388609 / 4194304 := by
  rw [hessenbergDetExampleTable13_round_storedAlpha_mul_firstStageDiag]
  rw [hessenbergDetExampleTable13_round_detProduct01_mul_secondStageDiag]
  exact hessenbergDetExampleTable13_round_detProduct012_mul_finalDiag

/-- Exact relative determinant error of the primitive left-to-right Table 1.3
determinant product against the source-value determinant. -/
theorem hessenbergDetExampleTable13_detProduct_relError_eq :
    relError (8388609 / 4194304 : ℝ)
        (Matrix.det
          (hessenbergDetExampleMatrix (1 / 10000000 : ℝ) :
            Matrix (Fin 4) (Fin 4) ℝ)) =
      12589 / 655360065536 := by
  rw [hessenbergDetExampleMatrix_alpha_ten_pow_det_eq]
  norm_num [relError]

/-- Binary32 storage of the Table 1.3 right-hand side keeps the exactly
representable `0`, `1`, and `2` entries fixed while exposing the rounded
`alpha - 3` source entry. -/
theorem hessenbergDetExampleTable13_storedRhs_rows :
    hessenbergDetExampleTable13StoredRhs 0 =
        hessenbergDetExampleTable13IeeeSingleFormat.finiteRoundToEven
          (hessenbergDetExampleTable13SourceAlpha - 3) ∧
      hessenbergDetExampleTable13StoredRhs 1 = 0 ∧
      hessenbergDetExampleTable13StoredRhs 2 = 1 ∧
      hessenbergDetExampleTable13StoredRhs 3 = 2 := by
  constructor
  · rfl
  constructor
  · simp [hessenbergDetExampleTable13StoredRhs, hessenbergDetExampleRhs]
  constructor
  · simp [hessenbergDetExampleTable13StoredRhs, hessenbergDetExampleRhs]
  · simp [hessenbergDetExampleTable13StoredRhs, hessenbergDetExampleRhs]

/-- The stored first right-hand-side entry `fl32(alpha-3)` rounds to `-3` in
the Table 1.3 binary32 model. -/
theorem hessenbergDetExampleTable13_round_sourceAlpha_sub_three :
    hessenbergDetExampleTable13IeeeSingleFormat.finiteRoundToEven
        (hessenbergDetExampleTable13SourceAlpha - 3) =
      -3 := by
  let fmt := hessenbergDetExampleTable13IeeeSingleFormat
  let a : ℝ := fmt.normalizedValue true 12582912 (2 : ℤ)
  let b : ℝ := fmt.normalizedValue true 12582911 (2 : ℤ)
  let x : ℝ := hessenbergDetExampleTable13SourceAlpha - 3
  have hm : fmt.normalizedMantissa 12582911 := by
    norm_num [fmt, hessenbergDetExampleTable13IeeeSingleFormat,
      FloatingPointFormat.ieeeSingleFormat,
      FloatingPointFormat.normalizedMantissa,
      FloatingPointFormat.mantissaInRange,
      FloatingPointFormat.minNormalMantissa]
  have hmnext : fmt.normalizedMantissa (12582911 + 1) := by
    norm_num [fmt, hessenbergDetExampleTable13IeeeSingleFormat,
      FloatingPointFormat.ieeeSingleFormat,
      FloatingPointFormat.normalizedMantissa,
      FloatingPointFormat.mantissaInRange,
      FloatingPointFormat.minNormalMantissa]
  have hadj : fmt.realOrderAdjacentNormalized a b :=
    fmt.realOrderAdjacentNormalized_of_sameExponentAdjacentNormalized
      ⟨true, 12582911, (2 : ℤ), hm, hmnext, Or.inr ⟨rfl, rfl⟩⟩
  have ha_value : a = (-3 : ℝ) := by
    norm_num [a, fmt, hessenbergDetExampleTable13IeeeSingleFormat,
      FloatingPointFormat.ieeeSingleFormat, FloatingPointFormat.normalizedValue,
      FloatingPointFormat.signValue, FloatingPointFormat.betaR, zpow_neg]
  have hb_value : b = -(12582911 : ℝ) / 4194304 := by
    norm_num [b, fmt, hessenbergDetExampleTable13IeeeSingleFormat,
      FloatingPointFormat.ieeeSingleFormat, FloatingPointFormat.normalizedValue,
      FloatingPointFormat.signValue, FloatingPointFormat.betaR, zpow_neg]
  have hx_value : x = -(29999999 : ℝ) / 10000000 := by
    norm_num [x, hessenbergDetExampleTable13SourceAlpha]
  have hxrange : fmt.finiteNormalRange x := by
    rw [FloatingPointFormat.finiteNormalRange]
    rw [hx_value, abs_of_neg (by norm_num)]
    constructor
    · norm_num [fmt, hessenbergDetExampleTable13IeeeSingleFormat,
        FloatingPointFormat.ieeeSingleFormat,
        FloatingPointFormat.minNormalMagnitude, FloatingPointFormat.betaR,
        zpow_neg]
    · calc
        -(-(29999999 : ℝ) / 10000000) ≤ 3 := by
          norm_num
        _ ≤ fmt.maxFiniteMagnitude := by
          norm_num [fmt, hessenbergDetExampleTable13IeeeSingleFormat,
            FloatingPointFormat.ieeeSingleFormat,
            FloatingPointFormat.maxFiniteMagnitude, FloatingPointFormat.betaR,
            zpow_neg]
          change (3 : ℝ) ≤ 340282346638528859811704183484516925440
          norm_num
  have hstrict : a < x ∧ x < b := by
    rw [ha_value, hb_value, hx_value]
    norm_num
  have hpolicy :
      fmt.sourceRoundToEvenEvidence x (fmt.finiteRoundToEven x) :=
    fmt.finiteRoundToEven_sourceRoundToEvenEvidence_of_finiteNormalRange hxrange
  have hleftCloser : |x - a| < |x - b| := by
    rw [ha_value, hb_value, hx_value]
    norm_num
  have hround : fmt.finiteRoundToEven x = a :=
    fmt.sourceRoundToEvenEvidence_eq_left_of_realOrderAdjacent_strict_between_left_closer
      hpolicy hadj hstrict hleftCloser
  change fmt.finiteRoundToEven x = (-3 : ℝ)
  simpa [x, fmt, ha_value] using hround

/-- The first stored right-hand-side entry is the concrete binary32 value `-3`. -/
theorem hessenbergDetExampleTable13StoredRhs0_eq_neg_three :
    hessenbergDetExampleTable13StoredRhs 0 = -3 := by
  have hrows := hessenbergDetExampleTable13_storedRhs_rows
  rw [hrows.1]
  exact hessenbergDetExampleTable13_round_sourceAlpha_sub_three

/-- The first RHS product `fl32(10^7*(-3))` is exact. -/
theorem hessenbergDetExampleTable13_round_ten_pow_seven_mul_neg_three :
    hessenbergDetExampleTable13IeeeSingleFormat.finiteRoundToEvenOp BasicOp.mul
        ((10 : ℝ) ^ 7) (-3) =
      -30000000 := by
  let fmt := hessenbergDetExampleTable13IeeeSingleFormat
  have hfin :
      fmt.finiteSystem
        (BasicOp.exact BasicOp.mul ((10 : ℝ) ^ 7) (-3 : ℝ)) := by
    have hm : fmt.normalizedMantissa 15000000 := by
      norm_num [fmt, hessenbergDetExampleTable13IeeeSingleFormat,
        FloatingPointFormat.ieeeSingleFormat,
        FloatingPointFormat.normalizedMantissa,
        FloatingPointFormat.mantissaInRange,
        FloatingPointFormat.minNormalMantissa]
    have he : fmt.exponentInRange (25 : ℤ) := by
      norm_num [fmt, hessenbergDetExampleTable13IeeeSingleFormat,
        FloatingPointFormat.ieeeSingleFormat,
        FloatingPointFormat.exponentInRange]
    refine Or.inr (Or.inl ⟨true, 15000000, (25 : ℤ), hm, he, ?_⟩)
    norm_num [BasicOp.exact, fmt, hessenbergDetExampleTable13IeeeSingleFormat,
      FloatingPointFormat.ieeeSingleFormat, FloatingPointFormat.normalizedValue,
      FloatingPointFormat.signValue, FloatingPointFormat.betaR, zpow_neg]
  have hround :=
    (fmt.finiteRoundToEvenOp_eq_exact_of_finiteSystem
      (op := BasicOp.mul) (x := ((10 : ℝ) ^ 7)) (y := (-3 : ℝ)) hfin)
  rw [hround]
  norm_num [BasicOp.exact]

/-- The first RHS subtraction `fl32(0 - (-30000000))` is exact. -/
theorem hessenbergDetExampleTable13_round_zero_sub_neg_thirty_million :
    hessenbergDetExampleTable13IeeeSingleFormat.finiteRoundToEvenOp BasicOp.sub
        (0 : ℝ) (-30000000 : ℝ) =
      30000000 := by
  let fmt := hessenbergDetExampleTable13IeeeSingleFormat
  have hfin :
      fmt.finiteSystem
        (BasicOp.exact BasicOp.sub (0 : ℝ) (-30000000 : ℝ)) := by
    have hm : fmt.normalizedMantissa 15000000 := by
      norm_num [fmt, hessenbergDetExampleTable13IeeeSingleFormat,
        FloatingPointFormat.ieeeSingleFormat,
        FloatingPointFormat.normalizedMantissa,
        FloatingPointFormat.mantissaInRange,
        FloatingPointFormat.minNormalMantissa]
    have he : fmt.exponentInRange (25 : ℤ) := by
      norm_num [fmt, hessenbergDetExampleTable13IeeeSingleFormat,
        FloatingPointFormat.ieeeSingleFormat,
        FloatingPointFormat.exponentInRange]
    refine Or.inr (Or.inl ⟨false, 15000000, (25 : ℤ), hm, he, ?_⟩)
    norm_num [BasicOp.exact, fmt, hessenbergDetExampleTable13IeeeSingleFormat,
      FloatingPointFormat.ieeeSingleFormat, FloatingPointFormat.normalizedValue,
      FloatingPointFormat.signValue, FloatingPointFormat.betaR, zpow_neg]
    rfl
  have hround :=
    (fmt.finiteRoundToEvenOp_eq_exact_of_finiteSystem
      (op := BasicOp.sub) (x := (0 : ℝ)) (y := (-30000000 : ℝ)) hfin)
  rw [hround]
  norm_num [BasicOp.exact]
  rfl

/-- Fully nested primitive binary32 trace for the first RHS elimination update
from the stored Table 1.3 system. -/
theorem hessenbergDetExampleTable13StoredRhs_firstStage_rhs1_rounds_to :
    hessenbergDetExampleTable13IeeeSingleFormat.finiteRoundToEvenOp BasicOp.sub
        (hessenbergDetExampleTable13StoredRhs 1)
        (hessenbergDetExampleTable13IeeeSingleFormat.finiteRoundToEvenOp BasicOp.mul
          (hessenbergDetExampleTable13IeeeSingleFormat.finiteRoundToEvenOp BasicOp.div
            (hessenbergDetExampleTable13StoredMatrix 1 0)
            (hessenbergDetExampleTable13StoredMatrix 0 0))
          (hessenbergDetExampleTable13StoredRhs 0)) =
      30000000 := by
  rw [hessenbergDetExampleTable13StoredMatrix_firstMultiplier_rounds_to_ten_pow_seven]
  rw [hessenbergDetExampleTable13StoredRhs0_eq_neg_three]
  have hrows := hessenbergDetExampleTable13_storedRhs_rows
  rw [hrows.2.1]
  simp [hessenbergDetExampleTable13_round_ten_pow_seven_mul_neg_three,
    hessenbergDetExampleTable13_round_zero_sub_neg_thirty_million]

/-- The second RHS product value `6291455/2097152` is representable in
binary32. -/
theorem hessenbergDetExampleTable13IeeeSingle_secondRhsProduct_finiteSystem :
    hessenbergDetExampleTable13IeeeSingleFormat.finiteSystem
      (6291455 / 2097152 : ℝ) := by
  let fmt := hessenbergDetExampleTable13IeeeSingleFormat
  have hm : fmt.normalizedMantissa 12582910 := by
    norm_num [fmt, hessenbergDetExampleTable13IeeeSingleFormat,
      FloatingPointFormat.ieeeSingleFormat,
      FloatingPointFormat.normalizedMantissa,
      FloatingPointFormat.mantissaInRange,
      FloatingPointFormat.minNormalMantissa]
  have he : fmt.exponentInRange (2 : ℤ) := by
    norm_num [fmt, hessenbergDetExampleTable13IeeeSingleFormat,
      FloatingPointFormat.ieeeSingleFormat,
      FloatingPointFormat.exponentInRange]
  refine Or.inr (Or.inl ⟨false, 12582910, (2 : ℤ), hm, he, ?_⟩)
  norm_num [fmt, hessenbergDetExampleTable13IeeeSingleFormat,
    FloatingPointFormat.ieeeSingleFormat, FloatingPointFormat.normalizedValue,
    FloatingPointFormat.signValue, FloatingPointFormat.betaR, zpow_neg]

/-- The second updated RHS value `-4194303/2097152` is representable in
binary32. -/
theorem hessenbergDetExampleTable13IeeeSingle_secondStageRhs_finiteSystem :
    hessenbergDetExampleTable13IeeeSingleFormat.finiteSystem
      (-4194303 / 2097152 : ℝ) := by
  let fmt := hessenbergDetExampleTable13IeeeSingleFormat
  have hm : fmt.normalizedMantissa 16777212 := by
    norm_num [fmt, hessenbergDetExampleTable13IeeeSingleFormat,
      FloatingPointFormat.ieeeSingleFormat,
      FloatingPointFormat.normalizedMantissa,
      FloatingPointFormat.mantissaInRange,
      FloatingPointFormat.minNormalMantissa]
  have he : fmt.exponentInRange (1 : ℤ) := by
    norm_num [fmt, hessenbergDetExampleTable13IeeeSingleFormat,
      FloatingPointFormat.ieeeSingleFormat,
      FloatingPointFormat.exponentInRange]
  refine Or.inr (Or.inl ⟨true, 16777212, (1 : ℤ), hm, he, ?_⟩)
  norm_num [fmt, hessenbergDetExampleTable13IeeeSingleFormat,
    FloatingPointFormat.ieeeSingleFormat, FloatingPointFormat.normalizedValue,
    FloatingPointFormat.signValue, FloatingPointFormat.betaR, zpow_neg]

/-- The final RHS product value `-8388606` is representable in binary32. -/
theorem hessenbergDetExampleTable13IeeeSingle_thirdRhsProduct_finiteSystem :
    hessenbergDetExampleTable13IeeeSingleFormat.finiteSystem
      (-8388606 : ℝ) := by
  let fmt := hessenbergDetExampleTable13IeeeSingleFormat
  have hm : fmt.normalizedMantissa 16777212 := by
    norm_num [fmt, hessenbergDetExampleTable13IeeeSingleFormat,
      FloatingPointFormat.ieeeSingleFormat,
      FloatingPointFormat.normalizedMantissa,
      FloatingPointFormat.mantissaInRange,
      FloatingPointFormat.minNormalMantissa]
  have he : fmt.exponentInRange (23 : ℤ) := by
    norm_num [fmt, hessenbergDetExampleTable13IeeeSingleFormat,
      FloatingPointFormat.ieeeSingleFormat,
      FloatingPointFormat.exponentInRange]
  refine Or.inr (Or.inl ⟨true, 16777212, (23 : ℤ), hm, he, ?_⟩)
  norm_num [fmt, hessenbergDetExampleTable13IeeeSingleFormat,
    FloatingPointFormat.ieeeSingleFormat, FloatingPointFormat.normalizedValue,
    FloatingPointFormat.signValue, FloatingPointFormat.betaR, zpow_neg]

/-- The second RHS product in the stored Table 1.3 trace:
`fl32((14073747/2^47)*30000000)` rounds to `6291455/2097152`. -/
theorem hessenbergDetExampleTable13_round_secondMultiplier_mul_firstStageRhs :
    hessenbergDetExampleTable13IeeeSingleFormat.finiteRoundToEvenOp BasicOp.mul
        (14073747 / (2 : ℝ) ^ 47) (30000000 : ℝ) =
      6291455 / 2097152 := by
  let fmt := hessenbergDetExampleTable13IeeeSingleFormat
  let a : ℝ := fmt.normalizedValue false 12582910 (2 : ℤ)
  let b : ℝ := fmt.normalizedValue false 12582911 (2 : ℤ)
  let x : ℝ := BasicOp.exact BasicOp.mul
    (14073747 / (2 : ℝ) ^ 47) (30000000 : ℝ)
  have hm : fmt.normalizedMantissa 12582910 := by
    norm_num [fmt, hessenbergDetExampleTable13IeeeSingleFormat,
      FloatingPointFormat.ieeeSingleFormat,
      FloatingPointFormat.normalizedMantissa,
      FloatingPointFormat.mantissaInRange,
      FloatingPointFormat.minNormalMantissa]
  have hmnext : fmt.normalizedMantissa (12582910 + 1) := by
    norm_num [fmt, hessenbergDetExampleTable13IeeeSingleFormat,
      FloatingPointFormat.ieeeSingleFormat,
      FloatingPointFormat.normalizedMantissa,
      FloatingPointFormat.mantissaInRange,
      FloatingPointFormat.minNormalMantissa]
  have hadj : fmt.realOrderAdjacentNormalized a b :=
    fmt.realOrderAdjacentNormalized_of_sameExponentAdjacentNormalized
      ⟨false, 12582910, (2 : ℤ), hm, hmnext, Or.inl ⟨rfl, rfl⟩⟩
  have ha_value : a = (6291455 : ℝ) / 2097152 := by
    norm_num [a, fmt, hessenbergDetExampleTable13IeeeSingleFormat,
      FloatingPointFormat.ieeeSingleFormat, FloatingPointFormat.normalizedValue,
      FloatingPointFormat.signValue, FloatingPointFormat.betaR, zpow_neg]
  have hb_value : b = (12582911 : ℝ) / 4194304 := by
    norm_num [b, fmt, hessenbergDetExampleTable13IeeeSingleFormat,
      FloatingPointFormat.ieeeSingleFormat, FloatingPointFormat.normalizedValue,
      FloatingPointFormat.signValue, FloatingPointFormat.betaR, zpow_neg]
  have hx_value : x = (3298534453125 : ℝ) / 1099511627776 := by
    norm_num [x, BasicOp.exact]
  have hxrange : fmt.finiteNormalRange x := by
    rw [FloatingPointFormat.finiteNormalRange]
    rw [hx_value, abs_of_pos (by norm_num)]
    constructor
    · norm_num [fmt, hessenbergDetExampleTable13IeeeSingleFormat,
        FloatingPointFormat.ieeeSingleFormat,
        FloatingPointFormat.minNormalMagnitude, FloatingPointFormat.betaR,
        zpow_neg]
    · calc
        (3298534453125 : ℝ) / 1099511627776 ≤ 3 := by
          norm_num
        _ ≤ fmt.maxFiniteMagnitude := by
          norm_num [fmt, hessenbergDetExampleTable13IeeeSingleFormat,
            FloatingPointFormat.ieeeSingleFormat,
            FloatingPointFormat.maxFiniteMagnitude, FloatingPointFormat.betaR,
            zpow_neg]
          change (3 : ℝ) ≤ 340282346638528859811704183484516925440
          norm_num
  have hstrict : a < x ∧ x < b := by
    rw [ha_value, hb_value, hx_value]
    norm_num
  have hpolicy :
      fmt.sourceRoundToEvenEvidence x (fmt.finiteRoundToEven x) :=
    fmt.finiteRoundToEven_sourceRoundToEvenEvidence_of_finiteNormalRange hxrange
  have hleftCloser : |x - a| < |x - b| := by
    rw [ha_value, hb_value, hx_value]
    norm_num
  have hround : fmt.finiteRoundToEven x = a :=
    fmt.sourceRoundToEvenEvidence_eq_left_of_realOrderAdjacent_strict_between_left_closer
      hpolicy hadj hstrict hleftCloser
  change fmt.finiteRoundToEven x = (6291455 : ℝ) / 2097152
  simpa [x, fmt, ha_value] using hround

/-- The second RHS subtraction `fl32(1 - 6291455/2097152)` is exact. -/
theorem hessenbergDetExampleTable13_round_one_sub_secondRhsProduct :
    hessenbergDetExampleTable13IeeeSingleFormat.finiteRoundToEvenOp BasicOp.sub
        (1 : ℝ) (6291455 / 2097152 : ℝ) =
      -4194303 / 2097152 := by
  let fmt := hessenbergDetExampleTable13IeeeSingleFormat
  have hfin :
      fmt.finiteSystem
        (BasicOp.exact BasicOp.sub (1 : ℝ) (6291455 / 2097152 : ℝ)) := by
    convert hessenbergDetExampleTable13IeeeSingle_secondStageRhs_finiteSystem using 1
    norm_num [BasicOp.exact]
  have hround :=
    (fmt.finiteRoundToEvenOp_eq_exact_of_finiteSystem
      (op := BasicOp.sub) (x := (1 : ℝ))
      (y := (6291455 / 2097152 : ℝ)) hfin)
  rw [hround]
  norm_num [BasicOp.exact]

/-- Fully nested primitive binary32 trace for the second RHS elimination update
from the stored Table 1.3 system. -/
theorem hessenbergDetExampleTable13StoredRhs_secondStage_rhs2_rounds_to :
    hessenbergDetExampleTable13IeeeSingleFormat.finiteRoundToEvenOp BasicOp.sub
        (hessenbergDetExampleTable13StoredRhs 2)
        (hessenbergDetExampleTable13IeeeSingleFormat.finiteRoundToEvenOp BasicOp.mul
          (hessenbergDetExampleTable13IeeeSingleFormat.finiteRoundToEvenOp BasicOp.div
            (hessenbergDetExampleTable13StoredMatrix 2 1)
            (hessenbergDetExampleTable13IeeeSingleFormat.finiteRoundToEvenOp BasicOp.sub
              (hessenbergDetExampleTable13StoredMatrix 1 1)
              (hessenbergDetExampleTable13IeeeSingleFormat.finiteRoundToEvenOp BasicOp.mul
                (hessenbergDetExampleTable13IeeeSingleFormat.finiteRoundToEvenOp BasicOp.div
                  (hessenbergDetExampleTable13StoredMatrix 1 0)
                  (hessenbergDetExampleTable13StoredMatrix 0 0))
                (hessenbergDetExampleTable13StoredMatrix 0 1))))
          (hessenbergDetExampleTable13IeeeSingleFormat.finiteRoundToEvenOp BasicOp.sub
            (hessenbergDetExampleTable13StoredRhs 1)
            (hessenbergDetExampleTable13IeeeSingleFormat.finiteRoundToEvenOp BasicOp.mul
              (hessenbergDetExampleTable13IeeeSingleFormat.finiteRoundToEvenOp BasicOp.div
                (hessenbergDetExampleTable13StoredMatrix 1 0)
                (hessenbergDetExampleTable13StoredMatrix 0 0))
              (hessenbergDetExampleTable13StoredRhs 0)))) =
      -4194303 / 2097152 := by
  rw [hessenbergDetExampleTable13StoredMatrix_secondMultiplier_rounds_to]
  rw [hessenbergDetExampleTable13StoredRhs_firstStage_rhs1_rounds_to]
  have hrows := hessenbergDetExampleTable13_storedRhs_rows
  rw [hrows.2.2.1]
  simp [hessenbergDetExampleTable13_round_secondMultiplier_mul_firstStageRhs,
    hessenbergDetExampleTable13_round_one_sub_secondRhsProduct]

/-- The final RHS product `fl32(4194304*(-4194303/2097152))` is exact. -/
theorem hessenbergDetExampleTable13_round_thirdMultiplier_mul_secondStageRhs :
    hessenbergDetExampleTable13IeeeSingleFormat.finiteRoundToEvenOp BasicOp.mul
        (4194304 : ℝ) (-4194303 / 2097152 : ℝ) =
      -8388606 := by
  let fmt := hessenbergDetExampleTable13IeeeSingleFormat
  have hfin :
      fmt.finiteSystem
        (BasicOp.exact BasicOp.mul (4194304 : ℝ)
          (-4194303 / 2097152 : ℝ)) := by
    convert hessenbergDetExampleTable13IeeeSingle_thirdRhsProduct_finiteSystem using 1
    norm_num [BasicOp.exact]
  have hround :=
    (fmt.finiteRoundToEvenOp_eq_exact_of_finiteSystem
      (op := BasicOp.mul) (x := (4194304 : ℝ))
      (y := (-4194303 / 2097152 : ℝ)) hfin)
  rw [hround]
  norm_num [BasicOp.exact]

/-- The final RHS subtraction `fl32(2 - (-8388606))` is exact. -/
theorem hessenbergDetExampleTable13_round_two_sub_thirdRhsProduct :
    hessenbergDetExampleTable13IeeeSingleFormat.finiteRoundToEvenOp BasicOp.sub
        (2 : ℝ) (-8388606 : ℝ) =
      8388608 := by
  let fmt := hessenbergDetExampleTable13IeeeSingleFormat
  have hfin :
      fmt.finiteSystem
        (BasicOp.exact BasicOp.sub (2 : ℝ) (-8388606 : ℝ)) := by
    convert hessenbergDetExampleTable13IeeeSingle_finalDiag_finiteSystem using 1
    norm_num [BasicOp.exact]
    rfl
  have hround :=
    (fmt.finiteRoundToEvenOp_eq_exact_of_finiteSystem
      (op := BasicOp.sub) (x := (2 : ℝ)) (y := (-8388606 : ℝ)) hfin)
  rw [hround]
  norm_num [BasicOp.exact]
  rfl

/-- Fully nested primitive binary32 trace for the final RHS elimination update
from the stored Table 1.3 system. -/
theorem hessenbergDetExampleTable13StoredRhs_finalStage_rhs3_rounds_to :
    let fmt := hessenbergDetExampleTable13IeeeSingleFormat
    let d1 := fmt.finiteRoundToEvenOp BasicOp.sub
      (hessenbergDetExampleTable13StoredMatrix 1 1)
      (fmt.finiteRoundToEvenOp BasicOp.mul
        (fmt.finiteRoundToEvenOp BasicOp.div
          (hessenbergDetExampleTable13StoredMatrix 1 0)
          (hessenbergDetExampleTable13StoredMatrix 0 0))
        (hessenbergDetExampleTable13StoredMatrix 0 1))
    let m2 := fmt.finiteRoundToEvenOp BasicOp.div
      (hessenbergDetExampleTable13StoredMatrix 2 1) d1
    let u22 := fmt.finiteRoundToEvenOp BasicOp.sub
      (hessenbergDetExampleTable13StoredMatrix 2 2)
      (fmt.finiteRoundToEvenOp BasicOp.mul m2
        (fmt.finiteRoundToEvenOp BasicOp.sub
          (hessenbergDetExampleTable13StoredMatrix 1 2)
          (fmt.finiteRoundToEvenOp BasicOp.mul
            (fmt.finiteRoundToEvenOp BasicOp.div
              (hessenbergDetExampleTable13StoredMatrix 1 0)
              (hessenbergDetExampleTable13StoredMatrix 0 0))
            (hessenbergDetExampleTable13StoredMatrix 0 2))))
    let m3 := fmt.finiteRoundToEvenOp BasicOp.div
      (hessenbergDetExampleTable13StoredMatrix 3 2) u22
    let rhs1 := fmt.finiteRoundToEvenOp BasicOp.sub
      (hessenbergDetExampleTable13StoredRhs 1)
      (fmt.finiteRoundToEvenOp BasicOp.mul
        (fmt.finiteRoundToEvenOp BasicOp.div
          (hessenbergDetExampleTable13StoredMatrix 1 0)
          (hessenbergDetExampleTable13StoredMatrix 0 0))
        (hessenbergDetExampleTable13StoredRhs 0))
    let rhs2 := fmt.finiteRoundToEvenOp BasicOp.sub
      (hessenbergDetExampleTable13StoredRhs 2)
      (fmt.finiteRoundToEvenOp BasicOp.mul m2 rhs1)
    fmt.finiteRoundToEvenOp BasicOp.sub
        (hessenbergDetExampleTable13StoredRhs 3)
        (fmt.finiteRoundToEvenOp BasicOp.mul m3 rhs2) =
      8388608 := by
  dsimp only
  rw [hessenbergDetExampleTable13StoredMatrix_thirdMultiplier_rounds_to]
  rw [hessenbergDetExampleTable13StoredRhs_secondStage_rhs2_rounds_to]
  have hrows := hessenbergDetExampleTable13_storedRhs_rows
  rw [hrows.2.2.2]
  simp [hessenbergDetExampleTable13_round_thirdMultiplier_mul_secondStageRhs,
    hessenbergDetExampleTable13_round_two_sub_thirdRhsProduct]

/-- The row-3 back-substitution division is exact:
`fl32(8388608/8388608)=1`. -/
theorem hessenbergDetExampleTable13_backSub_x3_rounds_to_one :
    hessenbergDetExampleTable13IeeeSingleFormat.finiteRoundToEvenOp BasicOp.div
        (8388608 : ℝ) (8388608 : ℝ) =
      1 := by
  let fmt := hessenbergDetExampleTable13IeeeSingleFormat
  have hfin :
      fmt.finiteSystem
        (BasicOp.exact BasicOp.div (8388608 : ℝ) (8388608 : ℝ)) := by
    convert hessenbergDetExampleTable13IeeeSingle_one_finiteSystem using 1
    norm_num [BasicOp.exact]
    rfl
  have hround :=
    (fmt.finiteRoundToEvenOp_eq_exact_of_finiteSystem
      (op := BasicOp.div) (x := (8388608 : ℝ)) (y := (8388608 : ℝ)) hfin)
  rw [hround]
  norm_num [BasicOp.exact]
  rfl

/-- The row-2 back-substitution product by the computed `x_3=1` is exact. -/
theorem hessenbergDetExampleTable13_backSub_row2_product_rounds_to :
    hessenbergDetExampleTable13IeeeSingleFormat.finiteRoundToEvenOp BasicOp.mul
        (-8388607 / 4194304 : ℝ) 1 =
      -8388607 / 4194304 := by
  let fmt := hessenbergDetExampleTable13IeeeSingleFormat
  have hfin :
      fmt.finiteSystem
        (BasicOp.exact BasicOp.mul (-8388607 / 4194304 : ℝ) (1 : ℝ)) := by
    convert hessenbergDetExampleTable13IeeeSingle_secondStageSuper_finiteSystem using 1
    norm_num [BasicOp.exact]
  have hround :=
    (fmt.finiteRoundToEvenOp_eq_exact_of_finiteSystem
      (op := BasicOp.mul) (x := (-8388607 / 4194304 : ℝ)) (y := (1 : ℝ)) hfin)
  rw [hround]
  norm_num [BasicOp.exact]

/-- The row-2 back-substitution subtraction recovers the tiny pivot
`1/4194304`. -/
theorem hessenbergDetExampleTable13_backSub_row2_sub_rounds_to :
    hessenbergDetExampleTable13IeeeSingleFormat.finiteRoundToEvenOp BasicOp.sub
        (-4194303 / 2097152 : ℝ) (-8388607 / 4194304 : ℝ) =
      1 / 4194304 := by
  let fmt := hessenbergDetExampleTable13IeeeSingleFormat
  have hfin :
      fmt.finiteSystem
        (BasicOp.exact BasicOp.sub (-4194303 / 2097152 : ℝ)
          (-8388607 / 4194304 : ℝ)) := by
    convert hessenbergDetExampleTable13IeeeSingle_secondStageDiag_finiteSystem using 1
    norm_num [BasicOp.exact]
  have hround :=
    (fmt.finiteRoundToEvenOp_eq_exact_of_finiteSystem
      (op := BasicOp.sub) (x := (-4194303 / 2097152 : ℝ))
      (y := (-8388607 / 4194304 : ℝ)) hfin)
  rw [hround]
  norm_num [BasicOp.exact]

/-- The row-2 back-substitution division gives `x_2=1`. -/
theorem hessenbergDetExampleTable13_backSub_x2_rounds_to_one :
    hessenbergDetExampleTable13IeeeSingleFormat.finiteRoundToEvenOp BasicOp.div
        (hessenbergDetExampleTable13IeeeSingleFormat.finiteRoundToEvenOp BasicOp.sub
          (-4194303 / 2097152 : ℝ)
          (hessenbergDetExampleTable13IeeeSingleFormat.finiteRoundToEvenOp BasicOp.mul
            (-8388607 / 4194304 : ℝ)
            (hessenbergDetExampleTable13IeeeSingleFormat.finiteRoundToEvenOp BasicOp.div
              (8388608 : ℝ) (8388608 : ℝ))))
        (1 / 4194304 : ℝ) =
      1 := by
  rw [hessenbergDetExampleTable13_backSub_x3_rounds_to_one]
  rw [hessenbergDetExampleTable13_backSub_row2_product_rounds_to]
  rw [hessenbergDetExampleTable13_backSub_row2_sub_rounds_to]
  let fmt := hessenbergDetExampleTable13IeeeSingleFormat
  have hfin :
      fmt.finiteSystem
        (BasicOp.exact BasicOp.div (1 / 4194304 : ℝ) (1 / 4194304 : ℝ)) := by
    convert hessenbergDetExampleTable13IeeeSingle_one_finiteSystem using 1
    norm_num [BasicOp.exact]
    rfl
  have hround :=
    (fmt.finiteRoundToEvenOp_eq_exact_of_finiteSystem
      (op := BasicOp.div) (x := (1 / 4194304 : ℝ)) (y := (1 / 4194304 : ℝ)) hfin)
  rw [hround]
  norm_num [BasicOp.exact]
  rfl

/-- The row-1 first back-substitution product `fl32(9999999*1)` is exact. -/
theorem hessenbergDetExampleTable13_backSub_row1_product_rounds_to :
    hessenbergDetExampleTable13IeeeSingleFormat.finiteRoundToEvenOp BasicOp.mul
        (9999999 : ℝ) 1 =
      9999999 := by
  let fmt := hessenbergDetExampleTable13IeeeSingleFormat
  have hfin :
      fmt.finiteSystem
        (BasicOp.exact BasicOp.mul (9999999 : ℝ) (1 : ℝ)) := by
    convert hessenbergDetExampleTable13IeeeSingle_firstStageSuper_finiteSystem using 1
    norm_num [BasicOp.exact]
  have hround :=
    (fmt.finiteRoundToEvenOp_eq_exact_of_finiteSystem
      (op := BasicOp.mul) (x := (9999999 : ℝ)) (y := (1 : ℝ)) hfin)
  rw [hround]
  norm_num [BasicOp.exact]

/-- The row-1 first back-substitution subtraction is a tie and nearest/even
rounds `30000000 - 9999999 = 20000001` to `20000000`. -/
theorem hessenbergDetExampleTable13_backSub_row1_firstSub_rounds_to :
    hessenbergDetExampleTable13IeeeSingleFormat.finiteRoundToEvenOp BasicOp.sub
        (30000000 : ℝ) (9999999 : ℝ) =
      20000000 := by
  let fmt := hessenbergDetExampleTable13IeeeSingleFormat
  let a : ℝ := fmt.normalizedValue false 10000000 (25 : ℤ)
  let b : ℝ := fmt.normalizedValue false 10000001 (25 : ℤ)
  let x : ℝ := BasicOp.exact BasicOp.sub (30000000 : ℝ) (9999999 : ℝ)
  have hm : fmt.normalizedMantissa 10000000 := by
    norm_num [fmt, hessenbergDetExampleTable13IeeeSingleFormat,
      FloatingPointFormat.ieeeSingleFormat,
      FloatingPointFormat.normalizedMantissa,
      FloatingPointFormat.mantissaInRange,
      FloatingPointFormat.minNormalMantissa]
  have hmnext : fmt.normalizedMantissa (10000000 + 1) := by
    norm_num [fmt, hessenbergDetExampleTable13IeeeSingleFormat,
      FloatingPointFormat.ieeeSingleFormat,
      FloatingPointFormat.normalizedMantissa,
      FloatingPointFormat.mantissaInRange,
      FloatingPointFormat.minNormalMantissa]
  have hadj : fmt.realOrderAdjacentNormalized a b :=
    fmt.realOrderAdjacentNormalized_of_sameExponentAdjacentNormalized
      ⟨false, 10000000, (25 : ℤ), hm, hmnext, Or.inl ⟨rfl, rfl⟩⟩
  have ha_value : a = (20000000 : ℝ) := by
    norm_num [a, fmt, hessenbergDetExampleTable13IeeeSingleFormat,
      FloatingPointFormat.ieeeSingleFormat, FloatingPointFormat.normalizedValue,
      FloatingPointFormat.signValue, FloatingPointFormat.betaR, zpow_neg]
  have hb_value : b = (20000002 : ℝ) := by
    norm_num [b, fmt, hessenbergDetExampleTable13IeeeSingleFormat,
      FloatingPointFormat.ieeeSingleFormat, FloatingPointFormat.normalizedValue,
      FloatingPointFormat.signValue, FloatingPointFormat.betaR, zpow_neg]
  have hx_value : x = (20000001 : ℝ) := by
    norm_num [x, BasicOp.exact]
    rfl
  have hxrange : fmt.finiteNormalRange x := by
    rw [FloatingPointFormat.finiteNormalRange]
    rw [hx_value, abs_of_pos (by norm_num)]
    constructor
    · norm_num [fmt, hessenbergDetExampleTable13IeeeSingleFormat,
        FloatingPointFormat.ieeeSingleFormat,
        FloatingPointFormat.minNormalMagnitude, FloatingPointFormat.betaR,
        zpow_neg]
    · calc
        (20000001 : ℝ) ≤ 30000000 := by norm_num
        _ ≤ fmt.maxFiniteMagnitude := by
          norm_num [fmt, hessenbergDetExampleTable13IeeeSingleFormat,
            FloatingPointFormat.ieeeSingleFormat,
            FloatingPointFormat.maxFiniteMagnitude, FloatingPointFormat.betaR,
            zpow_neg]
          change (30000000 : ℝ) ≤ 340282346638528859811704183484516925440
          norm_num
  have hstrict : a < x ∧ x < b := by
    rw [ha_value, hb_value, hx_value]
    norm_num
  have hpolicy :
      fmt.sourceRoundToEvenEvidence x (fmt.finiteRoundToEven x) :=
    fmt.finiteRoundToEven_sourceRoundToEvenEvidence_of_finiteNormalRange hxrange
  have hleft : a = fmt.normalizedValue false 10000000 (25 : ℤ) := rfl
  have htie : |x - a| = |x - b| := by
    rw [ha_value, hb_value, hx_value]
    norm_num
  have heven : FloatingPointFormat.evenMantissa 10000000 := by
    norm_num [FloatingPointFormat.evenMantissa]
  have hround : fmt.finiteRoundToEven x = a :=
    fmt.sourceRoundToEvenEvidence_eq_left_of_realOrderAdjacent_strict_between_tie_even
      hpolicy hadj hstrict hm hleft htie heven
  change fmt.finiteRoundToEven x = (20000000 : ℝ)
  simpa [x, fmt, ha_value] using hround

/-- The row-1 second back-substitution subtraction is exact after the
tie-to-even first subtraction. -/
theorem hessenbergDetExampleTable13_backSub_row1_secondSub_rounds_to :
    hessenbergDetExampleTable13IeeeSingleFormat.finiteRoundToEvenOp BasicOp.sub
        (20000000 : ℝ) (9999999 : ℝ) =
      10000001 := by
  let fmt := hessenbergDetExampleTable13IeeeSingleFormat
  have hfin :
      fmt.finiteSystem
        (BasicOp.exact BasicOp.sub (20000000 : ℝ) (9999999 : ℝ)) := by
    convert hessenbergDetExampleTable13IeeeSingle_firstStageDiag_finiteSystem using 1
    norm_num [BasicOp.exact]
    rfl
  have hround :=
    (fmt.finiteRoundToEvenOp_eq_exact_of_finiteSystem
      (op := BasicOp.sub) (x := (20000000 : ℝ)) (y := (9999999 : ℝ)) hfin)
  rw [hround]
  norm_num [BasicOp.exact]
  rfl

/-- The row-1 back-substitution division gives `x_1=1`. -/
theorem hessenbergDetExampleTable13_backSub_x1_rounds_to_one :
    let fmt := hessenbergDetExampleTable13IeeeSingleFormat
    let x3 := fmt.finiteRoundToEvenOp BasicOp.div (8388608 : ℝ) (8388608 : ℝ)
    let x2 := fmt.finiteRoundToEvenOp BasicOp.div
      (fmt.finiteRoundToEvenOp BasicOp.sub (-4194303 / 2097152 : ℝ)
        (fmt.finiteRoundToEvenOp BasicOp.mul (-8388607 / 4194304 : ℝ) x3))
      (1 / 4194304 : ℝ)
    let s1 := fmt.finiteRoundToEvenOp BasicOp.sub (30000000 : ℝ)
      (fmt.finiteRoundToEvenOp BasicOp.mul (9999999 : ℝ) x2)
    let s2 := fmt.finiteRoundToEvenOp BasicOp.sub s1
      (fmt.finiteRoundToEvenOp BasicOp.mul (9999999 : ℝ) x3)
    fmt.finiteRoundToEvenOp BasicOp.div s2 (10000001 : ℝ) =
      1 := by
  dsimp only
  rw [hessenbergDetExampleTable13_backSub_x2_rounds_to_one]
  rw [hessenbergDetExampleTable13_backSub_x3_rounds_to_one]
  rw [hessenbergDetExampleTable13_backSub_row1_product_rounds_to]
  rw [hessenbergDetExampleTable13_backSub_row1_firstSub_rounds_to]
  rw [hessenbergDetExampleTable13_backSub_row1_secondSub_rounds_to]
  let fmt := hessenbergDetExampleTable13IeeeSingleFormat
  have hfin :
      fmt.finiteSystem
        (BasicOp.exact BasicOp.div (10000001 : ℝ) (10000001 : ℝ)) := by
    convert hessenbergDetExampleTable13IeeeSingle_one_finiteSystem using 1
    norm_num [BasicOp.exact]
    rfl
  have hround :=
    (fmt.finiteRoundToEvenOp_eq_exact_of_finiteSystem
      (op := BasicOp.div) (x := (10000001 : ℝ)) (y := (10000001 : ℝ)) hfin)
  rw [hround]
  norm_num [BasicOp.exact]
  rfl

/-- The row-0 product `fl32((-1)*1)` used in back substitution is exact. -/
theorem hessenbergDetExampleTable13_backSub_row0_product_rounds_to :
    hessenbergDetExampleTable13IeeeSingleFormat.finiteRoundToEvenOp BasicOp.mul
        (-1 : ℝ) 1 =
      -1 := by
  let fmt := hessenbergDetExampleTable13IeeeSingleFormat
  have hfin :
      fmt.finiteSystem
        (BasicOp.exact BasicOp.mul (-1 : ℝ) (1 : ℝ)) := by
    have hneg :
        fmt.finiteSystem (-(1 : ℝ)) :=
      fmt.finiteSystem_neg hessenbergDetExampleTable13IeeeSingle_one_finiteSystem
    convert hneg using 1
    norm_num [BasicOp.exact]
  have hround :=
    (fmt.finiteRoundToEvenOp_eq_exact_of_finiteSystem
      (op := BasicOp.mul) (x := (-1 : ℝ)) (y := (1 : ℝ)) hfin)
  rw [hround]
  norm_num [BasicOp.exact]

/-- The first row-0 back-substitution subtraction gives `-2`. -/
theorem hessenbergDetExampleTable13_backSub_row0_firstSub_rounds_to :
    hessenbergDetExampleTable13IeeeSingleFormat.finiteRoundToEvenOp BasicOp.sub
        (-3 : ℝ) (-1 : ℝ) =
      -2 := by
  let fmt := hessenbergDetExampleTable13IeeeSingleFormat
  have hfin :
      fmt.finiteSystem
        (BasicOp.exact BasicOp.sub (-3 : ℝ) (-1 : ℝ)) := by
    have hneg :
        fmt.finiteSystem (-(2 : ℝ)) :=
      fmt.finiteSystem_neg hessenbergDetExampleTable13IeeeSingle_two_finiteSystem
    convert hneg using 1
    norm_num [BasicOp.exact]
  have hround :=
    (fmt.finiteRoundToEvenOp_eq_exact_of_finiteSystem
      (op := BasicOp.sub) (x := (-3 : ℝ)) (y := (-1 : ℝ)) hfin)
  rw [hround]
  norm_num [BasicOp.exact]

/-- The second row-0 back-substitution subtraction gives `-1`. -/
theorem hessenbergDetExampleTable13_backSub_row0_secondSub_rounds_to :
    hessenbergDetExampleTable13IeeeSingleFormat.finiteRoundToEvenOp BasicOp.sub
        (-2 : ℝ) (-1 : ℝ) =
      -1 := by
  let fmt := hessenbergDetExampleTable13IeeeSingleFormat
  have hfin :
      fmt.finiteSystem
        (BasicOp.exact BasicOp.sub (-2 : ℝ) (-1 : ℝ)) := by
    have hneg :
        fmt.finiteSystem (-(1 : ℝ)) :=
      fmt.finiteSystem_neg hessenbergDetExampleTable13IeeeSingle_one_finiteSystem
    convert hneg using 1
    norm_num [BasicOp.exact]
  have hround :=
    (fmt.finiteRoundToEvenOp_eq_exact_of_finiteSystem
      (op := BasicOp.sub) (x := (-2 : ℝ)) (y := (-1 : ℝ)) hfin)
  rw [hround]
  norm_num [BasicOp.exact]

/-- The third row-0 back-substitution subtraction gives zero. -/
theorem hessenbergDetExampleTable13_backSub_row0_thirdSub_rounds_to :
    hessenbergDetExampleTable13IeeeSingleFormat.finiteRoundToEvenOp BasicOp.sub
        (-1 : ℝ) (-1 : ℝ) =
      0 := by
  let fmt := hessenbergDetExampleTable13IeeeSingleFormat
  have hfin :
      fmt.finiteSystem
        (BasicOp.exact BasicOp.sub (-1 : ℝ) (-1 : ℝ)) := by
    convert fmt.finiteSystem_zero using 1
    norm_num [BasicOp.exact]
    rfl
  have hround :=
    (fmt.finiteRoundToEvenOp_eq_exact_of_finiteSystem
      (op := BasicOp.sub) (x := (-1 : ℝ)) (y := (-1 : ℝ)) hfin)
  rw [hround]
  norm_num [BasicOp.exact]
  rfl

/-- The final row-0 back-substitution division gives `x_0=0` under the explicit
binary32 trace. -/
theorem hessenbergDetExampleTable13_backSub_x0_rounds_to_zero :
    let fmt := hessenbergDetExampleTable13IeeeSingleFormat
    let x3 := fmt.finiteRoundToEvenOp BasicOp.div (8388608 : ℝ) (8388608 : ℝ)
    let x2 := fmt.finiteRoundToEvenOp BasicOp.div
      (fmt.finiteRoundToEvenOp BasicOp.sub (-4194303 / 2097152 : ℝ)
        (fmt.finiteRoundToEvenOp BasicOp.mul (-8388607 / 4194304 : ℝ) x3))
      (1 / 4194304 : ℝ)
    let s1 := fmt.finiteRoundToEvenOp BasicOp.sub (30000000 : ℝ)
      (fmt.finiteRoundToEvenOp BasicOp.mul (9999999 : ℝ) x2)
    let s2 := fmt.finiteRoundToEvenOp BasicOp.sub s1
      (fmt.finiteRoundToEvenOp BasicOp.mul (9999999 : ℝ) x3)
    let x1 := fmt.finiteRoundToEvenOp BasicOp.div s2 (10000001 : ℝ)
    let r1 := fmt.finiteRoundToEvenOp BasicOp.sub (-3 : ℝ)
      (fmt.finiteRoundToEvenOp BasicOp.mul (-1 : ℝ) x1)
    let r2 := fmt.finiteRoundToEvenOp BasicOp.sub r1
      (fmt.finiteRoundToEvenOp BasicOp.mul (-1 : ℝ) x2)
    let r3 := fmt.finiteRoundToEvenOp BasicOp.sub r2
      (fmt.finiteRoundToEvenOp BasicOp.mul (-1 : ℝ) x3)
    fmt.finiteRoundToEvenOp BasicOp.div r3 hessenbergDetExampleTable13StoredAlpha =
      0 := by
  dsimp only
  rw [hessenbergDetExampleTable13_backSub_x1_rounds_to_one]
  rw [hessenbergDetExampleTable13_backSub_x2_rounds_to_one]
  rw [hessenbergDetExampleTable13_backSub_x3_rounds_to_one]
  rw [hessenbergDetExampleTable13_backSub_row0_product_rounds_to]
  rw [hessenbergDetExampleTable13_backSub_row0_firstSub_rounds_to]
  rw [hessenbergDetExampleTable13_backSub_row0_secondSub_rounds_to]
  rw [hessenbergDetExampleTable13_backSub_row0_thirdSub_rounds_to]
  let fmt := hessenbergDetExampleTable13IeeeSingleFormat
  have hfin :
      fmt.finiteSystem
        (BasicOp.exact BasicOp.div (0 : ℝ) hessenbergDetExampleTable13StoredAlpha) := by
    convert fmt.finiteSystem_zero using 1
    norm_num [BasicOp.exact]
  have hround :=
    (fmt.finiteRoundToEvenOp_eq_exact_of_finiteSystem
      (op := BasicOp.div) (x := (0 : ℝ))
      (y := hessenbergDetExampleTable13StoredAlpha) hfin)
  rw [hround]
  norm_num [BasicOp.exact]

/-- The standard nearest/even binary32 back-substitution trace for the stored
Table 1.3 triangular system gives `[0,1,1,1]^T`. -/
theorem hessenbergDetExampleTable13_standardBackSubSolution_rows :
    let fmt := hessenbergDetExampleTable13IeeeSingleFormat
    let x3 := fmt.finiteRoundToEvenOp BasicOp.div (8388608 : ℝ) (8388608 : ℝ)
    let x2 := fmt.finiteRoundToEvenOp BasicOp.div
      (fmt.finiteRoundToEvenOp BasicOp.sub (-4194303 / 2097152 : ℝ)
        (fmt.finiteRoundToEvenOp BasicOp.mul (-8388607 / 4194304 : ℝ) x3))
      (1 / 4194304 : ℝ)
    let s1 := fmt.finiteRoundToEvenOp BasicOp.sub (30000000 : ℝ)
      (fmt.finiteRoundToEvenOp BasicOp.mul (9999999 : ℝ) x2)
    let s2 := fmt.finiteRoundToEvenOp BasicOp.sub s1
      (fmt.finiteRoundToEvenOp BasicOp.mul (9999999 : ℝ) x3)
    let x1 := fmt.finiteRoundToEvenOp BasicOp.div s2 (10000001 : ℝ)
    let r1 := fmt.finiteRoundToEvenOp BasicOp.sub (-3 : ℝ)
      (fmt.finiteRoundToEvenOp BasicOp.mul (-1 : ℝ) x1)
    let r2 := fmt.finiteRoundToEvenOp BasicOp.sub r1
      (fmt.finiteRoundToEvenOp BasicOp.mul (-1 : ℝ) x2)
    let r3 := fmt.finiteRoundToEvenOp BasicOp.sub r2
      (fmt.finiteRoundToEvenOp BasicOp.mul (-1 : ℝ) x3)
    let x0 := fmt.finiteRoundToEvenOp BasicOp.div r3 hessenbergDetExampleTable13StoredAlpha
    x0 = 0 ∧ x1 = 1 ∧ x2 = 1 ∧ x3 = 1 := by
  dsimp only
  rw [hessenbergDetExampleTable13_backSub_x0_rounds_to_zero]
  rw [hessenbergDetExampleTable13_backSub_x1_rounds_to_one]
  rw [hessenbergDetExampleTable13_backSub_x2_rounds_to_one]
  rw [hessenbergDetExampleTable13_backSub_x3_rounds_to_one]
  simp

/-- The displayed computed solution vector in Higham Table 1.3, encoded as
exact rationals.  This records the printed table entries; it is not yet a
primitive-operation reconstruction of the hidden single-precision GE trace. -/
noncomputable def hessenbergDetExampleTable13ComputedSolution :
    Fin 4 → ℝ
  | ⟨0, _⟩ => 23842 / (10 : ℝ) ^ 4
  | ⟨1, _⟩ => 1
  | ⟨2, _⟩ => 1
  | ⟨3, _⟩ => 1

/-- The displayed relative solution error in Higham Table 1.3. -/
noncomputable def hessenbergDetExampleTable13SolutionRelativeError : ℝ :=
  13842 / (10 : ℝ) ^ 4

/-- The five-significant-figure exact determinant display in Higham Table 1.3. -/
noncomputable def hessenbergDetExampleTable13ExactDetDisplay : ℝ :=
  2

/-- The five-significant-figure computed determinant display in Higham Table 1.3. -/
noncomputable def hessenbergDetExampleTable13ComputedDetDisplay : ℝ :=
  2

/-- The displayed determinant relative error in Higham Table 1.3.  The exact
and computed determinant entries are printed only to five significant figures,
so this is a table datum rather than the relative error of the rounded display
`2.0000` against the exact rational determinant. -/
noncomputable def hessenbergDetExampleTable13DetRelativeError : ℝ :=
  19209 / (10 : ℝ) ^ 12

/-- The standard nearest/even binary32 back-substitution trace cannot be the
printed Table 1.3 solution row, whose first component is `2.3842`. -/
theorem hessenbergDetExampleTable13_standardBackSub_first_component_ne_printed :
    (0 : ℝ) ≠ hessenbergDetExampleTable13ComputedSolution 0 := by
  norm_num [hessenbergDetExampleTable13ComputedSolution]

/-- The adjacent binary32 value immediately above `-3` that would be obtained
by rounding the first RHS entry toward zero rather than by nearest/even storage
of the exact source value `alpha - 3`. -/
noncomputable def hessenbergDetExampleTable13AltStoredRhs0 : ℝ :=
  -12582911 / 4194304

/-- The alternate first RHS value is a finite binary32 number. -/
theorem hessenbergDetExampleTable13AltStoredRhs0_finiteSystem :
    hessenbergDetExampleTable13IeeeSingleFormat.finiteSystem
      hessenbergDetExampleTable13AltStoredRhs0 := by
  let fmt := hessenbergDetExampleTable13IeeeSingleFormat
  have hm : fmt.normalizedMantissa 12582911 := by
    norm_num [fmt, hessenbergDetExampleTable13IeeeSingleFormat,
      FloatingPointFormat.ieeeSingleFormat,
      FloatingPointFormat.normalizedMantissa,
      FloatingPointFormat.mantissaInRange,
      FloatingPointFormat.minNormalMantissa]
  have he : fmt.exponentInRange (2 : ℤ) := by
    norm_num [fmt, hessenbergDetExampleTable13IeeeSingleFormat,
      FloatingPointFormat.ieeeSingleFormat,
      FloatingPointFormat.exponentInRange]
  refine Or.inr (Or.inl ⟨true, 12582911, (2 : ℤ), hm, he, ?_⟩)
  norm_num [hessenbergDetExampleTable13AltStoredRhs0, fmt,
    hessenbergDetExampleTable13IeeeSingleFormat,
    FloatingPointFormat.ieeeSingleFormat, FloatingPointFormat.normalizedValue,
    FloatingPointFormat.signValue, FloatingPointFormat.betaR, zpow_neg]

/-- The alternate first RHS value is strictly above `-3`, matching the
one-step-toward-zero binary32 neighbor. -/
theorem hessenbergDetExampleTable13AltStoredRhs0_gt_neg_three :
    (-3 : ℝ) < hessenbergDetExampleTable13AltStoredRhs0 := by
  norm_num [hessenbergDetExampleTable13AltStoredRhs0]

/-- The alternate first RHS value is exactly the normalized binary32 neighbor
with mantissa `12582911` and exponent `2`. -/
theorem hessenbergDetExampleTable13AltStoredRhs0_eq_normalizedValue :
    hessenbergDetExampleTable13AltStoredRhs0 =
      hessenbergDetExampleTable13IeeeSingleFormat.normalizedValue
        true 12582911 (2 : ℤ) := by
  norm_num [hessenbergDetExampleTable13AltStoredRhs0,
    hessenbergDetExampleTable13IeeeSingleFormat,
    FloatingPointFormat.ieeeSingleFormat, FloatingPointFormat.normalizedValue,
    FloatingPointFormat.signValue, FloatingPointFormat.betaR, zpow_neg]

/-- The alternate first RHS value is the immediate binary32 neighbor above
`-3`; this isolates the hidden one-step-toward-zero convention needed to obtain
the printed Table 1.3 first component by the standard back-substitution path. -/
theorem hessenbergDetExampleTable13_neg_three_altStoredRhs0_adjacent :
    hessenbergDetExampleTable13IeeeSingleFormat.realOrderAdjacentNormalized
      (-3 : ℝ) hessenbergDetExampleTable13AltStoredRhs0 := by
  let fmt := hessenbergDetExampleTable13IeeeSingleFormat
  have hm : fmt.normalizedMantissa 12582911 := by
    norm_num [fmt, hessenbergDetExampleTable13IeeeSingleFormat,
      FloatingPointFormat.ieeeSingleFormat,
      FloatingPointFormat.normalizedMantissa,
      FloatingPointFormat.mantissaInRange,
      FloatingPointFormat.minNormalMantissa]
  have hmnext : fmt.normalizedMantissa (12582911 + 1) := by
    norm_num [fmt, hessenbergDetExampleTable13IeeeSingleFormat,
      FloatingPointFormat.ieeeSingleFormat,
      FloatingPointFormat.normalizedMantissa,
      FloatingPointFormat.mantissaInRange,
      FloatingPointFormat.minNormalMantissa]
  have hadj : fmt.realOrderAdjacentNormalized
      (fmt.normalizedValue true 12582912 (2 : ℤ))
      (fmt.normalizedValue true 12582911 (2 : ℤ)) :=
    fmt.realOrderAdjacentNormalized_of_sameExponentAdjacentNormalized
      ⟨true, 12582911, (2 : ℤ), hm, hmnext, Or.inr ⟨rfl, rfl⟩⟩
  have hleft : fmt.normalizedValue true 12582912 (2 : ℤ) = (-3 : ℝ) := by
    norm_num [fmt, hessenbergDetExampleTable13IeeeSingleFormat,
      FloatingPointFormat.ieeeSingleFormat, FloatingPointFormat.normalizedValue,
      FloatingPointFormat.signValue, FloatingPointFormat.betaR, zpow_neg]
  have hright : fmt.normalizedValue true 12582911 (2 : ℤ) =
      hessenbergDetExampleTable13AltStoredRhs0 := by
    rw [hessenbergDetExampleTable13AltStoredRhs0_eq_normalizedValue]
  simpa [fmt, hleft, hright] using hadj

/-- The actual nearest/even stored first RHS entry is strictly below the
alternate adjacent value that reproduces the printed Table 1.3 first component. -/
theorem hessenbergDetExampleTable13StoredRhs0_lt_altStoredRhs0 :
    hessenbergDetExampleTable13StoredRhs 0 <
      hessenbergDetExampleTable13AltStoredRhs0 := by
  rw [hessenbergDetExampleTable13StoredRhs0_eq_neg_three]
  exact hessenbergDetExampleTable13AltStoredRhs0_gt_neg_three

/-- Consequently the alternate-RHS diagnostic is not the same as ordinary
nearest/even storage of the source right-hand side. -/
theorem hessenbergDetExampleTable13StoredRhs0_ne_altStoredRhs0 :
    hessenbergDetExampleTable13StoredRhs 0 ≠
      hessenbergDetExampleTable13AltStoredRhs0 :=
  ne_of_lt hessenbergDetExampleTable13StoredRhs0_lt_altStoredRhs0

/-- The intermediate alternate row-0 value `-4194303/4194304` is representable
in binary32. -/
theorem hessenbergDetExampleTable13IeeeSingle_altRow0SecondSub_finiteSystem :
    hessenbergDetExampleTable13IeeeSingleFormat.finiteSystem
      (-4194303 / 4194304 : ℝ) := by
  let fmt := hessenbergDetExampleTable13IeeeSingleFormat
  have hm : fmt.normalizedMantissa 16777212 := by
    norm_num [fmt, hessenbergDetExampleTable13IeeeSingleFormat,
      FloatingPointFormat.ieeeSingleFormat,
      FloatingPointFormat.normalizedMantissa,
      FloatingPointFormat.mantissaInRange,
      FloatingPointFormat.minNormalMantissa]
  have he : fmt.exponentInRange (0 : ℤ) := by
    norm_num [fmt, hessenbergDetExampleTable13IeeeSingleFormat,
      FloatingPointFormat.ieeeSingleFormat,
      FloatingPointFormat.exponentInRange]
  refine Or.inr (Or.inl ⟨true, 16777212, (0 : ℤ), hm, he, ?_⟩)
  norm_num [fmt, hessenbergDetExampleTable13IeeeSingleFormat,
    FloatingPointFormat.ieeeSingleFormat, FloatingPointFormat.normalizedValue,
    FloatingPointFormat.signValue, FloatingPointFormat.betaR, zpow_neg]

/-- With the alternate first RHS value, the first row-0 subtraction gives the
binary32 neighbor `-8388607/4194304` exactly. -/
theorem hessenbergDetExampleTable13_altRhsBackSub_row0_firstSub_rounds_to :
    hessenbergDetExampleTable13IeeeSingleFormat.finiteRoundToEvenOp BasicOp.sub
        hessenbergDetExampleTable13AltStoredRhs0 (-1 : ℝ) =
      -8388607 / 4194304 := by
  let fmt := hessenbergDetExampleTable13IeeeSingleFormat
  have hfin :
      fmt.finiteSystem
        (BasicOp.exact BasicOp.sub hessenbergDetExampleTable13AltStoredRhs0
          (-1 : ℝ)) := by
    convert hessenbergDetExampleTable13IeeeSingle_secondStageSuper_finiteSystem using 1
    norm_num [BasicOp.exact, hessenbergDetExampleTable13AltStoredRhs0]
  have hround :=
    (fmt.finiteRoundToEvenOp_eq_exact_of_finiteSystem
      (op := BasicOp.sub) (x := hessenbergDetExampleTable13AltStoredRhs0)
      (y := (-1 : ℝ)) hfin)
  rw [hround]
  norm_num [BasicOp.exact, hessenbergDetExampleTable13AltStoredRhs0]

/-- With the alternate first RHS value, the second row-0 subtraction gives
`-4194303/4194304` exactly. -/
theorem hessenbergDetExampleTable13_altRhsBackSub_row0_secondSub_rounds_to :
    hessenbergDetExampleTable13IeeeSingleFormat.finiteRoundToEvenOp BasicOp.sub
        (-8388607 / 4194304 : ℝ) (-1 : ℝ) =
      -4194303 / 4194304 := by
  let fmt := hessenbergDetExampleTable13IeeeSingleFormat
  have hfin :
      fmt.finiteSystem
        (BasicOp.exact BasicOp.sub (-8388607 / 4194304 : ℝ) (-1 : ℝ)) := by
    convert hessenbergDetExampleTable13IeeeSingle_altRow0SecondSub_finiteSystem using 1
    norm_num [BasicOp.exact]
  have hround :=
    (fmt.finiteRoundToEvenOp_eq_exact_of_finiteSystem
      (op := BasicOp.sub) (x := (-8388607 / 4194304 : ℝ))
      (y := (-1 : ℝ)) hfin)
  rw [hround]
  norm_num [BasicOp.exact]

/-- With the alternate first RHS value, the third row-0 subtraction leaves the
small binary32 value `1/4194304`. -/
theorem hessenbergDetExampleTable13_altRhsBackSub_row0_thirdSub_rounds_to :
    hessenbergDetExampleTable13IeeeSingleFormat.finiteRoundToEvenOp BasicOp.sub
        (-4194303 / 4194304 : ℝ) (-1 : ℝ) =
      1 / 4194304 := by
  let fmt := hessenbergDetExampleTable13IeeeSingleFormat
  have hfin :
      fmt.finiteSystem
        (BasicOp.exact BasicOp.sub (-4194303 / 4194304 : ℝ) (-1 : ℝ)) := by
    convert hessenbergDetExampleTable13IeeeSingle_secondStageDiag_finiteSystem using 1
    norm_num [BasicOp.exact]
  have hround :=
    (fmt.finiteRoundToEvenOp_eq_exact_of_finiteSystem
      (op := BasicOp.sub) (x := (-4194303 / 4194304 : ℝ))
      (y := (-1 : ℝ)) hfin)
  rw [hround]
  norm_num [BasicOp.exact]

/-- The alternate row-0 numerator divided by the stored first pivot rounds to
the binary32 value whose decimal display is `2.3842`. -/
theorem hessenbergDetExampleTable13_altRhsBackSub_row0_div_rounds_to :
    hessenbergDetExampleTable13IeeeSingleFormat.finiteRoundToEvenOp BasicOp.div
        (1 / 4194304 : ℝ) hessenbergDetExampleTable13StoredAlpha =
      78125 / 32768 := by
  let fmt := hessenbergDetExampleTable13IeeeSingleFormat
  let a : ℝ := fmt.normalizedValue false 9999999 (2 : ℤ)
  let b : ℝ := fmt.normalizedValue false 10000000 (2 : ℤ)
  let x : ℝ := BasicOp.exact BasicOp.div (1 / 4194304 : ℝ)
    hessenbergDetExampleTable13StoredAlpha
  have hm : fmt.normalizedMantissa 9999999 := by
    norm_num [fmt, hessenbergDetExampleTable13IeeeSingleFormat,
      FloatingPointFormat.ieeeSingleFormat,
      FloatingPointFormat.normalizedMantissa,
      FloatingPointFormat.mantissaInRange,
      FloatingPointFormat.minNormalMantissa]
  have hmnext : fmt.normalizedMantissa (9999999 + 1) := by
    norm_num [fmt, hessenbergDetExampleTable13IeeeSingleFormat,
      FloatingPointFormat.ieeeSingleFormat,
      FloatingPointFormat.normalizedMantissa,
      FloatingPointFormat.mantissaInRange,
      FloatingPointFormat.minNormalMantissa]
  have hadj : fmt.realOrderAdjacentNormalized a b :=
    fmt.realOrderAdjacentNormalized_of_sameExponentAdjacentNormalized
      ⟨false, 9999999, (2 : ℤ), hm, hmnext, Or.inl ⟨rfl, rfl⟩⟩
  have ha_value : a = (9999999 : ℝ) / 4194304 := by
    norm_num [a, fmt, hessenbergDetExampleTable13IeeeSingleFormat,
      FloatingPointFormat.ieeeSingleFormat, FloatingPointFormat.normalizedValue,
      FloatingPointFormat.signValue, FloatingPointFormat.betaR, zpow_neg]
  have hb_value : b = (78125 : ℝ) / 32768 := by
    norm_num [b, fmt, hessenbergDetExampleTable13IeeeSingleFormat,
      FloatingPointFormat.ieeeSingleFormat, FloatingPointFormat.normalizedValue,
      FloatingPointFormat.signValue, FloatingPointFormat.betaR, zpow_neg]
  have hx_value : x = (33554432 : ℝ) / 14073749 := by
    norm_num [x, BasicOp.exact, hessenbergDetExampleTable13StoredAlpha_eq]
  have hxrange : fmt.finiteNormalRange x := by
    rw [FloatingPointFormat.finiteNormalRange]
    rw [hx_value, abs_of_pos (by norm_num)]
    constructor
    · norm_num [fmt, hessenbergDetExampleTable13IeeeSingleFormat,
        FloatingPointFormat.ieeeSingleFormat, FloatingPointFormat.minNormalMagnitude,
        FloatingPointFormat.betaR, zpow_neg]
    · calc
        (33554432 : ℝ) / 14073749 ≤ 3 := by
          norm_num
        _ ≤ fmt.maxFiniteMagnitude := by
          norm_num [fmt, hessenbergDetExampleTable13IeeeSingleFormat,
            FloatingPointFormat.ieeeSingleFormat,
            FloatingPointFormat.maxFiniteMagnitude, FloatingPointFormat.betaR,
            zpow_neg]
          change (3 : ℝ) ≤ 340282346638528859811704183484516925440
          norm_num
  have hstrict : a < x ∧ x < b := by
    rw [ha_value, hb_value, hx_value]
    norm_num
  have hpolicy :
      fmt.sourceRoundToEvenEvidence x (fmt.finiteRoundToEven x) :=
    fmt.finiteRoundToEven_sourceRoundToEvenEvidence_of_finiteNormalRange hxrange
  have hrightCloser : |x - b| < |x - a| := by
    rw [ha_value, hb_value, hx_value]
    norm_num
  have hround : fmt.finiteRoundToEven x = b :=
    fmt.sourceRoundToEvenEvidence_eq_right_of_realOrderAdjacent_strict_between_right_closer
      hpolicy hadj hstrict hrightCloser
  change fmt.finiteRoundToEven x = (78125 : ℝ) / 32768
  simpa [x, fmt, hb_value] using hround

/-- If only the first stored RHS entry is replaced by the adjacent binary32
value above `-3`, the same standard back-substitution trace returns the
binary32 first component that prints as the Table 1.3 value. -/
theorem hessenbergDetExampleTable13_altRhsBackSub_x0_rounds_to_printed_float :
    let fmt := hessenbergDetExampleTable13IeeeSingleFormat
    let x3 := fmt.finiteRoundToEvenOp BasicOp.div (8388608 : ℝ) (8388608 : ℝ)
    let x2 := fmt.finiteRoundToEvenOp BasicOp.div
      (fmt.finiteRoundToEvenOp BasicOp.sub (-4194303 / 2097152 : ℝ)
        (fmt.finiteRoundToEvenOp BasicOp.mul (-8388607 / 4194304 : ℝ) x3))
      (1 / 4194304 : ℝ)
    let s1 := fmt.finiteRoundToEvenOp BasicOp.sub (30000000 : ℝ)
      (fmt.finiteRoundToEvenOp BasicOp.mul (9999999 : ℝ) x2)
    let s2 := fmt.finiteRoundToEvenOp BasicOp.sub s1
      (fmt.finiteRoundToEvenOp BasicOp.mul (9999999 : ℝ) x3)
    let x1 := fmt.finiteRoundToEvenOp BasicOp.div s2 (10000001 : ℝ)
    let r1 := fmt.finiteRoundToEvenOp BasicOp.sub
      hessenbergDetExampleTable13AltStoredRhs0
      (fmt.finiteRoundToEvenOp BasicOp.mul (-1 : ℝ) x1)
    let r2 := fmt.finiteRoundToEvenOp BasicOp.sub r1
      (fmt.finiteRoundToEvenOp BasicOp.mul (-1 : ℝ) x2)
    let r3 := fmt.finiteRoundToEvenOp BasicOp.sub r2
      (fmt.finiteRoundToEvenOp BasicOp.mul (-1 : ℝ) x3)
    fmt.finiteRoundToEvenOp BasicOp.div r3 hessenbergDetExampleTable13StoredAlpha =
      78125 / 32768 := by
  dsimp only
  rw [hessenbergDetExampleTable13_backSub_x1_rounds_to_one]
  rw [hessenbergDetExampleTable13_backSub_x2_rounds_to_one]
  rw [hessenbergDetExampleTable13_backSub_x3_rounds_to_one]
  rw [hessenbergDetExampleTable13_backSub_row0_product_rounds_to]
  rw [hessenbergDetExampleTable13_altRhsBackSub_row0_firstSub_rounds_to]
  rw [hessenbergDetExampleTable13_altRhsBackSub_row0_secondSub_rounds_to]
  rw [hessenbergDetExampleTable13_altRhsBackSub_row0_thirdSub_rounds_to]
  exact hessenbergDetExampleTable13_altRhsBackSub_row0_div_rounds_to

/-- The alternate-RHS back-substitution first component is within half a unit in
the fifth displayed decimal place of the printed Table 1.3 value `2.3842`. -/
theorem hessenbergDetExampleTable13_altRhsBackSub_first_component_matches_printed :
    let fmt := hessenbergDetExampleTable13IeeeSingleFormat
    let x3 := fmt.finiteRoundToEvenOp BasicOp.div (8388608 : ℝ) (8388608 : ℝ)
    let x2 := fmt.finiteRoundToEvenOp BasicOp.div
      (fmt.finiteRoundToEvenOp BasicOp.sub (-4194303 / 2097152 : ℝ)
        (fmt.finiteRoundToEvenOp BasicOp.mul (-8388607 / 4194304 : ℝ) x3))
      (1 / 4194304 : ℝ)
    let s1 := fmt.finiteRoundToEvenOp BasicOp.sub (30000000 : ℝ)
      (fmt.finiteRoundToEvenOp BasicOp.mul (9999999 : ℝ) x2)
    let s2 := fmt.finiteRoundToEvenOp BasicOp.sub s1
      (fmt.finiteRoundToEvenOp BasicOp.mul (9999999 : ℝ) x3)
    let x1 := fmt.finiteRoundToEvenOp BasicOp.div s2 (10000001 : ℝ)
    let r1 := fmt.finiteRoundToEvenOp BasicOp.sub
      hessenbergDetExampleTable13AltStoredRhs0
      (fmt.finiteRoundToEvenOp BasicOp.mul (-1 : ℝ) x1)
    let r2 := fmt.finiteRoundToEvenOp BasicOp.sub r1
      (fmt.finiteRoundToEvenOp BasicOp.mul (-1 : ℝ) x2)
    let r3 := fmt.finiteRoundToEvenOp BasicOp.sub r2
      (fmt.finiteRoundToEvenOp BasicOp.mul (-1 : ℝ) x3)
    |fmt.finiteRoundToEvenOp BasicOp.div r3 hessenbergDetExampleTable13StoredAlpha -
        hessenbergDetExampleTable13ComputedSolution 0| <
      1 / (2 * (10 : ℝ) ^ 4) := by
  dsimp only
  rw [hessenbergDetExampleTable13_altRhsBackSub_x0_rounds_to_printed_float]
  norm_num [hessenbergDetExampleTable13ComputedSolution]

/-- Exact rational transcription of the displayed computed solution vector in
Table 1.3. -/
theorem hessenbergDetExampleTable13_computedSolution_rows :
    hessenbergDetExampleTable13ComputedSolution 0 =
        23842 / (10 : ℝ) ^ 4 ∧
    hessenbergDetExampleTable13ComputedSolution 1 = 1 ∧
    hessenbergDetExampleTable13ComputedSolution 2 = 1 ∧
    hessenbergDetExampleTable13ComputedSolution 3 = 1 := by
  norm_num [hessenbergDetExampleTable13ComputedSolution]

/-- Exact rational transcription of the displayed exact solution vector in
Table 1.3. -/
theorem hessenbergDetExampleTable13_exactSolution_rows :
    hessenbergDetExampleOnes 0 = 1 ∧
    hessenbergDetExampleOnes 1 = 1 ∧
    hessenbergDetExampleOnes 2 = 1 ∧
    hessenbergDetExampleOnes 3 = 1 := by
  norm_num [hessenbergDetExampleOnes]

/-- Exact rational transcription of the determinant row in Table 1.3. -/
theorem hessenbergDetExampleTable13_det_rows :
    hessenbergDetExampleTable13ExactDetDisplay = 2 ∧
    hessenbergDetExampleTable13ComputedDetDisplay = 2 ∧
    hessenbergDetExampleTable13DetRelativeError =
      19209 / (10 : ℝ) ^ 12 := by
  norm_num [hessenbergDetExampleTable13ExactDetDisplay,
    hessenbergDetExampleTable13ComputedDetDisplay,
    hessenbergDetExampleTable13DetRelativeError]

/-- The primitive determinant product is close enough to the printed computed
determinant entry `2.0000` in Table 1.3. -/
theorem hessenbergDetExampleTable13_detProduct_computedDisplay_near :
    |(8388609 / 4194304 : ℝ) -
        hessenbergDetExampleTable13ComputedDetDisplay| <
      1 / (2 * (10 : ℝ) ^ 4) := by
  norm_num [hessenbergDetExampleTable13ComputedDetDisplay]

/-- The exact relative error of the primitive determinant product agrees with
the displayed Table 1.3 determinant-relative-error row to the printed decimal
precision. -/
theorem hessenbergDetExampleTable13_detProduct_relError_matches_display :
    |relError (8388609 / 4194304 : ℝ)
        (Matrix.det
          (hessenbergDetExampleMatrix (1 / 10000000 : ℝ) :
            Matrix (Fin 4) (Fin 4) ℝ)) -
        hessenbergDetExampleTable13DetRelativeError| <
      1 / (2 * (10 : ℝ) ^ 12) := by
  rw [hessenbergDetExampleTable13_detProduct_relError_eq]
  norm_num [hessenbergDetExampleTable13DetRelativeError]

/-- The exact solution vector in the Table 1.3 row has infinity norm one. -/
theorem hessenbergDetExampleTable13_exactSolution_infNorm_eq :
    infNormVec hessenbergDetExampleOnes = 1 := by
  apply le_antisymm
  · apply infNormVec_le_of_abs_le
    · intro i
      fin_cases i <;> norm_num [hessenbergDetExampleOnes]
    · norm_num
  · have h := abs_le_infNormVec hessenbergDetExampleOnes (0 : Fin 4)
    norm_num [hessenbergDetExampleOnes] at h
    exact h

/-- The infinity norm of the displayed solution error vector in Table 1.3 is
the first-component error `1.3842`. -/
theorem hessenbergDetExampleTable13_solutionError_infNorm_eq :
    infNormVec
        (fun i => hessenbergDetExampleTable13ComputedSolution i -
          hessenbergDetExampleOnes i) =
      13842 / (10 : ℝ) ^ 4 := by
  apply le_antisymm
  · apply infNormVec_le_of_abs_le
    · intro i
      fin_cases i <;>
        norm_num [hessenbergDetExampleTable13ComputedSolution,
          hessenbergDetExampleOnes]
    · norm_num
  · have h :=
      abs_le_infNormVec
        (fun i => hessenbergDetExampleTable13ComputedSolution i -
          hessenbergDetExampleOnes i) (0 : Fin 4)
    norm_num [hessenbergDetExampleTable13ComputedSolution,
      hessenbergDetExampleOnes] at h ⊢
    exact h

/-- The displayed computed solution has the Table 1.3 relative infinity-norm
error `1.3842` against the exact solution vector. -/
theorem hessenbergDetExampleTable13_solution_relative_error_eq :
    infNormVec
        (fun i => hessenbergDetExampleTable13ComputedSolution i -
          hessenbergDetExampleOnes i) /
        infNormVec hessenbergDetExampleOnes =
      hessenbergDetExampleTable13SolutionRelativeError := by
  rw [hessenbergDetExampleTable13_solutionError_infNorm_eq,
    hessenbergDetExampleTable13_exactSolution_infNorm_eq]
  norm_num [hessenbergDetExampleTable13SolutionRelativeError]

/-- Table 1.3's displayed computed solution has first-component absolute error
larger than one, formalizing the source's "no correct figures" observation at
the printed-data level. -/
theorem hessenbergDetExampleTable13_first_component_abs_error_gt_one :
    1 <
      |hessenbergDetExampleTable13ComputedSolution 0 -
        hessenbergDetExampleOnes 0| := by
  norm_num [hessenbergDetExampleTable13ComputedSolution,
    hessenbergDetExampleOnes]

/-- The displayed solution relative error in Table 1.3 is larger than one. -/
theorem hessenbergDetExampleTable13_solution_relative_error_gt_one :
    1 < hessenbergDetExampleTable13SolutionRelativeError := by
  norm_num [hessenbergDetExampleTable13SolutionRelativeError]

/-- The displayed determinant relative error in Table 1.3 is below `2e-8`,
capturing the table's "very accurate determinant" contrast. -/
theorem hessenbergDetExampleTable13_det_relative_error_lt_two_eight :
    hessenbergDetExampleTable13DetRelativeError < 2 / (10 : ℝ) ^ 8 := by
  norm_num [hessenbergDetExampleTable13DetRelativeError]

/-- The residual `b - A*xhat` obtained by inserting the displayed Table 1.3
computed solution into the exact source system.  This is a printed-data
consequence, not a primitive-operation reconstruction of the GE solve. -/
noncomputable def hessenbergDetExampleTable13Residual : Fin 4 → ℝ :=
  fun i =>
    hessenbergDetExampleRhs (1 / 10000000 : ℝ) i -
      matMulVec 4
        (hessenbergDetExampleMatrix (1 / 10000000 : ℝ))
        hessenbergDetExampleTable13ComputedSolution i

/-- Exact rows of `b - A*xhat` for the displayed Table 1.3 computed solution. -/
theorem hessenbergDetExampleTable13_residual_rows :
    hessenbergDetExampleTable13Residual 0 =
        -(13842 / (10 : ℝ) ^ 11) ∧
    hessenbergDetExampleTable13Residual 1 =
        -(13842 / (10 : ℝ) ^ 4) ∧
    hessenbergDetExampleTable13Residual 2 = 0 ∧
    hessenbergDetExampleTable13Residual 3 = 0 := by
  constructor
  · unfold hessenbergDetExampleTable13Residual matMulVec
    rw [Fin.sum_univ_four]
    norm_num [hessenbergDetExampleMatrix, hessenbergDetExampleRhs,
      hessenbergDetExampleTable13ComputedSolution]
  constructor
  · unfold hessenbergDetExampleTable13Residual matMulVec
    rw [Fin.sum_univ_four]
    norm_num [hessenbergDetExampleMatrix, hessenbergDetExampleRhs,
      hessenbergDetExampleTable13ComputedSolution]
  constructor
  · unfold hessenbergDetExampleTable13Residual matMulVec
    rw [Fin.sum_univ_four]
    norm_num [hessenbergDetExampleMatrix, hessenbergDetExampleRhs,
      hessenbergDetExampleTable13ComputedSolution]
    exact sub_self (1 : ℝ)
  · unfold hessenbergDetExampleTable13Residual matMulVec
    rw [Fin.sum_univ_four]
    norm_num [hessenbergDetExampleMatrix, hessenbergDetExampleRhs,
      hessenbergDetExampleTable13ComputedSolution]

/-- The displayed computed solution vector has infinity norm `2.3842`. -/
theorem hessenbergDetExampleTable13_computedSolution_infNorm_eq :
    infNormVec hessenbergDetExampleTable13ComputedSolution =
      23842 / (10 : ℝ) ^ 4 := by
  apply le_antisymm
  · apply infNormVec_le_of_abs_le
    · intro i
      fin_cases i <;>
        norm_num [hessenbergDetExampleTable13ComputedSolution]
    · norm_num
  · have h :=
      abs_le_infNormVec hessenbergDetExampleTable13ComputedSolution (0 : Fin 4)
    norm_num [hessenbergDetExampleTable13ComputedSolution] at h ⊢
    exact h

/-- The exact residual of the displayed computed solution has infinity norm
`1.3842`, the same visible magnitude as the forward error. -/
theorem hessenbergDetExampleTable13_residual_infNorm_eq :
    infNormVec hessenbergDetExampleTable13Residual =
      13842 / (10 : ℝ) ^ 4 := by
  apply le_antisymm
  · apply infNormVec_le_of_abs_le
    · intro i
      rcases hessenbergDetExampleTable13_residual_rows with
        ⟨h0, h1, h2, h3⟩
      fin_cases i <;> simp [h0, h1, h2, h3] <;> norm_num
    · norm_num
  · have h := abs_le_infNormVec hessenbergDetExampleTable13Residual (1 : Fin 4)
    norm_num [hessenbergDetExampleTable13Residual, matMulVec,
      hessenbergDetExampleMatrix, hessenbergDetExampleRhs,
      hessenbergDetExampleTable13ComputedSolution, Fin.sum_univ_four] at h ⊢
    exact h

/-- The source-scaled residual of the displayed computed solution is exactly
`6921/47684` when scaled by `||A||∞ * ||xhat||∞`. -/
theorem hessenbergDetExampleTable13_scaled_residual_eq :
    infNormVec hessenbergDetExampleTable13Residual /
        (infNorm (hessenbergDetExampleMatrix (1 / 10000000 : ℝ)) *
          infNormVec hessenbergDetExampleTable13ComputedSolution) =
      6921 / 47684 := by
  rw [hessenbergDetExampleTable13_residual_infNorm_eq,
    hessenbergDetExampleMatrix_alpha_ten_pow_infNorm_eq,
    hessenbergDetExampleTable13_computedSolution_infNorm_eq]
  norm_num

/-- The source-scaled residual of the displayed computed solution is already
larger than `0.1`, another printed-data indication that this solve path is not
backward stable on the example. -/
theorem hessenbergDetExampleTable13_scaled_residual_gt_one_tenth :
    1 / (10 : ℝ) <
      infNormVec hessenbergDetExampleTable13Residual /
        (infNorm (hessenbergDetExampleMatrix (1 / 10000000 : ℝ)) *
          infNormVec hessenbergDetExampleTable13ComputedSolution) := by
  rw [hessenbergDetExampleTable13_scaled_residual_eq]
  norm_num

/-- Source-value specialization of the §1.16 mixed-stability determinant
bridge: for `alpha = 10^-7`, the final rounded determinant product is within
`gamma_4` of the exact determinant `10000001/5000000`. -/
theorem hessenbergDetExample_alpha_ten_pow_roundedProduct_relError_le_gamma
    (fp : FPModel) (eta : Fin 4 → ℝ)
    (heta : ∀ i : Fin 4, |eta i| ≤ fp.u)
    (hgamma : gammaValid fp 4) :
    relError
        (hessenbergDetRoundedProduct 4
          (hessenbergDetExampleNoPivotUDiag (1 / 10000000 : ℝ)) eta)
        (10000001 / 5000000 : ℝ) ≤ gamma fp 4 := by
  have hbase :=
    hessenbergDetExampleRoundedProduct_relError_le_gamma
      fp (1 / 10000000 : ℝ) eta
      (by norm_num) (by norm_num) heta hgamma
  have hdet :
      Matrix.det
          (hessenbergDetExampleMatrix (1 / 10000000 : ℝ) :
            Matrix (Fin 4) (Fin 4) ℝ) =
        (10000001 / 5000000 : ℝ) :=
    hessenbergDetExampleMatrix_alpha_ten_pow_det_eq
  rw [hdet] at hbase
  exact hbase

/-- The first no-pivot multiplier is `a21/a11 = 1/alpha`. -/
noncomputable def hessenbergDetExampleFirstMultiplier (alpha : ℝ) : ℝ :=
  hessenbergDetExampleMatrix alpha 1 0 / hessenbergDetExampleMatrix alpha 0 0

theorem hessenbergDetExampleFirstMultiplier_eq (alpha : ℝ) :
    hessenbergDetExampleFirstMultiplier alpha = 1 / alpha := by
  norm_num [hessenbergDetExampleFirstMultiplier, hessenbergDetExampleMatrix]

/-- For the displayed `alpha = 10^-7`, the first multiplier is `10^7`. -/
theorem hessenbergDetExampleFirstMultiplier_alpha_ten_pow :
    hessenbergDetExampleFirstMultiplier (1 / (10 : ℝ) ^ 7) =
      (10 : ℝ) ^ 7 := by
  rw [hessenbergDetExampleFirstMultiplier_eq]
  norm_num

end NumStability
