import Mathlib.Algebra.BigOperators.Fin
import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.FinCases
import Mathlib.Tactic.NormNum
import Mathlib.Tactic.Ring
import NumStability.Analysis.Error.Measures.ScalarDefinitions
import NumStability.Analysis.Error.Measures.ScalarWitnesses
import NumStability.Analysis.MatrixAlgebra
import NumStability.Analysis.Rounding
import NumStability.FloatingPoint.Model

-- Analysis/ProblemDependentStability.lean
--
-- Exact examples from Higham Chapter 1, Section 1.16.











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

























































































































































































































































































































































/-! ## Table 1.3 displayed single-precision data -/

























































































































































































































































































































































































































































































































































































































































































































































































































































































































































































































































































































































































































































































































































































































































































































































































































































































































































































































































































































































































































































































































































































































































































































































































































































































































































































































































































































































end NumStability
