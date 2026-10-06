import Mathlib.Algebra.BigOperators.Intervals
import Mathlib.Algebra.BigOperators.Ring.Finset
import Mathlib.Algebra.Polynomial.Roots
import Mathlib.Analysis.SpecialFunctions.Gaussian.GaussianIntegral
import Mathlib.Analysis.SpecialFunctions.OrdinaryHypergeometric
import Mathlib.Analysis.SpecialFunctions.Pow.Real
import Mathlib.Analysis.SpecialFunctions.Stirling
import Mathlib.Data.Nat.Choose.Cast
import Mathlib.Data.Nat.Choose.Sum
import Mathlib.Data.Nat.Choose.Vandermonde
import Mathlib.LinearAlgebra.Matrix.Block
import Mathlib.LinearAlgebra.UnitaryGroup
import Mathlib.MeasureTheory.Constructions.Pi
import Mathlib.MeasureTheory.Function.L2Space
import Mathlib.MeasureTheory.Integral.Bochner.Basic
import Mathlib.MeasureTheory.Integral.Pi
import Mathlib.MeasureTheory.Measure.Haar.Basic
import Mathlib.Probability.Distributions.Gaussian.Real
import NumStability.Algorithms.LinearSystems.QR.HouseholderReflector
import NumStability.Algorithms.LinearSystems.QR.Householder.TrailingPanels
import NumStability.Analysis.Conditioning.LinearSystems.PerronFrobenius
import NumStability.Analysis.MatrixAlgebra

/-!
# Chapter28 Section02 RealGinibre FiniteExpectation GinibreCharacteristicProduct

Canonical destination for material split out of
`NumStability.Algorithms.TestMatrices.Higham28GinibreCharacteristicProduct` by wave W09 of the August 2026 repository reorganization.
Declaration names, statements and proofs are unchanged; only the
module they live in has changed. The historical module still
resolves and re-exports this one.
-/

noncomputable section

namespace NumStability

open Matrix MeasureTheory ProbabilityTheory

open scoped BigOperators

/-- The second moment of a standard real Gaussian is one. -/
theorem integral_standardGaussian_sq :
    (∫ x : ℝ, x ^ 2 ∂gaussianReal 0 1) = 1 := by
  have hv := @variance_id_gaussianReal (0 : ℝ) (1 : NNReal)
  change Var[(fun x : ℝ => x); gaussianReal 0 1] = (1 : NNReal) at hv
  rw [variance_of_integral_eq_zero measurable_id'.aemeasurable (by simp)] at hv
  norm_num at hv ⊢
  exact hv

/-- The identity function is integrable under the standard real Gaussian. -/
theorem integrable_standardGaussian_id :
    Integrable (fun x : ℝ => x) (gaussianReal 0 1) := by
  simpa only [id_eq] using
    ((memLp_id_gaussianReal (μ := (0 : ℝ)) (v := (1 : NNReal)) 1).integrable
      (by norm_num))

/-- The square function is integrable under the standard real Gaussian. -/
theorem integrable_standardGaussian_sq :
    Integrable (fun x : ℝ => x ^ 2) (gaussianReal 0 1) := by
  simpa only [id_eq] using
    (memLp_id_gaussianReal (μ := (0 : ℝ)) (v := (1 : NNReal)) 2).integrable_sq

/-- The coordinate factor obtained by multiplying the monomials belonging
to two determinant permutations. -/
def ginibrePermutationPairCoordinateFactor {n : ℕ}
    (σ τ : Equiv.Perm (Fin n)) (i j : Fin n) (x : ℝ) : ℝ :=
  (if σ j = i then x else 1) * (if τ j = i then x else 1)

/-- Multiplying the coordinate factors recovers the product of the two
permutation monomials. -/
theorem ginibrePermutationPairCoordinateProduct {n : ℕ}
    (σ τ : Equiv.Perm (Fin n)) (A : RSqMat n) :
    (∏ i, ∏ j, ginibrePermutationPairCoordinateFactor σ τ i j (A i j)) =
      (∏ j, A (σ j) j) * ∏ j, A (τ j) j := by
  rw [Finset.prod_comm]
  simp_rw [ginibrePermutationPairCoordinateFactor, Finset.prod_mul_distrib]
  simp

/-- Every one-coordinate permutation-pair factor is integrable. -/
theorem integrable_ginibrePermutationPairCoordinateFactor {n : ℕ}
    (σ τ : Equiv.Perm (Fin n)) (i j : Fin n) :
    Integrable (ginibrePermutationPairCoordinateFactor σ τ i j)
      (gaussianReal 0 1) := by
  change Integrable
    (fun x : ℝ =>
      (if σ j = i then x else 1) * (if τ j = i then x else 1))
    (gaussianReal 0 1)
  by_cases hσ : σ j = i <;> by_cases hτ : τ j = i
  · simpa [hσ, hτ, pow_two] using
      integrable_standardGaussian_sq
  · simpa [hσ, hτ] using
      integrable_standardGaussian_id
  · simpa [hσ, hτ] using
      integrable_standardGaussian_id
  · simpa [hσ, hτ] using
      (integrable_const (μ := gaussianReal 0 1) (c := (1 : ℝ)))

/-- The integral of a single coordinate factor is one exactly when the two
permutation monomials either both use that coordinate or both omit it. -/
theorem integral_ginibrePermutationPairCoordinateFactor {n : ℕ}
    (σ τ : Equiv.Perm (Fin n)) (i j : Fin n) :
    (∫ x : ℝ, ginibrePermutationPairCoordinateFactor σ τ i j x
      ∂gaussianReal 0 1) =
      if (σ j = i ↔ τ j = i) then 1 else 0 := by
  by_cases hσ : σ j = i <;> by_cases hτ : τ j = i
  · have hiff : (σ j = i ↔ τ j = i) := ⟨fun _ => hτ, fun _ => hσ⟩
    rw [if_pos hiff]
    simpa [ginibrePermutationPairCoordinateFactor, hσ, hτ, pow_two] using
      integral_standardGaussian_sq
  · have hiff : ¬(σ j = i ↔ τ j = i) := fun h => hτ (h.mp hσ)
    rw [if_neg hiff]
    simp [ginibrePermutationPairCoordinateFactor, hσ, hτ]
  · have hiff : ¬(σ j = i ↔ τ j = i) := fun h => hσ (h.mpr hτ)
    rw [if_neg hiff]
    simp [ginibrePermutationPairCoordinateFactor, hσ, hτ]
  · have hiff : (σ j = i ↔ τ j = i) :=
      ⟨fun h => (hσ h).elim, fun h => (hτ h).elim⟩
    rw [if_pos hiff]
    simp [ginibrePermutationPairCoordinateFactor, hσ, hτ]

/-- The full product of coordinate-factor integrals is the Kronecker delta
on determinant permutations. -/
theorem prod_integral_ginibrePermutationPairCoordinateFactor {n : ℕ}
    (σ τ : Equiv.Perm (Fin n)) :
    (∏ i, ∏ j,
      ∫ x : ℝ, ginibrePermutationPairCoordinateFactor σ τ i j x
        ∂gaussianReal 0 1) =
      if σ = τ then 1 else 0 := by
  simp_rw [integral_ginibrePermutationPairCoordinateFactor]
  by_cases hστ : σ = τ
  · subst τ
    simp
  · rw [if_neg hστ]
    have hex : ∃ j : Fin n, σ j ≠ τ j := by
      by_contra h
      push_neg at h
      exact hστ (Equiv.ext h)
    obtain ⟨j, hj⟩ := hex
    have hrev : τ j ≠ σ j := Ne.symm hj
    apply Finset.prod_eq_zero (Finset.mem_univ (σ j))
    apply Finset.prod_eq_zero (Finset.mem_univ j)
    simp [hrev]

/-- The real sign coefficient in the Leibniz determinant expansion. -/
def ginibrePermutationSignReal {n : ℕ} (σ : Equiv.Perm (Fin n)) : ℝ :=
  (((Equiv.Perm.sign σ : ℤˣ) : ℤ) : ℝ)

/-- A real permutation sign squares to one. -/
theorem ginibrePermutationSignReal_mul_self {n : ℕ}
    (σ : Equiv.Perm (Fin n)) :
    ginibrePermutationSignReal σ * ginibrePermutationSignReal σ = 1 := by
  have hunit : Equiv.Perm.sign σ * Equiv.Perm.sign σ = 1 := by
    rw [← Equiv.Perm.sign_inv σ, ← Equiv.Perm.sign_mul]
    simp
  have hint :
      ((Equiv.Perm.sign σ : ℤˣ) : ℤ) *
          ((Equiv.Perm.sign σ : ℤˣ) : ℤ) = 1 := by
    simpa using congrArg (fun u : ℤˣ => (u : ℤ)) hunit
  unfold ginibrePermutationSignReal
  exact_mod_cast hint

/-- A signed monomial in the Leibniz determinant expansion. -/
def ginibreDeterminantPermutationTerm {n : ℕ}
    (σ : Equiv.Perm (Fin n)) (A : RSqMat n) : ℝ :=
  ginibrePermutationSignReal σ * ∏ j, A (σ j) j

/-- The determinant is the sum of its signed permutation monomials. -/
theorem ginibre_det_eq_sum_permutationTerms {n : ℕ} (A : RSqMat n) :
    A.det = ∑ σ : Equiv.Perm (Fin n),
      ginibreDeterminantPermutationTerm σ A := by
  simpa [ginibreDeterminantPermutationTerm, ginibrePermutationSignReal] using
    Matrix.det_apply' A

/-- The standard-Gaussian mean of the affine function `z - x`. -/
theorem integral_standardGaussian_sub (z : ℝ) :
    (∫ x : ℝ, z - x ∂gaussianReal 0 1) = z := by
  rw [integral_sub (integrable_const _) integrable_standardGaussian_id]
  simp

/-- The negative of a centered standard Gaussian still has mean zero. -/
theorem integral_standardGaussian_neg :
    (∫ x : ℝ, -x ∂gaussianReal 0 1) = 0 := by
  rw [integral_neg (fun x : ℝ => x), integral_id_gaussianReal]
  simp

/-- A product of two affine functions is integrable under the standard
Gaussian law. -/
theorem integrable_standardGaussian_sub_mul_sub (z w : ℝ) :
    Integrable (fun x : ℝ => (z - x) * (w - x)) (gaussianReal 0 1) := by
  have hpoly : Integrable
      (fun x : ℝ => x ^ 2 - (z + w) * x + z * w)
      (gaussianReal 0 1) :=
    ((integrable_standardGaussian_sq.sub
      (integrable_standardGaussian_id.const_mul (z + w))).add
        (integrable_const (μ := gaussianReal 0 1) (c := z * w)))
  apply hpoly.congr
  filter_upwards with x
  ring

/-- The exact Gaussian affine-product identity
`𝔼[(z-X)(w-X)] = zw + 1`. -/
theorem integral_standardGaussian_sub_mul_sub (z w : ℝ) :
    (∫ x : ℝ, (z - x) * (w - x) ∂gaussianReal 0 1) = z * w + 1 := by
  calc
    (∫ x : ℝ, (z - x) * (w - x) ∂gaussianReal 0 1) =
        ∫ x : ℝ, x ^ 2 - (z + w) * x + z * w
          ∂gaussianReal 0 1 := by
            apply integral_congr_ae
            filter_upwards with x
            ring
    _ = (∫ x : ℝ, x ^ 2 ∂gaussianReal 0 1) -
          (z + w) * (∫ x : ℝ, x ∂gaussianReal 0 1) +
          (∫ _x : ℝ, z * w ∂gaussianReal 0 1) := by
      rw [integral_add]
      · rw [integral_sub]
        · rw [integral_const_mul]
        · exact integrable_standardGaussian_sq
        · exact integrable_standardGaussian_id.const_mul (z + w)
      · exact integrable_standardGaussian_sq.sub
          (integrable_standardGaussian_id.const_mul (z + w))
      · exact integrable_const _
    _ = z * w + 1 := by
      rw [integral_standardGaussian_sq, integral_id_gaussianReal]
      simp
      ring

/-- The coordinate factor for the product of permutation monomials in
`det (zI-A)` and `det (wI-A)`. -/
def ginibreShiftedPermutationPairCoordinateFactor {n : ℕ}
    (z w : ℝ) (σ τ : Equiv.Perm (Fin n)) (i j : Fin n) (x : ℝ) : ℝ :=
  (if σ j = i then (if i = j then z - x else -x) else 1) *
    (if τ j = i then (if i = j then w - x else -x) else 1)

/-- Multiplying shifted coordinate factors recovers the two shifted
permutation monomials. -/
theorem ginibreShiftedPermutationPairCoordinateProduct {n : ℕ}
    (z w : ℝ) (σ τ : Equiv.Perm (Fin n)) (A : RSqMat n) :
    (∏ i, ∏ j,
      ginibreShiftedPermutationPairCoordinateFactor z w σ τ i j (A i j)) =
      (∏ j, (z • (1 : RSqMat n) - A) (σ j) j) *
        ∏ j, (w • (1 : RSqMat n) - A) (τ j) j := by
  rw [Finset.prod_comm]
  simp_rw [ginibreShiftedPermutationPairCoordinateFactor,
    Finset.prod_mul_distrib]
  simp [Matrix.one_apply, apply_ite]
  congr 1
  · apply Finset.prod_congr rfl
    intro j hj
    split_ifs <;> ring
  · apply Finset.prod_congr rfl
    intro j hj
    split_ifs <;> ring

/-- Every shifted coordinate factor is integrable. -/
theorem integrable_ginibreShiftedPermutationPairCoordinateFactor {n : ℕ}
    (z w : ℝ) (σ τ : Equiv.Perm (Fin n)) (i j : Fin n) :
    Integrable (ginibreShiftedPermutationPairCoordinateFactor z w σ τ i j)
      (gaussianReal 0 1) := by
  change Integrable
    (fun x : ℝ =>
      (if σ j = i then (if i = j then z - x else -x) else 1) *
        (if τ j = i then (if i = j then w - x else -x) else 1))
    (gaussianReal 0 1)
  by_cases hij : i = j
  · subst i
    by_cases hσ : σ j = j <;> by_cases hτ : τ j = j
    · simpa [hσ, hτ] using
        integrable_standardGaussian_sub_mul_sub z w
    · simpa [hσ, hτ] using
        (integrable_const (μ := gaussianReal 0 1) (c := (z : ℝ))).sub
          integrable_standardGaussian_id
    · simpa [hσ, hτ] using
        (integrable_const (μ := gaussianReal 0 1) (c := (w : ℝ))).sub
          integrable_standardGaussian_id
    · simpa [hσ, hτ] using
        (integrable_const (μ := gaussianReal 0 1) (c := (1 : ℝ)))
  · by_cases hσ : σ j = i <;> by_cases hτ : τ j = i
    · simpa [hσ, hτ, hij, neg_mul_neg, pow_two] using
        integrable_standardGaussian_sq
    · have hneg : Integrable (fun x : ℝ => -x) (gaussianReal 0 1) :=
        integrable_standardGaussian_id.neg
      simpa [hσ, hτ, hij] using hneg
    · have hneg : Integrable (fun x : ℝ => -x) (gaussianReal 0 1) :=
        integrable_standardGaussian_id.neg
      simpa [hσ, hτ, hij] using hneg
    · simpa [hσ, hτ, hij] using
        (integrable_const (μ := gaussianReal 0 1) (c := (1 : ℝ)))

/-- Exact integral of one shifted coordinate factor. -/
theorem integral_ginibreShiftedPermutationPairCoordinateFactor {n : ℕ}
    (z w : ℝ) (σ τ : Equiv.Perm (Fin n)) (i j : Fin n) :
    (∫ x : ℝ,
      ginibreShiftedPermutationPairCoordinateFactor z w σ τ i j x
      ∂gaussianReal 0 1) =
      if σ j = i then
        if τ j = i then (if i = j then z * w + 1 else 1)
        else (if i = j then z else 0)
      else if τ j = i then (if i = j then w else 0) else 1 := by
  by_cases hij : i = j
  · subst i
    by_cases hσ : σ j = j <;> by_cases hτ : τ j = j
    · simp [ginibreShiftedPermutationPairCoordinateFactor, hσ, hτ,
        integral_standardGaussian_sub_mul_sub]
    · simp [ginibreShiftedPermutationPairCoordinateFactor, hσ, hτ,
        integral_standardGaussian_sub]
    · simp [ginibreShiftedPermutationPairCoordinateFactor, hσ, hτ,
        integral_standardGaussian_sub]
    · simp [ginibreShiftedPermutationPairCoordinateFactor, hσ, hτ]
  · by_cases hσ : σ j = i <;> by_cases hτ : τ j = i
    · simpa [ginibreShiftedPermutationPairCoordinateFactor, hσ, hτ, hij,
        neg_mul_neg, pow_two] using integral_standardGaussian_sq
    · simpa [ginibreShiftedPermutationPairCoordinateFactor, hσ, hτ, hij] using
        integral_standardGaussian_neg
    · simpa [ginibreShiftedPermutationPairCoordinateFactor, hσ, hτ, hij] using
        integral_standardGaussian_neg
    · simp [ginibreShiftedPermutationPairCoordinateFactor, hσ, hτ, hij]

/-- The fixed points of a finite permutation as a finset. -/
def ginibrePermutationFixedPoints {n : ℕ}
    (σ : Equiv.Perm (Fin n)) : Finset (Fin n) :=
  Finset.univ.filter fun j => σ j = j

@[simp] theorem mem_ginibrePermutationFixedPoints {n : ℕ}
    (σ : Equiv.Perm (Fin n)) (j : Fin n) :
    j ∈ ginibrePermutationFixedPoints σ ↔ σ j = j := by
  simp [ginibrePermutationFixedPoints]

/-- Diagonal specialization of the one-coordinate shifted integral. -/
theorem integral_ginibreShiftedPermutationPairCoordinateFactor_self {n : ℕ}
    (z w : ℝ) (σ : Equiv.Perm (Fin n)) (i j : Fin n) :
    (∫ x : ℝ,
      ginibreShiftedPermutationPairCoordinateFactor z w σ σ i j x
      ∂gaussianReal 0 1) =
      if σ j = i then (if i = j then 1 + z * w else 1) else 1 := by
  rw [integral_ginibreShiftedPermutationPairCoordinateFactor]
  by_cases hij : i = j
  · subst i
    by_cases h : σ j = j <;> simp [h] <;> ring
  · by_cases h : σ j = i <;> simp [h, hij]

/-- The product of all shifted coordinate-factor integrals vanishes for
distinct permutations.  On the diagonal it records one factor `1+zw` per
fixed point. -/
theorem prod_integral_ginibreShiftedPermutationPairCoordinateFactor {n : ℕ}
    (z w : ℝ) (σ τ : Equiv.Perm (Fin n)) :
    (∏ i, ∏ j,
      ∫ x : ℝ,
        ginibreShiftedPermutationPairCoordinateFactor z w σ τ i j x
        ∂gaussianReal 0 1) =
      if σ = τ then
        (1 + z * w) ^ (ginibrePermutationFixedPoints σ).card
      else 0 := by
  by_cases hστ : σ = τ
  · subst τ
    rw [if_pos rfl]
    simp_rw [integral_ginibreShiftedPermutationPairCoordinateFactor_self]
    rw [Finset.prod_comm]
    have hinner (j : Fin n) :
        (∏ i : Fin n,
          if σ j = i then (if i = j then 1 + z * w else 1) else 1) =
          if σ j = j then 1 + z * w else 1 := by
      simpa [eq_comm] using
        (Finset.prod_ite_eq' (Finset.univ : Finset (Fin n)) (σ j)
          (fun i => if i = j then 1 + z * w else 1))
    simp_rw [hinner]
    rw [← Finset.prod_filter]
    simp [ginibrePermutationFixedPoints, Finset.prod_const]
  · simp_rw [integral_ginibreShiftedPermutationPairCoordinateFactor]
    rw [if_neg hστ]
    have hex : ∃ j : Fin n, σ j ≠ τ j := by
      by_contra h
      push_neg at h
      exact hστ (Equiv.ext h)
    obtain ⟨j, hj⟩ := hex
    by_cases hdiag : σ j = j
    · have hτdiag : τ j ≠ j := fun h => hj (hdiag.trans h.symm)
      have hjτ : j ≠ τ j := Ne.symm hτdiag
      apply Finset.prod_eq_zero (Finset.mem_univ (τ j))
      apply Finset.prod_eq_zero (Finset.mem_univ j)
      simp [hdiag, hτdiag, hjτ]
    · have hrev : τ j ≠ σ j := Ne.symm hj
      apply Finset.prod_eq_zero (Finset.mem_univ (σ j))
      apply Finset.prod_eq_zero (Finset.mem_univ j)
      simp [hdiag, hrev]

/-- A signed permutation term in the shifted determinant `det (zI-A)`. -/
def ginibreShiftedDeterminantPermutationTerm {n : ℕ}
    (z : ℝ) (σ : Equiv.Perm (Fin n)) (A : RSqMat n) : ℝ :=
  ginibrePermutationSignReal σ *
    ∏ j, (z • (1 : RSqMat n) - A) (σ j) j

/-- Leibniz expansion of the shifted determinant. -/
theorem ginibre_shiftedDet_eq_sum_permutationTerms {n : ℕ}
    (z : ℝ) (A : RSqMat n) :
    (z • (1 : RSqMat n) - A).det =
      ∑ σ : Equiv.Perm (Fin n),
        ginibreShiftedDeterminantPermutationTerm z σ A := by
  simpa [ginibreShiftedDeterminantPermutationTerm,
    ginibrePermutationSignReal] using
      Matrix.det_apply' (z • (1 : RSqMat n) - A)

/-- Permutations that fix every element of `S` pointwise. -/
def ginibrePermutationsFixing {n : ℕ} (S : Finset (Fin n)) :=
  {σ : Equiv.Perm (Fin n) // ∀ j, j ∈ S → σ j = j}

noncomputable instance ginibrePermutationsFixingFintype {n : ℕ}
    (S : Finset (Fin n)) : Fintype (ginibrePermutationsFixing S) := by
  exact Fintype.ofInjective
    (fun σ : ginibrePermutationsFixing S => σ.1) Subtype.val_injective

/-- Extending a permutation of the complement of `S` gives a permutation
that fixes `S` pointwise. -/
def ginibreComplementPermToFixing {n : ℕ} (S : Finset (Fin n)) :
    Equiv.Perm {j : Fin n // j ∉ S} → ginibrePermutationsFixing S :=
  fun π => ⟨Equiv.Perm.ofSubtype π, fun j hj => by
    rw [Equiv.Perm.ofSubtype_apply_of_not_mem]
    simpa using hj⟩

theorem ginibreComplementPermToFixing_injective {n : ℕ}
    (S : Finset (Fin n)) :
    Function.Injective (ginibreComplementPermToFixing S) := by
  intro π ρ h
  apply Equiv.Perm.ofSubtype_injective
  exact congrArg Subtype.val h

theorem ginibreComplementPermToFixing_surjective {n : ℕ}
    (S : Finset (Fin n)) :
    Function.Surjective (ginibreComplementPermToFixing S) := by
  intro σ
  have hmem (x : Fin n) : σ.1 x ∈ S ↔ x ∈ S := by
    constructor
    · intro hx
      have hfix : σ.1 (σ.1 x) = σ.1 x := σ.2 (σ.1 x) hx
      have heq : σ.1 x = x := σ.1.injective hfix
      simpa [heq] using hx
    · intro hx
      simpa [σ.2 x hx] using hx
  have hinv (x : Fin n) : σ.1 x ∉ S ↔ x ∉ S := not_congr (hmem x)
  have hmove (x : Fin n) (hx : σ.1 x ≠ x) : x ∉ S := by
    intro hxS
    exact hx (σ.2 x hxS)
  let π : Equiv.Perm {j : Fin n // j ∉ S} := σ.1.subtypePerm hinv
  refine ⟨π, Subtype.ext ?_⟩
  change Equiv.Perm.ofSubtype π = σ.1
  exact Equiv.Perm.ofSubtype_subtypePerm hinv hmove

/-- Permutations of the complement are equivalent to permutations fixing
`S` pointwise. -/
def ginibreComplementPermEquivFixing {n : ℕ} (S : Finset (Fin n)) :
    Equiv.Perm {j : Fin n // j ∉ S} ≃ ginibrePermutationsFixing S :=
  Equiv.ofBijective (ginibreComplementPermToFixing S)
    ⟨ginibreComplementPermToFixing_injective S,
      ginibreComplementPermToFixing_surjective S⟩

/-- Exactly `(n-|S|)!` permutations fix `S` pointwise. -/
theorem card_ginibrePermutationsFixing {n : ℕ} (S : Finset (Fin n)) :
    Fintype.card (ginibrePermutationsFixing S) = (n - S.card).factorial := by
  rw [← Fintype.card_congr (ginibreComplementPermEquivFixing S)]
  rw [Fintype.card_perm]
  congr 1
  simpa using Fintype.card_subtype_compl (fun j : Fin n => j ∈ S)

/-- A constant summed over permutations fixing `S` contributes exactly
`(n-|S|)!` copies. -/
theorem sum_indicator_ginibrePermutationsFixing {n : ℕ}
    (S : Finset (Fin n)) (c : ℝ) :
    (∑ σ : Equiv.Perm (Fin n),
      if (∀ j, j ∈ S → σ j = j) then c else 0) =
      ((n - S.card).factorial : ℝ) * c := by
  let p : Equiv.Perm (Fin n) → Prop :=
    fun σ => ∀ j, j ∈ S → σ j = j
  change (∑ σ : Equiv.Perm (Fin n), if p σ then c else 0) = _
  rw [← Finset.sum_filter]
  have hsum : (∑ σ ∈ Finset.univ.filter p, c) =
      ∑ _σ : ginibrePermutationsFixing S, c := by
    unfold ginibrePermutationsFixing
    exact Finset.sum_subtype (Finset.univ.filter p) (by
      intro σ
      simp [p]) (fun _ => c)
  rw [hsum]
  simp [card_ginibrePermutationsFixing, nsmul_eq_mul]

/-- Binomial expansion indexed by subsets of the fixed-point set. -/
theorem one_add_pow_card_ginibrePermutationFixedPoints {n : ℕ}
    (t : ℝ) (σ : Equiv.Perm (Fin n)) :
    (1 + t) ^ (ginibrePermutationFixedPoints σ).card =
      ∑ S ∈ (ginibrePermutationFixedPoints σ).powerset, t ^ S.card := by
  calc
    (1 + t) ^ (ginibrePermutationFixedPoints σ).card =
        ∏ _j ∈ ginibrePermutationFixedPoints σ, (1 + t) := by
      simp [Finset.prod_const]
    _ = ∑ S ∈ (ginibrePermutationFixedPoints σ).powerset,
          ∏ _j ∈ S, t := by
      simpa using Finset.prod_one_add
        (f := fun _j : Fin n => t) (ginibrePermutationFixedPoints σ)
    _ = ∑ S ∈ (ginibrePermutationFixedPoints σ).powerset,
          t ^ S.card := by
      apply Finset.sum_congr rfl
      intro S hS
      simp [Finset.prod_const]

/-- A subset sum over the fixed points may be extended to all subsets by
an indicator that the subset is fixed pointwise. -/
theorem sum_powerset_ginibrePermutationFixedPoints_eq_indicator {n : ℕ}
    (t : ℝ) (σ : Equiv.Perm (Fin n)) :
    (∑ S ∈ (ginibrePermutationFixedPoints σ).powerset, t ^ S.card) =
      ∑ S ∈ (Finset.univ : Finset (Fin n)).powerset,
        if S ⊆ ginibrePermutationFixedPoints σ then t ^ S.card else 0 := by
  have hfilter :
      ((Finset.univ : Finset (Fin n)).powerset.filter
        (fun S => S ⊆ ginibrePermutationFixedPoints σ)) =
        (ginibrePermutationFixedPoints σ).powerset := by
    ext S
    simp
  rw [← Finset.sum_filter]
  rw [hfilter]

/-- The fixed-point enumerator is the subset-weighted factorial sum. -/
theorem sum_pow_card_ginibrePermutationFixedPoints_eq_powerset
    (n : ℕ) (t : ℝ) :
    (∑ σ : Equiv.Perm (Fin n),
      (1 + t) ^ (ginibrePermutationFixedPoints σ).card) =
      ∑ S ∈ (Finset.univ : Finset (Fin n)).powerset,
        ((n - S.card).factorial : ℝ) * t ^ S.card := by
  simp_rw [one_add_pow_card_ginibrePermutationFixedPoints,
    sum_powerset_ginibrePermutationFixedPoints_eq_indicator]
  rw [Finset.sum_comm]
  apply Finset.sum_congr rfl
  intro S hS
  have hfix (σ : Equiv.Perm (Fin n)) :
      S ⊆ ginibrePermutationFixedPoints σ ↔
        ∀ j, j ∈ S → σ j = j := by
    simp [Finset.subset_iff]
  simp_rw [hfix]
  exact sum_indicator_ginibrePermutationsFixing S (t ^ S.card)

/-- Grouping the subset-weighted sum by subset cardinality produces the
binomial-coefficient form. -/
theorem sum_pow_card_ginibrePermutationFixedPoints_eq_range
    (n : ℕ) (t : ℝ) :
    (∑ σ : Equiv.Perm (Fin n),
      (1 + t) ^ (ginibrePermutationFixedPoints σ).card) =
      ∑ k ∈ Finset.range (n + 1),
        (n.choose k : ℝ) * ((n - k).factorial : ℝ) * t ^ k := by
  rw [sum_pow_card_ginibrePermutationFixedPoints_eq_powerset]
  have h := Finset.sum_powerset_apply_card
    (x := (Finset.univ : Finset (Fin n)))
    (fun k => ((n - k).factorial : ℝ) * t ^ k)
  simpa only [Finset.card_univ, Fintype.card_fin, nsmul_eq_mul,
    Nat.cast_ofNat, mul_assoc] using h

/-- Real-cast form of `choose(n,k) (n-k)! = n!/k!`. -/
theorem cast_choose_mul_factorial_sub_eq_factorial_div
    {n k : ℕ} (hk : k ≤ n) :
    (n.choose k : ℝ) * ((n - k).factorial : ℝ) =
      (n.factorial : ℝ) / (k.factorial : ℝ) := by
  have hnat := Nat.choose_mul_factorial_mul_factorial hk
  have hreal :
      (n.choose k : ℝ) * (k.factorial : ℝ) *
          ((n - k).factorial : ℝ) = (n.factorial : ℝ) := by
    exact_mod_cast hnat
  rw [eq_div_iff (by positivity : (k.factorial : ℝ) ≠ 0)]
  calc
    (n.choose k : ℝ) * ((n - k).factorial : ℝ) *
        (k.factorial : ℝ) =
        (n.choose k : ℝ) * (k.factorial : ℝ) *
          ((n - k).factorial : ℝ) := by ring
    _ = (n.factorial : ℝ) := hreal

/-- Closed form of the finite symmetric-group fixed-point enumerator. -/
theorem sum_pow_card_ginibrePermutationFixedPoints
    (n : ℕ) (t : ℝ) :
    (∑ σ : Equiv.Perm (Fin n),
      (1 + t) ^ (ginibrePermutationFixedPoints σ).card) =
      (n.factorial : ℝ) *
        ∑ k ∈ Finset.range (n + 1),
          t ^ k / (k.factorial : ℝ) := by
  rw [sum_pow_card_ginibrePermutationFixedPoints_eq_range]
  rw [Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro k hk
  have hkn : k ≤ n := Nat.le_of_lt_succ (Finset.mem_range.1 hk)
  rw [cast_choose_mul_factorial_sub_eq_factorial_div hkn]
  ring

/-- Reversing both shifted determinants introduces two copies of the same
`(-1)^n` factor, so their product is unchanged. -/
theorem det_sub_smul_one_mul_det_sub_smul_one_eq
    (n : ℕ) (A : RSqMat n) (u x : ℝ) :
    (A - u • (1 : RSqMat n)).det *
        (A - x • (1 : RSqMat n)).det =
      (u • (1 : RSqMat n) - A).det *
        (x • (1 : RSqMat n) - A).det := by
  have hu : A - u • (1 : RSqMat n) =
      -(u • (1 : RSqMat n) - A) := by
    abel
  have hx : A - x • (1 : RSqMat n) =
      -(x • (1 : RSqMat n) - A) := by
    abel
  rw [hu, hx, Matrix.det_neg, Matrix.det_neg, Fintype.card_fin]
  have hsign : ((-1 : ℝ) ^ n) * ((-1 : ℝ) ^ n) = 1 := by
    rw [← pow_two, ← pow_mul]
    norm_num
  calc
    (-1 : ℝ) ^ n * (u • (1 : RSqMat n) - A).det *
          ((-1 : ℝ) ^ n * (x • (1 : RSqMat n) - A).det) =
        (((-1 : ℝ) ^ n) * ((-1 : ℝ) ^ n)) *
          ((u • (1 : RSqMat n) - A).det *
            (x • (1 : RSqMat n) - A).det) := by ring
    _ = _ := by rw [hsign, one_mul]

theorem integrable_standardGaussian_complex_id :
    Integrable (fun x : ℝ => (x : ℂ)) (gaussianReal 0 1) :=
  integrable_standardGaussian_id.ofReal

theorem integral_standardGaussian_complex_id :
    (∫ x : ℝ, (x : ℂ) ∂gaussianReal 0 1) = 0 := by
  calc
    (∫ x : ℝ, (x : ℂ) ∂gaussianReal 0 1) =
        Complex.ofReal (∫ x : ℝ, x ∂gaussianReal 0 1) := by
      exact integral_complex_ofReal
        (μ := gaussianReal 0 1) (f := fun x : ℝ => x)
    _ = 0 := by rw [integral_id_gaussianReal]; simp

theorem integrable_standardGaussian_complex_sq :
    Integrable (fun x : ℝ => (x : ℂ) ^ 2) (gaussianReal 0 1) := by
  have h : Integrable (fun x : ℝ => ((x ^ 2 : ℝ) : ℂ))
      (gaussianReal 0 1) := integrable_standardGaussian_sq.ofReal
  apply h.congr
  filter_upwards with x
  simp

theorem integral_standardGaussian_complex_sq :
    (∫ x : ℝ, (x : ℂ) ^ 2 ∂gaussianReal 0 1) = 1 := by
  have h := @integral_complex_ofReal ℝ _ (gaussianReal 0 1)
    (fun x : ℝ => x ^ 2)
  rw [integral_standardGaussian_sq] at h
  simpa only [Complex.ofReal_pow, Complex.ofReal_one] using h

theorem integral_standardGaussian_complex_sub (z : ℂ) :
    (∫ x : ℝ, z - (x : ℂ) ∂gaussianReal 0 1) = z := by
  rw [integral_sub (integrable_const _) integrable_standardGaussian_complex_id]
  rw [integral_standardGaussian_complex_id]
  simp

theorem integrable_standardGaussian_complex_sub_mul_sub (z w : ℂ) :
    Integrable (fun x : ℝ => (z - (x : ℂ)) * (w - (x : ℂ)))
      (gaussianReal 0 1) := by
  have hpoly : Integrable
      (fun x : ℝ => (x : ℂ) ^ 2 - (z + w) * (x : ℂ) + z * w)
      (gaussianReal 0 1) :=
    ((integrable_standardGaussian_complex_sq.sub
      (integrable_standardGaussian_complex_id.const_mul (z + w))).add
        (integrable_const (μ := gaussianReal 0 1) (c := z * w)))
  apply hpoly.congr
  filter_upwards with x
  ring

theorem integral_standardGaussian_complex_sub_mul_sub (z w : ℂ) :
    (∫ x : ℝ, (z - (x : ℂ)) * (w - (x : ℂ)) ∂gaussianReal 0 1) =
      z * w + 1 := by
  calc
    (∫ x : ℝ, (z - (x : ℂ)) * (w - (x : ℂ)) ∂gaussianReal 0 1) =
        ∫ x : ℝ, (x : ℂ) ^ 2 - (z + w) * (x : ℂ) + z * w
          ∂gaussianReal 0 1 := by
            apply integral_congr_ae
            filter_upwards with x
            ring
    _ = (∫ x : ℝ, (x : ℂ) ^ 2 - (z + w) * (x : ℂ)
          ∂gaussianReal 0 1) +
          (∫ _x : ℝ, z * w ∂gaussianReal 0 1) := by
      exact integral_add
        (integrable_standardGaussian_complex_sq.sub
          (integrable_standardGaussian_complex_id.const_mul (z + w)))
        (integrable_const _)
    _ = ((∫ x : ℝ, (x : ℂ) ^ 2 ∂gaussianReal 0 1) -
          ∫ x : ℝ, (z + w) * (x : ℂ) ∂gaussianReal 0 1) +
          (∫ _x : ℝ, z * w ∂gaussianReal 0 1) := by
      rw [integral_sub integrable_standardGaussian_complex_sq
        (integrable_standardGaussian_complex_id.const_mul (z + w))]
    _ = (∫ x : ℝ, (x : ℂ) ^ 2 ∂gaussianReal 0 1) -
          (z + w) * (∫ x : ℝ, (x : ℂ) ∂gaussianReal 0 1) +
          (∫ _x : ℝ, z * w ∂gaussianReal 0 1) := by
      have hcmul :
          (∫ x : ℝ, (z + w) * (x : ℂ) ∂gaussianReal 0 1) =
            (z + w) *
              ∫ x : ℝ, (x : ℂ) ∂gaussianReal 0 1 :=
        integral_const_mul (μ := gaussianReal 0 1)
          (z + w) (fun x : ℝ => (x : ℂ))
      rw [hcmul]
    _ = z * w + 1 := by
      rw [integral_standardGaussian_complex_sq,
        integral_standardGaussian_complex_id]
      simp
      ring

/-- The coordinate factor for complex spectral parameters and real matrix
entries. -/
def ginibreComplexShiftedPermutationPairCoordinateFactor {n : ℕ}
    (z w : ℂ) (σ τ : Equiv.Perm (Fin n)) (i j : Fin n) (x : ℝ) : ℂ :=
  (if σ j = i then (if i = j then z - (x : ℂ) else -(x : ℂ)) else 1) *
    (if τ j = i then (if i = j then w - (x : ℂ) else -(x : ℂ)) else 1)

/-- Coordinate-product reconstruction for the complexified matrix. -/
theorem ginibreComplexShiftedPermutationPairCoordinateProduct {n : ℕ}
    (z w : ℂ) (σ τ : Equiv.Perm (Fin n)) (A : RSqMat n) :
    (∏ i, ∏ j,
      ginibreComplexShiftedPermutationPairCoordinateFactor z w σ τ i j (A i j)) =
      (∏ j,
        (Matrix.scalar (Fin n) z - A.map Complex.ofReal) (σ j) j) *
        ∏ j, (Matrix.scalar (Fin n) w - A.map Complex.ofReal) (τ j) j := by
  rw [Finset.prod_comm]
  simp_rw [ginibreComplexShiftedPermutationPairCoordinateFactor,
    Finset.prod_mul_distrib]
  simp [Matrix.scalar_apply, Matrix.diagonal_apply]
  congr 1
  · apply Finset.prod_congr rfl
    intro j hj
    by_cases h : σ j = j <;> simp [h, Matrix.diagonal_apply]
  · apply Finset.prod_congr rfl
    intro j hj
    by_cases h : τ j = j <;> simp [h, Matrix.diagonal_apply]

/-- Every complex shifted coordinate factor is integrable against the
standard real Gaussian law. -/
theorem integrable_ginibreComplexShiftedPermutationPairCoordinateFactor
    {n : ℕ} (z w : ℂ) (σ τ : Equiv.Perm (Fin n)) (i j : Fin n) :
    Integrable
      (ginibreComplexShiftedPermutationPairCoordinateFactor z w σ τ i j)
      (gaussianReal 0 1) := by
  change Integrable
    (fun x : ℝ =>
      (if σ j = i then
          (if i = j then z - (x : ℂ) else -(x : ℂ)) else 1) *
        (if τ j = i then
          (if i = j then w - (x : ℂ) else -(x : ℂ)) else 1))
    (gaussianReal 0 1)
  by_cases hij : i = j
  · subst i
    by_cases hσ : σ j = j <;> by_cases hτ : τ j = j
    · simpa [hσ, hτ] using
        integrable_standardGaussian_complex_sub_mul_sub z w
    · simpa [hσ, hτ] using
        (integrable_const (μ := gaussianReal 0 1) (c := z)).sub
          integrable_standardGaussian_complex_id
    · simpa [hσ, hτ] using
        (integrable_const (μ := gaussianReal 0 1) (c := w)).sub
          integrable_standardGaussian_complex_id
    · simpa [hσ, hτ] using
        (integrable_const (μ := gaussianReal 0 1) (c := (1 : ℂ)))
  · by_cases hσ : σ j = i <;> by_cases hτ : τ j = i
    · simpa [hσ, hτ, hij, neg_mul_neg, pow_two] using
        integrable_standardGaussian_complex_sq
    · have hneg : Integrable (fun x : ℝ => -(x : ℂ))
          (gaussianReal 0 1) := integrable_standardGaussian_complex_id.neg
      simpa [hσ, hτ, hij] using hneg
    · have hneg : Integrable (fun x : ℝ => -(x : ℂ))
          (gaussianReal 0 1) := integrable_standardGaussian_complex_id.neg
      simpa [hσ, hτ, hij] using hneg
    · simpa [hσ, hτ, hij] using
        (integrable_const (μ := gaussianReal 0 1) (c := (1 : ℂ)))

theorem integral_standardGaussian_complex_neg :
    (∫ x : ℝ, -(x : ℂ) ∂gaussianReal 0 1) = 0 := by
  rw [integral_neg (fun x : ℝ => (x : ℂ)),
    integral_standardGaussian_complex_id]
  simp

/-- Exact integral of one complex shifted coordinate factor. -/
theorem integral_ginibreComplexShiftedPermutationPairCoordinateFactor
    {n : ℕ} (z w : ℂ) (σ τ : Equiv.Perm (Fin n)) (i j : Fin n) :
    (∫ x : ℝ,
      ginibreComplexShiftedPermutationPairCoordinateFactor z w σ τ i j x
      ∂gaussianReal 0 1) =
      if σ j = i then
        if τ j = i then (if i = j then z * w + 1 else 1)
        else (if i = j then z else 0)
      else if τ j = i then (if i = j then w else 0) else 1 := by
  by_cases hij : i = j
  · subst i
    by_cases hσ : σ j = j <;> by_cases hτ : τ j = j
    · simp [ginibreComplexShiftedPermutationPairCoordinateFactor, hσ, hτ,
        integral_standardGaussian_complex_sub_mul_sub]
    · simp [ginibreComplexShiftedPermutationPairCoordinateFactor, hσ, hτ,
        integral_standardGaussian_complex_sub]
    · simp [ginibreComplexShiftedPermutationPairCoordinateFactor, hσ, hτ,
        integral_standardGaussian_complex_sub]
    · simp [ginibreComplexShiftedPermutationPairCoordinateFactor, hσ, hτ]
  · by_cases hσ : σ j = i <;> by_cases hτ : τ j = i
    · simpa [ginibreComplexShiftedPermutationPairCoordinateFactor, hσ, hτ,
        hij, neg_mul_neg, pow_two] using
        integral_standardGaussian_complex_sq
    · simpa [ginibreComplexShiftedPermutationPairCoordinateFactor, hσ, hτ,
        hij] using integral_standardGaussian_complex_neg
    · simpa [ginibreComplexShiftedPermutationPairCoordinateFactor, hσ, hτ,
        hij] using integral_standardGaussian_complex_neg
    · simp [ginibreComplexShiftedPermutationPairCoordinateFactor, hσ, hτ, hij]

/-- Diagonal specialization of the one-coordinate complex integral. -/
theorem integral_ginibreComplexShiftedPermutationPairCoordinateFactor_self
    {n : ℕ} (z w : ℂ) (σ : Equiv.Perm (Fin n)) (i j : Fin n) :
    (∫ x : ℝ,
      ginibreComplexShiftedPermutationPairCoordinateFactor z w σ σ i j x
      ∂gaussianReal 0 1) =
      if σ j = i then (if i = j then 1 + z * w else 1) else 1 := by
  rw [integral_ginibreComplexShiftedPermutationPairCoordinateFactor]
  by_cases hij : i = j
  · subst i
    by_cases h : σ j = j <;> simp [h] <;> ring
  · by_cases h : σ j = i <;> simp [h, hij]

/-- Product of all complex coordinate-factor integrals. -/
theorem prod_integral_ginibreComplexShiftedPermutationPairCoordinateFactor
    {n : ℕ} (z w : ℂ) (σ τ : Equiv.Perm (Fin n)) :
    (∏ i, ∏ j,
      ∫ x : ℝ,
        ginibreComplexShiftedPermutationPairCoordinateFactor z w σ τ i j x
        ∂gaussianReal 0 1) =
      if σ = τ then
        (1 + z * w) ^ (ginibrePermutationFixedPoints σ).card
      else 0 := by
  by_cases hστ : σ = τ
  · subst τ
    rw [if_pos rfl]
    simp_rw [
      integral_ginibreComplexShiftedPermutationPairCoordinateFactor_self]
    rw [Finset.prod_comm]
    have hinner (j : Fin n) :
        (∏ i : Fin n,
          if σ j = i then (if i = j then 1 + z * w else 1) else 1) =
          if σ j = j then 1 + z * w else 1 := by
      simpa [eq_comm] using
        (Finset.prod_ite_eq' (Finset.univ : Finset (Fin n)) (σ j)
          (fun i => if i = j then 1 + z * w else 1))
    simp_rw [hinner]
    rw [← Finset.prod_filter]
    simp [ginibrePermutationFixedPoints, Finset.prod_const]
  · simp_rw [integral_ginibreComplexShiftedPermutationPairCoordinateFactor]
    rw [if_neg hστ]
    have hex : ∃ j : Fin n, σ j ≠ τ j := by
      by_contra h
      push_neg at h
      exact hστ (Equiv.ext h)
    obtain ⟨j, hj⟩ := hex
    by_cases hdiag : σ j = j
    · have hτdiag : τ j ≠ j := fun h => hj (hdiag.trans h.symm)
      have hjτ : j ≠ τ j := Ne.symm hτdiag
      apply Finset.prod_eq_zero (Finset.mem_univ (τ j))
      apply Finset.prod_eq_zero (Finset.mem_univ j)
      simp [hdiag, hτdiag, hjτ]
    · have hrev : τ j ≠ σ j := Ne.symm hj
      apply Finset.prod_eq_zero (Finset.mem_univ (σ j))
      apply Finset.prod_eq_zero (Finset.mem_univ j)
      simp [hdiag, hrev]

/-- The complex permutation sign in the Leibniz expansion. -/
def ginibrePermutationSignComplex {n : ℕ}
    (σ : Equiv.Perm (Fin n)) : ℂ :=
  Complex.ofReal (ginibrePermutationSignReal σ)

/-- A complex permutation sign squares to one. -/
theorem ginibrePermutationSignComplex_mul_self {n : ℕ}
    (σ : Equiv.Perm (Fin n)) :
    ginibrePermutationSignComplex σ * ginibrePermutationSignComplex σ = 1 := by
  rw [ginibrePermutationSignComplex, ← Complex.ofReal_mul,
    ginibrePermutationSignReal_mul_self]
  simp

/-- A signed permutation term in the complex shifted determinant. -/
def ginibreComplexShiftedDeterminantPermutationTerm {n : ℕ}
    (z : ℂ) (σ : Equiv.Perm (Fin n)) (A : RSqMat n) : ℂ :=
  ginibrePermutationSignComplex σ *
    ∏ j, (Matrix.scalar (Fin n) z - A.map Complex.ofReal) (σ j) j

/-- Leibniz expansion of the complex shifted determinant. -/
theorem ginibre_complexShiftedDet_eq_sum_permutationTerms {n : ℕ}
    (z : ℂ) (A : RSqMat n) :
    (Matrix.scalar (Fin n) z - A.map Complex.ofReal).det =
      ∑ σ : Equiv.Perm (Fin n),
        ginibreComplexShiftedDeterminantPermutationTerm z σ A := by
  simpa [ginibreComplexShiftedDeterminantPermutationTerm,
    ginibrePermutationSignComplex, ginibrePermutationSignReal] using
      Matrix.det_apply' (Matrix.scalar (Fin n) z - A.map Complex.ofReal)

/-- Complex-valued constant sum over permutations fixing `S`. -/
theorem sum_indicator_ginibrePermutationsFixing_complex {n : ℕ}
    (S : Finset (Fin n)) (c : ℂ) :
    (∑ σ : Equiv.Perm (Fin n),
      if (∀ j, j ∈ S → σ j = j) then c else 0) =
      ((n - S.card).factorial : ℂ) * c := by
  let p : Equiv.Perm (Fin n) → Prop :=
    fun σ => ∀ j, j ∈ S → σ j = j
  change (∑ σ : Equiv.Perm (Fin n), if p σ then c else 0) = _
  rw [← Finset.sum_filter]
  have hsum : (∑ σ ∈ Finset.univ.filter p, c) =
      ∑ _σ : ginibrePermutationsFixing S, c := by
    unfold ginibrePermutationsFixing
    exact Finset.sum_subtype (Finset.univ.filter p) (by
      intro σ
      simp [p]) (fun _ => c)
  rw [hsum]
  simp [card_ginibrePermutationsFixing, nsmul_eq_mul]

/-- Complex binomial expansion indexed by subsets of the fixed-point set. -/
theorem one_add_pow_card_ginibrePermutationFixedPoints_complex {n : ℕ}
    (t : ℂ) (σ : Equiv.Perm (Fin n)) :
    (1 + t) ^ (ginibrePermutationFixedPoints σ).card =
      ∑ S ∈ (ginibrePermutationFixedPoints σ).powerset, t ^ S.card := by
  calc
    (1 + t) ^ (ginibrePermutationFixedPoints σ).card =
        ∏ _j ∈ ginibrePermutationFixedPoints σ, (1 + t) := by
      simp [Finset.prod_const]
    _ = ∑ S ∈ (ginibrePermutationFixedPoints σ).powerset,
          ∏ _j ∈ S, t := by
      simpa using Finset.prod_one_add
        (f := fun _j : Fin n => t) (ginibrePermutationFixedPoints σ)
    _ = ∑ S ∈ (ginibrePermutationFixedPoints σ).powerset,
          t ^ S.card := by
      apply Finset.sum_congr rfl
      intro S hS
      simp [Finset.prod_const]

/-- Extend a complex subset sum over fixed points to all subsets. -/
theorem sum_powerset_ginibrePermutationFixedPoints_eq_indicator_complex
    {n : ℕ} (t : ℂ) (σ : Equiv.Perm (Fin n)) :
    (∑ S ∈ (ginibrePermutationFixedPoints σ).powerset, t ^ S.card) =
      ∑ S ∈ (Finset.univ : Finset (Fin n)).powerset,
        if S ⊆ ginibrePermutationFixedPoints σ then t ^ S.card else 0 := by
  have hfilter :
      ((Finset.univ : Finset (Fin n)).powerset.filter
        (fun S => S ⊆ ginibrePermutationFixedPoints σ)) =
        (ginibrePermutationFixedPoints σ).powerset := by
    ext S
    simp
  rw [← Finset.sum_filter]
  rw [hfilter]

/-- Complex fixed-point enumerator as a subset-weighted factorial sum. -/
theorem sum_pow_card_ginibrePermutationFixedPoints_eq_powerset_complex
    (n : ℕ) (t : ℂ) :
    (∑ σ : Equiv.Perm (Fin n),
      (1 + t) ^ (ginibrePermutationFixedPoints σ).card) =
      ∑ S ∈ (Finset.univ : Finset (Fin n)).powerset,
        ((n - S.card).factorial : ℂ) * t ^ S.card := by
  simp_rw [one_add_pow_card_ginibrePermutationFixedPoints_complex,
    sum_powerset_ginibrePermutationFixedPoints_eq_indicator_complex]
  rw [Finset.sum_comm]
  apply Finset.sum_congr rfl
  intro S hS
  have hfix (σ : Equiv.Perm (Fin n)) :
      S ⊆ ginibrePermutationFixedPoints σ ↔
        ∀ j, j ∈ S → σ j = j := by
    simp [Finset.subset_iff]
  simp_rw [hfix]
  exact sum_indicator_ginibrePermutationsFixing_complex S (t ^ S.card)

/-- Complex fixed-point enumerator grouped by subset cardinality. -/
theorem sum_pow_card_ginibrePermutationFixedPoints_eq_range_complex
    (n : ℕ) (t : ℂ) :
    (∑ σ : Equiv.Perm (Fin n),
      (1 + t) ^ (ginibrePermutationFixedPoints σ).card) =
      ∑ k ∈ Finset.range (n + 1),
        (n.choose k : ℂ) * ((n - k).factorial : ℂ) * t ^ k := by
  rw [sum_pow_card_ginibrePermutationFixedPoints_eq_powerset_complex]
  have h := Finset.sum_powerset_apply_card
    (x := (Finset.univ : Finset (Fin n)))
    (fun k => ((n - k).factorial : ℂ) * t ^ k)
  simpa only [Finset.card_univ, Fintype.card_fin, nsmul_eq_mul,
    Nat.cast_ofNat, mul_assoc] using h

/-- Complex-cast form of `choose(n,k) (n-k)! = n!/k!`. -/
theorem cast_choose_mul_factorial_sub_eq_factorial_div_complex
    {n k : ℕ} (hk : k ≤ n) :
    (n.choose k : ℂ) * ((n - k).factorial : ℂ) =
      (n.factorial : ℂ) / (k.factorial : ℂ) := by
  have h := congrArg Complex.ofReal
    (cast_choose_mul_factorial_sub_eq_factorial_div (n := n) (k := k) hk)
  norm_num at h ⊢
  exact h

/-- Closed form of the complex symmetric-group fixed-point enumerator. -/
theorem sum_pow_card_ginibrePermutationFixedPoints_complex
    (n : ℕ) (t : ℂ) :
    (∑ σ : Equiv.Perm (Fin n),
      (1 + t) ^ (ginibrePermutationFixedPoints σ).card) =
      (n.factorial : ℂ) *
        ∑ k ∈ Finset.range (n + 1),
          t ^ k / (k.factorial : ℂ) := by
  rw [sum_pow_card_ginibrePermutationFixedPoints_eq_range_complex]
  rw [Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro k hk
  have hkn : k ≤ n := Nat.le_of_lt_succ (Finset.mem_range.1 hk)
  rw [cast_choose_mul_factorial_sub_eq_factorial_div_complex hkn]
  ring

end NumStability

end
