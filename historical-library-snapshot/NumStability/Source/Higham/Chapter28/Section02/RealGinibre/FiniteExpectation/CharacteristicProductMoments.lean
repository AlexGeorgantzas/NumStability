import NumStability.Analysis.LinearOperators.Jordan.NormalForm.PrimaryDecomposition
import NumStability.Source.Higham.Chapter04.Problem04
import NumStability.Source.Higham.Chapter28.Section02.RealGinibre.FiniteExpectation.GinibreCharacteristicProduct
import NumStability.Source.Higham.Chapter28.Section02.RealGinibre.ProbabilityLaw.ProductLaw
import NumStability.Source.Higham.Chapter28.Section02.RealGinibre.SignedIncidence.GinibreSignedScalar
import NumStability.Upstream.Lindemann.MonoidAlgebraCompat

/-!
Relocated from the historical wave owners NumStability.Algorithms.TestMatrices.Higham28GinibreCharacteristicProduct, NumStability.Algorithms.TestMatrices.Higham28GinibreSignedScalar under the R09/R10 completion waves; source-tier destination per the reviewed route ledger.
-/

noncomputable section

namespace NumStability

open Matrix MeasureTheory ProbabilityTheory

open scoped BigOperators

private local instance ginibreCharacteristicProductMeasurableSpace (n : ℕ) :
    MeasurableSpace (RSqMat n) := MeasurableSpace.pi

private local instance ginibreCharacteristicProductSigmaFiniteRow (n : ℕ) :
    SigmaFinite (Measure.pi (fun _ : Fin n => gaussianReal 0 1)) := by
  infer_instance

/-- An arbitrary product of one-coordinate functions factors under the
independent-entry real-Ginibre law. -/
theorem integral_realGinibre_coordinateProduct
    (n : ℕ) (f : Fin n → Fin n → ℝ → ℝ) :
    (∫ A : RSqMat n, ∏ i, ∏ j, f i j (A i j) ∂realGinibreMeasure n) =
      ∏ i, ∏ j, ∫ x : ℝ, f i j x ∂gaussianReal 0 1 := by
  unfold realGinibreMeasure
  change
    (∫ A : (i : Fin n) → (Fin n → ℝ),
        ∏ i, ∏ j, f i j (A i j)
      ∂Measure.pi (fun _ : Fin n =>
        Measure.pi (fun _ : Fin n => gaussianReal 0 1))) = _
  calc
    (∫ A : (i : Fin n) → (Fin n → ℝ),
        ∏ i, ∏ j, f i j (A i j)
      ∂Measure.pi (fun _ : Fin n =>
        Measure.pi (fun _ : Fin n => gaussianReal 0 1))) =
        ∏ i : Fin n,
          ∫ row : Fin n → ℝ, ∏ j, f i j (row j)
            ∂Measure.pi (fun _ : Fin n => gaussianReal 0 1) :=
      integral_fintype_prod_eq_prod
        (fun i (row : Fin n → ℝ) => ∏ j, f i j (row j))
    _ = ∏ i, ∏ j, ∫ x : ℝ, f i j x ∂gaussianReal 0 1 := by
      apply Finset.prod_congr rfl
      intro i hi
      exact integral_fintype_prod_eq_prod (fun j => f i j)

/-- A product of two determinant permutation monomials is integrable under
the real-Ginibre law. -/
theorem integrable_ginibrePermutationPairMonomial {n : ℕ}
    (σ τ : Equiv.Perm (Fin n)) :
    Integrable
      (fun A : RSqMat n =>
        (∏ j, A (σ j) j) * ∏ j, A (τ j) j)
      (realGinibreMeasure n) := by
  have hcoord : Integrable
      (fun A : RSqMat n =>
        ∏ i, ∏ j,
          ginibrePermutationPairCoordinateFactor σ τ i j (A i j))
      (realGinibreMeasure n) := by
    unfold realGinibreMeasure
    refine Integrable.fintype_prod
      (f := fun i (row : Fin n → ℝ) =>
        ∏ j, ginibrePermutationPairCoordinateFactor σ τ i j (row j))
      (μ := fun _ : Fin n =>
        Measure.pi (fun _ : Fin n => gaussianReal 0 1)) (fun i => ?_)
    exact Integrable.fintype_prod
      (f := fun j (x : ℝ) => ginibrePermutationPairCoordinateFactor σ τ i j x)
      (μ := fun _ : Fin n => gaussianReal 0 1)
      (fun j => integrable_ginibrePermutationPairCoordinateFactor σ τ i j)
  apply hcoord.congr
  filter_upwards with A
  exact ginibrePermutationPairCoordinateProduct σ τ A

/-- Two determinant permutation monomials are orthonormal under the
independent standard-Gaussian entry law. -/
theorem integral_ginibrePermutationPairMonomial {n : ℕ}
    (σ τ : Equiv.Perm (Fin n)) :
    (∫ A : RSqMat n,
        (∏ j, A (σ j) j) * ∏ j, A (τ j) j
      ∂realGinibreMeasure n) =
      if σ = τ then 1 else 0 := by
  calc
    (∫ A : RSqMat n,
        (∏ j, A (σ j) j) * ∏ j, A (τ j) j
      ∂realGinibreMeasure n) =
        ∫ A : RSqMat n,
          ∏ i, ∏ j,
            ginibrePermutationPairCoordinateFactor σ τ i j (A i j)
          ∂realGinibreMeasure n := by
            apply integral_congr_ae
            filter_upwards with A
            exact (ginibrePermutationPairCoordinateProduct σ τ A).symm
    _ = ∏ i, ∏ j,
          ∫ x : ℝ, ginibrePermutationPairCoordinateFactor σ τ i j x
            ∂gaussianReal 0 1 :=
      integral_realGinibre_coordinateProduct n
        (ginibrePermutationPairCoordinateFactor σ τ)
    _ = if σ = τ then 1 else 0 :=
      prod_integral_ginibrePermutationPairCoordinateFactor σ τ

/-- Products of signed determinant permutation terms are integrable. -/
theorem integrable_ginibreDeterminantPermutationTerm_mul {n : ℕ}
    (σ τ : Equiv.Perm (Fin n)) :
    Integrable
      (fun A : RSqMat n =>
        ginibreDeterminantPermutationTerm σ A *
          ginibreDeterminantPermutationTerm τ A)
      (realGinibreMeasure n) := by
  have h := (integrable_ginibrePermutationPairMonomial σ τ).const_mul
    (ginibrePermutationSignReal σ * ginibrePermutationSignReal τ)
  apply h.congr
  filter_upwards with A
  simp only [ginibreDeterminantPermutationTerm]
  ring

/-- Signed determinant permutation terms remain orthogonal; on the diagonal
their integral is the product of the two signs. -/
theorem integral_ginibreDeterminantPermutationTerm_mul {n : ℕ}
    (σ τ : Equiv.Perm (Fin n)) :
    (∫ A : RSqMat n,
        ginibreDeterminantPermutationTerm σ A *
          ginibreDeterminantPermutationTerm τ A
      ∂realGinibreMeasure n) =
      ginibrePermutationSignReal σ * ginibrePermutationSignReal τ *
        (if σ = τ then 1 else 0) := by
  calc
    (∫ A : RSqMat n,
        ginibreDeterminantPermutationTerm σ A *
          ginibreDeterminantPermutationTerm τ A
      ∂realGinibreMeasure n) =
        ∫ A : RSqMat n,
          (ginibrePermutationSignReal σ * ginibrePermutationSignReal τ) *
            ((∏ j, A (σ j) j) * ∏ j, A (τ j) j)
          ∂realGinibreMeasure n := by
            apply integral_congr_ae
            filter_upwards with A
            simp only [ginibreDeterminantPermutationTerm]
            ring
    _ = (ginibrePermutationSignReal σ * ginibrePermutationSignReal τ) *
          ∫ A : RSqMat n,
            (∏ j, A (σ j) j) * ∏ j, A (τ j) j
            ∂realGinibreMeasure n := by
      rw [integral_const_mul]
    _ = ginibrePermutationSignReal σ * ginibrePermutationSignReal τ *
          (if σ = τ then 1 else 0) := by
      rw [integral_ginibrePermutationPairMonomial]

/-- The exact real-Ginibre determinant second moment:
`𝔼[(det G)²] = n!`. -/
theorem integral_realGinibre_det_sq (n : ℕ) :
    (∫ A : RSqMat n, A.det ^ 2 ∂realGinibreMeasure n) =
      (n.factorial : ℝ) := by
  have hterm (σ τ : Equiv.Perm (Fin n)) :
      Integrable
        (fun A : RSqMat n =>
          ginibreDeterminantPermutationTerm σ A *
            ginibreDeterminantPermutationTerm τ A)
        (realGinibreMeasure n) :=
    integrable_ginibreDeterminantPermutationTerm_mul σ τ
  have hinner (σ : Equiv.Perm (Fin n)) :
      Integrable
        (fun A : RSqMat n =>
          ∑ τ : Equiv.Perm (Fin n),
            ginibreDeterminantPermutationTerm σ A *
              ginibreDeterminantPermutationTerm τ A)
        (realGinibreMeasure n) :=
    integrable_finset_sum _ (fun τ _ => hterm σ τ)
  calc
    (∫ A : RSqMat n, A.det ^ 2 ∂realGinibreMeasure n) =
        ∫ A : RSqMat n,
          ∑ σ : Equiv.Perm (Fin n),
            ∑ τ : Equiv.Perm (Fin n),
              ginibreDeterminantPermutationTerm σ A *
                ginibreDeterminantPermutationTerm τ A
          ∂realGinibreMeasure n := by
            apply integral_congr_ae
            filter_upwards with A
            rw [pow_two, ginibre_det_eq_sum_permutationTerms,
              Finset.sum_mul]
            simp_rw [Finset.mul_sum]
    _ = ∑ σ : Equiv.Perm (Fin n),
          ∫ A : RSqMat n,
            ∑ τ : Equiv.Perm (Fin n),
              ginibreDeterminantPermutationTerm σ A *
                ginibreDeterminantPermutationTerm τ A
            ∂realGinibreMeasure n := by
      exact integral_finset_sum _ (fun σ _ => hinner σ)
    _ = ∑ σ : Equiv.Perm (Fin n),
          ∑ τ : Equiv.Perm (Fin n),
            ∫ A : RSqMat n,
              ginibreDeterminantPermutationTerm σ A *
                ginibreDeterminantPermutationTerm τ A
              ∂realGinibreMeasure n := by
      apply Finset.sum_congr rfl
      intro σ hσ
      exact integral_finset_sum _ (fun τ _ => hterm σ τ)
    _ = ∑ σ : Equiv.Perm (Fin n),
          ∑ τ : Equiv.Perm (Fin n),
            ginibrePermutationSignReal σ * ginibrePermutationSignReal τ *
              (if σ = τ then 1 else 0) := by
      apply Finset.sum_congr rfl
      intro σ hσ
      apply Finset.sum_congr rfl
      intro τ hτ
      exact integral_ginibreDeterminantPermutationTerm_mul σ τ
    _ = ∑ σ : Equiv.Perm (Fin n),
          ginibrePermutationSignReal σ * ginibrePermutationSignReal σ := by
      apply Finset.sum_congr rfl
      intro σ hσ
      simp
    _ = ∑ _σ : Equiv.Perm (Fin n), (1 : ℝ) := by
      apply Finset.sum_congr rfl
      intro σ hσ
      exact ginibrePermutationSignReal_mul_self σ
    _ = (n.factorial : ℝ) := by
      simp [Fintype.card_perm]

/-- A product of two shifted determinant permutation monomials is
integrable. -/
theorem integrable_ginibreShiftedPermutationPairMonomial {n : ℕ}
    (z w : ℝ) (σ τ : Equiv.Perm (Fin n)) :
    Integrable
      (fun A : RSqMat n =>
        (∏ j, (z • (1 : RSqMat n) - A) (σ j) j) *
          ∏ j, (w • (1 : RSqMat n) - A) (τ j) j)
      (realGinibreMeasure n) := by
  have hcoord : Integrable
      (fun A : RSqMat n =>
        ∏ i, ∏ j,
          ginibreShiftedPermutationPairCoordinateFactor z w σ τ i j (A i j))
      (realGinibreMeasure n) := by
    unfold realGinibreMeasure
    refine Integrable.fintype_prod
      (f := fun i (row : Fin n → ℝ) =>
        ∏ j, ginibreShiftedPermutationPairCoordinateFactor z w σ τ i j (row j))
      (μ := fun _ : Fin n =>
        Measure.pi (fun _ : Fin n => gaussianReal 0 1)) (fun i => ?_)
    exact Integrable.fintype_prod
      (f := fun j (x : ℝ) =>
        ginibreShiftedPermutationPairCoordinateFactor z w σ τ i j x)
      (μ := fun _ : Fin n => gaussianReal 0 1)
      (fun j =>
        integrable_ginibreShiftedPermutationPairCoordinateFactor z w σ τ i j)
  apply hcoord.congr
  filter_upwards with A
  exact ginibreShiftedPermutationPairCoordinateProduct z w σ τ A

/-- Exact shifted permutation-monomial integral. -/
theorem integral_ginibreShiftedPermutationPairMonomial {n : ℕ}
    (z w : ℝ) (σ τ : Equiv.Perm (Fin n)) :
    (∫ A : RSqMat n,
        (∏ j, (z • (1 : RSqMat n) - A) (σ j) j) *
          ∏ j, (w • (1 : RSqMat n) - A) (τ j) j
      ∂realGinibreMeasure n) =
      if σ = τ then
        (1 + z * w) ^ (ginibrePermutationFixedPoints σ).card
      else 0 := by
  calc
    (∫ A : RSqMat n,
        (∏ j, (z • (1 : RSqMat n) - A) (σ j) j) *
          ∏ j, (w • (1 : RSqMat n) - A) (τ j) j
      ∂realGinibreMeasure n) =
        ∫ A : RSqMat n,
          ∏ i, ∏ j,
            ginibreShiftedPermutationPairCoordinateFactor z w σ τ i j (A i j)
          ∂realGinibreMeasure n := by
            apply integral_congr_ae
            filter_upwards with A
            exact
              (ginibreShiftedPermutationPairCoordinateProduct z w σ τ A).symm
    _ = ∏ i, ∏ j,
          ∫ x : ℝ,
            ginibreShiftedPermutationPairCoordinateFactor z w σ τ i j x
            ∂gaussianReal 0 1 :=
      integral_realGinibre_coordinateProduct n
        (ginibreShiftedPermutationPairCoordinateFactor z w σ τ)
    _ = if σ = τ then
          (1 + z * w) ^ (ginibrePermutationFixedPoints σ).card
        else 0 :=
      prod_integral_ginibreShiftedPermutationPairCoordinateFactor z w σ τ

/-- Products of shifted signed determinant terms are integrable. -/
theorem integrable_ginibreShiftedDeterminantPermutationTerm_mul {n : ℕ}
    (z w : ℝ) (σ τ : Equiv.Perm (Fin n)) :
    Integrable
      (fun A : RSqMat n =>
        ginibreShiftedDeterminantPermutationTerm z σ A *
          ginibreShiftedDeterminantPermutationTerm w τ A)
      (realGinibreMeasure n) := by
  have h := (integrable_ginibreShiftedPermutationPairMonomial z w σ τ).const_mul
    (ginibrePermutationSignReal σ * ginibrePermutationSignReal τ)
  apply h.congr
  filter_upwards with A
  simp only [ginibreShiftedDeterminantPermutationTerm]
  ring

/-- Exact integral of two shifted signed determinant terms. -/
theorem integral_ginibreShiftedDeterminantPermutationTerm_mul {n : ℕ}
    (z w : ℝ) (σ τ : Equiv.Perm (Fin n)) :
    (∫ A : RSqMat n,
        ginibreShiftedDeterminantPermutationTerm z σ A *
          ginibreShiftedDeterminantPermutationTerm w τ A
      ∂realGinibreMeasure n) =
      ginibrePermutationSignReal σ * ginibrePermutationSignReal τ *
        (if σ = τ then
          (1 + z * w) ^ (ginibrePermutationFixedPoints σ).card
        else 0) := by
  calc
    (∫ A : RSqMat n,
        ginibreShiftedDeterminantPermutationTerm z σ A *
          ginibreShiftedDeterminantPermutationTerm w τ A
      ∂realGinibreMeasure n) =
        ∫ A : RSqMat n,
          (ginibrePermutationSignReal σ * ginibrePermutationSignReal τ) *
            ((∏ j, (z • (1 : RSqMat n) - A) (σ j) j) *
              ∏ j, (w • (1 : RSqMat n) - A) (τ j) j)
          ∂realGinibreMeasure n := by
            apply integral_congr_ae
            filter_upwards with A
            simp only [ginibreShiftedDeterminantPermutationTerm]
            ring
    _ = (ginibrePermutationSignReal σ * ginibrePermutationSignReal τ) *
          ∫ A : RSqMat n,
            (∏ j, (z • (1 : RSqMat n) - A) (σ j) j) *
              ∏ j, (w • (1 : RSqMat n) - A) (τ j) j
            ∂realGinibreMeasure n := by
      rw [integral_const_mul]
    _ = ginibrePermutationSignReal σ * ginibrePermutationSignReal τ *
          (if σ = τ then
            (1 + z * w) ^ (ginibrePermutationFixedPoints σ).card
          else 0) := by
      rw [integral_ginibreShiftedPermutationPairMonomial]

/-- The two-shift real-Ginibre characteristic product is the fixed-point
enumerator of the symmetric group. -/
theorem integral_realGinibre_characteristicProduct_eq_sum_fixedPoints
    (n : ℕ) (z w : ℝ) :
    (∫ A : RSqMat n,
        (z • (1 : RSqMat n) - A).det *
          (w • (1 : RSqMat n) - A).det
      ∂realGinibreMeasure n) =
      ∑ σ : Equiv.Perm (Fin n),
        (1 + z * w) ^ (ginibrePermutationFixedPoints σ).card := by
  have hterm (σ τ : Equiv.Perm (Fin n)) :
      Integrable
        (fun A : RSqMat n =>
          ginibreShiftedDeterminantPermutationTerm z σ A *
            ginibreShiftedDeterminantPermutationTerm w τ A)
        (realGinibreMeasure n) :=
    integrable_ginibreShiftedDeterminantPermutationTerm_mul z w σ τ
  have hinner (σ : Equiv.Perm (Fin n)) :
      Integrable
        (fun A : RSqMat n =>
          ∑ τ : Equiv.Perm (Fin n),
            ginibreShiftedDeterminantPermutationTerm z σ A *
              ginibreShiftedDeterminantPermutationTerm w τ A)
        (realGinibreMeasure n) :=
    integrable_finset_sum _ (fun τ _ => hterm σ τ)
  calc
    (∫ A : RSqMat n,
        (z • (1 : RSqMat n) - A).det *
          (w • (1 : RSqMat n) - A).det
      ∂realGinibreMeasure n) =
        ∫ A : RSqMat n,
          ∑ σ : Equiv.Perm (Fin n),
            ∑ τ : Equiv.Perm (Fin n),
              ginibreShiftedDeterminantPermutationTerm z σ A *
                ginibreShiftedDeterminantPermutationTerm w τ A
          ∂realGinibreMeasure n := by
            apply integral_congr_ae
            filter_upwards with A
            rw [ginibre_shiftedDet_eq_sum_permutationTerms,
              ginibre_shiftedDet_eq_sum_permutationTerms,
              Finset.sum_mul]
            simp_rw [Finset.mul_sum]
    _ = ∑ σ : Equiv.Perm (Fin n),
          ∫ A : RSqMat n,
            ∑ τ : Equiv.Perm (Fin n),
              ginibreShiftedDeterminantPermutationTerm z σ A *
                ginibreShiftedDeterminantPermutationTerm w τ A
            ∂realGinibreMeasure n := by
      exact integral_finset_sum _ (fun σ _ => hinner σ)
    _ = ∑ σ : Equiv.Perm (Fin n),
          ∑ τ : Equiv.Perm (Fin n),
            ∫ A : RSqMat n,
              ginibreShiftedDeterminantPermutationTerm z σ A *
                ginibreShiftedDeterminantPermutationTerm w τ A
              ∂realGinibreMeasure n := by
      apply Finset.sum_congr rfl
      intro σ hσ
      exact integral_finset_sum _ (fun τ _ => hterm σ τ)
    _ = ∑ σ : Equiv.Perm (Fin n),
          ∑ τ : Equiv.Perm (Fin n),
            ginibrePermutationSignReal σ * ginibrePermutationSignReal τ *
              (if σ = τ then
                (1 + z * w) ^ (ginibrePermutationFixedPoints σ).card
              else 0) := by
      apply Finset.sum_congr rfl
      intro σ hσ
      apply Finset.sum_congr rfl
      intro τ hτ
      exact integral_ginibreShiftedDeterminantPermutationTerm_mul z w σ τ
    _ = ∑ σ : Equiv.Perm (Fin n),
          ginibrePermutationSignReal σ * ginibrePermutationSignReal σ *
            (1 + z * w) ^ (ginibrePermutationFixedPoints σ).card := by
      apply Finset.sum_congr rfl
      intro σ hσ
      simp
    _ = ∑ σ : Equiv.Perm (Fin n),
          (1 + z * w) ^ (ginibrePermutationFixedPoints σ).card := by
      apply Finset.sum_congr rfl
      intro σ hσ
      rw [ginibrePermutationSignReal_mul_self, one_mul]

/-- Exact two-point real-Ginibre characteristic-polynomial product:

`𝔼[det(zI-G) det(wI-G)] = n! ∑_{k=0}^n (zw)^k/k!`.
-/
theorem integral_realGinibre_characteristicProduct
    (n : ℕ) (z w : ℝ) :
    (∫ A : RSqMat n,
        (z • (1 : RSqMat n) - A).det *
          (w • (1 : RSqMat n) - A).det
      ∂realGinibreMeasure n) =
      (n.factorial : ℝ) *
        ∑ k ∈ Finset.range (n + 1),
          (z * w) ^ k / (k.factorial : ℝ) := by
  rw [integral_realGinibre_characteristicProduct_eq_sum_fixedPoints]
  exact sum_pow_card_ginibrePermutationFixedPoints n (z * w)

/-- The characteristic-product integrand is integrable for every pair of
real spectral parameters.  This is exposed separately from its integral so
that later Fubini arguments can use the fixed-parameter sections. -/
theorem integrable_realGinibre_characteristicProduct
    (n : ℕ) (z w : ℝ) :
    Integrable
      (fun A : RSqMat n =>
        (z • (1 : RSqMat n) - A).det *
          (w • (1 : RSqMat n) - A).det)
      (realGinibreMeasure n) := by
  have hterm (σ τ : Equiv.Perm (Fin n)) :
      Integrable
        (fun A : RSqMat n =>
          ginibreShiftedDeterminantPermutationTerm z σ A *
            ginibreShiftedDeterminantPermutationTerm w τ A)
        (realGinibreMeasure n) :=
    integrable_ginibreShiftedDeterminantPermutationTerm_mul z w σ τ
  have hinner (σ : Equiv.Perm (Fin n)) :
      Integrable
        (fun A : RSqMat n =>
          ∑ τ : Equiv.Perm (Fin n),
            ginibreShiftedDeterminantPermutationTerm z σ A *
              ginibreShiftedDeterminantPermutationTerm w τ A)
        (realGinibreMeasure n) :=
    integrable_finset_sum _ (fun τ _ => hterm σ τ)
  have hsum : Integrable
      (fun A : RSqMat n =>
        ∑ σ : Equiv.Perm (Fin n),
          ∑ τ : Equiv.Perm (Fin n),
            ginibreShiftedDeterminantPermutationTerm z σ A *
              ginibreShiftedDeterminantPermutationTerm w τ A)
      (realGinibreMeasure n) :=
    integrable_finset_sum _ (fun σ _ => hinner σ)
  apply hsum.congr
  filter_upwards with A
  rw [ginibre_shiftedDet_eq_sum_permutationTerms,
    ginibre_shiftedDet_eq_sum_permutationTerms, Finset.sum_mul]
  simp_rw [Finset.mul_sum]

/-- Fixed incidence-form characteristic products are integrable. -/
theorem integrable_realGinibre_det_sub_smul_one_mul_det_sub_smul_one
    (n : ℕ) (u x : ℝ) :
    Integrable
      (fun A : RSqMat n =>
        (A - u • (1 : RSqMat n)).det *
          (A - x • (1 : RSqMat n)).det)
      (realGinibreMeasure n) := by
  apply (integrable_realGinibre_characteristicProduct n u x).congr
  filter_upwards with A
  exact (det_sub_smul_one_mul_det_sub_smul_one_eq n A u x).symm

/-- Incidence-form orientation of the two-point characteristic-product
identity.  This is the matrix integral appearing after the signed two-root
incidence formula; the two determinant sign changes cancel. -/
theorem integral_realGinibre_det_sub_smul_one_mul_det_sub_smul_one
    (n : ℕ) (u x : ℝ) :
    (∫ A : RSqMat n,
        (A - u • (1 : RSqMat n)).det *
          (A - x • (1 : RSqMat n)).det
      ∂realGinibreMeasure n) =
      (n.factorial : ℝ) *
        ∑ k ∈ Finset.range (n + 1),
          (u * x) ^ k / (k.factorial : ℝ) := by
  rw [show (fun A : RSqMat n =>
      (A - u • (1 : RSqMat n)).det *
        (A - x • (1 : RSqMat n)).det) =
      (fun A : RSqMat n =>
        (u • (1 : RSqMat n) - A).det *
          (x • (1 : RSqMat n) - A).det) by
    funext A
    exact det_sub_smul_one_mul_det_sub_smul_one_eq n A u x]
  exact integral_realGinibre_characteristicProduct n u x

/-- Complex-valued coordinate products also factor under the real-Ginibre
entry law. -/
theorem integral_realGinibre_coordinateProduct_complex
    (n : ℕ) (f : Fin n → Fin n → ℝ → ℂ) :
    (∫ A : RSqMat n, ∏ i, ∏ j, f i j (A i j) ∂realGinibreMeasure n) =
      ∏ i, ∏ j, ∫ x : ℝ, f i j x ∂gaussianReal 0 1 := by
  unfold realGinibreMeasure
  change
    (∫ A : (i : Fin n) → (Fin n → ℝ),
        ∏ i, ∏ j, f i j (A i j)
      ∂Measure.pi (fun _ : Fin n =>
        Measure.pi (fun _ : Fin n => gaussianReal 0 1))) = _
  calc
    (∫ A : (i : Fin n) → (Fin n → ℝ),
        ∏ i, ∏ j, f i j (A i j)
      ∂Measure.pi (fun _ : Fin n =>
        Measure.pi (fun _ : Fin n => gaussianReal 0 1))) =
        ∏ i : Fin n,
          ∫ row : Fin n → ℝ, ∏ j, f i j (row j)
            ∂Measure.pi (fun _ : Fin n => gaussianReal 0 1) := by
      exact integral_fintype_prod_eq_prod
        (𝕜 := ℂ) (ι := Fin n)
        (E := fun _ : Fin n => Fin n → ℝ)
        (μ := fun _ : Fin n =>
          Measure.pi (fun _ : Fin n => gaussianReal 0 1))
        (fun i (row : Fin n → ℝ) => ∏ j, f i j (row j))
    _ = ∏ i, ∏ j, ∫ x : ℝ, f i j x ∂gaussianReal 0 1 := by
      apply Finset.prod_congr rfl
      intro i hi
      exact integral_fintype_prod_eq_prod (𝕜 := ℂ) (fun j => f i j)

/-- A product of two complex shifted permutation monomials is integrable. -/
theorem integrable_ginibreComplexShiftedPermutationPairMonomial {n : ℕ}
    (z w : ℂ) (σ τ : Equiv.Perm (Fin n)) :
    Integrable
      (fun A : RSqMat n =>
        (∏ j,
          (Matrix.scalar (Fin n) z - A.map Complex.ofReal) (σ j) j) *
          ∏ j,
            (Matrix.scalar (Fin n) w - A.map Complex.ofReal) (τ j) j)
      (realGinibreMeasure n) := by
  have hcoord : Integrable
      (fun A : RSqMat n =>
        ∏ i, ∏ j,
          ginibreComplexShiftedPermutationPairCoordinateFactor
            z w σ τ i j (A i j))
      (realGinibreMeasure n) := by
    unfold realGinibreMeasure
    refine Integrable.fintype_prod
      (f := fun i (row : Fin n → ℝ) =>
        ∏ j,
          ginibreComplexShiftedPermutationPairCoordinateFactor
            z w σ τ i j (row j))
      (μ := fun _ : Fin n =>
        Measure.pi (fun _ : Fin n => gaussianReal 0 1)) (fun i => ?_)
    exact Integrable.fintype_prod
      (f := fun j (x : ℝ) =>
        ginibreComplexShiftedPermutationPairCoordinateFactor
          z w σ τ i j x)
      (μ := fun _ : Fin n => gaussianReal 0 1)
      (fun j =>
        integrable_ginibreComplexShiftedPermutationPairCoordinateFactor
          z w σ τ i j)
  apply hcoord.congr
  filter_upwards with A
  exact ginibreComplexShiftedPermutationPairCoordinateProduct z w σ τ A

/-- Exact integral of two complex shifted permutation monomials. -/
theorem integral_ginibreComplexShiftedPermutationPairMonomial {n : ℕ}
    (z w : ℂ) (σ τ : Equiv.Perm (Fin n)) :
    (∫ A : RSqMat n,
        (∏ j,
          (Matrix.scalar (Fin n) z - A.map Complex.ofReal) (σ j) j) *
          ∏ j,
            (Matrix.scalar (Fin n) w - A.map Complex.ofReal) (τ j) j
      ∂realGinibreMeasure n) =
      if σ = τ then
        (1 + z * w) ^ (ginibrePermutationFixedPoints σ).card
      else 0 := by
  calc
    (∫ A : RSqMat n,
        (∏ j,
          (Matrix.scalar (Fin n) z - A.map Complex.ofReal) (σ j) j) *
          ∏ j,
            (Matrix.scalar (Fin n) w - A.map Complex.ofReal) (τ j) j
      ∂realGinibreMeasure n) =
        ∫ A : RSqMat n,
          ∏ i, ∏ j,
            ginibreComplexShiftedPermutationPairCoordinateFactor
              z w σ τ i j (A i j)
          ∂realGinibreMeasure n := by
            apply integral_congr_ae
            filter_upwards with A
            exact
              (ginibreComplexShiftedPermutationPairCoordinateProduct
                z w σ τ A).symm
    _ = ∏ i, ∏ j,
          ∫ x : ℝ,
            ginibreComplexShiftedPermutationPairCoordinateFactor
              z w σ τ i j x
            ∂gaussianReal 0 1 :=
      integral_realGinibre_coordinateProduct_complex n
        (ginibreComplexShiftedPermutationPairCoordinateFactor z w σ τ)
    _ = if σ = τ then
          (1 + z * w) ^ (ginibrePermutationFixedPoints σ).card
        else 0 :=
      prod_integral_ginibreComplexShiftedPermutationPairCoordinateFactor
        z w σ τ

/-- Products of complex shifted signed determinant terms are integrable. -/
theorem integrable_ginibreComplexShiftedDeterminantPermutationTerm_mul
    {n : ℕ} (z w : ℂ) (σ τ : Equiv.Perm (Fin n)) :
    Integrable
      (fun A : RSqMat n =>
        ginibreComplexShiftedDeterminantPermutationTerm z σ A *
          ginibreComplexShiftedDeterminantPermutationTerm w τ A)
      (realGinibreMeasure n) := by
  have h :=
    (integrable_ginibreComplexShiftedPermutationPairMonomial z w σ τ).const_mul
      (ginibrePermutationSignComplex σ * ginibrePermutationSignComplex τ)
  apply h.congr
  filter_upwards with A
  simp only [ginibreComplexShiftedDeterminantPermutationTerm]
  ring

/-- Exact integral of two complex shifted signed determinant terms. -/
theorem integral_ginibreComplexShiftedDeterminantPermutationTerm_mul
    {n : ℕ} (z w : ℂ) (σ τ : Equiv.Perm (Fin n)) :
    (∫ A : RSqMat n,
        ginibreComplexShiftedDeterminantPermutationTerm z σ A *
          ginibreComplexShiftedDeterminantPermutationTerm w τ A
      ∂realGinibreMeasure n) =
      ginibrePermutationSignComplex σ * ginibrePermutationSignComplex τ *
        (if σ = τ then
          (1 + z * w) ^ (ginibrePermutationFixedPoints σ).card
        else 0) := by
  calc
    (∫ A : RSqMat n,
        ginibreComplexShiftedDeterminantPermutationTerm z σ A *
          ginibreComplexShiftedDeterminantPermutationTerm w τ A
      ∂realGinibreMeasure n) =
        ∫ A : RSqMat n,
          (ginibrePermutationSignComplex σ *
              ginibrePermutationSignComplex τ) *
            ((∏ j,
              (Matrix.scalar (Fin n) z - A.map Complex.ofReal) (σ j) j) *
              ∏ j,
                (Matrix.scalar (Fin n) w - A.map Complex.ofReal) (τ j) j)
          ∂realGinibreMeasure n := by
            apply integral_congr_ae
            filter_upwards with A
            simp only [ginibreComplexShiftedDeterminantPermutationTerm]
            ring
    _ = (ginibrePermutationSignComplex σ *
            ginibrePermutationSignComplex τ) *
          ∫ A : RSqMat n,
            (∏ j,
              (Matrix.scalar (Fin n) z - A.map Complex.ofReal) (σ j) j) *
              ∏ j,
                (Matrix.scalar (Fin n) w - A.map Complex.ofReal) (τ j) j
            ∂realGinibreMeasure n := by
      exact integral_const_mul
        (μ := realGinibreMeasure n)
        (ginibrePermutationSignComplex σ * ginibrePermutationSignComplex τ)
        (fun A : RSqMat n =>
          (∏ j,
            (Matrix.scalar (Fin n) z - A.map Complex.ofReal) (σ j) j) *
            ∏ j,
              (Matrix.scalar (Fin n) w - A.map Complex.ofReal) (τ j) j)
    _ = ginibrePermutationSignComplex σ * ginibrePermutationSignComplex τ *
          (if σ = τ then
            (1 + z * w) ^ (ginibrePermutationFixedPoints σ).card
          else 0) := by
      rw [integral_ginibreComplexShiftedPermutationPairMonomial]

/-- The two-shift complexified real-Ginibre characteristic product is the
same fixed-point enumerator. -/
theorem integral_realGinibre_characteristicProduct_complex_eq_sum_fixedPoints
    (n : ℕ) (z w : ℂ) :
    (∫ A : RSqMat n,
        (Matrix.scalar (Fin n) z - A.map Complex.ofReal).det *
          (Matrix.scalar (Fin n) w - A.map Complex.ofReal).det
      ∂realGinibreMeasure n) =
      ∑ σ : Equiv.Perm (Fin n),
        (1 + z * w) ^ (ginibrePermutationFixedPoints σ).card := by
  have hterm (σ τ : Equiv.Perm (Fin n)) :
      Integrable
        (fun A : RSqMat n =>
          ginibreComplexShiftedDeterminantPermutationTerm z σ A *
            ginibreComplexShiftedDeterminantPermutationTerm w τ A)
        (realGinibreMeasure n) :=
    integrable_ginibreComplexShiftedDeterminantPermutationTerm_mul z w σ τ
  have hinner (σ : Equiv.Perm (Fin n)) :
      Integrable
        (fun A : RSqMat n =>
          ∑ τ : Equiv.Perm (Fin n),
            ginibreComplexShiftedDeterminantPermutationTerm z σ A *
              ginibreComplexShiftedDeterminantPermutationTerm w τ A)
        (realGinibreMeasure n) :=
    integrable_finset_sum _ (fun τ _ => hterm σ τ)
  calc
    (∫ A : RSqMat n,
        (Matrix.scalar (Fin n) z - A.map Complex.ofReal).det *
          (Matrix.scalar (Fin n) w - A.map Complex.ofReal).det
      ∂realGinibreMeasure n) =
        ∫ A : RSqMat n,
          ∑ σ : Equiv.Perm (Fin n),
            ∑ τ : Equiv.Perm (Fin n),
              ginibreComplexShiftedDeterminantPermutationTerm z σ A *
                ginibreComplexShiftedDeterminantPermutationTerm w τ A
          ∂realGinibreMeasure n := by
            apply integral_congr_ae
            filter_upwards with A
            rw [ginibre_complexShiftedDet_eq_sum_permutationTerms,
              ginibre_complexShiftedDet_eq_sum_permutationTerms,
              Finset.sum_mul]
            simp_rw [Finset.mul_sum]
    _ = ∑ σ : Equiv.Perm (Fin n),
          ∫ A : RSqMat n,
            ∑ τ : Equiv.Perm (Fin n),
              ginibreComplexShiftedDeterminantPermutationTerm z σ A *
                ginibreComplexShiftedDeterminantPermutationTerm w τ A
            ∂realGinibreMeasure n := by
      exact integral_finset_sum _ (fun σ _ => hinner σ)
    _ = ∑ σ : Equiv.Perm (Fin n),
          ∑ τ : Equiv.Perm (Fin n),
            ∫ A : RSqMat n,
              ginibreComplexShiftedDeterminantPermutationTerm z σ A *
                ginibreComplexShiftedDeterminantPermutationTerm w τ A
              ∂realGinibreMeasure n := by
      apply Finset.sum_congr rfl
      intro σ hσ
      exact integral_finset_sum _ (fun τ _ => hterm σ τ)
    _ = ∑ σ : Equiv.Perm (Fin n),
          ∑ τ : Equiv.Perm (Fin n),
            ginibrePermutationSignComplex σ *
              ginibrePermutationSignComplex τ *
              (if σ = τ then
                (1 + z * w) ^ (ginibrePermutationFixedPoints σ).card
              else 0) := by
      apply Finset.sum_congr rfl
      intro σ hσ
      apply Finset.sum_congr rfl
      intro τ hτ
      exact
        integral_ginibreComplexShiftedDeterminantPermutationTerm_mul z w σ τ
    _ = ∑ σ : Equiv.Perm (Fin n),
          ginibrePermutationSignComplex σ *
            ginibrePermutationSignComplex σ *
            (1 + z * w) ^ (ginibrePermutationFixedPoints σ).card := by
      apply Finset.sum_congr rfl
      intro σ hσ
      simp
    _ = ∑ σ : Equiv.Perm (Fin n),
          (1 + z * w) ^ (ginibrePermutationFixedPoints σ).card := by
      apply Finset.sum_congr rfl
      intro σ hσ
      rw [ginibrePermutationSignComplex_mul_self, one_mul]

/-- Exact characteristic-polynomial product for arbitrary complex spectral
parameters and a real-Ginibre matrix:

`𝔼[det(zI-G) det(wI-G)] = n! ∑_{k=0}^n (zw)^k/k!`.
-/
theorem integral_realGinibre_characteristicProduct_complex
    (n : ℕ) (z w : ℂ) :
    (∫ A : RSqMat n,
        (Matrix.scalar (Fin n) z - A.map Complex.ofReal).det *
          (Matrix.scalar (Fin n) w - A.map Complex.ofReal).det
      ∂realGinibreMeasure n) =
      (n.factorial : ℂ) *
        ∑ k ∈ Finset.range (n + 1),
          (z * w) ^ k / (k.factorial : ℂ) := by
  rw [integral_realGinibre_characteristicProduct_complex_eq_sum_fixedPoints]
  exact sum_pow_card_ginibrePermutationFixedPoints_complex n (z * w)

/-- Conjugate-shift specialization of the complex characteristic-product
identity. -/
theorem integral_realGinibre_characteristicProduct_conj
    (n : ℕ) (z : ℂ) :
    (∫ A : RSqMat n,
        (Matrix.scalar (Fin n) z - A.map Complex.ofReal).det *
          (Matrix.scalar (Fin n) (starRingEnd ℂ z) -
            A.map Complex.ofReal).det
      ∂realGinibreMeasure n) =
      (n.factorial : ℂ) *
        ∑ k ∈ Finset.range (n + 1),
          (z * starRingEnd ℂ z) ^ k / (k.factorial : ℂ) :=
  integral_realGinibre_characteristicProduct_complex n z (starRingEnd ℂ z)

end NumStability

end

noncomputable section

namespace NumStability

open MeasureTheory ProbabilityTheory Set Real Filter

open scoped BigOperators

/-- The characteristic-product integral is the scalar kernel evaluated at
the product of its two spectral parameters. -/
theorem integral_realGinibre_characteristicProduct_eq_kernel
    (m : ℕ) (u x : ℝ) :
    (∫ A : RSqMat m,
        (u • (1 : RSqMat m) - A).det *
          (x • (1 : RSqMat m) - A).det
      ∂realGinibreMeasure m) =
      ginibreCharacteristicProductKernel m (u * x) := by
  exact integral_realGinibre_characteristicProduct m u x

end NumStability

end
