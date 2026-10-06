/-
Copyright (c) 2026 QED. All rights reserved.
Released under Apache 2.0 license as described in LICENSES/Apache-2.0.txt.
SPDX-License-Identifier: Apache-2.0
See LICENSES/Apache-2.0.txt.
Authors: QED
-/
import NumStability.Algorithms.TestMatrices.Higham28Exact
import NumStability.Algorithms.TestMatrices.Higham28Stewart
import NumStability.Analysis.HighamChapter7
import Mathlib.Probability.Distributions.Gaussian.Real
import Mathlib.MeasureTheory.Constructions.Pi
import Mathlib.MeasureTheory.Integral.Bochner.Basic
import Mathlib.Algebra.Polynomial.Roots

namespace NumStability

/-! # Higham Chapter 28: precise probability statement surfaces

The chapter's two precise probabilistic prose claims are instantiated here on
standard product Gaussian and product uniform measures.  These declarations
make the remaining probability dependencies exact without assuming either
limit/almost-sure conclusion.
-/

open MeasureTheory Filter ProbabilityTheory

local instance (n : ℕ) : MeasurableSpace (RSqMat n) := MeasurableSpace.pi

noncomputable def realGinibreMeasure (n : ℕ) : Measure (RSqMat n) :=
  Measure.pi (fun _ : Fin n => Measure.pi (fun _ : Fin n => gaussianReal 0 1))

noncomputable def realEigenvalueCount (n : ℕ) (A : RSqMat n) : ℕ :=
  (Matrix.charpoly A).roots.card

noncomputable def expectedRealEigenvalueCount (n : ℕ) : ℝ :=
  ∫ A : RSqMat n, (realEigenvalueCount n A : ℝ) ∂realGinibreMeasure n

/-- Precise standard-limit formulation of the real-Ginibre prose on p. 517. -/
def RealGinibreExpectedCountLimit : Prop :=
  Tendsto (fun n : ℕ => expectedRealEigenvalueCount n / Real.sqrt n)
    atTop (nhds (Real.sqrt (2 / Real.pi)))

noncomputable def uniformUnitIntervalMatrixMeasure (n : ℕ) : Measure (RSqMat n) :=
  Measure.pi (fun _ : Fin n =>
    Measure.pi (fun _ : Fin n => volume.restrict (Set.Icc (0 : ℝ) 1)))

def strictlyPositiveMatrixSet (n : ℕ) : Set (RSqMat n) :=
  {A | ∀ i j, 0 < A i j}

def HasPositiveDominantEigenvalue {n : ℕ} (A : RSqMat n) : Prop :=
  ∃ r : ℝ, 0 < r ∧ (Matrix.charpoly A).IsRoot r ∧
    ∀ z : ℂ, ((Matrix.charpoly A).map Complex.ofRealHom).IsRoot z → ‖z‖ ≤ r

def positiveDominantEigenvalueSet (n : ℕ) : Set (RSqMat n) :=
  {A | HasPositiveDominantEigenvalue A}

/-- Precise almost-sure formulation of the iid-uniform Perron prose on p. 517. -/
def UniformPositivePerronAlmostSure : Prop :=
  ∀ n : ℕ, 0 < n →
    uniformUnitIntervalMatrixMeasure n
      (strictlyPositiveMatrixSet n ∩ positiveDominantEigenvalueSet n) = 1

/-! ## Explicit-domain probability transfers and compatibility predicates -/

/-- The standard real-Ginibre product law is normalized.  This is the
nonvacuity check for the probability space used by the expectation transfer
below; no random-matrix spectral claim is hidden in it. -/
theorem realGinibreMeasure_univ (n : ℕ) :
    realGinibreMeasure n Set.univ = 1 := by
  unfold realGinibreMeasure
  calc
    (Measure.pi (fun _ : Fin n =>
        Measure.pi (fun _ : Fin n => gaussianReal 0 1))) Set.univ =
        ∏ i : Fin n,
          Measure.pi (fun _ : Fin n => gaussianReal 0 1) Set.univ :=
      MeasureTheory.Measure.pi_univ _
    _ = 1 := by simp

/-- Higham, 2nd ed., pp. 516-517: explicit-domain transfer of the real
Ginibre expected-real-root limit.  `a` is the coefficient sequence delivered
by the cited finite-`n` expectation calculation; the two premises are the
genuine upstream finite formula and its Gamma/Stirling estimate. -/
theorem realGinibreExpectedCountLimit_of_coefficient_formula
    (a : ℕ → ℝ)
    (hfinite : ∀ n, expectedRealEigenvalueCount n = a n)
    (hestimate : Tendsto (fun n : ℕ => a n / Real.sqrt n)
      atTop (nhds (Real.sqrt (2 / Real.pi)))) :
    RealGinibreExpectedCountLimit := by
  unfold RealGinibreExpectedCountLimit
  convert hestimate using 1
  funext n
  rw [hfinite]

/-- The standard iid restricted-volume matrix law is normalized. -/
theorem uniformUnitIntervalMatrixMeasure_univ (n : ℕ) :
    uniformUnitIntervalMatrixMeasure n Set.univ = 1 := by
  unfold uniformUnitIntervalMatrixMeasure
  calc
    (Measure.pi (fun _ : Fin n => Measure.pi (fun _ : Fin n =>
        volume.restrict (Set.Icc (0 : ℝ) 1)))) Set.univ =
        ∏ i : Fin n, Measure.pi (fun _ : Fin n =>
          volume.restrict (Set.Icc (0 : ℝ) 1)) Set.univ :=
      MeasureTheory.Measure.pi_univ _
    _ = 1 := by simp [MeasureTheory.Measure.pi_univ]

/-- Every entry is strictly positive almost surely under the actual iid
uniform-`[0,1]` product law.  The only excluded boundary is the zero endpoint,
whose one-dimensional restricted-volume measure is zero. -/
theorem uniformUnitIntervalMatrixMeasure_strictlyPositive (n : ℕ) :
    uniformUnitIntervalMatrixMeasure n (strictlyPositiveMatrixSet n) = 1 := by
  have hset : strictlyPositiveMatrixSet n =
      Set.pi Set.univ (fun _ : Fin n ↦
        Set.pi Set.univ (fun _ : Fin n ↦ Set.Ioi (0 : ℝ))) := by
    ext A
    constructor
    · intro h i _ j _
      exact h i j
    · intro h i j
      exact h i (Set.mem_univ i) j (Set.mem_univ j)
  rw [hset]
  unfold uniformUnitIntervalMatrixMeasure
  have hcoord :
      (volume.restrict (Set.Icc (0 : ℝ) 1)) (Set.Ioi 0) = 1 := by
    rw [Measure.restrict_apply measurableSet_Ioi]
    have hinter : Set.Ioi (0 : ℝ) ∩ Set.Icc 0 1 = Set.Ioc 0 1 := by
      ext x
      constructor
      · rintro ⟨hx, -, hx1⟩
        exact ⟨hx, hx1⟩
      · rintro ⟨hx, hx1⟩
        exact ⟨hx, hx.le, hx1⟩
    rw [hinter, Real.volume_Ioc]
    norm_num
    rfl
  calc
    (Measure.pi (fun _ : Fin n ↦
        Measure.pi (fun _ : Fin n ↦ volume.restrict (Set.Icc (0 : ℝ) 1))))
        (Set.pi Set.univ (fun _ : Fin n ↦
          Set.pi Set.univ (fun _ : Fin n ↦ Set.Ioi (0 : ℝ)))) =
      ∏ _ : Fin n,
        Measure.pi (fun _ : Fin n ↦ volume.restrict (Set.Icc (0 : ℝ) 1))
          (Set.pi Set.univ (fun _ : Fin n ↦ Set.Ioi (0 : ℝ))) := by
            exact Measure.pi_pi _ _
    _ = ∏ _ : Fin n, ∏ _ : Fin n,
        (volume.restrict (Set.Icc (0 : ℝ) 1)) (Set.Ioi 0) := by
          congr 1
          funext i
          exact Measure.pi_pi _ _
    _ = 1 := by simp [hcoord]

/-- The strict-positivity event is genuinely inhabited in every dimension;
the all-ones matrix is a concrete witness. -/
theorem strictlyPositiveMatrixSet_nonempty (n : ℕ) :
    (strictlyPositiveMatrixSet n).Nonempty := by
  refine ⟨fun _ _ => 1, ?_⟩
  simp [strictlyPositiveMatrixSet]

/-- Every positive-dimensional entrywise-positive real matrix has a positive
real eigenvalue that dominates the moduli of all roots of its complexified
characteristic polynomial.  This is the deterministic Perron bridge needed
by the iid-uniform almost-sure statement below. -/
theorem hasPositiveDominantEigenvalue_of_strictlyPositive
    {n : ℕ} (hn : 0 < n) (A : RSqMat n)
    (hA : A ∈ strictlyPositiveMatrixSet n) :
    HasPositiveDominantEigenvalue A := by
  have hIrred : Matrix.IsIrreducible
      (Matrix.of A : Matrix (Fin n) (Fin n) ℝ) :=
    ch7_matrix_isIrreducible_of_pos_entries A hA
  obtain ⟨mu, _z, _x, y, _hz_ne, _hx_ne, _hx_nonneg, hy_pos,
      _heig_complex, _hrad, _hsubx, heig_real⟩ :=
    ch7_exists_spectralRadius_attaining_positive_eigenvector hn A hIrred
  let r : ℝ := ‖mu‖
  have hA_nonneg : ∀ i j : Fin n, 0 ≤ A i j :=
    fun i j => le_of_lt (hA i j)
  have hr_pos : 0 < r :=
    ch7_perronScalar_pos_of_nonneg_irreducible_eigenvector
      hn A r y hA_nonneg hIrred hy_pos heig_real
  have hy_ne : y ≠ 0 := by
    intro hy
    have h0 := congrFun hy ⟨0, hn⟩
    exact (ne_of_gt (hy_pos ⟨0, hn⟩)) h0
  have heig_matrix :
      Matrix.mulVec (Matrix.of A : Matrix (Fin n) (Fin n) ℝ) y = r • y := by
    rw [ch7_matrix_mulVec_eq_matMulVec]
    ext i
    simpa [Pi.smul_apply, smul_eq_mul] using heig_real i
  have hhas : Module.End.HasEigenvalue
      (Matrix.toLin' (Matrix.of A : Matrix (Fin n) (Fin n) ℝ)) r := by
    apply Module.End.hasEigenvalue_of_hasEigenvector
    rw [Module.End.hasEigenvector_iff]
    refine ⟨Module.End.mem_eigenspace_iff.mpr ?_, hy_ne⟩
    simpa [Matrix.toLin'_apply] using heig_matrix
  have hroot : (Matrix.charpoly A).IsRoot r := by
    rw [← Matrix.charpoly_toLin', ← Module.End.hasEigenvalue_iff_isRoot_charpoly]
    exact hhas
  have hradius : ch7IsComplexEigenvalueRadius A r :=
    ch7_isComplexEigenvalueRadius_of_positive_real_eigenvector
      hn A r y hA_nonneg hy_pos heig_real
  refine ⟨r, hr_pos, hroot, ?_⟩
  intro w hw
  have hcharpoly_complex :
      (show Matrix (Fin n) (Fin n) ℂ from realRectToCMatrix A).charpoly =
        (Matrix.charpoly A).map Complex.ofRealHom := by
    simpa [realRectToCMatrix, RingHom.mapMatrix_apply] using
      Matrix.charpoly_map (Matrix.of A : Matrix (Fin n) (Fin n) ℝ)
        Complex.ofRealHom
  have hwroot :
      (show Matrix (Fin n) (Fin n) ℂ from
        realRectToCMatrix A).charpoly.IsRoot w := by
    rwa [hcharpoly_complex]
  have hwspec_matrix : w ∈ spectrum ℂ
      (show Matrix (Fin n) (Fin n) ℂ from realRectToCMatrix A) :=
    Matrix.mem_spectrum_of_isRoot_charpoly hwroot
  have hwspec : w ∈ spectrum ℂ
      (Matrix.toLin'
        (show Matrix (Fin n) (Fin n) ℂ from realRectToCMatrix A)) := by
    rwa [Matrix.spectrum_toLin']
  have hgreatest :=
    ch7_toLin_spectrum_modulusSet_isGreatest_of_isComplexEigenvalueRadius hradius
  exact hgreatest.2 ⟨w, hwspec, rfl⟩

/-- Higham, 2nd ed., p. 517: explicit-domain transfer from the two missing
foundations, namely boundary-nullness of the product law and the deterministic
Perron theorem for entrywise-positive matrices.  Neither premise restates the
almost-sure intersection conclusion. -/
theorem uniformPositivePerronAlmostSure_of_boundary_null_of_perron
    (hpositive : ∀ n : ℕ, 0 < n →
      uniformUnitIntervalMatrixMeasure n (strictlyPositiveMatrixSet n) = 1)
    (hperron : ∀ {n : ℕ} (A : RSqMat n),
      A ∈ strictlyPositiveMatrixSet n → HasPositiveDominantEigenvalue A) :
    UniformPositivePerronAlmostSure := by
  intro n hn
  have hset : strictlyPositiveMatrixSet n ∩ positiveDominantEigenvalueSet n =
      strictlyPositiveMatrixSet n := by
    ext A
    constructor
    · exact fun h => h.1
    · intro hA
      exact ⟨hA, hperron A hA⟩
  rw [hset, hpositive n hn]

/-- Higham, 2nd ed., p. 517: an iid uniform-`[0,1]` matrix is entrywise
positive and hence has a positive dominant Perron root almost surely in every
positive dimension. -/
theorem uniformPositivePerronAlmostSure :
    UniformPositivePerronAlmostSure := by
  intro n hn
  have hset : strictlyPositiveMatrixSet n ∩ positiveDominantEigenvalueSet n =
      strictlyPositiveMatrixSet n := by
    ext A
    constructor
    · exact fun h => h.1
    · intro hA
      exact ⟨hA, hasPositiveDominantEigenvalue_of_strictlyPositive hn A hA⟩
  rw [hset, uniformUnitIntervalMatrixMeasure_strictlyPositive]

/-- An ambient-matrix compatibility predicate for a normalized orthogonally
supported, left-invariant law.  This is useful as a transfer surface, but is
not Mathlib's group-level `Measure.IsHaarMeasure` endpoint and does not by
itself prove Stewart's Theorem 28.1.  The exact source push-forward and exact
group-level endpoint are `stewartOrthogonalGroupLaw` and
`StewartTheorem28_1HaarConclusion`. -/
def IsNormalizedOrthogonalHaarLaw (n : ℕ) (mu : Measure (RSqMat n)) : Prop :=
  mu Set.univ = 1 ∧
    mu {Q | IsOrthogonal n Q} = 1 ∧
    ∀ (U : RSqMat n), IsOrthogonal n U →
      ∀ s : Set (RSqMat n), MeasurableSet s →
        mu ((fun Q => U * Q) ⁻¹' s) = mu s

/-- Constructor for the ambient compatibility predicate from its three
fields.  This is a packaging lemma only: callers must still produce
normalization, orthogonal support, and left invariance, and the theorem does
not identify Stewart's Gaussian push-forward with group Haar measure. -/
theorem stewartLaw_isNormalizedOrthogonalHaarLaw
    {n : ℕ} (mu : Measure (RSqMat n))
    (hmass : mu Set.univ = 1)
    (hsupport : mu {Q | IsOrthogonal n Q} = 1)
    (hinvariant : ∀ (U : RSqMat n), IsOrthogonal n U →
      ∀ s : Set (RSqMat n), MeasurableSet s →
        mu ((fun Q => U * Q) ⁻¹' s) = mu s) :
    IsNormalizedOrthogonalHaarLaw n mu :=
  ⟨hmass, hsupport, hinvariant⟩

/-- The ambient compatibility predicate is inhabited in dimension zero: the
matrix space is a singleton, so the Dirac law at the identity has all three
fields.  This is not a nonvacuity witness for Stewart's positive-dimensional
Gaussian producer or its Haar conclusion. -/
theorem diracIdentity_isNormalizedOrthogonalHaarLaw_zero :
    IsNormalizedOrthogonalHaarLaw 0
      (Measure.dirac (1 : RSqMat 0)) := by
  refine ⟨by simp, ?_, ?_⟩
  · have horth : ∀ Q : RSqMat 0, IsOrthogonal 0 Q := by
      intro Q
      rw [Subsingleton.elim Q (1 : RSqMat 0)]
      exact IsOrthogonal.id 0
    have hset : {Q : RSqMat 0 | IsOrthogonal 0 Q} = Set.univ := by
      ext Q
      simp [horth Q]
    rw [hset]
    simp
  · intro U hU s hs
    have hpre : (fun Q : RSqMat 0 => U * Q) ⁻¹' s = s := by
      ext Q
      have hmul : U * Q = Q := Subsingleton.elim _ _
      change U * Q ∈ s ↔ Q ∈ s
      rw [hmul]
    rw [hpre]

end NumStability
