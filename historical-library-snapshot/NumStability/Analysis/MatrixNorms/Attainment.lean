-- Analysis/MatrixNorms/Attainment.lean
--
-- Extremizers for finite-dimensional complex matrix norms.

import NumStability.Analysis.MatrixNorms.Comparisons
import NumStability.Analysis.OperatorNorms.Attainment
import NumStability.Analysis.VectorNorms.Attainment

/-!
# Matrix-norm attainment

Proves compactness and attainment results for induced and standard matrix
norms, packaging explicit maximizing vectors where needed.
-/

namespace NumStability

open scoped BigOperators
open scoped ComplexOrder
open ENNReal


/-- Values of `ν(Ax)` on the `ν(x)=1` unit sphere for Problem 6.16. -/
def RealImagMatrixUnitNormSet {m n : ℕ} (A : CMatrix m n) : Set ℝ :=
  {r | ∃ x : CVec n, complexVecRealImagOneNorm x = 1 ∧
    r = complexVecRealImagOneNorm (complexMatrixVecMul A x)}

/-- Predicate form of `ν(A) = max_{ν(x)=1} ν(Ax)` for Problem 6.16. -/
def IsMaxRealImagMatrixNormValue {m n : ℕ} (A : CMatrix m n) (c : ℝ) : Prop :=
  c ∈ RealImagMatrixUnitNormSet A ∧
    ∀ r : ℝ, r ∈ RealImagMatrixUnitNormSet A → r ≤ c

/-- Problem 6.16: explicit induced expression for
    `ν(A) = max_{ν(x)=1} ν(Ax)`. -/
theorem complexMatrixRealImagOneNorm_isMaxRealImagMatrixNormValue
    {m n : ℕ} (hn : 0 < n) (A : CMatrix m n) :
    IsMaxRealImagMatrixNormValue A (complexMatrixRealImagOneNorm A) := by
  classical
  let f : Fin n → NNReal := fun j => ∑ i : Fin m, complexRealImagAbsNN (A i j)
  have huniv : (Finset.univ : Finset (Fin n)).Nonempty :=
    ⟨⟨0, hn⟩, Finset.mem_univ _⟩
  obtain ⟨j, _hjmem, hsup⟩ :=
    Finset.exists_mem_eq_sup (s := (Finset.univ : Finset (Fin n))) huniv f
  refine ⟨?_, ?_⟩
  · refine ⟨standardBasisCVec j, complexVecRealImagOneNorm_standardBasisCVec j, ?_⟩
    rw [complexMatrixVecMul_standardBasisCVec]
    exact complexMatrixRealImagOneNorm_column_value_of_sup A j hsup
  · intro r hr
    obtain ⟨x, hxunit, hr⟩ := hr
    rw [hr]
    have hbound := complexMatrixVecMul_realImagOneNorm_le A x
    rwa [hxunit, mul_one] at hbound

/-- Candidate value set `{x^* A x : ||x||_∞ = 1}` for the Higham Problem 6.12
    maximum, represented by real quadratic-form values. -/
def ComplexMatrixInfOneQuadraticUnitSet {n : ℕ}
    (A : CMatrix n n) : Set ℝ :=
  {r | ∃ x : CVec n,
    complexVecInfNorm x = 1 ∧ r = complexMatrixQuadraticFormRe A x}

/-- Predicate saying `M` is the maximum of `{x^* A x : ||x||_∞ = 1}`. This
    keeps compact-attainment infrastructure separate from the norm identity. -/
def IsMaxComplexMatrixInfOneQuadraticUnitValue {n : ℕ}
    (A : CMatrix n n) (M : ℝ) : Prop :=
  M ∈ ComplexMatrixInfOneQuadraticUnitSet A ∧
    ∀ r : ℝ, r ∈ ComplexMatrixInfOneQuadraticUnitSet A → r ≤ M

lemma complexMatrix_oneNorm_mulVec_le_quadratic_max_of_unit
    {n : ℕ} (hn : 0 < n) {A : CMatrix n n}
    (hA : Matrix.PosSemidef (A : Matrix (Fin n) (Fin n) ℂ))
    {M : ℝ}
    (hM : IsMaxComplexMatrixInfOneQuadraticUnitValue A M)
    {u : CVec n} (hu : complexVecInfNorm u = 1) :
    complexVecOneNorm (complexMatrixVecMul A u) ≤ M := by
  obtain ⟨v, hvunit, hvpair⟩ :=
    exists_unit_infNorm_pairing_oneNorm hn (complexMatrixVecMul A u)
  have hM_nonneg : 0 ≤ M := by
    obtain ⟨x0, hx0, hMx0⟩ := hM.1
    rw [hMx0]
    exact complexMatrixQuadraticFormRe_nonneg_of_posSemidef hA x0
  have huM :
      complexMatrixQuadraticFormRe A u ≤ M :=
    hM.2 _ ⟨u, hu, rfl⟩
  have hvM :
      complexMatrixQuadraticFormRe A v ≤ M :=
    hM.2 _ ⟨v, hvunit, rfl⟩
  calc
    complexVecOneNorm (complexMatrixVecMul A u)
        = ‖∑ i : Fin n, star (v i) * complexMatrixVecMul A u i‖ := hvpair.symm
    _ ≤ Real.sqrt (complexMatrixQuadraticFormRe A u) *
          Real.sqrt (complexMatrixQuadraticFormRe A v) :=
        complexMatrixQuadraticForm_cauchy_of_posSemidef hA u v
    _ ≤ Real.sqrt M * Real.sqrt M := by
        exact mul_le_mul (Real.sqrt_le_sqrt huM) (Real.sqrt_le_sqrt hvM)
          (Real.sqrt_nonneg _) (Real.sqrt_nonneg _)
    _ = M := by
        rw [← sq, Real.sq_sqrt hM_nonneg]

set_option linter.unusedTactic false in
/-- Higham Problem 6.12, in a reusable PSD form: if the local mixed subordinate
    `∞ -> 1` norm value exists and the quadratic form has a recorded maximum
    over the infinity-unit sphere, then the two values are equal. -/
theorem complexMatrix_infOneNormValue_eq_quadraticUnitMax_of_posSemidef
    {n : ℕ} (hn : 0 < n) {A : CMatrix n n}
    (hA : Matrix.PosSemidef (A : Matrix (Fin n) (Fin n) ℂ))
    {d M : ℝ}
    (hd : IsMixedSubordinateMatrixNormValue complexVecInfNorm complexVecOneNorm A d)
    (hM : IsMaxComplexMatrixInfOneQuadraticUnitValue A M) :
    d = M := by
  -- Preserve frozen auxiliary names across the semantic module split.
  run_tac do
    let ngen ← Lean.getDeclNGen
    Lean.setDeclNGen { ngen with idx := 4 }
  have hbound : MixedSubordinateMatrixBound complexVecInfNorm complexVecOneNorm A M := by
    intro x
    by_cases hx : x = 0
    · simp [hx, complexMatrixVecMul, complexVecOneNorm, complexVecInfNorm]
    · let r : ℝ := complexVecInfNorm x
      have hr_nonneg : 0 ≤ r := complexVecInfNorm_nonneg x
      have hr_ne : r ≠ 0 := by
        intro hr
        have hxzero :=
          (complexVecInfNorm_isComplexVectorNorm.eq_zero_iff x).mp hr
        exact hx hxzero
      let u : CVec n := complexVecSMul (((r)⁻¹ : ℝ) : ℂ) x
      have hu : complexVecInfNorm u = 1 := by
        dsimp [u]
        rw [complexVecInfNorm_isComplexVectorNorm.smul]
        have hinv_nonneg : 0 ≤ r⁻¹ := inv_nonneg.mpr hr_nonneg
        rw [Complex.norm_of_nonneg hinv_nonneg]
        exact inv_mul_cancel₀ hr_ne
      have hunit :=
        complexMatrix_oneNorm_mulVec_le_quadratic_max_of_unit
          hn hA hM hu
      have hx_eq : x = complexVecSMul ((r : ℂ)) u := by
        ext i
        dsimp [u, complexVecSMul]
        norm_num
        field_simp [hr_ne]
      calc
        complexVecOneNorm (complexMatrixVecMul A x)
            = complexVecOneNorm
                (complexMatrixVecMul A (complexVecSMul (r : ℂ) u)) := by
                rw [hx_eq]
        _ = complexVecOneNorm
              (complexVecSMul (r : ℂ) (complexMatrixVecMul A u)) := by
              rw [(complexMatrixVecMul_linear A).map_smul]
        _ = ‖(r : ℂ)‖ * complexVecOneNorm (complexMatrixVecMul A u) := by
              rw [complexVecOneNorm_isComplexVectorNorm.smul]
        _ = r * complexVecOneNorm (complexMatrixVecMul A u) := by
              rw [Complex.norm_of_nonneg hr_nonneg]
        _ ≤ r * M := mul_le_mul_of_nonneg_left hunit hr_nonneg
        _ = M * complexVecInfNorm x := by
              simp [r, mul_comm]
  have hd_le : d ≤ M := hd.2 M hbound
  have hM_le : M ≤ d := by
    obtain ⟨x0, hx0, hMx0⟩ := hM.1
    have hpair :=
      complexVecConjInfNorm_mul_oneNorm_pairing_le
        x0 (complexMatrixVecMul A x0)
    have hquad_pair :
        complexMatrixQuadraticForm A x0 =
          ∑ i : Fin n, star (x0 i) * complexMatrixVecMul A x0 i :=
      complexMatrixQuadraticForm_eq_pairing A x0
    calc
      M = complexMatrixQuadraticFormRe A x0 := hMx0
      _ = ‖complexMatrixQuadraticForm A x0‖ :=
          complexMatrixQuadraticFormRe_eq_norm_of_posSemidef hA x0
      _ = ‖∑ i : Fin n, star (x0 i) * complexMatrixVecMul A x0 i‖ := by
          rw [hquad_pair]
      _ ≤ complexVecInfNorm x0 * complexVecOneNorm (complexMatrixVecMul A x0) :=
          hpair
      _ = complexVecOneNorm (complexMatrixVecMul A x0) := by
          rw [hx0, one_mul]
      _ ≤ d * complexVecInfNorm x0 := hd.1 x0
      _ = d := by
          rw [hx0, mul_one]
  exact le_antisymm hd_le hM_le

/-- Higham Problem 6.12 in the source's Hermitian positive definite wording.
    Positive definiteness supplies the PSD hypothesis used by the proof. -/
theorem complexMatrix_infOneNormValue_eq_quadraticUnitMax_of_posDef
    {n : ℕ} (hn : 0 < n) {A : CMatrix n n}
    (hA : Matrix.PosDef (A : Matrix (Fin n) (Fin n) ℂ))
    {d M : ℝ}
    (hd : IsMixedSubordinateMatrixNormValue complexVecInfNorm complexVecOneNorm A d)
    (hM : IsMaxComplexMatrixInfOneQuadraticUnitValue A M) :
    d = M :=
  complexMatrix_infOneNormValue_eq_quadraticUnitMax_of_posSemidef
    hn hA.posSemidef hd hM

/-- Matrix version of the unit-sphere image norm set in equations (6.5)-(6.6). -/
def MixedSubordinateMatrixUnitNormSet {n m : ℕ} (να : CVec n → ℝ)
    (νβ : CVec m → ℝ) (A : CMatrix m n) : Set ℝ :=
  MixedUnitImageNormSet να νβ (complexMatrixVecMul A)

/-- Matrix version of the nonzero-vector ratio set in equation (6.5). -/
def MixedSubordinateMatrixNonzeroRatioSet {n m : ℕ} (να : CVec n → ℝ)
    (νβ : CVec m → ℝ) (A : CMatrix m n) : Set ℝ :=
  MixedNonzeroImageRatioSet να νβ (complexMatrixVecMul A)

/-- Matrix version of the source-facing unit-sphere maximum. -/
def IsMaxMixedSubordinateMatrixNormValue {n m : ℕ} (να : CVec n → ℝ)
    (νβ : CVec m → ℝ) (A : CMatrix m n) (c : ℝ) : Prop :=
  IsMaxMixedUnitImageNormValue να νβ (complexMatrixVecMul A) c

/-- Matrix version of the source-facing nonzero-vector ratio maximum. -/
def IsMaxMixedSubordinateMatrixRatioValue {n m : ℕ} (να : CVec n → ℝ)
    (νβ : CVec m → ℝ) (A : CMatrix m n) (c : ℝ) : Prop :=
  IsMaxMixedNonzeroImageRatioValue να νβ (complexMatrixVecMul A) c

/-- Matrix version of the source-facing minimum nonzero-vector gain. -/
def IsMinMixedSubordinateMatrixRatioValue {n m : ℕ} (να : CVec n → ℝ)
    (νβ : CVec m → ℝ) (A : CMatrix m n) (c : ℝ) : Prop :=
  IsMinMixedNonzeroImageRatioValue να νβ (complexMatrixVecMul A) c

-- Keep lazily generated equation theorems in their frozen semantic owner.
run_meta do
  for declName in #[
      ``NumStability.IsMaxMixedSubordinateMatrixRatioValue,
      ``NumStability.IsMinMixedSubordinateMatrixRatioValue] do
    discard <| Lean.Meta.getEqnsFor? declName

/-- Matrix version of the source-facing dual-unit real pairing set. -/
def MixedSubordinateMatrixDualUnitPairingRealSet {n m : ℕ}
    (να : CVec n → ℝ) (νβ : CVec m → ℝ) (A : CMatrix m n) : Set ℝ :=
  MixedDualUnitPairingRealSet να νβ (complexMatrixVecMul A)

/-- Matrix version of the source-facing dual-unit real pairing maximum. -/
def IsMaxMixedSubordinateMatrixDualUnitPairingRealValue {n m : ℕ}
    (να : CVec n → ℝ) (νβ : CVec m → ℝ) (A : CMatrix m n) (c : ℝ) : Prop :=
  IsMaxMixedDualUnitPairingRealValue να νβ (complexMatrixVecMul A) c

/-- Source-facing unit-sphere image set for the matrix `p`-norm notation
    `||A||_p` in Higham Chapter 6. -/
def ComplexMatrixLpUnitNormSet {m n : ℕ} (p : ℝ≥0∞)
    (A : CMatrix m n) : Set ℝ :=
  MixedSubordinateMatrixUnitNormSet
    (complexVecLpNorm (n := n) p) (complexVecLpNorm (n := m) p) A

/-- Source-facing nonzero-vector ratio set for the matrix `p`-norm notation
    `||A||_p` in Higham Chapter 6. -/
def ComplexMatrixLpNonzeroRatioSet {m n : ℕ} (p : ℝ≥0∞)
    (A : CMatrix m n) : Set ℝ :=
  MixedSubordinateMatrixNonzeroRatioSet
    (complexVecLpNorm (n := n) p) (complexVecLpNorm (n := m) p) A

/-- Source-facing maximum form of the matrix `p`-norm: `c` is the maximum of
    `||A x||_p` over `||x||_p = 1`. -/
def IsMaxComplexMatrixLpNormValue {m n : ℕ} (p : ℝ≥0∞)
    (A : CMatrix m n) (c : ℝ) : Prop :=
  IsMaxMixedSubordinateMatrixNormValue
    (complexVecLpNorm (n := n) p) (complexVecLpNorm (n := m) p) A c

/-- Source-facing ratio form of the matrix `p`-norm: `c` is the maximum of
    `||A x||_p / ||x||_p` over nonzero `x`. -/
def IsMaxComplexMatrixLpNormRatioValue {m n : ℕ} (p : ℝ≥0∞)
    (A : CMatrix m n) (c : ℝ) : Prop :=
  IsMaxMixedSubordinateMatrixRatioValue
    (complexVecLpNorm (n := n) p) (complexVecLpNorm (n := m) p) A c

theorem isMixedSubordinateMatrixNormValue_of_isMaxMatrixNormValue
    {n m : ℕ} {να : CVec n → ℝ} {νβ : CVec m → ℝ}
    {A : CMatrix m n} {c : ℝ}
    (hα : IsComplexVectorNorm να) (hβ : IsComplexVectorNorm νβ)
    (hmax : IsMaxMixedSubordinateMatrixNormValue να νβ A c) :
    IsMixedSubordinateMatrixNormValue να νβ A c :=
  isMixedSubordinateNormValue_of_isMaxMixedUnitImageNormValue hα hβ
    (complexMatrixVecMul_linear A) hmax

/-- Concrete matrix form of equations (6.5)-(6.6): a positive least mixed
    subordinate matrix norm value is the maximum of the target norm on the
    source unit sphere. -/
theorem isMaxMixedSubordinateMatrixNormValue_of_matrixNormValue
    {n m : ℕ} {να : CVec n → ℝ} {νβ : CVec m → ℝ}
    (hα : IsComplexVectorNorm να) (hβ : IsComplexVectorNorm νβ)
    {A : CMatrix m n} {c : ℝ}
    (hAval : IsMixedSubordinateMatrixNormValue να νβ A c)
    (hcpos : 0 < c) :
    IsMaxMixedSubordinateMatrixNormValue να νβ A c :=
  isMaxMixedUnitImageNormValue_of_mixedSubordinateNormValue hα hβ
    (complexMatrixVecMul_linear A) hAval hcpos

/-- Nonempty-domain concrete matrix form of equations (6.5)-(6.6), including
    the zero matrix/value case. -/
theorem isMaxMixedSubordinateMatrixNormValue_of_matrixNormValue_nonempty
    {n m : ℕ} {να : CVec n → ℝ} {νβ : CVec m → ℝ}
    (hα : IsComplexVectorNorm να) (hβ : IsComplexVectorNorm νβ) (hn : 0 < n)
    {A : CMatrix m n} {c : ℝ}
    (hAval : IsMixedSubordinateMatrixNormValue να νβ A c) :
    IsMaxMixedSubordinateMatrixNormValue να νβ A c :=
  isMaxMixedUnitImageNormValue_of_mixedSubordinateNormValue_nonempty
    hα hβ hn (complexMatrixVecMul_linear A) hAval

theorem isMaxMixedSubordinateMatrixRatioValue_iff_unitNormValue
    {n m : ℕ} {να : CVec n → ℝ} {νβ : CVec m → ℝ}
    (hα : IsComplexVectorNorm να) (hβ : IsComplexVectorNorm νβ)
    {A : CMatrix m n} {c : ℝ} :
    IsMaxMixedSubordinateMatrixRatioValue να νβ A c ↔
      IsMaxMixedSubordinateMatrixNormValue να νβ A c :=
  isMaxMixedNonzeroImageRatioValue_iff_unitImageNormValue hα hβ
    (complexMatrixVecMul_linear A)

/-- Concrete matrix form of Higham equation (6.5): for a positive local mixed
    subordinate matrix norm value, the nonzero-vector ratio maximum and the
    unit-sphere maximum agree at the same value. -/
theorem isMaxMixedSubordinateMatrixRatioValue_of_matrixNormValue
    {n m : ℕ} {να : CVec n → ℝ} {νβ : CVec m → ℝ}
    (hα : IsComplexVectorNorm να) (hβ : IsComplexVectorNorm νβ)
    {A : CMatrix m n} {c : ℝ}
    (hAval : IsMixedSubordinateMatrixNormValue να νβ A c)
    (hcpos : 0 < c) :
    IsMaxMixedSubordinateMatrixRatioValue να νβ A c :=
  (isMaxMixedSubordinateMatrixRatioValue_iff_unitNormValue hα hβ).2
    (isMaxMixedSubordinateMatrixNormValue_of_matrixNormValue hα hβ hAval hcpos)

/-- Nonempty-domain concrete matrix ratio form of equation (6.5), including
    the zero matrix/value case. -/
theorem isMaxMixedSubordinateMatrixRatioValue_of_matrixNormValue_nonempty
    {n m : ℕ} {να : CVec n → ℝ} {νβ : CVec m → ℝ}
    (hα : IsComplexVectorNorm να) (hβ : IsComplexVectorNorm νβ) (hn : 0 < n)
    {A : CMatrix m n} {c : ℝ}
    (hAval : IsMixedSubordinateMatrixNormValue να νβ A c) :
    IsMaxMixedSubordinateMatrixRatioValue να νβ A c :=
  (isMaxMixedSubordinateMatrixRatioValue_iff_unitNormValue hα hβ).2
    (isMaxMixedSubordinateMatrixNormValue_of_matrixNormValue_nonempty
      hα hβ hn hAval)

/-- Concrete matrix wrapper for the Problem 6.3 dual-pairing maximum. -/
theorem isMaxMixedSubordinateMatrixDualUnitPairingRealValue_of_matrixNormValue_nonempty
    {n m : ℕ} {να : CVec n → ℝ} {νβ : CVec m → ℝ}
    (hα : IsComplexVectorNorm να) (hβ : IsComplexVectorNorm νβ)
    (hn : 0 < n) (hm : 0 < m) {A : CMatrix m n} {c : ℝ}
    (hAval : IsMixedSubordinateMatrixNormValue να νβ A c) :
    IsMaxMixedSubordinateMatrixDualUnitPairingRealValue να νβ A c := by
  simpa [IsMaxMixedSubordinateMatrixDualUnitPairingRealValue,
    IsMixedSubordinateMatrixNormValue] using
    (isMaxMixedDualUnitPairingRealValue_of_mixedSubordinateNormValue_nonempty
      hα hβ hn hm (complexMatrixVecMul_linear A) hAval)

/-- Source-facing `p`-norm max-to-least bridge: the unit-sphere maximum form
    of `||A||_p` gives the local least-bound predicate. -/
theorem isComplexMatrixLpNormValue_of_isMaxComplexMatrixLpNormValue
    {m n : ℕ} {p : ℝ≥0∞} [Fact (1 ≤ p)] {A : CMatrix m n} {c : ℝ}
    (hmax : IsMaxComplexMatrixLpNormValue p A c) :
    IsComplexMatrixLpNormValue p A c := by
  simpa [IsComplexMatrixLpNormValue, IsMaxComplexMatrixLpNormValue] using
    (isMixedSubordinateMatrixNormValue_of_isMaxMatrixNormValue
      (complexVecLpNorm_isComplexVectorNorm (n := n) p)
      (complexVecLpNorm_isComplexVectorNorm (n := m) p) hmax)

/-- Nonempty-domain source-facing maximum form of the matrix `p`-norm:
    a local least-bound `p`-norm value is the maximum over `||x||_p = 1`. -/
theorem isMaxComplexMatrixLpNormValue_of_complexMatrixLpNormValue_nonempty
    {m n : ℕ} (hn : 0 < n) {p : ℝ≥0∞} [Fact (1 ≤ p)]
    {A : CMatrix m n} {c : ℝ}
    (hA : IsComplexMatrixLpNormValue p A c) :
    IsMaxComplexMatrixLpNormValue p A c := by
  simpa [IsComplexMatrixLpNormValue, IsMaxComplexMatrixLpNormValue] using
    (isMaxMixedSubordinateMatrixNormValue_of_matrixNormValue_nonempty
      (complexVecLpNorm_isComplexVectorNorm (n := n) p)
      (complexVecLpNorm_isComplexVectorNorm (n := m) p) hn hA)

/-- Source-facing equivalence between the nonzero-vector ratio and unit-sphere
    maximum forms of the matrix `p`-norm. -/
theorem isMaxComplexMatrixLpNormRatioValue_iff_normValue
    {m n : ℕ} {p : ℝ≥0∞} [Fact (1 ≤ p)]
    {A : CMatrix m n} {c : ℝ} :
    IsMaxComplexMatrixLpNormRatioValue p A c ↔
      IsMaxComplexMatrixLpNormValue p A c := by
  simpa [IsMaxComplexMatrixLpNormRatioValue, IsMaxComplexMatrixLpNormValue] using
    (isMaxMixedSubordinateMatrixRatioValue_iff_unitNormValue
      (complexVecLpNorm_isComplexVectorNorm (n := n) p)
      (complexVecLpNorm_isComplexVectorNorm (n := m) p)
      (A := A) (c := c))

/-- Nonempty-domain source-facing ratio form of the matrix `p`-norm:
    a local least-bound `p`-norm value is also the maximum of
    `||A x||_p / ||x||_p` over nonzero `x`. -/
theorem isMaxComplexMatrixLpNormRatioValue_of_complexMatrixLpNormValue_nonempty
    {m n : ℕ} (hn : 0 < n) {p : ℝ≥0∞} [Fact (1 ≤ p)]
    {A : CMatrix m n} {c : ℝ}
    (hA : IsComplexMatrixLpNormValue p A c) :
    IsMaxComplexMatrixLpNormRatioValue p A c :=
  (isMaxComplexMatrixLpNormRatioValue_iff_normValue (A := A) (c := c)).2
    (isMaxComplexMatrixLpNormValue_of_complexMatrixLpNormValue_nonempty
      hn hA)

/-- Finite real-exponent wrapper for the unit-sphere maximum form of the matrix
    `p`-norm. -/
theorem isMaxComplexMatrixLpNormValue_of_complexMatrixLpNormValue_ofReal
    {m n : ℕ} (hn : 0 < n) {p : ℝ} (hp : 1 ≤ p)
    {A : CMatrix m n} {c : ℝ}
    (hA : IsComplexMatrixLpNormValue (ENNReal.ofReal p) A c) :
    IsMaxComplexMatrixLpNormValue (ENNReal.ofReal p) A c := by
  haveI hpFact : Fact (1 ≤ ENNReal.ofReal p) := ⟨by
    rw [ENNReal.one_le_ofReal]
    exact hp⟩
  exact isMaxComplexMatrixLpNormValue_of_complexMatrixLpNormValue_nonempty
    hn hA

/-- Finite real-exponent wrapper for the nonzero-vector ratio maximum form of
    the matrix `p`-norm. -/
theorem isMaxComplexMatrixLpNormRatioValue_of_complexMatrixLpNormValue_ofReal
    {m n : ℕ} (hn : 0 < n) {p : ℝ} (hp : 1 ≤ p)
    {A : CMatrix m n} {c : ℝ}
    (hA : IsComplexMatrixLpNormValue (ENNReal.ofReal p) A c) :
    IsMaxComplexMatrixLpNormRatioValue (ENNReal.ofReal p) A c := by
  haveI hpFact : Fact (1 ≤ ENNReal.ofReal p) := ⟨by
    rw [ENNReal.one_le_ofReal]
    exact hp⟩
  exact isMaxComplexMatrixLpNormRatioValue_of_complexMatrixLpNormValue_nonempty
    hn hA

/-- Equation (6.11), p = 1, source-facing maximum form for the concrete
    maximum-column-sum matrix norm. -/
theorem complexMatrixOneNorm_isMaxMixedSubordinateMatrixNormValue
    {m n : ℕ} (hn : 0 < n) (A : CMatrix m n) :
    IsMaxMixedSubordinateMatrixNormValue complexVecOneNorm complexVecOneNorm A
      (complexMatrixOneNorm A) :=
  isMaxMixedSubordinateMatrixNormValue_of_matrixNormValue_nonempty
    complexVecOneNorm_isComplexVectorNorm complexVecOneNorm_isComplexVectorNorm hn
    (complexMatrixOneNorm_isMixedSubordinateMatrixNormValue hn A)

/-- Equation (6.5), p = 1, nonzero-vector ratio maximum form for the concrete
    maximum-column-sum matrix norm. -/
theorem complexMatrixOneNorm_isMaxMixedSubordinateMatrixRatioValue
    {m n : ℕ} (hn : 0 < n) (A : CMatrix m n) :
    IsMaxMixedSubordinateMatrixRatioValue complexVecOneNorm complexVecOneNorm A
      (complexMatrixOneNorm A) :=
  isMaxMixedSubordinateMatrixRatioValue_of_matrixNormValue_nonempty
    complexVecOneNorm_isComplexVectorNorm complexVecOneNorm_isComplexVectorNorm hn
    (complexMatrixOneNorm_isMixedSubordinateMatrixNormValue hn A)

/-- Problem 6.11(a), source-facing maximum form: the mixed subordinate matrix
    norm from the source `1`-norm to an arbitrary target vector norm is attained
    by a column of the matrix. -/
theorem complexMatrixColumnMaxVectorNorm_isMaxMixedSubordinateMatrixNormValue
    {m n : ℕ} {νβ : CVec m → ℝ} (hβ : IsComplexVectorNorm νβ)
    (hn : 0 < n) (A : CMatrix m n) :
    IsMaxMixedSubordinateMatrixNormValue complexVecOneNorm νβ A
      (complexMatrixColumnMaxVectorNorm νβ A) :=
  isMaxMixedSubordinateMatrixNormValue_of_matrixNormValue_nonempty
    complexVecOneNorm_isComplexVectorNorm hβ hn
    (complexMatrixColumnMaxVectorNorm_isMixedSubordinateMatrixNormValue hβ hn A)

/-- Problem 6.11(a), nonzero-vector ratio form. -/
theorem complexMatrixColumnMaxVectorNorm_isMaxMixedSubordinateMatrixRatioValue
    {m n : ℕ} {νβ : CVec m → ℝ} (hβ : IsComplexVectorNorm νβ)
    (hn : 0 < n) (A : CMatrix m n) :
    IsMaxMixedSubordinateMatrixRatioValue complexVecOneNorm νβ A
      (complexMatrixColumnMaxVectorNorm νβ A) :=
  isMaxMixedSubordinateMatrixRatioValue_of_matrixNormValue_nonempty
    complexVecOneNorm_isComplexVectorNorm hβ hn
    (complexMatrixColumnMaxVectorNorm_isMixedSubordinateMatrixNormValue hβ hn A)

/-- Problem 6.11(b), source-facing maximum form: the mixed subordinate matrix
    norm from an arbitrary source norm to the infinity norm is attained by a row
    functional with maximum dual norm value. -/
theorem complexMatrixRowDualMaxNorm_isMaxMixedSubordinateMatrixNormValue
    {m n : ℕ} {να : CVec n → ℝ} (hα : IsComplexVectorNorm να) (hn : 0 < n)
    (A : CMatrix m n) (drow : Fin m → ℝ)
    (hrow : ∀ i : Fin m,
      IsDualFunctionalNormValue να (complexMatrixRowFunctional A i) (drow i)) :
    IsMaxMixedSubordinateMatrixNormValue να complexVecInfNorm A
      (complexMatrixRowDualMaxNorm drow) :=
  isMaxMixedSubordinateMatrixNormValue_of_matrixNormValue_nonempty
    hα complexVecInfNorm_isComplexVectorNorm hn
    (complexMatrixRowDualMaxNorm_isMixedSubordinateMatrixNormValue hα hn A drow hrow)

/-- Problem 6.11(b), nonzero-vector ratio form. -/
theorem complexMatrixRowDualMaxNorm_isMaxMixedSubordinateMatrixRatioValue
    {m n : ℕ} {να : CVec n → ℝ} (hα : IsComplexVectorNorm να) (hn : 0 < n)
    (A : CMatrix m n) (drow : Fin m → ℝ)
    (hrow : ∀ i : Fin m,
      IsDualFunctionalNormValue να (complexMatrixRowFunctional A i) (drow i)) :
    IsMaxMixedSubordinateMatrixRatioValue να complexVecInfNorm A
      (complexMatrixRowDualMaxNorm drow) :=
  isMaxMixedSubordinateMatrixRatioValue_of_matrixNormValue_nonempty
    hα complexVecInfNorm_isComplexVectorNorm hn
    (complexMatrixRowDualMaxNorm_isMixedSubordinateMatrixNormValue hα hn A drow hrow)

/-- Problem 6.11(b), concrete `1 -> infinity` specialization:
    the mixed subordinate matrix norm induced by the source 1-norm and target
    infinity norm is the maximum row infinity norm. -/
theorem complexMatrixOneInfNorm_isMixedSubordinateMatrixNormValue
    {m n : ℕ} (hn : 0 < n) (A : CMatrix m n) :
    IsMixedSubordinateMatrixNormValue complexVecOneNorm complexVecInfNorm A
      (complexMatrixOneInfNorm A) := by
  unfold complexMatrixOneInfNorm
  exact complexMatrixRowDualMaxNorm_isMixedSubordinateMatrixNormValue
    complexVecOneNorm_isComplexVectorNorm hn A
    (fun i : Fin m => complexVecInfNorm (fun j : Fin n => A i j))
    (fun i => complexMatrixRowFunctional_oneNormDualValue hn A i)

/-- Problem 6.11(b), concrete `1 -> infinity` unit-sphere maximum form. -/
theorem complexMatrixOneInfNorm_isMaxMixedSubordinateMatrixNormValue
    {m n : ℕ} (hn : 0 < n) (A : CMatrix m n) :
    IsMaxMixedSubordinateMatrixNormValue complexVecOneNorm complexVecInfNorm A
      (complexMatrixOneInfNorm A) :=
  isMaxMixedSubordinateMatrixNormValue_of_matrixNormValue_nonempty
    complexVecOneNorm_isComplexVectorNorm complexVecInfNorm_isComplexVectorNorm hn
    (complexMatrixOneInfNorm_isMixedSubordinateMatrixNormValue hn A)

/-- Problem 6.11(b), concrete `1 -> infinity` nonzero-vector ratio form. -/
theorem complexMatrixOneInfNorm_isMaxMixedSubordinateMatrixRatioValue
    {m n : ℕ} (hn : 0 < n) (A : CMatrix m n) :
    IsMaxMixedSubordinateMatrixRatioValue complexVecOneNorm complexVecInfNorm A
      (complexMatrixOneInfNorm A) :=
  isMaxMixedSubordinateMatrixRatioValue_of_matrixNormValue_nonempty
    complexVecOneNorm_isComplexVectorNorm complexVecInfNorm_isComplexVectorNorm hn
    (complexMatrixOneInfNorm_isMixedSubordinateMatrixNormValue hn A)

/-- Equation (6.11), p = infinity, source-facing maximum form for the concrete
    maximum-row-sum matrix norm. -/
theorem complexMatrixInfNorm_isMaxMixedSubordinateMatrixNormValue
    {m n : ℕ} (hn : 0 < n) (A : CMatrix m n) :
    IsMaxMixedSubordinateMatrixNormValue complexVecInfNorm complexVecInfNorm A
      (complexMatrixInfNorm A) :=
  isMaxMixedSubordinateMatrixNormValue_of_matrixNormValue_nonempty
    complexVecInfNorm_isComplexVectorNorm complexVecInfNorm_isComplexVectorNorm hn
    (complexMatrixInfNorm_isMixedSubordinateMatrixNormValue hn A)

/-- Equation (6.5), p = infinity, nonzero-vector ratio maximum form for the
    concrete maximum-row-sum matrix norm. -/
theorem complexMatrixInfNorm_isMaxMixedSubordinateMatrixRatioValue
    {m n : ℕ} (hn : 0 < n) (A : CMatrix m n) :
    IsMaxMixedSubordinateMatrixRatioValue complexVecInfNorm complexVecInfNorm A
      (complexMatrixInfNorm A) :=
  isMaxMixedSubordinateMatrixRatioValue_of_matrixNormValue_nonempty
    complexVecInfNorm_isComplexVectorNorm complexVecInfNorm_isComplexVectorNorm hn
    (complexMatrixInfNorm_isMixedSubordinateMatrixNormValue hn A)

/-- Concrete matrix representing the rank-one map `v ↦ φ(v)y`, using the
    standard basis expansion of the linear functional `φ`. -/
noncomputable def rankOneCMatrixFromFunctional {n m : ℕ}
    (φ : CVec n → ℂ) (y : CVec m) : CMatrix m n :=
  fun i j => y i * φ (standardBasisCVec j)

lemma complexMatrixVecMul_rankOneCMatrixFromFunctional {n m : ℕ}
    {φ : CVec n → ℂ} {y : CVec m} (hφ : IsComplexLinearForm φ) :
    complexMatrixVecMul (rankOneCMatrixFromFunctional φ y) =
      rankOneOperator φ y := by
  ext v i
  calc
    (complexMatrixVecMul (rankOneCMatrixFromFunctional φ y) v) i =
        ∑ j : Fin n, (y i * φ (standardBasisCVec j)) * v j := by
          rfl
    _ = y i * ∑ j : Fin n, v j * φ (standardBasisCVec j) := by
          rw [Finset.mul_sum]
          refine Finset.sum_congr rfl ?_
          intro j _hj
          ring
    _ = y i * φ v := by
          rw [← hφ.apply_eq_sum_basis v]
    _ = (rankOneOperator φ y v) i := by
          simp [rankOneOperator]
          ring

/-- Concrete matrix form of Problem 6.2 for a rank-one map represented through
    a dual functional. -/
theorem rankOneCMatrix_isMixedSubordinateMatrixNormValue_of_dualFunctionalNormValue
    {n m : ℕ} {να : CVec n → ℝ} {νβ : CVec m → ℝ}
    (hβ : IsComplexVectorNorm νβ) {φ : CVec n → ℂ} {y : CVec m} {d : ℝ}
    (hφ : IsDualFunctionalNormValue να φ d) (hypos : 0 < νβ y) :
    IsMixedSubordinateMatrixNormValue να νβ (rankOneCMatrixFromFunctional φ y)
      (νβ y * d) := by
  have hmap := complexMatrixVecMul_rankOneCMatrixFromFunctional
    (n := n) (m := m) (φ := φ) (y := y) hφ.linear
  have hval :=
    (rankOneOperator_isMixedSubordinateNormValue_of_dualFunctionalNormValue
      hβ hφ hypos).2
  dsimp [IsMixedSubordinateMatrixNormValue]
  rw [hmap]
  exact hval

/-- Concrete matrix form of the rank-one construction in Lemma 6.3. -/
theorem rankOneCMatrix_isMixedSubordinateMatrixNormValue_one_of_normingFunctional
    {n m : ℕ} {να : CVec n → ℝ} {νβ : CVec m → ℝ}
    (hβ : IsComplexVectorNorm νβ) {x : CVec n} {y : CVec m}
    {φ : CVec n → ℂ} (hx : να x = 1) (hy : νβ y = 1)
    (hφ : IsNormingFunctionalAt να x φ) :
    IsMixedSubordinateMatrixNormValue να νβ (rankOneCMatrixFromFunctional φ y) 1 ∧
      complexMatrixVecMul (rankOneCMatrixFromFunctional φ y) x = y := by
  have hmap := complexMatrixVecMul_rankOneCMatrixFromFunctional
    (n := n) (m := m) (φ := φ) (y := y) hφ.linear
  have hmain :=
    rankOne_isMixedSubordinateNormValue_one_of_normingFunctional hβ hx hy hφ
  constructor
  · dsimp [IsMixedSubordinateMatrixNormValue]
    rw [hmap]
    exact hmain.1
  · rw [hmap]
    exact hmain.2

/-- Higham, 2nd ed., Chapter 6, Lemma 6.3 foundation, concrete matrix form:
    for unit source and target vectors there is a rank-one matrix with local
    mixed subordinate matrix norm value `1` mapping the source vector to the
    target vector. -/
theorem exists_rankOneCMatrix_isMixedSubordinateMatrixNormValue_one
    {n m : ℕ} {να : CVec n → ℝ} {νβ : CVec m → ℝ}
    (hα : IsComplexVectorNorm να) (hβ : IsComplexVectorNorm νβ)
    {x : CVec n} {y : CVec m} (hx : να x = 1) (hy : νβ y = 1) :
    ∃ A : CMatrix m n,
      IsMixedSubordinateMatrixNormValue να νβ A 1 ∧
        complexMatrixVecMul A x = y := by
  obtain ⟨φ, hφ⟩ := NormedCVec.exists_normingFunctionalAt_of_unit_vector hα hx
  have hmain :=
    rankOneCMatrix_isMixedSubordinateMatrixNormValue_one_of_normingFunctional
      hβ hx hy hφ
  exact ⟨rankOneCMatrixFromFunctional φ y, hmain⟩

/-- Values of ratios between two local mixed subordinate matrix norm values. -/
def MixedSubordinateMatrixNormRatioSet {n m : ℕ}
    (ναSrc : CVec n → ℝ) (ναTgt : CVec m → ℝ)
    (νβSrc : CVec n → ℝ) (νβTgt : CVec m → ℝ) : Set ℝ :=
  {r | ∃ (A : CMatrix m n) (dα dβ : ℝ),
    IsMixedSubordinateMatrixNormValue ναSrc ναTgt A dα ∧
      IsMixedSubordinateMatrixNormValue νβSrc νβTgt A dβ ∧
        dβ ≠ 0 ∧ r = dα / dβ}

/-- Maximum ratio between two local mixed subordinate matrix norms. -/
def IsMaxMixedSubordinateMatrixNormRatioValue {n m : ℕ}
    (ναSrc : CVec n → ℝ) (ναTgt : CVec m → ℝ)
    (νβSrc : CVec n → ℝ) (νβTgt : CVec m → ℝ) (c : ℝ) : Prop :=
  c ∈ MixedSubordinateMatrixNormRatioSet ναSrc ναTgt νβSrc νβTgt ∧
    ∀ r : ℝ, r ∈ MixedSubordinateMatrixNormRatioSet ναSrc ναTgt νβSrc νβTgt →
      r ≤ c

/-- Higham, 2nd ed., Chapter 6, equation (6.14), upper-bound direction in the
    local mixed-subordinate API: vector-norm ratio maxima bound the ratio of
    the corresponding matrix norm values. -/
theorem mixedSubordinateMatrixNormValue_le_mul_of_vectorNormRatioMax
    {m n : ℕ} (hn : 0 < n)
    {ναSrc νβSrc : CVec n → ℝ} {ναTgt νβTgt : CVec m → ℝ}
    (hαSrc : IsComplexVectorNorm ναSrc) (hβSrc : IsComplexVectorNorm νβSrc)
    (hαTgt : IsComplexVectorNorm ναTgt) (hβTgt : IsComplexVectorNorm νβTgt)
    {cTgt cSrc : ℝ}
    (hTgt : IsMaxVectorNormRatioValue ναTgt νβTgt cTgt)
    (hSrc : IsMaxVectorNormRatioValue νβSrc ναSrc cSrc)
    {A : CMatrix m n} {dα dβ : ℝ}
    (hAα : IsMixedSubordinateMatrixNormValue ναSrc ναTgt A dα)
    (hAβ : IsMixedSubordinateMatrixNormValue νβSrc νβTgt A dβ) :
    dα ≤ (cTgt * cSrc) * dβ := by
  have hcTgt_nonneg : 0 ≤ cTgt :=
    isMaxVectorNormRatioValue_nonneg hαTgt hβTgt hTgt
  have hdβ_nonneg : 0 ≤ dβ :=
    mixedSubordinateMatrixNormValue_nonneg_of_nonempty hn hβSrc hβTgt hAβ
  apply hAα.2
  intro x
  have htarget :
      ναTgt (complexMatrixVecMul A x) ≤
        cTgt * νβTgt (complexMatrixVecMul A x) :=
    vectorNorm_le_mul_of_isMaxVectorNormRatioValue hαTgt hβTgt hTgt _
  have hsource : νβSrc x ≤ cSrc * ναSrc x :=
    vectorNorm_le_mul_of_isMaxVectorNormRatioValue hβSrc hαSrc hSrc x
  have hmiddle :
      νβTgt (complexMatrixVecMul A x) ≤ dβ * (cSrc * ναSrc x) :=
    (hAβ.1 x).trans (mul_le_mul_of_nonneg_left hsource hdβ_nonneg)
  calc
    ναTgt (complexMatrixVecMul A x)
        ≤ cTgt * νβTgt (complexMatrixVecMul A x) := htarget
    _ ≤ cTgt * (dβ * (cSrc * ναSrc x)) :=
        mul_le_mul_of_nonneg_left hmiddle hcTgt_nonneg
    _ = ((cTgt * cSrc) * dβ) * ναSrc x := by ring

/-- Higham, 2nd ed., Chapter 6, equation (6.14), local Schneider-Strang
    comparison formula.  If the two vector-ratio maxima exist, then the
    corresponding maximum matrix-norm ratio is their product. -/
theorem schneiderStrang_mixedSubordinateMatrixNormRatio_isMax
    {m n : ℕ} (hn : 0 < n)
    {ναSrc νβSrc : CVec n → ℝ} {ναTgt νβTgt : CVec m → ℝ}
    (hαSrc : IsComplexVectorNorm ναSrc) (hβSrc : IsComplexVectorNorm νβSrc)
    (hαTgt : IsComplexVectorNorm ναTgt) (hβTgt : IsComplexVectorNorm νβTgt)
    {cTgt cSrc : ℝ}
    (hTgt : IsMaxVectorNormRatioValue ναTgt νβTgt cTgt)
    (hSrc : IsMaxVectorNormRatioValue νβSrc ναSrc cSrc) :
    IsMaxMixedSubordinateMatrixNormRatioValue ναSrc ναTgt νβSrc νβTgt
      (cTgt * cSrc) := by
  have hcTgt_pos : 0 < cTgt :=
    isMaxVectorNormRatioValue_pos hαTgt hβTgt hTgt
  have hcSrc_pos : 0 < cSrc :=
    isMaxVectorNormRatioValue_pos hβSrc hαSrc hSrc
  obtain ⟨y, hyne, hyc⟩ := hTgt.1
  obtain ⟨x, hxne, hxc⟩ := hSrc.1
  have hyβ_pos : 0 < νβTgt y := by
    have hne : νβTgt y ≠ 0 := by
      intro hy
      exact hyne ((hβTgt.eq_zero_iff y).mp hy)
    exact lt_of_le_of_ne (hβTgt.nonneg y) (Ne.symm hne)
  have hxβ_pos : 0 < νβSrc x := by
    have hne : νβSrc x ≠ 0 := by
      intro hx
      exact hxne ((hβSrc.eq_zero_iff x).mp hx)
    exact lt_of_le_of_ne (hβSrc.nonneg x) (Ne.symm hne)
  have hxα_pos : 0 < ναSrc x := by
    have hne : ναSrc x ≠ 0 := by
      intro hx
      exact hxne ((hαSrc.eq_zero_iff x).mp hx)
    exact lt_of_le_of_ne (hαSrc.nonneg x) (Ne.symm hne)
  let yβ : CVec m := complexVecSMul (((νβTgt y)⁻¹ : ℝ) : ℂ) y
  let xβ : CVec n := complexVecSMul (((νβSrc x)⁻¹ : ℝ) : ℂ) x
  have hyβ_unit : νβTgt yβ = 1 := by
    dsimp [yβ]
    rw [hβTgt.smul, Complex.norm_of_nonneg (inv_nonneg.mpr (hβTgt.nonneg y))]
    field_simp [ne_of_gt hyβ_pos]
  have hxβ_unit : νβSrc xβ = 1 := by
    dsimp [xβ]
    rw [hβSrc.smul, Complex.norm_of_nonneg (inv_nonneg.mpr (hβSrc.nonneg x))]
    field_simp [ne_of_gt hxβ_pos]
  have hyα_value : ναTgt yβ = cTgt := by
    dsimp [yβ]
    rw [hαTgt.smul, Complex.norm_of_nonneg (inv_nonneg.mpr (hβTgt.nonneg y))]
    calc
      (νβTgt y)⁻¹ * ναTgt y = ναTgt y / νβTgt y := by ring
      _ = cTgt := hyc.symm
  have hxα_mul_cSrc : ναSrc xβ * cSrc = 1 := by
    dsimp [xβ]
    rw [hαSrc.smul, Complex.norm_of_nonneg (inv_nonneg.mpr (hβSrc.nonneg x))]
    rw [hxc]
    field_simp [ne_of_gt hxα_pos, ne_of_gt hxβ_pos]
  obtain ⟨A, hAβ, hAx⟩ :=
    exists_rankOneCMatrix_isMixedSubordinateMatrixNormValue_one
      hβSrc hβTgt hxβ_unit hyβ_unit
  have hAα : IsMixedSubordinateMatrixNormValue ναSrc ναTgt A (cTgt * cSrc) := by
    refine ⟨?_, ?_⟩
    · intro z
      have htarget :
          ναTgt (complexMatrixVecMul A z) ≤
            cTgt * νβTgt (complexMatrixVecMul A z) :=
        vectorNorm_le_mul_of_isMaxVectorNormRatioValue hαTgt hβTgt hTgt _
      have hsource : νβSrc z ≤ cSrc * ναSrc z :=
        vectorNorm_le_mul_of_isMaxVectorNormRatioValue hβSrc hαSrc hSrc z
      have hmiddle :
          νβTgt (complexMatrixVecMul A z) ≤ cSrc * ναSrc z := by
        have hbeta : νβTgt (complexMatrixVecMul A z) ≤ νβSrc z := by
          simpa [one_mul] using hAβ.1 z
        exact hbeta.trans hsource
      calc
        ναTgt (complexMatrixVecMul A z)
            ≤ cTgt * νβTgt (complexMatrixVecMul A z) := htarget
        _ ≤ cTgt * (cSrc * ναSrc z) :=
            mul_le_mul_of_nonneg_left hmiddle (le_of_lt hcTgt_pos)
        _ = (cTgt * cSrc) * ναSrc z := by ring
    · intro e he
      have htest := he xβ
      rw [hAx, hyα_value] at htest
      have hmul := mul_le_mul_of_nonneg_right htest (le_of_lt hcSrc_pos)
      calc
        cTgt * cSrc ≤ (e * ναSrc xβ) * cSrc := by simpa [mul_comm] using hmul
        _ = e * (ναSrc xβ * cSrc) := by ring
        _ = e := by rw [hxα_mul_cSrc, mul_one]
  refine ⟨?_, ?_⟩
  · refine ⟨A, cTgt * cSrc, 1, hAα, hAβ, by norm_num, ?_⟩
    ring
  · intro r hr
    obtain ⟨B, dα, dβ, hBα, hBβ, hdβ_ne, hr⟩ := hr
    have hdβ_nonneg : 0 ≤ dβ :=
      mixedSubordinateMatrixNormValue_nonneg_of_nonempty hn hβSrc hβTgt hBβ
    have hdβ_pos : 0 < dβ :=
      lt_of_le_of_ne hdβ_nonneg (Ne.symm hdβ_ne)
    have hle :=
      mixedSubordinateMatrixNormValue_le_mul_of_vectorNormRatioMax
        (m := m) (n := n) hn hαSrc hβSrc hαTgt hβTgt
        hTgt hSrc hBα hBβ
    rw [hr]
    rw [div_le_iff₀ hdβ_pos]
    simpa [mul_assoc, mul_comm, mul_left_comm] using hle

/-- Higham, 2nd ed., Chapter 6, equation (6.15), sharp source-facing
    matrix p/q ratio for the case `1 <= q <= p`, in the local
    mixed-subordinate matrix norm-value API. -/
theorem complexMatrixLpNorm_ratio_max_card_rpow_of_exponent_le
    {n : ℕ} (hn : 0 < n) {p q : ℝ} (hq : 1 ≤ q) (hqp : q ≤ p) :
    IsMaxMixedSubordinateMatrixNormRatioValue
      (complexVecLpNorm (n := n) (ENNReal.ofReal p))
      (complexVecLpNorm (n := n) (ENNReal.ofReal p))
      (complexVecLpNorm (n := n) (ENNReal.ofReal q))
      (complexVecLpNorm (n := n) (ENNReal.ofReal q))
      ((n : ℝ) ^ (q⁻¹ - p⁻¹)) := by
  have hp : 1 ≤ p := hq.trans hqp
  haveI hpFact : Fact (1 ≤ ENNReal.ofReal p) := ⟨by
    rw [ENNReal.one_le_ofReal]
    exact hp⟩
  haveI hqFact : Fact (1 ≤ ENNReal.ofReal q) := ⟨by
    rw [ENNReal.one_le_ofReal]
    exact hq⟩
  have hpNorm : IsComplexVectorNorm
      (complexVecLpNorm (n := n) (ENNReal.ofReal p)) :=
    complexVecLpNorm_isComplexVectorNorm (ENNReal.ofReal p)
  have hqNorm : IsComplexVectorNorm
      (complexVecLpNorm (n := n) (ENNReal.ofReal q)) :=
    complexVecLpNorm_isComplexVectorNorm (ENNReal.ofReal q)
  have hTgt := complexVecLpNorm_ratio_max_one_of_exponent_le hn hq hqp
  have hSrc := complexVecLpNorm_ratio_max_card_rpow_of_exponent_le hn hq hqp
  have h := schneiderStrang_mixedSubordinateMatrixNormRatio_isMax
    (m := n) (n := n) hn hpNorm hqNorm hpNorm hqNorm hTgt hSrc
  simpa [one_mul] using h

/-- Higham, 2nd ed., Chapter 6, equation (6.15), sharp source-facing
    matrix p/q ratio for the case `1 <= p <= q`, in the local
    mixed-subordinate matrix norm-value API. -/
theorem complexMatrixLpNorm_ratio_max_card_rpow_of_exponent_ge
    {n : ℕ} (hn : 0 < n) {p q : ℝ} (hp : 1 ≤ p) (hpq : p ≤ q) :
    IsMaxMixedSubordinateMatrixNormRatioValue
      (complexVecLpNorm (n := n) (ENNReal.ofReal p))
      (complexVecLpNorm (n := n) (ENNReal.ofReal p))
      (complexVecLpNorm (n := n) (ENNReal.ofReal q))
      (complexVecLpNorm (n := n) (ENNReal.ofReal q))
      ((n : ℝ) ^ (p⁻¹ - q⁻¹)) := by
  have hq : 1 ≤ q := hp.trans hpq
  haveI hpFact : Fact (1 ≤ ENNReal.ofReal p) := ⟨by
    rw [ENNReal.one_le_ofReal]
    exact hp⟩
  haveI hqFact : Fact (1 ≤ ENNReal.ofReal q) := ⟨by
    rw [ENNReal.one_le_ofReal]
    exact hq⟩
  have hpNorm : IsComplexVectorNorm
      (complexVecLpNorm (n := n) (ENNReal.ofReal p)) :=
    complexVecLpNorm_isComplexVectorNorm (ENNReal.ofReal p)
  have hqNorm : IsComplexVectorNorm
      (complexVecLpNorm (n := n) (ENNReal.ofReal q)) :=
    complexVecLpNorm_isComplexVectorNorm (ENNReal.ofReal q)
  have hTgt := complexVecLpNorm_ratio_max_card_rpow_of_exponent_le
    (n := n) hn (p := q) (q := p) hp hpq
  have hSrc := complexVecLpNorm_ratio_max_one_of_exponent_le
    (n := n) hn (p := q) (q := p) hp hpq
  have h := schneiderStrang_mixedSubordinateMatrixNormRatio_isMax
    (m := n) (n := n) hn hpNorm hqNorm hpNorm hqNorm hTgt hSrc
  simpa [mul_one] using h

/-- Higham, 2nd ed., Chapter 6, equation (6.15), sharp finite square
    matrix p/q ratio:
    `max_{A != 0} ||A||_p / ||A||_q = n^|1/p - 1/q|`, stated for the
    local mixed-subordinate matrix norm-value API. -/
theorem complexMatrixLpNorm_pq_ratio_isMax
    {n : ℕ} (hn : 0 < n) {p q : ℝ} (hp : 1 ≤ p) (hq : 1 ≤ q) :
    IsMaxMixedSubordinateMatrixNormRatioValue
      (complexVecLpNorm (n := n) (ENNReal.ofReal p))
      (complexVecLpNorm (n := n) (ENNReal.ofReal p))
      (complexVecLpNorm (n := n) (ENNReal.ofReal q))
      (complexVecLpNorm (n := n) (ENNReal.ofReal q))
      ((n : ℝ) ^ |p⁻¹ - q⁻¹|) := by
  rcases le_total p q with hpq | hqp
  · have h := complexMatrixLpNorm_ratio_max_card_rpow_of_exponent_ge
      (n := n) hn (p := p) (q := q) hp hpq
    have hp_pos : 0 < p := lt_of_lt_of_le zero_lt_one hp
    have hdiff_nonneg : 0 ≤ p⁻¹ - q⁻¹ := by
      exact sub_nonneg.mpr (inv_anti₀ hp_pos hpq)
    have habs : |p⁻¹ - q⁻¹| = p⁻¹ - q⁻¹ := abs_of_nonneg hdiff_nonneg
    simpa [habs] using h
  · have h := complexMatrixLpNorm_ratio_max_card_rpow_of_exponent_le
      (n := n) hn (p := p) (q := q) hq hqp
    have hq_pos : 0 < q := lt_of_lt_of_le zero_lt_one hq
    have hdiff_nonpos : p⁻¹ - q⁻¹ ≤ 0 := by
      exact sub_nonpos.mpr (inv_anti₀ hq_pos hqp)
    have habs : |p⁻¹ - q⁻¹| = q⁻¹ - p⁻¹ := by
      rw [abs_of_nonpos hdiff_nonpos]
      ring
    simpa [habs] using h
end NumStability
