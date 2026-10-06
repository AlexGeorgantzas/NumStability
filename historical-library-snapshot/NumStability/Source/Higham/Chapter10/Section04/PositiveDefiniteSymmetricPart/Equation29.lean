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
import NumStability.Algorithms.LinearSystems.Cholesky.ErrorAnalysis.Certificates
import NumStability.Algorithms.LinearSystems.Cholesky.Perturbation.Basic
import NumStability.Algorithms.LinearSystems.LU.NonsymmetricPositiveDefinite.Basic
import NumStability.Algorithms.LinearSystems.Triangular.BackSubstitution
import NumStability.Algorithms.LinearSystems.Triangular.ForwardSubstitution
import NumStability.Analysis.MatrixNorms.SpectralExtrema.Basic
import NumStability.Analysis.MatrixSpectral
import NumStability.Analysis.Rounding
import NumStability.Analysis.SubtractionFold
import NumStability.Analysis.Summation.ErrorBounds
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
import NumStability.Source.Higham.Chapter10.Section02.ErrorAnalysis.Basic
import NumStability.Source.Higham.Chapter10.Section04.PositiveDefiniteSymmetricPart.Endpoints

/-!
# Chapter10 Section04 PositiveDefiniteSymmetricPart Equation29

Canonical destination for material split out of
`NumStability.Algorithms.Cholesky.Higham1029Source` by wave W03 of the August 2026 repository reorganization.
Declaration names, statements and proofs are unchanged; only the
module they live in has changed. The historical module still
resolves and re-exports this one.
-/

open scoped BigOperators

namespace NumStability

open Matrix in
/-- The row and column Gram forms agree for a matrix whose symmetric part has
a two-sided inverse.  Both equal `A_S + A_Kᵀ A_S⁻¹ A_K`. -/
theorem higham10_29_rowGram_eq_colGram {n : ℕ}
    (A Hinv : Fin n → Fin n → ℝ)
    (hRight : IsRightInverse n (symmetricPart n A) Hinv)
    (hLeft : IsLeftInverse n (symmetricPart n A) Hinv) :
    matMul n (matMul n A Hinv) (fun i j => A j i) =
      matMul n (matMul n (fun i j => A j i) Hinv) A := by
  let Amat : Matrix (Fin n) (Fin n) ℝ := Matrix.of A
  let H : Matrix (Fin n) (Fin n) ℝ := Matrix.of (symmetricPart n A)
  let K : Matrix (Fin n) (Fin n) ℝ := Matrix.of (skewSymmetricPart n A)
  let HinvM : Matrix (Fin n) (Fin n) ℝ := Matrix.of Hinv
  have hA : Amat = H + K := by
    ext i j
    exact higham10_29_symmetric_skew_decomposition n A i j
  have hHsym : Hᵀ = H := by
    ext i j
    exact symmetricPart_symmetric n A j i
  have hKskew : Kᵀ = -K := by
    ext i j
    simp [K, skewSymmetricPart]
    ring
  have hRH : H * HinvM = 1 := by
    ext i j
    simpa [H, HinvM, Matrix.mul_apply, Matrix.one_apply] using hRight i j
  have hLH : HinvM * H = 1 := by
    ext i j
    simpa [H, HinvM, Matrix.mul_apply, Matrix.one_apply] using hLeft i j
  have hcol := symPart_skew_inverse_identity Amat H K HinvM
    hA hHsym hKskew hRH hLH
  have hAT : Amatᵀ = H + (-K) := by
    rw [hA, Matrix.transpose_add, hHsym, hKskew]
  have hminusKskew : (-K)ᵀ = -(-K) := by
    rw [Matrix.transpose_neg, hKskew]
  have hrow := symPart_skew_inverse_identity Amatᵀ H (-K) HinvM
    hAT hHsym hminusKskew hRH hLH
  have hRHS : H + (-K)ᵀ * HinvM * (-K) = H + Kᵀ * HinvM * K := by
    rw [Matrix.transpose_neg, hKskew]
    simp
  rw [hRHS] at hrow
  have hrow' : Amat * HinvM * Amatᵀ = H + Kᵀ * HinvM * K := by
    simpa using hrow
  have heq : Amat * HinvM * Amatᵀ = Amatᵀ * HinvM * Amat := by
    rw [hrow', hcol]
  ext i j
  simpa [Amat, HinvM, matMul, Matrix.mul_apply] using
    congrArg (fun M => M i j) heq

/-- Function-shaped quadratic form agrees with its expanded double sum. -/
theorem higham10_29_quadForm_action_eq {n : ℕ}
    (M : Fin n → Fin n → ℝ) (x : Fin n → ℝ) :
    (∑ i : Fin n, x i * matMulVec n M x i) =
      ∑ i : Fin n, ∑ j : Fin n, x i * M i j * x j := by
  refine Finset.sum_congr rfl fun i _ => ?_
  unfold matMulVec
  rw [Finset.mul_sum]
  exact Finset.sum_congr rfl fun j _ => by ring

/-- A congruence Gram matrix has nonnegative largest eigenvalue when the
middle matrix has nonnegative quadratic form. -/
theorem higham10_29_finiteMaxEigenvalue_gram_conj_nonneg {n : ℕ}
    (hn : 0 < n) (M G : Fin n → Fin n → ℝ)
    (hMsym : ∀ i j : Fin n, M i j = M j i)
    (hMpsd : ∀ z : Fin n → ℝ,
      0 ≤ ∑ i : Fin n, z i * matMulVec n M z i) :
    0 ≤ finiteMaxEigenvalue hn
      (matMul n (matMul n (fun i j => G j i) M) G)
      (gram_conj_isSymm M G hMsym) := by
  let k0 : Fin n := ⟨0, hn⟩
  let e : Fin n → ℝ := fun i => if i = k0 then 1 else 0
  have he2 : ∑ i : Fin n, e i ^ 2 = 1 := by
    rw [Finset.sum_eq_single k0]
    · simp [e]
    · intro b _ hb
      simp [e, hb]
    · intro h
      exact absurd (Finset.mem_univ k0) h
  have hqnonneg :
      0 ≤ ∑ i : Fin n, e i *
        matMulVec n (matMul n (matMul n (fun i j => G j i) M) G) e i := by
    rw [quadForm_gram_conj M G e]
    exact hMpsd (matMulVec n G e)
  have hray := finiteMaxEigenvalue_rayleigh hn
    (matMul n (matMul n (fun i j => G j i) M) G)
    (gram_conj_isSymm M G hMsym) e
  rw [← higham10_29_quadForm_action_eq, he2, mul_one] at hray
  linarith

/-- The Frobenius norm of the rank-one border contribution at the first LU
step is bounded by the parent stage's source spectral quantity. -/
theorem higham10_29_firstRank_frob_le {n : ℕ} (hn : 0 < n)
    (A Hinv : Fin n → Fin n → ℝ)
    (hA : higham10_4_IsNonsymPosDef n A)
    (hHinvSym : ∀ i j : Fin n, Hinv i j = Hinv j i)
    (hRight : IsRightInverse n (symmetricPart n A) Hinv)
    (hLeft : IsLeftInverse n (symmetricPart n A) Hinv) :
    frobNorm (fun i j =>
      |A i ⟨0, hn⟩ / A ⟨0, hn⟩ ⟨0, hn⟩| * |A ⟨0, hn⟩ j|) ≤
      finiteMaxEigenvalue hn
        (matMul n (matMul n (fun i j => A j i) Hinv) A)
        (gram_conj_isSymm Hinv A hHinvSym) := by
  let H : Fin n → Fin n → ℝ := symmetricPart n A
  let Q : Fin n → Fin n → ℝ :=
    matMul n (matMul n (fun i j => A j i) Hinv) A
  let c : ℝ := finiteMaxEigenvalue hn Q
    (gram_conj_isSymm Hinv A hHinvSym)
  let k0 : Fin n := ⟨0, hn⟩
  let col : Fin n → ℝ := fun i => A i k0
  let row : Fin n → ℝ := fun j => A k0 j
  let zcol : Fin n → ℝ := matMulVec n (fun i j => A j i) col
  let zrow : Fin n → ℝ := matMulVec n A row
  have hHpd : IsSymPosDef n H := by
    simpa [H] using (higham10_29_nonsymPosDef_iff_symPartSPD n A).mp hA
  have hHsym : ∀ i j : Fin n, H i j = H j i := hHpd.1
  have hHinvPSD : ∀ z : Fin n → ℝ,
      0 ≤ ∑ i : Fin n, ∑ j : Fin n, z i * Hinv i j * z j := by
    intro z
    rw [← higham10_29_quadForm_action_eq]
    exact spd_inv_quadForm_nonneg H Hinv hHpd hRight z
  have hHinvPSDact : ∀ z : Fin n → ℝ,
      0 ≤ ∑ i : Fin n, z i * matMulVec n Hinv z i := by
    intro z
    exact spd_inv_quadForm_nonneg H Hinv hHpd hRight z
  have hH00 : H k0 k0 = A k0 k0 := by
    simp [H, symmetricPart]
  have hpivot : 0 < A k0 k0 := nonsymPosDef_diag_pos hA k0
  have hQrow :
      matMul n (matMul n A Hinv) (fun i j => A j i) = Q := by
    simpa [Q] using higham10_29_rowGram_eq_colGram A Hinv hRight hLeft
  have hc : 0 ≤ c := by
    exact higham10_29_finiteMaxEigenvalue_gram_conj_nonneg hn Hinv A
      hHinvSym hHinvPSDact
  have hzcol0 : zcol k0 = vecNorm2Sq col := by
    unfold zcol col matMulVec vecNorm2Sq
    exact Finset.sum_congr rfl fun i _ => by ring
  have hzrow0 : zrow k0 = vecNorm2Sq row := by
    unfold zrow row matMulVec vecNorm2Sq
    exact Finset.sum_congr rfl fun i _ => by ring
  have hcolGram :
      (∑ i : Fin n, zcol i * matMulVec n Hinv zcol i) =
        ∑ i : Fin n, col i * matMulVec n Q col i := by
    have h := quadForm_gram_conj Hinv (fun i j => A j i) col
    rw [hQrow] at h
    simpa [zcol] using h.symm
  have hrowGram :
      (∑ i : Fin n, zrow i * matMulVec n Hinv zrow i) =
        ∑ i : Fin n, row i * matMulVec n Q row i := by
    have h := quadForm_gram_conj Hinv A row
    simpa [Q, zrow] using h.symm
  have hcolPivot := spd_pivot_quadForm_bound H Hinv hHsym hHinvSym
    hHinvPSD hRight hLeft k0 zcol
  have hrowPivot := spd_pivot_quadForm_bound H Hinv hHsym hHinvSym
    hHinvPSD hRight hLeft k0 zrow
  rw [← higham10_29_quadForm_action_eq] at hcolPivot hrowPivot
  rw [hH00, hzcol0, hcolGram] at hcolPivot
  rw [hH00, hzrow0, hrowGram] at hrowPivot
  have hcolRay := finiteMaxEigenvalue_rayleigh hn Q
    (gram_conj_isSymm Hinv A hHinvSym) col
  have hrowRay := finiteMaxEigenvalue_rayleigh hn Q
    (gram_conj_isSymm Hinv A hHinvSym) row
  rw [← higham10_29_quadForm_action_eq] at hcolRay hrowRay
  change _ ≤ c * _ at hcolRay hrowRay
  have hcolSq0 : 0 ≤ vecNorm2Sq col := vecNorm2Sq_nonneg col
  have hrowSq0 : 0 ≤ vecNorm2Sq row := vecNorm2Sq_nonneg row
  have hcolSq_le : vecNorm2Sq col ≤ A k0 k0 * c := by
    have hstep : (vecNorm2Sq col) ^ 2 ≤ A k0 k0 * (c * vecNorm2Sq col) :=
      hcolPivot.trans (mul_le_mul_of_nonneg_left hcolRay hpivot.le)
    rcases eq_or_lt_of_le hcolSq0 with hz | hz
    · rw [← hz]
      exact mul_nonneg hpivot.le hc
    · nlinarith
  have hrowSq_le : vecNorm2Sq row ≤ A k0 k0 * c := by
    have hstep : (vecNorm2Sq row) ^ 2 ≤ A k0 k0 * (c * vecNorm2Sq row) :=
      hrowPivot.trans (mul_le_mul_of_nonneg_left hrowRay hpivot.le)
    rcases eq_or_lt_of_le hrowSq0 with hz | hz
    · rw [← hz]
      exact mul_nonneg hpivot.le hc
    · nlinarith
  have hvnorm : vecNorm2 (fun i => A i k0 / A k0 k0) =
      vecNorm2 col / A k0 k0 := by
    have heq : (fun i => A i k0 / A k0 k0) =
        fun i => (A k0 k0)⁻¹ * col i := by
      funext i
      simp [col, div_eq_mul_inv, mul_comm]
    rw [heq, vecNorm2_smul, abs_of_pos (inv_pos.mpr hpivot)]
    field_simp
  have hprodSq :
      (vecNorm2 (fun i => A i k0 / A k0 k0) * vecNorm2 row) ^ 2 ≤
        c ^ 2 := by
    rw [hvnorm]
    have hmul : vecNorm2Sq col * vecNorm2Sq row ≤
        (A k0 k0 * c) * (A k0 k0 * c) :=
      mul_le_mul hcolSq_le hrowSq_le hrowSq0 (mul_nonneg hpivot.le hc)
    rw [← vecNorm2_sq, ← vecNorm2_sq] at hmul
    have hpiv_ne : A k0 k0 ≠ 0 := ne_of_gt hpivot
    calc
      (vecNorm2 col / A k0 k0 * vecNorm2 row) ^ 2
          = (vecNorm2 col ^ 2 * vecNorm2 row ^ 2) / (A k0 k0) ^ 2 := by ring
      _ ≤ ((A k0 k0 * c) * (A k0 k0 * c)) / (A k0 k0) ^ 2 :=
        div_le_div_of_nonneg_right hmul (sq_nonneg _)
      _ = c ^ 2 := by field_simp
  have hprod :
      vecNorm2 (fun i => A i k0 / A k0 k0) * vecNorm2 row ≤ c := by
    have hnonneg : 0 ≤
        vecNorm2 (fun i : Fin n => A i k0 / A k0 k0) * vecNorm2 row :=
      mul_nonneg (vecNorm2_nonneg (fun i : Fin n => A i k0 / A k0 k0))
        (vecNorm2_nonneg row)
    nlinarith
  rw [frobNorm_rankOne]
  rw [vecNorm2_abs, vecNorm2_abs]
  simpa [row, c, Q] using hprod

/-- Entrywise product `|L||U|` from equation (10.29). -/
noncomputable def higham10_29_absLUProduct {n : ℕ}
    (L U : Fin n → Fin n → ℝ) : Fin n → Fin n → ℝ :=
  fun i j => ∑ k : Fin n, |L i k| * |U k j|

/-- Embed a child-stage square matrix in the trailing block, padding its first
row and column by zero. -/
noncomputable def higham10_29_tailPad {m : ℕ}
    (P : Fin m → Fin m → ℝ) : Fin (m + 1) → Fin (m + 1) → ℝ :=
  fun i j =>
    if hi : i = 0 then 0
    else if hj : j = 0 then 0
    else P (i.pred hi) (j.pred hj)

/-- Zero-padding a trailing block preserves its Frobenius norm. -/
theorem higham10_29_tailPad_frobNorm {m : ℕ}
    (P : Fin m → Fin m → ℝ) :
    frobNorm (higham10_29_tailPad P) = frobNorm P := by
  rw [frobNorm_eq_sqrt_frobNormSq, frobNorm_eq_sqrt_frobNormSq]
  congr 1
  simp [frobNormSq, higham10_29_tailPad, Fin.sum_univ_succ]

/-- Exact first-step decomposition of `|L||U|`: the pivot border contributes
one rank-one matrix and all child contributions occupy the trailing block. -/
theorem higham10_29_absLUProduct_firstStep {m : ℕ}
    (A : Fin (m + 1) → Fin (m + 1) → ℝ)
    (hpivot : A 0 0 ≠ 0)
    (L₁ U₁ : Fin m → Fin m → ℝ) :
    higham10_29_absLUProduct (luFirstStepL A L₁) (luFirstStepU A U₁) =
      fun i j =>
        |A i 0 / A 0 0| * |A 0 j| +
          higham10_29_tailPad (higham10_29_absLUProduct L₁ U₁) i j := by
  funext i j
  unfold higham10_29_absLUProduct
  rw [Fin.sum_univ_succ]
  by_cases hi : i = 0
  · subst i
    simp [luFirstStepL, luFirstStepU, higham10_29_tailPad, hpivot]
  · by_cases hj : j = 0
    · subst j
      simp [luFirstStepL, luFirstStepU, higham10_29_tailPad, hi]
    · simp [luFirstStepL, luFirstStepU, higham10_29_tailPad, hi, hj]

/-- Frobenius triangle inequality applied to the exact first-step
decomposition. -/
theorem higham10_29_absLUProduct_firstStep_frobNorm_le {m : ℕ}
    (A : Fin (m + 1) → Fin (m + 1) → ℝ)
    (hpivot : A 0 0 ≠ 0)
    (L₁ U₁ : Fin m → Fin m → ℝ) :
    frobNorm
        (higham10_29_absLUProduct (luFirstStepL A L₁) (luFirstStepU A U₁)) ≤
      frobNorm (fun i j => |A i 0 / A 0 0| * |A 0 j|) +
        frobNorm (higham10_29_absLUProduct L₁ U₁) := by
  rw [higham10_29_absLUProduct_firstStep A hpivot L₁ U₁]
  exact (frobNorm_add_le _ _).trans_eq
    (congrArg
      (fun x => frobNorm (fun i j => |A i 0 / A 0 0| * |A 0 j|) + x)
      (higham10_29_tailPad_frobNorm (higham10_29_absLUProduct L₁ U₁)))

/-- A matrix with positive-definite symmetric part has nonzero determinant.
This determinant form lets exact-LU uniqueness transfer the recursively
constructed estimate to an arbitrary exact `LUFactSpec`. -/
theorem higham10_29_nonsymPosDef_det_ne_zero {n : ℕ}
    (A : Fin n → Fin n → ℝ)
    (hA : higham10_4_IsNonsymPosDef n A) :
    Matrix.det (Matrix.of A : Matrix (Fin n) (Fin n) ℝ) ≠ 0 := by
  let M : Matrix (Fin n) (Fin n) ℝ := Matrix.of A
  have hM_inj : Function.Injective M.mulVec := by
    intro x y hxy
    by_contra hne
    have hdiff_ne : ∃ i : Fin n, x i - y i ≠ 0 := by
      by_contra hall
      push_neg at hall
      apply hne
      funext i
      exact sub_eq_zero.mp (hall i)
    obtain ⟨i, hi⟩ :=
      nonsymPosDef_mulVec_ne_zero hA (fun j => x j - y j) hdiff_ne
    apply hi
    calc
      (∑ j : Fin n, A i j * (x j - y j)) =
          M.mulVec x i - M.mulVec y i := by
        simp only [M, Matrix.mulVec, Matrix.of_apply, dotProduct]
        rw [← Finset.sum_sub_distrib]
        exact Finset.sum_congr rfl fun j _ => by ring
      _ = 0 := sub_eq_zero.mpr (congrFun hxy i)
  have hunitM : IsUnit M := Matrix.mulVec_injective_iff_isUnit.mp hM_inj
  have hdetUnit : IsUnit M.det := (Matrix.isUnit_iff_isUnit_det M).mp hunitM
  have hdetNe : M.det ≠ 0 := isUnit_iff_ne_zero.mp hdetUnit
  simpa [M] using hdetNe

/-- The matrix printed on the right of equation (10.29):
`A_S + A_Kᵀ A_S⁻¹ A_K`. -/
noncomputable def higham10_29_sourceMatrix {n : ℕ}
    (A Hinv : Fin n → Fin n → ℝ) : Fin n → Fin n → ℝ :=
  fun i j => symmetricPart n A i j +
    matMul n
      (matMul n (fun a b => skewSymmetricPart n A b a) Hinv)
      (skewSymmetricPart n A) i j

open Matrix in
/-- Exact algebraic identity behind the source form of (10.29):
`Aᵀ A_S⁻¹ A = A_S + A_Kᵀ A_S⁻¹ A_K`. -/
theorem higham10_29_gram_eq_sourceMatrix {n : ℕ}
    (A Hinv : Fin n → Fin n → ℝ)
    (hRight : IsRightInverse n (symmetricPart n A) Hinv)
    (hLeft : IsLeftInverse n (symmetricPart n A) Hinv) :
    matMul n (matMul n (fun i j => A j i) Hinv) A =
      higham10_29_sourceMatrix A Hinv := by
  let Amat : Matrix (Fin n) (Fin n) ℝ := Matrix.of A
  let H : Matrix (Fin n) (Fin n) ℝ := Matrix.of (symmetricPart n A)
  let K : Matrix (Fin n) (Fin n) ℝ := Matrix.of (skewSymmetricPart n A)
  let HinvM : Matrix (Fin n) (Fin n) ℝ := Matrix.of Hinv
  have hA : Amat = H + K := by
    ext i j
    exact higham10_29_symmetric_skew_decomposition n A i j
  have hHsym : Hᵀ = H := by
    ext i j
    exact symmetricPart_symmetric n A j i
  have hKskew : Kᵀ = -K := by
    ext i j
    simp [K, skewSymmetricPart]
    ring
  have hRH : H * HinvM = 1 := by
    ext i j
    simpa [H, HinvM, Matrix.mul_apply, Matrix.one_apply] using hRight i j
  have hLH : HinvM * H = 1 := by
    ext i j
    simpa [H, HinvM, Matrix.mul_apply, Matrix.one_apply] using hLeft i j
  have hidentity :=
    symPart_skew_inverse_identity Amat H K HinvM hA hHsym hKskew hRH hLH
  ext i j
  simpa [Amat, H, K, HinvM, higham10_29_sourceMatrix, matMul,
    Matrix.mul_apply] using congrArg (fun M => M i j) hidentity

/-- The printed source matrix in (10.29) is symmetric. -/
theorem higham10_29_sourceMatrix_isSymm {n : ℕ}
    (A Hinv : Fin n → Fin n → ℝ)
    (hHinvSym : ∀ i j : Fin n, Hinv i j = Hinv j i)
    (hRight : IsRightInverse n (symmetricPart n A) Hinv)
    (hLeft : IsLeftInverse n (symmetricPart n A) Hinv) :
    ∀ i j : Fin n, higham10_29_sourceMatrix A Hinv i j =
      higham10_29_sourceMatrix A Hinv j i := by
  rw [← higham10_29_gram_eq_sourceMatrix A Hinv hRight hLeft]
  exact gram_conj_isSymm Hinv A hHinvSym

/-- Largest eigenvalue is invariant under equality of symmetric finite
matrices; the explicit lemma handles the dependent symmetry certificates. -/
theorem finiteMaxEigenvalue_congr {n : ℕ} (hn : 0 < n)
    (M N : Fin n → Fin n → ℝ)
    (hM : IsSymmetricFiniteMatrix M)
    (hN : IsSymmetricFiniteMatrix N) (hMN : M = N) :
    finiteMaxEigenvalue hn M hM = finiteMaxEigenvalue hn N hN := by
  subst N
  rfl

end NumStability
