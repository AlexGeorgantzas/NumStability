/-
  Algorithms/Ch10ComplexPositiveDefiniteSourceClosure.lean

  Source closure for the complex-symmetric matrices discussed after (10.30).
  The printed growth theorem applies when both real and imaginary parts are
  symmetric positive definite.  This file also records a concrete obstruction
  to weakening the imaginary-part hypothesis to symmetry alone.
-/

import NumStability.Algorithms.HighamChapter10
import NumStability.Algorithms.ComplexBackwardError
import NumStability.Analysis.ComplexArithmetic
import NumStability.Analysis.MatrixAlgebra
import Mathlib.Data.Complex.BigOperators

namespace NumStability

open scoped BigOperators

/-! ## The missing hypothesis cannot be dropped -/

/-- The positive-definite real part in the two-by-two discrepancy witness. -/
def higham10_30_relaxedCounterB : Fin 2 → Fin 2 → ℝ :=
  fun i j => if i = j then 1 else 0

/-- A symmetric, but indefinite, imaginary part. -/
def higham10_30_relaxedCounterC : Fin 2 → Fin 2 → ℝ :=
  fun i j => if i = j then 0 else 4

/-- Exact lower factor produced by no-pivot elimination on the witness. -/
noncomputable def higham10_30_relaxedCounterL : Fin 2 → Fin 2 → ℂ :=
  fun i j =>
    if i = 0 ∧ j = 0 then 1
    else if i = 1 ∧ j = 0 then 4 * Complex.I
    else if i = 1 ∧ j = 1 then 1
    else 0

/-- Exact upper factor produced by no-pivot elimination on the witness. -/
noncomputable def higham10_30_relaxedCounterU : Fin 2 → Fin 2 → ℂ :=
  fun i j =>
    if i = 0 ∧ j = 0 then 1
    else if i = 0 ∧ j = 1 then 4 * Complex.I
    else if i = 1 ∧ j = 1 then 17
    else 0

theorem higham10_30_relaxedCounterB_spd :
    IsSymPosDef 2 higham10_30_relaxedCounterB := by
  constructor
  · intro i j
    simp only [higham10_30_relaxedCounterB]
    by_cases h : i = j
    · simp [h]
    · have h' : j ≠ i := fun hji => h hji.symm
      simp [h, h']
  · intro x hx
    simp only [Fin.sum_univ_two, higham10_30_relaxedCounterB]
    simp only [ite_true, Fin.zero_ne_one, ite_false]
    rcases hx with ⟨i, hi⟩
    fin_cases i
    · simp_all
      nlinarith [mul_self_pos.mpr hi, sq_nonneg (x 1)]
    · simp_all
      nlinarith [sq_nonneg (x 0), mul_self_pos.mpr hi]

theorem higham10_30_relaxedCounterC_symmetric :
    ∀ i j, higham10_30_relaxedCounterC i j = higham10_30_relaxedCounterC j i := by
  intro i j
  simp only [higham10_30_relaxedCounterC]
  by_cases h : i = j
  · simp [h]
  · have h' : j ≠ i := fun hji => h hji.symm
    simp [h, h']

theorem higham10_30_relaxedCounter_exact_lu :
    higham9_8_ComplexLUFactSpec 2
      (higham10_30_complexPositiveDefiniteForm 2
        higham10_30_relaxedCounterB higham10_30_relaxedCounterC)
      higham10_30_relaxedCounterL higham10_30_relaxedCounterU := by
  refine ⟨?_, ?_, ?_, ?_⟩
  · intro i
    fin_cases i <;>
      norm_num [higham10_30_relaxedCounterL]
  · intro i j hij
    fin_cases i <;> fin_cases j <;>
      simp_all [higham10_30_relaxedCounterL]
  · intro i j hij
    fin_cases i <;> fin_cases j <;>
      simp_all [higham10_30_relaxedCounterU]
  · intro i j
    fin_cases i
    · fin_cases j
      · norm_num [Fin.sum_univ_two, higham10_30_relaxedCounterB,
          higham10_30_relaxedCounterC, higham10_30_relaxedCounterL,
          higham10_30_relaxedCounterU,
          higham10_30_complexPositiveDefiniteForm]
      · norm_num [Fin.sum_univ_two, higham10_30_relaxedCounterB,
          higham10_30_relaxedCounterC, higham10_30_relaxedCounterL,
          higham10_30_relaxedCounterU,
          higham10_30_complexPositiveDefiniteForm]
        ring
    · fin_cases j
      · norm_num [Fin.sum_univ_two, higham10_30_relaxedCounterB,
          higham10_30_relaxedCounterC, higham10_30_relaxedCounterL,
          higham10_30_relaxedCounterU,
          higham10_30_complexPositiveDefiniteForm]
        ring
      · norm_num [Fin.sum_univ_two, higham10_30_relaxedCounterB,
          higham10_30_relaxedCounterC, higham10_30_relaxedCounterL,
          higham10_30_relaxedCounterU,
          higham10_30_complexPositiveDefiniteForm, Complex.I_sq]
        have hI : (4 : ℂ) * Complex.I * (4 * Complex.I) = -16 := by
          calc
            (4 : ℂ) * Complex.I * (4 * Complex.I) =
                16 * (Complex.I * Complex.I) := by ring
            _ = -16 := by rw [Complex.I_mul_I]; norm_num
        rw [hI]
        norm_num

theorem higham10_30_relaxedCounter_input_max_eq_four :
    higham9_13_complexMaxEntryNorm (by decide : 0 < 2)
      (higham10_30_complexPositiveDefiniteForm 2
        higham10_30_relaxedCounterB higham10_30_relaxedCounterC) = 4 := by
  let A := higham10_30_complexPositiveDefiniteForm 2
    higham10_30_relaxedCounterB higham10_30_relaxedCounterC
  apply le_antisymm
  · apply higham9_13_complexMaxEntryNorm_le_of_entry_le_bound
    intro i j
    fin_cases i <;> fin_cases j <;>
      norm_num [A, higham10_30_complexPositiveDefiniteForm,
        higham10_30_relaxedCounterB, higham10_30_relaxedCounterC,
        norm_mul]
  · have h := higham9_13_entry_norm_le_complexMaxEntryNorm
      (by decide : 0 < 2) A (0 : Fin 2) (1 : Fin 2)
    norm_num [A, higham10_30_complexPositiveDefiniteForm,
      higham10_30_relaxedCounterB, higham10_30_relaxedCounterC,
      norm_mul] at h
    exact h

theorem higham10_30_relaxedCounter_upper_max_eq_seventeen :
    higham9_13_complexMaxEntryNorm (by decide : 0 < 2)
      higham10_30_relaxedCounterU = 17 := by
  apply le_antisymm
  · apply higham9_13_complexMaxEntryNorm_le_of_entry_le_bound
    intro i j
    fin_cases i <;> fin_cases j <;>
      norm_num [higham10_30_relaxedCounterU, norm_mul]
  · have h := higham9_13_entry_norm_le_complexMaxEntryNorm
      (by decide : 0 < 2) higham10_30_relaxedCounterU (1 : Fin 2) (1 : Fin 2)
    norm_num [higham10_30_relaxedCounterU] at h
    exact h

/-- With only `B` positive definite and `C` symmetric, the requested
    `rho < 3` assertion is false: the exact no-pivot upper factor has growth
    `17/4`. -/
theorem higham10_30_relaxedCounter_growth_gt_three :
    3 < higham9_13_complexGrowthFactorEntry (by decide : 0 < 2)
      (higham10_30_complexPositiveDefiniteForm 2
        higham10_30_relaxedCounterB higham10_30_relaxedCounterC)
      higham10_30_relaxedCounterU := by
  rw [higham9_13_complexGrowthFactorEntry,
    higham10_30_relaxedCounter_input_max_eq_four,
    higham10_30_relaxedCounter_upper_max_eq_seventeen]
  norm_num

/-! ## Positive real/imaginary quadratic forms -/

/-- Real quadratic form in the repository's function-shaped matrix style. -/
noncomputable def higham10_30_realQuadForm {n : ℕ}
    (M : Fin n → Fin n → ℝ) (x : Fin n → ℝ) : ℝ :=
  ∑ i : Fin n, ∑ j : Fin n, x i * M i j * x j

/-- Bilinear complex quadratic form `zᴴ A z`. -/
noncomputable def higham10_30_complexQuadForm {n : ℕ}
    (A : Fin n → Fin n → ℂ) (z : Fin n → ℂ) : ℂ :=
  ∑ i : Fin n, ∑ j : Fin n, star (z i) * A i j * z j

private lemma higham10_30_symmetric_cross_sum_eq {n : ℕ}
    (M : Fin n → Fin n → ℝ)
    (hM : ∀ i j, M i j = M j i) (x y : Fin n → ℝ) :
    (∑ i : Fin n, ∑ j : Fin n, y i * M i j * x j) =
      ∑ i : Fin n, ∑ j : Fin n, x i * M i j * y j := by
  calc
    (∑ i : Fin n, ∑ j : Fin n, y i * M i j * x j) =
        ∑ j : Fin n, ∑ i : Fin n, y i * M i j * x j := Finset.sum_comm
    _ = ∑ j : Fin n, ∑ i : Fin n, x j * M j i * y i := by
      apply Finset.sum_congr rfl
      intro j _
      apply Finset.sum_congr rfl
      intro i _
      rw [hM i j]
      ring
    _ = ∑ i : Fin n, ∑ j : Fin n, x i * M i j * y j := by
      rfl

private lemma higham10_30_symmetric_cross_sum_sub_eq_zero {n : ℕ}
    (M : Fin n → Fin n → ℝ)
    (hM : ∀ i j, M i j = M j i) (x y : Fin n → ℝ) :
    (∑ i : Fin n, ∑ j : Fin n,
      (y i * M i j * x j - x i * M i j * y j)) = 0 := by
  simp_rw [Finset.sum_sub_distrib]
  rw [higham10_30_symmetric_cross_sum_eq M hM x y]
  ring

private lemma higham10_30_symmetric_mulVec_cross_eq {n : ℕ}
    (M : Matrix (Fin n) (Fin n) ℝ)
    (hM : ∀ i j, M i j = M j i) (x y : Fin n → ℝ) :
    (∑ i : Fin n, y i * Matrix.mulVec M x i) =
      ∑ i : Fin n, x i * Matrix.mulVec M y i := by
  simp only [Matrix.mulVec, dotProduct]
  calc
    (∑ i : Fin n, y i * ∑ j : Fin n, M i j * x j) =
        ∑ i : Fin n, ∑ j : Fin n, y i * M i j * x j := by
      apply Finset.sum_congr rfl
      intro i _
      rw [Finset.mul_sum]
      apply Finset.sum_congr rfl
      intro j _
      ring
    _ = ∑ i : Fin n, ∑ j : Fin n, x i * M i j * y j :=
      higham10_30_symmetric_cross_sum_eq M hM x y
    _ = ∑ i : Fin n, x i * ∑ j : Fin n, M i j * y j := by
      apply Finset.sum_congr rfl
      intro i _
      rw [Finset.mul_sum]
      apply Finset.sum_congr rfl
      intro j _
      ring

/-- For `A = B + iC`, the real part of `zᴴAz` is the sum of the
    `B`-quadratic forms of the real and imaginary parts of `z`. -/
theorem higham10_30_complexQuadForm_re {n : ℕ}
    (B C : Fin n → Fin n → ℝ)
    (hC : ∀ i j, C i j = C j i) (z : Fin n → ℂ) :
    (higham10_30_complexQuadForm
      (higham10_30_complexPositiveDefiniteForm n B C) z).re =
      higham10_30_realQuadForm B (fun i => (z i).re) +
        higham10_30_realQuadForm B (fun i => (z i).im) := by
  have hcross := higham10_30_symmetric_cross_sum_sub_eq_zero C hC
    (fun i => (z i).re) (fun i => (z i).im)
  unfold higham10_30_complexQuadForm higham10_30_realQuadForm
    higham10_30_complexPositiveDefiniteForm
  simp_rw [Complex.re_sum]
  simp [Complex.mul_re, Complex.mul_im]
  simp_rw [add_mul, Finset.sum_add_distrib]
  simp_rw [Finset.sum_sub_distrib] at hcross
  ring_nf at hcross ⊢
  simp_rw [Finset.sum_neg_distrib]
  linarith

/-- The imaginary part of `zᴴAz` is the analogous sum of `C`-quadratic
    forms. -/
theorem higham10_30_complexQuadForm_im {n : ℕ}
    (B C : Fin n → Fin n → ℝ)
    (hB : ∀ i j, B i j = B j i) (z : Fin n → ℂ) :
    (higham10_30_complexQuadForm
      (higham10_30_complexPositiveDefiniteForm n B C) z).im =
      higham10_30_realQuadForm C (fun i => (z i).re) +
        higham10_30_realQuadForm C (fun i => (z i).im) := by
  have hcross := higham10_30_symmetric_cross_sum_sub_eq_zero B hB
    (fun i => (z i).re) (fun i => (z i).im)
  unfold higham10_30_complexQuadForm higham10_30_realQuadForm
    higham10_30_complexPositiveDefiniteForm
  simp_rw [Complex.im_sum]
  simp [Complex.mul_re, Complex.mul_im]
  simp_rw [add_mul, Finset.sum_add_distrib]
  simp_rw [Finset.sum_sub_distrib] at hcross
  ring_nf at hcross ⊢
  simp_rw [Finset.sum_neg_distrib]
  linarith

private lemma higham10_30_realQuadForm_nonneg_of_spd {n : ℕ}
    {B : Fin n → Fin n → ℝ} (hB : IsSymPosDef n B)
    (x : Fin n → ℝ) : 0 ≤ higham10_30_realQuadForm B x := by
  by_cases hx : ∃ i, x i ≠ 0
  · exact (hB.2 x hx).le
  · push_neg at hx
    simp [higham10_30_realQuadForm, hx]

private lemma higham10_30_complexVector_re_or_im_nonzero {n : ℕ}
    {z : Fin n → ℂ} (hz : z ≠ 0) :
    (∃ i, (z i).re ≠ 0) ∨ (∃ i, (z i).im ≠ 0) := by
  by_contra h
  push_neg at h
  apply hz
  funext i
  apply Complex.ext
  · simpa using h.1 i
  · simpa using h.2 i

/-- A complex matrix whose real part is real SPD is nonsingular.  Symmetry of
    `C` is used only to make its contribution to `Re(zᴴAz)` cancel. -/
theorem higham10_30_det_ne_zero_of_real_spd {n : ℕ}
    (B C : Fin n → Fin n → ℝ)
    (hB : IsSymPosDef n B)
    (hC : ∀ i j, C i j = C j i) :
    Matrix.det
      (Matrix.of (higham10_30_complexPositiveDefiniteForm n B C) :
        Matrix (Fin n) (Fin n) ℂ) ≠ 0 := by
  classical
  intro hdet
  obtain ⟨z, hz, hAz⟩ := Matrix.exists_mulVec_eq_zero_iff.mpr hdet
  have hqzero :
      higham10_30_complexQuadForm
        (higham10_30_complexPositiveDefiniteForm n B C) z = 0 := by
    unfold higham10_30_complexQuadForm
    have hrow : ∀ i : Fin n,
        (∑ j : Fin n,
          higham10_30_complexPositiveDefiniteForm n B C i j * z j) = 0 := by
      intro i
      have hi := congrFun hAz i
      simpa [Matrix.mulVec, dotProduct] using hi
    calc
      (∑ i : Fin n, ∑ j : Fin n,
          star (z i) * higham10_30_complexPositiveDefiniteForm n B C i j * z j) =
          ∑ i : Fin n, star (z i) *
            (∑ j : Fin n,
              higham10_30_complexPositiveDefiniteForm n B C i j * z j) := by
            apply Finset.sum_congr rfl
            intro i _
            rw [Finset.mul_sum]
            apply Finset.sum_congr rfl
            intro j _
            ring
      _ = 0 := by simp [hrow]
  have hre :
      higham10_30_realQuadForm B (fun i => (z i).re) +
        higham10_30_realQuadForm B (fun i => (z i).im) = 0 := by
    have := congrArg Complex.re hqzero
    simpa [higham10_30_complexQuadForm_re B C hC z] using this
  rcases higham10_30_complexVector_re_or_im_nonzero hz with hre_ne | him_ne
  · have hpos := hB.2 (fun i => (z i).re) hre_ne
    change 0 < higham10_30_realQuadForm B (fun i => (z i).re) at hpos
    have hnonneg := higham10_30_realQuadForm_nonneg_of_spd hB (fun i => (z i).im)
    linarith
  · have hnonneg := higham10_30_realQuadForm_nonneg_of_spd hB (fun i => (z i).re)
    have hpos := hB.2 (fun i => (z i).im) him_ne
    change 0 < higham10_30_realQuadForm B (fun i => (z i).im) at hpos
    linarith

/-! ## Leading blocks and exact no-pivot LU -/

/-- The leading principal restriction of a real matrix. -/
noncomputable def higham10_30_leadingRealBlock {n : ℕ}
    (M : Fin n → Fin n → ℝ) (k : ℕ) (hk : k ≤ n) :
    Fin k → Fin k → ℝ :=
  fun i j => M (Fin.castLE hk i) (Fin.castLE hk j)

private theorem higham10_30_matrixPosDef_to_isSymPosDef {n : ℕ}
    (A : Fin n → Fin n → ℝ)
    (hA : Matrix.PosDef (A : Matrix (Fin n) (Fin n) ℝ)) :
    IsSymPosDef n A := by
  constructor
  · intro i j
    have hherm := hA.1.eq
    have hij := congrArg (fun M : Matrix (Fin n) (Fin n) ℝ => M i j) hherm
    simpa using hij.symm
  · intro x hx
    have hxne : x ≠ 0 := by
      intro hzero
      obtain ⟨i, hi⟩ := hx
      exact hi (congrFun hzero i)
    have hpos := hA.dotProduct_mulVec_pos hxne
    simpa [dotProduct, Matrix.mulVec, Finset.mul_sum,
      Finset.sum_mul, mul_assoc] using hpos

/-- Every leading principal block of an SPD matrix is SPD. -/
theorem higham10_30_leadingRealBlock_spd {n k : ℕ}
    (B : Fin n → Fin n → ℝ) (hB : IsSymPosDef n B) (hk : k ≤ n) :
    IsSymPosDef k (higham10_30_leadingRealBlock B k hk) := by
  exact higham10_30_matrixPosDef_to_isSymPosDef _
    (matrix_posDef_submatrix_of_injective
      (isSymPosDef_to_matrix_posDef B hB)
      (Fin.castLE hk) (Fin.castLE_injective hk))

/-- Every leading principal block of `B + iC` is nonsingular when `B` is
    positive definite and `C` is symmetric. -/
theorem higham10_30_leadingComplexBlock_det_ne_zero {n : ℕ}
    (B C : Fin n → Fin n → ℝ)
    (hB : IsSymPosDef n B)
    (hC : ∀ i j, C i j = C j i)
    (k : ℕ) (hk : k ≤ n) :
    Matrix.det
      (fun i j : Fin k =>
        higham10_30_complexPositiveDefiniteForm n B C
          (Fin.castLE hk i) (Fin.castLE hk j)) ≠ 0 := by
  let Bk := higham10_30_leadingRealBlock B k hk
  let Ck := higham10_30_leadingRealBlock C k hk
  have hBk : IsSymPosDef k Bk := by
    simpa [Bk] using higham10_30_leadingRealBlock_spd B hB hk
  have hCk : ∀ i j, Ck i j = Ck j i := by
    intro i j
    exact hC _ _
  simpa [Bk, Ck, higham10_30_leadingRealBlock,
    higham10_30_complexPositiveDefiniteForm] using
      higham10_30_det_ne_zero_of_real_spd Bk Ck hBk hCk

/-- Complex analogue of Theorem 9.1's existence direction: nonvanishing
    leading principal minors give an exact unit-lower/upper no-pivot LU
    certificate. -/
theorem higham10_30_complexLU_exists_of_leadingPrincipalBlock_det_ne_zero :
    ∀ n : ℕ, ∀ A : Fin n → Fin n → ℂ,
      (∀ k : ℕ, ∀ hk : k ≤ n,
        Matrix.det
          (fun i j : Fin k => A (Fin.castLE hk i) (Fin.castLE hk j)) ≠ 0) →
      ∃ L U : Fin n → Fin n → ℂ,
        higham9_8_ComplexLUFactSpec n A L U := by
  intro n
  induction n with
  | zero =>
      intro A _hlead
      refine ⟨A, A, ?_⟩
      exact
        { L_diag := fun i => i.elim0
          L_upper_zero := fun i => i.elim0
          U_lower_zero := fun i => i.elim0
          product_eq := fun i => i.elim0 }
  | succ m ih =>
      intro A hlead
      have h1le : (1 : ℕ) ≤ m + 1 := by omega
      have hpivot : A 0 0 ≠ 0 := by
        have hdet := hlead 1 h1le
        simpa using hdet
      let S : Fin m → Fin m → ℂ :=
        higham9_8_complexFirstSchurComplement A
      have hSlead : ∀ k : ℕ, ∀ hk : k ≤ m,
          Matrix.det
            (fun i j : Fin k => S (Fin.castLE hk i) (Fin.castLE hk j)) ≠ 0 := by
        intro k hk
        by_cases hk0 : k = 0
        · subst k
          simp
        · have hk1 : k + 1 ≤ m + 1 := by omega
          let Ak : Fin (k + 1) → Fin (k + 1) → ℂ :=
            fun i j => A (Fin.castLE hk1 i) (Fin.castLE hk1 j)
          have hpivotAk : Ak 0 0 ≠ 0 := by
            simpa [Ak, Fin.castLE] using hpivot
          have hdetAk :
              Matrix.det (Matrix.of Ak : Matrix (Fin (k + 1)) (Fin (k + 1)) ℂ) ≠ 0 := by
            simpa [Ak] using hlead (k + 1) hk1
          have hdetSchur :=
            higham9_8_complexFirstSchurComplement_det_ne_zero
              Ak hpivotAk hdetAk
          simpa [S, Ak, higham9_8_complexFirstSchurComplement,
            Fin.castLE] using hdetSchur
      obtain ⟨L₁, U₁, hLU₁⟩ := ih S hSlead
      exact
        ⟨higham9_8_complexLUFirstStepL A L₁,
          higham9_8_complexLUFirstStepU A U₁,
          higham9_8_complexLUFactSpec_of_firstSchurComplement_explicit
            hpivot hLU₁⟩

/-- The matrices in (10.30) have an exact no-pivot LU factorization.  The
    proof uses no success premise: positive definiteness supplies every
    nonzero leading pivot. -/
theorem higham10_30_complexPositiveDefinite_exists_noPivotLU {n : ℕ}
    (B C : Fin n → Fin n → ℝ)
    (hB : IsSymPosDef n B)
    (hC : IsSymPosDef n C) :
    ∃ L U : Fin n → Fin n → ℂ,
      higham9_8_ComplexLUFactSpec n
        (higham10_30_complexPositiveDefiniteForm n B C) L U := by
  apply higham10_30_complexLU_exists_of_leadingPrincipalBlock_det_ne_zero n
    (higham10_30_complexPositiveDefiniteForm n B C)
  intro k hk
  exact higham10_30_leadingComplexBlock_det_ne_zero B C hB hC.1 k hk

/-! ## The inverse-order estimate used in the George--Ikramov--Kucherov proof -/

/-- Inversion reverses Loewner order on finite real positive-definite
    matrices.  The proof is the standard two-Schur-complement block argument. -/
private theorem higham10_30_posDef_inverse_anti
    {ι : Type*} [Fintype ι] [DecidableEq ι]
    {P Q : Matrix ι ι ℝ}
    (hP : Matrix.PosDef P) (hQ : Matrix.PosDef Q)
    (hPQ : (P - Q).PosSemidef) :
    (Q⁻¹ - P⁻¹).PosSemidef := by
  letI := hP.isUnit.invertible
  letI := hQ.isUnit.invertible
  have hblock' :
      (Matrix.fromBlocks P (1 : Matrix ι ι ℝ)
        (Matrix.conjTranspose (1 : Matrix ι ι ℝ)) Q⁻¹).PosSemidef := by
    rw [Matrix.PosDef.fromBlocks₂₂
      (A := P) (B := (1 : Matrix ι ι ℝ)) hQ.inv]
    simpa using hPQ
  have hblock :
      (Matrix.fromBlocks P (1 : Matrix ι ι ℝ)
        (1 : Matrix ι ι ℝ) Q⁻¹).PosSemidef := by
    simpa using hblock'
  have hschur :=
    (Matrix.PosDef.fromBlocks₁₁
      (B := (1 : Matrix ι ι ℝ)) (D := Q⁻¹) hP).mp
      (by simpa using hblock)
  simpa using hschur

/-- The real inverse estimate in the published proof:
    `(B + C B⁻¹ C)⁻¹ ≤ (1/2) C⁻¹`. -/
private theorem higham10_30_inverse_real_part_upper
    {ι : Type*} [Fintype ι] [DecidableEq ι]
    {B C : Matrix ι ι ℝ}
    (hB : Matrix.PosDef B) (hC : Matrix.PosDef C) :
    (((2 : ℝ)⁻¹ • C⁻¹) - (B + C * B⁻¹ * C)⁻¹).PosSemidef := by
  letI := hB.isUnit.invertible
  letI := hC.isUnit.invertible
  let P : Matrix ι ι ℝ := B + C * B⁻¹ * C
  let Q : Matrix ι ι ℝ := (2 : ℝ) • C
  have hCterm : (C * B⁻¹ * C).PosSemidef := by
    have h := hB.inv.posSemidef.conjTranspose_mul_mul_same C
    rw [hC.isHermitian.eq] at h
    exact h
  have hP : Matrix.PosDef P := by
    exact hB.add_posSemidef hCterm
  have hQ : Matrix.PosDef Q := by
    exact hC.smul (by norm_num)
  have hdiff : (P - Q).PosSemidef := by
    have hfactor := hB.inv.posSemidef.conjTranspose_mul_mul_same (B - C)
    have hBCherm : (B - C).IsHermitian :=
      hB.isHermitian.sub hC.isHermitian
    have heq :
        P - Q = Matrix.conjTranspose (B - C) * B⁻¹ * (B - C) := by
      rw [hBCherm.eq]
      symm
      calc
        (B - C) * B⁻¹ * (B - C) =
            (B * B⁻¹ - C * B⁻¹) * (B - C) := by
              rw [sub_mul]
        _ = B * B⁻¹ * (B - C) - C * B⁻¹ * (B - C) := by
              rw [sub_mul]
        _ = (B - C) - C * B⁻¹ * (B - C) := by simp
        _ = (B - C) - (C * B⁻¹ * B - C * B⁻¹ * C) := by
              rw [mul_sub]
        _ = (B - C) - (C - C * B⁻¹ * C) := by
              rw [Matrix.mul_assoc, Matrix.inv_mul_of_invertible]
              simp
        _ = P - Q := by
              simp only [P, Q, two_smul]
              abel
    rw [heq]
    exact hfactor
  have hanti := higham10_30_posDef_inverse_anti hP hQ hdiff
  have hQinv : Q⁻¹ = (2 : ℝ)⁻¹ • C⁻¹ := by
    simpa [Q] using
      (Matrix.inv_smul (A := C) (2 : ℝ)
        (Matrix.isUnit_det_of_invertible C))
  rw [hQinv] at hanti
  simpa [P] using hanti

/-- Real part `X` of `(B+iC)⁻¹ = X-iY` in the source proof. -/
private noncomputable def higham10_30_inverseX {k : ℕ}
    (B C : Matrix (Fin k) (Fin k) ℝ) : Matrix (Fin k) (Fin k) ℝ :=
  (B + C * B⁻¹ * C)⁻¹

/-- Positive imaginary coefficient `Y` of `(B+iC)⁻¹ = X-iY`. -/
private noncomputable def higham10_30_inverseY {k : ℕ}
    (B C : Matrix (Fin k) (Fin k) ℝ) : Matrix (Fin k) (Fin k) ℝ :=
  B⁻¹ * C * higham10_30_inverseX B C

private theorem higham10_30_inverseX_posDef {k : ℕ}
    {B C : Matrix (Fin k) (Fin k) ℝ}
    (hB : Matrix.PosDef B) (hC : Matrix.PosDef C) :
    Matrix.PosDef (higham10_30_inverseX B C) := by
  letI := hB.isUnit.invertible
  have hterm : (C * B⁻¹ * C).PosSemidef := by
    have h := hB.inv.posSemidef.conjTranspose_mul_mul_same C
    rw [hC.isHermitian.eq] at h
    exact h
  exact (hB.add_posSemidef hterm).inv

/-- The second inverse formula from the paper:
    `Y = (C + B C⁻¹ B)⁻¹`. -/
private theorem higham10_30_inverseY_eq_swappedX {k : ℕ}
    {B C : Matrix (Fin k) (Fin k) ℝ}
    (hB : Matrix.PosDef B) (hC : Matrix.PosDef C) :
    higham10_30_inverseY B C = higham10_30_inverseX C B := by
  letI := hB.isUnit.invertible
  letI := hC.isUnit.invertible
  let P : Matrix (Fin k) (Fin k) ℝ := B + C * B⁻¹ * C
  let Q : Matrix (Fin k) (Fin k) ℝ := C + B * C⁻¹ * B
  have hP : Matrix.PosDef P := by
    have hterm : (C * B⁻¹ * C).PosSemidef := by
      have h := hB.inv.posSemidef.conjTranspose_mul_mul_same C
      rw [hC.isHermitian.eq] at h
      exact h
    exact hB.add_posSemidef hterm
  have hQ : Matrix.PosDef Q := by
    have hterm : (B * C⁻¹ * B).PosSemidef := by
      have h := hC.inv.posSemidef.conjTranspose_mul_mul_same B
      rw [hB.isHermitian.eq] at h
      exact h
    exact hC.add_posSemidef hterm
  letI := hP.isUnit.invertible
  letI := hQ.isUnit.invertible
  have hBY : B * higham10_30_inverseY B C =
      C * higham10_30_inverseX B C := by
    simp [higham10_30_inverseY, Matrix.mul_assoc]
  have hQY : Q * higham10_30_inverseY B C = 1 := by
    calc
      Q * higham10_30_inverseY B C =
          C * higham10_30_inverseY B C +
            B * C⁻¹ * (B * higham10_30_inverseY B C) := by
              simp only [Q]
              noncomm_ring
      _ = C * higham10_30_inverseY B C +
            B * C⁻¹ * (C * higham10_30_inverseX B C) := by rw [hBY]
      _ = C * higham10_30_inverseY B C +
            B * higham10_30_inverseX B C := by
              simp [Matrix.mul_assoc]
      _ = P * higham10_30_inverseX B C := by
              simp only [P, higham10_30_inverseY]
              noncomm_ring
      _ = 1 := by
              simp only [P, higham10_30_inverseX]
              exact Matrix.mul_inv_of_invertible _
  have hY : higham10_30_inverseY B C = Q⁻¹ := by
    calc
      higham10_30_inverseY B C =
          1 * higham10_30_inverseY B C := by simp
      _ = (Q⁻¹ * Q) * higham10_30_inverseY B C := by
        rw [Matrix.inv_mul_of_invertible]
      _ = Q⁻¹ * (Q * higham10_30_inverseY B C) := by
        rw [Matrix.mul_assoc]
      _ = Q⁻¹ := by rw [hQY]; simp
  simpa [Q, higham10_30_inverseX] using hY

private theorem higham10_30_inverseY_posDef {k : ℕ}
    {B C : Matrix (Fin k) (Fin k) ℝ}
    (hB : Matrix.PosDef B) (hC : Matrix.PosDef C) :
    Matrix.PosDef (higham10_30_inverseY B C) := by
  rw [higham10_30_inverseY_eq_swappedX hB hC]
  exact higham10_30_inverseX_posDef hC hB

/-- The two real block equations satisfied by
    `(x+iy) = (X-iY)(b+ic)`. -/
private theorem higham10_30_inverse_split_equations {k : ℕ}
    {B C : Matrix (Fin k) (Fin k) ℝ}
    (hB : Matrix.PosDef B) (hC : Matrix.PosDef C)
    (b c : Fin k → ℝ) :
    let X := higham10_30_inverseX B C
    let Y := higham10_30_inverseY B C
    let x := Matrix.mulVec X b + Matrix.mulVec Y c
    let y := Matrix.mulVec X c - Matrix.mulVec Y b
    (∀ i, (∑ j : Fin k, B i j * x j) -
      (∑ j : Fin k, C i j * y j) = b i) ∧
    (∀ i, (∑ j : Fin k, C i j * x j) +
      (∑ j : Fin k, B i j * y j) = c i) := by
  letI := hB.isUnit.invertible
  let P : Matrix (Fin k) (Fin k) ℝ := B + C * B⁻¹ * C
  have hP : Matrix.PosDef P := by
    have hterm : (C * B⁻¹ * C).PosSemidef := by
      have h := hB.inv.posSemidef.conjTranspose_mul_mul_same C
      rw [hC.isHermitian.eq] at h
      exact h
    exact hB.add_posSemidef hterm
  letI := hP.isUnit.invertible
  let X := higham10_30_inverseX B C
  let Y := higham10_30_inverseY B C
  have hsum : B * X + C * Y = 1 := by
    calc
      B * X + C * Y =
          (B + C * B⁻¹ * C) * (B + C * B⁻¹ * C)⁻¹ := by
            simp only [X, Y, higham10_30_inverseX, higham10_30_inverseY]
            noncomm_ring
      _ = 1 := Matrix.mul_inv_of_invertible _
  have hzero : B * Y - C * X = 0 := by
    simp only [X, Y, higham10_30_inverseX, higham10_30_inverseY]
    simp [Matrix.mul_assoc]
  dsimp only
  constructor
  · intro i
    have hvec :
        Matrix.mulVec B (Matrix.mulVec X b + Matrix.mulVec Y c) -
          Matrix.mulVec C (Matrix.mulVec X c - Matrix.mulVec Y b) = b := by
      calc
        _ = Matrix.mulVec (B * X + C * Y) b +
            Matrix.mulVec (B * Y - C * X) c := by
          simp only [Matrix.mulVec_add, Matrix.mulVec_sub,
            Matrix.mulVec_mulVec, Matrix.add_mulVec, Matrix.sub_mulVec]
          module
        _ = b := by rw [hsum, hzero]; simp
    exact congrFun hvec i
  · intro i
    have hvec :
        Matrix.mulVec C (Matrix.mulVec X b + Matrix.mulVec Y c) +
          Matrix.mulVec B (Matrix.mulVec X c - Matrix.mulVec Y b) = c := by
      calc
        _ = Matrix.mulVec (-(B * Y - C * X)) b +
            Matrix.mulVec (B * X + C * Y) c := by
          simp only [Matrix.mulVec_add, Matrix.mulVec_sub,
            Matrix.mulVec_mulVec, Matrix.add_mulVec, Matrix.sub_mulVec,
            Matrix.neg_mulVec]
          module
        _ = c := by rw [hsum, hzero]; simp
    exact congrFun hvec i

/-- A real symmetric bordered matrix, indexed as `Fin k ⊕ Fin 1`. -/
private noncomputable def higham10_30_borderedRealMatrix {k : ℕ}
    (B : Matrix (Fin k) (Fin k) ℝ) (b : Fin k → ℝ) (β : ℝ) :
    Matrix (Fin k ⊕ Fin 1) (Fin k ⊕ Fin 1) ℝ :=
  Matrix.fromBlocks B (fun i _ => b i) (fun _ j => b j) (fun _ _ => β)

/-- Positivity of the real part of a scalar complex Schur complement, written
    entirely in real block equations. -/
private theorem higham10_30_real_schur_scalar_pos
    {k : ℕ}
    {B C : Matrix (Fin k) (Fin k) ℝ}
    {b c x y : Fin k → ℝ} {β : ℝ}
    (hC : ∀ i j, C i j = C j i)
    (hBfull : Matrix.PosDef (higham10_30_borderedRealMatrix B b β))
    (hEqB : ∀ i, (∑ j : Fin k, B i j * x j) -
      (∑ j : Fin k, C i j * y j) = b i)
    (hEqC : ∀ i, (∑ j : Fin k, C i j * x j) +
      (∑ j : Fin k, B i j * y j) = c i) :
    0 < β - (∑ i : Fin k, b i * x i) + (∑ i : Fin k, c i * y i) := by
  let z : (Fin k ⊕ Fin 1) → ℝ :=
    Sum.elim (fun i => -x i) (fun _ => 1)
  have hz : z ≠ 0 := by
    intro hzero
    have hlast := congrFun hzero (Sum.inr (0 : Fin 1))
    norm_num [z] at hlast
  have hpos := hBfull.dotProduct_mulVec_pos hz
  let zy : (Fin k ⊕ Fin 1) → ℝ :=
    Sum.elim (fun i => -y i) (fun _ => 0)
  have hynonneg := hBfull.posSemidef.dotProduct_mulVec_nonneg zy
  have hcross := higham10_30_symmetric_cross_sum_eq C hC x y
  have hEqBx :
      (∑ i : Fin k, x i *
        ((∑ j : Fin k, B i j * x j) - (∑ j : Fin k, C i j * y j))) =
        ∑ i : Fin k, x i * b i := by
    apply Finset.sum_congr rfl
    intro i _
    rw [hEqB i]
  have hEqCy :
      (∑ i : Fin k, y i *
        ((∑ j : Fin k, C i j * x j) + (∑ j : Fin k, B i j * y j))) =
        ∑ i : Fin k, y i * c i := by
    apply Finset.sum_congr rfl
    intro i _
    rw [hEqC i]
  simp [z, higham10_30_borderedRealMatrix, dotProduct, Matrix.mulVec,
    Fintype.sum_sum_type] at hpos
  simp [zy, higham10_30_borderedRealMatrix, dotProduct, Matrix.mulVec,
    Fintype.sum_sum_type] at hynonneg
  have hEqBx' :
      (∑ i : Fin k, x i * (∑ j : Fin k, B i j * x j)) -
          (∑ i : Fin k, x i * (∑ j : Fin k, C i j * y j)) =
        ∑ i : Fin k, x i * b i := by
    calc
      _ = ∑ i : Fin k,
          (x i * (∑ j : Fin k, B i j * x j) -
            x i * (∑ j : Fin k, C i j * y j)) := by
              rw [Finset.sum_sub_distrib]
      _ = ∑ i : Fin k, x i *
          ((∑ j : Fin k, B i j * x j) -
            (∑ j : Fin k, C i j * y j)) := by
              apply Finset.sum_congr rfl
              intro i _
              ring
      _ = _ := hEqBx
  have hEqCy' :
      (∑ i : Fin k, y i * (∑ j : Fin k, C i j * x j)) +
          (∑ i : Fin k, y i * (∑ j : Fin k, B i j * y j)) =
        ∑ i : Fin k, y i * c i := by
    calc
      _ = ∑ i : Fin k,
          (y i * (∑ j : Fin k, C i j * x j) +
            y i * (∑ j : Fin k, B i j * y j)) := by
              rw [Finset.sum_add_distrib]
      _ = ∑ i : Fin k, y i *
          ((∑ j : Fin k, C i j * x j) +
            (∑ j : Fin k, B i j * y j)) := by
              apply Finset.sum_congr rfl
              intro i _
              ring
      _ = _ := hEqCy
  have hcross' :
      (∑ i : Fin k, y i * (∑ j : Fin k, C i j * x j)) =
        ∑ i : Fin k, x i * (∑ j : Fin k, C i j * y j) := by
    calc
      _ = ∑ i : Fin k, ∑ j : Fin k, y i * C i j * x j := by
        apply Finset.sum_congr rfl
        intro i _
        rw [Finset.mul_sum]
        apply Finset.sum_congr rfl
        intro j _
        ring
      _ = ∑ i : Fin k, ∑ j : Fin k, x i * C i j * y j := hcross
      _ = _ := by
        apply Finset.sum_congr rfl
        intro i _
        rw [Finset.mul_sum]
        apply Finset.sum_congr rfl
        intro j _
        ring
  ring_nf at hpos
  simp_rw [Finset.sum_add_distrib] at hpos
  simp_rw [Finset.sum_neg_distrib] at hpos
  have hbxcomm :
      (∑ i : Fin k, b i * x i) = ∑ i : Fin k, x i * b i := by
    apply Finset.sum_congr rfl
    intro i _
    ring
  have hcycomm :
      (∑ i : Fin k, c i * y i) = ∑ i : Fin k, y i * c i := by
    apply Finset.sum_congr rfl
    intro i _
    ring
  ring_nf at hpos hynonneg hEqBx' hEqCy' hcross' ⊢
  linarith [hbxcomm, hcycomm]

/-- Imaginary-part counterpart of `higham10_30_real_schur_scalar_pos`. -/
private theorem higham10_30_imag_schur_scalar_pos
    {k : ℕ}
    {B C : Matrix (Fin k) (Fin k) ℝ}
    {b c x y : Fin k → ℝ} {γ : ℝ}
    (hB : ∀ i j, B i j = B j i)
    (hCfull : Matrix.PosDef (higham10_30_borderedRealMatrix C c γ))
    (hEqB : ∀ i, (∑ j : Fin k, B i j * x j) -
      (∑ j : Fin k, C i j * y j) = b i)
    (hEqC : ∀ i, (∑ j : Fin k, C i j * x j) +
      (∑ j : Fin k, B i j * y j) = c i) :
    0 < γ - (∑ i : Fin k, c i * x i) - (∑ i : Fin k, b i * y i) := by
  have hEqB' : ∀ i,
      (∑ j : Fin k, C i j * x j) -
          (∑ j : Fin k, B i j * (-y j)) = c i := by
    intro i
    have h := hEqC i
    simp_rw [mul_neg, Finset.sum_neg_distrib]
    linarith
  have hEqC' : ∀ i,
      (∑ j : Fin k, B i j * x j) +
          (∑ j : Fin k, C i j * (-y j)) = b i := by
    intro i
    have h := hEqB i
    simp_rw [mul_neg, Finset.sum_neg_distrib]
    linarith
  have hpos := higham10_30_real_schur_scalar_pos
    (B := C) (C := B) (b := c) (c := b) (x := x) (y := fun i => -y i)
    hB hCfull hEqB' hEqC'
  simpa only [mul_neg, Finset.sum_neg_distrib, sub_eq_add_neg,
    neg_neg] using hpos

/-- Strict scalar Schur-complement inequality for an SPD bordered matrix. -/
private theorem higham10_30_bordered_inverse_energy_lt
    {k : ℕ} {C : Matrix (Fin k) (Fin k) ℝ}
    {c : Fin k → ℝ} {γ : ℝ}
    (hC : Matrix.PosDef C)
    (hCfull : Matrix.PosDef (higham10_30_borderedRealMatrix C c γ)) :
    (∑ i : Fin k, c i * Matrix.mulVec C⁻¹ c i) < γ := by
  letI := hC.isUnit.invertible
  have hright : Matrix.mulVec C (Matrix.mulVec C⁻¹ c) = c := by
    rw [Matrix.mulVec_mulVec, Matrix.mul_inv_of_invertible]
    simp
  have hpos := higham10_30_real_schur_scalar_pos
    (B := C) (C := (0 : Matrix (Fin k) (Fin k) ℝ))
    (b := c) (c := fun _ => 0)
    (x := Matrix.mulVec C⁻¹ c) (y := fun _ => 0)
    (β := γ) (by simp) hCfull
    (by
      intro i
      have hi := congrFun hright i
      simpa [Matrix.mulVec] using hi)
    (by simp)
  simpa using hpos

/-- Quadratic-form consequence of the inverse estimate:
    `2 cᵀXc < γ` for a column `c` of an SPD bordered `C`. -/
private theorem higham10_30_inverseX_energy_two_lt_border
    {k : ℕ} {B C : Matrix (Fin k) (Fin k) ℝ}
    {c : Fin k → ℝ} {γ : ℝ}
    (hB : Matrix.PosDef B) (hC : Matrix.PosDef C)
    (hCfull : Matrix.PosDef (higham10_30_borderedRealMatrix C c γ)) :
    2 * (∑ i : Fin k,
      c i * Matrix.mulVec (higham10_30_inverseX B C) c i) < γ := by
  have hupper := higham10_30_inverse_real_part_upper hB hC
  have hquad := hupper.dotProduct_mulVec_nonneg c
  have hborder := higham10_30_bordered_inverse_energy_lt hC hCfull
  simp only [dotProduct, Matrix.sub_mulVec, Matrix.smul_mulVec,
    Pi.sub_apply, Pi.smul_apply, smul_eq_mul] at hquad
  norm_num at hquad
  simp_rw [mul_sub] at hquad
  rw [Finset.sum_sub_distrib] at hquad
  have hscale :
      (∑ i : Fin k, c i * (1 / 2 * Matrix.mulVec C⁻¹ c i)) =
        (1 / 2 : ℝ) * ∑ i : Fin k, c i * Matrix.mulVec C⁻¹ c i := by
    rw [Finset.mul_sum]
    apply Finset.sum_congr rfl
    intro i _
    ring
  rw [hscale] at hquad
  change 2 * (∑ i : Fin k,
      c i * Matrix.mulVec (B + C * B⁻¹ * C)⁻¹ c i) < γ
  norm_num at hquad
  linarith

/-- Swapped form of the inverse estimate: `2 bᵀYb < β`. -/
private theorem higham10_30_inverseY_energy_two_lt_border
    {k : ℕ} {B C : Matrix (Fin k) (Fin k) ℝ}
    {b : Fin k → ℝ} {β : ℝ}
    (hB : Matrix.PosDef B) (hC : Matrix.PosDef C)
    (hBfull : Matrix.PosDef (higham10_30_borderedRealMatrix B b β)) :
    2 * (∑ i : Fin k,
      b i * Matrix.mulVec (higham10_30_inverseY B C) b i) < β := by
  rw [higham10_30_inverseY_eq_swappedX hB hC]
  exact higham10_30_inverseX_energy_two_lt_border hC hB hBfull

/-- The scalar estimate at the heart of the George--Ikramov--Kucherov
    proof.  Here `φ + iψ` is the last diagonal entry of a Schur complement,
    while `β + iγ` is the corresponding diagonal entry before elimination. -/
theorem higham10_30_source_schur_diagonal_growth_sq_lt_nine
    {k : ℕ} {B C : Matrix (Fin k) (Fin k) ℝ}
    {b c : Fin k → ℝ} {β γ : ℝ}
    (hB : Matrix.PosDef B) (hC : Matrix.PosDef C)
    (hBfull : Matrix.PosDef (higham10_30_borderedRealMatrix B b β))
    (hCfull : Matrix.PosDef (higham10_30_borderedRealMatrix C c γ)) :
    let X := higham10_30_inverseX B C
    let Y := higham10_30_inverseY B C
    let φ := β - (∑ i : Fin k, b i * Matrix.mulVec X b i) +
        (∑ i : Fin k, c i * Matrix.mulVec X c i) -
        2 * (∑ i : Fin k, b i * Matrix.mulVec Y c i)
    let ψ := γ + (∑ i : Fin k, b i * Matrix.mulVec Y b i) -
        (∑ i : Fin k, c i * Matrix.mulVec Y c i) -
        2 * (∑ i : Fin k, b i * Matrix.mulVec X c i)
    φ ^ 2 + ψ ^ 2 < 9 * (β ^ 2 + γ ^ 2) := by
  let X := higham10_30_inverseX B C
  let Y := higham10_30_inverseY B C
  let bXb := ∑ i : Fin k, b i * Matrix.mulVec X b i
  let cXc := ∑ i : Fin k, c i * Matrix.mulVec X c i
  let bYb := ∑ i : Fin k, b i * Matrix.mulVec Y b i
  let cYc := ∑ i : Fin k, c i * Matrix.mulVec Y c i
  let bYc := ∑ i : Fin k, b i * Matrix.mulVec Y c i
  let bXc := ∑ i : Fin k, b i * Matrix.mulVec X c i
  let φ := β - bXb + cXc - 2 * bYc
  let ψ := γ + bYb - cYc - 2 * bXc
  change φ ^ 2 + ψ ^ 2 < 9 * (β ^ 2 + γ ^ 2)
  have hXpos : Matrix.PosDef X := by
    exact higham10_30_inverseX_posDef hB hC
  have hYpos : Matrix.PosDef Y := by
    exact higham10_30_inverseY_posDef hB hC
  have hXsymm : ∀ i j, X i j = X j i := by
    intro i j
    simpa using hXpos.isHermitian.apply j i
  have hYsymm : ∀ i j, Y i j = Y j i := by
    intro i j
    simpa using hYpos.isHermitian.apply j i
  have hBsymm : ∀ i j, B i j = B j i := by
    intro i j
    simpa using hB.isHermitian.apply j i
  have hCsymm : ∀ i j, C i j = C j i := by
    intro i j
    simpa using hC.isHermitian.apply j i
  have hXcross :
      (∑ i : Fin k, c i * Matrix.mulVec X b i) = bXc := by
    exact higham10_30_symmetric_mulVec_cross_eq X hXsymm b c
  have hYcross :
      (∑ i : Fin k, c i * Matrix.mulVec Y b i) = bYc := by
    exact higham10_30_symmetric_mulVec_cross_eq Y hYsymm b c
  have hEq := higham10_30_inverse_split_equations hB hC b c
  dsimp only at hEq
  have hrealMinus := higham10_30_real_schur_scalar_pos
    (B := B) (C := C) (b := b) (c := c)
    (x := Matrix.mulVec X b + Matrix.mulVec Y c)
    (y := Matrix.mulVec X c - Matrix.mulVec Y b)
    hCsymm hBfull hEq.1 hEq.2
  have himagMinus := higham10_30_imag_schur_scalar_pos
    (B := B) (C := C) (b := b) (c := c)
    (x := Matrix.mulVec X b + Matrix.mulVec Y c)
    (y := Matrix.mulVec X c - Matrix.mulVec Y b)
    hBsymm hCfull hEq.1 hEq.2
  have hEqRealPlus := higham10_30_inverse_split_equations hB hC b (-c)
  dsimp only at hEqRealPlus
  have hrealPlus := higham10_30_real_schur_scalar_pos
    (B := B) (C := C) (b := b) (c := -c)
    (x := Matrix.mulVec X b + Matrix.mulVec Y (-c))
    (y := Matrix.mulVec X (-c) - Matrix.mulVec Y b)
    hCsymm hBfull hEqRealPlus.1 hEqRealPlus.2
  have hEqImagPlus := higham10_30_inverse_split_equations hB hC (-b) c
  dsimp only at hEqImagPlus
  have himagPlus := higham10_30_imag_schur_scalar_pos
    (B := B) (C := C) (b := -b) (c := c)
    (x := Matrix.mulVec X (-b) + Matrix.mulVec Y c)
    (y := Matrix.mulVec X c - Matrix.mulVec Y (-b))
    hBsymm hCfull hEqImagPlus.1 hEqImagPlus.2
  simp only [Pi.add_apply, Pi.sub_apply, Pi.neg_apply, Matrix.mulVec_neg,
    mul_add, mul_sub, mul_neg, Finset.sum_add_distrib,
    Finset.sum_sub_distrib, Finset.sum_neg_distrib, neg_mul,
    sub_neg_eq_add] at hrealMinus himagMinus hrealPlus himagPlus
  have hφpos : 0 < φ := by
    dsimp only [φ, bXb, cXc, bYc]
    linarith [hYcross]
  have hφplus : 0 < β - bXb + cXc + 2 * bYc := by
    dsimp only [bXb, cXc, bYc]
    linarith [hrealPlus, hYcross]
  have hψpos : 0 < ψ := by
    dsimp only [ψ, bYb, cYc, bXc]
    linarith [himagMinus, hXcross]
  have hψplus : 0 < γ + bYb - cYc + 2 * bXc := by
    dsimp only [bYb, cYc, bXc]
    linarith [himagPlus, hXcross]
  have hbXb0 : 0 ≤ bXb := by
    simpa [bXb, X, dotProduct] using
      hXpos.posSemidef.dotProduct_mulVec_nonneg b
  have hcXc0 : 0 ≤ cXc := by
    simpa [cXc, X, dotProduct] using
      hXpos.posSemidef.dotProduct_mulVec_nonneg c
  have hbYb0 : 0 ≤ bYb := by
    simpa [bYb, Y, dotProduct] using
      hYpos.posSemidef.dotProduct_mulVec_nonneg b
  have hcYc0 : 0 ≤ cYc := by
    simpa [cYc, Y, dotProduct] using
      hYpos.posSemidef.dotProduct_mulVec_nonneg c
  have hcXcBound : 2 * cXc < γ := by
    simpa [cXc, X] using
      higham10_30_inverseX_energy_two_lt_border hB hC hCfull
  have hbYbBound : 2 * bYb < β := by
    simpa [bYb, Y] using
      higham10_30_inverseY_energy_two_lt_border hB hC hBfull
  have hβpos : 0 < β := by linarith
  have hγpos : 0 < γ := by linarith
  have hφupper : φ < 2 * β + γ := by
    dsimp only [φ]
    linarith
  have hψupper : ψ < β + 2 * γ := by
    dsimp only [ψ]
    linarith
  have hφsq : φ ^ 2 < (2 * β + γ) ^ 2 := by nlinarith
  have hψsq : ψ ^ 2 < (β + 2 * γ) ^ 2 := by nlinarith
  nlinarith [sq_nonneg (β - γ)]

/-- Norm form of the source estimate: every diagonal Schur-complement entry
    is strictly smaller than three times its original diagonal entry. -/
theorem higham10_30_source_schur_diagonal_norm_lt_three
    {k : ℕ} {B C : Matrix (Fin k) (Fin k) ℝ}
    {b c : Fin k → ℝ} {β γ : ℝ}
    (hB : Matrix.PosDef B) (hC : Matrix.PosDef C)
    (hBfull : Matrix.PosDef (higham10_30_borderedRealMatrix B b β))
    (hCfull : Matrix.PosDef (higham10_30_borderedRealMatrix C c γ)) :
    let X := higham10_30_inverseX B C
    let Y := higham10_30_inverseY B C
    let φ := β - (∑ i : Fin k, b i * Matrix.mulVec X b i) +
        (∑ i : Fin k, c i * Matrix.mulVec X c i) -
        2 * (∑ i : Fin k, b i * Matrix.mulVec Y c i)
    let ψ := γ + (∑ i : Fin k, b i * Matrix.mulVec Y b i) -
        (∑ i : Fin k, c i * Matrix.mulVec Y c i) -
        2 * (∑ i : Fin k, b i * Matrix.mulVec X c i)
    ‖(φ : ℂ) + Complex.I * (ψ : ℂ)‖ <
      3 * ‖(β : ℂ) + Complex.I * (γ : ℂ)‖ := by
  let X := higham10_30_inverseX B C
  let Y := higham10_30_inverseY B C
  let φ := β - (∑ i : Fin k, b i * Matrix.mulVec X b i) +
      (∑ i : Fin k, c i * Matrix.mulVec X c i) -
      2 * (∑ i : Fin k, b i * Matrix.mulVec Y c i)
  let ψ := γ + (∑ i : Fin k, b i * Matrix.mulVec Y b i) -
      (∑ i : Fin k, c i * Matrix.mulVec Y c i) -
      2 * (∑ i : Fin k, b i * Matrix.mulVec X c i)
  change ‖(φ : ℂ) + Complex.I * (ψ : ℂ)‖ <
    3 * ‖(β : ℂ) + Complex.I * (γ : ℂ)‖
  have hsquare : φ ^ 2 + ψ ^ 2 < 9 * (β ^ 2 + γ ^ 2) := by
    simpa [X, Y, φ, ψ] using
      higham10_30_source_schur_diagonal_growth_sq_lt_nine
        hB hC hBfull hCfull
  let zout : ℂ := (φ : ℂ) + Complex.I * (ψ : ℂ)
  let zin : ℂ := (β : ℂ) + Complex.I * (γ : ℂ)
  have hzoutSq : ‖zout‖ ^ 2 = φ ^ 2 + ψ ^ 2 := by
    rw [Complex.sq_norm, Complex.normSq_apply]
    simp [zout]
    ring
  have hzinSq : ‖zin‖ ^ 2 = β ^ 2 + γ ^ 2 := by
    rw [Complex.sq_norm, Complex.normSq_apply]
    simp [zin]
    ring
  have hβpos : 0 < β := by
    have hdiag := hBfull.diag_pos (i := Sum.inr (0 : Fin 1))
    simpa [higham10_30_borderedRealMatrix] using hdiag
  have hzinNe : zin ≠ 0 := by
    intro hz
    have hre := congrArg Complex.re hz
    simp [zin] at hre
    linarith
  have hzinNorm : 0 < ‖zin‖ := norm_pos_iff.mpr hzinNe
  have hnormSq : ‖zout‖ ^ 2 < 9 * ‖zin‖ ^ 2 := by
    rw [hzoutSq, hzinSq]
    exact hsquare
  change ‖zout‖ < 3 * ‖zin‖
  nlinarith [norm_nonneg zout]

private theorem higham10_30_posDef_entry_sq_le_diag_mul_diag
    {n : ℕ} {M : Matrix (Fin n) (Fin n) ℝ}
    (hM : Matrix.PosDef M) (i j : Fin n) :
    M i j ^ 2 ≤ M i i * M j j := by
  classical
  by_cases hij : i = j
  · subst j
    nlinarith
  · let f : Fin 2 → Fin n := fun q => if q = 0 then i else j
    have hf : Function.Injective f := by
      intro a b hab
      fin_cases a <;> fin_cases b <;> simp_all [f]
    have hsub : Matrix.PosDef (M.submatrix f f) :=
      matrix_posDef_submatrix_of_injective hM f hf
    have hdet := Matrix.PosDef.det_pos hsub
    have hsym : M j i = M i j := by
      simpa using hM.isHermitian.apply i j
    simpa [Matrix.det_fin_two, f, hsym, pow_two] using hdet.le

/-- For separately SPD real and imaginary parts, the largest complex entry
    norm is attained on the diagonal (in the pairwise form needed below). -/
theorem higham10_30_complex_entry_norm_le_max_diagonal
    {n : ℕ} {B C : Matrix (Fin n) (Fin n) ℝ}
    (hB : Matrix.PosDef B) (hC : Matrix.PosDef C) (i j : Fin n) :
    ‖(B i j : ℂ) + Complex.I * (C i j : ℂ)‖ ≤
      max ‖(B i i : ℂ) + Complex.I * (C i i : ℂ)‖
        ‖(B j j : ℂ) + Complex.I * (C j j : ℂ)‖ := by
  let zij : ℂ := (B i j : ℂ) + Complex.I * (C i j : ℂ)
  let zii : ℂ := (B i i : ℂ) + Complex.I * (C i i : ℂ)
  let zjj : ℂ := (B j j : ℂ) + Complex.I * (C j j : ℂ)
  let d : ℝ := B i i * B j j + C i i * C j j
  have hBij := higham10_30_posDef_entry_sq_le_diag_mul_diag hB i j
  have hCij := higham10_30_posDef_entry_sq_le_diag_mul_diag hC i j
  have hBii : 0 < B i i := hB.diag_pos
  have hBjj : 0 < B j j := hB.diag_pos
  have hCii : 0 < C i i := hC.diag_pos
  have hCjj : 0 < C j j := hC.diag_pos
  have hzijSq : ‖zij‖ ^ 2 = B i j ^ 2 + C i j ^ 2 := by
    rw [Complex.sq_norm, Complex.normSq_apply]
    simp [zij]
    ring
  have hziiSq : ‖zii‖ ^ 2 = B i i ^ 2 + C i i ^ 2 := by
    rw [Complex.sq_norm, Complex.normSq_apply]
    simp [zii]
    ring
  have hzjjSq : ‖zjj‖ ^ 2 = B j j ^ 2 + C j j ^ 2 := by
    rw [Complex.sq_norm, Complex.normSq_apply]
    simp [zjj]
    ring
  have hd0 : 0 ≤ d := by
    dsimp only [d]
    positivity
  have hdSq : d ^ 2 ≤ ‖zii‖ ^ 2 * ‖zjj‖ ^ 2 := by
    rw [hziiSq, hzjjSq]
    dsimp only [d]
    nlinarith [sq_nonneg (B i i * C j j - C i i * B j j)]
  have hdle : d ≤ ‖zii‖ * ‖zjj‖ := by
    nlinarith [norm_nonneg zii, norm_nonneg zjj,
      mul_nonneg (norm_nonneg zii) (norm_nonneg zjj)]
  have hentrySq : ‖zij‖ ^ 2 ≤ ‖zii‖ * ‖zjj‖ := by
    rw [hzijSq]
    dsimp only [d] at hdle
    linarith
  have hprod : ‖zii‖ * ‖zjj‖ ≤ (max ‖zii‖ ‖zjj‖) ^ 2 := by
    have := mul_le_mul (le_max_left ‖zii‖ ‖zjj‖)
      (le_max_right ‖zii‖ ‖zjj‖) (norm_nonneg zjj)
      (le_trans (norm_nonneg zii) (le_max_left _ _))
    nlinarith
  change ‖zij‖ ≤ max ‖zii‖ ‖zjj‖
  have hmax0 : 0 ≤ max ‖zii‖ ‖zjj‖ :=
    le_trans (norm_nonneg zii) (le_max_left _ _)
  nlinarith [norm_nonneg zij]

/-! ## Exact Schur trace and the global growth factor -/

private theorem higham10_30_complex_leading_det_eq_prod_U_diag
    {n : ℕ} {A L U : Fin n → Fin n → ℂ}
    (hLU : higham9_8_ComplexLUFactSpec n A L U)
    {k : ℕ} (hk : k ≤ n) :
    Matrix.det
        ((Matrix.of A : Matrix (Fin n) (Fin n) ℂ).submatrix
          (Fin.castLE hk) (Fin.castLE hk)) =
      ∏ i : Fin k, U (Fin.castLE hk i) (Fin.castLE hk i) := by
  classical
  set e : Fin k → Fin n := Fin.castLE hk with he
  have hinj : Function.Injective e := Fin.castLE_injective hk
  set Lk : Matrix (Fin k) (Fin k) ℂ :=
    (Matrix.of L : Matrix (Fin n) (Fin n) ℂ).submatrix e e with hLk
  set Uk : Matrix (Fin k) (Fin k) ℂ :=
    (Matrix.of U : Matrix (Fin n) (Fin n) ℂ).submatrix e e with hUk
  set Ak : Matrix (Fin k) (Fin k) ℂ :=
    (Matrix.of A : Matrix (Fin n) (Fin n) ℂ).submatrix e e with hAk
  have hprod : Ak = Lk * Uk := by
    ext i j
    have hAij : Ak i j = ∑ p : Fin n, L (e i) p * U p (e j) := by
      simp only [hAk, Matrix.submatrix_apply, Matrix.of_apply]
      rw [← hLU.product_eq (e i) (e j)]
    have hLUij : (Lk * Uk) i j =
        ∑ m : Fin k, L (e i) (e m) * U (e m) (e j) := by
      simp only [hLk, hUk, Matrix.mul_apply, Matrix.submatrix_apply,
        Matrix.of_apply]
    rw [hAij, hLUij]
    rw [show (∑ m : Fin k, L (e i) (e m) * U (e m) (e j)) =
          ∑ p ∈ Finset.univ.map ⟨e, hinj⟩,
            L (e i) p * U p (e j) from
      (Finset.sum_map Finset.univ ⟨e, hinj⟩
        (fun p => L (e i) p * U p (e j))).symm]
    refine (Finset.sum_subset (Finset.subset_univ _) ?_).symm
    intro p _ hp
    have hpk : k ≤ p.val := by
      by_contra hlt
      push_neg at hlt
      exact hp (Finset.mem_map.mpr
        ⟨⟨p.val, hlt⟩, Finset.mem_univ _, by
          apply Fin.ext
          simp [he, Fin.coe_castLE]⟩)
    have hlt : (e i).val < p.val := by
      have h1 : (e i).val = i.val := by simp [he, Fin.coe_castLE]
      have h2 : i.val < k := i.isLt
      omega
    rw [hLU.L_upper_zero (e i) p hlt, zero_mul]
  have hLtri : Matrix.BlockTriangular Lk OrderDual.toDual := by
    intro a b hab
    have hab' : a.val < b.val := by simpa using hab
    have : (e a).val < (e b).val := by
      simp [he, Fin.coe_castLE]
      exact hab'
    simp only [hLk, Matrix.submatrix_apply, Matrix.of_apply]
    exact hLU.L_upper_zero (e a) (e b) this
  have hUtri : Matrix.BlockTriangular Uk id := by
    intro a b hab
    have hab' : b.val < a.val := by simpa using hab
    have : (e b).val < (e a).val := by
      simp [he, Fin.coe_castLE]
      exact hab'
    simp only [hUk, Matrix.submatrix_apply, Matrix.of_apply]
    exact hLU.U_lower_zero (e a) (e b) this
  have hLdet : Lk.det = 1 := by
    rw [Matrix.det_of_lowerTriangular _ hLtri]
    refine Finset.prod_eq_one ?_
    intro i _
    simp only [hLk, Matrix.submatrix_apply, Matrix.of_apply]
    exact hLU.L_diag (e i)
  calc
    Ak.det = (Lk * Uk).det := by rw [hprod]
    _ = Lk.det * Uk.det := Matrix.det_mul _ _
    _ = Uk.det := by rw [hLdet, one_mul]
    _ = ∏ i : Fin k, Uk i i := Matrix.det_of_upperTriangular hUtri
    _ = ∏ i : Fin k, U (e i) (e i) := by
      apply Finset.prod_congr rfl
      intro i _
      simp only [hUk, Matrix.submatrix_apply, Matrix.of_apply]

private theorem higham10_30_complex_leadingRows_mul_of_lower_left
    {n : ℕ} (L X : Matrix (Fin n) (Fin n) ℂ)
    (hL : ∀ i j : Fin n, i.val < j.val → L i j = 0)
    {k : ℕ} (hk : k ≤ n) (g : Fin k → Fin n) :
    (L * X).submatrix (Fin.castLE hk) g =
      L.submatrix (Fin.castLE hk) (Fin.castLE hk) *
        X.submatrix (Fin.castLE hk) g := by
  classical
  set e : Fin k → Fin n := Fin.castLE hk with he
  have hinj : Function.Injective e := Fin.castLE_injective hk
  ext i j
  simp only [Matrix.submatrix_apply, Matrix.mul_apply]
  rw [show (∑ m : Fin k, L (e i) (e m) * X (e m) (g j)) =
      ∑ p ∈ Finset.univ.map ⟨e, hinj⟩, L (e i) p * X p (g j) from
    (Finset.sum_map Finset.univ ⟨e, hinj⟩
      (fun p => L (e i) p * X p (g j))).symm]
  refine (Finset.sum_subset (Finset.subset_univ _) ?_).symm
  intro p _ hp
  have hpk : k ≤ p.val := by
    by_contra hlt
    push_neg at hlt
    exact hp (Finset.mem_map.mpr
      ⟨⟨p.val, hlt⟩, Finset.mem_univ _, by
        apply Fin.ext
        simp [he]⟩)
  have hlt : (e i).val < p.val := by
    have h1 : (e i).val = i.val := by simp [he]
    have h2 : i.val < k := i.isLt
    omega
  rw [hL (e i) p hlt, zero_mul]

private theorem higham10_30_complex_borderedU_det {n : ℕ}
    (U : Matrix (Fin n) (Fin n) ℂ)
    (hU : ∀ i j : Fin n, j.val < i.val → U i j = 0)
    {k : ℕ} (hk1 : k + 1 ≤ n) (j : Fin n) :
    (U.submatrix (Fin.castLE hk1)
      (higham9_15_borderedCols hk1 j)).det =
      (∏ i : Fin k, U (Fin.castLE (Nat.le_of_succ_le hk1) i)
          (Fin.castLE (Nat.le_of_succ_le hk1) i)) * U ⟨k, hk1⟩ j := by
  classical
  have htri : Matrix.BlockTriangular
      (U.submatrix (Fin.castLE hk1) (higham9_15_borderedCols hk1 j)) id := by
    intro a b hab
    have hab' : b.val < a.val := by simpa using hab
    have hbk : b.val < k := by have := a.isLt; omega
    simp only [Matrix.submatrix_apply]
    have hcol : higham9_15_borderedCols hk1 j b = ⟨b.val, by omega⟩ := by
      simp [higham9_15_borderedCols, hbk]
    rw [hcol]
    exact hU _ _ (by simpa using hab')
  rw [Matrix.det_of_upperTriangular htri]
  rw [Fin.prod_univ_castSucc (f := fun c : Fin (k + 1) =>
    (U.submatrix (Fin.castLE hk1) (higham9_15_borderedCols hk1 j)) c c)]
  congr 1
  · refine Finset.prod_congr rfl (fun c _ => ?_)
    simp only [Matrix.submatrix_apply]
    rw [higham9_15_borderedCols_castSucc]
    rfl
  · simp only [Matrix.submatrix_apply, higham9_15_borderedCols_last]
    rfl

private theorem higham10_30_complex_borderedMinor_eq_pivots_mul_U
    {n : ℕ} {A L U : Fin n → Fin n → ℂ}
    (hLU : higham9_8_ComplexLUFactSpec n A L U)
    {k : ℕ} (hk1 : k + 1 ≤ n) (j : Fin n) :
    ((Matrix.of A : Matrix (Fin n) (Fin n) ℂ).submatrix
        (Fin.castLE hk1) (higham9_15_borderedCols hk1 j)).det =
      (∏ i : Fin k, U (Fin.castLE (Nat.le_of_succ_le hk1) i)
          (Fin.castLE (Nat.le_of_succ_le hk1) i)) * U ⟨k, hk1⟩ j := by
  classical
  have hfact : (Matrix.of A : Matrix (Fin n) (Fin n) ℂ) =
      (Matrix.of L : Matrix (Fin n) (Fin n) ℂ) *
        (Matrix.of U : Matrix (Fin n) (Fin n) ℂ) := by
    ext a b
    simpa [Matrix.mul_apply] using (hLU.product_eq a b).symm
  rw [hfact, higham10_30_complex_leadingRows_mul_of_lower_left
    (Matrix.of L) (Matrix.of U)
    (fun a b hab => hLU.L_upper_zero a b hab) hk1
    (higham9_15_borderedCols hk1 j), Matrix.det_mul]
  have hLdet : ((Matrix.of L : Matrix (Fin n) (Fin n) ℂ).submatrix
      (Fin.castLE hk1) (Fin.castLE hk1)).det = 1 := by
    have hLtri : Matrix.BlockTriangular
        ((Matrix.of L : Matrix (Fin n) (Fin n) ℂ).submatrix
          (Fin.castLE hk1) (Fin.castLE hk1)) OrderDual.toDual := by
      intro a b hab
      have hab' : a.val < b.val := by simpa using hab
      simp only [Matrix.submatrix_apply, Matrix.of_apply]
      exact hLU.L_upper_zero _ _ (by simpa using hab')
    rw [Matrix.det_of_lowerTriangular _ hLtri]
    refine Finset.prod_eq_one (fun c _ => ?_)
    simp only [Matrix.submatrix_apply, Matrix.of_apply]
    exact hLU.L_diag _
  rw [hLdet, one_mul]
  exact higham10_30_complex_borderedU_det (Matrix.of U)
    (fun a b hab => hLU.U_lower_zero a b hab) hk1 j

private theorem higham10_30_complex_U_entry_eq_leading_schur
    {n k : ℕ} {A L U : Fin n → Fin n → ℂ}
    (hLU : higham9_8_ComplexLUFactSpec n A L U)
    (hk1 : k + 1 ≤ n) (j : Fin n)
    (hPdet : Matrix.det
      ((Matrix.of A : Matrix (Fin n) (Fin n) ℂ).submatrix
        (Fin.castLE (Nat.le_of_succ_le hk1))
        (Fin.castLE (Nat.le_of_succ_le hk1))) ≠ 0) :
    let e : Fin k → Fin n := Fin.castLE (Nat.le_of_succ_le hk1)
    let pivot : Fin n := ⟨k, hk1⟩
    let P : Matrix (Fin k) (Fin k) ℂ := fun p q => A (e p) (e q)
    U pivot j = A pivot j -
      ∑ p : Fin k, A pivot (e p) * Matrix.mulVec P⁻¹ (fun q => A (e q) j) p := by
  classical
  let e : Fin k → Fin n := Fin.castLE (Nat.le_of_succ_le hk1)
  let pivot : Fin n := ⟨k, hk1⟩
  let P : Matrix (Fin k) (Fin k) ℂ := fun p q => A (e p) (e q)
  let q : Matrix (Fin k) (Fin 1) ℂ := fun p _ => A (e p) j
  let r : Matrix (Fin 1) (Fin k) ℂ := fun _ p => A pivot (e p)
  let d : Matrix (Fin 1) (Fin 1) ℂ := fun _ _ => A pivot j
  let M : Matrix (Fin (k + 1)) (Fin (k + 1)) ℂ :=
    (Matrix.of A : Matrix (Fin n) (Fin n) ℂ).submatrix
      (Fin.castLE hk1) (higham9_15_borderedCols hk1 j)
  have hPdet' : Matrix.det P ≠ 0 := by
    simpa [P, e, Matrix.submatrix_apply, Matrix.of_apply] using hPdet
  letI : Invertible (Matrix.det P) := invertibleOfNonzero hPdet'
  letI : Invertible P := Matrix.invertibleOfDetInvertible P
  have hMblock :
      M.submatrix finSumFinEquiv finSumFinEquiv =
        Matrix.fromBlocks P q r d := by
    ext a b
    rcases a with a | a <;> rcases b with b | b
    · have ha : Fin.castLE hk1 (finSumFinEquiv (Sum.inl a)) = e a :=
        Fin.ext (by simp [e])
      have hb : higham9_15_borderedCols hk1 j
          (finSumFinEquiv (Sum.inl b)) = e b :=
        Fin.ext (by simp [e, higham9_15_borderedCols])
      simp only [M, P, q, r, d, Matrix.submatrix_apply,
        Matrix.fromBlocks_apply₁₁, Matrix.of_apply]
      rw [ha, hb]
    · have ha : Fin.castLE hk1 (finSumFinEquiv (Sum.inl a)) = e a :=
        Fin.ext (by simp [e])
      have hb : higham9_15_borderedCols hk1 j
          (finSumFinEquiv (Sum.inr b)) = j := by
        apply Fin.ext
        simp [higham9_15_borderedCols]
      simp only [M, P, q, r, d, Matrix.submatrix_apply,
        Matrix.fromBlocks_apply₁₂, Matrix.of_apply]
      rw [ha, hb]
    · have ha : Fin.castLE hk1 (finSumFinEquiv (Sum.inr a)) =
          pivot := Fin.ext (by simp [pivot])
      have hb : higham9_15_borderedCols hk1 j
          (finSumFinEquiv (Sum.inl b)) = e b :=
        Fin.ext (by simp [e, higham9_15_borderedCols])
      simp only [M, P, q, r, d, Matrix.submatrix_apply,
        Matrix.fromBlocks_apply₂₁, Matrix.of_apply]
      rw [ha, hb]
    · have ha : Fin.castLE hk1 (finSumFinEquiv (Sum.inr a)) =
          pivot := Fin.ext (by simp [pivot])
      have hb : higham9_15_borderedCols hk1 j
          (finSumFinEquiv (Sum.inr b)) = j := by
        apply Fin.ext
        simp [higham9_15_borderedCols]
      simp only [M, P, q, r, d, Matrix.submatrix_apply,
        Matrix.fromBlocks_apply₂₂, Matrix.of_apply]
      rw [ha, hb]
  have hMdet : Matrix.det M =
      Matrix.det (Matrix.fromBlocks P q r d) := by
    calc
      Matrix.det M = Matrix.det (M.submatrix finSumFinEquiv finSumFinEquiv) :=
        (Matrix.det_submatrix_equiv_self finSumFinEquiv M).symm
      _ = _ := by rw [hMblock]
  have hblockdet : Matrix.det (Matrix.fromBlocks P q r d) =
      Matrix.det P * (A pivot j -
        ∑ p : Fin k, A pivot (e p) *
          Matrix.mulVec P⁻¹ (fun q => A (e q) j) p) := by
    rw [Matrix.det_fromBlocks₁₁]
    congr 1
    rw [Matrix.mul_assoc]
    simp [P, q, r, d, e, pivot, Matrix.mul_apply, Matrix.mulVec,
      dotProduct, Matrix.invOf_eq_nonsing_inv]
  have hborder := higham10_30_complex_borderedMinor_eq_pivots_mul_U
    hLU hk1 j
  have hlead := higham10_30_complex_leading_det_eq_prod_U_diag
    hLU (Nat.le_of_succ_le hk1)
  have hpivotEq : pivot = ⟨k, hk1⟩ := rfl
  dsimp only
  rw [← hpivotEq]
  have hfactor :
      Matrix.det P * U pivot j =
        Matrix.det P * (A pivot j -
          ∑ p : Fin k, A pivot (e p) *
            Matrix.mulVec P⁻¹ (fun q => A (e q) j) p) := by
    have hPprod : Matrix.det P =
        ∏ i : Fin k, U (Fin.castLE (Nat.le_of_succ_le hk1) i)
          (Fin.castLE (Nat.le_of_succ_le hk1) i) := by
      simpa [P, e, Matrix.submatrix_apply, Matrix.of_apply] using hlead
    calc
      Matrix.det P * U pivot j = M.det := by
        rw [hPprod, hpivotEq]
        exact hborder.symm
      _ = Matrix.det (Matrix.fromBlocks P q r d) := hMdet
      _ = _ := hblockdet
  exact mul_left_cancel₀ hPdet' hfactor

private theorem higham10_30_complex_inverse_eq_X_minus_iY
    {k : ℕ} {B C : Matrix (Fin k) (Fin k) ℝ}
    (hB : Matrix.PosDef B) (hC : Matrix.PosDef C) :
    (Matrix.of (higham10_30_complexPositiveDefiniteForm k B C) :
      Matrix (Fin k) (Fin k) ℂ)⁻¹ =
      fun i j =>
        (higham10_30_inverseX B C i j : ℂ) -
          Complex.I * (higham10_30_inverseY B C i j : ℂ) := by
  letI := hB.isUnit.invertible
  let P : Matrix (Fin k) (Fin k) ℝ := B + C * B⁻¹ * C
  have hP : Matrix.PosDef P := by
    have hterm : (C * B⁻¹ * C).PosSemidef := by
      have h := hB.inv.posSemidef.conjTranspose_mul_mul_same C
      rw [hC.isHermitian.eq] at h
      exact h
    exact hB.add_posSemidef hterm
  letI := hP.isUnit.invertible
  let X := higham10_30_inverseX B C
  let Y := higham10_30_inverseY B C
  have hsum : B * X + C * Y = 1 := by
    calc
      B * X + C * Y =
          (B + C * B⁻¹ * C) * (B + C * B⁻¹ * C)⁻¹ := by
        simp only [X, Y, higham10_30_inverseX, higham10_30_inverseY]
        noncomm_ring
      _ = 1 := Matrix.mul_inv_of_invertible _
  have hzero : B * Y - C * X = 0 := by
    simp only [X, Y, higham10_30_inverseX, higham10_30_inverseY]
    simp [Matrix.mul_assoc]
  let A : Matrix (Fin k) (Fin k) ℂ :=
    Matrix.of (higham10_30_complexPositiveDefiniteForm k B C)
  let Z : Matrix (Fin k) (Fin k) ℂ := fun i j =>
    (X i j : ℂ) - Complex.I * (Y i j : ℂ)
  have hAZ : A * Z = 1 := by
    ext i j
    apply Complex.ext
    · have h := congrArg (fun M : Matrix (Fin k) (Fin k) ℝ => M i j) hsum
      simp only [Matrix.add_apply, Matrix.mul_apply] at h
      simp [A, Z, higham10_30_complexPositiveDefiniteForm,
        Matrix.mul_apply, Complex.mul_re]
      by_cases hij : i = j
      · simpa [Finset.sum_add_distrib, Matrix.one_apply, hij] using h
      · simpa [Finset.sum_add_distrib, Matrix.one_apply, hij] using h
    · have h := congrArg (fun M : Matrix (Fin k) (Fin k) ℝ => M i j) hzero
      simp only [Matrix.sub_apply, Matrix.mul_apply, Matrix.zero_apply] at h
      simp [A, Z, higham10_30_complexPositiveDefiniteForm,
        Matrix.mul_apply, Complex.mul_im]
      simp_rw [Finset.sum_add_distrib, Finset.sum_neg_distrib]
      have honeIm : ((1 : Matrix (Fin k) (Fin k) ℂ) i j).im = 0 := by
        by_cases hij : i = j <;> simp [Matrix.one_apply, hij]
      rw [honeIm]
      linarith
  have hAisSym : ∀ i j, C i j = C j i := by
    intro i j
    simpa using hC.isHermitian.apply j i
  have hAdet : Matrix.det A ≠ 0 := by
    exact higham10_30_det_ne_zero_of_real_spd B C
      (higham10_30_matrixPosDef_to_isSymPosDef B hB) hAisSym
  letI : Invertible A := Matrix.invertibleOfIsUnitDet A
    (isUnit_iff_ne_zero.mpr hAdet)
  have hZ : Z = A⁻¹ := by
    calc
      Z = 1 * Z := by simp
      _ = (A⁻¹ * A) * Z := by rw [Matrix.inv_mul_of_invertible]
      _ = A⁻¹ * (A * Z) := by rw [Matrix.mul_assoc]
      _ = A⁻¹ := by rw [hAZ]; simp
  simpa [A, Z, X, Y] using hZ.symm

private theorem higham10_30_principal_border_posDef
    {n k : ℕ} {M : Matrix (Fin n) (Fin n) ℝ}
    (hM : Matrix.PosDef M) (hk1 : k + 1 ≤ n) :
    let e : Fin k → Fin n := Fin.castLE (Nat.le_of_succ_le hk1)
    let pivot : Fin n := ⟨k, hk1⟩
    Matrix.PosDef (higham10_30_borderedRealMatrix
      (fun p q => M (e p) (e q)) (fun p => M (e p) pivot)
      (M pivot pivot)) := by
  classical
  let e : Fin k → Fin n := Fin.castLE (Nat.le_of_succ_le hk1)
  let pivot : Fin n := ⟨k, hk1⟩
  let f : Fin k ⊕ Fin 1 → Fin n :=
    Sum.elim e (fun _ => pivot)
  have hf : Function.Injective f := by
    intro a b hab
    rcases a with a | a <;> rcases b with b | b
    · have hv := congrArg Fin.val hab
      simp [f, e] at hv
      exact congrArg Sum.inl (Fin.ext hv)
    · exfalso
      have hv := congrArg Fin.val hab
      simp [f, e, pivot] at hv
      omega
    · exfalso
      have hv := congrArg Fin.val hab
      simp [f, e, pivot] at hv
      omega
    · apply congrArg Sum.inr
      exact Subsingleton.elim _ _
  have hsub := matrix_posDef_submatrix_of_injective hM f hf
  have hsym : ∀ p : Fin k, M pivot (e p) = M (e p) pivot := by
    intro p
    simpa using hM.isHermitian.apply (e p) pivot
  have heq : M.submatrix f f = higham10_30_borderedRealMatrix
      (fun p q => M (e p) (e q)) (fun p => M (e p) pivot)
      (M pivot pivot) := by
    ext a b
    rcases a with a | a <;> rcases b with b | b
    · rfl
    · rfl
    · simpa [f, higham10_30_borderedRealMatrix,
        Matrix.submatrix_apply] using hsym b
    · rfl
  dsimp only
  rw [← heq]
  exact hsub

private theorem higham10_30_principal_border_at_posDef
    {n k : ℕ} {M : Matrix (Fin n) (Fin n) ℝ}
    (hM : Matrix.PosDef M) (hk : k ≤ n) (r : Fin n) (hkr : k ≤ r.val) :
    let e : Fin k → Fin n := Fin.castLE hk
    Matrix.PosDef (higham10_30_borderedRealMatrix
      (fun p q => M (e p) (e q)) (fun p => M (e p) r)
      (M r r)) := by
  classical
  let e : Fin k → Fin n := Fin.castLE hk
  let f : Fin k ⊕ Fin 1 → Fin n := Sum.elim e (fun _ => r)
  have hf : Function.Injective f := by
    intro a b hab
    rcases a with a | a <;> rcases b with b | b
    · have hv := congrArg Fin.val hab
      simp [f, e] at hv
      exact congrArg Sum.inl (Fin.ext hv)
    · exfalso
      have hv := congrArg Fin.val hab
      simp [f, e] at hv
      omega
    · exfalso
      have hv := congrArg Fin.val hab
      simp [f, e] at hv
      omega
    · apply congrArg Sum.inr
      exact Subsingleton.elim _ _
  have hsub := matrix_posDef_submatrix_of_injective hM f hf
  have hsym : ∀ p : Fin k, M r (e p) = M (e p) r := by
    intro p
    simpa using hM.isHermitian.apply (e p) r
  have heq : M.submatrix f f = higham10_30_borderedRealMatrix
      (fun p q => M (e p) (e q)) (fun p => M (e p) r)
      (M r r) := by
    ext a b
    rcases a with a | a <;> rcases b with b | b
    · rfl
    · rfl
    · simpa [f, higham10_30_borderedRealMatrix,
        Matrix.submatrix_apply] using hsym b
    · rfl
  dsimp only
  rw [← heq]
  exact hsub

private theorem higham10_30_twoTrailingPrincipal_posDef
    {n k : ℕ} {M : Matrix (Fin n) (Fin n) ℝ}
    (hM : Matrix.PosDef M) (hk : k ≤ n)
    (r s : Fin n) (hkr : k ≤ r.val) (hks : k ≤ s.val) (hrs : r ≠ s) :
    let e : Fin k → Fin n := Fin.castLE hk
    let t : Fin 2 → Fin n := fun a => if a = 0 then r else s
    let A11 : Matrix (Fin k) (Fin k) ℝ := fun p q => M (e p) (e q)
    let A21 : Matrix (Fin 2) (Fin k) ℝ := fun a p => M (t a) (e p)
    let A22 : Matrix (Fin 2) (Fin 2) ℝ := fun a b => M (t a) (t b)
    Matrix.PosDef (Matrix.fromBlocks A11 A21.transpose A21 A22) := by
  classical
  let e : Fin k → Fin n := Fin.castLE hk
  let t : Fin 2 → Fin n := fun a => if a = 0 then r else s
  have ht : Function.Injective t := by
    intro a b hab
    fin_cases a <;> fin_cases b <;> simp_all [t]
  have htge : ∀ a : Fin 2, k ≤ (t a).val := by
    intro a
    fin_cases a <;> simp [t, hkr, hks]
  let f : Fin k ⊕ Fin 2 → Fin n := Sum.elim e t
  have hf : Function.Injective f := by
    intro a b hab
    rcases a with a | a <;> rcases b with b | b
    · have hv := congrArg Fin.val hab
      simp [f, e] at hv
      exact congrArg Sum.inl (Fin.ext hv)
    · exfalso
      have hv := congrArg Fin.val hab
      have ha : (e a).val < k := by simp [e]
      have hb := htge b
      simp only [f, Sum.elim_inl, Sum.elim_inr] at hv
      omega
    · exfalso
      have hv := congrArg Fin.val hab
      have ha := htge a
      have hb : (e b).val < k := by simp [e]
      simp only [f, Sum.elim_inl, Sum.elim_inr] at hv
      omega
    · exact congrArg Sum.inr (ht hab)
  let A11 : Matrix (Fin k) (Fin k) ℝ := fun p q => M (e p) (e q)
  let A21 : Matrix (Fin 2) (Fin k) ℝ := fun a p => M (t a) (e p)
  let A22 : Matrix (Fin 2) (Fin 2) ℝ := fun a b => M (t a) (t b)
  have hsub : Matrix.PosDef (M.submatrix f f) :=
    matrix_posDef_submatrix_of_injective hM f hf
  have heq : M.submatrix f f =
      Matrix.fromBlocks A11 A21.transpose A21 A22 := by
    ext a b
    rcases a with a | a <;> rcases b with b | b
    · rfl
    · simpa [f, A21, Matrix.transpose_apply, Matrix.submatrix_apply] using
        hM.isHermitian.apply (t b) (e a)
    · rfl
    · rfl
  have hfull : Matrix.PosDef
      (Matrix.fromBlocks A11 A21.transpose A21 A22) := by
    rw [← heq]
    exact hsub
  dsimp only
  exact hfull

private lemma higham10_30_symmetric_cross_sum_sub_eq_zero_fintype
    {ι : Type*} [Fintype ι]
    (M : ι → ι → ℝ) (hM : ∀ i j, M i j = M j i)
    (x y : ι → ℝ) :
    (∑ i, ∑ j, (y i * M i j * x j - x i * M i j * y j)) = 0 := by
  have hcross : (∑ i, ∑ j, y i * M i j * x j) =
      ∑ i, ∑ j, x i * M i j * y j := by
    calc
      (∑ i, ∑ j, y i * M i j * x j) =
          ∑ j, ∑ i, y i * M i j * x j := Finset.sum_comm
      _ = ∑ j, ∑ i, x j * M j i * y i := by
        apply Finset.sum_congr rfl
        intro j _
        apply Finset.sum_congr rfl
        intro i _
        rw [hM i j]
        ring
      _ = ∑ i, ∑ j, x i * M i j * y j := rfl
  simp_rw [Finset.sum_sub_distrib]
  rw [hcross]
  ring

private lemma higham10_30_symmetric_mulVec_cross_eq_fintype
    {ι : Type*} [Fintype ι]
    (M : Matrix ι ι ℝ) (hM : ∀ i j, M i j = M j i)
    (x y : ι → ℝ) :
    (∑ i, y i * Matrix.mulVec M x i) =
      ∑ i, x i * Matrix.mulVec M y i := by
  simp only [Matrix.mulVec, dotProduct]
  calc
    (∑ i, y i * ∑ j, M i j * x j) =
        ∑ i, ∑ j, y i * M i j * x j := by
      apply Finset.sum_congr rfl
      intro i _
      rw [Finset.mul_sum]
      apply Finset.sum_congr rfl
      intro j _
      ring
    _ = ∑ j, ∑ i, y i * M i j * x j := Finset.sum_comm
    _ = ∑ j, ∑ i, x j * M j i * y i := by
      apply Finset.sum_congr rfl
      intro j _
      apply Finset.sum_congr rfl
      intro i _
      rw [hM i j]
      ring
    _ = ∑ i, x i * ∑ j, M i j * y j := by
      apply Finset.sum_congr rfl
      intro i _
      rw [Finset.mul_sum]
      apply Finset.sum_congr rfl
      intro j _
      ring

private theorem higham10_30_complexEnergy_re_fintype
    {ι : Type*} [Fintype ι]
    (B C : Matrix ι ι ℝ) (hC : ∀ i j, C i j = C j i)
    (z : ι → ℂ) :
    (star z ⬝ᵥ Matrix.mulVec
      (fun i j => (B i j : ℂ) + Complex.I * (C i j : ℂ)) z).re =
      (fun i => (z i).re) ⬝ᵥ Matrix.mulVec B (fun i => (z i).re) +
      (fun i => (z i).im) ⬝ᵥ Matrix.mulVec B (fun i => (z i).im) := by
  have hcrossEq := higham10_30_symmetric_mulVec_cross_eq_fintype
    C hC (fun i => (z i).re) (fun i => (z i).im)
  simp only [Matrix.mulVec, dotProduct] at hcrossEq
  simp only [dotProduct, Matrix.mulVec]
  simp_rw [Complex.re_sum]
  simp [Complex.mul_re, Complex.mul_im]
  simp_rw [Finset.sum_add_distrib]
  simp_rw [mul_add]
  simp_rw [mul_sub]
  rw [Finset.sum_sub_distrib, Finset.sum_add_distrib]
  rw [hcrossEq]
  ring

private theorem higham10_30_complexEnergy_im_fintype
    {ι : Type*} [Fintype ι]
    (B C : Matrix ι ι ℝ) (hB : ∀ i j, B i j = B j i)
    (z : ι → ℂ) :
    (star z ⬝ᵥ Matrix.mulVec
      (fun i j => (B i j : ℂ) + Complex.I * (C i j : ℂ)) z).im =
      (fun i => (z i).re) ⬝ᵥ Matrix.mulVec C (fun i => (z i).re) +
      (fun i => (z i).im) ⬝ᵥ Matrix.mulVec C (fun i => (z i).im) := by
  have hcrossEq := higham10_30_symmetric_mulVec_cross_eq_fintype
    B hB (fun i => (z i).re) (fun i => (z i).im)
  simp only [Matrix.mulVec, dotProduct] at hcrossEq
  simp only [dotProduct, Matrix.mulVec]
  simp_rw [Complex.im_sum]
  simp [Complex.mul_re, Complex.mul_im]
  simp_rw [Finset.sum_add_distrib]
  simp_rw [mul_add]
  simp_rw [mul_sub, neg_sub]
  rw [Finset.sum_sub_distrib]
  rw [hcrossEq]
  rw [Finset.sum_add_distrib]
  ring

private theorem higham10_30_complexBlockSchur_re_im_posDef
    {k m : ℕ}
    (B11 C11 : Matrix (Fin k) (Fin k) ℝ)
    (B12 C12 : Matrix (Fin k) (Fin m) ℝ)
    (B22 C22 : Matrix (Fin m) (Fin m) ℝ)
    (hBfull : Matrix.PosDef
      (Matrix.fromBlocks B11 B12 B12.transpose B22))
    (hCfull : Matrix.PosDef
      (Matrix.fromBlocks C11 C12 C12.transpose C22)) :
    let P : Matrix (Fin k) (Fin k) ℂ :=
      fun i j => (B11 i j : ℂ) + Complex.I * (C11 i j : ℂ)
    let Q : Matrix (Fin k) (Fin m) ℂ :=
      fun i j => (B12 i j : ℂ) + Complex.I * (C12 i j : ℂ)
    let D : Matrix (Fin m) (Fin m) ℂ :=
      fun i j => (B22 i j : ℂ) + Complex.I * (C22 i j : ℂ)
    let S : Matrix (Fin m) (Fin m) ℂ := D - Q.transpose * P⁻¹ * Q
    Matrix.PosDef (fun i j => (S i j).re) ∧
      Matrix.PosDef (fun i j => (S i j).im) := by
  classical
  let BF : Matrix (Fin k ⊕ Fin m) (Fin k ⊕ Fin m) ℝ :=
    Matrix.fromBlocks B11 B12 B12.transpose B22
  let CF : Matrix (Fin k ⊕ Fin m) (Fin k ⊕ Fin m) ℝ :=
    Matrix.fromBlocks C11 C12 C12.transpose C22
  let P : Matrix (Fin k) (Fin k) ℂ :=
    fun i j => (B11 i j : ℂ) + Complex.I * (C11 i j : ℂ)
  let Q : Matrix (Fin k) (Fin m) ℂ :=
    fun i j => (B12 i j : ℂ) + Complex.I * (C12 i j : ℂ)
  let D : Matrix (Fin m) (Fin m) ℂ :=
    fun i j => (B22 i j : ℂ) + Complex.I * (C22 i j : ℂ)
  let S : Matrix (Fin m) (Fin m) ℂ := D - Q.transpose * P⁻¹ * Q
  let E : Matrix (Fin m) (Fin m) ℝ := fun i j => (S i j).re
  let F : Matrix (Fin m) (Fin m) ℝ := fun i j => (S i j).im
  have hB11 : Matrix.PosDef B11 := by
    simpa [BF] using matrix_posDef_submatrix_of_injective hBfull Sum.inl
      (fun _ _ h => Sum.inl.inj h)
  have hC11 : Matrix.PosDef C11 := by
    simpa [CF] using matrix_posDef_submatrix_of_injective hCfull Sum.inl
      (fun _ _ h => Sum.inl.inj h)
  have hB22 : Matrix.PosDef B22 := by
    simpa [BF] using matrix_posDef_submatrix_of_injective hBfull Sum.inr
      (fun _ _ h => Sum.inr.inj h)
  have hC22 : Matrix.PosDef C22 := by
    simpa [CF] using matrix_posDef_submatrix_of_injective hCfull Sum.inr
      (fun _ _ h => Sum.inr.inj h)
  have hPdet : Matrix.det P ≠ 0 := by
    exact higham10_30_det_ne_zero_of_real_spd B11 C11
      (higham10_30_matrixPosDef_to_isSymPosDef B11 hB11)
      (fun i j => by simpa using hC11.isHermitian.apply j i)
  letI : Invertible P := Matrix.invertibleOfIsUnitDet P
    (isUnit_iff_ne_zero.mpr hPdet)
  have hPtrans : P.transpose = P := by
    ext i j
    apply Complex.ext
    · simpa [P, Matrix.transpose_apply] using
        (hB11.isHermitian.apply j i).symm
    · simpa [P, Matrix.transpose_apply] using
        (hC11.isHermitian.apply j i).symm
  have hDtrans : D.transpose = D := by
    ext i j
    apply Complex.ext
    · simpa [D, Matrix.transpose_apply] using
        (hB22.isHermitian.apply j i).symm
    · simpa [D, Matrix.transpose_apply] using
        (hC22.isHermitian.apply j i).symm
  have hStrans : S.transpose = S := by
    simp only [S, Matrix.transpose_sub, Matrix.transpose_mul,
      Matrix.transpose_nonsing_inv]
    rw [hDtrans, hPtrans]
    simp [Matrix.mul_assoc]
  have hEherm : E.IsHermitian := by
    change E.conjTranspose = E
    ext i j
    have hij := congrArg (fun M : Matrix (Fin m) (Fin m) ℂ => M j i) hStrans
    simpa [E, Matrix.conjTranspose_apply, Matrix.transpose_apply] using
      (congrArg Complex.re hij).symm
  have hFherm : F.IsHermitian := by
    change F.conjTranspose = F
    ext i j
    have hij := congrArg (fun M : Matrix (Fin m) (Fin m) ℂ => M j i) hStrans
    simpa [F, Matrix.conjTranspose_apply, Matrix.transpose_apply] using
      (congrArg Complex.im hij).symm
  have hBFsym : ∀ i j, BF i j = BF j i := by
    intro i j
    simpa using hBfull.isHermitian.apply j i
  have hCFsym : ∀ i j, CF i j = CF j i := by
    intro i j
    simpa using hCfull.isHermitian.apply j i
  let Ablock : Matrix (Fin k ⊕ Fin m) (Fin k ⊕ Fin m) ℂ :=
    Matrix.fromBlocks P Q Q.transpose D
  have hAblock : Ablock = fun i j =>
      (BF i j : ℂ) + Complex.I * (CF i j : ℂ) := by
    ext i j
    rcases i with i | i <;> rcases j with j | j <;>
      simp [Ablock, BF, CF, P, Q, D, Matrix.transpose_apply]
  have hpos : ∀ q : Fin m → ℝ, q ≠ 0 →
      0 < star q ⬝ᵥ Matrix.mulVec E q ∧
        0 < star q ⬝ᵥ Matrix.mulVec F q := by
    intro q hq
    let qc : Fin m → ℂ := fun i => (q i : ℂ)
    let w : Fin k → ℂ := Matrix.mulVec P⁻¹ (Matrix.mulVec Q qc)
    let z : Fin k ⊕ Fin m → ℂ := Sum.elim (fun i => -w i) qc
    have hzre : (fun i => (z i).re) ≠ 0 := by
      intro hz
      apply hq
      funext i
      have hi := congrFun hz (Sum.inr i)
      simpa [z, qc] using hi
    have htop : Matrix.mulVec P (fun i => -w i) + Matrix.mulVec Q qc = 0 := by
      rw [show (fun i => -w i) = -w by rfl, Matrix.mulVec_neg]
      simp [w, Matrix.mulVec_mulVec, Matrix.mul_inv_of_invertible]
    have hbot : Matrix.mulVec Q.transpose (fun i => -w i) +
        Matrix.mulVec D qc = Matrix.mulVec S qc := by
      calc
        Matrix.mulVec Q.transpose (fun i => -w i) + Matrix.mulVec D qc =
            Matrix.mulVec D qc - Matrix.mulVec Q.transpose w := by
          rw [show (fun i => -w i) = -w by rfl, Matrix.mulVec_neg]
          module
        _ = Matrix.mulVec D qc -
            Matrix.mulVec (Q.transpose * P⁻¹ * Q) qc := by
          simp [w, Matrix.mulVec_mulVec, Matrix.mul_assoc]
        _ = Matrix.mulVec S qc := by simp [S, Matrix.sub_mulVec]
    have hAz : Matrix.mulVec Ablock z =
        Sum.elim (fun _ : Fin k => 0) (Matrix.mulVec S qc) := by
      funext i
      rcases i with i | i
      · have hi := congrFun htop i
        simpa [Ablock, z, Matrix.fromBlocks_mulVec] using hi
      · have hi := congrFun hbot i
        simpa [Ablock, z, Matrix.fromBlocks_mulVec] using hi
    have henergy : star z ⬝ᵥ Matrix.mulVec Ablock z =
        star qc ⬝ᵥ Matrix.mulVec S qc := by
      rw [hAz]
      simp [z, qc, dotProduct, Fintype.sum_sum_type]
    have hBre := hBfull.dotProduct_mulVec_pos hzre
    have hBim := hBfull.posSemidef.dotProduct_mulVec_nonneg
      (fun i => (z i).im)
    have hCre := hCfull.dotProduct_mulVec_pos hzre
    have hCim := hCfull.posSemidef.dotProduct_mulVec_nonneg
      (fun i => (z i).im)
    have henergyRe : 0 < (star z ⬝ᵥ Matrix.mulVec Ablock z).re := by
      rw [hAblock, higham10_30_complexEnergy_re_fintype BF CF hCFsym z]
      exact add_pos_of_pos_of_nonneg hBre hBim
    have henergyIm : 0 < (star z ⬝ᵥ Matrix.mulVec Ablock z).im := by
      rw [hAblock, higham10_30_complexEnergy_im_fintype BF CF hBFsym z]
      exact add_pos_of_pos_of_nonneg hCre hCim
    constructor
    · have heq : (star z ⬝ᵥ Matrix.mulVec Ablock z).re =
          star q ⬝ᵥ Matrix.mulVec E q := by
        rw [henergy]
        simp [qc, E, dotProduct, Matrix.mulVec, Complex.mul_re]
      rwa [heq] at henergyRe
    · have heq : (star z ⬝ᵥ Matrix.mulVec Ablock z).im =
          star q ⬝ᵥ Matrix.mulVec F q := by
        rw [henergy]
        simp [qc, F, dotProduct, Matrix.mulVec, Complex.mul_im]
      rwa [heq] at henergyIm
  dsimp only
  constructor
  · exact Matrix.PosDef.of_dotProduct_mulVec_pos hEherm
      (fun q hq => (hpos q hq).1)
  · exact Matrix.PosDef.of_dotProduct_mulVec_pos hFherm
      (fun q hq => (hpos q hq).2)

/-- Structural witness that a complex number is a diagonal entry of a Schur
    complement of the source matrix.  It records the original bordered SPD
    blocks and the exact inverse formula, rather than assuming any bound. -/
noncomputable def higham10_30_SourceSchurDiagonalRep {n : ℕ}
    (B₀ C₀ : Fin n → Fin n → ℝ) (z : ℂ) : Prop :=
  ∃ (k : ℕ) (B C : Matrix (Fin k) (Fin k) ℝ)
      (b c : Fin k → ℝ) (β γ : ℝ) (r : Fin n),
    Matrix.PosDef B ∧ Matrix.PosDef C ∧
    Matrix.PosDef (higham10_30_borderedRealMatrix B b β) ∧
    Matrix.PosDef (higham10_30_borderedRealMatrix C c γ) ∧
    (β : ℂ) + Complex.I * (γ : ℂ) =
      higham10_30_complexPositiveDefiniteForm n B₀ C₀ r r ∧
    z =
      let X := higham10_30_inverseX B C
      let Y := higham10_30_inverseY B C
      let φ := β - (∑ i : Fin k, b i * Matrix.mulVec X b i) +
          (∑ i : Fin k, c i * Matrix.mulVec X c i) -
          2 * (∑ i : Fin k, b i * Matrix.mulVec Y c i)
      let ψ := γ + (∑ i : Fin k, b i * Matrix.mulVec Y b i) -
          (∑ i : Fin k, c i * Matrix.mulVec Y c i) -
          2 * (∑ i : Fin k, b i * Matrix.mulVec X c i)
      (φ : ℂ) + Complex.I * (ψ : ℂ)

private theorem higham10_30_sourceSchurDiagonalRep_of_leading
    {n k : ℕ} (B₀ C₀ : Fin n → Fin n → ℝ)
    (hB₀ : IsSymPosDef n B₀) (hC₀ : IsSymPosDef n C₀)
    (hk : k ≤ n) (r : Fin n) (hkr : k ≤ r.val) :
    let e : Fin k → Fin n := Fin.castLE hk
    let B : Matrix (Fin k) (Fin k) ℝ := fun p q => B₀ (e p) (e q)
    let C : Matrix (Fin k) (Fin k) ℝ := fun p q => C₀ (e p) (e q)
    let P : Matrix (Fin k) (Fin k) ℂ :=
      Matrix.of (higham10_30_complexPositiveDefiniteForm k B C)
    higham10_30_SourceSchurDiagonalRep B₀ C₀
      (higham10_30_complexPositiveDefiniteForm n B₀ C₀ r r -
        ∑ p : Fin k,
          higham10_30_complexPositiveDefiniteForm n B₀ C₀ r (e p) *
            Matrix.mulVec P⁻¹
              (fun q => higham10_30_complexPositiveDefiniteForm n B₀ C₀
                (e q) r) p) := by
  classical
  let e : Fin k → Fin n := Fin.castLE hk
  let B : Matrix (Fin k) (Fin k) ℝ := fun p q => B₀ (e p) (e q)
  let C : Matrix (Fin k) (Fin k) ℝ := fun p q => C₀ (e p) (e q)
  let b : Fin k → ℝ := fun p => B₀ (e p) r
  let c : Fin k → ℝ := fun p => C₀ (e p) r
  let β : ℝ := B₀ r r
  let γ : ℝ := C₀ r r
  have hB : Matrix.PosDef B := by
    exact matrix_posDef_submatrix_of_injective
      (isSymPosDef_to_matrix_posDef B₀ hB₀) e (Fin.castLE_injective hk)
  have hC : Matrix.PosDef C := by
    exact matrix_posDef_submatrix_of_injective
      (isSymPosDef_to_matrix_posDef C₀ hC₀) e (Fin.castLE_injective hk)
  have hBfull : Matrix.PosDef (higham10_30_borderedRealMatrix B b β) := by
    simpa [B, b, β, e] using
      higham10_30_principal_border_at_posDef
        (isSymPosDef_to_matrix_posDef B₀ hB₀) hk r hkr
  have hCfull : Matrix.PosDef (higham10_30_borderedRealMatrix C c γ) := by
    simpa [C, c, γ, e] using
      higham10_30_principal_border_at_posDef
        (isSymPosDef_to_matrix_posDef C₀ hC₀) hk r hkr
  refine ⟨k, B, C, b, c, β, γ, r, hB, hC, hBfull, hCfull, ?_, ?_⟩
  · simp [β, γ, higham10_30_complexPositiveDefiniteForm]
  · let P : Matrix (Fin k) (Fin k) ℂ :=
      Matrix.of (higham10_30_complexPositiveDefiniteForm k B C)
    have hinv := higham10_30_complex_inverse_eq_X_minus_iY hB hC
    change
      higham10_30_complexPositiveDefiniteForm n B₀ C₀ r r -
          ∑ p : Fin k,
            higham10_30_complexPositiveDefiniteForm n B₀ C₀ r (e p) *
              Matrix.mulVec P⁻¹
                (fun q => higham10_30_complexPositiveDefiniteForm n B₀ C₀
                  (e q) r) p =
        ((β - (∑ i : Fin k, b i * Matrix.mulVec
              (higham10_30_inverseX B C) b i) +
            (∑ i : Fin k, c i * Matrix.mulVec
              (higham10_30_inverseX B C) c i) -
            2 * (∑ i : Fin k, b i * Matrix.mulVec
              (higham10_30_inverseY B C) c i) : ℝ) : ℂ) +
          Complex.I *
            ((γ + (∑ i : Fin k, b i * Matrix.mulVec
                (higham10_30_inverseY B C) b i) -
              (∑ i : Fin k, c i * Matrix.mulVec
                (higham10_30_inverseY B C) c i) -
              2 * (∑ i : Fin k, b i * Matrix.mulVec
                (higham10_30_inverseX B C) c i) : ℝ) : ℂ)
    rw [hinv]
    have hBsym : ∀ p : Fin k, B₀ r (e p) = B₀ (e p) r := by
      intro p
      exact hB₀.1 _ _
    have hCsym : ∀ p : Fin k, C₀ r (e p) = C₀ (e p) r := by
      intro p
      exact hC₀.1 _ _
    have hXsym : ∀ i j,
        higham10_30_inverseX B C i j = higham10_30_inverseX B C j i := by
      intro i j
      simpa using (higham10_30_inverseX_posDef hB hC).isHermitian.apply j i
    have hYsym : ∀ i j,
        higham10_30_inverseY B C i j = higham10_30_inverseY B C j i := by
      intro i j
      simpa using (higham10_30_inverseY_posDef hB hC).isHermitian.apply j i
    have hXcross := higham10_30_symmetric_mulVec_cross_eq
      (higham10_30_inverseX B C) hXsym b c
    have hYcross := higham10_30_symmetric_mulVec_cross_eq
      (higham10_30_inverseY B C) hYsym b c
    let v : Fin k → ℂ := Matrix.mulVec
      (fun i j => (higham10_30_inverseX B C i j : ℂ) -
        Complex.I * (higham10_30_inverseY B C i j : ℂ))
      (fun q => higham10_30_complexPositiveDefiniteForm n B₀ C₀ (e q) r)
    have hvre : ∀ p : Fin k, (v p).re =
        Matrix.mulVec (higham10_30_inverseX B C) b p +
          Matrix.mulVec (higham10_30_inverseY B C) c p := by
      intro p
      simp [v, B, C, b, c, e, higham10_30_complexPositiveDefiniteForm,
        Matrix.mulVec, dotProduct, Complex.mul_re, Complex.mul_im,
        Finset.sum_add_distrib]
    have hvim : ∀ p : Fin k, (v p).im =
        Matrix.mulVec (higham10_30_inverseX B C) c p -
          Matrix.mulVec (higham10_30_inverseY B C) b p := by
      intro p
      simp [v, B, C, b, c, e, higham10_30_complexPositiveDefiniteForm,
        Matrix.mulVec, dotProduct, Complex.mul_re, Complex.mul_im,
        Finset.sum_add_distrib, Finset.sum_sub_distrib]
      ring
    change higham10_30_complexPositiveDefiniteForm n B₀ C₀ r r -
        ∑ p : Fin k,
          higham10_30_complexPositiveDefiniteForm n B₀ C₀ r (e p) * v p = _
    apply Complex.ext
    · simp [B, C, b, c, β, γ, e, hBsym, hCsym, hvre, hvim,
        higham10_30_complexPositiveDefiniteForm,
        Complex.mul_re, Complex.mul_im, Finset.sum_add_distrib,
        Finset.sum_sub_distrib]
      simp_rw [mul_add, mul_sub]
      rw [Finset.sum_add_distrib, Finset.sum_sub_distrib]
      rw [hYcross]
      ring
    · simp [B, C, b, c, β, γ, e, hBsym, hCsym, hvre, hvim,
        higham10_30_complexPositiveDefiniteForm,
        Complex.mul_re, Complex.mul_im, Finset.sum_add_distrib,
        Finset.sum_sub_distrib]
      simp_rw [mul_add, mul_sub]
      rw [Finset.sum_sub_distrib, Finset.sum_add_distrib]
      rw [hXcross]
      ring

/-- Structural witness for an upper-factor entry: it is an entry of a matrix
    whose real and imaginary parts are SPD Schur complements, and the two
    relevant stage diagonals carry exact source representations. -/
noncomputable def higham10_30_SourceUpperEntryRep {n : ℕ}
    (B₀ C₀ : Fin n → Fin n → ℝ) (z : ℂ) : Prop :=
  higham10_30_SourceSchurDiagonalRep B₀ C₀ z ∨
    ∃ (m : ℕ) (B C : Matrix (Fin m) (Fin m) ℝ) (i j : Fin m),
      Matrix.PosDef B ∧ Matrix.PosDef C ∧
      z = (B i j : ℂ) + Complex.I * (C i j : ℂ) ∧
      higham10_30_SourceSchurDiagonalRep B₀ C₀
        ((B i i : ℂ) + Complex.I * (C i i : ℂ)) ∧
      higham10_30_SourceSchurDiagonalRep B₀ C₀
        ((B j j : ℂ) + Complex.I * (C j j : ℂ))

private theorem higham10_30_sourceUpperEntryRep_of_exactLU
    {n : ℕ} (B₀ C₀ : Fin n → Fin n → ℝ)
    (hB₀ : IsSymPosDef n B₀) (hC₀ : IsSymPosDef n C₀)
    (L U : Fin n → Fin n → ℂ)
    (hLU : higham9_8_ComplexLUFactSpec n
      (higham10_30_complexPositiveDefiniteForm n B₀ C₀) L U)
    (i j : Fin n) (hij : i ≤ j) :
    higham10_30_SourceUpperEntryRep B₀ C₀ (U i j) := by
  classical
  let k := i.val
  have hk1 : k + 1 ≤ n := i.isLt
  have hk : k ≤ n := Nat.le_of_succ_le hk1
  let e : Fin k → Fin n := Fin.castLE hk
  let A := higham10_30_complexPositiveDefiniteForm n B₀ C₀
  let B11 : Matrix (Fin k) (Fin k) ℝ := fun p q => B₀ (e p) (e q)
  let C11 : Matrix (Fin k) (Fin k) ℝ := fun p q => C₀ (e p) (e q)
  let P : Matrix (Fin k) (Fin k) ℂ :=
    fun p q => A (e p) (e q)
  have hPdet : Matrix.det P ≠ 0 := by
    simpa [P, A, e, B11, C11,
      higham10_30_complexPositiveDefiniteForm] using
      higham10_30_leadingComplexBlock_det_ne_zero B₀ C₀ hB₀ hC₀.1 k hk
  have hU := higham10_30_complex_U_entry_eq_leading_schur
    hLU hk1 j hPdet
  have hpivot : (⟨k, hk1⟩ : Fin n) = i := Fin.ext rfl
  rw [hpivot] at hU
  by_cases hijeq : i = j
  · subst j
    left
    have hdiag := higham10_30_sourceSchurDiagonalRep_of_leading
      B₀ C₀ hB₀ hC₀ hk i (by simp [k])
    rw [hU]
    simpa [A, P, B11, C11, e,
      higham10_30_complexPositiveDefiniteForm] using hdiag
  · have hijlt : i < j := lt_of_le_of_ne hij hijeq
    let t : Fin 2 → Fin n := fun a => if a = 0 then i else j
    have ht0 : t (0 : Fin 2) = i := by simp [t]
    have ht1 : t (1 : Fin 2) = j := by simp [t]
    let B12 : Matrix (Fin k) (Fin 2) ℝ := fun p a => B₀ (e p) (t a)
    let C12 : Matrix (Fin k) (Fin 2) ℝ := fun p a => C₀ (e p) (t a)
    let B22 : Matrix (Fin 2) (Fin 2) ℝ := fun a b => B₀ (t a) (t b)
    let C22 : Matrix (Fin 2) (Fin 2) ℝ := fun a b => C₀ (t a) (t b)
    have hBfull : Matrix.PosDef
        (Matrix.fromBlocks B11 B12 B12.transpose B22) := by
      have h := higham10_30_twoTrailingPrincipal_posDef
        (isSymPosDef_to_matrix_posDef B₀ hB₀) hk i j
          (by simp [k]) (by simpa [k] using hij) hijeq
      simpa [B11, B12, B22, e, t, Matrix.transpose_apply, hB₀.1] using h
    have hCfull : Matrix.PosDef
        (Matrix.fromBlocks C11 C12 C12.transpose C22) := by
      have h := higham10_30_twoTrailingPrincipal_posDef
        (isSymPosDef_to_matrix_posDef C₀ hC₀) hk i j
          (by simp [k]) (by simpa [k] using hij) hijeq
      simpa [C11, C12, C22, e, t, Matrix.transpose_apply, hC₀.1] using h
    let Q : Matrix (Fin k) (Fin 2) ℂ :=
      fun p a => (B12 p a : ℂ) + Complex.I * (C12 p a : ℂ)
    let D : Matrix (Fin 2) (Fin 2) ℂ :=
      fun a b => (B22 a b : ℂ) + Complex.I * (C22 a b : ℂ)
    let S : Matrix (Fin 2) (Fin 2) ℂ := D - Q.transpose * P⁻¹ * Q
    let E : Matrix (Fin 2) (Fin 2) ℝ := fun a b => (S a b).re
    let F : Matrix (Fin 2) (Fin 2) ℝ := fun a b => (S a b).im
    have hEF : Matrix.PosDef E ∧ Matrix.PosDef F := by
      simpa [P, Q, D, S, E, F, A, B11, C11,
        higham10_30_complexPositiveDefiniteForm] using
        higham10_30_complexBlockSchur_re_im_posDef
          B11 C11 B12 C12 B22 C22 hBfull hCfull
    have hSentry : ∀ a b : Fin 2,
        S a b = A (t a) (t b) -
          ∑ p : Fin k, A (t a) (e p) *
            Matrix.mulVec P⁻¹ (fun q => A (e q) (t b)) p := by
      intro a b
      have hAsym : ∀ p : Fin k, A (t a) (e p) = A (e p) (t a) := by
        intro p
        apply Complex.ext
        · simpa [A, higham10_30_complexPositiveDefiniteForm] using
            hB₀.1 (t a) (e p)
        · simpa [A, higham10_30_complexPositiveDefiniteForm] using
            hC₀.1 (t a) (e p)
      have hQsrc : ∀ p c, Q p c = A (e p) (t c) := by
        intro p c
        apply Complex.ext <;>
          simp [Q, A, B12, C12, higham10_30_complexPositiveDefiniteForm]
      have hDsrc : D a b = A (t a) (t b) := by
        apply Complex.ext <;>
          simp [D, A, B22, C22, higham10_30_complexPositiveDefiniteForm]
      have hsum :
          (∑ p : Fin k, A (t a) (e p) *
            Matrix.mulVec P⁻¹ (fun q => A (e q) (t b)) p) =
          ∑ p : Fin k, Q p a * Matrix.mulVec P⁻¹ (fun q => Q q b) p := by
        apply Finset.sum_congr rfl
        intro p _
        rw [hAsym p, ← hQsrc p a]
        congr 2
      change D a b - (Q.transpose * P⁻¹ * Q) a b = _
      rw [hDsrc, hsum]
      apply congrArg (fun z : ℂ => A (t a) (t b) - z)
      simp only [Matrix.mul_apply, Matrix.transpose_apply, Matrix.mulVec,
        dotProduct]
      calc
        (∑ x, (∑ x_1, Q x_1 a * P⁻¹ x_1 x) * Q x b) =
          ∑ x, ∑ x_1, Q x_1 a * P⁻¹ x_1 x * Q x b := by
            apply Finset.sum_congr rfl
            intro x _
            rw [Finset.sum_mul]
        _ = ∑ x_1, ∑ x, Q x_1 a * P⁻¹ x_1 x * Q x b :=
            Finset.sum_comm
        _ = ∑ x, Q x a * ∑ x_1, P⁻¹ x x_1 * Q x_1 b := by
            apply Finset.sum_congr rfl
            intro x _
            rw [Finset.mul_sum]
            apply Finset.sum_congr rfl
            intro x_1 _
            ring
    have hS01 : U i j = S (0 : Fin 2) (1 : Fin 2) := by
      rw [hU, hSentry]
      simp [ht0, ht1, A, P, e]
    have hcomplexEntry : U i j =
        (E (0 : Fin 2) (1 : Fin 2) : ℂ) +
          Complex.I * (F (0 : Fin 2) (1 : Fin 2) : ℂ) := by
      rw [hS01]
      apply Complex.ext <;> simp [E, F]
    have hdiag0 := higham10_30_sourceSchurDiagonalRep_of_leading
      B₀ C₀ hB₀ hC₀ hk i (by simp [k])
    have hdiag1 := higham10_30_sourceSchurDiagonalRep_of_leading
      B₀ C₀ hB₀ hC₀ hk j (by simpa [k] using hij)
    have hdiag0S : higham10_30_SourceSchurDiagonalRep B₀ C₀
        (S (0 : Fin 2) (0 : Fin 2)) := by
      rw [hSentry]
      simpa [ht0, A, P, B11, C11, e,
        higham10_30_complexPositiveDefiniteForm] using hdiag0
    have hdiag1S : higham10_30_SourceSchurDiagonalRep B₀ C₀
        (S (1 : Fin 2) (1 : Fin 2)) := by
      rw [hSentry]
      simpa [ht1, A, P, B11, C11, e,
        higham10_30_complexPositiveDefiniteForm] using hdiag1
    right
    refine ⟨2, E, F, (0 : Fin 2), (1 : Fin 2), hEF.1, hEF.2,
      hcomplexEntry, ?_, ?_⟩
    · have hsplit : S (0 : Fin 2) (0 : Fin 2) =
          (E (0 : Fin 2) (0 : Fin 2) : ℂ) +
            Complex.I * (F (0 : Fin 2) (0 : Fin 2) : ℂ) := by
        apply Complex.ext <;> simp [E, F]
      rwa [← hsplit]
    · have hsplit : S (1 : Fin 2) (1 : Fin 2) =
          (E (1 : Fin 2) (1 : Fin 2) : ℂ) +
            Complex.I * (F (1 : Fin 2) (1 : Fin 2) : ℂ) := by
        apply Complex.ext <;> simp [E, F]
      rwa [← hsplit]

/-- Exact no-pivot GE trace used by the source growth proof.  This contains
    only Schur-complement identities and positivity data; it contains no
    success or growth inequality. -/
def higham10_30_SourceGETrace {n : ℕ}
    (B₀ C₀ : Fin n → Fin n → ℝ)
    (U : Fin n → Fin n → ℂ) : Prop :=
  ∀ i j : Fin n, i ≤ j →
    higham10_30_SourceUpperEntryRep B₀ C₀ (U i j)

/-- The exact no-pivot LU equations themselves construct the source Schur
    trace; no trace, success, or growth premise is needed. -/
theorem higham10_30_complexPositiveDefinite_sourceGETrace
    {n : ℕ} (B C : Fin n → Fin n → ℝ)
    (hB : IsSymPosDef n B) (hC : IsSymPosDef n C)
    (L U : Fin n → Fin n → ℂ)
    (hLU : higham9_8_ComplexLUFactSpec n
      (higham10_30_complexPositiveDefiniteForm n B C) L U) :
    higham10_30_SourceGETrace B C U := by
  intro i j hij
  exact higham10_30_sourceUpperEntryRep_of_exactLU
    B C hB hC L U hLU i j hij

private theorem higham10_30_sourceDiagonalRep_norm_lt_three_max
    {n : ℕ} (hn : 0 < n) {B₀ C₀ : Fin n → Fin n → ℝ}
    {z : ℂ} (hz : higham10_30_SourceSchurDiagonalRep B₀ C₀ z) :
    ‖z‖ < 3 * higham9_13_complexMaxEntryNorm hn
      (higham10_30_complexPositiveDefiniteForm n B₀ C₀) := by
  rcases hz with ⟨k, B, C, b, c, β, γ, r,
    hB, hC, hBfull, hCfull, horiginal, rfl⟩
  have hlocal := higham10_30_source_schur_diagonal_norm_lt_three
    hB hC hBfull hCfull
  have horiginalLe := higham9_13_entry_norm_le_complexMaxEntryNorm hn
    (higham10_30_complexPositiveDefiniteForm n B₀ C₀) r r
  rw [← horiginal] at horiginalLe
  exact lt_of_lt_of_le hlocal (mul_le_mul_of_nonneg_left horiginalLe (by norm_num))

private theorem higham10_30_sourceUpperEntryRep_norm_lt_three_max
    {n : ℕ} (hn : 0 < n) {B₀ C₀ : Fin n → Fin n → ℝ}
    {z : ℂ} (hz : higham10_30_SourceUpperEntryRep B₀ C₀ z) :
    ‖z‖ < 3 * higham9_13_complexMaxEntryNorm hn
      (higham10_30_complexPositiveDefiniteForm n B₀ C₀) := by
  rcases hz with hz | ⟨m, B, C, i, j, hB, hC, rfl, hii, hjj⟩
  · exact higham10_30_sourceDiagonalRep_norm_lt_three_max hn hz
  · have hentry := higham10_30_complex_entry_norm_le_max_diagonal hB hC i j
    have hi := higham10_30_sourceDiagonalRep_norm_lt_three_max hn hii
    have hj := higham10_30_sourceDiagonalRep_norm_lt_three_max hn hjj
    exact lt_of_le_of_lt hentry (max_lt hi hj)

private theorem higham10_30_input_complexMaxEntryNorm_pos
    {n : ℕ} (hn : 0 < n) (B C : Fin n → Fin n → ℝ)
    (hB : IsSymPosDef n B) :
    0 < higham9_13_complexMaxEntryNorm hn
      (higham10_30_complexPositiveDefiniteForm n B C) := by
  let i₀ : Fin n := ⟨0, hn⟩
  have hBmat := isSymPosDef_to_matrix_posDef B hB
  have hBdiag : 0 < B i₀ i₀ := hBmat.diag_pos
  have hdiagNe :
      higham10_30_complexPositiveDefiniteForm n B C i₀ i₀ ≠ 0 := by
    intro hzero
    have hre := congrArg Complex.re hzero
    simp [higham10_30_complexPositiveDefiniteForm] at hre
    linarith
  exact lt_of_lt_of_le (norm_pos_iff.mpr hdiagNe)
    (higham9_13_entry_norm_le_complexMaxEntryNorm hn
      (higham10_30_complexPositiveDefiniteForm n B C) i₀ i₀)

/-- Source-faithful global growth theorem for (10.30).  Every exact no-pivot
    LU factor constructed from source-corrected SPD real and imaginary parts
    has max-entry growth factor `< 3`.  The Schur trace is derived internally;
    no success, trace, or growth premise occurs. -/
theorem higham10_30_complexPositiveDefinite_growth_lt_three
    {n : ℕ} (hn : 0 < n)
    (B C : Fin n → Fin n → ℝ)
    (hB : IsSymPosDef n B) (_hC : IsSymPosDef n C)
    (L U : Fin n → Fin n → ℂ)
    (hLU : higham9_8_ComplexLUFactSpec n
      (higham10_30_complexPositiveDefiniteForm n B C) L U) :
    higham9_13_complexGrowthFactorEntry hn
      (higham10_30_complexPositiveDefiniteForm n B C) U < 3 := by
  let A := higham10_30_complexPositiveDefiniteForm n B C
  let M := higham9_13_complexMaxEntryNorm hn A
  have htrace : higham10_30_SourceGETrace B C U :=
    higham10_30_complexPositiveDefinite_sourceGETrace B C hB _hC L U hLU
  have hMpos : 0 < M := by
    exact higham10_30_input_complexMaxEntryNorm_pos hn B C hB
  have hentry : ∀ i j : Fin n, ‖U i j‖ < 3 * M := by
    intro i j
    by_cases hij : i ≤ j
    · exact higham10_30_sourceUpperEntryRep_norm_lt_three_max hn (htrace i j hij)
    · have hji : j < i := lt_of_not_ge hij
      rw [hLU.U_lower_zero i j hji]
      simpa using mul_pos (by norm_num : (0 : ℝ) < 3) hMpos
  have hUmax : higham9_13_complexMaxEntryNorm hn U < 3 * M := by
    unfold higham9_13_complexMaxEntryNorm
    rw [Finset.sup'_lt_iff]
    intro i _
    rw [Finset.sup'_lt_iff]
    intro j _
    exact hentry i j
  rw [higham9_13_complexGrowthFactorEntry]
  exact (div_lt_iff₀ hMpos).2 (by simpa [M, A] using hUmax)

/-- Fully existential source endpoint for (10.30): no-pivot LU exists and its
    exact max-entry growth factor is strictly less than three. -/
theorem higham10_30_complexPositiveDefinite_exists_noPivotLU_growth_lt_three
    {n : ℕ} (hn : 0 < n)
    (B C : Fin n → Fin n → ℝ)
    (hB : IsSymPosDef n B) (hC : IsSymPosDef n C) :
    ∃ L U : Fin n → Fin n → ℂ,
      higham9_8_ComplexLUFactSpec n
        (higham10_30_complexPositiveDefiniteForm n B C) L U ∧
      higham9_13_complexGrowthFactorEntry hn
        (higham10_30_complexPositiveDefiniteForm n B C) U < 3 := by
  obtain ⟨L, U, hLU⟩ :=
    higham10_30_complexPositiveDefinite_exists_noPivotLU B C hB hC
  exact ⟨L, U, hLU,
    higham10_30_complexPositiveDefinite_growth_lt_three
      hn B C hB hC L U hLU⟩

/-! ## A literal real-component complex Doolittle executor -/

/-- The rounded upper-entry fold in complex Doolittle elimination.  Each
    complex product and subtraction is implemented by the real-component
    operations from Chapter 3. -/
noncomputable def higham10_30_flComplexDoolittleUEntry (fp : FPModel) (n : ℕ)
    (A L U : Fin n → Fin n → ℂ) (k j : Fin n) : ℂ :=
  Fin.foldl k.val
    (fun acc (s : Fin k.val) =>
      fl_complexSub fp acc
        (fl_complexMul fp (L k ⟨s.val, by omega⟩)
          (U ⟨s.val, by omega⟩ j)))
    (A k j)

/-- The rounded lower-entry numerator in complex Doolittle elimination. -/
noncomputable def higham10_30_flComplexDoolittleLNumerator (fp : FPModel) (n : ℕ)
    (A L U : Fin n → Fin n → ℂ) (i k : Fin n) : ℂ :=
  Fin.foldl k.val
    (fun acc (s : Fin k.val) =>
      fl_complexSub fp acc
        (fl_complexMul fp (L i ⟨s.val, by omega⟩)
          (U ⟨s.val, by omega⟩ k)))
    (A i k)

/-- The rounded lower entry, using the ordinary real-component complex
    division formula (3.14c). -/
noncomputable def higham10_30_flComplexDoolittleLEntry (fp : FPModel) (n : ℕ)
    (A L U : Fin n → Fin n → ℂ) (i k : Fin n) : ℂ :=
  fl_complexDiv fp
    (higham10_30_flComplexDoolittleLNumerator fp n A L U i k) (U k k)

/-- One upper-row write of the literal complex Doolittle loop. -/
noncomputable def higham10_30_complexDoolittleStageUpdateU (fp : FPModel) {n : ℕ}
    (A L U : Fin n → Fin n → ℂ) (k : Fin n) :
    Fin n → Fin n → ℂ :=
  fun i j =>
    if _hi : i = k then
      if _hj : j.val < k.val then 0
      else higham10_30_flComplexDoolittleUEntry fp n A L U k j
    else U i j

/-- One lower-column write of the literal complex Doolittle loop. -/
noncomputable def higham10_30_complexDoolittleStageUpdateL (fp : FPModel) {n : ℕ}
    (A L U : Fin n → Fin n → ℂ) (k : Fin n) :
    Fin n → Fin n → ℂ :=
  fun i j =>
    if _hj : j = k then
      if _hi : i.val < k.val then 0
      else if _hik : k.val < i.val then
        higham10_30_flComplexDoolittleLEntry fp n A L U i k
      else 1
    else L i j

/-- State of the literal square complex Doolittle loop. -/
abbrev higham10_30_ComplexDoolittleState (n : ℕ) :=
  (Fin n → Fin n → ℂ) × (Fin n → Fin n → ℂ)

/-- One literal complex Doolittle stage: write the active upper row first,
    then the active lower column using the newly written pivot. -/
noncomputable def higham10_30_complexDoolittleStageStep (fp : FPModel) {n : ℕ}
    (A : Fin n → Fin n → ℂ) (k : Fin n)
    (state : higham10_30_ComplexDoolittleState n) :
    higham10_30_ComplexDoolittleState n :=
  let U₁ := higham10_30_complexDoolittleStageUpdateU fp A state.1 state.2 k
  (higham10_30_complexDoolittleStageUpdateL fp A state.1 U₁ k, U₁)

/-- The first `T` stages of the literal complex Doolittle loop. -/
noncomputable def higham10_30_complexDoolittleLoopState (fp : FPModel) {n : ℕ}
    (A : Fin n → Fin n → ℂ) :
    ∀ T : ℕ, T ≤ n → higham10_30_ComplexDoolittleState n
  | 0, _ => (fun _ _ => 0, fun _ _ => 0)
  | T + 1, hT =>
      let prev := higham10_30_complexDoolittleLoopState fp A T
        (Nat.le_of_succ_le hT)
      higham10_30_complexDoolittleStageStep fp A
        ⟨T, Nat.lt_of_succ_le hT⟩ prev

/-- Computed lower factor returned by the literal complex Doolittle loop. -/
noncomputable def higham10_30_complexDoolittleL (fp : FPModel) {n : ℕ}
    (A : Fin n → Fin n → ℂ) : Fin n → Fin n → ℂ :=
  (higham10_30_complexDoolittleLoopState fp A n (Nat.le_refl n)).1

/-- Computed upper factor returned by the literal complex Doolittle loop. -/
noncomputable def higham10_30_complexDoolittleU (fp : FPModel) {n : ℕ}
    (A : Fin n → Fin n → ℂ) : Fin n → Fin n → ℂ :=
  (higham10_30_complexDoolittleLoopState fp A n (Nat.le_refl n)).2

/-! ## Complex GE backward error -/

/-- The operation-level relative-error certificate used by the complex GE
    backward-error argument.  It is the complex analogue of the usual
    accumulated product representation: each reconstructed entry of `A` has
    one relative perturbation per inner-product term. -/
def higham10_30_ComplexGERelErrorCertificate (n : ℕ)
    (A Lhat Uhat : Fin n → Fin n → ℂ) (γ : ℝ) : Prop :=
  ∀ i j : Fin n, ∃ η : Fin n → ℂ,
    (∀ k, ‖η k‖ ≤ γ) ∧
      A i j = ∑ k : Fin n, Lhat i k * Uhat k j * (1 + η k)

/-! ### Why the real `gamma_n` certificate cannot be imported literally -/

/-- An admissible real floating-point model used to audit the tempting
    `gamma_n` complex-GE certificate.  Every primitive satisfies `FPModel`'s
    standard relative-error law with `u = 1/10`; the deliberately correlated
    signs expose the extra constants incurred by real-component complex
    arithmetic. -/
private noncomputable def higham10_30_complexGammaCounterFP : FPModel where
  u := (1 : ℝ) / 10
  u_nonneg := by norm_num
  fl_add := fun x y =>
    if x = 0 then y
    else if x = y then (x + y) * (1 - (1 : ℝ) / 10)
    else (x + y) * (1 + (1 : ℝ) / 10)
  fl_sub := fun x y => (x - y) * (1 + (1 : ℝ) / 10)
  fl_mul := fun x y =>
    if x = 1 ∧ y = 1 then (x * y) * (1 - (1 : ℝ) / 10)
    else (x * y) * (1 + (1 : ℝ) / 10)
  fl_div := fun x y => (x / y) * (1 + (1 : ℝ) / 10)
  fl_sqrt := fun x => Real.sqrt x
  fl_add_zero := by intro x; simp
  model_add := by
    intro x y
    by_cases hx : x = 0
    · refine ⟨0, by norm_num, ?_⟩
      simp [hx]
    · by_cases hxy : x = y
      · refine ⟨-(1 : ℝ) / 10, by norm_num, ?_⟩
        have hy : y ≠ 0 := by
          intro hy0
          exact hx (hxy.trans hy0)
        simp [hxy, hy]
        ring
      · refine ⟨(1 : ℝ) / 10, by norm_num, ?_⟩
        simp [hx, hxy]
  model_sub := by
    intro x y
    refine ⟨(1 : ℝ) / 10, by norm_num, ?_⟩
    ring
  model_mul := by
    intro x y
    by_cases h : x = 1 ∧ y = 1
    · refine ⟨-(1 : ℝ) / 10, by norm_num, ?_⟩
      simp [h]
      ring
    · refine ⟨(1 : ℝ) / 10, by norm_num, ?_⟩
      simp [h]
  model_div := by
    intro x y _hy
    refine ⟨(1 : ℝ) / 10, by norm_num, ?_⟩
    ring
  model_sqrt := by
    intro x _hx
    refine ⟨0, by norm_num, ?_⟩
    ring

/-- SPD real part of the two-dimensional rounded-model audit. -/
private noncomputable def higham10_30_complexGammaCounterB :
    Fin 2 → Fin 2 → ℝ :=
  fun i j => if i = j then 1 else (1 : ℝ) / 2

/-- SPD imaginary part of the two-dimensional rounded-model audit. -/
private def higham10_30_complexGammaCounterC : Fin 2 → Fin 2 → ℝ :=
  fun i j => if i = j then 1 else 0

private noncomputable def higham10_30_complexGammaCounterA :
    Fin 2 → Fin 2 → ℂ :=
  higham10_30_complexPositiveDefiniteForm 2
    higham10_30_complexGammaCounterB higham10_30_complexGammaCounterC

private theorem higham10_30_complexGammaCounterB_spd :
    IsSymPosDef 2 higham10_30_complexGammaCounterB := by
  constructor
  · intro i j
    simp only [higham10_30_complexGammaCounterB]
    by_cases h : i = j
    · simp [h]
    · have h' : j ≠ i := fun hji => h hji.symm
      simp [h, h']
  · intro x hx
    simp only [Fin.sum_univ_two, higham10_30_complexGammaCounterB]
    simp only [ite_true, Fin.zero_ne_one, ite_false]
    rcases hx with ⟨i, hi⟩
    fin_cases i
    · simp_all
      nlinarith [sq_nonneg (x 0 + x 1), mul_self_pos.mpr hi,
        sq_nonneg (x 1)]
    · simp_all
      nlinarith [sq_nonneg (x 0 + x 1), sq_nonneg (x 0),
        mul_self_pos.mpr hi]

private theorem higham10_30_complexGammaCounterC_spd :
    IsSymPosDef 2 higham10_30_complexGammaCounterC := by
  constructor
  · intro i j
    simp only [higham10_30_complexGammaCounterC]
    by_cases h : i = j
    · simp [h]
    · have h' : j ≠ i := fun hji => h hji.symm
      simp [h, h']
  · intro x hx
    simp only [Fin.sum_univ_two, higham10_30_complexGammaCounterC]
    simp only [ite_true, Fin.zero_ne_one, ite_false]
    rcases hx with ⟨i, hi⟩
    fin_cases i
    · simp_all
      nlinarith [mul_self_pos.mpr hi, sq_nonneg (x 1)]
    · simp_all
      nlinarith [sq_nonneg (x 0), mul_self_pos.mpr hi]

private theorem higham10_30_complexGammaCounter_U00 :
    higham10_30_complexDoolittleU higham10_30_complexGammaCounterFP
      higham10_30_complexGammaCounterA 0 0 = 1 + Complex.I := by
  norm_num [higham10_30_complexDoolittleU,
    higham10_30_complexDoolittleLoopState,
    higham10_30_complexDoolittleStageStep,
    higham10_30_complexDoolittleStageUpdateU,
    higham10_30_complexDoolittleStageUpdateL,
    higham10_30_flComplexDoolittleUEntry,
    higham10_30_flComplexDoolittleLEntry,
    higham10_30_flComplexDoolittleLNumerator,
    fl_complexMul, fl_complexSub, fl_complexDiv,
    fl_complexDivDen, fl_complexDivNumRe, fl_complexDivNumIm,
    higham10_30_complexGammaCounterFP, higham10_30_complexGammaCounterA,
    higham10_30_complexGammaCounterB, higham10_30_complexGammaCounterC,
    higham10_30_complexPositiveDefiniteForm]

private theorem higham10_30_complexGammaCounter_U10 :
    higham10_30_complexDoolittleU higham10_30_complexGammaCounterFP
      higham10_30_complexGammaCounterA 1 0 = 0 := by
  norm_num [higham10_30_complexDoolittleU,
    higham10_30_complexDoolittleLoopState,
    higham10_30_complexDoolittleStageStep,
    higham10_30_complexDoolittleStageUpdateU,
    higham10_30_complexDoolittleStageUpdateL,
    higham10_30_flComplexDoolittleUEntry,
    higham10_30_flComplexDoolittleLEntry,
    higham10_30_flComplexDoolittleLNumerator,
    fl_complexMul, fl_complexSub, fl_complexDiv,
    fl_complexDivDen, fl_complexDivNumRe, fl_complexDivNumIm,
    higham10_30_complexGammaCounterFP, higham10_30_complexGammaCounterA,
    higham10_30_complexGammaCounterB, higham10_30_complexGammaCounterC,
    higham10_30_complexPositiveDefiniteForm]

private theorem higham10_30_complexGammaCounter_L10 :
    higham10_30_complexDoolittleL higham10_30_complexGammaCounterFP
      higham10_30_complexGammaCounterA 1 0 =
        ⟨(121 : ℝ) / 324, -(121 : ℝ) / 324⟩ := by
  norm_num [higham10_30_complexDoolittleL,
    higham10_30_complexDoolittleLoopState,
    higham10_30_complexDoolittleStageStep,
    higham10_30_complexDoolittleStageUpdateU,
    higham10_30_complexDoolittleStageUpdateL,
    higham10_30_flComplexDoolittleUEntry,
    higham10_30_flComplexDoolittleLEntry,
    higham10_30_flComplexDoolittleLNumerator,
    fl_complexMul, fl_complexSub, fl_complexDiv,
    fl_complexDivDen, fl_complexDivNumRe, fl_complexDivNumIm,
    higham10_30_complexGammaCounterFP, higham10_30_complexGammaCounterA,
    higham10_30_complexGammaCounterB, higham10_30_complexGammaCounterC,
    higham10_30_complexPositiveDefiniteForm]

private theorem higham10_30_complexGammaCounter_gammaValid :
    gammaValid higham10_30_complexGammaCounterFP 2 := by
  norm_num [gammaValid, higham10_30_complexGammaCounterFP]

private theorem higham10_30_complexGammaCounter_gamma :
    gamma higham10_30_complexGammaCounterFP 2 = (1 : ℝ) / 4 := by
  norm_num [gamma, higham10_30_complexGammaCounterFP]

private theorem higham10_30_complexGammaCounter_radius_lower_bound
    {γ : ℝ}
    (hcert : higham10_30_ComplexGERelErrorCertificate 2
      higham10_30_complexGammaCounterA
      (higham10_30_complexDoolittleL higham10_30_complexGammaCounterFP
        higham10_30_complexGammaCounterA)
      (higham10_30_complexDoolittleU higham10_30_complexGammaCounterFP
        higham10_30_complexGammaCounterA) γ) :
    (40 : ℝ) / 121 ≤ γ := by
  obtain ⟨η, hη, hentry⟩ := hcert (1 : Fin 2) (0 : Fin 2)
  have hA10 : higham10_30_complexGammaCounterA 1 0 =
      ((1 : ℝ) / 2 : ℂ) := by
    norm_num [higham10_30_complexGammaCounterA,
      higham10_30_complexGammaCounterB, higham10_30_complexGammaCounterC,
      higham10_30_complexPositiveDefiniteForm]
  rw [Fin.sum_univ_two, higham10_30_complexGammaCounter_L10,
    higham10_30_complexGammaCounter_U00,
    higham10_30_complexGammaCounter_U10, hA10] at hentry
  have hre := congrArg Complex.re hentry
  norm_num [Complex.mul_re, Complex.add_re] at hre
  have hreval : (η 0).re = -(40 : ℝ) / 121 := by
    norm_num at hre ⊢
    linarith
  have hlower : (40 : ℝ) / 121 ≤ ‖η 0‖ := by
    have hcomponent := Complex.abs_re_le_norm (η 0)
    rw [hreval] at hcomponent
    norm_num at hcomponent ⊢
    exact hcomponent
  exact hlower.trans (hη 0)

/-- The literal `gamma_n` certificate from real GE is false for the standard
    real-component complex-arithmetic model, even at `n = 2`, with both real
    and imaginary parts SPD and with `gammaValid fp 2`.  In the exhibited
    execution every certificate radius is at least `40/121`, whereas
    `gamma fp 2 = 1/4`.

    Thus the sentence after (10.30) is correctly classified as a qualitative
    consequence of bounded exact growth; it does not specify the real-field
    `gamma_n` constant for a literal complex implementation. -/
theorem higham10_30_literalComplexGE_gamma_n_certificate_source_discrepancy :
    ∃ (fp : FPModel) (B C : Fin 2 → Fin 2 → ℝ),
      IsSymPosDef 2 B ∧ IsSymPosDef 2 C ∧ gammaValid fp 2 ∧
      ¬ higham10_30_ComplexGERelErrorCertificate 2
        (higham10_30_complexPositiveDefiniteForm 2 B C)
        (higham10_30_complexDoolittleL fp
          (higham10_30_complexPositiveDefiniteForm 2 B C))
        (higham10_30_complexDoolittleU fp
          (higham10_30_complexPositiveDefiniteForm 2 B C))
        (gamma fp 2) := by
  refine ⟨higham10_30_complexGammaCounterFP,
    higham10_30_complexGammaCounterB,
    higham10_30_complexGammaCounterC,
    higham10_30_complexGammaCounterB_spd,
    higham10_30_complexGammaCounterC_spd,
    higham10_30_complexGammaCounter_gammaValid, ?_⟩
  intro hcert
  have hlower := higham10_30_complexGammaCounter_radius_lower_bound hcert
  rw [higham10_30_complexGammaCounter_gamma] at hlower
  norm_num at hlower

/-- A complex GE relative-error certificate yields the standard componentwise
    backward error `A + ΔA = Lhat Uhat`, with
    `|ΔA| ≤ γ |Lhat||Uhat|`. -/
theorem higham10_30_complexGE_backward_error
    {n : ℕ} {A Lhat Uhat : Fin n → Fin n → ℂ} {γ : ℝ}
    (_hγ : 0 ≤ γ)
    (hcert : higham10_30_ComplexGERelErrorCertificate n A Lhat Uhat γ) :
    ∃ ΔA : Fin n → Fin n → ℂ,
      (∀ i j,
        ‖ΔA i j‖ ≤ γ * ∑ k : Fin n, ‖Lhat i k‖ * ‖Uhat k j‖) ∧
      (∀ i j,
        ∑ k : Fin n, Lhat i k * Uhat k j = A i j + ΔA i j) := by
  let ΔA : Fin n → Fin n → ℂ :=
    fun i j => (∑ k : Fin n, Lhat i k * Uhat k j) - A i j
  refine ⟨ΔA, ?_, ?_⟩
  · intro i j
    obtain ⟨η, hη, hA⟩ := hcert i j
    have hΔ :
        ΔA i j = -∑ k : Fin n, Lhat i k * Uhat k j * η k := by
      simp only [ΔA]
      rw [hA]
      simp_rw [mul_add, mul_one, Finset.sum_add_distrib]
      ring
    rw [hΔ, norm_neg]
    calc
      ‖∑ k : Fin n, Lhat i k * Uhat k j * η k‖ ≤
          ∑ k : Fin n, ‖Lhat i k * Uhat k j * η k‖ :=
        norm_sum_le _ _
      _ = ∑ k : Fin n, (‖Lhat i k‖ * ‖Uhat k j‖) * ‖η k‖ := by
        apply Finset.sum_congr rfl
        intro k _
        simp only [norm_mul]
      _ ≤ ∑ k : Fin n, (‖Lhat i k‖ * ‖Uhat k j‖) * γ := by
        apply Finset.sum_le_sum
        intro k _
        exact mul_le_mul_of_nonneg_left (hη k)
          (mul_nonneg (norm_nonneg _) (norm_nonneg _))
      _ = γ * ∑ k : Fin n, ‖Lhat i k‖ * ‖Uhat k j‖ := by
        rw [Finset.mul_sum]
        apply Finset.sum_congr rfl
        intro k _
        ring
  · intro i j
    simp [ΔA]

/-- Conditional compatibility adapter for a caller that already has a complex
    GE relative-error certificate.  This is not the literal rounded closure of
    the prose after (10.30): the theorem above shows that radius `gamma fp n`
    is false in general for the real-component executor.  The source itself
    supplies only the exact growth bound and a qualitative stability verdict. -/
theorem higham10_30_complexPositiveDefinite_GE_backward_error_source
    {n : ℕ} (fp : FPModel)
    (B C : Fin n → Fin n → ℝ)
    (hB : IsSymPosDef n B) (hC : IsSymPosDef n C)
    (hγ : gammaValid fp n) :
    (∃ L U : Fin n → Fin n → ℂ,
      higham9_8_ComplexLUFactSpec n
        (higham10_30_complexPositiveDefiniteForm n B C) L U) ∧
    (∀ Lhat Uhat : Fin n → Fin n → ℂ,
      higham10_30_ComplexGERelErrorCertificate n
          (higham10_30_complexPositiveDefiniteForm n B C)
          Lhat Uhat (gamma fp n) →
        ∃ ΔA : Fin n → Fin n → ℂ,
          (∀ i j,
            ‖ΔA i j‖ ≤ gamma fp n *
              ∑ k : Fin n, ‖Lhat i k‖ * ‖Uhat k j‖) ∧
          (∀ i j,
            ∑ k : Fin n, Lhat i k * Uhat k j =
              higham10_30_complexPositiveDefiniteForm n B C i j + ΔA i j)) := by
  refine ⟨higham10_30_complexPositiveDefinite_exists_noPivotLU B C hB hC, ?_⟩
  intro Lhat Uhat hcert
  exact higham10_30_complexGE_backward_error (gamma_nonneg fp hγ) hcert

end NumStability
