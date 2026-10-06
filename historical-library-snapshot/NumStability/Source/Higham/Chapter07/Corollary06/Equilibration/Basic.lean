import NumStability.Algorithms.LinearSystems.Cholesky.ErrorAnalysis.Demmel
import NumStability.Analysis.MatrixNorms.SpectralExtrema.Basic
import NumStability.Algorithms.Summation.Compensated.FiniteFormat
import NumStability.Analysis.FirstOrder.AsymptoticFamilies
import NumStability.Analysis.Conditioning.LinearSystems.InversePerturbation
import NumStability.Source.Higham.Chapter07.Corollary06.LinearSystemsConditioning.Basic
import NumStability.Source.Higham.Chapter07.Corollary06.LinearSystemsConditioning.Results
import NumStability.Source.Higham.Chapter07.LinearSystemsConditioning.Problem01
import NumStability.Source.Higham.Chapter07.LinearSystemsConditioning.Problem10Bauer.Part01
import NumStability.Source.Higham.Chapter07.LinearSystemsConditioning.Theorem05.Part01
import NumStability.Source.Higham.Chapter07.LinearSystemsConditioning.Theorem05.Part02
import NumStability.Source.Higham.Chapter08.Section04.FanInAsymptotics.Basic
import NumStability.Source.Higham.Chapter09.DoolittleClosure
import NumStability.Source.Higham.Chapter09.Section11
import NumStability.Source.Higham.Chapter19.Theorem06.ColumnPivot

/-!
# Chapter07 Corollary06 Equilibration Basic

Canonical destination for material split out of
`NumStability.Algorithms.HighamChapters1To9SourceClosure` by wave W12 of the August 2026 repository reorganization.
Declaration names, statements and proofs are unchanged; only the
module they live in has changed. The historical module still
resolves and re-exports this one.
-/

open Filter Asymptotics
open scoped BigOperators
open scoped Topology
open scoped Matrix.Norms.Operator

namespace NumStability

/-- Higham, 2nd ed., Corollary 7.6 / equation (7.23), with all source
semantics exposed.  The Cholesky data certify that `A = RᵀR` is symmetric
positive semidefinite and nonsingular, `Rinv * Rinvᵀ` is its genuine inverse,
the printed diagonal pair is reciprocal, and the displayed inverse-side
scaling is a genuine inverse of `D*A*D`.  The final conjunct is the source
factor-`n` near-optimality bound.

Thus this theorem closes the gap in the lower-level estimate, whose formal
inverse-Gram argument did not itself require `Rinv` to invert `R`. -/
theorem higham7_6_spd_source_scaling_bound
    {n : ℕ} (hn : 0 < n)
    (A R Rinv : Fin n → Fin n → ℝ)
    (hGram : ∀ i j : Fin n, (∑ k : Fin n, R k i * R k j) = A i j)
    (hGramDiag : ∀ j : Fin n, (∑ k : Fin n, R k j * R k j) = A j j)
    (hdiag : ∀ j : Fin n, 0 < A j j)
    (hRinv : IsInverse n R Rinv) :
    IsSymmetricFiniteMatrix A ∧
      finitePSD A ∧
      IsInverse n A (ch7CholeskyInverseGram Rinv) ∧
      (∀ j : Fin n,
        ch7SymmetricDiagEquilibratingScale2 A j *
            ch7SymmetricDiagEquilibratingInvScale2 A j = 1) ∧
      IsInverse n
        (ch7TwoSidedScale (ch7SymmetricDiagEquilibratingScale2 A) A
          (ch7SymmetricDiagEquilibratingScale2 A))
        (ch7TwoSidedScale (ch7SymmetricDiagEquilibratingInvScale2 A)
          (ch7CholeskyInverseGram Rinv)
          (ch7SymmetricDiagEquilibratingInvScale2 A)) ∧
      ch7SymmetricOp2ScaledCond A (ch7CholeskyInverseGram Rinv)
          (ch7SymmetricDiagEquilibratingScale2 A)
          (ch7SymmetricDiagEquilibratingInvScale2 A) ≤
        (n : ℝ) *
          sInf (ch7SymmetricOp2ScaledCondSet A
            (ch7CholeskyInverseGram Rinv)) := by
  have hAeq : A = matMul n (matTranspose R) R := by
    ext i j
    unfold matMul matTranspose
    exact (hGram i j).symm
  have hArect : A = rectMatMul (finiteTranspose R) R := by
    simpa [rectMatMul, finiteTranspose, matMul, matTranspose] using hAeq
  have hsym : IsSymmetricFiniteMatrix A :=
    IsSymmetricFiniteMatrix_of_eq_rectMatMul_transpose_self R hArect
  have hpsd : finitePSD A :=
    finitePSD_of_eq_rectMatMul_transpose_self R hArect
  have hAinv : IsInverse n A (ch7CholeskyInverseGram Rinv) := by
    rw [hAeq]
    exact corollary7_6_cholesky_inverse_gram_isInverse R Rinv hRinv
  have hrecip : ∀ j : Fin n,
      ch7SymmetricDiagEquilibratingScale2 A j *
          ch7SymmetricDiagEquilibratingInvScale2 A j = 1 := by
    intro j
    have hsqrt : Real.sqrt (A j j) ≠ 0 :=
      ne_of_gt (Real.sqrt_pos.2 (hdiag j))
    simp [ch7SymmetricDiagEquilibratingScale2,
      ch7SymmetricDiagEquilibratingInvScale2, hsqrt]
  have hscaledInv :
      IsInverse n
        (ch7TwoSidedScale (ch7SymmetricDiagEquilibratingScale2 A) A
          (ch7SymmetricDiagEquilibratingScale2 A))
        (ch7TwoSidedScale (ch7SymmetricDiagEquilibratingInvScale2 A)
          (ch7CholeskyInverseGram Rinv)
          (ch7SymmetricDiagEquilibratingInvScale2 A)) :=
    corollary7_6_cholesky_scaled_inverse_gram_isInverse
      A R Rinv
      (ch7SymmetricDiagEquilibratingScale2 A)
      (ch7SymmetricDiagEquilibratingInvScale2 A)
      hGram hRinv hrecip
  exact ⟨hsym, hpsd, hAinv, hrecip, hscaledInv,
    corollary7_6_cholesky_scaled_cond_le_card_sInf_symmetric_scalings
      hn A R Rinv hGram hGramDiag hdiag⟩

/-- Higham's property A in permutation-free sign form.  The signs split the
indices into the two blocks of the source definition: entries inside either
block are diagonal, while cross-block entries are unrestricted.  Equivalently,
after a simultaneous permutation the matrix has a `2 × 2` block form whose
two diagonal blocks are diagonal. -/
def Higham7PropertyA {n : ℕ} (A : Fin n → Fin n → ℝ) : Prop :=
  ∃ s : Fin n → ℝ,
    (∀ i : Fin n, s i ^ 2 = 1) ∧
      ∀ i j : Fin n,
        s i * A i j * s j = if i = j then A i j else -A i j

/-- Property A is invariant under a simultaneous diagonal congruence. -/
lemma Higham7PropertyA.diagCongr
    {n : ℕ} {A : Fin n → Fin n → ℝ}
    (hA : Higham7PropertyA A) (d : Fin n → ℝ) :
    Higham7PropertyA (fun i j : Fin n => d i * A i j * d j) := by
  rcases hA with ⟨s, hs, hsign⟩
  refine ⟨s, hs, ?_⟩
  intro i j
  calc
    s i * (d i * A i j * d j) * s j =
        d i * (s i * A i j * s j) * d j := by ring
    _ = d i * (if i = j then A i j else -A i j) * d j := by
      rw [hsign i j]
    _ = if i = j then d i * A i j * d j else -(d i * A i j * d j) := by
      split <;> ring

/-- Spectral condition ratio for an SPD matrix. -/
noncomputable def higham7SPDConditionRatio
    {n : ℕ} (hn : 0 < n) (A : Fin n → Fin n → ℝ)
    (hSPD : IsSymPosDef n A) : ℝ :=
  finiteMaxEigenvalue hn A hSPD.1 / finiteMinEigenvalue hn A hSPD.1

/-- The SPD condition ratio is invariant under equality of the matrix; its
value is independent of the particular proof of positive definiteness. -/
lemma higham7SPDConditionRatio_congr
    {n : ℕ} (hn : 0 < n) {A B : Fin n → Fin n → ℝ}
    (hAB : A = B) (hA : IsSymPosDef n A) (hB : IsSymPosDef n B) :
    higham7SPDConditionRatio hn A hA =
      higham7SPDConditionRatio hn B hB := by
  subst B
  rfl

/-- The property-A sign involution preserves Euclidean norm. -/
lemma higham7_propertyA_sign_normSq
    {n : ℕ} {s x : Fin n → ℝ}
    (hs : ∀ i : Fin n, s i ^ 2 = 1) :
    (∑ i : Fin n, (s i * x i) ^ 2) = ∑ i : Fin n, x i ^ 2 := by
  apply Finset.sum_congr rfl
  intro i _
  rw [mul_pow, hs i, one_mul]

/-- For a unit-diagonal property-A matrix, the sign involution complements
every Rayleigh quadratic form about `1`:
`q_A(Sx) = 2‖x‖₂² - q_A(x)`. -/
lemma higham7_propertyA_quadForm_complement
    {n : ℕ} (A : Fin n → Fin n → ℝ) (s x : Fin n → ℝ)
    (hdiag : ∀ i : Fin n, A i i = 1)
    (hsign : ∀ i j : Fin n,
      s i * A i j * s j = if i = j then A i j else -A i j) :
    (∑ i : Fin n, ∑ j : Fin n,
        (s i * x i) * A i j * (s j * x j)) =
      2 * (∑ i : Fin n, x i ^ 2) -
        ∑ i : Fin n, ∑ j : Fin n, x i * A i j * x j := by
  classical
  calc
    (∑ i : Fin n, ∑ j : Fin n,
        (s i * x i) * A i j * (s j * x j)) =
        ∑ i : Fin n, ∑ j : Fin n,
          x i * (s i * A i j * s j) * x j := by
      apply Finset.sum_congr rfl
      intro i _
      apply Finset.sum_congr rfl
      intro j _
      ring
    _ = ∑ i : Fin n, ∑ j : Fin n,
          (2 * (if i = j then x i ^ 2 else 0) -
            x i * A i j * x j) := by
      apply Finset.sum_congr rfl
      intro i _
      apply Finset.sum_congr rfl
      intro j _
      rw [hsign i j]
      by_cases hij : i = j
      · subst j
        simp [hdiag i]
        ring
      · simp [hij]
    _ = 2 * (∑ i : Fin n, x i ^ 2) -
          ∑ i : Fin n, ∑ j : Fin n, x i * A i j * x j := by
      simp_rw [Finset.sum_sub_distrib]
      simp [Finset.mul_sum, Finset.sum_mul]

/-- An SPD matrix has a strictly positive finite minimum eigenvalue. -/
lemma higham7_finiteMinEigenvalue_pos_of_spd
    {n : ℕ} (hn : 0 < n) (A : Fin n → Fin n → ℝ)
    (hSPD : IsSymPosDef n A) :
    0 < finiteMinEigenvalue hn A hSPD.1 := by
  obtain ⟨a, ha⟩ := exists_finiteMinEigenvalue_eq hn A hSPD.1
  let x : Fin n → ℝ :=
    ⇑((IsSymmetricFiniteMatrix.to_matrix_isHermitian A hSPD.1).eigenvectorBasis a)
  have hnorm := finiteVecNorm2Sq_finiteHermitianEigenvector_eq_one
    A hSPD.1 a
  have hq :=
    finiteQuadraticForm_finiteHermitianEigenvector_eq_eigenvalue_mul_norm_sq
      A hSPD.1 a
  rw [hnorm, mul_one] at hq
  have hxsq : ∑ i : Fin n, x i ^ 2 = 1 := by
    simpa [x, finiteVecNorm2Sq] using hnorm
  have hx : ∃ i : Fin n, x i ≠ 0 := by
    by_contra h
    push_neg at h
    have : (∑ i : Fin n, x i ^ 2) = 0 := by simp [h]
    linarith
  have hpos := hSPD.2 x hx
  have hqv :
      (∑ i : Fin n, ∑ j : Fin n, x i * A i j * x j) =
        finiteMinEigenvalue hn A hSPD.1 := by
    rw [← ha, ← hq, finiteQuadraticForm_eq_sum_sum]
  rwa [hqv] at hpos

/-- The extreme eigenvalues of a unit-diagonal symmetric property-A matrix
are paired about `1`: `λ_min + λ_max = 2`. -/
theorem higham7_propertyA_min_add_max_eq_two
    {n : ℕ} (hn : 0 < n) (A : Fin n → Fin n → ℝ)
    (hSym : IsSymmetricFiniteMatrix A)
    (hdiag : ∀ i : Fin n, A i i = 1)
    (hA : Higham7PropertyA A) :
    finiteMinEigenvalue hn A hSym + finiteMaxEigenvalue hn A hSym = 2 := by
  rcases hA with ⟨s, hs, hsign⟩
  obtain ⟨amax, hamax⟩ := exists_finiteMaxEigenvalue_eq hn A hSym
  let xmax : Fin n → ℝ :=
    ⇑((IsSymmetricFiniteMatrix.to_matrix_isHermitian A hSym).eigenvectorBasis amax)
  have hmaxNorm := finiteVecNorm2Sq_finiteHermitianEigenvector_eq_one
    A hSym amax
  have hmaxQ :=
    finiteQuadraticForm_finiteHermitianEigenvector_eq_eigenvalue_mul_norm_sq
      A hSym amax
  rw [hmaxNorm, mul_one] at hmaxQ
  have hmaxNorm' : ∑ i : Fin n, xmax i ^ 2 = 1 := by
    simpa [xmax, finiteVecNorm2Sq] using hmaxNorm
  have hmaxQ' :
      (∑ i : Fin n, ∑ j : Fin n, xmax i * A i j * xmax j) =
        finiteMaxEigenvalue hn A hSym := by
    rw [← hamax, ← hmaxQ, finiteQuadraticForm_eq_sum_sum]
  have hminAtSigned := finiteMinEigenvalue_rayleigh hn A hSym
    (fun i => s i * xmax i)
  have hsignedMaxNorm :
      (∑ i : Fin n, (s i * xmax i) ^ 2) = 1 := by
    rw [higham7_propertyA_sign_normSq hs, hmaxNorm']
  have hsignedMaxQ :
      (∑ i : Fin n, ∑ j : Fin n,
        (s i * xmax i) * A i j * (s j * xmax j)) =
        2 - finiteMaxEigenvalue hn A hSym := by
    rw [higham7_propertyA_quadForm_complement A s xmax hdiag hsign,
      hmaxNorm', hmaxQ']
    ring
  rw [hsignedMaxNorm, mul_one, hsignedMaxQ] at hminAtSigned

  obtain ⟨amin, hamin⟩ := exists_finiteMinEigenvalue_eq hn A hSym
  let xmin : Fin n → ℝ :=
    ⇑((IsSymmetricFiniteMatrix.to_matrix_isHermitian A hSym).eigenvectorBasis amin)
  have hminNorm := finiteVecNorm2Sq_finiteHermitianEigenvector_eq_one
    A hSym amin
  have hminQ :=
    finiteQuadraticForm_finiteHermitianEigenvector_eq_eigenvalue_mul_norm_sq
      A hSym amin
  rw [hminNorm, mul_one] at hminQ
  have hminNorm' : ∑ i : Fin n, xmin i ^ 2 = 1 := by
    simpa [xmin, finiteVecNorm2Sq] using hminNorm
  have hminQ' :
      (∑ i : Fin n, ∑ j : Fin n, xmin i * A i j * xmin j) =
        finiteMinEigenvalue hn A hSym := by
    rw [← hamin, ← hminQ, finiteQuadraticForm_eq_sum_sum]
  have hmaxAtSigned := finiteMaxEigenvalue_rayleigh hn A hSym
    (fun i => s i * xmin i)
  have hsignedMinNorm :
      (∑ i : Fin n, (s i * xmin i) ^ 2) = 1 := by
    rw [higham7_propertyA_sign_normSq hs, hminNorm']
  have hsignedMinQ :
      (∑ i : Fin n, ∑ j : Fin n,
        (s i * xmin i) * A i j * (s j * xmin j)) =
        2 - finiteMinEigenvalue hn A hSym := by
    rw [higham7_propertyA_quadForm_complement A s xmin hdiag hsign,
      hminNorm', hminQ']
    ring
  rw [hsignedMinNorm, mul_one, hsignedMinQ] at hmaxAtSigned
  linarith

/-- Forsythe--Straus optimality quoted after Corollary 7.6: an SPD,
unit-diagonal property-A matrix has no better positive diagonal congruence in
the spectral condition-number ratio.  The proof uses the property-A sign
involution to pair the extreme eigenvalues, then tests an arbitrary congruence
on the sign-paired extremal vectors. -/
theorem higham7_propertyA_unitDiagonal_scaling_isOptimal
    {n : ℕ} (hn : 0 < n) (H : Fin n → Fin n → ℝ)
    (hSPD : IsSymPosDef n H)
    (hdiag : ∀ i : Fin n, H i i = 1)
    (hA : Higham7PropertyA H)
    (d : Fin n → ℝ) (hd : ∀ i : Fin n, 0 < d i) :
    finiteMaxEigenvalue hn H hSPD.1 /
        finiteMinEigenvalue hn H hSPD.1 ≤
      finiteMaxEigenvalue hn
          (fun i j : Fin n => d i * H i j * d j)
          (isSymPosDef_diagCongr n d H hd hSPD).1 /
        finiteMinEigenvalue hn
          (fun i j : Fin n => d i * H i j * d j)
          (isSymPosDef_diagCongr n d H hd hSPD).1 := by
  let M : Fin n → Fin n → ℝ := fun i j => d i * H i j * d j
  have hMSPD : IsSymPosDef n M := isSymPosDef_diagCongr n d H hd hSPD
  change finiteMaxEigenvalue hn H hSPD.1 /
      finiteMinEigenvalue hn H hSPD.1 ≤
    finiteMaxEigenvalue hn M hMSPD.1 /
      finiteMinEigenvalue hn M hMSPD.1
  rcases hA with ⟨s, hs, hsign⟩
  have hpair :
      finiteMinEigenvalue hn H hSPD.1 +
          finiteMaxEigenvalue hn H hSPD.1 = 2 :=
    higham7_propertyA_min_add_max_eq_two hn H hSPD.1 hdiag
      ⟨s, hs, hsign⟩
  have hminHpos := higham7_finiteMinEigenvalue_pos_of_spd hn H hSPD
  have hminMpos := higham7_finiteMinEigenvalue_pos_of_spd hn M hMSPD
  let i0 : Fin n := ⟨0, hn⟩
  have hminlemaxH :
      finiteMinEigenvalue hn H hSPD.1 ≤
        finiteMaxEigenvalue hn H hSPD.1 :=
    (finiteMinEigenvalue_le hn H hSPD.1 i0).trans
      (le_finiteMaxEigenvalue hn H hSPD.1 i0)
  have hminlemaxM :
      finiteMinEigenvalue hn M hMSPD.1 ≤
        finiteMaxEigenvalue hn M hMSPD.1 :=
    (finiteMinEigenvalue_le hn M hMSPD.1 i0).trans
      (le_finiteMaxEigenvalue hn M hMSPD.1 i0)
  have hmaxMnonneg : 0 ≤ finiteMaxEigenvalue hn M hMSPD.1 :=
    (le_of_lt hminMpos).trans hminlemaxM

  obtain ⟨amax, hamax⟩ := exists_finiteMaxEigenvalue_eq hn H hSPD.1
  let x : Fin n → ℝ :=
    ⇑((IsSymmetricFiniteMatrix.to_matrix_isHermitian H hSPD.1).eigenvectorBasis amax)
  have hxnorm := finiteVecNorm2Sq_finiteHermitianEigenvector_eq_one
    H hSPD.1 amax
  have hxQ :=
    finiteQuadraticForm_finiteHermitianEigenvector_eq_eigenvalue_mul_norm_sq
      H hSPD.1 amax
  rw [hxnorm, mul_one] at hxQ
  have hxnorm' : ∑ i : Fin n, x i ^ 2 = 1 := by
    simpa [x, finiteVecNorm2Sq] using hxnorm
  have hxQ' :
      (∑ i : Fin n, ∑ j : Fin n, x i * H i j * x j) =
        finiteMaxEigenvalue hn H hSPD.1 := by
    rw [← hamax, ← hxQ, finiteQuadraticForm_eq_sum_sum]
  have hxne : ∃ i : Fin n, x i ≠ 0 := by
    by_contra h
    push_neg at h
    have : (∑ i : Fin n, x i ^ 2) = 0 := by simp [h]
    linarith

  let z : Fin n → ℝ := fun i => x i / d i
  let zs : Fin n → ℝ := fun i => (s i * x i) / d i
  have hzne : ∃ i : Fin n, z i ≠ 0 := by
    rcases hxne with ⟨i, hi⟩
    exact ⟨i, div_ne_zero hi (ne_of_gt (hd i))⟩
  have hzsqpos : 0 < ∑ i : Fin n, z i ^ 2 :=
    sum_sq_pos_of_exists_ne n z hzne
  have hzsNorm : (∑ i : Fin n, zs i ^ 2) = ∑ i : Fin n, z i ^ 2 := by
    apply Finset.sum_congr rfl
    intro i _
    dsimp [zs, z]
    rw [div_pow, div_pow, mul_pow, hs i, one_mul]
  have hzQuad :
      (∑ i : Fin n, ∑ j : Fin n, z i * M i j * z j) =
        finiteMaxEigenvalue hn H hSPD.1 := by
    calc
      (∑ i : Fin n, ∑ j : Fin n, z i * M i j * z j) =
          ∑ i : Fin n, ∑ j : Fin n, x i * H i j * x j := by
        apply Finset.sum_congr rfl
        intro i _
        apply Finset.sum_congr rfl
        intro j _
        dsimp [z, M]
        field_simp [ne_of_gt (hd i), ne_of_gt (hd j)]
      _ = finiteMaxEigenvalue hn H hSPD.1 := hxQ'
  have hzsQuad :
      (∑ i : Fin n, ∑ j : Fin n, zs i * M i j * zs j) =
        finiteMinEigenvalue hn H hSPD.1 := by
    calc
      (∑ i : Fin n, ∑ j : Fin n, zs i * M i j * zs j) =
          ∑ i : Fin n, ∑ j : Fin n,
            (s i * x i) * H i j * (s j * x j) := by
        apply Finset.sum_congr rfl
        intro i _
        apply Finset.sum_congr rfl
        intro j _
        dsimp [zs, M]
        field_simp [ne_of_gt (hd i), ne_of_gt (hd j)]
      _ = 2 * (∑ i : Fin n, x i ^ 2) -
          ∑ i : Fin n, ∑ j : Fin n, x i * H i j * x j :=
        higham7_propertyA_quadForm_complement H s x hdiag hsign
      _ = finiteMinEigenvalue hn H hSPD.1 := by
        rw [hxnorm', hxQ']
        linarith
  have hmaxBound := finiteMaxEigenvalue_rayleigh hn M hMSPD.1 z
  rw [hzQuad] at hmaxBound
  have hminBound := finiteMinEigenvalue_rayleigh hn M hMSPD.1 zs
  rw [hzsNorm, hzsQuad] at hminBound
  rw [div_le_div_iff₀ hminHpos hminMpos]
  calc
    finiteMaxEigenvalue hn H hSPD.1 * finiteMinEigenvalue hn M hMSPD.1 ≤
        (finiteMaxEigenvalue hn M hMSPD.1 * (∑ i : Fin n, z i ^ 2)) *
          finiteMinEigenvalue hn M hMSPD.1 :=
      mul_le_mul_of_nonneg_right hmaxBound (le_of_lt hminMpos)
    _ = finiteMaxEigenvalue hn M hMSPD.1 *
          (finiteMinEigenvalue hn M hMSPD.1 * (∑ i : Fin n, z i ^ 2)) := by
      ring
    _ ≤ finiteMaxEigenvalue hn M hMSPD.1 *
          finiteMinEigenvalue hn H hSPD.1 :=
      mul_le_mul_of_nonneg_left hminBound hmaxMnonneg

/-- Source-shaped Forsythe--Straus result following Corollary 7.6.  If `A` is
SPD with property A, then the printed scaling
`D* = diag(a_ii^{-1/2})` is optimal among all positive diagonal congruences.
The theorem also returns the genuine SPD certificate and unit diagonal for the
scaled matrix, so the condition ratios are not merely symbolic expressions. -/
theorem higham7_6_propertyA_source_scaling_isOptimal
    {n : ℕ} (hn : 0 < n) (A : Fin n → Fin n → ℝ)
    (hSPD : IsSymPosDef n A) (hA : Higham7PropertyA A)
    (d : Fin n → ℝ) (hd : ∀ i : Fin n, 0 < d i) :
    let Dstar : Fin n → ℝ := ch7SymmetricDiagEquilibratingScale2 A
    let H : Fin n → Fin n → ℝ := ch7TwoSidedScale Dstar A Dstar
    let M : Fin n → Fin n → ℝ := ch7TwoSidedScale d A d
    ∃ (hHSPD : IsSymPosDef n H) (hMSPD : IsSymPosDef n M),
      Higham7PropertyA H ∧
        (∀ i : Fin n, H i i = 1) ∧
        higham7SPDConditionRatio hn H hHSPD ≤
          higham7SPDConditionRatio hn M hMSPD := by
  dsimp only
  let Dstar : Fin n → ℝ := ch7SymmetricDiagEquilibratingScale2 A
  let H : Fin n → Fin n → ℝ := ch7TwoSidedScale Dstar A Dstar
  let M : Fin n → Fin n → ℝ := ch7TwoSidedScale d A d
  have hAdiag : ∀ i : Fin n, 0 < A i i := by
    intro i
    have hi : ∃ k : Fin n, (fun k => if k = i then (1 : ℝ) else 0) k ≠ 0 := by
      exact ⟨i, by simp⟩
    have hpos := hSPD.2 (fun k => if k = i then (1 : ℝ) else 0) hi
    simpa [Finset.sum_ite_eq', Finset.mem_univ] using hpos
  have hDstar : ∀ i : Fin n, 0 < Dstar i := by
    intro i
    dsimp [Dstar, ch7SymmetricDiagEquilibratingScale2]
    exact one_div_pos.mpr (Real.sqrt_pos.2 (hAdiag i))
  have hHSPD : IsSymPosDef n H := by
    dsimp [H, ch7TwoSidedScale]
    exact isSymPosDef_diagCongr n Dstar A hDstar hSPD
  have hMSPD : IsSymPosDef n M := by
    dsimp [M, ch7TwoSidedScale]
    exact isSymPosDef_diagCongr n d A hd hSPD
  have hHA : Higham7PropertyA H := by
    dsimp [H, ch7TwoSidedScale]
    exact hA.diagCongr Dstar
  have hHdiag : ∀ i : Fin n, H i i = 1 := by
    intro i
    dsimp [H, Dstar, ch7TwoSidedScale,
      ch7SymmetricDiagEquilibratingScale2]
    have hsqrt := Real.sqrt_pos.2 (hAdiag i)
    field_simp [ne_of_gt hsqrt]
    nlinarith [Real.sq_sqrt (le_of_lt (hAdiag i))]
  let e : Fin n → ℝ := fun i => d i * Real.sqrt (A i i)
  have he : ∀ i : Fin n, 0 < e i := by
    intro i
    exact mul_pos (hd i) (Real.sqrt_pos.2 (hAdiag i))
  have hscaledEq :
      (fun i j : Fin n => e i * H i j * e j) = M := by
    funext i j
    dsimp [e, H, M, Dstar, ch7TwoSidedScale,
      ch7SymmetricDiagEquilibratingScale2]
    have hi := Real.sqrt_pos.2 (hAdiag i)
    have hj := Real.sqrt_pos.2 (hAdiag j)
    field_simp [ne_of_gt hi, ne_of_gt hj]
  have hopt := higham7_propertyA_unitDiagonal_scaling_isOptimal
    hn H hHSPD hHdiag hHA e he
  change higham7SPDConditionRatio hn H hHSPD ≤
    higham7SPDConditionRatio hn
      (fun i j : Fin n => e i * H i j * e j)
      (isSymPosDef_diagCongr n e H he hHSPD) at hopt
  have hratioEq := higham7SPDConditionRatio_congr hn hscaledEq
    (isSymPosDef_diagCongr n e H he hHSPD) hMSPD
  have hfinal := hopt.trans_eq hratioEq
  simpa [Dstar, H, M] using
    (show ∃ (hHSPD : IsSymPosDef n H) (hMSPD : IsSymPosDef n M),
        Higham7PropertyA H ∧
          (∀ i : Fin n, H i i = 1) ∧
          higham7SPDConditionRatio hn H hHSPD ≤
            higham7SPDConditionRatio hn M hMSPD from
      ⟨hHSPD, hMSPD, hHA, hHdiag, hfinal⟩)

/-- Complexifying a real column preserves its Euclidean norm, expressed in
the Chapter 6 `p = 2` vector-norm API used by the sparse-row form of (6.23). -/
lemma higham7_complex_column_two_norm_eq_real_column_norm
    {m n : ℕ} (A : Fin m → Fin n → ℝ) (j : Fin n) :
    complexVecLpNorm (ENNReal.ofReal (2 : ℝ))
        (fun i : Fin m => realRectToCMatrix A i j) =
      ch7RectColumnNorm2 A j := by
  letI : Fact (1 ≤ ENNReal.ofReal (2 : ℝ)) := ⟨by norm_num⟩
  have hcomplex := complexVecLpNorm_rpow_eq_sum_rpow
    (p := (2 : ℝ)) (by norm_num) (fun i : Fin m => realRectToCMatrix A i j)
  have hcomplex_sq :
      complexVecLpNorm (ENNReal.ofReal (2 : ℝ))
          (fun i : Fin m => realRectToCMatrix A i j) ^ 2 =
        ∑ i : Fin m, ‖realRectToCMatrix A i j‖ ^ 2 := by
    simpa [Real.rpow_natCast] using hcomplex
  have hreal := vecNorm2_sq (fun i : Fin m => A i j)
  apply (sq_eq_sq₀
    ((complexVecLpNorm_isComplexVectorNorm
      (ENNReal.ofReal (2 : ℝ))).nonneg
        (fun i : Fin m => realRectToCMatrix A i j))
    (ch7RectColumnNorm2_nonneg A j)).mp
  rw [hcomplex_sq]
  rw [show ch7RectColumnNorm2 A j = vecNorm2 (fun i : Fin m => A i j) from rfl,
    hreal]
  simp [realRectToCMatrix, vecNorm2Sq, sq_abs]

/-- A nonzero diagonal right scaling preserves every row support. -/
lemma higham7_complexified_rightScale_rowSupport_eq
    {m n : ℕ} (A : Fin m → Fin n → ℝ) (d : Fin n → ℝ)
    (hd : ∀ j : Fin n, d j ≠ 0) (i : Fin m) :
    complexMatrixRowSupport
        (realRectToCMatrix (ch7RectRightScale A d)) i =
      complexMatrixRowSupport (realRectToCMatrix A) i := by
  classical
  ext j
  simp [complexMatrixRowSupport, realRectToCMatrix, ch7RectRightScale,
    hd j]

/-- Row sparsity is therefore unchanged by the source column-equilibrating
diagonal, whose entries are nonzero when all columns are nonzero. -/
lemma higham7_column_equilibratingScale_preserves_sparseRows
    {m n μ : ℕ} (A : Fin m → Fin n → ℝ)
    (hcol : ∀ j : Fin n, 0 < ch7RectColumnNorm2 A j)
    (hrows : complexMatrixRowsSupportCardLe (realRectToCMatrix A) μ) :
    complexMatrixRowsSupportCardLe
      (realRectToCMatrix
        (ch7RectRightScale A (ch7ColumnEquilibratingScale2 A))) μ := by
  intro i
  rw [higham7_complexified_rightScale_rowSupport_eq A
    (ch7ColumnEquilibratingScale2 A)
    (fun j => by
      unfold ch7ColumnEquilibratingScale2
      exact one_div_ne_zero (ne_of_gt (hcol j))) i]
  exact hrows i

/-- Sparse-row strengthening of (7.21): if every row has at most `μ`
nonzeros, column equilibration has operator 2-norm at most `sqrt μ`, replacing
the ambient `sqrt n` factor exactly as stated after Corollary 7.6. -/
theorem higham7_sparseRows_column_equilibrated_op2_le_sqrt
    {m n μ : ℕ} (hn : 0 < n)
    (A : Fin m → Fin n → ℝ)
    (hcol : ∀ j : Fin n, 0 < ch7RectColumnNorm2 A j)
    (hrows : complexMatrixRowsSupportCardLe (realRectToCMatrix A) μ) :
    complexMatrixOp2
        (realRectToCMatrix
          (ch7RectRightScale A (ch7ColumnEquilibratingScale2 A))) ≤
      Real.sqrt (μ : ℝ) := by
  letI : Fact (1 ≤ ENNReal.ofReal (2 : ℝ)) := ⟨by norm_num⟩
  let B : Fin m → Fin n → ℝ :=
    ch7RectRightScale A (ch7ColumnEquilibratingScale2 A)
  have hrowsB : complexMatrixRowsSupportCardLe (realRectToCMatrix B) μ := by
    dsimp [B]
    exact higham7_column_equilibratingScale_preserves_sparseRows A hcol hrows
  have hsparse :=
    (complexMatrixLpNormOfReal_sparseRows_bounds
      (m := m) (n := n) (μ := μ) hn (p := (2 : ℝ)) (by norm_num)
      hrowsB).2
  have hcolmax :
      complexMatrixColumnMaxVectorNorm
          (complexVecLpNorm (n := m) (ENNReal.ofReal (2 : ℝ)))
          (realRectToCMatrix B) ≤ 1 := by
    apply complexMatrixColumnMaxVectorNorm_le_of_col_le
      (complexVecLpNorm_isComplexVectorNorm
        (ENNReal.ofReal (2 : ℝ))) (by norm_num)
    intro j
    rw [higham7_complex_column_two_norm_eq_real_column_norm B j]
    dsimp [B]
    rw [ch7RectColumnNorm2_rightScale_equilibrating A hcol j]
  rw [complexMatrixLpNormOfReal_two_eq_complexMatrixOp2] at hsparse
  calc
    complexMatrixOp2 (realRectToCMatrix B) ≤
        (μ : ℝ) ^ (1 - (2 : ℝ)⁻¹) *
          complexMatrixColumnMaxVectorNorm
            (complexVecLpNorm (n := m) (ENNReal.ofReal (2 : ℝ)))
            (realRectToCMatrix B) := hsparse
    _ ≤ (μ : ℝ) ^ (1 - (2 : ℝ)⁻¹) * 1 :=
      mul_le_mul_of_nonneg_left hcolmax
        (Real.rpow_nonneg (Nat.cast_nonneg μ) _)
    _ = Real.sqrt (μ : ℝ) := by
      norm_num [Real.sqrt_eq_rpow]

/-- Sparse-row version of Theorem 7.5, equation (7.18), at `p = 2`:
the ambient `sqrt n` factor is replaced by the square root of the maximum row
support size. -/
theorem higham7_5_p2_column_equilibration_le_sqrt_sparseRows_right_scaling
    {m n μ : ℕ} (hn : 0 < n)
    (A : Fin m → Fin n → ℝ) (Aplus : Fin n → Fin m → ℝ)
    (hcol : ∀ j : Fin n, 0 < ch7RectColumnNorm2 A j)
    (hrows : complexMatrixRowsSupportCardLe (realRectToCMatrix A) μ)
    (d dInv : Fin n → ℝ)
    (hdiag : ∀ j : Fin n, d j * dInv j = 1) :
    ch7Op2RightScaledCond A Aplus
        (ch7ColumnEquilibratingScale2 A)
        (fun j : Fin n => ch7RectColumnNorm2 A j) ≤
      Real.sqrt (μ : ℝ) * ch7Op2RightScaledCond A Aplus d dInv := by
  unfold ch7Op2RightScaledCond
  let ADc : Fin m → Fin n → ℝ :=
    ch7RectRightScale A (ch7ColumnEquilibratingScale2 A)
  let AplusDcInv : Fin n → Fin m → ℝ :=
    ch7RectLeftScale (fun j : Fin n => ch7RectColumnNorm2 A j) Aplus
  let AD : Fin m → Fin n → ℝ := ch7RectRightScale A d
  let DinvAplus : Fin n → Fin m → ℝ := ch7RectLeftScale dInv Aplus
  have hADc :
      complexMatrixOp2 (realRectToCMatrix ADc) ≤ Real.sqrt (μ : ℝ) := by
    dsimp [ADc]
    exact higham7_sparseRows_column_equilibrated_op2_le_sqrt
      hn A hcol hrows
  have hside :
      complexMatrixOp2 (realRectToCMatrix AplusDcInv) ≤
        complexMatrixOp2 (realRectToCMatrix AD) *
          complexMatrixOp2 (realRectToCMatrix DinvAplus) := by
    dsimp [AplusDcInv, AD, DinvAplus]
    exact eq_7_22_op2_inverseSide_bound A Aplus d dInv hdiag
  have hAplusDcInv_nonneg :
      0 ≤ complexMatrixOp2 (realRectToCMatrix AplusDcInv) :=
    complexMatrixOp2_nonneg _
  calc
    complexMatrixOp2 (realRectToCMatrix ADc) *
        complexMatrixOp2 (realRectToCMatrix AplusDcInv) ≤
      Real.sqrt (μ : ℝ) *
        complexMatrixOp2 (realRectToCMatrix AplusDcInv) :=
      mul_le_mul_of_nonneg_right hADc hAplusDcInv_nonneg
    _ ≤ Real.sqrt (μ : ℝ) *
        (complexMatrixOp2 (realRectToCMatrix AD) *
          complexMatrixOp2 (realRectToCMatrix DinvAplus)) :=
      mul_le_mul_of_nonneg_left hside (Real.sqrt_nonneg _)

/-- Infimum form of the sparse-row Theorem 7.5 refinement. -/
theorem higham7_5_p2_column_equilibration_le_sqrt_sparseRows_sInf
    {m n μ : ℕ} (hn : 0 < n) (hμ : 0 < μ)
    (A : Fin m → Fin n → ℝ) (Aplus : Fin n → Fin m → ℝ)
    (hcol : ∀ j : Fin n, 0 < ch7RectColumnNorm2 A j)
    (hrows : complexMatrixRowsSupportCardLe (realRectToCMatrix A) μ) :
    ch7Op2RightScaledCond A Aplus
        (ch7ColumnEquilibratingScale2 A)
        (fun j : Fin n => ch7RectColumnNorm2 A j) ≤
      Real.sqrt (μ : ℝ) * sInf (ch7Op2RightScaledCondSet A Aplus) := by
  let c : ℝ := ch7Op2RightScaledCond A Aplus
    (ch7ColumnEquilibratingScale2 A)
    (fun j : Fin n => ch7RectColumnNorm2 A j)
  let S : Set ℝ := ch7Op2RightScaledCondSet A Aplus
  let α : ℝ := Real.sqrt (μ : ℝ)
  have hαpos : 0 < α := Real.sqrt_pos.2 (Nat.cast_pos.mpr hμ)
  have hS_nonempty : S.Nonempty := by
    simpa [S] using ch7Op2RightScaledCondSet_nonempty A Aplus
  have hlower : ∀ κ : ℝ, κ ∈ S → c / α ≤ κ := by
    intro κ hκ
    rcases hκ with ⟨d, dInv, hdiag, rfl⟩
    rw [div_le_iff₀ hαpos]
    simpa [c, α, mul_comm] using
      higham7_5_p2_column_equilibration_le_sqrt_sparseRows_right_scaling
        hn A Aplus hcol hrows d dInv hdiag
  have hsInf : c / α ≤ sInf S := le_csInf hS_nonempty hlower
  have hmul := mul_le_mul_of_nonneg_left hsInf (le_of_lt hαpos)
  have hcancel : α * (c / α) = c := by
    field_simp [ne_of_gt hαpos]
  change c ≤ α * sInf S
  exact hcancel ▸ hmul

/-- Sparse-row strengthening of Corollary 7.6.  If every row of the Cholesky
factor `R` has at most `μ` nonzeros, the factor `n` in (7.23) is replaced by
`μ`; this is the printed refinement obtained from sparse equation (6.23). -/
theorem higham7_6_cholesky_scaled_cond_le_sparseRows_sInf
    {n μ : ℕ} (hn : 0 < n) (hμ : 0 < μ)
    (A R Rinv : Fin n → Fin n → ℝ)
    (hGram : ∀ i j : Fin n, (∑ k : Fin n, R k i * R k j) = A i j)
    (hGramDiag : ∀ j : Fin n, (∑ k : Fin n, R k j * R k j) = A j j)
    (hdiag : ∀ j : Fin n, 0 < A j j)
    (hrows : complexMatrixRowsSupportCardLe (realRectToCMatrix R) μ) :
    ch7SymmetricOp2ScaledCond A (ch7CholeskyInverseGram Rinv)
        (ch7SymmetricDiagEquilibratingScale2 A)
        (ch7SymmetricDiagEquilibratingInvScale2 A) ≤
      (μ : ℝ) *
        sInf (ch7SymmetricOp2ScaledCondSet A
          (ch7CholeskyInverseGram Rinv)) := by
  let d : Fin n → ℝ := ch7SymmetricDiagEquilibratingScale2 A
  let dInv : Fin n → ℝ := ch7SymmetricDiagEquilibratingInvScale2 A
  let c : ℝ := ch7Op2RightScaledCond R Rinv d dInv
  let S : Set ℝ := ch7Op2RightScaledCondSet R Rinv
  let T : Set ℝ :=
    ch7SymmetricOp2ScaledCondSet A (ch7CholeskyInverseGram Rinv)
  have hscale := corollary7_6_cholesky_diag_scale_eq_column_equilibrating
    A R hGramDiag hdiag
  have hinvScale := corollary7_6_cholesky_diag_invScale_eq_column_norm
    A R hGramDiag hdiag
  have hcol := corollary7_6_cholesky_column_norm_pos
    A R hGramDiag hdiag
  have hfactor : c ≤ Real.sqrt (μ : ℝ) * sInf S := by
    dsimp [c, d, dInv, S]
    rw [hscale, hinvScale]
    exact higham7_5_p2_column_equilibration_le_sqrt_sparseRows_sInf
      hn hμ R Rinv hcol hrows
  have hc_nonneg : 0 ≤ c := by
    dsimp [c]
    exact ch7Op2RightScaledCond_nonneg R Rinv d dInv
  have hsInf_nonneg : 0 ≤ sInf S := by
    simpa [S] using ch7Op2RightScaledCondSet_sInf_nonneg R Rinv
  have hrhs_nonneg : 0 ≤ Real.sqrt (μ : ℝ) * sInf S :=
    mul_nonneg (Real.sqrt_nonneg _) hsInf_nonneg
  have hsq : c ^ 2 ≤ (Real.sqrt (μ : ℝ) * sInf S) ^ 2 :=
    (sq_le_sq₀ hc_nonneg hrhs_nonneg).mpr hfactor
  have hcond :
      ch7SymmetricOp2ScaledCond A (ch7CholeskyInverseGram Rinv) d dInv =
        c ^ 2 := by
    dsimp [c]
    exact corollary7_6_cholesky_scaled_cond_eq_factor_cond_sq
      A R Rinv d dInv hGram
  have hsqrt_sq :
      (Real.sqrt (μ : ℝ) * sInf S) ^ 2 =
        (μ : ℝ) * (sInf S) ^ 2 := by
    rw [mul_pow, Real.sq_sqrt (Nat.cast_nonneg μ)]
  have hfactorSq :
      ch7SymmetricOp2ScaledCond A (ch7CholeskyInverseGram Rinv)
          (ch7SymmetricDiagEquilibratingScale2 A)
          (ch7SymmetricDiagEquilibratingInvScale2 A) ≤
        (μ : ℝ) * (sInf S) ^ 2 := by
    rw [show ch7SymmetricDiagEquilibratingScale2 A = d from rfl,
      show ch7SymmetricDiagEquilibratingInvScale2 A = dInv from rfl,
      hcond]
    rw [hsqrt_sq] at hsq
    exact hsq
  have htransfer : (sInf S) ^ 2 ≤ sInf T := by
    simpa [S, T] using
      corollary7_6_cholesky_right_sInf_sq_le_symmetric_sInf A R Rinv hGram
  have hmul : (μ : ℝ) * (sInf S) ^ 2 ≤ (μ : ℝ) * sInf T :=
    mul_le_mul_of_nonneg_left htransfer (Nat.cast_nonneg μ)
  exact hfactorSq.trans (by simpa [T] using hmul)

/-- Fully source-facing sparse Corollary 7.6 wrapper: alongside the refined
factor-`μ` estimate, it certifies the SPD semantics, both inverse identities,
and reciprocity of the printed diagonal pair. -/
theorem higham7_6_spd_sparseRows_source_scaling_bound
    {n μ : ℕ} (hn : 0 < n) (hμ : 0 < μ)
    (A R Rinv : Fin n → Fin n → ℝ)
    (hGram : ∀ i j : Fin n, (∑ k : Fin n, R k i * R k j) = A i j)
    (hGramDiag : ∀ j : Fin n, (∑ k : Fin n, R k j * R k j) = A j j)
    (hdiag : ∀ j : Fin n, 0 < A j j)
    (hRinv : IsInverse n R Rinv)
    (hrows : complexMatrixRowsSupportCardLe (realRectToCMatrix R) μ) :
    IsSymmetricFiniteMatrix A ∧
      finitePSD A ∧
      IsInverse n A (ch7CholeskyInverseGram Rinv) ∧
      (∀ j : Fin n,
        ch7SymmetricDiagEquilibratingScale2 A j *
            ch7SymmetricDiagEquilibratingInvScale2 A j = 1) ∧
      IsInverse n
        (ch7TwoSidedScale (ch7SymmetricDiagEquilibratingScale2 A) A
          (ch7SymmetricDiagEquilibratingScale2 A))
        (ch7TwoSidedScale (ch7SymmetricDiagEquilibratingInvScale2 A)
          (ch7CholeskyInverseGram Rinv)
          (ch7SymmetricDiagEquilibratingInvScale2 A)) ∧
      ch7SymmetricOp2ScaledCond A (ch7CholeskyInverseGram Rinv)
          (ch7SymmetricDiagEquilibratingScale2 A)
          (ch7SymmetricDiagEquilibratingInvScale2 A) ≤
        (μ : ℝ) *
          sInf (ch7SymmetricOp2ScaledCondSet A
            (ch7CholeskyInverseGram Rinv)) := by
  have hbase := higham7_6_spd_source_scaling_bound
    hn A R Rinv hGram hGramDiag hdiag hRinv
  exact ⟨hbase.1, hbase.2.1, hbase.2.2.1, hbase.2.2.2.1,
    hbase.2.2.2.2.1,
    higham7_6_cholesky_scaled_cond_le_sparseRows_sInf
      hn hμ A R Rinv hGram hGramDiag hdiag hrows⟩

lemma higham7_abs_eq_one_of_sq_eq_one {x : ℝ} (hx : x ^ 2 = 1) :
    |x| = 1 := by
  have habsSq : |x| ^ 2 = 1 := by
    simpa [sq_abs] using hx
  nlinarith [abs_nonneg x]

namespace Higham8MatrixFamilyIsBigO

theorem const {ι : Type*} {n : ℕ} {l : Filter ι}
    (A : Matrix (Fin n) (Fin n) ℝ) :
    Higham8MatrixFamilyIsBigO l (fun _ : ι => (1 : ℝ)) (fun _ => A) := by
  intro i j
  exact ScalarFamilyIsBigOOne.const (A i j)

theorem add {ι : Type*} {n : ℕ} {l : Filter ι} {s : ι → ℝ}
    {A B : ι → Matrix (Fin n) (Fin n) ℝ}
    (hA : Higham8MatrixFamilyIsBigO l s A)
    (hB : Higham8MatrixFamilyIsBigO l s B) :
    Higham8MatrixFamilyIsBigO l s (fun t => A t + B t) := by
  intro i j
  simpa using (hA i j).add (hB i j)

theorem abs {ι : Type*} {n : ℕ} {l : Filter ι} {s : ι → ℝ}
    {A : ι → Matrix (Fin n) (Fin n) ℝ}
    (hA : Higham8MatrixFamilyIsBigO l s A) :
    Higham8MatrixFamilyIsBigO l s (fun t i j => |A t i j|) := by
  intro i j
  simpa only [Real.norm_eq_abs] using (hA i j).norm_left

theorem mul {ι : Type*} {n : ℕ} {l : Filter ι} {s r : ι → ℝ}
    {A B : ι → Matrix (Fin n) (Fin n) ℝ}
    (hA : Higham8MatrixFamilyIsBigO l s A)
    (hB : Higham8MatrixFamilyIsBigO l r B) :
    Higham8MatrixFamilyIsBigO l (fun t => s t * r t)
      (fun t => A t * B t) := by
  intro i j
  simp only [Matrix.mul_apply]
  apply Asymptotics.IsBigO.sum
  intro k _hk
  exact (hA i k).mul (hB k j)

theorem unit_mul_unit {ι : Type*} {n : ℕ} {l : Filter ι} {u : ι → ℝ}
    {A B : ι → Matrix (Fin n) (Fin n) ℝ}
    (hA : Higham8MatrixFamilyIsBigO l u A)
    (hB : Higham8MatrixFamilyIsBigO l u B) :
    Higham8MatrixFamilyIsBigO l (fun t => u t ^ 2) (fun t => A t * B t) := by
  simpa only [pow_two] using hA.mul hB

theorem unit_mul_one {ι : Type*} {n : ℕ} {l : Filter ι} {u : ι → ℝ}
    {A B : ι → Matrix (Fin n) (Fin n) ℝ}
    (hA : Higham8MatrixFamilyIsBigO l u A)
    (hB : Higham8MatrixFamilyIsBigO l (fun _ : ι => (1 : ℝ)) B) :
    Higham8MatrixFamilyIsBigO l u (fun t => A t * B t) := by
  simpa only [mul_one] using hA.mul hB

theorem one_mul_unit {ι : Type*} {n : ℕ} {l : Filter ι} {u : ι → ℝ}
    {A B : ι → Matrix (Fin n) (Fin n) ℝ}
    (hA : Higham8MatrixFamilyIsBigO l (fun _ : ι => (1 : ℝ)) A)
    (hB : Higham8MatrixFamilyIsBigO l u B) :
    Higham8MatrixFamilyIsBigO l u (fun t => A t * B t) := by
  simpa only [one_mul] using hA.mul hB

theorem sq_mul_one {ι : Type*} {n : ℕ} {l : Filter ι} {u : ι → ℝ}
    {A B : ι → Matrix (Fin n) (Fin n) ℝ}
    (hA : Higham8MatrixFamilyIsBigO l (fun t => u t ^ 2) A)
    (hB : Higham8MatrixFamilyIsBigO l (fun _ : ι => (1 : ℝ)) B) :
    Higham8MatrixFamilyIsBigO l (fun t => u t ^ 2) (fun t => A t * B t) := by
  simpa only [mul_one] using hA.mul hB

theorem one_mul_sq {ι : Type*} {n : ℕ} {l : Filter ι} {u : ι → ℝ}
    {A B : ι → Matrix (Fin n) (Fin n) ℝ}
    (hA : Higham8MatrixFamilyIsBigO l (fun _ : ι => (1 : ℝ)) A)
    (hB : Higham8MatrixFamilyIsBigO l (fun t => u t ^ 2) B) :
    Higham8MatrixFamilyIsBigO l (fun t => u t ^ 2) (fun t => A t * B t) := by
  simpa only [one_mul] using hA.mul hB

theorem unit_to_one {ι : Type*} {n : ℕ} {l : Filter ι} {u : ι → ℝ}
    {A : ι → Matrix (Fin n) (Fin n) ℝ}
    (hA : Higham8MatrixFamilyIsBigO l u A)
    (hu : Tendsto u l (𝓝 0)) :
    Higham8MatrixFamilyIsBigO l (fun _ : ι => (1 : ℝ)) A := by
  intro i j
  exact (hA i j).trans (hu.isBigO_one ℝ)

theorem sq_to_one {ι : Type*} {n : ℕ} {l : Filter ι} {u : ι → ℝ}
    {A : ι → Matrix (Fin n) (Fin n) ℝ}
    (hA : Higham8MatrixFamilyIsBigO l (fun t => u t ^ 2) A)
    (hu : Tendsto u l (𝓝 0)) :
    Higham8MatrixFamilyIsBigO l (fun _ : ι => (1 : ℝ)) A := by
  intro i j
  exact (hA i j).trans ((hu.pow 2).isBigO_one ℝ)

end Higham8MatrixFamilyIsBigO

/-- Right-handed form of the nonnegative resolvent comparison. -/
theorem higham9_15_resolvent_matrix_majorant_right_of_componentwise_inequality
    {n : ℕ} (M R V W : Matrix (Fin n) (Fin n) ℝ)
    (hR : ch7NonnegativeResolvent n M R)
    (hineq : ∀ i j : Fin n,
      W i j ≤ V i j + rectMatMul W M i j) :
    ∀ i j : Fin n, W i j ≤ rectMatMul V R i j := by
  have hRT : ch7NonnegativeResolvent n
      (finiteTranspose M) (finiteTranspose R) := by
    refine ⟨?_, ?_⟩
    · intro i j
      exact hR.1 j i
    · have hright : IsRightInverse n (matSub_id n M) R :=
        ch7_isRightInverse_of_isLeftInverse hR.2
      have ht := isLeftInverse_finiteTranspose_of_isRightInverse hright
      have hsubT : finiteTranspose (matSub_id n M) =
          matSub_id n (finiteTranspose M) := by
        ext i j
        simp [finiteTranspose, matSub_id, idMatrix, eq_comm]
      simpa [hsubT] using ht
  have hineqT : ∀ i j : Fin n,
      finiteTranspose W i j ≤
        finiteTranspose V i j +
          rectMatMul (finiteTranspose M) (finiteTranspose W) i j := by
    intro i j
    have h := hineq j i
    simpa [finiteTranspose, rectMatMul, mul_comm] using h
  have hmajorT :=
    higham9_15_resolvent_matrix_majorant_of_componentwise_inequality
      (finiteTranspose M) (finiteTranspose R)
      (finiteTranspose V) (finiteTranspose W) hRT hineqT
  intro i j
  have h := hmajorT j i
  simpa [finiteTranspose, rectMatMul, mul_comm] using h

end NumStability
