import NumStability.Algorithms.Cholesky.Higham1014SourceError
import NumStability.Algorithms.HighamChapter10
import NumStability.Analysis.FirstOrder

namespace NumStability

open Filter Asymptotics
open scoped BigOperators Topology

/-!
# Higham Theorem 10.14, equation (10.22)

This module supplies the algebraic and asymptotic bridge deliberately omitted
from `Higham1014SourceError`.  All matrices occurring below are extracted from
the literal truncated execution of Algorithm 10.2.  In particular, the error
and trailing Schur block are definitions, not caller-provided backward-error
certificates.
-/

section Blocks

variable {r s : ℕ}

/-- Leading principal block in the fixed `Fin r ⊕ Fin s` partition. -/
def higham10_14_block11
    (A : Fin (r + s) → Fin (r + s) → ℝ) : Fin r → Fin r → ℝ :=
  fun i j => A (Fin.castAdd s i) (Fin.castAdd s j)

/-- North-east block in the fixed `Fin r ⊕ Fin s` partition. -/
def higham10_14_block12
    (A : Fin (r + s) → Fin (r + s) → ℝ) : Fin r → Fin s → ℝ :=
  fun i j => A (Fin.castAdd s i) (Fin.natAdd r j)

/-- South-west block in the fixed `Fin r ⊕ Fin s` partition. -/
def higham10_14_block21
    (A : Fin (r + s) → Fin (r + s) → ℝ) : Fin s → Fin r → ℝ :=
  fun i j => A (Fin.natAdd r i) (Fin.castAdd s j)

/-- Trailing principal block in the fixed `Fin r ⊕ Fin s` partition. -/
def higham10_14_block22
    (A : Fin (r + s) → Fin (r + s) → ℝ) : Fin s → Fin s → ℝ :=
  fun i j => A (Fin.natAdd r i) (Fin.natAdd r j)

/-- The computed `r × r` triangular block of the actual factor. -/
noncomputable def higham10_14_actualR11 (fp : FPModel)
    (A : Fin (r + s) → Fin (r + s) → ℝ) : Fin r → Fin r → ℝ :=
  fun i j => fl_cholesky fp (r + s) A (Fin.castAdd s i) (Fin.castAdd s j)

/-- The computed `r × s` border block of the actual factor. -/
noncomputable def higham10_14_actualR12 (fp : FPModel)
    (A : Fin (r + s) → Fin (r + s) → ℝ) : Fin r → Fin s → ℝ :=
  fun i j => fl_cholesky fp (r + s) A (Fin.castAdd s i) (Fin.natAdd r j)

/-- The literal trailing block left by the rounded `r`-stage execution. -/
noncomputable def higham10_14_actualSchur (fp : FPModel)
    (A : Fin (r + s) → Fin (r + s) → ℝ) : Fin s → Fin s → ℝ :=
  higham10_14_block22
    (higham10_14_sourceTrailing fp A r (Nat.le_add_right r s))

/-- The fixed matrix `W = A₁₁⁻¹ A₁₂` appearing in (10.22). -/
noncomputable def higham10_14_W
    (A : Fin (r + s) → Fin (r + s) → ℝ) : Fin r → Fin s → ℝ :=
  rectMatMul (nonsingInv r (higham10_14_block11 A))
    (higham10_14_block12 A)

/-- The literal matrix `A - R̂ᵣᵀR̂ᵣ` in (10.22), with `R̂ᵣ` produced by
the rounded `r`-stage Cholesky executor. -/
noncomputable def higham10_14_actualResidual (fp : FPModel)
    (A : Fin (r + s) → Fin (r + s) → ℝ) :
    Fin (r + s) → Fin (r + s) → ℝ :=
  fun i j => A i j -
    ∑ k : Fin (r + s),
      fl_choleskyTrunc fp (r + s) A r k i *
        fl_choleskyTrunc fp (r + s) A r k j

/-- The fixed coefficient multiplying `‖E‖₂²` in the quantitative
Lemma 10.10 specialization used below. -/
noncomputable def higham10_14_schurQuadraticCoeff
    (A : Fin (r + s) → Fin (r + s) → ℝ) : ℝ :=
  let a := complexMatrixOp2 (realRectToCMatrix A)
  let μ := complexMatrixOp2 (realRectToCMatrix
    (nonsingInv r (higham10_14_block11 A)))
  (s : ℝ) * ((r : ℝ) ^ 2 * μ +
    2 * (r : ℝ) ^ 6 * a ^ 2 * μ ^ 3 +
    4 * (r : ℝ) ^ 4 * a * μ ^ 2 +
    2 * (r : ℝ) ^ 4 * μ ^ 2)

end Blocks

/-! ## Exact rank/Schur algebra -/

/-- A rank-`r` Gram representation whose leading `r × r` Gram block is
nonsingular has zero Schur complement.  This is the exact linear-algebra step
used in the proof of Theorem 10.14 before any rounding estimate is applied. -/
theorem higham10_14_gram_schur_zero {r s : ℕ}
    (Z1 : Fin r → Fin r → ℝ) (Z2 : Fin r → Fin s → ℝ)
    (hdet : Matrix.det
      (rectMatMul (finiteTranspose Z1) Z1 : Matrix (Fin r) (Fin r) ℝ) ≠ 0) :
    rectMatMul (finiteTranspose Z2) Z2 =
      rectMatMul
        (rectMatMul (finiteTranspose Z2) Z1)
        (rectMatMul
          (nonsingInv r (rectMatMul (finiteTranspose Z1) Z1))
          (rectMatMul (finiteTranspose Z1) Z2)) := by
  have hdetZof : Matrix.det (Matrix.of Z1) ≠ 0 := by
    have hGramEq :
        Matrix.of (rectMatMul (finiteTranspose Z1) Z1) =
          (Matrix.of Z1).transpose * Matrix.of Z1 := by
      ext i j
      rfl
    have hdetprod : Matrix.det
        ((Matrix.of Z1).transpose * Matrix.of Z1) ≠ 0 := by
      rw [← hGramEq]
      exact hdet
    intro hz
    apply hdetprod
    rw [Matrix.det_mul, Matrix.det_transpose, hz, mul_zero]
  have hdetZ : Matrix.det (Z1 : Matrix (Fin r) (Fin r) ℝ) ≠ 0 := by
    simpa using hdetZof
  let Z1inv := nonsingInv r Z1
  have hInv : IsInverse r Z1 Z1inv :=
    isInverse_nonsingInv_of_det_ne_zero r Z1 hdetZ
  have hGramInv :
      nonsingInv r (rectMatMul (finiteTranspose Z1) Z1) =
        rectMatMul Z1inv (finiteTranspose Z1inv) :=
    nonsingInv_rectMatMul_transpose_self_of_IsInverse hInv
  have hright : rectMatMul Z1 Z1inv = idMatrix r := by
    ext i j
    exact hInv.2 i j
  have hleftT :
      rectMatMul (finiteTranspose Z1inv) (finiteTranspose Z1) = idMatrix r := by
    ext i j
    unfold rectMatMul finiteTranspose idMatrix
    have h := hInv.2 j i
    simpa [eq_comm, mul_comm] using h
  rw [hGramInv]
  have hcancel :
      rectMatMul Z1
          (rectMatMul Z1inv
            (rectMatMul (finiteTranspose Z1inv)
              (rectMatMul (finiteTranspose Z1) Z2))) = Z2 := by
    rw [← rectMatMul_assoc Z1 Z1inv, hright, rectMatMul_id_left,
      ← rectMatMul_assoc (finiteTranspose Z1inv) (finiteTranspose Z1),
      hleftT, rectMatMul_id_left]
  symm
  calc
    rectMatMul
        (rectMatMul (finiteTranspose Z2) Z1)
        (rectMatMul
          (rectMatMul Z1inv (finiteTranspose Z1inv))
          (rectMatMul (finiteTranspose Z1) Z2)) =
      rectMatMul (finiteTranspose Z2)
        (rectMatMul Z1
          (rectMatMul Z1inv
            (rectMatMul (finiteTranspose Z1inv)
              (rectMatMul (finiteTranspose Z1) Z2)))) := by
        simp only [rectMatMul_assoc]
    _ = rectMatMul (finiteTranspose Z2) Z2 := by rw [hcancel]

/-- The PSD/rank hypotheses of Theorem 10.14 generate the exact zero Schur
complement; no Schur identity is accepted as an extra premise.  The proof
uses the constructive rank-truncated pivoted Cholesky factor from Theorem
10.9, undoes its permutation, and then applies
`higham10_14_gram_schur_zero`. -/
theorem higham10_14_psd_rank_schur_zero {r s : ℕ}
    (A : Fin (r + s) → Fin (r + s) → ℝ)
    (hPSD : IsPosSemiDef (r + s) A)
    (hrank : (Matrix.of A).rank = r)
    (hA11 : IsSymPosDef r (higham10_14_block11 A)) :
    higham10_14_block22 A =
      rectMatMul
        (rectMatMul (higham10_14_block21 A)
          (nonsingInv r (higham10_14_block11 A)))
        (higham10_14_block12 A) := by
  obtain ⟨q, σ, R, hq, hspec, hqrank⟩ :=
    higham10_9_psd_pivoted_cholesky_rank (r + s) A hPSD
  have hqr : q = r := by omega
  have hspecR :
      higham10_9_PivotedCholeskySpec (r + s) A R σ r := by
    simpa [hqr] using hspec
  obtain ⟨τ, hleft, hright⟩ :=
    Function.bijective_iff_has_inverse.mp hspecR.perm
  let Z1 : Fin r → Fin r → ℝ := fun k j =>
    R (Fin.castAdd s k) (τ (Fin.castAdd s j))
  let Z2 : Fin r → Fin s → ℝ := fun k j =>
    R (Fin.castAdd s k) (τ (Fin.natAdd r j))
  have hGram : ∀ i j : Fin (r + s),
      A i j = ∑ k : Fin r,
        R (Fin.castAdd s k) (τ i) * R (Fin.castAdd s k) (τ j) := by
    intro i j
    have hp := hspecR.product_eq (τ i) (τ j)
    rw [hright i, hright j, Fin.sum_univ_add] at hp
    have htail :
        (∑ k : Fin s,
          R (Fin.natAdd r k) (τ i) * R (Fin.natAdd r k) (τ j)) = 0 := by
      apply Finset.sum_eq_zero
      intro k _
      rw [hspecR.R_rank_zero (Fin.natAdd r k) (τ i) (by simp), zero_mul]
    rw [htail, add_zero] at hp
    exact hp.symm
  have h11 : higham10_14_block11 A =
      rectMatMul (finiteTranspose Z1) Z1 := by
    ext i j
    simpa [higham10_14_block11, Z1, rectMatMul, finiteTranspose] using
      hGram (Fin.castAdd s i) (Fin.castAdd s j)
  have h12 : higham10_14_block12 A =
      rectMatMul (finiteTranspose Z1) Z2 := by
    ext i j
    simpa [higham10_14_block12, Z1, Z2, rectMatMul, finiteTranspose] using
      hGram (Fin.castAdd s i) (Fin.natAdd r j)
  have h21 : higham10_14_block21 A =
      rectMatMul (finiteTranspose Z2) Z1 := by
    ext i j
    simpa [higham10_14_block21, Z1, Z2, rectMatMul, finiteTranspose] using
      hGram (Fin.natAdd r i) (Fin.castAdd s j)
  have h22 : higham10_14_block22 A =
      rectMatMul (finiteTranspose Z2) Z2 := by
    ext i j
    simpa [higham10_14_block22, Z2, rectMatMul, finiteTranspose] using
      hGram (Fin.natAdd r i) (Fin.natAdd r j)
  have hdet11 : Matrix.det
      (higham10_14_block11 A : Matrix (Fin r) (Fin r) ℝ) ≠ 0 :=
    isSymPosDef_det_ne_zero (higham10_14_block11 A) hA11
  have hdetGram : Matrix.det
      (rectMatMul (finiteTranspose Z1) Z1 : Matrix (Fin r) (Fin r) ℝ) ≠ 0 := by
    rw [← h11]
    exact hdet11
  rw [h11, h12, h21, h22]
  rw [rectMatMul_assoc]
  exact higham10_14_gram_schur_zero Z1 Z2 hdetGram

/-! ## The literal executor is a perturbed Schur complement -/

/-- The square zero-padded Gram product of `fl_choleskyTrunc` is exactly the
Gram product of the `r` rows actually produced by Algorithm 10.2. -/
theorem higham10_14_truncGram_eq_actualRows (fp : FPModel) {r s : ℕ}
    (A : Fin (r + s) → Fin (r + s) → ℝ) (i j : Fin (r + s)) :
    (∑ k : Fin (r + s),
      fl_choleskyTrunc fp (r + s) A r k i *
        fl_choleskyTrunc fp (r + s) A r k j) =
      rectMatMul
        (finiteTranspose (higham10_14_sourceFactorRows fp A))
        (higham10_14_sourceFactorRows fp A) i j := by
  rw [fl_choleskyTrunc_gram]
  change (∑ k ∈ Finset.univ.filter (fun k : Fin (r + s) => k.val < r),
      fl_cholesky fp (r + s) A k i * fl_cholesky fp (r + s) A k j) =
    ∑ k : Fin r,
      fl_cholesky fp (r + s) A (Fin.castAdd s k) i *
        fl_cholesky fp (r + s) A (Fin.castAdd s k) j
  simpa [Fin.castAdd, Fin.castLE] using
    (sum_fin_eq_sum_filter_lt' (Nat.le_add_right r s)
      (fun k : Fin (r + s) => fl_cholesky fp (r + s) A k i *
        fl_cholesky fp (r + s) A k j)).symm

/-- Positive completion of the first `r` literal stages makes their computed
triangular block genuinely invertible. -/
theorem higham10_14_actualR11_isInverse (fp : FPModel) {r s : ℕ}
    (A : Fin (r + s) → Fin (r + s) → ℝ)
    (hr1 : gammaValid fp (r + 1))
    (hsuccess : ∀ q : Fin (r + s), q.val < r →
      0 < fl_cholPivot fp (r + s) A q) :
    IsInverse r (higham10_14_actualR11 fp A)
      (nonsingInv r (higham10_14_actualR11 fp A)) := by
  have hu : fp.u < 1 := by
    have hcast : (1 : ℝ) ≤ (r + 1 : ℕ) := by norm_num
    have hmul := mul_le_mul_of_nonneg_right hcast fp.u_nonneg
    unfold gammaValid at hr1
    simpa only [one_mul] using lt_of_le_of_lt hmul hr1
  have hupper : ∀ i j : Fin r, j.val < i.val →
      higham10_14_actualR11 fp A i j = 0 := by
    intro i j hji
    exact fl_cholesky_strict_lower fp (r + s) A
      (Fin.castAdd s i) (Fin.castAdd s j) (by simpa using hji)
  have hdiag : ∀ i : Fin r, higham10_14_actualR11 fp A i i ≠ 0 := by
    intro i
    have hp := hsuccess (Fin.castAdd s i) (by simp)
    have hsqrt : 0 < fl_cholesky fp (r + s) A
        (Fin.castAdd s i) (Fin.castAdd s i) := by
      rw [fl_cholesky_diag_eq]
      exact fl_sqrt_pos fp hu _ (by simpa [fl_cholPivot] using hp)
    exact hsqrt.ne'
  exact isInverse_nonsingInv_of_det_ne_zero r _
    (det_ne_zero_of_upper_triangular_diag_ne_zero r _ hupper hdiag)

/-- The four block equations obtained by restricting literal display (10.23).
The first three have no trailing contribution; the fourth contains precisely
the actual trailing executor. -/
theorem higham10_14_actual_block_equations (fp : FPModel) {r s : ℕ}
    (A : Fin (r + s) → Fin (r + s) → ℝ) :
    let E := higham10_14_sourceError fp A r (Nat.le_add_right r s)
    let R11 := higham10_14_actualR11 fp A
    let R12 := higham10_14_actualR12 fp A
    let S := higham10_14_actualSchur fp A
    higham10_14_block11 A + higham10_14_block11 E =
        rectMatMul (finiteTranspose R11) R11 ∧
      higham10_14_block12 A + higham10_14_block12 E =
        rectMatMul (finiteTranspose R11) R12 ∧
      higham10_14_block21 A + higham10_14_block21 E =
        rectMatMul (finiteTranspose R12) R11 ∧
      higham10_14_block22 A + higham10_14_block22 E =
        rectMatMul (finiteTranspose R12) R12 + S := by
  dsimp only
  constructor
  · ext i j
    have hi : ¬r ≤ i.val := Nat.not_le_of_lt i.isLt
    have hj : ¬r ≤ j.val := Nat.not_le_of_lt j.isLt
    have h23 := higham10_14_equation_10_23 fp A r
      (Nat.le_add_right r s) (Fin.castAdd s i) (Fin.castAdd s j)
    rw [higham10_14_truncGram_eq_actualRows] at h23
    simpa [higham10_14_block11, higham10_14_actualR11,
      higham10_14_sourceFactorRows, higham10_14_sourceTrailing,
      rectMatMul, finiteTranspose, hi, hj] using h23
  constructor
  · ext i j
    have hi : ¬r ≤ i.val := Nat.not_le_of_lt i.isLt
    have h23 := higham10_14_equation_10_23 fp A r
      (Nat.le_add_right r s) (Fin.castAdd s i) (Fin.natAdd r j)
    rw [higham10_14_truncGram_eq_actualRows] at h23
    simpa [higham10_14_block12, higham10_14_actualR11,
      higham10_14_actualR12, higham10_14_sourceFactorRows,
      higham10_14_sourceTrailing, rectMatMul, finiteTranspose, hi] using h23
  constructor
  · ext i j
    have hj : ¬r ≤ j.val := Nat.not_le_of_lt j.isLt
    have h23 := higham10_14_equation_10_23 fp A r
      (Nat.le_add_right r s) (Fin.natAdd r i) (Fin.castAdd s j)
    rw [higham10_14_truncGram_eq_actualRows] at h23
    simpa [higham10_14_block21, higham10_14_actualR11,
      higham10_14_actualR12, higham10_14_sourceFactorRows,
      higham10_14_sourceTrailing, rectMatMul, finiteTranspose, hj] using h23
  · ext i j
    have h23 := higham10_14_equation_10_23 fp A r
      (Nat.le_add_right r s) (Fin.natAdd r i) (Fin.natAdd r j)
    rw [higham10_14_truncGram_eq_actualRows] at h23
    simpa [higham10_14_block22, higham10_14_actualR12,
      higham10_14_actualSchur, higham10_14_sourceFactorRows,
      rectMatMul, finiteTranspose] using h23

/-- The literal trailing executor is exactly the Schur complement of
`A + E`, where `E` is the actual error defined by (10.23). -/
theorem higham10_14_actualSchur_eq_perturbedSchur (fp : FPModel) {r s : ℕ}
    (A : Fin (r + s) → Fin (r + s) → ℝ)
    (hr1 : gammaValid fp (r + 1))
    (hsuccess : ∀ q : Fin (r + s), q.val < r →
      0 < fl_cholPivot fp (r + s) A q) :
    let E := higham10_14_sourceError fp A r (Nat.le_add_right r s)
    let X := nonsingInv r
      (higham10_14_block11 A + higham10_14_block11 E)
    higham10_14_actualSchur fp A =
      (higham10_14_block22 A + higham10_14_block22 E) -
        rectMatMul
          (rectMatMul
            (higham10_14_block21 A + higham10_14_block21 E) X)
          (higham10_14_block12 A + higham10_14_block12 E) := by
  dsimp only
  let E := higham10_14_sourceError fp A r (Nat.le_add_right r s)
  let R11 := higham10_14_actualR11 fp A
  let R12 := higham10_14_actualR12 fp A
  let S := higham10_14_actualSchur fp A
  obtain ⟨h11, h12, h21, h22⟩ :=
    higham10_14_actual_block_equations fp A
  have hRinv := higham10_14_actualR11_isInverse fp A hr1 hsuccess
  have hdetGram : Matrix.det
      (rectMatMul (finiteTranspose R11) R11 : Matrix (Fin r) (Fin r) ℝ) ≠ 0 := by
    have hmul : (Matrix.of R11) * Matrix.of (nonsingInv r R11) = 1 := by
      ext i j
      simpa [Matrix.mul_apply] using hRinv.2 i j
    have hdetRof : Matrix.det (Matrix.of R11) ≠ 0 := by
      intro hz
      have hd := congrArg Matrix.det hmul
      rw [Matrix.det_mul, hz, zero_mul, Matrix.det_one] at hd
      norm_num at hd
    have hdetR : Matrix.det (R11 : Matrix (Fin r) (Fin r) ℝ) ≠ 0 := by
      simpa using hdetRof
    have heq : Matrix.of (rectMatMul (finiteTranspose R11) R11) =
        (Matrix.of R11).transpose * Matrix.of R11 := by ext i j; rfl
    have hdetGramOf : Matrix.det
        (Matrix.of (rectMatMul (finiteTranspose R11) R11)) ≠ 0 := by
      rw [heq, Matrix.det_mul, Matrix.det_transpose]
      exact mul_ne_zero hdetRof hdetRof
    simpa using hdetGramOf
  have hcancel := higham10_14_gram_schur_zero R11 R12 hdetGram
  change S = _
  rw [h11, h12, h21, h22]
  rw [rectMatMul_assoc]
  rw [← hcancel]
  abel

/-- Literal Lemma 10.10 specialized to the matrices generated in Theorem
10.14.  The unperturbed Schur term is eliminated from the PSD/rank
hypotheses, the perturbed inverse is generated from the actual computed
triangular block, and every term in the final parenthesis contains at least
two factors from the actual error `E`. -/
theorem higham10_14_actual_schur_perturbation_exact (fp : FPModel) {r s : ℕ}
    (A : Fin (r + s) → Fin (r + s) → ℝ)
    (hPSD : IsPosSemiDef (r + s) A)
    (hrank : (Matrix.of A).rank = r)
    (hA11 : IsSymPosDef r (higham10_14_block11 A))
    (hr1 : gammaValid fp (r + 1))
    (hsuccess : ∀ q : Fin (r + s), q.val < r →
      0 < fl_cholPivot fp (r + s) A q) :
    let E := higham10_14_sourceError fp A r (Nat.le_add_right r s)
    let A11 : Matrix (Fin r) (Fin r) ℝ := higham10_14_block11 A
    let A12 : Matrix (Fin r) (Fin s) ℝ := higham10_14_block12 A
    let A21 : Matrix (Fin s) (Fin r) ℝ := higham10_14_block21 A
    let M : Matrix (Fin r) (Fin r) ℝ :=
      nonsingInv r (higham10_14_block11 A)
    let X : Matrix (Fin r) (Fin r) ℝ :=
      nonsingInv r
        (higham10_14_block11 A + higham10_14_block11 E)
    let E11 : Matrix (Fin r) (Fin r) ℝ := higham10_14_block11 E
    let E12 : Matrix (Fin r) (Fin s) ℝ := higham10_14_block12 E
    let E21 : Matrix (Fin s) (Fin r) ℝ := higham10_14_block21 E
    let E22 : Matrix (Fin s) (Fin s) ℝ := higham10_14_block22 E
    (higham10_14_actualSchur fp A : Matrix (Fin s) (Fin s) ℝ) =
      (E22 - E21 * M * A12 - A21 * M * E12
          + A21 * (M * E11 * M) * A12)
      + (-(E21 * M * E12)
          - A21 * (M * E11 * (M * E11 * X)) * A12
          + E21 * (M * E11 * X) * A12
          + A21 * (M * E11 * X) * E12
          + E21 * (M * E11 * X) * E12) := by
  dsimp only
  let E := higham10_14_sourceError fp A r (Nat.le_add_right r s)
  let A11 : Matrix (Fin r) (Fin r) ℝ := higham10_14_block11 A
  let A12 : Matrix (Fin r) (Fin s) ℝ := higham10_14_block12 A
  let A21 : Matrix (Fin s) (Fin r) ℝ := higham10_14_block21 A
  let A22 : Matrix (Fin s) (Fin s) ℝ := higham10_14_block22 A
  let M : Matrix (Fin r) (Fin r) ℝ := nonsingInv r (higham10_14_block11 A)
  let X : Matrix (Fin r) (Fin r) ℝ := nonsingInv r
    (higham10_14_block11 A + higham10_14_block11 E)
  let E11 : Matrix (Fin r) (Fin r) ℝ := higham10_14_block11 E
  let E12 : Matrix (Fin r) (Fin s) ℝ := higham10_14_block12 E
  let E21 : Matrix (Fin s) (Fin r) ℝ := higham10_14_block21 E
  let E22 : Matrix (Fin s) (Fin s) ℝ := higham10_14_block22 E
  have hSchurF := higham10_14_actualSchur_eq_perturbedSchur
    fp A hr1 hsuccess
  have hSchur : (higham10_14_actualSchur fp A : Matrix (Fin s) (Fin s) ℝ) =
      (A22 + E22) - (A21 + E21) * X * (A12 + E12) := by
    ext i j
    simpa [A11, A12, A21, A22, E, E11, E12, E21, E22, X,
      rectMatMul, Matrix.mul_apply] using congrFun (congrFun hSchurF i) j
  have hZeroF := higham10_14_psd_rank_schur_zero A hPSD hrank hA11
  have hZero : A22 - A21 * M * A12 = 0 := by
    ext i j
    have h := congrFun (congrFun hZeroF i) j
    simp only [A22, A21, A12, M]
    simpa [rectMatMul, Matrix.mul_apply] using sub_eq_zero.mpr h
  have hdetA11 : Matrix.det A11 ≠ 0 := by
    simpa [A11] using isSymPosDef_det_ne_zero
      (higham10_14_block11 A) hA11
  have hMpred : IsInverse r (higham10_14_block11 A)
      (nonsingInv r (higham10_14_block11 A)) :=
    isInverse_nonsingInv_of_det_ne_zero r _ (by simpa [A11] using hdetA11)
  have hM : M * A11 = 1 := by
    ext i j
    simpa [M, A11, Matrix.mul_apply] using hMpred.1 i j
  obtain ⟨h11F, _h12F, _h21F, _h22F⟩ :=
    higham10_14_actual_block_equations fp A
  let R11 := higham10_14_actualR11 fp A
  have hRinv := higham10_14_actualR11_isInverse fp A hr1 hsuccess
  have hdetRof : Matrix.det (Matrix.of R11) ≠ 0 := by
    have hmul : Matrix.of R11 * Matrix.of (nonsingInv r R11) = 1 := by
      ext i j
      simpa [Matrix.mul_apply, R11] using hRinv.2 i j
    intro hz
    have hd := congrArg Matrix.det hmul
    rw [Matrix.det_mul, hz, zero_mul, Matrix.det_one] at hd
    norm_num at hd
  have hdetGram : Matrix.det
      (Matrix.of (rectMatMul (finiteTranspose R11) R11)) ≠ 0 := by
    have heq : Matrix.of (rectMatMul (finiteTranspose R11) R11) =
        (Matrix.of R11).transpose * Matrix.of R11 := by ext i j; rfl
    rw [heq, Matrix.det_mul, Matrix.det_transpose]
    exact mul_ne_zero hdetRof hdetRof
  have hdetPert : Matrix.det
      ((higham10_14_block11 A + higham10_14_block11 E :
        Fin r → Fin r → ℝ) : Matrix (Fin r) (Fin r) ℝ) ≠ 0 := by
    have hmat : Matrix.of
        (higham10_14_block11 A + higham10_14_block11 E) =
          Matrix.of (rectMatMul (finiteTranspose R11) R11) := by
      simpa [R11, E] using congrArg Matrix.of h11F
    have hdetPertOf : Matrix.det
        (Matrix.of (higham10_14_block11 A + higham10_14_block11 E)) ≠ 0 := by
      rw [hmat]
      exact hdetGram
    simpa using hdetPertOf
  have hXpred : IsInverse r
      (higham10_14_block11 A + higham10_14_block11 E)
      (nonsingInv r
        (higham10_14_block11 A + higham10_14_block11 E)) :=
    isInverse_nonsingInv_of_det_ne_zero r _ hdetPert
  have hX : (A11 + E11) * X = 1 := by
    ext i j
    simpa [A11, E11, X, Matrix.mul_apply] using hXpred.2 i j
  have hres : X = M - M * E11 * X :=
    schur_resolvent_from_inverses M X A11 E11 hM hX
  have hexact := schur_perturbation_exact A21 E21 A12 E12 A22 E22
    M X E11 hres
  calc
    (higham10_14_actualSchur fp A : Matrix (Fin s) (Fin s) ℝ) =
        (A22 + E22) - (A21 + E21) * X * (A12 + E12) := hSchur
    _ = (A22 - A21 * M * A12)
        + (E22 - E21 * M * A12 - A21 * M * E12
            + A21 * (M * E11 * M) * A12)
        + (-(E21 * M * E12)
            - A21 * (M * E11 * (M * E11 * X)) * A12
            + E21 * (M * E11 * X) * A12
            + A21 * (M * E11 * X) * E12
            + E21 * (M * E11 * X) * E12) := hexact
    _ = (E22 - E21 * M * A12 - A21 * M * E12
          + A21 * (M * E11 * M) * A12)
        + (-(E21 * M * E12)
            - A21 * (M * E11 * (M * E11 * X)) * A12
            + E21 * (M * E11 * X) * A12
            + A21 * (M * E11 * X) * E12
            + E21 * (M * E11 * X) * E12) := by rw [hZero, zero_add]

/-- The inverse of the actual perturbed leading block satisfies the resolvent
identity with the exact inverse of `A₁₁`.  Both inverse certificates are
derived here: the first from positive definiteness and the second from the
literal positive pivots of the computed triangular block. -/
theorem higham10_14_actual_inverse_resolvent (fp : FPModel) {r s : ℕ}
    (A : Fin (r + s) → Fin (r + s) → ℝ)
    (hA11 : IsSymPosDef r (higham10_14_block11 A))
    (hr1 : gammaValid fp (r + 1))
    (hsuccess : ∀ q : Fin (r + s), q.val < r →
      0 < fl_cholPivot fp (r + s) A q) :
    let E := higham10_14_sourceError fp A r (Nat.le_add_right r s)
    let A11 : Matrix (Fin r) (Fin r) ℝ := higham10_14_block11 A
    let M : Matrix (Fin r) (Fin r) ℝ := nonsingInv r A11
    let E11 : Matrix (Fin r) (Fin r) ℝ := higham10_14_block11 E
    let X : Matrix (Fin r) (Fin r) ℝ := nonsingInv r (A11 + E11)
    X = M - M * E11 * X := by
  dsimp only
  let E := higham10_14_sourceError fp A r (Nat.le_add_right r s)
  let A11 : Matrix (Fin r) (Fin r) ℝ := higham10_14_block11 A
  let M : Matrix (Fin r) (Fin r) ℝ := nonsingInv r A11
  let E11 : Matrix (Fin r) (Fin r) ℝ := higham10_14_block11 E
  let X : Matrix (Fin r) (Fin r) ℝ := nonsingInv r (A11 + E11)
  have hdetA11 : Matrix.det A11 ≠ 0 := by
    simpa [A11] using isSymPosDef_det_ne_zero
      (higham10_14_block11 A) hA11
  have hMpred : IsInverse r (higham10_14_block11 A)
      (nonsingInv r (higham10_14_block11 A)) :=
    isInverse_nonsingInv_of_det_ne_zero r _ (by simpa [A11] using hdetA11)
  have hM : M * A11 = 1 := by
    ext i j
    simpa [M, A11, Matrix.mul_apply] using hMpred.1 i j
  obtain ⟨h11F, _h12F, _h21F, _h22F⟩ :=
    higham10_14_actual_block_equations fp A
  let R11 := higham10_14_actualR11 fp A
  have hRinv := higham10_14_actualR11_isInverse fp A hr1 hsuccess
  have hdetRof : Matrix.det (Matrix.of R11) ≠ 0 := by
    have hmul : Matrix.of R11 * Matrix.of (nonsingInv r R11) = 1 := by
      ext i j
      simpa [Matrix.mul_apply, R11] using hRinv.2 i j
    intro hz
    have hd := congrArg Matrix.det hmul
    rw [Matrix.det_mul, hz, zero_mul, Matrix.det_one] at hd
    norm_num at hd
  have hdetGram : Matrix.det
      (Matrix.of (rectMatMul (finiteTranspose R11) R11)) ≠ 0 := by
    have heq : Matrix.of (rectMatMul (finiteTranspose R11) R11) =
        (Matrix.of R11).transpose * Matrix.of R11 := by ext i j; rfl
    rw [heq, Matrix.det_mul, Matrix.det_transpose]
    exact mul_ne_zero hdetRof hdetRof
  have hdetPert : Matrix.det
      ((higham10_14_block11 A + higham10_14_block11 E :
        Fin r → Fin r → ℝ) : Matrix (Fin r) (Fin r) ℝ) ≠ 0 := by
    have hmat : Matrix.of
        (higham10_14_block11 A + higham10_14_block11 E) =
          Matrix.of (rectMatMul (finiteTranspose R11) R11) := by
      simpa [R11, E] using congrArg Matrix.of h11F
    have hdetPertOf : Matrix.det
        (Matrix.of (higham10_14_block11 A + higham10_14_block11 E)) ≠ 0 := by
      rw [hmat]
      exact hdetGram
    simpa using hdetPertOf
  have hXpred : IsInverse r
      (higham10_14_block11 A + higham10_14_block11 E)
      (nonsingInv r
        (higham10_14_block11 A + higham10_14_block11 E)) :=
    isInverse_nonsingInv_of_det_ne_zero r _ hdetPert
  have hX : (A11 + E11) * X = 1 := by
    ext i j
    simpa [A11, E11, X, Matrix.mul_apply] using hXpred.2 i j
  exact schur_resolvent_from_inverses M X A11 E11 hM hX

/-! ## Uniform scalar absorption behind (10.22) -/

/-- The scalar last step of Higham's proof, stated for a whole roundoff
family.  `e`, `q`, and `d` stand respectively for `‖E‖₂`, the trailing
Schur norm, and `‖A-R̂ᵀR̂‖₂`; `rho` is the already-proved quadratic remainder
from Lemma 10.10.  The two half-radius hypotheses are an explicit uniform
asymptotic neighbourhood, not a bound on the desired conclusion.

The resulting remainder coefficient is independent of the family index, so
the conclusion is the non-vacuous `FamilyFirstOrderLe` predicate. -/
theorem higham10_14_scalar_absorption_family {ι : Type*} {l : Filter ι}
    (r n : ℕ) (u g e q d rho : ι → ℝ) (a K CG CR : ℝ)
    (ha : 0 ≤ a) (hK : 1 ≤ K) (hCG : 0 ≤ CG) (hCR : 0 ≤ CR)
    (hu0 : ∀ t, 0 ≤ u t) (hu1 : ∀ t, u t ≤ 1)
    (hg0 : ∀ t, 0 ≤ g t) (he0 : ∀ t, 0 ≤ e t)
    (hq0 : ∀ t, 0 ≤ q t) (hd0 : ∀ t, 0 ≤ d t)
    (hrho0 : ∀ t, 0 ≤ rho t)
    (hg : ∀ t, g t ≤ CG * u t)
    (hradius : ∀ t, (r : ℝ) * g t ≤ 1 / 2)
    (habsorb : ∀ t,
      (g t / (1 - (r : ℝ) * g t)) * (n : ℝ) * K ≤ 1 / 2)
    (he : ∀ t, e t ≤
      g t / (1 - (r : ℝ) * g t) *
        ((r : ℝ) * a + (n : ℝ) * q t))
    (hq : ∀ t, q t ≤ K * e t + rho t)
    (hd : ∀ t, d t ≤ e t + q t)
    (hrho : ∀ t, rho t ≤ CR * u t ^ 2) :
    FamilyFirstOrderLe l u
      (fun t => 2 * (r : ℝ) * g t * a * K) d := by
  let C : ℝ :=
    8 * K * (r : ℝ) * a * ((r : ℝ) + (n : ℝ) * K) * CG ^ 2 +
      8 * K * (n : ℝ) * CG * CR + CR
  have hC : 0 ≤ C := by
    dsimp [C]
    positivity
  apply FamilyFirstOrderLe.of_uniform_quadratic hC
  intro t
  let α : ℝ := g t / (1 - (r : ℝ) * g t)
  let z : ℝ := α * (n : ℝ) * K
  let β : ℝ := 1 / (1 - z)
  have hr0 : (0 : ℝ) ≤ r := Nat.cast_nonneg r
  have hn0 : (0 : ℝ) ≤ n := Nat.cast_nonneg n
  have hKt0 : 0 ≤ K := le_trans zero_le_one hK
  have hgt0 : 0 ≤ g t := hg0 t
  have hut0 : 0 ≤ u t := hu0 t
  have hdenα : 0 < 1 - (r : ℝ) * g t := by
    linarith [hradius t]
  have hα0 : 0 ≤ α := by
    exact div_nonneg hgt0 hdenα.le
  have hα_le : α ≤ 2 * g t := by
    dsimp [α]
    rw [div_le_iff₀ hdenα]
    nlinarith [hradius t]
  have hα_ge : g t ≤ α := by
    dsimp [α]
    rw [le_div_iff₀ hdenα]
    nlinarith [mul_nonneg hr0 hgt0]
  have hαdiff : α - g t ≤ 2 * (r : ℝ) * g t ^ 2 := by
    have heq : α - g t =
        (r : ℝ) * g t ^ 2 / (1 - (r : ℝ) * g t) := by
      dsimp [α]
      apply (eq_div_iff (ne_of_gt hdenα)).2
      rw [sub_mul, div_mul_cancel₀ _ (ne_of_gt hdenα)]
      ring
    rw [heq]
    apply (div_le_iff₀ hdenα).2
    have hfac : 1 ≤ 2 * (1 - (r : ℝ) * g t) := by
      linarith [hradius t]
    have hmul := mul_le_mul_of_nonneg_right hfac
      (mul_nonneg hr0 (sq_nonneg (g t)))
    convert hmul using 1 <;> ring
  have hz0 : 0 ≤ z := by
    exact mul_nonneg (mul_nonneg hα0 hn0) hKt0
  have hzhalf : z ≤ 1 / 2 := by
    simpa [z, α] using habsorb t
  have hdenβ : 0 < 1 - z := by linarith
  have hβ0 : 0 ≤ β := by exact div_nonneg zero_le_one hdenβ.le
  have hβ_le : β ≤ 2 := by
    dsimp [β]
    rw [div_le_iff₀ hdenβ]
    nlinarith
  have hβ_ge : 1 ≤ β := by
    dsimp [β]
    rw [le_div_iff₀ hdenβ]
    nlinarith
  have hβdiff : β - 1 ≤ 2 * z := by
    have heq : β - 1 = z / (1 - z) := by
      dsimp [β]
      apply (eq_div_iff (ne_of_gt hdenβ)).2
      rw [sub_mul, div_mul_cancel₀ _ (ne_of_gt hdenβ)]
      ring
    rw [heq]
    apply (div_le_iff₀ hdenβ).2
    have hfac : 1 ≤ 2 * (1 - z) := by linarith
    have hmul := mul_le_mul_of_nonneg_right hfac hz0
    convert hmul using 1 <;> ring
  have hαβdiff : α * β - g t ≤
      4 * ((r : ℝ) + (n : ℝ) * K) * g t ^ 2 := by
    have hzle : z ≤ 2 * g t * (n : ℝ) * K := by
      dsimp [z]
      exact mul_le_mul_of_nonneg_right
        (mul_le_mul_of_nonneg_right hα_le hn0) hKt0
    have hsplit : α * β - g t =
        (α - g t) * β + g t * (β - 1) := by ring
    rw [hsplit]
    have hfirst : (α - g t) * β ≤
        (2 * (r : ℝ) * g t ^ 2) * 2 :=
      mul_le_mul hαdiff hβ_le hβ0 (by nlinarith [hα_ge])
    have hsecond : g t * (β - 1) ≤ g t * (2 * z) :=
      mul_le_mul_of_nonneg_left hβdiff hgt0
    have hsecond' : g t * (2 * z) ≤
        4 * (n : ℝ) * K * g t ^ 2 := by
      nlinarith [hzle, hgt0, hn0, hKt0]
    nlinarith [hfirst, hsecond, hsecond']
  have hαβ_le : α * β ≤ 4 * g t := by
    calc
      α * β ≤ (2 * g t) * 2 :=
        mul_le_mul hα_le hβ_le hβ0 (by positivity)
      _ = 4 * g t := by ring
  have hepre : (1 - z) * e t ≤
      α * ((r : ℝ) * a + (n : ℝ) * rho t) := by
    have he' : e t ≤ α * ((r : ℝ) * a + (n : ℝ) * q t) := by
      simpa [α] using he t
    have hq' := hq t
    have hmono : α * ((r : ℝ) * a + (n : ℝ) * q t) ≤
        α * ((r : ℝ) * a + (n : ℝ) * (K * e t + rho t)) := by
      apply mul_le_mul_of_nonneg_left _ hα0
      exact add_le_add le_rfl (mul_le_mul_of_nonneg_left hq' hn0)
    calc
      (1 - z) * e t = e t - α * (n : ℝ) * K * e t := by
        dsimp [z]
        ring
      _ ≤ α * ((r : ℝ) * a + (n : ℝ) * q t) -
          α * (n : ℝ) * K * e t := sub_le_sub_right he' _
      _ ≤ α * ((r : ℝ) * a + (n : ℝ) * (K * e t + rho t)) -
          α * (n : ℝ) * K * e t := sub_le_sub_right hmono _
      _ = α * ((r : ℝ) * a + (n : ℝ) * rho t) := by ring
  have heβ : e t ≤ α * β *
      ((r : ℝ) * a + (n : ℝ) * rho t) := by
    have hdiv : e t ≤
        α * ((r : ℝ) * a + (n : ℝ) * rho t) / (1 - z) := by
      apply (le_div_iff₀ hdenβ).2
      nlinarith [hepre]
    dsimp [β]
    calc
      e t ≤ α * ((r : ℝ) * a + (n : ℝ) * rho t) / (1 - z) := hdiv
      _ = α * (1 / (1 - z)) *
          ((r : ℝ) * a + (n : ℝ) * rho t) := by ring
  have hdmain : d t ≤ (K + 1) * e t + rho t := by
    nlinarith [hd t, hq t]
  have hKtwo : K + 1 ≤ 2 * K := by linarith
  have hlead : d t ≤
      2 * K * (α * β) *
          ((r : ℝ) * a + (n : ℝ) * rho t) + rho t := by
    let B : ℝ := α * β *
      ((r : ℝ) * a + (n : ℝ) * rho t)
    have hB0 : 0 ≤ B := by
      dsimp [B]
      exact mul_nonneg (mul_nonneg hα0 hβ0)
        (add_nonneg (mul_nonneg hr0 ha)
          (mul_nonneg hn0 (hrho0 t)))
    calc
      d t ≤ (K + 1) * e t + rho t := hdmain
      _ ≤ (K + 1) * B + rho t := by
        exact add_le_add
          (mul_le_mul_of_nonneg_left heβ (by linarith)) le_rfl
      _ ≤ (2 * K) * B + rho t := by
        exact add_le_add (mul_le_mul_of_nonneg_right hKtwo hB0) le_rfl
      _ = 2 * K * (α * β) *
          ((r : ℝ) * a + (n : ℝ) * rho t) + rho t := by
        dsimp [B]
        ring
  have hg_sq : g t ^ 2 ≤ CG ^ 2 * u t ^ 2 := by
    have hs := mul_self_le_mul_self hgt0 (hg t)
    rw [pow_two, pow_two]
    convert hs using 1 <;> ring
  have hgrho : g t * rho t ≤ CG * CR * u t ^ 2 := by
    have h1 : g t * rho t ≤ (CG * u t) * (CR * u t ^ 2) :=
      mul_le_mul (hg t) (hrho t) (hrho0 t)
        (mul_nonneg hCG hut0)
    have hu3 : u t ^ 3 ≤ u t ^ 2 := by
      have hs := mul_le_mul_of_nonneg_left (hu1 t) (sq_nonneg (u t))
      convert hs using 1 <;> ring
    calc
      g t * rho t ≤ (CG * u t) * (CR * u t ^ 2) := h1
      _ = CG * CR * u t ^ 3 := by ring
      _ ≤ CG * CR * u t ^ 2 :=
        mul_le_mul_of_nonneg_left hu3 (mul_nonneg hCG hCR)
  dsimp [C]
  have hdiffmain :
      2 * K * (α * β) * ((r : ℝ) * a + (n : ℝ) * rho t) + rho t -
          2 * (r : ℝ) * g t * a * K ≤
        (8 * K * (r : ℝ) * a * ((r : ℝ) + (n : ℝ) * K) * CG ^ 2 +
            8 * K * (n : ℝ) * CG * CR + CR) * u t ^ 2 := by
    have hfirst :
        2 * K * (r : ℝ) * a * (α * β - g t) ≤
          8 * K * (r : ℝ) * a * ((r : ℝ) + (n : ℝ) * K) * g t ^ 2 := by
      have hc : 0 ≤ 2 * K * (r : ℝ) * a := by positivity
      have h := mul_le_mul_of_nonneg_left hαβdiff
        hc
      convert h using 1 <;> ring
    have hsecond :
        2 * K * (α * β) * (n : ℝ) * rho t ≤
          8 * K * (n : ℝ) * (g t * rho t) := by
      have hc : 0 ≤ 2 * K * (n : ℝ) * rho t :=
        mul_nonneg (mul_nonneg (mul_nonneg (by norm_num) hKt0) hn0)
          (hrho0 t)
      have := mul_le_mul_of_nonneg_right hαβ_le
        hc
      convert this using 1 <;> ring
    have hfirst' :
        8 * K * (r : ℝ) * a * ((r : ℝ) + (n : ℝ) * K) * g t ^ 2 ≤
          8 * K * (r : ℝ) * a * ((r : ℝ) + (n : ℝ) * K) *
            (CG ^ 2 * u t ^ 2) :=
      mul_le_mul_of_nonneg_left hg_sq (by positivity)
    have hsecond' : 8 * K * (n : ℝ) * (g t * rho t) ≤
        8 * K * (n : ℝ) * (CG * CR * u t ^ 2) :=
      mul_le_mul_of_nonneg_left hgrho (by positivity)
    have hdecomp :
        2 * K * (α * β) * ((r : ℝ) * a + (n : ℝ) * rho t) + rho t -
            2 * (r : ℝ) * g t * a * K =
          2 * K * (r : ℝ) * a * (α * β - g t) +
            2 * K * (α * β) * (n : ℝ) * rho t + rho t := by ring
    rw [hdecomp]
    calc
      2 * K * (r : ℝ) * a * (α * β - g t) +
            2 * K * (α * β) * (n : ℝ) * rho t + rho t
          ≤ 8 * K * (r : ℝ) * a * ((r : ℝ) + (n : ℝ) * K) * g t ^ 2 +
              8 * K * (n : ℝ) * (g t * rho t) + rho t :=
            add_le_add (add_le_add hfirst hsecond) le_rfl
      _ ≤ 8 * K * (r : ℝ) * a * ((r : ℝ) + (n : ℝ) * K) *
              (CG ^ 2 * u t ^ 2) +
            8 * K * (n : ℝ) * (CG * CR * u t ^ 2) +
              CR * u t ^ 2 :=
            add_le_add (add_le_add hfirst' hsecond') (hrho t)
      _ = (8 * K * (r : ℝ) * a * ((r : ℝ) + (n : ℝ) * K) * CG ^ 2 +
            8 * K * (n : ℝ) * CG * CR + CR) * u t ^ 2 := by ring
  calc
    d t ≤ 2 * K * (α * β) *
        ((r : ℝ) * a + (n : ℝ) * rho t) + rho t := hlead
    _ = 2 * (r : ℝ) * g t * a * K +
        (2 * K * (α * β) *
          ((r : ℝ) * a + (n : ℝ) * rho t) + rho t -
            2 * (r : ℝ) * g t * a * K) := by ring
    _ ≤ 2 * (r : ℝ) * g t * a * K +
        (8 * K * (r : ℝ) * a * ((r : ℝ) + (n : ℝ) * K) * CG ^ 2 +
          8 * K * (n : ℝ) * CG * CR + CR) * u t ^ 2 :=
      add_le_add le_rfl hdiffmain

/-- Scalar absorption when Lemma 10.10 supplies the remainder directly as a
fixed multiple of the *actual* error squared.  The two quarter-radius
conditions first derive `e = O(u)` from (10.25), so the quadratic remainder
is then genuinely uniform `O(u²)`; no `e ≤ C u` premise is assumed. -/
theorem higham10_14_scalar_absorption_family_of_error_sq
    {ι : Type*} {l : Filter ι}
    (r n : ℕ) (u g e q d : ι → ℝ) (a K D CG : ℝ)
    (ha : 0 ≤ a) (hK : 1 ≤ K) (hD : 0 ≤ D) (hCG : 0 ≤ CG)
    (hu0 : ∀ t, 0 ≤ u t) (hu1 : ∀ t, u t ≤ 1)
    (hg0 : ∀ t, 0 ≤ g t) (he0 : ∀ t, 0 ≤ e t)
    (hq0 : ∀ t, 0 ≤ q t) (hd0 : ∀ t, 0 ≤ d t)
    (hg : ∀ t, g t ≤ CG * u t)
    (hradius : ∀ t, (r : ℝ) * g t ≤ 1 / 2)
    (hlinearAbsorb : ∀ t,
      (g t / (1 - (r : ℝ) * g t)) * (n : ℝ) * K ≤ 1 / 4)
    (hquadraticAbsorb : ∀ t,
      (g t / (1 - (r : ℝ) * g t)) * (n : ℝ) * D * e t ≤ 1 / 4)
    (he : ∀ t, e t ≤
      g t / (1 - (r : ℝ) * g t) *
        ((r : ℝ) * a + (n : ℝ) * q t))
    (hq : ∀ t, q t ≤ K * e t + D * e t ^ 2)
    (hd : ∀ t, d t ≤ e t + q t) :
    FamilyFirstOrderLe l u
      (fun t => 2 * (r : ℝ) * g t * a * K) d := by
  let rho : ι → ℝ := fun t => D * e t ^ 2
  let CR : ℝ := 16 * D * (r : ℝ) ^ 2 * a ^ 2 * CG ^ 2
  have hCR : 0 ≤ CR := by dsimp [CR]; positivity
  have hrho0 : ∀ t, 0 ≤ rho t := fun t =>
    mul_nonneg hD (sq_nonneg (e t))
  have heLinear : ∀ t, e t ≤ 4 * (r : ℝ) * a * g t := by
    intro t
    let α : ℝ := g t / (1 - (r : ℝ) * g t)
    have hr0 : (0 : ℝ) ≤ r := Nat.cast_nonneg r
    have hn0 : (0 : ℝ) ≤ n := Nat.cast_nonneg n
    have hgt0 : 0 ≤ g t := hg0 t
    have hden : 0 < 1 - (r : ℝ) * g t := by linarith [hradius t]
    have hα0 : 0 ≤ α := div_nonneg hgt0 hden.le
    have hαle : α ≤ 2 * g t := by
      dsimp [α]
      rw [div_le_iff₀ hden]
      nlinarith [hradius t]
    have hKn : 0 ≤ (n : ℝ) * K :=
      mul_nonneg hn0 (le_trans zero_le_one hK)
    have hDn : 0 ≤ (n : ℝ) * D := mul_nonneg hn0 hD
    have hqmul : α * (n : ℝ) * q t ≤
        α * (n : ℝ) * (K * e t + D * e t ^ 2) :=
      mul_le_mul_of_nonneg_left (hq t) (mul_nonneg hα0 hn0)
    have heExpanded : e t ≤
        α * (r : ℝ) * a +
          (α * (n : ℝ) * K) * e t +
          (α * (n : ℝ) * D * e t) * e t := by
      calc
        e t ≤ α * ((r : ℝ) * a + (n : ℝ) * q t) := by
          simpa [α] using he t
        _ = α * (r : ℝ) * a + α * (n : ℝ) * q t := by ring
        _ ≤ α * (r : ℝ) * a +
            α * (n : ℝ) * (K * e t + D * e t ^ 2) :=
          add_le_add le_rfl hqmul
        _ = α * (r : ℝ) * a +
            (α * (n : ℝ) * K) * e t +
            (α * (n : ℝ) * D * e t) * e t := by ring
    have hlin : α * (n : ℝ) * K ≤ 1 / 4 := by
      simpa [α] using hlinearAbsorb t
    have hquad : α * (n : ℝ) * D * e t ≤ 1 / 4 := by
      simpa [α] using hquadraticAbsorb t
    have hlinE : (α * (n : ℝ) * K) * e t ≤ (1 / 4) * e t :=
      mul_le_mul_of_nonneg_right hlin (he0 t)
    have hquadE : (α * (n : ℝ) * D * e t) * e t ≤ (1 / 4) * e t :=
      mul_le_mul_of_nonneg_right hquad (he0 t)
    have heα : e t ≤ 2 * α * (r : ℝ) * a := by
      nlinarith [heExpanded, hlinE, hquadE]
    have hscale : 0 ≤ 2 * (r : ℝ) * a :=
      mul_nonneg (mul_nonneg (by norm_num) hr0) ha
    calc
      e t ≤ 2 * α * (r : ℝ) * a := heα
      _ ≤ 2 * (2 * g t) * (r : ℝ) * a := by
        have hs := mul_le_mul_of_nonneg_left hαle hscale
        convert hs using 1 <;> ring
      _ = 4 * (r : ℝ) * a * g t := by ring
  have hrho : ∀ t, rho t ≤ CR * u t ^ 2 := by
    intro t
    have hB0 : 0 ≤ 4 * (r : ℝ) * a * g t :=
      mul_nonneg (mul_nonneg (mul_nonneg (by norm_num) (Nat.cast_nonneg r)) ha)
        (hg0 t)
    have heSq : e t ^ 2 ≤ (4 * (r : ℝ) * a * g t) ^ 2 := by
      nlinarith [he0 t, heLinear t]
    have hgSq : g t ^ 2 ≤ CG ^ 2 * u t ^ 2 := by
      have hs := mul_self_le_mul_self (hg0 t) (hg t)
      rw [pow_two, pow_two]
      convert hs using 1 <;> ring
    calc
      rho t = D * e t ^ 2 := rfl
      _ ≤ D * (4 * (r : ℝ) * a * g t) ^ 2 :=
        mul_le_mul_of_nonneg_left heSq hD
      _ = 16 * D * (r : ℝ) ^ 2 * a ^ 2 * g t ^ 2 := by ring
      _ ≤ 16 * D * (r : ℝ) ^ 2 * a ^ 2 * (CG ^ 2 * u t ^ 2) :=
        mul_le_mul_of_nonneg_left hgSq (by positivity)
      _ = CR * u t ^ 2 := by ring
  apply higham10_14_scalar_absorption_family r n u g e q d rho a K CG CR
    ha hK hCG hCR hu0 hu1 hg0 he0 hq0 hd0 hrho0 hg hradius
  · intro t
    exact le_trans (hlinearAbsorb t) (by norm_num)
  · exact he
  · intro t
    simpa [rho] using hq t
  · exact hd
  · exact hrho

/-! ## Operator-norm bridges for the actual matrices -/

private theorem higham10_14_rectOpNorm2Le_add {m n : ℕ}
    (A B : Fin m → Fin n → ℝ) {a b : ℝ}
    (hA : rectOpNorm2Le A a) (hB : rectOpNorm2Le B b) :
    rectOpNorm2Le (fun i j => A i j + B i j) (a + b) := by
  intro x
  have haction : rectMatMulVec (fun i j => A i j + B i j) x =
      fun i => rectMatMulVec A x i + rectMatMulVec B x i := by
    ext i
    unfold rectMatMulVec
    rw [← Finset.sum_add_distrib]
    apply Finset.sum_congr rfl
    intro j _
    ring
  rw [haction]
  calc
    vecNorm2 (fun i => rectMatMulVec A x i + rectMatMulVec B x i)
        ≤ vecNorm2 (rectMatMulVec A x) + vecNorm2 (rectMatMulVec B x) :=
          vecNorm2_add_le _ _
    _ ≤ a * vecNorm2 x + b * vecNorm2 x := add_le_add (hA x) (hB x)
    _ = (a + b) * vecNorm2 x := by ring

private theorem higham10_14_rectOpNorm2Le_neg {m n : ℕ}
    (A : Fin m → Fin n → ℝ) {a : ℝ} (hA : rectOpNorm2Le A a) :
    rectOpNorm2Le (fun i j => -A i j) a := by
  intro x
  have haction : rectMatMulVec (fun i j => -A i j) x =
      fun i => -rectMatMulVec A x i := by
    ext i
    unfold rectMatMulVec
    rw [← Finset.sum_neg_distrib]
    apply Finset.sum_congr rfl
    intro j _
    ring
  rw [haction, vecNorm2_neg]
  exact hA x

private theorem higham10_14_abs_entry_le_of_rectOpNorm2Le {m n : ℕ}
    (A : Fin m → Fin n → ℝ) {a : ℝ} (hA : rectOpNorm2Le A a)
    (i : Fin m) (j : Fin n) : |A i j| ≤ a := by
  let x : Fin n → ℝ := finiteBasisVec j
  have hcol : rectMatMulVec A x = fun k => A k j := by
    ext k
    unfold rectMatMulVec x finiteBasisVec
    simp [Finset.sum_ite_eq', Finset.mem_univ]
  have hcoord := abs_coord_le_vecNorm2 (rectMatMulVec A x) i
  have hnorm := hA x
  have hx : vecNorm2 x = 1 := by
    simpa [x] using vecNorm2_finiteBasisVec j
  rw [hcol] at hcoord
  rw [hcol, hx, mul_one] at hnorm
  exact le_trans hcoord hnorm

/-- For symmetric `A`, the other off-diagonal product is exactly `Wᵀ`.
This is the algebraic identity used to obtain `(‖W‖₂ + 1)²`. -/
theorem higham10_14_A21M_eq_Wtranspose {r s : ℕ}
    (A : Fin (r + s) → Fin (r + s) → ℝ)
    (hsymm : ∀ i j, A i j = A j i) :
    rectMatMul (higham10_14_block21 A)
        (nonsingInv r (higham10_14_block11 A)) =
      finiteTranspose (higham10_14_W A) := by
  have hM : IsSymmetricFiniteMatrix
      (nonsingInv r (higham10_14_block11 A)) :=
    nonsingInv_symmetric_of_symmetric _ (by
      intro i j
      exact hsymm (Fin.castAdd s i) (Fin.castAdd s j))
  ext i j
  unfold rectMatMul finiteTranspose higham10_14_W higham10_14_block21
  apply Finset.sum_congr rfl
  intro k _
  rw [hsymm (Fin.natAdd r i) (Fin.castAdd s k), hM k j]
  unfold higham10_14_block12
  ring

/-- Every block of a simultaneously partitioned square matrix inherits its
full operator-2 certificate with constant one. -/
theorem higham10_14_blocks_opNorm2Le {r s : ℕ}
    (E : Fin (r + s) → Fin (r + s) → ℝ) {e : ℝ}
    (hE : opNorm2Le E e) :
    opNorm2Le (higham10_14_block11 E) e ∧
      rectOpNorm2Le (higham10_14_block12 E) e ∧
      rectOpNorm2Le (higham10_14_block21 E) e ∧
      opNorm2Le (higham10_14_block22 E) e := by
  let esum : Fin r ⊕ Fin s ≃ Fin (r + s) := finSumFinEquiv
  let Esum : Fin r ⊕ Fin s → Fin r ⊕ Fin s → ℝ :=
    fun i j => E (esum i) (esum j)
  have hsum : finiteOpNorm2Le Esum e := by
    exact finiteOpNorm2Le_reindex_equiv esum E
      (finiteOpNorm2Le_of_opNorm2Le E hE)
  have h11sum := finiteOpNorm2Le_sumInl_principal Esum hsum
  have h22sum := finiteOpNorm2Le_sumInr_principal Esum hsum
  have h12sum := rectOpNorm2Le_sumInl_sumInr_of_finiteOpNorm2Le Esum hsum
  have h21sum := rectOpNorm2Le_sumInr_sumInl_of_finiteOpNorm2Le Esum hsum
  refine ⟨?_, ?_, ?_, ?_⟩
  · apply opNorm2Le_of_finiteOpNorm2Le
    simpa [Esum, esum, higham10_14_block11] using h11sum
  · simpa [Esum, esum, higham10_14_block12] using h12sum
  · simpa [Esum, esum, higham10_14_block21] using h21sum
  · apply opNorm2Le_of_finiteOpNorm2Le
    simpa [Esum, esum, higham10_14_block22] using h22sum

/-- The first-order Schur perturbation generated by an arbitrary full error
matrix has operator norm at most `‖E‖₂ (‖W‖₂ + 1)²`. -/
theorem higham10_14_linearSchur_opNorm2Le {r s : ℕ}
    (A E : Fin (r + s) → Fin (r + s) → ℝ) :
    let W := higham10_14_W A
    let e := complexMatrixOp2 (realRectToCMatrix E)
    let w := complexMatrixOp2 (realRectToCMatrix W)
    rectOpNorm2Le
      (fun i j =>
        higham10_14_block22 E i j -
          rectMatMul (higham10_14_block21 E) W i j -
          rectMatMul (finiteTranspose W) (higham10_14_block12 E) i j +
          rectMatMul
            (rectMatMul (finiteTranspose W) (higham10_14_block11 E)) W i j)
      (e * (w + 1) ^ 2) := by
  dsimp only
  let W := higham10_14_W A
  let e := complexMatrixOp2 (realRectToCMatrix E)
  let w := complexMatrixOp2 (realRectToCMatrix W)
  have he0 : 0 ≤ e := complexMatrixOp2_nonneg _
  have hw0 : 0 ≤ w := complexMatrixOp2_nonneg _
  have hEfull : opNorm2Le E e :=
    opNorm2Le_complexMatrixOp2_realRectToCMatrix E
  obtain ⟨hE11, hE12, hE21, hE22⟩ :=
    higham10_14_blocks_opNorm2Le E hEfull
  have hE11r : rectOpNorm2Le (higham10_14_block11 E) e := by
    intro x
    simpa [rectOpNorm2Le, opNorm2Le, rectMatMulVec, matMulVec] using hE11 x
  have hE22r : rectOpNorm2Le (higham10_14_block22 E) e := by
    intro x
    simpa [rectOpNorm2Le, opNorm2Le, rectMatMulVec, matMulVec] using hE22 x
  have hW : rectOpNorm2Le W w :=
    rectOpNorm2Le_of_complexMatrixOp2_realRectToCMatrix_le W le_rfl
  have hWt : rectOpNorm2Le (finiteTranspose W) w :=
    rectOpNorm2Le_finiteTranspose_of_rectOpNorm2Le W hw0 hW
  have h21W : rectOpNorm2Le
      (rectMatMul (higham10_14_block21 E) W) (e * w) :=
    rectOpNorm2Le_rectMatMul _ _ he0 hE21 hW
  have hWt12 : rectOpNorm2Le
      (rectMatMul (finiteTranspose W) (higham10_14_block12 E)) (w * e) :=
    rectOpNorm2Le_rectMatMul _ _ hw0 hWt hE12
  have hWt11 : rectOpNorm2Le
      (rectMatMul (finiteTranspose W) (higham10_14_block11 E)) (w * e) :=
    rectOpNorm2Le_rectMatMul _ _ hw0 hWt hE11r
  have hWt11W : rectOpNorm2Le
      (rectMatMul
        (rectMatMul (finiteTranspose W) (higham10_14_block11 E)) W)
      (w * e * w) :=
    rectOpNorm2Le_rectMatMul _ _ (mul_nonneg hw0 he0) hWt11 hW
  have hneg21 := higham10_14_rectOpNorm2Le_neg
    (rectMatMul (higham10_14_block21 E) W) h21W
  have hneg12 := higham10_14_rectOpNorm2Le_neg
    (rectMatMul (finiteTranspose W) (higham10_14_block12 E)) hWt12
  have h1 := higham10_14_rectOpNorm2Le_add
    (higham10_14_block22 E)
    (fun i j => -rectMatMul (higham10_14_block21 E) W i j)
    hE22r hneg21
  have h2 := higham10_14_rectOpNorm2Le_add
    (fun i j => higham10_14_block22 E i j -
      rectMatMul (higham10_14_block21 E) W i j)
    (fun i j => -rectMatMul (finiteTranspose W)
      (higham10_14_block12 E) i j)
    h1 hneg12
  have h3 := higham10_14_rectOpNorm2Le_add
    (fun i j => higham10_14_block22 E i j -
      rectMatMul (higham10_14_block21 E) W i j -
      rectMatMul (finiteTranspose W) (higham10_14_block12 E) i j)
    (rectMatMul
      (rectMatMul (finiteTranspose W) (higham10_14_block11 E)) W)
    h2 hWt11W
  convert h3 using 1 <;> ring

/-- The rectangular row representation of the trailing matrix is a zero
left-column padding of `higham10_14_actualSchur`; hence it has the same
operator upper bound. -/
theorem higham10_14_trailingRows_opNorm2Le_of_actualSchur {r s : ℕ}
    (fp : FPModel) (A : Fin (r + s) → Fin (r + s) → ℝ) {q : ℝ}
    (hq0 : 0 ≤ q) (hS : opNorm2Le (higham10_14_actualSchur fp A) q) :
    rectOpNorm2Le (higham10_14_sourceTrailingRows fp A) q := by
  intro x
  let y : Fin s → ℝ := fun j => x (Fin.natAdd r j)
  have hy : vecNorm2 y ≤ vecNorm2 x := by
    unfold vecNorm2 vecNorm2Sq y
    apply Real.sqrt_le_sqrt
    rw [Fin.sum_univ_add]
    exact le_add_of_nonneg_left
      (Finset.sum_nonneg fun i _ => sq_nonneg (x (Fin.castAdd s i)))
  have haction : rectMatMulVec (higham10_14_sourceTrailingRows fp A) x =
      matMulVec s (higham10_14_actualSchur fp A) y := by
    ext i
    unfold rectMatMulVec matMulVec
    rw [Fin.sum_univ_add]
    have htop : (∑ j : Fin r,
        higham10_14_sourceTrailingRows fp A i (Fin.castAdd s j) *
          x (Fin.castAdd s j)) = 0 := by
      apply Finset.sum_eq_zero
      intro j _
      simp [higham10_14_sourceTrailingRows, higham10_14_sourceTrailing]
    rw [htop, zero_add]
    apply Finset.sum_congr rfl
    intro j _
    rfl
  rw [haction]
  calc
    vecNorm2 (matMulVec s (higham10_14_actualSchur fp A) y)
        ≤ q * vecNorm2 y := hS y
    _ ≤ q * vecNorm2 x := mul_le_mul_of_nonneg_left hy hq0

/-- The full trailing executor is obtained by padding
`higham10_14_sourceTrailingRows` with `r` zero rows. -/
theorem higham10_14_sourceTrailing_opNorm2Le_of_rows {r s : ℕ}
    (fp : FPModel) (A : Fin (r + s) → Fin (r + s) → ℝ) {q : ℝ}
    (hrows : rectOpNorm2Le (higham10_14_sourceTrailingRows fp A) q) :
    opNorm2Le
      (higham10_14_sourceTrailing fp A r (Nat.le_add_right r s)) q := by
  intro x
  have htopAction : ∀ i : Fin r,
      matMulVec (r + s)
          (higham10_14_sourceTrailing fp A r (Nat.le_add_right r s)) x
          (Fin.castAdd s i) = 0 := by
    intro i
    unfold matMulVec
    have hi : ¬ r ≤ (i : ℕ) := Nat.not_le_of_lt i.isLt
    simp [higham10_14_sourceTrailing, Fin.castAdd, hi]
  have htailAction : ∀ i : Fin s,
      matMulVec (r + s)
          (higham10_14_sourceTrailing fp A r (Nat.le_add_right r s)) x
          (Fin.natAdd r i) =
        rectMatMulVec (higham10_14_sourceTrailingRows fp A) x i := by
    intro i
    unfold matMulVec rectMatMulVec
    apply Finset.sum_congr rfl
    intro j _
    rfl
  have hnorm :
      vecNorm2
          (matMulVec (r + s)
            (higham10_14_sourceTrailing fp A r (Nat.le_add_right r s)) x) =
        vecNorm2
          (rectMatMulVec (higham10_14_sourceTrailingRows fp A) x) := by
    unfold vecNorm2 vecNorm2Sq
    congr 1
    rw [Fin.sum_univ_add]
    simp_rw [htopAction, htailAction]
    simp
  rw [hnorm]
  exact hrows x

/-- A Neumann-radius estimate for the inverse of the actual perturbed leading
block.  The perturbed inverse is the literal one generated by the computed
positive pivots; no inverse or Schur-complement bound is supplied. -/
theorem higham10_14_actual_inverse_complexOp2_le {r s : ℕ}
    (fp : FPModel) (A : Fin (r + s) → Fin (r + s) → ℝ)
    (hA11 : IsSymPosDef r (higham10_14_block11 A))
    (hr1 : gammaValid fp (r + 1))
    (hsuccess : ∀ q : Fin (r + s), q.val < r →
      0 < fl_cholPivot fp (r + s) A q)
    (hsmall :
      complexMatrixOp2 (realRectToCMatrix
          (nonsingInv r (higham10_14_block11 A))) *
        complexMatrixOp2 (realRectToCMatrix
          (higham10_14_block11
            (higham10_14_sourceError fp A r (Nat.le_add_right r s)))) ≤
        1 / 2) :
    complexMatrixOp2 (realRectToCMatrix
        (nonsingInv r
          (higham10_14_block11 A +
            higham10_14_block11
              (higham10_14_sourceError fp A r (Nat.le_add_right r s))))) ≤
      2 * complexMatrixOp2 (realRectToCMatrix
        (nonsingInv r (higham10_14_block11 A))) := by
  let E := higham10_14_sourceError fp A r (Nat.le_add_right r s)
  let M : Fin r → Fin r → ℝ := nonsingInv r (higham10_14_block11 A)
  let E11 : Fin r → Fin r → ℝ := higham10_14_block11 E
  let X : Fin r → Fin r → ℝ :=
    nonsingInv r (higham10_14_block11 A + E11)
  let μ := complexMatrixOp2 (realRectToCMatrix M)
  let e := complexMatrixOp2 (realRectToCMatrix E11)
  let xnorm := complexMatrixOp2 (realRectToCMatrix X)
  have hμ0 : 0 ≤ μ := complexMatrixOp2_nonneg _
  have he0 : 0 ≤ e := complexMatrixOp2_nonneg _
  have hx0 : 0 ≤ xnorm := complexMatrixOp2_nonneg _
  have hE11 : opNorm2Le E11 e :=
    opNorm2Le_complexMatrixOp2_realRectToCMatrix E11
  have hMcert : opNorm2Le M μ :=
    opNorm2Le_complexMatrixOp2_realRectToCMatrix M
  have hXcert : opNorm2Le X xnorm :=
    opNorm2Le_complexMatrixOp2_realRectToCMatrix X
  have hME : opNorm2Le (matMul r M E11) (μ * e) :=
    opNorm2Le_matMul r M E11 μ e hμ0 hMcert hE11
  have hMEX : opNorm2Le (matMul r (matMul r M E11) X)
      (μ * e * xnorm) :=
    opNorm2Le_matMul r (matMul r M E11) X
      (μ * e) xnorm (mul_nonneg hμ0 he0) hME hXcert
  have hneg : opNorm2Le
      (fun i j => -matMul r (matMul r M E11) X i j)
      (μ * e * xnorm) := by
    intro v
    have haction : matMulVec r
        (fun i j => -matMul r (matMul r M E11) X i j) v =
        fun i => -matMulVec r
          (matMul r (matMul r M E11) X) v i := by
      ext i
      unfold matMulVec
      rw [← Finset.sum_neg_distrib]
      apply Finset.sum_congr rfl
      intro j _
      ring
    rw [haction, vecNorm2_neg]
    exact hMEX v
  have hres : X = fun i j => M i j - matMul r (matMul r M E11) X i j := by
    ext i j
    have hs := higham10_14_actual_inverse_resolvent fp A hA11 hr1 hsuccess
    have hij := congrFun (congrFun hs i) j
    simpa [E, M, E11, X, matMul, Matrix.mul_apply] using hij
  have hXupperCert : opNorm2Le X (μ + μ * e * xnorm) := by
    have hadd := opNorm2Le_add M
      (fun i j => -matMul r (matMul r M E11) X i j)
      μ (μ * e * xnorm) hMcert hneg
    rw [hres]
    simpa [sub_eq_add_neg] using hadd
  have hxle : xnorm ≤ μ + μ * e * xnorm :=
    complexMatrixOp2_realRectToCMatrix_le_of_opNorm2Le X
      (add_nonneg hμ0 (mul_nonneg (mul_nonneg hμ0 he0) hx0)) hXupperCert
  have hsmall' : μ * e ≤ 1 / 2 := by
    simpa [μ, e, E, E11, M] using hsmall
  have hfinal : xnorm ≤ 2 * μ := by nlinarith
  simpa [xnorm, μ, X, M, E11, E] using hfinal

/-- Quantitative Lemma 10.10 for the literal trailing block in Theorem
10.14.  The leading term has the exact source coefficient
`(‖W‖₂+1)²‖E‖₂`; the displayed second term is a fixed multiple of `‖E‖₂²`.
The only radius assumptions control the actual perturbation and are not
bounds on the Schur complement or final residual. -/
theorem higham10_14_actualSchur_quadratic_bound {r s : ℕ}
    (fp : FPModel) (A : Fin (r + s) → Fin (r + s) → ℝ)
    (hPSD : IsPosSemiDef (r + s) A)
    (hrank : (Matrix.of A).rank = r)
    (hA11 : IsSymPosDef r (higham10_14_block11 A))
    (hr1 : gammaValid fp (r + 1))
    (hsuccess : ∀ q : Fin (r + s), q.val < r →
      0 < fl_cholPivot fp (r + s) A q)
    (hEone : complexMatrixOp2 (realRectToCMatrix
      (higham10_14_sourceError fp A r (Nat.le_add_right r s))) ≤ 1)
    (hinvRadius :
      complexMatrixOp2 (realRectToCMatrix
          (nonsingInv r (higham10_14_block11 A))) *
        complexMatrixOp2 (realRectToCMatrix
          (higham10_14_sourceError fp A r (Nat.le_add_right r s))) ≤ 1 / 2) :
    let E := higham10_14_sourceError fp A r (Nat.le_add_right r s)
    let e := complexMatrixOp2 (realRectToCMatrix E)
    let a := complexMatrixOp2 (realRectToCMatrix A)
    let M := nonsingInv r (higham10_14_block11 A)
    let μ := complexMatrixOp2 (realRectToCMatrix M)
    let W := higham10_14_W A
    let w := complexMatrixOp2 (realRectToCMatrix W)
    let C := (s : ℝ) *
      ((r : ℝ) ^ 2 * μ + 2 * (r : ℝ) ^ 6 * a ^ 2 * μ ^ 3 +
        4 * (r : ℝ) ^ 4 * a * μ ^ 2 + 2 * (r : ℝ) ^ 4 * μ ^ 2)
    complexMatrixOp2 (realRectToCMatrix (higham10_14_actualSchur fp A)) ≤
      e * (w + 1) ^ 2 + C * e ^ 2 := by
  dsimp only
  let E := higham10_14_sourceError fp A r (Nat.le_add_right r s)
  let e := complexMatrixOp2 (realRectToCMatrix E)
  let a := complexMatrixOp2 (realRectToCMatrix A)
  let A12 : Matrix (Fin r) (Fin s) ℝ := higham10_14_block12 A
  let A21 : Matrix (Fin s) (Fin r) ℝ := higham10_14_block21 A
  let M : Matrix (Fin r) (Fin r) ℝ :=
    nonsingInv r (higham10_14_block11 A)
  let μ := complexMatrixOp2 (realRectToCMatrix M)
  let W : Matrix (Fin r) (Fin s) ℝ := higham10_14_W A
  let Wt : Matrix (Fin s) (Fin r) ℝ := finiteTranspose W
  let w := complexMatrixOp2 (realRectToCMatrix W)
  let E11 : Matrix (Fin r) (Fin r) ℝ := higham10_14_block11 E
  let E12 : Matrix (Fin r) (Fin s) ℝ := higham10_14_block12 E
  let E21 : Matrix (Fin s) (Fin r) ℝ := higham10_14_block21 E
  let E22 : Matrix (Fin s) (Fin s) ℝ := higham10_14_block22 E
  let X : Matrix (Fin r) (Fin r) ℝ :=
    nonsingInv r (higham10_14_block11 A + higham10_14_block11 E)
  let R : Matrix (Fin s) (Fin s) ℝ :=
    -(E21 * M * E12)
      - A21 * (M * E11 * (M * E11 * X)) * A12
      + E21 * (M * E11 * X) * A12
      + A21 * (M * E11 * X) * E12
      + E21 * (M * E11 * X) * E12
  let C0 := (r : ℝ) ^ 2 * μ + 2 * (r : ℝ) ^ 6 * a ^ 2 * μ ^ 3 +
    4 * (r : ℝ) ^ 4 * a * μ ^ 2 + 2 * (r : ℝ) ^ 4 * μ ^ 2
  let C := (s : ℝ) * C0
  have he0 : 0 ≤ e := complexMatrixOp2_nonneg _
  have ha0 : 0 ≤ a := complexMatrixOp2_nonneg _
  have hμ0 : 0 ≤ μ := complexMatrixOp2_nonneg _
  have hw0 : 0 ≤ w := complexMatrixOp2_nonneg _
  have hC0 : 0 ≤ C0 := by dsimp [C0]; positivity
  have hC : 0 ≤ C := mul_nonneg (Nat.cast_nonneg s) hC0
  have hEfull : opNorm2Le E e :=
    opNorm2Le_complexMatrixOp2_realRectToCMatrix E
  obtain ⟨hE11op, hE12op, hE21op, _hE22op⟩ :=
    higham10_14_blocks_opNorm2Le E hEfull
  have hAfull : opNorm2Le A a :=
    opNorm2Le_complexMatrixOp2_realRectToCMatrix A
  obtain ⟨_hA11op, hA12op, hA21op, _hA22op⟩ :=
    higham10_14_blocks_opNorm2Le A hAfull
  have hMop : opNorm2Le M μ :=
    opNorm2Le_complexMatrixOp2_realRectToCMatrix M
  have hE11norm : complexMatrixOp2 (realRectToCMatrix E11) ≤ e :=
    complexMatrixOp2_realRectToCMatrix_le_of_opNorm2Le E11 he0 hE11op
  have hsmall11 : μ * complexMatrixOp2 (realRectToCMatrix E11) ≤ 1 / 2 := by
    exact le_trans (mul_le_mul_of_nonneg_left hE11norm hμ0)
      (by simpa [μ, e, E, M] using hinvRadius)
  have hXnorm : complexMatrixOp2 (realRectToCMatrix X) ≤ 2 * μ := by
    simpa [E, E11, X, M, μ] using
      higham10_14_actual_inverse_complexOp2_le fp A hA11 hr1 hsuccess hsmall11
  have hXop : opNorm2Le X (2 * μ) := by
    intro v
    calc
      vecNorm2 (matMulVec r X v) ≤
          complexMatrixOp2 (realRectToCMatrix X) * vecNorm2 v :=
        opNorm2Le_complexMatrixOp2_realRectToCMatrix X v
      _ ≤ (2 * μ) * vecNorm2 v :=
        mul_le_mul_of_nonneg_right hXnorm (vecNorm2_nonneg v)
  have hE11r : rectOpNorm2Le E11 e := by
    intro v
    simpa [rectOpNorm2Le, opNorm2Le, rectMatMulVec, matMulVec] using hE11op v
  have hMr : rectOpNorm2Le M μ := by
    intro v
    simpa [rectOpNorm2Le, opNorm2Le, rectMatMulVec, matMulVec] using hMop v
  have hXr : rectOpNorm2Le X (2 * μ) := by
    intro v
    simpa [rectOpNorm2Le, opNorm2Le, rectMatMulVec, matMulVec] using hXop v
  have hA21ent : ∀ i j, |A21 i j| ≤ a :=
    fun i j => higham10_14_abs_entry_le_of_rectOpNorm2Le A21 hA21op i j
  have hA12ent : ∀ i j, |A12 i j| ≤ a :=
    fun i j => higham10_14_abs_entry_le_of_rectOpNorm2Le A12 hA12op i j
  have hE21ent : ∀ i j, |E21 i j| ≤ e :=
    fun i j => higham10_14_abs_entry_le_of_rectOpNorm2Le E21 hE21op i j
  have hE12ent : ∀ i j, |E12 i j| ≤ e :=
    fun i j => higham10_14_abs_entry_le_of_rectOpNorm2Le E12 hE12op i j
  have hE11ent : ∀ i j, |E11 i j| ≤ e :=
    fun i j => higham10_14_abs_entry_le_of_rectOpNorm2Le E11 hE11r i j
  have hMent : ∀ i j, |M i j| ≤ μ :=
    fun i j => higham10_14_abs_entry_le_of_rectOpNorm2Le M hMr i j
  have hXent : ∀ i j, |X i j| ≤ 2 * μ :=
    fun i j => higham10_14_abs_entry_le_of_rectOpNorm2Le X hXr i j
  have hRraw := schur_perturbation_remainder_bound
    A21 E21 A12 E12 M X E11 a μ (2 * μ) e
    ha0 hμ0 (mul_nonneg (by norm_num) hμ0) he0
    hA21ent hA12ent hE21ent hE12ent hE11ent hMent hXent
  have hcoef :
      (r : ℝ) ^ 2 * μ + (r : ℝ) ^ 6 * a ^ 2 * μ ^ 2 * (2 * μ) +
          2 * ((r : ℝ) ^ 4 * a * μ * (2 * μ)) +
          (r : ℝ) ^ 4 * μ * (2 * μ) * e ≤ C0 := by
    calc
      (r : ℝ) ^ 2 * μ + (r : ℝ) ^ 6 * a ^ 2 * μ ^ 2 * (2 * μ) +
            2 * ((r : ℝ) ^ 4 * a * μ * (2 * μ)) +
            (r : ℝ) ^ 4 * μ * (2 * μ) * e =
          ((r : ℝ) ^ 2 * μ + 2 * (r : ℝ) ^ 6 * a ^ 2 * μ ^ 3 +
            4 * (r : ℝ) ^ 4 * a * μ ^ 2) +
              (2 * (r : ℝ) ^ 4 * μ ^ 2) * e := by ring
      _ ≤ ((r : ℝ) ^ 2 * μ + 2 * (r : ℝ) ^ 6 * a ^ 2 * μ ^ 3 +
            4 * (r : ℝ) ^ 4 * a * μ ^ 2) +
              (2 * (r : ℝ) ^ 4 * μ ^ 2) * 1 :=
        add_le_add le_rfl
          (mul_le_mul_of_nonneg_left (by simpa [e, E] using hEone) (by positivity))
      _ = C0 := by ring
  have hRentry : ∀ i j, |R i j| ≤ C0 * e ^ 2 := by
    intro i j
    calc
      |R i j| ≤
          ((r : ℝ) ^ 2 * μ + (r : ℝ) ^ 6 * a ^ 2 * μ ^ 2 * (2 * μ) +
            2 * ((r : ℝ) ^ 4 * a * μ * (2 * μ)) +
            (r : ℝ) ^ 4 * μ * (2 * μ) * e) * e ^ 2 := by
        simpa [R] using hRraw i j
      _ ≤ C0 * e ^ 2 := mul_le_mul_of_nonneg_right hcoef (sq_nonneg e)
  have hscaled := opNorm2Le_smul s (fun _ _ : Fin s => (1 : ℝ))
    (s : ℝ) (C0 * e ^ 2) (mul_nonneg hC0 (sq_nonneg e))
    (higham10_7_onesMatrix_opNorm2Le s)
  have hRop : opNorm2Le R (C * e ^ 2) := by
    have hpre := opNorm2Le_of_abs_le s R (fun _ _ => C0 * e ^ 2 * 1)
      (fun i j => by rw [mul_one]; exact hRentry i j)
      (C0 * e ^ 2 * (s : ℝ)) hscaled
    convert hpre using 1 <;> simp [C] <;> ring
  let L : Matrix (Fin s) (Fin s) ℝ := fun i j =>
    E22 i j - rectMatMul E21 W i j -
      rectMatMul (finiteTranspose W) E12 i j +
      rectMatMul (rectMatMul (finiteTranspose W) E11) W i j
  have hLrect : rectOpNorm2Le L (e * (w + 1) ^ 2) := by
    simpa [L, E, E11, E12, E21, E22, W, e, w] using
      higham10_14_linearSchur_opNorm2Le A E
  have hLop : opNorm2Le L (e * (w + 1) ^ 2) := by
    intro v
    simpa [rectOpNorm2Le, opNorm2Le, rectMatMulVec, matMulVec] using hLrect v
  have hMA12 : M * A12 = (W : Matrix (Fin r) (Fin s) ℝ) := by
    ext i j
    rfl
  have hA21M : A21 * M =
      Wt := by
    ext i j
    exact congrFun (congrFun
      (higham10_14_A21M_eq_Wtranspose A hPSD.1) i) j
  have hterm1 : E21 * M * A12 = E21 * (W : Matrix (Fin r) (Fin s) ℝ) := by
    rw [Matrix.mul_assoc, hMA12]
  have hterm2 : A21 * M * E12 =
      Wt * E12 := by
    rw [hA21M]
  have hterm3 : A21 * (M * E11 * M) * A12 =
      Wt * E11 * W := by
    calc
      A21 * (M * E11 * M) * A12 = (A21 * M) * E11 * (M * A12) := by
        simp only [Matrix.mul_assoc]
      _ = Wt * E11 * W := by
        rw [hA21M, hMA12]
  have hexact := higham10_14_actual_schur_perturbation_exact
    fp A hPSD hrank hA11 hr1 hsuccess
  have hEqM : (higham10_14_actualSchur fp A : Matrix (Fin s) (Fin s) ℝ) =
      (L : Matrix (Fin s) (Fin s) ℝ) + R := by
    dsimp only at hexact
    rw [hterm1, hterm2, hterm3] at hexact
    calc
      (higham10_14_actualSchur fp A : Matrix (Fin s) (Fin s) ℝ) =
          (E22 - E21 * W - Wt * E12 + Wt * E11 * W) + R := by
        simpa [E, A12, A21, M, E11, E12, E21, E22, X, R] using hexact
      _ = (L : Matrix (Fin s) (Fin s) ℝ) + R := by
        congr 1
  have hEq : higham10_14_actualSchur fp A =
      fun i j => L i j + R i j := by
    ext i j
    exact congrFun (congrFun hEqM i) j
  have hSop : opNorm2Le (higham10_14_actualSchur fp A)
      (e * (w + 1) ^ 2 + C * e ^ 2) := by
    rw [hEq]
    exact opNorm2Le_add L R _ _ hLop hRop
  have hbound := complexMatrixOp2_realRectToCMatrix_le_of_opNorm2Le
    (higham10_14_actualSchur fp A)
    (add_nonneg (mul_nonneg he0 (sq_nonneg (w + 1)))
      (mul_nonneg hC (sq_nonneg e))) hSop
  simpa [E, e, a, M, μ, W, Wt, w, C, C0] using hbound

/-- **Theorem 10.14, equation (10.22), literal family form.**

For a family of floating-point models whose unit roundoff tends to zero, this
theorem bounds the operator 2-norm of the matrix produced by the literal
truncated Cholesky executor.  The leading coefficient is exactly the one in
the book, and the remainder is the uniform family-level `O(u²)` predicate.
The hypotheses below are explicit small-roundoff radii on `gamma` and the
actual source error; none assumes a bound on the final residual or trailing
Schur block. -/
theorem higham10_14_equation_10_22_family_of_success
    {ι : Type*} {l : Filter ι} {r s : ℕ}
    (F : ι → FPModel) (U : RoundoffFamily ι l)
    (hunit : ∀ t, (F t).u = U.unit t)
    (A : Fin (r + s) → Fin (r + s) → ℝ)
    (hr0 : 0 < r)
    (hPSD : IsPosSemiDef (r + s) A)
    (hrank : (Matrix.of A).rank = r)
    (hA11 : IsSymPosDef r (higham10_14_block11 A))
    (hsuccess : ∀ t, ∀ q : Fin (r + s), q.val < r →
      0 < fl_cholPivot (F t) (r + s) A q)
    (hhalf : ∀ t, ((r + 1 : ℕ) : ℝ) * U.unit t ≤ 1 / 2)
    (hgammaRadius : ∀ t,
      (r : ℝ) * gamma (F t) (r + 1) ≤ 1 / 2)
    (hlinearAbsorb : ∀ t,
      (gamma (F t) (r + 1) /
          (1 - (r : ℝ) * gamma (F t) (r + 1))) *
        ((r + s : ℕ) : ℝ) *
          (complexMatrixOp2 (realRectToCMatrix (higham10_14_W A)) + 1) ^ 2 ≤
        1 / 4)
    (hquadraticAbsorb : ∀ t,
      (gamma (F t) (r + 1) /
          (1 - (r : ℝ) * gamma (F t) (r + 1))) *
        ((r + s : ℕ) : ℝ) * higham10_14_schurQuadraticCoeff A *
          complexMatrixOp2 (realRectToCMatrix
            (higham10_14_sourceError (F t) A r
              (Nat.le_add_right r s))) ≤ 1 / 4)
    (hEone : ∀ t, complexMatrixOp2 (realRectToCMatrix
      (higham10_14_sourceError (F t) A r (Nat.le_add_right r s))) ≤ 1)
    (hinvRadius : ∀ t,
      complexMatrixOp2 (realRectToCMatrix
          (nonsingInv r (higham10_14_block11 A))) *
        complexMatrixOp2 (realRectToCMatrix
          (higham10_14_sourceError (F t) A r
            (Nat.le_add_right r s))) ≤ 1 / 2) :
    FamilyFirstOrderLe l U.unit
      (fun t =>
        2 * (r : ℝ) * gamma (F t) (r + 1) *
          complexMatrixOp2 (realRectToCMatrix A) *
          (complexMatrixOp2 (realRectToCMatrix (higham10_14_W A)) + 1) ^ 2)
      (fun t => complexMatrixOp2 (realRectToCMatrix
        (higham10_14_actualResidual (F t) A))) := by
  let u : ι → ℝ := U.unit
  let g : ι → ℝ := fun t => gamma (F t) (r + 1)
  let E : ι → Fin (r + s) → Fin (r + s) → ℝ := fun t =>
    higham10_14_sourceError (F t) A r (Nat.le_add_right r s)
  let e : ι → ℝ := fun t => complexMatrixOp2 (realRectToCMatrix (E t))
  let q : ι → ℝ := fun t => complexMatrixOp2
    (realRectToCMatrix (higham10_14_actualSchur (F t) A))
  let d : ι → ℝ := fun t => complexMatrixOp2
    (realRectToCMatrix (higham10_14_actualResidual (F t) A))
  let a : ℝ := complexMatrixOp2 (realRectToCMatrix A)
  let W := higham10_14_W A
  let w : ℝ := complexMatrixOp2 (realRectToCMatrix W)
  let K : ℝ := (w + 1) ^ 2
  let C : ℝ := higham10_14_schurQuadraticCoeff A
  let CG : ℝ := 2 * ((r + 1 : ℕ) : ℝ)
  have ha0 : 0 ≤ a := complexMatrixOp2_nonneg _
  have hw0 : 0 ≤ w := complexMatrixOp2_nonneg _
  have hK : 1 ≤ K := by
    dsimp [K]
    nlinarith [sq_nonneg w]
  have hC : 0 ≤ C := by
    unfold C higham10_14_schurQuadraticCoeff
    dsimp only
    have ha' : 0 ≤ complexMatrixOp2 (realRectToCMatrix A) :=
      complexMatrixOp2_nonneg _
    have hμ' : 0 ≤ complexMatrixOp2 (realRectToCMatrix
        (nonsingInv r (higham10_14_block11 A))) :=
      complexMatrixOp2_nonneg _
    positivity
  have hCG : 0 ≤ CG := by dsimp [CG]; positivity
  have hr1 : ∀ t, gammaValid (F t) (r + 1) := by
    intro t
    unfold gammaValid
    rw [hunit t]
    linarith [hhalf t]
  have hg0 : ∀ t, 0 ≤ g t := fun t => gamma_nonneg (F t) (hr1 t)
  have hg : ∀ t, g t ≤ CG * u t := by
    intro t
    have ht := gamma_le_two_mul_n_u_of_nu_le_half (F t) (r + 1)
      (by simpa [hunit t] using hhalf t)
    dsimp [g, CG, u]
    rw [hunit t] at ht
    convert ht using 1 <;> ring
  have he0 : ∀ t, 0 ≤ e t := fun t => complexMatrixOp2_nonneg _
  have hq0 : ∀ t, 0 ≤ q t := fun t => complexMatrixOp2_nonneg _
  have hd0 : ∀ t, 0 ≤ d t := fun t => complexMatrixOp2_nonneg _
  have hSop : ∀ t,
      opNorm2Le (higham10_14_actualSchur (F t) A) (q t) := by
    intro t
    exact opNorm2Le_complexMatrixOp2_realRectToCMatrix _
  have hrows : ∀ t,
      rectOpNorm2Le (higham10_14_sourceTrailingRows (F t) A) (q t) := by
    intro t
    exact higham10_14_trailingRows_opNorm2Le_of_actualSchur
      (F t) A (hq0 t) (hSop t)
  have hrowsNorm : ∀ t,
      complexMatrixOp2
          (realRectToCMatrix (higham10_14_sourceTrailingRows (F t) A)) ≤
        q t := by
    intro t
    exact complexMatrixOp2_realRectToCMatrix_le_of_rectOpNorm2Le _
      (hq0 t) (hrows t)
  have htrail : ∀ t,
      opNorm2Le
        (higham10_14_sourceTrailing (F t) A r (Nat.le_add_right r s))
        (q t) := by
    intro t
    exact higham10_14_sourceTrailing_opNorm2Le_of_rows (F t) A (hrows t)
  have he : ∀ t, e t ≤
      g t / (1 - (r : ℝ) * g t) *
        ((r : ℝ) * a + ((r + s : ℕ) : ℝ) * q t) := by
    intro t
    have hrg : (r : ℝ) * g t < 1 :=
      lt_of_le_of_lt (by simpa [g] using hgammaRadius t) (by norm_num)
    have h25 := higham10_14_equation_10_25
      (F t) A hr0 (hr1 t) hrg hPSD.1 (hsuccess t)
    let rowsNorm := complexMatrixOp2
      (realRectToCMatrix (higham10_14_sourceTrailingRows (F t) A))
    have hden : 0 < 1 - (r : ℝ) * g t := by linarith
    have hα0 : 0 ≤ g t / (1 - (r : ℝ) * g t) :=
      div_nonneg (hg0 t) hden.le
    have hbase0 : 0 ≤ (r : ℝ) * a + ((r + s : ℕ) : ℝ) * rowsNorm := by
      exact add_nonneg
        (mul_nonneg (Nat.cast_nonneg r) ha0)
        (mul_nonneg (Nat.cast_nonneg (r + s)) (complexMatrixOp2_nonneg _))
    have heRaw : e t ≤
        g t / (1 - (r : ℝ) * g t) *
          ((r : ℝ) * a + ((r + s : ℕ) : ℝ) * rowsNorm) := by
      exact complexMatrixOp2_realRectToCMatrix_le_of_opNorm2Le (E t)
        (mul_nonneg hα0 hbase0) (by simpa [E, e, g, a, rowsNorm] using h25)
    calc
      e t ≤ g t / (1 - (r : ℝ) * g t) *
          ((r : ℝ) * a + ((r + s : ℕ) : ℝ) * rowsNorm) := heRaw
      _ ≤ g t / (1 - (r : ℝ) * g t) *
          ((r : ℝ) * a + ((r + s : ℕ) : ℝ) * q t) := by
        apply mul_le_mul_of_nonneg_left _ hα0
        exact add_le_add le_rfl
          (mul_le_mul_of_nonneg_left
            (by simpa [rowsNorm] using hrowsNorm t)
            (Nat.cast_nonneg (r + s)))
  have hq : ∀ t, q t ≤ K * e t + C * e t ^ 2 := by
    intro t
    have ht := higham10_14_actualSchur_quadratic_bound
      (F t) A hPSD hrank hA11 (hr1 t) (hsuccess t)
      (by simpa [E, e] using hEone t)
      (by simpa [E, e] using hinvRadius t)
    change q t ≤ e t * K + C * e t ^ 2 at ht
    nlinarith
  have hd : ∀ t, d t ≤ e t + q t := by
    intro t
    have hEop : opNorm2Le (E t) (e t) :=
      opNorm2Le_complexMatrixOp2_realRectToCMatrix _
    have hErect : rectOpNorm2Le (E t) (e t) := by
      intro v
      simpa [rectOpNorm2Le, opNorm2Le, rectMatMulVec, matMulVec] using hEop v
    have hnegRect := higham10_14_rectOpNorm2Le_neg (E t) hErect
    have hneg : opNorm2Le (fun i j => -(E t i j)) (e t) := by
      intro v
      simpa [rectOpNorm2Le, opNorm2Le, rectMatMulVec, matMulVec] using hnegRect v
    have hadd := opNorm2Le_add
      (higham10_14_sourceTrailing (F t) A r (Nat.le_add_right r s))
      (fun i j => -(E t i j)) (q t) (e t) (htrail t) hneg
    have h23 := higham10_14_equation_10_23
      (F t) A r (Nat.le_add_right r s)
    have hres : higham10_14_actualResidual (F t) A = fun i j =>
        higham10_14_sourceTrailing (F t) A r (Nat.le_add_right r s) i j -
          E t i j := by
      ext i j
      have hij := h23 i j
      unfold higham10_14_actualResidual
      dsimp [E]
      linarith
    have hresOp : opNorm2Le (higham10_14_actualResidual (F t) A)
        (q t + e t) := by
      rw [hres]
      simpa [sub_eq_add_neg] using hadd
    have hnorm := complexMatrixOp2_realRectToCMatrix_le_of_opNorm2Le
      (higham10_14_actualResidual (F t) A)
      (add_nonneg (hq0 t) (he0 t)) hresOp
    dsimp [d]
    linarith
  apply higham10_14_scalar_absorption_family_of_error_sq
    r (r + s) u g e q d a K C CG ha0 hK hC hCG
    U.unit_nonneg U.unit_le_one hg0 he0 hq0 hd0 hg
  · intro t
    simpa [g] using hgammaRadius t
  · intro t
    simpa [g, K, W, w] using hlinearAbsorb t
  · intro t
    simpa [g, C, E, e] using hquadraticAbsorb t
  · exact he
  · exact hq
  · exact hd

/-- Source-facing form of (10.22): display (10.21) is used to derive the
positive pivots of the literal rounded executor, after which
`higham10_14_equation_10_22_family_of_success` supplies the matrix 2-norm
bound and uniform quadratic remainder. -/
theorem higham10_14_equation_10_22_family
    {ι : Type*} {l : Filter ι} {r s : ℕ}
    (F : ι → FPModel) (U : RoundoffFamily ι l)
    (hunit : ∀ t, (F t).u = U.unit t)
    (A : Fin (r + s) → Fin (r + s) → ℝ)
    (hr0 : 0 < r)
    (hPSD : IsPosSemiDef (r + s) A)
    (hrank : (Matrix.of A).rank = r)
    (hA11 : IsSymPosDef r (higham10_14_block11 A))
    (hH11sym : IsSymmetricFiniteMatrix (fun i j : Fin r =>
      A (Fin.castAdd s i) (Fin.castAdd s j) /
        (Real.sqrt (A (Fin.castAdd s i) (Fin.castAdd s i)) *
         Real.sqrt (A (Fin.castAdd s j) (Fin.castAdd s j)))))
    (h1021 : ∀ t, (r : ℝ) *
        (gamma (F t) (r + 1) / (1 - gamma (F t) (r + 1))) <
      finiteMinEigenvalue hr0 (fun i j : Fin r =>
        A (Fin.castAdd s i) (Fin.castAdd s j) /
          (Real.sqrt (A (Fin.castAdd s i) (Fin.castAdd s i)) *
           Real.sqrt (A (Fin.castAdd s j) (Fin.castAdd s j)))) hH11sym)
    (hhalf : ∀ t, ((r + 1 : ℕ) : ℝ) * U.unit t ≤ 1 / 2)
    (hgammaRadius : ∀ t,
      (r : ℝ) * gamma (F t) (r + 1) ≤ 1 / 2)
    (hlinearAbsorb : ∀ t,
      (gamma (F t) (r + 1) /
          (1 - (r : ℝ) * gamma (F t) (r + 1))) *
        ((r + s : ℕ) : ℝ) *
          (complexMatrixOp2 (realRectToCMatrix (higham10_14_W A)) + 1) ^ 2 ≤
        1 / 4)
    (hquadraticAbsorb : ∀ t,
      (gamma (F t) (r + 1) /
          (1 - (r : ℝ) * gamma (F t) (r + 1))) *
        ((r + s : ℕ) : ℝ) * higham10_14_schurQuadraticCoeff A *
          complexMatrixOp2 (realRectToCMatrix
            (higham10_14_sourceError (F t) A r
              (Nat.le_add_right r s))) ≤ 1 / 4)
    (hEone : ∀ t, complexMatrixOp2 (realRectToCMatrix
      (higham10_14_sourceError (F t) A r (Nat.le_add_right r s))) ≤ 1)
    (hinvRadius : ∀ t,
      complexMatrixOp2 (realRectToCMatrix
          (nonsingInv r (higham10_14_block11 A))) *
        complexMatrixOp2 (realRectToCMatrix
          (higham10_14_sourceError (F t) A r
            (Nat.le_add_right r s))) ≤ 1 / 2) :
    FamilyFirstOrderLe l U.unit
      (fun t =>
        2 * (r : ℝ) * gamma (F t) (r + 1) *
          complexMatrixOp2 (realRectToCMatrix A) *
          (complexMatrixOp2 (realRectToCMatrix (higham10_14_W A)) + 1) ^ 2)
      (fun t => complexMatrixOp2 (realRectToCMatrix
        (higham10_14_actualResidual (F t) A))) := by
  have hr1 : ∀ t, gammaValid (F t) (r + 1) := by
    intro t
    unfold gammaValid
    rw [hunit t]
    linarith [hhalf t]
  have hγlt : ∀ t, gamma (F t) (r + 1) < 1 := by
    intro t
    have hg0 := gamma_nonneg (F t) (hr1 t)
    have hrOne : (1 : ℝ) ≤ r := by exact_mod_cast hr0
    have hle : gamma (F t) (r + 1) ≤
        (r : ℝ) * gamma (F t) (r + 1) :=
      le_mul_of_one_le_left hg0 hrOne
    linarith [hgammaRadius t]
  have hsuccess : ∀ t, ∀ q : Fin (r + s), q.val < r →
      0 < fl_cholPivot (F t) (r + s) A q := by
    intro t
    have hs := higham10_14_fl_cholesky_success_source
      (F t) A r hr0 (Nat.le_add_right r s)
      (by simpa [higham10_14_block11, Fin.castAdd] using hA11)
      (hr1 t) (hγlt t)
      (by simpa [Fin.castAdd] using hH11sym)
      (by simpa [Fin.castAdd] using h1021 t)
    exact hs
  exact higham10_14_equation_10_22_family_of_success
    F U hunit A hr0 hPSD hrank hA11 hsuccess hhalf hgammaRadius
    hlinearAbsorb hquadraticAbsorb hEone hinvRadius

end NumStability
