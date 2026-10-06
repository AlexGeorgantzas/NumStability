import NumStability.Algorithms.HighamChapter9
import NumStability.Algorithms.LinearSystems.Triangular.InverseBounds
import NumStability.Algorithms.Cholesky.CholeskySpec

namespace NumStability

open scoped BigOperators

noncomputable section

/-!
# Higham Theorem 10.8: componentwise resolvent bridge

This file closes the non-circular algebraic core of the second clause of
Theorem 10.8.  If an upper-triangular normalized factor `S` with positive
diagonal satisfies

`Sᵀ S = I - G`,

then, for `C = |G|` and `rho(C) < 1`,

`|I - S| <= triu(C (I - C)⁻¹)`.

The proof uses the exact identity `T - S = T G` for `T = S⁻ᵀ`.  Triangularity
and positivity give the entrywise inequality

`|T| <= I + |T| C`.

The canonical nonnegative resolvent therefore yields
`|T| <= (I - C)⁻¹`; substituting this back into `T - S = T G` gives the
printed upper-triangular envelope.  No copy of the desired conclusion occurs
among the hypotheses.
-/

private theorem higham10_8_one_sub_le_recip_sub_abs
    {s t : ℝ} (hs : 0 < s) (ht : t = 1 / s) :
    |1 - s| ≤ |t - s| := by
  subst t
  by_cases hle : s ≤ 1
  · have hsq : s * s ≤ 1 := by nlinarith
    have hst : s ≤ 1 / s := (le_div_iff₀ hs).2 (by simpa using hsq)
    have htone : 1 ≤ 1 / s := (le_div_iff₀ hs).2 (by simpa using hle)
    rw [abs_of_nonneg (by linarith), abs_of_nonneg (by linarith)]
    linarith
  · have hone : 1 ≤ s := le_of_lt (lt_of_not_ge hle)
    have hts : 1 / s ≤ 1 := (div_le_one hs).2 hone
    rw [abs_of_nonpos (by linarith), abs_of_nonpos (by linarith)]
    linarith

private theorem higham10_8_recip_abs_le_one_add_gap
    {s t : ℝ} (hs : 0 < s) (ht : t = 1 / s) :
    |t| ≤ 1 + |t - s| := by
  subst t
  have htpos : 0 < 1 / s := one_div_pos.mpr hs
  rw [abs_of_pos htpos]
  by_cases hle : s ≤ 1
  · have hsq : s * s ≤ 1 := by nlinarith
    have hst : s ≤ 1 / s := (le_div_iff₀ hs).2 (by simpa using hsq)
    rw [abs_of_nonneg (by linarith)]
    linarith
  · have hone : 1 ≤ s := le_of_lt (lt_of_not_ge hle)
    have hts : 1 / s ≤ 1 := (div_le_one hs).2 hone
    linarith [abs_nonneg (1 / s - s)]

private theorem higham10_8_absMatrix_symmetric_of_symmetric {n : ℕ}
    (G : Fin n → Fin n → ℝ) (hG : IsSymmetricFiniteMatrix G) :
    IsSymmetricFiniteMatrix (absMatrix n G) := by
  intro i j
  simp only [absMatrix]
  rw [hG i j]

private theorem higham10_8_matSub_id_symmetric {n : ℕ}
    (C : Fin n → Fin n → ℝ) (hC : IsSymmetricFiniteMatrix C) :
    IsSymmetricFiniteMatrix (matSub_id n C) := by
  intro i j
  unfold matSub_id idMatrix
  rw [hC i j]
  by_cases hij : i = j
  · subst j
    rfl
  · have hji : j ≠ i := fun h => hij h.symm
    simp [hij, hji]

/-- A right-acting version of the repository resolvent majorant.  Symmetry of
`C` and its resolvent turns `W <= I + W C` into the existing columnwise
left-acting theorem after transposition. -/
private theorem higham10_8_right_resolvent_majorant_id {n : ℕ}
    (C R W : Fin n → Fin n → ℝ)
    (hC : IsSymmetricFiniteMatrix C)
    (hR : IsSymmetricFiniteMatrix R)
    (hres : ch7NonnegativeResolvent n C R)
    (hineq : ∀ i j : Fin n,
      W i j ≤ idMatrix n i j + rectMatMul W C i j) :
    ∀ i j : Fin n, W i j ≤ R i j := by
  let WT : Fin n → Fin n → ℝ := finiteTranspose W
  have htrans : ∀ i j : Fin n,
      WT i j ≤ idMatrix n i j + rectMatMul C WT i j := by
    intro i j
    have h := hineq j i
    have hmul : rectMatMul W C j i = rectMatMul C WT i j := by
      unfold rectMatMul WT finiteTranspose
      apply Finset.sum_congr rfl
      intro k _
      rw [hC i k]
      ring
    simpa [WT, finiteTranspose, idMatrix, hmul, eq_comm] using h
  have hbound :=
    higham9_15_resolvent_matrix_majorant_of_componentwise_inequality
      C R (idMatrix n) WT hres htrans
  intro i j
  have h := hbound j i
  rw [rectMatMul_id_right] at h
  simpa [WT, finiteTranspose, hR j i] using h

/-- The canonical resolvent commutes with its contraction matrix. -/
private theorem higham10_8_resolvent_commutes {n : ℕ}
    (C R : Fin n → Fin n → ℝ)
    (hInv : IsInverse n (matSub_id n C) R) :
    ∀ i j : Fin n,
      rectMatMul R C i j = rectMatMul C R i j := by
  intro i j
  have hleft := hInv.1 i j
  have hright := hInv.2 i j
  have hleft' : R i j - rectMatMul R C i j = idMatrix n i j := by
    simpa [IsLeftInverse, rectMatMul, matSub_id, idMatrix,
      mul_sub, Finset.sum_sub_distrib] using hleft
  have hright' : R i j - rectMatMul C R i j = idMatrix n i j := by
    simpa [IsRightInverse, rectMatMul, matSub_id, idMatrix,
      sub_mul, Finset.sum_sub_distrib] using hright
  linarith

/-- The exact normalized componentwise clause underlying Higham Theorem 10.8.

`S` is the normalized upper Cholesky factor and `G` is the normalized symmetric
matrix perturbation.  The only inverse premise is the ordinary two-sided
inverse certificate for `Sᵀ`; the spectral-radius hypothesis constructs the
printed canonical resolvent internally. -/
theorem higham10_8_normalized_componentwise_resolvent {n : ℕ}
    (hn : 0 < n)
    (S T G : Fin n → Fin n → ℝ)
    (hSupper : ∀ i j : Fin n, j.val < i.val → S i j = 0)
    (hSdiag : ∀ i : Fin n, 0 < S i i)
    (hTinv : IsInverse n (finiteTranspose S) T)
    (hGram : rectMatMul (finiteTranspose S) S = matSub_id n G)
    (hGsym : IsSymmetricFiniteMatrix G)
    (hrho :
      spectralRadius ℂ
        (Matrix.toLin'
          (show Matrix (Fin n) (Fin n) ℂ from
            realRectToCMatrix (absMatrix n G))) < 1) :
    ∀ i j : Fin n,
      |idMatrix n i j - S i j| ≤
        higham9_15_triuPart
          (rectMatMul (absMatrix n G)
            (nonsingInv n (matSub_id n (absMatrix n G)))) i j := by
  let C : Fin n → Fin n → ℝ := absMatrix n G
  let Res : Fin n → Fin n → ℝ := nonsingInv n (matSub_id n C)
  have hC_nonneg : ∀ i j : Fin n, 0 ≤ C i j := by
    intro i j
    simp [C, absMatrix]
  have hC_sym : IsSymmetricFiniteMatrix C := by
    exact higham10_8_absMatrix_symmetric_of_symmetric G hGsym
  have hIC_sym : IsSymmetricFiniteMatrix (matSub_id n C) :=
    higham10_8_matSub_id_symmetric C hC_sym
  have hRes_sym : IsSymmetricFiniteMatrix Res := by
    exact nonsingInv_symmetric_of_symmetric (matSub_id n C) hIC_sym
  have hres : ch7NonnegativeResolvent n C Res := by
    exact higham9_15_nonnegative_resolvent_nonsingInv_of_spectralRadius_lt_one
      hn C hC_nonneg (by simpa [C] using hrho)
  have hResInv : IsInverse n (matSub_id n C) Res := by
    exact higham9_15_matSub_id_nonsingInv_isInverse_of_spectralRadius_lt_one
      C (by simpa [C] using hrho)
  have hLlower : ∀ i j : Fin n, i.val < j.val → finiteTranspose S i j = 0 := by
    intro i j hij
    exact hSupper j i hij
  have hLdiag : ∀ i : Fin n, finiteTranspose S i i ≠ 0 := by
    intro i
    exact ne_of_gt (hSdiag i)
  have hTlower : ∀ i j : Fin n, i.val < j.val → T i j = 0 :=
    inv_lower_tri n (finiteTranspose S) T hLlower hLdiag hTinv.1
  have hTdiag : ∀ i : Fin n, T i i = 1 / S i i := by
    intro i
    simpa [finiteTranspose] using
      inv_diag_entry_lower n (finiteTranspose S) T hLlower hLdiag
        hTinv.1 hTlower i
  have hTS : rectMatMul T (finiteTranspose S) = idMatrix n := by
    ext i j
    exact hTinv.1 i j
  have hTsubS : ∀ i j : Fin n,
      T i j - S i j = rectMatMul T G i j := by
    have hmul : rectMatMul T (matSub_id n G) = S := by
      calc
        rectMatMul T (matSub_id n G) =
            rectMatMul T (rectMatMul (finiteTranspose S) S) := by rw [hGram]
        _ = rectMatMul (rectMatMul T (finiteTranspose S)) S := by
            rw [rectMatMul_assoc]
        _ = rectMatMul (idMatrix n) S := by rw [hTS]
        _ = S := rectMatMul_id_left S
    intro i j
    have hentry := congrFun (congrFun hmul i) j
    have hexpand :
        rectMatMul T (matSub_id n G) i j =
          T i j - rectMatMul T G i j := by
      unfold rectMatMul matSub_id idMatrix
      simp_rw [mul_sub, Finset.sum_sub_distrib]
      simp
    rw [hexpand] at hentry
    linarith
  have hprod : ∀ i j : Fin n,
      |rectMatMul T G i j| ≤ rectMatMul (absMatrix n T) C i j := by
    intro i j
    simpa [C] using
      higham9_15_abs_rectMatMul_right_le T (absMatrix n T) G
        (fun _ _ => le_rfl) i j
  have hTmajorStep : ∀ i j : Fin n,
      absMatrix n T i j ≤
        idMatrix n i j + rectMatMul (absMatrix n T) C i j := by
    intro i j
    by_cases hij : i.val < j.val
    · simp only [absMatrix]
      rw [hTlower i j hij, abs_zero]
      have hsum : 0 ≤ rectMatMul (absMatrix n T) C i j := by
        unfold rectMatMul
        exact Finset.sum_nonneg fun k _ =>
          mul_nonneg (abs_nonneg _) (hC_nonneg k j)
      have hne : i ≠ j := Fin.ne_of_val_ne (by omega)
      simp [idMatrix, hne, hsum]
    · by_cases hji : j.val < i.val
      · have hSzero := hSupper i j hji
        have hidzero : idMatrix n i j = 0 := by
          have hne : i ≠ j := Fin.ne_of_val_ne (by omega)
          simp [idMatrix, hne]
        have heq : T i j = rectMatMul T G i j := by
          linarith [hTsubS i j]
        rw [absMatrix, heq, hidzero, zero_add]
        exact hprod i j
      · have heq : i = j := Fin.ext (by omega)
        subst j
        have hscalar :=
          higham10_8_recip_abs_le_one_add_gap (hSdiag i) (hTdiag i)
        have hgap : |T i i - S i i| ≤
            rectMatMul (absMatrix n T) C i i := by
          rw [hTsubS i i]
          exact hprod i i
        have hscalar' : |T i i| ≤
            1 + rectMatMul (absMatrix n T) C i i := by
          linarith
        simpa [absMatrix, idMatrix] using hscalar'
  have hTabs : ∀ i j : Fin n, absMatrix n T i j ≤ Res i j :=
    higham10_8_right_resolvent_majorant_id C Res (absMatrix n T)
      hC_sym hRes_sym hres hTmajorStep
  have hTC : ∀ i j : Fin n,
      rectMatMul (absMatrix n T) C i j ≤ rectMatMul Res C i j := by
    intro i j
    unfold rectMatMul
    apply Finset.sum_le_sum
    intro k _
    exact mul_le_mul_of_nonneg_right (hTabs i k) (hC_nonneg k j)
  have hcomm : ∀ i j : Fin n,
      rectMatMul Res C i j = rectMatMul C Res i j :=
    higham10_8_resolvent_commutes C Res hResInv
  intro i j
  by_cases hij : i.val ≤ j.val
  · rw [show higham9_15_triuPart (rectMatMul (absMatrix n G)
          (nonsingInv n (matSub_id n (absMatrix n G)))) i j =
          rectMatMul C Res i j by simp [higham9_15_triuPart, hij, C, Res]]
    by_cases heq : i = j
    · subst j
      have hscalar :=
        higham10_8_one_sub_le_recip_sub_abs (hSdiag i) (hTdiag i)
      have hgap : |T i i - S i i| ≤
          rectMatMul (absMatrix n T) C i i := by
        rw [hTsubS i i]
        exact hprod i i
      simpa [idMatrix] using
        hscalar.trans (hgap.trans ((hTC i i).trans_eq (hcomm i i)))
    · have hlt : i.val < j.val := by omega
      have hTzero := hTlower i j hlt
      have hidzero : idMatrix n i j = 0 := by simp [idMatrix, heq]
      have heqTG : -S i j = rectMatMul T G i j := by
        linarith [hTsubS i j]
      rw [hidzero, zero_sub, heqTG]
      exact (hprod i j).trans ((hTC i j).trans_eq (hcomm i j))
  · have hji : j.val < i.val := by omega
    have hSzero := hSupper i j hji
    have hne : i ≠ j := Fin.ne_of_val_ne (by omega)
    simp [higham9_15_triuPart, hij, idMatrix, hne, hSzero]

/-- The normalized perturbation matrix printed in Theorem 10.8:
`Gtilde = Rhat⁻ᵀ DeltaA Rhat⁻¹`. -/
noncomputable def higham10_8_Gtilde {n : ℕ}
    (RhatInv DeltaA : Fin n → Fin n → ℝ) : Fin n → Fin n → ℝ :=
  rectMatMul (finiteTranspose RhatInv) (rectMatMul DeltaA RhatInv)

/-- The matrix appearing before `|Rhat|` in the printed componentwise bound. -/
noncomputable def higham10_8_componentwiseEnvelope {n : ℕ}
    (Gtilde : Fin n → Fin n → ℝ) : Fin n → Fin n → ℝ :=
  higham9_15_triuPart
    (rectMatMul (absMatrix n Gtilde)
      (nonsingInv n (matSub_id n (absMatrix n Gtilde))))

/-- Congruence by an arbitrary real matrix preserves symmetry. -/
theorem higham10_8_Gtilde_symmetric {n : ℕ}
    (RhatInv DeltaA : Fin n → Fin n → ℝ)
    (hDeltaSym : IsSymmetricFiniteMatrix DeltaA) :
    IsSymmetricFiniteMatrix (higham10_8_Gtilde RhatInv DeltaA) := by
  intro i j
  unfold higham10_8_Gtilde rectMatMul finiteTranspose
  simp_rw [Finset.mul_sum]
  rw [Finset.sum_comm]
  apply Finset.sum_congr rfl
  intro k _
  apply Finset.sum_congr rfl
  intro l _
  rw [hDeltaSym l k]
  ring

/-- Source-shaped, non-circular componentwise endpoint for Theorem 10.8.

The normalized identities are exact algebraic certificates:

* `Sᵀ S = I - Gtilde`,
* `T = S⁻ᵀ`, and
* `DeltaR = (I - S) Rhat`.

From these identities and the sole analytic smallness condition
`rho(|Gtilde|) < 1`, the theorem derives the printed componentwise bound. -/
theorem higham10_8_componentwise_source_of_normalized_certificate {n : ℕ}
    (hn : 0 < n)
    (Rhat RhatInv DeltaA DeltaR S T : Fin n → Fin n → ℝ)
    (hDeltaSym : IsSymmetricFiniteMatrix DeltaA)
    (hSupper : ∀ i j : Fin n, j.val < i.val → S i j = 0)
    (hSdiag : ∀ i : Fin n, 0 < S i i)
    (hTinv : IsInverse n (finiteTranspose S) T)
    (hGram :
      rectMatMul (finiteTranspose S) S =
        matSub_id n (higham10_8_Gtilde RhatInv DeltaA))
    (hDeltaNormalized :
      DeltaR = rectMatMul
        (fun i j : Fin n => idMatrix n i j - S i j) Rhat)
    (hrho :
      spectralRadius ℂ
        (Matrix.toLin'
          (show Matrix (Fin n) (Fin n) ℂ from
            realRectToCMatrix
              (absMatrix n (higham10_8_Gtilde RhatInv DeltaA)))) < 1) :
    ∀ i j : Fin n,
      |DeltaR i j| ≤
        rectMatMul
          (higham10_8_componentwiseEnvelope
            (higham10_8_Gtilde RhatInv DeltaA))
          (absMatrix n Rhat) i j := by
  let Gtilde := higham10_8_Gtilde RhatInv DeltaA
  let B := higham10_8_componentwiseEnvelope Gtilde
  have hGsym : IsSymmetricFiniteMatrix Gtilde := by
    exact higham10_8_Gtilde_symmetric RhatInv DeltaA hDeltaSym
  have hX : ∀ i j : Fin n,
      |idMatrix n i j - S i j| ≤ B i j := by
    simpa [Gtilde, B, higham10_8_componentwiseEnvelope] using
      higham10_8_normalized_componentwise_resolvent hn S T Gtilde
        hSupper hSdiag hTinv (by simpa [Gtilde] using hGram)
        hGsym (by simpa [Gtilde] using hrho)
  intro i j
  rw [hDeltaNormalized]
  simpa [B, Gtilde] using
    higham9_15_abs_rectMatMul_right_le
      (fun a b : Fin n => idMatrix n a b - S a b) B Rhat hX i j

/-- Fully assembled componentwise clause of Higham Theorem 10.8.

Here `R` and `Rhat` are the positive-diagonal Cholesky factors of `A` and
`A + DeltaA`; `RhatInv` is the ordinary inverse of `Rhat`.  Every normalized
certificate consumed by
`higham10_8_componentwise_source_of_normalized_certificate` is constructed
inside this proof.  Thus the sole smallness assumption is exactly the printed
condition `rho(|Gtilde|) < 1`. -/
theorem higham10_8_componentwise_source {n : ℕ}
    (hn : 0 < n)
    (A R Rhat RhatInv DeltaA : Fin n → Fin n → ℝ)
    (hR : CholeskyFactSpec n A R)
    (hRhat : CholeskyFactSpec n
      (fun i j : Fin n => A i j + DeltaA i j) Rhat)
    (hRhatInv : IsInverse n Rhat RhatInv)
    (hrho :
      spectralRadius ℂ
        (Matrix.toLin'
          (show Matrix (Fin n) (Fin n) ℂ from
            realRectToCMatrix
              (absMatrix n (higham10_8_Gtilde RhatInv DeltaA)))) < 1) :
    ∀ i j : Fin n,
      |Rhat i j - R i j| ≤
        rectMatMul
          (higham10_8_componentwiseEnvelope
            (higham10_8_Gtilde RhatInv DeltaA))
          (absMatrix n Rhat) i j := by
  have hAsym : IsSymmetricFiniteMatrix A := by
    intro i j
    rw [← hR.product_eq i j, ← hR.product_eq j i]
    apply Finset.sum_congr rfl
    intro k _
    ring
  have hAplusSym : IsSymmetricFiniteMatrix
      (fun i j : Fin n => A i j + DeltaA i j) := by
    intro i j
    change A i j + DeltaA i j = A j i + DeltaA j i
    rw [← hRhat.product_eq i j, ← hRhat.product_eq j i]
    apply Finset.sum_congr rfl
    intro k _
    ring
  have hDeltaSym : IsSymmetricFiniteMatrix DeltaA := by
    intro i j
    have h₁ := hAplusSym i j
    have h₂ := hAsym i j
    dsimp at h₁
    linarith
  have hRhatDiag : ∀ i : Fin n, Rhat i i ≠ 0 :=
    fun i => ne_of_gt (hRhat.R_diag_pos i)
  have hRhatInvUpper : ∀ i j : Fin n,
      j.val < i.val → RhatInv i j = 0 :=
    inv_upper_tri n Rhat RhatInv hRhat.R_upper hRhatDiag hRhatInv.1
  have hRhatInvDiag : ∀ i : Fin n, RhatInv i i = 1 / Rhat i i :=
    inv_diag_entry n Rhat RhatInv hRhat.R_upper hRhatDiag
      hRhatInv.1 hRhatInvUpper
  let S : Fin n → Fin n → ℝ := rectMatMul R RhatInv
  have hSupper : ∀ i j : Fin n, j.val < i.val → S i j = 0 := by
    intro i j hij
    unfold S rectMatMul
    apply Finset.sum_eq_zero
    intro k _
    by_cases hki : k.val < i.val
    · rw [hR.R_upper i k hki, zero_mul]
    · have hjk : j.val < k.val := by omega
      rw [hRhatInvUpper k j hjk, mul_zero]
  have hSdiagEntry : ∀ i : Fin n,
      S i i = R i i * RhatInv i i := by
    intro i
    unfold S rectMatMul
    rw [Finset.sum_eq_single i]
    · intro k _ hki
      by_cases hlt : k.val < i.val
      · rw [hR.R_upper i k hlt, zero_mul]
      · have hgt : i.val < k.val := by
          have hne : k.val ≠ i.val := by
            intro h
            exact hki (Fin.ext h)
          omega
        rw [hRhatInvUpper k i hgt, mul_zero]
    · simp
  have hSdiag : ∀ i : Fin n, 0 < S i i := by
    intro i
    rw [hSdiagEntry i, hRhatInvDiag i]
    exact mul_pos (hR.R_diag_pos i) (one_div_pos.mpr (hRhat.R_diag_pos i))
  let T : Fin n → Fin n → ℝ :=
    nonsingInv n (finiteTranspose S)
  have hSTlower : ∀ i j : Fin n,
      i.val < j.val → finiteTranspose S i j = 0 := by
    intro i j hij
    exact hSupper j i hij
  have hSTdiag : ∀ i : Fin n, finiteTranspose S i i ≠ 0 := by
    intro i
    exact ne_of_gt (hSdiag i)
  have hSTdet :
      Matrix.det
        (finiteTranspose S : Matrix (Fin n) (Fin n) ℝ) ≠ 0 :=
    det_ne_zero_of_lower_triangular_diag_ne_zero n
      (finiteTranspose S) hSTlower hSTdiag
  have hTinv : IsInverse n (finiteTranspose S) T := by
    exact isInverse_nonsingInv_of_det_ne_zero n (finiteTranspose S) hSTdet
  have hRprod : rectMatMul (finiteTranspose R) R = A := by
    ext i j
    exact hR.product_eq i j
  have hRhatProd :
      rectMatMul (finiteTranspose Rhat) Rhat =
        (fun i j : Fin n => A i j + DeltaA i j) := by
    ext i j
    exact hRhat.product_eq i j
  have hRhatInvLeft : rectMatMul RhatInv Rhat = idMatrix n := by
    ext i j
    exact hRhatInv.1 i j
  have hRhatInvRight : rectMatMul Rhat RhatInv = idMatrix n := by
    ext i j
    exact hRhatInv.2 i j
  have hTransInvLeft :
      rectMatMul (finiteTranspose RhatInv) (finiteTranspose Rhat) =
        idMatrix n := by
    ext i j
    exact
      (isLeftInverse_finiteTranspose_of_isRightInverse hRhatInv.2) i j
  have hTransposeS :
      finiteTranspose S =
        rectMatMul (finiteTranspose RhatInv) (finiteTranspose R) := by
    ext i j
    unfold S finiteTranspose rectMatMul
    apply Finset.sum_congr rfl
    intro k _
    ring
  have hSGramBase :
      rectMatMul (finiteTranspose S) S =
        rectMatMul (finiteTranspose RhatInv)
          (rectMatMul A RhatInv) := by
    calc
      rectMatMul (finiteTranspose S) S =
          rectMatMul
            (rectMatMul (finiteTranspose RhatInv) (finiteTranspose R))
            (rectMatMul R RhatInv) := by rw [hTransposeS]
      _ = rectMatMul (finiteTranspose RhatInv)
            (rectMatMul (finiteTranspose R) (rectMatMul R RhatInv)) := by
              rw [rectMatMul_assoc]
      _ = rectMatMul (finiteTranspose RhatInv)
            (rectMatMul (rectMatMul (finiteTranspose R) R) RhatInv) := by
              rw [rectMatMul_assoc (finiteTranspose R) R RhatInv]
      _ = rectMatMul (finiteTranspose RhatInv)
            (rectMatMul A RhatInv) := by rw [hRprod]
  have hFull :
      rectMatMul (finiteTranspose RhatInv)
          (rectMatMul (fun i j : Fin n => A i j + DeltaA i j) RhatInv) =
        idMatrix n := by
    calc
      rectMatMul (finiteTranspose RhatInv)
          (rectMatMul (fun i j : Fin n => A i j + DeltaA i j) RhatInv) =
          rectMatMul (finiteTranspose RhatInv)
            (rectMatMul (rectMatMul (finiteTranspose Rhat) Rhat) RhatInv) := by
              rw [hRhatProd]
      _ = rectMatMul (finiteTranspose RhatInv)
            (rectMatMul (finiteTranspose Rhat)
              (rectMatMul Rhat RhatInv)) := by
              rw [rectMatMul_assoc (finiteTranspose Rhat) Rhat RhatInv]
      _ = rectMatMul
            (rectMatMul (finiteTranspose RhatInv) (finiteTranspose Rhat))
            (rectMatMul Rhat RhatInv) := by
              rw [rectMatMul_assoc]
      _ = rectMatMul (idMatrix n) (idMatrix n) := by
              rw [hTransInvLeft, hRhatInvRight]
      _ = idMatrix n := rectMatMul_id_left (idMatrix n)
  have hSplit :
      rectMatMul (finiteTranspose RhatInv)
          (rectMatMul (fun i j : Fin n => A i j + DeltaA i j) RhatInv) =
        (fun i j : Fin n =>
          rectMatMul (finiteTranspose RhatInv) (rectMatMul A RhatInv) i j +
            higham10_8_Gtilde RhatInv DeltaA i j) := by
    rw [rectMatMul_add_left, rectMatMul_add_right]
    rfl
  have hGram :
      rectMatMul (finiteTranspose S) S =
        matSub_id n (higham10_8_Gtilde RhatInv DeltaA) := by
    ext i j
    have hbase := congrFun (congrFun hSGramBase i) j
    have hfull := congrFun (congrFun hFull i) j
    have hsplit := congrFun (congrFun hSplit i) j
    unfold matSub_id
    linarith
  have hSRhat : rectMatMul S Rhat = R := by
    calc
      rectMatMul S Rhat = rectMatMul (rectMatMul R RhatInv) Rhat := rfl
      _ = rectMatMul R (rectMatMul RhatInv Rhat) :=
            rectMatMul_assoc R RhatInv Rhat
      _ = rectMatMul R (idMatrix n) := by rw [hRhatInvLeft]
      _ = R := rectMatMul_id_right R
  have hDeltaNormalized :
      (fun i j : Fin n => Rhat i j - R i j) =
        rectMatMul (fun i j : Fin n => idMatrix n i j - S i j) Rhat := by
    rw [rectMatMul_sub_left, rectMatMul_id_left, hSRhat]
  exact
    higham10_8_componentwise_source_of_normalized_certificate hn
      Rhat RhatInv DeltaA (fun i j : Fin n => Rhat i j - R i j) S T
      hDeltaSym hSupper hSdiag hTinv hGram hDeltaNormalized hrho

/-- Canonical-inverse form of the printed componentwise clause.  The inverse
of `Rhat` is constructed from its positive upper-triangular Cholesky
certificate, so the hypotheses are exactly the two factorizations and the
source spectral-radius contraction. -/
theorem higham10_8_componentwise_source_nonsingInv {n : ℕ}
    (hn : 0 < n)
    (A R Rhat DeltaA : Fin n → Fin n → ℝ)
    (hR : CholeskyFactSpec n A R)
    (hRhat : CholeskyFactSpec n
      (fun i j : Fin n => A i j + DeltaA i j) Rhat)
    (hrho :
      spectralRadius ℂ
        (Matrix.toLin'
          (show Matrix (Fin n) (Fin n) ℂ from
            realRectToCMatrix
              (absMatrix n
                (higham10_8_Gtilde (nonsingInv n Rhat) DeltaA)))) < 1) :
    ∀ i j : Fin n,
      |Rhat i j - R i j| ≤
        rectMatMul
          (higham10_8_componentwiseEnvelope
            (higham10_8_Gtilde (nonsingInv n Rhat) DeltaA))
          (absMatrix n Rhat) i j := by
  have hdet : Matrix.det (Rhat : Matrix (Fin n) (Fin n) ℝ) ≠ 0 :=
    det_ne_zero_of_upper_triangular_diag_ne_zero n Rhat hRhat.R_upper
      (fun i => ne_of_gt (hRhat.R_diag_pos i))
  have hInv : IsInverse n Rhat (nonsingInv n Rhat) :=
    isInverse_nonsingInv_of_det_ne_zero n Rhat hdet
  exact higham10_8_componentwise_source hn A R Rhat
    (nonsingInv n Rhat) DeltaA hR hRhat hInv hrho

end

end NumStability
