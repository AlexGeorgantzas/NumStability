import NumStability.Algorithms.HighamChapter9Theorem914Actual

/-!
# Higham Theorem 9.14: diagonally-dominant actual-recurrence closure

This module derives a source-only small-unit-roundoff growth bound for the
actual primitive tridiagonal recurrence.  It does not assume a growth bound
on the computed factors.
-/

namespace NumStability

open scoped BigOperators

/-- A nonsingular row- or column-diagonally-dominant tridiagonal source has a
positive unit-roundoff threshold below which the actual primitive recurrence
does not break down and its computed bidiagonal factors satisfy the explicit
componentwise bound `|Lhat||Uhat| ≤ 16|A|`.

The constant 16 is intentionally conservative.  It follows from exact
three-growth, a finite positive floor for the source diagonals and exact
pivots, and the primitive forward-relative division law. -/
theorem higham9_14_exists_threshold_actual_diagDominant_growth_bound_16
    {n : ℕ} (hn : 0 < n) (T : TridiagData n)
    (hdet : Matrix.det
      (Matrix.of (tridiag_to_matrix T) : Matrix (Fin n) (Fin n) ℝ) ≠ 0)
    (hdom : IsRowDiagDominant n (tridiag_to_matrix T) ∨
      IsDiagDominant n (tridiag_to_matrix T)) :
    ∃ epsilon : ℝ, 0 < epsilon ∧ epsilon ≤ (1 : ℝ) / 2 ∧
      ∀ fp : FPModel, fp.u < epsilon →
        (∀ i : Fin n, higham9_14_roundedPivotVec fp T i ≠ 0) ∧
        ∀ i j : Fin n,
          (∑ k : Fin n,
            |tridiag_L_matrix
                (higham9_14_roundedMultiplierVec fp T) i k| *
              |tridiag_U_matrix
                (higham9_14_roundedPivotVec fp T) T.c k j|) ≤
            16 * |tridiag_to_matrix T i j| := by
  have hpivot : ∀ i : Fin n, higham9_14_exactPivotVec T i ≠ 0 :=
    hdom.elim
      (higham9_14_exactPivotVec_ne_zero_of_rowDiagDominant T hdet)
      (higham9_14_exactPivotVec_ne_zero_of_colDiagDominant T hdet)
  have hdiag_ne : ∀ i : Fin n, T.d i ≠ 0 := by
    intro i
    have hAii : tridiag_to_matrix T i i = T.d i := by
      simp [tridiag_to_matrix]
    rw [← hAii]
    exact hdom.elim
      (fun hrow =>
        (higham9_9_rowDiagDominant_diag_ne_zero_of_det_ne_zero hrow hdet) i)
      (fun hcol =>
        (higham9_9_colDiagDominant_diag_ne_zero_of_det_ne_zero hcol hdet) i)
  let gaps : Finset ℝ :=
    (Finset.univ : Finset (Fin n)).image
      (fun i => min |T.d i| (|higham9_14_exactPivotVec T i| / 2))
  have hgaps : gaps.Nonempty := by
    let i0 : Fin n := ⟨0, hn⟩
    refine ⟨min |T.d i0| (|higham9_14_exactPivotVec T i0| / 2), ?_⟩
    exact Finset.mem_image.mpr ⟨i0, Finset.mem_univ i0, rfl⟩
  let eta : ℝ := gaps.min' hgaps
  have heta : 0 < eta := by
    have hmem : gaps.min' hgaps ∈ gaps := Finset.min'_mem gaps hgaps
    obtain ⟨i, _hi, hi⟩ := Finset.mem_image.mp hmem
    have hdpos : 0 < |T.d i| := abs_pos.mpr (hdiag_ne i)
    have hppos : 0 < |higham9_14_exactPivotVec T i| / 2 :=
      div_pos (abs_pos.mpr (hpivot i)) (by norm_num)
    simpa [eta, hi] using lt_min hdpos hppos
  have heta_diag : ∀ i : Fin n, eta ≤ |T.d i| := by
    intro i
    exact (Finset.min'_le gaps _
      (Finset.mem_image.mpr ⟨i, Finset.mem_univ i, rfl⟩)).trans
        (min_le_left _ _)
  have heta_pivot : ∀ i : Fin n,
      eta ≤ |higham9_14_exactPivotVec T i| / 2 := by
    intro i
    exact (Finset.min'_le gaps _
      (Finset.mem_image.mpr ⟨i, Finset.mem_univ i, rfl⟩)).trans
        (min_le_right _ _)
  let N := n - 1
  have hpivot_nat : ∀ k : ℕ, k ≤ N →
      higham9_14_exactPivot
        (higham9_14_natExtension T.a)
        (higham9_14_natExtension T.d)
        (higham9_14_natExtension T.c) k ≠ 0 := by
    intro k hk
    have hkn : k < n := by
      dsimp [N] at hk
      omega
    exact hpivot ⟨k, hkn⟩
  obtain ⟨epsilon₀, hepsilon₀, hthreshold⟩ :=
    higham9_14_exists_unitRoundoff_threshold_of_exact_pivots_ne_zero_with_tolerance
      (higham9_14_natExtension T.a)
      (higham9_14_natExtension T.d)
      (higham9_14_natExtension T.c) N hpivot_nat heta
  let epsilon := min epsilon₀ ((1 : ℝ) / 2)
  have hepsilon : 0 < epsilon := lt_min hepsilon₀ (by norm_num)
  refine ⟨epsilon, hepsilon, min_le_right _ _, ?_⟩
  intro fp hfp
  have hfp₀ : fp.u < epsilon₀ := hfp.trans_le (min_le_left _ _)
  have hu_half : fp.u < (1 : ℝ) / 2 := hfp.trans_le (min_le_right _ _)
  have hu1 : fp.u < 1 := by linarith
  have hclose : ∀ i : Fin n,
      |higham9_14_roundedPivotVec fp T i -
        higham9_14_exactPivotVec T i| < eta ∧
      0 < higham9_14_roundedPivotVec fp T i *
        higham9_14_exactPivotVec T i := by
    intro i
    have hiN : i.val ≤ N := by
      dsimp [N]
      omega
    simpa [higham9_14_roundedPivotVec, higham9_14_exactPivotVec] using
      hthreshold fp hfp₀ i.val hiN
  have hpivot_hat : ∀ i : Fin n,
      higham9_14_roundedPivotVec fp T i ≠ 0 := by
    intro i
    exact (mul_ne_zero_iff.mp (ne_of_gt (hclose i).2)).1
  refine ⟨hpivot_hat, ?_⟩
  let L0 := tridiag_L_matrix
    (higham9_14_roundedMultiplierVec higham9_14_exactFPModel T)
  let U0 := tridiag_U_matrix
    (higham9_14_roundedPivotVec higham9_14_exactFPModel T) T.c
  have hLU0 : LUFactSpec n (tridiag_to_matrix T) L0 U0 := by
    exact higham9_14_exactFP_LUFactSpec T hpivot
  have hgrowth0 : ∀ i j : Fin n,
      (∑ k : Fin n, |L0 i k| * |U0 k j|) ≤
        3 * |tridiag_to_matrix T i j| := by
    intro i j
    exact hdom.elim
      (fun hrow =>
        higham9_13_rowDiagDom_tridiag_growth_bound_3_of_LUFactSpec
          (tridiag_to_matrix T) L0 U0 hLU0 hdet
          (tridiag_to_matrix_isTridiagonal T) hrow i j)
      (fun hcol =>
        higham9_13_colDiagDom_tridiag_growth_bound_3_of_LUFactSpec
          (tridiag_to_matrix T) L0 U0 hLU0 hdet
          (tridiag_to_matrix_isTridiagonal T) hcol i j)
  let Lhat := tridiag_L_matrix
    (higham9_14_roundedMultiplierVec fp T)
  let Uhat := tridiag_U_matrix
    (higham9_14_roundedPivotVec fp T) T.c
  let P := tridiag_to_matrix (higham9_14_roundedProductData fp T)
  have hStructHat : IsTridiagLU n Lhat Uhat :=
    tridiag_matrices_isTridiagLU _ _ _
  have hLUhat : ∀ r s : Fin n,
      ∑ k : Fin n, Lhat r k * Uhat k s = P r s := by
    intro r s
    simpa [Lhat, Uhat, P, higham9_14_roundedProductData] using
      tridiag_exact_product_of_recurrence
        (higham9_14_roundedProductData fp T)
        (higham9_14_roundedMultiplierVec fp T)
        (higham9_14_roundedPivotVec fp T)
        (higham9_14_roundedProductData_recurrence fp T) r s
  intro i j
  by_cases hdiag : i = j
  · subst j
    have hp_exact_bound : |higham9_14_exactPivotVec T i| ≤
        3 * |T.d i| := by
      have hsingle : |L0 i i| * |U0 i i| ≤
          ∑ k : Fin n, |L0 i k| * |U0 k i| :=
        Finset.single_le_sum
          (f := fun k : Fin n => |L0 i k| * |U0 k i|)
          (fun k _ => mul_nonneg (abs_nonneg _) (abs_nonneg _))
          (Finset.mem_univ i)
      calc
        |higham9_14_exactPivotVec T i| ≤
            ∑ k : Fin n, |L0 i k| * |U0 k i| := by
          simpa [L0, U0, tridiag_L_matrix, tridiag_U_matrix] using hsingle
        _ ≤ 3 * |tridiag_to_matrix T i i| := hgrowth0 i i
        _ = 3 * |T.d i| := by simp [tridiag_to_matrix]
    have hp_hat_bound : |higham9_14_roundedPivotVec fp T i| ≤
        4 * |T.d i| := by
      have htri : |higham9_14_roundedPivotVec fp T i| ≤
          |higham9_14_exactPivotVec T i| +
            |higham9_14_roundedPivotVec fp T i -
              higham9_14_exactPivotVec T i| := by
        have heq : higham9_14_roundedPivotVec fp T i =
            higham9_14_exactPivotVec T i +
              (higham9_14_roundedPivotVec fp T i -
                higham9_14_exactPivotVec T i) := by ring
        calc
          |higham9_14_roundedPivotVec fp T i| =
              |higham9_14_exactPivotVec T i +
                (higham9_14_roundedPivotVec fp T i -
                  higham9_14_exactPivotVec T i)| := congrArg abs heq
          _ ≤ |higham9_14_exactPivotVec T i| +
              |higham9_14_roundedPivotVec fp T i -
                higham9_14_exactPivotVec T i| := abs_add_le _ _
      have herr := (hclose i).1
      have heta_i := heta_diag i
      linarith
    rw [higham9_14_absLU_diag_sum Lhat Uhat hStructHat i]
    by_cases hi : 0 < i.val
    · let im1 := tridiag_prevIndex i hi
      have him1 : im1.val + 1 = i.val := by
        simp [im1, tridiag_prevIndex]
        omega
      have him1_eq : (⟨i.val - 1, by omega⟩ : Fin n) = im1 := by
        apply Fin.ext
        simp [im1, tridiag_prevIndex]
      have hlexact_bound :
          |higham9_14_exactMultiplierVec T i| * |T.c im1| ≤
            3 * |T.d i| := by
        have hsingle : |L0 i im1| * |U0 im1 i| ≤
            ∑ k : Fin n, |L0 i k| * |U0 k i| :=
          Finset.single_le_sum
            (f := fun k : Fin n => |L0 i k| * |U0 k i|)
            (fun k _ => mul_nonneg (abs_nonneg _) (abs_nonneg _))
            (Finset.mem_univ im1)
        have hLentry : L0 i im1 = higham9_14_exactMultiplierVec T i := by
          simp [L0, tridiag_L_matrix, him1,
            show im1.val ≠ i.val by omega]
        have hUentry : U0 im1 i = T.c im1 := by
          simp [U0, tridiag_U_matrix, him1,
            show i.val ≠ im1.val by omega]
        calc
          |higham9_14_exactMultiplierVec T i| * |T.c im1| ≤
              ∑ k : Fin n, |L0 i k| * |U0 k i| := by
            simpa [hLentry, hUentry] using hsingle
          _ ≤ 3 * |tridiag_to_matrix T i i| := hgrowth0 i i
          _ = 3 * |T.d i| := by simp [tridiag_to_matrix]
      have him1close :
          |higham9_14_roundedPivotVec fp T im1 -
            higham9_14_exactPivotVec T im1| <
              |higham9_14_exactPivotVec T im1| / 2 :=
        (hclose im1).1.trans_le (heta_pivot im1)
      have hlhat_bound :
          |higham9_14_roundedMultiplierVec fp T i| * |T.c im1| ≤
            12 * |T.d i| := by
        have hfour := higham9_14_fl_div_mul_abs_le_four_exact fp
          (hpivot im1) (hpivot_hat im1) him1close hu1
          (a := T.a i) (c := T.c im1)
        calc
          |higham9_14_roundedMultiplierVec fp T i| * |T.c im1| =
              |higham9_14_roundedMultiplierVec fp T i * T.c im1| :=
            (abs_mul _ _).symm
          _ ≤ 4 * |higham9_14_exactMultiplierVec T i * T.c im1| := by
            simpa [higham9_14_roundedMultiplierVec_of_pos fp T i hi,
              higham9_14_exactMultiplierVec_of_pos T i hi] using hfour
          _ = 4 * (|higham9_14_exactMultiplierVec T i| * |T.c im1|) := by
            rw [abs_mul]
          _ ≤ 12 * |T.d i| := by
            nlinarith [hlexact_bound, abs_nonneg (T.d i)]
      have hlocal :
          |higham9_14_roundedPivotVec fp T i| +
              |higham9_14_roundedMultiplierVec fp T i| * |T.c im1| ≤
            16 * |T.d i| := by linarith
      rw [dif_pos hi, him1_eq]
      have hUii : Uhat i i = higham9_14_roundedPivotVec fp T i := by
        simp [Uhat, tridiag_U_matrix]
      have hLim1 : Lhat i im1 =
          higham9_14_roundedMultiplierVec fp T i := by
        simp [Lhat, tridiag_L_matrix, him1,
          show im1.val ≠ i.val by omega]
      have hUim1i : Uhat im1 i = T.c im1 := by
        simp [Uhat, tridiag_U_matrix, him1,
          show i.val ≠ im1.val by omega]
      have hAii : tridiag_to_matrix T i i = T.d i := by
        simp [tridiag_to_matrix]
      rw [hUii, hLim1, hUim1i, hAii]
      exact hlocal
    · have hlocal : |higham9_14_roundedPivotVec fp T i| ≤
          16 * |T.d i| := by
        linarith [abs_nonneg (T.d i)]
      rw [dif_neg hi]
      have hUii : Uhat i i = higham9_14_roundedPivotVec fp T i := by
        simp [Uhat, tridiag_U_matrix]
      have hAii : tridiag_to_matrix T i i = T.d i := by
        simp [tridiag_to_matrix]
      rw [hUii, hAii, add_zero]
      exact hlocal
  · by_cases hfar : i.val + 1 < j.val ∨ j.val + 1 < i.val
    · rw [tridiag_bidiag_absLU_sparse Lhat Uhat hStructHat i j hfar]
      positivity
    · push_neg at hfar
      by_cases hsub : j.val + 1 = i.val
      · have hle := tridiag_bidiag_growth_offdiag_sub
          Lhat Uhat P hStructHat hLUhat i j hsub
        have hi : 0 < i.val := by omega
        have him1 : tridiag_prevIndex i hi = j := by
          apply Fin.ext
          simp [tridiag_prevIndex]
          omega
        have hscalar := higham9_14_fl_div_mul_den_abs_le_two fp
          (hpivot_hat j) hu1 (a := T.a i)
          (p := higham9_14_roundedPivotVec fp T j)
        have hP : P i j =
            higham9_14_roundedMultiplierVec fp T i *
              higham9_14_roundedPivotVec fp T j := by
          simp [P, tridiag_to_matrix, higham9_14_roundedProductData,
            hi, hsub, him1, show j.val ≠ i.val by omega,
            show i.val + 1 ≠ j.val by omega]
        have hA : tridiag_to_matrix T i j = T.a i := by
          simp [tridiag_to_matrix, hsub,
            show j.val ≠ i.val by omega,
            show i.val + 1 ≠ j.val by omega]
        rw [hP] at hle
        rw [higham9_14_roundedMultiplierVec_of_pos fp T i hi, him1] at hle
        rw [hA]
        exact hle.trans (hscalar.trans (by
          nlinarith [abs_nonneg (T.a i)]))
      · have hsuper : i.val + 1 = j.val := by omega
        have hle := tridiag_bidiag_growth_offdiag_super
          Lhat Uhat P hStructHat hLUhat i j hsuper
        have hP : P i j = T.c i := by
          simp [P, tridiag_to_matrix, higham9_14_roundedProductData,
            hsuper, show j.val ≠ i.val by omega,
            show j.val + 1 ≠ i.val by omega]
        have hA : tridiag_to_matrix T i j = T.c i := by
          simp [tridiag_to_matrix, hsuper,
            show j.val ≠ i.val by omega,
            show j.val + 1 ≠ i.val by omega]
        rw [hP] at hle
        rw [hA]
        exact hle.trans (by nlinarith [abs_nonneg (T.c i)])

/-- Source-only corrected diagonally-dominant clause of Theorem 9.14 for the
actual primitive recurrence.  Under sufficiently small unit roundoff it
produces the computed solve and a componentwise backward error bounded by
`16 * h(u/(1-u)) * |A|`.  The factor 16 replaces the printed factor 3 because
the repository's bare forward-relative model permits adversarial primitive
roundings; no computed-factor growth premise appears. -/
theorem higham9_14_exists_threshold_actual_source_sixteen_h_corrected_of_diagDominant
    {n : ℕ} (hn : 0 < n) (T : TridiagData n) (b : Fin n → ℝ)
    (hdet : Matrix.det
      (Matrix.of (tridiag_to_matrix T) : Matrix (Fin n) (Fin n) ℝ) ≠ 0)
    (hdom : IsRowDiagDominant n (tridiag_to_matrix T) ∨
      IsDiagDominant n (tridiag_to_matrix T)) :
    ∃ epsilon : ℝ, 0 < epsilon ∧
      ∀ fp : FPModel, fp.u < epsilon →
        ∃ DeltaA : Fin n → Fin n → ℝ,
          (∀ i j, |DeltaA i j| ≤
            16 * higham9_14_h (fp.u / (1 - fp.u)) *
              |tridiag_to_matrix T i j|) ∧
          (∀ i,
            ∑ j : Fin n, (tridiag_to_matrix T i j + DeltaA i j) *
              higham9_21_upperSolve fp
                (higham9_14_roundedPivotVec fp T) T.c
                (higham9_21_lowerSolve fp
                  (higham9_14_roundedMultiplierVec fp T) b) j = b i) := by
  obtain ⟨epsilon, hepsilon, hepsilon_half, hthreshold⟩ :=
    higham9_14_exists_threshold_actual_diagDominant_growth_bound_16
      hn T hdet hdom
  refine ⟨epsilon, hepsilon, ?_⟩
  intro fp hfp
  obtain ⟨hpivot, hgrowth⟩ := hthreshold fp hfp
  have hu_half : fp.u < (1 : ℝ) / 2 := hfp.trans_le hepsilon_half
  exact higham9_14_actual_tridiag_source_scaled_h_bound_corrected_of_growth
    fp T b 16 (by norm_num) hu_half hpivot hgrowth

end NumStability
