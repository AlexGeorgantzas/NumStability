import NumStability.Algorithms.HighamChapter9Theorem914Primitive

/-!
# Higham Theorem 9.14: actual tridiagonal factorization bridge

This module connects the primitive scalar recurrence used by the proof of
Theorem 9.14 to finite `TridiagData` and its bidiagonal matrix builders.  The
computed factors are the actual outputs of `fl_div`, `fl_mul`, and `fl_sub`;
they are never identified with an exact LU factorization of the source.

The repository's `FPModel` is a forward-relative model.  Consequently the
honest equation-(9.20) coefficient is `u / (1-u)`, as proved at the scalar
level in `HighamChapter9Theorem914Primitive`.
-/

namespace NumStability

open scoped BigOperators

/-- Extend a finite tridiagonal data vector by zero to a natural-indexed
sequence, so it can be consumed by the primitive recurrence. -/
noncomputable def higham9_14_natExtension {n : ℕ} (v : Fin n → ℝ) : ℕ → ℝ :=
  fun k => if hk : k < n then v ⟨k, hk⟩ else 0

@[simp] theorem higham9_14_natExtension_fin {n : ℕ}
    (v : Fin n → ℝ) (i : Fin n) :
    higham9_14_natExtension v i.val = v i := by
  simp [higham9_14_natExtension]

/-- Exact scalar pivots associated with finite tridiagonal source data. -/
noncomputable def higham9_14_exactPivotVec {n : ℕ}
    (T : TridiagData n) (i : Fin n) : ℝ :=
  higham9_14_exactPivot
    (higham9_14_natExtension T.a)
    (higham9_14_natExtension T.d)
    (higham9_14_natExtension T.c) i.val

/-- Actual rounded scalar pivots associated with finite tridiagonal data. -/
noncomputable def higham9_14_roundedPivotVec (fp : FPModel) {n : ℕ}
    (T : TridiagData n) (i : Fin n) : ℝ :=
  higham9_14_roundedPivot fp
    (higham9_14_natExtension T.a)
    (higham9_14_natExtension T.d)
    (higham9_14_natExtension T.c) i.val

/-- Actual rounded multipliers associated with finite tridiagonal data. -/
noncomputable def higham9_14_roundedMultiplierVec (fp : FPModel) {n : ℕ}
    (T : TridiagData n) (i : Fin n) : ℝ :=
  higham9_14_roundedMultiplier fp
    (higham9_14_natExtension T.a)
    (higham9_14_natExtension T.d)
    (higham9_14_natExtension T.c) i.val

/-- Exact finite multiplier vector paired with `higham9_14_exactPivotVec`. -/
noncomputable def higham9_14_exactMultiplierVec {n : ℕ}
    (T : TridiagData n) (i : Fin n) : ℝ :=
  higham9_14_exactMultiplier
    (higham9_14_natExtension T.a)
    (higham9_14_natExtension T.d)
    (higham9_14_natExtension T.c) i.val

/-- Exact arithmetic as a zero-unit-roundoff instance of the repository's
primitive model. -/
noncomputable def higham9_14_exactFPModel : FPModel :=
  FPModel.exactWithUnitRoundoff 0 (by norm_num)

/-- Under the exact primitive model, the actual rounded pivot recurrence is
definitionally the exact recurrence. -/
theorem higham9_14_roundedPivot_exactFPModel_eq
    (a d c : ℕ → ℝ) : ∀ k : ℕ,
    higham9_14_roundedPivot higham9_14_exactFPModel a d c k =
      higham9_14_exactPivot a d c k := by
  intro k
  induction k with
  | zero => rfl
  | succ k ih =>
      rw [higham9_14_roundedPivot_succ, higham9_14_exactPivot_succ]
      change d (k + 1) -
          (a (k + 1) /
            higham9_14_roundedPivot higham9_14_exactFPModel a d c k) * c k =
        d (k + 1) -
          (a (k + 1) / higham9_14_exactPivot a d c k) * c k
      rw [ih]

/-- The same exact-model identity for the multiplier recurrence. -/
theorem higham9_14_roundedMultiplier_exactFPModel_eq
    (a d c : ℕ → ℝ) : ∀ k : ℕ,
    higham9_14_roundedMultiplier higham9_14_exactFPModel a d c k =
      higham9_14_exactMultiplier a d c k := by
  intro k
  cases k with
  | zero => rfl
  | succ k =>
      change a (k + 1) /
          higham9_14_roundedPivot higham9_14_exactFPModel a d c k =
        a (k + 1) / higham9_14_exactPivot a d c k
      rw [higham9_14_roundedPivot_exactFPModel_eq]

@[simp] theorem higham9_14_roundedPivotVec_exactFPModel_eq {n : ℕ}
    (T : TridiagData n) (i : Fin n) :
    higham9_14_roundedPivotVec higham9_14_exactFPModel T i =
      higham9_14_exactPivotVec T i := by
  exact higham9_14_roundedPivot_exactFPModel_eq _ _ _ i.val

@[simp] theorem higham9_14_roundedMultiplierVec_exactFPModel_eq {n : ℕ}
    (T : TridiagData n) (i : Fin n) :
    higham9_14_roundedMultiplierVec higham9_14_exactFPModel T i =
      higham9_14_exactMultiplierVec T i := by
  exact higham9_14_roundedMultiplier_exactFPModel_eq _ _ _ i.val

theorem higham9_14_exactMultiplierVec_of_pos {n : ℕ}
    (T : TridiagData n) (i : Fin n) (hi : 0 < i.val) :
    higham9_14_exactMultiplierVec T i =
      T.a i / higham9_14_exactPivotVec T (tridiag_prevIndex i hi) := by
  have hsucc : i.val = (i.val - 1) + 1 := by omega
  unfold higham9_14_exactMultiplierVec higham9_14_exactPivotVec
  rw [hsucc]
  simp only [higham9_14_exactMultiplier]
  have ha : higham9_14_natExtension T.a (i.val - 1 + 1) = T.a i := by
    rw [← hsucc]
    exact higham9_14_natExtension_fin T.a i
  rw [ha]
  rfl

theorem higham9_14_exactPivotVec_of_pos {n : ℕ}
    (T : TridiagData n) (i : Fin n) (hi : 0 < i.val) :
    higham9_14_exactPivotVec T i = T.d i -
      higham9_14_exactMultiplierVec T i *
        T.c (tridiag_prevIndex i hi) := by
  have hsucc : i.val = (i.val - 1) + 1 := by omega
  unfold higham9_14_exactPivotVec higham9_14_exactMultiplierVec
  rw [hsucc]
  simp only [higham9_14_exactPivot, higham9_14_exactMultiplier]
  have hd : higham9_14_natExtension T.d (i.val - 1 + 1) = T.d i := by
    rw [← hsucc]
    exact higham9_14_natExtension_fin T.d i
  have hc : higham9_14_natExtension T.c (i.val - 1) =
      T.c (tridiag_prevIndex i hi) := by
    change higham9_14_natExtension T.c (tridiag_prevIndex i hi).val =
      T.c (tridiag_prevIndex i hi)
    exact higham9_14_natExtension_fin T.c (tridiag_prevIndex i hi)
  rw [hd, hc]

@[simp] theorem higham9_14_roundedPivotVec_zero (fp : FPModel) {n : ℕ}
    (T : TridiagData n) (i : Fin n) (hi : i.val = 0) :
    higham9_14_roundedPivotVec fp T i = T.d i := by
  have hi' : i = ⟨0, by omega⟩ := Fin.ext hi
  rw [hi']
  simpa [higham9_14_roundedPivotVec] using
    higham9_14_natExtension_fin T.d (⟨0, by omega⟩ : Fin n)

theorem higham9_14_roundedMultiplierVec_of_pos (fp : FPModel) {n : ℕ}
    (T : TridiagData n) (i : Fin n) (hi : 0 < i.val) :
    higham9_14_roundedMultiplierVec fp T i =
      fp.fl_div (T.a i)
        (higham9_14_roundedPivotVec fp T (tridiag_prevIndex i hi)) := by
  have hsucc : i.val = (i.val - 1) + 1 := by omega
  unfold higham9_14_roundedMultiplierVec higham9_14_roundedPivotVec
  rw [hsucc]
  simp only [higham9_14_roundedMultiplier]
  have ha : higham9_14_natExtension T.a (i.val - 1 + 1) = T.a i := by
    rw [← hsucc]
    exact higham9_14_natExtension_fin T.a i
  rw [ha]
  rfl

theorem higham9_14_roundedPivotVec_of_pos (fp : FPModel) {n : ℕ}
    (T : TridiagData n) (i : Fin n) (hi : 0 < i.val) :
    higham9_14_roundedPivotVec fp T i =
      fp.fl_sub (T.d i)
        (fp.fl_mul (higham9_14_roundedMultiplierVec fp T i)
          (T.c (tridiag_prevIndex i hi))) := by
  have hsucc : i.val = (i.val - 1) + 1 := by omega
  unfold higham9_14_roundedPivotVec higham9_14_roundedMultiplierVec
  rw [hsucc]
  simp only [higham9_14_roundedPivot, higham9_14_roundedMultiplier]
  have hd : higham9_14_natExtension T.d (i.val - 1 + 1) = T.d i := by
    rw [← hsucc]
    exact higham9_14_natExtension_fin T.d i
  have hc : higham9_14_natExtension T.c (i.val - 1) =
      T.c (tridiag_prevIndex i hi) := by
    change higham9_14_natExtension T.c
        (tridiag_prevIndex i hi).val = T.c (tridiag_prevIndex i hi)
    exact higham9_14_natExtension_fin T.c (tridiag_prevIndex i hi)
  rw [hd, hc]

/-- The exact tridiagonal data whose exact bidiagonal product is formed by
the actual rounded multiplier and pivot vectors. -/
noncomputable def higham9_14_roundedProductData (fp : FPModel) {n : ℕ}
    (T : TridiagData n) : TridiagData n where
  a := fun i => if hi : 0 < i.val then
      higham9_14_roundedMultiplierVec fp T i *
        higham9_14_roundedPivotVec fp T (tridiag_prevIndex i hi)
    else T.a i
  d := fun i => if hi : 0 < i.val then
      higham9_14_roundedPivotVec fp T i +
        higham9_14_roundedMultiplierVec fp T i *
          T.c (tridiag_prevIndex i hi)
    else T.d i
  c := T.c

/-- The actual rounded vectors satisfy an exact recurrence for the nearby
data `higham9_14_roundedProductData`. -/
theorem higham9_14_roundedProductData_recurrence (fp : FPModel) {n : ℕ}
    (T : TridiagData n) :
    TridiagExactLURecurrence (higham9_14_roundedProductData fp T)
      (higham9_14_roundedMultiplierVec fp T)
      (higham9_14_roundedPivotVec fp T) := by
  refine ⟨?_, ?_, ?_⟩
  · intro i hi
    simp [higham9_14_roundedProductData, hi]
  · intro i hi
    simp [higham9_14_roundedProductData, hi]
  · intro i hi
    simp [higham9_14_roundedProductData, hi]

/-- Entrywise perturbation between the actual rounded factor product and the
source tridiagonal matrix. -/
noncomputable def higham9_14_actualFactorDelta (fp : FPModel) {n : ℕ}
    (T : TridiagData n) : Fin n → Fin n → ℝ :=
  fun i j =>
    tridiag_to_matrix (higham9_14_roundedProductData fp T) i j -
      tridiag_to_matrix T i j

/-- The actual rounded factor product is exactly the source plus the explicit
nearby-data perturbation. -/
theorem higham9_14_actualFactorDelta_product (fp : FPModel) {n : ℕ}
    (T : TridiagData n) :
    ∀ i j : Fin n,
      ∑ k : Fin n,
          tridiag_L_matrix (higham9_14_roundedMultiplierVec fp T) i k *
            tridiag_U_matrix (higham9_14_roundedPivotVec fp T) T.c k j =
        tridiag_to_matrix T i j + higham9_14_actualFactorDelta fp T i j := by
  intro i j
  calc
    ∑ k : Fin n,
          tridiag_L_matrix (higham9_14_roundedMultiplierVec fp T) i k *
            tridiag_U_matrix (higham9_14_roundedPivotVec fp T) T.c k j =
        tridiag_to_matrix (higham9_14_roundedProductData fp T) i j := by
          simpa [higham9_14_roundedProductData] using
            tridiag_exact_product_of_recurrence
              (higham9_14_roundedProductData fp T)
              (higham9_14_roundedMultiplierVec fp T)
              (higham9_14_roundedPivotVec fp T)
              (higham9_14_roundedProductData_recurrence fp T) i j
    _ = tridiag_to_matrix T i j + higham9_14_actualFactorDelta fp T i j := by
      simp [higham9_14_actualFactorDelta]

/-- Exact source product obtained by running the actual recurrence with exact
primitives.  This supplies a concrete no-pivot LU certificate rather than an
existential factorization unrelated to the recurrence. -/
theorem higham9_14_exactFP_product_eq_source {n : ℕ}
    (T : TridiagData n)
    (hpivot : ∀ i : Fin n, higham9_14_exactPivotVec T i ≠ 0) :
    ∀ i j : Fin n,
      ∑ k : Fin n,
          tridiag_L_matrix
              (higham9_14_roundedMultiplierVec higham9_14_exactFPModel T) i k *
            tridiag_U_matrix
              (higham9_14_roundedPivotVec higham9_14_exactFPModel T) T.c k j =
        tridiag_to_matrix T i j := by
  intro i j
  calc
    ∑ k : Fin n,
          tridiag_L_matrix
              (higham9_14_roundedMultiplierVec higham9_14_exactFPModel T) i k *
            tridiag_U_matrix
              (higham9_14_roundedPivotVec higham9_14_exactFPModel T) T.c k j =
        tridiag_to_matrix
          (higham9_14_roundedProductData higham9_14_exactFPModel T) i j := by
      simpa [higham9_14_roundedProductData] using
        tridiag_exact_product_of_recurrence
          (higham9_14_roundedProductData higham9_14_exactFPModel T)
          (higham9_14_roundedMultiplierVec higham9_14_exactFPModel T)
          (higham9_14_roundedPivotVec higham9_14_exactFPModel T)
          (higham9_14_roundedProductData_recurrence
            higham9_14_exactFPModel T) i j
    _ = tridiag_to_matrix T i j := by
      by_cases hdiag : j.val = i.val
      · have hji : j = i := Fin.ext hdiag
        subst j
        by_cases hi : 0 < i.val
        · have hrec := higham9_14_exactPivotVec_of_pos T i hi
          simp only [tridiag_to_matrix, hdiag, if_pos,
            higham9_14_roundedProductData,
            higham9_14_roundedPivotVec_exactFPModel_eq,
            higham9_14_roundedMultiplierVec_exactFPModel_eq]
          split <;> rename_i hsplit
          · linarith
          · exact (hsplit hi).elim
        · have hi0 : i.val = 0 := by omega
          simp [tridiag_to_matrix, higham9_14_roundedProductData, hi0]
      · by_cases hsub : j.val + 1 = i.val
        · have hi : 0 < i.val := by omega
          have hj : tridiag_prevIndex i hi = j := by
            ext
            simp [tridiag_prevIndex]
            omega
          subst j
          have hl := higham9_14_exactMultiplierVec_of_pos T i hi
          have hmul :
              higham9_14_exactMultiplierVec T i *
                  higham9_14_exactPivotVec T (tridiag_prevIndex i hi) =
                T.a i := by
            rw [hl, div_mul_cancel₀ _ (hpivot (tridiag_prevIndex i hi))]
          simp [tridiag_to_matrix, higham9_14_roundedProductData, hi,
            show (tridiag_prevIndex i hi).val ≠ i.val by
              simp [tridiag_prevIndex]; omega,
            show (tridiag_prevIndex i hi).val + 1 = i.val by
              simp [tridiag_prevIndex]; omega,
            hmul]
        · by_cases hsuper : i.val + 1 = j.val
          · simp [tridiag_to_matrix, higham9_14_roundedProductData,
              hdiag, hsub, hsuper]
          · simp [tridiag_to_matrix, higham9_14_roundedProductData,
              hdiag, hsub, hsuper]

/-- Concrete `LUFactSpec` packaged from the exact-primitive recurrence. -/
theorem higham9_14_exactFP_LUFactSpec {n : ℕ} (T : TridiagData n)
    (hpivot : ∀ i : Fin n, higham9_14_exactPivotVec T i ≠ 0) :
    LUFactSpec n (tridiag_to_matrix T)
      (tridiag_L_matrix
        (higham9_14_roundedMultiplierVec higham9_14_exactFPModel T))
      (tridiag_U_matrix
        (higham9_14_roundedPivotVec higham9_14_exactFPModel T) T.c) :=
  { L_diag := tridiag_L_diag _
    L_upper_zero := tridiag_L_upper_zero _
    U_lower_zero := tridiag_U_lower_zero _ _
    product_eq := higham9_14_exactFP_product_eq_source T hpivot }

private theorem higham9_14_actualFactor_abs_diag_le_sum (fp : FPModel)
    {n : ℕ} (T : TridiagData n) (i : Fin n) (hi : 0 < i.val) :
    |higham9_14_roundedPivotVec fp T i| +
        |higham9_14_roundedMultiplierVec fp T i *
          T.c (tridiag_prevIndex i hi)| ≤
      ∑ k : Fin n,
        |tridiag_L_matrix (higham9_14_roundedMultiplierVec fp T) i k| *
          |tridiag_U_matrix (higham9_14_roundedPivotVec fp T) T.c k i| := by
  classical
  let im1 : Fin n := tridiag_prevIndex i hi
  let f : Fin n → ℝ := fun k =>
    |tridiag_L_matrix (higham9_14_roundedMultiplierVec fp T) i k| *
      |tridiag_U_matrix (higham9_14_roundedPivotVec fp T) T.c k i|
  have hne : im1 ≠ i := by
    intro h
    have := congrArg Fin.val h
    simp [im1, tridiag_prevIndex] at this
    omega
  have hpair : (∑ k ∈ {im1, i}, f k) ≤ ∑ k : Fin n, f k := by
    apply Finset.sum_le_sum_of_subset_of_nonneg
    · simp
    · intro k _hk _hnot
      exact mul_nonneg (abs_nonneg _) (abs_nonneg _)
  have him1 : im1.val + 1 = i.val := by
    simp [im1, tridiag_prevIndex]
    omega
  have hpair_eq :
      (∑ k ∈ {im1, i}, f k) =
        |higham9_14_roundedMultiplierVec fp T i * T.c im1| +
          |higham9_14_roundedPivotVec fp T i| := by
    rw [Finset.sum_pair hne]
    simp [f, tridiag_L_matrix, tridiag_U_matrix, him1,
      show im1.val ≠ i.val by omega, show i.val ≠ im1.val by omega,
      abs_mul]
  rw [hpair_eq] at hpair
  simpa [im1, add_comm] using hpair

private theorem higham9_14_actualFactor_abs_sub_le_sum (fp : FPModel)
    {n : ℕ} (T : TridiagData n) (i : Fin n) (hi : 0 < i.val) :
    |higham9_14_roundedMultiplierVec fp T i *
        higham9_14_roundedPivotVec fp T (tridiag_prevIndex i hi)| ≤
      ∑ k : Fin n,
        |tridiag_L_matrix (higham9_14_roundedMultiplierVec fp T) i k| *
          |tridiag_U_matrix (higham9_14_roundedPivotVec fp T) T.c k
            (tridiag_prevIndex i hi)| := by
  classical
  let im1 : Fin n := tridiag_prevIndex i hi
  let f : Fin n → ℝ := fun k =>
    |tridiag_L_matrix (higham9_14_roundedMultiplierVec fp T) i k| *
      |tridiag_U_matrix (higham9_14_roundedPivotVec fp T) T.c k im1|
  have hsingle : f im1 ≤ ∑ k : Fin n, f k :=
    Finset.single_le_sum
      (fun k _ => mul_nonneg (abs_nonneg _) (abs_nonneg _))
      (Finset.mem_univ im1)
  have him1 : im1.val + 1 = i.val := by
    simp [im1, tridiag_prevIndex]
    omega
  have hterm : f im1 =
      |higham9_14_roundedMultiplierVec fp T i *
        higham9_14_roundedPivotVec fp T im1| := by
    simp [f, tridiag_L_matrix, tridiag_U_matrix, him1,
      show im1.val ≠ i.val by omega, abs_mul]
  rw [hterm] at hsingle
  simpa [im1] using hsingle

/-- Honest equation (9.20) for the *actual* primitive tridiagonal recurrence.

Under the repository's forward-relative `FPModel`, inversion of the division
law changes the coefficient from `u` to `u/(1-u)`.  No exact rounded-LU
identity, computed-factor sign, growth, or target comparison is assumed. -/
theorem higham9_20_actual_tridiag_lu_perturbation_model_corrected
    (fp : FPModel) {n : ℕ} (T : TridiagData n)
    (hu1 : fp.u < 1)
    (hpivot : ∀ i : Fin n,
      higham9_14_roundedPivotVec fp T i ≠ 0) :
    higham9_20_tridiag_lu_perturbation_model n
      (tridiag_to_matrix T)
      (tridiag_L_matrix (higham9_14_roundedMultiplierVec fp T))
      (tridiag_U_matrix (higham9_14_roundedPivotVec fp T) T.c)
      (higham9_14_actualFactorDelta fp T)
      (fp.u / (1 - fp.u)) := by
  refine ⟨higham9_14_actualFactorDelta_product fp T, ?_⟩
  have hbeta : 0 ≤ fp.u / (1 - fp.u) := by
    exact div_nonneg fp.u_nonneg (by linarith)
  intro i j
  by_cases hdiag : j.val = i.val
  · have hji : j = i := Fin.ext hdiag
    subst j
    by_cases hi : 0 < i.val
    · have hlocal :=
        higham9_20_primitive_diagonal_residual_corrected fp
          (higham9_14_roundedMultiplierVec fp T i) (T.d i)
          (T.c (tridiag_prevIndex i hi)) hu1
      rw [← higham9_14_roundedPivotVec_of_pos fp T i hi] at hlocal
      have hsum := higham9_14_actualFactor_abs_diag_le_sum fp T i hi
      have hscaled := mul_le_mul_of_nonneg_left hsum hbeta
      have hdelta : higham9_14_actualFactorDelta fp T i i =
          higham9_14_roundedPivotVec fp T i +
            higham9_14_roundedMultiplierVec fp T i *
              T.c (tridiag_prevIndex i hi) - T.d i := by
        simp [higham9_14_actualFactorDelta, tridiag_to_matrix,
          higham9_14_roundedProductData, hi]
      rw [hdelta]
      exact hlocal.trans hscaled
    · have hi0 : i.val = 0 := by omega
      have hzero : higham9_14_actualFactorDelta fp T i i = 0 := by
        simp [higham9_14_actualFactorDelta, tridiag_to_matrix,
          higham9_14_roundedProductData, hi0]
      rw [hzero, abs_zero]
      exact mul_nonneg hbeta
        (Finset.sum_nonneg fun _ _ =>
          mul_nonneg (abs_nonneg _) (abs_nonneg _))
  · by_cases hsub : j.val + 1 = i.val
    · have hi : 0 < i.val := by omega
      have hj : tridiag_prevIndex i hi = j := by
        ext
        simp [tridiag_prevIndex]
        omega
      subst j
      have hlocal :=
        higham9_20_primitive_division_residual_corrected fp
          (a := T.a i)
          (phat := higham9_14_roundedPivotVec fp T (tridiag_prevIndex i hi))
          (hpivot (tridiag_prevIndex i hi)) hu1
      rw [← higham9_14_roundedMultiplierVec_of_pos fp T i hi] at hlocal
      have hsum := higham9_14_actualFactor_abs_sub_le_sum fp T i hi
      have hscaled := mul_le_mul_of_nonneg_left hsum hbeta
      have hprev_ne : (tridiag_prevIndex i hi).val ≠ i.val := by
        simp [tridiag_prevIndex]
        omega
      have hprev_succ : (tridiag_prevIndex i hi).val + 1 = i.val := by
        simp [tridiag_prevIndex]
        omega
      have hdelta :
          higham9_14_actualFactorDelta fp T i (tridiag_prevIndex i hi) =
            higham9_14_roundedMultiplierVec fp T i *
              higham9_14_roundedPivotVec fp T (tridiag_prevIndex i hi) -
                T.a i := by
        simp [higham9_14_actualFactorDelta, tridiag_to_matrix,
          higham9_14_roundedProductData, hi, hprev_ne, hprev_succ]
      rw [hdelta]
      exact hlocal.trans hscaled
    · by_cases hsuper : i.val + 1 = j.val
      · have hzero : higham9_14_actualFactorDelta fp T i j = 0 := by
          simp [higham9_14_actualFactorDelta, tridiag_to_matrix,
            higham9_14_roundedProductData, hdiag, hsub, hsuper]
        rw [hzero, abs_zero]
        exact mul_nonneg hbeta
          (Finset.sum_nonneg fun _ _ =>
            mul_nonneg (abs_nonneg _) (abs_nonneg _))
      · have hzero : higham9_14_actualFactorDelta fp T i j = 0 := by
          simp [higham9_14_actualFactorDelta, tridiag_to_matrix,
            hdiag, hsub, hsuper]
        rw [hzero, abs_zero]
        exact mul_nonneg hbeta
          (Finset.sum_nonneg fun _ _ =>
            mul_nonneg (abs_nonneg _) (abs_nonneg _))

/-- Finite-data form of the primitive qualitative nonbreakdown theorem.  A
nonzero exact pivot at every source index produces a positive unit-roundoff
threshold below which all actual rounded pivots preserve their exact signs. -/
theorem higham9_14_exists_unitRoundoff_threshold_of_exactPivotVec_ne_zero
    {n : ℕ} (hn : 0 < n) (T : TridiagData n)
    (hpivot : ∀ i : Fin n, higham9_14_exactPivotVec T i ≠ 0) :
    ∃ epsilon : ℝ, 0 < epsilon ∧ epsilon ≤ 1 ∧
      ∀ fp : FPModel, fp.u < epsilon →
        ∀ i : Fin n,
          0 < higham9_14_roundedPivotVec fp T i *
            higham9_14_exactPivotVec T i := by
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
    higham9_14_exists_unitRoundoff_threshold_of_exact_pivots_ne_zero
      (higham9_14_natExtension T.a)
      (higham9_14_natExtension T.d)
      (higham9_14_natExtension T.c) N hpivot_nat
  let epsilon := min epsilon₀ 1
  have hepsilon : 0 < epsilon := lt_min hepsilon₀ one_pos
  refine ⟨epsilon, hepsilon, min_le_right _ _, ?_⟩
  intro fp hfp i
  have hfp₀ : fp.u < epsilon₀ := hfp.trans_le (min_le_left _ _)
  have hiN : i.val ≤ N := by
    dsimp [N]
    omega
  simpa [higham9_14_roundedPivotVec, higham9_14_exactPivotVec] using
    hthreshold fp hfp₀ i.val hiN

/-- Strongest source-shaped factorization producer available from the bare
`FPModel`: exact source pivots imply a uniform small-`u` regime in which the
actual recurrence does not break down and satisfies corrected equation
(9.20). -/
theorem higham9_20_exists_threshold_actual_tridiag_corrected
    {n : ℕ} (hn : 0 < n) (T : TridiagData n)
    (hpivot : ∀ i : Fin n, higham9_14_exactPivotVec T i ≠ 0) :
    ∃ epsilon : ℝ, 0 < epsilon ∧
      ∀ fp : FPModel, fp.u < epsilon →
        higham9_20_tridiag_lu_perturbation_model n
          (tridiag_to_matrix T)
          (tridiag_L_matrix (higham9_14_roundedMultiplierVec fp T))
          (tridiag_U_matrix (higham9_14_roundedPivotVec fp T) T.c)
          (higham9_14_actualFactorDelta fp T)
          (fp.u / (1 - fp.u)) := by
  obtain ⟨epsilon, hepsilon, hepsilon_le_one, hthreshold⟩ :=
    higham9_14_exists_unitRoundoff_threshold_of_exactPivotVec_ne_zero
      hn T hpivot
  refine ⟨epsilon, hepsilon, ?_⟩
  intro fp hfp
  have hu1 : fp.u < 1 := hfp.trans_le hepsilon_le_one
  apply higham9_20_actual_tridiag_lu_perturbation_model_corrected fp T hu1
  intro i
  exact (mul_ne_zero_iff.mp (ne_of_gt (hthreshold fp hfp i))).1

/-! ## Actual bidiagonal solves for equations (9.21)--(9.22) -/

/-- Natural-indexed forward sweep for a unit lower-bidiagonal system.  The
zero-th component is copied, and every later component uses exactly one
rounded multiplication and one rounded subtraction. -/
noncomputable def higham9_21_lowerSolveNat (fp : FPModel)
    (l b : ℕ → ℝ) : ℕ → ℝ
  | 0 => b 0
  | k + 1 =>
      fp.fl_sub (b (k + 1))
        (fp.fl_mul (l (k + 1)) (higham9_21_lowerSolveNat fp l b k))

/-- Actual rounded forward solve for the unit lower-bidiagonal factor. -/
noncomputable def higham9_21_lowerSolve (fp : FPModel) {n : ℕ}
    (l b : Fin n → ℝ) : Fin n → ℝ :=
  fun i => higham9_21_lowerSolveNat fp
    (higham9_14_natExtension l) (higham9_14_natExtension b) i.val

theorem higham9_21_lowerSolve_zero (fp : FPModel) {n : ℕ}
    (l b : Fin n → ℝ) (i : Fin n) (hi : i.val = 0) :
    higham9_21_lowerSolve fp l b i = b i := by
  have hn : 0 < n := by omega
  have hieq : i = ⟨0, hn⟩ := Fin.ext hi
  subst i
  unfold higham9_21_lowerSolve
  simp only [higham9_21_lowerSolveNat]
  exact higham9_14_natExtension_fin b ⟨0, hn⟩

theorem higham9_21_lowerSolve_of_pos (fp : FPModel) {n : ℕ}
    (l b : Fin n → ℝ) (i : Fin n) (hi : 0 < i.val) :
    higham9_21_lowerSolve fp l b i =
      fp.fl_sub (b i)
        (fp.fl_mul (l i)
          (higham9_21_lowerSolve fp l b (tridiag_prevIndex i hi))) := by
  have hsucc : i.val = (i.val - 1) + 1 := by omega
  unfold higham9_21_lowerSolve
  rw [hsucc]
  simp only [higham9_21_lowerSolveNat]
  have hb : higham9_14_natExtension b (i.val - 1 + 1) = b i := by
    rw [← hsucc]
    exact higham9_14_natExtension_fin b i
  have hl : higham9_14_natExtension l (i.val - 1 + 1) = l i := by
    rw [← hsucc]
    exact higham9_14_natExtension_fin l i
  rw [hb, hl]
  rfl

/-- Natural-indexed forward recursion on the reversed upper-bidiagonal
system.  Index zero is the last source row. -/
noncomputable def higham9_21_upperSolveRevNat (fp : FPModel)
    (u c y : ℕ → ℝ) : ℕ → ℝ
  | 0 => fp.fl_div (y 0) (u 0)
  | k + 1 =>
      fp.fl_div
        (fp.fl_sub (y (k + 1))
          (fp.fl_mul (c (k + 1))
            (higham9_21_upperSolveRevNat fp u c y k)))
        (u (k + 1))

/-- Actual rounded back solve for an upper-bidiagonal factor.  Reversal by
`Fin.rev` lets the implementation be a structurally recursive forward
sweep, while each source row still executes the literal back-substitution
operations. -/
noncomputable def higham9_21_upperSolve (fp : FPModel) {n : ℕ}
    (u c y : Fin n → ℝ) : Fin n → ℝ :=
  fun i => higham9_21_upperSolveRevNat fp
    (higham9_14_natExtension (fun r => u (Fin.rev r)))
    (higham9_14_natExtension (fun r => c (Fin.rev r)))
    (higham9_14_natExtension (fun r => y (Fin.rev r)))
    (Fin.rev i).val

theorem higham9_21_upperSolve_last (fp : FPModel) {n : ℕ}
    (u c y : Fin n → ℝ) (i : Fin n) (hi : i.val + 1 = n) :
    higham9_21_upperSolve fp u c y i = fp.fl_div (y i) (u i) := by
  unfold higham9_21_upperSolve
  have hrev : (Fin.rev i).val = 0 := by
    simp only [Fin.val_rev]
    omega
  have hy :
      higham9_14_natExtension (fun r : Fin n => y (Fin.rev r)) 0 = y i := by
    calc
      higham9_14_natExtension (fun r : Fin n => y (Fin.rev r)) 0 =
          higham9_14_natExtension (fun r : Fin n => y (Fin.rev r))
            (Fin.rev i).val := by rw [hrev]
      _ = y (Fin.rev (Fin.rev i)) :=
        higham9_14_natExtension_fin (fun r : Fin n => y (Fin.rev r)) (Fin.rev i)
      _ = y i := by simp
  have hu :
      higham9_14_natExtension (fun r : Fin n => u (Fin.rev r)) 0 = u i := by
    calc
      higham9_14_natExtension (fun r : Fin n => u (Fin.rev r)) 0 =
          higham9_14_natExtension (fun r : Fin n => u (Fin.rev r))
            (Fin.rev i).val := by rw [hrev]
      _ = u (Fin.rev (Fin.rev i)) :=
        higham9_14_natExtension_fin (fun r : Fin n => u (Fin.rev r)) (Fin.rev i)
      _ = u i := by simp
  rw [hrev]
  simp only [higham9_21_upperSolveRevNat]
  rw [hy, hu]

theorem higham9_21_upperSolve_of_not_last (fp : FPModel) {n : ℕ}
    (u c y : Fin n → ℝ) (i : Fin n) (hi : i.val + 1 < n) :
    higham9_21_upperSolve fp u c y i =
      fp.fl_div
        (fp.fl_sub (y i)
          (fp.fl_mul (c i)
            (higham9_21_upperSolve fp u c y ⟨i.val + 1, hi⟩)))
        (u i) := by
  let s : Fin n := ⟨i.val + 1, hi⟩
  have hrev : (Fin.rev i).val = (Fin.rev s).val + 1 := by
    simp only [Fin.val_rev]
    simp [s]
    omega
  unfold higham9_21_upperSolve
  rw [hrev]
  simp only [higham9_21_upperSolveRevNat]
  have hy :
      higham9_14_natExtension (fun r : Fin n => y (Fin.rev r))
          ((Fin.rev s).val + 1) = y i := by
    rw [← hrev]
    simpa using
      higham9_14_natExtension_fin (fun r : Fin n => y (Fin.rev r)) (Fin.rev i)
  have hc :
      higham9_14_natExtension (fun r : Fin n => c (Fin.rev r))
          ((Fin.rev s).val + 1) = c i := by
    rw [← hrev]
    simpa using
      higham9_14_natExtension_fin (fun r : Fin n => c (Fin.rev r)) (Fin.rev i)
  have hu :
      higham9_14_natExtension (fun r : Fin n => u (Fin.rev r))
          ((Fin.rev s).val + 1) = u i := by
    rw [← hrev]
    simpa using
      higham9_14_natExtension_fin (fun r : Fin n => u (Fin.rev r)) (Fin.rev i)
  rw [hy, hc, hu]

private theorem higham9_21_lower_row_sum
    {n : ℕ} (i : Fin n) (diag sub : ℝ) (v : Fin n → ℝ) :
    (∑ j : Fin n,
        (if j = i then diag
          else if j.val + 1 = i.val then sub else 0) * v j) =
      if h : 0 < i.val then
        diag * v i + sub * v (tridiag_prevIndex i h)
      else diag * v i := by
  classical
  split_ifs with h
  · let p : Fin n := tridiag_prevIndex i h
    have hne : p ≠ i := by
      intro heq
      have := congrArg Fin.val heq
      simp [p, tridiag_prevIndex] at this
      omega
    have hp : p.val + 1 = i.val := by
      simp [p, tridiag_prevIndex]
      omega
    calc
      (∑ j : Fin n,
          (if j = i then diag
            else if j.val + 1 = i.val then sub else 0) * v j) =
          ∑ j : Fin n,
            ((if j = i then diag * v j else 0) +
              (if j = p then sub * v j else 0)) := by
            apply Finset.sum_congr rfl
            intro j _hj
            have hsub : (j.val + 1 = i.val) ↔ j = p := by
              constructor
              · intro hv
                apply Fin.ext
                simp [p, tridiag_prevIndex]
                omega
              · intro hj
                simpa [hj] using hp
            simp only [hsub]
            by_cases hji : j = i
            · subst j
              simp [Ne.symm hne]
            · by_cases hjp : j = p
              · subst j
                simp [hne]
              · simp [hji, hjp]
      _ = diag * v i + sub * v p := by
        rw [Finset.sum_add_distrib]
        simp
      _ = diag * v i + sub * v (tridiag_prevIndex i h) := rfl
  · have hsub : ∀ j : Fin n, j.val + 1 ≠ i.val := by
      intro j hj
      exact h (by omega)
    calc
      (∑ j : Fin n,
          (if j = i then diag
            else if j.val + 1 = i.val then sub else 0) * v j) =
          ∑ j : Fin n, if j = i then diag * v j else 0 := by
            apply Finset.sum_congr rfl
            intro j _hj
            simp [hsub j]
      _ = diag * v i := by simp

private theorem higham9_21_upper_row_sum
    {n : ℕ} (i : Fin n) (diag super : ℝ) (v : Fin n → ℝ) :
    (∑ j : Fin n,
        (if j = i then diag
          else if i.val + 1 = j.val then super else 0) * v j) =
      if h : i.val + 1 < n then
        diag * v i + super * v ⟨i.val + 1, h⟩
      else diag * v i := by
  classical
  split_ifs with h
  · let s : Fin n := ⟨i.val + 1, h⟩
    have hne : s ≠ i := by
      intro heq
      have := congrArg Fin.val heq
      simp [s] at this
    calc
      (∑ j : Fin n,
          (if j = i then diag
            else if i.val + 1 = j.val then super else 0) * v j) =
          ∑ j : Fin n,
            ((if j = i then diag * v j else 0) +
              (if j = s then super * v j else 0)) := by
            apply Finset.sum_congr rfl
            intro j _hj
            have hsuper : (i.val + 1 = j.val) ↔ j = s := by
              constructor
              · intro hv
                exact Fin.ext (by simpa [s] using hv.symm)
              · intro hj
                simpa [s, hj]
            simp only [hsuper]
            by_cases hji : j = i
            · subst j
              simp [Ne.symm hne]
            · by_cases hjs : j = s
              · subst j
                simp [hne]
              · simp [hji, hjs]
      _ = diag * v i + super * v s := by
        rw [Finset.sum_add_distrib]
        simp
      _ = diag * v i + super * v ⟨i.val + 1, h⟩ := rfl
  · have hsuper : ∀ j : Fin n, i.val + 1 ≠ j.val := by
      intro j hj
      exact h (by simpa [hj] using j.isLt)
    calc
      (∑ j : Fin n,
          (if j = i then diag
            else if i.val + 1 = j.val then super else 0) * v j) =
          ∑ j : Fin n, if j = i then diag * v j else 0 := by
            apply Finset.sum_congr rfl
            intro j _hj
            simp [hsuper j]
      _ = diag * v i := by simp

private theorem higham9_21_lower_step_corrected
    (fp : FPModel) {l b yprev : ℝ} (hu1 : fp.u < 1) :
    ∃ ddiag dsub : ℝ,
      |ddiag| ≤ fp.u / (1 - fp.u) ∧
      |dsub| ≤ (fp.u / (1 - fp.u)) * |l| ∧
      (1 + ddiag) * fp.fl_sub b (fp.fl_mul l yprev) +
          (l + dsub) * yprev = b := by
  obtain ⟨delta, hdelta, hmul⟩ := fp.model_mul l yprev
  obtain ⟨theta, htheta, hsub⟩ := fp.model_sub b (fp.fl_mul l yprev)
  obtain ⟨epsilon, hepsilon, heq⟩ :=
    higham9_14_backward_relative_correction
      fp.u_nonneg hu1 htheta hsub
  have hone_sub_pos : 0 < 1 - fp.u := by linarith
  have hu_le_beta : fp.u ≤ fp.u / (1 - fp.u) := by
    apply (le_div_iff₀ hone_sub_pos).2
    nlinarith [fp.u_nonneg]
  refine ⟨epsilon, l * delta, hepsilon, ?_, ?_⟩
  · rw [abs_mul]
    simpa [mul_comm] using
      mul_le_mul_of_nonneg_left (hdelta.trans hu_le_beta) (abs_nonneg l)
  · calc
      (1 + epsilon) * fp.fl_sub b (fp.fl_mul l yprev) +
          (l + l * delta) * yprev =
          (1 + epsilon) * fp.fl_sub b (fp.fl_mul l yprev) +
            fp.fl_mul l yprev := by rw [hmul]; ring
      _ = b := by linarith [heq]

private theorem higham9_21_upper_last_step_corrected
    (fp : FPModel) {u y : ℝ} (hu : u ≠ 0) (hu1 : fp.u < 1) :
    ∃ ddiag : ℝ,
      |ddiag| ≤
        (2 * (fp.u / (1 - fp.u)) + (fp.u / (1 - fp.u)) ^ 2) * |u| ∧
      (u + ddiag) * fp.fl_div y u = y := by
  obtain ⟨epsilon, hepsilon, heq⟩ :=
    higham9_14_model_div_backward_corrected fp hu hu1
  let beta := fp.u / (1 - fp.u)
  have hbeta : 0 ≤ beta := by
    exact div_nonneg fp.u_nonneg (by linarith)
  have hbeta_le : beta ≤ 2 * beta + beta ^ 2 := by
    nlinarith [sq_nonneg beta]
  refine ⟨u * epsilon, ?_, ?_⟩
  · rw [abs_mul]
    simpa [beta, mul_comm] using
      mul_le_mul_of_nonneg_left
        (hepsilon.trans hbeta_le) (abs_nonneg u)
  · have heq' : u * ((1 + epsilon) * fp.fl_div y u) = y := by
      rw [heq]
      exact mul_div_cancel₀ y hu
    rw [show u + u * epsilon = u * (1 + epsilon) by ring]
    simpa [mul_assoc] using heq'

private theorem higham9_21_upper_step_corrected
    (fp : FPModel) {u c y xnext : ℝ} (hu : u ≠ 0)
    (hu1 : fp.u < 1) :
    let x := fp.fl_div
      (fp.fl_sub y (fp.fl_mul c xnext)) u
    ∃ ddiag dsuper : ℝ,
      |ddiag| ≤
        (2 * (fp.u / (1 - fp.u)) + (fp.u / (1 - fp.u)) ^ 2) * |u| ∧
      |dsuper| ≤
        (2 * (fp.u / (1 - fp.u)) + (fp.u / (1 - fp.u)) ^ 2) * |c| ∧
      (u + ddiag) * x + (c + dsuper) * xnext = y := by
  dsimp only
  let m := fp.fl_mul c xnext
  let s := fp.fl_sub y m
  let x := fp.fl_div s u
  let beta := fp.u / (1 - fp.u)
  obtain ⟨delta, hdelta, hmul⟩ := fp.model_mul c xnext
  obtain ⟨theta, htheta, hsub⟩ := fp.model_sub y m
  obtain ⟨epsilonS, hepsilonS, heqS⟩ :=
    higham9_14_backward_relative_correction
      fp.u_nonneg hu1 htheta hsub
  obtain ⟨epsilonD, hepsilonD, heqD⟩ :=
    higham9_14_model_div_backward_corrected fp hu hu1
  have hbeta : 0 ≤ beta := by
    exact div_nonneg fp.u_nonneg (by linarith)
  have hone_sub_pos : 0 < 1 - fp.u := by linarith
  have hu_le_beta : fp.u ≤ beta := by
    dsimp [beta]
    apply (le_div_iff₀ hone_sub_pos).2
    nlinarith [fp.u_nonneg]
  have hfactor :
      |(1 + epsilonS) * (1 + epsilonD) - 1| ≤
        2 * beta + beta ^ 2 := by
    calc
      |(1 + epsilonS) * (1 + epsilonD) - 1| =
          |epsilonS + epsilonD + epsilonS * epsilonD| := by ring_nf
      _ ≤ |epsilonS| + |epsilonD| + |epsilonS * epsilonD| := by
        exact (abs_add_le (epsilonS + epsilonD) (epsilonS * epsilonD)).trans
          (add_le_add (abs_add_le epsilonS epsilonD) le_rfl)
      _ = |epsilonS| + |epsilonD| + |epsilonS| * |epsilonD| := by
        rw [abs_mul]
      _ ≤ beta + beta + beta * beta := by
        exact add_le_add
          (add_le_add hepsilonS hepsilonD)
          (mul_le_mul hepsilonS hepsilonD (abs_nonneg _) hbeta)
      _ = 2 * beta + beta ^ 2 := by ring
  have hu_le_coeff : fp.u ≤ 2 * beta + beta ^ 2 := by
    nlinarith [sq_nonneg beta]
  have hdivEq : u * ((1 + epsilonD) * x) = s := by
    dsimp [x]
    rw [heqD]
    exact mul_div_cancel₀ s hu
  refine
    ⟨u * ((1 + epsilonS) * (1 + epsilonD) - 1), c * delta, ?_, ?_, ?_⟩
  · rw [abs_mul]
    simpa [beta, mul_comm] using
      mul_le_mul_of_nonneg_left hfactor (abs_nonneg u)
  · rw [abs_mul]
    simpa [beta, mul_comm] using
      mul_le_mul_of_nonneg_left
        (hdelta.trans hu_le_coeff) (abs_nonneg c)
  · have hdiag :
        (u + u * ((1 + epsilonS) * (1 + epsilonD) - 1)) * x =
          (1 + epsilonS) * s := by
      calc
        (u + u * ((1 + epsilonS) * (1 + epsilonD) - 1)) * x =
            (1 + epsilonS) * (u * ((1 + epsilonD) * x)) := by ring
        _ = (1 + epsilonS) * s := by rw [hdivEq]
    rw [hdiag]
    have hm : m = c * xnext * (1 + delta) := hmul
    change (1 + epsilonS) * s = y - m at heqS
    calc
      (1 + epsilonS) * s + (c + c * delta) * xnext =
          (1 + epsilonS) * s + m := by rw [hm]; ring
      _ = y := by linarith [heqS]

/-- Corrected equation (9.21) for the actual sparse bidiagonal sweeps.

The lower solve uses the corrected coefficient `beta = u/(1-u)`.  The upper
solve has the exact source coefficient `2*beta + beta^2`, represented by the
existing equation-(9.21) predicate at parameter `beta`.  No dense triangular
solve, exact computed-factor identity, or sign/growth comparison is assumed. -/
theorem higham9_21_actual_bidiagonal_solve_perturbation_model_corrected
    (fp : FPModel) {n : ℕ}
    (l u c b : Fin n → ℝ) (hu1 : fp.u < 1)
    (hu_diag : ∀ i : Fin n, u i ≠ 0) :
    ∃ DeltaL DeltaU : Fin n → Fin n → ℝ,
      higham9_21_tridiag_solve_perturbation_model n
        (tridiag_L_matrix l) (tridiag_U_matrix u c)
        (higham9_21_lowerSolve fp l b)
        (higham9_21_upperSolve fp u c (higham9_21_lowerSolve fp l b))
        b DeltaL DeltaU (fp.u / (1 - fp.u)) := by
  classical
  let beta := fp.u / (1 - fp.u)
  let coeff := 2 * beta + beta ^ 2
  let yhat := higham9_21_lowerSolve fp l b
  let xhat := higham9_21_upperSolve fp u c yhat
  have hbeta : 0 ≤ beta := by
    exact div_nonneg fp.u_nonneg (by linarith)
  have hLrows : ∀ i : Fin n, ∃ ddiag dsub : ℝ,
      |ddiag| ≤ beta ∧ |dsub| ≤ beta * |l i| ∧
      (1 + ddiag) * yhat i +
          (if hi : 0 < i.val then
            (l i + dsub) * yhat (tridiag_prevIndex i hi) else 0) = b i := by
    intro i
    by_cases hi : 0 < i.val
    · obtain ⟨ddiag, dsub, hddiag, hdsub, heq⟩ :=
        higham9_21_lower_step_corrected fp
          (l := l i) (b := b i)
          (yprev := yhat (tridiag_prevIndex i hi)) hu1
      refine ⟨ddiag, dsub, hddiag, ?_, ?_⟩
      · simpa [beta] using hdsub
      · simp only [hi, dite_true]
        rw [show yhat i =
            fp.fl_sub (b i)
              (fp.fl_mul (l i) (yhat (tridiag_prevIndex i hi))) by
          simpa [yhat] using higham9_21_lowerSolve_of_pos fp l b i hi]
        exact heq
    · have hi0 : i.val = 0 := by omega
      refine ⟨0, 0, by simpa using hbeta, ?_, ?_⟩
      · simpa using mul_nonneg hbeta (abs_nonneg (l i))
      · simp [hi, yhat, higham9_21_lowerSolve_zero fp l b i hi0]
  choose ldiag lsub hldiag hlsub hLeq using hLrows
  have hUrows : ∀ i : Fin n, ∃ ddiag dsuper : ℝ,
      |ddiag| ≤ coeff * |u i| ∧
      |dsuper| ≤ coeff * |c i| ∧
      (u i + ddiag) * xhat i +
          (if hi : i.val + 1 < n then
            (c i + dsuper) * xhat ⟨i.val + 1, hi⟩ else 0) = yhat i := by
    intro i
    by_cases hi : i.val + 1 < n
    · obtain ⟨ddiag, dsuper, hddiag, hdsuper, heq⟩ :=
        higham9_21_upper_step_corrected fp
          (u := u i) (c := c i) (y := yhat i)
          (xnext := xhat ⟨i.val + 1, hi⟩) (hu_diag i) hu1
      refine ⟨ddiag, dsuper, ?_, ?_, ?_⟩
      · simpa [beta, coeff] using hddiag
      · simpa [beta, coeff] using hdsuper
      · simp only [hi, dite_true]
        rw [show xhat i = fp.fl_div
            (fp.fl_sub (yhat i)
              (fp.fl_mul (c i) (xhat ⟨i.val + 1, hi⟩))) (u i) by
          simpa [xhat] using
            higham9_21_upperSolve_of_not_last fp u c yhat i hi]
        exact heq
    · have hilast : i.val + 1 = n := by omega
      obtain ⟨ddiag, hddiag, heq⟩ :=
        higham9_21_upper_last_step_corrected fp
          (u := u i) (y := yhat i) (hu_diag i) hu1
      refine ⟨ddiag, 0, ?_, ?_, ?_⟩
      · simpa [beta, coeff] using hddiag
      · have hcoeff : 0 ≤ coeff := by
          dsimp [coeff]
          nlinarith [sq_nonneg beta]
        simpa using mul_nonneg hcoeff (abs_nonneg (c i))
      · simp only [hi, dite_false, add_zero]
        rw [show xhat i = fp.fl_div (yhat i) (u i) by
          simpa [xhat] using higham9_21_upperSolve_last fp u c yhat i hilast]
        exact heq
  choose udiag usuper hudiag husuper hUeq using hUrows
  let DeltaL : Fin n → Fin n → ℝ := fun i j =>
    if j = i then ldiag i
    else if j.val + 1 = i.val then lsub i
    else 0
  let DeltaU : Fin n → Fin n → ℝ := fun i j =>
    if j = i then udiag i
    else if i.val + 1 = j.val then usuper i
    else 0
  refine ⟨DeltaL, DeltaU, ?_, ?_, ?_, ?_⟩
  · intro i
    have hshape :
        (∑ j : Fin n,
          (tridiag_L_matrix l i j + DeltaL i j) * yhat j) =
        ∑ j : Fin n,
          (if j = i then 1 + ldiag i
           else if j.val + 1 = i.val then l i + lsub i else 0) * yhat j := by
      apply Finset.sum_congr rfl
      intro j _hj
      by_cases hd : j = i
      · subst j
        simp [tridiag_L_matrix, DeltaL]
      · by_cases hs : j.val + 1 = i.val
        · have hval : j.val ≠ i.val := by omega
          simp [tridiag_L_matrix, DeltaL, hd, hs, hval]
        · have hval : j.val ≠ i.val := by
            intro hval
            exact hd (Fin.ext hval)
          simp [tridiag_L_matrix, DeltaL, hd, hs, hval]
    rw [hshape, higham9_21_lower_row_sum]
    by_cases hi : 0 < i.val
    · simpa [hi] using hLeq i
    · simpa [hi] using hLeq i
  · intro i j
    by_cases hd : j = i
    · subst j
      simpa [DeltaL, tridiag_L_matrix] using hldiag i
    · by_cases hs : j.val + 1 = i.val
      · have hval : j.val ≠ i.val := by omega
        simpa [DeltaL, tridiag_L_matrix, hd, hs, hval] using hlsub i
      · have hval : j.val ≠ i.val := by
          intro hval
          exact hd (Fin.ext hval)
        simp [DeltaL, tridiag_L_matrix, hd, hs, hval, hbeta]
  · intro i
    have hshape :
        (∑ j : Fin n,
          (tridiag_U_matrix u c i j + DeltaU i j) * xhat j) =
        ∑ j : Fin n,
          (if j = i then u i + udiag i
           else if i.val + 1 = j.val then c i + usuper i else 0) * xhat j := by
      apply Finset.sum_congr rfl
      intro j _hj
      by_cases hd : j = i
      · subst j
        simp [tridiag_U_matrix, DeltaU]
      · by_cases hs : i.val + 1 = j.val
        · have hval : j.val ≠ i.val := by omega
          simp [tridiag_U_matrix, DeltaU, hd, hs, hval]
        · have hval : j.val ≠ i.val := by
            intro hval
            exact hd (Fin.ext hval)
          simp [tridiag_U_matrix, DeltaU, hd, hs, hval]
    rw [hshape, higham9_21_upper_row_sum]
    change
      (if h : i.val + 1 < n then
        (u i + udiag i) * xhat i +
          (c i + usuper i) * xhat ⟨i.val + 1, h⟩
       else (u i + udiag i) * xhat i) = yhat i
    by_cases hi : i.val + 1 < n
    · simpa only [dif_pos hi] using hUeq i
    · simpa only [dif_neg hi, add_zero] using hUeq i
  · intro i j
    by_cases hd : j = i
    · subst j
      simpa [DeltaU, tridiag_U_matrix, coeff] using hudiag i
    · by_cases hs : i.val + 1 = j.val
      · have hval : j.val ≠ i.val := by omega
        simpa [DeltaU, tridiag_U_matrix, hd, hs, hval, coeff] using husuper i
      · have hval : j.val ≠ i.val := by
          intro hval
          exact hd (Fin.ext hval)
        have hcoeff : 0 ≤ 2 * beta + beta ^ 2 := by
          nlinarith [sq_nonneg beta]
        simp [DeltaU, tridiag_U_matrix, hd, hs, hval, beta, hcoeff]

/-- Equations (9.20)--(9.22) for the actual recurrence and actual sparse
solves.  The source coefficient is the printed polynomial evaluated at the
honest primitive parameter `beta = u/(1-u)`. -/
theorem higham9_22_actual_tridiag_source_f_bound_corrected
    (fp : FPModel) {n : ℕ} (T : TridiagData n) (b : Fin n → ℝ)
    (hu1 : fp.u < 1)
    (hpivot : ∀ i : Fin n, higham9_14_roundedPivotVec fp T i ≠ 0) :
    ∃ DeltaA : Fin n → Fin n → ℝ,
      (∀ i j, |DeltaA i j| ≤
        higham9_14_f (fp.u / (1 - fp.u)) *
          ∑ k : Fin n,
            |tridiag_L_matrix (higham9_14_roundedMultiplierVec fp T) i k| *
            |tridiag_U_matrix (higham9_14_roundedPivotVec fp T) T.c k j|) ∧
      (∀ i,
        ∑ j : Fin n, (tridiag_to_matrix T i j + DeltaA i j) *
          higham9_21_upperSolve fp
            (higham9_14_roundedPivotVec fp T) T.c
            (higham9_21_lowerSolve fp
              (higham9_14_roundedMultiplierVec fp T) b) j = b i) := by
  let beta := fp.u / (1 - fp.u)
  have hbeta : 0 ≤ beta := by
    exact div_nonneg fp.u_nonneg (by linarith)
  have h20 :=
    higham9_20_actual_tridiag_lu_perturbation_model_corrected
      fp T hu1 hpivot
  obtain ⟨DeltaL, DeltaU, h21⟩ :=
    higham9_21_actual_bidiagonal_solve_perturbation_model_corrected
      fp (higham9_14_roundedMultiplierVec fp T)
        (higham9_14_roundedPivotVec fp T) T.c b hu1 hpivot
  simpa [beta] using
    higham9_22_source_f_bound_of_9_20_9_21_models n
      (tridiag_to_matrix T)
      (tridiag_L_matrix (higham9_14_roundedMultiplierVec fp T))
      (tridiag_U_matrix (higham9_14_roundedPivotVec fp T) T.c)
      (higham9_21_lowerSolve fp
        (higham9_14_roundedMultiplierVec fp T) b)
      (higham9_21_upperSolve fp
        (higham9_14_roundedPivotVec fp T) T.c
        (higham9_21_lowerSolve fp
          (higham9_14_roundedMultiplierVec fp T) b))
      b beta hbeta (higham9_14_actualFactorDelta fp T)
      DeltaL DeltaU h20 h21

/-- Uniform small-unit-roundoff producer for the actual factorization and
actual bidiagonal solves through equation (9.22). -/
theorem higham9_22_exists_threshold_actual_tridiag_source_f_corrected
    {n : ℕ} (hn : 0 < n) (T : TridiagData n) (b : Fin n → ℝ)
    (hpivot : ∀ i : Fin n, higham9_14_exactPivotVec T i ≠ 0) :
    ∃ epsilon : ℝ, 0 < epsilon ∧
      ∀ fp : FPModel, fp.u < epsilon →
        ∃ DeltaA : Fin n → Fin n → ℝ,
          (∀ i j, |DeltaA i j| ≤
            higham9_14_f (fp.u / (1 - fp.u)) *
              ∑ k : Fin n,
                |tridiag_L_matrix
                    (higham9_14_roundedMultiplierVec fp T) i k| *
                |tridiag_U_matrix
                    (higham9_14_roundedPivotVec fp T) T.c k j|) ∧
          (∀ i,
            ∑ j : Fin n, (tridiag_to_matrix T i j + DeltaA i j) *
              higham9_21_upperSolve fp
                (higham9_14_roundedPivotVec fp T) T.c
                (higham9_21_lowerSolve fp
                  (higham9_14_roundedMultiplierVec fp T) b) j = b i) := by
  obtain ⟨epsilon, hepsilon, hepsilon_le_one, hthreshold⟩ :=
    higham9_14_exists_unitRoundoff_threshold_of_exactPivotVec_ne_zero
      hn T hpivot
  refine ⟨epsilon, hepsilon, ?_⟩
  intro fp hfp
  have hu1 : fp.u < 1 := hfp.trans_le hepsilon_le_one
  have hpivot_round : ∀ i : Fin n,
      higham9_14_roundedPivotVec fp T i ≠ 0 := by
    intro i
    exact (mul_ne_zero_iff.mp (ne_of_gt (hthreshold fp hfp i))).1
  exact higham9_22_actual_tridiag_source_f_bound_corrected
    fp T b hu1 hpivot_round

/-- Corrected source-relative endpoint for the *actual* recurrence, under the
exact local condition used in Higham's last absorption step: the computed
bidiagonal product has no entrywise cancellation.  The bare forward-relative
`FPModel` changes the primitive parameter from `u` to
`beta = u / (1-u)`, so the honest conclusion is `h(beta)|A|` and the
smallness condition is `u < 1/2`.

This theorem deliberately takes no-cancellation as a visible hypothesis.  It
therefore isolates the sole class-specific obligation without identifying the
rounded factors with an exact factorization of the source. -/
theorem higham9_14_actual_tridiag_source_h_bound_corrected_of_noCancellation
    (fp : FPModel) {n : ℕ} (T : TridiagData n) (b : Fin n → ℝ)
    (hu_half : fp.u < (1 : ℝ) / 2)
    (hpivot : ∀ i : Fin n, higham9_14_roundedPivotVec fp T i ≠ 0)
    (hNoCancellation : ∀ i j : Fin n,
      (∑ k : Fin n,
        |tridiag_L_matrix (higham9_14_roundedMultiplierVec fp T) i k| *
          |tridiag_U_matrix
            (higham9_14_roundedPivotVec fp T) T.c k j|) =
        |∑ k : Fin n,
          tridiag_L_matrix (higham9_14_roundedMultiplierVec fp T) i k *
            tridiag_U_matrix
              (higham9_14_roundedPivotVec fp T) T.c k j|) :
    ∃ DeltaA : Fin n → Fin n → ℝ,
      (∀ i j, |DeltaA i j| ≤
        higham9_14_h (fp.u / (1 - fp.u)) *
          |tridiag_to_matrix T i j|) ∧
      (∀ i,
        ∑ j : Fin n, (tridiag_to_matrix T i j + DeltaA i j) *
          higham9_21_upperSolve fp
            (higham9_14_roundedPivotVec fp T) T.c
            (higham9_21_lowerSolve fp
              (higham9_14_roundedMultiplierVec fp T) b) j = b i) := by
  let beta := fp.u / (1 - fp.u)
  have hu1 : fp.u < 1 := by linarith
  have hbeta_nonneg : 0 ≤ beta :=
    div_nonneg fp.u_nonneg (by linarith)
  have hbeta_lt_one : beta < 1 := by
    rw [div_lt_one (by linarith : 0 < 1 - fp.u)]
    linarith
  have h20 :=
    higham9_20_actual_tridiag_lu_perturbation_model_corrected
      fp T hu1 hpivot
  obtain ⟨DeltaL, DeltaU, h21⟩ :=
    higham9_21_actual_bidiagonal_solve_perturbation_model_corrected
      fp (higham9_14_roundedMultiplierVec fp T)
        (higham9_14_roundedPivotVec fp T) T.c b hu1 hpivot
  have hAbsLUhat_mul_bound : ∀ i j : Fin n,
      (1 - beta) *
          (∑ k : Fin n,
            |tridiag_L_matrix
                (higham9_14_roundedMultiplierVec fp T) i k| *
              |tridiag_U_matrix
                (higham9_14_roundedPivotVec fp T) T.c k j|) ≤
        |tridiag_to_matrix T i j| := by
    intro i j
    let S := ∑ k : Fin n,
      |tridiag_L_matrix
          (higham9_14_roundedMultiplierVec fp T) i k| *
        |tridiag_U_matrix
          (higham9_14_roundedPivotVec fp T) T.c k j|
    have hS_nonneg : 0 ≤ S :=
      Finset.sum_nonneg fun k _ =>
        mul_nonneg (abs_nonneg _) (abs_nonneg _)
    have hproduct :
        (∑ k : Fin n,
          tridiag_L_matrix
              (higham9_14_roundedMultiplierVec fp T) i k *
            tridiag_U_matrix
              (higham9_14_roundedPivotVec fp T) T.c k j) =
          tridiag_to_matrix T i j +
            higham9_14_actualFactorDelta fp T i j := h20.1 i j
    have hS_eq : S =
        |tridiag_to_matrix T i j +
          higham9_14_actualFactorDelta fp T i j| := by
      rw [show S =
          |∑ k : Fin n,
            tridiag_L_matrix
                (higham9_14_roundedMultiplierVec fp T) i k *
              tridiag_U_matrix
                (higham9_14_roundedPivotVec fp T) T.c k j| from
        hNoCancellation i j]
      rw [hproduct]
    have hDelta :
        |higham9_14_actualFactorDelta fp T i j| ≤ beta * S := by
      simpa [beta, S] using h20.2 i j
    have htriangle :
        |tridiag_to_matrix T i j +
            higham9_14_actualFactorDelta fp T i j| ≤
          |tridiag_to_matrix T i j| +
            |higham9_14_actualFactorDelta fp T i j| :=
      abs_add_le _ _
    change (1 - beta) * S ≤ |tridiag_to_matrix T i j|
    rw [← hS_eq] at htriangle
    nlinarith
  simpa [beta] using
    higham9_14_source_h_bound_of_9_20_9_21_models_absLUhat_mul_one_sub_bound
      n (tridiag_to_matrix T)
      (tridiag_L_matrix (higham9_14_roundedMultiplierVec fp T))
      (tridiag_U_matrix (higham9_14_roundedPivotVec fp T) T.c)
      (higham9_21_lowerSolve fp
        (higham9_14_roundedMultiplierVec fp T) b)
      (higham9_21_upperSolve fp
        (higham9_14_roundedPivotVec fp T) T.c
        (higham9_21_lowerSolve fp
          (higham9_14_roundedMultiplierVec fp T) b))
      b beta hbeta_nonneg hbeta_lt_one hAbsLUhat_mul_bound
      (higham9_14_actualFactorDelta fp T) DeltaL DeltaU h20 h21

/-- Strongest direct corrected `3h` endpoint: if the *actual computed factors*
satisfy the factor-growth comparison used in the diagonal-dominant clause,
the actual recurrence and solves have a `3 h(u/(1-u)) |A|` backward error.
The premise is deliberately about the computed factors; source diagonal
dominance alone does not imply it in the repository's bare `FPModel`. -/
theorem higham9_14_actual_tridiag_source_three_h_bound_corrected_of_growth
    (fp : FPModel) {n : ℕ} (T : TridiagData n) (b : Fin n → ℝ)
    (hu_half : fp.u < (1 : ℝ) / 2)
    (hpivot : ∀ i : Fin n, higham9_14_roundedPivotVec fp T i ≠ 0)
    (hgrowth : ∀ i j : Fin n,
      (∑ k : Fin n,
        |tridiag_L_matrix (higham9_14_roundedMultiplierVec fp T) i k| *
          |tridiag_U_matrix
            (higham9_14_roundedPivotVec fp T) T.c k j|) ≤
        3 * |tridiag_to_matrix T i j|) :
    ∃ DeltaA : Fin n → Fin n → ℝ,
      (∀ i j, |DeltaA i j| ≤
        3 * higham9_14_h (fp.u / (1 - fp.u)) *
          |tridiag_to_matrix T i j|) ∧
      (∀ i,
        ∑ j : Fin n, (tridiag_to_matrix T i j + DeltaA i j) *
          higham9_21_upperSolve fp
            (higham9_14_roundedPivotVec fp T) T.c
            (higham9_21_lowerSolve fp
              (higham9_14_roundedMultiplierVec fp T) b) j = b i) := by
  let beta := fp.u / (1 - fp.u)
  have hu1 : fp.u < 1 := by linarith
  have hbeta_nonneg : 0 ≤ beta :=
    div_nonneg fp.u_nonneg (by linarith)
  have hbeta_lt_one : beta < 1 := by
    rw [div_lt_one (by linarith : 0 < 1 - fp.u)]
    linarith
  obtain ⟨DeltaA, hDeltaA, hsolve⟩ :=
    higham9_22_actual_tridiag_source_f_bound_corrected fp T b hu1 hpivot
  refine ⟨DeltaA, ?_, hsolve⟩
  intro i j
  have hf_nonneg := higham9_14_f_nonneg hbeta_nonneg
  have hfh := higham9_14_f_le_h hbeta_nonneg hbeta_lt_one
  calc
    |DeltaA i j| ≤ higham9_14_f beta *
        (∑ k : Fin n,
          |tridiag_L_matrix (higham9_14_roundedMultiplierVec fp T) i k| *
            |tridiag_U_matrix
              (higham9_14_roundedPivotVec fp T) T.c k j|) := by
      simpa [beta] using hDeltaA i j
    _ ≤ higham9_14_f beta * (3 * |tridiag_to_matrix T i j|) :=
      mul_le_mul_of_nonneg_left (hgrowth i j) hf_nonneg
    _ ≤ higham9_14_h beta * (3 * |tridiag_to_matrix T i j|) :=
      mul_le_mul_of_nonneg_right hfh
        (mul_nonneg (by norm_num) (abs_nonneg _))
    _ = 3 * higham9_14_h beta * |tridiag_to_matrix T i j| := by ring

/-- Corrected source-relative endpoint with an arbitrary nonnegative
computed-factor growth constant.  This is the reusable absorption lemma
behind the diagonal-dominant small-unit-roundoff closure below. -/
theorem higham9_14_actual_tridiag_source_scaled_h_bound_corrected_of_growth
    (fp : FPModel) {n : ℕ} (T : TridiagData n) (b : Fin n → ℝ)
    (K : ℝ) (hK : 0 ≤ K)
    (hu_half : fp.u < (1 : ℝ) / 2)
    (hpivot : ∀ i : Fin n, higham9_14_roundedPivotVec fp T i ≠ 0)
    (hgrowth : ∀ i j : Fin n,
      (∑ k : Fin n,
        |tridiag_L_matrix (higham9_14_roundedMultiplierVec fp T) i k| *
          |tridiag_U_matrix
            (higham9_14_roundedPivotVec fp T) T.c k j|) ≤
        K * |tridiag_to_matrix T i j|) :
    ∃ DeltaA : Fin n → Fin n → ℝ,
      (∀ i j, |DeltaA i j| ≤
        K * higham9_14_h (fp.u / (1 - fp.u)) *
          |tridiag_to_matrix T i j|) ∧
      (∀ i,
        ∑ j : Fin n, (tridiag_to_matrix T i j + DeltaA i j) *
          higham9_21_upperSolve fp
            (higham9_14_roundedPivotVec fp T) T.c
            (higham9_21_lowerSolve fp
              (higham9_14_roundedMultiplierVec fp T) b) j = b i) := by
  let beta := fp.u / (1 - fp.u)
  have hu1 : fp.u < 1 := by linarith
  have hbeta_nonneg : 0 ≤ beta :=
    div_nonneg fp.u_nonneg (by linarith)
  have hbeta_lt_one : beta < 1 := by
    rw [div_lt_one (by linarith : 0 < 1 - fp.u)]
    linarith
  obtain ⟨DeltaA, hDeltaA, hsolve⟩ :=
    higham9_22_actual_tridiag_source_f_bound_corrected fp T b hu1 hpivot
  refine ⟨DeltaA, ?_, hsolve⟩
  intro i j
  have hf_nonneg := higham9_14_f_nonneg hbeta_nonneg
  have hfh := higham9_14_f_le_h hbeta_nonneg hbeta_lt_one
  calc
    |DeltaA i j| ≤ higham9_14_f beta *
        (∑ k : Fin n,
          |tridiag_L_matrix (higham9_14_roundedMultiplierVec fp T) i k| *
            |tridiag_U_matrix
              (higham9_14_roundedPivotVec fp T) T.c k j|) := by
      simpa [beta] using hDeltaA i j
    _ ≤ higham9_14_f beta * (K * |tridiag_to_matrix T i j|) :=
      mul_le_mul_of_nonneg_left (hgrowth i j) hf_nonneg
    _ ≤ higham9_14_h beta * (K * |tridiag_to_matrix T i j|) :=
      mul_le_mul_of_nonneg_right hfh
        (mul_nonneg hK (abs_nonneg _))
    _ = K * higham9_14_h beta * |tridiag_to_matrix T i j| := by ring

/-! ## Exact-source pivot bridges -/

private theorem higham9_14_exact_LU_super_eq {n : ℕ}
    (L U A : Fin n → Fin n → ℝ)
    (hStruct : IsTridiagLU n L U)
    (hLU_eq : ∀ i j : Fin n, ∑ k : Fin n, L i k * U k j = A i j) :
    ∀ i j : Fin n, i.val + 1 = j.val → U i j = A i j := by
  intro i j hij
  have hsum : ∑ k : Fin n, L i k * U k j = L i i * U i j := by
    apply Finset.sum_eq_single i
    · intro k _ hki
      by_cases h : i.val < k.val
      · rw [hStruct.L_upper_zero i k h, zero_mul]
      · have hk_lt_i : k.val < i.val := by
          have : k.val ≤ i.val := Nat.le_of_not_lt h
          rcases Nat.eq_or_lt_of_le this with h2 | h2
          · exfalso
            exact hki (Fin.ext h2)
          · exact h2
        exact mul_eq_zero_of_right _
          (hStruct.U_upper_bidiag k j (by omega))
    · intro h
      exact absurd (Finset.mem_univ i) h
  rw [← hLU_eq, hsum, hStruct.L_diag, one_mul]

private theorem higham9_14_exact_LU_sub_eq {n : ℕ}
    (L U A : Fin n → Fin n → ℝ)
    (hStruct : IsTridiagLU n L U)
    (hLU_eq : ∀ i j : Fin n, ∑ k : Fin n, L i k * U k j = A i j) :
    ∀ i j : Fin n, j.val + 1 = i.val → L i j * U j j = A i j := by
  intro i j hij
  have hsum : ∑ k : Fin n, L i k * U k j = L i j * U j j := by
    apply Finset.sum_eq_single j
    · intro k _ hkj
      by_cases hki : k.val = i.val
      · rw [show U k j = 0 from hStruct.U_lower_zero k j (by omega),
          mul_zero]
      · by_cases hsub : k.val + 1 = i.val
        · exfalso
          exact hkj (Fin.ext (by omega))
        · by_cases habove : i.val < k.val
          · rw [hStruct.L_upper_zero i k habove, zero_mul]
          · rw [hStruct.L_lower_bidiag i k (by omega), zero_mul]
    · intro h
      exact absurd (Finset.mem_univ j) h
  rw [← hLU_eq, hsum]

private theorem higham9_14_exact_LU_diag_rel {n : ℕ}
    (L U A : Fin n → Fin n → ℝ)
    (hStruct : IsTridiagLU n L U)
    (hLU_eq : ∀ i j : Fin n, ∑ k : Fin n, L i k * U k j = A i j) :
    ∀ i : Fin n,
      A i i = U i i + (if h : 0 < i.val then
        L i ⟨i.val - 1, by omega⟩ * U ⟨i.val - 1, by omega⟩ i
      else 0) := by
  intro i
  have hsum := hLU_eq i i
  have hsum2 : ∑ k : Fin n, L i k * U k i =
      L i i * U i i + ∑ k ∈ Finset.univ.erase i, L i k * U k i := by
    rw [← Finset.add_sum_erase _ _ (Finset.mem_univ i)]
  have hrest : ∑ k ∈ Finset.univ.erase i, L i k * U k i =
      if h : 0 < i.val then
        L i ⟨i.val - 1, by omega⟩ * U ⟨i.val - 1, by omega⟩ i
      else 0 := by
    split
    · rename_i hi
      have hn : i.val - 1 < n := by omega
      let im1 : Fin n := ⟨i.val - 1, hn⟩
      have him1_ne : im1 ≠ i := by
        intro h
        have := congr_arg Fin.val h
        simp [im1] at this
        omega
      have him1_mem : im1 ∈ Finset.univ.erase i :=
        Finset.mem_erase.mpr ⟨him1_ne, Finset.mem_univ _⟩
      have : ∑ k ∈ Finset.univ.erase i, L i k * U k i =
          L i im1 * U im1 i := by
        apply Finset.sum_eq_single_of_mem im1 him1_mem
        intro k hk hk_ne
        have hk_ne_i : k.val ≠ i.val := by
          intro h
          exact ((Finset.mem_erase.mp hk).1) (Fin.ext h)
        by_cases h2 : i.val < k.val
        · rw [hStruct.L_upper_zero i k h2, zero_mul]
        · have hk_ne_im1 : k.val ≠ i.val - 1 := by
            intro h3
            exact hk_ne (Fin.ext (by simp [im1]; omega))
          rw [hStruct.L_lower_bidiag i k (by omega), zero_mul]
      rw [this]
    · rename_i hi
      push_neg at hi
      have hi0 : i.val = 0 := Nat.eq_zero_of_le_zero hi
      apply Finset.sum_eq_zero
      intro k hk
      have hk_ne_i : k.val ≠ i.val := by
        intro h
        exact ((Finset.mem_erase.mp hk).1) (Fin.ext h)
      by_cases h2 : i.val < k.val
      · rw [hStruct.L_upper_zero i k h2, zero_mul]
      · exfalso
        omega
  rw [← hsum, hsum2, hrest, hStruct.L_diag, one_mul]

private theorem higham9_14_abs_add_eq_add_abs_of_mul_nonneg
    (x y : ℝ) (hxy : 0 ≤ x * y) :
    |x + y| = |x| + |y| := by
  by_cases hx0 : x = 0
  · subst x
    simp
  by_cases hx : 0 < x
  · have hy : 0 ≤ y := by
      by_contra hy
      push_neg at hy
      have : x * y < 0 := mul_neg_of_pos_of_neg hx hy
      linarith
    rw [abs_of_pos hx, abs_of_nonneg hy, abs_of_nonneg (add_nonneg hx.le hy)]
  · have hxneg : x < 0 := lt_of_le_of_ne (le_of_not_gt hx) hx0
    have hy : y ≤ 0 := by
      by_contra hy
      push_neg at hy
      have : x * y < 0 := mul_neg_of_neg_of_pos hxneg hy
      linarith
    rw [abs_of_neg hxneg, abs_of_nonpos hy,
      abs_of_nonpos (add_nonpos hxneg.le hy)]
    ring

/-- The diagonal entry of the absolute product of bidiagonal factors has only
the diagonal and predecessor terms.  The corresponding helper in the older
chapter file is private, so the actual-recurrence audit records the statement
locally rather than assuming it. -/
theorem higham9_14_absLU_diag_sum {n : ℕ}
    (L U : Fin n → Fin n → ℝ) (hStruct : IsTridiagLU n L U) :
    ∀ i : Fin n,
      ∑ k : Fin n, |L i k| * |U k i| =
        |U i i| + (if h : 0 < i.val then
          |L i ⟨i.val - 1, by omega⟩| *
            |U ⟨i.val - 1, by omega⟩ i|
        else 0) := by
  intro i
  have hsum2 : ∑ k : Fin n, |L i k| * |U k i| =
      |L i i| * |U i i| +
        ∑ k ∈ Finset.univ.erase i, |L i k| * |U k i| := by
    rw [← Finset.add_sum_erase _ _ (Finset.mem_univ i)]
  have hrest : ∑ k ∈ Finset.univ.erase i, |L i k| * |U k i| =
      if h : 0 < i.val then
        |L i ⟨i.val - 1, by omega⟩| *
          |U ⟨i.val - 1, by omega⟩ i|
      else 0 := by
    split
    · rename_i hi
      have hn : i.val - 1 < n := by omega
      let im1 : Fin n := ⟨i.val - 1, hn⟩
      have him1_ne : im1 ≠ i := by
        intro h
        have := congr_arg Fin.val h
        simp [im1] at this
        omega
      have him1_mem : im1 ∈ Finset.univ.erase i :=
        Finset.mem_erase.mpr ⟨him1_ne, Finset.mem_univ _⟩
      have : ∑ k ∈ Finset.univ.erase i, |L i k| * |U k i| =
          |L i im1| * |U im1 i| := by
        apply Finset.sum_eq_single_of_mem im1 him1_mem
        intro k hk hk_ne
        have hk_ne_i : k.val ≠ i.val := by
          intro h
          exact ((Finset.mem_erase.mp hk).1) (Fin.ext h)
        by_cases h2 : i.val < k.val
        · rw [hStruct.L_upper_zero i k h2, abs_zero, zero_mul]
        · have hk_ne_im1 : k.val ≠ i.val - 1 := by
            intro h3
            exact hk_ne (Fin.ext (by simp [im1]; omega))
          rw [hStruct.L_lower_bidiag i k (by omega), abs_zero, zero_mul]
      rw [this]
    · rename_i hi
      push_neg at hi
      have hi0 : i.val = 0 := Nat.eq_zero_of_le_zero hi
      apply Finset.sum_eq_zero
      intro k hk
      have hk_ne_i : k.val ≠ i.val := by
        intro h
        exact ((Finset.mem_erase.mp hk).1) (Fin.ext h)
      by_cases h2 : i.val < k.val
      · rw [hStruct.L_upper_zero i k h2, abs_zero, zero_mul]
      · exfalso
        omega
  rw [hsum2, hrest, hStruct.L_diag, abs_one, one_mul]

/-- A forward-relative rounded quotient, multiplied back by its nonzero
denominator, has magnitude at most twice that of its numerator when `u < 1`.
This deliberately uses only the primitive `FPModel` division law. -/
theorem higham9_14_fl_div_mul_den_abs_le_two
    (fp : FPModel) {a p : ℝ} (hp : p ≠ 0) (hu1 : fp.u < 1) :
    |fp.fl_div a p * p| ≤ 2 * |a| := by
  obtain ⟨delta, hdelta, hfl⟩ := fp.model_div a p hp
  have hfactor : |1 + delta| ≤ 2 := by
    calc
      |1 + delta| ≤ |(1 : ℝ)| + |delta| := abs_add_le _ _
      _ ≤ 2 := by norm_num; linarith
  have hid : fp.fl_div a p * p = a * (1 + delta) := by
    rw [hfl]
    field_simp [hp]
  rw [hid, abs_mul]
  simpa [mul_comm] using
    (mul_le_mul_of_nonneg_left hfactor (abs_nonneg a))

/-- If a computed denominator is within half the modulus of a nonzero exact
denominator, a forward-relative rounded quotient times any common factor is
at most four times its exact counterpart. -/
theorem higham9_14_fl_div_mul_abs_le_four_exact
    (fp : FPModel) {a c p phat : ℝ}
    (hp : p ≠ 0) (hphat : phat ≠ 0)
    (hclose : |phat - p| < |p| / 2) (hu1 : fp.u < 1) :
    |fp.fl_div a phat * c| ≤ 4 * |(a / p) * c| := by
  have hpabs : 0 < |p| := abs_pos.mpr hp
  have hphatabs : 0 < |phat| := abs_pos.mpr hphat
  have htri : |p| ≤ |phat| + |phat - p| := by
    have heq : p = phat - (phat - p) := by ring
    calc
      |p| = |phat - (phat - p)| := congrArg abs heq
      _ ≤ |phat| + |phat - p| := abs_sub _ _
  have hp_le_two : |p| ≤ 2 * |phat| := by linarith
  have hratio : |p / phat| ≤ 2 := by
    rw [abs_div]
    exact (div_le_iff₀ hphatabs).2 (by simpa [mul_comm] using hp_le_two)
  obtain ⟨delta, hdelta, hfl⟩ := fp.model_div a phat hphat
  have hfactor : |1 + delta| ≤ 2 := by
    calc
      |1 + delta| ≤ |(1 : ℝ)| + |delta| := abs_add_le _ _
      _ ≤ 2 := by norm_num; linarith
  have hid : fp.fl_div a phat * c =
      ((a / p) * c) * (p / phat) * (1 + delta) := by
    rw [hfl]
    field_simp [hp, hphat]
  rw [hid, abs_mul, abs_mul]
  calc
    |(a / p) * c| * |p / phat| * |1 + delta| ≤
        (|(a / p) * c| * 2) * 2 :=
      mul_le_mul
        (mul_le_mul_of_nonneg_left hratio (abs_nonneg _)) hfactor
        (by positivity) (by positivity)
    _ = 4 * |(a / p) * c| := by ring

/-- For the actual rounded bidiagonal factors, entrywise no-cancellation
reduces exactly to the sign of the two terms on each noninitial diagonal.
Off-diagonal entries contain one term and entries outside the tridiagonal band
vanish. -/
theorem higham9_14_actual_noCancellation_of_diagonal_term_sign
    (fp : FPModel) {n : ℕ} (T : TridiagData n)
    (hdiagSign : ∀ i : Fin n, ∀ hi : 0 < i.val,
      0 ≤ higham9_14_roundedPivotVec fp T i *
        (higham9_14_roundedMultiplierVec fp T i *
          T.c (tridiag_prevIndex i hi))) :
    ∀ i j : Fin n,
      (∑ k : Fin n,
        |tridiag_L_matrix (higham9_14_roundedMultiplierVec fp T) i k| *
          |tridiag_U_matrix
            (higham9_14_roundedPivotVec fp T) T.c k j|) =
        |∑ k : Fin n,
          tridiag_L_matrix (higham9_14_roundedMultiplierVec fp T) i k *
            tridiag_U_matrix
              (higham9_14_roundedPivotVec fp T) T.c k j| := by
  intro i j
  let L := tridiag_L_matrix (higham9_14_roundedMultiplierVec fp T)
  let U := tridiag_U_matrix (higham9_14_roundedPivotVec fp T) T.c
  let P := tridiag_to_matrix (higham9_14_roundedProductData fp T)
  have hStruct : IsTridiagLU n L U :=
    tridiag_matrices_isTridiagLU _ _ _
  have hLUeq : ∀ r s : Fin n, ∑ k : Fin n, L r k * U k s = P r s := by
    intro r s
    simpa [L, U, P, higham9_14_roundedProductData] using
      tridiag_exact_product_of_recurrence
        (higham9_14_roundedProductData fp T)
        (higham9_14_roundedMultiplierVec fp T)
        (higham9_14_roundedPivotVec fp T)
        (higham9_14_roundedProductData_recurrence fp T) r s
  have habs_reverse :
      |∑ k : Fin n, L i k * U k j| ≤
        ∑ k : Fin n, |L i k| * |U k j| := by
    calc
      |∑ k : Fin n, L i k * U k j| ≤
          ∑ k : Fin n, |L i k * U k j| := Finset.abs_sum_le_sum_abs _ _
      _ = ∑ k : Fin n, |L i k| * |U k j| := by
        apply Finset.sum_congr rfl
        intro k _
        exact abs_mul _ _
  change (∑ k : Fin n, |L i k| * |U k j|) =
    |∑ k : Fin n, L i k * U k j|
  by_cases hdiag : i = j
  · subst j
    rw [higham9_14_absLU_diag_sum L U hStruct i, hLUeq]
    by_cases hi : 0 < i.val
    · let im1 : Fin n := tridiag_prevIndex i hi
      have him1 : im1.val + 1 = i.val := by
        simp [im1, tridiag_prevIndex]
        omega
      have him1_ne : im1.val ≠ i.val := by omega
      have hlocal := higham9_14_abs_add_eq_add_abs_of_mul_nonneg
        (higham9_14_roundedPivotVec fp T i)
        (higham9_14_roundedMultiplierVec fp T i * T.c im1)
        (hdiagSign i hi)
      have hpred_succ : i.val - 1 + 1 = i.val := by omega
      have hpred_ne : i.val - 1 ≠ i.val := by omega
      have hpred_ne' : i.val ≠ i.val - 1 := by omega
      simpa [P, tridiag_to_matrix, higham9_14_roundedProductData, hi,
        L, U, tridiag_L_matrix, tridiag_U_matrix, im1,
        tridiag_prevIndex, hpred_succ, hpred_ne, hpred_ne', abs_mul] using
          hlocal.symm
    · have hi0 : i.val = 0 := by omega
      simp [P, tridiag_to_matrix, higham9_14_roundedProductData,
        L, U, tridiag_U_matrix, hi, hi0]
  · by_cases hsub : j.val + 1 = i.val
    · have hup :=
        tridiag_bidiag_growth_offdiag_sub L U P hStruct hLUeq i j hsub
      rw [← hLUeq i j] at hup
      exact le_antisymm hup habs_reverse
    · by_cases hsuper : i.val + 1 = j.val
      · have hup :=
          tridiag_bidiag_growth_offdiag_super L U P hStruct hLUeq i j hsuper
        rw [← hLUeq i j] at hup
        exact le_antisymm hup habs_reverse
      · have hPzero : P i j = 0 := by
          simp [P, tridiag_to_matrix,
            show j.val ≠ i.val by intro h; exact hdiag (Fin.ext h.symm),
            hsub, hsuper]
        have hle := tridiag_bidiag_growth_offdiag L U P hStruct hLUeq i j hdiag
        rw [hPzero, abs_zero, mul_zero] at hle
        have hnonneg : 0 ≤ ∑ k : Fin n, |L i k| * |U k j| :=
          Finset.sum_nonneg fun k _ =>
            mul_nonneg (abs_nonneg _) (abs_nonneg _)
        have hsum0 : ∑ k : Fin n, |L i k| * |U k j| = 0 :=
          le_antisymm hle hnonneg
        rw [hLUeq, hPzero, abs_zero, hsum0]

/-- A forward-relative rounded division preserves the sign of its exact
quotient when `u < 1`.  Multiplying by a second numerator-side factor gives
the form needed by the tridiagonal diagonal term. -/
theorem higham9_14_fl_div_mul_nonneg_of_pos_den
    (fp : FPModel) {a c p : ℝ} (hu1 : fp.u < 1)
    (hp : 0 < p) (hac : 0 ≤ a * c) :
    0 ≤ fp.fl_div a p * c := by
  obtain ⟨delta, hdelta, hfl⟩ := fp.model_div a p (ne_of_gt hp)
  have hdelta_lower : -fp.u ≤ delta :=
    neg_le_of_abs_le hdelta
  have hfactor : 0 ≤ 1 + delta := by linarith
  have hbase : 0 ≤ (a / p) * c := by
    rw [show (a / p) * c = (a * c) / p by ring]
    exact div_nonneg hac hp.le
  rw [hfl]
  nlinarith

/-- A positive exact-pivot family, the qualitative rounded sign margin, and
nonnegative products of opposite off-diagonal source entries discharge the
entire actual-factor no-cancellation obligation. -/
theorem higham9_14_actual_noCancellation_of_positive_exact_pivots
    (fp : FPModel) {n : ℕ} (T : TridiagData n)
    (hu1 : fp.u < 1)
    (hexact : ∀ i : Fin n, 0 < higham9_14_exactPivotVec T i)
    (hmargin : ∀ i : Fin n,
      0 < higham9_14_roundedPivotVec fp T i *
        higham9_14_exactPivotVec T i)
    (hoffdiag : ∀ i : Fin n, ∀ hi : 0 < i.val,
      0 ≤ T.a i * T.c (tridiag_prevIndex i hi)) :
    ∀ i j : Fin n,
      (∑ k : Fin n,
        |tridiag_L_matrix (higham9_14_roundedMultiplierVec fp T) i k| *
          |tridiag_U_matrix
            (higham9_14_roundedPivotVec fp T) T.c k j|) =
        |∑ k : Fin n,
          tridiag_L_matrix (higham9_14_roundedMultiplierVec fp T) i k *
            tridiag_U_matrix
              (higham9_14_roundedPivotVec fp T) T.c k j| := by
  apply higham9_14_actual_noCancellation_of_diagonal_term_sign fp T
  intro i hi
  have hrounded_pos : ∀ r : Fin n,
      0 < higham9_14_roundedPivotVec fp T r := by
    intro r
    rcases mul_pos_iff.mp (hmargin r) with h | h
    · exact h.1
    · exact (not_lt_of_ge (hexact r).le h.2).elim
  have him1 := hrounded_pos (tridiag_prevIndex i hi)
  have hlocal :
      0 ≤ higham9_14_roundedMultiplierVec fp T i *
        T.c (tridiag_prevIndex i hi) := by
    rw [higham9_14_roundedMultiplierVec_of_pos fp T i hi]
    exact higham9_14_fl_div_mul_nonneg_of_pos_den fp hu1 him1
      (hoffdiag i hi)
  exact mul_nonneg (hrounded_pos i).le hlocal

/-- Signed version of the rounded-division lemma.  It is the exact primitive
needed for Theorem 9.12(d), whose diagonal sign transformations need not leave
all pivots positive. -/
theorem higham9_14_fl_div_signed_diagonal_nonneg
    (fp : FPModel) {a c p q : ℝ} (hu1 : fp.u < 1)
    (hp : p ≠ 0) (hsign : 0 ≤ q * p * (a * c)) :
    0 ≤ q * (fp.fl_div a p * c) := by
  obtain ⟨delta, hdelta, hfl⟩ := fp.model_div a p hp
  have hfactor : 0 ≤ 1 + delta := by
    have := neg_le_of_abs_le hdelta
    linarith
  have hp2 : 0 < p ^ 2 := sq_pos_of_ne_zero hp
  have hbase : 0 ≤ q * ((a / p) * c) := by
    rw [show q * ((a / p) * c) = (q * p * (a * c)) / p ^ 2 by
      field_simp [hp]]
    exact div_nonneg hsign hp2.le
  rw [hfl]
  calc
    0 ≤ (q * ((a / p) * c)) * (1 + delta) :=
      mul_nonneg hbase hfactor
    _ = q * (((a / p) * (1 + delta)) * c) := by ring

/-- Actual-factor no-cancellation with arbitrary nonzero exact-pivot signs.
The source condition is invariant under diagonal sign equivalence:
`p_i p_{i-1} a_i c_{i-1} ≥ 0`. -/
theorem higham9_14_actual_noCancellation_of_signed_exact_pivots
    (fp : FPModel) {n : ℕ} (T : TridiagData n)
    (hu1 : fp.u < 1)
    (hexact : ∀ i : Fin n, higham9_14_exactPivotVec T i ≠ 0)
    (hmargin : ∀ i : Fin n,
      0 < higham9_14_roundedPivotVec fp T i *
        higham9_14_exactPivotVec T i)
    (hsigned : ∀ i : Fin n, ∀ hi : 0 < i.val,
      0 ≤ higham9_14_exactPivotVec T i *
        higham9_14_exactPivotVec T (tridiag_prevIndex i hi) *
          (T.a i * T.c (tridiag_prevIndex i hi))) :
    ∀ i j : Fin n,
      (∑ k : Fin n,
        |tridiag_L_matrix (higham9_14_roundedMultiplierVec fp T) i k| *
          |tridiag_U_matrix
            (higham9_14_roundedPivotVec fp T) T.c k j|) =
        |∑ k : Fin n,
          tridiag_L_matrix (higham9_14_roundedMultiplierVec fp T) i k *
            tridiag_U_matrix
              (higham9_14_roundedPivotVec fp T) T.c k j| := by
  apply higham9_14_actual_noCancellation_of_diagonal_term_sign fp T
  intro i hi
  let im1 := tridiag_prevIndex i hi
  let ri := higham9_14_roundedPivotVec fp T i
  let rp := higham9_14_roundedPivotVec fp T im1
  let ei := higham9_14_exactPivotVec T i
  let ep := higham9_14_exactPivotVec T im1
  have hri : 0 < ri * ei := hmargin i
  have hrp : 0 < rp * ep := hmargin im1
  have hs : 0 ≤ ei * ep * (T.a i * T.c im1) := hsigned i hi
  have hsquares : 0 < (ei ^ 2) * (ep ^ 2) :=
    mul_pos (sq_pos_of_ne_zero (hexact i))
      (sq_pos_of_ne_zero (hexact im1))
  have hall :
      0 ≤ (ri * rp * (T.a i * T.c im1)) *
        ((ei ^ 2) * (ep ^ 2)) := by
    have hmul : 0 ≤ (ri * ei) * (rp * ep) *
        (ei * ep * (T.a i * T.c im1)) :=
      mul_nonneg (mul_nonneg hri.le hrp.le) hs
    convert hmul using 1 <;> ring
  have hroundedSigned :
      0 ≤ ri * rp * (T.a i * T.c im1) :=
    nonneg_of_mul_nonneg_left hall hsquares
  have hrp_ne : rp ≠ 0 :=
    (mul_ne_zero_iff.mp (ne_of_gt hrp)).1
  rw [show higham9_14_roundedMultiplierVec fp T i =
      fp.fl_div (T.a i) rp by
    simpa [rp, im1] using higham9_14_roundedMultiplierVec_of_pos fp T i hi]
  exact higham9_14_fl_div_signed_diagonal_nonneg fp hu1 hrp_ne
    hroundedSigned

/-- For any nonsingular exact no-pivot LU certificate of the source
tridiagonal matrix, the diagonal of `U` is exactly recurrence (9.19). -/
theorem higham9_14_exactPivotVec_eq_U_diag_of_LUFactSpec {n : ℕ}
    (T : TridiagData n) (L U : Fin n → Fin n → ℝ)
    (hLU : LUFactSpec n (tridiag_to_matrix T) L U)
    (hUdiag : ∀ i : Fin n, U i i ≠ 0) :
    ∀ i : Fin n, higham9_14_exactPivotVec T i = U i i := by
  have hStruct := hLU.isTridiagLU_of_tridiagonal
    (tridiag_to_matrix_isTridiagonal T) hUdiag
  intro i
  induction hi_val : i.val using Nat.strong_induction_on generalizing i with
  | h k ih =>
    by_cases hk : k = 0
    · have hi0 : i.val = 0 := by omega
      have hdiag := higham9_14_exact_LU_diag_rel L U (tridiag_to_matrix T)
        hStruct hLU.product_eq i
      unfold higham9_14_exactPivotVec
      rw [hi0, higham9_14_exactPivot_zero]
      have hd0 : higham9_14_natExtension T.d 0 = T.d i := by
        rw [← hi0]
        exact higham9_14_natExtension_fin T.d i
      rw [hd0]
      simpa [tridiag_to_matrix, hi0] using hdiag
    · have hi : 0 < i.val := by omega
      let ip : Fin n := tridiag_prevIndex i hi
      have hiplt : ip.val < k := by
        simp [ip, tridiag_prevIndex]
        omega
      have ihp : higham9_14_exactPivotVec T ip = U ip ip :=
        ih ip.val hiplt ip rfl
      have hip_succ : ip.val + 1 = i.val := by
        simp [ip, tridiag_prevIndex]
        omega
      have hsub := higham9_14_exact_LU_sub_eq L U (tridiag_to_matrix T)
        hStruct hLU.product_eq i ip hip_succ
      have hsuper := higham9_14_exact_LU_super_eq L U (tridiag_to_matrix T)
        hStruct hLU.product_eq ip i hip_succ
      have hdiag := higham9_14_exact_LU_diag_rel L U (tridiag_to_matrix T)
        hStruct hLU.product_eq i
      have hL : L i ip = T.a i / U ip ip := by
        apply (eq_div_iff (hUdiag ip)).2
        have hip_ne_i : ip.val ≠ i.val := by omega
        simpa [tridiag_to_matrix, hip_ne_i, hip_succ] using hsub
      have hU : U ip i = T.c ip := by
        have hi_ne_ip : i.val ≠ ip.val := by omega
        have hi_succ_ne_ip : i.val + 1 ≠ ip.val := by omega
        simpa [tridiag_to_matrix, hi_ne_ip, hi_succ_ne_ip, hip_succ]
          using hsuper
      have hk_succ : i.val = (i.val - 1) + 1 := by omega
      rw [higham9_14_exactPivotVec, hk_succ, higham9_14_exactPivot_succ]
      simp only [higham9_14_exactMultiplier]
      have hd : higham9_14_natExtension T.d (i.val - 1 + 1) = T.d i := by
        rw [← hk_succ]
        exact higham9_14_natExtension_fin T.d i
      have ha : higham9_14_natExtension T.a (i.val - 1 + 1) = T.a i := by
        rw [← hk_succ]
        exact higham9_14_natExtension_fin T.a i
      have hc : higham9_14_natExtension T.c (i.val - 1) = T.c ip := by
        change higham9_14_natExtension T.c ip.val = T.c ip
        exact higham9_14_natExtension_fin T.c ip
      have hp : higham9_14_exactPivot
          (higham9_14_natExtension T.a)
          (higham9_14_natExtension T.d)
          (higham9_14_natExtension T.c) (i.val - 1) = U ip ip := by
        simpa [higham9_14_exactPivotVec, ip, tridiag_prevIndex] using ihp
      rw [hd, ha, hc, hp, ← hL, ← hU]
      have hdiag' : T.d i = U i i + L i ip * U ip i := by
        simpa [tridiag_to_matrix, hi, ip, tridiag_prevIndex] using hdiag
      linarith

/-- A nonsingular exact no-pivot LU certificate discharges the primitive
nonzero exact-pivot premise without identifying any rounded factor with it. -/
theorem higham9_14_exactPivotVec_ne_zero_of_LUFactSpec {n : ℕ}
    (T : TridiagData n) (L U : Fin n → Fin n → ℝ)
    (hLU : LUFactSpec n (tridiag_to_matrix T) L U)
    (hUdiag : ∀ i : Fin n, U i i ≠ 0) :
    ∀ i : Fin n, higham9_14_exactPivotVec T i ≠ 0 := by
  intro i
  rw [higham9_14_exactPivotVec_eq_U_diag_of_LUFactSpec T L U hLU hUdiag i]
  exact hUdiag i

/-- Nonzero leading principal minors are a source-only sufficient condition
for every exact scalar pivot in (9.19) to be nonzero. -/
theorem higham9_14_exactPivotVec_ne_zero_of_leadingPrincipalBlock_det_ne_zero
    {n : ℕ} (hn : 0 < n) (T : TridiagData n)
    (hlead : ∀ (k : ℕ) (hk : k ≤ n), k ≠ 0 →
      Matrix.det (fun i j : Fin k =>
        tridiag_to_matrix T (Fin.castLE hk i) (Fin.castLE hk j)) ≠ 0) :
    ∀ i : Fin n, higham9_14_exactPivotVec T i ≠ 0 := by
  obtain ⟨L, U, hLU⟩ :=
    higham9_1_lu_exists_of_leadingPrincipalBlock_det_ne_zero
      n (tridiag_to_matrix T) hlead
  have hdet : Matrix.det
      (Matrix.of (tridiag_to_matrix T) : Matrix (Fin n) (Fin n) ℝ) ≠ 0 := by
    simpa using hlead n le_rfl (ne_of_gt hn)
  exact higham9_14_exactPivotVec_ne_zero_of_LUFactSpec T L U hLU
    (hLU.det_ne_zero_iff_U_diag_ne_zero.mp hdet)

/-- Positive leading principal minors make every exact tridiagonal recurrence
pivot strictly positive.  This is the determinant-ratio sign argument, proved
through the repository's exact no-pivot LU existence theorem and the already
formalized leading-minor/product identity. -/
theorem higham9_14_exactPivotVec_pos_of_leadingPrincipalBlock_det_pos
    {n : ℕ} (hn : 0 < n) (T : TridiagData n)
    (hlead : ∀ (k : ℕ) (hk : k ≤ n), k ≠ 0 →
      0 < Matrix.det (fun i j : Fin k =>
        tridiag_to_matrix T (Fin.castLE hk i) (Fin.castLE hk j))) :
    ∀ i : Fin n, 0 < higham9_14_exactPivotVec T i := by
  have hlead_ne : ∀ (k : ℕ) (hk : k ≤ n), k ≠ 0 →
      Matrix.det (fun i j : Fin k =>
        tridiag_to_matrix T (Fin.castLE hk i) (Fin.castLE hk j)) ≠ 0 := by
    intro k hk hk0
    exact ne_of_gt (hlead k hk hk0)
  obtain ⟨L, U, hLU⟩ :=
    higham9_1_lu_exists_of_leadingPrincipalBlock_det_ne_zero
      n (tridiag_to_matrix T) hlead_ne
  have hdet : Matrix.det
      (Matrix.of (tridiag_to_matrix T) : Matrix (Fin n) (Fin n) ℝ) ≠ 0 := by
    simpa using hlead_ne n le_rfl (ne_of_gt hn)
  have hUdiag : ∀ i : Fin n, U i i ≠ 0 :=
    hLU.det_ne_zero_iff_U_diag_ne_zero.mp hdet
  have hpivot_eq :=
    higham9_14_exactPivotVec_eq_U_diag_of_LUFactSpec T L U hLU hUdiag
  intro i
  rw [hpivot_eq i]
  induction hi_val : i.val using Nat.strong_induction_on generalizing i with
  | h m ih =>
      let k := m + 1
      have hk : k ≤ n := by
        dsimp [k]
        omega
      let ilast : Fin k := ⟨m, by simp [k]⟩
      let f : Fin k → ℝ := fun r =>
        U (Fin.castLE hk r) (Fin.castLE hk r)
      have hprod_pos : 0 < ∏ r : Fin k, f r := by
        rw [← higham9_14_LUFactSpec_leadingSubmatrix_det_eq_prod_U_diag
          hLU hk]
        simpa [k] using hlead k hk (by simp [k])
      have hrest_pos :
          0 < ∏ r ∈ Finset.univ.erase ilast, f r := by
        apply Finset.prod_pos
        intro r hr
        have hr_ne : r ≠ ilast := (Finset.mem_erase.mp hr).1
        have hr_ne_val : r.val ≠ m := by
          intro hrm
          exact hr_ne (Fin.ext (by simp [ilast, hrm]))
        have hr_lt : r.val < m := by
          have := r.isLt
          dsimp [k] at this
          omega
        exact ih r.val hr_lt (Fin.castLE hk r) (by simp)
      have hmul := Finset.mul_prod_erase Finset.univ f
        (Finset.mem_univ ilast)
      have hilast : Fin.castLE hk ilast = i := by
        ext
        simp [ilast, hi_val]
      have hlast_pos : 0 < f ilast := by
        by_contra hnot
        push_neg at hnot
        have hnonpos :
            f ilast * (∏ r ∈ Finset.univ.erase ilast, f r) ≤ 0 :=
          mul_nonpos_of_nonpos_of_nonneg hnot hrest_pos.le
        rw [hmul] at hnonpos
        linarith
      simpa [f, hilast] using hlast_pos

/-- Positive definiteness passes to every leading principal block. -/
theorem higham9_14_posDef_leadingPrincipalBlock {n k : ℕ} (hk : k ≤ n)
    (A : Matrix (Fin n) (Fin n) ℝ) (hA : A.PosDef) :
    (A.submatrix (Fin.castLE hk) (Fin.castLE hk)).PosDef := by
  classical
  let e : Fin k → Fin n := Fin.castLE hk
  let B : Matrix (Fin n) (Fin k) ℝ := fun i j => if i = e j then 1 else 0
  have hBinj : Function.Injective B.mulVec := by
    intro x y hxy
    funext j
    have hj := congrFun hxy (e j)
    simpa [B, e, Matrix.mulVec, dotProduct] using hj
  have hpos : (B.conjTranspose * A * B).PosDef :=
    hA.conjTranspose_mul_mul_same hBinj
  have heq : B.conjTranspose * A * B =
      A.submatrix (Fin.castLE hk) (Fin.castLE hk) := by
    ext i j
    simp [B, e, Matrix.mul_apply]
  rwa [heq] at hpos

/-- Every nonempty leading principal minor of an SPD source is positive. -/
theorem higham9_14_leadingPrincipalBlock_det_pos_of_symPosDef {n : ℕ}
    (A : Fin n → Fin n → ℝ) (hSPD : IsSymPosDef n A) :
    ∀ (k : ℕ) (hk : k ≤ n), k ≠ 0 →
      0 < Matrix.det (fun i j : Fin k =>
        A (Fin.castLE hk i) (Fin.castLE hk j)) := by
  intro k hk _hk0
  have hpos := higham9_14_posDef_leadingPrincipalBlock hk (Matrix.of A)
    (isSymPosDef_to_matrix_posDef A hSPD)
  simpa using hpos.det_pos

/-- Theorem 9.12(a) source sign: all exact recurrence pivots of an SPD
tridiagonal source are positive. -/
theorem higham9_14_exactPivotVec_pos_of_symPosDef {n : ℕ}
    (hn : 0 < n) (T : TridiagData n)
    (hSPD : IsSymPosDef n (tridiag_to_matrix T)) :
    ∀ i : Fin n, 0 < higham9_14_exactPivotVec T i := by
  apply higham9_14_exactPivotVec_pos_of_leadingPrincipalBlock_det_pos hn T
  intro k hk hk0
  exact higham9_14_leadingPrincipalBlock_det_pos_of_symPosDef
    (tridiag_to_matrix T) hSPD k hk hk0

/-- Honest Theorem 9.12(a) bridge: an SPD tridiagonal source has no zero
exact recurrence pivot. -/
theorem higham9_14_exactPivotVec_ne_zero_of_symPosDef {n : ℕ}
    (hn : 0 < n) (T : TridiagData n)
    (hSPD : IsSymPosDef n (tridiag_to_matrix T)) :
    ∀ i : Fin n, higham9_14_exactPivotVec T i ≠ 0 := by
  apply higham9_14_exactPivotVec_ne_zero_of_leadingPrincipalBlock_det_ne_zero
    hn T
  intro k hk hk0
  exact ne_of_gt (higham9_14_leadingPrincipalBlock_det_pos_of_symPosDef
    (tridiag_to_matrix T) hSPD k hk hk0)

/-- Honest Theorem 9.12(b) bridge: a nonsingular totally nonnegative
tridiagonal source has no zero exact recurrence pivot. -/
theorem higham9_14_exactPivotVec_ne_zero_of_totalNonnegative {n : ℕ}
    (hn : 0 < n) (T : TridiagData n)
    (hTN : higham9_6_IsTotallyNonnegative (tridiag_to_matrix T))
    (hdet : Matrix.det
      (Matrix.of (tridiag_to_matrix T) : Matrix (Fin n) (Fin n) ℝ) ≠ 0) :
    ∀ i : Fin n, higham9_14_exactPivotVec T i ≠ 0 := by
  apply higham9_14_exactPivotVec_ne_zero_of_leadingPrincipalBlock_det_ne_zero
    hn T
  intro k hk hk0
  exact ne_of_gt
    (higham9_6_leadingPrincipalBlock_det_pos_of_totalNonnegative_det_ne_zero
      n (tridiag_to_matrix T) hTN hdet k hk hk0)

/-- Theorem 9.12(b) source sign: nonsingularity upgrades all leading minors
of a totally nonnegative tridiagonal source to strict positivity, hence every
exact recurrence pivot is positive. -/
theorem higham9_14_exactPivotVec_pos_of_totalNonnegative {n : ℕ}
    (hn : 0 < n) (T : TridiagData n)
    (hTN : higham9_6_IsTotallyNonnegative (tridiag_to_matrix T))
    (hdet : Matrix.det
      (Matrix.of (tridiag_to_matrix T) : Matrix (Fin n) (Fin n) ℝ) ≠ 0) :
    ∀ i : Fin n, 0 < higham9_14_exactPivotVec T i := by
  apply higham9_14_exactPivotVec_pos_of_leadingPrincipalBlock_det_pos hn T
  intro k hk hk0
  exact
    higham9_6_leadingPrincipalBlock_det_pos_of_totalNonnegative_det_ne_zero
      n (tridiag_to_matrix T) hTN hdet k hk hk0

/-- Honest Theorem 9.12(d) determinant bridge: source sign equivalence
preserves nonvanishing of every leading principal minor. -/
theorem higham9_14_leadingPrincipalBlock_det_ne_zero_of_signEquiv {n : ℕ}
    (A B : Fin n → Fin n → ℝ) (hAB : IsSignEquiv n A B)
    (hleadB : ∀ (k : ℕ) (hk : k ≤ n), k ≠ 0 →
      Matrix.det (fun i j : Fin k =>
        B (Fin.castLE hk i) (Fin.castLE hk j)) ≠ 0) :
    ∀ (k : ℕ) (hk : k ≤ n), k ≠ 0 →
      Matrix.det (fun i j : Fin k =>
        A (Fin.castLE hk i) (Fin.castLE hk j)) ≠ 0 := by
  classical
  rcases hAB with ⟨d₁, d₂, hd₁, hd₂, hAB⟩
  have hd₁ne : ∀ i : Fin n, d₁ i ≠ 0 := by
    intro i hi
    have h := hd₁ i
    simp [hi] at h
  have hd₂ne : ∀ i : Fin n, d₂ i ≠ 0 := by
    intro i hi
    have h := hd₂ i
    simp [hi] at h
  intro k hk hk0
  let d₁k : Fin k → ℝ := fun i => d₁ (Fin.castLE hk i)
  let d₂k : Fin k → ℝ := fun i => d₂ (Fin.castLE hk i)
  let D₁ : Matrix (Fin k) (Fin k) ℝ := Matrix.diagonal d₁k
  let D₂ : Matrix (Fin k) (Fin k) ℝ := Matrix.diagonal d₂k
  let Ak : Matrix (Fin k) (Fin k) ℝ := fun i j =>
    A (Fin.castLE hk i) (Fin.castLE hk j)
  let Bk : Matrix (Fin k) (Fin k) ℝ := fun i j =>
    B (Fin.castLE hk i) (Fin.castLE hk j)
  have hAk : Ak = D₁ * Bk * D₂ := by
    ext i j
    rw [show Ak i j = d₁k i * Bk i j * d₂k j by
      simp [Ak, Bk, d₁k, d₂k, hAB]]
    change d₁k i * Bk i j * d₂k j =
      ((Matrix.diagonal d₁k * Bk) * Matrix.diagonal d₂k) i j
    rw [Matrix.mul_diagonal, Matrix.diagonal_mul]
  have hD₁ : Matrix.det D₁ ≠ 0 := by
    rw [show D₁ = Matrix.diagonal d₁k by rfl, Matrix.det_diagonal]
    exact Finset.prod_ne_zero_iff.mpr (by
      intro i _hi
      exact hd₁ne (Fin.castLE hk i))
  have hD₂ : Matrix.det D₂ ≠ 0 := by
    rw [show D₂ = Matrix.diagonal d₂k by rfl, Matrix.det_diagonal]
    exact Finset.prod_ne_zero_iff.mpr (by
      intro i _hi
      exact hd₂ne (Fin.castLE hk i))
  change Matrix.det Ak ≠ 0
  rw [hAk, Matrix.det_mul, Matrix.det_mul]
  exact mul_ne_zero (mul_ne_zero hD₁ (hleadB k hk hk0)) hD₂

/-- Honest Theorem 9.12(d) pivot bridge: if a tridiagonal source is sign
equivalent to a tridiagonal base having nonzero leading principal minors,
then its exact recurrence has no zero pivot.  The premise is source-only and
does not bake the target conclusion into a new class predicate. -/
theorem higham9_14_exactPivotVec_ne_zero_of_signEquiv {n : ℕ}
    (hn : 0 < n) (T B : TridiagData n)
    (hAB : IsSignEquiv n
      (tridiag_to_matrix T) (tridiag_to_matrix B))
    (hleadB : ∀ (k : ℕ) (hk : k ≤ n), k ≠ 0 →
      Matrix.det (fun i j : Fin k =>
        tridiag_to_matrix B (Fin.castLE hk i) (Fin.castLE hk j)) ≠ 0) :
    ∀ i : Fin n, higham9_14_exactPivotVec T i ≠ 0 := by
  apply higham9_14_exactPivotVec_ne_zero_of_leadingPrincipalBlock_det_ne_zero
    hn T
  exact higham9_14_leadingPrincipalBlock_det_ne_zero_of_signEquiv
    (tridiag_to_matrix T) (tridiag_to_matrix B) hAB hleadB

/-- Nonsingular column-diagonally-dominant tridiagonal sources have no zero
exact recurrence pivot. -/
theorem higham9_14_exactPivotVec_ne_zero_of_colDiagDominant {n : ℕ}
    (T : TridiagData n)
    (hdet : Matrix.det
      (Matrix.of (tridiag_to_matrix T) : Matrix (Fin n) (Fin n) ℝ) ≠ 0)
    (hdom : IsDiagDominant n (tridiag_to_matrix T)) :
    ∀ i : Fin n, higham9_14_exactPivotVec T i ≠ 0 := by
  obtain ⟨L, U, hLU, _hL, _hgrowth⟩ :=
    higham9_13_colDiagDom_exists_LUFactSpec_growth_bound_3
      (tridiag_to_matrix T) hdet (tridiag_to_matrix_isTridiagonal T) hdom
  exact higham9_14_exactPivotVec_ne_zero_of_LUFactSpec T L U hLU
    (hLU.det_ne_zero_iff_U_diag_ne_zero.mp hdet)

/-- Nonsingular row-diagonally-dominant tridiagonal sources have no zero
exact recurrence pivot. -/
theorem higham9_14_exactPivotVec_ne_zero_of_rowDiagDominant {n : ℕ}
    (T : TridiagData n)
    (hdet : Matrix.det
      (Matrix.of (tridiag_to_matrix T) : Matrix (Fin n) (Fin n) ℝ) ≠ 0)
    (hdom : IsRowDiagDominant n (tridiag_to_matrix T)) :
    ∀ i : Fin n, higham9_14_exactPivotVec T i ≠ 0 := by
  obtain ⟨L, U, hLU, _hgrowth⟩ :=
    higham9_13_rowDiagDom_exists_LUFactSpec_growth_bound_3
      (tridiag_to_matrix T) hdet (tridiag_to_matrix_isTridiagonal T) hdom
  exact higham9_14_exactPivotVec_ne_zero_of_LUFactSpec T L U hLU
    (hLU.det_ne_zero_iff_U_diag_ne_zero.mp hdet)

/-! ## Audit of the repository's M-matrix predicate -/

/-- The standard M-matrix condition named by Higham: a Z-matrix with a
nonnegative two-sided inverse.  The older repository predicate `IsMMatrix`
contains only the positive-diagonal/nonpositive-off-diagonal clauses. -/
def higham9_14_IsProperMMatrix (n : ℕ)
    (A : Fin n → Fin n → ℝ) : Prop :=
  IsMMatrix n A ∧
    ∃ Ainv : Fin n → Fin n → ℝ,
      IsInverse n A Ainv ∧ ∀ i j : Fin n, 0 ≤ Ainv i j

/-- The trailing principal block of a supplied inverse. -/
noncomputable def higham9_14_properM_tailInverse {m : ℕ}
    (Ainv : Fin (m + 1) → Fin (m + 1) → ℝ) :
    Fin m → Fin m → ℝ := fun i j => Ainv i.succ j.succ

/-- The trailing principal block of `A⁻¹` is a right inverse of the first
Schur complement.  This is the scalar block-inverse identity proved directly
from the repository's finite inverse equations. -/
theorem higham9_14_properM_firstSchur_rightInverse {m : ℕ}
    {A Ainv : Fin (m + 1) → Fin (m + 1) → ℝ}
    (hp : A 0 0 ≠ 0) (hRight : IsRightInverse (m + 1) A Ainv) :
    IsRightInverse m (luFirstSchurComplement A)
      (higham9_14_properM_tailInverse Ainv) := by
  intro i j
  have ht := hRight i.succ j.succ
  have h0 := hRight 0 j.succ
  rw [Fin.sum_univ_succ] at ht h0
  have h0' :
      A 0 0 * Ainv 0 j.succ +
        ∑ k : Fin m, A 0 k.succ * Ainv k.succ j.succ = 0 := by
    simpa using h0
  have ht' :
      A i.succ 0 * Ainv 0 j.succ +
        ∑ k : Fin m, A i.succ k.succ * Ainv k.succ j.succ =
          if i = j then 1 else 0 := by
    simpa [Fin.succ_inj] using ht
  let s0 : ℝ := ∑ k : Fin m, A 0 k.succ * Ainv k.succ j.succ
  let st : ℝ := ∑ k : Fin m, A i.succ k.succ * Ainv k.succ j.succ
  have hs0 : s0 = -A 0 0 * Ainv 0 j.succ := by
    dsimp [s0]
    linarith [h0']
  have hratio : (A i.succ 0 / A 0 0) * s0 =
      -A i.succ 0 * Ainv 0 j.succ := by
    rw [hs0]
    field_simp [hp]
  have hsum :
      (∑ k : Fin m,
        (A i.succ k.succ - A i.succ 0 * A 0 k.succ / A 0 0) *
          Ainv k.succ j.succ) = st - (A i.succ 0 / A 0 0) * s0 := by
    dsimp [st, s0]
    calc
      (∑ k : Fin m,
          (A i.succ k.succ - A i.succ 0 * A 0 k.succ / A 0 0) *
            Ainv k.succ j.succ) =
          ∑ k : Fin m,
            (A i.succ k.succ * Ainv k.succ j.succ -
              (A i.succ 0 / A 0 0) *
                (A 0 k.succ * Ainv k.succ j.succ)) := by
        apply Finset.sum_congr rfl
        intro k _hk
        field_simp [hp]
      _ = (∑ k : Fin m, A i.succ k.succ * Ainv k.succ j.succ) -
          ∑ k : Fin m, (A i.succ 0 / A 0 0) *
            (A 0 k.succ * Ainv k.succ j.succ) := by
        rw [Finset.sum_sub_distrib]
      _ = (∑ k : Fin m, A i.succ k.succ * Ainv k.succ j.succ) -
          (A i.succ 0 / A 0 0) *
            ∑ k : Fin m, A 0 k.succ * Ainv k.succ j.succ := by
        rw [Finset.mul_sum]
  change (∑ k : Fin m,
      (A i.succ k.succ - A i.succ 0 * A 0 k.succ / A 0 0) *
        Ainv k.succ j.succ) = if i = j then 1 else 0
  rw [hsum, hratio]
  dsimp [st] at ht' ⊢
  linarith [ht']

/-- A genuine inverse-positive Z-matrix remains one after the first exact
Schur-complement step.  In particular, positivity of the new diagonal is
derived from the nonnegative trailing inverse, not assumed. -/
theorem higham9_14_properM_firstSchur {m : ℕ}
    {A : Fin (m + 1) → Fin (m + 1) → ℝ}
    (hM : higham9_14_IsProperMMatrix (m + 1) A) :
    higham9_14_IsProperMMatrix m (luFirstSchurComplement A) := by
  classical
  rcases hM with ⟨hZ, Ainv, hInv, hInvNN⟩
  have hp : 0 < A 0 0 := hZ.1 0
  let Sinv : Fin m → Fin m → ℝ :=
    higham9_14_properM_tailInverse Ainv
  have hSinvNN : ∀ i j : Fin m, 0 ≤ Sinv i j := by
    intro i j
    exact hInvNN i.succ j.succ
  have hSright : IsRightInverse m (luFirstSchurComplement A) Sinv := by
    exact higham9_14_properM_firstSchur_rightInverse (ne_of_gt hp) hInv.2
  have hSoff : ∀ i j : Fin m, i ≠ j →
      luFirstSchurComplement A i j ≤ 0 := by
    intro i j hij
    have haij : A i.succ j.succ ≤ 0 := hZ.2 i.succ j.succ (by
      exact fun h => hij (Fin.succ_inj.mp h))
    have hai0 : A i.succ 0 ≤ 0 :=
      hZ.2 i.succ 0 (Fin.succ_ne_zero i)
    have ha0j : A 0 j.succ ≤ 0 :=
      hZ.2 0 j.succ (Ne.symm (Fin.succ_ne_zero j))
    have hcorr : 0 ≤ A i.succ 0 * A 0 j.succ / A 0 0 :=
      div_nonneg (mul_nonneg_of_nonpos_of_nonpos hai0 ha0j) (le_of_lt hp)
    dsimp [luFirstSchurComplement]
    linarith
  have hSdiag : ∀ i : Fin m, 0 < luFirstSchurComplement A i i := by
    intro i
    have hrow := hSright i i
    have hsplit :
        (∑ k : Fin m, luFirstSchurComplement A i k * Sinv k i) =
          luFirstSchurComplement A i i * Sinv i i +
            ∑ k ∈ Finset.univ.erase i,
              luFirstSchurComplement A i k * Sinv k i := by
      rw [← Finset.add_sum_erase _ _ (Finset.mem_univ i)]
    have hrest :
        (∑ k ∈ Finset.univ.erase i,
          luFirstSchurComplement A i k * Sinv k i) ≤ 0 := by
      apply Finset.sum_nonpos
      intro k hk
      exact mul_nonpos_of_nonpos_of_nonneg
        (hSoff i k (Ne.symm (Finset.mem_erase.mp hk).1)) (hSinvNN k i)
    rw [hsplit] at hrow
    simp at hrow
    have hprod : 0 < luFirstSchurComplement A i i * Sinv i i := by
      linarith
    nlinarith [hSinvNN i i]
  have hSleft : IsLeftInverse m (luFirstSchurComplement A) Sinv :=
    isLeftInverse_of_isRightInverse
      (Matrix.of (luFirstSchurComplement A)) (Matrix.of Sinv) hSright
  exact ⟨⟨hSdiag, hSoff⟩, Sinv, ⟨hSleft, hSright⟩, hSinvNN⟩

/-- A source-strength M-matrix has an exact no-pivot LU factorization whose
upper diagonal is strictly positive. -/
theorem higham9_14_properM_exists_LUFactSpec_U_diag_pos :
    ∀ n : ℕ, ∀ A : Fin n → Fin n → ℝ,
      higham9_14_IsProperMMatrix n A →
      ∃ L U : Fin n → Fin n → ℝ,
        LUFactSpec n A L U ∧ ∀ i : Fin n, 0 < U i i := by
  intro n
  induction n with
  | zero =>
      intro A _hM
      let L : Fin 0 → Fin 0 → ℝ := fun i _j => Fin.elim0 i
      let U : Fin 0 → Fin 0 → ℝ := fun i _j => Fin.elim0 i
      refine ⟨L, U, ?_, ?_⟩
      · refine
          { L_diag := ?_
            L_upper_zero := ?_
            U_lower_zero := ?_
            product_eq := ?_ }
        · intro i
          exact Fin.elim0 i
        · intro i _j _h
          exact Fin.elim0 i
        · intro i _j _h
          exact Fin.elim0 i
        · intro i _j
          exact Fin.elim0 i
      · intro i
        exact Fin.elim0 i
  | succ m ih =>
      intro A hM
      have hp : 0 < A 0 0 := hM.1.1 0
      let S : Fin m → Fin m → ℝ := luFirstSchurComplement A
      have hSM : higham9_14_IsProperMMatrix m S := by
        exact higham9_14_properM_firstSchur hM
      obtain ⟨L₁, U₁, hLU₁, hU₁pos⟩ := ih S hSM
      let L : Fin (m + 1) → Fin (m + 1) → ℝ := luFirstStepL A L₁
      let U : Fin (m + 1) → Fin (m + 1) → ℝ := luFirstStepU A U₁
      have hLU : LUFactSpec (m + 1) A L U := by
        exact LUFactSpec.of_firstSchurComplement_explicit (ne_of_gt hp) hLU₁
      refine ⟨L, U, hLU, ?_⟩
      intro i
      by_cases hi : i = 0
      · subst i
        simpa [U, luFirstStepU] using hp
      · have ht := hU₁pos (i.pred hi)
        simpa [U, luFirstStepU, hi] using ht

/-- Honest Theorem 9.12(c) bridge: the standard inverse-positive M-matrix
source predicate yields strictly positive exact recurrence pivots. -/
theorem higham9_14_exactPivotVec_pos_of_properMMatrix {n : ℕ}
    (T : TridiagData n)
    (hM : higham9_14_IsProperMMatrix n (tridiag_to_matrix T)) :
    ∀ i : Fin n, 0 < higham9_14_exactPivotVec T i := by
  obtain ⟨L, U, hLU, hUpos⟩ :=
    higham9_14_properM_exists_LUFactSpec_U_diag_pos
      n (tridiag_to_matrix T) hM
  have hUne : ∀ i : Fin n, U i i ≠ 0 := fun i => ne_of_gt (hUpos i)
  intro i
  rw [higham9_14_exactPivotVec_eq_U_diag_of_LUFactSpec T L U hLU hUne i]
  exact hUpos i

theorem higham9_14_exactPivotVec_ne_zero_of_properMMatrix {n : ℕ}
    (T : TridiagData n)
    (hM : higham9_14_IsProperMMatrix n (tridiag_to_matrix T)) :
    ∀ i : Fin n, higham9_14_exactPivotVec T i ≠ 0 := fun i =>
  ne_of_gt (higham9_14_exactPivotVec_pos_of_properMMatrix T hM i)

/-! The four source classes now feed the actual rounded-pivot margin theorem
without any exact/rounded factor identification. -/

theorem higham9_14_exists_unitRoundoff_threshold_of_symPosDef {n : ℕ}
    (hn : 0 < n) (T : TridiagData n)
    (hSPD : IsSymPosDef n (tridiag_to_matrix T)) :
    ∃ epsilon : ℝ, 0 < epsilon ∧ epsilon ≤ 1 ∧
      ∀ fp : FPModel, fp.u < epsilon →
        ∀ i : Fin n,
          0 < higham9_14_roundedPivotVec fp T i *
            higham9_14_exactPivotVec T i :=
  higham9_14_exists_unitRoundoff_threshold_of_exactPivotVec_ne_zero hn T
    (higham9_14_exactPivotVec_ne_zero_of_symPosDef hn T hSPD)

theorem higham9_14_exists_unitRoundoff_threshold_of_totalNonnegative
    {n : ℕ} (hn : 0 < n) (T : TridiagData n)
    (hTN : higham9_6_IsTotallyNonnegative (tridiag_to_matrix T))
    (hdet : Matrix.det
      (Matrix.of (tridiag_to_matrix T) : Matrix (Fin n) (Fin n) ℝ) ≠ 0) :
    ∃ epsilon : ℝ, 0 < epsilon ∧ epsilon ≤ 1 ∧
      ∀ fp : FPModel, fp.u < epsilon →
        ∀ i : Fin n,
          0 < higham9_14_roundedPivotVec fp T i *
            higham9_14_exactPivotVec T i :=
  higham9_14_exists_unitRoundoff_threshold_of_exactPivotVec_ne_zero hn T
    (higham9_14_exactPivotVec_ne_zero_of_totalNonnegative hn T hTN hdet)

theorem higham9_14_exists_unitRoundoff_threshold_of_properMMatrix
    {n : ℕ} (hn : 0 < n) (T : TridiagData n)
    (hM : higham9_14_IsProperMMatrix n (tridiag_to_matrix T)) :
    ∃ epsilon : ℝ, 0 < epsilon ∧ epsilon ≤ 1 ∧
      ∀ fp : FPModel, fp.u < epsilon →
        ∀ i : Fin n,
          0 < higham9_14_roundedPivotVec fp T i *
            higham9_14_exactPivotVec T i :=
  higham9_14_exists_unitRoundoff_threshold_of_exactPivotVec_ne_zero hn T
    (higham9_14_exactPivotVec_ne_zero_of_properMMatrix T hM)

/-- Compact name for the corrected source-relative conclusion produced by the
actual tridiagonal recurrence and the two actual sparse solves. -/
def higham9_14_ActualCorrectedSourceBound (fp : FPModel) {n : ℕ}
    (T : TridiagData n) (b : Fin n → ℝ) : Prop :=
  ∃ DeltaA : Fin n → Fin n → ℝ,
    (∀ i j, |DeltaA i j| ≤
      higham9_14_h (fp.u / (1 - fp.u)) * |tridiag_to_matrix T i j|) ∧
    (∀ i,
      ∑ j : Fin n, (tridiag_to_matrix T i j + DeltaA i j) *
        higham9_21_upperSolve fp
          (higham9_14_roundedPivotVec fp T) T.c
          (higham9_21_lowerSolve fp
            (higham9_14_roundedMultiplierVec fp T) b) j = b i)

/-- Generic source-class closure theorem.  Positive exact pivots and
nonnegative opposite-offdiagonal products are precisely the source facts used
to obtain actual-factor no-cancellation; no rounded factor is identified with
an exact source factor. -/
theorem higham9_14_exists_threshold_actual_source_h_corrected_of_positive_pivots
    {n : ℕ} (hn : 0 < n) (T : TridiagData n) (b : Fin n → ℝ)
    (hexact : ∀ i : Fin n, 0 < higham9_14_exactPivotVec T i)
    (hoffdiag : ∀ i : Fin n, ∀ hi : 0 < i.val,
      0 ≤ T.a i * T.c (tridiag_prevIndex i hi)) :
    ∃ epsilon : ℝ, 0 < epsilon ∧
      ∀ fp : FPModel, fp.u < epsilon →
        higham9_14_ActualCorrectedSourceBound fp T b := by
  obtain ⟨epsilon₀, hepsilon₀, _hepsilon_le_one, hmargin⟩ :=
    higham9_14_exists_unitRoundoff_threshold_of_exactPivotVec_ne_zero
      hn T (fun i => ne_of_gt (hexact i))
  let epsilon := min epsilon₀ ((1 : ℝ) / 2)
  have hepsilon : 0 < epsilon := lt_min hepsilon₀ (by norm_num)
  refine ⟨epsilon, hepsilon, ?_⟩
  intro fp hfp
  have hfp₀ : fp.u < epsilon₀ := hfp.trans_le (min_le_left _ _)
  have hu_half : fp.u < (1 : ℝ) / 2 :=
    hfp.trans_le (min_le_right _ _)
  have hu1 : fp.u < 1 := by linarith
  have hpivot : ∀ i : Fin n,
      higham9_14_roundedPivotVec fp T i ≠ 0 := by
    intro i
    exact (mul_ne_zero_iff.mp (ne_of_gt (hmargin fp hfp₀ i))).1
  have hNoCancellation :=
    higham9_14_actual_noCancellation_of_positive_exact_pivots
      fp T hu1 hexact (hmargin fp hfp₀) hoffdiag
  exact higham9_14_actual_tridiag_source_h_bound_corrected_of_noCancellation
    fp T b hu_half hpivot hNoCancellation

/-- Signed-pivot version of the generic corrected source-class closure.  This
is the invariant form consumed by diagonal sign-equivalent sources. -/
theorem higham9_14_exists_threshold_actual_source_h_corrected_of_signed_pivots
    {n : ℕ} (hn : 0 < n) (T : TridiagData n) (b : Fin n → ℝ)
    (hexact : ∀ i : Fin n, higham9_14_exactPivotVec T i ≠ 0)
    (hsigned : ∀ i : Fin n, ∀ hi : 0 < i.val,
      0 ≤ higham9_14_exactPivotVec T i *
        higham9_14_exactPivotVec T (tridiag_prevIndex i hi) *
          (T.a i * T.c (tridiag_prevIndex i hi))) :
    ∃ epsilon : ℝ, 0 < epsilon ∧
      ∀ fp : FPModel, fp.u < epsilon →
        higham9_14_ActualCorrectedSourceBound fp T b := by
  obtain ⟨epsilon₀, hepsilon₀, _hepsilon_le_one, hmargin⟩ :=
    higham9_14_exists_unitRoundoff_threshold_of_exactPivotVec_ne_zero
      hn T hexact
  let epsilon := min epsilon₀ ((1 : ℝ) / 2)
  have hepsilon : 0 < epsilon := lt_min hepsilon₀ (by norm_num)
  refine ⟨epsilon, hepsilon, ?_⟩
  intro fp hfp
  have hfp₀ : fp.u < epsilon₀ := hfp.trans_le (min_le_left _ _)
  have hu_half : fp.u < (1 : ℝ) / 2 :=
    hfp.trans_le (min_le_right _ _)
  have hu1 : fp.u < 1 := by linarith
  have hpivot : ∀ i : Fin n,
      higham9_14_roundedPivotVec fp T i ≠ 0 := by
    intro i
    exact (mul_ne_zero_iff.mp (ne_of_gt (hmargin fp hfp₀ i))).1
  have hNoCancellation :=
    higham9_14_actual_noCancellation_of_signed_exact_pivots
      fp T hu1 hexact (hmargin fp hfp₀) hsigned
  exact higham9_14_actual_tridiag_source_h_bound_corrected_of_noCancellation
    fp T b hu_half hpivot hNoCancellation

/-- Corrected actual-recurrence Theorem 9.14(a), directly from an SPD
tridiagonal source. -/
theorem higham9_14_exists_threshold_actual_source_h_corrected_of_symPosDef
    {n : ℕ} (hn : 0 < n) (T : TridiagData n) (b : Fin n → ℝ)
    (hSPD : IsSymPosDef n (tridiag_to_matrix T)) :
    ∃ epsilon : ℝ, 0 < epsilon ∧
      ∀ fp : FPModel, fp.u < epsilon →
        higham9_14_ActualCorrectedSourceBound fp T b := by
  apply higham9_14_exists_threshold_actual_source_h_corrected_of_positive_pivots
    hn T b (higham9_14_exactPivotVec_pos_of_symPosDef hn T hSPD)
  intro i hi
  let im1 := tridiag_prevIndex i hi
  have him1 : im1.val + 1 = i.val := by
    simp [im1, tridiag_prevIndex]
    omega
  have him1_ne : im1.val ≠ i.val := by omega
  have hi_ne : i.val ≠ im1.val := by omega
  have hsym := hSPD.1 i im1
  have hac : T.a i = T.c im1 := by
    simpa [tridiag_to_matrix, him1, him1_ne, hi_ne,
      show i.val + 1 ≠ im1.val by omega] using hsym
  rw [hac]
  exact mul_self_nonneg _

/-- Corrected actual-recurrence Theorem 9.14(b), directly from a nonsingular
totally nonnegative tridiagonal source. -/
theorem higham9_14_exists_threshold_actual_source_h_corrected_of_totalNonnegative
    {n : ℕ} (hn : 0 < n) (T : TridiagData n) (b : Fin n → ℝ)
    (hTN : higham9_6_IsTotallyNonnegative (tridiag_to_matrix T))
    (hdet : Matrix.det
      (Matrix.of (tridiag_to_matrix T) : Matrix (Fin n) (Fin n) ℝ) ≠ 0) :
    ∃ epsilon : ℝ, 0 < epsilon ∧
      ∀ fp : FPModel, fp.u < epsilon →
        higham9_14_ActualCorrectedSourceBound fp T b := by
  apply higham9_14_exists_threshold_actual_source_h_corrected_of_positive_pivots
    hn T b (higham9_14_exactPivotVec_pos_of_totalNonnegative hn T hTN hdet)
  intro i hi
  let im1 := tridiag_prevIndex i hi
  have him1 : im1.val + 1 = i.val := by
    simp [im1, tridiag_prevIndex]
    omega
  have him1_ne : im1.val ≠ i.val := by omega
  have hi_ne : i.val ≠ im1.val := by omega
  have ha : 0 ≤ T.a i := by
    simpa [tridiag_to_matrix, him1, him1_ne, hi_ne,
      show i.val + 1 ≠ im1.val by omega] using
      higham9_6_totalNonnegative_entry_nonneg hTN i im1
  have hc : 0 ≤ T.c im1 := by
    simpa [tridiag_to_matrix, him1, him1_ne, hi_ne,
      show i.val + 1 ≠ im1.val by omega] using
      higham9_6_totalNonnegative_entry_nonneg hTN im1 i
  exact mul_nonneg ha hc

/-- Corrected actual-recurrence Theorem 9.14(c), directly from the genuine
inverse-positive M-matrix predicate. -/
theorem higham9_14_exists_threshold_actual_source_h_corrected_of_properMMatrix
    {n : ℕ} (hn : 0 < n) (T : TridiagData n) (b : Fin n → ℝ)
    (hM : higham9_14_IsProperMMatrix n (tridiag_to_matrix T)) :
    ∃ epsilon : ℝ, 0 < epsilon ∧
      ∀ fp : FPModel, fp.u < epsilon →
        higham9_14_ActualCorrectedSourceBound fp T b := by
  apply higham9_14_exists_threshold_actual_source_h_corrected_of_positive_pivots
    hn T b (higham9_14_exactPivotVec_pos_of_properMMatrix T hM)
  intro i hi
  let im1 := tridiag_prevIndex i hi
  have him1 : im1.val + 1 = i.val := by
    simp [im1, tridiag_prevIndex]
    omega
  have him1_ne : im1 ≠ i := by
    intro h
    have := congrArg Fin.val h
    omega
  have haA := hM.1.2 i im1 (Ne.symm him1_ne)
  have hcA := hM.1.2 im1 i him1_ne
  have ha : T.a i ≤ 0 := by
    simpa [tridiag_to_matrix, him1,
      show im1.val ≠ i.val by omega,
      show i.val ≠ im1.val by omega,
      show i.val + 1 ≠ im1.val by omega] using haA
  have hc : T.c im1 ≤ 0 := by
    simpa [tridiag_to_matrix, him1,
      show im1.val ≠ i.val by omega,
      show i.val ≠ im1.val by omega,
      show i.val + 1 ≠ im1.val by omega] using hcA
  exact mul_nonneg_of_nonpos_of_nonpos ha hc

/-- Source-facing exact Theorem 9.12 core for every tridiagonal class whose
recurrence pivots are positive and whose opposite off-diagonal products are
nonnegative.  The witnesses are the concrete exact-primitive recurrence
factors, and both `LUFactSpec` and `|L||U| = |A|` are produced. -/
theorem higham9_12_exists_LUFactSpec_absLU_eq_of_positive_pivots
    {n : ℕ} (T : TridiagData n)
    (hexact : ∀ i : Fin n, 0 < higham9_14_exactPivotVec T i)
    (hoffdiag : ∀ i : Fin n, ∀ hi : 0 < i.val,
      0 ≤ T.a i * T.c (tridiag_prevIndex i hi)) :
    ∃ L U : Fin n → Fin n → ℝ,
      LUFactSpec n (tridiag_to_matrix T) L U ∧
        ∀ i j : Fin n,
          ∑ k : Fin n, |L i k| * |U k j| =
            |tridiag_to_matrix T i j| := by
  let L := tridiag_L_matrix
    (higham9_14_roundedMultiplierVec higham9_14_exactFPModel T)
  let U := tridiag_U_matrix
    (higham9_14_roundedPivotVec higham9_14_exactFPModel T) T.c
  have hproduct : ∀ i j : Fin n,
      ∑ k : Fin n, L i k * U k j = tridiag_to_matrix T i j := by
    intro i j
    change ∑ k : Fin n,
        tridiag_L_matrix
            (higham9_14_roundedMultiplierVec higham9_14_exactFPModel T) i k *
          tridiag_U_matrix
            (higham9_14_roundedPivotVec higham9_14_exactFPModel T) T.c k j =
      tridiag_to_matrix T i j
    exact higham9_14_exactFP_product_eq_source T
      (fun r => ne_of_gt (hexact r)) i j
  have hmargin : ∀ i : Fin n,
      0 < higham9_14_roundedPivotVec higham9_14_exactFPModel T i *
        higham9_14_exactPivotVec T i := by
    intro i
    rw [higham9_14_roundedPivotVec_exactFPModel_eq]
    exact mul_self_pos.mpr (ne_of_gt (hexact i))
  have hNoCancellation :=
    higham9_14_actual_noCancellation_of_positive_exact_pivots
      higham9_14_exactFPModel T (by change (0 : ℝ) < 1; norm_num)
      hexact hmargin hoffdiag
  refine ⟨L, U, ?_, ?_⟩
  · refine
      { L_diag := ?_
        L_upper_zero := ?_
        U_lower_zero := ?_
        product_eq := hproduct }
    · exact tridiag_L_diag _
    · exact tridiag_L_upper_zero _
    · exact tridiag_U_lower_zero _ _
  · intro i j
    rw [show (∑ k : Fin n, |L i k| * |U k j|) =
        |∑ k : Fin n, L i k * U k j| by
      simpa [L, U] using hNoCancellation i j]
    rw [hproduct i j]

/-- Literal Theorem 9.12(a) source endpoint for SPD tridiagonal matrices. -/
theorem higham9_12_symPosDef_exists_LUFactSpec_absLU_eq
    {n : ℕ} (hn : 0 < n) (T : TridiagData n)
    (hSPD : IsSymPosDef n (tridiag_to_matrix T)) :
    ∃ L U : Fin n → Fin n → ℝ,
      LUFactSpec n (tridiag_to_matrix T) L U ∧
        ∀ i j : Fin n,
          ∑ k : Fin n, |L i k| * |U k j| =
            |tridiag_to_matrix T i j| := by
  apply higham9_12_exists_LUFactSpec_absLU_eq_of_positive_pivots T
    (higham9_14_exactPivotVec_pos_of_symPosDef hn T hSPD)
  intro i hi
  let im1 := tridiag_prevIndex i hi
  have him1 : im1.val + 1 = i.val := by
    simp [im1, tridiag_prevIndex]
    omega
  have hsym := hSPD.1 i im1
  have hac : T.a i = T.c im1 := by
    simpa [tridiag_to_matrix, him1,
      show im1.val ≠ i.val by omega,
      show i.val ≠ im1.val by omega,
      show i.val + 1 ≠ im1.val by omega] using hsym
  rw [hac]
  exact mul_self_nonneg _

/-- Literal Theorem 9.12(b) source endpoint for nonsingular totally
nonnegative tridiagonal matrices. -/
theorem higham9_12_totalNonnegative_exists_LUFactSpec_absLU_eq
    {n : ℕ} (hn : 0 < n) (T : TridiagData n)
    (hTN : higham9_6_IsTotallyNonnegative (tridiag_to_matrix T))
    (hdet : Matrix.det
      (Matrix.of (tridiag_to_matrix T) : Matrix (Fin n) (Fin n) ℝ) ≠ 0) :
    ∃ L U : Fin n → Fin n → ℝ,
      LUFactSpec n (tridiag_to_matrix T) L U ∧
        ∀ i j : Fin n,
          ∑ k : Fin n, |L i k| * |U k j| =
            |tridiag_to_matrix T i j| := by
  apply higham9_12_exists_LUFactSpec_absLU_eq_of_positive_pivots T
    (higham9_14_exactPivotVec_pos_of_totalNonnegative hn T hTN hdet)
  intro i hi
  let im1 := tridiag_prevIndex i hi
  have him1 : im1.val + 1 = i.val := by
    simp [im1, tridiag_prevIndex]
    omega
  have ha : 0 ≤ T.a i := by
    simpa [tridiag_to_matrix, him1,
      show im1.val ≠ i.val by omega,
      show i.val ≠ im1.val by omega,
      show i.val + 1 ≠ im1.val by omega] using
      higham9_6_totalNonnegative_entry_nonneg hTN i im1
  have hc : 0 ≤ T.c im1 := by
    simpa [tridiag_to_matrix, him1,
      show im1.val ≠ i.val by omega,
      show i.val ≠ im1.val by omega,
      show i.val + 1 ≠ im1.val by omega] using
      higham9_6_totalNonnegative_entry_nonneg hTN im1 i
  exact mul_nonneg ha hc

/-- Literal Theorem 9.12(c) source endpoint for the genuine inverse-positive
M-matrix predicate. -/
theorem higham9_12_properMMatrix_exists_LUFactSpec_absLU_eq
    {n : ℕ} (T : TridiagData n)
    (hM : higham9_14_IsProperMMatrix n (tridiag_to_matrix T)) :
    ∃ L U : Fin n → Fin n → ℝ,
      LUFactSpec n (tridiag_to_matrix T) L U ∧
        ∀ i j : Fin n,
          ∑ k : Fin n, |L i k| * |U k j| =
            |tridiag_to_matrix T i j| := by
  apply higham9_12_exists_LUFactSpec_absLU_eq_of_positive_pivots T
    (higham9_14_exactPivotVec_pos_of_properMMatrix T hM)
  intro i hi
  let im1 := tridiag_prevIndex i hi
  have him1 : im1.val + 1 = i.val := by
    simp [im1, tridiag_prevIndex]
    omega
  have him1_ne : im1 ≠ i := by
    intro h
    have := congrArg Fin.val h
    omega
  have haA := hM.1.2 i im1 (Ne.symm him1_ne)
  have hcA := hM.1.2 im1 i him1_ne
  have ha : T.a i ≤ 0 := by
    simpa [tridiag_to_matrix, him1,
      show im1.val ≠ i.val by omega,
      show i.val ≠ im1.val by omega,
      show i.val + 1 ≠ im1.val by omega] using haA
  have hc : T.c im1 ≤ 0 := by
    simpa [tridiag_to_matrix, him1,
      show im1.val ≠ i.val by omega,
      show i.val ≠ im1.val by omega,
      show i.val + 1 ≠ im1.val by omega] using hcA
  exact mul_nonneg_of_nonpos_of_nonpos ha hc

/-- Nonsingularity is preserved in the forward direction by source sign
equivalence. -/
theorem higham9_14_det_ne_zero_of_signEquiv {n : ℕ}
    (A B : Fin n → Fin n → ℝ) (hAB : IsSignEquiv n A B)
    (hdetB : Matrix.det (Matrix.of B : Matrix (Fin n) (Fin n) ℝ) ≠ 0) :
    Matrix.det (Matrix.of A : Matrix (Fin n) (Fin n) ℝ) ≠ 0 := by
  classical
  rcases hAB with ⟨d₁, d₂, hd₁, hd₂, hA⟩
  let D₁ : Matrix (Fin n) (Fin n) ℝ := Matrix.diagonal d₁
  let D₂ : Matrix (Fin n) (Fin n) ℝ := Matrix.diagonal d₂
  have hmatrix : (Matrix.of A : Matrix (Fin n) (Fin n) ℝ) =
      D₁ * Matrix.of B * D₂ := by
    ext i j
    change A i j = ((D₁ * Matrix.of B) * D₂) i j
    rw [Matrix.mul_diagonal, Matrix.diagonal_mul]
    exact hA i j
  have hD₁ : Matrix.det D₁ ≠ 0 := by
    rw [show D₁ = Matrix.diagonal d₁ by rfl, Matrix.det_diagonal]
    exact Finset.prod_ne_zero_iff.mpr (by
      intro i _
      intro hi
      have := hd₁ i
      simp [hi] at this)
  have hD₂ : Matrix.det D₂ ≠ 0 := by
    rw [show D₂ = Matrix.diagonal d₂ by rfl, Matrix.det_diagonal]
    exact Finset.prod_ne_zero_iff.mpr (by
      intro i _
      intro hi
      have := hd₂ i
      simp [hi] at this)
  rw [hmatrix, Matrix.det_mul, Matrix.det_mul]
  exact mul_ne_zero (mul_ne_zero hD₁ hdetB) hD₂

/-- Sign equivalence is symmetric because every diagonal sign is its own
inverse. -/
theorem higham9_14_IsSignEquiv_symm {n : ℕ}
    {A B : Fin n → Fin n → ℝ} (hAB : IsSignEquiv n A B) :
    IsSignEquiv n B A := by
  rcases hAB with ⟨d₁, d₂, hd₁, hd₂, hA⟩
  refine ⟨d₁, d₂, hd₁, hd₂, ?_⟩
  intro i j
  have hd₁sq : d₁ i * d₁ i = 1 := by
    nlinarith [sq_abs (d₁ i), hd₁ i]
  have hd₂sq : d₂ j * d₂ j = 1 := by
    nlinarith [sq_abs (d₂ j), hd₂ j]
  rw [hA i j]
  calc
    B i j = (d₁ i * d₁ i) * B i j * (d₂ j * d₂ j) := by
      rw [hd₁sq, hd₂sq]
      ring
    _ = d₁ i * (d₁ i * B i j * d₂ j) * d₂ j := by ring

theorem higham9_14_det_ne_zero_iff_of_signEquiv {n : ℕ}
    (A B : Fin n → Fin n → ℝ) (hAB : IsSignEquiv n A B) :
    Matrix.det (Matrix.of A : Matrix (Fin n) (Fin n) ℝ) ≠ 0 ↔
      Matrix.det (Matrix.of B : Matrix (Fin n) (Fin n) ℝ) ≠ 0 := by
  constructor
  · exact higham9_14_det_ne_zero_of_signEquiv B A
      (higham9_14_IsSignEquiv_symm hAB)
  · exact higham9_14_det_ne_zero_of_signEquiv A B hAB

/-- Unit-lower factor transported by a left diagonal sign. -/
def higham9_14_signEquivL {n : ℕ} (d₁ : Fin n → ℝ)
    (L : Fin n → Fin n → ℝ) : Fin n → Fin n → ℝ :=
  fun i k => d₁ i * L i k * d₁ k

/-- Upper factor transported by the left and right diagonal signs. -/
def higham9_14_signEquivU {n : ℕ} (d₁ d₂ : Fin n → ℝ)
    (U : Fin n → Fin n → ℝ) : Fin n → Fin n → ℝ :=
  fun k j => d₁ k * U k j * d₂ j

/-- Exact LU transport retaining the explicit transformed factors. -/
theorem higham9_14_signEquiv_LUFactSpec_transform {n : ℕ}
    (A B L U : Fin n → Fin n → ℝ) (d₁ d₂ : Fin n → ℝ)
    (hd₁ : ∀ i : Fin n, |d₁ i| = 1)
    (_hd₂ : ∀ j : Fin n, |d₂ j| = 1)
    (hA : ∀ i j : Fin n, A i j = d₁ i * B i j * d₂ j)
    (hLU : LUFactSpec n B L U) :
    LUFactSpec n A (higham9_14_signEquivL d₁ L)
      (higham9_14_signEquivU d₁ d₂ U) := by
  classical
  have hd₁sq : ∀ i : Fin n, d₁ i * d₁ i = 1 := by
    intro i
    nlinarith [sq_abs (d₁ i), hd₁ i]
  refine
    { L_diag := ?_
      L_upper_zero := ?_
      U_lower_zero := ?_
      product_eq := ?_ }
  · intro i
    simp [higham9_14_signEquivL, hLU.L_diag i, hd₁sq i]
  · intro i j hij
    simp [higham9_14_signEquivL, hLU.L_upper_zero i j hij]
  · intro i j hij
    simp [higham9_14_signEquivU, hLU.U_lower_zero i j hij]
  · intro i j
    calc
      ∑ k : Fin n,
          higham9_14_signEquivL d₁ L i k *
            higham9_14_signEquivU d₁ d₂ U k j =
          ∑ k : Fin n, d₁ i * (L i k * U k j) * d₂ j := by
        apply Finset.sum_congr rfl
        intro k _
        simp only [higham9_14_signEquivL, higham9_14_signEquivU]
        calc
          (d₁ i * L i k * d₁ k) * (d₁ k * U k j * d₂ j) =
              d₁ i * (L i k * U k j) * d₂ j *
                (d₁ k * d₁ k) := by ring
          _ = d₁ i * (L i k * U k j) * d₂ j := by
            rw [hd₁sq k]
            ring
      _ = d₁ i * (∑ k : Fin n, L i k * U k j) * d₂ j := by
        rw [Finset.mul_sum, Finset.sum_mul]
      _ = A i j := by rw [hLU.product_eq i j, hA i j]

/-- The signed exact-pivot/offdiagonal invariant is preserved by literal
diagonal sign equivalence from a positive-pivot base class. -/
theorem higham9_14_signed_pivots_of_signEquiv_positive_base {n : ℕ}
    (T B : TridiagData n)
    (hAB : IsSignEquiv n (tridiag_to_matrix T) (tridiag_to_matrix B))
    (hBpos : ∀ i : Fin n, 0 < higham9_14_exactPivotVec B i)
    (hBoffdiag : ∀ i : Fin n, ∀ hi : 0 < i.val,
      0 ≤ B.a i * B.c (tridiag_prevIndex i hi)) :
    (∀ i : Fin n, higham9_14_exactPivotVec T i ≠ 0) ∧
      ∀ i : Fin n, ∀ hi : 0 < i.val,
        0 ≤ higham9_14_exactPivotVec T i *
          higham9_14_exactPivotVec T (tridiag_prevIndex i hi) *
            (T.a i * T.c (tridiag_prevIndex i hi)) := by
  rcases hAB with ⟨d₁, d₂, hd₁, hd₂, hA⟩
  let L_B := tridiag_L_matrix
    (higham9_14_roundedMultiplierVec higham9_14_exactFPModel B)
  let U_B := tridiag_U_matrix
    (higham9_14_roundedPivotVec higham9_14_exactFPModel B) B.c
  have hLU_B : LUFactSpec n (tridiag_to_matrix B) L_B U_B := by
    simpa [L_B, U_B] using higham9_14_exactFP_LUFactSpec B
      (fun i => ne_of_gt (hBpos i))
  let L_A := higham9_14_signEquivL d₁ L_B
  let U_A := higham9_14_signEquivU d₁ d₂ U_B
  have hLU_A : LUFactSpec n (tridiag_to_matrix T) L_A U_A := by
    exact higham9_14_signEquiv_LUFactSpec_transform _ _ L_B U_B d₁ d₂
      hd₁ hd₂ hA hLU_B
  have hU_A_diag : ∀ r : Fin n,
      U_A r r = d₁ r * higham9_14_exactPivotVec B r * d₂ r := by
    intro r
    change d₁ r * U_B r r * d₂ r =
      d₁ r * higham9_14_exactPivotVec B r * d₂ r
    rw [show U_B r r = higham9_14_exactPivotVec B r by
      simp [U_B, tridiag_U_matrix]]
  have hU_A_ne : ∀ r : Fin n, U_A r r ≠ 0 := by
    intro r
    have hd₁ne : d₁ r ≠ 0 := by
      intro h
      have := hd₁ r
      simp [h] at this
    have hd₂ne : d₂ r ≠ 0 := by
      intro h
      have := hd₂ r
      simp [h] at this
    rw [hU_A_diag r]
    exact mul_ne_zero (mul_ne_zero hd₁ne (ne_of_gt (hBpos r))) hd₂ne
  have hpivotT : ∀ r : Fin n,
      higham9_14_exactPivotVec T r =
        d₁ r * higham9_14_exactPivotVec B r * d₂ r := by
    intro r
    rw [higham9_14_exactPivotVec_eq_U_diag_of_LUFactSpec
      T L_A U_A hLU_A hU_A_ne r]
    exact hU_A_diag r
  refine ⟨fun r => by
    rw [hpivotT r, ← hU_A_diag r]
    exact hU_A_ne r, ?_⟩
  intro i hi
  let im1 := tridiag_prevIndex i hi
  have him1 : im1.val + 1 = i.val := by
    simp [im1, tridiag_prevIndex]
    omega
  have ha : T.a i = d₁ i * B.a i * d₂ im1 := by
    simpa [tridiag_to_matrix, him1,
      show im1.val ≠ i.val by omega,
      show i.val ≠ im1.val by omega,
      show i.val + 1 ≠ im1.val by omega] using hA i im1
  have hc : T.c im1 = d₁ im1 * B.c im1 * d₂ i := by
    simpa [tridiag_to_matrix, him1,
      show im1.val ≠ i.val by omega,
      show i.val ≠ im1.val by omega,
      show i.val + 1 ≠ im1.val by omega] using hA im1 i
  have hd₁sq : ∀ r : Fin n, d₁ r * d₁ r = 1 := by
    intro r
    nlinarith [sq_abs (d₁ r), hd₁ r]
  have hd₂sq : ∀ r : Fin n, d₂ r * d₂ r = 1 := by
    intro r
    nlinarith [sq_abs (d₂ r), hd₂ r]
  rw [hpivotT i, hpivotT im1, ha, hc]
  calc
    (d₁ i * higham9_14_exactPivotVec B i * d₂ i) *
          (d₁ im1 * higham9_14_exactPivotVec B im1 * d₂ im1) *
        ((d₁ i * B.a i * d₂ im1) * (d₁ im1 * B.c im1 * d₂ i)) =
      (d₁ i * d₁ i) * (d₂ i * d₂ i) *
        (d₁ im1 * d₁ im1) * (d₂ im1 * d₂ im1) *
          (higham9_14_exactPivotVec B i *
            higham9_14_exactPivotVec B im1 * (B.a i * B.c im1)) := by ring
    _ = higham9_14_exactPivotVec B i *
          higham9_14_exactPivotVec B im1 * (B.a i * B.c im1) := by
      rw [hd₁sq i, hd₂sq i, hd₁sq im1, hd₂sq im1]
      ring
    _ ≥ 0 := mul_nonneg
      (mul_pos (hBpos i) (hBpos im1)).le (hBoffdiag i hi)

/-- Corrected actual-recurrence Theorem 9.14(d), SPD-base branch. -/
theorem higham9_14_exists_threshold_actual_source_h_corrected_of_signEquiv_symPosDef
    {n : ℕ} (hn : 0 < n) (T B : TridiagData n) (b : Fin n → ℝ)
    (hAB : IsSignEquiv n (tridiag_to_matrix T) (tridiag_to_matrix B))
    (hSPD : IsSymPosDef n (tridiag_to_matrix B)) :
    ∃ epsilon : ℝ, 0 < epsilon ∧
      ∀ fp : FPModel, fp.u < epsilon →
        higham9_14_ActualCorrectedSourceBound fp T b := by
  have hBpos := higham9_14_exactPivotVec_pos_of_symPosDef hn B hSPD
  have hBoff : ∀ i : Fin n, ∀ hi : 0 < i.val,
      0 ≤ B.a i * B.c (tridiag_prevIndex i hi) := by
    intro i hi
    let im1 := tridiag_prevIndex i hi
    have him1 : im1.val + 1 = i.val := by
      simp [im1, tridiag_prevIndex]
      omega
    have hsym := hSPD.1 i im1
    have hac : B.a i = B.c im1 := by
      simpa [tridiag_to_matrix, him1,
        show im1.val ≠ i.val by omega,
        show i.val ≠ im1.val by omega,
        show i.val + 1 ≠ im1.val by omega] using hsym
    rw [hac]
    exact mul_self_nonneg _
  obtain ⟨hTne, hTsigned⟩ :=
    higham9_14_signed_pivots_of_signEquiv_positive_base T B hAB hBpos hBoff
  exact higham9_14_exists_threshold_actual_source_h_corrected_of_signed_pivots
    hn T b hTne hTsigned

/-- Corrected actual-recurrence Theorem 9.14(d), totally-nonnegative-base
branch.  The printed nonsingularity premise is on the source and is
transported to the base. -/
theorem higham9_14_exists_threshold_actual_source_h_corrected_of_signEquiv_totalNonnegative
    {n : ℕ} (hn : 0 < n) (T B : TridiagData n) (b : Fin n → ℝ)
    (hAB : IsSignEquiv n (tridiag_to_matrix T) (tridiag_to_matrix B))
    (hTN : higham9_6_IsTotallyNonnegative (tridiag_to_matrix B))
    (hdetA : Matrix.det
      (Matrix.of (tridiag_to_matrix T) : Matrix (Fin n) (Fin n) ℝ) ≠ 0) :
    ∃ epsilon : ℝ, 0 < epsilon ∧
      ∀ fp : FPModel, fp.u < epsilon →
        higham9_14_ActualCorrectedSourceBound fp T b := by
  have hdetB := (higham9_14_det_ne_zero_iff_of_signEquiv
    (tridiag_to_matrix T) (tridiag_to_matrix B) hAB).mp hdetA
  have hBpos :=
    higham9_14_exactPivotVec_pos_of_totalNonnegative hn B hTN hdetB
  have hBoff : ∀ i : Fin n, ∀ hi : 0 < i.val,
      0 ≤ B.a i * B.c (tridiag_prevIndex i hi) := by
    intro i hi
    let im1 := tridiag_prevIndex i hi
    have him1 : im1.val + 1 = i.val := by
      simp [im1, tridiag_prevIndex]
      omega
    have ha : 0 ≤ B.a i := by
      simpa [tridiag_to_matrix, him1,
        show im1.val ≠ i.val by omega,
        show i.val ≠ im1.val by omega,
        show i.val + 1 ≠ im1.val by omega] using
        higham9_6_totalNonnegative_entry_nonneg hTN i im1
    have hc : 0 ≤ B.c im1 := by
      simpa [tridiag_to_matrix, him1,
        show im1.val ≠ i.val by omega,
        show i.val ≠ im1.val by omega,
        show i.val + 1 ≠ im1.val by omega] using
        higham9_6_totalNonnegative_entry_nonneg hTN im1 i
    exact mul_nonneg ha hc
  obtain ⟨hTne, hTsigned⟩ :=
    higham9_14_signed_pivots_of_signEquiv_positive_base T B hAB hBpos hBoff
  exact higham9_14_exists_threshold_actual_source_h_corrected_of_signed_pivots
    hn T b hTne hTsigned

/-- Corrected actual-recurrence Theorem 9.14(d), proper-M-matrix-base branch. -/
theorem higham9_14_exists_threshold_actual_source_h_corrected_of_signEquiv_properMMatrix
    {n : ℕ} (hn : 0 < n) (T B : TridiagData n) (b : Fin n → ℝ)
    (hAB : IsSignEquiv n (tridiag_to_matrix T) (tridiag_to_matrix B))
    (hM : higham9_14_IsProperMMatrix n (tridiag_to_matrix B)) :
    ∃ epsilon : ℝ, 0 < epsilon ∧
      ∀ fp : FPModel, fp.u < epsilon →
        higham9_14_ActualCorrectedSourceBound fp T b := by
  have hBpos := higham9_14_exactPivotVec_pos_of_properMMatrix B hM
  have hBoff : ∀ i : Fin n, ∀ hi : 0 < i.val,
      0 ≤ B.a i * B.c (tridiag_prevIndex i hi) := by
    intro i hi
    let im1 := tridiag_prevIndex i hi
    have him1 : im1.val + 1 = i.val := by
      simp [im1, tridiag_prevIndex]
      omega
    have him1_ne : im1 ≠ i := by
      intro h
      have := congrArg Fin.val h
      omega
    have haA := hM.1.2 i im1 (Ne.symm him1_ne)
    have hcA := hM.1.2 im1 i him1_ne
    have ha : B.a i ≤ 0 := by
      simpa [tridiag_to_matrix, him1,
        show im1.val ≠ i.val by omega,
        show i.val ≠ im1.val by omega,
        show i.val + 1 ≠ im1.val by omega] using haA
    have hc : B.c im1 ≤ 0 := by
      simpa [tridiag_to_matrix, him1,
        show im1.val ≠ i.val by omega,
        show i.val ≠ im1.val by omega,
        show i.val + 1 ≠ im1.val by omega] using hcA
    exact mul_nonneg_of_nonpos_of_nonpos ha hc
  obtain ⟨hTne, hTsigned⟩ :=
    higham9_14_signed_pivots_of_signEquiv_positive_base T B hAB hBpos hBoff
  exact higham9_14_exists_threshold_actual_source_h_corrected_of_signed_pivots
    hn T b hTne hTsigned

/-- Exact LU and optimal componentwise growth transport across the literal
Theorem 9.12(d) sign-equivalence relation.  The transformed lower factor is
renormalized with the left sign on both sides, preserving its unit diagonal. -/
theorem higham9_12_signEquiv_exists_LUFactSpec_absLU_eq {n : ℕ}
    (A B : Fin n → Fin n → ℝ) (hAB : IsSignEquiv n A B)
    (hbase : ∃ L_B U_B : Fin n → Fin n → ℝ,
      LUFactSpec n B L_B U_B ∧
        ∀ i j : Fin n,
          ∑ k : Fin n, |L_B i k| * |U_B k j| = |B i j|) :
    ∃ L_A U_A : Fin n → Fin n → ℝ,
      LUFactSpec n A L_A U_A ∧
        ∀ i j : Fin n,
          ∑ k : Fin n, |L_A i k| * |U_A k j| = |A i j| := by
  classical
  rcases hAB with ⟨d₁, d₂, hd₁, hd₂, hA⟩
  obtain ⟨L_B, U_B, hLU_B, hgrowth_B⟩ := hbase
  let L_A : Fin n → Fin n → ℝ := fun i k => d₁ i * L_B i k * d₁ k
  let U_A : Fin n → Fin n → ℝ := fun k j => d₁ k * U_B k j * d₂ j
  have hd₁sq : ∀ i : Fin n, d₁ i * d₁ i = 1 := by
    intro i
    nlinarith [sq_abs (d₁ i), hd₁ i]
  have hproduct : ∀ i j : Fin n,
      ∑ k : Fin n, L_A i k * U_A k j = A i j := by
    intro i j
    calc
      ∑ k : Fin n, L_A i k * U_A k j =
          ∑ k : Fin n, d₁ i * (L_B i k * U_B k j) * d₂ j := by
        apply Finset.sum_congr rfl
        intro k _
        dsimp [L_A, U_A]
        calc
          (d₁ i * L_B i k * d₁ k) * (d₁ k * U_B k j * d₂ j) =
              d₁ i * (L_B i k * U_B k j) * d₂ j *
                (d₁ k * d₁ k) := by ring
          _ = d₁ i * (L_B i k * U_B k j) * d₂ j := by
            rw [hd₁sq k]
            ring
      _ = d₁ i * (∑ k : Fin n, L_B i k * U_B k j) * d₂ j := by
        rw [Finset.mul_sum, Finset.sum_mul]
      _ = A i j := by rw [hLU_B.product_eq i j, hA i j]
  have hLU_A : LUFactSpec n A L_A U_A := by
    refine
      { L_diag := ?_
        L_upper_zero := ?_
        U_lower_zero := ?_
        product_eq := hproduct }
    · intro i
      simp [L_A, hLU_B.L_diag i, hd₁sq i]
    · intro i j hij
      simp [L_A, hLU_B.L_upper_zero i j hij]
    · intro i j hij
      simp [U_A, hLU_B.U_lower_zero i j hij]
  refine ⟨L_A, U_A, hLU_A, ?_⟩
  intro i j
  calc
    ∑ k : Fin n, |L_A i k| * |U_A k j| =
        ∑ k : Fin n, |L_B i k| * |U_B k j| := by
      apply Finset.sum_congr rfl
      intro k _
      simp [L_A, U_A, abs_mul, hd₁ i, hd₁ k, hd₂ j]
    _ = |B i j| := hgrowth_B i j
    _ = |A i j| := by
      rw [hA i j, abs_mul, abs_mul, hd₁ i, hd₂ j, one_mul, mul_one]

/-- Literal Theorem 9.12(d), SPD-base branch. -/
theorem higham9_12_signEquiv_symPosDef_exists_LUFactSpec_absLU_eq
    {n : ℕ} (hn : 0 < n) (T B : TridiagData n)
    (hAB : IsSignEquiv n (tridiag_to_matrix T) (tridiag_to_matrix B))
    (hSPD : IsSymPosDef n (tridiag_to_matrix B)) :
    ∃ L U : Fin n → Fin n → ℝ,
      LUFactSpec n (tridiag_to_matrix T) L U ∧
        ∀ i j : Fin n, ∑ k : Fin n, |L i k| * |U k j| =
          |tridiag_to_matrix T i j| :=
  higham9_12_signEquiv_exists_LUFactSpec_absLU_eq _ _ hAB
    (higham9_12_symPosDef_exists_LUFactSpec_absLU_eq hn B hSPD)

/-- Literal Theorem 9.12(d), totally-nonnegative-base branch.  Nonsingularity
is supplied on the source `A` exactly as printed and transferred to the base. -/
theorem higham9_12_signEquiv_totalNonnegative_exists_LUFactSpec_absLU_eq
    {n : ℕ} (hn : 0 < n) (T B : TridiagData n)
    (hAB : IsSignEquiv n (tridiag_to_matrix T) (tridiag_to_matrix B))
    (hTN : higham9_6_IsTotallyNonnegative (tridiag_to_matrix B))
    (hdetA : Matrix.det
      (Matrix.of (tridiag_to_matrix T) : Matrix (Fin n) (Fin n) ℝ) ≠ 0) :
    ∃ L U : Fin n → Fin n → ℝ,
      LUFactSpec n (tridiag_to_matrix T) L U ∧
        ∀ i j : Fin n, ∑ k : Fin n, |L i k| * |U k j| =
          |tridiag_to_matrix T i j| := by
  apply higham9_12_signEquiv_exists_LUFactSpec_absLU_eq _ _ hAB
  apply higham9_12_totalNonnegative_exists_LUFactSpec_absLU_eq hn B hTN
  exact (higham9_14_det_ne_zero_iff_of_signEquiv
    (tridiag_to_matrix T) (tridiag_to_matrix B) hAB).mp hdetA

/-- Literal Theorem 9.12(d), proper-M-matrix-base branch. -/
theorem higham9_12_signEquiv_properMMatrix_exists_LUFactSpec_absLU_eq
    {n : ℕ} (T B : TridiagData n)
    (hAB : IsSignEquiv n (tridiag_to_matrix T) (tridiag_to_matrix B))
    (hM : higham9_14_IsProperMMatrix n (tridiag_to_matrix B)) :
    ∃ L U : Fin n → Fin n → ℝ,
      LUFactSpec n (tridiag_to_matrix T) L U ∧
        ∀ i j : Fin n, ∑ k : Fin n, |L i k| * |U k j| =
          |tridiag_to_matrix T i j| :=
  higham9_12_signEquiv_exists_LUFactSpec_absLU_eq _ _ hAB
    (higham9_12_properMMatrix_exists_LUFactSpec_absLU_eq B hM)

theorem higham9_14_exists_unitRoundoff_threshold_of_signEquiv {n : ℕ}
    (hn : 0 < n) (T B : TridiagData n)
    (hAB : IsSignEquiv n
      (tridiag_to_matrix T) (tridiag_to_matrix B))
    (hleadB : ∀ (k : ℕ) (hk : k ≤ n), k ≠ 0 →
      Matrix.det (fun i j : Fin k =>
        tridiag_to_matrix B (Fin.castLE hk i) (Fin.castLE hk j)) ≠ 0) :
    ∃ epsilon : ℝ, 0 < epsilon ∧ epsilon ≤ 1 ∧
      ∀ fp : FPModel, fp.u < epsilon →
        ∀ i : Fin n,
          0 < higham9_14_roundedPivotVec fp T i *
            higham9_14_exactPivotVec T i :=
  higham9_14_exists_unitRoundoff_threshold_of_exactPivotVec_ne_zero hn T
    (higham9_14_exactPivotVec_ne_zero_of_signEquiv hn T B hAB hleadB)

/-! ## Bare-model obstruction to the unrestricted diagonal-dominant clause -/

/-- A valid unit-roundoff-one model in which every subtraction is rounded to
zero.  The forward-relative law permits this through the witness `delta=-1`. -/
noncomputable def higham9_14_unitSubtractionZeroModel : FPModel where
  u := 1
  u_nonneg := by norm_num
  fl_add := fun x y => x + y
  fl_sub := fun _ _ => 0
  fl_mul := fun x y => x * y
  fl_div := fun x y => x / y
  fl_sqrt := fun x => Real.sqrt x
  fl_add_zero := by intro x; ring
  model_add := by
    intro x y
    exact ⟨0, by norm_num, by ring⟩
  model_sub := by
    intro x y
    exact ⟨-1, by norm_num, by ring⟩
  model_mul := by
    intro x y
    exact ⟨0, by norm_num, by ring⟩
  model_div := by
    intro x y _hy
    exact ⟨0, by norm_num, by ring⟩
  model_sqrt := by
    intro x _hx
    exact ⟨0, by norm_num, by ring⟩

/-- Two-by-two identity data, used as a nonsingular row- and
column-diagonally-dominant witness. -/
noncomputable def higham9_14_diagDominantCounterexampleData : TridiagData 2 where
  a := fun _ => 0
  d := fun _ => 1
  c := fun _ => 0

theorem higham9_14_diagDominantCounterexample_row :
    IsRowDiagDominant 2
      (tridiag_to_matrix higham9_14_diagDominantCounterexampleData) := by
  intro i
  fin_cases i <;>
    norm_num [IsRowDiagDominant, tridiag_to_matrix,
      higham9_14_diagDominantCounterexampleData]

theorem higham9_14_diagDominantCounterexample_col :
    IsDiagDominant 2
      (tridiag_to_matrix higham9_14_diagDominantCounterexampleData) := by
  intro j
  fin_cases j <;>
    norm_num [IsDiagDominant, tridiag_to_matrix,
      higham9_14_diagDominantCounterexampleData]

theorem higham9_14_diagDominantCounterexample_det_ne_zero :
    Matrix.det
      (Matrix.of (tridiag_to_matrix higham9_14_diagDominantCounterexampleData) :
        Matrix (Fin 2) (Fin 2) ℝ) ≠ 0 := by
  rw [Matrix.det_fin_two]
  norm_num [tridiag_to_matrix, higham9_14_diagDominantCounterexampleData]

theorem higham9_14_diagDominantCounterexample_roundedPivot_one_eq_zero :
    higham9_14_roundedPivotVec higham9_14_unitSubtractionZeroModel
      higham9_14_diagDominantCounterexampleData (1 : Fin 2) = 0 := by
  norm_num [higham9_14_roundedPivotVec, higham9_14_roundedPivot,
    higham9_14_roundedMultiplier, higham9_14_natExtension,
    higham9_14_unitSubtractionZeroModel,
    higham9_14_diagDominantCounterexampleData]

/-- Formal discrepancy witness for the last sentence of Theorem 9.14: source
diagonal dominance and nonsingularity do not give unrestricted nonbreakdown
for every instance of the repository's bare `FPModel`. -/
theorem higham9_14_diagDominant_unrestricted_nonbreakdown_not_from_bare_FPModel :
    ¬ (∀ (fp : FPModel) {n : ℕ} (T : TridiagData n),
      Matrix.det
          (Matrix.of (tridiag_to_matrix T) : Matrix (Fin n) (Fin n) ℝ) ≠ 0 →
      (IsRowDiagDominant n (tridiag_to_matrix T) ∨
        IsDiagDominant n (tridiag_to_matrix T)) →
      ∀ i : Fin n, higham9_14_roundedPivotVec fp T i ≠ 0) := by
  intro h
  exact (h higham9_14_unitSubtractionZeroModel
      higham9_14_diagDominantCounterexampleData
      higham9_14_diagDominantCounterexample_det_ne_zero
      (Or.inl higham9_14_diagDominantCounterexample_row) (1 : Fin 2))
    higham9_14_diagDominantCounterexample_roundedPivot_one_eq_zero

/-- A genuinely small-unit-roundoff (`u=0.1`) bare model in which division and
multiplication both round upward by their full permitted relative error. -/
noncomputable def higham9_14_tenthRoundUpMulDivModel : FPModel where
  u := (1 : ℝ) / 10
  u_nonneg := by norm_num
  fl_add := fun x y => x + y
  fl_sub := fun x y => x - y
  fl_mul := fun x y => (x * y) * ((11 : ℝ) / 10)
  fl_div := fun x y => (x / y) * ((11 : ℝ) / 10)
  fl_sqrt := fun x => Real.sqrt x
  fl_add_zero := by intro x; ring
  model_add := by
    intro x y
    exact ⟨0, by norm_num, by ring⟩
  model_sub := by
    intro x y
    exact ⟨0, by norm_num, by ring⟩
  model_mul := by
    intro x y
    exact ⟨(1 : ℝ) / 10, by norm_num, by ring⟩
  model_div := by
    intro x y _hy
    exact ⟨(1 : ℝ) / 10, by norm_num, by ring⟩
  model_sqrt := by
    intro x _hx
    exact ⟨0, by norm_num, by ring⟩

/-- The matrix `[[1,1],[1,1.21]]`: nonsingular and diagonally dominant in
both directions, but tailored to the two full upward roundings above. -/
noncomputable def higham9_14_smallUDiagDominantCounterexampleData :
    TridiagData 2 where
  a := fun i => if i.val = 0 then 0 else 1
  d := fun i => if i.val = 0 then 1 else (121 : ℝ) / 100
  c := fun i => if i.val = 0 then 1 else 0

theorem higham9_14_tenthRoundUpMulDivModel_u_lt_half :
    higham9_14_tenthRoundUpMulDivModel.u < (1 : ℝ) / 2 := by
  norm_num [higham9_14_tenthRoundUpMulDivModel]

theorem higham9_14_smallUDiagDominantCounterexample_row :
    IsRowDiagDominant 2
      (tridiag_to_matrix higham9_14_smallUDiagDominantCounterexampleData) := by
  intro i
  fin_cases i <;>
    norm_num [IsRowDiagDominant, tridiag_to_matrix,
      higham9_14_smallUDiagDominantCounterexampleData]

theorem higham9_14_smallUDiagDominantCounterexample_col :
    IsDiagDominant 2
      (tridiag_to_matrix higham9_14_smallUDiagDominantCounterexampleData) := by
  intro j
  fin_cases j <;>
    norm_num [IsDiagDominant, tridiag_to_matrix,
      higham9_14_smallUDiagDominantCounterexampleData]

theorem higham9_14_smallUDiagDominantCounterexample_det_ne_zero :
    Matrix.det
      (Matrix.of
        (tridiag_to_matrix higham9_14_smallUDiagDominantCounterexampleData) :
          Matrix (Fin 2) (Fin 2) ℝ) ≠ 0 := by
  rw [Matrix.det_fin_two]
  norm_num [tridiag_to_matrix,
    higham9_14_smallUDiagDominantCounterexampleData]

theorem higham9_14_smallUDiagDominantCounterexample_roundedPivot_one_eq_zero :
    higham9_14_roundedPivotVec higham9_14_tenthRoundUpMulDivModel
      higham9_14_smallUDiagDominantCounterexampleData (1 : Fin 2) = 0 := by
  norm_num [higham9_14_roundedPivotVec, higham9_14_roundedPivot,
    higham9_14_roundedMultiplier, higham9_14_natExtension,
    higham9_14_tenthRoundUpMulDivModel,
    higham9_14_smallUDiagDominantCounterexampleData] <;> rfl

/-- Even restricting the bare model to `u < 1/2`, nonsingular row/column
diagonal dominance does not guarantee nonbreakdown of the actual recurrence. -/
theorem higham9_14_diagDominant_small_u_nonbreakdown_not_from_bare_FPModel :
    ¬ (∀ (fp : FPModel), fp.u < (1 : ℝ) / 2 →
      ∀ {n : ℕ} (T : TridiagData n),
        Matrix.det
            (Matrix.of (tridiag_to_matrix T) : Matrix (Fin n) (Fin n) ℝ) ≠ 0 →
        (IsRowDiagDominant n (tridiag_to_matrix T) ∨
          IsDiagDominant n (tridiag_to_matrix T)) →
        ∀ i : Fin n, higham9_14_roundedPivotVec fp T i ≠ 0) := by
  intro h
  exact (h higham9_14_tenthRoundUpMulDivModel
      higham9_14_tenthRoundUpMulDivModel_u_lt_half
      higham9_14_smallUDiagDominantCounterexampleData
      higham9_14_smallUDiagDominantCounterexample_det_ne_zero
      (Or.inl higham9_14_smallUDiagDominantCounterexample_row) (1 : Fin 2))
    higham9_14_smallUDiagDominantCounterexample_roundedPivot_one_eq_zero

/-- A nonsingular tridiagonal Z-matrix satisfying the repository's weak
`IsMMatrix` predicate but having a zero second exact pivot:

`[[1,-1,0],[-1,1,-1],[0,-1,1]]`.

Its determinant is `-1`, while its leading `2 x 2` determinant is zero. -/
noncomputable def higham9_14_weakMMatrixCounterexampleData : TridiagData 3 where
  a := fun i => if i.val = 0 then 0 else -1
  d := fun _ => 1
  c := fun i => if i.val < 2 then -1 else 0

theorem higham9_14_weakMMatrixCounterexample_isMMatrix :
    IsMMatrix 3
      (tridiag_to_matrix higham9_14_weakMMatrixCounterexampleData) := by
  constructor
  · intro i
    fin_cases i <;>
      norm_num [tridiag_to_matrix, higham9_14_weakMMatrixCounterexampleData]
  · intro i j hij
    fin_cases i
    all_goals fin_cases j
    all_goals
      norm_num [tridiag_to_matrix,
        higham9_14_weakMMatrixCounterexampleData] at *

theorem higham9_14_weakMMatrixCounterexample_det_ne_zero :
    Matrix.det
      (Matrix.of (tridiag_to_matrix higham9_14_weakMMatrixCounterexampleData) :
        Matrix (Fin 3) (Fin 3) ℝ) ≠ 0 := by
  rw [Matrix.det_fin_three]
  simp [tridiag_to_matrix, higham9_14_weakMMatrixCounterexampleData]

theorem higham9_14_weakMMatrixCounterexample_exactPivot_one_eq_zero :
    higham9_14_exactPivotVec higham9_14_weakMMatrixCounterexampleData
      (1 : Fin 3) = 0 := by
  simp [higham9_14_exactPivotVec, higham9_14_exactPivot,
    higham9_14_natExtension, higham9_14_weakMMatrixCounterexampleData]

/-- Therefore the repository's current `IsMMatrix` plus nonsingularity is
strictly too weak to discharge the no-breakdown premise of Theorem 9.14. -/
theorem higham9_14_weak_IsMMatrix_nonsingular_does_not_force_exact_pivots :
    ¬ (∀ {n : ℕ} (T : TridiagData n),
      IsMMatrix n (tridiag_to_matrix T) →
      Matrix.det
          (Matrix.of (tridiag_to_matrix T) : Matrix (Fin n) (Fin n) ℝ) ≠ 0 →
      ∀ i : Fin n, higham9_14_exactPivotVec T i ≠ 0) := by
  intro h
  exact (h higham9_14_weakMMatrixCounterexampleData
      higham9_14_weakMMatrixCounterexample_isMMatrix
      higham9_14_weakMMatrixCounterexample_det_ne_zero (1 : Fin 3))
    higham9_14_weakMMatrixCounterexample_exactPivot_one_eq_zero

end NumStability
