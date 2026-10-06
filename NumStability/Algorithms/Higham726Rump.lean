/-
Copyright (c) 2026.
Released under Apache 2.0 license as described in LICENSES/Apache-2.0.txt.
SPDX-License-Identifier: Apache-2.0
See LICENSES/Apache-2.0.txt.
Authors: QED94 contributors
-/

import NumStability.Algorithms.HighamChapters1To9SourceClosure
import Mathlib.Analysis.Polynomial.Basic
import Mathlib.Algebra.Order.Field.GeomSum
import Mathlib.Data.Fintype.Pigeonhole
import Mathlib.LinearAlgebra.Matrix.Charpoly.Basic
import Mathlib.LinearAlgebra.Matrix.Charpoly.Coeff
import Mathlib.LinearAlgebra.Matrix.ToLinearEquiv
import Mathlib.Logic.Equiv.Fin.Rotate

/-!
# Rump's cycle construction for Higham's equation (7.26)

This module formalizes the reusable finite-dimensional ingredients in Rump's
proof that an ill-conditioned matrix is componentwise near singularity.  The
first group of lemmas is the sign-real spectral-radius argument of Rump's
Theorem 3.1: a componentwise lower growth bound can be converted into an
ordinary real eigenpair after signing the rows.
-/

namespace NumStability

open Filter
open scoped BigOperators Topology

/-- Multiplication of the rows of a real matrix by the entries of `d`. -/
def higham7_26_rowScale {n : ℕ}
    (d : Fin n → ℝ) (A : Fin n → Fin n → ℝ) :
    Fin n → Fin n → ℝ :=
  fun i j ↦ d i * A i j

/-- Multiplication of the columns of a real matrix by the entries of `s`. -/
def higham7_26_columnScale {n : ℕ}
    (A : Fin n → Fin n → ℝ) (s : Fin n → ℝ) :
    Fin n → Fin n → ℝ :=
  fun i j ↦ A i j * s j

@[simp]
lemma higham7_26_columnScale_mulVec {n : ℕ}
    (A : Fin n → Fin n → ℝ) (s x : Fin n → ℝ) :
    matMulVec n (higham7_26_columnScale A s) x =
      matMulVec n A (fun j ↦ s j * x j) := by
  funext i
  unfold matMulVec higham7_26_columnScale
  apply Finset.sum_congr rfl
  intro j _
  ring

/-- The characteristic determinant of a row-scaled matrix. -/
def higham7_26_rowScaledCharDet {n : ℕ}
    (A : Fin n → Fin n → ℝ) (r : ℝ) (d : Fin n → ℝ) : ℝ :=
  (Matrix.scalar (Fin n) r - Matrix.of (higham7_26_rowScale d A)).det

@[simp]
lemma higham7_26_rowScale_mulVec {n : ℕ}
    (d : Fin n → ℝ) (A : Fin n → Fin n → ℝ) (x : Fin n → ℝ) :
    Matrix.mulVec (Matrix.of (higham7_26_rowScale d A) :
        Matrix (Fin n) (Fin n) ℝ) x =
      fun i ↦ d i * matMulVec n A x i := by
  funext i
  unfold Matrix.mulVec dotProduct matMulVec
  rw [Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro j _
  simp [higham7_26_rowScale]
  ring

@[simp]
lemma higham7_26_rowScale_matMulVec {n : ℕ}
    (d : Fin n → ℝ) (A : Fin n → Fin n → ℝ) (x : Fin n → ℝ) :
    matMulVec n (higham7_26_rowScale d A) x =
      fun i ↦ d i * matMulVec n A x i := by
  funext i
  unfold matMulVec higham7_26_rowScale
  rw [Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro j _
  ring

/-- Replacing one row multiplier by a convex combination gives the same
convex combination of characteristic determinants. -/
lemma higham7_26_rowScaledCharDet_update_convex {n : ℕ}
    (A : Fin n → Fin n → ℝ) (r θ a b : ℝ)
    (d : Fin n → ℝ) (i : Fin n) :
    higham7_26_rowScaledCharDet A r
        (Function.update d i (θ * a + (1 - θ) * b)) =
      θ * higham7_26_rowScaledCharDet A r (Function.update d i a) +
        (1 - θ) *
          higham7_26_rowScaledCharDet A r (Function.update d i b) := by
  classical
  let B : Matrix (Fin n) (Fin n) ℝ :=
    Matrix.scalar (Fin n) r - Matrix.of (higham7_26_rowScale d A)
  let row : ℝ → Fin n → ℝ := fun c j ↦
    (Matrix.scalar (Fin n) r) i j - c * A i j
  have hmatrix (c : ℝ) :
      Matrix.scalar (Fin n) r -
          Matrix.of (higham7_26_rowScale (Function.update d i c) A) =
        B.updateRow i (row c) := by
    ext p q
    by_cases hpi : p = i
    · subst p
      simp [B, row, higham7_26_rowScale]
    · simp [B, row, higham7_26_rowScale, hpi]
  have hrow :
      row (θ * a + (1 - θ) * b) =
        θ • row a + (1 - θ) • row b := by
    funext j
    simp [row]
    ring
  simp only [higham7_26_rowScaledCharDet, hmatrix]
  rw [hrow, Matrix.det_updateRow_add, Matrix.det_updateRow_smul,
    Matrix.det_updateRow_smul]

/-- A nonpositive convex combination has a nonpositive endpoint. -/
private lemma higham7_26_exists_nonpos_endpoint
    (θ u v : ℝ) (hθ0 : 0 ≤ θ) (hθ1 : θ ≤ 1)
    (h : θ * u + (1 - θ) * v ≤ 0) :
    u ≤ 0 ∨ v ≤ 0 := by
  by_contra hnot
  push_neg at hnot
  have hfirst : 0 ≤ θ * u := mul_nonneg hθ0 (le_of_lt hnot.1)
  have hsecond : 0 ≤ (1 - θ) * v :=
    mul_nonneg (sub_nonneg.mpr hθ1) (le_of_lt hnot.2)
  by_cases hθ : θ = 0
  · subst θ
    have hv : v ≤ 0 := by simpa using h
    exact (not_le_of_gt hnot.2) hv
  · have hfirst_pos : 0 < θ * u :=
      mul_pos (lt_of_le_of_ne hθ0 (Ne.symm hθ)) hnot.1
    linarith

/-- One multiplier in `[-1,1]` can be replaced by a sign without turning a
nonpositive characteristic determinant positive. -/
lemma higham7_26_exists_sign_update_charDet_nonpos {n : ℕ}
    (A : Fin n → Fin n → ℝ) (r : ℝ) (d : Fin n → ℝ)
    (i : Fin n) (hdi : |d i| ≤ 1)
    (hdet : higham7_26_rowScaledCharDet A r d ≤ 0) :
    ∃ ε : ℝ, (ε = 1 ∨ ε = -1) ∧
      higham7_26_rowScaledCharDet A r (Function.update d i ε) ≤ 0 := by
  let θ : ℝ := (d i + 1) / 2
  have hd_bounds : -1 ≤ d i ∧ d i ≤ 1 := (abs_le.mp hdi)
  have hθ0 : 0 ≤ θ := by
    dsimp [θ]
    linarith
  have hθ1 : θ ≤ 1 := by
    dsimp [θ]
    linarith
  have hconv : θ * (1 : ℝ) + (1 - θ) * (-1) = d i := by
    dsimp [θ]
    ring
  have hdet_conv :
      θ * higham7_26_rowScaledCharDet A r (Function.update d i 1) +
          (1 - θ) *
            higham7_26_rowScaledCharDet A r (Function.update d i (-1)) ≤ 0 := by
    rw [← higham7_26_rowScaledCharDet_update_convex A r θ 1 (-1) d i,
      hconv, Function.update_eq_self]
    exact hdet
  rcases higham7_26_exists_nonpos_endpoint θ _ _ hθ0 hθ1 hdet_conv with hp | hm
  · exact ⟨1, Or.inl rfl, hp⟩
  · exact ⟨-1, Or.inr rfl, hm⟩

/-- Simultaneously replace all row multipliers in `[-1,1]` by signs while
preserving nonpositivity of the characteristic determinant. -/
theorem higham7_26_exists_rowSignature_charDet_nonpos {n : ℕ}
    (A : Fin n → Fin n → ℝ) (r : ℝ) (d : Fin n → ℝ)
    (hd : ∀ i : Fin n, |d i| ≤ 1)
    (hdet : higham7_26_rowScaledCharDet A r d ≤ 0) :
    ∃ s : Fin n → ℝ, (∀ i : Fin n, s i = 1 ∨ s i = -1) ∧
      higham7_26_rowScaledCharDet A r s ≤ 0 := by
  classical
  have hfinite : ∀ t : Finset (Fin n),
      ∃ e : Fin n → ℝ,
        (∀ i ∈ t, e i = 1 ∨ e i = -1) ∧
        (∀ i ∉ t, e i = d i) ∧
        higham7_26_rowScaledCharDet A r e ≤ 0 := by
    intro t
    induction t using Finset.induction_on with
    | empty =>
        exact ⟨d, by simp, by simp, hdet⟩
    | @insert i t hit ih =>
        rcases ih with ⟨e, hesign, heoutside, hedet⟩
        have hei : e i = d i := heoutside i hit
        obtain ⟨ε, hεsign, hεdet⟩ :=
          higham7_26_exists_sign_update_charDet_nonpos A r e i
            (by simpa [hei] using hd i) hedet
        refine ⟨Function.update e i ε, ?_, ?_, hεdet⟩
        · intro j hj
          rcases Finset.mem_insert.mp hj with rfl | hjt
          · simpa using hεsign
          · by_cases hji : j = i
            · subst j
              simpa using hεsign
            · rw [Function.update_of_ne hji]
              exact hesign j hjt
        · intro j hj
          have hji : j ≠ i := by
            intro h
            subst j
            exact hj (Finset.mem_insert_self i t)
          have hjt : j ∉ t := by
            intro h
            exact hj (Finset.mem_insert_of_mem h)
          rw [Function.update_of_ne hji]
          exact heoutside j hjt
  obtain ⟨s, hsign, _houtside, hsdet⟩ := hfinite Finset.univ
  exact ⟨s, fun i ↦ hsign i (Finset.mem_univ i), hsdet⟩

/-- Rump's Theorem 3.1 in eigenpair form.  If one real vector is expanded
componentwise by at least `r`, signing the rows exposes an ordinary real
eigenvalue at least `r`. -/
theorem higham7_26_rump_sign_real_eigenpair_of_componentwise_growth
    {n : ℕ} (hn : 0 < n) (A : Fin n → Fin n → ℝ)
    (r : ℝ) (x : Fin n → ℝ)
    (hr : 0 ≤ r) (hx : x ≠ 0)
    (hgrowth : ∀ i : Fin n,
      r * |x i| ≤ |matMulVec n A x i|) :
    ∃ s : Fin n → ℝ, ∃ lam : ℝ, ∃ z : Fin n → ℝ,
      (∀ i : Fin n, s i = 1 ∨ s i = -1) ∧
      z ≠ 0 ∧ r ≤ lam ∧
      matMulVec n (higham7_26_rowScale s A) z =
        fun i ↦ lam * z i := by
  classical
  let d : Fin n → ℝ := fun i ↦
    if h : matMulVec n A x i = 0 then 0
    else r * x i / matMulVec n A x i
  have hd : ∀ i : Fin n, |d i| ≤ 1 := by
    intro i
    by_cases hzero : matMulVec n A x i = 0
    · simp [d, hzero]
    · have hden : 0 < |matMulVec n A x i| := abs_pos.mpr hzero
      simp only [d, dif_neg hzero, abs_div, abs_mul, abs_of_nonneg hr]
      exact (div_le_one hden).2 (hgrowth i)
  have hdaction : ∀ i : Fin n,
      d i * matMulVec n A x i = r * x i := by
    intro i
    by_cases hzero : matMulVec n A x i = 0
    · have hprod_abs : r * |x i| = 0 := by
        apply le_antisymm
        · simpa [hzero] using hgrowth i
        · exact mul_nonneg hr (abs_nonneg _)
      have hprod : r * x i = 0 := by
        apply abs_eq_zero.mp
        simpa [abs_mul, abs_of_nonneg hr] using hprod_abs
      simp [d, hzero, hprod]
    · simp [d, hzero]
  have hdetzero : higham7_26_rowScaledCharDet A r d = 0 := by
    apply Matrix.exists_mulVec_eq_zero_iff.mp
    refine ⟨x, hx, ?_⟩
    funext i
    have hi : r * x i - d i * matMulVec n A x i = 0 := by
      rw [hdaction i]
      ring
    simpa [Matrix.sub_mulVec, Matrix.scalar_apply] using hi
  obtain ⟨s, hs, hsdet⟩ :=
    higham7_26_exists_rowSignature_charDet_nonpos A r d hd (le_of_eq hdetzero)
  let M : Matrix (Fin n) (Fin n) ℝ :=
    Matrix.of (higham7_26_rowScale s A)
  let p : Polynomial ℝ := M.charpoly
  have hpdeg : 0 < p.degree := by
    simp [p, M, Matrix.charpoly_degree_eq_dim, hn]
  have hplead : 0 ≤ p.leadingCoeff := by
    have hpmonic : p.Monic := by
      dsimp [p]
      exact Matrix.charpoly_monic M
    rw [hpmonic.leadingCoeff]
    norm_num
  have hptop : Tendsto (fun t : ℝ ↦ p.eval t) atTop atTop :=
    Polynomial.tendsto_atTop_of_leadingCoeff_nonneg p hpdeg hplead
  obtain ⟨t, htpos, hrt⟩ :=
    ((hptop.eventually_gt_atTop 0).and (eventually_ge_atTop r)).exists
  have hpreval : p.eval r ≤ 0 := by
    simpa [p, M, higham7_26_rowScaledCharDet, Matrix.eval_charpoly] using hsdet
  have hzero_mem : 0 ∈ (fun u : ℝ ↦ p.eval u) '' Set.Icc r t := by
    apply intermediate_value_Icc hrt p.continuous.continuousOn
    exact ⟨hpreval, le_of_lt htpos⟩
  rcases hzero_mem with ⟨lam, hlam_mem, hlam_root⟩
  have hdet_lam : (Matrix.scalar (Fin n) lam - M).det = 0 := by
    rw [← Matrix.eval_charpoly]
    exact hlam_root
  obtain ⟨z, hz, hzker⟩ := Matrix.exists_mulVec_eq_zero_iff.mpr hdet_lam
  have heig : Matrix.mulVec M z = fun i ↦ lam * z i := by
    funext i
    have hi := congrFun hzker i
    have hcoord : lam * z i - Matrix.mulVec M z i = 0 := by
      simpa [Matrix.sub_mulVec, Matrix.scalar_apply] using hi
    linarith
  refine ⟨s, lam, z, hs, hz, hlam_mem.1, ?_⟩
  simpa [M, ch7_matrix_mulVec_eq_matMulVec] using heig

/-! ## Rump's lower-triangular column-sign selection -/

/-- One of the two signs prevents an existing partial sum from decreasing the
absolute value of a new summand. -/
lemma higham7_26_exists_sign_abs_add_mul_ge
    (a b : ℝ) :
    ∃ ε : ℝ, (ε = 1 ∨ ε = -1) ∧ |a + ε * b| ≥ |b| := by
  by_cases h : 0 ≤ a * b
  · refine ⟨1, Or.inl rfl, ?_⟩
    have hsquare : b ^ 2 ≤ (a + b) ^ 2 := by
      nlinarith [sq_nonneg a]
    have hb := abs_nonneg b
    have hab := abs_nonneg (a + b)
    rw [show a + 1 * b = a + b by ring]
    nlinarith [sq_abs b, sq_abs (a + b)]
  · refine ⟨-1, Or.inr rfl, ?_⟩
    have hneg : a * b < 0 := lt_of_not_ge h
    have hsquare : b ^ 2 ≤ (a - b) ^ 2 := by
      nlinarith [sq_nonneg a]
    have hb := abs_nonneg b
    have hab := abs_nonneg (a - b)
    rw [show a + (-1) * b = a - b by ring]
    nlinarith [sq_abs b, sq_abs (a - b)]

/-- Rump's Lemma 4.2, in the equivalent form where the diagonal has already
been combined with the strictly lower-triangular part.  Column signs can be
chosen successively so that every row dominates its diagonal contribution. -/
theorem higham7_26_exists_columnSignature_lowerTriangular_diagonal_dominance
    {n : ℕ} (B : Fin n → Fin n → ℝ) (x : Fin n → ℝ)
    (hB : ∀ i j : Fin n, i.val < j.val → B i j = 0) :
    ∃ s : Fin n → ℝ,
      (∀ j : Fin n, s j = 1 ∨ s j = -1) ∧
      ∀ i : Fin n,
        |matMulVec n B (fun j ↦ s j * x j) i| ≥ |B i i * x i| := by
  classical
  have hstage : ∀ k : ℕ, k ≤ n →
      ∃ s : Fin n → ℝ,
        (∀ j : Fin n, s j = 1 ∨ s j = -1) ∧
        ∀ i : Fin n, i.val < k →
          |matMulVec n B (fun j ↦ s j * x j) i| ≥ |B i i * x i| := by
    intro k hk
    induction k with
    | zero =>
        exact ⟨fun _ ↦ 1, by simp, by simp⟩
    | succ k ih =>
        have hklt : k < n := Nat.lt_of_succ_le hk
        obtain ⟨s, hsign, hrows⟩ := ih (Nat.le_of_succ_le hk)
        let i : Fin n := ⟨k, hklt⟩
        let a : ℝ :=
          ∑ j ∈ (Finset.univ.erase i), B i j * (s j * x j)
        let b : ℝ := B i i * x i
        obtain ⟨ε, hεsign, hεbound⟩ :=
          higham7_26_exists_sign_abs_add_mul_ge a b
        let s' : Fin n → ℝ := Function.update s i ε
        refine ⟨s', ?_, ?_⟩
        · intro j
          by_cases hji : j = i
          · subst j
            simpa [s'] using hεsign
          · simpa [s', Function.update_of_ne hji] using hsign j
        · intro p hp
          have hp_cases : p.val < k ∨ p = i := by
            have hple : p.val ≤ k := Nat.le_of_lt_succ hp
            rcases Nat.lt_or_eq_of_le hple with hpk | hpk
            · exact Or.inl hpk
            · right
              apply Fin.ext
              simpa [i] using hpk
          rcases hp_cases with hpk | rfl
          · have hpi : p ≠ i := by
              intro h
              subst p
              simp [i] at hpk
            have hzero : B p i = 0 := hB p i (by simpa [i] using hpk)
            have hsame :
                matMulVec n B (fun j ↦ s' j * x j) p =
                  matMulVec n B (fun j ↦ s j * x j) p := by
              unfold matMulVec
              apply Finset.sum_congr rfl
              intro j _
              by_cases hji : j = i
              · subst j
                simp [hzero]
              · simp [s', Function.update_of_ne hji]
            rw [hsame]
            exact hrows p hpk
          · have hrow :
                matMulVec n B (fun j ↦ s' j * x j) i = a + ε * b := by
              unfold matMulVec
              rw [← Finset.sum_erase_add _ _ (Finset.mem_univ i)]
              congr 1
              · apply Finset.sum_congr rfl
                intro j hj
                have hji : j ≠ i := Finset.ne_of_mem_erase hj
                simp [s', Function.update_of_ne hji]
              · simp [s', b]
                ring
            rw [hrow]
            exact hεbound
  obtain ⟨s, hsign, hrows⟩ := hstage n le_rfl
  exact ⟨s, hsign, fun i ↦ hrows i i.isLt⟩

/-- The geometric tail over `Fin n` is bounded by the corresponding infinite
geometric tail. -/
lemma higham7_26_fin_geometric_tail_le {n : ℕ} (i : Fin n) (q : ℝ)
    (hq0 : 0 ≤ q) (hq1 : q < 1) :
    ∑ j ∈ Finset.Ioi i, q ^ j.val ≤ q ^ (i.val + 1) / (1 - q) := by
  have hsum :
      (∑ j ∈ Finset.Ioi i, q ^ j.val) =
        ∑ m ∈ Finset.Ico (i.val + 1) n, q ^ m := by
    calc
      (∑ j ∈ Finset.Ioi i, q ^ j.val) =
          ∑ m ∈ (Finset.Ioi i).map Fin.valEmbedding, q ^ m := by
            rw [Finset.sum_map]
            rfl
      _ = ∑ m ∈ Finset.Ioo i.val n, q ^ m := by
            rw [Fin.map_valEmbedding_Ioi]
      _ = ∑ m ∈ Finset.Ico (i.val + 1) n, q ^ m := by
            have hinterval :
                Finset.Ioo i.val n = Finset.Ico (i.val + 1) n := by
              simpa [Nat.succ_eq_add_one] using
                (Finset.Ico_succ_left_eq_Ioo i.val n).symm
            rw [hinterval]
  rw [hsum]
  exact geom_sum_Ico_le_of_lt_one hq0 hq1

/-- Rump's optimizing geometric ratio. -/
noncomputable def higham7_26_rumpGeometricRatio : ℝ :=
  1 - Real.sqrt 2 / 2

/-- The reciprocal of Rump's universal constant `3 + 2√2`. -/
noncomputable def higham7_26_rumpCycleConstant : ℝ :=
  1 / (3 + 2 * Real.sqrt 2)

lemma higham7_26_rumpGeometricRatio_pos :
    0 < higham7_26_rumpGeometricRatio := by
  have hs0 : 0 ≤ Real.sqrt 2 := Real.sqrt_nonneg _
  have hs2 : (Real.sqrt 2) ^ 2 = 2 := Real.sq_sqrt (by norm_num)
  dsimp [higham7_26_rumpGeometricRatio]
  nlinarith

lemma higham7_26_rumpGeometricRatio_lt_one :
    higham7_26_rumpGeometricRatio < 1 := by
  have hspos : 0 < Real.sqrt 2 := Real.sqrt_pos.2 (by norm_num)
  dsimp [higham7_26_rumpGeometricRatio]
  linarith

lemma higham7_26_rumpCycleConstant_pos :
    0 < higham7_26_rumpCycleConstant := by
  dsimp [higham7_26_rumpCycleConstant]
  positivity

/-- The scalar identity optimized in Rump's proof of Lemma 4.3. -/
lemma higham7_26_rumpGeometricRatio_identity :
    higham7_26_rumpGeometricRatio *
          (1 - 2 * higham7_26_rumpGeometricRatio) /
        (1 - higham7_26_rumpGeometricRatio) =
      higham7_26_rumpCycleConstant := by
  have hspos : 0 < Real.sqrt 2 := Real.sqrt_pos.2 (by norm_num)
  have hs2 : (Real.sqrt 2) ^ 2 = 2 := Real.sq_sqrt (by norm_num)
  dsimp [higham7_26_rumpGeometricRatio, higham7_26_rumpCycleConstant]
  field_simp
  nlinarith

lemma higham7_26_rumpCycleConstant_le_wrap_margin :
    higham7_26_rumpCycleConstant ≤
      1 - higham7_26_rumpGeometricRatio /
        (1 - higham7_26_rumpGeometricRatio) := by
  have hspos : 0 < Real.sqrt 2 := Real.sqrt_pos.2 (by norm_num)
  have hs2 : (Real.sqrt 2) ^ 2 = 2 := Real.sq_sqrt (by norm_num)
  dsimp [higham7_26_rumpGeometricRatio, higham7_26_rumpCycleConstant]
  field_simp
  nlinarith

/-! ## Rump's normalized full-cycle lemma -/

/-- Rump's Lemma 4.3 in eigenpair form.  A matrix bounded entrywise by one
whose cyclic superdiagonal is one admits row and column signatures exposing a
real eigenvalue at least `(3 + 2√2)⁻¹`. -/
theorem higham7_26_rump_normalized_fullCycle_eigenpair
    {k : ℕ} (hk : 0 < k) (A : Fin k → Fin k → ℝ)
    (hA_bound : ∀ i j : Fin k, |A i j| ≤ 1)
    (hcycle : ∀ i : Fin k, A i (finRotate k i) = 1) :
    ∃ rowSign colSign : Fin k → ℝ,
      ∃ lam : ℝ, ∃ z : Fin k → ℝ,
        (∀ i : Fin k, rowSign i = 1 ∨ rowSign i = -1) ∧
        (∀ j : Fin k, colSign j = 1 ∨ colSign j = -1) ∧
        z ≠ 0 ∧ higham7_26_rumpCycleConstant ≤ lam ∧
        matMulVec k
            (higham7_26_rowScale rowSign
              (higham7_26_columnScale A colSign)) z =
          fun i ↦ lam * z i := by
  classical
  letI : NeZero k := ⟨Nat.ne_of_gt hk⟩
  let q : ℝ := higham7_26_rumpGeometricRatio
  let y : Fin k → ℝ := fun i ↦ q ^ i.val
  let B : Fin k → Fin k → ℝ := fun i j ↦ A ((finRotate k).symm i) j
  let LD : Fin k → Fin k → ℝ := fun i j ↦
    if j.val ≤ i.val then B i j else 0
  let U : Fin k → Fin k → ℝ := fun i j ↦
    if i.val < j.val then B i j else 0
  have hq0 : 0 ≤ q := le_of_lt higham7_26_rumpGeometricRatio_pos
  have hq1 : q < 1 := higham7_26_rumpGeometricRatio_lt_one
  have hy_nonneg : ∀ i : Fin k, 0 ≤ y i := fun i ↦ pow_nonneg hq0 _
  have hLD_lower : ∀ i j : Fin k, i.val < j.val → LD i j = 0 := by
    intro i j hij
    dsimp [LD]
    rw [if_neg (Nat.not_le_of_gt hij)]
  obtain ⟨colSign, hcolSign, hLDdom⟩ :=
    higham7_26_exists_columnSignature_lowerTriangular_diagonal_dominance
      LD y hLD_lower
  let v : Fin k → ℝ := fun j ↦ colSign j * y j
  have hBdiag : ∀ i : Fin k, B i i = 1 := by
    intro i
    dsimp [B]
    have hi := hcycle ((finRotate k).symm i)
    rw [(finRotate k).apply_symm_apply i] at hi
    exact hi
  have hLDdiag : ∀ i : Fin k, LD i i = 1 := by
    intro i
    simp [LD, hBdiag i]
  have hLDabs : ∀ i : Fin k,
      y i ≤ |matMulVec k LD v i| := by
    intro i
    have hi := hLDdom i
    rw [hLDdiag i] at hi
    simpa [v, abs_of_nonneg (hy_nonneg i)] using hi
  have hcolAbs : ∀ j : Fin k, |colSign j| = 1 := by
    intro j
    rcases hcolSign j with hj | hj <;> simp [hj]
  have hUabs : ∀ i : Fin k,
      |matMulVec k U v i| ≤ ∑ j ∈ Finset.Ioi i, y j := by
    intro i
    calc
      |matMulVec k U v i| ≤ ∑ j : Fin k, |U i j| * |v j| :=
        abs_matMulVec_le k U v i
      _ ≤ ∑ j : Fin k, if i < j then y j else 0 := by
        apply Finset.sum_le_sum
        intro j _
        by_cases hij : i < j
        · have hBij : |B i j| ≤ 1 := hA_bound ((finRotate k).symm i) j
          have hvabs : |v j| = y j := by
            simp [v, abs_mul, hcolAbs j, abs_of_nonneg (hy_nonneg j)]
          simp [U, hij, hvabs]
          exact mul_le_of_le_one_left (hy_nonneg j) hBij
        · simp [U, hij]
      _ = ∑ j ∈ Finset.Ioi i, y j := by
        rw [← Finset.sum_filter]
        apply Finset.sum_congr
        · ext j
          simp
        · intro j _
          simp
  have hBdecomp : ∀ i : Fin k,
      matMulVec k B v i = matMulVec k LD v i + matMulVec k U v i := by
    intro i
    unfold matMulVec
    rw [← Finset.sum_add_distrib]
    apply Finset.sum_congr rfl
    intro j _
    by_cases hij : j.val ≤ i.val
    · dsimp [LD, U]
      rw [if_pos hij, if_neg (Nat.not_lt_of_ge hij)]
      ring
    · have hij' : i.val < j.val := Nat.lt_of_not_ge hij
      dsimp [LD, U]
      rw [if_neg hij, if_pos hij']
      ring
  have hBgrowth : ∀ i : Fin k,
      y i - (∑ j ∈ Finset.Ioi i, y j) ≤ |matMulVec k B v i| := by
    intro i
    calc
      y i - (∑ j ∈ Finset.Ioi i, y j) ≤
          |matMulVec k LD v i| - |matMulVec k U v i| :=
        sub_le_sub (hLDabs i) (hUabs i)
      _ ≤ |matMulVec k LD v i + matMulVec k U v i| := by
        simpa only [abs_neg, sub_neg_eq_add] using
          (abs_sub_abs_le_abs_sub
            (matMulVec k LD v i) (-matMulVec k U v i))
      _ = |matMulVec k B v i| := by rw [hBdecomp i]
  have hmargin : ∀ p : Fin k,
      higham7_26_rumpCycleConstant * y p ≤
        y (finRotate k p) -
          ∑ j ∈ Finset.Ioi (finRotate k p), y j := by
    intro p
    by_cases hrotzero : finRotate k p = 0
    · have htail := higham7_26_fin_geometric_tail_le (0 : Fin k) q hq0 hq1
      have htail0 :
          (∑ j ∈ Finset.Ioi (0 : Fin k), y j) ≤ q / (1 - q) := by
        simpa [y] using htail
      have hyp_le : y p ≤ 1 := by
        dsimp [y]
        exact pow_le_one₀ hq0 (le_of_lt hq1)
      have hconst_nonneg : 0 ≤ higham7_26_rumpCycleConstant :=
        le_of_lt higham7_26_rumpCycleConstant_pos
      rw [hrotzero]
      calc
        higham7_26_rumpCycleConstant * y p ≤
            higham7_26_rumpCycleConstant := by
          simpa using mul_le_of_le_one_right hconst_nonneg hyp_le
        _ ≤ 1 - q / (1 - q) := by
          simpa [q] using higham7_26_rumpCycleConstant_le_wrap_margin
        _ ≤ y (0 : Fin k) - ∑ j ∈ Finset.Ioi (0 : Fin k), y j := by
          have hy0 : y (0 : Fin k) = 1 := by simp [y]
          rw [hy0]
          exact sub_le_sub_left htail0 1
    · have hprevval :=
        coe_finRotate_symm_of_ne_zero (n := k) hrotzero
      rw [(finRotate k).symm_apply_apply p] at hprevval
      have hrotval : (finRotate k p).val = p.val + 1 := by
        have hrotpos : 0 < (finRotate k p).val := by
          exact Nat.pos_of_ne_zero (by
            intro hval
            apply hrotzero
            apply Fin.ext
            simpa using hval)
        omega
      have htail :=
        higham7_26_fin_geometric_tail_le (finRotate k p) q hq0 hq1
      have hpow :
          q ^ (p.val + 1) - q ^ (p.val + 2) / (1 - q) =
            higham7_26_rumpCycleConstant * q ^ p.val := by
        rw [← higham7_26_rumpGeometricRatio_identity]
        change
          q ^ (p.val + 1) - q ^ (p.val + 2) / (1 - q) =
            (q * (1 - 2 * q) / (1 - q)) * q ^ p.val
        have hden : 1 - q ≠ 0 := ne_of_gt (sub_pos.mpr hq1)
        rw [show p.val + 1 = Nat.succ p.val by omega, pow_succ,
          show p.val + 2 = Nat.succ (p.val + 1) by omega, pow_succ,
          show p.val + 1 = Nat.succ p.val by omega, pow_succ]
        field_simp
        ring
      dsimp [y] at htail ⊢
      rw [hrotval] at htail ⊢
      rw [← hpow]
      exact sub_le_sub_left htail _
  have hAgrowth : ∀ p : Fin k,
      higham7_26_rumpCycleConstant * |y p| ≤
        |matMulVec k (higham7_26_columnScale A colSign) y p| := by
    intro p
    have hrow := hBgrowth (finRotate k p)
    have hBrow : matMulVec k B v (finRotate k p) =
        matMulVec k A v p := by
      unfold matMulVec
      change
        (∑ j : Fin k, A ((finRotate k).symm (finRotate k p)) j * v j) =
          ∑ j : Fin k, A p j * v j
      rw [(finRotate k).symm_apply_apply p]
    rw [hBrow] at hrow
    rw [higham7_26_columnScale_mulVec]
    change higham7_26_rumpCycleConstant * |y p| ≤
      |matMulVec k A v p|
    rw [abs_of_nonneg (hy_nonneg p)]
    exact (hmargin p).trans hrow
  have hy_ne : y ≠ 0 := by
    intro hy
    have hzero := congrFun hy (0 : Fin k)
    simp [y] at hzero
  obtain ⟨rowSign, lam, z, hrowSign, hz, hlam, heig⟩ :=
    higham7_26_rump_sign_real_eigenpair_of_componentwise_growth
      hk (higham7_26_columnScale A colSign)
        higham7_26_rumpCycleConstant y
        (le_of_lt higham7_26_rumpCycleConstant_pos) hy_ne hAgrowth
  exact ⟨rowSign, colSign, lam, z, hrowSign, hcolSign, hz, hlam, heig⟩

/-! ## Cycles in finite functional graphs -/

/-- A simple directed cycle in the functional graph of `f`, ordered by the
standard cyclic permutation of `Fin length`. -/
structure Higham7_26FunctionalCycle {α : Type*} (f : α → α) where
  length : ℕ
  length_pos : 0 < length
  vertex : Fin length → α
  vertex_injective : Function.Injective vertex
  next_vertex : ∀ t : Fin length,
    f (vertex t) = vertex (finRotate length t)

private lemma higham7_26_iterate_period_next {α : Type*}
    (f : α → α) (x : α) {k : ℕ} (hk : 0 < k)
    (hperiod : f^[k] x = x) (t : Fin k) :
    f (f^[t.val] x) = f^[(finRotate k t).val] x := by
  obtain ⟨m, rfl⟩ := Nat.exists_eq_succ_of_ne_zero (Nat.ne_of_gt hk)
  rw [finRotate_succ_apply, Fin.val_add_one]
  by_cases ht : t = Fin.last m
  · subst t
    simpa [Function.iterate_succ_apply'] using hperiod
  · simp [ht, Function.iterate_succ_apply']

/-- Every self-map of a nonempty finite type has a simple directed cycle. -/
theorem higham7_26_exists_functionalCycle
    {α : Type*} [Fintype α] [Nonempty α] (f : α → α) :
    Nonempty (Higham7_26FunctionalCycle f) := by
  classical
  let a : α := Classical.choice (inferInstance : Nonempty α)
  obtain ⟨p, q, hpq, heq⟩ :=
    Finite.exists_ne_map_eq_of_infinite (fun t : ℕ ↦ f^[t] a)
  have hex : ∃ x : α, ∃ k : ℕ, 0 < k ∧ f^[k] x = x := by
    rcases lt_or_gt_of_ne hpq with hpq' | hqp'
    · let x : α := f^[p] a
      let k : ℕ := q - p
      refine ⟨x, k, Nat.sub_pos_of_lt hpq', ?_⟩
      dsimp [x, k]
      calc
        f^[q - p] (f^[p] a) = f^[(q - p) + p] a := by
          rw [Function.iterate_add_apply]
        _ = f^[q] a := by rw [Nat.sub_add_cancel hpq'.le]
        _ = f^[p] a := heq.symm
    · let x : α := f^[q] a
      let k : ℕ := p - q
      refine ⟨x, k, Nat.sub_pos_of_lt hqp', ?_⟩
      dsimp [x, k]
      calc
        f^[p - q] (f^[q] a) = f^[(p - q) + q] a := by
          rw [Function.iterate_add_apply]
        _ = f^[p] a := by rw [Nat.sub_add_cancel hqp'.le]
        _ = f^[q] a := heq
  obtain ⟨x, period, hperiod_pos, hperiod⟩ := hex
  let P : ℕ → Prop := fun k ↦ 0 < k ∧ f^[k] x = x
  have hP : ∃ k, P k := ⟨period, hperiod_pos, hperiod⟩
  let k : ℕ := Nat.find hP
  have hk_spec : P k := Nat.find_spec hP
  have hk_min : ∀ m : ℕ, P m → k ≤ m := by
    intro m hm
    exact Nat.find_min' hP hm
  let vertex : Fin k → α := fun t ↦ f^[t.val] x
  have hno_repeat : ∀ u v : Fin k, u.val < v.val →
      vertex u = vertex v → False := by
    intro u v huv_order huv
    let m : ℕ := k - v.val + u.val
    have hm_pos : 0 < m := by
      dsimp [m]
      have : 0 < k - v.val := Nat.sub_pos_of_lt v.isLt
      omega
    have hm_lt : m < k := by
      dsimp [m]
      omega
    have hm_period : f^[m] x = x := by
      dsimp [m]
      calc
        f^[k - v.val + u.val] x =
            f^[k - v.val] (f^[u.val] x) := by
          rw [Function.iterate_add_apply]
        _ = f^[k - v.val] (f^[v.val] x) := by
          rw [show f^[u.val] x = f^[v.val] x from huv]
        _ = f^[(k - v.val) + v.val] x := by
          rw [Function.iterate_add_apply]
        _ = f^[k] x := by rw [Nat.sub_add_cancel v.isLt.le]
        _ = x := hk_spec.2
    exact (not_lt_of_ge (hk_min m ⟨hm_pos, hm_period⟩)) hm_lt
  have hvertex_inj : Function.Injective vertex := by
    intro u v huv
    apply Fin.ext
    by_contra hval
    rcases lt_or_gt_of_ne hval with huv_order | hvu_order
    · exact hno_repeat u v huv_order huv
    · exact hno_repeat v u hvu_order huv.symm
  refine ⟨⟨k, hk_spec.1, vertex, hvertex_inj, ?_⟩⟩
  intro t
  exact higham7_26_iterate_period_next f x hk_spec.1 hk_spec.2 t

/-! ## Perron row maxima -/

/-- A finite family has an entry which is both maximal and at least its
arithmetic average. -/
lemma higham7_26_exists_max_entry_ge_average {n : ℕ} (hn : 0 < n)
    (a : Fin n → ℝ) (r : ℝ) (hr : r ≤ ∑ j : Fin n, a j) :
    ∃ j : Fin n,
      r / (n : ℝ) ≤ a j ∧ ∀ l : Fin n, a l ≤ a j := by
  classical
  have huniv : (Finset.univ : Finset (Fin n)).Nonempty :=
    Finset.univ_nonempty_iff.mpr ⟨⟨0, hn⟩⟩
  obtain ⟨j, _hj, hjmax⟩ :=
    Finset.exists_mem_eq_sup' (s := (Finset.univ : Finset (Fin n))) huniv a
  have hmax : ∀ l : Fin n, a l ≤ a j := by
    intro l
    rw [← hjmax]
    exact Finset.le_sup' (s := (Finset.univ : Finset (Fin n)))
      (f := a) (Finset.mem_univ l)
  refine ⟨j, ?_, hmax⟩
  have hsum : (∑ l : Fin n, a l) ≤ (n : ℝ) * a j := by
    calc
      (∑ l : Fin n, a l) ≤ ∑ _l : Fin n, a j :=
        Finset.sum_le_sum fun l _ ↦ hmax l
      _ = (n : ℝ) * a j := by simp
  apply (div_le_iff₀ (Nat.cast_pos.mpr hn)).2
  simpa [mul_comm] using hr.trans hsum

/-- A positive nonnegative subeigenvector supplies a simple cycle of rowwise
maximal diagonally-scaled entries.  Every selected edge is at least `rho / n`.
This is the finite functional-graph form of the Perron step on p. 9 of Rump. -/
theorem higham7_26_exists_perronRowMaxCycle_of_subeigenvector
    {n : ℕ} (hn : 0 < n) (M : Fin n → Fin n → ℝ)
    (rho : ℝ) (x : Fin n → ℝ)
    (hrho : 0 < rho) (hx_nonneg : ∀ i : Fin n, 0 ≤ x i)
    (hx_ne : x ≠ 0)
    (hsub : ∀ i : Fin n, rho * x i ≤ matMulVec n M x i) :
    ∃ k : ℕ, ∃ vertex : Fin k → Fin n,
      0 < k ∧ Function.Injective vertex ∧
      (∀ t : Fin k, 0 < x (vertex t)) ∧
      (∀ t : Fin k,
        rho / (n : ℝ) ≤
          M (vertex t) (vertex (finRotate k t)) *
              x (vertex (finRotate k t)) / x (vertex t)) ∧
      (∀ t u : Fin k,
        M (vertex t) (vertex u) * x (vertex u) / x (vertex t) ≤
          M (vertex t) (vertex (finRotate k t)) *
              x (vertex (finRotate k t)) / x (vertex t)) := by
  classical
  let support := {i : Fin n // 0 < x i}
  have hsupport : Nonempty support := by
    by_contra hempty
    have hall : ∀ i : Fin n, x i = 0 := by
      intro i
      have hnot : ¬ 0 < x i := by
        intro hi
        exact hempty ⟨⟨i, hi⟩⟩
      exact le_antisymm (le_of_not_gt hnot) (hx_nonneg i)
    apply hx_ne
    funext i
    exact hall i
  let chosen : support → Fin n := fun i ↦
    Classical.choose (higham7_26_exists_max_entry_ge_average hn
      (fun j : Fin n ↦ M i.1 j * x j / x i.1) rho (by
        have hdiv : rho ≤ matMulVec n M x i.1 / x i.1 := by
          apply (le_div_iff₀ i.2).2
          simpa using hsub i.1
        simpa [matMulVec, Finset.sum_div] using hdiv))
  have hchosen : ∀ i : support,
      rho / (n : ℝ) ≤ M i.1 (chosen i) * x (chosen i) / x i.1 ∧
      ∀ l : Fin n,
        M i.1 l * x l / x i.1 ≤
          M i.1 (chosen i) * x (chosen i) / x i.1 := by
    intro i
    exact Classical.choose_spec
      (higham7_26_exists_max_entry_ge_average hn
        (fun j : Fin n ↦ M i.1 j * x j / x i.1) rho (by
          have hdiv : rho ≤ matMulVec n M x i.1 / x i.1 := by
            apply (le_div_iff₀ i.2).2
            simpa using hsub i.1
          simpa [matMulVec, Finset.sum_div] using hdiv))
  have hchosen_pos : ∀ i : support, 0 < x (chosen i) := by
    intro i
    have havg : 0 < rho / (n : ℝ) := div_pos hrho (Nat.cast_pos.mpr hn)
    have hterm : 0 < M i.1 (chosen i) * x (chosen i) / x i.1 :=
      lt_of_lt_of_le havg (hchosen i).1
    by_contra hnot
    have hxzero : x (chosen i) = 0 :=
      le_antisymm (le_of_not_gt hnot) (hx_nonneg (chosen i))
    simp [hxzero] at hterm
  let next : support → support := fun i ↦ ⟨chosen i, hchosen_pos i⟩
  let cycle : Higham7_26FunctionalCycle next :=
    Classical.choice (higham7_26_exists_functionalCycle next)
  let vertex : Fin cycle.length → Fin n := fun t ↦ (cycle.vertex t).1
  have hnext_underlying : ∀ t : Fin cycle.length,
      chosen (cycle.vertex t) = vertex (finRotate cycle.length t) := by
    intro t
    have ht := congrArg Subtype.val (cycle.next_vertex t)
    exact ht
  refine ⟨cycle.length, vertex, cycle.length_pos, ?_, ?_, ?_, ?_⟩
  · intro s t hst
    apply cycle.vertex_injective
    apply Subtype.ext
    exact hst
  · intro t
    exact (cycle.vertex t).2
  · intro t
    simpa [vertex, hnext_underlying t] using (hchosen (cycle.vertex t)).1
  · intro t u
    have hmax := (hchosen (cycle.vertex t)).2 (vertex u)
    simpa [vertex, hnext_underlying t] using hmax

/-! ## Column signs realizing a selected cycle -/

/-- A real sign chosen so that `a * sign(a) = |a|`. -/
noncomputable def higham7_26_entrySign (a : ℝ) : ℝ :=
  if 0 ≤ a then 1 else -1

lemma higham7_26_entrySign_eq_one_or_neg_one (a : ℝ) :
    higham7_26_entrySign a = 1 ∨ higham7_26_entrySign a = -1 := by
  by_cases h : 0 ≤ a
  · left
    simp [higham7_26_entrySign, h]
  · right
    simp [higham7_26_entrySign, h]

@[simp]
lemma higham7_26_abs_entrySign (a : ℝ) :
    |higham7_26_entrySign a| = 1 := by
  rcases higham7_26_entrySign_eq_one_or_neg_one a with h | h <;> simp [h]

@[simp]
lemma higham7_26_mul_entrySign (a : ℝ) :
    a * higham7_26_entrySign a = |a| := by
  by_cases h : 0 ≤ a
  · simp [higham7_26_entrySign, h, abs_of_nonneg h]
  · have ha : a < 0 := lt_of_not_ge h
    simp [higham7_26_entrySign, h, abs_of_neg ha]

/-- Choose the signs in each cycle-target column of `F` so that `Ainv * F`
agrees with `|Ainv|E` on every selected cycle edge.  The same construction is
globally dominated in absolute value by `|Ainv|E`. -/
theorem higham7_26_exists_signedMatrix_realizing_cycle
    {n k : ℕ} (hn : 0 < n)
    (Ainv E : Fin n → Fin n → ℝ)
    (hE : ∀ i j : Fin n, 0 ≤ E i j)
    (vertex : Fin k → Fin n) (hvertex : Function.Injective vertex) :
    ∃ F : Fin n → Fin n → ℝ,
      (∀ i j : Fin n, |F i j| ≤ E i j) ∧
      (∀ i j : Fin n,
        |matMul n Ainv F i j| ≤
          higham7_26_distanceMajorant n Ainv E i j) ∧
      (∀ t : Fin k,
        matMul n Ainv F (vertex t) (vertex (finRotate k t)) =
          higham7_26_distanceMajorant n Ainv E
            (vertex t) (vertex (finRotate k t))) := by
  classical
  let predecessor : Fin n → Fin n := fun j ↦
    if h : ∃ t : Fin k, vertex (finRotate k t) = j then
      vertex (Classical.choose h)
    else ⟨0, hn⟩
  have hpredecessor : ∀ t : Fin k,
      predecessor (vertex (finRotate k t)) = vertex t := by
    intro t
    dsimp [predecessor]
    rw [dif_pos ⟨t, rfl⟩]
    let u : Fin k := Classical.choose
      (show ∃ u : Fin k,
        vertex (finRotate k u) = vertex (finRotate k t) from ⟨t, rfl⟩)
    have hu : vertex (finRotate k u) = vertex (finRotate k t) :=
      Classical.choose_spec
        (show ∃ u : Fin k,
          vertex (finRotate k u) = vertex (finRotate k t) from ⟨t, rfl⟩)
    have hrot : finRotate k u = finRotate k t := hvertex hu
    have hut : u = t := (finRotate k).injective hrot
    exact congrArg vertex hut
  let F : Fin n → Fin n → ℝ := fun a j ↦
    higham7_26_entrySign (Ainv (predecessor j) a) * E a j
  refine ⟨F, ?_, ?_, ?_⟩
  · intro a j
    simp [F, abs_mul, abs_of_nonneg (hE a j)]
  · intro i j
    calc
      |matMul n Ainv F i j| ≤
          ∑ a : Fin n, |Ainv i a * F a j| := by
        exact Finset.abs_sum_le_sum_abs _ _
      _ = ∑ a : Fin n, |Ainv i a| * E a j := by
        apply Finset.sum_congr rfl
        intro a _
        simp [F, abs_mul, abs_of_nonneg (hE a j)]
      _ = higham7_26_distanceMajorant n Ainv E i j := by
        rfl
  · intro t
    unfold matMul
    dsimp [F]
    rw [show predecessor (vertex (finRotate k t)) = vertex t from hpredecessor t]
    change
      (∑ a : Fin n,
        Ainv (vertex t) a *
          (higham7_26_entrySign (Ainv (vertex t) a) *
            E a (vertex (finRotate k t)))) =
        ∑ a : Fin n, |Ainv (vertex t) a| * E a (vertex (finRotate k t))
    apply Finset.sum_congr rfl
    intro a _
    rw [← mul_assoc, higham7_26_mul_entrySign]

/-! ## Embedding a cycle vector in the ambient coordinates -/

/-- Extend coefficients on an injectively indexed cycle by zero to the ambient
index type.  The sum presentation makes subsequent matrix-vector algebra
independent of a chosen inverse to `vertex`. -/
noncomputable def higham7_26_cycleEmbed {n k : ℕ}
    (vertex : Fin k → Fin n) (c : Fin k → ℝ) : Fin n → ℝ :=
  fun i ↦ ∑ t : Fin k, if vertex t = i then c t else 0

@[simp]
lemma higham7_26_cycleEmbed_vertex {n k : ℕ}
    (vertex : Fin k → Fin n) (hvertex : Function.Injective vertex)
    (c : Fin k → ℝ) (t : Fin k) :
    higham7_26_cycleEmbed vertex c (vertex t) = c t := by
  classical
  unfold higham7_26_cycleEmbed
  rw [Finset.sum_eq_single t]
  · simp
  · intro u _ hut
    have hne : vertex u ≠ vertex t := fun h ↦ hut (hvertex h)
    simp [hne]
  · simp

lemma higham7_26_cycleEmbed_eq_zero_of_not_mem {n k : ℕ}
    (vertex : Fin k → Fin n) (c : Fin k → ℝ) (i : Fin n)
    (hi : ¬ ∃ t : Fin k, vertex t = i) :
    higham7_26_cycleEmbed vertex c i = 0 := by
  classical
  unfold higham7_26_cycleEmbed
  apply Finset.sum_eq_zero
  intro t _
  have hne : vertex t ≠ i := fun h ↦ hi ⟨t, h⟩
  simp [hne]

lemma higham7_26_matMulVec_cycleEmbed_vertex {n k : ℕ}
    (A : Fin n → Fin n → ℝ) (vertex : Fin k → Fin n)
    (c : Fin k → ℝ) (t : Fin k) :
    matMulVec n A (higham7_26_cycleEmbed vertex c) (vertex t) =
      ∑ u : Fin k, A (vertex t) (vertex u) * c u := by
  classical
  unfold matMulVec higham7_26_cycleEmbed
  calc
    (∑ j : Fin n, A (vertex t) j *
        ∑ u : Fin k, if vertex u = j then c u else 0) =
        ∑ j : Fin n, ∑ u : Fin k,
          A (vertex t) j * (if vertex u = j then c u else 0) := by
      apply Finset.sum_congr rfl
      intro j _
      rw [Finset.mul_sum]
    _ = ∑ u : Fin k, ∑ j : Fin n,
        A (vertex t) j * (if vertex u = j then c u else 0) := by
      rw [Finset.sum_comm]
    _ = ∑ u : Fin k, A (vertex t) (vertex u) * c u := by
      apply Finset.sum_congr rfl
      intro u _
      rw [Finset.sum_eq_single (vertex u)]
      · simp
      · intro j _ hju
        simp [Ne.symm hju]
      · simp

/-! ## Universal Rump certificate construction -/

/-- Core construction from a spectral-radius subeigenvector.  All cycle,
Perron, and sign data are constructed internally; the only additional
hypothesis identifies the supplied scalar with the source spectral radius. -/
theorem higham7_26_nonempty_rumpEigenpairCertificate_of_subeigenvector
    {n : ℕ} (hn : 0 < n)
    (Ainv E : Fin n → Fin n → ℝ)
    (hE : ∀ i j : Fin n, 0 ≤ E i j)
    (rho : ℝ) (x : Fin n → ℝ)
    (hrho : 0 < rho) (hx_nonneg : ∀ i : Fin n, 0 ≤ x i)
    (hx_ne : x ≠ 0)
    (hsub : ∀ i : Fin n,
      rho * x i ≤
        matMulVec n (higham7_26_distanceMajorant n Ainv E) x i)
    (hrho_eq : rho = higham7_26_spectralRadius
      (higham7_26_distanceMajorant n Ainv E)) :
    Nonempty (Higham7_26RumpEigenpairCertificate Ainv E) := by
  classical
  let M : Fin n → Fin n → ℝ := higham7_26_distanceMajorant n Ainv E
  obtain ⟨k, vertex, hk, hvertex, hxvertex, hedge_lower, hedge_max⟩ :=
    higham7_26_exists_perronRowMaxCycle_of_subeigenvector
      hn M rho x hrho hx_nonneg hx_ne (by simpa [M] using hsub)
  obtain ⟨F, hFbound, hKbound, hKcycle⟩ :=
    higham7_26_exists_signedMatrix_realizing_cycle
      hn Ainv E hE vertex hvertex
  let K : Fin n → Fin n → ℝ := matMul n Ainv F
  let edge : Fin k → ℝ := fun t ↦
    M (vertex t) (vertex (finRotate k t)) *
        x (vertex (finRotate k t)) / x (vertex t)
  have hedge_lower' : ∀ t : Fin k, rho / (n : ℝ) ≤ edge t := by
    intro t
    exact hedge_lower t
  have hedge_pos : ∀ t : Fin k, 0 < edge t := by
    intro t
    exact lt_of_lt_of_le (div_pos hrho (Nat.cast_pos.mpr hn)) (hedge_lower' t)
  let G : Fin k → Fin k → ℝ := fun t u ↦
    K (vertex t) (vertex u) * x (vertex u) / x (vertex t)
  let H : Fin k → Fin k → ℝ := fun t u ↦ G t u / edge t
  have hGabs : ∀ t u : Fin k, |G t u| ≤ edge t := by
    intro t u
    have hnum :
        |K (vertex t) (vertex u)| * x (vertex u) ≤
          M (vertex t) (vertex u) * x (vertex u) :=
      mul_le_mul_of_nonneg_right
        (by simpa [K, M] using hKbound (vertex t) (vertex u))
        (le_of_lt (hxvertex u))
    calc
      |G t u| = |K (vertex t) (vertex u)| * x (vertex u) /
          x (vertex t) := by
        simp [G, abs_div, abs_mul, abs_of_nonneg (le_of_lt (hxvertex u)),
          abs_of_pos (hxvertex t)]
      _ ≤ M (vertex t) (vertex u) * x (vertex u) /
          x (vertex t) :=
        (div_le_div_iff_of_pos_right (hxvertex t)).2 hnum
      _ ≤ edge t := hedge_max t u
  have hHbound : ∀ t u : Fin k, |H t u| ≤ 1 := by
    intro t u
    rw [show |H t u| = |G t u| / edge t by
      simp [H, abs_div, abs_of_pos (hedge_pos t)]]
    exact (div_le_one (hedge_pos t)).2 (hGabs t u)
  have hGcycle : ∀ t : Fin k, G t (finRotate k t) = edge t := by
    intro t
    simp only [G, edge]
    rw [show K (vertex t) (vertex (finRotate k t)) =
        M (vertex t) (vertex (finRotate k t)) by
      simpa [K, M] using hKcycle t]
  have hHcycle : ∀ t : Fin k, H t (finRotate k t) = 1 := by
    intro t
    simp [H, hGcycle t, ne_of_gt (hedge_pos t)]
  obtain ⟨row0, col0, lam0, z0, hrow0, hcol0, hz0, hlam0, heig0⟩ :=
    higham7_26_rump_normalized_fullCycle_eigenpair hk H hHbound hHcycle
  let w0 : Fin k → ℝ := fun u ↦ col0 u * z0 u
  have hrow0abs : ∀ t : Fin k, |row0 t| = 1 := by
    intro t
    rcases hrow0 t with ht | ht <;> simp [ht]
  have hcol0abs : ∀ t : Fin k, |col0 t| = 1 := by
    intro t
    rcases hcol0 t with ht | ht <;> simp [ht]
  have hlam0_nonneg : 0 ≤ lam0 :=
    (le_of_lt higham7_26_rumpCycleConstant_pos).trans hlam0
  have hHcoord : ∀ t : Fin k,
      row0 t * matMulVec k H w0 t = lam0 * z0 t := by
    intro t
    have ht := congrFun heig0 t
    simpa [w0] using ht
  have hHabs : ∀ t : Fin k,
      |matMulVec k H w0 t| = lam0 * |z0 t| := by
    intro t
    calc
      |matMulVec k H w0 t| =
          |row0 t * matMulVec k H w0 t| := by
        simp [abs_mul, hrow0abs t]
      _ = |lam0 * z0 t| := congrArg abs (hHcoord t)
      _ = lam0 * |z0 t| := by
        rw [abs_mul, abs_of_nonneg hlam0_nonneg]
  have hGfactor : ∀ t u : Fin k, G t u = edge t * H t u := by
    intro t u
    dsimp [H]
    field_simp [ne_of_gt (hedge_pos t)]
  have hGmul : ∀ t : Fin k,
      matMulVec k G w0 t = edge t * matMulVec k H w0 t := by
    intro t
    unfold matMulVec
    rw [Finset.mul_sum]
    apply Finset.sum_congr rfl
    intro u _
    rw [hGfactor t u]
    ring
  let base : ℝ := rho / (n : ℝ) * higham7_26_rumpCycleConstant
  have hbase_pos : 0 < base := by
    dsimp [base]
    exact mul_pos (div_pos hrho (Nat.cast_pos.mpr hn))
      higham7_26_rumpCycleConstant_pos
  have hGgrowth : ∀ t : Fin k,
      base * |z0 t| ≤ |matMulVec k G w0 t| := by
    intro t
    have hzabs : 0 ≤ |z0 t| := abs_nonneg _
    have hcycle_scaled :
        higham7_26_rumpCycleConstant * |z0 t| ≤
          lam0 * |z0 t| :=
      mul_le_mul_of_nonneg_right hlam0 hzabs
    calc
      base * |z0 t| =
          (rho / (n : ℝ)) *
            (higham7_26_rumpCycleConstant * |z0 t|) := by
        simp [base]
        ring
      _ ≤ edge t *
          (higham7_26_rumpCycleConstant * |z0 t|) :=
        mul_le_mul_of_nonneg_right (hedge_lower' t)
          (mul_nonneg (le_of_lt higham7_26_rumpCycleConstant_pos) hzabs)
      _ ≤ edge t * (lam0 * |z0 t|) :=
        mul_le_mul_of_nonneg_left hcycle_scaled (le_of_lt (hedge_pos t))
      _ = |matMulVec k G w0 t| := by
        rw [hGmul t, abs_mul, abs_of_pos (hedge_pos t), hHabs t]
  let coeff : Fin k → ℝ := fun u ↦ x (vertex u) * w0 u
  let w : Fin n → ℝ := higham7_26_cycleEmbed vertex coeff
  have hw_vertex : ∀ t : Fin k,
      w (vertex t) = x (vertex t) * w0 t := by
    intro t
    exact higham7_26_cycleEmbed_vertex vertex hvertex coeff t
  have hw_ne : w ≠ 0 := by
    intro hw
    apply hz0
    funext t
    have ht := congrFun hw (vertex t)
    rw [hw_vertex t] at ht
    have hxne : x (vertex t) ≠ 0 := ne_of_gt (hxvertex t)
    have hw0zero : w0 t = 0 := (mul_eq_zero.mp ht).resolve_left hxne
    have hcolne : col0 t ≠ 0 := by
      rcases hcol0 t with h | h <;> simp [h]
    exact (mul_eq_zero.mp hw0zero).resolve_left hcolne
  have hKembed : ∀ t : Fin k,
      matMulVec n K w (vertex t) =
        x (vertex t) * matMulVec k G w0 t := by
    intro t
    rw [show matMulVec n K w (vertex t) =
        ∑ u : Fin k, K (vertex t) (vertex u) * coeff u by
      exact higham7_26_matMulVec_cycleEmbed_vertex K vertex coeff t]
    unfold matMulVec
    rw [Finset.mul_sum]
    apply Finset.sum_congr rfl
    intro u _
    simp only [coeff, G]
    field_simp [ne_of_gt (hxvertex t)]
  have hKgrowth : ∀ i : Fin n,
      base * |w i| ≤ |matMulVec n K w i| := by
    intro i
    by_cases hi : ∃ t : Fin k, vertex t = i
    · obtain ⟨t, rfl⟩ := hi
      rw [hKembed t, hw_vertex t, abs_mul, abs_mul,
        abs_of_pos (hxvertex t), hcol0abs t, one_mul]
      have hxnonneg : 0 ≤ x (vertex t) := le_of_lt (hxvertex t)
      calc
        base * (x (vertex t) * |z0 t|) =
            x (vertex t) * (base * |z0 t|) := by ring
        _ ≤ x (vertex t) * |matMulVec k G w0 t| :=
          mul_le_mul_of_nonneg_left (hGgrowth t) hxnonneg
        _ = |x (vertex t) * matMulVec k G w0 t| := by
          rw [abs_mul, abs_of_nonneg hxnonneg]
    · have hwi := higham7_26_cycleEmbed_eq_zero_of_not_mem vertex coeff i hi
      rw [show w i = 0 from hwi]
      simp
  obtain ⟨rowSign, lam, z, hrowSign, hz, hlam, heig⟩ :=
    higham7_26_rump_sign_real_eigenpair_of_componentwise_growth
      hn K base w (le_of_lt hbase_pos) hw_ne hKgrowth
  let finalF : Fin n → Fin n → ℝ :=
    higham7_26_columnScale F rowSign
  let finalX : Fin n → ℝ := fun i ↦ rowSign i * z i
  have hrowSignAbs : ∀ i : Fin n, |rowSign i| = 1 := by
    intro i
    rcases hrowSign i with hi | hi <;> simp [hi]
  have hfinalX_ne : finalX ≠ 0 := by
    intro hzero
    apply hz
    funext i
    have hi := congrFun hzero i
    have hsne : rowSign i ≠ 0 := by
      rcases hrowSign i with h | h <;> simp [h]
    exact (mul_eq_zero.mp hi).resolve_left hsne
  have hfinalF_bound : ∀ i j : Fin n, |finalF i j| ≤ E i j := by
    intro i j
    simp [finalF, higham7_26_columnScale, abs_mul, hrowSignAbs j]
    exact hFbound i j
  have hFfinalX : matMulVec n finalF finalX = matMulVec n F z := by
    funext i
    unfold matMulVec
    apply Finset.sum_congr rfl
    intro j _
    rcases hrowSign j with hj | hj <;> simp [finalF, finalX,
      higham7_26_columnScale, hj]
  have hKeig : ∀ i : Fin n,
      matMulVec n K z i = lam * finalX i := by
    intro i
    have hi := congrFun heig i
    rcases hrowSign i with hs | hs
    · simp [finalX, hs] at hi ⊢
      exact hi
    · simp [finalX, hs] at hi ⊢
      linarith
  have hfinalEig :
      matMulVec n Ainv (matMulVec n finalF finalX) =
        fun i ↦ lam * finalX i := by
    rw [hFfinalX]
    funext i
    rw [← matMulVec_matMul n Ainv F z i]
    exact hKeig i
  have hlam_pos : 0 < lam := hbase_pos.trans_le hlam
  have hfraction_base :
      higham7_26_spectralRadius M / higham7_26_rumpFactor n = base := by
    rw [← hrho_eq]
    dsimp [higham7_26_rumpFactor, higham7_26_rumpCycleConstant, base]
    have hn0 : (n : ℝ) ≠ 0 := ne_of_gt (Nat.cast_pos.mpr hn)
    have hc0 : 3 + 2 * Real.sqrt 2 ≠ 0 := by positivity
    field_simp
  refine ⟨⟨finalF, finalX, lam, hfinalX_ne, hlam_pos,
    hfinalF_bound, hfinalEig, ?_⟩⟩
  rw [show higham7_26_distanceMajorant n Ainv E = M from rfl,
    hfraction_base]
  exact hlam

/-- Rump's universal certificate construction from the source data alone.
The nonnegative spectral-radius subeigenvector, row-max cycle, column signs,
and ordinary real eigenpair are all constructed in the proof. -/
theorem higham7_26_nonempty_rumpEigenpairCertificate
    {n : ℕ} (hn : 0 < n)
    (Ainv E : Fin n → Fin n → ℝ)
    (hE : ∀ i j : Fin n, 0 ≤ E i j)
    (hrho : 0 < higham7_26_spectralRadius
      (higham7_26_distanceMajorant n Ainv E)) :
    Nonempty (Higham7_26RumpEigenpairCertificate Ainv E) := by
  let M : Fin n → Fin n → ℝ := higham7_26_distanceMajorant n Ainv E
  have hM : ∀ i j : Fin n, 0 ≤ M i j := by
    simpa [M] using higham7_26_distanceMajorant_nonneg n Ainv E hE
  obtain ⟨mu, z, x, _hz_ne, hx_ne, hx_nonneg, _heig, hrad, hsub⟩ :=
    ch7_exists_spectralRadius_attaining_nonneg_subeigenvector hn M hM
  have hrad_matrix :
      (nnnorm mu : ENNReal) =
        spectralRadius ℂ
          (show Matrix (Fin n) (Fin n) ℂ from realRectToCMatrix M) := by
    calc
      (nnnorm mu : ENNReal) =
          spectralRadius ℂ
            (Matrix.toLin'
              (show Matrix (Fin n) (Fin n) ℂ from realRectToCMatrix M)) := hrad
      _ = spectralRadius ℂ
          (show Matrix (Fin n) (Fin n) ℂ from realRectToCMatrix M) :=
        ch7_toLin_spectralRadius_eq_matrix_spectralRadius _
  have hnorm_eq : ‖mu‖ = higham7_26_spectralRadius M := by
    have hreal := congrArg ENNReal.toReal hrad_matrix
    simpa [higham7_26_spectralRadius] using hreal
  apply higham7_26_nonempty_rumpEigenpairCertificate_of_subeigenvector
    hn Ainv E hE ‖mu‖ x
  · simpa [hnorm_eq, M] using hrho
  · exact hx_nonneg
  · exact hx_ne
  · simpa [M] using hsub
  · exact hnorm_eq

/-- Certificate-free upper half of Higham's equation (7.26), from the book
hypotheses alone. -/
theorem higham7_26_componentwiseDistance_le_rumpBound
    {n : ℕ} (hn : 0 < n)
    (A Ainv E : Fin n → Fin n → ℝ) (d : ℝ)
    (hInv : IsInverse n A Ainv)
    (hE : ∀ i j : Fin n, 0 ≤ E i j)
    (hd : IsHigham7_26ComponentwiseDistance A E d)
    (hrho : 0 < higham7_26_spectralRadius
      (higham7_26_distanceMajorant n Ainv E)) :
    d ≤ higham7_26_rumpFactor n /
      higham7_26_spectralRadius
        (higham7_26_distanceMajorant n Ainv E) := by
  let c : Higham7_26RumpEigenpairCertificate Ainv E :=
    Classical.choice
      (higham7_26_nonempty_rumpEigenpairCertificate hn Ainv E hE hrho)
  exact higham7_26_componentwiseDistance_le_rumpBound_of_eigenpairCertificate
    hn A Ainv E d hInv hd hrho c

/-- Certificate-free two-sided source equation (7.26). -/
theorem higham7_26_source_distance_sandwich
    {n : ℕ} (hn : 0 < n)
    (A Ainv E : Fin n → Fin n → ℝ) (d : ℝ)
    (hInv : IsInverse n A Ainv)
    (hE : ∀ i j : Fin n, 0 ≤ E i j)
    (hd : IsHigham7_26ComponentwiseDistance A E d)
    (hrho : 0 < higham7_26_spectralRadius
      (higham7_26_distanceMajorant n Ainv E)) :
    1 / higham7_26_spectralRadius
          (higham7_26_distanceMajorant n Ainv E) ≤ d ∧
      d ≤ higham7_26_rumpFactor n /
        higham7_26_spectralRadius
          (higham7_26_distanceMajorant n Ainv E) :=
  ⟨higham7_26_componentwiseDistance_ge_reciprocal_spectralRadius
      hn A Ainv E d hInv hE hd,
    higham7_26_componentwiseDistance_le_rumpBound
      hn A Ainv E d hInv hE hd hrho⟩

end NumStability
