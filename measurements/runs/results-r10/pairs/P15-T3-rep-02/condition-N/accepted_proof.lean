import HighamBench.P15Definitions

namespace HighamBench

open scoped BigOperators Matrix.Norms.Frobenius

set_option maxHeartbeats 1000000

lemma p15RectFrobNorm_eq_norm {m n : ℕ} (A : P15RectMatrix m n) :
    p15RectFrobNorm A = ‖A‖ := by
  rw [p15RectFrobNorm, Matrix.frobenius_norm_def]
  simp only [Real.norm_eq_abs, Real.rpow_two, sq_abs, Real.sqrt_eq_rpow]

lemma p15_orthonormal_transpose_mul_self {b r : ℕ}
    (X : P15RectMatrix b r) (hX : p15OrthonormalColumns X) :
    p15RectMatMul (p15RectTranspose X) X = (1 : P15Matrix r) := by
  ext j k
  simp only [p15RectMatMul, p15RectTranspose]
  rw [hX]
  rfl

lemma p15_orthonormal_left_norm {b r p : ℕ}
    (X : P15RectMatrix b r) (M : P15RectMatrix r p)
    (hX : p15OrthonormalColumns X) :
    p15RectFrobNorm (p15RectMatMul X M) = p15RectFrobNorm M := by
  unfold p15OrthonormalColumns at hX
  unfold p15RectFrobNorm
  congr 1
  calc
    ∑ i : Fin b, ∑ j : Fin p, (p15RectMatMul X M i j) ^ 2 =
        ∑ j : Fin p, ∑ k : Fin r, ∑ l : Fin r,
          M k j * M l j * (∑ i : Fin b, X i k * X i l) := by
            simp only [p15RectMatMul, Finset.sum_mul, Finset.mul_sum]
            rw [Finset.sum_comm]
            apply Finset.sum_congr rfl
            intro j hj
            simp only [pow_two]
            simp_rw [Finset.sum_mul, Finset.mul_sum]
            rw [Finset.sum_comm]
            apply Finset.sum_congr rfl
            intro k hk
            rw [Finset.sum_comm]
            apply Finset.sum_congr rfl
            intro l hl
            apply Finset.sum_congr rfl
            intro i hi
            ring
    _ = ∑ j : Fin p, ∑ k : Fin r, M k j ^ 2 := by
      apply Finset.sum_congr rfl
      intro j hj
      simp_rw [hX]
      apply Finset.sum_congr rfl
      intro k hk
      simp [pow_two]
    _ = ∑ i : Fin r, ∑ j : Fin p, M i j ^ 2 := Finset.sum_comm

lemma p15_transpose_norm {m n : ℕ} (A : P15RectMatrix m n) :
    p15RectFrobNorm (p15RectTranspose A) = p15RectFrobNorm A := by
  rw [p15RectFrobNorm_eq_norm, p15RectFrobNorm_eq_norm]
  exact Matrix.frobenius_norm_transpose A

lemma p15_orthonormal_right_norm {m b r : ℕ}
    (M : P15RectMatrix m r) (X : P15RectMatrix b r)
    (hX : p15OrthonormalColumns X) :
    p15RectFrobNorm (p15RectMatMul M (p15RectTranspose X)) =
      p15RectFrobNorm M := by
  calc
    p15RectFrobNorm (p15RectMatMul M (p15RectTranspose X)) =
        p15RectFrobNorm
          (p15RectTranspose (p15RectMatMul M (p15RectTranspose X))) :=
      (p15_transpose_norm _).symm
    _ = p15RectFrobNorm (p15RectMatMul X (p15RectTranspose M)) := by
      congr 1
      ext i j
      simp only [p15RectTranspose, p15RectMatMul]
      apply Finset.sum_congr rfl
      intro k hk
      ring
    _ = p15RectFrobNorm (p15RectTranspose M) :=
      p15_orthonormal_left_norm X (p15RectTranspose M) hX
    _ = p15RectFrobNorm M := p15_transpose_norm M

lemma p15_orthonormal_norm {b r : ℕ}
    (X : P15RectMatrix b r) (hX : p15OrthonormalColumns X) :
    p15RectFrobNorm X = Real.sqrt (r : ℝ) := by
  unfold p15RectFrobNorm
  congr 1
  calc
    ∑ i : Fin b, ∑ j : Fin r, X i j ^ 2 =
        ∑ j : Fin r, ∑ i : Fin b, X i j ^ 2 := Finset.sum_comm
    _ = ∑ j : Fin r, 1 := by
      apply Finset.sum_congr rfl
      intro j hj
      simpa only [pow_two, if_pos rfl] using hX j j
    _ = (r : ℝ) := by simp

lemma p15RectFrobNorm_nonneg {m n : ℕ} (A : P15RectMatrix m n) :
    0 ≤ p15RectFrobNorm A := by
  rw [p15RectFrobNorm_eq_norm]
  exact norm_nonneg A

lemma p15RectFrobNorm_add_le {m n : ℕ}
    (A B : P15RectMatrix m n) :
    p15RectFrobNorm (A + B) ≤ p15RectFrobNorm A + p15RectFrobNorm B := by
  simpa only [p15RectFrobNorm_eq_norm] using norm_add_le A B

lemma p15RectFrobNorm_sub_le {m n : ℕ}
    (A B : P15RectMatrix m n) :
    p15RectFrobNorm (A - B) ≤ p15RectFrobNorm A + p15RectFrobNorm B := by
  simpa only [p15RectFrobNorm_eq_norm] using norm_sub_le A B

lemma p15RectFrobNorm_add_add_le {m n : ℕ}
    (A B C : P15RectMatrix m n) :
    p15RectFrobNorm (A + B + C) ≤
      p15RectFrobNorm A + p15RectFrobNorm B + p15RectFrobNorm C := by
  exact (p15RectFrobNorm_add_le (A + B) C).trans
    (add_le_add (p15RectFrobNorm_add_le A B) (le_refl _))

lemma p15RectFrobNorm_mul_le {m n p : ℕ}
    (A : P15RectMatrix m n) (B : P15RectMatrix n p) :
    p15RectFrobNorm (p15RectMatMul A B) ≤
      p15RectFrobNorm A * p15RectFrobNorm B := by
  simpa only [p15RectFrobNorm_eq_norm] using
    (Matrix.frobenius_norm_mul A B)

lemma p15RectMatMul_assoc {m n p q : ℕ}
    (A : P15RectMatrix m n) (B : P15RectMatrix n p)
    (C : P15RectMatrix p q) :
    p15RectMatMul (p15RectMatMul A B) C =
      p15RectMatMul A (p15RectMatMul B C) := by
  change A * B * C = A * (B * C)
  exact Matrix.mul_assoc A B C

lemma p15RectMatMul_add_left {m n p : ℕ}
    (A B : P15RectMatrix m n) (C : P15RectMatrix n p) :
    p15RectMatMul (A + B) C = p15RectMatMul A C + p15RectMatMul B C := by
  change (A + B) * C = A * C + B * C
  exact Matrix.add_mul A B C

lemma p15RectMatMul_add_right {m n p : ℕ}
    (A : P15RectMatrix m n) (B C : P15RectMatrix n p) :
    p15RectMatMul A (B + C) = p15RectMatMul A B + p15RectMatMul A C := by
  change A * (B + C) = A * B + A * C
  exact Matrix.mul_add A B C

lemma p15GammaReal_nonneg {a u : ℝ} (ha : 0 ≤ a) (hu : 0 ≤ u)
    (hvalid : a * u < 1) : 0 ≤ p15GammaReal a u := by
  unfold p15GammaReal
  exact div_nonneg (mul_nonneg ha hu) (by linarith)

lemma p15GammaReal_add {a c u : ℝ}
    (ha : 0 ≤ a) (hc : 0 ≤ c) (hu : 0 ≤ u)
    (hvalid : (a + c) * u < 1) :
    p15GammaReal a u + p15GammaReal c u +
        p15GammaReal a u * p15GammaReal c u ≤
      p15GammaReal (a + c) u := by
  have hau : a * u < 1 := by nlinarith [mul_nonneg hc hu]
  have hcu : c * u < 1 := by nlinarith [mul_nonneg ha hu]
  have hda : 0 < 1 - a * u := by linarith
  have hdc : 0 < 1 - c * u := by linarith
  have hds : 0 < 1 - (a + c) * u := by linarith
  have hprod : 0 < (1 - a * u) * (1 - c * u) := mul_pos hda hdc
  have hden : 1 - (a + c) * u ≤ (1 - a * u) * (1 - c * u) := by
    nlinarith [mul_nonneg (mul_nonneg ha hc) (sq_nonneg u)]
  have hleft :
      p15GammaReal a u + p15GammaReal c u +
          p15GammaReal a u * p15GammaReal c u =
        1 / ((1 - a * u) * (1 - c * u)) - 1 := by
    unfold p15GammaReal
    have hda' : 1 - u * a ≠ 0 := by nlinarith
    have hdc' : 1 - u * c ≠ 0 := by nlinarith
    field_simp [ne_of_gt hda, ne_of_gt hdc, hda', hdc']
    <;> ring
  have hright :
      p15GammaReal (a + c) u = 1 / (1 - (a + c) * u) - 1 := by
    unfold p15GammaReal
    field_simp [ne_of_gt hds]
    ring
  rw [hleft, hright]
  linarith [one_div_le_one_div_of_le hds hden]

lemma p15GammaReal_scale_le {a s u : ℝ}
    (ha : 0 ≤ a) (hs : 1 ≤ s) (hu : 0 ≤ u)
    (hvalid : (a * s) * u < 1) :
    s * p15GammaReal a u ≤ p15GammaReal (a * s) u := by
  have has : 0 ≤ a * s := mul_nonneg ha (by linarith)
  have ha_le : a ≤ a * s := by
    calc
      a = a * 1 := by ring
      _ ≤ a * s := mul_le_mul_of_nonneg_left hs ha
  have hau_le : a * u ≤ (a * s) * u :=
    mul_le_mul_of_nonneg_right ha_le hu
  have htarget : 0 < 1 - (a * s) * u := by linarith
  have hsource : 0 < 1 - a * u := by linarith
  have hfrac :
      (a * s * u) / (1 - a * u) ≤
        (a * s * u) / (1 - (a * s) * u) := by
    exact div_le_div₀ (mul_nonneg has hu) le_rfl htarget (by linarith)
  unfold p15GammaReal
  convert hfrac using 1 <;> ring

lemma p15_low_rank_gamma_accumulation (b r : ℕ) (u : ℝ)
    (hu : 0 ≤ u)
    (hvalid : p15LowRankMatMulCost b r * u < 1) :
    let gb := p15GammaReal (b : ℝ) u
    let gr := p15GammaReal (r : ℝ) u
    let s := Real.sqrt (r : ℝ)
    let gc := p15GammaReal (p15LowRankMatMulCost b r) u
    gb + gr * s * (1 + gb) +
        gr * s * (1 + gb + gr * s * (1 + gb)) ≤ gc := by
  dsimp only
  by_cases hr0 : r = 0
  · subst r
    simp [p15LowRankMatMulCost, p15GammaReal]
  · have hrNat : 1 ≤ r := (Nat.one_le_iff_ne_zero).2 hr0
    let B : ℝ := (b : ℝ)
    let R : ℝ := (r : ℝ)
    let s : ℝ := Real.sqrt R
    let q : ℝ := R * s
    let gb : ℝ := p15GammaReal B u
    let gr : ℝ := p15GammaReal R u
    let gq : ℝ := p15GammaReal q u
    let g1 : ℝ := p15GammaReal (B + q) u
    let gc : ℝ := p15GammaReal (B + 2 * q) u
    have hB : 0 ≤ B := by positivity
    have hR : 0 ≤ R := by positivity
    have hs : 1 ≤ s := by
      dsimp [s, R]
      simpa using (show (1 : ℝ) ≤ (r : ℝ) by exact_mod_cast hrNat)
    have hq : 0 ≤ q := mul_nonneg hR (by linarith)
    have hcost : p15LowRankMatMulCost b r = B + 2 * q := by
      simp only [p15LowRankMatMulCost, B, q, R, s]
      ring
    have hK : (B + 2 * q) * u < 1 := by simpa [hcost] using hvalid
    have hqvalid : q * u < 1 := by
      nlinarith [mul_nonneg hB hu, mul_nonneg hq hu]
    have hBqvalid : (B + q) * u < 1 := by
      nlinarith [mul_nonneg hq hu]
    have hBvalid : B * u < 1 := by
      nlinarith [mul_nonneg hq hu]
    have hRvalid : R * u < 1 := by
      have hRq : R ≤ q := by dsimp [q]; nlinarith
      nlinarith [mul_nonneg (sub_nonneg.mpr hRq) hu]
    have ht : gr * s ≤ gq := by
      have := p15GammaReal_scale_le hR hs hu hqvalid
      simpa [gr, gq, q, mul_comm] using this
    have hgb : 0 ≤ gb := p15GammaReal_nonneg hB hu hBvalid
    have hgr : 0 ≤ gr := p15GammaReal_nonneg hR hu hRvalid
    have hgq : 0 ≤ gq := p15GammaReal_nonneg hq hu hqvalid
    have ht0 : 0 ≤ gr * s := mul_nonneg hgr (by linarith)
    have hfirst : gb + gq + gb * gq ≤ g1 := by
      simpa [gb, gq, g1] using p15GammaReal_add hB hq hu hBqvalid
    let c1 : ℝ := gb + gr * s + gb * (gr * s)
    have hc1zero : 0 ≤ c1 := by dsimp [c1]; positivity
    have hc1 : c1 ≤ g1 := by
      have hmono : gb + gr * s + gb * (gr * s) ≤ gb + gq + gb * gq := by
        nlinarith [mul_nonneg hgb (sub_nonneg.mpr ht)]
      exact hmono.trans hfirst
    have hg1 : 0 ≤ g1 :=
      p15GammaReal_nonneg (add_nonneg hB hq) hu hBqvalid
    have hsecond : g1 + gq + g1 * gq ≤ gc := by
      have hK' : (B + q + q) * u < 1 := by nlinarith
      have hadd := p15GammaReal_add (add_nonneg hB hq) hq hu hK'
      dsimp [g1, gq, gc] at ⊢ hadd
      convert hadd using 1 <;> ring
    have hmono2 : c1 + gr * s + c1 * (gr * s) ≤
        g1 + gq + g1 * gq := by
      have hA := mul_nonneg (sub_nonneg.mpr hc1) (by nlinarith : 0 ≤ 1 + gq)
      have hT := mul_nonneg (sub_nonneg.mpr ht) (by nlinarith : 0 ≤ 1 + c1)
      nlinarith
    have hfinal : c1 + gr * s + c1 * (gr * s) ≤ gc :=
      hmono2.trans hsecond
    rw [hcost]
    change gb + gr * s * (1 + gb) +
        gr * s * (1 + gb + gr * s * (1 + gb)) ≤ gc
    dsimp [c1] at hfinal
    convert hfinal using 1 <;> ring

lemma p15_trace_low_rank_error {b r : ℕ} {u : ℝ}
    {XA YA XB YB : P15RectMatrix b r}
    (hu : 0 ≤ u)
    (hvalid : p15LowRankMatMulCost b r * u < 1)
    (hXA : p15OrthonormalColumns XA)
    (hXB : p15OrthonormalColumns XB)
    (trace : P15LowRankMatMulTrace u XA YA XB YB) :
    p15FrobNorm
        (trace.result -
          p15MatMul (p15LowRankMatrix XA YA) (p15LowRankMatrix YB XB)) ≤
      p15GammaReal (p15LowRankMatMulCost b r) u *
        p15FrobNorm (p15LowRankMatrix XA YA) *
        p15FrobNorm (p15LowRankMatrix YB XB) := by
  let At : P15Matrix b := p15LowRankMatrix XA YA
  let Bt : P15Matrix b := p15LowRankMatrix YB XB
  let N : ℝ := p15FrobNorm At * p15FrobNorm Bt
  let gb : ℝ := p15GammaReal (b : ℝ) u
  let gr : ℝ := p15GammaReal (r : ℝ) u
  let s : ℝ := Real.sqrt (r : ℝ)
  let gc : ℝ := p15GammaReal (p15LowRankMatMulCost b r) u
  have hcostnonneg : 0 ≤ p15LowRankMatMulCost b r := by
    unfold p15LowRankMatMulCost
    positivity
  have hgc : 0 ≤ gc :=
    p15GammaReal_nonneg hcostnonneg hu hvalid
  have hgbvalid : (b : ℝ) * u < 1 := by
    unfold p15LowRankMatMulCost at hvalid
    have hrs : 0 ≤ 2 * (r : ℝ) * Real.sqrt (r : ℝ) := by positivity
    nlinarith [mul_nonneg hrs hu]
  have hgrvalid : (r : ℝ) * u < 1 := by
    by_cases hr0 : r = 0
    · subst r
      simpa using (show (0 : ℝ) < 1 by norm_num)
    · have hrsqrt : 1 ≤ Real.sqrt (r : ℝ) := by
        simpa using (show (1 : ℝ) ≤ (r : ℝ) by
          exact_mod_cast (Nat.one_le_iff_ne_zero.2 hr0))
      unfold p15LowRankMatMulCost at hvalid
      have hb0 : 0 ≤ (b : ℝ) := by positivity
      have hr0' : 0 ≤ (r : ℝ) := by positivity
      have hru : (r : ℝ) * u ≤
          ((b : ℝ) + 2 * (r : ℝ) * Real.sqrt (r : ℝ)) * u := by
        have hle : (r : ℝ) ≤
            (b : ℝ) + 2 * (r : ℝ) * Real.sqrt (r : ℝ) := by
          nlinarith [mul_nonneg hr0' (sub_nonneg.mpr hrsqrt)]
        exact mul_le_mul_of_nonneg_right hle hu
      linarith
  have hgb : 0 ≤ gb := p15GammaReal_nonneg (by positivity) hu hgbvalid
  have hgr : 0 ≤ gr := p15GammaReal_nonneg (by positivity) hu hgrvalid
  have hs : 0 ≤ s := Real.sqrt_nonneg _
  have hAt0 : 0 ≤ p15FrobNorm At := p15RectFrobNorm_nonneg At
  have hBt0 : 0 ≤ p15FrobNorm Bt := p15RectFrobNorm_nonneg Bt
  have hN : 0 ≤ N := mul_nonneg hAt0 hBt0
  have hXAnorm : p15RectFrobNorm XA = s := p15_orthonormal_norm XA hXA
  have hXBnorm : p15RectFrobNorm (p15RectTranspose XB) = s := by
    rw [p15_transpose_norm, p15_orthonormal_norm XB hXB]
  have hYAnorm : p15RectFrobNorm (p15RectTranspose YA) = p15FrobNorm At := by
    dsimp [At]
    exact (p15_orthonormal_left_norm XA (p15RectTranspose YA) hXA).symm
  have hYBnorm : p15RectFrobNorm YB = p15FrobNorm Bt := by
    dsimp [Bt]
    symm
    exact p15_orthonormal_right_norm YB XB hXB
  have hacc := p15_low_rank_gamma_accumulation b r u hu hvalid
  dsimp only at hacc
  change p15FrobNorm (trace.result - p15MatMul At Bt) ≤
    gc * p15FrobNorm At * p15FrobNorm Bt
  rw [mul_assoc]
  change p15FrobNorm (trace.result - p15MatMul At Bt) ≤ gc * N
  cases trace with
  | leftAssociated middleStage leftStage finalStage =>
      let e0 := middleStage.error
      let e1 := leftStage.error
      let e2 := finalStage.error
      have he0 : p15RectFrobNorm e0 ≤ gb * N := by
        have hm := middleStage.error_le
        rw [hYAnorm, hYBnorm] at hm
        rw [mul_assoc] at hm
        exact hm
      have hmprod :
          p15RectFrobNorm
              (p15RectMatMul (p15RectTranspose YA) YB) ≤ N := by
        have hm := p15RectFrobNorm_mul_le (p15RectTranspose YA) YB
        rw [hYAnorm, hYBnorm] at hm
        exact hm
      have hmiddle : p15RectFrobNorm middleStage.result ≤ (1 + gb) * N := by
        calc
          p15RectFrobNorm middleStage.result =
              p15RectFrobNorm
                (p15RectMatMul (p15RectTranspose YA) YB + e0) := rfl
          _ ≤ p15RectFrobNorm (p15RectMatMul (p15RectTranspose YA) YB) +
                p15RectFrobNorm e0 := p15RectFrobNorm_add_le _ _
          _ ≤ N + gb * N := add_le_add hmprod he0
          _ = (1 + gb) * N := by ring
      have he1 : p15RectFrobNorm e1 ≤ gr * s * ((1 + gb) * N) := by
        have he := leftStage.error_le
        rw [hXAnorm] at he
        calc
          p15RectFrobNorm e1 ≤ gr * s * p15RectFrobNorm middleStage.result := he
          _ ≤ gr * s * ((1 + gb) * N) :=
            mul_le_mul_of_nonneg_left hmiddle (mul_nonneg hgr hs)
      have hleft : p15RectFrobNorm leftStage.result ≤
          (1 + gb + gr * s * (1 + gb)) * N := by
        calc
          p15RectFrobNorm leftStage.result =
              p15RectFrobNorm
                (p15RectMatMul XA middleStage.result + e1) := rfl
          _ ≤ p15RectFrobNorm (p15RectMatMul XA middleStage.result) +
                p15RectFrobNorm e1 := p15RectFrobNorm_add_le _ _
          _ = p15RectFrobNorm middleStage.result + p15RectFrobNorm e1 := by
            rw [p15_orthonormal_left_norm XA middleStage.result hXA]
          _ ≤ (1 + gb) * N + gr * s * ((1 + gb) * N) :=
            add_le_add hmiddle he1
          _ = (1 + gb + gr * s * (1 + gb)) * N := by ring
      have he2 : p15RectFrobNorm e2 ≤
          gr * s * ((1 + gb + gr * s * (1 + gb)) * N) := by
        have he := finalStage.error_le
        rw [hXBnorm] at he
        calc
          p15RectFrobNorm e2 ≤ gr * p15RectFrobNorm leftStage.result * s := he
          _ = gr * s * p15RectFrobNorm leftStage.result := by ring
          _ ≤ gr * s * ((1 + gb + gr * s * (1 + gb)) * N) :=
            mul_le_mul_of_nonneg_left hleft (mul_nonneg hgr hs)
      have herr :
          finalStage.result - p15MatMul At Bt =
            p15RectMatMul (p15RectMatMul XA e0) (p15RectTranspose XB) +
              p15RectMatMul e1 (p15RectTranspose XB) + e2 := by
        change
          ((XA * ((p15RectTranspose YA * YB) + e0) + e1) *
                p15RectTranspose XB + e2) -
              ((XA * p15RectTranspose YA) * (YB * p15RectTranspose XB)) =
            (XA * e0) * p15RectTranspose XB +
              e1 * p15RectTranspose XB + e2
        simp only [Matrix.mul_add, Matrix.add_mul, Matrix.mul_assoc]
        abel
      change p15FrobNorm (finalStage.result - p15MatMul At Bt) ≤ gc * N
      rw [herr]
      calc
        p15FrobNorm
            (p15RectMatMul (p15RectMatMul XA e0) (p15RectTranspose XB) +
              p15RectMatMul e1 (p15RectTranspose XB) + e2) ≤
            (p15RectFrobNorm e0 + p15RectFrobNorm e1) +
              p15RectFrobNorm e2 := by
          calc
            _ ≤ p15RectFrobNorm
                    (p15RectMatMul (p15RectMatMul XA e0) (p15RectTranspose XB)) +
                  p15RectFrobNorm (p15RectMatMul e1 (p15RectTranspose XB)) +
                  p15RectFrobNorm e2 := p15RectFrobNorm_add_add_le _ _ _
            _ = (p15RectFrobNorm e0 + p15RectFrobNorm e1) +
                  p15RectFrobNorm e2 := by
              rw [p15_orthonormal_right_norm (p15RectMatMul XA e0) XB hXB,
                p15_orthonormal_left_norm XA e0 hXA,
                p15_orthonormal_right_norm e1 XB hXB]
        _ ≤ (gb * N + gr * s * ((1 + gb) * N)) +
              gr * s * ((1 + gb + gr * s * (1 + gb)) * N) :=
          add_le_add (add_le_add he0 he1) he2
        _ = (gb + gr * s * (1 + gb) +
              gr * s * (1 + gb + gr * s * (1 + gb))) * N := by ring
        _ ≤ gc * N := mul_le_mul_of_nonneg_right hacc hN

  | rightAssociated middleStage rightStage finalStage =>
      let e0 := middleStage.error
      let e1 := rightStage.error
      let e2 := finalStage.error
      have he0 : p15RectFrobNorm e0 ≤ gb * N := by
        have hm := middleStage.error_le
        rw [hYAnorm, hYBnorm] at hm
        rw [mul_assoc] at hm
        exact hm
      have hmprod :
          p15RectFrobNorm
              (p15RectMatMul (p15RectTranspose YA) YB) ≤ N := by
        have hm := p15RectFrobNorm_mul_le (p15RectTranspose YA) YB
        rw [hYAnorm, hYBnorm] at hm
        exact hm
      have hmiddle : p15RectFrobNorm middleStage.result ≤ (1 + gb) * N := by
        calc
          p15RectFrobNorm middleStage.result =
              p15RectFrobNorm
                (p15RectMatMul (p15RectTranspose YA) YB + e0) := rfl
          _ ≤ p15RectFrobNorm (p15RectMatMul (p15RectTranspose YA) YB) +
                p15RectFrobNorm e0 := p15RectFrobNorm_add_le _ _
          _ ≤ N + gb * N := add_le_add hmprod he0
          _ = (1 + gb) * N := by ring
      have he1 : p15RectFrobNorm e1 ≤ gr * s * ((1 + gb) * N) := by
        have he := rightStage.error_le
        rw [hXBnorm] at he
        calc
          p15RectFrobNorm e1 ≤ gr * p15RectFrobNorm middleStage.result * s := he
          _ = gr * s * p15RectFrobNorm middleStage.result := by ring
          _ ≤ gr * s * ((1 + gb) * N) :=
            mul_le_mul_of_nonneg_left hmiddle (mul_nonneg hgr hs)
      have hright : p15RectFrobNorm rightStage.result ≤
          (1 + gb + gr * s * (1 + gb)) * N := by
        calc
          p15RectFrobNorm rightStage.result =
              p15RectFrobNorm
                (p15RectMatMul middleStage.result (p15RectTranspose XB) + e1) := rfl
          _ ≤ p15RectFrobNorm
                  (p15RectMatMul middleStage.result (p15RectTranspose XB)) +
                p15RectFrobNorm e1 := p15RectFrobNorm_add_le _ _
          _ = p15RectFrobNorm middleStage.result + p15RectFrobNorm e1 := by
            rw [p15_orthonormal_right_norm middleStage.result XB hXB]
          _ ≤ (1 + gb) * N + gr * s * ((1 + gb) * N) :=
            add_le_add hmiddle he1
          _ = (1 + gb + gr * s * (1 + gb)) * N := by ring
      have he2 : p15RectFrobNorm e2 ≤
          gr * s * ((1 + gb + gr * s * (1 + gb)) * N) := by
        have he := finalStage.error_le
        rw [hXAnorm] at he
        calc
          p15RectFrobNorm e2 ≤ gr * s * p15RectFrobNorm rightStage.result := he
          _ ≤ gr * s * ((1 + gb + gr * s * (1 + gb)) * N) :=
            mul_le_mul_of_nonneg_left hright (mul_nonneg hgr hs)
      have herr :
          finalStage.result - p15MatMul At Bt =
            p15RectMatMul XA
                (p15RectMatMul e0 (p15RectTranspose XB)) +
              p15RectMatMul XA e1 + e2 := by
        change
          (XA * (((p15RectTranspose YA * YB) + e0) *
                  p15RectTranspose XB + e1) + e2) -
              ((XA * p15RectTranspose YA) * (YB * p15RectTranspose XB)) =
            XA * (e0 * p15RectTranspose XB) + XA * e1 + e2
        simp only [Matrix.mul_add, Matrix.add_mul, Matrix.mul_assoc]
        abel
      change p15FrobNorm (finalStage.result - p15MatMul At Bt) ≤ gc * N
      rw [herr]
      calc
        p15FrobNorm
            (p15RectMatMul XA (p15RectMatMul e0 (p15RectTranspose XB)) +
              p15RectMatMul XA e1 + e2) ≤
            (p15RectFrobNorm e0 + p15RectFrobNorm e1) +
              p15RectFrobNorm e2 := by
          calc
            _ ≤ p15RectFrobNorm
                    (p15RectMatMul XA
                      (p15RectMatMul e0 (p15RectTranspose XB))) +
                  p15RectFrobNorm (p15RectMatMul XA e1) +
                  p15RectFrobNorm e2 := p15RectFrobNorm_add_add_le _ _ _
            _ = (p15RectFrobNorm e0 + p15RectFrobNorm e1) +
                  p15RectFrobNorm e2 := by
              rw [p15_orthonormal_left_norm XA
                    (p15RectMatMul e0 (p15RectTranspose XB)) hXA,
                p15_orthonormal_right_norm e0 XB hXB,
                p15_orthonormal_left_norm XA e1 hXA]
        _ ≤ (gb * N + gr * s * ((1 + gb) * N)) +
              gr * s * ((1 + gb + gr * s * (1 + gb)) * N) :=
          add_le_add (add_le_add he0 he1) he2
        _ = (gb + gr * s * (1 + gb) +
              gr * s * (1 + gb + gr * s * (1 + gb))) * N := by ring
        _ ≤ gc * N := mul_le_mul_of_nonneg_right hacc hN

lemma p15_matmul_perturbation_bound {n : ℕ}
    (R At Bt A B EA EB : P15Matrix n) (g ea eb : ℝ)
    (hg : 0 ≤ g)
    (hAt : At = A + EA) (hBt : Bt = B + EB)
    (hEA : p15FrobNorm EA ≤ ea) (hEB : p15FrobNorm EB ≤ eb)
    (hfirst : p15FrobNorm (R - p15MatMul At Bt) ≤
      g * p15FrobNorm At * p15FrobNorm Bt) :
    p15FrobNorm (R - p15MatMul A B) ≤
      g * p15FrobNorm A * p15FrobNorm B +
        (1 + g) *
          (ea * p15FrobNorm B + p15FrobNorm A * eb + ea * eb) := by
  have hea0 : 0 ≤ ea :=
    (p15RectFrobNorm_nonneg EA).trans hEA
  have heb0 : 0 ≤ eb :=
    (p15RectFrobNorm_nonneg EB).trans hEB
  have hA0 : 0 ≤ p15FrobNorm A := p15RectFrobNorm_nonneg A
  have hB0 : 0 ≤ p15FrobNorm B := p15RectFrobNorm_nonneg B
  have hBt0 : 0 ≤ p15FrobNorm Bt := p15RectFrobNorm_nonneg Bt
  have hAtnorm : p15FrobNorm At ≤ p15FrobNorm A + ea := by
    rw [hAt]
    exact (p15RectFrobNorm_add_le A EA).trans
      (add_le_add (le_refl _) hEA)
  have hBtnorm : p15FrobNorm Bt ≤ p15FrobNorm B + eb := by
    rw [hBt]
    exact (p15RectFrobNorm_add_le B EB).trans
      (add_le_add (le_refl _) hEB)
  have hAtBt : p15FrobNorm At * p15FrobNorm Bt ≤
      (p15FrobNorm A + ea) * (p15FrobNorm B + eb) := by
    exact mul_le_mul hAtnorm hBtnorm hBt0 (add_nonneg hA0 hea0)
  have hfirst' : p15FrobNorm (R - p15MatMul At Bt) ≤
      g * ((p15FrobNorm A + ea) * (p15FrobNorm B + eb)) := by
    calc
      _ ≤ g * p15FrobNorm At * p15FrobNorm Bt := hfirst
      _ = g * (p15FrobNorm At * p15FrobNorm Bt) := by ring
      _ ≤ g * ((p15FrobNorm A + ea) * (p15FrobNorm B + eb)) :=
        mul_le_mul_of_nonneg_left hAtBt hg
  have hpert : p15FrobNorm
        (p15MatMul EA B + p15MatMul A EB + p15MatMul EA EB) ≤
      ea * p15FrobNorm B + p15FrobNorm A * eb + ea * eb := by
    calc
      _ ≤ p15FrobNorm (p15MatMul EA B) +
            p15FrobNorm (p15MatMul A EB) +
            p15FrobNorm (p15MatMul EA EB) :=
        p15RectFrobNorm_add_add_le _ _ _
      _ ≤ (p15FrobNorm EA * p15FrobNorm B) +
            (p15FrobNorm A * p15FrobNorm EB) +
            (p15FrobNorm EA * p15FrobNorm EB) := by
        exact add_le_add
          (add_le_add (p15RectFrobNorm_mul_le EA B)
            (p15RectFrobNorm_mul_le A EB))
          (p15RectFrobNorm_mul_le EA EB)
      _ ≤ ea * p15FrobNorm B + p15FrobNorm A * eb + ea * eb := by
        exact add_le_add
          (add_le_add
            (mul_le_mul_of_nonneg_right hEA hB0)
            (mul_le_mul_of_nonneg_left hEB hA0))
          (mul_le_mul hEA hEB (p15RectFrobNorm_nonneg EB) hea0)
  have herr :
      R - p15MatMul A B =
        (R - p15MatMul At Bt) +
          (p15MatMul EA B + p15MatMul A EB + p15MatMul EA EB) := by
    rw [hAt, hBt]
    change
      R - A * B =
        (R - (A + EA) * (B + EB)) +
          (EA * B + A * EB + EA * EB)
    simp only [Matrix.mul_add, Matrix.add_mul]
    abel
  rw [herr]
  calc
    p15FrobNorm
        ((R - p15MatMul At Bt) +
          (p15MatMul EA B + p15MatMul A EB + p15MatMul EA EB)) ≤
      p15FrobNorm (R - p15MatMul At Bt) +
        p15FrobNorm (p15MatMul EA B + p15MatMul A EB + p15MatMul EA EB) :=
      p15RectFrobNorm_add_le _ _
    _ ≤ g * ((p15FrobNorm A + ea) * (p15FrobNorm B + eb)) +
          (ea * p15FrobNorm B + p15FrobNorm A * eb + ea * eb) :=
      add_le_add hfirst' hpert
    _ = g * p15FrobNorm A * p15FrobNorm B +
          (1 + g) *
            (ea * p15FrobNorm B + p15FrobNorm A * eb + ea * eb) := by
      ring

theorem p15_t3_low_rank_matmul_error {b r : ℕ}
    (run : P15LowRankMatMulExecution b r) :
    let Atilde := p15LowRankMatrix run.XA run.YA
    let Btilde := p15LowRankMatrix run.YB run.XB
    let gammaC :=
      p15GammaReal (p15LowRankMatMulCost b r) run.unitRoundoff
    p15FrobNorm (run.trace.result - p15MatMul Atilde Btilde) ≤
        gammaC * p15FrobNorm Atilde * p15FrobNorm Btilde ∧
      p15FrobNorm (run.trace.result - p15MatMul run.A run.B) ≤
        gammaC * p15FrobNorm run.A * p15FrobNorm run.B +
          run.epsilon * (1 + gammaC) *
            (run.betaA * p15FrobNorm run.B +
              p15FrobNorm run.A * run.betaB +
              run.epsilon * run.betaA * run.betaB) := by
  -- PROOF_START P15-T3-H001
  dsimp only
  let Atilde : P15Matrix b := p15LowRankMatrix run.XA run.YA
  let Btilde : P15Matrix b := p15LowRankMatrix run.YB run.XB
  let gammaC : ℝ :=
    p15GammaReal (p15LowRankMatMulCost b r) run.unitRoundoff
  have hfirst :
      p15FrobNorm (run.trace.result - p15MatMul Atilde Btilde) ≤
        gammaC * p15FrobNorm Atilde * p15FrobNorm Btilde := by
    exact p15_trace_low_rank_error run.unitRoundoff_nonneg run.gamma_valid
      run.xA_orthonormal run.xB_orthonormal run.trace
  constructor
  · exact hfirst
  · have hcostnonneg : 0 ≤ p15LowRankMatMulCost b r := by
      unfold p15LowRankMatMulCost
      positivity
    have hgamma : 0 ≤ gammaC :=
      p15GammaReal_nonneg hcostnonneg run.unitRoundoff_nonneg run.gamma_valid
    have hpert := p15_matmul_perturbation_bound
      run.trace.result Atilde Btilde run.A run.B
      run.approximationErrorA run.approximationErrorB gammaC
      (run.epsilon * run.betaA) (run.epsilon * run.betaB)
      hgamma run.approximationA_eq run.approximationB_eq
      run.approximationErrorA_le run.approximationErrorB_le hfirst
    convert hpert using 1 <;> ring

end HighamBench
