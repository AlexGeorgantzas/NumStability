import HighamBench.P15Definitions
import NumStability.Analysis.MatrixAlgebra

namespace HighamBench

lemma p15GammaReal_nonneg {k u : ℝ} (hk : 0 ≤ k) (hu : 0 ≤ u)
    (hvalid : k * u < 1) :
    0 ≤ p15GammaReal k u := by
  unfold p15GammaReal
  exact div_nonneg (mul_nonneg hk hu) (le_of_lt (sub_pos.mpr hvalid))

lemma p15_one_add_gammaReal {k u : ℝ} (hvalid : k * u < 1) :
    1 + p15GammaReal k u = 1 / (1 - k * u) := by
  unfold p15GammaReal
  have hne : 1 - k * u ≠ 0 := ne_of_gt (sub_pos.mpr hvalid)
  field_simp
  ring

lemma p15_one_add_gammaReal_mul_le {x y u : ℝ}
    (hx : 0 ≤ x) (hy : 0 ≤ y) (hu : 0 ≤ u)
    (hvalid : (x + y) * u < 1) :
    (1 + p15GammaReal x u) * (1 + p15GammaReal y u) ≤
      1 + p15GammaReal (x + y) u := by
  have hxu : x * u ≤ (x + y) * u := by nlinarith [mul_nonneg hy hu]
  have hyu : y * u ≤ (x + y) * u := by nlinarith [mul_nonneg hx hu]
  have hxv : x * u < 1 := lt_of_le_of_lt hxu hvalid
  have hyv : y * u < 1 := lt_of_le_of_lt hyu hvalid
  rw [p15_one_add_gammaReal hxv, p15_one_add_gammaReal hyv,
    p15_one_add_gammaReal hvalid]
  have hsumpos : 0 < 1 - (x + y) * u := sub_pos.mpr hvalid
  have hden : 1 - (x + y) * u ≤ (1 - x * u) * (1 - y * u) := by
    nlinarith [mul_nonneg (mul_nonneg hx hy) (sq_nonneg u)]
  calc
    (1 / (1 - x * u)) * (1 / (1 - y * u)) =
        1 / ((1 - x * u) * (1 - y * u)) := by
          field_simp
    _ ≤ 1 / (1 - (x + y) * u) :=
      one_div_le_one_div_of_le hsumpos hden

lemma p15_gammaReal_mul_scale_le {x z u : ℝ}
    (hx : 0 ≤ x) (hz : 1 ≤ z) (hu : 0 ≤ u)
    (hvalid : (x * z) * u < 1) :
    p15GammaReal x u * z ≤ p15GammaReal (x * z) u := by
  have hxzu : 0 ≤ x * z * u := mul_nonneg (mul_nonneg hx (le_trans (by norm_num) hz)) hu
  have hdenpos : 0 < 1 - (x * z) * u := sub_pos.mpr hvalid
  have hdenle : 1 - (x * z) * u ≤ 1 - x * u := by
    have h : 0 ≤ x * u * (z - 1) :=
      mul_nonneg (mul_nonneg hx hu) (sub_nonneg.mpr hz)
    nlinarith
  calc
    p15GammaReal x u * z = (x * z * u) / (1 - x * u) := by
      unfold p15GammaReal
      ring
    _ ≤ (x * z * u) / (1 - (x * z) * u) :=
      div_le_div_of_nonneg_left hxzu hdenpos hdenle
    _ = p15GammaReal (x * z) u := by
      unfold p15GammaReal
      ring

lemma p15RectFrobNorm_nonneg {m n : ℕ} (A : P15RectMatrix m n) :
    0 ≤ p15RectFrobNorm A := by
  exact Real.sqrt_nonneg _

lemma p15RectFrobNorm_add_le {m n : ℕ}
    (A B : P15RectMatrix m n) :
    p15RectFrobNorm (A + B) ≤ p15RectFrobNorm A + p15RectFrobNorm B := by
  simpa only [p15RectFrobNorm, NumStability.frobNormRect,
    NumStability.frobNormSqRect, Pi.add_apply] using
      (NumStability.frobNormRect_add_le A B)

lemma p15RectFrobNorm_rectMatMul_le {m n p : ℕ}
    (A : P15RectMatrix m n) (B : P15RectMatrix n p) :
    p15RectFrobNorm (p15RectMatMul A B) ≤
      p15RectFrobNorm A * p15RectFrobNorm B := by
  simpa only [p15RectFrobNorm, p15RectMatMul,
    NumStability.frobNormRect, NumStability.frobNormSqRect,
    NumStability.rectMatMul] using
      (NumStability.frobNormRect_rectMatMul_le A B)

lemma p15RectFrobNorm_transpose {m n : ℕ} (A : P15RectMatrix m n) :
    p15RectFrobNorm (p15RectTranspose A) = p15RectFrobNorm A := by
  unfold p15RectFrobNorm p15RectTranspose
  congr 1
  rw [Finset.sum_comm]

lemma p15RectFrobNorm_left_orthonormal {m r n : ℕ}
    (X : P15RectMatrix m r) (A : P15RectMatrix r n)
    (hX : p15OrthonormalColumns X) :
    p15RectFrobNorm (p15RectMatMul X A) = p15RectFrobNorm A := by
  unfold p15OrthonormalColumns at hX
  unfold p15RectFrobNorm p15RectMatMul
  congr 1
  conv_lhs => rw [Finset.sum_comm]
  conv_rhs => rw [Finset.sum_comm]
  apply Finset.sum_congr rfl
  intro j _
  have expand : ∀ i : Fin m,
      (∑ k : Fin r, X i k * A k j) ^ 2 =
        ∑ k : Fin r, ∑ l : Fin r,
          X i k * X i l * (A k j * A l j) := by
    intro i
    rw [sq, Finset.sum_mul]
    apply Finset.sum_congr rfl
    intro k _
    rw [Finset.mul_sum]
    apply Finset.sum_congr rfl
    intro l _
    ring
  simp_rw [expand]
  rw [Finset.sum_comm]
  have collapse : ∀ k : Fin r,
      ∑ i : Fin m, ∑ l : Fin r,
          X i k * X i l * (A k j * A l j) = A k j ^ 2 := by
    intro k
    rw [Finset.sum_comm]
    have factor : ∀ l : Fin r,
        ∑ i : Fin m, X i k * X i l * (A k j * A l j) =
          (∑ i : Fin m, X i k * X i l) * (A k j * A l j) := by
      intro l
      rw [← Finset.sum_mul]
    simp_rw [factor, hX]
    simp [Finset.sum_ite_eq, Finset.mem_univ]
    ring
  exact Finset.sum_congr rfl (fun k _ ↦ collapse k)

lemma p15RectFrobNorm_right_transpose_orthonormal {m r n : ℕ}
    (A : P15RectMatrix n r) (X : P15RectMatrix m r)
    (hX : p15OrthonormalColumns X) :
    p15RectFrobNorm (p15RectMatMul A (p15RectTranspose X)) =
      p15RectFrobNorm A := by
  unfold p15OrthonormalColumns at hX
  unfold p15RectFrobNorm p15RectMatMul p15RectTranspose
  congr 1
  apply Finset.sum_congr rfl
  intro i _
  have expand : ∀ j : Fin m,
      (∑ k : Fin r, A i k * X j k) ^ 2 =
        ∑ k : Fin r, ∑ l : Fin r,
          A i k * A i l * (X j k * X j l) := by
    intro j
    rw [sq, Finset.sum_mul]
    apply Finset.sum_congr rfl
    intro k _
    rw [Finset.mul_sum]
    apply Finset.sum_congr rfl
    intro l _
    ring
  simp_rw [expand]
  rw [Finset.sum_comm]
  have collapse : ∀ k : Fin r,
      ∑ j : Fin m, ∑ l : Fin r,
          A i k * A i l * (X j k * X j l) = A i k ^ 2 := by
    intro k
    rw [Finset.sum_comm]
    have factor : ∀ l : Fin r,
        ∑ j : Fin m, A i k * A i l * (X j k * X j l) =
          A i k * A i l * (∑ j : Fin m, X j k * X j l) := by
      intro l
      rw [Finset.mul_sum]
    simp_rw [factor, hX]
    simp [Finset.sum_ite_eq, Finset.mem_univ]
    ring
  exact Finset.sum_congr rfl (fun k _ ↦ collapse k)

lemma p15RectFrobNorm_orthonormal {m r : ℕ}
    (X : P15RectMatrix m r) (hX : p15OrthonormalColumns X) :
    p15RectFrobNorm X = Real.sqrt (r : ℝ) := by
  unfold p15RectFrobNorm
  congr 1
  rw [Finset.sum_comm]
  calc
    (∑ j : Fin r, ∑ i : Fin m, X i j ^ 2) = ∑ _j : Fin r, (1 : ℝ) := by
      apply Finset.sum_congr rfl
      intro j _
      simpa [sq] using hX j j
    _ = (r : ℝ) := by simp

lemma p15RectMatMul_assoc {m n p q : ℕ}
    (A : P15RectMatrix m n) (B : P15RectMatrix n p)
    (C : P15RectMatrix p q) :
    p15RectMatMul (p15RectMatMul A B) C =
      p15RectMatMul A (p15RectMatMul B C) := by
  simpa only [p15RectMatMul, NumStability.rectMatMul] using
    (NumStability.rectMatMul_assoc (A := A) (B := B) (C := C))

lemma p15_lowRank_three_stage_coefficient_le {b r : ℕ} {u : ℝ}
    (hu : 0 ≤ u) (hvalid : p15LowRankMatMulCost b r * u < 1) :
    (1 + p15GammaReal (b : ℝ) u) *
          (1 + p15GammaReal (r : ℝ) u * Real.sqrt (r : ℝ)) ^ 2 - 1 ≤
      p15GammaReal (p15LowRankMatMulCost b r) u := by
  by_cases hrzero : r = 0
  · subst r
    simpa [p15LowRankMatMulCost, p15GammaReal] using le_rfl
  · have hrnat : 1 ≤ r := (Nat.one_le_iff_ne_zero).mpr hrzero
    let br : ℝ := (b : ℝ)
    let rr : ℝ := (r : ℝ)
    let z : ℝ := Real.sqrt rr
    let s : ℝ := rr * z
    let gb : ℝ := p15GammaReal br u
    let gr : ℝ := p15GammaReal rr u
    let gs : ℝ := p15GammaReal s u
    have hbr0 : 0 ≤ br := Nat.cast_nonneg b
    have hrr0 : 0 ≤ rr := Nat.cast_nonneg r
    have hz1 : 1 ≤ z := by
      dsimp [z, rr]
      exact Real.one_le_sqrt.mpr (by exact_mod_cast hrnat)
    have hz0 : 0 ≤ z := le_trans (by norm_num) hz1
    have hs0 : 0 ≤ s := mul_nonneg hrr0 hz0
    have hcost : p15LowRankMatMulCost b r = br + s + s := by
      simp [p15LowRankMatMulCost, br, rr, s, z]
      ring
    rw [hcost] at hvalid ⊢
    have hsv : s * u < 1 := by
      have hle : s * u ≤ (br + s + s) * u := by
        nlinarith [mul_nonneg hbr0 hu, mul_nonneg hs0 hu]
      exact lt_of_le_of_lt hle hvalid
    have hbsv : (br + s) * u < 1 := by
      have hle : (br + s) * u ≤ (br + s + s) * u := by
        nlinarith [mul_nonneg hs0 hu]
      exact lt_of_le_of_lt hle hvalid
    have hbv : br * u < 1 := by
      have hle : br * u ≤ (br + s + s) * u := by
        nlinarith [mul_nonneg hs0 hu]
      exact lt_of_le_of_lt hle hvalid
    have hrv : rr * u < 1 := by
      have hrs : rr ≤ s := by
        dsimp [s]
        nlinarith [mul_nonneg hrr0 (sub_nonneg.mpr hz1)]
      have hle : rr * u ≤ s * u := mul_le_mul_of_nonneg_right hrs hu
      exact lt_of_le_of_lt hle hsv
    have hgb0 : 0 ≤ gb := p15GammaReal_nonneg hbr0 hu hbv
    have hgr0 : 0 ≤ gr := p15GammaReal_nonneg hrr0 hu hrv
    have hgs0 : 0 ≤ gs := p15GammaReal_nonneg hs0 hu hsv
    have hscale : gr * z ≤ gs := by
      dsimp [gr, gs, s]
      exact p15_gammaReal_mul_scale_le hrr0 hz1 hu hsv
    have hq0 : 0 ≤ gr * z := mul_nonneg hgr0 hz0
    have hsq : (1 + gr * z) ^ 2 ≤ (1 + gs) ^ 2 := by
      nlinarith
    have hreplace :
        (1 + gb) * (1 + gr * z) ^ 2 ≤
          (1 + gb) * (1 + gs) ^ 2 :=
      mul_le_mul_of_nonneg_left hsq (by linarith)
    have hcombine1 :
        (1 + gb) * (1 + gs) ≤
          1 + p15GammaReal (br + s) u := by
      dsimp [gb, gs]
      exact p15_one_add_gammaReal_mul_le hbr0 hs0 hu hbsv
    have hcombine1' :
        (1 + gb) * (1 + gs) * (1 + gs) ≤
          (1 + p15GammaReal (br + s) u) * (1 + gs) :=
      mul_le_mul_of_nonneg_right hcombine1 (by linarith)
    have hcombine2 :
        (1 + p15GammaReal (br + s) u) * (1 + gs) ≤
          1 + p15GammaReal (br + s + s) u := by
      dsimp [gs]
      exact p15_one_add_gammaReal_mul_le
        (add_nonneg hbr0 hs0) hs0 hu hvalid
    have htotal :
        (1 + gb) * (1 + gs) ^ 2 ≤
          1 + p15GammaReal (br + s + s) u := by
      calc
        (1 + gb) * (1 + gs) ^ 2 =
            (1 + gb) * (1 + gs) * (1 + gs) := by ring
        _ ≤ (1 + p15GammaReal (br + s) u) * (1 + gs) := hcombine1'
        _ ≤ 1 + p15GammaReal (br + s + s) u := hcombine2
    apply sub_le_iff_le_add.mpr
    simpa [add_comm] using hreplace.trans htotal

lemma p15LowRankMatMulTrace_forward_error {b r : ℕ} {u : ℝ}
    {XA YA XB YB : P15RectMatrix b r}
    (hXA : p15OrthonormalColumns XA)
    (hXB : p15OrthonormalColumns XB)
    (hu : 0 ≤ u)
    (hvalid : p15LowRankMatMulCost b r * u < 1)
    (trace : P15LowRankMatMulTrace u XA YA XB YB) :
    p15FrobNorm
        (trace.result -
          p15MatMul (p15LowRankMatrix XA YA) (p15LowRankMatrix YB XB)) ≤
      p15GammaReal (p15LowRankMatMulCost b r) u *
        p15FrobNorm (p15LowRankMatrix XA YA) *
        p15FrobNorm (p15LowRankMatrix YB XB) := by
  have hExact :
      p15MatMul (p15LowRankMatrix XA YA) (p15LowRankMatrix YB XB) =
        p15RectMatMul
          (p15RectMatMul XA
            (p15RectMatMul (p15RectTranspose YA) YB))
          (p15RectTranspose XB) := by
    unfold p15LowRankMatrix p15MatMul
    calc
      p15RectMatMul (p15RectMatMul XA (p15RectTranspose YA))
          (p15RectMatMul YB (p15RectTranspose XB)) =
          p15RectMatMul XA
            (p15RectMatMul (p15RectTranspose YA)
              (p15RectMatMul YB (p15RectTranspose XB))) :=
        p15RectMatMul_assoc _ _ _
      _ = p15RectMatMul XA
            (p15RectMatMul
              (p15RectMatMul (p15RectTranspose YA) YB)
              (p15RectTranspose XB)) := by
        exact congrArg (p15RectMatMul XA)
          (p15RectMatMul_assoc (p15RectTranspose YA) YB
            (p15RectTranspose XB)).symm
      _ = p15RectMatMul
            (p15RectMatMul XA
              (p15RectMatMul (p15RectTranspose YA) YB))
            (p15RectTranspose XB) := by
        exact (p15RectMatMul_assoc XA
          (p15RectMatMul (p15RectTranspose YA) YB)
          (p15RectTranspose XB)).symm
  have hExactRight :
      p15MatMul (p15LowRankMatrix XA YA) (p15LowRankMatrix YB XB) =
        p15RectMatMul XA
          (p15RectMatMul
            (p15RectMatMul (p15RectTranspose YA) YB)
            (p15RectTranspose XB)) := by
    rw [hExact, p15RectMatMul_assoc]
  have hcostb : (b : ℝ) ≤ p15LowRankMatMulCost b r := by
    unfold p15LowRankMatMulCost
    have hrr : 0 ≤ (r : ℝ) := Nat.cast_nonneg r
    have hz : 0 ≤ Real.sqrt (r : ℝ) := Real.sqrt_nonneg _
    nlinarith [mul_nonneg hrr hz]
  have hcostr : (r : ℝ) ≤ p15LowRankMatMulCost b r := by
    by_cases hrzero : r = 0
    · subst r
      simp [p15LowRankMatMulCost]
    · have hrnat : 1 ≤ r := (Nat.one_le_iff_ne_zero).mpr hrzero
      have hz1 : 1 ≤ Real.sqrt (r : ℝ) :=
        Real.one_le_sqrt.mpr (by exact_mod_cast hrnat)
      have hrr : 0 ≤ (r : ℝ) := Nat.cast_nonneg r
      have hbb : 0 ≤ (b : ℝ) := Nat.cast_nonneg b
      have haux : 0 ≤ (r : ℝ) * (Real.sqrt (r : ℝ) - 1) :=
        mul_nonneg hrr (sub_nonneg.mpr hz1)
      unfold p15LowRankMatMulCost
      nlinarith
  have hbvalid : (b : ℝ) * u < 1 :=
    lt_of_le_of_lt (mul_le_mul_of_nonneg_right hcostb hu) hvalid
  have hrvalid : (r : ℝ) * u < 1 :=
    lt_of_le_of_lt (mul_le_mul_of_nonneg_right hcostr hu) hvalid
  have hgb0 : 0 ≤ p15GammaReal (b : ℝ) u :=
    p15GammaReal_nonneg (Nat.cast_nonneg b) hu hbvalid
  have hgr0 : 0 ≤ p15GammaReal (r : ℝ) u :=
    p15GammaReal_nonneg (Nat.cast_nonneg r) hu hrvalid
  have hz0 : 0 ≤ Real.sqrt (r : ℝ) := Real.sqrt_nonneg _
  have hq0 : 0 ≤ p15GammaReal (r : ℝ) u * Real.sqrt (r : ℝ) :=
    mul_nonneg hgr0 hz0
  have hcoeff := p15_lowRank_three_stage_coefficient_le (b := b) (r := r) hu hvalid
  have hAnorm :
      p15FrobNorm (p15LowRankMatrix XA YA) = p15RectFrobNorm YA := by
    change p15RectFrobNorm (p15RectMatMul XA (p15RectTranspose YA)) = _
    rw [p15RectFrobNorm_left_orthonormal _ _ hXA,
      p15RectFrobNorm_transpose]
  have hBnorm :
      p15FrobNorm (p15LowRankMatrix YB XB) = p15RectFrobNorm YB := by
    change p15RectFrobNorm (p15RectMatMul YB (p15RectTranspose XB)) = _
    exact p15RectFrobNorm_right_transpose_orthonormal YB XB hXB
  have hXAnorm : p15RectFrobNorm XA = Real.sqrt (r : ℝ) :=
    p15RectFrobNorm_orthonormal XA hXA
  have hXBnorm : p15RectFrobNorm (p15RectTranspose XB) = Real.sqrt (r : ℝ) := by
    rw [p15RectFrobNorm_transpose, p15RectFrobNorm_orthonormal XB hXB]
  have hYAtransnorm : p15RectFrobNorm (p15RectTranspose YA) = p15RectFrobNorm YA :=
    p15RectFrobNorm_transpose YA
  cases trace with
  | leftAssociated middleStage leftStage finalStage =>
      have hrepr :
          finalStage.result -
              p15MatMul (p15LowRankMatrix XA YA) (p15LowRankMatrix YB XB) =
            (p15RectMatMul (p15RectMatMul XA middleStage.error)
                (p15RectTranspose XB) +
              p15RectMatMul leftStage.error (p15RectTranspose XB)) +
                finalStage.error := by
        rw [hExact]
        ext i j
        simp [P15RoundedMatMulStage.result, p15MatMul, p15LowRankMatrix,
          p15RectMatMul, p15RectTranspose, add_mul, mul_add,
          Finset.sum_add_distrib]
        ring
      change p15RectFrobNorm
          (finalStage.result -
            p15MatMul (p15LowRankMatrix XA YA) (p15LowRankMatrix YB XB)) ≤ _
      rw [hrepr]
      let gm := p15GammaReal (b : ℝ) u
      let gr := p15GammaReal (r : ℝ) u
      let z := Real.sqrt (r : ℝ)
      let q := gr * z
      let a := p15RectFrobNorm YA
      let d := p15RectFrobNorm YB
      have ha0 : 0 ≤ a := p15RectFrobNorm_nonneg YA
      have hd0 : 0 ≤ d := p15RectFrobNorm_nonneg YB
      have hab0 : 0 ≤ a * d := mul_nonneg ha0 hd0
      have hgm0' : 0 ≤ gm := hgb0
      have hq0' : 0 ≤ q := hq0
      have hmiddleExact :
          p15RectFrobNorm
              (p15RectMatMul (p15RectTranspose YA) YB) ≤ a * d := by
        calc
          p15RectFrobNorm (p15RectMatMul (p15RectTranspose YA) YB) ≤
              p15RectFrobNorm (p15RectTranspose YA) * p15RectFrobNorm YB :=
            p15RectFrobNorm_rectMatMul_le _ _
          _ = a * d := by rw [hYAtransnorm]
      have hmiddleError :
          p15RectFrobNorm middleStage.error ≤ gm * a * d := by
        simpa [gm, a, d, hYAtransnorm] using middleStage.error_le
      have hmiddleResult :
          p15RectFrobNorm middleStage.result ≤ (1 + gm) * a * d := by
        calc
          p15RectFrobNorm middleStage.result =
              p15RectFrobNorm
                (p15RectMatMul (p15RectTranspose YA) YB + middleStage.error) := rfl
          _ ≤ p15RectFrobNorm
                (p15RectMatMul (p15RectTranspose YA) YB) +
                p15RectFrobNorm middleStage.error :=
              p15RectFrobNorm_add_le _ _
          _ ≤ a * d + gm * a * d := add_le_add hmiddleExact hmiddleError
          _ = (1 + gm) * a * d := by ring
      have hleftError :
          p15RectFrobNorm leftStage.error ≤ q * (1 + gm) * a * d := by
        calc
          p15RectFrobNorm leftStage.error ≤
              gr * p15RectFrobNorm XA * p15RectFrobNorm middleStage.result := by
            simpa [gr] using leftStage.error_le
          _ = q * p15RectFrobNorm middleStage.result := by
            rw [hXAnorm]
          _ ≤ q * ((1 + gm) * a * d) :=
            mul_le_mul_of_nonneg_left hmiddleResult hq0'
          _ = q * (1 + gm) * a * d := by ring
      have hleftResult :
          p15RectFrobNorm leftStage.result ≤
            (1 + q) * (1 + gm) * a * d := by
        calc
          p15RectFrobNorm leftStage.result =
              p15RectFrobNorm
                (p15RectMatMul XA middleStage.result + leftStage.error) := rfl
          _ ≤ p15RectFrobNorm (p15RectMatMul XA middleStage.result) +
                p15RectFrobNorm leftStage.error := p15RectFrobNorm_add_le _ _
          _ = p15RectFrobNorm middleStage.result +
                p15RectFrobNorm leftStage.error := by
              rw [p15RectFrobNorm_left_orthonormal _ _ hXA]
          _ ≤ (1 + gm) * a * d + q * (1 + gm) * a * d :=
            add_le_add hmiddleResult hleftError
          _ = (1 + q) * (1 + gm) * a * d := by ring
      have hfinalError :
          p15RectFrobNorm finalStage.error ≤
            q * (1 + q) * (1 + gm) * a * d := by
        calc
          p15RectFrobNorm finalStage.error ≤
              gr * p15RectFrobNorm leftStage.result *
                p15RectFrobNorm (p15RectTranspose XB) := by
            simpa [gr] using finalStage.error_le
          _ = q * p15RectFrobNorm leftStage.result := by
            rw [hXBnorm]
            simp [q, z]
            ring
          _ ≤ q * ((1 + q) * (1 + gm) * a * d) :=
            mul_le_mul_of_nonneg_left hleftResult hq0'
          _ = q * (1 + q) * (1 + gm) * a * d := by ring
      have hfirstNorm :
          p15RectFrobNorm
              (p15RectMatMul (p15RectMatMul XA middleStage.error)
                (p15RectTranspose XB)) =
            p15RectFrobNorm middleStage.error := by
        rw [p15RectFrobNorm_right_transpose_orthonormal _ _ hXB,
          p15RectFrobNorm_left_orthonormal _ _ hXA]
      have hsecondNorm :
          p15RectFrobNorm
              (p15RectMatMul leftStage.error (p15RectTranspose XB)) =
            p15RectFrobNorm leftStage.error :=
        p15RectFrobNorm_right_transpose_orthonormal _ _ hXB
      calc
        p15RectFrobNorm
            ((p15RectMatMul (p15RectMatMul XA middleStage.error)
                (p15RectTranspose XB) +
              p15RectMatMul leftStage.error (p15RectTranspose XB)) +
                finalStage.error) ≤
            p15RectFrobNorm
                (p15RectMatMul (p15RectMatMul XA middleStage.error)
                    (p15RectTranspose XB) +
                  p15RectMatMul leftStage.error (p15RectTranspose XB)) +
              p15RectFrobNorm finalStage.error := p15RectFrobNorm_add_le _ _
        _ ≤
            (p15RectFrobNorm
                (p15RectMatMul (p15RectMatMul XA middleStage.error)
                  (p15RectTranspose XB)) +
              p15RectFrobNorm
                (p15RectMatMul leftStage.error (p15RectTranspose XB))) +
              p15RectFrobNorm finalStage.error := by
            gcongr
            exact p15RectFrobNorm_add_le _ _
        _ = p15RectFrobNorm middleStage.error +
              p15RectFrobNorm leftStage.error + p15RectFrobNorm finalStage.error := by
            rw [hfirstNorm, hsecondNorm]
        _ ≤ gm * a * d + q * (1 + gm) * a * d +
              q * (1 + q) * (1 + gm) * a * d :=
            add_le_add (add_le_add hmiddleError hleftError) hfinalError
        _ = ((1 + gm) * (1 + q) ^ 2 - 1) * (a * d) := by ring
        _ ≤ p15GammaReal (p15LowRankMatMulCost b r) u * (a * d) :=
            mul_le_mul_of_nonneg_right (by simpa [gm, gr, z, q] using hcoeff) hab0
        _ = p15GammaReal (p15LowRankMatMulCost b r) u *
              p15FrobNorm (p15LowRankMatrix XA YA) *
              p15FrobNorm (p15LowRankMatrix YB XB) := by
            rw [hAnorm, hBnorm]
            simp only [a, d]
            ring
  | rightAssociated middleStage rightStage finalStage =>
      have hrepr :
          finalStage.result -
              p15MatMul (p15LowRankMatrix XA YA) (p15LowRankMatrix YB XB) =
            (p15RectMatMul XA
                (p15RectMatMul middleStage.error (p15RectTranspose XB)) +
              p15RectMatMul XA rightStage.error) + finalStage.error := by
        rw [hExactRight]
        ext i j
        simp [P15RoundedMatMulStage.result, p15RectMatMul,
          p15RectTranspose, add_mul, mul_add, Finset.sum_add_distrib]
        ring
      change p15RectFrobNorm
          (finalStage.result -
            p15MatMul (p15LowRankMatrix XA YA) (p15LowRankMatrix YB XB)) ≤ _
      rw [hrepr]
      let gm := p15GammaReal (b : ℝ) u
      let gr := p15GammaReal (r : ℝ) u
      let z := Real.sqrt (r : ℝ)
      let q := gr * z
      let a := p15RectFrobNorm YA
      let d := p15RectFrobNorm YB
      have ha0 : 0 ≤ a := p15RectFrobNorm_nonneg YA
      have hd0 : 0 ≤ d := p15RectFrobNorm_nonneg YB
      have hab0 : 0 ≤ a * d := mul_nonneg ha0 hd0
      have hgm0' : 0 ≤ gm := hgb0
      have hq0' : 0 ≤ q := hq0
      have hmiddleExact :
          p15RectFrobNorm
              (p15RectMatMul (p15RectTranspose YA) YB) ≤ a * d := by
        calc
          p15RectFrobNorm (p15RectMatMul (p15RectTranspose YA) YB) ≤
              p15RectFrobNorm (p15RectTranspose YA) * p15RectFrobNorm YB :=
            p15RectFrobNorm_rectMatMul_le _ _
          _ = a * d := by rw [hYAtransnorm]
      have hmiddleError :
          p15RectFrobNorm middleStage.error ≤ gm * a * d := by
        simpa [gm, a, d, hYAtransnorm] using middleStage.error_le
      have hmiddleResult :
          p15RectFrobNorm middleStage.result ≤ (1 + gm) * a * d := by
        calc
          p15RectFrobNorm middleStage.result =
              p15RectFrobNorm
                (p15RectMatMul (p15RectTranspose YA) YB + middleStage.error) := rfl
          _ ≤ p15RectFrobNorm
                (p15RectMatMul (p15RectTranspose YA) YB) +
                p15RectFrobNorm middleStage.error :=
              p15RectFrobNorm_add_le _ _
          _ ≤ a * d + gm * a * d := add_le_add hmiddleExact hmiddleError
          _ = (1 + gm) * a * d := by ring
      have hrightError :
          p15RectFrobNorm rightStage.error ≤ q * (1 + gm) * a * d := by
        calc
          p15RectFrobNorm rightStage.error ≤
              gr * p15RectFrobNorm middleStage.result *
                p15RectFrobNorm (p15RectTranspose XB) := by
            simpa [gr] using rightStage.error_le
          _ = q * p15RectFrobNorm middleStage.result := by
            rw [hXBnorm]
            simp [q, z]
            ring
          _ ≤ q * ((1 + gm) * a * d) :=
            mul_le_mul_of_nonneg_left hmiddleResult hq0'
          _ = q * (1 + gm) * a * d := by ring
      have hrightResult :
          p15RectFrobNorm rightStage.result ≤
            (1 + q) * (1 + gm) * a * d := by
        calc
          p15RectFrobNorm rightStage.result =
              p15RectFrobNorm
                (p15RectMatMul middleStage.result (p15RectTranspose XB) +
                  rightStage.error) := rfl
          _ ≤ p15RectFrobNorm
                (p15RectMatMul middleStage.result (p15RectTranspose XB)) +
                p15RectFrobNorm rightStage.error := p15RectFrobNorm_add_le _ _
          _ = p15RectFrobNorm middleStage.result +
                p15RectFrobNorm rightStage.error := by
              rw [p15RectFrobNorm_right_transpose_orthonormal _ _ hXB]
          _ ≤ (1 + gm) * a * d + q * (1 + gm) * a * d :=
            add_le_add hmiddleResult hrightError
          _ = (1 + q) * (1 + gm) * a * d := by ring
      have hfinalError :
          p15RectFrobNorm finalStage.error ≤
            q * (1 + q) * (1 + gm) * a * d := by
        calc
          p15RectFrobNorm finalStage.error ≤
              gr * p15RectFrobNorm XA * p15RectFrobNorm rightStage.result := by
            simpa [gr] using finalStage.error_le
          _ = q * p15RectFrobNorm rightStage.result := by
            rw [hXAnorm]
          _ ≤ q * ((1 + q) * (1 + gm) * a * d) :=
            mul_le_mul_of_nonneg_left hrightResult hq0'
          _ = q * (1 + q) * (1 + gm) * a * d := by ring
      have hfirstNorm :
          p15RectFrobNorm
              (p15RectMatMul XA
                (p15RectMatMul middleStage.error (p15RectTranspose XB))) =
            p15RectFrobNorm middleStage.error := by
        rw [p15RectFrobNorm_left_orthonormal _ _ hXA,
          p15RectFrobNorm_right_transpose_orthonormal _ _ hXB]
      have hsecondNorm :
          p15RectFrobNorm (p15RectMatMul XA rightStage.error) =
            p15RectFrobNorm rightStage.error :=
        p15RectFrobNorm_left_orthonormal _ _ hXA
      calc
        p15RectFrobNorm
            ((p15RectMatMul XA
                (p15RectMatMul middleStage.error (p15RectTranspose XB)) +
              p15RectMatMul XA rightStage.error) + finalStage.error) ≤
            p15RectFrobNorm
                (p15RectMatMul XA
                    (p15RectMatMul middleStage.error (p15RectTranspose XB)) +
                  p15RectMatMul XA rightStage.error) +
              p15RectFrobNorm finalStage.error := p15RectFrobNorm_add_le _ _
        _ ≤
            (p15RectFrobNorm
                (p15RectMatMul XA
                  (p15RectMatMul middleStage.error (p15RectTranspose XB))) +
              p15RectFrobNorm (p15RectMatMul XA rightStage.error)) +
              p15RectFrobNorm finalStage.error := by
            gcongr
            exact p15RectFrobNorm_add_le _ _
        _ = p15RectFrobNorm middleStage.error +
              p15RectFrobNorm rightStage.error + p15RectFrobNorm finalStage.error := by
            rw [hfirstNorm, hsecondNorm]
        _ ≤ gm * a * d + q * (1 + gm) * a * d +
              q * (1 + q) * (1 + gm) * a * d :=
            add_le_add (add_le_add hmiddleError hrightError) hfinalError
        _ = ((1 + gm) * (1 + q) ^ 2 - 1) * (a * d) := by ring
        _ ≤ p15GammaReal (p15LowRankMatMulCost b r) u * (a * d) :=
            mul_le_mul_of_nonneg_right (by simpa [gm, gr, z, q] using hcoeff) hab0
        _ = p15GammaReal (p15LowRankMatMulCost b r) u *
              p15FrobNorm (p15LowRankMatrix XA YA) *
              p15FrobNorm (p15LowRankMatrix YB XB) := by
            rw [hAnorm, hBnorm]
            simp only [a, d]
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
  let Atilde := p15LowRankMatrix run.XA run.YA
  let Btilde := p15LowRankMatrix run.YB run.XB
  let gammaC := p15GammaReal (p15LowRankMatMulCost b r) run.unitRoundoff
  let eA := run.epsilon * run.betaA
  let eB := run.epsilon * run.betaB
  have hforward :
      p15FrobNorm (run.trace.result - p15MatMul Atilde Btilde) ≤
        gammaC * p15FrobNorm Atilde * p15FrobNorm Btilde := by
    dsimp [Atilde, Btilde, gammaC]
    exact p15LowRankMatMulTrace_forward_error
      run.xA_orthonormal run.xB_orthonormal run.unitRoundoff_nonneg
      run.gamma_valid run.trace
  constructor
  · exact hforward
  · have hA0 : 0 ≤ p15FrobNorm run.A := p15RectFrobNorm_nonneg run.A
    have hB0 : 0 ≤ p15FrobNorm run.B := p15RectFrobNorm_nonneg run.B
    have hEA_norm0 : 0 ≤ p15FrobNorm run.approximationErrorA :=
      p15RectFrobNorm_nonneg run.approximationErrorA
    have hEB_norm0 : 0 ≤ p15FrobNorm run.approximationErrorB :=
      p15RectFrobNorm_nonneg run.approximationErrorB
    have heA0 : 0 ≤ eA :=
      le_trans hEA_norm0 (by simpa [eA] using run.approximationErrorA_le)
    have heB0 : 0 ≤ eB :=
      le_trans hEB_norm0 (by simpa [eB] using run.approximationErrorB_le)
    have hcost0 : 0 ≤ p15LowRankMatMulCost b r := by
      unfold p15LowRankMatMulCost
      have hrr : 0 ≤ (r : ℝ) := Nat.cast_nonneg r
      have hbb : 0 ≤ (b : ℝ) := Nat.cast_nonneg b
      have hz : 0 ≤ Real.sqrt (r : ℝ) := Real.sqrt_nonneg _
      nlinarith [mul_nonneg hrr hz]
    have hgamma0 : 0 ≤ gammaC := by
      dsimp [gammaC]
      exact p15GammaReal_nonneg hcost0 run.unitRoundoff_nonneg run.gamma_valid
    have hAtNorm : p15FrobNorm Atilde ≤ p15FrobNorm run.A + eA := by
      calc
        p15FrobNorm Atilde =
            p15FrobNorm (run.A + run.approximationErrorA) := by
          dsimp [Atilde]
          rw [run.approximationA_eq]
        _ ≤ p15FrobNorm run.A + p15FrobNorm run.approximationErrorA :=
          p15RectFrobNorm_add_le _ _
        _ ≤ p15FrobNorm run.A + eA := by
          gcongr
          simpa [eA] using run.approximationErrorA_le
    have hBtNorm : p15FrobNorm Btilde ≤ p15FrobNorm run.B + eB := by
      calc
        p15FrobNorm Btilde =
            p15FrobNorm (run.B + run.approximationErrorB) := by
          dsimp [Btilde]
          rw [run.approximationB_eq]
        _ ≤ p15FrobNorm run.B + p15FrobNorm run.approximationErrorB :=
          p15RectFrobNorm_add_le _ _
        _ ≤ p15FrobNorm run.B + eB := by
          gcongr
          simpa [eB] using run.approximationErrorB_le
    have hABprod :
        p15FrobNorm Atilde * p15FrobNorm Btilde ≤
          (p15FrobNorm run.A + eA) * (p15FrobNorm run.B + eB) := by
      exact mul_le_mul hAtNorm hBtNorm
        (p15RectFrobNorm_nonneg Btilde) (add_nonneg hA0 heA0)
    have hforward' :
        p15FrobNorm (run.trace.result - p15MatMul Atilde Btilde) ≤
          gammaC * ((p15FrobNorm run.A + eA) *
            (p15FrobNorm run.B + eB)) := by
      calc
        p15FrobNorm (run.trace.result - p15MatMul Atilde Btilde) ≤
            gammaC * p15FrobNorm Atilde * p15FrobNorm Btilde := hforward
        _ = gammaC * (p15FrobNorm Atilde * p15FrobNorm Btilde) := by ring
        _ ≤ gammaC * ((p15FrobNorm run.A + eA) *
              (p15FrobNorm run.B + eB)) :=
          mul_le_mul_of_nonneg_left hABprod hgamma0
    have hpertRepr :
        p15MatMul Atilde Btilde - p15MatMul run.A run.B =
          (p15MatMul run.approximationErrorA run.B +
            p15MatMul run.A run.approximationErrorB) +
              p15MatMul run.approximationErrorA run.approximationErrorB := by
      dsimp [Atilde, Btilde]
      rw [run.approximationA_eq, run.approximationB_eq]
      ext i j
      simp [p15MatMul, add_mul, mul_add, Finset.sum_add_distrib]
      ring
    have hEA_mul_B :
        p15FrobNorm (p15MatMul run.approximationErrorA run.B) ≤
          eA * p15FrobNorm run.B := by
      calc
        p15FrobNorm (p15MatMul run.approximationErrorA run.B) ≤
            p15FrobNorm run.approximationErrorA * p15FrobNorm run.B :=
          p15RectFrobNorm_rectMatMul_le _ _
        _ ≤ eA * p15FrobNorm run.B :=
          mul_le_mul_of_nonneg_right
            (by simpa [eA] using run.approximationErrorA_le) hB0
    have hA_mul_EB :
        p15FrobNorm (p15MatMul run.A run.approximationErrorB) ≤
          p15FrobNorm run.A * eB := by
      calc
        p15FrobNorm (p15MatMul run.A run.approximationErrorB) ≤
            p15FrobNorm run.A * p15FrobNorm run.approximationErrorB :=
          p15RectFrobNorm_rectMatMul_le _ _
        _ ≤ p15FrobNorm run.A * eB :=
          mul_le_mul_of_nonneg_left
            (by simpa [eB] using run.approximationErrorB_le) hA0
    have hEA_mul_EB :
        p15FrobNorm
            (p15MatMul run.approximationErrorA run.approximationErrorB) ≤
          eA * eB := by
      calc
        p15FrobNorm
            (p15MatMul run.approximationErrorA run.approximationErrorB) ≤
            p15FrobNorm run.approximationErrorA *
              p15FrobNorm run.approximationErrorB :=
          p15RectFrobNorm_rectMatMul_le _ _
        _ ≤ eA * eB := by
          exact mul_le_mul
            (by simpa [eA] using run.approximationErrorA_le)
            (by simpa [eB] using run.approximationErrorB_le)
            hEB_norm0 heA0
    have hpert :
        p15FrobNorm (p15MatMul Atilde Btilde - p15MatMul run.A run.B) ≤
          eA * p15FrobNorm run.B + p15FrobNorm run.A * eB + eA * eB := by
      rw [hpertRepr]
      calc
        p15FrobNorm
            ((p15MatMul run.approximationErrorA run.B +
              p15MatMul run.A run.approximationErrorB) +
                p15MatMul run.approximationErrorA run.approximationErrorB) ≤
            p15FrobNorm
                (p15MatMul run.approximationErrorA run.B +
                  p15MatMul run.A run.approximationErrorB) +
              p15FrobNorm
                (p15MatMul run.approximationErrorA run.approximationErrorB) :=
          p15RectFrobNorm_add_le _ _
        _ ≤
            (p15FrobNorm (p15MatMul run.approximationErrorA run.B) +
              p15FrobNorm (p15MatMul run.A run.approximationErrorB)) +
              p15FrobNorm
                (p15MatMul run.approximationErrorA run.approximationErrorB) := by
          gcongr
          exact p15RectFrobNorm_add_le _ _
        _ ≤ eA * p15FrobNorm run.B + p15FrobNorm run.A * eB + eA * eB :=
          add_le_add (add_le_add hEA_mul_B hA_mul_EB) hEA_mul_EB
    have hsplit :
        run.trace.result - p15MatMul run.A run.B =
          (run.trace.result - p15MatMul Atilde Btilde) +
            (p15MatMul Atilde Btilde - p15MatMul run.A run.B) := by
      ext i j
      simp
    rw [hsplit]
    calc
      p15FrobNorm
          ((run.trace.result - p15MatMul Atilde Btilde) +
            (p15MatMul Atilde Btilde - p15MatMul run.A run.B)) ≤
          p15FrobNorm (run.trace.result - p15MatMul Atilde Btilde) +
            p15FrobNorm (p15MatMul Atilde Btilde - p15MatMul run.A run.B) :=
        p15RectFrobNorm_add_le _ _
      _ ≤ gammaC * ((p15FrobNorm run.A + eA) *
              (p15FrobNorm run.B + eB)) +
            (eA * p15FrobNorm run.B + p15FrobNorm run.A * eB + eA * eB) :=
        add_le_add hforward' hpert
      _ = gammaC * p15FrobNorm run.A * p15FrobNorm run.B +
          run.epsilon * (1 + gammaC) *
            (run.betaA * p15FrobNorm run.B +
              p15FrobNorm run.A * run.betaB +
              run.epsilon * run.betaA * run.betaB) := by
        dsimp [eA, eB, gammaC]
        ring

end HighamBench
