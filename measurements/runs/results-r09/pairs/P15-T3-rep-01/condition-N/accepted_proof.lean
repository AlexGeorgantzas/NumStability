import HighamBench.P15Definitions

namespace HighamBench

open scoped Matrix.Norms.Frobenius

lemma p15RectMatMul_eq_mul {m n p : ℕ}
    (A : P15RectMatrix m n) (B : P15RectMatrix n p) :
    p15RectMatMul A B = A * B := rfl

lemma p15MatMul_eq_mul {n : ℕ} (A B : P15Matrix n) :
    p15MatMul A B = A * B := rfl

lemma p15RectTranspose_eq_transpose {m n : ℕ} (A : P15RectMatrix m n) :
    p15RectTranspose A = A.transpose := rfl

lemma p15RectFrobNorm_eq_norm {m n : ℕ} (A : P15RectMatrix m n) :
    p15RectFrobNorm A = ‖A‖ := by
  rw [p15RectFrobNorm, Matrix.frobenius_norm_def, Real.sqrt_eq_rpow]
  congr 1
  apply Finset.sum_congr rfl
  intro i _
  apply Finset.sum_congr rfl
  intro j _
  simp [sq_abs]

lemma p15_orthonormal_left_sum_sq {b r p : ℕ}
    (X : P15RectMatrix b r) (hX : p15OrthonormalColumns X)
    (M : P15RectMatrix r p) :
    (∑ i : Fin b, ∑ k : Fin p, (∑ j : Fin r, X i j * M j k) ^ 2) =
      ∑ j : Fin r, ∑ k : Fin p, M j k ^ 2 := by
  rw [Finset.sum_comm]
  conv_rhs => rw [Finset.sum_comm]
  apply Finset.sum_congr rfl
  intro k _
  calc
    (∑ i : Fin b, (∑ j : Fin r, X i j * M j k) ^ 2) =
        ∑ i : Fin b, ∑ j : Fin r, ∑ l : Fin r,
          (X i j * M j k) * (X i l * M l k) := by
            simp_rw [pow_two, Finset.sum_mul, Finset.mul_sum]
    _ = ∑ j : Fin r, ∑ l : Fin r, ∑ i : Fin b,
          (X i j * X i l) * (M j k * M l k) := by
            rw [Finset.sum_comm]
            apply Finset.sum_congr rfl
            intro j _
            rw [Finset.sum_comm]
            apply Finset.sum_congr rfl
            intro l _
            apply Finset.sum_congr rfl
            intro i _
            ring
    _ = ∑ j : Fin r, ∑ l : Fin r,
          (∑ i : Fin b, X i j * X i l) * (M j k * M l k) := by
            simp_rw [Finset.sum_mul]
    _ = ∑ j : Fin r, M j k ^ 2 := by
            change ∀ j l, (∑ i : Fin b, X i j * X i l) =
              (if j = l then 1 else 0) at hX
            simp_rw [hX]
            simp [pow_two]

lemma p15RectFrobNorm_transpose {m n : ℕ} (A : P15RectMatrix m n) :
    p15RectFrobNorm (p15RectTranspose A) = p15RectFrobNorm A := by
  simp only [p15RectFrobNorm, p15RectTranspose]
  rw [Finset.sum_comm]

lemma p15RectFrobNorm_mul_le {m n p : ℕ}
    (A : P15RectMatrix m n) (B : P15RectMatrix n p) :
    p15RectFrobNorm (p15RectMatMul A B) ≤
      p15RectFrobNorm A * p15RectFrobNorm B := by
  simpa only [p15RectFrobNorm_eq_norm] using Matrix.frobenius_norm_mul A B

lemma p15RectFrobNorm_add_le {m n : ℕ} (A B : P15RectMatrix m n) :
    p15RectFrobNorm (A + B) ≤ p15RectFrobNorm A + p15RectFrobNorm B := by
  simpa only [p15RectFrobNorm_eq_norm] using norm_add_le A B

lemma p15RectFrobNorm_sub_le {m n : ℕ} (A B : P15RectMatrix m n) :
    p15RectFrobNorm (A - B) ≤ p15RectFrobNorm A + p15RectFrobNorm B := by
  simpa only [p15RectFrobNorm_eq_norm] using norm_sub_le A B

lemma p15RectFrobNorm_orthonormal_left {b r p : ℕ}
    (X : P15RectMatrix b r) (hX : p15OrthonormalColumns X)
    (M : P15RectMatrix r p) :
    p15RectFrobNorm (p15RectMatMul X M) = p15RectFrobNorm M := by
  unfold p15RectFrobNorm p15RectMatMul
  rw [p15_orthonormal_left_sum_sq X hX M]

lemma p15RectFrobNorm_orthonormal_right {b r p : ℕ}
    (X : P15RectMatrix b r) (hX : p15OrthonormalColumns X)
    (M : P15RectMatrix p r) :
    p15RectFrobNorm (p15RectMatMul M (p15RectTranspose X)) =
      p15RectFrobNorm M := by
  calc
    p15RectFrobNorm (p15RectMatMul M (p15RectTranspose X)) =
        p15RectFrobNorm
          (p15RectTranspose (p15RectMatMul M (p15RectTranspose X))) := by
            rw [p15RectFrobNorm_transpose]
    _ = p15RectFrobNorm
          (p15RectMatMul X (p15RectTranspose M)) := by
            congr 1
            ext i j
            simp only [p15RectTranspose, p15RectMatMul]
            apply Finset.sum_congr rfl
            intro k _
            ring
    _ = p15RectFrobNorm (p15RectTranspose M) :=
          p15RectFrobNorm_orthonormal_left X hX (p15RectTranspose M)
    _ = p15RectFrobNorm M := p15RectFrobNorm_transpose M

lemma p15RectFrobNorm_orthonormal_columns {b r : ℕ}
    (X : P15RectMatrix b r) (hX : p15OrthonormalColumns X) :
    p15RectFrobNorm X = Real.sqrt (r : ℝ) := by
  unfold p15RectFrobNorm
  congr 1
  rw [Finset.sum_comm]
  calc
    (∑ j : Fin r, ∑ i : Fin b, X i j ^ 2) = ∑ j : Fin r, (1 : ℝ) := by
      apply Finset.sum_congr rfl
      intro j _
      calc
        (∑ i : Fin b, X i j ^ 2) = ∑ i : Fin b, X i j * X i j := by
          apply Finset.sum_congr rfl
          intro i _
          ring
        _ = 1 := by
          simpa [p15OrthonormalColumns] using hX j j
    _ = (r : ℝ) := by simp

lemma p15FrobNorm_lowRank_left {b r : ℕ}
    (X Y : P15RectMatrix b r) (hX : p15OrthonormalColumns X) :
    p15FrobNorm (p15LowRankMatrix X Y) = p15RectFrobNorm Y := by
  change p15RectFrobNorm (p15RectMatMul X (p15RectTranspose Y)) = _
  rw [p15RectFrobNorm_orthonormal_left X hX,
    p15RectFrobNorm_transpose]

lemma p15FrobNorm_lowRank_right {b r : ℕ}
    (X Y : P15RectMatrix b r) (hX : p15OrthonormalColumns X) :
    p15FrobNorm (p15LowRankMatrix Y X) = p15RectFrobNorm Y := by
  exact p15RectFrobNorm_orthonormal_right X hX Y

lemma p15GammaReal_nonneg {k u : ℝ} (hk : 0 ≤ k) (hu : 0 ≤ u)
    (hvalid : k * u < 1) : 0 ≤ p15GammaReal k u := by
  unfold p15GammaReal
  exact div_nonneg (mul_nonneg hk hu) (le_of_lt (sub_pos.mpr hvalid))

lemma p15_gamma_three (a q u : ℝ) (ha : 0 ≤ a) (hq : 0 ≤ q)
    (hu : 0 ≤ u) (hvalid : (a + 2 * q) * u < 1) :
    (1 + p15GammaReal a u) * (1 + p15GammaReal q u) ^ 2 ≤
      1 + p15GammaReal (a + 2 * q) u := by
  have ha_u : a * u < 1 := by nlinarith [mul_nonneg hq hu]
  have hq_u : q * u < 1 := by nlinarith [mul_nonneg ha hu, mul_nonneg hq hu]
  have hda : 0 < 1 - a * u := sub_pos.mpr ha_u
  have hdq : 0 < 1 - q * u := sub_pos.mpr hq_u
  have hdc : 0 < 1 - (a + 2 * q) * u := sub_pos.mpr hvalid
  have hx : 0 ≤ a * u := mul_nonneg ha hu
  have hy : 0 ≤ q * u := mul_nonneg hq hu
  have hden :
      1 - (a + 2 * q) * u ≤ (1 - a * u) * (1 - q * u) ^ 2 := by
    have h₁ : 0 ≤ (q * u) ^ 2 * (1 - a * u) :=
      mul_nonneg (sq_nonneg _) (le_of_lt hda)
    have h₂ : 0 ≤ 2 * (a * u) * (q * u) := by positivity
    nlinarith
  have hrecip :
      1 / ((1 - a * u) * (1 - q * u) ^ 2) ≤
        1 / (1 - (a + 2 * q) * u) :=
    one_div_le_one_div_of_le hdc hden
  have hga : 1 + p15GammaReal a u = 1 / (1 - a * u) := by
    unfold p15GammaReal
    field_simp
    ring
  have hgq : 1 + p15GammaReal q u = 1 / (1 - q * u) := by
    unfold p15GammaReal
    field_simp
    ring
  have hgc : 1 + p15GammaReal (a + 2 * q) u =
      1 / (1 - (a + 2 * q) * u) := by
    unfold p15GammaReal
    field_simp
    ring
  rw [hga, hgq, hgc]
  convert hrecip using 1 <;> field_simp <;> ring

lemma p15_gamma_low_rank_coeff (b r : ℕ) (u : ℝ) (hu : 0 ≤ u)
    (hvalid : p15LowRankMatMulCost b r * u < 1) :
    p15GammaReal (b : ℝ) u +
        (p15GammaReal (r : ℝ) u * Real.sqrt (r : ℝ)) *
          (1 + p15GammaReal (b : ℝ) u) +
        (p15GammaReal (r : ℝ) u * Real.sqrt (r : ℝ)) *
          (1 + p15GammaReal (r : ℝ) u * Real.sqrt (r : ℝ)) *
          (1 + p15GammaReal (b : ℝ) u) ≤
      p15GammaReal (p15LowRankMatMulCost b r) u := by
  let a : ℝ := b
  let s : ℝ := Real.sqrt (r : ℝ)
  let q : ℝ := (r : ℝ) * s
  have ha : 0 ≤ a := by positivity
  have hs : 0 ≤ s := by dsimp [s]; positivity
  have hr : 0 ≤ (r : ℝ) := by positivity
  have hq : 0 ≤ q := mul_nonneg hr hs
  have hcost : p15LowRankMatMulCost b r = a + 2 * q := by
    simp only [p15LowRankMatMulCost, a, q, s]
    ring
  have hvalid' : (a + 2 * q) * u < 1 := by simpa [hcost] using hvalid
  have ha_valid : a * u < 1 := by nlinarith [mul_nonneg hq hu]
  have hq_valid : q * u < 1 := by
    nlinarith [mul_nonneg ha hu, mul_nonneg hq hu]
  have hrq : (r : ℝ) ≤ q := by
    by_cases hzero : r = 0
    · simp [hzero, q]
    · have hr_one_nat : 1 ≤ r := (Nat.one_le_iff_ne_zero).2 hzero
      have hr_one : (1 : ℝ) ≤ (r : ℝ) := by exact_mod_cast hr_one_nat
      have hs_one : 1 ≤ s := by
        dsimp [s]
        exact Real.one_le_sqrt.mpr hr_one
      simpa [q] using mul_le_mul_of_nonneg_left hs_one hr
  have hr_valid : (r : ℝ) * u < 1 := by
    have hru_le : (r : ℝ) * u ≤ q * u :=
      mul_le_mul_of_nonneg_right hrq hu
    exact lt_of_le_of_lt hru_le hq_valid
  have hgb : 0 ≤ p15GammaReal a u :=
    p15GammaReal_nonneg ha hu ha_valid
  have hgq : 0 ≤ p15GammaReal q u :=
    p15GammaReal_nonneg hq hu hq_valid
  have ht :
      p15GammaReal (r : ℝ) u * s ≤ p15GammaReal q u := by
    have hnum : 0 ≤ q * u := mul_nonneg hq hu
    have hdenq : 0 < 1 - q * u := sub_pos.mpr hq_valid
    have hdenord : 1 - q * u ≤ 1 - (r : ℝ) * u := by
      exact sub_le_sub_left (mul_le_mul_of_nonneg_right hrq hu) 1
    have hdiv : q * u / (1 - (r : ℝ) * u) ≤ q * u / (1 - q * u) :=
      div_le_div₀ hnum (le_refl _) hdenq hdenord
    unfold p15GammaReal
    calc
      ((r : ℝ) * u / (1 - (r : ℝ) * u)) * s =
          q * u / (1 - (r : ℝ) * u) := by
            dsimp [q]
            field_simp
      _ ≤ q * u / (1 - q * u) := hdiv
  have ht_nonneg : 0 ≤ p15GammaReal (r : ℝ) u * s := by
    exact mul_nonneg (p15GammaReal_nonneg hr hu hr_valid) hs
  have hsq :
      (1 + p15GammaReal (r : ℝ) u * s) ^ 2 ≤
        (1 + p15GammaReal q u) ^ 2 := by
    rw [sq_le_sq₀ (by linarith) (by linarith)]
    linarith
  have hmono :
      (1 + p15GammaReal a u) *
          (1 + p15GammaReal (r : ℝ) u * s) ^ 2 ≤
        (1 + p15GammaReal a u) * (1 + p15GammaReal q u) ^ 2 :=
    mul_le_mul_of_nonneg_left hsq (by linarith)
  have hthree := p15_gamma_three a q u ha hq hu hvalid'
  rw [hcost]
  dsimp [a, s] at hgb ht_nonneg hmono hthree ⊢
  nlinarith

lemma p15_left_trace_error_eq {b r : ℕ} {u : ℝ}
    {XA YA XB YB : P15RectMatrix b r}
    (middle : P15RoundedMatMulStage r b r u (p15RectTranspose YA) YB)
    (left : P15RoundedMatMulStage b r r u XA middle.result)
    (final : P15RoundedMatMulStage b r b u left.result (p15RectTranspose XB)) :
    final.result -
        p15MatMul (p15LowRankMatrix XA YA) (p15LowRankMatrix YB XB) =
      p15RectMatMul (p15RectMatMul XA middle.error) (p15RectTranspose XB) +
        p15RectMatMul left.error (p15RectTranspose XB) + final.error := by
  simp only [P15RoundedMatMulStage.result, p15LowRankMatrix,
    p15RectMatMul_eq_mul, p15MatMul_eq_mul, p15RectTranspose_eq_transpose,
    Matrix.mul_add, Matrix.add_mul, Matrix.mul_assoc]
  abel

lemma p15_right_trace_error_eq {b r : ℕ} {u : ℝ}
    {XA YA XB YB : P15RectMatrix b r}
    (middle : P15RoundedMatMulStage r b r u (p15RectTranspose YA) YB)
    (right : P15RoundedMatMulStage r r b u middle.result (p15RectTranspose XB))
    (final : P15RoundedMatMulStage b r b u XA right.result) :
    final.result -
        p15MatMul (p15LowRankMatrix XA YA) (p15LowRankMatrix YB XB) =
      p15RectMatMul XA
          (p15RectMatMul middle.error (p15RectTranspose XB)) +
        p15RectMatMul XA right.error + final.error := by
  simp only [P15RoundedMatMulStage.result, p15LowRankMatrix,
    p15RectMatMul_eq_mul, p15MatMul_eq_mul, p15RectTranspose_eq_transpose,
    Matrix.mul_add, Matrix.add_mul, Matrix.mul_assoc]
  abel

lemma p15RectFrobNorm_nonneg {m n : ℕ} (A : P15RectMatrix m n) :
    0 ≤ p15RectFrobNorm A := by
  rw [p15RectFrobNorm_eq_norm]
  exact norm_nonneg A

lemma p15LowRankMatMulCost_nonneg (b r : ℕ) :
    0 ≤ p15LowRankMatMulCost b r := by
  unfold p15LowRankMatMulCost
  have hterm : 0 ≤ 2 * (r : ℝ) * Real.sqrt (r : ℝ) := by positivity
  linarith

lemma p15LowRankMatMulCost_b_le (b r : ℕ) :
    (b : ℝ) ≤ p15LowRankMatMulCost b r := by
  unfold p15LowRankMatMulCost
  have hterm : 0 ≤ 2 * (r : ℝ) * Real.sqrt (r : ℝ) := by positivity
  linarith

lemma p15LowRankMatMulCost_r_le (b r : ℕ) :
    (r : ℝ) ≤ p15LowRankMatMulCost b r := by
  by_cases hzero : r = 0
  · simp [hzero, p15LowRankMatMulCost]
  · have hr_one_nat : 1 ≤ r := (Nat.one_le_iff_ne_zero).2 hzero
    have hr_one : (1 : ℝ) ≤ (r : ℝ) := by exact_mod_cast hr_one_nat
    have hs_one : (1 : ℝ) ≤ Real.sqrt (r : ℝ) :=
      Real.one_le_sqrt.mpr hr_one
    have hr_nonneg : 0 ≤ (r : ℝ) := by positivity
    have hmul : (r : ℝ) ≤ (r : ℝ) * Real.sqrt (r : ℝ) := by
      simpa using mul_le_mul_of_nonneg_left hs_one hr_nonneg
    have hb_nonneg : 0 ≤ (b : ℝ) := by positivity
    unfold p15LowRankMatMulCost
    nlinarith

lemma p15GammaReal_component_nonneg {b r : ℕ} {u k : ℝ}
    (hu : 0 ≤ u) (hvalid : p15LowRankMatMulCost b r * u < 1)
    (hk : 0 ≤ k) (hkc : k ≤ p15LowRankMatMulCost b r) :
    0 ≤ p15GammaReal k u := by
  apply p15GammaReal_nonneg hk hu
  exact lt_of_le_of_lt (mul_le_mul_of_nonneg_right hkc hu) hvalid

lemma p15_trace_error_bound {b r : ℕ} {u : ℝ}
    {XA YA XB YB : P15RectMatrix b r}
    (hu : 0 ≤ u) (hvalid : p15LowRankMatMulCost b r * u < 1)
    (hXA : p15OrthonormalColumns XA) (hXB : p15OrthonormalColumns XB)
    (trace : P15LowRankMatMulTrace u XA YA XB YB) :
    p15FrobNorm
        (trace.result -
          p15MatMul (p15LowRankMatrix XA YA) (p15LowRankMatrix YB XB)) ≤
      p15GammaReal (p15LowRankMatMulCost b r) u *
        p15FrobNorm (p15LowRankMatrix XA YA) *
        p15FrobNorm (p15LowRankMatrix YB XB) := by
  have hgb : 0 ≤ p15GammaReal (b : ℝ) u :=
    p15GammaReal_component_nonneg hu hvalid (by positivity)
      (p15LowRankMatMulCost_b_le b r)
  have hgr : 0 ≤ p15GammaReal (r : ℝ) u :=
    p15GammaReal_component_nonneg hu hvalid (by positivity)
      (p15LowRankMatMulCost_r_le b r)
  have hs : 0 ≤ Real.sqrt (r : ℝ) := Real.sqrt_nonneg _
  have ht : 0 ≤ p15GammaReal (r : ℝ) u * Real.sqrt (r : ℝ) :=
    mul_nonneg hgr hs
  have ha : 0 ≤ p15RectFrobNorm YA := p15RectFrobNorm_nonneg YA
  have hd : 0 ≤ p15RectFrobNorm YB := p15RectFrobNorm_nonneg YB
  have had : 0 ≤ p15RectFrobNorm YA * p15RectFrobNorm YB :=
    mul_nonneg ha hd
  have hcoeff := p15_gamma_low_rank_coeff b r u hu hvalid
  cases trace with
  | leftAssociated middle left final =>
      have he0 :
          p15RectFrobNorm middle.error ≤
            p15GammaReal (b : ℝ) u * p15RectFrobNorm YA *
              p15RectFrobNorm YB := by
        simpa only [p15RectFrobNorm_transpose] using middle.error_le
      have hmiddle_exact :
          p15RectFrobNorm
              (p15RectMatMul (p15RectTranspose YA) YB) ≤
            p15RectFrobNorm YA * p15RectFrobNorm YB := by
        calc
          p15RectFrobNorm (p15RectMatMul (p15RectTranspose YA) YB) ≤
              p15RectFrobNorm (p15RectTranspose YA) *
                p15RectFrobNorm YB :=
            p15RectFrobNorm_mul_le _ _
          _ = p15RectFrobNorm YA * p15RectFrobNorm YB := by
            rw [p15RectFrobNorm_transpose]
      have hmiddle :
          p15RectFrobNorm middle.result ≤
            (1 + p15GammaReal (b : ℝ) u) *
              p15RectFrobNorm YA * p15RectFrobNorm YB := by
        calc
          p15RectFrobNorm middle.result ≤
              p15RectFrobNorm
                  (p15RectMatMul (p15RectTranspose YA) YB) +
                p15RectFrobNorm middle.error := by
            rw [P15RoundedMatMulStage.result]
            exact p15RectFrobNorm_add_le _ _
          _ ≤ p15RectFrobNorm YA * p15RectFrobNorm YB +
                p15GammaReal (b : ℝ) u * p15RectFrobNorm YA *
                  p15RectFrobNorm YB := add_le_add hmiddle_exact he0
          _ = (1 + p15GammaReal (b : ℝ) u) *
                p15RectFrobNorm YA * p15RectFrobNorm YB := by ring
      have he1 :
          p15RectFrobNorm left.error ≤
            (p15GammaReal (r : ℝ) u * Real.sqrt (r : ℝ)) *
              (1 + p15GammaReal (b : ℝ) u) *
              p15RectFrobNorm YA * p15RectFrobNorm YB := by
        calc
          p15RectFrobNorm left.error ≤
              p15GammaReal (r : ℝ) u * p15RectFrobNorm XA *
                p15RectFrobNorm middle.result := left.error_le
          _ = (p15GammaReal (r : ℝ) u * Real.sqrt (r : ℝ)) *
                p15RectFrobNorm middle.result := by
            rw [p15RectFrobNorm_orthonormal_columns XA hXA]
          _ ≤ (p15GammaReal (r : ℝ) u * Real.sqrt (r : ℝ)) *
                ((1 + p15GammaReal (b : ℝ) u) *
                  p15RectFrobNorm YA * p15RectFrobNorm YB) :=
            mul_le_mul_of_nonneg_left hmiddle ht
          _ = (p15GammaReal (r : ℝ) u * Real.sqrt (r : ℝ)) *
                (1 + p15GammaReal (b : ℝ) u) *
                p15RectFrobNorm YA * p15RectFrobNorm YB := by ring
      have hleft :
          p15RectFrobNorm left.result ≤
            (1 + p15GammaReal (r : ℝ) u * Real.sqrt (r : ℝ)) *
              (1 + p15GammaReal (b : ℝ) u) *
              p15RectFrobNorm YA * p15RectFrobNorm YB := by
        calc
          p15RectFrobNorm left.result ≤
              p15RectFrobNorm (p15RectMatMul XA middle.result) +
                p15RectFrobNorm left.error := by
            rw [P15RoundedMatMulStage.result]
            exact p15RectFrobNorm_add_le _ _
          _ = p15RectFrobNorm middle.result +
                p15RectFrobNorm left.error := by
            rw [p15RectFrobNorm_orthonormal_left XA hXA]
          _ ≤ (1 + p15GammaReal (b : ℝ) u) *
                  p15RectFrobNorm YA * p15RectFrobNorm YB +
                (p15GammaReal (r : ℝ) u * Real.sqrt (r : ℝ)) *
                  (1 + p15GammaReal (b : ℝ) u) *
                  p15RectFrobNorm YA * p15RectFrobNorm YB :=
            add_le_add hmiddle he1
          _ = (1 + p15GammaReal (r : ℝ) u * Real.sqrt (r : ℝ)) *
                (1 + p15GammaReal (b : ℝ) u) *
                p15RectFrobNorm YA * p15RectFrobNorm YB := by ring
      have he2 :
          p15RectFrobNorm final.error ≤
            (p15GammaReal (r : ℝ) u * Real.sqrt (r : ℝ)) *
              (1 + p15GammaReal (r : ℝ) u * Real.sqrt (r : ℝ)) *
              (1 + p15GammaReal (b : ℝ) u) *
              p15RectFrobNorm YA * p15RectFrobNorm YB := by
        calc
          p15RectFrobNorm final.error ≤
              p15GammaReal (r : ℝ) u * p15RectFrobNorm left.result *
                p15RectFrobNorm (p15RectTranspose XB) := final.error_le
          _ = (p15GammaReal (r : ℝ) u * Real.sqrt (r : ℝ)) *
                p15RectFrobNorm left.result := by
            rw [p15RectFrobNorm_transpose,
              p15RectFrobNorm_orthonormal_columns XB hXB]
            ring
          _ ≤ (p15GammaReal (r : ℝ) u * Real.sqrt (r : ℝ)) *
                ((1 + p15GammaReal (r : ℝ) u * Real.sqrt (r : ℝ)) *
                  (1 + p15GammaReal (b : ℝ) u) *
                  p15RectFrobNorm YA * p15RectFrobNorm YB) :=
            mul_le_mul_of_nonneg_left hleft ht
          _ = (p15GammaReal (r : ℝ) u * Real.sqrt (r : ℝ)) *
                (1 + p15GammaReal (r : ℝ) u * Real.sqrt (r : ℝ)) *
                (1 + p15GammaReal (b : ℝ) u) *
                p15RectFrobNorm YA * p15RectFrobNorm YB := by ring
      have htotal :
          p15FrobNorm
              (final.result -
                p15MatMul (p15LowRankMatrix XA YA)
                  (p15LowRankMatrix YB XB)) ≤
            p15RectFrobNorm middle.error + p15RectFrobNorm left.error +
              p15RectFrobNorm final.error := by
        rw [p15_left_trace_error_eq middle left final]
        calc
          p15RectFrobNorm
              (p15RectMatMul (p15RectMatMul XA middle.error)
                    (p15RectTranspose XB) +
                p15RectMatMul left.error (p15RectTranspose XB) +
                final.error) ≤
              p15RectFrobNorm
                  (p15RectMatMul (p15RectMatMul XA middle.error)
                      (p15RectTranspose XB) +
                    p15RectMatMul left.error (p15RectTranspose XB)) +
                p15RectFrobNorm final.error := p15RectFrobNorm_add_le _ _
          _ ≤ (p15RectFrobNorm
                    (p15RectMatMul (p15RectMatMul XA middle.error)
                      (p15RectTranspose XB)) +
                  p15RectFrobNorm
                    (p15RectMatMul left.error (p15RectTranspose XB))) +
                p15RectFrobNorm final.error := by
            gcongr
            exact p15RectFrobNorm_add_le _ _
          _ = p15RectFrobNorm middle.error + p15RectFrobNorm left.error +
                p15RectFrobNorm final.error := by
            rw [p15RectFrobNorm_orthonormal_right XB hXB,
              p15RectFrobNorm_orthonormal_left XA hXA,
              p15RectFrobNorm_orthonormal_right XB hXB]
      calc
        p15FrobNorm
            (final.result -
              p15MatMul (p15LowRankMatrix XA YA)
                (p15LowRankMatrix YB XB)) ≤
            p15RectFrobNorm middle.error + p15RectFrobNorm left.error +
              p15RectFrobNorm final.error := htotal
        _ ≤ p15GammaReal (b : ℝ) u * p15RectFrobNorm YA *
                p15RectFrobNorm YB +
              (p15GammaReal (r : ℝ) u * Real.sqrt (r : ℝ)) *
                (1 + p15GammaReal (b : ℝ) u) *
                p15RectFrobNorm YA * p15RectFrobNorm YB +
              (p15GammaReal (r : ℝ) u * Real.sqrt (r : ℝ)) *
                (1 + p15GammaReal (r : ℝ) u * Real.sqrt (r : ℝ)) *
                (1 + p15GammaReal (b : ℝ) u) *
                p15RectFrobNorm YA * p15RectFrobNorm YB :=
          add_le_add (add_le_add he0 he1) he2
        _ = (p15GammaReal (b : ℝ) u +
                (p15GammaReal (r : ℝ) u * Real.sqrt (r : ℝ)) *
                  (1 + p15GammaReal (b : ℝ) u) +
                (p15GammaReal (r : ℝ) u * Real.sqrt (r : ℝ)) *
                  (1 + p15GammaReal (r : ℝ) u * Real.sqrt (r : ℝ)) *
                  (1 + p15GammaReal (b : ℝ) u)) *
              (p15RectFrobNorm YA * p15RectFrobNorm YB) := by ring
        _ ≤ p15GammaReal (p15LowRankMatMulCost b r) u *
              (p15RectFrobNorm YA * p15RectFrobNorm YB) :=
          mul_le_mul_of_nonneg_right hcoeff had
        _ = p15GammaReal (p15LowRankMatMulCost b r) u *
              p15FrobNorm (p15LowRankMatrix XA YA) *
              p15FrobNorm (p15LowRankMatrix YB XB) := by
          rw [p15FrobNorm_lowRank_left XA YA hXA,
            p15FrobNorm_lowRank_right XB YB hXB]
          ring

  | rightAssociated middle right final =>
      have he0 :
          p15RectFrobNorm middle.error ≤
            p15GammaReal (b : ℝ) u * p15RectFrobNorm YA *
              p15RectFrobNorm YB := by
        simpa only [p15RectFrobNorm_transpose] using middle.error_le
      have hmiddle_exact :
          p15RectFrobNorm
              (p15RectMatMul (p15RectTranspose YA) YB) ≤
            p15RectFrobNorm YA * p15RectFrobNorm YB := by
        calc
          p15RectFrobNorm (p15RectMatMul (p15RectTranspose YA) YB) ≤
              p15RectFrobNorm (p15RectTranspose YA) *
                p15RectFrobNorm YB :=
            p15RectFrobNorm_mul_le _ _
          _ = p15RectFrobNorm YA * p15RectFrobNorm YB := by
            rw [p15RectFrobNorm_transpose]
      have hmiddle :
          p15RectFrobNorm middle.result ≤
            (1 + p15GammaReal (b : ℝ) u) *
              p15RectFrobNorm YA * p15RectFrobNorm YB := by
        calc
          p15RectFrobNorm middle.result ≤
              p15RectFrobNorm
                  (p15RectMatMul (p15RectTranspose YA) YB) +
                p15RectFrobNorm middle.error := by
            rw [P15RoundedMatMulStage.result]
            exact p15RectFrobNorm_add_le _ _
          _ ≤ p15RectFrobNorm YA * p15RectFrobNorm YB +
                p15GammaReal (b : ℝ) u * p15RectFrobNorm YA *
                  p15RectFrobNorm YB := add_le_add hmiddle_exact he0
          _ = (1 + p15GammaReal (b : ℝ) u) *
                p15RectFrobNorm YA * p15RectFrobNorm YB := by ring
      have he1 :
          p15RectFrobNorm right.error ≤
            (p15GammaReal (r : ℝ) u * Real.sqrt (r : ℝ)) *
              (1 + p15GammaReal (b : ℝ) u) *
              p15RectFrobNorm YA * p15RectFrobNorm YB := by
        calc
          p15RectFrobNorm right.error ≤
              p15GammaReal (r : ℝ) u * p15RectFrobNorm middle.result *
                p15RectFrobNorm (p15RectTranspose XB) := right.error_le
          _ = (p15GammaReal (r : ℝ) u * Real.sqrt (r : ℝ)) *
                p15RectFrobNorm middle.result := by
            rw [p15RectFrobNorm_transpose,
              p15RectFrobNorm_orthonormal_columns XB hXB]
            ring
          _ ≤ (p15GammaReal (r : ℝ) u * Real.sqrt (r : ℝ)) *
                ((1 + p15GammaReal (b : ℝ) u) *
                  p15RectFrobNorm YA * p15RectFrobNorm YB) :=
            mul_le_mul_of_nonneg_left hmiddle ht
          _ = (p15GammaReal (r : ℝ) u * Real.sqrt (r : ℝ)) *
                (1 + p15GammaReal (b : ℝ) u) *
                p15RectFrobNorm YA * p15RectFrobNorm YB := by ring
      have hright :
          p15RectFrobNorm right.result ≤
            (1 + p15GammaReal (r : ℝ) u * Real.sqrt (r : ℝ)) *
              (1 + p15GammaReal (b : ℝ) u) *
              p15RectFrobNorm YA * p15RectFrobNorm YB := by
        calc
          p15RectFrobNorm right.result ≤
              p15RectFrobNorm
                  (p15RectMatMul middle.result (p15RectTranspose XB)) +
                p15RectFrobNorm right.error := by
            rw [P15RoundedMatMulStage.result]
            exact p15RectFrobNorm_add_le _ _
          _ = p15RectFrobNorm middle.result +
                p15RectFrobNorm right.error := by
            rw [p15RectFrobNorm_orthonormal_right XB hXB]
          _ ≤ (1 + p15GammaReal (b : ℝ) u) *
                  p15RectFrobNorm YA * p15RectFrobNorm YB +
                (p15GammaReal (r : ℝ) u * Real.sqrt (r : ℝ)) *
                  (1 + p15GammaReal (b : ℝ) u) *
                  p15RectFrobNorm YA * p15RectFrobNorm YB :=
            add_le_add hmiddle he1
          _ = (1 + p15GammaReal (r : ℝ) u * Real.sqrt (r : ℝ)) *
                (1 + p15GammaReal (b : ℝ) u) *
                p15RectFrobNorm YA * p15RectFrobNorm YB := by ring
      have he2 :
          p15RectFrobNorm final.error ≤
            (p15GammaReal (r : ℝ) u * Real.sqrt (r : ℝ)) *
              (1 + p15GammaReal (r : ℝ) u * Real.sqrt (r : ℝ)) *
              (1 + p15GammaReal (b : ℝ) u) *
              p15RectFrobNorm YA * p15RectFrobNorm YB := by
        calc
          p15RectFrobNorm final.error ≤
              p15GammaReal (r : ℝ) u * p15RectFrobNorm XA *
                p15RectFrobNorm right.result := final.error_le
          _ = (p15GammaReal (r : ℝ) u * Real.sqrt (r : ℝ)) *
                p15RectFrobNorm right.result := by
            rw [p15RectFrobNorm_orthonormal_columns XA hXA]
          _ ≤ (p15GammaReal (r : ℝ) u * Real.sqrt (r : ℝ)) *
                ((1 + p15GammaReal (r : ℝ) u * Real.sqrt (r : ℝ)) *
                  (1 + p15GammaReal (b : ℝ) u) *
                  p15RectFrobNorm YA * p15RectFrobNorm YB) :=
            mul_le_mul_of_nonneg_left hright ht
          _ = (p15GammaReal (r : ℝ) u * Real.sqrt (r : ℝ)) *
                (1 + p15GammaReal (r : ℝ) u * Real.sqrt (r : ℝ)) *
                (1 + p15GammaReal (b : ℝ) u) *
                p15RectFrobNorm YA * p15RectFrobNorm YB := by ring
      have htotal :
          p15FrobNorm
              (final.result -
                p15MatMul (p15LowRankMatrix XA YA)
                  (p15LowRankMatrix YB XB)) ≤
            p15RectFrobNorm middle.error + p15RectFrobNorm right.error +
              p15RectFrobNorm final.error := by
        rw [p15_right_trace_error_eq middle right final]
        calc
          p15RectFrobNorm
              (p15RectMatMul XA
                    (p15RectMatMul middle.error (p15RectTranspose XB)) +
                p15RectMatMul XA right.error + final.error) ≤
              p15RectFrobNorm
                  (p15RectMatMul XA
                      (p15RectMatMul middle.error (p15RectTranspose XB)) +
                    p15RectMatMul XA right.error) +
                p15RectFrobNorm final.error := p15RectFrobNorm_add_le _ _
          _ ≤ (p15RectFrobNorm
                    (p15RectMatMul XA
                      (p15RectMatMul middle.error (p15RectTranspose XB))) +
                  p15RectFrobNorm (p15RectMatMul XA right.error)) +
                p15RectFrobNorm final.error := by
            gcongr
            exact p15RectFrobNorm_add_le _ _
          _ = p15RectFrobNorm middle.error + p15RectFrobNorm right.error +
                p15RectFrobNorm final.error := by
            rw [p15RectFrobNorm_orthonormal_left XA hXA,
              p15RectFrobNorm_orthonormal_right XB hXB,
              p15RectFrobNorm_orthonormal_left XA hXA]
      calc
        p15FrobNorm
            (final.result -
              p15MatMul (p15LowRankMatrix XA YA)
                (p15LowRankMatrix YB XB)) ≤
            p15RectFrobNorm middle.error + p15RectFrobNorm right.error +
              p15RectFrobNorm final.error := htotal
        _ ≤ p15GammaReal (b : ℝ) u * p15RectFrobNorm YA *
                p15RectFrobNorm YB +
              (p15GammaReal (r : ℝ) u * Real.sqrt (r : ℝ)) *
                (1 + p15GammaReal (b : ℝ) u) *
                p15RectFrobNorm YA * p15RectFrobNorm YB +
              (p15GammaReal (r : ℝ) u * Real.sqrt (r : ℝ)) *
                (1 + p15GammaReal (r : ℝ) u * Real.sqrt (r : ℝ)) *
                (1 + p15GammaReal (b : ℝ) u) *
                p15RectFrobNorm YA * p15RectFrobNorm YB :=
          add_le_add (add_le_add he0 he1) he2
        _ = (p15GammaReal (b : ℝ) u +
                (p15GammaReal (r : ℝ) u * Real.sqrt (r : ℝ)) *
                  (1 + p15GammaReal (b : ℝ) u) +
                (p15GammaReal (r : ℝ) u * Real.sqrt (r : ℝ)) *
                  (1 + p15GammaReal (r : ℝ) u * Real.sqrt (r : ℝ)) *
                  (1 + p15GammaReal (b : ℝ) u)) *
              (p15RectFrobNorm YA * p15RectFrobNorm YB) := by ring
        _ ≤ p15GammaReal (p15LowRankMatMulCost b r) u *
              (p15RectFrobNorm YA * p15RectFrobNorm YB) :=
          mul_le_mul_of_nonneg_right hcoeff had
        _ = p15GammaReal (p15LowRankMatMulCost b r) u *
              p15FrobNorm (p15LowRankMatrix XA YA) *
              p15FrobNorm (p15LowRankMatrix YB XB) := by
          rw [p15FrobNorm_lowRank_left XA YA hXA,
            p15FrobNorm_lowRank_right XB YB hXB]
          ring

lemma p15_product_perturbation_eq {n : ℕ}
    (A B EA EB Atilde Btilde : P15Matrix n)
    (hA : Atilde = A + EA) (hB : Btilde = B + EB) :
    p15MatMul Atilde Btilde - p15MatMul A B =
      p15MatMul EA B + p15MatMul A EB + p15MatMul EA EB := by
  rw [hA, hB]
  simp only [p15MatMul_eq_mul, Matrix.add_mul, Matrix.mul_add]
  abel

lemma p15_approximation_transfer {n : ℕ}
    (C A B EA EB Atilde Btilde : P15Matrix n) (g alpha delta : ℝ)
    (hg : 0 ≤ g)
    (hA : Atilde = A + EA) (hB : Btilde = B + EB)
    (hEA : p15FrobNorm EA ≤ alpha) (hEB : p15FrobNorm EB ≤ delta)
    (hforward :
      p15FrobNorm (C - p15MatMul Atilde Btilde) ≤
        g * p15FrobNorm Atilde * p15FrobNorm Btilde) :
    p15FrobNorm (C - p15MatMul A B) ≤
      g * p15FrobNorm A * p15FrobNorm B +
        (1 + g) *
          (alpha * p15FrobNorm B + p15FrobNorm A * delta + alpha * delta) := by
  have hnA : 0 ≤ p15FrobNorm A := p15RectFrobNorm_nonneg A
  have hnB : 0 ≤ p15FrobNorm B := p15RectFrobNorm_nonneg B
  have hnEA : 0 ≤ p15FrobNorm EA := p15RectFrobNorm_nonneg EA
  have hnEB : 0 ≤ p15FrobNorm EB := p15RectFrobNorm_nonneg EB
  have hnBt : 0 ≤ p15FrobNorm Btilde := p15RectFrobNorm_nonneg Btilde
  have halpha : 0 ≤ alpha := le_trans hnEA hEA
  have hdelta : 0 ≤ delta := le_trans hnEB hEB
  have hAt : p15FrobNorm Atilde ≤ p15FrobNorm A + alpha := by
    calc
      p15FrobNorm Atilde = p15FrobNorm (A + EA) := by rw [hA]
      _ ≤ p15FrobNorm A + p15FrobNorm EA := p15RectFrobNorm_add_le _ _
      _ ≤ p15FrobNorm A + alpha := add_le_add (le_refl _) hEA
  have hBt : p15FrobNorm Btilde ≤ p15FrobNorm B + delta := by
    calc
      p15FrobNorm Btilde = p15FrobNorm (B + EB) := by rw [hB]
      _ ≤ p15FrobNorm B + p15FrobNorm EB := p15RectFrobNorm_add_le _ _
      _ ≤ p15FrobNorm B + delta := add_le_add (le_refl _) hEB
  have hAtBt :
      p15FrobNorm Atilde * p15FrobNorm Btilde ≤
        (p15FrobNorm A + alpha) * (p15FrobNorm B + delta) := by
    calc
      p15FrobNorm Atilde * p15FrobNorm Btilde ≤
          (p15FrobNorm A + alpha) * p15FrobNorm Btilde :=
        mul_le_mul_of_nonneg_right hAt hnBt
      _ ≤ (p15FrobNorm A + alpha) * (p15FrobNorm B + delta) :=
        mul_le_mul_of_nonneg_left hBt (add_nonneg hnA halpha)
  have hforward' :
      p15FrobNorm (C - p15MatMul Atilde Btilde) ≤
        g * ((p15FrobNorm A + alpha) * (p15FrobNorm B + delta)) := by
    calc
      p15FrobNorm (C - p15MatMul Atilde Btilde) ≤
          g * p15FrobNorm Atilde * p15FrobNorm Btilde := hforward
      _ = g * (p15FrobNorm Atilde * p15FrobNorm Btilde) := by ring
      _ ≤ g * ((p15FrobNorm A + alpha) * (p15FrobNorm B + delta)) :=
        mul_le_mul_of_nonneg_left hAtBt hg
  have hEA_B :
      p15FrobNorm (p15MatMul EA B) ≤ alpha * p15FrobNorm B := by
    calc
      p15FrobNorm (p15MatMul EA B) ≤
          p15FrobNorm EA * p15FrobNorm B := p15RectFrobNorm_mul_le _ _
      _ ≤ alpha * p15FrobNorm B := mul_le_mul_of_nonneg_right hEA hnB
  have hA_EB :
      p15FrobNorm (p15MatMul A EB) ≤ p15FrobNorm A * delta := by
    calc
      p15FrobNorm (p15MatMul A EB) ≤
          p15FrobNorm A * p15FrobNorm EB := p15RectFrobNorm_mul_le _ _
      _ ≤ p15FrobNorm A * delta := mul_le_mul_of_nonneg_left hEB hnA
  have hEA_EB :
      p15FrobNorm (p15MatMul EA EB) ≤ alpha * delta := by
    calc
      p15FrobNorm (p15MatMul EA EB) ≤
          p15FrobNorm EA * p15FrobNorm EB := p15RectFrobNorm_mul_le _ _
      _ ≤ alpha * p15FrobNorm EB := mul_le_mul_of_nonneg_right hEA hnEB
      _ ≤ alpha * delta := mul_le_mul_of_nonneg_left hEB halpha
  have hperturb :
      p15FrobNorm (p15MatMul Atilde Btilde - p15MatMul A B) ≤
        alpha * p15FrobNorm B + p15FrobNorm A * delta + alpha * delta := by
    rw [p15_product_perturbation_eq A B EA EB Atilde Btilde hA hB]
    calc
      p15FrobNorm
          (p15MatMul EA B + p15MatMul A EB + p15MatMul EA EB) ≤
          p15FrobNorm (p15MatMul EA B + p15MatMul A EB) +
            p15FrobNorm (p15MatMul EA EB) := p15RectFrobNorm_add_le _ _
      _ ≤ (p15FrobNorm (p15MatMul EA B) +
              p15FrobNorm (p15MatMul A EB)) +
            p15FrobNorm (p15MatMul EA EB) := by
        gcongr
        exact p15RectFrobNorm_add_le _ _
      _ ≤ alpha * p15FrobNorm B + p15FrobNorm A * delta + alpha * delta :=
        add_le_add (add_le_add hEA_B hA_EB) hEA_EB
  have hsplit :
      C - p15MatMul A B =
        (C - p15MatMul Atilde Btilde) +
          (p15MatMul Atilde Btilde - p15MatMul A B) := by abel
  rw [hsplit]
  calc
    p15FrobNorm
        ((C - p15MatMul Atilde Btilde) +
          (p15MatMul Atilde Btilde - p15MatMul A B)) ≤
        p15FrobNorm (C - p15MatMul Atilde Btilde) +
          p15FrobNorm (p15MatMul Atilde Btilde - p15MatMul A B) :=
      p15RectFrobNorm_add_le _ _
    _ ≤ g * ((p15FrobNorm A + alpha) * (p15FrobNorm B + delta)) +
          (alpha * p15FrobNorm B + p15FrobNorm A * delta + alpha * delta) :=
      add_le_add hforward' hperturb
    _ = g * p15FrobNorm A * p15FrobNorm B +
          (1 + g) *
            (alpha * p15FrobNorm B + p15FrobNorm A * delta + alpha * delta) := by
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
  have hfirst :
      p15FrobNorm (run.trace.result - p15MatMul Atilde Btilde) ≤
        gammaC * p15FrobNorm Atilde * p15FrobNorm Btilde := by
    exact p15_trace_error_bound run.unitRoundoff_nonneg run.gamma_valid
      run.xA_orthonormal run.xB_orthonormal run.trace
  refine ⟨hfirst, ?_⟩
  have hgamma : 0 ≤ gammaC := by
    dsimp [gammaC]
    exact p15GammaReal_nonneg (p15LowRankMatMulCost_nonneg b r)
      run.unitRoundoff_nonneg run.gamma_valid
  have htransfer := p15_approximation_transfer
    run.trace.result run.A run.B run.approximationErrorA
      run.approximationErrorB Atilde Btilde gammaC
      (run.epsilon * run.betaA) (run.epsilon * run.betaB)
      hgamma run.approximationA_eq run.approximationB_eq
      run.approximationErrorA_le run.approximationErrorB_le hfirst
  calc
    p15FrobNorm (run.trace.result - p15MatMul run.A run.B) ≤
        gammaC * p15FrobNorm run.A * p15FrobNorm run.B +
          (1 + gammaC) *
            ((run.epsilon * run.betaA) * p15FrobNorm run.B +
              p15FrobNorm run.A * (run.epsilon * run.betaB) +
              (run.epsilon * run.betaA) * (run.epsilon * run.betaB)) :=
      htransfer
    _ = gammaC * p15FrobNorm run.A * p15FrobNorm run.B +
          run.epsilon * (1 + gammaC) *
            (run.betaA * p15FrobNorm run.B +
              p15FrobNorm run.A * run.betaB +
              run.epsilon * run.betaA * run.betaB) := by ring

end HighamBench
