import HighamBench.P15Definitions

namespace HighamBench

open scoped Matrix.Norms.Frobenius

lemma p15RectFrobNorm_eq_norm {m n : ℕ} (A : P15RectMatrix m n) :
    p15RectFrobNorm A = ‖A‖ := by
  rw [p15RectFrobNorm, Matrix.frobenius_norm_def, Real.sqrt_eq_rpow]
  congr 2
  funext i
  apply Finset.sum_congr rfl
  intro j hj
  rw [Real.rpow_two, Real.norm_eq_abs]
  exact (sq_abs (A i j)).symm

lemma p15_sum_sq_mul_left {b r n : ℕ}
    (X : P15RectMatrix b r) (M : P15RectMatrix r n)
    (hX : p15OrthonormalColumns X) :
    (∑ i : Fin b, ∑ j : Fin n, p15RectMatMul X M i j ^ 2) =
      ∑ k : Fin r, ∑ j : Fin n, M k j ^ 2 := by
  rw [Finset.sum_comm]
  calc
    (∑ j : Fin n, ∑ i : Fin b, p15RectMatMul X M i j ^ 2) =
        ∑ j : Fin n, ∑ k : Fin r, M k j ^ 2 := by
      apply Finset.sum_congr rfl
      intro j hj
      simp only [p15RectMatMul, pow_two]
      calc
        (∑ i : Fin b, (∑ k : Fin r, X i k * M k j) *
            ∑ l : Fin r, X i l * M l j) =
            ∑ i : Fin b, ∑ k : Fin r, ∑ l : Fin r,
              (X i k * M k j) * (X i l * M l j) := by
          apply Finset.sum_congr rfl
          intro i hi
          rw [Finset.sum_mul]
          apply Finset.sum_congr rfl
          intro k hk
          rw [Finset.mul_sum]
        _ = ∑ k : Fin r, ∑ i : Fin b, ∑ l : Fin r,
              (X i k * M k j) * (X i l * M l j) := Finset.sum_comm
        _ = ∑ k : Fin r, ∑ l : Fin r, ∑ i : Fin b,
              (X i k * M k j) * (X i l * M l j) := by
          apply Finset.sum_congr rfl
          intro k hk
          exact Finset.sum_comm
        _ = ∑ k : Fin r, ∑ l : Fin r,
              (∑ i : Fin b, X i k * X i l) * (M k j * M l j) := by
          apply Finset.sum_congr rfl
          intro k hk
          apply Finset.sum_congr rfl
          intro l hl
          rw [Finset.sum_mul]
          apply Finset.sum_congr rfl
          intro i hi
          ring
        _ = ∑ k : Fin r, M k j * M k j := by
          apply Finset.sum_congr rfl
          intro k hk
          simp [hX k]
    _ = ∑ k : Fin r, ∑ j : Fin n, M k j ^ 2 := Finset.sum_comm

lemma p15RectFrobNorm_mul_left_eq {b r n : ℕ}
    (X : P15RectMatrix b r) (M : P15RectMatrix r n)
    (hX : p15OrthonormalColumns X) :
    p15RectFrobNorm (p15RectMatMul X M) = p15RectFrobNorm M := by
  unfold p15RectFrobNorm
  rw [p15_sum_sq_mul_left X M hX]

lemma p15RectFrobNorm_transpose {m n : ℕ} (A : P15RectMatrix m n) :
    p15RectFrobNorm (p15RectTranspose A) = p15RectFrobNorm A := by
  unfold p15RectFrobNorm p15RectTranspose
  rw [Finset.sum_comm]

lemma p15RectFrobNorm_mul_right_transpose_eq {m b r : ℕ}
    (M : P15RectMatrix m r) (X : P15RectMatrix b r)
    (hX : p15OrthonormalColumns X) :
    p15RectFrobNorm (p15RectMatMul M (p15RectTranspose X)) =
      p15RectFrobNorm M := by
  have htranspose :
      p15RectTranspose (p15RectMatMul M (p15RectTranspose X)) =
        p15RectMatMul X (p15RectTranspose M) := by
    funext i j
    simp only [p15RectTranspose, p15RectMatMul]
    apply Finset.sum_congr rfl
    intro k hk
    ring
  calc
    p15RectFrobNorm (p15RectMatMul M (p15RectTranspose X)) =
        p15RectFrobNorm
          (p15RectTranspose (p15RectMatMul M (p15RectTranspose X))) :=
      (p15RectFrobNorm_transpose _).symm
    _ = p15RectFrobNorm (p15RectMatMul X (p15RectTranspose M)) := by rw [htranspose]
    _ = p15RectFrobNorm (p15RectTranspose M) :=
      p15RectFrobNorm_mul_left_eq X _ hX
    _ = p15RectFrobNorm M := p15RectFrobNorm_transpose M

lemma p15RectFrobNorm_orthonormal {b r : ℕ}
    (X : P15RectMatrix b r) (hX : p15OrthonormalColumns X) :
    p15RectFrobNorm X = Real.sqrt (r : ℝ) := by
  unfold p15RectFrobNorm
  congr 1
  rw [Finset.sum_comm]
  calc
    (∑ j : Fin r, ∑ i : Fin b, X i j ^ 2) = ∑ j : Fin r, (1 : ℝ) := by
      apply Finset.sum_congr rfl
      intro j hj
      simpa [pow_two] using hX j j
    _ = (r : ℝ) := by simp

lemma p15RectFrobNorm_add_le {m n : ℕ} (A B : P15RectMatrix m n) :
    p15RectFrobNorm (A + B) ≤ p15RectFrobNorm A + p15RectFrobNorm B := by
  simpa only [p15RectFrobNorm_eq_norm] using norm_add_le A B

lemma p15RectFrobNorm_sub_le {m n : ℕ} (A B : P15RectMatrix m n) :
    p15RectFrobNorm (A - B) ≤ p15RectFrobNorm A + p15RectFrobNorm B := by
  simpa only [p15RectFrobNorm_eq_norm] using norm_sub_le A B

lemma p15RectFrobNorm_mul_le {m n p : ℕ}
    (A : P15RectMatrix m n) (B : P15RectMatrix n p) :
    p15RectFrobNorm (p15RectMatMul A B) ≤
      p15RectFrobNorm A * p15RectFrobNorm B := by
  simpa only [p15RectFrobNorm_eq_norm] using Matrix.frobenius_norm_mul A B

lemma p15RectFrobNorm_nonneg {m n : ℕ} (A : P15RectMatrix m n) :
    0 ≤ p15RectFrobNorm A := by
  rw [p15RectFrobNorm_eq_norm]
  exact norm_nonneg A

lemma p15RectMatMul_assoc {m n p q : ℕ}
    (A : P15RectMatrix m n) (B : P15RectMatrix n p)
    (C : P15RectMatrix p q) :
    p15RectMatMul (p15RectMatMul A B) C =
      p15RectMatMul A (p15RectMatMul B C) := by
  change (A * B) * C = A * (B * C)
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

lemma p15_low_rank_product_assoc {b r : ℕ}
    (XA YA XB YB : P15RectMatrix b r) :
    p15MatMul (p15LowRankMatrix XA YA) (p15LowRankMatrix YB XB) =
      p15RectMatMul
        (p15RectMatMul XA
          (p15RectMatMul (p15RectTranspose YA) YB))
        (p15RectTranspose XB) := by
  change (XA * Matrix.transpose YA) * (YB * Matrix.transpose XB) =
    (XA * (Matrix.transpose YA * YB)) * Matrix.transpose XB
  simp only [Matrix.mul_assoc]

lemma p15GammaReal_nonneg {k u : ℝ} (hk : 0 ≤ k) (hu : 0 ≤ u)
    (hvalid : k * u < 1) : 0 ≤ p15GammaReal k u := by
  unfold p15GammaReal
  exact div_nonneg (mul_nonneg hk hu) (by linarith)

lemma p15GammaReal_comp_le {a d u : ℝ}
    (ha : 0 ≤ a) (hd : 0 ≤ d) (hu : 0 ≤ u)
    (hvalid : (a + d) * u < 1) :
    p15GammaReal a u + p15GammaReal d u +
        p15GammaReal a u * p15GammaReal d u ≤
      p15GammaReal (a + d) u := by
  have ha_valid : a * u < 1 := by
    nlinarith [mul_nonneg hd hu]
  have hd_valid : d * u < 1 := by
    nlinarith [mul_nonneg ha hu]
  have hda : 0 < 1 - a * u := by linarith
  have hdd : 0 < 1 - d * u := by linarith
  have hdad : 0 < 1 - (a + d) * u := by linarith
  have hrem :
      0 ≤ (a * u) * (d * u) /
        ((1 - (a + d) * u) * (1 - a * u) * (1 - d * u)) := by
    exact div_nonneg
      (mul_nonneg (mul_nonneg ha hu) (mul_nonneg hd hu))
      (mul_nonneg (mul_nonneg hdad.le hda.le) hdd.le)
  have hid :
      p15GammaReal (a + d) u =
        p15GammaReal a u + p15GammaReal d u +
          p15GammaReal a u * p15GammaReal d u +
            (a * u) * (d * u) /
              ((1 - (a + d) * u) * (1 - a * u) * (1 - d * u)) := by
    unfold p15GammaReal
    field_simp [ne_of_gt hda, ne_of_gt hdd, ne_of_gt hdad]
    ring
  rw [hid]
  linarith

lemma p15GammaReal_mul_le_gamma_mul {x s u : ℝ}
    (hx : 0 ≤ x) (hs : 1 ≤ s) (hu : 0 ≤ u)
    (hvalid : (x * s) * u < 1) :
    p15GammaReal x u * s ≤ p15GammaReal (x * s) u := by
  have hxu_nonneg : 0 ≤ x * u := mul_nonneg hx hu
  have hxs_nonneg : 0 ≤ x * s * u :=
    mul_nonneg (mul_nonneg hx (le_trans (by norm_num) hs)) hu
  have horder : x * u ≤ x * s * u := by nlinarith
  have hx_valid : x * u < 1 := lt_of_le_of_lt horder hvalid
  have hdx : 0 < 1 - x * u := by linarith
  have hdxs : 0 < 1 - x * s * u := by linarith
  unfold p15GammaReal
  rw [show x * u / (1 - x * u) * s =
      (x * s) * u / (1 - x * u) by
        field_simp [ne_of_gt hdx]]
  apply (div_le_div_iff₀ hdx hdxs).2
  nlinarith [mul_nonneg hxs_nonneg (sub_nonneg.mpr horder)]

lemma p15GammaReal_nat_mul_sqrt_le (r : ℕ) {u : ℝ} (hu : 0 ≤ u)
    (hvalid : ((r : ℝ) * Real.sqrt (r : ℝ)) * u < 1) :
    p15GammaReal (r : ℝ) u * Real.sqrt (r : ℝ) ≤
      p15GammaReal ((r : ℝ) * Real.sqrt (r : ℝ)) u := by
  cases r with
  | zero => simp [p15GammaReal]
  | succ r =>
      apply p15GammaReal_mul_le_gamma_mul
      · positivity
      · rw [Real.one_le_sqrt]
        exact_mod_cast Nat.succ_le_succ (Nat.zero_le r)
      · exact hu
      · exact hvalid

lemma p15_three_stage_gamma_le (b r : ℕ) {u : ℝ} (hu : 0 ≤ u)
    (hvalid : p15LowRankMatMulCost b r * u < 1) :
    let gb := p15GammaReal (b : ℝ) u
    let t := (r : ℝ) * Real.sqrt (r : ℝ)
    let gt := p15GammaReal t u
    gb + gt * (1 + gb) + gt * (1 + gt) * (1 + gb) ≤
      p15GammaReal (p15LowRankMatMulCost b r) u := by
  dsimp only
  let t : ℝ := (r : ℝ) * Real.sqrt (r : ℝ)
  have ht : 0 ≤ t := mul_nonneg (Nat.cast_nonneg r) (Real.sqrt_nonneg _)
  have hb : 0 ≤ (b : ℝ) := Nat.cast_nonneg b
  have hcost : p15LowRankMatMulCost b r = (b : ℝ) + 2 * t := by
    unfold p15LowRankMatMulCost t
    ring
  have hvalid' : ((b : ℝ) + 2 * t) * u < 1 := by simpa [hcost] using hvalid
  have hvalid1 : ((b : ℝ) + t) * u < 1 := by
    nlinarith [mul_nonneg ht hu]
  have hvalidt : t * u < 1 := by
    nlinarith [mul_nonneg hb hu, mul_nonneg ht hu]
  have hvalidb : (b : ℝ) * u < 1 := by
    nlinarith [mul_nonneg ht hu]
  let gb := p15GammaReal (b : ℝ) u
  let gt := p15GammaReal t u
  let gbt := p15GammaReal ((b : ℝ) + t) u
  have hgb : 0 ≤ gb := p15GammaReal_nonneg hb hu hvalidb
  have hgt : 0 ≤ gt := p15GammaReal_nonneg ht hu hvalidt
  have hfirst : gb + gt + gb * gt ≤ gbt := by
    exact p15GammaReal_comp_le hb ht hu hvalid1
  have hsecond : gbt + gt + gbt * gt ≤
      p15GammaReal (((b : ℝ) + t) + t) u := by
    apply p15GammaReal_comp_le (add_nonneg hb ht) ht hu
    nlinarith
  have hmul : (gb + gt + gb * gt) * gt ≤ gbt * gt :=
    mul_le_mul_of_nonneg_right hfirst hgt
  have hcombined :
      gb + gt * (1 + gb) + gt * (1 + gt) * (1 + gb) ≤
        gbt + gt + gbt * gt := by
    nlinarith
  calc
    gb + gt * (1 + gb) + gt * (1 + gt) * (1 + gb)
        ≤ gbt + gt + gbt * gt := hcombined
    _ ≤ p15GammaReal (((b : ℝ) + t) + t) u := hsecond
    _ = p15GammaReal (p15LowRankMatMulCost b r) u := by
      apply congrArg (fun z => p15GammaReal z u)
      rw [hcost]
      ring

lemma p15_trace_low_rank_error {b r : ℕ} {u : ℝ}
    (XA YA XB YB : P15RectMatrix b r)
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
  let At := p15LowRankMatrix XA YA
  let Bt := p15LowRankMatrix YB XB
  let M := p15RectMatMul (p15RectTranspose YA) YB
  let gb := p15GammaReal (b : ℝ) u
  let t := (r : ℝ) * Real.sqrt (r : ℝ)
  let gt := p15GammaReal t u
  let gc := p15GammaReal (p15LowRankMatMulCost b r) u
  let z := p15FrobNorm At * p15FrobNorm Bt
  have hAt : p15FrobNorm At = p15RectFrobNorm YA := by
    calc
      p15FrobNorm At =
          p15RectFrobNorm (p15RectMatMul XA (p15RectTranspose YA)) := by
            rfl
      _ = p15RectFrobNorm (p15RectTranspose YA) :=
        p15RectFrobNorm_mul_left_eq XA _ hXA
      _ = p15RectFrobNorm YA := p15RectFrobNorm_transpose YA
  have hBt : p15FrobNorm Bt = p15RectFrobNorm YB := by
    calc
      p15FrobNorm Bt =
          p15RectFrobNorm (p15RectMatMul YB (p15RectTranspose XB)) := by
            rfl
      _ = p15RectFrobNorm YB :=
        p15RectFrobNorm_mul_right_transpose_eq YB XB hXB
  have hz : 0 ≤ z :=
    mul_nonneg (p15RectFrobNorm_nonneg At) (p15RectFrobNorm_nonneg Bt)
  have hM : p15RectFrobNorm M ≤ z := by
    calc
      p15RectFrobNorm M ≤
          p15RectFrobNorm (p15RectTranspose YA) * p15RectFrobNorm YB :=
        p15RectFrobNorm_mul_le _ _
      _ = z := by rw [p15RectFrobNorm_transpose, ← hAt, ← hBt]
  have ht : 0 ≤ t := mul_nonneg (Nat.cast_nonneg r) (Real.sqrt_nonneg _)
  have hb : 0 ≤ (b : ℝ) := Nat.cast_nonneg b
  have hcost : p15LowRankMatMulCost b r = (b : ℝ) + 2 * t := by
    unfold p15LowRankMatMulCost t
    ring
  have hvalidt : t * u < 1 := by
    have hcost' : ((b : ℝ) + 2 * t) * u < 1 := by simpa [hcost] using hvalid
    nlinarith [mul_nonneg hb hu, mul_nonneg ht hu]
  have hvalidb : (b : ℝ) * u < 1 := by
    have hcost' : ((b : ℝ) + 2 * t) * u < 1 := by simpa [hcost] using hvalid
    nlinarith [mul_nonneg ht hu]
  have hgb : 0 ≤ gb := p15GammaReal_nonneg hb hu hvalidb
  have hgt : 0 ≤ gt := p15GammaReal_nonneg ht hu hvalidt
  have hdelta :
      p15GammaReal (r : ℝ) u * Real.sqrt (r : ℝ) ≤ gt := by
    exact p15GammaReal_nat_mul_sqrt_le r hu hvalidt
  have hcoeff : gb + gt * (1 + gb) + gt * (1 + gt) * (1 + gb) ≤ gc := by
    exact p15_three_stage_gamma_le b r hu hvalid
  cases trace with
  | leftAssociated middleStage leftStage finalStage =>
      have he0 : p15RectFrobNorm middleStage.error ≤ gb * z := by
        calc
          p15RectFrobNorm middleStage.error ≤
              p15GammaReal (b : ℝ) u *
                p15RectFrobNorm (p15RectTranspose YA) * p15RectFrobNorm YB :=
            middleStage.error_le
          _ = gb * z := by
            rw [p15RectFrobNorm_transpose, ← hAt, ← hBt]
            simp only [gb, z]
            ring
      have hmiddle : p15RectFrobNorm middleStage.result ≤ (1 + gb) * z := by
        calc
          p15RectFrobNorm middleStage.result =
              p15RectFrobNorm (M + middleStage.error) := by rfl
          _ ≤ p15RectFrobNorm M + p15RectFrobNorm middleStage.error :=
            p15RectFrobNorm_add_le _ _
          _ ≤ z + gb * z := add_le_add hM he0
          _ = (1 + gb) * z := by ring
      have he1 : p15RectFrobNorm leftStage.error ≤ gt * (1 + gb) * z := by
        calc
          p15RectFrobNorm leftStage.error ≤
              p15GammaReal (r : ℝ) u * p15RectFrobNorm XA *
                p15RectFrobNorm middleStage.result := leftStage.error_le
          _ = (p15GammaReal (r : ℝ) u * Real.sqrt (r : ℝ)) *
                p15RectFrobNorm middleStage.result := by
            rw [p15RectFrobNorm_orthonormal XA hXA]
          _ ≤ gt * p15RectFrobNorm middleStage.result := by
            exact mul_le_mul_of_nonneg_right hdelta
              (p15RectFrobNorm_nonneg middleStage.result)
          _ ≤ gt * ((1 + gb) * z) := by
            exact mul_le_mul_of_nonneg_left hmiddle hgt
          _ = gt * (1 + gb) * z := by ring
      have hleft : p15RectFrobNorm leftStage.result ≤
          (1 + gt) * (1 + gb) * z := by
        calc
          p15RectFrobNorm leftStage.result =
              p15RectFrobNorm
                (p15RectMatMul XA middleStage.result + leftStage.error) := by rfl
          _ ≤ p15RectFrobNorm (p15RectMatMul XA middleStage.result) +
                p15RectFrobNorm leftStage.error := p15RectFrobNorm_add_le _ _
          _ = p15RectFrobNorm middleStage.result +
                p15RectFrobNorm leftStage.error := by
            rw [p15RectFrobNorm_mul_left_eq XA _ hXA]
          _ ≤ (1 + gb) * z + gt * (1 + gb) * z := add_le_add hmiddle he1
          _ = (1 + gt) * (1 + gb) * z := by ring
      have he2 : p15RectFrobNorm finalStage.error ≤
          gt * (1 + gt) * (1 + gb) * z := by
        calc
          p15RectFrobNorm finalStage.error ≤
              p15GammaReal (r : ℝ) u * p15RectFrobNorm leftStage.result *
                p15RectFrobNorm (p15RectTranspose XB) := finalStage.error_le
          _ = (p15GammaReal (r : ℝ) u * Real.sqrt (r : ℝ)) *
                p15RectFrobNorm leftStage.result := by
            rw [p15RectFrobNorm_transpose, p15RectFrobNorm_orthonormal XB hXB]
            ring
          _ ≤ gt * p15RectFrobNorm leftStage.result := by
            exact mul_le_mul_of_nonneg_right hdelta
              (p15RectFrobNorm_nonneg leftStage.result)
          _ ≤ gt * ((1 + gt) * (1 + gb) * z) :=
            mul_le_mul_of_nonneg_left hleft hgt
          _ = gt * (1 + gt) * (1 + gb) * z := by ring
      have hdiff :
          finalStage.result - p15MatMul At Bt =
            p15RectMatMul
                (p15RectMatMul XA middleStage.error + leftStage.error)
                (p15RectTranspose XB) + finalStage.error := by
        rw [show p15MatMul At Bt =
            p15RectMatMul (p15RectMatMul XA M) (p15RectTranspose XB) by
              exact p15_low_rank_product_assoc XA YA XB YB]
        simp only [P15RoundedMatMulStage.result, p15RectMatMul_add_left,
          p15RectMatMul_add_right]
        abel
      have hnorm : p15RectFrobNorm (finalStage.result - p15MatMul At Bt) ≤
          p15RectFrobNorm middleStage.error + p15RectFrobNorm leftStage.error +
            p15RectFrobNorm finalStage.error := by
        rw [hdiff]
        calc
          p15RectFrobNorm
              (p15RectMatMul
                  (p15RectMatMul XA middleStage.error + leftStage.error)
                  (p15RectTranspose XB) + finalStage.error) ≤
              p15RectFrobNorm
                  (p15RectMatMul
                    (p15RectMatMul XA middleStage.error + leftStage.error)
                    (p15RectTranspose XB)) + p15RectFrobNorm finalStage.error :=
            p15RectFrobNorm_add_le _ _
          _ = p15RectFrobNorm (p15RectMatMul XA middleStage.error + leftStage.error) +
                p15RectFrobNorm finalStage.error := by
            rw [p15RectFrobNorm_mul_right_transpose_eq _ XB hXB]
          _ ≤ (p15RectFrobNorm (p15RectMatMul XA middleStage.error) +
                p15RectFrobNorm leftStage.error) + p15RectFrobNorm finalStage.error := by
            gcongr
            exact p15RectFrobNorm_add_le _ _
          _ = p15RectFrobNorm middleStage.error + p15RectFrobNorm leftStage.error +
                p15RectFrobNorm finalStage.error := by
            rw [p15RectFrobNorm_mul_left_eq XA _ hXA]
      have hfinal : p15RectFrobNorm (finalStage.result - p15MatMul At Bt) ≤ gc * z := by
        calc
          p15RectFrobNorm (finalStage.result - p15MatMul At Bt) ≤
              p15RectFrobNorm middleStage.error + p15RectFrobNorm leftStage.error +
                p15RectFrobNorm finalStage.error := hnorm
          _ ≤ gb * z + gt * (1 + gb) * z + gt * (1 + gt) * (1 + gb) * z := by
            gcongr
          _ = (gb + gt * (1 + gb) + gt * (1 + gt) * (1 + gb)) * z := by ring
          _ ≤ gc * z := mul_le_mul_of_nonneg_right hcoeff hz
      simpa only [P15LowRankMatMulTrace.result, At, Bt, gc, z, p15FrobNorm,
        mul_assoc] using hfinal

  | rightAssociated middleStage rightStage finalStage =>
      have he0 : p15RectFrobNorm middleStage.error ≤ gb * z := by
        calc
          p15RectFrobNorm middleStage.error ≤
              p15GammaReal (b : ℝ) u *
                p15RectFrobNorm (p15RectTranspose YA) * p15RectFrobNorm YB :=
            middleStage.error_le
          _ = gb * z := by
            rw [p15RectFrobNorm_transpose, ← hAt, ← hBt]
            simp only [gb, z]
            ring
      have hmiddle : p15RectFrobNorm middleStage.result ≤ (1 + gb) * z := by
        calc
          p15RectFrobNorm middleStage.result =
              p15RectFrobNorm (M + middleStage.error) := by rfl
          _ ≤ p15RectFrobNorm M + p15RectFrobNorm middleStage.error :=
            p15RectFrobNorm_add_le _ _
          _ ≤ z + gb * z := add_le_add hM he0
          _ = (1 + gb) * z := by ring
      have he1 : p15RectFrobNorm rightStage.error ≤ gt * (1 + gb) * z := by
        calc
          p15RectFrobNorm rightStage.error ≤
              p15GammaReal (r : ℝ) u * p15RectFrobNorm middleStage.result *
                p15RectFrobNorm (p15RectTranspose XB) := rightStage.error_le
          _ = (p15GammaReal (r : ℝ) u * Real.sqrt (r : ℝ)) *
                p15RectFrobNorm middleStage.result := by
            rw [p15RectFrobNorm_transpose, p15RectFrobNorm_orthonormal XB hXB]
            ring
          _ ≤ gt * p15RectFrobNorm middleStage.result := by
            exact mul_le_mul_of_nonneg_right hdelta
              (p15RectFrobNorm_nonneg middleStage.result)
          _ ≤ gt * ((1 + gb) * z) := mul_le_mul_of_nonneg_left hmiddle hgt
          _ = gt * (1 + gb) * z := by ring
      have hright : p15RectFrobNorm rightStage.result ≤
          (1 + gt) * (1 + gb) * z := by
        calc
          p15RectFrobNorm rightStage.result =
              p15RectFrobNorm
                (p15RectMatMul middleStage.result (p15RectTranspose XB) +
                  rightStage.error) := by rfl
          _ ≤ p15RectFrobNorm
                  (p15RectMatMul middleStage.result (p15RectTranspose XB)) +
                p15RectFrobNorm rightStage.error := p15RectFrobNorm_add_le _ _
          _ = p15RectFrobNorm middleStage.result + p15RectFrobNorm rightStage.error := by
            rw [p15RectFrobNorm_mul_right_transpose_eq _ XB hXB]
          _ ≤ (1 + gb) * z + gt * (1 + gb) * z := add_le_add hmiddle he1
          _ = (1 + gt) * (1 + gb) * z := by ring
      have he2 : p15RectFrobNorm finalStage.error ≤
          gt * (1 + gt) * (1 + gb) * z := by
        calc
          p15RectFrobNorm finalStage.error ≤
              p15GammaReal (r : ℝ) u * p15RectFrobNorm XA *
                p15RectFrobNorm rightStage.result := finalStage.error_le
          _ = (p15GammaReal (r : ℝ) u * Real.sqrt (r : ℝ)) *
                p15RectFrobNorm rightStage.result := by
            rw [p15RectFrobNorm_orthonormal XA hXA]
          _ ≤ gt * p15RectFrobNorm rightStage.result := by
            exact mul_le_mul_of_nonneg_right hdelta
              (p15RectFrobNorm_nonneg rightStage.result)
          _ ≤ gt * ((1 + gt) * (1 + gb) * z) :=
            mul_le_mul_of_nonneg_left hright hgt
          _ = gt * (1 + gt) * (1 + gb) * z := by ring
      have hdiff :
          finalStage.result - p15MatMul At Bt =
            p15RectMatMul XA
                (p15RectMatMul middleStage.error (p15RectTranspose XB) +
                  rightStage.error) + finalStage.error := by
        rw [show p15MatMul At Bt =
            p15RectMatMul (p15RectMatMul XA M) (p15RectTranspose XB) by
              exact p15_low_rank_product_assoc XA YA XB YB]
        dsimp only [M]
        simp only [P15RoundedMatMulStage.result, p15RectMatMul_add_left,
          p15RectMatMul_add_right, p15RectMatMul_assoc]
        abel
      have hnorm : p15RectFrobNorm (finalStage.result - p15MatMul At Bt) ≤
          p15RectFrobNorm middleStage.error + p15RectFrobNorm rightStage.error +
            p15RectFrobNorm finalStage.error := by
        rw [hdiff]
        calc
          p15RectFrobNorm
              (p15RectMatMul XA
                  (p15RectMatMul middleStage.error (p15RectTranspose XB) +
                    rightStage.error) + finalStage.error) ≤
              p15RectFrobNorm
                  (p15RectMatMul XA
                    (p15RectMatMul middleStage.error (p15RectTranspose XB) +
                      rightStage.error)) + p15RectFrobNorm finalStage.error :=
            p15RectFrobNorm_add_le _ _
          _ = p15RectFrobNorm
                  (p15RectMatMul middleStage.error (p15RectTranspose XB) +
                    rightStage.error) + p15RectFrobNorm finalStage.error := by
            rw [p15RectFrobNorm_mul_left_eq XA _ hXA]
          _ ≤ (p15RectFrobNorm
                  (p15RectMatMul middleStage.error (p15RectTranspose XB)) +
                p15RectFrobNorm rightStage.error) + p15RectFrobNorm finalStage.error := by
            gcongr
            exact p15RectFrobNorm_add_le _ _
          _ = p15RectFrobNorm middleStage.error + p15RectFrobNorm rightStage.error +
                p15RectFrobNorm finalStage.error := by
            rw [p15RectFrobNorm_mul_right_transpose_eq _ XB hXB]
      have hfinal : p15RectFrobNorm (finalStage.result - p15MatMul At Bt) ≤ gc * z := by
        calc
          p15RectFrobNorm (finalStage.result - p15MatMul At Bt) ≤
              p15RectFrobNorm middleStage.error + p15RectFrobNorm rightStage.error +
                p15RectFrobNorm finalStage.error := hnorm
          _ ≤ gb * z + gt * (1 + gb) * z + gt * (1 + gt) * (1 + gb) * z := by
            gcongr
          _ = (gb + gt * (1 + gb) + gt * (1 + gt) * (1 + gb)) * z := by ring
          _ ≤ gc * z := mul_le_mul_of_nonneg_right hcoeff hz
      simpa only [P15LowRankMatMulTrace.result, At, Bt, gc, z, p15FrobNorm,
        mul_assoc] using hfinal

lemma p15_approximation_transfer {n : ℕ}
    (C At Bt A B EA EB : P15Matrix n) (epsilon betaA betaB gammaC : ℝ)
    (hgamma : 0 ≤ gammaC)
    (hAt : At = A + EA) (hBt : Bt = B + EB)
    (hEA : p15FrobNorm EA ≤ epsilon * betaA)
    (hEB : p15FrobNorm EB ≤ epsilon * betaB)
    (hcomputed : p15FrobNorm (C - p15MatMul At Bt) ≤
      gammaC * p15FrobNorm At * p15FrobNorm Bt) :
    p15FrobNorm (C - p15MatMul A B) ≤
      gammaC * p15FrobNorm A * p15FrobNorm B +
        epsilon * (1 + gammaC) *
          (betaA * p15FrobNorm B +
            p15FrobNorm A * betaB + epsilon * betaA * betaB) := by
  let a := epsilon * betaA
  let d := epsilon * betaB
  have hEA' : p15FrobNorm EA ≤ a := by simpa only [a] using hEA
  have hEB' : p15FrobNorm EB ≤ d := by simpa only [d] using hEB
  have ha : 0 ≤ a := le_trans (p15RectFrobNorm_nonneg EA) hEA'
  have hd : 0 ≤ d := le_trans (p15RectFrobNorm_nonneg EB) hEB'
  have hAn : 0 ≤ p15FrobNorm A := p15RectFrobNorm_nonneg A
  have hBn : 0 ≤ p15FrobNorm B := p15RectFrobNorm_nonneg B
  have hAtNorm : p15FrobNorm At ≤ p15FrobNorm A + a := by
    rw [hAt]
    calc
      p15FrobNorm (A + EA) ≤ p15FrobNorm A + p15FrobNorm EA :=
        p15RectFrobNorm_add_le A EA
      _ ≤ p15FrobNorm A + a := by gcongr
  have hBtNorm : p15FrobNorm Bt ≤ p15FrobNorm B + d := by
    rw [hBt]
    calc
      p15FrobNorm (B + EB) ≤ p15FrobNorm B + p15FrobNorm EB :=
        p15RectFrobNorm_add_le B EB
      _ ≤ p15FrobNorm B + d := by gcongr
  have hnormProduct : p15FrobNorm At * p15FrobNorm Bt ≤
      (p15FrobNorm A + a) * (p15FrobNorm B + d) := by
    exact mul_le_mul hAtNorm hBtNorm (p15RectFrobNorm_nonneg Bt)
      (add_nonneg hAn ha)
  have hcomputed' : p15FrobNorm (C - p15MatMul At Bt) ≤
      gammaC * ((p15FrobNorm A + a) * (p15FrobNorm B + d)) := by
    calc
      p15FrobNorm (C - p15MatMul At Bt) ≤
          gammaC * p15FrobNorm At * p15FrobNorm Bt := hcomputed
      _ = gammaC * (p15FrobNorm At * p15FrobNorm Bt) := by ring
      _ ≤ gammaC * ((p15FrobNorm A + a) * (p15FrobNorm B + d)) :=
        mul_le_mul_of_nonneg_left hnormProduct hgamma
  have hEAB : p15FrobNorm (p15MatMul EA B) ≤ a * p15FrobNorm B := by
    calc
      p15FrobNorm (p15MatMul EA B) ≤ p15FrobNorm EA * p15FrobNorm B :=
        p15RectFrobNorm_mul_le EA B
      _ ≤ a * p15FrobNorm B := mul_le_mul_of_nonneg_right hEA' hBn
  have hAEB : p15FrobNorm (p15MatMul A EB) ≤ p15FrobNorm A * d := by
    calc
      p15FrobNorm (p15MatMul A EB) ≤ p15FrobNorm A * p15FrobNorm EB :=
        p15RectFrobNorm_mul_le A EB
      _ ≤ p15FrobNorm A * d := mul_le_mul_of_nonneg_left hEB' hAn
  have hEAEB : p15FrobNorm (p15MatMul EA EB) ≤ a * d := by
    calc
      p15FrobNorm (p15MatMul EA EB) ≤ p15FrobNorm EA * p15FrobNorm EB :=
        p15RectFrobNorm_mul_le EA EB
      _ ≤ a * d :=
        mul_le_mul hEA' hEB' (p15RectFrobNorm_nonneg EB) ha
  have hproductEq :
      p15MatMul At Bt - p15MatMul A B =
        p15MatMul EA B + p15MatMul A EB + p15MatMul EA EB := by
    rw [hAt, hBt]
    change (A + EA) * (B + EB) - A * B = EA * B + A * EB + EA * EB
    simp only [Matrix.add_mul, Matrix.mul_add]
    abel
  have hproductError : p15FrobNorm (p15MatMul At Bt - p15MatMul A B) ≤
      a * p15FrobNorm B + p15FrobNorm A * d + a * d := by
    rw [hproductEq]
    calc
      p15FrobNorm (p15MatMul EA B + p15MatMul A EB + p15MatMul EA EB) ≤
          p15FrobNorm (p15MatMul EA B + p15MatMul A EB) +
            p15FrobNorm (p15MatMul EA EB) := p15RectFrobNorm_add_le _ _
      _ ≤ (p15FrobNorm (p15MatMul EA B) + p15FrobNorm (p15MatMul A EB)) +
            p15FrobNorm (p15MatMul EA EB) := by
        gcongr
        exact p15RectFrobNorm_add_le _ _
      _ ≤ (a * p15FrobNorm B + p15FrobNorm A * d) + a * d := by
        gcongr
      _ = a * p15FrobNorm B + p15FrobNorm A * d + a * d := by ring
  have hdecomp :
      C - p15MatMul A B =
        (C - p15MatMul At Bt) + (p15MatMul At Bt - p15MatMul A B) := by
    abel
  rw [hdecomp]
  calc
    p15FrobNorm
        ((C - p15MatMul At Bt) + (p15MatMul At Bt - p15MatMul A B)) ≤
      p15FrobNorm (C - p15MatMul At Bt) +
        p15FrobNorm (p15MatMul At Bt - p15MatMul A B) :=
      p15RectFrobNorm_add_le _ _
    _ ≤ gammaC * ((p15FrobNorm A + a) * (p15FrobNorm B + d)) +
        (a * p15FrobNorm B + p15FrobNorm A * d + a * d) :=
      add_le_add hcomputed' hproductError
    _ = gammaC * p15FrobNorm A * p15FrobNorm B +
        epsilon * (1 + gammaC) *
          (betaA * p15FrobNorm B + p15FrobNorm A * betaB +
            epsilon * betaA * betaB) := by
      dsimp only [a, d]
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
  have hfirst := p15_trace_low_rank_error
    run.XA run.YA run.XB run.YB run.xA_orthonormal run.xB_orthonormal
      run.unitRoundoff_nonneg run.gamma_valid run.trace
  have hcost_nonneg : 0 ≤ p15LowRankMatMulCost b r := by
    unfold p15LowRankMatMulCost
    positivity
  have hgamma :
      0 ≤ p15GammaReal (p15LowRankMatMulCost b r) run.unitRoundoff :=
    p15GammaReal_nonneg hcost_nonneg run.unitRoundoff_nonneg run.gamma_valid
  refine ⟨hfirst, ?_⟩
  exact p15_approximation_transfer
    run.trace.result
    (p15LowRankMatrix run.XA run.YA)
    (p15LowRankMatrix run.YB run.XB)
    run.A run.B run.approximationErrorA run.approximationErrorB
    run.epsilon run.betaA run.betaB
    (p15GammaReal (p15LowRankMatMulCost b r) run.unitRoundoff)
    hgamma run.approximationA_eq run.approximationB_eq
    run.approximationErrorA_le run.approximationErrorB_le hfirst

end HighamBench
