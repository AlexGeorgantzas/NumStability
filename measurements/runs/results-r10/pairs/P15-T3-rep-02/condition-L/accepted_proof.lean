import HighamBench.P15Definitions
import NumStability.Source.Higham.Chapter19.Sensitivity.Closure

namespace HighamBench

open scoped BigOperators

lemma p15RectFrobNorm_nonneg {m n : ℕ} (A : P15RectMatrix m n) :
    0 ≤ p15RectFrobNorm A := by
  exact Real.sqrt_nonneg _

lemma p15RectFrobNorm_add_le {m n : ℕ}
    (A B : P15RectMatrix m n) :
    p15RectFrobNorm (A + B) ≤ p15RectFrobNorm A + p15RectFrobNorm B := by
  simpa [p15RectFrobNorm, NumStability.frobNormRect,
    NumStability.frobNormSqRect] using
    (NumStability.frobNormRect_add_le A B)

lemma p15RectFrobNorm_sub_le {m n : ℕ}
    (A B : P15RectMatrix m n) :
    p15RectFrobNorm (A - B) ≤ p15RectFrobNorm A + p15RectFrobNorm B := by
  simpa [p15RectFrobNorm, NumStability.frobNormRect,
    NumStability.frobNormSqRect] using
    (NumStability.frobNormRect_sub_le A B)

lemma p15RectFrobNorm_add_add_le {m n : ℕ}
    (A B C : P15RectMatrix m n) :
    p15RectFrobNorm (A + B + C) ≤
      p15RectFrobNorm A + p15RectFrobNorm B + p15RectFrobNorm C := by
  have h := add_le_add_right (p15RectFrobNorm_add_le A B)
    (p15RectFrobNorm C)
  exact le_trans (p15RectFrobNorm_add_le (A + B) C) (by linarith)

lemma p15RectFrobNorm_rectMatMul_le {m n p : ℕ}
    (A : P15RectMatrix m n) (B : P15RectMatrix n p) :
    p15RectFrobNorm (p15RectMatMul A B) ≤
      p15RectFrobNorm A * p15RectFrobNorm B := by
  simpa [p15RectFrobNorm, p15RectMatMul,
    NumStability.frobNormRect, NumStability.frobNormSqRect,
    NumStability.rectMatMul] using
    (NumStability.frobNormRect_rectMatMul_le A B)

lemma p15RectMatMul_assoc {m n p q : ℕ}
    (A : P15RectMatrix m n) (B : P15RectMatrix n p)
    (C : P15RectMatrix p q) :
    p15RectMatMul (p15RectMatMul A B) C =
      p15RectMatMul A (p15RectMatMul B C) := by
  simpa [p15RectMatMul, NumStability.rectMatMul] using
    (NumStability.rectMatMul_assoc A B C)

lemma p15RectMatMul_add_left {m n p : ℕ}
    (A B : P15RectMatrix m n) (C : P15RectMatrix n p) :
    p15RectMatMul (A + B) C =
      p15RectMatMul A C + p15RectMatMul B C := by
  simpa [p15RectMatMul, NumStability.rectMatMul] using
    (NumStability.rectMatMul_add_left A B C)

lemma p15RectMatMul_add_right {m n p : ℕ}
    (A : P15RectMatrix m n) (B C : P15RectMatrix n p) :
    p15RectMatMul A (B + C) =
      p15RectMatMul A B + p15RectMatMul A C := by
  simpa [p15RectMatMul, NumStability.rectMatMul] using
    (NumStability.rectMatMul_add_right A B C)

lemma p15RectFrobNorm_transpose {m n : ℕ} (A : P15RectMatrix m n) :
    p15RectFrobNorm (p15RectTranspose A) = p15RectFrobNorm A := by
  simpa [p15RectFrobNorm, p15RectTranspose,
    NumStability.frobNormRect, NumStability.frobNormSqRect,
    NumStability.finiteTranspose] using
    (NumStability.frobNormRect_finiteTranspose A)

lemma p15RectTranspose_mul {m n p : ℕ}
    (A : P15RectMatrix m n) (B : P15RectMatrix n p) :
    p15RectTranspose (p15RectMatMul A B) =
      p15RectMatMul (p15RectTranspose B) (p15RectTranspose A) := by
  ext i j
  simp only [p15RectTranspose, p15RectMatMul]
  apply Finset.sum_congr rfl
  intro k _
  ring

lemma p15RectFrobNorm_mul_eq_of_orthonormal_left {m n p : ℕ}
    (Q : P15RectMatrix m n) (B : P15RectMatrix n p)
    (hQ : p15OrthonormalColumns Q) :
    p15RectFrobNorm (p15RectMatMul Q B) = p15RectFrobNorm B := by
  have hQ' : NumStability.GramSchmidtOrthonormalColumns Q := by
    intro i j
    simpa [NumStability.GramSchmidtOrthonormalColumns,
      NumStability.rectangularGram, NumStability.idMatrix] using hQ i j
  simpa [p15RectFrobNorm, p15RectMatMul,
    NumStability.frobNormRect, NumStability.frobNormSqRect,
    NumStability.rectMatMul] using
    (NumStability.H19Sensitivity.frobNormRect_rectMatMul_eq_of_orthonormal_left
      Q B hQ')

lemma p15RectFrobNorm_mul_transpose_eq_of_orthonormal_right {m n p : ℕ}
    (A : P15RectMatrix m n) (Q : P15RectMatrix p n)
    (hQ : p15OrthonormalColumns Q) :
    p15RectFrobNorm (p15RectMatMul A (p15RectTranspose Q)) =
      p15RectFrobNorm A := by
  calc
    p15RectFrobNorm (p15RectMatMul A (p15RectTranspose Q)) =
        p15RectFrobNorm
          (p15RectTranspose (p15RectMatMul A (p15RectTranspose Q))) := by
            rw [p15RectFrobNorm_transpose]
    _ = p15RectFrobNorm
          (p15RectMatMul Q (p15RectTranspose A)) := by
            rw [p15RectTranspose_mul]
            rfl
    _ = p15RectFrobNorm (p15RectTranspose A) :=
          p15RectFrobNorm_mul_eq_of_orthonormal_left Q _ hQ
    _ = p15RectFrobNorm A := p15RectFrobNorm_transpose A

lemma p15RectFrobNorm_orthonormal {m n : ℕ}
    (Q : P15RectMatrix m n) (hQ : p15OrthonormalColumns Q) :
    p15RectFrobNorm Q = Real.sqrt (n : ℝ) := by
  unfold p15RectFrobNorm
  congr 1
  calc
    (∑ i : Fin m, ∑ j : Fin n, Q i j ^ 2) =
        ∑ j : Fin n, ∑ i : Fin m, Q i j ^ 2 := by
          rw [Finset.sum_comm]
    _ = ∑ _j : Fin n, (1 : ℝ) := by
          apply Finset.sum_congr rfl
          intro j _
          simpa [pow_two] using hQ j j
    _ = (n : ℝ) := by simp

lemma p15GammaReal_nonneg {x u : ℝ} (hx : 0 ≤ x) (hu : 0 ≤ u)
    (hvalid : x * u < 1) :
    0 ≤ p15GammaReal x u := by
  unfold p15GammaReal
  exact div_nonneg (mul_nonneg hx hu) (le_of_lt (sub_pos.mpr hvalid))

lemma p15_one_add_gamma_mul_le {x y u : ℝ}
    (hx : 0 ≤ x) (hy : 0 ≤ y) (hu : 0 ≤ u)
    (hvalid : (x + y) * u < 1) :
    (1 + p15GammaReal x u) * (1 + p15GammaReal y u) ≤
      1 + p15GammaReal (x + y) u := by
  have hxu : x * u < 1 := by nlinarith [mul_nonneg hy hu]
  have hyu : y * u < 1 := by nlinarith [mul_nonneg hx hu]
  have hxden : 0 < 1 - x * u := sub_pos.mpr hxu
  have hyden : 0 < 1 - y * u := sub_pos.mpr hyu
  have hxyden : 0 < 1 - (x + y) * u := sub_pos.mpr hvalid
  rw [show 1 + p15GammaReal x u = 1 / (1 - x * u) by
        unfold p15GammaReal
        field_simp
        ring,
      show 1 + p15GammaReal y u = 1 / (1 - y * u) by
        unfold p15GammaReal
        field_simp
        ring,
      show 1 + p15GammaReal (x + y) u =
          1 / (1 - (x + y) * u) by
        unfold p15GammaReal
        field_simp
        ring,
      one_div, one_div, one_div]
  have hinv :
      (1 - x * u)⁻¹ * (1 - y * u)⁻¹ =
        ((1 - x * u) * (1 - y * u))⁻¹ := by
    field_simp
  rw [hinv]
  rw [inv_le_inv₀ (mul_pos hxden hyden) hxyden]
  nlinarith [mul_nonneg (mul_nonneg hx hy) (sq_nonneg u)]

lemma p15GammaReal_nat_mul_sqrt_le (r : ℕ) {u : ℝ}
    (hu : 0 ≤ u)
    (hvalid : ((r : ℝ) * Real.sqrt (r : ℝ)) * u < 1) :
    p15GammaReal (r : ℝ) u * Real.sqrt (r : ℝ) ≤
      p15GammaReal ((r : ℝ) * Real.sqrt (r : ℝ)) u := by
  by_cases hr : r = 0
  · subst r
    simp [p15GammaReal]
  · have hrpos : 0 < r := Nat.pos_of_ne_zero hr
    let s : ℝ := Real.sqrt (r : ℝ)
    let q : ℝ := (r : ℝ) * s
    have hrsq : s ^ 2 = (r : ℝ) := by
      dsimp [s]
      exact Real.sq_sqrt (by positivity)
    have hs0 : 0 ≤ s := Real.sqrt_nonneg _
    have hs1 : 1 ≤ s := by
      have hr1 : (1 : ℝ) ≤ (r : ℝ) := by exact_mod_cast hrpos
      nlinarith
    have hrq : (r : ℝ) ≤ q := by
      dsimp [q]
      simpa only [one_mul, mul_one] using
        (mul_le_mul_of_nonneg_left hs1 (Nat.cast_nonneg r : (0 : ℝ) ≤ r))
    have hq0 : 0 ≤ q := mul_nonneg (Nat.cast_nonneg r) hs0
    have hqu : q * u < 1 := by simpa [q, s] using hvalid
    have hru : (r : ℝ) * u < 1 := by
      nlinarith [mul_nonneg (sub_nonneg.mpr hrq) hu]
    have hrden : 0 < 1 - (r : ℝ) * u := sub_pos.mpr hru
    have hqden : 0 < 1 - q * u := sub_pos.mpr hqu
    have hnum : 0 ≤ q * u := mul_nonneg hq0 hu
    change (((r : ℝ) * u / (1 - (r : ℝ) * u)) * s) ≤
      q * u / (1 - q * u)
    rw [show ((r : ℝ) * u / (1 - (r : ℝ) * u)) * s =
        q * u / (1 - (r : ℝ) * u) by
      dsimp [q]
      ring]
    apply (div_le_div_iff₀ hrden hqden).2
    nlinarith [mul_nonneg hnum (mul_nonneg (sub_nonneg.mpr hrq) hu)]

lemma p15LowRank_gamma_coefficient_le {b r : ℕ} {u : ℝ}
    (hu : 0 ≤ u)
    (hvalid : p15LowRankMatMulCost b r * u < 1) :
    let gb := p15GammaReal (b : ℝ) u
    let a := p15GammaReal (r : ℝ) u * Real.sqrt (r : ℝ)
    let gc := p15GammaReal (p15LowRankMatMulCost b r) u
    gb + a * (1 + gb) + a * (1 + a) * (1 + gb) ≤ gc := by
  dsimp only
  let s : ℝ := Real.sqrt (r : ℝ)
  let q : ℝ := (r : ℝ) * s
  let gb : ℝ := p15GammaReal (b : ℝ) u
  let gq : ℝ := p15GammaReal q u
  let a : ℝ := p15GammaReal (r : ℝ) u * s
  let gc : ℝ := p15GammaReal (p15LowRankMatMulCost b r) u
  have hs0 : 0 ≤ s := Real.sqrt_nonneg _
  have hq0 : 0 ≤ q := mul_nonneg (Nat.cast_nonneg r) hs0
  have hb0 : 0 ≤ (b : ℝ) := Nat.cast_nonneg b
  have hcost : p15LowRankMatMulCost b r = (b : ℝ) + 2 * q := by
    dsimp [q, s]
    unfold p15LowRankMatMulCost
    ring
  have hbqvalid : ((b : ℝ) + q) * u < 1 := by
    rw [hcost] at hvalid
    nlinarith [mul_nonneg hq0 hu]
  have hqvalid : q * u < 1 := by
    rw [hcost] at hvalid
    nlinarith [mul_nonneg hb0 hu, mul_nonneg hq0 hu]
  have hbvalid : (b : ℝ) * u < 1 := by
    nlinarith [mul_nonneg hq0 hu]
  have hgb0 : 0 ≤ gb := p15GammaReal_nonneg hb0 hu hbvalid
  have hgq0 : 0 ≤ gq := p15GammaReal_nonneg hq0 hu hqvalid
  have ha0 : 0 ≤ a := by
    dsimp [a, s]
    exact mul_nonneg
      (p15GammaReal_nonneg (Nat.cast_nonneg r) hu (by
        have hrq : (r : ℝ) ≤ q := by
          by_cases hr : r = 0
          · subst r; simp [q]
          · have hrpos : 0 < r := Nat.pos_of_ne_zero hr
            have hrsq : s ^ 2 = (r : ℝ) := by
              dsimp [s]
              exact Real.sq_sqrt (by positivity)
            have hs1 : 1 ≤ s := by
              have : (1 : ℝ) ≤ (r : ℝ) := by exact_mod_cast hrpos
              nlinarith [Real.sqrt_nonneg (r : ℝ)]
            dsimp [q]
            simpa only [one_mul, mul_one] using
              (mul_le_mul_of_nonneg_left hs1
                (Nat.cast_nonneg r : (0 : ℝ) ≤ r))
        nlinarith [mul_nonneg (sub_nonneg.mpr hrq) hu])) hs0
  have haq : a ≤ gq := by
    dsimp [a, gq, q, s]
    exact p15GammaReal_nat_mul_sqrt_le r hu hqvalid
  have hcomp1 :
      (1 + gb) * (1 + gq) ≤
        1 + p15GammaReal ((b : ℝ) + q) u := by
    dsimp [gb, gq]
    exact p15_one_add_gamma_mul_le hb0 hq0 hu hbqvalid
  have hcomp2 :
      (1 + p15GammaReal ((b : ℝ) + q) u) * (1 + gq) ≤ 1 + gc := by
    have htotalvalid : (((b : ℝ) + q) + q) * u < 1 := by
      calc
        (((b : ℝ) + q) + q) * u = ((b : ℝ) + 2 * q) * u := by ring
        _ = p15LowRankMatMulCost b r * u := by rw [hcost]
        _ < 1 := hvalid
    have hc := p15_one_add_gamma_mul_le
      (add_nonneg hb0 hq0) hq0 hu htotalvalid
    dsimp [gq, gc]
    rw [hcost]
    convert hc using 1 <;> ring
  have hprod : (1 + gb) * (1 + a) * (1 + a) ≤ 1 + gc := by
    calc
      (1 + gb) * (1 + a) * (1 + a) ≤
          (1 + gb) * (1 + gq) * (1 + gq) := by gcongr
      _ ≤ (1 + p15GammaReal ((b : ℝ) + q) u) * (1 + gq) := by
        gcongr
      _ ≤ 1 + gc := hcomp2
  change
    p15GammaReal (b : ℝ) u +
        (p15GammaReal (r : ℝ) u * Real.sqrt (r : ℝ)) *
          (1 + p15GammaReal (b : ℝ) u) +
        (p15GammaReal (r : ℝ) u * Real.sqrt (r : ℝ)) *
          (1 + p15GammaReal (r : ℝ) u * Real.sqrt (r : ℝ)) *
          (1 + p15GammaReal (b : ℝ) u) ≤
      p15GammaReal (p15LowRankMatMulCost b r) u
  change gb + a * (1 + gb) + a * (1 + a) * (1 + gb) ≤ gc
  nlinarith [hprod]

lemma p15LowRankMatMulCost_nonneg (b r : ℕ) :
    0 ≤ p15LowRankMatMulCost b r := by
  unfold p15LowRankMatMulCost
  positivity

lemma p15LowRankMatMulCost_ge_b (b r : ℕ) :
    (b : ℝ) ≤ p15LowRankMatMulCost b r := by
  unfold p15LowRankMatMulCost
  have : 0 ≤ 2 * (r : ℝ) * Real.sqrt (r : ℝ) := by positivity
  linarith

lemma p15LowRankMatMulCost_ge_r (b r : ℕ) :
    (r : ℝ) ≤ p15LowRankMatMulCost b r := by
  by_cases hr : r = 0
  · subst r
    simp [p15LowRankMatMulCost]
  · have hrpos : 0 < r := Nat.pos_of_ne_zero hr
    have hrsq : Real.sqrt (r : ℝ) ^ 2 = (r : ℝ) :=
      Real.sq_sqrt (by positivity)
    have hrsqrt : 1 ≤ Real.sqrt (r : ℝ) := by
      have : (1 : ℝ) ≤ (r : ℝ) := by exact_mod_cast hrpos
      nlinarith [Real.sqrt_nonneg (r : ℝ)]
    unfold p15LowRankMatMulCost
    nlinarith [(Nat.cast_nonneg b : (0 : ℝ) ≤ b),
      (Nat.cast_nonneg r : (0 : ℝ) ≤ r)]

lemma p15LowRank_product_assoc {b r : ℕ}
    (XA YA XB YB : P15RectMatrix b r) :
    p15MatMul (p15LowRankMatrix XA YA) (p15LowRankMatrix YB XB) =
      p15RectMatMul
        (p15RectMatMul XA
          (p15RectMatMul (p15RectTranspose YA) YB))
        (p15RectTranspose XB) := by
  change
    p15RectMatMul
        (p15RectMatMul XA (p15RectTranspose YA))
        (p15RectMatMul YB (p15RectTranspose XB)) = _
  rw [p15RectMatMul_assoc]
  rw [← p15RectMatMul_assoc (p15RectTranspose YA)]
  rw [← p15RectMatMul_assoc XA]

lemma p15_leftAssociated_error_eq {b r : ℕ} {u : ℝ}
    {XA YA XB YB : P15RectMatrix b r}
    (middle : P15RoundedMatMulStage r b r u (p15RectTranspose YA) YB)
    (left : P15RoundedMatMulStage b r r u XA middle.result)
    (final : P15RoundedMatMulStage b r b u left.result
      (p15RectTranspose XB)) :
    final.result -
        p15MatMul (p15LowRankMatrix XA YA) (p15LowRankMatrix YB XB) =
      p15RectMatMul
          (p15RectMatMul XA middle.error + left.error)
          (p15RectTranspose XB) + final.error := by
  rw [p15LowRank_product_assoc]
  change
    p15RectMatMul
          (p15RectMatMul XA
              (p15RectMatMul (p15RectTranspose YA) YB + middle.error) +
            left.error)
          (p15RectTranspose XB) + final.error -
        p15RectMatMul
          (p15RectMatMul XA
            (p15RectMatMul (p15RectTranspose YA) YB))
          (p15RectTranspose XB) = _
  rw [p15RectMatMul_add_right, p15RectMatMul_add_left,
    p15RectMatMul_add_left]
  rw [p15RectMatMul_add_left]
  abel

lemma p15_rightAssociated_error_eq {b r : ℕ} {u : ℝ}
    {XA YA XB YB : P15RectMatrix b r}
    (middle : P15RoundedMatMulStage r b r u (p15RectTranspose YA) YB)
    (right : P15RoundedMatMulStage r r b u middle.result
      (p15RectTranspose XB))
    (final : P15RoundedMatMulStage b r b u XA right.result) :
    final.result -
        p15MatMul (p15LowRankMatrix XA YA) (p15LowRankMatrix YB XB) =
      p15RectMatMul XA
          (p15RectMatMul middle.error (p15RectTranspose XB) + right.error) +
        final.error := by
  rw [p15LowRank_product_assoc]
  change
    p15RectMatMul XA
          (p15RectMatMul
              (p15RectMatMul (p15RectTranspose YA) YB + middle.error)
              (p15RectTranspose XB) + right.error) +
        final.error -
      p15RectMatMul
          (p15RectMatMul XA
            (p15RectMatMul (p15RectTranspose YA) YB))
          (p15RectTranspose XB) = _
  rw [p15RectMatMul_add_left, p15RectMatMul_add_right,
    p15RectMatMul_add_right, p15RectMatMul_assoc]
  rw [p15RectMatMul_add_right]
  rw [← p15RectMatMul_assoc (p15RectTranspose YA) YB,
    ← p15RectMatMul_assoc XA]
  abel

lemma p15MatMul_perturbation_eq {n : ℕ}
    (A B EA EB : P15Matrix n) :
    p15MatMul (A + EA) (B + EB) - p15MatMul A B =
      p15MatMul EA B + p15MatMul A EB + p15MatMul EA EB := by
  change
    p15RectMatMul (A + EA) (B + EB) - p15RectMatMul A B =
      p15RectMatMul EA B + p15RectMatMul A EB + p15RectMatMul EA EB
  rw [p15RectMatMul_add_left, p15RectMatMul_add_right,
    p15RectMatMul_add_right]
  abel

set_option maxHeartbeats 1000000

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
  let gammaB : ℝ := p15GammaReal (b : ℝ) run.unitRoundoff
  let gammaR : ℝ := p15GammaReal (r : ℝ) run.unitRoundoff
  let sqrtR : ℝ := Real.sqrt (r : ℝ)
  let alpha : ℝ := gammaR * sqrtR
  let gammaC : ℝ :=
    p15GammaReal (p15LowRankMatMulCost b r) run.unitRoundoff
  change
    p15FrobNorm (run.trace.result - p15MatMul Atilde Btilde) ≤
        gammaC * p15FrobNorm Atilde * p15FrobNorm Btilde ∧
      p15FrobNorm (run.trace.result - p15MatMul run.A run.B) ≤
        gammaC * p15FrobNorm run.A * p15FrobNorm run.B +
          run.epsilon * (1 + gammaC) *
            (run.betaA * p15FrobNorm run.B +
              p15FrobNorm run.A * run.betaB +
              run.epsilon * run.betaA * run.betaB)
  have hAtilde : p15FrobNorm Atilde = p15RectFrobNorm run.YA := by
    dsimp [Atilde, p15LowRankMatrix, p15FrobNorm]
    rw [p15RectFrobNorm_mul_eq_of_orthonormal_left _ _ run.xA_orthonormal]
    exact p15RectFrobNorm_transpose run.YA
  have hBtilde : p15FrobNorm Btilde = p15RectFrobNorm run.YB := by
    dsimp [Btilde, p15LowRankMatrix, p15FrobNorm]
    exact p15RectFrobNorm_mul_transpose_eq_of_orthonormal_right
      run.YB run.XB run.xB_orthonormal
  have hXA : p15RectFrobNorm run.XA = sqrtR := by
    dsimp [sqrtR]
    exact p15RectFrobNorm_orthonormal run.XA run.xA_orthonormal
  have hXB : p15RectFrobNorm (p15RectTranspose run.XB) = sqrtR := by
    rw [p15RectFrobNorm_transpose]
    dsimp [sqrtR]
    exact p15RectFrobNorm_orthonormal run.XB run.xB_orthonormal
  have hvalidB : (b : ℝ) * run.unitRoundoff < 1 := by
    exact lt_of_le_of_lt
      (mul_le_mul_of_nonneg_right (p15LowRankMatMulCost_ge_b b r)
        run.unitRoundoff_nonneg)
      run.gamma_valid
  have hvalidR : (r : ℝ) * run.unitRoundoff < 1 := by
    exact lt_of_le_of_lt
      (mul_le_mul_of_nonneg_right (p15LowRankMatMulCost_ge_r b r)
        run.unitRoundoff_nonneg)
      run.gamma_valid
  have hgammaB0 : 0 ≤ gammaB := by
    dsimp [gammaB]
    exact p15GammaReal_nonneg (Nat.cast_nonneg b)
      run.unitRoundoff_nonneg hvalidB
  have hgammaR0 : 0 ≤ gammaR := by
    dsimp [gammaR]
    exact p15GammaReal_nonneg (Nat.cast_nonneg r)
      run.unitRoundoff_nonneg hvalidR
  have hsqrtR0 : 0 ≤ sqrtR := by
    dsimp [sqrtR]
    exact Real.sqrt_nonneg _
  have halpha0 : 0 ≤ alpha := mul_nonneg hgammaR0 hsqrtR0
  have hgammaC0 : 0 ≤ gammaC := by
    dsimp [gammaC]
    exact p15GammaReal_nonneg (p15LowRankMatMulCost_nonneg b r)
      run.unitRoundoff_nonneg run.gamma_valid
  have hcoef :
      gammaB + alpha * (1 + gammaB) +
          alpha * (1 + alpha) * (1 + gammaB) ≤ gammaC := by
    dsimp [gammaB, alpha, gammaR, sqrtR, gammaC]
    exact p15LowRank_gamma_coefficient_le
      run.unitRoundoff_nonneg run.gamma_valid
  have hbase0 :
      0 ≤ p15FrobNorm Atilde * p15FrobNorm Btilde :=
    mul_nonneg (p15RectFrobNorm_nonneg Atilde)
      (p15RectFrobNorm_nonneg Btilde)
  have hfirst :
      p15FrobNorm (run.trace.result - p15MatMul Atilde Btilde) ≤
        gammaC * p15FrobNorm Atilde * p15FrobNorm Btilde := by
    cases htrace : run.trace with
    | leftAssociated middle left final =>
        have hmiddleExact :
            p15RectFrobNorm
                (p15RectMatMul (p15RectTranspose run.YA) run.YB) ≤
              p15FrobNorm Atilde * p15FrobNorm Btilde := by
          calc
            p15RectFrobNorm
                (p15RectMatMul (p15RectTranspose run.YA) run.YB) ≤
                p15RectFrobNorm (p15RectTranspose run.YA) *
                  p15RectFrobNorm run.YB :=
              p15RectFrobNorm_rectMatMul_le _ _
            _ = p15FrobNorm Atilde * p15FrobNorm Btilde := by
              rw [p15RectFrobNorm_transpose, ← hAtilde, ← hBtilde]
        have hmiddleError :
            p15RectFrobNorm middle.error ≤
              gammaB * (p15FrobNorm Atilde * p15FrobNorm Btilde) := by
          calc
            p15RectFrobNorm middle.error ≤
                gammaB * p15RectFrobNorm (p15RectTranspose run.YA) *
                  p15RectFrobNorm run.YB := by
              simpa [gammaB] using middle.error_le
            _ = gammaB *
                (p15FrobNorm Atilde * p15FrobNorm Btilde) := by
              rw [p15RectFrobNorm_transpose, ← hAtilde, ← hBtilde]
              ring
        have hmiddleResult :
            p15RectFrobNorm middle.result ≤
              (1 + gammaB) *
                (p15FrobNorm Atilde * p15FrobNorm Btilde) := by
          calc
            p15RectFrobNorm middle.result ≤
                p15RectFrobNorm
                    (p15RectMatMul (p15RectTranspose run.YA) run.YB) +
                  p15RectFrobNorm middle.error := by
              exact p15RectFrobNorm_add_le _ _
            _ ≤ (1 + gammaB) *
                (p15FrobNorm Atilde * p15FrobNorm Btilde) := by
              nlinarith
        have hleftError :
            p15RectFrobNorm left.error ≤
              alpha * (1 + gammaB) *
                (p15FrobNorm Atilde * p15FrobNorm Btilde) := by
          calc
            p15RectFrobNorm left.error ≤
                gammaR * p15RectFrobNorm run.XA *
                  p15RectFrobNorm middle.result := by
              simpa [gammaR] using left.error_le
            _ = alpha * p15RectFrobNorm middle.result := by
              rw [hXA]
            _ ≤ alpha *
                ((1 + gammaB) *
                  (p15FrobNorm Atilde * p15FrobNorm Btilde)) :=
              mul_le_mul_of_nonneg_left hmiddleResult halpha0
            _ = alpha * (1 + gammaB) *
                (p15FrobNorm Atilde * p15FrobNorm Btilde) := by ring
        have hleftResult :
            p15RectFrobNorm left.result ≤
              (1 + alpha) * (1 + gammaB) *
                (p15FrobNorm Atilde * p15FrobNorm Btilde) := by
          calc
            p15RectFrobNorm left.result ≤
                p15RectFrobNorm
                    (p15RectMatMul run.XA middle.result) +
                  p15RectFrobNorm left.error :=
              p15RectFrobNorm_add_le _ _
            _ = p15RectFrobNorm middle.result +
                  p15RectFrobNorm left.error := by
              rw [p15RectFrobNorm_mul_eq_of_orthonormal_left
                run.XA middle.result run.xA_orthonormal]
            _ ≤ (1 + alpha) * (1 + gammaB) *
                (p15FrobNorm Atilde * p15FrobNorm Btilde) := by
              nlinarith
        have hfinalError :
            p15FrobNorm final.error ≤
              alpha * (1 + alpha) * (1 + gammaB) *
                (p15FrobNorm Atilde * p15FrobNorm Btilde) := by
          calc
            p15FrobNorm final.error ≤
                gammaR * p15RectFrobNorm left.result *
                  p15RectFrobNorm (p15RectTranspose run.XB) := by
              simpa [gammaR, p15FrobNorm] using final.error_le
            _ = alpha * p15RectFrobNorm left.result := by
              rw [hXB]
              dsimp [alpha]
              ring
            _ ≤ alpha *
                ((1 + alpha) * (1 + gammaB) *
                  (p15FrobNorm Atilde * p15FrobNorm Btilde)) :=
              mul_le_mul_of_nonneg_left hleftResult halpha0
            _ = alpha * (1 + alpha) * (1 + gammaB) *
                (p15FrobNorm Atilde * p15FrobNorm Btilde) := by ring
        rw [show
          (P15LowRankMatMulTrace.leftAssociated middle left final).result -
              p15MatMul Atilde Btilde =
            p15RectMatMul
                (p15RectMatMul run.XA middle.error + left.error)
                (p15RectTranspose run.XB) + final.error by
          dsimp [Atilde, Btilde, P15LowRankMatMulTrace.result]
          exact p15_leftAssociated_error_eq middle left final]
        calc
          p15FrobNorm
              (p15RectMatMul
                    (p15RectMatMul run.XA middle.error + left.error)
                    (p15RectTranspose run.XB) + final.error) ≤
              p15RectFrobNorm
                  (p15RectMatMul
                    (p15RectMatMul run.XA middle.error + left.error)
                    (p15RectTranspose run.XB)) +
                p15FrobNorm final.error :=
            p15RectFrobNorm_add_le _ _
          _ = p15RectFrobNorm
                (p15RectMatMul run.XA middle.error + left.error) +
                p15FrobNorm final.error := by
            rw [p15RectFrobNorm_mul_transpose_eq_of_orthonormal_right
              _ run.XB run.xB_orthonormal]
          _ ≤ (p15RectFrobNorm (p15RectMatMul run.XA middle.error) +
                  p15RectFrobNorm left.error) +
                p15FrobNorm final.error := by
            gcongr
            exact p15RectFrobNorm_add_le _ _
          _ = (p15RectFrobNorm middle.error +
                  p15RectFrobNorm left.error) +
                p15FrobNorm final.error := by
            rw [p15RectFrobNorm_mul_eq_of_orthonormal_left
              run.XA middle.error run.xA_orthonormal]
          _ ≤ (gammaB + alpha * (1 + gammaB) +
                  alpha * (1 + alpha) * (1 + gammaB)) *
                (p15FrobNorm Atilde * p15FrobNorm Btilde) := by
            nlinarith
          _ ≤ gammaC *
                (p15FrobNorm Atilde * p15FrobNorm Btilde) :=
            mul_le_mul_of_nonneg_right hcoef hbase0
          _ = gammaC * p15FrobNorm Atilde * p15FrobNorm Btilde := by ring
    | rightAssociated middle right final =>
        have hmiddleExact :
            p15RectFrobNorm
                (p15RectMatMul (p15RectTranspose run.YA) run.YB) ≤
              p15FrobNorm Atilde * p15FrobNorm Btilde := by
          calc
            p15RectFrobNorm
                (p15RectMatMul (p15RectTranspose run.YA) run.YB) ≤
                p15RectFrobNorm (p15RectTranspose run.YA) *
                  p15RectFrobNorm run.YB :=
              p15RectFrobNorm_rectMatMul_le _ _
            _ = p15FrobNorm Atilde * p15FrobNorm Btilde := by
              rw [p15RectFrobNorm_transpose, ← hAtilde, ← hBtilde]
        have hmiddleError :
            p15RectFrobNorm middle.error ≤
              gammaB * (p15FrobNorm Atilde * p15FrobNorm Btilde) := by
          calc
            p15RectFrobNorm middle.error ≤
                gammaB * p15RectFrobNorm (p15RectTranspose run.YA) *
                  p15RectFrobNorm run.YB := by
              simpa [gammaB] using middle.error_le
            _ = gammaB *
                (p15FrobNorm Atilde * p15FrobNorm Btilde) := by
              rw [p15RectFrobNorm_transpose, ← hAtilde, ← hBtilde]
              ring
        have hmiddleResult :
            p15RectFrobNorm middle.result ≤
              (1 + gammaB) *
                (p15FrobNorm Atilde * p15FrobNorm Btilde) := by
          calc
            p15RectFrobNorm middle.result ≤
                p15RectFrobNorm
                    (p15RectMatMul (p15RectTranspose run.YA) run.YB) +
                  p15RectFrobNorm middle.error :=
              p15RectFrobNorm_add_le _ _
            _ ≤ (1 + gammaB) *
                (p15FrobNorm Atilde * p15FrobNorm Btilde) := by
              nlinarith
        have hrightError :
            p15RectFrobNorm right.error ≤
              alpha * (1 + gammaB) *
                (p15FrobNorm Atilde * p15FrobNorm Btilde) := by
          calc
            p15RectFrobNorm right.error ≤
                gammaR * p15RectFrobNorm middle.result *
                  p15RectFrobNorm (p15RectTranspose run.XB) := by
              simpa [gammaR] using right.error_le
            _ = alpha * p15RectFrobNorm middle.result := by
              rw [hXB]
              dsimp [alpha]
              ring
            _ ≤ alpha *
                ((1 + gammaB) *
                  (p15FrobNorm Atilde * p15FrobNorm Btilde)) :=
              mul_le_mul_of_nonneg_left hmiddleResult halpha0
            _ = alpha * (1 + gammaB) *
                (p15FrobNorm Atilde * p15FrobNorm Btilde) := by ring
        have hrightResult :
            p15RectFrobNorm right.result ≤
              (1 + alpha) * (1 + gammaB) *
                (p15FrobNorm Atilde * p15FrobNorm Btilde) := by
          calc
            p15RectFrobNorm right.result ≤
                p15RectFrobNorm
                    (p15RectMatMul middle.result
                      (p15RectTranspose run.XB)) +
                  p15RectFrobNorm right.error :=
              p15RectFrobNorm_add_le _ _
            _ = p15RectFrobNorm middle.result +
                  p15RectFrobNorm right.error := by
              rw [p15RectFrobNorm_mul_transpose_eq_of_orthonormal_right
                middle.result run.XB run.xB_orthonormal]
            _ ≤ (1 + alpha) * (1 + gammaB) *
                (p15FrobNorm Atilde * p15FrobNorm Btilde) := by
              nlinarith
        have hfinalError :
            p15FrobNorm final.error ≤
              alpha * (1 + alpha) * (1 + gammaB) *
                (p15FrobNorm Atilde * p15FrobNorm Btilde) := by
          calc
            p15FrobNorm final.error ≤
                gammaR * p15RectFrobNorm run.XA *
                  p15RectFrobNorm right.result := by
              simpa [gammaR, p15FrobNorm] using final.error_le
            _ = alpha * p15RectFrobNorm right.result := by
              rw [hXA]
            _ ≤ alpha *
                ((1 + alpha) * (1 + gammaB) *
                  (p15FrobNorm Atilde * p15FrobNorm Btilde)) :=
              mul_le_mul_of_nonneg_left hrightResult halpha0
            _ = alpha * (1 + alpha) * (1 + gammaB) *
                (p15FrobNorm Atilde * p15FrobNorm Btilde) := by ring
        rw [show
          (P15LowRankMatMulTrace.rightAssociated middle right final).result -
              p15MatMul Atilde Btilde =
            p15RectMatMul run.XA
                (p15RectMatMul middle.error (p15RectTranspose run.XB) +
                  right.error) + final.error by
          dsimp [Atilde, Btilde, P15LowRankMatMulTrace.result]
          exact p15_rightAssociated_error_eq middle right final]
        calc
          p15FrobNorm
              (p15RectMatMul run.XA
                  (p15RectMatMul middle.error (p15RectTranspose run.XB) +
                    right.error) + final.error) ≤
              p15RectFrobNorm
                  (p15RectMatMul run.XA
                    (p15RectMatMul middle.error (p15RectTranspose run.XB) +
                      right.error)) +
                p15FrobNorm final.error :=
            p15RectFrobNorm_add_le _ _
          _ = p15RectFrobNorm
                (p15RectMatMul middle.error (p15RectTranspose run.XB) +
                  right.error) + p15FrobNorm final.error := by
            rw [p15RectFrobNorm_mul_eq_of_orthonormal_left
              run.XA _ run.xA_orthonormal]
          _ ≤
              (p15RectFrobNorm
                    (p15RectMatMul middle.error (p15RectTranspose run.XB)) +
                  p15RectFrobNorm right.error) +
                p15FrobNorm final.error := by
            gcongr
            exact p15RectFrobNorm_add_le _ _
          _ = (p15RectFrobNorm middle.error +
                  p15RectFrobNorm right.error) +
                p15FrobNorm final.error := by
            rw [p15RectFrobNorm_mul_transpose_eq_of_orthonormal_right
              middle.error run.XB run.xB_orthonormal]
          _ ≤ (gammaB + alpha * (1 + gammaB) +
                  alpha * (1 + alpha) * (1 + gammaB)) *
                (p15FrobNorm Atilde * p15FrobNorm Btilde) := by
            nlinarith
          _ ≤ gammaC *
                (p15FrobNorm Atilde * p15FrobNorm Btilde) :=
            mul_le_mul_of_nonneg_right hcoef hbase0
          _ = gammaC * p15FrobNorm Atilde * p15FrobNorm Btilde := by ring
  constructor
  · exact hfirst
  · let errorA : P15Matrix b := run.approximationErrorA
    let errorB : P15Matrix b := run.approximationErrorB
    let normA : ℝ := p15FrobNorm run.A
    let normB : ℝ := p15FrobNorm run.B
    let boundA : ℝ := run.epsilon * run.betaA
    let boundB : ℝ := run.epsilon * run.betaB
    have hnormA0 : 0 ≤ normA := p15RectFrobNorm_nonneg run.A
    have hnormB0 : 0 ≤ normB := p15RectFrobNorm_nonneg run.B
    have herrorA0 : 0 ≤ p15FrobNorm errorA :=
      p15RectFrobNorm_nonneg errorA
    have herrorB0 : 0 ≤ p15FrobNorm errorB :=
      p15RectFrobNorm_nonneg errorB
    have herrorA : p15FrobNorm errorA ≤ boundA := by
      simpa [errorA, boundA] using run.approximationErrorA_le
    have herrorB : p15FrobNorm errorB ≤ boundB := by
      simpa [errorB, boundB] using run.approximationErrorB_le
    have hboundA0 : 0 ≤ boundA := le_trans herrorA0 herrorA
    have hboundB0 : 0 ≤ boundB := le_trans herrorB0 herrorB
    have hAtildeBound : p15FrobNorm Atilde ≤ normA + boundA := by
      calc
        p15FrobNorm Atilde = p15FrobNorm (run.A + errorA) := by
          rw [show Atilde = run.A + errorA by
            simpa [Atilde, errorA] using run.approximationA_eq]
        _ ≤ p15FrobNorm run.A + p15FrobNorm errorA :=
          p15RectFrobNorm_add_le _ _
        _ ≤ normA + boundA := by
          dsimp [normA]
          linarith
    have hBtildeBound : p15FrobNorm Btilde ≤ normB + boundB := by
      calc
        p15FrobNorm Btilde = p15FrobNorm (run.B + errorB) := by
          rw [show Btilde = run.B + errorB by
            simpa [Btilde, errorB] using run.approximationB_eq]
        _ ≤ p15FrobNorm run.B + p15FrobNorm errorB :=
          p15RectFrobNorm_add_le _ _
        _ ≤ normB + boundB := by
          dsimp [normB]
          linarith
    have htildeProduct :
        p15FrobNorm Atilde * p15FrobNorm Btilde ≤
          (normA + boundA) * (normB + boundB) := by
      exact mul_le_mul hAtildeBound hBtildeBound
        (p15RectFrobNorm_nonneg Btilde)
        (add_nonneg hnormA0 hboundA0)
    have hperturbationIdentity :
        p15MatMul Atilde Btilde - p15MatMul run.A run.B =
          p15MatMul errorA run.B + p15MatMul run.A errorB +
            p15MatMul errorA errorB := by
      rw [show Atilde = run.A + errorA by
        simpa [Atilde, errorA] using run.approximationA_eq]
      rw [show Btilde = run.B + errorB by
        simpa [Btilde, errorB] using run.approximationB_eq]
      exact p15MatMul_perturbation_eq run.A run.B errorA errorB
    have hperturbation :
        p15FrobNorm (p15MatMul Atilde Btilde - p15MatMul run.A run.B) ≤
          boundA * normB + normA * boundB + boundA * boundB := by
      rw [hperturbationIdentity]
      have hmulErrorA :
          p15FrobNorm (p15MatMul errorA run.B) ≤
            p15FrobNorm errorA * normB := by
        dsimp [normB]
        exact p15RectFrobNorm_rectMatMul_le errorA run.B
      have hmulErrorB :
          p15FrobNorm (p15MatMul run.A errorB) ≤
            normA * p15FrobNorm errorB := by
        dsimp [normA]
        exact p15RectFrobNorm_rectMatMul_le run.A errorB
      have hmulBoth :
          p15FrobNorm (p15MatMul errorA errorB) ≤
            p15FrobNorm errorA * p15FrobNorm errorB :=
        p15RectFrobNorm_rectMatMul_le errorA errorB
      calc
        p15FrobNorm
            (p15MatMul errorA run.B + p15MatMul run.A errorB +
              p15MatMul errorA errorB) ≤
            (p15FrobNorm (p15MatMul errorA run.B) +
              p15FrobNorm (p15MatMul run.A errorB)) +
              p15FrobNorm (p15MatMul errorA errorB) :=
          p15RectFrobNorm_add_add_le _ _ _
        _ ≤
            (p15FrobNorm errorA * normB + normA * p15FrobNorm errorB) +
              p15FrobNorm errorA * p15FrobNorm errorB := by
          linarith
        _ ≤ boundA * normB + normA * boundB + boundA * boundB := by
          have hEA_B : p15FrobNorm errorA * normB ≤ boundA * normB :=
            mul_le_mul_of_nonneg_right herrorA hnormB0
          have hA_EB : normA * p15FrobNorm errorB ≤ normA * boundB :=
            mul_le_mul_of_nonneg_left herrorB hnormA0
          have hEA_EB :
              p15FrobNorm errorA * p15FrobNorm errorB ≤
                boundA * boundB :=
            mul_le_mul herrorA herrorB herrorB0 hboundA0
          linarith
    have hsplit :
        run.trace.result - p15MatMul run.A run.B =
          (run.trace.result - p15MatMul Atilde Btilde) +
            (p15MatMul Atilde Btilde - p15MatMul run.A run.B) := by
      abel
    calc
      p15FrobNorm (run.trace.result - p15MatMul run.A run.B) =
          p15FrobNorm
            ((run.trace.result - p15MatMul Atilde Btilde) +
              (p15MatMul Atilde Btilde - p15MatMul run.A run.B)) :=
        congrArg p15FrobNorm hsplit
      _ ≤
          p15FrobNorm (run.trace.result - p15MatMul Atilde Btilde) +
            p15FrobNorm
              (p15MatMul Atilde Btilde - p15MatMul run.A run.B) :=
        p15RectFrobNorm_add_le _ _
      _ ≤ gammaC * p15FrobNorm Atilde * p15FrobNorm Btilde +
            (boundA * normB + normA * boundB + boundA * boundB) :=
        add_le_add hfirst hperturbation
      _ ≤ gammaC * ((normA + boundA) * (normB + boundB)) +
            (boundA * normB + normA * boundB + boundA * boundB) := by
        have hm := mul_le_mul_of_nonneg_left htildeProduct hgammaC0
        have ha := add_le_add_right hm
          (boundA * normB + normA * boundB + boundA * boundB)
        simpa only [mul_assoc, add_comm, add_left_comm, add_assoc] using ha
      _ = gammaC * normA * normB +
            run.epsilon * (1 + gammaC) *
              (run.betaA * normB + normA * run.betaB +
                run.epsilon * run.betaA * run.betaB) := by
        dsimp [boundA, boundB]
        ring
      _ = gammaC * p15FrobNorm run.A * p15FrobNorm run.B +
            run.epsilon * (1 + gammaC) *
              (run.betaA * p15FrobNorm run.B +
                p15FrobNorm run.A * run.betaB +
                run.epsilon * run.betaA * run.betaB) := by
        rfl

end HighamBench
