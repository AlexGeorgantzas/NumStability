import HighamBench.P15Definitions
import NumStability.Source.Higham.Chapter19.Sensitivity.Closure

namespace HighamBench

open scoped BigOperators

private lemma p15FrobNorm_nonneg {m n : ℕ}
    (A : P15RectMatrix m n) :
    0 ≤ p15RectFrobNorm A := by
  exact Real.sqrt_nonneg _

private lemma p15FrobNorm_add_le {m n : ℕ}
    (A B : P15RectMatrix m n) :
    p15RectFrobNorm (A + B) ≤ p15RectFrobNorm A + p15RectFrobNorm B := by
  simpa [p15RectFrobNorm, NumStability.frobNormRect,
    NumStability.frobNormSqRect] using
    (NumStability.frobNormRect_add_le A B)

private lemma p15FrobNorm_sub_le {m n : ℕ}
    (A B : P15RectMatrix m n) :
    p15RectFrobNorm (A - B) ≤ p15RectFrobNorm A + p15RectFrobNorm B := by
  simpa [p15RectFrobNorm, NumStability.frobNormRect,
    NumStability.frobNormSqRect] using
    (NumStability.frobNormRect_sub_le A B)

private lemma p15FrobNorm_mul_le {m n p : ℕ}
    (A : P15RectMatrix m n) (B : P15RectMatrix n p) :
    p15RectFrobNorm (p15RectMatMul A B) ≤
      p15RectFrobNorm A * p15RectFrobNorm B := by
  simpa [p15RectFrobNorm, p15RectMatMul,
    NumStability.frobNormRect, NumStability.frobNormSqRect,
    NumStability.rectMatMul] using
    (NumStability.frobNormRect_rectMatMul_le A B)

private lemma p15FrobNorm_transpose {m n : ℕ}
    (A : P15RectMatrix m n) :
    p15RectFrobNorm (p15RectTranspose A) = p15RectFrobNorm A := by
  simpa [p15RectFrobNorm, p15RectTranspose,
    NumStability.frobNormRect, NumStability.frobNormSqRect,
    NumStability.finiteTranspose] using
    (NumStability.frobNormRect_finiteTranspose A)

private lemma p15OrthonormalColumns.toGramSchmidt {m n : ℕ}
    {Q : P15RectMatrix m n} (hQ : p15OrthonormalColumns Q) :
    NumStability.GramSchmidtOrthonormalColumns Q := by
  intro i j
  simpa [NumStability.rectangularGram, NumStability.matMulRect,
    NumStability.finiteTranspose, NumStability.idMatrix] using hQ i j

private lemma p15FrobNorm_orthonormal_left {m n p : ℕ}
    (Q : P15RectMatrix m n) (A : P15RectMatrix n p)
    (hQ : p15OrthonormalColumns Q) :
    p15RectFrobNorm (p15RectMatMul Q A) = p15RectFrobNorm A := by
  simpa [p15RectFrobNorm, p15RectMatMul,
    NumStability.frobNormRect, NumStability.frobNormSqRect,
    NumStability.rectMatMul] using
    (NumStability.H19Sensitivity.frobNormRect_rectMatMul_eq_of_orthonormal_left
      Q A hQ.toGramSchmidt)

private lemma p15FrobNorm_orthonormal_right {m n p : ℕ}
    (A : P15RectMatrix p n) (Q : P15RectMatrix m n)
    (hQ : p15OrthonormalColumns Q) :
    p15RectFrobNorm (p15RectMatMul A (p15RectTranspose Q)) =
      p15RectFrobNorm A := by
  rw [← p15FrobNorm_transpose]
  have hprod :
      p15RectTranspose (p15RectMatMul A (p15RectTranspose Q)) =
        p15RectMatMul Q (p15RectTranspose A) := by
    ext i j
    simp only [p15RectTranspose, p15RectMatMul]
    apply Finset.sum_congr rfl
    intro k _
    ring
  rw [hprod, p15FrobNorm_orthonormal_left Q (p15RectTranspose A) hQ]
  exact p15FrobNorm_transpose A

private lemma p15FrobNorm_orthonormal {m n : ℕ}
    (Q : P15RectMatrix m n) (hQ : p15OrthonormalColumns Q) :
    p15RectFrobNorm Q = Real.sqrt (n : ℝ) := by
  simpa [p15RectFrobNorm, NumStability.frobNormRect,
    NumStability.frobNormSqRect] using
    (NumStability.H19Sensitivity.frobNormRect_eq_sqrt_nat_of_orthonormal
      hQ.toGramSchmidt)

private lemma p15RectMatMul_assoc {m n p q : ℕ}
    (A : P15RectMatrix m n) (B : P15RectMatrix n p)
    (C : P15RectMatrix p q) :
    p15RectMatMul (p15RectMatMul A B) C =
      p15RectMatMul A (p15RectMatMul B C) := by
  simpa [p15RectMatMul, NumStability.rectMatMul] using
    (NumStability.rectMatMul_assoc A B C)

private lemma p15RectMatMul_add_left {m n p : ℕ}
    (A B : P15RectMatrix m n) (C : P15RectMatrix n p) :
    p15RectMatMul (A + B) C =
      p15RectMatMul A C + p15RectMatMul B C := by
  simpa [p15RectMatMul, NumStability.rectMatMul] using
    (NumStability.rectMatMul_add_left A B C)

private lemma p15RectMatMul_add_right {m n p : ℕ}
    (A : P15RectMatrix m n) (B C : P15RectMatrix n p) :
    p15RectMatMul A (B + C) =
      p15RectMatMul A B + p15RectMatMul A C := by
  simpa [p15RectMatMul, NumStability.rectMatMul] using
    (NumStability.rectMatMul_add_right A B C)

private lemma p15GammaReal_nonneg {k u : ℝ}
    (hk : 0 ≤ k) (hu : 0 ≤ u) (hvalid : k * u < 1) :
    0 ≤ p15GammaReal k u := by
  unfold p15GammaReal
  exact div_nonneg (mul_nonneg hk hu) (sub_nonneg.mpr hvalid.le)

private lemma p15_scaled_gamma_le {R D s u : ℝ}
    (hR : 0 ≤ R) (hu : 0 ≤ u) (hs : 1 ≤ s)
    (hD : D = R * s) (hvalid : D * u < 1) :
    p15GammaReal R u * s ≤ p15GammaReal D u := by
  have hD0 : 0 ≤ D := by rw [hD]; positivity
  have hRD : R ≤ D := by
    rw [hD]
    nlinarith [mul_nonneg hR (sub_nonneg.mpr hs)]
  have hRu : R * u ≤ D * u :=
    mul_le_mul_of_nonneg_right hRD hu
  have hdenR : 0 < 1 - R * u := by linarith
  have hdenD : 0 < 1 - D * u := by linarith
  have heq :
      p15GammaReal R u * s = (D * u) / (1 - R * u) := by
    unfold p15GammaReal
    field_simp [ne_of_gt hdenR]
    rw [hD]
    ring
  rw [heq]
  unfold p15GammaReal
  rw [div_le_div_iff₀ hdenR hdenD]
  have hn : 0 ≤ D * u := mul_nonneg hD0 hu
  have hgap : 0 ≤ (D - R) * u :=
    mul_nonneg (sub_nonneg.mpr hRD) hu
  nlinarith [mul_nonneg hn hgap]

private lemma p15_gamma_two_stage_collapse {B D u : ℝ}
    (hB : 0 ≤ B) (hD : 0 ≤ D) (hu : 0 ≤ u)
    (hvalid : (B + 2 * D) * u < 1) :
    let gB := p15GammaReal B u
    let gD := p15GammaReal D u
    gB + gD * (1 + gB) + gD * (1 + gD) * (1 + gB) ≤
      p15GammaReal (B + 2 * D) u := by
  dsimp
  have hBu : B * u ≤ (B + 2 * D) * u := by
    apply mul_le_mul_of_nonneg_right _ hu
    nlinarith
  have hDu : D * u ≤ (B + 2 * D) * u := by
    apply mul_le_mul_of_nonneg_right _ hu
    nlinarith
  have hdenB : 0 < 1 - B * u := by linarith
  have hdenD : 0 < 1 - D * u := by linarith
  have hdenC : 0 < 1 - (B + 2 * D) * u := by linarith
  have hdenProd : 0 < (1 - B * u) * (1 - D * u) ^ 2 := by positivity
  have hpoly :
      1 - (B + 2 * D) * u ≤
        (1 - B * u) * (1 - D * u) ^ 2 := by
    have h1 : 0 ≤ 1 - B * u := hdenB.le
    have hterm1 : 0 ≤ D ^ 2 * u ^ 2 * (1 - B * u) := by positivity
    have hterm2 : 0 ≤ 2 * B * D * u ^ 2 := by positivity
    nlinarith
  have hrecip :
      1 / ((1 - B * u) * (1 - D * u) ^ 2) ≤
        1 / (1 - (B + 2 * D) * u) := by
    rw [div_le_div_iff₀ hdenProd hdenC]
    simpa using hpoly
  have hlhs :
      p15GammaReal B u +
          p15GammaReal D u * (1 + p15GammaReal B u) +
          p15GammaReal D u * (1 + p15GammaReal D u) *
            (1 + p15GammaReal B u) =
        1 / ((1 - B * u) * (1 - D * u) ^ 2) - 1 := by
    have honeB :
        1 + p15GammaReal B u = 1 / (1 - B * u) := by
      unfold p15GammaReal
      field_simp [ne_of_gt hdenB]
      ring
    have honeD :
        1 + p15GammaReal D u = 1 / (1 - D * u) := by
      unfold p15GammaReal
      field_simp [ne_of_gt hdenD]
      ring
    calc
      p15GammaReal B u +
            p15GammaReal D u * (1 + p15GammaReal B u) +
            p15GammaReal D u * (1 + p15GammaReal D u) *
              (1 + p15GammaReal B u) =
          (1 + p15GammaReal B u) *
              (1 + p15GammaReal D u) ^ 2 - 1 := by ring
      _ = 1 / ((1 - B * u) * (1 - D * u) ^ 2) - 1 := by
        rw [honeB, honeD]
        field_simp [ne_of_gt hdenB, ne_of_gt hdenD]
  have hrhs :
      p15GammaReal (B + 2 * D) u =
        1 / (1 - (B + 2 * D) * u) - 1 := by
    unfold p15GammaReal
    field_simp [ne_of_gt hdenC]
    ring
  rw [hlhs, hrhs]
  linarith

private lemma p15_gamma_cost_bound (b r : ℕ) {u : ℝ}
    (hu : 0 ≤ u)
    (hvalid : p15LowRankMatMulCost b r * u < 1) :
    let gb := p15GammaReal (b : ℝ) u
    let q := p15GammaReal (r : ℝ) u * Real.sqrt (r : ℝ)
    let gc := p15GammaReal (p15LowRankMatMulCost b r) u
    gb + q * (1 + gb) + q * (1 + q) * (1 + gb) ≤ gc := by
  dsimp
  let R : ℝ := (r : ℝ)
  let s : ℝ := Real.sqrt R
  let D : ℝ := R * s
  have hR : 0 ≤ R := by positivity
  have hs0 : 0 ≤ s := Real.sqrt_nonneg _
  have hD0 : 0 ≤ D := mul_nonneg hR hs0
  have hcost : p15LowRankMatMulCost b r = (b : ℝ) + 2 * D := by
    simp [p15LowRankMatMulCost, D, R, s]
    ring
  by_cases hr : r = 0
  · subst r
    simp [p15LowRankMatMulCost, p15GammaReal]
  · have hrpos : 0 < r := Nat.pos_of_ne_zero hr
    have hrone : 1 ≤ r := hrpos
    have hRone : 1 ≤ R := by
      dsimp [R]
      exact_mod_cast hrone
    have hsone : 1 ≤ s := by
      rw [show (1 : ℝ) = Real.sqrt 1 by norm_num]
      exact Real.sqrt_le_sqrt hRone
    have hDvalid : D * u < 1 := by
      have hle : D ≤ (b : ℝ) + 2 * D := by
        have hb0 : 0 ≤ (b : ℝ) := by positivity
        nlinarith
      exact lt_of_le_of_lt (mul_le_mul_of_nonneg_right hle hu) (by simpa [hcost] using hvalid)
    have hq :
        p15GammaReal R u * s ≤ p15GammaReal D u :=
      p15_scaled_gamma_le hR hu hsone rfl hDvalid
    have hB0 : 0 ≤ (b : ℝ) := by positivity
    have hcollapse :=
      p15_gamma_two_stage_collapse hB0 hD0 hu (by simpa [hcost] using hvalid)
    have hBvalid : (b : ℝ) * u < 1 := by
      have hle : (b : ℝ) ≤ (b : ℝ) + 2 * D := by
        nlinarith [hD0]
      exact lt_of_le_of_lt (mul_le_mul_of_nonneg_right hle hu) (by simpa [hcost] using hvalid)
    have hgB0 : 0 ≤ p15GammaReal (b : ℝ) u :=
      p15GammaReal_nonneg hB0 hu hBvalid
    have hq0 : 0 ≤ p15GammaReal R u * s := by
      have hRD : R ≤ D := by
        dsimp [D]
        nlinarith [mul_nonneg hR (sub_nonneg.mpr hsone)]
      have hRvalid : R * u < 1 :=
        lt_of_le_of_lt (mul_le_mul_of_nonneg_right hRD hu) hDvalid
      apply mul_nonneg
      · exact p15GammaReal_nonneg hR hu hRvalid
      · exact hs0
    have hgD0 : 0 ≤ p15GammaReal D u :=
      p15GammaReal_nonneg hD0 hu hDvalid
    have hlin :
        p15GammaReal R u * s * (1 + p15GammaReal (b : ℝ) u) ≤
          p15GammaReal D u * (1 + p15GammaReal (b : ℝ) u) :=
      mul_le_mul_of_nonneg_right hq (by positivity)
    have hquad0 :
        p15GammaReal R u * s * (1 + p15GammaReal R u * s) ≤
          p15GammaReal D u * (1 + p15GammaReal D u) := by
      exact mul_le_mul hq (by linarith) (by linarith) hgD0
    have hquad :
        (p15GammaReal R u * s * (1 + p15GammaReal R u * s)) *
            (1 + p15GammaReal (b : ℝ) u) ≤
          (p15GammaReal D u * (1 + p15GammaReal D u)) *
            (1 + p15GammaReal (b : ℝ) u) :=
      mul_le_mul_of_nonneg_right hquad0 (by positivity)
    rw [hcost]
    dsimp [R, s] at hlin hquad ⊢
    linarith

private lemma p15_b_le_cost (b r : ℕ) :
    (b : ℝ) ≤ p15LowRankMatMulCost b r := by
  unfold p15LowRankMatMulCost
  have h : 0 ≤ 2 * (r : ℝ) * Real.sqrt (r : ℝ) := by positivity
  linarith

private lemma p15_r_le_cost (b r : ℕ) :
    (r : ℝ) ≤ p15LowRankMatMulCost b r := by
  unfold p15LowRankMatMulCost
  by_cases hr : r = 0
  · subst r
    simp
  · have hrone : (1 : ℝ) ≤ (r : ℝ) := by
      exact_mod_cast (Nat.one_le_iff_ne_zero.mpr hr)
    have hsone : (1 : ℝ) ≤ Real.sqrt (r : ℝ) := by
      rw [show (1 : ℝ) = Real.sqrt 1 by norm_num]
      exact Real.sqrt_le_sqrt hrone
    have hb0 : 0 ≤ (b : ℝ) := by positivity
    have hr0 : 0 ≤ (r : ℝ) := by positivity
    nlinarith [mul_nonneg hr0 (sub_nonneg.mpr hsone)]

set_option maxHeartbeats 2000000 in
private lemma p15_trace_error {b r : ℕ} {u : ℝ}
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
  let Atilde := p15LowRankMatrix XA YA
  let Btilde := p15LowRankMatrix YB XB
  let M := p15RectMatMul (p15RectTranspose YA) YB
  let P := p15FrobNorm Atilde * p15FrobNorm Btilde
  let gb := p15GammaReal (b : ℝ) u
  let gr := p15GammaReal (r : ℝ) u
  let s := Real.sqrt (r : ℝ)
  let q := gr * s
  let gc := p15GammaReal (p15LowRankMatMulCost b r) u
  have hAt : p15FrobNorm Atilde = p15RectFrobNorm YA := by
    dsimp [Atilde, p15LowRankMatrix, p15FrobNorm]
    exact p15FrobNorm_orthonormal_left XA (p15RectTranspose YA) hXA |>.trans
      (p15FrobNorm_transpose YA)
  have hBt : p15FrobNorm Btilde = p15RectFrobNorm YB := by
    dsimp [Btilde, p15LowRankMatrix, p15FrobNorm]
    exact p15FrobNorm_orthonormal_right YB XB hXB
  have hP0 : 0 ≤ P := by
    dsimp [P]
    exact mul_nonneg (p15FrobNorm_nonneg _) (p15FrobNorm_nonneg _)
  have hbvalid : (b : ℝ) * u < 1 :=
    lt_of_le_of_lt
      (mul_le_mul_of_nonneg_right (p15_b_le_cost b r) hu) hvalid
  have hrvalid : (r : ℝ) * u < 1 :=
    lt_of_le_of_lt
      (mul_le_mul_of_nonneg_right (p15_r_le_cost b r) hu) hvalid
  have hgb0 : 0 ≤ gb := by
    exact p15GammaReal_nonneg (by positivity) hu hbvalid
  have hgr0 : 0 ≤ gr := by
    exact p15GammaReal_nonneg (by positivity) hu hrvalid
  have hs0 : 0 ≤ s := Real.sqrt_nonneg _
  have hq0 : 0 ≤ q := mul_nonneg hgr0 hs0
  have hXA_norm : p15RectFrobNorm XA = s := by
    exact p15FrobNorm_orthonormal XA hXA
  have hXB_norm : p15RectFrobNorm (p15RectTranspose XB) = s := by
    rw [p15FrobNorm_transpose, p15FrobNorm_orthonormal XB hXB]
  have hM : p15RectFrobNorm M ≤ P := by
    calc
      p15RectFrobNorm M ≤
          p15RectFrobNorm (p15RectTranspose YA) * p15RectFrobNorm YB := by
        exact p15FrobNorm_mul_le _ _
      _ = P := by rw [p15FrobNorm_transpose, ← hAt, ← hBt]
  have hExact :
      p15MatMul Atilde Btilde =
        p15RectMatMul (p15RectMatMul XA M) (p15RectTranspose XB) := by
    dsimp [Atilde, Btilde, M, p15LowRankMatrix, p15MatMul]
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
  have hcost :
      gb + q * (1 + gb) + q * (1 + q) * (1 + gb) ≤ gc := by
    exact p15_gamma_cost_bound b r hu hvalid
  cases trace with
  | leftAssociated middleStage leftStage finalStage =>
      have hMiddleErr :
          p15RectFrobNorm middleStage.error ≤ gb * P := by
        calc
          p15RectFrobNorm middleStage.error ≤
              gb * p15RectFrobNorm (p15RectTranspose YA) *
                p15RectFrobNorm YB := middleStage.error_le
          _ = gb * P := by
            rw [p15FrobNorm_transpose, ← hAt, ← hBt]
            dsimp [P]
            ring
      have hMiddleResult :
          p15RectFrobNorm middleStage.result ≤ (1 + gb) * P := by
        calc
          p15RectFrobNorm middleStage.result ≤
              p15RectFrobNorm M + p15RectFrobNorm middleStage.error := by
            simpa [P15RoundedMatMulStage.result, M] using
              (p15FrobNorm_add_le M middleStage.error)
          _ ≤ P + gb * P := add_le_add hM hMiddleErr
          _ = (1 + gb) * P := by ring
      have hLeftErrRaw :
          p15RectFrobNorm leftStage.error ≤
            q * p15RectFrobNorm middleStage.result := by
        calc
          p15RectFrobNorm leftStage.error ≤
              gr * p15RectFrobNorm XA *
                p15RectFrobNorm middleStage.result := leftStage.error_le
          _ = q * p15RectFrobNorm middleStage.result := by
            rw [hXA_norm]
      have hLeftErr :
          p15RectFrobNorm leftStage.error ≤ q * (1 + gb) * P := by
        calc
          p15RectFrobNorm leftStage.error ≤
              q * p15RectFrobNorm middleStage.result := hLeftErrRaw
          _ ≤ q * ((1 + gb) * P) :=
            mul_le_mul_of_nonneg_left hMiddleResult hq0
          _ = q * (1 + gb) * P := by ring
      have hLeftResult :
          p15RectFrobNorm leftStage.result ≤
            (1 + q) * (1 + gb) * P := by
        calc
          p15RectFrobNorm leftStage.result ≤
              p15RectFrobNorm
                  (p15RectMatMul XA middleStage.result) +
                p15RectFrobNorm leftStage.error := by
            simpa [P15RoundedMatMulStage.result] using
              (p15FrobNorm_add_le
                (p15RectMatMul XA middleStage.result) leftStage.error)
          _ = p15RectFrobNorm middleStage.result +
                p15RectFrobNorm leftStage.error := by
            rw [p15FrobNorm_orthonormal_left XA middleStage.result hXA]
          _ ≤ p15RectFrobNorm middleStage.result +
                q * p15RectFrobNorm middleStage.result :=
            add_le_add (le_refl _) hLeftErrRaw
          _ = (1 + q) * p15RectFrobNorm middleStage.result := by ring
          _ ≤ (1 + q) * ((1 + gb) * P) :=
            mul_le_mul_of_nonneg_left hMiddleResult (by positivity)
          _ = (1 + q) * (1 + gb) * P := by ring
      have hFinalErr :
          p15RectFrobNorm finalStage.error ≤
            q * (1 + q) * (1 + gb) * P := by
        calc
          p15RectFrobNorm finalStage.error ≤
              gr * p15RectFrobNorm leftStage.result *
                p15RectFrobNorm (p15RectTranspose XB) := finalStage.error_le
          _ = q * p15RectFrobNorm leftStage.result := by
            rw [hXB_norm]
            ring
          _ ≤ q * ((1 + q) * (1 + gb) * P) :=
            mul_le_mul_of_nonneg_left hLeftResult hq0
          _ = q * (1 + q) * (1 + gb) * P := by ring
      let T0 : P15Matrix b :=
        p15RectMatMul (p15RectMatMul XA middleStage.error)
          (p15RectTranspose XB)
      let T1 : P15Matrix b :=
        p15RectMatMul leftStage.error (p15RectTranspose XB)
      have hdiff :
          finalStage.result - p15MatMul Atilde Btilde =
            T0 + T1 + finalStage.error := by
        rw [hExact]
        change
          p15RectMatMul
                (p15RectMatMul XA (M + middleStage.error) + leftStage.error)
                (p15RectTranspose XB) + finalStage.error -
              p15RectMatMul (p15RectMatMul XA M) (p15RectTranspose XB) = _
        rw [p15RectMatMul_add_right XA M middleStage.error]
        rw [p15RectMatMul_add_left
          (p15RectMatMul XA M + p15RectMatMul XA middleStage.error)
          leftStage.error (p15RectTranspose XB)]
        rw [p15RectMatMul_add_left
          (p15RectMatMul XA M) (p15RectMatMul XA middleStage.error)
          (p15RectTranspose XB)]
        abel
      change p15FrobNorm
          (finalStage.result -
            p15MatMul (p15LowRankMatrix XA YA) (p15LowRankMatrix YB XB)) ≤
          p15GammaReal (p15LowRankMatMulCost b r) u *
            p15FrobNorm (p15LowRankMatrix XA YA) *
            p15FrobNorm (p15LowRankMatrix YB XB)
      change p15FrobNorm (finalStage.result - p15MatMul Atilde Btilde) ≤
        gc * p15FrobNorm Atilde * p15FrobNorm Btilde
      rw [hdiff]
      have hnormMiddle :
          p15RectFrobNorm T0 = p15RectFrobNorm middleStage.error := by
        dsimp [T0]
        rw [p15FrobNorm_orthonormal_right
          (p15RectMatMul XA middleStage.error) XB hXB]
        exact p15FrobNorm_orthonormal_left XA middleStage.error hXA
      have hnormLeft :
          p15RectFrobNorm T1 = p15RectFrobNorm leftStage.error := by
        dsimp [T1]
        exact p15FrobNorm_orthonormal_right leftStage.error XB hXB
      have htri :
          p15FrobNorm (T0 + T1 + finalStage.error) ≤
            (p15RectFrobNorm T0 + p15RectFrobNorm T1) +
              p15RectFrobNorm finalStage.error := by
        calc
          p15FrobNorm (T0 + T1 + finalStage.error) ≤
              p15RectFrobNorm (T0 + T1) +
                p15RectFrobNorm finalStage.error :=
            p15FrobNorm_add_le (T0 + T1) finalStage.error
          _ ≤ (p15RectFrobNorm T0 + p15RectFrobNorm T1) +
                p15RectFrobNorm finalStage.error :=
            add_le_add (p15FrobNorm_add_le T0 T1) (le_refl _)
      calc
        p15FrobNorm (T0 + T1 + finalStage.error) ≤
            (p15RectFrobNorm T0 + p15RectFrobNorm T1) +
              p15RectFrobNorm finalStage.error := htri
        _ = p15RectFrobNorm middleStage.error +
              p15RectFrobNorm leftStage.error +
              p15RectFrobNorm finalStage.error := by
          rw [hnormMiddle, hnormLeft]
        _ ≤ gb * P + q * (1 + gb) * P +
              q * (1 + q) * (1 + gb) * P := by
          exact add_le_add (add_le_add hMiddleErr hLeftErr) hFinalErr
        _ = (gb + q * (1 + gb) + q * (1 + q) * (1 + gb)) * P := by
          ring
        _ ≤ gc * P := mul_le_mul_of_nonneg_right hcost hP0
        _ = gc * p15FrobNorm Atilde * p15FrobNorm Btilde := by
          dsimp [P]
          ring
  | rightAssociated middleStage rightStage finalStage =>
      have hMiddleErr :
          p15RectFrobNorm middleStage.error ≤ gb * P := by
        calc
          p15RectFrobNorm middleStage.error ≤
              gb * p15RectFrobNorm (p15RectTranspose YA) *
                p15RectFrobNorm YB := middleStage.error_le
          _ = gb * P := by
            rw [p15FrobNorm_transpose, ← hAt, ← hBt]
            dsimp [P]
            ring
      have hMiddleResult :
          p15RectFrobNorm middleStage.result ≤ (1 + gb) * P := by
        calc
          p15RectFrobNorm middleStage.result ≤
              p15RectFrobNorm M + p15RectFrobNorm middleStage.error := by
            simpa [P15RoundedMatMulStage.result, M] using
              (p15FrobNorm_add_le M middleStage.error)
          _ ≤ P + gb * P := add_le_add hM hMiddleErr
          _ = (1 + gb) * P := by ring
      have hRightErrRaw :
          p15RectFrobNorm rightStage.error ≤
            q * p15RectFrobNorm middleStage.result := by
        calc
          p15RectFrobNorm rightStage.error ≤
              gr * p15RectFrobNorm middleStage.result *
                p15RectFrobNorm (p15RectTranspose XB) := rightStage.error_le
          _ = q * p15RectFrobNorm middleStage.result := by
            rw [hXB_norm]
            ring
      have hRightErr :
          p15RectFrobNorm rightStage.error ≤ q * (1 + gb) * P := by
        calc
          p15RectFrobNorm rightStage.error ≤
              q * p15RectFrobNorm middleStage.result := hRightErrRaw
          _ ≤ q * ((1 + gb) * P) :=
            mul_le_mul_of_nonneg_left hMiddleResult hq0
          _ = q * (1 + gb) * P := by ring
      have hRightResult :
          p15RectFrobNorm rightStage.result ≤
            (1 + q) * (1 + gb) * P := by
        calc
          p15RectFrobNorm rightStage.result ≤
              p15RectFrobNorm
                  (p15RectMatMul middleStage.result (p15RectTranspose XB)) +
                p15RectFrobNorm rightStage.error := by
            simpa [P15RoundedMatMulStage.result] using
              (p15FrobNorm_add_le
                (p15RectMatMul middleStage.result (p15RectTranspose XB))
                rightStage.error)
          _ = p15RectFrobNorm middleStage.result +
                p15RectFrobNorm rightStage.error := by
            rw [p15FrobNorm_orthonormal_right middleStage.result XB hXB]
          _ ≤ p15RectFrobNorm middleStage.result +
                q * p15RectFrobNorm middleStage.result :=
            add_le_add (le_refl _) hRightErrRaw
          _ = (1 + q) * p15RectFrobNorm middleStage.result := by ring
          _ ≤ (1 + q) * ((1 + gb) * P) :=
            mul_le_mul_of_nonneg_left hMiddleResult (by positivity)
          _ = (1 + q) * (1 + gb) * P := by ring
      have hFinalErr :
          p15RectFrobNorm finalStage.error ≤
            q * (1 + q) * (1 + gb) * P := by
        calc
          p15RectFrobNorm finalStage.error ≤
              gr * p15RectFrobNorm XA *
                p15RectFrobNorm rightStage.result := finalStage.error_le
          _ = q * p15RectFrobNorm rightStage.result := by
            rw [hXA_norm]
          _ ≤ q * ((1 + q) * (1 + gb) * P) :=
            mul_le_mul_of_nonneg_left hRightResult hq0
          _ = q * (1 + q) * (1 + gb) * P := by ring
      let T0 : P15Matrix b :=
        p15RectMatMul XA
          (p15RectMatMul middleStage.error (p15RectTranspose XB))
      let T1 : P15Matrix b := p15RectMatMul XA rightStage.error
      have hdiff :
          finalStage.result - p15MatMul Atilde Btilde =
            T0 + T1 + finalStage.error := by
        rw [hExact]
        change
          p15RectMatMul XA
                (p15RectMatMul (M + middleStage.error)
                    (p15RectTranspose XB) + rightStage.error) +
              finalStage.error -
              p15RectMatMul (p15RectMatMul XA M) (p15RectTranspose XB) = _
        rw [p15RectMatMul_add_left M middleStage.error
          (p15RectTranspose XB)]
        rw [p15RectMatMul_add_right XA
          (p15RectMatMul M (p15RectTranspose XB) +
            p15RectMatMul middleStage.error (p15RectTranspose XB))
          rightStage.error]
        rw [p15RectMatMul_add_right XA
          (p15RectMatMul M (p15RectTranspose XB))
          (p15RectMatMul middleStage.error (p15RectTranspose XB))]
        rw [p15RectMatMul_assoc XA M (p15RectTranspose XB)]
        abel
      change p15FrobNorm
          (finalStage.result -
            p15MatMul (p15LowRankMatrix XA YA) (p15LowRankMatrix YB XB)) ≤
          p15GammaReal (p15LowRankMatMulCost b r) u *
            p15FrobNorm (p15LowRankMatrix XA YA) *
            p15FrobNorm (p15LowRankMatrix YB XB)
      change p15FrobNorm (finalStage.result - p15MatMul Atilde Btilde) ≤
        gc * p15FrobNorm Atilde * p15FrobNorm Btilde
      rw [hdiff]
      have hnormMiddle :
          p15RectFrobNorm T0 = p15RectFrobNorm middleStage.error := by
        dsimp [T0]
        rw [p15FrobNorm_orthonormal_left XA _ hXA]
        exact p15FrobNorm_orthonormal_right middleStage.error XB hXB
      have hnormRight :
          p15RectFrobNorm T1 = p15RectFrobNorm rightStage.error := by
        dsimp [T1]
        exact p15FrobNorm_orthonormal_left XA rightStage.error hXA
      have htri :
          p15FrobNorm (T0 + T1 + finalStage.error) ≤
            (p15RectFrobNorm T0 + p15RectFrobNorm T1) +
              p15RectFrobNorm finalStage.error := by
        calc
          p15FrobNorm (T0 + T1 + finalStage.error) ≤
              p15RectFrobNorm (T0 + T1) +
                p15RectFrobNorm finalStage.error :=
            p15FrobNorm_add_le (T0 + T1) finalStage.error
          _ ≤ (p15RectFrobNorm T0 + p15RectFrobNorm T1) +
                p15RectFrobNorm finalStage.error :=
            add_le_add (p15FrobNorm_add_le T0 T1) (le_refl _)
      calc
        p15FrobNorm (T0 + T1 + finalStage.error) ≤
            (p15RectFrobNorm T0 + p15RectFrobNorm T1) +
              p15RectFrobNorm finalStage.error := htri
        _ = p15RectFrobNorm middleStage.error +
              p15RectFrobNorm rightStage.error +
              p15RectFrobNorm finalStage.error := by
          rw [hnormMiddle, hnormRight]
        _ ≤ gb * P + q * (1 + gb) * P +
              q * (1 + q) * (1 + gb) * P := by
          exact add_le_add (add_le_add hMiddleErr hRightErr) hFinalErr
        _ = (gb + q * (1 + gb) + q * (1 + q) * (1 + gb)) * P := by
          ring
        _ ≤ gc * P := mul_le_mul_of_nonneg_right hcost hP0
        _ = gc * p15FrobNorm Atilde * p15FrobNorm Btilde := by
          dsimp [P]
          ring

set_option maxHeartbeats 1000000 in
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
    exact p15_trace_error run.unitRoundoff_nonneg run.gamma_valid
      run.xA_orthonormal run.xB_orthonormal run.trace
  refine ⟨hfirst, ?_⟩
  let x := run.epsilon * run.betaA
  let y := run.epsilon * run.betaB
  have hx0 : 0 ≤ x := by
    exact le_trans (p15FrobNorm_nonneg run.approximationErrorA)
      (by simpa [x] using run.approximationErrorA_le)
  have hy0 : 0 ≤ y := by
    exact le_trans (p15FrobNorm_nonneg run.approximationErrorB)
      (by simpa [y] using run.approximationErrorB_le)
  have hcost0 : 0 ≤ p15LowRankMatMulCost b r :=
    le_trans (by positivity) (p15_b_le_cost b r)
  have hgamma0 : 0 ≤ gammaC := by
    exact p15GammaReal_nonneg hcost0 run.unitRoundoff_nonneg run.gamma_valid
  have hAtNorm :
      p15FrobNorm Atilde ≤ p15FrobNorm run.A + x := by
    rw [show Atilde = run.A + run.approximationErrorA by
      exact run.approximationA_eq]
    exact le_trans (p15FrobNorm_add_le run.A run.approximationErrorA)
      (add_le_add (le_refl _) (by simpa [x] using run.approximationErrorA_le))
  have hBtNorm :
      p15FrobNorm Btilde ≤ p15FrobNorm run.B + y := by
    rw [show Btilde = run.B + run.approximationErrorB by
      exact run.approximationB_eq]
    exact le_trans (p15FrobNorm_add_le run.B run.approximationErrorB)
      (add_le_add (le_refl _) (by simpa [y] using run.approximationErrorB_le))
  have hAtBtNorm :
      p15FrobNorm Atilde * p15FrobNorm Btilde ≤
        (p15FrobNorm run.A + x) * (p15FrobNorm run.B + y) := by
    exact mul_le_mul hAtNorm hBtNorm (p15FrobNorm_nonneg _)
      (add_nonneg (p15FrobNorm_nonneg _) hx0)
  let F := run.trace.result - p15MatMul Atilde Btilde
  let G := p15MatMul Atilde Btilde - p15MatMul run.A run.B
  have hsplit :
      run.trace.result - p15MatMul run.A run.B = F + G := by
    dsimp [F, G]
    abel
  have hGdecomp :
      G = p15MatMul run.approximationErrorA run.B +
          p15MatMul run.A run.approximationErrorB +
          p15MatMul run.approximationErrorA run.approximationErrorB := by
    dsimp [G, Atilde, Btilde]
    rw [run.approximationA_eq, run.approximationB_eq]
    change
      p15RectMatMul (run.A + run.approximationErrorA)
          (run.B + run.approximationErrorB) -
        p15RectMatMul run.A run.B =
          p15RectMatMul run.approximationErrorA run.B +
            p15RectMatMul run.A run.approximationErrorB +
            p15RectMatMul run.approximationErrorA run.approximationErrorB
    rw [p15RectMatMul_add_left]
    rw [p15RectMatMul_add_right run.A]
    rw [p15RectMatMul_add_right run.approximationErrorA]
    abel
  have hEAB :
      p15FrobNorm (p15MatMul run.approximationErrorA run.B) ≤
        x * p15FrobNorm run.B := by
    calc
      p15FrobNorm (p15MatMul run.approximationErrorA run.B) ≤
          p15FrobNorm run.approximationErrorA * p15FrobNorm run.B :=
        p15FrobNorm_mul_le _ _
      _ ≤ x * p15FrobNorm run.B :=
        mul_le_mul_of_nonneg_right
          (by simpa [x] using run.approximationErrorA_le)
          (p15FrobNorm_nonneg _)
  have hAEB :
      p15FrobNorm (p15MatMul run.A run.approximationErrorB) ≤
        p15FrobNorm run.A * y := by
    calc
      p15FrobNorm (p15MatMul run.A run.approximationErrorB) ≤
          p15FrobNorm run.A * p15FrobNorm run.approximationErrorB :=
        p15FrobNorm_mul_le _ _
      _ ≤ p15FrobNorm run.A * y :=
        mul_le_mul_of_nonneg_left
          (by simpa [y] using run.approximationErrorB_le)
          (p15FrobNorm_nonneg _)
  have hEAEB :
      p15FrobNorm
          (p15MatMul run.approximationErrorA run.approximationErrorB) ≤
        x * y := by
    calc
      p15FrobNorm
            (p15MatMul run.approximationErrorA run.approximationErrorB) ≤
          p15FrobNorm run.approximationErrorA *
            p15FrobNorm run.approximationErrorB := p15FrobNorm_mul_le _ _
      _ ≤ x * y := by
        exact mul_le_mul
          (by simpa [x] using run.approximationErrorA_le)
          (by simpa [y] using run.approximationErrorB_le)
          (p15FrobNorm_nonneg _) hx0
  have hG :
      p15FrobNorm G ≤
        x * p15FrobNorm run.B + p15FrobNorm run.A * y + x * y := by
    rw [hGdecomp]
    calc
      p15FrobNorm
            (p15MatMul run.approximationErrorA run.B +
                p15MatMul run.A run.approximationErrorB +
              p15MatMul run.approximationErrorA run.approximationErrorB) ≤
          (p15FrobNorm (p15MatMul run.approximationErrorA run.B) +
            p15FrobNorm (p15MatMul run.A run.approximationErrorB)) +
            p15FrobNorm
              (p15MatMul run.approximationErrorA run.approximationErrorB) := by
        exact le_trans
          (p15FrobNorm_add_le
            (p15MatMul run.approximationErrorA run.B +
              p15MatMul run.A run.approximationErrorB)
            (p15MatMul run.approximationErrorA run.approximationErrorB))
          (add_le_add
            (p15FrobNorm_add_le
              (p15MatMul run.approximationErrorA run.B)
              (p15MatMul run.A run.approximationErrorB))
            (le_refl _))
      _ ≤ x * p15FrobNorm run.B + p15FrobNorm run.A * y + x * y :=
        add_le_add (add_le_add hEAB hAEB) hEAEB
  rw [hsplit]
  calc
    p15FrobNorm (F + G) ≤ p15FrobNorm F + p15FrobNorm G :=
      p15FrobNorm_add_le F G
    _ ≤ gammaC * p15FrobNorm Atilde * p15FrobNorm Btilde +
          (x * p15FrobNorm run.B + p15FrobNorm run.A * y + x * y) :=
      add_le_add hfirst hG
    _ ≤ gammaC *
            ((p15FrobNorm run.A + x) * (p15FrobNorm run.B + y)) +
          (x * p15FrobNorm run.B + p15FrobNorm run.A * y + x * y) := by
      exact add_le_add
        (calc
          gammaC * p15FrobNorm Atilde * p15FrobNorm Btilde =
              gammaC * (p15FrobNorm Atilde * p15FrobNorm Btilde) := by ring
          _ ≤ gammaC *
                ((p15FrobNorm run.A + x) * (p15FrobNorm run.B + y)) :=
            mul_le_mul_of_nonneg_left hAtBtNorm hgamma0)
        (le_refl _)
    _ = gammaC * p15FrobNorm run.A * p15FrobNorm run.B +
          run.epsilon * (1 + gammaC) *
            (run.betaA * p15FrobNorm run.B +
              p15FrobNorm run.A * run.betaB +
              run.epsilon * run.betaA * run.betaB) := by
      dsimp [x, y]
      ring

end HighamBench
