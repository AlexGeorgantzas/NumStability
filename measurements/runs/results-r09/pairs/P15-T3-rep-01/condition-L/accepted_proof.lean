import HighamBench.P15Definitions
import NumStability.Source.Higham.Chapter19.Sensitivity.Closure

namespace HighamBench

open scoped BigOperators

open NumStability

private lemma p15_frob_nonneg {m n : ℕ} (A : P15RectMatrix m n) :
    0 ≤ p15RectFrobNorm A := by
  simpa [p15RectFrobNorm, NumStability.frobNormRect,
    NumStability.frobNormSqRect] using NumStability.frobNormRect_nonneg A

private lemma p15_frob_add_le {m n : ℕ}
    (A B : P15RectMatrix m n) :
    p15RectFrobNorm (A + B) ≤ p15RectFrobNorm A + p15RectFrobNorm B := by
  simpa [p15RectFrobNorm, NumStability.frobNormRect,
    NumStability.frobNormSqRect] using NumStability.frobNormRect_add_le A B

private lemma p15_frob_sub_le {m n : ℕ}
    (A B : P15RectMatrix m n) :
    p15RectFrobNorm (A - B) ≤ p15RectFrobNorm A + p15RectFrobNorm B := by
  simpa [p15RectFrobNorm, NumStability.frobNormRect,
    NumStability.frobNormSqRect] using NumStability.frobNormRect_sub_le A B

private lemma p15_frob_mul_le {m n p : ℕ}
    (A : P15RectMatrix m n) (B : P15RectMatrix n p) :
    p15RectFrobNorm (p15RectMatMul A B) ≤
      p15RectFrobNorm A * p15RectFrobNorm B := by
  simpa [p15RectFrobNorm, p15RectMatMul, NumStability.frobNormRect,
    NumStability.frobNormSqRect, NumStability.rectMatMul] using
      NumStability.frobNormRect_rectMatMul_le A B

private lemma p15_frob_transpose {m n : ℕ} (A : P15RectMatrix m n) :
    p15RectFrobNorm (p15RectTranspose A) = p15RectFrobNorm A := by
  simpa [p15RectFrobNorm, p15RectTranspose, NumStability.frobNormRect,
    NumStability.frobNormSqRect, NumStability.finiteTranspose] using
      NumStability.frobNormRect_finiteTranspose A

private lemma p15_mul_assoc {m n p q : ℕ}
    (A : P15RectMatrix m n) (B : P15RectMatrix n p)
    (C : P15RectMatrix p q) :
    p15RectMatMul (p15RectMatMul A B) C =
      p15RectMatMul A (p15RectMatMul B C) := by
  simpa [p15RectMatMul, NumStability.rectMatMul] using
    NumStability.rectMatMul_assoc A B C

private lemma p15_mul_add_left {m n p : ℕ}
    (A E : P15RectMatrix m n) (B : P15RectMatrix n p) :
    p15RectMatMul (A + E) B = p15RectMatMul A B + p15RectMatMul E B := by
  simpa [p15RectMatMul, NumStability.rectMatMul] using
    NumStability.rectMatMul_add_left A E B

private lemma p15_mul_add_right {m n p : ℕ}
    (A : P15RectMatrix m n) (B E : P15RectMatrix n p) :
    p15RectMatMul A (B + E) = p15RectMatMul A B + p15RectMatMul A E := by
  simpa [p15RectMatMul, NumStability.rectMatMul] using
    NumStability.rectMatMul_add_right A B E

private lemma p15_orthonormal_isometry_left {m n p : ℕ}
    (Q : P15RectMatrix m n) (B : P15RectMatrix n p)
    (hQ : p15OrthonormalColumns Q) :
    p15RectFrobNorm (p15RectMatMul Q B) = p15RectFrobNorm B := by
  have hQ' : NumStability.GramSchmidtOrthonormalColumns Q := by
    intro j k
    simpa [NumStability.GramSchmidtOrthonormalColumns,
      NumStability.rectangularGram, NumStability.idMatrix] using hQ j k
  simpa [p15RectFrobNorm, p15RectMatMul, NumStability.frobNormRect,
    NumStability.frobNormSqRect, NumStability.rectMatMul] using
      NumStability.H19Sensitivity.frobNormRect_rectMatMul_eq_of_orthonormal_left
        Q B hQ'

private lemma p15_orthonormal_isometry_right {m n p : ℕ}
    (A : P15RectMatrix p n) (Q : P15RectMatrix m n)
    (hQ : p15OrthonormalColumns Q) :
    p15RectFrobNorm (p15RectMatMul A (p15RectTranspose Q)) =
      p15RectFrobNorm A := by
  have htranspose :
      p15RectTranspose (p15RectMatMul A (p15RectTranspose Q)) =
        p15RectMatMul Q (p15RectTranspose A) := by
    ext i j
    simp only [p15RectTranspose, p15RectMatMul]
    apply Finset.sum_congr rfl
    intro k _
    ring
  calc
    p15RectFrobNorm (p15RectMatMul A (p15RectTranspose Q)) =
        p15RectFrobNorm
          (p15RectTranspose (p15RectMatMul A (p15RectTranspose Q))) :=
      (p15_frob_transpose _).symm
    _ = p15RectFrobNorm (p15RectMatMul Q (p15RectTranspose A)) := by
      rw [htranspose]
    _ = p15RectFrobNorm (p15RectTranspose A) :=
      p15_orthonormal_isometry_left Q (p15RectTranspose A) hQ
    _ = p15RectFrobNorm A := p15_frob_transpose A

private lemma p15_orthonormal_frob {m n : ℕ}
    (Q : P15RectMatrix m n) (hQ : p15OrthonormalColumns Q) :
    p15RectFrobNorm Q = Real.sqrt (n : ℝ) := by
  unfold p15RectFrobNorm
  congr 1
  rw [Finset.sum_comm]
  calc
    (∑ j : Fin n, ∑ i : Fin m, Q i j ^ 2) = ∑ _j : Fin n, (1 : ℝ) := by
      apply Finset.sum_congr rfl
      intro j _
      simpa [pow_two] using hQ j j
    _ = (n : ℝ) := by simp

private lemma p15_gamma_nonneg {k u : ℝ} (hk : 0 ≤ k) (hu : 0 ≤ u)
    (hvalid : k * u < 1) :
    0 ≤ p15GammaReal k u := by
  unfold p15GammaReal
  exact div_nonneg (mul_nonneg hk hu) (sub_nonneg.mpr hvalid.le)

private lemma p15_gamma_mono {x y u : ℝ}
    (hx : 0 ≤ x) (hxy : x ≤ y) (hu : 0 ≤ u)
    (hy : y * u < 1) :
    p15GammaReal x u ≤ p15GammaReal y u := by
  have hxu : x * u < 1 := lt_of_le_of_lt (mul_le_mul_of_nonneg_right hxy hu) hy
  have hdx : 0 < 1 - x * u := sub_pos.mpr hxu
  have hdy : 0 < 1 - y * u := sub_pos.mpr hy
  unfold p15GammaReal
  apply (div_le_div_iff₀ hdx hdy).2
  nlinarith

private lemma p15_one_add_gamma {x u : ℝ} (h : x * u < 1) :
    1 + p15GammaReal x u = 1 / (1 - x * u) := by
  unfold p15GammaReal
  field_simp [ne_of_gt (sub_pos.mpr h)]
  ring

private lemma p15_gamma_compose {x y u : ℝ}
    (hx : 0 ≤ x) (hy : 0 ≤ y) (hu : 0 ≤ u)
    (hvalid : (x + y) * u < 1) :
    (1 + p15GammaReal x u) * (1 + p15GammaReal y u) ≤
      1 + p15GammaReal (x + y) u := by
  have hxu : x * u < 1 := by nlinarith [mul_nonneg hy hu]
  have hyu : y * u < 1 := by nlinarith [mul_nonneg hx hu]
  have hdx : 0 < 1 - x * u := sub_pos.mpr hxu
  have hdy : 0 < 1 - y * u := sub_pos.mpr hyu
  have hdxy : 0 < 1 - (x + y) * u := sub_pos.mpr hvalid
  rw [p15_one_add_gamma hxu, p15_one_add_gamma hyu,
    p15_one_add_gamma hvalid]
  have hcombine :
      1 / (1 - x * u) * (1 / (1 - y * u)) =
        1 / ((1 - x * u) * (1 - y * u)) := by
    field_simp [ne_of_gt hdx, ne_of_gt hdy]
  rw [hcombine]
  apply (div_le_div_iff₀ (mul_pos hdx hdy) hdxy).2
  nlinarith [mul_nonneg (mul_nonneg hx hy) (mul_nonneg hu hu)]

private lemma p15_scaled_gamma_le {x s u : ℝ}
    (hx : 0 ≤ x) (hs : 1 ≤ s) (hu : 0 ≤ u)
    (hvalid : x * s * u < 1) :
    p15GammaReal x u * s ≤ p15GammaReal (x * s) u := by
  have hxs : x ≤ x * s := by nlinarith
  have hxvalid : x * u < 1 := by
    apply lt_of_le_of_lt _ hvalid
    nlinarith [mul_nonneg hx hu]
  have hd1 : 0 < 1 - x * u := sub_pos.mpr hxvalid
  have hd2 : 0 < 1 - x * s * u := sub_pos.mpr hvalid
  unfold p15GammaReal
  have hnum : 0 ≤ x * u * s := mul_nonneg (mul_nonneg hx hu) (le_trans zero_le_one hs)
  have hden : 1 - x * s * u ≤ 1 - x * u := by
    nlinarith [mul_le_mul_of_nonneg_right hxs hu]
  calc
    x * u / (1 - x * u) * s = (x * u * s) / (1 - x * u) := by ring
    _ ≤ (x * u * s) / (1 - x * s * u) :=
      div_le_div_of_nonneg_left hnum hd2 hden
    _ = x * s * u / (1 - x * s * u) := by ring

private lemma p15_low_rank_gamma_budget {b r : ℕ} {u : ℝ}
    (hu : 0 ≤ u) (hvalid : p15LowRankMatMulCost b r * u < 1) :
    let s := Real.sqrt (r : ℝ)
    let t := (r : ℝ) * s
    let gb := p15GammaReal (b : ℝ) u
    let gr := p15GammaReal (r : ℝ) u
    let gt := p15GammaReal t u
    let gc := p15GammaReal (p15LowRankMatMulCost b r) u
    0 ≤ gb ∧ 0 ≤ gt ∧ 0 ≤ gc ∧ gr * s ≤ gt ∧
      gb + gt * (1 + gb) + gt * (1 + gt) * (1 + gb) ≤ gc := by
  dsimp only
  let s : ℝ := Real.sqrt (r : ℝ)
  let t : ℝ := (r : ℝ) * s
  let c : ℝ := p15LowRankMatMulCost b r
  have hs0 : 0 ≤ s := Real.sqrt_nonneg _
  have ht0 : 0 ≤ t := mul_nonneg (Nat.cast_nonneg r) hs0
  have hb0 : 0 ≤ (b : ℝ) := Nat.cast_nonneg b
  have hc_eq : c = (b : ℝ) + 2 * t := by
    simp only [c, t, s, p15LowRankMatMulCost]
    ring
  have hc0 : 0 ≤ c := by rw [hc_eq]; positivity
  have hb_le : (b : ℝ) ≤ c := by rw [hc_eq]; nlinarith
  have ht_le : t ≤ c := by rw [hc_eq]; nlinarith
  have hbt_le : (b : ℝ) + t ≤ c := by rw [hc_eq]; nlinarith
  have hb_valid : (b : ℝ) * u < 1 :=
    lt_of_le_of_lt (mul_le_mul_of_nonneg_right hb_le hu) hvalid
  have ht_valid : t * u < 1 :=
    lt_of_le_of_lt (mul_le_mul_of_nonneg_right ht_le hu) hvalid
  have hbt_valid : ((b : ℝ) + t) * u < 1 :=
    lt_of_le_of_lt (mul_le_mul_of_nonneg_right hbt_le hu) hvalid
  have hgb0 := p15_gamma_nonneg hb0 hu hb_valid
  have hgt0 := p15_gamma_nonneg ht0 hu ht_valid
  have hgc0 := p15_gamma_nonneg hc0 hu hvalid
  have hgrs : p15GammaReal (r : ℝ) u * s ≤ p15GammaReal t u := by
    by_cases hr : r = 0
    · subst r
      simp [s, t, p15GammaReal]
    · have hr1 : (1 : ℝ) ≤ (r : ℝ) := by exact_mod_cast Nat.one_le_iff_ne_zero.mpr hr
      have hs_sq : s ^ 2 = (r : ℝ) := by
        simp only [s]
        exact Real.sq_sqrt (Nat.cast_nonneg r)
      have hs1 : 1 ≤ s := by nlinarith
      have hru_valid : (r : ℝ) * s * u < 1 := by simpa [t]
      simpa [t] using
        p15_scaled_gamma_le (x := (r : ℝ)) (s := s) (u := u)
          (Nat.cast_nonneg r) hs1 hu hru_valid
  have hcomp1 :
      (1 + p15GammaReal (b : ℝ) u) * (1 + p15GammaReal t u) ≤
        1 + p15GammaReal ((b : ℝ) + t) u :=
    p15_gamma_compose hb0 ht0 hu hbt_valid
  have hsum0 : 0 ≤ (b : ℝ) + t := add_nonneg hb0 ht0
  have hcomp2 :
      (1 + p15GammaReal ((b : ℝ) + t) u) *
          (1 + p15GammaReal t u) ≤
        1 + p15GammaReal (((b : ℝ) + t) + t) u := by
    apply p15_gamma_compose hsum0 ht0 hu
    calc
      ((b : ℝ) + t + t) * u = c * u := by rw [hc_eq]; ring
      _ < 1 := by simpa [c] using hvalid
  have honegt : 0 ≤ 1 + p15GammaReal t u := by positivity
  have hfactor :
      (1 + p15GammaReal (b : ℝ) u) * (1 + p15GammaReal t u) *
          (1 + p15GammaReal t u) ≤
        1 + p15GammaReal c u := by
    calc
      (1 + p15GammaReal (b : ℝ) u) * (1 + p15GammaReal t u) *
            (1 + p15GammaReal t u)
          ≤ (1 + p15GammaReal ((b : ℝ) + t) u) *
              (1 + p15GammaReal t u) :=
        mul_le_mul_of_nonneg_right hcomp1 honegt
      _ ≤ 1 + p15GammaReal (((b : ℝ) + t) + t) u := hcomp2
      _ = 1 + p15GammaReal c u := by rw [hc_eq]; congr 2 <;> ring
  refine ⟨hgb0, hgt0, hgc0, hgrs, ?_⟩
  nlinarith [hfactor]

private theorem p15_trace_error_bound {b r : ℕ} {u : ℝ}
    (XA YA XB YB : P15RectMatrix b r)
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
  let s : ℝ := Real.sqrt (r : ℝ)
  let t : ℝ := (r : ℝ) * s
  let gb : ℝ := p15GammaReal (b : ℝ) u
  let gr : ℝ := p15GammaReal (r : ℝ) u
  let gt : ℝ := p15GammaReal t u
  let gc : ℝ := p15GammaReal (p15LowRankMatMulCost b r) u
  let Atilde : P15Matrix b := p15LowRankMatrix XA YA
  let Btilde : P15Matrix b := p15LowRankMatrix YB XB
  let M : P15RectMatrix r r :=
    p15RectMatMul (p15RectTranspose YA) YB
  let base : ℝ := p15FrobNorm Atilde * p15FrobNorm Btilde
  have hbudget := p15_low_rank_gamma_budget (b := b) (r := r) hu hvalid
  change 0 ≤ gb ∧ 0 ≤ gt ∧ 0 ≤ gc ∧ gr * s ≤ gt ∧
    gb + gt * (1 + gb) + gt * (1 + gt) * (1 + gb) ≤ gc at hbudget
  obtain ⟨hgb0, hgt0, hgc0, hgrs, hcoeff⟩ := hbudget
  have hAtYA : p15FrobNorm Atilde = p15RectFrobNorm YA := by
    calc
      p15FrobNorm Atilde =
          p15RectFrobNorm (p15RectMatMul XA (p15RectTranspose YA)) := rfl
      _ = p15RectFrobNorm (p15RectTranspose YA) :=
        p15_orthonormal_isometry_left XA (p15RectTranspose YA) hXA
      _ = p15RectFrobNorm YA := p15_frob_transpose YA
  have hBtYB : p15FrobNorm Btilde = p15RectFrobNorm YB := by
    calc
      p15FrobNorm Btilde =
          p15RectFrobNorm (p15RectMatMul YB (p15RectTranspose XB)) := rfl
      _ = p15RectFrobNorm YB :=
        p15_orthonormal_isometry_right YB XB hXB
  have hXAnorm : p15RectFrobNorm XA = s := by
    simpa [s] using p15_orthonormal_frob XA hXA
  have hXBnorm : p15RectFrobNorm (p15RectTranspose XB) = s := by
    rw [p15_frob_transpose, p15_orthonormal_frob XB hXB]
  have hbase0 : 0 ≤ base := by
    exact mul_nonneg (p15_frob_nonneg Atilde) (p15_frob_nonneg Btilde)
  have hM : p15RectFrobNorm M ≤ base := by
    calc
      p15RectFrobNorm M ≤
          p15RectFrobNorm (p15RectTranspose YA) * p15RectFrobNorm YB :=
        p15_frob_mul_le _ _
      _ = base := by rw [p15_frob_transpose, ← hAtYA, ← hBtYB]
  have hexact :
      p15MatMul Atilde Btilde =
        p15RectMatMul (p15RectMatMul XA M) (p15RectTranspose XB) := by
    change
      p15RectMatMul
          (p15RectMatMul XA (p15RectTranspose YA))
          (p15RectMatMul YB (p15RectTranspose XB)) =
        p15RectMatMul
          (p15RectMatMul XA
            (p15RectMatMul (p15RectTranspose YA) YB))
          (p15RectTranspose XB)
    rw [p15_mul_assoc, ← p15_mul_assoc (p15RectTranspose YA) YB,
      ← p15_mul_assoc XA]
  cases trace with
  | leftAssociated middleStage leftStage finalStage =>
      let Em : P15RectMatrix r r := middleStage.error
      let El : P15RectMatrix b r := leftStage.error
      let Ef : P15Matrix b := finalStage.error
      have hEm : p15RectFrobNorm Em ≤ gb * base := by
        calc
          p15RectFrobNorm Em ≤
              gb * p15RectFrobNorm (p15RectTranspose YA) *
                p15RectFrobNorm YB := middleStage.error_le
          _ = gb * base := by
            rw [p15_frob_transpose, ← hAtYA, ← hBtYB]
            change gb * p15FrobNorm Atilde * p15FrobNorm Btilde =
              gb * (p15FrobNorm Atilde * p15FrobNorm Btilde)
            ring
      have hmiddle :
          p15RectFrobNorm middleStage.result ≤ (1 + gb) * base := by
        calc
          p15RectFrobNorm middleStage.result = p15RectFrobNorm (M + Em) := rfl
          _ ≤ p15RectFrobNorm M + p15RectFrobNorm Em := p15_frob_add_le _ _
          _ ≤ base + gb * base := add_le_add hM hEm
          _ = (1 + gb) * base := by ring
      have hEl :
          p15RectFrobNorm El ≤ gt * (1 + gb) * base := by
        calc
          p15RectFrobNorm El ≤
              gr * p15RectFrobNorm XA *
                p15RectFrobNorm middleStage.result := leftStage.error_le
          _ = (gr * s) * p15RectFrobNorm middleStage.result := by rw [hXAnorm]
          _ ≤ gt * p15RectFrobNorm middleStage.result :=
            mul_le_mul_of_nonneg_right hgrs (p15_frob_nonneg _)
          _ ≤ gt * ((1 + gb) * base) :=
            mul_le_mul_of_nonneg_left hmiddle hgt0
          _ = gt * (1 + gb) * base := by ring
      have hleft :
          p15RectFrobNorm leftStage.result ≤
            (1 + gt) * (1 + gb) * base := by
        calc
          p15RectFrobNorm leftStage.result =
              p15RectFrobNorm
                (p15RectMatMul XA middleStage.result + El) := rfl
          _ ≤ p15RectFrobNorm (p15RectMatMul XA middleStage.result) +
              p15RectFrobNorm El := p15_frob_add_le _ _
          _ = p15RectFrobNorm middleStage.result + p15RectFrobNorm El := by
            rw [p15_orthonormal_isometry_left XA middleStage.result hXA]
          _ ≤ (1 + gb) * base + gt * (1 + gb) * base :=
            add_le_add hmiddle hEl
          _ = (1 + gt) * (1 + gb) * base := by ring
      have hEf :
          p15RectFrobNorm Ef ≤ gt * (1 + gt) * (1 + gb) * base := by
        calc
          p15RectFrobNorm Ef ≤
              gr * p15RectFrobNorm leftStage.result *
                p15RectFrobNorm (p15RectTranspose XB) := finalStage.error_le
          _ = (gr * s) * p15RectFrobNorm leftStage.result := by rw [hXBnorm]; ring
          _ ≤ gt * p15RectFrobNorm leftStage.result :=
            mul_le_mul_of_nonneg_right hgrs (p15_frob_nonneg _)
          _ ≤ gt * ((1 + gt) * (1 + gb) * base) :=
            mul_le_mul_of_nonneg_left hleft hgt0
          _ = gt * (1 + gt) * (1 + gb) * base := by ring
      have hdecomp :
          finalStage.result - p15MatMul Atilde Btilde =
            p15RectMatMul
                (p15RectMatMul XA Em + El) (p15RectTranspose XB) + Ef := by
        rw [hexact]
        change
          (p15RectMatMul
              (p15RectMatMul XA (M + Em) + El) (p15RectTranspose XB) + Ef) -
              p15RectMatMul (p15RectMatMul XA M) (p15RectTranspose XB) =
            p15RectMatMul (p15RectMatMul XA Em + El) (p15RectTranspose XB) + Ef
        rw [p15_mul_add_right XA M Em,
          p15_mul_add_left
            (p15RectMatMul XA M + p15RectMatMul XA Em) El,
          p15_mul_add_left (p15RectMatMul XA M) (p15RectMatMul XA Em),
          p15_mul_add_left (p15RectMatMul XA Em) El]
        abel
      calc
        p15FrobNorm
            (finalStage.result - p15MatMul Atilde Btilde) =
            p15RectFrobNorm
              (p15RectMatMul
                  (p15RectMatMul XA Em + El) (p15RectTranspose XB) + Ef) := by
          rw [hdecomp]
          rfl
        _ ≤ p15RectFrobNorm
                (p15RectMatMul
                  (p15RectMatMul XA Em + El) (p15RectTranspose XB)) +
              p15RectFrobNorm Ef := p15_frob_add_le _ _
        _ = p15RectFrobNorm (p15RectMatMul XA Em + El) +
              p15RectFrobNorm Ef := by
          rw [p15_orthonormal_isometry_right _ XB hXB]
        _ ≤ (p15RectFrobNorm (p15RectMatMul XA Em) +
                p15RectFrobNorm El) + p15RectFrobNorm Ef := by
          gcongr
          exact p15_frob_add_le _ _
        _ = (p15RectFrobNorm Em + p15RectFrobNorm El) +
              p15RectFrobNorm Ef := by
          rw [p15_orthonormal_isometry_left XA Em hXA]
        _ ≤ (gb * base + gt * (1 + gb) * base) +
              gt * (1 + gt) * (1 + gb) * base :=
          add_le_add (add_le_add hEm hEl) hEf
        _ = (gb + gt * (1 + gb) + gt * (1 + gt) * (1 + gb)) * base := by ring
        _ ≤ gc * base := mul_le_mul_of_nonneg_right hcoeff hbase0
        _ = p15GammaReal (p15LowRankMatMulCost b r) u *
              p15FrobNorm Atilde * p15FrobNorm Btilde := by
          simp only [gc, base]
          ring

  | rightAssociated middleStage rightStage finalStage =>
      let Em : P15RectMatrix r r := middleStage.error
      let Er : P15RectMatrix r b := rightStage.error
      let Ef : P15Matrix b := finalStage.error
      have hEm : p15RectFrobNorm Em ≤ gb * base := by
        calc
          p15RectFrobNorm Em ≤
              gb * p15RectFrobNorm (p15RectTranspose YA) *
                p15RectFrobNorm YB := middleStage.error_le
          _ = gb * base := by
            rw [p15_frob_transpose, ← hAtYA, ← hBtYB]
            change gb * p15FrobNorm Atilde * p15FrobNorm Btilde =
              gb * (p15FrobNorm Atilde * p15FrobNorm Btilde)
            ring
      have hmiddle :
          p15RectFrobNorm middleStage.result ≤ (1 + gb) * base := by
        calc
          p15RectFrobNorm middleStage.result = p15RectFrobNorm (M + Em) := rfl
          _ ≤ p15RectFrobNorm M + p15RectFrobNorm Em := p15_frob_add_le _ _
          _ ≤ base + gb * base := add_le_add hM hEm
          _ = (1 + gb) * base := by ring
      have hEr :
          p15RectFrobNorm Er ≤ gt * (1 + gb) * base := by
        calc
          p15RectFrobNorm Er ≤
              gr * p15RectFrobNorm middleStage.result *
                p15RectFrobNorm (p15RectTranspose XB) := rightStage.error_le
          _ = (gr * s) * p15RectFrobNorm middleStage.result := by rw [hXBnorm]; ring
          _ ≤ gt * p15RectFrobNorm middleStage.result :=
            mul_le_mul_of_nonneg_right hgrs (p15_frob_nonneg _)
          _ ≤ gt * ((1 + gb) * base) :=
            mul_le_mul_of_nonneg_left hmiddle hgt0
          _ = gt * (1 + gb) * base := by ring
      have hright :
          p15RectFrobNorm rightStage.result ≤
            (1 + gt) * (1 + gb) * base := by
        calc
          p15RectFrobNorm rightStage.result =
              p15RectFrobNorm
                (p15RectMatMul middleStage.result (p15RectTranspose XB) + Er) := rfl
          _ ≤
              p15RectFrobNorm
                  (p15RectMatMul middleStage.result (p15RectTranspose XB)) +
                p15RectFrobNorm Er := p15_frob_add_le _ _
          _ = p15RectFrobNorm middleStage.result + p15RectFrobNorm Er := by
            rw [p15_orthonormal_isometry_right middleStage.result XB hXB]
          _ ≤ (1 + gb) * base + gt * (1 + gb) * base :=
            add_le_add hmiddle hEr
          _ = (1 + gt) * (1 + gb) * base := by ring
      have hEf :
          p15RectFrobNorm Ef ≤ gt * (1 + gt) * (1 + gb) * base := by
        calc
          p15RectFrobNorm Ef ≤
              gr * p15RectFrobNorm XA *
                p15RectFrobNorm rightStage.result := finalStage.error_le
          _ = (gr * s) * p15RectFrobNorm rightStage.result := by rw [hXAnorm]
          _ ≤ gt * p15RectFrobNorm rightStage.result :=
            mul_le_mul_of_nonneg_right hgrs (p15_frob_nonneg _)
          _ ≤ gt * ((1 + gt) * (1 + gb) * base) :=
            mul_le_mul_of_nonneg_left hright hgt0
          _ = gt * (1 + gt) * (1 + gb) * base := by ring
      have hdecomp :
          finalStage.result - p15MatMul Atilde Btilde =
            p15RectMatMul XA
                (p15RectMatMul Em (p15RectTranspose XB) + Er) + Ef := by
        rw [hexact]
        change
          (p15RectMatMul XA
              (p15RectMatMul (M + Em) (p15RectTranspose XB) + Er) + Ef) -
              p15RectMatMul (p15RectMatMul XA M) (p15RectTranspose XB) =
            p15RectMatMul XA
              (p15RectMatMul Em (p15RectTranspose XB) + Er) + Ef
        rw [p15_mul_add_left M Em,
          p15_mul_add_right XA
            (p15RectMatMul M (p15RectTranspose XB) +
              p15RectMatMul Em (p15RectTranspose XB)) Er,
          p15_mul_add_right XA
            (p15RectMatMul M (p15RectTranspose XB))
            (p15RectMatMul Em (p15RectTranspose XB)),
          p15_mul_add_right XA
            (p15RectMatMul Em (p15RectTranspose XB)) Er,
          ← p15_mul_assoc XA M]
        abel
      calc
        p15FrobNorm
            (finalStage.result - p15MatMul Atilde Btilde) =
            p15RectFrobNorm
              (p15RectMatMul XA
                  (p15RectMatMul Em (p15RectTranspose XB) + Er) + Ef) := by
          rw [hdecomp]
          rfl
        _ ≤ p15RectFrobNorm
                (p15RectMatMul XA
                  (p15RectMatMul Em (p15RectTranspose XB) + Er)) +
              p15RectFrobNorm Ef := p15_frob_add_le _ _
        _ = p15RectFrobNorm
                (p15RectMatMul Em (p15RectTranspose XB) + Er) +
              p15RectFrobNorm Ef := by
          rw [p15_orthonormal_isometry_left XA _ hXA]
        _ ≤
            (p15RectFrobNorm
                (p15RectMatMul Em (p15RectTranspose XB)) +
              p15RectFrobNorm Er) + p15RectFrobNorm Ef := by
          gcongr
          exact p15_frob_add_le _ _
        _ = (p15RectFrobNorm Em + p15RectFrobNorm Er) +
              p15RectFrobNorm Ef := by
          rw [p15_orthonormal_isometry_right Em XB hXB]
        _ ≤ (gb * base + gt * (1 + gb) * base) +
              gt * (1 + gt) * (1 + gb) * base :=
          add_le_add (add_le_add hEm hEr) hEf
        _ = (gb + gt * (1 + gb) + gt * (1 + gt) * (1 + gb)) * base := by ring
        _ ≤ gc * base := mul_le_mul_of_nonneg_right hcoeff hbase0
        _ = p15GammaReal (p15LowRankMatMulCost b r) u *
              p15FrobNorm Atilde * p15FrobNorm Btilde := by
          simp only [gc, base]
          ring

private theorem p15_perturbed_product_error {n : ℕ}
    (A B Atilde Btilde EA EB C : P15Matrix n)
    (g ea eb : ℝ)
    (hg : 0 ≤ g) (hea : 0 ≤ ea) (heb : 0 ≤ eb)
    (hAtilde : Atilde = A + EA)
    (hBtilde : Btilde = B + EB)
    (hEA : p15FrobNorm EA ≤ ea)
    (hEB : p15FrobNorm EB ≤ eb)
    (hfirst :
      p15FrobNorm (C - p15MatMul Atilde Btilde) ≤
        g * p15FrobNorm Atilde * p15FrobNorm Btilde) :
    p15FrobNorm (C - p15MatMul A B) ≤
      g * p15FrobNorm A * p15FrobNorm B +
        (1 + g) *
          (ea * p15FrobNorm B + p15FrobNorm A * eb + ea * eb) := by
  have hAnorm : p15FrobNorm Atilde ≤ p15FrobNorm A + ea := by
    rw [hAtilde]
    calc
      p15FrobNorm (A + EA) = p15RectFrobNorm (A + EA) := rfl
      _ ≤ p15RectFrobNorm A + p15RectFrobNorm EA := p15_frob_add_le A EA
      _ = p15FrobNorm A + p15FrobNorm EA := rfl
      _ ≤ p15FrobNorm A + ea := add_le_add (le_refl _) hEA
  have hBnorm : p15FrobNorm Btilde ≤ p15FrobNorm B + eb := by
    rw [hBtilde]
    calc
      p15FrobNorm (B + EB) = p15RectFrobNorm (B + EB) := rfl
      _ ≤ p15RectFrobNorm B + p15RectFrobNorm EB := p15_frob_add_le B EB
      _ = p15FrobNorm B + p15FrobNorm EB := rfl
      _ ≤ p15FrobNorm B + eb := add_le_add (le_refl _) hEB
  have hAplus0 : 0 ≤ p15FrobNorm A + ea :=
    add_nonneg (p15_frob_nonneg A) hea
  have hBplus0 : 0 ≤ p15FrobNorm B + eb :=
    add_nonneg (p15_frob_nonneg B) heb
  have htildeprod :
      p15FrobNorm Atilde * p15FrobNorm Btilde ≤
        (p15FrobNorm A + ea) * (p15FrobNorm B + eb) :=
    mul_le_mul hAnorm hBnorm (p15_frob_nonneg Btilde) hAplus0
  have hexpand :
      p15MatMul Atilde Btilde - p15MatMul A B =
        p15MatMul EA B + p15MatMul A EB + p15MatMul EA EB := by
    rw [hAtilde, hBtilde]
    change
      p15RectMatMul (A + EA) (B + EB) - p15RectMatMul A B =
        p15RectMatMul EA B + p15RectMatMul A EB + p15RectMatMul EA EB
    rw [p15_mul_add_right (A + EA) B EB,
      p15_mul_add_left A EA B, p15_mul_add_left A EA EB]
    abel
  have hperturb :
      p15FrobNorm (p15MatMul Atilde Btilde - p15MatMul A B) ≤
        ea * p15FrobNorm B + p15FrobNorm A * eb + ea * eb := by
    calc
      p15FrobNorm (p15MatMul Atilde Btilde - p15MatMul A B) =
          p15FrobNorm
            ((p15MatMul EA B + p15MatMul A EB) + p15MatMul EA EB) := by
        rw [hexpand]
      _ ≤ p15FrobNorm (p15MatMul EA B + p15MatMul A EB) +
            p15FrobNorm (p15MatMul EA EB) := p15_frob_add_le _ _
      _ ≤ (p15FrobNorm (p15MatMul EA B) +
              p15FrobNorm (p15MatMul A EB)) +
            p15FrobNorm (p15MatMul EA EB) := by
        gcongr
        exact p15_frob_add_le _ _
      _ ≤ (p15FrobNorm EA * p15FrobNorm B +
              p15FrobNorm A * p15FrobNorm EB) +
            p15FrobNorm EA * p15FrobNorm EB := by
        exact add_le_add
          (add_le_add (p15_frob_mul_le EA B) (p15_frob_mul_le A EB))
          (p15_frob_mul_le EA EB)
      _ ≤ (ea * p15FrobNorm B + p15FrobNorm A * eb) + ea * eb := by
        exact add_le_add
          (add_le_add
            (mul_le_mul_of_nonneg_right hEA (p15_frob_nonneg B))
            (mul_le_mul_of_nonneg_left hEB (p15_frob_nonneg A)))
          (mul_le_mul hEA hEB (p15_frob_nonneg EB) hea)
      _ = ea * p15FrobNorm B + p15FrobNorm A * eb + ea * eb := by ring
  have hdecomp :
      C - p15MatMul A B =
        (C - p15MatMul Atilde Btilde) +
          (p15MatMul Atilde Btilde - p15MatMul A B) := by
    abel
  calc
    p15FrobNorm (C - p15MatMul A B) =
        p15FrobNorm
          ((C - p15MatMul Atilde Btilde) +
            (p15MatMul Atilde Btilde - p15MatMul A B)) := by rw [hdecomp]
    _ ≤ p15FrobNorm (C - p15MatMul Atilde Btilde) +
          p15FrobNorm (p15MatMul Atilde Btilde - p15MatMul A B) :=
      p15_frob_add_le _ _
    _ ≤ g * p15FrobNorm Atilde * p15FrobNorm Btilde +
          (ea * p15FrobNorm B + p15FrobNorm A * eb + ea * eb) :=
      add_le_add hfirst hperturb
    _ ≤ g * ((p15FrobNorm A + ea) * (p15FrobNorm B + eb)) +
          (ea * p15FrobNorm B + p15FrobNorm A * eb + ea * eb) := by
      have hmain :
          g * p15FrobNorm Atilde * p15FrobNorm Btilde ≤
            g * ((p15FrobNorm A + ea) * (p15FrobNorm B + eb)) := by
        calc
          g * p15FrobNorm Atilde * p15FrobNorm Btilde =
              g * (p15FrobNorm Atilde * p15FrobNorm Btilde) := by ring
          _ ≤ g * ((p15FrobNorm A + ea) * (p15FrobNorm B + eb)) :=
            mul_le_mul_of_nonneg_left htildeprod hg
      exact add_le_add hmain (le_refl _)
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
  let gammaC : ℝ :=
    p15GammaReal (p15LowRankMatMulCost b r) run.unitRoundoff
  have hfirst :
      p15FrobNorm
          (run.trace.result -
            p15MatMul (p15LowRankMatrix run.XA run.YA)
              (p15LowRankMatrix run.YB run.XB)) ≤
        gammaC * p15FrobNorm (p15LowRankMatrix run.XA run.YA) *
          p15FrobNorm (p15LowRankMatrix run.YB run.XB) := by
    simpa only [gammaC] using
      p15_trace_error_bound run.XA run.YA run.XB run.YB
        run.unitRoundoff_nonneg run.gamma_valid
        run.xA_orthonormal run.xB_orthonormal run.trace
  have hbudget := p15_low_rank_gamma_budget
    (b := b) (r := r) run.unitRoundoff_nonneg run.gamma_valid
  have hgammaC : 0 ≤ gammaC := by
    simpa only [gammaC] using hbudget.2.2.1
  have hea : 0 ≤ run.epsilon * run.betaA :=
    le_trans (p15_frob_nonneg run.approximationErrorA)
      run.approximationErrorA_le
  have heb : 0 ≤ run.epsilon * run.betaB :=
    le_trans (p15_frob_nonneg run.approximationErrorB)
      run.approximationErrorB_le
  refine ⟨hfirst, ?_⟩
  have hsecond := p15_perturbed_product_error
    (A := run.A) (B := run.B)
    (Atilde := p15LowRankMatrix run.XA run.YA)
    (Btilde := p15LowRankMatrix run.YB run.XB)
    (EA := run.approximationErrorA)
    (EB := run.approximationErrorB)
    (C := run.trace.result)
    (g := gammaC)
    (ea := run.epsilon * run.betaA)
    (eb := run.epsilon * run.betaB)
    hgammaC hea heb
    run.approximationA_eq run.approximationB_eq
    run.approximationErrorA_le run.approximationErrorB_le hfirst
  calc
    p15FrobNorm (run.trace.result - p15MatMul run.A run.B) ≤
        gammaC * p15FrobNorm run.A * p15FrobNorm run.B +
          (1 + gammaC) *
            ((run.epsilon * run.betaA) * p15FrobNorm run.B +
              p15FrobNorm run.A * (run.epsilon * run.betaB) +
              (run.epsilon * run.betaA) * (run.epsilon * run.betaB)) := hsecond
    _ = gammaC * p15FrobNorm run.A * p15FrobNorm run.B +
          run.epsilon * (1 + gammaC) *
            (run.betaA * p15FrobNorm run.B +
              p15FrobNorm run.A * run.betaB +
              run.epsilon * run.betaA * run.betaB) := by
      ring

end HighamBench
