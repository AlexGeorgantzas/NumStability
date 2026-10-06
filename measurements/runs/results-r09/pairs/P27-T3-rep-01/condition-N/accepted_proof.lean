import HighamBench.P27Definitions

namespace HighamBench

open scoped BigOperators

private lemma p27_vecNormSq_nonneg {n : ℕ} (x : P27Vector n) :
    0 ≤ p27VecNormSq x := by
  simp only [p27VecNormSq]
  positivity

private lemma p27_dot_sq_le {n : ℕ} (x y : P27Vector n) :
    (∑ i, x i * y i) ^ 2 ≤ p27VecNormSq x * p27VecNormSq y := by
  simpa only [p27VecNormSq] using
    (Finset.sum_mul_sq_le_sq_mul_sq (Finset.univ) x y)

private lemma p27_matVec_normSq_le {k q : ℕ}
    (X : P27Coupling k q) (v : P27Vector q) :
    p27VecNormSq (p27MatVec X v) ≤
      (∑ i, ∑ j, X i j ^ 2) * p27VecNormSq v := by
  unfold p27VecNormSq p27MatVec
  calc
    ∑ i, (∑ j, X i j * v j) ^ 2 ≤
        ∑ i, (∑ j, X i j ^ 2) * ∑ j, v j ^ 2 := by
      exact Finset.sum_le_sum fun i _ ↦
        Finset.sum_mul_sq_le_sq_mul_sq Finset.univ (X i) v
    _ = (∑ i, ∑ j, X i j ^ 2) * ∑ j, v j ^ 2 := by
      rw [Finset.sum_mul]

private lemma p27_vecNormSq_add {n : ℕ} (x y : P27Vector n) :
    p27VecNormSq (x + y) = p27VecNormSq x +
      2 * (∑ i, x i * y i) + p27VecNormSq y := by
  simp only [p27VecNormSq, Pi.add_apply]
  calc
    ∑ i, (x i + y i) ^ 2 =
        ∑ i, (x i ^ 2 + 2 * (x i * y i) + y i ^ 2) := by
      apply Finset.sum_congr rfl
      intro i _
      ring
    _ = _ := by
      rw [Finset.sum_add_distrib, Finset.sum_add_distrib,
        ← Finset.mul_sum]

private lemma p27_vecNormSq_smul {n : ℕ} (a : ℝ) (x : P27Vector n) :
    p27VecNormSq (a • x) = a ^ 2 * p27VecNormSq x := by
  simp only [p27VecNormSq, Pi.smul_apply, smul_eq_mul]
  rw [Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro i _
  ring

private lemma p27_vecNormSq_sub {n : ℕ} (x y : P27Vector n) :
    p27VecNormSq (x - y) = p27VecNormSq x -
      2 * (∑ i, x i * y i) + p27VecNormSq y := by
  simp only [p27VecNormSq, Pi.sub_apply]
  calc
    ∑ i, (x i - y i) ^ 2 =
        ∑ i, (x i ^ 2 - 2 * (x i * y i) + y i ^ 2) := by
      apply Finset.sum_congr rfl
      intro i _
      ring
    _ = _ := by
      rw [Finset.sum_add_distrib, Finset.sum_sub_distrib,
        ← Finset.mul_sum]

private lemma p27_w1_frobenius_gain {k q : ℕ}
    (X : P27Coupling k q) (a : ℝ) :
    P27SquaredGainBound (p27W1 X a)
      (1 + (∑ i, ∑ j, X i j ^ 2) + a ^ 2) := by
  intro u v
  let y : P27Vector k := p27MatVec X v
  let s : ℝ := ∑ i, ∑ j, X i j ^ 2
  let U : ℝ := p27VecNormSq u
  let V : ℝ := p27VecNormSq v
  let Y : ℝ := p27VecNormSq y
  let d : ℝ := ∑ i, u i * y i
  have hs : 0 ≤ s := by
    dsimp [s]
    positivity
  have hU : 0 ≤ U := p27_vecNormSq_nonneg u
  have hV : 0 ≤ V := p27_vecNormSq_nonneg v
  have hY : Y ≤ s * V := by
    simpa only [y, Y, s, V] using p27_matVec_normSq_le X v
  have hd : d ^ 2 ≤ U * Y := by
    simpa only [d, U, Y] using p27_dot_sq_le u y
  have hsd : d ^ 2 ≤ (s * U) * V := by
    calc
      d ^ 2 ≤ U * Y := hd
      _ ≤ U * (s * V) := mul_le_mul_of_nonneg_left hY hU
      _ = (s * U) * V := by ring
  have hcross : 2 * d ≤ s * U + V := by
    have hsum : 0 ≤ s * U + V := by positivity
    have hamgm : 4 * ((s * U) * V) ≤ (s * U + V) ^ 2 := by
      nlinarith [sq_nonneg (s * U - V)]
    have hsq : (2 * d) ^ 2 ≤ (s * U + V) ^ 2 := by
      nlinarith
    have habs : |2 * d| ≤ s * U + V := by
      rw [← sq_le_sq₀ (abs_nonneg (2 * d)) hsum, sq_abs]
      exact hsq
    exact (le_abs_self (2 * d)).trans habs
  simp only [p27W1, p27PairNormSq, Prod.fst, Prod.snd]
  rw [p27_vecNormSq_add, p27_vecNormSq_smul]
  change U + 2 * d + Y + a ^ 2 * V ≤ (1 + s + a ^ 2) * (U + V)
  nlinarith [sq_nonneg a]

private lemma p27_w2_frobenius_gain {k q : ℕ}
    (X : P27Coupling k q) (a : ℝ) :
    P27SquaredGainBound (p27W2 X a)
      (1 + (∑ i, ∑ j, X i j ^ 2) + a ^ 2) := by
  intro u v
  let y : P27Vector k := p27MatVec X v
  let s : ℝ := ∑ i, ∑ j, X i j ^ 2
  let U : ℝ := p27VecNormSq u
  let V : ℝ := p27VecNormSq v
  let Y : ℝ := p27VecNormSq y
  let d : ℝ := ∑ i, u i * y i
  have hs : 0 ≤ s := by
    dsimp [s]
    positivity
  have hU : 0 ≤ U := p27_vecNormSq_nonneg u
  have hV : 0 ≤ V := p27_vecNormSq_nonneg v
  have hY : Y ≤ s * V := by
    simpa only [y, Y, s, V] using p27_matVec_normSq_le X v
  have hd : d ^ 2 ≤ U * Y := by
    simpa only [d, U, Y] using p27_dot_sq_le u y
  have hsd : d ^ 2 ≤ (s * U) * V := by
    calc
      d ^ 2 ≤ U * Y := hd
      _ ≤ U * (s * V) := mul_le_mul_of_nonneg_left hY hU
      _ = (s * U) * V := by ring
  have hscaled : (a * d) ^ 2 ≤ (s * U) * (a ^ 2 * V) := by
    nlinarith [sq_nonneg a]
  have hcross : -(2 * (a * d)) ≤ s * U + a ^ 2 * V := by
    have hsum : 0 ≤ s * U + a ^ 2 * V := by positivity
    have hamgm : 4 * ((s * U) * (a ^ 2 * V)) ≤
        (s * U + a ^ 2 * V) ^ 2 := by
      nlinarith [sq_nonneg (s * U - a ^ 2 * V)]
    have hsq : (-(2 * (a * d))) ^ 2 ≤
        (s * U + a ^ 2 * V) ^ 2 := by
      nlinarith
    have habs : |-(2 * (a * d))| ≤ s * U + a ^ 2 * V := by
      rw [← sq_le_sq₀ (abs_nonneg (-(2 * (a * d)))) hsum, sq_abs]
      exact hsq
    exact (le_abs_self (-(2 * (a * d)))).trans habs
  simp only [p27W2, p27PairNormSq, Prod.fst, Prod.snd]
  rw [p27_vecNormSq_sub, p27_vecNormSq_smul]
  have hdot : (∑ i, (a • u) i * y i) = a * d := by
    simp only [Pi.smul_apply, smul_eq_mul]
    rw [Finset.mul_sum]
    apply Finset.sum_congr rfl
    intro i _
    ring
  rw [hdot]
  change a ^ 2 * U - 2 * (a * d) + Y + V ≤
    (1 + s + a ^ 2) * (U + V)
  nlinarith

private lemma p27_gain_mono {k q : ℕ}
    {W : P27Vector k → P27Vector q → P27Vector k × P27Vector q}
    {a b : ℝ} (hab : a ≤ b) (ha : P27SquaredGainBound W a) :
    P27SquaredGainBound W b := by
  intro u v
  calc
    p27PairNormSq (W u v).1 (W u v).2 ≤
        a * p27PairNormSq u v := ha u v
    _ ≤ b * p27PairNormSq u v := by
      exact mul_le_mul_of_nonneg_right hab
        (add_nonneg (p27_vecNormSq_nonneg u) (p27_vecNormSq_nonneg v))

private lemma p27_frobenius_parameter_le {k q : ℕ}
    (data : P27Theorem32Data k q) :
    1 + (∑ i, ∑ j, data.X i j ^ 2) + data.alpha ^ 2 ≤
      1 + data.f ^ 2 * (k : ℝ) * (q : ℝ) := by
  have hpairs :
      (∑ i, ∑ j, (data.X i j ^ 2 + data.ratio i j ^ 2)) ≤
        ∑ i : Fin k, ∑ _j : Fin q, data.f ^ 2 := by
    exact Finset.sum_le_sum fun i _ ↦ Finset.sum_le_sum fun j _ ↦
      (data.p_lt_f i j).le
  have hsplit :
      (∑ i, ∑ j, (data.X i j ^ 2 + data.ratio i j ^ 2)) =
        (∑ i, ∑ j, data.X i j ^ 2) +
          ∑ i, ∑ j, data.ratio i j ^ 2 := by
    simp only [Finset.sum_add_distrib]
  have hconst : (∑ i : Fin k, ∑ _j : Fin q, data.f ^ 2) =
      data.f ^ 2 * (k : ℝ) * (q : ℝ) := by
    simp only [Finset.sum_const, Finset.card_univ, Fintype.card_fin,
      nsmul_eq_mul]
    ring
  rw [hsplit, hconst] at hpairs
  linarith [data.alpha_sq_le]

/-- P27-T3: the two strong rank-revealing bounds in Theorem 3.2. -/
theorem p27_t3_theorem3_2 {k q : ℕ} (data : P27Theorem32Data k q) :
    (∀ i, data.sigmaMTop i / p27StrongFactor k q data.f ≤ data.sigmaA i) ∧
    (∀ j, data.sigmaC j ≤
      data.sigmaMTail j * p27StrongFactor k q data.f) := by
  -- PROOF_START P27-T3-H001
  let gSq : ℝ := 1 + data.f ^ 2 * (k : ℝ) * (q : ℝ)
  have hg_one : 1 ≤ gSq := by
    dsimp [gSq]
    exact le_add_of_nonneg_right (by positivity)
  have hg : 0 ≤ gSq := le_trans (by norm_num) hg_one
  have hparameter :
      1 + (∑ i, ∑ j, data.X i j ^ 2) + data.alpha ^ 2 ≤ gSq := by
    simpa only [gSq] using p27_frobenius_parameter_le data
  have hgain1 : P27SquaredGainBound (p27W1 data.X data.alpha) gSq :=
    p27_gain_mono hparameter (p27_w1_frobenius_gain data.X data.alpha)
  have hgain2 : P27SquaredGainBound (p27W2 data.X data.alpha) gSq :=
    p27_gain_mono hparameter (p27_w2_frobenius_gain data.X data.alpha)
  have htop := data.hornJohnson_top gSq hg hgain1
  have htail := data.hornJohnson_tail gSq hg hgain2
  have hgpos : 0 < gSq := lt_of_lt_of_le zero_lt_one hg_one
  have hsqrtpos : 0 < Real.sqrt gSq := Real.sqrt_pos.2 hgpos
  constructor
  · intro i
    apply (div_le_iff₀ (by
      simpa only [p27StrongFactor, gSq] using hsqrtpos)).2
    simpa only [p27StrongFactor, gSq] using htop i
  · intro j
    simpa only [p27StrongFactor, gSq] using htail j

end HighamBench
