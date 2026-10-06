import HighamBench.P27Definitions

namespace HighamBench

open scoped BigOperators

private lemma p27_vecNormSq_nonneg {n : ℕ} (x : P27Vector n) :
    0 ≤ p27VecNormSq x := by
  unfold p27VecNormSq
  positivity

private lemma p27_two_mul_le_add_of_sq_le_mul {a b r : ℝ}
    (ha : 0 ≤ a) (hb : 0 ≤ b) (h : r ^ 2 ≤ a * b) :
    2 * r ≤ a + b := by
  by_cases hr : r ≤ 0
  · nlinarith
  · have hs : 4 * r ^ 2 ≤ (a + b) ^ 2 := by
      nlinarith [sq_nonneg (a - b)]
    nlinarith [sq_nonneg (a + b + 2 * r)]

private lemma p27_matVec_normSq_le {k q : ℕ} (X : P27Coupling k q)
    (v : P27Vector q) :
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

private lemma p27_dot_sq_le {n : ℕ} (x y : P27Vector n) :
    (∑ i, x i * y i) ^ 2 ≤ p27VecNormSq x * p27VecNormSq y := by
  exact Finset.sum_mul_sq_le_sq_mul_sq Finset.univ x y

private lemma p27_w1_gain {k q : ℕ} (X : P27Coupling k q) (alpha : ℝ) :
    P27SquaredGainBound (p27W1 X alpha)
      (1 + (∑ i, ∑ j, X i j ^ 2) + alpha ^ 2) := by
  intro u v
  let S : ℝ := ∑ i, ∑ j, X i j ^ 2
  let U : ℝ := p27VecNormSq u
  let V : ℝ := p27VecNormSq v
  let y : P27Vector k := p27MatVec X v
  let Y : ℝ := p27VecNormSq y
  let D : ℝ := ∑ i, u i * y i
  have hS : 0 ≤ S := by
    dsimp [S]
    positivity
  have hU : 0 ≤ U := p27_vecNormSq_nonneg u
  have hV : 0 ≤ V := p27_vecNormSq_nonneg v
  have hY : 0 ≤ Y := p27_vecNormSq_nonneg y
  have hy : Y ≤ S * V := by
    simpa [S, V, Y, y] using p27_matVec_normSq_le X v
  have hD : D ^ 2 ≤ U * Y := by
    simpa [D, U, Y] using p27_dot_sq_le u y
  have hcross : 2 * D ≤ (S + alpha ^ 2) * U + V := by
    apply p27_two_mul_le_add_of_sq_le_mul
    · positivity
    · exact hV
    · calc
        D ^ 2 ≤ U * Y := hD
        _ ≤ U * (S * V) := by gcongr
        _ = (S * U) * V := by ring
        _ ≤ ((S + alpha ^ 2) * U) * V := by
          exact mul_le_mul_of_nonneg_right
            (by nlinarith [mul_nonneg (sq_nonneg alpha) hU]) hV
  change p27PairNormSq (u + p27MatVec X v) (alpha • v) ≤
    (1 + (∑ i, ∑ j, X i j ^ 2) + alpha ^ 2) * p27PairNormSq u v
  simp only [p27PairNormSq, p27VecNormSq, Pi.add_apply, smul_eq_mul]
  change (∑ i, (u i + y i) ^ 2) + ∑ j, (alpha * v j) ^ 2 ≤
    (1 + S + alpha ^ 2) * (U + V)
  have huv : (∑ i, (u i + y i) ^ 2) = U + 2 * D + Y := by
    dsimp [U, D, Y]
    unfold p27VecNormSq
    simp_rw [add_sq, Finset.sum_add_distrib]
    rw [Finset.mul_sum]
    ring
  have hav : (∑ j, (alpha * v j) ^ 2) = alpha ^ 2 * V := by
    dsimp [V]
    unfold p27VecNormSq
    simp_rw [mul_pow, ← Finset.mul_sum]
  rw [huv, hav]
  nlinarith [mul_nonneg (sq_nonneg alpha) hU,
    mul_nonneg (sq_nonneg alpha) hV]

private lemma p27_w2_gain {k q : ℕ} (X : P27Coupling k q) (alpha : ℝ) :
    P27SquaredGainBound (p27W2 X alpha)
      (1 + (∑ i, ∑ j, X i j ^ 2) + alpha ^ 2) := by
  intro u v
  let S : ℝ := ∑ i, ∑ j, X i j ^ 2
  let U : ℝ := p27VecNormSq u
  let V : ℝ := p27VecNormSq v
  let y : P27Vector k := p27MatVec X v
  let Y : ℝ := p27VecNormSq y
  let D : ℝ := ∑ i, u i * y i
  have hS : 0 ≤ S := by
    dsimp [S]
    positivity
  have hU : 0 ≤ U := p27_vecNormSq_nonneg u
  have hV : 0 ≤ V := p27_vecNormSq_nonneg v
  have hY : 0 ≤ Y := p27_vecNormSq_nonneg y
  have hy : Y ≤ S * V := by
    simpa [S, V, Y, y] using p27_matVec_normSq_le X v
  have hD : D ^ 2 ≤ U * Y := by
    simpa [D, U, Y] using p27_dot_sq_le u y
  have hcross : 2 * (-alpha * D) ≤ (S + 1) * U + alpha ^ 2 * V := by
    apply p27_two_mul_le_add_of_sq_le_mul
    · positivity
    · positivity
    · calc
        (-alpha * D) ^ 2 = alpha ^ 2 * D ^ 2 := by ring
        _ ≤ alpha ^ 2 * (U * Y) := by gcongr
        _ ≤ alpha ^ 2 * (U * (S * V)) := by gcongr
        _ ≤ ((S + 1) * U) * (alpha ^ 2 * V) := by
          nlinarith [mul_nonneg (sq_nonneg alpha) hU,
            mul_nonneg (sq_nonneg alpha) hV]
  change p27PairNormSq (alpha • u - p27MatVec X v) v ≤
    (1 + (∑ i, ∑ j, X i j ^ 2) + alpha ^ 2) * p27PairNormSq u v
  simp only [p27PairNormSq, p27VecNormSq, Pi.sub_apply, smul_eq_mul]
  change (∑ i, (alpha * u i - y i) ^ 2) + ∑ j, v j ^ 2 ≤
    (1 + S + alpha ^ 2) * (U + V)
  have hau : (∑ i, (alpha * u i - y i) ^ 2) =
      alpha ^ 2 * U - 2 * alpha * D + Y := by
    dsimp [U, D, Y]
    unfold p27VecNormSq
    simp_rw [sub_sq, mul_pow, Finset.sum_add_distrib, Finset.sum_sub_distrib,
      ← Finset.mul_sum]
    simp_rw [Finset.mul_sum]
    ring_nf
  rw [hau]
  change alpha ^ 2 * U - 2 * alpha * D + Y + V ≤
    (1 + S + alpha ^ 2) * (U + V)
  nlinarith [mul_nonneg (sq_nonneg alpha) hU,
    mul_nonneg (sq_nonneg alpha) hV]

private lemma p27_sum_bound {k q : ℕ} (data : P27Theorem32Data k q) :
    (∑ i, ∑ j, data.X i j ^ 2) + data.alpha ^ 2 ≤
      data.f ^ 2 * (k : ℝ) * (q : ℝ) := by
  calc
    (∑ i, ∑ j, data.X i j ^ 2) + data.alpha ^ 2 ≤
        (∑ i, ∑ j, data.X i j ^ 2) +
          ∑ i, ∑ j, data.ratio i j ^ 2 := by
      gcongr
      exact data.alpha_sq_le
    _ = ∑ i, ∑ j, (data.X i j ^ 2 + data.ratio i j ^ 2) := by
      simp_rw [Finset.sum_add_distrib]
    _ ≤ ∑ _i : Fin k, ∑ _j : Fin q, data.f ^ 2 := by
      apply Finset.sum_le_sum
      intro i _
      apply Finset.sum_le_sum
      intro j _
      exact (data.p_lt_f i j).le
    _ = data.f ^ 2 * (k : ℝ) * (q : ℝ) := by
      simp
      ring

/-- P27-T3: the two strong rank-revealing bounds in Theorem 3.2. -/
theorem p27_t3_theorem3_2 {k q : ℕ} (data : P27Theorem32Data k q) :
    (∀ i, data.sigmaMTop i / p27StrongFactor k q data.f ≤ data.sigmaA i) ∧
    (∀ j, data.sigmaC j ≤
      data.sigmaMTail j * p27StrongFactor k q data.f) := by
  -- PROOF_START P27-T3-H001
  let gSq : ℝ := 1 + data.f ^ 2 * (k : ℝ) * (q : ℝ)
  have hgSq : 0 ≤ gSq := by
    dsimp [gSq]
    positivity
  have hsum := p27_sum_bound data
  have hw1 : P27SquaredGainBound (p27W1 data.X data.alpha) gSq := by
    intro u v
    calc
      p27PairNormSq (p27W1 data.X data.alpha u v).1
          (p27W1 data.X data.alpha u v).2 ≤
          (1 + (∑ i, ∑ j, data.X i j ^ 2) + data.alpha ^ 2) *
            p27PairNormSq u v := p27_w1_gain data.X data.alpha u v
      _ ≤ gSq * p27PairNormSq u v := by
        exact mul_le_mul_of_nonneg_right (by dsimp [gSq]; linarith)
          (by
            unfold p27PairNormSq
            exact add_nonneg (p27_vecNormSq_nonneg u) (p27_vecNormSq_nonneg v))
  have hw2 : P27SquaredGainBound (p27W2 data.X data.alpha) gSq := by
    intro u v
    calc
      p27PairNormSq (p27W2 data.X data.alpha u v).1
          (p27W2 data.X data.alpha u v).2 ≤
          (1 + (∑ i, ∑ j, data.X i j ^ 2) + data.alpha ^ 2) *
            p27PairNormSq u v := p27_w2_gain data.X data.alpha u v
      _ ≤ gSq * p27PairNormSq u v := by
        exact mul_le_mul_of_nonneg_right (by dsimp [gSq]; linarith)
          (by
            unfold p27PairNormSq
            exact add_nonneg (p27_vecNormSq_nonneg u) (p27_vecNormSq_nonneg v))
  have hsqrt : 0 < Real.sqrt gSq := Real.sqrt_pos.2 (by
    dsimp [gSq]
    nlinarith [mul_nonneg (mul_nonneg (sq_nonneg data.f) (Nat.cast_nonneg k))
      (Nat.cast_nonneg q)])
  constructor
  · intro i
    rw [p27StrongFactor]
    exact (div_le_iff₀ hsqrt).2 (data.hornJohnson_top gSq hgSq hw1 i)
  · intro j
    rw [p27StrongFactor]
    exact data.hornJohnson_tail gSq hgSq hw2 j

end HighamBench
