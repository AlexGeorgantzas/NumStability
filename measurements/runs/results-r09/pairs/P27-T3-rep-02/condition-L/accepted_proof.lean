import HighamBench.P27Definitions

namespace HighamBench

open scoped BigOperators

private lemma p27_two_mul_le_add_of_sq_le_mul {a b c : ℝ}
    (ha : 0 ≤ a) (hb : 0 ≤ b) (h : c ^ 2 ≤ a * b) :
    2 * c ≤ a + b := by
  nlinarith [sq_nonneg (a - b), sq_nonneg (2 * c + a + b)]

private lemma p27_matVec_normSq_le {k q : ℕ}
    (X : P27Coupling k q) (v : P27Vector q) :
    p27VecNormSq (p27MatVec X v) ≤
      (∑ i, ∑ j, X i j ^ 2) * p27VecNormSq v := by
  unfold p27VecNormSq p27MatVec
  calc
    ∑ i, (∑ j, X i j * v j) ^ 2 ≤
        ∑ i, (∑ j, X i j ^ 2) * (∑ j, v j ^ 2) := by
      apply Finset.sum_le_sum
      intro i hi
      exact Finset.sum_mul_sq_le_sq_mul_sq Finset.univ
        (fun j ↦ X i j) (fun j ↦ v j)
    _ = (∑ i, ∑ j, X i j ^ 2) * (∑ j, v j ^ 2) := by
      rw [Finset.sum_mul]

private lemma p27_inner_matVec_sq_le {k q : ℕ}
    (X : P27Coupling k q) (u : P27Vector k) (v : P27Vector q) :
    (∑ i, u i * p27MatVec X v i) ^ 2 ≤
      p27VecNormSq u *
        ((∑ i, ∑ j, X i j ^ 2) * p27VecNormSq v) := by
  have hcs := Finset.sum_mul_sq_le_sq_mul_sq (Finset.univ : Finset (Fin k))
    u (p27MatVec X v)
  have hu : 0 ≤ p27VecNormSq u := by
    exact Finset.sum_nonneg (fun i _ ↦ sq_nonneg (u i))
  exact hcs.trans (mul_le_mul_of_nonneg_left (p27_matVec_normSq_le X v) hu)

private lemma p27_pairNormSq_nonneg {k q : ℕ}
    (u : P27Vector k) (v : P27Vector q) :
    0 ≤ p27PairNormSq u v := by
  unfold p27PairNormSq p27VecNormSq
  positivity

private lemma p27_w1_gain_bound {k q : ℕ}
    (X : P27Coupling k q) (alpha : ℝ) :
    P27SquaredGainBound (p27W1 X alpha)
      (1 + (∑ i, ∑ j, X i j ^ 2) + alpha ^ 2) := by
  intro u v
  let U : ℝ := p27VecNormSq u
  let V : ℝ := p27VecNormSq v
  let Y : ℝ := p27VecNormSq (p27MatVec X v)
  let C : ℝ := ∑ i, u i * p27MatVec X v i
  let S : ℝ := ∑ i, ∑ j, X i j ^ 2
  have hU : 0 ≤ U := by
    dsimp [U, p27VecNormSq]
    positivity
  have hV : 0 ≤ V := by
    dsimp [V, p27VecNormSq]
    positivity
  have hS : 0 ≤ S := by
    dsimp [S]
    positivity
  have ha : 0 ≤ alpha ^ 2 := sq_nonneg alpha
  have hY : Y ≤ S * V := by
    simpa [Y, S, V] using p27_matVec_normSq_le X v
  have hC_sq : C ^ 2 ≤ U * (S * V) := by
    simpa [C, U, S, V] using p27_inner_matVec_sq_le X u v
  have hcross : 2 * C ≤ S * U + V := by
    apply p27_two_mul_le_add_of_sq_le_mul
    · positivity
    · exact hV
    · simpa [mul_assoc, mul_left_comm, mul_comm] using hC_sq
  have hexpand :
      p27PairNormSq (p27W1 X alpha u v).1 (p27W1 X alpha u v).2 =
        U + 2 * C + Y + alpha ^ 2 * V := by
    dsimp [p27PairNormSq, p27W1, p27VecNormSq, U, V, Y, C]
    calc
      (∑ i, (u i + p27MatVec X v i) ^ 2) + ∑ j, (alpha * v j) ^ 2 =
          (∑ i, (u i ^ 2 + 2 * (u i * p27MatVec X v i) +
            p27MatVec X v i ^ 2)) + ∑ j, alpha ^ 2 * v j ^ 2 := by
        congr 1 <;> apply Finset.sum_congr rfl <;> intro i hi <;> ring
      _ = (∑ i, u i ^ 2) + 2 * (∑ i, u i * p27MatVec X v i) +
          (∑ i, p27MatVec X v i ^ 2) + alpha ^ 2 * (∑ j, v j ^ 2) := by
        simp only [Finset.sum_add_distrib, ← Finset.mul_sum]
  rw [hexpand]
  dsimp [p27PairNormSq]
  change U + 2 * C + Y + alpha ^ 2 * V ≤
    (1 + S + alpha ^ 2) * (U + V)
  nlinarith [mul_nonneg ha hU]

private lemma p27_w2_gain_bound {k q : ℕ}
    (X : P27Coupling k q) (alpha : ℝ) :
    P27SquaredGainBound (p27W2 X alpha)
      (1 + (∑ i, ∑ j, X i j ^ 2) + alpha ^ 2) := by
  intro u v
  let U : ℝ := p27VecNormSq u
  let V : ℝ := p27VecNormSq v
  let Y : ℝ := p27VecNormSq (p27MatVec X v)
  let C : ℝ := ∑ i, u i * p27MatVec X v i
  let S : ℝ := ∑ i, ∑ j, X i j ^ 2
  have hU : 0 ≤ U := by
    dsimp [U, p27VecNormSq]
    positivity
  have hV : 0 ≤ V := by
    dsimp [V, p27VecNormSq]
    positivity
  have hS : 0 ≤ S := by
    dsimp [S]
    positivity
  have ha : 0 ≤ alpha ^ 2 := sq_nonneg alpha
  have hY : Y ≤ S * V := by
    simpa [Y, S, V] using p27_matVec_normSq_le X v
  have hC_sq : C ^ 2 ≤ U * (S * V) := by
    simpa [C, U, S, V] using p27_inner_matVec_sq_le X u v
  have hac_sq : (-alpha * C) ^ 2 ≤ (S * U) * (alpha ^ 2 * V) := by
    calc
      (-alpha * C) ^ 2 = alpha ^ 2 * C ^ 2 := by ring
      _ ≤ alpha ^ 2 * (U * (S * V)) :=
        mul_le_mul_of_nonneg_left hC_sq ha
      _ = (S * U) * (alpha ^ 2 * V) := by ring
  have hcross : -2 * alpha * C ≤ S * U + alpha ^ 2 * V := by
    have := p27_two_mul_le_add_of_sq_le_mul
      (mul_nonneg hS hU) (mul_nonneg ha hV) hac_sq
    nlinarith
  have hexpand :
      p27PairNormSq (p27W2 X alpha u v).1 (p27W2 X alpha u v).2 =
        alpha ^ 2 * U - 2 * alpha * C + Y + V := by
    dsimp [p27PairNormSq, p27W2, p27VecNormSq, U, V, Y, C]
    calc
      (∑ i, (alpha * u i - p27MatVec X v i) ^ 2) + ∑ j, v j ^ 2 =
          (∑ i, (alpha ^ 2 * u i ^ 2 -
            2 * alpha * (u i * p27MatVec X v i) +
            p27MatVec X v i ^ 2)) + ∑ j, v j ^ 2 := by
        congr 1
        apply Finset.sum_congr rfl
        intro i hi
        ring
      _ = alpha ^ 2 * (∑ i, u i ^ 2) -
          2 * alpha * (∑ i, u i * p27MatVec X v i) +
          (∑ i, p27MatVec X v i ^ 2) + ∑ j, v j ^ 2 := by
        simp only [Finset.sum_add_distrib, Finset.sum_sub_distrib,
          ← Finset.mul_sum]
  rw [hexpand]
  dsimp [p27PairNormSq]
  change alpha ^ 2 * U - 2 * alpha * C + Y + V ≤
    (1 + S + alpha ^ 2) * (U + V)
  nlinarith

/-- P27-T3: the two strong rank-revealing bounds in Theorem 3.2. -/
theorem p27_t3_theorem3_2 {k q : ℕ} (data : P27Theorem32Data k q) :
    (∀ i, data.sigmaMTop i / p27StrongFactor k q data.f ≤ data.sigmaA i) ∧
    (∀ j, data.sigmaC j ≤
      data.sigmaMTail j * p27StrongFactor k q data.f) := by
  -- PROOF_START P27-T3-H001
  let S : ℝ := ∑ i, ∑ j, data.X i j ^ 2
  let T : ℝ := ∑ i, ∑ j, data.ratio i j ^ 2
  let G : ℝ := 1 + data.f ^ 2 * (k : ℝ) * (q : ℝ)
  have hST : S + T ≤ data.f ^ 2 * (k : ℝ) * (q : ℝ) := by
    have h := Finset.sum_le_sum fun i (_ : i ∈ (Finset.univ : Finset (Fin k))) ↦
      Finset.sum_le_sum fun j (_ : j ∈ (Finset.univ : Finset (Fin q))) ↦
        (data.p_lt_f i j).le
    simpa [S, T, Finset.sum_add_distrib, mul_assoc, mul_left_comm, mul_comm]
      using h
  have hSa : S + data.alpha ^ 2 ≤
      data.f ^ 2 * (k : ℝ) * (q : ℝ) := by
    have haT : data.alpha ^ 2 ≤ T := by
      simpa [T] using data.alpha_sq_le
    nlinarith
  have hG : 0 ≤ G := by
    dsimp [G]
    positivity
  have hgain1 : P27SquaredGainBound (p27W1 data.X data.alpha) G := by
    intro u v
    have hbase := p27_w1_gain_bound data.X data.alpha u v
    have hnorm := p27_pairNormSq_nonneg u v
    dsimp [G, S] at hSa ⊢
    exact hbase.trans (mul_le_mul_of_nonneg_right (by nlinarith) hnorm)
  have hgain2 : P27SquaredGainBound (p27W2 data.X data.alpha) G := by
    intro u v
    have hbase := p27_w2_gain_bound data.X data.alpha u v
    have hnorm := p27_pairNormSq_nonneg u v
    dsimp [G, S] at hSa ⊢
    exact hbase.trans (mul_le_mul_of_nonneg_right (by nlinarith) hnorm)
  have hfactor : p27StrongFactor k q data.f = Real.sqrt G := by
    rfl
  have hfactor_pos : 0 < p27StrongFactor k q data.f := by
    unfold p27StrongFactor
    positivity
  constructor
  · intro i
    have htop := data.hornJohnson_top G hG hgain1 i
    rw [hfactor] at hfactor_pos ⊢
    exact (div_le_iff₀ hfactor_pos).2 htop
  · intro j
    simpa [hfactor] using data.hornJohnson_tail G hG hgain2 j

end HighamBench
