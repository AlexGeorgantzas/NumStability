import HighamBench.P27Definitions

namespace HighamBench

private lemma p27_two_mul_le_add_of_sq_le_mul {a b c : ℝ}
    (hb : 0 ≤ b) (hc : 0 ≤ c) (h : a ^ 2 ≤ b * c) :
    2 * a ≤ b + c := by
  nlinarith [sq_nonneg (b - c)]

private lemma p27_bilinear_sq_le {k q : ℕ} (X : P27Coupling k q)
    (u : P27Vector k) (v : P27Vector q) :
    (∑ i, ∑ j, X i j * (u i * v j)) ^ 2 ≤
      (∑ i, ∑ j, X i j ^ 2) *
        ((∑ i, u i ^ 2) * ∑ j, v j ^ 2) := by
  have h := Finset.sum_mul_sq_le_sq_mul_sq
    (Finset.univ ×ˢ Finset.univ)
    (fun p : Fin k × Fin q ↦ X p.1 p.2)
    (fun p : Fin k × Fin q ↦ u p.1 * v p.2)
  have huv :
      (∑ i : Fin k, ∑ j : Fin q, (u i * v j) ^ 2) =
        (∑ i, u i ^ 2) * ∑ j, v j ^ 2 := by
    simp_rw [mul_pow]
    simp_rw [← Finset.mul_sum]
    rw [Finset.sum_mul]
  calc
    (∑ i, ∑ j, X i j * (u i * v j)) ^ 2 =
        (∑ p ∈ Finset.univ ×ˢ Finset.univ,
          X p.1 p.2 * (u p.1 * v p.2)) ^ 2 := by
            rw [Finset.sum_product]
    _ ≤ (∑ p ∈ Finset.univ ×ˢ Finset.univ, X p.1 p.2 ^ 2) *
          ∑ p ∈ Finset.univ ×ˢ Finset.univ,
            (u p.1 * v p.2) ^ 2 := h
    _ = (∑ i, ∑ j, X i j ^ 2) *
          ((∑ i, u i ^ 2) * ∑ j, v j ^ 2) := by
            rw [Finset.sum_product, Finset.sum_product, huv]

private lemma p27_matVec_norm_sq_le {k q : ℕ} (X : P27Coupling k q)
    (v : P27Vector q) :
    (∑ i, (p27MatVec X v i) ^ 2) ≤
      (∑ i, ∑ j, X i j ^ 2) * ∑ j, v j ^ 2 := by
  unfold p27MatVec
  calc
    (∑ i, (∑ j, X i j * v j) ^ 2) ≤
        ∑ i, (∑ j, X i j ^ 2) * ∑ j, v j ^ 2 := by
          apply Finset.sum_le_sum
          intro i hi
          exact Finset.sum_mul_sq_le_sq_mul_sq Finset.univ (X i) v
    _ = (∑ i, ∑ j, X i j ^ 2) * ∑ j, v j ^ 2 := by
          rw [Finset.sum_mul]

private lemma p27_gain_bound_w1 {k q : ℕ} (X : P27Coupling k q)
    (alpha : ℝ) :
    P27SquaredGainBound (p27W1 X alpha)
      (1 + (∑ i, ∑ j, X i j ^ 2) + alpha ^ 2) := by
  intro u v
  let U : ℝ := ∑ i, u i ^ 2
  let V : ℝ := ∑ j, v j ^ 2
  let S : ℝ := ∑ i, ∑ j, X i j ^ 2
  let D : ℝ := ∑ i, ∑ j, X i j * (u i * v j)
  let Y : ℝ := ∑ i, (p27MatVec X v i) ^ 2
  have hU : 0 ≤ U := Finset.sum_nonneg fun _ _ ↦ sq_nonneg _
  have hV : 0 ≤ V := Finset.sum_nonneg fun _ _ ↦ sq_nonneg _
  have hS : 0 ≤ S := Finset.sum_nonneg fun _ _ ↦
    Finset.sum_nonneg fun _ _ ↦ sq_nonneg _
  have hDsq : D ^ 2 ≤ S * (U * V) := by
    exact p27_bilinear_sq_le X u v
  have hcross : 2 * D ≤ S * U + V := by
    apply p27_two_mul_le_add_of_sq_le_mul (mul_nonneg hS hU) hV
    nlinarith
  have hY : Y ≤ S * V := p27_matVec_norm_sq_le X v
  have hdot : ∑ i, u i * p27MatVec X v i = D := by
    dsimp [D, p27MatVec]
    apply Finset.sum_congr rfl
    intro i hi
    rw [Finset.mul_sum]
    apply Finset.sum_congr rfl
    intro j hj
    ring
  have h_expand :
      p27PairNormSq (p27W1 X alpha u v).1 (p27W1 X alpha u v).2 =
        U + 2 * D + Y + alpha ^ 2 * V := by
    simp only [p27PairNormSq, p27VecNormSq, p27W1, Pi.add_apply,
      smul_eq_mul]
    dsimp [U, V, D, Y]
    simp_rw [add_sq]
    simp_rw [Finset.sum_add_distrib]
    rw [show (∑ i, 2 * u i * p27MatVec X v i) = 2 * D by
      rw [← hdot, Finset.mul_sum]
      apply Finset.sum_congr rfl
      intro i hi
      ring]
    rw [show (∑ j, (alpha * v j) ^ 2) = alpha ^ 2 * ∑ j, v j ^ 2 by
      rw [Finset.mul_sum]
      apply Finset.sum_congr rfl
      intro j hj
      ring]
  rw [h_expand]
  change U + 2 * D + Y + alpha ^ 2 * V ≤
    (1 + S + alpha ^ 2) * (U + V)
  nlinarith [sq_nonneg alpha]

private lemma p27_gain_bound_w2 {k q : ℕ} (X : P27Coupling k q)
    (alpha : ℝ) :
    P27SquaredGainBound (p27W2 X alpha)
      (1 + (∑ i, ∑ j, X i j ^ 2) + alpha ^ 2) := by
  intro u v
  let U : ℝ := ∑ i, u i ^ 2
  let V : ℝ := ∑ j, v j ^ 2
  let S : ℝ := ∑ i, ∑ j, X i j ^ 2
  let D : ℝ := ∑ i, ∑ j, X i j * (u i * v j)
  let Y : ℝ := ∑ i, (p27MatVec X v i) ^ 2
  have hU : 0 ≤ U := Finset.sum_nonneg fun _ _ ↦ sq_nonneg _
  have hV : 0 ≤ V := Finset.sum_nonneg fun _ _ ↦ sq_nonneg _
  have hS : 0 ≤ S := Finset.sum_nonneg fun _ _ ↦
    Finset.sum_nonneg fun _ _ ↦ sq_nonneg _
  have hDsq : D ^ 2 ≤ S * (U * V) := by
    exact p27_bilinear_sq_le X u v
  have hcross : -2 * alpha * D ≤ S * U + alpha ^ 2 * V := by
    have hscaled : (-alpha * D) ^ 2 ≤ (S * U) * (alpha ^ 2 * V) := by
      have hmul := mul_le_mul_of_nonneg_left hDsq (sq_nonneg alpha)
      nlinarith
    have h := p27_two_mul_le_add_of_sq_le_mul
      (a := -alpha * D) (mul_nonneg hS hU)
      (mul_nonneg (sq_nonneg alpha) hV) hscaled
    nlinarith
  have hY : Y ≤ S * V := p27_matVec_norm_sq_le X v
  have hdot : ∑ i, u i * p27MatVec X v i = D := by
    dsimp [D, p27MatVec]
    apply Finset.sum_congr rfl
    intro i hi
    rw [Finset.mul_sum]
    apply Finset.sum_congr rfl
    intro j hj
    ring
  have h_expand :
      p27PairNormSq (p27W2 X alpha u v).1 (p27W2 X alpha u v).2 =
        alpha ^ 2 * U - 2 * alpha * D + Y + V := by
    simp only [p27PairNormSq, p27VecNormSq, p27W2, Pi.sub_apply,
      smul_eq_mul]
    dsimp [U, V, D, Y]
    simp_rw [sub_sq]
    simp_rw [Finset.sum_add_distrib, Finset.sum_sub_distrib]
    rw [show (∑ i, (alpha * u i) ^ 2) = alpha ^ 2 * ∑ i, u i ^ 2 by
      rw [Finset.mul_sum]
      apply Finset.sum_congr rfl
      intro i hi
      ring]
    rw [show (∑ i, 2 * (alpha * u i) * p27MatVec X v i) =
        2 * alpha * D by
      rw [← hdot]
      rw [Finset.mul_sum]
      apply Finset.sum_congr rfl
      intro i hi
      ring]
  rw [h_expand]
  change alpha ^ 2 * U - 2 * alpha * D + Y + V ≤
    (1 + S + alpha ^ 2) * (U + V)
  nlinarith [sq_nonneg alpha]

/-- P27-T3: the two strong rank-revealing bounds in Theorem 3.2. -/
theorem p27_t3_theorem3_2 {k q : ℕ} (data : P27Theorem32Data k q) :
    (∀ i, data.sigmaMTop i / p27StrongFactor k q data.f ≤ data.sigmaA i) ∧
    (∀ j, data.sigmaC j ≤
      data.sigmaMTail j * p27StrongFactor k q data.f) := by
  -- PROOF_START P27-T3-H001
  let S : ℝ := ∑ i, ∑ j, data.X i j ^ 2
  let T : ℝ := ∑ i, ∑ j, data.ratio i j ^ 2
  let gSq : ℝ := 1 + data.f ^ 2 * (k : ℝ) * (q : ℝ)
  have hS : 0 ≤ S := Finset.sum_nonneg fun _ _ ↦
    Finset.sum_nonneg fun _ _ ↦ sq_nonneg _
  have hT : 0 ≤ T := Finset.sum_nonneg fun _ _ ↦
    Finset.sum_nonneg fun _ _ ↦ sq_nonneg _
  have hentrySum : S + T ≤ data.f ^ 2 * (k : ℝ) * (q : ℝ) := by
    calc
      S + T = ∑ i, ∑ j, (data.X i j ^ 2 + data.ratio i j ^ 2) := by
        dsimp [S, T]
        simp_rw [Finset.sum_add_distrib]
      _ ≤ ∑ i, ∑ j, data.f ^ 2 := by
        apply Finset.sum_le_sum
        intro i hi
        apply Finset.sum_le_sum
        intro j hj
        exact (data.p_lt_f i j).le
      _ = data.f ^ 2 * (k : ℝ) * (q : ℝ) := by
        simp
        ring
  have hSa : S + data.alpha ^ 2 ≤
      data.f ^ 2 * (k : ℝ) * (q : ℝ) := by
    dsimp [T] at hT
    have halpha : data.alpha ^ 2 ≤ T := data.alpha_sq_le
    nlinarith
  have hgSq : 0 ≤ gSq := by
    dsimp [gSq]
    positivity
  have hgSq_pos : 0 < gSq := by
    dsimp [gSq]
    positivity
  have hpair_nonneg : ∀ (u : P27Vector k) (v : P27Vector q),
      0 ≤ p27PairNormSq u v := by
    intro u v
    unfold p27PairNormSq p27VecNormSq
    positivity
  have hW1 : P27SquaredGainBound (p27W1 data.X data.alpha) gSq := by
    intro u v
    calc
      p27PairNormSq (p27W1 data.X data.alpha u v).1
          (p27W1 data.X data.alpha u v).2 ≤
          (1 + S + data.alpha ^ 2) * p27PairNormSq u v := by
            simpa only [S] using p27_gain_bound_w1 data.X data.alpha u v
      _ ≤ gSq * p27PairNormSq u v := by
        apply mul_le_mul_of_nonneg_right _ (hpair_nonneg u v)
        dsimp [gSq]
        nlinarith
  have hW2 : P27SquaredGainBound (p27W2 data.X data.alpha) gSq := by
    intro u v
    calc
      p27PairNormSq (p27W2 data.X data.alpha u v).1
          (p27W2 data.X data.alpha u v).2 ≤
          (1 + S + data.alpha ^ 2) * p27PairNormSq u v := by
            simpa only [S] using p27_gain_bound_w2 data.X data.alpha u v
      _ ≤ gSq * p27PairNormSq u v := by
        apply mul_le_mul_of_nonneg_right _ (hpair_nonneg u v)
        dsimp [gSq]
        nlinarith
  have htop := data.hornJohnson_top gSq hgSq hW1
  have htail := data.hornJohnson_tail gSq hgSq hW2
  have hsqrt_pos : 0 < Real.sqrt gSq := Real.sqrt_pos.2 hgSq_pos
  constructor
  · intro i
    rw [p27StrongFactor]
    change data.sigmaMTop i / Real.sqrt gSq ≤ data.sigmaA i
    exact (div_le_iff₀ hsqrt_pos).2 (htop i)
  · intro j
    rw [p27StrongFactor]
    change data.sigmaC j ≤ data.sigmaMTail j * Real.sqrt gSq
    exact htail j

end HighamBench
