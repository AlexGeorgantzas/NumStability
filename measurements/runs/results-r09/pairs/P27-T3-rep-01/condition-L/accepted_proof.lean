import HighamBench.P27Definitions

namespace HighamBench

open scoped BigOperators

private lemma p27_matVec_normSq_le {k q : ℕ}
    (X : P27Coupling k q) (v : P27Vector q) :
    p27VecNormSq (p27MatVec X v) ≤
      (∑ i, ∑ j, X i j ^ 2) * p27VecNormSq v := by
  simp only [p27VecNormSq, p27MatVec]
  calc
    ∑ i, (∑ j, X i j * v j) ^ 2 ≤
        ∑ i, (∑ j, X i j ^ 2) * ∑ j, v j ^ 2 := by
      exact Finset.sum_le_sum fun i _ ↦
        Finset.sum_mul_sq_le_sq_mul_sq Finset.univ (X i) v
    _ = (∑ i, ∑ j, X i j ^ 2) * ∑ j, v j ^ 2 := by
      rw [Finset.sum_mul]

private lemma p27_vec_add_bound {n : ℕ}
    (a b : P27Vector n) {U V sa sb : ℝ}
    (hU : 0 ≤ U) (hV : 0 ≤ V) (hsa : 0 ≤ sa) (hsb : 0 ≤ sb)
    (ha : p27VecNormSq a ≤ sa * U)
    (hb : p27VecNormSq b ≤ sb * V) :
    p27VecNormSq (a + b) ≤ (sa + sb) * (U + V) := by
  let A := p27VecNormSq a
  let B := p27VecNormSq b
  let C := ∑ i, a i * b i
  have hA : 0 ≤ A := by
    dsimp [A, p27VecNormSq]
    positivity
  have hB : 0 ≤ B := by
    dsimp [B, p27VecNormSq]
    positivity
  have hC : C ≤ Real.sqrt A * Real.sqrt B := by
    dsimp [C, A, B, p27VecNormSq]
    exact Real.sum_mul_le_sqrt_mul_sqrt Finset.univ a b
  have hsU : 0 ≤ sa * U := mul_nonneg hsa hU
  have hsV : 0 ≤ sb * V := mul_nonneg hsb hV
  have hsqrtA : Real.sqrt A ≤ Real.sqrt sa * Real.sqrt U := by
    rw [← Real.sqrt_mul hsa]
    exact Real.sqrt_le_sqrt ha
  have hsqrtB : Real.sqrt B ≤ Real.sqrt sb * Real.sqrt V := by
    rw [← Real.sqrt_mul hsb]
    exact Real.sqrt_le_sqrt hb
  have hcross : C ≤
      (Real.sqrt sa * Real.sqrt U) * (Real.sqrt sb * Real.sqrt V) := by
    calc
      C ≤ Real.sqrt A * Real.sqrt B := hC
      _ ≤ (Real.sqrt sa * Real.sqrt U) * (Real.sqrt sb * Real.sqrt V) := by
        gcongr <;> positivity
  have hsasq : (Real.sqrt sa) ^ 2 = sa := Real.sq_sqrt hsa
  have hsbsq : (Real.sqrt sb) ^ 2 = sb := Real.sq_sqrt hsb
  have hUsq : (Real.sqrt U) ^ 2 = U := Real.sq_sqrt hU
  have hVsq : (Real.sqrt V) ^ 2 = V := Real.sq_sqrt hV
  have htwo : 2 * C ≤ sa * V + sb * U := by
    have hsq := sq_nonneg
      (Real.sqrt sa * Real.sqrt V - Real.sqrt sb * Real.sqrt U)
    nlinarith
  have hexpand : p27VecNormSq (a + b) = A + 2 * C + B := by
    dsimp [p27VecNormSq, A, B, C]
    simp_rw [add_sq]
    rw [Finset.sum_add_distrib, Finset.sum_add_distrib]
    simp_rw [mul_assoc]
    rw [← Finset.mul_sum]
  rw [hexpand]
  nlinarith

/-- P27-T3: the two strong rank-revealing bounds in Theorem 3.2. -/
theorem p27_t3_theorem3_2 {k q : ℕ} (data : P27Theorem32Data k q) :
    (∀ i, data.sigmaMTop i / p27StrongFactor k q data.f ≤ data.sigmaA i) ∧
    (∀ j, data.sigmaC j ≤
      data.sigmaMTail j * p27StrongFactor k q data.f) := by
  -- PROOF_START P27-T3-H001
  have hsum :
      (∑ i, ∑ j, data.X i j ^ 2) +
          (∑ i, ∑ j, data.ratio i j ^ 2) ≤
        data.f ^ 2 * (k : ℝ) * (q : ℝ) := by
    have h : (∑ i : Fin k, ∑ j : Fin q,
        (data.X i j ^ 2 + data.ratio i j ^ 2)) ≤
        ∑ _i : Fin k, ∑ _j : Fin q, data.f ^ 2 := by
      exact Finset.sum_le_sum fun i _ ↦
        Finset.sum_le_sum fun j _ ↦ (data.p_lt_f i j).le
    simp_rw [Finset.sum_add_distrib] at h
    calc
      _ ≤ (k : ℝ) * ((q : ℝ) * data.f ^ 2) := by
        simpa [Finset.sum_const, Fintype.card_fin, nsmul_eq_mul] using h
      _ = _ := by ring
  have hg : 0 ≤ 1 + data.f ^ 2 * (k : ℝ) * (q : ℝ) := by positivity
  have hW1 : P27SquaredGainBound (p27W1 data.X data.alpha)
      (1 + data.f ^ 2 * (k : ℝ) * (q : ℝ)) := by
    intro u v
    have hU : 0 ≤ p27VecNormSq u := by
      exact Finset.sum_nonneg fun _ _ ↦ sq_nonneg _
    have hV : 0 ≤ p27VecNormSq v := by
      exact Finset.sum_nonneg fun _ _ ↦ sq_nonneg _
    have hX : 0 ≤ ∑ i, ∑ j, data.X i j ^ 2 := by positivity
    have hadd := p27_vec_add_bound u (p27MatVec data.X v)
      hU hV (by positivity : (0 : ℝ) ≤ 1) hX
      (by simp) (p27_matVec_normSq_le data.X v)
    have hscale : p27VecNormSq (data.alpha • v) =
        data.alpha ^ 2 * p27VecNormSq v := by
      simp only [p27VecNormSq, Pi.smul_apply, smul_eq_mul, mul_pow]
      rw [Finset.mul_sum]
    simp only [P27SquaredGainBound, p27W1, p27PairNormSq] at *
    rw [hscale]
    nlinarith [data.alpha_sq_le]
  have hW2 : P27SquaredGainBound (p27W2 data.X data.alpha)
      (1 + data.f ^ 2 * (k : ℝ) * (q : ℝ)) := by
    intro u v
    have hU : 0 ≤ p27VecNormSq u := by
      exact Finset.sum_nonneg fun _ _ ↦ sq_nonneg _
    have hV : 0 ≤ p27VecNormSq v := by
      exact Finset.sum_nonneg fun _ _ ↦ sq_nonneg _
    have hX : 0 ≤ ∑ i, ∑ j, data.X i j ^ 2 := by positivity
    have hscale : p27VecNormSq (data.alpha • u) =
        data.alpha ^ 2 * p27VecNormSq u := by
      simp only [p27VecNormSq, Pi.smul_apply, smul_eq_mul, mul_pow]
      rw [Finset.mul_sum]
    have hneg : p27VecNormSq (-p27MatVec data.X v) ≤
        (∑ i, ∑ j, data.X i j ^ 2) * p27VecNormSq v := by
      simpa [p27VecNormSq] using p27_matVec_normSq_le data.X v
    have hadd := p27_vec_add_bound (data.alpha • u) (-p27MatVec data.X v)
      hU hV (sq_nonneg data.alpha) hX (le_of_eq hscale)
      hneg
    simp only [P27SquaredGainBound, p27W2, p27PairNormSq] at *
    rw [sub_eq_add_neg]
    nlinarith [data.alpha_sq_le]
  constructor
  · intro i
    have htop := data.hornJohnson_top
      (1 + data.f ^ 2 * (k : ℝ) * (q : ℝ)) hg hW1 i
    rw [p27StrongFactor]
    have hsqrt : 0 < Real.sqrt
        (1 + data.f ^ 2 * (k : ℝ) * (q : ℝ)) :=
      Real.sqrt_pos.2 (by positivity)
    exact (div_le_iff₀ hsqrt).2 htop
  · intro j
    exact data.hornJohnson_tail
      (1 + data.f ^ 2 * (k : ℝ) * (q : ℝ)) hg hW2 j

end HighamBench
