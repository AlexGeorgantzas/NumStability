import HighamBench.P27Definitions

namespace HighamBench

private lemma p27_matVec_sq_le {k q : ℕ} (X : P27Coupling k q)
    (v : P27Vector q) :
    p27VecNormSq (p27MatVec X v) ≤
      (∑ i, ∑ j, X i j ^ 2) * p27VecNormSq v := by
  unfold p27VecNormSq p27MatVec
  calc
    ∑ i, (∑ j, X i j * v j) ^ 2 ≤
        ∑ i, (∑ j, X i j ^ 2) * ∑ j, v j ^ 2 := by
      gcongr with i
      exact Finset.sum_mul_sq_le_sq_mul_sq Finset.univ (X i) v
    _ = (∑ i, ∑ j, X i j ^ 2) * ∑ j, v j ^ 2 := by
      rw [Finset.sum_mul]

private lemma p27_sum_add_sq_le {n : ℕ} (a b : P27Vector n)
    (ca cb U V : ℝ)
    (hca : 0 ≤ ca) (hcb : 0 ≤ cb) (hU : 0 ≤ U) (hV : 0 ≤ V)
    (ha : p27VecNormSq a ≤ ca * U)
    (hb : p27VecNormSq b ≤ cb * V) :
    p27VecNormSq (a + b) ≤ (ca + cb) * (U + V) := by
  let A : ℝ := p27VecNormSq a
  let B : ℝ := p27VecNormSq b
  let D : ℝ := ∑ i, a i * b i
  have hA : 0 ≤ A := by
    dsimp [A, p27VecNormSq]
    positivity
  have hB : 0 ≤ B := by
    dsimp [B, p27VecNormSq]
    positivity
  have hD : D ^ 2 ≤ A * B := by
    exact Finset.sum_mul_sq_le_sq_mul_sq Finset.univ a b
  have hAB : A * B ≤ (ca * U) * (cb * V) :=
    mul_le_mul ha hb hB (mul_nonneg hca hU)
  have hcross : 2 * D ≤ cb * U + ca * V := by
    have hleft : 0 ≤ cb * U := mul_nonneg hcb hU
    have hright : 0 ≤ ca * V := mul_nonneg hca hV
    have hsquare : 0 ≤ (cb * U - ca * V) ^ 2 := sq_nonneg _
    nlinarith [hD.trans hAB]
  change ∑ i, (a i + b i) ^ 2 ≤ _
  have hexpand : (∑ i, (a i + b i) ^ 2) = A + 2 * D + B := by
    dsimp [A, B, D, p27VecNormSq]
    simp_rw [add_sq]
    rw [Finset.sum_add_distrib, Finset.sum_add_distrib]
    rw [Finset.mul_sum]
    ring
  rw [hexpand]
  nlinarith

/-- P27-T3: the two strong rank-revealing bounds in Theorem 3.2. -/
theorem p27_t3_theorem3_2 {k q : ℕ} (data : P27Theorem32Data k q) :
    (∀ i, data.sigmaMTop i / p27StrongFactor k q data.f ≤ data.sigmaA i) ∧
    (∀ j, data.sigmaC j ≤
      data.sigmaMTail j * p27StrongFactor k q data.f) := by
  -- PROOF_START P27-T3-H001
  let S : ℝ := ∑ i, ∑ j, data.X i j ^ 2
  let R : ℝ := ∑ i, ∑ j, data.ratio i j ^ 2
  let G : ℝ := 1 + data.f ^ 2 * (k : ℝ) * (q : ℝ)
  have hS : 0 ≤ S := by
    dsimp [S]
    positivity
  have hR : 0 ≤ R := by
    dsimp [R]
    positivity
  have hcount : S + R ≤ data.f ^ 2 * (k : ℝ) * (q : ℝ) := by
    dsimp [S, R]
    calc
      (∑ i, ∑ j, data.X i j ^ 2) + ∑ i, ∑ j, data.ratio i j ^ 2 =
          ∑ i, ∑ j, (data.X i j ^ 2 + data.ratio i j ^ 2) := by
            simp_rw [Finset.sum_add_distrib]
      _ ≤ ∑ _i : Fin k, ∑ _j : Fin q, data.f ^ 2 := by
            gcongr with i hi j hj
            exact (data.p_lt_f i j).le
      _ = data.f ^ 2 * (k : ℝ) * (q : ℝ) := by
            simp
            ring
  have halpha : data.alpha ^ 2 ≤ R := data.alpha_sq_le
  have hSG : S + data.alpha ^ 2 ≤ data.f ^ 2 * (k : ℝ) * (q : ℝ) := by
    linarith
  have hG : 0 ≤ G := by
    dsimp [G]
    positivity
  have hgain1 : P27SquaredGainBound (p27W1 data.X data.alpha) G := by
    intro u v
    let U := p27VecNormSq u
    let V := p27VecNormSq v
    have hU : 0 ≤ U := by
      dsimp [U, p27VecNormSq]
      positivity
    have hV : 0 ≤ V := by
      dsimp [V, p27VecNormSq]
      positivity
    have htop : p27VecNormSq (u + p27MatVec data.X v) ≤
        (1 + S) * (U + V) := by
      apply p27_sum_add_sq_le u (p27MatVec data.X v) 1 S U V
      · positivity
      · exact hS
      · exact hU
      · exact hV
      · simp [U]
      · exact p27_matVec_sq_le data.X v
    have hbottom : p27VecNormSq (data.alpha • v) = data.alpha ^ 2 * V := by
      change (∑ i, (data.alpha * v i) ^ 2) =
        data.alpha ^ 2 * ∑ i, v i ^ 2
      simp_rw [mul_pow]
      rw [Finset.mul_sum]
    change p27VecNormSq (u + p27MatVec data.X v) +
      p27VecNormSq (data.alpha • v) ≤
        G * (p27VecNormSq u + p27VecNormSq v)
    rw [hbottom]
    change p27VecNormSq (u + p27MatVec data.X v) + data.alpha ^ 2 * V ≤
      G * (U + V)
    have hUV : 0 ≤ U + V := by positivity
    calc
      _ ≤ (1 + S) * (U + V) + data.alpha ^ 2 * V :=
        add_le_add htop le_rfl
      _ ≤ (1 + S + data.alpha ^ 2) * (U + V) := by
        nlinarith [mul_nonneg (sq_nonneg data.alpha) hU]
      _ ≤ G * (U + V) := by
        apply mul_le_mul_of_nonneg_right _ hUV
        dsimp [G]
        linarith
  have hgain2 : P27SquaredGainBound (p27W2 data.X data.alpha) G := by
    intro u v
    let U := p27VecNormSq u
    let V := p27VecNormSq v
    have hU : 0 ≤ U := by
      dsimp [U, p27VecNormSq]
      positivity
    have hV : 0 ≤ V := by
      dsimp [V, p27VecNormSq]
      positivity
    have halphaU : p27VecNormSq (data.alpha • u) = data.alpha ^ 2 * U := by
      change (∑ i, (data.alpha * u i) ^ 2) =
        data.alpha ^ 2 * ∑ i, u i ^ 2
      simp_rw [mul_pow]
      rw [Finset.mul_sum]
    have hnegX : p27VecNormSq (-p27MatVec data.X v) ≤ S * V := by
      simpa [p27VecNormSq] using p27_matVec_sq_le data.X v
    have htop : p27VecNormSq (data.alpha • u + -p27MatVec data.X v) ≤
        (data.alpha ^ 2 + S) * (U + V) := by
      apply p27_sum_add_sq_le (data.alpha • u) (-p27MatVec data.X v)
        (data.alpha ^ 2) S U V
      · positivity
      · exact hS
      · exact hU
      · exact hV
      · exact halphaU.le
      · exact hnegX
    change p27VecNormSq (data.alpha • u - p27MatVec data.X v) +
      p27VecNormSq v ≤ G * (p27VecNormSq u + p27VecNormSq v)
    rw [show data.alpha • u - p27MatVec data.X v =
      data.alpha • u + -p27MatVec data.X v by rw [sub_eq_add_neg]]
    change p27VecNormSq (data.alpha • u + -p27MatVec data.X v) + V ≤
      G * (U + V)
    have hUV : 0 ≤ U + V := by positivity
    calc
      _ ≤ (data.alpha ^ 2 + S) * (U + V) + V :=
        add_le_add htop le_rfl
      _ ≤ (1 + S + data.alpha ^ 2) * (U + V) := by
        nlinarith
      _ ≤ G * (U + V) := by
        apply mul_le_mul_of_nonneg_right _ hUV
        dsimp [G]
        linarith
  have hfactor : p27StrongFactor k q data.f = Real.sqrt G := by
    rfl
  have hfactor_pos : 0 < p27StrongFactor k q data.f := by
    rw [hfactor, Real.sqrt_pos]
    dsimp [G]
    positivity
  constructor
  · intro i
    have h := data.hornJohnson_top G hG hgain1 i
    rw [← hfactor] at h
    exact (div_le_iff₀ hfactor_pos).2 h
  · intro j
    have h := data.hornJohnson_tail G hG hgain2 j
    rwa [← hfactor] at h

end HighamBench
