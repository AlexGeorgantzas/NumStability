import Mathlib
import NumStability.Analysis.Summation.ErrorBounds

namespace HighamBenchCandidate

open scoped BigOperators

/-- Exact softmax (paper equation (1.2)) on a positive number of entries. -/
noncomputable def softmax (n : ℕ) (x : Fin (n + 1) → ℝ) : Fin (n + 1) → ℝ :=
  fun j => Real.exp (x j) / ∑ i : Fin (n + 1), Real.exp (x i)

/-- The stored exponential from line 3 of the basic Algorithm 3.1. -/
noncomputable def roundedExp (n : ℕ) (x : Fin (n + 1) → ℝ)
    (δexp : Fin (n + 1) → ℝ) : Fin (n + 1) → ℝ :=
  fun i => Real.exp (x i) * (1 + δexp i)

/-- Lines 1–5 of Algorithm 3.1. The addition from zero is exact, so there
are `n` rounded additions for `n + 1` stored exponentials. Each subsequent
addition has its own standard-model relative error. -/
noncomputable def roundedDenominator (n : ℕ) (x : Fin (n + 1) → ℝ)
    (δexp : Fin (n + 1) → ℝ) (δadd : Fin n → ℝ) : ℝ :=
  let w := roundedExp n x δexp
  Fin.foldl n (fun s i => (s + w i.succ) * (1 + δadd i)) (w 0)

/-- Lines 7–9 of Algorithm 3.1, with one rounded division per component. -/
noncomputable def roundedSoftmax (n : ℕ) (x : Fin (n + 1) → ℝ)
    (δexp : Fin (n + 1) → ℝ) (δadd : Fin n → ℝ)
    (δdiv : Fin (n + 1) → ℝ) : Fin (n + 1) → ℝ :=
  fun j =>
    (roundedExp n x δexp j / roundedDenominator n x δexp δadd) *
      (1 + δdiv j)

private theorem fold_relative_error (fp : NumStability.FPModel) (n : ℕ)
    (v : Fin n → ℝ) (s : ℝ) (δ : Fin n → ℝ)
    (hs : 0 ≤ s) (hv : ∀ i, 0 ≤ v i)
    (hδ : ∀ i, |δ i| ≤ fp.u) (hn : NumStability.gammaValid fp n) :
    |Fin.foldl n (fun acc i => (acc + v i) * (1 + δ i)) s -
      (s + ∑ i, v i)| ≤ NumStability.gamma fp n * (s + ∑ i, v i) := by
  let P : ℝ := ∏ i : Fin n, (1 + δ i)
  let S : Fin n → ℝ := NumStability.sumSuffixErrorProduct n δ
  have hP : |P - 1| ≤ NumStability.gamma fp n := by
    obtain ⟨θ, hθ, hprod⟩ := NumStability.prod_error_bound fp n δ hδ hn
    change P = 1 + θ at hprod
    rw [hprod]
    simpa using hθ
  have hS (i : Fin n) : |S i - 1| ≤ NumStability.gamma fp n := by
    have hni : NumStability.gammaValid fp (n - i.val) :=
      NumStability.gammaValid_mono fp (by omega) hn
    obtain ⟨θ, hθ, hprod⟩ :=
      NumStability.sumSuffixErrorProduct_exists_theta_le_gamma fp n δ hδ i hni
    change S i = 1 + θ at hprod
    rw [hprod]
    simpa using hθ.trans (NumStability.gamma_mono fp (by omega) hn)
  have hfold := NumStability.foldl_add_mul_one_add_suffix_expansion n v s δ
  change Fin.foldl n (fun acc i => (acc + v i) * (1 + δ i)) s =
    s * P + ∑ i, v i * S i at hfold
  have hrewrite :
      Fin.foldl n (fun acc i => (acc + v i) * (1 + δ i)) s -
          (s + ∑ i, v i) =
        s * (P - 1) + ∑ i, v i * (S i - 1) := by
    rw [hfold]
    simp_rw [mul_sub]
    rw [Finset.sum_sub_distrib]
    simp
    ring
  rw [hrewrite]
  calc
    |s * (P - 1) + ∑ i, v i * (S i - 1)| ≤
        |s * (P - 1)| + |∑ i, v i * (S i - 1)| := abs_add_le _ _
    _ ≤ |s * (P - 1)| + ∑ i, |v i * (S i - 1)| := by
      exact add_le_add_right (Finset.abs_sum_le_sum_abs _ _) _
    _ = s * |P - 1| + ∑ i, v i * |S i - 1| := by
      simp [abs_mul, abs_of_nonneg hs, abs_of_nonneg (hv _)]
    _ ≤ s * NumStability.gamma fp n +
          ∑ i, v i * NumStability.gamma fp n := by
      apply add_le_add (mul_le_mul_of_nonneg_left hP hs)
      exact Finset.sum_le_sum (fun i _ => mul_le_mul_of_nonneg_left (hS i) (hv i))
    _ = NumStability.gamma fp n * (s + ∑ i, v i) := by
      rw [← Finset.sum_mul]
      ring

private theorem denominator_relative_error (fp : NumStability.FPModel)
    (n : ℕ) (x : Fin (n + 1) → ℝ)
    (δexp : Fin (n + 1) → ℝ) (δadd : Fin n → ℝ)
    (hsmall : fp.u ≤ 1) (he : ∀ i, |δexp i| ≤ fp.u)
    (ha : ∀ i, |δadd i| ≤ fp.u)
    (hn : NumStability.gammaValid fp n) :
    let s := ∑ i : Fin (n + 1), Real.exp (x i)
    |roundedDenominator n x δexp δadd - s| ≤
      (NumStability.gamma fp n * (1 + fp.u) + fp.u) * s := by
  let w := roundedExp n x δexp
  let s : ℝ := ∑ i : Fin (n + 1), Real.exp (x i)
  let W : ℝ := ∑ i : Fin (n + 1), w i
  have hu0 : 0 ≤ fp.u := fp.u_nonneg
  have hw0 (i : Fin (n + 1)) : 0 ≤ w i := by
    have hδlow : -fp.u ≤ δexp i := (abs_le.mp (he i)).1
    exact mul_nonneg (Real.exp_pos _).le (by linarith)
  have hwe (i : Fin (n + 1)) :
      |w i - Real.exp (x i)| ≤ fp.u * Real.exp (x i) := by
    have hw : w i - Real.exp (x i) = Real.exp (x i) * δexp i := by
      simp [w, roundedExp]; ring
    rw [hw, abs_mul, abs_of_pos (Real.exp_pos _)]
    nlinarith [he i, (Real.exp_pos (x i)).le]
  have hWerror : |W - s| ≤ fp.u * s := by
    have hsum : W - s = ∑ i : Fin (n + 1), (w i - Real.exp (x i)) := by
      simp [W, s, Finset.sum_sub_distrib]
    rw [hsum]
    calc
      |∑ i : Fin (n + 1), (w i - Real.exp (x i))| ≤
          ∑ i : Fin (n + 1), |w i - Real.exp (x i)| :=
        Finset.abs_sum_le_sum_abs _ _
      _ ≤ ∑ i : Fin (n + 1), fp.u * Real.exp (x i) :=
        Finset.sum_le_sum (fun i _ => hwe i)
      _ = fp.u * s := by simp [s, Finset.mul_sum]
  have hs0 : 0 ≤ s := by
    dsimp [s]
    exact Finset.sum_nonneg (fun i _ => (Real.exp_pos (x i)).le)
  have hWupper : W ≤ (1 + fp.u) * s := by
    have := le_abs_self (W - s)
    nlinarith
  have hγ0 : 0 ≤ NumStability.gamma fp n := NumStability.gamma_nonneg fp hn
  have hfold :
      |roundedDenominator n x δexp δadd - W| ≤
        NumStability.gamma fp n * W := by
    have h := fold_relative_error fp n (fun i => w i.succ) (w 0) δadd
      (hw0 0) (fun i => hw0 i.succ) ha hn
    simpa [roundedDenominator, w, W, Fin.sum_univ_succ] using h
  dsimp
  calc
    |roundedDenominator n x δexp δadd - s| ≤
        |roundedDenominator n x δexp δadd - W| + |W - s| := by
          convert abs_add_le
            (roundedDenominator n x δexp δadd - W) (W - s) using 1 <;> ring
    _ ≤ NumStability.gamma fp n * W + fp.u * s := add_le_add hfold hWerror
    _ ≤ (NumStability.gamma fp n * (1 + fp.u) + fp.u) * s := by
      nlinarith [mul_le_mul_of_nonneg_left hWupper hγ0]

private theorem gamma_budget (n : ℕ) (u : ℝ) (hu : 0 < u)
    (hcap : u ≤ 1 / (8 * ((n : ℝ) + 1) ^ 2)) :
    let fp := NumStability.FPModel.exactWithUnitRoundoff u hu.le
    let A := NumStability.gamma fp n * (1 + u) + u
    NumStability.gammaValid fp n ∧
      A ≤ ((n : ℝ) + 2) * u ∧ A ≤ 1 / 4 := by
  let m : ℝ := n
  let N : ℝ := m + 1
  have hm0 : 0 ≤ m := by dsimp [m]; exact_mod_cast n.zero_le
  have hN1 : 1 ≤ N := by dsimp [N]; linarith
  have hNpos : 0 < N := by linarith
  have hN2pos : 0 < 8 * N ^ 2 := by positivity
  have hcap' : 8 * N ^ 2 * u ≤ 1 := by
    have h := (le_div_iff₀ hN2pos).mp (show u ≤ 1 / (8 * N ^ 2) by simpa [N, m] using hcap)
    nlinarith
  have hmu : m * u ≤ 1 / 8 := by
    have hN2 : N ≤ N ^ 2 := by nlinarith
    nlinarith [mul_nonneg (show 0 ≤ N ^ 2 - m by nlinarith) hu.le]
  have hden : 0 < 1 - m * u := by linarith
  have hvalid : NumStability.gammaValid
      (NumStability.FPModel.exactWithUnitRoundoff u hu.le) n := by
    simp only [NumStability.gammaValid, NumStability.FPModel.exactWithUnitRoundoff]
    dsimp [m] at hden
    linarith
  have hmu_extra : m * (N + 1) * u ≤ 1 := by
    have hbound : m * (N + 1) ≤ 2 * N ^ 2 := by
      dsimp [N]
      nlinarith [sq_nonneg m]
    have hpos : 0 ≤ 2 * N ^ 2 - m * (N + 1) := by linarith
    nlinarith [mul_nonneg hpos hu.le]
  have hA :
      m * u / (1 - m * u) * (1 + u) + u ≤ (m + 2) * u := by
    rw [div_mul_eq_mul_div]
    have hfr : m * u * (1 + u) / (1 - m * u) ≤ (m + 1) * u :=
      (div_le_iff₀ hden).2 (by nlinarith [hmu_extra])
    nlinarith
  have hAquarter :
      m * u / (1 - m * u) * (1 + u) + u ≤ 1 / 4 := by
    have huN : N * u ≤ 1 / 8 := by
      have hN2 : N ≤ N ^ 2 := by nlinarith
      nlinarith [mul_nonneg (show 0 ≤ N ^ 2 - N by linarith) hu.le]
    have hu2 : u ≤ 1 / 8 := by nlinarith [mul_nonneg (show 0 ≤ N - 1 by linarith) hu.le]
    have hA' := hA
    dsimp [N] at huN
    nlinarith
  dsimp
  refine ⟨hvalid, ?_, ?_⟩
  · simpa [NumStability.gamma, NumStability.FPModel.exactWithUnitRoundoff, m] using hA
  · simpa [NumStability.gamma, NumStability.FPModel.exactWithUnitRoundoff, m] using hAquarter

private theorem ratio_error (M u A a d e : ℝ)
    (hM : 1 ≤ M) (hu : 0 < u)
    (ha : |a| ≤ u) (hd : |d| ≤ u) (he : |e| ≤ A)
    (hA : A ≤ (M + 1) * u) (hAquarter : A ≤ 1 / 4) :
    |(1 + a) * (1 + d) / (1 + e) - 1| ≤
      (M + 3) * u + 4 * (1 + (M + 3) * (M + 1)) * u ^ 2 := by
  let C : ℝ := 4 * (1 + (M + 3) * (M + 1))
  let B : ℝ := (M + 3) * u + C * u ^ 2
  have hA0 : 0 ≤ A := le_trans (abs_nonneg e) he
  have hden : 0 < 1 + e := by
    have := (abs_le.mp he).1
    linarith
  have hprod : |a * d| ≤ u ^ 2 := by
    rw [abs_mul]
    nlinarith [mul_le_mul ha hd (abs_nonneg d) hu.le]
  have hnum : |(1 + a) * (1 + d) - (1 + e)| ≤ 2 * u + u ^ 2 + A := by
    have h1 := abs_add_le a d
    have h2 := abs_add_le (a + d) (a * d)
    have h3 := abs_add_le (a + d + a * d) (-e)
    have hrewrite : (1 + a) * (1 + d) - (1 + e) = a + d + a * d - e := by ring
    rw [hrewrite]
    rw [show a + d + a * d - e = a + d + a * d + -e by ring] at *
    rw [abs_neg] at h3
    nlinarith
  have hM3 : 0 ≤ M + 3 := by linarith
  have hC0 : 0 ≤ C := by dsimp [C]; positivity
  have hcross : (M + 3) * u * A ≤ (M + 3) * (M + 1) * u ^ 2 := by
    nlinarith [mul_le_mul_of_nonneg_left hA (mul_nonneg hM3 hu.le)]
  have hquadratic : C * u ^ 2 * A ≤ C * u ^ 2 / 4 := by
    nlinarith [mul_le_mul_of_nonneg_left hAquarter (mul_nonneg hC0 (sq_nonneg u))]
  have hCbig : 1 + (M + 3) * (M + 1) ≤ 3 * C / 4 := by
    dsimp [C]
    nlinarith [mul_nonneg hM3 (show 0 ≤ M + 1 by linarith)]
  have hCbig' : (1 + (M + 3) * (M + 1)) * u ^ 2 ≤ 3 * C / 4 * u ^ 2 :=
    mul_le_mul_of_nonneg_right hCbig (sq_nonneg u)
  have hBden : 2 * u + u ^ 2 + A ≤ B * (1 + e) := by
    have he_low : -A ≤ e := (abs_le.mp he).1
    have hB0 : 0 ≤ B := by dsimp [B]; positivity
    have hBe : B * (1 - A) ≤ B * (1 + e) :=
      mul_le_mul_of_nonneg_left (by linarith) hB0
    have hbase : 2 * u + u ^ 2 + A ≤ B * (1 - A) := by
      dsimp [B]
      nlinarith [hcross, hquadratic, hCbig']
    exact hbase.trans hBe
  have hratio :
      (1 + a) * (1 + d) / (1 + e) - 1 =
        ((1 + a) * (1 + d) - (1 + e)) / (1 + e) := by
    field_simp
  rw [hratio, abs_div, abs_of_pos hden]
  exact (div_le_iff₀ hden).2 (le_trans hnum hBden)

private theorem norm_ratio_of_componentwise (n : ℕ)
    (g r : Fin (n + 1) → ℝ) (B : ℝ)
    (hg : ∀ j, 0 < g j) (hB : 0 ≤ B)
    (hcomp : ∀ j, |r j - g j| ≤ B * g j) :
    ‖g - r‖ / ‖g‖ ≤ B := by
  have hg_ne : g ≠ 0 := by
    intro h
    have h0 := congrArg (fun f : Fin (n + 1) → ℝ => f 0) h
    simp at h0
    linarith [hg 0]
  have hgnorm : 0 < ‖g‖ := norm_pos_iff.mpr hg_ne
  have hnorm : ‖g - r‖ ≤ B * ‖g‖ :=
    (pi_norm_le_iff_of_nonneg (mul_nonneg hB (norm_nonneg g))).2 (fun j => by
      have hj : |r j - g j| ≤ B * |g j| := by
        simpa [abs_of_pos (hg j)] using hcomp j
      calc
        ‖(g - r) j‖ = |r j - g j| := by
          simp [Pi.sub_apply, Real.norm_eq_abs, abs_sub_comm]
        _ ≤ B * |g j| := hj
        _ ≤ B * ‖g‖ := mul_le_mul_of_nonneg_left (norm_le_pi_norm g j) hB)
  exact (div_le_iff₀ hgnorm).2 hnorm

/-- Theorem 3.3 and the componentwise result immediately preceding it.
The standard relative-error laws for exponentiation, addition, and division
express the paper's no-overflow/no-underflow regime. The constants in the
quadratic remainder are fixed before choosing the unit roundoff or any local
rounding errors. -/
theorem target :
    ∀ (n : ℕ) (x : Fin (n + 1) → ℝ),
      ∃ C u₀ : ℝ, 0 < C ∧ 0 < u₀ ∧
        ∀ (u : ℝ), 0 < u → u ≤ u₀ →
          ∀ (δexp : Fin (n + 1) → ℝ) (δadd : Fin n → ℝ)
            (δdiv : Fin (n + 1) → ℝ),
            (∀ i, |δexp i| ≤ u) →
            (∀ i, |δadd i| ≤ u) →
            (∀ i, |δdiv i| ≤ u) →
              ∃ τ : Fin (n + 1) → ℝ,
                (∀ j,
                  |τ j| ≤ ((n + 1 : ℕ) + 3 : ℝ) * u + C * u ^ 2 ∧
                  roundedSoftmax n x δexp δadd δdiv j =
                    softmax n x j * (1 + τ j)) ∧
                ‖softmax n x - roundedSoftmax n x δexp δadd δdiv‖ /
                    ‖softmax n x‖ ≤
                  ((n + 1 : ℕ) + 3 : ℝ) * u + C * u ^ 2 := by
  intro n x
  let M : ℝ := (n : ℝ) + 1
  let C : ℝ := 4 * (1 + (M + 3) * (M + 1))
  let u₀ : ℝ := 1 / (8 * M ^ 2)
  have hM : 1 ≤ M := by
    dsimp [M]
    exact_mod_cast Nat.succ_le_succ n.zero_le
  have hMpos : 0 < M := by linarith
  have hCpos : 0 < C := by dsimp [C]; positivity
  have hu₀pos : 0 < u₀ := by dsimp [u₀]; positivity
  refine ⟨C, u₀, hCpos, hu₀pos, ?_⟩
  intro u hu hu₀ δexp δadd δdiv he ha hd
  let fp := NumStability.FPModel.exactWithUnitRoundoff u hu.le
  let A : ℝ := NumStability.gamma fp n * (1 + u) + u
  have hcap : u ≤ 1 / (8 * ((n : ℝ) + 1) ^ 2) := by
    simpa [u₀, M] using hu₀
  obtain ⟨hvalid, hA', hAquarter⟩ := gamma_budget n u hu hcap
  have hvalid' : NumStability.gammaValid fp n := by simpa [fp] using hvalid
  have hA : A ≤ (M + 1) * u := by
    have hA'' : A ≤ ((n : ℝ) + 2) * u := by simpa [A, fp] using hA'
    simpa [M, show (2 : ℝ) = 1 + 1 by ring, add_assoc] using hA''
  have hAquarter' : A ≤ 1 / 4 := by simpa [A, fp] using hAquarter
  have hu1 : u ≤ 1 := by
    have hM2 : 1 ≤ M ^ 2 := by nlinarith
    have hden : 0 < 8 * M ^ 2 := by positivity
    have hmul := (le_div_iff₀ hden).mp (show u ≤ 1 / (8 * M ^ 2) by simpa [u₀] using hu₀)
    nlinarith
  let s : ℝ := ∑ i : Fin (n + 1), Real.exp (x i)
  let ŝ : ℝ := roundedDenominator n x δexp δadd
  have hspos : 0 < s := by
    dsimp [s]
    rw [Fin.sum_univ_succ]
    exact add_pos_of_pos_of_nonneg (Real.exp_pos _) (Finset.sum_nonneg (fun i _ => (Real.exp_pos _).le))
  have hsnz : s ≠ 0 := ne_of_gt hspos
  have hdenerr : |ŝ - s| ≤ A * s := by
    simpa [ŝ, s, A, fp, NumStability.FPModel.exactWithUnitRoundoff] using
      denominator_relative_error fp n x δexp δadd (by simpa [fp] using hu1)
        (by simpa [fp] using he) (by simpa [fp] using ha) hvalid'
  let e : ℝ := ŝ / s - 1
  have heA : |e| ≤ A := by
    have heq : e = (ŝ - s) / s := by
      dsimp [e]
      field_simp
    rw [heq, abs_div, abs_of_pos hspos]
    exact (div_le_iff₀ hspos).2 hdenerr
  have heshat : ŝ = s * (1 + e) := by
    dsimp [e]
    field_simp
    ring
  have h1epos : 0 < 1 + e := by
    have := (abs_le.mp heA).1
    linarith
  have h1enz : 1 + e ≠ 0 := ne_of_gt h1epos
  let τ : Fin (n + 1) → ℝ :=
    fun j => (1 + δexp j) * (1 + δdiv j) / (1 + e) - 1
  have hτ (j : Fin (n + 1)) :
      |τ j| ≤ ((n + 1 : ℕ) + 3 : ℝ) * u + C * u ^ 2 ∧
        roundedSoftmax n x δexp δadd δdiv j = softmax n x j * (1 + τ j) := by
    constructor
    · simpa [τ, C, M] using
        ratio_error M u A (δexp j) (δdiv j) e hM hu (he j) (hd j) heA hA hAquarter'
    · change (Real.exp (x j) * (1 + δexp j) / ŝ) * (1 + δdiv j) =
        (Real.exp (x j) / s) * (1 + τ j)
      rw [heshat]
      dsimp [τ]
      field_simp
      ring
  refine ⟨τ, hτ, ?_⟩
  let g := softmax n x
  let r := roundedSoftmax n x δexp δadd δdiv
  let B : ℝ := ((n + 1 : ℕ) + 3 : ℝ) * u + C * u ^ 2
  have hB : 0 ≤ B := by dsimp [B]; positivity
  have hg (j : Fin (n + 1)) : 0 < g j := by
    dsimp [g, softmax]
    exact div_pos (Real.exp_pos _) hspos
  have hcomp (j : Fin (n + 1)) : |r j - g j| ≤ B * g j := by
    have hj := hτ j
    change |roundedSoftmax n x δexp δadd δdiv j - softmax n x j| ≤
      B * softmax n x j
    rw [hj.2]
    have hmul : softmax n x j * (1 + τ j) - softmax n x j =
        softmax n x j * τ j := by ring
    rw [hmul, abs_mul, abs_of_pos (hg j)]
    simpa [B, g, mul_comm] using mul_le_mul_of_nonneg_left hj.1 (hg j).le
  exact norm_ratio_of_componentwise n g r B hg hB hcomp

end HighamBenchCandidate
