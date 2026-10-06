import HighamBench.P23Definitions
import Mathlib

namespace HighamBench

open scoped BigOperators

private lemma p23_gamma_nonneg (u : ℝ) (m : ℕ) (hu : 0 ≤ u)
    (hv : P23GammaValid u m) : 0 ≤ p23Gamma u m := by
  unfold P23GammaValid at hv
  unfold p23Gamma
  exact div_nonneg (mul_nonneg (Nat.cast_nonneg m) hu) (by linarith)

private lemma p23_u_le_gamma_one (u : ℝ) (hu : 0 ≤ u)
    (hv : P23GammaValid u 1) : u ≤ p23Gamma u 1 := by
  unfold P23GammaValid at hv
  unfold p23Gamma
  norm_num at hv ⊢
  apply (le_div_iff₀ (by linarith)).2
  nlinarith [sq_nonneg u]

private lemma p23_gamma_step_mul (u : ℝ) (m : ℕ) (hu : 0 ≤ u)
    (hv : P23GammaValid u (m + 1)) :
    p23Gamma u m * (1 + u) + u ≤ p23Gamma u (m + 1) := by
  unfold P23GammaValid at hv
  have hm : ((m : ℝ) * u) < 1 := by
    have hc : (m : ℝ) ≤ (m + 1 : ℕ) := by norm_num
    have := mul_le_mul_of_nonneg_right hc hu
    norm_num at this hv ⊢
    linarith
  have hden : (1 - (m : ℝ) * u) ≠ 0 := ne_of_gt (by linarith)
  have heq : p23Gamma u m * (1 + u) + u =
      ((((m + 1 : ℕ) : ℝ) * u) / (1 - (m : ℝ) * u)) := by
    unfold p23Gamma
    field_simp [hden]
    norm_num
    ring
    simp
  rw [heq]
  unfold p23Gamma
  apply (div_le_div_iff₀ (by linarith) (by norm_num at hv ⊢; linarith)).2
  have hn : 0 ≤ (((m + 1 : ℕ) : ℝ) * u) :=
    mul_nonneg (Nat.cast_nonneg _) hu
  have harg : (m : ℝ) * u ≤ ((m + 1 : ℕ) : ℝ) * u := by
    exact mul_le_mul_of_nonneg_right (by norm_num) hu
  have hdens : 1 - ((m + 1 : ℕ) : ℝ) * u ≤ 1 - (m : ℝ) * u :=
    sub_le_sub_left harg 1
  exact mul_le_mul_of_nonneg_left hdens hn

private lemma p23_two_error_le_gamma (u : ℝ) (m : ℕ) (hu : 0 ≤ u)
    (hm : 1 ≤ m) (hv : P23GammaValid u (m + 1)) :
    2 * u + u ^ 2 ≤ p23Gamma u (m + 1) := by
  unfold P23GammaValid at hv
  have htwo : 2 * u < 1 := by
    have hc : (2 : ℝ) ≤ (m + 1 : ℕ) := by exact_mod_cast Nat.succ_le_succ hm
    have := mul_le_mul_of_nonneg_right hc hu
    norm_num at this hv ⊢
    linarith
  have hbase : 2 * u + u ^ 2 ≤ (2 * u) / (1 - 2 * u) := by
    apply (le_div_iff₀ (by linarith)).2
    nlinarith [sq_nonneg u, mul_nonneg (sq_nonneg u) hu]
  have hmono : (2 * u) / (1 - 2 * u) ≤
      (((m + 1 : ℕ) : ℝ) * u) / (1 - ((m + 1 : ℕ) : ℝ) * u) := by
    apply (div_le_div_iff₀ (by linarith) (by linarith)).2
    have hc : (2 : ℝ) ≤ (m + 1 : ℕ) := by exact_mod_cast Nat.succ_le_succ hm
    nlinarith [mul_nonneg (sub_nonneg.mpr hc) hu]
  exact hbase.trans (by simpa [p23Gamma] using hmono)

private lemma p23_gamma_mono (u : ℝ) (a b : ℕ) (hu : 0 ≤ u) (hab : a ≤ b)
    (hv : P23GammaValid u b) : p23Gamma u a ≤ p23Gamma u b := by
  unfold P23GammaValid at hv
  have hcast : (a : ℝ) ≤ (b : ℝ) := by exact_mod_cast hab
  have hau : (a : ℝ) * u ≤ (b : ℝ) * u :=
    mul_le_mul_of_nonneg_right hcast hu
  have ha : (a : ℝ) * u < 1 := lt_of_le_of_lt hau hv
  unfold p23Gamma
  apply (div_le_div_iff₀ (by linarith) (by linarith)).2
  nlinarith

private lemma p23_gamma_valid_of_le (u : ℝ) (a b : ℕ) (hu : 0 ≤ u)
    (hab : a ≤ b) (hv : P23GammaValid u b) : P23GammaValid u a := by
  unfold P23GammaValid at hv ⊢
  exact lt_of_le_of_lt
    (mul_le_mul_of_nonneg_right (by exact_mod_cast hab) hu) hv

private lemma p23_one_add_gamma (u : ℝ) (m : ℕ)
    (hv : P23GammaValid u m) :
    1 + p23Gamma u m = 1 / (1 - (m : ℝ) * u) := by
  unfold P23GammaValid at hv
  unfold p23Gamma
  have hne : 1 - (m : ℝ) * u ≠ 0 := ne_of_gt (by linarith)
  field_simp [hne]
  ring

private lemma p23_gamma_combine (u : ℝ) (a b : ℕ) (hu : 0 ≤ u)
    (hv : P23GammaValid u (a + b)) :
    p23Gamma u b * (1 + p23Gamma u a) + p23Gamma u a ≤
      p23Gamma u (a + b) := by
  have ha_le : a ≤ a + b := Nat.le_add_right a b
  have hb_le : b ≤ a + b := Nat.le_add_left b a
  have hva : P23GammaValid u a := by
    unfold P23GammaValid at hv ⊢
    exact lt_of_le_of_lt
      (mul_le_mul_of_nonneg_right (by exact_mod_cast ha_le) hu) hv
  have hvb : P23GammaValid u b := by
    unfold P23GammaValid at hv ⊢
    exact lt_of_le_of_lt
      (mul_le_mul_of_nonneg_right (by exact_mod_cast hb_le) hu) hv
  have hda : 0 < 1 - (a : ℝ) * u := by
    unfold P23GammaValid at hva
    linarith
  have hdb : 0 < 1 - (b : ℝ) * u := by
    unfold P23GammaValid at hvb
    linarith
  have hdt : 0 < 1 - ((a + b : ℕ) : ℝ) * u := by
    unfold P23GammaValid at hv
    linarith
  have hden : 1 - ((a + b : ℕ) : ℝ) * u ≤
      (1 - (a : ℝ) * u) * (1 - (b : ℝ) * u) := by
    norm_num
    nlinarith [mul_nonneg
      (mul_nonneg (Nat.cast_nonneg a) (Nat.cast_nonneg b)) (sq_nonneg u)]
  have hinv : 1 / ((1 - (a : ℝ) * u) * (1 - (b : ℝ) * u)) ≤
      1 / (1 - ((a + b : ℕ) : ℝ) * u) := by
    exact one_div_le_one_div_of_le hdt hden
  have hleft :
      1 + (p23Gamma u b * (1 + p23Gamma u a) + p23Gamma u a) =
        1 / ((1 - (a : ℝ) * u) * (1 - (b : ℝ) * u)) := by
    calc
      1 + (p23Gamma u b * (1 + p23Gamma u a) + p23Gamma u a) =
          (1 + p23Gamma u a) * (1 + p23Gamma u b) := by ring
      _ = (1 / (1 - (a : ℝ) * u)) * (1 / (1 - (b : ℝ) * u)) := by
        rw [p23_one_add_gamma u a hva, p23_one_add_gamma u b hvb]
      _ = 1 / ((1 - (a : ℝ) * u) * (1 - (b : ℝ) * u)) :=
        one_div_mul_one_div _ _
  have hright : 1 + p23Gamma u (a + b) =
      1 / (1 - ((a + b : ℕ) : ℝ) * u) :=
    p23_one_add_gamma u (a + b) hv
  linarith

/-- Error bound for one rounded scalar product, in the form needed below. -/
private lemma p23_rounded_dot_error (fp : P23FPModel) (n : ℕ)
    (x y : Fin n → ℝ) (hv : P23GammaValid fp.u n) :
    |p23RoundedDotProduct fp n x y - ∑ i, x i * y i| ≤
      p23Gamma fp.u n * ∑ i, |x i * y i| := by
  induction n with
  | zero =>
      simp [p23RoundedDotProduct, p23Gamma]
  | succ n ih =>
      cases n with
      | zero =>
          obtain ⟨d, hd, hmul⟩ := fp.model_mul (x 0) (y 0)
          have hu_gamma := p23_u_le_gamma_one fp.u fp.u_nonneg hv
          have hscalar :
              |fp.fl_mul (x 0) (y 0) - x 0 * y 0| ≤
                p23Gamma fp.u 1 * |x 0 * y 0| := by
            rw [hmul]
            calc
            |x 0 * y 0 * (1 + d) - x 0 * y 0| = |(x 0 * y 0) * d| := by ring_nf
            _ = |x 0 * y 0| * |d| := abs_mul _ _
            _ ≤ |x 0 * y 0| * fp.u :=
              mul_le_mul_of_nonneg_left hd (abs_nonneg _)
            _ ≤ p23Gamma fp.u 1 * |x 0 * y 0| := by
              simpa [mul_comm] using
                mul_le_mul_of_nonneg_right hu_gamma (abs_nonneg (x 0 * y 0))
          simpa [p23RoundedDotProduct] using hscalar
      | succ m =>
          let x' : Fin (m + 1) → ℝ := fun i => x i.castSucc
          let y' : Fin (m + 1) → ℝ := fun i => y i.castSucc
          let last : Fin (m + 2) := Fin.last (m + 1)
          let R := p23RoundedDotProduct fp (m + 1) x' y'
          let S := ∑ i : Fin (m + 1), x' i * y' i
          let t := x last * y last
          have hvpre : P23GammaValid fp.u (m + 1) := by
            apply lt_of_le_of_lt ?_ hv
            exact mul_le_mul_of_nonneg_right (by norm_num) fp.u_nonneg
          have hprefix : |R - S| ≤
              p23Gamma fp.u (m + 1) * ∑ i : Fin (m + 1), |x' i * y' i| := by
            exact ih x' y' hvpre
          obtain ⟨dm, hdm, hmul⟩ := fp.model_mul (x last) (y last)
          obtain ⟨da, hda, hadd⟩ := fp.model_add R (fp.fl_mul (x last) (y last))
          have hda1 : |1 + da| ≤ 1 + fp.u := by
            calc
              |1 + da| ≤ |(1 : ℝ)| + |da| := abs_add_le _ _
              _ ≤ 1 + fp.u := by simpa using add_le_add_left hda 1
          have hcoeff : |(1 + dm) * (1 + da) - 1| ≤ 2 * fp.u + fp.u ^ 2 := by
            have hprod : |dm| * |da| ≤ fp.u * fp.u :=
              mul_le_mul hdm hda (abs_nonneg _) fp.u_nonneg
            calc
              |(1 + dm) * (1 + da) - 1| = |dm + da + dm * da| := by ring_nf
              _ ≤ |dm + da| + |dm * da| := abs_add_le _ _
              _ ≤ (|dm| + |da|) + |dm| * |da| := by
                rw [abs_mul]
                gcongr
                exact abs_add_le dm da
              _ ≤ 2 * fp.u + fp.u ^ 2 := by nlinarith
          have hcoeff_gamma : |(1 + dm) * (1 + da) - 1| ≤
              p23Gamma fp.u (m + 2) :=
            hcoeff.trans (p23_two_error_le_gamma fp.u (m + 1) fp.u_nonneg
              (by omega) (by simpa [Nat.add_assoc] using hv))
          have hgamma_step : p23Gamma fp.u (m + 1) * (1 + fp.u) + fp.u ≤
              p23Gamma fp.u (m + 2) :=
            p23_gamma_step_mul fp.u (m + 1) fp.u_nonneg
              (by simpa [Nat.add_assoc] using hv)
          have hGpre : 0 ≤ p23Gamma fp.u (m + 1) :=
            p23_gamma_nonneg fp.u (m + 1) fp.u_nonneg hvpre
          have hA : 0 ≤ ∑ i : Fin (m + 1), |x' i * y' i| :=
            Finset.sum_nonneg fun _ _ => abs_nonneg _
          have hdot : p23RoundedDotProduct fp (m + 2) x y =
              fp.fl_add R (fp.fl_mul (x last) (y last)) := by
            simp [R, x', y', last, p23RoundedDotProduct, Fin.foldl_succ_last]
          have hsum : (∑ i : Fin (m + 2), x i * y i) = S + t := by
            simpa [S, t, x', y', last] using
              (Fin.sum_univ_castSucc (fun i : Fin (m + 2) => x i * y i))
          have habssum : (∑ i : Fin (m + 2), |x i * y i|) =
              (∑ i : Fin (m + 1), |x' i * y' i|) + |t| := by
            simpa [t, x', y', last] using
              (Fin.sum_univ_castSucc (fun i : Fin (m + 2) => |x i * y i|))
          rw [hdot, hsum, hadd, hmul, habssum]
          have hid : (R + t * (1 + dm)) * (1 + da) - (S + t) =
              (R - S) * (1 + da) + S * da +
                t * ((1 + dm) * (1 + da) - 1) := by
            ring
          rw [hid]
          calc
            |(R - S) * (1 + da) + S * da +
                t * ((1 + dm) * (1 + da) - 1)| ≤
                |(R - S) * (1 + da)| + |S * da| +
                  |t * ((1 + dm) * (1 + da) - 1)| := abs_add_three _ _ _
            _ = |R - S| * |1 + da| + |S| * |da| +
                  |t| * |(1 + dm) * (1 + da) - 1| := by
              rw [abs_mul, abs_mul, abs_mul]
            _ ≤ (p23Gamma fp.u (m + 1) * ∑ i : Fin (m + 1), |x' i * y' i|) *
                  (1 + fp.u) +
                  (∑ i : Fin (m + 1), |x' i * y' i|) * fp.u +
                  |t| * p23Gamma fp.u (m + 2) := by
              apply add_le_add
              · apply add_le_add
                · exact mul_le_mul hprefix hda1 (abs_nonneg _)
                    (mul_nonneg hGpre hA)
                · exact mul_le_mul
                    (by exact Finset.abs_sum_le_sum_abs (fun i => x' i * y' i) Finset.univ)
                    hda (abs_nonneg _) hA
              · exact mul_le_mul_of_nonneg_left hcoeff_gamma (abs_nonneg _)
            _ = (p23Gamma fp.u (m + 1) * (1 + fp.u) + fp.u) *
                  (∑ i : Fin (m + 1), |x' i * y' i|) +
                  p23Gamma fp.u (m + 2) * |t| := by ring
            _ ≤ p23Gamma fp.u (m + 2) *
                  (∑ i : Fin (m + 1), |x' i * y' i|) +
                  p23Gamma fp.u (m + 2) * |t| := by
              gcongr
            _ = p23Gamma fp.u (m + 2) *
                  ((∑ i : Fin (m + 1), |x' i * y' i|) + |t|) := by ring

private lemma p23_rounded_matmul_error (fp : P23FPModel) {n : ℕ}
    (A B : P23Matrix n) (hv : P23GammaValid fp.u n) (i j : Fin n) :
    |p23RoundedMatMul fp A B i j - p23MatMul A B i j| ≤
      p23Gamma fp.u n * p23MatMul (p23AbsMatrix A) (p23AbsMatrix B) i j := by
  simpa [p23RoundedMatMul, p23MatMul, p23AbsMatrix, abs_mul] using
    p23_rounded_dot_error fp n (A i) (fun l => B l j) hv

private lemma p23_abs_power_nonneg {n : ℕ} (X : P23Matrix n) :
    ∀ k i j, 0 ≤ p23PowerSteps (p23AbsMatrix X) k i j := by
  intro k
  induction k with
  | zero =>
      intro i j
      exact abs_nonneg _
  | succ k ih =>
      intro i j
      simp only [p23PowerSteps, p23MatMul, p23AbsMatrix]
      exact Finset.sum_nonneg fun l _ =>
        mul_nonneg (ih i l) (abs_nonneg (X l j))

private lemma p23_exact_power_abs {n : ℕ} (X : P23Matrix n) :
    ∀ k i j,
      |p23PowerSteps X k i j| ≤ p23PowerSteps (p23AbsMatrix X) k i j := by
  intro k
  induction k with
  | zero =>
      intro i j
      exact le_rfl
  | succ k ih =>
      intro i j
      simp only [p23PowerSteps, p23MatMul]
      calc
        |∑ l, p23PowerSteps X k i l * X l j| ≤
            ∑ l, |p23PowerSteps X k i l * X l j| :=
          Finset.abs_sum_le_sum_abs _ _
        _ = ∑ l, |p23PowerSteps X k i l| * |X l j| := by
          apply Finset.sum_congr rfl
          intro l _
          exact abs_mul _ _
        _ ≤ ∑ l, p23PowerSteps (p23AbsMatrix X) k i l * |X l j| := by
          apply Finset.sum_le_sum
          intro l _
          exact mul_le_mul_of_nonneg_right (ih i l) (abs_nonneg _)

/-- P23-T1: Lemma 2.2, reindexed so `k` counts the rounded matrix
multiplications after the supplied matrix `X`. -/
theorem p23_t1_lemma_2_2
    (fp : P23FPModel) (n k : ℕ) (X : P23Matrix n)
    (hvalid : P23GammaValid fp.u (k * n)) :
    ∀ i j,
      |p23RoundedPowerSteps fp X k i j - p23PowerSteps X k i j| ≤
        p23Gamma fp.u (k * n) * p23PowerSteps (p23AbsMatrix X) k i j := by
  -- PROOF_START P23-T1-H001
  have main : ∀ q : ℕ, P23GammaValid fp.u (q * n) → ∀ i j,
      |p23RoundedPowerSteps fp X q i j - p23PowerSteps X q i j| ≤
        p23Gamma fp.u (q * n) * p23PowerSteps (p23AbsMatrix X) q i j := by
    intro q
    induction q with
    | zero =>
        intro _ i j
        simp [p23RoundedPowerSteps, p23PowerSteps, p23Gamma]
    | succ q ih =>
        intro hv i j
        have hq_le : q * n ≤ (q + 1) * n := Nat.mul_le_mul_right n (Nat.le_succ q)
        have hn_le : n ≤ (q + 1) * n := by
          rw [Nat.succ_mul]
          omega
        have hvq : P23GammaValid fp.u (q * n) :=
          p23_gamma_valid_of_le fp.u (q * n) ((q + 1) * n) fp.u_nonneg
            hq_le (by simpa using hv)
        have hvn : P23GammaValid fp.u n :=
          p23_gamma_valid_of_le fp.u n ((q + 1) * n) fp.u_nonneg
            hn_le (by simpa using hv)
        let R := p23RoundedPowerSteps fp X q
        let P := p23PowerSteps X q
        let A := p23PowerSteps (p23AbsMatrix X) q
        let G := p23Gamma fp.u (q * n)
        let C := p23MatMul A (p23AbsMatrix X) i j
        have hG : 0 ≤ G := p23_gamma_nonneg fp.u (q * n) fp.u_nonneg hvq
        have hGn : 0 ≤ p23Gamma fp.u n :=
          p23_gamma_nonneg fp.u n fp.u_nonneg hvn
        have hC : 0 ≤ C := by
          dsimp [C]
          exact Finset.sum_nonneg fun l _ =>
            mul_nonneg (p23_abs_power_nonneg X q i l) (abs_nonneg (X l j))
        have hRabs : ∀ l : Fin n, |R i l| ≤ (1 + G) * A i l := by
          intro l
          calc
            |R i l| = |(R i l - P i l) + P i l| := by ring_nf
            _ ≤ |R i l - P i l| + |P i l| := abs_add_le _ _
            _ ≤ G * A i l + A i l := by
              apply add_le_add
              · exact ih hvq i l
              · exact p23_exact_power_abs X q i l
            _ = (1 + G) * A i l := by ring
        have hmul_abs :
            p23MatMul (p23AbsMatrix R) (p23AbsMatrix X) i j ≤
              (1 + G) * C := by
          simp only [p23MatMul, p23AbsMatrix]
          calc
            (∑ l, |R i l| * |X l j|) ≤
                ∑ l, ((1 + G) * A i l) * |X l j| := by
              apply Finset.sum_le_sum
              intro l _
              exact mul_le_mul_of_nonneg_right (hRabs l) (abs_nonneg _)
            _ = (1 + G) * C := by
              simp only [C, p23MatMul, p23AbsMatrix, Finset.mul_sum]
              apply Finset.sum_congr rfl
              intro l _
              ring
        have hround :
            |p23RoundedMatMul fp R X i j - p23MatMul R X i j| ≤
              p23Gamma fp.u n * (1 + G) * C := by
          calc
            |p23RoundedMatMul fp R X i j - p23MatMul R X i j| ≤
                p23Gamma fp.u n *
                  p23MatMul (p23AbsMatrix R) (p23AbsMatrix X) i j :=
              p23_rounded_matmul_error fp R X hvn i j
            _ ≤ p23Gamma fp.u n * ((1 + G) * C) :=
              mul_le_mul_of_nonneg_left hmul_abs hGn
            _ = p23Gamma fp.u n * (1 + G) * C := by ring
        have hprop : |p23MatMul R X i j - p23MatMul P X i j| ≤ G * C := by
          have heq : p23MatMul R X i j - p23MatMul P X i j =
              ∑ l, (R i l - P i l) * X l j := by
            simp only [p23MatMul, sub_mul, Finset.sum_sub_distrib]
          rw [heq]
          calc
            |∑ l, (R i l - P i l) * X l j| ≤
                ∑ l, |(R i l - P i l) * X l j| :=
              Finset.abs_sum_le_sum_abs _ _
            _ = ∑ l, |R i l - P i l| * |X l j| := by
              apply Finset.sum_congr rfl
              intro l _
              exact abs_mul _ _
            _ ≤ ∑ l, (G * A i l) * |X l j| := by
              apply Finset.sum_le_sum
              intro l _
              exact mul_le_mul_of_nonneg_right (ih hvq i l) (abs_nonneg _)
            _ = G * C := by
              simp only [C, p23MatMul, p23AbsMatrix, Finset.mul_sum]
              apply Finset.sum_congr rfl
              intro l _
              ring
        have hcombine : p23Gamma fp.u n * (1 + G) + G ≤
            p23Gamma fp.u ((q + 1) * n) := by
          simpa [G, Nat.succ_mul] using
            p23_gamma_combine fp.u (q * n) n fp.u_nonneg
              (by simpa [Nat.succ_mul] using hv)
        simp only [p23RoundedPowerSteps, p23PowerSteps]
        change |p23RoundedMatMul fp R X i j - p23MatMul P X i j| ≤
          p23Gamma fp.u ((q + 1) * n) * C
        calc
          |p23RoundedMatMul fp R X i j - p23MatMul P X i j| =
              |(p23RoundedMatMul fp R X i j - p23MatMul R X i j) +
                (p23MatMul R X i j - p23MatMul P X i j)| := by ring_nf
          _ ≤ |p23RoundedMatMul fp R X i j - p23MatMul R X i j| +
                |p23MatMul R X i j - p23MatMul P X i j| := abs_add_le _ _
          _ ≤ p23Gamma fp.u n * (1 + G) * C + G * C :=
            add_le_add hround hprop
          _ = (p23Gamma fp.u n * (1 + G) + G) * C := by ring
          _ ≤ p23Gamma fp.u ((q + 1) * n) * C :=
            mul_le_mul_of_nonneg_right hcombine hC
  exact main k hvalid

end HighamBench
