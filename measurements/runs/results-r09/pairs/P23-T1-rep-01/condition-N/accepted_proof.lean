import HighamBench.P23Definitions
import Mathlib

namespace HighamBench

open scoped BigOperators

private lemma p23_gamma_nonneg {u : ℝ} (hu : 0 ≤ u) {m : ℕ}
    (hv : (m : ℝ) * u < 1) : 0 ≤ p23Gamma u m := by
  rw [p23Gamma]
  exact div_nonneg (mul_nonneg (Nat.cast_nonneg _) hu) (le_of_lt (sub_pos.mpr hv))

private lemma p23_gamma_mono {u : ℝ} (hu : 0 ≤ u) {a b : ℕ}
    (hab : a ≤ b) (hv : (b : ℝ) * u < 1) :
    p23Gamma u a ≤ p23Gamma u b := by
  have hcast : (a : ℝ) ≤ (b : ℝ) := by exact_mod_cast hab
  have hau : (a : ℝ) * u ≤ (b : ℝ) * u :=
    mul_le_mul_of_nonneg_right hcast hu
  have hda : 0 < 1 - (a : ℝ) * u := by
    nlinarith
  have hdb : 0 < 1 - (b : ℝ) * u := sub_pos.mpr hv
  rw [p23Gamma, p23Gamma]
  apply (div_le_div_iff₀ hda hdb).2
  nlinarith

private lemma p23_u_le_gamma {u : ℝ} (hu : 0 ≤ u) {m : ℕ}
    (hm : 1 ≤ m) (hv : (m : ℝ) * u < 1) : u ≤ p23Gamma u m := by
  have hcast : (1 : ℝ) ≤ (m : ℝ) := by exact_mod_cast hm
  have hum : u ≤ (m : ℝ) * u := by
    nlinarith [mul_nonneg (sub_nonneg.mpr hcast) hu]
  have hd : 0 < 1 - (m : ℝ) * u := sub_pos.mpr hv
  rw [p23Gamma]
  apply (le_div_iff₀ hd).2
  calc
    u * (1 - (m : ℝ) * u) ≤ u * 1 := by
      apply mul_le_mul_of_nonneg_left _ hu
      nlinarith [mul_nonneg (Nat.cast_nonneg m) hu]
    _ ≤ (m : ℝ) * u := by simpa using hum

private lemma p23_gamma_compose {u : ℝ} (hu : 0 ≤ u) (a b : ℕ)
    (hv : ((a + b : ℕ) : ℝ) * u < 1) :
    p23Gamma u a + p23Gamma u b +
        p23Gamma u a * p23Gamma u b ≤ p23Gamma u (a + b) := by
  have ha0 : 0 ≤ (a : ℝ) * u := mul_nonneg (Nat.cast_nonneg _) hu
  have hb0 : 0 ≤ (b : ℝ) * u := mul_nonneg (Nat.cast_nonneg _) hu
  have hab : ((a + b : ℕ) : ℝ) * u = (a : ℝ) * u + (b : ℝ) * u := by
    push_cast
    ring
  have hsum : (a : ℝ) * u + (b : ℝ) * u < 1 := by
    rw [hab] at hv
    exact hv
  have hda : 0 < 1 - (a : ℝ) * u := by nlinarith
  have hdb : 0 < 1 - (b : ℝ) * u := by nlinarith
  have hda' : 1 - u * (a : ℝ) ≠ 0 := by nlinarith [hda]
  have hdb' : 1 - u * (b : ℝ) ≠ 0 := by nlinarith [hdb]
  have hds : 0 < 1 - ((a + b : ℕ) : ℝ) * u := sub_pos.mpr hv
  rw [p23Gamma, p23Gamma, p23Gamma]
  have heq :
      (a : ℝ) * u / (1 - (a : ℝ) * u) +
          (b : ℝ) * u / (1 - (b : ℝ) * u) +
          ((a : ℝ) * u / (1 - (a : ℝ) * u)) *
            ((b : ℝ) * u / (1 - (b : ℝ) * u)) =
          ((a : ℝ) * u + (b : ℝ) * u -
            ((a : ℝ) * u) * ((b : ℝ) * u)) /
          ((1 - (a : ℝ) * u) * (1 - (b : ℝ) * u)) := by
    field_simp [ne_of_gt hda, ne_of_gt hdb, hda', hdb']
    field_simp [ne_of_gt hda, ne_of_gt hdb, hda', hdb']
    ring
  rw [heq, hab]
  have hdab : 0 < 1 - ((a : ℝ) * u + (b : ℝ) * u) := by
    rw [hab] at hds
    exact hds
  apply (div_le_div_iff₀ (mul_pos hda hdb) hdab).2
  have hid :
      ((a : ℝ) * u + (b : ℝ) * u) *
          ((1 - (a : ℝ) * u) * (1 - (b : ℝ) * u)) -
        ((a : ℝ) * u + (b : ℝ) * u -
            ((a : ℝ) * u) * ((b : ℝ) * u)) *
          (1 - ((a : ℝ) * u + (b : ℝ) * u)) =
        ((a : ℝ) * u) * ((b : ℝ) * u) := by ring
  nlinarith [mul_nonneg ha0 hb0]

private lemma p23_roundedDotProduct_succ (fp : P23FPModel) (m : ℕ)
    (x y : Fin (m + 2) → ℝ) :
    p23RoundedDotProduct fp (m + 2) x y =
      fp.fl_add
        (p23RoundedDotProduct fp (m + 1)
          (fun i => x i.castSucc) (fun i => y i.castSucc))
        (fp.fl_mul (x (Fin.last (m + 1))) (y (Fin.last (m + 1)))) := by
  simp only [p23RoundedDotProduct]
  rw [Fin.foldl_succ_last]
  rfl

private lemma p23_two_roundings_bound
    {u q s z d e A B g : ℝ}
    (hu : 0 ≤ u) (hA : 0 ≤ A) (hB : 0 ≤ B) (hg : 0 ≤ g)
    (hd : |d| ≤ u) (he : |e| ≤ u)
    (hq : |q - s| ≤ g * A) (hs : |s| ≤ A) (hz : |z| ≤ B) :
    |(q + z * (1 + d)) * (1 + e) - (s + z)| ≤
      (g * (1 + u) + u) * A + (u * (1 + u) + u) * B := by
  have h1e : |1 + e| ≤ 1 + u := by
    calc
      |1 + e| ≤ |(1 : ℝ)| + |e| := abs_add_le _ _
      _ ≤ 1 + u := by norm_num; linarith
  have h1u : 0 ≤ 1 + u := by positivity
  have hqa : |q - s| * |1 + e| ≤ (g * A) * (1 + u) :=
    mul_le_mul hq h1e (abs_nonneg _) (mul_nonneg hg hA)
  have hse : |s| * |e| ≤ A * u :=
    mul_le_mul hs he (abs_nonneg _) hA
  have hde : |d * (1 + e) + e| ≤ u * (1 + u) + u := by
    calc
      |d * (1 + e) + e| ≤ |d * (1 + e)| + |e| := abs_add_le _ _
      _ = |d| * |1 + e| + |e| := by rw [abs_mul]
      _ ≤ u * (1 + u) + u := by
        gcongr
  have hcoef : 0 ≤ u * (1 + u) + u := by positivity
  have hzb : |z| * |d * (1 + e) + e| ≤ B * (u * (1 + u) + u) :=
    mul_le_mul hz hde (abs_nonneg _) hB
  have hid :
      (q + z * (1 + d)) * (1 + e) - (s + z) =
        (q - s) * (1 + e) + s * e + z * (d * (1 + e) + e) := by ring
  rw [hid]
  calc
    |(q - s) * (1 + e) + s * e + z * (d * (1 + e) + e)| ≤
        (|(q - s) * (1 + e)| + |s * e|) + |z * (d * (1 + e) + e)| := by
      exact (abs_add_le _ _).trans (add_le_add (abs_add_le _ _) (le_refl _))
    _ = (|q - s| * |1 + e| + |s| * |e|) +
          |z| * |d * (1 + e) + e| := by simp only [abs_mul]
    _ ≤ ((g * A) * (1 + u) + A * u) + B * (u * (1 + u) + u) := by
      gcongr
    _ = (g * (1 + u) + u) * A + (u * (1 + u) + u) * B := by ring

private lemma p23_roundedDotProduct_error (fp : P23FPModel) (n : ℕ)
    (x y : Fin n → ℝ) (hvalid : P23GammaValid fp.u n) :
    |p23RoundedDotProduct fp n x y - ∑ i, x i * y i| ≤
      p23Gamma fp.u n * ∑ i, |x i| * |y i| := by
  induction n with
  | zero =>
      simp [p23RoundedDotProduct, p23Gamma]
  | succ n ih =>
      cases n with
      | zero =>
          obtain ⟨d, hd, hmul⟩ := fp.model_mul (x 0) (y 0)
          have hug : fp.u ≤ p23Gamma fp.u 1 :=
            p23_u_le_gamma fp.u_nonneg (by omega) hvalid
          simp only [p23RoundedDotProduct, Fin.foldl_zero, Nat.zero_add]
          rw [hmul]
          rw [show (∑ i, x i * y i) = x 0 * y 0 from Fin.sum_univ_one _,
            show (∑ i, |x i| * |y i|) = |x 0| * |y 0| from Fin.sum_univ_one _]
          have hid : x 0 * y 0 * (1 + d) - x 0 * y 0 = (x 0 * y 0) * d := by
            ring
          rw [hid, abs_mul, abs_mul]
          calc
            |x 0| * |y 0| * |d| ≤ |x 0| * |y 0| * fp.u := by
              gcongr
            _ ≤ p23Gamma fp.u 1 * (|x 0| * |y 0|) := by
              nlinarith [mul_le_mul_of_nonneg_left hug
                (mul_nonneg (abs_nonneg (x 0)) (abs_nonneg (y 0)))]
      | succ m =>
          have hvalidPrev : P23GammaValid fp.u (m + 1) := by
            unfold P23GammaValid at hvalid ⊢
            have hc : ((m + 1 : ℕ) : ℝ) ≤ ((m + 2 : ℕ) : ℝ) := by
              norm_num
            exact lt_of_le_of_lt
              (mul_le_mul_of_nonneg_right hc fp.u_nonneg) hvalid
          have hvalidOne : P23GammaValid fp.u 1 := by
            unfold P23GammaValid at hvalid ⊢
            have hcn : (1 : ℕ) ≤ m + 1 + 1 := by omega
            have hc : ((1 : ℕ) : ℝ) ≤ ((m + 1 + 1 : ℕ) : ℝ) := by
              exact_mod_cast hcn
            exact lt_of_le_of_lt
              (mul_le_mul_of_nonneg_right hc fp.u_nonneg) hvalid
          have hvalidTwo : P23GammaValid fp.u 2 := by
            unfold P23GammaValid at hvalid ⊢
            have hcn : (2 : ℕ) ≤ m + 1 + 1 := by omega
            have hc : ((2 : ℕ) : ℝ) ≤ ((m + 1 + 1 : ℕ) : ℝ) := by
              exact_mod_cast hcn
            exact lt_of_le_of_lt
              (mul_le_mul_of_nonneg_right hc fp.u_nonneg) hvalid
          let q := p23RoundedDotProduct fp (m + 1)
            (fun i => x i.castSucc) (fun i => y i.castSucc)
          let s := ∑ i : Fin (m + 1), x i.castSucc * y i.castSucc
          let z := x (Fin.last (m + 1)) * y (Fin.last (m + 1))
          let A := ∑ i : Fin (m + 1), |x i.castSucc| * |y i.castSucc|
          let B := |x (Fin.last (m + 1))| * |y (Fin.last (m + 1))|
          let g := p23Gamma fp.u (m + 1)
          let G := p23Gamma fp.u (m + 2)
          have hq : |q - s| ≤ g * A := by
            simpa [q, s, g, A] using
              (ih (fun i => x i.castSucc) (fun i => y i.castSucc) hvalidPrev)
          have hs : |s| ≤ A := by
            simpa [s, A, abs_mul] using
              (Finset.abs_sum_le_sum_abs
                (fun i : Fin (m + 1) => x i.castSucc * y i.castSucc) Finset.univ)
          have hA : 0 ≤ A := by
            dsimp [A]
            positivity
          have hB : 0 ≤ B := by
            dsimp [B]
            positivity
          have hz : |z| ≤ B := by
            simp [z, B, abs_mul]
          have hg : 0 ≤ g := by
            exact p23_gamma_nonneg fp.u_nonneg hvalidPrev
          obtain ⟨d, hd, hmul⟩ :=
            fp.model_mul (x (Fin.last (m + 1))) (y (Fin.last (m + 1)))
          obtain ⟨e, he, hadd⟩ := fp.model_add q
            (fp.fl_mul (x (Fin.last (m + 1))) (y (Fin.last (m + 1))))
          have hraw :
              |fp.fl_add q
                    (fp.fl_mul (x (Fin.last (m + 1))) (y (Fin.last (m + 1)))) -
                  (s + z)| ≤
                (g * (1 + fp.u) + fp.u) * A +
                  (fp.u * (1 + fp.u) + fp.u) * B := by
            rw [hadd, hmul]
            exact p23_two_roundings_bound fp.u_nonneg hA hB hg hd he hq hs hz
          have hg1 : 0 ≤ p23Gamma fp.u 1 :=
            p23_gamma_nonneg fp.u_nonneg hvalidOne
          have hu1 : fp.u ≤ p23Gamma fp.u 1 :=
            p23_u_le_gamma fp.u_nonneg (by omega) hvalidOne
          have hCold : g * (1 + fp.u) + fp.u ≤ G := by
            have hgu : g * fp.u ≤ g * p23Gamma fp.u 1 :=
              mul_le_mul_of_nonneg_left hu1 hg
            calc
              g * (1 + fp.u) + fp.u =
                  g + fp.u + g * fp.u := by ring
              _ ≤ g + p23Gamma fp.u 1 + g * p23Gamma fp.u 1 := by
                linarith
              _ ≤ G := by
                simpa [g, G, Nat.add_assoc] using
                  (p23_gamma_compose fp.u_nonneg (m + 1) 1 hvalid)
          have hCnew : fp.u * (1 + fp.u) + fp.u ≤ G := by
            have huu : fp.u * fp.u ≤
                p23Gamma fp.u 1 * p23Gamma fp.u 1 :=
              mul_le_mul hu1 hu1 fp.u_nonneg hg1
            have hcomp11 := p23_gamma_compose fp.u_nonneg 1 1 hvalidTwo
            have hmono : p23Gamma fp.u 2 ≤ G := by
              exact p23_gamma_mono fp.u_nonneg (by omega) hvalid
            calc
              fp.u * (1 + fp.u) + fp.u =
                  fp.u + fp.u + fp.u * fp.u := by ring
              _ ≤ p23Gamma fp.u 1 + p23Gamma fp.u 1 +
                    p23Gamma fp.u 1 * p23Gamma fp.u 1 := by
                linarith
              _ ≤ p23Gamma fp.u 2 := by simpa using hcomp11
              _ ≤ G := hmono
          have hfinal :
              |fp.fl_add q
                    (fp.fl_mul (x (Fin.last (m + 1))) (y (Fin.last (m + 1)))) -
                  (s + z)| ≤ G * (A + B) := by
            calc
              _ ≤ (g * (1 + fp.u) + fp.u) * A +
                    (fp.u * (1 + fp.u) + fp.u) * B := hraw
              _ ≤ G * A + G * B := by
                exact add_le_add
                  (mul_le_mul_of_nonneg_right hCold hA)
                  (mul_le_mul_of_nonneg_right hCnew hB)
              _ = G * (A + B) := by ring
          simpa [q, s, z, A, B, G, p23_roundedDotProduct_succ,
            Fin.sum_univ_castSucc] using hfinal

private lemma p23_absPower_nonneg {n : ℕ} (X : P23Matrix n) (k : ℕ) :
    ∀ i j, 0 ≤ p23PowerSteps (p23AbsMatrix X) k i j := by
  induction k with
  | zero =>
      intro i j
      exact abs_nonneg (X i j)
  | succ k ih =>
      intro i j
      simp only [p23PowerSteps, p23MatMul]
      exact Finset.sum_nonneg fun l _ =>
        mul_nonneg (ih i l) (abs_nonneg (X l j))

private lemma p23_power_abs_le {n : ℕ} (X : P23Matrix n) (k : ℕ) :
    ∀ i j,
      |p23PowerSteps X k i j| ≤
        p23PowerSteps (p23AbsMatrix X) k i j := by
  induction k with
  | zero =>
      intro i j
      exact le_rfl
  | succ k ih =>
      intro i j
      simp only [p23PowerSteps, p23MatMul]
      calc
        |∑ l, p23PowerSteps X k i l * X l j| ≤
            ∑ l, |p23PowerSteps X k i l * X l j| := by
          simpa using
            (Finset.abs_sum_le_sum_abs
              (fun l : Fin n => p23PowerSteps X k i l * X l j) Finset.univ)
        _ = ∑ l, |p23PowerSteps X k i l| * |X l j| := by
          apply Finset.sum_congr rfl
          intro l hl
          rw [abs_mul]
        _ ≤ ∑ l, p23PowerSteps (p23AbsMatrix X) k i l * |X l j| := by
          apply Finset.sum_le_sum
          intro l hl
          exact mul_le_mul_of_nonneg_right (ih i l) (abs_nonneg _)
        _ = ∑ l, p23PowerSteps (p23AbsMatrix X) k i l *
              p23AbsMatrix X l j := by rfl

/-- P23-T1: Lemma 2.2, reindexed so `k` counts the rounded matrix
multiplications after the supplied matrix `X`. -/
theorem p23_t1_lemma_2_2
    (fp : P23FPModel) (n k : ℕ) (X : P23Matrix n)
    (hvalid : P23GammaValid fp.u (k * n)) :
    ∀ i j,
      |p23RoundedPowerSteps fp X k i j - p23PowerSteps X k i j| ≤
        p23Gamma fp.u (k * n) * p23PowerSteps (p23AbsMatrix X) k i j := by
  -- PROOF_START P23-T1-H001
  revert hvalid
  induction k with
  | zero =>
      intro hvalid i j
      simp [p23RoundedPowerSteps, p23PowerSteps, p23Gamma]
  | succ k ih =>
      intro hvalid i j
      have hknNat : k * n ≤ (k + 1) * n :=
        Nat.mul_le_mul_right n (Nat.le_succ k)
      have hknCast : ((k * n : ℕ) : ℝ) ≤ (((k + 1) * n : ℕ) : ℝ) := by
        exact_mod_cast hknNat
      have hvalidPrev : P23GammaValid fp.u (k * n) := by
        unfold P23GammaValid at hvalid ⊢
        exact lt_of_le_of_lt
          (mul_le_mul_of_nonneg_right hknCast fp.u_nonneg) hvalid
      have hnNat : n ≤ (k + 1) * n := by
        calc
          n = 1 * n := by simp
          _ ≤ (k + 1) * n := Nat.mul_le_mul_right n (by omega)
      have hnCast : (n : ℝ) ≤ (((k + 1) * n : ℕ) : ℝ) := by
        exact_mod_cast hnNat
      have hvalidN : P23GammaValid fp.u n := by
        unfold P23GammaValid at hvalid ⊢
        exact lt_of_le_of_lt
          (mul_le_mul_of_nonneg_right hnCast fp.u_nonneg) hvalid
      have hvalidSum : P23GammaValid fp.u (k * n + n) := by
        simpa [Nat.succ_eq_add_one, Nat.add_mul] using hvalid
      let R := p23RoundedPowerSteps fp X k
      let E := p23PowerSteps X k
      let P := p23PowerSteps (p23AbsMatrix X) k
      let g := p23Gamma fp.u (k * n)
      let gn := p23Gamma fp.u n
      let G := p23Gamma fp.u ((k + 1) * n)
      let S := ∑ l : Fin n, P i l * |X l j|
      have hIH : ∀ a b, |R a b - E a b| ≤ g * P a b := by
        simpa [R, E, P, g] using ih hvalidPrev
      have hP : ∀ a b, 0 ≤ P a b := by
        simpa [P] using p23_absPower_nonneg X k
      have hE : ∀ a b, |E a b| ≤ P a b := by
        simpa [E, P] using p23_power_abs_le X k
      have hg : 0 ≤ g := p23_gamma_nonneg fp.u_nonneg hvalidPrev
      have hgn : 0 ≤ gn := p23_gamma_nonneg fp.u_nonneg hvalidN
      have hS : 0 ≤ S := by
        dsimp [S]
        exact Finset.sum_nonneg fun l _ =>
          mul_nonneg (hP i l) (abs_nonneg (X l j))
      have hR : ∀ a b, |R a b| ≤ (1 + g) * P a b := by
        intro a b
        calc
          |R a b| = |(R a b - E a b) + E a b| := by ring_nf
          _ ≤ |R a b - E a b| + |E a b| := abs_add_le _ _
          _ ≤ g * P a b + P a b := add_le_add (hIH a b) (hE a b)
          _ = (1 + g) * P a b := by ring
      let T := ∑ l : Fin n, |R i l| * |X l j|
      have hTS : T ≤ (1 + g) * S := by
        calc
          T ≤ ∑ l : Fin n, ((1 + g) * P i l) * |X l j| := by
            dsimp [T]
            apply Finset.sum_le_sum
            intro l hl
            exact mul_le_mul_of_nonneg_right (hR i l) (abs_nonneg _)
          _ = (1 + g) * S := by
            dsimp [S]
            simp_rw [mul_assoc]
            rw [Finset.mul_sum]
      have hdot0 := p23_roundedDotProduct_error fp n
        (fun l => R i l) (fun l => X l j) hvalidN
      have hdot :
          |p23RoundedDotProduct fp n (fun l => R i l) (fun l => X l j) -
              ∑ l, R i l * X l j| ≤ gn * ((1 + g) * S) := by
        calc
          _ ≤ gn * T := by simpa [gn, T] using hdot0
          _ ≤ gn * ((1 + g) * S) :=
            mul_le_mul_of_nonneg_left hTS hgn
      have hprop :
          |(∑ l, R i l * X l j) - (∑ l, E i l * X l j)| ≤ g * S := by
        calc
          |(∑ l, R i l * X l j) - (∑ l, E i l * X l j)| =
              |∑ l, (R i l - E i l) * X l j| := by
            congr 1
            rw [← Finset.sum_sub_distrib]
            apply Finset.sum_congr rfl
            intro l hl
            ring
          _ ≤ ∑ l, |(R i l - E i l) * X l j| := by
            simpa using
              (Finset.abs_sum_le_sum_abs
                (fun l : Fin n => (R i l - E i l) * X l j) Finset.univ)
          _ = ∑ l, |R i l - E i l| * |X l j| := by
            apply Finset.sum_congr rfl
            intro l hl
            rw [abs_mul]
          _ ≤ ∑ l, (g * P i l) * |X l j| := by
            apply Finset.sum_le_sum
            intro l hl
            exact mul_le_mul_of_nonneg_right (hIH i l) (abs_nonneg _)
          _ = g * S := by
            dsimp [S]
            simp_rw [mul_assoc]
            rw [Finset.mul_sum]
      have hcoeff : gn * (1 + g) + g ≤ G := by
        have hc := p23_gamma_compose fp.u_nonneg (k * n) n hvalidSum
        calc
          gn * (1 + g) + g = g + gn + g * gn := by ring
          _ ≤ G := by
            simpa [g, gn, G, Nat.succ_eq_add_one, Nat.add_mul] using hc
      have htotal :
          |p23RoundedDotProduct fp n (fun l => R i l) (fun l => X l j) -
              ∑ l, E i l * X l j| ≤ G * S := by
        calc
          |p23RoundedDotProduct fp n (fun l => R i l) (fun l => X l j) -
              ∑ l, E i l * X l j| =
              |(p23RoundedDotProduct fp n (fun l => R i l) (fun l => X l j) -
                  ∑ l, R i l * X l j) +
                ((∑ l, R i l * X l j) - (∑ l, E i l * X l j))| := by
            congr 1
            ring
          _ ≤
              |p23RoundedDotProduct fp n (fun l => R i l) (fun l => X l j) -
                  ∑ l, R i l * X l j| +
                |(∑ l, R i l * X l j) - (∑ l, E i l * X l j)| :=
            abs_add_le _ _
          _ ≤ gn * ((1 + g) * S) + g * S := add_le_add hdot hprop
          _ = (gn * (1 + g) + g) * S := by ring
          _ ≤ G * S := mul_le_mul_of_nonneg_right hcoeff hS
      simpa [R, E, P, G, S, p23RoundedPowerSteps, p23PowerSteps,
        p23RoundedMatMul, p23MatMul, p23AbsMatrix] using htotal

end HighamBench
