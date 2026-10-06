import HighamBench.P23Definitions
import Mathlib

namespace HighamBench

open scoped BigOperators

private lemma p23_gamma_nonneg (u : ℝ) (m : ℕ) (hu : 0 ≤ u)
    (hv : P23GammaValid u m) : 0 ≤ p23Gamma u m := by
  rw [p23Gamma]
  exact div_nonneg (mul_nonneg (Nat.cast_nonneg _) hu)
    (le_of_lt (sub_pos.mpr hv))

private lemma p23_gamma_ge_u (u : ℝ) (m : ℕ) (hu : 0 ≤ u)
    (hm : 1 ≤ m) (hv : P23GammaValid u m) : u ≤ p23Gamma u m := by
  have hm' : (1 : ℝ) ≤ (m : ℝ) := by exact_mod_cast hm
  have hd : 0 < 1 - (m : ℝ) * u := sub_pos.mpr hv
  rw [p23Gamma]
  apply (le_div_iff₀ hd).2
  have h₁ : 0 ≤ ((m : ℝ) - 1) * u :=
    mul_nonneg (sub_nonneg.mpr hm') hu
  have h₂ : 0 ≤ (m : ℝ) * u * u :=
    mul_nonneg (mul_nonneg (Nat.cast_nonneg _) hu) hu
  nlinarith

private lemma p23_gamma_mono_valid (u : ℝ) {a b : ℕ} (hu : 0 ≤ u)
    (hab : a ≤ b) (hv : P23GammaValid u b) :
    P23GammaValid u a := by
  unfold P23GammaValid at hv ⊢
  have hab' : (a : ℝ) ≤ (b : ℝ) := by exact_mod_cast hab
  nlinarith [mul_le_mul_of_nonneg_right hab' hu]

private lemma p23_gamma_step (u : ℝ) (m : ℕ) (hu : 0 ≤ u)
    (hv : P23GammaValid u (m + 1)) :
    (1 + u) * p23Gamma u m + u ≤ p23Gamma u (m + 1) := by
  have hm : m ≤ m + 1 := Nat.le_succ m
  have hvm := p23_gamma_mono_valid u hu hm hv
  have hd : 0 < 1 - (m : ℝ) * u := sub_pos.mpr hvm
  have hD : 0 < 1 - ((m + 1 : ℕ) : ℝ) * u := sub_pos.mpr hv
  have hnum : 0 ≤ ((m + 1 : ℕ) : ℝ) * u :=
    mul_nonneg (Nat.cast_nonneg _) hu
  have hid :
      (1 + u) * p23Gamma u m + u =
        (((m + 1 : ℕ) : ℝ) * u) / (1 - (m : ℝ) * u) := by
    have hd' : 1 - u * (m : ℝ) ≠ 0 := by nlinarith
    rw [p23Gamma]
    field_simp [hd']
    push_cast
    ring
  rw [hid, p23Gamma]
  apply (div_le_div_iff₀ hd hD).2
  apply mul_le_mul_of_nonneg_left _ hnum
  push_cast
  nlinarith

private lemma p23_two_rounds_le_gamma (u : ℝ) (m : ℕ) (hu : 0 ≤ u)
    (hm : 1 ≤ m) (hv : P23GammaValid u (m + 1)) :
    2 * u + u ^ 2 ≤ p23Gamma u (m + 1) := by
  have hvm : P23GammaValid u m :=
    p23_gamma_mono_valid u hu (Nat.le_succ m) hv
  calc
    2 * u + u ^ 2 = (1 + u) * u + u := by ring
    _ ≤ (1 + u) * p23Gamma u m + u := by
      have hone : 0 ≤ 1 + u := by linarith
      have hh : (1 + u) * u ≤ (1 + u) * p23Gamma u m :=
        mul_le_mul_of_nonneg_left (p23_gamma_ge_u u m hu hm hvm) hone
      simpa [add_comm] using add_le_add_right hh u
    _ ≤ p23Gamma u (m + 1) := p23_gamma_step u m hu hv

private lemma p23_round_accumulate_step
    (fp : P23FPModel) (m : ℕ) (hm : 1 ≤ m)
    (hv : P23GammaValid fp.u (m + 1))
    (a s q x y : ℝ) (hq : |s| ≤ q)
    (ha : |a - s| ≤ p23Gamma fp.u m * q) :
    |fp.fl_add a (fp.fl_mul x y) - (s + x * y)| ≤
      p23Gamma fp.u (m + 1) * (q + |x| * |y|) := by
  obtain ⟨dm, hdm, hmuleq⟩ := fp.model_mul x y
  obtain ⟨da, hda, haddeq⟩ := fp.model_add a (fp.fl_mul x y)
  have hu := fp.u_nonneg
  have hvm : P23GammaValid fp.u m :=
    p23_gamma_mono_valid fp.u hu (Nat.le_succ m) hv
  have hgamma := p23_gamma_nonneg fp.u m hu hvm
  have hmulerr : |fp.fl_mul x y - x * y| ≤ fp.u * (|x| * |y|) := by
    rw [hmuleq]
    calc
      |x * y * (1 + dm) - x * y| = |x * y * dm| := by congr 1 <;> ring
      _ = |x| * |y| * |dm| := by simp [abs_mul]
      _ ≤ |x| * |y| * fp.u := by gcongr
      _ = fp.u * (|x| * |y|) := by ring
  have hmulabs : |fp.fl_mul x y| ≤ (1 + fp.u) * (|x| * |y|) := by
    rw [hmuleq, abs_mul, abs_mul]
    have h1d : |1 + dm| ≤ 1 + fp.u := by
      calc
        |1 + dm| ≤ |(1 : ℝ)| + |dm| := abs_add_le _ _
        _ ≤ 1 + fp.u := by norm_num; linarith
    calc
      |x| * |y| * |1 + dm| ≤ |x| * |y| * (1 + fp.u) := by
        exact mul_le_mul_of_nonneg_left h1d (mul_nonneg (abs_nonneg _) (abs_nonneg _))
      _ = (1 + fp.u) * (|x| * |y|) := by ring
  have haabs : |a| ≤ q + p23Gamma fp.u m * q := by
    calc
      |a| = |(a - s) + s| := by congr 1 <;> ring
      _ ≤ |a - s| + |s| := abs_add_le _ _
      _ ≤ p23Gamma fp.u m * q + q := add_le_add ha hq
      _ = q + p23Gamma fp.u m * q := by ring
  have haddpert :
      |(a + fp.fl_mul x y) * da| ≤
        fp.u * (q + p23Gamma fp.u m * q +
          (1 + fp.u) * (|x| * |y|)) := by
    rw [abs_mul]
    calc
      |a + fp.fl_mul x y| * |da| ≤
          (|a| + |fp.fl_mul x y|) * fp.u := by
            exact mul_le_mul (abs_add_le _ _) hda (abs_nonneg _)
              (by positivity)
      _ ≤ (q + p23Gamma fp.u m * q +
          (1 + fp.u) * (|x| * |y|)) * fp.u := by
            gcongr
      _ = fp.u * (q + p23Gamma fp.u m * q +
          (1 + fp.u) * (|x| * |y|)) := by ring
  have hraw :
      |fp.fl_add a (fp.fl_mul x y) - (s + x * y)| ≤
        (1 + fp.u) * p23Gamma fp.u m * q + fp.u * q +
          (2 * fp.u + fp.u ^ 2) * (|x| * |y|) := by
    rw [haddeq]
    calc
      |(a + fp.fl_mul x y) * (1 + da) - (s + x * y)| =
          |(a - s) + (fp.fl_mul x y - x * y) +
            (a + fp.fl_mul x y) * da| := by congr 1 <;> ring
      _ ≤ |a - s| + |fp.fl_mul x y - x * y| +
          |(a + fp.fl_mul x y) * da| := by
            calc
              _ ≤ |(a - s) + (fp.fl_mul x y - x * y)| +
                    |(a + fp.fl_mul x y) * da| := abs_add_le _ _
              _ ≤ _ := by gcongr; exact abs_add_le _ _
      _ ≤ p23Gamma fp.u m * q + fp.u * (|x| * |y|) +
          fp.u * (q + p23Gamma fp.u m * q +
            (1 + fp.u) * (|x| * |y|)) := by gcongr
      _ = (1 + fp.u) * p23Gamma fp.u m * q + fp.u * q +
          (2 * fp.u + fp.u ^ 2) * (|x| * |y|) := by ring
  have hcq :
      (1 + fp.u) * p23Gamma fp.u m + fp.u ≤
        p23Gamma fp.u (m + 1) := p23_gamma_step fp.u m hu hv
  have hct : 2 * fp.u + fp.u ^ 2 ≤ p23Gamma fp.u (m + 1) :=
    p23_two_rounds_le_gamma fp.u m hu hm hv
  calc
    _ ≤ ((1 + fp.u) * p23Gamma fp.u m + fp.u) * q +
        (2 * fp.u + fp.u ^ 2) * (|x| * |y|) := by
          convert hraw using 1 <;> ring
    _ ≤ p23Gamma fp.u (m + 1) * q +
        p23Gamma fp.u (m + 1) * (|x| * |y|) := by
          exact add_le_add
            (mul_le_mul_of_nonneg_right hcq (le_trans (abs_nonneg s) hq))
            (mul_le_mul_of_nonneg_right hct
              (mul_nonneg (abs_nonneg x) (abs_nonneg y)))
    _ = _ := by ring

private lemma p23_rounded_fold_error
    (fp : P23FPModel) (r m : ℕ) (hr : 1 ≤ r)
    (hv : P23GammaValid fp.u (r + m))
    (a s q : ℝ) (x y : Fin m → ℝ)
    (hq : |s| ≤ q)
    (ha : |a - s| ≤ p23Gamma fp.u r * q) :
    |Fin.foldl m
        (fun acc i => fp.fl_add acc (fp.fl_mul (x i) (y i))) a -
      (s + ∑ i, x i * y i)| ≤
      p23Gamma fp.u (r + m) *
        (q + ∑ i, |x i| * |y i|) := by
  induction m generalizing r a s q with
  | zero =>
      simpa using ha
  | succ m ih =>
      have hrs : 1 ≤ r + 1 := by omega
      have hrs_le : r + 1 ≤ r + (m + 1) := by omega
      have hvstep : P23GammaValid fp.u (r + 1) :=
        p23_gamma_mono_valid fp.u fp.u_nonneg hrs_le hv
      let a' := fp.fl_add a (fp.fl_mul (x 0) (y 0))
      let s' := s + x 0 * y 0
      let q' := q + |x 0| * |y 0|
      have hq' : |s'| ≤ q' := by
        dsimp [s', q']
        calc
          |s + x 0 * y 0| ≤ |s| + |x 0 * y 0| := abs_add_le _ _
          _ = |s| + |x 0| * |y 0| := by rw [abs_mul]
          _ ≤ q + |x 0| * |y 0| := by gcongr
      have ha' : |a' - s'| ≤ p23Gamma fp.u (r + 1) * q' := by
        exact p23_round_accumulate_step fp r hr hvstep a s q (x 0) (y 0) hq ha
      have hv' : P23GammaValid fp.u ((r + 1) + m) := by
        convert hv using 1 <;> omega
      have hi := ih (r + 1) hrs hv' a' s' q'
        (fun i => x i.succ) (fun i => y i.succ) hq' ha'
      rw [Fin.foldl_succ, Fin.sum_univ_succ, Fin.sum_univ_succ]
      convert hi using 1 <;> simp only [a', s', q'] <;> ring

private lemma p23_rounded_dot_error
    (fp : P23FPModel) (n : ℕ) (x y : Fin n → ℝ)
    (hv : P23GammaValid fp.u n) :
    |p23RoundedDotProduct fp n x y - ∑ i, x i * y i| ≤
      p23Gamma fp.u n * ∑ i, |x i| * |y i| := by
  cases n with
  | zero => simp [p23RoundedDotProduct, p23Gamma]
  | succ m =>
      have h1le : 1 ≤ m + 1 := by omega
      have hv1 : P23GammaValid fp.u 1 :=
        p23_gamma_mono_valid fp.u fp.u_nonneg h1le hv
      obtain ⟨d, hd, heq⟩ := fp.model_mul (x 0) (y 0)
      have hseed0 :
          |fp.fl_mul (x 0) (y 0) - x 0 * y 0| ≤
            fp.u * (|x 0| * |y 0|) := by
        rw [heq]
        calc
          |x 0 * y 0 * (1 + d) - x 0 * y 0| =
              |x 0 * y 0 * d| := by congr 1 <;> ring
          _ = |x 0| * |y 0| * |d| := by simp [abs_mul]
          _ ≤ |x 0| * |y 0| * fp.u := by gcongr
          _ = fp.u * (|x 0| * |y 0|) := by ring
      have hseed :
          |fp.fl_mul (x 0) (y 0) - x 0 * y 0| ≤
            p23Gamma fp.u 1 * (|x 0| * |y 0|) := by
        calc
          _ ≤ fp.u * (|x 0| * |y 0|) := hseed0
          _ ≤ p23Gamma fp.u 1 * (|x 0| * |y 0|) := by
            exact mul_le_mul_of_nonneg_right
              (p23_gamma_ge_u fp.u 1 fp.u_nonneg (by omega) hv1)
              (mul_nonneg (abs_nonneg _) (abs_nonneg _))
      have hq : |x 0 * y 0| ≤ |x 0| * |y 0| := by rw [abs_mul]
      have hf := p23_rounded_fold_error fp 1 m (by omega) (by
          convert hv using 1 <;> omega)
        (fp.fl_mul (x 0) (y 0)) (x 0 * y 0)
        (|x 0| * |y 0|) (fun i => x i.succ) (fun i => y i.succ)
        hq hseed
      simpa only [p23RoundedDotProduct, Fin.sum_univ_succ,
        Nat.one_add] using hf

private lemma p23_abs_power_nonneg {n : ℕ} (X : P23Matrix n) :
    ∀ k i j, 0 ≤ p23PowerSteps (p23AbsMatrix X) k i j := by
  intro k
  induction k with
  | zero =>
      intro i j
      simp [p23PowerSteps, p23AbsMatrix]
  | succ k ih =>
      intro i j
      simp only [p23PowerSteps, p23MatMul]
      exact Finset.sum_nonneg fun l _ =>
        mul_nonneg (ih i l) (abs_nonneg (X l j))

private lemma p23_exact_power_abs_le {n : ℕ} (X : P23Matrix n) :
    ∀ k i j,
      |p23PowerSteps X k i j| ≤
        p23PowerSteps (p23AbsMatrix X) k i j := by
  intro k
  induction k with
  | zero =>
      intro i j
      simp [p23PowerSteps, p23AbsMatrix]
  | succ k ih =>
      intro i j
      simp only [p23PowerSteps, p23MatMul]
      calc
        |∑ l, p23PowerSteps X k i l * X l j| ≤
            ∑ l, |p23PowerSteps X k i l * X l j| := by
              exact Finset.abs_sum_le_sum_abs _ _
        _ = ∑ l, |p23PowerSteps X k i l| * |X l j| := by
              apply Finset.sum_congr rfl
              intro l _
              rw [abs_mul]
        _ ≤ ∑ l, p23PowerSteps (p23AbsMatrix X) k i l * |X l j| := by
              gcongr with l
              exact ih i l

private lemma p23_rounded_matmul_error
    (fp : P23FPModel) {n : ℕ} (A B : P23Matrix n)
    (hv : P23GammaValid fp.u n) (i j : Fin n) :
    |p23RoundedMatMul fp A B i j - p23MatMul A B i j| ≤
      p23Gamma fp.u n * p23MatMul (p23AbsMatrix A) (p23AbsMatrix B) i j := by
  simpa only [p23RoundedMatMul, p23MatMul, p23AbsMatrix] using
    p23_rounded_dot_error fp n (A i) (fun l => B l j) hv

private lemma p23_gamma_combine (u : ℝ) (a b : ℕ) (hu : 0 ≤ u)
    (hv : P23GammaValid u (a + b)) :
    p23Gamma u b * (1 + p23Gamma u a) + p23Gamma u a ≤
      p23Gamma u (a + b) := by
  let A : ℝ := (a : ℝ) * u
  let B : ℝ := (b : ℝ) * u
  have hA0 : 0 ≤ A := by dsimp [A]; positivity
  have hB0 : 0 ≤ B := by dsimp [B]; positivity
  have hsum : A + B < 1 := by
    unfold P23GammaValid at hv
    dsimp [A, B]
    push_cast at hv
    nlinarith
  have hA : A < 1 := lt_of_le_of_lt (by linarith) hsum
  have hB : B < 1 := lt_of_le_of_lt (by linarith) hsum
  have hdA : 0 < 1 - A := sub_pos.mpr hA
  have hdB : 0 < 1 - B := sub_pos.mpr hB
  have hdS : 0 < 1 - A - B := by linarith
  have hlhs :
      p23Gamma u b * (1 + p23Gamma u a) + p23Gamma u a =
        (A + B - A * B) / ((1 - A) * (1 - B)) := by
    have hAne : 1 - A ≠ 0 := ne_of_gt hdA
    have hBne : 1 - B ≠ 0 := ne_of_gt hdB
    have hAne' : 1 - u * (a : ℝ) ≠ 0 := by
      dsimp [A] at hdA
      nlinarith
    have hBne' : 1 - u * (b : ℝ) ≠ 0 := by
      dsimp [B] at hdB
      nlinarith
    dsimp [A, B] at hAne hBne ⊢
    rw [p23Gamma, p23Gamma]
    field_simp [hAne, hBne, hAne', hBne']
    ring
  have hrhs :
      p23Gamma u (a + b) = (A + B) / (1 - A - B) := by
    dsimp [A, B]
    rw [p23Gamma]
    push_cast
    congr 1 <;> ring
  rw [hlhs, hrhs]
  apply (div_le_div_iff₀ (mul_pos hdA hdB) hdS).2
  have hAB : 0 ≤ A * B := mul_nonneg hA0 hB0
  nlinarith

private lemma p23_power_error_bound
    (fp : P23FPModel) (n : ℕ) (X : P23Matrix n) :
    ∀ k, P23GammaValid fp.u (k * n) → ∀ i j,
      |p23RoundedPowerSteps fp X k i j - p23PowerSteps X k i j| ≤
        p23Gamma fp.u (k * n) *
          p23PowerSteps (p23AbsMatrix X) k i j := by
  intro k
  induction k with
  | zero =>
      intro hv i j
      simp [p23RoundedPowerSteps, p23PowerSteps, p23Gamma]
  | succ k ih =>
      intro hv i j
      have hkn_le : k * n ≤ (k + 1) * n := by
        exact Nat.mul_le_mul_right n (Nat.le_succ k)
      have hn_le : n ≤ (k + 1) * n := by
        calc
          n = 1 * n := by omega
          _ ≤ (k + 1) * n := Nat.mul_le_mul_right n (by omega)
      have hvk : P23GammaValid fp.u (k * n) :=
        p23_gamma_mono_valid fp.u fp.u_nonneg hkn_le hv
      have hvn : P23GammaValid fp.u n :=
        p23_gamma_mono_valid fp.u fp.u_nonneg hn_le hv
      have hgk : 0 ≤ p23Gamma fp.u (k * n) :=
        p23_gamma_nonneg fp.u (k * n) fp.u_nonneg hvk
      have hgn : 0 ≤ p23Gamma fp.u n :=
        p23_gamma_nonneg fp.u n fp.u_nonneg hvn
      have hrounded_abs (l : Fin n) :
          |p23RoundedPowerSteps fp X k i l| ≤
            (1 + p23Gamma fp.u (k * n)) *
              p23PowerSteps (p23AbsMatrix X) k i l := by
        calc
          |p23RoundedPowerSteps fp X k i l| =
              |(p23RoundedPowerSteps fp X k i l -
                  p23PowerSteps X k i l) + p23PowerSteps X k i l| := by
                    congr 1 <;> ring
          _ ≤ |p23RoundedPowerSteps fp X k i l -
                  p23PowerSteps X k i l| +
                |p23PowerSteps X k i l| := abs_add_le _ _
          _ ≤ p23Gamma fp.u (k * n) *
                  p23PowerSteps (p23AbsMatrix X) k i l +
                p23PowerSteps (p23AbsMatrix X) k i l := by
                  exact add_le_add (ih hvk i l)
                    (p23_exact_power_abs_le X k i l)
          _ = (1 + p23Gamma fp.u (k * n)) *
                p23PowerSteps (p23AbsMatrix X) k i l := by ring
      have hmatrix_abs :
          p23MatMul
              (p23AbsMatrix (p23RoundedPowerSteps fp X k))
              (p23AbsMatrix X) i j ≤
            (1 + p23Gamma fp.u (k * n)) *
              p23PowerSteps (p23AbsMatrix X) (k + 1) i j := by
        simp only [p23MatMul, p23AbsMatrix, p23PowerSteps]
        calc
          (∑ l, |p23RoundedPowerSteps fp X k i l| * |X l j|) ≤
              ∑ l, ((1 + p23Gamma fp.u (k * n)) *
                p23PowerSteps (p23AbsMatrix X) k i l) * |X l j| := by
                  gcongr with l
                  exact hrounded_abs l
          _ = (1 + p23Gamma fp.u (k * n)) *
              ∑ l, p23PowerSteps (p23AbsMatrix X) k i l * |X l j| := by
                rw [Finset.mul_sum]
                apply Finset.sum_congr rfl
                intro l _
                ring
      have hfresh :
          |p23RoundedMatMul fp (p23RoundedPowerSteps fp X k) X i j -
              p23MatMul (p23RoundedPowerSteps fp X k) X i j| ≤
            (p23Gamma fp.u n * (1 + p23Gamma fp.u (k * n))) *
              p23PowerSteps (p23AbsMatrix X) (k + 1) i j := by
        calc
          _ ≤ p23Gamma fp.u n *
              p23MatMul
                (p23AbsMatrix (p23RoundedPowerSteps fp X k))
                (p23AbsMatrix X) i j :=
                  p23_rounded_matmul_error fp
                    (p23RoundedPowerSteps fp X k) X hvn i j
          _ ≤ p23Gamma fp.u n *
              ((1 + p23Gamma fp.u (k * n)) *
                p23PowerSteps (p23AbsMatrix X) (k + 1) i j) :=
                  mul_le_mul_of_nonneg_left hmatrix_abs hgn
          _ = _ := by ring
      have hpropagated :
          |p23MatMul (p23RoundedPowerSteps fp X k) X i j -
              p23MatMul (p23PowerSteps X k) X i j| ≤
            p23Gamma fp.u (k * n) *
              p23PowerSteps (p23AbsMatrix X) (k + 1) i j := by
        simp only [p23MatMul, p23PowerSteps]
        calc
          |(∑ l, p23RoundedPowerSteps fp X k i l * X l j) -
              ∑ l, p23PowerSteps X k i l * X l j| =
              |∑ l, (p23RoundedPowerSteps fp X k i l * X l j -
                p23PowerSteps X k i l * X l j)| := by
                  congr 1
                  rw [Finset.sum_sub_distrib]
          _ =
              |∑ l, (p23RoundedPowerSteps fp X k i l -
                p23PowerSteps X k i l) * X l j| := by
                  congr 1
                  apply Finset.sum_congr rfl
                  intro l _
                  ring
          _ ≤ ∑ l, |(p23RoundedPowerSteps fp X k i l -
                p23PowerSteps X k i l) * X l j| := by
                  exact Finset.abs_sum_le_sum_abs _ _
          _ = ∑ l, |p23RoundedPowerSteps fp X k i l -
                p23PowerSteps X k i l| * |X l j| := by
                  apply Finset.sum_congr rfl
                  intro l _
                  rw [abs_mul]
          _ ≤ ∑ l, (p23Gamma fp.u (k * n) *
                p23PowerSteps (p23AbsMatrix X) k i l) * |X l j| := by
                  gcongr with l
                  exact ih hvk i l
          _ = p23Gamma fp.u (k * n) *
              ∑ l, p23PowerSteps (p23AbsMatrix X) k i l * |X l j| := by
                  rw [Finset.mul_sum]
                  apply Finset.sum_congr rfl
                  intro l _
                  ring
      have hcombine :
          p23Gamma fp.u n * (1 + p23Gamma fp.u (k * n)) +
              p23Gamma fp.u (k * n) ≤
            p23Gamma fp.u ((k + 1) * n) := by
        have hvsum : P23GammaValid fp.u (k * n + n) := by
          simpa [Nat.add_mul] using hv
        have hc := p23_gamma_combine fp.u (k * n) n fp.u_nonneg hvsum
        simpa [Nat.add_mul] using hc
      have habsnext :
          0 ≤ p23PowerSteps (p23AbsMatrix X) (k + 1) i j :=
        p23_abs_power_nonneg X (k + 1) i j
      simp only [p23RoundedPowerSteps, p23PowerSteps]
      calc
        |p23RoundedMatMul fp (p23RoundedPowerSteps fp X k) X i j -
            p23MatMul (p23PowerSteps X k) X i j| ≤
            |p23RoundedMatMul fp (p23RoundedPowerSteps fp X k) X i j -
              p23MatMul (p23RoundedPowerSteps fp X k) X i j| +
            |p23MatMul (p23RoundedPowerSteps fp X k) X i j -
              p23MatMul (p23PowerSteps X k) X i j| := by
                calc
                  _ = |(p23RoundedMatMul fp
                        (p23RoundedPowerSteps fp X k) X i j -
                        p23MatMul (p23RoundedPowerSteps fp X k) X i j) +
                      (p23MatMul (p23RoundedPowerSteps fp X k) X i j -
                        p23MatMul (p23PowerSteps X k) X i j)| := by
                          congr 1 <;> ring
                  _ ≤ _ := abs_add_le _ _
        _ ≤ (p23Gamma fp.u n * (1 + p23Gamma fp.u (k * n)) +
              p23Gamma fp.u (k * n)) *
              p23MatMul
                (p23PowerSteps (p23AbsMatrix X) k)
                (p23AbsMatrix X) i j := by
                  rw [add_mul]
                  exact add_le_add hfresh hpropagated
        _ ≤ p23Gamma fp.u ((k + 1) * n) *
              p23MatMul
                (p23PowerSteps (p23AbsMatrix X) k)
                (p23AbsMatrix X) i j :=
                  mul_le_mul_of_nonneg_right hcombine habsnext

/-- P23-T1: Lemma 2.2, reindexed so `k` counts the rounded matrix
multiplications after the supplied matrix `X`. -/
theorem p23_t1_lemma_2_2
    (fp : P23FPModel) (n k : ℕ) (X : P23Matrix n)
    (hvalid : P23GammaValid fp.u (k * n)) :
    ∀ i j,
      |p23RoundedPowerSteps fp X k i j - p23PowerSteps X k i j| ≤
        p23Gamma fp.u (k * n) * p23PowerSteps (p23AbsMatrix X) k i j := by
  -- PROOF_START P23-T1-H001
  exact p23_power_error_bound fp n X k hvalid

end HighamBench
