import HighamBench.P09Definitions

namespace HighamBench

open scoped BigOperators

private lemma p09_componentwise_scale_norm_le (x : ℂ) (a b : ℝ)
    (ha : |a| ≤ 1) (hb : |b| ≤ 1) :
    ‖({ re := a * x.re, im := b * x.im } : ℂ)‖ ≤ ‖x‖ := by
  have ha2 : a ^ 2 ≤ 1 := (sq_le_one_iff_abs_le_one a).2 ha
  have hb2 : b ^ 2 ≤ 1 := (sq_le_one_iff_abs_le_one b).2 hb
  apply (sq_le_sq₀ (norm_nonneg _) (norm_nonneg _)).mp
  rw [Complex.sq_norm, Complex.sq_norm, Complex.normSq_apply,
    Complex.normSq_apply]
  nlinarith [mul_le_mul_of_nonneg_right ha2 (sq_nonneg x.re),
    mul_le_mul_of_nonneg_right hb2 (sq_nonneg x.im)]

private lemma p09_roundedComplexAdd_error_le
    (model : P09WilkinsonModel) (x y : ℂ) :
    ‖p09RoundedComplexAdd model x y - (x + y)‖ ≤
      model.epsilon * (‖x‖ + ‖y‖) := by
  obtain ⟨ax, ay, hax, hay, hx⟩ := model.add_model x.re y.re
  obtain ⟨bx, cy, hbx, hcy, hy⟩ := model.add_model x.im y.im
  let dx : ℂ := { re := ax * x.re, im := bx * x.im }
  let dy : ℂ := { re := ay * y.re, im := cy * y.im }
  have hdx : ‖dx‖ ≤ ‖x‖ :=
    p09_componentwise_scale_norm_le x ax bx hax hbx
  have hdy : ‖dy‖ ≤ ‖y‖ :=
    p09_componentwise_scale_norm_le y ay cy hay hcy
  have heq : p09RoundedComplexAdd model x y - (x + y) =
      (model.epsilon : ℂ) * (dx + dy) := by
    apply Complex.ext <;> simp [p09RoundedComplexAdd, dx, dy, hx, hy] <;> ring
  rw [heq, norm_mul, Complex.norm_real, Real.norm_eq_abs,
    abs_of_pos model.epsilon_pos]
  exact mul_le_mul_of_nonneg_left
    ((norm_add_le dx dy).trans (add_le_add hdx hdy))
    (le_of_lt model.epsilon_pos)

private lemma p09_complexNorm2_sq {n : ℕ} [NeZero n]
    (x : ZMod n → ℂ) :
    p09ComplexNorm2 x ^ 2 = ∑ i : ZMod n, ‖x i‖ ^ 2 := by
  unfold p09ComplexNorm2 p09ComplexNorm2Sq
  rw [Real.sq_sqrt]
  exact Finset.sum_nonneg fun i _ ↦ sq_nonneg ‖x i‖

private lemma p09_complexNorm2_nonneg {n : ℕ} [NeZero n]
    (x : ZMod n → ℂ) : 0 ≤ p09ComplexNorm2 x := by
  exact Real.sqrt_nonneg _

private lemma p09_complexNorm2_eq_euclidean {n : ℕ} [NeZero n]
    (x : ZMod n → ℂ) :
    p09ComplexNorm2 x =
      ‖(WithLp.toLp 2 x : EuclideanSpace ℂ (ZMod n))‖ := by
  rw [EuclideanSpace.norm_eq]
  rfl

private lemma p09_complexNorm2_add_le {n : ℕ} [NeZero n]
    (x y : ZMod n → ℂ) :
    p09ComplexNorm2 (fun i ↦ x i + y i) ≤
      p09ComplexNorm2 x + p09ComplexNorm2 y := by
  rw [p09_complexNorm2_eq_euclidean, p09_complexNorm2_eq_euclidean,
    p09_complexNorm2_eq_euclidean]
  simpa using
    (norm_add_le
      (WithLp.toLp 2 x : EuclideanSpace ℂ (ZMod n))
      (WithLp.toLp 2 y : EuclideanSpace ℂ (ZMod n)))

private lemma p09_sum_norm_sq_le_card_mul {ι : Type*} [Fintype ι]
    (x : ι → ℂ) :
    (∑ i, ‖x i‖) ^ 2 ≤ Fintype.card ι * ∑ i, ‖x i‖ ^ 2 := by
  simpa [mul_comm] using
    (Finset.sum_mul_sq_le_sq_mul_sq (Finset.univ : Finset ι)
      (fun i ↦ ‖x i‖) (fun _ ↦ (1 : ℝ)))

private lemma p09_complexNorm2_le_of_pointwise_l1 {n : ℕ} [NeZero n]
    (e x : ZMod n → ℂ) (c : ℝ) (hc : 0 ≤ c)
    (h : ∀ k, ‖e k‖ ≤ c * ∑ j, ‖x j‖) :
    p09ComplexNorm2 e ≤ (n : ℝ) * c * p09ComplexNorm2 x := by
  have hn : (0 : ℝ) ≤ n := by positivity
  apply (sq_le_sq₀ (p09_complexNorm2_nonneg e)
    (mul_nonneg (mul_nonneg hn hc) (p09_complexNorm2_nonneg x))).mp
  rw [p09_complexNorm2_sq e]
  have hpoint : ∀ k : ZMod n,
      ‖e k‖ ^ 2 ≤ (c * ∑ j : ZMod n, ‖x j‖) ^ 2 := by
    intro k
    exact (sq_le_sq₀ (norm_nonneg _) (mul_nonneg hc (Finset.sum_nonneg
      fun _ _ ↦ norm_nonneg _))).2 (h k)
  calc
    (∑ k : ZMod n, ‖e k‖ ^ 2)
        ≤ ∑ _k : ZMod n, (c * ∑ j : ZMod n, ‖x j‖) ^ 2 :=
          Finset.sum_le_sum fun k _ ↦ hpoint k
    _ = (n : ℝ) * (c * ∑ j : ZMod n, ‖x j‖) ^ 2 := by simp
    _ ≤ (n : ℝ) * (c ^ 2 * ((n : ℝ) * ∑ j : ZMod n, ‖x j‖ ^ 2)) := by
      gcongr
      calc
        (c * ∑ j : ZMod n, ‖x j‖) ^ 2 =
            c ^ 2 * (∑ j : ZMod n, ‖x j‖) ^ 2 := by ring
        _ ≤ c ^ 2 * ((n : ℝ) * ∑ j : ZMod n, ‖x j‖ ^ 2) := by
          gcongr
          simpa using (p09_sum_norm_sq_le_card_mul x)
    _ = ((n : ℝ) * c * p09ComplexNorm2 x) ^ 2 := by
      rw [← p09_complexNorm2_sq x]
      ring

private lemma p09_stdAddChar_two_zero :
    ZMod.stdAddChar (N := 2) (0 : ZMod 2) = 1 :=
  (ZMod.stdAddChar (N := 2)).map_zero_eq_one

private lemma p09_stdAddChar_two_one :
    ZMod.stdAddChar (N := 2) (1 : ZMod 2) = -1 := by
  rw [show (1 : ZMod 2) = ((1 : ℤ) : ZMod 2) by norm_num,
    ZMod.stdAddChar_coe]
  convert Complex.exp_pi_mul_I using 2 <;> norm_num <;> ring

private lemma p09_sum_zmod_two {M : Type*} [AddCommMonoid M]
    (f : ZMod 2 → M) : ∑ j : ZMod 2, f j = f 0 + f 1 := by
  rw [← Equiv.sum_comp (ZMod.finEquiv 2).toEquiv, Fin.sum_univ_two]
  rfl

private lemma p09_radixTwo_exact_block (x : ZMod 2 → ℂ) (k : ZMod 2) :
    (∑ j : ZMod 2, ZMod.stdAddChar (j * k) * x j) =
      p09RadixTwoCoefficientApply ((0 : ZMod 2) * k) (x 0) +
      p09RadixTwoCoefficientApply ((1 : ZMod 2) * k) (x 1) := by
  rw [p09_sum_zmod_two]
  have hk : k = 0 ∨ k = 1 := by
    fin_cases k
    · left; rfl
    · right; rfl
  rcases hk with rfl | rfl
  · simp only [mul_zero, p09_stdAddChar_two_zero, one_mul]
    simp [p09RadixTwoCoefficientApply]
  · simp only [mul_one, p09_stdAddChar_two_zero, p09_stdAddChar_two_one,
      one_mul, neg_mul]
    simp [p09RadixTwoCoefficientApply]

private lemma p09_radixTwo_rounded_block (model : P09WilkinsonModel)
    (x : ZMod 2 → ℂ) (k : ZMod 2) :
    p09RoundedRadixTwoBlock model x k =
      p09RoundedComplexAdd model
        (p09RadixTwoCoefficientApply ((0 : ZMod 2) * k) (x 0))
        (p09RadixTwoCoefficientApply ((1 : ZMod 2) * k) (x 1)) := by
  simp [p09RoundedRadixTwoBlock, p09RoundedComplexSum, recursiveSum]
  rfl

private lemma p09_radixTwo_coefficient_norm (j : ZMod 2) (x : ℂ) :
    ‖p09RadixTwoCoefficientApply j x‖ = ‖x‖ := by
  by_cases h : j = 0
  · simp [p09RadixTwoCoefficientApply, h]
  · simp [p09RadixTwoCoefficientApply, h]

private lemma p09_radixTwo_block_error_pointwise
    (model : P09WilkinsonModel) (x : ZMod 2 → ℂ) (k : ZMod 2) :
    ‖p09RoundedRadixTwoBlock model x k -
        ∑ j : ZMod 2, ZMod.stdAddChar (j * k) * x j‖ ≤
      model.epsilon * ∑ j : ZMod 2, ‖x j‖ := by
  rw [p09_radixTwo_rounded_block, p09_radixTwo_exact_block,
    p09_sum_zmod_two]
  simpa only [p09_radixTwo_coefficient_norm] using
    p09_roundedComplexAdd_error_le model
      (p09RadixTwoCoefficientApply ((0 : ZMod 2) * k) (x 0))
      (p09RadixTwoCoefficientApply ((1 : ZMod 2) * k) (x 1))

private lemma p09_radixTwo_block_error_norm2
    (model : P09WilkinsonModel) (x : ZMod 2 → ℂ) :
    p09ComplexNorm2 (fun k ↦ p09RoundedRadixTwoBlock model x k -
        ∑ j : ZMod 2, ZMod.stdAddChar (j * k) * x j) ≤
      2 * model.epsilon * p09ComplexNorm2 x := by
  exact p09_complexNorm2_le_of_pointwise_l1 _ _ model.epsilon
    (le_of_lt model.epsilon_pos)
    (p09_radixTwo_block_error_pointwise model x)

private lemma p09_abs_re_add_abs_im_le_three_halves_norm (x : ℂ) :
    |x.re| + |x.im| ≤ (3 / 2 : ℝ) * ‖x‖ := by
  have hsqrt : Real.sqrt 2 ≤ (3 / 2 : ℝ) := by
    rw [Real.sqrt_le_iff]
    constructor <;> norm_num
  have hsquare : (|x.re| + |x.im|) ^ 2 ≤ 2 * ‖x‖ ^ 2 := by
    rw [Complex.sq_norm, Complex.normSq_apply]
    nlinarith [sq_nonneg (|x.re| - |x.im|), sq_abs x.re, sq_abs x.im]
  have hs : |x.re| + |x.im| ≤ Real.sqrt 2 * ‖x‖ := by
    have hsq2 : (Real.sqrt 2 * ‖x‖) ^ 2 = 2 * ‖x‖ ^ 2 := by
      rw [mul_pow, Real.sq_sqrt (by norm_num : (0 : ℝ) ≤ 2)]
    apply (sq_le_sq₀ (by positivity) (by positivity)).mp
    rwa [hsq2]
  exact hs.trans (mul_le_mul_of_nonneg_right hsqrt (norm_nonneg x))

private lemma p09_roundedComplexMul_error_le
    (model : P09WilkinsonModel) (x y : ℂ) :
    ‖p09RoundedComplexMul model x y - x * y‖ ≤
      (3 * model.epsilon + 2 * model.epsilon ^ 2) * ‖x‖ * ‖y‖ := by
  have hu : 0 ≤ model.epsilon := le_of_lt model.epsilon_pos
  obtain ⟨a₁, ha₁, h₁⟩ := model.mul_model x.re y.re
  obtain ⟨a₂, ha₂, h₂⟩ := model.mul_model x.re y.im
  obtain ⟨b₁, hb₁, h₃⟩ := model.mul_model x.im y.im
  obtain ⟨b₂, hb₂, h₄⟩ := model.mul_model x.im y.re
  let A : ℂ := ⟨model.flMul x.re y.re, model.flMul x.re y.im⟩
  let B : ℂ := ⟨-model.flMul x.im y.im, model.flMul x.im y.re⟩
  let A₀ : ℂ := ⟨x.re * y.re, x.re * y.im⟩
  let B₀ : ℂ := ⟨-x.im * y.im, x.im * y.re⟩
  let dA : ℂ := ⟨a₁ * (x.re * y.re), a₂ * (x.re * y.im)⟩
  let dB : ℂ := ⟨-b₁ * (x.im * y.im), b₂ * (x.im * y.re)⟩
  have hA : A = A₀ + (model.epsilon : ℂ) * dA := by
    apply Complex.ext <;> simp [A, A₀, dA, h₁, h₂] <;> ring
  have hB : B = B₀ + (model.epsilon : ℂ) * dB := by
    apply Complex.ext <;> simp [B, B₀, dB, h₃, h₄] <;> ring
  have hdA : ‖dA‖ ≤ |x.re| * ‖y‖ := by
    have h := p09_componentwise_scale_norm_le y a₁ a₂ ha₁ ha₂
    have heq : dA = (x.re : ℂ) *
        ({ re := a₁ * y.re, im := a₂ * y.im } : ℂ) := by
      apply Complex.ext <;> simp [dA] <;> ring
    rw [heq, norm_mul, Complex.norm_real, Real.norm_eq_abs]
    gcongr
  have hdB : ‖dB‖ ≤ |x.im| * ‖y‖ := by
    have h := p09_componentwise_scale_norm_le y b₁ b₂ hb₁ hb₂
    have heq : dB = (x.im : ℂ) *
        ({ re := -b₁ * y.im, im := b₂ * y.re } : ℂ) := by
      apply Complex.ext <;> simp [dB] <;> ring
    have hrot : ‖({ re := -b₁ * y.im, im := b₂ * y.re } : ℂ)‖ ≤ ‖y‖ := by
      apply (sq_le_sq₀ (norm_nonneg _) (norm_nonneg _)).mp
      rw [Complex.sq_norm, Complex.sq_norm, Complex.normSq_apply,
        Complex.normSq_apply]
      have hb₁2 : b₁ ^ 2 ≤ 1 := (sq_le_one_iff_abs_le_one b₁).2 hb₁
      have hb₂2 : b₂ ^ 2 ≤ 1 := (sq_le_one_iff_abs_le_one b₂).2 hb₂
      nlinarith [mul_le_mul_of_nonneg_right hb₁2 (sq_nonneg y.im),
        mul_le_mul_of_nonneg_right hb₂2 (sq_nonneg y.re)]
    rw [heq, norm_mul, Complex.norm_real, Real.norm_eq_abs]
    gcongr
  have hA_norm : ‖A‖ ≤ (1 + model.epsilon) * |x.re| * ‖y‖ := by
    rw [hA]
    calc
      ‖A₀ + (model.epsilon : ℂ) * dA‖
          ≤ ‖A₀‖ + ‖(model.epsilon : ℂ) * dA‖ := norm_add_le _ _
      _ ≤ |x.re| * ‖y‖ + model.epsilon * (|x.re| * ‖y‖) := by
        have hA₀ : ‖A₀‖ = |x.re| * ‖y‖ := by
          have heq : A₀ = (x.re : ℂ) * y := by
            apply Complex.ext <;> simp [A₀] <;> ring
          rw [heq, norm_mul, Complex.norm_real, Real.norm_eq_abs]
        rw [hA₀, norm_mul, Complex.norm_real, Real.norm_eq_abs,
          abs_of_pos model.epsilon_pos]
        gcongr
      _ = (1 + model.epsilon) * |x.re| * ‖y‖ := by ring
  have hB_norm : ‖B‖ ≤ (1 + model.epsilon) * |x.im| * ‖y‖ := by
    rw [hB]
    calc
      ‖B₀ + (model.epsilon : ℂ) * dB‖
          ≤ ‖B₀‖ + ‖(model.epsilon : ℂ) * dB‖ := norm_add_le _ _
      _ ≤ |x.im| * ‖y‖ + model.epsilon * (|x.im| * ‖y‖) := by
        have hB₀ : ‖B₀‖ = |x.im| * ‖y‖ := by
          apply (sq_eq_sq₀ (norm_nonneg _) (by positivity)).mp
          rw [Complex.sq_norm, Complex.normSq_apply, mul_pow,
            Complex.sq_norm, Complex.normSq_apply]
          simp [B₀, sq_abs]
          ring
        rw [hB₀, norm_mul, Complex.norm_real, Real.norm_eq_abs,
          abs_of_pos model.epsilon_pos]
        gcongr
      _ = (1 + model.epsilon) * |x.im| * ‖y‖ := by ring
  have hrounded : p09RoundedComplexMul model x y =
      p09RoundedComplexAdd model A B := by rfl
  have hexact : A₀ + B₀ = x * y := by
    apply Complex.ext <;> simp [A₀, B₀] <;> ring
  calc
    ‖p09RoundedComplexMul model x y - x * y‖
        = ‖(p09RoundedComplexAdd model A B - (A + B)) +
            ((A - A₀) + (B - B₀))‖ := by
          congr 1
          rw [hrounded, ← hexact]
          abel
    _ ≤ ‖p09RoundedComplexAdd model A B - (A + B)‖ +
          (‖A - A₀‖ + ‖B - B₀‖) := by
          exact (norm_add_le _ _).trans (add_le_add le_rfl (norm_add_le _ _))
    _ ≤ model.epsilon * (‖A‖ + ‖B‖) +
          (model.epsilon * (|x.re| * ‖y‖) +
            model.epsilon * (|x.im| * ‖y‖)) := by
          gcongr
          · exact p09_roundedComplexAdd_error_le model A B
          · rw [hA, add_sub_cancel_left, norm_mul, Complex.norm_real,
              Real.norm_eq_abs, abs_of_pos model.epsilon_pos]
            gcongr
          · rw [hB, add_sub_cancel_left, norm_mul, Complex.norm_real,
              Real.norm_eq_abs, abs_of_pos model.epsilon_pos]
            gcongr
    _ ≤ (2 * model.epsilon + model.epsilon ^ 2) *
          (|x.re| + |x.im|) * ‖y‖ := by
          have hnorm := add_le_add hA_norm hB_norm
          calc
            model.epsilon * (‖A‖ + ‖B‖) +
                (model.epsilon * (|x.re| * ‖y‖) +
                  model.epsilon * (|x.im| * ‖y‖))
              ≤ model.epsilon * (((1 + model.epsilon) * |x.re| * ‖y‖) +
                  ((1 + model.epsilon) * |x.im| * ‖y‖)) +
                (model.epsilon * (|x.re| * ‖y‖) +
                  model.epsilon * (|x.im| * ‖y‖)) := by gcongr
            _ = (2 * model.epsilon + model.epsilon ^ 2) *
                (|x.re| + |x.im|) * ‖y‖ := by ring
    _ ≤ (3 * model.epsilon + 2 * model.epsilon ^ 2) * ‖x‖ * ‖y‖ := by
          have hc : 0 ≤ 2 * model.epsilon + model.epsilon ^ 2 := by positivity
          calc
            (2 * model.epsilon + model.epsilon ^ 2) *
                (|x.re| + |x.im|) * ‖y‖
              ≤ (2 * model.epsilon + model.epsilon ^ 2) *
                  ((3 / 2 : ℝ) * ‖x‖) * ‖y‖ := by
                    exact mul_le_mul_of_nonneg_right
                      (mul_le_mul_of_nonneg_left
                        (p09_abs_re_add_abs_im_le_three_halves_norm x) hc)
                      (norm_nonneg y)
            _ ≤ (3 * model.epsilon + 2 * model.epsilon ^ 2) * ‖x‖ * ‖y‖ := by
              have hcoef : (2 * model.epsilon + model.epsilon ^ 2) *
                  (3 / 2 : ℝ) ≤ 3 * model.epsilon + 2 * model.epsilon ^ 2 := by
                nlinarith [sq_nonneg model.epsilon]
              have hxmul := mul_le_mul_of_nonneg_right hcoef (norm_nonneg x)
              have hymul := mul_le_mul_of_nonneg_right hxmul (norm_nonneg y)
              simpa [mul_assoc] using hymul

private lemma p09_exactRoot_eq_stdAddChar {q : ℕ} [NeZero q]
    (j : ZMod q) :
    ({ re := Real.cos (p09RootAngle j),
       im := Real.sin (p09RootAngle j) } : ℂ) = ZMod.stdAddChar j := by
  have he : (⟨Real.cos (p09RootAngle j),
      Real.sin (p09RootAngle j)⟩ : ℂ) =
      Complex.exp ((p09RootAngle j : ℂ) * Complex.I) := by
    apply Complex.ext
    · rw [Complex.exp_re]
      simp
    · rw [Complex.exp_im]
      simp
  rw [he, p09StdAddChar_positive_exp]
  congr 1
  unfold p09RootAngle
  push_cast
  field_simp

private lemma p09_roundedRoot_error_le {q : ℕ} [NeZero q]
    (model : P09WilkinsonModel) (hγ : 0 ≤ model.gamma) (j : ZMod q) :
    ‖p09RoundedRoot model j - ZMod.stdAddChar j‖ ≤
      2 * model.gamma * model.epsilon := by
  obtain ⟨a, ha, hcos⟩ := model.cos_model (p09RootAngle j)
  obtain ⟨b, hb, hsin⟩ := model.sin_model (p09RootAngle j)
  let d : ℂ := ⟨a, b⟩
  have hd : ‖d‖ ≤ 2 := by
    calc
      ‖d‖ ≤ ‖(1 : ℂ)‖ + ‖(1 : ℂ)‖ := by
        apply (sq_le_sq₀ (norm_nonneg _) (by positivity)).mp
        rw [Complex.sq_norm, Complex.normSq_apply]
        simp [d]
        have ha2 : a ^ 2 ≤ 1 := (sq_le_one_iff_abs_le_one a).2 ha
        have hb2 : b ^ 2 ≤ 1 := (sq_le_one_iff_abs_le_one b).2 hb
        norm_num
        nlinarith
      _ = 2 := by norm_num
  have heq : p09RoundedRoot model j - ZMod.stdAddChar j =
      ((model.gamma * model.epsilon : ℝ) : ℂ) * d := by
    rw [← p09_exactRoot_eq_stdAddChar j]
    apply Complex.ext <;>
      simp [p09RoundedRoot, d, hcos, hsin] <;> ring
  rw [heq, norm_mul, Complex.norm_real, Real.norm_eq_abs,
    abs_of_nonneg (mul_nonneg hγ (le_of_lt model.epsilon_pos))]
  have h := mul_le_mul_of_nonneg_left hd
    (mul_nonneg hγ (le_of_lt model.epsilon_pos))
  nlinarith

private lemma p09_roundedRoot_norm_le {q : ℕ} [NeZero q]
    (model : P09WilkinsonModel) (hγ : 0 ≤ model.gamma) (j : ZMod q) :
    ‖p09RoundedRoot model j‖ ≤ 1 + 2 * model.gamma * model.epsilon := by
  calc
    ‖p09RoundedRoot model j‖ ≤
        ‖ZMod.stdAddChar j‖ + ‖p09RoundedRoot model j - ZMod.stdAddChar j‖ := by
      have h := norm_add_le (ZMod.stdAddChar j)
        (p09RoundedRoot model j - ZMod.stdAddChar j)
      simpa only [add_sub_cancel] using h
    _ ≤ 1 + 2 * model.gamma * model.epsilon := by
      have hchar : ‖ZMod.stdAddChar j‖ = 1 := by
        simp [ZMod.stdAddChar_apply]
      rw [hchar]
      gcongr
      exact p09_roundedRoot_error_le model hγ j

private lemma p09_roundedGeneric_term_error_le {q : ℕ} [NeZero q]
    (model : P09WilkinsonModel) (hγ : 0 ≤ model.gamma)
    (hu1 : model.epsilon ≤ 1) (j k : ZMod q) (x : ℂ) :
    ‖p09RoundedComplexMul model (p09RoundedRoot model (j * k)) x -
        ZMod.stdAddChar (j * k) * x‖ ≤
      ((3 + 2 * model.gamma) * model.epsilon +
        (2 + 10 * model.gamma) * model.epsilon ^ 2) * ‖x‖ := by
  have hu : 0 ≤ model.epsilon := le_of_lt model.epsilon_pos
  have hr0 := p09_roundedRoot_norm_le model hγ (j * k)
  have hre := p09_roundedRoot_error_le model hγ (j * k)
  calc
    ‖p09RoundedComplexMul model (p09RoundedRoot model (j * k)) x -
        ZMod.stdAddChar (j * k) * x‖
      ≤ ‖p09RoundedComplexMul model (p09RoundedRoot model (j * k)) x -
            p09RoundedRoot model (j * k) * x‖ +
          ‖(p09RoundedRoot model (j * k) - ZMod.stdAddChar (j * k)) * x‖ := by
        have h := norm_add_le
          (p09RoundedComplexMul model (p09RoundedRoot model (j * k)) x -
            p09RoundedRoot model (j * k) * x)
          ((p09RoundedRoot model (j * k) - ZMod.stdAddChar (j * k)) * x)
        convert h using 1 <;> ring
    _ ≤ (3 * model.epsilon + 2 * model.epsilon ^ 2) *
          (1 + 2 * model.gamma * model.epsilon) * ‖x‖ +
        (2 * model.gamma * model.epsilon) * ‖x‖ := by
      rw [norm_mul]
      have hc : 0 ≤ 3 * model.epsilon + 2 * model.epsilon ^ 2 := by positivity
      have hmul := p09_roundedComplexMul_error_le model
        (p09RoundedRoot model (j * k)) x
      have hfirst : (3 * model.epsilon + 2 * model.epsilon ^ 2) *
          ‖p09RoundedRoot model (j * k)‖ * ‖x‖ ≤
          (3 * model.epsilon + 2 * model.epsilon ^ 2) *
            (1 + 2 * model.gamma * model.epsilon) * ‖x‖ :=
        mul_le_mul_of_nonneg_right
          (mul_le_mul_of_nonneg_left hr0 hc) (norm_nonneg x)
      exact add_le_add (hmul.trans hfirst)
        (mul_le_mul_of_nonneg_right hre (norm_nonneg x))
    _ ≤ ((3 + 2 * model.gamma) * model.epsilon +
          (2 + 10 * model.gamma) * model.epsilon ^ 2) * ‖x‖ := by
      have hrem : 0 ≤ 4 * model.gamma * model.epsilon ^ 2 *
          (1 - model.epsilon) := by
        exact mul_nonneg
          (mul_nonneg (mul_nonneg (by norm_num) hγ) (sq_nonneg _))
          (sub_nonneg.mpr hu1)
      have hcoef :
          (3 * model.epsilon + 2 * model.epsilon ^ 2) *
              (1 + 2 * model.gamma * model.epsilon) +
            2 * model.gamma * model.epsilon ≤
          (3 + 2 * model.gamma) * model.epsilon +
            (2 + 10 * model.gamma) * model.epsilon ^ 2 := by
        nlinarith
      simpa [add_mul, mul_assoc] using
        (mul_le_mul_of_nonneg_right hcoef (norm_nonneg x))

private lemma p09_recursiveSum_error_le (model : P09WilkinsonModel) :
    ∀ (n : ℕ) (v : Fin n → ℝ),
      |recursiveSum model.flAdd n v - ∑ i, v i| ≤
        (n : ℝ) * model.epsilon * (1 + model.epsilon) ^ n *
          ∑ i, |v i| := by
  intro n
  induction n with
  | zero =>
      intro v
      simp [recursiveSum]
  | succ n ih =>
      intro v
      by_cases hn : n = 0
      · subst n
        simp [recursiveSum]
        exact mul_nonneg
          (mul_nonneg (le_of_lt model.epsilon_pos) (by linarith [model.epsilon_pos]))
          (abs_nonneg _)
      · let prev : ℝ := recursiveSum model.flAdd n (fun i ↦ v i.castSucc)
        let exactPrev : ℝ := ∑ i : Fin n, v i.castSucc
        let last : ℝ := v (Fin.last n)
        obtain ⟨a, b, ha, hb, hadd⟩ := model.add_model prev last
        have hprev : |prev - exactPrev| ≤
            (n : ℝ) * model.epsilon * (1 + model.epsilon) ^ n *
              ∑ i : Fin n, |v i.castSucc| := by
          simpa [prev, exactPrev] using ih (fun i ↦ v i.castSucc)
        have hprevnorm : |prev| ≤
            (1 + (n : ℝ) * model.epsilon * (1 + model.epsilon) ^ n) *
              ∑ i : Fin n, |v i.castSucc| := by
          calc
            |prev| = |exactPrev + (prev - exactPrev)| := by ring_nf
            _ ≤ |exactPrev| + |prev - exactPrev| := abs_add_le _ _
            _ ≤ (∑ i : Fin n, |v i.castSucc|) +
                ((n : ℝ) * model.epsilon * (1 + model.epsilon) ^ n *
                  ∑ i : Fin n, |v i.castSucc|) := by
              gcongr
              exact Finset.abs_sum_le_sum_abs _ _
            _ = (1 + (n : ℝ) * model.epsilon * (1 + model.epsilon) ^ n) *
                ∑ i : Fin n, |v i.castSucc| := by ring
        have hform : recursiveSum model.flAdd (n + 1) v - ∑ i, v i =
            (prev - exactPrev) + model.epsilon * (a * prev + b * last) := by
          rw [recursiveSum, dif_neg hn, Fin.sum_univ_castSucc]
          simp only [prev, exactPrev, last] at hadd ⊢
          rw [hadd]
          ring
        have hu : 0 ≤ model.epsilon := le_of_lt model.epsilon_pos
        have hbase : 1 ≤ 1 + model.epsilon := by linarith
        have hpow : 1 ≤ (1 + model.epsilon) ^ (n + 1) :=
          one_le_pow₀ hbase
        rw [hform]
        calc
          |(prev - exactPrev) + model.epsilon * (a * prev + b * last)|
              ≤ |prev - exactPrev| +
                model.epsilon * (|prev| + |last|) := by
            calc
              _ ≤ |prev - exactPrev| +
                  |model.epsilon * (a * prev + b * last)| := abs_add_le _ _
              _ ≤ |prev - exactPrev| +
                  model.epsilon * (|prev| + |last|) := by
                rw [abs_mul, abs_of_nonneg hu]
                gcongr
                calc
                  |a * prev + b * last| ≤ |a * prev| + |b * last| := abs_add_le _ _
                  _ = |a| * |prev| + |b| * |last| := by rw [abs_mul, abs_mul]
                  _ ≤ |prev| + |last| := by
                    exact add_le_add
                      (mul_le_of_le_one_left (abs_nonneg prev) ha)
                      (mul_le_of_le_one_left (abs_nonneg last) hb)
          _ ≤ (n : ℝ) * model.epsilon * (1 + model.epsilon) ^ n *
                (∑ i : Fin n, |v i.castSucc|) +
              model.epsilon *
                ((1 + (n : ℝ) * model.epsilon * (1 + model.epsilon) ^ n) *
                    (∑ i : Fin n, |v i.castSucc|) + |last|) := by
            gcongr
          _ ≤ ((n + 1 : ℕ) : ℝ) * model.epsilon *
                (1 + model.epsilon) ^ (n + 1) *
                  ((∑ i : Fin n, |v i.castSucc|) + |last|) := by
            have hn0 : (0 : ℝ) ≤ n := by positivity
            have hsum0 : 0 ≤ ∑ i : Fin n, |v i.castSucc| := by positivity
            have hlast0 : 0 ≤ |last| := abs_nonneg _
            let P : ℝ := (1 + model.epsilon) ^ n
            let S : ℝ := ∑ i : Fin n, |v i.castSucc|
            let L : ℝ := |last|
            have hpow' : 1 ≤ (1 + model.epsilon) * P := by
              simpa [P, pow_succ, mul_comm] using hpow
            have hcast : (1 : ℝ) ≤ (n + 1 : ℕ) := by exact_mod_cast Nat.succ_le_succ n.zero_le
            have hcoefS : (n : ℝ) * (1 + model.epsilon) * P + 1 ≤
                ((n + 1 : ℕ) : ℝ) * (1 + model.epsilon) * P := by
              rw [Nat.cast_add, Nat.cast_one]
              nlinarith
            have hcoefL : 1 ≤ ((n + 1 : ℕ) : ℝ) *
                (1 + model.epsilon) * P := by
              calc
                1 ≤ (1 + model.epsilon) * P := hpow'
                _ ≤ ((n + 1 : ℕ) : ℝ) * ((1 + model.epsilon) * P) :=
                  (le_mul_of_one_le_left (by positivity) hcast)
                _ = _ := by ring
            change (n : ℝ) * model.epsilon * P * S +
                model.epsilon * ((1 + (n : ℝ) * model.epsilon * P) * S + L) ≤ _
            rw [show (1 + model.epsilon) ^ (n + 1) =
                (1 + model.epsilon) * P by simp [P, pow_succ, mul_comm]]
            calc
              (n : ℝ) * model.epsilon * P * S +
                    model.epsilon * ((1 + (n : ℝ) * model.epsilon * P) * S + L)
                  = model.epsilon *
                      ((((n : ℝ) * (1 + model.epsilon) * P + 1) * S) + L) := by ring
              _ ≤ model.epsilon *
                    ((((n + 1 : ℕ) : ℝ) * (1 + model.epsilon) * P * S) +
                      (((n + 1 : ℕ) : ℝ) * (1 + model.epsilon) * P * L)) := by
                apply mul_le_mul_of_nonneg_left _ hu
                have hs := mul_le_mul_of_nonneg_right hcoefS hsum0
                have hl := mul_le_mul_of_nonneg_right hcoefL hlast0
                simpa [S, L] using add_le_add hs hl
              _ = ((n + 1 : ℕ) : ℝ) * model.epsilon *
                    ((1 + model.epsilon) * P) * (S + L) := by ring
          _ = ((n + 1 : ℕ) : ℝ) * model.epsilon *
                (1 + model.epsilon) ^ (n + 1) * ∑ i, |v i| := by
            rw [Fin.sum_univ_castSucc]

private lemma p09_roundedComplexSum_error_le {q : ℕ} [NeZero q]
    (model : P09WilkinsonModel) (term : ZMod q → ℂ) :
    ‖p09RoundedComplexSum model term - ∑ j, term j‖ ≤
      (q : ℝ) * model.epsilon * (1 + model.epsilon) ^ q *
        ∑ j, ‖term j‖ := by
  let index : Fin q ≃ ZMod q := (ZMod.finEquiv q).toEquiv
  let vr : Fin q → ℝ := fun i ↦ (term (index i)).re
  let vi : Fin q → ℝ := fun i ↦ (term (index i)).im
  let er : ℝ := recursiveSum model.flAdd q vr - ∑ i, vr i
  let ei : ℝ := recursiveSum model.flAdd q vi - ∑ i, vi i
  let c : ℝ := (q : ℝ) * model.epsilon * (1 + model.epsilon) ^ q
  have hc : 0 ≤ c := by
    dsimp [c]
    exact mul_nonneg
      (mul_nonneg (by positivity) (le_of_lt model.epsilon_pos))
      (pow_nonneg (by linarith [model.epsilon_pos]) _)
  have her : |er| ≤ c * ∑ i, |vr i| := by
    simpa [er, c] using p09_recursiveSum_error_le model q vr
  have hei : |ei| ≤ c * ∑ i, |vi i| := by
    simpa [ei, c] using p09_recursiveSum_error_le model q vi
  have heq : p09RoundedComplexSum model term - ∑ j, term j = ⟨er, ei⟩ := by
    apply Complex.ext
    · simp only [p09RoundedComplexSum, index, vr, er,
        Complex.sub_re]
      rw [← Equiv.sum_comp index]
      congr 1
      simp
      apply Finset.sum_congr rfl
      intro i hi
      rfl
    · simp only [p09RoundedComplexSum, index, vi, ei,
        Complex.sub_im]
      rw [← Equiv.sum_comp index]
      congr 1
      simp
      apply Finset.sum_congr rfl
      intro i hi
      rfl
  rw [heq]
  have hsq : ‖(⟨er, ei⟩ : ℂ)‖ ≤
      c * ‖(⟨∑ i, |vr i|, ∑ i, |vi i|⟩ : ℂ)‖ := by
    apply (sq_le_sq₀ (norm_nonneg _) (mul_nonneg hc (norm_nonneg _))).mp
    rw [mul_pow, Complex.sq_norm, Complex.sq_norm, Complex.normSq_apply,
      Complex.normSq_apply]
    have her2 := (sq_le_sq₀ (abs_nonneg er)
      (mul_nonneg hc (by positivity))).2 her
    have hei2 := (sq_le_sq₀ (abs_nonneg ei)
      (mul_nonneg hc (by positivity))).2 hei
    rw [sq_abs er] at her2
    rw [sq_abs ei] at hei2
    ring_nf at her2 hei2 ⊢
    nlinarith
  calc
    ‖(⟨er, ei⟩ : ℂ)‖
      ≤ c * ‖(⟨∑ i, |vr i|, ∑ i, |vi i|⟩ : ℂ)‖ := hsq
    _ ≤ c * ∑ i : Fin q, ‖term (index i)‖ := by
      apply mul_le_mul_of_nonneg_left _ hc
      have hsum := norm_sum_le (Finset.univ : Finset (Fin q))
        (fun i ↦ (⟨|vr i|, |vi i|⟩ : ℂ))
      have heqsum : (∑ i : Fin q, (⟨|vr i|, |vi i|⟩ : ℂ)) =
          (⟨∑ i, |vr i|, ∑ i, |vi i|⟩ : ℂ) := by
        apply Complex.ext <;> simp
      rw [heqsum] at hsum
      have habs : ∀ z : ℂ, ‖(⟨|z.re|, |z.im|⟩ : ℂ)‖ = ‖z‖ := by
        intro z
        apply (sq_eq_sq₀ (norm_nonneg _) (norm_nonneg _)).mp
        rw [Complex.sq_norm, Complex.sq_norm, Complex.normSq_apply,
          Complex.normSq_apply]
        simp only [pow_two] at *
        simp
      simpa only [vr, vi, habs] using hsum
    _ = (q : ℝ) * model.epsilon * (1 + model.epsilon) ^ q *
          ∑ j, ‖term j‖ := by
      unfold c
      rw [Equiv.sum_comp index (fun j ↦ ‖term j‖)]

private lemma p09_one_add_pow_le_linear (u : ℝ) (hu : 0 ≤ u) (hu1 : u ≤ 1) :
    ∀ n : ℕ, (1 + u) ^ n ≤ 1 + (3 : ℝ) ^ n * u := by
  intro n
  induction n with
  | zero => simpa using hu
  | succ n ih =>
      have hbase : 0 ≤ 1 + u := by linarith
      have hthree : (1 : ℝ) ≤ 3 ^ n := one_le_pow₀ (by norm_num)
      rw [pow_succ, pow_succ]
      calc
        (1 + u) ^ n * (1 + u) ≤ (1 + 3 ^ n * u) * (1 + u) := by
          gcongr
        _ ≤ 1 + (3 ^ n * 3) * u := by
          have huu : u ^ 2 ≤ u := by nlinarith
          have h3 : 0 ≤ (3 : ℝ) ^ n := by positivity
          nlinarith [mul_le_mul_of_nonneg_left huu h3]
        _ = 1 + 3 ^ n * 3 * u := rfl

private lemma p09_generic_block_error_pointwise {q : ℕ} [NeZero q]
    (model : P09WilkinsonModel) (hγ : 0 ≤ model.gamma)
    (hu1 : model.epsilon ≤ 1) (x : ZMod q → ℂ) (k : ZMod q) :
    ‖p09RoundedGenericRadixBlock model x k -
        ∑ j : ZMod q, ZMod.stdAddChar (j * k) * x j‖ ≤
      (((q : ℝ) + (3 + 2 * model.gamma)) * model.epsilon +
        ((q : ℝ) * ((1 + (3 : ℝ) ^ q) *
          (1 + ((3 + 2 * model.gamma) + (2 + 10 * model.gamma)))) +
          (2 + 10 * model.gamma)) * model.epsilon ^ 2) *
        ∑ j, ‖x j‖ := by
  let u := model.epsilon
  let B : ℝ := 3 + 2 * model.gamma
  let C : ℝ := 2 + 10 * model.gamma
  let M : ℝ := (1 + (3 : ℝ) ^ q) * (1 + (B + C))
  let roundedTerm : ZMod q → ℂ := fun j ↦
    p09RoundedComplexMul model (p09RoundedRoot model (j * k)) (x j)
  let exactTerm : ZMod q → ℂ := fun j ↦ ZMod.stdAddChar (j * k) * x j
  have hu : 0 ≤ u := le_of_lt model.epsilon_pos
  have hB : 0 ≤ B := by dsimp [B]; positivity
  have hC : 0 ≤ C := by dsimp [C]; positivity
  have hM : 0 ≤ M := by dsimp [M]; positivity
  have hterm (j : ZMod q) : ‖roundedTerm j - exactTerm j‖ ≤
      (B * u + C * u ^ 2) * ‖x j‖ := by
    simpa [roundedTerm, exactTerm, B, C, u] using
      p09_roundedGeneric_term_error_le model hγ hu1 j k (x j)
  have htermSum : ∑ j, ‖roundedTerm j - exactTerm j‖ ≤
      (B * u + C * u ^ 2) * ∑ j, ‖x j‖ := by
    calc
      ∑ j, ‖roundedTerm j - exactTerm j‖
          ≤ ∑ j, (B * u + C * u ^ 2) * ‖x j‖ :=
        Finset.sum_le_sum fun j _ ↦ hterm j
      _ = (B * u + C * u ^ 2) * ∑ j, ‖x j‖ := by
        rw [Finset.mul_sum]
  have happPoint (j : ZMod q) : ‖roundedTerm j‖ ≤
      (1 + B * u + C * u ^ 2) * ‖x j‖ := by
    calc
      ‖roundedTerm j‖ ≤ ‖exactTerm j‖ + ‖roundedTerm j - exactTerm j‖ := by
        have h := norm_add_le (exactTerm j) (roundedTerm j - exactTerm j)
        simpa only [add_sub_cancel] using h
      _ ≤ ‖x j‖ + (B * u + C * u ^ 2) * ‖x j‖ := by
        gcongr
        · simp [exactTerm]
        · exact hterm j
      _ = (1 + B * u + C * u ^ 2) * ‖x j‖ := by ring
  have happSum : ∑ j, ‖roundedTerm j‖ ≤
      (1 + B * u + C * u ^ 2) * ∑ j, ‖x j‖ := by
    calc
      ∑ j, ‖roundedTerm j‖ ≤
          ∑ j, (1 + B * u + C * u ^ 2) * ‖x j‖ :=
        Finset.sum_le_sum fun j _ ↦ happPoint j
      _ = _ := by rw [Finset.mul_sum]
  have hpow := p09_one_add_pow_le_linear u hu hu1 q
  have hfactor : (1 + u) ^ q * (1 + B * u + C * u ^ 2) ≤
      1 + M * u := by
    have hu2 : u ^ 2 ≤ u := by nlinarith
    have happfac : 1 + B * u + C * u ^ 2 ≤ 1 + (B + C) * u := by
      nlinarith [mul_le_mul_of_nonneg_left hu2 hC]
    have hleft0 : 0 ≤ (1 + u) ^ q := by positivity
    have hright0 : 0 ≤ 1 + (B + C) * u := by positivity
    calc
      (1 + u) ^ q * (1 + B * u + C * u ^ 2)
          ≤ (1 + u) ^ q * (1 + (B + C) * u) := by gcongr
      _ ≤ (1 + (3 : ℝ) ^ q * u) * (1 + (B + C) * u) := by gcongr
      _ ≤ 1 + M * u := by
        have h3 : 0 ≤ (3 : ℝ) ^ q := by positivity
        dsimp [M]
        nlinarith [mul_le_mul_of_nonneg_left hu2
          (mul_nonneg h3 (add_nonneg hB hC))]
  have hsumround := p09_roundedComplexSum_error_le model roundedTerm
  change ‖p09RoundedComplexSum model roundedTerm - ∑ j, exactTerm j‖ ≤ _
  calc
    ‖p09RoundedComplexSum model roundedTerm - ∑ j, exactTerm j‖
      ≤ ‖p09RoundedComplexSum model roundedTerm - ∑ j, roundedTerm j‖ +
          ∑ j, ‖roundedTerm j - exactTerm j‖ := by
        have htri := norm_add_le
          (p09RoundedComplexSum model roundedTerm - ∑ j, roundedTerm j)
          (∑ j, (roundedTerm j - exactTerm j))
        have hnormsum := norm_sum_le (Finset.univ : Finset (ZMod q))
          (fun j ↦ roundedTerm j - exactTerm j)
        calc
          _ = ‖(p09RoundedComplexSum model roundedTerm - ∑ j, roundedTerm j) +
                ∑ j, (roundedTerm j - exactTerm j)‖ := by
              congr 1
              simp only [Finset.sum_sub_distrib]
              abel
          _ ≤ ‖p09RoundedComplexSum model roundedTerm - ∑ j, roundedTerm j‖ +
                ‖∑ j, (roundedTerm j - exactTerm j)‖ := htri
          _ ≤ _ := add_le_add le_rfl hnormsum
    _ ≤ ((q : ℝ) * u * (1 + u) ^ q *
            (1 + B * u + C * u ^ 2) + (B * u + C * u ^ 2)) *
          ∑ j, ‖x j‖ := by
      calc
        _ ≤ ((q : ℝ) * u * (1 + u) ^ q) *
              ((1 + B * u + C * u ^ 2) * ∑ j, ‖x j‖) +
            (B * u + C * u ^ 2) * ∑ j, ‖x j‖ := by
          have hcoef0 : 0 ≤ (q : ℝ) * u * (1 + u) ^ q := by positivity
          have hsr : ‖p09RoundedComplexSum model roundedTerm -
                ∑ j, roundedTerm j‖ ≤
              ((q : ℝ) * u * (1 + u) ^ q) *
                ((1 + B * u + C * u ^ 2) * ∑ j, ‖x j‖) := by
            have h0 := hsumround.trans
              (mul_le_mul_of_nonneg_left happSum hcoef0)
            simpa [u, mul_assoc] using h0
          exact add_le_add hsr htermSum
        _ = _ := by ring
    _ ≤ (((q : ℝ) + B) * u + ((q : ℝ) * M + C) * u ^ 2) *
          ∑ j, ‖x j‖ := by
      have hq : (0 : ℝ) ≤ q := by positivity
      have hsumx : 0 ≤ ∑ j, ‖x j‖ := by positivity
      apply mul_le_mul_of_nonneg_right _ hsumx
      have hscaled := mul_le_mul_of_nonneg_left hfactor (mul_nonneg hq hu)
      nlinarith
    _ = _ := by rfl

private lemma p09_generic_block_error_norm2 {q : ℕ} [NeZero q]
    (model : P09WilkinsonModel) (hγ : 0 ≤ model.gamma)
    (hu1 : model.epsilon ≤ 1) (x : ZMod q → ℂ) :
    p09ComplexNorm2 (fun k ↦ p09RoundedGenericRadixBlock model x k -
        ∑ j : ZMod q, ZMod.stdAddChar (j * k) * x j) ≤
      (q : ℝ) *
        (((q : ℝ) + (3 + 2 * model.gamma)) * model.epsilon +
          ((q : ℝ) * ((1 + (3 : ℝ) ^ q) *
            (1 + ((3 + 2 * model.gamma) + (2 + 10 * model.gamma)))) +
            (2 + 10 * model.gamma)) * model.epsilon ^ 2) *
        p09ComplexNorm2 x := by
  apply p09_complexNorm2_le_of_pointwise_l1
  · have hq : (0 : ℝ) ≤ q := by positivity
    have hu : 0 ≤ model.epsilon := le_of_lt model.epsilon_pos
    have hγ3 : 0 ≤ 3 + 2 * model.gamma := by positivity
    have hγ2 : 0 ≤ 2 + 10 * model.gamma := by positivity
    positivity
  · exact p09_generic_block_error_pointwise model hγ hu1 x

private lemma p09_stdAddChar_four_zero :
    ZMod.stdAddChar (N := 4) (0 : ZMod 4) = 1 :=
  (ZMod.stdAddChar (N := 4)).map_zero_eq_one

private lemma p09_stdAddChar_four_one :
    ZMod.stdAddChar (N := 4) (1 : ZMod 4) = Complex.I := by
  rw [show (1 : ZMod 4) = ((1 : ℤ) : ZMod 4) by norm_num,
    ZMod.stdAddChar_coe]
  convert Complex.exp_pi_div_two_mul_I using 2 <;> norm_num <;> ring

private lemma p09_stdAddChar_four_two :
    ZMod.stdAddChar (N := 4) (2 : ZMod 4) = -1 := by
  rw [show (2 : ZMod 4) = ((2 : ℤ) : ZMod 4) by norm_num,
    ZMod.stdAddChar_coe]
  convert Complex.exp_pi_mul_I using 2 <;> norm_num <;> ring

private lemma p09_stdAddChar_four_three :
    ZMod.stdAddChar (N := 4) (3 : ZMod 4) = -Complex.I := by
  rw [show (3 : ZMod 4) = (2 : ZMod 4) + 1 by decide,
    AddChar.map_add_eq_mul, p09_stdAddChar_four_two,
    p09_stdAddChar_four_one]
  ring

private lemma p09_radixFour_coefficient_eq (j : ZMod 4) (x : ℂ) :
    p09RadixFourCoefficientApply j x = ZMod.stdAddChar j * x := by
  have hj : j = 0 ∨ j = 1 ∨ j = 2 ∨ j = 3 := by
    fin_cases j
    · exact Or.inl rfl
    · exact Or.inr (Or.inl rfl)
    · exact Or.inr (Or.inr (Or.inl rfl))
    · exact Or.inr (Or.inr (Or.inr rfl))
  rcases hj with rfl | rfl | rfl | rfl
  · simp [p09RadixFourCoefficientApply, p09_stdAddChar_four_zero]
  · rw [p09_stdAddChar_four_one]
    simp only [p09RadixFourCoefficientApply,
      if_neg (by decide : (1 : ZMod 4) ≠ 0)]
    apply Complex.ext <;> norm_num
  · rw [p09_stdAddChar_four_two]
    simp only [p09RadixFourCoefficientApply,
      if_neg (by decide : (2 : ZMod 4) ≠ 0),
      if_neg (by decide : (2 : ZMod 4) ≠ 1)]
    simp
  · rw [p09_stdAddChar_four_three]
    simp only [p09RadixFourCoefficientApply,
      if_neg (by decide : (3 : ZMod 4) ≠ 0),
      if_neg (by decide : (3 : ZMod 4) ≠ 1),
      if_neg (by decide : (3 : ZMod 4) ≠ 2)]
    apply Complex.ext <;> norm_num

private lemma p09_radixFour_coefficient_norm (j : ZMod 4) (x : ℂ) :
    ‖p09RadixFourCoefficientApply j x‖ = ‖x‖ := by
  rw [p09_radixFour_coefficient_eq, norm_mul]
  have hchar : ‖ZMod.stdAddChar j‖ = 1 := by
    simp [ZMod.stdAddChar_apply]
  rw [hchar, one_mul]

private lemma p09_sum_zmod_four {M : Type*} [AddCommMonoid M]
    (f : ZMod 4 → M) : ∑ j : ZMod 4, f j = f 0 + f 1 + f 2 + f 3 := by
  rw [← Equiv.sum_comp (ZMod.finEquiv 4).toEquiv, Fin.sum_univ_four]
  rfl

private lemma p09_radixFour_exact_block (x : ZMod 4 → ℂ) (k : ZMod 4) :
    (∑ j : ZMod 4, ZMod.stdAddChar (j * k) * x j) =
      p09RadixFourCoefficientApply ((0 : ZMod 4) * k) (x 0) +
      p09RadixFourCoefficientApply ((1 : ZMod 4) * k) (x 1) +
      p09RadixFourCoefficientApply ((2 : ZMod 4) * k) (x 2) +
      p09RadixFourCoefficientApply ((3 : ZMod 4) * k) (x 3) := by
  rw [p09_sum_zmod_four]
  simp only [p09_radixFour_coefficient_eq]

private lemma p09_radixFour_rounded_block (model : P09WilkinsonModel)
    (x : ZMod 4 → ℂ) (k : ZMod 4) :
    p09RoundedRadixFourBlock model x k =
      p09RoundedComplexAdd model
        (p09RoundedComplexAdd model
          (p09RadixFourCoefficientApply ((0 : ZMod 4) * k) (x 0))
          (p09RadixFourCoefficientApply ((1 : ZMod 4) * k) (x 1)))
        (p09RoundedComplexAdd model
          (p09RadixFourCoefficientApply ((2 : ZMod 4) * k) (x 2))
          (p09RadixFourCoefficientApply ((3 : ZMod 4) * k) (x 3))) := by
  simp [p09RoundedRadixFourBlock]
  rfl

private lemma p09_radixFour_block_error_pointwise
    (model : P09WilkinsonModel) (x : ZMod 4 → ℂ) (k : ZMod 4) :
    ‖p09RoundedRadixFourBlock model x k -
        ∑ j : ZMod 4, ZMod.stdAddChar (j * k) * x j‖ ≤
      (2 * model.epsilon + model.epsilon ^ 2) * ∑ j, ‖x j‖ := by
  let t0 := p09RadixFourCoefficientApply ((0 : ZMod 4) * k) (x 0)
  let t1 := p09RadixFourCoefficientApply ((1 : ZMod 4) * k) (x 1)
  let t2 := p09RadixFourCoefficientApply ((2 : ZMod 4) * k) (x 2)
  let t3 := p09RadixFourCoefficientApply ((3 : ZMod 4) * k) (x 3)
  let a := p09RoundedComplexAdd model t0 t1
  let b := p09RoundedComplexAdd model t2 t3
  let r := p09RoundedComplexAdd model a b
  let L := ‖t0‖ + ‖t1‖ + ‖t2‖ + ‖t3‖
  have hu : 0 ≤ model.epsilon := le_of_lt model.epsilon_pos
  have ha : ‖a - (t0 + t1)‖ ≤ model.epsilon * (‖t0‖ + ‖t1‖) :=
    p09_roundedComplexAdd_error_le model t0 t1
  have hb : ‖b - (t2 + t3)‖ ≤ model.epsilon * (‖t2‖ + ‖t3‖) :=
    p09_roundedComplexAdd_error_le model t2 t3
  have han : ‖a‖ ≤ (1 + model.epsilon) * (‖t0‖ + ‖t1‖) := by
    calc
      ‖a‖ ≤ ‖t0 + t1‖ + ‖a - (t0 + t1)‖ := by
        have h := norm_add_le (t0 + t1) (a - (t0 + t1))
        simpa only [add_sub_cancel] using h
      _ ≤ (‖t0‖ + ‖t1‖) + model.epsilon * (‖t0‖ + ‖t1‖) := by
        gcongr
        exact norm_add_le _ _
      _ = _ := by ring
  have hbn : ‖b‖ ≤ (1 + model.epsilon) * (‖t2‖ + ‖t3‖) := by
    calc
      ‖b‖ ≤ ‖t2 + t3‖ + ‖b - (t2 + t3)‖ := by
        have h := norm_add_le (t2 + t3) (b - (t2 + t3))
        simpa only [add_sub_cancel] using h
      _ ≤ (‖t2‖ + ‖t3‖) + model.epsilon * (‖t2‖ + ‖t3‖) := by
        gcongr
        exact norm_add_le _ _
      _ = _ := by ring
  have hr : ‖r - (a + b)‖ ≤ model.epsilon * (‖a‖ + ‖b‖) :=
    p09_roundedComplexAdd_error_le model a b
  rw [p09_radixFour_rounded_block, p09_radixFour_exact_block]
  change ‖r - (t0 + t1 + t2 + t3)‖ ≤ _
  calc
    ‖r - (t0 + t1 + t2 + t3)‖
      ≤ ‖r - (a + b)‖ + (‖a - (t0 + t1)‖ + ‖b - (t2 + t3)‖) := by
        have h := norm_add_le (r - (a + b))
          ((a - (t0 + t1)) + (b - (t2 + t3)))
        calc
          _ = ‖(r - (a + b)) + ((a - (t0 + t1)) + (b - (t2 + t3)))‖ := by
            congr 1
            abel
          _ ≤ _ := h.trans (add_le_add le_rfl (norm_add_le _ _))
    _ ≤ model.epsilon * ((1 + model.epsilon) * L) +
          model.epsilon * L := by
      have habn := add_le_add han hbn
      have haberr := add_le_add ha hb
      calc
        _ ≤ model.epsilon * (‖a‖ + ‖b‖) +
            (model.epsilon * (‖t0‖ + ‖t1‖) +
              model.epsilon * (‖t2‖ + ‖t3‖)) := by gcongr
        _ ≤ model.epsilon * ((1 + model.epsilon) * L) +
            model.epsilon * L := by
          have hfirst : model.epsilon * (‖a‖ + ‖b‖) ≤
              model.epsilon * ((1 + model.epsilon) * L) := by
            apply mul_le_mul_of_nonneg_left _ hu
            dsimp [L]
            convert habn using 1 <;> ring
          have hsecond : model.epsilon * (‖t0‖ + ‖t1‖) +
                model.epsilon * (‖t2‖ + ‖t3‖) = model.epsilon * L := by
            dsimp [L]
            ring
          rw [hsecond]
          exact add_le_add hfirst le_rfl
    _ = (2 * model.epsilon + model.epsilon ^ 2) * L := by ring
    _ = (2 * model.epsilon + model.epsilon ^ 2) * ∑ j, ‖x j‖ := by
      simp [L, t0, t1, t2, t3, p09_sum_zmod_four,
        p09_radixFour_coefficient_norm]

private lemma p09_radixFour_block_error_norm2
    (model : P09WilkinsonModel) (x : ZMod 4 → ℂ) :
    p09ComplexNorm2 (fun k ↦ p09RoundedRadixFourBlock model x k -
        ∑ j : ZMod 4, ZMod.stdAddChar (j * k) * x j) ≤
      4 * (2 * model.epsilon + model.epsilon ^ 2) * p09ComplexNorm2 x := by
  apply p09_complexNorm2_le_of_pointwise_l1
  · have hu : 0 ≤ model.epsilon := le_of_lt model.epsilon_pos
    positivity
  · exact p09_radixFour_block_error_pointwise model x

private lemma p09_complexNorm2_equiv {n₁ n₂ : ℕ} [NeZero n₁] [NeZero n₂]
    (e : ZMod n₁ ≃ ZMod n₂) (x : ZMod n₂ → ℂ) :
    p09ComplexNorm2 (fun i ↦ x (e i)) = p09ComplexNorm2 x := by
  apply (sq_eq_sq₀ (p09_complexNorm2_nonneg _) (p09_complexNorm2_nonneg _)).mp
  rw [p09_complexNorm2_sq, p09_complexNorm2_sq]
  exact Equiv.sum_comp e (fun i ↦ ‖x i‖ ^ 2)

private lemma p09_aggregate_block_norm2 {b q n : ℕ} [NeZero q] [NeZero n]
    (reindex : Fin b × ZMod q ≃ ZMod n)
    (err inp : ZMod n → ℂ) (c : ℝ) (hc : 0 ≤ c)
    (hblock : ∀ block : Fin b,
      p09ComplexNorm2 (fun k ↦ err (reindex (block, k))) ≤
        c * p09ComplexNorm2 (fun j ↦ inp (reindex (block, j)))) :
    p09ComplexNorm2 err ≤ c * p09ComplexNorm2 inp := by
  apply (sq_le_sq₀ (p09_complexNorm2_nonneg err)
    (mul_nonneg hc (p09_complexNorm2_nonneg inp))).mp
  rw [p09_complexNorm2_sq, mul_pow, p09_complexNorm2_sq]
  rw [← Equiv.sum_comp reindex, Fintype.sum_prod_type,
    ← Equiv.sum_comp reindex, Fintype.sum_prod_type]
  calc
    (∑ block : Fin b, ∑ k : ZMod q, ‖err (reindex (block, k))‖ ^ 2)
      ≤ ∑ block : Fin b,
          c ^ 2 * ∑ j : ZMod q, ‖inp (reindex (block, j))‖ ^ 2 := by
        apply Finset.sum_le_sum
        intro block _
        have hb := (sq_le_sq₀
          (p09_complexNorm2_nonneg (fun k ↦ err (reindex (block, k))))
          (mul_nonneg hc (p09_complexNorm2_nonneg
            (fun j ↦ inp (reindex (block, j)))))).2 (hblock block)
        rw [p09_complexNorm2_sq, mul_pow, p09_complexNorm2_sq] at hb
        exact hb
    _ = c ^ 2 * ∑ block : Fin b,
          ∑ j : ZMod q, ‖inp (reindex (block, j))‖ ^ 2 := by
        rw [Finset.mul_sum]

private noncomputable def p09BlockSecond (q : ℕ) (γ : ℝ) : ℝ :=
  if q = 2 then 4
  else if q = 4 then 2
  else
    (q : ℝ) *
      ((q : ℝ) * ((1 + (3 : ℝ) ^ q) *
        (1 + ((3 + 2 * γ) + (2 + 10 * γ)))) + (2 + 10 * γ))

private lemma p09_alpha_nonneg (q : ℕ) (γ : ℝ) (hq : 2 ≤ q) (hγ : 0 ≤ γ) :
    0 ≤ p09Alpha q γ := by
  unfold p09Alpha
  split_ifs
  · exact Real.sqrt_nonneg _
  · norm_num
  · positivity

private lemma p09_blockSecond_nonneg (q : ℕ) (γ : ℝ)
    (hq : 2 ≤ q) (hγ : 0 ≤ γ) : 0 ≤ p09BlockSecond q γ := by
  unfold p09BlockSecond
  split_ifs
  · norm_num
  · norm_num
  · positivity

private lemma p09_sqrt_nat_one_le (q : ℕ) (hq : 1 ≤ q) :
    (1 : ℝ) ≤ Real.sqrt q := by
  rw [Real.le_sqrt (by norm_num)]
  exact_mod_cast hq
  positivity

@[simp] private lemma p09_zmod_cast_roundtrip {q r : ℕ} (h : q = r)
    (k : ZMod r) :
    h ▸ (Equiv.cast (congrArg ZMod h.symm) k) = k := by
  subst q
  rfl

@[simp] private lemma p09_zmod_equivCast_eq_transport {q r : ℕ} (h : q = r)
    (k : ZMod r) :
    Equiv.cast (congrArg ZMod h.symm) k = h.symm ▸ k := by
  subst q
  rfl

@[simp] private lemma p09_stdAddChar_equivCast_mul {q r : ℕ}
    [NeZero q] [NeZero r] (h : q = r) (j k : ZMod r) :
    @ZMod.stdAddChar q _
        ((Equiv.cast (congrArg ZMod h.symm) j) *
          (Equiv.cast (congrArg ZMod h.symm) k)) =
      @ZMod.stdAddChar r _ (j * k) := by
  subst q
  rfl

private lemma p09_roundedMixedRadixBlock_error_norm2 {n : ℕ} [NeZero n]
    (model : P09WilkinsonModel) (hγ : 0 ≤ model.gamma)
    (hu1 : model.epsilon ≤ 1) (stage : P09MixedRadixStage n)
    (x : ZMod n → ℂ) :
    p09ComplexNorm2 (fun i ↦
        p09RoundedMixedRadixBlockApply model stage x i -
          p09MixedRadixBlockApply stage x i) ≤
      Real.sqrt stage.radix *
        (p09Alpha stage.radix model.gamma * model.epsilon +
          p09BlockSecond stage.radix model.gamma * model.epsilon ^ 2) *
        p09ComplexNorm2 x := by
  let permuted : ZMod n → ℂ := fun i ↦ x (stage.permutation i)
  let c : ℝ := Real.sqrt stage.radix *
    (p09Alpha stage.radix model.gamma * model.epsilon +
      p09BlockSecond stage.radix model.gamma * model.epsilon ^ 2)
  have hα : 0 ≤ p09Alpha stage.radix model.gamma :=
    p09_alpha_nonneg stage.radix model.gamma stage.radix_two_le hγ
  have hS : 0 ≤ p09BlockSecond stage.radix model.gamma :=
    p09_blockSecond_nonneg stage.radix model.gamma stage.radix_two_le hγ
  have hu : 0 ≤ model.epsilon := le_of_lt model.epsilon_pos
  have hc : 0 ≤ c := by dsimp [c]; positivity
  have hagg : p09ComplexNorm2 (fun i ↦
        p09RoundedMixedRadixBlockApply model stage x i -
          p09MixedRadixBlockApply stage x i) ≤
      c * p09ComplexNorm2 permuted := by
    by_cases h2 : stage.radix = 2
    · let cast2 : ZMod 2 ≃ ZMod stage.radix :=
        Equiv.cast (congrArg ZMod h2.symm)
      let reindex2 : Fin stage.blockCount × ZMod 2 ≃ ZMod n :=
        (Equiv.prodCongr (Equiv.refl _) cast2).trans stage.reindex
      have hsqrt : Real.sqrt (2 : ℝ) * Real.sqrt 2 = 2 := by
        exact Real.mul_self_sqrt (by norm_num)
      have hcle : 2 * model.epsilon ≤ c := by
        have hcform : c = Real.sqrt 2 *
            (Real.sqrt 2 * model.epsilon + 4 * model.epsilon ^ 2) := by
          simp [c, p09BlockSecond, p09Alpha, h2]
        rw [hcform]
        nlinarith [hsqrt, sq_nonneg model.epsilon,
          Real.sqrt_nonneg (2 : ℝ)]
      apply p09_aggregate_block_norm2 reindex2 _ _ c hc
      intro block
      have hb := p09_radixTwo_block_error_norm2 model
        (fun j : ZMod 2 ↦ permuted (reindex2 (block, j)))
      have hscale := mul_le_mul_of_nonneg_right hcle
        (p09_complexNorm2_nonneg
          (fun j : ZMod 2 ↦ permuted (reindex2 (block, j))))
      have herrEq : (fun k : ZMod 2 ↦
          p09RoundedMixedRadixBlockApply model stage x (reindex2 (block, k)) -
            p09MixedRadixBlockApply stage x (reindex2 (block, k))) =
          (fun k : ZMod 2 ↦
            p09RoundedRadixTwoBlock model
                (fun j ↦ permuted (reindex2 (block, j))) k -
              ∑ j : ZMod 2, ZMod.stdAddChar (j * k) *
                permuted (reindex2 (block, j))) := by
        funext k
        simp only [p09RoundedMixedRadixBlockApply,
          p09MixedRadixBlockApply]
        simp [reindex2, cast2, permuted, h2]
        rw [← Equiv.sum_comp cast2]
        apply congrArg₂ (fun a b : ℂ ↦ a - b)
        · congr 1
          funext j
          congr 3
          exact congrArg (fun z ↦ (block, z))
            (p09_zmod_equivCast_eq_transport h2 j).symm
          exact p09_zmod_cast_roundtrip h2 k
        · apply Finset.sum_congr rfl
          intro j hj
          simp [cast2]
          left
          exact p09_stdAddChar_equivCast_mul h2 j k
      rw [herrEq]
      exact hb.trans hscale
    · by_cases h4 : stage.radix = 4
      · let cast4 : ZMod 4 ≃ ZMod stage.radix :=
          Equiv.cast (congrArg ZMod h4.symm)
        let reindex4 : Fin stage.blockCount × ZMod 4 ≃ ZMod n :=
          (Equiv.prodCongr (Equiv.refl _) cast4).trans stage.reindex
        have hsqrt : Real.sqrt (4 : ℝ) = 2 := by norm_num
        have hcle : 4 * (2 * model.epsilon + model.epsilon ^ 2) ≤ c := by
          have hcform : c = 2 * (5 * model.epsilon +
              2 * model.epsilon ^ 2) := by
            simp [c, p09BlockSecond, p09Alpha, h2, h4, hsqrt]
          rw [hcform]
          nlinarith [sq_nonneg model.epsilon]
        apply p09_aggregate_block_norm2 reindex4 _ _ c hc
        intro block
        have hb := p09_radixFour_block_error_norm2 model
          (fun j : ZMod 4 ↦ permuted (reindex4 (block, j)))
        have hscale := mul_le_mul_of_nonneg_right hcle
          (p09_complexNorm2_nonneg
            (fun j : ZMod 4 ↦ permuted (reindex4 (block, j))))
        have herrEq : (fun k : ZMod 4 ↦
            p09RoundedMixedRadixBlockApply model stage x (reindex4 (block, k)) -
              p09MixedRadixBlockApply stage x (reindex4 (block, k))) =
            (fun k : ZMod 4 ↦
              p09RoundedRadixFourBlock model
                  (fun j ↦ permuted (reindex4 (block, j))) k -
                ∑ j : ZMod 4, ZMod.stdAddChar (j * k) *
                  permuted (reindex4 (block, j))) := by
          funext k
          simp only [p09RoundedMixedRadixBlockApply,
            p09MixedRadixBlockApply]
          simp [reindex4, cast4, permuted, h2, h4]
          rw [← Equiv.sum_comp cast4]
          apply congrArg₂ (fun a b : ℂ ↦ a - b)
          · congr 1
            funext j
            congr 3
            exact congrArg (fun z ↦ (block, z))
              (p09_zmod_equivCast_eq_transport h4 j).symm
            exact p09_zmod_cast_roundtrip h4 k
          · apply Finset.sum_congr rfl
            intro j hj
            simp [cast4]
            left
            exact p09_stdAddChar_equivCast_mul h4 j k
        rw [herrEq]
        exact hb.trans hscale
      · apply p09_aggregate_block_norm2 stage.reindex _ _ c hc
        intro block
        have hb := p09_generic_block_error_norm2 model hγ hu1
          (fun j : ZMod stage.radix ↦ permuted (stage.reindex (block, j)))
        let B : ℝ := 3 + 2 * model.gamma
        let D : ℝ :=
          (stage.radix : ℝ) * ((1 + (3 : ℝ) ^ stage.radix) *
            (1 + ((3 + 2 * model.gamma) + (2 + 10 * model.gamma)))) +
              (2 + 10 * model.gamma)
        have hq2 := stage.radix_two_le
        have hq3 : 3 ≤ stage.radix := by omega
        have hfirst : (stage.radix : ℝ) * ((stage.radix : ℝ) + B) ≤
            Real.sqrt stage.radix *
              p09Alpha stage.radix model.gamma := by
          have hsq : Real.sqrt (stage.radix : ℝ) ^ 2 = stage.radix :=
            Real.sq_sqrt (by positivity)
          have hq3r : (3 : ℝ) ≤ stage.radix := by exact_mod_cast hq3
          have hprod : 0 ≤ (stage.radix : ℝ) * ((stage.radix : ℝ) - 3) :=
            mul_nonneg (by positivity) (sub_nonneg.mpr hq3r)
          rw [show p09Alpha stage.radix model.gamma =
              2 * Real.sqrt stage.radix * ((stage.radix : ℝ) + model.gamma) by
            simp [p09Alpha, h2, h4]]
          dsimp [B]
          nlinarith
        have hsecond : (stage.radix : ℝ) * D ≤
            Real.sqrt stage.radix * p09BlockSecond stage.radix model.gamma := by
          have hs1 := p09_sqrt_nat_one_le stage.radix (by omega)
          have hD : 0 ≤ D := by dsimp [D]; positivity
          rw [show p09BlockSecond stage.radix model.gamma =
              (stage.radix : ℝ) * D by simp [p09BlockSecond, h2, h4, D]]
          simpa only [one_mul] using mul_le_mul_of_nonneg_right hs1
            (mul_nonneg (show (0 : ℝ) ≤ stage.radix by positivity) hD)
        have hcle : (stage.radix : ℝ) *
              (((stage.radix : ℝ) + B) * model.epsilon +
                D * model.epsilon ^ 2) ≤ c := by
          dsimp [c]
          have hf := mul_le_mul_of_nonneg_right hfirst hu
          have hs := mul_le_mul_of_nonneg_right hsecond (sq_nonneg model.epsilon)
          nlinarith
        have hscale := mul_le_mul_of_nonneg_right hcle
          (p09_complexNorm2_nonneg
            (fun j : ZMod stage.radix ↦ permuted (stage.reindex (block, j))))
        simpa [p09RoundedMixedRadixBlockApply, p09MixedRadixBlockApply,
          permuted, h2, h4, B, D] using hb.trans hscale
  have hperm : p09ComplexNorm2 permuted = p09ComplexNorm2 x :=
    p09_complexNorm2_equiv stage.permutation x
  simpa [c, hperm] using hagg

private lemma p09_complexNorm2_le_pointwise_scale {n : ℕ} [NeZero n]
    (e x : ZMod n → ℂ) (c : ℝ) (hc : 0 ≤ c)
    (h : ∀ i, ‖e i‖ ≤ c * ‖x i‖) :
    p09ComplexNorm2 e ≤ c * p09ComplexNorm2 x := by
  apply (sq_le_sq₀ (p09_complexNorm2_nonneg e)
    (mul_nonneg hc (p09_complexNorm2_nonneg x))).mp
  rw [p09_complexNorm2_sq, mul_pow, p09_complexNorm2_sq]
  calc
    (∑ i, ‖e i‖ ^ 2) ≤ ∑ i, (c * ‖x i‖) ^ 2 := by
      apply Finset.sum_le_sum
      intro i hi
      exact (sq_le_sq₀ (norm_nonneg (e i))
        (mul_nonneg hc (norm_nonneg (x i)))).2 (h i)
    _ = c ^ 2 * ∑ i, ‖x i‖ ^ 2 := by
      simp_rw [mul_pow]
      rw [Finset.mul_sum]

private lemma p09_mixedRadixTwiddle_norm2 {n : ℕ} [NeZero n]
    (stage : P09MixedRadixStage n) (x : ZMod n → ℂ) :
    p09ComplexNorm2 (p09MixedRadixTwiddleApply stage x) =
      p09ComplexNorm2 x := by
  apply (sq_eq_sq₀ (p09_complexNorm2_nonneg _)
    (p09_complexNorm2_nonneg _)).mp
  rw [p09_complexNorm2_sq, p09_complexNorm2_sq]
  apply Finset.sum_congr rfl
  intro i hi
  simp only [p09MixedRadixTwiddleApply]
  split
  · rw [norm_mul]
    have hchar : ‖ZMod.stdAddChar (stage.twiddleExponent i)‖ = 1 := by
      simp [ZMod.stdAddChar_apply]
    rw [hchar, one_mul]
  · rfl

private lemma p09_mixedRadixTwiddle_sub_norm2 {n : ℕ} [NeZero n]
    (stage : P09MixedRadixStage n) (x y : ZMod n → ℂ) :
    p09ComplexNorm2 (fun i ↦ p09MixedRadixTwiddleApply stage x i -
        p09MixedRadixTwiddleApply stage y i) =
      p09ComplexNorm2 (fun i ↦ x i - y i) := by
  apply (sq_eq_sq₀ (p09_complexNorm2_nonneg _)
    (p09_complexNorm2_nonneg _)).mp
  rw [p09_complexNorm2_sq, p09_complexNorm2_sq]
  apply Finset.sum_congr rfl
  intro i hi
  simp only [p09MixedRadixTwiddleApply]
  split
  · rw [← mul_sub, norm_mul]
    have hchar : ‖ZMod.stdAddChar (stage.twiddleExponent i)‖ = 1 := by
      simp [ZMod.stdAddChar_apply]
    rw [hchar, one_mul]
  · rfl

private lemma p09_roundedTwiddle_error_norm2 {n : ℕ} [NeZero n]
    (model : P09WilkinsonModel) (hγ : 0 ≤ model.gamma)
    (hu1 : model.epsilon ≤ 1) (stage : P09MixedRadixStage n)
    (x : ZMod n → ℂ) :
    p09ComplexNorm2 (fun i ↦
        p09RoundedMixedRadixTwiddleApply model stage x i -
          p09MixedRadixTwiddleApply stage x i) ≤
      (if stage.useTwiddle then
          (3 + 2 * model.gamma) * model.epsilon +
            (2 + 10 * model.gamma) * model.epsilon ^ 2
        else 0) * p09ComplexNorm2 x := by
  let c : ℝ := if stage.useTwiddle then
      (3 + 2 * model.gamma) * model.epsilon +
        (2 + 10 * model.gamma) * model.epsilon ^ 2 else 0
  have hu : 0 ≤ model.epsilon := le_of_lt model.epsilon_pos
  have hc : 0 ≤ c := by dsimp [c]; split <;> positivity
  apply p09_complexNorm2_le_pointwise_scale _ _ c hc
  intro i
  simp only [p09RoundedMixedRadixTwiddleApply,
    p09MixedRadixTwiddleApply]
  by_cases ht : stage.useTwiddle
  · simp only [ht, if_true]
    have hterm := p09_roundedGeneric_term_error_le model hγ hu1
      (stage.twiddleExponent i) (1 : ZMod n) (x i)
    simpa [c, ht] using hterm
  · simp [ht, c]

private noncomputable def p09StageSecond {n : ℕ} [NeZero n]
    (stage : P09MixedRadixStage n) (γ : ℝ) : ℝ :=
  p09BlockSecond stage.radix γ +
    if stage.useTwiddle then
      (2 + 10 * γ) +
        ((3 + 2 * γ) + (2 + 10 * γ)) *
          (p09Alpha stage.radix γ + p09BlockSecond stage.radix γ)
    else 0

private lemma p09_stageSecond_nonneg {n : ℕ} [NeZero n]
    (stage : P09MixedRadixStage n) (γ : ℝ) (hγ : 0 ≤ γ) :
    0 ≤ p09StageSecond stage γ := by
  unfold p09StageSecond
  have ha := p09_alpha_nonneg stage.radix γ stage.radix_two_le hγ
  have hs := p09_blockSecond_nonneg stage.radix γ stage.radix_two_le hγ
  split <;> positivity

private lemma p09_roundedMixedRadixStage_error_norm2 {n : ℕ} [NeZero n]
    (model : P09WilkinsonModel) (hγ : 0 ≤ model.gamma)
    (hu1 : model.epsilon ≤ 1) (stage : P09MixedRadixStage n)
    (hnorm : ∀ v : ZMod n → ℂ,
      p09ComplexNorm2 (p09MixedRadixStageApply stage v) =
        Real.sqrt stage.radix * p09ComplexNorm2 v)
    (x : ZMod n → ℂ) :
    p09ComplexNorm2 (fun i ↦
        p09RoundedMixedRadixStageApply model stage x i -
          p09MixedRadixStageApply stage x i) ≤
      Real.sqrt stage.radix *
        ((p09Alpha stage.radix model.gamma +
            if stage.useTwiddle then 3 + 2 * model.gamma else 0) *
            model.epsilon +
          p09StageSecond stage model.gamma * model.epsilon ^ 2) *
        p09ComplexNorm2 x := by
  let z := p09RoundedMixedRadixBlockApply model stage x
  let y := p09MixedRadixBlockApply stage x
  let a := p09Alpha stage.radix model.gamma
  let s := p09BlockSecond stage.radix model.gamma
  let b : ℝ := 3 + 2 * model.gamma
  let d : ℝ := 2 + 10 * model.gamma
  have hu : 0 ≤ model.epsilon := le_of_lt model.epsilon_pos
  have ha : 0 ≤ a := p09_alpha_nonneg _ _ stage.radix_two_le hγ
  have hs : 0 ≤ s := p09_blockSecond_nonneg _ _ stage.radix_two_le hγ
  have hb : 0 ≤ b := by dsimp [b]; positivity
  have hd : 0 ≤ d := by dsimp [d]; positivity
  have hblock := p09_roundedMixedRadixBlock_error_norm2 model hγ hu1 stage x
  have hblock' : p09ComplexNorm2 (fun i ↦ z i - y i) ≤
      Real.sqrt stage.radix * (a * model.epsilon +
        s * model.epsilon ^ 2) * p09ComplexNorm2 x := by
    simpa [z, y, a, s] using hblock
  have hy : p09ComplexNorm2 y = Real.sqrt stage.radix * p09ComplexNorm2 x := by
    have hn := p09_mixedRadixTwiddle_norm2 stage y
    calc
      p09ComplexNorm2 y =
          p09ComplexNorm2 (p09MixedRadixTwiddleApply stage y) := hn.symm
      _ = p09ComplexNorm2 (p09MixedRadixStageApply stage x) := by rfl
      _ = Real.sqrt stage.radix * p09ComplexNorm2 x := hnorm x
  have hz : p09ComplexNorm2 z ≤ Real.sqrt stage.radix *
      (1 + a * model.epsilon + s * model.epsilon ^ 2) *
        p09ComplexNorm2 x := by
    have htri : p09ComplexNorm2 z ≤ p09ComplexNorm2 y +
        p09ComplexNorm2 (fun i ↦ z i - y i) := by
      calc
        p09ComplexNorm2 z =
            p09ComplexNorm2 (fun i ↦ y i + (z i - y i)) := by
              congr 2
              funext i
              abel
        _ ≤ p09ComplexNorm2 y + p09ComplexNorm2 (fun i ↦ z i - y i) :=
          p09_complexNorm2_add_le _ _
    calc
      p09ComplexNorm2 z ≤ p09ComplexNorm2 y +
          p09ComplexNorm2 (fun i ↦ z i - y i) := htri
      _ ≤ Real.sqrt stage.radix * p09ComplexNorm2 x +
          (Real.sqrt stage.radix * (a * model.epsilon +
            s * model.epsilon ^ 2) * p09ComplexNorm2 x) := by
        rw [hy]
        exact add_le_add le_rfl hblock'
      _ = Real.sqrt stage.radix *
          (1 + a * model.epsilon + s * model.epsilon ^ 2) *
            p09ComplexNorm2 x := by ring
  have htw := p09_roundedTwiddle_error_norm2 model hγ hu1 stage z
  have hlip := p09_mixedRadixTwiddle_sub_norm2 stage z y
  have htriStage : p09ComplexNorm2 (fun i ↦
        p09RoundedMixedRadixStageApply model stage x i -
          p09MixedRadixStageApply stage x i) ≤
      p09ComplexNorm2 (fun i ↦
        p09RoundedMixedRadixTwiddleApply model stage z i -
          p09MixedRadixTwiddleApply stage z i) +
      p09ComplexNorm2 (fun i ↦ z i - y i) := by
    calc
      _ = p09ComplexNorm2 (fun i ↦
          (p09RoundedMixedRadixTwiddleApply model stage z i -
            p09MixedRadixTwiddleApply stage z i) +
          (p09MixedRadixTwiddleApply stage z i -
            p09MixedRadixTwiddleApply stage y i)) := by
        congr 2
        funext i
        simp [p09RoundedMixedRadixStageApply, p09MixedRadixStageApply, z, y]
      _ ≤ p09ComplexNorm2 (fun i ↦
            p09RoundedMixedRadixTwiddleApply model stage z i -
              p09MixedRadixTwiddleApply stage z i) +
          p09ComplexNorm2 (fun i ↦
            p09MixedRadixTwiddleApply stage z i -
              p09MixedRadixTwiddleApply stage y i) :=
        p09_complexNorm2_add_le _ _
      _ = _ := by rw [hlip]
  by_cases ht : stage.useTwiddle
  · have htw' : p09ComplexNorm2 (fun i ↦
        p09RoundedMixedRadixTwiddleApply model stage z i -
          p09MixedRadixTwiddleApply stage z i) ≤
        (b * model.epsilon + d * model.epsilon ^ 2) *
          p09ComplexNorm2 z := by simpa [ht, b, d] using htw
    have hcross : (b * model.epsilon + d * model.epsilon ^ 2) *
          (a * model.epsilon + s * model.epsilon ^ 2) ≤
        (b + d) * (a + s) * model.epsilon ^ 2 := by
      have hua : a * model.epsilon + s * model.epsilon ^ 2 ≤
          (a + s) * model.epsilon := by
        nlinarith [mul_le_mul_of_nonneg_left
          (show model.epsilon ^ 2 ≤ model.epsilon by nlinarith) hs]
      have hub : b * model.epsilon + d * model.epsilon ^ 2 ≤
          (b + d) * model.epsilon := by
        nlinarith [mul_le_mul_of_nonneg_left
          (show model.epsilon ^ 2 ≤ model.epsilon by nlinarith) hd]
      exact mul_le_mul hub hua (by positivity) (by positivity) |>.trans_eq (by ring)
    calc
      _ ≤ (b * model.epsilon + d * model.epsilon ^ 2) *
            p09ComplexNorm2 z +
          p09ComplexNorm2 (fun i ↦ z i - y i) :=
        htriStage.trans (add_le_add htw' le_rfl)
      _ ≤ (b * model.epsilon + d * model.epsilon ^ 2) *
            (Real.sqrt stage.radix *
              (1 + a * model.epsilon + s * model.epsilon ^ 2) *
                p09ComplexNorm2 x) +
          (Real.sqrt stage.radix * (a * model.epsilon +
            s * model.epsilon ^ 2) * p09ComplexNorm2 x) := by
        exact add_le_add
          (mul_le_mul_of_nonneg_left hz (by positivity)) hblock'
      _ ≤ Real.sqrt stage.radix *
          ((a + b) * model.epsilon +
            (s + d + (b + d) * (a + s)) * model.epsilon ^ 2) *
            p09ComplexNorm2 x := by
        have hsqrt : 0 ≤ Real.sqrt (stage.radix : ℝ) := Real.sqrt_nonneg _
        have hx : 0 ≤ p09ComplexNorm2 x := p09_complexNorm2_nonneg _
        have hcoef :
            (b * model.epsilon + d * model.epsilon ^ 2) *
                (1 + a * model.epsilon + s * model.epsilon ^ 2) +
              (a * model.epsilon + s * model.epsilon ^ 2) ≤
            (a + b) * model.epsilon +
              (s + d + (b + d) * (a + s)) * model.epsilon ^ 2 := by
          nlinarith
        have hm := mul_le_mul_of_nonneg_right
          (mul_le_mul_of_nonneg_left hcoef hsqrt) hx
        convert hm using 1 <;> ring
      _ = _ := by
        simp only [p09StageSecond, ht, if_pos]
        dsimp [a, b, d, s]
        ring
  · have htwzero : p09ComplexNorm2 (fun i ↦
        p09RoundedMixedRadixTwiddleApply model stage z i -
          p09MixedRadixTwiddleApply stage z i) = 0 := by
      have := htw
      simp [ht] at this
      exact le_antisymm this (p09_complexNorm2_nonneg _)
    calc
      _ ≤ 0 + p09ComplexNorm2 (fun i ↦ z i - y i) := by
        rw [← htwzero]
        exact htriStage
      _ ≤ Real.sqrt stage.radix * (a * model.epsilon +
            s * model.epsilon ^ 2) * p09ComplexNorm2 x := by
        simpa using hblock'
      _ = _ := by
        simp only [p09StageSecond, ht, if_neg]
        dsimp [a, s]
        ring

private noncomputable def p09StageFirst {n : ℕ} [NeZero n]
    (stage : P09MixedRadixStage n) (γ : ℝ) : ℝ :=
  p09Alpha stage.radix γ +
    if stage.useTwiddle then 3 + 2 * γ else 0

private noncomputable def p09StageScale {n : ℕ} [NeZero n]
    (stage : P09MixedRadixStage n) : ℝ := Real.sqrt stage.radix

private noncomputable def p09StageListFirst {n : ℕ} [NeZero n]
    (stages : List (P09MixedRadixStage n)) (γ : ℝ) : ℝ :=
  (stages.map fun stage ↦ p09StageFirst stage γ).sum

private noncomputable def p09StageListScale {n : ℕ} [NeZero n]
    (stages : List (P09MixedRadixStage n)) : ℝ :=
  (stages.map p09StageScale).prod

private noncomputable def p09StageListSecond {n : ℕ} [NeZero n]
    (γ : ℝ) : List (P09MixedRadixStage n) → ℝ
  | [] => 0
  | stage :: stages =>
      let A := p09StageFirst stage γ
      let S := p09StageSecond stage γ
      let AT := p09StageListFirst stages γ
      let ST := p09StageListSecond γ stages
      ST + S + (AT + ST) * (A + S)

private lemma p09_stageFirst_nonneg {n : ℕ} [NeZero n]
    (stage : P09MixedRadixStage n) (γ : ℝ) (hγ : 0 ≤ γ) :
    0 ≤ p09StageFirst stage γ := by
  unfold p09StageFirst
  have ha := p09_alpha_nonneg stage.radix γ stage.radix_two_le hγ
  split <;> positivity

private lemma p09_stageListFirst_nonneg {n : ℕ} [NeZero n]
    (stages : List (P09MixedRadixStage n)) (γ : ℝ) (hγ : 0 ≤ γ) :
    0 ≤ p09StageListFirst stages γ := by
  induction stages with
  | nil => simp [p09StageListFirst]
  | cons stage stages ih =>
      simp only [p09StageListFirst, List.map_cons, List.sum_cons]
      exact add_nonneg (p09_stageFirst_nonneg stage γ hγ) ih

private lemma p09_stageListScale_nonneg {n : ℕ} [NeZero n]
    (stages : List (P09MixedRadixStage n)) :
    0 ≤ p09StageListScale stages := by
  induction stages with
  | nil => simp [p09StageListScale]
  | cons stage stages ih =>
      simp only [p09StageListScale, List.map_cons, List.prod_cons,
        p09StageScale]
      exact mul_nonneg (Real.sqrt_nonneg _) ih

private lemma p09_stageListSecond_nonneg {n : ℕ} [NeZero n]
    (stages : List (P09MixedRadixStage n)) (γ : ℝ) (hγ : 0 ≤ γ) :
    0 ≤ p09StageListSecond γ stages := by
  induction stages with
  | nil => simp [p09StageListSecond]
  | cons stage stages ih =>
      simp only [p09StageListSecond]
      have ha := p09_stageFirst_nonneg stage γ hγ
      have hs := p09_stageSecond_nonneg stage γ hγ
      have hat := p09_stageListFirst_nonneg stages γ hγ
      positivity

private lemma p09_mixedRadixStage_sub {n : ℕ} [NeZero n]
    (stage : P09MixedRadixStage n) (x y : ZMod n → ℂ) :
    p09MixedRadixStageApply stage (fun i ↦ x i - y i) =
      fun i ↦ p09MixedRadixStageApply stage x i -
        p09MixedRadixStageApply stage y i := by
  funext i
  simp only [p09MixedRadixStageApply, p09MixedRadixTwiddleApply,
    p09MixedRadixBlockApply]
  split <;> simp_rw [mul_sub, Finset.sum_sub_distrib] <;> ring

private lemma p09_exactStageList_sub {n : ℕ} [NeZero n]
    (stages : List (P09MixedRadixStage n)) (x y : ZMod n → ℂ) :
    stages.foldl (fun state stage ↦ p09MixedRadixStageApply stage state)
        (fun i ↦ x i - y i) =
      fun i ↦
        stages.foldl (fun state stage ↦ p09MixedRadixStageApply stage state) x i -
        stages.foldl (fun state stage ↦ p09MixedRadixStageApply stage state) y i := by
  induction stages generalizing x y with
  | nil => rfl
  | cons stage stages ih =>
      simp only [List.foldl_cons]
      rw [p09_mixedRadixStage_sub]
      exact ih _ _

private lemma p09_exactStageList_norm2 {n : ℕ} [NeZero n]
    (stages : List (P09MixedRadixStage n))
    (hnorm : ∀ stage ∈ stages, ∀ v : ZMod n → ℂ,
      p09ComplexNorm2 (p09MixedRadixStageApply stage v) =
        Real.sqrt stage.radix * p09ComplexNorm2 v)
    (x : ZMod n → ℂ) :
    p09ComplexNorm2
        (stages.foldl (fun state stage ↦ p09MixedRadixStageApply stage state) x) =
      p09StageListScale stages * p09ComplexNorm2 x := by
  induction stages generalizing x with
  | nil => simp [p09StageListScale]
  | cons stage stages ih =>
      simp only [List.foldl_cons]
      rw [ih (fun s hs ↦ hnorm s (by simp [hs]))]
      rw [hnorm stage (by simp)]
      simp only [p09StageListScale, List.map_cons, List.prod_cons,
        p09StageScale]
      ring

private lemma p09_exactStageList_sub_norm2 {n : ℕ} [NeZero n]
    (stages : List (P09MixedRadixStage n))
    (hnorm : ∀ stage ∈ stages, ∀ v : ZMod n → ℂ,
      p09ComplexNorm2 (p09MixedRadixStageApply stage v) =
        Real.sqrt stage.radix * p09ComplexNorm2 v)
    (x y : ZMod n → ℂ) :
    p09ComplexNorm2 (fun i ↦
        stages.foldl (fun state stage ↦ p09MixedRadixStageApply stage state) x i -
        stages.foldl (fun state stage ↦ p09MixedRadixStageApply stage state) y i) =
      p09StageListScale stages * p09ComplexNorm2 (fun i ↦ x i - y i) := by
  rw [← p09_exactStageList_sub]
  exact p09_exactStageList_norm2 stages hnorm _

private lemma p09_roundedStageList_error_norm2 {n : ℕ} [NeZero n]
    (model : P09WilkinsonModel) (hγ : 0 ≤ model.gamma)
    (hu1 : model.epsilon ≤ 1)
    (stages : List (P09MixedRadixStage n))
    (hnorm : ∀ stage ∈ stages, ∀ v : ZMod n → ℂ,
      p09ComplexNorm2 (p09MixedRadixStageApply stage v) =
        Real.sqrt stage.radix * p09ComplexNorm2 v)
    (x : ZMod n → ℂ) :
    p09ComplexNorm2 (fun i ↦
        stages.foldl
            (fun state stage ↦ p09RoundedMixedRadixStageApply model stage state) x i -
          stages.foldl
            (fun state stage ↦ p09MixedRadixStageApply stage state) x i) ≤
      p09StageListScale stages *
        (p09StageListFirst stages model.gamma * model.epsilon +
          p09StageListSecond model.gamma stages * model.epsilon ^ 2) *
        p09ComplexNorm2 x := by
  induction stages generalizing x with
  | nil =>
      simp [p09StageListScale, p09StageListFirst, p09StageListSecond,
        p09ComplexNorm2, p09ComplexNorm2Sq]
  | cons stage stages ih =>
      let rx := p09RoundedMixedRadixStageApply model stage x
      let ex := p09MixedRadixStageApply stage x
      let A := p09StageFirst stage model.gamma
      let S := p09StageSecond stage model.gamma
      let AT := p09StageListFirst stages model.gamma
      let ST := p09StageListSecond model.gamma stages
      let scaleT := p09StageListScale stages
      have hu : 0 ≤ model.epsilon := le_of_lt model.epsilon_pos
      have hA := p09_stageFirst_nonneg stage model.gamma hγ
      have hS := p09_stageSecond_nonneg stage model.gamma hγ
      have hAT := p09_stageListFirst_nonneg stages model.gamma hγ
      have hST := p09_stageListSecond_nonneg stages model.gamma hγ
      have hscaleT := p09_stageListScale_nonneg stages
      have hnormStage := hnorm stage (by simp)
      have hnormTail : ∀ s ∈ stages, ∀ v : ZMod n → ℂ,
          p09ComplexNorm2 (p09MixedRadixStageApply s v) =
            Real.sqrt s.radix * p09ComplexNorm2 v :=
        fun s hs ↦ hnorm s (by simp [hs])
      have hlocal := p09_roundedMixedRadixStage_error_norm2
        model hγ hu1 stage hnormStage x
      have hlocal' : p09ComplexNorm2 (fun i ↦ rx i - ex i) ≤
          Real.sqrt stage.radix *
            (A * model.epsilon + S * model.epsilon ^ 2) *
              p09ComplexNorm2 x := by
        simpa [rx, ex, A, S, p09StageFirst] using hlocal
      have hrx : p09ComplexNorm2 rx ≤ Real.sqrt stage.radix *
          (1 + A * model.epsilon + S * model.epsilon ^ 2) *
            p09ComplexNorm2 x := by
        calc
          p09ComplexNorm2 rx ≤ p09ComplexNorm2 ex +
              p09ComplexNorm2 (fun i ↦ rx i - ex i) := by
            calc
              _ = p09ComplexNorm2 (fun i ↦ ex i + (rx i - ex i)) := by
                congr 2
                funext i
                abel
              _ ≤ _ := p09_complexNorm2_add_le _ _
          _ ≤ Real.sqrt stage.radix * p09ComplexNorm2 x +
              Real.sqrt stage.radix * (A * model.epsilon +
                S * model.epsilon ^ 2) * p09ComplexNorm2 x := by
            rw [hnormStage]
            exact add_le_add le_rfl hlocal'
          _ = _ := by ring
      have htailRounded := ih hnormTail rx
      have htailExact := p09_exactStageList_sub_norm2 stages hnormTail rx ex
      have htri : p09ComplexNorm2 (fun i ↦
          stages.foldl
              (fun state stage ↦ p09RoundedMixedRadixStageApply model stage state) rx i -
            stages.foldl
              (fun state stage ↦ p09MixedRadixStageApply stage state) ex i) ≤
          p09ComplexNorm2 (fun i ↦
            stages.foldl
                (fun state stage ↦ p09RoundedMixedRadixStageApply model stage state) rx i -
              stages.foldl
                (fun state stage ↦ p09MixedRadixStageApply stage state) rx i) +
          p09ComplexNorm2 (fun i ↦
            stages.foldl
                (fun state stage ↦ p09MixedRadixStageApply stage state) rx i -
              stages.foldl
                (fun state stage ↦ p09MixedRadixStageApply stage state) ex i) := by
        calc
          _ = p09ComplexNorm2 (fun i ↦
              (stages.foldl
                  (fun state stage ↦ p09RoundedMixedRadixStageApply model stage state) rx i -
                stages.foldl
                  (fun state stage ↦ p09MixedRadixStageApply stage state) rx i) +
              (stages.foldl
                  (fun state stage ↦ p09MixedRadixStageApply stage state) rx i -
                stages.foldl
                  (fun state stage ↦ p09MixedRadixStageApply stage state) ex i)) := by
            congr 2
            funext i
            ring
          _ ≤ _ := p09_complexNorm2_add_le _ _
      have hcross : (AT * model.epsilon + ST * model.epsilon ^ 2) *
            (A * model.epsilon + S * model.epsilon ^ 2) ≤
          (AT + ST) * (A + S) * model.epsilon ^ 2 := by
        have hu2 : model.epsilon ^ 2 ≤ model.epsilon := by nlinarith
        have hleft : AT * model.epsilon + ST * model.epsilon ^ 2 ≤
            (AT + ST) * model.epsilon := by
          nlinarith [mul_le_mul_of_nonneg_left hu2 hST]
        have hright : A * model.epsilon + S * model.epsilon ^ 2 ≤
            (A + S) * model.epsilon := by
          nlinarith [mul_le_mul_of_nonneg_left hu2 hS]
        have hp := mul_le_mul hleft hright (by positivity) (by positivity)
        convert hp using 1 <;> ring
      simp only [List.foldl_cons]
      calc
        _ ≤ p09ComplexNorm2 (fun i ↦
              stages.foldl
                  (fun state stage ↦ p09RoundedMixedRadixStageApply model stage state) rx i -
                stages.foldl
                  (fun state stage ↦ p09MixedRadixStageApply stage state) rx i) +
            p09ComplexNorm2 (fun i ↦
              stages.foldl
                  (fun state stage ↦ p09MixedRadixStageApply stage state) rx i -
                stages.foldl
                  (fun state stage ↦ p09MixedRadixStageApply stage state) ex i) := htri
        _ ≤ scaleT * (AT * model.epsilon + ST * model.epsilon ^ 2) *
              p09ComplexNorm2 rx +
            scaleT * p09ComplexNorm2 (fun i ↦ rx i - ex i) := by
          rw [htailExact]
          exact add_le_add htailRounded le_rfl
        _ ≤ scaleT * (AT * model.epsilon + ST * model.epsilon ^ 2) *
              (Real.sqrt stage.radix *
                (1 + A * model.epsilon + S * model.epsilon ^ 2) *
                  p09ComplexNorm2 x) +
            scaleT * (Real.sqrt stage.radix *
              (A * model.epsilon + S * model.epsilon ^ 2) *
                p09ComplexNorm2 x) := by
          exact add_le_add
            (mul_le_mul_of_nonneg_left hrx
              (mul_nonneg hscaleT (by positivity)))
            (mul_le_mul_of_nonneg_left hlocal' hscaleT)
        _ ≤ (Real.sqrt stage.radix * scaleT) *
              ((AT + A) * model.epsilon +
                (ST + S + (AT + ST) * (A + S)) * model.epsilon ^ 2) *
              p09ComplexNorm2 x := by
          have hsqrt := Real.sqrt_nonneg (stage.radix : ℝ)
          have hx := p09_complexNorm2_nonneg x
          have hcoef :
              (AT * model.epsilon + ST * model.epsilon ^ 2) *
                  (1 + A * model.epsilon + S * model.epsilon ^ 2) +
                (A * model.epsilon + S * model.epsilon ^ 2) ≤
              (AT + A) * model.epsilon +
                (ST + S + (AT + ST) * (A + S)) * model.epsilon ^ 2 := by
            nlinarith
          have hm := mul_le_mul_of_nonneg_right
            (mul_le_mul_of_nonneg_left hcoef
              (mul_nonneg hscaleT hsqrt)) hx
          convert hm using 1 <;> ring
        _ = p09StageListScale (stage :: stages) *
              (p09StageListFirst (stage :: stages) model.gamma * model.epsilon +
                p09StageListSecond model.gamma (stage :: stages) *
                  model.epsilon ^ 2) * p09ComplexNorm2 x := by
          simp only [p09StageListScale, p09StageListFirst,
            p09StageListSecond, List.map_cons, List.prod_cons,
            List.sum_cons]
          change Real.sqrt stage.radix * scaleT *
              ((AT + A) * model.epsilon +
                (ST + S + (AT + ST) * (A + S)) * model.epsilon ^ 2) *
                p09ComplexNorm2 x =
            Real.sqrt stage.radix * scaleT *
              ((A + AT) * model.epsilon +
                (ST + S + (AT + ST) * (A + S)) * model.epsilon ^ 2) *
                p09ComplexNorm2 x
          ring

private lemma p09_list_prod_sqrt {α : Type} (xs : List α) (q : α → ℕ) :
    (xs.map (fun a ↦ Real.sqrt (q a : ℝ))).prod =
      Real.sqrt (((xs.map q).prod : ℕ) : ℝ) := by
  induction xs with
  | nil => simp
  | cons a xs ih =>
      simp only [List.map_cons, List.prod_cons, Nat.cast_mul]
      rw [ih, Real.sqrt_mul (Nat.cast_nonneg (q a))]

private lemma p09_fftStageList_scale {n : ℕ} [NeZero n]
    (plan : P09MixedRadixFftPlan n) :
    p09StageListScale (List.ofFn plan.stage) = Real.sqrt (n : ℝ) := by
  rw [p09StageListScale]
  change ((List.ofFn plan.stage).map
      (fun stage ↦ Real.sqrt (stage.radix : ℝ))).prod = _
  rw [p09_list_prod_sqrt]
  congr 2
  rw [List.map_ofFn]
  rw [Fin.prod_ofFn]
  exact_mod_cast plan.order_factorization

private lemma p09_sum_twiddle_pattern {r : ℕ} (hr : 0 < r)
    (useTwiddle : Fin r → Bool)
    (hpattern : ∀ i : Fin r,
      useTwiddle i = decide (i.val + 1 < r)) (c : ℝ) :
    (∑ i : Fin r, if useTwiddle i = true then c else 0) =
      ((r : ℝ) - 1) * c := by
  obtain ⟨k, rfl⟩ := Nat.exists_eq_succ_of_ne_zero (Nat.ne_of_gt hr)
  rw [Fin.sum_univ_castSucc]
  simp only [hpattern]
  simp

private lemma p09_fftStageList_first {n : ℕ} [NeZero n]
    (plan : P09MixedRadixFftPlan n) (γ : ℝ) :
    p09StageListFirst (List.ofFn plan.stage) γ = p09K plan γ := by
  unfold p09StageListFirst p09StageFirst p09K
  rw [List.map_ofFn, List.sum_ofFn]
  simp only [Function.comp_apply]
  rw [Finset.sum_add_distrib]
  rw [p09_sum_twiddle_pattern plan.stageCount_pos
    (fun i ↦ (plan.stage i).useTwiddle) plan.twiddle_pattern]

private lemma p09_roundedFft_error_norm2 {n : ℕ} [NeZero n]
    (plan : P09MixedRadixFftPlan n) (model : P09WilkinsonModel)
    (hγ : 0 ≤ model.gamma) (hu1 : model.epsilon ≤ 1)
    (x : ZMod n → ℂ) :
    p09ComplexNorm2 (fun i ↦
        p09RoundedFftApply plan model x i - p09FourierTransform x i) ≤
      Real.sqrt (n : ℝ) *
        (p09K plan model.gamma * model.epsilon +
          p09StageListSecond model.gamma (List.ofFn plan.stage) *
            model.epsilon ^ 2) * p09ComplexNorm2 x := by
  have hnorm : ∀ stage ∈ List.ofFn plan.stage,
      ∀ v : ZMod n → ℂ,
        p09ComplexNorm2 (p09MixedRadixStageApply stage v) =
          Real.sqrt stage.radix * p09ComplexNorm2 v := by
    intro stage hstage v
    rcases List.mem_ofFn.mp hstage with ⟨i, rfl⟩
    exact plan.stage_norm_scaling i v
  have h := p09_roundedStageList_error_norm2 model hγ hu1
    (List.ofFn plan.stage) hnorm x
  rw [p09_fftStageList_scale plan, p09_fftStageList_first plan] at h
  let err : ZMod n → ℂ := fun i ↦
    p09ApplyRoundedMixedRadixStages model plan.stage x i -
      p09ApplyMixedRadixStages plan.stage x i
  calc
    p09ComplexNorm2 (fun i ↦
        p09RoundedFftApply plan model x i - p09FourierTransform x i) =
        p09ComplexNorm2 (fun i ↦ err (plan.finalPermutation i)) := by
      rw [← plan.exact_factorization x]
      rfl
    _ = p09ComplexNorm2 err := p09_complexNorm2_equiv plan.finalPermutation err
    _ ≤ _ := by simpa [err, p09ApplyRoundedMixedRadixStages,
      p09ApplyMixedRadixStages] using h

private lemma p09_multiNorm2_nonneg {m : ℕ}
    {axis : Fin m → P09FftAxis} (x : P09MultiArray axis) :
    0 ≤ p09MultiNorm2 x := by
  unfold p09MultiNorm2
  exact norm_nonneg _

private lemma p09_multiNorm2_sq {m : ℕ}
    {axis : Fin m → P09FftAxis} (x : P09MultiArray axis) :
    p09MultiNorm2 x ^ 2 = ∑ index : P09MultiIndex axis, ‖x index‖ ^ 2 := by
  unfold p09MultiNorm2
  rw [EuclideanSpace.norm_sq_eq]

private abbrev P09FiberBase {m : ℕ} (axis : Fin m → P09FftAxis)
    (i : Fin m) :=
  {index : P09MultiIndex axis // index i = 0}

private def p09FiberEquiv {m : ℕ} (axis : Fin m → P09FftAxis)
    (i : Fin m) :
    P09FiberBase axis i × ZMod (axis i).order ≃ P09MultiIndex axis where
  toFun p := Function.update p.1.1 i p.2
  invFun index :=
    (⟨Function.update index i 0, by simp⟩, index i)
  left_inv p := by
    apply Prod.ext
    · apply Subtype.ext
      funext k
      by_cases hki : k = i
      · subst k
        simp [p.1.2]
      · simp [hki]
    · simp
  right_inv index := by
    funext k
    by_cases hki : k = i
    · subst k
      simp
    · simp [hki]

private lemma p09_aggregate_multi_fibers {m q : ℕ} [NeZero q]
    {axis : Fin m → P09FftAxis} {α : Type} [Fintype α]
    (reindex : α × ZMod q ≃ P09MultiIndex axis)
    (err inp : P09MultiArray axis) (c : ℝ) (hc : 0 ≤ c)
    (hblock : ∀ block : α,
      p09ComplexNorm2 (fun k ↦ err (reindex (block, k))) ≤
        c * p09ComplexNorm2 (fun j ↦ inp (reindex (block, j)))) :
    p09MultiNorm2 err ≤ c * p09MultiNorm2 inp := by
  apply (sq_le_sq₀ (p09_multiNorm2_nonneg err)
    (mul_nonneg hc (p09_multiNorm2_nonneg inp))).mp
  rw [p09_multiNorm2_sq, mul_pow, p09_multiNorm2_sq]
  rw [← Equiv.sum_comp reindex, Fintype.sum_prod_type,
    ← Equiv.sum_comp reindex, Fintype.sum_prod_type]
  calc
    (∑ block : α, ∑ k : ZMod q, ‖err (reindex (block, k))‖ ^ 2)
        ≤ ∑ block : α,
            c ^ 2 * ∑ j : ZMod q, ‖inp (reindex (block, j))‖ ^ 2 := by
          apply Finset.sum_le_sum
          intro block _
          have hb := (sq_le_sq₀
            (p09_complexNorm2_nonneg (fun k ↦ err (reindex (block, k))))
            (mul_nonneg hc (p09_complexNorm2_nonneg
              (fun j ↦ inp (reindex (block, j)))))).2 (hblock block)
          rw [p09_complexNorm2_sq, mul_pow, p09_complexNorm2_sq] at hb
          exact hb
    _ = c ^ 2 * ∑ block : α,
          ∑ j : ZMod q, ‖inp (reindex (block, j))‖ ^ 2 := by
        rw [Finset.mul_sum]

private lemma p09_axisK_nonneg (axis : P09FftAxis) (γ : ℝ)
    (hγ : 0 ≤ γ) : 0 ≤ p09AxisK axis γ := by
  change 0 ≤ p09K axis.plan γ
  rw [← p09_fftStageList_first axis.plan]
  exact p09_stageListFirst_nonneg _ _ hγ

private noncomputable def p09AxisSecond (axis : P09FftAxis) (γ : ℝ) : ℝ :=
  @p09StageListSecond axis.order (p09FftAxisOrderNeZero axis) γ
    (List.ofFn axis.plan.stage)

private lemma p09_roundedCoordinate_error_norm2 {m : ℕ}
    (axis : Fin m → P09FftAxis) (i : Fin m)
    (model : P09WilkinsonModel) (hγ : 0 ≤ model.gamma)
    (hu1 : model.epsilon ≤ 1) (x : P09MultiArray axis) :
    p09MultiNorm2 (fun index : P09MultiIndex axis ↦
        p09RoundedCoordinateTransform axis i model x index -
          p09CoordinateTransform axis i x index) ≤
      Real.sqrt ((axis i).order : ℝ) *
        (p09AxisK (axis i) model.gamma * model.epsilon +
          p09AxisSecond (axis i) model.gamma * model.epsilon ^ 2) *
        p09MultiNorm2 x := by
  let C := p09AxisSecond (axis i) model.gamma
  let c := Real.sqrt ((axis i).order : ℝ) *
    (p09AxisK (axis i) model.gamma * model.epsilon +
      C * model.epsilon ^ 2)
  have hu : 0 ≤ model.epsilon := le_of_lt model.epsilon_pos
  have hC : 0 ≤ C := by
    dsimp [C, p09AxisSecond]
    exact p09_stageListSecond_nonneg _ _ hγ
  have hK : 0 ≤ p09AxisK (axis i) model.gamma :=
    p09_axisK_nonneg _ _ hγ
  have hc : 0 ≤ c := by positivity
  apply p09_aggregate_multi_fibers (p09FiberEquiv axis i)
    (fun index ↦
      p09RoundedCoordinateTransform axis i model x index -
        p09CoordinateTransform axis i x index) x c hc
  intro base
  let fiber : ZMod (axis i).order → ℂ := fun j ↦
    x (Function.update base.1 i j)
  have h := p09_roundedFft_error_norm2 (axis i).plan model hγ hu1 fiber
  simpa [c, C, fiber, p09AxisK, p09FiberEquiv,
    p09RoundedCoordinateTransform, p09CoordinateTransform] using h

private noncomputable def p09AccumSecond (K C : ℕ → ℝ) : ℕ → ℝ
  | 0 => 0
  | r + 1 =>
      let KT := ∑ i : Fin r, K i.val
      let ST := p09AccumSecond K C r
      ST + C r + (KT + ST) * (K r + C r)

private lemma p09_accumSecond_nonneg (K C : ℕ → ℝ)
    (hK : ∀ i, 0 ≤ K i) (hC : ∀ i, 0 ≤ C i) :
    ∀ r, 0 ≤ p09AccumSecond K C r := by
  intro r
  induction r with
  | zero => simp [p09AccumSecond]
  | succ r ih =>
      simp only [p09AccumSecond]
      have hsum : 0 ≤ ∑ i : Fin r, K i.val :=
        Finset.sum_nonneg fun i _ ↦ hK i.val
      exact add_nonneg (add_nonneg ih (hC r))
        (mul_nonneg (add_nonneg hsum ih) (add_nonneg (hK r) (hC r)))

private lemma p09_sequence_error_bound {V : Type} [SeminormedAddCommGroup V]
    (x : ℕ → V) (K C : ℕ → ℝ) (u : ℝ)
    (hu : 0 ≤ u) (hu1 : u ≤ 1)
    (hK : ∀ i, 0 ≤ K i) (hC : ∀ i, 0 ≤ C i)
    (hstep : ∀ i, ‖x i - x (i + 1)‖ ≤
      (K i * u + C i * u ^ 2) * ‖x (i + 1)‖) :
    ∀ r, ‖x 0 - x r‖ ≤
      ((∑ i : Fin r, K i.val) * u +
        p09AccumSecond K C r * u ^ 2) * ‖x r‖ := by
  intro r
  induction r with
  | zero => simp [p09AccumSecond]
  | succ r ih =>
      let KT := ∑ i : Fin r, K i.val
      let ST := p09AccumSecond K C r
      let A := K r
      let S := C r
      let δ := A * u + S * u ^ 2
      have hKT : 0 ≤ KT := Finset.sum_nonneg fun i _ ↦ hK i.val
      have hST : 0 ≤ ST := p09_accumSecond_nonneg K C hK hC r
      have hA : 0 ≤ A := hK r
      have hS : 0 ≤ S := hC r
      have hδ : 0 ≤ δ := by positivity
      have hlast : ‖x r - x (r + 1)‖ ≤ δ * ‖x (r + 1)‖ := by
        simpa [δ, A, S] using hstep r
      have hxr : ‖x r‖ ≤ (1 + δ) * ‖x (r + 1)‖ := by
        calc
          ‖x r‖ = ‖(x r - x (r + 1)) + x (r + 1)‖ := by
            congr 1
            abel
          _ ≤ ‖x r - x (r + 1)‖ + ‖x (r + 1)‖ := norm_add_le _ _
          _ ≤ δ * ‖x (r + 1)‖ + ‖x (r + 1)‖ :=
            add_le_add hlast le_rfl
          _ = _ := by ring
      have hu2 : u ^ 2 ≤ u := by nlinarith
      have hcross : (KT * u + ST * u ^ 2) * (A * u + S * u ^ 2) ≤
          (KT + ST) * (A + S) * u ^ 2 := by
        have hleft : KT * u + ST * u ^ 2 ≤ (KT + ST) * u := by
          nlinarith [mul_le_mul_of_nonneg_left hu2 hST]
        have hright : A * u + S * u ^ 2 ≤ (A + S) * u := by
          nlinarith [mul_le_mul_of_nonneg_left hu2 hS]
        have hp := mul_le_mul hleft hright (by positivity) (by positivity)
        convert hp using 1 <;> ring
      have hcoef :
          (KT * u + ST * u ^ 2) * (1 + δ) + δ ≤
            (KT + A) * u +
              (ST + S + (KT + ST) * (A + S)) * u ^ 2 := by
        dsimp [δ]
        nlinarith
      calc
        ‖x 0 - x (r + 1)‖ ≤
            ‖x 0 - x r‖ + ‖x r - x (r + 1)‖ := by
          calc
            _ = ‖(x 0 - x r) + (x r - x (r + 1))‖ := by
              congr 1
              abel
            _ ≤ _ := norm_add_le _ _
        _ ≤ (KT * u + ST * u ^ 2) * ‖x r‖ +
              δ * ‖x (r + 1)‖ := by
          exact add_le_add (by simpa [KT, ST] using ih) hlast
        _ ≤ (KT * u + ST * u ^ 2) *
                ((1 + δ) * ‖x (r + 1)‖) +
              δ * ‖x (r + 1)‖ := by
          gcongr
        _ ≤ ((KT + A) * u +
              (ST + S + (KT + ST) * (A + S)) * u ^ 2) *
                ‖x (r + 1)‖ := by
          have hm := mul_le_mul_of_nonneg_right hcoef (norm_nonneg (x (r + 1)))
          convert hm using 1 <;> ring
        _ = ((∑ i : Fin (r + 1), K i.val) * u +
              p09AccumSecond K C (r + 1) * u ^ 2) *
                ‖x (r + 1)‖ := by
          rw [Fin.sum_univ_castSucc]
          simp only [Fin.val_last, p09AccumSecond]
          dsimp [KT, ST, A, S]

private lemma p09_multiCardinality_pos {m : ℕ}
    (axis : Fin m → P09FftAxis) : 0 < p09MultiCardinality axis := by
  unfold p09MultiCardinality
  exact Finset.prod_pos fun i _ ↦ (axis i).order_pos

private lemma p09_prefix_norm_scaling {m : ℕ} [NeZero m]
    (plan : P09MultidimensionalFftPlan m)
    (k : ℕ) (hk : k ≤ m) (x : P09MultiArray plan.axis) :
    p09MultiNorm2 (p09ApplyCoordinatePrefix plan.axis k x) =
      Real.sqrt (p09PrefixOrderProduct plan.axis k hk : ℝ) *
        p09MultiNorm2 x := by
  have h := plan.prefix_rms_scaling k hk x
  unfold p09MultiRms at h
  have hcard : Real.sqrt (p09MultiCardinality plan.axis : ℝ) ≠ 0 := by
    exact ne_of_gt (Real.sqrt_pos.2 (Nat.cast_pos.2
      (p09_multiCardinality_pos plan.axis)))
  field_simp [hcard] at h
  exact h

private lemma p09_coordinateTransform_sub {m : ℕ}
    (axis : Fin m → P09FftAxis) (i : Fin m)
    (x y : P09MultiArray axis) :
    p09CoordinateTransform axis i (fun index ↦ x index - y index) =
      fun index ↦ p09CoordinateTransform axis i x index -
        p09CoordinateTransform axis i y index := by
  funext index
  unfold p09CoordinateTransform
  rw [← Finset.sum_sub_distrib]
  apply Finset.sum_congr rfl
  intro j _
  ring

private lemma p09_coordinateTransformNat_sub {m : ℕ}
    (axis : Fin m → P09FftAxis) (i : ℕ)
    (x y : P09MultiArray axis) :
    p09CoordinateTransformNat axis i (fun index ↦ x index - y index) =
      fun index ↦ p09CoordinateTransformNat axis i x index -
        p09CoordinateTransformNat axis i y index := by
  unfold p09CoordinateTransformNat
  split
  · exact p09_coordinateTransform_sub axis _ x y
  · rfl

private lemma p09_prefix_sub {m : ℕ}
    (axis : Fin m → P09FftAxis) (k : ℕ)
    (x y : P09MultiArray axis) :
    p09ApplyCoordinatePrefix axis k (fun index ↦ x index - y index) =
      fun index ↦ p09ApplyCoordinatePrefix axis k x index -
        p09ApplyCoordinatePrefix axis k y index := by
  induction k generalizing x y with
  | zero => rfl
  | succ k ih =>
      simp only [p09ApplyCoordinatePrefix]
      rw [p09_coordinateTransformNat_sub, ih]

private lemma p09_prefixOrderProduct_succ {m : ℕ}
    (axis : Fin m → P09FftAxis) (i : Fin m) :
    p09PrefixOrderProduct axis (i.val + 1) (Nat.succ_le_of_lt i.isLt) =
      p09PrefixOrderProduct axis i.val (Nat.le_of_lt i.isLt) *
        (axis i).order := by
  unfold p09PrefixOrderProduct
  rw [Fin.prod_univ_castSucc]
  congr 1

private lemma p09_prefix_sqrt_succ {m : ℕ}
    (axis : Fin m → P09FftAxis) (i : Fin m) :
    Real.sqrt (p09PrefixOrderProduct axis i.val
        (Nat.le_of_lt i.isLt) : ℝ) *
        Real.sqrt ((axis i).order : ℝ) =
      Real.sqrt (p09PrefixOrderProduct axis (i.val + 1)
        (Nat.succ_le_of_lt i.isLt) : ℝ) := by
  rw [p09_prefixOrderProduct_succ]
  rw [Nat.cast_mul, Real.sqrt_mul (Nat.cast_nonneg _)]

private noncomputable def p09RunPrefixState {m : ℕ} [NeZero m]
    {plan : P09MultidimensionalFftPlan m} {model : P09WilkinsonModel}
    (run : P09MultidimensionalFftRun plan model) (k : Fin (m + 1)) :
    P09MultiArray plan.axis :=
  p09ApplyCoordinatePrefix plan.axis k.val (run.computedState k)

private lemma p09_run_adjacent_error {m : ℕ} [NeZero m]
    (plan : P09MultidimensionalFftPlan m) (model : P09WilkinsonModel)
    (run : P09MultidimensionalFftRun plan model)
    (hγ : 0 ≤ model.gamma) (hu1 : model.epsilon ≤ 1)
    (i : Fin m) :
    ‖(WithLp.toLp 2
        (@p09MultiVecSub m plan.axis
          (p09RunPrefixState (plan := plan) (model := model) run i.castSucc)
          (p09RunPrefixState (plan := plan) (model := model) run i.succ)) :
        EuclideanSpace ℂ (P09MultiIndex plan.axis))‖ ≤
      (p09AxisK (plan.axis i) model.gamma * model.epsilon +
        p09AxisSecond (plan.axis i) model.gamma * model.epsilon ^ 2) *
        ‖(WithLp.toLp 2
          (p09RunPrefixState (plan := plan) (model := model) run i.succ) :
          EuclideanSpace ℂ (P09MultiIndex plan.axis))‖ := by
  let locerr : P09MultiArray plan.axis := fun index : P09MultiIndex plan.axis ↦
    p09RoundedCoordinateTransform plan.axis i model
        (run.computedState i.succ) index -
      p09CoordinateTransform plan.axis i
        (run.computedState i.succ) index
  let δ := p09AxisK (plan.axis i) model.gamma * model.epsilon +
    p09AxisSecond (plan.axis i) model.gamma * model.epsilon ^ 2
  have hlocal := p09_roundedCoordinate_error_norm2 plan.axis i model hγ hu1
    (run.computedState i.succ)
  have hpref := p09_prefix_norm_scaling plan i.val
    (Nat.le_of_lt i.isLt) locerr
  have hprefNext := p09_prefix_norm_scaling plan (i.val + 1)
    (Nat.succ_le_of_lt i.isLt) (run.computedState i.succ)
  have hident : p09MultiVecSub
        (p09RunPrefixState (plan := plan) (model := model) run i.castSucc)
        (p09RunPrefixState (plan := plan) (model := model) run i.succ) =
      p09ApplyCoordinatePrefix plan.axis i.val locerr := by
    unfold p09RunPrefixState p09MultiVecSub
    rw [run.stage_step i]
    rw [p09_prefix_sub]
    simp [p09ApplyCoordinatePrefix, p09CoordinateTransformNat, i.isLt]
  change p09MultiNorm2
      (p09MultiVecSub
        (p09RunPrefixState (plan := plan) (model := model) run i.castSucc)
        (p09RunPrefixState (plan := plan) (model := model) run i.succ)) ≤
    δ * p09MultiNorm2
      (p09ApplyCoordinatePrefix plan.axis (i.val + 1)
        (run.computedState i.succ))
  rw [hident, hpref, hprefNext]
  calc
    Real.sqrt (p09PrefixOrderProduct plan.axis i.val
          (Nat.le_of_lt i.isLt) : ℝ) * p09MultiNorm2 locerr ≤
        Real.sqrt (p09PrefixOrderProduct plan.axis i.val
          (Nat.le_of_lt i.isLt) : ℝ) *
          (Real.sqrt ((plan.axis i).order : ℝ) * δ *
            p09MultiNorm2 (run.computedState i.succ)) := by
      exact mul_le_mul_of_nonneg_left (by simpa [locerr, δ] using hlocal)
        (Real.sqrt_nonneg _)
    _ = δ * (Real.sqrt (p09PrefixOrderProduct plan.axis (i.val + 1)
          (Nat.succ_le_of_lt i.isLt) : ℝ) *
            p09MultiNorm2 (run.computedState i.succ)) := by
      rw [← p09_prefix_sqrt_succ plan.axis i]
      ring

private noncomputable def p09AxisKNat {m : ℕ} [NeZero m]
    (plan : P09MultidimensionalFftPlan m) (γ : ℝ) (i : ℕ) : ℝ :=
  if hi : i < m then p09AxisK (plan.axis ⟨i, hi⟩) γ else 0

private noncomputable def p09AxisSecondNat {m : ℕ} [NeZero m]
    (plan : P09MultidimensionalFftPlan m) (γ : ℝ) (i : ℕ) : ℝ :=
  if hi : i < m then p09AxisSecond (plan.axis ⟨i, hi⟩) γ else 0

private noncomputable def p09MultiSecond {m : ℕ} [NeZero m]
    (plan : P09MultidimensionalFftPlan m) (γ : ℝ) : ℝ :=
  p09AccumSecond (p09AxisKNat plan γ) (p09AxisSecondNat plan γ) m

private lemma p09_axisKNat_nonneg {m : ℕ} [NeZero m]
    (plan : P09MultidimensionalFftPlan m) (γ : ℝ) (hγ : 0 ≤ γ) :
    ∀ i, 0 ≤ p09AxisKNat plan γ i := by
  intro i
  unfold p09AxisKNat
  split
  · exact p09_axisK_nonneg _ _ hγ
  · exact le_rfl

private lemma p09_axisSecondNat_nonneg {m : ℕ} [NeZero m]
    (plan : P09MultidimensionalFftPlan m) (γ : ℝ) (hγ : 0 ≤ γ) :
    ∀ i, 0 ≤ p09AxisSecondNat plan γ i := by
  intro i
  unfold p09AxisSecondNat
  split
  · unfold p09AxisSecond
    exact p09_stageListSecond_nonneg _ _ hγ
  · exact le_rfl

private lemma p09_run_global_error_norm2 {m : ℕ} [NeZero m]
    (plan : P09MultidimensionalFftPlan m) (model : P09WilkinsonModel)
    (run : P09MultidimensionalFftRun plan model)
    (hγ : 0 ≤ model.gamma) (hu1 : model.epsilon ≤ 1) :
    p09MultiNorm2 (p09MultiFftRoundoffError run) ≤
      ((∑ i : Fin m, p09AxisK (plan.axis i) model.gamma) * model.epsilon +
        p09MultiSecond plan model.gamma * model.epsilon ^ 2) *
        p09MultiNorm2 (p09MultiExactOutput run) := by
  let exactOut : P09MultiArray plan.axis := p09MultiExactOutput run
  let seqArray : ℕ → P09MultiArray plan.axis := fun k ↦
    if hk : k ≤ m then
      p09RunPrefixState (plan := plan) (model := model) run
        ⟨k, Nat.lt_succ_of_le hk⟩
    else exactOut
  let seq : ℕ → EuclideanSpace ℂ (P09MultiIndex plan.axis) := fun k ↦
    WithLp.toLp 2 (seqArray k)
  let K : ℕ → ℝ := p09AxisKNat plan model.gamma
  let C : ℕ → ℝ := p09AxisSecondNat plan model.gamma
  have hu : 0 ≤ model.epsilon := le_of_lt model.epsilon_pos
  have hK : ∀ i, 0 ≤ K i := p09_axisKNat_nonneg plan model.gamma hγ
  have hC : ∀ i, 0 ≤ C i := p09_axisSecondNat_nonneg plan model.gamma hγ
  have hstep : ∀ i, ‖seq i - seq (i + 1)‖ ≤
      (K i * model.epsilon + C i * model.epsilon ^ 2) * ‖seq (i + 1)‖ := by
    intro k
    by_cases hk : k < m
    · let i : Fin m := ⟨k, hk⟩
      have hadj := p09_run_adjacent_error plan model run hγ hu1 i
      simpa [seq, seqArray, K, C, p09AxisKNat, p09AxisSecondNat,
        i, hk, Nat.le_of_lt hk, Nat.succ_le_iff.mpr hk,
        p09MultiNorm2, p09MultiVecSub] using hadj
    · have hmk : m ≤ k := Nat.le_of_not_gt hk
      have hseqk : seqArray k = exactOut := by
        unfold seqArray
        split
        · rename_i hkm
          have heq : k = m := Nat.le_antisymm hkm hmk
          subst k
          change p09ApplyCoordinatePrefix plan.axis m
              (run.computedState ⟨m, _⟩) =
            p09ApplyCoordinatePrefix plan.axis m run.input
          rw [show (⟨m, by omega⟩ : Fin (m + 1)) = Fin.last m by
            apply Fin.ext
            rfl]
          rw [run.computed_input]
        · rfl
      have hseqNext : seqArray (k + 1) = exactOut := by
        have hn : ¬k + 1 ≤ m := by omega
        simp [seqArray, hn]
      simp [seq, hseqk, hseqNext, K, C, p09AxisKNat,
        p09AxisSecondNat, hk]
  have hbound := p09_sequence_error_bound seq K C model.epsilon hu hu1
    hK hC hstep m
  have hseq0 : seq 0 = WithLp.toLp 2 (p09MultiComputedOutput run) := by
    unfold seq seqArray
    rw [dif_pos (Nat.zero_le m)]
    unfold p09RunPrefixState p09MultiComputedOutput
    simp only [p09ApplyCoordinatePrefix]
    rw [show (⟨0, by omega⟩ : Fin (m + 1)) = 0 by
      apply Fin.ext
      rfl]
  have hseqm : seq m = WithLp.toLp 2 exactOut := by
    unfold seq seqArray
    rw [dif_pos le_rfl]
    unfold exactOut p09RunPrefixState p09MultiExactOutput
    congr 2
    rw [show (⟨m, by omega⟩ : Fin (m + 1)) = Fin.last m by
      apply Fin.ext
      rfl]
    exact run.computed_input
  rw [hseq0, hseqm] at hbound
  change p09MultiNorm2 (p09MultiFftRoundoffError run) ≤ _
  change ‖(WithLp.toLp 2 (p09MultiFftRoundoffError run) :
      EuclideanSpace ℂ (P09MultiIndex plan.axis))‖ ≤ _
  simpa [K, C, p09MultiSecond, p09AxisKNat, p09MultiFftRoundoffError,
    p09MultiVecSub, exactOut, p09MultiNorm2] using hbound

theorem p09_t3_multidimensional_rms_error_bound
    {m : ℕ} [NeZero m]
    (plan : P09MultidimensionalFftPlan m) (γ : ℝ)
    (family : P09AsymptoticMultidimensionalFftFamily plan γ)
    (hexactOutput : 0 < p09MultiRms (p09FamilyMultiExactOutput family)) :
    ∃ secondOrderCoeff : ℝ, 0 ≤ secondOrderCoeff ∧
      ∃ radius : ℝ, 0 < radius ∧
        ∀ ε : P09PositiveEpsilon, ε.1 ≤ radius →
          p09MultiRms (p09FamilyMultiFftRoundoffError family ε) /
              p09MultiRms (p09FamilyMultiExactOutput family) ≤
            ε.1 * (∑ i : Fin m, p09AxisK (plan.axis i) γ) +
              secondOrderCoeff * ε.1 ^ 2 := by
  -- PROOF_START P09-T3-H001
  have hKnat : ∀ i, 0 ≤ p09AxisKNat plan γ i :=
    p09_axisKNat_nonneg plan γ family.gamma_nonneg
  have hCnat : ∀ i, 0 ≤ p09AxisSecondNat plan γ i :=
    p09_axisSecondNat_nonneg plan γ family.gamma_nonneg
  have hsecond : 0 ≤ p09MultiSecond plan γ := by
    unfold p09MultiSecond
    exact p09_accumSecond_nonneg _ _ hKnat hCnat m
  refine ⟨p09MultiSecond plan γ, hsecond, 1, by norm_num, ?_⟩
  intro ε hε
  have hγmodel : 0 ≤ (family.model ε).gamma := by
    rw [family.model_gamma ε]
    exact family.gamma_nonneg
  have hu1 : (family.model ε).epsilon ≤ 1 := by
    rw [family.model_epsilon ε]
    exact hε
  have hrun := p09_run_global_error_norm2 plan (family.model ε)
    (family.run ε) hγmodel hu1
  rw [family.model_gamma ε, family.model_epsilon ε] at hrun
  have hexact : p09MultiExactOutput (family.run ε) =
      p09FamilyMultiExactOutput family := by
    unfold p09MultiExactOutput p09FamilyMultiExactOutput
    rw [family.run_input ε]
  have herr : p09MultiFftRoundoffError (family.run ε) =
      p09FamilyMultiFftRoundoffError family ε := by
    unfold p09MultiFftRoundoffError p09FamilyMultiFftRoundoffError
    rw [hexact]
  rw [herr, hexact] at hrun
  have hden : 0 < Real.sqrt (p09MultiCardinality plan.axis : ℝ) :=
    Real.sqrt_pos.2 (Nat.cast_pos.2 (p09_multiCardinality_pos plan.axis))
  have hrms :
      p09MultiRms (p09FamilyMultiFftRoundoffError family ε) ≤
        ((∑ i : Fin m, p09AxisK (plan.axis i) γ) * ε.1 +
          p09MultiSecond plan γ * ε.1 ^ 2) *
          p09MultiRms (p09FamilyMultiExactOutput family) := by
    unfold p09MultiRms
    calc
      p09MultiNorm2 (p09FamilyMultiFftRoundoffError family ε) /
          Real.sqrt (p09MultiCardinality plan.axis : ℝ) ≤
        (((∑ i : Fin m, p09AxisK (plan.axis i) γ) * ε.1 +
            p09MultiSecond plan γ * ε.1 ^ 2) *
          p09MultiNorm2 (p09FamilyMultiExactOutput family)) /
            Real.sqrt (p09MultiCardinality plan.axis : ℝ) := by
          exact div_le_div_of_nonneg_right hrun (le_of_lt hden)
      _ = ((∑ i : Fin m, p09AxisK (plan.axis i) γ) * ε.1 +
            p09MultiSecond plan γ * ε.1 ^ 2) *
          (p09MultiNorm2 (p09FamilyMultiExactOutput family) /
            Real.sqrt (p09MultiCardinality plan.axis : ℝ)) := by ring
  apply (div_le_iff₀ hexactOutput).2
  convert hrms using 1 <;> ring

end HighamBench
