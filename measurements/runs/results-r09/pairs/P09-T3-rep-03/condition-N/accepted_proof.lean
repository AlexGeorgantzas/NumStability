import HighamBench.P09Definitions

namespace HighamBench

open scoped BigOperators

set_option maxHeartbeats 1000000
set_option maxRecDepth 10000

private lemma p09_abs_one_add_mul_mul_one_add_mul_sub_one
    {e a b : ℝ} (he : 0 ≤ e) (ha : |a| ≤ 1) (hb : |b| ≤ 1) :
    |(1 + a * e) * (1 + b * e) - 1| ≤ 2 * e + e ^ 2 := by
  rw [show (1 + a * e) * (1 + b * e) - 1 =
      a * e + b * e + (a * b) * e ^ 2 by ring]
  calc
    |a * e + b * e + (a * b) * e ^ 2|
        ≤ |a * e| + |b * e| + |(a * b) * e ^ 2| := by
          simpa only [add_assoc] using abs_add_three (a * e) (b * e) ((a * b) * e ^ 2)
    _ = |a| * e + |b| * e + (|a| * |b|) * e ^ 2 := by
          simp [abs_mul, abs_of_nonneg he, abs_of_nonneg (sq_nonneg e)]
    _ ≤ 2 * e + e ^ 2 := by
          have hab : |a| * |b| ≤ 1 := by nlinarith [abs_nonneg a, abs_nonneg b]
          nlinarith [sq_nonneg e, mul_le_mul_of_nonneg_right ha he,
            mul_le_mul_of_nonneg_right hb he,
            mul_le_mul_of_nonneg_right hab (sq_nonneg e)]

private lemma p09_complex_component_pair_bound
    {z : ℂ} {A B : ℝ} (hA : 0 ≤ A) (hB : 0 ≤ B)
    (hre : |z.re| ≤ A) (him : |z.im| ≤ B) :
    ‖z‖ ^ 2 ≤ A ^ 2 + B ^ 2 := by
  rw [Complex.sq_norm, Complex.normSq_apply]
  nlinarith [sq_nonneg (A - |z.re|), sq_nonneg (B - |z.im|),
    abs_nonneg z.re, abs_nonneg z.im, sq_abs z.re, sq_abs z.im]

private lemma p09_pair_sum_sq_bound (a b c d : ℝ) :
    (|a * c| + |b * d|) ^ 2 + (|a * d| + |b * c|) ^ 2 ≤
      2 * (a ^ 2 + b ^ 2) * (c ^ 2 + d ^ 2) := by
  have h1 : (|a * c| + |b * d|) ^ 2 ≤
      2 * (|a * c| ^ 2 + |b * d| ^ 2) := by
    nlinarith [sq_nonneg (|a * c| - |b * d|)]
  have h2 : (|a * d| + |b * c|) ^ 2 ≤
      2 * (|a * d| ^ 2 + |b * c| ^ 2) := by
    nlinarith [sq_nonneg (|a * d| - |b * c|)]
  have hac : |a * c| ^ 2 = (a * c) ^ 2 := sq_abs _
  have hbd : |b * d| ^ 2 = (b * d) ^ 2 := sq_abs _
  have had : |a * d| ^ 2 = (a * d) ^ 2 := sq_abs _
  have hbc : |b * c| ^ 2 = (b * c) ^ 2 := sq_abs _
  nlinarith [h1, h2]

private lemma p09RoundedComplexMul_error
    (model : P09WilkinsonModel) (x y : ℂ) :
    ‖p09RoundedComplexMul model x y - x * y‖ ≤
      (3 * model.epsilon + 2 * model.epsilon ^ 2) * ‖x‖ * ‖y‖ := by
  let e := model.epsilon
  have he : 0 ≤ e := le_of_lt model.epsilon_pos
  rcases model.mul_model x.re y.re with ⟨t₁, ht₁, h₁⟩
  rcases model.mul_model x.im y.im with ⟨t₂, ht₂, h₂⟩
  rcases model.mul_model x.re y.im with ⟨t₃, ht₃, h₃⟩
  rcases model.mul_model x.im y.re with ⟨t₄, ht₄, h₄⟩
  rcases model.add_model (model.flMul x.re y.re) (-model.flMul x.im y.im) with
    ⟨u₁, u₂, hu₁, hu₂, ha₁⟩
  rcases model.add_model (model.flMul x.re y.im) (model.flMul x.im y.re) with
    ⟨u₃, u₄, hu₃, hu₄, ha₂⟩
  have hb₁ := p09_abs_one_add_mul_mul_one_add_mul_sub_one he ht₁ hu₁
  have hb₂ := p09_abs_one_add_mul_mul_one_add_mul_sub_one he ht₂ hu₂
  have hb₃ := p09_abs_one_add_mul_mul_one_add_mul_sub_one he ht₃ hu₃
  have hb₄ := p09_abs_one_add_mul_mul_one_add_mul_sub_one he ht₄ hu₄
  let T : ℝ := 2 * e + e ^ 2
  have hT : 0 ≤ T := by dsimp [T]; positivity
  let z := p09RoundedComplexMul model x y - x * y
  have hzre : |z.re| ≤ T * (|x.re * y.re| + |x.im * y.im|) := by
    dsimp [z, p09RoundedComplexMul]
    rw [ha₁, h₁, h₂]
    have hrewrite :
        x.re * y.re * (1 + t₁ * e) * (1 + u₁ * e) +
              -(x.im * y.im * (1 + t₂ * e)) * (1 + u₂ * e) -
            (x.re * y.re - x.im * y.im) =
          x.re * y.re * ((1 + t₁ * e) * (1 + u₁ * e) - 1) -
            x.im * y.im * ((1 + t₂ * e) * (1 + u₂ * e) - 1) := by ring
    rw [hrewrite]
    calc
      |x.re * y.re * ((1 + t₁ * e) * (1 + u₁ * e) - 1) -
          x.im * y.im * ((1 + t₂ * e) * (1 + u₂ * e) - 1)|
          ≤ |x.re * y.re| * |(1 + t₁ * e) * (1 + u₁ * e) - 1| +
              |x.im * y.im| * |(1 + t₂ * e) * (1 + u₂ * e) - 1| := by
                simpa [abs_mul] using
                  (abs_sub
                    (x.re * y.re * ((1 + t₁ * e) * (1 + u₁ * e) - 1))
                    (x.im * y.im * ((1 + t₂ * e) * (1 + u₂ * e) - 1)))
      _ ≤ |x.re * y.re| * T + |x.im * y.im| * T := by gcongr
      _ = T * (|x.re * y.re| + |x.im * y.im|) := by ring
  have hzim : |z.im| ≤ T * (|x.re * y.im| + |x.im * y.re|) := by
    dsimp [z, p09RoundedComplexMul]
    rw [ha₂, h₃, h₄]
    have hrewrite :
        x.re * y.im * (1 + t₃ * e) * (1 + u₃ * e) +
              x.im * y.re * (1 + t₄ * e) * (1 + u₄ * e) -
            (x.re * y.im + x.im * y.re) =
          x.re * y.im * ((1 + t₃ * e) * (1 + u₃ * e) - 1) +
            x.im * y.re * ((1 + t₄ * e) * (1 + u₄ * e) - 1) := by ring
    rw [hrewrite]
    calc
      |x.re * y.im * ((1 + t₃ * e) * (1 + u₃ * e) - 1) +
          x.im * y.re * ((1 + t₄ * e) * (1 + u₄ * e) - 1)|
          ≤ |x.re * y.im| * |(1 + t₃ * e) * (1 + u₃ * e) - 1| +
              |x.im * y.re| * |(1 + t₄ * e) * (1 + u₄ * e) - 1| := by
                simpa [abs_mul] using
                  (abs_add_le
                    (x.re * y.im * ((1 + t₃ * e) * (1 + u₃ * e) - 1))
                    (x.im * y.re * ((1 + t₄ * e) * (1 + u₄ * e) - 1)))
      _ ≤ |x.re * y.im| * T + |x.im * y.re| * T := by gcongr
      _ = T * (|x.re * y.im| + |x.im * y.re|) := by ring
  have hzsq := p09_complex_component_pair_bound
      (mul_nonneg hT (by positivity)) (mul_nonneg hT (by positivity)) hzre hzim
  have hpairs := p09_pair_sum_sq_bound x.re x.im y.re y.im
  have hx : x.re ^ 2 + x.im ^ 2 = ‖x‖ ^ 2 := by
    rw [Complex.sq_norm, Complex.normSq_apply]
    ring
  have hy : y.re ^ 2 + y.im ^ 2 = ‖y‖ ^ 2 := by
    rw [Complex.sq_norm, Complex.normSq_apply]
    ring
  have hsqrt : 0 ≤ Real.sqrt 2 := Real.sqrt_nonneg _
  have hsqrt_sq : (Real.sqrt 2) ^ 2 = 2 := Real.sq_sqrt (by norm_num)
  have hroot_le : 2 * Real.sqrt 2 ≤ 3 := by nlinarith
  have hroot_le' : Real.sqrt 2 ≤ 2 := by nlinarith [hroot_le, hsqrt]
  have hcoef : Real.sqrt 2 * T ≤ 3 * e + 2 * e ^ 2 := by
    dsimp [T]
    nlinarith [mul_le_mul_of_nonneg_right hroot_le he,
      mul_le_mul_of_nonneg_right hroot_le' (sq_nonneg e)]
  have hsq : ‖z‖ ^ 2 ≤
      (Real.sqrt 2 * T * ‖x‖ * ‖y‖) ^ 2 := by
    calc
      ‖z‖ ^ 2 ≤ T ^ 2 *
          ((|x.re * y.re| + |x.im * y.im|) ^ 2 +
            (|x.re * y.im| + |x.im * y.re|) ^ 2) := by
              calc
                ‖z‖ ^ 2 ≤
                    (T * (|x.re * y.re| + |x.im * y.im|)) ^ 2 +
                      (T * (|x.re * y.im| + |x.im * y.re|)) ^ 2 := hzsq
                _ = _ := by ring
      _ ≤ T ^ 2 * (2 * (x.re ^ 2 + x.im ^ 2) *
          (y.re ^ 2 + y.im ^ 2)) :=
            mul_le_mul_of_nonneg_left hpairs (sq_nonneg T)
      _ = (Real.sqrt 2) ^ 2 * T ^ 2 * ‖x‖ ^ 2 * ‖y‖ ^ 2 := by
            rw [hx, hy, hsqrt_sq]
            ring
      _ = (Real.sqrt 2 * T * ‖x‖ * ‖y‖) ^ 2 := by ring
  have hznonneg : 0 ≤ ‖z‖ := norm_nonneg _
  have hrhsnonneg : 0 ≤ Real.sqrt 2 * T * ‖x‖ * ‖y‖ := by positivity
  have hzle : ‖z‖ ≤ Real.sqrt 2 * T * ‖x‖ * ‖y‖ :=
    (sq_le_sq₀ hznonneg hrhsnonneg).mp hsq
  calc
    ‖p09RoundedComplexMul model x y - x * y‖ = ‖z‖ := rfl
    _ ≤ Real.sqrt 2 * T * ‖x‖ * ‖y‖ := hzle
    _ ≤ (3 * e + 2 * e ^ 2) * ‖x‖ * ‖y‖ := by
      gcongr

private lemma p09_complex_l1_le_sqrt_two_norm (z : ℂ) :
    |z.re| + |z.im| ≤ Real.sqrt 2 * ‖z‖ := by
  have hsq : (|z.re| + |z.im|) ^ 2 ≤
      (Real.sqrt 2 * ‖z‖) ^ 2 := by
    have hz := sq_nonneg (|z.re| - |z.im|)
    have hn : z.re ^ 2 + z.im ^ 2 = ‖z‖ ^ 2 := by
      rw [Complex.sq_norm, Complex.normSq_apply]
      ring
    have hs : (Real.sqrt 2) ^ 2 = 2 := Real.sq_sqrt (by norm_num)
    rw [mul_pow, hs, ← hn]
    nlinarith [sq_abs z.re, sq_abs z.im]
  exact (sq_le_sq₀ (by positivity) (by positivity)).mp hsq

private lemma p09_norm_le_l1 (z : ℂ) : ‖z‖ ≤ |z.re| + |z.im| := by
  have hsq : ‖z‖ ^ 2 ≤ (|z.re| + |z.im|) ^ 2 := by
    rw [Complex.sq_norm, Complex.normSq_apply]
    nlinarith [sq_abs z.re, sq_abs z.im,
      mul_nonneg (abs_nonneg z.re) (abs_nonneg z.im)]
  exact (sq_le_sq₀ (norm_nonneg _) (by positivity)).mp hsq

private lemma p09RoundedComplexAdd_error
    (model : P09WilkinsonModel) (x y : ℂ) :
    ‖p09RoundedComplexAdd model x y - (x + y)‖ ≤
      model.epsilon * (‖x‖ + ‖y‖) := by
  rcases model.add_model x.re y.re with ⟨a, b, ha, hb, hre⟩
  rcases model.add_model x.im y.im with ⟨c, d, hc, hd, him⟩
  let e := model.epsilon
  have he : 0 ≤ e := le_of_lt model.epsilon_pos
  let z := p09RoundedComplexAdd model x y - (x + y)
  have hzre : |z.re| ≤ e * (|x.re| + |y.re|) := by
    dsimp [z, p09RoundedComplexAdd]
    rw [hre]
    have heq : x.re * (1 + a * e) + y.re * (1 + b * e) -
        (x.re + y.re) = x.re * a * e + y.re * b * e := by ring
    rw [heq]
    calc
      |x.re * a * e + y.re * b * e|
          ≤ |x.re * a * e| + |y.re * b * e| := abs_add_le _ _
      _ = |x.re| * |a| * e + |y.re| * |b| * e := by
          simp [abs_mul, abs_of_nonneg he]
      _ ≤ e * (|x.re| + |y.re|) := by
          have hxa := mul_le_mul_of_nonneg_left ha (abs_nonneg x.re)
          have hyb := mul_le_mul_of_nonneg_left hb (abs_nonneg y.re)
          nlinarith [mul_le_mul_of_nonneg_right hxa he,
            mul_le_mul_of_nonneg_right hyb he]
  have hzim : |z.im| ≤ e * (|x.im| + |y.im|) := by
    dsimp [z, p09RoundedComplexAdd]
    rw [him]
    have heq : x.im * (1 + c * e) + y.im * (1 + d * e) -
        (x.im + y.im) = x.im * c * e + y.im * d * e := by ring
    rw [heq]
    calc
      |x.im * c * e + y.im * d * e|
          ≤ |x.im * c * e| + |y.im * d * e| := abs_add_le _ _
      _ = |x.im| * |c| * e + |y.im| * |d| * e := by
          simp [abs_mul, abs_of_nonneg he]
      _ ≤ e * (|x.im| + |y.im|) := by
          have hxc := mul_le_mul_of_nonneg_left hc (abs_nonneg x.im)
          have hyd := mul_le_mul_of_nonneg_left hd (abs_nonneg y.im)
          nlinarith [mul_le_mul_of_nonneg_right hxc he,
            mul_le_mul_of_nonneg_right hyd he]
  let zx : ℂ := ⟨x.re * a * e, x.im * c * e⟩
  let zy : ℂ := ⟨y.re * b * e, y.im * d * e⟩
  have hz : z = zx + zy := by
    apply Complex.ext
    · dsimp [z, zx, zy, p09RoundedComplexAdd]
      rw [hre]
      ring
    · dsimp [z, zx, zy, p09RoundedComplexAdd]
      rw [him]
      ring
  have hzx : ‖zx‖ ≤ e * ‖x‖ := by
    have hs : ‖zx‖ ^ 2 ≤ (e * ‖x‖) ^ 2 := by
      rw [Complex.sq_norm, Complex.normSq_apply]
      dsimp [zx]
      have hax : a ^ 2 ≤ 1 := by nlinarith [sq_abs a, abs_nonneg a]
      have hcx : c ^ 2 ≤ 1 := by nlinarith [sq_abs c, abs_nonneg c]
      have hx : x.re ^ 2 + x.im ^ 2 = ‖x‖ ^ 2 := by
        rw [Complex.sq_norm, Complex.normSq_apply]
        ring
      have hr := mul_le_mul_of_nonneg_left hax (sq_nonneg x.re)
      have hi := mul_le_mul_of_nonneg_left hcx (sq_nonneg x.im)
      have hsum : x.re ^ 2 * a ^ 2 + x.im ^ 2 * c ^ 2 ≤
          x.re ^ 2 + x.im ^ 2 := by nlinarith
      have hesum := mul_le_mul_of_nonneg_left hsum (sq_nonneg e)
      nlinarith
    exact (sq_le_sq₀ (norm_nonneg _) (by positivity)).mp hs
  have hzy : ‖zy‖ ≤ e * ‖y‖ := by
    have hs : ‖zy‖ ^ 2 ≤ (e * ‖y‖) ^ 2 := by
      rw [Complex.sq_norm, Complex.normSq_apply]
      dsimp [zy]
      have hbx : b ^ 2 ≤ 1 := by nlinarith [sq_abs b, abs_nonneg b]
      have hdx : d ^ 2 ≤ 1 := by nlinarith [sq_abs d, abs_nonneg d]
      have hy : y.re ^ 2 + y.im ^ 2 = ‖y‖ ^ 2 := by
        rw [Complex.sq_norm, Complex.normSq_apply]
        ring
      have hr := mul_le_mul_of_nonneg_left hbx (sq_nonneg y.re)
      have hi := mul_le_mul_of_nonneg_left hdx (sq_nonneg y.im)
      have hsum : y.re ^ 2 * b ^ 2 + y.im ^ 2 * d ^ 2 ≤
          y.re ^ 2 + y.im ^ 2 := by nlinarith
      have hesum := mul_le_mul_of_nonneg_left hsum (sq_nonneg e)
      nlinarith
    exact (sq_le_sq₀ (norm_nonneg _) (by positivity)).mp hs
  change ‖z‖ ≤ model.epsilon * (‖x‖ + ‖y‖)
  rw [hz]
  calc
    ‖zx + zy‖ ≤ ‖zx‖ + ‖zy‖ := norm_add_le _ _
    _ ≤ e * ‖x‖ + e * ‖y‖ := add_le_add hzx hzy
    _ = model.epsilon * (‖x‖ + ‖y‖) := by dsimp [e]; ring

private lemma p09StdAddChar_eq_cos_sin {q : ℕ} [NeZero q]
    (j : ZMod q) : ZMod.stdAddChar j =
      ⟨Real.cos (p09RootAngle j), Real.sin (p09RootAngle j)⟩ := by
  rw [p09StdAddChar_positive_exp]
  have hq : (q : ℂ) ≠ 0 := by exact_mod_cast (NeZero.ne q)
  rw [show 2 * (Real.pi : ℂ) * Complex.I * (j.val : ℂ) / (q : ℂ) =
      (p09RootAngle j : ℂ) * Complex.I by
        simp only [p09RootAngle]
        push_cast
        field_simp]
  rw [Complex.exp_ofReal_mul_I]
  apply Complex.ext
  · simp only [Complex.add_re, Complex.mul_re, Complex.ofReal_re,
      Complex.ofReal_im, Complex.I_re, Complex.I_im]
    ring
  · simp only [Complex.add_im, Complex.mul_im, Complex.ofReal_re,
      Complex.ofReal_im, Complex.I_re, Complex.I_im]
    ring

private lemma p09StdAddChar_norm {q : ℕ} [NeZero q] (j : ZMod q) :
    ‖ZMod.stdAddChar j‖ = 1 := by
  rw [p09StdAddChar_eq_cos_sin, Complex.norm_def, Complex.normSq_apply]
  have ht := Real.sin_sq_add_cos_sq (p09RootAngle j)
  rw [show Real.cos (p09RootAngle j) * Real.cos (p09RootAngle j) +
      Real.sin (p09RootAngle j) * Real.sin (p09RootAngle j) = 1 by
        nlinarith]
  exact Real.sqrt_one

private lemma p09RoundedRoot_error {q : ℕ} [NeZero q]
    (model : P09WilkinsonModel) (j : ZMod q) :
    ‖p09RoundedRoot model j - ZMod.stdAddChar j‖ ≤
      2 * model.gamma * model.epsilon := by
  rcases model.cos_model (p09RootAngle j) with ⟨a, ha, hcos⟩
  rcases model.sin_model (p09RootAngle j) with ⟨b, hb, hsin⟩
  have he : 0 ≤ model.epsilon := le_of_lt model.epsilon_pos
  have hg : 0 ≤ model.gamma := model.gamma_nonneg
  have hchar := p09StdAddChar_eq_cos_sin j
  rw [hchar]
  apply le_trans (p09_norm_le_l1 _)
  simp only [p09RoundedRoot, Complex.sub_re, Complex.sub_im,
    Complex.ofReal_re, Complex.ofReal_im]
  rw [hcos, hsin]
  have ha' : |model.gamma * a * model.epsilon| ≤
      model.gamma * model.epsilon := by
    rw [abs_mul, abs_mul, abs_of_nonneg hg, abs_of_nonneg he]
    nlinarith [mul_le_mul_of_nonneg_left ha hg,
      mul_le_mul_of_nonneg_right
        (mul_le_mul_of_nonneg_left ha hg) he]
  have hb' : |model.gamma * b * model.epsilon| ≤
      model.gamma * model.epsilon := by
    rw [abs_mul, abs_mul, abs_of_nonneg hg, abs_of_nonneg he]
    nlinarith [mul_le_mul_of_nonneg_left hb hg,
      mul_le_mul_of_nonneg_right
        (mul_le_mul_of_nonneg_left hb hg) he]
  convert (add_le_add ha' hb') using 1 <;> ring

private lemma p09RoundedRoot_norm {q : ℕ} [NeZero q]
    (model : P09WilkinsonModel) (j : ZMod q) :
    ‖p09RoundedRoot model j‖ ≤ 1 + 2 * model.gamma * model.epsilon := by
  calc
    ‖p09RoundedRoot model j‖ ≤
        ‖ZMod.stdAddChar j‖ + ‖p09RoundedRoot model j - ZMod.stdAddChar j‖ := by
      have := norm_add_le (ZMod.stdAddChar j)
        (p09RoundedRoot model j - ZMod.stdAddChar j)
      simpa only [add_sub_cancel] using this
    _ ≤ 1 + 2 * model.gamma * model.epsilon := by
      have hnorm : ‖ZMod.stdAddChar j‖ = 1 := by
        exact p09StdAddChar_norm j
      rw [hnorm]
      nlinarith [p09RoundedRoot_error model j]

private lemma p09RoundedRootMul_error {q : ℕ} [NeZero q]
    (model : P09WilkinsonModel) (j : ZMod q) (x : ℂ)
    (he_one : model.epsilon ≤ 1) :
    ‖p09RoundedComplexMul model (p09RoundedRoot model j) x -
        ZMod.stdAddChar j * x‖ ≤
      ((3 + 2 * model.gamma) * model.epsilon +
        (2 + 10 * model.gamma) * model.epsilon ^ 2) * ‖x‖ := by
  let e := model.epsilon
  let g := model.gamma
  have he : 0 ≤ e := le_of_lt model.epsilon_pos
  have hg : 0 ≤ g := model.gamma_nonneg
  have hm := p09RoundedComplexMul_error model (p09RoundedRoot model j) x
  have hr := p09RoundedRoot_error model j
  have hrn := p09RoundedRoot_norm model j
  calc
    ‖p09RoundedComplexMul model (p09RoundedRoot model j) x -
        ZMod.stdAddChar j * x‖
        ≤ ‖p09RoundedComplexMul model (p09RoundedRoot model j) x -
              p09RoundedRoot model j * x‖ +
            ‖p09RoundedRoot model j * x - ZMod.stdAddChar j * x‖ := by
          rw [show p09RoundedComplexMul model (p09RoundedRoot model j) x -
                ZMod.stdAddChar j * x =
              (p09RoundedComplexMul model (p09RoundedRoot model j) x -
                p09RoundedRoot model j * x) +
              (p09RoundedRoot model j * x - ZMod.stdAddChar j * x) by ring]
          exact norm_add_le _ _
    _ ≤ (3 * e + 2 * e ^ 2) * (1 + 2 * g * e) * ‖x‖ +
          (2 * g * e) * ‖x‖ := by
      apply add_le_add
      · calc
          ‖p09RoundedComplexMul model (p09RoundedRoot model j) x -
              p09RoundedRoot model j * x‖
              ≤ (3 * e + 2 * e ^ 2) *
                  ‖p09RoundedRoot model j‖ * ‖x‖ := hm
          _ ≤ (3 * e + 2 * e ^ 2) * (1 + 2 * g * e) * ‖x‖ := by
            gcongr
      · rw [← sub_mul, norm_mul]
        exact mul_le_mul_of_nonneg_right hr (norm_nonneg x)
    _ ≤ ((3 + 2 * g) * e + (2 + 10 * g) * e ^ 2) * ‖x‖ := by
      have he3 : e ^ 3 ≤ e ^ 2 := by nlinarith [sq_nonneg e]
      have hge3 := mul_le_mul_of_nonneg_left he3 (by positivity : 0 ≤ 4 * g)
      nlinarith [norm_nonneg x,
        mul_le_mul_of_nonneg_right hge3 (norm_nonneg x)]

private lemma p09_flAdd_error (model : P09WilkinsonModel) (a b : ℝ) :
    |model.flAdd a b - (a + b)| ≤
      model.epsilon * (|a| + |b|) := by
  rcases model.add_model a b with ⟨u, v, hu, hv, h⟩
  have he : 0 ≤ model.epsilon := le_of_lt model.epsilon_pos
  rw [h]
  have heq : a * (1 + u * model.epsilon) + b * (1 + v * model.epsilon) -
      (a + b) = a * u * model.epsilon + b * v * model.epsilon := by ring
  rw [heq]
  calc
    |a * u * model.epsilon + b * v * model.epsilon|
        ≤ |a * u * model.epsilon| + |b * v * model.epsilon| := abs_add_le _ _
    _ = |a| * |u| * model.epsilon + |b| * |v| * model.epsilon := by
      simp [abs_mul, abs_of_nonneg he]
    _ ≤ model.epsilon * (|a| + |b|) := by
      have hau := mul_le_mul_of_nonneg_left hu (abs_nonneg a)
      have hbv := mul_le_mul_of_nonneg_left hv (abs_nonneg b)
      nlinarith [mul_le_mul_of_nonneg_right hau he,
        mul_le_mul_of_nonneg_right hbv he]

private lemma p09_recursiveSum_error : ∀ n : ℕ, ∃ D : ℝ, 0 ≤ D ∧
    ∀ (model : P09WilkinsonModel), model.epsilon ≤ 1 →
      ∀ v : Fin n → ℝ,
        |recursiveSum model.flAdd n v - ∑ i, v i| ≤
          (((n - 1 : ℕ) : ℝ) * model.epsilon + D * model.epsilon ^ 2) *
            ∑ i, |v i| := by
  intro n
  induction n with
  | zero =>
      refine ⟨0, by positivity, ?_⟩
      intro model he v
      simp [recursiveSum]
  | succ n ih =>
      by_cases hn : n = 0
      · subst n
        refine ⟨0, by positivity, ?_⟩
        intro model he v
        simp [recursiveSum]
      · rcases ih with ⟨D, hD, ih⟩
        let D' : ℝ := 2 * D + (n - 1 : ℕ)
        refine ⟨D', by dsimp [D']; positivity, ?_⟩
        intro model heone v
        let old : ℝ := recursiveSum model.flAdd n (fun i => v i.castSucc)
        let exactOld : ℝ := ∑ i : Fin n, v i.castSucc
        let last : ℝ := v (Fin.last n)
        have he : 0 ≤ model.epsilon := le_of_lt model.epsilon_pos
        have hold := ih model heone (fun i => v i.castSucc)
        have holdnorm : |old| ≤ |exactOld| + |old - exactOld| := by
          have h := abs_add_le (old - exactOld) exactOld
          rw [sub_add_cancel] at h
          nlinarith [abs_nonneg (old - exactOld), abs_nonneg exactOld]
        have hexactnorm : |exactOld| ≤ ∑ i : Fin n, |v i.castSucc| := by
          exact Finset.abs_sum_le_sum_abs _ _
        have hadd := p09_flAdd_error model old last
        have hsum : (∑ i : Fin (n + 1), v i) = exactOld + last := by
          exact Fin.sum_univ_castSucc v
        have habssum : (∑ i : Fin (n + 1), |v i|) =
            (∑ i : Fin n, |v i.castSucc|) + |last| := by
          exact Fin.sum_univ_castSucc (fun i => |v i|)
        simp only [recursiveSum, hn, dite_false]
        rw [hsum, habssum]
        have hsplit :
            |model.flAdd old last - (exactOld + last)| ≤
              |model.flAdd old last - (old + last)| + |old - exactOld| := by
          calc
            |model.flAdd old last - (exactOld + last)| =
                |(model.flAdd old last - (old + last)) + (old - exactOld)| := by
                  congr 1
                  ring
            _ ≤ _ := abs_add_le _ _
        calc
          |model.flAdd old last - (exactOld + last)|
              ≤ |model.flAdd old last - (old + last)| + |old - exactOld| := hsplit
          _ ≤ model.epsilon * (|old| + |last|) + |old - exactOld| := by
            gcongr
          _ ≤ model.epsilon *
                ((∑ i : Fin n, |v i.castSucc|) + |old - exactOld| + |last|) +
              |old - exactOld| := by
            gcongr
            nlinarith
          _ ≤ ((((n : ℕ) : ℝ) * model.epsilon + D' * model.epsilon ^ 2) *
                ((∑ i : Fin n, |v i.castSucc|) + |last|)) := by
            have hsnonneg : 0 ≤ ∑ i : Fin n, |v i.castSucc| := by positivity
            have hlast : 0 ≤ |last| := abs_nonneg _
            have hDpart : D * model.epsilon ^ 3 ≤ D * model.epsilon ^ 2 := by
              have he3 : model.epsilon ^ 3 ≤ model.epsilon ^ 2 := by
                nlinarith [sq_nonneg model.epsilon]
              exact mul_le_mul_of_nonneg_left he3 hD
            have hncast : ((n - 1 : ℕ) : ℝ) + 1 = (n : ℝ) := by
              exact_mod_cast Nat.sub_add_cancel (Nat.one_le_iff_ne_zero.mpr hn)
            have hcoef :
                (1 + model.epsilon) *
                    (((n - 1 : ℕ) : ℝ) * model.epsilon +
                      D * model.epsilon ^ 2) ≤
                  ((n - 1 : ℕ) : ℝ) * model.epsilon +
                    (2 * D + (n - 1 : ℕ)) * model.epsilon ^ 2 := by
              nlinarith
            have hE := mul_le_mul_of_nonneg_left hold
              (by positivity : 0 ≤ 1 + model.epsilon)
            have hES := mul_le_mul_of_nonneg_right hcoef hsnonneg
            have hn1 : (1 : ℝ) ≤ n := by exact_mod_cast (Nat.one_le_iff_ne_zero.mpr hn)
            have hmaincoef : model.epsilon ≤
                (n : ℝ) * model.epsilon +
                  (2 * D + (n - 1 : ℕ)) * model.epsilon ^ 2 := by
              nlinarith [mul_nonneg hD (sq_nonneg model.epsilon),
                mul_nonneg (by positivity : 0 ≤ ((n - 1 : ℕ) : ℝ))
                  (sq_nonneg model.epsilon)]
            dsimp [D']
            push_cast
            have hL := mul_le_mul_of_nonneg_right hmaincoef hlast
            have hOldTerm :
                (1 + model.epsilon) * |old - exactOld| ≤
                  (((n - 1 : ℕ) : ℝ) * model.epsilon +
                    (2 * D + (n - 1 : ℕ)) * model.epsilon ^ 2) *
                      (∑ i : Fin n, |v i.castSucc|) := by
              exact le_trans hE (by simpa [mul_assoc] using hES)
            calc
              model.epsilon *
                    ((∑ i : Fin n, |v i.castSucc|) + |old - exactOld| + |last|) +
                  |old - exactOld| =
                model.epsilon * (∑ i : Fin n, |v i.castSucc|) +
                  (1 + model.epsilon) * |old - exactOld| +
                  model.epsilon * |last| := by ring
              _ ≤ model.epsilon * (∑ i : Fin n, |v i.castSucc|) +
                  (((n - 1 : ℕ) : ℝ) * model.epsilon +
                    (2 * D + (n - 1 : ℕ)) * model.epsilon ^ 2) *
                      (∑ i : Fin n, |v i.castSucc|) +
                  model.epsilon * |last| := by gcongr
              _ ≤ model.epsilon * (∑ i : Fin n, |v i.castSucc|) +
                  (((n - 1 : ℕ) : ℝ) * model.epsilon +
                    (2 * D + (n - 1 : ℕ)) * model.epsilon ^ 2) *
                      (∑ i : Fin n, |v i.castSucc|) +
                  ((n : ℝ) * model.epsilon +
                    (2 * D + (n - 1 : ℕ)) * model.epsilon ^ 2) * |last| := by
                gcongr
              _ = ((n : ℝ) * model.epsilon +
                    (2 * D + (n - 1 : ℕ)) * model.epsilon ^ 2) *
                    ((∑ i : Fin n, |v i.castSucc|) + |last|) := by
                rw [← hncast]
                ring

private lemma p09RoundedComplexSum_error {q : ℕ} [NeZero q] :
    ∃ D : ℝ, 0 ≤ D ∧ ∀ (model : P09WilkinsonModel), model.epsilon ≤ 1 →
      ∀ term : ZMod q → ℂ,
        ‖p09RoundedComplexSum model term - ∑ j, term j‖ ≤
          (Real.sqrt 2 * ((q - 1 : ℕ) : ℝ) * model.epsilon +
              D * model.epsilon ^ 2) * ∑ j, ‖term j‖ := by
  rcases p09_recursiveSum_error q with ⟨D, hD, hrec⟩
  refine ⟨Real.sqrt 2 * D, by positivity, ?_⟩
  intro model heone term
  let index : Fin q ≃ ZMod q := (ZMod.finEquiv q).toEquiv
  let exact : ℂ := ∑ j : ZMod q, term j
  let rounded : ℂ := p09RoundedComplexSum model term
  have hre := hrec model heone (fun i : Fin q => (term (index i)).re)
  have him := hrec model heone (fun i : Fin q => (term (index i)).im)
  have hsumre : (∑ i : Fin q, (term (index i)).re) = exact.re := by
    dsimp [exact]
    calc
      (∑ i : Fin q, (term (index i)).re) =
          ∑ j : ZMod q, (term j).re := by
            exact Fintype.sum_equiv index _ _ (fun i => rfl)
      _ = (∑ j : ZMod q, term j).re := by simp
  have hsumim : (∑ i : Fin q, (term (index i)).im) = exact.im := by
    dsimp [exact]
    calc
      (∑ i : Fin q, (term (index i)).im) =
          ∑ j : ZMod q, (term j).im := by
            exact Fintype.sum_equiv index _ _ (fun i => rfl)
      _ = (∑ j : ZMod q, term j).im := by simp
  have hroundre : rounded.re =
      recursiveSum model.flAdd q (fun i : Fin q => (term (index i)).re) := by
    rfl
  have hroundim : rounded.im =
      recursiveSum model.flAdd q (fun i : Fin q => (term (index i)).im) := by
    rfl
  rw [hsumre, ← hroundre] at hre
  rw [hsumim, ← hroundim] at him
  let C : ℝ := ((q - 1 : ℕ) : ℝ) * model.epsilon + D * model.epsilon ^ 2
  have hC : 0 ≤ C := by
    dsimp [C]
    exact add_nonneg
      (mul_nonneg (Nat.cast_nonneg _) (le_of_lt model.epsilon_pos))
      (mul_nonneg hD (sq_nonneg _))
  have hrealimag :
      (∑ i : Fin q, |(term (index i)).re|) +
          (∑ i : Fin q, |(term (index i)).im|) ≤
        Real.sqrt 2 * ∑ j : ZMod q, ‖term j‖ := by
    calc
      (∑ i : Fin q, |(term (index i)).re|) +
          (∑ i : Fin q, |(term (index i)).im|) =
          ∑ i : Fin q, (|(term (index i)).re| + |(term (index i)).im|) := by
            rw [Finset.sum_add_distrib]
      _ ≤ ∑ i : Fin q, Real.sqrt 2 * ‖term (index i)‖ := by
            gcongr with i
            exact p09_complex_l1_le_sqrt_two_norm _
      _ = Real.sqrt 2 * ∑ j : ZMod q, ‖term j‖ := by
            rw [Finset.mul_sum]
            exact Fintype.sum_equiv index
              (fun i : Fin q => Real.sqrt 2 * ‖term (index i)‖)
              (fun j : ZMod q => Real.sqrt 2 * ‖term j‖) (fun i => rfl)
  calc
    ‖p09RoundedComplexSum model term - ∑ j, term j‖ = ‖rounded - exact‖ := rfl
    _ ≤ |(rounded - exact).re| + |(rounded - exact).im| := p09_norm_le_l1 _
    _ ≤ C * ((∑ i : Fin q, |(term (index i)).re|) +
          (∑ i : Fin q, |(term (index i)).im|)) := by
            dsimp [C]
            nlinarith
    _ ≤ C * (Real.sqrt 2 * ∑ j : ZMod q, ‖term j‖) := by gcongr
    _ = (Real.sqrt 2 * ((q - 1 : ℕ) : ℝ) * model.epsilon +
              (Real.sqrt 2 * D) * model.epsilon ^ 2) *
            ∑ j : ZMod q, ‖term j‖ := by
          dsimp [C]
          ring

private lemma p09RoundedGenericRadixBlock_error {q : ℕ} [NeZero q]
    (γ : ℝ) (hγ : 0 ≤ γ) (hq3 : 3 ≤ q) : ∃ D : ℝ, 0 ≤ D ∧
      ∀ (model : P09WilkinsonModel), model.gamma = γ → model.epsilon ≤ 1 →
        ∀ (x : ZMod q → ℂ) (k : ZMod q),
          ‖p09RoundedGenericRadixBlock model x k -
              ∑ j : ZMod q, ZMod.stdAddChar (j * k) * x j‖ ≤
            (2 * ((q : ℝ) + model.gamma) * model.epsilon +
                D * model.epsilon ^ 2) * ∑ j : ZMod q, ‖x j‖ := by
  rcases p09RoundedComplexSum_error (q := q) with ⟨B, hB, hsum⟩
  let A : ℝ := Real.sqrt 2 * ((q - 1 : ℕ) : ℝ)
  let C : ℝ := 3 + 2 * γ
  let E : ℝ := 2 + 10 * γ
  let D : ℝ := B + A * C + A * E + B * C + B * E + E
  refine ⟨D, by dsimp [D, A, C, E]; positivity, ?_⟩
  intro model hmodelgamma heone x k
  have he : 0 ≤ model.epsilon := le_of_lt model.epsilon_pos
  have hroot (j : ZMod q) := p09RoundedRootMul_error model (j * k) (x j) heone
  have happrox (j : ZMod q) :
      ‖p09RoundedComplexMul model (p09RoundedRoot model (j * k)) (x j)‖ ≤
        (1 + C * model.epsilon + E * model.epsilon ^ 2) * ‖x j‖ := by
    calc
      ‖p09RoundedComplexMul model (p09RoundedRoot model (j * k)) (x j)‖ ≤
          ‖ZMod.stdAddChar (j * k) * x j‖ +
            ‖p09RoundedComplexMul model (p09RoundedRoot model (j * k)) (x j) -
              ZMod.stdAddChar (j * k) * x j‖ := by
            have ht := norm_add_le (ZMod.stdAddChar (j * k) * x j)
              (p09RoundedComplexMul model (p09RoundedRoot model (j * k)) (x j) -
                ZMod.stdAddChar (j * k) * x j)
            simpa only [add_sub_cancel] using ht
      _ ≤ ‖x j‖ + (C * model.epsilon + E * model.epsilon ^ 2) * ‖x j‖ := by
            rw [norm_mul, p09StdAddChar_norm, one_mul]
            simpa [C, E, hmodelgamma] using add_le_add_left (hroot j) ‖x j‖
      _ = (1 + C * model.epsilon + E * model.epsilon ^ 2) * ‖x j‖ := by ring
  have hsumnorm :
      (∑ j : ZMod q,
          ‖p09RoundedComplexMul model (p09RoundedRoot model (j * k)) (x j)‖) ≤
        (1 + C * model.epsilon + E * model.epsilon ^ 2) *
          ∑ j : ZMod q, ‖x j‖ := by
    calc
      _ ≤ ∑ j : ZMod q,
          (1 + C * model.epsilon + E * model.epsilon ^ 2) * ‖x j‖ := by
            gcongr with j
            exact happrox j
      _ = _ := by rw [Finset.mul_sum]
  have hsumround := hsum model heone
      (fun j : ZMod q =>
        p09RoundedComplexMul model (p09RoundedRoot model (j * k)) (x j))
  have hterms :
      ‖(∑ j : ZMod q,
          p09RoundedComplexMul model (p09RoundedRoot model (j * k)) (x j)) -
          ∑ j : ZMod q, ZMod.stdAddChar (j * k) * x j‖ ≤
        (C * model.epsilon + E * model.epsilon ^ 2) *
          ∑ j : ZMod q, ‖x j‖ := by
    calc
      _ = ‖∑ j : ZMod q,
          (p09RoundedComplexMul model (p09RoundedRoot model (j * k)) (x j) -
            ZMod.stdAddChar (j * k) * x j)‖ := by rw [Finset.sum_sub_distrib]
      _ ≤ ∑ j : ZMod q,
          ‖p09RoundedComplexMul model (p09RoundedRoot model (j * k)) (x j) -
            ZMod.stdAddChar (j * k) * x j‖ := norm_sum_le _ _
      _ ≤ ∑ j : ZMod q,
          (C * model.epsilon + E * model.epsilon ^ 2) * ‖x j‖ := by
            gcongr with j
            simpa [C, E, hmodelgamma] using hroot j
      _ = _ := by rw [Finset.mul_sum]
  have hsqrt : 0 ≤ Real.sqrt 2 := Real.sqrt_nonneg _
  have hsqrt_sq : (Real.sqrt 2) ^ 2 = 2 := Real.sq_sqrt (by norm_num)
  have hsqrt_le : Real.sqrt 2 ≤ 3 / 2 := by nlinarith
  have hAfirst : A + C ≤ 2 * ((q : ℝ) + γ) := by
    have hqcast : (3 : ℝ) ≤ q := by exact_mod_cast hq3
    have hsub : ((q - 1 : ℕ) : ℝ) = (q : ℝ) - 1 := by
      rw [Nat.cast_sub (by omega : 1 ≤ q)]
      norm_num
    dsimp [A, C]
    rw [hsub]
    have hqm1 : 0 ≤ (q : ℝ) - 1 := by nlinarith
    nlinarith [mul_le_mul_of_nonneg_right hsqrt_le hqm1]
  have hprod :
      (A * model.epsilon + B * model.epsilon ^ 2) *
          (1 + C * model.epsilon + E * model.epsilon ^ 2) +
          (C * model.epsilon + E * model.epsilon ^ 2) ≤
        (A + C) * model.epsilon + D * model.epsilon ^ 2 := by
    have he3 : model.epsilon ^ 3 ≤ model.epsilon ^ 2 := by
      nlinarith [sq_nonneg model.epsilon]
    have he4 : model.epsilon ^ 4 ≤ model.epsilon ^ 2 := by
      nlinarith [sq_nonneg model.epsilon, sq_nonneg (model.epsilon ^ 2 - model.epsilon)]
    have hAC := mul_le_mul_of_nonneg_left he3 (by positivity : 0 ≤ A * C)
    have hAE := mul_le_mul_of_nonneg_left he3 (by positivity : 0 ≤ A * E)
    have hBC := mul_le_mul_of_nonneg_left he3 (by positivity : 0 ≤ B * C)
    have hBE := mul_le_mul_of_nonneg_left he4 (by positivity : 0 ≤ B * E)
    dsimp [D]
    nlinarith
  rw [p09RoundedGenericRadixBlock]
  let approx : ZMod q → ℂ := fun j =>
    p09RoundedComplexMul model (p09RoundedRoot model (j * k)) (x j)
  calc
    ‖p09RoundedComplexSum model approx -
        ∑ j : ZMod q, ZMod.stdAddChar (j * k) * x j‖ ≤
      ‖p09RoundedComplexSum model approx - ∑ j, approx j‖ +
        ‖(∑ j, approx j) - ∑ j, ZMod.stdAddChar (j * k) * x j‖ := by
          rw [show p09RoundedComplexSum model approx -
                ∑ j : ZMod q, ZMod.stdAddChar (j * k) * x j =
              (p09RoundedComplexSum model approx - ∑ j, approx j) +
                ((∑ j, approx j) -
                  ∑ j, ZMod.stdAddChar (j * k) * x j) by ring]
          exact norm_add_le _ _
    _ ≤ (A * model.epsilon + B * model.epsilon ^ 2) *
          ((1 + C * model.epsilon + E * model.epsilon ^ 2) *
            ∑ j : ZMod q, ‖x j‖) +
          (C * model.epsilon + E * model.epsilon ^ 2) *
            ∑ j : ZMod q, ‖x j‖ := by
          apply add_le_add
          · calc
              ‖p09RoundedComplexSum model approx - ∑ j, approx j‖ ≤
                  (A * model.epsilon + B * model.epsilon ^ 2) *
                    ∑ j, ‖approx j‖ := by
                      simpa [A, approx] using hsumround
              _ ≤ _ := by gcongr
          · simpa [approx] using hterms
    _ = ((A * model.epsilon + B * model.epsilon ^ 2) *
          (1 + C * model.epsilon + E * model.epsilon ^ 2) +
          (C * model.epsilon + E * model.epsilon ^ 2)) *
            ∑ j : ZMod q, ‖x j‖ := by ring
    _ ≤ ((A + C) * model.epsilon + D * model.epsilon ^ 2) *
            ∑ j : ZMod q, ‖x j‖ := by gcongr
    _ ≤ (2 * ((q : ℝ) + model.gamma) * model.epsilon +
              D * model.epsilon ^ 2) * ∑ j : ZMod q, ‖x j‖ := by
          rw [hmodelgamma]
          gcongr

private lemma p09RadixTwoCoefficient_eq_char (j : ZMod 2) (x : ℂ) :
    p09RadixTwoCoefficientApply j x = ZMod.stdAddChar j * x := by
  fin_cases j
  · change p09RadixTwoCoefficientApply (0 : ZMod 2) x =
        ZMod.stdAddChar (0 : ZMod 2) * x
    rw [p09StdAddChar_eq_cos_sin]
    simp only [p09RadixTwoCoefficientApply, if_pos rfl, p09RootAngle,
      ZMod.val_zero, Nat.cast_zero, mul_zero, zero_div, Real.cos_zero,
      Real.sin_zero]
    apply Complex.ext <;> simp
  · have hang : p09RootAngle (1 : ZMod 2) = Real.pi := by
      change 2 * Real.pi * (((1 : ZMod 2).val : ℕ) : ℝ) / (2 : ℝ) = Real.pi
      have hv : (1 : ZMod 2).val = 1 := by decide
      rw [hv]
      norm_num
    change p09RadixTwoCoefficientApply (1 : ZMod 2) x =
      ZMod.stdAddChar (1 : ZMod 2) * x
    rw [p09StdAddChar_eq_cos_sin, hang]
    have hne : (1 : ZMod 2) ≠ 0 := by decide
    simp only [p09RadixTwoCoefficientApply, if_neg hne, Real.cos_pi,
      Real.sin_pi]
    apply Complex.ext <;> simp

private lemma p09RadixTwoCoefficient_norm (j : ZMod 2) (x : ℂ) :
    ‖p09RadixTwoCoefficientApply j x‖ = ‖x‖ := by
  rw [p09RadixTwoCoefficient_eq_char, norm_mul, p09StdAddChar_norm, one_mul]

private lemma p09RoundedRadixTwoBlock_pointwise
    (model : P09WilkinsonModel) (x : ZMod 2 → ℂ) (k : ZMod 2) :
    ‖p09RoundedRadixTwoBlock model x k -
        ∑ j : ZMod 2, ZMod.stdAddChar (j * k) * x j‖ ≤
      model.epsilon * (‖x 0‖ + ‖x 1‖) := by
  let e : Fin 2 ≃ ZMod 2 := (ZMod.finEquiv 2).toEquiv
  have hrounded : p09RoundedRadixTwoBlock model x k =
      p09RoundedComplexAdd model
        (p09RadixTwoCoefficientApply (0 * k) (x 0))
        (p09RadixTwoCoefficientApply (1 * k) (x 1)) := by
    simp [p09RoundedRadixTwoBlock, p09RoundedComplexSum, recursiveSum,
      p09RoundedComplexAdd]
  have hexact : (∑ j : ZMod 2, ZMod.stdAddChar (j * k) * x j) =
      p09RadixTwoCoefficientApply (0 * k) (x 0) +
        p09RadixTwoCoefficientApply (1 * k) (x 1) := by
    rw [← Equiv.sum_comp e
      (fun j : ZMod 2 => ZMod.stdAddChar (j * k) * x j), Fin.sum_univ_two]
    rw [← p09RadixTwoCoefficient_eq_char, ← p09RadixTwoCoefficient_eq_char]
    change p09RadixTwoCoefficientApply (0 * k) (x 0) +
      p09RadixTwoCoefficientApply (1 * k) (x 1) = _
    rfl
  rw [hrounded, hexact]
  simpa [p09RadixTwoCoefficient_norm] using
    p09RoundedComplexAdd_error model
      (p09RadixTwoCoefficientApply (0 * k) (x 0))
      (p09RadixTwoCoefficientApply (1 * k) (x 1))

private lemma p09RoundedRadixTwoBlock_l2
    (model : P09WilkinsonModel) (x : ZMod 2 → ℂ) :
    p09ComplexNorm2 (fun k => p09RoundedRadixTwoBlock model x k -
        ∑ j : ZMod 2, ZMod.stdAddChar (j * k) * x j) ≤
      2 * model.epsilon * p09ComplexNorm2 x := by
  let e : Fin 2 ≃ ZMod 2 := (ZMod.finEquiv 2).toEquiv
  let err : ZMod 2 → ℂ := fun k => p09RoundedRadixTwoBlock model x k -
    ∑ j : ZMod 2, ZMod.stdAddChar (j * k) * x j
  have he : 0 ≤ model.epsilon := le_of_lt model.epsilon_pos
  have hpoint (k : ZMod 2) := p09RoundedRadixTwoBlock_pointwise model x k
  have herrsq : (∑ k : ZMod 2, ‖err k‖ ^ 2) ≤
      2 * model.epsilon ^ 2 * (‖x 0‖ + ‖x 1‖) ^ 2 := by
    rw [← Equiv.sum_comp e (fun k : ZMod 2 => ‖err k‖ ^ 2), Fin.sum_univ_two]
    change ‖err 0‖ ^ 2 + ‖err 1‖ ^ 2 ≤ _
    have h0 := (pow_le_pow_left₀ (norm_nonneg _) (hpoint 0) 2)
    have h1 := (pow_le_pow_left₀ (norm_nonneg _) (hpoint 1) 2)
    nlinarith [sq_nonneg (model.epsilon * (‖x 0‖ + ‖x 1‖))]
  have hxsum : (‖x 0‖ + ‖x 1‖) ^ 2 ≤
      2 * (∑ j : ZMod 2, ‖x j‖ ^ 2) := by
    rw [← Equiv.sum_comp e (fun j : ZMod 2 => ‖x j‖ ^ 2), Fin.sum_univ_two]
    change (‖x 0‖ + ‖x 1‖) ^ 2 ≤ 2 * (‖x 0‖ ^ 2 + ‖x 1‖ ^ 2)
    nlinarith [sq_nonneg (‖x 0‖ - ‖x 1‖)]
  have hsq : (∑ k : ZMod 2, ‖err k‖ ^ 2) ≤
      (2 * model.epsilon * p09ComplexNorm2 x) ^ 2 := by
    have hmul := mul_le_mul_of_nonneg_left hxsum
      (by positivity : 0 ≤ 2 * model.epsilon ^ 2)
    rw [p09ComplexNorm2, p09ComplexNorm2Sq]
    have hsumx : 0 ≤ ∑ j : ZMod 2, ‖x j‖ ^ 2 := by positivity
    calc
      (∑ k : ZMod 2, ‖err k‖ ^ 2) ≤
          2 * model.epsilon ^ 2 * (2 * ∑ j : ZMod 2, ‖x j‖ ^ 2) :=
            le_trans herrsq hmul
      _ = 4 * model.epsilon ^ 2 *
          (Real.sqrt (∑ j : ZMod 2, ‖x j‖ ^ 2)) ^ 2 := by
            rw [Real.sq_sqrt hsumx]
            ring
      _ = (2 * model.epsilon *
          Real.sqrt (∑ j : ZMod 2, ‖x j‖ ^ 2)) ^ 2 := by ring
  rw [p09ComplexNorm2, p09ComplexNorm2Sq]
  change Real.sqrt (∑ k : ZMod 2, ‖err k‖ ^ 2) ≤
    2 * model.epsilon * Real.sqrt (∑ j : ZMod 2, ‖x j‖ ^ 2)
  have herrnonneg : 0 ≤ ∑ k : ZMod 2, ‖err k‖ ^ 2 := by positivity
  have hsqrt_sq := Real.sq_sqrt herrnonneg
  have hrhs : 0 ≤ 2 * model.epsilon *
      Real.sqrt (∑ j : ZMod 2, ‖x j‖ ^ 2) := by positivity
  apply (sq_le_sq₀ (Real.sqrt_nonneg _) hrhs).mp
  rw [Real.sq_sqrt herrnonneg]
  exact hsq

private lemma p09RadixFourCoefficient_eq_char (j : ZMod 4) (x : ℂ) :
    p09RadixFourCoefficientApply j x = ZMod.stdAddChar j * x := by
  fin_cases j
  · change p09RadixFourCoefficientApply (0 : ZMod 4) x =
      ZMod.stdAddChar (0 : ZMod 4) * x
    rw [p09StdAddChar_eq_cos_sin]
    simp only [p09RadixFourCoefficientApply, if_pos rfl, p09RootAngle,
      ZMod.val_zero, Nat.cast_zero, mul_zero, zero_div, Real.cos_zero,
      Real.sin_zero]
    apply Complex.ext <;> simp
  · have hang : p09RootAngle (1 : ZMod 4) = Real.pi / 2 := by
      change 2 * Real.pi * (((1 : ZMod 4).val : ℕ) : ℝ) / (4 : ℝ) = _
      have hv : (1 : ZMod 4).val = 1 := by decide
      rw [hv]
      norm_num
      ring
    change p09RadixFourCoefficientApply (1 : ZMod 4) x =
      ZMod.stdAddChar (1 : ZMod 4) * x
    rw [p09StdAddChar_eq_cos_sin, hang]
    have h10 : (1 : ZMod 4) ≠ 0 := by decide
    simp only [p09RadixFourCoefficientApply, if_neg h10, if_pos rfl,
      Real.cos_pi_div_two, Real.sin_pi_div_two]
    apply Complex.ext <;> simp
  · have hang : p09RootAngle (2 : ZMod 4) = Real.pi := by
      change 2 * Real.pi * (((2 : ZMod 4).val : ℕ) : ℝ) / (4 : ℝ) = _
      have hv : (2 : ZMod 4).val = 2 := by decide
      rw [hv]
      norm_num
      ring
    change p09RadixFourCoefficientApply (2 : ZMod 4) x =
      ZMod.stdAddChar (2 : ZMod 4) * x
    rw [p09StdAddChar_eq_cos_sin, hang]
    have h20 : (2 : ZMod 4) ≠ 0 := by decide
    have h21 : (2 : ZMod 4) ≠ 1 := by decide
    simp only [p09RadixFourCoefficientApply, if_neg h20, if_neg h21,
      if_pos rfl, Real.cos_pi, Real.sin_pi]
    apply Complex.ext <;> simp
  · have hang : p09RootAngle (3 : ZMod 4) = Real.pi + Real.pi / 2 := by
      change 2 * Real.pi * (((3 : ZMod 4).val : ℕ) : ℝ) / (4 : ℝ) = _
      have hv : (3 : ZMod 4).val = 3 := by decide
      rw [hv]
      ring
    change p09RadixFourCoefficientApply (3 : ZMod 4) x =
      ZMod.stdAddChar (3 : ZMod 4) * x
    rw [p09StdAddChar_eq_cos_sin, hang, Real.cos_add, Real.sin_add,
      Real.cos_pi, Real.sin_pi, Real.cos_pi_div_two, Real.sin_pi_div_two]
    have h30 : (3 : ZMod 4) ≠ 0 := by decide
    have h31 : (3 : ZMod 4) ≠ 1 := by decide
    have h32 : (3 : ZMod 4) ≠ 2 := by decide
    simp only [p09RadixFourCoefficientApply, if_neg h30, if_neg h31,
      if_neg h32]
    apply Complex.ext <;> simp <;> ring

private lemma p09RadixFourCoefficient_norm (j : ZMod 4) (x : ℂ) :
    ‖p09RadixFourCoefficientApply j x‖ = ‖x‖ := by
  rw [p09RadixFourCoefficient_eq_char, norm_mul, p09StdAddChar_norm, one_mul]

private lemma p09RoundedRadixFourBlock_pointwise
    (model : P09WilkinsonModel) (x : ZMod 4 → ℂ) (k : ZMod 4) :
    ‖p09RoundedRadixFourBlock model x k -
        ∑ j : ZMod 4, ZMod.stdAddChar (j * k) * x j‖ ≤
      (2 * model.epsilon + model.epsilon ^ 2) * ∑ j : ZMod 4, ‖x j‖ := by
  let t : Fin 4 → ℂ := fun i =>
    p09RadixFourCoefficientApply (((ZMod.finEquiv 4).toEquiv i) * k)
      (x ((ZMod.finEquiv 4).toEquiv i))
  let a := p09RoundedComplexAdd model (t 0) (t 1)
  let b := p09RoundedComplexAdd model (t 2) (t 3)
  have hea := p09RoundedComplexAdd_error model (t 0) (t 1)
  have heb := p09RoundedComplexAdd_error model (t 2) (t 3)
  have ha : ‖a‖ ≤ (1 + model.epsilon) * (‖t 0‖ + ‖t 1‖) := by
    calc
      ‖a‖ ≤ ‖t 0 + t 1‖ + ‖a - (t 0 + t 1)‖ := by
        have h := norm_add_le (t 0 + t 1) (a - (t 0 + t 1))
        simpa only [add_sub_cancel] using h
      _ ≤ (‖t 0‖ + ‖t 1‖) +
          model.epsilon * (‖t 0‖ + ‖t 1‖) := by
            gcongr
            exact norm_add_le _ _
      _ = _ := by ring
  have hb : ‖b‖ ≤ (1 + model.epsilon) * (‖t 2‖ + ‖t 3‖) := by
    calc
      ‖b‖ ≤ ‖t 2 + t 3‖ + ‖b - (t 2 + t 3)‖ := by
        have h := norm_add_le (t 2 + t 3) (b - (t 2 + t 3))
        simpa only [add_sub_cancel] using h
      _ ≤ (‖t 2‖ + ‖t 3‖) +
          model.epsilon * (‖t 2‖ + ‖t 3‖) := by
            gcongr
            exact norm_add_le _ _
      _ = _ := by ring
  have hout := p09RoundedComplexAdd_error model a b
  have hrounded : p09RoundedRadixFourBlock model x k =
      p09RoundedComplexAdd model a b := by rfl
  have hexact : (∑ j : ZMod 4, ZMod.stdAddChar (j * k) * x j) =
      (t 0 + t 1) + (t 2 + t 3) := by
    rw [← Equiv.sum_comp (ZMod.finEquiv 4).toEquiv
      (fun j : ZMod 4 => ZMod.stdAddChar (j * k) * x j), Fin.sum_univ_four]
    simp only [t]
    rw [← p09RadixFourCoefficient_eq_char, ← p09RadixFourCoefficient_eq_char,
      ← p09RadixFourCoefficient_eq_char, ← p09RadixFourCoefficient_eq_char]
    abel
  have hsplit :
      ‖p09RoundedComplexAdd model a b - ((t 0 + t 1) + (t 2 + t 3))‖ ≤
        ‖p09RoundedComplexAdd model a b - (a + b)‖ +
          ‖a - (t 0 + t 1)‖ + ‖b - (t 2 + t 3)‖ := by
    rw [show p09RoundedComplexAdd model a b - ((t 0 + t 1) + (t 2 + t 3)) =
        (p09RoundedComplexAdd model a b - (a + b)) +
          ((a - (t 0 + t 1)) + (b - (t 2 + t 3))) by ring]
    calc
      _ ≤ ‖p09RoundedComplexAdd model a b - (a + b)‖ +
          ‖(a - (t 0 + t 1)) + (b - (t 2 + t 3))‖ := norm_add_le _ _
      _ ≤ ‖p09RoundedComplexAdd model a b - (a + b)‖ +
          (‖a - (t 0 + t 1)‖ + ‖b - (t 2 + t 3)‖) := by
            gcongr
            exact norm_add_le _ _
      _ = _ := by ring
  rw [hrounded, hexact]
  calc
    _ ≤ ‖p09RoundedComplexAdd model a b - (a + b)‖ +
          ‖a - (t 0 + t 1)‖ + ‖b - (t 2 + t 3)‖ := hsplit
    _ ≤ model.epsilon * (‖a‖ + ‖b‖) +
          model.epsilon * (‖t 0‖ + ‖t 1‖) +
          model.epsilon * (‖t 2‖ + ‖t 3‖) := by gcongr
    _ ≤ (2 * model.epsilon + model.epsilon ^ 2) *
          (‖t 0‖ + ‖t 1‖ + ‖t 2‖ + ‖t 3‖) := by
            have he := le_of_lt model.epsilon_pos
            nlinarith [mul_le_mul_of_nonneg_left ha he,
              mul_le_mul_of_nonneg_left hb he]
    _ = (2 * model.epsilon + model.epsilon ^ 2) *
          ∑ j : ZMod 4, ‖x j‖ := by
            rw [← Equiv.sum_comp (ZMod.finEquiv 4).toEquiv
              (fun j : ZMod 4 => ‖x j‖), Fin.sum_univ_four]
            simp only [t, p09RadixFourCoefficient_norm]

private lemma p09RoundedRadixFourBlock_l2
    (model : P09WilkinsonModel) (x : ZMod 4 → ℂ) :
    p09ComplexNorm2 (fun k => p09RoundedRadixFourBlock model x k -
        ∑ j : ZMod 4, ZMod.stdAddChar (j * k) * x j) ≤
      (10 * model.epsilon + 4 * model.epsilon ^ 2) * p09ComplexNorm2 x := by
  let err : ZMod 4 → ℂ := fun k => p09RoundedRadixFourBlock model x k -
    ∑ j : ZMod 4, ZMod.stdAddChar (j * k) * x j
  let L : ℝ := ∑ j : ZMod 4, ‖x j‖
  let M : ℝ := (2 * model.epsilon + model.epsilon ^ 2) * L
  have he : 0 ≤ model.epsilon := le_of_lt model.epsilon_pos
  have hM : 0 ≤ M := by dsimp [M, L]; positivity
  have hp (k : ZMod 4) : ‖err k‖ ≤ M := by
    exact p09RoundedRadixFourBlock_pointwise model x k
  have herrsq : (∑ k : ZMod 4, ‖err k‖ ^ 2) ≤ 4 * M ^ 2 := by
    calc
      _ ≤ ∑ _k : ZMod 4, M ^ 2 := by
        apply Finset.sum_le_sum
        intro k hk
        exact pow_le_pow_left₀ (norm_nonneg _) (hp k) 2
      _ = 4 * M ^ 2 := by simp
  have hl1 : L ^ 2 ≤ 4 * ∑ j : ZMod 4, ‖x j‖ ^ 2 := by
    have hc := Finset.sum_mul_sq_le_sq_mul_sq (Finset.univ : Finset (ZMod 4))
      (fun _ => (1 : ℝ)) (fun j => ‖x j‖)
    simpa [L] using hc
  have hcoef : 4 * (2 * model.epsilon + model.epsilon ^ 2) ≤
      10 * model.epsilon + 4 * model.epsilon ^ 2 := by nlinarith
  rw [p09ComplexNorm2, p09ComplexNorm2Sq]
  change Real.sqrt (∑ k : ZMod 4, ‖err k‖ ^ 2) ≤
    (10 * model.epsilon + 4 * model.epsilon ^ 2) *
      Real.sqrt (∑ j : ZMod 4, ‖x j‖ ^ 2)
  have hsumerr : 0 ≤ ∑ k : ZMod 4, ‖err k‖ ^ 2 := by positivity
  have hsumx : 0 ≤ ∑ j : ZMod 4, ‖x j‖ ^ 2 := by positivity
  have hrhs : 0 ≤ (10 * model.epsilon + 4 * model.epsilon ^ 2) *
      Real.sqrt (∑ j : ZMod 4, ‖x j‖ ^ 2) := by positivity
  apply (sq_le_sq₀ (Real.sqrt_nonneg _) hrhs).mp
  rw [Real.sq_sqrt hsumerr]
  calc
    (∑ k : ZMod 4, ‖err k‖ ^ 2) ≤ 4 * M ^ 2 := herrsq
    _ = (4 * (2 * model.epsilon + model.epsilon ^ 2)) ^ 2 * (L ^ 2 / 4) := by
      dsimp [M]
      ring
    _ ≤ (4 * (2 * model.epsilon + model.epsilon ^ 2)) ^ 2 *
          (∑ j : ZMod 4, ‖x j‖ ^ 2) := by
      gcongr
      nlinarith
    _ ≤ (10 * model.epsilon + 4 * model.epsilon ^ 2) ^ 2 *
          (∑ j : ZMod 4, ‖x j‖ ^ 2) := by
      gcongr
    _ = (10 * model.epsilon + 4 * model.epsilon ^ 2) ^ 2 *
          (Real.sqrt (∑ j : ZMod 4, ‖x j‖ ^ 2)) ^ 2 := by
      rw [Real.sq_sqrt hsumx]
    _ = ((10 * model.epsilon + 4 * model.epsilon ^ 2) *
          Real.sqrt (∑ j : ZMod 4, ‖x j‖ ^ 2)) ^ 2 := by ring

private lemma p09_l2_of_pointwise_l1 {q : ℕ} [NeZero q]
    (c : ℝ) (hc : 0 ≤ c) (x err : ZMod q → ℂ)
    (hpoint : ∀ k, ‖err k‖ ≤ c * ∑ j, ‖x j‖) :
    p09ComplexNorm2 err ≤ (q : ℝ) * c * p09ComplexNorm2 x := by
  let L : ℝ := ∑ j : ZMod q, ‖x j‖
  have hL : 0 ≤ L := by dsimp [L]; positivity
  have herrsq : (∑ k : ZMod q, ‖err k‖ ^ 2) ≤
      (q : ℝ) * (c * L) ^ 2 := by
    calc
      _ ≤ ∑ _k : ZMod q, (c * L) ^ 2 := by
        apply Finset.sum_le_sum
        intro k hk
        exact pow_le_pow_left₀ (norm_nonneg _) (hpoint k) 2
      _ = (q : ℝ) * (c * L) ^ 2 := by simp [ZMod.card]
  have hl1 : L ^ 2 ≤ (q : ℝ) * ∑ j : ZMod q, ‖x j‖ ^ 2 := by
    have hcauchy := Finset.sum_mul_sq_le_sq_mul_sq
      (Finset.univ : Finset (ZMod q)) (fun _ => (1 : ℝ)) (fun j => ‖x j‖)
    simpa [L, ZMod.card] using hcauchy
  rw [p09ComplexNorm2, p09ComplexNorm2Sq]
  change Real.sqrt (∑ k : ZMod q, ‖err k‖ ^ 2) ≤
    (q : ℝ) * c * Real.sqrt (∑ j : ZMod q, ‖x j‖ ^ 2)
  have hq : 0 ≤ (q : ℝ) := by positivity
  have hsumerr : 0 ≤ ∑ k : ZMod q, ‖err k‖ ^ 2 := by positivity
  have hsumx : 0 ≤ ∑ j : ZMod q, ‖x j‖ ^ 2 := by positivity
  have hrhs : 0 ≤ (q : ℝ) * c *
      Real.sqrt (∑ j : ZMod q, ‖x j‖ ^ 2) := by positivity
  apply (sq_le_sq₀ (Real.sqrt_nonneg _) hrhs).mp
  rw [Real.sq_sqrt hsumerr]
  calc
    (∑ k : ZMod q, ‖err k‖ ^ 2) ≤ (q : ℝ) * (c * L) ^ 2 := herrsq
    _ ≤ (q : ℝ) * (c ^ 2 * ((q : ℝ) * ∑ j : ZMod q, ‖x j‖ ^ 2)) := by
      gcongr
      simpa [mul_pow] using mul_le_mul_of_nonneg_left hl1 (sq_nonneg c)
    _ = ((q : ℝ) * c) ^ 2 *
          (Real.sqrt (∑ j : ZMod q, ‖x j‖ ^ 2)) ^ 2 := by
      rw [Real.sq_sqrt hsumx]
      ring
    _ = ((q : ℝ) * c *
          Real.sqrt (∑ j : ZMod q, ‖x j‖ ^ 2)) ^ 2 := by ring

private lemma p09RoundedGenericRadixBlock_l2 {q : ℕ} [NeZero q]
    (γ : ℝ) (hγ : 0 ≤ γ) (hq3 : 3 ≤ q) (hq4 : q ≠ 4) :
    ∃ D : ℝ, 0 ≤ D ∧
      ∀ (model : P09WilkinsonModel), model.gamma = γ → model.epsilon ≤ 1 →
        ∀ x : ZMod q → ℂ,
          p09ComplexNorm2 (fun k => p09RoundedGenericRadixBlock model x k -
            ∑ j : ZMod q, ZMod.stdAddChar (j * k) * x j) ≤
          (p09Alpha q γ * model.epsilon + D * model.epsilon ^ 2) *
            Real.sqrt (q : ℝ) * p09ComplexNorm2 x := by
  rcases p09RoundedGenericRadixBlock_error γ hγ hq3 with ⟨B, hB, hpoint⟩
  let D : ℝ := (q : ℝ) * B
  refine ⟨D, by dsimp [D]; positivity, ?_⟩
  intro model hmg heone x
  let c : ℝ := 2 * ((q : ℝ) + model.gamma) * model.epsilon +
    B * model.epsilon ^ 2
  have hc : 0 ≤ c := by
    dsimp [c]
    rw [hmg]
    exact add_nonneg
      (mul_nonneg (mul_nonneg (by positivity)
        (add_nonneg (Nat.cast_nonneg _) hγ)) (le_of_lt model.epsilon_pos))
      (mul_nonneg hB (sq_nonneg _))
  have hl2 := p09_l2_of_pointwise_l1 c hc x
    (fun k => p09RoundedGenericRadixBlock model x k -
      ∑ j : ZMod q, ZMod.stdAddChar (j * k) * x j)
    (hpoint model hmg heone x)
  have hq0 : 0 ≤ (q : ℝ) := by positivity
  have hqsq : Real.sqrt (q : ℝ) ^ 2 = (q : ℝ) := Real.sq_sqrt hq0
  have hqsqrt : 1 ≤ Real.sqrt (q : ℝ) := by
    have : (1 : ℝ) ≤ q := by exact_mod_cast (by omega : 1 ≤ q)
    nlinarith [Real.sqrt_nonneg (q : ℝ)]
  calc
    p09ComplexNorm2 (fun k => p09RoundedGenericRadixBlock model x k -
        ∑ j : ZMod q, ZMod.stdAddChar (j * k) * x j) ≤
      (q : ℝ) * c * p09ComplexNorm2 x := hl2
    _ ≤ (p09Alpha q γ * model.epsilon + D * model.epsilon ^ 2) *
          Real.sqrt (q : ℝ) * p09ComplexNorm2 x := by
      rw [show p09Alpha q γ = 2 * Real.sqrt q * ((q : ℝ) + γ) by
        have hq2 : q ≠ 2 := by omega
        simp [p09Alpha, hq2, hq4]]
      dsimp [c, D]
      rw [hmg]
      have hDextra := mul_le_mul_of_nonneg_left hqsqrt
        (by positivity : 0 ≤ (q : ℝ) * B * model.epsilon ^ 2)
      have hlead :
          2 * (q : ℝ) * ((q : ℝ) + γ) * model.epsilon =
            (2 * Real.sqrt (q : ℝ) * ((q : ℝ) + γ) * model.epsilon) *
              Real.sqrt (q : ℝ) := by
        calc
          2 * (q : ℝ) * ((q : ℝ) + γ) * model.epsilon =
              2 * (Real.sqrt (q : ℝ)) ^ 2 * ((q : ℝ) + γ) *
                model.epsilon := by rw [hqsq]
          _ = _ := by ring
      have hcoef :
          (q : ℝ) *
              (2 * ((q : ℝ) + γ) * model.epsilon + B * model.epsilon ^ 2) ≤
            (2 * Real.sqrt (q : ℝ) * ((q : ℝ) + γ) * model.epsilon +
                (q : ℝ) * B * model.epsilon ^ 2) * Real.sqrt (q : ℝ) := by
        calc
          (q : ℝ) *
                (2 * ((q : ℝ) + γ) * model.epsilon + B * model.epsilon ^ 2) =
              2 * (q : ℝ) * ((q : ℝ) + γ) * model.epsilon +
                (q : ℝ) * B * model.epsilon ^ 2 := by ring
          _ = (2 * Real.sqrt (q : ℝ) * ((q : ℝ) + γ) * model.epsilon) *
                Real.sqrt (q : ℝ) + (q : ℝ) * B * model.epsilon ^ 2 := by
              rw [← hlead]
          _ ≤ (2 * Real.sqrt (q : ℝ) * ((q : ℝ) + γ) * model.epsilon) *
                Real.sqrt (q : ℝ) +
                  (q : ℝ) * B * model.epsilon ^ 2 * Real.sqrt (q : ℝ) := by
              exact add_le_add_right (by simpa using hDextra) _
          _ = _ := by ring
      have hxnorm : 0 ≤ p09ComplexNorm2 x := by
        simp [p09ComplexNorm2]
      exact mul_le_mul_of_nonneg_right hcoef hxnorm

private noncomputable def p09RoundedRadixDispatch {q : ℕ} [NeZero q]
    (model : P09WilkinsonModel) (x : ZMod q → ℂ) (k : ZMod q) : ℂ :=
  if h2 : q = 2 then
    p09RoundedRadixTwoBlock model
      (fun j : ZMod 2 => x (h2.symm ▸ j)) (h2 ▸ k)
  else if h4 : q = 4 then
    p09RoundedRadixFourBlock model
      (fun j : ZMod 4 => x (h4.symm ▸ j)) (h4 ▸ k)
  else p09RoundedGenericRadixBlock model x k

private lemma p09RoundedRadixDispatch_l2 {q : ℕ} [NeZero q]
    (hq2 : 2 ≤ q) (γ : ℝ) (hγ : 0 ≤ γ) : ∃ D : ℝ, 0 ≤ D ∧
      ∀ (model : P09WilkinsonModel), model.gamma = γ → model.epsilon ≤ 1 →
        ∀ x : ZMod q → ℂ,
          p09ComplexNorm2 (fun k => p09RoundedRadixDispatch model x k -
            ∑ j : ZMod q, ZMod.stdAddChar (j * k) * x j) ≤
          (p09Alpha q γ * model.epsilon + D * model.epsilon ^ 2) *
            Real.sqrt (q : ℝ) * p09ComplexNorm2 x := by
  by_cases h2 : q = 2
  · subst q
    refine ⟨0, by positivity, ?_⟩
    intro model hmg heone x
    have h := p09RoundedRadixTwoBlock_l2 model x
    calc
      p09ComplexNorm2 (fun k => p09RoundedRadixDispatch model x k -
          ∑ j : ZMod 2, ZMod.stdAddChar (j * k) * x j) ≤
        2 * model.epsilon * p09ComplexNorm2 x := by
          simpa [p09RoundedRadixDispatch] using h
      _ = (p09Alpha 2 γ * model.epsilon + 0 * model.epsilon ^ 2) *
          Real.sqrt (2 : ℝ) * p09ComplexNorm2 x := by
          have hs : Real.sqrt (2 : ℝ) ^ 2 = 2 := Real.sq_sqrt (by norm_num)
          have ha : p09Alpha 2 γ = Real.sqrt 2 := by simp [p09Alpha]
          rw [ha]
          simp only [zero_mul, add_zero]
          calc
            2 * model.epsilon * p09ComplexNorm2 x =
                Real.sqrt 2 ^ 2 * model.epsilon * p09ComplexNorm2 x := by rw [hs]
            _ = _ := by ring
  · by_cases h4 : q = 4
    · subst q
      refine ⟨2, by positivity, ?_⟩
      intro model hmg heone x
      have h := p09RoundedRadixFourBlock_l2 model x
      calc
        p09ComplexNorm2 (fun k => p09RoundedRadixDispatch model x k -
            ∑ j : ZMod 4, ZMod.stdAddChar (j * k) * x j) ≤
          (10 * model.epsilon + 4 * model.epsilon ^ 2) *
            p09ComplexNorm2 x := by
              simpa [p09RoundedRadixDispatch] using h
        _ = (p09Alpha 4 γ * model.epsilon + 2 * model.epsilon ^ 2) *
            Real.sqrt (4 : ℝ) * p09ComplexNorm2 x := by
              have ha : p09Alpha 4 γ = 5 := by simp [p09Alpha]
              rw [ha]
              have hs : Real.sqrt (4 : ℝ) = 2 := by norm_num
              rw [hs]
              ring
    · have hq3 : 3 ≤ q := by omega
      rcases p09RoundedGenericRadixBlock_l2 γ hγ hq3 h4 with ⟨D, hD, h⟩
      refine ⟨D, hD, ?_⟩
      intro model hmg heone x
      simpa [p09RoundedRadixDispatch, h2, h4] using h model hmg heone x

private lemma p09RoundedMixedRadixBlockApply_l2 {n : ℕ} [NeZero n]
    (stage : P09MixedRadixStage n) (γ : ℝ) (hγ : 0 ≤ γ) :
    ∃ D : ℝ, 0 ≤ D ∧
      ∀ (model : P09WilkinsonModel), model.gamma = γ → model.epsilon ≤ 1 →
        ∀ x : ZMod n → ℂ,
          p09ComplexNorm2 (fun i =>
            p09RoundedMixedRadixBlockApply model stage x i -
              p09MixedRadixBlockApply stage x i) ≤
          (p09Alpha stage.radix γ * model.epsilon + D * model.epsilon ^ 2) *
            Real.sqrt (stage.radix : ℝ) * p09ComplexNorm2 x := by
  letI : NeZero stage.radix := ⟨stage.radix_ne_zero⟩
  rcases p09RoundedRadixDispatch_l2 stage.radix_two_le γ hγ with ⟨D, hD, hlocal⟩
  refine ⟨D, hD, ?_⟩
  intro model hmg heone x
  let permuted : ZMod n → ℂ := fun i => x (stage.permutation i)
  let xb : Fin stage.blockCount → ZMod stage.radix → ℂ :=
    fun b j => permuted (stage.reindex (b, j))
  let errb : Fin stage.blockCount → ZMod stage.radix → ℂ := fun b k =>
    p09RoundedRadixDispatch model (xb b) k -
      ∑ j : ZMod stage.radix, ZMod.stdAddChar (j * k) * xb b j
  let C : ℝ := (p09Alpha stage.radix γ * model.epsilon +
      D * model.epsilon ^ 2) * Real.sqrt (stage.radix : ℝ)
  have halpha : 0 ≤ p09Alpha stage.radix γ := by
    simp only [p09Alpha]
    split_ifs <;> positivity
  have hC : 0 ≤ C := by
    dsimp [C]
    exact mul_nonneg
      (add_nonneg (mul_nonneg halpha (le_of_lt model.epsilon_pos))
        (mul_nonneg hD (sq_nonneg _))) (Real.sqrt_nonneg _)
  have hb (b : Fin stage.blockCount) :
      p09ComplexNorm2 (errb b) ≤ C * p09ComplexNorm2 (xb b) := by
    exact hlocal model hmg heone (xb b)
  have hbsq (b : Fin stage.blockCount) :
      (∑ k : ZMod stage.radix, ‖errb b k‖ ^ 2) ≤
        C ^ 2 * ∑ j : ZMod stage.radix, ‖xb b j‖ ^ 2 := by
    have hsq := (pow_le_pow_left₀ (by
      simp [p09ComplexNorm2]) (hb b) 2)
    simp only [p09ComplexNorm2, p09ComplexNorm2Sq] at hsq
    have he : 0 ≤ ∑ k : ZMod stage.radix, ‖errb b k‖ ^ 2 := by positivity
    have hx : 0 ≤ ∑ j : ZMod stage.radix, ‖xb b j‖ ^ 2 := by positivity
    rw [Real.sq_sqrt he, mul_pow, Real.sq_sqrt hx] at hsq
    exact hsq
  have hsumblocks :
      (∑ b : Fin stage.blockCount, ∑ k : ZMod stage.radix, ‖errb b k‖ ^ 2) ≤
        C ^ 2 *
          (∑ b : Fin stage.blockCount, ∑ j : ZMod stage.radix, ‖xb b j‖ ^ 2) := by
    calc
      _ ≤ ∑ b : Fin stage.blockCount,
          C ^ 2 * ∑ j : ZMod stage.radix, ‖xb b j‖ ^ 2 := by
            gcongr with b
            exact hbsq b
      _ = _ := by rw [Finset.mul_sum]
  have houtsum :
      (∑ i : ZMod n,
        ‖p09RoundedMixedRadixBlockApply model stage x i -
          p09MixedRadixBlockApply stage x i‖ ^ 2) =
        ∑ b : Fin stage.blockCount,
          ∑ k : ZMod stage.radix, ‖errb b k‖ ^ 2 := by
    rw [← Equiv.sum_comp stage.reindex
      (fun i : ZMod n =>
        ‖p09RoundedMixedRadixBlockApply model stage x i -
          p09MixedRadixBlockApply stage x i‖ ^ 2)]
    rw [Fintype.sum_prod_type]
    apply Finset.sum_congr rfl
    intro b hbmem
    apply Finset.sum_congr rfl
    intro k hkmem
    have hround :
        p09RoundedMixedRadixBlockApply model stage x (stage.reindex (b, k)) =
          p09RoundedRadixDispatch model (xb b) k := by
      simp [p09RoundedMixedRadixBlockApply, p09RoundedRadixDispatch,
        xb, permuted]
    have hexact : p09MixedRadixBlockApply stage x (stage.reindex (b, k)) =
        ∑ j : ZMod stage.radix, ZMod.stdAddChar (j * k) * xb b j := by
      change (∑ j : ZMod stage.radix,
          ZMod.stdAddChar
              (j * (stage.reindex.symm (stage.reindex (b, k))).2) *
            x (stage.permutation
              (stage.reindex ((stage.reindex.symm (stage.reindex (b, k))).1, j)))) = _
      rw [stage.reindex.symm_apply_apply]
    rw [hround, hexact]
  have hinsum :
      (∑ b : Fin stage.blockCount,
          ∑ j : ZMod stage.radix, ‖xb b j‖ ^ 2) =
        ∑ i : ZMod n, ‖x i‖ ^ 2 := by
    change (∑ b : Fin stage.blockCount, ∑ j : ZMod stage.radix,
      ‖x (stage.permutation (stage.reindex (b, j)))‖ ^ 2) = _
    calc
      (∑ b : Fin stage.blockCount, ∑ j : ZMod stage.radix,
          ‖x (stage.permutation (stage.reindex (b, j)))‖ ^ 2) =
          ∑ p : Fin stage.blockCount × ZMod stage.radix,
            ‖x (stage.permutation (stage.reindex p))‖ ^ 2 :=
              (Fintype.sum_prod_type
                (fun p : Fin stage.blockCount × ZMod stage.radix =>
                  ‖x (stage.permutation (stage.reindex p))‖ ^ 2)).symm
      _ = ∑ i : ZMod n, ‖x (stage.permutation i)‖ ^ 2 := by
        exact Fintype.sum_equiv stage.reindex _ _ (fun p => rfl)
      _ = ∑ i : ZMod n, ‖x i‖ ^ 2 := by
        exact Fintype.sum_equiv stage.permutation _ _ (fun i => rfl)
  rw [p09ComplexNorm2, p09ComplexNorm2Sq]
  change Real.sqrt (∑ i : ZMod n,
      ‖p09RoundedMixedRadixBlockApply model stage x i -
        p09MixedRadixBlockApply stage x i‖ ^ 2) ≤
    C * Real.sqrt (∑ i : ZMod n, ‖x i‖ ^ 2)
  rw [houtsum, ← hinsum]
  have he : 0 ≤ ∑ b : Fin stage.blockCount,
      ∑ k : ZMod stage.radix, ‖errb b k‖ ^ 2 := by positivity
  have hx : 0 ≤ ∑ b : Fin stage.blockCount,
      ∑ j : ZMod stage.radix, ‖xb b j‖ ^ 2 := by positivity
  apply (sq_le_sq₀ (Real.sqrt_nonneg _) (by positivity)).mp
  rw [Real.sq_sqrt he, mul_pow, Real.sq_sqrt hx]
  exact hsumblocks

private lemma p09_l2_of_pointwise {n : ℕ} [NeZero n]
    (c : ℝ) (hc : 0 ≤ c) (x err : ZMod n → ℂ)
    (hpoint : ∀ i, ‖err i‖ ≤ c * ‖x i‖) :
    p09ComplexNorm2 err ≤ c * p09ComplexNorm2 x := by
  have hsum : (∑ i : ZMod n, ‖err i‖ ^ 2) ≤
      c ^ 2 * ∑ i : ZMod n, ‖x i‖ ^ 2 := by
    calc
      _ ≤ ∑ i : ZMod n, (c * ‖x i‖) ^ 2 := by
        apply Finset.sum_le_sum
        intro i hi
        exact pow_le_pow_left₀ (norm_nonneg _) (hpoint i) 2
      _ = _ := by rw [Finset.mul_sum]; congr 1; funext i; ring
  simp only [p09ComplexNorm2, p09ComplexNorm2Sq]
  have he : 0 ≤ ∑ i : ZMod n, ‖err i‖ ^ 2 := by positivity
  have hx : 0 ≤ ∑ i : ZMod n, ‖x i‖ ^ 2 := by positivity
  apply (sq_le_sq₀ (Real.sqrt_nonneg _)
    (mul_nonneg hc (Real.sqrt_nonneg _))).mp
  rw [Real.sq_sqrt he, mul_pow, Real.sq_sqrt hx]
  exact hsum

private lemma p09MixedRadixTwiddleApply_norm {n : ℕ} [NeZero n]
    (stage : P09MixedRadixStage n) (x : ZMod n → ℂ) :
    p09ComplexNorm2 (p09MixedRadixTwiddleApply stage x) = p09ComplexNorm2 x := by
  simp only [p09ComplexNorm2, p09ComplexNorm2Sq]
  congr 1
  apply Finset.sum_congr rfl
  intro i hi
  simp only [p09MixedRadixTwiddleApply]
  split_ifs
  · rw [norm_mul, p09StdAddChar_norm, one_mul]
  · rfl

private lemma p09RoundedMixedRadixTwiddleApply_l2 {n : ℕ} [NeZero n]
    (stage : P09MixedRadixStage n) (γ : ℝ) (hγ : 0 ≤ γ) :
    ∃ D : ℝ, 0 ≤ D ∧
      ∀ (model : P09WilkinsonModel), model.gamma = γ → model.epsilon ≤ 1 →
        ∀ x : ZMod n → ℂ,
          p09ComplexNorm2 (fun i =>
            p09RoundedMixedRadixTwiddleApply model stage x i -
              p09MixedRadixTwiddleApply stage x i) ≤
          (if stage.useTwiddle then
              (3 + 2 * γ) * model.epsilon + D * model.epsilon ^ 2
            else 0) * p09ComplexNorm2 x := by
  let D : ℝ := 2 + 10 * γ
  refine ⟨D, by dsimp [D]; positivity, ?_⟩
  intro model hmg heone x
  by_cases ht : stage.useTwiddle
  · rw [if_pos ht]
    let c : ℝ := (3 + 2 * γ) * model.epsilon + D * model.epsilon ^ 2
    have hc : 0 ≤ c := by
      dsimp [c, D]
      exact add_nonneg
        (mul_nonneg (by nlinarith) (le_of_lt model.epsilon_pos))
        (mul_nonneg (by nlinarith) (sq_nonneg _))
    apply p09_l2_of_pointwise c hc x
    intro i
    simp only [p09RoundedMixedRadixTwiddleApply,
      p09MixedRadixTwiddleApply, ht, if_pos]
    simpa [c, D, hmg] using
      p09RoundedRootMul_error model (stage.twiddleExponent i) (x i) heone
  · rw [if_neg ht]
    simp [p09RoundedMixedRadixTwiddleApply,
      p09MixedRadixTwiddleApply, ht, p09ComplexNorm2, p09ComplexNorm2Sq]

private lemma p09ComplexNorm2_eq_norm {n : ℕ} [NeZero n] (x : ZMod n → ℂ) :
    p09ComplexNorm2 x = ‖(WithLp.toLp 2 x : EuclideanSpace ℂ (ZMod n))‖ := by
  rw [p09ComplexNorm2, p09ComplexNorm2Sq, EuclideanSpace.norm_eq]

private lemma p09ComplexNorm2_add {n : ℕ} [NeZero n]
    (x y : ZMod n → ℂ) :
    p09ComplexNorm2 (fun i => x i + y i) ≤
      p09ComplexNorm2 x + p09ComplexNorm2 y := by
  rw [p09ComplexNorm2_eq_norm, p09ComplexNorm2_eq_norm,
    p09ComplexNorm2_eq_norm]
  simpa using norm_add_le (WithLp.toLp 2 x : EuclideanSpace ℂ (ZMod n))
    (WithLp.toLp 2 y : EuclideanSpace ℂ (ZMod n))

private lemma p09RoundedMixedRadixStageApply_l2 {n : ℕ} [NeZero n]
    (plan : P09MixedRadixFftPlan n) (s : Fin plan.stageCount)
    (γ : ℝ) (hγ : 0 ≤ γ) : ∃ D : ℝ, 0 ≤ D ∧
      ∀ (model : P09WilkinsonModel), model.gamma = γ → model.epsilon ≤ 1 →
        ∀ x : ZMod n → ℂ,
          p09ComplexNorm2 (fun i =>
            p09RoundedMixedRadixStageApply model (plan.stage s) x i -
              p09MixedRadixStageApply (plan.stage s) x i) ≤
          ((p09Alpha (plan.stage s).radix γ +
                if (plan.stage s).useTwiddle then 3 + 2 * γ else 0) *
              model.epsilon + D * model.epsilon ^ 2) *
            Real.sqrt ((plan.stage s).radix : ℝ) * p09ComplexNorm2 x := by
  let stage := plan.stage s
  letI : NeZero stage.radix := ⟨stage.radix_ne_zero⟩
  rcases p09RoundedMixedRadixBlockApply_l2 stage γ hγ with ⟨B, hB, hblock⟩
  rcases p09RoundedMixedRadixTwiddleApply_l2 stage γ hγ with ⟨U, hU, htwiddle⟩
  let A : ℝ := p09Alpha stage.radix γ
  let T : ℝ := if stage.useTwiddle then 3 + 2 * γ else 0
  let D : ℝ := B + U + T * A + T * B + U * A + U * B
  have hA : 0 ≤ A := by
    dsimp [A]
    simp only [p09Alpha]
    split_ifs <;> positivity
  have hT : 0 ≤ T := by dsimp [T]; split_ifs <;> positivity
  refine ⟨D, by dsimp [D]; positivity, ?_⟩
  intro model hmg heone x
  let bx := p09MixedRadixBlockApply stage x
  let rbx := p09RoundedMixedRadixBlockApply model stage x
  let bcoef : ℝ := A * model.epsilon + B * model.epsilon ^ 2
  let tcoef : ℝ := T * model.epsilon + U * model.epsilon ^ 2
  have he : 0 ≤ model.epsilon := le_of_lt model.epsilon_pos
  have hbcoef : 0 ≤ bcoef := by dsimp [bcoef]; positivity
  have htcoef : 0 ≤ tcoef := by dsimp [tcoef]; positivity
  have hb := hblock model hmg heone x
  have htw0 := htwiddle model hmg heone rbx
  have htw : p09ComplexNorm2 (fun i =>
      p09RoundedMixedRadixTwiddleApply model stage rbx i -
        p09MixedRadixTwiddleApply stage rbx i) ≤
      tcoef * p09ComplexNorm2 rbx := by
    by_cases hu : stage.useTwiddle
    · simpa [tcoef, T, hu] using htw0
    · have hz : p09ComplexNorm2 (fun i =>
          p09RoundedMixedRadixTwiddleApply model stage rbx i -
            p09MixedRadixTwiddleApply stage rbx i) = 0 := by
          simpa [hu, p09RoundedMixedRadixTwiddleApply,
            p09MixedRadixTwiddleApply, p09ComplexNorm2, p09ComplexNorm2Sq]
      rw [hz]
      exact mul_nonneg htcoef (by simp [p09ComplexNorm2])
  have hbnorm : p09ComplexNorm2 bx =
      Real.sqrt (stage.radix : ℝ) * p09ComplexNorm2 x := by
    have hs := plan.stage_norm_scaling s x
    rw [p09MixedRadixStageApply, p09MixedRadixTwiddleApply_norm] at hs
    exact hs
  have hrbnorm : p09ComplexNorm2 rbx ≤
      (1 + bcoef) * Real.sqrt (stage.radix : ℝ) * p09ComplexNorm2 x := by
    have htri : p09ComplexNorm2 rbx ≤ p09ComplexNorm2 bx +
        p09ComplexNorm2 (fun i => rbx i - bx i) := by
      have h := p09ComplexNorm2_add bx (fun i => rbx i - bx i)
      have hf : (fun i => bx i + (rbx i - bx i)) = rbx := by
        funext i
        ring
      rw [hf] at h
      exact h
    calc
      p09ComplexNorm2 rbx ≤ p09ComplexNorm2 bx +
          p09ComplexNorm2 (fun i => rbx i - bx i) := htri
      _ ≤ Real.sqrt (stage.radix : ℝ) * p09ComplexNorm2 x +
          bcoef * Real.sqrt (stage.radix : ℝ) * p09ComplexNorm2 x := by
            rw [hbnorm]
            have hb' : p09ComplexNorm2 (fun i => rbx i - bx i) ≤
                bcoef * Real.sqrt (stage.radix : ℝ) * p09ComplexNorm2 x := hb
            exact add_le_add_right hb' _
      _ = (1 + bcoef) * Real.sqrt (stage.radix : ℝ) *
          p09ComplexNorm2 x := by ring
  have hiso : p09ComplexNorm2 (fun i =>
      p09MixedRadixTwiddleApply stage rbx i -
        p09MixedRadixTwiddleApply stage bx i) =
      p09ComplexNorm2 (fun i => rbx i - bx i) := by
    have h := p09MixedRadixTwiddleApply_norm stage (fun i => rbx i - bx i)
    have hf : (fun i =>
        p09MixedRadixTwiddleApply stage rbx i -
          p09MixedRadixTwiddleApply stage bx i) =
        p09MixedRadixTwiddleApply stage (fun i => rbx i - bx i) := by
      funext i
      simp only [p09MixedRadixTwiddleApply]
      split_ifs <;> ring
    rw [hf]
    exact h
  have herror : p09ComplexNorm2 (fun i =>
      p09RoundedMixedRadixStageApply model stage x i -
        p09MixedRadixStageApply stage x i) ≤
      tcoef * p09ComplexNorm2 rbx +
        bcoef * Real.sqrt (stage.radix : ℝ) * p09ComplexNorm2 x := by
    let e1 : ZMod n → ℂ := fun i =>
      p09RoundedMixedRadixTwiddleApply model stage rbx i -
        p09MixedRadixTwiddleApply stage rbx i
    let e2 : ZMod n → ℂ := fun i =>
      p09MixedRadixTwiddleApply stage rbx i -
        p09MixedRadixTwiddleApply stage bx i
    have htri := p09ComplexNorm2_add e1 e2
    have hid : (fun i =>
        p09RoundedMixedRadixStageApply model stage x i -
          p09MixedRadixStageApply stage x i) = fun i => e1 i + e2 i := by
      funext i
      dsimp [e1, e2, rbx, bx, p09RoundedMixedRadixStageApply,
        p09MixedRadixStageApply]
      ring
    rw [hid]
    calc
      p09ComplexNorm2 (fun i => e1 i + e2 i) ≤
          p09ComplexNorm2 e1 + p09ComplexNorm2 e2 := htri
      _ ≤ tcoef * p09ComplexNorm2 rbx +
          bcoef * Real.sqrt (stage.radix : ℝ) * p09ComplexNorm2 x := by
            apply add_le_add htw
            rw [show p09ComplexNorm2 e2 =
                p09ComplexNorm2 (fun i => rbx i - bx i) by exact hiso]
            exact hb
  have hpoly : tcoef * (1 + bcoef) + bcoef ≤
      (A + T) * model.epsilon + D * model.epsilon ^ 2 := by
    have he3 : model.epsilon ^ 3 ≤ model.epsilon ^ 2 := by
      nlinarith [sq_nonneg model.epsilon]
    have he4 : model.epsilon ^ 4 ≤ model.epsilon ^ 2 := by
      nlinarith [sq_nonneg model.epsilon,
        sq_nonneg (model.epsilon ^ 2 - model.epsilon)]
    have hTA := mul_le_mul_of_nonneg_left he3 (by positivity : 0 ≤ T * A)
    have hTB := mul_le_mul_of_nonneg_left he3 (by positivity : 0 ≤ T * B)
    have hUA := mul_le_mul_of_nonneg_left he3 (by positivity : 0 ≤ U * A)
    have hUB := mul_le_mul_of_nonneg_left he4 (by positivity : 0 ≤ U * B)
    dsimp [tcoef, bcoef, D]
    nlinarith
  change p09ComplexNorm2 (fun i =>
      p09RoundedMixedRadixStageApply model stage x i -
        p09MixedRadixStageApply stage x i) ≤ _
  calc
    _ ≤ tcoef * p09ComplexNorm2 rbx +
        bcoef * Real.sqrt (stage.radix : ℝ) * p09ComplexNorm2 x := herror
    _ ≤ (tcoef * (1 + bcoef) + bcoef) *
          Real.sqrt (stage.radix : ℝ) * p09ComplexNorm2 x := by
            have ht := mul_le_mul_of_nonneg_left hrbnorm htcoef
            have hxnonneg : 0 ≤ p09ComplexNorm2 x := by
              simp [p09ComplexNorm2]
            nlinarith [norm_nonneg
              (WithLp.toLp 2 x : EuclideanSpace ℂ (ZMod n)),
              Real.sqrt_nonneg (stage.radix : ℝ), hxnonneg]
    _ ≤ ((A + T) * model.epsilon + D * model.epsilon ^ 2) *
          Real.sqrt (stage.radix : ℝ) * p09ComplexNorm2 x := by
            have hxnonneg : 0 ≤ p09ComplexNorm2 x := by
              simp [p09ComplexNorm2]
            exact mul_le_mul_of_nonneg_right
              (mul_le_mul_of_nonneg_right hpoly (Real.sqrt_nonneg _)) hxnonneg
    _ = ((p09Alpha (plan.stage s).radix γ +
              if (plan.stage s).useTwiddle then 3 + 2 * γ else 0) *
            model.epsilon + D * model.epsilon ^ 2) *
          Real.sqrt ((plan.stage s).radix : ℝ) * p09ComplexNorm2 x := by rfl

private lemma p09MixedRadixStageApply_sub {n : ℕ} [NeZero n]
    (stage : P09MixedRadixStage n) (x y : ZMod n → ℂ) :
    (fun i => p09MixedRadixStageApply stage x i -
      p09MixedRadixStageApply stage y i) =
      p09MixedRadixStageApply stage (fun i => x i - y i) := by
  funext i
  simp only [p09MixedRadixStageApply, p09MixedRadixTwiddleApply]
  split_ifs
  · rw [← mul_sub]
    congr 1
    simp only [p09MixedRadixBlockApply]
    rw [← Finset.sum_sub_distrib]
    apply Finset.sum_congr rfl
    intro j hj
    rw [mul_sub]
  · simp only [p09MixedRadixBlockApply]
    rw [← Finset.sum_sub_distrib]
    apply Finset.sum_congr rfl
    intro j hj
    rw [mul_sub]

private noncomputable def p09ExactPlanPrefix {n : ℕ} [NeZero n]
    (plan : P09MixedRadixFftPlan n) :
    ∀ k : ℕ, k ≤ plan.stageCount → (ZMod n → ℂ) → ZMod n → ℂ
  | 0, _, x => x
  | k + 1, hk, x =>
      p09MixedRadixStageApply
        (plan.stage ⟨k, Nat.lt_of_succ_le hk⟩)
        (p09ExactPlanPrefix plan k (Nat.le_of_succ_le hk) x)

private noncomputable def p09RoundedPlanPrefix {n : ℕ} [NeZero n]
    (plan : P09MixedRadixFftPlan n) (model : P09WilkinsonModel) :
    ∀ k : ℕ, k ≤ plan.stageCount → (ZMod n → ℂ) → ZMod n → ℂ
  | 0, _, x => x
  | k + 1, hk, x =>
      p09RoundedMixedRadixStageApply model
        (plan.stage ⟨k, Nat.lt_of_succ_le hk⟩)
        (p09RoundedPlanPrefix plan model k (Nat.le_of_succ_le hk) x)

private noncomputable def p09PlanPrefixScale {n : ℕ} [NeZero n]
    (plan : P09MixedRadixFftPlan n) (k : ℕ) (hk : k ≤ plan.stageCount) : ℝ :=
  ∏ i : Fin k, Real.sqrt ((plan.stage (Fin.castLE hk i)).radix : ℝ)

private noncomputable def p09PlanPrefixCoeff {n : ℕ} [NeZero n]
    (plan : P09MixedRadixFftPlan n) (γ : ℝ)
    (k : ℕ) (hk : k ≤ plan.stageCount) : ℝ :=
  ∑ i : Fin k, (p09Alpha (plan.stage (Fin.castLE hk i)).radix γ +
    if (plan.stage (Fin.castLE hk i)).useTwiddle then 3 + 2 * γ else 0)

private lemma p09ExactPlanPrefix_norm {n : ℕ} [NeZero n]
    (plan : P09MixedRadixFftPlan n) (k : ℕ) (hk : k ≤ plan.stageCount)
    (x : ZMod n → ℂ) :
    p09ComplexNorm2 (p09ExactPlanPrefix plan k hk x) =
      p09PlanPrefixScale plan k hk * p09ComplexNorm2 x := by
  induction k with
  | zero => simp [p09ExactPlanPrefix, p09PlanPrefixScale]
  | succ k ih =>
      let hk' : k ≤ plan.stageCount := Nat.le_of_succ_le hk
      let s : Fin plan.stageCount := ⟨k, Nat.lt_of_succ_le hk⟩
      rw [p09ExactPlanPrefix]
      rw [plan.stage_norm_scaling s]
      rw [ih hk']
      have hscale : p09PlanPrefixScale plan (k + 1) hk =
          p09PlanPrefixScale plan k hk' *
            Real.sqrt ((plan.stage s).radix : ℝ) := by
        unfold p09PlanPrefixScale
        rw [Fin.prod_univ_castSucc]
        congr 1
      rw [hscale]
      ring

private lemma p09PlanPrefixScale_nonneg {n : ℕ} [NeZero n]
    (plan : P09MixedRadixFftPlan n) (k : ℕ) (hk : k ≤ plan.stageCount) :
    0 ≤ p09PlanPrefixScale plan k hk := by
  unfold p09PlanPrefixScale
  exact Finset.prod_nonneg (fun i hi => Real.sqrt_nonneg _)

private lemma p09PlanPrefixCoeff_nonneg {n : ℕ} [NeZero n]
    (plan : P09MixedRadixFftPlan n) (γ : ℝ) (hγ : 0 ≤ γ)
    (k : ℕ) (hk : k ≤ plan.stageCount) :
    0 ≤ p09PlanPrefixCoeff plan γ k hk := by
  apply Finset.sum_nonneg
  intro i hi
  have ha : 0 ≤ p09Alpha (plan.stage (Fin.castLE hk i)).radix γ := by
    simp only [p09Alpha]
    split_ifs <;> positivity
  split_ifs <;> positivity

private lemma p09PlanPrefix_asymptotic {n : ℕ} [NeZero n]
    (plan : P09MixedRadixFftPlan n) (γ : ℝ) (hγ : 0 ≤ γ)
    (k : ℕ) (hk : k ≤ plan.stageCount) : ∃ D : ℝ, 0 ≤ D ∧
      ∀ (model : P09WilkinsonModel), model.gamma = γ → model.epsilon ≤ 1 →
        ∀ x : ZMod n → ℂ,
          p09ComplexNorm2 (fun i =>
            p09RoundedPlanPrefix plan model k hk x i -
              p09ExactPlanPrefix plan k hk x i) ≤
          (p09PlanPrefixCoeff plan γ k hk * model.epsilon +
              D * model.epsilon ^ 2) *
            p09PlanPrefixScale plan k hk * p09ComplexNorm2 x := by
  induction k with
  | zero =>
      refine ⟨0, by positivity, ?_⟩
      intro model hmg heone x
      simp [p09RoundedPlanPrefix, p09ExactPlanPrefix, p09PlanPrefixCoeff,
        p09PlanPrefixScale, p09ComplexNorm2, p09ComplexNorm2Sq]
  | succ k ih =>
      let hk' : k ≤ plan.stageCount := Nat.le_of_succ_le hk
      let s : Fin plan.stageCount := ⟨k, Nat.lt_of_succ_le hk⟩
      rcases ih hk' with ⟨P, hP, hprev⟩
      rcases p09RoundedMixedRadixStageApply_l2 plan s γ hγ with
        ⟨Q, hQ, hstage⟩
      let C : ℝ := p09PlanPrefixCoeff plan γ k hk'
      let c : ℝ := p09Alpha (plan.stage s).radix γ +
        if (plan.stage s).useTwiddle then 3 + 2 * γ else 0
      let D : ℝ := P + Q + c * C + c * P + Q * C + Q * P
      have hC : 0 ≤ C := p09PlanPrefixCoeff_nonneg plan γ hγ k hk'
      have hc : 0 ≤ c := by
        dsimp [c]
        have ha : 0 ≤ p09Alpha (plan.stage s).radix γ := by
          simp only [p09Alpha]
          split_ifs <;> positivity
        split_ifs <;> positivity
      refine ⟨D, by dsimp [D]; positivity, ?_⟩
      intro model hmg heone x
      let ep := p09ExactPlanPrefix plan k hk' x
      let rp := p09RoundedPlanPrefix plan model k hk' x
      let S : ℝ := p09PlanPrefixScale plan k hk'
      let pcoef : ℝ := C * model.epsilon + P * model.epsilon ^ 2
      let scoef : ℝ := c * model.epsilon + Q * model.epsilon ^ 2
      have he : 0 ≤ model.epsilon := le_of_lt model.epsilon_pos
      have hS : 0 ≤ S := p09PlanPrefixScale_nonneg plan k hk'
      have hpcoef : 0 ≤ pcoef := by dsimp [pcoef]; positivity
      have hscoef : 0 ≤ scoef := by dsimp [scoef]; positivity
      have hp := hprev model hmg heone x
      have hpnorm : p09ComplexNorm2 rp ≤
          (1 + pcoef) * S * p09ComplexNorm2 x := by
        have htri := p09ComplexNorm2_add ep (fun i => rp i - ep i)
        have hf : (fun i => ep i + (rp i - ep i)) = rp := by
          funext i
          ring
        rw [hf] at htri
        calc
          p09ComplexNorm2 rp ≤ p09ComplexNorm2 ep +
              p09ComplexNorm2 (fun i => rp i - ep i) := htri
          _ ≤ S * p09ComplexNorm2 x + pcoef * S * p09ComplexNorm2 x := by
            rw [show p09ComplexNorm2 ep = S * p09ComplexNorm2 x by
              exact p09ExactPlanPrefix_norm plan k hk' x]
            exact add_le_add_right hp _
          _ = (1 + pcoef) * S * p09ComplexNorm2 x := by ring
      have hs := hstage model hmg heone rp
      have hs' : p09ComplexNorm2 (fun i =>
          p09RoundedMixedRadixStageApply model (plan.stage s) rp i -
            p09MixedRadixStageApply (plan.stage s) rp i) ≤
          scoef * Real.sqrt ((plan.stage s).radix : ℝ) *
            p09ComplexNorm2 rp := by
        exact hs
      have hexactdiff : p09ComplexNorm2 (fun i =>
          p09MixedRadixStageApply (plan.stage s) rp i -
            p09MixedRadixStageApply (plan.stage s) ep i) =
          Real.sqrt ((plan.stage s).radix : ℝ) *
            p09ComplexNorm2 (fun i => rp i - ep i) := by
        rw [p09MixedRadixStageApply_sub]
        exact plan.stage_norm_scaling s (fun i => rp i - ep i)
      have herr : p09ComplexNorm2 (fun i =>
          p09RoundedPlanPrefix plan model (k + 1) hk x i -
            p09ExactPlanPrefix plan (k + 1) hk x i) ≤
          scoef * Real.sqrt ((plan.stage s).radix : ℝ) *
              p09ComplexNorm2 rp +
            Real.sqrt ((plan.stage s).radix : ℝ) *
              (pcoef * S * p09ComplexNorm2 x) := by
        let e1 : ZMod n → ℂ := fun i =>
          p09RoundedMixedRadixStageApply model (plan.stage s) rp i -
            p09MixedRadixStageApply (plan.stage s) rp i
        let e2 : ZMod n → ℂ := fun i =>
          p09MixedRadixStageApply (plan.stage s) rp i -
            p09MixedRadixStageApply (plan.stage s) ep i
        have htri := p09ComplexNorm2_add e1 e2
        have hid : (fun i =>
            p09RoundedPlanPrefix plan model (k + 1) hk x i -
              p09ExactPlanPrefix plan (k + 1) hk x i) =
            fun i => e1 i + e2 i := by
          funext i
          dsimp [p09RoundedPlanPrefix, p09ExactPlanPrefix, e1, e2, rp, ep, s]
          ring
        rw [hid]
        calc
          p09ComplexNorm2 (fun i => e1 i + e2 i) ≤
              p09ComplexNorm2 e1 + p09ComplexNorm2 e2 := htri
          _ ≤ scoef * Real.sqrt ((plan.stage s).radix : ℝ) *
                p09ComplexNorm2 rp +
              Real.sqrt ((plan.stage s).radix : ℝ) *
                (pcoef * S * p09ComplexNorm2 x) := by
            apply add_le_add hs'
            rw [show p09ComplexNorm2 e2 =
                Real.sqrt ((plan.stage s).radix : ℝ) *
                  p09ComplexNorm2 (fun i => rp i - ep i) by exact hexactdiff]
            gcongr
      have hpoly : scoef * (1 + pcoef) + pcoef ≤
          (C + c) * model.epsilon + D * model.epsilon ^ 2 := by
        have he3 : model.epsilon ^ 3 ≤ model.epsilon ^ 2 := by
          nlinarith [sq_nonneg model.epsilon]
        have he4 : model.epsilon ^ 4 ≤ model.epsilon ^ 2 := by
          nlinarith [sq_nonneg model.epsilon,
            sq_nonneg (model.epsilon ^ 2 - model.epsilon)]
        have hcC := mul_le_mul_of_nonneg_left he3 (by positivity : 0 ≤ c * C)
        have hcP := mul_le_mul_of_nonneg_left he3 (by positivity : 0 ≤ c * P)
        have hQC := mul_le_mul_of_nonneg_left he3 (by positivity : 0 ≤ Q * C)
        have hQP := mul_le_mul_of_nonneg_left he4 (by positivity : 0 ≤ Q * P)
        dsimp [scoef, pcoef, D]
        nlinarith
      have hscale : p09PlanPrefixScale plan (k + 1) hk =
          S * Real.sqrt ((plan.stage s).radix : ℝ) := by
        unfold p09PlanPrefixScale
        rw [Fin.prod_univ_castSucc]
        congr 1
      have hcoeff : p09PlanPrefixCoeff plan γ (k + 1) hk = C + c := by
        unfold p09PlanPrefixCoeff
        rw [Fin.sum_univ_castSucc]
        congr 1
      calc
        p09ComplexNorm2 (fun i =>
            p09RoundedPlanPrefix plan model (k + 1) hk x i -
              p09ExactPlanPrefix plan (k + 1) hk x i) ≤
            scoef * Real.sqrt ((plan.stage s).radix : ℝ) *
                p09ComplexNorm2 rp +
              Real.sqrt ((plan.stage s).radix : ℝ) *
                (pcoef * S * p09ComplexNorm2 x) := herr
        _ ≤ (scoef * (1 + pcoef) + pcoef) *
              (S * Real.sqrt ((plan.stage s).radix : ℝ)) *
                p09ComplexNorm2 x := by
          calc
            scoef * Real.sqrt ((plan.stage s).radix : ℝ) *
                  p09ComplexNorm2 rp +
                Real.sqrt ((plan.stage s).radix : ℝ) *
                  (pcoef * S * p09ComplexNorm2 x) ≤
              scoef * Real.sqrt ((plan.stage s).radix : ℝ) *
                    ((1 + pcoef) * S * p09ComplexNorm2 x) +
                Real.sqrt ((plan.stage s).radix : ℝ) *
                  (pcoef * S * p09ComplexNorm2 x) := by
                    gcongr
            _ = (scoef * (1 + pcoef) + pcoef) *
                (S * Real.sqrt ((plan.stage s).radix : ℝ)) *
                  p09ComplexNorm2 x := by ring
        _ ≤ ((C + c) * model.epsilon + D * model.epsilon ^ 2) *
              (S * Real.sqrt ((plan.stage s).radix : ℝ)) *
                p09ComplexNorm2 x := by
          exact mul_le_mul_of_nonneg_right
            (mul_le_mul_of_nonneg_right hpoly
              (mul_nonneg hS (Real.sqrt_nonneg _)))
            (by simp [p09ComplexNorm2])
        _ = (p09PlanPrefixCoeff plan γ (k + 1) hk * model.epsilon +
              D * model.epsilon ^ 2) *
            p09PlanPrefixScale plan (k + 1) hk * p09ComplexNorm2 x := by
          rw [hscale, hcoeff]

private lemma p09ExactPlanPrefix_eq_apply {n : ℕ} [NeZero n]
    (plan : P09MixedRadixFftPlan n) (x : ZMod n → ℂ) :
    p09ExactPlanPrefix plan plan.stageCount (le_refl _) x =
      p09ApplyMixedRadixStages plan.stage x := by
  have haux : ∀ (k : ℕ) (hk : k ≤ plan.stageCount),
      p09ExactPlanPrefix plan k hk x =
        (List.ofFn (fun i : Fin k => plan.stage (Fin.castLE hk i))).foldl
          (fun state stage => p09MixedRadixStageApply stage state) x := by
    intro k
    induction k with
    | zero => intro hk; simp [p09ExactPlanPrefix]
    | succ k ih =>
        intro hk
        rw [p09ExactPlanPrefix, List.ofFn_succ', List.concat_eq_append,
          List.foldl_concat]
        let hk' := Nat.le_of_succ_le hk
        have hlist :
            List.ofFn (fun i : Fin k => plan.stage (Fin.castLE hk i.castSucc)) =
              List.ofFn (fun i : Fin k => plan.stage (Fin.castLE hk' i)) := by
          apply congrArg List.ofFn
          funext i
          apply congrArg plan.stage
          apply Fin.ext
          rfl
        rw [hlist, ← ih hk']
        congr
  rw [haux]
  unfold p09ApplyMixedRadixStages
  congr 2

private lemma p09RoundedPlanPrefix_eq_apply {n : ℕ} [NeZero n]
    (plan : P09MixedRadixFftPlan n) (model : P09WilkinsonModel)
    (x : ZMod n → ℂ) :
    p09RoundedPlanPrefix plan model plan.stageCount (le_refl _) x =
      p09ApplyRoundedMixedRadixStages model plan.stage x := by
  have haux : ∀ (k : ℕ) (hk : k ≤ plan.stageCount),
      p09RoundedPlanPrefix plan model k hk x =
        (List.ofFn (fun i : Fin k => plan.stage (Fin.castLE hk i))).foldl
          (fun state stage => p09RoundedMixedRadixStageApply model stage state) x := by
    intro k
    induction k with
    | zero => intro hk; simp [p09RoundedPlanPrefix]
    | succ k ih =>
        intro hk
        rw [p09RoundedPlanPrefix, List.ofFn_succ', List.concat_eq_append,
          List.foldl_concat]
        let hk' := Nat.le_of_succ_le hk
        have hlist :
            List.ofFn (fun i : Fin k => plan.stage (Fin.castLE hk i.castSucc)) =
              List.ofFn (fun i : Fin k => plan.stage (Fin.castLE hk' i)) := by
          apply congrArg List.ofFn
          funext i
          apply congrArg plan.stage
          apply Fin.ext
          rfl
        rw [hlist, ← ih hk']
        congr
  rw [haux]
  unfold p09ApplyRoundedMixedRadixStages
  congr 2

private lemma p09PlanPrefixScale_full {n : ℕ} [NeZero n]
    (plan : P09MixedRadixFftPlan n) :
    p09PlanPrefixScale plan plan.stageCount (le_refl _) = Real.sqrt (n : ℝ) := by
  unfold p09PlanPrefixScale
  have hsqrt := Real.sqrt_prod (Finset.univ : Finset (Fin plan.stageCount))
    (fun i hi => Nat.cast_nonneg (plan.stage i).radix)
  have hprod : (∏ i : Fin plan.stageCount, ((plan.stage i).radix : ℝ)) =
      (n : ℝ) := by exact_mod_cast plan.order_factorization
  calc
    (∏ i : Fin plan.stageCount,
        Real.sqrt ((plan.stage (Fin.castLE (le_refl _) i)).radix : ℝ)) =
        ∏ i : Fin plan.stageCount, Real.sqrt ((plan.stage i).radix : ℝ) := by
          apply Finset.prod_congr rfl
          intro i hi
          rw [Fin.castLE_refl]
    _ = Real.sqrt (∏ i : Fin plan.stageCount, ((plan.stage i).radix : ℝ)) :=
      hsqrt.symm
    _ = Real.sqrt (n : ℝ) := by rw [hprod]

private lemma p09_fin_sum_before_last (r : ℕ) (hr : 0 < r) (c : ℝ) :
    (∑ i : Fin r, if i.val + 1 < r then c else 0) = ((r : ℝ) - 1) * c := by
  cases r with
  | zero => omega
  | succ r =>
      rw [Fin.sum_univ_castSucc]
      have hcast (i : Fin r) : i.castSucc.val + 1 < r + 1 := by
        exact Nat.succ_lt_succ i.isLt
      have hlast : ¬(Fin.last r).val + 1 < r + 1 := by simp
      simp only [hcast, if_true, hlast, if_false, add_zero]
      simp

private lemma p09PlanPrefixCoeff_full {n : ℕ} [NeZero n]
    (plan : P09MixedRadixFftPlan n) (γ : ℝ) :
    p09PlanPrefixCoeff plan γ plan.stageCount (le_refl _) = p09K plan γ := by
  unfold p09PlanPrefixCoeff p09K
  rw [Finset.sum_add_distrib]
  congr 1
  calc
    (∑ i : Fin plan.stageCount,
        if (plan.stage (Fin.castLE (le_refl _) i)).useTwiddle then
          3 + 2 * γ else 0) =
      ∑ i : Fin plan.stageCount,
        if i.val + 1 < plan.stageCount then 3 + 2 * γ else 0 := by
          apply Finset.sum_congr rfl
          intro i hi
          rw [Fin.castLE_refl, plan.twiddle_pattern]
          simp
    _ = ((plan.stageCount : ℝ) - 1) * (3 + 2 * γ) :=
      p09_fin_sum_before_last plan.stageCount plan.stageCount_pos (3 + 2 * γ)

private lemma p09Permute_norm {n : ℕ} [NeZero n]
    (permutation : ZMod n ≃ ZMod n) (x : ZMod n → ℂ) :
    p09ComplexNorm2 (p09Permute permutation x) = p09ComplexNorm2 x := by
  rw [p09ComplexNorm2, p09ComplexNorm2Sq]
  congr 1
  exact Equiv.sum_comp permutation (fun i : ZMod n => ‖x i‖ ^ 2)

private lemma p09RoundedFftApply_asymptotic {n : ℕ} [NeZero n]
    (plan : P09MixedRadixFftPlan n) (γ : ℝ) (hγ : 0 ≤ γ) :
    ∃ D : ℝ, 0 ≤ D ∧
      ∀ (model : P09WilkinsonModel), model.gamma = γ → model.epsilon ≤ 1 →
        ∀ x : ZMod n → ℂ,
          p09ComplexNorm2 (fun i =>
            p09RoundedFftApply plan model x i - p09FourierTransform x i) ≤
          (p09K plan γ * model.epsilon + D * model.epsilon ^ 2) *
            Real.sqrt (n : ℝ) * p09ComplexNorm2 x := by
  rcases p09PlanPrefix_asymptotic plan γ hγ plan.stageCount (le_refl _) with
    ⟨D, hD, h⟩
  refine ⟨D, hD, ?_⟩
  intro model hmg heone x
  have hp := h model hmg heone x
  rw [p09ExactPlanPrefix_eq_apply, p09RoundedPlanPrefix_eq_apply,
    p09PlanPrefixCoeff_full, p09PlanPrefixScale_full] at hp
  have hexact := plan.exact_factorization x
  have hfun : (fun i =>
      p09RoundedFftApply plan model x i - p09FourierTransform x i) =
      p09Permute plan.finalPermutation (fun i =>
        p09ApplyRoundedMixedRadixStages model plan.stage x i -
          p09ApplyMixedRadixStages plan.stage x i) := by
    funext i
    rw [← hexact]
    rfl
  rw [hfun, p09Permute_norm]
  exact hp

private abbrev P09AxisFiber {m : ℕ} (axis : Fin m → P09FftAxis)
    (i : Fin m) :=
  (j : {j : Fin m // j ≠ i}) → ZMod (axis j).order

private noncomputable def p09MultiIndexAxisEquiv {m : ℕ}
    (axis : Fin m → P09FftAxis) (i : Fin m) :
    P09MultiIndex axis ≃ ZMod (axis i).order × P09AxisFiber axis i where
  toFun index := (index i, fun j => index j)
  invFun p := fun j => if h : j = i then h ▸ p.1 else p.2 ⟨j, h⟩
  left_inv index := by
    funext j
    by_cases h : j = i
    · subst j
      simp
    · simp [h]
  right_inv p := by
    apply Prod.ext
    · simp
    · funext j
      simp [j.property]

private lemma p09MultiIndexAxisEquiv_update {m : ℕ}
    (axis : Fin m → P09FftAxis) (i : Fin m)
    (p : ZMod (axis i).order × P09AxisFiber axis i)
    (j : ZMod (axis i).order) :
    Function.update ((p09MultiIndexAxisEquiv axis i).symm p) i j =
      (p09MultiIndexAxisEquiv axis i).symm (j, p.2) := by
  funext k
  by_cases h : k = i
  · subst k
    simp [p09MultiIndexAxisEquiv]
  · simp [p09MultiIndexAxisEquiv, Function.update, h]

private lemma p09MultiIndexAxisEquiv_symm_coord {m : ℕ}
    (axis : Fin m → P09FftAxis) (i : Fin m)
    (p : ZMod (axis i).order × P09AxisFiber axis i) :
    (p09MultiIndexAxisEquiv axis i).symm p i = p.1 := by
  have h := congrArg Prod.fst
    ((p09MultiIndexAxisEquiv axis i).apply_symm_apply p)
  exact h

private lemma p09CoordinateTransform_fiber {m : ℕ}
    (axis : Fin m → P09FftAxis) (i : Fin m)
    (x : P09MultiArray axis)
    (p : ZMod (axis i).order × P09AxisFiber axis i) :
    p09CoordinateTransform axis i x ((p09MultiIndexAxisEquiv axis i).symm p) =
      p09FourierTransform
        (fun j => x ((p09MultiIndexAxisEquiv axis i).symm (j, p.2))) p.1 := by
  unfold p09CoordinateTransform p09FourierTransform
  apply Finset.sum_congr rfl
  intro j hj
  rw [p09MultiIndexAxisEquiv_update]
  rw [p09MultiIndexAxisEquiv_symm_coord]

private lemma p09RoundedCoordinateTransform_fiber {m : ℕ}
    (axis : Fin m → P09FftAxis) (i : Fin m)
    (model : P09WilkinsonModel) (x : P09MultiArray axis)
    (p : ZMod (axis i).order × P09AxisFiber axis i) :
    p09RoundedCoordinateTransform axis i model x
        ((p09MultiIndexAxisEquiv axis i).symm p) =
      p09RoundedFftApply (axis i).plan model
        (fun j => x ((p09MultiIndexAxisEquiv axis i).symm (j, p.2))) p.1 := by
  unfold p09RoundedCoordinateTransform
  have hinput : (fun j =>
      x (Function.update ((p09MultiIndexAxisEquiv axis i).symm p) i j)) =
      (fun j => x ((p09MultiIndexAxisEquiv axis i).symm (j, p.2))) := by
    funext j
    rw [p09MultiIndexAxisEquiv_update]
  rw [hinput, p09MultiIndexAxisEquiv_symm_coord]

private lemma p09RoundedCoordinateTransform_asymptotic {m : ℕ}
    (axis : Fin m → P09FftAxis) (i : Fin m)
    (γ : ℝ) (hγ : 0 ≤ γ) : ∃ D : ℝ, 0 ≤ D ∧
      ∀ (model : P09WilkinsonModel), model.gamma = γ → model.epsilon ≤ 1 →
        ∀ x : P09MultiArray axis,
          p09MultiNorm2 (fun index =>
            p09RoundedCoordinateTransform axis i model x index -
              p09CoordinateTransform axis i x index) ≤
          (p09AxisK (axis i) γ * model.epsilon + D * model.epsilon ^ 2) *
            Real.sqrt ((axis i).order : ℝ) * p09MultiNorm2 x := by
  letI (j : Fin m) : NeZero (axis j).order :=
    ⟨Nat.ne_of_gt (axis j).order_pos⟩
  rcases p09RoundedFftApply_asymptotic (axis i).plan γ hγ with ⟨D, hD, haxis⟩
  refine ⟨D, hD, ?_⟩
  intro model hmg heone x
  let F := P09AxisFiber axis i
  let eqv := p09MultiIndexAxisEquiv axis i
  let xslice : F → ZMod (axis i).order → ℂ := fun f j => x (eqv.symm (j, f))
  let errslice : F → ZMod (axis i).order → ℂ := fun f k =>
    p09RoundedFftApply (axis i).plan model (xslice f) k -
      p09FourierTransform (xslice f) k
  let C : ℝ := p09AxisK (axis i) γ * model.epsilon + D * model.epsilon ^ 2
  have hK : 0 ≤ p09AxisK (axis i) γ := by
    unfold p09AxisK p09K
    have ha : ∀ s : Fin (axis i).plan.stageCount,
        0 ≤ p09Alpha ((axis i).plan.stage s).radix γ := by
      intro s
      simp only [p09Alpha]
      split_ifs <;> positivity
    have hr : (1 : ℝ) ≤ (axis i).plan.stageCount := by
      exact_mod_cast (axis i).plan.stageCount_pos
    exact add_nonneg (Finset.sum_nonneg (fun s hs => ha s))
      (mul_nonneg (by nlinarith) (by positivity))
  have hC : 0 ≤ C := by
    dsimp [C]
    exact add_nonneg (mul_nonneg hK (le_of_lt model.epsilon_pos))
      (mul_nonneg hD (sq_nonneg _))
  have hf (f : F) : p09ComplexNorm2 (errslice f) ≤
      C * Real.sqrt ((axis i).order : ℝ) * p09ComplexNorm2 (xslice f) := by
    simpa [C, p09AxisK, errslice, xslice] using haxis model hmg heone (xslice f)
  have hfsq (f : F) :
      (∑ k : ZMod (axis i).order, ‖errslice f k‖ ^ 2) ≤
        (C * Real.sqrt ((axis i).order : ℝ)) ^ 2 *
          ∑ j : ZMod (axis i).order, ‖xslice f j‖ ^ 2 := by
    have hs := pow_le_pow_left₀ (by simp [p09ComplexNorm2]) (hf f) 2
    simp only [p09ComplexNorm2, p09ComplexNorm2Sq] at hs
    have he : 0 ≤ ∑ k : ZMod (axis i).order, ‖errslice f k‖ ^ 2 := by positivity
    have hx : 0 ≤ ∑ j : ZMod (axis i).order, ‖xslice f j‖ ^ 2 := by positivity
    rw [Real.sq_sqrt he, mul_pow, Real.sq_sqrt hx] at hs
    exact hs
  have hsums : (∑ f : F, ∑ k : ZMod (axis i).order, ‖errslice f k‖ ^ 2) ≤
      (C * Real.sqrt ((axis i).order : ℝ)) ^ 2 *
        ∑ f : F, ∑ j : ZMod (axis i).order, ‖xslice f j‖ ^ 2 := by
    calc
      _ ≤ ∑ f : F, (C * Real.sqrt ((axis i).order : ℝ)) ^ 2 *
          ∑ j : ZMod (axis i).order, ‖xslice f j‖ ^ 2 := by
            gcongr with f
            exact hfsq f
      _ = _ := by rw [Finset.mul_sum]
  let err : P09MultiArray axis := fun index =>
    p09RoundedCoordinateTransform axis i model x index -
      p09CoordinateTransform axis i x index
  have herrfiber (p : ZMod (axis i).order × F) :
      err (eqv.symm p) = errslice p.2 p.1 := by
    dsimp [err, errslice]
    rw [p09RoundedCoordinateTransform_fiber,
      p09CoordinateTransform_fiber]
  have houtsum : (∑ index : P09MultiIndex axis, ‖err index‖ ^ 2) =
      ∑ f : F, ∑ k : ZMod (axis i).order, ‖errslice f k‖ ^ 2 := by
    rw [← Equiv.sum_comp eqv.symm
      (fun index : P09MultiIndex axis => ‖err index‖ ^ 2)]
    rw [Fintype.sum_prod_type]
    rw [Finset.sum_comm]
    apply Finset.sum_congr rfl
    intro f hfmem
    apply Finset.sum_congr rfl
    intro k hkmem
    rw [herrfiber]
  have hinsum : (∑ index : P09MultiIndex axis, ‖x index‖ ^ 2) =
      ∑ f : F, ∑ j : ZMod (axis i).order, ‖xslice f j‖ ^ 2 := by
    rw [← Equiv.sum_comp eqv.symm
      (fun index : P09MultiIndex axis => ‖x index‖ ^ 2)]
    rw [Fintype.sum_prod_type]
    rw [Finset.sum_comm]
  change p09MultiNorm2 err ≤ C * Real.sqrt ((axis i).order : ℝ) * p09MultiNorm2 x
  simp only [p09MultiNorm2]
  rw [EuclideanSpace.norm_eq, EuclideanSpace.norm_eq]
  change Real.sqrt (∑ index : P09MultiIndex axis, ‖err index‖ ^ 2) ≤
    C * Real.sqrt ((axis i).order : ℝ) *
      Real.sqrt (∑ index : P09MultiIndex axis, ‖x index‖ ^ 2)
  rw [houtsum, hinsum]
  have he : 0 ≤ ∑ f : F,
      ∑ k : ZMod (axis i).order, ‖errslice f k‖ ^ 2 := by positivity
  have hx : 0 ≤ ∑ f : F,
      ∑ j : ZMod (axis i).order, ‖xslice f j‖ ^ 2 := by positivity
  apply (sq_le_sq₀ (Real.sqrt_nonneg _) (by positivity)).mp
  rw [Real.sq_sqrt he, mul_pow, Real.sq_sqrt hx]
  exact hsums

private lemma p09MultiNorm2_add {m : ℕ} (axis : Fin m → P09FftAxis)
    (x y : P09MultiArray axis) :
    p09MultiNorm2 (fun index => x index + y index) ≤
      p09MultiNorm2 x + p09MultiNorm2 y := by
  unfold p09MultiNorm2
  simpa using norm_add_le
    (WithLp.toLp 2 x : EuclideanSpace ℂ (P09MultiIndex axis))
    (WithLp.toLp 2 y : EuclideanSpace ℂ (P09MultiIndex axis))

private lemma p09MultiRms_add {m : ℕ} (axis : Fin m → P09FftAxis)
    (x y : P09MultiArray axis) :
    p09MultiRms (fun index => x index + y index) ≤
      p09MultiRms x + p09MultiRms y := by
  unfold p09MultiRms
  rw [← add_div]
  exact div_le_div_of_nonneg_right (p09MultiNorm2_add axis x y)
    (Real.sqrt_nonneg _)

private lemma p09MultiRms_nonneg {m : ℕ} (axis : Fin m → P09FftAxis)
    (x : P09MultiArray axis) : 0 ≤ p09MultiRms x := by
  unfold p09MultiRms
  exact div_nonneg (by simp [p09MultiNorm2]) (Real.sqrt_nonneg _)

private lemma p09MultiRms_zero {m : ℕ} (axis : Fin m → P09FftAxis) :
    p09MultiRms (axis := axis)
      (fun _ : P09MultiIndex axis => (0 : ℂ)) = 0 := by
  unfold p09MultiRms p09MultiNorm2
  change ‖(0 : EuclideanSpace ℂ (P09MultiIndex axis))‖ /
      Real.sqrt (p09MultiCardinality axis : ℝ) = 0
  simp

private lemma p09FourierTransform_norm {n : ℕ} [NeZero n]
    (plan : P09MixedRadixFftPlan n) (x : ZMod n → ℂ) :
    p09ComplexNorm2 (p09FourierTransform x) =
      Real.sqrt (n : ℝ) * p09ComplexNorm2 x := by
  have h := plan.fourier_rms_scaling x
  unfold p09ComplexRms at h
  have hnNat : 0 < n := Nat.pos_of_ne_zero (NeZero.ne n)
  have hn : 0 < Real.sqrt (n : ℝ) := by positivity
  field_simp [ne_of_gt hn] at h
  exact h

private lemma p09CoordinateTransform_norm {m : ℕ}
    (axis : Fin m → P09FftAxis) (i : Fin m)
    (x : P09MultiArray axis) :
    p09MultiNorm2 (p09CoordinateTransform axis i x) =
      Real.sqrt ((axis i).order : ℝ) * p09MultiNorm2 x := by
  letI (j : Fin m) : NeZero (axis j).order :=
    ⟨Nat.ne_of_gt (axis j).order_pos⟩
  let F := P09AxisFiber axis i
  let eqv := p09MultiIndexAxisEquiv axis i
  let xslice : F → ZMod (axis i).order → ℂ :=
    fun f j => x (eqv.symm (j, f))
  let outslice : F → ZMod (axis i).order → ℂ :=
    fun f => p09FourierTransform (xslice f)
  have hf (f : F) : p09ComplexNorm2 (outslice f) =
      Real.sqrt ((axis i).order : ℝ) * p09ComplexNorm2 (xslice f) := by
    exact p09FourierTransform_norm (axis i).plan (xslice f)
  have hfsq (f : F) :
      (∑ k : ZMod (axis i).order, ‖outslice f k‖ ^ 2) =
        ((axis i).order : ℝ) *
          ∑ j : ZMod (axis i).order, ‖xslice f j‖ ^ 2 := by
    have hs := congrArg (fun z : ℝ => z ^ 2) (hf f)
    simp only [p09ComplexNorm2, p09ComplexNorm2Sq] at hs
    have ho : 0 ≤ ∑ k : ZMod (axis i).order, ‖outslice f k‖ ^ 2 := by
      positivity
    have hx : 0 ≤ ∑ j : ZMod (axis i).order, ‖xslice f j‖ ^ 2 := by
      positivity
    rw [Real.sq_sqrt ho, mul_pow, Real.sq_sqrt hx,
      Real.sq_sqrt (by positivity : 0 ≤ ((axis i).order : ℝ))] at hs
    exact hs
  have houtsum :
      (∑ index : P09MultiIndex axis,
          ‖p09CoordinateTransform axis i x index‖ ^ 2) =
        ∑ f : F, ∑ k : ZMod (axis i).order, ‖outslice f k‖ ^ 2 := by
    rw [← Equiv.sum_comp eqv.symm
      (fun index : P09MultiIndex axis =>
        ‖p09CoordinateTransform axis i x index‖ ^ 2)]
    rw [Fintype.sum_prod_type, Finset.sum_comm]
    apply Finset.sum_congr rfl
    intro f hfmem
    apply Finset.sum_congr rfl
    intro k hkmem
    dsimp [outslice, xslice]
    rw [p09CoordinateTransform_fiber]
  have hinsum : (∑ index : P09MultiIndex axis, ‖x index‖ ^ 2) =
      ∑ f : F, ∑ j : ZMod (axis i).order, ‖xslice f j‖ ^ 2 := by
    rw [← Equiv.sum_comp eqv.symm
      (fun index : P09MultiIndex axis => ‖x index‖ ^ 2)]
    rw [Fintype.sum_prod_type, Finset.sum_comm]
  simp only [p09MultiNorm2]
  rw [EuclideanSpace.norm_eq, EuclideanSpace.norm_eq]
  change Real.sqrt (∑ index : P09MultiIndex axis,
      ‖p09CoordinateTransform axis i x index‖ ^ 2) =
    Real.sqrt ((axis i).order : ℝ) *
      Real.sqrt (∑ index : P09MultiIndex axis, ‖x index‖ ^ 2)
  rw [houtsum, hinsum]
  have hsums : (∑ f : F, ∑ k : ZMod (axis i).order,
      ‖outslice f k‖ ^ 2) =
      ((axis i).order : ℝ) *
        ∑ f : F, ∑ j : ZMod (axis i).order, ‖xslice f j‖ ^ 2 := by
    calc
      _ = ∑ f : F, ((axis i).order : ℝ) *
          ∑ j : ZMod (axis i).order, ‖xslice f j‖ ^ 2 := by
            apply Finset.sum_congr rfl
            intro f hfmem
            exact hfsq f
      _ = _ := by rw [Finset.mul_sum]
  rw [hsums, Real.sqrt_mul (by positivity : 0 ≤ ((axis i).order : ℝ))]

private lemma p09CoordinateTransform_rms {m : ℕ}
    (axis : Fin m → P09FftAxis) (i : Fin m)
    (x : P09MultiArray axis) :
    p09MultiRms (p09CoordinateTransform axis i x) =
      Real.sqrt ((axis i).order : ℝ) * p09MultiRms x := by
  unfold p09MultiRms
  rw [p09CoordinateTransform_norm]
  ring

private lemma p09RoundedCoordinateTransform_rms_asymptotic {m : ℕ}
    (axis : Fin m → P09FftAxis) (i : Fin m)
    (model : P09WilkinsonModel) (x : P09MultiArray axis)
    (C : ℝ)
    (h : p09MultiNorm2 (fun index =>
        p09RoundedCoordinateTransform axis i model x index -
          p09CoordinateTransform axis i x index) ≤
      C * Real.sqrt ((axis i).order : ℝ) * p09MultiNorm2 x) :
    p09MultiRms (fun index =>
        p09RoundedCoordinateTransform axis i model x index -
          p09CoordinateTransform axis i x index) ≤
      C * Real.sqrt ((axis i).order : ℝ) * p09MultiRms x := by
  unfold p09MultiRms
  calc
    _ ≤ (C * Real.sqrt ((axis i).order : ℝ) * p09MultiNorm2 x) /
        Real.sqrt (p09MultiCardinality axis : ℝ) :=
      div_le_div_of_nonneg_right h (Real.sqrt_nonneg _)
    _ = C * Real.sqrt ((axis i).order : ℝ) *
        (p09MultiNorm2 x / Real.sqrt (p09MultiCardinality axis : ℝ)) := by
      ring

private lemma p09CoordinateTransform_sub {m : ℕ}
    (axis : Fin m → P09FftAxis) (i : Fin m)
    (x y : P09MultiArray axis) :
    p09CoordinateTransform axis i (fun index => x index - y index) =
      fun index => p09CoordinateTransform axis i x index -
        p09CoordinateTransform axis i y index := by
  funext index
  simp only [p09CoordinateTransform, mul_sub, Finset.sum_sub_distrib]

private lemma p09CoordinateTransformNat_sub {m : ℕ}
    (axis : Fin m → P09FftAxis) (i : ℕ)
    (x y : P09MultiArray axis) :
    p09CoordinateTransformNat axis i (fun index => x index - y index) =
      fun index => p09CoordinateTransformNat axis i x index -
        p09CoordinateTransformNat axis i y index := by
  unfold p09CoordinateTransformNat
  split_ifs with hi
  · exact p09CoordinateTransform_sub axis ⟨i, hi⟩ x y
  · rfl

private lemma p09ApplyCoordinatePrefix_sub {m : ℕ}
    (axis : Fin m → P09FftAxis) (k : ℕ)
    (x y : P09MultiArray axis) :
    p09ApplyCoordinatePrefix axis k (fun index => x index - y index) =
      fun index => p09ApplyCoordinatePrefix axis k x index -
        p09ApplyCoordinatePrefix axis k y index := by
  induction k generalizing x y with
  | zero => rfl
  | succ k ih =>
      rw [p09ApplyCoordinatePrefix, p09CoordinateTransformNat_sub, ih]
      rfl

private noncomputable def p09RoundedCoordinatePrefix {m : ℕ}
    (axis : Fin m → P09FftAxis) (model : P09WilkinsonModel) :
    ∀ k : ℕ, k ≤ m → P09MultiArray axis → P09MultiArray axis
  | 0, _, x => x
  | k + 1, hk, x =>
      p09RoundedCoordinatePrefix axis model k (Nat.le_of_succ_le hk)
        (p09RoundedCoordinateTransform axis
          ⟨k, Nat.lt_of_succ_le hk⟩ model x)

private noncomputable def p09MultiPrefixScale {m : ℕ} [NeZero m]
    (plan : P09MultidimensionalFftPlan m)
    (k : ℕ) (hk : k ≤ m) : ℝ :=
  Real.sqrt (p09PrefixOrderProduct plan.axis k hk : ℝ)

private noncomputable def p09MultiPrefixCoeff {m : ℕ} [NeZero m]
    (plan : P09MultidimensionalFftPlan m) (γ : ℝ)
    (k : ℕ) (hk : k ≤ m) : ℝ :=
  ∑ i : Fin k, p09AxisK (plan.axis (Fin.castLE hk i)) γ

private lemma p09AxisK_nonneg (axis : P09FftAxis) (γ : ℝ) (hγ : 0 ≤ γ) :
    0 ≤ p09AxisK axis γ := by
  unfold p09AxisK
  rw [← p09PlanPrefixCoeff_full axis.plan γ]
  exact p09PlanPrefixCoeff_nonneg axis.plan γ hγ
    axis.plan.stageCount (le_refl _)

private lemma p09MultiPrefixScale_nonneg {m : ℕ} [NeZero m]
    (plan : P09MultidimensionalFftPlan m)
    (k : ℕ) (hk : k ≤ m) :
    0 ≤ p09MultiPrefixScale plan k hk := by
  exact Real.sqrt_nonneg _

private lemma p09MultiPrefixCoeff_nonneg {m : ℕ} [NeZero m]
    (plan : P09MultidimensionalFftPlan m) (γ : ℝ) (hγ : 0 ≤ γ)
    (k : ℕ) (hk : k ≤ m) :
    0 ≤ p09MultiPrefixCoeff plan γ k hk := by
  unfold p09MultiPrefixCoeff
  apply Finset.sum_nonneg
  intro i hi
  exact p09AxisK_nonneg _ γ hγ

private lemma p09MultiPrefixScale_succ {m : ℕ} [NeZero m]
    (plan : P09MultidimensionalFftPlan m)
    (k : ℕ) (hk : k + 1 ≤ m) :
    p09MultiPrefixScale plan (k + 1) hk =
      p09MultiPrefixScale plan k (Nat.le_of_succ_le hk) *
        Real.sqrt ((plan.axis ⟨k, Nat.lt_of_succ_le hk⟩).order : ℝ) := by
  let hk' : k ≤ m := Nat.le_of_succ_le hk
  let i : Fin m := ⟨k, Nat.lt_of_succ_le hk⟩
  have hprod : p09PrefixOrderProduct plan.axis (k + 1) hk =
      p09PrefixOrderProduct plan.axis k hk' * (plan.axis i).order := by
    unfold p09PrefixOrderProduct
    rw [Fin.prod_univ_castSucc]
    congr 1
  unfold p09MultiPrefixScale
  rw [hprod]
  push_cast
  rw [Real.sqrt_mul (by positivity : 0 ≤
    (p09PrefixOrderProduct plan.axis k hk' : ℝ))]

private lemma p09MultiPrefixCoeff_succ {m : ℕ} [NeZero m]
    (plan : P09MultidimensionalFftPlan m) (γ : ℝ)
    (k : ℕ) (hk : k + 1 ≤ m) :
    p09MultiPrefixCoeff plan γ (k + 1) hk =
      p09MultiPrefixCoeff plan γ k (Nat.le_of_succ_le hk) +
        p09AxisK (plan.axis ⟨k, Nat.lt_of_succ_le hk⟩) γ := by
  unfold p09MultiPrefixCoeff
  rw [Fin.sum_univ_castSucc]
  congr 1

private lemma p09RoundedCoordinatePrefix_asymptotic {m : ℕ} [NeZero m]
    (plan : P09MultidimensionalFftPlan m) (γ : ℝ) (hγ : 0 ≤ γ)
    (k : ℕ) (hk : k ≤ m) : ∃ D : ℝ, 0 ≤ D ∧
      ∀ (model : P09WilkinsonModel), model.gamma = γ → model.epsilon ≤ 1 →
        ∀ x : P09MultiArray plan.axis,
          p09MultiRms (fun index =>
            p09RoundedCoordinatePrefix plan.axis model k hk x index -
              p09ApplyCoordinatePrefix plan.axis k x index) ≤
          (p09MultiPrefixCoeff plan γ k hk * model.epsilon +
              D * model.epsilon ^ 2) *
            p09MultiPrefixScale plan k hk * p09MultiRms x := by
  induction k with
  | zero =>
      refine ⟨0, by positivity, ?_⟩
      intro model hmg heone x
      change p09MultiRms (fun index => x index - x index) ≤
        (p09MultiPrefixCoeff plan γ 0 hk * model.epsilon +
          0 * model.epsilon ^ 2) * p09MultiPrefixScale plan 0 hk *
            p09MultiRms x
      simp [p09MultiPrefixCoeff, p09MultiPrefixScale,
        p09PrefixOrderProduct, p09MultiRms_zero]
  | succ k ih =>
      let hk' : k ≤ m := Nat.le_of_succ_le hk
      let i : Fin m := ⟨k, Nat.lt_of_succ_le hk⟩
      rcases ih hk' with ⟨P, hP, hprev⟩
      rcases p09RoundedCoordinateTransform_asymptotic
          plan.axis i γ hγ with ⟨Q, hQ, hstage⟩
      let C : ℝ := p09MultiPrefixCoeff plan γ k hk'
      let c : ℝ := p09AxisK (plan.axis i) γ
      let D : ℝ := P + Q + C * c + P * c + C * Q + P * Q
      have hC : 0 ≤ C := p09MultiPrefixCoeff_nonneg plan γ hγ k hk'
      have hc : 0 ≤ c := p09AxisK_nonneg (plan.axis i) γ hγ
      refine ⟨D, by dsimp [D]; positivity, ?_⟩
      intro model hmg heone x
      let rx : P09MultiArray plan.axis :=
        p09RoundedCoordinateTransform plan.axis i model x
      let ex : P09MultiArray plan.axis :=
        p09CoordinateTransform plan.axis i x
      let S : ℝ := p09MultiPrefixScale plan k hk'
      let pcoef : ℝ := C * model.epsilon + P * model.epsilon ^ 2
      let scoef : ℝ := c * model.epsilon + Q * model.epsilon ^ 2
      have he : 0 ≤ model.epsilon := le_of_lt model.epsilon_pos
      have hS : 0 ≤ S := p09MultiPrefixScale_nonneg plan k hk'
      have hpcoef : 0 ≤ pcoef := by dsimp [pcoef]; positivity
      have hscoef : 0 ≤ scoef := by dsimp [scoef]; positivity
      have hp : p09MultiRms (fun index =>
          p09RoundedCoordinatePrefix plan.axis model k hk' rx index -
            p09ApplyCoordinatePrefix plan.axis k rx index) ≤
          pcoef * S * p09MultiRms rx := by
        simpa [C, S, pcoef] using hprev model hmg heone rx
      have hsNorm := hstage model hmg heone x
      have hs : p09MultiRms (fun index => rx index - ex index) ≤
          scoef * Real.sqrt ((plan.axis i).order : ℝ) * p09MultiRms x := by
        apply p09RoundedCoordinateTransform_rms_asymptotic
          plan.axis i model x scoef
        simpa [rx, ex, c, scoef, p09AxisK] using hsNorm
      have hex : p09MultiRms ex =
          Real.sqrt ((plan.axis i).order : ℝ) * p09MultiRms x := by
        exact p09CoordinateTransform_rms plan.axis i x
      have hrnorm : p09MultiRms rx ≤
          (1 + scoef) * Real.sqrt ((plan.axis i).order : ℝ) *
            p09MultiRms x := by
        have htri := p09MultiRms_add plan.axis ex
          (fun index => rx index - ex index)
        have hid : (fun index => ex index + (rx index - ex index)) = rx := by
          funext index
          ring
        rw [hid] at htri
        calc
          p09MultiRms rx ≤ p09MultiRms ex +
              p09MultiRms (fun index => rx index - ex index) := htri
          _ = Real.sqrt ((plan.axis i).order : ℝ) * p09MultiRms x +
              p09MultiRms (fun index => rx index - ex index) := by rw [hex]
          _ ≤ Real.sqrt ((plan.axis i).order : ℝ) * p09MultiRms x +
              scoef * Real.sqrt ((plan.axis i).order : ℝ) *
                p09MultiRms x := by linarith
          _ = (1 + scoef) * Real.sqrt ((plan.axis i).order : ℝ) *
                p09MultiRms x := by ring
      let e1 : P09MultiArray plan.axis := fun index =>
        p09RoundedCoordinatePrefix plan.axis model k hk' rx index -
          p09ApplyCoordinatePrefix plan.axis k rx index
      let e2 : P09MultiArray plan.axis := fun index =>
        p09ApplyCoordinatePrefix plan.axis k rx index -
          p09ApplyCoordinatePrefix plan.axis k ex index
      have he2 : p09MultiRms e2 = S *
          p09MultiRms (fun index => rx index - ex index) := by
        have hsub := p09ApplyCoordinatePrefix_sub plan.axis k rx ex
        have hscale := plan.prefix_rms_scaling k hk'
          (fun index => rx index - ex index)
        rw [hsub] at hscale
        simpa [e2, S, p09MultiPrefixScale] using hscale
      have herr : p09MultiRms (fun index =>
          p09RoundedCoordinatePrefix plan.axis model (k + 1) hk x index -
            p09ApplyCoordinatePrefix plan.axis (k + 1) x index) ≤
          pcoef * S * p09MultiRms rx +
            S * (scoef * Real.sqrt ((plan.axis i).order : ℝ) *
              p09MultiRms x) := by
        have htri := p09MultiRms_add plan.axis e1 e2
        have hid : (fun index =>
            p09RoundedCoordinatePrefix plan.axis model (k + 1) hk x index -
              p09ApplyCoordinatePrefix plan.axis (k + 1) x index) =
            fun index => e1 index + e2 index := by
          funext index
          dsimp [p09RoundedCoordinatePrefix, e1, e2, rx, ex, i]
          simp only [p09ApplyCoordinatePrefix, p09CoordinateTransformNat,
            dif_pos (Nat.lt_of_succ_le hk)]
          ring
        rw [hid]
        calc
          p09MultiRms (fun index => e1 index + e2 index) ≤
              p09MultiRms e1 + p09MultiRms e2 := htri
          _ ≤ pcoef * S * p09MultiRms rx +
              S * (scoef * Real.sqrt ((plan.axis i).order : ℝ) *
                p09MultiRms x) := by
            apply add_le_add hp
            rw [he2]
            exact mul_le_mul_of_nonneg_left hs hS
      have hpoly : pcoef * (1 + scoef) + scoef ≤
          (C + c) * model.epsilon + D * model.epsilon ^ 2 := by
        have he3 : model.epsilon ^ 3 ≤ model.epsilon ^ 2 := by
          nlinarith [sq_nonneg model.epsilon]
        have he4 : model.epsilon ^ 4 ≤ model.epsilon ^ 2 := by
          nlinarith [sq_nonneg model.epsilon,
            sq_nonneg (model.epsilon ^ 2 - model.epsilon)]
        have hPc := mul_le_mul_of_nonneg_left he3 (by positivity : 0 ≤ P * c)
        have hCQ := mul_le_mul_of_nonneg_left he3 (by positivity : 0 ≤ C * Q)
        have hPQ := mul_le_mul_of_nonneg_left he4 (by positivity : 0 ≤ P * Q)
        dsimp [pcoef, scoef, D]
        nlinarith
      have hscale : p09MultiPrefixScale plan (k + 1) hk =
          S * Real.sqrt ((plan.axis i).order : ℝ) := by
        exact p09MultiPrefixScale_succ plan k hk
      have hcoeff : p09MultiPrefixCoeff plan γ (k + 1) hk = C + c := by
        exact p09MultiPrefixCoeff_succ plan γ k hk
      calc
        p09MultiRms (fun index =>
            p09RoundedCoordinatePrefix plan.axis model (k + 1) hk x index -
              p09ApplyCoordinatePrefix plan.axis (k + 1) x index) ≤
            pcoef * S * p09MultiRms rx +
              S * (scoef * Real.sqrt ((plan.axis i).order : ℝ) *
                p09MultiRms x) := herr
        _ ≤ pcoef * S *
              ((1 + scoef) * Real.sqrt ((plan.axis i).order : ℝ) *
                p09MultiRms x) +
              S * (scoef * Real.sqrt ((plan.axis i).order : ℝ) *
                p09MultiRms x) := by gcongr
        _ = (pcoef * (1 + scoef) + scoef) *
              (S * Real.sqrt ((plan.axis i).order : ℝ)) *
                p09MultiRms x := by ring
        _ ≤ ((C + c) * model.epsilon + D * model.epsilon ^ 2) *
              (S * Real.sqrt ((plan.axis i).order : ℝ)) *
                p09MultiRms x := by
          exact mul_le_mul_of_nonneg_right
            (mul_le_mul_of_nonneg_right hpoly
              (mul_nonneg hS (Real.sqrt_nonneg _)))
            (p09MultiRms_nonneg plan.axis x)
        _ = (p09MultiPrefixCoeff plan γ (k + 1) hk * model.epsilon +
              D * model.epsilon ^ 2) *
            p09MultiPrefixScale plan (k + 1) hk * p09MultiRms x := by
          rw [hscale, hcoeff]

private lemma p09Run_computedState_zero_eq_roundedPrefix {m : ℕ} [NeZero m]
    {plan : P09MultidimensionalFftPlan m} {model : P09WilkinsonModel}
    (run : P09MultidimensionalFftRun plan model) :
    run.computedState 0 =
      p09RoundedCoordinatePrefix plan.axis model m (le_refl m) run.input := by
  have haux : ∀ (k : ℕ) (hk : k ≤ m),
      run.computedState 0 =
        p09RoundedCoordinatePrefix plan.axis model k hk
          (run.computedState ⟨k, Nat.lt_succ_of_le hk⟩) := by
    intro k
    induction k with
    | zero =>
        intro hk
        rfl
    | succ k ih =>
        intro hk
        let hk' : k ≤ m := Nat.le_of_succ_le hk
        let i : Fin m := ⟨k, Nat.lt_of_succ_le hk⟩
        rw [ih hk']
        have hstep := run.stage_step i
        have hstep' : run.computedState ⟨k, Nat.lt_succ_of_le hk'⟩ =
            p09RoundedCoordinateTransform plan.axis i model
              (run.computedState ⟨k + 1, Nat.lt_succ_of_le hk⟩) := by
          simpa [i] using hstep
        rw [hstep']
        rfl
  rw [haux m (le_refl m)]
  have hlast : (⟨m, Nat.lt_succ_self m⟩ : Fin (m + 1)) = Fin.last m := by
    apply Fin.ext
    rfl
  rw [hlast, run.computed_input]

private lemma p09MultiPrefixCoeff_full {m : ℕ} [NeZero m]
    (plan : P09MultidimensionalFftPlan m) (γ : ℝ) :
    p09MultiPrefixCoeff plan γ m (le_refl m) =
      ∑ i : Fin m, p09AxisK (plan.axis i) γ := by
  unfold p09MultiPrefixCoeff
  apply Finset.sum_congr rfl
  intro i hi
  rw [Fin.castLE_refl]

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
  rcases p09RoundedCoordinatePrefix_asymptotic plan γ family.gamma_nonneg
      m (le_refl m) with ⟨D, hD, hfull⟩
  refine ⟨D, hD, 1, by norm_num, ?_⟩
  intro ε hε
  have hmodelone : (family.model ε).epsilon ≤ 1 := by
    rw [family.model_epsilon]
    exact hε
  have h := hfull (family.model ε) (family.model_gamma ε)
    hmodelone family.input
  have hscale : p09MultiPrefixScale plan m (le_refl m) *
      p09MultiRms family.input =
        p09MultiRms (p09FamilyMultiExactOutput family) := by
    have hs := plan.prefix_rms_scaling m (le_refl m) family.input
    simpa [p09MultiPrefixScale, p09FamilyMultiExactOutput] using hs.symm
  have hcomputed : p09MultiComputedOutput (family.run ε) =
      p09RoundedCoordinatePrefix plan.axis (family.model ε)
        m (le_refl m) family.input := by
    unfold p09MultiComputedOutput
    rw [p09Run_computedState_zero_eq_roundedPrefix,
      family.run_input]
  have herr : p09FamilyMultiFftRoundoffError family ε = fun index =>
      p09RoundedCoordinatePrefix plan.axis (family.model ε)
          m (le_refl m) family.input index -
        p09ApplyCoordinatePrefix plan.axis m family.input index := by
    funext index
    unfold p09FamilyMultiFftRoundoffError p09MultiVecSub
    rw [hcomputed]
    rfl
  rw [p09MultiPrefixCoeff_full, family.model_epsilon] at h
  rw [mul_assoc, hscale, ← herr] at h
  apply (div_le_iff₀ hexactOutput).2
  nlinarith

end HighamBench
