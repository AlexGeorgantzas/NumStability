import HighamBench.P09Definitions

set_option maxHeartbeats 800000

namespace HighamBench

open scoped BigOperators

private lemma p09_abs_add_error
    (model : P09WilkinsonModel) (e : ℝ) (he : model.epsilon = e)
    (a b : ℝ) :
    |model.flAdd a b - (a + b)| ≤ e * (|a| + |b|) := by
  obtain ⟨u, v, hu, hv, h⟩ := model.add_model a b
  rw [h, he]
  have he0 : 0 ≤ e := by rw [← he]; exact le_of_lt model.epsilon_pos
  calc
    |a * (1 + u * e) + b * (1 + v * e) - (a + b)| =
        e * |a * u + b * v| := by
          rw [show a * (1 + u * e) + b * (1 + v * e) - (a + b) =
            e * (a * u + b * v) by ring, abs_mul, abs_of_nonneg he0]
    _ ≤ e * (|a * u| + |b * v|) := by
      exact mul_le_mul_of_nonneg_left (abs_add_le _ _) he0
    _ ≤ e * (|a| + |b|) := by
      apply mul_le_mul_of_nonneg_left _ he0
      rw [abs_mul, abs_mul]
      have hau : |a| * |u| ≤ |a| := by
        simpa using mul_le_mul_of_nonneg_left hu (abs_nonneg a)
      have hbv : |b| * |v| ≤ |b| := by
        simpa using mul_le_mul_of_nonneg_left hv (abs_nonneg b)
      linarith

private lemma p09_abs_mul_error
    (model : P09WilkinsonModel) (e : ℝ) (he : model.epsilon = e)
    (a b : ℝ) :
    |model.flMul a b - a * b| ≤ e * |a * b| := by
  obtain ⟨u, hu, h⟩ := model.mul_model a b
  rw [h, he]
  have he0 : 0 ≤ e := by rw [← he]; exact le_of_lt model.epsilon_pos
  rw [show a * b * (1 + u * e) - a * b = e * (u * (a * b)) by ring,
    abs_mul, abs_mul, abs_of_nonneg he0]
  apply mul_le_mul_of_nonneg_left _ he0
  simpa using mul_le_mul_of_nonneg_right hu (abs_nonneg (a * b))

private lemma p09_abs_flMul_le
    (model : P09WilkinsonModel) (e : ℝ) (he : model.epsilon = e)
    (a b : ℝ) :
    |model.flMul a b| ≤ (1 + e) * |a * b| := by
  calc
    |model.flMul a b| ≤ |a * b| + |model.flMul a b - a * b| := by
      have := abs_add_le (a * b) (model.flMul a b - a * b)
      simpa [add_comm] using this
    _ ≤ |a * b| + e * |a * b| := by gcongr; exact p09_abs_mul_error model e he a b
    _ = (1 + e) * |a * b| := by ring

private lemma p09_complex_component_contraction
    (x : ℂ) (u v : ℝ) (hu : |u| ≤ 1) (hv : |v| ≤ 1) :
    ‖(⟨x.re * u, x.im * v⟩ : ℂ)‖ ≤ ‖x‖ := by
  rw [← sq_le_sq₀ (norm_nonneg _) (norm_nonneg _),
    Complex.sq_norm, Complex.sq_norm, Complex.normSq_apply,
    Complex.normSq_apply]
  have hu2 : u ^ 2 ≤ 1 := by
    have := (sq_le_sq₀ (abs_nonneg u) zero_le_one).2 hu
    simpa [sq_abs] using this
  have hv2 : v ^ 2 ≤ 1 := by
    have := (sq_le_sq₀ (abs_nonneg v) zero_le_one).2 hv
    simpa [sq_abs] using this
  nlinarith [sq_nonneg x.re, sq_nonneg x.im]

private lemma p09_complex_add_error
    (model : P09WilkinsonModel) (e : ℝ) (he : model.epsilon = e)
    (x y : ℂ) :
    ‖p09RoundedComplexAdd model x y - (x + y)‖ ≤
      e * (‖x‖ + ‖y‖) := by
  obtain ⟨ur, vr, hur, hvr, hr⟩ := model.add_model x.re y.re
  obtain ⟨ui, vi, hui, hvi, hi⟩ := model.add_model x.im y.im
  have he0 : 0 ≤ e := by rw [← he]; exact le_of_lt model.epsilon_pos
  let dx : ℂ := ⟨x.re * ur, x.im * ui⟩
  let dy : ℂ := ⟨y.re * vr, y.im * vi⟩
  have hdx : ‖dx‖ ≤ ‖x‖ := p09_complex_component_contraction x ur ui hur hui
  have hdy : ‖dy‖ ≤ ‖y‖ := p09_complex_component_contraction y vr vi hvr hvi
  have hid : p09RoundedComplexAdd model x y - (x + y) =
      (e : ℂ) * dx + (e : ℂ) * dy := by
    apply Complex.ext <;> simp [p09RoundedComplexAdd, dx, dy, hr, hi, he] <;> ring
  rw [hid]
  calc
    ‖(e : ℂ) * dx + (e : ℂ) * dy‖ ≤
        ‖(e : ℂ) * dx‖ + ‖(e : ℂ) * dy‖ := norm_add_le _ _
    _ = e * (‖dx‖ + ‖dy‖) := by
      simp [norm_mul, abs_of_nonneg he0]; ring
    _ ≤ e * (‖x‖ + ‖y‖) := by gcongr

private lemma p09_complex_flAdd_le
    (model : P09WilkinsonModel) (e : ℝ) (he : model.epsilon = e)
    (x y : ℂ) :
    ‖p09RoundedComplexAdd model x y‖ ≤ (1 + e) * (‖x‖ + ‖y‖) := by
  have he0 : 0 ≤ e := by rw [← he]; exact le_of_lt model.epsilon_pos
  calc
    ‖p09RoundedComplexAdd model x y‖ ≤
        ‖x + y‖ + ‖p09RoundedComplexAdd model x y - (x + y)‖ := by
      have h := norm_add_le (x + y) (p09RoundedComplexAdd model x y - (x + y))
      simpa [add_comm] using h
    _ ≤ (‖x‖ + ‖y‖) + e * (‖x‖ + ‖y‖) := by
      gcongr
      · exact norm_add_le _ _
      · exact p09_complex_add_error model e he x y
    _ = (1 + e) * (‖x‖ + ‖y‖) := by ring

private lemma p09_complex_norm_le_of_components
    (z : ℂ) (a b : ℝ) (ha : 0 ≤ a) (hb : 0 ≤ b)
    (hre : |z.re| ≤ a) (him : |z.im| ≤ b) :
    ‖z‖ ≤ ‖(⟨a, b⟩ : ℂ)‖ := by
  rw [← sq_le_sq₀ (norm_nonneg _) (norm_nonneg _),
    Complex.sq_norm, Complex.sq_norm, Complex.normSq_apply,
    Complex.normSq_apply]
  have hre2 := (sq_le_sq₀ (abs_nonneg z.re) ha).2 hre
  have him2 := (sq_le_sq₀ (abs_nonneg z.im) hb).2 him
  simpa [sq_abs, pow_two] using add_le_add hre2 him2

private lemma p09_pair_products_norm_le (a b c d : ℝ) :
    ‖(⟨a * c + b * d, a * d + b * c⟩ : ℂ)‖ ≤
      Real.sqrt 2 * ‖(⟨a, b⟩ : ℂ)‖ * ‖(⟨c, d⟩ : ℂ)‖ := by
  rw [← sq_le_sq₀ (norm_nonneg _) (by positivity),
    Complex.sq_norm, Complex.normSq_apply, mul_pow]
  rw [mul_pow, Real.sq_sqrt (by norm_num : (0 : ℝ) ≤ 2),
    Complex.sq_norm, Complex.sq_norm, Complex.normSq_apply,
    Complex.normSq_apply]
  nlinarith [sq_nonneg (a * d - b * c), sq_nonneg (a * c - b * d)]

private lemma p09_sqrt_two_le_three_halves : Real.sqrt 2 ≤ (3 : ℝ) / 2 := by
  rw [← sq_le_sq₀ (Real.sqrt_nonneg _) (by norm_num)]
  rw [Real.sq_sqrt (by norm_num : (0 : ℝ) ≤ 2)]
  norm_num

private lemma p09_sqrt_two_le_two : Real.sqrt 2 ≤ (2 : ℝ) :=
  p09_sqrt_two_le_three_halves.trans (by norm_num)

private lemma p09_complex_mul_rounding_error
    (model : P09WilkinsonModel) (e : ℝ) (he : model.epsilon = e)
    (w x : ℂ) :
    ‖p09RoundedComplexMul model w x - w * x‖ ≤
      (3 * e + 2 * e ^ 2) * ‖w‖ * ‖x‖ := by
  let p₁ := model.flMul w.re x.re
  let p₂ := model.flMul w.im x.im
  let p₃ := model.flMul w.re x.im
  let p₄ := model.flMul w.im x.re
  let exact₁ := w.re * x.re
  let exact₂ := w.im * x.im
  let exact₃ := w.re * x.im
  let exact₄ := w.im * x.re
  let mulError : ℂ := ⟨(p₁ - exact₁) - (p₂ - exact₂),
    (p₃ - exact₃) + (p₄ - exact₄)⟩
  let addError : ℂ := ⟨model.flAdd p₁ (-p₂) - (p₁ - p₂),
    model.flAdd p₃ p₄ - (p₃ + p₄)⟩
  have he0 : 0 ≤ e := by rw [← he]; exact le_of_lt model.epsilon_pos
  have he1 : 0 ≤ 1 + e := by positivity
  have hmul : ‖mulError‖ ≤ Real.sqrt 2 * e * ‖w‖ * ‖x‖ := by
    let a := e * (|exact₁| + |exact₂|)
    let b := e * (|exact₃| + |exact₄|)
    have ha : 0 ≤ a := by positivity
    have hb : 0 ≤ b := by positivity
    have hre : |mulError.re| ≤ a := by
      dsimp [mulError, a]
      calc
        |(p₁ - exact₁) - (p₂ - exact₂)| ≤
            |p₁ - exact₁| + |p₂ - exact₂| := abs_sub _ _
        _ ≤ e * |exact₁| + e * |exact₂| := by
          gcongr <;> exact p09_abs_mul_error model e he _ _
        _ = e * (|exact₁| + |exact₂|) := by ring
    have him : |mulError.im| ≤ b := by
      dsimp [mulError, b]
      calc
        |(p₃ - exact₃) + (p₄ - exact₄)| ≤
            |p₃ - exact₃| + |p₄ - exact₄| := abs_add_le _ _
        _ ≤ e * |exact₃| + e * |exact₄| := by
          gcongr <;> exact p09_abs_mul_error model e he _ _
        _ = e * (|exact₃| + |exact₄|) := by ring
    calc
      ‖mulError‖ ≤ ‖(⟨a, b⟩ : ℂ)‖ :=
        p09_complex_norm_le_of_components mulError a b ha hb hre him
      _ = e * ‖(⟨|w.re| * |x.re| + |w.im| * |x.im|,
          |w.re| * |x.im| + |w.im| * |x.re|⟩ : ℂ)‖ := by
        have hab : (⟨a, b⟩ : ℂ) = (e : ℂ) *
            ⟨|w.re| * |x.re| + |w.im| * |x.im|,
              |w.re| * |x.im| + |w.im| * |x.re|⟩ := by
          apply Complex.ext <;> simp [a, b, exact₁, exact₂, exact₃, exact₄,
            abs_mul] <;> ring
        rw [hab, norm_mul]
        simp [abs_of_nonneg he0]
      _ ≤ e * (Real.sqrt 2 *
          ‖(⟨|w.re|, |w.im|⟩ : ℂ)‖ *
          ‖(⟨|x.re|, |x.im|⟩ : ℂ)‖) := by
        gcongr
        exact p09_pair_products_norm_le _ _ _ _
      _ = Real.sqrt 2 * e * ‖w‖ * ‖x‖ := by
        have hw : ‖(⟨|w.re|, |w.im|⟩ : ℂ)‖ = ‖w‖ := by
          rw [← sq_eq_sq₀ (norm_nonneg _) (norm_nonneg _),
            Complex.sq_norm, Complex.sq_norm, Complex.normSq_apply,
            Complex.normSq_apply]
          simp [sq_abs]
        have hx : ‖(⟨|x.re|, |x.im|⟩ : ℂ)‖ = ‖x‖ := by
          rw [← sq_eq_sq₀ (norm_nonneg _) (norm_nonneg _),
            Complex.sq_norm, Complex.sq_norm, Complex.normSq_apply,
            Complex.normSq_apply]
          simp [sq_abs]
        rw [hw, hx]
        ring
  have hadd : ‖addError‖ ≤ Real.sqrt 2 * e * (1 + e) * ‖w‖ * ‖x‖ := by
    let a := e * (1 + e) * (|exact₁| + |exact₂|)
    let b := e * (1 + e) * (|exact₃| + |exact₄|)
    have ha : 0 ≤ a := by positivity
    have hb : 0 ≤ b := by positivity
    have hre : |addError.re| ≤ a := by
      dsimp [addError, a]
      calc
        |model.flAdd p₁ (-p₂) - (p₁ - p₂)| ≤
            e * (|p₁| + |-p₂|) := by
              simpa [sub_eq_add_neg] using p09_abs_add_error model e he p₁ (-p₂)
        _ ≤ e * ((1 + e) * |exact₁| + (1 + e) * |exact₂|) := by
          apply mul_le_mul_of_nonneg_left _ he0
          apply add_le_add
          · simpa [p₁, exact₁] using p09_abs_flMul_le model e he w.re x.re
          · simpa [p₂, exact₂] using p09_abs_flMul_le model e he w.im x.im
        _ = e * (1 + e) * (|exact₁| + |exact₂|) := by ring
    have him : |addError.im| ≤ b := by
      dsimp [addError, b]
      calc
        |model.flAdd p₃ p₄ - (p₃ + p₄)| ≤
            e * (|p₃| + |p₄|) := p09_abs_add_error model e he _ _
        _ ≤ e * ((1 + e) * |exact₃| + (1 + e) * |exact₄|) := by
          apply mul_le_mul_of_nonneg_left _ he0
          apply add_le_add
          · simpa [p₃, exact₃] using p09_abs_flMul_le model e he w.re x.im
          · simpa [p₄, exact₄] using p09_abs_flMul_le model e he w.im x.re
        _ = e * (1 + e) * (|exact₃| + |exact₄|) := by ring
    calc
      ‖addError‖ ≤ ‖(⟨a, b⟩ : ℂ)‖ :=
        p09_complex_norm_le_of_components addError a b ha hb hre him
      _ = e * (1 + e) * ‖(⟨|w.re| * |x.re| + |w.im| * |x.im|,
          |w.re| * |x.im| + |w.im| * |x.re|⟩ : ℂ)‖ := by
        have hab : (⟨a, b⟩ : ℂ) = ((e * (1 + e) : ℝ) : ℂ) *
            ⟨|w.re| * |x.re| + |w.im| * |x.im|,
              |w.re| * |x.im| + |w.im| * |x.re|⟩ := by
          apply Complex.ext <;> simp [a, b, exact₁, exact₂, exact₃, exact₄,
            abs_mul] <;> ring
        rw [hab]
        have hs : ‖((e * (1 + e) : ℝ) : ℂ)‖ = e * (1 + e) := by
          rw [Complex.norm_real, Real.norm_eq_abs,
            abs_of_nonneg (mul_nonneg he0 he1)]
        rw [norm_mul, hs]
      _ ≤ e * (1 + e) * (Real.sqrt 2 *
          ‖(⟨|w.re|, |w.im|⟩ : ℂ)‖ *
          ‖(⟨|x.re|, |x.im|⟩ : ℂ)‖) := by
        gcongr
        exact p09_pair_products_norm_le _ _ _ _
      _ = Real.sqrt 2 * e * (1 + e) * ‖w‖ * ‖x‖ := by
        have hw : ‖(⟨|w.re|, |w.im|⟩ : ℂ)‖ = ‖w‖ := by
          rw [← sq_eq_sq₀ (norm_nonneg _) (norm_nonneg _),
            Complex.sq_norm, Complex.sq_norm, Complex.normSq_apply,
            Complex.normSq_apply]
          simp [sq_abs]
        have hx : ‖(⟨|x.re|, |x.im|⟩ : ℂ)‖ = ‖x‖ := by
          rw [← sq_eq_sq₀ (norm_nonneg _) (norm_nonneg _),
            Complex.sq_norm, Complex.sq_norm, Complex.normSq_apply,
            Complex.normSq_apply]
          simp [sq_abs]
        rw [hw, hx]
        ring
  have hid : p09RoundedComplexMul model w x - w * x = addError + mulError := by
    apply Complex.ext <;> simp [p09RoundedComplexMul, addError, mulError, p₁, p₂, p₃, p₄,
      exact₁, exact₂, exact₃, exact₄] <;> ring
  rw [hid]
  calc
    ‖addError + mulError‖ ≤ ‖addError‖ + ‖mulError‖ := norm_add_le _ _
    _ ≤ Real.sqrt 2 * e * (1 + e) * ‖w‖ * ‖x‖ +
        Real.sqrt 2 * e * ‖w‖ * ‖x‖ := add_le_add hadd hmul
    _ = (Real.sqrt 2 * e * (1 + e) + Real.sqrt 2 * e) * ‖w‖ * ‖x‖ := by ring
    _ ≤ (3 * e + 2 * e ^ 2) * ‖w‖ * ‖x‖ := by
      have hw0 := norm_nonneg w
      have hx0 := norm_nonneg x
      have hc : Real.sqrt 2 * e * (1 + e) + Real.sqrt 2 * e ≤
          3 * e + 2 * e ^ 2 := by
        have hs0 : 0 ≤ Real.sqrt 2 := Real.sqrt_nonneg _
        nlinarith [p09_sqrt_two_le_three_halves, p09_sqrt_two_le_two]
      exact mul_le_mul_of_nonneg_right
        (mul_le_mul_of_nonneg_right hc hw0) hx0

private noncomputable def p09ExactRoot {q : ℕ} [NeZero q]
    (j : ZMod q) : ℂ :=
  ⟨Real.cos (p09RootAngle j), Real.sin (p09RootAngle j)⟩

private lemma p09_exactRoot_norm {q : ℕ} [NeZero q] (j : ZMod q) :
    ‖p09ExactRoot j‖ = 1 := by
  rw [← sq_eq_sq₀ (norm_nonneg _) zero_le_one, Complex.sq_norm,
    Complex.normSq_apply]
  dsimp [p09ExactRoot]
  nlinarith [Real.sin_sq_add_cos_sq (p09RootAngle j)]

private lemma p09_roundedRoot_error {q : ℕ} [NeZero q]
    (model : P09WilkinsonModel) (e γ : ℝ)
    (he : model.epsilon = e) (hγ : model.gamma = γ) (hγ0 : 0 ≤ γ)
    (j : ZMod q) :
    ‖p09RoundedRoot model j - p09ExactRoot j‖ ≤ 2 * γ * e := by
  obtain ⟨u, hu, hsu⟩ := model.sin_model (p09RootAngle j)
  obtain ⟨v, hv, hcv⟩ := model.cos_model (p09RootAngle j)
  have he0 : 0 ≤ e := by rw [← he]; exact le_of_lt model.epsilon_pos
  have hge0 : 0 ≤ γ * e := mul_nonneg hγ0 he0
  have hre : |(p09RoundedRoot model j - p09ExactRoot j).re| ≤ γ * e := by
    change |model.flCos (p09RootAngle j) - Real.cos (p09RootAngle j)| ≤ γ * e
    rw [hcv, hγ, he]
    rw [show Real.cos (p09RootAngle j) + γ * v * e -
      Real.cos (p09RootAngle j) = (γ * e) * v by ring, abs_mul,
      abs_of_nonneg hge0]
    simpa using mul_le_mul_of_nonneg_left hv hge0
  have him : |(p09RoundedRoot model j - p09ExactRoot j).im| ≤ γ * e := by
    change |model.flSin (p09RootAngle j) - Real.sin (p09RootAngle j)| ≤ γ * e
    rw [hsu, hγ, he]
    rw [show Real.sin (p09RootAngle j) + γ * u * e -
      Real.sin (p09RootAngle j) = (γ * e) * u by ring, abs_mul,
      abs_of_nonneg hge0]
    simpa using mul_le_mul_of_nonneg_left hu hge0
  calc
    ‖p09RoundedRoot model j - p09ExactRoot j‖ ≤
        ‖(⟨γ * e, γ * e⟩ : ℂ)‖ :=
      p09_complex_norm_le_of_components _ _ _ hge0 hge0 hre him
    _ = Real.sqrt 2 * (γ * e) := by
      rw [← sq_eq_sq₀ (norm_nonneg _) (mul_nonneg (Real.sqrt_nonneg _) hge0),
        Complex.sq_norm, Complex.normSq_apply, mul_pow,
        Real.sq_sqrt (by norm_num : (0 : ℝ) ≤ 2)]
      ring
    _ ≤ 2 * γ * e := by
      have := mul_le_mul_of_nonneg_right p09_sqrt_two_le_two hge0
      nlinarith

private lemma p09_roundedRoot_norm {q : ℕ} [NeZero q]
    (model : P09WilkinsonModel) (e γ : ℝ)
    (he : model.epsilon = e) (hγ : model.gamma = γ) (hγ0 : 0 ≤ γ)
    (j : ZMod q) :
    ‖p09RoundedRoot model j‖ ≤ 1 + 2 * γ * e := by
  calc
    ‖p09RoundedRoot model j‖ ≤ ‖p09ExactRoot j‖ +
        ‖p09RoundedRoot model j - p09ExactRoot j‖ := by
      have h := norm_add_le (p09ExactRoot j)
        (p09RoundedRoot model j - p09ExactRoot j)
      simpa [add_comm] using h
    _ ≤ 1 + 2 * γ * e := by
      rw [p09_exactRoot_norm]
      gcongr
      exact p09_roundedRoot_error model e γ he hγ hγ0 j

private lemma p09_rounded_root_mul_error {q : ℕ} [NeZero q]
    (model : P09WilkinsonModel) (e γ : ℝ)
    (he : model.epsilon = e) (hγ : model.gamma = γ) (hγ0 : 0 ≤ γ)
    (he1 : e ≤ 1) (j : ZMod q) (x : ℂ) :
    ‖p09RoundedComplexMul model (p09RoundedRoot model j) x -
        p09ExactRoot j * x‖ ≤
      ((3 + 2 * γ) * e + (2 + 10 * γ) * e ^ 2) * ‖x‖ := by
  have he0 : 0 ≤ e := by rw [← he]; exact le_of_lt model.epsilon_pos
  let w := p09RoundedRoot model j
  let w₀ := p09ExactRoot j
  have hw : ‖w‖ ≤ 1 + 2 * γ * e :=
    p09_roundedRoot_norm model e γ he hγ hγ0 j
  have hroot : ‖w - w₀‖ ≤ 2 * γ * e :=
    p09_roundedRoot_error model e γ he hγ hγ0 j
  have hdecomp : p09RoundedComplexMul model w x - w₀ * x =
      (p09RoundedComplexMul model w x - w * x) + (w - w₀) * x := by ring
  rw [hdecomp]
  calc
    ‖(p09RoundedComplexMul model w x - w * x) + (w - w₀) * x‖ ≤
        ‖p09RoundedComplexMul model w x - w * x‖ + ‖(w - w₀) * x‖ :=
      norm_add_le _ _
    _ ≤ (3 * e + 2 * e ^ 2) * ‖w‖ * ‖x‖ +
        (2 * γ * e) * ‖x‖ := by
      apply add_le_add
      · exact p09_complex_mul_rounding_error model e he w x
      · rw [norm_mul]
        exact mul_le_mul_of_nonneg_right hroot (norm_nonneg x)
    _ ≤ (3 * e + 2 * e ^ 2) * (1 + 2 * γ * e) * ‖x‖ +
        (2 * γ * e) * ‖x‖ := by
      gcongr
    _ ≤ ((3 + 2 * γ) * e + (2 + 10 * γ) * e ^ 2) * ‖x‖ := by
      rw [← add_mul]
      apply mul_le_mul_of_nonneg_right _ (norm_nonneg x)
      have he2 : e ^ 3 ≤ e ^ 2 := by nlinarith [sq_nonneg e]
      nlinarith [mul_nonneg hγ0 (sub_nonneg.mpr he2)]

private lemma p09_recursiveSum_error (n : ℕ) :
    ∃ B : ℝ, 0 ≤ B ∧
      ∀ (model : P09WilkinsonModel) (e : ℝ), model.epsilon = e → e ≤ 1 →
      ∀ v : Fin n → ℝ,
        |recursiveSum model.flAdd n v - ∑ i : Fin n, v i| ≤
          e * (n - 1 : ℕ) * (∑ i : Fin n, |v i|) +
            B * e ^ 2 * (∑ i : Fin n, |v i|) := by
  induction n with
  | zero =>
      refine ⟨0, le_rfl, ?_⟩
      intro model e he he1 v
      simp [recursiveSum]
  | succ n ih =>
      by_cases hn : n = 0
      · subst n
        refine ⟨0, le_rfl, ?_⟩
        intro model e he he1 v
        simp [recursiveSum]
      · obtain ⟨B, hB0, hB⟩ := ih
        refine ⟨2 * B + n, by positivity, ?_⟩
        intro model e he he1 v
        have he0 : 0 ≤ e := by rw [← he]; exact le_of_lt model.epsilon_pos
        let prev := recursiveSum model.flAdd n (fun i ↦ v i.castSucc)
        let exactPrev := ∑ i : Fin n, v i.castSucc
        let s := ∑ i : Fin n, |v i.castSucc|
        let last := v (Fin.last n)
        have hs0 : 0 ≤ s := Finset.sum_nonneg fun _ _ ↦ abs_nonneg _
        have habsExact : |exactPrev| ≤ s := by
          dsimp [exactPrev, s]
          exact Finset.abs_sum_le_sum_abs _ _
        have hold : |prev - exactPrev| ≤
            e * (n - 1 : ℕ) * s + B * e ^ 2 * s := by
          simpa [prev, exactPrev, s] using
            hB model e he he1 (fun i ↦ v i.castSucc)
        have hprev : |prev| ≤ s + |prev - exactPrev| := by
          have h := abs_add_le exactPrev (prev - exactPrev)
          calc
            |prev| = |exactPrev + (prev - exactPrev)| := by ring_nf
            _ ≤ |exactPrev| + |prev - exactPrev| := h
            _ ≤ s + |prev - exactPrev| := by linarith
        have hlocal : |model.flAdd prev last - (prev + last)| ≤
            e * (s + |prev - exactPrev| + |last|) := by
          calc
            |model.flAdd prev last - (prev + last)| ≤
                e * (|prev| + |last|) := p09_abs_add_error model e he prev last
            _ ≤ e * (s + |prev - exactPrev| + |last|) := by
              apply mul_le_mul_of_nonneg_left _ he0
              linarith
        have htotal : |model.flAdd prev last - (exactPrev + last)| ≤
            e * (s + |prev - exactPrev| + |last|) + |prev - exactPrev| := by
          calc
            |model.flAdd prev last - (exactPrev + last)| =
                |(model.flAdd prev last - (prev + last)) + (prev - exactPrev)| := by ring_nf
            _ ≤ |model.flAdd prev last - (prev + last)| + |prev - exactPrev| :=
              abs_add_le _ _
            _ ≤ e * (s + |prev - exactPrev| + |last|) + |prev - exactPrev| := by
              linarith
        have he3 : e ^ 3 ≤ e ^ 2 := by nlinarith [sq_nonneg e]
        have hcoeff : (0 : ℝ) ≤ (n - 1 : ℕ) := by positivity
        have hn1 : 1 ≤ n := Nat.one_le_iff_ne_zero.mpr hn
        have hncast : ((n - 1 : ℕ) : ℝ) + 1 = (n : ℝ) := by
          exact_mod_cast Nat.sub_add_cancel hn1
        rw [recursiveSum, dif_neg hn, Fin.sum_univ_castSucc]
        change |model.flAdd prev last - (exactPrev + last)| ≤ _
        rw [Fin.sum_univ_castSucc]
        change |model.flAdd prev last - (exactPrev + last)| ≤
          e * (n : ℝ) * (s + |last|) +
            (2 * B + n) * e ^ 2 * (s + |last|)
        have hsLast : 0 ≤ s + |last| := by positivity
        have hgamma : 0 ≤ B * (e ^ 2 - e ^ 3) * s :=
          mul_nonneg (mul_nonneg hB0 (sub_nonneg.mpr he3)) hs0
        have hupper : |model.flAdd prev last - (exactPrev + last)| ≤
            e * (s + |last|) + (1 + e) *
              (e * (n - 1 : ℕ) * s + B * e ^ 2 * s) := by
          calc
            |model.flAdd prev last - (exactPrev + last)| ≤
                e * (s + |prev - exactPrev| + |last|) +
                  |prev - exactPrev| := htotal
            _ = e * (s + |last|) + (1 + e) * |prev - exactPrev| := by ring
            _ ≤ e * (s + |last|) + (1 + e) *
                (e * (n - 1 : ℕ) * s + B * e ^ 2 * s) := by
              exact add_le_add (le_refl _)
                (mul_le_mul_of_nonneg_left hold (show 0 ≤ 1 + e by linarith))
        have hnsub0 : (0 : ℝ) ≤ (n : ℝ) - 1 := by
          linarith
        have htwoBn : 0 ≤ 2 * B + (n : ℝ) := by positivity
        have hdiff :
            e * (n : ℝ) * (s + |last|) +
                (2 * B + n) * e ^ 2 * (s + |last|) -
              (e * (s + |last|) + (1 + e) *
                (e * (n - 1 : ℕ) * s + B * e ^ 2 * s)) =
            e * ((n : ℝ) - 1) * |last| + e ^ 2 * s +
              B * (e ^ 2 - e ^ 3) * s +
              (2 * B + n) * e ^ 2 * |last| := by
          rw [← hncast]
          ring
        have hdiff0 : 0 ≤
            e * ((n : ℝ) - 1) * |last| + e ^ 2 * s +
              B * (e ^ 2 - e ^ 3) * s +
              (2 * B + n) * e ^ 2 * |last| := by positivity
        nlinarith

private lemma p09_abs_re_add_abs_im_le (z : ℂ) :
    |z.re| + |z.im| ≤ Real.sqrt 2 * ‖z‖ := by
  rw [← sq_le_sq₀ (by positivity) (by positivity), mul_pow,
    Real.sq_sqrt (by norm_num : (0 : ℝ) ≤ 2), Complex.sq_norm,
    Complex.normSq_apply]
  nlinarith [sq_nonneg (|z.re| - |z.im|), sq_abs z.re, sq_abs z.im]

private lemma p09_roundedComplexSum_error {q : ℕ} [NeZero q] :
    ∃ B : ℝ, 0 ≤ B ∧
      ∀ (model : P09WilkinsonModel) (e : ℝ), model.epsilon = e → e ≤ 1 →
      ∀ term : ZMod q → ℂ,
        let index : Fin q ≃ ZMod q := (ZMod.finEquiv q).toEquiv
        ‖p09RoundedComplexSum model term - ∑ i : Fin q, term (index i)‖ ≤
          Real.sqrt 2 * e * (q - 1 : ℕ) * (∑ i : Fin q, ‖term (index i)‖) +
            Real.sqrt 2 * B * e ^ 2 * (∑ i : Fin q, ‖term (index i)‖) := by
  obtain ⟨B, hB0, hB⟩ := p09_recursiveSum_error q
  refine ⟨B, hB0, ?_⟩
  intro model e he he1 term
  let index : Fin q ≃ ZMod q := (ZMod.finEquiv q).toEquiv
  let z := p09RoundedComplexSum model term - ∑ i : Fin q, term (index i)
  let sr := ∑ i : Fin q, |(term (index i)).re|
  let si := ∑ i : Fin q, |(term (index i)).im|
  let sn := ∑ i : Fin q, ‖term (index i)‖
  have hsr0 : 0 ≤ sr := Finset.sum_nonneg fun _ _ ↦ abs_nonneg _
  have hsi0 : 0 ≤ si := Finset.sum_nonneg fun _ _ ↦ abs_nonneg _
  have hsn0 : 0 ≤ sn := Finset.sum_nonneg fun _ _ ↦ norm_nonneg _
  have hre : |z.re| ≤ e * (q - 1 : ℕ) * sr + B * e ^ 2 * sr := by
    simpa [z, sr, index, p09RoundedComplexSum] using
      hB model e he he1 (fun i ↦ (term (index i)).re)
  have him : |z.im| ≤ e * (q - 1 : ℕ) * si + B * e ^ 2 * si := by
    simpa [z, si, index, p09RoundedComplexSum] using
      hB model e he he1 (fun i ↦ (term (index i)).im)
  have hl1 : sr + si ≤ Real.sqrt 2 * sn := by
    dsimp [sr, si, sn]
    rw [← Finset.sum_add_distrib, Finset.mul_sum]
    exact Finset.sum_le_sum fun i _ ↦ p09_abs_re_add_abs_im_le (term (index i))
  have he0 : 0 ≤ e := by rw [← he]; exact le_of_lt model.epsilon_pos
  have hc0 : 0 ≤ e * (q - 1 : ℕ) + B * e ^ 2 := by positivity
  dsimp only
  change ‖z‖ ≤ _
  calc
    ‖z‖ ≤ |z.re| + |z.im| := Complex.norm_le_abs_re_add_abs_im z
    _ ≤ (e * (q - 1 : ℕ) + B * e ^ 2) * (sr + si) := by
      nlinarith
    _ ≤ (e * (q - 1 : ℕ) + B * e ^ 2) * (Real.sqrt 2 * sn) :=
      mul_le_mul_of_nonneg_left hl1 hc0
    _ = Real.sqrt 2 * e * (q - 1 : ℕ) * sn +
        Real.sqrt 2 * B * e ^ 2 * sn := by ring

private lemma p09_exactRoot_eq_stdAddChar {q : ℕ} [NeZero q] (j : ZMod q) :
    p09ExactRoot j = ZMod.stdAddChar j := by
  rw [p09StdAddChar_positive_exp]
  have hexp : 2 * Real.pi * Complex.I * (j.val : ℂ) / (q : ℂ) =
      ((p09RootAngle j : ℝ) : ℂ) * Complex.I := by
    simp only [p09RootAngle, Nat.cast_ofNat, Complex.ofReal_mul, Complex.ofReal_ofNat,
      Complex.ofReal_natCast, Complex.ofReal_div]
    ring
  rw [hexp]
  apply Complex.ext
  · simpa [p09ExactRoot] using
      (Complex.exp_ofReal_mul_I_re (p09RootAngle j)).symm
  · simpa [p09ExactRoot] using
      (Complex.exp_ofReal_mul_I_im (p09RootAngle j)).symm

private lemma p09_partition_l1_l2_bound
    {A B C : Type*} [Fintype A] [Fintype B] [Fintype C]
    (equiv : A × B ≃ C) (x error : C → ℂ) (c : ℝ) (hc : 0 ≤ c)
    (hpoint : ∀ a b, ‖error (equiv (a, b))‖ ≤
      c * (∑ j : B, ‖x (equiv (a, j))‖)) :
    ‖(WithLp.toLp 2 error : EuclideanSpace ℂ C)‖ ≤
      c * Fintype.card B *
        ‖(WithLp.toLp 2 x : EuclideanSpace ℂ C)‖ := by
  rw [← sq_le_sq₀ (norm_nonneg _) (by positivity),
    EuclideanSpace.norm_sq_eq, mul_pow, mul_pow, EuclideanSpace.norm_sq_eq]
  change (∑ i : C, ‖error i‖ ^ 2) ≤
    c ^ 2 * (Fintype.card B : ℝ) ^ 2 * (∑ i : C, ‖x i‖ ^ 2)
  rw [← equiv.sum_comp, ← equiv.sum_comp]
  simp only [Fintype.sum_prod_type]
  calc
    ∑ a, ∑ b, ‖error (equiv (a, b))‖ ^ 2 ≤
        ∑ a, ∑ _b : B, (c * ∑ j : B, ‖x (equiv (a, j))‖) ^ 2 := by
      apply Finset.sum_le_sum
      intro a ha
      apply Finset.sum_le_sum
      intro b hb
      exact (sq_le_sq₀ (norm_nonneg _) (by positivity)).2 (hpoint a b)
    _ = Fintype.card B * ∑ a,
        c ^ 2 * (∑ j : B, ‖x (equiv (a, j))‖) ^ 2 := by
      simp only [Finset.sum_const, Finset.card_univ, nsmul_eq_mul]
      simp_rw [← Finset.mul_sum]
      rw [Finset.mul_sum]
      rw [Finset.mul_sum]
      rw [Finset.mul_sum]
      ring
    _ ≤ Fintype.card B * ∑ a,
        c ^ 2 * (Fintype.card B * ∑ j : B, ‖x (equiv (a, j))‖ ^ 2) := by
      apply mul_le_mul_of_nonneg_left _ (by positivity)
      apply Finset.sum_le_sum
      intro a ha
      apply mul_le_mul_of_nonneg_left _ (sq_nonneg c)
      simpa only [Finset.sum_filter, Finset.mem_univ, ↓reduceIte] using
        (sq_sum_le_card_mul_sum_sq (s := Finset.univ)
          (f := fun j : B ↦ ‖x (equiv (a, j))‖))
    _ = (c * Fintype.card B) ^ 2 *
        ∑ a, ∑ b, ‖x (equiv (a, b))‖ ^ 2 := by
      push_cast
      simp_rw [← Finset.mul_sum]
      ring
    _ = c ^ 2 * (Fintype.card B : ℝ) ^ 2 *
        ∑ a, ∑ b, ‖x (equiv (a, b))‖ ^ 2 := by ring

private lemma p09_genericBlock_point_error {q : ℕ} [NeZero q]
    (hq : 3 ≤ q) (γ : ℝ) (hγ0 : 0 ≤ γ) :
    ∃ C : ℝ, 0 ≤ C ∧
      ∀ (model : P09WilkinsonModel) (e : ℝ), model.epsilon = e →
      model.gamma = γ → e ≤ 1 → ∀ (x : ZMod q → ℂ) (k : ZMod q),
      ‖p09RoundedGenericRadixBlock model x k -
          ∑ j : ZMod q, ZMod.stdAddChar (j * k) * x j‖ ≤
        (2 * ((q : ℝ) + γ) * e + C * e ^ 2) *
          (∑ j : ZMod q, ‖x j‖) := by
  obtain ⟨B, hB0, hsum⟩ := p09_roundedComplexSum_error (q := q)
  let A : ℝ := 3 + 2 * γ
  let C₀ : ℝ := 2 + 10 * γ
  let d : ℝ := Real.sqrt 2 * (q - 1 : ℕ)
  let C : ℝ := d * (A + C₀) + Real.sqrt 2 * B * (1 + A + C₀) + C₀
  have hA0 : 0 ≤ A := by dsimp [A]; positivity
  have hC₀0 : 0 ≤ C₀ := by dsimp [C₀]; positivity
  have hd0 : 0 ≤ d := by dsimp [d]; positivity
  have hC0 : 0 ≤ C := by dsimp [C]; positivity
  refine ⟨C, hC0, ?_⟩
  intro model e he hγ he1 x k
  let index : Fin q ≃ ZMod q := (ZMod.finEquiv q).toEquiv
  let rt : ZMod q → ℂ := fun j ↦
    p09RoundedComplexMul model (p09RoundedRoot model (j * k)) (x j)
  let et : ZMod q → ℂ := fun j ↦ p09ExactRoot (j * k) * x j
  let S : ℝ := ∑ i : Fin q, ‖x (index i)‖
  have he0 : 0 ≤ e := by rw [← he]; exact le_of_lt model.epsilon_pos
  have hS0 : 0 ≤ S := Finset.sum_nonneg fun _ _ ↦ norm_nonneg _
  have hterm : ∀ i : Fin q, ‖rt (index i) - et (index i)‖ ≤
      (A * e + C₀ * e ^ 2) * ‖x (index i)‖ := by
    intro i
    simpa [rt, et, A, C₀] using
      p09_rounded_root_mul_error model e γ he hγ hγ0 he1 (index i * k) (x (index i))
  have hrt : ∑ i : Fin q, ‖rt (index i)‖ ≤
      (1 + A * e + C₀ * e ^ 2) * S := by
    calc
      ∑ i : Fin q, ‖rt (index i)‖ ≤
          ∑ i : Fin q, (‖et (index i)‖ + ‖rt (index i) - et (index i)‖) := by
        apply Finset.sum_le_sum
        intro i hi
        have h := norm_add_le (et (index i)) (rt (index i) - et (index i))
        simpa [add_comm] using h
      _ ≤ ∑ i : Fin q,
          (‖x (index i)‖ + (A * e + C₀ * e ^ 2) * ‖x (index i)‖) := by
        apply Finset.sum_le_sum
        intro i hi
        apply add_le_add
        · simp [et, p09_exactRoot_norm]
        · exact hterm i
      _ = (1 + A * e + C₀ * e ^ 2) * S := by
        dsimp [S]
        rw [Finset.mul_sum]
        apply Finset.sum_congr rfl
        intro i hi
        ring
  have hsum' := hsum model e he he1 rt
  dsimp only at hsum'
  have hsum'' : ‖p09RoundedComplexSum model rt - ∑ i : Fin q, rt (index i)‖ ≤
      d * e * (∑ i : Fin q, ‖rt (index i)‖) +
        Real.sqrt 2 * B * e ^ 2 * (∑ i : Fin q, ‖rt (index i)‖) := by
    have hsum0 : ‖p09RoundedComplexSum model rt - ∑ i : Fin q, rt (index i)‖ ≤
        Real.sqrt 2 * e * (q - 1 : ℕ) * (∑ i : Fin q, ‖rt (index i)‖) +
          Real.sqrt 2 * B * e ^ 2 * (∑ i : Fin q, ‖rt (index i)‖) := by
      simpa [index] using hsum'
    calc
      _ ≤ _ := hsum0
      _ = _ := by dsimp [d]; ring
  have hsumBound : ‖p09RoundedComplexSum model rt - ∑ i : Fin q, rt (index i)‖ ≤
      (d * e + Real.sqrt 2 * B * e ^ 2) *
        ((1 + A * e + C₀ * e ^ 2) * S) := by
    calc
      _ ≤ d * e * (∑ i : Fin q, ‖rt (index i)‖) +
          Real.sqrt 2 * B * e ^ 2 * (∑ i : Fin q, ‖rt (index i)‖) := hsum''
      _ = (d * e + Real.sqrt 2 * B * e ^ 2) *
          (∑ i : Fin q, ‖rt (index i)‖) := by ring
      _ ≤ (d * e + Real.sqrt 2 * B * e ^ 2) *
          ((1 + A * e + C₀ * e ^ 2) * S) := by
        apply mul_le_mul_of_nonneg_left hrt
        positivity
  have hterms : ‖(∑ i : Fin q, rt (index i)) - ∑ i : Fin q, et (index i)‖ ≤
      (A * e + C₀ * e ^ 2) * S := by
    rw [← Finset.sum_sub_distrib]
    calc
      ‖∑ i : Fin q, (rt (index i) - et (index i))‖ ≤
          ∑ i : Fin q, ‖rt (index i) - et (index i)‖ := norm_sum_le _ _
      _ ≤ ∑ i : Fin q, (A * e + C₀ * e ^ 2) * ‖x (index i)‖ := by
        exact Finset.sum_le_sum fun i _ ↦ hterm i
      _ = (A * e + C₀ * e ^ 2) * S := by rw [Finset.mul_sum]
  have hraw : ‖p09RoundedComplexSum model rt - ∑ i : Fin q, et (index i)‖ ≤
      ((d + A) * e + C * e ^ 2) * S := by
    have htri : ‖p09RoundedComplexSum model rt - ∑ i : Fin q, et (index i)‖ ≤
        ‖p09RoundedComplexSum model rt - ∑ i : Fin q, rt (index i)‖ +
          ‖(∑ i : Fin q, rt (index i)) - ∑ i : Fin q, et (index i)‖ := by
      have := norm_add_le
        (p09RoundedComplexSum model rt - ∑ i : Fin q, rt (index i))
        ((∑ i : Fin q, rt (index i)) - ∑ i : Fin q, et (index i))
      simpa only [sub_add_sub_cancel] using this
    calc
      _ ≤ _ := htri
      _ ≤ (d * e + Real.sqrt 2 * B * e ^ 2) *
            ((1 + A * e + C₀ * e ^ 2) * S) +
          (A * e + C₀ * e ^ 2) * S := add_le_add hsumBound hterms
      _ ≤ ((d + A) * e + C * e ^ 2) * S := by
        rw [show (d * e + Real.sqrt 2 * B * e ^ 2) *
              ((1 + A * e + C₀ * e ^ 2) * S) +
              (A * e + C₀ * e ^ 2) * S =
            ((d * e + Real.sqrt 2 * B * e ^ 2) *
              (1 + A * e + C₀ * e ^ 2) + (A * e + C₀ * e ^ 2)) * S by ring]
        apply mul_le_mul_of_nonneg_right _ hS0
        have he2 : e ^ 2 ≤ e := by nlinarith [sq_nonneg e]
        have he3 : e ^ 3 ≤ e ^ 2 := by nlinarith [sq_nonneg e]
        have he4 : e ^ 4 ≤ e ^ 2 := by nlinarith [sq_nonneg (e ^ 2), sq_nonneg e]
        dsimp [C]
        nlinarith [mul_nonneg hd0 (sub_nonneg.mpr he3),
          mul_nonneg (mul_nonneg (Real.sqrt_nonneg 2) hB0) (sub_nonneg.mpr he3),
          mul_nonneg (mul_nonneg (Real.sqrt_nonneg 2) hB0) (sub_nonneg.mpr he4)]
  have hcoef : d + A ≤ 2 * ((q : ℝ) + γ) := by
    have hqR : (3 : ℝ) ≤ q := by exact_mod_cast hq
    have hqm : ((q - 1 : ℕ) : ℝ) = (q : ℝ) - 1 := by
      rw [Nat.cast_sub (by omega : 1 ≤ q)]
      norm_num
    dsimp [d, A]
    rw [hqm]
    nlinarith [p09_sqrt_two_le_three_halves,
      mul_nonneg (sub_nonneg.mpr (show (1 : ℝ) ≤ q by linarith))
        (sub_nonneg.mpr p09_sqrt_two_le_three_halves)]
  have hlinear : (d + A) * e ≤ 2 * ((q : ℝ) + γ) * e :=
    mul_le_mul_of_nonneg_right hcoef he0
  have hwhole : (d + A) * e + C * e ^ 2 ≤
      2 * ((q : ℝ) + γ) * e + C * e ^ 2 :=
    add_le_add hlinear le_rfl
  have hfinal := hraw.trans (mul_le_mul_of_nonneg_right hwhole hS0)
  have het : (∑ i : Fin q, et (index i)) =
      ∑ j : ZMod q, ZMod.stdAddChar (j * k) * x j := by
    rw [index.sum_comp]
    simp [et, p09_exactRoot_eq_stdAddChar]
  have hSn : S = ∑ j : ZMod q, ‖x j‖ := by
    dsimp [S]
    exact index.sum_comp (fun j ↦ ‖x j‖)
  rw [het, hSn] at hfinal
  simpa [p09RoundedGenericRadixBlock, rt] using hfinal

private lemma p09_stdAddChar_two_one : ZMod.stdAddChar (1 : ZMod 2) = (-1 : ℂ) := by
  rw [← p09_exactRoot_eq_stdAddChar]
  apply Complex.ext <;>
    norm_num [p09ExactRoot, p09RootAngle, ZMod.val_one]

private lemma p09_radixTwo_coeff_exact (x : ZMod 2 → ℂ) (k : ZMod 2) :
    (∑ j : ZMod 2, ZMod.stdAddChar (j * k) * x j) =
      ∑ i : Fin 2,
        p09RadixTwoCoefficientApply ((ZMod.finEquiv 2 i) * k) (x (ZMod.finEquiv 2 i)) := by
  rw [← (ZMod.finEquiv 2).sum_comp (fun j ↦ ZMod.stdAddChar (j * k) * x j)]
  apply Finset.sum_congr rfl
  intro i hi
  let z : ZMod 2 := (ZMod.finEquiv 2 i) * k
  by_cases hz : z = 0
  · simp [p09RadixTwoCoefficientApply, z, hz]
  · have hz1 : z = 1 := by
      have hzlt : z.val < 2 := z.val_lt
      interval_cases hval : z.val
      · exfalso
        apply hz
        apply ZMod.val_injective
        simp [hval]
      · apply ZMod.val_injective
        simpa [ZMod.val_one] using hval
    simp [p09RadixTwoCoefficientApply, z, hz, hz1, p09_stdAddChar_two_one]

private lemma p09_radixTwoBlock_point_error
    (model : P09WilkinsonModel) (e : ℝ) (he : model.epsilon = e)
    (x : ZMod 2 → ℂ) (k : ZMod 2) :
    ‖p09RoundedRadixTwoBlock model x k -
        ∑ j : ZMod 2, ZMod.stdAddChar (j * k) * x j‖ ≤
      e * (∑ j : ZMod 2, ‖x j‖) := by
  let index : Fin 2 ≃ ZMod 2 := (ZMod.finEquiv 2).toEquiv
  let t : Fin 2 → ℂ := fun i ↦
    p09RadixTwoCoefficientApply (index i * k) (x (index i))
  have hround : p09RoundedRadixTwoBlock model x k =
      p09RoundedComplexAdd model (t 0) (t 1) := by
    simp [p09RoundedRadixTwoBlock, p09RoundedComplexSum, p09RoundedComplexAdd,
      recursiveSum, t, index]
  have hexact : (∑ j : ZMod 2, ZMod.stdAddChar (j * k) * x j) = t 0 + t 1 := by
    rw [p09_radixTwo_coeff_exact]
    simp [Fin.sum_univ_succ, t, index]
  rw [hround, hexact]
  calc
    ‖p09RoundedComplexAdd model (t 0) (t 1) - (t 0 + t 1)‖ ≤
        e * (‖t 0‖ + ‖t 1‖) := p09_complex_add_error model e he _ _
    _ = e * (∑ j : ZMod 2, ‖x j‖) := by
      have ht : ∀ i, ‖t i‖ = ‖x (index i)‖ := by
        intro i
        simp only [t, p09RadixTwoCoefficientApply]
        split <;> simp
      rw [ht 0, ht 1, ← index.sum_comp (fun j ↦ ‖x j‖)]
      simp [Fin.sum_univ_succ]

private lemma p09_stdAddChar_four_one : ZMod.stdAddChar (1 : ZMod 4) = Complex.I := by
  rw [← p09_exactRoot_eq_stdAddChar]
  apply Complex.ext
  · change Real.cos (2 * Real.pi * (((1 : ZMod 4).val : ℕ) : ℝ) / 4) = 0
    have hv : (1 : ZMod 4).val = 1 :=
      ZMod.val_natCast_of_lt (n := 4) (a := 1) (by norm_num)
    rw [hv]
    convert Real.cos_pi_div_two using 1 <;> ring
  · change Real.sin (2 * Real.pi * (((1 : ZMod 4).val : ℕ) : ℝ) / 4) = 1
    have hv : (1 : ZMod 4).val = 1 :=
      ZMod.val_natCast_of_lt (n := 4) (a := 1) (by norm_num)
    rw [hv]
    convert Real.sin_pi_div_two using 1 <;> ring

private lemma p09_stdAddChar_four_two : ZMod.stdAddChar (2 : ZMod 4) = (-1 : ℂ) := by
  rw [← p09_exactRoot_eq_stdAddChar]
  apply Complex.ext
  · simp only [p09ExactRoot, Complex.neg_re, Complex.one_re]
    change Real.cos (2 * Real.pi * (((2 : ZMod 4).val : ℕ) : ℝ) / 4) = -1
    norm_num only [ZMod.val_ofNat]
    rw [show 2 * Real.pi * (2 : ℝ) / 4 = Real.pi by ring, Real.cos_pi]
  · simp only [p09ExactRoot, Complex.neg_im, Complex.one_im, neg_zero]
    change Real.sin (2 * Real.pi * (((2 : ZMod 4).val : ℕ) : ℝ) / 4) = 0
    norm_num only [ZMod.val_ofNat]
    rw [show 2 * Real.pi * (2 : ℝ) / 4 = Real.pi by ring, Real.sin_pi]

private lemma p09_stdAddChar_four_three : ZMod.stdAddChar (3 : ZMod 4) = -Complex.I := by
  rw [← p09_exactRoot_eq_stdAddChar]
  apply Complex.ext
  · simp only [p09ExactRoot, Complex.neg_re, Complex.I_re, neg_zero]
    change Real.cos (2 * Real.pi * (((3 : ZMod 4).val : ℕ) : ℝ) / 4) = 0
    norm_num only [ZMod.val_ofNat]
    rw [show 2 * Real.pi * (3 : ℝ) / 4 = Real.pi + Real.pi / 2 by ring,
      Real.cos_add, Real.cos_pi, Real.sin_pi, Real.cos_pi_div_two,
      Real.sin_pi_div_two]
    norm_num
  · simp only [p09ExactRoot, Complex.neg_im, Complex.I_im]
    change Real.sin (2 * Real.pi * (((3 : ZMod 4).val : ℕ) : ℝ) / 4) = -1
    norm_num only [ZMod.val_ofNat]
    rw [show 2 * Real.pi * (3 : ℝ) / 4 = Real.pi + Real.pi / 2 by ring,
      Real.sin_add, Real.cos_pi, Real.sin_pi, Real.cos_pi_div_two,
      Real.sin_pi_div_two]
    norm_num

private lemma p09_radixFour_coeff_apply_exact (z : ZMod 4) (x : ℂ) :
    p09RadixFourCoefficientApply z x = ZMod.stdAddChar z * x := by
  have hzlt : z.val < 4 := z.val_lt
  interval_cases hval : z.val
  · have hz : z = 0 := by apply ZMod.val_injective; simpa [hval]
    simp [hz, p09RadixFourCoefficientApply]
  · have hz : z = 1 := by
      apply ZMod.val_injective
      simpa [ZMod.val_one] using hval
    rw [hz, p09_stdAddChar_four_one]
    apply Complex.ext <;>
      simp [p09RadixFourCoefficientApply,
        show (1 : ZMod 4) ≠ 0 by decide] <;> ring
  · have hz : z = 2 := by
      apply ZMod.val_injective
      simpa [ZMod.val_ofNat_of_lt] using hval
    rw [hz, p09_stdAddChar_four_two]
    simp [p09RadixFourCoefficientApply,
      show (2 : ZMod 4) ≠ 0 by decide,
      show (2 : ZMod 4) ≠ 1 by decide]
  · have hz : z = 3 := by
      apply ZMod.val_injective
      simpa [ZMod.val_ofNat_of_lt] using hval
    rw [hz, p09_stdAddChar_four_three]
    apply Complex.ext <;>
      simp [p09RadixFourCoefficientApply,
        show (3 : ZMod 4) ≠ 0 by decide,
        show (3 : ZMod 4) ≠ 1 by decide,
        show (3 : ZMod 4) ≠ 2 by decide] <;> ring

private lemma p09_radixFour_coeff_exact (x : ZMod 4 → ℂ) (k : ZMod 4) :
    (∑ j : ZMod 4, ZMod.stdAddChar (j * k) * x j) =
      ∑ i : Fin 4,
        p09RadixFourCoefficientApply ((ZMod.finEquiv 4 i) * k) (x (ZMod.finEquiv 4 i)) := by
  rw [← (ZMod.finEquiv 4).sum_comp (fun j ↦ ZMod.stdAddChar (j * k) * x j)]
  apply Finset.sum_congr rfl
  intro i hi
  exact (p09_radixFour_coeff_apply_exact _ _).symm

private lemma p09_radixFourBlock_point_error
    (model : P09WilkinsonModel) (e : ℝ) (he : model.epsilon = e)
    (x : ZMod 4 → ℂ) (k : ZMod 4) :
    ‖p09RoundedRadixFourBlock model x k -
        ∑ j : ZMod 4, ZMod.stdAddChar (j * k) * x j‖ ≤
      (2 * e + e ^ 2) * (∑ j : ZMod 4, ‖x j‖) := by
  let index : Fin 4 ≃ ZMod 4 := (ZMod.finEquiv 4).toEquiv
  let t : Fin 4 → ℂ := fun i ↦
    p09RadixFourCoefficientApply (index i * k) (x (index i))
  let a := p09RoundedComplexAdd model (t 0) (t 1)
  let b := p09RoundedComplexAdd model (t 2) (t 3)
  let a₀ := t 0 + t 1
  let b₀ := t 2 + t 3
  let S := ‖t 0‖ + ‖t 1‖ + ‖t 2‖ + ‖t 3‖
  have he0 : 0 ≤ e := by rw [← he]; exact le_of_lt model.epsilon_pos
  have hS0 : 0 ≤ S := by dsimp [S]; positivity
  have ha : ‖a - a₀‖ ≤ e * (‖t 0‖ + ‖t 1‖) :=
    p09_complex_add_error model e he _ _
  have hb : ‖b - b₀‖ ≤ e * (‖t 2‖ + ‖t 3‖) :=
    p09_complex_add_error model e he _ _
  have hab : ‖a - a₀‖ + ‖b - b₀‖ ≤ e * S := by
    dsimp [S]
    linarith
  have hmags : ‖a‖ + ‖b‖ ≤ (1 + e) * S := by
    have ha' : ‖a‖ ≤ ‖a₀‖ + ‖a - a₀‖ := by
      have := norm_add_le a₀ (a - a₀)
      simpa [add_comm] using this
    have hb' : ‖b‖ ≤ ‖b₀‖ + ‖b - b₀‖ := by
      have := norm_add_le b₀ (b - b₀)
      simpa [add_comm] using this
    have ha0 : ‖a₀‖ ≤ ‖t 0‖ + ‖t 1‖ := norm_add_le _ _
    have hb0 : ‖b₀‖ ≤ ‖t 2‖ + ‖t 3‖ := norm_add_le _ _
    dsimp [S]
    nlinarith
  have hfinalRound : ‖p09RoundedComplexAdd model a b - (a + b)‖ ≤
      e * ((1 + e) * S) :=
    (p09_complex_add_error model e he a b).trans
      (mul_le_mul_of_nonneg_left hmags he0)
  have hdecomp : p09RoundedComplexAdd model a b - (a₀ + b₀) =
      (p09RoundedComplexAdd model a b - (a + b)) + (a - a₀) + (b - b₀) := by ring
  have hraw : ‖p09RoundedComplexAdd model a b - (a₀ + b₀)‖ ≤
      (2 * e + e ^ 2) * S := by
    rw [hdecomp]
    calc
      ‖(p09RoundedComplexAdd model a b - (a + b)) + (a - a₀) + (b - b₀)‖ ≤
          ‖p09RoundedComplexAdd model a b - (a + b)‖ +
            ‖a - a₀‖ + ‖b - b₀‖ := by
        calc
          _ ≤ ‖(p09RoundedComplexAdd model a b - (a + b)) + (a - a₀)‖ +
              ‖b - b₀‖ := norm_add_le _ _
          _ ≤ (‖p09RoundedComplexAdd model a b - (a + b)‖ + ‖a - a₀‖) +
              ‖b - b₀‖ := by
            have h := norm_add_le
              (p09RoundedComplexAdd model a b - (a + b)) (a - a₀)
            linarith
      _ ≤ e * ((1 + e) * S) + e * S := by linarith
      _ = (2 * e + e ^ 2) * S := by ring
  have hround : p09RoundedRadixFourBlock model x k =
      p09RoundedComplexAdd model a b := by
    simp [p09RoundedRadixFourBlock, a, b, t, index]
  have hexact : (∑ j : ZMod 4, ZMod.stdAddChar (j * k) * x j) = a₀ + b₀ := by
    rw [p09_radixFour_coeff_exact]
    simp [Fin.sum_univ_succ, a₀, b₀, t, index]
    ring
  rw [hround, hexact]
  have ht : ∀ i, ‖t i‖ = ‖x (index i)‖ := by
    intro i
    dsimp [t]
    rw [p09_radixFour_coeff_apply_exact, norm_mul]
    simp
  have hSn : S = ∑ j : ZMod 4, ‖x j‖ := by
    dsimp [S]
    rw [ht 0, ht 1, ht 2, ht 3, ← index.sum_comp (fun j ↦ ‖x j‖)]
    simp [Fin.sum_univ_succ]
    ring
  rw [← hSn]
  exact hraw

private lemma p09_radixTwoBlock_point_error_cast {q : ℕ} [NeZero q]
    (hq : q = 2) (model : P09WilkinsonModel) (e : ℝ)
    (he : model.epsilon = e) (x : ZMod q → ℂ) (k : ZMod q) :
    ‖p09RoundedRadixTwoBlock model (fun j : ZMod 2 ↦ x (hq.symm ▸ j)) (hq ▸ k) -
        ∑ j : ZMod q, ZMod.stdAddChar (j * k) * x j‖ ≤
      e * (∑ j : ZMod q, ‖x j‖) := by
  subst q
  simpa using p09_radixTwoBlock_point_error model e he x k

private lemma p09_radixFourBlock_point_error_cast {q : ℕ} [NeZero q]
    (hq : q = 4) (model : P09WilkinsonModel) (e : ℝ)
    (he : model.epsilon = e) (x : ZMod q → ℂ) (k : ZMod q) :
    ‖p09RoundedRadixFourBlock model (fun j : ZMod 4 ↦ x (hq.symm ▸ j)) (hq ▸ k) -
        ∑ j : ZMod q, ZMod.stdAddChar (j * k) * x j‖ ≤
      (2 * e + e ^ 2) * (∑ j : ZMod q, ‖x j‖) := by
  subst q
  simpa using p09_radixFourBlock_point_error model e he x k

private lemma p09_l2_equiv {A B : Type*} [Fintype A] [Fintype B]
    (equiv : A ≃ B) (x : B → ℂ) :
    ‖(WithLp.toLp 2 (fun i ↦ x (equiv i)) : EuclideanSpace ℂ A)‖ =
      ‖(WithLp.toLp 2 x : EuclideanSpace ℂ B)‖ := by
  rw [← sq_eq_sq₀ (norm_nonneg _) (norm_nonneg _),
    EuclideanSpace.norm_sq_eq, EuclideanSpace.norm_sq_eq]
  change (∑ i : A, ‖x (equiv i)‖ ^ 2) = ∑ i : B, ‖x i‖ ^ 2
  exact equiv.sum_comp (fun i ↦ ‖x i‖ ^ 2)

private lemma p09_complexNorm2_eq_l2 {q : ℕ} [NeZero q] (x : ZMod q → ℂ) :
    p09ComplexNorm2 x =
      ‖(WithLp.toLp 2 x : EuclideanSpace ℂ (ZMod q))‖ := by
  rw [p09ComplexNorm2, p09ComplexNorm2Sq, EuclideanSpace.norm_eq]

private lemma p09_stageBlock_error {n : ℕ} [NeZero n]
    (stage : P09MixedRadixStage n) (γ : ℝ) (hγ0 : 0 ≤ γ) :
  ∃ C : ℝ, 0 ≤ C ∧
    ∀ (model : P09WilkinsonModel) (e : ℝ), model.epsilon = e →
    model.gamma = γ → e ≤ 1 → ∀ x : ZMod n → ℂ,
      p09ComplexNorm2
          (fun i ↦ p09RoundedMixedRadixBlockApply model stage x i -
            p09MixedRadixBlockApply stage x i) ≤
        (Real.sqrt stage.radix * p09Alpha stage.radix γ * e + C * e ^ 2) *
          p09ComplexNorm2 x := by
  letI : NeZero stage.radix := ⟨stage.radix_ne_zero⟩
  by_cases h2 : stage.radix = 2
  · refine ⟨0, le_rfl, ?_⟩
    intro model e he hγ he1 x
    let permuted : ZMod n → ℂ := fun i ↦ x (stage.permutation i)
    let error : ZMod n → ℂ := fun i ↦
      p09RoundedMixedRadixBlockApply model stage x i -
        p09MixedRadixBlockApply stage x i
    have hpoint : ∀ b : Fin stage.blockCount, ∀ k : ZMod stage.radix,
        ‖error (stage.reindex (b, k))‖ ≤
          e * (∑ j : ZMod stage.radix, ‖permuted (stage.reindex (b, j))‖) := by
      intro b k
      have hp := p09_radixTwoBlock_point_error_cast h2 model e he
        (fun j ↦ permuted (stage.reindex (b, j))) k
      simpa [error, permuted, p09RoundedMixedRadixBlockApply,
        p09MixedRadixBlockApply, h2] using hp
    have hl2 := p09_partition_l1_l2_bound stage.reindex permuted error e
      (by rw [← he]; exact le_of_lt model.epsilon_pos) hpoint
    rw [ZMod.card, h2] at hl2
    rw [p09_complexNorm2_eq_l2, p09_complexNorm2_eq_l2]
    calc
      ‖WithLp.toLp 2 error‖ ≤ e * 2 * ‖WithLp.toLp 2 permuted‖ := hl2
      _ = (Real.sqrt stage.radix * p09Alpha stage.radix γ * e + 0 * e ^ 2) *
          ‖WithLp.toLp 2 x‖ := by
        rw [p09_l2_equiv stage.permutation x]
        have hc : e * 2 = Real.sqrt stage.radix * p09Alpha stage.radix γ * e := by
          simp [p09Alpha, h2]
          ring
        rw [hc]
        ring
  · by_cases h4 : stage.radix = 4
    · refine ⟨4, by norm_num, ?_⟩
      intro model e he hγ he1 x
      let permuted : ZMod n → ℂ := fun i ↦ x (stage.permutation i)
      let error : ZMod n → ℂ := fun i ↦
        p09RoundedMixedRadixBlockApply model stage x i -
          p09MixedRadixBlockApply stage x i
      have hpoint : ∀ b : Fin stage.blockCount, ∀ k : ZMod stage.radix,
          ‖error (stage.reindex (b, k))‖ ≤
            (2 * e + e ^ 2) *
              (∑ j : ZMod stage.radix, ‖permuted (stage.reindex (b, j))‖) := by
        intro b k
        have hp := p09_radixFourBlock_point_error_cast h4 model e he
          (fun j ↦ permuted (stage.reindex (b, j))) k
        simpa [error, permuted, p09RoundedMixedRadixBlockApply,
          p09MixedRadixBlockApply, h2, h4] using hp
      have hc0 : 0 ≤ 2 * e + e ^ 2 := by
        have : 0 ≤ e := by rw [← he]; exact le_of_lt model.epsilon_pos
        positivity
      have hl2 := p09_partition_l1_l2_bound stage.reindex permuted error
        (2 * e + e ^ 2) hc0 hpoint
      rw [ZMod.card, h4] at hl2
      rw [p09_complexNorm2_eq_l2, p09_complexNorm2_eq_l2]
      calc
        ‖WithLp.toLp 2 error‖ ≤ (2 * e + e ^ 2) * 4 *
            ‖WithLp.toLp 2 permuted‖ := hl2
        _ ≤ (Real.sqrt stage.radix * p09Alpha stage.radix γ * e + 4 * e ^ 2) *
            ‖WithLp.toLp 2 x‖ := by
          rw [p09_l2_equiv stage.permutation x]
          apply mul_le_mul_of_nonneg_right _ (norm_nonneg _)
          have hs : Real.sqrt (stage.radix : ℝ) = 2 := by
            rw [h4]
            norm_num
          rw [hs]
          simp [p09Alpha, h4]
          have he0 : 0 ≤ e := by rw [← he]; exact le_of_lt model.epsilon_pos
          nlinarith
    · have hq3 : 3 ≤ stage.radix := by
        have hr2 := stage.radix_two_le
        omega
      obtain ⟨C₀, hC₀0, hp⟩ :=
        p09_genericBlock_point_error hq3 γ hγ0
      refine ⟨stage.radix * C₀, by positivity, ?_⟩
      intro model e he hγ he1 x
      let permuted : ZMod n → ℂ := fun i ↦ x (stage.permutation i)
      let error : ZMod n → ℂ := fun i ↦
        p09RoundedMixedRadixBlockApply model stage x i -
          p09MixedRadixBlockApply stage x i
      have hpoint : ∀ b : Fin stage.blockCount, ∀ k : ZMod stage.radix,
          ‖error (stage.reindex (b, k))‖ ≤
            (2 * ((stage.radix : ℝ) + γ) * e + C₀ * e ^ 2) *
              (∑ j : ZMod stage.radix, ‖permuted (stage.reindex (b, j))‖) := by
        intro b k
        simpa [error, permuted, p09RoundedMixedRadixBlockApply,
          p09MixedRadixBlockApply, h2, h4] using
          hp model e he hγ he1 (fun j ↦ permuted (stage.reindex (b, j))) k
      have hc0 : 0 ≤ 2 * ((stage.radix : ℝ) + γ) * e + C₀ * e ^ 2 := by
        have he0 : 0 ≤ e := by rw [← he]; exact le_of_lt model.epsilon_pos
        have hq0 : (0 : ℝ) ≤ stage.radix := by exact_mod_cast Nat.zero_le stage.radix
        positivity
      have hl2 := p09_partition_l1_l2_bound stage.reindex permuted error
        _ hc0 hpoint
      rw [ZMod.card] at hl2
      rw [p09_complexNorm2_eq_l2, p09_complexNorm2_eq_l2]
      calc
        ‖WithLp.toLp 2 error‖ ≤
            (2 * ((stage.radix : ℝ) + γ) * e + C₀ * e ^ 2) *
              stage.radix * ‖WithLp.toLp 2 permuted‖ := hl2
        _ = (Real.sqrt stage.radix * p09Alpha stage.radix γ * e +
              stage.radix * C₀ * e ^ 2) * ‖WithLp.toLp 2 x‖ := by
          rw [p09_l2_equiv stage.permutation x]
          have hq0 : (0 : ℝ) ≤ stage.radix := by exact_mod_cast Nat.zero_le stage.radix
          have hs : Real.sqrt (stage.radix : ℝ) ^ 2 = stage.radix := Real.sq_sqrt hq0
          simp only [p09Alpha, h2, if_false, h4]
          rw [show Real.sqrt (stage.radix : ℝ) *
              (2 * Real.sqrt stage.radix * ((stage.radix : ℝ) + γ)) =
              2 * (Real.sqrt stage.radix ^ 2) * ((stage.radix : ℝ) + γ) by ring,
            hs]
          ring

private lemma p09_pointwise_l2_bound {A : Type*} [Fintype A]
    (x error : A → ℂ) (c : ℝ) (hc : 0 ≤ c)
    (hpoint : ∀ i, ‖error i‖ ≤ c * ‖x i‖) :
    ‖(WithLp.toLp 2 error : EuclideanSpace ℂ A)‖ ≤
      c * ‖(WithLp.toLp 2 x : EuclideanSpace ℂ A)‖ := by
  rw [← sq_le_sq₀ (norm_nonneg _) (by positivity),
    EuclideanSpace.norm_sq_eq, mul_pow, EuclideanSpace.norm_sq_eq]
  change (∑ i : A, ‖error i‖ ^ 2) ≤ c ^ 2 * ∑ i : A, ‖x i‖ ^ 2
  rw [Finset.mul_sum]
  apply Finset.sum_le_sum
  intro i hi
  have h := (sq_le_sq₀ (norm_nonneg _) (by positivity)).2 (hpoint i)
  simpa [mul_pow] using h

private lemma p09_twiddle_norm {n : ℕ} [NeZero n]
    (stage : P09MixedRadixStage n) (x : ZMod n → ℂ) :
    p09ComplexNorm2 (p09MixedRadixTwiddleApply stage x) = p09ComplexNorm2 x := by
  rw [p09_complexNorm2_eq_l2, p09_complexNorm2_eq_l2,
    ← sq_eq_sq₀ (norm_nonneg _) (norm_nonneg _),
    EuclideanSpace.norm_sq_eq, EuclideanSpace.norm_sq_eq]
  apply Finset.sum_congr rfl
  intro i hi
  by_cases ht : stage.useTwiddle
  · simp [p09MixedRadixTwiddleApply, ht, norm_mul,
      ← p09_exactRoot_eq_stdAddChar, p09_exactRoot_norm]
  · simp [p09MixedRadixTwiddleApply, ht]

private lemma p09_twiddle_error {n : ℕ} [NeZero n]
    (stage : P09MixedRadixStage n) (γ : ℝ) (hγ0 : 0 ≤ γ) :
    ∃ C : ℝ, 0 ≤ C ∧
      ∀ (model : P09WilkinsonModel) (e : ℝ), model.epsilon = e →
      model.gamma = γ → e ≤ 1 → ∀ x : ZMod n → ℂ,
      p09ComplexNorm2
          (fun i ↦ p09RoundedMixedRadixTwiddleApply model stage x i -
            p09MixedRadixTwiddleApply stage x i) ≤
        (((if stage.useTwiddle then 3 + 2 * γ else 0) * e) + C * e ^ 2) *
          p09ComplexNorm2 x := by
  by_cases ht : stage.useTwiddle
  · refine ⟨2 + 10 * γ, by positivity, ?_⟩
    intro model e he hγ he1 x
    rw [p09_complexNorm2_eq_l2, p09_complexNorm2_eq_l2]
    apply p09_pointwise_l2_bound _ _ _ (by
      have he0 : 0 ≤ e := by rw [← he]; exact le_of_lt model.epsilon_pos
      simp [ht]
      positivity)
    intro i
    simpa [p09RoundedMixedRadixTwiddleApply, p09MixedRadixTwiddleApply,
      ht, p09_exactRoot_eq_stdAddChar] using
      p09_rounded_root_mul_error model e γ he hγ hγ0 he1
        (stage.twiddleExponent i) (x i)
  · refine ⟨0, le_rfl, ?_⟩
    intro model e he hγ he1 x
    simp [p09RoundedMixedRadixTwiddleApply, p09MixedRadixTwiddleApply, ht,
      p09ComplexNorm2Sq, p09ComplexNorm2]

private lemma p09_stage_error {n : ℕ} [NeZero n]
    (stage : P09MixedRadixStage n) (γ : ℝ) (hγ0 : 0 ≤ γ)
    (hexactScale : ∀ x : ZMod n → ℂ,
      p09ComplexNorm2 (p09MixedRadixStageApply stage x) =
        Real.sqrt stage.radix * p09ComplexNorm2 x) :
    ∃ C : ℝ, 0 ≤ C ∧
      ∀ (model : P09WilkinsonModel) (e : ℝ), model.epsilon = e →
      model.gamma = γ → e ≤ 1 → ∀ x : ZMod n → ℂ,
      p09ComplexNorm2
          (fun i ↦ p09RoundedMixedRadixStageApply model stage x i -
            p09MixedRadixStageApply stage x i) ≤
        (Real.sqrt stage.radix *
            (p09Alpha stage.radix γ +
              if stage.useTwiddle then 3 + 2 * γ else 0) * e + C * e ^ 2) *
          p09ComplexNorm2 x := by
  obtain ⟨Cb, hCb0, hb⟩ := p09_stageBlock_error stage γ hγ0
  obtain ⟨Ct, hCt0, ht⟩ := p09_twiddle_error stage γ hγ0
  let a : ℝ := Real.sqrt stage.radix * p09Alpha stage.radix γ
  let t : ℝ := if stage.useTwiddle then 3 + 2 * γ else 0
  let C : ℝ := Ct * (Real.sqrt stage.radix + a + Cb) + t * (a + Cb) + Cb
  have hs0 : 0 ≤ Real.sqrt stage.radix := Real.sqrt_nonneg _
  have halpha0 : 0 ≤ p09Alpha stage.radix γ := by
    simp [p09Alpha]
    split <;> positivity
  have ha0 : 0 ≤ a := mul_nonneg hs0 halpha0
  have ht0 : 0 ≤ t := by
    dsimp [t]
    split <;> positivity
  have hC0 : 0 ≤ C := by dsimp [C]; positivity
  refine ⟨C, hC0, ?_⟩
  intro model e he hγ he1 x
  have he0 : 0 ≤ e := by rw [← he]; exact le_of_lt model.epsilon_pos
  let bx := p09RoundedMixedRadixBlockApply model stage x
  let b₀ := p09MixedRadixBlockApply stage x
  let rtw := p09RoundedMixedRadixTwiddleApply model stage
  let tw := p09MixedRadixTwiddleApply stage
  have hb' : p09ComplexNorm2 (fun i ↦ bx i - b₀ i) ≤
      (a * e + Cb * e ^ 2) * p09ComplexNorm2 x := by
    simpa [bx, b₀, a] using hb model e he hγ he1 x
  have hbmag : p09ComplexNorm2 bx ≤
      (Real.sqrt stage.radix + a * e + Cb * e ^ 2) * p09ComplexNorm2 x := by
    have htri : p09ComplexNorm2 bx ≤
        p09ComplexNorm2 b₀ + p09ComplexNorm2 (fun i ↦ bx i - b₀ i) := by
      rw [p09_complexNorm2_eq_l2, p09_complexNorm2_eq_l2, p09_complexNorm2_eq_l2]
      have heq : (WithLp.toLp 2 bx : EuclideanSpace ℂ (ZMod n)) =
          WithLp.toLp 2 b₀ + WithLp.toLp 2 (fun i ↦ bx i - b₀ i) := by
        ext i
        simp
      rw [heq]
      exact norm_add_le _ _
    have hb0norm : p09ComplexNorm2 b₀ = Real.sqrt stage.radix * p09ComplexNorm2 x := by
      rw [← hexactScale x]
      exact (p09_twiddle_norm stage b₀).symm
    calc
      p09ComplexNorm2 bx ≤
          p09ComplexNorm2 b₀ + p09ComplexNorm2 (fun i ↦ bx i - b₀ i) := htri
      _ ≤ Real.sqrt stage.radix * p09ComplexNorm2 x +
          (a * e + Cb * e ^ 2) * p09ComplexNorm2 x := by
        rw [hb0norm]
        gcongr
      _ = (Real.sqrt stage.radix + a * e + Cb * e ^ 2) *
          p09ComplexNorm2 x := by ring
  have htw := ht model e he hγ he1 bx
  have hdecomp : (fun i ↦ rtw bx i - tw b₀ i) =
      (fun i ↦ (rtw bx i - tw bx i) + tw (fun j ↦ bx j - b₀ j) i) := by
    funext i
    by_cases hu : stage.useTwiddle
    · simp [tw, p09MixedRadixTwiddleApply, hu]
      ring
    · simp [tw, p09MixedRadixTwiddleApply, hu]
  change p09ComplexNorm2 (fun i ↦ rtw bx i - tw b₀ i) ≤ _
  rw [hdecomp]
  have htri : p09ComplexNorm2
      (fun i ↦ (rtw bx i - tw bx i) + tw (fun j ↦ bx j - b₀ j) i) ≤
      p09ComplexNorm2 (fun i ↦ rtw bx i - tw bx i) +
        p09ComplexNorm2 (tw (fun j ↦ bx j - b₀ j)) := by
    rw [p09_complexNorm2_eq_l2, p09_complexNorm2_eq_l2, p09_complexNorm2_eq_l2]
    have h := norm_add_le
      (WithLp.toLp 2 (fun i ↦ rtw bx i - tw bx i) : EuclideanSpace ℂ (ZMod n))
      (WithLp.toLp 2 (fun i ↦ tw (fun j ↦ bx j - b₀ j) i) :
        EuclideanSpace ℂ (ZMod n))
    simpa only [WithLp.toLp_add] using h
  calc
    _ ≤ _ := htri
    _ = p09ComplexNorm2 (fun i ↦ rtw bx i - tw bx i) +
        p09ComplexNorm2 (fun j ↦ bx j - b₀ j) := by
      rw [p09_twiddle_norm]
    _ ≤ (t * e + Ct * e ^ 2) * p09ComplexNorm2 bx +
        (a * e + Cb * e ^ 2) * p09ComplexNorm2 x := add_le_add (by
          simpa [rtw, tw, t] using htw) hb'
    _ ≤ (t * e + Ct * e ^ 2) *
          ((Real.sqrt stage.radix + a * e + Cb * e ^ 2) * p09ComplexNorm2 x) +
        (a * e + Cb * e ^ 2) * p09ComplexNorm2 x := by
      gcongr
    _ ≤ (Real.sqrt stage.radix * (p09Alpha stage.radix γ + t) * e +
          C * e ^ 2) * p09ComplexNorm2 x := by
      rw [show (t * e + Ct * e ^ 2) *
            ((Real.sqrt stage.radix + a * e + Cb * e ^ 2) * p09ComplexNorm2 x) +
            (a * e + Cb * e ^ 2) * p09ComplexNorm2 x =
          ((t * e + Ct * e ^ 2) *
            (Real.sqrt stage.radix + a * e + Cb * e ^ 2) +
            (a * e + Cb * e ^ 2)) * p09ComplexNorm2 x by ring]
      apply mul_le_mul_of_nonneg_right _ (by
        unfold p09ComplexNorm2
        positivity)
      have he3 : e ^ 3 ≤ e ^ 2 := by nlinarith [sq_nonneg e]
      have he4 : e ^ 4 ≤ e ^ 2 := by nlinarith [sq_nonneg (e ^ 2), sq_nonneg e]
      dsimp [C, a]
      nlinarith [mul_nonneg (mul_nonneg hCt0 ha0) (sub_nonneg.mpr he3),
        mul_nonneg (mul_nonneg hCt0 hCb0) (sub_nonneg.mpr he4),
        mul_nonneg (mul_nonneg ht0 hCb0) (sub_nonneg.mpr he3)]

private noncomputable def p09ExactStageList {n : ℕ} [NeZero n]
    (stages : List (P09MixedRadixStage n)) (x : ZMod n → ℂ) : ZMod n → ℂ :=
  stages.foldl (fun state stage ↦ p09MixedRadixStageApply stage state) x

private noncomputable def p09RoundedStageList {n : ℕ} [NeZero n]
    (model : P09WilkinsonModel) (stages : List (P09MixedRadixStage n))
    (x : ZMod n → ℂ) : ZMod n → ℂ :=
  stages.foldl (fun state stage ↦ p09RoundedMixedRadixStageApply model stage state) x

private noncomputable def p09StageScale {n : ℕ} [NeZero n]
    (stages : List (P09MixedRadixStage n)) : ℝ :=
  (stages.map fun stage ↦ Real.sqrt (stage.radix : ℝ)).prod

private noncomputable def p09StageFirst {n : ℕ} [NeZero n]
    (stages : List (P09MixedRadixStage n)) (γ : ℝ) : ℝ :=
  (stages.map fun stage ↦ p09Alpha stage.radix γ +
    if stage.useTwiddle then 3 + 2 * γ else 0).sum

private lemma p09_stage_sub {n : ℕ} [NeZero n]
    (stage : P09MixedRadixStage n) (x y : ZMod n → ℂ) :
    p09MixedRadixStageApply stage (fun i ↦ x i - y i) =
      (fun i ↦ p09MixedRadixStageApply stage x i -
        p09MixedRadixStageApply stage y i) := by
  funext i
  simp only [p09MixedRadixStageApply, p09MixedRadixTwiddleApply,
    p09MixedRadixBlockApply]
  split
  · simp only [mul_sub, Finset.sum_sub_distrib]
  · simp only [mul_sub, Finset.sum_sub_distrib]

private lemma p09_exactStageList_sub {n : ℕ} [NeZero n]
    (stages : List (P09MixedRadixStage n)) (x y : ZMod n → ℂ) :
    p09ExactStageList stages (fun i ↦ x i - y i) =
      (fun i ↦ p09ExactStageList stages x i - p09ExactStageList stages y i) := by
  induction stages generalizing x y with
  | nil => rfl
  | cons stage stages ih =>
      simp only [p09ExactStageList, List.foldl_cons]
      rw [p09_stage_sub stage x y]
      exact ih _ _

private lemma p09_exactStageList_norm {n : ℕ} [NeZero n]
    (stages : List (P09MixedRadixStage n))
    (hscale : ∀ stage ∈ stages, ∀ x : ZMod n → ℂ,
      p09ComplexNorm2 (p09MixedRadixStageApply stage x) =
        Real.sqrt stage.radix * p09ComplexNorm2 x)
    (x : ZMod n → ℂ) :
    p09ComplexNorm2 (p09ExactStageList stages x) =
      p09StageScale stages * p09ComplexNorm2 x := by
  induction stages generalizing x with
  | nil => simp [p09ExactStageList, p09StageScale]
  | cons stage stages ih =>
      rw [show p09ExactStageList (stage :: stages) x =
        p09ExactStageList stages (p09MixedRadixStageApply stage x) by rfl,
        ih (fun s hs ↦ hscale s (by simp [hs])), hscale stage (by simp)]
      simp [p09StageScale]
      ring

private lemma p09_stageFirst_nonneg {n : ℕ} [NeZero n]
    (stages : List (P09MixedRadixStage n)) (γ : ℝ) (hγ0 : 0 ≤ γ) :
    0 ≤ p09StageFirst stages γ := by
  unfold p09StageFirst
  apply List.sum_nonneg
  intro a ha
  obtain ⟨stage, hstage, rfl⟩ := List.mem_map.mp ha
  have halpha : 0 ≤ p09Alpha stage.radix γ := by
    simp [p09Alpha]
    split <;> positivity
  split <;> positivity

private lemma p09_stageScale_nonneg {n : ℕ} [NeZero n]
    (stages : List (P09MixedRadixStage n)) : 0 ≤ p09StageScale stages := by
  unfold p09StageScale
  exact List.prod_nonneg fun a ha ↦ by
    obtain ⟨stage, hstage, rfl⟩ := List.mem_map.mp ha
    exact Real.sqrt_nonneg _

private lemma p09_complexNorm2_triangle_sub {n : ℕ} [NeZero n]
    (x y z : ZMod n → ℂ) :
    p09ComplexNorm2 (fun i ↦ x i - z i) ≤
      p09ComplexNorm2 (fun i ↦ x i - y i) +
        p09ComplexNorm2 (fun i ↦ y i - z i) := by
  rw [p09_complexNorm2_eq_l2, p09_complexNorm2_eq_l2, p09_complexNorm2_eq_l2]
  have heq : (WithLp.toLp 2 (fun i ↦ x i - z i) :
      EuclideanSpace ℂ (ZMod n)) =
      WithLp.toLp 2 (fun i ↦ x i - y i) +
        WithLp.toLp 2 (fun i ↦ y i - z i) := by
    ext i
    simp
  rw [heq]
  exact norm_add_le _ _

private lemma p09_complexNorm2_le_add_error {n : ℕ} [NeZero n]
    (x y : ZMod n → ℂ) :
    p09ComplexNorm2 x ≤ p09ComplexNorm2 y +
      p09ComplexNorm2 (fun i ↦ x i - y i) := by
  rw [p09_complexNorm2_eq_l2, p09_complexNorm2_eq_l2, p09_complexNorm2_eq_l2]
  have heq : (WithLp.toLp 2 x : EuclideanSpace ℂ (ZMod n)) =
      WithLp.toLp 2 y + WithLp.toLp 2 (fun i ↦ x i - y i) := by
    ext i
    simp
  rw [heq]
  exact norm_add_le _ _

private lemma p09_stageList_error {n : ℕ} [NeZero n]
    (stages : List (P09MixedRadixStage n)) (γ : ℝ) (hγ0 : 0 ≤ γ)
    (hscale : ∀ stage ∈ stages, ∀ x : ZMod n → ℂ,
      p09ComplexNorm2 (p09MixedRadixStageApply stage x) =
        Real.sqrt stage.radix * p09ComplexNorm2 x) :
    ∃ C : ℝ, 0 ≤ C ∧
      ∀ (model : P09WilkinsonModel) (e : ℝ), model.epsilon = e →
      model.gamma = γ → e ≤ 1 → ∀ x : ZMod n → ℂ,
      p09ComplexNorm2
          (fun i ↦ p09RoundedStageList model stages x i -
            p09ExactStageList stages x i) ≤
        (p09StageScale stages * p09StageFirst stages γ * e + C * e ^ 2) *
          p09ComplexNorm2 x := by
  induction stages with
  | nil =>
      refine ⟨0, le_rfl, ?_⟩
      intro model e he hγ he1 x
      simp [p09RoundedStageList, p09ExactStageList, p09StageScale,
        p09StageFirst, p09ComplexNorm2Sq, p09ComplexNorm2]
  | cons stage stages ih =>
      have hscaleTail : ∀ s ∈ stages, ∀ x : ZMod n → ℂ,
          p09ComplexNorm2 (p09MixedRadixStageApply s x) =
            Real.sqrt s.radix * p09ComplexNorm2 x := by
        intro s hs
        exact hscale s (by simp [hs])
      obtain ⟨Ct, hCt0, htail⟩ := ih hscaleTail
      obtain ⟨Ch, hCh0, hhead⟩ := p09_stage_error stage γ hγ0
        (hscale stage (by simp))
      let sh : ℝ := Real.sqrt stage.radix
      let ah : ℝ := p09Alpha stage.radix γ +
        if stage.useTwiddle then 3 + 2 * γ else 0
      let st : ℝ := p09StageScale stages
      let tailA : ℝ := p09StageFirst stages γ
      let B : ℝ := st * tailA
      let C : ℝ := B * sh * ah + Ct * sh + st * Ch + B * Ch +
        Ct * sh * ah + Ct * Ch
      have hsh0 : 0 ≤ sh := Real.sqrt_nonneg _
      have hah0 : 0 ≤ ah := by
        dsimp [ah]
        have halpha : 0 ≤ p09Alpha stage.radix γ := by
          simp [p09Alpha]
          split <;> positivity
        split <;> positivity
      have hst0 : 0 ≤ st := p09_stageScale_nonneg stages
      have htailA0 : 0 ≤ tailA := p09_stageFirst_nonneg stages γ hγ0
      have hB0 : 0 ≤ B := mul_nonneg hst0 htailA0
      have hC0 : 0 ≤ C := by dsimp [C]; positivity
      refine ⟨C, hC0, ?_⟩
      intro model e he hγ he1 x
      have he0 : 0 ≤ e := by rw [← he]; exact le_of_lt model.epsilon_pos
      let rh := p09RoundedMixedRadixStageApply model stage x
      let eh := p09MixedRadixStageApply stage x
      let rt := p09RoundedStageList model stages rh
      let etr := p09ExactStageList stages rh
      let ete := p09ExactStageList stages eh
      have hhead' : p09ComplexNorm2 (fun i ↦ rh i - eh i) ≤
          (sh * ah * e + Ch * e ^ 2) * p09ComplexNorm2 x := by
        simpa [rh, eh, sh, ah, mul_assoc] using hhead model e he hγ he1 x
      have hrh : p09ComplexNorm2 rh ≤
          (sh + sh * ah * e + Ch * e ^ 2) * p09ComplexNorm2 x := by
        calc
          p09ComplexNorm2 rh ≤ p09ComplexNorm2 eh +
              p09ComplexNorm2 (fun i ↦ rh i - eh i) :=
            p09_complexNorm2_le_add_error rh eh
          _ ≤ sh * p09ComplexNorm2 x +
              (sh * ah * e + Ch * e ^ 2) * p09ComplexNorm2 x := by
            rw [show p09ComplexNorm2 eh = sh * p09ComplexNorm2 x by
              simpa [eh, sh] using hscale stage (by simp) x]
            gcongr
          _ = (sh + sh * ah * e + Ch * e ^ 2) * p09ComplexNorm2 x := by ring
      have htail' : p09ComplexNorm2 (fun i ↦ rt i - etr i) ≤
          (B * e + Ct * e ^ 2) * p09ComplexNorm2 rh := by
        simpa [rt, etr, B] using htail model e he hγ he1 rh
      have hexactDiff : p09ComplexNorm2 (fun i ↦ etr i - ete i) =
          st * p09ComplexNorm2 (fun i ↦ rh i - eh i) := by
        rw [← p09_exactStageList_sub stages rh eh]
        exact p09_exactStageList_norm stages hscaleTail _
      have htri := p09_complexNorm2_triangle_sub rt etr ete
      change p09ComplexNorm2 (fun i ↦ rt i - ete i) ≤ _
      calc
        p09ComplexNorm2 (fun i ↦ rt i - ete i) ≤
            p09ComplexNorm2 (fun i ↦ rt i - etr i) +
              p09ComplexNorm2 (fun i ↦ etr i - ete i) := htri
        _ ≤ (B * e + Ct * e ^ 2) * p09ComplexNorm2 rh +
              st * ((sh * ah * e + Ch * e ^ 2) * p09ComplexNorm2 x) := by
            rw [hexactDiff]
            exact add_le_add htail' (mul_le_mul_of_nonneg_left hhead' hst0)
        _ ≤ (B * e + Ct * e ^ 2) *
              ((sh + sh * ah * e + Ch * e ^ 2) * p09ComplexNorm2 x) +
              st * ((sh * ah * e + Ch * e ^ 2) * p09ComplexNorm2 x) := by
            gcongr
        _ ≤ (p09StageScale (stage :: stages) *
              p09StageFirst (stage :: stages) γ * e + C * e ^ 2) *
              p09ComplexNorm2 x := by
            rw [show (B * e + Ct * e ^ 2) *
                  ((sh + sh * ah * e + Ch * e ^ 2) * p09ComplexNorm2 x) +
                  st * ((sh * ah * e + Ch * e ^ 2) * p09ComplexNorm2 x) =
                ((B * e + Ct * e ^ 2) *
                  (sh + sh * ah * e + Ch * e ^ 2) +
                  st * (sh * ah * e + Ch * e ^ 2)) * p09ComplexNorm2 x by ring]
            apply mul_le_mul_of_nonneg_right _ (by
              unfold p09ComplexNorm2
              positivity)
            have he3 : e ^ 3 ≤ e ^ 2 := by nlinarith [sq_nonneg e]
            have he4 : e ^ 4 ≤ e ^ 2 := by
              nlinarith [sq_nonneg (e ^ 2), sq_nonneg e]
            simp only [p09StageScale, p09StageFirst, List.map_cons, List.prod_cons,
              List.sum_cons]
            dsimp [C, B, st, tailA, sh, ah]
            have hhigh3a : B * Ch * e ^ 3 ≤ B * Ch * e ^ 2 :=
              mul_le_mul_of_nonneg_left he3 (mul_nonneg hB0 hCh0)
            have hhigh3b : Ct * sh * ah * e ^ 3 ≤ Ct * sh * ah * e ^ 2 :=
              mul_le_mul_of_nonneg_left he3
                (mul_nonneg (mul_nonneg hCt0 hsh0) hah0)
            have hhigh4 : Ct * Ch * e ^ 4 ≤ Ct * Ch * e ^ 2 :=
              mul_le_mul_of_nonneg_left he4 (mul_nonneg hCt0 hCh0)
            dsimp [B, st, tailA, sh, ah] at hhigh3a hhigh3b hhigh4
            simp only [p09StageScale, p09StageFirst] at hhigh3a hhigh3b hhigh4 ⊢
            ring_nf at hhigh3a hhigh3b hhigh4 ⊢
            linarith

private lemma p09_stageScale_eq_sqrt_prod {n : ℕ} [NeZero n]
    (stages : List (P09MixedRadixStage n)) :
    p09StageScale stages =
      Real.sqrt ((stages.map fun stage ↦ stage.radix).prod : ℝ) := by
  induction stages with
  | nil => simp [p09StageScale]
  | cons stage stages ih =>
      simp only [p09StageScale, List.map_cons, List.prod_cons]
      change Real.sqrt stage.radix * p09StageScale stages =
        Real.sqrt ((stage.radix : ℝ) *
          ((stages.map fun stage ↦ stage.radix).prod : ℝ))
      rw [ih, Real.sqrt_mul (by positivity)]

private lemma p09_sum_before_last (r : ℕ) (c : ℝ) :
    (∑ i : Fin r, if i.val + 1 < r then c else 0) = (r - 1 : ℕ) * c := by
  induction r with
  | zero => simp
  | succ r ih =>
      rw [Fin.sum_univ_succ]
      simp only [Fin.val_zero, Fin.val_succ]
      by_cases hr : r = 0
      · subst r
        simp
      · have hrpos : 0 < r := Nat.pos_of_ne_zero hr
        have hzero : 0 + 1 < r + 1 := by omega
        rw [if_pos hzero]
        have hcond : ∀ i : Fin r,
            (i.val + 1 + 1 < r + 1) = (i.val + 1 < r) := by
          intro i
          apply propext
          omega
        simp_rw [hcond, ih]
        simp only [Nat.add_sub_cancel]
        have hcast : (r : ℝ) = (r - 1 : ℕ) + 1 := by
          norm_cast
          omega
        rw [hcast]
        ring

private lemma p09_plan_stageScale {n : ℕ} [NeZero n]
    (plan : P09MixedRadixFftPlan n) :
    p09StageScale (List.ofFn plan.stage) = Real.sqrt n := by
  rw [p09_stageScale_eq_sqrt_prod]
  congr 1
  simp only [List.map_ofFn, List.prod_ofFn, Function.comp_apply]
  exact_mod_cast plan.order_factorization

private lemma p09_plan_stageFirst {n : ℕ} [NeZero n]
    (plan : P09MixedRadixFftPlan n) (γ : ℝ) :
    p09StageFirst (List.ofFn plan.stage) γ = p09K plan γ := by
  unfold p09StageFirst p09K
  rw [List.map_ofFn, List.sum_ofFn]
  simp only [Function.comp_apply]
  simp_rw [plan.twiddle_pattern]
  simp only [decide_eq_true_eq, Finset.sum_add_distrib]
  rw [p09_sum_before_last]
  rw [Nat.cast_sub (Nat.one_le_iff_ne_zero.mpr
    (Nat.ne_of_gt plan.stageCount_pos))]
  norm_num

private lemma p09_permute_diff_norm {n : ℕ} [NeZero n]
    (permutation : ZMod n ≃ ZMod n) (x y : ZMod n → ℂ) :
    p09ComplexNorm2
        (fun i ↦ p09Permute permutation x i - p09Permute permutation y i) =
      p09ComplexNorm2 (fun i ↦ x i - y i) := by
  rw [p09_complexNorm2_eq_l2, p09_complexNorm2_eq_l2]
  simpa [p09Permute] using
    p09_l2_equiv permutation (fun i ↦ x i - y i)

private lemma p09_fft_error {n : ℕ} [NeZero n]
    (plan : P09MixedRadixFftPlan n) (γ : ℝ) (hγ0 : 0 ≤ γ) :
    ∃ C : ℝ, 0 ≤ C ∧
      ∀ (model : P09WilkinsonModel) (e : ℝ), model.epsilon = e →
      model.gamma = γ → e ≤ 1 → ∀ x : ZMod n → ℂ,
      p09ComplexNorm2
          (fun i ↦ p09RoundedFftApply plan model x i - p09FourierTransform x i) ≤
        (Real.sqrt n * p09K plan γ * e + C * e ^ 2) * p09ComplexNorm2 x := by
  have hscale : ∀ stage ∈ List.ofFn plan.stage, ∀ x : ZMod n → ℂ,
      p09ComplexNorm2 (p09MixedRadixStageApply stage x) =
        Real.sqrt stage.radix * p09ComplexNorm2 x := by
    intro stage hstage x
    obtain ⟨i, hi⟩ := List.mem_ofFn.mp hstage
    rw [← hi]
    exact plan.stage_norm_scaling i x
  obtain ⟨C, hC0, hlist⟩ := p09_stageList_error (List.ofFn plan.stage)
    γ hγ0 hscale
  refine ⟨C, hC0, ?_⟩
  intro model e he hγ he1 x
  let rounded := p09RoundedStageList model (List.ofFn plan.stage) x
  let exact := p09ExactStageList (List.ofFn plan.stage) x
  have hnorm : p09ComplexNorm2
        (fun i ↦ p09RoundedFftApply plan model x i - p09FourierTransform x i) =
      p09ComplexNorm2 (fun i ↦ rounded i - exact i) := by
    rw [← plan.exact_factorization x]
    change p09ComplexNorm2
        (fun i ↦ p09Permute plan.finalPermutation rounded i -
          p09Permute plan.finalPermutation exact i) = _
    exact p09_permute_diff_norm plan.finalPermutation rounded exact
  rw [hnorm, ← p09_plan_stageScale plan, ← p09_plan_stageFirst plan γ]
  exact hlist model e he hγ he1 x

private def p09UpdateEquiv {m : ℕ} (axis : Fin m → P09FftAxis) (i : Fin m) :
    (P09MultiIndex axis × ZMod (axis i).order) ≃
      (P09MultiIndex axis × ZMod (axis i).order) where
  toFun p := (Function.update p.1 i p.2, p.1 i)
  invFun p := (Function.update p.1 i p.2, p.1 i)
  left_inv := by
    intro p
    apply Prod.ext
    · funext k
      by_cases hki : k = i
      · subst k
        simp
      · simp [hki]
    · simp
  right_inv := by
    intro p
    apply Prod.ext
    · funext k
      by_cases hki : k = i
      · subst k
        simp
      · simp [hki]
    · simp

private lemma p09_sum_update {m : ℕ} (axis : Fin m → P09FftAxis)
    (i : Fin m) (f : P09MultiIndex axis → ℝ) :
    (∑ index : P09MultiIndex axis, ∑ j : ZMod (axis i).order,
        f (Function.update index i j)) =
      (axis i).order * ∑ index : P09MultiIndex axis, f index := by
  letI (k : Fin m) : NeZero (axis k).order :=
    ⟨Nat.ne_of_gt (axis k).order_pos⟩
  have h := (p09UpdateEquiv axis i).sum_comp (fun p ↦ f p.1)
  rw [Fintype.sum_prod_type, Fintype.sum_prod_type] at h
  calc
    (∑ index : P09MultiIndex axis, ∑ j : ZMod (axis i).order,
        f (Function.update index i j)) =
        ∑ index : P09MultiIndex axis, (axis i).order * f index := by
      simpa [p09UpdateEquiv, Finset.sum_const, nsmul_eq_mul] using h
    _ = (axis i).order * ∑ index : P09MultiIndex axis, f index := by
      rw [Finset.mul_sum]

private lemma p09_multiNorm2_sq {m : ℕ} (axis : Fin m → P09FftAxis)
    (x : P09MultiArray axis) :
    p09MultiNorm2 x ^ 2 = ∑ index : P09MultiIndex axis, ‖x index‖ ^ 2 := by
  letI (k : Fin m) : NeZero (axis k).order :=
    ⟨Nat.ne_of_gt (axis k).order_pos⟩
  unfold p09MultiNorm2
  rw [EuclideanSpace.norm_sq_eq]

private lemma p09_complexNorm2_sq_sum {n : ℕ} [NeZero n]
    (x : ZMod n → ℂ) :
    p09ComplexNorm2 x ^ 2 = ∑ i : ZMod n, ‖x i‖ ^ 2 := by
  rw [p09_complexNorm2_eq_l2, EuclideanSpace.norm_sq_eq]

private lemma p09_coordinate_error {m : ℕ} (axis : Fin m → P09FftAxis)
    (i : Fin m) (γ : ℝ) (hγ0 : 0 ≤ γ) :
    ∃ C : ℝ, 0 ≤ C ∧
      ∀ (model : P09WilkinsonModel) (e : ℝ), model.epsilon = e →
      model.gamma = γ → e ≤ 1 → ∀ x : P09MultiArray axis,
      p09MultiNorm2
          (fun index ↦ p09RoundedCoordinateTransform axis i model x index -
            p09CoordinateTransform axis i x index) ≤
        (Real.sqrt (axis i).order * p09K (axis i).plan γ * e + C * e ^ 2) *
          p09MultiNorm2 x := by
  letI (k : Fin m) : NeZero (axis k).order :=
    ⟨Nat.ne_of_gt (axis k).order_pos⟩
  obtain ⟨C, hC0, hfft⟩ := p09_fft_error (axis i).plan γ hγ0
  refine ⟨C, hC0, ?_⟩
  intro model e he hγ he1 x
  let c : ℝ := Real.sqrt (axis i).order * p09K (axis i).plan γ * e + C * e ^ 2
  let error : P09MultiArray axis := fun index ↦
    p09RoundedCoordinateTransform axis i model x index -
      p09CoordinateTransform axis i x index
  have hK0 : 0 ≤ p09K (axis i).plan γ := by
    rw [← p09_plan_stageFirst]
    exact p09_stageFirst_nonneg _ _ hγ0
  have he0 : 0 ≤ e := by rw [← he]; exact le_of_lt model.epsilon_pos
  have hc0 : 0 ≤ c := by dsimp [c]; positivity
  have hfiber : ∀ base : P09MultiIndex axis,
      p09ComplexNorm2 (fun j ↦ error (Function.update base i j)) ≤
        c * p09ComplexNorm2 (fun j ↦ x (Function.update base i j)) := by
    intro base
    have h := hfft model e he hγ he1 (fun j ↦ x (Function.update base i j))
    simpa [error, c, p09RoundedCoordinateTransform, p09CoordinateTransform,
      p09FourierTransform] using h
  have hfiberSq : ∀ base : P09MultiIndex axis,
      (∑ j : ZMod (axis i).order,
          ‖error (Function.update base i j)‖ ^ 2) ≤
        c ^ 2 * ∑ j : ZMod (axis i).order,
          ‖x (Function.update base i j)‖ ^ 2 := by
    intro base
    have hsq := (sq_le_sq₀ (by
        unfold p09ComplexNorm2
        positivity) (mul_nonneg hc0 (by
        unfold p09ComplexNorm2
        positivity))).2 (hfiber base)
    rw [p09_complexNorm2_sq_sum, mul_pow, p09_complexNorm2_sq_sum] at hsq
    exact hsq
  have hsum : (∑ base : P09MultiIndex axis,
        ∑ j : ZMod (axis i).order,
          ‖error (Function.update base i j)‖ ^ 2) ≤
      ∑ base : P09MultiIndex axis, c ^ 2 *
        ∑ j : ZMod (axis i).order,
          ‖x (Function.update base i j)‖ ^ 2 := by
    exact Finset.sum_le_sum fun base hbase ↦ hfiberSq base
  have herrorSum := p09_sum_update axis i (fun index ↦ ‖error index‖ ^ 2)
  have hxSum := p09_sum_update axis i (fun index ↦ ‖x index‖ ^ 2)
  rw [herrorSum, ← Finset.mul_sum, hxSum] at hsum
  have hglobalSq : (∑ index : P09MultiIndex axis, ‖error index‖ ^ 2) ≤
      c ^ 2 * ∑ index : P09MultiIndex axis, ‖x index‖ ^ 2 := by
    have hn : (0 : ℝ) < (axis i).order := by
      exact_mod_cast (axis i).order_pos
    nlinarith
  change p09MultiNorm2 error ≤ c * p09MultiNorm2 x
  apply (sq_le_sq₀ (by
    unfold p09MultiNorm2
    positivity) (mul_nonneg hc0 (by
    unfold p09MultiNorm2
    positivity))).1
  rw [p09_multiNorm2_sq, mul_pow, p09_multiNorm2_sq]
  exact hglobalSq

private lemma p09_multiCardinality_pos {m : ℕ} (axis : Fin m → P09FftAxis) :
    0 < p09MultiCardinality axis := by
  unfold p09MultiCardinality
  exact Finset.prod_pos fun i hi ↦ (axis i).order_pos

private lemma p09_prefix_norm_scaling {m : ℕ} [NeZero m]
    (plan : P09MultidimensionalFftPlan m) (k : ℕ) (hk : k ≤ m)
    (x : P09MultiArray plan.axis) :
    p09MultiNorm2 (p09ApplyCoordinatePrefix plan.axis k x) =
      Real.sqrt (p09PrefixOrderProduct plan.axis k hk : ℝ) * p09MultiNorm2 x := by
  have h := plan.prefix_rms_scaling k hk x
  unfold p09MultiRms at h
  have hd : Real.sqrt (p09MultiCardinality plan.axis : ℝ) ≠ 0 := by
    apply ne_of_gt
    apply Real.sqrt_pos.2
    exact_mod_cast p09_multiCardinality_pos plan.axis
  field_simp [hd] at h
  exact h

private lemma p09_coordinate_sub {m : ℕ} (axis : Fin m → P09FftAxis)
    (i : Fin m) (x y : P09MultiArray axis) :
    p09CoordinateTransform axis i (fun index ↦ x index - y index) =
      (fun index ↦ p09CoordinateTransform axis i x index -
        p09CoordinateTransform axis i y index) := by
  funext index
  simp only [p09CoordinateTransform, mul_sub, Finset.sum_sub_distrib]

private lemma p09_coordinateNat_sub {m : ℕ} (axis : Fin m → P09FftAxis)
    (i : ℕ) (x y : P09MultiArray axis) :
    p09CoordinateTransformNat axis i (fun index ↦ x index - y index) =
      (fun index ↦ p09CoordinateTransformNat axis i x index -
        p09CoordinateTransformNat axis i y index) := by
  unfold p09CoordinateTransformNat
  split
  · exact p09_coordinate_sub axis _ x y
  · rfl

private lemma p09_prefix_sub {m : ℕ} (axis : Fin m → P09FftAxis)
    (k : ℕ) (x y : P09MultiArray axis) :
    p09ApplyCoordinatePrefix axis k (fun index ↦ x index - y index) =
      (fun index ↦ p09ApplyCoordinatePrefix axis k x index -
        p09ApplyCoordinatePrefix axis k y index) := by
  induction k generalizing x y with
  | zero => rfl
  | succ k ih =>
      simp only [p09ApplyCoordinatePrefix]
      rw [p09_coordinateNat_sub, ih]

private lemma p09_multiNorm2_triangle_sub {m : ℕ} (axis : Fin m → P09FftAxis)
    (x y z : P09MultiArray axis) :
    p09MultiNorm2 (fun index ↦ x index - z index) ≤
      p09MultiNorm2 (fun index ↦ x index - y index) +
        p09MultiNorm2 (fun index ↦ y index - z index) := by
  letI (k : Fin m) : NeZero (axis k).order :=
    ⟨Nat.ne_of_gt (axis k).order_pos⟩
  unfold p09MultiNorm2
  have heq : (WithLp.toLp 2 (fun index ↦ x index - z index) :
      EuclideanSpace ℂ (P09MultiIndex axis)) =
      WithLp.toLp 2 (fun index ↦ x index - y index) +
        WithLp.toLp 2 (fun index ↦ y index - z index) := by
    ext index
    simp
  rw [heq]
  exact norm_add_le _ _

private lemma p09_multiNorm2_le_add_error {m : ℕ} (axis : Fin m → P09FftAxis)
    (x y : P09MultiArray axis) :
    p09MultiNorm2 x ≤ p09MultiNorm2 y +
      p09MultiNorm2 (fun index ↦ x index - y index) := by
  letI (k : Fin m) : NeZero (axis k).order :=
    ⟨Nat.ne_of_gt (axis k).order_pos⟩
  unfold p09MultiNorm2
  have heq : (WithLp.toLp 2 x : EuclideanSpace ℂ (P09MultiIndex axis)) =
      WithLp.toLp 2 y + WithLp.toLp 2 (fun index ↦ x index - y index) := by
    ext index
    simp
  rw [heq]
  exact norm_add_le _ _

private lemma p09_fourier_norm_scaling {n : ℕ} [NeZero n]
    (plan : P09MixedRadixFftPlan n) (x : ZMod n → ℂ) :
    p09ComplexNorm2 (p09FourierTransform x) =
      Real.sqrt n * p09ComplexNorm2 x := by
  have h := plan.fourier_rms_scaling x
  unfold p09ComplexRms at h
  have hs0 : 0 ≤ Real.sqrt (n : ℝ) := Real.sqrt_nonneg _
  have hn : (0 : ℝ) < n := by exact_mod_cast NeZero.pos n
  have hs2 : Real.sqrt (n : ℝ) ^ 2 = n := Real.sq_sqrt (le_of_lt hn)
  have hs : Real.sqrt (n : ℝ) ≠ 0 := ne_of_gt (Real.sqrt_pos.2 hn)
  field_simp [hs] at h
  nlinarith

private lemma p09_coordinate_norm_scaling {m : ℕ}
    (axis : Fin m → P09FftAxis) (i : Fin m) (x : P09MultiArray axis) :
    p09MultiNorm2 (p09CoordinateTransform axis i x) =
      Real.sqrt (axis i).order * p09MultiNorm2 x := by
  letI (k : Fin m) : NeZero (axis k).order :=
    ⟨Nat.ne_of_gt (axis k).order_pos⟩
  let tx := p09CoordinateTransform axis i x
  have hfiber : ∀ base : P09MultiIndex axis,
      p09ComplexNorm2 (fun j ↦ tx (Function.update base i j)) =
        Real.sqrt (axis i).order *
          p09ComplexNorm2 (fun j ↦ x (Function.update base i j)) := by
    intro base
    have h := p09_fourier_norm_scaling (axis i).plan
      (fun j ↦ x (Function.update base i j))
    simpa [tx, p09CoordinateTransform, p09FourierTransform] using h
  have hfiberSq : ∀ base : P09MultiIndex axis,
      (∑ j : ZMod (axis i).order,
          ‖tx (Function.update base i j)‖ ^ 2) =
        (axis i).order * ∑ j : ZMod (axis i).order,
          ‖x (Function.update base i j)‖ ^ 2 := by
    intro base
    have h := congrArg (fun z : ℝ ↦ z ^ 2) (hfiber base)
    change (p09ComplexNorm2 (fun j ↦ tx (Function.update base i j))) ^ 2 =
      (Real.sqrt (axis i).order *
        p09ComplexNorm2 (fun j ↦ x (Function.update base i j))) ^ 2 at h
    rw [p09_complexNorm2_sq_sum, mul_pow, p09_complexNorm2_sq_sum,
      Real.sq_sqrt (by positivity)] at h
    exact h
  have hsum : (∑ base : P09MultiIndex axis,
        ∑ j : ZMod (axis i).order, ‖tx (Function.update base i j)‖ ^ 2) =
      ∑ base : P09MultiIndex axis, (axis i).order *
        ∑ j : ZMod (axis i).order, ‖x (Function.update base i j)‖ ^ 2 := by
    apply Finset.sum_congr rfl
    intro base hbase
    exact hfiberSq base
  have htxSum := p09_sum_update axis i (fun index ↦ ‖tx index‖ ^ 2)
  have hxSum := p09_sum_update axis i (fun index ↦ ‖x index‖ ^ 2)
  rw [htxSum, ← Finset.mul_sum, hxSum] at hsum
  have hn : (0 : ℝ) < (axis i).order := by
    exact_mod_cast (axis i).order_pos
  have hglobal : (∑ index : P09MultiIndex axis, ‖tx index‖ ^ 2) =
      (axis i).order * ∑ index : P09MultiIndex axis, ‖x index‖ ^ 2 := by
    nlinarith
  apply (sq_eq_sq₀ (by
    unfold p09MultiNorm2
    positivity) (mul_nonneg (Real.sqrt_nonneg _) (by
    unfold p09MultiNorm2
    positivity))).mp
  rw [p09_multiNorm2_sq, mul_pow, p09_multiNorm2_sq,
    Real.sq_sqrt (by positivity)]
  exact hglobal

private lemma p09_prefixProduct_succ {m : ℕ} (axis : Fin m → P09FftAxis)
    (k : ℕ) (hk : k + 1 ≤ m) :
    p09PrefixOrderProduct axis (k + 1) hk =
      p09PrefixOrderProduct axis k (Nat.le_trans (Nat.le_succ k) hk) *
        (axis ⟨k, Nat.lt_of_lt_of_le (Nat.lt_succ_self k) hk⟩).order := by
  unfold p09PrefixOrderProduct
  rw [Fin.prod_univ_castSucc]
  congr 1

private lemma p09_prefixSum_succ {m : ℕ} (axis : Fin m → P09FftAxis)
    (γ : ℝ) (k : ℕ) (hk : k + 1 ≤ m) :
    (∑ j : Fin (k + 1),
        p09AxisK (axis (Fin.castLE hk j)) γ) =
      (∑ j : Fin k,
        p09AxisK (axis (Fin.castLE (Nat.le_trans (Nat.le_succ k) hk) j)) γ) +
        p09AxisK (axis ⟨k, Nat.lt_of_lt_of_le (Nat.lt_succ_self k) hk⟩) γ := by
  rw [Fin.sum_univ_castSucc]
  congr 1

private lemma p09_axisK_nonneg (axis : P09FftAxis) (γ : ℝ) (hγ0 : 0 ≤ γ) :
    0 ≤ p09AxisK axis γ := by
  unfold p09AxisK
  rw [← p09_plan_stageFirst]
  exact p09_stageFirst_nonneg _ _ hγ0

private lemma p09_prefixSum_nonneg {m : ℕ} (axis : Fin m → P09FftAxis)
    (γ : ℝ) (hγ0 : 0 ≤ γ) (k : ℕ) (hk : k ≤ m) :
    0 ≤ ∑ j : Fin k, p09AxisK (axis (Fin.castLE hk j)) γ := by
  exact Finset.sum_nonneg fun j hj ↦ p09_axisK_nonneg _ _ hγ0

private lemma p09_prefixProduct_pos {m : ℕ} (axis : Fin m → P09FftAxis)
    (k : ℕ) (hk : k ≤ m) :
    0 < p09PrefixOrderProduct axis k hk := by
  unfold p09PrefixOrderProduct
  exact Finset.prod_pos fun j hj ↦ (axis (Fin.castLE hk j)).order_pos

private def p09RunStateAt {m : ℕ} [NeZero m]
    {plan : P09MultidimensionalFftPlan m} {model : P09WilkinsonModel}
    (run : P09MultidimensionalFftRun plan model) (k : ℕ) (hk : k ≤ m) :
    P09MultiArray plan.axis :=
  run.computedState ⟨k, Nat.lt_succ_of_le hk⟩

private lemma p09_run_prefix_error {m : ℕ} [NeZero m]
    (plan : P09MultidimensionalFftPlan m) (γ : ℝ) (hγ0 : 0 ≤ γ) :
    ∀ (k : ℕ) (hk : k ≤ m),
    ∃ C : ℝ, 0 ≤ C ∧
      ∀ (model : P09WilkinsonModel) (e : ℝ), model.epsilon = e →
      model.gamma = γ → e ≤ 1 →
      ∀ run : P09MultidimensionalFftRun plan model,
      p09MultiNorm2
          (fun index ↦ p09RunStateAt run 0 (Nat.zero_le m) index -
            p09ApplyCoordinatePrefix plan.axis k (p09RunStateAt run k hk) index) ≤
        (Real.sqrt (p09PrefixOrderProduct plan.axis k hk : ℝ) *
            (∑ j : Fin k, p09AxisK (plan.axis (Fin.castLE hk j)) γ) * e +
          C * e ^ 2) * p09MultiNorm2 (p09RunStateAt run k hk) := by
  intro k
  induction k with
  | zero =>
      intro hk
      refine ⟨0, le_rfl, ?_⟩
      intro model e he hγ he1 run
      simp [p09RunStateAt, p09ApplyCoordinatePrefix, p09PrefixOrderProduct,
        p09MultiNorm2]
      rfl
  | succ k ih =>
      intro hk
      let hk0 : k ≤ m := Nat.le_trans (Nat.le_succ k) hk
      let ik : Fin m := ⟨k, Nat.lt_of_lt_of_le (Nat.lt_succ_self k) hk⟩
      obtain ⟨Ct, hCt0, htail⟩ := ih hk0
      obtain ⟨Ch, hCh0, hlocal⟩ := p09_coordinate_error plan.axis ik γ hγ0
      let sp : ℝ := Real.sqrt (p09PrefixOrderProduct plan.axis k hk0 : ℝ)
      let sn : ℝ := Real.sqrt (plan.axis ik).order
      let A : ℝ := ∑ j : Fin k, p09AxisK (plan.axis (Fin.castLE hk0 j)) γ
      let K : ℝ := p09AxisK (plan.axis ik) γ
      let B : ℝ := sp * A
      let C : ℝ := B * sn * K + Ct * sn + sp * Ch + B * Ch +
        Ct * sn * K + Ct * Ch
      have hsp0 : 0 ≤ sp := Real.sqrt_nonneg _
      have hsn0 : 0 ≤ sn := Real.sqrt_nonneg _
      have hA0 : 0 ≤ A := p09_prefixSum_nonneg plan.axis γ hγ0 k hk0
      have hK0 : 0 ≤ K := p09_axisK_nonneg _ _ hγ0
      have hB0 : 0 ≤ B := mul_nonneg hsp0 hA0
      have hC0 : 0 ≤ C := by dsimp [C]; positivity
      refine ⟨C, hC0, ?_⟩
      intro model e he hγ he1 run
      have he0 : 0 ≤ e := by rw [← he]; exact le_of_lt model.epsilon_pos
      let s0 := p09RunStateAt run 0 (Nat.zero_le m)
      let sk := p09RunStateAt run k hk0
      let sk1 := p09RunStateAt run (k + 1) hk
      let ek := p09CoordinateTransform plan.axis ik sk1
      have hstep : sk = p09RoundedCoordinateTransform plan.axis ik model sk1 := by
        dsimp [sk, sk1, ik, p09RunStateAt]
        simpa using run.stage_step ik
      have hlocal' : p09MultiNorm2 (fun index ↦ sk index - ek index) ≤
          (sn * K * e + Ch * e ^ 2) * p09MultiNorm2 sk1 := by
        rw [hstep]
        simpa [ek, sn, K, mul_assoc] using
          hlocal model e he hγ he1 sk1
      have hsk : p09MultiNorm2 sk ≤
          (sn + sn * K * e + Ch * e ^ 2) * p09MultiNorm2 sk1 := by
        calc
          p09MultiNorm2 sk ≤ p09MultiNorm2 ek +
              p09MultiNorm2 (fun index ↦ sk index - ek index) :=
            p09_multiNorm2_le_add_error plan.axis sk ek
          _ ≤ sn * p09MultiNorm2 sk1 +
              (sn * K * e + Ch * e ^ 2) * p09MultiNorm2 sk1 := by
            rw [show p09MultiNorm2 ek = sn * p09MultiNorm2 sk1 by
              simpa [ek, sn, ik] using
                p09_coordinate_norm_scaling plan.axis ik sk1]
            gcongr
          _ = (sn + sn * K * e + Ch * e ^ 2) * p09MultiNorm2 sk1 := by ring
      have htail' : p09MultiNorm2
          (fun index ↦ s0 index -
            p09ApplyCoordinatePrefix plan.axis k sk index) ≤
          (B * e + Ct * e ^ 2) * p09MultiNorm2 sk := by
        simpa [s0, sk, B, hk0] using htail model e he hγ he1 run
      let oldExact := p09ApplyCoordinatePrefix plan.axis k sk
      let newExact := p09ApplyCoordinatePrefix plan.axis k ek
      have hprefixDiff : p09MultiNorm2
          (fun index ↦ oldExact index - newExact index) =
          sp * p09MultiNorm2 (fun index ↦ sk index - ek index) := by
        rw [← p09_prefix_sub plan.axis k sk ek]
        exact p09_prefix_norm_scaling plan k hk0 _
      have hprefixSucc :
          p09ApplyCoordinatePrefix plan.axis (k + 1) sk1 = newExact := by
        simp only [p09ApplyCoordinatePrefix]
        unfold p09CoordinateTransformNat
        rw [dif_pos (show k < m from ik.isLt)]
      have htri := p09_multiNorm2_triangle_sub plan.axis s0 oldExact newExact
      rw [hprefixSucc]
      change p09MultiNorm2 (fun index ↦ s0 index - newExact index) ≤ _
      calc
        p09MultiNorm2 (fun index ↦ s0 index - newExact index) ≤
            p09MultiNorm2 (fun index ↦ s0 index - oldExact index) +
              p09MultiNorm2 (fun index ↦ oldExact index - newExact index) := htri
        _ ≤ (B * e + Ct * e ^ 2) * p09MultiNorm2 sk +
              sp * ((sn * K * e + Ch * e ^ 2) * p09MultiNorm2 sk1) := by
            rw [hprefixDiff]
            exact add_le_add htail' (mul_le_mul_of_nonneg_left hlocal' hsp0)
        _ ≤ (B * e + Ct * e ^ 2) *
              ((sn + sn * K * e + Ch * e ^ 2) * p09MultiNorm2 sk1) +
              sp * ((sn * K * e + Ch * e ^ 2) * p09MultiNorm2 sk1) := by
            gcongr
        _ ≤ (Real.sqrt (p09PrefixOrderProduct plan.axis (k + 1) hk : ℝ) *
              (∑ j : Fin (k + 1),
                p09AxisK (plan.axis (Fin.castLE hk j)) γ) * e + C * e ^ 2) *
              p09MultiNorm2 sk1 := by
            rw [show (B * e + Ct * e ^ 2) *
                  ((sn + sn * K * e + Ch * e ^ 2) * p09MultiNorm2 sk1) +
                  sp * ((sn * K * e + Ch * e ^ 2) * p09MultiNorm2 sk1) =
                ((B * e + Ct * e ^ 2) *
                  (sn + sn * K * e + Ch * e ^ 2) +
                  sp * (sn * K * e + Ch * e ^ 2)) * p09MultiNorm2 sk1 by ring]
            apply mul_le_mul_of_nonneg_right _ (by
              unfold p09MultiNorm2
              positivity)
            have hprod := p09_prefixProduct_succ plan.axis k hk
            have hprod0 : (0 : ℝ) ≤ p09PrefixOrderProduct plan.axis k hk0 := by
              exact_mod_cast Nat.zero_le _
            have hsprod : Real.sqrt (p09PrefixOrderProduct plan.axis (k + 1) hk : ℝ) =
                sp * sn := by
              rw [hprod, Nat.cast_mul, Real.sqrt_mul hprod0]
            have hsum := p09_prefixSum_succ plan.axis γ k hk
            rw [hsprod, hsum]
            have he3 : e ^ 3 ≤ e ^ 2 := by nlinarith [sq_nonneg e]
            have he4 : e ^ 4 ≤ e ^ 2 := by
              nlinarith [sq_nonneg (e ^ 2), sq_nonneg e]
            dsimp [C, B]
            have hhigh3a : B * Ch * e ^ 3 ≤ B * Ch * e ^ 2 :=
              mul_le_mul_of_nonneg_left he3 (mul_nonneg hB0 hCh0)
            have hhigh3b : Ct * sn * K * e ^ 3 ≤ Ct * sn * K * e ^ 2 :=
              mul_le_mul_of_nonneg_left he3
                (mul_nonneg (mul_nonneg hCt0 hsn0) hK0)
            have hhigh4 : Ct * Ch * e ^ 4 ≤ Ct * Ch * e ^ 2 :=
              mul_le_mul_of_nonneg_left he4 (mul_nonneg hCt0 hCh0)
            dsimp [B, sp, sn, A, K] at hhigh3a hhigh3b hhigh4 ⊢
            ring_nf at hhigh3a hhigh3b hhigh4 ⊢
            linarith

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
  obtain ⟨C, hC0, hbound⟩ :=
    p09_run_prefix_error plan γ family.gamma_nonneg m (Nat.le_refl m)
  let P : ℕ := p09PrefixOrderProduct plan.axis m (Nat.le_refl m)
  let sp : ℝ := Real.sqrt P
  let S : ℝ := ∑ i : Fin m, p09AxisK (plan.axis i) γ
  have hPpos : 0 < P := p09_prefixProduct_pos plan.axis m (Nat.le_refl m)
  have hsp : 0 < sp := by
    dsimp [sp]
    apply Real.sqrt_pos.2
    exact_mod_cast hPpos
  let secondOrderCoeff : ℝ := C / sp
  refine ⟨secondOrderCoeff, div_nonneg hC0 (le_of_lt hsp), 1, by norm_num, ?_⟩
  intro ε hε
  let model := family.model ε
  let run := family.run ε
  have hstateM : p09RunStateAt run m (Nat.le_refl m) = family.input := by
    exact (show run.computedState (Fin.last m) = family.input from
      run.computed_input.trans (family.run_input ε))
  have hstate0 : p09RunStateAt run 0 (Nat.zero_le m) =
      p09MultiComputedOutput run := rfl
  have herr : (fun index ↦ p09RunStateAt run 0 (Nat.zero_le m) index -
        p09ApplyCoordinatePrefix plan.axis m
          (p09RunStateAt run m (Nat.le_refl m)) index) =
      p09FamilyMultiFftRoundoffError family ε := by
    rw [hstate0, hstateM]
    rfl
  have hb := hbound model ε.1 (family.model_epsilon ε)
    (family.model_gamma ε) hε run
  rw [herr, hstateM] at hb
  change p09MultiNorm2 (p09FamilyMultiFftRoundoffError family ε) ≤
      (sp * S * ε.1 + C * ε.1 ^ 2) * p09MultiNorm2 family.input at hb
  have hd : 0 < Real.sqrt (p09MultiCardinality plan.axis : ℝ) := by
    apply Real.sqrt_pos.2
    exact_mod_cast p09_multiCardinality_pos plan.axis
  have hbRms : p09MultiRms (p09FamilyMultiFftRoundoffError family ε) ≤
      (sp * S * ε.1 + C * ε.1 ^ 2) * p09MultiRms family.input := by
    unfold p09MultiRms
    calc
      p09MultiNorm2 (p09FamilyMultiFftRoundoffError family ε) /
          Real.sqrt (p09MultiCardinality plan.axis : ℝ) ≤
        ((sp * S * ε.1 + C * ε.1 ^ 2) * p09MultiNorm2 family.input) /
          Real.sqrt (p09MultiCardinality plan.axis : ℝ) :=
        div_le_div_of_nonneg_right hb (le_of_lt hd)
      _ = (sp * S * ε.1 + C * ε.1 ^ 2) *
          (p09MultiNorm2 family.input /
            Real.sqrt (p09MultiCardinality plan.axis : ℝ)) := by ring
  have hexactScale : p09MultiRms (p09FamilyMultiExactOutput family) =
      sp * p09MultiRms family.input := by
    simpa [p09FamilyMultiExactOutput, P, sp] using
      plan.prefix_rms_scaling m (Nat.le_refl m) family.input
  apply (div_le_iff₀ hexactOutput).2
  calc
    p09MultiRms (p09FamilyMultiFftRoundoffError family ε) ≤
        (sp * S * ε.1 + C * ε.1 ^ 2) * p09MultiRms family.input := hbRms
    _ = (ε.1 * S + secondOrderCoeff * ε.1 ^ 2) *
        p09MultiRms (p09FamilyMultiExactOutput family) := by
      rw [hexactScale]
      dsimp [secondOrderCoeff]
      field_simp [ne_of_gt hsp]

end HighamBench
