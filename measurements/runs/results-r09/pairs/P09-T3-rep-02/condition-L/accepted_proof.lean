import HighamBench.P09Definitions

namespace HighamBench

open scoped BigOperators

set_option maxHeartbeats 2000000

noncomputable def p09ExactWilkinsonModel
    (ε : P09PositiveEpsilon) (γ : ℝ) (hγ : 0 ≤ γ) :
    P09WilkinsonModel where
  epsilon := ε.1
  epsilon_pos := ε.2
  gamma := γ
  gamma_nonneg := hγ
  flAdd := (· + ·)
  flMul := (· * ·)
  flSin := Real.sin
  flCos := Real.cos
  flInput := id
  add_model := by
    intro a b
    exact ⟨0, 0, by simp, by simp, by ring⟩
  mul_model := by
    intro a b
    exact ⟨0, by simp, by ring⟩
  sin_model := by
    intro a
    exact ⟨0, by simp⟩
  cos_model := by
    intro a
    exact ⟨0, by simp⟩

lemma p09ExactWilkinsonModel_root {q : ℕ} [NeZero q]
    (ε : P09PositiveEpsilon) (γ : ℝ) (hγ : 0 ≤ γ) (j : ZMod q) :
    p09RoundedRoot (p09ExactWilkinsonModel ε γ hγ) j =
      ZMod.stdAddChar j := by
  rw [p09StdAddChar_positive_exp]
  let a : ℝ := 2 * Real.pi * (j.val : ℝ) / (q : ℝ)
  have hq : (q : ℂ) ≠ 0 := by
    exact_mod_cast (NeZero.ne q)
  have harg :
      (a : ℂ) * Complex.I =
        2 * (Real.pi : ℂ) * Complex.I * (j.val : ℂ) / (q : ℂ) := by
    simp only [a]
    push_cast
    field_simp [hq]
  calc
    p09RoundedRoot (p09ExactWilkinsonModel ε γ hγ) j =
        (Real.cos a : ℂ) + (Real.sin a : ℂ) * Complex.I := by
          apply Complex.ext
          · dsimp [p09RoundedRoot, p09ExactWilkinsonModel, p09RootAngle, a]
            ring
          · dsimp [p09RoundedRoot, p09ExactWilkinsonModel, p09RootAngle, a]
            ring
    _ = Complex.exp ((a : ℂ) * Complex.I) :=
      (Complex.exp_ofReal_mul_I a).symm
    _ = Complex.exp
        (2 * (Real.pi : ℂ) * Complex.I * (j.val : ℂ) / (q : ℂ)) := by
      rw [harg]

lemma p09_flAdd_error_le (model : P09WilkinsonModel) (a b : ℝ) :
    |model.flAdd a b - (a + b)| ≤
      model.epsilon * (|a| + |b|) := by
  obtain ⟨θa, θb, hθa, hθb, hfl⟩ := model.add_model a b
  rw [hfl]
  have hε : 0 ≤ model.epsilon := le_of_lt model.epsilon_pos
  calc
    |a * (1 + θa * model.epsilon) +
          b * (1 + θb * model.epsilon) - (a + b)| =
        model.epsilon * |a * θa + b * θb| := by
          rw [show a * (1 + θa * model.epsilon) +
              b * (1 + θb * model.epsilon) - (a + b) =
              model.epsilon * (a * θa + b * θb) by ring,
            abs_mul, abs_of_nonneg hε]
    _ ≤ model.epsilon * (|a * θa| + |b * θb|) := by
      exact mul_le_mul_of_nonneg_left (abs_add_le _ _) hε
    _ ≤ model.epsilon * (|a| + |b|) := by
      apply mul_le_mul_of_nonneg_left _ hε
      calc
        |a * θa| + |b * θb| =
            |a| * |θa| + |b| * |θb| := by rw [abs_mul, abs_mul]
        _ ≤ |a| * 1 + |b| * 1 := add_le_add
          (mul_le_mul_of_nonneg_left hθa (abs_nonneg a))
          (mul_le_mul_of_nonneg_left hθb (abs_nonneg b))
        _ = |a| + |b| := by ring

lemma p09_flMul_error_le (model : P09WilkinsonModel) (a b : ℝ) :
    |model.flMul a b - a * b| ≤
      model.epsilon * |a| * |b| := by
  obtain ⟨θ, hθ, hfl⟩ := model.mul_model a b
  rw [hfl]
  have hε : 0 ≤ model.epsilon := le_of_lt model.epsilon_pos
  calc
    |a * b * (1 + θ * model.epsilon) - a * b| =
        model.epsilon * |a| * |b| * |θ| := by
          rw [show a * b * (1 + θ * model.epsilon) - a * b =
              model.epsilon * a * b * θ by ring,
            abs_mul, abs_mul, abs_mul, abs_of_nonneg hε]
    _ ≤ model.epsilon * |a| * |b| := by
      nlinarith [mul_le_mul_of_nonneg_left hθ
        (mul_nonneg (mul_nonneg hε (abs_nonneg a)) (abs_nonneg b))]

lemma p09_flSin_error_le (model : P09WilkinsonModel) (a : ℝ) :
    |model.flSin a - Real.sin a| ≤ model.gamma * model.epsilon := by
  obtain ⟨θ, hθ, hfl⟩ := model.sin_model a
  rw [hfl]
  have hγ : 0 ≤ model.gamma := model.gamma_nonneg
  have hε : 0 ≤ model.epsilon := le_of_lt model.epsilon_pos
  rw [show Real.sin a + model.gamma * θ * model.epsilon - Real.sin a =
    model.gamma * model.epsilon * θ by ring, abs_mul,
    abs_of_nonneg (mul_nonneg hγ hε)]
  nlinarith [mul_le_mul_of_nonneg_left hθ (mul_nonneg hγ hε)]

lemma p09_flCos_error_le (model : P09WilkinsonModel) (a : ℝ) :
    |model.flCos a - Real.cos a| ≤ model.gamma * model.epsilon := by
  obtain ⟨θ, hθ, hfl⟩ := model.cos_model a
  rw [hfl]
  have hγ : 0 ≤ model.gamma := model.gamma_nonneg
  have hε : 0 ≤ model.epsilon := le_of_lt model.epsilon_pos
  rw [show Real.cos a + model.gamma * θ * model.epsilon - Real.cos a =
    model.gamma * model.epsilon * θ by ring, abs_mul,
    abs_of_nonneg (mul_nonneg hγ hε)]
  nlinarith [mul_le_mul_of_nonneg_left hθ (mul_nonneg hγ hε)]

def p09AbsComponents (z : ℂ) : ℂ := ⟨|z.re|, |z.im|⟩

lemma p09AbsComponents_norm (z : ℂ) :
    ‖p09AbsComponents z‖ = ‖z‖ := by
  rw [Complex.norm_eq_sqrt_sq_add_sq, Complex.norm_eq_sqrt_sq_add_sq]
  simp [p09AbsComponents, sq_abs]

lemma p09_complex_norm_le_of_components {z w : ℂ}
    (hre : |z.re| ≤ |w.re|) (him : |z.im| ≤ |w.im|) :
    ‖z‖ ≤ ‖w‖ := by
  rw [← sq_le_sq₀ (norm_nonneg z) (norm_nonneg w),
    Complex.sq_norm, Complex.sq_norm, Complex.normSq_apply,
    Complex.normSq_apply]
  nlinarith [sq_le_sq.mpr hre, sq_le_sq.mpr him]

lemma p09RoundedComplexAdd_error_le (model : P09WilkinsonModel)
    (x y : ℂ) :
    ‖p09RoundedComplexAdd model x y - (x + y)‖ ≤
      model.epsilon * (‖x‖ + ‖y‖) := by
  let w : ℂ := (model.epsilon : ℂ) *
    (p09AbsComponents x + p09AbsComponents y)
  have hwre : 0 ≤ w.re := by
    dsimp [w, p09AbsComponents]
    simp only [zero_mul, sub_zero]
    exact mul_nonneg (le_of_lt model.epsilon_pos)
      (add_nonneg (abs_nonneg _) (abs_nonneg _))
  have hwim : 0 ≤ w.im := by
    dsimp [w, p09AbsComponents]
    simp only [zero_mul, add_zero]
    exact mul_nonneg (le_of_lt model.epsilon_pos)
      (add_nonneg (abs_nonneg _) (abs_nonneg _))
  have hre :
      |(p09RoundedComplexAdd model x y - (x + y)).re| ≤ |w.re| := by
    rw [abs_of_nonneg hwre]
    simpa [p09RoundedComplexAdd, w, p09AbsComponents] using
      p09_flAdd_error_le model x.re y.re
  have him :
      |(p09RoundedComplexAdd model x y - (x + y)).im| ≤ |w.im| := by
    rw [abs_of_nonneg hwim]
    simpa [p09RoundedComplexAdd, w, p09AbsComponents] using
      p09_flAdd_error_le model x.im y.im
  calc
    ‖p09RoundedComplexAdd model x y - (x + y)‖ ≤ ‖w‖ :=
      p09_complex_norm_le_of_components hre him
    _ = model.epsilon *
        ‖p09AbsComponents x + p09AbsComponents y‖ := by
      dsimp only [w]
      rw [norm_mul]
      simp [Real.norm_eq_abs, abs_of_nonneg (le_of_lt model.epsilon_pos)]
    _ ≤ model.epsilon *
        (‖p09AbsComponents x‖ + ‖p09AbsComponents y‖) := by
      exact mul_le_mul_of_nonneg_left (norm_add_le _ _)
        (le_of_lt model.epsilon_pos)
    _ = model.epsilon * (‖x‖ + ‖y‖) := by
      rw [p09AbsComponents_norm, p09AbsComponents_norm]

lemma p09_cauchy_two {a b c d : ℝ}
    (ha : 0 ≤ a) (hb : 0 ≤ b) (hc : 0 ≤ c) (hd : 0 ≤ d) :
    a * c + b * d ≤ Real.sqrt (a ^ 2 + b ^ 2) *
      Real.sqrt (c ^ 2 + d ^ 2) := by
  have hab : 0 ≤ a ^ 2 + b ^ 2 := add_nonneg (sq_nonneg _) (sq_nonneg _)
  have hcd : 0 ≤ c ^ 2 + d ^ 2 := add_nonneg (sq_nonneg _) (sq_nonneg _)
  have hl : 0 ≤ a * c + b * d :=
    add_nonneg (mul_nonneg ha hc) (mul_nonneg hb hd)
  have hr : 0 ≤ Real.sqrt (a ^ 2 + b ^ 2) *
      Real.sqrt (c ^ 2 + d ^ 2) := mul_nonneg (Real.sqrt_nonneg _)
        (Real.sqrt_nonneg _)
  rw [← sq_le_sq₀ hl hr, mul_pow, Real.sq_sqrt hab, Real.sq_sqrt hcd]
  nlinarith [sq_nonneg (a * d - b * c)]

lemma p09_complex_abs_dot_le_norm_mul (x y : ℂ) :
    |x.re| * |y.re| + |x.im| * |y.im| ≤ ‖x‖ * ‖y‖ := by
  rw [Complex.norm_eq_sqrt_sq_add_sq, Complex.norm_eq_sqrt_sq_add_sq]
  simpa only [sq_abs] using
    p09_cauchy_two (a := |x.re|) (b := |x.im|)
      (c := |y.re|) (d := |y.im|) (abs_nonneg _) (abs_nonneg _)
      (abs_nonneg _) (abs_nonneg _)

lemma p09_complex_abs_cross_le_norm_mul (x y : ℂ) :
    |x.re| * |y.im| + |x.im| * |y.re| ≤ ‖x‖ * ‖y‖ := by
  rw [Complex.norm_eq_sqrt_sq_add_sq, Complex.norm_eq_sqrt_sq_add_sq]
  simpa only [sq_abs, add_comm] using p09_cauchy_two (a := |x.re|) (b := |x.im|)
    (c := |y.im|) (d := |y.re|) (abs_nonneg _) (abs_nonneg _)
    (abs_nonneg _) (abs_nonneg _)

lemma p09_complex_norm_le_sqrt_two_mul {z : ℂ} {v : ℝ}
    (hv : 0 ≤ v) (hre : |z.re| ≤ v) (him : |z.im| ≤ v) :
    ‖z‖ ≤ Real.sqrt 2 * v := by
  let w : ℂ := ⟨v, v⟩
  have hzw : ‖z‖ ≤ ‖w‖ := by
    apply p09_complex_norm_le_of_components
    · simpa [w, abs_of_nonneg hv] using hre
    · simpa [w, abs_of_nonneg hv] using him
  calc
    ‖z‖ ≤ ‖w‖ := hzw
    _ = Real.sqrt (v ^ 2 + v ^ 2) := by
      rw [Complex.norm_eq_sqrt_sq_add_sq]
    _ = Real.sqrt 2 * v := by
      rw [show v ^ 2 + v ^ 2 = 2 * v ^ 2 by ring,
        Real.sqrt_mul (by norm_num : (0 : ℝ) ≤ 2), Real.sqrt_sq hv]

lemma p09_sqrt_two_le_three_halves : Real.sqrt 2 ≤ (3 : ℝ) / 2 := by
  nlinarith [Real.sq_sqrt (by norm_num : (0 : ℝ) ≤ 2), Real.sqrt_nonneg 2]

lemma p09_sqrt_two_le_two : Real.sqrt 2 ≤ (2 : ℝ) := by
  linarith [p09_sqrt_two_le_three_halves]

lemma p09_flMul_abs_le (model : P09WilkinsonModel) (a b : ℝ) :
    |model.flMul a b| ≤
      (1 + model.epsilon) * |a| * |b| := by
  calc
    |model.flMul a b| ≤ |model.flMul a b - a * b| + |a * b| := by
      have := abs_add_le (model.flMul a b - a * b) (a * b)
      simpa only [sub_add_cancel] using this
    _ ≤ model.epsilon * |a| * |b| + |a * b| :=
      add_le_add (p09_flMul_error_le model a b) le_rfl
    _ = (1 + model.epsilon) * |a| * |b| := by
      rw [abs_mul]
      ring

lemma p09RoundedComplexMul_error_le (model : P09WilkinsonModel)
    (r x : ℂ) :
    ‖p09RoundedComplexMul model r x - r * x‖ ≤
      (3 * model.epsilon + 2 * model.epsilon ^ 2) * ‖r‖ * ‖x‖ := by
  let p₁ := model.flMul r.re x.re
  let p₂ := model.flMul r.im x.im
  let p₃ := model.flMul r.re x.im
  let p₄ := model.flMul r.im x.re
  let u : ℂ := ⟨p₁, p₃⟩
  let v : ℂ := ⟨-p₂, p₄⟩
  let addError : ℂ := p09RoundedComplexMul model r x - (u + v)
  let mulError : ℂ := (u + v) - r * x
  have hε : 0 ≤ model.epsilon := le_of_lt model.epsilon_pos
  have hOne : 0 ≤ 1 + model.epsilon := by linarith
  have hR : 0 ≤ ‖r‖ * ‖x‖ := mul_nonneg (norm_nonneg _) (norm_nonneg _)
  have hp₁ : |p₁| ≤ (1 + model.epsilon) * |r.re| * |x.re| :=
    p09_flMul_abs_le model _ _
  have hp₂ : |p₂| ≤ (1 + model.epsilon) * |r.im| * |x.im| :=
    p09_flMul_abs_le model _ _
  have hp₃ : |p₃| ≤ (1 + model.epsilon) * |r.re| * |x.im| :=
    p09_flMul_abs_le model _ _
  have hp₄ : |p₄| ≤ (1 + model.epsilon) * |r.im| * |x.re| :=
    p09_flMul_abs_le model _ _
  have haddRe : |addError.re| ≤
      model.epsilon * (1 + model.epsilon) * (‖r‖ * ‖x‖) := by
    have hlocal := p09_flAdd_error_le model p₁ (-p₂)
    have h₁ : |p₁| + |-p₂| ≤
        (1 + model.epsilon) *
          (|r.re| * |x.re| + |r.im| * |x.im|) := by
      rw [abs_neg]
      nlinarith
    calc
      |addError.re| ≤ model.epsilon * (|p₁| + |-p₂|) := by
        simpa [addError, u, v, p₁, p₂, p₃, p₄,
          p09RoundedComplexMul] using hlocal
      _ ≤ model.epsilon * ((1 + model.epsilon) *
          (|r.re| * |x.re| + |r.im| * |x.im|)) :=
        mul_le_mul_of_nonneg_left h₁ hε
      _ ≤ model.epsilon * (1 + model.epsilon) * (‖r‖ * ‖x‖) := by
        simpa only [mul_assoc] using mul_le_mul_of_nonneg_left
          (p09_complex_abs_dot_le_norm_mul r x)
          (mul_nonneg hε hOne)
  have haddIm : |addError.im| ≤
      model.epsilon * (1 + model.epsilon) * (‖r‖ * ‖x‖) := by
    have hlocal := p09_flAdd_error_le model p₃ p₄
    have h₁ : |p₃| + |p₄| ≤
        (1 + model.epsilon) *
          (|r.re| * |x.im| + |r.im| * |x.re|) := by
      nlinarith
    calc
      |addError.im| ≤ model.epsilon * (|p₃| + |p₄|) := by
        simpa [addError, u, v, p₁, p₂, p₃, p₄,
          p09RoundedComplexMul] using hlocal
      _ ≤ model.epsilon * ((1 + model.epsilon) *
          (|r.re| * |x.im| + |r.im| * |x.re|)) :=
        mul_le_mul_of_nonneg_left h₁ hε
      _ ≤ model.epsilon * (1 + model.epsilon) * (‖r‖ * ‖x‖) := by
        simpa only [mul_assoc] using mul_le_mul_of_nonneg_left
          (p09_complex_abs_cross_le_norm_mul r x)
          (mul_nonneg hε hOne)
  have hadd : ‖addError‖ ≤ Real.sqrt 2 *
      (model.epsilon * (1 + model.epsilon) * (‖r‖ * ‖x‖)) :=
    p09_complex_norm_le_sqrt_two_mul
      (mul_nonneg (mul_nonneg hε hOne) hR) haddRe haddIm
  have hmulRe : |mulError.re| ≤ model.epsilon * (‖r‖ * ‖x‖) := by
    have h₁ := p09_flMul_error_le model r.re x.re
    have h₂ := p09_flMul_error_le model r.im x.im
    calc
      |mulError.re| ≤ |p₁ - r.re * x.re| + |p₂ - r.im * x.im| := by
        rw [show mulError.re =
          (p₁ - r.re * x.re) - (p₂ - r.im * x.im) by
            simp [mulError, u, v, p₁, p₂, p₃, p₄]
            ring]
        exact abs_sub _ _
      _ ≤ model.epsilon * |r.re| * |x.re| +
          model.epsilon * |r.im| * |x.im| := add_le_add h₁ h₂
      _ = model.epsilon *
          (|r.re| * |x.re| + |r.im| * |x.im|) := by ring
      _ ≤ model.epsilon * (‖r‖ * ‖x‖) :=
        mul_le_mul_of_nonneg_left (p09_complex_abs_dot_le_norm_mul r x) hε
  have hmulIm : |mulError.im| ≤ model.epsilon * (‖r‖ * ‖x‖) := by
    have h₃ := p09_flMul_error_le model r.re x.im
    have h₄ := p09_flMul_error_le model r.im x.re
    calc
      |mulError.im| ≤ |p₃ - r.re * x.im| + |p₄ - r.im * x.re| := by
        rw [show mulError.im =
          (p₃ - r.re * x.im) + (p₄ - r.im * x.re) by
            simp [mulError, u, v, p₁, p₂, p₃, p₄]
            ring]
        exact abs_add_le _ _
      _ ≤ model.epsilon * |r.re| * |x.im| +
          model.epsilon * |r.im| * |x.re| := add_le_add h₃ h₄
      _ = model.epsilon *
          (|r.re| * |x.im| + |r.im| * |x.re|) := by ring
      _ ≤ model.epsilon * (‖r‖ * ‖x‖) :=
        mul_le_mul_of_nonneg_left (p09_complex_abs_cross_le_norm_mul r x) hε
  have hmul : ‖mulError‖ ≤
      Real.sqrt 2 * (model.epsilon * (‖r‖ * ‖x‖)) :=
    p09_complex_norm_le_sqrt_two_mul (mul_nonneg hε hR) hmulRe hmulIm
  have hsplit : p09RoundedComplexMul model r x - r * x =
      addError + mulError := by
    simp [addError, mulError]
  rw [hsplit]
  calc
    ‖addError + mulError‖ ≤ ‖addError‖ + ‖mulError‖ := norm_add_le _ _
    _ ≤ Real.sqrt 2 *
          (model.epsilon * (1 + model.epsilon) * (‖r‖ * ‖x‖)) +
        Real.sqrt 2 * (model.epsilon * (‖r‖ * ‖x‖)) := add_le_add hadd hmul
    _ = (2 * Real.sqrt 2 * model.epsilon +
          Real.sqrt 2 * model.epsilon ^ 2) * ‖r‖ * ‖x‖ := by ring
    _ ≤ (3 * model.epsilon + 2 * model.epsilon ^ 2) * ‖r‖ * ‖x‖ := by
      apply mul_le_mul_of_nonneg_right _ (norm_nonneg x)
      apply mul_le_mul_of_nonneg_right _ (norm_nonneg r)
      nlinarith [mul_le_mul_of_nonneg_right p09_sqrt_two_le_three_halves hε,
        mul_le_mul_of_nonneg_right p09_sqrt_two_le_two (sq_nonneg model.epsilon)]

lemma p09RoundedRoot_error_le {q : ℕ} [NeZero q]
    (model : P09WilkinsonModel) (j : ZMod q) :
    ‖p09RoundedRoot model j - ZMod.stdAddChar j‖ ≤
      2 * model.gamma * model.epsilon := by
  let ε : P09PositiveEpsilon := ⟨model.epsilon, model.epsilon_pos⟩
  let exactModel := p09ExactWilkinsonModel ε model.gamma model.gamma_nonneg
  have hexact : p09RoundedRoot exactModel j = ZMod.stdAddChar j :=
    p09ExactWilkinsonModel_root ε model.gamma model.gamma_nonneg j
  have hre : |(p09RoundedRoot model j - ZMod.stdAddChar j).re| ≤
      model.gamma * model.epsilon := by
    rw [← hexact]
    simpa [p09RoundedRoot, exactModel, p09ExactWilkinsonModel] using
      p09_flCos_error_le model (p09RootAngle j)
  have him : |(p09RoundedRoot model j - ZMod.stdAddChar j).im| ≤
      model.gamma * model.epsilon := by
    rw [← hexact]
    simpa [p09RoundedRoot, exactModel, p09ExactWilkinsonModel] using
      p09_flSin_error_le model (p09RootAngle j)
  have hγε : 0 ≤ model.gamma * model.epsilon :=
    mul_nonneg model.gamma_nonneg (le_of_lt model.epsilon_pos)
  calc
    ‖p09RoundedRoot model j - ZMod.stdAddChar j‖ ≤
        Real.sqrt 2 * (model.gamma * model.epsilon) :=
      p09_complex_norm_le_sqrt_two_mul hγε hre him
    _ ≤ 2 * model.gamma * model.epsilon := by
      nlinarith [mul_le_mul_of_nonneg_right p09_sqrt_two_le_two hγε]

lemma p09RoundedRoot_norm_le {q : ℕ} [NeZero q]
    (model : P09WilkinsonModel) (j : ZMod q) :
    ‖p09RoundedRoot model j‖ ≤ 1 + 2 * model.gamma * model.epsilon := by
  calc
    ‖p09RoundedRoot model j‖ ≤
        ‖p09RoundedRoot model j - ZMod.stdAddChar j‖ +
          ‖ZMod.stdAddChar j‖ := by
      have := norm_add_le
        (p09RoundedRoot model j - ZMod.stdAddChar j) (ZMod.stdAddChar j)
      simpa only [sub_add_cancel] using this
    _ ≤ 2 * model.gamma * model.epsilon + ‖ZMod.stdAddChar j‖ :=
      add_le_add (p09RoundedRoot_error_le model j) le_rfl
    _ = 1 + 2 * model.gamma * model.epsilon := by
      simp [add_comm]

lemma p09RoundedRootMul_error_le {q : ℕ} [NeZero q]
    (model : P09WilkinsonModel) (j : ZMod q) (x : ℂ)
    (hεone : model.epsilon ≤ 1) :
    ‖p09RoundedComplexMul model (p09RoundedRoot model j) x -
        ZMod.stdAddChar j * x‖ ≤
      (model.epsilon * (3 + 2 * model.gamma) +
        (2 + 10 * model.gamma) * model.epsilon ^ 2) * ‖x‖ := by
  let r := p09RoundedRoot model j
  let ω := ZMod.stdAddChar j
  have hε : 0 ≤ model.epsilon := le_of_lt model.epsilon_pos
  have hγ : 0 ≤ model.gamma := model.gamma_nonneg
  have hr : ‖r‖ ≤ 1 + 2 * model.gamma * model.epsilon :=
    p09RoundedRoot_norm_le model j
  have harith := p09RoundedComplexMul_error_le model r x
  have hroot := p09RoundedRoot_error_le model j
  have hsplit : p09RoundedComplexMul model r x - ω * x =
      (p09RoundedComplexMul model r x - r * x) + (r - ω) * x := by
    ring
  rw [hsplit]
  calc
    ‖(p09RoundedComplexMul model r x - r * x) + (r - ω) * x‖ ≤
        ‖p09RoundedComplexMul model r x - r * x‖ + ‖(r - ω) * x‖ :=
      norm_add_le _ _
    _ ≤ (3 * model.epsilon + 2 * model.epsilon ^ 2) * ‖r‖ * ‖x‖ +
        (2 * model.gamma * model.epsilon) * ‖x‖ := by
      exact add_le_add harith (by
        rw [norm_mul]
        exact mul_le_mul_of_nonneg_right hroot (norm_nonneg x))
    _ ≤ (3 * model.epsilon + 2 * model.epsilon ^ 2) *
          (1 + 2 * model.gamma * model.epsilon) * ‖x‖ +
        (2 * model.gamma * model.epsilon) * ‖x‖ := by
      gcongr
    _ ≤ (model.epsilon * (3 + 2 * model.gamma) +
          (2 + 10 * model.gamma) * model.epsilon ^ 2) * ‖x‖ := by
      have hcoef :
          (3 * model.epsilon + 2 * model.epsilon ^ 2) *
              (1 + 2 * model.gamma * model.epsilon) +
            2 * model.gamma * model.epsilon ≤
          model.epsilon * (3 + 2 * model.gamma) +
            (2 + 10 * model.gamma) * model.epsilon ^ 2 := by
        nlinarith [mul_le_mul_of_nonneg_left
          (mul_self_le_mul_self hε hεone) hγ]
      nlinarith [mul_le_mul_of_nonneg_right hcoef (norm_nonneg x)]

def p09SumSecondCoeff : ℕ → ℝ
  | 0 => 0
  | n + 1 => 2 * p09SumSecondCoeff n + n

lemma p09SumSecondCoeff_nonneg (n : ℕ) : 0 ≤ p09SumSecondCoeff n := by
  induction n with
  | zero => simp [p09SumSecondCoeff]
  | succ n ih =>
      simp only [p09SumSecondCoeff]
      positivity

lemma p09_recursiveSum_error_le (model : P09WilkinsonModel)
    (n : ℕ) (v : Fin n → ℝ) (hεone : model.epsilon ≤ 1) :
    |recursiveSum model.flAdd n v - ∑ i : Fin n, v i| ≤
      (model.epsilon * (n - 1 : ℕ) +
        p09SumSecondCoeff n * model.epsilon ^ 2) *
        ∑ i : Fin n, |v i| := by
  induction n with
  | zero => simp [recursiveSum]
  | succ n ih =>
      by_cases hn : n = 0
      · subst n
        simp [recursiveSum, p09SumSecondCoeff]
      · have hnpos : 0 < n := Nat.pos_of_ne_zero hn
        have hε : 0 ≤ model.epsilon := le_of_lt model.epsilon_pos
        let head : Fin n → ℝ := fun i ↦ v i.castSucc
        let last : ℝ := v (Fin.last n)
        let rounded : ℝ := recursiveSum model.flAdd n head
        let exact : ℝ := ∑ i : Fin n, head i
        let mass : ℝ := ∑ i : Fin n, |head i|
        let oldCoeff : ℝ := model.epsilon * (n - 1 : ℕ) +
          p09SumSecondCoeff n * model.epsilon ^ 2
        have hmass : 0 ≤ mass := Finset.sum_nonneg fun _ _ ↦ abs_nonneg _
        have holdCoeff : 0 ≤ oldCoeff := by
          dsimp [oldCoeff]
          exact add_nonneg
            (mul_nonneg hε (Nat.cast_nonneg _))
            (mul_nonneg (p09SumSecondCoeff_nonneg n) (sq_nonneg _))
        have hold : |rounded - exact| ≤ oldCoeff * mass := by
          simpa [rounded, exact, mass, head, oldCoeff] using ih head
        have hexact_abs : |exact| ≤ mass := by
          dsimp [exact, mass, head]
          exact Finset.abs_sum_le_sum_abs _ _
        have hrounded_abs : |rounded| ≤ mass + oldCoeff * mass := by
          calc
            |rounded| ≤ |rounded - exact| + |exact| := by
              have h := abs_add_le (rounded - exact) exact
              simpa only [sub_add_cancel] using h
            _ ≤ oldCoeff * mass + mass := add_le_add hold hexact_abs
            _ = mass + oldCoeff * mass := by ring
        have hlocal := p09_flAdd_error_le model rounded last
        have hstep :
            |model.flAdd rounded last - (exact + last)| ≤
              model.epsilon * (mass + |last|) +
                (1 + model.epsilon) * oldCoeff * mass := by
          calc
            |model.flAdd rounded last - (exact + last)| ≤
                |model.flAdd rounded last - (rounded + last)| +
                  |rounded - exact| := by
              rw [show model.flAdd rounded last - (exact + last) =
                (model.flAdd rounded last - (rounded + last)) +
                  (rounded - exact) by ring]
              exact abs_add_le _ _
            _ ≤ model.epsilon * (|rounded| + |last|) +
                oldCoeff * mass := add_le_add hlocal hold
            _ ≤ model.epsilon *
                  (mass + oldCoeff * mass + |last|) + oldCoeff * mass := by
              gcongr
            _ = model.epsilon * (mass + |last|) +
                (1 + model.epsilon) * oldCoeff * mass := by ring
        have hmassle : mass ≤ mass + |last| := le_add_of_nonneg_right (abs_nonneg _)
        have htotal : 0 ≤ mass + |last| := add_nonneg hmass (abs_nonneg _)
        have hcastOld : ((n - 1 : ℕ) : ℝ) = (n : ℝ) - 1 := by
          rw [Nat.cast_sub (by omega : 1 ≤ n)]
          norm_num
        have hbound :
            model.epsilon * (mass + |last|) +
                (1 + model.epsilon) * oldCoeff * mass ≤
              (model.epsilon * (n : ℝ) +
                p09SumSecondCoeff (n + 1) * model.epsilon ^ 2) *
                (mass + |last|) := by
          have he2mass : model.epsilon ^ 2 * mass ≤
              model.epsilon ^ 2 * (mass + |last|) :=
            mul_le_mul_of_nonneg_left hmassle (sq_nonneg _)
          have he3mass : model.epsilon ^ 3 * mass ≤
              model.epsilon ^ 2 * (mass + |last|) := by
            have hepow : model.epsilon ^ 3 ≤ model.epsilon ^ 2 := by
              nlinarith [mul_self_le_mul_self hε hεone]
            exact le_trans
              (mul_le_mul_of_nonneg_right hepow hmass)
              he2mass
          dsimp [oldCoeff]
          rw [hcastOld]
          simp only [p09SumSecondCoeff]
          have hC := p09SumSecondCoeff_nonneg n
          have hnreal : (1 : ℝ) ≤ (n : ℝ) := by exact_mod_cast hnpos
          have hDn : (n : ℝ) - 1 ≤ (n : ℝ) := by linarith
          have hLead : model.epsilon * ((n : ℝ) - 1) * mass ≤
              model.epsilon * ((n : ℝ) - 1) * (mass + |last|) := by
            exact mul_le_mul_of_nonneg_left hmassle
              (mul_nonneg hε (by linarith))
          have hQuadN : model.epsilon ^ 2 * ((n : ℝ) - 1) * mass ≤
              model.epsilon ^ 2 * (n : ℝ) * (mass + |last|) := by
            have hfactor : model.epsilon ^ 2 * ((n : ℝ) - 1) ≤
                model.epsilon ^ 2 * (n : ℝ) :=
              mul_le_mul_of_nonneg_left hDn (sq_nonneg _)
            exact le_trans
              (mul_le_mul_of_nonneg_right hfactor hmass)
              (mul_le_mul_of_nonneg_left hmassle
                (mul_nonneg (sq_nonneg _) (Nat.cast_nonneg _)))
          have hQuadC : p09SumSecondCoeff n * model.epsilon ^ 2 * mass ≤
              p09SumSecondCoeff n * model.epsilon ^ 2 * (mass + |last|) :=
            mul_le_mul_of_nonneg_left hmassle
              (mul_nonneg hC (sq_nonneg _))
          have hCubicC : p09SumSecondCoeff n *
                (model.epsilon ^ 3 * mass) ≤
              p09SumSecondCoeff n *
                (model.epsilon ^ 2 * (mass + |last|)) :=
            mul_le_mul_of_nonneg_left he3mass hC
          nlinarith
        rw [recursiveSum]
        simp only [hn]
        rw [Fin.sum_univ_castSucc]
        have hsumAbs : (∑ i : Fin (n + 1), |v i|) = mass + |last| := by
          rw [Fin.sum_univ_castSucc]
        rw [hsumAbs]
        have hcastNew : (((n + 1) - 1 : ℕ) : ℝ) = (n : ℝ) := by
          norm_num
        rw [hcastNew]
        exact le_trans hstep hbound

lemma p09RoundedComplexSum_error_le {q : ℕ} [NeZero q]
    (model : P09WilkinsonModel) (term : ZMod q → ℂ)
    (hεone : model.epsilon ≤ 1) :
    ‖p09RoundedComplexSum model term - ∑ j : ZMod q, term j‖ ≤
      (model.epsilon * (q - 1 : ℕ) +
        p09SumSecondCoeff q * model.epsilon ^ 2) *
        ∑ j : ZMod q, ‖term j‖ := by
  let index : Fin q ≃ ZMod q := (ZMod.finEquiv q).toEquiv
  let exact : ℂ := ∑ i : Fin q, term (index i)
  let massVec : ℂ := ∑ i : Fin q, p09AbsComponents (term (index i))
  let coeff : ℝ := model.epsilon * (q - 1 : ℕ) +
    p09SumSecondCoeff q * model.epsilon ^ 2
  have hε : 0 ≤ model.epsilon := le_of_lt model.epsilon_pos
  have hcoeff : 0 ≤ coeff := by
    dsimp [coeff]
    exact add_nonneg
      (mul_nonneg hε (Nat.cast_nonneg _))
      (mul_nonneg (p09SumSecondCoeff_nonneg q) (sq_nonneg _))
  have hsum : exact = ∑ j : ZMod q, term j := by
    dsimp [exact]
    exact index.sum_comp term
  have hre0 := p09_recursiveSum_error_le model q
    (fun i : Fin q ↦ (term (index i)).re) hεone
  have him0 := p09_recursiveSum_error_le model q
    (fun i : Fin q ↦ (term (index i)).im) hεone
  have hre : |(p09RoundedComplexSum model term - exact).re| ≤
      coeff * massVec.re := by
    simpa [p09RoundedComplexSum, index, exact, coeff, massVec,
      p09AbsComponents, map_sum] using hre0
  have him : |(p09RoundedComplexSum model term - exact).im| ≤
      coeff * massVec.im := by
    simpa [p09RoundedComplexSum, index, exact, coeff, massVec,
      p09AbsComponents, map_sum] using him0
  have hmassRe : 0 ≤ massVec.re := by
    dsimp [massVec, p09AbsComponents]
    rw [← Complex.reCLM_apply, map_sum]
    simp only [Complex.reCLM_apply]
    exact Finset.sum_nonneg fun _ _ ↦ abs_nonneg _
  have hmassIm : 0 ≤ massVec.im := by
    dsimp [massVec, p09AbsComponents]
    rw [← Complex.imCLM_apply, map_sum]
    simp only [Complex.imCLM_apply]
    exact Finset.sum_nonneg fun _ _ ↦ abs_nonneg _
  let w : ℂ := (coeff : ℂ) * massVec
  have hwre : |w.re| = coeff * massVec.re := by
    dsimp [w]
    rw [abs_of_nonneg]
    · ring
    · simp only [Complex.mul_re, Complex.ofReal_re, Complex.ofReal_im,
        zero_mul, sub_zero]
      exact mul_nonneg hcoeff hmassRe
  have hwim : |w.im| = coeff * massVec.im := by
    dsimp [w]
    rw [abs_of_nonneg]
    · ring
    · simp only [Complex.mul_im, Complex.ofReal_re, Complex.ofReal_im,
        zero_mul, add_zero]
      exact mul_nonneg hcoeff hmassIm
  have herr : ‖p09RoundedComplexSum model term - exact‖ ≤ ‖w‖ := by
    apply p09_complex_norm_le_of_components
    · simpa only [hwre] using hre
    · simpa only [hwim] using him
  rw [← hsum]
  calc
    ‖p09RoundedComplexSum model term - exact‖ ≤ ‖w‖ := herr
    _ = coeff * ‖massVec‖ := by
      dsimp only [w]
      rw [norm_mul]
      simp [Real.norm_eq_abs, abs_of_nonneg hcoeff]
    _ ≤ coeff * (∑ i : Fin q, ‖p09AbsComponents (term (index i))‖) := by
      apply mul_le_mul_of_nonneg_left _ hcoeff
      dsimp only [massVec]
      exact norm_sum_le _ _
    _ = coeff * (∑ i : Fin q, ‖term (index i)‖) := by
      simp only [p09AbsComponents_norm]
    _ = coeff * (∑ j : ZMod q, ‖term j‖) := by
      congr 1
      exact index.sum_comp (fun j ↦ ‖term j‖)
    _ = (model.epsilon * (q - 1 : ℕ) +
          p09SumSecondCoeff q * model.epsilon ^ 2) *
          ∑ j : ZMod q, ‖term j‖ := by rfl

lemma p09RadixTwoCoefficientApply_eq (j : ZMod 2) (x : ℂ) :
    p09RadixTwoCoefficientApply j x = ZMod.stdAddChar j * x := by
  have hjlt := j.val_lt
  interval_cases h : j.val
  · have hj : j = 0 := by
      apply ZMod.val_injective
      simpa using h
    simp [hj, p09RadixTwoCoefficientApply]
  · have hj : j = 1 := by
      apply ZMod.val_injective
      simpa using h
    have hne : j ≠ 0 := by simpa [hj] using (show (1 : ZMod 2) ≠ 0 by decide)
    rw [p09RadixTwoCoefficientApply, if_neg hne,
      p09StdAddChar_positive_exp, h]
    have harg :
        2 * (Real.pi : ℂ) * Complex.I * ((1 : ℕ) : ℂ) / ((2 : ℕ) : ℂ) =
          (Real.pi : ℂ) * Complex.I := by ring
    rw [harg, Complex.exp_pi_mul_I]
    simp

lemma p09RadixFourCoefficientApply_eq (j : ZMod 4) (x : ℂ) :
    p09RadixFourCoefficientApply j x = ZMod.stdAddChar j * x := by
  have hjlt := j.val_lt
  interval_cases h : j.val
  · have hj : j = 0 := by
      apply ZMod.val_injective
      simpa using h
    simp [hj, p09RadixFourCoefficientApply]
  · have hj : j = 1 := by
      apply ZMod.val_injective
      simpa using h
    have h10 : j ≠ 0 := by simpa [hj] using (show (1 : ZMod 4) ≠ 0 by decide)
    rw [p09RadixFourCoefficientApply, if_neg h10, if_pos hj,
      p09StdAddChar_positive_exp, h]
    have harg :
        2 * (Real.pi : ℂ) * Complex.I * ((1 : ℕ) : ℂ) / ((4 : ℕ) : ℂ) =
          (Real.pi / 2 : ℂ) * Complex.I := by
      ring
    rw [harg, Complex.exp_pi_div_two_mul_I]
    apply Complex.ext <;> simp
  · have hj : j = 2 := by
      apply ZMod.val_injective
      simpa using h
    have h20 : j ≠ 0 := by simpa [hj] using (show (2 : ZMod 4) ≠ 0 by decide)
    have h21 : j ≠ 1 := by simpa [hj] using (show (2 : ZMod 4) ≠ 1 by decide)
    rw [p09RadixFourCoefficientApply, if_neg h20, if_neg h21, if_pos hj,
      p09StdAddChar_positive_exp, h]
    have harg :
        2 * (Real.pi : ℂ) * Complex.I * ((2 : ℕ) : ℂ) / ((4 : ℕ) : ℂ) =
          (Real.pi : ℂ) * Complex.I := by
      ring
    rw [harg, Complex.exp_pi_mul_I]
    simp
  · have hj : j = 3 := by
      apply ZMod.val_injective
      simpa using h
    have h30 : j ≠ 0 := by simpa [hj] using (show (3 : ZMod 4) ≠ 0 by decide)
    have h31 : j ≠ 1 := by simpa [hj] using (show (3 : ZMod 4) ≠ 1 by decide)
    have h32 : j ≠ 2 := by simpa [hj] using (show (3 : ZMod 4) ≠ 2 by decide)
    rw [p09RadixFourCoefficientApply, if_neg h30, if_neg h31, if_neg h32,
      p09StdAddChar_positive_exp, h]
    have harg :
        2 * (Real.pi : ℂ) * Complex.I * ((3 : ℕ) : ℂ) / ((4 : ℕ) : ℂ) =
          ((Real.pi : ℂ) + Real.pi / 2) * Complex.I := by
      ring
    rw [harg, add_mul, Complex.exp_add, Complex.exp_pi_mul_I,
      Complex.exp_pi_div_two_mul_I]
    apply Complex.ext <;> simp

lemma p09RadixTwoCoefficientApply_norm (j : ZMod 2) (x : ℂ) :
    ‖p09RadixTwoCoefficientApply j x‖ = ‖x‖ := by
  rw [p09RadixTwoCoefficientApply_eq, norm_mul]
  simp

lemma p09RadixFourCoefficientApply_norm (j : ZMod 4) (x : ℂ) :
    ‖p09RadixFourCoefficientApply j x‖ = ‖x‖ := by
  rw [p09RadixFourCoefficientApply_eq, norm_mul]
  simp

lemma p09RoundedRadixTwoBlock_error_le (model : P09WilkinsonModel)
    (x : ZMod 2 → ℂ) (k : ZMod 2) (hεone : model.epsilon ≤ 1) :
    ‖p09RoundedRadixTwoBlock model x k -
        ∑ j : ZMod 2, ZMod.stdAddChar (j * k) * x j‖ ≤
      (model.epsilon + model.epsilon ^ 2) *
        ∑ j : ZMod 2, ‖x j‖ := by
  have h := p09RoundedComplexSum_error_le model
    (fun j : ZMod 2 ↦ p09RadixTwoCoefficientApply (j * k) (x j)) hεone
  simpa [p09RoundedRadixTwoBlock, p09RadixTwoCoefficientApply_eq,
    p09RadixTwoCoefficientApply_norm, p09SumSecondCoeff] using h

lemma p09RoundedRadixFourBlock_error_le (model : P09WilkinsonModel)
    (x : ZMod 4 → ℂ) (k : ZMod 4) (hεone : model.epsilon ≤ 1) :
    ‖p09RoundedRadixFourBlock model x k -
        ∑ j : ZMod 4, ZMod.stdAddChar (j * k) * x j‖ ≤
      (2 * model.epsilon + model.epsilon ^ 2) *
        ∑ j : ZMod 4, ‖x j‖ := by
  let index : Fin 4 ≃ ZMod 4 := (ZMod.finEquiv 4).toEquiv
  let term : Fin 4 → ℂ := fun i ↦
    p09RadixFourCoefficientApply (index i * k) (x (index i))
  let a := p09RoundedComplexAdd model (term 0) (term 1)
  let b := p09RoundedComplexAdd model (term 2) (term 3)
  let s₁ := term 0 + term 1
  let s₂ := term 2 + term 3
  let mass₁ := ‖term 0‖ + ‖term 1‖
  let mass₂ := ‖term 2‖ + ‖term 3‖
  have hε : 0 ≤ model.epsilon := le_of_lt model.epsilon_pos
  have he₁ : ‖a - s₁‖ ≤ model.epsilon * mass₁ := by
    simpa [a, s₁, mass₁] using
      p09RoundedComplexAdd_error_le model (term 0) (term 1)
  have he₂ : ‖b - s₂‖ ≤ model.epsilon * mass₂ := by
    simpa [b, s₂, mass₂] using
      p09RoundedComplexAdd_error_le model (term 2) (term 3)
  have ha : ‖a‖ ≤ (1 + model.epsilon) * mass₁ := by
    calc
      ‖a‖ ≤ ‖a - s₁‖ + ‖s₁‖ := by
        have h := norm_add_le (a - s₁) s₁
        simpa only [sub_add_cancel] using h
      _ ≤ model.epsilon * mass₁ + mass₁ := by
        exact add_le_add he₁ (by
          dsimp [s₁, mass₁]
          exact norm_add_le _ _)
      _ = (1 + model.epsilon) * mass₁ := by ring
  have hb : ‖b‖ ≤ (1 + model.epsilon) * mass₂ := by
    calc
      ‖b‖ ≤ ‖b - s₂‖ + ‖s₂‖ := by
        have h := norm_add_le (b - s₂) s₂
        simpa only [sub_add_cancel] using h
      _ ≤ model.epsilon * mass₂ + mass₂ := by
        exact add_le_add he₂ (by
          dsimp [s₂, mass₂]
          exact norm_add_le _ _)
      _ = (1 + model.epsilon) * mass₂ := by ring
  have hout := p09RoundedComplexAdd_error_le model a b
  have hsplit :
      p09RoundedComplexAdd model a b - (s₁ + s₂) =
        (p09RoundedComplexAdd model a b - (a + b)) +
          (a - s₁) + (b - s₂) := by ring
  have hmain : ‖p09RoundedComplexAdd model a b - (s₁ + s₂)‖ ≤
      (2 * model.epsilon + model.epsilon ^ 2) * (mass₁ + mass₂) := by
    rw [hsplit]
    calc
      ‖(p09RoundedComplexAdd model a b - (a + b)) +
          (a - s₁) + (b - s₂)‖ ≤
          ‖p09RoundedComplexAdd model a b - (a + b)‖ +
            ‖a - s₁‖ + ‖b - s₂‖ := by
        exact le_trans (norm_add_le _ _)
          (add_le_add (norm_add_le _ _) le_rfl)
      _ ≤ model.epsilon * (‖a‖ + ‖b‖) +
          model.epsilon * mass₁ + model.epsilon * mass₂ := by
        exact add_le_add (add_le_add hout he₁) he₂
      _ ≤ model.epsilon * ((1 + model.epsilon) * mass₁ +
          (1 + model.epsilon) * mass₂) +
          model.epsilon * mass₁ + model.epsilon * mass₂ := by
        gcongr
      _ = (2 * model.epsilon + model.epsilon ^ 2) *
          (mass₁ + mass₂) := by ring
  have hsum : s₁ + s₂ =
      ∑ j : ZMod 4, ZMod.stdAddChar (j * k) * x j := by
    have hfin : s₁ + s₂ = ∑ i : Fin 4, term i := by
      simp [s₁, s₂, Fin.sum_univ_succ, term]
      ring
    rw [hfin]
    calc
      (∑ i : Fin 4, term i) =
          ∑ i : Fin 4, ZMod.stdAddChar (index i * k) * x (index i) := by
        apply Finset.sum_congr rfl
        intro i _
        exact p09RadixFourCoefficientApply_eq _ _
      _ = ∑ j : ZMod 4, ZMod.stdAddChar (j * k) * x j :=
        index.sum_comp (fun j ↦ ZMod.stdAddChar (j * k) * x j)
  have hmass : mass₁ + mass₂ = ∑ j : ZMod 4, ‖x j‖ := by
    have hfin : mass₁ + mass₂ = ∑ i : Fin 4, ‖term i‖ := by
      simp [mass₁, mass₂, Fin.sum_univ_succ, term]
      ring
    rw [hfin]
    simp only [term, p09RadixFourCoefficientApply_norm]
    exact index.sum_comp (fun j ↦ ‖x j‖)
  change ‖p09RoundedComplexAdd model a b -
      (∑ j : ZMod 4, ZMod.stdAddChar (j * k) * x j)‖ ≤
    (2 * model.epsilon + model.epsilon ^ 2) * ∑ j : ZMod 4, ‖x j‖
  rw [← hsum, ← hmass]
  exact hmain

noncomputable def p09GenericBlockSecondCoeff (q : ℕ) (γ : ℝ) : ℝ :=
  let s : ℝ := (q - 1 : ℕ)
  let A : ℝ := 3 + 2 * γ
  let B : ℝ := 2 + 10 * γ
  let C : ℝ := p09SumSecondCoeff q
  C + s * A + B + s * B + C * A + C * B

lemma p09GenericBlockSecondCoeff_nonneg (q : ℕ) {γ : ℝ} (hγ : 0 ≤ γ) :
    0 ≤ p09GenericBlockSecondCoeff q γ := by
  dsimp [p09GenericBlockSecondCoeff]
  have hC := p09SumSecondCoeff_nonneg q
  positivity

lemma p09RoundedGenericRadixBlock_error_le {q : ℕ} [NeZero q]
    (model : P09WilkinsonModel) (x : ZMod q → ℂ) (k : ZMod q)
    (hq : 2 ≤ q) (hεone : model.epsilon ≤ 1) :
    ‖p09RoundedGenericRadixBlock model x k -
        ∑ j : ZMod q, ZMod.stdAddChar (j * k) * x j‖ ≤
      (model.epsilon * (2 * ((q : ℝ) + model.gamma)) +
        p09GenericBlockSecondCoeff q model.gamma * model.epsilon ^ 2) *
        ∑ j : ZMod q, ‖x j‖ := by
  let roundedTerm : ZMod q → ℂ := fun j ↦
    p09RoundedComplexMul model (p09RoundedRoot model (j * k)) (x j)
  let exactTerm : ZMod q → ℂ := fun j ↦ ZMod.stdAddChar (j * k) * x j
  let mass : ℝ := ∑ j : ZMod q, ‖x j‖
  let A : ℝ := 3 + 2 * model.gamma
  let B : ℝ := 2 + 10 * model.gamma
  let s : ℝ := (q - 1 : ℕ)
  let C : ℝ := p09SumSecondCoeff q
  let termCoeff : ℝ := model.epsilon * A + B * model.epsilon ^ 2
  let sumCoeff : ℝ := model.epsilon * s + C * model.epsilon ^ 2
  have hε : 0 ≤ model.epsilon := le_of_lt model.epsilon_pos
  have hγ : 0 ≤ model.gamma := model.gamma_nonneg
  have hA : 0 ≤ A := by dsimp [A]; positivity
  have hB : 0 ≤ B := by dsimp [B]; positivity
  have hs : 0 ≤ s := by dsimp [s]; positivity
  have hC : 0 ≤ C := by exact p09SumSecondCoeff_nonneg q
  have htermCoeff : 0 ≤ termCoeff := by
    dsimp [termCoeff]
    positivity
  have hsumCoeff : 0 ≤ sumCoeff := by
    dsimp [sumCoeff]
    positivity
  have hterm : ∀ j, ‖roundedTerm j - exactTerm j‖ ≤
      termCoeff * ‖x j‖ := by
    intro j
    simpa [roundedTerm, exactTerm, termCoeff, A, B] using
      p09RoundedRootMul_error_le model (j * k) (x j) hεone
  have hroundedTerm : ∀ j, ‖roundedTerm j‖ ≤
      (1 + termCoeff) * ‖x j‖ := by
    intro j
    calc
      ‖roundedTerm j‖ ≤ ‖roundedTerm j - exactTerm j‖ + ‖exactTerm j‖ := by
        have h := norm_add_le (roundedTerm j - exactTerm j) (exactTerm j)
        simpa only [sub_add_cancel] using h
      _ ≤ termCoeff * ‖x j‖ + ‖x j‖ := by
        exact add_le_add (hterm j) (by simp [exactTerm])
      _ = (1 + termCoeff) * ‖x j‖ := by ring
  have hmass : 0 ≤ mass := by
    dsimp [mass]
    exact Finset.sum_nonneg fun _ _ ↦ norm_nonneg _
  have hroundedMass : (∑ j : ZMod q, ‖roundedTerm j‖) ≤
      (1 + termCoeff) * mass := by
    calc
      (∑ j : ZMod q, ‖roundedTerm j‖) ≤
          ∑ j : ZMod q, (1 + termCoeff) * ‖x j‖ :=
        Finset.sum_le_sum fun j _ ↦ hroundedTerm j
      _ = (1 + termCoeff) * mass := by
        simp [mass, Finset.mul_sum]
  have hsumRound := p09RoundedComplexSum_error_le model roundedTerm hεone
  have hsumRound' :
      ‖p09RoundedComplexSum model roundedTerm - ∑ j, roundedTerm j‖ ≤
        sumCoeff * ((1 + termCoeff) * mass) := by
    calc
      ‖p09RoundedComplexSum model roundedTerm - ∑ j, roundedTerm j‖ ≤
          sumCoeff * ∑ j, ‖roundedTerm j‖ := by
        simpa [sumCoeff, s, C] using hsumRound
      _ ≤ sumCoeff * ((1 + termCoeff) * mass) :=
        mul_le_mul_of_nonneg_left hroundedMass hsumCoeff
  have htermSum : ‖(∑ j, roundedTerm j) - ∑ j, exactTerm j‖ ≤
      termCoeff * mass := by
    rw [← Finset.sum_sub_distrib]
    calc
      ‖∑ j : ZMod q, (roundedTerm j - exactTerm j)‖ ≤
          ∑ j : ZMod q, ‖roundedTerm j - exactTerm j‖ := norm_sum_le _ _
      _ ≤ ∑ j : ZMod q, termCoeff * ‖x j‖ :=
        Finset.sum_le_sum fun j _ ↦ hterm j
      _ = termCoeff * mass := by simp [mass, Finset.mul_sum]
  have hsplit :
      p09RoundedComplexSum model roundedTerm - ∑ j, exactTerm j =
        (p09RoundedComplexSum model roundedTerm - ∑ j, roundedTerm j) +
          ((∑ j, roundedTerm j) - ∑ j, exactTerm j) := by ring
  have hraw :
      ‖p09RoundedComplexSum model roundedTerm - ∑ j, exactTerm j‖ ≤
        (sumCoeff * (1 + termCoeff) + termCoeff) * mass := by
    rw [hsplit]
    calc
      ‖(p09RoundedComplexSum model roundedTerm - ∑ j, roundedTerm j) +
          ((∑ j, roundedTerm j) - ∑ j, exactTerm j)‖ ≤
          ‖p09RoundedComplexSum model roundedTerm - ∑ j, roundedTerm j‖ +
            ‖(∑ j, roundedTerm j) - ∑ j, exactTerm j‖ := norm_add_le _ _
      _ ≤ sumCoeff * ((1 + termCoeff) * mass) + termCoeff * mass :=
        add_le_add hsumRound' htermSum
      _ = (sumCoeff * (1 + termCoeff) + termCoeff) * mass := by ring
  have he3 : model.epsilon ^ 3 ≤ model.epsilon ^ 2 := by
    nlinarith [mul_self_le_mul_self hε hεone]
  have he4 : model.epsilon ^ 4 ≤ model.epsilon ^ 2 := by
    have he2one : model.epsilon ^ 2 ≤ 1 := by
      nlinarith [mul_self_le_mul_self hε hεone]
    nlinarith [mul_le_mul_of_nonneg_left he2one (sq_nonneg model.epsilon)]
  have hlead : s + A ≤ 2 * ((q : ℝ) + model.gamma) := by
    have hq1 : (1 : ℕ) ≤ q := by omega
    have hcast : ((q - 1 : ℕ) : ℝ) = (q : ℝ) - 1 := by
      rw [Nat.cast_sub hq1]
      norm_num
    dsimp [s, A]
    rw [hcast]
    have hqreal : (2 : ℝ) ≤ (q : ℝ) := by exact_mod_cast hq
    linarith
  have hcoeff : sumCoeff * (1 + termCoeff) + termCoeff ≤
      model.epsilon * (2 * ((q : ℝ) + model.gamma)) +
        p09GenericBlockSecondCoeff q model.gamma * model.epsilon ^ 2 := by
    dsimp [sumCoeff, termCoeff, s, A, B, C,
      p09GenericBlockSecondCoeff] at *
    have hsB : 0 ≤ ((q - 1 : ℕ) : ℝ) * (2 + 10 * model.gamma) :=
      mul_nonneg (Nat.cast_nonneg _) hB
    have hCA : 0 ≤ p09SumSecondCoeff q * (3 + 2 * model.gamma) :=
      mul_nonneg hC hA
    have hCB : 0 ≤ p09SumSecondCoeff q * (2 + 10 * model.gamma) :=
      mul_nonneg hC hB
    nlinarith [mul_le_mul_of_nonneg_left he3 hsB,
      mul_le_mul_of_nonneg_left he3 hCA,
      mul_le_mul_of_nonneg_left he4 hCB,
      mul_le_mul_of_nonneg_left hlead hε]
  change ‖p09RoundedComplexSum model roundedTerm - ∑ j, exactTerm j‖ ≤ _
  exact le_trans hraw (mul_le_mul_of_nonneg_right hcoeff hmass)

noncomputable def p09FiniteNorm2 {ι : Type*} [Fintype ι] (x : ι → ℂ) : ℝ :=
  Real.sqrt (∑ i, ‖x i‖ ^ 2)

lemma p09FiniteNorm2_equiv {ι κ : Type*} [Fintype ι] [Fintype κ]
    (e : ι ≃ κ) (x : κ → ℂ) :
    p09FiniteNorm2 (fun i ↦ x (e i)) = p09FiniteNorm2 x := by
  unfold p09FiniteNorm2
  congr 1
  exact e.sum_comp (fun i ↦ ‖x i‖ ^ 2)

lemma p09FiniteNorm2_block_bound {β κ : Type*} [Fintype β] [Fintype κ]
    (err x : β × κ → ℂ) (c : ℝ) (hc : 0 ≤ c)
    (h : ∀ b k, ‖err (b, k)‖ ≤ c * ∑ j : κ, ‖x (b, j)‖) :
    p09FiniteNorm2 err ≤
      c * (Fintype.card κ : ℝ) * p09FiniteNorm2 x := by
  let q : ℝ := Fintype.card κ
  let mass : β → ℝ := fun b ↦ ∑ j : κ, ‖x (b, j)‖
  have hq : 0 ≤ q := by dsimp [q]; positivity
  have hmass : ∀ b, 0 ≤ mass b := by
    intro b
    exact Finset.sum_nonneg fun _ _ ↦ norm_nonneg _
  have hpoint : ∀ b k, ‖err (b, k)‖ ^ 2 ≤ c ^ 2 * (mass b) ^ 2 := by
    intro b k
    calc
      ‖err (b, k)‖ ^ 2 ≤ (c * mass b) ^ 2 :=
        (sq_le_sq₀ (norm_nonneg _) (mul_nonneg hc (hmass b))).2
          (by simpa [mass] using h b k)
      _ = c ^ 2 * (mass b) ^ 2 := by rw [mul_pow]
  have hmassSq : ∀ b, (mass b) ^ 2 ≤
      q * ∑ j : κ, ‖x (b, j)‖ ^ 2 := by
    intro b
    dsimp [mass, q]
    simpa using (sq_sum_le_card_mul_sum_sq
      (s := (Finset.univ : Finset κ)) (f := fun j ↦ ‖x (b, j)‖))
  have hsum : (∑ p : β × κ, ‖err p‖ ^ 2) ≤
      c ^ 2 * q ^ 2 * ∑ p : β × κ, ‖x p‖ ^ 2 := by
    rw [Fintype.sum_prod_type, Fintype.sum_prod_type]
    calc
      (∑ b : β, ∑ k : κ, ‖err (b, k)‖ ^ 2) ≤
          ∑ b : β, ∑ _k : κ, c ^ 2 * (mass b) ^ 2 :=
        Finset.sum_le_sum fun b _ ↦ Finset.sum_le_sum fun k _ ↦ hpoint b k
      _ = ∑ b : β, q * (c ^ 2 * (mass b) ^ 2) := by
        apply Finset.sum_congr rfl
        intro b _
        simp [q, mul_comm]
      _ ≤ ∑ b : β, q * (c ^ 2 *
          (q * ∑ j : κ, ‖x (b, j)‖ ^ 2)) := by
        apply Finset.sum_le_sum
        intro b _
        exact mul_le_mul_of_nonneg_left
          (mul_le_mul_of_nonneg_left (hmassSq b) (sq_nonneg c)) hq
      _ = c ^ 2 * q ^ 2 *
          ∑ b : β, ∑ j : κ, ‖x (b, j)‖ ^ 2 := by
        rw [Finset.mul_sum]
        apply Finset.sum_congr rfl
        intro b _
        ring
  have herrsum : 0 ≤ ∑ p : β × κ, ‖err p‖ ^ 2 :=
    Finset.sum_nonneg fun _ _ ↦ sq_nonneg _
  have hxsum : 0 ≤ ∑ p : β × κ, ‖x p‖ ^ 2 :=
    Finset.sum_nonneg fun _ _ ↦ sq_nonneg _
  unfold p09FiniteNorm2
  rw [← sq_le_sq₀ (Real.sqrt_nonneg _)
    (mul_nonneg (mul_nonneg hc hq) (Real.sqrt_nonneg _)),
    Real.sq_sqrt herrsum, mul_pow, mul_pow, Real.sq_sqrt hxsum]
  simpa [mul_assoc] using hsum

lemma p09ComplexNorm2_eq_finiteNorm2 {n : ℕ} [NeZero n]
    (x : ZMod n → ℂ) : p09ComplexNorm2 x = p09FiniteNorm2 x := rfl

lemma p09RoundedRadixTwoBlock_error_le_cast {q : ℕ} [NeZero q]
    (hq : q = 2) (model : P09WilkinsonModel) (x : ZMod q → ℂ)
    (k : ZMod q) (hεone : model.epsilon ≤ 1) :
    ‖p09RoundedRadixTwoBlock model
          (fun j : ZMod 2 ↦ x (hq.symm ▸ j)) (hq ▸ k) -
        ∑ j : ZMod q, ZMod.stdAddChar (j * k) * x j‖ ≤
      (model.epsilon + model.epsilon ^ 2) * ∑ j : ZMod q, ‖x j‖ := by
  subst q
  simpa using p09RoundedRadixTwoBlock_error_le model x k hεone

lemma p09RoundedRadixFourBlock_error_le_cast {q : ℕ} [NeZero q]
    (hq : q = 4) (model : P09WilkinsonModel) (x : ZMod q → ℂ)
    (k : ZMod q) (hεone : model.epsilon ≤ 1) :
    ‖p09RoundedRadixFourBlock model
          (fun j : ZMod 4 ↦ x (hq.symm ▸ j)) (hq ▸ k) -
        ∑ j : ZMod q, ZMod.stdAddChar (j * k) * x j‖ ≤
      (2 * model.epsilon + model.epsilon ^ 2) * ∑ j : ZMod q, ‖x j‖ := by
  subst q
  simpa using p09RoundedRadixFourBlock_error_le model x k hεone

noncomputable def p09BlockSecondCoeff {n : ℕ} [NeZero n]
    (stage : P09MixedRadixStage n) (γ : ℝ) : ℝ :=
  if stage.radix = 2 then 2
  else if stage.radix = 4 then 4
  else (stage.radix : ℝ) * p09GenericBlockSecondCoeff stage.radix γ

lemma p09RoundedMixedRadixBlockApply_error_le {n : ℕ} [NeZero n]
    (model : P09WilkinsonModel) (stage : P09MixedRadixStage n)
    (x : ZMod n → ℂ) (hεone : model.epsilon ≤ 1) :
    0 ≤ p09BlockSecondCoeff stage model.gamma ∧
      p09ComplexNorm2 (fun i ↦
        p09RoundedMixedRadixBlockApply model stage x i -
          p09MixedRadixBlockApply stage x i) ≤
        (model.epsilon *
            (Real.sqrt (stage.radix : ℝ) *
              p09Alpha stage.radix model.gamma) +
          p09BlockSecondCoeff stage model.gamma * model.epsilon ^ 2) *
            p09ComplexNorm2 x := by
  letI : NeZero stage.radix := ⟨stage.radix_ne_zero⟩
  let input : Fin stage.blockCount × ZMod stage.radix → ℂ := fun bj ↦
    x (stage.permutation (stage.reindex bj))
  let err : Fin stage.blockCount × ZMod stage.radix → ℂ := fun bk ↦
    p09RoundedMixedRadixBlockApply model stage x (stage.reindex bk) -
      p09MixedRadixBlockApply stage x (stage.reindex bk)
  have hinputNorm : p09FiniteNorm2 input = p09ComplexNorm2 x := by
    rw [p09ComplexNorm2_eq_finiteNorm2]
    exact p09FiniteNorm2_equiv (stage.reindex.trans stage.permutation) x
  have herrNorm : p09ComplexNorm2 (fun i ↦
      p09RoundedMixedRadixBlockApply model stage x i -
        p09MixedRadixBlockApply stage x i) = p09FiniteNorm2 err := by
    rw [p09ComplexNorm2_eq_finiteNorm2]
    symm
    exact p09FiniteNorm2_equiv stage.reindex (fun i ↦
      p09RoundedMixedRadixBlockApply model stage x i -
        p09MixedRadixBlockApply stage x i)
  have hε : 0 ≤ model.epsilon := le_of_lt model.epsilon_pos
  by_cases h2 : stage.radix = 2
  · refine ⟨by simp [p09BlockSecondCoeff, h2], ?_⟩
    have hpoint : ∀ b k, ‖err (b, k)‖ ≤
        (model.epsilon + model.epsilon ^ 2) *
          ∑ j : ZMod stage.radix, ‖input (b, j)‖ := by
      intro b k
      have hb := p09RoundedRadixTwoBlock_error_le_cast h2 model
        (fun j ↦ input (b, j)) k hεone
      simpa [err, input, p09RoundedMixedRadixBlockApply,
        p09MixedRadixBlockApply, h2] using hb
    have hc : 0 ≤ model.epsilon + model.epsilon ^ 2 :=
      add_nonneg hε (sq_nonneg _)
    have hb := p09FiniteNorm2_block_bound err input
      (model.epsilon + model.epsilon ^ 2) hc hpoint
    rw [herrNorm]
    rw [hinputNorm] at hb
    simpa [p09BlockSecondCoeff, h2] using (show
      p09FiniteNorm2 err ≤
        (model.epsilon *
            (Real.sqrt (stage.radix : ℝ) * p09Alpha stage.radix model.gamma) +
          2 * model.epsilon ^ 2) * p09ComplexNorm2 x from (by
      calc
      p09FiniteNorm2 err ≤
          (model.epsilon + model.epsilon ^ 2) *
            (Fintype.card (ZMod stage.radix) : ℝ) * p09ComplexNorm2 x := by
        simpa [hinputNorm] using hb
      _ = (model.epsilon *
            (Real.sqrt (stage.radix : ℝ) * p09Alpha stage.radix model.gamma) +
          2 * model.epsilon ^ 2) * p09ComplexNorm2 x := by
        rw [ZMod.card]
        have halpha : Real.sqrt (stage.radix : ℝ) *
            p09Alpha stage.radix model.gamma = 2 := by
          simp only [h2, p09Alpha, if_pos]
          norm_num
        rw [halpha, h2]
        ring))
  · by_cases h4 : stage.radix = 4
    · refine ⟨by simp [p09BlockSecondCoeff, h2, h4], ?_⟩
      have hpoint : ∀ b k, ‖err (b, k)‖ ≤
          (2 * model.epsilon + model.epsilon ^ 2) *
            ∑ j : ZMod stage.radix, ‖input (b, j)‖ := by
        intro b k
        have hb := p09RoundedRadixFourBlock_error_le_cast h4 model
          (fun j ↦ input (b, j)) k hεone
        simpa [err, input, p09RoundedMixedRadixBlockApply,
          p09MixedRadixBlockApply, h2, h4] using hb
      have hc : 0 ≤ 2 * model.epsilon + model.epsilon ^ 2 :=
        add_nonneg (mul_nonneg (by norm_num) hε) (sq_nonneg _)
      have hb := p09FiniteNorm2_block_bound err input
        (2 * model.epsilon + model.epsilon ^ 2) hc hpoint
      rw [herrNorm]
      rw [hinputNorm] at hb
      simpa [p09BlockSecondCoeff, h2, h4] using (show
        p09FiniteNorm2 err ≤
          (model.epsilon *
              (Real.sqrt (stage.radix : ℝ) * p09Alpha stage.radix model.gamma) +
            4 * model.epsilon ^ 2) * p09ComplexNorm2 x from (by
        calc
        p09FiniteNorm2 err ≤
            (2 * model.epsilon + model.epsilon ^ 2) *
              (Fintype.card (ZMod stage.radix) : ℝ) * p09ComplexNorm2 x := by
          simpa [hinputNorm] using hb
        _ ≤ (model.epsilon *
              (Real.sqrt (stage.radix : ℝ) * p09Alpha stage.radix model.gamma) +
            4 * model.epsilon ^ 2) * p09ComplexNorm2 x := by
          rw [ZMod.card]
          have halpha : Real.sqrt (stage.radix : ℝ) *
              p09Alpha stage.radix model.gamma = 10 := by
            simp only [h4, p09Alpha, if_false, if_pos]
            norm_num
          rw [halpha, h4]
          have hcoef : (2 * model.epsilon + model.epsilon ^ 2) * (4 : ℝ) ≤
              model.epsilon * 10 + 4 * model.epsilon ^ 2 := by nlinarith
          have hxnorm : 0 ≤ p09ComplexNorm2 x := by
            unfold p09ComplexNorm2
            positivity
          norm_num
          exact mul_le_mul_of_nonneg_right hcoef hxnorm))
    · let D := p09GenericBlockSecondCoeff stage.radix model.gamma
      refine ⟨?_, ?_⟩
      · simp only [p09BlockSecondCoeff, h2, h4, if_false]
        exact mul_nonneg (Nat.cast_nonneg _)
          (p09GenericBlockSecondCoeff_nonneg _ model.gamma_nonneg)
      have hpoint : ∀ b k, ‖err (b, k)‖ ≤
          (model.epsilon * (2 * ((stage.radix : ℝ) + model.gamma)) +
            D * model.epsilon ^ 2) *
            ∑ j : ZMod stage.radix, ‖input (b, j)‖ := by
        intro b k
        have hb := p09RoundedGenericRadixBlock_error_le model
          (fun j ↦ input (b, j)) k stage.radix_two_le hεone
        simpa [err, input, D, p09RoundedMixedRadixBlockApply,
          p09MixedRadixBlockApply, h2, h4] using hb
      have hc : 0 ≤ model.epsilon *
            (2 * ((stage.radix : ℝ) + model.gamma)) +
          D * model.epsilon ^ 2 := by
        apply add_nonneg
        · exact mul_nonneg hε (mul_nonneg (by norm_num)
            (add_nonneg (Nat.cast_nonneg _) model.gamma_nonneg))
        · exact mul_nonneg (p09GenericBlockSecondCoeff_nonneg _
            model.gamma_nonneg) (sq_nonneg _)
      have hb := p09FiniteNorm2_block_bound err input _ hc hpoint
      rw [herrNorm]
      rw [hinputNorm] at hb
      simpa [p09BlockSecondCoeff, h2, h4, D] using (show
        p09FiniteNorm2 err ≤
          (model.epsilon *
              (Real.sqrt (stage.radix : ℝ) *
                p09Alpha stage.radix model.gamma) +
            ((stage.radix : ℝ) * D) * model.epsilon ^ 2) *
              p09ComplexNorm2 x from (by
        calc
        p09FiniteNorm2 err ≤
            (model.epsilon * (2 * ((stage.radix : ℝ) + model.gamma)) +
              D * model.epsilon ^ 2) *
              (Fintype.card (ZMod stage.radix) : ℝ) * p09ComplexNorm2 x := by
          simpa [hinputNorm] using hb
        _ = (model.epsilon *
              (Real.sqrt (stage.radix : ℝ) *
                p09Alpha stage.radix model.gamma) +
            ((stage.radix : ℝ) * D) * model.epsilon ^ 2) *
              p09ComplexNorm2 x := by
          have hrad : 0 ≤ (stage.radix : ℝ) := Nat.cast_nonneg _
          rw [ZMod.card]
          rw [p09Alpha]
          simp only [h2, h4, if_false]
          have hsqrt : Real.sqrt (stage.radix : ℝ) *
              Real.sqrt (stage.radix : ℝ) = (stage.radix : ℝ) := by
            simpa [pow_two] using Real.sq_sqrt hrad
          have hprod : Real.sqrt (stage.radix : ℝ) *
                (2 * Real.sqrt (stage.radix : ℝ) *
                  ((stage.radix : ℝ) + model.gamma)) =
              2 * (stage.radix : ℝ) *
                ((stage.radix : ℝ) + model.gamma) := by
            calc
              _ = 2 * (Real.sqrt (stage.radix : ℝ) *
                    Real.sqrt (stage.radix : ℝ)) *
                  ((stage.radix : ℝ) + model.gamma) := by ring
              _ = _ := by rw [hsqrt]
          rw [hprod]
          ring))

lemma p09FiniteNorm2_eq_euclidean {ι : Type*} [Fintype ι] (x : ι → ℂ) :
    p09FiniteNorm2 x =
      ‖(WithLp.toLp 2 x : EuclideanSpace ℂ ι)‖ := by
  rw [EuclideanSpace.norm_eq]
  rfl

lemma p09FiniteNorm2_add_le {ι : Type*} [Fintype ι] (x y : ι → ℂ) :
    p09FiniteNorm2 (fun i ↦ x i + y i) ≤
      p09FiniteNorm2 x + p09FiniteNorm2 y := by
  simp only [p09FiniteNorm2_eq_euclidean]
  exact norm_add_le
    (WithLp.toLp 2 x : EuclideanSpace ℂ ι)
    (WithLp.toLp 2 y : EuclideanSpace ℂ ι)

lemma p09FiniteNorm2_sub_le {ι : Type*} [Fintype ι] (x y : ι → ℂ) :
    p09FiniteNorm2 (fun i ↦ x i - y i) ≤
      p09FiniteNorm2 x + p09FiniteNorm2 y := by
  simp only [p09FiniteNorm2_eq_euclidean]
  exact norm_sub_le
    (WithLp.toLp 2 x : EuclideanSpace ℂ ι)
    (WithLp.toLp 2 y : EuclideanSpace ℂ ι)

lemma p09FiniteNorm2_pointwise_bound {ι : Type*} [Fintype ι]
    (x y : ι → ℂ) (c : ℝ) (hc : 0 ≤ c)
    (h : ∀ i, ‖x i‖ ≤ c * ‖y i‖) :
    p09FiniteNorm2 x ≤ c * p09FiniteNorm2 y := by
  have hs : (∑ i, ‖x i‖ ^ 2) ≤ c ^ 2 * ∑ i, ‖y i‖ ^ 2 := by
    calc
      (∑ i, ‖x i‖ ^ 2) ≤ ∑ i, (c * ‖y i‖) ^ 2 := by
        apply Finset.sum_le_sum
        intro i _
        exact (sq_le_sq₀ (norm_nonneg _) (mul_nonneg hc (norm_nonneg _))).2 (h i)
      _ = c ^ 2 * ∑ i, ‖y i‖ ^ 2 := by
        rw [Finset.mul_sum]
        apply Finset.sum_congr rfl
        intro i _
        ring
  have hx : 0 ≤ ∑ i, ‖x i‖ ^ 2 := Finset.sum_nonneg fun _ _ ↦ sq_nonneg _
  have hy : 0 ≤ ∑ i, ‖y i‖ ^ 2 := Finset.sum_nonneg fun _ _ ↦ sq_nonneg _
  unfold p09FiniteNorm2
  rw [← sq_le_sq₀ (Real.sqrt_nonneg _) (mul_nonneg hc (Real.sqrt_nonneg _)),
    Real.sq_sqrt hx, mul_pow, Real.sq_sqrt hy]
  exact hs

lemma p09ComplexNorm2_add_le {n : ℕ} [NeZero n] (x y : ZMod n → ℂ) :
    p09ComplexNorm2 (fun i ↦ x i + y i) ≤
      p09ComplexNorm2 x + p09ComplexNorm2 y :=
  p09FiniteNorm2_add_le x y

lemma p09ComplexNorm2_sub_le {n : ℕ} [NeZero n] (x y : ZMod n → ℂ) :
    p09ComplexNorm2 (fun i ↦ x i - y i) ≤
      p09ComplexNorm2 x + p09ComplexNorm2 y :=
  p09FiniteNorm2_sub_le x y

lemma p09MixedRadixTwiddleApply_norm {n : ℕ} [NeZero n]
    (stage : P09MixedRadixStage n) (x : ZMod n → ℂ) :
    p09ComplexNorm2 (p09MixedRadixTwiddleApply stage x) =
      p09ComplexNorm2 x := by
  unfold p09ComplexNorm2 p09ComplexNorm2Sq p09MixedRadixTwiddleApply
  congr 1
  apply Finset.sum_congr rfl
  intro i _
  split_ifs
  · rw [norm_mul]
    simp
  · rfl

noncomputable def p09TwiddleSecondCoeff {n : ℕ} [NeZero n]
    (stage : P09MixedRadixStage n) (γ : ℝ) : ℝ :=
  if stage.useTwiddle then 2 + 10 * γ else 0

lemma p09RoundedMixedRadixTwiddleApply_error_le {n : ℕ} [NeZero n]
    (model : P09WilkinsonModel) (stage : P09MixedRadixStage n)
    (x : ZMod n → ℂ) (hεone : model.epsilon ≤ 1) :
    0 ≤ p09TwiddleSecondCoeff stage model.gamma ∧
      p09ComplexNorm2 (fun i ↦
        p09RoundedMixedRadixTwiddleApply model stage x i -
          p09MixedRadixTwiddleApply stage x i) ≤
        (model.epsilon * (if stage.useTwiddle then 3 + 2 * model.gamma else 0) +
          p09TwiddleSecondCoeff stage model.gamma * model.epsilon ^ 2) *
            p09ComplexNorm2 x := by
  by_cases ht : stage.useTwiddle
  · have hγ := model.gamma_nonneg
    refine ⟨by simp [p09TwiddleSecondCoeff, ht]; nlinarith, ?_⟩
    let c := model.epsilon * (3 + 2 * model.gamma) +
      (2 + 10 * model.gamma) * model.epsilon ^ 2
    have hc : 0 ≤ c := by
      dsimp [c]
      exact add_nonneg
        (mul_nonneg (le_of_lt model.epsilon_pos) (by nlinarith))
        (mul_nonneg (by nlinarith) (sq_nonneg _))
    have hp : ∀ i, ‖p09RoundedMixedRadixTwiddleApply model stage x i -
        p09MixedRadixTwiddleApply stage x i‖ ≤ c * ‖x i‖ := by
      intro i
      simpa [p09RoundedMixedRadixTwiddleApply,
        p09MixedRadixTwiddleApply, ht, c] using
        p09RoundedRootMul_error_le model (stage.twiddleExponent i) (x i) hεone
    simpa [p09TwiddleSecondCoeff, ht, c, p09ComplexNorm2_eq_finiteNorm2] using
      p09FiniteNorm2_pointwise_bound _ _ c hc hp
  · refine ⟨by simp [p09TwiddleSecondCoeff, ht], ?_⟩
    simp [p09RoundedMixedRadixTwiddleApply,
      p09MixedRadixTwiddleApply, p09TwiddleSecondCoeff, ht, p09ComplexNorm2,
      p09ComplexNorm2Sq]

lemma p09Alpha_nonneg (q : ℕ) {γ : ℝ} (hγ : 0 ≤ γ) :
    0 ≤ p09Alpha q γ := by
  unfold p09Alpha
  split_ifs <;> positivity

noncomputable def p09StageSecondCoeff {n : ℕ} [NeZero n]
    (stage : P09MixedRadixStage n) (γ : ℝ) : ℝ :=
  let CB := p09BlockSecondCoeff stage γ
  let CT := p09TwiddleSecondCoeff stage γ
  let r := Real.sqrt (stage.radix : ℝ)
  let t := if stage.useTwiddle then 3 + 2 * γ else 0
  let a := r * p09Alpha stage.radix γ
  CT * r + t * a + CB + t * CB + CT * a + CT * CB

lemma p09RoundedMixedRadixStageApply_error_le {n : ℕ} [NeZero n]
    (model : P09WilkinsonModel) (stage : P09MixedRadixStage n)
    (x : ZMod n → ℂ) (hεone : model.epsilon ≤ 1)
    (hexactScaling :
      p09ComplexNorm2 (p09MixedRadixStageApply stage x) =
        Real.sqrt (stage.radix : ℝ) * p09ComplexNorm2 x) :
    0 ≤ p09StageSecondCoeff stage model.gamma ∧
      p09ComplexNorm2 (fun i ↦
        p09RoundedMixedRadixStageApply model stage x i -
          p09MixedRadixStageApply stage x i) ≤
        (model.epsilon * (Real.sqrt (stage.radix : ℝ) *
            (p09Alpha stage.radix model.gamma +
              if stage.useTwiddle then 3 + 2 * model.gamma else 0)) +
          p09StageSecondCoeff stage model.gamma * model.epsilon ^ 2) *
            p09ComplexNorm2 x := by
  let CB := p09BlockSecondCoeff stage model.gamma
  have hblockData := p09RoundedMixedRadixBlockApply_error_le model stage x hεone
  have hCB : 0 ≤ CB := by simpa [CB] using hblockData.1
  have hblock := hblockData.2
  let xhat := p09RoundedMixedRadixBlockApply model stage x
  let xexact := p09MixedRadixBlockApply stage x
  let a := Real.sqrt (stage.radix : ℝ) * p09Alpha stage.radix model.gamma
  let r := Real.sqrt (stage.radix : ℝ)
  let t := if stage.useTwiddle then 3 + 2 * model.gamma else 0
  let bcoeff := model.epsilon * a + CB * model.epsilon ^ 2
  let CT := p09TwiddleSecondCoeff stage model.gamma
  have htwiddleData :=
    p09RoundedMixedRadixTwiddleApply_error_le model stage xhat hεone
  have hCT : 0 ≤ CT := by simpa [CT] using htwiddleData.1
  have htwiddle := htwiddleData.2
  let tcoeff := model.epsilon * t + CT * model.epsilon ^ 2
  let C := CT * r + t * a + CB + t * CB + CT * a + CT * CB
  have hε : 0 ≤ model.epsilon := le_of_lt model.epsilon_pos
  have hγ : 0 ≤ model.gamma := model.gamma_nonneg
  have hr : 0 ≤ r := Real.sqrt_nonneg _
  have halpha : 0 ≤ p09Alpha stage.radix model.gamma :=
    p09Alpha_nonneg _ hγ
  have ha : 0 ≤ a := mul_nonneg hr halpha
  have ht : 0 ≤ t := by
    dsimp [t]
    split <;> positivity
  have hbcoeff : 0 ≤ bcoeff := by
    dsimp [bcoeff]
    exact add_nonneg (mul_nonneg hε ha) (mul_nonneg hCB (sq_nonneg _))
  have htcoeff : 0 ≤ tcoeff := by
    dsimp [tcoeff]
    exact add_nonneg (mul_nonneg hε ht) (mul_nonneg hCT (sq_nonneg _))
  have hC : 0 ≤ C := by
    dsimp [C]
    positivity
  change 0 ≤ C ∧ _
  refine ⟨hC, ?_⟩
  have hblock' : p09ComplexNorm2 (fun i ↦ xhat i - xexact i) ≤
      bcoeff * p09ComplexNorm2 x := by
    simpa [xhat, xexact, bcoeff, a] using hblock
  have hxexact : p09ComplexNorm2 xexact = r * p09ComplexNorm2 x := by
    calc
      p09ComplexNorm2 xexact =
          p09ComplexNorm2 (p09MixedRadixTwiddleApply stage xexact) :=
        (p09MixedRadixTwiddleApply_norm stage xexact).symm
      _ = p09ComplexNorm2 (p09MixedRadixStageApply stage x) := by rfl
      _ = r * p09ComplexNorm2 x := by simpa [r] using hexactScaling
  have hxhat : p09ComplexNorm2 xhat ≤
      (r + bcoeff) * p09ComplexNorm2 x := by
    calc
      p09ComplexNorm2 xhat ≤
          p09ComplexNorm2 (fun i ↦ xhat i - xexact i) +
            p09ComplexNorm2 xexact := by
        have h := p09ComplexNorm2_add_le
          (fun i ↦ xhat i - xexact i) xexact
        simpa only [sub_add_cancel] using h
      _ ≤ bcoeff * p09ComplexNorm2 x + r * p09ComplexNorm2 x :=
        add_le_add hblock' (le_of_eq hxexact)
      _ = (r + bcoeff) * p09ComplexNorm2 x := by ring
  have htwiddle' : p09ComplexNorm2 (fun i ↦
      p09RoundedMixedRadixTwiddleApply model stage xhat i -
        p09MixedRadixTwiddleApply stage xhat i) ≤
      tcoeff * p09ComplexNorm2 xhat := by
    simpa [tcoeff, t] using htwiddle
  have hexactDifference : p09ComplexNorm2 (fun i ↦
      p09MixedRadixTwiddleApply stage xhat i -
        p09MixedRadixTwiddleApply stage xexact i) =
      p09ComplexNorm2 (fun i ↦ xhat i - xexact i) := by
    have hfun : (fun i ↦
        p09MixedRadixTwiddleApply stage xhat i -
          p09MixedRadixTwiddleApply stage xexact i) =
        p09MixedRadixTwiddleApply stage (fun i ↦ xhat i - xexact i) := by
      funext i
      simp only [p09MixedRadixTwiddleApply]
      split_ifs <;> ring
    rw [hfun, p09MixedRadixTwiddleApply_norm]
  have hsplit : (fun i ↦
      p09RoundedMixedRadixStageApply model stage x i -
        p09MixedRadixStageApply stage x i) =
      (fun i ↦
        (p09RoundedMixedRadixTwiddleApply model stage xhat i -
          p09MixedRadixTwiddleApply stage xhat i) +
        (p09MixedRadixTwiddleApply stage xhat i -
          p09MixedRadixTwiddleApply stage xexact i)) := by
    funext i
    simp [p09RoundedMixedRadixStageApply, p09MixedRadixStageApply,
      xhat, xexact]
  rw [hsplit]
  have hraw : p09ComplexNorm2 (fun i ↦
        (p09RoundedMixedRadixTwiddleApply model stage xhat i -
          p09MixedRadixTwiddleApply stage xhat i) +
        (p09MixedRadixTwiddleApply stage xhat i -
          p09MixedRadixTwiddleApply stage xexact i)) ≤
      (tcoeff * (r + bcoeff) + bcoeff) * p09ComplexNorm2 x := by
    calc
      _ ≤ p09ComplexNorm2 (fun i ↦
            p09RoundedMixedRadixTwiddleApply model stage xhat i -
              p09MixedRadixTwiddleApply stage xhat i) +
          p09ComplexNorm2 (fun i ↦
            p09MixedRadixTwiddleApply stage xhat i -
              p09MixedRadixTwiddleApply stage xexact i) :=
        p09ComplexNorm2_add_le _ _
      _ = p09ComplexNorm2 (fun i ↦
            p09RoundedMixedRadixTwiddleApply model stage xhat i -
              p09MixedRadixTwiddleApply stage xhat i) +
          p09ComplexNorm2 (fun i ↦ xhat i - xexact i) := by
        rw [hexactDifference]
      _ ≤ tcoeff * p09ComplexNorm2 xhat +
          bcoeff * p09ComplexNorm2 x := add_le_add htwiddle' hblock'
      _ ≤ tcoeff * ((r + bcoeff) * p09ComplexNorm2 x) +
          bcoeff * p09ComplexNorm2 x :=
        add_le_add (mul_le_mul_of_nonneg_left hxhat htcoeff) le_rfl
      _ = (tcoeff * (r + bcoeff) + bcoeff) * p09ComplexNorm2 x := by ring
  refine le_trans hraw (mul_le_mul_of_nonneg_right ?_ (by
    unfold p09ComplexNorm2
    positivity))
  have he3 : model.epsilon ^ 3 ≤ model.epsilon ^ 2 := by
    nlinarith [mul_self_le_mul_self hε hεone]
  have he4 : model.epsilon ^ 4 ≤ model.epsilon ^ 2 := by
    have he2one : model.epsilon ^ 2 ≤ 1 := by
      nlinarith [mul_self_le_mul_self hε hεone]
    nlinarith [mul_le_mul_of_nonneg_left he2one (sq_nonneg model.epsilon)]
  dsimp [tcoeff, bcoeff, C]
  have htCB : 0 ≤ t * CB := mul_nonneg ht hCB
  have hCTa : 0 ≤ CT * a := mul_nonneg hCT ha
  have hCTCB : 0 ≤ CT * CB := mul_nonneg hCT hCB
  have hlead : r * (p09Alpha stage.radix model.gamma + t) = a + r * t := by
    dsimp [a]
    ring
  rw [hlead, show p09StageSecondCoeff stage model.gamma = C by rfl]
  nlinarith [mul_le_mul_of_nonneg_left he3 htCB,
    mul_le_mul_of_nonneg_left he3 hCTa,
    mul_le_mul_of_nonneg_left he4 hCTCB]

lemma p09MixedRadixBlockApply_sub {n : ℕ} [NeZero n]
    (stage : P09MixedRadixStage n) (x y : ZMod n → ℂ) :
    p09MixedRadixBlockApply stage (fun i ↦ x i - y i) =
      fun i ↦ p09MixedRadixBlockApply stage x i -
        p09MixedRadixBlockApply stage y i := by
  funext i
  simp only [p09MixedRadixBlockApply]
  rw [← Finset.sum_sub_distrib]
  apply Finset.sum_congr rfl
  intro j _
  ring

lemma p09MixedRadixTwiddleApply_sub {n : ℕ} [NeZero n]
    (stage : P09MixedRadixStage n) (x y : ZMod n → ℂ) :
    p09MixedRadixTwiddleApply stage (fun i ↦ x i - y i) =
      fun i ↦ p09MixedRadixTwiddleApply stage x i -
        p09MixedRadixTwiddleApply stage y i := by
  funext i
  simp only [p09MixedRadixTwiddleApply]
  split_ifs <;> ring

lemma p09MixedRadixStageApply_sub {n : ℕ} [NeZero n]
    (stage : P09MixedRadixStage n) (x y : ZMod n → ℂ) :
    p09MixedRadixStageApply stage (fun i ↦ x i - y i) =
      fun i ↦ p09MixedRadixStageApply stage x i -
        p09MixedRadixStageApply stage y i := by
  unfold p09MixedRadixStageApply
  rw [p09MixedRadixBlockApply_sub, p09MixedRadixTwiddleApply_sub]

noncomputable def p09StageScale {n : ℕ} [NeZero n]
    (stage : P09MixedRadixStage n) : ℝ :=
  Real.sqrt (stage.radix : ℝ)

noncomputable def p09StageLead {n : ℕ} [NeZero n]
    (stage : P09MixedRadixStage n) (γ : ℝ) : ℝ :=
  p09Alpha stage.radix γ +
    if stage.useTwiddle then 3 + 2 * γ else 0

noncomputable def p09ExactStageListApply {n : ℕ} [NeZero n]
    (stages : List (P09MixedRadixStage n)) (x : ZMod n → ℂ) : ZMod n → ℂ :=
  stages.foldl (fun state stage ↦ p09MixedRadixStageApply stage state) x

noncomputable def p09RoundedStageListApply {n : ℕ} [NeZero n]
    (model : P09WilkinsonModel) (stages : List (P09MixedRadixStage n))
    (x : ZMod n → ℂ) : ZMod n → ℂ :=
  stages.foldl
    (fun state stage ↦ p09RoundedMixedRadixStageApply model stage state) x

lemma p09ExactStageListApply_sub {n : ℕ} [NeZero n]
    (stages : List (P09MixedRadixStage n)) (x y : ZMod n → ℂ) :
    p09ExactStageListApply stages (fun i ↦ x i - y i) =
      fun i ↦ p09ExactStageListApply stages x i -
        p09ExactStageListApply stages y i := by
  induction stages generalizing x y with
  | nil => rfl
  | cons stage stages ih =>
      simp only [p09ExactStageListApply, List.foldl_cons]
      rw [p09MixedRadixStageApply_sub]
      exact ih _ _

lemma p09ExactStageListApply_norm
    {n : ℕ} [NeZero n] (stages : List (P09MixedRadixStage n))
    (hscale : ∀ stage ∈ stages, ∀ x : ZMod n → ℂ,
      p09ComplexNorm2 (p09MixedRadixStageApply stage x) =
        p09StageScale stage * p09ComplexNorm2 x)
    (x : ZMod n → ℂ) :
    p09ComplexNorm2 (p09ExactStageListApply stages x) =
      (stages.map p09StageScale).prod * p09ComplexNorm2 x := by
  induction stages generalizing x with
  | nil => simp [p09ExactStageListApply]
  | cons stage stages ih =>
      change p09ComplexNorm2
          (p09ExactStageListApply stages (p09MixedRadixStageApply stage x)) =
        p09StageScale stage * (stages.map p09StageScale).prod *
          p09ComplexNorm2 x
      rw [ih (fun s hs ↦ hscale s (by simp [hs]))]
      rw [hscale stage (by simp)]
      ring

noncomputable def p09StageListSecondCoeff {n : ℕ} [NeZero n]
    (γ : ℝ) : List (P09MixedRadixStage n) → ℝ
  | [] => 0
  | stage :: stages =>
      let CR := p09StageListSecondCoeff γ stages
      let CS := p09StageSecondCoeff stage γ
      let scaleR := (stages.map p09StageScale).prod
      let leadR := (stages.map (fun s ↦ p09StageLead s γ)).sum
      let scaleS := p09StageScale stage
      let leadS := p09StageLead stage γ
      CR * scaleS + scaleR * CS + scaleR * leadR * scaleS * leadS +
        scaleR * leadR * CS + CR * scaleS * leadS + CR * CS

lemma p09RoundedStageListApply_error_le
    {n : ℕ} [NeZero n] (model : P09WilkinsonModel)
    (stages : List (P09MixedRadixStage n))
    (hscale : ∀ stage ∈ stages, ∀ x : ZMod n → ℂ,
      p09ComplexNorm2 (p09MixedRadixStageApply stage x) =
        p09StageScale stage * p09ComplexNorm2 x)
    (x : ZMod n → ℂ) (hεone : model.epsilon ≤ 1) :
    0 ≤ p09StageListSecondCoeff model.gamma stages ∧
      p09ComplexNorm2 (fun i ↦
        p09RoundedStageListApply model stages x i -
          p09ExactStageListApply stages x i) ≤
        (model.epsilon * ((stages.map p09StageScale).prod *
            (stages.map (fun s ↦ p09StageLead s model.gamma)).sum) +
          p09StageListSecondCoeff model.gamma stages * model.epsilon ^ 2) *
            p09ComplexNorm2 x := by
  induction stages generalizing x with
  | nil =>
      refine ⟨by simp [p09StageListSecondCoeff], ?_⟩
      simp [p09RoundedStageListApply, p09ExactStageListApply,
        p09StageListSecondCoeff, p09ComplexNorm2, p09ComplexNorm2Sq]
  | cons stage stages ih =>
      have hsStage : ∀ z : ZMod n → ℂ,
          p09ComplexNorm2 (p09MixedRadixStageApply stage z) =
            p09StageScale stage * p09ComplexNorm2 z :=
        hscale stage (by simp)
      let xhat := p09RoundedMixedRadixStageApply model stage x
      let xexact := p09MixedRadixStageApply stage x
      let CS := p09StageSecondCoeff stage model.gamma
      have hstageData :=
        p09RoundedMixedRadixStageApply_error_le model stage x hεone
          (by simpa [p09StageScale] using hsStage x)
      have hCS : 0 ≤ CS := by simpa [CS] using hstageData.1
      have hstage := hstageData.2
      let CR := p09StageListSecondCoeff model.gamma stages
      have hrestData := ih
        (fun s hs ↦ hscale s (by simp [hs])) xhat
      have hCR : 0 ≤ CR := by simpa [CR] using hrestData.1
      have hrest := hrestData.2
      let scaleR := (stages.map p09StageScale).prod
      let leadR := (stages.map (fun s ↦ p09StageLead s model.gamma)).sum
      let scaleS := p09StageScale stage
      let leadS := p09StageLead stage model.gamma
      let scoeff := model.epsilon * (scaleS * leadS) +
        CS * model.epsilon ^ 2
      let rcoeff := model.epsilon * (scaleR * leadR) +
        CR * model.epsilon ^ 2
      let C := CR * scaleS + scaleR * CS + scaleR * leadR * scaleS * leadS +
        scaleR * leadR * CS + CR * scaleS * leadS + CR * CS
      have hε : 0 ≤ model.epsilon := le_of_lt model.epsilon_pos
      have hscaleS : 0 ≤ scaleS := Real.sqrt_nonneg _
      have hleadS : 0 ≤ leadS := by
        dsimp [leadS, p09StageLead]
        have ha := p09Alpha_nonneg stage.radix model.gamma_nonneg
        split
        · exact add_nonneg ha (by nlinarith [model.gamma_nonneg])
        · simpa using ha
      have hscaleR : 0 ≤ scaleR := by
        dsimp [scaleR]
        apply List.prod_nonneg
        intro a ha
        rcases List.mem_map.mp ha with ⟨s, hs, rfl⟩
        exact Real.sqrt_nonneg _
      have hleadR : 0 ≤ leadR := by
        dsimp [leadR]
        apply List.sum_nonneg
        intro a ha
        rcases List.mem_map.mp ha with ⟨s, hs, rfl⟩
        dsimp [p09StageLead]
        have hα := p09Alpha_nonneg s.radix model.gamma_nonneg
        split
        · exact add_nonneg hα (by nlinarith [model.gamma_nonneg])
        · simpa using hα
      have hscoeff : 0 ≤ scoeff := by
        dsimp [scoeff]
        positivity
      have hrcoeff : 0 ≤ rcoeff := by
        dsimp [rcoeff]
        positivity
      have hC : 0 ≤ C := by
        dsimp [C]
        positivity
      change 0 ≤ C ∧ _
      refine ⟨hC, ?_⟩
      have hstage' : p09ComplexNorm2 (fun i ↦ xhat i - xexact i) ≤
          scoeff * p09ComplexNorm2 x := by
        simpa [xhat, xexact, scoeff, scaleS, leadS,
          p09StageScale, p09StageLead] using hstage
      have hxhat : p09ComplexNorm2 xhat ≤
          (scaleS + scoeff) * p09ComplexNorm2 x := by
        calc
          p09ComplexNorm2 xhat ≤
              p09ComplexNorm2 (fun i ↦ xhat i - xexact i) +
                p09ComplexNorm2 xexact := by
            have h := p09ComplexNorm2_add_le
              (fun i ↦ xhat i - xexact i) xexact
            simpa only [sub_add_cancel] using h
          _ ≤ scoeff * p09ComplexNorm2 x +
              scaleS * p09ComplexNorm2 x := by
            exact add_le_add hstage' (le_of_eq (by
              simpa [xexact, scaleS] using hsStage x))
          _ = (scaleS + scoeff) * p09ComplexNorm2 x := by ring
      have hrest' : p09ComplexNorm2 (fun i ↦
          p09RoundedStageListApply model stages xhat i -
            p09ExactStageListApply stages xhat i) ≤
          rcoeff * p09ComplexNorm2 xhat := by
        simpa [rcoeff, scaleR, leadR] using hrest
      have hprop : p09ComplexNorm2 (fun i ↦
          p09ExactStageListApply stages xhat i -
            p09ExactStageListApply stages xexact i) =
          scaleR * p09ComplexNorm2 (fun i ↦ xhat i - xexact i) := by
        rw [← p09ExactStageListApply_sub]
        exact p09ExactStageListApply_norm stages
          (fun s hs ↦ hscale s (by simp [hs])) _
      have hsplit : (fun i ↦
          p09RoundedStageListApply model (stage :: stages) x i -
            p09ExactStageListApply (stage :: stages) x i) =
          (fun i ↦
            (p09RoundedStageListApply model stages xhat i -
              p09ExactStageListApply stages xhat i) +
            (p09ExactStageListApply stages xhat i -
              p09ExactStageListApply stages xexact i)) := by
        funext i
        simp [p09RoundedStageListApply, p09ExactStageListApply, xhat, xexact]
      rw [hsplit]
      have hraw : p09ComplexNorm2 (fun i ↦
            (p09RoundedStageListApply model stages xhat i -
              p09ExactStageListApply stages xhat i) +
            (p09ExactStageListApply stages xhat i -
              p09ExactStageListApply stages xexact i)) ≤
          (rcoeff * (scaleS + scoeff) + scaleR * scoeff) *
            p09ComplexNorm2 x := by
        calc
          _ ≤ p09ComplexNorm2 (fun i ↦
                p09RoundedStageListApply model stages xhat i -
                  p09ExactStageListApply stages xhat i) +
              p09ComplexNorm2 (fun i ↦
                p09ExactStageListApply stages xhat i -
                  p09ExactStageListApply stages xexact i) :=
            p09ComplexNorm2_add_le _ _
          _ = p09ComplexNorm2 (fun i ↦
                p09RoundedStageListApply model stages xhat i -
                  p09ExactStageListApply stages xhat i) +
              scaleR * p09ComplexNorm2 (fun i ↦ xhat i - xexact i) := by
            rw [hprop]
          _ ≤ rcoeff * p09ComplexNorm2 xhat +
              scaleR * (scoeff * p09ComplexNorm2 x) :=
            add_le_add hrest' (mul_le_mul_of_nonneg_left hstage' hscaleR)
          _ ≤ rcoeff * ((scaleS + scoeff) * p09ComplexNorm2 x) +
              scaleR * (scoeff * p09ComplexNorm2 x) :=
            add_le_add (mul_le_mul_of_nonneg_left hxhat hrcoeff) le_rfl
          _ = (rcoeff * (scaleS + scoeff) + scaleR * scoeff) *
              p09ComplexNorm2 x := by ring
      refine le_trans hraw (mul_le_mul_of_nonneg_right ?_ (by
        unfold p09ComplexNorm2
        positivity))
      have he3 : model.epsilon ^ 3 ≤ model.epsilon ^ 2 := by
        nlinarith [mul_self_le_mul_self hε hεone]
      have he4 : model.epsilon ^ 4 ≤ model.epsilon ^ 2 := by
        have he2one : model.epsilon ^ 2 ≤ 1 := by
          nlinarith [mul_self_le_mul_self hε hεone]
        nlinarith [mul_le_mul_of_nonneg_left he2one (sq_nonneg model.epsilon)]
      simp only [List.map_cons, List.prod_cons, List.sum_cons]
      dsimp [rcoeff, scoeff, C]
      have hRLSL : 0 ≤ scaleR * leadR * scaleS * leadS := by positivity
      have hRLCS : 0 ≤ scaleR * leadR * CS := by positivity
      have hCRSL : 0 ≤ CR * scaleS * leadS := by positivity
      have hCRCS : 0 ≤ CR * CS := by positivity
      rw [show p09StageListSecondCoeff model.gamma (stage :: stages) =
        CR * scaleS + scaleR * CS + scaleR * leadR * scaleS * leadS +
          scaleR * leadR * CS + CR * scaleS * leadS + CR * CS by rfl]
      nlinarith [mul_le_mul_of_nonneg_left he3 hRLCS,
        mul_le_mul_of_nonneg_left he3 hCRSL,
        mul_le_mul_of_nonneg_left he4 hCRCS]

lemma p09_fin_twiddle_sum (M : ℕ) (hM : 0 < M) (t : ℝ) :
    (∑ i : Fin M, if i.val + 1 < M then t else 0) =
      ((M : ℝ) - 1) * t := by
  obtain ⟨k, rfl⟩ := Nat.exists_eq_succ_of_ne_zero (Nat.ne_of_gt hM)
  rw [Fin.sum_univ_castSucc]
  have hall : ∀ i : Fin k, i.val + 1 < k + 1 := fun i ↦ by omega
  simp only [hall, if_true, Fin.val_last, lt_self_iff_false, if_false, add_zero]
  simp

lemma p09MixedRadixPlan_scale_product {n : ℕ} [NeZero n]
    (plan : P09MixedRadixFftPlan n) :
    ((List.ofFn plan.stage).map p09StageScale).prod = Real.sqrt (n : ℝ) := by
  rw [List.map_ofFn, List.prod_ofFn]
  simp only [Function.comp_apply, p09StageScale]
  rw [← Real.sqrt_prod (Finset.univ : Finset (Fin plan.stageCount))
    (fun i _ ↦ Nat.cast_nonneg (plan.stage i).radix)]
  congr 1
  norm_cast
  exact plan.order_factorization

lemma p09MixedRadixPlan_lead_sum {n : ℕ} [NeZero n]
    (plan : P09MixedRadixFftPlan n) (γ : ℝ) :
    ((List.ofFn plan.stage).map (fun s ↦ p09StageLead s γ)).sum =
      p09K plan γ := by
  rw [List.map_ofFn, List.sum_ofFn]
  simp only [Function.comp_apply, p09StageLead]
  unfold p09K
  rw [Finset.sum_add_distrib]
  congr 1
  calc
    (∑ i : Fin plan.stageCount,
        if (plan.stage i).useTwiddle then 3 + 2 * γ else 0) =
        ∑ i : Fin plan.stageCount,
          if i.val + 1 < plan.stageCount then 3 + 2 * γ else 0 := by
      apply Finset.sum_congr rfl
      intro i _
      rw [plan.twiddle_pattern]
      simp
    _ = ((plan.stageCount : ℝ) - 1) * (3 + 2 * γ) :=
      p09_fin_twiddle_sum plan.stageCount plan.stageCount_pos _

lemma p09ComplexNorm2_permute {n : ℕ} [NeZero n]
    (e : ZMod n ≃ ZMod n) (x : ZMod n → ℂ) :
    p09ComplexNorm2 (p09Permute e x) = p09ComplexNorm2 x := by
  rw [p09ComplexNorm2_eq_finiteNorm2]
  exact p09FiniteNorm2_equiv e x

noncomputable def p09FftSecondCoeff {n : ℕ} [NeZero n]
    (plan : P09MixedRadixFftPlan n) (γ : ℝ) : ℝ :=
  p09StageListSecondCoeff γ (List.ofFn plan.stage)

lemma p09RoundedFftApply_error_le {n : ℕ} [NeZero n]
    (plan : P09MixedRadixFftPlan n) (model : P09WilkinsonModel)
    (x : ZMod n → ℂ) (hεone : model.epsilon ≤ 1) :
    0 ≤ p09FftSecondCoeff plan model.gamma ∧
      p09ComplexNorm2 (fun i ↦
        p09RoundedFftApply plan model x i - p09FourierTransform x i) ≤
        (model.epsilon * (Real.sqrt (n : ℝ) * p09K plan model.gamma) +
          p09FftSecondCoeff plan model.gamma * model.epsilon ^ 2) *
            p09ComplexNorm2 x := by
  let stages := List.ofFn plan.stage
  have hdata := p09RoundedStageListApply_error_le model stages
    (fun stage hstage z ↦ by
      rw [List.mem_ofFn] at hstage
      obtain ⟨i, rfl⟩ := hstage
      simpa [p09StageScale] using plan.stage_norm_scaling i z)
    x hεone
  have hC : 0 ≤ p09FftSecondCoeff plan model.gamma := by
    simpa [p09FftSecondCoeff, stages] using hdata.1
  have hbound := hdata.2
  refine ⟨hC, ?_⟩
  have hrounded : p09RoundedFftApply plan model x =
      p09Permute plan.finalPermutation (p09RoundedStageListApply model stages x) := by
    rfl
  have hexact : p09FourierTransform x =
      p09Permute plan.finalPermutation (p09ExactStageListApply stages x) := by
    symm
    exact plan.exact_factorization x
  have herr : (fun i ↦
      p09RoundedFftApply plan model x i - p09FourierTransform x i) =
      p09Permute plan.finalPermutation (fun i ↦
        p09RoundedStageListApply model stages x i -
          p09ExactStageListApply stages x i) := by
    funext i
    rw [hrounded, hexact]
    rfl
  rw [herr, p09ComplexNorm2_permute]
  rw [p09MixedRadixPlan_scale_product plan,
    p09MixedRadixPlan_lead_sum plan model.gamma] at hbound
  simpa [p09FftSecondCoeff, stages] using hbound

lemma p09FourierTransform_norm {n : ℕ} [NeZero n]
    (plan : P09MixedRadixFftPlan n) (x : ZMod n → ℂ) :
    p09ComplexNorm2 (p09FourierTransform x) =
      Real.sqrt (n : ℝ) * p09ComplexNorm2 x := by
  let stages := List.ofFn plan.stage
  have hscale : ∀ stage ∈ stages, ∀ z : ZMod n → ℂ,
      p09ComplexNorm2 (p09MixedRadixStageApply stage z) =
        p09StageScale stage * p09ComplexNorm2 z := by
    intro stage hstage z
    rw [List.mem_ofFn] at hstage
    obtain ⟨i, rfl⟩ := hstage
    simpa [p09StageScale] using plan.stage_norm_scaling i z
  calc
    p09ComplexNorm2 (p09FourierTransform x) =
        p09ComplexNorm2
          (p09Permute plan.finalPermutation
            (p09ExactStageListApply stages x)) := by
      congr 1
      symm
      exact plan.exact_factorization x
    _ = p09ComplexNorm2 (p09ExactStageListApply stages x) :=
      p09ComplexNorm2_permute plan.finalPermutation _
    _ = (stages.map p09StageScale).prod * p09ComplexNorm2 x :=
      p09ExactStageListApply_norm stages hscale x
    _ = Real.sqrt (n : ℝ) * p09ComplexNorm2 x := by
      rw [p09MixedRadixPlan_scale_product]

lemma p09K_nonneg {n : ℕ} [NeZero n]
    (plan : P09MixedRadixFftPlan n) {γ : ℝ} (hγ : 0 ≤ γ) :
    0 ≤ p09K plan γ := by
  rw [← p09MixedRadixPlan_lead_sum plan γ]
  apply List.sum_nonneg
  intro a ha
  rcases List.mem_map.mp ha with ⟨stage, hstage, rfl⟩
  unfold p09StageLead
  have hα := p09Alpha_nonneg stage.radix hγ
  split
  · exact add_nonneg hα (by nlinarith)
  · simpa using hα

lemma p09FiniteNorm2_prod_bound {β κ : Type*} [Fintype β] [Fintype κ]
    (err x : β → κ → ℂ) (c : ℝ) (hc : 0 ≤ c)
    (h : ∀ b, p09FiniteNorm2 (err b) ≤ c * p09FiniteNorm2 (x b)) :
    p09FiniteNorm2 (fun p : β × κ ↦ err p.1 p.2) ≤
      c * p09FiniteNorm2 (fun p : β × κ ↦ x p.1 p.2) := by
  have hs : (∑ p : β × κ, ‖err p.1 p.2‖ ^ 2) ≤
      c ^ 2 * ∑ p : β × κ, ‖x p.1 p.2‖ ^ 2 := by
    rw [Fintype.sum_prod_type, Fintype.sum_prod_type, Finset.mul_sum]
    apply Finset.sum_le_sum
    intro b hb
    have hleft : 0 ≤ ∑ k : κ, ‖err b k‖ ^ 2 :=
      Finset.sum_nonneg fun _ _ ↦ sq_nonneg _
    have hright : 0 ≤ ∑ k : κ, ‖x b k‖ ^ 2 :=
      Finset.sum_nonneg fun _ _ ↦ sq_nonneg _
    have hsquare := (sq_le_sq₀ (Real.sqrt_nonneg _)
      (mul_nonneg hc (Real.sqrt_nonneg _))).2 (h b)
    simpa [p09FiniteNorm2, Real.sq_sqrt hleft,
      Real.sq_sqrt hright, mul_pow] using hsquare
  have he : 0 ≤ ∑ p : β × κ, ‖err p.1 p.2‖ ^ 2 :=
    Finset.sum_nonneg fun _ _ ↦ sq_nonneg _
  have hx : 0 ≤ ∑ p : β × κ, ‖x p.1 p.2‖ ^ 2 :=
    Finset.sum_nonneg fun _ _ ↦ sq_nonneg _
  unfold p09FiniteNorm2
  rw [← sq_le_sq₀ (Real.sqrt_nonneg _)
    (mul_nonneg hc (Real.sqrt_nonneg _)), Real.sq_sqrt he,
    mul_pow, Real.sq_sqrt hx]
  exact hs

lemma p09FiniteNorm2_prod_bound' {β κ : Type*} [Fintype β] [Fintype κ]
    (err x : β × κ → ℂ) (c : ℝ) (hc : 0 ≤ c)
    (h : ∀ b, p09FiniteNorm2 (fun k ↦ err (b, k)) ≤
      c * p09FiniteNorm2 (fun k ↦ x (b, k))) :
    p09FiniteNorm2 err ≤ c * p09FiniteNorm2 x := by
  exact p09FiniteNorm2_prod_bound
    (fun b k ↦ err (b, k)) (fun b k ↦ x (b, k)) c hc h

lemma p09FiniteNorm2_prod_scale {β κ : Type*} [Fintype β] [Fintype κ]
    (y x : β × κ → ℂ) (s : ℝ) (hs : 0 ≤ s)
    (h : ∀ b, p09FiniteNorm2 (fun k ↦ y (b, k)) =
      s * p09FiniteNorm2 (fun k ↦ x (b, k))) :
    p09FiniteNorm2 y = s * p09FiniteNorm2 x := by
  have hsum : (∑ p : β × κ, ‖y p‖ ^ 2) =
      s ^ 2 * ∑ p : β × κ, ‖x p‖ ^ 2 := by
    rw [Fintype.sum_prod_type, Fintype.sum_prod_type, Finset.mul_sum]
    apply Finset.sum_congr rfl
    intro b hb
    have hy : 0 ≤ ∑ k : κ, ‖y (b, k)‖ ^ 2 :=
      Finset.sum_nonneg fun _ _ ↦ sq_nonneg _
    have hx : 0 ≤ ∑ k : κ, ‖x (b, k)‖ ^ 2 :=
      Finset.sum_nonneg fun _ _ ↦ sq_nonneg _
    have hb' := congrArg (fun z : ℝ ↦ z ^ 2) (h b)
    simpa [p09FiniteNorm2, Real.sq_sqrt hy, Real.sq_sqrt hx,
      mul_pow] using hb'
  have hxsum : 0 ≤ ∑ p : β × κ, ‖x p‖ ^ 2 :=
    Finset.sum_nonneg fun _ _ ↦ sq_nonneg _
  unfold p09FiniteNorm2
  rw [hsum, Real.sqrt_mul (sq_nonneg s), Real.sqrt_sq hs]

lemma p09MultiNorm2_eq_finiteNorm2 {m : ℕ}
    {axis : Fin m → P09FftAxis} (x : P09MultiArray axis) :
    p09MultiNorm2 x = p09FiniteNorm2 x := by
  rw [p09FiniteNorm2_eq_euclidean]
  rfl

abbrev P09AxisRestIndex {m : ℕ} (axis : Fin m → P09FftAxis)
    (i : Fin m) :=
  (j : {j : Fin m // j ≠ i}) → ZMod (axis j).order

noncomputable instance p09AxisRestIndexFintype {m : ℕ}
    (axis : Fin m → P09FftAxis) (i : Fin m) :
    Fintype (P09AxisRestIndex axis i) := by
  letI (j : {j : Fin m // j ≠ i}) : NeZero (axis j).order :=
    ⟨Nat.ne_of_gt (axis j).order_pos⟩
  infer_instance

noncomputable def p09AxisSplitEquiv {m : ℕ}
    (axis : Fin m → P09FftAxis) (i : Fin m) :
    P09MultiIndex axis ≃ P09AxisRestIndex axis i × ZMod (axis i).order :=
  (Equiv.piSplitAt i (fun j ↦ ZMod (axis j).order)).trans
    (Equiv.prodComm _ _)

lemma p09AxisSplitEquiv_update {m : ℕ}
    (axis : Fin m → P09FftAxis) (i : Fin m)
    (rest : P09AxisRestIndex axis i)
    (k l : ZMod (axis i).order) :
    Function.update ((p09AxisSplitEquiv axis i).symm (rest, k)) i l =
      (p09AxisSplitEquiv axis i).symm (rest, l) := by
  funext j
  by_cases hji : j = i
  · subst j
    simp [p09AxisSplitEquiv, Equiv.piSplitAt]
  · simp [p09AxisSplitEquiv, Equiv.piSplitAt, hji]

lemma p09AxisSplitEquiv_symm_apply {m : ℕ}
    (axis : Fin m → P09FftAxis) (i : Fin m)
    (rest : P09AxisRestIndex axis i)
    (k : ZMod (axis i).order) :
    (p09AxisSplitEquiv axis i).symm (rest, k) i = k := by
  simp [p09AxisSplitEquiv, Equiv.piSplitAt]

lemma p09RoundedCoordinateTransform_split {m : ℕ}
    (axis : Fin m → P09FftAxis) (i : Fin m)
    (model : P09WilkinsonModel) (x : P09MultiArray axis)
    (rest : P09AxisRestIndex axis i)
    (k : ZMod (axis i).order) :
    p09RoundedCoordinateTransform axis i model x
        ((p09AxisSplitEquiv axis i).symm (rest, k)) =
      p09RoundedFftApply (axis i).plan model
        (fun j ↦ x ((p09AxisSplitEquiv axis i).symm (rest, j))) k := by
  simp only [p09RoundedCoordinateTransform]
  rw [p09AxisSplitEquiv_symm_apply]
  congr 2
  funext j
  rw [p09AxisSplitEquiv_update]

lemma p09CoordinateTransform_split {m : ℕ}
    (axis : Fin m → P09FftAxis) (i : Fin m)
    (x : P09MultiArray axis)
    (rest : P09AxisRestIndex axis i)
    (k : ZMod (axis i).order) :
    p09CoordinateTransform axis i x
        ((p09AxisSplitEquiv axis i).symm (rest, k)) =
      p09FourierTransform
        (fun j ↦ x ((p09AxisSplitEquiv axis i).symm (rest, j))) k := by
  simp only [p09CoordinateTransform, p09FourierTransform]
  rw [p09AxisSplitEquiv_symm_apply]
  apply Finset.sum_congr rfl
  intro j hj
  rw [p09AxisSplitEquiv_update]

noncomputable def p09CoordinateSlice {m : ℕ}
    (axis : Fin m → P09FftAxis) (i : Fin m) (x : P09MultiArray axis)
    (rest : P09AxisRestIndex axis i) :
    ZMod (axis i).order → ℂ :=
  fun k ↦ x ((p09AxisSplitEquiv axis i).symm (rest, k))

noncomputable def p09CoordinateSliceError {m : ℕ}
    (axis : Fin m → P09FftAxis) (i : Fin m)
    (model : P09WilkinsonModel) (x : P09MultiArray axis)
    (rest : P09AxisRestIndex axis i) :
    ZMod (axis i).order → ℂ :=
  fun k ↦
    p09RoundedFftApply (axis i).plan model
        (p09CoordinateSlice axis i x rest) k -
      p09FourierTransform (p09CoordinateSlice axis i x rest) k

lemma p09CoordinateError_reindex {m : ℕ}
    (axis : Fin m → P09FftAxis) (i : Fin m)
    (model : P09WilkinsonModel) (x : P09MultiArray axis) :
    (fun p : P09AxisRestIndex axis i × ZMod (axis i).order ↦
      p09RoundedCoordinateTransform axis i model x
          ((p09AxisSplitEquiv axis i).symm p) -
        p09CoordinateTransform axis i x
          ((p09AxisSplitEquiv axis i).symm p)) =
      (fun p ↦ p09CoordinateSliceError axis i model x p.1 p.2) := by
  funext p
  rcases p with ⟨rest, k⟩
  rw [p09RoundedCoordinateTransform_split, p09CoordinateTransform_split]
  rfl

lemma p09CoordinateTransform_reindex {m : ℕ}
    (axis : Fin m → P09FftAxis) (i : Fin m)
    (x : P09MultiArray axis) :
    (fun p : P09AxisRestIndex axis i × ZMod (axis i).order ↦
      p09CoordinateTransform axis i x
        ((p09AxisSplitEquiv axis i).symm p)) =
      (fun p ↦ p09FourierTransform
        (p09CoordinateSlice axis i x p.1) p.2) := by
  funext p
  rcases p with ⟨rest, k⟩
  rw [p09CoordinateTransform_split]
  rfl

lemma p09MultiNorm2_reindex {m : ℕ} {axis : Fin m → P09FftAxis}
    {κ : Type*} [Fintype κ] (e : κ ≃ P09MultiIndex axis)
    (x : P09MultiArray axis) :
    p09MultiNorm2 x = p09FiniteNorm2 (fun k ↦ x (e k)) := by
  rw [p09MultiNorm2_eq_finiteNorm2]
  exact (p09FiniteNorm2_equiv e x).symm

lemma p09FftSecondCoeff_nonneg {n : ℕ} [NeZero n]
    (plan : P09MixedRadixFftPlan n) {γ : ℝ} (hγ : 0 ≤ γ) :
    0 ≤ p09FftSecondCoeff plan γ := by
  let ε : P09PositiveEpsilon := ⟨1, zero_lt_one⟩
  let model := p09ExactWilkinsonModel ε γ hγ
  have h := (p09RoundedFftApply_error_le plan model (fun _ ↦ 0)
    (by change (1 : ℝ) ≤ 1; norm_num)).1
  simpa [model, p09ExactWilkinsonModel] using h

lemma p09CoordinateSliceError_le {m : ℕ}
    (axis : Fin m → P09FftAxis) (i : Fin m)
    (model : P09WilkinsonModel) (x : P09MultiArray axis)
    (rest : P09AxisRestIndex axis i)
    (hεone : model.epsilon ≤ 1) :
    p09FiniteNorm2 (p09CoordinateSliceError axis i model x rest) ≤
      (model.epsilon * (Real.sqrt ((axis i).order : ℝ) *
          p09AxisK (axis i) model.gamma) +
        p09FftSecondCoeff (axis i).plan model.gamma * model.epsilon ^ 2) *
          p09FiniteNorm2 (p09CoordinateSlice axis i x rest) := by
  have hfft := (p09RoundedFftApply_error_le (axis i).plan model
    (p09CoordinateSlice axis i x rest) hεone).2
  simpa [p09CoordinateSliceError, p09AxisK,
    p09ComplexNorm2_eq_finiteNorm2] using hfft

lemma p09CoordinateTransform_norm {m : ℕ}
    (axis : Fin m → P09FftAxis) (i : Fin m)
    (x : P09MultiArray axis) :
    p09MultiNorm2 (p09CoordinateTransform axis i x) =
      Real.sqrt ((axis i).order : ℝ) * p09MultiNorm2 x := by
  let s := Real.sqrt ((axis i).order : ℝ)
  have hs : 0 ≤ s := Real.sqrt_nonneg _
  have hfiber : ∀ rest,
      p09FiniteNorm2 (fun k ↦ p09FourierTransform
          (p09CoordinateSlice axis i x rest) k) =
        s * p09FiniteNorm2 (p09CoordinateSlice axis i x rest) := by
    intro rest
    simpa [s, p09ComplexNorm2_eq_finiteNorm2] using
      p09FourierTransform_norm (axis i).plan
        (p09CoordinateSlice axis i x rest)
  calc
    p09MultiNorm2 (p09CoordinateTransform axis i x) =
        p09FiniteNorm2 (fun p : P09AxisRestIndex axis i ×
            ZMod (axis i).order ↦
          p09FourierTransform (p09CoordinateSlice axis i x p.1) p.2) := by
      rw [p09MultiNorm2_reindex (p09AxisSplitEquiv axis i).symm]
      rw [p09CoordinateTransform_reindex]
    _ = s * p09FiniteNorm2 (fun p : P09AxisRestIndex axis i ×
          ZMod (axis i).order ↦ p09CoordinateSlice axis i x p.1 p.2) := by
      exact p09FiniteNorm2_prod_scale
        (fun p ↦ p09FourierTransform
          (p09CoordinateSlice axis i x p.1) p.2)
        (fun p ↦ p09CoordinateSlice axis i x p.1 p.2)
        s hs hfiber
    _ = s * p09FiniteNorm2 x := by
      congr 1
      exact p09FiniteNorm2_equiv (p09AxisSplitEquiv axis i).symm x
    _ = Real.sqrt ((axis i).order : ℝ) * p09MultiNorm2 x := by
      rw [p09MultiNorm2_eq_finiteNorm2]

lemma p09CoordinateError_norm_of_slices {m : ℕ}
    (axis : Fin m → P09FftAxis) (i : Fin m)
    (model : P09WilkinsonModel) (x : P09MultiArray axis)
    (c : ℝ) (hc : 0 ≤ c)
    (hfiber : ∀ rest,
      p09FiniteNorm2 (p09CoordinateSliceError axis i model x rest) ≤
        c * p09FiniteNorm2 (p09CoordinateSlice axis i x rest)) :
    p09MultiNorm2 (fun index ↦
        p09RoundedCoordinateTransform axis i model x index -
          p09CoordinateTransform axis i x index) ≤
      c * p09MultiNorm2 x := by
  calc
    p09MultiNorm2 (fun index ↦
        p09RoundedCoordinateTransform axis i model x index -
          p09CoordinateTransform axis i x index) =
        p09FiniteNorm2 (fun p : P09AxisRestIndex axis i ×
            ZMod (axis i).order ↦
          p09CoordinateSliceError axis i model x p.1 p.2) := by
      rw [p09MultiNorm2_reindex (p09AxisSplitEquiv axis i).symm]
      rw [p09CoordinateError_reindex]
    _ ≤ c * p09FiniteNorm2 (fun p : P09AxisRestIndex axis i ×
          ZMod (axis i).order ↦
          p09CoordinateSlice axis i x p.1 p.2) := by
      exact p09FiniteNorm2_prod_bound'
        (β := P09AxisRestIndex axis i)
        (κ := ZMod (axis i).order)
        (err := fun p ↦ p09CoordinateSliceError axis i model x p.1 p.2)
        (x := fun p ↦ p09CoordinateSlice axis i x p.1 p.2)
        c hc hfiber
    _ = c * p09FiniteNorm2 x := by
      congr 1
      exact p09FiniteNorm2_equiv (p09AxisSplitEquiv axis i).symm x
    _ = c * p09MultiNorm2 x := by rw [p09MultiNorm2_eq_finiteNorm2]

lemma p09RoundedCoordinateTransform_error_le {m : ℕ}
    (axis : Fin m → P09FftAxis) (i : Fin m)
    (model : P09WilkinsonModel) (x : P09MultiArray axis)
    (hεone : model.epsilon ≤ 1) :
    0 ≤ p09FftSecondCoeff (axis i).plan model.gamma ∧
      p09MultiNorm2 (fun index ↦
        p09RoundedCoordinateTransform axis i model x index -
          p09CoordinateTransform axis i x index) ≤
        (model.epsilon * (Real.sqrt ((axis i).order : ℝ) *
            p09AxisK (axis i) model.gamma) +
          p09FftSecondCoeff (axis i).plan model.gamma * model.epsilon ^ 2) *
            p09MultiNorm2 x := by
  let C := p09FftSecondCoeff (axis i).plan model.gamma
  let c := model.epsilon * (Real.sqrt ((axis i).order : ℝ) *
      p09AxisK (axis i) model.gamma) + C * model.epsilon ^ 2
  have hC : 0 ≤ C := by
    simpa [C] using p09FftSecondCoeff_nonneg (axis i).plan model.gamma_nonneg
  have hc : 0 ≤ c := by
    dsimp [c]
    exact add_nonneg
      (mul_nonneg (le_of_lt model.epsilon_pos)
        (mul_nonneg (Real.sqrt_nonneg _)
          (by simpa [p09AxisK] using
            p09K_nonneg (axis i).plan model.gamma_nonneg)))
      (mul_nonneg hC (sq_nonneg _))
  refine ⟨by simpa [C] using hC, ?_⟩
  have hfiber : ∀ rest,
      p09FiniteNorm2 (p09CoordinateSliceError axis i model x rest) ≤
        c * p09FiniteNorm2 (p09CoordinateSlice axis i x rest) := by
    intro rest
    simpa [c, C] using
      p09CoordinateSliceError_le axis i model x rest hεone
  simpa [c, C] using
    p09CoordinateError_norm_of_slices axis i model x c hc hfiber

lemma p09MultiNorm2_add_le {m : ℕ} {axis : Fin m → P09FftAxis}
    (x y : P09MultiArray axis) :
    p09MultiNorm2 (fun i ↦ x i + y i) ≤ p09MultiNorm2 x + p09MultiNorm2 y := by
  simpa only [p09MultiNorm2_eq_finiteNorm2] using p09FiniteNorm2_add_le x y

lemma p09CoordinateTransform_sub {m : ℕ} (axis : Fin m → P09FftAxis)
    (i : Fin m) (x y : P09MultiArray axis) :
    p09CoordinateTransform axis i (fun index ↦ x index - y index) =
      fun index ↦ p09CoordinateTransform axis i x index -
        p09CoordinateTransform axis i y index := by
  funext index
  simp only [p09CoordinateTransform]
  rw [← Finset.sum_sub_distrib]
  apply Finset.sum_congr rfl
  intro j hj
  ring

noncomputable def p09CoordinateScale {m : ℕ}
    (axis : Fin m → P09FftAxis) (i : Fin m) : ℝ :=
  Real.sqrt ((axis i).order : ℝ)

noncomputable def p09ExactCoordinateListApply {m : ℕ}
    (axis : Fin m → P09FftAxis) (stages : List (Fin m))
    (x : P09MultiArray axis) : P09MultiArray axis :=
  stages.foldl (fun state i ↦ p09CoordinateTransform axis i state) x

noncomputable def p09RoundedCoordinateListApply {m : ℕ}
    (axis : Fin m → P09FftAxis) (model : P09WilkinsonModel)
    (stages : List (Fin m)) (x : P09MultiArray axis) : P09MultiArray axis :=
  stages.foldl
    (fun state i ↦ p09RoundedCoordinateTransform axis i model state) x

lemma p09ExactCoordinateListApply_sub {m : ℕ}
    (axis : Fin m → P09FftAxis) (stages : List (Fin m))
    (x y : P09MultiArray axis) :
    p09ExactCoordinateListApply axis stages (fun index ↦ x index - y index) =
      fun index ↦ p09ExactCoordinateListApply axis stages x index -
        p09ExactCoordinateListApply axis stages y index := by
  induction stages generalizing x y with
  | nil => rfl
  | cons stage stages ih =>
      simp only [p09ExactCoordinateListApply, List.foldl_cons]
      rw [p09CoordinateTransform_sub]
      exact ih _ _

lemma p09ExactCoordinateListApply_norm {m : ℕ}
    (axis : Fin m → P09FftAxis) (stages : List (Fin m))
    (x : P09MultiArray axis) :
    p09MultiNorm2 (p09ExactCoordinateListApply axis stages x) =
      (stages.map (p09CoordinateScale axis)).prod * p09MultiNorm2 x := by
  induction stages generalizing x with
  | nil => simp [p09ExactCoordinateListApply]
  | cons stage stages ih =>
      change p09MultiNorm2 (p09ExactCoordinateListApply axis stages
          (p09CoordinateTransform axis stage x)) =
        p09CoordinateScale axis stage *
          (stages.map (p09CoordinateScale axis)).prod * p09MultiNorm2 x
      rw [ih, p09CoordinateTransform_norm]
      unfold p09CoordinateScale
      ring

noncomputable def p09CoordinateListSecondCoeff {m : ℕ}
    (axis : Fin m → P09FftAxis) (γ : ℝ) : List (Fin m) → ℝ
  | [] => 0
  | stage :: stages =>
      let CR := p09CoordinateListSecondCoeff axis γ stages
      let CS := p09FftSecondCoeff (axis stage).plan γ
      let scaleR := (stages.map (p09CoordinateScale axis)).prod
      let leadR := (stages.map (fun i ↦ p09AxisK (axis i) γ)).sum
      let scaleS := p09CoordinateScale axis stage
      let leadS := p09AxisK (axis stage) γ
      CR * scaleS + scaleR * CS + scaleR * leadR * scaleS * leadS +
        scaleR * leadR * CS + CR * scaleS * leadS + CR * CS

lemma p09RoundedCoordinateListApply_error_le {m : ℕ}
    (axis : Fin m → P09FftAxis) (model : P09WilkinsonModel)
    (stages : List (Fin m)) (x : P09MultiArray axis)
    (hεone : model.epsilon ≤ 1) :
    0 ≤ p09CoordinateListSecondCoeff axis model.gamma stages ∧
      p09MultiNorm2 (fun index ↦
        p09RoundedCoordinateListApply axis model stages x index -
          p09ExactCoordinateListApply axis stages x index) ≤
        (model.epsilon *
            ((stages.map (p09CoordinateScale axis)).prod *
              (stages.map (fun i ↦ p09AxisK (axis i) model.gamma)).sum) +
          p09CoordinateListSecondCoeff axis model.gamma stages *
            model.epsilon ^ 2) * p09MultiNorm2 x := by
  induction stages generalizing x with
  | nil =>
      refine ⟨by simp [p09CoordinateListSecondCoeff], ?_⟩
      simp [p09RoundedCoordinateListApply, p09ExactCoordinateListApply,
        p09CoordinateListSecondCoeff, p09MultiNorm2_eq_finiteNorm2,
        p09FiniteNorm2]
  | cons stage stages ih =>
      let xhat := p09RoundedCoordinateTransform axis stage model x
      let xexact := p09CoordinateTransform axis stage x
      let CS := p09FftSecondCoeff (axis stage).plan model.gamma
      have hstageData := p09RoundedCoordinateTransform_error_le
        axis stage model x hεone
      have hCS : 0 ≤ CS := by simpa [CS] using hstageData.1
      have hstage := hstageData.2
      let CR := p09CoordinateListSecondCoeff axis model.gamma stages
      have hrestData := ih xhat
      have hCR : 0 ≤ CR := by simpa [CR] using hrestData.1
      have hrest := hrestData.2
      let scaleR := (stages.map (p09CoordinateScale axis)).prod
      let leadR :=
        (stages.map (fun i ↦ p09AxisK (axis i) model.gamma)).sum
      let scaleS := p09CoordinateScale axis stage
      let leadS := p09AxisK (axis stage) model.gamma
      let scoeff := model.epsilon * (scaleS * leadS) +
        CS * model.epsilon ^ 2
      let rcoeff := model.epsilon * (scaleR * leadR) +
        CR * model.epsilon ^ 2
      let C := CR * scaleS + scaleR * CS +
        scaleR * leadR * scaleS * leadS + scaleR * leadR * CS +
          CR * scaleS * leadS + CR * CS
      have hε : 0 ≤ model.epsilon := le_of_lt model.epsilon_pos
      have hscaleS : 0 ≤ scaleS := by
        dsimp [scaleS, p09CoordinateScale]
        positivity
      have hleadS : 0 ≤ leadS := by
        dsimp [leadS, p09AxisK]
        exact p09K_nonneg (axis stage).plan model.gamma_nonneg
      have hscaleR : 0 ≤ scaleR := by
        dsimp [scaleR]
        apply List.prod_nonneg
        intro a ha
        rcases List.mem_map.mp ha with ⟨i, hi, rfl⟩
        exact Real.sqrt_nonneg _
      have hleadR : 0 ≤ leadR := by
        dsimp [leadR]
        apply List.sum_nonneg
        intro a ha
        rcases List.mem_map.mp ha with ⟨i, hi, rfl⟩
        exact p09K_nonneg (axis i).plan model.gamma_nonneg
      have hscoeff : 0 ≤ scoeff := by
        dsimp [scoeff]
        positivity
      have hrcoeff : 0 ≤ rcoeff := by
        dsimp [rcoeff]
        positivity
      have hC : 0 ≤ C := by
        dsimp [C]
        positivity
      change 0 ≤ C ∧ _
      refine ⟨hC, ?_⟩
      have hstage' : p09MultiNorm2 (fun index ↦
          xhat index - xexact index) ≤
          scoeff * p09MultiNorm2 x := by
        simpa [xhat, xexact, scoeff, scaleS, leadS,
          p09CoordinateScale] using hstage
      have hxhat : p09MultiNorm2 xhat ≤
          (scaleS + scoeff) * p09MultiNorm2 x := by
        calc
          p09MultiNorm2 xhat ≤
              p09MultiNorm2 (fun index ↦ xhat index - xexact index) +
                p09MultiNorm2 xexact := by
            have h := p09MultiNorm2_add_le
              (fun index ↦ xhat index - xexact index) xexact
            simpa only [sub_add_cancel] using h
          _ ≤ scoeff * p09MultiNorm2 x + scaleS * p09MultiNorm2 x :=
            add_le_add hstage' (le_of_eq (by
              simpa [xexact, scaleS, p09CoordinateScale] using
                p09CoordinateTransform_norm axis stage x))
          _ = (scaleS + scoeff) * p09MultiNorm2 x := by ring
      have hrest' : p09MultiNorm2 (fun index ↦
          p09RoundedCoordinateListApply axis model stages xhat index -
            p09ExactCoordinateListApply axis stages xhat index) ≤
          rcoeff * p09MultiNorm2 xhat := by
        simpa [rcoeff, scaleR, leadR] using hrest
      have hprop : p09MultiNorm2 (fun index ↦
          p09ExactCoordinateListApply axis stages xhat index -
            p09ExactCoordinateListApply axis stages xexact index) =
          scaleR * p09MultiNorm2 (fun index ↦
            xhat index - xexact index) := by
        rw [← p09ExactCoordinateListApply_sub]
        exact p09ExactCoordinateListApply_norm axis stages _
      have hsplit : (fun index ↦
          p09RoundedCoordinateListApply axis model (stage :: stages) x index -
            p09ExactCoordinateListApply axis (stage :: stages) x index) =
          (fun index ↦
            (p09RoundedCoordinateListApply axis model stages xhat index -
              p09ExactCoordinateListApply axis stages xhat index) +
            (p09ExactCoordinateListApply axis stages xhat index -
              p09ExactCoordinateListApply axis stages xexact index)) := by
        funext index
        simp [p09RoundedCoordinateListApply, p09ExactCoordinateListApply,
          xhat, xexact]
      rw [hsplit]
      have hraw : p09MultiNorm2 (fun index ↦
            (p09RoundedCoordinateListApply axis model stages xhat index -
              p09ExactCoordinateListApply axis stages xhat index) +
            (p09ExactCoordinateListApply axis stages xhat index -
              p09ExactCoordinateListApply axis stages xexact index)) ≤
          (rcoeff * (scaleS + scoeff) + scaleR * scoeff) *
            p09MultiNorm2 x := by
        calc
          _ ≤ p09MultiNorm2 (fun index ↦
                p09RoundedCoordinateListApply axis model stages xhat index -
                  p09ExactCoordinateListApply axis stages xhat index) +
              p09MultiNorm2 (fun index ↦
                p09ExactCoordinateListApply axis stages xhat index -
                  p09ExactCoordinateListApply axis stages xexact index) :=
            p09MultiNorm2_add_le _ _
          _ = p09MultiNorm2 (fun index ↦
                p09RoundedCoordinateListApply axis model stages xhat index -
                  p09ExactCoordinateListApply axis stages xhat index) +
              scaleR * p09MultiNorm2 (fun index ↦
                xhat index - xexact index) := by rw [hprop]
          _ ≤ rcoeff * p09MultiNorm2 xhat +
              scaleR * (scoeff * p09MultiNorm2 x) :=
            add_le_add hrest'
              (mul_le_mul_of_nonneg_left hstage' hscaleR)
          _ ≤ rcoeff * ((scaleS + scoeff) * p09MultiNorm2 x) +
              scaleR * (scoeff * p09MultiNorm2 x) :=
            add_le_add (mul_le_mul_of_nonneg_left hxhat hrcoeff) le_rfl
          _ = (rcoeff * (scaleS + scoeff) + scaleR * scoeff) *
              p09MultiNorm2 x := by ring
      refine le_trans hraw (mul_le_mul_of_nonneg_right ?_ (by
        unfold p09MultiNorm2
        positivity))
      have he3 : model.epsilon ^ 3 ≤ model.epsilon ^ 2 := by
        nlinarith [mul_self_le_mul_self hε hεone]
      have he4 : model.epsilon ^ 4 ≤ model.epsilon ^ 2 := by
        have he2one : model.epsilon ^ 2 ≤ 1 := by
          nlinarith [mul_self_le_mul_self hε hεone]
        nlinarith [mul_le_mul_of_nonneg_left he2one
          (sq_nonneg model.epsilon)]
      simp only [List.map_cons, List.prod_cons, List.sum_cons]
      dsimp [rcoeff, scoeff, C]
      rw [show p09CoordinateListSecondCoeff axis model.gamma
          (stage :: stages) =
        CR * scaleS + scaleR * CS + scaleR * leadR * scaleS * leadS +
          scaleR * leadR * CS + CR * scaleS * leadS + CR * CS by rfl]
      have hRLSL : 0 ≤ scaleR * leadR * scaleS * leadS := by positivity
      have hRLCS : 0 ≤ scaleR * leadR * CS := by positivity
      have hCRSL : 0 ≤ CR * scaleS * leadS := by positivity
      have hCRCS : 0 ≤ CR * CS := by positivity
      nlinarith [mul_le_mul_of_nonneg_left he3 hRLCS,
        mul_le_mul_of_nonneg_left he3 hCRSL,
        mul_le_mul_of_nonneg_left he4 hCRCS]

def p09ForwardCoordinateList {m : ℕ} (k : ℕ) (hk : k ≤ m) :
    List (Fin m) :=
  List.ofFn (fun i : Fin k ↦ Fin.castLE hk i)

def p09ReverseCoordinateList {m : ℕ} (k : ℕ) (hk : k ≤ m) :
    List (Fin m) :=
  (p09ForwardCoordinateList k hk).reverse

lemma p09ApplyCoordinatePrefix_eq_foldr {m : ℕ}
    (axis : Fin m → P09FftAxis) (k : ℕ) (hk : k ≤ m)
    (x : P09MultiArray axis) :
    p09ApplyCoordinatePrefix axis k x =
      (p09ForwardCoordinateList k hk).foldr
        (fun i state ↦ p09CoordinateTransform axis i state) x := by
  induction k generalizing x with
  | zero => simp [p09ApplyCoordinatePrefix, p09ForwardCoordinateList]
  | succ k ih =>
      have hk' : k ≤ m := le_trans (Nat.le_succ k) hk
      have hkm : k < m := lt_of_lt_of_le (Nat.lt_succ_self k) hk
      rw [p09ApplyCoordinatePrefix]
      simp only [p09CoordinateTransformNat, dif_pos hkm]
      rw [ih hk' (p09CoordinateTransform axis ⟨k, hkm⟩ x)]
      have hlist : p09ForwardCoordinateList (k + 1) hk =
          p09ForwardCoordinateList k hk' ++ [⟨k, hkm⟩] := by
        unfold p09ForwardCoordinateList
        rw [List.ofFn_succ', List.concat_eq_append]
        congr 1
      rw [hlist, List.foldr_append]
      rfl

lemma p09ExactCoordinateReverseList_eq_prefix {m : ℕ}
    (axis : Fin m → P09FftAxis) (k : ℕ) (hk : k ≤ m)
    (x : P09MultiArray axis) :
    p09ExactCoordinateListApply axis (p09ReverseCoordinateList k hk) x =
      p09ApplyCoordinatePrefix axis k x := by
  unfold p09ExactCoordinateListApply p09ReverseCoordinateList
  rw [List.foldl_reverse]
  symm
  exact p09ApplyCoordinatePrefix_eq_foldr axis k hk x

lemma p09ReverseCoordinateList_succ {m k : ℕ} (hk : k + 1 ≤ m) :
    p09ReverseCoordinateList (k + 1) hk =
      ⟨k, lt_of_lt_of_le (Nat.lt_succ_self k) hk⟩ ::
        p09ReverseCoordinateList k (le_trans (Nat.le_succ k) hk) := by
  have hforward : p09ForwardCoordinateList (k + 1) hk =
      p09ForwardCoordinateList k (le_trans (Nat.le_succ k) hk) ++
        [⟨k, lt_of_lt_of_le (Nat.lt_succ_self k) hk⟩] := by
    unfold p09ForwardCoordinateList
    rw [List.ofFn_succ', List.concat_eq_append]
    congr 1
  unfold p09ReverseCoordinateList
  rw [hforward, List.reverse_append]
  rfl

lemma p09Run_rounded_reverse_list {m : ℕ} [NeZero m]
    {plan : P09MultidimensionalFftPlan m} {model : P09WilkinsonModel}
    (run : P09MultidimensionalFftRun plan model)
    (k : ℕ) (hk : k ≤ m) :
    p09RoundedCoordinateListApply plan.axis model
        (p09ReverseCoordinateList k hk)
        (run.computedState ⟨k, Nat.lt_succ_of_le hk⟩) =
      run.computedState 0 := by
  induction k with
  | zero =>
      simp [p09ReverseCoordinateList, p09ForwardCoordinateList,
        p09RoundedCoordinateListApply]
  | succ k ih =>
      have hk' : k ≤ m := le_trans (Nat.le_succ k) hk
      have hkm : k < m := lt_of_lt_of_le (Nat.lt_succ_self k) hk
      rw [p09ReverseCoordinateList_succ]
      simp only [p09RoundedCoordinateListApply, List.foldl_cons]
      have hstep := run.stage_step ⟨k, hkm⟩
      have hstep' : p09RoundedCoordinateTransform plan.axis ⟨k, hkm⟩ model
          (run.computedState ⟨k + 1, Nat.lt_succ_of_le hk⟩) =
          run.computedState ⟨k, Nat.lt_succ_of_le hk'⟩ := by
        simpa only [Fin.succ_mk, Fin.castSucc_mk] using hstep.symm
      rw [hstep']
      exact ih hk'

lemma p09Run_computedOutput_eq_rounded_list {m : ℕ} [NeZero m]
    {plan : P09MultidimensionalFftPlan m} {model : P09WilkinsonModel}
    (run : P09MultidimensionalFftRun plan model) :
    p09MultiComputedOutput run =
      p09RoundedCoordinateListApply plan.axis model
        (p09ReverseCoordinateList m le_rfl) run.input := by
  have h := p09Run_rounded_reverse_list run m le_rfl
  have hlast : (⟨m, Nat.lt_succ_self m⟩ : Fin (m + 1)) = Fin.last m := by
    apply Fin.ext
    rfl
  rw [hlast, run.computed_input] at h
  unfold p09MultiComputedOutput
  exact h.symm

lemma p09ReverseCoordinateList_lead_sum {m : ℕ}
    (axis : Fin m → P09FftAxis) (γ : ℝ) :
    ((p09ReverseCoordinateList m le_rfl).map
      (fun i ↦ p09AxisK (axis i) γ)).sum =
      ∑ i : Fin m, p09AxisK (axis i) γ := by
  unfold p09ReverseCoordinateList p09ForwardCoordinateList
  rw [List.map_reverse, List.sum_reverse, List.map_ofFn, List.sum_ofFn]
  simp

lemma p09ReverseCoordinateList_scale_product {m : ℕ}
    (axis : Fin m → P09FftAxis) :
    ((p09ReverseCoordinateList m le_rfl).map
      (p09CoordinateScale axis)).prod =
      Real.sqrt (p09MultiCardinality axis : ℝ) := by
  unfold p09ReverseCoordinateList p09ForwardCoordinateList
  rw [List.map_reverse, List.prod_reverse, List.map_ofFn, List.prod_ofFn]
  simp only [Function.comp_apply, Fin.castLE_rfl, id_eq,
    p09CoordinateScale]
  rw [← Real.sqrt_prod (Finset.univ : Finset (Fin m))
    (fun i hi ↦ Nat.cast_nonneg (axis i).order)]
  congr 1
  simp [p09MultiCardinality, Nat.cast_prod]

lemma p09MultiCardinality_pos {m : ℕ} (axis : Fin m → P09FftAxis) :
    0 < p09MultiCardinality axis := by
  unfold p09MultiCardinality
  exact Finset.prod_pos fun i hi ↦ (axis i).order_pos

lemma p09MultiRms_le_of_norm_le {m : ℕ} {axis : Fin m → P09FftAxis}
    (x y : P09MultiArray axis) (c : ℝ)
    (h : p09MultiNorm2 x ≤ c * p09MultiNorm2 y) :
    p09MultiRms x ≤ c * p09MultiRms y := by
  have hd : 0 ≤ Real.sqrt (p09MultiCardinality axis : ℝ) :=
    Real.sqrt_nonneg _
  unfold p09MultiRms
  calc
    p09MultiNorm2 x / Real.sqrt (p09MultiCardinality axis : ℝ) ≤
        (c * p09MultiNorm2 y) /
          Real.sqrt (p09MultiCardinality axis : ℝ) :=
      div_le_div_of_nonneg_right h hd
    _ = c * (p09MultiNorm2 y /
          Real.sqrt (p09MultiCardinality axis : ℝ)) := by ring

lemma p09FamilyExactOutput_rms_scaling {m : ℕ} [NeZero m]
    (plan : P09MultidimensionalFftPlan m) (γ : ℝ)
    (family : P09AsymptoticMultidimensionalFftFamily plan γ) :
    p09MultiRms (p09FamilyMultiExactOutput family) =
      Real.sqrt (p09MultiCardinality plan.axis : ℝ) *
        p09MultiRms family.input := by
  have h := plan.prefix_rms_scaling m le_rfl family.input
  simpa [p09FamilyMultiExactOutput, p09PrefixOrderProduct,
    p09MultiCardinality] using h

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
  let stages := p09ReverseCoordinateList m le_rfl
  let C := p09CoordinateListSecondCoeff plan.axis γ stages
  have hC : 0 ≤ C := by
    let ε0 : P09PositiveEpsilon := ⟨1, zero_lt_one⟩
    let model0 := p09ExactWilkinsonModel ε0 γ family.gamma_nonneg
    have h := (p09RoundedCoordinateListApply_error_le plan.axis model0
      stages family.input (by change (1 : ℝ) ≤ 1; norm_num)).1
    simpa [C, model0, p09ExactWilkinsonModel] using h
  let exactRms := p09MultiRms (p09FamilyMultiExactOutput family)
  let inputRms := p09MultiRms family.input
  let secondOrderCoeff := C * inputRms / exactRms
  have hinputRms : 0 ≤ inputRms := by
    dsimp [inputRms, p09MultiRms]
    exact div_nonneg (by unfold p09MultiNorm2; positivity)
      (Real.sqrt_nonneg _)
  have hsecond : 0 ≤ secondOrderCoeff := by
    dsimp [secondOrderCoeff]
    exact div_nonneg (mul_nonneg hC hinputRms)
      (le_of_lt (by simpa [exactRms] using hexactOutput))
  refine ⟨secondOrderCoeff, hsecond, 1, zero_lt_one, ?_⟩
  intro ε hεone
  have hmodelOne : (family.model ε).epsilon ≤ 1 := by
    simpa [family.model_epsilon ε] using hεone
  have hcomp := (p09RoundedCoordinateListApply_error_le plan.axis
    (family.model ε) stages family.input hmodelOne).2
  have hrounded := p09Run_computedOutput_eq_rounded_list (family.run ε)
  rw [family.run_input ε] at hrounded
  have hexactList := p09ExactCoordinateReverseList_eq_prefix
    plan.axis m le_rfl family.input
  have herr : (fun index ↦
      p09RoundedCoordinateListApply plan.axis (family.model ε)
          stages family.input index -
        p09ExactCoordinateListApply plan.axis stages family.input index) =
      p09FamilyMultiFftRoundoffError family ε := by
    funext index
    dsimp [stages]
    rw [← hrounded, hexactList]
    rfl
  have hnorm :
      p09MultiNorm2 (p09FamilyMultiFftRoundoffError family ε) ≤
        (ε.1 * (Real.sqrt (p09MultiCardinality plan.axis : ℝ) *
            (∑ i : Fin m, p09AxisK (plan.axis i) γ)) +
          C * ε.1 ^ 2) * p09MultiNorm2 family.input := by
    rw [herr] at hcomp
    simpa [stages, C, family.model_epsilon ε, family.model_gamma ε,
      p09ReverseCoordinateList_scale_product,
      p09ReverseCoordinateList_lead_sum] using hcomp
  have hrms :
      p09MultiRms (p09FamilyMultiFftRoundoffError family ε) ≤
        (ε.1 * (Real.sqrt (p09MultiCardinality plan.axis : ℝ) *
            (∑ i : Fin m, p09AxisK (plan.axis i) γ)) +
          C * ε.1 ^ 2) * inputRms := by
    simpa [inputRms] using p09MultiRms_le_of_norm_le _ _ _ hnorm
  have hexactScale : exactRms =
      Real.sqrt (p09MultiCardinality plan.axis : ℝ) * inputRms := by
    simpa [exactRms, inputRms] using
      p09FamilyExactOutput_rms_scaling plan γ family
  have hratio :
      p09MultiRms (p09FamilyMultiFftRoundoffError family ε) / exactRms ≤
        ((ε.1 * (Real.sqrt (p09MultiCardinality plan.axis : ℝ) *
            (∑ i : Fin m, p09AxisK (plan.axis i) γ)) +
          C * ε.1 ^ 2) * inputRms) / exactRms :=
    div_le_div_of_nonneg_right hrms
      (le_of_lt (by simpa [exactRms] using hexactOutput))
  change p09MultiRms (p09FamilyMultiFftRoundoffError family ε) /
      exactRms ≤ _
  refine le_trans hratio ?_
  change ((ε.1 * (Real.sqrt (p09MultiCardinality plan.axis : ℝ) *
          (∑ i : Fin m, p09AxisK (plan.axis i) γ)) +
        C * ε.1 ^ 2) * inputRms) / exactRms ≤
    ε.1 * (∑ i : Fin m, p09AxisK (plan.axis i) γ) +
      (C * inputRms / exactRms) * ε.1 ^ 2
  have hexactNe : exactRms ≠ 0 :=
    ne_of_gt (by simpa [exactRms] using hexactOutput)
  have hscalePos : 0 < Real.sqrt (p09MultiCardinality plan.axis : ℝ) := by
    apply Real.sqrt_pos.2
    exact_mod_cast p09MultiCardinality_pos plan.axis
  have hinputPos : 0 < inputRms := by
    have hout : 0 < exactRms := by simpa [exactRms] using hexactOutput
    rw [hexactScale] at hout
    exact pos_of_mul_pos_right hout (le_of_lt hscalePos)
  have hleadCancel :
      Real.sqrt (p09MultiCardinality plan.axis : ℝ) * inputRms /
          exactRms = 1 := by
    rw [hexactScale]
    field_simp [ne_of_gt hscalePos, ne_of_gt hinputPos]
  calc
    ((ε.1 * (Real.sqrt (p09MultiCardinality plan.axis : ℝ) *
          (∑ i : Fin m, p09AxisK (plan.axis i) γ)) +
        C * ε.1 ^ 2) * inputRms) / exactRms =
        ε.1 * (∑ i : Fin m, p09AxisK (plan.axis i) γ) *
            (Real.sqrt (p09MultiCardinality plan.axis : ℝ) * inputRms /
              exactRms) +
          (C * inputRms / exactRms) * ε.1 ^ 2 := by ring
    _ ≤ ε.1 * (∑ i : Fin m, p09AxisK (plan.axis i) γ) +
          (C * inputRms / exactRms) * ε.1 ^ 2 := by
      rw [hleadCancel, mul_one]

end HighamBench
