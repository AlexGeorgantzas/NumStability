import HighamBench.P09Definitions

namespace HighamBench

open scoped BigOperators

private theorem p09_abs_flAdd_sub
    (model : P09WilkinsonModel) (a b : ℝ) :
    |model.flAdd a b - (a + b)| ≤
      model.epsilon * (|a| + |b|) := by
  rcases model.add_model a b with ⟨θa, θb, hθa, hθb, hfl⟩
  rw [hfl]
  have he : 0 < model.epsilon := model.epsilon_pos
  have hid :
      a * (1 + θa * model.epsilon) + b * (1 + θb * model.epsilon) -
          (a + b) = model.epsilon * (a * θa + b * θb) := by ring
  calc
    |a * (1 + θa * model.epsilon) + b * (1 + θb * model.epsilon) -
        (a + b)| = model.epsilon * |a * θa + b * θb| := by
          rw [hid, abs_mul, abs_of_pos he]
    _ ≤ model.epsilon * (|a| * |θa| + |b| * |θb|) := by
          gcongr
          calc
            |a * θa + b * θb| ≤ |a * θa| + |b * θb| := abs_add_le _ _
            _ = |a| * |θa| + |b| * |θb| := by rw [abs_mul, abs_mul]
    _ ≤ model.epsilon * (|a| + |b|) := by
          gcongr
          · nlinarith [abs_nonneg a]
          · nlinarith [abs_nonneg b]

private theorem p09_abs_flMul_sub
    (model : P09WilkinsonModel) (a b : ℝ) :
    |model.flMul a b - a * b| ≤
      model.epsilon * |a * b| := by
  rcases model.mul_model a b with ⟨θ, hθ, hfl⟩
  rw [hfl]
  have he : 0 < model.epsilon := model.epsilon_pos
  have hid : a * b * (1 + θ * model.epsilon) - a * b =
      model.epsilon * (a * b) * θ := by ring
  calc
    |a * b * (1 + θ * model.epsilon) - a * b| =
        model.epsilon * |a * b| * |θ| := by
          rw [hid, abs_mul, abs_mul, abs_of_pos he]
    _ ≤ model.epsilon * |a * b| := by
          nlinarith [abs_nonneg (a * b), mul_nonneg (le_of_lt he) (abs_nonneg (a*b))]

private theorem p09_pow_one_add_first_order (k : ℕ) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ e : ℝ, 0 ≤ e → e ≤ 1 →
      (1 + e) ^ k - 1 ≤ (k : ℝ) * e + C * e ^ 2 := by
  induction k with
  | zero =>
      exact ⟨0, le_rfl, by intro e he he1; norm_num⟩
  | succ k ih =>
      rcases ih with ⟨C, hC, hbound⟩
      refine ⟨2 * C + k, by positivity, ?_⟩
      intro e he he1
      have hpow_nonneg : 0 ≤ (1 + e) ^ k := by positivity
      have hone : 0 ≤ 1 + e := by positivity
      have hmul := mul_le_mul_of_nonneg_right (hbound e he he1) hone
      rw [pow_succ]
      calc
        (1 + e) ^ k * (1 + e) - 1
            ≤ ((k : ℝ) * e + C * e ^ 2 + 1) * (1 + e) - 1 := by
              nlinarith
        _ ≤ ((k + 1 : ℕ) : ℝ) * e + (2 * C + k) * e ^ 2 := by
              push_cast
              have he3 : e ^ 3 ≤ e ^ 2 := by nlinarith [sq_nonneg e]
              nlinarith

private theorem p09_recursiveSum_error {n : ℕ}
    (model : P09WilkinsonModel) (v : Fin n → ℝ) :
    |recursiveSum model.flAdd n v - ∑ i, v i| ≤
      ((1 + model.epsilon) ^ (n - 1) - 1) * ∑ i, |v i| := by
  induction n with
  | zero => simp [recursiveSum]
  | succ n ih =>
      by_cases hn : n = 0
      · subst n
        simp [recursiveSum]
      · have hnpos : 0 < n := Nat.pos_of_ne_zero hn
        let w : Fin n → ℝ := fun i => v i.castSucc
        let last : ℝ := v (Fin.last n)
        have hadd := p09_abs_flAdd_sub model (recursiveSum model.flAdd n w) last
        have htri :
            |model.flAdd (recursiveSum model.flAdd n w) last -
                ((∑ i, w i) + last)| ≤
              |model.flAdd (recursiveSum model.flAdd n w) last -
                  (recursiveSum model.flAdd n w + last)| +
                |recursiveSum model.flAdd n w - ∑ i, w i| := by
          have hid :
              model.flAdd (recursiveSum model.flAdd n w) last -
                    ((∑ i, w i) + last) =
                (model.flAdd (recursiveSum model.flAdd n w) last -
                    (recursiveSum model.flAdd n w + last)) +
                  (recursiveSum model.flAdd n w - ∑ i, w i) := by ring
          rw [hid]
          exact abs_add_le _ _
        have hrec := ih w
        have habsrec :
            |recursiveSum model.flAdd n w| ≤
              (1 + ((1 + model.epsilon) ^ (n - 1) - 1)) *
                ∑ i, |w i| := by
          calc
            |recursiveSum model.flAdd n w| ≤
                |recursiveSum model.flAdd n w - ∑ i, w i| + |∑ i, w i| := by
                  have := abs_add_le
                    (recursiveSum model.flAdd n w - ∑ i, w i) (∑ i, w i)
                  simpa using this
            _ ≤ ((1 + model.epsilon) ^ (n - 1) - 1) * ∑ i, |w i| +
                ∑ i, |w i| := by
                  gcongr
                  exact Finset.abs_sum_le_sum_abs w Finset.univ
            _ = (1 + ((1 + model.epsilon) ^ (n - 1) - 1)) *
                ∑ i, |w i| := by ring
        rw [recursiveSum, dif_neg hn]
        rw [Fin.sum_univ_castSucc]
        rw [show n + 1 - 1 = n by omega]
        rw [Fin.sum_univ_castSucc]
        change
          |model.flAdd (recursiveSum model.flAdd n w) last -
              ((∑ i, w i) + last)| ≤
            ((1 + model.epsilon) ^ n - 1) *
              ((∑ i, |w i|) + |last|)
        have he0 : 0 ≤ model.epsilon := le_of_lt model.epsilon_pos
        let g : ℝ := (1 + model.epsilon) ^ (n - 1) - 1
        let G : ℝ := (1 + model.epsilon) ^ n - 1
        have hg0 : 0 ≤ g := by
          dsimp [g]
          have hp : 1 ≤ (1 + model.epsilon) ^ (n - 1) := by
            exact one_le_pow₀ (by linarith)
          linarith
        have hG : G = (1 + model.epsilon) * g + model.epsilon := by
          dsimp [G, g]
          have hpow : (1 + model.epsilon) ^ n =
              (1 + model.epsilon) ^ (n - 1) * (1 + model.epsilon) := by
            rw [← pow_succ]
            congr 1
            omega
          rw [hpow]
          ring
        have hG0 : 0 ≤ G := by
          rw [hG]
          positivity
        have hG_ge_e : model.epsilon ≤ G := by
          rw [hG]
          nlinarith
        calc
          |model.flAdd (recursiveSum model.flAdd n w) last -
              ((∑ i, w i) + last)|
              ≤ |model.flAdd (recursiveSum model.flAdd n w) last -
                    (recursiveSum model.flAdd n w + last)| +
                  |recursiveSum model.flAdd n w - ∑ i, w i| := htri
          _ ≤ model.epsilon *
                  (|recursiveSum model.flAdd n w| + |last|) +
                g * ∑ i, |w i| := by
                  gcongr
          _ ≤ model.epsilon *
                  ((1 + g) * (∑ i, |w i|) + |last|) +
                g * ∑ i, |w i| := by
                  gcongr
          _ = G * (∑ i, |w i|) + model.epsilon * |last| := by
                  rw [hG]
                  ring
          _ ≤ G * ((∑ i, |w i|) + |last|) := by
                  have hlast : 0 ≤ |last| := abs_nonneg _
                  nlinarith

private theorem p09_complex_diag_norm_le (z : ℂ) (a b : ℝ)
    (ha : |a| ≤ 1) (hb : |b| ≤ 1) :
    ‖(⟨a * z.re, b * z.im⟩ : ℂ)‖ ≤ ‖z‖ := by
  apply (sq_le_sq₀ (norm_nonneg _) (norm_nonneg _)).mp
  rw [Complex.sq_norm, Complex.sq_norm, Complex.normSq_apply,
    Complex.normSq_apply]
  have ha2 : a ^ 2 ≤ 1 := (sq_le_one_iff_abs_le_one a).2 ha
  have hb2 : b ^ 2 ≤ 1 := (sq_le_one_iff_abs_le_one b).2 hb
  have hre : a ^ 2 * z.re ^ 2 ≤ z.re ^ 2 := by
    nlinarith [sq_nonneg z.re,
      mul_le_mul_of_nonneg_right ha2 (sq_nonneg z.re)]
  have him : b ^ 2 * z.im ^ 2 ≤ z.im ^ 2 := by
    nlinarith [sq_nonneg z.im,
      mul_le_mul_of_nonneg_right hb2 (sq_nonneg z.im)]
  norm_num
  nlinarith

private theorem p09_roundedComplexAdd_error
    (model : P09WilkinsonModel) (x y : ℂ) :
    ‖p09RoundedComplexAdd model x y - (x + y)‖ ≤
      model.epsilon * (‖x‖ + ‖y‖) := by
  rcases model.add_model x.re y.re with ⟨ar, br, har, hbr, hre⟩
  rcases model.add_model x.im y.im with ⟨ai, bi, hai, hbi, him⟩
  let dx : ℂ := ⟨ar * x.re, ai * x.im⟩
  let dy : ℂ := ⟨br * y.re, bi * y.im⟩
  have hdx : ‖dx‖ ≤ ‖x‖ := p09_complex_diag_norm_le x ar ai har hai
  have hdy : ‖dy‖ ≤ ‖y‖ := p09_complex_diag_norm_le y br bi hbr hbi
  have hid : p09RoundedComplexAdd model x y - (x + y) =
      (model.epsilon : ℂ) * dx + (model.epsilon : ℂ) * dy := by
    apply Complex.ext <;> simp [p09RoundedComplexAdd, hre, him, dx, dy] <;> ring
  rw [hid]
  calc
    ‖(model.epsilon : ℂ) * dx + (model.epsilon : ℂ) * dy‖
        ≤ ‖(model.epsilon : ℂ) * dx‖ + ‖(model.epsilon : ℂ) * dy‖ :=
          norm_add_le _ _
    _ = model.epsilon * (‖dx‖ + ‖dy‖) := by
          rw [norm_mul, norm_mul]
          simp [abs_of_pos model.epsilon_pos]
          ring
    _ ≤ model.epsilon * (‖x‖ + ‖y‖) := by
          exact mul_le_mul_of_nonneg_left (add_le_add hdx hdy)
            (le_of_lt model.epsilon_pos)

private theorem p09_abs_re_add_abs_im_le (z : ℂ) :
    |z.re| + |z.im| ≤ (3 / 2 : ℝ) * ‖z‖ := by
  have hsq : (|z.re| + |z.im|) ^ 2 ≤ 2 * ‖z‖ ^ 2 := by
    rw [Complex.sq_norm, Complex.normSq_apply]
    nlinarith [sq_nonneg (|z.re| - |z.im|), sq_abs z.re, sq_abs z.im]
  have hsqrt2 : Real.sqrt 2 ≤ (3 / 2 : ℝ) := by nlinarith [Real.sq_sqrt (by norm_num : (0:ℝ) ≤ 2)]
  have hfirst : |z.re| + |z.im| ≤ Real.sqrt 2 * ‖z‖ := by
    apply (sq_le_sq₀ (by positivity) (by positivity)).mp
    rw [mul_pow, Real.sq_sqrt (by norm_num : (0:ℝ) ≤ 2)]
    exact hsq
  exact hfirst.trans (mul_le_mul_of_nonneg_right hsqrt2 (norm_nonneg z))

private theorem p09_roundedComplexSum_error {q : ℕ} [NeZero q] :
    ∃ C : ℝ, 0 ≤ C ∧
      ∀ (model : P09WilkinsonModel), model.epsilon ≤ 1 →
      ∀ term : ZMod q → ℂ,
        ‖p09RoundedComplexSum model term - ∑ j, term j‖ ≤
          ((3 / 2 : ℝ) * (q - 1 : ℕ)) * model.epsilon *
              (∑ j, ‖term j‖) +
            C * model.epsilon ^ 2 * (∑ j, ‖term j‖) := by
  rcases p09_pow_one_add_first_order (q - 1) with ⟨C, hC, hpow⟩
  refine ⟨(3 / 2 : ℝ) * C, by positivity, ?_⟩
  intro model he1 term
  let index : Fin q ≃ ZMod q := (ZMod.finEquiv q).toEquiv
  let re : Fin q → ℝ := fun i => (term (index i)).re
  let im : Fin q → ℝ := fun i => (term (index i)).im
  have hre := p09_recursiveSum_error model re
  have him := p09_recursiveSum_error model im
  have hpow' := hpow model.epsilon (le_of_lt model.epsilon_pos) he1
  have hfactor0 : 0 ≤ (1 + model.epsilon) ^ (q - 1) - 1 := by
    have : 1 ≤ (1 + model.epsilon) ^ (q - 1) :=
      one_le_pow₀ (by linarith [model.epsilon_pos])
    linarith
  have hcomponent :
      |recursiveSum model.flAdd q re - ∑ i, re i| +
          |recursiveSum model.flAdd q im - ∑ i, im i| ≤
        ((1 + model.epsilon) ^ (q - 1) - 1) *
          ∑ i, (|(term (index i)).re| + |(term (index i)).im|) := by
    calc
      _ ≤ ((1 + model.epsilon) ^ (q - 1) - 1) * (∑ i, |re i|) +
          ((1 + model.epsilon) ^ (q - 1) - 1) * (∑ i, |im i|) :=
            add_le_add hre him
      _ = ((1 + model.epsilon) ^ (q - 1) - 1) *
          ∑ i, (|(term (index i)).re| + |(term (index i)).im|) := by
            simp only [re, im, Finset.sum_add_distrib]
            ring
  have hl1 :
      (∑ i, (|(term (index i)).re| + |(term (index i)).im|)) ≤
        (3 / 2 : ℝ) * ∑ j, ‖term j‖ := by
    calc
      _ ≤ ∑ i, (3 / 2 : ℝ) * ‖term (index i)‖ := by
            gcongr with i
            exact p09_abs_re_add_abs_im_le _
      _ = (3 / 2 : ℝ) * ∑ j, ‖term j‖ := by
            rw [← index.sum_comp]
            simp only [Finset.mul_sum]
  have hnormcomponent :
      ‖p09RoundedComplexSum model term - ∑ j, term j‖ ≤
        |recursiveSum model.flAdd q re - ∑ i, re i| +
          |recursiveSum model.flAdd q im - ∑ i, im i| := by
    rw [p09RoundedComplexSum]
    change ‖(⟨recursiveSum model.flAdd q re,
          recursiveSum model.flAdd q im⟩ : ℂ) - ∑ j, term j‖ ≤ _
    have hreSum : (∑ j, term j).re = ∑ i, re i := by
      change Complex.reCLM (∑ j, term j) = ∑ i, re i
      rw [map_sum]
      simp only [Complex.reCLM_apply, re]
      exact (index.sum_comp (fun j : ZMod q => (term j).re)).symm
    have himSum : (∑ j, term j).im = ∑ i, im i := by
      change Complex.imCLM (∑ j, term j) = ∑ i, im i
      rw [map_sum]
      simp only [Complex.imCLM_apply, im]
      exact (index.sum_comp (fun j : ZMod q => (term j).im)).symm
    rw [Complex.norm_def, Complex.normSq_apply]
    simp only [Complex.sub_re, Complex.sub_im, hreSum, himSum]
    have hsqrt : Real.sqrt
          ((recursiveSum model.flAdd q re - ∑ i, re i) ^ 2 +
           (recursiveSum model.flAdd q im - ∑ i, im i) ^ 2) ≤
        |recursiveSum model.flAdd q re - ∑ i, re i| +
          |recursiveSum model.flAdd q im - ∑ i, im i| := by
      rw [Real.sqrt_le_iff]
      constructor
      · positivity
      · nlinarith [sq_abs (recursiveSum model.flAdd q re - ∑ i, re i),
          sq_abs (recursiveSum model.flAdd q im - ∑ i, im i),
          mul_nonneg (abs_nonneg (recursiveSum model.flAdd q re - ∑ i, re i))
            (abs_nonneg (recursiveSum model.flAdd q im - ∑ i, im i))]
    simpa [pow_two] using hsqrt
  calc
    ‖p09RoundedComplexSum model term - ∑ j, term j‖
        ≤ ((1 + model.epsilon) ^ (q - 1) - 1) *
          ∑ i, (|(term (index i)).re| + |(term (index i)).im|) :=
            hnormcomponent.trans hcomponent
    _ ≤ ((1 + model.epsilon) ^ (q - 1) - 1) *
          ((3 / 2 : ℝ) * ∑ j, ‖term j‖) := by
            gcongr
    _ ≤ (((q - 1 : ℕ) : ℝ) * model.epsilon + C * model.epsilon ^ 2) *
          ((3 / 2 : ℝ) * ∑ j, ‖term j‖) := by
            gcongr
    _ = ((3 / 2 : ℝ) * (q - 1 : ℕ)) * model.epsilon *
              (∑ j, ‖term j‖) +
            ((3 / 2 : ℝ) * C) * model.epsilon ^ 2 *
              (∑ j, ‖term j‖) := by ring

private theorem p09_four_real_complex_norm_le
    (a b c d : ℝ) :
    ‖(⟨a - b, c + d⟩ : ℂ)‖ ≤
      (3 / 2 : ℝ) * Real.sqrt (a ^ 2 + b ^ 2 + c ^ 2 + d ^ 2) := by
  apply (sq_le_sq₀ (norm_nonneg _) (by positivity)).mp
  rw [Complex.sq_norm, Complex.normSq_apply, mul_pow,
    Real.sq_sqrt (by positivity : 0 ≤ a ^ 2 + b ^ 2 + c ^ 2 + d ^ 2)]
  norm_num
  nlinarith [sq_nonneg (a + b), sq_nonneg (c - d), sq_nonneg a,
    sq_nonneg b, sq_nonneg c, sq_nonneg d]

private theorem p09_flMul_abs_le
    (model : P09WilkinsonModel) (a b : ℝ) :
    |model.flMul a b| ≤ (1 + model.epsilon) * |a * b| := by
  calc
    |model.flMul a b| ≤ |model.flMul a b - a * b| + |a * b| := by
      have := abs_add_le (model.flMul a b - a * b) (a * b)
      simpa using this
    _ ≤ model.epsilon * |a * b| + |a * b| := by
      gcongr
      exact p09_abs_flMul_sub model a b
    _ = (1 + model.epsilon) * |a * b| := by ring

private theorem p09_roundedComplexMul_error
    (model : P09WilkinsonModel) (x y : ℂ) :
    ‖p09RoundedComplexMul model x y - x * y‖ ≤
      3 * model.epsilon * ‖x‖ * ‖y‖ +
        (3 / 2 : ℝ) * model.epsilon ^ 2 * ‖x‖ * ‖y‖ := by
  let p₁ : ℝ := x.re * y.re
  let p₂ : ℝ := x.im * y.im
  let p₃ : ℝ := x.re * y.im
  let p₄ : ℝ := x.im * y.re
  let u₁ : ℝ := model.flMul x.re y.re
  let u₂ : ℝ := model.flMul x.im y.im
  let u₃ : ℝ := model.flMul x.re y.im
  let u₄ : ℝ := model.flMul x.im y.re
  let mulError : ℂ := ⟨(u₁ - p₁) - (u₂ - p₂),
    (u₃ - p₃) + (u₄ - p₄)⟩
  let addError : ℂ :=
    ⟨model.flAdd u₁ (-u₂) - (u₁ - u₂),
      model.flAdd u₃ u₄ - (u₃ + u₄)⟩
  have hdecomp : p09RoundedComplexMul model x y - x * y =
      mulError + addError := by
    apply Complex.ext <;>
      simp [p09RoundedComplexMul, mulError, addError, u₁, u₂, u₃, u₄,
        p₁, p₂, p₃, p₄] <;> ring
  have hprodSq : p₁ ^ 2 + p₂ ^ 2 + p₃ ^ 2 + p₄ ^ 2 =
      ‖x‖ ^ 2 * ‖y‖ ^ 2 := by
    rw [Complex.sq_norm, Complex.sq_norm, Complex.normSq_apply,
      Complex.normSq_apply]
    simp only [p₁, p₂, p₃, p₄]
    ring
  have hmul : ‖mulError‖ ≤
      (3 / 2 : ℝ) * model.epsilon * ‖x‖ * ‖y‖ := by
    have hfour := p09_four_real_complex_norm_le
      (u₁ - p₁) (u₂ - p₂) (u₃ - p₃) (u₄ - p₄)
    have hsqsum :
        (u₁ - p₁) ^ 2 + (u₂ - p₂) ^ 2 +
              (u₃ - p₃) ^ 2 + (u₄ - p₄) ^ 2 ≤
          model.epsilon ^ 2 *
            (p₁ ^ 2 + p₂ ^ 2 + p₃ ^ 2 + p₄ ^ 2) := by
      have h₁ := p09_abs_flMul_sub model x.re y.re
      have h₂ := p09_abs_flMul_sub model x.im y.im
      have h₃ := p09_abs_flMul_sub model x.re y.im
      have h₄ := p09_abs_flMul_sub model x.im y.re
      simp only [u₁, u₂, u₃, u₄, p₁, p₂, p₃, p₄] at h₁ h₂ h₃ h₄ ⊢
      have hs₁ := (sq_le_sq₀ (abs_nonneg _)
        (mul_nonneg (le_of_lt model.epsilon_pos) (abs_nonneg _))).2 h₁
      have hs₂ := (sq_le_sq₀ (abs_nonneg _)
        (mul_nonneg (le_of_lt model.epsilon_pos) (abs_nonneg _))).2 h₂
      have hs₃ := (sq_le_sq₀ (abs_nonneg _)
        (mul_nonneg (le_of_lt model.epsilon_pos) (abs_nonneg _))).2 h₃
      have hs₄ := (sq_le_sq₀ (abs_nonneg _)
        (mul_nonneg (le_of_lt model.epsilon_pos) (abs_nonneg _))).2 h₄
      simp only [mul_pow, sq_abs] at hs₁ hs₂ hs₃ hs₄
      nlinarith
    calc
      ‖mulError‖ ≤ (3 / 2 : ℝ) * Real.sqrt
          ((u₁ - p₁) ^ 2 + (u₂ - p₂) ^ 2 +
            (u₃ - p₃) ^ 2 + (u₄ - p₄) ^ 2) := hfour
      _ ≤ (3 / 2 : ℝ) * Real.sqrt
          (model.epsilon ^ 2 *
            (p₁ ^ 2 + p₂ ^ 2 + p₃ ^ 2 + p₄ ^ 2)) := by
              gcongr
      _ = (3 / 2 : ℝ) * model.epsilon * ‖x‖ * ‖y‖ := by
              rw [hprodSq, Real.sqrt_mul (sq_nonneg _), Real.sqrt_sq_eq_abs,
                abs_of_pos model.epsilon_pos, Real.sqrt_mul (sq_nonneg _),
                Real.sqrt_sq_eq_abs, abs_of_nonneg (norm_nonneg x),
                Real.sqrt_sq_eq_abs, abs_of_nonneg (norm_nonneg y)]
              ring
  have hadd : ‖addError‖ ≤
      (3 / 2 : ℝ) * model.epsilon * (1 + model.epsilon) * ‖x‖ * ‖y‖ := by
    let a : ℂ := ⟨u₁, u₃⟩
    let b : ℂ := ⟨-u₂, u₄⟩
    have hadd0 := p09_roundedComplexAdd_error model a b
    have haddEq : addError = p09RoundedComplexAdd model a b - (a + b) := by
      apply Complex.ext <;>
        simp [addError, a, b, p09RoundedComplexAdd] <;> ring
    rw [haddEq]
    have hab : ‖a‖ + ‖b‖ ≤
        (3 / 2 : ℝ) * Real.sqrt (‖a‖ ^ 2 + ‖b‖ ^ 2) := by
      apply (sq_le_sq₀ (by positivity) (by positivity)).mp
      rw [mul_pow, Real.sq_sqrt (by positivity)]
      norm_num
      nlinarith [sq_nonneg (‖a‖ - ‖b‖)]
    have hu₁ := p09_flMul_abs_le model x.re y.re
    have hu₂ := p09_flMul_abs_le model x.im y.im
    have hu₃ := p09_flMul_abs_le model x.re y.im
    have hu₄ := p09_flMul_abs_le model x.im y.re
    have huvSq : ‖a‖ ^ 2 + ‖b‖ ^ 2 ≤
        (1 + model.epsilon) ^ 2 *
          (p₁ ^ 2 + p₂ ^ 2 + p₃ ^ 2 + p₄ ^ 2) := by
      rw [Complex.sq_norm, Complex.sq_norm, Complex.normSq_apply,
        Complex.normSq_apply]
      simp only [a, b, neg_mul, mul_neg, neg_sq]
      have he1 : 0 ≤ 1 + model.epsilon := by linarith [model.epsilon_pos]
      have hu₁2 := (sq_le_sq₀ (abs_nonneg _)
        (mul_nonneg he1 (abs_nonneg _))).2 hu₁
      have hu₂2 := (sq_le_sq₀ (abs_nonneg _)
        (mul_nonneg he1 (abs_nonneg _))).2 hu₂
      have hu₃2 := (sq_le_sq₀ (abs_nonneg _)
        (mul_nonneg he1 (abs_nonneg _))).2 hu₃
      have hu₄2 := (sq_le_sq₀ (abs_nonneg _)
        (mul_nonneg he1 (abs_nonneg _))).2 hu₄
      simp only [sq_abs, mul_pow] at hu₁2 hu₂2 hu₃2 hu₄2
      simp only [p₁, p₂, p₃, p₄, u₁, u₂, u₃, u₄] at *
      nlinarith
    have hsqrt : Real.sqrt (‖a‖ ^ 2 + ‖b‖ ^ 2) ≤
        (1 + model.epsilon) * ‖x‖ * ‖y‖ := by
      have he1 : 0 ≤ 1 + model.epsilon := by linarith [model.epsilon_pos]
      calc
        _ ≤ Real.sqrt ((1 + model.epsilon) ^ 2 *
            (p₁ ^ 2 + p₂ ^ 2 + p₃ ^ 2 + p₄ ^ 2)) := by gcongr
        _ = (1 + model.epsilon) * ‖x‖ * ‖y‖ := by
          rw [hprodSq, Real.sqrt_mul (sq_nonneg _), Real.sqrt_sq_eq_abs,
            abs_of_nonneg he1, Real.sqrt_mul (sq_nonneg _),
            Real.sqrt_sq_eq_abs, abs_of_nonneg (norm_nonneg x),
            Real.sqrt_sq_eq_abs, abs_of_nonneg (norm_nonneg y)]
          ring
    calc
      ‖p09RoundedComplexAdd model a b - (a + b)‖
          ≤ model.epsilon * (‖a‖ + ‖b‖) := hadd0
      _ ≤ model.epsilon * ((3 / 2 : ℝ) *
            Real.sqrt (‖a‖ ^ 2 + ‖b‖ ^ 2)) :=
              mul_le_mul_of_nonneg_left hab (le_of_lt model.epsilon_pos)
      _ ≤ model.epsilon * ((3 / 2 : ℝ) *
            ((1 + model.epsilon) * ‖x‖ * ‖y‖)) := by
              exact mul_le_mul_of_nonneg_left
                (mul_le_mul_of_nonneg_left hsqrt (by norm_num))
                (le_of_lt model.epsilon_pos)
      _ = (3 / 2 : ℝ) * model.epsilon * (1 + model.epsilon) *
          ‖x‖ * ‖y‖ := by ring
  rw [hdecomp]
  calc
    ‖mulError + addError‖ ≤ ‖mulError‖ + ‖addError‖ := norm_add_le _ _
    _ ≤ (3 / 2 : ℝ) * model.epsilon * ‖x‖ * ‖y‖ +
        (3 / 2 : ℝ) * model.epsilon * (1 + model.epsilon) * ‖x‖ * ‖y‖ :=
          add_le_add hmul hadd
    _ = 3 * model.epsilon * ‖x‖ * ‖y‖ +
        (3 / 2 : ℝ) * model.epsilon ^ 2 * ‖x‖ * ‖y‖ := by ring

private theorem p09_stdAddChar_eq_cos_sin {q : ℕ} [NeZero q]
    (j : ZMod q) :
    ZMod.stdAddChar j =
      (⟨Real.cos (p09RootAngle j), Real.sin (p09RootAngle j)⟩ : ℂ) := by
  rw [p09StdAddChar_positive_exp]
  have harg :
      2 * Real.pi * Complex.I * (j.val : ℂ) / (q : ℂ) =
        (p09RootAngle j : ℂ) * Complex.I := by
    simp only [p09RootAngle, Complex.ofReal_mul, Complex.ofReal_ofNat,
      Complex.ofReal_natCast, Complex.ofReal_div]
    push_cast
    ring
  rw [harg, Complex.exp_mul_I]
  apply Complex.ext <;>
    simp [Complex.cos_ofReal_re, Complex.cos_ofReal_im,
      Complex.sin_ofReal_re, Complex.sin_ofReal_im]

private theorem p09_roundedRoot_error {q : ℕ} [NeZero q]
    (model : P09WilkinsonModel) (j : ZMod q) :
    ‖p09RoundedRoot model j - ZMod.stdAddChar j‖ ≤
      2 * model.gamma * model.epsilon := by
  rcases model.cos_model (p09RootAngle j) with ⟨θc, hθc, hc⟩
  rcases model.sin_model (p09RootAngle j) with ⟨θs, hθs, hs⟩
  rw [p09_stdAddChar_eq_cos_sin]
  rw [Complex.norm_def, Complex.normSq_apply]
  simp only [p09RoundedRoot, Complex.sub_re, Complex.sub_im, hc, hs]
  have hγ : 0 ≤ model.gamma := model.gamma_nonneg
  have he : 0 ≤ model.epsilon := le_of_lt model.epsilon_pos
  have hθc' : θc ^ 2 ≤ 1 := (sq_le_one_iff_abs_le_one θc).2 hθc
  have hθs' : θs ^ 2 ≤ 1 := (sq_le_one_iff_abs_le_one θs).2 hθs
  rw [show Real.cos (p09RootAngle j) + model.gamma * θc * model.epsilon -
          Real.cos (p09RootAngle j) = model.gamma * θc * model.epsilon by ring,
      show Real.sin (p09RootAngle j) + model.gamma * θs * model.epsilon -
          Real.sin (p09RootAngle j) = model.gamma * θs * model.epsilon by ring]
  apply (sq_le_sq₀ (Real.sqrt_nonneg _) (by positivity)).mp
  rw [show model.gamma * θc * model.epsilon * (model.gamma * θc * model.epsilon) +
        model.gamma * θs * model.epsilon * (model.gamma * θs * model.epsilon) =
      (model.gamma * θc * model.epsilon) ^ 2 +
        (model.gamma * θs * model.epsilon) ^ 2 by ring,
    Real.sq_sqrt (add_nonneg (sq_nonneg _) (sq_nonneg _)), mul_pow]
  nlinarith [sq_nonneg (model.gamma * model.epsilon),
    mul_le_mul_of_nonneg_left (add_le_add hθc' hθs')
      (sq_nonneg (model.gamma * model.epsilon))]

private theorem p09_roundedRoot_norm_le {q : ℕ} [NeZero q]
    (model : P09WilkinsonModel) (j : ZMod q) :
    ‖p09RoundedRoot model j‖ ≤ 1 + 2 * model.gamma * model.epsilon := by
  calc
    ‖p09RoundedRoot model j‖ ≤
        ‖p09RoundedRoot model j - ZMod.stdAddChar j‖ +
          ‖ZMod.stdAddChar j‖ := by
      have := norm_add_le
        (p09RoundedRoot model j - ZMod.stdAddChar j) (ZMod.stdAddChar j)
      simpa using this
    _ ≤ 2 * model.gamma * model.epsilon + 1 := by
      have hchar : ‖ZMod.stdAddChar j‖ = 1 := by
        rw [p09_stdAddChar_eq_cos_sin, Complex.norm_def,
          Complex.normSq_apply]
        simp only
        rw [show Real.cos (p09RootAngle j) * Real.cos (p09RootAngle j) +
              Real.sin (p09RootAngle j) * Real.sin (p09RootAngle j) = 1 by
                nlinarith [Real.sin_sq_add_cos_sq (p09RootAngle j)],
          Real.sqrt_one]
      rw [hchar]
      exact add_le_add (p09_roundedRoot_error model j) le_rfl
    _ = 1 + 2 * model.gamma * model.epsilon := by ring

private theorem p09_roundedRootMul_error {q : ℕ} [NeZero q]
    (model : P09WilkinsonModel) (j : ZMod q) (x : ℂ)
    (he1 : model.epsilon ≤ 1) :
    ‖p09RoundedComplexMul model (p09RoundedRoot model j) x -
        ZMod.stdAddChar j * x‖ ≤
      (3 + 2 * model.gamma) * model.epsilon * ‖x‖ +
        9 * (1 + model.gamma) ^ 2 * model.epsilon ^ 2 * ‖x‖ := by
  have hmul := p09_roundedComplexMul_error model (p09RoundedRoot model j) x
  have hroot := p09_roundedRoot_error model j
  have hrootnorm := p09_roundedRoot_norm_le model j
  have hdecomp :
      p09RoundedComplexMul model (p09RoundedRoot model j) x -
          ZMod.stdAddChar j * x =
        (p09RoundedComplexMul model (p09RoundedRoot model j) x -
          p09RoundedRoot model j * x) +
        (p09RoundedRoot model j - ZMod.stdAddChar j) * x := by ring
  rw [hdecomp]
  calc
    _ ≤ ‖p09RoundedComplexMul model (p09RoundedRoot model j) x -
          p09RoundedRoot model j * x‖ +
        ‖(p09RoundedRoot model j - ZMod.stdAddChar j) * x‖ := norm_add_le _ _
    _ ≤ (3 * model.epsilon * ‖p09RoundedRoot model j‖ * ‖x‖ +
          (3 / 2 : ℝ) * model.epsilon ^ 2 *
            ‖p09RoundedRoot model j‖ * ‖x‖) +
        (2 * model.gamma * model.epsilon) * ‖x‖ := by
      rw [norm_mul]
      gcongr
    _ ≤ (3 * model.epsilon *
            (1 + 2 * model.gamma * model.epsilon) * ‖x‖ +
          (3 / 2 : ℝ) * model.epsilon ^ 2 *
            (1 + 2 * model.gamma * model.epsilon) * ‖x‖) +
        (2 * model.gamma * model.epsilon) * ‖x‖ := by
      have he := le_of_lt model.epsilon_pos
      gcongr
    _ ≤ (3 + 2 * model.gamma) * model.epsilon * ‖x‖ +
        9 * (1 + model.gamma) ^ 2 * model.epsilon ^ 2 * ‖x‖ := by
      have hγ := model.gamma_nonneg
      have he := le_of_lt model.epsilon_pos
      have he3 : model.epsilon ^ 3 ≤ model.epsilon ^ 2 := by
        nlinarith [sq_nonneg model.epsilon]
      have hx := norm_nonneg x
      have hcubic : model.gamma * model.epsilon ^ 3 * ‖x‖ ≤
          model.gamma * model.epsilon ^ 2 * ‖x‖ :=
        mul_le_mul_of_nonneg_right
          (mul_le_mul_of_nonneg_left he3 hγ) hx
      nlinarith [mul_nonneg (sq_nonneg (1 + model.gamma))
          (mul_nonneg (sq_nonneg model.epsilon) hx),
        hcubic,
        mul_nonneg (sq_nonneg model.epsilon) hx]

private theorem p09_radixTwoCoefficient_exact (j : ZMod 2) (x : ℂ) :
    p09RadixTwoCoefficientApply j x = ZMod.stdAddChar j * x := by
  fin_cases j
  · let j0 : ZMod 2 := ⟨0, by decide⟩
    change p09RadixTwoCoefficientApply j0 x = ZMod.stdAddChar j0 * x
    have hangle : p09RootAngle j0 = 0 := by
      simp [p09RootAngle, j0, ZMod.cast, ZMod.val, ZMod]
    rw [p09RadixTwoCoefficientApply, p09_stdAddChar_eq_cos_sin, hangle]
    rw [if_pos (by rfl : j0 = 0)]
    apply Complex.ext <;> simp
  · let j1 : ZMod 2 := ⟨1, by decide⟩
    change p09RadixTwoCoefficientApply j1 x = ZMod.stdAddChar j1 * x
    have hangle : p09RootAngle j1 = Real.pi := by
      simp [p09RootAngle, j1, ZMod.cast, ZMod.val, ZMod]
    rw [p09RadixTwoCoefficientApply, p09_stdAddChar_eq_cos_sin, hangle]
    have hj10 : j1 ≠ 0 := by
      change (⟨1, by decide⟩ : Fin 2) ≠ ⟨0, by decide⟩
      decide
    rw [if_neg hj10]
    apply Complex.ext <;> simp

private theorem p09_radixFourCoefficient_exact (j : ZMod 4) (x : ℂ) :
    p09RadixFourCoefficientApply j x = ZMod.stdAddChar j * x := by
  fin_cases j
  · let j0 : ZMod 4 := ⟨0, by decide⟩
    change p09RadixFourCoefficientApply j0 x = ZMod.stdAddChar j0 * x
    have hangle : p09RootAngle j0 = 0 := by
      simp [p09RootAngle, j0, ZMod.cast, ZMod.val, ZMod]
    rw [p09RadixFourCoefficientApply, p09_stdAddChar_eq_cos_sin, hangle]
    rw [if_pos (by rfl : j0 = 0)]
    apply Complex.ext <;> simp
  · let j1 : ZMod 4 := ⟨1, by decide⟩
    change p09RadixFourCoefficientApply j1 x = ZMod.stdAddChar j1 * x
    have hangle : p09RootAngle j1 = Real.pi / 2 := by
      simp [p09RootAngle, j1, ZMod.cast, ZMod.val, ZMod]
      ring
    rw [p09RadixFourCoefficientApply, p09_stdAddChar_eq_cos_sin, hangle]
    have hj10 : j1 ≠ 0 := by
      change (⟨1, by decide⟩ : Fin 4) ≠ ⟨0, by decide⟩
      decide
    rw [if_neg hj10, if_pos (by rfl : j1 = 1)]
    apply Complex.ext <;> simp
  · let j2 : ZMod 4 := ⟨2, by decide⟩
    change p09RadixFourCoefficientApply j2 x = ZMod.stdAddChar j2 * x
    have hangle : p09RootAngle j2 = Real.pi := by
      simp [p09RootAngle, j2, ZMod.cast, ZMod.val, ZMod]
      ring
    rw [p09RadixFourCoefficientApply, p09_stdAddChar_eq_cos_sin, hangle]
    have hj20 : j2 ≠ 0 := by
      change (⟨2, by decide⟩ : Fin 4) ≠ ⟨0, by decide⟩
      decide
    have hj21 : j2 ≠ 1 := by
      change (⟨2, by decide⟩ : Fin 4) ≠ ⟨1, by decide⟩
      decide
    rw [if_neg hj20, if_neg hj21, if_pos (by rfl : j2 = 2)]
    apply Complex.ext <;> simp
  · let j3 : ZMod 4 := ⟨3, by decide⟩
    change p09RadixFourCoefficientApply j3 x = ZMod.stdAddChar j3 * x
    have hangle : p09RootAngle j3 = 3 * Real.pi / 2 := by
      simp [p09RootAngle, j3, ZMod.cast, ZMod.val, ZMod]
      ring
    rw [p09RadixFourCoefficientApply, p09_stdAddChar_eq_cos_sin, hangle]
    rw [show 3 * Real.pi / 2 = Real.pi + Real.pi / 2 by ring,
      Real.cos_add, Real.sin_add]
    have hj30 : j3 ≠ 0 := by
      change (⟨3, by decide⟩ : Fin 4) ≠ ⟨0, by decide⟩
      decide
    have hj31 : j3 ≠ 1 := by
      change (⟨3, by decide⟩ : Fin 4) ≠ ⟨1, by decide⟩
      decide
    have hj32 : j3 ≠ 2 := by
      change (⟨3, by decide⟩ : Fin 4) ≠ ⟨2, by decide⟩
      decide
    rw [if_neg hj30, if_neg hj31, if_neg hj32]
    apply Complex.ext <;> simp

private theorem p09_roundedRadixTwoBlock_error
    (model : P09WilkinsonModel) (x : ZMod 2 → ℂ) (k : ZMod 2) :
    ‖p09RoundedRadixTwoBlock model x k -
        ∑ j : ZMod 2, ZMod.stdAddChar (j * k) * x j‖ ≤
      model.epsilon * ∑ j : ZMod 2, ‖x j‖ := by
  let index : Fin 2 ≃ ZMod 2 := (ZMod.finEquiv 2).toEquiv
  let term : ZMod 2 → ℂ := fun j => p09RadixTwoCoefficientApply (j * k) (x j)
  have hrounded : p09RoundedRadixTwoBlock model x k =
      p09RoundedComplexAdd model (term (index 0)) (term (index 1)) := by
    apply Complex.ext <;>
      simp [p09RoundedRadixTwoBlock, p09RoundedComplexSum,
        recursiveSum, term, index, p09RoundedComplexAdd]
  have hexact : (∑ j : ZMod 2, ZMod.stdAddChar (j * k) * x j) =
      term (index 0) + term (index 1) := by
    rw [← index.sum_comp]
    simp only [Fin.sum_univ_two]
    simp only [term]
    rw [p09_radixTwoCoefficient_exact, p09_radixTwoCoefficient_exact]
  rw [hrounded, hexact]
  have hadd := p09_roundedComplexAdd_error model (term (index 0)) (term (index 1))
  calc
    _ ≤ model.epsilon * (‖term (index 0)‖ + ‖term (index 1)‖) := hadd
    _ = model.epsilon * ∑ j : ZMod 2, ‖x j‖ := by
      rw [← index.sum_comp]
      simp only [Fin.sum_univ_two]
      have hnorm (j : ZMod 2) :
          ‖p09RadixTwoCoefficientApply (j * k) (x j)‖ = ‖x j‖ := by
        rw [p09_radixTwoCoefficient_exact, norm_mul]
        simp
      rw [hnorm, hnorm]

private theorem p09_roundedAddTreeFour_error
    (model : P09WilkinsonModel) (a b c d : ℂ) :
    ‖p09RoundedComplexAdd model
          (p09RoundedComplexAdd model a b)
          (p09RoundedComplexAdd model c d) -
        ((a + b) + (c + d))‖ ≤
      2 * model.epsilon * (‖a‖ + ‖b‖ + ‖c‖ + ‖d‖) +
        model.epsilon ^ 2 * (‖a‖ + ‖b‖ + ‖c‖ + ‖d‖) := by
  let ab := p09RoundedComplexAdd model a b
  let cd := p09RoundedComplexAdd model c d
  have hab := p09_roundedComplexAdd_error model a b
  have hcd := p09_roundedComplexAdd_error model c d
  have hout := p09_roundedComplexAdd_error model ab cd
  have habNorm : ‖ab‖ ≤ (1 + model.epsilon) * (‖a‖ + ‖b‖) := by
    calc
      ‖ab‖ ≤ ‖ab - (a + b)‖ + ‖a + b‖ := by
        have := norm_add_le (ab - (a + b)) (a + b)
        simpa using this
      _ ≤ model.epsilon * (‖a‖ + ‖b‖) + (‖a‖ + ‖b‖) := by
        gcongr
        exact norm_add_le _ _
      _ = (1 + model.epsilon) * (‖a‖ + ‖b‖) := by ring
  have hcdNorm : ‖cd‖ ≤ (1 + model.epsilon) * (‖c‖ + ‖d‖) := by
    calc
      ‖cd‖ ≤ ‖cd - (c + d)‖ + ‖c + d‖ := by
        have := norm_add_le (cd - (c + d)) (c + d)
        simpa using this
      _ ≤ model.epsilon * (‖c‖ + ‖d‖) + (‖c‖ + ‖d‖) := by
        gcongr
        exact norm_add_le _ _
      _ = (1 + model.epsilon) * (‖c‖ + ‖d‖) := by ring
  have hdecomp :
      p09RoundedComplexAdd model ab cd - ((a + b) + (c + d)) =
        (p09RoundedComplexAdd model ab cd - (ab + cd)) +
          (ab - (a + b)) + (cd - (c + d)) := by ring
  rw [hdecomp]
  calc
    _ ≤ ‖p09RoundedComplexAdd model ab cd - (ab + cd)‖ +
          ‖ab - (a + b)‖ + ‖cd - (c + d)‖ := by
      exact (norm_add_le _ _).trans (add_le_add (norm_add_le _ _) le_rfl)
    _ ≤ model.epsilon * (‖ab‖ + ‖cd‖) +
          model.epsilon * (‖a‖ + ‖b‖) +
          model.epsilon * (‖c‖ + ‖d‖) := by
      gcongr
    _ ≤ model.epsilon *
            ((1 + model.epsilon) * (‖a‖ + ‖b‖) +
              (1 + model.epsilon) * (‖c‖ + ‖d‖)) +
          model.epsilon * (‖a‖ + ‖b‖) +
          model.epsilon * (‖c‖ + ‖d‖) := by
      have he := le_of_lt model.epsilon_pos
      gcongr
    _ = 2 * model.epsilon * (‖a‖ + ‖b‖ + ‖c‖ + ‖d‖) +
        model.epsilon ^ 2 * (‖a‖ + ‖b‖ + ‖c‖ + ‖d‖) := by ring

private theorem p09_roundedRadixFourBlock_error
    (model : P09WilkinsonModel) (x : ZMod 4 → ℂ) (k : ZMod 4) :
    ‖p09RoundedRadixFourBlock model x k -
        ∑ j : ZMod 4, ZMod.stdAddChar (j * k) * x j‖ ≤
      2 * model.epsilon * (∑ j : ZMod 4, ‖x j‖) +
        model.epsilon ^ 2 * (∑ j : ZMod 4, ‖x j‖) := by
  let index : Fin 4 ≃ ZMod 4 := (ZMod.finEquiv 4).toEquiv
  let term : Fin 4 → ℂ := fun i =>
    p09RadixFourCoefficientApply (index i * k) (x (index i))
  have hbound := p09_roundedAddTreeFour_error model
    (term 0) (term 1) (term 2) (term 3)
  have hexact : (∑ j : ZMod 4, ZMod.stdAddChar (j * k) * x j) =
      (term 0 + term 1) + (term 2 + term 3) := by
    rw [← index.sum_comp]
    simp only [Fin.sum_univ_four]
    simp only [term]
    simp_rw [p09_radixFourCoefficient_exact]
    ring
  rw [p09RoundedRadixFourBlock, hexact]
  change ‖p09RoundedComplexAdd model
      (p09RoundedComplexAdd model (term 0) (term 1))
      (p09RoundedComplexAdd model (term 2) (term 3)) -
        ((term 0 + term 1) + (term 2 + term 3))‖ ≤ _
  calc
    _ ≤ 2 * model.epsilon *
          (‖term 0‖ + ‖term 1‖ + ‖term 2‖ + ‖term 3‖) +
        model.epsilon ^ 2 *
          (‖term 0‖ + ‖term 1‖ + ‖term 2‖ + ‖term 3‖) := hbound
    _ = 2 * model.epsilon * (∑ j : ZMod 4, ‖x j‖) +
        model.epsilon ^ 2 * (∑ j : ZMod 4, ‖x j‖) := by
      rw [← index.sum_comp]
      simp only [Fin.sum_univ_four]
      have hnorm (i : Fin 4) : ‖term i‖ = ‖x (index i)‖ := by
        simp only [term]
        rw [p09_radixFourCoefficient_exact, norm_mul]
        simp
      simp only [hnorm]

private theorem p09_roundedRadixTwoBlock_error_cast
    {q : ℕ} [NeZero q] (hq : q = 2)
    (model : P09WilkinsonModel) (x : ZMod q → ℂ) (k : ZMod q) :
    ‖p09RoundedRadixTwoBlock model
          (fun j : ZMod 2 => x (hq.symm ▸ j)) (hq ▸ k) -
        ∑ j : ZMod q, ZMod.stdAddChar (j * k) * x j‖ ≤
      model.epsilon * ∑ j : ZMod q, ‖x j‖ := by
  subst q
  simpa using p09_roundedRadixTwoBlock_error model x k

private theorem p09_roundedRadixFourBlock_error_cast
    {q : ℕ} [NeZero q] (hq : q = 4)
    (model : P09WilkinsonModel) (x : ZMod q → ℂ) (k : ZMod q) :
    ‖p09RoundedRadixFourBlock model
          (fun j : ZMod 4 => x (hq.symm ▸ j)) (hq ▸ k) -
        ∑ j : ZMod q, ZMod.stdAddChar (j * k) * x j‖ ≤
      2 * model.epsilon * (∑ j : ZMod q, ‖x j‖) +
        model.epsilon ^ 2 * (∑ j : ZMod q, ‖x j‖) := by
  subst q
  simpa using p09_roundedRadixFourBlock_error model x k

private theorem p09_roundedGenericRadixBlock_error {q : ℕ} [NeZero q]
    (hq2 : 2 ≤ q) (hqne2 : q ≠ 2) (γ : ℝ) (hγ : 0 ≤ γ) :
    ∃ C : ℝ, 0 ≤ C ∧
      ∀ (model : P09WilkinsonModel), model.gamma = γ → model.epsilon ≤ 1 →
      ∀ (x : ZMod q → ℂ) (k : ZMod q),
        ‖p09RoundedGenericRadixBlock model x k -
            ∑ j : ZMod q, ZMod.stdAddChar (j * k) * x j‖ ≤
          (2 * (q + γ)) * model.epsilon * (∑ j, ‖x j‖) +
            C * model.epsilon ^ 2 * (∑ j, ‖x j‖) := by
  rcases p09_roundedComplexSum_error (q := q) with ⟨S, hS, hsum⟩
  let A : ℝ := (3 / 2 : ℝ) * (q - 1 : ℕ)
  let B : ℝ := 3 + 2 * γ
  let D : ℝ := 9 * (1 + γ) ^ 2
  let C : ℝ := A * B + D + S + A * D + S * B + S * D
  have hA : 0 ≤ A := by positivity
  have hB : 0 ≤ B := by dsimp [B]; positivity
  have hD : 0 ≤ D := by positivity
  have hC : 0 ≤ C := by dsimp [C]; positivity
  refine ⟨C, hC, ?_⟩
  intro model hmodelγ he1 x k
  have hprod (j : ZMod q) :
      ‖p09RoundedComplexMul model (p09RoundedRoot model (j * k)) (x j) -
          ZMod.stdAddChar (j * k) * x j‖ ≤
        B * model.epsilon * ‖x j‖ + D * model.epsilon ^ 2 * ‖x j‖ := by
    have hj := p09_roundedRootMul_error model (j * k) (x j) he1
    simpa [B, D, hmodelγ] using hj
  let roundedTerm : ZMod q → ℂ := fun j =>
    p09RoundedComplexMul model (p09RoundedRoot model (j * k)) (x j)
  let exactTerm : ZMod q → ℂ := fun j => ZMod.stdAddChar (j * k) * x j
  let L : ℝ := ∑ j : ZMod q, ‖x j‖
  have hL : 0 ≤ L := by dsimp [L]; positivity
  have hroundedNorm (j : ZMod q) :
      ‖roundedTerm j‖ ≤
        (1 + B * model.epsilon + D * model.epsilon ^ 2) * ‖x j‖ := by
    calc
      ‖roundedTerm j‖ ≤ ‖roundedTerm j - exactTerm j‖ + ‖exactTerm j‖ := by
        have := norm_add_le (roundedTerm j - exactTerm j) (exactTerm j)
        simpa using this
      _ ≤ (B * model.epsilon * ‖x j‖ +
              D * model.epsilon ^ 2 * ‖x j‖) + ‖x j‖ := by
        gcongr
        · simpa [roundedTerm, exactTerm] using hprod j
        · simp [exactTerm]
      _ = (1 + B * model.epsilon + D * model.epsilon ^ 2) * ‖x j‖ := by ring
  have hroundedSum :
      ∑ j : ZMod q, ‖roundedTerm j‖ ≤
        (1 + B * model.epsilon + D * model.epsilon ^ 2) * L := by
    calc
      _ ≤ ∑ j : ZMod q,
          (1 + B * model.epsilon + D * model.epsilon ^ 2) * ‖x j‖ := by
            gcongr with j
            exact hroundedNorm j
      _ = _ := by simp [L, Finset.mul_sum]
  have hproductSum :
      ‖(∑ j, roundedTerm j) - ∑ j, exactTerm j‖ ≤
        B * model.epsilon * L + D * model.epsilon ^ 2 * L := by
    rw [← Finset.sum_sub_distrib]
    calc
      ‖∑ j, (roundedTerm j - exactTerm j)‖ ≤
          ∑ j, ‖roundedTerm j - exactTerm j‖ := norm_sum_le _ _
      _ ≤ ∑ j, (B * model.epsilon * ‖x j‖ +
          D * model.epsilon ^ 2 * ‖x j‖) := by
            gcongr with j
            simpa [roundedTerm, exactTerm] using hprod j
      _ = _ := by simp [L, Finset.sum_add_distrib, Finset.mul_sum]
  have hsumAlg := hsum model he1 roundedTerm
  have hdecomp :
      p09RoundedGenericRadixBlock model x k - ∑ j, exactTerm j =
        (p09RoundedComplexSum model roundedTerm - ∑ j, roundedTerm j) +
          ((∑ j, roundedTerm j) - ∑ j, exactTerm j) := by
    simp only [p09RoundedGenericRadixBlock, roundedTerm, exactTerm]
    ring
  have he := le_of_lt model.epsilon_pos
  have he3 : model.epsilon ^ 3 ≤ model.epsilon ^ 2 := by
    nlinarith [sq_nonneg model.epsilon]
  have he4 : model.epsilon ^ 4 ≤ model.epsilon ^ 2 := by
    nlinarith [sq_nonneg model.epsilon, mul_self_le_mul_self (by positivity) he1]
  have hlead : A + B ≤ 2 * (q + γ) := by
    have hq3 : 3 ≤ q := by omega
    dsimp [A, B]
    rw [Nat.cast_sub (by omega : 1 ≤ q)]
    push_cast
    have hq3r : (3 : ℝ) ≤ (q : ℝ) := by exact_mod_cast hq3
    nlinarith
  rw [show p09RoundedGenericRadixBlock model x k -
        (∑ j : ZMod q, ZMod.stdAddChar (j * k) * x j) =
      p09RoundedGenericRadixBlock model x k - ∑ j, exactTerm j by rfl,
    hdecomp]
  calc
    _ ≤ ‖p09RoundedComplexSum model roundedTerm - ∑ j, roundedTerm j‖ +
          ‖(∑ j, roundedTerm j) - ∑ j, exactTerm j‖ := norm_add_le _ _
    _ ≤ (A * model.epsilon * (∑ j, ‖roundedTerm j‖) +
          S * model.epsilon ^ 2 * (∑ j, ‖roundedTerm j‖)) +
        (B * model.epsilon * L + D * model.epsilon ^ 2 * L) := by
      exact add_le_add (by simpa [A] using hsumAlg) hproductSum
    _ ≤ (A * model.epsilon *
            ((1 + B * model.epsilon + D * model.epsilon ^ 2) * L) +
          S * model.epsilon ^ 2 *
            ((1 + B * model.epsilon + D * model.epsilon ^ 2) * L)) +
        (B * model.epsilon * L + D * model.epsilon ^ 2 * L) := by
      have hfacA : 0 ≤ A * model.epsilon := mul_nonneg hA he
      have hfacS : 0 ≤ S * model.epsilon ^ 2 := mul_nonneg hS (sq_nonneg _)
      gcongr
    _ ≤ (A + B) * model.epsilon * L + C * model.epsilon ^ 2 * L := by
      have h3L := mul_le_mul_of_nonneg_right he3 hL
      have h4L := mul_le_mul_of_nonneg_right he4 hL
      have hAD := mul_le_mul_of_nonneg_left h3L (mul_nonneg hA hD)
      have hSB := mul_le_mul_of_nonneg_left h3L (mul_nonneg hS hB)
      have hSD := mul_le_mul_of_nonneg_left h4L (mul_nonneg hS hD)
      dsimp [C]
      nlinarith
    _ ≤ 2 * (q + γ) * model.epsilon * L + C * model.epsilon ^ 2 * L := by
      have heL : 0 ≤ model.epsilon * L := mul_nonneg he hL
      gcongr

private theorem p09_block_fiber_bound_to_norm
    {n q b : ℕ} [NeZero n] [NeZero q]
    (reindex : Fin b × ZMod q ≃ ZMod n)
    (permutation : ZMod n ≃ ZMod n)
    (x err : ZMod n → ℂ) (F : ℝ) (hF : 0 ≤ F)
    (hpoint : ∀ p : Fin b × ZMod q,
      ‖err (reindex p)‖ ≤
        F * ∑ j : ZMod q, ‖x (permutation (reindex (p.1, j)))‖) :
    p09ComplexNorm2 err ≤ (q : ℝ) * F * p09ComplexNorm2 x := by
  let L : Fin b → ℝ := fun bi =>
    ∑ j : ZMod q, ‖x (permutation (reindex (bi, j)))‖
  have hL (bi : Fin b) : 0 ≤ L bi := by dsimp [L]; positivity
  have herrSq :
      (∑ i : ZMod n, ‖err i‖ ^ 2) ≤
        (q : ℝ) ^ 2 * F ^ 2 * ∑ i : ZMod n, ‖x i‖ ^ 2 := by
    calc
      (∑ i : ZMod n, ‖err i‖ ^ 2) =
          ∑ p : Fin b × ZMod q, ‖err (reindex p)‖ ^ 2 := by
            exact (reindex.sum_comp (fun i => ‖err i‖ ^ 2)).symm
      _ = ∑ bi : Fin b, ∑ k : ZMod q,
          ‖err (reindex (bi, k))‖ ^ 2 := by
            rw [Fintype.sum_prod_type]
      _ ≤ ∑ bi : Fin b, ∑ _k : ZMod q, (F * L bi) ^ 2 := by
            apply Finset.sum_le_sum
            intro bi hbi
            apply Finset.sum_le_sum
            intro k hk
            exact (sq_le_sq₀ (norm_nonneg _) (mul_nonneg hF (hL bi))).2
              (by simpa [L] using hpoint (bi, k))
      _ = ∑ bi : Fin b, (q : ℝ) * (F * L bi) ^ 2 := by
            congr 1 with bi
            rw [Finset.sum_const, Finset.card_univ, ZMod.card, nsmul_eq_mul]
      _ ≤ ∑ bi : Fin b,
          (q : ℝ) * (F ^ 2 * ((q : ℝ) *
            ∑ j : ZMod q, ‖x (permutation (reindex (bi, j)))‖ ^ 2)) := by
            gcongr with bi
            have hc := sq_sum_le_card_mul_sum_sq
              (s := (Finset.univ : Finset (ZMod q)))
              (f := fun j : ZMod q => ‖x (permutation (reindex (bi, j)))‖)
            rw [Finset.card_univ, ZMod.card] at hc
            nlinarith [sq_nonneg F]
      _ = (q : ℝ) ^ 2 * F ^ 2 *
          ∑ p : Fin b × ZMod q, ‖x (permutation (reindex p))‖ ^ 2 := by
            rw [Fintype.sum_prod_type]
            simp only [Finset.mul_sum]
            ring
      _ = (q : ℝ) ^ 2 * F ^ 2 * ∑ i : ZMod n, ‖x i‖ ^ 2 := by
            congr 1
            calc
              (∑ p : Fin b × ZMod q, ‖x (permutation (reindex p))‖ ^ 2) =
                  ∑ z : ZMod n, ‖x (permutation z)‖ ^ 2 :=
                    reindex.sum_comp
                      (fun z : ZMod n => ‖x (permutation z)‖ ^ 2)
              _ = ∑ i : ZMod n, ‖x i‖ ^ 2 :=
                    permutation.sum_comp (fun i : ZMod n => ‖x i‖ ^ 2)
  have herrnon : 0 ≤ p09ComplexNorm2Sq err := by
    unfold p09ComplexNorm2Sq
    positivity
  have hxnon : 0 ≤ p09ComplexNorm2Sq x := by
    unfold p09ComplexNorm2Sq
    positivity
  rw [p09ComplexNorm2, p09ComplexNorm2]
  apply (sq_le_sq₀ (Real.sqrt_nonneg _)
    (mul_nonneg (mul_nonneg (by positivity) hF) (Real.sqrt_nonneg _))).mp
  rw [Real.sq_sqrt herrnon, mul_pow, Real.sq_sqrt hxnon]
  unfold p09ComplexNorm2Sq at *
  nlinarith

private theorem p09_complexNorm2_nonneg {n : ℕ} [NeZero n]
    (x : ZMod n → ℂ) : 0 ≤ p09ComplexNorm2 x := by
  unfold p09ComplexNorm2
  exact Real.sqrt_nonneg _

private theorem p09_mixedRadixBlock_norm_error {n : ℕ} [NeZero n]
    (stage : P09MixedRadixStage n) (γ : ℝ) (hγ : 0 ≤ γ) :
    ∃ C : ℝ, 0 ≤ C ∧
      ∀ (model : P09WilkinsonModel), model.gamma = γ → model.epsilon ≤ 1 →
      ∀ x : ZMod n → ℂ,
        p09ComplexNorm2 (fun i =>
            p09RoundedMixedRadixBlockApply model stage x i -
              p09MixedRadixBlockApply stage x i) ≤
          Real.sqrt (stage.radix : ℝ) *
              p09Alpha stage.radix γ * model.epsilon * p09ComplexNorm2 x +
            C * model.epsilon ^ 2 * p09ComplexNorm2 x := by
  letI : NeZero stage.radix := ⟨stage.radix_ne_zero⟩
  by_cases h2 : stage.radix = 2
  · refine ⟨2, by norm_num, ?_⟩
    intro model hmodelγ he1 x
    let err : ZMod n → ℂ := fun i =>
      p09RoundedMixedRadixBlockApply model stage x i -
        p09MixedRadixBlockApply stage x i
    let F : ℝ := model.epsilon
    have hF : 0 ≤ F := le_of_lt model.epsilon_pos
    have hpoint (p : Fin stage.blockCount × ZMod stage.radix) :
        ‖err (stage.reindex p)‖ ≤
          F * ∑ j : ZMod stage.radix,
            ‖x (stage.permutation (stage.reindex (p.1, j)))‖ := by
      let xq : ZMod stage.radix → ℂ := fun j =>
        x (stage.permutation (stage.reindex (p.1, j)))
      have hb := p09_roundedRadixTwoBlock_error_cast h2 model xq p.2
      simpa [err, F, p09RoundedMixedRadixBlockApply,
        p09MixedRadixBlockApply, h2, xq] using hb
    have hn := p09_block_fiber_bound_to_norm stage.reindex stage.permutation
      x err F hF hpoint
    change p09ComplexNorm2 err ≤ _
    calc
      p09ComplexNorm2 err ≤ (stage.radix : ℝ) * F * p09ComplexNorm2 x := hn
      _ = 2 * model.epsilon * p09ComplexNorm2 x := by rw [h2]; simp [F]
      _ ≤ Real.sqrt (stage.radix : ℝ) * p09Alpha stage.radix γ *
            model.epsilon * p09ComplexNorm2 x +
          2 * model.epsilon ^ 2 * p09ComplexNorm2 x := by
        have hsqrt : Real.sqrt 2 * Real.sqrt 2 = 2 :=
          by simpa [pow_two] using
            (Real.sq_sqrt (by norm_num : (0 : ℝ) ≤ 2))
        rw [h2]
        simp only [p09Alpha, if_pos, Nat.cast_ofNat]
        rw [hsqrt]
        exact le_add_of_nonneg_right
          (mul_nonneg (mul_nonneg (by norm_num) (sq_nonneg _))
            (p09_complexNorm2_nonneg x))
  · by_cases h4 : stage.radix = 4
    · refine ⟨4, by norm_num, ?_⟩
      intro model hmodelγ he1 x
      let err : ZMod n → ℂ := fun i =>
        p09RoundedMixedRadixBlockApply model stage x i -
          p09MixedRadixBlockApply stage x i
      let F : ℝ := 2 * model.epsilon + model.epsilon ^ 2
      have hF : 0 ≤ F := by
        dsimp [F]
        nlinarith [model.epsilon_pos, sq_nonneg model.epsilon]
      have hpoint (p : Fin stage.blockCount × ZMod stage.radix) :
          ‖err (stage.reindex p)‖ ≤
            F * ∑ j : ZMod stage.radix,
              ‖x (stage.permutation (stage.reindex (p.1, j)))‖ := by
        let xq : ZMod stage.radix → ℂ := fun j =>
          x (stage.permutation (stage.reindex (p.1, j)))
        have hb := p09_roundedRadixFourBlock_error_cast h4 model xq p.2
        convert hb using 1 <;>
          simp [err, F, p09RoundedMixedRadixBlockApply,
            p09MixedRadixBlockApply, h2, h4, xq, mul_add] <;> ring
      have hn := p09_block_fiber_bound_to_norm stage.reindex stage.permutation
        x err F hF hpoint
      change p09ComplexNorm2 err ≤ _
      calc
        p09ComplexNorm2 err ≤ (stage.radix : ℝ) * F * p09ComplexNorm2 x := hn
        _ ≤ Real.sqrt (stage.radix : ℝ) * p09Alpha stage.radix γ *
              model.epsilon * p09ComplexNorm2 x +
            4 * model.epsilon ^ 2 * p09ComplexNorm2 x := by
          rw [h4]
          norm_num [F, p09Alpha]
          have he := le_of_lt model.epsilon_pos
          have hx := p09_complexNorm2_nonneg x
          nlinarith [mul_nonneg he hx]
    · rcases p09_roundedGenericRadixBlock_error
          stage.radix_two_le h2 γ hγ with ⟨C0, hC0, hgeneric⟩
      refine ⟨(stage.radix : ℝ) * C0, mul_nonneg (by positivity) hC0, ?_⟩
      intro model hmodelγ he1 x
      let err : ZMod n → ℂ := fun i =>
        p09RoundedMixedRadixBlockApply model stage x i -
          p09MixedRadixBlockApply stage x i
      let F : ℝ := 2 * (stage.radix + γ) * model.epsilon +
        C0 * model.epsilon ^ 2
      have hF : 0 ≤ F := by
        dsimp [F]
        have hq : 0 ≤ (stage.radix : ℝ) := by positivity
        have hsum : 0 ≤ (stage.radix : ℝ) + γ := add_nonneg hq hγ
        exact add_nonneg
          (mul_nonneg (mul_nonneg (by positivity) hsum)
            (le_of_lt model.epsilon_pos))
          (mul_nonneg hC0 (sq_nonneg _))
      have hpoint (p : Fin stage.blockCount × ZMod stage.radix) :
          ‖err (stage.reindex p)‖ ≤
            F * ∑ j : ZMod stage.radix,
              ‖x (stage.permutation (stage.reindex (p.1, j)))‖ := by
        let xq : ZMod stage.radix → ℂ := fun j =>
          x (stage.permutation (stage.reindex (p.1, j)))
        have hb := hgeneric model hmodelγ he1 xq p.2
        have hb' :
            ‖p09RoundedGenericRadixBlock model xq p.2 -
                ∑ j, ZMod.stdAddChar (j * p.2) * xq j‖ ≤
              F * ∑ j, ‖xq j‖ := by
          dsimp [F]
          convert hb using 1 <;> ring
        simpa [err, p09RoundedMixedRadixBlockApply,
          p09MixedRadixBlockApply, h2, h4, xq] using hb'
      have hn := p09_block_fiber_bound_to_norm stage.reindex stage.permutation
        x err F hF hpoint
      change p09ComplexNorm2 err ≤ _
      calc
        p09ComplexNorm2 err ≤ (stage.radix : ℝ) * F * p09ComplexNorm2 x := hn
        _ = Real.sqrt (stage.radix : ℝ) * p09Alpha stage.radix γ *
              model.epsilon * p09ComplexNorm2 x +
            ((stage.radix : ℝ) * C0) * model.epsilon ^ 2 *
              p09ComplexNorm2 x := by
          dsimp [F]
          simp only [p09Alpha, if_neg h2, if_neg h4]
          have hsqrt : Real.sqrt (stage.radix : ℝ) *
              Real.sqrt (stage.radix : ℝ) = (stage.radix : ℝ) :=
            by simpa [pow_two] using
              (Real.sq_sqrt (by positivity : 0 ≤ (stage.radix : ℝ)))
          have hlead : Real.sqrt (stage.radix : ℝ) *
                (2 * Real.sqrt (stage.radix : ℝ) *
                  ((stage.radix : ℝ) + γ)) =
              2 * (stage.radix : ℝ) * ((stage.radix : ℝ) + γ) := by
            calc
              _ = 2 * (Real.sqrt (stage.radix : ℝ) *
                    Real.sqrt (stage.radix : ℝ)) *
                  ((stage.radix : ℝ) + γ) := by ring
              _ = _ := by rw [hsqrt]
          rw [hlead]
          ring

private theorem p09_complexNorm2_eq_euclidean {n : ℕ} [NeZero n]
    (x : ZMod n → ℂ) :
    p09ComplexNorm2 x =
      ‖(WithLp.toLp 2 x : EuclideanSpace ℂ (ZMod n))‖ := by
  rw [EuclideanSpace.norm_eq]
  rfl

private theorem p09_complexNorm2_add_le {n : ℕ} [NeZero n]
    (x y : ZMod n → ℂ) :
    p09ComplexNorm2 (fun i => x i + y i) ≤
      p09ComplexNorm2 x + p09ComplexNorm2 y := by
  rw [p09_complexNorm2_eq_euclidean, p09_complexNorm2_eq_euclidean,
    p09_complexNorm2_eq_euclidean]
  exact norm_add_le _ _

private theorem p09_complexNorm2_pointwise_le {n : ℕ} [NeZero n]
    (x y : ZMod n → ℂ) (h : ∀ i, ‖x i‖ ≤ ‖y i‖) :
    p09ComplexNorm2 x ≤ p09ComplexNorm2 y := by
  simp only [p09ComplexNorm2, p09ComplexNorm2Sq]
  apply Real.sqrt_le_sqrt
  gcongr with i
  exact h i

private theorem p09_complexNorm2_pointwise_factor {n : ℕ} [NeZero n]
    (x y : ZMod n → ℂ) (F : ℝ) (hF : 0 ≤ F)
    (h : ∀ i, ‖x i‖ ≤ F * ‖y i‖) :
    p09ComplexNorm2 x ≤ F * p09ComplexNorm2 y := by
  simp only [p09ComplexNorm2, p09ComplexNorm2Sq]
  have hxsum : 0 ≤ ∑ i : ZMod n, ‖x i‖ ^ 2 := by positivity
  have hysum : 0 ≤ ∑ i : ZMod n, ‖y i‖ ^ 2 := by positivity
  apply (sq_le_sq₀ (Real.sqrt_nonneg _)
    (mul_nonneg hF (Real.sqrt_nonneg _))).mp
  rw [Real.sq_sqrt hxsum, mul_pow, Real.sq_sqrt hysum]
  calc
    (∑ i, ‖x i‖ ^ 2) ≤ ∑ i, (F * ‖y i‖) ^ 2 := by
      gcongr with i
      exact h i
    _ = F ^ 2 * ∑ i, ‖y i‖ ^ 2 := by
      simp only [mul_pow]
      rw [← Finset.mul_sum]

private theorem p09_exactTwiddle_norm {n : ℕ} [NeZero n]
    (stage : P09MixedRadixStage n) (x : ZMod n → ℂ) :
    p09ComplexNorm2 (p09MixedRadixTwiddleApply stage x) = p09ComplexNorm2 x := by
  apply le_antisymm
  · apply p09_complexNorm2_pointwise_le
    intro i
    by_cases h : stage.useTwiddle = true <;>
      simp [p09MixedRadixTwiddleApply, h]
  · apply p09_complexNorm2_pointwise_le
    intro i
    by_cases h : stage.useTwiddle = true <;>
      simp [p09MixedRadixTwiddleApply, h]

private theorem p09_roundedTwiddle_norm_error {n : ℕ} [NeZero n]
    (stage : P09MixedRadixStage n) (γ : ℝ) :
    ∀ (model : P09WilkinsonModel), model.gamma = γ → model.epsilon ≤ 1 →
    ∀ x : ZMod n → ℂ,
      p09ComplexNorm2 (fun i =>
          p09RoundedMixedRadixTwiddleApply model stage x i -
            p09MixedRadixTwiddleApply stage x i) ≤
        (if stage.useTwiddle then (3 + 2 * γ) * model.epsilon +
            9 * (1 + γ) ^ 2 * model.epsilon ^ 2 else 0) *
          p09ComplexNorm2 x := by
  intro model hmodelγ he1 x
  by_cases htw : stage.useTwiddle
  · have hF : 0 ≤ (3 + 2 * γ) * model.epsilon +
        9 * (1 + γ) ^ 2 * model.epsilon ^ 2 := by
      rw [← hmodelγ]
      have hγ := model.gamma_nonneg
      exact add_nonneg
        (mul_nonneg (by positivity) (le_of_lt model.epsilon_pos))
        (mul_nonneg (by positivity) (sq_nonneg _))
    simp only [if_pos htw]
    apply (p09_complexNorm2_pointwise_factor _ _ _ hF)
    intro i
    have hi := p09_roundedRootMul_error model (stage.twiddleExponent i) (x i) he1
    simp [p09RoundedMixedRadixTwiddleApply, p09MixedRadixTwiddleApply,
      htw, hmodelγ]
    rw [hmodelγ] at hi
    convert hi using 1 <;> ring
  · simp only [if_neg htw]
    have hz : (fun i : ZMod n =>
        p09RoundedMixedRadixTwiddleApply model stage x i -
          p09MixedRadixTwiddleApply stage x i) = 0 := by
      funext i
      simp [p09RoundedMixedRadixTwiddleApply, p09MixedRadixTwiddleApply, htw]
    rw [hz]
    simp [p09ComplexNorm2, p09ComplexNorm2Sq]

private theorem p09_plan_stage_norm_error {n : ℕ} [NeZero n]
    (plan : P09MixedRadixFftPlan n) (s : Fin plan.stageCount)
    (γ : ℝ) (hγ : 0 ≤ γ) :
    ∃ C : ℝ, 0 ≤ C ∧
      ∀ (model : P09WilkinsonModel), model.gamma = γ → model.epsilon ≤ 1 →
      ∀ x : ZMod n → ℂ,
        p09ComplexNorm2 (fun i =>
            p09RoundedMixedRadixStageApply model (plan.stage s) x i -
              p09MixedRadixStageApply (plan.stage s) x i) ≤
          Real.sqrt ((plan.stage s).radix : ℝ) *
            (p09Alpha (plan.stage s).radix γ +
              if (plan.stage s).useTwiddle then 3 + 2 * γ else 0) *
              model.epsilon * p09ComplexNorm2 x +
            C * model.epsilon ^ 2 * p09ComplexNorm2 x := by
  rcases p09_mixedRadixBlock_norm_error (plan.stage s) γ hγ with
    ⟨Cb, hCb, hblock⟩
  let A := p09Alpha (plan.stage s).radix γ
  let B := 3 + 2 * γ
  let D := 9 * (1 + γ) ^ 2
  let C := Cb + (if (plan.stage s).useTwiddle then
    D * Real.sqrt ((plan.stage s).radix : ℝ) + B *
      (Real.sqrt ((plan.stage s).radix : ℝ) * A + Cb) +
      D * (Real.sqrt ((plan.stage s).radix : ℝ) * A + Cb) else 0)
  have hA : 0 ≤ A := by
    dsimp [A]
    by_cases h2 : (plan.stage s).radix = 2
    · simp [p09Alpha, h2]
    · by_cases h4 : (plan.stage s).radix = 4
      · simp [p09Alpha, h2, h4]
      · simp [p09Alpha, h2, h4]
        positivity
  have hB : 0 ≤ B := by dsimp [B]; positivity
  have hD : 0 ≤ D := by dsimp [D]; positivity
  have hsqrt : 0 ≤ Real.sqrt ((plan.stage s).radix : ℝ) := Real.sqrt_nonneg _
  have hC : 0 ≤ C := by
    dsimp [C]
    by_cases htw : (plan.stage s).useTwiddle = true
    · rw [if_pos htw]
      positivity
    · rw [if_neg htw]
      simpa using hCb
  refine ⟨C, hC, ?_⟩
  intro model hmodelγ he1 x
  let block := p09MixedRadixBlockApply (plan.stage s) x
  let rblock := p09RoundedMixedRadixBlockApply model (plan.stage s) x
  let blockErr : ZMod n → ℂ := fun i => rblock i - block i
  have hb := hblock model hmodelγ he1 x
  have hb' : p09ComplexNorm2 blockErr ≤
      Real.sqrt ((plan.stage s).radix : ℝ) * A * model.epsilon *
          p09ComplexNorm2 x + Cb * model.epsilon ^ 2 * p09ComplexNorm2 x := by
    simpa [blockErr, block, rblock, A] using hb
  have hblockNorm : p09ComplexNorm2 block =
      Real.sqrt ((plan.stage s).radix : ℝ) * p09ComplexNorm2 x := by
    have hs := plan.stage_norm_scaling s x
    rw [p09MixedRadixStageApply, p09_exactTwiddle_norm] at hs
    simpa [block] using hs
  have hrblockNorm : p09ComplexNorm2 rblock ≤
      (Real.sqrt ((plan.stage s).radix : ℝ) +
        Real.sqrt ((plan.stage s).radix : ℝ) * A * model.epsilon +
        Cb * model.epsilon ^ 2) * p09ComplexNorm2 x := by
    have hdecomp : rblock = fun i => blockErr i + block i := by
      funext i
      simp [blockErr]
    rw [hdecomp]
    calc
      _ ≤ p09ComplexNorm2 blockErr + p09ComplexNorm2 block :=
        p09_complexNorm2_add_le _ _
      _ ≤ (Real.sqrt ((plan.stage s).radix : ℝ) * A * model.epsilon *
              p09ComplexNorm2 x + Cb * model.epsilon ^ 2 * p09ComplexNorm2 x) +
            Real.sqrt ((plan.stage s).radix : ℝ) * p09ComplexNorm2 x := by
          rw [hblockNorm]
          gcongr
      _ = _ := by ring
  have htw := p09_roundedTwiddle_norm_error (plan.stage s) γ
    model hmodelγ he1 rblock
  have hdecomp :
      (fun i => p09RoundedMixedRadixStageApply model (plan.stage s) x i -
          p09MixedRadixStageApply (plan.stage s) x i) =
        fun i =>
          (p09RoundedMixedRadixTwiddleApply model (plan.stage s) rblock i -
            p09MixedRadixTwiddleApply (plan.stage s) rblock i) +
          p09MixedRadixTwiddleApply (plan.stage s) blockErr i := by
    funext i
    simp [p09RoundedMixedRadixStageApply, p09MixedRadixStageApply,
      rblock, blockErr, block, p09MixedRadixTwiddleApply]
    split <;> ring
  rw [hdecomp]
  calc
    _ ≤ p09ComplexNorm2 (fun i =>
          p09RoundedMixedRadixTwiddleApply model (plan.stage s) rblock i -
            p09MixedRadixTwiddleApply (plan.stage s) rblock i) +
        p09ComplexNorm2 (p09MixedRadixTwiddleApply (plan.stage s) blockErr) :=
      p09_complexNorm2_add_le _ _
    _ ≤ (if (plan.stage s).useTwiddle then B * model.epsilon +
            D * model.epsilon ^ 2 else 0) * p09ComplexNorm2 rblock +
          p09ComplexNorm2 blockErr := by
      rw [p09_exactTwiddle_norm]
      by_cases huse : (plan.stage s).useTwiddle = true <;>
        simp [huse, B, D] at htw ⊢ <;> linarith
    _ ≤ (if (plan.stage s).useTwiddle then B * model.epsilon +
            D * model.epsilon ^ 2 else 0) *
          ((Real.sqrt ((plan.stage s).radix : ℝ) +
            Real.sqrt ((plan.stage s).radix : ℝ) * A * model.epsilon +
            Cb * model.epsilon ^ 2) * p09ComplexNorm2 x) +
        (Real.sqrt ((plan.stage s).radix : ℝ) * A * model.epsilon *
          p09ComplexNorm2 x + Cb * model.epsilon ^ 2 * p09ComplexNorm2 x) := by
      have hfac : 0 ≤ (if (plan.stage s).useTwiddle then B * model.epsilon +
          D * model.epsilon ^ 2 else 0) := by
        by_cases huse : (plan.stage s).useTwiddle = true
        · rw [if_pos huse]
          exact add_nonneg
            (mul_nonneg hB (le_of_lt model.epsilon_pos))
            (mul_nonneg hD (sq_nonneg _))
        · rw [if_neg huse]
      exact add_le_add (mul_le_mul_of_nonneg_left hrblockNorm hfac) hb'
    _ ≤ Real.sqrt ((plan.stage s).radix : ℝ) *
          (A + if (plan.stage s).useTwiddle then B else 0) *
            model.epsilon * p09ComplexNorm2 x +
          C * model.epsilon ^ 2 * p09ComplexNorm2 x := by
      have he := le_of_lt model.epsilon_pos
      have he3 : model.epsilon ^ 3 ≤ model.epsilon ^ 2 := by
        nlinarith [sq_nonneg model.epsilon]
      have he4 : model.epsilon ^ 4 ≤ model.epsilon ^ 2 := by
        nlinarith [sq_nonneg model.epsilon,
          mul_self_le_mul_self he he1]
      have hx := p09_complexNorm2_nonneg x
      dsimp [C]
      split <;> simp_all only [Bool.false_eq_true, ↓reduceIte]
      · have h3x := mul_le_mul_of_nonneg_right he3 hx
        have h4x := mul_le_mul_of_nonneg_right he4 hx
        have hBA := mul_le_mul_of_nonneg_left h3x (mul_nonneg hB hA)
        have hBC := mul_le_mul_of_nonneg_left h3x (mul_nonneg hB hCb)
        have hDA := mul_le_mul_of_nonneg_left h3x (mul_nonneg hD hA)
        have hDC := mul_le_mul_of_nonneg_left h4x (mul_nonneg hD hCb)
        nlinarith
      · nlinarith

private theorem p09_mixedRadixStage_sub {n : ℕ} [NeZero n]
    (stage : P09MixedRadixStage n) (x y : ZMod n → ℂ) :
    p09MixedRadixStageApply stage (fun i => x i - y i) =
      fun i => p09MixedRadixStageApply stage x i -
        p09MixedRadixStageApply stage y i := by
  funext i
  simp only [p09MixedRadixStageApply, p09MixedRadixTwiddleApply,
    p09MixedRadixBlockApply]
  split
  · rw [← mul_sub]
    congr 1
    rw [← Finset.sum_sub_distrib]
    apply Finset.sum_congr rfl
    intro j hj
    rw [mul_sub]
  · rw [← Finset.sum_sub_distrib]
    apply Finset.sum_congr rfl
    intro j hj
    rw [mul_sub]

private noncomputable def p09ExactStageFold {n r : ℕ} [NeZero n]
    (plan : P09MixedRadixFftPlan n) (indices : List (Fin r))
    (embed : Fin r → Fin plan.stageCount) (x : ZMod n → ℂ) : ZMod n → ℂ :=
  indices.foldl (fun state i =>
    p09MixedRadixStageApply (plan.stage (embed i)) state) x

private noncomputable def p09RoundedStageFold {n r : ℕ} [NeZero n]
    (plan : P09MixedRadixFftPlan n) (model : P09WilkinsonModel)
    (indices : List (Fin r)) (embed : Fin r → Fin plan.stageCount)
    (x : ZMod n → ℂ) : ZMod n → ℂ :=
  indices.foldl (fun state i =>
    p09RoundedMixedRadixStageApply model (plan.stage (embed i)) state) x

private theorem p09_exactStageFold_sub {n r : ℕ} [NeZero n]
    (plan : P09MixedRadixFftPlan n) (indices : List (Fin r))
    (embed : Fin r → Fin plan.stageCount) (x y : ZMod n → ℂ) :
    p09ExactStageFold plan indices embed (fun i => x i - y i) =
      fun i => p09ExactStageFold plan indices embed x i -
        p09ExactStageFold plan indices embed y i := by
  induction indices generalizing x y with
  | nil => rfl
  | cons s tail ih =>
      change p09ExactStageFold plan tail embed
          (p09MixedRadixStageApply (plan.stage (embed s))
            (fun i => x i - y i)) =
        fun i => p09ExactStageFold plan tail embed
            (p09MixedRadixStageApply (plan.stage (embed s)) x) i -
          p09ExactStageFold plan tail embed
            (p09MixedRadixStageApply (plan.stage (embed s)) y) i
      rw [p09_mixedRadixStage_sub]
      exact ih _ _

private def p09FoldSecondCoeff {ι : Type*}
    (scale leading remainder : ι → ℝ) : List ι → ℝ
  | [] => 0
  | i :: tail =>
      let P := (tail.map scale).prod
      let S := (tail.map leading).sum
      let Ct := p09FoldSecondCoeff scale leading remainder tail
      P * S * scale i * leading i + P * S * remainder i +
        Ct * scale i + Ct * scale i * leading i + Ct * remainder i +
        P * remainder i

private theorem p09FoldSecondCoeff_nonneg {ι : Type*}
    (scale leading remainder : ι → ℝ)
    (hscale : ∀ i, 0 ≤ scale i) (hleading : ∀ i, 0 ≤ leading i)
    (hremainder : ∀ i, 0 ≤ remainder i) (indices : List ι) :
    0 ≤ p09FoldSecondCoeff scale leading remainder indices := by
  induction indices with
  | nil => simp [p09FoldSecondCoeff]
  | cons i tail ih =>
      simp only [p09FoldSecondCoeff]
      have hP : 0 ≤ (tail.map scale).prod := by
        exact List.prod_nonneg (fun x hx => by
          rcases List.mem_map.mp hx with ⟨j, hj, rfl⟩
          exact hscale j)
      have hS : 0 ≤ (tail.map leading).sum := by
        exact List.sum_nonneg (fun x hx => by
          rcases List.mem_map.mp hx with ⟨j, hj, rfl⟩
          exact hleading j)
      have h1 : 0 ≤ (tail.map scale).prod * (tail.map leading).sum *
          scale i * leading i :=
        mul_nonneg (mul_nonneg (mul_nonneg hP hS) (hscale i)) (hleading i)
      have h2 : 0 ≤ (tail.map scale).prod * (tail.map leading).sum *
          remainder i :=
        mul_nonneg (mul_nonneg hP hS) (hremainder i)
      have h3 : 0 ≤ p09FoldSecondCoeff scale leading remainder tail *
          scale i := mul_nonneg ih (hscale i)
      have h4 : 0 ≤ p09FoldSecondCoeff scale leading remainder tail *
          scale i * leading i :=
        mul_nonneg (mul_nonneg ih (hscale i)) (hleading i)
      have h5 : 0 ≤ p09FoldSecondCoeff scale leading remainder tail *
          remainder i := mul_nonneg ih (hremainder i)
      have h6 : 0 ≤ (tail.map scale).prod * remainder i :=
        mul_nonneg hP (hremainder i)
      linarith

private theorem p09_exactStageFold_norm {n r : ℕ} [NeZero n]
    (plan : P09MixedRadixFftPlan n) (indices : List (Fin r))
    (embed : Fin r → Fin plan.stageCount) (x : ZMod n → ℂ) :
    p09ComplexNorm2 (p09ExactStageFold plan indices embed x) =
      (indices.map (fun i =>
        Real.sqrt ((plan.stage (embed i)).radix : ℝ))).prod *
        p09ComplexNorm2 x := by
  induction indices generalizing x with
  | nil => simp [p09ExactStageFold]
  | cons i tail ih =>
      change p09ComplexNorm2
          (p09ExactStageFold plan tail embed
            (p09MixedRadixStageApply (plan.stage (embed i)) x)) =
        Real.sqrt ((plan.stage (embed i)).radix : ℝ) *
          (tail.map (fun j =>
            Real.sqrt ((plan.stage (embed j)).radix : ℝ))).prod *
          p09ComplexNorm2 x
      rw [ih, plan.stage_norm_scaling]
      ring

private theorem p09_stageFold_error_bound {n r : ℕ} [NeZero n]
    (plan : P09MixedRadixFftPlan n) (model : P09WilkinsonModel)
    (indices : List (Fin r)) (embed : Fin r → Fin plan.stageCount)
    (leading remainder : Fin r → ℝ)
    (hleading : ∀ i, 0 ≤ leading i) (hremainder : ∀ i, 0 ≤ remainder i)
    (he1 : model.epsilon ≤ 1)
    (hloc : ∀ i x,
      p09ComplexNorm2 (fun k =>
          p09RoundedMixedRadixStageApply model (plan.stage (embed i)) x k -
            p09MixedRadixStageApply (plan.stage (embed i)) x k) ≤
        Real.sqrt ((plan.stage (embed i)).radix : ℝ) * leading i *
            model.epsilon * p09ComplexNorm2 x +
          remainder i * model.epsilon ^ 2 * p09ComplexNorm2 x)
    (x : ZMod n → ℂ) :
    p09ComplexNorm2 (fun k =>
        p09RoundedStageFold plan model indices embed x k -
          p09ExactStageFold plan indices embed x k) ≤
      (indices.map (fun i =>
          Real.sqrt ((plan.stage (embed i)).radix : ℝ))).prod *
        (indices.map leading).sum * model.epsilon * p09ComplexNorm2 x +
      p09FoldSecondCoeff
          (fun i => Real.sqrt ((plan.stage (embed i)).radix : ℝ))
          leading remainder indices * model.epsilon ^ 2 * p09ComplexNorm2 x := by
  induction indices generalizing x with
  | nil =>
      simp [p09RoundedStageFold, p09ExactStageFold, p09ComplexNorm2,
        p09ComplexNorm2Sq, p09FoldSecondCoeff]
  | cons i tail ih =>
      let scale : Fin r → ℝ := fun j =>
        Real.sqrt ((plan.stage (embed j)).radix : ℝ)
      let P := (tail.map scale).prod
      let S := (tail.map leading).sum
      let Ct := p09FoldSecondCoeff scale leading remainder tail
      let rx := p09RoundedMixedRadixStageApply model (plan.stage (embed i)) x
      let tx := p09MixedRadixStageApply (plan.stage (embed i)) x
      let localErr : ZMod n → ℂ := fun k => rx k - tx k
      have hscale (j : Fin r) : 0 ≤ scale j := Real.sqrt_nonneg _
      have hP : 0 ≤ P := by
        dsimp [P]
        exact List.prod_nonneg (fun z hz => by
          rcases List.mem_map.mp hz with ⟨j, hj, rfl⟩
          exact hscale j)
      have hS : 0 ≤ S := by
        dsimp [S]
        exact List.sum_nonneg (fun z hz => by
          rcases List.mem_map.mp hz with ⟨j, hj, rfl⟩
          exact hleading j)
      have hCt : 0 ≤ Ct := by
        exact p09FoldSecondCoeff_nonneg scale leading remainder
          hscale hleading hremainder tail
      have hlocal := hloc i x
      have hlocal' : p09ComplexNorm2 localErr ≤
          scale i * leading i * model.epsilon * p09ComplexNorm2 x +
            remainder i * model.epsilon ^ 2 * p09ComplexNorm2 x := by
        simpa [localErr, rx, tx, scale] using hlocal
      have hrx : p09ComplexNorm2 rx ≤
          (scale i + scale i * leading i * model.epsilon +
            remainder i * model.epsilon ^ 2) * p09ComplexNorm2 x := by
        have hdecomp : rx = fun k => localErr k + tx k := by
          funext k
          simp [localErr]
        rw [hdecomp]
        calc
          _ ≤ p09ComplexNorm2 localErr + p09ComplexNorm2 tx :=
            p09_complexNorm2_add_le _ _
          _ ≤ (scale i * leading i * model.epsilon * p09ComplexNorm2 x +
                remainder i * model.epsilon ^ 2 * p09ComplexNorm2 x) +
              scale i * p09ComplexNorm2 x := by
            rw [show p09ComplexNorm2 tx = scale i * p09ComplexNorm2 x by
              simpa [tx, scale] using plan.stage_norm_scaling (embed i) x]
            gcongr
          _ = _ := by ring
      have htailRound := ih rx
      have htailExactErr :
          p09ComplexNorm2 (fun k =>
              p09ExactStageFold plan tail embed rx k -
                p09ExactStageFold plan tail embed tx k) =
            P * p09ComplexNorm2 localErr := by
        rw [← p09_exactStageFold_sub]
        simpa [P, scale, localErr] using
          p09_exactStageFold_norm plan tail embed localErr
      have hdecomp :
          (fun k => p09RoundedStageFold plan model (i :: tail) embed x k -
            p09ExactStageFold plan (i :: tail) embed x k) =
          fun k =>
            (p09RoundedStageFold plan model tail embed rx k -
              p09ExactStageFold plan tail embed rx k) +
            (p09ExactStageFold plan tail embed rx k -
              p09ExactStageFold plan tail embed tx k) := by
        funext k
        simp only [p09RoundedStageFold, p09ExactStageFold, List.foldl_cons]
        simp only [rx, tx]
        ring
      rw [hdecomp]
      have he := le_of_lt model.epsilon_pos
      have he3 : model.epsilon ^ 3 ≤ model.epsilon ^ 2 := by
        nlinarith [sq_nonneg model.epsilon]
      have he4 : model.epsilon ^ 4 ≤ model.epsilon ^ 2 := by
        nlinarith [sq_nonneg model.epsilon, mul_self_le_mul_self he he1]
      have hx := p09_complexNorm2_nonneg x
      calc
        _ ≤ p09ComplexNorm2 (fun k =>
              p09RoundedStageFold plan model tail embed rx k -
                p09ExactStageFold plan tail embed rx k) +
            p09ComplexNorm2 (fun k =>
              p09ExactStageFold plan tail embed rx k -
                p09ExactStageFold plan tail embed tx k) :=
              p09_complexNorm2_add_le _ _
        _ ≤ (P * S * model.epsilon * p09ComplexNorm2 rx +
              Ct * model.epsilon ^ 2 * p09ComplexNorm2 rx) +
            P * p09ComplexNorm2 localErr := by
          rw [htailExactErr]
          exact add_le_add
            (by simpa [P, S, Ct, scale] using htailRound)
            (le_refl (P * p09ComplexNorm2 localErr))
        _ ≤ (P * S * model.epsilon *
              ((scale i + scale i * leading i * model.epsilon +
                remainder i * model.epsilon ^ 2) * p09ComplexNorm2 x) +
              Ct * model.epsilon ^ 2 *
              ((scale i + scale i * leading i * model.epsilon +
                remainder i * model.epsilon ^ 2) * p09ComplexNorm2 x)) +
            P * (scale i * leading i * model.epsilon * p09ComplexNorm2 x +
              remainder i * model.epsilon ^ 2 * p09ComplexNorm2 x) := by
          have hPS : 0 ≤ P * S * model.epsilon := by positivity
          have hCtE : 0 ≤ Ct * model.epsilon ^ 2 := by positivity
          exact add_le_add
            (add_le_add
              (mul_le_mul_of_nonneg_left hrx hPS)
              (mul_le_mul_of_nonneg_left hrx hCtE))
            (mul_le_mul_of_nonneg_left hlocal' hP)
        _ ≤ ((i :: tail).map scale).prod *
              ((i :: tail).map leading).sum * model.epsilon *
                p09ComplexNorm2 x +
            p09FoldSecondCoeff scale leading remainder (i :: tail) *
              model.epsilon ^ 2 * p09ComplexNorm2 x := by
          have h3x := mul_le_mul_of_nonneg_right he3 hx
          have h4x := mul_le_mul_of_nonneg_right he4 hx
          have hPSR := mul_le_mul_of_nonneg_left h3x
            (mul_nonneg (mul_nonneg hP hS) (hremainder i))
          have hCtA := mul_le_mul_of_nonneg_left h3x
            (mul_nonneg (mul_nonneg hCt (hscale i)) (hleading i))
          have hCtR := mul_le_mul_of_nonneg_left h4x
            (mul_nonneg hCt (hremainder i))
          simp only [List.map_cons, List.prod_cons, List.sum_cons,
            p09FoldSecondCoeff]
          dsimp [P, S, Ct]
          nlinarith
        _ = _ := by rfl

private theorem p09_exactFold_all {n : ℕ} [NeZero n]
    (plan : P09MixedRadixFftPlan n) (x : ZMod n → ℂ) :
    p09ExactStageFold plan (List.ofFn id) id x =
      p09ApplyMixedRadixStages plan.stage x := by
  simp [p09ExactStageFold, p09ApplyMixedRadixStages, List.ofFn_eq_map,
    List.foldl_map]

private theorem p09_roundedFold_all {n : ℕ} [NeZero n]
    (plan : P09MixedRadixFftPlan n) (model : P09WilkinsonModel)
    (x : ZMod n → ℂ) :
    p09RoundedStageFold plan model (List.ofFn id) id x =
      p09ApplyRoundedMixedRadixStages model plan.stage x := by
  simp [p09RoundedStageFold, p09ApplyRoundedMixedRadixStages,
    List.ofFn_eq_map, List.foldl_map]

private theorem p09_permute_complexNorm2 {n : ℕ} [NeZero n]
    (e : ZMod n ≃ ZMod n) (x : ZMod n → ℂ) :
    p09ComplexNorm2 (p09Permute e x) = p09ComplexNorm2 x := by
  unfold p09ComplexNorm2 p09ComplexNorm2Sq p09Permute
  congr 1
  exact e.sum_comp (fun i => ‖x i‖ ^ 2)

private theorem p09_sum_before_last (n : ℕ) (B : ℝ) :
    (∑ i : Fin n, if i.val + 1 < n then B else 0) = (n - 1 : ℕ) * B := by
  calc
    (∑ i : Fin n, if i.val + 1 < n then B else 0) =
        ∑ i : Fin n, if i.val < n - 1 then B else 0 := by
      apply Finset.sum_congr rfl
      intro i hi
      have hi_lt : i.val < n := i.isLt
      have hiff : i.val + 1 < n ↔ i.val < n - 1 := by omega
      rw [if_congr hiff rfl rfl]
    _ = ((Finset.univ.filter (fun i : Fin n => i.val < n - 1)).card : ℝ) * B := by
      simp [Finset.sum_ite]
    _ = (n - 1 : ℕ) * B := by
      rw [Fin.card_filter_val_lt]
      simp

private theorem p09_stage_leading_sum {n : ℕ} [NeZero n]
    (plan : P09MixedRadixFftPlan n) (γ : ℝ) :
    ∑ i : Fin plan.stageCount,
        (p09Alpha (plan.stage i).radix γ +
          if (plan.stage i).useTwiddle then 3 + 2 * γ else 0) =
      p09K plan γ := by
  unfold p09K
  rw [Finset.sum_add_distrib]
  congr 1
  calc
    (∑ i : Fin plan.stageCount,
        if (plan.stage i).useTwiddle then 3 + 2 * γ else 0) =
        ∑ i : Fin plan.stageCount,
          if i.val + 1 < plan.stageCount then 3 + 2 * γ else 0 := by
      apply Finset.sum_congr rfl
      intro i hi
      rw [plan.twiddle_pattern]
      simp
    _ = (plan.stageCount - 1 : ℕ) * (3 + 2 * γ) :=
      p09_sum_before_last plan.stageCount (3 + 2 * γ)
    _ = ((plan.stageCount : ℝ) - 1) * (3 + 2 * γ) := by
      congr 1
      have hsc := plan.stageCount_pos
      rw [Nat.cast_sub (by omega : 1 ≤ plan.stageCount)]
      norm_num

private theorem p09_stage_scale_product {n : ℕ} [NeZero n]
    (plan : P09MixedRadixFftPlan n) :
    ∏ i : Fin plan.stageCount,
        Real.sqrt ((plan.stage i).radix : ℝ) = Real.sqrt (n : ℝ) := by
  rw [← Real.sqrt_prod Finset.univ]
  · congr 1
    norm_cast
    exact plan.order_factorization
  · intro i hi
    positivity

private noncomputable def p09StageRemainder {n : ℕ} [NeZero n]
    (plan : P09MixedRadixFftPlan n) (γ : ℝ) (hγ : 0 ≤ γ)
    (i : Fin plan.stageCount) : ℝ :=
  Classical.choose (p09_plan_stage_norm_error plan i γ hγ)

private theorem p09StageRemainder_nonneg {n : ℕ} [NeZero n]
    (plan : P09MixedRadixFftPlan n) (γ : ℝ) (hγ : 0 ≤ γ)
    (i : Fin plan.stageCount) :
    0 ≤ p09StageRemainder plan γ hγ i :=
  (Classical.choose_spec (p09_plan_stage_norm_error plan i γ hγ)).1

private theorem p09StageRemainder_bound {n : ℕ} [NeZero n]
    (plan : P09MixedRadixFftPlan n) (γ : ℝ) (hγ : 0 ≤ γ)
    (i : Fin plan.stageCount) (model : P09WilkinsonModel)
    (hmodelγ : model.gamma = γ) (he1 : model.epsilon ≤ 1)
    (x : ZMod n → ℂ) :
    p09ComplexNorm2 (fun k =>
        p09RoundedMixedRadixStageApply model (plan.stage i) x k -
          p09MixedRadixStageApply (plan.stage i) x k) ≤
      Real.sqrt ((plan.stage i).radix : ℝ) *
          (p09Alpha (plan.stage i).radix γ +
            if (plan.stage i).useTwiddle then 3 + 2 * γ else 0) *
          model.epsilon * p09ComplexNorm2 x +
        p09StageRemainder plan γ hγ i * model.epsilon ^ 2 *
          p09ComplexNorm2 x :=
  (Classical.choose_spec (p09_plan_stage_norm_error plan i γ hγ)).2
    model hmodelγ he1 x

private theorem p09Alpha_nonneg (q : ℕ) (γ : ℝ) (hγ : 0 ≤ γ) :
    0 ≤ p09Alpha q γ := by
  unfold p09Alpha
  split
  · positivity
  split
  · norm_num
  · positivity

private theorem p09_fft_norm_error_bound {n : ℕ} [NeZero n]
    (plan : P09MixedRadixFftPlan n) (γ : ℝ) (hγ : 0 ≤ γ) :
    ∃ C : ℝ, 0 ≤ C ∧
      ∀ (model : P09WilkinsonModel), model.gamma = γ →
        model.epsilon ≤ 1 → ∀ x : ZMod n → ℂ,
        p09ComplexNorm2 (fun k =>
            p09RoundedFftApply plan model x k - p09FourierTransform x k) ≤
          Real.sqrt (n : ℝ) * p09K plan γ * model.epsilon *
              p09ComplexNorm2 x +
            C * model.epsilon ^ 2 * p09ComplexNorm2 x := by
  let leading : Fin plan.stageCount → ℝ := fun i =>
    p09Alpha (plan.stage i).radix γ +
      if (plan.stage i).useTwiddle then 3 + 2 * γ else 0
  let remainder : Fin plan.stageCount → ℝ :=
    p09StageRemainder plan γ hγ
  let scale : Fin plan.stageCount → ℝ := fun i =>
    Real.sqrt ((plan.stage i).radix : ℝ)
  let indices : List (Fin plan.stageCount) := List.ofFn id
  let C := p09FoldSecondCoeff scale leading remainder indices
  have hleading (i : Fin plan.stageCount) : 0 ≤ leading i := by
    dsimp [leading]
    apply add_nonneg (p09Alpha_nonneg _ _ hγ)
    split
    · positivity
    · norm_num
  have hremainder (i : Fin plan.stageCount) : 0 ≤ remainder i := by
    exact p09StageRemainder_nonneg plan γ hγ i
  have hscale (i : Fin plan.stageCount) : 0 ≤ scale i := by
    exact Real.sqrt_nonneg _
  have hC : 0 ≤ C := by
    exact p09FoldSecondCoeff_nonneg scale leading remainder
      hscale hleading hremainder indices
  refine ⟨C, hC, ?_⟩
  intro model hmodelγ he1 x
  have hfold := p09_stageFold_error_bound plan model indices id
    leading remainder hleading hremainder he1
    (fun i z => by
      simpa [leading, remainder] using
        p09StageRemainder_bound plan γ hγ i model hmodelγ he1 z) x
  have hprod : (indices.map scale).prod = Real.sqrt (n : ℝ) := by
    dsimp [indices]
    rw [← List.ofFn_comp']
    rw [Fin.prod_ofFn]
    exact p09_stage_scale_product plan
  have hsum : (indices.map leading).sum = p09K plan γ := by
    dsimp [indices]
    rw [← List.ofFn_comp']
    rw [Fin.sum_ofFn]
    exact p09_stage_leading_sum plan γ
  have hraw :
      p09ComplexNorm2 (fun k =>
          p09RoundedStageFold plan model indices id x k -
            p09ExactStageFold plan indices id x k) ≤
        Real.sqrt (n : ℝ) * p09K plan γ * model.epsilon *
            p09ComplexNorm2 x +
          C * model.epsilon ^ 2 * p09ComplexNorm2 x := by
    simpa [scale, C, hprod, hsum] using hfold
  have herr :
      (fun k => p09RoundedFftApply plan model x k -
          p09FourierTransform x k) =
        p09Permute plan.finalPermutation (fun k =>
          p09RoundedStageFold plan model indices id x k -
            p09ExactStageFold plan indices id x k) := by
    funext k
    rw [← plan.exact_factorization x]
    simp only [p09RoundedFftApply, p09Permute]
    rw [← p09_roundedFold_all, ← p09_exactFold_all]
  rw [herr, p09_permute_complexNorm2]
  exact hraw

private abbrev P09MultiFiberBase {m : ℕ}
    (axis : Fin m → P09FftAxis) (i : Fin m) :=
  {index : P09MultiIndex axis // index i = 0}

private noncomputable def p09MultiFiberEquiv {m : ℕ}
    (axis : Fin m → P09FftAxis) (i : Fin m) :
    P09MultiFiberBase axis i × ZMod (axis i).order ≃ P09MultiIndex axis where
  toFun p := Function.update p.1.1 i p.2
  invFun index :=
    (⟨Function.update index i 0, by simp⟩, index i)
  left_inv := by
    intro p
    apply Prod.ext
    · apply Subtype.ext
      funext k
      by_cases hki : k = i
      · subst k
        simp [p.1.property]
      · simp [hki]
    · simp
  right_inv := by
    intro index
    funext k
    by_cases hki : k = i
    · subst k
      simp
    · simp [hki]

private theorem p09_multiNorm2_nonneg {m : ℕ}
    {axis : Fin m → P09FftAxis} (x : P09MultiArray axis) :
    0 ≤ p09MultiNorm2 x := by
  unfold p09MultiNorm2
  exact norm_nonneg _

private theorem p09_multiNorm2_sq_fiber {m : ℕ}
    (axis : Fin m → P09FftAxis) (i : Fin m)
    (x : P09MultiArray axis) :
    p09MultiNorm2 x ^ 2 =
      ∑ b : P09MultiFiberBase axis i,
        ∑ j : ZMod (axis i).order,
          ‖x (Function.update b.1 i j)‖ ^ 2 := by
  unfold p09MultiNorm2
  rw [EuclideanSpace.norm_sq_eq]
  change (∑ index : P09MultiIndex axis, ‖x index‖ ^ 2) = _
  calc
    _ = ∑ p : P09MultiFiberBase axis i × ZMod (axis i).order,
        ‖x (p09MultiFiberEquiv axis i p)‖ ^ 2 :=
      ((p09MultiFiberEquiv axis i).sum_comp
        (fun index => ‖x index‖ ^ 2)).symm
    _ = _ := Fintype.sum_prod_type _

private theorem p09_complexNorm2_sq_eq {n : ℕ} [NeZero n]
    (x : ZMod n → ℂ) :
    p09ComplexNorm2 x ^ 2 = ∑ i : ZMod n, ‖x i‖ ^ 2 := by
  unfold p09ComplexNorm2 p09ComplexNorm2Sq
  rw [Real.sq_sqrt]
  positivity

private theorem p09_multiNorm2_of_fiber_bound {m : ℕ}
    (axis : Fin m → P09FftAxis) (i : Fin m)
    (x y : P09MultiArray axis) (L : ℝ) (hL : 0 ≤ L)
    (hfiber : ∀ b : P09MultiFiberBase axis i,
      p09ComplexNorm2 (fun j => y (Function.update b.1 i j)) ≤
        L * p09ComplexNorm2 (fun j => x (Function.update b.1 i j))) :
    p09MultiNorm2 y ≤ L * p09MultiNorm2 x := by
  have hsq : p09MultiNorm2 y ^ 2 ≤ (L * p09MultiNorm2 x) ^ 2 := by
    rw [p09_multiNorm2_sq_fiber axis i y, mul_pow,
      p09_multiNorm2_sq_fiber axis i x, Finset.mul_sum]
    apply Finset.sum_le_sum
    intro b hb
    rw [← p09_complexNorm2_sq_eq,
      ← p09_complexNorm2_sq_eq]
    simpa [mul_pow] using
      ((sq_le_sq₀ (p09_complexNorm2_nonneg _)
        (mul_nonneg hL (p09_complexNorm2_nonneg _))).2 (hfiber b))
  exact (sq_le_sq₀ (p09_multiNorm2_nonneg y)
    (mul_nonneg hL (p09_multiNorm2_nonneg x))).1 hsq

private theorem p09_multiCardinality_pos {m : ℕ}
    (axis : Fin m → P09FftAxis) : 0 < p09MultiCardinality axis := by
  unfold p09MultiCardinality
  exact Finset.prod_pos fun i hi => (axis i).order_pos

private theorem p09_multiRms_of_norm_bound {m : ℕ}
    (axis : Fin m → P09FftAxis) (x y : P09MultiArray axis)
    (L : ℝ) (h : p09MultiNorm2 y ≤ L * p09MultiNorm2 x) :
    p09MultiRms y ≤ L * p09MultiRms x := by
  unfold p09MultiRms
  have hden : 0 < Real.sqrt (p09MultiCardinality axis : ℝ) := by
    apply Real.sqrt_pos.2
    exact_mod_cast p09_multiCardinality_pos axis
  apply (div_le_iff₀ hden).2
  calc
    p09MultiNorm2 y ≤ L * p09MultiNorm2 x := h
    _ = (L * (p09MultiNorm2 x /
        Real.sqrt (p09MultiCardinality axis : ℝ))) *
          Real.sqrt (p09MultiCardinality axis : ℝ) := by
      field_simp

private theorem p09K_nonneg {n : ℕ} [NeZero n]
    (plan : P09MixedRadixFftPlan n) (γ : ℝ) (hγ : 0 ≤ γ) :
    0 ≤ p09K plan γ := by
  rw [← p09_stage_leading_sum plan γ]
  exact Finset.sum_nonneg fun i hi =>
    add_nonneg (p09Alpha_nonneg _ _ hγ) (by split <;> positivity)

private theorem p09_coordinate_rms_error_bound {m : ℕ}
    (axis : Fin m → P09FftAxis) (i : Fin m)
    (γ : ℝ) (hγ : 0 ≤ γ) :
    ∃ C : ℝ, 0 ≤ C ∧
      ∀ (model : P09WilkinsonModel), model.gamma = γ →
        model.epsilon ≤ 1 → ∀ x : P09MultiArray axis,
        p09MultiRms (p09MultiVecSub
            (p09RoundedCoordinateTransform axis i model x)
            (p09CoordinateTransform axis i x)) ≤
          Real.sqrt ((axis i).order : ℝ) *
            (p09AxisK (axis i) γ * model.epsilon +
              C * model.epsilon ^ 2) * p09MultiRms x := by
  rcases p09_fft_norm_error_bound (axis i).plan γ hγ with
    ⟨C, hC, hfft⟩
  refine ⟨C, hC, ?_⟩
  intro model hmodelγ he1 x
  let y := p09MultiVecSub
    (p09RoundedCoordinateTransform axis i model x)
    (p09CoordinateTransform axis i x)
  let L := Real.sqrt ((axis i).order : ℝ) *
      p09AxisK (axis i) γ * model.epsilon + C * model.epsilon ^ 2
  have hK : 0 ≤ p09AxisK (axis i) γ :=
    p09K_nonneg (axis i).plan γ hγ
  have hL : 0 ≤ L := by
    dsimp [L]
    exact add_nonneg
      (mul_nonneg (mul_nonneg (Real.sqrt_nonneg _) hK)
        (le_of_lt model.epsilon_pos))
      (mul_nonneg hC (sq_nonneg _))
  have hnorm : p09MultiNorm2 y ≤ L * p09MultiNorm2 x := by
    apply p09_multiNorm2_of_fiber_bound axis i x y L hL
    intro b
    have hb := hfft model hmodelγ he1
      (fun j => x (Function.update b.1 i j))
    calc
      p09ComplexNorm2 (fun j => y (Function.update b.1 i j)) =
          p09ComplexNorm2 (fun j =>
            p09RoundedFftApply (axis i).plan model
                (fun k => x (Function.update b.1 i k)) j -
              p09FourierTransform
                (fun k => x (Function.update b.1 i k)) j) := by
        congr 1
        funext j
        simp [y, p09MultiVecSub, p09RoundedCoordinateTransform,
          p09CoordinateTransform, p09FourierTransform]
      _ ≤ Real.sqrt ((axis i).order : ℝ) *
            p09K (axis i).plan γ * model.epsilon *
              p09ComplexNorm2 (fun j => x (Function.update b.1 i j)) +
          C * model.epsilon ^ 2 *
              p09ComplexNorm2 (fun j => x (Function.update b.1 i j)) := hb
      _ = L * p09ComplexNorm2
            (fun j => x (Function.update b.1 i j)) := by
        dsimp [L, p09AxisK]
        ring
  have hrms : p09MultiRms y ≤ L * p09MultiRms x :=
    p09_multiRms_of_norm_bound axis x y L hnorm
  have hsqrtSq : Real.sqrt ((axis i).order : ℝ) ^ 2 =
      ((axis i).order : ℝ) := Real.sq_sqrt (by positivity)
  have hsqrt1 : 1 ≤ Real.sqrt ((axis i).order : ℝ) := by
    have horder : (1 : ℝ) ≤ ((axis i).order : ℝ) := by
      exact_mod_cast (axis i).order_pos
    nlinarith [Real.sqrt_nonneg ((axis i).order : ℝ)]
  have hx := p09_multiNorm2_nonneg x
  have hrmsx : 0 ≤ p09MultiRms x := by
    unfold p09MultiRms
    positivity
  dsimp [y] at hrms ⊢
  dsimp [L] at hrms
  calc
    _ ≤ (Real.sqrt ((axis i).order : ℝ) * p09AxisK (axis i) γ *
          model.epsilon + C * model.epsilon ^ 2) * p09MultiRms x := hrms
    _ ≤ Real.sqrt ((axis i).order : ℝ) *
          (p09AxisK (axis i) γ * model.epsilon +
            C * model.epsilon ^ 2) * p09MultiRms x := by
      apply mul_le_mul_of_nonneg_right _ hrmsx
      have hsecond : C * model.epsilon ^ 2 ≤
          Real.sqrt ((axis i).order : ℝ) * (C * model.epsilon ^ 2) := by
        have := mul_le_mul_of_nonneg_right hsqrt1
          (mul_nonneg hC (sq_nonneg model.epsilon))
        simpa using this
      calc
        Real.sqrt ((axis i).order : ℝ) * p09AxisK (axis i) γ *
              model.epsilon + C * model.epsilon ^ 2 =
            Real.sqrt ((axis i).order : ℝ) *
                (p09AxisK (axis i) γ * model.epsilon) +
              C * model.epsilon ^ 2 := by ring
        _ ≤ Real.sqrt ((axis i).order : ℝ) *
                (p09AxisK (axis i) γ * model.epsilon) +
              Real.sqrt ((axis i).order : ℝ) *
                (C * model.epsilon ^ 2) := add_le_add_right hsecond _
        _ = _ := by ring

private def p09MapFold {V ι : Type*} (op : ι → V → V)
    (indices : List ι) (x : V) : V :=
  indices.foldl (fun state i => op i state) x

private theorem p09_mapFold_sub {V ι : Type*} [AddCommGroup V]
    (op : ι → V → V) (hop : ∀ i x y, op i (x - y) = op i x - op i y)
    (indices : List ι) (x y : V) :
    p09MapFold op indices (x - y) =
      p09MapFold op indices x - p09MapFold op indices y := by
  induction indices generalizing x y with
  | nil => rfl
  | cons i tail ih =>
      change p09MapFold op tail (op i (x - y)) =
        p09MapFold op tail (op i x) - p09MapFold op tail (op i y)
      rw [hop, ih]

private theorem p09_mapFold_norm {V ι : Type*}
    (op : ι → V → V) (N : V → ℝ) (scale : ι → ℝ)
    (hop : ∀ i x, N (op i x) = scale i * N x)
    (indices : List ι) (x : V) :
    N (p09MapFold op indices x) = (indices.map scale).prod * N x := by
  induction indices generalizing x with
  | nil => simp [p09MapFold]
  | cons i tail ih =>
      change N (p09MapFold op tail (op i x)) =
        scale i * (tail.map scale).prod * N x
      rw [ih, hop]
      ring

private theorem p09_mapFold_error_bound {V ι : Type*} [AddCommGroup V]
    (exact rounded : ι → V → V) (N : V → ℝ)
    (indices : List ι) (scale leading remainder : ι → ℝ)
    (hNnonneg : ∀ x, 0 ≤ N x)
    (hNzero : N 0 = 0)
    (hNadd : ∀ x y, N (x + y) ≤ N x + N y)
    (hexactSub : ∀ i x y, exact i (x - y) = exact i x - exact i y)
    (hexactNorm : ∀ i x, N (exact i x) = scale i * N x)
    (hscale : ∀ i, 0 ≤ scale i)
    (hleading : ∀ i, 0 ≤ leading i)
    (hremainder : ∀ i, 0 ≤ remainder i)
    (ε : ℝ) (he : 0 ≤ ε) (he1 : ε ≤ 1)
    (hloc : ∀ i x,
      N (rounded i x - exact i x) ≤
        scale i * leading i * ε * N x + remainder i * ε ^ 2 * N x)
    (x : V) :
    N (p09MapFold rounded indices x - p09MapFold exact indices x) ≤
      (indices.map scale).prod * (indices.map leading).sum * ε * N x +
        p09FoldSecondCoeff scale leading remainder indices * ε ^ 2 * N x := by
  induction indices generalizing x with
  | nil =>
      simp [p09MapFold, p09FoldSecondCoeff, hNzero]
  | cons i tail ih =>
      let P := (tail.map scale).prod
      let S := (tail.map leading).sum
      let Ct := p09FoldSecondCoeff scale leading remainder tail
      let rx := rounded i x
      let tx := exact i x
      let localErr := rx - tx
      have hP : 0 ≤ P := by
        dsimp [P]
        exact List.prod_nonneg (fun z hz => by
          rcases List.mem_map.mp hz with ⟨j, hj, rfl⟩
          exact hscale j)
      have hS : 0 ≤ S := by
        dsimp [S]
        exact List.sum_nonneg (fun z hz => by
          rcases List.mem_map.mp hz with ⟨j, hj, rfl⟩
          exact hleading j)
      have hCt : 0 ≤ Ct :=
        p09FoldSecondCoeff_nonneg scale leading remainder
          hscale hleading hremainder tail
      have hlocal : N localErr ≤
          scale i * leading i * ε * N x +
            remainder i * ε ^ 2 * N x := by
        simpa [localErr, rx, tx] using hloc i x
      have hrx : N rx ≤
          (scale i + scale i * leading i * ε + remainder i * ε ^ 2) * N x := by
        have hdecomp : rx = localErr + tx := by
          dsimp [localErr]
          abel
        rw [hdecomp]
        calc
          _ ≤ N localErr + N tx := hNadd _ _
          _ ≤ (scale i * leading i * ε * N x +
                remainder i * ε ^ 2 * N x) + scale i * N x := by
            rw [hexactNorm]
            gcongr
          _ = _ := by ring
      have htailRound := ih rx
      have htailExactErr :
          N (p09MapFold exact tail rx - p09MapFold exact tail tx) =
            P * N localErr := by
        rw [← p09_mapFold_sub exact hexactSub]
        simpa [P, localErr] using
          p09_mapFold_norm exact N scale hexactNorm tail localErr
      have hdecomp :
          p09MapFold rounded (i :: tail) x - p09MapFold exact (i :: tail) x =
            (p09MapFold rounded tail rx - p09MapFold exact tail rx) +
              (p09MapFold exact tail rx - p09MapFold exact tail tx) := by
        change p09MapFold rounded tail rx - p09MapFold exact tail tx = _
        abel
      rw [hdecomp]
      have he3 : ε ^ 3 ≤ ε ^ 2 := by
        nlinarith [sq_nonneg ε]
      have he4 : ε ^ 4 ≤ ε ^ 2 := by
        nlinarith [sq_nonneg ε, mul_self_le_mul_self he he1]
      have hx := hNnonneg x
      calc
        _ ≤ N (p09MapFold rounded tail rx - p09MapFold exact tail rx) +
            N (p09MapFold exact tail rx - p09MapFold exact tail tx) := hNadd _ _
        _ ≤ (P * S * ε * N rx + Ct * ε ^ 2 * N rx) +
            P * N localErr := by
          rw [htailExactErr]
          exact add_le_add
            (by simpa [P, S, Ct] using htailRound)
            (le_refl (P * N localErr))
        _ ≤ (P * S * ε *
              ((scale i + scale i * leading i * ε +
                remainder i * ε ^ 2) * N x) +
              Ct * ε ^ 2 *
              ((scale i + scale i * leading i * ε +
                remainder i * ε ^ 2) * N x)) +
            P * (scale i * leading i * ε * N x +
              remainder i * ε ^ 2 * N x) := by
          have hPS : 0 ≤ P * S * ε := by positivity
          have hCtE : 0 ≤ Ct * ε ^ 2 := by positivity
          exact add_le_add
            (add_le_add
              (mul_le_mul_of_nonneg_left hrx hPS)
              (mul_le_mul_of_nonneg_left hrx hCtE))
            (mul_le_mul_of_nonneg_left hlocal hP)
        _ ≤ ((i :: tail).map scale).prod *
              ((i :: tail).map leading).sum * ε * N x +
            p09FoldSecondCoeff scale leading remainder (i :: tail) *
              ε ^ 2 * N x := by
          have h3x := mul_le_mul_of_nonneg_right he3 hx
          have h4x := mul_le_mul_of_nonneg_right he4 hx
          have hPSR := mul_le_mul_of_nonneg_left h3x
            (mul_nonneg (mul_nonneg hP hS) (hremainder i))
          have hCtA := mul_le_mul_of_nonneg_left h3x
            (mul_nonneg (mul_nonneg hCt (hscale i)) (hleading i))
          have hCtR := mul_le_mul_of_nonneg_left h4x
            (mul_nonneg hCt (hremainder i))
          simp only [List.map_cons, List.prod_cons, List.sum_cons,
            p09FoldSecondCoeff]
          dsimp [P, S, Ct]
          nlinarith

private theorem p09_fourier_complexNorm2 {n : ℕ} [NeZero n]
    (plan : P09MixedRadixFftPlan n) (x : ZMod n → ℂ) :
    p09ComplexNorm2 (p09FourierTransform x) =
      Real.sqrt (n : ℝ) * p09ComplexNorm2 x := by
  rw [← plan.exact_factorization x, p09_permute_complexNorm2]
  rw [← p09_exactFold_all]
  rw [p09_exactStageFold_norm]
  have hprod :
      ((List.ofFn id).map (fun i : Fin plan.stageCount =>
        Real.sqrt ((plan.stage i).radix : ℝ))).prod = Real.sqrt (n : ℝ) := by
    rw [← List.ofFn_comp', Fin.prod_ofFn]
    exact p09_stage_scale_product plan
  simpa only [id_eq] using
    congrArg (fun z => z * p09ComplexNorm2 x) hprod

private theorem p09_multiNorm2_of_fiber_eq {m : ℕ}
    (axis : Fin m → P09FftAxis) (i : Fin m)
    (x y : P09MultiArray axis) (L : ℝ) (hL : 0 ≤ L)
    (hfiber : ∀ b : P09MultiFiberBase axis i,
      p09ComplexNorm2 (fun j => y (Function.update b.1 i j)) =
        L * p09ComplexNorm2 (fun j => x (Function.update b.1 i j))) :
    p09MultiNorm2 y = L * p09MultiNorm2 x := by
  have hsq : p09MultiNorm2 y ^ 2 = (L * p09MultiNorm2 x) ^ 2 := by
    rw [p09_multiNorm2_sq_fiber axis i y, mul_pow,
      p09_multiNorm2_sq_fiber axis i x, Finset.mul_sum]
    apply Finset.sum_congr rfl
    intro b hb
    rw [← p09_complexNorm2_sq_eq, ← p09_complexNorm2_sq_eq, hfiber b]
    ring
  nlinarith [p09_multiNorm2_nonneg y,
    mul_nonneg hL (p09_multiNorm2_nonneg x)]

private theorem p09_coordinate_norm_scaling {m : ℕ}
    (axis : Fin m → P09FftAxis) (i : Fin m)
    (x : P09MultiArray axis) :
    p09MultiNorm2 (p09CoordinateTransform axis i x) =
      Real.sqrt ((axis i).order : ℝ) * p09MultiNorm2 x := by
  apply p09_multiNorm2_of_fiber_eq axis i x
    (p09CoordinateTransform axis i x) _ (Real.sqrt_nonneg _)
  intro b
  calc
    p09ComplexNorm2 (fun j =>
        p09CoordinateTransform axis i x (Function.update b.1 i j)) =
        p09ComplexNorm2 (p09FourierTransform
          (fun k => x (Function.update b.1 i k))) := by
      congr 1
      funext j
      simp [p09CoordinateTransform, p09FourierTransform]
    _ = Real.sqrt ((axis i).order : ℝ) *
        p09ComplexNorm2 (fun k => x (Function.update b.1 i k)) :=
      p09_fourier_complexNorm2 (axis i).plan _

private theorem p09_coordinate_rms_scaling {m : ℕ}
    (axis : Fin m → P09FftAxis) (i : Fin m)
    (x : P09MultiArray axis) :
    p09MultiRms (p09CoordinateTransform axis i x) =
      Real.sqrt ((axis i).order : ℝ) * p09MultiRms x := by
  unfold p09MultiRms
  rw [p09_coordinate_norm_scaling]
  ring

private theorem p09_coordinate_sub {m : ℕ}
    (axis : Fin m → P09FftAxis) (i : Fin m)
    (x y : P09MultiArray axis) :
    p09CoordinateTransform axis i (x - y) =
      p09CoordinateTransform axis i x - p09CoordinateTransform axis i y := by
  funext index
  simp only [p09CoordinateTransform, Pi.sub_apply, mul_sub,
    Finset.sum_sub_distrib]

private theorem p09_multiRms_zero {m : ℕ}
    (axis : Fin m → P09FftAxis) :
    p09MultiRms (0 : P09MultiArray axis) = 0 := by
  unfold p09MultiRms p09MultiNorm2
  simp

private theorem p09_multiRms_add_le {m : ℕ}
    (axis : Fin m → P09FftAxis) (x y : P09MultiArray axis) :
    p09MultiRms (x + y) ≤ p09MultiRms x + p09MultiRms y := by
  unfold p09MultiRms p09MultiNorm2
  have hden : 0 ≤ Real.sqrt (p09MultiCardinality axis : ℝ) :=
    Real.sqrt_nonneg _
  calc
    ‖WithLp.toLp 2 (x + y)‖ / Real.sqrt (p09MultiCardinality axis : ℝ) =
        ‖WithLp.toLp 2 x + WithLp.toLp 2 y‖ /
          Real.sqrt (p09MultiCardinality axis : ℝ) := by rfl
    _ ≤ (‖WithLp.toLp 2 x‖ + ‖WithLp.toLp 2 y‖) /
          Real.sqrt (p09MultiCardinality axis : ℝ) :=
      div_le_div_of_nonneg_right (norm_add_le _ _) hden
    _ = ‖WithLp.toLp 2 x‖ / Real.sqrt (p09MultiCardinality axis : ℝ) +
          ‖WithLp.toLp 2 y‖ / Real.sqrt (p09MultiCardinality axis : ℝ) := by
      ring

private theorem p09_exactCoordinateFold_eq_prefix {m : ℕ}
    (axis : Fin m → P09FftAxis) (k : ℕ) (hk : k ≤ m)
    (x : P09MultiArray axis) :
    p09MapFold (fun i => p09CoordinateTransform axis i)
        (List.ofFn (fun j : Fin k => Fin.castLE hk j)).reverse x =
      p09ApplyCoordinatePrefix axis k x := by
  induction k generalizing x with
  | zero => simp [p09MapFold, p09ApplyCoordinatePrefix]
  | succ k ih =>
      have hk' : k ≤ m := le_trans (Nat.le_succ k) hk
      have hkm : k < m := lt_of_lt_of_le (Nat.lt_succ_self k) hk
      rw [List.ofFn_succ']
      rw [List.concat_eq_append, List.reverse_concat']
      change p09MapFold (fun i => p09CoordinateTransform axis i)
          (List.ofFn (fun i : Fin k =>
            (fun j : Fin (k + 1) => Fin.castLE hk j) i.castSucc)).reverse
          (p09CoordinateTransform axis
            ((fun j : Fin (k + 1) => Fin.castLE hk j) (Fin.last k)) x) = _
      rw [show (fun j : Fin (k + 1) => Fin.castLE hk j) (Fin.last k) =
          (⟨k, hkm⟩ : Fin m) by ext; rfl]
      rw [show (List.ofFn (fun i : Fin k =>
          (fun j : Fin (k + 1) => Fin.castLE hk j) i.castSucc)).reverse =
          (List.ofFn (fun j : Fin k => Fin.castLE hk' j)).reverse by
        congr 2]
      rw [ih hk']
      simp [p09ApplyCoordinatePrefix, p09CoordinateTransformNat, hkm]

private theorem p09_roundedCoordinateFold_eq_stateZero {m : ℕ} [NeZero m]
    {plan : P09MultidimensionalFftPlan m} {model : P09WilkinsonModel}
    (run : P09MultidimensionalFftRun plan model)
    (k : ℕ) (hk : k ≤ m) :
    p09MapFold (fun i =>
        p09RoundedCoordinateTransform plan.axis i model)
        (List.ofFn (fun j : Fin k => Fin.castLE hk j)).reverse
        (run.computedState ⟨k, Nat.lt_succ_of_le hk⟩) =
      run.computedState 0 := by
  induction k with
  | zero => simp [p09MapFold]
  | succ k ih =>
      have hk' : k ≤ m := le_trans (Nat.le_succ k) hk
      have hkm : k < m := lt_of_lt_of_le (Nat.lt_succ_self k) hk
      rw [List.ofFn_succ']
      rw [List.concat_eq_append, List.reverse_concat']
      change p09MapFold (fun i =>
          p09RoundedCoordinateTransform plan.axis i model)
          (List.ofFn (fun i : Fin k =>
            (fun j : Fin (k + 1) => Fin.castLE hk j) i.castSucc)).reverse
          (p09RoundedCoordinateTransform plan.axis
            ((fun j : Fin (k + 1) => Fin.castLE hk j) (Fin.last k)) model
            (run.computedState ⟨k + 1, Nat.lt_succ_of_le hk⟩)) = _
      rw [show (fun j : Fin (k + 1) => Fin.castLE hk j) (Fin.last k) =
          (⟨k, hkm⟩ : Fin m) by ext; rfl]
      rw [show (run.computedState ⟨k + 1, Nat.lt_succ_of_le hk⟩) =
          run.computedState (⟨k, hkm⟩ : Fin m).succ by congr 2]
      rw [← run.stage_step (⟨k, hkm⟩ : Fin m)]
      rw [show (run.computedState (⟨k, hkm⟩ : Fin m).castSucc) =
          run.computedState ⟨k, Nat.lt_succ_of_le hk'⟩ by congr 2]
      rw [show (List.ofFn (fun i : Fin k =>
          (fun j : Fin (k + 1) => Fin.castLE hk j) i.castSucc)).reverse =
          (List.ofFn (fun j : Fin k => Fin.castLE hk' j)).reverse by
        congr 2]
      exact ih hk'

private noncomputable def p09AxisSecondBase {m : ℕ} [NeZero m]
    (plan : P09MultidimensionalFftPlan m) (γ : ℝ) (hγ : 0 ≤ γ)
    (i : Fin m) : ℝ :=
  Classical.choose (p09_coordinate_rms_error_bound plan.axis i γ hγ)

private theorem p09AxisSecondBase_nonneg {m : ℕ} [NeZero m]
    (plan : P09MultidimensionalFftPlan m) (γ : ℝ) (hγ : 0 ≤ γ)
    (i : Fin m) : 0 ≤ p09AxisSecondBase plan γ hγ i :=
  (Classical.choose_spec
    (p09_coordinate_rms_error_bound plan.axis i γ hγ)).1

private theorem p09AxisSecondBase_bound {m : ℕ} [NeZero m]
    (plan : P09MultidimensionalFftPlan m) (γ : ℝ) (hγ : 0 ≤ γ)
    (i : Fin m) (model : P09WilkinsonModel)
    (hmodelγ : model.gamma = γ) (he1 : model.epsilon ≤ 1)
    (x : P09MultiArray plan.axis) :
    p09MultiRms (p09MultiVecSub
        (p09RoundedCoordinateTransform plan.axis i model x)
        (p09CoordinateTransform plan.axis i x)) ≤
      Real.sqrt ((plan.axis i).order : ℝ) *
        (p09AxisK (plan.axis i) γ * model.epsilon +
          p09AxisSecondBase plan γ hγ i * model.epsilon ^ 2) *
        p09MultiRms x :=
  (Classical.choose_spec
    (p09_coordinate_rms_error_bound plan.axis i γ hγ)).2
      model hmodelγ he1 x

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
  let indices : List (Fin m) := (List.ofFn id).reverse
  let scale : Fin m → ℝ := fun i => Real.sqrt ((plan.axis i).order : ℝ)
  let leading : Fin m → ℝ := fun i => p09AxisK (plan.axis i) γ
  let base : Fin m → ℝ := p09AxisSecondBase plan γ family.gamma_nonneg
  let remainder : Fin m → ℝ := fun i => scale i * base i
  let Cfold := p09FoldSecondCoeff scale leading remainder indices
  let P := (indices.map scale).prod
  have hscale (i : Fin m) : 0 ≤ scale i := Real.sqrt_nonneg _
  have hscalePos (i : Fin m) : 0 < scale i := by
    dsimp [scale]
    apply Real.sqrt_pos.2
    exact_mod_cast (plan.axis i).order_pos
  have hleading (i : Fin m) : 0 ≤ leading i := by
    exact p09K_nonneg (plan.axis i).plan γ family.gamma_nonneg
  have hbase (i : Fin m) : 0 ≤ base i :=
    p09AxisSecondBase_nonneg plan γ family.gamma_nonneg i
  have hremainder (i : Fin m) : 0 ≤ remainder i :=
    mul_nonneg (hscale i) (hbase i)
  have hCfold : 0 ≤ Cfold :=
    p09FoldSecondCoeff_nonneg scale leading remainder
      hscale hleading hremainder indices
  have hP : 0 < P := by
    dsimp [P]
    exact List.prod_pos (fun z hz => by
      rcases List.mem_map.mp hz with ⟨i, hi, rfl⟩
      exact hscalePos i)
  refine ⟨Cfold / P, div_nonneg hCfold (le_of_lt hP), 1, zero_lt_one, ?_⟩
  intro ε heps
  let model := family.model ε
  let run := family.run ε
  have hmodelEpsilon : model.epsilon = ε.1 := family.model_epsilon ε
  have hmodelGamma : model.gamma = γ := family.model_gamma ε
  have he1 : model.epsilon ≤ 1 := by simpa [hmodelEpsilon] using heps
  have he0 : 0 ≤ model.epsilon := le_of_lt model.epsilon_pos
  have hfold := p09_mapFold_error_bound
    (fun i => p09CoordinateTransform plan.axis i)
    (fun i => p09RoundedCoordinateTransform plan.axis i model)
    (p09MultiRms : P09MultiArray plan.axis → ℝ)
    indices scale leading remainder
    (fun x => by
      unfold p09MultiRms
      exact div_nonneg (p09_multiNorm2_nonneg x) (Real.sqrt_nonneg _))
    (p09_multiRms_zero plan.axis)
    (p09_multiRms_add_le plan.axis)
    (p09_coordinate_sub plan.axis)
    (p09_coordinate_rms_scaling plan.axis)
    hscale hleading hremainder model.epsilon he0 he1
    (fun i x => by
      have hb := p09AxisSecondBase_bound plan γ family.gamma_nonneg i
        model hmodelGamma he1 x
      change p09MultiRms (p09MultiVecSub
          (p09RoundedCoordinateTransform plan.axis i model x)
          (p09CoordinateTransform plan.axis i x)) ≤ _
      calc
        _ ≤ Real.sqrt ((plan.axis i).order : ℝ) *
              (p09AxisK (plan.axis i) γ * model.epsilon +
                p09AxisSecondBase plan γ family.gamma_nonneg i *
                  model.epsilon ^ 2) * p09MultiRms x := hb
        _ = scale i * leading i * model.epsilon * p09MultiRms x +
              remainder i * model.epsilon ^ 2 * p09MultiRms x := by
          dsimp [scale, leading, remainder, base]
          ring)
    family.input
  have hsum : (indices.map leading).sum =
      ∑ i : Fin m, p09AxisK (plan.axis i) γ := by
    dsimp [indices]
    rw [List.map_reverse, List.sum_reverse, ← List.ofFn_comp', Fin.sum_ofFn]
    rfl
  have hexactFold :
      p09MapFold (fun i => p09CoordinateTransform plan.axis i)
          indices family.input = p09FamilyMultiExactOutput family := by
    dsimp [indices, p09FamilyMultiExactOutput]
    exact p09_exactCoordinateFold_eq_prefix plan.axis m le_rfl family.input
  have hlast :
      run.computedState ⟨m, Nat.lt_succ_self m⟩ = family.input := by
    rw [show (⟨m, Nat.lt_succ_self m⟩ : Fin (m + 1)) = Fin.last m by
      apply Fin.ext
      rfl]
    rw [run.computed_input]
    exact family.run_input ε
  have hroundedFold :
      p09MapFold (fun i =>
          p09RoundedCoordinateTransform plan.axis i model)
          indices family.input = p09MultiComputedOutput run := by
    rw [← hlast]
    dsimp [indices, p09MultiComputedOutput]
    exact p09_roundedCoordinateFold_eq_stateZero run m le_rfl
  have herror :
      p09FamilyMultiFftRoundoffError family ε =
        p09MapFold (fun i =>
            p09RoundedCoordinateTransform plan.axis i model)
            indices family.input -
          p09MapFold (fun i => p09CoordinateTransform plan.axis i)
            indices family.input := by
    funext index
    simp only [p09FamilyMultiFftRoundoffError, p09MultiVecSub,
      Pi.sub_apply]
    rw [hroundedFold, hexactFold]
  have hexactRms :
      p09MultiRms (p09FamilyMultiExactOutput family) =
        P * p09MultiRms family.input := by
    rw [← hexactFold]
    simpa [P] using p09_mapFold_norm
      (fun i => p09CoordinateTransform plan.axis i)
      (p09MultiRms : P09MultiArray plan.axis → ℝ) scale
      (p09_coordinate_rms_scaling plan.axis) indices family.input
  have hraw :
      p09MultiRms (p09FamilyMultiFftRoundoffError family ε) ≤
        P * (∑ i : Fin m, p09AxisK (plan.axis i) γ) *
            model.epsilon * p09MultiRms family.input +
          Cfold * model.epsilon ^ 2 * p09MultiRms family.input := by
    rw [herror]
    simpa [P, Cfold, hsum] using hfold
  have hbound :
      p09MultiRms (p09FamilyMultiFftRoundoffError family ε) ≤
        (ε.1 * (∑ i : Fin m, p09AxisK (plan.axis i) γ) +
          Cfold / P * ε.1 ^ 2) *
            p09MultiRms (p09FamilyMultiExactOutput family) := by
    calc
      _ ≤ P * (∑ i : Fin m, p09AxisK (plan.axis i) γ) *
            model.epsilon * p09MultiRms family.input +
          Cfold * model.epsilon ^ 2 * p09MultiRms family.input := hraw
      _ = (ε.1 * (∑ i : Fin m, p09AxisK (plan.axis i) γ) +
            Cfold / P * ε.1 ^ 2) *
              p09MultiRms (p09FamilyMultiExactOutput family) := by
        rw [hmodelEpsilon, hexactRms]
        field_simp [ne_of_gt hP]
  apply (div_le_iff₀ hexactOutput).2
  simpa [mul_assoc] using hbound

end HighamBench
