import HighamBench.P09Definitions

namespace HighamBench

open scoped BigOperators

lemma p09_componentwise_contraction (z : ℂ) (a b : ℝ)
    (ha : |a| ≤ 1) (hb : |b| ≤ 1) :
    ‖(⟨a * z.re, b * z.im⟩ : ℂ)‖ ≤ ‖z‖ := by
  rw [← (sq_le_sq₀ (norm_nonneg _) (norm_nonneg _))]
  rw [Complex.sq_norm, Complex.sq_norm, Complex.normSq_apply,
    Complex.normSq_apply]
  have ha2 : a ^ 2 ≤ 1 := by
    calc
      a ^ 2 = |a| ^ 2 := sq_abs a |>.symm
      _ ≤ (1 : ℝ) ^ 2 := (sq_le_sq₀ (abs_nonneg a) zero_le_one).2 (by simpa using ha)
      _ = 1 := by norm_num
  have hb2 : b ^ 2 ≤ 1 := by
    calc
      b ^ 2 = |b| ^ 2 := sq_abs b |>.symm
      _ ≤ (1 : ℝ) ^ 2 := (sq_le_sq₀ (abs_nonneg b) zero_le_one).2 (by simpa using hb)
      _ = 1 := by norm_num
  have hr : 0 ≤ z.re ^ 2 := sq_nonneg _
  have hi : 0 ≤ z.im ^ 2 := sq_nonneg _
  nlinarith [mul_le_mul_of_nonneg_right ha2 hr,
    mul_le_mul_of_nonneg_right hb2 hi]

lemma p09_roundedComplexAdd_error
    (model : P09WilkinsonModel) (x y : ℂ) :
    ‖p09RoundedComplexAdd model x y - (x + y)‖ ≤
      model.epsilon * (‖x‖ + ‖y‖) := by
  rcases model.add_model x.re y.re with ⟨ar, br, har, hbr, hr⟩
  rcases model.add_model x.im y.im with ⟨ai, bi, hai, hbi, hi⟩
  let dx : ℂ := ⟨ar * x.re, ai * x.im⟩
  let dy : ℂ := ⟨br * y.re, bi * y.im⟩
  have heq : p09RoundedComplexAdd model x y - (x + y) =
      (model.epsilon : ℂ) * (dx + dy) := by
    apply Complex.ext <;>
      simp [p09RoundedComplexAdd, dx, dy, hr, hi] <;> ring
  rw [heq, norm_mul, Complex.norm_real, Real.norm_eq_abs,
    abs_of_pos model.epsilon_pos]
  calc
    model.epsilon * ‖dx + dy‖ ≤
        model.epsilon * (‖dx‖ + ‖dy‖) := by
          exact mul_le_mul_of_nonneg_left (norm_add_le dx dy)
            (le_of_lt model.epsilon_pos)
    _ ≤ model.epsilon * (‖x‖ + ‖y‖) := by
          exact mul_le_mul_of_nonneg_left
            (add_le_add (p09_componentwise_contraction x ar ai har hai)
              (p09_componentwise_contraction y br bi hbr hbi))
            (le_of_lt model.epsilon_pos)

lemma p09_flMul_pair_error (model : P09WilkinsonModel) (a : ℝ) (z : ℂ) :
    ‖(⟨model.flMul a z.re, model.flMul a z.im⟩ : ℂ) - (a : ℂ) * z‖ ≤
      model.epsilon * |a| * ‖z‖ := by
  rcases model.mul_model a z.re with ⟨tr, htr, hr⟩
  rcases model.mul_model a z.im with ⟨ti, hti, hi⟩
  let d : ℂ := ⟨tr * z.re, ti * z.im⟩
  have heq : (⟨model.flMul a z.re, model.flMul a z.im⟩ : ℂ) -
      (a : ℂ) * z = (model.epsilon * a : ℝ) * d := by
    apply Complex.ext <;> simp [d, hr, hi] <;> ring
  rw [heq, norm_mul, Complex.norm_real, Real.norm_eq_abs,
    abs_mul, abs_of_pos model.epsilon_pos]
  exact mul_le_mul_of_nonneg_left
    (p09_componentwise_contraction z tr ti htr hti)
    (mul_nonneg (le_of_lt model.epsilon_pos) (abs_nonneg a))

lemma p09_l1_le_two_norm (z : ℂ) : |z.re| + |z.im| ≤ 2 * ‖z‖ := by
  nlinarith [Complex.abs_re_le_norm z, Complex.abs_im_le_norm z]

lemma p09_two_l1_le_three_norm (z : ℂ) :
    2 * (|z.re| + |z.im|) ≤ 3 * ‖z‖ := by
  have hs : (|z.re| + |z.im|) ^ 2 ≤ 2 * ‖z‖ ^ 2 := by
    rw [Complex.sq_norm, Complex.normSq_apply]
    nlinarith [sq_nonneg (|z.re| - |z.im|), sq_abs z.re, sq_abs z.im]
  rw [← (sq_le_sq₀ (by positivity) (by positivity))]
  nlinarith [sq_nonneg ‖z‖]

lemma p09_roundedComplexMul_error
    (model : P09WilkinsonModel) (x y : ℂ) :
    ‖p09RoundedComplexMul model x y - x * y‖ ≤
      (3 * model.epsilon + 2 * model.epsilon ^ 2) * ‖x‖ * ‖y‖ := by
  let u : ℂ :=
    ⟨model.flMul x.re y.re, model.flMul x.re y.im⟩
  let v : ℂ :=
    ⟨-model.flMul x.im y.im, model.flMul x.im y.re⟩
  let u₀ : ℂ := (x.re : ℂ) * y
  let v₀ : ℂ := Complex.I * ((x.im : ℂ) * y)
  have hform : p09RoundedComplexMul model x y =
      p09RoundedComplexAdd model u v := by
    apply Complex.ext <;> simp [p09RoundedComplexMul, p09RoundedComplexAdd, u, v]
  have hexact : x * y = u₀ + v₀ := by
    apply Complex.ext <;> simp [u₀, v₀] <;> ring
  have hu : ‖u - u₀‖ ≤ model.epsilon * |x.re| * ‖y‖ := by
    simpa [u, u₀] using p09_flMul_pair_error model x.re y
  have hv : ‖v - v₀‖ ≤ model.epsilon * |x.im| * ‖y‖ := by
    have h := p09_flMul_pair_error model x.im y
    have heq : v - v₀ = Complex.I *
        ((⟨model.flMul x.im y.re, model.flMul x.im y.im⟩ : ℂ) -
          (x.im : ℂ) * y) := by
      apply Complex.ext <;> simp [v, v₀] <;> ring
    rw [heq, norm_mul, Complex.norm_I, one_mul]
    exact h
  have hu_norm : ‖u‖ ≤ |x.re| * ‖y‖ + model.epsilon * |x.re| * ‖y‖ := by
    calc
      ‖u‖ ≤ ‖u₀‖ + ‖u - u₀‖ := by
        have := norm_add_le u₀ (u - u₀)
        simpa [sub_add_cancel] using this
      _ ≤ ‖u₀‖ + model.epsilon * |x.re| * ‖y‖ :=
        add_le_add_right hu ‖u₀‖
      _ = _ := by simp [u₀, mul_assoc]
  have hv_norm : ‖v‖ ≤ |x.im| * ‖y‖ + model.epsilon * |x.im| * ‖y‖ := by
    calc
      ‖v‖ ≤ ‖v₀‖ + ‖v - v₀‖ := by
        have := norm_add_le v₀ (v - v₀)
        simpa [sub_add_cancel] using this
      _ ≤ ‖v₀‖ + model.epsilon * |x.im| * ‖y‖ :=
        add_le_add_right hv ‖v₀‖
      _ = _ := by simp [v₀, mul_assoc]
  calc
    ‖p09RoundedComplexMul model x y - x * y‖ =
        ‖(p09RoundedComplexAdd model u v - (u + v)) +
          ((u - u₀) + (v - v₀))‖ := by rw [hform, hexact]; congr 1; abel
    _ ≤ ‖p09RoundedComplexAdd model u v - (u + v)‖ +
          (‖u - u₀‖ + ‖v - v₀‖) := by
        exact (norm_add_le _ _).trans
          (add_le_add_right (norm_add_le (u - u₀) (v - v₀))
            ‖p09RoundedComplexAdd model u v - (u + v)‖)
    _ ≤ model.epsilon * (‖u‖ + ‖v‖) +
          (model.epsilon * |x.re| * ‖y‖ +
            model.epsilon * |x.im| * ‖y‖) := by
        exact add_le_add (p09_roundedComplexAdd_error model u v) (add_le_add hu hv)
    _ ≤ model.epsilon *
          ((|x.re| * ‖y‖ + model.epsilon * |x.re| * ‖y‖) +
           (|x.im| * ‖y‖ + model.epsilon * |x.im| * ‖y‖)) +
          (model.epsilon * |x.re| * ‖y‖ +
            model.epsilon * |x.im| * ‖y‖) := by
        exact add_le_add_left
          (mul_le_mul_of_nonneg_left (add_le_add hu_norm hv_norm)
            (le_of_lt model.epsilon_pos)) _
    _ = (2 * model.epsilon + model.epsilon ^ 2) *
          (|x.re| + |x.im|) * ‖y‖ := by ring
    _ ≤ (3 * model.epsilon + 2 * model.epsilon ^ 2) * ‖x‖ * ‖y‖ := by
        have he : 0 ≤ model.epsilon := le_of_lt model.epsilon_pos
        have h1 := p09_two_l1_le_three_norm x
        have h2 := p09_l1_le_two_norm x
        have ha := mul_le_mul_of_nonneg_right h1
          (mul_nonneg he (norm_nonneg y))
        have hb := mul_le_mul_of_nonneg_right h2
          (mul_nonneg (sq_nonneg model.epsilon) (norm_nonneg y))
        nlinarith

lemma p09_stdAddChar_eq_mk {q : ℕ} [NeZero q] (j : ZMod q) :
    ZMod.stdAddChar j =
      ⟨Real.cos (p09RootAngle j), Real.sin (p09RootAngle j)⟩ := by
  rw [p09StdAddChar_positive_exp]
  have hq : (q : ℂ) ≠ 0 := by exact_mod_cast (NeZero.ne q)
  have harg : 2 * Real.pi * Complex.I * (j.val : ℂ) / (q : ℂ) =
      (p09RootAngle j : ℂ) * Complex.I := by
    rw [p09RootAngle]
    push_cast
    field_simp
  rw [harg, Complex.exp_mul_I]
  apply Complex.ext <;>
    simp [Complex.cos_ofReal_re, Complex.sin_ofReal_re]

lemma p09_roundedRoot_error {q : ℕ} [NeZero q]
    (model : P09WilkinsonModel) (j : ZMod q) :
    ‖p09RoundedRoot model j - ZMod.stdAddChar j‖ ≤
      2 * model.gamma * model.epsilon := by
  rcases model.cos_model (p09RootAngle j) with ⟨tc, htc, hc⟩
  rcases model.sin_model (p09RootAngle j) with ⟨ts, hts, hs⟩
  rw [p09_stdAddChar_eq_mk]
  refine (Complex.norm_le_abs_re_add_abs_im _).trans ?_
  simp only [p09RoundedRoot, Complex.sub_re, Complex.sub_im]
  rw [hc, hs]
  have he : 0 ≤ model.epsilon := le_of_lt model.epsilon_pos
  have hg : 0 ≤ model.gamma := model.gamma_nonneg
  rw [show Real.cos (p09RootAngle j) + model.gamma * tc * model.epsilon -
      Real.cos (p09RootAngle j) = model.gamma * tc * model.epsilon by ring,
    show Real.sin (p09RootAngle j) + model.gamma * ts * model.epsilon -
      Real.sin (p09RootAngle j) = model.gamma * ts * model.epsilon by ring,
    abs_mul, abs_mul, abs_mul, abs_mul,
    abs_of_nonneg hg, abs_of_pos model.epsilon_pos]
  nlinarith [mul_le_mul_of_nonneg_left htc (mul_nonneg hg he),
    mul_le_mul_of_nonneg_left hts (mul_nonneg hg he)]

lemma p09_stdAddChar_norm {q : ℕ} [NeZero q] (j : ZMod q) :
    ‖ZMod.stdAddChar j‖ = 1 := by
  rw [p09_stdAddChar_eq_mk]
  rw [Complex.norm_def, Complex.normSq_apply]
  rw [show Real.cos (p09RootAngle j) * Real.cos (p09RootAngle j) +
      Real.sin (p09RootAngle j) * Real.sin (p09RootAngle j) =
      Real.sin (p09RootAngle j) ^ 2 + Real.cos (p09RootAngle j) ^ 2 by ring,
    Real.sin_sq_add_cos_sq, Real.sqrt_one]

lemma p09_roundedRoot_norm {q : ℕ} [NeZero q]
    (model : P09WilkinsonModel) (j : ZMod q) :
    ‖p09RoundedRoot model j‖ ≤ 1 + 2 * model.gamma * model.epsilon := by
  calc
    ‖p09RoundedRoot model j‖ ≤
        ‖ZMod.stdAddChar j‖ +
          ‖p09RoundedRoot model j - ZMod.stdAddChar j‖ := by
      have h := norm_add_le (ZMod.stdAddChar j)
        (p09RoundedRoot model j - ZMod.stdAddChar j)
      simpa [sub_add_cancel] using h
    _ ≤ 1 + 2 * model.gamma * model.epsilon := by
      rw [p09_stdAddChar_norm]
      exact add_le_add_right (p09_roundedRoot_error model j) 1

lemma p09_roundedTwiddleMul_error {q : ℕ} [NeZero q]
    (model : P09WilkinsonModel) (j : ZMod q) (x : ℂ) :
    ‖p09RoundedComplexMul model (p09RoundedRoot model j) x -
        ZMod.stdAddChar j * x‖ ≤
      ((3 + 2 * model.gamma) * model.epsilon +
        (2 + 6 * model.gamma) * model.epsilon ^ 2 +
        4 * model.gamma * model.epsilon ^ 3) * ‖x‖ := by
  let r := p09RoundedRoot model j
  let w := ZMod.stdAddChar j
  calc
    ‖p09RoundedComplexMul model r x - w * x‖ ≤
        ‖p09RoundedComplexMul model r x - r * x‖ + ‖r * x - w * x‖ := by
      simpa only [sub_add_sub_cancel] using
        norm_add_le (p09RoundedComplexMul model r x - r * x) (r * x - w * x)
    _ ≤ (3 * model.epsilon + 2 * model.epsilon ^ 2) * ‖r‖ * ‖x‖ +
        (2 * model.gamma * model.epsilon) * ‖x‖ := by
      exact add_le_add (p09_roundedComplexMul_error model r x)
        (by rw [← sub_mul, norm_mul];
            exact mul_le_mul_of_nonneg_right (p09_roundedRoot_error model j)
              (norm_nonneg x))
    _ ≤ (3 * model.epsilon + 2 * model.epsilon ^ 2) *
          (1 + 2 * model.gamma * model.epsilon) * ‖x‖ +
        (2 * model.gamma * model.epsilon) * ‖x‖ := by
      have hcoef : 0 ≤ 3 * model.epsilon + 2 * model.epsilon ^ 2 := by
        nlinarith [model.epsilon_pos, sq_nonneg model.epsilon]
      exact add_le_add_left
        (mul_le_mul_of_nonneg_right
          (mul_le_mul_of_nonneg_left (p09_roundedRoot_norm model j) hcoef)
          (norm_nonneg x)) _
    _ = _ := by ring

lemma p09_roundedTwiddleMul_error_quadratic {q : ℕ} [NeZero q]
    (model : P09WilkinsonModel) (he : model.epsilon ≤ 1)
    (j : ZMod q) (x : ℂ) :
    ‖p09RoundedComplexMul model (p09RoundedRoot model j) x -
        ZMod.stdAddChar j * x‖ ≤
      ((3 + 2 * model.gamma) * model.epsilon +
        (2 + 10 * model.gamma) * model.epsilon ^ 2) * ‖x‖ := by
  have h := p09_roundedTwiddleMul_error model j x
  refine h.trans (mul_le_mul_of_nonneg_right ?_ (norm_nonneg x))
  have he0 : 0 ≤ model.epsilon := le_of_lt model.epsilon_pos
  have hg : 0 ≤ model.gamma := model.gamma_nonneg
  have he3 : model.epsilon ^ 3 ≤ model.epsilon ^ 2 := by
    nlinarith [sq_nonneg model.epsilon]
  have hm := mul_le_mul_of_nonneg_left he3
    (mul_nonneg (show (0 : ℝ) ≤ 4 by norm_num) hg)
  nlinarith

noncomputable def p09ComplexRecursiveSum (model : P09WilkinsonModel) :
    (n : ℕ) → (Fin n → ℂ) → ℂ
  | 0, _ => 0
  | n + 1, v =>
      if h : n = 0 then v ⟨0, by omega⟩
      else p09RoundedComplexAdd model
        (p09ComplexRecursiveSum model n (fun i => v i.castSucc))
        (v (Fin.last n))

lemma p09ComplexRecursiveSum_re (model : P09WilkinsonModel)
    (n : ℕ) (v : Fin n → ℂ) :
    (p09ComplexRecursiveSum model n v).re =
      recursiveSum model.flAdd n (fun i => (v i).re) := by
  induction n with
  | zero => simp [p09ComplexRecursiveSum, recursiveSum]
  | succ n ih =>
      by_cases hn : n = 0
      · subst n
        simp [p09ComplexRecursiveSum, recursiveSum]
      · simp [p09ComplexRecursiveSum, recursiveSum, hn,
          p09RoundedComplexAdd, ih]

lemma p09ComplexRecursiveSum_im (model : P09WilkinsonModel)
    (n : ℕ) (v : Fin n → ℂ) :
    (p09ComplexRecursiveSum model n v).im =
      recursiveSum model.flAdd n (fun i => (v i).im) := by
  induction n with
  | zero => simp [p09ComplexRecursiveSum, recursiveSum]
  | succ n ih =>
      by_cases hn : n = 0
      · subst n
        simp [p09ComplexRecursiveSum, recursiveSum]
      · simp [p09ComplexRecursiveSum, recursiveSum, hn,
          p09RoundedComplexAdd, ih]

lemma p09RoundedComplexSum_eq_recursive {q : ℕ} [NeZero q]
    (model : P09WilkinsonModel) (term : ZMod q → ℂ) :
    p09RoundedComplexSum model term =
      p09ComplexRecursiveSum model q
        (fun i => term ((ZMod.finEquiv q).toEquiv i)) := by
  apply Complex.ext
  · simp [p09RoundedComplexSum, p09ComplexRecursiveSum_re]
  · simp [p09RoundedComplexSum, p09ComplexRecursiveSum_im]

lemma p09_complexRecursiveSum_error
    (model : P09WilkinsonModel) (he : model.epsilon ≤ 1)
    (n : ℕ) (v : Fin n → ℂ) :
    ‖p09ComplexRecursiveSum model n v - ∑ i, v i‖ ≤
      model.epsilon * (n : ℝ) * (∑ i, ‖v i‖) +
        model.epsilon ^ 2 * ((4 : ℝ) ^ n * ((n : ℝ) + 1) ^ 2) *
          (∑ i, ‖v i‖) := by
  induction n with
  | zero => simp [p09ComplexRecursiveSum]
  | succ n ih =>
      by_cases hn : n = 0
      · subst n
        simp [p09ComplexRecursiveSum]
        have he0 : 0 ≤ model.epsilon := le_of_lt model.epsilon_pos
        positivity
      · let head : ℂ := p09ComplexRecursiveSum model n (fun i => v i.castSucc)
        let exactHead : ℂ := ∑ i : Fin n, v i.castSucc
        let last : ℂ := v (Fin.last n)
        let S : ℝ := ∑ i : Fin (n + 1), ‖v i‖
        have hS : 0 ≤ S := Finset.sum_nonneg fun _ _ => norm_nonneg _
        have hheadS : (∑ i : Fin n, ‖v i.castSucc‖) ≤ S := by
          rw [show S = (∑ i : Fin n, ‖v i.castSucc‖) + ‖last‖ by
            simp [S, last, Fin.sum_univ_castSucc]]
          exact le_add_of_nonneg_right (norm_nonneg _)
        have hheadExact : ‖exactHead‖ ≤ S := by
          calc
            ‖exactHead‖ ≤ ∑ i : Fin n, ‖v i.castSucc‖ :=
              norm_sum_le _ _
            _ ≤ S := hheadS
        have herr := ih (fun i : Fin n => v i.castSucc)
        have herrS : ‖head - exactHead‖ ≤
            model.epsilon * (n : ℝ) * S +
              model.epsilon ^ 2 * ((4 : ℝ) ^ n * ((n : ℝ) + 1) ^ 2) * S := by
          dsimp [head, exactHead]
          exact herr.trans (by
            have hcoef1 : 0 ≤ model.epsilon * (n : ℝ) := by
              have := model.epsilon_pos
              positivity
            have hcoef2 : 0 ≤ model.epsilon ^ 2 *
                ((4 : ℝ) ^ n * ((n : ℝ) + 1) ^ 2) := by positivity
            exact add_le_add
              (mul_le_mul_of_nonneg_left hheadS hcoef1)
              (mul_le_mul_of_nonneg_left hheadS hcoef2))
        have hheadNorm : ‖head‖ ≤ ‖exactHead‖ + ‖head - exactHead‖ := by
          have h := norm_add_le exactHead (head - exactHead)
          simpa [sub_add_cancel] using h
        have hstep : p09ComplexRecursiveSum model (n + 1) v =
            p09RoundedComplexAdd model head last := by
          simp [p09ComplexRecursiveSum, hn, head, last]
        rw [hstep, Fin.sum_univ_castSucc]
        calc
          ‖p09RoundedComplexAdd model head last - (exactHead + last)‖ ≤
              ‖p09RoundedComplexAdd model head last - (head + last)‖ +
                ‖head - exactHead‖ := by
            have h := norm_add_le
              (p09RoundedComplexAdd model head last - (head + last))
              (head - exactHead)
            convert h using 1 <;> abel
          _ ≤ model.epsilon * (‖head‖ + ‖last‖) +
                ‖head - exactHead‖ :=
            add_le_add_left (p09_roundedComplexAdd_error model head last) _
          _ ≤ model.epsilon * (S + ‖head - exactHead‖) +
                ‖head - exactHead‖ := by
            have hsplit : (∑ i : Fin n, ‖v i.castSucc‖) + ‖last‖ = S := by
              simp [S, last, Fin.sum_univ_castSucc]
            have hpair : ‖exactHead‖ + ‖last‖ ≤ S := by
              calc
                ‖exactHead‖ + ‖last‖ ≤
                    (∑ i : Fin n, ‖v i.castSucc‖) + ‖last‖ :=
                  add_le_add_left (norm_sum_le _ _) _
                _ = S := hsplit
            have : ‖head‖ + ‖last‖ ≤ S + ‖head - exactHead‖ := by
              nlinarith
            exact add_le_add_left
              (mul_le_mul_of_nonneg_left this (le_of_lt model.epsilon_pos)) _
          _ ≤ model.epsilon * ((n + 1 : ℕ) : ℝ) * S +
                model.epsilon ^ 2 *
                  ((4 : ℝ) ^ (n + 1) * (((n + 1 : ℕ) : ℝ) + 1) ^ 2) * S := by
            have he0 : 0 ≤ model.epsilon := le_of_lt model.epsilon_pos
            let C : ℝ := (4 : ℝ) ^ n * ((n : ℝ) + 1) ^ 2
            let C' : ℝ := (4 : ℝ) ^ (n + 1) * ((n : ℝ) + 2) ^ 2
            have hC : 0 ≤ C := by positivity
            have hC' : 0 ≤ C' := by positivity
            have hpow1 : (1 : ℝ) ≤ 4 ^ n := one_le_pow₀ (by norm_num)
            have hnC : (n : ℝ) ≤ C := by
              dsimp [C]
              have hn_sq : (n : ℝ) ≤ ((n : ℝ) + 1) ^ 2 := by
                have hn0 : (0 : ℝ) ≤ n := by positivity
                nlinarith [sq_nonneg ((n : ℝ) + 1)]
              calc
                (n : ℝ) ≤ ((n : ℝ) + 1) ^ 2 := hn_sq
                _ ≤ 4 ^ n * ((n : ℝ) + 1) ^ 2 := by
                  nlinarith [sq_nonneg ((n : ℝ) + 1)]
            have hCC' : (n : ℝ) + 2 * C ≤ C' := by
              have hsquares : ((n : ℝ) + 1) ^ 2 ≤ ((n : ℝ) + 2) ^ 2 := by
                nlinarith
              have hmul := mul_le_mul_of_nonneg_left hsquares
                (show (0 : ℝ) ≤ 4 ^ n by positivity)
              calc
                (n : ℝ) + 2 * C ≤ 3 * C := by nlinarith
                _ ≤ 4 * C := by nlinarith
                _ ≤ 4 * (4 ^ n * ((n : ℝ) + 2) ^ 2) :=
                  mul_le_mul_of_nonneg_left hmul (by norm_num)
                _ = C' := by dsimp [C']; rw [pow_succ]; ring
            have he3 : model.epsilon ^ 3 ≤ model.epsilon ^ 2 := by
              nlinarith [sq_nonneg model.epsilon]
            have he3mul : model.epsilon ^ 3 * C * S ≤
                model.epsilon ^ 2 * C * S := by
              exact mul_le_mul_of_nonneg_right
                (mul_le_mul_of_nonneg_right he3 hC) hS
            calc
              model.epsilon * (S + ‖head - exactHead‖) +
                    ‖head - exactHead‖ =
                  model.epsilon * S + (1 + model.epsilon) *
                    ‖head - exactHead‖ := by ring
              _ ≤ model.epsilon * S + (1 + model.epsilon) *
                    (model.epsilon * (n : ℝ) * S + model.epsilon ^ 2 * C * S) := by
                  have herrC : ‖head - exactHead‖ ≤
                      model.epsilon * (n : ℝ) * S +
                        model.epsilon ^ 2 * C * S := by simpa [C] using herrS
                  have hone : 0 ≤ 1 + model.epsilon := by nlinarith
                  exact add_le_add_right
                    (mul_le_mul_of_nonneg_left herrC hone) _
              _ = model.epsilon * ((n : ℕ) + 1 : ℕ) * S +
                    model.epsilon ^ 2 * ((n : ℝ) + C) * S +
                    model.epsilon ^ 3 * C * S := by push_cast; ring
              _ ≤ model.epsilon * ((n : ℕ) + 1 : ℕ) * S +
                    model.epsilon ^ 2 * ((n : ℝ) + 2 * C) * S := by
                  push_cast
                  nlinarith
              _ ≤ model.epsilon * ((n + 1 : ℕ) : ℝ) * S +
                    model.epsilon ^ 2 * C' * S := by
                  have hh := mul_le_mul_of_nonneg_right
                    (mul_le_mul_of_nonneg_left hCC' (sq_nonneg model.epsilon)) hS
                  exact add_le_add_right (by simpa [mul_assoc] using hh) _
              _ = _ := by dsimp [C']; push_cast; ring

lemma p09_roundedGenericRadixBlock_error {q : ℕ} [NeZero q]
    (model : P09WilkinsonModel) (he : model.epsilon ≤ 1)
    (x : ZMod q → ℂ) (k : ZMod q) :
    let A : ℝ := 3 + 2 * model.gamma
    let B₁ : ℝ := 2 + 10 * model.gamma
    let C : ℝ := (4 : ℝ) ^ q * ((q : ℝ) + 1) ^ 2
    let B : ℝ := B₁ + (q : ℝ) * (A + B₁) + C * (1 + A + B₁)
    ‖p09RoundedGenericRadixBlock model x k -
        ∑ j : ZMod q, ZMod.stdAddChar (j * k) * x j‖ ≤
      (model.epsilon * ((q : ℝ) + 3 + 2 * model.gamma) +
        B * model.epsilon ^ 2) * (∑ j : ZMod q, ‖x j‖) := by
  dsimp only
  let index : Fin q ≃ ZMod q := (ZMod.finEquiv q).toEquiv
  let rounded : Fin q → ℂ := fun i =>
    p09RoundedComplexMul model
      (p09RoundedRoot model (index i * k)) (x (index i))
  let exact : Fin q → ℂ := fun i =>
    ZMod.stdAddChar (index i * k) * x (index i)
  let S : ℝ := ∑ j : ZMod q, ‖x j‖
  let A : ℝ := 3 + 2 * model.gamma
  let B₁ : ℝ := 2 + 10 * model.gamma
  let C : ℝ := (4 : ℝ) ^ q * ((q : ℝ) + 1) ^ 2
  have he0 : 0 ≤ model.epsilon := le_of_lt model.epsilon_pos
  have hg : 0 ≤ model.gamma := model.gamma_nonneg
  have hA : 0 ≤ A := by dsimp [A]; nlinarith
  have hB₁ : 0 ≤ B₁ := by dsimp [B₁]; nlinarith
  have hC : 0 ≤ C := by positivity
  have hS : 0 ≤ S := Finset.sum_nonneg fun _ _ => norm_nonneg _
  have hterm (i : Fin q) : ‖rounded i - exact i‖ ≤
      (A * model.epsilon + B₁ * model.epsilon ^ 2) * ‖x (index i)‖ := by
    simpa [rounded, exact, A, B₁, mul_comm] using
      p09_roundedTwiddleMul_error_quadratic model he (index i * k) (x (index i))
  have hsumNorm : (∑ i : Fin q, ‖rounded i - exact i‖) ≤
      (A * model.epsilon + B₁ * model.epsilon ^ 2) * S := by
    calc
      (∑ i : Fin q, ‖rounded i - exact i‖) ≤
          ∑ i : Fin q, (A * model.epsilon + B₁ * model.epsilon ^ 2) *
            ‖x (index i)‖ := Finset.sum_le_sum fun i _ => hterm i
      _ = (A * model.epsilon + B₁ * model.epsilon ^ 2) * S := by
        rw [← Finset.mul_sum]
        exact congrArg (fun t : ℝ => (A * model.epsilon + B₁ * model.epsilon ^ 2) * t)
          (Equiv.sum_comp index (fun j : ZMod q => ‖x j‖))
  have hroundedNorm : (∑ i : Fin q, ‖rounded i‖) ≤
      (1 + A * model.epsilon + B₁ * model.epsilon ^ 2) * S := by
    calc
      (∑ i : Fin q, ‖rounded i‖) ≤
          ∑ i : Fin q, (‖exact i‖ + ‖rounded i - exact i‖) := by
        apply Finset.sum_le_sum
        intro i _
        have h := norm_add_le (exact i) (rounded i - exact i)
        simpa [sub_add_cancel] using h
      _ = (∑ i : Fin q, ‖exact i‖) +
          (∑ i : Fin q, ‖rounded i - exact i‖) := Finset.sum_add_distrib
      _ ≤ S + (A * model.epsilon + B₁ * model.epsilon ^ 2) * S := by
        have hexactNorm : (∑ i : Fin q, ‖exact i‖) = S := by
          dsimp [exact, S]
          simp only [norm_mul, p09_stdAddChar_norm, one_mul]
          exact Equiv.sum_comp index (fun j : ZMod q => ‖x j‖)
        rw [hexactNorm]
        exact add_le_add_right hsumNorm S
      _ = (1 + A * model.epsilon + B₁ * model.epsilon ^ 2) * S := by ring
  have hsumRound := p09_complexRecursiveSum_error model he q rounded
  have hsumRound' :
      ‖p09ComplexRecursiveSum model q rounded - ∑ i, rounded i‖ ≤
        (model.epsilon * (q : ℝ) + model.epsilon ^ 2 * C) *
          (1 + A * model.epsilon + B₁ * model.epsilon ^ 2) * S := by
    calc
      ‖p09ComplexRecursiveSum model q rounded - ∑ i, rounded i‖ ≤
          (model.epsilon * (q : ℝ) + model.epsilon ^ 2 * C) *
            (∑ i, ‖rounded i‖) := by
        simpa [C, add_mul] using hsumRound
      _ ≤ (model.epsilon * (q : ℝ) + model.epsilon ^ 2 * C) *
          ((1 + A * model.epsilon + B₁ * model.epsilon ^ 2) * S) := by
        exact mul_le_mul_of_nonneg_left hroundedNorm (by positivity)
      _ = _ := by ring
  have he2 : model.epsilon ^ 2 ≤ model.epsilon := by
    nlinarith [sq_nonneg model.epsilon]
  have he3 : model.epsilon ^ 3 ≤ model.epsilon ^ 2 := by
    nlinarith [sq_nonneg model.epsilon]
  have he4 : model.epsilon ^ 4 ≤ model.epsilon ^ 2 := by
    have := mul_le_mul_of_nonneg_left he2 (sq_nonneg model.epsilon)
    nlinarith
  rw [p09RoundedGenericRadixBlock, p09RoundedComplexSum_eq_recursive]
  have hexactSum : (∑ j : ZMod q, ZMod.stdAddChar (j * k) * x j) =
      ∑ i : Fin q, exact i := by
    dsimp [exact]
    exact (Equiv.sum_comp index
      (fun j : ZMod q => ZMod.stdAddChar (j * k) * x j)).symm
  rw [hexactSum]
  change ‖p09ComplexRecursiveSum model q rounded - ∑ i : Fin q, exact i‖ ≤ _
  calc
    ‖p09ComplexRecursiveSum model q rounded - ∑ i : Fin q, exact i‖ ≤
        ‖p09ComplexRecursiveSum model q rounded - ∑ i, rounded i‖ +
          ‖∑ i : Fin q, (rounded i - exact i)‖ := by
      have h := norm_add_le
        (p09ComplexRecursiveSum model q rounded - ∑ i, rounded i)
        (∑ i : Fin q, (rounded i - exact i))
      convert h using 1 <;> simp [Finset.sum_sub_distrib]
    _ ≤ ‖p09ComplexRecursiveSum model q rounded - ∑ i, rounded i‖ +
          (∑ i : Fin q, ‖rounded i - exact i‖) :=
      add_le_add_right (norm_sum_le _ _) _
    _ ≤ (model.epsilon * (q : ℝ) + model.epsilon ^ 2 * C) *
          (1 + A * model.epsilon + B₁ * model.epsilon ^ 2) * S +
        (A * model.epsilon + B₁ * model.epsilon ^ 2) * S :=
      add_le_add hsumRound' hsumNorm
    _ ≤ (model.epsilon * ((q : ℝ) + 3 + 2 * model.gamma) +
          (B₁ + (q : ℝ) * (A + B₁) + C * (1 + A + B₁)) *
            model.epsilon ^ 2) * S := by
      have hq : (0 : ℝ) ≤ q := by positivity
      have h2A := mul_le_mul_of_nonneg_left he3
        (mul_nonneg hq hA)
      have h2B := mul_le_mul_of_nonneg_left he4
        (mul_nonneg hq hB₁)
      have hCA := mul_le_mul_of_nonneg_left he3
        (mul_nonneg hC hA)
      have hCB := mul_le_mul_of_nonneg_left he4
        (mul_nonneg hC hB₁)
      have hcoef :
          (model.epsilon * (q : ℝ) + model.epsilon ^ 2 * C) *
                (1 + A * model.epsilon + B₁ * model.epsilon ^ 2) +
              (A * model.epsilon + B₁ * model.epsilon ^ 2) ≤
            model.epsilon * ((q : ℝ) + 3 + 2 * model.gamma) +
              (B₁ + (q : ℝ) * (A + B₁) + C * (1 + A + B₁)) *
                model.epsilon ^ 2 := by
        dsimp [A, B₁] at *
        nlinarith
      simpa [add_mul] using mul_le_mul_of_nonneg_right hcoef hS
    _ = _ := by simp [A, B₁, C, S]

lemma p09_rootAngle_natCast {q : ℕ} [NeZero q] (a : ℕ) (ha : a < q) :
    p09RootAngle (a : ZMod q) = 2 * Real.pi * (a : ℝ) / q := by
  rw [p09RootAngle, ZMod.val_natCast, Nat.mod_eq_of_lt ha]

lemma p09_radixTwoCoefficient_eq (j : ZMod 2) (x : ℂ) :
    p09RadixTwoCoefficientApply j x = ZMod.stdAddChar j * x := by
  have hj := j.val_lt
  rw [← ZMod.natCast_zmod_val j]
  interval_cases hval : j.val
  · rw [p09_stdAddChar_eq_mk, p09_rootAngle_natCast 0 (by norm_num)]
    apply Complex.ext <;>
      simp [p09RadixTwoCoefficientApply]
  ·
    rw [p09_stdAddChar_eq_mk, p09_rootAngle_natCast 1 (by norm_num)]
    norm_num
    apply Complex.ext <;>
      simp [p09RadixTwoCoefficientApply, show (1 : ZMod 2) ≠ 0 by decide]

lemma p09_radixFourCoefficient_eq (j : ZMod 4) (x : ℂ) :
    p09RadixFourCoefficientApply j x = ZMod.stdAddChar j * x := by
  have hj := j.val_lt
  rw [← ZMod.natCast_zmod_val j]
  interval_cases hval : j.val
  · rw [p09_stdAddChar_eq_mk, p09_rootAngle_natCast 0 (by norm_num)]
    apply Complex.ext <;>
      simp [p09RadixFourCoefficientApply]
  ·
    have hhalf : 2 * Real.pi / 4 = Real.pi / 2 := by ring
    rw [p09_stdAddChar_eq_mk, p09_rootAngle_natCast 1 (by norm_num)]
    norm_num
    rw [hhalf]
    apply Complex.ext <;>
      simp [p09RadixFourCoefficientApply, show (1 : ZMod 4) ≠ 0 by decide]
  ·
    have hpi : 2 * Real.pi * (2 : ℝ) / 4 = Real.pi := by ring
    rw [p09_stdAddChar_eq_mk, p09_rootAngle_natCast 2 (by norm_num)]
    norm_num
    rw [hpi]
    apply Complex.ext <;>
      simp [p09RadixFourCoefficientApply, show (2 : ZMod 4) ≠ 0 by decide,
        show (2 : ZMod 4) ≠ 1 by decide]
  ·
    have hthree : 2 * Real.pi * (3 : ℝ) / 4 = Real.pi + Real.pi / 2 := by ring
    rw [p09_stdAddChar_eq_mk, p09_rootAngle_natCast 3 (by norm_num)]
    norm_num
    rw [hthree]
    apply Complex.ext <;>
      simp [p09RadixFourCoefficientApply, show (3 : ZMod 4) ≠ 0 by decide,
        show (3 : ZMod 4) ≠ 1 by decide, show (3 : ZMod 4) ≠ 2 by decide,
        Real.sin_add, Real.cos_add]

lemma p09_roundedRadixTwoBlock_error
    (model : P09WilkinsonModel) (x : ZMod 2 → ℂ) (k : ZMod 2) :
    ‖p09RoundedRadixTwoBlock model x k -
        ∑ j : ZMod 2, ZMod.stdAddChar (j * k) * x j‖ ≤
      model.epsilon * (∑ j : ZMod 2, ‖x j‖) := by
  let term : ZMod 2 → ℂ := fun j => p09RadixTwoCoefficientApply (j * k) (x j)
  have hterm (j : ZMod 2) : term j = ZMod.stdAddChar (j * k) * x j :=
    p09_radixTwoCoefficient_eq (j * k) (x j)
  rw [p09RoundedRadixTwoBlock, p09RoundedComplexSum_eq_recursive]
  change ‖p09RoundedComplexAdd model (term 0) (term 1) -
      ∑ j : ZMod 2, ZMod.stdAddChar (j * k) * x j‖ ≤ _
  rw [show (∑ j : ZMod 2, ZMod.stdAddChar (j * k) * x j) = term 0 + term 1 by
    rw [show (∑ j : ZMod 2, ZMod.stdAddChar (j * k) * x j) =
      ∑ j : ZMod 2, term j by apply Finset.sum_congr rfl; intro j _; exact (hterm j).symm]
    exact Fin.sum_univ_two term]
  refine (p09_roundedComplexAdd_error model (term 0) (term 1)).trans ?_
  rw [show (∑ j : ZMod 2, ‖x j‖) = ‖x 0‖ + ‖x 1‖ by
    exact Fin.sum_univ_two (fun j : ZMod 2 => ‖x j‖)]
  simp only [term, p09_radixTwoCoefficient_eq, norm_mul,
    p09_stdAddChar_norm, one_mul]
  rfl

lemma p09_roundedRadixFourBlock_error
    (model : P09WilkinsonModel) (x : ZMod 4 → ℂ) (k : ZMod 4) :
    ‖p09RoundedRadixFourBlock model x k -
        ∑ j : ZMod 4, ZMod.stdAddChar (j * k) * x j‖ ≤
      (2 * model.epsilon + model.epsilon ^ 2) *
        (∑ j : ZMod 4, ‖x j‖) := by
  let term : ZMod 4 → ℂ := fun j => p09RadixFourCoefficientApply (j * k) (x j)
  let a := term 0
  let b := term 1
  let c := term 2
  let d := term 3
  let ab := p09RoundedComplexAdd model a b
  let cd := p09RoundedComplexAdd model c d
  have hterm (j : ZMod 4) : term j = ZMod.stdAddChar (j * k) * x j :=
    p09_radixFourCoefficient_eq (j * k) (x j)
  have hab : ‖ab - (a + b)‖ ≤ model.epsilon * (‖a‖ + ‖b‖) :=
    p09_roundedComplexAdd_error model a b
  have hcd : ‖cd - (c + d)‖ ≤ model.epsilon * (‖c‖ + ‖d‖) :=
    p09_roundedComplexAdd_error model c d
  have habn : ‖ab‖ ≤ (1 + model.epsilon) * (‖a‖ + ‖b‖) := by
    calc
      ‖ab‖ ≤ ‖a + b‖ + ‖ab - (a + b)‖ := by
        have h := norm_add_le (a + b) (ab - (a + b))
        simpa [sub_add_cancel] using h
      _ ≤ (‖a‖ + ‖b‖) + model.epsilon * (‖a‖ + ‖b‖) :=
        add_le_add (norm_add_le a b) hab
      _ = _ := by ring
  have hcdn : ‖cd‖ ≤ (1 + model.epsilon) * (‖c‖ + ‖d‖) := by
    calc
      ‖cd‖ ≤ ‖c + d‖ + ‖cd - (c + d)‖ := by
        have h := norm_add_le (c + d) (cd - (c + d))
        simpa [sub_add_cancel] using h
      _ ≤ (‖c‖ + ‖d‖) + model.epsilon * (‖c‖ + ‖d‖) :=
        add_le_add (norm_add_le c d) hcd
      _ = _ := by ring
  have hfinal := p09_roundedComplexAdd_error model ab cd
  rw [p09RoundedRadixFourBlock]
  change ‖p09RoundedComplexAdd model ab cd -
      ∑ j : ZMod 4, ZMod.stdAddChar (j * k) * x j‖ ≤ _
  rw [show (∑ j : ZMod 4, ZMod.stdAddChar (j * k) * x j) =
      (a + b) + (c + d) by
    rw [show (∑ j : ZMod 4, ZMod.stdAddChar (j * k) * x j) =
      ∑ j : ZMod 4, term j by apply Finset.sum_congr rfl; intro j _; exact (hterm j).symm]
    rw [← Equiv.sum_comp ((ZMod.finEquiv 4).toEquiv) term,
      Fin.sum_univ_four]
    simp only [a, b, c, d]
    abel]
  calc
    ‖p09RoundedComplexAdd model ab cd - ((a + b) + (c + d))‖ =
        ‖(p09RoundedComplexAdd model ab cd - (ab + cd)) +
          ((ab - (a + b)) + (cd - (c + d)))‖ := by congr 1; abel
    _ ≤ ‖p09RoundedComplexAdd model ab cd - (ab + cd)‖ +
          ‖(ab - (a + b)) + (cd - (c + d))‖ := norm_add_le _ _
    _ ≤
        ‖p09RoundedComplexAdd model ab cd - (ab + cd)‖ +
          (‖ab - (a + b)‖ + ‖cd - (c + d)‖) := by
      exact add_le_add_right (norm_add_le _ _) _
    _ ≤ model.epsilon * (‖ab‖ + ‖cd‖) +
          (model.epsilon * (‖a‖ + ‖b‖) +
            model.epsilon * (‖c‖ + ‖d‖)) :=
      add_le_add hfinal (add_le_add hab hcd)
    _ ≤ model.epsilon * ((1 + model.epsilon) * (‖a‖ + ‖b‖) +
          (1 + model.epsilon) * (‖c‖ + ‖d‖)) +
          (model.epsilon * (‖a‖ + ‖b‖) +
            model.epsilon * (‖c‖ + ‖d‖)) := by
      exact add_le_add_left
        (mul_le_mul_of_nonneg_left (add_le_add habn hcdn)
          (le_of_lt model.epsilon_pos)) _
    _ = (2 * model.epsilon + model.epsilon ^ 2) *
          (‖a‖ + ‖b‖ + ‖c‖ + ‖d‖) := by ring
    _ = (2 * model.epsilon + model.epsilon ^ 2) *
          (∑ j : ZMod 4, ‖x j‖) := by
      rw [show (∑ j : ZMod 4, ‖x j‖) = ‖x 0‖ + ‖x 1‖ + ‖x 2‖ + ‖x 3‖ by
        exact Fin.sum_univ_four (fun j : ZMod 4 => ‖x j‖)]
      simp only [a, b, c, d, term, p09_radixFourCoefficient_eq,
        norm_mul, p09_stdAddChar_norm, one_mul]

lemma p09_roundedRadixTwoBlock_error_cast {q : ℕ} [NeZero q]
    (hq : q = 2) (model : P09WilkinsonModel) (x : ZMod q → ℂ) (k : ZMod q) :
    ‖p09RoundedRadixTwoBlock model
        (fun j : ZMod 2 => x (hq.symm ▸ j)) (hq ▸ k) -
        ∑ j : ZMod q, ZMod.stdAddChar (j * k) * x j‖ ≤
      model.epsilon * (∑ j : ZMod q, ‖x j‖) := by
  subst q
  simpa using p09_roundedRadixTwoBlock_error model x k

lemma p09_roundedRadixFourBlock_error_cast {q : ℕ} [NeZero q]
    (hq : q = 4) (model : P09WilkinsonModel) (x : ZMod q → ℂ) (k : ZMod q) :
    ‖p09RoundedRadixFourBlock model
        (fun j : ZMod 4 => x (hq.symm ▸ j)) (hq ▸ k) -
        ∑ j : ZMod q, ZMod.stdAddChar (j * k) * x j‖ ≤
      (2 * model.epsilon + model.epsilon ^ 2) *
        (∑ j : ZMod q, ‖x j‖) := by
  subst q
  simpa using p09_roundedRadixFourBlock_error model x k

noncomputable def p09L2 {I : Type*} [Fintype I] (x : I → ℂ) : ℝ :=
  Real.sqrt (∑ i, ‖x i‖ ^ 2)

lemma p09L2_block_bound {B J : Type*} [Fintype B] [Fintype J]
    (a : ℝ) (ha : 0 ≤ a) (e x : B × J → ℂ)
    (h : ∀ b k, ‖e (b, k)‖ ≤ a * (∑ j : J, ‖x (b, j)‖)) :
    p09L2 e ≤ (Fintype.card J : ℝ) * a * p09L2 x := by
  let c : ℝ := Fintype.card J
  let X : ℝ := ∑ z : B × J, ‖x z‖ ^ 2
  let E : ℝ := ∑ z : B × J, ‖e z‖ ^ 2
  have hc : 0 ≤ c := by positivity
  have hX : 0 ≤ X := Finset.sum_nonneg fun _ _ => sq_nonneg _
  have hpoint (b : B) (k : J) : ‖e (b, k)‖ ^ 2 ≤
      (a * (∑ j : J, ‖x (b, j)‖)) ^ 2 :=
    (sq_le_sq₀ (norm_nonneg _) (mul_nonneg ha (Finset.sum_nonneg fun _ _ => norm_nonneg _))).2
      (h b k)
  have hcauchy (b : B) : (∑ j : J, ‖x (b, j)‖) ^ 2 ≤
      c * (∑ j : J, ‖x (b, j)‖ ^ 2) := by
    dsimp [c]
    simpa using (sq_sum_le_card_mul_sum_sq
      (s := (Finset.univ : Finset J)) (f := fun j => ‖x (b, j)‖))
  have hE : E ≤ c ^ 2 * a ^ 2 * X := by
    rw [show E = ∑ b : B, ∑ k : J, ‖e (b, k)‖ ^ 2 by
      simp [E, Fintype.sum_prod_type]]
    rw [show X = ∑ b : B, ∑ j : J, ‖x (b, j)‖ ^ 2 by
      simp [X, Fintype.sum_prod_type]]
    calc
      (∑ b : B, ∑ k : J, ‖e (b, k)‖ ^ 2) ≤
          ∑ b : B, ∑ k : J,
            (a * (∑ j : J, ‖x (b, j)‖)) ^ 2 := by
        exact Finset.sum_le_sum fun b _ => Finset.sum_le_sum fun k _ => hpoint b k
      _ = ∑ b : B, c * (a * (∑ j : J, ‖x (b, j)‖)) ^ 2 := by
        apply Finset.sum_congr rfl
        intro b _
        simp [c]
      _ ≤ ∑ b : B, c ^ 2 * a ^ 2 *
            (∑ j : J, ‖x (b, j)‖ ^ 2) := by
        apply Finset.sum_le_sum
        intro b _
        have hh := mul_le_mul_of_nonneg_left (hcauchy b)
          (mul_nonneg hc (sq_nonneg a))
        nlinarith
      _ = c ^ 2 * a ^ 2 * ∑ b : B, ∑ j : J, ‖x (b, j)‖ ^ 2 := by
        rw [Finset.mul_sum]
  rw [p09L2, p09L2]
  dsimp [E, X] at hE ⊢
  rw [Real.sqrt_le_iff]
  constructor
  · positivity
  · rw [mul_pow, mul_pow, Real.sq_sqrt hX]
    nlinarith

lemma p09L2_equiv {I J : Type*} [Fintype I] [Fintype J]
    (e : I ≃ J) (x : J → ℂ) : p09L2 (fun i => x (e i)) = p09L2 x := by
  simp only [p09L2]
  exact congrArg Real.sqrt (Equiv.sum_comp e (fun j => ‖x j‖ ^ 2))

lemma p09ComplexNorm2_eq_l2 {n : ℕ} [NeZero n] (x : ZMod n → ℂ) :
    p09ComplexNorm2 x = p09L2 x := rfl

noncomputable def p09BlockSecondCoeff {n : ℕ} [NeZero n]
    (stage : P09MixedRadixStage n) (g : ℝ) : ℝ :=
  if stage.radix = 2 then 0
  else if stage.radix = 4 then 2
  else
    let A := 3 + 2 * g
    let B₁ := 2 + 10 * g
    let C := (4 : ℝ) ^ stage.radix * ((stage.radix : ℝ) + 1) ^ 2
    let D := B₁ + (stage.radix : ℝ) * (A + B₁) + C * (1 + A + B₁)
    Real.sqrt (stage.radix : ℝ) * D

lemma p09_roundedMixedRadixBlockApply_error {n : ℕ} [NeZero n]
    (model : P09WilkinsonModel) (he : model.epsilon ≤ 1)
    (stage : P09MixedRadixStage n) (x : ZMod n → ℂ) :
    0 ≤ p09BlockSecondCoeff stage model.gamma ∧
      p09ComplexNorm2 (fun i =>
        p09RoundedMixedRadixBlockApply model stage x i -
          p09MixedRadixBlockApply stage x i) ≤
        Real.sqrt (stage.radix : ℝ) *
          (model.epsilon * p09Alpha stage.radix model.gamma +
            p09BlockSecondCoeff stage model.gamma * model.epsilon ^ 2) *
              p09ComplexNorm2 x := by
  letI : NeZero stage.radix := ⟨stage.radix_ne_zero⟩
  let permuted : ZMod n → ℂ := fun i => x (stage.permutation i)
  let err : Fin stage.blockCount × ZMod stage.radix → ℂ := fun bk =>
    p09RoundedMixedRadixBlockApply model stage x (stage.reindex bk) -
      p09MixedRadixBlockApply stage x (stage.reindex bk)
  let inp : Fin stage.blockCount × ZMod stage.radix → ℂ := fun bj =>
    permuted (stage.reindex bj)
  have herrNorm : p09L2 err = p09ComplexNorm2 (fun i =>
      p09RoundedMixedRadixBlockApply model stage x i -
        p09MixedRadixBlockApply stage x i) := by
    rw [p09ComplexNorm2_eq_l2, ← p09L2_equiv stage.reindex]
  have hinpNorm : p09L2 inp = p09ComplexNorm2 x := by
    rw [p09ComplexNorm2_eq_l2]
    calc
      p09L2 inp = p09L2 permuted := p09L2_equiv stage.reindex permuted
      _ = p09L2 x := p09L2_equiv stage.permutation x
  by_cases h2 : stage.radix = 2
  · constructor
    · simp [p09BlockSecondCoeff, h2]
    have hp (b : Fin stage.blockCount) (k : ZMod stage.radix) :
        ‖err (b, k)‖ ≤ model.epsilon * (∑ j : ZMod stage.radix, ‖inp (b, j)‖) := by
      let xb : ZMod 2 → ℂ := fun j =>
        permuted (stage.reindex (b, h2.symm ▸ j))
      have hb := p09_roundedRadixTwoBlock_error_cast h2 model
        (fun j : ZMod stage.radix => permuted (stage.reindex (b, j))) k
      simpa [err, inp, xb, permuted, p09RoundedMixedRadixBlockApply,
        p09MixedRadixBlockApply, h2] using hb
    have hb := p09L2_block_bound model.epsilon (le_of_lt model.epsilon_pos) err inp hp
    rw [herrNorm, hinpNorm] at hb
    rw [ZMod.card] at hb
    have hs : Real.sqrt 2 ^ 2 = 2 := Real.sq_sqrt (by norm_num)
    have hBc : p09BlockSecondCoeff stage model.gamma = 0 := by
      simp [p09BlockSecondCoeff, h2]
    calc
      p09ComplexNorm2 (fun i => p09RoundedMixedRadixBlockApply model stage x i -
          p09MixedRadixBlockApply stage x i) ≤
          (stage.radix : ℝ) * model.epsilon * p09ComplexNorm2 x := hb
      _ = Real.sqrt (stage.radix : ℝ) *
          (model.epsilon * p09Alpha stage.radix model.gamma +
            p09BlockSecondCoeff stage model.gamma * model.epsilon ^ 2) *
              p09ComplexNorm2 x := by
        rw [h2]
        rw [hBc]
        simp only [p09Alpha, if_true, zero_mul, add_zero]
        calc
          (2 : ℝ) * model.epsilon * p09ComplexNorm2 x =
              (Real.sqrt 2 ^ 2) * model.epsilon * p09ComplexNorm2 x := by rw [hs]
          _ = Real.sqrt 2 * (model.epsilon * Real.sqrt 2) *
              p09ComplexNorm2 x := by ring
  · by_cases h4 : stage.radix = 4
    · constructor
      · simp [p09BlockSecondCoeff, h2, h4]
      have hp (b : Fin stage.blockCount) (k : ZMod stage.radix) :
          ‖err (b, k)‖ ≤ (2 * model.epsilon + model.epsilon ^ 2) *
            (∑ j : ZMod stage.radix, ‖inp (b, j)‖) := by
        let xb : ZMod 4 → ℂ := fun j =>
          permuted (stage.reindex (b, h4.symm ▸ j))
        have hb := p09_roundedRadixFourBlock_error_cast h4 model
          (fun j : ZMod stage.radix => permuted (stage.reindex (b, j))) k
        simpa [err, inp, xb, permuted, p09RoundedMixedRadixBlockApply,
          p09MixedRadixBlockApply, h2, h4] using hb
      have hfac : 0 ≤ 2 * model.epsilon + model.epsilon ^ 2 := by
        nlinarith [model.epsilon_pos, sq_nonneg model.epsilon]
      have hb := p09L2_block_bound (2 * model.epsilon + model.epsilon ^ 2)
        hfac err inp hp
      rw [herrNorm, hinpNorm] at hb
      rw [ZMod.card] at hb
      have hn : 0 ≤ p09ComplexNorm2 x := Real.sqrt_nonneg _
      have hBc : p09BlockSecondCoeff stage model.gamma = 2 := by
        simp [p09BlockSecondCoeff, h2, h4]
      calc
        p09ComplexNorm2 (fun i => p09RoundedMixedRadixBlockApply model stage x i -
            p09MixedRadixBlockApply stage x i) ≤
            (stage.radix : ℝ) * (2 * model.epsilon + model.epsilon ^ 2) *
              p09ComplexNorm2 x := hb
        _ ≤ Real.sqrt (stage.radix : ℝ) *
            (model.epsilon * p09Alpha stage.radix model.gamma +
              p09BlockSecondCoeff stage model.gamma * model.epsilon ^ 2) *
                p09ComplexNorm2 x := by
          rw [h4]
          rw [hBc]
          simp only [p09Alpha, if_pos rfl]
          norm_num
          exact mul_le_mul_of_nonneg_right (by nlinarith [model.epsilon_pos]) hn
    · let A : ℝ := 3 + 2 * model.gamma
      let B₁ : ℝ := 2 + 10 * model.gamma
      let C : ℝ := (4 : ℝ) ^ stage.radix *
        ((stage.radix : ℝ) + 1) ^ 2
      let D : ℝ := B₁ + (stage.radix : ℝ) * (A + B₁) +
        C * (1 + A + B₁)
      have hA : 0 ≤ A := by dsimp [A]; nlinarith [model.gamma_nonneg]
      have hB₁ : 0 ≤ B₁ := by dsimp [B₁]; nlinarith [model.gamma_nonneg]
      have hC : 0 ≤ C := by positivity
      have hD : 0 ≤ D := by
        dsimp [D]
        positivity
      have hBc : p09BlockSecondCoeff stage model.gamma =
          Real.sqrt (stage.radix : ℝ) * D := by
        simp [p09BlockSecondCoeff, h2, h4, D, C, B₁, A]
      constructor
      · simp [p09BlockSecondCoeff, h2, h4, D, C, B₁, A]
        positivity
      have hp (b : Fin stage.blockCount) (k : ZMod stage.radix) :
          ‖err (b, k)‖ ≤
            (model.epsilon * ((stage.radix : ℝ) + 3 + 2 * model.gamma) +
              D * model.epsilon ^ 2) *
              (∑ j : ZMod stage.radix, ‖inp (b, j)‖) := by
        let xb : ZMod stage.radix → ℂ := fun j =>
          permuted (stage.reindex (b, j))
        have hb := p09_roundedGenericRadixBlock_error model he xb k
        simpa [err, inp, xb, permuted, p09RoundedMixedRadixBlockApply,
          p09MixedRadixBlockApply, h2, h4, D, C, B₁, A] using hb
      have hfactor : 0 ≤
          model.epsilon * ((stage.radix : ℝ) + 3 + 2 * model.gamma) +
            D * model.epsilon ^ 2 := by
        have hq : (0 : ℝ) ≤ stage.radix := by positivity
        have hlin : 0 ≤ (stage.radix : ℝ) + 3 + 2 * model.gamma := by
          nlinarith [model.gamma_nonneg]
        exact add_nonneg (mul_nonneg (le_of_lt model.epsilon_pos) hlin)
          (mul_nonneg hD (sq_nonneg model.epsilon))
      have hb := p09L2_block_bound
        (model.epsilon * ((stage.radix : ℝ) + 3 + 2 * model.gamma) +
          D * model.epsilon ^ 2) hfactor err inp hp
      rw [herrNorm, hinpNorm] at hb
      rw [ZMod.card] at hb
      have hq2 := stage.radix_two_le
      have hq3 : 3 ≤ stage.radix := by omega
      have hq0 : (0 : ℝ) ≤ stage.radix := by positivity
      have hsqrt : Real.sqrt (stage.radix : ℝ) ^ 2 = stage.radix :=
        Real.sq_sqrt hq0
      have hlead : (stage.radix : ℝ) *
          ((stage.radix : ℝ) + 3 + 2 * model.gamma) ≤
          Real.sqrt (stage.radix : ℝ) *
            (2 * Real.sqrt (stage.radix : ℝ) *
              ((stage.radix : ℝ) + model.gamma)) := by
        have hinner : (stage.radix : ℝ) + 3 + 2 * model.gamma ≤
            2 * ((stage.radix : ℝ) + model.gamma) := by
          have hq3r : (3 : ℝ) ≤ stage.radix := by exact_mod_cast hq3
          nlinarith
        calc
          (stage.radix : ℝ) * ((stage.radix : ℝ) + 3 + 2 * model.gamma) ≤
              (stage.radix : ℝ) * (2 * ((stage.radix : ℝ) + model.gamma)) :=
            mul_le_mul_of_nonneg_left hinner hq0
          _ = Real.sqrt (stage.radix : ℝ) *
              (2 * Real.sqrt (stage.radix : ℝ) *
                ((stage.radix : ℝ) + model.gamma)) := by
            rw [show Real.sqrt (stage.radix : ℝ) *
                (2 * Real.sqrt (stage.radix : ℝ) *
                  ((stage.radix : ℝ) + model.gamma)) =
                2 * Real.sqrt (stage.radix : ℝ) ^ 2 *
                  ((stage.radix : ℝ) + model.gamma) by ring, hsqrt]
            ring
      have hrem : (stage.radix : ℝ) * D =
          Real.sqrt (stage.radix : ℝ) *
            (Real.sqrt (stage.radix : ℝ) * D) := by
        calc
          (stage.radix : ℝ) * D = Real.sqrt (stage.radix : ℝ) ^ 2 * D := by
            rw [hsqrt]
          _ = _ := by ring
      have hn : 0 ≤ p09ComplexNorm2 x := Real.sqrt_nonneg _
      have he0 := le_of_lt model.epsilon_pos
      have hcoeff : (stage.radix : ℝ) *
            (model.epsilon * ((stage.radix : ℝ) + 3 + 2 * model.gamma) +
              D * model.epsilon ^ 2) ≤
          Real.sqrt (stage.radix : ℝ) *
            (model.epsilon * (2 * Real.sqrt (stage.radix : ℝ) *
              ((stage.radix : ℝ) + model.gamma)) +
              (Real.sqrt (stage.radix : ℝ) * D) * model.epsilon ^ 2) := by
        calc
          (stage.radix : ℝ) *
              (model.epsilon * ((stage.radix : ℝ) + 3 + 2 * model.gamma) +
                D * model.epsilon ^ 2) =
              model.epsilon * ((stage.radix : ℝ) *
                ((stage.radix : ℝ) + 3 + 2 * model.gamma)) +
                model.epsilon ^ 2 * ((stage.radix : ℝ) * D) := by ring
          _ ≤ model.epsilon * (Real.sqrt (stage.radix : ℝ) *
                (2 * Real.sqrt (stage.radix : ℝ) *
                  ((stage.radix : ℝ) + model.gamma))) +
              model.epsilon ^ 2 * (Real.sqrt (stage.radix : ℝ) *
                (Real.sqrt (stage.radix : ℝ) * D)) :=
            add_le_add (mul_le_mul_of_nonneg_left hlead he0)
              (mul_le_mul_of_nonneg_left hrem.le (sq_nonneg model.epsilon))
          _ = _ := by ring
      calc
        p09ComplexNorm2 (fun i => p09RoundedMixedRadixBlockApply model stage x i -
            p09MixedRadixBlockApply stage x i) ≤
            (stage.radix : ℝ) *
              (model.epsilon * ((stage.radix : ℝ) + 3 + 2 * model.gamma) +
                D * model.epsilon ^ 2) * p09ComplexNorm2 x := hb
        _ ≤ Real.sqrt (stage.radix : ℝ) *
              (model.epsilon * (2 * Real.sqrt (stage.radix : ℝ) *
                ((stage.radix : ℝ) + model.gamma)) +
                (Real.sqrt (stage.radix : ℝ) * D) * model.epsilon ^ 2) *
              p09ComplexNorm2 x := mul_le_mul_of_nonneg_right hcoeff hn
        _ = Real.sqrt (stage.radix : ℝ) *
              (model.epsilon * p09Alpha stage.radix model.gamma +
                p09BlockSecondCoeff stage model.gamma * model.epsilon ^ 2) *
              p09ComplexNorm2 x := by rw [hBc]; simp [p09Alpha, h2, h4]

lemma p09L2_pointwise_bound {I : Type*} [Fintype I]
    (a : ℝ) (ha : 0 ≤ a) (e x : I → ℂ)
    (h : ∀ i, ‖e i‖ ≤ a * ‖x i‖) :
    p09L2 e ≤ a * p09L2 x := by
  let E : ℝ := ∑ i, ‖e i‖ ^ 2
  let X : ℝ := ∑ i, ‖x i‖ ^ 2
  have hX : 0 ≤ X := Finset.sum_nonneg fun _ _ => sq_nonneg _
  have hE : E ≤ a ^ 2 * X := by
    dsimp [E, X]
    calc
      (∑ i, ‖e i‖ ^ 2) ≤ ∑ i, (a * ‖x i‖) ^ 2 := by
        exact Finset.sum_le_sum fun i _ =>
          (sq_le_sq₀ (norm_nonneg _) (mul_nonneg ha (norm_nonneg _))).2 (h i)
      _ = a ^ 2 * ∑ i, ‖x i‖ ^ 2 := by rw [Finset.mul_sum]; ring
  simp only [p09L2]
  rw [Real.sqrt_le_iff]
  constructor
  · positivity
  · rw [mul_pow, Real.sq_sqrt hX]
    exact hE

lemma p09ComplexNorm2_triangle {n : ℕ} [NeZero n]
    (x y z : ZMod n → ℂ) (h : ∀ i, x i = y i + z i) :
    p09ComplexNorm2 x ≤ p09ComplexNorm2 y + p09ComplexNorm2 z := by
  simp only [p09ComplexNorm2, p09ComplexNorm2Sq]
  have heq : (WithLp.toLp 2 x : EuclideanSpace ℂ (ZMod n)) =
      WithLp.toLp 2 y + WithLp.toLp 2 z := by
    ext i
    simp [h]
  simpa only [EuclideanSpace.norm_eq] using
    (show ‖(WithLp.toLp 2 x : EuclideanSpace ℂ (ZMod n))‖ ≤
        ‖(WithLp.toLp 2 y : EuclideanSpace ℂ (ZMod n))‖ +
          ‖(WithLp.toLp 2 z : EuclideanSpace ℂ (ZMod n))‖ by
      rw [heq]
      exact norm_add_le _ _)

lemma p09MixedRadixTwiddleApply_norm {n : ℕ} [NeZero n]
    (stage : P09MixedRadixStage n) (x : ZMod n → ℂ) :
    p09ComplexNorm2 (p09MixedRadixTwiddleApply stage x) = p09ComplexNorm2 x := by
  simp only [p09ComplexNorm2, p09ComplexNorm2Sq,
    p09MixedRadixTwiddleApply]
  congr 1
  apply Finset.sum_congr rfl
  intro i _
  split_ifs
  · rw [norm_mul, p09_stdAddChar_norm, one_mul]
  · rfl

lemma p09_roundedMixedRadixTwiddleApply_error {n : ℕ} [NeZero n]
    (model : P09WilkinsonModel) (he : model.epsilon ≤ 1)
    (stage : P09MixedRadixStage n) (x : ZMod n → ℂ) :
    p09ComplexNorm2 (fun i =>
      p09RoundedMixedRadixTwiddleApply model stage x i -
        p09MixedRadixTwiddleApply stage x i) ≤
      (if stage.useTwiddle then
        ((3 + 2 * model.gamma) * model.epsilon +
          (2 + 10 * model.gamma) * model.epsilon ^ 2) * p09ComplexNorm2 x
       else 0) := by
  by_cases ht : stage.useTwiddle
  · rw [if_pos ht, p09ComplexNorm2_eq_l2, p09ComplexNorm2_eq_l2]
    apply p09L2_pointwise_bound
    · exact add_nonneg
        (mul_nonneg (by nlinarith [model.gamma_nonneg])
          (le_of_lt model.epsilon_pos))
        (mul_nonneg (by nlinarith [model.gamma_nonneg])
          (sq_nonneg model.epsilon))
    · intro i
      simpa [p09RoundedMixedRadixTwiddleApply, p09MixedRadixTwiddleApply, ht,
        mul_comm] using p09_roundedTwiddleMul_error_quadratic model he
          (stage.twiddleExponent i) (x i)
  · rw [if_neg ht]
    simp [p09RoundedMixedRadixTwiddleApply, p09MixedRadixTwiddleApply, ht,
      p09ComplexNorm2, p09ComplexNorm2Sq]

lemma p09Alpha_nonneg (q : ℕ) (hq : 2 ≤ q) (g : ℝ) (hg : 0 ≤ g) :
    0 ≤ p09Alpha q g := by
  rw [p09Alpha]
  split_ifs
  · positivity
  · norm_num
  · have hqr : (0 : ℝ) ≤ q := by positivity
    positivity

noncomputable def p09StageSecondCoeff {n : ℕ} [NeZero n]
    (stage : P09MixedRadixStage n) (g : ℝ) : ℝ :=
  let Bb := p09BlockSecondCoeff stage g
  if stage.useTwiddle then
    (2 + 10 * g) + Bb + ((3 + 2 * g) + (2 + 10 * g)) *
      (p09Alpha stage.radix g + Bb)
  else Bb

lemma p09_roundedMixedRadixStageApply_error {n : ℕ} [NeZero n]
    (model : P09WilkinsonModel) (he : model.epsilon ≤ 1)
    (stage : P09MixedRadixStage n)
    (hscale : ∀ z : ZMod n → ℂ,
      p09ComplexNorm2 (p09MixedRadixStageApply stage z) =
        Real.sqrt (stage.radix : ℝ) * p09ComplexNorm2 z)
    (x : ZMod n → ℂ) :
    0 ≤ p09StageSecondCoeff stage model.gamma ∧
      p09ComplexNorm2 (fun i =>
        p09RoundedMixedRadixStageApply model stage x i -
          p09MixedRadixStageApply stage x i) ≤
        Real.sqrt (stage.radix : ℝ) *
          (model.epsilon *
              (p09Alpha stage.radix model.gamma +
                if stage.useTwiddle then 3 + 2 * model.gamma else 0) +
            p09StageSecondCoeff stage model.gamma * model.epsilon ^ 2) *
              p09ComplexNorm2 x := by
  let Bb := p09BlockSecondCoeff stage model.gamma
  have hblock := p09_roundedMixedRadixBlockApply_error model he stage x
  have hBb : 0 ≤ Bb := by simpa [Bb] using hblock.1
  have hb := hblock.2
  let rb := p09RoundedMixedRadixBlockApply model stage x
  let eb := p09MixedRadixBlockApply stage x
  let db : ZMod n → ℂ := fun i => rb i - eb i
  have hdb : p09ComplexNorm2 db ≤
      Real.sqrt (stage.radix : ℝ) *
        (model.epsilon * p09Alpha stage.radix model.gamma +
          Bb * model.epsilon ^ 2) * p09ComplexNorm2 x := by
    simpa [db, rb, eb] using hb
  have heb : p09ComplexNorm2 eb =
      Real.sqrt (stage.radix : ℝ) * p09ComplexNorm2 x := by
    rw [← hscale x]
    exact (p09MixedRadixTwiddleApply_norm stage eb).symm
  have hrb : p09ComplexNorm2 rb ≤ p09ComplexNorm2 eb + p09ComplexNorm2 db := by
    apply p09ComplexNorm2_triangle rb eb db
    intro i
    simp [db]
  by_cases ht : stage.useTwiddle
  · let A : ℝ := 3 + 2 * model.gamma
    let Bt : ℝ := 2 + 10 * model.gamma
    let alpha : ℝ := p09Alpha stage.radix model.gamma
    let B : ℝ := Bt + Bb + (A + Bt) * (alpha + Bb)
    have hA : 0 ≤ A := by dsimp [A]; nlinarith [model.gamma_nonneg]
    have hBt : 0 ≤ Bt := by dsimp [Bt]; nlinarith [model.gamma_nonneg]
    have halpha : 0 ≤ alpha :=
      p09Alpha_nonneg stage.radix stage.radix_two_le model.gamma model.gamma_nonneg
    have hB : 0 ≤ B := by dsimp [B]; positivity
    constructor
    · simpa [p09StageSecondCoeff, ht, B, A, Bt, alpha, Bb] using hB
    let dt : ZMod n → ℂ := fun i =>
      p09RoundedMixedRadixTwiddleApply model stage rb i -
        p09MixedRadixTwiddleApply stage rb i
    let pdb : ZMod n → ℂ := p09MixedRadixTwiddleApply stage db
    have hdt : p09ComplexNorm2 dt ≤
        (A * model.epsilon + Bt * model.epsilon ^ 2) * p09ComplexNorm2 rb := by
      have h := p09_roundedMixedRadixTwiddleApply_error model he stage rb
      simpa [ht, dt, A, Bt, mul_comm] using h
    have hpdb : p09ComplexNorm2 pdb = p09ComplexNorm2 db :=
      p09MixedRadixTwiddleApply_norm stage db
    have hsplit : ∀ i,
        p09RoundedMixedRadixStageApply model stage x i -
            p09MixedRadixStageApply stage x i = dt i + pdb i := by
      intro i
      simp only [p09RoundedMixedRadixStageApply, p09MixedRadixStageApply,
        dt, pdb, rb, eb, db]
      simp [p09RoundedMixedRadixTwiddleApply, p09MixedRadixTwiddleApply, ht]
      ring
    have htri := p09ComplexNorm2_triangle _ dt pdb hsplit
    have he0 : 0 ≤ model.epsilon := le_of_lt model.epsilon_pos
    have hn : 0 ≤ p09ComplexNorm2 x := Real.sqrt_nonneg _
    have hs : 0 ≤ Real.sqrt (stage.radix : ℝ) := Real.sqrt_nonneg _
    have htbound : A * model.epsilon + Bt * model.epsilon ^ 2 ≤
        model.epsilon * (A + Bt) := by
      have he2 : model.epsilon ^ 2 ≤ model.epsilon := by
        nlinarith [sq_nonneg model.epsilon]
      nlinarith [mul_le_mul_of_nonneg_left he2 hBt]
    have hbbound : model.epsilon * alpha + Bb * model.epsilon ^ 2 ≤
        model.epsilon * (alpha + Bb) := by
      have he2 : model.epsilon ^ 2 ≤ model.epsilon := by
        nlinarith [sq_nonneg model.epsilon]
      nlinarith [mul_le_mul_of_nonneg_left he2 hBb]
    calc
      p09ComplexNorm2 (fun i =>
          p09RoundedMixedRadixStageApply model stage x i -
            p09MixedRadixStageApply stage x i) ≤
          p09ComplexNorm2 dt + p09ComplexNorm2 pdb := htri
      _ ≤ (A * model.epsilon + Bt * model.epsilon ^ 2) *
            p09ComplexNorm2 rb + p09ComplexNorm2 db := by
          rw [hpdb]
          exact add_le_add_left hdt _
      _ ≤ (A * model.epsilon + Bt * model.epsilon ^ 2) *
            (p09ComplexNorm2 eb + p09ComplexNorm2 db) + p09ComplexNorm2 db := by
          exact add_le_add_left
            (mul_le_mul_of_nonneg_left hrb (by positivity)) _
      _ ≤ (A * model.epsilon + Bt * model.epsilon ^ 2) *
            (Real.sqrt (stage.radix : ℝ) * p09ComplexNorm2 x +
              Real.sqrt (stage.radix : ℝ) *
                (model.epsilon * alpha + Bb * model.epsilon ^ 2) *
                  p09ComplexNorm2 x) +
            Real.sqrt (stage.radix : ℝ) *
              (model.epsilon * alpha + Bb * model.epsilon ^ 2) *
                p09ComplexNorm2 x := by
          rw [heb]
          have hcoef : 0 ≤ A * model.epsilon + Bt * model.epsilon ^ 2 := by positivity
          exact add_le_add
            (mul_le_mul_of_nonneg_left (add_le_add_right hdb _) hcoef) hdb
      _ ≤ Real.sqrt (stage.radix : ℝ) *
            (model.epsilon * (alpha + A) + B * model.epsilon ^ 2) *
              p09ComplexNorm2 x := by
          have hcross := mul_le_mul_of_nonneg_right
            (mul_le_mul htbound hbbound (by positivity) (by positivity))
            (mul_nonneg hs hn)
          dsimp [B]
          nlinarith [mul_nonneg he0 (mul_nonneg hs hn),
            mul_nonneg (sq_nonneg model.epsilon) (mul_nonneg hs hn)]
      _ = Real.sqrt (stage.radix : ℝ) *
            (model.epsilon *
              (p09Alpha stage.radix model.gamma +
                if stage.useTwiddle then 3 + 2 * model.gamma else 0) +
              p09StageSecondCoeff stage model.gamma * model.epsilon ^ 2) *
                p09ComplexNorm2 x := by
          simp [p09StageSecondCoeff, ht, B, A, Bt, alpha, Bb]
  · constructor
    · simpa [p09StageSecondCoeff, ht, Bb] using hBb
    simpa [p09RoundedMixedRadixStageApply, p09MixedRadixStageApply,
      p09RoundedMixedRadixTwiddleApply, p09MixedRadixTwiddleApply, ht, rb, eb,
      db, p09StageSecondCoeff, Bb] using hdb

lemma p09MixedRadixStageApply_sub {n : ℕ} [NeZero n]
    (stage : P09MixedRadixStage n) (x y : ZMod n → ℂ) :
    p09MixedRadixStageApply stage x - p09MixedRadixStageApply stage y =
      p09MixedRadixStageApply stage (fun i => x i - y i) := by
  funext i
  simp only [Pi.sub_apply, p09MixedRadixStageApply,
    p09MixedRadixTwiddleApply, p09MixedRadixBlockApply]
  split_ifs <;>
    simp only [mul_sub, Finset.sum_sub_distrib]

noncomputable def p09StageScale {n : ℕ} [NeZero n]
    (stage : P09MixedRadixStage n) : ℝ :=
  Real.sqrt (stage.radix : ℝ)

noncomputable def p09StageFirstCoeff {n : ℕ} [NeZero n]
    (stage : P09MixedRadixStage n) (g : ℝ) : ℝ :=
  p09Alpha stage.radix g + if stage.useTwiddle then 3 + 2 * g else 0

noncomputable def p09StageListScale {n : ℕ} [NeZero n]
    (stages : List (P09MixedRadixStage n)) : ℝ :=
  (stages.map p09StageScale).prod

noncomputable def p09StageListFirstCoeff {n : ℕ} [NeZero n]
    (stages : List (P09MixedRadixStage n)) (g : ℝ) : ℝ :=
  (stages.map (fun s => p09StageFirstCoeff s g)).sum

noncomputable def p09StageListCoeffState {n : ℕ} [NeZero n]
    (stages : List (P09MixedRadixStage n)) (g : ℝ) : ℝ × ℝ :=
  stages.foldl (fun p s =>
    (p.1 + p09StageFirstCoeff s g,
      p09StageSecondCoeff s g + p.2 +
        (p09StageFirstCoeff s g + p09StageSecondCoeff s g) *
          (p.1 + p.2))) (0, 0)

noncomputable def p09StageListSecondCoeff {n : ℕ} [NeZero n]
    (stages : List (P09MixedRadixStage n)) (g : ℝ) : ℝ :=
  (p09StageListCoeffState stages g).2

lemma p09StageListCoeffState_fst {n : ℕ} [NeZero n]
    (stages : List (P09MixedRadixStage n)) (g : ℝ) :
    (p09StageListCoeffState stages g).1 =
      p09StageListFirstCoeff stages g := by
  induction stages using List.reverseRecOn with
  | nil => simp [p09StageListCoeffState, p09StageListFirstCoeff]
  | append_singleton stages s ih =>
      rw [p09StageListCoeffState, List.foldl_append]
      simp only [List.foldl]
      change (p09StageListCoeffState stages g).1 + p09StageFirstCoeff s g =
        p09StageListFirstCoeff (stages ++ [s]) g
      rw [ih]
      simp [p09StageListFirstCoeff]

lemma p09_stageList_exact_norm {n : ℕ} [NeZero n]
    (stages : List (P09MixedRadixStage n))
    (hscale : ∀ s ∈ stages, ∀ z : ZMod n → ℂ,
      p09ComplexNorm2 (p09MixedRadixStageApply s z) =
        p09StageScale s * p09ComplexNorm2 z)
    (x : ZMod n → ℂ) :
    p09ComplexNorm2
        (stages.foldl (fun state s => p09MixedRadixStageApply s state) x) =
      p09StageListScale stages * p09ComplexNorm2 x := by
  induction stages using List.reverseRecOn with
  | nil => simp [p09StageListScale]
  | append_singleton stages s ih =>
      rw [List.foldl_append]
      simp only [List.foldl]
      rw [hscale s (by simp)]
      rw [ih (by intro t ht; exact hscale t (by simp [ht]))]
      simp [p09StageListScale]
      ring

lemma p09_roundedStageList_error {n : ℕ} [NeZero n]
    (model : P09WilkinsonModel) (he : model.epsilon ≤ 1)
    (stages : List (P09MixedRadixStage n))
    (hscale : ∀ s ∈ stages, ∀ z : ZMod n → ℂ,
      p09ComplexNorm2 (p09MixedRadixStageApply s z) =
        p09StageScale s * p09ComplexNorm2 z)
    (x : ZMod n → ℂ) :
    0 ≤ p09StageListSecondCoeff stages model.gamma ∧
      p09ComplexNorm2 (fun i =>
        (stages.foldl
          (fun state s => p09RoundedMixedRadixStageApply model s state) x) i -
        (stages.foldl
          (fun state s => p09MixedRadixStageApply s state) x) i) ≤
      p09StageListScale stages *
        (model.epsilon * p09StageListFirstCoeff stages model.gamma +
          p09StageListSecondCoeff stages model.gamma * model.epsilon ^ 2) *
            p09ComplexNorm2 x := by
  induction stages using List.reverseRecOn with
  | nil =>
      constructor
      · simp [p09StageListSecondCoeff, p09StageListCoeffState]
      simp [p09ComplexNorm2, p09ComplexNorm2Sq, p09StageListScale,
        p09StageListFirstCoeff, p09StageListSecondCoeff, p09StageListCoeffState]
  | append_singleton stages s ih =>
      have hs_mem : s ∈ stages ++ [s] := by simp
      have hsscale := hscale s hs_mem
      have hpreScale : ∀ t ∈ stages, ∀ z : ZMod n → ℂ,
          p09ComplexNorm2 (p09MixedRadixStageApply t z) =
            p09StageScale t * p09ComplexNorm2 z := by
        intro t ht
        exact hscale t (by simp [ht])
      let Bp := p09StageListSecondCoeff stages model.gamma
      have hprev := ih hpreScale
      have hBp : 0 ≤ Bp := by simpa [Bp] using hprev.1
      have hp := hprev.2
      let xr := stages.foldl
        (fun state t => p09RoundedMixedRadixStageApply model t state) x
      let xe := stages.foldl (fun state t => p09MixedRadixStageApply t state) x
      let d : ZMod n → ℂ := fun i => xr i - xe i
      have hd : p09ComplexNorm2 d ≤
          p09StageListScale stages *
            (model.epsilon * p09StageListFirstCoeff stages model.gamma +
              Bp * model.epsilon ^ 2) * p09ComplexNorm2 x := by
        simpa [d, xr, xe] using hp
      have hxe : p09ComplexNorm2 xe =
          p09StageListScale stages * p09ComplexNorm2 x :=
        p09_stageList_exact_norm stages hpreScale x
      have hxr : p09ComplexNorm2 xr ≤ p09ComplexNorm2 xe + p09ComplexNorm2 d := by
        apply p09ComplexNorm2_triangle xr xe d
        intro i
        simp [d]
      let Bs := p09StageSecondCoeff s model.gamma
      have hstage := p09_roundedMixedRadixStageApply_error model he s hsscale xr
      have hBs : 0 ≤ Bs := by simpa [Bs] using hstage.1
      have hs := hstage.2
      let As := p09StageFirstCoeff s model.gamma
      let Ap := p09StageListFirstCoeff stages model.gamma
      let B : ℝ := Bs + Bp + (As + Bs) * (Ap + Bp)
      have hAs : 0 ≤ As := by
        dsimp [As, p09StageFirstCoeff]
        exact add_nonneg
          (p09Alpha_nonneg s.radix s.radix_two_le model.gamma model.gamma_nonneg)
          (by split_ifs <;> nlinarith [model.gamma_nonneg])
      have hAp : 0 ≤ Ap := by
        dsimp [Ap, p09StageListFirstCoeff]
        apply List.sum_nonneg
        intro a ha
        simp only [List.mem_map] at ha
        rcases ha with ⟨t, ht, rfl⟩
        dsimp [p09StageFirstCoeff]
        exact add_nonneg
          (p09Alpha_nonneg t.radix t.radix_two_le model.gamma model.gamma_nonneg)
          (by split_ifs <;> nlinarith [model.gamma_nonneg])
      have hB : 0 ≤ B := by dsimp [B]; positivity
      have hBeq : p09StageListSecondCoeff (stages ++ [s]) model.gamma = B := by
        rw [p09StageListSecondCoeff, p09StageListCoeffState, List.foldl_append]
        simp only [List.foldl]
        change Bs + Bp + (As + Bs) *
          ((p09StageListCoeffState stages model.gamma).1 + Bp) = B
        rw [p09StageListCoeffState_fst]
      constructor
      · rw [hBeq]
        exact hB
      let loc : ZMod n → ℂ := fun i =>
        p09RoundedMixedRadixStageApply model s xr i -
          p09MixedRadixStageApply s xr i
      let propagated : ZMod n → ℂ := p09MixedRadixStageApply s d
      have hlocal : p09ComplexNorm2 loc ≤
          p09StageScale s *
            (model.epsilon * As + Bs * model.epsilon ^ 2) *
              p09ComplexNorm2 xr := by
        simpa [loc, As, p09StageScale, p09StageFirstCoeff] using hs
      have hprop : p09ComplexNorm2 propagated =
          p09StageScale s * p09ComplexNorm2 d := hsscale d
      have hsplit : ∀ i,
          p09RoundedMixedRadixStageApply model s xr i -
              p09MixedRadixStageApply s xe i = loc i + propagated i := by
        intro i
        have hlin := congrFun (p09MixedRadixStageApply_sub s xr xe) i
        simp only [Pi.sub_apply] at hlin
        dsimp [loc, propagated, d]
        rw [← hlin]
        ring
      have htri := p09ComplexNorm2_triangle _ loc propagated hsplit
      have he0 : 0 ≤ model.epsilon := le_of_lt model.epsilon_pos
      have he2 : model.epsilon ^ 2 ≤ model.epsilon := by
        nlinarith [sq_nonneg model.epsilon]
      have htbound : model.epsilon * As + Bs * model.epsilon ^ 2 ≤
          model.epsilon * (As + Bs) := by
        nlinarith [mul_le_mul_of_nonneg_left he2 hBs]
      have hpbound : model.epsilon * Ap + Bp * model.epsilon ^ 2 ≤
          model.epsilon * (Ap + Bp) := by
        nlinarith [mul_le_mul_of_nonneg_left he2 hBp]
      have hscale0 : 0 ≤ p09StageScale s := Real.sqrt_nonneg _
      have hpre0 : 0 ≤ p09StageListScale stages := by
        dsimp [p09StageListScale]
        apply List.prod_nonneg
        intro a ha
        simp only [List.mem_map] at ha
        rcases ha with ⟨t, ht, rfl⟩
        exact Real.sqrt_nonneg _
      rw [List.foldl_append, List.foldl_append]
      simp only [List.foldl]
      calc
        p09ComplexNorm2 (fun i =>
            p09RoundedMixedRadixStageApply model s xr i -
              p09MixedRadixStageApply s xe i) ≤
            p09ComplexNorm2 loc + p09ComplexNorm2 propagated := htri
        _ ≤ p09StageScale s *
              (model.epsilon * As + Bs * model.epsilon ^ 2) *
                p09ComplexNorm2 xr +
            p09StageScale s * p09ComplexNorm2 d := by
          rw [hprop]
          exact add_le_add_left hlocal _
        _ ≤ p09StageScale s *
              (model.epsilon * As + Bs * model.epsilon ^ 2) *
                (p09ComplexNorm2 xe + p09ComplexNorm2 d) +
            p09StageScale s * p09ComplexNorm2 d := by
          exact add_le_add_left
            (mul_le_mul_of_nonneg_left hxr
              (mul_nonneg hscale0 (add_nonneg
                (mul_nonneg he0 hAs) (mul_nonneg hBs (sq_nonneg model.epsilon))))) _
        _ ≤ p09StageScale s *
              (model.epsilon * As + Bs * model.epsilon ^ 2) *
                (p09StageListScale stages * p09ComplexNorm2 x +
                  p09StageListScale stages *
                    (model.epsilon * Ap + Bp * model.epsilon ^ 2) *
                      p09ComplexNorm2 x) +
            p09StageScale s *
              (p09StageListScale stages *
                (model.epsilon * Ap + Bp * model.epsilon ^ 2) *
                  p09ComplexNorm2 x) := by
          rw [hxe]
          have hc : 0 ≤ p09StageScale s *
              (model.epsilon * As + Bs * model.epsilon ^ 2) :=
            mul_nonneg hscale0 (add_nonneg (mul_nonneg he0 hAs)
              (mul_nonneg hBs (sq_nonneg model.epsilon)))
          exact add_le_add
            (mul_le_mul_of_nonneg_left (add_le_add_right hd _) hc)
            (mul_le_mul_of_nonneg_left hd hscale0)
        _ ≤ p09StageListScale (stages ++ [s]) *
              (model.epsilon * p09StageListFirstCoeff (stages ++ [s]) model.gamma +
                p09StageListSecondCoeff (stages ++ [s]) model.gamma *
                  model.epsilon ^ 2) * p09ComplexNorm2 x := by
          have hx0 : 0 ≤ p09ComplexNorm2 x := Real.sqrt_nonneg _
          have hleftPrev : 0 ≤ model.epsilon * Ap + Bp * model.epsilon ^ 2 :=
            add_nonneg (mul_nonneg he0 hAp) (mul_nonneg hBp (sq_nonneg model.epsilon))
          have hrightStage : 0 ≤ model.epsilon * (As + Bs) :=
            mul_nonneg he0 (add_nonneg hAs hBs)
          have hcross := mul_le_mul htbound hpbound hleftPrev hrightStage
          have hcoef :
              (model.epsilon * As + Bs * model.epsilon ^ 2) *
                  (1 + (model.epsilon * Ap + Bp * model.epsilon ^ 2)) +
                (model.epsilon * Ap + Bp * model.epsilon ^ 2) ≤
              model.epsilon * (Ap + As) + B * model.epsilon ^ 2 := by
            dsimp [B]
            nlinarith
          have hQ : 0 ≤ p09StageScale s * p09StageListScale stages *
              p09ComplexNorm2 x := by positivity
          have hmul := mul_le_mul_of_nonneg_left hcoef hQ
          rw [hBeq]
          convert hmul using 1 <;>
            simp [p09StageListScale, p09StageListFirstCoeff, As, Ap] <;> ring

lemma p09_fin_sum_except_last (r : ℕ) (c : ℝ) :
    (∑ i : Fin r, if i.val + 1 < r then c else 0) = (r - 1 : ℕ) * c := by
  cases r with
  | zero => simp
  | succ r =>
      rw [Fin.sum_univ_castSucc]
      simp

lemma p09_plan_stageListScale {n : ℕ} [NeZero n]
    (plan : P09MixedRadixFftPlan n) :
    p09StageListScale (List.ofFn plan.stage) = Real.sqrt (n : ℝ) := by
  have hprod : (∏ i : Fin plan.stageCount,
      Real.sqrt ((plan.stage i).radix : ℝ)) =
      Real.sqrt (∏ i : Fin plan.stageCount, ((plan.stage i).radix : ℝ)) := by
    rw [Real.sqrt_prod Finset.univ (by intro i _; positivity)]
  rw [p09StageListScale]
  rw [List.map_ofFn]
  change (List.ofFn (fun i : Fin plan.stageCount =>
    Real.sqrt ((plan.stage i).radix : ℝ))).prod = _
  rw [List.prod_ofFn, hprod]
  congr 1
  exact_mod_cast plan.order_factorization

lemma p09_plan_stageListFirstCoeff {n : ℕ} [NeZero n]
    (plan : P09MixedRadixFftPlan n) (g : ℝ) :
    p09StageListFirstCoeff (List.ofFn plan.stage) g = p09K plan g := by
  rw [p09StageListFirstCoeff]
  rw [List.map_ofFn]
  change (List.ofFn (fun i : Fin plan.stageCount =>
    p09Alpha (plan.stage i).radix g +
      if (plan.stage i).useTwiddle then 3 + 2 * g else 0)).sum = _
  rw [List.sum_ofFn]
  simp only [plan.twiddle_pattern]
  rw [Finset.sum_add_distrib]
  have htw : (∑ i : Fin plan.stageCount,
      if decide (i.val + 1 < plan.stageCount) = true then 3 + 2 * g else 0) =
      ((plan.stageCount - 1 : ℕ) : ℝ) * (3 + 2 * g) := by
    simpa only [decide_eq_true_eq] using
      p09_fin_sum_except_last plan.stageCount (3 + 2 * g)
  rw [htw]
  rw [p09K]
  congr 1
  rw [Nat.cast_sub (Nat.one_le_iff_ne_zero.mpr
    (Nat.ne_of_gt plan.stageCount_pos)), Nat.cast_one]

noncomputable def p09FftSecondCoeff {n : ℕ} [NeZero n]
    (plan : P09MixedRadixFftPlan n) (g : ℝ) : ℝ :=
  p09StageListSecondCoeff (List.ofFn plan.stage) g

lemma p09_roundedFftApply_error {n : ℕ} [NeZero n]
    (plan : P09MixedRadixFftPlan n) (model : P09WilkinsonModel)
    (he : model.epsilon ≤ 1) (x : ZMod n → ℂ) :
    0 ≤ p09FftSecondCoeff plan model.gamma ∧
      p09ComplexNorm2 (fun i =>
        p09RoundedFftApply plan model x i - p09FourierTransform x i) ≤
      Real.sqrt (n : ℝ) *
        (model.epsilon * p09K plan model.gamma +
          p09FftSecondCoeff plan model.gamma * model.epsilon ^ 2) *
          p09ComplexNorm2 x := by
  let stages := List.ofFn plan.stage
  have hscale : ∀ s ∈ stages, ∀ z : ZMod n → ℂ,
      p09ComplexNorm2 (p09MixedRadixStageApply s z) =
        p09StageScale s * p09ComplexNorm2 z := by
    intro s hs z
    rw [List.mem_ofFn] at hs
    rcases hs with ⟨i, rfl⟩
    simpa [p09StageScale] using plan.stage_norm_scaling i z
  have hlist := p09_roundedStageList_error model he stages hscale x
  constructor
  · simpa [p09FftSecondCoeff, stages] using hlist.1
  have hb := hlist.2
  let re : ZMod n → ℂ := fun i =>
    (stages.foldl (fun state s => p09RoundedMixedRadixStageApply model s state) x) i -
      (stages.foldl (fun state s => p09MixedRadixStageApply s state) x) i
  have herr : p09ComplexNorm2 (fun i =>
      p09RoundedFftApply plan model x i - p09FourierTransform x i) =
      p09ComplexNorm2 re := by
    have hexact := plan.exact_factorization x
    unfold p09RoundedFftApply p09ApplyRoundedMixedRadixStages
    rw [← hexact]
    rw [p09ComplexNorm2_eq_l2, p09ComplexNorm2_eq_l2]
    change p09L2 (fun i => re (plan.finalPermutation i)) = p09L2 re
    exact p09L2_equiv plan.finalPermutation re
  rw [herr]
  simpa [re, stages, p09_plan_stageListScale,
    p09_plan_stageListFirstCoeff, p09FftSecondCoeff] using hb

abbrev P09FiberIndex {m : ℕ} (axis : Fin m → P09FftAxis) (i : Fin m) :=
  {index : P09MultiIndex axis // index i = 0}

noncomputable def p09FiberEquiv {m : ℕ} (axis : Fin m → P09FftAxis)
    (i : Fin m) : P09FiberIndex axis i × ZMod (axis i).order ≃
      P09MultiIndex axis where
  toFun bj := Function.update bj.1.1 i bj.2
  invFun index := ⟨⟨Function.update index i 0, by simp⟩, index i⟩
  left_inv bj := by
    rcases bj with ⟨b, j⟩
    apply Prod.ext
    · apply Subtype.ext
      funext k
      by_cases hki : k = i
      · subst k
        simp [b.2]
      · simp [hki]
    · simp
  right_inv index := by
    funext k
    by_cases hki : k = i
    · subst k
      simp
    · simp [hki]

lemma p09MultiNorm2_eq_l2 {m : ℕ} {axis : Fin m → P09FftAxis}
    (x : P09MultiArray axis) : p09MultiNorm2 x = p09L2 x := by
  simp only [p09MultiNorm2, p09L2]
  rw [EuclideanSpace.norm_eq]

lemma p09_fourier_norm_scaling {n : ℕ} [NeZero n]
    (plan : P09MixedRadixFftPlan n) (x : ZMod n → ℂ) :
    p09ComplexNorm2 (p09FourierTransform x) =
      Real.sqrt (n : ℝ) * p09ComplexNorm2 x := by
  have hnNat : 0 < n := Nat.pos_of_ne_zero (NeZero.ne n)
  have hn : 0 < Real.sqrt (n : ℝ) := Real.sqrt_pos.2 (by exact_mod_cast hnNat)
  have h := plan.fourier_rms_scaling x
  rw [p09ComplexRms, p09ComplexRms] at h
  field_simp at h
  nlinarith

lemma p09L2_fiber_bound {B J : Type*} [Fintype B] [Fintype J]
    (a : ℝ) (ha : 0 ≤ a) (e x : B × J → ℂ)
    (h : ∀ b, p09L2 (fun j => e (b, j)) ≤
      a * p09L2 (fun j => x (b, j))) :
    p09L2 e ≤ a * p09L2 x := by
  let E : ℝ := ∑ z : B × J, ‖e z‖ ^ 2
  let X : ℝ := ∑ z : B × J, ‖x z‖ ^ 2
  have hX : 0 ≤ X := Finset.sum_nonneg fun _ _ => sq_nonneg _
  have hslice (b : B) : (∑ j : J, ‖e (b, j)‖ ^ 2) ≤
      a ^ 2 * (∑ j : J, ‖x (b, j)‖ ^ 2) := by
    have hb := h b
    rw [p09L2, p09L2] at hb
    have heSum : 0 ≤ ∑ j : J, ‖e (b, j)‖ ^ 2 :=
      Finset.sum_nonneg fun _ _ => sq_nonneg _
    have hxSum : 0 ≤ ∑ j : J, ‖x (b, j)‖ ^ 2 :=
      Finset.sum_nonneg fun _ _ => sq_nonneg _
    rw [← sq_le_sq₀ (Real.sqrt_nonneg _) (mul_nonneg ha (Real.sqrt_nonneg _)),
      mul_pow, Real.sq_sqrt heSum, Real.sq_sqrt hxSum] at hb
    exact hb
  have hE : E ≤ a ^ 2 * X := by
    rw [show E = ∑ b : B, ∑ j : J, ‖e (b, j)‖ ^ 2 by
      simp [E, Fintype.sum_prod_type]]
    rw [show X = ∑ b : B, ∑ j : J, ‖x (b, j)‖ ^ 2 by
      simp [X, Fintype.sum_prod_type]]
    calc
      (∑ b : B, ∑ j : J, ‖e (b, j)‖ ^ 2) ≤
          ∑ b : B, a ^ 2 * (∑ j : J, ‖x (b, j)‖ ^ 2) :=
        Finset.sum_le_sum fun b _ => hslice b
      _ = a ^ 2 * ∑ b : B, ∑ j : J, ‖x (b, j)‖ ^ 2 := by
        rw [Finset.mul_sum]
  rw [p09L2, p09L2, Real.sqrt_le_iff]
  constructor
  · positivity
  · rw [mul_pow, Real.sq_sqrt hX]
    exact hE

lemma p09L2_fiber_scale {B J : Type*} [Fintype B] [Fintype J]
    (a : ℝ) (ha : 0 ≤ a) (e x : B × J → ℂ)
    (h : ∀ b, p09L2 (fun j => e (b, j)) =
      a * p09L2 (fun j => x (b, j))) :
    p09L2 e = a * p09L2 x := by
  have hs (b : B) : (∑ j : J, ‖e (b, j)‖ ^ 2) =
      a ^ 2 * (∑ j : J, ‖x (b, j)‖ ^ 2) := by
    have hb := congrArg (fun z : ℝ => z ^ 2) (h b)
    simp only [p09L2, mul_pow] at hb
    rw [Real.sq_sqrt (Finset.sum_nonneg fun _ _ => sq_nonneg _),
      Real.sq_sqrt (Finset.sum_nonneg fun _ _ => sq_nonneg _)] at hb
    exact hb
  have hsum : (∑ z : B × J, ‖e z‖ ^ 2) =
      a ^ 2 * (∑ z : B × J, ‖x z‖ ^ 2) := by
    rw [Fintype.sum_prod_type, Fintype.sum_prod_type]
    calc
      (∑ b : B, ∑ j : J, ‖e (b, j)‖ ^ 2) =
          ∑ b : B, a ^ 2 * (∑ j : J, ‖x (b, j)‖ ^ 2) :=
        Finset.sum_congr rfl fun b _ => hs b
      _ = _ := by rw [Finset.mul_sum]
  rw [p09L2, p09L2, hsum, Real.sqrt_mul (sq_nonneg a), Real.sqrt_sq ha]

lemma p09_coordinateTransform_norm {m : ℕ}
    (axis : Fin m → P09FftAxis) (i : Fin m) (x : P09MultiArray axis) :
    p09MultiNorm2 (p09CoordinateTransform axis i x) =
      Real.sqrt ((axis i).order : ℝ) * p09MultiNorm2 x := by
  letI : NeZero (axis i).order := ⟨Nat.ne_of_gt (axis i).order_pos⟩
  let E := p09FiberEquiv axis i
  let input : P09FiberIndex axis i × ZMod (axis i).order → ℂ := fun bj =>
    x (E bj)
  let output : P09FiberIndex axis i × ZMod (axis i).order → ℂ := fun bk =>
    p09CoordinateTransform axis i x (E bk)
  have hs (b : P09FiberIndex axis i) :
      p09L2 (fun k => output (b, k)) =
        Real.sqrt ((axis i).order : ℝ) * p09L2 (fun j => input (b, j)) := by
    have hf := p09_fourier_norm_scaling (axis i).plan
      (fun j => x (Function.update b.1 i j))
    rw [p09ComplexNorm2_eq_l2, p09ComplexNorm2_eq_l2] at hf
    have hin : (fun j : ZMod (axis i).order =>
        x (Function.update b.1 i j)) = fun j => input (b, j) := by
      funext j
      simp [input, E, p09FiberEquiv]
    have hout : p09FourierTransform
          (fun j : ZMod (axis i).order => x (Function.update b.1 i j)) =
        fun k => output (b, k) := by
      funext k
      simp [output, E, p09FiberEquiv, p09CoordinateTransform,
        p09FourierTransform, Function.update_idem]
    rwa [hout, hin] at hf
  have hg := p09L2_fiber_scale (Real.sqrt ((axis i).order : ℝ))
    (Real.sqrt_nonneg _) output input hs
  rw [p09MultiNorm2_eq_l2, p09MultiNorm2_eq_l2]
  rw [← p09L2_equiv E, ← p09L2_equiv E]
  exact hg

lemma p09MultiNorm2_triangle {m : ℕ} {axis : Fin m → P09FftAxis}
    (x y z : P09MultiArray axis) (h : ∀ i, x i = y i + z i) :
    p09MultiNorm2 x ≤ p09MultiNorm2 y + p09MultiNorm2 z := by
  rw [p09MultiNorm2_eq_l2, p09MultiNorm2_eq_l2, p09MultiNorm2_eq_l2]
  simp only [p09L2]
  have heq : (WithLp.toLp 2 x : EuclideanSpace ℂ (P09MultiIndex axis)) =
      WithLp.toLp 2 y + WithLp.toLp 2 z := by
    ext i
    simp [h]
  simpa only [EuclideanSpace.norm_eq] using
    (show ‖(WithLp.toLp 2 x : EuclideanSpace ℂ (P09MultiIndex axis))‖ ≤
        ‖(WithLp.toLp 2 y : EuclideanSpace ℂ (P09MultiIndex axis))‖ +
          ‖(WithLp.toLp 2 z : EuclideanSpace ℂ (P09MultiIndex axis))‖ by
      rw [heq]
      exact norm_add_le _ _)

lemma p09CoordinateTransform_sub {m : ℕ} (axis : Fin m → P09FftAxis)
    (i : Fin m) (x y : P09MultiArray axis) :
    p09MultiVecSub (p09CoordinateTransform axis i x)
        (p09CoordinateTransform axis i y) =
      p09CoordinateTransform axis i (p09MultiVecSub x y) := by
  funext index
  simp only [p09MultiVecSub, p09CoordinateTransform, mul_sub,
    Finset.sum_sub_distrib]

noncomputable def p09CoordinateListScale {m : ℕ}
    (axis : Fin m → P09FftAxis) (is : List (Fin m)) : ℝ :=
  (is.map (fun i => Real.sqrt ((axis i).order : ℝ))).prod

noncomputable def p09CoordinateListFirstCoeff {m : ℕ}
    (axis : Fin m → P09FftAxis) (g : ℝ) (is : List (Fin m)) : ℝ :=
  (is.map (fun i => p09AxisK (axis i) g)).sum

noncomputable def p09CoordinateListSecondCoeff {m : ℕ}
    (axis : Fin m → P09FftAxis) (g : ℝ) : List (Fin m) → ℝ
  | [] => 0
  | i :: is =>
      let Ai := p09AxisK (axis i) g
      let Bi := p09FftSecondCoeff (axis i).plan g
      let Ap := p09CoordinateListFirstCoeff axis g is
      let Bp := p09CoordinateListSecondCoeff axis g is
      Bi + Bp + (Ai + Bi) * (Ap + Bp)

lemma p09_coordinateList_exact_norm {m : ℕ}
    (axis : Fin m → P09FftAxis) (is : List (Fin m))
    (x : P09MultiArray axis) :
    p09MultiNorm2 (is.foldr (fun i state =>
        p09CoordinateTransform axis i state) x) =
      p09CoordinateListScale axis is * p09MultiNorm2 x := by
  induction is with
  | nil => simp [p09CoordinateListScale]
  | cons i is ih =>
      simp only [List.foldr_cons]
      rw [p09_coordinateTransform_norm, ih]
      simp [p09CoordinateListScale]
      ring

lemma p09_roundedCoordinateTransform_error {m : ℕ}
    (axis : Fin m → P09FftAxis) (i : Fin m)
    (model : P09WilkinsonModel) (he : model.epsilon ≤ 1)
    (x : P09MultiArray axis) :
    0 ≤ p09FftSecondCoeff (axis i).plan model.gamma ∧
      p09MultiNorm2 (fun index =>
        p09RoundedCoordinateTransform axis i model x index -
          p09CoordinateTransform axis i x index) ≤
      Real.sqrt ((axis i).order : ℝ) *
        (model.epsilon * p09AxisK (axis i) model.gamma +
          p09FftSecondCoeff (axis i).plan model.gamma * model.epsilon ^ 2) *
            p09MultiNorm2 x := by
  letI : NeZero (axis i).order := ⟨Nat.ne_of_gt (axis i).order_pos⟩
  let E := p09FiberEquiv axis i
  let input : P09FiberIndex axis i × ZMod (axis i).order → ℂ := fun bj =>
    x (E bj)
  let err : P09FiberIndex axis i × ZMod (axis i).order → ℂ := fun bk =>
    p09RoundedCoordinateTransform axis i model x (E bk) -
      p09CoordinateTransform axis i x (E bk)
  let B : ℝ := p09FftSecondCoeff (axis i).plan model.gamma
  have hB : 0 ≤ B := (p09_roundedFftApply_error (axis i).plan model he
    (fun _ => 0)).1
  constructor
  · exact hB
  have hslice (b : P09FiberIndex axis i) :
      p09L2 (fun k => err (b, k)) ≤
        Real.sqrt ((axis i).order : ℝ) *
          (model.epsilon * p09AxisK (axis i) model.gamma +
            B * model.epsilon ^ 2) *
              p09L2 (fun j => input (b, j)) := by
    have hb := (p09_roundedFftApply_error (axis i).plan model he
        (fun j => x (Function.update b.1 i j))).2
    have hin : (fun j : ZMod (axis i).order =>
        x (Function.update b.1 i j)) = fun j => input (b, j) := by
      funext j
      simp [input, E, p09FiberEquiv]
    have hout : (fun k : ZMod (axis i).order =>
        p09RoundedFftApply (axis i).plan model
            (fun j => x (Function.update b.1 i j)) k -
          p09FourierTransform (fun j => x (Function.update b.1 i j)) k) =
        fun k => err (b, k) := by
      funext k
      simp [err, E, p09FiberEquiv, p09RoundedCoordinateTransform,
        p09CoordinateTransform, p09FourierTransform, Function.update_idem]
    have hbL : p09L2 (fun k : ZMod (axis i).order =>
        p09RoundedFftApply (axis i).plan model
            (fun j => x (Function.update b.1 i j)) k -
          p09FourierTransform (fun j => x (Function.update b.1 i j)) k) ≤
        Real.sqrt ((axis i).order : ℝ) *
          (model.epsilon * p09K (axis i).plan model.gamma +
            B * model.epsilon ^ 2) *
          p09L2 (fun j => x (Function.update b.1 i j)) := by
      simpa only [p09ComplexNorm2_eq_l2, B, p09FftSecondCoeff] using hb
    have houtNorm := congrArg p09L2 hout
    have hinNorm := congrArg p09L2 hin
    rw [houtNorm, hinNorm] at hbL
    simpa only [p09AxisK] using hbL
  have hglobal := p09L2_fiber_bound
    (Real.sqrt ((axis i).order : ℝ) *
      (model.epsilon * p09AxisK (axis i) model.gamma + B * model.epsilon ^ 2))
    (by
      have haxisK : 0 ≤ p09AxisK (axis i) model.gamma := by
        rw [p09AxisK, p09K]
        have hstage : 0 ≤ ∑ s : Fin (axis i).plan.stageCount,
            p09Alpha ((axis i).plan.stage s).radix model.gamma :=
          Finset.sum_nonneg fun s _ => p09Alpha_nonneg _
            ((axis i).plan.stage s).radix_two_le _ model.gamma_nonneg
        have hc : 0 ≤ ((axis i).plan.stageCount : ℝ) - 1 := by
          apply sub_nonneg.mpr
          exact_mod_cast (Nat.one_le_iff_ne_zero.mpr
            (Nat.ne_of_gt (axis i).plan.stageCount_pos))
        exact add_nonneg hstage (mul_nonneg hc (by nlinarith [model.gamma_nonneg]))
      exact mul_nonneg (Real.sqrt_nonneg _)
        (add_nonneg (mul_nonneg (le_of_lt model.epsilon_pos) haxisK)
          (mul_nonneg hB (sq_nonneg model.epsilon))))
    err input hslice
  rw [p09MultiNorm2_eq_l2, p09MultiNorm2_eq_l2]
  rw [← p09L2_equiv E, ← p09L2_equiv E]
  exact hglobal

lemma p09_roundedCoordinateList_error {m : ℕ}
    (axis : Fin m → P09FftAxis) (g : ℝ) (hg : 0 ≤ g)
    (model : P09WilkinsonModel) (hgamma : model.gamma = g)
    (he : model.epsilon ≤ 1) (is : List (Fin m))
    (x : P09MultiArray axis) :
    0 ≤ p09CoordinateListSecondCoeff axis g is ∧
    p09MultiNorm2 (fun index =>
      (is.foldr (fun i state =>
        p09RoundedCoordinateTransform axis i model state) x) index -
      (is.foldr (fun i state => p09CoordinateTransform axis i state) x) index) ≤
      p09CoordinateListScale axis is *
        (model.epsilon * p09CoordinateListFirstCoeff axis g is +
          p09CoordinateListSecondCoeff axis g is * model.epsilon ^ 2) *
        p09MultiNorm2 x := by
  induction is with
  | nil =>
      constructor
      · simp [p09CoordinateListSecondCoeff]
      · have hz : (fun index => x index - x index) = (0 : P09MultiArray axis) := by
          funext index
          simp
        simp only [List.foldr]
        rw [hz]
        simp [p09MultiNorm2, p09CoordinateListScale,
          p09CoordinateListFirstCoeff, p09CoordinateListSecondCoeff]
  | cons i is ih =>
      let rr := is.foldr (fun j state =>
        p09RoundedCoordinateTransform axis j model state) x
      let re := is.foldr (fun j state => p09CoordinateTransform axis j state) x
      let d : P09MultiArray axis := fun index => rr index - re index
      let Ai := p09AxisK (axis i) g
      let Bi := p09FftSecondCoeff (axis i).plan g
      let Ap := p09CoordinateListFirstCoeff axis g is
      let Bp := p09CoordinateListSecondCoeff axis g is
      have hprev := ih
      have hBp : 0 ≤ Bp := by simpa [Bp] using hprev.1
      have hd : p09MultiNorm2 d ≤
          p09CoordinateListScale axis is *
            (model.epsilon * Ap + Bp * model.epsilon ^ 2) *
              p09MultiNorm2 x := by
        simpa [d, rr, re, Ap, Bp] using hprev.2
      have hre : p09MultiNorm2 re =
          p09CoordinateListScale axis is * p09MultiNorm2 x := by
        simpa [re] using p09_coordinateList_exact_norm axis is x
      have hrr : p09MultiNorm2 rr ≤ p09MultiNorm2 re + p09MultiNorm2 d := by
        apply p09MultiNorm2_triangle rr re d
        intro index
        simp [d]
      have hlocal0 := p09_roundedCoordinateTransform_error axis i model he rr
      have hBi : 0 ≤ Bi := by
        simpa [Bi, hgamma] using hlocal0.1
      have hlocal : p09MultiNorm2 (fun index =>
          p09RoundedCoordinateTransform axis i model rr index -
            p09CoordinateTransform axis i rr index) ≤
          Real.sqrt ((axis i).order : ℝ) *
            (model.epsilon * Ai + Bi * model.epsilon ^ 2) *
              p09MultiNorm2 rr := by
        simpa [Ai, Bi, hgamma] using hlocal0.2
      have hAi : 0 ≤ Ai := by
        dsimp [Ai, p09AxisK, p09K]
        have hs : 0 ≤ ∑ s : Fin (axis i).plan.stageCount,
            p09Alpha ((axis i).plan.stage s).radix g :=
          Finset.sum_nonneg fun s _ => p09Alpha_nonneg _
            ((axis i).plan.stage s).radix_two_le _ hg
        have hc : 0 ≤ ((axis i).plan.stageCount : ℝ) - 1 := by
          apply sub_nonneg.mpr
          exact_mod_cast (Nat.one_le_iff_ne_zero.mpr
            (Nat.ne_of_gt (axis i).plan.stageCount_pos))
        exact add_nonneg hs (mul_nonneg hc (by nlinarith))
      let loc : P09MultiArray axis := fun index =>
        p09RoundedCoordinateTransform axis i model rr index -
          p09CoordinateTransform axis i rr index
      let prop : P09MultiArray axis := p09CoordinateTransform axis i d
      have hprop : p09MultiNorm2 prop =
          Real.sqrt ((axis i).order : ℝ) * p09MultiNorm2 d := by
        simpa [prop] using p09_coordinateTransform_norm axis i d
      have hsplit : ∀ index,
          p09RoundedCoordinateTransform axis i model rr index -
              p09CoordinateTransform axis i re index = loc index + prop index := by
        intro index
        have hlin := congrFun (p09CoordinateTransform_sub axis i rr re) index
        simp only [p09MultiVecSub] at hlin
        dsimp [loc, prop]
        change p09RoundedCoordinateTransform axis i model rr index -
            p09CoordinateTransform axis i re index =
          (p09RoundedCoordinateTransform axis i model rr index -
            p09CoordinateTransform axis i rr index) +
          p09CoordinateTransform axis i (p09MultiVecSub rr re) index
        rw [← hlin]
        ring
      have htri := p09MultiNorm2_triangle _ loc prop hsplit
      have he0 : 0 ≤ model.epsilon := le_of_lt model.epsilon_pos
      have he2 : model.epsilon ^ 2 ≤ model.epsilon := by
        nlinarith [sq_nonneg model.epsilon]
      have hibound : model.epsilon * Ai + Bi * model.epsilon ^ 2 ≤
          model.epsilon * (Ai + Bi) := by
        nlinarith [mul_le_mul_of_nonneg_left he2 hBi]
      have hAp : 0 ≤ Ap := by
        dsimp [Ap, p09CoordinateListFirstCoeff]
        apply List.sum_nonneg
        intro a ha
        simp only [List.mem_map] at ha
        rcases ha with ⟨j, hj, rfl⟩
        dsimp [p09AxisK, p09K]
        have hs : 0 ≤ ∑ s : Fin (axis j).plan.stageCount,
            p09Alpha ((axis j).plan.stage s).radix g :=
          Finset.sum_nonneg fun s _ => p09Alpha_nonneg _
            ((axis j).plan.stage s).radix_two_le _ hg
        have hc : 0 ≤ ((axis j).plan.stageCount : ℝ) - 1 := by
          apply sub_nonneg.mpr
          exact_mod_cast (Nat.one_le_iff_ne_zero.mpr
            (Nat.ne_of_gt (axis j).plan.stageCount_pos))
        exact add_nonneg hs (mul_nonneg hc (by nlinarith))
      have hpbound : model.epsilon * Ap + Bp * model.epsilon ^ 2 ≤
          model.epsilon * (Ap + Bp) := by
        nlinarith [mul_le_mul_of_nonneg_left he2 hBp]
      have hscale0 : 0 ≤ Real.sqrt ((axis i).order : ℝ) := Real.sqrt_nonneg _
      have hpre0 : 0 ≤ p09CoordinateListScale axis is := by
        dsimp [p09CoordinateListScale]
        apply List.prod_nonneg
        intro a ha
        simp only [List.mem_map] at ha
        rcases ha with ⟨j, hj, rfl⟩
        exact Real.sqrt_nonneg _
      have hBnew : 0 ≤ Bi + Bp + (Ai + Bi) * (Ap + Bp) := by
        positivity
      constructor
      · simpa [p09CoordinateListSecondCoeff, Ai, Bi, Ap, Bp] using hBnew
      · simp only [List.foldr_cons]
        have hloc : p09MultiNorm2 loc ≤
            Real.sqrt ((axis i).order : ℝ) *
              (model.epsilon * Ai + Bi * model.epsilon ^ 2) *
                p09MultiNorm2 rr := by simpa [loc] using hlocal
        calc
          p09MultiNorm2 (fun index =>
              p09RoundedCoordinateTransform axis i model rr index -
                p09CoordinateTransform axis i re index) ≤
              p09MultiNorm2 loc + p09MultiNorm2 prop := htri
          _ ≤ Real.sqrt ((axis i).order : ℝ) *
                (model.epsilon * Ai + Bi * model.epsilon ^ 2) *
                  p09MultiNorm2 rr +
              Real.sqrt ((axis i).order : ℝ) * p09MultiNorm2 d := by
            rw [hprop]
            exact add_le_add_left hloc _
          _ ≤ Real.sqrt ((axis i).order : ℝ) *
                (model.epsilon * Ai + Bi * model.epsilon ^ 2) *
                  (p09MultiNorm2 re + p09MultiNorm2 d) +
              Real.sqrt ((axis i).order : ℝ) * p09MultiNorm2 d := by
            exact add_le_add_left (mul_le_mul_of_nonneg_left hrr
              (mul_nonneg hscale0 (add_nonneg (mul_nonneg he0 hAi)
                (mul_nonneg hBi (sq_nonneg model.epsilon))))) _
          _ ≤ Real.sqrt ((axis i).order : ℝ) *
                (model.epsilon * Ai + Bi * model.epsilon ^ 2) *
                  (p09CoordinateListScale axis is * p09MultiNorm2 x +
                    p09CoordinateListScale axis is *
                      (model.epsilon * Ap + Bp * model.epsilon ^ 2) *
                        p09MultiNorm2 x) +
              Real.sqrt ((axis i).order : ℝ) *
                (p09CoordinateListScale axis is *
                  (model.epsilon * Ap + Bp * model.epsilon ^ 2) *
                    p09MultiNorm2 x) := by
            rw [hre]
            have hc : 0 ≤ Real.sqrt ((axis i).order : ℝ) *
                (model.epsilon * Ai + Bi * model.epsilon ^ 2) := by positivity
            exact add_le_add
              (mul_le_mul_of_nonneg_left (add_le_add_right hd _) hc)
              (mul_le_mul_of_nonneg_left hd hscale0)
          _ ≤ p09CoordinateListScale axis (i :: is) *
                (model.epsilon * p09CoordinateListFirstCoeff axis g (i :: is) +
                  p09CoordinateListSecondCoeff axis g (i :: is) *
                    model.epsilon ^ 2) * p09MultiNorm2 x := by
            have hleft : 0 ≤ model.epsilon * Ap + Bp * model.epsilon ^ 2 := by
              positivity
            have hcross := mul_le_mul hibound hpbound hleft
              (mul_nonneg he0 (add_nonneg hAi hBi))
            have hcoef :
                (model.epsilon * Ai + Bi * model.epsilon ^ 2) *
                    (1 + (model.epsilon * Ap + Bp * model.epsilon ^ 2)) +
                  (model.epsilon * Ap + Bp * model.epsilon ^ 2) ≤
                model.epsilon * (Ai + Ap) +
                  (Bi + Bp + (Ai + Bi) * (Ap + Bp)) * model.epsilon ^ 2 := by
              nlinarith
            have hQ : 0 ≤ Real.sqrt ((axis i).order : ℝ) *
                p09CoordinateListScale axis is * p09MultiNorm2 x :=
              mul_nonneg (mul_nonneg hscale0 hpre0) (by
                rw [p09MultiNorm2_eq_l2]
                exact Real.sqrt_nonneg _)
            have hmul := mul_le_mul_of_nonneg_left hcoef hQ
            convert hmul using 1 <;>
              simp [p09CoordinateListScale, p09CoordinateListFirstCoeff,
                p09CoordinateListSecondCoeff, Ai, Bi, Ap, Bp] <;> ring

lemma p09_fin_state_foldr {m : ℕ} {X : Type*}
    (f : Fin m → X → X) (state : Fin (m + 1) → X)
    (hstep : ∀ i : Fin m, state i.castSucc = f i (state i.succ)) :
    state 0 = (List.ofFn fun i : Fin m => i).foldr f (state (Fin.last m)) := by
  induction m with
  | zero => simp
  | succ m ih =>
      rw [List.ofFn_succ]
      simp only [List.foldr_cons]
      have hs0 := hstep (0 : Fin (m + 1))
      change state 0 = f 0 (state (Fin.succ 0)) at hs0
      rw [hs0]
      apply congrArg (f 0)
      let f' : Fin m → X → X := fun i => f i.succ
      let state' : Fin (m + 1) → X := fun i => state i.succ
      have hs' : ∀ i : Fin m, state' i.castSucc = f' i (state' i.succ) := by
        intro i
        simpa [state', f'] using hstep i.succ
      have hh := ih f' state' hs'
      change state 1 = List.foldr f (state (Fin.last (m + 1)))
        (List.ofFn fun i : Fin m => i.succ)
      calc
        state 1 = List.foldr f' (state (Fin.last (m + 1)))
            (List.ofFn fun i : Fin m => i) := by simpa [state'] using hh
        _ = List.foldr f (state (Fin.last (m + 1)))
            (List.ofFn fun i : Fin m => i.succ) := by
          rw [← List.foldr_map, List.map_ofFn]
          rfl

lemma p09_coordinatePrefix_eq_foldr {m : ℕ}
    (axis : Fin m → P09FftAxis) (k : ℕ) (hk : k ≤ m)
    (x : P09MultiArray axis) :
    p09ApplyCoordinatePrefix axis k x =
      (List.ofFn fun i : Fin k => Fin.castLE hk i).foldr
        (fun i state => p09CoordinateTransform axis i state) x := by
  induction k generalizing x with
  | zero => simp [p09ApplyCoordinatePrefix]
  | succ k ih =>
      have hk' : k ≤ m := Nat.le_trans (Nat.le_succ k) hk
      rw [List.ofFn_succ_last, List.foldr_append]
      simp only [List.foldr_cons, List.foldr_nil]
      rw [show p09ApplyCoordinatePrefix axis (k + 1) x =
          p09ApplyCoordinatePrefix axis k
            (p09CoordinateTransform axis (Fin.castLE hk (Fin.last k)) x) by
        rw [p09ApplyCoordinatePrefix]
        simp only [p09CoordinateTransformNat]
        rw [dif_pos (lt_of_lt_of_le (Nat.lt_succ_self k) hk)]
        congr 2]
      rw [ih hk' (p09CoordinateTransform axis (Fin.castLE hk (Fin.last k)) x)]
      congr 1

lemma p09CoordinateListFirstCoeff_all {m : ℕ}
    (axis : Fin m → P09FftAxis) (g : ℝ) :
    p09CoordinateListFirstCoeff axis g (List.ofFn fun i : Fin m => i) =
      ∑ i : Fin m, p09AxisK (axis i) g := by
  simp [p09CoordinateListFirstCoeff, List.map_ofFn, List.sum_ofFn]

lemma p09MultiCardinality_pos {m : ℕ} (axis : Fin m → P09FftAxis) :
    0 < p09MultiCardinality axis := by
  rw [p09MultiCardinality]
  exact Finset.prod_pos fun i _ => (axis i).order_pos

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
  let indices : List (Fin m) := List.ofFn fun i : Fin m => i
  let B := p09CoordinateListSecondCoeff plan.axis γ indices
  let one : P09PositiveEpsilon := ⟨1, zero_lt_one⟩
  have hBone := p09_roundedCoordinateList_error plan.axis γ family.gamma_nonneg
    (family.model one) (family.model_gamma one) (by
      rw [family.model_epsilon]) indices family.input
  have hB : 0 ≤ B := by simpa [B] using hBone.1
  refine ⟨B, hB, 1, zero_lt_one, ?_⟩
  intro ε hε
  let model := family.model ε
  let run := family.run ε
  have he : model.epsilon ≤ 1 := by
    rw [show model.epsilon = ε.1 by simpa [model] using family.model_epsilon ε]
    exact hε
  have hlist := p09_roundedCoordinateList_error plan.axis γ family.gamma_nonneg
    model (by simpa [model] using family.model_gamma ε) he indices family.input
  have hround : run.computedState 0 =
      indices.foldr (fun i state =>
        p09RoundedCoordinateTransform plan.axis i model state) family.input := by
    have hr := p09_fin_state_foldr
      (fun i state => p09RoundedCoordinateTransform plan.axis i model state)
      run.computedState run.stage_step
    rw [run.computed_input, family.run_input ε] at hr
    simpa [indices, run, model] using hr
  have hexact : p09FamilyMultiExactOutput family =
      indices.foldr (fun i state =>
        p09CoordinateTransform plan.axis i state) family.input := by
    unfold p09FamilyMultiExactOutput
    have hp := p09_coordinatePrefix_eq_foldr plan.axis m le_rfl family.input
    simpa [indices] using hp
  have hnorm0 :
      p09MultiNorm2 (p09FamilyMultiFftRoundoffError family ε) ≤
        p09CoordinateListScale plan.axis indices *
          (model.epsilon * p09CoordinateListFirstCoeff plan.axis γ indices +
            B * model.epsilon ^ 2) * p09MultiNorm2 family.input := by
    have hb := hlist.2
    rw [← hround, ← hexact] at hb
    simpa [p09FamilyMultiFftRoundoffError, p09MultiFftRoundoffError,
      p09MultiComputedOutput, run, model, B] using hb
  have hexactNorm : p09MultiNorm2 (p09FamilyMultiExactOutput family) =
      p09CoordinateListScale plan.axis indices * p09MultiNorm2 family.input := by
    rw [hexact]
    exact p09_coordinateList_exact_norm plan.axis indices family.input
  let coeff : ℝ := ε.1 * (∑ i : Fin m, p09AxisK (plan.axis i) γ) +
    B * ε.1 ^ 2
  have hnorm :
      p09MultiNorm2 (p09FamilyMultiFftRoundoffError family ε) ≤
        coeff * p09MultiNorm2 (p09FamilyMultiExactOutput family) := by
    calc
      p09MultiNorm2 (p09FamilyMultiFftRoundoffError family ε) ≤
          p09CoordinateListScale plan.axis indices *
            (model.epsilon * p09CoordinateListFirstCoeff plan.axis γ indices +
              B * model.epsilon ^ 2) * p09MultiNorm2 family.input := hnorm0
      _ = coeff * p09MultiNorm2 (p09FamilyMultiExactOutput family) := by
        rw [hexactNorm]
        simp only [coeff]
        rw [show model.epsilon = ε.1 by
          simpa [model] using family.model_epsilon ε]
        rw [show p09CoordinateListFirstCoeff plan.axis γ indices =
            ∑ i : Fin m, p09AxisK (plan.axis i) γ by
          simpa [indices] using p09CoordinateListFirstCoeff_all plan.axis γ]
        ring
  have hcardNat : 0 < p09MultiCardinality plan.axis :=
    p09MultiCardinality_pos plan.axis
  have hcard : 0 < Real.sqrt (p09MultiCardinality plan.axis : ℝ) :=
    Real.sqrt_pos.2 (by exact_mod_cast hcardNat)
  have hrms : p09MultiRms (p09FamilyMultiFftRoundoffError family ε) ≤
      coeff * p09MultiRms (p09FamilyMultiExactOutput family) := by
    unfold p09MultiRms
    rw [div_le_iff₀ hcard]
    calc
      p09MultiNorm2 (p09FamilyMultiFftRoundoffError family ε) ≤
          coeff * p09MultiNorm2 (p09FamilyMultiExactOutput family) := hnorm
      _ = coeff *
          (p09MultiNorm2 (p09FamilyMultiExactOutput family) /
            Real.sqrt (p09MultiCardinality plan.axis : ℝ)) *
          Real.sqrt (p09MultiCardinality plan.axis : ℝ) := by
        field_simp
  rw [div_le_iff₀ hexactOutput]
  simpa [coeff] using hrms

end HighamBench
