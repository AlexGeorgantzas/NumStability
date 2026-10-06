import HighamBench.P05Definitions

namespace HighamBench

lemma p05_test_algebra
    (a b u X S q : ℝ)
    (ha : 1 ≤ a) (hb : 1 ≤ b)
    (hu : 0 ≤ u) (hu2 : u ≤ 1 / 2)
    (hX : 0 ≤ X) (hS : 0 ≤ S)
    (hq1 : q ≤ u * (1 + a * u) * X)
    (hq2 : q ≤ (1 + b * u) * S) :
    q ≤ b * u * X + a * u * S := by
  have ha0 : 0 ≤ a := le_trans (by norm_num) ha
  have hb0 : 0 ≤ b := le_trans (by norm_num) hb
  have hu1 : u ≤ 1 := le_trans hu2 (by norm_num)
  have hcore :
      (1 + a * u) * (1 + (b - a) * u) ≤ b * (1 + b * u) := by
    by_cases hab : a ≤ b
    · have hp : 0 ≤ b * (b - 1) - a * (b - a) := by
        nlinarith [sq_nonneg (b - a),
          mul_nonneg hb0 (sub_nonneg.mpr ha)]
      have huu : 0 ≤ u * (1 - u) :=
        mul_nonneg hu (sub_nonneg.mpr hu1)
      have hbu : 0 ≤ 1 + b * u - b * u ^ 2 := by
        nlinarith [mul_nonneg hb0 huu]
      have h₁ := mul_nonneg hp (sq_nonneg u)
      have h₂ := mul_nonneg (sub_nonneg.mpr hb) hbu
      nlinarith
    · have hba : b ≤ a := le_of_not_ge hab
      have hpos : 0 ≤ 1 + b * u := by positivity
      have h₁ := mul_nonneg (sub_nonneg.mpr hb) hpos
      have h₂ := mul_nonneg
        (mul_nonneg ha0 (sub_nonneg.mpr hba)) (sq_nonneg u)
      nlinarith
  by_cases hu0 : u = 0
  · subst u
    norm_num at hq1 ⊢
    exact hq1
  have hu_pos : 0 < u := lt_of_le_of_ne hu (Ne.symm hu0)
  let A := u * (1 + a * u)
  let B := 1 + b * u
  let C := b * u
  let D := a * u
  have hA : 0 < A := by dsimp [A]; positivity
  have hB : 0 < B := by dsimp [B]; positivity
  have hC : 0 ≤ C := by dsimp [C]; positivity
  have hD : 0 ≤ D := by dsimp [D]; positivity
  have hcoef : A * (B - D) ≤ C * B := by
    dsimp [A, B, C, D]
    have := mul_le_mul_of_nonneg_left hcore hu
    nlinarith
  have hqA : q ≤ A * X := by simpa [A] using hq1
  have hqB : q ≤ B * S := by simpa [B] using hq2
  have hresult : q ≤ C * X + D * S := by
    by_cases hmin : A * X ≤ B * S
    · have hcoef' : B * (A - C) ≤ D * A := by nlinarith [hcoef]
      have hm₁ := mul_le_mul_of_nonneg_right hcoef' hX
      have hm₂ := mul_le_mul_of_nonneg_left hmin hD
      have hcancel : (A - C) * X ≤ D * S := by
        have hc : B * ((A - C) * X) ≤ B * (D * S) := calc
          B * ((A - C) * X) = (B * (A - C)) * X := by ring
          _ ≤ (D * A) * X := hm₁
          _ ≤ D * (B * S) := by nlinarith [hm₂]
          _ = B * (D * S) := by ring
        exact le_of_mul_le_mul_left hc hB
      nlinarith
    · have hmin' : B * S ≤ A * X := le_of_not_ge hmin
      have hm₁ := mul_le_mul_of_nonneg_right hcoef hS
      have hm₂ := mul_le_mul_of_nonneg_left hmin' hC
      have hcancel : (B - D) * S ≤ C * X := by
        have hc : A * ((B - D) * S) ≤ A * (C * X) := calc
          A * ((B - D) * S) = (A * (B - D)) * S := by ring
          _ ≤ (C * B) * S := hm₁
          _ ≤ C * (A * X) := by nlinarith [hm₂]
          _ = A * (C * X) := by ring
        exact le_of_mul_le_mul_left hc hA
      nlinarith
  simpa [C, D] using hresult

lemma p05_protected_sum_trace_bound
    {fmt : P05FiniteRoundToNearestFormat}
    {termCount : ℕ} {pivotValue outsideExact outsideAbs computed : ℝ}
    (trace : P05ProtectedSumTrace fmt termCount pivotValue
      outsideExact outsideAbs computed) :
    0 < termCount ∧
    fmt.representable computed ∧
    0 ≤ outsideAbs ∧
    |outsideExact| ≤ outsideAbs ∧
    |computed - (pivotValue + outsideExact)| ≤
      ((termCount - 1 : ℕ) : ℝ) * fmt.unitRoundoff *
        (outsideAbs + |computed|) := by
  induction trace with
  | leaf pivotValue pivot_representable =>
      constructor
      · norm_num
      constructor
      · exact pivot_representable
      constructor
      · norm_num
      constructor
      · norm_num
      · simp [mul_nonneg fmt.unitRoundoff_nonneg (abs_nonneg pivotValue)]
  | @merge outerCount siblingCount pivotValue siblingExact siblingAbs
      siblingComputed outerExact outerAbs computed pivot_representable
      sibling_count_pos sibling_abs_nonneg sibling_exact_abs_le
      sibling_computed_representable sibling_error_bound merge_safe outer ih =>
      rcases ih with
        ⟨outer_count_pos, computed_representable, outer_abs_nonneg,
          outer_exact_abs_le, outer_error_bound⟩
      have hu : 0 ≤ fmt.unitRoundoff := fmt.unitRoundoff_nonneg
      have hu2 : fmt.unitRoundoff ≤ 1 / 2 := fmt.unitRoundoff_le_half
      have hs_count : (1 : ℝ) ≤ siblingCount := by
        exact_mod_cast sibling_count_pos
      have ho_count : (1 : ℝ) ≤ outerCount := by
        exact_mod_cast outer_count_pos
      have hround_output :
          |fmt.round (pivotValue + siblingComputed) -
              (pivotValue + siblingComputed)| ≤
            fmt.unitRoundoff *
              |fmt.round (pivotValue + siblingComputed)| :=
        fmt.round_error_to_output _ merge_safe
      have hround_nearest :
          |(pivotValue + siblingComputed) -
              fmt.round (pivotValue + siblingComputed)| ≤
            |siblingComputed| := by
        have h := fmt.round_nearest _ merge_safe pivotValue pivot_representable
        simpa using h
      have hs_computed :
          |siblingComputed| ≤
            (1 + (siblingCount : ℝ) * fmt.unitRoundoff) * siblingAbs := by
        calc
          |siblingComputed| =
              |(siblingComputed - siblingExact) + siblingExact| := by ring_nf
          _ ≤ |siblingComputed - siblingExact| + |siblingExact| := abs_add_le _ _
          _ ≤ (siblingCount : ℝ) * fmt.unitRoundoff * siblingAbs +
                siblingAbs := add_le_add sibling_error_bound sibling_exact_abs_le
          _ = (1 + (siblingCount : ℝ) * fmt.unitRoundoff) *
                siblingAbs := by ring
      have hrounded :
          |fmt.round (pivotValue + siblingComputed)| ≤
            (1 + ((outerCount - 1 : ℕ) : ℝ) * fmt.unitRoundoff) *
              (outerAbs + |computed|) := by
        calc
          |fmt.round (pivotValue + siblingComputed)| =
              |(fmt.round (pivotValue + siblingComputed) + outerExact - computed) +
                  (computed - outerExact)| := by
                    congr 1
                    ring
          _ ≤ |fmt.round (pivotValue + siblingComputed) + outerExact - computed| +
                |computed - outerExact| := abs_add_le _ _
          _ = |computed -
                  (fmt.round (pivotValue + siblingComputed) + outerExact)| +
                |computed - outerExact| := by rw [abs_sub_comm]
          _ ≤ |computed -
                  (fmt.round (pivotValue + siblingComputed) + outerExact)| +
                (|computed| + |outerExact|) :=
            add_le_add_right (abs_sub _ _) _
          _ ≤ ((outerCount - 1 : ℕ) : ℝ) * fmt.unitRoundoff *
                  (outerAbs + |computed|) +
                (|computed| + outerAbs) := by
            exact add_le_add outer_error_bound
              (add_le_add_right outer_exact_abs_le _)
          _ = (1 + ((outerCount - 1 : ℕ) : ℝ) * fmt.unitRoundoff) *
                (outerAbs + |computed|) := by ring
      have hround₁ :
          |fmt.round (pivotValue + siblingComputed) -
              (pivotValue + siblingComputed)| ≤
            fmt.unitRoundoff *
              (1 + ((outerCount - 1 : ℕ) : ℝ) * fmt.unitRoundoff) *
                (outerAbs + |computed|) := by
        calc
          _ ≤ fmt.unitRoundoff *
              |fmt.round (pivotValue + siblingComputed)| := hround_output
          _ ≤ fmt.unitRoundoff *
              ((1 + ((outerCount - 1 : ℕ) : ℝ) * fmt.unitRoundoff) *
                (outerAbs + |computed|)) :=
            mul_le_mul_of_nonneg_left hrounded hu
          _ = _ := by ring
      have hround₂ :
          |fmt.round (pivotValue + siblingComputed) -
              (pivotValue + siblingComputed)| ≤
            (1 + (siblingCount : ℝ) * fmt.unitRoundoff) *
              siblingAbs := by
        rw [abs_sub_comm]
        exact le_trans hround_nearest hs_computed
      have hround :
          |fmt.round (pivotValue + siblingComputed) -
              (pivotValue + siblingComputed)| ≤
            (siblingCount : ℝ) * fmt.unitRoundoff *
                (outerAbs + |computed|) +
              ((outerCount - 1 : ℕ) : ℝ) * fmt.unitRoundoff * siblingAbs := by
        by_cases hoc : outerCount = 1
        · subst outerCount
          norm_num at hround₁ ⊢
          nlinarith [mul_nonneg hu
            (add_nonneg outer_abs_nonneg (abs_nonneg computed))]
        · have hoc_nat : 1 ≤ outerCount - 1 := by omega
          have hoc_real : (1 : ℝ) ≤ (outerCount - 1 : ℕ) := by
            exact_mod_cast hoc_nat
          exact p05_test_algebra
            ((outerCount - 1 : ℕ) : ℝ) (siblingCount : ℝ)
            fmt.unitRoundoff (outerAbs + |computed|) siblingAbs
            |fmt.round (pivotValue + siblingComputed) -
              (pivotValue + siblingComputed)|
            hoc_real hs_count hu hu2
            (add_nonneg outer_abs_nonneg (abs_nonneg _))
            sibling_abs_nonneg hround₁ hround₂
      constructor
      · omega
      constructor
      · exact computed_representable
      constructor
      · exact add_nonneg sibling_abs_nonneg outer_abs_nonneg
      constructor
      · calc
          |siblingExact + outerExact| ≤
              |siblingExact| + |outerExact| := abs_add_le _ _
          _ ≤ siblingAbs + outerAbs :=
            add_le_add sibling_exact_abs_le outer_exact_abs_le
      · calc
          |computed - (pivotValue + (siblingExact + outerExact))| =
              |(computed -
                  (fmt.round (pivotValue + siblingComputed) + outerExact)) +
                (fmt.round (pivotValue + siblingComputed) -
                  (pivotValue + siblingComputed)) +
                (siblingComputed - siblingExact)| := by ring_nf
          _ ≤ |computed -
                  (fmt.round (pivotValue + siblingComputed) + outerExact)| +
                |fmt.round (pivotValue + siblingComputed) -
                  (pivotValue + siblingComputed)| +
                |siblingComputed - siblingExact| := by
            calc
              _ ≤ |(computed -
                      (fmt.round (pivotValue + siblingComputed) + outerExact)) +
                    (fmt.round (pivotValue + siblingComputed) -
                      (pivotValue + siblingComputed))| +
                    |siblingComputed - siblingExact| := abs_add_le _ _
              _ ≤ (|computed -
                      (fmt.round (pivotValue + siblingComputed) + outerExact)| +
                    |fmt.round (pivotValue + siblingComputed) -
                      (pivotValue + siblingComputed)|) +
                    |siblingComputed - siblingExact| :=
                add_le_add_left (abs_add_le _ _) _
          _ ≤ ((outerCount - 1 : ℕ) : ℝ) * fmt.unitRoundoff *
                  (outerAbs + |computed|) +
                ((siblingCount : ℝ) * fmt.unitRoundoff *
                    (outerAbs + |computed|) +
                  ((outerCount - 1 : ℕ) : ℝ) *
                    fmt.unitRoundoff * siblingAbs) +
                ((siblingCount : ℝ) * fmt.unitRoundoff * siblingAbs) := by
            gcongr
          _ = ((outerCount + siblingCount - 1 : ℕ) : ℝ) *
                fmt.unitRoundoff *
                  ((siblingAbs + outerAbs) + |computed|) := by
            have hn : outerCount + siblingCount - 1 =
                (outerCount - 1) + siblingCount := by omega
            rw [hn]
            push_cast
            ring

lemma p05_protected_sum_trace_close
    {fmt : P05FiniteRoundToNearestFormat}
    {termCount : ℕ} {pivotValue outsideExact outsideAbs computed : ℝ}
    (trace : P05ProtectedSumTrace fmt termCount pivotValue
      outsideExact outsideAbs computed)
    {tailCount : ℕ} (tail_count_pos : 0 < tailCount)
    {tailExact tailAbs : ℝ}
    (tail_abs_nonneg : 0 ≤ tailAbs)
    (tail_exact_abs_le : |tailExact| ≤ tailAbs)
    (tail_error_bound :
      |computed + tailExact| ≤
        (tailCount : ℝ) * fmt.unitRoundoff * tailAbs) :
    |pivotValue + outsideExact + tailExact| ≤
      (((termCount - 1) + tailCount : ℕ) : ℝ) *
        fmt.unitRoundoff * (outsideAbs + tailAbs) := by
  induction trace with
  | leaf pivotValue pivot_representable =>
      simpa using tail_error_bound
  | @merge outerCount siblingCount pivotValue siblingExact siblingAbs
      siblingComputed outerExact outerAbs computed pivot_representable
      sibling_count_pos sibling_abs_nonneg sibling_exact_abs_le
      sibling_computed_representable sibling_error_bound merge_safe outer ih =>
      rcases p05_protected_sum_trace_bound outer with
        ⟨outer_count_pos, computed_representable, outer_abs_nonneg,
          outer_exact_abs_le, outer_residual⟩
      have hu : 0 ≤ fmt.unitRoundoff := fmt.unitRoundoff_nonneg
      have hu2 : fmt.unitRoundoff ≤ 1 / 2 := fmt.unitRoundoff_le_half
      have hs_count : (1 : ℝ) ≤ siblingCount := by
        exact_mod_cast sibling_count_pos
      have htail_count : (1 : ℝ) ≤ tailCount := by
        exact_mod_cast tail_count_pos
      have houter := ih tail_error_bound
      have hcombined_count_nat :
          1 ≤ (outerCount - 1) + tailCount := by omega
      have hcombined_count :
          (1 : ℝ) ≤ ((outerCount - 1) + tailCount : ℕ) := by
        exact_mod_cast hcombined_count_nat
      have hround_output :
          |fmt.round (pivotValue + siblingComputed) -
              (pivotValue + siblingComputed)| ≤
            fmt.unitRoundoff *
              |fmt.round (pivotValue + siblingComputed)| :=
        fmt.round_error_to_output _ merge_safe
      have hround_nearest :
          |(pivotValue + siblingComputed) -
              fmt.round (pivotValue + siblingComputed)| ≤
            |siblingComputed| := by
        have h := fmt.round_nearest _ merge_safe pivotValue pivot_representable
        simpa using h
      have hs_computed :
          |siblingComputed| ≤
            (1 + (siblingCount : ℝ) * fmt.unitRoundoff) * siblingAbs := by
        calc
          |siblingComputed| =
              |(siblingComputed - siblingExact) + siblingExact| := by ring_nf
          _ ≤ |siblingComputed - siblingExact| + |siblingExact| := abs_add_le _ _
          _ ≤ (siblingCount : ℝ) * fmt.unitRoundoff * siblingAbs +
                siblingAbs := add_le_add sibling_error_bound sibling_exact_abs_le
          _ = (1 + (siblingCount : ℝ) * fmt.unitRoundoff) *
                siblingAbs := by ring
      have hrounded :
          |fmt.round (pivotValue + siblingComputed)| ≤
            (1 + (((outerCount - 1) + tailCount : ℕ) : ℝ) *
              fmt.unitRoundoff) * (outerAbs + tailAbs) := by
        calc
          |fmt.round (pivotValue + siblingComputed)| =
              |(fmt.round (pivotValue + siblingComputed) + outerExact +
                  tailExact) - (outerExact + tailExact)| := by
                    congr 1
                    ring
          _ ≤ |fmt.round (pivotValue + siblingComputed) + outerExact +
                  tailExact| + |outerExact + tailExact| := abs_sub _ _
          _ ≤ |fmt.round (pivotValue + siblingComputed) + outerExact +
                  tailExact| + (|outerExact| + |tailExact|) :=
            add_le_add_right (abs_add_le _ _) _
          _ ≤ (((outerCount - 1) + tailCount : ℕ) : ℝ) *
                  fmt.unitRoundoff * (outerAbs + tailAbs) +
                (outerAbs + tailAbs) := by
            exact add_le_add houter
              (add_le_add outer_exact_abs_le tail_exact_abs_le)
          _ = (1 + (((outerCount - 1) + tailCount : ℕ) : ℝ) *
                fmt.unitRoundoff) * (outerAbs + tailAbs) := by ring
      have hround₁ :
          |fmt.round (pivotValue + siblingComputed) -
              (pivotValue + siblingComputed)| ≤
            fmt.unitRoundoff *
              (1 + (((outerCount - 1) + tailCount : ℕ) : ℝ) *
                fmt.unitRoundoff) * (outerAbs + tailAbs) := by
        calc
          _ ≤ fmt.unitRoundoff *
              |fmt.round (pivotValue + siblingComputed)| := hround_output
          _ ≤ fmt.unitRoundoff *
              ((1 + (((outerCount - 1) + tailCount : ℕ) : ℝ) *
                fmt.unitRoundoff) * (outerAbs + tailAbs)) :=
            mul_le_mul_of_nonneg_left hrounded hu
          _ = _ := by ring
      have hround₂ :
          |fmt.round (pivotValue + siblingComputed) -
              (pivotValue + siblingComputed)| ≤
            (1 + (siblingCount : ℝ) * fmt.unitRoundoff) *
              siblingAbs := by
        rw [abs_sub_comm]
        exact le_trans hround_nearest hs_computed
      have hround :
          |fmt.round (pivotValue + siblingComputed) -
              (pivotValue + siblingComputed)| ≤
            (siblingCount : ℝ) * fmt.unitRoundoff *
                (outerAbs + tailAbs) +
              (((outerCount - 1) + tailCount : ℕ) : ℝ) *
                fmt.unitRoundoff * siblingAbs := by
        exact p05_test_algebra
          (((outerCount - 1) + tailCount : ℕ) : ℝ)
          (siblingCount : ℝ) fmt.unitRoundoff
          (outerAbs + tailAbs) siblingAbs
          |fmt.round (pivotValue + siblingComputed) -
            (pivotValue + siblingComputed)|
          hcombined_count hs_count hu hu2
          (add_nonneg outer_abs_nonneg tail_abs_nonneg)
          sibling_abs_nonneg hround₁ hround₂
      calc
        |pivotValue + (siblingExact + outerExact) + tailExact| =
            |(fmt.round (pivotValue + siblingComputed) + outerExact +
                tailExact) -
              (fmt.round (pivotValue + siblingComputed) -
                (pivotValue + siblingComputed)) -
              (siblingComputed - siblingExact)| := by
                  congr 1
                  ring
        _ ≤ |fmt.round (pivotValue + siblingComputed) + outerExact +
                tailExact| +
              |fmt.round (pivotValue + siblingComputed) -
                (pivotValue + siblingComputed)| +
              |siblingComputed - siblingExact| := by
          calc
            _ ≤ |(fmt.round (pivotValue + siblingComputed) + outerExact +
                    tailExact) -
                  (fmt.round (pivotValue + siblingComputed) -
                    (pivotValue + siblingComputed))| +
                |siblingComputed - siblingExact| := abs_sub _ _
            _ ≤ (|fmt.round (pivotValue + siblingComputed) + outerExact +
                    tailExact| +
                  |fmt.round (pivotValue + siblingComputed) -
                    (pivotValue + siblingComputed)|) +
                |siblingComputed - siblingExact| :=
              add_le_add_left (abs_sub _ _) _
        _ ≤ (((outerCount - 1) + tailCount : ℕ) : ℝ) *
                fmt.unitRoundoff * (outerAbs + tailAbs) +
              ((siblingCount : ℝ) * fmt.unitRoundoff *
                  (outerAbs + tailAbs) +
                (((outerCount - 1) + tailCount : ℕ) : ℝ) *
                  fmt.unitRoundoff * siblingAbs) +
              ((siblingCount : ℝ) * fmt.unitRoundoff * siblingAbs) := by
          gcongr
        _ = ((((outerCount + siblingCount) - 1) + tailCount : ℕ) : ℝ) *
              fmt.unitRoundoff * ((siblingAbs + outerAbs) + tailAbs) := by
          have hn : (outerCount + siblingCount - 1) + tailCount =
              ((outerCount - 1) + tailCount) + siblingCount := by omega
          rw [hn]
          push_cast
          ring

lemma p05_lemma41_run_bound {m : ℕ} (run : P05Lemma41Run m) :
    run.format.representable run.yHat ∧
    |run.c - ((∑ i : Fin m, run.a i * run.b i) +
        run.bK * run.yHat)| ≤
      ((m + 1 : ℕ) : ℝ) * run.format.unitRoundoff *
        ((∑ i : Fin m, |run.a i * run.b i|) +
          |run.bK * run.yHat|) := by
  rcases p05_protected_sum_trace_bound run.protected_sum_trace with
    ⟨trace_count_pos, numerator_representable, trace_abs_nonneg,
      trace_exact_abs_le, trace_residual⟩
  have hy_representable : run.format.representable run.yHat := by
    by_cases hb : run.bK = 1
    · rw [run.no_division_when_unit hb]
      exact numerator_representable
    · rw [run.rounded_division hb]
      exact run.format.round_representable _ (run.division_safe hb)
  have hdivision :
      |run.numerator - run.bK * run.yHat| ≤
        run.format.unitRoundoff * |run.bK * run.yHat| := by
    by_cases hb : run.bK = 1
    · rw [hb, run.no_division_when_unit hb]
      simp only [one_mul, sub_self, abs_zero]
      exact mul_nonneg run.format.unitRoundoff_nonneg (abs_nonneg _)
    · have hround :
          |run.yHat - run.numerator / run.bK| ≤
            run.format.unitRoundoff * |run.yHat| := by
        rw [run.rounded_division hb]
        exact run.format.round_error_to_output _ (run.division_safe hb)
      calc
        |run.numerator - run.bK * run.yHat| =
            |run.bK| * |run.numerator / run.bK - run.yHat| := by
              rw [← abs_mul]
              congr 1
              field_simp [run.bK_nonzero]
        _ = |run.bK| * |run.yHat - run.numerator / run.bK| := by
              rw [abs_sub_comm]
        _ ≤ |run.bK| *
              (run.format.unitRoundoff * |run.yHat|) :=
          mul_le_mul_of_nonneg_left hround (abs_nonneg _)
        _ = run.format.unitRoundoff * |run.bK * run.yHat| := by
          rw [abs_mul]
          ring
  have htail :
      |run.numerator + (-(run.bK * run.yHat))| ≤
        ((1 : ℕ) : ℝ) * run.format.unitRoundoff *
          |run.bK * run.yHat| := by
    simpa [sub_eq_add_neg] using hdivision
  have hclose := p05_protected_sum_trace_close
    run.protected_sum_trace (tailCount := 1) (by norm_num)
    (tailExact := -(run.bK * run.yHat))
    (tailAbs := |run.bK * run.yHat|)
    (abs_nonneg _) (by simp) htail
  constructor
  · exact hy_representable
  · convert hclose using 1
    · congr 1
      ring

lemma p05_lemma43_run_bound {m : ℕ} (run : P05Lemma43Run m) :
    run.format.representable run.yHat ∧
    |run.c - ((∑ i : Fin m, run.a i * run.b i) +
        run.yHat * run.yHat)| ≤
      ((m + 2 : ℕ) : ℝ) * run.format.unitRoundoff *
        ((∑ i : Fin m, |run.a i * run.b i|) +
          |run.yHat| * |run.yHat|) := by
  rcases p05_protected_sum_trace_bound run.protected_sum_trace with
    ⟨trace_count_pos, numerator_representable, trace_abs_nonneg,
      trace_exact_abs_le, trace_residual⟩
  have hy_representable : run.format.representable run.yHat := by
    rw [run.rounded_sqrt]
    exact run.format.round_representable _ run.sqrt_safe
  have hsquare :
      |run.yHat ^ 2 - run.numerator| ≤
        2 * run.format.unitRoundoff * |run.yHat ^ 2| := by
    rw [run.rounded_sqrt]
    exact run.format.sqrt_round_square_error _ run.numerator_nonneg
      numerator_representable run.sqrt_safe
  have htail :
      |run.numerator + (-(run.yHat ^ 2))| ≤
        ((2 : ℕ) : ℝ) * run.format.unitRoundoff *
          |run.yHat ^ 2| := by
    rw [← abs_sub_comm] at hsquare
    simpa [sub_eq_add_neg] using hsquare
  have hclose := p05_protected_sum_trace_close
    run.protected_sum_trace (tailCount := 2) (by norm_num)
    (tailExact := -(run.yHat ^ 2)) (tailAbs := |run.yHat ^ 2|)
    (abs_nonneg _) (by simp) htail
  constructor
  · exact hy_representable
  · convert hclose using 1
    · congr 1
      ring
    · simp [pow_two, abs_mul]

lemma p05_cholesky_off_diagonal_bound {n : ℕ}
    (run : P05CholeskyRun n) (i j : Fin n) (hij : i.val < j.val) :
    run.format.representable (run.RHat i j) ∧
    |run.A i j - p05CholeskyThroughDot run.RHat i j| ≤
      ((i.val + 1 : ℕ) : ℝ) * run.format.unitRoundoff *
        p05CholeskyThroughAbsDot run.RHat i j := by
  let entry := run.off_diagonal_entry i j hij
  rcases p05_lemma41_run_bound entry.execution with ⟨hrep, hbound⟩
  have hrep' : run.format.representable (run.RHat i j) := by
    have hf := congrArg
      (fun fmt : P05FiniteRoundToNearestFormat =>
        fmt.representable entry.execution.yHat) entry.format_eq
    rw [← entry.computed_output_eq]
    exact hf.mp hrep
  have hbound' := hbound
  have hu : entry.execution.format.unitRoundoff =
      run.format.unitRoundoff := congrArg
        (fun fmt : P05FiniteRoundToNearestFormat => fmt.unitRoundoff)
        entry.format_eq
  simp_rw [entry.left_input_eq, entry.right_input_eq] at hbound'
  rw [hu, entry.denominator_eq, entry.protected_input_eq,
    entry.computed_output_eq] at hbound'
  constructor
  · exact hrep'
  · simpa [p05CholeskyThroughDot, p05CholeskyPrefixDot,
      p05CholeskyThroughAbsDot, p05CholeskyPrefixAbsDot] using hbound'

lemma p05_cholesky_diagonal_bound {n : ℕ}
    (run : P05CholeskyRun n) (j : Fin n) :
    run.format.representable (run.RHat j j) ∧
    |run.A j j - p05CholeskyThroughDot run.RHat j j| ≤
      ((j.val + 2 : ℕ) : ℝ) * run.format.unitRoundoff *
        p05CholeskyThroughAbsDot run.RHat j j := by
  let entry := run.diagonal_entry j
  rcases p05_lemma43_run_bound entry.execution with ⟨hrep, hbound⟩
  have hrep' : run.format.representable (run.RHat j j) := by
    have hf := congrArg
      (fun fmt : P05FiniteRoundToNearestFormat =>
        fmt.representable entry.execution.yHat) entry.format_eq
    rw [← entry.computed_output_eq]
    exact hf.mp hrep
  have hbound' := hbound
  have hu : entry.execution.format.unitRoundoff =
      run.format.unitRoundoff := congrArg
        (fun fmt : P05FiniteRoundToNearestFormat => fmt.unitRoundoff)
        entry.format_eq
  simp_rw [entry.left_input_eq, entry.right_input_eq] at hbound'
  rw [hu, entry.protected_input_eq, entry.computed_output_eq] at hbound'
  constructor
  · exact hrep'
  · simpa [p05CholeskyThroughDot, p05CholeskyPrefixDot,
      p05CholeskyThroughAbsDot, p05CholeskyPrefixAbsDot] using hbound'

lemma p05_fin_sum_eq_prefix_add {n : ℕ} (i : Fin n) (f : Fin n → ℝ)
    (hzero : ∀ k : Fin n, i.val < k.val → f k = 0) :
    (∑ k : Fin n, f k) =
      (∑ k : Fin i.val, f (p05PrefixIndex i k)) + f i := by
  let g : ℕ → ℝ := fun k => if hk : k < n then f ⟨k, hk⟩ else 0
  have hfull : (∑ k : Fin n, f k) =
      ∑ k ∈ Finset.range n, g k := by
    rw [← Fin.sum_univ_eq_sum_range g n]
    apply Finset.sum_congr rfl
    intro k hk
    simp [g, Fin.ext_iff]
  have hprefix : (∑ k : Fin i.val, f (p05PrefixIndex i k)) =
      ∑ k ∈ Finset.range i.val, g k := by
    rw [← Fin.sum_univ_eq_sum_range g i.val]
    apply Finset.sum_congr rfl
    intro k hk
    have hkn : k.val < n := lt_trans k.isLt i.isLt
    simp only [g, dif_pos hkn]
    apply congrArg f
    apply Fin.ext
    rfl
  have hsubset : Finset.range (i.val + 1) ⊆ Finset.range n := by
    intro k hk
    simp only [Finset.mem_range] at hk ⊢
    omega
  have hextra : ∀ k ∈ Finset.range n,
      k ∉ Finset.range (i.val + 1) → g k = 0 := by
    intro k hkn hki
    simp only [Finset.mem_range] at hkn hki
    simp only [g, dif_pos hkn]
    apply hzero
    change i.val < k
    omega
  have hrange := Finset.sum_subset hsubset hextra
  rw [hfull, ← hrange, Finset.sum_range_succ, ← hprefix]
  simp [g, i.isLt, Fin.ext_iff]

lemma p05_cholesky_matmul_eq_through {n : ℕ} (run : P05CholeskyRun n)
    (i j : Fin n) :
    p05MatMul (p05Transpose run.RHat) run.RHat i j =
      p05CholeskyThroughDot run.RHat i j := by
  unfold p05MatMul p05Transpose p05CholeskyThroughDot
    p05CholeskyPrefixDot
  apply p05_fin_sum_eq_prefix_add
  intro k hik
  rw [run.RHat_lower_zero k i hik]
  simp

lemma p05_cholesky_abs_matmul_eq_through {n : ℕ} (run : P05CholeskyRun n)
    (i j : Fin n) :
    p05AbsMatMul (p05Transpose run.RHat) run.RHat i j =
      p05CholeskyThroughAbsDot run.RHat i j := by
  unfold p05AbsMatMul p05Transpose p05CholeskyThroughAbsDot
    p05CholeskyPrefixAbsDot
  apply p05_fin_sum_eq_prefix_add
  intro k hik
  rw [run.RHat_lower_zero k i hik]
  simp

lemma p05_cholesky_matmul_symmetric {n : ℕ} (run : P05CholeskyRun n)
    (i j : Fin n) :
    p05MatMul (p05Transpose run.RHat) run.RHat i j =
      p05MatMul (p05Transpose run.RHat) run.RHat j i := by
  unfold p05MatMul p05Transpose
  apply Finset.sum_congr rfl
  intro k hk
  ring

lemma p05_cholesky_abs_matmul_symmetric {n : ℕ} (run : P05CholeskyRun n)
    (i j : Fin n) :
    p05AbsMatMul (p05Transpose run.RHat) run.RHat i j =
      p05AbsMatMul (p05Transpose run.RHat) run.RHat j i := by
  unfold p05AbsMatMul p05Transpose
  apply Finset.sum_congr rfl
  intro k hk
  ring

lemma p05_cholesky_abs_matmul_nonneg {n : ℕ} (run : P05CholeskyRun n)
    (i j : Fin n) :
    0 ≤ p05AbsMatMul (p05Transpose run.RHat) run.RHat i j := by
  unfold p05AbsMatMul p05Transpose
  exact Finset.sum_nonneg fun k hk =>
    mul_nonneg (abs_nonneg _) (abs_nonneg _)

lemma p05_cholesky_gram_entry_bound {n : ℕ} (run : P05CholeskyRun n)
    (i j : Fin n) :
    |run.A i j - p05MatMul (p05Transpose run.RHat) run.RHat i j| ≤
      ((i.val + 2 : ℕ) : ℝ) * run.format.unitRoundoff *
        p05AbsMatMul (p05Transpose run.RHat) run.RHat i j := by
  by_cases hij : i.val < j.val
  · have h := (p05_cholesky_off_diagonal_bound run i j hij).2
    rw [← p05_cholesky_matmul_eq_through run i j,
      ← p05_cholesky_abs_matmul_eq_through run i j] at h
    calc
      _ ≤ ((i.val + 1 : ℕ) : ℝ) * run.format.unitRoundoff *
          p05AbsMatMul (p05Transpose run.RHat) run.RHat i j := h
      _ ≤ ((i.val + 2 : ℕ) : ℝ) * run.format.unitRoundoff *
          p05AbsMatMul (p05Transpose run.RHat) run.RHat i j := by
        have hu := run.format.unitRoundoff_nonneg
        have habs := p05_cholesky_abs_matmul_nonneg run i j
        norm_num only [Nat.cast_add, Nat.cast_one, Nat.cast_ofNat]
        nlinarith
  · by_cases hji : j.val < i.val
    · have h := (p05_cholesky_off_diagonal_bound run j i hji).2
      rw [← p05_cholesky_matmul_eq_through run j i,
        ← p05_cholesky_abs_matmul_eq_through run j i] at h
      calc
        |run.A i j - p05MatMul (p05Transpose run.RHat) run.RHat i j| =
            |run.A j i - p05MatMul (p05Transpose run.RHat) run.RHat j i| := by
          rw [run.A_symmetric i j, p05_cholesky_matmul_symmetric run i j]
        _ ≤ ((j.val + 1 : ℕ) : ℝ) * run.format.unitRoundoff *
            p05AbsMatMul (p05Transpose run.RHat) run.RHat j i := h
        _ = ((j.val + 1 : ℕ) : ℝ) * run.format.unitRoundoff *
            p05AbsMatMul (p05Transpose run.RHat) run.RHat i j := by
          rw [p05_cholesky_abs_matmul_symmetric run i j]
        _ ≤ ((i.val + 2 : ℕ) : ℝ) * run.format.unitRoundoff *
            p05AbsMatMul (p05Transpose run.RHat) run.RHat i j := by
          have hu := run.format.unitRoundoff_nonneg
          have habs := p05_cholesky_abs_matmul_nonneg run i j
          have hv : ((j.val + 1 : ℕ) : ℝ) ≤ (i.val + 2 : ℕ) := by
            exact_mod_cast (show j.val + 1 ≤ i.val + 2 by omega)
          have hz : 0 ≤ run.format.unitRoundoff *
              p05AbsMatMul (p05Transpose run.RHat) run.RHat i j :=
            mul_nonneg hu habs
          simpa [mul_assoc] using mul_le_mul_of_nonneg_right hv hz
    · have heq : i = j := Fin.ext (by omega)
      subst j
      have h := (p05_cholesky_diagonal_bound run i).2
      rwa [← p05_cholesky_matmul_eq_through run i i,
        ← p05_cholesky_abs_matmul_eq_through run i i] at h

theorem p05_t3_cholesky_backward_error
    {n : ℕ} (run : P05CholeskyRun n) :
    (∀ i j, run.format.representable (run.RHat i j)) ∧
    (∀ i j, i.val < j.val →
      |run.A i j - p05CholeskyThroughDot run.RHat i j| ≤
        ((i.val + 1 : ℕ) : ℝ) * run.format.unitRoundoff *
          p05CholeskyThroughAbsDot run.RHat i j) ∧
    (∀ j,
      |run.A j j - p05CholeskyThroughDot run.RHat j j| ≤
        ((j.val + 2 : ℕ) : ℝ) * run.format.unitRoundoff *
          p05CholeskyThroughAbsDot run.RHat j j) ∧
    ∃ ΔA : Fin n → Fin n → ℝ,
      p05MatMul (p05Transpose run.RHat) run.RHat = run.A + ΔA ∧
      (∀ i j,
        |ΔA i j| ≤ ((i.val + 2 : ℕ) : ℝ) *
          run.format.unitRoundoff *
            p05AbsMatMul (p05Transpose run.RHat) run.RHat i j) ∧
      ∀ i j,
        |ΔA i j| ≤ ((n + 1 : ℕ) : ℝ) *
          run.format.unitRoundoff *
            p05AbsMatMul (p05Transpose run.RHat) run.RHat i j := by
  -- PROOF_START P05-T3-H001
  constructor
  · intro i j
    by_cases hji : j.val < i.val
    · rw [run.RHat_lower_zero i j hji]
      exact run.format.zero_representable
    · by_cases hij : i.val < j.val
      · exact (p05_cholesky_off_diagonal_bound run i j hij).1
      · have heq : i = j := Fin.ext (by omega)
        subst j
        exact (p05_cholesky_diagonal_bound run i).1
  constructor
  · intro i j hij
    exact (p05_cholesky_off_diagonal_bound run i j hij).2
  constructor
  · intro j
    exact (p05_cholesky_diagonal_bound run j).2
  · let ΔA : Fin n → Fin n → ℝ := fun i j =>
      p05MatMul (p05Transpose run.RHat) run.RHat i j - run.A i j
    refine ⟨ΔA, ?_, ?_, ?_⟩
    · funext i j
      change p05MatMul (p05Transpose run.RHat) run.RHat i j =
        run.A i j +
          (p05MatMul (p05Transpose run.RHat) run.RHat i j - run.A i j)
      ring
    · intro i j
      change |p05MatMul (p05Transpose run.RHat) run.RHat i j - run.A i j| ≤ _
      rw [abs_sub_comm]
      exact p05_cholesky_gram_entry_bound run i j
    · intro i j
      have hentry := p05_cholesky_gram_entry_bound run i j
      have hv : ((i.val + 2 : ℕ) : ℝ) ≤ (n + 1 : ℕ) := by
        exact_mod_cast (show i.val + 2 ≤ n + 1 by omega)
      have hz : 0 ≤ run.format.unitRoundoff *
          p05AbsMatMul (p05Transpose run.RHat) run.RHat i j :=
        mul_nonneg run.format.unitRoundoff_nonneg
          (p05_cholesky_abs_matmul_nonneg run i j)
      change |p05MatMul (p05Transpose run.RHat) run.RHat i j - run.A i j| ≤ _
      rw [abs_sub_comm]
      exact le_trans hentry (by
        simpa [mul_assoc] using mul_le_mul_of_nonneg_right hv hz)

end HighamBench
