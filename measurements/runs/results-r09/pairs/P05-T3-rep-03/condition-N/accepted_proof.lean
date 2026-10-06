import HighamBench.P05Definitions

namespace HighamBench

open scoped BigOperators

private theorem p05_trace_count_pos
    {fmt : P05FiniteRoundToNearestFormat} {termCount : ℕ}
    {pivotValue outsideExact outsideAbs computed : ℝ}
    (h : P05ProtectedSumTrace fmt termCount pivotValue outsideExact outsideAbs computed) :
    0 < termCount := by
  induction h with
  | leaf => simp
  | merge sibling_count_pos outer ih => omega

private theorem p05_trace_abs_data
    {fmt : P05FiniteRoundToNearestFormat} {termCount : ℕ}
    {pivotValue outsideExact outsideAbs computed : ℝ}
    (h : P05ProtectedSumTrace fmt termCount pivotValue outsideExact outsideAbs computed) :
    0 ≤ outsideAbs ∧ |outsideExact| ≤ outsideAbs := by
  induction h with
  | leaf => simp
  | @merge outerCount siblingCount pivotValue siblingExact siblingAbs
      siblingComputed outerExact outerAbs computed pivot_representable
      sibling_count_pos sibling_abs_nonneg sibling_exact_abs_le
      sibling_computed_representable sibling_error_bound merge_safe outer ih =>
      constructor
      · exact add_nonneg sibling_abs_nonneg ih.1
      · calc
          |siblingExact + outerExact| ≤
              |siblingExact| + |outerExact| := abs_add_le _ _
          _ ≤ _ := add_le_add sibling_exact_abs_le ih.2

private theorem p05_min_amortization
    {u O S Y B e : ℝ}
    (hu0 : 0 ≤ u) (hu : u ≤ 1 / 2)
    (hO : 1 ≤ O) (hS : 1 ≤ S)
    (hY : 0 ≤ Y) (hB : 0 ≤ B) (he : 0 ≤ e)
    (heY : e ≤ u * (1 + O * u) * Y)
    (heB : e ≤ (1 + S * u) * B) :
    e ≤ u * (S * Y + O * B) := by
  by_cases hfirst : u * (1 + O * u) * Y ≤ u * (S * Y + O * B)
  · exact heY.trans hfirst
  · have hu1 : u ≤ 1 := by linarith
    have hu_sq : u ^ 2 ≤ u := by nlinarith
    have hkey :
        0 ≤ (S - 1) * (1 + S * u) + O * (O - S) * u ^ 2 := by
      by_cases hOS : S ≤ O
      · have hS0 : 0 ≤ S := by linarith
        have hO0 : 0 ≤ O := by linarith
        have hS1 : 0 ≤ S - 1 := by linarith
        have hOS0 : 0 ≤ O - S := by linarith
        have hsu : 0 ≤ 1 + S * u := by positivity
        exact add_nonneg (mul_nonneg hS1 hsu)
          (mul_nonneg (mul_nonneg hO0 hOS0) (sq_nonneg u))
      · have hOleS : O ≤ S := le_of_not_ge hOS
        have hSO0 : 0 ≤ S - O := sub_nonneg.mpr hOleS
        have hS10 : 0 ≤ S - 1 := sub_nonneg.mpr hS
        have hOS_le : O * (S - O) ≤ S * (S - 1) := by
          exact mul_le_mul hOleS (by linarith) hSO0 (by linarith)
        have hprod : O * (S - O) * u ^ 2 ≤ S * (S - 1) * u := by
          calc
            O * (S - O) * u ^ 2 ≤ S * (S - 1) * u ^ 2 := by
              gcongr
            _ ≤ S * (S - 1) * u := by
              gcongr
        nlinarith
    have hcoeff :
        (1 + (S - O) * u) * (1 + O * u - S) ≤ O * u * S := by
      nlinarith
    have hUYB : u * (1 + O * u) * Y > u * (S * Y + O * B) :=
      lt_of_not_ge hfirst
    have hu_pos : 0 < u := by
      by_contra huz
      have : u = 0 := le_antisymm (le_of_not_gt huz) hu0
      subst u
      norm_num at hUYB
    have hgap : O * B < (1 + O * u - S) * Y := by
      nlinarith
    by_cases hc : 1 + (S - O) * u ≤ 0
    · have hS0 : 0 ≤ S := by linarith
      nlinarith [mul_nonneg hu0 (mul_nonneg hS0 hY)]
    · have hc0 : 0 ≤ 1 + (S - O) * u := le_of_not_ge hc
      have hm := mul_le_mul_of_nonneg_left (le_of_lt hgap) hc0
      have hS0 : 0 ≤ S := by linarith
      nlinarith [mul_nonneg hu0 (mul_nonneg hS0 hY)]

private theorem p05_protected_sum_trace_terminal_error
    {fmt : P05FiniteRoundToNearestFormat} {termCount : ℕ}
    {pivotValue outsideExact outsideAbs computed : ℝ}
    (h : P05ProtectedSumTrace fmt termCount pivotValue outsideExact outsideAbs computed)
    {terminal baseWeight : ℝ} (hbase : 1 ≤ baseWeight)
    (hterminal : |terminal - computed| ≤
      baseWeight * fmt.unitRoundoff * |terminal|) :
    |terminal - (pivotValue + outsideExact)| ≤
      ((termCount : ℝ) - 1 + baseWeight) * fmt.unitRoundoff *
        (|terminal| + outsideAbs) := by
  induction h with
  | leaf => simpa using hterminal
  | @merge outerCount siblingCount pivotValue siblingExact siblingAbs
      siblingComputed outerExact outerAbs computed pivot_representable
      sibling_count_pos sibling_abs_nonneg sibling_exact_abs_le
      sibling_computed_representable sibling_error_bound merge_safe outer ih =>
      let q := fmt.round (pivotValue + siblingComputed)
      let u := fmt.unitRoundoff
      let K := (outerCount : ℝ) - 1 + baseWeight
      have hu0 : 0 ≤ u := fmt.unitRoundoff_nonneg
      have hu : u ≤ 1 / 2 := fmt.unitRoundoff_le_half
      have hout := p05_trace_abs_data outer
      have houterCount : 1 ≤ (outerCount : ℝ) := by
        exact_mod_cast p05_trace_count_pos outer
      have hK : 1 ≤ K := by
        dsimp [K]
        linarith
      have hsiblingCount : 1 ≤ (siblingCount : ℝ) := by
        exact_mod_cast sibling_count_pos
      have hY : 0 ≤ |terminal| + outerAbs :=
        add_nonneg (abs_nonneg _) hout.1
      have hround :
          |q - (pivotValue + siblingComputed)| ≤ u * |q| := by
        simpa [q, u] using
          fmt.round_error_to_output (pivotValue + siblingComputed) merge_safe
      have hnearest :
          |q - (pivotValue + siblingComputed)| ≤ |siblingComputed| := by
        have hn := fmt.round_nearest (pivotValue + siblingComputed) merge_safe
          pivotValue pivot_representable
        rw [abs_sub_comm] at hn
        simpa [q] using hn
      have hscomp :
          |siblingComputed| ≤
            (1 + (siblingCount : ℝ) * u) * siblingAbs := by
        calc
          |siblingComputed| =
              |(siblingComputed - siblingExact) + siblingExact| := by ring_nf
          _ ≤ |siblingComputed - siblingExact| + |siblingExact| := abs_add_le _ _
          _ ≤ (siblingCount : ℝ) * u * siblingAbs + siblingAbs :=
            add_le_add (by simpa [u] using sibling_error_bound) sibling_exact_abs_le
          _ = (1 + (siblingCount : ℝ) * u) * siblingAbs := by ring
      have hq :
          |q| ≤
            (1 + K * u) * (|terminal| + outerAbs) := by
        have hq0 :
            |q| ≤ |terminal| + |outerExact| +
              |terminal - (q + outerExact)| := by
          calc
            |q| =
                |(terminal - outerExact) - (terminal - (q + outerExact))| := by
                  congr 1 <;> ring
            _ ≤ |terminal - outerExact| +
                |terminal - (q + outerExact)| := abs_sub _ _
            _ ≤ (|terminal| + |outerExact|) +
                |terminal - (q + outerExact)| := by
                  gcongr
                  exact abs_sub _ _
        have hih :
            |terminal - (q + outerExact)| ≤
              K * u * (|terminal| + outerAbs) := by
          simpa [q, u, K] using ih hterminal
        calc
          |q| ≤ |terminal| + |outerExact| +
              |terminal - (q + outerExact)| := hq0
          _ ≤ (|terminal| + outerAbs) +
              K * u * (|terminal| + outerAbs) := by
                gcongr
                exact hout.2
          _ = (1 + K * u) * (|terminal| + outerAbs) := by ring
      have hlocalY :
          |q - (pivotValue + siblingComputed)| ≤
            u * (1 + K * u) *
              (|terminal| + outerAbs) := by
        simpa only [mul_assoc] using
          hround.trans (mul_le_mul_of_nonneg_left hq hu0)
      have hlocalB :
          |q - (pivotValue + siblingComputed)| ≤
            (1 + (siblingCount : ℝ) * u) * siblingAbs :=
        hnearest.trans hscomp
      have hlocal :
          |q - (pivotValue + siblingComputed)| ≤
            u * ((siblingCount : ℝ) * (|terminal| + outerAbs) +
              K * siblingAbs) := by
        exact p05_min_amortization hu0 hu hK hsiblingCount hY
          sibling_abs_nonneg (abs_nonneg _) hlocalY hlocalB
      have htotal :
          |terminal - (pivotValue + (siblingExact + outerExact))| ≤
            |terminal - (q + outerExact)| +
              |q - (pivotValue + siblingComputed)| +
                |siblingComputed - siblingExact| := by
        calc
          |terminal - (pivotValue + (siblingExact + outerExact))| =
              |(terminal - (q + outerExact)) +
                (q - (pivotValue + siblingComputed)) +
                  (siblingComputed - siblingExact)| := by congr 1 <;> ring
          _ ≤ |terminal - (q + outerExact)| +
                |q - (pivotValue + siblingComputed)| +
                  |siblingComputed - siblingExact| :=
            abs_add_three _ _ _
      calc
        |terminal - (pivotValue + (siblingExact + outerExact))| ≤
            |terminal - (q + outerExact)| +
              |q - (pivotValue + siblingComputed)| +
                |siblingComputed - siblingExact| := htotal
        _ ≤ K * u * (|terminal| + outerAbs) +
              u * ((siblingCount : ℝ) * (|terminal| + outerAbs) +
                K * siblingAbs) +
              (siblingCount : ℝ) * u * siblingAbs := by
            exact add_le_add
              (add_le_add (by simpa [q, u, K] using ih hterminal) hlocal)
              (by simpa [u] using sibling_error_bound)
        _ = (((outerCount + siblingCount : ℕ) : ℝ) - 1 + baseWeight) * u *
              (|terminal| + (siblingAbs + outerAbs)) := by
            dsimp [K]
            push_cast
            ring

private theorem p05_protected_sum_trace_error
    {fmt : P05FiniteRoundToNearestFormat} {termCount : ℕ}
    {pivotValue outsideExact outsideAbs computed : ℝ}
    (h : P05ProtectedSumTrace fmt termCount pivotValue outsideExact outsideAbs computed) :
    |computed - (pivotValue + outsideExact)| ≤
      (termCount : ℝ) * fmt.unitRoundoff * (|computed| + outsideAbs) := by
  have hz : |computed - computed| ≤
      (1 : ℝ) * fmt.unitRoundoff * |computed| := by
    simpa using mul_nonneg fmt.unitRoundoff_nonneg (abs_nonneg computed)
  simpa using p05_protected_sum_trace_terminal_error h (baseWeight := (1 : ℝ))
    (by norm_num) hz

private theorem p05_sum_tree_eval_representable
    (fmt : P05FiniteRoundToNearestFormat) {n : ℕ}
    (tree : P05SumTree n) (v : Fin n → ℝ)
    (h : p05SumTreeSafe fmt tree v) :
    fmt.representable (p05SumTreeEval fmt tree v) := by
  induction tree with
  | leaf => simpa [p05SumTreeSafe, p05SumTreeEval] using h
  | @node m n left right ihLeft ihRight =>
      simp only [p05SumTreeSafe] at h
      simp only [p05SumTreeEval]
      exact fmt.round_representable _ h.2.2

private theorem p05_lemma41_output_representable {m : ℕ}
    (ex : P05Lemma41Run m) : ex.format.representable ex.yHat := by
  by_cases hb : ex.bK = 1
  · rw [ex.no_division_when_unit hb, ex.numerator_eq]
    exact p05_sum_tree_eval_representable ex.format ex.tree _ ex.tree_safe
  · rw [ex.rounded_division hb]
    exact ex.format.round_representable _ (ex.division_safe hb)

private theorem p05_lemma41_error {m : ℕ} (ex : P05Lemma41Run m) :
    |ex.c - ((∑ i : Fin m, ex.a i * ex.b i) + ex.bK * ex.yHat)| ≤
      ((m + 1 : ℕ) : ℝ) * ex.format.unitRoundoff *
        ((∑ i : Fin m, |ex.a i * ex.b i|) + |ex.bK| * |ex.yHat|) := by
  let z := ex.bK * ex.yHat
  have hz : |z - ex.numerator| ≤
      (1 : ℝ) * ex.format.unitRoundoff * |z| := by
    by_cases hb : ex.bK = 1
    · have hy := ex.no_division_when_unit hb
      simp [z, hb, hy]
      exact mul_nonneg ex.format.unitRoundoff_nonneg (abs_nonneg ex.numerator)
    · have hr := ex.format.round_error_to_output (ex.numerator / ex.bK)
          (ex.division_safe hb)
      rw [← ex.rounded_division hb] at hr
      have heq :
          |z - ex.numerator| = |ex.bK| * |ex.yHat - ex.numerator / ex.bK| := by
        rw [← abs_mul]
        congr 1
        dsimp [z]
        field_simp [ex.bK_nonzero]
      calc
        |z - ex.numerator| =
            |ex.bK| * |ex.yHat - ex.numerator / ex.bK| := heq
        _ ≤ |ex.bK| * (ex.format.unitRoundoff * |ex.yHat|) := by
          gcongr
        _ = (1 : ℝ) * ex.format.unitRoundoff * |z| := by
          simp only [one_mul]
          dsimp [z]
          rw [abs_mul]
          ring
  have ht := p05_protected_sum_trace_terminal_error ex.protected_sum_trace
    (terminal := z) (baseWeight := (1 : ℝ)) (by norm_num) hz
  dsimp [z] at ht
  have hcast : ((m + 1 : ℕ) : ℝ) = (m : ℝ) + 1 := by push_cast; ring
  have hlhs :
      |ex.c - ((∑ i : Fin m, ex.a i * ex.b i) + ex.bK * ex.yHat)| =
        |ex.bK * ex.yHat - (ex.c + -(∑ i : Fin m, ex.a i * ex.b i))| := by
    rw [abs_sub_comm]
    congr 1
    ring
  calc
    |ex.c - ((∑ i : Fin m, ex.a i * ex.b i) + ex.bK * ex.yHat)| =
        |ex.bK * ex.yHat - (ex.c + -(∑ i : Fin m, ex.a i * ex.b i))| := hlhs
    _ ≤ ((m + 1 : ℕ) : ℝ) * ex.format.unitRoundoff *
        (|ex.bK * ex.yHat| + (∑ i : Fin m, |ex.a i * ex.b i|)) := by
      rw [hcast]
      simpa using ht
    _ = ((m + 1 : ℕ) : ℝ) * ex.format.unitRoundoff *
        ((∑ i : Fin m, |ex.a i * ex.b i|) + |ex.bK| * |ex.yHat|) := by
      rw [abs_mul]
      ring

private theorem p05_lemma43_output_representable {m : ℕ}
    (ex : P05Lemma43Run m) : ex.format.representable ex.yHat := by
  rw [ex.rounded_sqrt]
  exact ex.format.round_representable _ ex.sqrt_safe

private theorem p05_lemma43_output_nonneg {m : ℕ}
    (ex : P05Lemma43Run m) : 0 ≤ ex.yHat := by
  rw [ex.rounded_sqrt]
  exact ex.format.round_nonnegative _ (Real.sqrt_nonneg _) ex.sqrt_safe

private theorem p05_lemma43_error {m : ℕ} (ex : P05Lemma43Run m) :
    |ex.c - ((∑ i : Fin m, ex.a i * ex.b i) + ex.yHat * ex.yHat)| ≤
      ((m + 2 : ℕ) : ℝ) * ex.format.unitRoundoff *
        ((∑ i : Fin m, |ex.a i * ex.b i|) + |ex.yHat| * |ex.yHat|) := by
  have hnum : ex.format.representable ex.numerator := by
    rw [ex.numerator_eq]
    exact p05_sum_tree_eval_representable ex.format ex.tree _ ex.tree_safe
  have hsquare := ex.format.sqrt_round_square_error ex.numerator
    ex.numerator_nonneg hnum ex.sqrt_safe
  rw [← ex.rounded_sqrt] at hsquare
  have ht := p05_protected_sum_trace_terminal_error ex.protected_sum_trace
    (terminal := ex.yHat ^ 2) (baseWeight := (2 : ℝ)) (by norm_num) (by
      simpa using hsquare)
  have hcast : ((m + 1 : ℕ) : ℝ) - 1 + 2 = ((m + 2 : ℕ) : ℝ) := by
    push_cast
    ring
  rw [hcast] at ht
  have hlhs :
      |ex.c - ((∑ i : Fin m, ex.a i * ex.b i) + ex.yHat * ex.yHat)| =
        |ex.yHat ^ 2 - (ex.c + -(∑ i : Fin m, ex.a i * ex.b i))| := by
    rw [abs_sub_comm]
    congr 1
    ring
  calc
    |ex.c - ((∑ i : Fin m, ex.a i * ex.b i) + ex.yHat * ex.yHat)| =
        |ex.yHat ^ 2 - (ex.c + -(∑ i : Fin m, ex.a i * ex.b i))| := hlhs
    _ ≤ ((m + 2 : ℕ) : ℝ) * ex.format.unitRoundoff *
        (|ex.yHat ^ 2| + (∑ i : Fin m, |ex.a i * ex.b i|)) := ht
    _ = ((m + 2 : ℕ) : ℝ) * ex.format.unitRoundoff *
        ((∑ i : Fin m, |ex.a i * ex.b i|) + |ex.yHat| * |ex.yHat|) := by
      rw [abs_sq, ← sq_abs]
      ring

private theorem p05_sum_prefix_eq_Iio {n : ℕ} (i : Fin n)
    (f : Fin n → ℝ) :
    (∑ k : Fin i.val, f (p05PrefixIndex i k)) =
      ∑ k ∈ Finset.Iio i, f k := by
  classical
  apply Finset.sum_bij (fun k _ => p05PrefixIndex i k)
  · intro k hk
    simpa only [Finset.mem_Iio] using k.isLt
  · intro a ha b hb hab
    apply Fin.ext
    exact congrArg (fun x : Fin n => x.val) hab
  · intro b hb
    have hbi : b.val < i.val := by simpa using hb
    let a : Fin i.val := ⟨b.val, hbi⟩
    refine ⟨a, Finset.mem_univ a, ?_⟩
    apply Fin.ext
    rfl
  · intro a ha
    rfl

private theorem p05_gram_eq_through {n : ℕ}
    (R : Fin n → Fin n → ℝ)
    (hlower : ∀ i j, j.val < i.val → R i j = 0)
    (i j : Fin n) :
    p05MatMul (p05Transpose R) R i j = p05CholeskyThroughDot R i j := by
  classical
  let f : Fin n → ℝ := fun k => R k i * R k j
  have hsubset :
      (∑ k ∈ Finset.Iic i, f k) = ∑ k : Fin n, f k := by
    apply Finset.sum_subset (by simp)
    intro k hk hki
    have hik : i.val < k.val := by
      have : ¬ k ≤ i := by simpa using hki
      omega
    simp [f, hlower k i hik]
  have hiic : Finset.Iic i = insert i (Finset.Iio i) := by
    ext k
    simp only [Finset.mem_Iic, Finset.mem_insert, Finset.mem_Iio]
    omega
  have hsplit :
      (∑ k : Fin n, f k) = (∑ k ∈ Finset.Iio i, f k) + f i := by
    rw [← hsubset, hiic, Finset.sum_insert (by simp)]
    ring
  change (∑ k : Fin n, R k i * R k j) =
    (∑ k : Fin i.val,
      R (p05PrefixIndex i k) i * R (p05PrefixIndex i k) j) + R i i * R i j
  change (∑ k : Fin n, f k) = _
  rw [hsplit, ← p05_sum_prefix_eq_Iio i f]

private theorem p05_abs_gram_eq_through {n : ℕ}
    (R : Fin n → Fin n → ℝ)
    (hlower : ∀ i j, j.val < i.val → R i j = 0)
    (i j : Fin n) :
    p05AbsMatMul (p05Transpose R) R i j =
      p05CholeskyThroughAbsDot R i j := by
  classical
  let f : Fin n → ℝ := fun k => |R k i| * |R k j|
  have hsubset :
      (∑ k ∈ Finset.Iic i, f k) = ∑ k : Fin n, f k := by
    apply Finset.sum_subset (by simp)
    intro k hk hki
    have hik : i.val < k.val := by
      have : ¬ k ≤ i := by simpa using hki
      omega
    simp [f, hlower k i hik]
  have hiic : Finset.Iic i = insert i (Finset.Iio i) := by
    ext k
    simp only [Finset.mem_Iic, Finset.mem_insert, Finset.mem_Iio]
    omega
  have hsplit :
      (∑ k : Fin n, f k) = (∑ k ∈ Finset.Iio i, f k) + f i := by
    rw [← hsubset, hiic, Finset.sum_insert (by simp)]
    ring
  change (∑ k : Fin n, |R k i| * |R k j|) =
    (∑ k : Fin i.val,
      |R (p05PrefixIndex i k) i| * |R (p05PrefixIndex i k) j|) +
        |R i i| * |R i j|
  change (∑ k : Fin n, f k) = _
  rw [hsplit, ← p05_sum_prefix_eq_Iio i f]

private theorem p05_gram_symmetric {n : ℕ}
    (R : Fin n → Fin n → ℝ) (i j : Fin n) :
    p05MatMul (p05Transpose R) R i j =
      p05MatMul (p05Transpose R) R j i := by
  simp only [p05MatMul, p05Transpose]
  apply Finset.sum_congr rfl
  intro k hk
  ring

private theorem p05_abs_gram_symmetric {n : ℕ}
    (R : Fin n → Fin n → ℝ) (i j : Fin n) :
    p05AbsMatMul (p05Transpose R) R i j =
      p05AbsMatMul (p05Transpose R) R j i := by
  simp only [p05AbsMatMul, p05Transpose]
  apply Finset.sum_congr rfl
  intro k hk
  ring

private theorem p05_abs_gram_nonneg {n : ℕ}
    (R : Fin n → Fin n → ℝ) (i j : Fin n) :
    0 ≤ p05AbsMatMul (p05Transpose R) R i j := by
  simp only [p05AbsMatMul, p05Transpose]
  positivity

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
  have hrep : ∀ i j, run.format.representable (run.RHat i j) := by
    intro i j
    rcases lt_trichotomy i.val j.val with hij | hij | hij
    · let entry := run.off_diagonal_entry i j hij
      rw [← entry.computed_output_eq]
      have he := p05_lemma41_output_representable entry.execution
      have hf := congrArg
        (fun f : P05FiniteRoundToNearestFormat =>
          f.representable entry.execution.yHat) entry.format_eq
      exact hf.mp he
    · have hij' : i = j := Fin.ext hij
      subst j
      let entry := run.diagonal_entry i
      rw [← entry.computed_output_eq]
      have he := p05_lemma43_output_representable entry.execution
      have hf := congrArg
        (fun f : P05FiniteRoundToNearestFormat =>
          f.representable entry.execution.yHat) entry.format_eq
      exact hf.mp he
    · rw [run.RHat_lower_zero i j hij]
      exact run.format.zero_representable
  have hoff : ∀ i j, i.val < j.val →
      |run.A i j - p05CholeskyThroughDot run.RHat i j| ≤
        ((i.val + 1 : ℕ) : ℝ) * run.format.unitRoundoff *
          p05CholeskyThroughAbsDot run.RHat i j := by
    intro i j hij
    let entry := run.off_diagonal_entry i j hij
    have he := p05_lemma41_error entry.execution
    simp_rw [entry.left_input_eq, entry.right_input_eq] at he
    rw [entry.protected_input_eq, entry.denominator_eq,
      entry.computed_output_eq, entry.format_eq] at he
    simpa [p05CholeskyThroughDot, p05CholeskyPrefixDot,
      p05CholeskyThroughAbsDot, p05CholeskyPrefixAbsDot] using he
  have hdiag : ∀ j,
      |run.A j j - p05CholeskyThroughDot run.RHat j j| ≤
        ((j.val + 2 : ℕ) : ℝ) * run.format.unitRoundoff *
          p05CholeskyThroughAbsDot run.RHat j j := by
    intro j
    let entry := run.diagonal_entry j
    have he := p05_lemma43_error entry.execution
    simp_rw [entry.left_input_eq, entry.right_input_eq] at he
    rw [entry.protected_input_eq, entry.computed_output_eq, entry.format_eq] at he
    simpa [p05CholeskyThroughDot, p05CholeskyPrefixDot,
      p05CholeskyThroughAbsDot, p05CholeskyPrefixAbsDot] using he
  refine ⟨hrep, hoff, hdiag, ?_⟩
  let ΔA : Fin n → Fin n → ℝ := fun i j =>
    p05MatMul (p05Transpose run.RHat) run.RHat i j - run.A i j
  have hmatrix :
      p05MatMul (p05Transpose run.RHat) run.RHat = run.A + ΔA := by
    funext i j
    simp only [Pi.add_apply]
    dsimp [ΔA]
    ring
  have hdelta : ∀ i j,
      |ΔA i j| ≤ ((i.val + 2 : ℕ) : ℝ) *
        run.format.unitRoundoff *
          p05AbsMatMul (p05Transpose run.RHat) run.RHat i j := by
    intro i j
    have hdot_i := p05_gram_eq_through run.RHat run.RHat_lower_zero i j
    have habs_i := p05_abs_gram_eq_through run.RHat run.RHat_lower_zero i j
    rcases lt_trichotomy i.val j.val with hij | hij | hij
    · have h := hoff i j hij
      rw [← hdot_i, ← habs_i, abs_sub_comm] at h
      dsimp [ΔA]
      calc
        |p05MatMul (p05Transpose run.RHat) run.RHat i j - run.A i j| ≤
            ((i.val + 1 : ℕ) : ℝ) * run.format.unitRoundoff *
              p05AbsMatMul (p05Transpose run.RHat) run.RHat i j := h
        _ ≤ ((i.val + 2 : ℕ) : ℝ) * run.format.unitRoundoff *
              p05AbsMatMul (p05Transpose run.RHat) run.RHat i j := by
            have hfac : 0 ≤ run.format.unitRoundoff *
                p05AbsMatMul (p05Transpose run.RHat) run.RHat i j :=
              mul_nonneg run.format.unitRoundoff_nonneg
                (p05_abs_gram_nonneg run.RHat i j)
            have hc : ((i.val + 1 : ℕ) : ℝ) ≤ ((i.val + 2 : ℕ) : ℝ) := by
              exact_mod_cast (show i.val + 1 ≤ i.val + 2 by omega)
            simpa only [mul_assoc] using mul_le_mul_of_nonneg_right hc hfac
    · have hij' : i = j := Fin.ext hij
      subst j
      have h := hdiag i
      rw [← hdot_i, ← habs_i, abs_sub_comm] at h
      simpa [ΔA] using h
    · have h := hoff j i hij
      have hdot_j := p05_gram_eq_through run.RHat run.RHat_lower_zero j i
      have habs_j := p05_abs_gram_eq_through run.RHat run.RHat_lower_zero j i
      rw [← hdot_j, ← habs_j, abs_sub_comm] at h
      have hsymm :
          p05MatMul (p05Transpose run.RHat) run.RHat i j - run.A i j =
            p05MatMul (p05Transpose run.RHat) run.RHat j i - run.A j i := by
        rw [p05_gram_symmetric run.RHat i j, run.A_symmetric i j]
      have habssymm :
          p05AbsMatMul (p05Transpose run.RHat) run.RHat j i =
            p05AbsMatMul (p05Transpose run.RHat) run.RHat i j :=
        p05_abs_gram_symmetric run.RHat j i
      dsimp [ΔA]
      rw [hsymm]
      calc
        |p05MatMul (p05Transpose run.RHat) run.RHat j i - run.A j i| ≤
            ((j.val + 1 : ℕ) : ℝ) * run.format.unitRoundoff *
              p05AbsMatMul (p05Transpose run.RHat) run.RHat j i := h
        _ = ((j.val + 1 : ℕ) : ℝ) * run.format.unitRoundoff *
              p05AbsMatMul (p05Transpose run.RHat) run.RHat i j := by
            rw [habssymm]
        _ ≤ ((i.val + 2 : ℕ) : ℝ) * run.format.unitRoundoff *
              p05AbsMatMul (p05Transpose run.RHat) run.RHat i j := by
            have hfac : 0 ≤ run.format.unitRoundoff *
                p05AbsMatMul (p05Transpose run.RHat) run.RHat i j :=
              mul_nonneg run.format.unitRoundoff_nonneg
                (p05_abs_gram_nonneg run.RHat i j)
            have hc : ((j.val + 1 : ℕ) : ℝ) ≤ ((i.val + 2 : ℕ) : ℝ) := by
              exact_mod_cast (show j.val + 1 ≤ i.val + 2 by omega)
            simpa only [mul_assoc] using mul_le_mul_of_nonneg_right hc hfac
  refine ⟨ΔA, hmatrix, hdelta, ?_⟩
  intro i j
  calc
    |ΔA i j| ≤ ((i.val + 2 : ℕ) : ℝ) *
        run.format.unitRoundoff *
          p05AbsMatMul (p05Transpose run.RHat) run.RHat i j := hdelta i j
    _ ≤ ((n + 1 : ℕ) : ℝ) * run.format.unitRoundoff *
          p05AbsMatMul (p05Transpose run.RHat) run.RHat i j := by
      have hfac : 0 ≤ run.format.unitRoundoff *
          p05AbsMatMul (p05Transpose run.RHat) run.RHat i j :=
        mul_nonneg run.format.unitRoundoff_nonneg
          (p05_abs_gram_nonneg run.RHat i j)
      have hc : ((i.val + 2 : ℕ) : ℝ) ≤ ((n + 1 : ℕ) : ℝ) := by
        exact_mod_cast (show i.val + 2 ≤ n + 1 by omega)
      simpa only [mul_assoc] using mul_le_mul_of_nonneg_right hc hfac

end HighamBench
