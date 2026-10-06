import HighamBench.P05Definitions

namespace HighamBench

open scoped BigOperators

private lemma p05_protected_trace_basic
    {fmt : P05FiniteRoundToNearestFormat}
    {termCount : ℕ} {pivotValue outsideExact outsideAbs computed : ℝ}
    (h : P05ProtectedSumTrace fmt termCount pivotValue outsideExact outsideAbs computed) :
    0 < termCount ∧ 0 ≤ outsideAbs ∧ |outsideExact| ≤ outsideAbs ∧
      fmt.representable computed := by
  induction h with
  | leaf pivotValue hpivot =>
      simp [hpivot]
  | @merge outerCount siblingCount pivotValue siblingExact siblingAbs
      siblingComputed outerExact outerAbs computed hpivot hsiblingCount
      hsiblingAbs hsiblingExact hsiblingComputed hsiblingError hsafe outer ih =>
      rcases ih with ⟨houterCount, houterAbs, houterExact, hcomputed⟩
      refine ⟨by omega, add_nonneg hsiblingAbs houterAbs, ?_, hcomputed⟩
      calc
        |siblingExact + outerExact| ≤ |siblingExact| + |outerExact| := abs_add_le _ _
        _ ≤ siblingAbs + outerAbs := add_le_add hsiblingExact houterExact

private lemma p05_protected_trace_bound
    {fmt : P05FiniteRoundToNearestFormat}
    {termCount : ℕ} {pivotValue outsideExact outsideAbs computed z : ℝ}
    (h : P05ProtectedSumTrace fmt termCount pivotValue outsideExact outsideAbs computed)
    (q : ℕ)
    (hq : 0 < q)
    (hcomputed : |computed - z| ≤ (q : ℝ) * fmt.unitRoundoff * |z|) :
    |pivotValue + outsideExact - z| ≤
      (((termCount - 1 + q : ℕ) : ℝ) * fmt.unitRoundoff) *
        (outsideAbs + |z|) := by
  induction h with
  | leaf pivotValue hpivot =>
      simpa using hcomputed
  | @merge outerCount siblingCount pivotValue siblingExact siblingAbs
      siblingComputed outerExact outerAbs computed hpivot hsiblingCount
      hsiblingAbs hsiblingExact hsiblingComputed hsiblingError hsafe outer ih =>
      have hbasic := p05_protected_trace_basic outer
      rcases hbasic with ⟨houterCount, houterAbs, houterExact, hcomputedRep⟩
      let r : ℝ := fmt.round (pivotValue + siblingComputed)
      let u : ℝ := fmt.unitRoundoff
      let Q : ℝ := outerAbs + |z|
      let a : ℝ := ((outerCount - 1 + q : ℕ) : ℝ)
      have hu0 : 0 ≤ u := fmt.unitRoundoff_nonneg
      have hu1 : u ≤ 1 := le_trans fmt.unitRoundoff_le_half (by norm_num)
      have hQ0 : 0 ≤ Q := add_nonneg houterAbs (abs_nonneg z)
      have ha0 : 0 ≤ a := Nat.cast_nonneg _
      have ha1 : (1 : ℝ) ≤ a := by
        dsimp [a]
        exact_mod_cast (show 1 ≤ outerCount - 1 + q by omega)
      have hs0 : 0 ≤ (siblingCount : ℝ) := Nat.cast_nonneg _
      have hs1 : (1 : ℝ) ≤ siblingCount := by exact_mod_cast hsiblingCount
      have hout : |r + outerExact - z| ≤ a * u * Q := by
        simpa [r, u, Q, a, mul_assoc] using ih hcomputed
      have hsiberr : |siblingComputed - siblingExact| ≤
          (siblingCount : ℝ) * u * siblingAbs := by
        simpa [u] using hsiblingError
      have hsibcomp : |siblingComputed| ≤
          (1 + (siblingCount : ℝ) * u) * siblingAbs := by
        have htri : |siblingComputed| ≤
            |siblingComputed - siblingExact| + |siblingExact| := by
          calc
            |siblingComputed| = |(siblingComputed - siblingExact) + siblingExact| := by ring_nf
            _ ≤ |siblingComputed - siblingExact| + |siblingExact| := abs_add_le _ _
        calc
          |siblingComputed| ≤
              |siblingComputed - siblingExact| + |siblingExact| := htri
          _ ≤ (siblingCount : ℝ) * u * siblingAbs + siblingAbs :=
            add_le_add hsiberr hsiblingExact
          _ = (1 + (siblingCount : ℝ) * u) * siblingAbs := by ring
      have hroundOutput : |r - (pivotValue + siblingComputed)| ≤ u * |r| := by
        simpa [r, u] using fmt.round_error_to_output
          (pivotValue + siblingComputed) hsafe
      have hroundPivot : |r - (pivotValue + siblingComputed)| ≤
          |siblingComputed| := by
        have hnear := fmt.round_nearest
          (pivotValue + siblingComputed) hsafe pivotValue hpivot
        rw [abs_sub_comm] at hnear
        simpa [r] using hnear
      have hrabs : |r| ≤ (1 + a * u) * Q := by
        have htri : |r| ≤ |r + outerExact - z| + |outerExact| + |z| := by
          calc
            |r| = |(r + outerExact - z) - outerExact + z| := by ring_nf
            _ ≤ |(r + outerExact - z) - outerExact| + |z| := abs_add_le _ _
            _ ≤ (|r + outerExact - z| + |outerExact|) + |z| := by
              gcongr
              simpa only [sub_eq_add_neg, abs_neg] using
                (abs_add_le (r + outerExact - z) (-outerExact))
        calc
          |r| ≤ |r + outerExact - z| + |outerExact| + |z| := htri
          _ ≤ a * u * Q + outerAbs + |z| := by gcongr
          _ = (1 + a * u) * Q := by simp [Q]; ring
      have hroundQ : |r - (pivotValue + siblingComputed)| ≤
          u * (1 + a * u) * Q := by
        calc
          |r - (pivotValue + siblingComputed)| ≤ u * |r| := hroundOutput
          _ ≤ u * ((1 + a * u) * Q) :=
            mul_le_mul_of_nonneg_left hrabs hu0
          _ = u * (1 + a * u) * Q := by ring
      have hroundS : |r - (pivotValue + siblingComputed)| ≤
          (1 + (siblingCount : ℝ) * u) * siblingAbs :=
        le_trans hroundPivot hsibcomp
      have hroundCombined : |r - (pivotValue + siblingComputed)| ≤
          a * u * siblingAbs + (siblingCount : ℝ) * u * Q := by
        by_cases hsmall : siblingAbs ≤ u * Q
        · calc
            |r - (pivotValue + siblingComputed)| ≤
                (1 + (siblingCount : ℝ) * u) * siblingAbs := hroundS
            _ ≤ a * u * siblingAbs + (siblingCount : ℝ) * u * Q := by
              have hcoef : 1 + ((siblingCount : ℝ) - a) * u ≤
                  (siblingCount : ℝ) := by
                nlinarith [mul_nonneg (sub_nonneg.mpr hs1) (sub_nonneg.mpr hu1),
                  mul_nonneg (sub_nonneg.mpr ha1) hu0]
              have hmul := mul_le_mul_of_nonneg_left hsmall
                (mul_nonneg hs0 hu0)
              nlinarith [mul_nonneg hu0 hQ0,
                mul_nonneg (mul_nonneg ha0 hu0) hsiblingAbs]
        · have hlarge : u * Q ≤ siblingAbs := le_of_not_ge hsmall
          calc
            |r - (pivotValue + siblingComputed)| ≤
                u * (1 + a * u) * Q := hroundQ
            _ ≤ a * u * siblingAbs + (siblingCount : ℝ) * u * Q := by
              have hamul := mul_le_mul_of_nonneg_left hlarge
                (mul_nonneg ha0 hu0)
              nlinarith [mul_nonneg hu0 hQ0]
      have htotal : |pivotValue + (siblingExact + outerExact) - z| ≤
          |r + outerExact - z| +
            |siblingComputed - siblingExact| +
            |r - (pivotValue + siblingComputed)| := by
        calc
          |pivotValue + (siblingExact + outerExact) - z| =
              |(r + outerExact - z) - (siblingComputed - siblingExact) -
                (r - (pivotValue + siblingComputed))| := by
                  congr 1 <;> ring
          _ ≤ |(r + outerExact - z) - (siblingComputed - siblingExact)| +
                |r - (pivotValue + siblingComputed)| := by
              simpa only [sub_eq_add_neg, abs_neg] using
                (abs_add_le ((r + outerExact - z) -
                  (siblingComputed - siblingExact))
                  (-(r - (pivotValue + siblingComputed))))
          _ ≤ (|r + outerExact - z| +
                |siblingComputed - siblingExact|) +
                |r - (pivotValue + siblingComputed)| := by
              gcongr
              simpa only [sub_eq_add_neg, abs_neg] using
                (abs_add_le (r + outerExact - z)
                  (-(siblingComputed - siblingExact)))
      calc
        |pivotValue + (siblingExact + outerExact) - z| ≤
            |r + outerExact - z| +
              |siblingComputed - siblingExact| +
              |r - (pivotValue + siblingComputed)| := htotal
        _ ≤ a * u * Q +
              (siblingCount : ℝ) * u * siblingAbs +
              (a * u * siblingAbs + (siblingCount : ℝ) * u * Q) := by
            gcongr
        _ = ((((outerCount + siblingCount) - 1 + q : ℕ) : ℝ) * u) *
              (siblingAbs + outerAbs + |z|) := by
            have hnat : (outerCount + siblingCount) - 1 + q =
                (outerCount - 1 + q) + siblingCount := by omega
            rw [hnat, Nat.cast_add]
            simp only [a, Q]
            ring

private lemma p05_lemma41_run_result {m : ℕ} (run : P05Lemma41Run m) :
    run.format.representable run.yHat ∧
    |run.c - ((∑ i : Fin m, run.a i * run.b i) + run.bK * run.yHat)| ≤
      ((m + 1 : ℕ) : ℝ) * run.format.unitRoundoff *
        ((∑ i : Fin m, |run.a i * run.b i|) + |run.bK| * |run.yHat|) := by
  have htrace := p05_protected_trace_basic run.protected_sum_trace
  rcases htrace with ⟨hcount, hsumNonneg, hsumExact, hnumRep⟩
  by_cases hunit : run.bK = 1
  · have hy : run.yHat = run.numerator := run.no_division_when_unit hunit
    refine ⟨hy.symm ▸ hnumRep, ?_⟩
    have hext : |run.numerator - run.bK * run.yHat| ≤
        run.format.unitRoundoff * |run.bK * run.yHat| := by
      rw [hunit, one_mul, hy, sub_self, abs_zero]
      exact mul_nonneg run.format.unitRoundoff_nonneg (abs_nonneg run.numerator)
    have hbound := p05_protected_trace_bound (z := run.bK * run.yHat)
      run.protected_sum_trace 1
      (by omega) (by simpa using hext)
    have hrhs : ((m + 1 : ℕ) : ℝ) * run.format.unitRoundoff *
          ((∑ i : Fin m, |run.a i * run.b i|) + |run.bK| * |run.yHat|) =
        ((((m + 1) - 1 + 1 : ℕ) : ℝ) * run.format.unitRoundoff) *
          ((∑ i : Fin m, |run.a i * run.b i|) + |run.bK * run.yHat|) := by
      simp [abs_mul, mul_assoc]
    rw [hrhs]
    convert hbound using 1 <;> ring
  · have hsafe := run.division_safe hunit
    have hy : run.yHat = run.format.round (run.numerator / run.bK) :=
      run.rounded_division hunit
    have hyRep : run.format.representable run.yHat := by
      rw [hy]
      exact run.format.round_representable _ hsafe
    refine ⟨hyRep, ?_⟩
    have hround := run.format.round_error_to_output
      (run.numerator / run.bK) hsafe
    have heq : run.numerator - run.bK * run.yHat =
        -run.bK * (run.yHat - run.numerator / run.bK) := by
      field_simp [run.bK_nonzero]
      <;> ring
    have hext : |run.numerator - run.bK * run.yHat| ≤
        run.format.unitRoundoff * |run.bK * run.yHat| := by
      rw [heq, abs_mul, abs_neg, abs_mul]
      rw [← hy] at hround
      have hscaled := mul_le_mul_of_nonneg_left hround (abs_nonneg run.bK)
      simpa [mul_assoc, mul_left_comm, mul_comm] using hscaled
    have hbound := p05_protected_trace_bound (z := run.bK * run.yHat)
      run.protected_sum_trace 1
      (by omega) (by simpa using hext)
    have hrhs : ((m + 1 : ℕ) : ℝ) * run.format.unitRoundoff *
          ((∑ i : Fin m, |run.a i * run.b i|) + |run.bK| * |run.yHat|) =
        ((((m + 1) - 1 + 1 : ℕ) : ℝ) * run.format.unitRoundoff) *
          ((∑ i : Fin m, |run.a i * run.b i|) + |run.bK * run.yHat|) := by
      simp [abs_mul, mul_assoc]
    rw [hrhs]
    convert hbound using 1 <;> ring

private lemma p05_lemma43_run_result {m : ℕ} (run : P05Lemma43Run m) :
    run.format.representable run.yHat ∧
    |run.c - ((∑ i : Fin m, run.a i * run.b i) + run.yHat ^ 2)| ≤
      ((m + 2 : ℕ) : ℝ) * run.format.unitRoundoff *
        ((∑ i : Fin m, |run.a i * run.b i|) + |run.yHat| * |run.yHat|) := by
  have htrace := p05_protected_trace_basic run.protected_sum_trace
  rcases htrace with ⟨hcount, hsumNonneg, hsumExact, hnumRep⟩
  have hy : run.yHat = run.format.round (Real.sqrt run.numerator) :=
    run.rounded_sqrt
  have hyRep : run.format.representable run.yHat := by
    rw [hy]
    exact run.format.round_representable _ run.sqrt_safe
  refine ⟨hyRep, ?_⟩
  have hsquare := run.format.sqrt_round_square_error run.numerator
    run.numerator_nonneg hnumRep run.sqrt_safe
  rw [← hy] at hsquare
  have hext : |run.numerator - run.yHat ^ 2| ≤
      (2 : ℝ) * run.format.unitRoundoff * |run.yHat ^ 2| := by
    simpa [abs_sub_comm] using hsquare
  have hbound := p05_protected_trace_bound run.protected_sum_trace 2
    (by omega) hext
  have hrhs : ((m + 2 : ℕ) : ℝ) * run.format.unitRoundoff *
        ((∑ i : Fin m, |run.a i * run.b i|) + |run.yHat| * |run.yHat|) =
      (((m + 1 - 1 + 2 : ℕ) : ℝ) * run.format.unitRoundoff) *
        ((∑ i : Fin m, |run.a i * run.b i|) + |run.yHat ^ 2|) := by
    simp [abs_mul, abs_pow, pow_two, mul_assoc]
  rw [hrhs]
  convert hbound using 1 <;> ring

private lemma p05_off_diagonal_result {n : ℕ} (run : P05CholeskyRun n)
    (i j : Fin n) (hij : i.val < j.val) :
    run.format.representable (run.RHat i j) ∧
    |run.A i j - p05CholeskyThroughDot run.RHat i j| ≤
      ((i.val + 1 : ℕ) : ℝ) * run.format.unitRoundoff *
        p05CholeskyThroughAbsDot run.RHat i j := by
  let entry := run.off_diagonal_entry i j hij
  have h := p05_lemma41_run_result entry.execution
  rcases h with ⟨hrep, hbound⟩
  constructor
  · simpa only [entry.format_eq, entry.computed_output_eq] using hrep
  · simpa only [p05CholeskyThroughDot, p05CholeskyPrefixDot,
      p05CholeskyThroughAbsDot, p05CholeskyPrefixAbsDot,
      entry.protected_input_eq, entry.denominator_eq,
      entry.computed_output_eq, entry.left_input_eq, entry.right_input_eq,
      entry.format_eq, abs_mul] using hbound

private lemma p05_diagonal_result {n : ℕ} (run : P05CholeskyRun n)
    (j : Fin n) :
    run.format.representable (run.RHat j j) ∧
    |run.A j j - p05CholeskyThroughDot run.RHat j j| ≤
      ((j.val + 2 : ℕ) : ℝ) * run.format.unitRoundoff *
        p05CholeskyThroughAbsDot run.RHat j j := by
  let entry := run.diagonal_entry j
  have h := p05_lemma43_run_result entry.execution
  rcases h with ⟨hrep, hbound⟩
  constructor
  · simpa only [entry.format_eq, entry.computed_output_eq] using hrep
  · simpa only [p05CholeskyThroughDot, p05CholeskyPrefixDot,
      p05CholeskyThroughAbsDot, p05CholeskyPrefixAbsDot,
      entry.protected_input_eq, entry.computed_output_eq,
      entry.left_input_eq, entry.right_input_eq, entry.format_eq,
      abs_mul, pow_two] using hbound

private lemma p05_sum_eq_prefix_add {n : ℕ} (i : Fin n) (f : Fin n → ℝ)
    (hzero : ∀ k : Fin n, i.val < k.val → f k = 0) :
    (∑ k : Fin n, f k) =
      (∑ k : Fin i.val, f (p05PrefixIndex i k)) + f i := by
  rw [← Finset.sum_filter_add_sum_filter_not Finset.univ
    (fun k : Fin n => k.val < i.val) f]
  congr 1
  · symm
    refine Finset.sum_bij
      (fun k : Fin i.val => fun _ => p05PrefixIndex i k) ?_ ?_ ?_ ?_
    · intro k hk
      simp only [Finset.mem_filter, Finset.mem_univ, true_and]
      exact k.isLt
    · intro a ha b hb hab
      apply Fin.ext
      simpa [p05PrefixIndex] using congrArg Fin.val hab
    · intro k hk
      have hki : k.val < i.val := by simpa using hk
      let a : Fin i.val := ⟨k.val, hki⟩
      refine ⟨a, by simp, ?_⟩
      exact Fin.ext rfl
    · intro k hk
      rfl
  · apply Finset.sum_eq_single i
    · intro k hk hki
      have hnot : ¬ k.val < i.val := by simpa using hk
      exact hzero k (by omega)
    · intro hi
      exfalso
      apply hi
      simp

private lemma p05_matmul_eq_through {n : ℕ} (run : P05CholeskyRun n)
    (i j : Fin n) :
    p05MatMul (p05Transpose run.RHat) run.RHat i j =
      p05CholeskyThroughDot run.RHat i j := by
  unfold p05MatMul p05Transpose p05CholeskyThroughDot
  rw [p05_sum_eq_prefix_add i]
  · rfl
  · intro k hik
    rw [run.RHat_lower_zero k i hik, zero_mul]

private lemma p05_absmatmul_eq_through {n : ℕ} (run : P05CholeskyRun n)
    (i j : Fin n) :
    p05AbsMatMul (p05Transpose run.RHat) run.RHat i j =
      p05CholeskyThroughAbsDot run.RHat i j := by
  unfold p05AbsMatMul p05Transpose p05CholeskyThroughAbsDot
  rw [p05_sum_eq_prefix_add i]
  · rfl
  · intro k hik
    rw [run.RHat_lower_zero k i hik, abs_zero, zero_mul]

private lemma p05_matmul_symmetric {n : ℕ} (R : Fin n → Fin n → ℝ)
    (i j : Fin n) :
    p05MatMul (p05Transpose R) R i j =
      p05MatMul (p05Transpose R) R j i := by
  unfold p05MatMul p05Transpose
  apply Finset.sum_congr rfl
  intro k hk
  ring

private lemma p05_absmatmul_symmetric {n : ℕ} (R : Fin n → Fin n → ℝ)
    (i j : Fin n) :
    p05AbsMatMul (p05Transpose R) R i j =
      p05AbsMatMul (p05Transpose R) R j i := by
  unfold p05AbsMatMul p05Transpose
  apply Finset.sum_congr rfl
  intro k hk
  ring

private lemma p05_absmatmul_nonneg {n : ℕ} (R : Fin n → Fin n → ℝ)
    (i j : Fin n) :
    0 ≤ p05AbsMatMul (p05Transpose R) R i j := by
  unfold p05AbsMatMul p05Transpose
  positivity

private lemma p05_factor_entry_bound {n : ℕ} (run : P05CholeskyRun n)
    (i j : Fin n) :
    |run.A i j - p05MatMul (p05Transpose run.RHat) run.RHat i j| ≤
      ((i.val + 2 : ℕ) : ℝ) * run.format.unitRoundoff *
        p05AbsMatMul (p05Transpose run.RHat) run.RHat i j := by
  by_cases hij : i.val < j.val
  · have hlocal := (p05_off_diagonal_result run i j hij).2
    rw [p05_matmul_eq_through run i j,
      p05_absmatmul_eq_through run i j]
    calc
      |run.A i j - p05CholeskyThroughDot run.RHat i j| ≤
          ((i.val + 1 : ℕ) : ℝ) * run.format.unitRoundoff *
            p05CholeskyThroughAbsDot run.RHat i j := hlocal
      _ ≤ ((i.val + 2 : ℕ) : ℝ) * run.format.unitRoundoff *
            p05CholeskyThroughAbsDot run.RHat i j := by
          have hu := run.format.unitRoundoff_nonneg
          have habs : 0 ≤ p05CholeskyThroughAbsDot run.RHat i j := by
            rw [← p05_absmatmul_eq_through run i j]
            exact p05_absmatmul_nonneg run.RHat i j
          have hcoef : ((i.val + 1 : ℕ) : ℝ) ≤ ((i.val + 2 : ℕ) : ℝ) := by
            norm_num
          exact mul_le_mul_of_nonneg_right
            (mul_le_mul_of_nonneg_right hcoef hu) habs
  · by_cases hji : j.val < i.val
    · have hlocal := (p05_off_diagonal_result run j i hji).2
      rw [run.A_symmetric i j, p05_matmul_symmetric run.RHat i j,
        p05_absmatmul_symmetric run.RHat i j]
      rw [p05_matmul_eq_through run j i,
        p05_absmatmul_eq_through run j i]
      calc
        |run.A j i - p05CholeskyThroughDot run.RHat j i| ≤
            ((j.val + 1 : ℕ) : ℝ) * run.format.unitRoundoff *
              p05CholeskyThroughAbsDot run.RHat j i := hlocal
        _ ≤ ((i.val + 2 : ℕ) : ℝ) * run.format.unitRoundoff *
              p05CholeskyThroughAbsDot run.RHat j i := by
            have hu := run.format.unitRoundoff_nonneg
            have habs : 0 ≤ p05CholeskyThroughAbsDot run.RHat j i := by
              rw [← p05_absmatmul_eq_through run j i]
              exact p05_absmatmul_nonneg run.RHat j i
            have hcoef : ((j.val + 1 : ℕ) : ℝ) ≤ ((i.val + 2 : ℕ) : ℝ) := by
              exact_mod_cast (show j.val + 1 ≤ i.val + 2 by omega)
            exact mul_le_mul_of_nonneg_right
              (mul_le_mul_of_nonneg_right hcoef hu) habs
    · have hijEq : i = j := Fin.ext (by omega)
      subst j
      simpa only [p05_matmul_eq_through run i i,
        p05_absmatmul_eq_through run i i] using
          (p05_diagonal_result run i).2

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
  refine ⟨?_, ?_, ?_, ?_⟩
  · intro i j
    by_cases hij : i.val < j.val
    · exact (p05_off_diagonal_result run i j hij).1
    · by_cases hji : j.val < i.val
      · rw [run.RHat_lower_zero i j hji]
        exact run.format.zero_representable
      · have hijEq : i = j := Fin.ext (by omega)
        subst j
        exact (p05_diagonal_result run i).1
  · intro i j hij
    exact (p05_off_diagonal_result run i j hij).2
  · intro j
    exact (p05_diagonal_result run j).2
  · let ΔA : Fin n → Fin n → ℝ := fun i j =>
      p05MatMul (p05Transpose run.RHat) run.RHat i j - run.A i j
    refine ⟨ΔA, ?_, ?_, ?_⟩
    · funext i j
      change p05MatMul (p05Transpose run.RHat) run.RHat i j =
        run.A i j +
          (p05MatMul (p05Transpose run.RHat) run.RHat i j - run.A i j)
      ring
    · intro i j
      change |p05MatMul (p05Transpose run.RHat) run.RHat i j - run.A i j| ≤
        ((i.val + 2 : ℕ) : ℝ) * run.format.unitRoundoff *
          p05AbsMatMul (p05Transpose run.RHat) run.RHat i j
      simpa only [abs_sub_comm] using p05_factor_entry_bound run i j
    · intro i j
      change |p05MatMul (p05Transpose run.RHat) run.RHat i j - run.A i j| ≤
        ((n + 1 : ℕ) : ℝ) * run.format.unitRoundoff *
          p05AbsMatMul (p05Transpose run.RHat) run.RHat i j
      have hrow := p05_factor_entry_bound run i j
      rw [abs_sub_comm]
      calc
        |run.A i j - p05MatMul (p05Transpose run.RHat) run.RHat i j| ≤
            ((i.val + 2 : ℕ) : ℝ) * run.format.unitRoundoff *
              p05AbsMatMul (p05Transpose run.RHat) run.RHat i j := hrow
        _ ≤ ((n + 1 : ℕ) : ℝ) * run.format.unitRoundoff *
              p05AbsMatMul (p05Transpose run.RHat) run.RHat i j := by
            have hcoef : ((i.val + 2 : ℕ) : ℝ) ≤ ((n + 1 : ℕ) : ℝ) := by
              exact_mod_cast (show i.val + 2 ≤ n + 1 by omega)
            exact mul_le_mul_of_nonneg_right
              (mul_le_mul_of_nonneg_right hcoef run.format.unitRoundoff_nonneg)
              (p05_absmatmul_nonneg run.RHat i j)

end HighamBench
