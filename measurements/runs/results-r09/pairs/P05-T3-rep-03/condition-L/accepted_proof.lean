import HighamBench.P05Definitions

namespace HighamBench

open scoped BigOperators

private lemma p05_min_bound
    {u a b x y z : ℝ}
    (hu0 : 0 ≤ u) (hu : u ≤ 1 / 2)
    (ha : 1 ≤ a) (hb : 1 ≤ b)
    (hx : 0 ≤ x) (hy : 0 ≤ y) (hz : 0 ≤ z)
    (hux : z ≤ u * (1 + a * u) * x)
    (hby : z ≤ (1 + b * u) * y) :
    z ≤ b * u * x + a * u * y := by
  have ha0 : 0 ≤ a := le_trans (by norm_num) ha
  have hb0 : 0 ≤ b := le_trans (by norm_num) hb
  by_cases hu_zero : u = 0
  · subst u
    simp at hux ⊢
    linarith
  have hu_pos : 0 < u := lt_of_le_of_ne hu0 (Ne.symm hu_zero)
  have hu1 : u ≤ 1 := by linarith
  have hD0 : 0 ≤ 1 + b * u := by positivity
  have hcoeff :
      (1 + a * u) * (1 + b * u) ≤
        b * (1 + b * u) + a * u * (1 + a * u) := by
    by_cases hba : b ≤ a
    · have hba0 : 0 ≤ a - b := sub_nonneg.mpr hba
      have hb10 : 0 ≤ b - 1 := sub_nonneg.mpr hb
      have h1 := mul_nonneg hb10 hD0
      have h2 := mul_nonneg (mul_nonneg ha0 hba0) (sq_nonneg u)
      nlinarith
    · have hab : a ≤ b := le_of_lt (lt_of_not_ge hba)
      have hd0 : 0 ≤ b - a := sub_nonneg.mpr hab
      have hdle : b - a ≤ b - 1 := by linarith
      have hau : a * u ≤ b := by
        have := mul_le_mul_of_nonneg_left hu1 ha0
        nlinarith
      have hleft := mul_le_mul_of_nonneg_left hdle (mul_nonneg ha0 (sq_nonneg u))
      have hright := mul_le_mul_of_nonneg_left hau
        (mul_nonneg (sub_nonneg.mpr hb) hu0)
      have hdom : a * (b - a) * u ^ 2 ≤ b * (b - 1) * u := by
        nlinarith
      nlinarith
  have hA : 0 < u * (1 + a * u) := by positivity
  have hD : 0 < 1 + b * u := by positivity
  have h1 := mul_le_mul_of_nonneg_left hux (mul_nonneg hb0 (le_of_lt hD))
  have h2 := mul_le_mul_of_nonneg_left hby
    (mul_nonneg (mul_nonneg ha0 hu0) (by positivity : 0 ≤ 1 + a * u))
  have hzcoeff := mul_le_mul_of_nonneg_right hcoeff hz
  have hprod :
      (u * (1 + a * u) * (1 + b * u)) * z ≤
        (u * (1 + a * u) * (1 + b * u)) *
          (b * u * x + a * u * y) := by
    nlinarith
  exact le_of_mul_le_mul_left (by simpa [mul_assoc] using hprod) (mul_pos hA hD)

private lemma p05_protected_sum_trace_properties
    (fmt : P05FiniteRoundToNearestFormat)
    {termCount : ℕ} {pivotValue outsideExact outsideAbs computed : ℝ}
    (trace : P05ProtectedSumTrace fmt termCount pivotValue
      outsideExact outsideAbs computed) :
    fmt.representable computed ∧
      0 < termCount ∧
      0 ≤ outsideAbs ∧
      |outsideExact| ≤ outsideAbs ∧
      ∀ (q result : ℝ), 1 ≤ q →
        |result - computed| ≤ q * fmt.unitRoundoff * |result| →
        |result - (pivotValue + outsideExact)| ≤
          ((termCount : ℝ) + q - 1) * fmt.unitRoundoff *
            (|result| + outsideAbs) := by
  induction trace with
  | leaf pivotValue hpivot =>
      refine ⟨hpivot, by omega, by norm_num, by norm_num, ?_⟩
      intro q result hq hresult
      convert hresult using 1 <;> norm_num <;> ring
  | @merge outerCount siblingCount pivotValue siblingExact siblingAbs
      siblingComputed outerExact outerAbs computed hpivot hsibling_pos
      hsibling_abs hsibling_exact hsibling_repr hsibling_error hsafe outer ih =>
      rcases ih with ⟨hcomputed_repr, houter_pos, houter_abs,
        houter_exact, houter_final⟩
      have hu0 : 0 ≤ fmt.unitRoundoff := fmt.unitRoundoff_nonneg
      have hu_half : fmt.unitRoundoff ≤ 1 / 2 := fmt.unitRoundoff_le_half
      let rounded := fmt.round (pivotValue + siblingComputed)
      have hrounded_error :
          |rounded - (pivotValue + siblingComputed)| ≤
            fmt.unitRoundoff * |rounded| := by
        simpa [rounded] using
          fmt.round_error_to_output (pivotValue + siblingComputed) hsafe
      have hrounded_nearest :
          |rounded - (pivotValue + siblingComputed)| ≤ |siblingComputed| := by
        have h := fmt.round_nearest (pivotValue + siblingComputed) hsafe
          pivotValue hpivot
        simpa [rounded, abs_sub_comm] using h
      have hsibling_computed_abs :
          |siblingComputed| ≤
            (1 + (siblingCount : ℝ) * fmt.unitRoundoff) * siblingAbs := by
        calc
          |siblingComputed| =
              |(siblingComputed - siblingExact) + siblingExact| := by
                congr 1
                ring
          _ ≤ |siblingComputed - siblingExact| + |siblingExact| := abs_add_le _ _
          _ ≤ (siblingCount : ℝ) * fmt.unitRoundoff * siblingAbs +
                siblingAbs := add_le_add hsibling_error hsibling_exact
          _ = (1 + (siblingCount : ℝ) * fmt.unitRoundoff) * siblingAbs := by
                ring
      refine ⟨hcomputed_repr, by omega, add_nonneg hsibling_abs houter_abs,
        ?_, ?_⟩
      · calc
          |siblingExact + outerExact| ≤
              |siblingExact| + |outerExact| := abs_add_le _ _
          _ ≤ siblingAbs + outerAbs := add_le_add hsibling_exact houter_exact
      · intro q result hq hresult
        let effective := (outerCount : ℝ) + q - 1
        let x := |result| + outerAbs
        have heffective_one : 1 ≤ effective := by
          dsimp [effective]
          have houter_one : (1 : ℝ) ≤ (outerCount : ℝ) := by
            exact_mod_cast houter_pos
          linarith
        have hx : 0 ≤ x := by
          dsimp [x]
          positivity
        have houter_error := houter_final q result hq hresult
        have hrounded_abs : |rounded| ≤
            (1 + effective * fmt.unitRoundoff) * x := by
          have hfirst :
              |rounded| ≤ |result| +
                  |result - (rounded + outerExact)| + |outerExact| := by
            calc
              |rounded| = |(rounded + outerExact) - outerExact| := by
                congr 1
                ring
              _ ≤ |rounded + outerExact| + |outerExact| := abs_sub _ _
              _ = |result - (result - (rounded + outerExact))| +
                  |outerExact| := by
                rw [show result - (result - (rounded + outerExact)) =
                  rounded + outerExact by ring]
              _ ≤ (|result| + |result - (rounded + outerExact)|) +
                  |outerExact| := by
                have h := add_le_add_right
                  (abs_sub result (result - (rounded + outerExact))) |outerExact|
                simpa [add_assoc, add_comm, add_left_comm] using h
              _ = |result| + |result - (rounded + outerExact)| +
                  |outerExact| := by ring
          dsimp [effective, x] at houter_error ⊢
          nlinarith
        have hlocal_output :
            |rounded - (pivotValue + siblingComputed)| ≤
              fmt.unitRoundoff * (1 + effective * fmt.unitRoundoff) * x := by
          calc
            |rounded - (pivotValue + siblingComputed)| ≤
                fmt.unitRoundoff * |rounded| := hrounded_error
            _ ≤ fmt.unitRoundoff *
                ((1 + effective * fmt.unitRoundoff) * x) :=
                  mul_le_mul_of_nonneg_left hrounded_abs hu0
            _ = fmt.unitRoundoff * (1 + effective * fmt.unitRoundoff) * x := by
                  ring
        have hsibling_one : (1 : ℝ) ≤ (siblingCount : ℝ) := by
          exact_mod_cast hsibling_pos
        have hlocal :
            |rounded - (pivotValue + siblingComputed)| ≤
              (siblingCount : ℝ) * fmt.unitRoundoff * x +
                effective * fmt.unitRoundoff * siblingAbs := by
          exact p05_min_bound hu0 hu_half heffective_one hsibling_one hx
            hsibling_abs (abs_nonneg _) hlocal_output
            (hrounded_nearest.trans hsibling_computed_abs)
        have htotal :
            |result - (pivotValue + (siblingExact + outerExact))| ≤
              |result - (rounded + outerExact)| +
                |rounded - (pivotValue + siblingComputed)| +
                  |siblingComputed - siblingExact| := by
            calc
              |result - (pivotValue + (siblingExact + outerExact))| =
                  |(result - (rounded + outerExact)) +
                    (rounded - (pivotValue + siblingComputed)) +
                      (siblingComputed - siblingExact)| := by
                    congr 1
                    ring
              _ ≤ |(result - (rounded + outerExact)) +
                    (rounded - (pivotValue + siblingComputed))| +
                      |siblingComputed - siblingExact| := abs_add_le _ _
              _ ≤ (|result - (rounded + outerExact)| +
                    |rounded - (pivotValue + siblingComputed)|) +
                      |siblingComputed - siblingExact| := by
                    have h := add_le_add_right (abs_add_le
                      (result - (rounded + outerExact))
                      (rounded - (pivotValue + siblingComputed)))
                      |siblingComputed - siblingExact|
                    simpa [add_assoc, add_comm, add_left_comm] using h
              _ = |result - (rounded + outerExact)| +
                    |rounded - (pivotValue + siblingComputed)| +
                      |siblingComputed - siblingExact| := by ring
        calc
          |result - (pivotValue + (siblingExact + outerExact))| ≤
              |result - (rounded + outerExact)| +
                |rounded - (pivotValue + siblingComputed)| +
                  |siblingComputed - siblingExact| := htotal
          _ ≤ (effective * fmt.unitRoundoff * x) +
                ((siblingCount : ℝ) * fmt.unitRoundoff * x +
                  effective * fmt.unitRoundoff * siblingAbs) +
                ((siblingCount : ℝ) * fmt.unitRoundoff * siblingAbs) :=
              add_le_add (add_le_add houter_error hlocal) hsibling_error
          _ = (((outerCount + siblingCount : ℕ) : ℝ) + q - 1) *
                fmt.unitRoundoff *
                  (|result| + (siblingAbs + outerAbs)) := by
              dsimp [effective, x]
              push_cast
              ring

private lemma p05_lemma41_run_bound {m : ℕ} (exec : P05Lemma41Run m) :
    exec.format.representable exec.yHat ∧
      |exec.c - ((∑ i : Fin m, exec.a i * exec.b i) +
        exec.bK * exec.yHat)| ≤
        ((m + 1 : ℕ) : ℝ) * exec.format.unitRoundoff *
          ((∑ i : Fin m, |exec.a i * exec.b i|) +
            |exec.bK * exec.yHat|) := by
  have htrace := p05_protected_sum_trace_properties exec.format
    exec.protected_sum_trace
  rcases htrace with ⟨hnumerator_repr, hcount, habs_nonneg, hexact, hfinal⟩
  have hy_repr : exec.format.representable exec.yHat := by
    by_cases hb : exec.bK = 1
    · rw [exec.no_division_when_unit hb]
      exact hnumerator_repr
    · rw [exec.rounded_division hb]
      exact exec.format.round_representable _ (exec.division_safe hb)
  refine ⟨hy_repr, ?_⟩
  have hlast :
      |exec.bK * exec.yHat - exec.numerator| ≤
        (1 : ℝ) * exec.format.unitRoundoff *
          |exec.bK * exec.yHat| := by
    by_cases hb : exec.bK = 1
    · have hy := exec.no_division_when_unit hb
      simpa [hb, hy] using
        (mul_nonneg exec.format.unitRoundoff_nonneg
          (abs_nonneg exec.numerator))
    · have hround := exec.format.round_error_to_output
          (exec.numerator / exec.bK) (exec.division_safe hb)
      rw [exec.rounded_division hb]
      calc
        |exec.bK * exec.format.round (exec.numerator / exec.bK) -
            exec.numerator| =
            |exec.bK| *
              |exec.format.round (exec.numerator / exec.bK) -
                exec.numerator / exec.bK| := by
              rw [← abs_mul]
              congr 1
              field_simp [exec.bK_nonzero]
        _ ≤ |exec.bK| *
              (exec.format.unitRoundoff *
                |exec.format.round (exec.numerator / exec.bK)|) :=
            mul_le_mul_of_nonneg_left hround (abs_nonneg _)
        _ = (1 : ℝ) * exec.format.unitRoundoff *
              |exec.bK * exec.format.round (exec.numerator / exec.bK)| := by
            rw [abs_mul]
            ring
  have h := hfinal 1 (exec.bK * exec.yHat) (by norm_num) hlast
  calc
    |exec.c - ((∑ i : Fin m, exec.a i * exec.b i) +
        exec.bK * exec.yHat)| =
        |exec.bK * exec.yHat -
          (exec.c + -(∑ i : Fin m, exec.a i * exec.b i))| := by
            rw [abs_sub_comm]
            congr 1
            ring
    _ ≤ (((m + 1 : ℕ) : ℝ) + (1 : ℝ) - 1) *
          exec.format.unitRoundoff *
            (|exec.bK * exec.yHat| +
              ∑ i : Fin m, |exec.a i * exec.b i|) := h
    _ = ((m + 1 : ℕ) : ℝ) * exec.format.unitRoundoff *
          ((∑ i : Fin m, |exec.a i * exec.b i|) +
            |exec.bK * exec.yHat|) := by ring

private lemma p05_lemma43_run_bound {m : ℕ} (exec : P05Lemma43Run m) :
    exec.format.representable exec.yHat ∧
      |exec.c - ((∑ i : Fin m, exec.a i * exec.b i) + exec.yHat ^ 2)| ≤
        ((m + 2 : ℕ) : ℝ) * exec.format.unitRoundoff *
          ((∑ i : Fin m, |exec.a i * exec.b i|) + |exec.yHat ^ 2|) := by
  have htrace := p05_protected_sum_trace_properties exec.format
    exec.protected_sum_trace
  rcases htrace with ⟨hnumerator_repr, hcount, habs_nonneg, hexact, hfinal⟩
  have hy_repr : exec.format.representable exec.yHat := by
    rw [exec.rounded_sqrt]
    exact exec.format.round_representable _ exec.sqrt_safe
  refine ⟨hy_repr, ?_⟩
  have hsqrt := exec.format.sqrt_round_square_error exec.numerator
    exec.numerator_nonneg hnumerator_repr exec.sqrt_safe
  rw [← exec.rounded_sqrt] at hsqrt
  have h := hfinal 2 (exec.yHat ^ 2) (by norm_num) hsqrt
  calc
    |exec.c - ((∑ i : Fin m, exec.a i * exec.b i) + exec.yHat ^ 2)| =
        |exec.yHat ^ 2 -
          (exec.c + -(∑ i : Fin m, exec.a i * exec.b i))| := by
            rw [abs_sub_comm]
            congr 1
            ring
    _ ≤ (((m + 1 : ℕ) : ℝ) + (2 : ℝ) - 1) *
          exec.format.unitRoundoff *
            (|exec.yHat ^ 2| +
              ∑ i : Fin m, |exec.a i * exec.b i|) := h
    _ = ((m + 2 : ℕ) : ℝ) * exec.format.unitRoundoff *
          ((∑ i : Fin m, |exec.a i * exec.b i|) + |exec.yHat ^ 2|) := by
            push_cast
            ring

private lemma p05_off_diagonal_entry_bound {n : ℕ}
    (fmt : P05FiniteRoundToNearestFormat) (A R : Fin n → Fin n → ℝ)
    (i j : Fin n) (entry : P05CholeskyOffDiagonalEntry fmt A R i j) :
    fmt.representable (R i j) ∧
      |A i j - p05CholeskyThroughDot R i j| ≤
        ((i.val + 1 : ℕ) : ℝ) * fmt.unitRoundoff *
          p05CholeskyThroughAbsDot R i j := by
  rcases p05_lemma41_run_bound entry.execution with ⟨hrep, hbound⟩
  rw [entry.format_eq, entry.computed_output_eq] at hrep
  rw [entry.format_eq, entry.protected_input_eq, entry.denominator_eq,
    entry.computed_output_eq] at hbound
  simp_rw [entry.left_input_eq, entry.right_input_eq, abs_mul] at hbound
  refine ⟨hrep, ?_⟩
  simpa [p05CholeskyThroughDot, p05CholeskyPrefixDot,
    p05CholeskyThroughAbsDot, p05CholeskyPrefixAbsDot] using hbound

private lemma p05_diagonal_entry_bound {n : ℕ}
    (fmt : P05FiniteRoundToNearestFormat) (A R : Fin n → Fin n → ℝ)
    (j : Fin n) (entry : P05CholeskyDiagonalEntry fmt A R j) :
    fmt.representable (R j j) ∧
      |A j j - p05CholeskyThroughDot R j j| ≤
        ((j.val + 2 : ℕ) : ℝ) * fmt.unitRoundoff *
          p05CholeskyThroughAbsDot R j j := by
  rcases p05_lemma43_run_bound entry.execution with ⟨hrep, hbound⟩
  rw [entry.format_eq, entry.computed_output_eq] at hrep
  rw [entry.format_eq, entry.protected_input_eq,
    entry.computed_output_eq] at hbound
  simp_rw [entry.left_input_eq, entry.right_input_eq, abs_mul] at hbound
  refine ⟨hrep, ?_⟩
  simpa [p05CholeskyThroughDot, p05CholeskyPrefixDot,
    p05CholeskyThroughAbsDot, p05CholeskyPrefixAbsDot, pow_two] using hbound

private lemma p05_upper_sum_eq_through {n : ℕ} (R : Fin n → Fin n → ℝ)
    (hupper : ∀ i j, j.val < i.val → R i j = 0) (i j : Fin n) :
    (∑ k : Fin n, R k i * R k j) = p05CholeskyThroughDot R i j := by
  classical
  let f : Fin n → ℝ := fun k ↦ R k i * R k j
  let lower : Finset (Fin n) := Finset.univ.filter (fun k ↦ k.val < i.val)
  let through : Finset (Fin n) := Finset.univ.filter (fun k ↦ k.val ≤ i.val)
  have hsupport : (∑ k ∈ through, f k) = ∑ k : Fin n, f k := by
    apply Finset.sum_subset (by simp [through])
    intro k hk hnot
    have hik : i.val < k.val := by
      simp [through] at hnot
      omega
    simp [f, hupper k i hik]
  have hthrough : through = insert i lower := by
    ext k
    simp only [through, lower, Finset.mem_filter, Finset.mem_univ, true_and,
      Finset.mem_insert]
    constructor
    · intro hki
      by_cases hki' : k.val < i.val
      · exact Or.inr hki'
      · left
        apply Fin.ext
        omega
    · rintro (rfl | hki)
      · exact le_rfl
      · omega
  let e : Fin i.val ≃ {k : Fin n // k.val < i.val} :=
    { toFun := fun k ↦ ⟨p05PrefixIndex i k, k.isLt⟩
      invFun := fun k ↦ ⟨k.val, k.property⟩
      left_inv := fun k ↦ by apply Fin.ext; rfl
      right_inv := fun k ↦ by apply Subtype.ext; rfl }
  have hlower :
      (∑ k : Fin i.val, R (p05PrefixIndex i k) i *
        R (p05PrefixIndex i k) j) = ∑ k ∈ lower, f k := by
    calc
      (∑ k : Fin i.val, R (p05PrefixIndex i k) i *
          R (p05PrefixIndex i k) j) =
          ∑ k : {k : Fin n // k.val < i.val}, f k := by
            apply Fintype.sum_equiv e
            intro k
            rfl
      _ = ∑ k ∈ Finset.univ.subtype (fun k : Fin n ↦ k.val < i.val),
          f k := by simp
      _ = ∑ k ∈ lower, f k := by
          simpa [lower] using (Finset.sum_subtype_eq_sum_filter
            (s := Finset.univ) f (p := fun k : Fin n ↦ k.val < i.val))
  have hinot : i ∉ lower := by simp [lower]
  rw [← hsupport, hthrough, Finset.sum_insert hinot, ← hlower]
  simp [f, p05CholeskyThroughDot, p05CholeskyPrefixDot, add_comm]

private lemma p05_upper_abs_sum_eq_through {n : ℕ}
    (R : Fin n → Fin n → ℝ)
    (hupper : ∀ i j, j.val < i.val → R i j = 0) (i j : Fin n) :
    (∑ k : Fin n, |R k i| * |R k j|) =
      p05CholeskyThroughAbsDot R i j := by
  let S : Fin n → Fin n → ℝ := fun i j ↦ |R i j|
  have hS : ∀ i j, j.val < i.val → S i j = 0 := by
    intro a b hab
    simp [S, hupper a b hab]
  have h := p05_upper_sum_eq_through S hS i j
  simpa [S, p05CholeskyThroughDot, p05CholeskyPrefixDot,
    p05CholeskyThroughAbsDot, p05CholeskyPrefixAbsDot] using h

private lemma p05_nat_scale_mono {a b : ℕ} {u x : ℝ}
    (hab : a ≤ b) (hu : 0 ≤ u) (hx : 0 ≤ x) :
    (a : ℝ) * u * x ≤ (b : ℝ) * u * x := by
  have hab' : (a : ℝ) ≤ (b : ℝ) := by exact_mod_cast hab
  simpa [mul_assoc] using
    (mul_le_mul_of_nonneg_right hab' (mul_nonneg hu hx))

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
  have hoff : ∀ i j, i.val < j.val →
      run.format.representable (run.RHat i j) ∧
        |run.A i j - p05CholeskyThroughDot run.RHat i j| ≤
          ((i.val + 1 : ℕ) : ℝ) * run.format.unitRoundoff *
            p05CholeskyThroughAbsDot run.RHat i j := by
    intro i j hij
    exact p05_off_diagonal_entry_bound run.format run.A run.RHat i j
      (run.off_diagonal_entry i j hij)
  have hdiag : ∀ j,
      run.format.representable (run.RHat j j) ∧
        |run.A j j - p05CholeskyThroughDot run.RHat j j| ≤
          ((j.val + 2 : ℕ) : ℝ) * run.format.unitRoundoff *
            p05CholeskyThroughAbsDot run.RHat j j := by
    intro j
    exact p05_diagonal_entry_bound run.format run.A run.RHat j
      (run.diagonal_entry j)
  have hrep : ∀ i j, run.format.representable (run.RHat i j) := by
    intro i j
    by_cases hji : j.val < i.val
    · rw [run.RHat_lower_zero i j hji]
      exact run.format.zero_representable
    by_cases hij : i.val < j.val
    · exact (hoff i j hij).1
    · have heq : i = j := Fin.ext (by omega)
      subst j
      exact (hdiag i).1
  have hmm : ∀ i j,
      p05MatMul (p05Transpose run.RHat) run.RHat i j =
        p05CholeskyThroughDot run.RHat i j := by
    intro i j
    simpa [p05MatMul, p05Transpose] using
      (p05_upper_sum_eq_through run.RHat run.RHat_lower_zero i j)
  have habsm : ∀ i j,
      p05AbsMatMul (p05Transpose run.RHat) run.RHat i j =
        p05CholeskyThroughAbsDot run.RHat i j := by
    intro i j
    simpa [p05AbsMatMul, p05Transpose] using
      (p05_upper_abs_sum_eq_through run.RHat run.RHat_lower_zero i j)
  have hmat_sym : ∀ i j,
      p05MatMul (p05Transpose run.RHat) run.RHat i j =
        p05MatMul (p05Transpose run.RHat) run.RHat j i := by
    intro i j
    simp only [p05MatMul, p05Transpose]
    apply Finset.sum_congr rfl
    intro k hk
    ring
  have habsm_sym : ∀ i j,
      p05AbsMatMul (p05Transpose run.RHat) run.RHat i j =
        p05AbsMatMul (p05Transpose run.RHat) run.RHat j i := by
    intro i j
    simp only [p05AbsMatMul, p05Transpose]
    apply Finset.sum_congr rfl
    intro k hk
    ring
  have habsm_nonneg : ∀ i j,
      0 ≤ p05AbsMatMul (p05Transpose run.RHat) run.RHat i j := by
    intro i j
    simp only [p05AbsMatMul, p05Transpose]
    positivity
  have hrow : ∀ i j,
      |p05MatMul (p05Transpose run.RHat) run.RHat i j - run.A i j| ≤
        ((i.val + 2 : ℕ) : ℝ) * run.format.unitRoundoff *
          p05AbsMatMul (p05Transpose run.RHat) run.RHat i j := by
    intro i j
    by_cases hij : i.val < j.val
    · calc
        |p05MatMul (p05Transpose run.RHat) run.RHat i j - run.A i j| =
            |run.A i j - p05CholeskyThroughDot run.RHat i j| := by
              rw [hmm i j, abs_sub_comm]
        _ ≤ ((i.val + 1 : ℕ) : ℝ) * run.format.unitRoundoff *
              p05CholeskyThroughAbsDot run.RHat i j := (hoff i j hij).2
        _ = ((i.val + 1 : ℕ) : ℝ) * run.format.unitRoundoff *
              p05AbsMatMul (p05Transpose run.RHat) run.RHat i j := by
                rw [habsm i j]
        _ ≤ ((i.val + 2 : ℕ) : ℝ) * run.format.unitRoundoff *
              p05AbsMatMul (p05Transpose run.RHat) run.RHat i j :=
            p05_nat_scale_mono (by omega) run.format.unitRoundoff_nonneg
              (habsm_nonneg i j)
    · by_cases heq : i = j
      · subst j
        calc
          |p05MatMul (p05Transpose run.RHat) run.RHat i i - run.A i i| =
              |run.A i i - p05CholeskyThroughDot run.RHat i i| := by
                rw [hmm i i, abs_sub_comm]
          _ ≤ ((i.val + 2 : ℕ) : ℝ) * run.format.unitRoundoff *
                p05CholeskyThroughAbsDot run.RHat i i := (hdiag i).2
          _ = ((i.val + 2 : ℕ) : ℝ) * run.format.unitRoundoff *
                p05AbsMatMul (p05Transpose run.RHat) run.RHat i i := by
                  rw [habsm i i]
      · have hji : j.val < i.val := by
          have hneval : i.val ≠ j.val := by
            intro h
            exact heq (Fin.ext h)
          omega
        calc
          |p05MatMul (p05Transpose run.RHat) run.RHat i j - run.A i j| =
              |p05MatMul (p05Transpose run.RHat) run.RHat j i - run.A j i| := by
                rw [hmat_sym i j, run.A_symmetric i j]
          _ = |run.A j i - p05CholeskyThroughDot run.RHat j i| := by
                rw [hmm j i, abs_sub_comm]
          _ ≤ ((j.val + 1 : ℕ) : ℝ) * run.format.unitRoundoff *
                p05CholeskyThroughAbsDot run.RHat j i := (hoff j i hji).2
          _ = ((j.val + 1 : ℕ) : ℝ) * run.format.unitRoundoff *
                p05AbsMatMul (p05Transpose run.RHat) run.RHat i j := by
                  rw [← habsm j i, habsm_sym j i]
          _ ≤ ((i.val + 2 : ℕ) : ℝ) * run.format.unitRoundoff *
                p05AbsMatMul (p05Transpose run.RHat) run.RHat i j :=
              p05_nat_scale_mono (by omega) run.format.unitRoundoff_nonneg
                (habsm_nonneg i j)
  refine ⟨hrep, fun i j hij ↦ (hoff i j hij).2, fun j ↦ (hdiag j).2, ?_⟩
  let ΔA : Fin n → Fin n → ℝ := fun i j ↦
    p05MatMul (p05Transpose run.RHat) run.RHat i j - run.A i j
  refine ⟨ΔA, ?_, ?_, ?_⟩
  · funext i j
    simp [ΔA]
  · intro i j
    exact hrow i j
  · intro i j
    have hindex : i.val + 2 ≤ n + 1 := by omega
    exact (hrow i j).trans
      (p05_nat_scale_mono hindex run.format.unitRoundoff_nonneg
        (habsm_nonneg i j))

end HighamBench
