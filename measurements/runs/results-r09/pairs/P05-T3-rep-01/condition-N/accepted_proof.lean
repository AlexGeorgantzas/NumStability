import HighamBench.P05Definitions

namespace HighamBench

open scoped BigOperators

lemma p05ProtectedSumTrace_representable
    {fmt : P05FiniteRoundToNearestFormat} {termCount : ℕ}
    {pivotValue outsideExact outsideAbs computed : ℝ}
    (trace : P05ProtectedSumTrace fmt termCount pivotValue
      outsideExact outsideAbs computed) :
    fmt.representable computed := by
  induction trace with
  | leaf pivotValue hp => exact hp
  | merge hp hs hsa hse hcr hceb hsafe outer ih => exact ih

lemma p05ProtectedSumTrace_abs_properties
    {fmt : P05FiniteRoundToNearestFormat} {termCount : ℕ}
    {pivotValue outsideExact outsideAbs computed : ℝ}
    (trace : P05ProtectedSumTrace fmt termCount pivotValue
      outsideExact outsideAbs computed) :
    0 ≤ outsideAbs ∧ |outsideExact| ≤ outsideAbs := by
  induction trace with
  | leaf => simp
  | merge hp hs hsa hse hcr hceb hsafe outer ih =>
      constructor
      · exact add_nonneg hsa ih.1
      · calc
          |_ + _| ≤ |_| + |_| := abs_add_le _ _
          _ ≤ _ + _ := add_le_add hse ih.2

lemma p05ProtectedSumTrace_count_pos
    {fmt : P05FiniteRoundToNearestFormat} {termCount : ℕ}
    {pivotValue outsideExact outsideAbs computed : ℝ}
    (trace : P05ProtectedSumTrace fmt termCount pivotValue
      outsideExact outsideAbs computed) :
    0 < termCount := by
  induction trace with
  | leaf => simp
  | merge hp hs hsa hse hcr hceb hsafe outer ih => omega

lemma p05_two_upper_bounds
    {u C s V a e : ℝ}
    (hu0 : 0 ≤ u) (hu1 : u ≤ 1)
    (hC : 1 ≤ C) (hs : 1 ≤ s)
    (hV : 0 ≤ V) (ha : 0 ≤ a)
    (heV : e ≤ u * (1 + C * u) * V)
    (hea : e ≤ (1 + s * u) * a) :
    e ≤ s * u * V + C * u * a := by
  rcases le_total (u * V) a with huv | hav
  · have hus : u * V ≤ s * u * V := by
      have : 0 ≤ (s - 1) * u * V :=
        mul_nonneg (mul_nonneg (sub_nonneg.mpr hs) hu0) hV
      nlinarith
    have hcu : C * u * (u * V) ≤ C * u * a := by
      exact mul_le_mul_of_nonneg_left huv
        (mul_nonneg (le_trans (by norm_num) hC) hu0)
    calc
      e ≤ u * (1 + C * u) * V := heV
      _ = u * V + C * u * (u * V) := by ring
      _ ≤ s * u * V + C * u * a := add_le_add hus hcu
  · let q : ℝ := 1 + (s - 1) * u
    have hq0 : 0 ≤ q := by
      dsimp [q]
      exact add_nonneg (by norm_num) (mul_nonneg (sub_nonneg.mpr hs) hu0)
    have hqs : q ≤ s := by
      have : 0 ≤ (s - 1) * (1 - u) :=
        mul_nonneg (sub_nonneg.mpr hs) (sub_nonneg.mpr hu1)
      dsimp [q]
      nlinarith
    have hqa : q * a ≤ q * (u * V) :=
      mul_le_mul_of_nonneg_left hav hq0
    have hqV : q * (u * V) ≤ s * u * V := by
      have := mul_le_mul_of_nonneg_right hqs (mul_nonneg hu0 hV)
      nlinarith
    have hua : u * a ≤ C * u * a := by
      have := mul_le_mul_of_nonneg_right hC (mul_nonneg hu0 ha)
      nlinarith
    calc
      e ≤ (1 + s * u) * a := hea
      _ = q * a + u * a := by dsimp [q]; ring
      _ ≤ s * u * V + C * u * a :=
        add_le_add (hqa.trans hqV) hua

lemma p05ProtectedSumTrace_terminal_error
    {fmt : P05FiniteRoundToNearestFormat} {termCount : ℕ}
    {pivotValue outsideExact outsideAbs computed terminal d : ℝ}
    (trace : P05ProtectedSumTrace fmt termCount pivotValue
      outsideExact outsideAbs computed)
    (hd : 1 ≤ d)
    (hterminal : |computed - terminal| ≤
      d * fmt.unitRoundoff * |terminal|) :
    |terminal - (pivotValue + outsideExact)| ≤
      ((termCount : ℝ) + d - 1) * fmt.unitRoundoff *
        (|terminal| + outsideAbs) := by
  induction trace generalizing terminal d with
  | leaf pivotValue hp =>
      simpa [abs_sub_comm, mul_assoc] using hterminal
  | @merge outerCount siblingCount pivotValue siblingExact siblingAbs
      siblingComputed outerExact outerAbs computed hp hs hsa hse hcr
      hceb hsafe outer ih =>
      let u := fmt.unitRoundoff
      let rounded := fmt.round (pivotValue + siblingComputed)
      let V := |terminal| + outerAbs
      let C := (outerCount : ℝ) + d - 1
      let s := (siblingCount : ℝ)
      have hu0 : 0 ≤ u := fmt.unitRoundoff_nonneg
      have hu1 : u ≤ 1 := le_trans fmt.unitRoundoff_le_half (by norm_num)
      have houterProps := p05ProtectedSumTrace_abs_properties outer
      have houterCount := p05ProtectedSumTrace_count_pos outer
      have hV : 0 ≤ V := add_nonneg (abs_nonneg _) houterProps.1
      have hC : 1 ≤ C := by
        have hoc : (1 : ℝ) ≤ (outerCount : ℝ) := by
          exact_mod_cast (show 1 ≤ outerCount from houterCount)
        dsimp [C]
        linarith
      have hsreal : 1 ≤ s := by
        dsimp [s]
        exact_mod_cast hs
      have houter := ih hd hterminal
      have hroundOutput :
          |rounded - (pivotValue + siblingComputed)| ≤ u * |rounded| := by
        exact fmt.round_error_to_output _ hsafe
      have hroundNearest :
          |rounded - (pivotValue + siblingComputed)| ≤
            |siblingComputed| := by
        have hn := fmt.round_nearest _ hsafe pivotValue hp
        rw [abs_sub_comm] at hn
        simpa [rounded, abs_sub_comm, add_sub_cancel_left] using hn
      have hrounded : |rounded| ≤ V +
          |terminal - (rounded + outerExact)| := by
        have ht : rounded = terminal - outerExact -
            (terminal - (rounded + outerExact)) := by ring
        calc
          |rounded| = |terminal - outerExact -
              (terminal - (rounded + outerExact))| := congrArg abs ht
          _ ≤ |terminal - outerExact| +
              |terminal - (rounded + outerExact)| := abs_sub _ _
          _ ≤ (|terminal| + |outerExact|) +
              |terminal - (rounded + outerExact)| := by
                exact add_le_add (abs_sub terminal outerExact) le_rfl
          _ ≤ V + |terminal - (rounded + outerExact)| := by
                exact add_le_add (add_le_add le_rfl houterProps.2) le_rfl
      have hroundV :
          |rounded - (pivotValue + siblingComputed)| ≤
            u * (1 + C * u) * V := by
        calc
          _ ≤ u * |rounded| := hroundOutput
          _ ≤ u * (V + |terminal - (rounded + outerExact)|) := by
            gcongr
          _ ≤ u * (V + C * u * V) := by
            gcongr
          _ = u * (1 + C * u) * V := by ring
      have hsiblingComputed :
          |siblingComputed| ≤ (1 + s * u) * siblingAbs := by
        calc
          |siblingComputed| ≤
              |siblingExact| + |siblingComputed - siblingExact| := by
                have := abs_add_le (siblingComputed - siblingExact) siblingExact
                simpa [sub_add_cancel, add_comm] using this
          _ ≤ siblingAbs + s * u * siblingAbs := by
                exact add_le_add hse (by simpa [s, u] using hceb)
          _ = (1 + s * u) * siblingAbs := by ring
      have hroundCombined :
          |rounded - (pivotValue + siblingComputed)| ≤
            s * u * V + C * u * siblingAbs :=
        p05_two_upper_bounds hu0 hu1 hC hsreal hV hsa hroundV
          (hroundNearest.trans hsiblingComputed)
      calc
        |terminal - (pivotValue + (siblingExact + outerExact))| =
            |(terminal - (rounded + outerExact)) +
              (rounded - (pivotValue + siblingComputed)) +
              (siblingComputed - siblingExact)| := by ring_nf
        _ ≤ |terminal - (rounded + outerExact)| +
              |rounded - (pivotValue + siblingComputed)| +
              |siblingComputed - siblingExact| := by
                exact (abs_add_three _ _ _)
        _ ≤ C * u * V + (s * u * V + C * u * siblingAbs) +
              s * u * siblingAbs := by
                gcongr
        _ = (((outerCount + siblingCount : ℕ) : ℝ) + d - 1) * u *
              (|terminal| + (siblingAbs + outerAbs)) := by
                dsimp [C, s, V]
                push_cast
                ring

lemma p05Lemma41Run_representable_and_error {m : ℕ}
    (exec : P05Lemma41Run m) :
    exec.format.representable exec.yHat ∧
    |exec.c - ((∑ i : Fin m, exec.a i * exec.b i) +
        exec.bK * exec.yHat)| ≤
      (((m + 1 : ℕ) : ℝ) * exec.format.unitRoundoff) *
        ((∑ i : Fin m, |exec.a i| * |exec.b i|) +
          |exec.bK| * |exec.yHat|) := by
  have hnumrep :=
    p05ProtectedSumTrace_representable exec.protected_sum_trace
  have hyrep : exec.format.representable exec.yHat := by
    by_cases hb : exec.bK = 1
    · rw [exec.no_division_when_unit hb]
      exact hnumrep
    · rw [exec.rounded_division hb]
      exact exec.format.round_representable _ (exec.division_safe hb)
  constructor
  · exact hyrep
  · have hterminal :
        |exec.numerator - exec.bK * exec.yHat| ≤
          1 * exec.format.unitRoundoff * |exec.bK * exec.yHat| := by
      by_cases hb : exec.bK = 1
      · rw [exec.no_division_when_unit hb, hb]
        simpa using mul_nonneg exec.format.unitRoundoff_nonneg
          (abs_nonneg exec.numerator)
      · have hr := exec.format.round_error_to_output
            (exec.numerator / exec.bK) (exec.division_safe hb)
        rw [← exec.rounded_division hb] at hr
        have halg : exec.numerator - exec.bK * exec.yHat =
            -exec.bK * (exec.yHat - exec.numerator / exec.bK) := by
          field_simp [exec.bK_nonzero]
          <;> ring
        rw [halg, abs_mul, abs_neg, abs_mul]
        calc
          |exec.bK| * |exec.yHat - exec.numerator / exec.bK| ≤
              |exec.bK| *
                (exec.format.unitRoundoff * |exec.yHat|) := by
                  gcongr
          _ = 1 * exec.format.unitRoundoff *
              (|exec.bK| * |exec.yHat|) := by ring
    have htrace := p05ProtectedSumTrace_terminal_error
      exec.protected_sum_trace (terminal := exec.bK * exec.yHat)
      (d := (1 : ℝ)) (by norm_num) hterminal
    calc
      |exec.c - ((∑ i : Fin m, exec.a i * exec.b i) +
          exec.bK * exec.yHat)| =
          |exec.bK * exec.yHat -
            (exec.c + -(∑ i : Fin m, exec.a i * exec.b i))| := by
              rw [show exec.c - ((∑ i : Fin m, exec.a i * exec.b i) +
                exec.bK * exec.yHat) =
                -(exec.bK * exec.yHat -
                  (exec.c + -(∑ i : Fin m, exec.a i * exec.b i))) by ring,
                abs_neg]
      _ ≤ (((m + 1 : ℕ) : ℝ) * exec.format.unitRoundoff) *
          (|exec.bK * exec.yHat| +
            ∑ i : Fin m, |exec.a i * exec.b i|) := by
              simpa using htrace
      _ = (((m + 1 : ℕ) : ℝ) * exec.format.unitRoundoff) *
          ((∑ i : Fin m, |exec.a i| * |exec.b i|) +
            |exec.bK| * |exec.yHat|) := by
              simp only [abs_mul]
              ring

lemma p05Lemma43Run_representable_and_error {m : ℕ}
    (exec : P05Lemma43Run m) :
    exec.format.representable exec.yHat ∧
    |exec.c - ((∑ i : Fin m, exec.a i * exec.b i) +
        exec.yHat * exec.yHat)| ≤
      (((m + 2 : ℕ) : ℝ) * exec.format.unitRoundoff) *
        ((∑ i : Fin m, |exec.a i| * |exec.b i|) +
          |exec.yHat| * |exec.yHat|) := by
  have hnumrep :=
    p05ProtectedSumTrace_representable exec.protected_sum_trace
  have hyrep : exec.format.representable exec.yHat := by
    rw [exec.rounded_sqrt]
    exact exec.format.round_representable _ exec.sqrt_safe
  constructor
  · exact hyrep
  · have hsquare := exec.format.sqrt_round_square_error exec.numerator
        exec.numerator_nonneg hnumrep exec.sqrt_safe
    rw [← exec.rounded_sqrt] at hsquare
    have hterminal :
        |exec.numerator - exec.yHat ^ 2| ≤
          2 * exec.format.unitRoundoff * |exec.yHat ^ 2| := by
      simpa [abs_sub_comm] using hsquare
    have htrace := p05ProtectedSumTrace_terminal_error
      exec.protected_sum_trace (terminal := exec.yHat ^ 2)
      (d := (2 : ℝ)) (by norm_num) hterminal
    calc
      |exec.c - ((∑ i : Fin m, exec.a i * exec.b i) +
          exec.yHat * exec.yHat)| =
          |exec.yHat ^ 2 -
            (exec.c + -(∑ i : Fin m, exec.a i * exec.b i))| := by
              rw [show exec.c - ((∑ i : Fin m, exec.a i * exec.b i) +
                exec.yHat * exec.yHat) =
                -(exec.yHat ^ 2 -
                  (exec.c + -(∑ i : Fin m, exec.a i * exec.b i))) by
                    ring,
                abs_neg]
      _ ≤ (((m + 2 : ℕ) : ℝ) * exec.format.unitRoundoff) *
          (|exec.yHat ^ 2| +
            ∑ i : Fin m, |exec.a i * exec.b i|) := by
              convert htrace using 1 <;> push_cast <;> ring
      _ = (((m + 2 : ℕ) : ℝ) * exec.format.unitRoundoff) *
          ((∑ i : Fin m, |exec.a i| * |exec.b i|) +
            |exec.yHat| * |exec.yHat|) := by
              simp only [pow_two, abs_mul]
              ring

def p05PrefixEquiv {n : ℕ} (i : Fin n) :
    Fin i.val ≃ {k : Fin n // k.val < i.val} where
  toFun k := ⟨p05PrefixIndex i k, by simp [p05PrefixIndex]⟩
  invFun k := ⟨k.1.val, k.2⟩
  left_inv k := by apply Fin.ext; rfl
  right_inv k := by apply Subtype.ext; apply Fin.ext; rfl

lemma p05_fin_sum_eq_prefix {n : ℕ} (i : Fin n) (f : Fin n → ℝ)
    (hz : ∀ k, i.val < k.val → f k = 0) :
    ∑ k : Fin n, f k =
      (∑ k : Fin i.val, f (p05PrefixIndex i k)) + f i := by
  let below : Finset (Fin n) :=
    Finset.univ.filter (fun k => k.val < i.val)
  let through : Finset (Fin n) :=
    Finset.univ.filter (fun k => k.val ≤ i.val)
  have hi : i ∈ through := by simp [through]
  have herase : through.erase i = below := by
    ext k
    simp only [through, below, Finset.mem_erase, Finset.mem_filter,
      Finset.mem_univ, true_and]
    constructor
    · rintro ⟨hne, hle⟩
      exact lt_of_le_of_ne hle (fun h => hne (Fin.ext h))
    · intro hlt
      exact ⟨fun h => by subst k; exact (lt_irrefl _ hlt), Nat.le_of_lt hlt⟩
  have hthrough : ∑ k ∈ through, f k = ∑ k : Fin n, f k := by
    apply Finset.sum_subset (by simp [through])
    intro k hk hnot
    simp only [through, Finset.mem_filter, Finset.mem_univ, true_and] at hnot
    exact hz k (Nat.lt_of_not_ge hnot)
  have hbelow : ∑ k ∈ below, f k =
      ∑ k : Fin i.val, f (p05PrefixIndex i k) := by
    calc
      ∑ k ∈ below, f k =
          ∑ k : {k : Fin n // k.val < i.val}, f k.1 := by
            apply Finset.sum_subtype
            intro k
            simp [below]
      _ = ∑ k : Fin i.val, f (p05PrefixIndex i k) := by
            symm
            exact Equiv.sum_comp (p05PrefixEquiv i) (fun k => f k.1)
  calc
    ∑ k : Fin n, f k = ∑ k ∈ through, f k := hthrough.symm
    _ = (∑ k ∈ through.erase i, f k) + f i :=
      (Finset.sum_erase_add through f hi).symm
    _ = (∑ k : Fin i.val, f (p05PrefixIndex i k)) + f i := by
      rw [herase, hbelow]

lemma p05MatMul_eq_choleskyThrough {n : ℕ}
    (R : Fin n → Fin n → ℝ)
    (hlower : ∀ i j, j.val < i.val → R i j = 0)
    (i j : Fin n) :
    p05MatMul (p05Transpose R) R i j =
      p05CholeskyThroughDot R i j := by
  unfold p05MatMul p05Transpose p05CholeskyThroughDot
    p05CholeskyPrefixDot
  apply p05_fin_sum_eq_prefix
  intro k hik
  rw [hlower k i hik, zero_mul]

lemma p05AbsMatMul_eq_choleskyThrough {n : ℕ}
    (R : Fin n → Fin n → ℝ)
    (hlower : ∀ i j, j.val < i.val → R i j = 0)
    (i j : Fin n) :
    p05AbsMatMul (p05Transpose R) R i j =
      p05CholeskyThroughAbsDot R i j := by
  unfold p05AbsMatMul p05Transpose p05CholeskyThroughAbsDot
    p05CholeskyPrefixAbsDot
  apply p05_fin_sum_eq_prefix
  intro k hik
  rw [hlower k i hik, abs_zero, zero_mul]

lemma p05MatMul_transpose_self_symmetric {n : ℕ}
    (R : Fin n → Fin n → ℝ) (i j : Fin n) :
    p05MatMul (p05Transpose R) R i j =
      p05MatMul (p05Transpose R) R j i := by
  unfold p05MatMul p05Transpose
  apply Finset.sum_congr rfl
  intro k hk
  exact mul_comm _ _

lemma p05AbsMatMul_transpose_self_symmetric {n : ℕ}
    (R : Fin n → Fin n → ℝ) (i j : Fin n) :
    p05AbsMatMul (p05Transpose R) R i j =
      p05AbsMatMul (p05Transpose R) R j i := by
  unfold p05AbsMatMul p05Transpose
  apply Finset.sum_congr rfl
  intro k hk
  exact mul_comm _ _

lemma p05CholeskyRun_RHat_representable {n : ℕ}
    (run : P05CholeskyRun n) :
    ∀ i j, run.format.representable (run.RHat i j) := by
  intro i j
  rcases lt_trichotomy i.val j.val with hij | hij | hij
  · let entry := run.off_diagonal_entry i j hij
    have h := (p05Lemma41Run_representable_and_error entry.execution).1
    simpa only [entry.format_eq, entry.computed_output_eq] using h
  · have heq : i = j := Fin.ext hij
    subst j
    let entry := run.diagonal_entry i
    have h := (p05Lemma43Run_representable_and_error entry.execution).1
    simpa only [entry.format_eq, entry.computed_output_eq] using h
  · rw [run.RHat_lower_zero i j hij]
    exact run.format.zero_representable

lemma p05CholeskyRun_off_diagonal_error {n : ℕ}
    (run : P05CholeskyRun n) (i j : Fin n) (hij : i.val < j.val) :
    |run.A i j - p05CholeskyThroughDot run.RHat i j| ≤
      ((i.val + 1 : ℕ) : ℝ) * run.format.unitRoundoff *
        p05CholeskyThroughAbsDot run.RHat i j := by
  let entry := run.off_diagonal_entry i j hij
  have h := (p05Lemma41Run_representable_and_error entry.execution).2
  simp_rw [entry.left_input_eq, entry.right_input_eq] at h
  simpa only [entry.format_eq, entry.denominator_eq, entry.protected_input_eq,
    entry.computed_output_eq, p05CholeskyThroughDot,
    p05CholeskyThroughAbsDot, p05CholeskyPrefixDot,
    p05CholeskyPrefixAbsDot, abs_mul, mul_assoc] using h

lemma p05CholeskyRun_diagonal_error {n : ℕ}
    (run : P05CholeskyRun n) (j : Fin n) :
    |run.A j j - p05CholeskyThroughDot run.RHat j j| ≤
      ((j.val + 2 : ℕ) : ℝ) * run.format.unitRoundoff *
        p05CholeskyThroughAbsDot run.RHat j j := by
  let entry := run.diagonal_entry j
  have h := (p05Lemma43Run_representable_and_error entry.execution).2
  simp_rw [entry.left_input_eq, entry.right_input_eq] at h
  simpa only [entry.format_eq, entry.protected_input_eq,
    entry.computed_output_eq, p05CholeskyThroughDot,
    p05CholeskyThroughAbsDot, p05CholeskyPrefixDot,
    p05CholeskyPrefixAbsDot, abs_mul, mul_assoc] using h

lemma p05AbsMatMul_nonneg {n : ℕ}
    (A B : Fin n → Fin n → ℝ) (i j : Fin n) :
    0 ≤ p05AbsMatMul A B i j := by
  unfold p05AbsMatMul
  exact Finset.sum_nonneg fun k hk =>
    mul_nonneg (abs_nonneg _) (abs_nonneg _)

lemma p05CholeskyRun_residual_bound {n : ℕ}
    (run : P05CholeskyRun n) (i j : Fin n) :
    |p05MatMul (p05Transpose run.RHat) run.RHat i j - run.A i j| ≤
      ((i.val + 2 : ℕ) : ℝ) * run.format.unitRoundoff *
        p05AbsMatMul (p05Transpose run.RHat) run.RHat i j := by
  let M := p05MatMul (p05Transpose run.RHat) run.RHat
  let Mabs := p05AbsMatMul (p05Transpose run.RHat) run.RHat
  have hu := run.format.unitRoundoff_nonneg
  have habs : ∀ a b, 0 ≤ Mabs a b :=
    fun a b => p05AbsMatMul_nonneg _ _ a b
  rcases lt_trichotomy i.val j.val with hij | hij | hij
  · have h := p05CholeskyRun_off_diagonal_error run i j hij
    have hfull : |M i j - run.A i j| ≤
        ((i.val + 1 : ℕ) : ℝ) * run.format.unitRoundoff * Mabs i j := by
      dsimp only [M, Mabs]
      rw [p05MatMul_eq_choleskyThrough run.RHat run.RHat_lower_zero,
        abs_sub_comm,
        p05AbsMatMul_eq_choleskyThrough run.RHat run.RHat_lower_zero]
      exact h
    calc
      |p05MatMul (p05Transpose run.RHat) run.RHat i j - run.A i j| =
          |M i j - run.A i j| := rfl
      _ ≤ ((i.val + 1 : ℕ) : ℝ) * run.format.unitRoundoff * Mabs i j :=
        hfull
      _ ≤ ((i.val + 2 : ℕ) : ℝ) * run.format.unitRoundoff * Mabs i j := by
        have hc : (((i.val + 1 : ℕ) : ℝ)) ≤
            ((i.val + 2 : ℕ) : ℝ) := by norm_num
        exact mul_le_mul_of_nonneg_right
          (mul_le_mul_of_nonneg_right hc hu) (habs i j)
  · have heq : i = j := Fin.ext hij
    subst j
    have h := p05CholeskyRun_diagonal_error run i
    rw [p05MatMul_eq_choleskyThrough run.RHat run.RHat_lower_zero,
      abs_sub_comm,
      p05AbsMatMul_eq_choleskyThrough run.RHat run.RHat_lower_zero]
    exact h
  · have h := p05CholeskyRun_off_diagonal_error run j i hij
    have hfull : |M j i - run.A j i| ≤
        ((j.val + 1 : ℕ) : ℝ) * run.format.unitRoundoff * Mabs j i := by
      dsimp only [M, Mabs]
      rw [p05MatMul_eq_choleskyThrough run.RHat run.RHat_lower_zero,
        abs_sub_comm,
        p05AbsMatMul_eq_choleskyThrough run.RHat run.RHat_lower_zero]
      exact h
    have hc : (((j.val + 1 : ℕ) : ℝ)) ≤
        ((i.val + 2 : ℕ) : ℝ) := by
      exact_mod_cast (show j.val + 1 ≤ i.val + 2 by omega)
    calc
      |p05MatMul (p05Transpose run.RHat) run.RHat i j - run.A i j| =
          |M i j - run.A i j| := rfl
      _ = |M j i - run.A j i| := by
        dsimp only [M]
        rw [p05MatMul_transpose_self_symmetric run.RHat i j,
          run.A_symmetric i j]
      _ ≤ ((j.val + 1 : ℕ) : ℝ) * run.format.unitRoundoff * Mabs j i :=
        hfull
      _ = ((j.val + 1 : ℕ) : ℝ) * run.format.unitRoundoff * Mabs i j := by
        dsimp only [Mabs]
        rw [p05AbsMatMul_transpose_self_symmetric run.RHat j i]
      _ ≤ ((i.val + 2 : ℕ) : ℝ) * run.format.unitRoundoff * Mabs i j := by
        exact mul_le_mul_of_nonneg_right
          (mul_le_mul_of_nonneg_right hc hu) (habs i j)

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
  refine ⟨p05CholeskyRun_RHat_representable run,
    p05CholeskyRun_off_diagonal_error run,
    p05CholeskyRun_diagonal_error run, ?_⟩
  let ΔA : Fin n → Fin n → ℝ := fun i j =>
    p05MatMul (p05Transpose run.RHat) run.RHat i j - run.A i j
  refine ⟨ΔA, ?_, ?_, ?_⟩
  · funext i j
    dsimp [ΔA]
    ring
  · intro i j
    exact p05CholeskyRun_residual_bound run i j
  · intro i j
    have h := p05CholeskyRun_residual_bound run i j
    have hc : (((i.val + 2 : ℕ) : ℝ)) ≤ ((n + 1 : ℕ) : ℝ) := by
      exact_mod_cast (show i.val + 2 ≤ n + 1 by omega)
    exact h.trans (mul_le_mul_of_nonneg_right
      (mul_le_mul_of_nonneg_right hc run.format.unitRoundoff_nonneg)
      (p05AbsMatMul_nonneg _ _ i j))

end HighamBench
