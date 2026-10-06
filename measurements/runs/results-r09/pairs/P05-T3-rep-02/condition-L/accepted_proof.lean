import HighamBench.P05Definitions

namespace HighamBench

open scoped BigOperators

private lemma p05_blend_core
    (u : ℝ) (a s : ℕ) (hu0 : 0 ≤ u) (hu : u ≤ 1 / 2)
    (hs : 0 < s) :
    u * (1 + (a : ℝ) * u) * (1 + (s : ℝ) * u) ≤
      u * (a : ℝ) * (u * (1 + (a : ℝ) * u)) +
        u * (s : ℝ) * (1 + (s : ℝ) * u) := by
  by_cases hsa : s ≤ a
  · have ha0 : (0 : ℝ) ≤ a := by positivity
    have hs0 : (0 : ℝ) ≤ s := by positivity
    have has : (s : ℝ) ≤ a := by exact_mod_cast hsa
    have hs1 : (1 : ℝ) ≤ s := by exact_mod_cast hs
    have hD : 0 ≤ (s : ℝ) - 1 +
        (s : ℝ) * ((s : ℝ) - 1) * u +
        (a : ℝ) * ((a : ℝ) - (s : ℝ)) * (u * u) := by
      have hsm : (0 : ℝ) ≤ (s : ℝ) - 1 := by linarith
      have ham : (0 : ℝ) ≤ (a : ℝ) - (s : ℝ) := by linarith
      exact add_nonneg (add_nonneg hsm
        (mul_nonneg (mul_nonneg hs0 hsm) hu0))
        (mul_nonneg (mul_nonneg ha0 ham) (mul_nonneg hu0 hu0))
    nlinarith [mul_nonneg hu0 hD]
  · have has_nat : a < s := lt_of_not_ge hsa
    have ha0 : (0 : ℝ) ≤ a := by positivity
    have hs0 : (0 : ℝ) ≤ s := by positivity
    have hs1 : (1 : ℝ) ≤ s := by exact_mod_cast hs
    have has : (a : ℝ) ≤ (s : ℝ) - 1 := by
      have hnat : a ≤ s - 1 := by omega
      have hcast : (a : ℝ) ≤ ((s - 1 : ℕ) : ℝ) := by exact_mod_cast hnat
      rw [Nat.cast_sub (by omega : 1 ≤ s), Nat.cast_one] at hcast
      exact hcast
    have hsa0 : (0 : ℝ) ≤ (s : ℝ) - (a : ℝ) := by linarith
    have hprod :
        (a : ℝ) * ((s : ℝ) - (a : ℝ)) ≤
          (s : ℝ) * ((s : ℝ) - 1) := by
      calc
        (a : ℝ) * ((s : ℝ) - (a : ℝ)) ≤
            ((s : ℝ) - 1) * ((s : ℝ) - (a : ℝ)) :=
          mul_le_mul_of_nonneg_right has hsa0
        _ ≤ ((s : ℝ) - 1) * (s : ℝ) := by
          apply mul_le_mul_of_nonneg_left
          · linarith
          · linarith
        _ = _ := by ring
    have hu_one : u ≤ 1 := by norm_num at hu ⊢; linarith
    have huu : u * u ≤ u := by
      nlinarith [mul_nonneg hu0 (sub_nonneg.mpr hu_one)]
    have hmulprod :
        (a : ℝ) * ((s : ℝ) - (a : ℝ)) * (u * u) ≤
          (s : ℝ) * ((s : ℝ) - 1) * (u * u) :=
      mul_le_mul_of_nonneg_right hprod (mul_nonneg hu0 hu0)
    have hD : 0 ≤ (s : ℝ) - 1 +
        (s : ℝ) * ((s : ℝ) - 1) * u -
        (a : ℝ) * ((s : ℝ) - (a : ℝ)) * (u * u) := by
      have hfactor : 0 ≤ ((s : ℝ) - 1) *
          (1 + (s : ℝ) * (u - u * u)) := by
        have hu_diff : 0 ≤ u - u * u := by linarith
        have hinner : 0 ≤ 1 + (s : ℝ) * (u - u * u) :=
          add_nonneg zero_le_one (mul_nonneg hs0 hu_diff)
        exact mul_nonneg (by linarith) hinner
      nlinarith
    nlinarith [mul_nonneg hu0 hD]

private lemma p05_blend
    (u X Y z : ℝ) (a s : ℕ)
    (hu0 : 0 ≤ u) (hu : u ≤ 1 / 2) (hs : 0 < s)
    (hX : 0 ≤ X) (hY : 0 ≤ Y) (hz : 0 ≤ z)
    (hzX : z ≤ u * (1 + (a : ℝ) * u) * X)
    (hzY : z ≤ (1 + (s : ℝ) * u) * Y) :
    z ≤ u * ((a : ℝ) * Y + (s : ℝ) * X) := by
  by_cases hu_zero : u = 0
  · subst u
    simpa using hzX
  have hu_pos : 0 < u := lt_of_le_of_ne hu0 (Ne.symm hu_zero)
  let A : ℝ := u * (1 + (a : ℝ) * u)
  let B : ℝ := 1 + (s : ℝ) * u
  let C : ℝ := u * (a : ℝ)
  let D : ℝ := u * (s : ℝ)
  have hA : 0 < A := by
    dsimp [A]
    have : 0 < 1 + (a : ℝ) * u := by positivity
    positivity
  have hB : 0 < B := by
    dsimp [B]
    positivity
  have hC : 0 ≤ C := by dsimp [C]; positivity
  have hD : 0 ≤ D := by dsimp [D]; positivity
  have hcore : A * B ≤ C * A + D * B := by
    dsimp [A, B, C, D]
    exact p05_blend_core u a s hu0 hu hs
  have hleft := mul_le_mul_of_nonneg_left hzY (mul_nonneg hC (le_of_lt hA))
  have hright := mul_le_mul_of_nonneg_left hzX (mul_nonneg hD (le_of_lt hB))
  have hcorez := mul_le_mul_of_nonneg_right hcore hz
  have hAB : 0 < A * B := mul_pos hA hB
  dsimp [A, B, C, D] at hleft hright hcorez hAB
  nlinarith

private lemma p05ProtectedSumTrace_facts
    (fmt : P05FiniteRoundToNearestFormat)
    {termCount : ℕ} {pivotValue outsideExact outsideAbs computed : ℝ}
    (trace : P05ProtectedSumTrace fmt termCount pivotValue
      outsideExact outsideAbs computed) :
    0 < termCount ∧
    0 ≤ outsideAbs ∧
    |outsideExact| ≤ outsideAbs ∧
    fmt.representable computed ∧
    |computed - (pivotValue + outsideExact)| ≤
      (((termCount - 1 : ℕ) : ℝ) * fmt.unitRoundoff) *
        (outsideAbs + |computed|) := by
  induction trace with
  | leaf pivotValue hp =>
      simp [hp]
  | @merge outerCount siblingCount pivotValue siblingExact siblingAbs
      siblingComputed outerExact outerAbs computed hp hs hsabs hsexact
      hsrep hserr hsafe outer ih =>
      rcases ih with ⟨ho, hoabs, hoexact, hcrep, ih⟩
      have hu0 := fmt.unitRoundoff_nonneg
      have hu := fmt.unitRoundoff_le_half
      have hqrep : fmt.representable
          (fmt.round (pivotValue + siblingComputed)) :=
        fmt.round_representable _ hsafe
      have hlocal_output :
          |fmt.round (pivotValue + siblingComputed) -
              (pivotValue + siblingComputed)| ≤
            fmt.unitRoundoff *
              |fmt.round (pivotValue + siblingComputed)| :=
        fmt.round_error_to_output _ hsafe
      have hlocal_nearest :
          |fmt.round (pivotValue + siblingComputed) -
              (pivotValue + siblingComputed)| ≤ |siblingComputed| := by
        rw [abs_sub_comm]
        calc
          |pivotValue + siblingComputed -
              fmt.round (pivotValue + siblingComputed)|
              ≤ |pivotValue + siblingComputed - pivotValue| :=
                fmt.round_nearest _ hsafe _ hp
          _ = |siblingComputed| := by ring_nf
      have hscomp_abs :
          |siblingComputed| ≤
            (1 + (siblingCount : ℝ) * fmt.unitRoundoff) * siblingAbs := by
        calc
          |siblingComputed| =
              |(siblingComputed - siblingExact) + siblingExact| := by ring_nf
          _ ≤ |siblingComputed - siblingExact| + |siblingExact| := abs_add_le _ _
          _ ≤ (siblingCount : ℝ) * fmt.unitRoundoff * siblingAbs +
                siblingAbs := add_le_add hserr hsexact
          _ = _ := by ring
      let q := fmt.round (pivotValue + siblingComputed)
      let X := outerAbs + |computed|
      let Y := siblingAbs
      let z := |q - (pivotValue + siblingComputed)|
      have hX : 0 ≤ X := by dsimp [X]; positivity
      have hY : 0 ≤ Y := by exact hsabs
      have hz : 0 ≤ z := abs_nonneg _
      have hq_abs :
          |q| ≤
            (1 + (((outerCount - 1 : ℕ) : ℝ) * fmt.unitRoundoff)) * X := by
        have htri :
            |q| ≤ |computed - (q + outerExact)| +
                |outerExact| + |computed| := by
          calc
            |q| = |-(computed - (q + outerExact)) +
                (-outerExact) + computed| := by congr 1 <;> ring
            _ ≤ |-(computed - (q + outerExact)) + (-outerExact)| +
                  |computed| := abs_add_le _ _
            _ ≤ (|-(computed - (q + outerExact))| + |-outerExact|) +
                  |computed| := add_le_add (abs_add_le _ _) (le_refl _)
            _ = |computed - (q + outerExact)| +
                  |outerExact| + |computed| := by
                    rw [abs_sub_comm]
                    simp
        dsimp [q, X] at ih ⊢
        nlinarith
      have hzX : z ≤ fmt.unitRoundoff *
          (1 + (((outerCount - 1 : ℕ) : ℝ) * fmt.unitRoundoff)) * X := by
        calc
          z ≤ fmt.unitRoundoff * |q| := by
            simpa [z, q] using hlocal_output
          _ ≤ fmt.unitRoundoff *
              ((1 + (((outerCount - 1 : ℕ) : ℝ) * fmt.unitRoundoff)) * X) :=
            mul_le_mul_of_nonneg_left hq_abs hu0
          _ = _ := by ring
      have hzY : z ≤
          (1 + (siblingCount : ℝ) * fmt.unitRoundoff) * Y := by
        exact le_trans (by simpa [z, q] using hlocal_nearest)
          (by simpa [Y] using hscomp_abs)
      have hz_blend : z ≤ fmt.unitRoundoff *
          ((((outerCount - 1 : ℕ) : ℝ) * Y) +
            (siblingCount : ℝ) * X) :=
        p05_blend fmt.unitRoundoff X Y z (outerCount - 1) siblingCount
          hu0 hu hs hX hY hz hzX hzY
      have htotal :
          |computed - (pivotValue + (siblingExact + outerExact))| ≤
            |computed - (q + outerExact)| + z +
              |siblingComputed - siblingExact| := by
        calc
          |computed - (pivotValue + (siblingExact + outerExact))| =
              |(computed - (q + outerExact)) +
                (q - (pivotValue + siblingComputed)) +
                (siblingComputed - siblingExact)| := by
                  congr 1 <;> ring
          _ ≤ |computed - (q + outerExact)| +
                |q - (pivotValue + siblingComputed)| +
                |siblingComputed - siblingExact| := by
              calc
                _ ≤ |(computed - (q + outerExact)) +
                      (q - (pivotValue + siblingComputed))| +
                    |siblingComputed - siblingExact| := abs_add_le _ _
                _ ≤ (|computed - (q + outerExact)| +
                      |q - (pivotValue + siblingComputed)|) +
                    |siblingComputed - siblingExact| :=
                      add_le_add (abs_add_le _ _) (le_refl _)
          _ = _ := rfl
      have hcount : outerCount + siblingCount - 1 =
          (outerCount - 1) + siblingCount := by omega
      refine ⟨by omega, add_nonneg hsabs hoabs, ?_, hcrep, ?_⟩
      · exact le_trans (abs_add_le _ _)
          (add_le_add hsexact hoexact)
      · dsimp [q, X, Y, z] at ih hz_blend htotal ⊢
        rw [hcount, Nat.cast_add]
        nlinarith

private lemma p05ProtectedSumTrace_terminal_bound
    (fmt : P05FiniteRoundToNearestFormat)
    {termCount : ℕ} {pivotValue outsideExact outsideAbs computed : ℝ}
    (trace : P05ProtectedSumTrace fmt termCount pivotValue
      outsideExact outsideAbs computed)
    (target : ℝ) (terminalCount : ℕ)
    (terminal_error :
      |computed - target| ≤
        (terminalCount : ℝ) * fmt.unitRoundoff * |target|) :
    |target - (pivotValue + outsideExact)| ≤
      (((termCount - 1 + terminalCount : ℕ) : ℝ) *
        fmt.unitRoundoff) * (outsideAbs + |target|) := by
  induction trace with
  | leaf pivotValue hp =>
      simpa [abs_sub_comm] using terminal_error
  | @merge outerCount siblingCount pivotValue siblingExact siblingAbs
      siblingComputed outerExact outerAbs computed hp hs hsabs hsexact
      hsrep hserr hsafe outer ih =>
      rcases p05ProtectedSumTrace_facts fmt outer with
        ⟨ho, hoabs, hoexact, hcrep, houterSelf⟩
      have hu0 := fmt.unitRoundoff_nonneg
      have hu := fmt.unitRoundoff_le_half
      have houter := ih terminal_error
      have hlocal_output :
          |fmt.round (pivotValue + siblingComputed) -
              (pivotValue + siblingComputed)| ≤
            fmt.unitRoundoff *
              |fmt.round (pivotValue + siblingComputed)| :=
        fmt.round_error_to_output _ hsafe
      have hlocal_nearest :
          |fmt.round (pivotValue + siblingComputed) -
              (pivotValue + siblingComputed)| ≤ |siblingComputed| := by
        rw [abs_sub_comm]
        calc
          |pivotValue + siblingComputed -
              fmt.round (pivotValue + siblingComputed)|
              ≤ |pivotValue + siblingComputed - pivotValue| :=
                fmt.round_nearest _ hsafe _ hp
          _ = |siblingComputed| := by ring_nf
      have hscomp_abs :
          |siblingComputed| ≤
            (1 + (siblingCount : ℝ) * fmt.unitRoundoff) * siblingAbs := by
        calc
          |siblingComputed| =
              |(siblingComputed - siblingExact) + siblingExact| := by ring_nf
          _ ≤ |siblingComputed - siblingExact| + |siblingExact| :=
            abs_add_le _ _
          _ ≤ (siblingCount : ℝ) * fmt.unitRoundoff * siblingAbs +
                siblingAbs := add_le_add hserr hsexact
          _ = _ := by ring
      let q := fmt.round (pivotValue + siblingComputed)
      let a : ℕ := outerCount - 1 + terminalCount
      let X := outerAbs + |target|
      let Y := siblingAbs
      let z := |q - (pivotValue + siblingComputed)|
      have hX : 0 ≤ X := by dsimp [X]; positivity
      have hY : 0 ≤ Y := hsabs
      have hz : 0 ≤ z := abs_nonneg _
      have hq_abs : |q| ≤
          (1 + (a : ℝ) * fmt.unitRoundoff) * X := by
        have htri : |q| ≤
            |target - (q + outerExact)| + |outerExact| + |target| := by
          calc
            |q| = |-(target - (q + outerExact)) +
                (-outerExact) + target| := by congr 1 <;> ring
            _ ≤ |-(target - (q + outerExact)) + (-outerExact)| +
                  |target| := abs_add_le _ _
            _ ≤ (|-(target - (q + outerExact))| + |-outerExact|) +
                  |target| := add_le_add (abs_add_le _ _) (le_refl _)
            _ = |target - (q + outerExact)| +
                  |outerExact| + |target| := by simp only [abs_neg]
        dsimp [q, a, X] at houter ⊢
        nlinarith
      have hzX : z ≤ fmt.unitRoundoff *
          (1 + (a : ℝ) * fmt.unitRoundoff) * X := by
        calc
          z ≤ fmt.unitRoundoff * |q| := by
            simpa [z, q] using hlocal_output
          _ ≤ fmt.unitRoundoff *
              ((1 + (a : ℝ) * fmt.unitRoundoff) * X) :=
            mul_le_mul_of_nonneg_left hq_abs hu0
          _ = _ := by ring
      have hzY : z ≤
          (1 + (siblingCount : ℝ) * fmt.unitRoundoff) * Y :=
        le_trans (by simpa [z, q] using hlocal_nearest)
          (by simpa [Y] using hscomp_abs)
      have hz_blend : z ≤ fmt.unitRoundoff *
          ((a : ℝ) * Y + (siblingCount : ℝ) * X) :=
        p05_blend fmt.unitRoundoff X Y z a siblingCount
          hu0 hu hs hX hY hz hzX hzY
      have htotal :
          |target - (pivotValue + (siblingExact + outerExact))| ≤
            |target - (q + outerExact)| + z +
              |siblingComputed - siblingExact| := by
        calc
          |target - (pivotValue + (siblingExact + outerExact))| =
              |(target - (q + outerExact)) +
                (q - (pivotValue + siblingComputed)) +
                (siblingComputed - siblingExact)| := by
                  congr 1 <;> ring
          _ ≤ |(target - (q + outerExact)) +
                  (q - (pivotValue + siblingComputed))| +
                |siblingComputed - siblingExact| := abs_add_le _ _
          _ ≤ (|target - (q + outerExact)| +
                  |q - (pivotValue + siblingComputed)|) +
                |siblingComputed - siblingExact| :=
              add_le_add (abs_add_le _ _) (le_refl _)
          _ = _ := rfl
      have hcount : outerCount + siblingCount - 1 + terminalCount =
          (outerCount - 1 + terminalCount) + siblingCount := by omega
      dsimp [q, a, X, Y, z] at houter hz_blend htotal ⊢
      rw [hcount, Nat.cast_add]
      nlinarith

private lemma p05Lemma41_result {m : ℕ} (run : P05Lemma41Run m) :
    run.format.representable run.yHat ∧
    |run.c - ((∑ i : Fin m, run.a i * run.b i) + run.bK * run.yHat)| ≤
      ((m + 1 : ℕ) : ℝ) * run.format.unitRoundoff *
        ((∑ i : Fin m, |run.a i * run.b i|) +
          |run.bK| * |run.yHat|) := by
  rcases p05ProtectedSumTrace_facts run.format run.protected_sum_trace with
    ⟨hcount, habs, hexact, hnum_rep, hnum_bound⟩
  have hterminal :
      |run.numerator - run.bK * run.yHat| ≤
        ((1 : ℕ) : ℝ) * run.format.unitRoundoff * |run.bK * run.yHat| := by
    by_cases hb : run.bK = 1
    · have hy := run.no_division_when_unit hb
      rw [hb, hy]
      simp
      exact mul_nonneg run.format.unitRoundoff_nonneg (abs_nonneg _)
    · have hy := run.rounded_division hb
      have hsafe := run.division_safe hb
      have hround := run.format.round_error_to_output
        (run.numerator / run.bK) hsafe
      rw [hy]
      calc
        |run.numerator - run.bK *
            run.format.round (run.numerator / run.bK)| =
            |run.bK| *
              |run.numerator / run.bK -
                run.format.round (run.numerator / run.bK)| := by
          rw [← abs_mul]
          congr 1
          field_simp [run.bK_nonzero]
        _ = |run.bK| *
              |run.format.round (run.numerator / run.bK) -
                run.numerator / run.bK| := by rw [abs_sub_comm]
        _ ≤ |run.bK| *
              (run.format.unitRoundoff *
                |run.format.round (run.numerator / run.bK)|) :=
          mul_le_mul_of_nonneg_left hround (abs_nonneg _)
        _ = ((1 : ℕ) : ℝ) * run.format.unitRoundoff *
              |run.bK * run.format.round (run.numerator / run.bK)| := by
          rw [abs_mul]
          ring
  have hbound := p05ProtectedSumTrace_terminal_bound run.format
    run.protected_sum_trace (run.bK * run.yHat) 1 hterminal
  have hy_rep : run.format.representable run.yHat := by
    by_cases hb : run.bK = 1
    · rw [run.no_division_when_unit hb]
      exact hnum_rep
    · rw [run.rounded_division hb]
      exact run.format.round_representable _ (run.division_safe hb)
  refine ⟨hy_rep, ?_⟩
  calc
    |run.c - ((∑ i : Fin m, run.a i * run.b i) + run.bK * run.yHat)| =
        |run.bK * run.yHat -
          (run.c + -(∑ i : Fin m, run.a i * run.b i))| := by
            rw [show run.bK * run.yHat -
                (run.c + -(∑ i : Fin m, run.a i * run.b i)) =
              -(run.c - ((∑ i : Fin m, run.a i * run.b i) +
                run.bK * run.yHat)) by ring, abs_neg]
    _ ≤ ((m + 1 : ℕ) : ℝ) * run.format.unitRoundoff *
          ((∑ i : Fin m, |run.a i * run.b i|) +
            |run.bK * run.yHat|) := by
      simpa only [Nat.add_sub_cancel, Nat.cast_add, Nat.cast_one] using hbound
    _ = _ := by rw [abs_mul]

private lemma p05Lemma43_result {m : ℕ} (run : P05Lemma43Run m) :
    run.format.representable run.yHat ∧
    |run.c - ((∑ i : Fin m, run.a i * run.b i) + run.yHat ^ 2)| ≤
      ((m + 2 : ℕ) : ℝ) * run.format.unitRoundoff *
        ((∑ i : Fin m, |run.a i * run.b i|) + |run.yHat ^ 2|) := by
  rcases p05ProtectedSumTrace_facts run.format run.protected_sum_trace with
    ⟨hcount, habs, hexact, hnum_rep, hnum_bound⟩
  have hsqrt := run.format.sqrt_round_square_error run.numerator
    run.numerator_nonneg hnum_rep run.sqrt_safe
  have hterminal :
      |run.numerator - run.yHat ^ 2| ≤
        ((2 : ℕ) : ℝ) * run.format.unitRoundoff * |run.yHat ^ 2| := by
    rw [run.rounded_sqrt]
    simpa [abs_sub_comm] using hsqrt
  have hbound := p05ProtectedSumTrace_terminal_bound run.format
    run.protected_sum_trace (run.yHat ^ 2) 2 hterminal
  have hy_rep : run.format.representable run.yHat := by
    rw [run.rounded_sqrt]
    exact run.format.round_representable _ run.sqrt_safe
  refine ⟨hy_rep, ?_⟩
  calc
    |run.c - ((∑ i : Fin m, run.a i * run.b i) + run.yHat ^ 2)| =
        |run.yHat ^ 2 -
          (run.c + -(∑ i : Fin m, run.a i * run.b i))| := by
            rw [show run.yHat ^ 2 -
                (run.c + -(∑ i : Fin m, run.a i * run.b i)) =
              -(run.c - ((∑ i : Fin m, run.a i * run.b i) +
                run.yHat ^ 2)) by ring, abs_neg]
    _ ≤ ((m + 2 : ℕ) : ℝ) * run.format.unitRoundoff *
          ((∑ i : Fin m, |run.a i * run.b i|) + |run.yHat ^ 2|) := by
      norm_num only [Nat.cast_ofNat]
      simpa only [Nat.add_sub_cancel, Nat.cast_add, Nat.cast_ofNat] using hbound

private lemma p05_sum_prefix_eq_sum_Iio {n : ℕ}
    (f : Fin n → ℝ) (i : Fin n) :
    ∑ k : Fin i.val, f (p05PrefixIndex i k) =
      ∑ k ∈ Finset.Iio i, f k := by
  refine Finset.sum_bij (fun k _ => p05PrefixIndex i k) ?_ ?_ ?_ ?_
  · intro k hk
    simp only [Finset.mem_Iio]
    exact k.isLt
  · intro a ha b hb hab
    apply Fin.ext
    exact congrArg (fun x : Fin n => x.val) hab
  · intro b hb
    have hbi : b.val < i.val := by simpa only [Finset.mem_Iio] using hb
    refine ⟨⟨b.val, hbi⟩, Finset.mem_univ _, ?_⟩
    exact Fin.ext (by rfl)
  · intro a ha
    rfl

private lemma p05_upper_gram_eq_through {n : ℕ}
    (R : Fin n → Fin n → ℝ)
    (lower_zero : ∀ i j, j.val < i.val → R i j = 0)
    (i j : Fin n) :
    p05MatMul (p05Transpose R) R i j = p05CholeskyThroughDot R i j := by
  let f : Fin n → ℝ := fun k => R k i * R k j
  have htruncate : (∑ k : Fin n, f k) = ∑ k ∈ Finset.Iic i, f k := by
    symm
    apply Finset.sum_subset (by simp)
    intro k hk hki
    have hik : i.val < k.val := by
      have : ¬ k ≤ i := by simpa only [Finset.mem_Iic] using hki
      omega
    simp [f, lower_zero k i hik]
  have hIic : Finset.Iic i = insert i (Finset.Iio i) := by
    ext k
    simp only [Finset.mem_Iic, Finset.mem_insert, Finset.mem_Iio]
    omega
  have hprefix := p05_sum_prefix_eq_sum_Iio f i
  unfold p05MatMul p05Transpose p05CholeskyThroughDot
    p05CholeskyPrefixDot
  change (∑ k : Fin n, f k) =
    (∑ k : Fin i.val, f (p05PrefixIndex i k)) + f i
  rw [htruncate, hIic, Finset.sum_insert (by simp), ← hprefix]
  ring

private lemma p05_upper_absGram_eq_through {n : ℕ}
    (R : Fin n → Fin n → ℝ)
    (lower_zero : ∀ i j, j.val < i.val → R i j = 0)
    (i j : Fin n) :
    p05AbsMatMul (p05Transpose R) R i j =
      p05CholeskyThroughAbsDot R i j := by
  let f : Fin n → ℝ := fun k => |R k i| * |R k j|
  have htruncate : (∑ k : Fin n, f k) = ∑ k ∈ Finset.Iic i, f k := by
    symm
    apply Finset.sum_subset (by simp)
    intro k hk hki
    have hik : i.val < k.val := by
      have : ¬ k ≤ i := by simpa only [Finset.mem_Iic] using hki
      omega
    simp [f, lower_zero k i hik]
  have hIic : Finset.Iic i = insert i (Finset.Iio i) := by
    ext k
    simp only [Finset.mem_Iic, Finset.mem_insert, Finset.mem_Iio]
    omega
  have hprefix := p05_sum_prefix_eq_sum_Iio f i
  unfold p05AbsMatMul p05Transpose p05CholeskyThroughAbsDot
    p05CholeskyPrefixAbsDot
  change (∑ k : Fin n, f k) =
    (∑ k : Fin i.val, f (p05PrefixIndex i k)) + f i
  rw [htruncate, hIic, Finset.sum_insert (by simp), ← hprefix]
  ring

private lemma p05_gram_symmetric {n : ℕ}
    (R : Fin n → Fin n → ℝ) (i j : Fin n) :
    p05MatMul (p05Transpose R) R i j =
      p05MatMul (p05Transpose R) R j i := by
  unfold p05MatMul p05Transpose
  apply Finset.sum_congr rfl
  intro k hk
  ring

private lemma p05_absGram_symmetric {n : ℕ}
    (R : Fin n → Fin n → ℝ) (i j : Fin n) :
    p05AbsMatMul (p05Transpose R) R i j =
      p05AbsMatMul (p05Transpose R) R j i := by
  unfold p05AbsMatMul p05Transpose
  apply Finset.sum_congr rfl
  intro k hk
  ring

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
  have hrepr : ∀ i j, run.format.representable (run.RHat i j) := by
    intro i j
    rcases lt_trichotomy i.val j.val with hij | hij | hij
    · let entry := run.off_diagonal_entry i j hij
      have h := (p05Lemma41_result entry.execution).1
      rw [entry.format_eq, entry.computed_output_eq] at h
      exact h
    · have hij' : i = j := Fin.ext hij
      subst j
      let entry := run.diagonal_entry i
      have h := (p05Lemma43_result entry.execution).1
      rw [entry.format_eq, entry.computed_output_eq] at h
      exact h
    · rw [run.RHat_lower_zero i j hij]
      exact run.format.zero_representable
  have hoff : ∀ i j, i.val < j.val →
      |run.A i j - p05CholeskyThroughDot run.RHat i j| ≤
        ((i.val + 1 : ℕ) : ℝ) * run.format.unitRoundoff *
          p05CholeskyThroughAbsDot run.RHat i j := by
    intro i j hij
    let entry := run.off_diagonal_entry i j hij
    have h := (p05Lemma41_result entry.execution).2
    rw [entry.format_eq, entry.denominator_eq, entry.protected_input_eq,
      entry.computed_output_eq] at h
    simp_rw [entry.left_input_eq, entry.right_input_eq] at h
    simpa [p05CholeskyThroughDot, p05CholeskyPrefixDot,
      p05CholeskyThroughAbsDot, p05CholeskyPrefixAbsDot] using h
  have hdiag : ∀ j,
      |run.A j j - p05CholeskyThroughDot run.RHat j j| ≤
        ((j.val + 2 : ℕ) : ℝ) * run.format.unitRoundoff *
          p05CholeskyThroughAbsDot run.RHat j j := by
    intro j
    let entry := run.diagonal_entry j
    have h := (p05Lemma43_result entry.execution).2
    rw [entry.format_eq, entry.protected_input_eq,
      entry.computed_output_eq] at h
    simp_rw [entry.left_input_eq, entry.right_input_eq] at h
    simpa [p05CholeskyThroughDot, p05CholeskyPrefixDot,
      p05CholeskyThroughAbsDot, p05CholeskyPrefixAbsDot, pow_two,
      abs_mul] using h
  refine ⟨hrepr, hoff, hdiag, ?_⟩
  let ΔA : Fin n → Fin n → ℝ := fun i j =>
    p05MatMul (p05Transpose run.RHat) run.RHat i j - run.A i j
  have habs_nonneg : ∀ i j,
      0 ≤ p05AbsMatMul (p05Transpose run.RHat) run.RHat i j := by
    intro i j
    unfold p05AbsMatMul p05Transpose
    positivity
  have hdelta : ∀ i j,
      |ΔA i j| ≤ ((i.val + 2 : ℕ) : ℝ) *
        run.format.unitRoundoff *
          p05AbsMatMul (p05Transpose run.RHat) run.RHat i j := by
    intro i j
    rcases lt_trichotomy i.val j.val with hij | hij | hij
    · have h := hoff i j hij
      rw [← p05_upper_gram_eq_through run.RHat run.RHat_lower_zero i j,
        ← p05_upper_absGram_eq_through run.RHat run.RHat_lower_zero i j] at h
      have hfac : 0 ≤ run.format.unitRoundoff *
          p05AbsMatMul (p05Transpose run.RHat) run.RHat i j :=
        mul_nonneg run.format.unitRoundoff_nonneg (habs_nonneg i j)
      dsimp [ΔA]
      rw [abs_sub_comm]
      calc
        |run.A i j - p05MatMul (p05Transpose run.RHat) run.RHat i j| ≤
            ((i.val + 1 : ℕ) : ℝ) * run.format.unitRoundoff *
              p05AbsMatMul (p05Transpose run.RHat) run.RHat i j := h
        _ ≤ ((i.val + 2 : ℕ) : ℝ) * run.format.unitRoundoff *
              p05AbsMatMul (p05Transpose run.RHat) run.RHat i j := by
            rw [mul_assoc, mul_assoc]
            apply mul_le_mul_of_nonneg_right _ hfac
            norm_num
    · have hij' : i = j := Fin.ext hij
      subst j
      have h := hdiag i
      rw [← p05_upper_gram_eq_through run.RHat run.RHat_lower_zero i i,
        ← p05_upper_absGram_eq_through run.RHat run.RHat_lower_zero i i] at h
      dsimp [ΔA]
      simpa only [abs_sub_comm] using h
    · have h := hoff j i hij
      rw [← p05_upper_gram_eq_through run.RHat run.RHat_lower_zero j i,
        ← p05_upper_absGram_eq_through run.RHat run.RHat_lower_zero j i] at h
      have hfac : 0 ≤ run.format.unitRoundoff *
          p05AbsMatMul (p05Transpose run.RHat) run.RHat j i :=
        mul_nonneg run.format.unitRoundoff_nonneg (habs_nonneg j i)
      have hcoeff : ((j.val + 1 : ℕ) : ℝ) ≤
          ((i.val + 2 : ℕ) : ℝ) := by
        exact_mod_cast (show j.val + 1 ≤ i.val + 2 by omega)
      dsimp [ΔA]
      calc
        |p05MatMul (p05Transpose run.RHat) run.RHat i j - run.A i j| =
            |run.A j i -
              p05MatMul (p05Transpose run.RHat) run.RHat j i| := by
          rw [p05_gram_symmetric run.RHat i j, run.A_symmetric i j,
            abs_sub_comm]
        _ ≤ ((j.val + 1 : ℕ) : ℝ) * run.format.unitRoundoff *
              p05AbsMatMul (p05Transpose run.RHat) run.RHat j i := h
        _ ≤ ((i.val + 2 : ℕ) : ℝ) * run.format.unitRoundoff *
              p05AbsMatMul (p05Transpose run.RHat) run.RHat j i := by
            rw [mul_assoc, mul_assoc]
            exact mul_le_mul_of_nonneg_right hcoeff hfac
        _ = ((i.val + 2 : ℕ) : ℝ) * run.format.unitRoundoff *
              p05AbsMatMul (p05Transpose run.RHat) run.RHat i j := by
            rw [p05_absGram_symmetric run.RHat i j]
  refine ⟨ΔA, ?_, hdelta, ?_⟩
  · funext i j
    simp only [Pi.add_apply]
    dsimp [ΔA]
    ring
  · intro i j
    calc
      |ΔA i j| ≤ ((i.val + 2 : ℕ) : ℝ) *
          run.format.unitRoundoff *
            p05AbsMatMul (p05Transpose run.RHat) run.RHat i j := hdelta i j
      _ ≤ ((n + 1 : ℕ) : ℝ) * run.format.unitRoundoff *
            p05AbsMatMul (p05Transpose run.RHat) run.RHat i j := by
        have hcoeff : ((i.val + 2 : ℕ) : ℝ) ≤
            ((n + 1 : ℕ) : ℝ) := by
          exact_mod_cast (show i.val + 2 ≤ n + 1 by omega)
        have hfac : 0 ≤ run.format.unitRoundoff *
            p05AbsMatMul (p05Transpose run.RHat) run.RHat i j :=
          mul_nonneg run.format.unitRoundoff_nonneg (habs_nonneg i j)
        rw [mul_assoc, mul_assoc]
        exact mul_le_mul_of_nonneg_right hcoeff hfac

end HighamBench
