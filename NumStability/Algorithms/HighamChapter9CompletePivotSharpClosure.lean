-- Algorithms/HighamChapter9CompletePivotSharpClosure.lean
--
-- Implementation-facing closure of Higham's complete-pivoting growth bound
-- (9.14).  The hypotheses below start from the recursive executor trace,
-- rather than from a caller-supplied pivot sequence or growth certificate.

import NumStability.Algorithms.HighamChapter9

namespace NumStability

/-- Every recursive complete-pivoting trace is, in particular, a recursive
rook-pivoting trace with exactly the same exposed upper factor. -/
theorem higham9_14_completePivotTrace_to_rookTrace :
    ∀ {n : ℕ} {A U : Fin n → Fin n → ℝ},
      higham9_8_CompletePivotGECPUTrace n A U →
        higham9_16_RookPivotGEUTrace n A U := by
  intro n A U htrace
  induction htrace with
  | done =>
      exact higham9_16_RookPivotGEUTrace.done
  | step hchoice hpivot _hnext ih =>
      exact higham9_16_RookPivotGEUTrace.step
        (higham9_1_rookPivotChoice_of_completePivotChoice _ _ _ _ hchoice)
        hpivot ih

/-- Every diagonal entry exposed by the recursive complete-pivoting executor
is a nonzero selected pivot. -/
theorem higham9_14_CompletePivotGECPUTrace_diag_ne_zero :
    ∀ {n : ℕ} {A U : Fin n → Fin n → ℝ},
      higham9_8_CompletePivotGECPUTrace n A U →
        ∀ i : Fin n, U i i ≠ 0 := by
  intro n A U htrace
  induction htrace with
  | done =>
      intro i
      exact Fin.elim0 i
  | step hchoice hpivot _hnext ih =>
      rename_i m A r s U₁
      intro i
      by_cases hi : i = 0
      · subst i
        simpa [luFirstStepU, higham9_2_rowColPermutedMatrix,
          higham9_2_rowPermutedMatrix, higham9_2_colPermutedMatrix,
          higham9_7_firstPivotRowSwap] using hpivot
      · have hrec := ih (i.pred hi)
        simpa [luFirstStepU, hi] using hrec

/-- The first exposed diagonal entry is an entry of the input matrix, hence is
bounded by its max-entry norm. -/
theorem higham9_14_CompletePivotGECPUTrace_first_diag_le_maxEntryNorm
    {n : ℕ} (hn : 0 < n) {A U : Fin n → Fin n → ℝ}
    (htrace : higham9_8_CompletePivotGECPUTrace n A U) :
    |U ⟨0, hn⟩ ⟨0, hn⟩| ≤ maxEntryNorm hn A := by
  cases htrace with
  | done => omega
  | @step m A r s U₁ hchoice hpivot hnext =>
      simpa [luFirstStepU, higham9_2_rowColPermutedMatrix,
        higham9_2_rowPermutedMatrix, higham9_2_colPermutedMatrix,
        higham9_7_firstPivotRowSwap] using
        (entry_le_maxEntryNorm (Nat.succ_pos m) A r s)

/-- Prefix Hadamard constraint produced by the actual complete-pivoting
executor.  This is not an assumed pivot certificate: the cumulative `PAQ=LU`
factorization and its diagonal agreement are constructed from the trace, and
the entry bound is discharged by the trace's first complete-pivot choice. -/
theorem higham9_14_CompletePivotGECPUTrace_prefix_diagonal_bound
    {n : ℕ} (hn : 0 < n) {A U : Fin n → Fin n → ℝ}
    (htrace : higham9_8_CompletePivotGECPUTrace n A U)
    {k : ℕ} (hk : k ≤ n) (hkpos : 0 < k) :
    |∏ i : Fin k, U (Fin.castLE hk i) (Fin.castLE hk i)| ≤
      Real.sqrt ((k : ℝ) ^ k) * |U ⟨0, hn⟩ ⟨0, hn⟩| ^ k := by
  cases htrace with
  | done => omega
  | @step m A r s U₁ hchoice hpivot hnext =>
      let Utrace : Fin (m + 1) → Fin (m + 1) → ℝ :=
        luFirstStepU
          (higham9_2_rowColPermutedMatrix A
            (higham9_7_firstPivotRowSwap r)
            (higham9_7_firstPivotRowSwap s)) U₁
      have hcp : higham9_8_CompletePivotGECPUTrace (m + 1) A Utrace :=
        higham9_8_CompletePivotGECPUTrace.step hchoice hpivot hnext
      have hrook : higham9_16_RookPivotGEUTrace (m + 1) A Utrace :=
        higham9_14_completePivotTrace_to_rookTrace hcp
      obtain ⟨L, Uc, sigma, tau, hspec, _hL, _hrow, hdiag⟩ :=
        higham9_16_RookPivotGEUTrace_exists_spec_rook hrook
      have hLU : LUFactSpec (m + 1)
          (higham9_2_rowColPermutedMatrix A sigma tau) L Uc :=
        higham9_2_completePermutedLUFactSpec_to_LUFactSpec hspec
      have hentry : ∀ i j : Fin k,
          |higham9_2_rowColPermutedMatrix A sigma tau
              (Fin.castLE hk i) (Fin.castLE hk j)| ≤
            |Utrace ⟨0, Nat.succ_pos m⟩ ⟨0, Nat.succ_pos m⟩| := by
        intro i j
        have hmax := hchoice.2.2 (sigma (Fin.castLE hk i))
          (tau (Fin.castLE hk j)) (Nat.zero_le _) (Nat.zero_le _)
        simpa [Utrace, luFirstStepU, higham9_2_rowColPermutedMatrix,
          higham9_2_rowPermutedMatrix, higham9_2_colPermutedMatrix,
          higham9_7_firstPivotRowSwap] using hmax
      have hhad := higham9_14_abs_prod_leadingPivots_le_of_entries_le
        hLU hk hkpos hentry
      have hprod :
          (∏ i : Fin k, Uc (Fin.castLE hk i) (Fin.castLE hk i)) =
            ∏ i : Fin k, Utrace (Fin.castLE hk i) (Fin.castLE hk i) := by
        apply Finset.prod_congr rfl
        intro i _
        exact hdiag _
      rw [hprod] at hhad
      simpa [Utrace] using hhad

/-- Every consecutive diagonal segment of an actual complete-pivoting trace
satisfies Wilkinson's Hadamard constraint. -/
theorem higham9_14_CompletePivotGECPUTrace_segment_diagonal_bound :
    ∀ {n : ℕ} {A U : Fin n → Fin n → ℝ},
      higham9_8_CompletePivotGECPUTrace n A U →
      ∀ (a j : ℕ) (hjpos : 0 < j) (haj : a + j ≤ n),
        |∏ t : Fin j,
            U ⟨a + t.val, by have := t.isLt; omega⟩
              ⟨a + t.val, by have := t.isLt; omega⟩| ≤
          Real.sqrt ((j : ℝ) ^ j) *
            |U ⟨a, by omega⟩ ⟨a, by omega⟩| ^ j := by
  intro n A U htrace
  induction htrace with
  | done =>
      intro a j hjpos haj
      omega
  | step hchoice hpivot hnext ih =>
      rename_i m A r s U₁
      intro a j hjpos haj
      cases a with
      | zero =>
          have hprefix :=
            higham9_14_CompletePivotGECPUTrace_prefix_diagonal_bound
              (Nat.succ_pos m)
              (higham9_8_CompletePivotGECPUTrace.step hchoice hpivot hnext)
              (k := j) (by omega) hjpos
          convert hprefix using 1
          congr 1
          apply Finset.prod_congr rfl
          intro t _
          congr 1 <;> apply Fin.ext <;> simp
      | succ a =>
          have hrec := ih a j hjpos (by omega)
          convert hrec using 1
          · congr 1
            apply Finset.prod_congr rfl
            intro t _
            have hidx_ne :
                (⟨a + 1 + t.val, by have := t.isLt; omega⟩ : Fin (m + 1)) ≠ 0 := by
              intro h
              have hv := congrArg Fin.val h
              simp at hv
            simp [luFirstStepU, hidx_ne]
            congr 1 <;> apply Fin.ext <;> simp [Fin.val_pred]

/-- **Higham (9.14), implementation-facing closure.**  Every upper factor
produced by the recursive complete-pivoting executor satisfies Wilkinson's
sharp displayed max-entry growth bound. -/
theorem higham9_14_CompletePivotGECPUTrace_growthFactorEntry_le_wilkinsonBound
    {n : ℕ} (hn : 0 < n) (A U : Fin n → Fin n → ℝ)
    (hAmax : 0 < maxEntryNorm hn A)
    (htrace : higham9_8_CompletePivotGECPUTrace n A U) :
    growthFactorEntry hn A U hAmax ≤
      higham9_14_completePivotWilkinsonBound n := by
  classical
  let p : ℕ → ℝ := fun k =>
    if h : k - 1 < n then |U ⟨k - 1, h⟩ ⟨k - 1, h⟩| else 1
  have hpval : ∀ k, ∀ (h : k - 1 < n),
      p k = |U ⟨k - 1, h⟩ ⟨k - 1, h⟩| := by
    intro k h
    simp [p, dif_pos h]
  have hdiag := higham9_14_CompletePivotGECPUTrace_diag_ne_zero htrace
  have hpos : ∀ k, 1 ≤ k → k ≤ n → 0 < p k := by
    intro k hk1 hkn
    rw [hpval k (by omega)]
    exact abs_pos.mpr (hdiag _)
  have hpiv : ∀ a b, 1 ≤ a → a ≤ b → b ≤ n →
      ∏ i ∈ Finset.Icc a b, p i ≤
        Real.sqrt (((b - a + 1 : ℕ) : ℝ) ^ (b - a + 1)) *
          p a ^ (b - a + 1) := by
    intro a b ha1 hab hbn
    have hjpos : 0 < b - a + 1 := by omega
    have hseg := higham9_14_CompletePivotGECPUTrace_segment_diagonal_bound
      htrace (a - 1) (b - a + 1) hjpos (by omega)
    have hIcc_range : ∏ i ∈ Finset.Icc a b, p i =
        ∏ t ∈ Finset.range (b - a + 1), p (a + t) := by
      rw [← Finset.Ico_succ_right_eq_Icc, Order.succ_eq_add_one,
        Finset.prod_Ico_eq_prod_range,
        show b + 1 - a = b - a + 1 from by omega]
    have hIcc : ∏ i ∈ Finset.Icc a b, p i =
        ∏ t : Fin (b - a + 1), p (a + t.val) := by
      rw [hIcc_range]
      exact (Fin.prod_univ_eq_prod_range
        (fun t => p (a + t)) (b - a + 1)).symm
    rw [hIcc]
    have hterm : ∀ t : Fin (b - a + 1),
        p (a + t.val) =
          |U ⟨(a - 1) + t.val, by have := t.isLt; omega⟩
              ⟨(a - 1) + t.val, by have := t.isLt; omega⟩| := by
      intro t
      rw [hpval (a + t) (by
        have := t.isLt
        omega)]
      congr 2 <;> apply Fin.ext <;> simp <;> omega
    rw [Finset.prod_congr rfl (fun t _ => hterm t)]
    have hpa : p a = |U ⟨a - 1, by omega⟩ ⟨a - 1, by omega⟩| :=
      hpval a (by omega)
    rw [hpa]
    rw [Finset.abs_prod] at hseg
    exact hseg
  have hrook := higham9_14_completePivotTrace_to_rookTrace htrace
  have hrow := higham9_16_RookPivotGEUTrace_row_max hrook
  have hp1max : p 1 ≤ maxEntryNorm hn A := by
    rw [hpval 1 (by omega)]
    simpa using
      higham9_14_CompletePivotGECPUTrace_first_diag_le_maxEntryNorm hn htrace
  have hbound_nonneg := higham9_14_completePivotWilkinsonBound_nonneg n
  apply growthFactorEntry_le_of_entry_bound_factor hn A U
    (higham9_14_completePivotWilkinsonBound n) hAmax
  intro i j
  have hpivot_bound :
      p (i.val + 1) ≤ higham9_14_completePivotWilkinsonBound n * p 1 :=
    higham9_14_wilkinson_pivot_le_bound_mul hn p hpos hpiv
      (by omega) (by omega)
  have hpivot_eq : p (i.val + 1) = |U i i| := by
    simpa using hpval (i.val + 1) (by omega)
  calc
    |U i j| ≤ |U i i| := hrow i j
    _ = p (i.val + 1) := hpivot_eq.symm
    _ ≤ higham9_14_completePivotWilkinsonBound n * p 1 := hpivot_bound
    _ ≤ higham9_14_completePivotWilkinsonBound n * maxEntryNorm hn A :=
      mul_le_mul_of_nonneg_left hp1max hbound_nonneg

/-- A max-entry norm occurring in the *whole reduced-matrix history* of an
actual recursive complete-pivoting execution.  At a nonempty step the current
matrix is the current reduced matrix; `tail` descends to exactly its first
Schur complement after the chosen row and column interchanges. -/
inductive higham9_14_CompletePivotReducedStageNorm :
    {n : ℕ} → {A U : Fin n → Fin n → ℝ} →
      higham9_8_CompletePivotGECPUTrace n A U → ℝ → Prop
  | current {m : ℕ} {A : Fin (m + 1) → Fin (m + 1) → ℝ}
      {r s : Fin (m + 1)} {U₁ : Fin m → Fin m → ℝ}
      (hchoice : higham9_1_completePivotChoice A 0 r s)
      (hpivot : A r s ≠ 0)
      (hnext : higham9_8_CompletePivotGECPUTrace m
        (luFirstSchurComplement
          (higham9_2_rowColPermutedMatrix A
            (higham9_7_firstPivotRowSwap r)
            (higham9_7_firstPivotRowSwap s))) U₁) :
      higham9_14_CompletePivotReducedStageNorm
        (higham9_8_CompletePivotGECPUTrace.step hchoice hpivot hnext)
        (maxEntryNorm (Nat.succ_pos m) A)
  | tail {m : ℕ} {A : Fin (m + 1) → Fin (m + 1) → ℝ}
      {r s : Fin (m + 1)} {U₁ : Fin m → Fin m → ℝ}
      (hchoice : higham9_1_completePivotChoice A 0 r s)
      (hpivot : A r s ≠ 0)
      (hnext : higham9_8_CompletePivotGECPUTrace m
        (luFirstSchurComplement
          (higham9_2_rowColPermutedMatrix A
            (higham9_7_firstPivotRowSwap r)
            (higham9_7_firstPivotRowSwap s))) U₁)
      {x : ℝ} (hx : higham9_14_CompletePivotReducedStageNorm hnext x) :
      higham9_14_CompletePivotReducedStageNorm
        (higham9_8_CompletePivotGECPUTrace.step hchoice hpivot hnext) x

/-- The set of max-entry norms of `A⁽¹⁾, …, A⁽ⁿ⁾` stored by one actual
complete-pivoting trace. -/
def higham9_14_completePivotReducedHistoryNormSet
    {n : ℕ} {A U : Fin n → Fin n → ℝ}
    (htrace : higham9_8_CompletePivotGECPUTrace n A U) : Set ℝ :=
  {x | higham9_14_CompletePivotReducedStageNorm htrace x}

/-- The maximum entry magnitude over the full reduced-matrix history.  The
trace is finite and nonempty in positive dimension; the lemmas below prove
that this supremum is bounded by, and hence is the maximum represented by,
the trace's exposed pivot rows. -/
noncomputable def higham9_14_completePivotReducedHistoryMax
    {n : ℕ} {A U : Fin n → Fin n → ℝ}
    (htrace : higham9_8_CompletePivotGECPUTrace n A U) : ℝ :=
  sSup (higham9_14_completePivotReducedHistoryNormSet htrace)

/-- Higham's complete-pivoting growth factor `ρ⁽ᶜ⁾ₙ` for the actual recursive
executor: the maximum entry magnitude over every reduced matrix, divided by
the max-entry norm of the original input. -/
noncomputable def higham9_14_completePivotReducedHistoryGrowthFactor
    {n : ℕ} (hn : 0 < n) (A U : Fin n → Fin n → ℝ)
    (_hAmax : 0 < maxEntryNorm hn A)
    (htrace : higham9_8_CompletePivotGECPUTrace n A U) : ℝ :=
  higham9_14_completePivotReducedHistoryMax htrace / maxEntryNorm hn A

/-- The selected complete pivot at each recursive step is the maximum entry
of that reduced matrix and is exposed on the corresponding diagonal of `U`.
Consequently the maximum over the complete reduced-matrix history is bounded
by the max-entry norm of the trace's exposed upper factor. -/
theorem higham9_14_completePivotReducedHistoryMax_le_maxEntryNorm_U :
    ∀ {n : ℕ} {A U : Fin n → Fin n → ℝ}
      (htrace : higham9_8_CompletePivotGECPUTrace n A U)
      (hn : 0 < n),
      higham9_14_completePivotReducedHistoryMax htrace ≤ maxEntryNorm hn U := by
  intro n A U htrace hn
  unfold higham9_14_completePivotReducedHistoryMax
  apply csSup_le
  · cases htrace with
    | done => omega
    | step hchoice hpivot hnext =>
        exact ⟨maxEntryNorm (Nat.succ_pos _) _,
          higham9_14_CompletePivotReducedStageNorm.current hchoice hpivot hnext⟩
  · intro x hx
    change higham9_14_CompletePivotReducedStageNorm htrace x at hx
    induction hx with
    | @current m A r s U₁ hchoice hpivot hnext =>
        apply maxEntryNorm_le_of_entry_le_bound (Nat.succ_pos m) A
          (maxEntryNorm (Nat.succ_pos m)
            (luFirstStepU
              (higham9_2_rowColPermutedMatrix A
                (higham9_7_firstPivotRowSwap r)
                (higham9_7_firstPivotRowSwap s)) U₁))
        intro i j
        calc
          |A i j| ≤ |A r s| :=
            hchoice.2.2 i j (Nat.zero_le _) (Nat.zero_le _)
          _ = |luFirstStepU
                (higham9_2_rowColPermutedMatrix A
                  (higham9_7_firstPivotRowSwap r)
                  (higham9_7_firstPivotRowSwap s)) U₁ 0 0| := by
              simp [luFirstStepU, higham9_2_rowColPermutedMatrix,
                higham9_2_rowPermutedMatrix, higham9_2_colPermutedMatrix,
                higham9_7_firstPivotRowSwap]
          _ ≤ maxEntryNorm (Nat.succ_pos m)
                (luFirstStepU
                  (higham9_2_rowColPermutedMatrix A
                    (higham9_7_firstPivotRowSwap r)
                    (higham9_7_firstPivotRowSwap s)) U₁) :=
              entry_le_maxEntryNorm (Nat.succ_pos m) _ 0 0
    | @tail m A r s U₁ hchoice hpivot hnext x hx ih =>
        have hm : 0 < m := by
          by_contra hm
          have hm0 : m = 0 := Nat.eq_zero_of_not_pos hm
          subst m
          cases hx
        calc
          x ≤ maxEntryNorm hm U₁ := ih hm
          _ ≤ maxEntryNorm (Nat.succ_pos m)
                (luFirstStepU
                  (higham9_2_rowColPermutedMatrix A
                    (higham9_7_firstPivotRowSwap r)
                    (higham9_7_firstPivotRowSwap s)) U₁) := by
              apply maxEntryNorm_le_of_entry_le_bound hm U₁
                (maxEntryNorm (Nat.succ_pos m)
                  (luFirstStepU
                    (higham9_2_rowColPermutedMatrix A
                      (higham9_7_firstPivotRowSwap r)
                      (higham9_7_firstPivotRowSwap s)) U₁))
              intro i j
              have hentry := entry_le_maxEntryNorm (Nat.succ_pos m)
                (luFirstStepU
                  (higham9_2_rowColPermutedMatrix A
                    (higham9_7_firstPivotRowSwap r)
                    (higham9_7_firstPivotRowSwap s)) U₁) i.succ j.succ
              simpa [luFirstStepU] using hentry

/-- **Higham (9.14), actual all-reduced-matrices endpoint.**  The PDF's
growth factor—not merely the max-entry norm of the final `U`—satisfies
Wilkinson's sharp displayed product bound for every recursive complete-pivot
execution.  No pivot sequence, growth certificate, or target inequality is a
premise. -/
theorem higham9_14_CompletePivotGECPUTrace_reducedHistoryGrowthFactor_le_wilkinsonBound
    {n : ℕ} (hn : 0 < n) (A U : Fin n → Fin n → ℝ)
    (hAmax : 0 < maxEntryNorm hn A)
    (htrace : higham9_8_CompletePivotGECPUTrace n A U) :
    higham9_14_completePivotReducedHistoryGrowthFactor hn A U hAmax htrace ≤
      higham9_14_completePivotWilkinsonBound n := by
  have hhist :=
    higham9_14_completePivotReducedHistoryMax_le_maxEntryNorm_U htrace hn
  have hU :=
    higham9_14_CompletePivotGECPUTrace_growthFactorEntry_le_wilkinsonBound
      hn A U hAmax htrace
  unfold higham9_14_completePivotReducedHistoryGrowthFactor
  unfold growthFactorEntry at hU
  rw [div_le_iff₀ hAmax]
  rw [div_le_iff₀ hAmax] at hU
  exact hhist.trans hU

/-- Source-facing nonsingular-input endpoint: the repository's actual
complete-pivoting executor exists and its output satisfies (9.14), with no
caller-provided target, pivot sequence, or sharp-growth premise. -/
theorem higham9_14_exists_CompletePivotGECPUTrace_growthFactorEntry_le_wilkinsonBound
    {n : ℕ} (hn : 0 < n) (A : Fin n → Fin n → ℝ)
    (hdet : Matrix.det (Matrix.of A : Matrix (Fin n) (Fin n) ℝ) ≠ 0) :
    ∃ hAmax : 0 < maxEntryNorm hn A,
    ∃ U : Fin n → Fin n → ℝ,
      higham9_8_CompletePivotGECPUTrace n A U ∧
        growthFactorEntry hn A U hAmax ≤
          higham9_14_completePivotWilkinsonBound n := by
  have hAmax : 0 < maxEntryNorm hn A :=
    maxEntryNorm_pos_of_det_ne_zero hn A hdet
  obtain ⟨U, htrace⟩ :=
    higham9_8_exists_CompletePivotGECPUTrace_of_det_ne_zero (A := A) hdet
  exact ⟨hAmax, U, htrace,
    higham9_14_CompletePivotGECPUTrace_growthFactorEntry_le_wilkinsonBound
      hn A U hAmax htrace⟩

/-- Source-facing nonsingular-input closure for the PDF-faithful growth
factor over all reduced matrices.  The trace is constructed by the repository's
actual complete-pivoting GECP relation and the denominator is derived from
nonsingularity. -/
theorem higham9_14_exists_CompletePivotGECPUTrace_reducedHistoryGrowthFactor_le_wilkinsonBound
    {n : ℕ} (hn : 0 < n) (A : Fin n → Fin n → ℝ)
    (hdet : Matrix.det (Matrix.of A : Matrix (Fin n) (Fin n) ℝ) ≠ 0) :
    ∃ hAmax : 0 < maxEntryNorm hn A,
    ∃ U : Fin n → Fin n → ℝ,
    ∃ htrace : higham9_8_CompletePivotGECPUTrace n A U,
      higham9_14_completePivotReducedHistoryGrowthFactor hn A U hAmax htrace ≤
        higham9_14_completePivotWilkinsonBound n := by
  have hAmax : 0 < maxEntryNorm hn A :=
    maxEntryNorm_pos_of_det_ne_zero hn A hdet
  obtain ⟨U, htrace⟩ :=
    higham9_8_exists_CompletePivotGECPUTrace_of_det_ne_zero (A := A) hdet
  exact ⟨hAmax, U, htrace,
    higham9_14_CompletePivotGECPUTrace_reducedHistoryGrowthFactor_le_wilkinsonBound
      hn A U hAmax htrace⟩

end NumStability
