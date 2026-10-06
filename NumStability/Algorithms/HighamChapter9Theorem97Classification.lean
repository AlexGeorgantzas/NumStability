-- HighamChapter9Theorem97Classification.lean
--
-- Source-strength closure for Higham, Theorem 9.7.  The source growth
-- numerator is the maximum over all recursively reduced GEPP matrices, not
-- merely the maximum entry of the final upper factor.  Ties are resolved by
-- retaining the leading active row, exactly as required by the printed
-- no-interchange conclusion.

import NumStability.Algorithms.HighamChapter9

namespace NumStability

open scoped BigOperators

/-! ## A leading-row-on-ties GEPP trace and its source growth factor -/

/-- Partial pivoting with the explicit convention used by Theorem 9.7:
among equal-modulus column maxima, the already-leading active row is kept. -/
def higham9_7_leadingRowOnTiesChoice {m : ℕ}
    (A : Fin (m + 1) → Fin (m + 1) → ℝ) (r : Fin (m + 1)) : Prop :=
  higham9_1_partialPivotChoice A 0 r ∧
    (|A 0 0| = |A r 0| → r = 0)

/-- Exact recursive GEPP trace with Higham's leading-row-on-ties convention.
The exposed `U` is the actual upper factor assembled from the successive
pivot rows. -/
inductive higham9_7_LeadingTieGEPPTrace :
    (n : ℕ) → (Fin n → Fin n → ℝ) →
      (Fin n → Fin n → ℝ) → ℝ → Prop
  | done {A U : Fin 0 → Fin 0 → ℝ} :
      higham9_7_LeadingTieGEPPTrace 0 A U 0
  | step {m : ℕ} {A : Fin (m + 1) → Fin (m + 1) → ℝ}
      {r : Fin (m + 1)} {U₁ : Fin m → Fin m → ℝ} {g₁ : ℝ}
      (hchoice : higham9_7_leadingRowOnTiesChoice A r)
      (hpivot : A r 0 ≠ 0)
      (hnext :
        higham9_7_LeadingTieGEPPTrace m
          (luFirstSchurComplement
            (higham9_2_rowPermutedMatrix A (higham9_7_firstPivotRowSwap r))) U₁ g₁) :
      higham9_7_LeadingTieGEPPTrace (m + 1) A
        (luFirstStepU
          (higham9_2_rowPermutedMatrix A (higham9_7_firstPivotRowSwap r)) U₁)
        (max (maxEntryNorm (Nat.succ_pos m) A) g₁)

/-- Forgetting the tie convention gives the ordinary exact GEPP `U` trace. -/
theorem higham9_7_LeadingTieGEPPTrace.toPartialPivotGEPPUTrace :
    ∀ {n : ℕ} {A U : Fin n → Fin n → ℝ} {g : ℝ},
      higham9_7_LeadingTieGEPPTrace n A U g →
        higham9_7_PartialPivotGEPPUTrace n A U := by
  intro n A U g htrace
  induction htrace with
  | done => exact higham9_7_PartialPivotGEPPUTrace.done
  | step hchoice hpivot hnext ih =>
      exact higham9_7_PartialPivotGEPPUTrace.step hchoice.1 hpivot ih

/-- A nonsingular active matrix admits a partial-pivot choice satisfying the
leading-row-on-ties convention.  This makes the tie convention executable:
take the leading row whenever its modulus equals the finite column maximum,
and otherwise retain any ordinary partial-pivot maximizer. -/
theorem higham9_7_exists_leadingRowOnTiesChoice_pivot_ne_zero_of_det_ne_zero
    {m : ℕ} (A : Fin (m + 1) → Fin (m + 1) → ℝ)
    (hdet : Matrix.det
      (Matrix.of A : Matrix (Fin (m + 1)) (Fin (m + 1)) ℝ) ≠ 0) :
    ∃ r : Fin (m + 1),
      higham9_7_leadingRowOnTiesChoice A r ∧ A r 0 ≠ 0 := by
  obtain ⟨r, hchoice, hpivot⟩ :=
    higham9_10_exists_first_partialPivotChoice_pivot_ne_zero_of_det_ne_zero
      A hdet
  by_cases heq : |A 0 0| = |A r 0|
  · refine ⟨0, ⟨?_, fun _ => rfl⟩, ?_⟩
    · refine ⟨by simp, ?_⟩
      intro i _hi
      exact (hchoice.2 i (by simp)).trans_eq heq.symm
    · intro hzero
      apply hpivot
      apply abs_eq_zero.mp
      rw [← heq, hzero, abs_zero]
  · refine ⟨r, ⟨hchoice, ?_⟩, hpivot⟩
    intro htie
    exact False.elim (heq htie)

/-- Every nonsingular real matrix admits the exact recursive GEPP trace with
the tie convention used by Theorem 9.7.  Thus the classification theorem below
does not depend on a potentially empty or caller-invented execution surface. -/
theorem higham9_7_exists_LeadingTieGEPPTrace_of_det_ne_zero :
    ∀ {n : ℕ} {A : Fin n → Fin n → ℝ},
      Matrix.det (Matrix.of A : Matrix (Fin n) (Fin n) ℝ) ≠ 0 →
      ∃ (U : Fin n → Fin n → ℝ) (g : ℝ),
        higham9_7_LeadingTieGEPPTrace n A U g := by
  intro n
  induction n with
  | zero =>
      intro A _hdet
      exact ⟨A, 0, higham9_7_LeadingTieGEPPTrace.done⟩
  | succ m ih =>
      intro A hdet
      obtain ⟨r, hchoice, hpivot⟩ :=
        higham9_7_exists_leadingRowOnTiesChoice_pivot_ne_zero_of_det_ne_zero
          A hdet
      let Aperm : Fin (m + 1) → Fin (m + 1) → ℝ :=
        higham9_2_rowPermutedMatrix A (higham9_7_firstPivotRowSwap r)
      let S : Fin m → Fin m → ℝ := luFirstSchurComplement Aperm
      have hdetS :
          Matrix.det (Matrix.of S : Matrix (Fin m) (Fin m) ℝ) ≠ 0 := by
        simpa [S, Aperm] using
          higham9_10_firstSchurComplement_det_ne_zero_of_det_ne_zero
            A hpivot hdet
      obtain ⟨U₁, g₁, hnext⟩ := ih (A := S) hdetS
      refine ⟨luFirstStepU Aperm U₁,
        max (maxEntryNorm (Nat.succ_pos m) A) g₁, ?_⟩
      simpa [Aperm, S] using
        higham9_7_LeadingTieGEPPTrace.step hchoice hpivot hnext

/-- Higham's partial-pivoting growth factor, with numerator ranging over all
active reduced matrices in the source trace. -/
noncomputable def higham9_7_sourceReducedGrowthFactor {n : ℕ}
    (hn : 0 < n) (A U : Fin n → Fin n → ℝ)
    (_hApos : 0 < maxEntryNorm hn A)
    (g : ℝ) (_htrace : higham9_7_LeadingTieGEPPTrace n A U g) : ℝ :=
  g / maxEntryNorm hn A

/-- Every source reduced maximum is nonnegative. -/
theorem higham9_7_LeadingTieGEPPTrace_sourceMax_nonneg :
    ∀ {n : ℕ} {A U : Fin n → Fin n → ℝ} {g : ℝ},
      higham9_7_LeadingTieGEPPTrace n A U g → 0 ≤ g := by
  intro n A U g htrace
  induction htrace with
  | done => norm_num
  | step hchoice hpivot hnext ih =>
      exact le_max_of_le_right ih

/-- The source reduced maximum contains the initial matrix norm. -/
theorem higham9_7_LeadingTieGEPPTrace_initial_le_sourceMax {m : ℕ}
    {A U : Fin (m + 1) → Fin (m + 1) → ℝ} {g : ℝ}
    (htrace : higham9_7_LeadingTieGEPPTrace (m + 1) A U g) :
    maxEntryNorm (Nat.succ_pos m) A ≤ g := by
  cases htrace with
  | step hchoice hpivot hnext => exact le_max_left _ _

/-- Every final-`U` entry is literally a pivot-row entry from one of the
source reduced matrices, hence is bounded by the source reduced maximum. -/
theorem higham9_7_LeadingTieGEPPTrace_finalU_entry_le_sourceMax :
    ∀ {n : ℕ} {A U : Fin n → Fin n → ℝ} {g : ℝ},
      higham9_7_LeadingTieGEPPTrace n A U g →
        ∀ i j : Fin n, |U i j| ≤ g := by
  intro n A U g htrace
  induction htrace with
  | done =>
      intro i
      exact Fin.elim0 i
  | step hchoice hpivot hnext ih =>
      rename_i m A r U₁ g₁
      intro i j
      let sigma := higham9_7_firstPivotRowSwap r
      let Aperm := higham9_2_rowPermutedMatrix A sigma
      by_cases hi : i = 0
      · subst i
        have hentry : |A r j| ≤ maxEntryNorm (Nat.succ_pos m) A :=
          entry_le_maxEntryNorm (Nat.succ_pos m) A r j
        have hmax : maxEntryNorm (Nat.succ_pos m) A ≤
            max (maxEntryNorm (Nat.succ_pos m) A) g₁ := le_max_left _ _
        simpa [Aperm, sigma, luFirstStepU, higham9_2_rowPermutedMatrix,
          higham9_7_firstPivotRowSwap] using le_trans hentry hmax
      · by_cases hj : j = 0
        · subst j
          have hg : 0 ≤ max (maxEntryNorm (Nat.succ_pos m) A) g₁ :=
            le_trans (higham9_7_LeadingTieGEPPTrace_sourceMax_nonneg hnext)
              (le_max_right _ _)
          simpa [Aperm, luFirstStepU, hi] using hg
        · have htail := ih (i.pred hi) (j.pred hj)
          have hle : g₁ ≤ max (maxEntryNorm (Nat.succ_pos m) A) g₁ :=
            le_max_right _ _
          simpa [Aperm, luFirstStepU, hi, hj] using le_trans htail hle

/-- Consequently the final upper-factor norm is bounded by the source
reduced maximum.  This is the explicit source-history-to-final-`U` bridge
needed in the extremal argument. -/
theorem higham9_7_LeadingTieGEPPTrace_finalU_maxEntryNorm_le_sourceMax
    {n : ℕ} (hn : 0 < n) {A U : Fin n → Fin n → ℝ} {g : ℝ}
    (htrace : higham9_7_LeadingTieGEPPTrace n A U g) :
    maxEntryNorm hn U ≤ g := by
  apply maxEntryNorm_le_of_entry_le_bound hn U g
  exact higham9_7_LeadingTieGEPPTrace_finalU_entry_le_sourceMax htrace

/-- Source growth bound over all active reduced matrices. -/
theorem higham9_7_LeadingTieGEPPTrace_sourceMax_le_pow_two :
    ∀ {n : ℕ} {A U : Fin n → Fin n → ℝ} {g : ℝ},
      higham9_7_LeadingTieGEPPTrace n A U g →
        ∀ hn : 0 < n,
          g ≤ (2 : ℝ) ^ (n - 1) * maxEntryNorm hn A := by
  intro n A U g htrace
  induction htrace with
  | done =>
      intro hn
      omega
  | step hchoice hpivot hnext ih =>
      rename_i m A r U₁ g₁
      intro hn
      let sigma := higham9_7_firstPivotRowSwap r
      let Aperm := higham9_2_rowPermutedMatrix A sigma
      let S := luFirstSchurComplement Aperm
      by_cases hm : 0 < m
      · have hS : maxEntryNorm hm S ≤
            2 * maxEntryNorm (Nat.succ_pos m) A := by
          simpa [S, Aperm, sigma] using
            higham9_7_partialPivot_firstSchurComplement_maxEntryNorm_le_two
              hm A r hchoice.1 hpivot
        have hg₁ : g₁ ≤ (2 : ℝ) ^ (m - 1) * maxEntryNorm hm S :=
          ih hm
        have hpow_nonneg : 0 ≤ (2 : ℝ) ^ (m - 1) :=
          pow_nonneg (by norm_num) _
        have hg₁' : g₁ ≤ (2 : ℝ) ^ m *
            maxEntryNorm (Nat.succ_pos m) A := by
          calc
            g₁ ≤ (2 : ℝ) ^ (m - 1) * maxEntryNorm hm S := hg₁
            _ ≤ (2 : ℝ) ^ (m - 1) *
                  (2 * maxEntryNorm (Nat.succ_pos m) A) :=
              mul_le_mul_of_nonneg_left hS hpow_nonneg
            _ = (2 : ℝ) ^ m * maxEntryNorm (Nat.succ_pos m) A := by
              have hm_eq : m = (m - 1) + 1 := by omega
              have hpow : (2 : ℝ) ^ m = (2 : ℝ) ^ (m - 1) * 2 := by
                calc
                  (2 : ℝ) ^ m = (2 : ℝ) ^ ((m - 1) + 1) :=
                    congrArg (fun k : ℕ => (2 : ℝ) ^ k) hm_eq
                  _ = (2 : ℝ) ^ (m - 1) * 2 := pow_succ _ _
              rw [hpow]
              ring
        have hM_nonneg : 0 ≤ maxEntryNorm (Nat.succ_pos m) A :=
          maxEntryNorm_nonneg (Nat.succ_pos m) A
        have hpow_one : (1 : ℝ) ≤ (2 : ℝ) ^ m := by
          simpa using pow_le_pow_right₀ (by norm_num : (1 : ℝ) ≤ 2)
            (Nat.zero_le m)
        have hM : maxEntryNorm (Nat.succ_pos m) A ≤
            (2 : ℝ) ^ m * maxEntryNorm (Nat.succ_pos m) A := by
          calc
            maxEntryNorm (Nat.succ_pos m) A =
                1 * maxEntryNorm (Nat.succ_pos m) A := by ring
            _ ≤ (2 : ℝ) ^ m * maxEntryNorm (Nat.succ_pos m) A :=
              mul_le_mul_of_nonneg_right hpow_one hM_nonneg
        simpa using max_le hM hg₁'
      · have hm0 : m = 0 := Nat.eq_zero_of_not_pos hm
        subst m
        cases hnext
        simpa using maxEntryNorm_nonneg hn A

/-! ## Extremal algebra used by the equality classification -/

/-- The unit lower factor forced at equality: `D M D`, where `M` is the
unit lower matrix with every strict-lower entry equal to `-1`. -/
noncomputable def higham9_7_signedExtremalLower {n : ℕ}
    (d : Fin n → ℝ) : Fin n → Fin n → ℝ :=
  fun i j => d i * higham9_7_wilkinsonGrowthL i j * d j

/-- The fixed matrix `M` occurring literally in the printed statement. -/
noncomputable abbrev higham9_7_extremalM {n : ℕ} :
    Fin n → Fin n → ℝ :=
  higham9_7_wilkinsonGrowthL

theorem higham9_7_signedExtremalLower_diag {n : ℕ} {d : Fin n → ℝ}
    (hd : ∀ i, d i ^ 2 = 1) (i : Fin n) :
    higham9_7_signedExtremalLower d i i = 1 := by
  simp only [higham9_7_signedExtremalLower, higham9_7_wilkinsonGrowthL]
  simpa [pow_two] using hd i

theorem higham9_7_signedExtremalLower_upper_zero {n : ℕ}
    (d : Fin n → ℝ) (i j : Fin n) (hij : i.val < j.val) :
    higham9_7_signedExtremalLower d i j = 0 := by
  have hne : j.val ≠ i.val := Nat.ne_of_gt hij
  have hnlt : ¬j.val < i.val := Nat.not_lt_of_ge (Nat.le_of_lt hij)
  simp [higham9_7_signedExtremalLower, higham9_7_wilkinsonGrowthL,
    hne, hnlt]

theorem higham9_7_signedExtremalLower_strictLower {n : ℕ}
    (d : Fin n → ℝ) (i j : Fin n) (hji : j.val < i.val) :
    higham9_7_signedExtremalLower d i j = -(d i * d j) := by
  have hne : j.val ≠ i.val := ne_of_lt hji
  simp [higham9_7_signedExtremalLower, higham9_7_wilkinsonGrowthL,
    hne, hji]

/-- Binary-sum rigidity behind the final-column computation:
`(D M D) (alpha D d) = alpha D 1`. -/
theorem higham9_7_signedExtremalLower_mul_powerColumn {n : ℕ}
    (d : Fin n → ℝ) (hd : ∀ k, d k ^ 2 = 1)
    (alpha : ℝ) (i : Fin n) :
    (∑ k : Fin n,
      higham9_7_signedExtremalLower d i k *
        (alpha * d k * (2 : ℝ) ^ k.val)) = alpha * d i := by
  calc
    (∑ k : Fin n,
      higham9_7_signedExtremalLower d i k *
        (alpha * d k * (2 : ℝ) ^ k.val)) =
        alpha * d i *
          (∑ k : Fin n,
            higham9_7_wilkinsonGrowthL i k * (2 : ℝ) ^ k.val) := by
      rw [Finset.mul_sum]
      apply Finset.sum_congr rfl
      intro k _hk
      unfold higham9_7_signedExtremalLower
      have hdk := hd k
      simp only [pow_two] at hdk
      calc
        d i * higham9_7_wilkinsonGrowthL i k * d k *
              (alpha * d k * (2 : ℝ) ^ k.val) =
            alpha * d i * higham9_7_wilkinsonGrowthL i k *
              (d k * d k) * (2 : ℝ) ^ k.val := by ring
        _ = alpha * d i *
              (higham9_7_wilkinsonGrowthL i k * (2 : ℝ) ^ k.val) := by
          rw [hdk]
          ring
    _ = alpha * d i := by
      rw [higham9_7_wilkinsonGrowthL_two_pow_sum i]
      ring

/-- Equality in the local first-Schur-complement `2 alpha` bound fixes the
two contributing terms and their signs. -/
theorem higham9_7_sub_eq_two_mul_sign_rigidity
    {alpha delta x y : ℝ} (_halpha : 0 < alpha)
    (hdelta : delta ^ 2 = 1)
    (hx : |x| ≤ alpha) (hy : |y| ≤ alpha)
    (hxy : x - y = 2 * alpha * delta) :
    x = alpha * delta ∧ y = -(alpha * delta) := by
  rcases (sq_eq_one_iff.mp hdelta) with hdelta | hdelta
  · subst delta
    have hx' := (abs_le.mp hx)
    have hy' := (abs_le.mp hy)
    constructor <;> norm_num at hxy ⊢ <;> linarith
  · subst delta
    have hx' := (abs_le.mp hx)
    have hy' := (abs_le.mp hy)
    constructor <;> norm_num at hxy ⊢ <;> linarith

/-- The printed upper block `[T | alpha d; 0 | alpha*2^m]`, represented as
a full `(m+1)` square matrix. -/
noncomputable def higham9_7_printedUpperBlock {m : ℕ}
    (T : Fin m → Fin m → ℝ) (alpha : ℝ) :
    Fin (m + 1) → Fin (m + 1) → ℝ :=
  fun i j =>
    if hj : j = Fin.last m then alpha * (2 : ℝ) ^ i.val
    else if hi : i = Fin.last m then 0
    else T (Fin.castPred i hi) (Fin.castPred j hj)

@[simp] theorem higham9_7_printedUpperBlock_lastCol {m : ℕ}
    (T : Fin m → Fin m → ℝ) (alpha : ℝ) (i : Fin (m + 1)) :
    higham9_7_printedUpperBlock T alpha i (Fin.last m) =
      alpha * (2 : ℝ) ^ i.val := by
  simp [higham9_7_printedUpperBlock]

@[simp] theorem higham9_7_printedUpperBlock_castSucc {m : ℕ}
    (T : Fin m → Fin m → ℝ) (alpha : ℝ) (i j : Fin m) :
    higham9_7_printedUpperBlock T alpha i.castSucc j.castSucc = T i j := by
  simp [higham9_7_printedUpperBlock]

/-- Equality in the global doubling bound descends to equality in both the
first Schur-complement bound and the tail source trace. -/
theorem higham9_7_extremal_step_descent {m : ℕ} (hm : 0 < m)
    {M S g₁ : ℝ} (hM : 0 < M)
    (hS_le : S ≤ 2 * M)
    (hg₁_le : g₁ ≤ (2 : ℝ) ^ (m - 1) * S)
    (hmax : max M g₁ = (2 : ℝ) ^ m * M) :
    g₁ = (2 : ℝ) ^ m * M ∧ S = 2 * M := by
  have hpow_gt_one : (1 : ℝ) < (2 : ℝ) ^ m := by
    have hpow := pow_lt_pow_right₀ (by norm_num : (1 : ℝ) < 2) hm
    simpa using hpow
  have hM_lt_target : M < (2 : ℝ) ^ m * M := by
    nlinarith
  have hg₁_eq : g₁ = (2 : ℝ) ^ m * M := by
    rcases max_choice M g₁ with hleft | hright
    · rw [hleft] at hmax
      linarith
    · calc
        g₁ = max M g₁ := hright.symm
        _ = (2 : ℝ) ^ m * M := hmax
  refine ⟨hg₁_eq, ?_⟩
  have hc_pos : 0 < (2 : ℝ) ^ (m - 1) := pow_pos (by norm_num) _
  have hpow : (2 : ℝ) ^ m = (2 : ℝ) ^ (m - 1) * 2 := by
    have hm_eq : m = (m - 1) + 1 := by omega
    calc
      (2 : ℝ) ^ m = (2 : ℝ) ^ ((m - 1) + 1) :=
        congrArg (fun k : ℕ => (2 : ℝ) ^ k) hm_eq
      _ = (2 : ℝ) ^ (m - 1) * 2 := pow_succ _ _
  have hlower : 2 * M ≤ S := by
    apply (mul_le_mul_iff_of_pos_left hc_pos).mp
    calc
      (2 : ℝ) ^ (m - 1) * (2 * M) = (2 : ℝ) ^ m * M := by
        rw [hpow]
        ring
      _ = g₁ := hg₁_eq.symm
      _ ≤ (2 : ℝ) ^ (m - 1) * S := hg₁_le
  exact le_antisymm hS_le hlower

/-- Equality of the source growth factor is exactly equality of its explicit
source-history numerator after clearing the positive initial norm. -/
theorem higham9_7_sourceReducedGrowthFactor_eq_pow_iff {m : ℕ}
    (A U : Fin (m + 1) → Fin (m + 1) → ℝ)
    (hApos : 0 < maxEntryNorm (Nat.succ_pos m) A) (g : ℝ)
    (htrace : higham9_7_LeadingTieGEPPTrace (m + 1) A U g) :
    higham9_7_sourceReducedGrowthFactor (Nat.succ_pos m) A U hApos g htrace =
        (2 : ℝ) ^ m ↔
      g = (2 : ℝ) ^ m * maxEntryNorm (Nat.succ_pos m) A := by
  unfold higham9_7_sourceReducedGrowthFactor
  rw [div_eq_iff (ne_of_gt hApos)]

/-- Changing the bookkeeping start counter does not change a no-interchange
trace. -/
theorem higham9_7_noInterchangeTrace_rebase :
    ∀ {t n : ℕ} {A : Fin n → Fin n → ℝ},
      higham9_7_PartialPivotNoInterchangeTrace t n A →
        ∀ s : ℕ, higham9_7_PartialPivotNoInterchangeTrace s n A := by
  intro t n A htrace
  induction htrace with
  | done =>
      intro s
      exact higham9_7_PartialPivotNoInterchangeTrace.done
  | step hchoice hpivot hnext ih =>
      intro s
      exact higham9_7_PartialPivotNoInterchangeTrace.step hchoice hpivot (ih (s + 1))

/-! ## The equality trace forces the complete `D M D` / power-column core -/

/-- Strong recursive core of Theorem 9.7.  Notice that the equality
hypothesis is on `g`, the maximum over all reduced matrices.  The final-`U`
power column, the `D M D` lower factor, and the absence of swaps are all
conclusions. -/
theorem higham9_7_extremal_sourceTrace_core :
    ∀ (m : ℕ) (A U : Fin (m + 1) → Fin (m + 1) → ℝ) (g : ℝ),
      higham9_7_LeadingTieGEPPTrace (m + 1) A U g →
      0 < maxEntryNorm (Nat.succ_pos m) A →
      g = (2 : ℝ) ^ m * maxEntryNorm (Nat.succ_pos m) A →
      ∃ (L : Fin (m + 1) → Fin (m + 1) → ℝ) (d : Fin (m + 1) → ℝ),
        LUFactSpec (m + 1) A L U ∧
        (∀ i, d i ^ 2 = 1) ∧
        L = higham9_7_signedExtremalLower d ∧
        (∀ i, U i (Fin.last m) =
          maxEntryNorm (Nat.succ_pos m) A * d i * (2 : ℝ) ^ i.val) ∧
        (∀ i, U i i ≠ 0) ∧
        higham9_7_PartialPivotNoInterchangeTrace 0 (m + 1) A := by
  intro m
  induction m with
  | zero =>
      intro A U g htrace hApos hg
      cases htrace with
      | step hchoice hpivot hnext =>
          rename_i g₁ r U₁
          have hr : r = (0 : Fin 1) := Fin.eq_zero r
          subst r
          cases hnext
          have hnorm : maxEntryNorm (Nat.succ_pos 0) A = |A 0 0| := by
            apply le_antisymm
            · apply maxEntryNorm_le_of_entry_le_bound (Nat.succ_pos 0) A |A 0 0|
              intro i j
              have hi : i = (0 : Fin 1) := Fin.eq_zero i
              have hj : j = (0 : Fin 1) := Fin.eq_zero j
              simp [hi, hj]
            · exact entry_le_maxEntryNorm (Nat.succ_pos 0) A 0 0
          have habs : |A 0 0| = maxEntryNorm (Nat.succ_pos 0) A := hnorm.symm
          have hMnonneg : 0 ≤ maxEntryNorm (Nat.succ_pos 0) A := le_of_lt hApos
          rcases (abs_eq hMnonneg).mp habs with hpos | hneg
          · let d : Fin 1 → ℝ := fun _ => 1
            let L : Fin 1 → Fin 1 → ℝ := higham9_7_signedExtremalLower d
            refine ⟨L, d, ?_, ?_, rfl, ?_, ?_, ?_⟩
            · refine
                { L_diag := ?_
                  L_upper_zero := ?_
                  U_lower_zero := ?_
                  product_eq := ?_ }
              · intro i
                exact higham9_7_signedExtremalLower_diag (fun _ => by simp [d]) i
              · intro i j hij
                omega
              · intro i j hij
                omega
              · intro i j
                have hi : i = (0 : Fin 1) := Fin.eq_zero i
                have hj : j = (0 : Fin 1) := Fin.eq_zero j
                subst i
                subst j
                simp [L, d, higham9_7_signedExtremalLower,
                  higham9_7_wilkinsonGrowthL, luFirstStepU, hpos,
                  higham9_2_rowPermutedMatrix, higham9_7_firstPivotRowSwap]
            · intro i
              simp [d]
            · intro i
              have hi : i = (0 : Fin 1) := Fin.eq_zero i
              subst i
              simpa [d, luFirstStepU, hpos]
            · intro i
              have hi : i = (0 : Fin 1) := Fin.eq_zero i
              subst i
              simpa [luFirstStepU] using hpivot
            · exact higham9_7_PartialPivotNoInterchangeTrace.step
                hchoice.1 hpivot higham9_7_PartialPivotNoInterchangeTrace.done
          · let d : Fin 1 → ℝ := fun _ => -1
            let L : Fin 1 → Fin 1 → ℝ := higham9_7_signedExtremalLower d
            refine ⟨L, d, ?_, ?_, rfl, ?_, ?_, ?_⟩
            · refine
                { L_diag := ?_
                  L_upper_zero := ?_
                  U_lower_zero := ?_
                  product_eq := ?_ }
              · intro i
                exact higham9_7_signedExtremalLower_diag (fun _ => by simp [d]) i
              · intro i j hij
                omega
              · intro i j hij
                omega
              · intro i j
                have hi : i = (0 : Fin 1) := Fin.eq_zero i
                have hj : j = (0 : Fin 1) := Fin.eq_zero j
                subst i
                subst j
                simp [L, d, higham9_7_signedExtremalLower,
                  higham9_7_wilkinsonGrowthL, luFirstStepU, hneg,
                  higham9_2_rowPermutedMatrix, higham9_7_firstPivotRowSwap]
            · intro i
              simp [d]
            · intro i
              have hi : i = (0 : Fin 1) := Fin.eq_zero i
              subst i
              simpa [d, luFirstStepU, hneg]
            · intro i
              have hi : i = (0 : Fin 1) := Fin.eq_zero i
              subst i
              simpa [luFirstStepU] using hpivot
            · exact higham9_7_PartialPivotNoInterchangeTrace.step
                hchoice.1 hpivot higham9_7_PartialPivotNoInterchangeTrace.done
  | succ k ih =>
      intro A U g htrace hApos hg
      cases htrace with
      | step hchoice hpivot hnext =>
          rename_i g₁ r U₁
          let sigma := higham9_7_firstPivotRowSwap r
          let Aperm := higham9_2_rowPermutedMatrix A sigma
          let S := luFirstSchurComplement Aperm
          let M := maxEntryNorm (Nat.succ_pos (k + 1)) A
          let MS := maxEntryNorm (Nat.succ_pos k) S
          have hSle : MS ≤ 2 * M := by
            simpa [MS, M, S, Aperm, sigma] using
              higham9_7_partialPivot_firstSchurComplement_maxEntryNorm_le_two
                (Nat.succ_pos k) A r hchoice.1 hpivot
          have hg₁le : g₁ ≤ (2 : ℝ) ^ k * MS := by
            simpa [MS, S, Aperm, sigma] using
              higham9_7_LeadingTieGEPPTrace_sourceMax_le_pow_two hnext
                (Nat.succ_pos k)
          have hdesc := higham9_7_extremal_step_descent
            (m := k + 1) (Nat.succ_pos k) (M := M) (S := MS) (g₁ := g₁)
            (by simpa [M] using hApos) hSle (by simpa using hg₁le) (by simpa [M] using hg)
          rcases hdesc with ⟨hg₁, hMS⟩
          have hMSpos : 0 < MS := by
            rw [hMS]
            have hMpos : 0 < M := by simpa [M] using hApos
            linarith
          have hg₁tail : g₁ = (2 : ℝ) ^ k * MS := by
            rw [hg₁, hMS]
            rw [pow_succ]
            ring
          obtain ⟨L₁, d₁, hLU₁, hd₁, hL₁, hU₁last, hU₁diag, hnoswap₁⟩ :=
            ih S U₁ g₁ hnext hMSpos hg₁tail
          have hSlast (i : Fin (k + 1)) :
              S i (Fin.last k) = MS * d₁ i := by
            rw [← hLU₁.product_eq i (Fin.last k)]
            calc
              (∑ x : Fin (k + 1), L₁ i x * U₁ x (Fin.last k)) =
                  ∑ x : Fin (k + 1),
                    higham9_7_signedExtremalLower d₁ i x *
                      (MS * d₁ x * (2 : ℝ) ^ x.val) := by
                apply Finset.sum_congr rfl
                intro x _hx
                rw [hL₁, hU₁last x]
              _ = MS * d₁ i :=
                higham9_7_signedExtremalLower_mul_powerColumn d₁ hd₁ MS i
          have hApermMax :
              maxEntryNorm (Nat.succ_pos (k + 1)) Aperm = M := by
            simpa [Aperm, M, sigma] using
              higham9_2_rowPermutedMatrix_maxEntryNorm
                (Nat.succ_pos (k + 1)) A
                (higham9_7_firstPivotRowSwap_isPermutation r)
          have hratio (i : Fin (k + 1)) :
              |Aperm i.succ 0 / Aperm 0 0| ≤ 1 := by
            have hraw :=
              higham9_1_partialPivot_multiplier_abs_le_one
                A (0 : Fin (k + 2)) r (sigma i.succ)
                hchoice.1 hpivot (Nat.zero_le _)
            simpa [Aperm, sigma, higham9_2_rowPermutedMatrix,
              higham9_7_firstPivotRowSwap] using hraw
          have htopBound : |Aperm 0 (Fin.last (k + 1))| ≤ M := by
            rw [← hApermMax]
            exact entry_le_maxEntryNorm (Nat.succ_pos (k + 1)) Aperm
              0 (Fin.last (k + 1))
          have hlocal (i : Fin (k + 1)) :
              Aperm i.succ (Fin.last (k + 1)) = M * d₁ i ∧
              (Aperm i.succ 0 / Aperm 0 0) * Aperm 0 (Fin.last (k + 1)) =
                -(M * d₁ i) := by
            have hx : |Aperm i.succ (Fin.last (k + 1))| ≤ M := by
              rw [← hApermMax]
              exact entry_le_maxEntryNorm (Nat.succ_pos (k + 1)) Aperm
                i.succ (Fin.last (k + 1))
            have hy :
                |(Aperm i.succ 0 / Aperm 0 0) *
                    Aperm 0 (Fin.last (k + 1))| ≤ M := by
              rw [abs_mul]
              calc
                |Aperm i.succ 0 / Aperm 0 0| *
                    |Aperm 0 (Fin.last (k + 1))| ≤
                    1 * |Aperm 0 (Fin.last (k + 1))| :=
                  mul_le_mul_of_nonneg_right (hratio i) (abs_nonneg _)
                _ ≤ 1 * M := mul_le_mul_of_nonneg_left htopBound zero_le_one
                _ = M := by ring
            have hxy :
                Aperm i.succ (Fin.last (k + 1)) -
                    (Aperm i.succ 0 / Aperm 0 0) *
                      Aperm 0 (Fin.last (k + 1)) =
                  2 * M * d₁ i := by
              have hs := hSlast i
              rw [hMS] at hs
              calc
                Aperm i.succ (Fin.last (k + 1)) -
                    (Aperm i.succ 0 / Aperm 0 0) *
                      Aperm 0 (Fin.last (k + 1)) =
                    Aperm i.succ (Fin.last (k + 1)) -
                      Aperm i.succ 0 * Aperm 0 (Fin.last (k + 1)) /
                        Aperm 0 0 := by
                  rw [div_eq_mul_inv, div_eq_mul_inv]
                  ring
                _ = 2 * M * d₁ i := by
                  simpa [S, luFirstSchurComplement] using hs
            exact higham9_7_sub_eq_two_mul_sign_rigidity
              (by simpa [M] using hApos) (hd₁ i) hx hy hxy
          have hd₁abs (i : Fin (k + 1)) : |d₁ i| = 1 := by
            rcases sq_eq_one_iff.mp (hd₁ i) with hi | hi <;> simp [hi]
          have htopAbs : |Aperm 0 (Fin.last (k + 1))| = M := by
            let i0 : Fin (k + 1) := 0
            have hyEq := (hlocal i0).2
            have hyAbs :
                |(Aperm i0.succ 0 / Aperm 0 0) *
                    Aperm 0 (Fin.last (k + 1))| = M := by
              rw [hyEq, abs_neg, abs_mul, hd₁abs]
              have hMnonneg : 0 ≤ M := by simpa [M] using le_of_lt hApos
              rw [abs_of_nonneg hMnonneg]
              ring
            have hprod :
                |Aperm i0.succ 0 / Aperm 0 0| *
                    |Aperm 0 (Fin.last (k + 1))| = M := by
              simpa [abs_mul] using hyAbs
            have hprod_le :
                |Aperm i0.succ 0 / Aperm 0 0| *
                    |Aperm 0 (Fin.last (k + 1))| ≤
                  |Aperm 0 (Fin.last (k + 1))| := by
              calc
                |Aperm i0.succ 0 / Aperm 0 0| *
                    |Aperm 0 (Fin.last (k + 1))| ≤
                    1 * |Aperm 0 (Fin.last (k + 1))| :=
                  mul_le_mul_of_nonneg_right (hratio i0) (abs_nonneg _)
                _ = |Aperm 0 (Fin.last (k + 1))| := by ring
            apply le_antisymm htopBound
            linarith
          have hd0_exists : ∃ d0 : ℝ,
              d0 ^ 2 = 1 ∧ Aperm 0 (Fin.last (k + 1)) = M * d0 := by
            have hMnonneg : 0 ≤ M := by simpa [M] using le_of_lt hApos
            rcases (abs_eq hMnonneg).mp htopAbs with hp | hn
            · exact ⟨1, by norm_num, by simpa using hp⟩
            · exact ⟨-1, by norm_num, by simpa using hn⟩
          obtain ⟨d0, hd0, htop⟩ := hd0_exists
          have hd0abs : |d0| = 1 := by
            rcases sq_eq_one_iff.mp hd0 with hd | hd <;> simp [hd]
          have hmult (i : Fin (k + 1)) :
              Aperm i.succ 0 / Aperm 0 0 = -(d₁ i * d0) := by
            have hyEq := (hlocal i).2
            rw [htop] at hyEq
            rcases sq_eq_one_iff.mp hd0 with hd | hd
            · subst d0
              apply mul_left_cancel₀ (ne_of_gt (by simpa [M] using hApos) : M ≠ 0)
              calc
                M * (Aperm i.succ 0 / Aperm 0 0) =
                    (Aperm i.succ 0 / Aperm 0 0) * M := by ring
                _ = -(M * d₁ i) := by simpa using hyEq
                _ = M * (-(d₁ i * 1)) := by ring
            · subst d0
              apply mul_left_cancel₀ (ne_of_gt (by simpa [M] using hApos) : M ≠ 0)
              calc
                M * (Aperm i.succ 0 / Aperm 0 0) =
                    -((Aperm i.succ 0 / Aperm 0 0) * (-M)) := by ring
                _ = -((Aperm i.succ 0 / Aperm 0 0) * (M * -1)) := by ring
                _ = -(-(M * d₁ i)) := by rw [hyEq]
                _ = M * d₁ i := by ring
                _ = M * (-(d₁ i * -1)) := by ring
          have hr0 : r = 0 := by
            by_contra hr
            let p : Fin (k + 1) := r.pred hr
            have hpsucc : p.succ = r := Fin.succ_pred r hr
            have habsRatio : |Aperm p.succ 0 / Aperm 0 0| = 1 := by
              rw [hmult p, abs_neg, abs_mul, hd₁abs, hd0abs]
              norm_num
            rw [abs_div] at habsRatio
            have hpivotPerm : Aperm 0 0 ≠ 0 := by
              simpa [Aperm, sigma, higham9_2_rowPermutedMatrix,
                higham9_7_firstPivotRowSwap] using hpivot
            have habsEq : |Aperm p.succ 0| = |Aperm 0 0| :=
              (div_eq_one_iff_eq (abs_ne_zero.mpr hpivotPerm)).mp habsRatio
            have htie : |A 0 0| = |A r 0| := by
              simpa [Aperm, sigma, higham9_2_rowPermutedMatrix,
                higham9_7_firstPivotRowSwap, hr, hpsucc] using habsEq
            exact hr (hchoice.2 htie)
          subst r
          have hpivotA : A 0 0 ≠ 0 := by
            simpa [Aperm, sigma, higham9_2_rowPermutedMatrix,
              higham9_7_firstPivotRowSwap] using hpivot
          have hLU₁A : LUFactSpec (k + 1) (luFirstSchurComplement A) L₁ U₁ := by
            simpa [S, Aperm, sigma, higham9_2_rowPermutedMatrix,
              higham9_7_firstPivotRowSwap] using hLU₁
          let d : Fin (k + 2) → ℝ := Fin.cases d0 d₁
          let L : Fin (k + 2) → Fin (k + 2) → ℝ := luFirstStepL A L₁
          have hd : ∀ i, d i ^ 2 = 1 := by
            intro i
            refine Fin.cases hd0 ?_ i
            intro p
            exact hd₁ p
          have hLU : LUFactSpec (k + 2) A L (luFirstStepU A U₁) := by
            have hstep := LUFactSpec.of_firstSchurComplement_explicit hpivotA hLU₁A
            simpa [L] using hstep
          have hd0mul : d0 * d0 = 1 := by simpa [pow_two] using hd0
          have hLform : L = higham9_7_signedExtremalLower d := by
            funext i j
            refine Fin.cases ?_ (fun p => ?_) i
            · refine Fin.cases ?_ (fun q => ?_) j
              · simp [L, d, luFirstStepL,
                  higham9_7_signedExtremalLower, higham9_7_wilkinsonGrowthL,
                  hd0mul]
              · simp [L, d, luFirstStepL, higham9_7_signedExtremalLower,
                  higham9_7_wilkinsonGrowthL]
            · refine Fin.cases ?_ (fun q => ?_) j
              · have hm := hmult p
                simpa [L, d, luFirstStepL, Aperm, sigma,
                  higham9_2_rowPermutedMatrix, higham9_7_firstPivotRowSwap,
                  higham9_7_signedExtremalLower, higham9_7_wilkinsonGrowthL]
                  using hm
              · have hentry := congrFun (congrFun hL₁ p) q
                simpa [L, d, luFirstStepL, higham9_7_signedExtremalLower,
                  higham9_7_wilkinsonGrowthL] using hentry
          have hUlast : ∀ i : Fin (k + 2),
              luFirstStepU A U₁ i (Fin.last (k + 1)) =
                M * d i * (2 : ℝ) ^ i.val := by
            intro i
            refine Fin.cases ?_ (fun p => ?_) i
            · simpa [d, Aperm, sigma, higham9_2_rowPermutedMatrix,
                higham9_7_firstPivotRowSwap, luFirstStepU] using htop
            · have htail := hU₁last p
              change U₁ p (Fin.last k) = MS * d₁ p * (2 : ℝ) ^ p.val at htail
              rw [hMS] at htail
              change U₁ p ((Fin.last (k + 1)).pred (by simp)) =
                M * d₁ p * (2 : ℝ) ^ p.succ.val
              rw [show (Fin.last (k + 1)).pred (by simp) = Fin.last k by
                apply Fin.ext
                simp [Fin.val_pred]]
              rw [htail]
              simp only [Fin.val_succ, pow_succ]
              ring
          have hUdiag : ∀ i : Fin (k + 2), luFirstStepU A U₁ i i ≠ 0 := by
            intro i
            refine Fin.cases ?_ (fun p => ?_) i
            · simpa [Aperm, sigma, higham9_2_rowPermutedMatrix,
                higham9_7_firstPivotRowSwap, luFirstStepU] using hpivotA
            · simpa [Aperm, sigma, higham9_2_rowPermutedMatrix,
                higham9_7_firstPivotRowSwap, luFirstStepU] using hU₁diag p
          have hnoswap :
              higham9_7_PartialPivotNoInterchangeTrace 0 (k + 2) A := by
            apply higham9_7_PartialPivotNoInterchangeTrace.step hchoice.1 hpivotA
            simpa [S, Aperm, sigma, higham9_2_rowPermutedMatrix,
              higham9_7_firstPivotRowSwap] using
                (higham9_7_noInterchangeTrace_rebase hnoswap₁ 1)
          simpa [Aperm, sigma, higham9_2_rowPermutedMatrix,
            higham9_7_firstPivotRowSwap] using
              (⟨L, d, hLU, hd, hLform, hUlast, hUdiag, hnoswap⟩ :
                ∃ (L : Fin (k + 2) → Fin (k + 2) → ℝ)
                    (d : Fin (k + 2) → ℝ),
                  LUFactSpec (k + 2) A L (luFirstStepU A U₁) ∧
                  (∀ i, d i ^ 2 = 1) ∧
                  L = higham9_7_signedExtremalLower d ∧
                  (∀ i, luFirstStepU A U₁ i (Fin.last (k + 1)) =
                    maxEntryNorm (Nat.succ_pos (k + 1)) A * d i *
                      (2 : ℝ) ^ i.val) ∧
                  (∀ i, luFirstStepU A U₁ i i ≠ 0) ∧
                  higham9_7_PartialPivotNoInterchangeTrace 0 (k + 2) A)

/-! ## Source-growth bridge and the literal printed classification -/

/-- Extremality of the source reduced-stage growth factor forces (rather
than assumes) extremality of the final upper factor. -/
theorem higham9_7_sourceReducedGrowth_extremal_implies_finalU_extremal
    {m : ℕ} (A U : Fin (m + 1) → Fin (m + 1) → ℝ)
    (hApos : 0 < maxEntryNorm (Nat.succ_pos m) A) (g : ℝ)
    (htrace : higham9_7_LeadingTieGEPPTrace (m + 1) A U g)
    (hgrowth :
      higham9_7_sourceReducedGrowthFactor (Nat.succ_pos m)
        A U hApos g htrace = (2 : ℝ) ^ m) :
    maxEntryNorm (Nat.succ_pos m) U =
      (2 : ℝ) ^ m * maxEntryNorm (Nat.succ_pos m) A := by
  have hg :=
    (higham9_7_sourceReducedGrowthFactor_eq_pow_iff A U hApos g htrace).mp hgrowth
  obtain ⟨L, d, hLU, hd, hL, hUlast, hUdiag, hnoswap⟩ :=
    higham9_7_extremal_sourceTrace_core m A U g htrace hApos hg
  apply le_antisymm
  · calc
      maxEntryNorm (Nat.succ_pos m) U ≤ g :=
        higham9_7_LeadingTieGEPPTrace_finalU_maxEntryNorm_le_sourceMax
          (Nat.succ_pos m) htrace
      _ = (2 : ℝ) ^ m * maxEntryNorm (Nat.succ_pos m) A := hg
  · have hdabs : |d (Fin.last m)| = 1 := by
      rcases sq_eq_one_iff.mp (hd (Fin.last m)) with h | h <;> simp [h]
    have hMnonneg : 0 ≤ maxEntryNorm (Nat.succ_pos m) A :=
      le_of_lt hApos
    have hentry :
        |U (Fin.last m) (Fin.last m)| =
          (2 : ℝ) ^ m * maxEntryNorm (Nat.succ_pos m) A := by
      rw [hUlast, abs_mul, abs_mul, hdabs, abs_pow,
        abs_of_nonneg hMnonneg]
      norm_num
      ring
    rw [← hentry]
    exact entry_le_maxEntryNorm (Nat.succ_pos m) U (Fin.last m) (Fin.last m)

/-- **Theorem 9.7 (Higham--Higham), source form.**

For a real nonsingular GEPP trace using the explicit convention "retain the
leading active row on a tie", source reduced-stage growth `2^(n-1)` forces
the literal printed form

`A = D M [ T | alpha d ; 0 | alpha*2^(n-1) ]`.

Here `D = diag(±1)`, `M` is unit lower with every strict-lower entry `-1`,
`T` is nonsingular upper triangular of order `n-1`,
`d = (1,2,4,...,2^(n-1))ᵀ`, and
`alpha = |a₁ₙ| = maxᵢⱼ |aᵢⱼ|`.  The conclusion also exposes the
source proof's fact that no row interchange occurs.  The statement includes
the exact `n=1` edge (`T` is the empty nonsingular upper matrix). -/
theorem higham9_7_source_extremal_classification
    {m : ℕ} (A U : Fin (m + 1) → Fin (m + 1) → ℝ)
    (hApos : 0 < maxEntryNorm (Nat.succ_pos m) A) (g : ℝ)
    (htrace : higham9_7_LeadingTieGEPPTrace (m + 1) A U g)
    (hgrowth :
      higham9_7_sourceReducedGrowthFactor (Nat.succ_pos m)
        A U hApos g htrace = (2 : ℝ) ^ m) :
    ∃ (alpha : ℝ) (D : Fin (m + 1) → ℝ)
        (T : Fin m → Fin m → ℝ),
      alpha = maxEntryNorm (Nat.succ_pos m) A ∧
      alpha = |A 0 (Fin.last m)| ∧
      (∀ i, D i ^ 2 = 1) ∧
      (∀ i j, j.val < i.val → T i j = 0) ∧
      Matrix.det (Matrix.of T : Matrix (Fin m) (Fin m) ℝ) ≠ 0 ∧
      (∀ i j,
        A i j = ∑ k : Fin (m + 1),
          (D i * higham9_7_extremalM i k) *
            higham9_7_printedUpperBlock T alpha k j) ∧
      higham9_7_PartialPivotNoInterchangeTrace 0 (m + 1) A := by
  have hg :=
    (higham9_7_sourceReducedGrowthFactor_eq_pow_iff A U hApos g htrace).mp hgrowth
  obtain ⟨L, D, hLU, hD, hL, hUlast, hUdiag, hnoswap⟩ :=
    higham9_7_extremal_sourceTrace_core m A U g htrace hApos hg
  let alpha := maxEntryNorm (Nat.succ_pos m) A
  let T : Fin m → Fin m → ℝ :=
    fun i j => D i.castSucc * U i.castSucc j.castSucc
  have hDU (i j : Fin (m + 1)) :
      D i * U i j = higham9_7_printedUpperBlock T alpha i j := by
    by_cases hj : j = Fin.last m
    · subst j
      rw [higham9_7_printedUpperBlock_lastCol, hUlast]
      have hDi := hD i
      simp only [pow_two] at hDi
      change D i * (alpha * D i * (2 : ℝ) ^ i.val) =
        alpha * (2 : ℝ) ^ i.val
      calc
        D i * (alpha * D i * (2 : ℝ) ^ i.val) =
            alpha * (D i * D i) * (2 : ℝ) ^ i.val := by ring
        _ = alpha * (2 : ℝ) ^ i.val := by rw [hDi]; ring
    · by_cases hi : i = Fin.last m
      · have hji : j.val < i.val := by
          subst i
          have hjne : j.val ≠ m := by
            intro h
            apply hj
            apply Fin.ext
            simpa using h
          have hjlt : j.val < m := by omega
          simpa using hjlt
        have hzero := hLU.U_lower_zero i j hji
        rw [hzero]
        simp [higham9_7_printedUpperBlock, hj, hi]
      · simp [higham9_7_printedUpperBlock, hj, hi, T]
  have hTupper : ∀ i j : Fin m, j.val < i.val → T i j = 0 := by
    intro i j hji
    have hzero := hLU.U_lower_zero i.castSucc j.castSucc (by simpa using hji)
    simp [T, hzero]
  have hTdiag : ∀ i : Fin m, T i i ≠ 0 := by
    intro i
    exact mul_ne_zero
      (by
        intro hzero
        have h := hD i.castSucc
        simp [hzero] at h)
      (hUdiag i.castSucc)
  have hTdet : Matrix.det (Matrix.of T : Matrix (Fin m) (Fin m) ℝ) ≠ 0 := by
    have htri : Matrix.BlockTriangular
        (M := (Matrix.of T : Matrix (Fin m) (Fin m) ℝ)) id := by
      intro i j hij
      exact hTupper i j (by simpa using hij)
    rw [Matrix.det_of_upperTriangular htri]
    simpa [Matrix.of_apply] using
      (Finset.prod_ne_zero_iff.mpr (fun i _hi => hTdiag i))
  have hAform : ∀ i j,
      A i j = ∑ k : Fin (m + 1),
        (D i * higham9_7_extremalM i k) *
          higham9_7_printedUpperBlock T alpha k j := by
    intro i j
    rw [← hLU.product_eq i j]
    apply Finset.sum_congr rfl
    intro k _hk
    rw [hL]
    unfold higham9_7_signedExtremalLower
    rw [← hDU k j]
    ring
  have hA0last : A 0 (Fin.last m) = alpha * D 0 := by
    rw [← hLU.product_eq 0 (Fin.last m)]
    calc
      (∑ k : Fin (m + 1), L 0 k * U k (Fin.last m)) =
          ∑ k : Fin (m + 1),
            higham9_7_signedExtremalLower D 0 k *
              (alpha * D k * (2 : ℝ) ^ k.val) := by
        apply Finset.sum_congr rfl
        intro k _hk
        rw [hL, hUlast]
      _ = alpha * D 0 :=
        higham9_7_signedExtremalLower_mul_powerColumn D hD alpha 0
  have hAlphaAbs : alpha = |A 0 (Fin.last m)| := by
    have hDabs : |D 0| = 1 := by
      rcases sq_eq_one_iff.mp (hD 0) with h | h <;> simp [h]
    rw [hA0last, abs_mul, hDabs, mul_one]
    exact (abs_of_pos (by simpa [alpha] using hApos)).symm
  exact ⟨alpha, D, T, rfl, hAlphaAbs, hD, hTupper, hTdet, hAform, hnoswap⟩



end NumStability
