import NumStability.Algorithms.HighamChapter9

namespace NumStability

open scoped BigOperators

/-!
# Complex-domain closure for Higham Theorems 9.8--9.11

Higham states Theorems 9.8--9.11 for matrices over `ℂ`.  The older chapter
surface contains the real GEPP developments used elsewhere in the repository.
This file supplies the source-domain endpoints: an arbitrary-permuted-LU
version of Theorem 9.8 and exact complex partial-pivoting traces for the three
structured classes in Theorems 9.9--9.11.  All growth quantities below are
formed from complex moduli; no real-specialization hypothesis is used.
-/

/-! ## Shared complex max-entry and partial-pivoting infrastructure -/

/-- Complex row diagonal dominance, with the source modulus convention. -/
def higham9_ComplexRowDiagDominant {n : ℕ}
    (A : Fin n → Fin n → ℂ) : Prop :=
  ∀ i : Fin n, (∑ j : Fin n, if i = j then 0 else ‖A i j‖) ≤ ‖A i i‖

/-- Complex column diagonal dominance, equivalently row dominance of `Aᴴ` at
the level of moduli. -/
def higham9_ComplexColDiagDominant {n : ℕ}
    (A : Fin n → Fin n → ℂ) : Prop :=
  ∀ j : Fin n, (∑ i : Fin n, if i = j then 0 else ‖A i j‖) ≤ ‖A j j‖

/-- Function-shaped complex transpose.  Conjugation is immaterial for the
diagonal-dominance and GE argument because every comparison uses `‖·‖`. -/
def higham9_complexTranspose {n : ℕ} (A : Fin n → Fin n → ℂ) :
    Fin n → Fin n → ℂ := fun i j => A j i

theorem higham9_complexRowDiagDominant_transpose_iff_colDiagDominant {n : ℕ}
    (A : Fin n → Fin n → ℂ) :
    higham9_ComplexRowDiagDominant (higham9_complexTranspose A) ↔
      higham9_ComplexColDiagDominant A := by
  constructor <;> intro h i <;>
    simpa [higham9_ComplexRowDiagDominant, higham9_ComplexColDiagDominant,
      higham9_complexTranspose, eq_comm] using h i

/-- A complex partial-pivoting choice maximizes the modulus in the first
active column. -/
def higham9_complexPartialPivotChoice {m : ℕ}
    (A : Fin (m + 1) → Fin (m + 1) → ℂ) (r : Fin (m + 1)) : Prop :=
  ∀ i : Fin (m + 1), ‖A i 0‖ ≤ ‖A r 0‖

theorem higham9_exists_complexPartialPivotChoice {m : ℕ}
    (A : Fin (m + 1) → Fin (m + 1) → ℂ) :
    ∃ r : Fin (m + 1), higham9_complexPartialPivotChoice A r := by
  classical
  obtain ⟨r, _hr, hmax⟩ :=
    Finset.exists_max_image (Finset.univ : Finset (Fin (m + 1)))
      (fun i : Fin (m + 1) => ‖A i 0‖) (Finset.univ_nonempty_iff.mpr ⟨0⟩)
  exact ⟨r, fun i => hmax i (Finset.mem_univ i)⟩

theorem higham9_complexPartialPivotChoice_pivot_ne_zero_of_column {m : ℕ}
    (A : Fin (m + 1) → Fin (m + 1) → ℂ) (r : Fin (m + 1))
    (hchoice : higham9_complexPartialPivotChoice A r)
    (hcol : ∃ i : Fin (m + 1), A i 0 ≠ 0) : A r 0 ≠ 0 := by
  obtain ⟨i, hi⟩ := hcol
  intro hr
  have hle : ‖A i 0‖ ≤ 0 := by simpa [hr] using hchoice i
  exact hi (norm_eq_zero.mp (le_antisymm hle (norm_nonneg _)))

theorem higham9_complexPartialPivot_multiplier_norm_le_one {m : ℕ}
    (A : Fin (m + 1) → Fin (m + 1) → ℂ) (r i : Fin (m + 1))
    (hchoice : higham9_complexPartialPivotChoice A r)
    (hpivot : A r 0 ≠ 0) :
    ‖A i 0 / A r 0‖ ≤ 1 := by
  have hden : 0 < ‖A r 0‖ := norm_pos_iff.mpr hpivot
  rw [norm_div, div_le_iff₀ hden]
  simpa using hchoice i

/-- Row permutation that exposes the selected complex partial pivot. -/
def higham9_complexRowPermuted {n : ℕ} (A : Fin n → Fin n → ℂ)
    (σ : Fin n → Fin n) : Fin n → Fin n → ℂ := fun i j => A (σ i) j

/-- The exact first active matrix after selecting row `r`, swapping it with
row zero, and performing one complex Schur-complement update. -/
noncomputable def higham9_complexPartialSchur {m : ℕ}
    (A : Fin (m + 1) → Fin (m + 1) → ℂ) (r : Fin (m + 1)) :
    Fin m → Fin m → ℂ :=
  higham9_8_complexFirstSchurComplement
    (higham9_complexRowPermuted A (higham9_7_firstPivotRowSwap r))

/-- Complex max-entry growth formed from a final/reduced complex matrix. -/
noncomputable def higham9_complexGrowthFactor {n : ℕ} (hn : 0 < n)
    (A G : Fin n → Fin n → ℂ) : ℝ :=
  higham9_13_complexMaxEntryNorm hn G /
    higham9_13_complexMaxEntryNorm hn A

lemma higham9_complexMaxEntryNorm_pos_of_det_ne_zero {n : ℕ} (hn : 0 < n)
    (A : Fin n → Fin n → ℂ)
    (hdet : Matrix.det (Matrix.of A : Matrix (Fin n) (Fin n) ℂ) ≠ 0) :
    0 < higham9_13_complexMaxEntryNorm hn A := by
  have hnonneg := higham9_13_complexMaxEntryNorm_nonneg hn A
  rw [lt_iff_le_and_ne]
  refine ⟨hnonneg, ?_⟩
  intro hzero
  have hall : ∀ i j : Fin n, A i j = 0 := by
    intro i j
    apply norm_eq_zero.mp
    apply le_antisymm
    · exact le_trans
        (higham9_13_entry_norm_le_complexMaxEntryNorm hn A i j)
        (le_of_eq hzero.symm)
    · exact norm_nonneg _
  apply hdet
  have hmat : (Matrix.of A : Matrix (Fin n) (Fin n) ℂ) = 0 := by
    ext i j
    exact hall i j
  letI : Nonempty (Fin n) := ⟨⟨0, hn⟩⟩
  rw [hmat, Matrix.det_zero]
  exact ⟨⟨0, hn⟩⟩

/-! ## Theorem 9.8: arbitrary `P A Q = L U`, over `ℂ` -/

/-- The source `θ ≤ n` statement over `ℂ`, with the inverse exposed by its
right-inverse identity. -/
theorem higham9_8_complex_theta_le_card_of_rightInverse {n : ℕ} (hn : 0 < n)
    (A A_inv : Fin n → Fin n → ℂ)
    (hRight : higham9_8_ComplexIsRightInverse n A A_inv)
    (hA : 0 < higham9_13_complexMaxEntryNorm hn A)
    (hAinv : 0 < higham9_13_complexMaxEntryNorm hn A_inv) :
    1 / (higham9_13_complexMaxEntryNorm hn A *
      higham9_13_complexMaxEntryNorm hn A_inv) ≤ (n : ℝ) := by
  exact higham9_8_theta_le_card_complex hn A A_inv ⟨0, hn⟩ hA hAinv
    (hRight ⟨0, hn⟩ ⟨0, hn⟩)

/-- **Higham Theorem 9.8, complex and source-strength.**  For *any* row and
column permutations whose permuted matrix has the displayed exact LU
factorization, its GE-without-pivoting upper factor has growth at least
`θ = (max |A| max |A⁻¹|)⁻¹`.  No complete-pivoting choice is assumed. -/
theorem higham9_8_complex_growth_factor_ge_theta_of_permutedLU {n : ℕ}
    (hn : 0 < n)
    (A A_inv L U : Fin n → Fin n → ℂ)
    (sigma tau : Fin n → Fin n)
    (hLU : higham9_8_ComplexCompletePermutedLUFactSpec n A L U sigma tau)
    (hRight : higham9_8_ComplexIsRightInverse n A A_inv)
    (hA : 0 < higham9_13_complexMaxEntryNorm hn A)
    (hAinv : 0 < higham9_13_complexMaxEntryNorm hn A_inv) :
    1 / (higham9_13_complexMaxEntryNorm hn A *
      higham9_13_complexMaxEntryNorm hn A_inv) ≤
      higham9_complexGrowthFactor hn A U := by
  cases n with
  | zero => exact (Nat.not_lt_zero 0 hn).elim
  | succ m =>
      let last : Fin (m + 1) := Fin.last m
      let u : ℂ := U last last
      have hprod : u * A_inv (tau last) (sigma last) = 1 := by
        simpa [u, last] using
          higham9_8_complex_finalPivot_mul_inverse_entry_eq_one_of_completePermutedLUFactSpec
            A A_inv L U sigma tau hLU hRight
      have hu : u ≠ 0 := by
        intro hz
        rw [hz] at hprod
        norm_num at hprod
      have huEntry :
          ‖u‖ ≤ higham9_13_complexMaxEntryNorm (Nat.succ_pos m) U := by
        exact higham9_13_entry_norm_le_complexMaxEntryNorm
          (Nat.succ_pos m) U last last
      have huInv : u⁻¹ = A_inv (tau last) (sigma last) :=
        (eq_inv_of_mul_eq_one_right hprod).symm
      simpa [higham9_complexGrowthFactor] using
        higham9_8_complexGrowthFactorEntry_ge_inverse_entry_theta
          (Nat.succ_pos m) A A_inv U hA hAinv u
          (norm_pos_iff.mpr hu) huEntry
          ⟨tau last, sigma last, huInv⟩

/-- The complete source package for Theorem 9.8 over `ℂ`: both `θ ≤ n` and
the universal lower bound for an arbitrary admissible `P,Q,LU` certificate. -/
theorem higham9_8_complex_source_theorem {n : ℕ} (hn : 0 < n)
    (A A_inv L U : Fin n → Fin n → ℂ)
    (sigma tau : Fin n → Fin n)
    (hLU : higham9_8_ComplexCompletePermutedLUFactSpec n A L U sigma tau)
    (hRight : higham9_8_ComplexIsRightInverse n A A_inv)
    (hA : 0 < higham9_13_complexMaxEntryNorm hn A)
    (hAinv : 0 < higham9_13_complexMaxEntryNorm hn A_inv) :
    1 / (higham9_13_complexMaxEntryNorm hn A *
        higham9_13_complexMaxEntryNorm hn A_inv) ≤ (n : ℝ) ∧
      1 / (higham9_13_complexMaxEntryNorm hn A *
        higham9_13_complexMaxEntryNorm hn A_inv) ≤
        higham9_complexGrowthFactor hn A U :=
  ⟨higham9_8_complex_theta_le_card_of_rightInverse hn A A_inv hRight hA hAinv,
    higham9_8_complex_growth_factor_ge_theta_of_permutedLU
      hn A A_inv L U sigma tau hLU hRight hA hAinv⟩

/-! ## Exact complex GEPP trace, including singular zero-column skips -/

/-- Exact complex partial-pivoting elimination trace.  `pivot` performs the
actual row swap and Schur update.  `skip` is Higham's prescribed singular
case: when the whole active pivot column is zero, elimination of that column
is skipped and GE continues on the trailing submatrix. -/
inductive higham9_ComplexPartialPivotGEPPUTrace :
    (n : ℕ) → (Fin n → Fin n → ℂ) → (Fin n → Fin n → ℂ) → Prop
  | done {A U : Fin 0 → Fin 0 → ℂ} :
      higham9_ComplexPartialPivotGEPPUTrace 0 A U
  | pivot {m : ℕ} {A : Fin (m + 1) → Fin (m + 1) → ℂ}
      {r : Fin (m + 1)} {U₁ : Fin m → Fin m → ℂ}
      (hchoice : higham9_complexPartialPivotChoice A r)
      (hpivot : A r 0 ≠ 0)
      (hnext : higham9_ComplexPartialPivotGEPPUTrace m
        (higham9_complexPartialSchur A r) U₁) :
      higham9_ComplexPartialPivotGEPPUTrace (m + 1) A
        (higham9_8_complexLUFirstStepU
          (higham9_complexRowPermuted A (higham9_7_firstPivotRowSwap r)) U₁)
  | skip {m : ℕ} {A : Fin (m + 1) → Fin (m + 1) → ℂ}
      {U₁ : Fin m → Fin m → ℂ}
      (hzero : ∀ i : Fin (m + 1), A i 0 = 0)
      (hnext : higham9_ComplexPartialPivotGEPPUTrace m
        (fun i j => A i.succ j.succ) U₁) :
      higham9_ComplexPartialPivotGEPPUTrace (m + 1) A
        (higham9_8_complexLUFirstStepU A U₁)

/-- Every complex matrix, singular or nonsingular, has an exact GEPP trace.
This is a finite classical executor: it chooses a maximum-modulus pivot when
the first active column is nonzero and otherwise records the zero-column skip. -/
theorem higham9_exists_ComplexPartialPivotGEPPUTrace :
    ∀ {n : ℕ} (A : Fin n → Fin n → ℂ),
      ∃ U : Fin n → Fin n → ℂ,
        higham9_ComplexPartialPivotGEPPUTrace n A U := by
  intro n
  induction n with
  | zero =>
      intro A
      exact ⟨A, higham9_ComplexPartialPivotGEPPUTrace.done⟩
  | succ m ih =>
      intro A
      classical
      by_cases hcol : ∃ i : Fin (m + 1), A i 0 ≠ 0
      · obtain ⟨r, hchoice⟩ := higham9_exists_complexPartialPivotChoice A
        have hpivot :=
          higham9_complexPartialPivotChoice_pivot_ne_zero_of_column
            A r hchoice hcol
        obtain ⟨U₁, hnext⟩ := ih (higham9_complexPartialSchur A r)
        exact
          ⟨higham9_8_complexLUFirstStepU
            (higham9_complexRowPermuted A (higham9_7_firstPivotRowSwap r)) U₁,
            higham9_ComplexPartialPivotGEPPUTrace.pivot
              hchoice hpivot hnext⟩
      · push_neg at hcol
        obtain ⟨U₁, hnext⟩ := ih (fun i j => A i.succ j.succ)
        exact ⟨higham9_8_complexLUFirstStepU A U₁,
          higham9_ComplexPartialPivotGEPPUTrace.skip hcol hnext⟩

theorem higham9_ComplexPartialPivotGEPPUTrace_upper_zero :
    ∀ {n : ℕ} {A U : Fin n → Fin n → ℂ},
      higham9_ComplexPartialPivotGEPPUTrace n A U →
      ∀ i j : Fin n, j.val < i.val → U i j = 0 := by
  intro n A U htrace
  induction htrace with
  | done => intro i; exact Fin.elim0 i
  | pivot _hchoice _hpivot _hnext ih =>
      intro i j hij
      by_cases hi : i = 0
      · subst i; exact (Nat.not_lt_zero _ hij).elim
      · by_cases hj : j = 0
        · subst j; simp [higham9_8_complexLUFirstStepU, hi]
        · have hpred : (j.pred hj).val < (i.pred hi).val := by
            have hival := Fin.val_pred i hi
            have hjval := Fin.val_pred j hj
            have hi0 : i.val ≠ 0 := fun h => hi (Fin.ext h)
            have hj0 : j.val ≠ 0 := fun h => hj (Fin.ext h)
            omega
          simpa [higham9_8_complexLUFirstStepU, hi, hj] using
            ih (i.pred hi) (j.pred hj) hpred
  | skip _hzero _hnext ih =>
      intro i j hij
      by_cases hi : i = 0
      · subst i; exact (Nat.not_lt_zero _ hij).elim
      · by_cases hj : j = 0
        · subst j; simp [higham9_8_complexLUFirstStepU, hi]
        · have hpred : (j.pred hj).val < (i.pred hi).val := by
            have hival := Fin.val_pred i hi
            have hjval := Fin.val_pred j hj
            have hi0 : i.val ≠ 0 := fun h => hi (Fin.ext h)
            have hj0 : j.val ≠ 0 := fun h => hj (Fin.ext h)
            omega
          simpa [higham9_8_complexLUFirstStepU, hi, hj] using
            ih (i.pred hi) (j.pred hj) hpred

/-- A certificate that *every active reduced matrix* in an exact complex GEPP
trace is bounded entrywise by `C`.  This is the literal source-history notion
behind Higham's `max_{i,j,k}|aᵢⱼ⁽ᵏ⁾|`, whereas the final-`U` quotient is only
its convenient terminal consequence. -/
inductive higham9_ComplexGEPPActiveHistoryBound (C : ℝ) :
    {n : ℕ} → {A U : Fin n → Fin n → ℂ} →
      higham9_ComplexPartialPivotGEPPUTrace n A U → Prop
  | done {A U : Fin 0 → Fin 0 → ℂ} :
      higham9_ComplexGEPPActiveHistoryBound C
        (higham9_ComplexPartialPivotGEPPUTrace.done (A := A) (U := U))
  | pivot {m : ℕ} {A : Fin (m + 1) → Fin (m + 1) → ℂ}
      {r : Fin (m + 1)} {U₁ : Fin m → Fin m → ℂ}
      {hchoice : higham9_complexPartialPivotChoice A r}
      {hpivot : A r 0 ≠ 0}
      {hnext : higham9_ComplexPartialPivotGEPPUTrace m
        (higham9_complexPartialSchur A r) U₁}
      (hcurrent : ∀ i j : Fin (m + 1), ‖A i j‖ ≤ C)
      (hnextBound : higham9_ComplexGEPPActiveHistoryBound C hnext) :
      higham9_ComplexGEPPActiveHistoryBound C
        (higham9_ComplexPartialPivotGEPPUTrace.pivot
          hchoice hpivot hnext)
  | skip {m : ℕ} {A : Fin (m + 1) → Fin (m + 1) → ℂ}
      {U₁ : Fin m → Fin m → ℂ}
      {hzero : ∀ i : Fin (m + 1), A i 0 = 0}
      {hnext : higham9_ComplexPartialPivotGEPPUTrace m
        (fun i j => A i.succ j.succ) U₁}
      (hcurrent : ∀ i j : Fin (m + 1), ‖A i j‖ ≤ C)
      (hnextBound : higham9_ComplexGEPPActiveHistoryBound C hnext) :
      higham9_ComplexGEPPActiveHistoryBound C
        (higham9_ComplexPartialPivotGEPPUTrace.skip hzero hnext)

theorem higham9_ComplexGEPPActiveHistoryBound_current {C : ℝ} :
    ∀ {n : ℕ} {A U : Fin n → Fin n → ℂ}
      {htrace : higham9_ComplexPartialPivotGEPPUTrace n A U},
      higham9_ComplexGEPPActiveHistoryBound C htrace →
      ∀ i j : Fin n, ‖A i j‖ ≤ C := by
  intro n A U htrace hbound
  cases hbound with
  | done => intro i; exact Fin.elim0 i
  | pivot hcurrent _ => exact hcurrent
  | skip hcurrent _ => exact hcurrent

/-! ## Theorem 9.10: complex upper-Hessenberg GEPP -/

def higham9_10_ComplexUpperHessenberg {n : ℕ}
    (A : Fin n → Fin n → ℂ) : Prop :=
  ∀ i j : Fin n, j.val + 1 < i.val → A i j = 0

def higham9_10_ComplexHessenbergStageBound {n : ℕ}
    (M : ℝ) (k : ℕ) (A : Fin n → Fin n → ℂ) : Prop :=
  (∀ i j : Fin n, i.val = 0 → ‖A i j‖ ≤ (k : ℝ) * M) ∧
    (∀ i j : Fin n, 1 ≤ i.val → ‖A i j‖ ≤ M)

lemma higham9_10_complex_hessenberg_pivot_row_le_one {m : ℕ}
    {A : Fin (m + 1) → Fin (m + 1) → ℂ} {r : Fin (m + 1)}
    (hH : higham9_10_ComplexUpperHessenberg A) (hpivot : A r 0 ≠ 0) :
    r.val ≤ 1 := by
  by_contra h
  have hr : 1 < r.val := Nat.lt_of_not_ge h
  exact hpivot (hH r 0 (by simpa using hr))

lemma higham9_10_complex_partialSchur_tail {m : ℕ}
    {A : Fin (m + 1) → Fin (m + 1) → ℂ} {r : Fin (m + 1)}
    (hH : higham9_10_ComplexUpperHessenberg A) (hr : r.val ≤ 1)
    {i j : Fin m} (hi : 1 ≤ i.val) :
    higham9_complexPartialSchur A r i j = A i.succ j.succ := by
  have hswap : higham9_7_firstPivotRowSwap r i.succ = i.succ :=
    higham9_10_hessenberg_firstPivotRowSwap_tail hr hi
  have hbelow : (0 : Fin (m + 1)).val + 1 < i.succ.val := by
    simp only [Fin.val_zero, Fin.val_succ]
    omega
  have hzero : A i.succ 0 = 0 := hH i.succ 0 hbelow
  simp [higham9_complexPartialSchur, higham9_8_complexFirstSchurComplement,
    higham9_complexRowPermuted, hswap, hzero]

lemma higham9_10_complex_partialSchur_upperHessenberg {m : ℕ}
    {A : Fin (m + 1) → Fin (m + 1) → ℂ} {r : Fin (m + 1)}
    (hH : higham9_10_ComplexUpperHessenberg A) (hpivot : A r 0 ≠ 0) :
    higham9_10_ComplexUpperHessenberg (higham9_complexPartialSchur A r) := by
  intro i j hij
  have hr := higham9_10_complex_hessenberg_pivot_row_le_one hH hpivot
  by_cases hi : 1 ≤ i.val
  · rw [higham9_10_complex_partialSchur_tail hH hr hi]
    apply hH
    simp only [Fin.val_succ]
    omega
  · omega

lemma higham9_10_complex_partialSchur_stageBound {m k : ℕ} {M : ℝ}
    {A : Fin (m + 1) → Fin (m + 1) → ℂ} {r : Fin (m + 1)}
    (hH : higham9_10_ComplexUpperHessenberg A)
    (hstage : higham9_10_ComplexHessenbergStageBound M k A)
    (hchoice : higham9_complexPartialPivotChoice A r)
    (hpivot : A r 0 ≠ 0) :
    higham9_10_ComplexHessenbergStageBound M (k + 1)
      (higham9_complexPartialSchur A r) := by
  let σ := higham9_7_firstPivotRowSwap r
  let B := higham9_complexRowPermuted A σ
  have hr : r.val ≤ 1 :=
    higham9_10_complex_hessenberg_pivot_row_le_one hH hpivot
  have hratio : ∀ x : Fin (m + 1), ‖B x 0 / B 0 0‖ ≤ 1 := by
    intro x
    have hraw := higham9_complexPartialPivot_multiplier_norm_le_one
      A r (σ x) hchoice hpivot
    simpa [B, higham9_complexRowPermuted, σ, higham9_7_firstPivotRowSwap] using hraw
  constructor
  · intro i j hi0
    have hsplit :
        ‖higham9_complexPartialSchur A r i j‖ ≤
          ‖B i.succ j.succ‖ + ‖B 0 j.succ‖ := by
      have hterm :
          ‖B i.succ 0 * B 0 j.succ / B 0 0‖ ≤ ‖B 0 j.succ‖ := by
        have heq : B i.succ 0 * B 0 j.succ / B 0 0 =
            (B i.succ 0 / B 0 0) * B 0 j.succ := by ring
        rw [heq, norm_mul]
        simpa using mul_le_mul_of_nonneg_right (hratio i.succ)
          (norm_nonneg (B 0 j.succ))
      calc
        ‖higham9_complexPartialSchur A r i j‖ =
            ‖B i.succ j.succ - B i.succ 0 * B 0 j.succ / B 0 0‖ := rfl
        _ ≤ ‖B i.succ j.succ‖ +
              ‖B i.succ 0 * B 0 j.succ / B 0 0‖ :=
            norm_sub_le _ _
        _ ≤ ‖B i.succ j.succ‖ + ‖B 0 j.succ‖ :=
            add_le_add (le_refl _) hterm
    by_cases hr0 : r = 0
    · have hs1 : σ i.succ = i.succ := by
        simp [σ, higham9_7_firstPivotRowSwap, hr0]
      have hs0 : σ (0 : Fin (m + 1)) = 0 := by
        simp [σ, higham9_7_firstPivotRowSwap, hr0]
      have htail : ‖B i.succ j.succ‖ ≤ M := by
        simpa [B, higham9_complexRowPermuted, hs1] using
          hstage.2 i.succ j.succ (by simp)
      have hlead : ‖B 0 j.succ‖ ≤ (k : ℝ) * M := by
        simpa [B, higham9_complexRowPermuted, hs0] using
          hstage.1 (0 : Fin (m + 1)) j.succ rfl
      calc
        ‖higham9_complexPartialSchur A r i j‖
            ≤ ‖B i.succ j.succ‖ + ‖B 0 j.succ‖ := hsplit
        _ ≤ M + (k : ℝ) * M := add_le_add htail hlead
        _ = ((k + 1 : ℕ) : ℝ) * M := by push_cast; ring
    · have hrval : r.val = 1 := by
        have : r.val ≠ 0 := fun h => hr0 (Fin.ext h)
        omega
      have hs1 : σ i.succ = 0 := by
        have heq : i.succ = r := Fin.ext (by simp only [Fin.val_succ]; omega)
        simp [σ, higham9_7_firstPivotRowSwap, heq]
      have hs0 : σ (0 : Fin (m + 1)) = r := by
        simp [σ, higham9_7_firstPivotRowSwap]
      have hlead : ‖B i.succ j.succ‖ ≤ (k : ℝ) * M := by
        simpa [B, higham9_complexRowPermuted, hs1] using
          hstage.1 (0 : Fin (m + 1)) j.succ rfl
      have htail : ‖B 0 j.succ‖ ≤ M := by
        simpa [B, higham9_complexRowPermuted, hs0] using
          hstage.2 r j.succ (by omega)
      calc
        ‖higham9_complexPartialSchur A r i j‖
            ≤ ‖B i.succ j.succ‖ + ‖B 0 j.succ‖ := hsplit
        _ ≤ (k : ℝ) * M + M := add_le_add hlead htail
        _ = ((k + 1 : ℕ) : ℝ) * M := by push_cast; ring
  · intro i j hi
    rw [higham9_10_complex_partialSchur_tail hH hr hi]
    exact hstage.2 i.succ j.succ (by simp)

lemma higham9_10_complex_skip_upperHessenberg {m : ℕ}
    {A : Fin (m + 1) → Fin (m + 1) → ℂ}
    (hH : higham9_10_ComplexUpperHessenberg A) :
    higham9_10_ComplexUpperHessenberg (fun i j => A i.succ j.succ) := by
  intro i j hij
  apply hH
  simp only [Fin.val_succ]
  omega

lemma higham9_10_complex_skip_stageBound {m k : ℕ} {M : ℝ}
    (hM : 0 ≤ M) (hk : 0 < k)
    {A : Fin (m + 1) → Fin (m + 1) → ℂ}
    (hstage : higham9_10_ComplexHessenbergStageBound M k A) :
    higham9_10_ComplexHessenbergStageBound M (k + 1)
      (fun i j => A i.succ j.succ) := by
  constructor
  · intro i j _hi
    have htail := hstage.2 i.succ j.succ (by simp)
    have hcoef : (1 : ℝ) ≤ (k + 1 : ℕ) := by exact_mod_cast (by omega : 1 ≤ k + 1)
    calc
      ‖A i.succ j.succ‖ ≤ M := htail
      _ = 1 * M := by ring
      _ ≤ ((k + 1 : ℕ) : ℝ) * M :=
        mul_le_mul_of_nonneg_right hcoef hM
  · intro i j _hi
    exact hstage.2 i.succ j.succ (by simp)

lemma higham9_10_complex_initialStageBound {n : ℕ} (hn : 0 < n)
    (A : Fin n → Fin n → ℂ) :
    higham9_10_ComplexHessenbergStageBound
      (higham9_13_complexMaxEntryNorm hn A) 1 A := by
  constructor
  · intro i j _hi
    simpa using higham9_13_entry_norm_le_complexMaxEntryNorm hn A i j
  · intro i j _hi
    exact higham9_13_entry_norm_le_complexMaxEntryNorm hn A i j

/-- Modulus-envelope theorem for the actual complex GEPP trace.  Starting at
source stage `k`, exposed upper row `i` is bounded by `(k+i)M`.  Both genuine
complex Schur updates and singular zero-column skips are covered. -/
theorem higham9_10_ComplexPartialPivotGEPPUTrace_entry_norm_le_hessenberg :
    ∀ {n : ℕ} {A U : Fin n → Fin n → ℂ},
      higham9_ComplexPartialPivotGEPPUTrace n A U →
      ∀ (M : ℝ) (k : ℕ), 0 ≤ M → 0 < k →
        higham9_10_ComplexUpperHessenberg A →
        higham9_10_ComplexHessenbergStageBound M k A →
        ∀ i j : Fin n, ‖U i j‖ ≤ ((k + i.val : ℕ) : ℝ) * M := by
  intro n A U htrace
  induction htrace with
  | done =>
      intro M k hM hk hH hstage i
      exact Fin.elim0 i
  | pivot hchoice hpivot hnext ih =>
      rename_i m A r U₁
      intro M k hM hk hH hstage i j
      let σ := higham9_7_firstPivotRowSwap r
      let B := higham9_complexRowPermuted A σ
      by_cases hi : i = 0
      · subst i
        have hrle := higham9_10_complex_hessenberg_pivot_row_le_one hH hpivot
        have hpivrow : ‖B 0 j‖ ≤ (k : ℝ) * M := by
          by_cases hr0 : r = 0
          · simpa [B, higham9_complexRowPermuted, σ,
              higham9_7_firstPivotRowSwap, hr0] using
              hstage.1 (0 : Fin (m + 1)) j rfl
          · have hrpos : 1 ≤ r.val := by
              have : r.val ≠ 0 := fun h => hr0 (Fin.ext h)
              omega
            have htail : ‖A r j‖ ≤ M := hstage.2 r j hrpos
            have hkR : (1 : ℝ) ≤ (k : ℝ) := by exact_mod_cast hk
            have hMle : M ≤ (k : ℝ) * M := by
              calc M = 1 * M := by ring
                _ ≤ (k : ℝ) * M := mul_le_mul_of_nonneg_right hkR hM
            exact le_trans
              (by simpa [B, higham9_complexRowPermuted, σ,
                higham9_7_firstPivotRowSwap] using htail) hMle
        simpa [higham9_8_complexLUFirstStepU, B, σ] using hpivrow
      · by_cases hj : j = 0
        · subst j
          have hnonneg : 0 ≤ ((k + i.val : ℕ) : ℝ) * M :=
            mul_nonneg (Nat.cast_nonneg _) hM
          simpa [higham9_8_complexLUFirstStepU, hi] using hnonneg
        · have hHnext :=
            higham9_10_complex_partialSchur_upperHessenberg hH hpivot
          have hstagenext :=
            higham9_10_complex_partialSchur_stageBound hH hstage
              hchoice hpivot
          have hrec := ih M (k + 1) hM (by omega) hHnext hstagenext
            (i.pred hi) (j.pred hj)
          have hidx : (k + 1) + (i.pred hi).val = k + i.val := by
            have hip := Fin.val_pred i hi
            have hi0 : i.val ≠ 0 := fun h => hi (Fin.ext h)
            omega
          have hcast :
              (((k + 1) + (i.pred hi).val : ℕ) : ℝ) =
                ((k + i.val : ℕ) : ℝ) := by exact_mod_cast hidx
          rw [hcast] at hrec
          simpa [higham9_8_complexLUFirstStepU, hi, hj] using hrec

  | skip hzero hnext ih =>
      rename_i m A U₁
      intro M k hM hk hH hstage i j
      by_cases hi : i = 0
      · subst i
        have htop := hstage.1 (0 : Fin (m + 1)) j rfl
        simpa [higham9_8_complexLUFirstStepU] using htop
      · by_cases hj : j = 0
        · subst j
          have hnonneg : 0 ≤ ((k + i.val : ℕ) : ℝ) * M :=
            mul_nonneg (Nat.cast_nonneg _) hM
          simpa [higham9_8_complexLUFirstStepU, hi] using hnonneg
        · have hHnext := higham9_10_complex_skip_upperHessenberg hH
          have hstagenext := higham9_10_complex_skip_stageBound hM hk hstage
          have hrec := ih M (k + 1) hM (by omega) hHnext hstagenext
            (i.pred hi) (j.pred hj)
          have hidx : (k + 1) + (i.pred hi).val = k + i.val := by
            have hip := Fin.val_pred i hi
            have hi0 : i.val ≠ 0 := fun h => hi (Fin.ext h)
            omega
          have hcast :
              (((k + 1) + (i.pred hi).val : ℕ) : ℝ) =
                ((k + i.val : ℕ) : ℝ) := by exact_mod_cast hidx
          rw [hcast] at hrec
          simpa [higham9_8_complexLUFirstStepU, hi, hj] using hrec

/-- Literal reduced-history version of Theorem 9.10.  If `N` is the original
order (`k + activeOrder = N + 1`), every entry of every complex active matrix
in the trace is bounded by `N·M`. -/
theorem higham9_10_ComplexPartialPivotGEPPUTrace_activeHistoryBound :
    ∀ {n : ℕ} {A U : Fin n → Fin n → ℂ}
      (htrace : higham9_ComplexPartialPivotGEPPUTrace n A U),
      ∀ (M : ℝ) (k N : ℕ), 0 ≤ M → 0 < k → k + n ≤ N + 1 →
        higham9_10_ComplexUpperHessenberg A →
        higham9_10_ComplexHessenbergStageBound M k A →
        higham9_ComplexGEPPActiveHistoryBound ((N : ℝ) * M) htrace := by
  intro n A U htrace
  induction htrace with
  | done =>
      intro M k N hM hk hdim hH hstage
      exact higham9_ComplexGEPPActiveHistoryBound.done
  | pivot hchoice hpivot hnext ih =>
      rename_i m A r U₁
      intro M k N hM hk hdim hH hstage
      refine higham9_ComplexGEPPActiveHistoryBound.pivot
        (C := (N : ℝ) * M) (hchoice := hchoice) (hpivot := hpivot)
        (hnext := hnext) ?_ ?_
      · intro i j
        by_cases hi : i.val = 0
        · have hrow := hstage.1 i j hi
          have hkN : k ≤ N := by omega
          have hkNR : (k : ℝ) ≤ (N : ℝ) := by exact_mod_cast hkN
          exact le_trans hrow (mul_le_mul_of_nonneg_right hkNR hM)
        · have htail := hstage.2 i j (by omega)
          have hN : 1 ≤ N := by omega
          have hNR : (1 : ℝ) ≤ (N : ℝ) := by exact_mod_cast hN
          calc
            ‖A i j‖ ≤ M := htail
            _ = 1 * M := by ring
            _ ≤ (N : ℝ) * M := mul_le_mul_of_nonneg_right hNR hM
      · apply ih M (k + 1) N hM (by omega) (by omega)
        · exact higham9_10_complex_partialSchur_upperHessenberg hH hpivot
        · exact higham9_10_complex_partialSchur_stageBound
            hH hstage hchoice hpivot
  | skip hzero hnext ih =>
      rename_i m A U₁
      intro M k N hM hk hdim hH hstage
      refine higham9_ComplexGEPPActiveHistoryBound.skip
        (C := (N : ℝ) * M) (hzero := hzero) (hnext := hnext) ?_ ?_
      · intro i j
        by_cases hi : i.val = 0
        · have hrow := hstage.1 i j hi
          have hkN : k ≤ N := by omega
          have hkNR : (k : ℝ) ≤ (N : ℝ) := by exact_mod_cast hkN
          exact le_trans hrow (mul_le_mul_of_nonneg_right hkNR hM)
        · have htail := hstage.2 i j (by omega)
          have hN : 1 ≤ N := by omega
          have hNR : (1 : ℝ) ≤ (N : ℝ) := by exact_mod_cast hN
          calc
            ‖A i j‖ ≤ M := htail
            _ = 1 * M := by ring
            _ ≤ (N : ℝ) * M := mul_le_mul_of_nonneg_right hNR hM
      · apply ih M (k + 1) N hM (by omega) (by omega)
        · exact higham9_10_complex_skip_upperHessenberg hH
        · exact higham9_10_complex_skip_stageBound hM hk hstage

/-- **Theorem 9.10, literal source growth history.** -/
theorem higham9_10_complex_hessenberg_GEPP_activeHistory_le_card {n : ℕ}
    (hn : 0 < n) (A U : Fin n → Fin n → ℂ)
    (hH : higham9_10_ComplexUpperHessenberg A)
    (htrace : higham9_ComplexPartialPivotGEPPUTrace n A U) :
    higham9_ComplexGEPPActiveHistoryBound
      ((n : ℝ) * higham9_13_complexMaxEntryNorm hn A) htrace := by
  exact higham9_10_ComplexPartialPivotGEPPUTrace_activeHistoryBound htrace
    (higham9_13_complexMaxEntryNorm hn A) 1 n
    (higham9_13_complexMaxEntryNorm_nonneg hn A) (by norm_num) (by omega)
    hH (higham9_10_complex_initialStageBound hn A)

/-- **Higham Theorem 9.10, complex trace form.**  Every entry exposed by
complex GEPP on an upper-Hessenberg matrix is bounded by `n max|A|`. -/
theorem higham9_10_complex_hessenberg_GEPP_entry_norm_le_card {n : ℕ}
    (hn : 0 < n) (A U : Fin n → Fin n → ℂ)
    (hH : higham9_10_ComplexUpperHessenberg A)
    (htrace : higham9_ComplexPartialPivotGEPPUTrace n A U)
    (i j : Fin n) :
    ‖U i j‖ ≤ (n : ℝ) * higham9_13_complexMaxEntryNorm hn A := by
  have hrow :=
    higham9_10_ComplexPartialPivotGEPPUTrace_entry_norm_le_hessenberg
      htrace (higham9_13_complexMaxEntryNorm hn A) 1
      (higham9_13_complexMaxEntryNorm_nonneg hn A) (by norm_num) hH
      (higham9_10_complex_initialStageBound hn A) i j
  have hcoef : ((1 + i.val : ℕ) : ℝ) ≤ (n : ℝ) := by
    have hnat : 1 + i.val ≤ n := by omega
    exact_mod_cast hnat
  exact le_trans hrow
    (mul_le_mul_of_nonneg_right hcoef
      (higham9_13_complexMaxEntryNorm_nonneg hn A))

theorem higham9_10_complex_hessenberg_GEPP_growth_le_card {n : ℕ}
    (hn : 0 < n) (A U : Fin n → Fin n → ℂ)
    (hAmax : 0 < higham9_13_complexMaxEntryNorm hn A)
    (hH : higham9_10_ComplexUpperHessenberg A)
    (htrace : higham9_ComplexPartialPivotGEPPUTrace n A U) :
    higham9_complexGrowthFactor hn A U ≤ (n : ℝ) := by
  unfold higham9_complexGrowthFactor
  rw [div_le_iff₀ hAmax]
  apply higham9_13_complexMaxEntryNorm_le_of_entry_le_bound
  intro i j
  exact higham9_10_complex_hessenberg_GEPP_entry_norm_le_card
    hn A U hH htrace i j

/-- Source-facing existential form, valid also for singular nonzero complex
upper-Hessenberg matrices through the explicit zero-column-skip constructor. -/
theorem higham9_10_exists_complex_hessenberg_GEPP_growth_le_card {n : ℕ}
    (hn : 0 < n) (A : Fin n → Fin n → ℂ)
    (hAmax : 0 < higham9_13_complexMaxEntryNorm hn A)
    (hH : higham9_10_ComplexUpperHessenberg A) :
    ∃ U : Fin n → Fin n → ℂ,
      higham9_ComplexPartialPivotGEPPUTrace n A U ∧
        (∀ i j : Fin n, j.val < i.val → U i j = 0) ∧
        higham9_complexGrowthFactor hn A U ≤ (n : ℝ) := by
  obtain ⟨U, htrace⟩ := higham9_exists_ComplexPartialPivotGEPPUTrace A
  exact ⟨U, htrace,
    higham9_ComplexPartialPivotGEPPUTrace_upper_zero htrace,
    higham9_10_complex_hessenberg_GEPP_growth_le_card
      hn A U hAmax hH htrace⟩

/-- Source-complete existential form of Theorem 9.10.  Besides the actual
complex GEPP trace and its triangular output, it records the literal bound on
every active reduced matrix used in Higham's definition of growth. -/
theorem higham9_10_exists_complex_hessenberg_GEPP_source_growth_le_card
    {n : ℕ} (hn : 0 < n) (A : Fin n → Fin n → ℂ)
    (hAmax : 0 < higham9_13_complexMaxEntryNorm hn A)
    (hH : higham9_10_ComplexUpperHessenberg A) :
    ∃ U : Fin n → Fin n → ℂ,
      ∃ htrace : higham9_ComplexPartialPivotGEPPUTrace n A U,
        (∀ i j : Fin n, j.val < i.val → U i j = 0) ∧
        higham9_ComplexGEPPActiveHistoryBound
          ((n : ℝ) * higham9_13_complexMaxEntryNorm hn A) htrace ∧
        higham9_complexGrowthFactor hn A U ≤ (n : ℝ) := by
  obtain ⟨U, htrace⟩ := higham9_exists_ComplexPartialPivotGEPPUTrace A
  exact ⟨U, htrace,
    higham9_ComplexPartialPivotGEPPUTrace_upper_zero htrace,
    higham9_10_complex_hessenberg_GEPP_activeHistory_le_card
      hn A U hH htrace,
    higham9_10_complex_hessenberg_GEPP_growth_le_card
      hn A U hAmax hH htrace⟩

/-! ## Theorem 9.11: Bohte's sharp complex banded bound -/

/-- Equal lower and upper bandwidth `p`, over the source field `ℂ`. -/
def higham9_11_ComplexIsBanded {n : ℕ} (p : ℕ)
    (A : Fin n → Fin n → ℂ) : Prop :=
  ∀ i j : Fin n, j.val + p < i.val ∨ i.val + p < j.val → A i j = 0

/-- Complex-modulus version of Bohte's sharp active-window invariant.  The
scalar comparison function `higham9_11_bohteBaux` is the already-verified
closed recurrence from Bohte's proof. -/
def higham9_11_ComplexBandActiveBoundSharp (n p : ℕ) (M : ℝ)
    (S : Fin n → Fin n → ℂ) : Prop :=
  (∀ i j : Fin n, j.val + p < i.val → S i j = 0) ∧
  (∀ i j : Fin n, i.val ≤ p → 2 * p < j.val → S i j = 0) ∧
  (∀ i j : Fin n, i.val ≤ p →
    ‖S i j‖ ≤ M * higham9_11_bohteBaux p (2 * p - 1 - j.val) (i.val + 1)) ∧
  (∀ i i' j : Fin n, i.val ≤ p → i'.val ≤ p → j.val = 2 * p →
    S i j ≠ 0 → S i' j ≠ 0 → i = i') ∧
  (∀ i j : Fin n, p < i.val →
    ‖S i j‖ ≤ M ∧ (i.val + p < j.val → S i j = 0))

theorem higham9_11_complexBandActiveBoundSharp_of_isBanded {n p : ℕ}
    {M : ℝ} {A : Fin n → Fin n → ℂ} (hM : 0 ≤ M)
    (hband : higham9_11_ComplexIsBanded p A)
    (hbound : ∀ i j : Fin n, ‖A i j‖ ≤ M) :
    higham9_11_ComplexBandActiveBoundSharp n p M A := by
  have hMb : ∀ d i : ℕ, M ≤ M * higham9_11_bohteBaux p d i := fun d i =>
    le_mul_of_one_le_right hM (higham9_11_bohteBaux_one_le p d i)
  refine ⟨?_, ?_, ?_, ?_, ?_⟩
  · intro i j hij
    exact hband i j (Or.inl hij)
  · intro i j hi hj
    exact hband i j (Or.inr (by omega))
  · intro i j _hi
    exact le_trans (hbound i j) (hMb _ _)
  · intro i i' j hi hi' hj hne hne'
    have hiv : i.val = p := by
      by_contra h
      exact hne (hband i j (Or.inr (by omega)))
    have hiv' : i'.val = p := by
      by_contra h
      exact hne' (hband i' j (Or.inr (by omega)))
    exact Fin.ext (by omega)
  · intro i j hi
    exact ⟨hbound i j, fun hj => hband i j (Or.inr (by omega))⟩

theorem higham9_11_complexBandActiveSharp_entry_norm_le {n p : ℕ}
    {M : ℝ} {S : Fin n → Fin n → ℂ}
    (hM : 0 ≤ M)
    (hS : higham9_11_ComplexBandActiveBoundSharp n p M S)
    (i j : Fin n) :
    ‖S i j‖ ≤ higham9_11_bohteBaux p (2 * p - 1) 1 * M := by
  by_cases hi : i.val ≤ p
  · have h := hS.2.2.1 i j hi
    have htop := higham9_11_bohteBaux_le_top p (2 * p - 1)
      (2 * p - 1 - j.val) (i.val + 1) (by omega) (by omega)
    calc
      ‖S i j‖ ≤ M * higham9_11_bohteBaux p (2 * p - 1 - j.val)
          (i.val + 1) := h
      _ ≤ M * higham9_11_bohteBaux p (2 * p - 1) 1 :=
        mul_le_mul_of_nonneg_left htop hM
      _ = higham9_11_bohteBaux p (2 * p - 1) 1 * M := by ring
  · have h := (hS.2.2.2.2 i j (by omega)).1
    exact le_trans h
      (le_mul_of_one_le_left hM (higham9_11_bohteBaux_one_le p _ _))

/-- Signed real modulus envelope for one actual complex pivot.  The selected
pivot row is negated away from column zero.  Consequently its real Schur
update is the *sum* of the two modulus terms that bounds the complex Schur
update by the triangle inequality. -/
noncomputable def higham9_11_complexPivotEnvelope {m : ℕ}
    (S : Fin (m + 1) → Fin (m + 1) → ℂ) (r : Fin (m + 1)) :
    Fin (m + 1) → Fin (m + 1) → ℝ := fun i j =>
  if i = r ∧ j ≠ 0 then -‖S i j‖ else ‖S i j‖

lemma higham9_11_complexPivotEnvelope_abs {m : ℕ}
    (S : Fin (m + 1) → Fin (m + 1) → ℂ) (r i j : Fin (m + 1)) :
    |higham9_11_complexPivotEnvelope S r i j| = ‖S i j‖ := by
  by_cases h : i = r ∧ j ≠ 0 <;>
    simp [higham9_11_complexPivotEnvelope, h]

lemma higham9_11_complexPivotEnvelope_col_zero {m : ℕ}
    (S : Fin (m + 1) → Fin (m + 1) → ℂ) (r i : Fin (m + 1)) :
    higham9_11_complexPivotEnvelope S r i 0 = ‖S i 0‖ := by
  simp [higham9_11_complexPivotEnvelope]

lemma higham9_11_complexPivotEnvelope_nonzero_iff {m : ℕ}
    (S : Fin (m + 1) → Fin (m + 1) → ℂ) (r i j : Fin (m + 1)) :
    higham9_11_complexPivotEnvelope S r i j ≠ 0 ↔ S i j ≠ 0 := by
  rw [← abs_pos, higham9_11_complexPivotEnvelope_abs, norm_pos_iff]

lemma higham9_11_complexPivotEnvelope_partialPivotChoice {m : ℕ}
    (S : Fin (m + 1) → Fin (m + 1) → ℂ) (r : Fin (m + 1))
    (hchoice : higham9_complexPartialPivotChoice S r) :
    higham9_1_partialPivotChoice
      (higham9_11_complexPivotEnvelope S r) 0 r := by
  refine ⟨Nat.zero_le _, ?_⟩
  intro i _hi
  simp only [higham9_11_complexPivotEnvelope_abs]
  exact hchoice i

lemma higham9_11_complexBandActive_to_realEnvelope {p m : ℕ} {M : ℝ}
    {S : Fin (m + 1) → Fin (m + 1) → ℂ} {r : Fin (m + 1)}
    (hS : higham9_11_ComplexBandActiveBoundSharp (m + 1) p M S) :
    higham9_11_BandActiveBoundSharp (m + 1) p M
      (higham9_11_complexPivotEnvelope S r) := by
  obtain ⟨h1, h2, h3, h4, h5⟩ := hS
  refine ⟨?_, ?_, ?_, ?_, ?_⟩
  · intro i j hij
    simp [higham9_11_complexPivotEnvelope, h1 i j hij]
  · intro i j hi hj
    simp [higham9_11_complexPivotEnvelope, h2 i j hi hj]
  · intro i j hi
    simpa [higham9_11_complexPivotEnvelope_abs] using h3 i j hi
  · intro i i' j hi hi' hj hne hne'
    apply h4 i i' j hi hi' hj
    · exact (higham9_11_complexPivotEnvelope_nonzero_iff S r i j).mp hne
    · exact (higham9_11_complexPivotEnvelope_nonzero_iff S r i' j).mp hne'
  · intro i j hi
    exact ⟨by simpa [higham9_11_complexPivotEnvelope_abs] using (h5 i j hi).1,
      fun hj => by simp [higham9_11_complexPivotEnvelope, (h5 i j hi).2 hj]⟩

/-- The signed-envelope Schur update pointwise majorizes the modulus of the
actual complex Schur update. -/
lemma higham9_11_complexPartialSchur_norm_le_realEnvelopeSchur {m : ℕ}
    (S : Fin (m + 1) → Fin (m + 1) → ℂ) (r : Fin (m + 1))
    (i j : Fin m) :
    ‖higham9_complexPartialSchur S r i j‖ ≤
      luFirstSchurComplement
        (higham9_2_rowPermutedMatrix
          (higham9_11_complexPivotEnvelope S r)
          (higham9_7_firstPivotRowSwap r)) i j := by
  let σ := higham9_7_firstPivotRowSwap r
  let x : ℂ := S (σ i.succ) j.succ
  let a : ℂ := S (σ i.succ) 0
  let b : ℂ := S r j.succ
  let p : ℂ := S r 0
  have hσ0 : σ (0 : Fin (m + 1)) = r := by
    simp [σ, higham9_7_firstPivotRowSwap]
  have hσr : σ r = 0 := by
    by_cases hr0 : r = 0
    · simp [σ, higham9_7_firstPivotRowSwap, hr0]
    · simp [σ, higham9_7_firstPivotRowSwap, hr0]
  have hσne : σ i.succ ≠ r := by
    intro h
    have hc := congrArg σ h
    rw [hσr] at hc
    have hinv := higham9_7_firstPivotRowSwap_involutive r i.succ
    change σ (σ i.succ) = i.succ at hinv
    rw [hinv] at hc
    exact Fin.succ_ne_zero i hc
  have hjs : j.succ ≠ (0 : Fin (m + 1)) := Fin.succ_ne_zero j
  have hnormterm : ‖a * b / p‖ = ‖a‖ * ‖b‖ / ‖p‖ := by
    rw [norm_div, norm_mul]
  have htri : ‖x - a * b / p‖ ≤ ‖x‖ + ‖a‖ * ‖b‖ / ‖p‖ := by
    calc
      ‖x - a * b / p‖ ≤ ‖x‖ + ‖a * b / p‖ := norm_sub_le _ _
      _ = ‖x‖ + ‖a‖ * ‖b‖ / ‖p‖ := by rw [hnormterm]
  have hreal :
      luFirstSchurComplement
          (higham9_2_rowPermutedMatrix
            (higham9_11_complexPivotEnvelope S r) σ) i j =
        ‖x‖ + ‖a‖ * ‖b‖ / ‖p‖ := by
    simp [luFirstSchurComplement, higham9_2_rowPermutedMatrix,
      higham9_11_complexPivotEnvelope, σ, hσ0, hσne, hjs,
      x, a, b, p]
    ring
  change ‖x - a * b / p‖ ≤ _
  rw [hreal]
  exact htri

lemma higham9_11_realEnvelopeSchur_nonneg {m : ℕ}
    (S : Fin (m + 1) → Fin (m + 1) → ℂ) (r : Fin (m + 1))
    (i j : Fin m) :
    0 ≤ luFirstSchurComplement
      (higham9_2_rowPermutedMatrix
        (higham9_11_complexPivotEnvelope S r)
        (higham9_7_firstPivotRowSwap r)) i j := by
  exact le_trans (norm_nonneg _)
    (higham9_11_complexPartialSchur_norm_le_realEnvelopeSchur
      S r i j)

/-- One actual complex partial-pivoting Schur step preserves Bohte's sharp
invariant.  The proof is a certified modulus-envelope bridge to the already
proved nonnegative scalar recurrence, not a real specialization of the input. -/
theorem higham9_11_complexBandActiveSharp_pivot_preserved {p m : ℕ}
    {S : Fin (m + 1) → Fin (m + 1) → ℂ} {M : ℝ}
    {r : Fin (m + 1)} (hM : 0 ≤ M)
    (hS : higham9_11_ComplexBandActiveBoundSharp (m + 1) p M S)
    (hchoice : higham9_complexPartialPivotChoice S r)
    (hpivot : S r 0 ≠ 0) :
    higham9_11_ComplexBandActiveBoundSharp m p M
      (higham9_complexPartialSchur S r) := by
  let R : Fin (m + 1) → Fin (m + 1) → ℝ :=
    higham9_11_complexPivotEnvelope S r
  let σ := higham9_7_firstPivotRowSwap r
  let Rnext : Fin m → Fin m → ℝ :=
    luFirstSchurComplement (higham9_2_rowPermutedMatrix R σ)
  have hR : higham9_11_BandActiveBoundSharp (m + 1) p M R := by
    simpa [R] using
      (higham9_11_complexBandActive_to_realEnvelope (r := r) hS)
  have hchoiceR : higham9_1_partialPivotChoice R 0 r := by
    simpa [R] using
      higham9_11_complexPivotEnvelope_partialPivotChoice S r hchoice
  have hpivotR : R r 0 ≠ 0 := by
    simp [R, higham9_11_complexPivotEnvelope_col_zero, hpivot]
  have hRnext : higham9_11_BandActiveBoundSharp m p M Rnext := by
    simpa [Rnext, R, σ] using
      higham9_11_bandActiveSharp_schur_preserved hM hR hchoiceR hpivotR
  have hdom : ∀ i j : Fin m, ‖higham9_complexPartialSchur S r i j‖ ≤ Rnext i j := by
    intro i j
    simpa [Rnext, R, σ] using
      higham9_11_complexPartialSchur_norm_le_realEnvelopeSchur
        S r i j
  refine ⟨?_, ?_, ?_, ?_, ?_⟩
  · intro i j hij
    have hz := hRnext.1 i j hij
    apply norm_eq_zero.mp
    apply le_antisymm
    · exact le_trans (hdom i j) (le_of_eq hz)
    · exact norm_nonneg _
  · intro i j hi hj
    have hz := hRnext.2.1 i j hi hj
    apply norm_eq_zero.mp
    apply le_antisymm
    · exact le_trans (hdom i j) (le_of_eq hz)
    · exact norm_nonneg _
  · intro i j hi
    exact le_trans (hdom i j) <| le_trans (le_abs_self (Rnext i j))
      (hRnext.2.2.1 i j hi)
  · intro i i' j hi hi' hj hne hne'
    apply hRnext.2.2.2.1 i i' j hi hi' hj
    · intro hz
      apply hne
      apply norm_eq_zero.mp
      apply le_antisymm
      · exact le_trans (hdom i j) (le_of_eq hz)
      · exact norm_nonneg _
    · intro hz
      apply hne'
      apply norm_eq_zero.mp
      apply le_antisymm
      · exact le_trans (hdom i' j) (le_of_eq hz)
      · exact norm_nonneg _
  · intro i j hi
    refine ⟨?_, ?_⟩
    · exact le_trans (hdom i j) <| le_trans (le_abs_self (Rnext i j))
        (hRnext.2.2.2.2 i j hi).1
    · intro hij
      have hz := (hRnext.2.2.2.2 i j hi).2 hij
      apply norm_eq_zero.mp
      apply le_antisymm
      · exact le_trans (hdom i j) (le_of_eq hz)
      · exact norm_nonneg _

/-- A singular zero-pivot-column skip also preserves Bohte's invariant.  The
active indices shift by one; inside the fill window the required comparison
is exactly one unfolding of Bohte's recurrence, while the entrant row uses the
unchanged source-band bound `M`. -/
theorem higham9_11_complexBandActiveSharp_skip_preserved {p m : ℕ}
    {S : Fin (m + 1) → Fin (m + 1) → ℂ} {M : ℝ}
    (hM : 0 ≤ M)
    (hS : higham9_11_ComplexBandActiveBoundSharp (m + 1) p M S) :
    higham9_11_ComplexBandActiveBoundSharp m p M
      (fun i j => S i.succ j.succ) := by
  obtain ⟨h1, h2, h3, h4, h5⟩ := hS
  have hMb : ∀ d i : ℕ, M ≤ M * higham9_11_bohteBaux p d i := fun d i =>
    le_mul_of_one_le_right hM (higham9_11_bohteBaux_one_le p d i)
  refine ⟨?_, ?_, ?_, ?_, ?_⟩
  · intro i j hij
    apply h1 i.succ j.succ
    simp only [Fin.val_succ]
    omega
  · intro i j hi hj
    by_cases hwin : i.succ.val ≤ p
    · exact h2 i.succ j.succ hwin (by simp only [Fin.val_succ]; omega)
    · have hbelow : p < i.succ.val := Nat.lt_of_not_ge hwin
      exact (h5 i.succ j.succ hbelow).2 (by simp only [Fin.val_succ]; omega)
  · intro i j hi
    by_cases hwin : i.succ.val ≤ p
    · have hsrc := h3 i.succ j.succ hwin
      by_cases hj : j.val < 2 * p - 1
      · let d := 2 * p - 2 - j.val
        have hdsrc : 2 * p - 1 - j.succ.val = d := by
          simp only [Fin.val_succ]
          dsimp [d]
          omega
        have hdtgt : 2 * p - 1 - j.val = d + 1 := by
          dsimp [d]
          omega
        have hrow : i.succ.val + 1 = i.val + 2 := by simp
        rw [hdsrc, hrow] at hsrc
        rw [hdtgt, higham9_11_bohteBaux_succ (by simpa using hwin)]
        calc
          ‖S i.succ j.succ‖
              ≤ M * higham9_11_bohteBaux p d (i.val + 2) := hsrc
          _ ≤ M * (higham9_11_bohteBaux p d (i.val + 2) +
                higham9_11_bohteBaux p d 1) := by
              apply mul_le_mul_of_nonneg_left _ hM
              exact le_add_of_nonneg_right (higham9_11_bohteBaux_nonneg p d 1)
      · have hdsrc : 2 * p - 1 - j.succ.val = 0 := by
          simp only [Fin.val_succ]
          omega
        have hdtgt : 2 * p - 1 - j.val = 0 := by omega
        rw [hdsrc] at hsrc
        rw [hdtgt]
        simpa [higham9_11_bohteBaux] using hsrc
    · have hbelow : p < i.succ.val := Nat.lt_of_not_ge hwin
      exact le_trans (h5 i.succ j.succ hbelow).1 (hMb _ _)
  · intro i i' j hi hi' hj hne hne'
    have hiv : i.val = p := by
      by_contra h
      have hwin : i.succ.val ≤ p := by
        simp only [Fin.val_succ]
        omega
      apply hne
      apply h2 i.succ j.succ hwin
      simp only [Fin.val_succ]
      omega
    have hiv' : i'.val = p := by
      by_contra h
      have hwin : i'.succ.val ≤ p := by
        simp only [Fin.val_succ]
        omega
      apply hne'
      apply h2 i'.succ j.succ hwin
      simp only [Fin.val_succ]
      omega
    exact Fin.ext (by omega)
  · intro i j hi
    have hbelow : p < i.succ.val := by simp only [Fin.val_succ]; omega
    refine ⟨(h5 i.succ j.succ hbelow).1, ?_⟩
    intro hij
    apply (h5 i.succ j.succ hbelow).2
    simp only [Fin.val_succ]
    omega

/-- Trace-level Bohte envelope for the actual complex executor, including
zero-column skips. -/
theorem higham9_11_ComplexPartialPivotGEPPUTrace_entry_norm_le_bohteAux :
    ∀ {n : ℕ} {A U : Fin n → Fin n → ℂ},
      higham9_ComplexPartialPivotGEPPUTrace n A U →
      ∀ (p : ℕ) (M : ℝ), 0 ≤ M →
        higham9_11_ComplexBandActiveBoundSharp n p M A →
        ∀ i j : Fin n,
          ‖U i j‖ ≤ higham9_11_bohteBaux p (2 * p - 1) 1 * M := by
  intro n A U htrace
  induction htrace with
  | done =>
      intro p M hM hA i
      exact Fin.elim0 i
  | pivot hchoice hpivot hnext ih =>
      rename_i m A r U₁
      intro p M hM hA i j
      by_cases hi : i = 0
      · subst i
        have hrow := higham9_11_complexBandActiveSharp_entry_norm_le
          hM hA r j
        simpa [higham9_8_complexLUFirstStepU, higham9_complexRowPermuted,
          higham9_7_firstPivotRowSwap] using hrow
      · by_cases hj : j = 0
        · subst j
          have hnonneg :
              0 ≤ higham9_11_bohteBaux p (2 * p - 1) 1 * M :=
            mul_nonneg (higham9_11_bohteBaux_nonneg p _ _) hM
          simpa [higham9_8_complexLUFirstStepU, hi] using hnonneg
        · have hnextInv := higham9_11_complexBandActiveSharp_pivot_preserved
            hM hA hchoice hpivot
          have hrec := ih p M hM hnextInv (i.pred hi) (j.pred hj)
          simpa [higham9_8_complexLUFirstStepU, hi, hj] using hrec
  | skip hzero hnext ih =>
      rename_i m A U₁
      intro p M hM hA i j
      by_cases hi : i = 0
      · subst i
        have hrow := higham9_11_complexBandActiveSharp_entry_norm_le
          hM hA 0 j
        simpa [higham9_8_complexLUFirstStepU] using hrow
      · by_cases hj : j = 0
        · subst j
          have hnonneg :
              0 ≤ higham9_11_bohteBaux p (2 * p - 1) 1 * M :=
            mul_nonneg (higham9_11_bohteBaux_nonneg p _ _) hM
          simpa [higham9_8_complexLUFirstStepU, hi] using hnonneg
        · have hnextInv :=
            higham9_11_complexBandActiveSharp_skip_preserved hM hA
          have hrec := ih p M hM hnextInv (i.pred hi) (j.pred hj)
          simpa [higham9_8_complexLUFirstStepU, hi, hj] using hrec

/-- Literal source-growth version of Bohte's recurrence: the same sharp
modulus envelope bounds every active reduced matrix in the complex GEPP
history, including histories containing singular zero-column skips. -/
theorem higham9_11_ComplexPartialPivotGEPPUTrace_activeHistoryBound_bohteAux :
    ∀ {n : ℕ} {A U : Fin n → Fin n → ℂ}
      (htrace : higham9_ComplexPartialPivotGEPPUTrace n A U),
      ∀ (p : ℕ) (M : ℝ), 0 ≤ M →
        higham9_11_ComplexBandActiveBoundSharp n p M A →
        higham9_ComplexGEPPActiveHistoryBound
          (higham9_11_bohteBaux p (2 * p - 1) 1 * M) htrace := by
  intro n A U htrace
  induction htrace with
  | done =>
      intro p M hM hA
      exact higham9_ComplexGEPPActiveHistoryBound.done
  | pivot hchoice hpivot hnext ih =>
      rename_i m A r U₁
      intro p M hM hA
      refine higham9_ComplexGEPPActiveHistoryBound.pivot
        (C := higham9_11_bohteBaux p (2 * p - 1) 1 * M)
        (hchoice := hchoice) (hpivot := hpivot) (hnext := hnext) ?_ ?_
      · intro i j
        exact higham9_11_complexBandActiveSharp_entry_norm_le hM hA i j
      · apply ih p M hM
        exact higham9_11_complexBandActiveSharp_pivot_preserved
          hM hA hchoice hpivot
  | skip hzero hnext ih =>
      rename_i m A U₁
      intro p M hM hA
      refine higham9_ComplexGEPPActiveHistoryBound.skip
        (C := higham9_11_bohteBaux p (2 * p - 1) 1 * M)
        (hzero := hzero) (hnext := hnext) ?_ ?_
      · intro i j
        exact higham9_11_complexBandActiveSharp_entry_norm_le hM hA i j
      · apply ih p M hM
        exact higham9_11_complexBandActiveSharp_skip_preserved hM hA

/-- **Higham Theorem 9.11, literal complex source-growth history.**  Every
active reduced matrix is bounded by the printed Bohte coefficient times the
largest entry of the input. -/
theorem higham9_11_complex_banded_GEPP_activeHistory_le_bohteBound {n : ℕ}
    (hn : 0 < n) (A U : Fin n → Fin n → ℂ) (p : ℕ) (hp : 1 ≤ p)
    (hband : higham9_11_ComplexIsBanded p A)
    (htrace : higham9_ComplexPartialPivotGEPPUTrace n A U) :
    higham9_ComplexGEPPActiveHistoryBound
      (higham9_11_bohteBound p * higham9_13_complexMaxEntryNorm hn A)
      htrace := by
  rw [← higham9_11_bohteBaux_top_eq_bohteBound hp]
  apply higham9_11_ComplexPartialPivotGEPPUTrace_activeHistoryBound_bohteAux
    htrace p (higham9_13_complexMaxEntryNorm hn A)
      (higham9_13_complexMaxEntryNorm_nonneg hn A)
  exact higham9_11_complexBandActiveBoundSharp_of_isBanded
    (higham9_13_complexMaxEntryNorm_nonneg hn A) hband
    (fun i j => higham9_13_entry_norm_le_complexMaxEntryNorm hn A i j)

/-- **Higham Theorem 9.11 (Bohte), complex entry form.** -/
theorem higham9_11_complex_banded_GEPP_entry_norm_le_bohteBound {n : ℕ}
    (hn : 0 < n) (A U : Fin n → Fin n → ℂ) (p : ℕ) (hp : 1 ≤ p)
    (hband : higham9_11_ComplexIsBanded p A)
    (htrace : higham9_ComplexPartialPivotGEPPUTrace n A U)
    (i j : Fin n) :
    ‖U i j‖ ≤ higham9_11_bohteBound p *
      higham9_13_complexMaxEntryNorm hn A := by
  rw [← higham9_11_bohteBaux_top_eq_bohteBound hp]
  apply higham9_11_ComplexPartialPivotGEPPUTrace_entry_norm_le_bohteAux
    htrace p (higham9_13_complexMaxEntryNorm hn A)
      (higham9_13_complexMaxEntryNorm_nonneg hn A)
  exact higham9_11_complexBandActiveBoundSharp_of_isBanded
    (higham9_13_complexMaxEntryNorm_nonneg hn A) hband
    (fun i j => higham9_13_entry_norm_le_complexMaxEntryNorm hn A i j)

/-- **Higham Theorem 9.11 (Bohte), complex growth-factor form.**  This is
the printed `2^(2p-1) - (p-1)2^(p-2)` bound through the exact scalar
definition `higham9_11_bohteBound`. -/
theorem higham9_11_complex_banded_GEPP_growth_le_bohteBound {n : ℕ}
    (hn : 0 < n) (A U : Fin n → Fin n → ℂ) (p : ℕ) (hp : 1 ≤ p)
    (hAmax : 0 < higham9_13_complexMaxEntryNorm hn A)
    (hband : higham9_11_ComplexIsBanded p A)
    (htrace : higham9_ComplexPartialPivotGEPPUTrace n A U) :
    higham9_complexGrowthFactor hn A U ≤ higham9_11_bohteBound p := by
  unfold higham9_complexGrowthFactor
  rw [div_le_iff₀ hAmax]
  apply higham9_13_complexMaxEntryNorm_le_of_entry_le_bound
  intro i j
  exact higham9_11_complex_banded_GEPP_entry_norm_le_bohteBound
    hn A U p hp hband htrace i j

/-- Source-facing existential complex executor for Bohte's theorem. -/
theorem higham9_11_exists_complex_banded_GEPP_growth_le_bohteBound {n : ℕ}
    (hn : 0 < n) (A : Fin n → Fin n → ℂ) (p : ℕ) (hp : 1 ≤ p)
    (hAmax : 0 < higham9_13_complexMaxEntryNorm hn A)
    (hband : higham9_11_ComplexIsBanded p A) :
    ∃ U : Fin n → Fin n → ℂ,
      higham9_ComplexPartialPivotGEPPUTrace n A U ∧
        (∀ i j : Fin n, j.val < i.val → U i j = 0) ∧
        higham9_complexGrowthFactor hn A U ≤ higham9_11_bohteBound p := by
  obtain ⟨U, htrace⟩ := higham9_exists_ComplexPartialPivotGEPPUTrace A
  exact ⟨U, htrace,
    higham9_ComplexPartialPivotGEPPUTrace_upper_zero htrace,
    higham9_11_complex_banded_GEPP_growth_le_bohteBound
      hn A U p hp hAmax hband htrace⟩

/-- Source-complete existential form of Theorem 9.11: actual complex GEPP,
triangular output, the printed Bohte bound over the full reduced history, and
the corresponding final-output growth quotient. -/
theorem higham9_11_exists_complex_banded_GEPP_source_growth_le_bohteBound
    {n : ℕ} (hn : 0 < n) (A : Fin n → Fin n → ℂ)
    (p : ℕ) (hp : 1 ≤ p)
    (hAmax : 0 < higham9_13_complexMaxEntryNorm hn A)
    (hband : higham9_11_ComplexIsBanded p A) :
    ∃ U : Fin n → Fin n → ℂ,
      ∃ htrace : higham9_ComplexPartialPivotGEPPUTrace n A U,
        (∀ i j : Fin n, j.val < i.val → U i j = 0) ∧
        higham9_ComplexGEPPActiveHistoryBound
          (higham9_11_bohteBound p * higham9_13_complexMaxEntryNorm hn A)
          htrace ∧
        higham9_complexGrowthFactor hn A U ≤ higham9_11_bohteBound p := by
  obtain ⟨U, htrace⟩ := higham9_exists_ComplexPartialPivotGEPPUTrace A
  exact ⟨U, htrace,
    higham9_ComplexPartialPivotGEPPUTrace_upper_zero htrace,
    higham9_11_complex_banded_GEPP_activeHistory_le_bohteBound
      hn A U p hp hband htrace,
    higham9_11_complex_banded_GEPP_growth_le_bohteBound
      hn A U p hp hAmax hband htrace⟩

/-- The printed tridiagonal consequence over `ℂ`: common bandwidth one gives
complex GEPP growth at most two. -/
theorem higham9_11_complex_tridiagonal_GEPP_growth_le_two {n : ℕ}
    (hn : 0 < n) (A U : Fin n → Fin n → ℂ)
    (hAmax : 0 < higham9_13_complexMaxEntryNorm hn A)
    (htri : higham9_11_ComplexIsBanded 1 A)
    (htrace : higham9_ComplexPartialPivotGEPPUTrace n A U) :
    higham9_complexGrowthFactor hn A U ≤ 2 := by
  have h := higham9_11_complex_banded_GEPP_growth_le_bohteBound
    hn A U 1 (by norm_num) hAmax htri htrace
  rwa [higham9_11_bohteBound_tridiagonal] at h

/-- Literal source-history form of the printed tridiagonal consequence. -/
theorem higham9_11_complex_tridiagonal_GEPP_activeHistory_le_two {n : ℕ}
    (hn : 0 < n) (A U : Fin n → Fin n → ℂ)
    (htri : higham9_11_ComplexIsBanded 1 A)
    (htrace : higham9_ComplexPartialPivotGEPPUTrace n A U) :
    higham9_ComplexGEPPActiveHistoryBound
      (2 * higham9_13_complexMaxEntryNorm hn A) htrace := by
  have h := higham9_11_complex_banded_GEPP_activeHistory_le_bohteBound
    hn A U 1 (by norm_num) htri htrace
  rwa [higham9_11_bohteBound_tridiagonal] at h

/-! ### Complex embedding of Higham's displayed `n=9=2p+1` witness -/

noncomputable def higham9_realMatrixToComplex {n : ℕ}
    (A : Fin n → Fin n → ℝ) : Fin n → Fin n → ℂ :=
  fun i j => (A i j : ℂ)

lemma higham9_realMatrixToComplex_norm {n : ℕ}
    (A : Fin n → Fin n → ℝ) (i j : Fin n) :
    ‖higham9_realMatrixToComplex A i j‖ = |A i j| := by
  simp [higham9_realMatrixToComplex]

lemma higham9_realMatrixToComplex_maxEntryNorm {n : ℕ} (hn : 0 < n)
    (A : Fin n → Fin n → ℝ) :
    higham9_13_complexMaxEntryNorm hn (higham9_realMatrixToComplex A) =
      maxEntryNorm hn A := by
  unfold higham9_13_complexMaxEntryNorm maxEntryNorm
  congr 1
  funext i
  congr 1
  funext j
  exact higham9_realMatrixToComplex_norm A i j

lemma higham9_realMatrixToComplex_partialChoice {m : ℕ}
    (A : Fin (m + 1) → Fin (m + 1) → ℝ) (r : Fin (m + 1))
    (hchoice : higham9_1_partialPivotChoice A 0 r) :
    higham9_complexPartialPivotChoice (higham9_realMatrixToComplex A) r := by
  intro i
  simpa [higham9_realMatrixToComplex_norm] using hchoice.2 i (Nat.zero_le _)

lemma higham9_realMatrixToComplex_partialSchur {m : ℕ}
    (A : Fin (m + 1) → Fin (m + 1) → ℝ) (r : Fin (m + 1)) :
    higham9_complexPartialSchur (higham9_realMatrixToComplex A) r =
      higham9_realMatrixToComplex
        (luFirstSchurComplement
          (higham9_2_rowPermutedMatrix A (higham9_7_firstPivotRowSwap r))) := by
  funext i j
  simp [higham9_complexPartialSchur, higham9_8_complexFirstSchurComplement,
    higham9_complexRowPermuted, higham9_realMatrixToComplex,
    luFirstSchurComplement, higham9_2_rowPermutedMatrix]

lemma higham9_realMatrixToComplex_rowPermuted {n : ℕ}
    (A : Fin n → Fin n → ℝ) (σ : Fin n → Fin n) :
    higham9_complexRowPermuted (higham9_realMatrixToComplex A) σ =
      higham9_realMatrixToComplex (higham9_2_rowPermutedMatrix A σ) := by
  rfl

lemma higham9_realMatrixToComplex_luFirstStepU {m : ℕ}
    (A : Fin (m + 1) → Fin (m + 1) → ℝ)
    (U₁ : Fin m → Fin m → ℝ) :
    higham9_8_complexLUFirstStepU (higham9_realMatrixToComplex A)
        (higham9_realMatrixToComplex U₁) =
      higham9_realMatrixToComplex (luFirstStepU A U₁) := by
  funext i j
  by_cases hi : i = 0 <;> by_cases hj : j = 0 <;>
    simp [higham9_8_complexLUFirstStepU, luFirstStepU,
      higham9_realMatrixToComplex, hi, hj]

/-- A real exact GEPP trace embeds as an exact complex GEPP trace, with all
pivot choices and Schur updates preserved. -/
theorem higham9_real_PartialPivotGEPPUTrace_to_complex :
    ∀ {n : ℕ} {A U : Fin n → Fin n → ℝ},
      higham9_7_PartialPivotGEPPUTrace n A U →
      higham9_ComplexPartialPivotGEPPUTrace n
        (higham9_realMatrixToComplex A) (higham9_realMatrixToComplex U) := by
  intro n A U htrace
  induction htrace with
  | done => exact higham9_ComplexPartialPivotGEPPUTrace.done
  | step hchoice hpivot hnext ih =>
      rename_i m A r U₁
      have hchoiceC := higham9_realMatrixToComplex_partialChoice A r hchoice
      have hpivotC : higham9_realMatrixToComplex A r 0 ≠ 0 := by
        simpa [higham9_realMatrixToComplex] using hpivot
      have hnextC :
          higham9_ComplexPartialPivotGEPPUTrace m
            (higham9_complexPartialSchur (higham9_realMatrixToComplex A) r)
            (higham9_realMatrixToComplex U₁) := by
        rw [higham9_realMatrixToComplex_partialSchur]
        exact ih
      have hstep := higham9_ComplexPartialPivotGEPPUTrace.pivot
        hchoiceC hpivotC hnextC
      rw [higham9_realMatrixToComplex_rowPermuted] at hstep
      rw [higham9_realMatrixToComplex_luFirstStepU] at hstep
      exact hstep

noncomputable def higham9_11_complexBohteExample : Fin 9 → Fin 9 → ℂ :=
  higham9_realMatrixToComplex higham9_11_bohteExample

noncomputable def higham9_11_complexBohteExampleU : Fin 9 → Fin 9 → ℂ :=
  higham9_realMatrixToComplex higham9_11_bohteExampleU

theorem higham9_11_complexBohteExample_trace :
    higham9_ComplexPartialPivotGEPPUTrace 9
      higham9_11_complexBohteExample higham9_11_complexBohteExampleU := by
  exact higham9_real_PartialPivotGEPPUTrace_to_complex
    higham9_11_bohteExample_trace_explicit

theorem higham9_11_complexBohteExample_isBanded :
    higham9_11_ComplexIsBanded 4 higham9_11_complexBohteExample := by
  intro i j hij
  fin_cases i <;> fin_cases j
  all_goals
    simp_all [higham9_11_complexBohteExample, higham9_realMatrixToComplex,
      higham9_11_bohteExample]

lemma higham9_11_complexBohteExample_maxEntryNorm_pos :
    0 < higham9_13_complexMaxEntryNorm (by norm_num : 0 < 9)
      higham9_11_complexBohteExample := by
  have hentry := higham9_13_entry_norm_le_complexMaxEntryNorm
    (by norm_num : 0 < 9) higham9_11_complexBohteExample
      (0 : Fin 9) (0 : Fin 9)
  have hone : ‖higham9_11_complexBohteExample (0 : Fin 9) (0 : Fin 9)‖ = 1 := by
    norm_num [higham9_11_complexBohteExample, higham9_realMatrixToComplex,
      higham9_11_bohteExample]
  rw [hone] at hentry
  linarith

lemma higham9_realMatrixToComplex_growth_eq {n : ℕ} (hn : 0 < n)
    (A U : Fin n → Fin n → ℝ)
    (hA : 0 < maxEntryNorm hn A) :
    higham9_complexGrowthFactor hn (higham9_realMatrixToComplex A)
        (higham9_realMatrixToComplex U) =
      growthFactorEntry hn A U hA := by
  unfold higham9_complexGrowthFactor growthFactorEntry
  rw [higham9_realMatrixToComplex_maxEntryNorm,
    higham9_realMatrixToComplex_maxEntryNorm]

/-- **Theorem 9.11, complex near-attainability.**  Higham's displayed
`n = 9 = 2·4+1` matrix is a genuine complex bandwidth-four input whose exact
complex GEPP trace has growth at least `bohteBound 4 - 1`. -/
theorem higham9_11_complex_bohte_near_attainability :
    (9 : ℕ) = 2 * 4 + 1 ∧
    higham9_11_ComplexIsBanded 4 higham9_11_complexBohteExample ∧
    higham9_ComplexPartialPivotGEPPUTrace 9
      higham9_11_complexBohteExample higham9_11_complexBohteExampleU ∧
    higham9_11_bohteBound 4 - 1 ≤
      higham9_complexGrowthFactor (by norm_num : 0 < 9)
        higham9_11_complexBohteExample higham9_11_complexBohteExampleU := by
  have hrealPos :
      0 < maxEntryNorm (by norm_num : 0 < 9) higham9_11_bohteExample := by
    simpa [higham9_11_complexBohteExample,
      higham9_realMatrixToComplex_maxEntryNorm] using
        higham9_11_complexBohteExample_maxEntryNorm_pos
  have hnear := higham9_11_bohte_example_growth_ge_bohteBound_sub_one
    (by norm_num : 0 < 9) hrealPos
  have hgrowth := higham9_realMatrixToComplex_growth_eq
    (by norm_num : 0 < 9) higham9_11_bohteExample
      higham9_11_bohteExampleU hrealPos
  refine ⟨by norm_num, higham9_11_complexBohteExample_isBanded,
    higham9_11_complexBohteExample_trace, ?_⟩
  simpa [higham9_11_complexBohteExample,
    higham9_11_complexBohteExampleU, hgrowth] using hnear
end NumStability
