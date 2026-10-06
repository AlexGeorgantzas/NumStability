-- Algorithms/Cholesky/AasenCoupledFpCh11Closure.lean
--
-- Higham, 2nd ed., Chapter 11, Theorem 11.8 — module #2 of the faithful 11.8
-- closure: the *coupled* floating-point Aasen factorization.
--
-- The existing Aasen tower (`AasenFactorNormCh11Closure`,
-- `Aasen118ReducedCh11Closure`) discharges the outer-factor norm caps but
-- explicitly leaves a gap: "nothing in the repository computes `T̂` in floating
-- point, so `|T̂ − T|` cannot yet be bounded."  This file fills that gap by
-- *constructing* the computed factors `L̂, Ĥ, T̂` from the actual Aasen
-- algorithm run in floating point.
--
-- The construction is **coupled**: each column step reads the *already
-- computed* prior columns of `L̂, Ĥ, T̂` (not exact reference values) and applies
-- the fp operations `fl_dotProduct`, `fl_sub`, `fl_div`, `fl_mul` of the
-- standard model.  Nothing is assumed about the recurrences — they hold *by
-- definition* of the step.
--
-- Deliverables consumed by module #3 (`AasenFactorResidualCh11Closure`):
--   * `FlAasenState`, `flAasenStep`, `flAasen`  — the constructive fp algorithm;
--   * `FlAasenPivots`                            — nonzero-subdiagonal predicate;
--   * `flAasen_L_unit_diag`, `flAasen_L_upper_zero`, `flAasen_L_first_col`,
--     `flAasen_T_symTridiagonal`                 — structural facts;
--   * `flAasen_recurrences`                      — the rounded Aasen equations
--     (11.12)/(11.13)/(11.14) hold pointwise for `L̂, Ĥ, T̂`.
--
-- Convention: identity permutation (`A` is assumed pre-permuted, matching the
-- `σ = id` specializations used throughout the exact-arith Aasen encodings in
-- `HighamChapter11.lean`).

import NumStability.Algorithms.Cholesky.AasenGrowthCh11Closure

open scoped BigOperators

namespace NumStability.Ch11Closure.AasenDirect

open NumStability

/-- Running state of the coupled floating-point Aasen sweep: the computed unit
lower-triangular factor `L̂`, the computed upper-Hessenberg working array
`Ĥ = T̂ L̂ᵀ`, and the computed symmetric tridiagonal middle factor `T̂`. -/
structure FlAasenState (n : ℕ) where
  /-- Computed unit lower-triangular Aasen factor `L̂`. -/
  Lhat : Fin n → Fin n → ℝ
  /-- Computed working array `Ĥ` (upper Hessenberg, `≈ T̂ L̂ᵀ`). -/
  Hhat : Fin n → Fin n → ℝ
  /-- Computed symmetric tridiagonal middle factor `T̂`. -/
  That : Fin n → Fin n → ℝ

/-- Initial state of the Aasen sweep: `L̂ = I`, `Ĥ = 0`, `T̂ = 0`. -/
def flAasenInit (n : ℕ) : FlAasenState n where
  Lhat := fun i j => if i = j then 1 else 0
  Hhat := fun _ _ => 0
  That := fun _ _ => 0

/-! ### Per-stage computed quantities

At stage `i` (`0 ≤ i < n`), reading only the already-computed prior columns held
in the state `s`, the algorithm forms the following floating-point quantities.
They are exposed as named definitions so that the structural facts and the
rounded recurrences can refer to them precisely. -/

/-- Strictly-upper entry of column `i` of `Ĥ`, `Ĥ_{r,i} = fl(T̂ row r · L̂ row i)`
(equation (11.11), `H = T Lᵀ` computed in floating point). -/
noncomputable def aUpperH (fp : FPModel) (n : ℕ) (s : FlAasenState n)
    (i : ℕ) (hi : i < n) (r : Fin n) : ℝ :=
  fl_dotProduct fp n (fun q => s.That r q) (fun q => s.Lhat ⟨i, hi⟩ q)

/-- Diagonal entry `Ĥ_{i,i}` via (11.12): `A_{i,i} − ∑_{j<i} L̂_{i,j} Ĥ_{j,i}`. -/
noncomputable def aHdiag (fp : FPModel) (n : ℕ) (A : Fin n → Fin n → ℝ)
    (s : FlAasenState n) (i : ℕ) (hi : i < n) : ℝ :=
  fp.fl_sub (A ⟨i, hi⟩ ⟨i, hi⟩)
    (fl_dotProduct fp n (fun j => if j.val < i then s.Lhat ⟨i, hi⟩ j else 0)
      (fun j => if j.val < i then aUpperH fp n s i hi j else 0))

/-- Column `i` of `Ĥ` restricted to rows `j ≤ i` (strictly-upper part plus the
diagonal), used as the working column by the (11.13)/(11.14) recurrences. -/
noncomputable def aHcol (fp : FPModel) (n : ℕ) (A : Fin n → Fin n → ℝ)
    (s : FlAasenState n) (i : ℕ) (hi : i < n) (j : Fin n) : ℝ :=
  if j.val < i then aUpperH fp n s i hi j
  else if j.val = i then aHdiag fp n A s i hi else 0

/-- Subdiagonal pivot `Ĥ_{i+1,i}` via (11.13):
`A_{i+1,i} − ∑_{j≤i} L̂_{i+1,j} Ĥ_{j,i}` (this is `β̂_i`). -/
noncomputable def aHsub (fp : FPModel) (n : ℕ) (A : Fin n → Fin n → ℝ)
    (s : FlAasenState n) (i : ℕ) (hi : i < n) : ℝ :=
  if hnext : i + 1 < n then
    fp.fl_sub (A ⟨i + 1, hnext⟩ ⟨i, hi⟩)
      (fl_dotProduct fp n
        (fun j => if j.val ≤ i then s.Lhat ⟨i + 1, hnext⟩ j else 0)
        (fun j => aHcol fp n A s i hi j))
  else 0

/-- α-extraction `T̂_{i,i} = fl(Ĥ_{i,i} − β̂_{i-1} L̂_{i,i-1})`.  The masked sum
picks out the single `p = i-1` term (and is `0` for `i = 0`). -/
noncomputable def aTdiag (fp : FPModel) (n : ℕ) (A : Fin n → Fin n → ℝ)
    (s : FlAasenState n) (i : ℕ) (hi : i < n) : ℝ :=
  fp.fl_sub (aHdiag fp n A s i hi)
    (∑ p : Fin n, if p.val + 1 = i then fp.fl_mul (s.That ⟨i, hi⟩ p) (s.Lhat ⟨i, hi⟩ p) else 0)

/-- Column `i+1` of `L̂` (row `k`, used for `k ≥ i+2`) via the (11.14)
multiplier: `L̂_{k,i+1} = fl((A_{k,i} − ∑_{j≤i} L̂_{k,j} Ĥ_{j,i}) / Ĥ_{i+1,i})`. -/
noncomputable def aLcol (fp : FPModel) (n : ℕ) (A : Fin n → Fin n → ℝ)
    (s : FlAasenState n) (i : ℕ) (hi : i < n) (k : Fin n) : ℝ :=
  fp.fl_div
    (fp.fl_sub (A k ⟨i, hi⟩)
      (fl_dotProduct fp n (fun j => if j.val ≤ i then s.Lhat k j else 0)
        (fun j => aHcol fp n A s i hi j)))
    (aHsub fp n A s i hi)

/-- One coupled column step of floating-point Aasen (stage `i`).

Reading only the already-computed prior columns held in `s`, stage `i` writes
column `i` of `Ĥ` (strictly-upper via `aUpperH`, diagonal via `aHdiag`,
subdiagonal via `aHsub`), the middle-factor entries `T̂_{i,i} = aTdiag` and the
symmetric subdiagonal `T̂_{i+1,i} = T̂_{i,i+1} = aHsub`, and column `i+1` of `L̂`
below the first subdiagonal via `aLcol`.  Entries not written at this stage are
copied unchanged from `s`. -/
noncomputable def flAasenStep (fp : FPModel) (n : ℕ) (A : Fin n → Fin n → ℝ)
    (i : ℕ) (s : FlAasenState n) : FlAasenState n :=
  if hi : i < n then
    { Lhat := fun k c =>
        if c.val = i + 1 ∧ i + 2 ≤ k.val then aLcol fp n A s i hi k else s.Lhat k c
      Hhat := fun r c =>
        if c.val = i then
          (if r.val < i then aUpperH fp n s i hi r
            else if r.val = i then aHdiag fp n A s i hi
            else if r.val = i + 1 then aHsub fp n A s i hi else 0)
        else s.Hhat r c
      That := fun r c =>
        if r.val = i ∧ c.val = i then aTdiag fp n A s i hi
        else if (r.val = i + 1 ∧ c.val = i) ∨ (r.val = i ∧ c.val = i + 1) then
          aHsub fp n A s i hi
        else s.That r c }
  else s

/-- Iterate `m` coupled Aasen steps from the initial state. -/
noncomputable def flAasenIter (fp : FPModel) (n : ℕ) (A : Fin n → Fin n → ℝ) :
    ℕ → FlAasenState n :=
  Nat.rec (flAasenInit n) (fun i s => flAasenStep fp n A i s)

/-- The computed floating-point Aasen factorization: run `n` coupled column
steps. -/
noncomputable def flAasen (fp : FPModel) (n : ℕ) (A : Fin n → Fin n → ℝ) :
    FlAasenState n :=
  flAasenIter fp n A n

/-- Nonzero-subdiagonal-pivot predicate for the coupled fp Aasen sweep: every
computed subdiagonal pivot `Ĥ_{i+1,i}` used by the (11.14) division is nonzero.
This is the fp analogue of the exact `AasenSpec` nonzero-pivot hypothesis and of
`FlAllOneSymmetricPivots`. -/
def FlAasenPivots (fp : FPModel) (n : ℕ) (A : Fin n → Fin n → ℝ) : Prop :=
  ∀ (i : ℕ) (h : i + 1 < n),
    (flAasen fp n A).Hhat ⟨i + 1, h⟩ ⟨i, Nat.lt_of_succ_lt h⟩ ≠ 0

/-- Unfolding lemma: one more iteration is one more step. -/
theorem flAasenIter_succ (fp : FPModel) (n : ℕ) (A : Fin n → Fin n → ℝ) (m : ℕ) :
    flAasenIter fp n A (m + 1) = flAasenStep fp n A m (flAasenIter fp n A m) :=
  rfl

/-! ### Single-step preserve/write lemmas

These characterise which entries a single stage `i` touches.  A stage writes
only column `i` of `Ĥ`, the band entries `(i,i)`, `(i+1,i)`, `(i,i+1)` of `T̂`,
and column `i+1` of `L̂` below the first subdiagonal; every other entry is
copied unchanged. -/

/-- Stage `i` leaves `Ĥ` untouched away from column `i`. -/
theorem flAasenStep_Hhat_of_col_ne (fp : FPModel) (n : ℕ) (A : Fin n → Fin n → ℝ)
    (i : ℕ) (s : FlAasenState n) (r c : Fin n) (h : c.val ≠ i) :
    (flAasenStep fp n A i s).Hhat r c = s.Hhat r c := by
  by_cases hi : i < n
  · simp only [flAasenStep, dif_pos hi, if_neg h]
  · simp only [flAasenStep, dif_neg hi]

/-- Stage `i` writes column `i` of `Ĥ` with the computed upper/diagonal/
subdiagonal values. -/
theorem flAasenStep_Hhat_write (fp : FPModel) (n : ℕ) (A : Fin n → Fin n → ℝ)
    (s : FlAasenState n) (i : ℕ) (hi : i < n) (r c : Fin n) (hc : c.val = i) :
    (flAasenStep fp n A i s).Hhat r c
      = (if r.val < i then aUpperH fp n s i hi r
          else if r.val = i then aHdiag fp n A s i hi
          else if r.val = i + 1 then aHsub fp n A s i hi else 0) := by
  simp only [flAasenStep, dif_pos hi, if_pos hc]

/-- Stage `i` leaves `L̂` untouched away from column `i+1` below the first
subdiagonal. -/
theorem flAasenStep_Lhat_of_ne (fp : FPModel) (n : ℕ) (A : Fin n → Fin n → ℝ)
    (i : ℕ) (s : FlAasenState n) (k c : Fin n)
    (h : ¬ (c.val = i + 1 ∧ i + 2 ≤ k.val)) :
    (flAasenStep fp n A i s).Lhat k c = s.Lhat k c := by
  by_cases hi : i < n
  · simp only [flAasenStep, dif_pos hi, if_neg h]
  · simp only [flAasenStep, dif_neg hi]

/-- Stage `i` writes the `(k, i+1)` multiplier of `L̂` for `k ≥ i+2`. -/
theorem flAasenStep_Lhat_write (fp : FPModel) (n : ℕ) (A : Fin n → Fin n → ℝ)
    (s : FlAasenState n) (i : ℕ) (hi : i < n) (k c : Fin n)
    (hc : c.val = i + 1) (hk : i + 2 ≤ k.val) :
    (flAasenStep fp n A i s).Lhat k c = aLcol fp n A s i hi k := by
  simp only [flAasenStep, dif_pos hi, if_pos (And.intro hc hk)]

/-- Stage `i` leaves `T̂` untouched away from the band entries it writes. -/
theorem flAasenStep_That_of_ne (fp : FPModel) (n : ℕ) (A : Fin n → Fin n → ℝ)
    (i : ℕ) (s : FlAasenState n) (r c : Fin n)
    (h1 : ¬ (r.val = i ∧ c.val = i))
    (h2 : ¬ ((r.val = i + 1 ∧ c.val = i) ∨ (r.val = i ∧ c.val = i + 1))) :
    (flAasenStep fp n A i s).That r c = s.That r c := by
  by_cases hi : i < n
  · simp only [flAasenStep, dif_pos hi, if_neg h1, if_neg h2]
  · simp only [flAasenStep, dif_neg hi]

/-- Stage `i` writes the diagonal `T̂_{i,i} = α̂_i`. -/
theorem flAasenStep_That_diag (fp : FPModel) (n : ℕ) (A : Fin n → Fin n → ℝ)
    (s : FlAasenState n) (i : ℕ) (hi : i < n) (r c : Fin n)
    (hr : r.val = i) (hc : c.val = i) :
    (flAasenStep fp n A i s).That r c = aTdiag fp n A s i hi := by
  simp only [flAasenStep, dif_pos hi, if_pos (And.intro hr hc)]

/-- Stage `i` writes the symmetric subdiagonal `T̂_{i+1,i} = T̂_{i,i+1} = β̂_i`. -/
theorem flAasenStep_That_sub (fp : FPModel) (n : ℕ) (A : Fin n → Fin n → ℝ)
    (s : FlAasenState n) (i : ℕ) (hi : i < n) (r c : Fin n)
    (h : (r.val = i + 1 ∧ c.val = i) ∨ (r.val = i ∧ c.val = i + 1)) :
    (flAasenStep fp n A i s).That r c = aHsub fp n A s i hi := by
  have h1 : ¬ (r.val = i ∧ c.val = i) := by
    rcases h with ⟨ha, hb⟩ | ⟨ha, hb⟩ <;> omega
  simp only [flAasenStep, dif_pos hi, if_neg h1, if_pos h]

/-! ### Structural invariant and structural facts

`L̂` stays unit lower triangular with first column `e₁`, and `T̂` stays symmetric
tridiagonal, throughout the sweep.  These are proved by a single invariant that
each stage preserves. -/

/-- Structural invariant maintained by every stage: `L̂` unit lower triangular
with first column `e₁`, and `T̂` symmetric tridiagonal. -/
def StructInv {n : ℕ} (s : FlAasenState n) : Prop :=
  (∀ d : Fin n, s.Lhat d d = 1) ∧
  (∀ k c : Fin n, k.val < c.val → s.Lhat k c = 0) ∧
  (∀ k c : Fin n, c.val = 0 → k.val ≠ 0 → s.Lhat k c = 0) ∧
  (∀ r c : Fin n, s.That r c = s.That c r) ∧
  (∀ r c : Fin n, r.val + 1 < c.val ∨ c.val + 1 < r.val → s.That r c = 0)

/-- The initial state satisfies the structural invariant. -/
theorem structInv_init (n : ℕ) : StructInv (flAasenInit n) := by
  refine ⟨?_, ?_, ?_, ?_, ?_⟩
  · intro d; simp [flAasenInit]
  · intro k c h
    have hne : k ≠ c := by rintro rfl; omega
    simp only [flAasenInit, if_neg hne]
  · intro k c hc hk
    have hne : k ≠ c := by rintro rfl; exact hk hc
    simp only [flAasenInit, if_neg hne]
  · intro r c; simp [flAasenInit]
  · intro r c h; simp [flAasenInit]

/-- A single stage preserves the structural invariant. -/
theorem structInv_step (fp : FPModel) (n : ℕ) (A : Fin n → Fin n → ℝ)
    (i : ℕ) (s : FlAasenState n) (h : StructInv s) :
    StructInv (flAasenStep fp n A i s) := by
  obtain ⟨hd, hu, hf, hsym, hband⟩ := h
  by_cases hi : i < n
  · refine ⟨?_, ?_, ?_, ?_, ?_⟩
    · intro d
      rw [flAasenStep_Lhat_of_ne fp n A i s d d (by rintro ⟨e1, e2⟩; omega)]
      exact hd d
    · intro k c hkc
      rw [flAasenStep_Lhat_of_ne fp n A i s k c (by rintro ⟨e1, e2⟩; omega)]
      exact hu k c hkc
    · intro k c hc hk
      rw [flAasenStep_Lhat_of_ne fp n A i s k c (by rintro ⟨e1, e2⟩; omega)]
      exact hf k c hc hk
    · intro r c
      by_cases hdg : r.val = i ∧ c.val = i
      · rw [flAasenStep_That_diag fp n A s i hi r c hdg.1 hdg.2,
            flAasenStep_That_diag fp n A s i hi c r hdg.2 hdg.1]
      · by_cases hsub : (r.val = i + 1 ∧ c.val = i) ∨ (r.val = i ∧ c.val = i + 1)
        · rw [flAasenStep_That_sub fp n A s i hi r c hsub,
              flAasenStep_That_sub fp n A s i hi c r (by tauto)]
        · rw [flAasenStep_That_of_ne fp n A i s r c hdg hsub,
              flAasenStep_That_of_ne fp n A i s c r (by tauto) (by tauto)]
          exact hsym r c
    · intro r c hbnd
      have h1 : ¬ (r.val = i ∧ c.val = i) := by rintro ⟨e1, e2⟩; omega
      have h2 : ¬ ((r.val = i + 1 ∧ c.val = i) ∨ (r.val = i ∧ c.val = i + 1)) := by
        rintro (⟨e1, e2⟩ | ⟨e1, e2⟩) <;> omega
      rw [flAasenStep_That_of_ne fp n A i s r c h1 h2]
      exact hband r c hbnd
  · simp only [flAasenStep, dif_neg hi]
    exact ⟨hd, hu, hf, hsym, hband⟩

/-- Every iterate satisfies the structural invariant. -/
theorem structInv_iter (fp : FPModel) (n : ℕ) (A : Fin n → Fin n → ℝ) (m : ℕ) :
    StructInv (flAasenIter fp n A m) := by
  induction m with
  | zero => exact structInv_init n
  | succ p ih =>
      rw [flAasenIter_succ]
      exact structInv_step fp n A p (flAasenIter fp n A p) ih

/-- **Structural fact:** `L̂` has unit diagonal. -/
theorem flAasen_L_unit_diag (fp : FPModel) (n : ℕ) (A : Fin n → Fin n → ℝ) (d : Fin n) :
    (flAasen fp n A).Lhat d d = 1 :=
  (structInv_iter fp n A n).1 d

/-- **Structural fact:** `L̂` is lower triangular. -/
theorem flAasen_L_upper_zero (fp : FPModel) (n : ℕ) (A : Fin n → Fin n → ℝ)
    (k c : Fin n) (h : k.val < c.val) :
    (flAasen fp n A).Lhat k c = 0 :=
  (structInv_iter fp n A n).2.1 k c h

/-- **Structural fact:** the first column of `L̂` is `e₁` (partial pivoting). -/
theorem flAasen_L_first_col (fp : FPModel) (n : ℕ) (A : Fin n → Fin n → ℝ)
    (k c : Fin n) (hc : c.val = 0) (hk : k.val ≠ 0) :
    (flAasen fp n A).Lhat k c = 0 :=
  (structInv_iter fp n A n).2.2.1 k c hc hk

/-- **Structural fact:** `T̂` is symmetric. -/
theorem flAasen_T_symm (fp : FPModel) (n : ℕ) (A : Fin n → Fin n → ℝ) (r c : Fin n) :
    (flAasen fp n A).That r c = (flAasen fp n A).That c r :=
  (structInv_iter fp n A n).2.2.2.1 r c

/-- **Structural fact:** `T̂` is tridiagonal. -/
theorem flAasen_T_band (fp : FPModel) (n : ℕ) (A : Fin n → Fin n → ℝ)
    (r c : Fin n) (h : r.val + 1 < c.val ∨ c.val + 1 < r.val) :
    (flAasen fp n A).That r c = 0 :=
  (structInv_iter fp n A n).2.2.2.2 r c h

/-- **Structural fact:** `T̂` is symmetric tridiagonal (the `IsSymTridiagonal`
predicate consumed by the Aasen middle-factor endpoints). -/
theorem flAasen_T_symTridiagonal (fp : FPModel) (n : ℕ) (A : Fin n → Fin n → ℝ) :
    IsSymTridiagonal n (flAasen fp n A).That :=
  ⟨flAasen_T_symm fp n A, flAasen_T_band fp n A⟩

/-! ### Freezing lemmas: the final state exposes each stage's written values

Once stage `i` writes an entry it is never overwritten, so the final
factorization `flAasen = flAasenIter n` exposes exactly the value each stage
computed.  These lemmas turn `flAasen`-level entries into the per-stage
quantities `aUpperH`, `aHdiag`, `aHsub`, `aLcol`, which is what the rounded
recurrences need. -/

/-- Column `c` of `Ĥ`, once written at stage `c.val`, is frozen. -/
theorem flAasenIter_Hhat_freeze (fp : FPModel) (n : ℕ) (A : Fin n → Fin n → ℝ)
    (r c : Fin n) (d : ℕ) :
    (flAasenIter fp n A (c.val + 1 + d)).Hhat r c
      = (flAasenIter fp n A (c.val + 1)).Hhat r c := by
  induction d with
  | zero => rfl
  | succ e ih =>
      have hrw : c.val + 1 + (e + 1) = (c.val + 1 + e) + 1 := by ring
      rw [hrw, flAasenIter_succ,
        flAasenStep_Hhat_of_col_ne fp n A (c.val + 1 + e)
          (flAasenIter fp n A (c.val + 1 + e)) r c (by omega)]
      exact ih

/-- The final `Ĥ` agrees with the state right after column `c` is written. -/
theorem flAasen_Hhat_col_eq (fp : FPModel) (n : ℕ) (A : Fin n → Fin n → ℝ)
    (r c : Fin n) :
    (flAasen fp n A).Hhat r c = (flAasenIter fp n A (c.val + 1)).Hhat r c := by
  have hc := c.isLt
  have hn : flAasenIter fp n A n = flAasenIter fp n A (c.val + 1 + (n - (c.val + 1))) := by
    congr 1; omega
  unfold flAasen
  rw [hn]
  exact flAasenIter_Hhat_freeze fp n A r c (n - (c.val + 1))

/-- Final-state characterisation of every `Ĥ` entry in terms of the per-stage
computed quantities. -/
theorem flAasen_Hhat_eq (fp : FPModel) (n : ℕ) (A : Fin n → Fin n → ℝ) (r c : Fin n) :
    (flAasen fp n A).Hhat r c
      = (if r.val < c.val then aUpperH fp n (flAasenIter fp n A c.val) c.val c.isLt r
          else if r.val = c.val then aHdiag fp n A (flAasenIter fp n A c.val) c.val c.isLt
          else if r.val = c.val + 1 then aHsub fp n A (flAasenIter fp n A c.val) c.val c.isLt
          else 0) := by
  rw [flAasen_Hhat_col_eq, flAasenIter_succ,
    flAasenStep_Hhat_write fp n A (flAasenIter fp n A c.val) c.val c.isLt r c rfl]

/-- Strictly-upper `Ĥ` entries expose `aUpperH`. -/
theorem flAasen_Hhat_upper (fp : FPModel) (n : ℕ) (A : Fin n → Fin n → ℝ)
    (i j : Fin n) (hj : j.val < i.val) :
    (flAasen fp n A).Hhat j i = aUpperH fp n (flAasenIter fp n A i.val) i.val i.isLt j := by
  rw [flAasen_Hhat_eq, if_pos hj]

/-- Diagonal `Ĥ` entries expose `aHdiag`. -/
theorem flAasen_Hhat_diag (fp : FPModel) (n : ℕ) (A : Fin n → Fin n → ℝ) (i : Fin n) :
    (flAasen fp n A).Hhat i i = aHdiag fp n A (flAasenIter fp n A i.val) i.val i.isLt := by
  rw [flAasen_Hhat_eq, if_neg (lt_irrefl i.val), if_pos rfl]

/-- Subdiagonal `Ĥ` entries (the pivots) expose `aHsub`. -/
theorem flAasen_Hhat_subdiag (fp : FPModel) (n : ℕ) (A : Fin n → Fin n → ℝ)
    (i : Fin n) (hnext : i.val + 1 < n) :
    (flAasen fp n A).Hhat ⟨i.val + 1, hnext⟩ i
      = aHsub fp n A (flAasenIter fp n A i.val) i.val i.isLt := by
  rw [flAasen_Hhat_eq,
    if_neg (by omega : ¬ (i.val + 1 < i.val)),
    if_neg (by omega : ¬ (i.val + 1 = i.val)), if_pos rfl]

/-- **Structural fact:** `Ĥ` is upper Hessenberg. -/
theorem flAasen_H_upperHessenberg (fp : FPModel) (n : ℕ) (A : Fin n → Fin n → ℝ)
    (r c : Fin n) (h : c.val + 1 < r.val) :
    (flAasen fp n A).Hhat r c = 0 := by
  rw [flAasen_Hhat_eq,
    if_neg (by omega : ¬ (r.val < c.val)),
    if_neg (by omega : ¬ (r.val = c.val)),
    if_neg (by omega : ¬ (r.val = c.val + 1))]

/-- Column `c` of `L̂`, once written at stage `c.val - 1`, is frozen from stage
`c.val` on. -/
theorem flAasenIter_Lhat_freeze (fp : FPModel) (n : ℕ) (A : Fin n → Fin n → ℝ)
    (k c : Fin n) (d : ℕ) :
    (flAasenIter fp n A (c.val + d)).Lhat k c = (flAasenIter fp n A c.val).Lhat k c := by
  induction d with
  | zero => rfl
  | succ e ih =>
      have hrw : c.val + (e + 1) = (c.val + e) + 1 := by ring
      rw [hrw, flAasenIter_succ,
        flAasenStep_Lhat_of_ne fp n A (c.val + e) (flAasenIter fp n A (c.val + e))
          k c (by rintro ⟨e1, e2⟩; omega)]
      exact ih

/-- The final `L̂` agrees with any iterate at least as far as `c.val`. -/
theorem flAasenIter_Lhat_eq_flAasen (fp : FPModel) (n : ℕ) (A : Fin n → Fin n → ℝ)
    (k c : Fin n) (m : ℕ) (hm : c.val ≤ m) :
    (flAasenIter fp n A m).Lhat k c = (flAasen fp n A).Lhat k c := by
  have hc := c.isLt
  have key : (flAasen fp n A).Lhat k c = (flAasenIter fp n A c.val).Lhat k c := by
    have hn : flAasenIter fp n A n = flAasenIter fp n A (c.val + (n - c.val)) := by
      congr 1; omega
    unfold flAasen; rw [hn]
    exact flAasenIter_Lhat_freeze fp n A k c (n - c.val)
  rw [key]
  have hn : flAasenIter fp n A m = flAasenIter fp n A (c.val + (m - c.val)) := by
    congr 1; omega
  rw [hn]
  exact flAasenIter_Lhat_freeze fp n A k c (m - c.val)

/-- Column `i+1` of `L̂` exposes the `aLcol` multiplier for rows `k ≥ i+2`. -/
theorem flAasen_Lhat_write (fp : FPModel) (n : ℕ) (A : Fin n → Fin n → ℝ)
    (i : ℕ) (hi : i < n) (k c : Fin n) (hc : c.val = i + 1) (hk : i + 2 ≤ k.val) :
    (flAasen fp n A).Lhat k c = aLcol fp n A (flAasenIter fp n A i) i hi k := by
  have key : (flAasen fp n A).Lhat k c = (flAasenIter fp n A c.val).Lhat k c := by
    have hc' := c.isLt
    have hn : flAasenIter fp n A n = flAasenIter fp n A (c.val + (n - c.val)) := by
      congr 1; omega
    unfold flAasen; rw [hn]
    exact flAasenIter_Lhat_freeze fp n A k c (n - c.val)
  rw [key, hc, flAasenIter_succ,
    flAasenStep_Lhat_write fp n A (flAasenIter fp n A i) i hi k c hc hk]

/-- The `aHcol` working column at stage `i` exposes the final `Ĥ` column `i`
(masked to rows `j ≤ i`). -/
theorem aHcol_iter_eq_flAasen (fp : FPModel) (n : ℕ) (A : Fin n → Fin n → ℝ)
    (i j : Fin n) :
    aHcol fp n A (flAasenIter fp n A i.val) i.val i.isLt j
      = if j.val ≤ i.val then (flAasen fp n A).Hhat j i else 0 := by
  unfold aHcol
  by_cases hj1 : j.val < i.val
  · rw [if_pos hj1, if_pos (le_of_lt hj1), flAasen_Hhat_upper fp n A i j hj1]
  · by_cases hj2 : j.val = i.val
    · rw [if_neg hj1, if_pos hj2, if_pos (le_of_eq hj2)]
      have hji : j = i := Fin.ext hj2
      rw [hji, flAasen_Hhat_diag fp n A i]
    · rw [if_neg hj1, if_neg hj2, if_neg (by omega : ¬ j.val ≤ i.val)]

/-! ### The rounded Aasen recurrences

The computed factors `L̂, Ĥ, T̂` satisfy the rounded forms of the exact Aasen
equations (11.12)/(11.13)/(11.14), *by definition* of the coupled step.  These
are the equations module #3 rewrites with to bound the factorization residual
`|(L̂ Ĥ)_{k,i} − A_{k,i}|`. -/

/-- **Rounded equation (11.12)** (diagonal of `A = L̂ Ĥ`).  The computed diagonal
`Ĥ_{i,i}` is the floating-point subtraction of the masked dot product
`∑_{j<i} L̂_{i,j} Ĥ_{j,i}` from `A_{i,i}`. -/
theorem flAasen_recurrence_diagonal (fp : FPModel) (n : ℕ) (A : Fin n → Fin n → ℝ)
    (i : Fin n) :
    (flAasen fp n A).Hhat i i
      = fp.fl_sub (A i i)
          (fl_dotProduct fp n
            (fun j => if j.val < i.val then (flAasen fp n A).Lhat i j else 0)
            (fun j => if j.val < i.val then (flAasen fp n A).Hhat j i else 0)) := by
  rw [flAasen_Hhat_diag fp n A i]
  unfold aHdiag
  have hX : (fun j => if j.val < i.val then
              (flAasenIter fp n A i.val).Lhat ⟨i.val, i.isLt⟩ j else 0)
          = (fun j : Fin n => if j.val < i.val then (flAasen fp n A).Lhat i j else 0) := by
    funext j
    by_cases hj : j.val < i.val
    · rw [if_pos hj, if_pos hj]
      exact flAasenIter_Lhat_eq_flAasen fp n A i j i.val (le_of_lt hj)
    · rw [if_neg hj, if_neg hj]
  have hY : (fun j => if j.val < i.val then
              aUpperH fp n (flAasenIter fp n A i.val) i.val i.isLt j else 0)
          = (fun j : Fin n => if j.val < i.val then (flAasen fp n A).Hhat j i else 0) := by
    funext j
    by_cases hj : j.val < i.val
    · rw [if_pos hj, if_pos hj, flAasen_Hhat_upper fp n A i j hj]
    · rw [if_neg hj, if_neg hj]
  rw [hX, hY]

/-- **Rounded equation (11.13)** (subdiagonal of `A = L̂ Ĥ`).  The computed pivot
`Ĥ_{i+1,i}` is the floating-point subtraction of the masked dot product
`∑_{j≤i} L̂_{i+1,j} Ĥ_{j,i}` from `A_{i+1,i}`. -/
theorem flAasen_recurrence_subdiagonal (fp : FPModel) (n : ℕ) (A : Fin n → Fin n → ℝ)
    (i : Fin n) (hnext : i.val + 1 < n) :
    (flAasen fp n A).Hhat ⟨i.val + 1, hnext⟩ i
      = fp.fl_sub (A ⟨i.val + 1, hnext⟩ i)
          (fl_dotProduct fp n
            (fun j => if j.val ≤ i.val then (flAasen fp n A).Lhat ⟨i.val + 1, hnext⟩ j else 0)
            (fun j => if j.val ≤ i.val then (flAasen fp n A).Hhat j i else 0)) := by
  rw [flAasen_Hhat_subdiag fp n A i hnext]
  unfold aHsub
  rw [dif_pos hnext]
  have hX : (fun j => if j.val ≤ i.val then
              (flAasenIter fp n A i.val).Lhat ⟨i.val + 1, hnext⟩ j else 0)
          = (fun j : Fin n => if j.val ≤ i.val then
              (flAasen fp n A).Lhat ⟨i.val + 1, hnext⟩ j else 0) := by
    funext j
    by_cases hj : j.val ≤ i.val
    · rw [if_pos hj, if_pos hj]
      exact flAasenIter_Lhat_eq_flAasen fp n A ⟨i.val + 1, hnext⟩ j i.val hj
    · rw [if_neg hj, if_neg hj]
  have hY : (fun j => aHcol fp n A (flAasenIter fp n A i.val) i.val i.isLt j)
          = (fun j : Fin n => if j.val ≤ i.val then (flAasen fp n A).Hhat j i else 0) := by
    funext j; exact aHcol_iter_eq_flAasen fp n A i j
  rw [hX, hY]

/-- **Rounded equation (11.14)** (next column of `L̂`).  For `k ≥ i+2`, the
computed multiplier `L̂_{k,i+1}` is the floating-point quotient by the pivot
`Ĥ_{i+1,i}` of `A_{k,i} − ∑_{j≤i} L̂_{k,j} Ĥ_{j,i}`. -/
theorem flAasen_recurrence_nextColumn (fp : FPModel) (n : ℕ) (A : Fin n → Fin n → ℝ)
    (i : Fin n) (hnext : i.val + 1 < n) (k : Fin n) (hk : i.val + 2 ≤ k.val) :
    (flAasen fp n A).Lhat k ⟨i.val + 1, hnext⟩
      = fp.fl_div
          (fp.fl_sub (A k i)
            (fl_dotProduct fp n
              (fun j => if j.val ≤ i.val then (flAasen fp n A).Lhat k j else 0)
              (fun j => if j.val ≤ i.val then (flAasen fp n A).Hhat j i else 0)))
          ((flAasen fp n A).Hhat ⟨i.val + 1, hnext⟩ i) := by
  rw [flAasen_Lhat_write fp n A i.val i.isLt k ⟨i.val + 1, hnext⟩ rfl hk]
  unfold aLcol
  have hX : (fun j => if j.val ≤ i.val then (flAasenIter fp n A i.val).Lhat k j else 0)
          = (fun j : Fin n => if j.val ≤ i.val then (flAasen fp n A).Lhat k j else 0) := by
    funext j
    by_cases hj : j.val ≤ i.val
    · rw [if_pos hj, if_pos hj]
      exact flAasenIter_Lhat_eq_flAasen fp n A k j i.val hj
    · rw [if_neg hj, if_neg hj]
  have hY : (fun j => aHcol fp n A (flAasenIter fp n A i.val) i.val i.isLt j)
          = (fun j : Fin n => if j.val ≤ i.val then (flAasen fp n A).Hhat j i else 0) := by
    funext j; exact aHcol_iter_eq_flAasen fp n A i j
  rw [hX, hY, flAasen_Hhat_subdiag fp n A i hnext]

/-- **The rounded Aasen recurrences**, bundled.  The computed factors `L̂, Ĥ`
satisfy the floating-point forms of (11.12), (11.13) and (11.14) pointwise —
*by definition* of the coupled fp Aasen step.  Together with the upper-Hessenberg
structure of `Ĥ` (`flAasen_H_upperHessenberg`) and the structural facts, this is
the foundation module #3 consumes to bound `|(L̂ Ĥ)_{k,i} − A_{k,i}|`. -/
theorem flAasen_recurrences (fp : FPModel) (n : ℕ) (A : Fin n → Fin n → ℝ) :
    (∀ i : Fin n,
      (flAasen fp n A).Hhat i i
        = fp.fl_sub (A i i)
            (fl_dotProduct fp n
              (fun j => if j.val < i.val then (flAasen fp n A).Lhat i j else 0)
              (fun j => if j.val < i.val then (flAasen fp n A).Hhat j i else 0))) ∧
    (∀ (i : Fin n) (hnext : i.val + 1 < n),
      (flAasen fp n A).Hhat ⟨i.val + 1, hnext⟩ i
        = fp.fl_sub (A ⟨i.val + 1, hnext⟩ i)
            (fl_dotProduct fp n
              (fun j => if j.val ≤ i.val then (flAasen fp n A).Lhat ⟨i.val + 1, hnext⟩ j else 0)
              (fun j => if j.val ≤ i.val then (flAasen fp n A).Hhat j i else 0))) ∧
    (∀ (i : Fin n) (hnext : i.val + 1 < n) (k : Fin n) (_hk : i.val + 2 ≤ k.val),
      (flAasen fp n A).Lhat k ⟨i.val + 1, hnext⟩
        = fp.fl_div
            (fp.fl_sub (A k i)
              (fl_dotProduct fp n
                (fun j => if j.val ≤ i.val then (flAasen fp n A).Lhat k j else 0)
                (fun j => if j.val ≤ i.val then (flAasen fp n A).Hhat j i else 0)))
            ((flAasen fp n A).Hhat ⟨i.val + 1, hnext⟩ i)) :=
  ⟨flAasen_recurrence_diagonal fp n A,
   flAasen_recurrence_subdiagonal fp n A,
   fun i hnext k hk => flAasen_recurrence_nextColumn fp n A i hnext k hk⟩

/-! ### Middle-factor relations (`T̂` versus `Ĥ`)

The `α`/`β` extraction relates the computed middle factor `T̂` to the working
array `Ĥ`.  These are what module #3's `H = T̂ L̂ᵀ` residual (`B2`) consumes. -/

/-- The diagonal `T̂_{i,i}`, once written at stage `i`, is frozen. -/
theorem flAasenIter_That_diag_freeze (fp : FPModel) (n : ℕ) (A : Fin n → Fin n → ℝ)
    (i : Fin n) (d : ℕ) :
    (flAasenIter fp n A (i.val + 1 + d)).That i i
      = (flAasenIter fp n A (i.val + 1)).That i i := by
  induction d with
  | zero => rfl
  | succ e ih =>
      have hrw : i.val + 1 + (e + 1) = (i.val + 1 + e) + 1 := by ring
      rw [hrw, flAasenIter_succ,
        flAasenStep_That_of_ne fp n A (i.val + 1 + e) (flAasenIter fp n A (i.val + 1 + e))
          i i (by rintro ⟨e1, e2⟩; omega) (by rintro (⟨e1, e2⟩ | ⟨e1, e2⟩) <;> omega)]
      exact ih

/-- **α-extraction:** the computed diagonal `T̂_{i,i}` equals
`fl(Ĥ_{i,i} − β̂_{i-1} L̂_{i,i-1})` (`= aTdiag`). -/
theorem flAasen_T_diag_eq (fp : FPModel) (n : ℕ) (A : Fin n → Fin n → ℝ) (i : Fin n) :
    (flAasen fp n A).That i i = aTdiag fp n A (flAasenIter fp n A i.val) i.val i.isLt := by
  have hc := i.isLt
  have hn : flAasenIter fp n A n = flAasenIter fp n A (i.val + 1 + (n - (i.val + 1))) := by
    congr 1; omega
  unfold flAasen
  rw [hn, flAasenIter_That_diag_freeze fp n A i (n - (i.val + 1)), flAasenIter_succ,
    flAasenStep_That_diag fp n A (flAasenIter fp n A i.val) i.val i.isLt i i rfl rfl]

/-- The subdiagonal `T̂_{i+1,i}`, once written at stage `i`, is frozen. -/
theorem flAasenIter_That_sub_freeze (fp : FPModel) (n : ℕ) (A : Fin n → Fin n → ℝ)
    (i : Fin n) (hnext : i.val + 1 < n) (d : ℕ) :
    (flAasenIter fp n A (i.val + 1 + d)).That ⟨i.val + 1, hnext⟩ i
      = (flAasenIter fp n A (i.val + 1)).That ⟨i.val + 1, hnext⟩ i := by
  induction d with
  | zero => rfl
  | succ e ih =>
      have hrw : i.val + 1 + (e + 1) = (i.val + 1 + e) + 1 := by ring
      rw [hrw, flAasenIter_succ,
        flAasenStep_That_of_ne fp n A (i.val + 1 + e) (flAasenIter fp n A (i.val + 1 + e))
          ⟨i.val + 1, hnext⟩ i (by rintro ⟨e1, e2⟩; omega)
          (by rintro (⟨e1, e2⟩ | ⟨e1, e2⟩) <;> omega)]
      exact ih

/-- The subdiagonal `T̂_{i+1,i}` equals the computed pivot `aHsub`. -/
theorem flAasen_T_sub_eq (fp : FPModel) (n : ℕ) (A : Fin n → Fin n → ℝ)
    (i : Fin n) (hnext : i.val + 1 < n) :
    (flAasen fp n A).That ⟨i.val + 1, hnext⟩ i
      = aHsub fp n A (flAasenIter fp n A i.val) i.val i.isLt := by
  have hn : flAasenIter fp n A n = flAasenIter fp n A (i.val + 1 + (n - (i.val + 1))) := by
    have := i.isLt; congr 1; omega
  unfold flAasen
  rw [hn, flAasenIter_That_sub_freeze fp n A i hnext (n - (i.val + 1)), flAasenIter_succ,
    flAasenStep_That_sub fp n A (flAasenIter fp n A i.val) i.val i.isLt ⟨i.val + 1, hnext⟩ i
      (Or.inl ⟨rfl, rfl⟩)]

/-- **β-extraction (exact):** the computed subdiagonal `T̂_{i+1,i}` equals the
computed working-array pivot `Ĥ_{i+1,i}` with no rounding.  This is the identity
`β̂_i = Ĥ_{i+1,i}` that makes the `H = T̂ L̂ᵀ` subdiagonal residual exact. -/
theorem flAasen_T_subdiagonal_eq_H (fp : FPModel) (n : ℕ) (A : Fin n → Fin n → ℝ)
    (i : Fin n) (hnext : i.val + 1 < n) :
    (flAasen fp n A).That ⟨i.val + 1, hnext⟩ i
      = (flAasen fp n A).Hhat ⟨i.val + 1, hnext⟩ i := by
  rw [flAasen_T_sub_eq fp n A i hnext, flAasen_Hhat_subdiag fp n A i hnext]

/-- General freezing utility for `T̂`: away from the last stage that can touch it,
an entry `(r,c)` with `r.val < t` and `c.val < t` is constant. -/
theorem flAasenIter_That_freeze_gap (fp : FPModel) (n : ℕ) (A : Fin n → Fin n → ℝ)
    (r c : Fin n) (t d : ℕ) (hr : r.val < t) (_hc : c.val < t) :
    (flAasenIter fp n A (t + d)).That r c = (flAasenIter fp n A t).That r c := by
  induction d with
  | zero => rfl
  | succ e ih =>
      have hrw : t + (e + 1) = (t + e) + 1 := by ring
      rw [hrw, flAasenIter_succ,
        flAasenStep_That_of_ne fp n A (t + e) (flAasenIter fp n A (t + e)) r c
          (by rintro ⟨e1, e2⟩; omega) (by rintro (⟨e1, e2⟩ | ⟨e1, e2⟩) <;> omega)]
      exact ih

end NumStability.Ch11Closure.AasenDirect
