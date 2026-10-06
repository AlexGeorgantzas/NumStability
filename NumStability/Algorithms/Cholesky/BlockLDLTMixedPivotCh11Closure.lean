/-
Chapter 11 closure: printed-strength backward-error bound for the MIXED-pivot
(1×1 and 2×2 pivots, no interchange, σ = id) floating-point block-LDLᵀ
factorization.

This file builds directly on the completed, verified all-1×1-pivot closure
module `BlockLDLTAllOneByOnePrintedCh11Closure`.  It introduces a `PivotSchedule`
that records, stage by stage, whether a 1×1 or a 2×2 pivot is used, constructs
NAMED computed factors `L̂, D̂` for the recursive rounded mixed-pivot path,
proves the entrywise backward-error envelope for those named factors by
structural induction on the schedule, and shows the envelope is dominated by the
printed Theorem 11.3 first-order bound `p(n)·u·(|A| + |L̂||D̂||L̂ᵀ|)` with a
LINEAR polynomial `p`.

Honesty note on hypotheses (see the closing comment for the precise status):
  * The 1×1 stages are fully DERIVED from the floating-point model, reusing the
    verified all-1×1 machinery.
  * Each 2×2 stage rests on an explicit per-stage backward-error hypothesis
    carried by `FlMixedPivots` (the 2×2 solve/Schur envelope, eq. (11.5) plus
    the assembled 2×2 trailing envelope).  This is documented as a conditional
    partial; the standalone 2×2 trailing lemma is isolated with its exact
    statement.
-/
import NumStability.Algorithms.Cholesky.BlockLDLTAllOneByOnePrintedCh11Closure

open scoped BigOperators

namespace NumStability.Ch11Closure.Mixed

open NumStability
open NumStability.Ch11Closure

/-! ## Task 1 — the pivot schedule and its index embeddings -/

/-- A pivot schedule for a size-`n` symmetric block-LDLᵀ factorization.  Reading
    left to right, each constructor peels one leading pivot off the front:
    `consOne` a 1×1 pivot (size `n → n+1`) and `consTwo` a 2×2 pivot
    (size `n → n+2`).  Structural recursion on this type drives the whole
    mixed-pivot analysis (no well-founded recursion is needed). -/
inductive PivotSchedule : ℕ → Type
  | nil : PivotSchedule 0
  | consOne : {n : ℕ} → PivotSchedule n → PivotSchedule (n + 1)
  | consTwo : {n : ℕ} → PivotSchedule n → PivotSchedule (n + 2)

/-- Embed one of the two leading indices `{0,1}` of a 2×2 pivot block into
    `Fin (n+2)`. -/
def embedTwo (n : ℕ) : Fin 2 → Fin (n + 2) :=
  fun p => Fin.cases 0 (fun _ => 1) p

@[simp] theorem embedTwo_zero (n : ℕ) : embedTwo n 0 = 0 := rfl

@[simp] theorem embedTwo_one (n : ℕ) : embedTwo n 1 = 1 := rfl

/-- The leading 2×2 pivot block of `A : Fin (n+2) → Fin (n+2) → ℝ`. -/
def leadingTwoBlock (n : ℕ) (A : Fin (n + 2) → Fin (n + 2) → ℝ) :
    Fin 2 → Fin 2 → ℝ :=
  fun p q => A (embedTwo n p) (embedTwo n q)

@[simp] theorem leadingTwoBlock_apply (n : ℕ)
    (A : Fin (n + 2) → Fin (n + 2) → ℝ) (p q : Fin 2) :
    leadingTwoBlock n A p q = A (embedTwo n p) (embedTwo n q) := rfl

/-! ## Task 2 — rounded 2×2 multipliers, Schur complement, and named factors

For a leading 2×2 pivot of `A : Fin (m+2) → Fin (m+2) → ℝ` we use the two
leading indices `0` and `Fin.succ 0`, and the trailing index `i : Fin m` maps to
`i.succ.succ`.  The pivot block is `E = [[A00,A01],[A10,A11]]` with
`det = A00·A11 − A01·A10`; its inverse is `E⁻¹ = det⁻¹·[[A11,−A01],[−A10,A00]]`.
The multiplier row is the rounded product `w_i = c_i·E⁻¹`, and the rounded Schur
complement is `Ŝ_{ij} = fl(A_{i+2,j+2} − fl(w_{i0}·c_{j0} + w_{i1}·c_{j1}))`. -/

/-- The two-leading-index alias used everywhere below: `oneIdx m = Fin.succ 0`. -/
abbrev oneIdx (m : ℕ) : Fin (m + 2) := Fin.succ 0

@[simp] theorem embedTwo_one_eq (m : ℕ) : embedTwo m 1 = oneIdx m := rfl

/-- Determinant of the leading 2×2 pivot block. -/
noncomputable def mixedDet2 (m : ℕ) (A : Fin (m + 2) → Fin (m + 2) → ℝ) : ℝ :=
  A 0 0 * A (oneIdx m) (oneIdx m) - A 0 (oneIdx m) * A (oneIdx m) 0

/-- Rounded multiplier row `w_i = c_i · E⁻¹` (a length-2 vector) for the trailing
    row `i` of a 2×2-pivot stage.  Column `0` and column `1` of the 2×2 inverse
    are used; each entry is a rounded length-two inner product. -/
noncomputable def flMixedMult2 (m : ℕ) (fp : FPModel)
    (A : Fin (m + 2) → Fin (m + 2) → ℝ) : Fin m → Fin 2 → ℝ :=
  fun i p =>
    let d := mixedDet2 m A
    let e00 := A 0 0; let e01 := A 0 (oneIdx m)
    let e10 := A (oneIdx m) 0; let e11 := A (oneIdx m) (oneIdx m)
    let ci0 := A i.succ.succ 0; let ci1 := A i.succ.succ (oneIdx m)
    Fin.cases
      (fp.fl_add (fp.fl_mul ci0 (e11 / d)) (fp.fl_mul ci1 (-e10 / d)))
      (fun _ => fp.fl_add (fp.fl_mul ci0 (-e01 / d)) (fp.fl_mul ci1 (e00 / d)))
      p

/-- Rounded 2×2-pivot Schur complement
    `Ŝ_{ij} = fl(A_{i+2,j+2} − fl(w_{i0}·c_{j0} + w_{i1}·c_{j1}))`. -/
noncomputable def flSchurCompl2 (m : ℕ) (fp : FPModel)
    (A : Fin (m + 2) → Fin (m + 2) → ℝ) : Fin m → Fin m → ℝ :=
  fun i j =>
    fp.fl_sub (A i.succ.succ j.succ.succ)
      (fp.fl_add
        (fp.fl_mul (flMixedMult2 m fp A i 0) (A j.succ.succ 0))
        (fp.fl_mul (flMixedMult2 m fp A i 1) (A j.succ.succ (oneIdx m))))

/-- Named lower-triangular computed factor `L̂` for the rounded mixed-pivot path,
    by structural recursion on the pivot schedule. -/
noncomputable def flMixedL (fp : FPModel) :
    {n : ℕ} → PivotSchedule n → (Fin n → Fin n → ℝ) → Fin n → Fin n → ℝ
  | 0, .nil, _ => fun I _ => Fin.elim0 I
  | _ + 1, .consOne s, A => fun I J =>
      Fin.cases (Fin.cases 1 (fun _ => 0) J)
        (fun i => Fin.cases (fp.fl_div (A i.succ 0) (A 0 0))
          (fun j => flMixedL fp s (flSchurCompl _ fp A) i j) J) I
  | _ + 2, .consTwo s, A => fun I J =>
      Fin.cases
        (Fin.cases 1 (fun l => Fin.cases 0 (fun _ => 0) l) J)
        (fun k => Fin.cases
          (Fin.cases 0 (fun l => Fin.cases 1 (fun _ => 0) l) J)
          (fun i => Fin.cases (flMixedMult2 _ fp A i 0)
            (fun l => Fin.cases (flMixedMult2 _ fp A i 1)
              (fun j => flMixedL fp s (flSchurCompl2 _ fp A) i j) l) J)
          k) I

/-- Named block-diagonal computed factor `D̂` for the rounded mixed-pivot path. -/
noncomputable def flMixedD (fp : FPModel) :
    {n : ℕ} → PivotSchedule n → (Fin n → Fin n → ℝ) → Fin n → Fin n → ℝ
  | 0, .nil, _ => fun I _ => Fin.elim0 I
  | _ + 1, .consOne s, A => fun I J =>
      Fin.cases (Fin.cases (A 0 0) (fun _ => 0) J)
        (fun i => Fin.cases 0 (fun j => flMixedD fp s (flSchurCompl _ fp A) i j) J) I
  | _ + 2, .consTwo s, A => fun I J =>
      Fin.cases
        (Fin.cases (A 0 0) (fun l => Fin.cases (A 0 (oneIdx _)) (fun _ => 0) l) J)
        (fun k => Fin.cases
          (Fin.cases (A (oneIdx _) 0)
            (fun l => Fin.cases (A (oneIdx _) (oneIdx _)) (fun _ => 0) l) J)
          (fun i => Fin.cases 0
            (fun l => Fin.cases 0
              (fun j => flMixedD fp s (flSchurCompl2 _ fp A) i j) l) J)
          k) I

/-! ### Structural simp lemmas for the named factors -/

section ConsOneSimp
variable (fp : FPModel) {n : ℕ} (s : PivotSchedule n) (A : Fin (n + 1) → Fin (n + 1) → ℝ)

@[simp] theorem flMixedL_consOne_00 : flMixedL fp (s.consOne) A 0 0 = 1 := by
  simp [flMixedL]
@[simp] theorem flMixedL_consOne_0s (j : Fin n) : flMixedL fp (s.consOne) A 0 j.succ = 0 := by
  simp [flMixedL]
@[simp] theorem flMixedL_consOne_s0 (i : Fin n) :
    flMixedL fp (s.consOne) A i.succ 0 = fp.fl_div (A i.succ 0) (A 0 0) := by simp [flMixedL]
@[simp] theorem flMixedL_consOne_ss (i j : Fin n) :
    flMixedL fp (s.consOne) A i.succ j.succ = flMixedL fp s (flSchurCompl n fp A) i j := by
  simp [flMixedL]

@[simp] theorem flMixedD_consOne_00 : flMixedD fp (s.consOne) A 0 0 = A 0 0 := by simp [flMixedD]
@[simp] theorem flMixedD_consOne_0s (j : Fin n) : flMixedD fp (s.consOne) A 0 j.succ = 0 := by
  simp [flMixedD]
@[simp] theorem flMixedD_consOne_s0 (i : Fin n) : flMixedD fp (s.consOne) A i.succ 0 = 0 := by
  simp [flMixedD]
@[simp] theorem flMixedD_consOne_ss (i j : Fin n) :
    flMixedD fp (s.consOne) A i.succ j.succ = flMixedD fp s (flSchurCompl n fp A) i j := by
  simp [flMixedD]
end ConsOneSimp

section ConsTwoSimp
variable (fp : FPModel) {m : ℕ} (s : PivotSchedule m) (A : Fin (m + 2) → Fin (m + 2) → ℝ)

@[simp] theorem flMixedL_consTwo_00 : flMixedL fp (s.consTwo) A 0 0 = 1 := by
  simp only [flMixedL, Fin.cases_zero]
@[simp] theorem flMixedL_consTwo_01 : flMixedL fp (s.consTwo) A 0 (Fin.succ 0) = 0 := by
  simp only [flMixedL, Fin.cases_zero, Fin.cases_succ]
@[simp] theorem flMixedL_consTwo_0t (j : Fin m) : flMixedL fp (s.consTwo) A 0 j.succ.succ = 0 := by
  simp only [flMixedL, Fin.cases_zero, Fin.cases_succ]
@[simp] theorem flMixedL_consTwo_10 : flMixedL fp (s.consTwo) A (Fin.succ 0) 0 = 0 := by
  simp only [flMixedL, Fin.cases_zero, Fin.cases_succ]
@[simp] theorem flMixedL_consTwo_11 : flMixedL fp (s.consTwo) A (Fin.succ 0) (Fin.succ 0) = 1 := by
  simp only [flMixedL, Fin.cases_zero, Fin.cases_succ]
@[simp] theorem flMixedL_consTwo_1t (j : Fin m) :
    flMixedL fp (s.consTwo) A (Fin.succ 0) j.succ.succ = 0 := by
  simp only [flMixedL, Fin.cases_zero, Fin.cases_succ]
@[simp] theorem flMixedL_consTwo_t0 (i : Fin m) :
    flMixedL fp (s.consTwo) A i.succ.succ 0 = flMixedMult2 m fp A i 0 := by
  simp only [flMixedL, Fin.cases_zero, Fin.cases_succ]
@[simp] theorem flMixedL_consTwo_t1 (i : Fin m) :
    flMixedL fp (s.consTwo) A i.succ.succ (Fin.succ 0) = flMixedMult2 m fp A i 1 := by
  simp only [flMixedL, Fin.cases_zero, Fin.cases_succ]
@[simp] theorem flMixedL_consTwo_tt (i j : Fin m) :
    flMixedL fp (s.consTwo) A i.succ.succ j.succ.succ
      = flMixedL fp s (flSchurCompl2 m fp A) i j := by
  simp only [flMixedL, Fin.cases_succ]

@[simp] theorem flMixedD_consTwo_00 : flMixedD fp (s.consTwo) A 0 0 = A 0 0 := by
  simp only [flMixedD, Fin.cases_zero]
@[simp] theorem flMixedD_consTwo_01 :
    flMixedD fp (s.consTwo) A 0 (Fin.succ 0) = A 0 (oneIdx m) := by
  simp only [flMixedD, Fin.cases_zero, Fin.cases_succ]
@[simp] theorem flMixedD_consTwo_0t (j : Fin m) : flMixedD fp (s.consTwo) A 0 j.succ.succ = 0 := by
  simp only [flMixedD, Fin.cases_zero, Fin.cases_succ]
@[simp] theorem flMixedD_consTwo_10 :
    flMixedD fp (s.consTwo) A (Fin.succ 0) 0 = A (oneIdx m) 0 := by
  simp only [flMixedD, Fin.cases_zero, Fin.cases_succ]
@[simp] theorem flMixedD_consTwo_11 :
    flMixedD fp (s.consTwo) A (Fin.succ 0) (Fin.succ 0) = A (oneIdx m) (oneIdx m) := by
  simp only [flMixedD, Fin.cases_zero, Fin.cases_succ]
@[simp] theorem flMixedD_consTwo_1t (j : Fin m) :
    flMixedD fp (s.consTwo) A (Fin.succ 0) j.succ.succ = 0 := by
  simp only [flMixedD, Fin.cases_zero, Fin.cases_succ]
@[simp] theorem flMixedD_consTwo_t0 (i : Fin m) : flMixedD fp (s.consTwo) A i.succ.succ 0 = 0 := by
  simp only [flMixedD, Fin.cases_zero, Fin.cases_succ]
@[simp] theorem flMixedD_consTwo_t1 (i : Fin m) :
    flMixedD fp (s.consTwo) A i.succ.succ (Fin.succ 0) = 0 := by
  simp only [flMixedD, Fin.cases_zero, Fin.cases_succ]
@[simp] theorem flMixedD_consTwo_tt (i j : Fin m) :
    flMixedD fp (s.consTwo) A i.succ.succ j.succ.succ
      = flMixedD fp s (flSchurCompl2 m fp A) i j := by
  simp only [flMixedD, Fin.cases_succ]
end ConsTwoSimp

/-! ## Task 3 — reduction of the size-`(m+2)` product sum

These are the pure linear-algebra facts (no floating-point analysis) that split
the full `L̂D̂L̂ᵀ` entry into the leading 2×2 pivot-path contribution and the
recursive Schur-complement contribution.  They are the 2×2 analogue of the
`hreduce`/`row0` reductions used in `fl_blockLDLT_trailing_bound`. -/

/-- Split a sum over `Fin (m+2)` into its two leading terms and the trailing
    sum, reindexed by `Fin m`. -/
theorem sum_fin_add_two {M : Type*} [AddCommMonoid M] (m : ℕ) (g : Fin (m + 2) → M) :
    (∑ k, g k) = g 0 + g (Fin.succ 0) + ∑ k : Fin m, g k.succ.succ := by
  rw [Fin.sum_univ_succ, Fin.sum_univ_succ, ← add_assoc]

/-- The leading 2×2 pivot-path contribution to the `(i,j)` trailing entry of
    `L̂D̂L̂ᵀ`: `∑_{p,q<2} w_{ip}·E_{pq}·w_{jq}`. -/
noncomputable def pivotPath2 (m : ℕ) (fp : FPModel)
    (A : Fin (m + 2) → Fin (m + 2) → ℝ) (i j : Fin m) : ℝ :=
  ∑ p : Fin 2, ∑ q : Fin 2,
    flMixedMult2 m fp A i p * leadingTwoBlock m A p q * flMixedMult2 m fp A j q

/-- **Trailing reduction.**  The `(i+2, j+2)` entry of the named product splits
    as the leading 2×2 pivot-path term plus the Schur-complement product. -/
theorem product_consTwo_trailing (fp : FPModel) {m : ℕ}
    (s : PivotSchedule m) (A : Fin (m + 2) → Fin (m + 2) → ℝ) (i j : Fin m) :
    (∑ k₁, ∑ k₂, flMixedL fp (s.consTwo) A i.succ.succ k₁
        * flMixedD fp (s.consTwo) A k₁ k₂ * flMixedL fp (s.consTwo) A j.succ.succ k₂)
      = pivotPath2 m fp A i j
        + (∑ a, ∑ b, flMixedL fp s (flSchurCompl2 m fp A) i a
            * flMixedD fp s (flSchurCompl2 m fp A) a b * flMixedL fp s (flSchurCompl2 m fp A) j b) := by
  simp only [sum_fin_add_two]
  simp only [flMixedD_consTwo_t0, flMixedD_consTwo_t1, flMixedD_consTwo_tt,
    flMixedD_consTwo_00, flMixedD_consTwo_01, flMixedD_consTwo_10, flMixedD_consTwo_11,
    flMixedD_consTwo_0t, flMixedD_consTwo_1t,
    flMixedL_consTwo_t0, flMixedL_consTwo_t1, flMixedL_consTwo_tt,
    zero_mul, mul_zero, add_zero, zero_add, Finset.sum_const_zero]
  rw [pivotPath2, Fin.sum_univ_two, Fin.sum_univ_two, Fin.sum_univ_two]
  simp only [leadingTwoBlock_apply, embedTwo_zero, embedTwo_one_eq]

section Reductions
variable (fp : FPModel) {m : ℕ} (s : PivotSchedule m) (A : Fin (m + 2) → Fin (m + 2) → ℝ)

/-- **Pivot-block reduction (exact).**  The four leading entries of the named
    product reproduce the 2×2 pivot block `E` exactly. -/
theorem product_consTwo_00 :
    (∑ k₁, ∑ k₂, flMixedL fp (s.consTwo) A 0 k₁ * flMixedD fp (s.consTwo) A k₁ k₂
        * flMixedL fp (s.consTwo) A 0 k₂) = A 0 0 := by
  simp only [sum_fin_add_two, flMixedL_consTwo_00, flMixedL_consTwo_01, flMixedL_consTwo_0t,
    flMixedD_consTwo_00, flMixedD_consTwo_01, flMixedD_consTwo_0t,
    zero_mul, mul_zero, one_mul, mul_one, add_zero, zero_add, Finset.sum_const_zero]

theorem product_consTwo_0one :
    (∑ k₁, ∑ k₂, flMixedL fp (s.consTwo) A 0 k₁ * flMixedD fp (s.consTwo) A k₁ k₂
        * flMixedL fp (s.consTwo) A (Fin.succ 0) k₂) = A 0 (oneIdx m) := by
  simp only [sum_fin_add_two, flMixedL_consTwo_00, flMixedL_consTwo_01, flMixedL_consTwo_0t,
    flMixedL_consTwo_10, flMixedL_consTwo_11, flMixedL_consTwo_1t,
    flMixedD_consTwo_00, flMixedD_consTwo_01, flMixedD_consTwo_0t,
    zero_mul, mul_zero, one_mul, mul_one, add_zero, zero_add, Finset.sum_const_zero]

theorem product_consTwo_one0 :
    (∑ k₁, ∑ k₂, flMixedL fp (s.consTwo) A (Fin.succ 0) k₁ * flMixedD fp (s.consTwo) A k₁ k₂
        * flMixedL fp (s.consTwo) A 0 k₂) = A (oneIdx m) 0 := by
  simp only [sum_fin_add_two, flMixedL_consTwo_00, flMixedL_consTwo_01, flMixedL_consTwo_0t,
    flMixedL_consTwo_10, flMixedL_consTwo_11, flMixedL_consTwo_1t,
    flMixedD_consTwo_10, flMixedD_consTwo_11, flMixedD_consTwo_1t,
    zero_mul, mul_zero, one_mul, mul_one, add_zero, zero_add, Finset.sum_const_zero]

theorem product_consTwo_oneone :
    (∑ k₁, ∑ k₂, flMixedL fp (s.consTwo) A (Fin.succ 0) k₁ * flMixedD fp (s.consTwo) A k₁ k₂
        * flMixedL fp (s.consTwo) A (Fin.succ 0) k₂) = A (oneIdx m) (oneIdx m) := by
  simp only [sum_fin_add_two, flMixedL_consTwo_10, flMixedL_consTwo_11, flMixedL_consTwo_1t,
    flMixedD_consTwo_10, flMixedD_consTwo_11, flMixedD_consTwo_1t,
    zero_mul, mul_zero, one_mul, mul_one, add_zero, zero_add, Finset.sum_const_zero]

/-- **Pivot-row reductions.**  `(L̂D̂L̂ᵀ)_{p, j+2} = (E·w_jᵀ)_p`. -/
theorem product_consTwo_0t (j : Fin m) :
    (∑ k₁, ∑ k₂, flMixedL fp (s.consTwo) A 0 k₁ * flMixedD fp (s.consTwo) A k₁ k₂
        * flMixedL fp (s.consTwo) A j.succ.succ k₂)
      = A 0 0 * flMixedMult2 m fp A j 0 + A 0 (oneIdx m) * flMixedMult2 m fp A j 1 := by
  simp only [sum_fin_add_two, flMixedL_consTwo_00, flMixedL_consTwo_01, flMixedL_consTwo_0t,
    flMixedL_consTwo_t0, flMixedL_consTwo_t1, flMixedL_consTwo_tt,
    flMixedD_consTwo_00, flMixedD_consTwo_01, flMixedD_consTwo_0t,
    zero_mul, mul_zero, one_mul, mul_one, add_zero, zero_add, Finset.sum_const_zero]

theorem product_consTwo_1t (j : Fin m) :
    (∑ k₁, ∑ k₂, flMixedL fp (s.consTwo) A (Fin.succ 0) k₁ * flMixedD fp (s.consTwo) A k₁ k₂
        * flMixedL fp (s.consTwo) A j.succ.succ k₂)
      = A (oneIdx m) 0 * flMixedMult2 m fp A j 0
        + A (oneIdx m) (oneIdx m) * flMixedMult2 m fp A j 1 := by
  simp only [sum_fin_add_two, flMixedL_consTwo_10, flMixedL_consTwo_11, flMixedL_consTwo_1t,
    flMixedL_consTwo_t0, flMixedL_consTwo_t1, flMixedL_consTwo_tt,
    flMixedD_consTwo_10, flMixedD_consTwo_11, flMixedD_consTwo_1t,
    zero_mul, mul_zero, one_mul, mul_one, add_zero, zero_add, Finset.sum_const_zero]

/-- **Pivot-column reductions.**  `(L̂D̂L̂ᵀ)_{i+2, q} = (w_i·E)_q`. -/
theorem product_consTwo_t0 (i : Fin m) :
    (∑ k₁, ∑ k₂, flMixedL fp (s.consTwo) A i.succ.succ k₁ * flMixedD fp (s.consTwo) A k₁ k₂
        * flMixedL fp (s.consTwo) A 0 k₂)
      = flMixedMult2 m fp A i 0 * A 0 0 + flMixedMult2 m fp A i 1 * A (oneIdx m) 0 := by
  simp only [sum_fin_add_two, flMixedL_consTwo_00, flMixedL_consTwo_01, flMixedL_consTwo_0t,
    flMixedL_consTwo_t0, flMixedL_consTwo_t1, flMixedL_consTwo_tt,
    flMixedD_consTwo_00, flMixedD_consTwo_10, flMixedD_consTwo_t0,
    flMixedD_consTwo_01, flMixedD_consTwo_11, flMixedD_consTwo_t1,
    flMixedD_consTwo_0t, flMixedD_consTwo_1t, flMixedD_consTwo_tt,
    zero_mul, mul_zero, one_mul, mul_one, add_zero, zero_add, Finset.sum_const_zero]

theorem product_consTwo_t1 (i : Fin m) :
    (∑ k₁, ∑ k₂, flMixedL fp (s.consTwo) A i.succ.succ k₁ * flMixedD fp (s.consTwo) A k₁ k₂
        * flMixedL fp (s.consTwo) A (Fin.succ 0) k₂)
      = flMixedMult2 m fp A i 0 * A 0 (oneIdx m)
        + flMixedMult2 m fp A i 1 * A (oneIdx m) (oneIdx m) := by
  simp only [sum_fin_add_two, flMixedL_consTwo_10, flMixedL_consTwo_11, flMixedL_consTwo_1t,
    flMixedL_consTwo_t0, flMixedL_consTwo_t1, flMixedL_consTwo_tt,
    flMixedD_consTwo_00, flMixedD_consTwo_10, flMixedD_consTwo_t0,
    flMixedD_consTwo_01, flMixedD_consTwo_11, flMixedD_consTwo_t1,
    flMixedD_consTwo_0t, flMixedD_consTwo_1t, flMixedD_consTwo_tt,
    zero_mul, mul_zero, one_mul, mul_one, add_zero, zero_add, Finset.sum_const_zero]

end Reductions

/-! ## Task 4 — abs pivot-path helpers and the 2×2 stage envelope -/

/-- The `(i,j)` entry of the leading 2×2 abs pivot-path product
    `∑_{p,q<2} |w_{ip}|·|E_{pq}|·|w_{jq}|`.  This is exactly the leading
    contribution to the `|L̂||D̂||L̂ᵀ|` trailing entry (see the split lemma). -/
noncomputable def pivotPath2Abs (m : ℕ) (fp : FPModel)
    (A : Fin (m + 2) → Fin (m + 2) → ℝ) (i j : Fin m) : ℝ :=
  ∑ p : Fin 2, ∑ q : Fin 2,
    |flMixedMult2 m fp A i p| * |leadingTwoBlock m A p q| * |flMixedMult2 m fp A j q|

/-- The abs pivot-row path `∑_{q<2} |E_{pq}|·|w_{jq}|`, equal to the `(embed p, j+2)`
    entry of `|L̂||D̂||L̂ᵀ|`. -/
noncomputable def pivotRowPathAbs (m : ℕ) (fp : FPModel)
    (A : Fin (m + 2) → Fin (m + 2) → ℝ) (p : Fin 2) (j : Fin m) : ℝ :=
  ∑ q : Fin 2, |leadingTwoBlock m A p q| * |flMixedMult2 m fp A j q|

/-- The abs pivot-column path `∑_{p<2} |w_{ip}|·|E_{pq}|`, equal to the
    `(i+2, embed q)` entry of `|L̂||D̂||L̂ᵀ|`. -/
noncomputable def pivotColPathAbs (m : ℕ) (fp : FPModel)
    (A : Fin (m + 2) → Fin (m + 2) → ℝ) (i : Fin m) (q : Fin 2) : ℝ :=
  ∑ p : Fin 2, |flMixedMult2 m fp A i p| * |leadingTwoBlock m A p q|

/-- Entrywise one-stage backward-error envelope for a rounded 2×2-pivot block-LDLᵀ
    assemble step.  Pivot block entries have exact error `0`; pivot row/column
    entries have the 2×2-solve error `cSolve·u·(pivot-path)` (eq. (11.5)); trailing
    entries have the per-stage 2×2 Schur error `cStage·γ₃·(|A|+pivot-path)` plus the
    recursive trailing envelope `Bs`. -/
noncomputable def flBlockLDLTTwoByTwoStageBound (m : ℕ) (fp : FPModel)
    (A : Fin (m + 2) → Fin (m + 2) → ℝ) (cSolve cStage : ℝ)
    (Bs : Fin m → Fin m → ℝ) : Fin (m + 2) → Fin (m + 2) → ℝ :=
  fun I J =>
    Fin.cases
      -- I = 0 (pivot row 0)
      (Fin.cases 0 (fun l => Fin.cases 0
          (fun j => cSolve * fp.u * pivotRowPathAbs m fp A 0 j) l) J)
      (fun k => Fin.cases
        -- I = Fin.succ 0 (pivot row 1)
        (Fin.cases 0 (fun l => Fin.cases 0
            (fun j => cSolve * fp.u * pivotRowPathAbs m fp A 1 j) l) J)
        -- I = i.succ.succ (pivot column + trailing)
        (fun i => Fin.cases (cSolve * fp.u * pivotColPathAbs m fp A i 0)
          (fun l => Fin.cases (cSolve * fp.u * pivotColPathAbs m fp A i 1)
            (fun j => cStage * gamma fp 3
                * (|A i.succ.succ j.succ.succ| + pivotPath2Abs m fp A i j) + Bs i j) l) J)
        k) I

/-! ## Task 7 — recursive envelope and the mixed-pivot side condition -/

/-- Recursive entrywise backward-error envelope for the rounded mixed-pivot
    block-LDLᵀ path, threaded along the pivot schedule.  Each 1×1 stage uses the
    verified `flBlockLDLTOneByOneStageBound`; each 2×2 stage uses
    `flBlockLDLTTwoByTwoStageBound`. -/
noncomputable def flBlockLDLTMixedBound (fp : FPModel) (cSolve cStage : ℝ) :
    {n : ℕ} → PivotSchedule n → (Fin n → Fin n → ℝ) → Fin n → Fin n → ℝ
  | 0, .nil, _ => fun I _ => Fin.elim0 I
  | _ + 1, .consOne s, A =>
      flBlockLDLTOneByOneStageBound _ fp A
        (flBlockLDLTMixedBound fp cSolve cStage s (flSchurCompl _ fp A))
  | _ + 2, .consTwo s, A =>
      flBlockLDLTTwoByTwoStageBound _ fp A cSolve cStage
        (flBlockLDLTMixedBound fp cSolve cStage s (flSchurCompl2 _ fp A))

/-- The mixed-pivot recursive side condition.  1×1 stages carry the (derived)
    nonzero-pivot and first-row/column symmetry conditions.  2×2 stages carry the
    per-stage backward-error hypotheses:
      * pivot row/column: the (11.5) 2×2-solve bound, constant `cSolve`;
      * trailing block: the assembled 2×2 Schur backward error, constant `cStage`.
    Both are honest source-level per-stage facts (see the module header). -/
noncomputable def FlMixedPivots (fp : FPModel) (cSolve cStage : ℝ) :
    {n : ℕ} → PivotSchedule n → (Fin n → Fin n → ℝ) → Prop
  | 0, .nil, _ => True
  | _ + 1, .consOne s, A =>
      A 0 0 ≠ 0 ∧ (∀ i : Fin _, A 0 i.succ = A i.succ 0) ∧
      FlMixedPivots fp cSolve cStage s (flSchurCompl _ fp A)
  | m + 2, .consTwo s, A =>
      -- pivot-row (11.5) solve bound, embed 0 and embed 1
      (∀ j : Fin m,
        |A 0 0 * flMixedMult2 m fp A j 0 + A 0 (oneIdx m) * flMixedMult2 m fp A j 1
          - A 0 j.succ.succ| ≤ cSolve * fp.u * pivotRowPathAbs m fp A 0 j) ∧
      (∀ j : Fin m,
        |A (oneIdx m) 0 * flMixedMult2 m fp A j 0
            + A (oneIdx m) (oneIdx m) * flMixedMult2 m fp A j 1
          - A (oneIdx m) j.succ.succ| ≤ cSolve * fp.u * pivotRowPathAbs m fp A 1 j) ∧
      -- pivot-column (11.5) solve bound, embed 0 and embed 1
      (∀ i : Fin m,
        |flMixedMult2 m fp A i 0 * A 0 0 + flMixedMult2 m fp A i 1 * A (oneIdx m) 0
          - A i.succ.succ 0| ≤ cSolve * fp.u * pivotColPathAbs m fp A i 0) ∧
      (∀ i : Fin m,
        |flMixedMult2 m fp A i 0 * A 0 (oneIdx m)
            + flMixedMult2 m fp A i 1 * A (oneIdx m) (oneIdx m)
          - A i.succ.succ (oneIdx m)| ≤ cSolve * fp.u * pivotColPathAbs m fp A i 1) ∧
      -- trailing 2×2 Schur backward error (task-5 fact, assumed as a per-stage hypothesis)
      (∀ i j : Fin m,
        |pivotPath2 m fp A i j + flSchurCompl2 m fp A i j - A i.succ.succ j.succ.succ|
          ≤ cStage * gamma fp 3
              * (|A i.succ.succ j.succ.succ| + pivotPath2Abs m fp A i j)) ∧
      -- the (11.5) coupling `c_j ↔ E·w_j`, isolated as an entrywise inequality
      -- (holds with equality for an exact 2×2 solve; the pure-rounding part of the
      -- Schur-magnitude bound is DERIVED from the model in `flSchurCompl2_magnitude`)
      (∀ i j : Fin m,
        |flMixedMult2 m fp A i 0| * |A j.succ.succ 0|
            + |flMixedMult2 m fp A i 1| * |A j.succ.succ (oneIdx m)|
          ≤ pivotPath2Abs m fp A i j) ∧
      FlMixedPivots fp cSolve cStage s (flSchurCompl2 m fp A)

/-! ### Simp lemmas for the 2×2 stage envelope and the recursive envelope -/

section StageSimp
variable (m : ℕ) (fp : FPModel) (A : Fin (m + 2) → Fin (m + 2) → ℝ) (cSolve cStage : ℝ)
  (Bs : Fin m → Fin m → ℝ)

@[simp] theorem SB2_00 : flBlockLDLTTwoByTwoStageBound m fp A cSolve cStage Bs 0 0 = 0 := by
  simp only [flBlockLDLTTwoByTwoStageBound, Fin.cases_zero]
@[simp] theorem SB2_01 :
    flBlockLDLTTwoByTwoStageBound m fp A cSolve cStage Bs 0 (Fin.succ 0) = 0 := by
  simp only [flBlockLDLTTwoByTwoStageBound, Fin.cases_zero, Fin.cases_succ]
@[simp] theorem SB2_0t (j : Fin m) :
    flBlockLDLTTwoByTwoStageBound m fp A cSolve cStage Bs 0 j.succ.succ
      = cSolve * fp.u * pivotRowPathAbs m fp A 0 j := by
  simp only [flBlockLDLTTwoByTwoStageBound, Fin.cases_zero, Fin.cases_succ]
@[simp] theorem SB2_10 :
    flBlockLDLTTwoByTwoStageBound m fp A cSolve cStage Bs (Fin.succ 0) 0 = 0 := by
  simp only [flBlockLDLTTwoByTwoStageBound, Fin.cases_zero, Fin.cases_succ]
@[simp] theorem SB2_11 :
    flBlockLDLTTwoByTwoStageBound m fp A cSolve cStage Bs (Fin.succ 0) (Fin.succ 0) = 0 := by
  simp only [flBlockLDLTTwoByTwoStageBound, Fin.cases_zero, Fin.cases_succ]
@[simp] theorem SB2_1t (j : Fin m) :
    flBlockLDLTTwoByTwoStageBound m fp A cSolve cStage Bs (Fin.succ 0) j.succ.succ
      = cSolve * fp.u * pivotRowPathAbs m fp A 1 j := by
  simp only [flBlockLDLTTwoByTwoStageBound, Fin.cases_zero, Fin.cases_succ]
@[simp] theorem SB2_t0 (i : Fin m) :
    flBlockLDLTTwoByTwoStageBound m fp A cSolve cStage Bs i.succ.succ 0
      = cSolve * fp.u * pivotColPathAbs m fp A i 0 := by
  simp only [flBlockLDLTTwoByTwoStageBound, Fin.cases_zero, Fin.cases_succ]
@[simp] theorem SB2_t1 (i : Fin m) :
    flBlockLDLTTwoByTwoStageBound m fp A cSolve cStage Bs i.succ.succ (Fin.succ 0)
      = cSolve * fp.u * pivotColPathAbs m fp A i 1 := by
  simp only [flBlockLDLTTwoByTwoStageBound, Fin.cases_zero, Fin.cases_succ]
@[simp] theorem SB2_tt (i j : Fin m) :
    flBlockLDLTTwoByTwoStageBound m fp A cSolve cStage Bs i.succ.succ j.succ.succ
      = cStage * gamma fp 3 * (|A i.succ.succ j.succ.succ| + pivotPath2Abs m fp A i j) + Bs i j := by
  simp only [flBlockLDLTTwoByTwoStageBound, Fin.cases_zero, Fin.cases_succ]
end StageSimp

@[simp] theorem flBlockLDLTMixedBound_consOne (fp : FPModel) (cSolve cStage : ℝ) {n : ℕ}
    (s : PivotSchedule n) (A : Fin (n + 1) → Fin (n + 1) → ℝ) :
    flBlockLDLTMixedBound fp cSolve cStage (s.consOne) A
      = flBlockLDLTOneByOneStageBound n fp A
          (flBlockLDLTMixedBound fp cSolve cStage s (flSchurCompl n fp A)) := rfl

@[simp] theorem flBlockLDLTMixedBound_consTwo (fp : FPModel) (cSolve cStage : ℝ) {m : ℕ}
    (s : PivotSchedule m) (A : Fin (m + 2) → Fin (m + 2) → ℝ) :
    flBlockLDLTMixedBound fp cSolve cStage (s.consTwo) A
      = flBlockLDLTTwoByTwoStageBound m fp A cSolve cStage
          (flBlockLDLTMixedBound fp cSolve cStage s (flSchurCompl2 m fp A)) := rfl

/-! ## Task 6 — the one-stage 2×2 block-LDLᵀ backward-error bound

Given the recursion hypothesis `hIH` (the recursive factors approximate the 2×2
rounded Schur complement within `Bs`) and the per-2×2-stage backward-error
hypotheses `hrow*/hcol*/htrail` (eq. (11.5) plus the assembled trailing error),
the full size-`(m+2)` named product is bounded entrywise by the 2×2 stage
envelope.  All four index classes are handled via the reduction lemmas of
Task 3. -/
theorem fl_blockLDLT_twoByTwo_stage_bound (fp : FPModel) {m : ℕ}
    (s : PivotSchedule m) (A : Fin (m + 2) → Fin (m + 2) → ℝ) (cSolve cStage : ℝ)
    (Bs : Fin m → Fin m → ℝ)
    (hIH : ∀ i j : Fin m,
      |(∑ a, ∑ b, flMixedL fp s (flSchurCompl2 m fp A) i a
          * flMixedD fp s (flSchurCompl2 m fp A) a b * flMixedL fp s (flSchurCompl2 m fp A) j b)
        - flSchurCompl2 m fp A i j| ≤ Bs i j)
    (hrow0 : ∀ j : Fin m,
      |A 0 0 * flMixedMult2 m fp A j 0 + A 0 (oneIdx m) * flMixedMult2 m fp A j 1
        - A 0 j.succ.succ| ≤ cSolve * fp.u * pivotRowPathAbs m fp A 0 j)
    (hrow1 : ∀ j : Fin m,
      |A (oneIdx m) 0 * flMixedMult2 m fp A j 0
          + A (oneIdx m) (oneIdx m) * flMixedMult2 m fp A j 1
        - A (oneIdx m) j.succ.succ| ≤ cSolve * fp.u * pivotRowPathAbs m fp A 1 j)
    (hcol0 : ∀ i : Fin m,
      |flMixedMult2 m fp A i 0 * A 0 0 + flMixedMult2 m fp A i 1 * A (oneIdx m) 0
        - A i.succ.succ 0| ≤ cSolve * fp.u * pivotColPathAbs m fp A i 0)
    (hcol1 : ∀ i : Fin m,
      |flMixedMult2 m fp A i 0 * A 0 (oneIdx m)
          + flMixedMult2 m fp A i 1 * A (oneIdx m) (oneIdx m)
        - A i.succ.succ (oneIdx m)| ≤ cSolve * fp.u * pivotColPathAbs m fp A i 1)
    (htrail : ∀ i j : Fin m,
      |pivotPath2 m fp A i j + flSchurCompl2 m fp A i j - A i.succ.succ j.succ.succ|
        ≤ cStage * gamma fp 3 * (|A i.succ.succ j.succ.succ| + pivotPath2Abs m fp A i j)) :
    ∀ I J : Fin (m + 2),
      |(∑ k₁, ∑ k₂, flMixedL fp (s.consTwo) A I k₁ * flMixedD fp (s.consTwo) A k₁ k₂
          * flMixedL fp (s.consTwo) A J k₂) - A I J|
        ≤ flBlockLDLTTwoByTwoStageBound m fp A cSolve cStage Bs I J := by
  intro I J
  rcases Fin.eq_zero_or_eq_succ I with rfl | ⟨I', rfl⟩
  · rcases Fin.eq_zero_or_eq_succ J with rfl | ⟨J', rfl⟩
    · -- (0,0)
      rw [product_consTwo_00]; simp
    · rcases Fin.eq_zero_or_eq_succ J' with rfl | ⟨j, rfl⟩
      · -- (0, succ 0)
        rw [product_consTwo_0one, SB2_01]
        rw [show A 0 (oneIdx m) = A 0 (Fin.succ 0) from rfl, sub_self, abs_zero]
      · -- (0, j+2): pivot row 0
        rw [product_consTwo_0t, SB2_0t]; exact hrow0 j
  · rcases Fin.eq_zero_or_eq_succ I' with rfl | ⟨i, rfl⟩
    · rcases Fin.eq_zero_or_eq_succ J with rfl | ⟨J', rfl⟩
      · -- (succ 0, 0)
        rw [product_consTwo_one0, SB2_10]
        rw [show A (oneIdx m) 0 = A (Fin.succ 0) 0 from rfl, sub_self, abs_zero]
      · rcases Fin.eq_zero_or_eq_succ J' with rfl | ⟨j, rfl⟩
        · -- (succ 0, succ 0)
          rw [product_consTwo_oneone, SB2_11]
          rw [show A (oneIdx m) (oneIdx m) = A (Fin.succ 0) (Fin.succ 0) from rfl,
            sub_self, abs_zero]
        · -- (succ 0, j+2): pivot row 1
          rw [product_consTwo_1t, SB2_1t]; exact hrow1 j
    · rcases Fin.eq_zero_or_eq_succ J with rfl | ⟨J', rfl⟩
      · -- (i+2, 0): pivot column 0
        rw [product_consTwo_t0, SB2_t0]; exact hcol0 i
      · rcases Fin.eq_zero_or_eq_succ J' with rfl | ⟨j, rfl⟩
        · -- (i+2, succ 0): pivot column 1
          rw [product_consTwo_t1, SB2_t1]; exact hcol1 i
        · -- (i+2, j+2): trailing block
          rw [product_consTwo_trailing, SB2_tt]
          set Ŝ := flSchurCompl2 m fp A i j with hŜ
          set PS := (∑ a, ∑ b, flMixedL fp s (flSchurCompl2 m fp A) i a
              * flMixedD fp s (flSchurCompl2 m fp A) a b * flMixedL fp s (flSchurCompl2 m fp A) j b)
            with hPS
          have hsplit : pivotPath2 m fp A i j + PS - A i.succ.succ j.succ.succ
              = (pivotPath2 m fp A i j + Ŝ - A i.succ.succ j.succ.succ) + (PS - Ŝ) := by ring
          rw [hsplit]
          calc |(pivotPath2 m fp A i j + Ŝ - A i.succ.succ j.succ.succ) + (PS - Ŝ)|
              ≤ |pivotPath2 m fp A i j + Ŝ - A i.succ.succ j.succ.succ| + |PS - Ŝ| := abs_add_le _ _
            _ ≤ cStage * gamma fp 3 * (|A i.succ.succ j.succ.succ| + pivotPath2Abs m fp A i j)
                  + Bs i j := add_le_add (htrail i j) (hIH i j)

/-! ## Task 8 — the recursive mixed-pivot factorization bound

Structural induction on the pivot schedule.  Each 1×1 stage reuses the verified
`fl_blockLDLT_oneByOne_stage_bound`; each 2×2 stage uses the Task 6 stage bound
with the per-stage hypotheses supplied by `FlMixedPivots`. -/
theorem fl_blockLDLT_mixed_bound (fp : FPModel) (hval : gammaValid fp 3)
    (cSolve cStage : ℝ) :
    ∀ {n : ℕ} (s : PivotSchedule n) (A : Fin n → Fin n → ℝ),
      FlMixedPivots fp cSolve cStage s A →
      ∀ I J : Fin n,
        |(∑ k₁, ∑ k₂, flMixedL fp s A I k₁ * flMixedD fp s A k₁ k₂ * flMixedL fp s A J k₂)
            - A I J|
          ≤ flBlockLDLTMixedBound fp cSolve cStage s A I J := by
  intro n s
  induction s with
  | nil => intro A _ I; exact Fin.elim0 I
  | consOne s ih =>
      intro A hp
      obtain ⟨ha, hsym1, hpS⟩ := hp
      have hIHs := ih (flSchurCompl _ fp A) hpS
      simp only [flBlockLDLTMixedBound_consOne]
      apply fl_blockLDLT_oneByOne_stage_bound _ fp A ha hsym1 hval
        (flMixedL fp s (flSchurCompl _ fp A)) (flMixedD fp s (flSchurCompl _ fp A))
        (flBlockLDLTMixedBound fp cSolve cStage s (flSchurCompl _ fp A))
      · intro i j; simpa [flSchurCompl] using hIHs i j
      · simp
      · intro i; simp
      · intro j; simp
      · intro i j; simp
      · simp
      · intro j; simp
      · intro i; simp
      · intro i j; simp
  | consTwo s ih =>
      intro A hp
      obtain ⟨hr0, hr1, hc0, hc1, ht, _hbridge, hpS⟩ := hp
      have hIHs := ih (flSchurCompl2 _ fp A) hpS
      simp only [flBlockLDLTMixedBound_consTwo]
      exact fl_blockLDLT_twoByTwo_stage_bound fp s A cSolve cStage
        (flBlockLDLTMixedBound fp cSolve cStage s (flSchurCompl2 _ fp A))
        hIHs hr0 hr1 hc0 hc1 ht

/-! ## Task 9a — productEntry (`|L̂||D̂||L̂ᵀ|`) split lemmas

These are the abs analogues of the Task-3 reductions: the printed product entry
splits into the leading 2×2 abs pivot-path term and the Schur-complement product
entry.  They let the accounting fold each per-stage budget into the printed
first-order envelope. -/

section PESplit
variable (fp : FPModel) {m : ℕ} (s : PivotSchedule m) (A : Fin (m + 2) → Fin (m + 2) → ℝ)

theorem productEntry_consTwo_trailing (i j : Fin m) :
    higham11_4_bunchKaufmanProductEntry (m + 2) (flMixedL fp (s.consTwo) A)
        (flMixedD fp (s.consTwo) A) i.succ.succ j.succ.succ
      = pivotPath2Abs m fp A i j
        + higham11_4_bunchKaufmanProductEntry m (flMixedL fp s (flSchurCompl2 m fp A))
            (flMixedD fp s (flSchurCompl2 m fp A)) i j := by
  unfold higham11_4_bunchKaufmanProductEntry
  simp only [sum_fin_add_two, flMixedD_consTwo_t0, flMixedD_consTwo_t1, flMixedD_consTwo_tt,
    flMixedD_consTwo_00, flMixedD_consTwo_01, flMixedD_consTwo_10, flMixedD_consTwo_11,
    flMixedD_consTwo_0t, flMixedD_consTwo_1t,
    flMixedL_consTwo_t0, flMixedL_consTwo_t1, flMixedL_consTwo_tt,
    abs_zero, zero_mul, mul_zero, add_zero, zero_add, Finset.sum_const_zero]
  rw [pivotPath2Abs, Fin.sum_univ_two, Fin.sum_univ_two, Fin.sum_univ_two]
  simp only [leadingTwoBlock_apply, embedTwo_zero, embedTwo_one_eq]

theorem productEntry_consTwo_0t (j : Fin m) :
    higham11_4_bunchKaufmanProductEntry (m + 2) (flMixedL fp (s.consTwo) A)
        (flMixedD fp (s.consTwo) A) 0 j.succ.succ
      = pivotRowPathAbs m fp A 0 j := by
  unfold higham11_4_bunchKaufmanProductEntry
  simp only [sum_fin_add_two, flMixedL_consTwo_00, flMixedL_consTwo_01, flMixedL_consTwo_0t,
    flMixedL_consTwo_t0, flMixedL_consTwo_t1, flMixedL_consTwo_tt,
    flMixedD_consTwo_00, flMixedD_consTwo_01, flMixedD_consTwo_0t,
    abs_zero, abs_one, zero_mul, mul_zero, one_mul, mul_one, add_zero, zero_add,
    Finset.sum_const_zero]
  rw [pivotRowPathAbs, Fin.sum_univ_two]
  simp only [leadingTwoBlock_apply, embedTwo_zero, embedTwo_one_eq]

theorem productEntry_consTwo_1t (j : Fin m) :
    higham11_4_bunchKaufmanProductEntry (m + 2) (flMixedL fp (s.consTwo) A)
        (flMixedD fp (s.consTwo) A) (Fin.succ 0) j.succ.succ
      = pivotRowPathAbs m fp A 1 j := by
  unfold higham11_4_bunchKaufmanProductEntry
  simp only [sum_fin_add_two, flMixedL_consTwo_10, flMixedL_consTwo_11, flMixedL_consTwo_1t,
    flMixedL_consTwo_t0, flMixedL_consTwo_t1, flMixedL_consTwo_tt,
    flMixedD_consTwo_10, flMixedD_consTwo_11, flMixedD_consTwo_1t,
    abs_zero, abs_one, zero_mul, mul_zero, one_mul, mul_one, add_zero, zero_add,
    Finset.sum_const_zero]
  rw [pivotRowPathAbs, Fin.sum_univ_two]
  simp only [leadingTwoBlock_apply, embedTwo_zero, embedTwo_one_eq]

theorem productEntry_consTwo_t0 (i : Fin m) :
    higham11_4_bunchKaufmanProductEntry (m + 2) (flMixedL fp (s.consTwo) A)
        (flMixedD fp (s.consTwo) A) i.succ.succ 0
      = pivotColPathAbs m fp A i 0 := by
  unfold higham11_4_bunchKaufmanProductEntry
  simp only [sum_fin_add_two, flMixedL_consTwo_00, flMixedL_consTwo_01, flMixedL_consTwo_0t,
    flMixedL_consTwo_t0, flMixedL_consTwo_t1, flMixedL_consTwo_tt,
    flMixedD_consTwo_00, flMixedD_consTwo_10, flMixedD_consTwo_t0,
    flMixedD_consTwo_01, flMixedD_consTwo_11, flMixedD_consTwo_t1,
    flMixedD_consTwo_0t, flMixedD_consTwo_1t, flMixedD_consTwo_tt,
    abs_zero, abs_one, zero_mul, mul_zero, one_mul, mul_one, add_zero, zero_add,
    Finset.sum_const_zero]
  rw [pivotColPathAbs, Fin.sum_univ_two]
  simp only [leadingTwoBlock_apply, embedTwo_zero, embedTwo_one_eq]

theorem productEntry_consTwo_t1 (i : Fin m) :
    higham11_4_bunchKaufmanProductEntry (m + 2) (flMixedL fp (s.consTwo) A)
        (flMixedD fp (s.consTwo) A) i.succ.succ (Fin.succ 0)
      = pivotColPathAbs m fp A i 1 := by
  unfold higham11_4_bunchKaufmanProductEntry
  simp only [sum_fin_add_two, flMixedL_consTwo_10, flMixedL_consTwo_11, flMixedL_consTwo_1t,
    flMixedL_consTwo_t0, flMixedL_consTwo_t1, flMixedL_consTwo_tt,
    flMixedD_consTwo_00, flMixedD_consTwo_10, flMixedD_consTwo_t0,
    flMixedD_consTwo_01, flMixedD_consTwo_11, flMixedD_consTwo_t1,
    flMixedD_consTwo_0t, flMixedD_consTwo_1t, flMixedD_consTwo_tt,
    abs_zero, abs_one, zero_mul, mul_zero, one_mul, mul_one, add_zero, zero_add,
    Finset.sum_const_zero]
  rw [pivotColPathAbs, Fin.sum_univ_two]
  simp only [leadingTwoBlock_apply, embedTwo_zero, embedTwo_one_eq]

end PESplit

/-- **Derived pure-rounding bound on the computed 2×2 Schur entry** (a genuine
    fragment of the "task 5" derivation).  Purely from the floating-point model
    (three rounded operations: two products, an add, a subtract) the computed
    Schur entry satisfies
    `|Ŝ_{ij}| ≤ (1+u)|A_{i+2,j+2}| + (1+u)³·(|w_{i0}||c_{j0}| + |w_{i1}||c_{j1}|)`,
    where `c_j = (A_{j+2,0}, A_{j+2,1})` is the original active data.  No 2×2-solve
    (11.5) hypothesis is used here; only the standard model laws.  The remaining
    step to the printed pivot-path product `pivotPath2Abs = ∑|w||E||w|` is exactly
    the (11.5) coupling `c_j ↔ E·w_j`, isolated as `hbridge` in `FlMixedPivots`. -/
theorem flSchurCompl2_magnitude (fp : FPModel) {m : ℕ}
    (A : Fin (m + 2) → Fin (m + 2) → ℝ) (i j : Fin m) :
    |flSchurCompl2 m fp A i j|
      ≤ (1 + fp.u) * |A i.succ.succ j.succ.succ|
        + (1 + fp.u) ^ 3 * (|flMixedMult2 m fp A i 0| * |A j.succ.succ 0|
            + |flMixedMult2 m fp A i 1| * |A j.succ.succ (oneIdx m)|) := by
  unfold flSchurCompl2
  set b := A i.succ.succ j.succ.succ with hb
  set w0 := flMixedMult2 m fp A i 0
  set w1 := flMixedMult2 m fp A i 1
  set c0 := A j.succ.succ 0
  set c1 := A j.succ.succ (oneIdx m)
  obtain ⟨σ, hσ, hs⟩ := fp.model_sub b (fp.fl_add (fp.fl_mul w0 c0) (fp.fl_mul w1 c1))
  obtain ⟨α, hα, ha⟩ := fp.model_add (fp.fl_mul w0 c0) (fp.fl_mul w1 c1)
  obtain ⟨μ0, hμ0, hm0⟩ := fp.model_mul w0 c0
  obtain ⟨μ1, hμ1, hm1⟩ := fp.model_mul w1 c1
  have hu0 := fp.u_nonneg
  have h1u : (0 : ℝ) ≤ 1 + fp.u := by linarith
  have hW0 : 0 ≤ |w0| * |c0| := mul_nonneg (abs_nonneg _) (abs_nonneg _)
  have hW1 : 0 ≤ |w1| * |c1| := mul_nonneg (abs_nonneg _) (abs_nonneg _)
  -- rounded products
  have e0 : |fp.fl_mul w0 c0| ≤ (1 + fp.u) * (|w0| * |c0|) := by
    rw [hm0, abs_mul, abs_mul]
    calc |w0| * |c0| * |1 + μ0| ≤ |w0| * |c0| * (1 + fp.u) :=
          mul_le_mul_of_nonneg_left (abs_one_add_le fp hμ0) hW0
      _ = (1 + fp.u) * (|w0| * |c0|) := by ring
  have e1 : |fp.fl_mul w1 c1| ≤ (1 + fp.u) * (|w1| * |c1|) := by
    rw [hm1, abs_mul, abs_mul]
    calc |w1| * |c1| * |1 + μ1| ≤ |w1| * |c1| * (1 + fp.u) :=
          mul_le_mul_of_nonneg_left (abs_one_add_le fp hμ1) hW1
      _ = (1 + fp.u) * (|w1| * |c1|) := by ring
  -- rounded add
  have eadd : |fp.fl_add (fp.fl_mul w0 c0) (fp.fl_mul w1 c1)|
      ≤ (1 + fp.u) ^ 2 * (|w0| * |c0| + |w1| * |c1|) := by
    rw [ha, abs_mul]
    have hsum : |fp.fl_mul w0 c0 + fp.fl_mul w1 c1|
        ≤ (1 + fp.u) * (|w0| * |c0| + |w1| * |c1|) := by
      calc |fp.fl_mul w0 c0 + fp.fl_mul w1 c1|
          ≤ |fp.fl_mul w0 c0| + |fp.fl_mul w1 c1| := abs_add_le _ _
        _ ≤ (1 + fp.u) * (|w0| * |c0|) + (1 + fp.u) * (|w1| * |c1|) := add_le_add e0 e1
        _ = (1 + fp.u) * (|w0| * |c0| + |w1| * |c1|) := by ring
    calc |fp.fl_mul w0 c0 + fp.fl_mul w1 c1| * |1 + α|
        ≤ (1 + fp.u) * (|w0| * |c0| + |w1| * |c1|) * (1 + fp.u) :=
          mul_le_mul hsum (abs_one_add_le fp hα) (abs_nonneg _)
            (mul_nonneg h1u (by linarith [hW0, hW1]))
      _ = (1 + fp.u) ^ 2 * (|w0| * |c0| + |w1| * |c1|) := by ring
  -- rounded subtract
  rw [hs, abs_mul]
  have hbnn : 0 ≤ |b| := abs_nonneg _
  have haddnn : 0 ≤ |fp.fl_add (fp.fl_mul w0 c0) (fp.fl_mul w1 c1)| := abs_nonneg _
  calc |b - fp.fl_add (fp.fl_mul w0 c0) (fp.fl_mul w1 c1)| * |1 + σ|
      ≤ (|b| + |fp.fl_add (fp.fl_mul w0 c0) (fp.fl_mul w1 c1)|) * (1 + fp.u) := by
        apply mul_le_mul _ (abs_one_add_le fp hσ) (abs_nonneg _) (add_nonneg hbnn haddnn)
        exact abs_sub _ _
    _ ≤ (|b| + (1 + fp.u) ^ 2 * (|w0| * |c0| + |w1| * |c1|)) * (1 + fp.u) :=
        mul_le_mul_of_nonneg_right (by linarith [eadd]) h1u
    _ = (1 + fp.u) * |b| + (1 + fp.u) ^ 3 * (|w0| * |c0| + |w1| * |c1|) := by ring

/-- `|pivotPath2| ≤ pivotPath2Abs`: the signed 2×2 pivot path is dominated by its
    entrywise absolute value. -/
theorem abs_pivotPath2_le (fp : FPModel) {m : ℕ} (A : Fin (m + 2) → Fin (m + 2) → ℝ)
    (i j : Fin m) : |pivotPath2 m fp A i j| ≤ pivotPath2Abs m fp A i j := by
  rw [pivotPath2, pivotPath2Abs]
  refine (Finset.abs_sum_le_sum_abs _ _).trans ?_
  apply Finset.sum_le_sum; intro p _
  refine (Finset.abs_sum_le_sum_abs _ _).trans ?_
  apply Finset.sum_le_sum; intro q _
  rw [abs_mul, abs_mul]

/-- **2×2 trailing accounting core.**  The 2×2 analogue of the all-1×1
    `trailing_arith`, with the per-stage Schur constant `c ≤ 5` and the size step
    of two (target slope `20(K+2)`).  A self-contained real-number inequality. -/
theorem trailing_arith_two (u K p q t fs as g3 Bs c : ℝ)
    (hu0 : 0 ≤ u) (huε : u ≤ 1 / 100) (hK0 : 0 ≤ K) (hKu : K * u ≤ 1 / 100)
    (hp : 0 ≤ p) (hq : 0 ≤ q) (_ht : 0 ≤ t) (hfs : 0 ≤ fs) (_has0 : 0 ≤ as)
    (_hg3 : 0 ≤ g3) (hg3u : g3 ≤ 6 * u) (hc0 : 0 ≤ c) (hc5 : c ≤ 5)
    (has : as ≤ (1 + u) * p + (1 + u) ^ 3 * q)
    (htq : q * (1 - u) ^ 2 ≤ t)
    (hBs : Bs ≤ 20 * K * u * (as + fs)) :
    c * g3 * (p + q) + Bs ≤ 20 * (K + 2) * u * (p + t + fs) := by
  have hpq : 0 ≤ p + q := by linarith
  have h20Ku : 0 ≤ 20 * K * u :=
    mul_nonneg (mul_nonneg (by norm_num) hK0) hu0
  have step1 : c * g3 * (p + q) ≤ 30 * u * (p + q) := by
    have hcg : c * g3 ≤ 30 * u := by
      calc c * g3 ≤ 5 * (6 * u) := mul_le_mul hc5 hg3u _hg3 (by norm_num)
        _ = 30 * u := by ring
    exact mul_le_mul_of_nonneg_right hcg hpq
  have step2 : Bs ≤ 20 * K * u * ((1 + u) * p + (1 + u) ^ 3 * q + fs) :=
    hBs.trans (mul_le_mul_of_nonneg_left (by linarith) h20Ku)
  have hW : 0 ≤ 20 * (K + 2) * (1 - u) ^ 2 - 20 * K * (1 + u) ^ 3 - 30 := by
    have hKuu : K * u * u ≤ (1 / 100) * u :=
      mul_le_mul_of_nonneg_right hKu hu0
    nlinarith [hKu, huε, hu0, hK0, mul_nonneg hK0 hu0, hKuu,
      mul_nonneg (mul_nonneg hK0 hu0) hu0, sq_nonneg u]
  have hstar :
      30 * (p + q) + 20 * K * ((1 + u) * p + (1 + u) ^ 3 * q + fs)
        ≤ 20 * (K + 2) * (p + t + fs) := by
    have htbound : 20 * (K + 2) * (q * (1 - u) ^ 2) ≤ 20 * (K + 2) * t :=
      mul_le_mul_of_nonneg_left htq (by nlinarith [hK0])
    have hpc : 0 ≤ p * (10 - 20 * K * u) := mul_nonneg hp (by nlinarith [hKu])
    have hqW : 0 ≤ q * (20 * (K + 2) * (1 - u) ^ 2 - 20 * K * (1 + u) ^ 3 - 30) :=
      mul_nonneg hq hW
    nlinarith [hpc, hqW, htbound, hfs]
  have h44 :
      30 * u * (p + q) + 20 * K * u * ((1 + u) * p + (1 + u) ^ 3 * q + fs)
        ≤ 20 * (K + 2) * u * (p + t + fs) := by
    nlinarith [mul_le_mul_of_nonneg_left hstar hu0]
  linarith [step1, step2, h44]

/-- **ProductEntry consOne split** (mirror of the all-1×1 `productEntry_succ_split`
    for the mixed named factors). -/
theorem productEntry_consOne_split (fp : FPModel) {n : ℕ}
    (s : PivotSchedule n) (A : Fin (n + 1) → Fin (n + 1) → ℝ) (i j : Fin n) :
    higham11_4_bunchKaufmanProductEntry (n + 1) (flMixedL fp (s.consOne) A)
        (flMixedD fp (s.consOne) A) i.succ j.succ
      = |fp.fl_div (A i.succ 0) (A 0 0)| * |A 0 0| * |fp.fl_div (A j.succ 0) (A 0 0)|
        + higham11_4_bunchKaufmanProductEntry n (flMixedL fp s (flSchurCompl n fp A))
            (flMixedD fp s (flSchurCompl n fp A)) i j := by
  unfold higham11_4_bunchKaufmanProductEntry
  rw [Fin.sum_univ_succ]
  congr 1
  · rw [Fin.sum_univ_succ]
    have hz : (∑ k₂ : Fin n, |flMixedL fp (s.consOne) A i.succ 0|
        * |flMixedD fp (s.consOne) A 0 k₂.succ| * |flMixedL fp (s.consOne) A j.succ k₂.succ|)
          = 0 := by
      apply Finset.sum_eq_zero; intro x _; simp
    rw [hz, add_zero]; simp
  · apply Finset.sum_congr rfl; intro k₁ _
    rw [Fin.sum_univ_succ]
    have hz : |flMixedL fp (s.consOne) A i.succ k₁.succ|
        * |flMixedD fp (s.consOne) A k₁.succ 0| * |flMixedL fp (s.consOne) A j.succ 0| = 0 := by
      simp
    rw [hz, zero_add]
    apply Finset.sum_congr rfl; intro k₂ _; simp

/-- **Task 9 — envelope dominated by the printed first-order bound.**  Under the
    smallness `n·u ≤ 1/100` and the honest constant caps `cSolve ≤ 40`, `cStage ≤ 5`,
    the recursive mixed-pivot envelope is dominated by the printed Theorem 11.3
    first-order bound with the LINEAR polynomial `p(n) = 20 n`. -/
theorem flMixed_envelope_le_printed (fp : FPModel) (hval : gammaValid fp 3)
    (cSolve cStage : ℝ) (hcS0 : 0 ≤ cSolve) (hcS40 : cSolve ≤ 40)
    (hcSt0 : 0 ≤ cStage) (hcSt5 : cStage ≤ 5) :
    ∀ {n : ℕ} (s : PivotSchedule n) (A : Fin n → Fin n → ℝ),
      (n : ℝ) * fp.u ≤ 1 / 100 →
      FlMixedPivots fp cSolve cStage s A →
      ∀ i j : Fin n,
        flBlockLDLTMixedBound fp cSolve cStage s A i j
          ≤ higham11_3_printedFirstOrderBound n A (flMixedL fp s A) (flMixedD fp s A)
              id (pPoly n) fp.u i j := by
  intro n s
  induction s with
  | nil => intro A _ _ i; exact Fin.elim0 i
  | @consOne n s ih =>
      intro A hsmall hp i j
      obtain ⟨ha, hsym1, hpS⟩ := hp
      have hu0 := fp.u_nonneg
      have hsmall' : (n : ℝ) * fp.u ≤ 1 / 100 := by
        have hmono : (n : ℝ) * fp.u ≤ ((n + 1 : ℕ) : ℝ) * fp.u :=
          mul_le_mul_of_nonneg_right (by exact_mod_cast Nat.le_succ n) hu0
        push_cast at hmono hsmall ⊢; linarith
      have hu100 : fp.u ≤ 1 / 100 := by
        have h1 : (1 : ℝ) ≤ ((n + 1 : ℕ) : ℝ) := by exact_mod_cast Nat.succ_le_succ (Nat.zero_le n)
        have : fp.u ≤ ((n + 1 : ℕ) : ℝ) * fp.u := le_mul_of_one_le_left hu0 h1
        push_cast at this hsmall; linarith
      rcases Fin.eq_zero_or_eq_succ i with rfl | ⟨i', rfl⟩
      · rcases Fin.eq_zero_or_eq_succ j with rfl | ⟨j', rfl⟩
        · -- pivot (0,0)
          have hL : flBlockLDLTMixedBound fp cSolve cStage (s.consOne) A 0 0 = 0 := by
            simp [flBlockLDLTMixedBound_consOne, flBlockLDLTOneByOneStageBound]
          rw [hL]
          exact higham11_3_printedFirstOrderBound_nonneg (n + 1) A
            (flMixedL fp (s.consOne) A) (flMixedD fp (s.consOne) A) id
            (pPoly (n + 1)) fp.u (mul_nonneg (by unfold pPoly; positivity) hu0) 0 0
        · -- pivot row (0, j'+1)
          have hL : flBlockLDLTMixedBound fp cSolve cStage (s.consOne) A 0 j'.succ
              = fp.u * |A 0 j'.succ| := by
            simp [flBlockLDLTMixedBound_consOne, flBlockLDLTOneByOneStageBound]
          rw [hL]
          simp only [higham11_3_printedFirstOrderBound, pPoly, id_eq]
          push_cast
          refine easy_case_bound fp.u _ _ _ hu0 ?_ (abs_nonneg _)
            (higham11_4_bunchKaufmanProductEntry_nonneg _ _ _ _ _)
          nlinarith [Nat.cast_nonneg (α := ℝ) n]
      · rcases Fin.eq_zero_or_eq_succ j with rfl | ⟨j', rfl⟩
        · -- pivot column (i'+1, 0)
          have hL : flBlockLDLTMixedBound fp cSolve cStage (s.consOne) A i'.succ 0
              = fp.u * |A i'.succ 0| := by
            simp [flBlockLDLTMixedBound_consOne, flBlockLDLTOneByOneStageBound]
          rw [hL]
          simp only [higham11_3_printedFirstOrderBound, pPoly, id_eq]
          push_cast
          refine easy_case_bound fp.u _ _ _ hu0 ?_ (abs_nonneg _)
            (higham11_4_bunchKaufmanProductEntry_nonneg _ _ _ _ _)
          nlinarith [Nat.cast_nonneg (α := ℝ) n]
        · -- trailing block (i'+1, j'+1)
          have hLHS : flBlockLDLTMixedBound fp cSolve cStage (s.consOne) A i'.succ j'.succ
              = 2 * gamma fp 3
                  * (|A i'.succ j'.succ| + |A i'.succ 0 * A 0 j'.succ / A 0 0|)
                + flBlockLDLTMixedBound fp cSolve cStage s (flSchurCompl n fp A) i' j' := by
            simp [flBlockLDLTMixedBound_consOne, flBlockLDLTOneByOneStageBound]
          have hRHS : higham11_3_printedFirstOrderBound (n + 1) A
              (flMixedL fp (s.consOne) A) (flMixedD fp (s.consOne) A) id
              (pPoly (n + 1)) fp.u i'.succ j'.succ
              = 20 * ((n : ℝ) + 1) * fp.u
                  * (|A i'.succ j'.succ|
                      + |fp.fl_div (A i'.succ 0) (A 0 0)| * |A 0 0|
                          * |fp.fl_div (A j'.succ 0) (A 0 0)|
                      + higham11_4_bunchKaufmanProductEntry n
                          (flMixedL fp s (flSchurCompl n fp A))
                          (flMixedD fp s (flSchurCompl n fp A)) i' j') := by
            simp only [higham11_3_printedFirstOrderBound, pPoly, id_eq]
            rw [productEntry_consOne_split]
            push_cast; ring
          have hBs : flBlockLDLTMixedBound fp cSolve cStage s (flSchurCompl n fp A) i' j'
              ≤ 20 * (n : ℝ) * fp.u
                  * (|flSchurCompl n fp A i' j'|
                      + higham11_4_bunchKaufmanProductEntry n
                          (flMixedL fp s (flSchurCompl n fp A))
                          (flMixedD fp s (flSchurCompl n fp A)) i' j') := by
            have hih := ih (flSchurCompl n fp A) hsmall' hpS i' j'
            simpa [higham11_3_printedFirstOrderBound, pPoly, id_eq] using hih
          rw [hLHS, hRHS]
          exact trailing_arith fp.u (n : ℝ)
            (|A i'.succ j'.succ|)
            (|A i'.succ 0 * A 0 j'.succ / A 0 0|)
            (|fp.fl_div (A i'.succ 0) (A 0 0)| * |A 0 0|
              * |fp.fl_div (A j'.succ 0) (A 0 0)|)
            (higham11_4_bunchKaufmanProductEntry n
              (flMixedL fp s (flSchurCompl n fp A))
              (flMixedD fp s (flSchurCompl n fp A)) i' j')
            (|flSchurCompl n fp A i' j'|)
            (gamma fp 3)
            (flBlockLDLTMixedBound fp cSolve cStage s (flSchurCompl n fp A) i' j')
            hu0 hu100 (Nat.cast_nonneg n) hsmall'
            (abs_nonneg _) (abs_nonneg _)
            (mul_nonneg (mul_nonneg (abs_nonneg _) (abs_nonneg _)) (abs_nonneg _))
            (higham11_4_bunchKaufmanProductEntry_nonneg _ _ _ _ _)
            (abs_nonneg _)
            (gamma_nonneg fp hval)
            (gamma_three_le fp (by linarith))
            (schur_entry_upper fp hu0 n A i' j' ha)
            (schur_pivot_product_lower fp (by linarith) n A i' j' ha (hsym1 j'))
            hBs
  | @consTwo m s ih =>
      intro A hsmall hp i j
      obtain ⟨hr0, hr1, hc0, hc1, ht, hbridge, hpS⟩ := hp
      have hu0 := fp.u_nonneg
      have hsmall' : (m : ℝ) * fp.u ≤ 1 / 100 := by
        have hmono : (m : ℝ) * fp.u ≤ ((m + 2 : ℕ) : ℝ) * fp.u :=
          mul_le_mul_of_nonneg_right (by exact_mod_cast Nat.le_add_right m 2) hu0
        push_cast at hmono hsmall ⊢; linarith
      have hu100 : fp.u ≤ 1 / 100 := by
        have h1 : (1 : ℝ) ≤ ((m + 2 : ℕ) : ℝ) := by
          have : (1 : ℕ) ≤ m + 2 := by omega
          exact_mod_cast this
        have : fp.u ≤ ((m + 2 : ℕ) : ℝ) * fp.u := le_mul_of_one_le_left hu0 h1
        push_cast at this hsmall; linarith
      -- helper: cSolve·u·G ≤ 20(m+2)·u·(|A|+G) for the pivot row/column cases
      have hrowcol : ∀ (Aij G : ℝ), 0 ≤ Aij → 0 ≤ G →
          cSolve * fp.u * G ≤ 20 * ((m : ℝ) + 2) * fp.u * (Aij + G) := by
        intro Aij G hAij hG
        have hm2 : cSolve ≤ 20 * ((m : ℝ) + 2) := by
          have : (0 : ℝ) ≤ (m : ℝ) := Nat.cast_nonneg m
          nlinarith [hcS40]
        have h1 : cSolve * fp.u * G ≤ 20 * ((m : ℝ) + 2) * fp.u * G :=
          mul_le_mul_of_nonneg_right
            (mul_le_mul_of_nonneg_right hm2 hu0) hG
        have h2 : 20 * ((m : ℝ) + 2) * fp.u * G ≤ 20 * ((m : ℝ) + 2) * fp.u * (Aij + G) := by
          apply mul_le_mul_of_nonneg_left (by linarith)
          positivity
        linarith
      rcases Fin.eq_zero_or_eq_succ i with rfl | ⟨i', rfl⟩
      · rcases Fin.eq_zero_or_eq_succ j with rfl | ⟨j', rfl⟩
        · -- (0,0) block
          rw [flBlockLDLTMixedBound_consTwo, SB2_00]
          exact higham11_3_printedFirstOrderBound_nonneg (m + 2) A _ _ id _ _
            (mul_nonneg (by unfold pPoly; positivity) hu0) 0 0
        · rcases Fin.eq_zero_or_eq_succ j' with rfl | ⟨j, rfl⟩
          · -- (0, succ 0) block
            rw [flBlockLDLTMixedBound_consTwo, SB2_01]
            exact higham11_3_printedFirstOrderBound_nonneg (m + 2) A _ _ id _ _
              (mul_nonneg (by unfold pPoly; positivity) hu0) 0 (Fin.succ 0)
          · -- (0, j+2) pivot row
            rw [flBlockLDLTMixedBound_consTwo, SB2_0t]
            simp only [higham11_3_printedFirstOrderBound, pPoly, id_eq]
            rw [productEntry_consTwo_0t]
            push_cast
            exact hrowcol _ _ (abs_nonneg _)
              (Finset.sum_nonneg (fun q _ => mul_nonneg (abs_nonneg _) (abs_nonneg _)))
      · rcases Fin.eq_zero_or_eq_succ i' with rfl | ⟨i, rfl⟩
        · rcases Fin.eq_zero_or_eq_succ j with rfl | ⟨j', rfl⟩
          · -- (succ 0, 0) block
            rw [flBlockLDLTMixedBound_consTwo, SB2_10]
            exact higham11_3_printedFirstOrderBound_nonneg (m + 2) A _ _ id _ _
              (mul_nonneg (by unfold pPoly; positivity) hu0) (Fin.succ 0) 0
          · rcases Fin.eq_zero_or_eq_succ j' with rfl | ⟨j, rfl⟩
            · -- (succ 0, succ 0) block
              rw [flBlockLDLTMixedBound_consTwo, SB2_11]
              exact higham11_3_printedFirstOrderBound_nonneg (m + 2) A _ _ id _ _
                (mul_nonneg (by unfold pPoly; positivity) hu0) (Fin.succ 0) (Fin.succ 0)
            · -- (succ 0, j+2) pivot row 1
              rw [flBlockLDLTMixedBound_consTwo, SB2_1t]
              simp only [higham11_3_printedFirstOrderBound, pPoly, id_eq]
              rw [productEntry_consTwo_1t]
              push_cast
              exact hrowcol _ _ (abs_nonneg _)
                (Finset.sum_nonneg (fun q _ => mul_nonneg (abs_nonneg _) (abs_nonneg _)))
        · rcases Fin.eq_zero_or_eq_succ j with rfl | ⟨j', rfl⟩
          · -- (i+2, 0) pivot column 0
            rw [flBlockLDLTMixedBound_consTwo, SB2_t0]
            simp only [higham11_3_printedFirstOrderBound, pPoly, id_eq]
            rw [productEntry_consTwo_t0]
            push_cast
            exact hrowcol _ _ (abs_nonneg _)
              (Finset.sum_nonneg (fun p _ => mul_nonneg (abs_nonneg _) (abs_nonneg _)))
          · rcases Fin.eq_zero_or_eq_succ j' with rfl | ⟨j, rfl⟩
            · -- (i+2, succ 0) pivot column 1
              rw [flBlockLDLTMixedBound_consTwo, SB2_t1]
              simp only [higham11_3_printedFirstOrderBound, pPoly, id_eq]
              rw [productEntry_consTwo_t1]
              push_cast
              exact hrowcol _ _ (abs_nonneg _)
                (Finset.sum_nonneg (fun p _ => mul_nonneg (abs_nonneg _) (abs_nonneg _)))
            · -- (i+2, j+2) trailing block
              rw [flBlockLDLTMixedBound_consTwo, SB2_tt]
              have hRHS : higham11_3_printedFirstOrderBound (m + 2) A
                  (flMixedL fp (s.consTwo) A) (flMixedD fp (s.consTwo) A) id
                  (pPoly (m + 2)) fp.u i.succ.succ j.succ.succ
                  = 20 * ((m : ℝ) + 2) * fp.u
                      * (|A i.succ.succ j.succ.succ|
                          + pivotPath2Abs m fp A i j
                          + higham11_4_bunchKaufmanProductEntry m
                              (flMixedL fp s (flSchurCompl2 m fp A))
                              (flMixedD fp s (flSchurCompl2 m fp A)) i j) := by
                simp only [higham11_3_printedFirstOrderBound, pPoly, id_eq]
                rw [productEntry_consTwo_trailing]
                push_cast; ring
              rw [hRHS]
              have hBs : flBlockLDLTMixedBound fp cSolve cStage s (flSchurCompl2 m fp A) i j
                  ≤ 20 * (m : ℝ) * fp.u
                      * (|flSchurCompl2 m fp A i j|
                          + higham11_4_bunchKaufmanProductEntry m
                              (flMixedL fp s (flSchurCompl2 m fp A))
                              (flMixedD fp s (flSchurCompl2 m fp A)) i j) := by
                have hih := ih (flSchurCompl2 m fp A) hsmall' hpS i j
                simpa [higham11_3_printedFirstOrderBound, pPoly, id_eq] using hih
              have htq : pivotPath2Abs m fp A i j * (1 - fp.u) ^ 2
                  ≤ pivotPath2Abs m fp A i j := by
                have hpp : 0 ≤ pivotPath2Abs m fp A i j := by
                  rw [pivotPath2Abs]
                  exact Finset.sum_nonneg fun p _ => Finset.sum_nonneg fun q _ =>
                    mul_nonneg (mul_nonneg (abs_nonneg _) (abs_nonneg _)) (abs_nonneg _)
                have hfac : 0 ≤ pivotPath2Abs m fp A i j * (fp.u * (2 - fp.u)) :=
                  mul_nonneg hpp (mul_nonneg fp.u_nonneg (by linarith))
                nlinarith [hfac]
              have has : |flSchurCompl2 m fp A i j|
                  ≤ (1 + fp.u) * |A i.succ.succ j.succ.succ|
                    + (1 + fp.u) ^ 3 * pivotPath2Abs m fp A i j := by
                refine (flSchurCompl2_magnitude fp A i j).trans ?_
                have h3 : (0 : ℝ) ≤ (1 + fp.u) ^ 3 := by positivity
                have hb := mul_le_mul_of_nonneg_left (hbridge i j) h3
                linarith [hb]
              exact trailing_arith_two fp.u (m : ℝ)
                (|A i.succ.succ j.succ.succ|)
                (pivotPath2Abs m fp A i j)
                (pivotPath2Abs m fp A i j)
                (higham11_4_bunchKaufmanProductEntry m
                  (flMixedL fp s (flSchurCompl2 m fp A))
                  (flMixedD fp s (flSchurCompl2 m fp A)) i j)
                (|flSchurCompl2 m fp A i j|)
                (gamma fp 3)
                (flBlockLDLTMixedBound fp cSolve cStage s (flSchurCompl2 m fp A) i j)
                cStage
                hu0 hu100 (Nat.cast_nonneg m) hsmall'
                (abs_nonneg _)
                (by rw [pivotPath2Abs]; exact Finset.sum_nonneg fun p _ =>
                  Finset.sum_nonneg fun q _ =>
                    mul_nonneg (mul_nonneg (abs_nonneg _) (abs_nonneg _)) (abs_nonneg _))
                (by rw [pivotPath2Abs]; exact Finset.sum_nonneg fun p _ =>
                  Finset.sum_nonneg fun q _ =>
                    mul_nonneg (mul_nonneg (abs_nonneg _) (abs_nonneg _)) (abs_nonneg _))
                (higham11_4_bunchKaufmanProductEntry_nonneg _ _ _ _ _)
                (abs_nonneg _)
                (gamma_nonneg fp hval)
                (gamma_three_le fp (by linarith))
                hcSt0 hcSt5
                has
                htq
                hBs

/-! ## Task 10 — the printed-strength mixed-pivot factorization theorem -/

/-- **Theorem 11.3, mixed-pivot (1×1 and 2×2 pivots, σ = id) case, printed
    first-order strength.**  For a symmetric input whose rounded mixed-pivot
    block-LDLᵀ path (recorded by the schedule `s`) satisfies the per-stage
    conditions `FlMixedPivots` — 1×1 stages fully derived from the model, 2×2
    stages resting on the (11.5) 2×2-solve bound (constant `cSolve`) and the
    assembled 2×2 Schur backward/magnitude bounds (constant `cStage`) — under the
    smallness `n·u ≤ 1/100` and the honest constant caps `cSolve ≤ 40`,
    `cStage ≤ 5`, there are computed factors `L̂, D̂` and backward-error matrices
    `ΔA₁, ΔA₂` with

      `L̂D̂L̂ᵀ = A + ΔA₁`,   `|ΔAₖ| ≤ p(n)·u·(|A| + |L̂||D̂||L̂ᵀ|)`,

    the printed Higham (11.5) envelope with the LINEAR polynomial `p(n) = 20 n`.
    The named factors are `flMixedL`, `flMixedD`. -/
theorem higham11_3_block_ldlt_mixed_printed (fp : FPModel) (hval : gammaValid fp 3)
    (cSolve cStage : ℝ) (hcS0 : 0 ≤ cSolve) (hcS40 : cSolve ≤ 40)
    (hcSt0 : 0 ≤ cStage) (hcSt5 : cStage ≤ 5)
    {n : ℕ} (s : PivotSchedule n) (A : Fin n → Fin n → ℝ)
    (hsmall : (n : ℝ) * fp.u ≤ 1 / 100)
    (hp : FlMixedPivots fp cSolve cStage s A) :
    ∃ L D ΔA1 ΔA2 : Fin n → Fin n → ℝ,
      (∀ i j, |ΔA1 i j|
          ≤ higham11_3_printedFirstOrderBound n A L D id (pPoly n) fp.u i j) ∧
      (∀ i j, |ΔA2 i j|
          ≤ higham11_3_printedFirstOrderBound n A L D id (pPoly n) fp.u i j) ∧
      (∀ i j, (∑ k₁, ∑ k₂, L i k₁ * D k₁ k₂ * L j k₂) = A i j + ΔA1 i j) := by
  refine ⟨flMixedL fp s A, flMixedD fp s A,
    fun i j => (∑ k₁, ∑ k₂, flMixedL fp s A i k₁ * flMixedD fp s A k₁ k₂
        * flMixedL fp s A j k₂) - A i j,
    0, ?_, ?_, ?_⟩
  · intro i j
    exact le_trans (fl_blockLDLT_mixed_bound fp hval cSolve cStage s A hp i j)
      (flMixed_envelope_le_printed fp hval cSolve cStage hcS0 hcS40 hcSt0 hcSt5 s A hsmall hp i j)
  · intro i j
    simp only [Pi.zero_apply, abs_zero]
    exact higham11_3_printedFirstOrderBound_nonneg n A
      (flMixedL fp s A) (flMixedD fp s A) id (pPoly n) fp.u
      (mul_nonneg (by unfold pPoly; positivity) fp.u_nonneg) i j
  · intro i j; ring

end NumStability.Ch11Closure.Mixed
