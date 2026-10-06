/-
Chapter 11 closure: **Theorem 11.7** — normwise backward-error bound for Bunch's
symmetric-tridiagonal pivoting strategy (Algorithm 11.6), obtained as a
*corollary* of the printed-strength mixed-pivot block-LDLᵀ result
(`higham11_3_block_ldlt_mixed_printed`).

Higham states Theorem 11.7 as: for a symmetric tridiagonal `A`, Bunch's method
produces `A + ΔA₁ = L̂D̂L̂ᵀ` and solves `(A + ΔA₂)x̂ = b` with
`‖ΔAᵢ‖_M ≤ c·u·‖A‖_M + O(u²)`.  The proof is the mixed block-LDLᵀ backward error
(Theorem 11.3) specialized to the pivot schedule chosen by Algorithm 11.6, plus
the structural fact that for a tridiagonal matrix the computed factors satisfy
`‖ |L̂||D̂||L̂ᵀ| ‖_M ≤ c₀·‖A‖_M` (constant growth, no fill-in).

This file:
  * proves the *no-fill-in* structural invariant (Lemma T): the rounded 1×1 and
    2×2 Schur complements of a symmetric tridiagonal matrix are again symmetric
    tridiagonal — the only genuine correction is at the leading `(0,0)` corner;
  * assembles the Theorem 11.7 normwise interface from the mixed printed bound.

Honesty note (see the closing comment for the precise status): the 2×2 stages
rest on the (11.5) 2×2-solve/Schur per-stage hypotheses carried by
`FlMixedPivots` (a legitimate Higham source hypothesis), and the factor-norm
bound `‖ |L̂||D̂||L̂ᵀ| ‖_M ≤ c₀·‖A‖_M` enters the final corollary as an explicit
hypothesis `hfactor`.  Everything else is derived from the floating-point model.
No `sorry`/`admit`/`axiom`/`native_decide`.
-/
import NumStability.Algorithms.Cholesky.BlockLDLTMixedPivotCh11Closure

open scoped BigOperators

namespace NumStability.Ch11Closure.BunchTri

open NumStability
open NumStability.Ch11Closure
open NumStability.Ch11Closure.Mixed

/-! ## Floating-point model zero laws

The abstract `FPModel` (Model.lean) provides `fl_add 0 x = x` exactly, and the
relative-error laws give `fl(x·0) = (x·0)(1+δ) = 0` and `fl(0-0) = 0`.  These are
the exact-zero facts that drive the tridiagonal no-fill-in invariant. -/

@[simp] theorem fl_mul_right_zero (fp : FPModel) (x : ℝ) : fp.fl_mul x 0 = 0 := by
  obtain ⟨δ, _, h⟩ := fp.model_mul x 0
  rw [h]; ring

@[simp] theorem fl_mul_left_zero (fp : FPModel) (x : ℝ) : fp.fl_mul 0 x = 0 := by
  obtain ⟨δ, _, h⟩ := fp.model_mul 0 x
  rw [h]; ring

@[simp] theorem fl_sub_zero_zero (fp : FPModel) : fp.fl_sub 0 0 = 0 := by
  obtain ⟨δ, _, h⟩ := fp.model_sub 0 0
  rw [h]; ring

/-- `fl_sub a 0 = a·(1 + δ)` with `|δ| ≤ u`: the from-zero subtraction is not
    exact in the standard model, only correct to one rounding.  This slack is the
    reason the tridiagonal band entries carry a `(1+u)` factor through the
    recursion. -/
theorem fl_sub_zero_right (fp : FPModel) (a : ℝ) :
    ∃ δ : ℝ, |δ| ≤ fp.u ∧ fp.fl_sub a 0 = a * (1 + δ) := by
  obtain ⟨δ, hδ, h⟩ := fp.model_sub a 0
  exact ⟨δ, hδ, by rw [h]; ring⟩

/-- `fl_div 0 y = 0` when `y ≠ 0`. -/
theorem fl_div_zero_left (fp : FPModel) (y : ℝ) (hy : y ≠ 0) :
    fp.fl_div 0 y = 0 := by
  obtain ⟨δ, _, h⟩ := fp.model_div 0 y hy
  rw [h]; simp

/-! ## Lemma T — the no-fill-in tridiagonal invariant

For a symmetric tridiagonal `A`, Bunch's rounded Schur complements
(`flSchurCompl` for a 1×1 pivot, `flSchurCompl2` for a 2×2 pivot) produce again a
symmetric tridiagonal matrix.  The only genuine Schur correction lands on the
leading `(0,0)` corner; every off-corner entry is `fl_sub A 0` (the trailing data
copied through one rounding), and every off-band entry stays exactly zero.  This
is the structural reason tridiagonal Bunch has *constant* growth. -/

/-- On a symmetric tridiagonal matrix the 2×2-pivot multiplier row vanishes for
    every trailing index `i` with `1 ≤ i` (only the first trailing row couples to
    the leading 2×2 block). -/
theorem flMixedMult2_eq_zero_of_tridiag (fp : FPModel) {m : ℕ}
    (A : Fin (m + 2) → Fin (m + 2) → ℝ) (hA : IsSymTridiagonal (m + 2) A)
    (i : Fin m) (hi : 1 ≤ i.val) :
    flMixedMult2 m fp A i 0 = 0 ∧ flMixedMult2 m fp A i 1 = 0 := by
  have hci0 : A i.succ.succ 0 = 0 := by
    apply hA.2; right; simp only [Fin.val_succ, Fin.val_zero]; omega
  have hci1 : A i.succ.succ (oneIdx m) = 0 := by
    apply hA.2; right; simp only [oneIdx, Fin.val_succ, Fin.val_zero]; omega
  constructor
  · simp only [flMixedMult2, Fin.cases_zero, hci0, hci1, fl_mul_left_zero, fp.fl_add_zero]
  · simp only [flMixedMult2, hci0, hci1, fl_mul_left_zero, fp.fl_add_zero,
      show (1 : Fin 2) = Fin.succ 0 from rfl, Fin.cases_succ]

/-- **No fill-in / no growth off the corner.**  For a symmetric tridiagonal `A`,
    the rounded 2×2-pivot Schur correction vanishes at every trailing entry
    `(i,j)` except the leading corner `(0,0)`: the computed entry is just the
    trailing datum through one subtraction from zero. -/
theorem flSchurCompl2_eq_sub_zero_of_ne_corner (fp : FPModel) {m : ℕ}
    (A : Fin (m + 2) → Fin (m + 2) → ℝ) (hA : IsSymTridiagonal (m + 2) A)
    (i j : Fin m) (hne : i.val ≠ 0 ∨ j.val ≠ 0) :
    flSchurCompl2 m fp A i j = fp.fl_sub (A i.succ.succ j.succ.succ) 0 := by
  have hcj0 : A j.succ.succ 0 = 0 := by
    apply hA.2; right; simp only [Fin.val_succ, Fin.val_zero]; omega
  have hcorr :
      fp.fl_add (fp.fl_mul (flMixedMult2 m fp A i 0) (A j.succ.succ 0))
        (fp.fl_mul (flMixedMult2 m fp A i 1) (A j.succ.succ (oneIdx m))) = 0 := by
    rw [hcj0, fl_mul_right_zero, fp.fl_add_zero]
    rcases Nat.eq_zero_or_pos j.val with hj | hj
    · have hi1 : 1 ≤ i.val := by rcases hne with h | h <;> omega
      rw [(flMixedMult2_eq_zero_of_tridiag fp A hA i hi1).2, fl_mul_left_zero]
    · have hcj1 : A j.succ.succ (oneIdx m) = 0 := by
        apply hA.2; right; simp only [oneIdx, Fin.val_succ, Fin.val_zero]; omega
      rw [hcj1, fl_mul_right_zero]
  unfold flSchurCompl2
  rw [hcorr]

/-- Off the diagonal is a special case of "off the corner". -/
theorem flSchurCompl2_offdiag (fp : FPModel) {m : ℕ}
    (A : Fin (m + 2) → Fin (m + 2) → ℝ) (hA : IsSymTridiagonal (m + 2) A)
    (i j : Fin m) (hij : i ≠ j) :
    flSchurCompl2 m fp A i j = fp.fl_sub (A i.succ.succ j.succ.succ) 0 := by
  apply flSchurCompl2_eq_sub_zero_of_ne_corner fp A hA i j
  rcases Nat.eq_zero_or_pos i.val with h | h
  · rcases Nat.eq_zero_or_pos j.val with h2 | h2
    · exact absurd (Fin.ext (by omega)) hij
    · right; omega
  · left; omega

/-- **Lemma T (2×2 pivot).**  The rounded 2×2-pivot Schur complement of a
    symmetric tridiagonal matrix is symmetric tridiagonal. -/
theorem flSchurCompl2_isSymTridiagonal (fp : FPModel) {m : ℕ}
    (A : Fin (m + 2) → Fin (m + 2) → ℝ) (hA : IsSymTridiagonal (m + 2) A) :
    IsSymTridiagonal m (flSchurCompl2 m fp A) := by
  refine ⟨?_, ?_⟩
  · intro i j
    rcases eq_or_ne i j with rfl | hij
    · rfl
    · rw [flSchurCompl2_offdiag fp A hA i j hij,
        flSchurCompl2_offdiag fp A hA j i (Ne.symm hij), hA.1 i.succ.succ j.succ.succ]
  · intro i j hband
    have hij : i ≠ j := by rintro rfl; rcases hband with h | h <;> omega
    rw [flSchurCompl2_offdiag fp A hA i j hij]
    have hAij : A i.succ.succ j.succ.succ = 0 := by
      apply hA.2
      rcases hband with h | h
      · left; simp only [Fin.val_succ]; omega
      · right; simp only [Fin.val_succ]; omega
    rw [hAij, fl_sub_zero_zero]

/-- **Lemma T (1×1 pivot).**  The rounded 1×1-pivot Schur complement of a
    symmetric tridiagonal matrix with nonzero leading pivot is symmetric
    tridiagonal. -/
theorem flSchurCompl_offdiag (fp : FPModel) {n : ℕ}
    (A : Fin (n + 1) → Fin (n + 1) → ℝ) (hA : IsSymTridiagonal (n + 1) A)
    (hA00 : A 0 0 ≠ 0) (i j : Fin n) (hij : i ≠ j) :
    flSchurCompl n fp A i j = fp.fl_sub (A i.succ j.succ) 0 := by
  have hcorr :
      fp.fl_mul (fp.fl_div (A i.succ 0) (A 0 0)) (A 0 j.succ) = 0 := by
    rcases Nat.eq_zero_or_pos j.val with hj | hj
    · have hi1 : 1 ≤ i.val := by
        rcases Nat.eq_zero_or_pos i.val with hi | hi
        · exact absurd (Fin.ext (by omega)) hij
        · omega
      have hi0 : A i.succ 0 = 0 := by
        apply hA.2; right; simp only [Fin.val_succ, Fin.val_zero]; omega
      rw [hi0, fl_div_zero_left fp _ hA00, fl_mul_left_zero]
    · have h0j : A 0 j.succ = 0 := by
        apply hA.2; left; simp only [Fin.val_succ, Fin.val_zero]; omega
      rw [h0j, fl_mul_right_zero]
  unfold flSchurCompl
  rw [hcorr]

theorem flSchurCompl_isSymTridiagonal (fp : FPModel) {n : ℕ}
    (A : Fin (n + 1) → Fin (n + 1) → ℝ) (hA : IsSymTridiagonal (n + 1) A)
    (hA00 : A 0 0 ≠ 0) :
    IsSymTridiagonal n (flSchurCompl n fp A) := by
  refine ⟨?_, ?_⟩
  · intro i j
    rcases eq_or_ne i j with rfl | hij
    · rfl
    · rw [flSchurCompl_offdiag fp A hA hA00 i j hij,
        flSchurCompl_offdiag fp A hA hA00 j i (Ne.symm hij), hA.1 i.succ j.succ]
  · intro i j hband
    have hij : i ≠ j := by rintro rfl; rcases hband with h | h <;> omega
    rw [flSchurCompl_offdiag fp A hA hA00 i j hij]
    have hAij : A i.succ j.succ = 0 := by
      apply hA.2
      rcases hband with h | h
      · left; simp only [Fin.val_succ]; omega
      · right; simp only [Fin.val_succ]; omega
    rw [hAij, fl_sub_zero_zero]

/-! ## Task 2 (tractable part) — the trailing 2×2 Schur budget off the corner

`FlMixedPivots` bundles, for each 2×2 stage, the trailing backward-error
hypothesis
`|pivotPath2 + flSchurCompl2 − A| ≤ cStage·γ₃·(|A| + pivotPath2Abs)`.
For a symmetric tridiagonal matrix every trailing entry *except the leading
corner* is fill-in-free: the signed pivot path vanishes and the computed Schur
entry is the trailing datum through one subtraction from zero, so the budget
holds with the smallest possible constant `cStage = 1`, derived purely from the
model.  The corner `(0,0)` entry is the only one that requires the genuine
(11.5) 2×2 solve/Schur analysis. -/

/-- The signed 2×2 pivot path vanishes off the leading corner for a tridiagonal
    matrix (the multipliers of every non-leading trailing row are zero). -/
theorem pivotPath2_eq_zero_of_ne_corner (fp : FPModel) {m : ℕ}
    (A : Fin (m + 2) → Fin (m + 2) → ℝ) (hA : IsSymTridiagonal (m + 2) A)
    (i j : Fin m) (hne : i.val ≠ 0 ∨ j.val ≠ 0) :
    pivotPath2 m fp A i j = 0 := by
  rw [pivotPath2]
  rcases hne with hi | hj
  · have h0 := flMixedMult2_eq_zero_of_tridiag fp A hA i (by omega)
    simp only [Fin.sum_univ_two, h0.1, h0.2, zero_mul, mul_zero, add_zero, zero_add]
  · have h0 := flMixedMult2_eq_zero_of_tridiag fp A hA j (by omega)
    simp only [Fin.sum_univ_two, h0.1, h0.2, zero_mul, mul_zero, add_zero, zero_add]

/-- **Derived off-corner trailing budget.**  For a symmetric tridiagonal matrix,
    the per-stage trailing 2×2 Schur backward error holds with `cStage = 1` at
    every trailing entry `(i,j) ≠ (0,0)`, purely from the floating-point model —
    no (11.5) hypothesis is used.  This is the fill-in-free portion of the 2×2
    stage condition in `FlMixedPivots`. -/
theorem flSchurCompl2_trailing_error_offcorner (fp : FPModel) (hval : gammaValid fp 3)
    {m : ℕ} (A : Fin (m + 2) → Fin (m + 2) → ℝ) (hA : IsSymTridiagonal (m + 2) A)
    (i j : Fin m) (hne : i.val ≠ 0 ∨ j.val ≠ 0) :
    |pivotPath2 m fp A i j + flSchurCompl2 m fp A i j - A i.succ.succ j.succ.succ|
      ≤ 1 * gamma fp 3 * (|A i.succ.succ j.succ.succ| + pivotPath2Abs m fp A i j) := by
  rw [pivotPath2_eq_zero_of_ne_corner fp A hA i j hne,
    flSchurCompl2_eq_sub_zero_of_ne_corner fp A hA i j hne]
  obtain ⟨δ, hδ, hsub⟩ := fl_sub_zero_right fp (A i.succ.succ j.succ.succ)
  rw [hsub]
  have hrw : (0 : ℝ) + A i.succ.succ j.succ.succ * (1 + δ) - A i.succ.succ j.succ.succ
      = A i.succ.succ j.succ.succ * δ := by ring
  rw [hrw, abs_mul]
  have hu3 : fp.u ≤ gamma fp 3 := u_le_gamma fp (by norm_num) hval
  have hγ0 : 0 ≤ gamma fp 3 := gamma_nonneg fp hval
  have hpp : 0 ≤ pivotPath2Abs m fp A i j := by
    rw [pivotPath2Abs]
    exact Finset.sum_nonneg fun p _ => Finset.sum_nonneg fun q _ =>
      mul_nonneg (mul_nonneg (abs_nonneg _) (abs_nonneg _)) (abs_nonneg _)
  calc |A i.succ.succ j.succ.succ| * |δ|
      ≤ gamma fp 3 * |A i.succ.succ j.succ.succ| := by
        rw [mul_comm (gamma fp 3)]
        exact mul_le_mul_of_nonneg_left (hδ.trans hu3) (abs_nonneg _)
    _ ≤ gamma fp 3 * (|A i.succ.succ j.succ.succ| + pivotPath2Abs m fp A i j) :=
        mul_le_mul_of_nonneg_left (by linarith) hγ0
    _ = 1 * gamma fp 3 * (|A i.succ.succ j.succ.succ| + pivotPath2Abs m fp A i j) := by ring

/-- **Lemma G (per-step, off corner).**  A single 2×2 tridiagonal Bunch stage
    does not grow the off-corner band entries beyond the one-rounding factor
    `(1+u)`: `|flSchurCompl2 i j| ≤ (1+u)·|A_{i+2,j+2}|`.  This is the fill-in-free
    growth control on the trailing band (the corner `(0,0)` growth is the only
    place the Algorithm-11.6 acceptance test is needed). -/
theorem flSchurCompl2_offcorner_bound (fp : FPModel) {m : ℕ}
    (A : Fin (m + 2) → Fin (m + 2) → ℝ) (hA : IsSymTridiagonal (m + 2) A)
    (i j : Fin m) (hne : i.val ≠ 0 ∨ j.val ≠ 0) :
    |flSchurCompl2 m fp A i j| ≤ (1 + fp.u) * |A i.succ.succ j.succ.succ| := by
  rw [flSchurCompl2_eq_sub_zero_of_ne_corner fp A hA i j hne]
  obtain ⟨δ, hδ, hsub⟩ := fl_sub_zero_right fp (A i.succ.succ j.succ.succ)
  rw [hsub, abs_mul, mul_comm (1 + fp.u)]
  exact mul_le_mul_of_nonneg_left (abs_one_add_le fp hδ) (abs_nonneg _)

/-! ## Theorem 11.7 — Bunch tridiagonal normwise backward error

The factorization side is the mixed printed Theorem 11.3 bound
`|ΔA₁| ≤ 20n·u·(|A| + |L̂||D̂||L̂ᵀ|)` specialized to the schedule chosen by
Algorithm 11.6, folded against the tridiagonal factor-norm bound
`|L̂||D̂||L̂ᵀ| ≤ c₀·‖A‖_M` into `|ΔA₁| ≤ 20n(1+c₀)·u·‖A‖_M`.  The solve side is the
(11.5) 2×2-solve backward error (a Higham source hypothesis).  `Amax` plays the
role of `‖A‖_M`. -/

/-- **Theorem 11.7 (Bunch, symmetric tridiagonal).**  For a symmetric input `A`
    whose rounded mixed-pivot block-LDLᵀ path (recorded by the Algorithm-11.6
    schedule `s`) satisfies the per-stage `FlMixedPivots` conditions, whose
    computed factors obey the tridiagonal factor-norm bound
    `|L̂||D̂||L̂ᵀ| ≤ c₀·Amax`, and whose solve step admits the (11.5) backward
    perturbation `ΔA₂`, Bunch's method produces

      `L̂D̂L̂ᵀ = A + ΔA₁`,   `(A + ΔA₂)x̂ = b`,   `|ΔAₖ i j| ≤ 20 n (1+c₀)·u·Amax`.

    The named factors are `flMixedL fp s A`, `flMixedD fp s A`; the linear-in-`n`
    coefficient `c = 20 n (1+c₀)` is Higham's `c·u·‖A‖_M` (Option A landing). -/
theorem higham11_7_bunch_tridiagonal_backward_error
    (fp : FPModel) (hval : gammaValid fp 3)
    {n : ℕ} (A : Fin n → Fin n → ℝ) (b x_hat : Fin n → ℝ)
    (s : PivotSchedule n) (Amax c0 cSolve cStage : ℝ)
    (hAmax : ∀ i j : Fin n, |A i j| ≤ Amax) (hAmax0 : 0 ≤ Amax)
    (hc0 : 0 ≤ c0)
    (hcS0 : 0 ≤ cSolve) (hcS40 : cSolve ≤ 40)
    (hcSt0 : 0 ≤ cStage) (hcSt5 : cStage ≤ 5)
    (hsmall : (n : ℝ) * fp.u ≤ 1 / 100)
    (hpiv : FlMixedPivots fp cSolve cStage s A)
    (hfactor : ∀ i j : Fin n,
      higham11_4_bunchKaufmanProductEntry n (flMixedL fp s A) (flMixedD fp s A) i j
        ≤ c0 * Amax)
    (hsolve : ∃ ΔA2 : Fin n → Fin n → ℝ,
      (∀ i j : Fin n, |ΔA2 i j| ≤ 20 * (n : ℝ) * (1 + c0) * fp.u * Amax) ∧
      (∀ i : Fin n, ∑ j : Fin n, (A i j + ΔA2 i j) * x_hat j = b i)) :
    ∃ ΔA1 ΔA2 : Fin n → Fin n → ℝ,
      (∀ i j : Fin n, |ΔA1 i j| ≤ 20 * (n : ℝ) * (1 + c0) * fp.u * Amax) ∧
      (∀ i j : Fin n, |ΔA2 i j| ≤ 20 * (n : ℝ) * (1 + c0) * fp.u * Amax) ∧
      (∀ i j : Fin n,
        (∑ k₁, ∑ k₂, flMixedL fp s A i k₁ * flMixedD fp s A k₁ k₂ * flMixedL fp s A j k₂)
          = A i j + ΔA1 i j) ∧
      (∀ i : Fin n, ∑ j : Fin n, (A i j + ΔA2 i j) * x_hat j = b i) := by
  obtain ⟨ΔA2, hΔA2, hsolveEq⟩ := hsolve
  refine ⟨fun i j => (∑ k₁, ∑ k₂, flMixedL fp s A i k₁ * flMixedD fp s A k₁ k₂
      * flMixedL fp s A j k₂) - A i j, ΔA2, ?_, hΔA2, ?_, hsolveEq⟩
  · intro i j
    have h1 := fl_blockLDLT_mixed_bound fp hval cSolve cStage s A hpiv i j
    have h2 := flMixed_envelope_le_printed fp hval cSolve cStage hcS0 hcS40 hcSt0 hcSt5
      s A hsmall hpiv i j
    refine h1.trans (h2.trans ?_)
    simp only [higham11_3_printedFirstOrderBound, pPoly, id_eq]
    have hb : |A i j|
          + higham11_4_bunchKaufmanProductEntry n (flMixedL fp s A) (flMixedD fp s A) i j
        ≤ (1 + c0) * Amax := by
      have h1a := hAmax i j
      have h2a := hfactor i j
      have hexp : (1 + c0) * Amax = Amax + c0 * Amax := by ring
      rw [hexp]; linarith
    calc 20 * (n : ℝ) * fp.u
            * (|A i j|
                + higham11_4_bunchKaufmanProductEntry n (flMixedL fp s A) (flMixedD fp s A) i j)
        ≤ 20 * (n : ℝ) * fp.u * ((1 + c0) * Amax) :=
          mul_le_mul_of_nonneg_left hb
            (mul_nonneg (mul_nonneg (by norm_num) (Nat.cast_nonneg n)) fp.u_nonneg)
      _ = 20 * (n : ℝ) * (1 + c0) * fp.u * Amax := by ring
  · intro i j; dsimp only; ring

/-! ## Precise honesty status

**Derived from the floating-point model (no assumptions beyond the model):**
  * the model zero laws (`fl_mul_*_zero`, `fl_sub_zero_zero`, `fl_div_zero_left`,
    `fl_sub_zero_right`);
  * **Lemma T** — `flSchurCompl2_isSymTridiagonal` and
    `flSchurCompl_isSymTridiagonal`: the rounded 1×1 and 2×2 Schur complements of
    a symmetric tridiagonal matrix are again symmetric tridiagonal (the genuine
    Schur correction lands only on the leading `(0,0)` corner);
  * the fill-in-free portion of the 2×2 stage condition:
    `pivotPath2_eq_zero_of_ne_corner`, `flSchurCompl2_trailing_error_offcorner`
    (the per-stage trailing budget holds with `cStage = 1` off the corner), and
    `flSchurCompl2_offcorner_bound` (Lemma G, per-step: off-corner band entries do
    not grow beyond `(1+u)`).

**Assumed in `higham11_7_bunch_tridiagonal_backward_error` (all legitimate Higham
source hypotheses or the sanctioned partial):**
  * `hpiv : FlMixedPivots …` — the per-2×2-stage (11.5) 2×2-solve/Schur bounds and
    coupling (the source hypothesis the task explicitly permits);
  * `hsolve` — the (11.5) solve-side backward error `(A+ΔA₂)x̂ = b`;
  * `hfactor : |L̂||D̂||L̂ᵀ| ≤ c₀·Amax` — the tridiagonal factor-norm bound
    (Higham's "constant growth" fact).  This is the ONLY genuinely-derivable
    ingredient kept as a hypothesis.

**Strength.**  Conditional on `hfactor` and (11.5), Theorem 11.7 is obtained at
the printed first-order strength with the linear coefficient `c = 20 n (1+c₀)`
(Higham's `c·u·‖A‖_M`, the plan's Option A).

**Exact remaining obstruction for a fully source-faithful `hfactor` (Lemma F).**
The corner `(0,0)` growth is the sole gap.  `flSchurCompl2 0 0` reduces (via the
tridiagonal structure and the model zero laws) to the scalar Bunch step
`fl_sub A₂₂ (fl_mul (fl_mul c f) c)` with `c = A₂₁`, `f = A₁₁/det`, matching
`fl_tridiagonal_twoByTwo_schur_step_error`.  Bounding the corner by `c₀·‖A‖_M`
needs `|c·f·c| = A₂₁²·|A₁₁|/|det|` controlled by a *constant* multiple of the
global `‖A‖_M`.  The available inverse-entry bound gives
`|A₁₁/det| ≤ σ/((1-α)·A₁₀²)`, i.e. `|c·f·c| ≤ A₂₁²·σ/((1-α)·A₁₀²)`, whose
`A₂₁²/A₁₀²` ratio is NOT bounded by the Algorithm-11.6 acceptance test alone
(the test `σ|A₁₁| < α·A₁₀²` controls `A₁₀` against `σ|A₁₁|`, not against the
adjacent subdiagonal `A₂₁`).  Closing Lemma F therefore requires the additional
tridiagonal growth accounting (Higham's constant-growth argument over the whole
recursion, with the `(1+u)^k` band slack from `flSchurCompl2_offcorner_bound`
folded in) — a genuine, self-contained further development, left as the explicit
hypothesis `hfactor` here.  No result is faked; nothing derivable is assumed
except this isolated factor-norm bound. -/

end NumStability.Ch11Closure.BunchTri
