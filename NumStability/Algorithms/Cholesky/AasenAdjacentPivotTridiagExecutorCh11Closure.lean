/-
Algorithms/Cholesky/AasenAdjacentPivotTridiagExecutorCh11Closure.lean

A literal support-aware adjacent-pivot tridiagonal factor/solve executor.  The
storage and updates follow the DGTTRF/DGTTRS organization: `dl`, `d`, `du`, and
`du2` store the multiplier, diagonal, first superdiagonal, and pivot fill; a
Boolean records whether the adjacent interchange was taken.  Structural zero
updates use `skipZeroSubFP`, so they are copies rather than charged rounded
subtractions in the abstract model.

The unconditional development stops at the operational and local-arithmetic
layer.  It does not assume a target-shaped factorization residual.  The public
`DGTTRFNoBreakdown` predicate mentions only pivots encountered by the computed
run and the final computed diagonal.  A final conditional composition records
the exact global `gamma_1` forward premise that the printed `gamma_6` argument
would need; `AasenAdjacentPivotTridiagForwardCounterexampleCh11` proves that
premise false in general after consecutive adjacent pivots.
-/
import NumStability.Algorithms.Cholesky.BunchTridiagonalSparseFactorCh11Closure
import NumStability.Analysis.ComplexArithmetic

open scoped BigOperators

namespace NumStability.Ch11Closure.AasenAdjacentGEPP

open NumStability
open NumStability.Ch11Closure
open NumStability.Ch11Closure.SparseFactor
open NumStability.Ch11Closure.SparseSolve

/-! ## Finite functional storage -/

/-- Replace one entry of a finite functional vector. -/
def finReplace {n : ℕ} (x : Fin n → α) (i : Fin n) (a : α) : Fin n → α :=
  fun j => if j = i then a else x j

@[simp] theorem finReplace_same {n : ℕ} (x : Fin n → α) (i : Fin n) (a : α) :
    finReplace x i a i = a := by simp [finReplace]

@[simp] theorem finReplace_of_ne {n : ℕ} (x : Fin n → α) (i j : Fin n) (a : α)
    (h : j ≠ i) : finReplace x i a j = x j := by simp [finReplace, h]

/-- Interchange two entries of a finite functional vector. -/
def finSwap {n : ℕ} (x : Fin n → α) (i j : Fin n) : Fin n → α :=
  fun k => if k = i then x j else if k = j then x i else x k

@[simp] theorem finSwap_left {n : ℕ} (x : Fin n → α) (i j : Fin n) :
    finSwap x i j i = x j := by simp [finSwap]

@[simp] theorem finSwap_right {n : ℕ} (x : Fin n → α) (i j : Fin n) (h : j ≠ i) :
    finSwap x i j j = x i := by simp [finSwap, h]

/-- DGTTRF-style tridiagonal factor storage.  The last entries of `dl`, `du`,
and `du2` are padding.  `ipiv i = true` means that rows `i` and `i+1` were
interchanged at stage `i`; `perm` records the accumulated row labels. -/
structure DGTTRFData (n : ℕ) where
  dl : Fin n → ℝ
  d : Fin n → ℝ
  du : Fin n → ℝ
  du2 : Fin n → ℝ
  ipiv : Fin n → Bool
  perm : Fin n → Fin n

/-- Initial DGTTRF storage obtained by reading the three diagonals of `T`. -/
noncomputable def dgttrfInit (n : ℕ) (T : Fin n → Fin n → ℝ) : DGTTRFData n where
  dl := fun i => if h : i.val + 1 < n then T ⟨i.val + 1, h⟩ i else 0
  d := fun i => T i i
  du := fun i => if h : i.val + 1 < n then T i ⟨i.val + 1, h⟩ else 0
  du2 := fun _ => 0
  ipiv := fun _ => false
  perm := id

/-! ## Literal adjacent-pivot factorization -/

/-- One support-aware DGTTRF step at `k`, where `k+1` exists.

The no-interchange branch performs
`m = fl(dl/d)` and `dnext = fl(dnext - fl(m*du))`.
The interchange branch exposes the old next row as the pivot row and stores the
second-superdiagonal fill exactly as in DGTTRF. -/
noncomputable def flDGTTRFStepAt (fp : FPModel) {n : ℕ} (s : DGTTRFData n)
    (k : Fin n) (hk : k.val + 1 < n) : DGTTRFData n :=
  let kp : Fin n := ⟨k.val + 1, hk⟩
  let q := skipZeroSubFP fp
  if _hchoice : |s.d k| ≥ |s.dl k| then
    let m := q.fl_div (s.dl k) (s.d k)
    let dn := q.fl_sub (s.d kp) (q.fl_mul m (s.du k))
    { s with
      dl := finReplace s.dl k m
      d := finReplace s.d kp dn
      ipiv := finReplace s.ipiv k false }
  else
    let m := q.fl_div (s.d k) (s.dl k)
    let dn := q.fl_sub (s.du k) (q.fl_mul m (s.d kp))
    let dun := q.fl_mul (-m) (s.du kp)
    { s with
      dl := finReplace s.dl k m
      d := finReplace (finReplace s.d k (s.dl k)) kp dn
      du := finReplace (finReplace s.du k (s.d kp)) kp dun
      du2 := finReplace s.du2 k (s.du kp)
      ipiv := finReplace s.ipiv k true
      perm := finSwap s.perm k kp }

/-- State after the first `steps` adjacent-pivot stages.  Requests beyond the
available `n-1` stages are inert, which makes the recursion total at `n=0`. -/
noncomputable def flDGTTRFRun (fp : FPModel) (n : ℕ)
    (T : Fin n → Fin n → ℝ) : ℕ → DGTTRFData n
  | 0 => dgttrfInit n T
  | k + 1 =>
      let s := flDGTTRFRun fp n T k
      if hk : k + 1 < n then
        flDGTTRFStepAt fp s
          ⟨k, Nat.lt_trans (Nat.lt_succ_self k) hk⟩ hk
      else s

/-- Completed literal DGTTRF run. -/
noncomputable def flDGTTRF (fp : FPModel) (n : ℕ)
    (T : Fin n → Fin n → ℝ) : DGTTRFData n :=
  flDGTTRFRun fp n T (n - 1)

/-- The selected pivot at every executed stage is nonzero. -/
def DGTTRFStepPivotsNonzero (fp : FPModel) (n : ℕ)
    (T : Fin n → Fin n → ℝ) : Prop :=
  ∀ (k : ℕ) (hk : k + 1 < n),
    let s := flDGTTRFRun fp n T k
    let i : Fin n := ⟨k, Nat.lt_trans (Nat.lt_succ_self k) hk⟩
    if |s.d i| ≥ |s.dl i| then s.d i ≠ 0 else s.dl i ≠ 0

/-- Operational no-breakdown condition.  This predicate is intentionally
restricted to the computed pivot path and final computed upper diagonal; it
contains no residual, perturbation, solution, or desired conclusion. -/
def DGTTRFNoBreakdown (fp : FPModel) {n : ℕ}
    (T : Fin n → Fin n → ℝ) : Prop :=
  DGTTRFStepPivotsNonzero fp n T ∧
    ∀ i : Fin n, (flDGTTRF fp n T).d i ≠ 0

/-! ## Matrix views of the stored factors -/

/-- Unit lower-bidiagonal view of the stored multipliers.  With pivoting this
is a storage view, not an assertion that all interchanges commute past it. -/
def dgttrfL {n : ℕ} (s : DGTTRFData n) : Fin n → Fin n → ℝ :=
  fun i j => if i = j then 1 else if i.val = j.val + 1 then s.dl j else 0

/-- Upper bandwidth-two matrix represented by `d`, `du`, and `du2`. -/
def dgttrfU {n : ℕ} (s : DGTTRFData n) : Fin n → Fin n → ℝ :=
  fun i j =>
    if i = j then s.d i
    else if j.val = i.val + 1 then s.du i
    else if j.val = i.val + 2 then s.du2 i
    else 0

/-- Matrix view of the accumulated row labels. -/
def dgttrfP {n : ℕ} (s : DGTTRFData n) : Fin n → Fin n → ℝ :=
  fun i j => if s.perm i = j then 1 else 0

@[simp] theorem dgttrfL_diag {n : ℕ} (s : DGTTRFData n) (i : Fin n) :
    dgttrfL s i i = 1 := by simp [dgttrfL]

theorem dgttrfL_upper_zero {n : ℕ} (s : DGTTRFData n) (i j : Fin n)
    (hij : i.val < j.val) : dgttrfL s i j = 0 := by
  simp only [dgttrfL]
  split <;> rename_i h
  · subst j; omega
  · split <;> rename_i h'
    · omega
    · rfl

theorem dgttrfL_bandwidth_one {n : ℕ} (s : DGTTRFData n) (i j : Fin n)
    (hij : j.val + 1 < i.val) : dgttrfL s i j = 0 := by
  simp only [dgttrfL]
  split <;> rename_i h
  · subst j; omega
  · split <;> rename_i h'
    · omega
    · rfl

@[simp] theorem dgttrfU_diag {n : ℕ} (s : DGTTRFData n) (i : Fin n) :
    dgttrfU s i i = s.d i := by simp [dgttrfU]

theorem dgttrfU_lower_zero {n : ℕ} (s : DGTTRFData n) (i j : Fin n)
    (hji : j.val < i.val) : dgttrfU s i j = 0 := by
  simp only [dgttrfU]
  split <;> rename_i h
  · subst j; omega
  · split <;> rename_i h'
    · omega
    · split <;> rename_i h''
      · omega
      · rfl

theorem dgttrfU_bandwidth_two {n : ℕ} (s : DGTTRFData n) (i j : Fin n)
    (hij : i.val + 2 < j.val) : dgttrfU s i j = 0 := by
  simp only [dgttrfU]
  split <;> rename_i h
  · subst j; omega
  · split <;> rename_i h'
    · omega
    · split <;> rename_i h''
      · omega
      · rfl

/-! ## Accumulated adjacent-pivot `P`, `M`, and the actual source envelope -/

/-- Accumulated row permutation reconstructed from the stored adjacent pivot
bits.  Its value maps a current factor row to its source row.  Packaging it as
an equivalence makes the `Pᵀ` pullback used by the source perturbation budget
available without a separate bijectivity hypothesis. -/
def dgttrfPermEquivRun {n : ℕ} (s : DGTTRFData n) : ℕ → (Fin n ≃ Fin n)
  | 0 => Equiv.refl (Fin n)
  | k + 1 =>
      let p := dgttrfPermEquivRun s k
      if hk : k + 1 < n then
        let i : Fin n := ⟨k, Nat.lt_trans (Nat.lt_succ_self k) hk⟩
        let ip : Fin n := ⟨k + 1, hk⟩
        if s.ipiv i then (Equiv.swap i ip).trans p else p
      else p

/-- Completed accumulated adjacent row permutation. -/
def dgttrfPermEquiv {n : ℕ} (s : DGTTRFData n) : Fin n ≃ Fin n :=
  dgttrfPermEquivRun s (n - 1)

/-- Matrix of the accumulated pivot permutation reconstructed from `ipiv`. -/
def dgttrfPivotP {n : ℕ} (s : DGTTRFData n) : Fin n → Fin n → ℝ :=
  fun i j => if dgttrfPermEquiv s i = j then 1 else 0

/-- Identity starting point for the conventional accumulated lower factor. -/
def dgttrfMInit (n : ℕ) : Fin n → Fin n → ℝ :=
  fun i j => if i = j then 1 else 0

/-- One conventional accumulated-lower update.  On a pivot, only the already
formed prefix columns are interchanged; the new multiplier is then written at
`(k+1,k)`.  This is the standard accumulated `M` corresponding to DGTTRF's
interleaved storage, and is distinct from the bidiagonal storage view
`dgttrfL`. -/
def dgttrfMStepAt {n : ℕ} (s : DGTTRFData n)
    (M : Fin n → Fin n → ℝ) (k : Fin n) (hk : k.val + 1 < n) :
    Fin n → Fin n → ℝ :=
  let kp : Fin n := ⟨k.val + 1, hk⟩
  let Mswap : Fin n → Fin n → ℝ :=
    if s.ipiv k then
      fun i j =>
        if j.val < k.val then
          if i = k then M kp j else if i = kp then M k j else M i j
        else M i j
    else M
  fun i j => if i = kp ∧ j = k then s.dl k else Mswap i j

/-- Accumulated lower factor after the first `steps` stored stages. -/
def dgttrfMRun {n : ℕ} (s : DGTTRFData n) : ℕ → Fin n → Fin n → ℝ
  | 0 => dgttrfMInit n
  | k + 1 =>
      let M := dgttrfMRun s k
      if hk : k + 1 < n then
        dgttrfMStepAt s M
          ⟨k, Nat.lt_trans (Nat.lt_succ_self k) hk⟩ hk
      else M

/-- Conventional accumulated lower factor represented by the actual stored
pivot decisions and computed multipliers. -/
def dgttrfM {n : ℕ} (s : DGTTRFData n) : Fin n → Fin n → ℝ :=
  dgttrfMRun s (n - 1)

/-- The actual nonnegative `|M||U|` envelope in factor row order. -/
noncomputable def dgttrfMUEnvelope {n : ℕ} (s : DGTTRFData n) :
    Fin n → Fin n → ℝ :=
  fun i j => ∑ k : Fin n, |dgttrfM s i k| * |dgttrfU s k j|

/-- The source-ordered envelope `Pᵀ |M| |U|` required by Higham's printed
componentwise middle-solve bound. -/
noncomputable def dgttrfSourceEnvelope {n : ℕ} (s : DGTTRFData n) :
    Fin n → Fin n → ℝ :=
  fun i j => dgttrfMUEnvelope s ((dgttrfPermEquiv s).symm i) j

theorem dgttrfMUEnvelope_nonneg {n : ℕ} (s : DGTTRFData n) (i j : Fin n) :
    0 ≤ dgttrfMUEnvelope s i j := by
  exact Finset.sum_nonneg fun k _ =>
    mul_nonneg (abs_nonneg _) (abs_nonneg _)

theorem dgttrfSourceEnvelope_nonneg {n : ℕ} (s : DGTTRFData n)
    (i j : Fin n) : 0 ≤ dgttrfSourceEnvelope s i j :=
  dgttrfMUEnvelope_nonneg s ((dgttrfPermEquiv s).symm i) j

/-- Computed factor residual in factor-row order.  This definition is an
observable of the executable state, not an extra hypothesis. -/
noncomputable def dgttrfFactorResidual {n : ℕ}
    (T : Fin n → Fin n → ℝ) (s : DGTTRFData n) : Fin n → Fin n → ℝ :=
  fun i j =>
    (∑ k : Fin n, dgttrfM s i k * dgttrfU s k j) -
      T (dgttrfPermEquiv s i) j

/-- Definitional factor equation for the executable residual observable. -/
theorem dgttrfFactorResidual_equation {n : ℕ}
    (T : Fin n → Fin n → ℝ) (s : DGTTRFData n) (i j : Fin n) :
    ∑ k : Fin n, dgttrfM s i k * dgttrfU s k j =
      T (dgttrfPermEquiv s i) j + dgttrfFactorResidual T s i j := by
  simp only [dgttrfFactorResidual]
  ring

/-! ## Literal DGTTRS forward and backward sweeps -/

/-- One DGTTRS forward stage.  In the interchange branch the two RHS entries
are swapped while the eliminated entry is formed from their old values. -/
noncomputable def flDGTTRSForwardStepAt (fp : FPModel) {n : ℕ}
    (s : DGTTRFData n) (x : Fin n → ℝ) (k : Fin n)
    (hk : k.val + 1 < n) : Fin n → ℝ :=
  let kp : Fin n := ⟨k.val + 1, hk⟩
  let q := skipZeroSubFP fp
  if s.ipiv k then
    let tail := q.fl_sub (x k) (q.fl_mul (s.dl k) (x kp))
    finReplace (finReplace x k (x kp)) kp tail
  else
    finReplace x kp (q.fl_sub (x kp) (q.fl_mul (s.dl k) (x k)))

/-- State after the first `steps` DGTTRS forward stages. -/
noncomputable def flDGTTRSForwardRun (fp : FPModel) {n : ℕ}
    (s : DGTTRFData n) (z : Fin n → ℝ) : ℕ → Fin n → ℝ
  | 0 => z
  | k + 1 =>
      let x := flDGTTRSForwardRun fp s z k
      if hk : k + 1 < n then
        flDGTTRSForwardStepAt fp s x
          ⟨k, Nat.lt_trans (Nat.lt_succ_self k) hk⟩ hk
      else x

/-- Completed interleaved adjacent-permutation/unit-lower forward sweep. -/
noncomputable def flDGTTRSForward (fp : FPModel) {n : ℕ}
    (s : DGTTRFData n) (z : Fin n → ℝ) : Fin n → ℝ :=
  flDGTTRSForwardRun fp s z (n - 1)

/-- Support-aware bandwidth-two back solve against the stored upper factor. -/
noncomputable def flDGTTRSBackward (fp : FPModel) {n : ℕ}
    (s : DGTTRFData n) (q : Fin n → ℝ) : Fin n → ℝ :=
  flBand2BackSub (skipZeroSubFP fp) n (dgttrfU s) q

/-- Complete DGTTRF/DGTTRS tridiagonal solve. -/
noncomputable def flDGTTRS (fp : FPModel) (n : ℕ)
    (T : Fin n → Fin n → ℝ) (z : Fin n → ℝ) : Fin n → ℝ :=
  let s := flDGTTRF fp n T
  flDGTTRSBackward fp s (flDGTTRSForward fp s z)

/-- The concrete stored upper solve inherits the dimension-independent
bandwidth-two `gamma_3` componentwise backward error. -/
theorem flDGTTRSBackward_backward_error (fp : FPModel) {n : ℕ}
    (s : DGTTRFData n) (q : Fin n → ℝ)
    (hdiag : ∀ i : Fin n, s.d i ≠ 0)
    (hval3 : gammaValid fp 3) :
    ∃ ΔU : Fin n → Fin n → ℝ,
      (∀ i j, |ΔU i j| ≤ gamma fp 3 * |dgttrfU s i j|) ∧
      ∀ i, ∑ j : Fin n,
        (dgttrfU s i j + ΔU i j) * flDGTTRSBackward fp s q j = q i := by
  have hval3' : gammaValid (skipZeroSubFP fp) 3 := by
    simpa [gammaValid] using hval3
  obtain ⟨ΔU, hΔU, heq⟩ :=
    flBand2BackSub_backward_error (skipZeroSubFP fp) n (dgttrfU s) q
      (by simpa using hdiag)
      (dgttrfU_lower_zero s) (dgttrfU_bandwidth_two s) hval3'
  refine ⟨ΔU, ?_, ?_⟩
  · intro i j
    simpa [gamma] using hΔU i j
  · intro i
    simpa [flDGTTRSBackward] using heq i

/-! ## Local scalar arithmetic used by both pivot branches -/

/-- Rounded multiplier used by DGTTRF. -/
noncomputable def flDGTTRFMultiplier (fp : FPModel) (a pivot : ℝ) : ℝ :=
  (skipZeroSubFP fp).fl_div a pivot

/-- Rounded Schur/update scalar used by both DGTTRF and DGTTRS. -/
noncomputable def flDGTTRFUpdate (fp : FPModel) (a m x : ℝ) : ℝ :=
  (skipZeroSubFP fp).fl_sub a
    ((skipZeroSubFP fp).fl_mul m x)

/-- Rounded `-m*x` fill generated by an interchange. -/
noncomputable def flDGTTRFNegMul (fp : FPModel) (m x : ℝ) : ℝ :=
  (skipZeroSubFP fp).fl_mul (-m) x

/-- A computed multiplier has the literal one-operation relative-error
certificate, expressed with the original model's unit roundoff. -/
theorem flDGTTRFMultiplier_relative (fp : FPModel) (a pivot : ℝ)
    (hpivot : pivot ≠ 0) :
    ∃ δ : ℝ, |δ| ≤ fp.u ∧
      flDGTTRFMultiplier fp a pivot = (a / pivot) * (1 + δ) := by
  simpa [flDGTTRFMultiplier] using
    (skipZeroSubFP fp).model_div a pivot hpivot

/-- The divide/multiply/subtract update has Higham's local `gamma_3` error. -/
theorem flDGTTRFUpdate_div_error_le_gamma3 (fp : FPModel)
    (hval3 : gammaValid fp 3) (a b c pivot : ℝ) (hpivot : pivot ≠ 0) :
    |flDGTTRFUpdate fp a b (flDGTTRFMultiplier fp c pivot) -
        (a - b * (c / pivot))| ≤
      gamma fp 3 * (|a| + |b * (c / pivot)|) := by
  have hval3' : gammaValid (skipZeroSubFP fp) 3 := by
    simpa [gammaValid] using hval3
  simpa [flDGTTRFUpdate, flDGTTRFMultiplier, gamma] using
    (fl_sub_mul_div_error_le_gamma3 (skipZeroSubFP fp) hval3' a b c pivot hpivot)

/-- A support-aware multiply/subtract update with an already computed
multiplier costs two rounded operations. -/
theorem flDGTTRFUpdate_error_le_gamma2 (fp : FPModel)
    (hval2 : gammaValid fp 2) (a m x : ℝ) :
    |flDGTTRFUpdate fp a m x - (a - m * x)| ≤
      gamma fp 2 * (|a| + |m| * |x|) := by
  let q := skipZeroSubFP fp
  have hval2' : gammaValid q 2 := by simpa [q, gammaValid] using hval2
  have hval1 : gammaValid q 1 :=
    gammaValid_mono q (show 1 ≤ 2 by omega) hval2'
  obtain ⟨δm, hδm, hmul⟩ := q.model_mul m x
  obtain ⟨δs, hδs, hsub⟩ := q.model_sub a (q.fl_mul m x)
  have hδm1 : |δm| ≤ gamma q 1 :=
    le_trans hδm (u_le_gamma q (by omega) hval1)
  have hδs1 : |δs| ≤ gamma q 1 :=
    le_trans hδs (u_le_gamma q (by omega) hval1)
  obtain ⟨θ, hθ, hθeq⟩ :=
    gamma_mul q 1 1 δm δs hδm1 hδs1 (by simpa using hval2')
  have hδs2 : |δs| ≤ gamma q 2 :=
    le_trans hδs1 (gamma_mono q (by omega) hval2')
  have hrewrite :
      flDGTTRFUpdate fp a m x - (a - m * x) = a * δs - m * x * θ := by
    change q.fl_sub a (q.fl_mul m x) - (a - m * x) = _
    rw [hsub, hmul]
    have hθ' : θ = (1 + δm) * (1 + δs) - 1 := by linarith [hθeq]
    rw [hθ']
    ring
  rw [hrewrite]
  calc
    |a * δs - m * x * θ| ≤ |a * δs| + |m * x * θ| := by
      simpa [sub_eq_add_neg, abs_neg] using abs_add_le (a * δs) (-(m * x * θ))
    _ = |a| * |δs| + |m| * |x| * |θ| := by
      rw [abs_mul, abs_mul, abs_mul]
    _ ≤ |a| * gamma q 2 + |m| * |x| * gamma q 2 := by
      exact add_le_add
        (mul_le_mul_of_nonneg_left hδs2 (abs_nonneg _))
        (mul_le_mul_of_nonneg_left hθ
          (mul_nonneg (abs_nonneg _) (abs_nonneg _)))
    _ = gamma fp 2 * (|a| + |m| * |x|) := by
      simp [q, gamma]
      ring

/-- Coefficientwise backward form of one DGTTRS forward update.

Writing `t = fl(a - fl(m*x))`, there are perturbations of the retained unit
coefficient and of `m`, both bounded by `gamma_1`, for which
`(1+phiDiag)t + m(1+phiMul)x = a` exactly.  This is sharper than treating the
forward sweep as a dense triangular solve.  It is only a one-stage statement:
consecutive interchanges carry an accumulator through multiple such stages,
so it does not globalize to `|DeltaM| <= gamma_1 |M|`. -/
theorem flDGTTRFUpdate_backward_coefficients_gamma1 (fp : FPModel)
    (hval2 : gammaValid fp 2) (a m x : ℝ) :
    ∃ phiDiag phiMul : ℝ,
      |phiDiag| ≤ gamma fp 1 ∧
      |phiMul| ≤ gamma fp 1 ∧
      (1 + phiDiag) * flDGTTRFUpdate fp a m x +
          m * (1 + phiMul) * x = a := by
  let q := skipZeroSubFP fp
  have hval2q : gammaValid q 2 := by simpa [q, gammaValid] using hval2
  have hval1q : gammaValid q 1 :=
    gammaValid_mono q (show 1 ≤ 2 by omega) hval2q
  obtain ⟨deltaMul, hdeltaMul, hmul⟩ := q.model_mul m x
  obtain ⟨deltaSub, hdeltaSub, hsub⟩ := q.model_sub a (q.fl_mul m x)
  have hu1 : q.u < 1 := by
    simpa [gammaValid] using hval1q
  have hdeltaSub_lt : |deltaSub| < 1 := lt_of_le_of_lt hdeltaSub hu1
  have hpos : 0 < 1 + deltaSub := by
    have hlo : -1 < deltaSub := (abs_lt.mp hdeltaSub_lt).1
    linarith
  have hgamma_nonneg : 0 ≤ gamma q 1 := gamma_nonneg q hval1q
  have hden_ne : (1 : ℝ) - q.u ≠ 0 := by linarith
  have hgamma_eq : gamma q 1 * (1 - q.u) = q.u := by
    unfold gamma
    rw [Nat.cast_one, one_mul]
    field_simp
  let phiDiag : ℝ := -deltaSub / (1 + deltaSub)
  have hphiDiag_def : phiDiag = -deltaSub / (1 + deltaSub) := rfl
  have hphiDiag : |phiDiag| ≤ gamma q 1 := by
    rw [hphiDiag_def, abs_div, abs_neg, abs_of_pos hpos, div_le_iff₀ hpos]
    have hkey : |deltaSub| ≤ gamma q 1 * (1 + deltaSub) := by
      have hlow : 1 - q.u ≤ 1 + deltaSub := by
        have := (abs_le.mp hdeltaSub).1
        linarith
      have hscaled : gamma q 1 * (1 - q.u) ≤
          gamma q 1 * (1 + deltaSub) :=
        mul_le_mul_of_nonneg_left hlow hgamma_nonneg
      calc
        |deltaSub| ≤ q.u := hdeltaSub
        _ = gamma q 1 * (1 - q.u) := hgamma_eq.symm
        _ ≤ gamma q 1 * (1 + deltaSub) := hscaled
    exact hkey
  have hphiMul : |deltaMul| ≤ gamma q 1 :=
    le_trans hdeltaMul (u_le_gamma q (by omega) hval1q)
  refine ⟨phiDiag, deltaMul, ?_, ?_, ?_⟩
  · simpa [q, gamma] using hphiDiag
  · simpa [q, gamma] using hphiMul
  · change (1 + phiDiag) * q.fl_sub a (q.fl_mul m x) +
        m * (1 + deltaMul) * x = a
    rw [hsub, hmul]
    rw [hphiDiag_def]
    field_simp [ne_of_gt hpos]
    ring

/-- The interchange fill `fl(-m*x)` has a one-operation absolute residual. -/
theorem flDGTTRFNegMul_residual_le_u (fp : FPModel) (m x : ℝ) :
    |m * x + flDGTTRFNegMul fp m x| ≤ fp.u * |m| * |x| := by
  obtain ⟨δ, hδ, hmul⟩ := (skipZeroSubFP fp).model_mul (-m) x
  rw [flDGTTRFNegMul, hmul]
  have heq : m * x + ((-m) * x) * (1 + δ) = -(m * x * δ) := by ring
  rw [heq, abs_neg, abs_mul, abs_mul]
  have h := mul_le_mul_of_nonneg_left hδ (abs_nonneg (m * x))
  simpa [mul_assoc, mul_left_comm, mul_comm] using h

/-! ## One-step factor residuals -/

/-- Pivot-column residual in either branch: multiplying the rounded multiplier
back by its nonzero pivot perturbs the eliminated entry by at most one `u`. -/
theorem flDGTTRF_multiplier_pivot_residual_le_u (fp : FPModel)
    (a pivot : ℝ) (hpivot : pivot ≠ 0) :
    |flDGTTRFMultiplier fp a pivot * pivot - a| ≤ fp.u * |a| := by
  obtain ⟨δ, hδ, hm⟩ := flDGTTRFMultiplier_relative fp a pivot hpivot
  rw [hm]
  have hdiv : a / pivot * pivot = a := div_mul_cancel₀ a hpivot
  have heq : (a / pivot * (1 + δ)) * pivot - a = a * δ := by
    calc
      (a / pivot * (1 + δ)) * pivot - a
          = (a / pivot * pivot) * (1 + δ) - a := by ring
      _ = a * δ := by rw [hdiv]; ring
  rw [heq, abs_mul]
  simpa [mul_comm] using mul_le_mul_of_nonneg_left hδ (abs_nonneg a)

/-- No-interchange local diagonal equation. -/
theorem flDGTTRF_noSwap_diag_residual_le_gamma2 (fp : FPModel)
    (hval2 : gammaValid fp 2) (dnext m du : ℝ) :
    |m * du + flDGTTRFUpdate fp dnext m du - dnext| ≤
      gamma fp 2 * (|dnext| + |m| * |du|) := by
  have h := flDGTTRFUpdate_error_le_gamma2 fp hval2 dnext m du
  have heq : m * du + flDGTTRFUpdate fp dnext m du - dnext =
      flDGTTRFUpdate fp dnext m du - (dnext - m * du) := by ring
  rw [heq]
  exact h

/-- Interchange local diagonal equation; it has the same two-operation update
residual as the no-interchange branch. -/
theorem flDGTTRF_swap_diag_residual_le_gamma2 (fp : FPModel)
    (hval2 : gammaValid fp 2) (du0 m dnext : ℝ) :
    |m * dnext + flDGTTRFUpdate fp du0 m dnext - du0| ≤
      gamma fp 2 * (|du0| + |m| * |dnext|) :=
  flDGTTRF_noSwap_diag_residual_le_gamma2 fp hval2 du0 m dnext

/-- Interchange second-superdiagonal cancellation residual. -/
theorem flDGTTRF_swap_fill_residual_le_u (fp : FPModel) (m duNext : ℝ) :
    |m * duNext + flDGTTRFNegMul fp m duNext| ≤ fp.u * |m| * |duNext| :=
  flDGTTRFNegMul_residual_le_u fp m duNext

/-- Both DGTTRS forward branches use precisely the same two-operation local
row update; only the two old RHS entries supplied to it differ. -/
theorem flDGTTRS_forward_local_residual_le_gamma2 (fp : FPModel)
    (hval2 : gammaValid fp 2) (oldTarget multiplier oldPivotRhs : ℝ) :
    |flDGTTRFUpdate fp oldTarget multiplier oldPivotRhs -
        (oldTarget - multiplier * oldPivotRhs)| ≤
      gamma fp 2 * (|oldTarget| + |multiplier| * |oldPivotRhs|) :=
  flDGTTRFUpdate_error_le_gamma2 fp hval2 oldTarget multiplier oldPivotRhs

/-! ## Global factor/forward certificate and the `gamma_6` composition -/

/-- The candidate global interface needed by the printed `gamma_6` composition
for the literal DGTTRF factor sweep and interleaved DGTTRS forward sweep.

This proposition is deliberately separate from `DGTTRFNoBreakdown`.  Its
factor residual has coefficient `gamma_2`; its forward coefficient perturbation
has coefficient `gamma_1`, both against the actual accumulated `M` and stored
`U`.  The latter clause is not generally produced by the executable run:
`forwardCounter_not_factor_forward_certificate` gives a dimension-three,
two-consecutive-pivot counterexample. -/
def DGTTRFFactorForwardCertificate (fp : FPModel) (n : ℕ)
    (T : Fin n → Fin n → ℝ) (z : Fin n → ℝ) : Prop :=
  let s := flDGTTRF fp n T
  let M := dgttrfM s
  let U := dgttrfU s
  let p := dgttrfPermEquiv s
  let q := flDGTTRSForward fp s z
  ∃ DeltaF DeltaM : Fin n → Fin n → ℝ,
    (∀ i j : Fin n,
      ∑ k : Fin n, M i k * U k j = T (p i) j + DeltaF i j) ∧
    (∀ i j : Fin n,
      |DeltaF i j| ≤ gamma fp 2 * dgttrfMUEnvelope s i j) ∧
    (∀ i : Fin n,
      ∑ j : Fin n, (M i j + DeltaM i j) * q j = z (p i)) ∧
    (∀ i j : Fin n, |DeltaM i j| ≤ gamma fp 1 * |M i j|)

/-- Conditional algebraic composition of factor `gamma_2`, forward `gamma_1`,
and bandwidth-two backsolve `gamma_3` into a source-ordered
`gamma_6 Pᵀ|M||U|` envelope.

The backsolve certificate is produced here from the literal executor, and all
matrix expansion and gamma absorption are closed.  This theorem is not an
unconditional operational result: its `DGTTRFFactorForwardCertificate` premise
is false in general, as proved in the adjacent-pivot forward-counterexample
module. -/
theorem flDGTTRS_source_backward_error_gamma6_of_factor_forward_certificate
    (fp : FPModel) (n : ℕ) (T : Fin n → Fin n → ℝ) (z : Fin n → ℝ)
    (hnb : DGTTRFNoBreakdown fp T)
    (hcert : DGTTRFFactorForwardCertificate fp n T z)
    (hval6 : gammaValid fp 6) :
    ∃ DeltaT : Fin n → Fin n → ℝ,
      (∀ i j : Fin n,
        |DeltaT i j| ≤ gamma fp 6 *
          dgttrfSourceEnvelope (flDGTTRF fp n T) i j) ∧
      (∀ i : Fin n,
        ∑ j : Fin n, (T i j + DeltaT i j) * flDGTTRS fp n T z j = z i) := by
  let s := flDGTTRF fp n T
  let M := dgttrfM s
  let U := dgttrfU s
  let p := dgttrfPermEquiv s
  let q := flDGTTRSForward fp s z
  let y := flDGTTRSBackward fp s q
  change ∃ DeltaT : Fin n → Fin n → ℝ,
    (∀ i j : Fin n,
      |DeltaT i j| ≤ gamma fp 6 * dgttrfSourceEnvelope s i j) ∧
    (∀ i : Fin n, ∑ j : Fin n, (T i j + DeltaT i j) * y j = z i)
  rcases hcert with ⟨DeltaF, DeltaM, hfactor, hDeltaF, hforward, hDeltaM⟩
  have hval1 : gammaValid fp 1 := gammaValid_mono fp (by omega) hval6
  have hval2 : gammaValid fp 2 := gammaValid_mono fp (by omega) hval6
  have hval3 : gammaValid fp 3 := gammaValid_mono fp (by omega) hval6
  have hval4 : gammaValid fp 4 := gammaValid_mono fp (by omega) hval6
  have hdiag : ∀ i : Fin n, s.d i ≠ 0 := by
    simpa [s] using hnb.2
  obtain ⟨DeltaU, hDeltaU, hback⟩ :=
    flDGTTRSBackward_backward_error fp s q hdiag hval3
  let E : Fin n → Fin n → ℝ := fun i j =>
    DeltaF i j +
      (∑ k : Fin n, M i k * DeltaU k j) +
      (∑ k : Fin n, DeltaM i k * U k j) +
      (∑ k : Fin n, DeltaM i k * DeltaU k j)
  let DeltaT : Fin n → Fin n → ℝ := fun i j => E (p.symm i) j
  have h13 :
      gamma fp 1 + gamma fp 3 + gamma fp 1 * gamma fp 3 ≤ gamma fp 4 := by
    simpa using gamma_sum_le fp 1 3 hval4
  have h24 :
      gamma fp 2 + gamma fp 4 + gamma fp 2 * gamma fp 4 ≤ gamma fp 6 := by
    simpa using gamma_sum_le fp 2 4 hval6
  have hcoeff :
      gamma fp 2 + gamma fp 3 + gamma fp 1 + gamma fp 1 * gamma fp 3 ≤
        gamma fp 6 := by
    have hcross : 0 ≤ gamma fp 2 * gamma fp 4 :=
      mul_nonneg (gamma_nonneg fp hval2) (gamma_nonneg fp hval4)
    linarith
  have hEbound : ∀ i j : Fin n,
      |E i j| ≤ gamma fp 6 * dgttrfMUEnvelope s i j := by
    intro i j
    let W := dgttrfMUEnvelope s i j
    have hW : 0 ≤ W := dgttrfMUEnvelope_nonneg s i j
    have hF : |DeltaF i j| ≤ gamma fp 2 * W := by
      simpa [W, s, M, U, p, q] using hDeltaF i j
    have hMU : |∑ k : Fin n, M i k * DeltaU k j| ≤ gamma fp 3 * W := by
      calc
        |∑ k : Fin n, M i k * DeltaU k j|
            ≤ ∑ k : Fin n, |M i k * DeltaU k j| :=
              Finset.abs_sum_le_sum_abs _ _
        _ = ∑ k : Fin n, |M i k| * |DeltaU k j| := by
              apply Finset.sum_congr rfl
              intro k _
              rw [abs_mul]
        _ ≤ ∑ k : Fin n, |M i k| *
              (gamma fp 3 * |U k j|) := by
              apply Finset.sum_le_sum
              intro k _
              exact mul_le_mul_of_nonneg_left (hDeltaU k j) (abs_nonneg _)
        _ = gamma fp 3 * W := by
              simp only [W, dgttrfMUEnvelope, M, U]
              rw [Finset.mul_sum]
              apply Finset.sum_congr rfl
              intro k _
              ring
    have hDMU : |∑ k : Fin n, DeltaM i k * U k j| ≤ gamma fp 1 * W := by
      calc
        |∑ k : Fin n, DeltaM i k * U k j|
            ≤ ∑ k : Fin n, |DeltaM i k * U k j| :=
              Finset.abs_sum_le_sum_abs _ _
        _ = ∑ k : Fin n, |DeltaM i k| * |U k j| := by
              apply Finset.sum_congr rfl
              intro k _
              rw [abs_mul]
        _ ≤ ∑ k : Fin n, (gamma fp 1 * |M i k|) * |U k j| := by
              apply Finset.sum_le_sum
              intro k _
              exact mul_le_mul_of_nonneg_right (hDeltaM i k) (abs_nonneg _)
        _ = gamma fp 1 * W := by
              simp only [W, dgttrfMUEnvelope, M, U]
              rw [Finset.mul_sum]
              apply Finset.sum_congr rfl
              intro k _
              ring
    have hDMDU : |∑ k : Fin n, DeltaM i k * DeltaU k j| ≤
        (gamma fp 1 * gamma fp 3) * W := by
      calc
        |∑ k : Fin n, DeltaM i k * DeltaU k j|
            ≤ ∑ k : Fin n, |DeltaM i k * DeltaU k j| :=
              Finset.abs_sum_le_sum_abs _ _
        _ = ∑ k : Fin n, |DeltaM i k| * |DeltaU k j| := by
              apply Finset.sum_congr rfl
              intro k _
              rw [abs_mul]
        _ ≤ ∑ k : Fin n, (gamma fp 1 * |M i k|) *
              (gamma fp 3 * |U k j|) := by
              apply Finset.sum_le_sum
              intro k _
              exact mul_le_mul (hDeltaM i k) (hDeltaU k j)
                (abs_nonneg _)
                (mul_nonneg (gamma_nonneg fp hval1) (abs_nonneg _))
        _ = (gamma fp 1 * gamma fp 3) * W := by
              simp only [W, dgttrfMUEnvelope, M, U]
              rw [Finset.mul_sum]
              apply Finset.sum_congr rfl
              intro k _
              ring
    have htri : |E i j| ≤
        |DeltaF i j| +
          |∑ k : Fin n, M i k * DeltaU k j| +
          |∑ k : Fin n, DeltaM i k * U k j| +
          |∑ k : Fin n, DeltaM i k * DeltaU k j| := by
      dsimp only [E]
      calc
        |DeltaF i j + (∑ k, M i k * DeltaU k j) +
            (∑ k, DeltaM i k * U k j) +
            (∑ k, DeltaM i k * DeltaU k j)|
            ≤ |DeltaF i j + (∑ k, M i k * DeltaU k j) +
                (∑ k, DeltaM i k * U k j)| +
              |∑ k, DeltaM i k * DeltaU k j| := abs_add_le _ _
        _ ≤ (|DeltaF i j + (∑ k, M i k * DeltaU k j)| +
                |∑ k, DeltaM i k * U k j|) +
              |∑ k, DeltaM i k * DeltaU k j| := by
              gcongr
              exact abs_add_le _ _
        _ ≤ ((|DeltaF i j| + |∑ k, M i k * DeltaU k j|) +
                |∑ k, DeltaM i k * U k j|) +
              |∑ k, DeltaM i k * DeltaU k j| := by
              gcongr
              exact abs_add_le _ _
        _ = |DeltaF i j| + |∑ k, M i k * DeltaU k j| +
              |∑ k, DeltaM i k * U k j| +
              |∑ k, DeltaM i k * DeltaU k j| := by ring
    calc
      |E i j| ≤ |DeltaF i j| +
          |∑ k : Fin n, M i k * DeltaU k j| +
          |∑ k : Fin n, DeltaM i k * U k j| +
          |∑ k : Fin n, DeltaM i k * DeltaU k j| := htri
      _ ≤ gamma fp 2 * W + gamma fp 3 * W + gamma fp 1 * W +
          (gamma fp 1 * gamma fp 3) * W := by
            gcongr
      _ = (gamma fp 2 + gamma fp 3 + gamma fp 1 +
          gamma fp 1 * gamma fp 3) * W := by ring
      _ ≤ gamma fp 6 * W := mul_le_mul_of_nonneg_right hcoeff hW
      _ = gamma fp 6 * dgttrfMUEnvelope s i j := rfl
  have hsource : ∀ i : Fin n,
      ∑ j : Fin n, (T (p i) j + E i j) * y j = z (p i) := by
    intro i
    have hb : ∑ k : Fin n, (M i k + DeltaM i k) *
        (∑ j : Fin n, (U k j + DeltaU k j) * y j) = z (p i) := by
      calc
        ∑ k : Fin n, (M i k + DeltaM i k) *
            (∑ j : Fin n, (U k j + DeltaU k j) * y j)
            = ∑ k : Fin n, (M i k + DeltaM i k) * q k := by
                apply Finset.sum_congr rfl
                intro k _
                rw [hback k]
        _ = z (p i) := by
              simpa [s, M, U, p, q] using hforward i
    have hexpand : ∀ j : Fin n,
        ∑ k : Fin n, (M i k + DeltaM i k) *
            (U k j + DeltaU k j) = T (p i) j + E i j := by
      intro j
      have hprod :
          ∑ k : Fin n, (M i k + DeltaM i k) * (U k j + DeltaU k j) =
            (∑ k : Fin n, M i k * U k j) +
            (∑ k : Fin n, M i k * DeltaU k j) +
            (∑ k : Fin n, DeltaM i k * U k j) +
            (∑ k : Fin n, DeltaM i k * DeltaU k j) := by
        simp_rw [mul_add, add_mul, Finset.sum_add_distrib]
        ring
      rw [hprod, hfactor i j]
      dsimp only [E]
      ring
    rw [← hb]
    simp_rw [Finset.mul_sum]
    rw [Finset.sum_comm]
    apply Finset.sum_congr rfl
    intro j _
    simp_rw [← mul_assoc]
    rw [← Finset.sum_mul, hexpand j]
  refine ⟨DeltaT, ?_, ?_⟩
  · intro i j
    simpa [DeltaT, dgttrfSourceEnvelope] using hEbound (p.symm i) j
  · intro i
    have hi := hsource (p.symm i)
    simpa [DeltaT] using hi

end NumStability.Ch11Closure.AasenAdjacentGEPP
