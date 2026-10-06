-- NumStability/Source/Higham/Chapter05/Section02/BidiagonalDerivativeAnalysis/Results/Theorems.lean
--
-- Canonical destination introduced by reorganization wave R03
-- (phase branch B0005, projection P0005).
--
-- Whole-owner block relocation.
-- Historical owner: `NumStability.Algorithms.Ch5SourceClosure`. Public names, namespaces, kinds, visibility,
-- types, attributes and proofs are preserved exactly; private names carry
-- only the approved P0005 module-prefix normalization.

import Mathlib.Data.List.TakeDrop
import Mathlib.Tactic
import NumStability.Algorithms.PolynomialEvaluation.DerivativeEvaluation.ErrorBounds
import NumStability.Analysis.Rounding
import NumStability.FloatingPoint.Model
import NumStability.Source.Higham.Chapter05.Problem04.LejaOrdering.Basic
import NumStability.Source.Higham.Chapter05.Section02.BidiagonalDerivativeAnalysis.Basic
import NumStability.Source.Higham.Chapter05.Section03.NewtonEvaluation.Basic
import NumStability.Source.Higham.Chapter05.Section03.ResidualUnwind.Basic

/-!
# Theorems

Relocated from `NumStability.Algorithms.Ch5SourceClosure` by wave R03 under the frozen B0005 declaration
route and the P0005 baseline projection.
-/


/-!
# Ch5SourceClosure (compatibility module)

Historical path, retained so existing imports of `NumStability.Algorithms.Ch5SourceClosure`
keep resolving. Most of its declarations moved unchanged to the
canonical modules imported above.

The declarations still defined below are private declarations and
their users. Lean mangles a private name to
`_private.<module>.<n>.<name>`, so relocating one renames it and
breaks the frozen declaration graph; anything referring to one must
therefore stay with it. This module is a declaration-bearing facade,
not a pure import shim.
-/

open scoped BigOperators

namespace NumStability

/-- Matrix-vector action of a single upper-bidiagonal row.  This finite-sum
lemma is the indexing bridge used by the literal `(U + Δ) q̂ = a` producer. -/
private theorem ch5_bidiagonal_row_sum
    (n : ℕ) (i : Fin n) (diag super : ℝ) (v : Fin n → ℝ) :
    (∑ j : Fin n,
        (if j = i then diag
          else if j.val = i.val + 1 then super else 0) * v j) =
      if h : i.val + 1 < n then
        diag * v i + super * v ⟨i.val + 1, h⟩
      else diag * v i := by
  split_ifs with h
  · let s : Fin n := ⟨i.val + 1, h⟩
    have hne : s ≠ i := by
      intro heq
      have := congrArg Fin.val heq
      simp [s] at this
    calc
      (∑ x : Fin n,
          (if x = i then diag
            else if x.val = i.val + 1 then super else 0) * v x) =
          ∑ x : Fin n,
            ((if x = i then diag * v x else 0) +
              (if x = s then super * v x else 0)) := by
            apply Finset.sum_congr rfl
            intro x _hx
            have hsuper : (x.val = i.val + 1) ↔ x = s := by
              constructor
              · intro hv; exact Fin.ext (by simpa [s] using hv)
              · intro hx; simpa [s, hx]
            simp only [hsuper]
            by_cases hxi : x = i
            · subst x; simp [Ne.symm hne]
            · by_cases hxs : x = s
              · subst x; simp [hne]
              · simp [hxi, hxs]
      _ = diag * v i + super * v s := by
        rw [Finset.sum_add_distrib]
        simp only [Finset.sum_ite_eq', Finset.mem_univ, if_true]
  · have hsuper : ∀ x : Fin n, x.val ≠ i.val + 1 := by
      intro x hx
      exact h (by simpa [hx] using x.isLt)
    calc
      (∑ x : Fin n,
          (if x = i then diag
            else if x.val = i.val + 1 then super else 0) * v x) =
          ∑ x : Fin n, if x = i then diag * v x else 0 := by
            apply Finset.sum_congr rfl
            intro x _hx
            simp [hsuper x]
      _ = diag * v i := by simp

theorem highamBidiagonalUInv_rightInverse (alpha : ℝ) (n : ℕ) :
    IsRightInverse n (highamBidiagonalU alpha n)
      (highamBidiagonalUInv alpha n) := by
  intro i j
  have hrow := ch5_bidiagonal_row_sum n i 1 (-alpha)
    (fun k => highamBidiagonalUInv alpha n k j)
  have hsum :
      (∑ k : Fin n,
        highamBidiagonalU alpha n i k *
          highamBidiagonalUInv alpha n k j) =
      if h : i.val + 1 < n then
        highamBidiagonalUInv alpha n i j -
          alpha * highamBidiagonalUInv alpha n ⟨i.val + 1, h⟩ j
      else highamBidiagonalUInv alpha n i j := by
    simpa [highamBidiagonalU, Fin.ext_iff] using hrow
  rw [hsum]
  by_cases hs : i.val + 1 < n
  · simp only [hs, dite_true]
    by_cases hij : i = j
    · subst j
      simp [highamBidiagonalUInv]
    · by_cases hlt : i.val < j.val
      · have hisucc_le : i.val + 1 ≤ j.val := by omega
        have hpow : j.val - i.val = (j.val - (i.val + 1)) + 1 := by omega
        simp [highamBidiagonalUInv, Nat.le_of_lt hlt, hisucc_le, hij]
        rw [hpow, pow_succ]
        ring
      · have hji : j.val < i.val := by
          have hneval : i.val ≠ j.val := by
            intro h; exact hij (Fin.ext h)
          omega
        have hnot1 : ¬ i.val ≤ j.val := by omega
        have hnot2 : ¬ i.val + 1 ≤ j.val := by omega
        simp [highamBidiagonalUInv, hnot1, hnot2, hij]
  · simp only [hs, dite_false]
    have hilast : i.val + 1 = n := by omega
    by_cases hij : i = j
    · subst j
      simp [highamBidiagonalUInv]
    · have hji : j.val < i.val := by
        have hjlt : j.val < n := j.isLt
        have hneval : i.val ≠ j.val := by
          intro h; exact hij (Fin.ext h)
        omega
      have hnot : ¬ i.val ≤ j.val := by omega
      simp [highamBidiagonalUInv, hnot, hij]

theorem highamBidiagonalUInv_leftInverse (alpha : ℝ) (n : ℕ) :
    IsLeftInverse n (highamBidiagonalU alpha n)
      (highamBidiagonalUInv alpha n) :=
  isLeftInverse_of_isRightInverse _ _
    (highamBidiagonalUInv_rightInverse alpha n)

/-- First of the three literal matrices displayed below Higham (5.6):
`|U_n⁻¹||U_n|` has diagonal entries `1` and strict upper entries
`2|alpha|^(j-i)`. -/
theorem highamBidiagonalAbsInv_mul_absU_entry
    (alpha : ℝ) (n : ℕ) (i j : Fin n) :
    (∑ k : Fin n,
      |highamBidiagonalUInv alpha n i k| *
        |highamBidiagonalU alpha n k j|) =
      if i = j then 1
      else if i.val < j.val then 2 * |alpha| ^ (j.val - i.val)
      else 0 := by
  have habsInv : ∀ k : Fin n,
      |highamBidiagonalUInv alpha n i k| =
        highamBidiagonalUInv |alpha| n i k := by
    intro k
    simp only [highamBidiagonalUInv]
    split_ifs <;> simp [abs_pow]
  have habsU : ∀ k : Fin n,
      |highamBidiagonalU alpha n k j| =
        2 * (if k = j then 1 else 0) -
          highamBidiagonalU |alpha| n k j := by
    intro k
    simp only [highamBidiagonalU]
    by_cases hd : j.val = k.val
    · have hkj : k = j := Fin.ext hd.symm
      simp [hd, hkj]
      norm_num
    · by_cases hs : j.val = k.val + 1
      · have hne : k ≠ j := by intro h; subst j; omega
        simp [hs, hne]
      · have hne : k ≠ j := by
          intro h; subst j; exact hd rfl
        simp [hd, hs, hne]
  calc
    (∑ k : Fin n,
      |highamBidiagonalUInv alpha n i k| *
        |highamBidiagonalU alpha n k j|) =
        ∑ k : Fin n,
          highamBidiagonalUInv |alpha| n i k *
            (2 * (if k = j then 1 else 0) -
              highamBidiagonalU |alpha| n k j) := by
          apply Finset.sum_congr rfl
          intro k _hk
          rw [habsInv k, habsU k]
    _ = ∑ k : Fin n,
          (2 * (highamBidiagonalUInv |alpha| n i k *
            (if k = j then 1 else 0)) -
            highamBidiagonalUInv |alpha| n i k *
              highamBidiagonalU |alpha| n k j) := by
          apply Finset.sum_congr rfl
          intro k _hk
          ring
    _ = 2 * (∑ k : Fin n,
          highamBidiagonalUInv |alpha| n i k *
            (if k = j then 1 else 0)) -
        ∑ k : Fin n, highamBidiagonalUInv |alpha| n i k *
          highamBidiagonalU |alpha| n k j := by
          rw [Finset.sum_sub_distrib]
          rw [Finset.mul_sum]
    _ = 2 * highamBidiagonalUInv |alpha| n i j -
        (if i = j then 1 else 0) := by
          rw [highamBidiagonalUInv_leftInverse |alpha| n i j]
          simp
    _ = if i = j then 1
        else if i.val < j.val then 2 * |alpha| ^ (j.val - i.val)
        else 0 := by
      by_cases hij : i = j
      · subst j
        simp [highamBidiagonalUInv]
        norm_num
      · by_cases hlt : i.val < j.val
        · simp [hij, hlt, highamBidiagonalUInv, Nat.le_of_lt hlt]
        · have hnot : ¬i.val ≤ j.val := by
            have hne : i.val ≠ j.val := by
              intro h; exact hij (Fin.ext h)
            omega
          simp [hij, hlt, highamBidiagonalUInv, hnot]

/-- Third matrix displayed below Higham (5.6):
`|U_n⁻¹||U_n⁻¹||U_n|` has diagonal entries `1`, strict upper entries
`(2(j-i)+1)|alpha|^(j-i)`, and zero entries below the diagonal. -/
theorem highamBidiagonalAbsInv_mul_absInv_mul_absU_entry
    (alpha : ℝ) (n : ℕ) (i j : Fin n) :
    (∑ k : Fin n,
      |highamBidiagonalUInv alpha n i k| *
        (∑ l : Fin n,
          |highamBidiagonalUInv alpha n k l| *
            |highamBidiagonalU alpha n l j|)) =
      if i = j then 1
      else if i.val < j.val then
        ((2 * (j.val - i.val) + 1 : ℕ) : ℝ) *
          |alpha| ^ (j.val - i.val)
      else 0 := by
  have habsInv : ∀ a b : Fin n,
      |highamBidiagonalUInv alpha n a b| =
        highamBidiagonalUInv |alpha| n a b := by
    intro a b
    exact highamBidiagonalUInv_abs_entry alpha n a b
  have hinner : ∀ k : Fin n,
      (∑ l : Fin n,
        |highamBidiagonalUInv alpha n k l| *
          |highamBidiagonalU alpha n l j|) =
        2 * highamBidiagonalUInv |alpha| n k j -
          (if k = j then 1 else 0) := by
    intro k
    rw [highamBidiagonalAbsInv_mul_absU_entry]
    by_cases hkj : k = j
    · subst k
      simp [highamBidiagonalUInv]
      norm_num
    · by_cases hlt : k.val < j.val
      · simp [hkj, hlt, highamBidiagonalUInv, Nat.le_of_lt hlt]
      · have hnot : ¬k.val ≤ j.val := by
          have hne : k.val ≠ j.val := by
            intro h
            exact hkj (Fin.ext h)
          omega
        simp [hkj, hlt, highamBidiagonalUInv, hnot]
  calc
    (∑ k : Fin n,
      |highamBidiagonalUInv alpha n i k| *
        (∑ l : Fin n,
          |highamBidiagonalUInv alpha n k l| *
            |highamBidiagonalU alpha n l j|)) =
        ∑ k : Fin n,
          highamBidiagonalUInv |alpha| n i k *
            (2 * highamBidiagonalUInv |alpha| n k j -
              (if k = j then 1 else 0)) := by
              apply Finset.sum_congr rfl
              intro k _hk
              rw [habsInv i k, hinner k]
    _ = ∑ k : Fin n,
          (2 * (highamBidiagonalUInv |alpha| n i k *
              highamBidiagonalUInv |alpha| n k j) -
            highamBidiagonalUInv |alpha| n i k *
              (if k = j then 1 else 0)) := by
              apply Finset.sum_congr rfl
              intro k _hk
              ring
    _ = 2 * (∑ k : Fin n,
          highamBidiagonalUInv |alpha| n i k *
            highamBidiagonalUInv |alpha| n k j) -
        ∑ k : Fin n,
          highamBidiagonalUInv |alpha| n i k *
            (if k = j then 1 else 0) := by
            rw [Finset.sum_sub_distrib]
            rw [Finset.mul_sum]
    _ = 2 *
          (if i.val ≤ j.val then
            ((j.val - i.val + 1 : ℕ) : ℝ) *
              |alpha| ^ (j.val - i.val)
          else 0) - highamBidiagonalUInv |alpha| n i j := by
            rw [highamBidiagonalUInv_square_entry]
            simp
    _ = if i = j then 1
        else if i.val < j.val then
          ((2 * (j.val - i.val) + 1 : ℕ) : ℝ) *
            |alpha| ^ (j.val - i.val)
        else 0 := by
      by_cases hij : i = j
      · subst j
        simp [highamBidiagonalUInv]
        norm_num
      · by_cases hlt : i.val < j.val
        · have hle : i.val ≤ j.val := Nat.le_of_lt hlt
          simp only [hij, if_false, hlt, if_true, hle]
          simp only [highamBidiagonalUInv, hle, Nat.cast_add, Nat.cast_one,
            Nat.cast_mul, Nat.cast_ofNat]
          simp only [if_true]
          ring
        · have hnot : ¬i.val ≤ j.val := by
            have hne : i.val ≠ j.val := by
              intro h
              exact hij (Fin.ext h)
            omega
          simp [hij, hlt, hnot, highamBidiagonalUInv]

theorem highamBidiagonalExactSolve_system
    (alpha : ℝ) {n : ℕ} (a : Fin n → ℝ) :
    ∀ i : Fin n,
      ∑ j : Fin n, highamBidiagonalU alpha n i j *
          highamBidiagonalExactSolve alpha a j = a i := by
  intro i
  unfold highamBidiagonalExactSolve
  calc
    (∑ j : Fin n, highamBidiagonalU alpha n i j *
        ∑ k : Fin n, highamBidiagonalUInv alpha n j k * a k) =
        ∑ j : Fin n, ∑ k : Fin n,
          highamBidiagonalU alpha n i j *
            (highamBidiagonalUInv alpha n j k * a k) := by
          apply Finset.sum_congr rfl
          intro j _hj
          rw [Finset.mul_sum]
    _ = ∑ k : Fin n, ∑ j : Fin n,
          highamBidiagonalU alpha n i j *
            (highamBidiagonalUInv alpha n j k * a k) :=
      Finset.sum_comm
    _ = ∑ k : Fin n,
          (∑ j : Fin n,
            highamBidiagonalU alpha n i j *
              highamBidiagonalUInv alpha n j k) * a k := by
          apply Finset.sum_congr rfl
          intro k _hk
          rw [Finset.sum_mul]
          apply Finset.sum_congr rfl
          intro j _hj
          ring
    _ = ∑ k : Fin n, (if i = k then 1 else 0) * a k := by
          apply Finset.sum_congr rfl
          intro k _hk
          rw [highamBidiagonalUInv_rightInverse alpha n i k]
    _ = a i := by simp

private theorem ch5_fl_mul_right_zero (fp : FPModel) (x : ℝ) :
    fp.fl_mul x 0 = 0 := by
  obtain ⟨delta, _hdelta, hmul⟩ := fp.model_mul x 0
  rw [hmul]
  ring

private theorem ch5_fl_hornerDesc_append_singleton
    (fp : FPModel) (alpha a : ℝ) (l : List ℝ) :
    fl_hornerDesc fp alpha (l ++ [a]) =
      fl_hornerStep fp alpha (fl_hornerDesc fp alpha l) a := by
  cases l with
  | nil =>
      simp [fl_hornerDesc, fl_hornerStep, ch5_fl_mul_right_zero,
        fp.fl_add_zero]
  | cons b rest =>
      simp [fl_hornerDesc, List.foldl_append]

theorem flHighamBidiagonalSolve_succ
    (fp : FPModel) (alpha : ℝ) {n : ℕ}
    (a : Fin n → ℝ) (i : Fin n) (hi : i.val + 1 < n) :
    flHighamBidiagonalSolve fp alpha a i =
      fl_hornerStep fp alpha
        (flHighamBidiagonalSolve fp alpha a ⟨i.val + 1, hi⟩) (a i) := by
  let l := List.ofFn a
  have hil : i.val < l.length := by simpa [l] using i.isLt
  have hdrop := List.drop_eq_getElem_cons hil
  have hget : l[i.val] = a i := by
    simpa [l] using List.getElem_ofFn (f := a) hil
  unfold flHighamBidiagonalSolve
  rw [show (List.ofFn a).drop i.val =
      (List.ofFn a)[i.val] :: (List.ofFn a).drop (i.val + 1) by
        simpa [l] using hdrop]
  rw [List.reverse_cons, ch5_fl_hornerDesc_append_singleton]
  simpa [hget]

/-- Higham, 2nd ed., Chapter 5, Section 5.2, equation (5.5), literal
matrix-form producer.  The actual rounded Horner sweep satisfies
`(U_n + Δ) q̂ = a` with `|Δ| ≤ u |U_n|`.  The only additional hypothesis is
Higham's primitive inverse relative-error model (2.5) for rounded addition;
the matrix equation and perturbation bound are conclusions. -/
theorem flHighamBidiagonalSolve_backward_perturbation
    (fp : FPModel) (alpha : ℝ) {n : ℕ}
    (a : Fin n → ℝ)
    (haddInv : ∀ x y : ℝ,
      inverseRelErrorModel (fp.fl_add x y) (x + y) fp.u) :
    let qhat := flHighamBidiagonalSolve fp alpha a
    let Delta := flHighamBidiagonalDelta fp alpha a haddInv
    (∀ i : Fin n,
      ∑ j : Fin n,
        (highamBidiagonalU alpha n i j + Delta i j) * qhat j = a i) ∧
    (∀ i j : Fin n,
      |Delta i j| ≤ fp.u * |highamBidiagonalU alpha n i j|) := by
  classical
  dsimp only
  let qhat := flHighamBidiagonalSolve fp alpha a
  let delta : Fin n → ℝ := fun i =>
    if hi : i.val + 1 < n then
      Classical.choose (fp.model_mul alpha (qhat ⟨i.val + 1, hi⟩))
    else 0
  let eps : Fin n → ℝ := fun i =>
    if hi : i.val + 1 < n then
      Classical.choose
        (haddInv (fp.fl_mul alpha (qhat ⟨i.val + 1, hi⟩)) (a i))
    else 0
  have hDelta : flHighamBidiagonalDelta fp alpha a haddInv = fun i j =>
      if j = i then eps i
      else if j.val = i.val + 1 then -alpha * delta i
      else 0 := by
    rfl
  constructor
  · intro i
    by_cases hi : i.val + 1 < n
    · let s : Fin n := ⟨i.val + 1, hi⟩
      have hdelta := Classical.choose_spec (fp.model_mul alpha (qhat s))
      have heps := Classical.choose_spec
        (haddInv (fp.fl_mul alpha (qhat s)) (a i))
      have hdeltaEq : delta i = Classical.choose
          (fp.model_mul alpha (qhat s)) := by simp [delta, hi, s]
      have hepsEq : eps i = Classical.choose
          (haddInv (fp.fl_mul alpha (qhat s)) (a i)) := by
        simp [eps, hi, s]
      have hrec : qhat i =
          fp.fl_add (fp.fl_mul alpha (qhat s)) (a i) := by
        simpa [qhat, s, fl_hornerStep] using
          flHighamBidiagonalSolve_succ fp alpha a i hi
      have hepsAlg : (1 + eps i) * qhat i =
          fp.fl_mul alpha (qhat s) + a i := by
        have hepsNe : 1 + eps i ≠ 0 := by
          rw [hepsEq]
          exact heps.2.1
        have hepsComp : qhat i =
            (fp.fl_mul alpha (qhat s) + a i) / (1 + eps i) := by
          rw [hrec, hepsEq]
          exact heps.2.2
        rw [hepsComp]
        field_simp [hepsNe]
      have hmulAlg : fp.fl_mul alpha (qhat s) =
          alpha * qhat s * (1 + delta i) := by
        rw [hdeltaEq]
        exact hdelta.2
      rw [hDelta]
      have hrow := ch5_bidiagonal_row_sum n i
        (1 + eps i) (-alpha * (1 + delta i)) qhat
      have hshape :
          (∑ j : Fin n,
              (highamBidiagonalU alpha n i j +
                (if j = i then eps i
                 else if j.val = i.val + 1 then -alpha * delta i else 0)) *
                qhat j) =
            ∑ j : Fin n,
              (if j = i then 1 + eps i
               else if j.val = i.val + 1 then -alpha * (1 + delta i)
               else 0) * qhat j := by
        apply Finset.sum_congr rfl
        intro j _hj
        simp only [highamBidiagonalU]
        by_cases hd : j = i
        · subst j; simp
        · by_cases hs : j.val = i.val + 1
          · simp [hd, hs]; ring
          · have hdv : j.val ≠ i.val := by
              intro hv; exact hd (Fin.ext hv)
            simp [hd, hdv, hs]
      rw [hshape, hrow]
      simp [hi]
      rw [hepsAlg, hmulAlg]
      ring
    · have hilast : i.val + 1 = n := by omega
      have hq : qhat i = a i := by
        simpa [qhat] using
          flHighamBidiagonalSolve_last fp alpha a i hilast
      rw [hDelta]
      have heps0 : eps i = 0 := by simp [eps, hi]
      have hrow := ch5_bidiagonal_row_sum n i
        (1 + eps i) (-alpha * (1 + delta i)) qhat
      have hshape :
          (∑ j : Fin n,
              (highamBidiagonalU alpha n i j +
                (if j = i then eps i
                 else if j.val = i.val + 1 then -alpha * delta i else 0)) *
                qhat j) =
            ∑ j : Fin n,
              (if j = i then 1 + eps i
               else if j.val = i.val + 1 then -alpha * (1 + delta i)
               else 0) * qhat j := by
        apply Finset.sum_congr rfl
        intro j _hj
        simp only [highamBidiagonalU]
        by_cases hd : j = i
        · subst j; simp
        · by_cases hs : j.val = i.val + 1
          · simp [hd, hs]; ring
          · have hdv : j.val ≠ i.val := by
              intro hv; exact hd (Fin.ext hv)
            simp [hd, hdv, hs]
      rw [hshape, hrow]
      simp [hi, heps0, hq]
  · intro i j
    rw [hDelta]
    by_cases hd : j = i
    · subst j
      simp only [highamBidiagonalU_diag, abs_one, mul_one]
      by_cases hi : i.val + 1 < n
      · have heps := Classical.choose_spec
          (haddInv
            (fp.fl_mul alpha (qhat ⟨i.val + 1, hi⟩)) (a i))
        simpa [eps, hi] using heps.1
      · simp [eps, hi, fp.u_nonneg]
    · have hdv : j.val ≠ i.val := by
        intro hv; exact hd (Fin.ext hv)
      by_cases hs : j.val = i.val + 1
      · simp only [hd, if_false, hs, if_true]
        rw [highamBidiagonalU_superdiag alpha n i j hs]
        by_cases hi : i.val + 1 < n
        · have hdelta := Classical.choose_spec
            (fp.model_mul alpha (qhat ⟨i.val + 1, hi⟩))
          simp only [delta, hi, dif_pos, abs_mul]
          rw [abs_neg]
          simpa [mul_comm] using
            mul_le_mul_of_nonneg_left hdelta.1 (abs_nonneg alpha)
        · exfalso
          exact hi (by simpa [hs] using j.isLt)
      · simp [hd, hdv, hs,
          highamBidiagonalU_zero_of_not_diag_not_superdiag]

/-- The computed-vector majorant itself admits the literal source split
`u |U⁻¹||U||q| + u² (|U⁻¹||U|)²|q̂|`.  This is the
algebraic step that justifies replacing `q̂` by the exact `q` in (5.5). -/
theorem flHighamBidiagonalSolve_forward_majorant_first_order_quadratic
    (fp : FPModel) (alpha : ℝ) {n : ℕ}
    (a : Fin n → ℝ)
    (haddInv : ∀ x y : ℝ,
      inverseRelErrorModel (fp.fl_add x y) (x + y) fp.u) :
    ∀ i : Fin n,
      highamBidiagonalForwardErrorMajorant alpha n
          (highamBidiagonalUInv alpha n) fp.u
          (flHighamBidiagonalSolve fp alpha a) i ≤
        fp.u * highamBidiagonalAbsForwardAction alpha n
          (highamBidiagonalUInv alpha n)
          (fun k => |highamBidiagonalExactSolve alpha a k|) i +
        highamBidiagonalEq55QuadraticRemainder fp alpha n
          (flHighamBidiagonalSolve fp alpha a) i := by
  intro i
  let q := highamBidiagonalExactSolve alpha a
  let qhat := flHighamBidiagonalSolve fp alpha a
  have hback :=
    flHighamBidiagonalSolve_backward_perturbation fp alpha a haddInv
  have hraw : ∀ k : Fin n,
      |highamBidiagonalExactSolve alpha a k -
          flHighamBidiagonalSolve fp alpha a k| ≤
        highamBidiagonalForwardErrorMajorant alpha n
          (highamBidiagonalUInv alpha n) fp.u
          (flHighamBidiagonalSolve fp alpha a) k :=
    highamBidiagonal_forward_error_from_backward alpha n
      (highamBidiagonalUInv alpha n)
      (highamBidiagonalExactSolve alpha a)
      (flHighamBidiagonalSolve fp alpha a) a
      (flHighamBidiagonalDelta fp alpha a haddInv)
      fp.u fp.u_nonneg
      (highamBidiagonalUInv_leftInverse alpha n)
      (highamBidiagonalExactSolve_system alpha a)
      hback.1 hback.2
  have herror : ∀ k : Fin n,
      |q k - qhat k| ≤
        fp.u * highamBidiagonalAbsForwardAction alpha n
          (highamBidiagonalUInv alpha n) (fun l => |qhat l|) k := by
    intro k
    simpa [q, qhat,
      highamBidiagonalForwardErrorMajorant_eq_absForwardAction] using
      hraw k
  have hqhat : ∀ k : Fin n,
      |qhat k| ≤ |q k| +
        fp.u * highamBidiagonalAbsForwardAction alpha n
          (highamBidiagonalUInv alpha n) (fun l => |qhat l|) k := by
    intro k
    calc
      |qhat k| = |q k + (qhat k - q k)| := by congr 1 <;> ring
      _ ≤ |q k| + |qhat k - q k| := abs_add_le _ _
      _ = |q k| + |q k - qhat k| := by rw [abs_sub_comm]
      _ ≤ |q k| +
          fp.u * highamBidiagonalAbsForwardAction alpha n
            (highamBidiagonalUInv alpha n) (fun l => |qhat l|) k :=
        add_le_add (le_refl _) (herror k)
  have hmono := highamBidiagonalAbsForwardAction_mono alpha n
    (highamBidiagonalUInv alpha n) hqhat i
  have huscaled := mul_le_mul_of_nonneg_left hmono fp.u_nonneg
  rw [highamBidiagonalForwardErrorMajorant_eq_absForwardAction]
  calc
    fp.u * highamBidiagonalAbsForwardAction alpha n
        (highamBidiagonalUInv alpha n) (fun k => |qhat k|) i ≤
      fp.u * highamBidiagonalAbsForwardAction alpha n
        (highamBidiagonalUInv alpha n)
        (fun k => |q k| +
          fp.u * highamBidiagonalAbsForwardAction alpha n
            (highamBidiagonalUInv alpha n) (fun l => |qhat l|) k) i :=
      huscaled
    _ = fp.u * highamBidiagonalAbsForwardAction alpha n
          (highamBidiagonalUInv alpha n) (fun k => |q k|) i +
        highamBidiagonalEq55QuadraticRemainder fp alpha n qhat i := by
      rw [highamBidiagonalAbsForwardAction_add,
        highamBidiagonalAbsForwardAction_smul]
      simp only [highamBidiagonalEq55QuadraticRemainder]
      ring
    _ = fp.u * highamBidiagonalAbsForwardAction alpha n
          (highamBidiagonalUInv alpha n)
          (fun k => |highamBidiagonalExactSolve alpha a k|) i +
        highamBidiagonalEq55QuadraticRemainder fp alpha n
          (flHighamBidiagonalSolve fp alpha a) i := by
      rfl

/-- Higham equation (5.5), end-to-end exact componentwise form for the actual
rounded Horner sweep. -/
theorem flHighamBidiagonalSolve_forward_error
    (fp : FPModel) (alpha : ℝ) {n : ℕ}
    (a : Fin n → ℝ)
    (haddInv : ∀ x y : ℝ,
      inverseRelErrorModel (fp.fl_add x y) (x + y) fp.u) :
    ∀ i : Fin n,
      |highamBidiagonalExactSolve alpha a i -
          flHighamBidiagonalSolve fp alpha a i| ≤
        highamBidiagonalForwardErrorMajorant alpha n
          (highamBidiagonalUInv alpha n) fp.u
          (flHighamBidiagonalSolve fp alpha a) i := by
  have hback :=
    flHighamBidiagonalSolve_backward_perturbation fp alpha a haddInv
  exact highamBidiagonal_forward_error_from_backward alpha n
    (highamBidiagonalUInv alpha n)
    (highamBidiagonalExactSolve alpha a)
    (flHighamBidiagonalSolve fp alpha a) a
    (flHighamBidiagonalDelta fp alpha a haddInv)
    fp.u fp.u_nonneg
    (highamBidiagonalUInv_leftInverse alpha n)
    (highamBidiagonalExactSolve_system alpha a)
    hback.1 hback.2

/-- Printed-strength (5.5): the leading term uses the exact quotient `q`, and
the source's `O(u²)` is instantiated by an explicit nonnegative quadratic
remainder rather than being hidden in the computed vector. -/
theorem flHighamBidiagonalSolve_forward_error_first_order_quadratic
    (fp : FPModel) (alpha : ℝ) {n : ℕ}
    (a : Fin n → ℝ)
    (haddInv : ∀ x y : ℝ,
      inverseRelErrorModel (fp.fl_add x y) (x + y) fp.u) :
    ∀ i : Fin n,
      |highamBidiagonalExactSolve alpha a i -
          flHighamBidiagonalSolve fp alpha a i| ≤
        fp.u * highamBidiagonalAbsForwardAction alpha n
          (highamBidiagonalUInv alpha n)
          (fun k => |highamBidiagonalExactSolve alpha a k|) i +
        highamBidiagonalEq55QuadraticRemainder fp alpha n
          (flHighamBidiagonalSolve fp alpha a) i := by
  intro i
  exact (flHighamBidiagonalSolve_forward_error fp alpha a haddInv i).trans
    (flHighamBidiagonalSolve_forward_majorant_first_order_quadratic
      fp alpha a haddInv i)

/-- Equations (5.5) and (5.6), the two actual bidiagonal solves used for the
first derivative.  `q̂` is the rounded synthetic-division sweep and `r̂` is a
second rounded sweep over its tail; both printed perturbation systems and both
`u|U|` bounds are produced from the executions. -/
theorem flHighamBidiagonalSolve_two_sweeps_backward_perturbation
    (fp : FPModel) (alpha : ℝ) {n : ℕ}
    (a : Fin (n + 1) → ℝ)
    (haddInv : ∀ x y : ℝ,
      inverseRelErrorModel (fp.fl_add x y) (x + y) fp.u) :
    let qhat := flHighamBidiagonalSolve fp alpha a
    let qtail : Fin n → ℝ := fun i => qhat ⟨i.val + 1, Nat.succ_lt_succ i.isLt⟩
    let rhat := flHighamBidiagonalSolve fp alpha qtail
    let Delta1 := flHighamBidiagonalDelta fp alpha a haddInv
    let Delta2 := flHighamBidiagonalDelta fp alpha qtail haddInv
    (∀ i : Fin (n + 1),
      ∑ j : Fin (n + 1),
        (highamBidiagonalU alpha (n + 1) i j + Delta1 i j) * qhat j = a i) ∧
    (∀ i j : Fin (n + 1),
      |Delta1 i j| ≤ fp.u * |highamBidiagonalU alpha (n + 1) i j|) ∧
    (∀ i : Fin n,
      ∑ j : Fin n,
        (highamBidiagonalU alpha n i j + Delta2 i j) * rhat j = qtail i) ∧
    (∀ i j : Fin n,
      |Delta2 i j| ≤ fp.u * |highamBidiagonalU alpha n i j|) := by
  dsimp only
  exact ⟨
    (flHighamBidiagonalSolve_backward_perturbation
      fp alpha a haddInv).1,
    (flHighamBidiagonalSolve_backward_perturbation
      fp alpha a haddInv).2,
    (flHighamBidiagonalSolve_backward_perturbation fp alpha
      (fun i : Fin n =>
        flHighamBidiagonalSolve fp alpha a
          ⟨i.val + 1, Nat.succ_lt_succ i.isLt⟩) haddInv).1,
    (flHighamBidiagonalSolve_backward_perturbation fp alpha
      (fun i : Fin n =>
        flHighamBidiagonalSolve fp alpha a
          ⟨i.val + 1, Nat.succ_lt_succ i.isLt⟩) haddInv).2⟩

/-- Equation (5.6), end-to-end exact componentwise form for the two actual
rounded solves.  The first-sweep error is propagated through the explicit
inverse of the second system, while the second-sweep backward error contributes
its own (5.5) majorant.  Thus this is a remainder-free computed-vector version
of the first-order two-term estimate printed after (5.6). -/
theorem flHighamBidiagonalSolve_two_sweeps_forward_error
    (fp : FPModel) (alpha : ℝ) {n : ℕ}
    (a : Fin (n + 1) → ℝ)
    (haddInv : ∀ x y : ℝ,
      inverseRelErrorModel (fp.fl_add x y) (x + y) fp.u) :
    let q := highamBidiagonalExactSolve alpha a
    let qhat := flHighamBidiagonalSolve fp alpha a
    let qtail : Fin n → ℝ := fun j =>
      q ⟨j.val + 1, Nat.succ_lt_succ j.isLt⟩
    let qhatTail : Fin n → ℝ := fun j =>
      qhat ⟨j.val + 1, Nat.succ_lt_succ j.isLt⟩
    let r := highamBidiagonalExactSolve alpha qtail
    let rhat := flHighamBidiagonalSolve fp alpha qhatTail
    ∀ i : Fin n,
      |r i - rhat i| ≤
        (∑ j : Fin n,
          |highamBidiagonalUInv alpha n i j| *
            highamBidiagonalForwardErrorMajorant alpha (n + 1)
              (highamBidiagonalUInv alpha (n + 1)) fp.u qhat
              ⟨j.val + 1, Nat.succ_lt_succ j.isLt⟩) +
        highamBidiagonalForwardErrorMajorant alpha n
          (highamBidiagonalUInv alpha n) fp.u rhat i := by
  dsimp only
  intro i
  have hfirst (j : Fin n) :
      |highamBidiagonalExactSolve alpha a
          ⟨j.val + 1, Nat.succ_lt_succ j.isLt⟩ -
        flHighamBidiagonalSolve fp alpha a
          ⟨j.val + 1, Nat.succ_lt_succ j.isLt⟩| ≤
        highamBidiagonalForwardErrorMajorant alpha (n + 1)
          (highamBidiagonalUInv alpha (n + 1)) fp.u
          (flHighamBidiagonalSolve fp alpha a)
          ⟨j.val + 1, Nat.succ_lt_succ j.isLt⟩ :=
    flHighamBidiagonalSolve_forward_error fp alpha a haddInv
      ⟨j.val + 1, Nat.succ_lt_succ j.isLt⟩
  have hsecond :
      |highamBidiagonalExactSolve alpha
          (fun j : Fin n => flHighamBidiagonalSolve fp alpha a
            ⟨j.val + 1, Nat.succ_lt_succ j.isLt⟩) i -
        flHighamBidiagonalSolve fp alpha
          (fun j : Fin n => flHighamBidiagonalSolve fp alpha a
            ⟨j.val + 1, Nat.succ_lt_succ j.isLt⟩) i| ≤
        highamBidiagonalForwardErrorMajorant alpha n
          (highamBidiagonalUInv alpha n) fp.u
          (flHighamBidiagonalSolve fp alpha
            (fun j : Fin n => flHighamBidiagonalSolve fp alpha a
              ⟨j.val + 1, Nat.succ_lt_succ j.isLt⟩)) i :=
    flHighamBidiagonalSolve_forward_error fp alpha
      (fun j : Fin n => flHighamBidiagonalSolve fp alpha a
        ⟨j.val + 1, Nat.succ_lt_succ j.isLt⟩) haddInv i
  have hrDiff :
      highamBidiagonalExactSolve alpha
          (fun j : Fin n => highamBidiagonalExactSolve alpha a
            ⟨j.val + 1, Nat.succ_lt_succ j.isLt⟩) i -
        highamBidiagonalExactSolve alpha
          (fun j : Fin n => flHighamBidiagonalSolve fp alpha a
            ⟨j.val + 1, Nat.succ_lt_succ j.isLt⟩) i =
        ∑ j : Fin n, highamBidiagonalUInv alpha n i j *
          (highamBidiagonalExactSolve alpha a
              ⟨j.val + 1, Nat.succ_lt_succ j.isLt⟩ -
            flHighamBidiagonalSolve fp alpha a
              ⟨j.val + 1, Nat.succ_lt_succ j.isLt⟩) := by
    simp only [highamBidiagonalExactSolve]
    rw [← Finset.sum_sub_distrib]
    apply Finset.sum_congr rfl
    intro j _hj
    ring
  have hpropagated :
      |highamBidiagonalExactSolve alpha
          (fun j : Fin n => highamBidiagonalExactSolve alpha a
            ⟨j.val + 1, Nat.succ_lt_succ j.isLt⟩) i -
        highamBidiagonalExactSolve alpha
          (fun j : Fin n => flHighamBidiagonalSolve fp alpha a
            ⟨j.val + 1, Nat.succ_lt_succ j.isLt⟩) i| ≤
        ∑ j : Fin n,
          |highamBidiagonalUInv alpha n i j| *
            highamBidiagonalForwardErrorMajorant alpha (n + 1)
              (highamBidiagonalUInv alpha (n + 1)) fp.u
              (flHighamBidiagonalSolve fp alpha a)
              ⟨j.val + 1, Nat.succ_lt_succ j.isLt⟩ := by
    rw [hrDiff]
    calc
      |∑ j : Fin n, highamBidiagonalUInv alpha n i j *
          (highamBidiagonalExactSolve alpha a
              ⟨j.val + 1, Nat.succ_lt_succ j.isLt⟩ -
            flHighamBidiagonalSolve fp alpha a
              ⟨j.val + 1, Nat.succ_lt_succ j.isLt⟩)| ≤
          ∑ j : Fin n,
            |highamBidiagonalUInv alpha n i j *
              (highamBidiagonalExactSolve alpha a
                  ⟨j.val + 1, Nat.succ_lt_succ j.isLt⟩ -
                flHighamBidiagonalSolve fp alpha a
                  ⟨j.val + 1, Nat.succ_lt_succ j.isLt⟩)| :=
            Finset.abs_sum_le_sum_abs _ _
      _ = ∑ j : Fin n,
            |highamBidiagonalUInv alpha n i j| *
              |highamBidiagonalExactSolve alpha a
                  ⟨j.val + 1, Nat.succ_lt_succ j.isLt⟩ -
                flHighamBidiagonalSolve fp alpha a
                  ⟨j.val + 1, Nat.succ_lt_succ j.isLt⟩| := by
            apply Finset.sum_congr rfl
            intro j _hj
            rw [abs_mul]
      _ ≤ ∑ j : Fin n,
            |highamBidiagonalUInv alpha n i j| *
              highamBidiagonalForwardErrorMajorant alpha (n + 1)
                (highamBidiagonalUInv alpha (n + 1)) fp.u
                (flHighamBidiagonalSolve fp alpha a)
                ⟨j.val + 1, Nat.succ_lt_succ j.isLt⟩ := by
            apply Finset.sum_le_sum
            intro j _hj
            exact mul_le_mul_of_nonneg_left (hfirst j)
              (abs_nonneg (highamBidiagonalUInv alpha n i j))
  have hsplit :
      highamBidiagonalExactSolve alpha
          (fun j : Fin n => highamBidiagonalExactSolve alpha a
            ⟨j.val + 1, Nat.succ_lt_succ j.isLt⟩) i -
        flHighamBidiagonalSolve fp alpha
          (fun j : Fin n => flHighamBidiagonalSolve fp alpha a
            ⟨j.val + 1, Nat.succ_lt_succ j.isLt⟩) i =
        (highamBidiagonalExactSolve alpha
            (fun j : Fin n => highamBidiagonalExactSolve alpha a
              ⟨j.val + 1, Nat.succ_lt_succ j.isLt⟩) i -
          highamBidiagonalExactSolve alpha
            (fun j : Fin n => flHighamBidiagonalSolve fp alpha a
              ⟨j.val + 1, Nat.succ_lt_succ j.isLt⟩) i) +
        (highamBidiagonalExactSolve alpha
            (fun j : Fin n => flHighamBidiagonalSolve fp alpha a
              ⟨j.val + 1, Nat.succ_lt_succ j.isLt⟩) i -
          flHighamBidiagonalSolve fp alpha
            (fun j : Fin n => flHighamBidiagonalSolve fp alpha a
              ⟨j.val + 1, Nat.succ_lt_succ j.isLt⟩) i) := by
    ring
  rw [hsplit]
  exact le_trans (abs_add_le _ _)
    (add_le_add hpropagated hsecond)

/-- Printed-strength (5.6) for the two actual rounded sweeps.  Both leading
terms use the exact vectors `r` and `q`.  The two named remainder terms are
finite, nonnegative, and carry an explicit factor `u²`: one propagates the
first sweep's (5.5) remainder, and the other is the cross/sweep-feedback term. -/
theorem flHighamBidiagonalSolve_two_sweeps_forward_error_first_order_quadratic
    (fp : FPModel) (alpha : ℝ) {n : ℕ}
    (a : Fin (n + 1) → ℝ)
    (haddInv : ∀ x y : ℝ,
      inverseRelErrorModel (fp.fl_add x y) (x + y) fp.u) :
    let q := highamBidiagonalExactSolve alpha a
    let qhat := flHighamBidiagonalSolve fp alpha a
    let qtail : Fin n → ℝ := fun j =>
      q ⟨j.val + 1, Nat.succ_lt_succ j.isLt⟩
    let qhatTail : Fin n → ℝ := fun j =>
      qhat ⟨j.val + 1, Nat.succ_lt_succ j.isLt⟩
    let r := highamBidiagonalExactSolve alpha qtail
    let rhat := flHighamBidiagonalSolve fp alpha qhatTail
    ∀ i : Fin n,
      |r i - rhat i| ≤
        fp.u * highamBidiagonalAbsForwardAction alpha n
          (highamBidiagonalUInv alpha n) (fun k => |r k|) i +
        fp.u * highamBidiagonalAbsTailInverseAction alpha n
          (fun k =>
            highamBidiagonalAbsForwardAction alpha (n + 1)
              (highamBidiagonalUInv alpha (n + 1))
              (fun l => |q l|) k) i +
        highamBidiagonalEq56PropagationQuadraticRemainder
          fp alpha n qhat i +
        highamBidiagonalEq56CrossQuadraticRemainder
          fp alpha n qhat rhat i := by
  dsimp only
  let q := highamBidiagonalExactSolve alpha a
  let qhat := flHighamBidiagonalSolve fp alpha a
  let qtail : Fin n → ℝ := fun j =>
    q ⟨j.val + 1, Nat.succ_lt_succ j.isLt⟩
  let qhatTail : Fin n → ℝ := fun j =>
    qhat ⟨j.val + 1, Nat.succ_lt_succ j.isLt⟩
  let r := highamBidiagonalExactSolve alpha qtail
  let rhat := flHighamBidiagonalSolve fp alpha qhatTail
  change ∀ i : Fin n,
    |r i - rhat i| ≤
      fp.u * highamBidiagonalAbsForwardAction alpha n
        (highamBidiagonalUInv alpha n) (fun k => |r k|) i +
      fp.u * highamBidiagonalAbsTailInverseAction alpha n
        (fun k =>
          highamBidiagonalAbsForwardAction alpha (n + 1)
            (highamBidiagonalUInv alpha (n + 1))
            (fun l => |q l|) k) i +
      highamBidiagonalEq56PropagationQuadraticRemainder
        fp alpha n qhat i +
      highamBidiagonalEq56CrossQuadraticRemainder
        fp alpha n qhat rhat i
  intro i
  let firstMajorant : Fin (n + 1) → ℝ := fun k =>
    highamBidiagonalForwardErrorMajorant alpha (n + 1)
      (highamBidiagonalUInv alpha (n + 1)) fp.u qhat k
  let secondMajorant : Fin n → ℝ := fun k =>
    highamBidiagonalForwardErrorMajorant alpha n
      (highamBidiagonalUInv alpha n) fp.u rhat k
  let E : Fin n → ℝ := fun k =>
    highamBidiagonalAbsTailInverseAction alpha n firstMajorant k +
      secondMajorant k
  have hbase : ∀ k : Fin n, |r k - rhat k| ≤ E k := by
    intro k
    simpa [q, qhat, qtail, qhatTail, r, rhat, E, firstMajorant,
      secondMajorant, highamBidiagonalAbsTailInverseAction,
      highamBidiagonalAbsInverseAction] using
      flHighamBidiagonalSolve_two_sweeps_forward_error
        fp alpha a haddInv k
  have hfirst : ∀ k : Fin (n + 1),
      firstMajorant k ≤
        fp.u * highamBidiagonalAbsForwardAction alpha (n + 1)
          (highamBidiagonalUInv alpha (n + 1)) (fun l => |q l|) k +
        highamBidiagonalEq55QuadraticRemainder fp alpha (n + 1) qhat k := by
    intro k
    simpa [q, qhat, firstMajorant] using
      flHighamBidiagonalSolve_forward_majorant_first_order_quadratic
        fp alpha a haddInv k
  have hprop :
      highamBidiagonalAbsTailInverseAction alpha n firstMajorant i ≤
        fp.u * highamBidiagonalAbsTailInverseAction alpha n
          (fun k =>
            highamBidiagonalAbsForwardAction alpha (n + 1)
              (highamBidiagonalUInv alpha (n + 1))
              (fun l => |q l|) k) i +
        highamBidiagonalEq56PropagationQuadraticRemainder
          fp alpha n qhat i := by
    have hm := highamBidiagonalAbsInverseAction_mono n
      (highamBidiagonalUInv alpha n)
      (fun j => hfirst ⟨j.val + 1, Nat.succ_lt_succ j.isLt⟩) i
    calc
      highamBidiagonalAbsTailInverseAction alpha n firstMajorant i ≤
          highamBidiagonalAbsInverseAction n
            (highamBidiagonalUInv alpha n)
            (fun j =>
              fp.u * highamBidiagonalAbsForwardAction alpha (n + 1)
                (highamBidiagonalUInv alpha (n + 1))
                (fun l => |q l|)
                ⟨j.val + 1, Nat.succ_lt_succ j.isLt⟩ +
              highamBidiagonalEq55QuadraticRemainder fp alpha (n + 1)
                qhat ⟨j.val + 1, Nat.succ_lt_succ j.isLt⟩) i := by
            simpa [highamBidiagonalAbsTailInverseAction] using hm
      _ = fp.u * highamBidiagonalAbsTailInverseAction alpha n
            (fun k =>
              highamBidiagonalAbsForwardAction alpha (n + 1)
                (highamBidiagonalUInv alpha (n + 1))
                (fun l => |q l|) k) i +
          highamBidiagonalEq56PropagationQuadraticRemainder
            fp alpha n qhat i := by
        rw [highamBidiagonalAbsInverseAction_add,
          highamBidiagonalAbsInverseAction_smul]
        unfold highamBidiagonalEq55QuadraticRemainder
          highamBidiagonalEq56PropagationQuadraticRemainder
          highamBidiagonalAbsTailInverseAction
        rw [highamBidiagonalAbsInverseAction_smul]
  have hEform : ∀ k : Fin n,
      E k = fp.u *
        (highamBidiagonalAbsTailInverseAction alpha n
            (fun j =>
              highamBidiagonalAbsForwardAction alpha (n + 1)
                (highamBidiagonalUInv alpha (n + 1))
                (fun l => |qhat l|) j) k +
          highamBidiagonalAbsForwardAction alpha n
            (highamBidiagonalUInv alpha n) (fun j => |rhat j|) k) := by
    intro k
    unfold E firstMajorant secondMajorant
      highamBidiagonalAbsTailInverseAction
    simp_rw [highamBidiagonalForwardErrorMajorant_eq_absForwardAction]
    rw [highamBidiagonalAbsInverseAction_smul]
    ring
  have hrhat : ∀ k : Fin n, |rhat k| ≤ |r k| + E k := by
    intro k
    calc
      |rhat k| = |r k + (rhat k - r k)| := by congr 1 <;> ring
      _ ≤ |r k| + |rhat k - r k| := abs_add_le _ _
      _ = |r k| + |r k - rhat k| := by rw [abs_sub_comm]
      _ ≤ |r k| + E k := add_le_add (le_refl _) (hbase k)
  have hsecond : secondMajorant i ≤
      fp.u * highamBidiagonalAbsForwardAction alpha n
        (highamBidiagonalUInv alpha n) (fun k => |r k|) i +
      highamBidiagonalEq56CrossQuadraticRemainder
        fp alpha n qhat rhat i := by
    have hm := highamBidiagonalAbsForwardAction_mono alpha n
      (highamBidiagonalUInv alpha n) hrhat i
    have huscaled := mul_le_mul_of_nonneg_left hm fp.u_nonneg
    unfold secondMajorant
    rw [highamBidiagonalForwardErrorMajorant_eq_absForwardAction]
    calc
      fp.u * highamBidiagonalAbsForwardAction alpha n
          (highamBidiagonalUInv alpha n) (fun k => |rhat k|) i ≤
        fp.u * highamBidiagonalAbsForwardAction alpha n
          (highamBidiagonalUInv alpha n) (fun k => |r k| + E k) i :=
        huscaled
      _ = fp.u * highamBidiagonalAbsForwardAction alpha n
            (highamBidiagonalUInv alpha n) (fun k => |r k|) i +
          highamBidiagonalEq56CrossQuadraticRemainder
            fp alpha n qhat rhat i := by
        rw [highamBidiagonalAbsForwardAction_add]
        have hEfun : E = fun k => fp.u *
            (highamBidiagonalAbsTailInverseAction alpha n
                (fun j =>
                  highamBidiagonalAbsForwardAction alpha (n + 1)
                    (highamBidiagonalUInv alpha (n + 1))
                    (fun l => |qhat l|) j) k +
              highamBidiagonalAbsForwardAction alpha n
                (highamBidiagonalUInv alpha n) (fun j => |rhat j|) k) := by
          funext k
          exact hEform k
        rw [hEfun, highamBidiagonalAbsForwardAction_smul]
        unfold highamBidiagonalEq56CrossQuadraticRemainder
        ring
  calc
    |r i - rhat i| ≤
        highamBidiagonalAbsTailInverseAction alpha n firstMajorant i +
          secondMajorant i := hbase i
    _ ≤
        (fp.u * highamBidiagonalAbsTailInverseAction alpha n
            (fun k =>
              highamBidiagonalAbsForwardAction alpha (n + 1)
                (highamBidiagonalUInv alpha (n + 1))
                (fun l => |q l|) k) i +
          highamBidiagonalEq56PropagationQuadraticRemainder
            fp alpha n qhat i) +
        (fp.u * highamBidiagonalAbsForwardAction alpha n
            (highamBidiagonalUInv alpha n) (fun k => |r k|) i +
          highamBidiagonalEq56CrossQuadraticRemainder
            fp alpha n qhat rhat i) := add_le_add hprop hsecond
    _ = fp.u * highamBidiagonalAbsForwardAction alpha n
          (highamBidiagonalUInv alpha n) (fun k => |r k|) i +
        fp.u * highamBidiagonalAbsTailInverseAction alpha n
          (fun k =>
            highamBidiagonalAbsForwardAction alpha (n + 1)
              (highamBidiagonalUInv alpha (n + 1))
              (fun l => |q l|) k) i +
        highamBidiagonalEq56PropagationQuadraticRemainder
          fp alpha n qhat i +
        highamBidiagonalEq56CrossQuadraticRemainder
          fp alpha n qhat rhat i := by ring

end NumStability
