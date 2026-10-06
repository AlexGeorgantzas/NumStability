-- Algorithms/Ch5SourceClosure.lean
--
-- Literal source-form closure for Higham, 2nd ed., Chapter 5:
-- equations (5.5), (5.6), and the actual rounded producer behind (5.12).

import Mathlib.Tactic
import Mathlib.Data.List.TakeDrop
import NumStability.Algorithms.Ch5NewtonForm

namespace NumStability

open scoped BigOperators

/-! ## Literal bidiagonal systems in (5.5) and (5.6) -/

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

/-- The explicit inverse displayed below (5.6): entry `(i,j)` is
`alpha^(j-i)` on and above the diagonal and zero below it. -/
noncomputable def highamBidiagonalUInv (alpha : ℝ) (n : ℕ) :
    Fin n → Fin n → ℝ := fun i j =>
  if i.val ≤ j.val then alpha ^ (j.val - i.val) else 0

/-- The first matrix displayed below Higham (5.6), in entrywise form:
`|U_n⁻¹|` has entries `|alpha|^(j-i)` on and above the diagonal and zero
below it. -/
theorem highamBidiagonalUInv_abs_entry
    (alpha : ℝ) (n : ℕ) (i j : Fin n) :
    |highamBidiagonalUInv alpha n i j| =
      if i.val ≤ j.val then |alpha| ^ (j.val - i.val) else 0 := by
  simp only [highamBidiagonalUInv]
  split_ifs <;> simp [abs_pow]

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

/-- The convolution of two copies of the explicit upper-triangular inverse.
It is the finite-sum bridge needed for the third matrix displayed below (5.6). -/
theorem highamBidiagonalUInv_square_entry
    (r : ℝ) (n : ℕ) (i j : Fin n) :
    (∑ k : Fin n,
      highamBidiagonalUInv r n i k * highamBidiagonalUInv r n k j) =
      if i.val ≤ j.val then
        ((j.val - i.val + 1 : ℕ) : ℝ) * r ^ (j.val - i.val)
      else 0 := by
  by_cases hij : i.val ≤ j.val
  · rw [if_pos hij]
    have hterm : ∀ k : Fin n,
        highamBidiagonalUInv r n i k * highamBidiagonalUInv r n k j =
          if k ∈ Finset.Icc i j then r ^ (j.val - i.val) else 0 := by
      intro k
      by_cases hk : k ∈ Finset.Icc i j
      · have hkij : i.val ≤ k.val ∧ k.val ≤ j.val := by
          simpa using (Finset.mem_Icc.mp hk)
        simp [highamBidiagonalUInv, hk, hkij.1, hkij.2]
        rw [← pow_add]
        congr 1
        omega
      · have hnot : ¬(i.val ≤ k.val ∧ k.val ≤ j.val) := by
          intro h
          apply hk
          exact Finset.mem_Icc.mpr ⟨by simpa using h.1, by simpa using h.2⟩
        simp only [highamBidiagonalUInv, hk, if_false]
        by_cases hik : i.val ≤ k.val
        · have hkj : ¬k.val ≤ j.val := by tauto
          simp [hik, hkj]
        · simp [hik]
    calc
      (∑ k : Fin n,
        highamBidiagonalUInv r n i k * highamBidiagonalUInv r n k j) =
          ∑ k : Fin n,
            if k ∈ Finset.Icc i j then r ^ (j.val - i.val) else 0 := by
              apply Finset.sum_congr rfl
              intro k _hk
              exact hterm k
      _ = ∑ k ∈ Finset.Icc i j, r ^ (j.val - i.val) := by
        have hfilter :
            Finset.univ.filter (fun k : Fin n => k ∈ Finset.Icc i j) =
              Finset.Icc i j := by
          ext k
          simp
        rw [← Finset.sum_filter]
        rw [hfilter]
      _ = ((j.val - i.val + 1 : ℕ) : ℝ) * r ^ (j.val - i.val) := by
        have hcard : j.val + 1 - i.val = j.val - i.val + 1 := by omega
        rw [Finset.sum_const, Fin.card_Icc]
        simp [hcard, nsmul_eq_mul]
  · rw [if_neg hij]
    apply Finset.sum_eq_zero
    intro k _hk
    by_cases hik : i.val ≤ k.val
    · have hkj : ¬k.val ≤ j.val := by omega
      simp [highamBidiagonalUInv, hik, hkj]
    · simp [highamBidiagonalUInv, hik]

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

/-- Exact bidiagonal solution `q = U_n(α)⁻¹ a`. -/
noncomputable def highamBidiagonalExactSolve
    (alpha : ℝ) {n : ℕ} (a : Fin n → ℝ) : Fin n → ℝ :=
  fun i => ∑ j : Fin n, highamBidiagonalUInv alpha n i j * a j

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

/-- The actual rounded upper-bidiagonal solve used by Algorithm 5.2, in the
source's ascending coefficient order.  Entry `i` is rounded Horner evaluation
of the suffix `a_i,…,a_{n-1}`, processed from high to low degree. -/
noncomputable def flHighamBidiagonalSolve
    (fp : FPModel) (alpha : ℝ) {n : ℕ}
    (a : Fin n → ℝ) (i : Fin n) : ℝ :=
  fl_hornerDesc fp alpha ((List.ofFn a).drop i.val).reverse

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

theorem flHighamBidiagonalSolve_last
    (fp : FPModel) (alpha : ℝ) {n : ℕ}
    (a : Fin n → ℝ) (i : Fin n) (hi : i.val + 1 = n) :
    flHighamBidiagonalSolve fp alpha a i = a i := by
  let l := List.ofFn a
  have hil : i.val < l.length := by simpa [l] using i.isLt
  have hdrop := List.drop_eq_getElem_cons hil
  have htail : (List.ofFn a).drop (i.val + 1) = [] := by
    apply List.drop_eq_nil_of_le
    simp [hi]
  have hget : l[i.val] = a i := by
    simpa [l] using List.getElem_ofFn (f := a) hil
  unfold flHighamBidiagonalSolve
  rw [hdrop, htail]
  simp [fl_hornerDesc, hget]

/-- The concrete bidiagonal perturbation generated by the actual rounded
Horner sweep.  Its diagonal stores the inverse-addition (2.5) error and its
superdiagonal stores the multiplication (2.4) error. -/
noncomputable def flHighamBidiagonalDelta
    (fp : FPModel) (alpha : ℝ) {n : ℕ}
    (a : Fin n → ℝ)
    (haddInv : ∀ x y : ℝ,
      inverseRelErrorModel (fp.fl_add x y) (x + y) fp.u) :
    Fin n → Fin n → ℝ := by
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
  exact fun i j =>
    if j = i then eps i
    else if j.val = i.val + 1 then -alpha * delta i
    else 0

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

/-- The positive matrix action `|U⁻¹| |U| v` occurring in (5.5).
Naming the action makes the exact first-order/quadratic split below readable. -/
noncomputable def highamBidiagonalAbsForwardAction
    (alpha : ℝ) (n : ℕ) (Uinv : Fin n → Fin n → ℝ)
    (v : Fin n → ℝ) : Fin n → ℝ :=
  fun i =>
    ∑ j : Fin n,
      |Uinv i j| *
        (∑ k : Fin n, |highamBidiagonalU alpha n j k| * v k)

theorem highamBidiagonalForwardErrorMajorant_eq_absForwardAction
    (alpha : ℝ) (n : ℕ) (Uinv : Fin n → Fin n → ℝ)
    (epsilon : ℝ) (qhat : Fin n → ℝ) (i : Fin n) :
    highamBidiagonalForwardErrorMajorant alpha n Uinv epsilon qhat i =
      epsilon * highamBidiagonalAbsForwardAction alpha n Uinv
        (fun k => |qhat k|) i := by
  rfl

theorem highamBidiagonalAbsForwardAction_mono
    (alpha : ℝ) (n : ℕ) (Uinv : Fin n → Fin n → ℝ)
    {v w : Fin n → ℝ} (hvw : ∀ k, v k ≤ w k) (i : Fin n) :
    highamBidiagonalAbsForwardAction alpha n Uinv v i ≤
      highamBidiagonalAbsForwardAction alpha n Uinv w i := by
  unfold highamBidiagonalAbsForwardAction
  apply Finset.sum_le_sum
  intro j _hj
  apply mul_le_mul_of_nonneg_left _ (abs_nonneg (Uinv i j))
  apply Finset.sum_le_sum
  intro k _hk
  exact mul_le_mul_of_nonneg_left (hvw k)
    (abs_nonneg (highamBidiagonalU alpha n j k))

theorem highamBidiagonalAbsForwardAction_nonneg
    (alpha : ℝ) (n : ℕ) (Uinv : Fin n → Fin n → ℝ)
    {v : Fin n → ℝ} (hv : ∀ k, 0 ≤ v k) (i : Fin n) :
    0 ≤ highamBidiagonalAbsForwardAction alpha n Uinv v i := by
  unfold highamBidiagonalAbsForwardAction
  apply Finset.sum_nonneg
  intro j _hj
  apply mul_nonneg (abs_nonneg (Uinv i j))
  apply Finset.sum_nonneg
  intro k _hk
  exact mul_nonneg (abs_nonneg (highamBidiagonalU alpha n j k)) (hv k)

theorem highamBidiagonalAbsForwardAction_add
    (alpha : ℝ) (n : ℕ) (Uinv : Fin n → Fin n → ℝ)
    (v w : Fin n → ℝ) (i : Fin n) :
    highamBidiagonalAbsForwardAction alpha n Uinv (fun k => v k + w k) i =
      highamBidiagonalAbsForwardAction alpha n Uinv v i +
        highamBidiagonalAbsForwardAction alpha n Uinv w i := by
  simp only [highamBidiagonalAbsForwardAction, mul_add,
    Finset.sum_add_distrib]

theorem highamBidiagonalAbsForwardAction_smul
    (alpha : ℝ) (n : ℕ) (Uinv : Fin n → Fin n → ℝ)
    (c : ℝ) (v : Fin n → ℝ) (i : Fin n) :
    highamBidiagonalAbsForwardAction alpha n Uinv (fun k => c * v k) i =
      c * highamBidiagonalAbsForwardAction alpha n Uinv v i := by
  unfold highamBidiagonalAbsForwardAction
  calc
    (∑ j : Fin n, |Uinv i j| *
        (∑ k : Fin n,
          |highamBidiagonalU alpha n j k| * (c * v k))) =
        ∑ j : Fin n, c *
          (|Uinv i j| *
            (∑ k : Fin n,
              |highamBidiagonalU alpha n j k| * v k)) := by
          apply Finset.sum_congr rfl
          intro j _hj
          have hinner :
              (∑ k : Fin n,
                |highamBidiagonalU alpha n j k| * (c * v k)) =
                c * (∑ k : Fin n,
                  |highamBidiagonalU alpha n j k| * v k) := by
            calc
              (∑ k : Fin n,
                |highamBidiagonalU alpha n j k| * (c * v k)) =
                  ∑ k : Fin n, c *
                    (|highamBidiagonalU alpha n j k| * v k) := by
                    apply Finset.sum_congr rfl
                    intro k _hk
                    ring
              _ = c * (∑ k : Fin n,
                    |highamBidiagonalU alpha n j k| * v k) := by
                    rw [Finset.mul_sum]
          rw [hinner]
          ring
    _ = c * (∑ j : Fin n, |Uinv i j| *
          (∑ k : Fin n,
            |highamBidiagonalU alpha n j k| * v k)) := by
          rw [Finset.mul_sum]

/-- The exact quadratic remainder hidden by `O(u²)` in (5.5):
`u² (|U⁻¹||U|)² |q̂|`. -/
noncomputable def highamBidiagonalEq55QuadraticRemainder
    (fp : FPModel) (alpha : ℝ) (n : ℕ)
    (qhat : Fin n → ℝ) : Fin n → ℝ :=
  fun i => fp.u ^ 2 *
    highamBidiagonalAbsForwardAction alpha n
      (highamBidiagonalUInv alpha n)
      (fun k =>
        highamBidiagonalAbsForwardAction alpha n
          (highamBidiagonalUInv alpha n) (fun l => |qhat l|) k) i

theorem highamBidiagonalEq55QuadraticRemainder_nonneg
    (fp : FPModel) (alpha : ℝ) (n : ℕ)
    (qhat : Fin n → ℝ) (i : Fin n) :
    0 ≤ highamBidiagonalEq55QuadraticRemainder fp alpha n qhat i := by
  unfold highamBidiagonalEq55QuadraticRemainder
  apply mul_nonneg (sq_nonneg fp.u)
  apply highamBidiagonalAbsForwardAction_nonneg
  intro k
  apply highamBidiagonalAbsForwardAction_nonneg
  intro l
  exact abs_nonneg (qhat l)

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

/-- Positive action of an entrywise absolute inverse matrix. -/
noncomputable def highamBidiagonalAbsInverseAction
    (n : ℕ) (Uinv : Fin n → Fin n → ℝ)
    (v : Fin n → ℝ) : Fin n → ℝ :=
  fun i => ∑ j : Fin n, |Uinv i j| * v j

theorem highamBidiagonalAbsInverseAction_mono
    (n : ℕ) (Uinv : Fin n → Fin n → ℝ)
    {v w : Fin n → ℝ} (hvw : ∀ j, v j ≤ w j) (i : Fin n) :
    highamBidiagonalAbsInverseAction n Uinv v i ≤
      highamBidiagonalAbsInverseAction n Uinv w i := by
  unfold highamBidiagonalAbsInverseAction
  apply Finset.sum_le_sum
  intro j _hj
  exact mul_le_mul_of_nonneg_left (hvw j) (abs_nonneg (Uinv i j))

theorem highamBidiagonalAbsInverseAction_nonneg
    (n : ℕ) (Uinv : Fin n → Fin n → ℝ)
    {v : Fin n → ℝ} (hv : ∀ j, 0 ≤ v j) (i : Fin n) :
    0 ≤ highamBidiagonalAbsInverseAction n Uinv v i := by
  unfold highamBidiagonalAbsInverseAction
  exact Finset.sum_nonneg fun j _hj =>
    mul_nonneg (abs_nonneg (Uinv i j)) (hv j)

theorem highamBidiagonalAbsInverseAction_add
    (n : ℕ) (Uinv : Fin n → Fin n → ℝ)
    (v w : Fin n → ℝ) (i : Fin n) :
    highamBidiagonalAbsInverseAction n Uinv (fun j => v j + w j) i =
      highamBidiagonalAbsInverseAction n Uinv v i +
        highamBidiagonalAbsInverseAction n Uinv w i := by
  simp only [highamBidiagonalAbsInverseAction, mul_add,
    Finset.sum_add_distrib]

theorem highamBidiagonalAbsInverseAction_smul
    (n : ℕ) (Uinv : Fin n → Fin n → ℝ)
    (c : ℝ) (v : Fin n → ℝ) (i : Fin n) :
    highamBidiagonalAbsInverseAction n Uinv (fun j => c * v j) i =
      c * highamBidiagonalAbsInverseAction n Uinv v i := by
  unfold highamBidiagonalAbsInverseAction
  calc
    (∑ j : Fin n, |Uinv i j| * (c * v j)) =
        ∑ j : Fin n, c * (|Uinv i j| * v j) := by
          apply Finset.sum_congr rfl
          intro j _hj
          ring
    _ = c * (∑ j : Fin n, |Uinv i j| * v j) := by
          rw [Finset.mul_sum]

/-- Propagate a vector indexed by the first `(n+1)`-system through the
absolute inverse of the second `n`-system, dropping the first quotient entry. -/
noncomputable def highamBidiagonalAbsTailInverseAction
    (alpha : ℝ) (n : ℕ) (v : Fin (n + 1) → ℝ) : Fin n → ℝ :=
  highamBidiagonalAbsInverseAction n (highamBidiagonalUInv alpha n)
    (fun j => v ⟨j.val + 1, Nat.succ_lt_succ j.isLt⟩)

/-- The `q̂`-to-`q` propagation part of the exact `O(u²)` remainder in
(5.6). -/
noncomputable def highamBidiagonalEq56PropagationQuadraticRemainder
    (fp : FPModel) (alpha : ℝ) (n : ℕ)
    (qhat : Fin (n + 1) → ℝ) : Fin n → ℝ :=
  fun i => fp.u ^ 2 *
    highamBidiagonalAbsTailInverseAction alpha n
      (fun k =>
        highamBidiagonalAbsForwardAction alpha (n + 1)
          (highamBidiagonalUInv alpha (n + 1))
          (fun l =>
            highamBidiagonalAbsForwardAction alpha (n + 1)
              (highamBidiagonalUInv alpha (n + 1))
              (fun s => |qhat s|) l) k) i

/-- The cross/sweep-feedback part of the exact `O(u²)` remainder in (5.6).
It is `u² |U_n⁻¹||U_n|` applied to the sum of the first-sweep
propagation majorant and the second-sweep computed-vector majorant. -/
noncomputable def highamBidiagonalEq56CrossQuadraticRemainder
    (fp : FPModel) (alpha : ℝ) (n : ℕ)
    (qhat : Fin (n + 1) → ℝ) (rhat : Fin n → ℝ) : Fin n → ℝ :=
  fun i => fp.u ^ 2 *
    highamBidiagonalAbsForwardAction alpha n
      (highamBidiagonalUInv alpha n)
      (fun k =>
        highamBidiagonalAbsTailInverseAction alpha n
          (fun j =>
            highamBidiagonalAbsForwardAction alpha (n + 1)
              (highamBidiagonalUInv alpha (n + 1))
              (fun l => |qhat l|) j) k +
        highamBidiagonalAbsForwardAction alpha n
          (highamBidiagonalUInv alpha n) (fun j => |rhat j|) k) i

theorem highamBidiagonalEq56QuadraticRemainders_nonneg
    (fp : FPModel) (alpha : ℝ) (n : ℕ)
    (qhat : Fin (n + 1) → ℝ) (rhat : Fin n → ℝ) (i : Fin n) :
    0 ≤ highamBidiagonalEq56PropagationQuadraticRemainder
        fp alpha n qhat i ∧
      0 ≤ highamBidiagonalEq56CrossQuadraticRemainder
        fp alpha n qhat rhat i := by
  constructor
  · unfold highamBidiagonalEq56PropagationQuadraticRemainder
    apply mul_nonneg (sq_nonneg fp.u)
    unfold highamBidiagonalAbsTailInverseAction
    apply highamBidiagonalAbsInverseAction_nonneg
    intro j
    apply highamBidiagonalAbsForwardAction_nonneg
    intro k
    apply highamBidiagonalAbsForwardAction_nonneg
    intro l
    exact abs_nonneg (qhat l)
  · unfold highamBidiagonalEq56CrossQuadraticRemainder
    apply mul_nonneg (sq_nonneg fp.u)
    apply highamBidiagonalAbsForwardAction_nonneg
    intro k
    apply add_nonneg
    · unfold highamBidiagonalAbsTailInverseAction
      apply highamBidiagonalAbsInverseAction_nonneg
      intro j
      apply highamBidiagonalAbsForwardAction_nonneg
      intro l
      exact abs_nonneg (qhat l)
    · apply highamBidiagonalAbsForwardAction_nonneg
      intro j
      exact abs_nonneg (rhat j)

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

/-! ## The concrete inverse unwind behind (5.12) -/

/-- Under the standard model, a nonzero exact subtraction cannot round to
zero once `u < 1`.  `gammaValid fp 3` supplies that strict bound, so the
rounded-denominator nonbreakdown condition in the divided-difference unwind is
derived rather than imposed on the final (5.12) theorem. -/
theorem fl_sub_ne_zero_of_exact_ne_zero_of_gammaValid_three
    (fp : FPModel) (x y : ℝ) (hxy : x - y ≠ 0)
    (hγ : gammaValid fp 3) :
    fp.fl_sub x y ≠ 0 := by
  obtain ⟨delta, hdelta, hfl⟩ := fp.model_sub x y
  rw [hfl]
  apply mul_ne_zero hxy
  have hvalid1 : gammaValid fp 1 :=
    gammaValid_mono fp (by omega) hγ
  have hu : fp.u < 1 := by
    unfold gammaValid at hvalid1
    simpa using hvalid1
  have hdeltaLower : -fp.u ≤ delta := (abs_le.mp hdelta).1
  have hpos : 0 < 1 + delta := by linarith
  exact hpos.ne'

/-- One active entry of the actual rounded divided-difference recurrence has
both the forward `G_k` factor from (5.9) and its inverse factor used when the
analysis is unwound.  Both are genuine three-operation Stewart counters, so
both deviations from one are bounded by `gamma_3`; the inverse factor is not
obtained by the weaker estimate `gamma_3 / (1-gamma_3)`. -/
theorem fl_dividedDifferenceStep_entry_forward_inverse_gamma3
    (fp : FPModel) (nodes coeffs : ℕ → ℝ) {k j : ℕ}
    (hj : k < j)
    (hden : nodes j - nodes (j - k - 1) ≠ 0)
    (hdenHat : fp.fl_sub (nodes j) (nodes (j - k - 1)) ≠ 0)
    (hγ : gammaValid fp 3) :
    ∃ eta rho : ℝ,
      |eta - 1| ≤ gamma fp 3 ∧
      |rho - 1| ≤ gamma fp 3 ∧
      rho * eta = 1 ∧
      fl_dividedDifferenceStep fp nodes coeffs k j =
        eta * dividedDifferenceStep nodes coeffs k j := by
  rcases fl_dividedDifferenceStep_entry_error_factors
      fp nodes coeffs hj hden hdenHat with
    ⟨δnum, δden, δdiv, hδnum, hδden, hδdiv, hstep⟩
  let δ : Fin 3 → ℝ := fun i =>
    if i = 0 then δnum else if i = 1 then δden else δdiv
  let forwardNeg : Fin 3 → Bool := fun i => if i = 1 then true else false
  let inverseNeg : Fin 3 → Bool := fun i => if i = 1 then false else true
  have hδ : ∀ i : Fin 3, |δ i| ≤ fp.u := by
    intro i
    fin_cases i <;> simp [δ, hδnum, hδden, hδdiv]
  rcases prod_signed_error_bound fp 3 δ forwardNeg hδ hγ with
    ⟨thetaF, hthetaF, hforward⟩
  rcases prod_signed_error_bound fp 3 δ inverseNeg hδ hγ with
    ⟨thetaI, hthetaI, hinverse⟩
  let eta := ∏ i : Fin 3,
    (if forwardNeg i then 1 / (1 + δ i) else 1 + δ i)
  let rho := ∏ i : Fin 3,
    (if inverseNeg i then 1 / (1 + δ i) else 1 + δ i)
  have heta : eta =
      (1 + δnum) * (1 / (1 + δden)) * (1 + δdiv) := by
    simp [eta, forwardNeg, δ, Fin.prod_univ_three]
  have hrho : rho =
      (1 / (1 + δnum)) * (1 + δden) * (1 / (1 + δdiv)) := by
    simp [rho, inverseNeg, δ, Fin.prod_univ_three]
  have h1valid : gammaValid fp 1 :=
    gammaValid_mono fp (by omega) hγ
  have hu : fp.u < 1 := by
    unfold gammaValid at h1valid
    simpa using h1valid
  have hnum : 1 + δnum ≠ 0 := by
    have : 0 < 1 + δnum := by linarith [neg_abs_le δnum]
    exact this.ne'
  have hdenFactor : 1 + δden ≠ 0 := by
    have : 0 < 1 + δden := by linarith [neg_abs_le δden]
    exact this.ne'
  have hdiv : 1 + δdiv ≠ 0 := by
    have : 0 < 1 + δdiv := by linarith [neg_abs_le δdiv]
    exact this.ne'
  refine ⟨eta, rho, ?_, ?_, ?_, ?_⟩
  · have : eta = 1 + thetaF := by simpa [eta] using hforward
    rw [this]
    simpa using hthetaF
  · have : rho = 1 + thetaI := by simpa [rho] using hinverse
    rw [this]
    simpa using hthetaI
  · rw [heta, hrho]
    field_simp [hnum, hdenFactor, hdiv]
  · rw [hstep, heta]
    simp [div_eq_mul_inv]
    ring

/-- Higham, 2nd ed., Chapter 5, Section 5.3, equation (5.12), one active
entry of the inverse unwind.  The inverse factor is extracted from the three
rounded operations that produced the entry; it is not a caller-supplied
perturbation certificate. -/
theorem fl_dividedDifferenceStep_entry_inverse_gamma3
    (fp : FPModel) (nodes coeffs : ℕ → ℝ) {k j : ℕ}
    (hj : k < j)
    (hden : nodes j - nodes (j - k - 1) ≠ 0)
    (hdenHat : fp.fl_sub (nodes j) (nodes (j - k - 1)) ≠ 0)
    (hγ : gammaValid fp 3) :
    ∃ rho : ℝ,
      |rho - 1| ≤ gamma fp 3 ∧
      rho * fl_dividedDifferenceStep fp nodes coeffs k j =
        dividedDifferenceStep nodes coeffs k j := by
  rcases fl_dividedDifferenceStep_entry_forward_inverse_gamma3
      fp nodes coeffs hj hden hdenHat hγ with
    ⟨eta, rho, _heta, hrho, hinv, hstep⟩
  refine ⟨rho, hrho, ?_⟩
  rw [hstep]
  calc
    rho * (eta * dividedDifferenceStep nodes coeffs k j) =
        (rho * eta) * dividedDifferenceStep nodes coeffs k j := by ring
    _ = dividedDifferenceStep nodes coeffs k j := by rw [hinv]; ring

/-- The source inverse step `L_k⁻¹ G_k⁻¹`.  The supplied `rho j`
is the concrete inverse Stewart factor for active row `j`; inactive rows are
left unchanged by `dividedDifferenceGMatrixAction`. -/
noncomputable def flDividedDifferenceUnwindStep
    (nodes : ℕ → ℝ) (rho : ℕ → ℝ) (n : ℕ)
    (k : ℕ) (v : Fin (n + 1) → ℝ) : Fin (n + 1) → ℝ :=
  dividedDifferenceLInvAction nodes n k
    (dividedDifferenceGMatrixAction rho n k v)

/-- `L_k⁻¹ G_k⁻¹` differs componentwise from `L_k⁻¹` by at
most `gamma |L_k⁻¹|`.  This is the literal local perturbation premise
used in Higham's unwind leading to (5.12), now derived from inverse factors. -/
theorem flDividedDifferenceUnwindStep_abs_error
    (nodes : ℕ → ℝ) (rho : ℕ → ℝ) (n k : ℕ)
    (gamma : ℝ) (hgamma : 0 ≤ gamma)
    (hrho : ∀ i : Fin (n + 1), k < i.val →
      |rho i.val - 1| ≤ gamma) :
    ∀ (v : Fin (n + 1) → ℝ) (i : Fin (n + 1)),
      |flDividedDifferenceUnwindStep nodes rho n k v i -
          dividedDifferenceLInvAction nodes n k v i| ≤
        gamma * dividedDifferenceAbsLInvAction nodes n k
          (fun j => |v j|) i := by
  intro v i
  let gv := dividedDifferenceGMatrixAction rho n k v
  have hpoint : ∀ j : Fin (n + 1), |gv j - v j| ≤ gamma * |v j| := by
    intro j
    by_cases hj : j.val ≤ k
    · rw [show gv j = v j by
          simpa [gv] using
            dividedDifferenceGMatrixAction_of_le rho v hj]
      simp [mul_nonneg hgamma (abs_nonneg (v j))]
    · have hgt : k < j.val := Nat.lt_of_not_ge hj
      rw [show gv j = rho j.val * v j by
          simpa [gv] using
            dividedDifferenceGMatrixAction_of_gt rho v hgt]
      have hfactor : rho j.val * v j - v j =
          (rho j.val - 1) * v j := by ring
      rw [hfactor, abs_mul]
      exact mul_le_mul_of_nonneg_right (hrho j hgt) (abs_nonneg (v j))
  have hbase :=
    abs_dividedDifferenceLInvAction_sub_le_absLInvAction
      nodes n k gv v i
  have hmono := dividedDifferenceAbsLInvAction_mono nodes n k
    (fun j => |gv j - v j|) (fun j => gamma * |v j|) hpoint i
  have hsmul := dividedDifferenceAbsLInvAction_smul nodes n k gamma
    (fun j => |v j|) i
  calc
    |flDividedDifferenceUnwindStep nodes rho n k v i -
        dividedDifferenceLInvAction nodes n k v i|
        = |dividedDifferenceLInvAction nodes n k gv i -
            dividedDifferenceLInvAction nodes n k v i| := rfl
    _ ≤ dividedDifferenceAbsLInvAction nodes n k
          (fun j => |gv j - v j|) i := hbase
    _ ≤ dividedDifferenceAbsLInvAction nodes n k
          (fun j => gamma * |v j|) i := hmono
    _ = gamma * dividedDifferenceAbsLInvAction nodes n k
          (fun j => |v j|) i := hsmul

/-- One complete rounded divided-difference sweep can be undone exactly by
`L_k⁻¹ G_k⁻¹`, where every active diagonal entry of `G_k⁻¹` is within
`gamma_3` of one. Both the inverse factors and the equality are constructed
from the actual rounded sweep. -/
theorem fl_dividedDifferenceFiniteCoeffs_succ_exists_unwind_gamma3
    (fp : FPModel) (nodes f : ℕ → ℝ) {n k : ℕ}
    (hden : ∀ j, k < j → j < n + 1 →
      nodes j - nodes (j - k - 1) ≠ 0)
    (hdenHat : ∀ j, k < j → j < n + 1 →
      fp.fl_sub (nodes j) (nodes (j - k - 1)) ≠ 0)
    (hγ : gammaValid fp 3) :
    ∃ rho : ℕ → ℝ,
      (∀ i : Fin (n + 1), k < i.val →
        |rho i.val - 1| ≤ gamma fp 3) ∧
      flDividedDifferenceUnwindStep nodes rho n k
          (fl_dividedDifferenceFiniteCoeffs fp nodes f n (k + 1)) =
        fl_dividedDifferenceFiniteCoeffs fp nodes f n k := by
  classical
  let prev := fl_dividedDifferenceFiniteCoeffs fp nodes f n k
  let rho : ℕ → ℝ := fun j =>
    if hjk : k < j then
      if hjn : j < n + 1 then
        Classical.choose
          (fl_dividedDifferenceStep_entry_inverse_gamma3 fp nodes
            (dividedDifferenceFinToNat prev) hjk
            (hden j hjk hjn) (hdenHat j hjk hjn) hγ)
      else
        1
    else
      1
  have hrho : ∀ i : Fin (n + 1), k < i.val →
      |rho i.val - 1| ≤ gamma fp 3 := by
    intro i hi
    have hspec := Classical.choose_spec
      (fl_dividedDifferenceStep_entry_inverse_gamma3 fp nodes
        (dividedDifferenceFinToNat prev) hi
        (hden i.val hi i.isLt) (hdenHat i.val hi i.isLt) hγ)
    have hile : i.val ≤ n := Nat.lt_succ_iff.mp i.isLt
    simpa [rho, hi, hile] using hspec.1
  have hG :
      dividedDifferenceGMatrixAction rho n k
          (fl_dividedDifferenceFiniteCoeffs fp nodes f n (k + 1)) =
        dividedDifferenceLMatrixAction nodes n k prev := by
    funext i
    by_cases hi : i.val ≤ k
    · rw [dividedDifferenceGMatrixAction_of_le rho _ hi,
        dividedDifferenceLMatrixAction_of_le nodes prev hi]
      change fl_dividedDifferenceStep fp nodes
          (dividedDifferenceFinToNat prev) k i.val = prev i
      rw [fl_dividedDifferenceStep_of_le fp nodes _ hi]
      simp [dividedDifferenceFinToNat, i.isLt]
    · have hgt : k < i.val := Nat.lt_of_not_ge hi
      rw [dividedDifferenceGMatrixAction_of_gt rho _ hgt]
      have hspec := Classical.choose_spec
        (fl_dividedDifferenceStep_entry_inverse_gamma3 fp nodes
          (dividedDifferenceFinToNat prev) hgt
          (hden i.val hgt i.isLt) (hdenHat i.val hgt i.isLt) hγ)
      have hrhoChoose :
          rho i.val = Classical.choose
            (fl_dividedDifferenceStep_entry_inverse_gamma3 fp nodes
              (dividedDifferenceFinToNat prev) hgt
              (hden i.val hgt i.isLt) (hdenHat i.val hgt i.isLt) hγ) := by
        have hile : i.val ≤ n := Nat.lt_succ_iff.mp i.isLt
        simp [rho, hgt, hile]
      rw [hrhoChoose]
      calc
        Classical.choose
              (fl_dividedDifferenceStep_entry_inverse_gamma3 fp nodes
                (dividedDifferenceFinToNat prev) hgt
                (hden i.val hgt i.isLt) (hdenHat i.val hgt i.isLt) hγ) *
            fl_dividedDifferenceFiniteCoeffs fp nodes f n (k + 1) i =
            dividedDifferenceStep nodes (dividedDifferenceFinToNat prev)
              k i.val := by simpa [prev] using hspec.2
        _ = dividedDifferenceLMatrixAction nodes n k prev i := by
          symm
          exact dividedDifferenceLMatrixAction_eq_step nodes prev i
  refine ⟨rho, hrho, ?_⟩
  unfold flDividedDifferenceUnwindStep
  rw [hG]
  funext i
  exact dividedDifferenceLInvAction_LMatrixAction_eq nodes prev
    (fun j hj => hden j.val hj j.isLt) i

/-- The actual rounded divided-difference computation is the reverse product
of the constructed `L_k⁻¹ G_k⁻¹` unwind steps. This is the missing producer
identity behind the formerly conditional residual theorem for (5.12). -/
theorem fl_dividedDifferenceFiniteCoeffs_exists_inverse_unwind_gamma3
    (fp : FPModel) (nodes f : ℕ → ℝ) {n : ℕ} (m : ℕ)
    (hden : ∀ k j, k < j → j < n + 1 →
      nodes j - nodes (j - k - 1) ≠ 0)
    (hdenHat : ∀ k j, k < j → j < n + 1 →
      fp.fl_sub (nodes j) (nodes (j - k - 1)) ≠ 0)
    (hγ : gammaValid fp 3) :
    ∃ rho : ℕ → ℕ → ℝ,
      (∀ k, ∀ i : Fin (n + 1), k < i.val →
        |rho k i.val - 1| ≤ gamma fp 3) ∧
      (fun i : Fin (n + 1) => f i.val) =
        dividedDifferencePerturbedLInvProductAction
          (fun k v => flDividedDifferenceUnwindStep nodes (rho k) n k v)
          m (fl_dividedDifferenceFiniteCoeffs fp nodes f n m) := by
  classical
  let rho : ℕ → ℕ → ℝ := fun k => Classical.choose
    (fl_dividedDifferenceFiniteCoeffs_succ_exists_unwind_gamma3
      fp nodes f (n := n)
      (fun j hj hjn => hden k j hj hjn)
      (fun j hj hjn => hdenHat k j hj hjn) hγ)
  have hrho : ∀ k, ∀ i : Fin (n + 1), k < i.val →
      |rho k i.val - 1| ≤ gamma fp 3 := by
    intro k i hi
    exact (Classical.choose_spec
      (fl_dividedDifferenceFiniteCoeffs_succ_exists_unwind_gamma3
        fp nodes f (n := n)
        (fun j hj hjn => hden k j hj hjn)
        (fun j hj hjn => hdenHat k j hj hjn) hγ)).1 i hi
  have hunwind : ∀ k,
      flDividedDifferenceUnwindStep nodes (rho k) n k
          (fl_dividedDifferenceFiniteCoeffs fp nodes f n (k + 1)) =
        fl_dividedDifferenceFiniteCoeffs fp nodes f n k := by
    intro k
    exact (Classical.choose_spec
      (fl_dividedDifferenceFiniteCoeffs_succ_exists_unwind_gamma3
        fp nodes f (n := n)
        (fun j hj hjn => hden k j hj hjn)
        (fun j hj hjn => hdenHat k j hj hjn) hγ)).2
  refine ⟨rho, hrho, ?_⟩
  induction m with
  | zero => rfl
  | succ m ih =>
      simp only [dividedDifferencePerturbedLInvProductAction]
      rw [hunwind m]
      exact ih

/-- Higham, 2nd ed., Chapter 5, Section 5.3, equation (5.12), instantiated
for the actual rounded divided-difference recurrence. No perturbed inverse
steps or reconstruction equality are hypotheses: both are constructed above
from the three primitive operations in every active recurrence entry. -/
theorem fl_dividedDifferenceFiniteCoeffs_residual_error_bound_gamma3
    (fp : FPModel) (nodes f : ℕ → ℝ) {n : ℕ} (m : ℕ)
    (hden : ∀ k j, k < j → j < n + 1 →
      nodes j - nodes (j - k - 1) ≠ 0)
    (hγ : gammaValid fp 3) :
    ∀ i : Fin (n + 1),
      |f i.val - dividedDifferenceLInvProductAction nodes n m
          (fl_dividedDifferenceFiniteCoeffs fp nodes f n m) i| ≤
        ((1 + gamma fp 3) ^ m - 1) *
          dividedDifferenceAbsLInvProductAction nodes n m
            (fun j =>
              |fl_dividedDifferenceFiniteCoeffs fp nodes f n m j|) i := by
  have hdenHat : ∀ k j, k < j → j < n + 1 →
      fp.fl_sub (nodes j) (nodes (j - k - 1)) ≠ 0 := by
    intro k j hj hjn
    exact fl_sub_ne_zero_of_exact_ne_zero_of_gammaValid_three fp
      (nodes j) (nodes (j - k - 1)) (hden k j hj hjn) hγ
  obtain ⟨rho, hrho, hrecover⟩ :=
    fl_dividedDifferenceFiniteCoeffs_exists_inverse_unwind_gamma3
      fp nodes f m hden hdenHat hγ
  let step : ℕ → (Fin (n + 1) → ℝ) → Fin (n + 1) → ℝ :=
    fun k v => flDividedDifferenceUnwindStep nodes (rho k) n k v
  have hstep : ∀ k v i,
      |step k v i - dividedDifferenceLInvAction nodes n k v i| ≤
        gamma fp 3 * dividedDifferenceAbsLInvAction nodes n k
          (fun j => |v j|) i := by
    intro k v i
    exact flDividedDifferenceUnwindStep_abs_error nodes (rho k) n k
      (gamma fp 3) (gamma_nonneg fp hγ) (hrho k) v i
  apply dividedDifferenceResidual_error_bound nodes m (gamma_nonneg fp hγ)
    step hstep (fun i : Fin (n + 1) => f i.val)
    (fl_dividedDifferenceFiniteCoeffs fp nodes f n m)
  simpa [step] using hrecover

end NumStability
