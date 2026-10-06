import Mathlib.Data.List.TakeDrop
import Mathlib.Data.Real.Basic
import Mathlib.Tactic
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Ring
import NumStability.Analysis.FloatingPointArithmetic.IeeeSpecialValueOperations.Results
import NumStability.Analysis.ForwardError
import NumStability.Analysis.MatrixAlgebra
import NumStability.Analysis.Rounding
import NumStability.FloatingPoint.Model
import NumStability.Source.Higham.Chapter05.Section01.Horner.Basic
import NumStability.Source.Higham.Chapter05.Section02.DerivativeEvaluation.Bidiagonal
import NumStability.Source.Higham.Chapter05.Section03.DividedDifferences.Basic
import NumStability.Source.Higham.Chapter05.Section03.ResidualUnwind.Basic

/-!
# Chapter05 Section02 BidiagonalDerivativeAnalysis Basic

Canonical destination for material split out of
`NumStability.Algorithms.Ch5SourceClosure` by wave W12 of the August 2026 repository reorganization.
Declaration names, statements and proofs are unchanged; only the
module they live in has changed. The historical module still
resolves and re-exports this one.
-/

open scoped BigOperators

namespace NumStability

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

/-- Exact bidiagonal solution `q = U_n(α)⁻¹ a`. -/
noncomputable def highamBidiagonalExactSolve
    (alpha : ℝ) {n : ℕ} (a : Fin n → ℝ) : Fin n → ℝ :=
  fun i => ∑ j : Fin n, highamBidiagonalUInv alpha n i j * a j

/-- The actual rounded upper-bidiagonal solve used by Algorithm 5.2, in the
source's ascending coefficient order.  Entry `i` is rounded Horner evaluation
of the suffix `a_i,…,a_{n-1}`, processed from high to low degree. -/
noncomputable def flHighamBidiagonalSolve
    (fp : FPModel) (alpha : ℝ) {n : ℕ}
    (a : Fin n → ℝ) (i : Fin n) : ℝ :=
  fl_hornerDesc fp alpha ((List.ofFn a).drop i.val).reverse

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
