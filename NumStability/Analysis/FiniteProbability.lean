-- Analysis/FiniteProbability.lean
--
-- Lightweight finite probability spaces and elementary concentration kernels.

import Mathlib.Data.Real.Basic
import Mathlib.Analysis.Calculus.Deriv.MeanValue
import Mathlib.Analysis.Convex.Jensen
import Mathlib.Analysis.SpecialFunctions.ExpDeriv
import Mathlib.Analysis.SpecialFunctions.Log.Basic
import Mathlib.Analysis.SpecialFunctions.Log.Deriv
import Mathlib.Algebra.BigOperators.Group.Finset.Basic
import Mathlib.Algebra.Order.BigOperators.Group.Finset
import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Ring

namespace NumStability

open scoped BigOperators

/-!
## Finite probability spaces

This file provides a small real-valued finite probability interface and the
elementary Markov, Chebyshev, and Chernoff kernels used by algorithm-specific
randomized stability analyses.
-/

/-!
### Scalar exponential inequalities

These elementary real inequalities are used by finite entropy/Herbst routes
when exponential tilts are compared across one coordinate flip.
-/

/-- For every real `s`, `exp s - 1 <= s * exp s`.

This form follows from `1 - s <= exp (-s)` after multiplying by `exp s`. -/
lemma real_exp_sub_one_le_mul_exp (s : ℝ) :
    Real.exp s - 1 ≤ s * Real.exp s := by
  have h := Real.add_one_le_exp (-s)
  have hmul := mul_le_mul_of_nonneg_right h (le_of_lt (Real.exp_pos s))
  rw [Real.exp_neg, inv_mul_cancel₀ (Real.exp_pos s).ne'] at hmul
  nlinarith

/-- A symmetric Lipschitz-type bound for the scalar exponential. -/
lemma real_abs_exp_sub_exp_le_abs_sub_mul_exp_add_exp (x y : ℝ) :
    |Real.exp x - Real.exp y| ≤
      |x - y| * (Real.exp x + Real.exp y) := by
  rcases le_total x y with hxy | hyx
  · have hdiff_nonneg : 0 ≤ y - x := sub_nonneg.mpr hxy
    have hexp_le : Real.exp x ≤ Real.exp y := Real.exp_le_exp.mpr hxy
    have habs : |Real.exp x - Real.exp y| = Real.exp y - Real.exp x := by
      rw [abs_of_nonpos (sub_nonpos.mpr hexp_le)]
      ring
    have hbase := real_exp_sub_one_le_mul_exp (y - x)
    have hmul := mul_le_mul_of_nonneg_left hbase (le_of_lt (Real.exp_pos x))
    have hrewrite :
        Real.exp y - Real.exp x =
          Real.exp x * (Real.exp (y - x) - 1) := by
      rw [show y = x + (y - x) by ring, Real.exp_add]
      ring_nf
    have hstep :
        Real.exp y - Real.exp x ≤ (y - x) * Real.exp y := by
      calc
        Real.exp y - Real.exp x =
            Real.exp x * (Real.exp (y - x) - 1) := hrewrite
        _ ≤ Real.exp x * ((y - x) * Real.exp (y - x)) := hmul
        _ = (y - x) * Real.exp y := by
            rw [show y = x + (y - x) by ring, Real.exp_add]
            ring_nf
    have hsum : Real.exp y ≤ Real.exp x + Real.exp y := by
      exact le_add_of_nonneg_left (le_of_lt (Real.exp_pos x))
    have hfinal :
        (y - x) * Real.exp y ≤
          (y - x) * (Real.exp x + Real.exp y) :=
      mul_le_mul_of_nonneg_left hsum hdiff_nonneg
    calc
      |Real.exp x - Real.exp y| = Real.exp y - Real.exp x := habs
      _ ≤ (y - x) * Real.exp y := hstep
      _ ≤ (y - x) * (Real.exp x + Real.exp y) := hfinal
      _ = |x - y| * (Real.exp x + Real.exp y) := by
          rw [abs_of_nonpos]
          · ring_nf
          · linarith
  · have hdiff_nonneg : 0 ≤ x - y := sub_nonneg.mpr hyx
    have hexp_le : Real.exp y ≤ Real.exp x := Real.exp_le_exp.mpr hyx
    have habs : |Real.exp x - Real.exp y| = Real.exp x - Real.exp y := by
      rw [abs_of_nonneg (sub_nonneg.mpr hexp_le)]
    have hbase := real_exp_sub_one_le_mul_exp (x - y)
    have hmul := mul_le_mul_of_nonneg_left hbase (le_of_lt (Real.exp_pos y))
    have hrewrite :
        Real.exp x - Real.exp y =
          Real.exp y * (Real.exp (x - y) - 1) := by
      rw [show x = y + (x - y) by ring, Real.exp_add]
      ring_nf
    have hstep :
        Real.exp x - Real.exp y ≤ (x - y) * Real.exp x := by
      calc
        Real.exp x - Real.exp y =
            Real.exp y * (Real.exp (x - y) - 1) := hrewrite
        _ ≤ Real.exp y * ((x - y) * Real.exp (x - y)) := hmul
        _ = (x - y) * Real.exp x := by
            rw [show x = y + (x - y) by ring, Real.exp_add]
            ring_nf
    have hsum : Real.exp x ≤ Real.exp x + Real.exp y := by
      exact le_add_of_nonneg_right (le_of_lt (Real.exp_pos y))
    have hfinal :
        (x - y) * Real.exp x ≤
          (x - y) * (Real.exp x + Real.exp y) :=
      mul_le_mul_of_nonneg_left hsum hdiff_nonneg
    calc
      |Real.exp x - Real.exp y| = Real.exp x - Real.exp y := habs
      _ ≤ (x - y) * Real.exp x := hstep
      _ ≤ (x - y) * (Real.exp x + Real.exp y) := hfinal
      _ = |x - y| * (Real.exp x + Real.exp y) := by
          rw [abs_of_nonneg hdiff_nonneg]

/-- Ordered half-exponential difference bound.

If `b <= a`, then the one-sided half-tilt increment is controlled by the
larger exponential weight.  This is the scalar input for the positive-drop
self-bounding route on the Rademacher cube. -/
lemma real_exp_half_sub_sq_le_quarter_mul_sq_mul_exp_of_le
    {a b : ℝ} (hba : b ≤ a) :
    (Real.exp (a / 2) - Real.exp (b / 2)) ^ 2 ≤
      ((a - b) ^ 2 / 4) * Real.exp a := by
  let d : ℝ := a / 2 - b / 2
  have hd_nonneg : 0 ≤ d := by
    dsimp [d]
    linarith
  have hhalf_le : b / 2 ≤ a / 2 := by linarith
  have hdiff_nonneg :
      0 ≤ Real.exp (a / 2) - Real.exp (b / 2) := by
    exact sub_nonneg.mpr (Real.exp_le_exp.mpr hhalf_le)
  have hrewrite :
      Real.exp (a / 2) - Real.exp (b / 2) =
        Real.exp (b / 2) * (Real.exp d - 1) := by
    dsimp [d]
    rw [show a / 2 = b / 2 + (a / 2 - b / 2) by ring, Real.exp_add]
    ring_nf
  have hbase := real_exp_sub_one_le_mul_exp d
  have hmul :=
    mul_le_mul_of_nonneg_left hbase (le_of_lt (Real.exp_pos (b / 2)))
  have hdiff_le :
      Real.exp (a / 2) - Real.exp (b / 2) ≤
        d * Real.exp (a / 2) := by
    calc
      Real.exp (a / 2) - Real.exp (b / 2)
          = Real.exp (b / 2) * (Real.exp d - 1) := hrewrite
      _ ≤ Real.exp (b / 2) * (d * Real.exp d) := hmul
      _ = d * Real.exp (a / 2) := by
          dsimp [d]
          rw [show a / 2 = b / 2 + (a / 2 - b / 2) by ring, Real.exp_add]
          ring_nf
  have hrhs_nonneg : 0 ≤ d * Real.exp (a / 2) :=
    mul_nonneg hd_nonneg (le_of_lt (Real.exp_pos _))
  have hsq :
      (Real.exp (a / 2) - Real.exp (b / 2)) ^ 2 ≤
        (d * Real.exp (a / 2)) ^ 2 := by
    have habs :
        |Real.exp (a / 2) - Real.exp (b / 2)| ≤
          |d * Real.exp (a / 2)| := by
      simpa [abs_of_nonneg hdiff_nonneg, abs_of_nonneg hrhs_nonneg]
        using hdiff_le
    exact (sq_le_sq).mpr habs
  have hexp_sq : Real.exp (a / 2) ^ 2 = Real.exp a := by
    rw [pow_two, ← Real.exp_add]
    congr 1
    ring
  calc
    (Real.exp (a / 2) - Real.exp (b / 2)) ^ 2
        ≤ (d * Real.exp (a / 2)) ^ 2 := hsq
    _ = d ^ 2 * Real.exp (a / 2) ^ 2 := by ring
    _ = d ^ 2 * Real.exp a := by rw [hexp_sq]
    _ = ((a - b) ^ 2 / 4) * Real.exp a := by
        dsimp [d]
        ring

/-- Two-sided positive-drop form of the ordered half-exponential bound.

For `lam >= 0`, the half-tilt difference across two values is bounded by the
larger orientation's positive drop and exponential weight. -/
lemma real_exp_half_sub_sq_le_lam_sq_quarter_pair_pos
    {lam x y : ℝ} (hlam : 0 ≤ lam) :
    (Real.exp ((lam * x) / 2) - Real.exp ((lam * y) / 2)) ^ 2 ≤
      (lam ^ 2 / 4) *
        (Real.exp (lam * x) * (max (x - y) 0) ^ 2 +
          Real.exp (lam * y) * (max (y - x) 0) ^ 2) := by
  rcases le_total x y with hxy | hyx
  · have hlamxy : lam * x ≤ lam * y :=
      mul_le_mul_of_nonneg_left hxy hlam
    have hordered :=
      real_exp_half_sub_sq_le_quarter_mul_sq_mul_exp_of_le hlamxy
    have hsq_comm :
        (Real.exp ((lam * x) / 2) - Real.exp ((lam * y) / 2)) ^ 2 =
          (Real.exp ((lam * y) / 2) - Real.exp ((lam * x) / 2)) ^ 2 := by
      ring
    have hxmax : max (x - y) 0 = 0 := by
      exact max_eq_right (sub_nonpos.mpr hxy)
    have hymax : max (y - x) 0 = y - x := by
      exact max_eq_left (sub_nonneg.mpr hxy)
    calc
      (Real.exp ((lam * x) / 2) - Real.exp ((lam * y) / 2)) ^ 2
          =
        (Real.exp ((lam * y) / 2) - Real.exp ((lam * x) / 2)) ^ 2 := hsq_comm
      _ ≤ ((lam * y - lam * x) ^ 2 / 4) * Real.exp (lam * y) := hordered
      _ =
        (lam ^ 2 / 4) *
          (Real.exp (lam * x) * (max (x - y) 0) ^ 2 +
            Real.exp (lam * y) * (max (y - x) 0) ^ 2) := by
          rw [hxmax, hymax]
          ring
  · have hlamyx : lam * y ≤ lam * x :=
      mul_le_mul_of_nonneg_left hyx hlam
    have hordered :=
      real_exp_half_sub_sq_le_quarter_mul_sq_mul_exp_of_le hlamyx
    have hxmax : max (x - y) 0 = x - y := by
      exact max_eq_left (sub_nonneg.mpr hyx)
    have hymax : max (y - x) 0 = 0 := by
      exact max_eq_right (sub_nonpos.mpr hyx)
    calc
      (Real.exp ((lam * x) / 2) - Real.exp ((lam * y) / 2)) ^ 2
          ≤ ((lam * x - lam * y) ^ 2 / 4) * Real.exp (lam * x) := hordered
      _ =
        (lam ^ 2 / 4) *
          (Real.exp (lam * x) * (max (x - y) 0) ^ 2 +
            Real.exp (lam * y) * (max (y - x) 0) ^ 2) := by
          rw [hxmax, hymax]
          ring

/-- Squared exponential half-tilt difference bound.

This is the scalar estimate used to convert a coordinate-difference bound for
`X` into a pointwise pair bound for `exp (X / 2)`. -/
lemma real_exp_half_sub_sq_le_two_mul_half_diff_sq (a b : ℝ) :
    (Real.exp (a / 2) - Real.exp (b / 2)) ^ 2 ≤
      2 * ((a / 2) - (b / 2)) ^ 2 *
        (Real.exp a + Real.exp b) := by
  let x : ℝ := a / 2
  let y : ℝ := b / 2
  have h_abs :=
    real_abs_exp_sub_exp_le_abs_sub_mul_exp_add_exp x y
  have hM_nonneg :
      0 ≤ |x - y| * (Real.exp x + Real.exp y) := by
    positivity
  have hsq_abs :
      (Real.exp x - Real.exp y) ^ 2 ≤
        (|x - y| * (Real.exp x + Real.exp y)) ^ 2 := by
    have h_abs_to_abs :
        |Real.exp x - Real.exp y| ≤
          |(|x - y| * (Real.exp x + Real.exp y))| := by
      rwa [abs_of_nonneg hM_nonneg]
    have hsq := (sq_le_sq).mpr h_abs_to_abs
    simpa [sq_abs] using hsq
  have hsum_sq :
      (Real.exp x + Real.exp y) ^ 2 ≤
        2 * (Real.exp a + Real.exp b) := by
    have hbase :
        (Real.exp x + Real.exp y) ^ 2 ≤
          2 * (Real.exp x ^ 2 + Real.exp y ^ 2) := add_sq_le
    have hx : Real.exp x ^ 2 = Real.exp a := by
      dsimp [x]
      rw [pow_two, ← Real.exp_add]
      congr 1
      ring
    have hy : Real.exp y ^ 2 = Real.exp b := by
      dsimp [y]
      rw [pow_two, ← Real.exp_add]
      congr 1
      ring
    simpa [hx, hy] using hbase
  calc
    (Real.exp (a / 2) - Real.exp (b / 2)) ^ 2 =
        (Real.exp x - Real.exp y) ^ 2 := by rfl
    _ ≤ (|x - y| * (Real.exp x + Real.exp y)) ^ 2 := hsq_abs
    _ = (x - y) ^ 2 * (Real.exp x + Real.exp y) ^ 2 := by
        rw [mul_pow, sq_abs]
    _ ≤ (x - y) ^ 2 * (2 * (Real.exp a + Real.exp b)) := by
        exact mul_le_mul_of_nonneg_left hsum_sq (sq_nonneg (x - y))
    _ = 2 * ((a / 2) - (b / 2)) ^ 2 *
        (Real.exp a + Real.exp b) := by
        dsimp [x, y]
        ring

/-- A lightweight finite probability space, represented by a real mass function
    over a finite type. -/
structure FiniteProbability (Ω : Type*) [Fintype Ω] where
  prob : Ω → ℝ
  prob_nonneg : ∀ ω, 0 ≤ prob ω
  prob_sum : ∑ ω, prob ω = 1

namespace FiniteProbability

variable {Ω : Type*} [Fintype Ω]

/-- Finite probability spaces are equal when their mass functions are equal. -/
@[ext]
theorem ext {P Q : FiniteProbability Ω}
    (hprob : ∀ ω, P.prob ω = Q.prob ω) : P = Q := by
  cases P with
  | mk p hp hsum =>
      cases Q with
      | mk q hq qsum =>
          have hpq : p = q := funext hprob
          subst q
          simp

/-- Probability of an event in a finite probability space. -/
noncomputable def eventProb (P : FiniteProbability Ω) (E : Set Ω) : ℝ :=
  by
    classical
    exact ∑ ω, if ω ∈ E then P.prob ω else 0

/-- Expectation of a natural-valued random variable, coerced to `ℝ`. -/
noncomputable def expectationNat (P : FiniteProbability Ω) (X : Ω → ℕ) : ℝ :=
  ∑ ω, P.prob ω * (X ω : ℝ)

/-- Expectation of a real-valued random variable. -/
noncomputable def expectationReal (P : FiniteProbability Ω) (X : Ω → ℝ) : ℝ :=
  ∑ ω, P.prob ω * X ω

theorem expectationReal_sum {ι : Type*} [Fintype ι]
    (P : FiniteProbability Ω) (X : ι → Ω → ℝ) :
    P.expectationReal (fun ω => ∑ i, X i ω) =
      ∑ i, P.expectationReal (fun ω => X i ω) := by
  classical
  unfold expectationReal
  calc
    ∑ ω, P.prob ω * (∑ i, X i ω)
        = ∑ ω, ∑ i, P.prob ω * X i ω := by
            apply Finset.sum_congr rfl
            intro ω _
            rw [Finset.mul_sum]
    _ = ∑ i, ∑ ω, P.prob ω * X i ω := by
            rw [Finset.sum_comm]

theorem expectationReal_const (P : FiniteProbability Ω) (c : ℝ) :
    P.expectationReal (fun _ => c) = c := by
  classical
  unfold expectationReal
  calc
    ∑ ω, P.prob ω * c = (∑ ω, P.prob ω) * c := by
        rw [Finset.sum_mul]
    _ = c := by
        rw [P.prob_sum]
        ring

/-- The expectation of a real-valued event indicator is the event
probability. -/
theorem expectationReal_indicator_eq_eventProb
    (P : FiniteProbability Ω) (E : Set Ω)
    [DecidablePred (fun ω => ω ∈ E)] :
    P.expectationReal (fun ω => if ω ∈ E then (1 : ℝ) else 0) =
      P.eventProb E := by
  unfold expectationReal eventProb
  apply Finset.sum_congr rfl
  intro ω _
  by_cases hω : ω ∈ E
  · simp [hω]
  · simp [hω]

/-- Every finite probability law has at least one atom of positive mass.

This tiny support lemma is useful when turning pointwise strict positivity
into strict positivity of a finite matrix-valued expectation. -/
theorem exists_prob_pos (P : FiniteProbability Ω) :
    ∃ ω, 0 < P.prob ω := by
  classical
  by_contra h
  push_neg at h
  have hsum_nonpos : (∑ ω, P.prob ω) ≤ 0 :=
    Finset.sum_nonpos (fun ω _ => h ω)
  have hsum_nonneg : 0 ≤ (∑ ω, P.prob ω) :=
    Finset.sum_nonneg (fun ω _ => P.prob_nonneg ω)
  have hsum_zero : (∑ ω, P.prob ω) = 0 :=
    le_antisymm hsum_nonpos hsum_nonneg
  have : (1 : ℝ) = 0 := by
    rw [← P.prob_sum, hsum_zero]
  linarith

theorem expectationReal_add (P : FiniteProbability Ω) (X Y : Ω → ℝ) :
    P.expectationReal (fun ω => X ω + Y ω) =
      P.expectationReal X + P.expectationReal Y := by
  classical
  unfold expectationReal
  rw [← Finset.sum_add_distrib]
  apply Finset.sum_congr rfl
  intro ω _
  ring

theorem expectationReal_sub (P : FiniteProbability Ω) (X Y : Ω → ℝ) :
    P.expectationReal (fun ω => X ω - Y ω) =
      P.expectationReal X - P.expectationReal Y := by
  classical
  unfold expectationReal
  rw [← Finset.sum_sub_distrib]
  apply Finset.sum_congr rfl
  intro ω _
  ring

theorem expectationReal_mul_const (P : FiniteProbability Ω) (X : Ω → ℝ) (c : ℝ) :
    P.expectationReal (fun ω => X ω * c) = P.expectationReal X * c := by
  classical
  unfold expectationReal
  rw [Finset.sum_mul]
  apply Finset.sum_congr rfl
  intro ω _
  ring

theorem expectationReal_const_mul (P : FiniteProbability Ω) (X : Ω → ℝ) (c : ℝ) :
    P.expectationReal (fun ω => c * X ω) = c * P.expectationReal X := by
  classical
  unfold expectationReal
  rw [Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro ω _
  ring

/-- Monotonicity of expectation on a finite probability space. -/
theorem expectationReal_mono (P : FiniteProbability Ω) {X Y : Ω → ℝ}
    (hXY : ∀ ω, X ω ≤ Y ω) :
    P.expectationReal X ≤ P.expectationReal Y := by
  classical
  unfold expectationReal
  apply Finset.sum_le_sum
  intro ω _
  exact mul_le_mul_of_nonneg_left (hXY ω) (P.prob_nonneg ω)

/-- Finite Jensen inequality for concave real-valued functions under a
repository-native finite probability law.

This is the finite-probability wrapper around mathlib's
`ConcaveOn.le_map_sum`.  It is useful for the Lieb/Tropp trace-MGF route, where
Lieb's theorem supplies the concavity hypothesis and the probability weights
come from `FiniteProbability`. -/
theorem expectationReal_le_of_concaveOn
    {E : Type*} [AddCommGroup E] [Module ℝ E]
    (P : FiniteProbability Ω) {s : Set E} {f : E → ℝ} {X : Ω → E}
    (hf : ConcaveOn ℝ s f) (hX : ∀ ω, X ω ∈ s) :
    P.expectationReal (fun ω => f (X ω)) ≤
      f (∑ ω, P.prob ω • X ω) := by
  classical
  unfold expectationReal
  simpa using
    (hf.le_map_sum (t := Finset.univ) (w := fun ω => P.prob ω) (p := X)
      (fun ω _ => P.prob_nonneg ω)
      (by simpa using P.prob_sum)
      (fun ω _ => hX ω))

/-- Absolute value of a finite expectation is bounded by the expectation of
    the absolute value. -/
theorem abs_expectationReal_le_expectationReal_abs
    (P : FiniteProbability Ω) (X : Ω → ℝ) :
    |P.expectationReal X| ≤ P.expectationReal (fun ω => |X ω|) := by
  classical
  unfold expectationReal
  calc
    |∑ ω, P.prob ω * X ω|
        ≤ ∑ ω : Ω, |P.prob ω * X ω| := Finset.abs_sum_le_sum_abs _ _
    _ = ∑ ω : Ω, P.prob ω * |X ω| := by
        apply Finset.sum_congr rfl
        intro ω _
        rw [abs_mul, abs_of_nonneg (P.prob_nonneg ω)]

/-- Finite Cauchy--Schwarz for expectations:
    `(E Z)^2 ≤ E[Z^2]`. -/
theorem expectationReal_sq_le_expectationReal_sq
    (P : FiniteProbability Ω) (Z : Ω → ℝ) :
    P.expectationReal Z ^ 2 ≤ P.expectationReal (fun ω => Z ω ^ 2) := by
  classical
  have hcs := Finset.sum_mul_sq_le_sq_mul_sq
    (s := (Finset.univ : Finset Ω))
    (f := fun ω => Real.sqrt (P.prob ω))
    (g := fun ω => Real.sqrt (P.prob ω) * Z ω)
  have hleft :
      (∑ ω : Ω, Real.sqrt (P.prob ω) *
        (Real.sqrt (P.prob ω) * Z ω)) = P.expectationReal Z := by
    unfold expectationReal
    apply Finset.sum_congr rfl
    intro ω _
    rw [← mul_assoc, Real.mul_self_sqrt (P.prob_nonneg ω)]
  have hfirst :
      (∑ ω : Ω, Real.sqrt (P.prob ω) ^ 2) = 1 := by
    calc
      ∑ ω : Ω, Real.sqrt (P.prob ω) ^ 2
          = ∑ ω : Ω, P.prob ω := by
              apply Finset.sum_congr rfl
              intro ω _
              exact Real.sq_sqrt (P.prob_nonneg ω)
      _ = 1 := P.prob_sum
  have hsecond :
      (∑ ω : Ω, (Real.sqrt (P.prob ω) * Z ω) ^ 2) =
        P.expectationReal (fun ω => Z ω ^ 2) := by
    unfold expectationReal
    apply Finset.sum_congr rfl
    intro ω _
    rw [mul_pow, Real.sq_sqrt (P.prob_nonneg ω)]
  rw [hleft, hfirst, hsecond] at hcs
  simpa using hcs

/-- Finite Jensen/Cauchy corollary for nonnegative random variables:
    `E Z ≤ sqrt(E[Z^2])`. -/
theorem expectationReal_le_sqrt_expectationReal_sq
    (P : FiniteProbability Ω) (Z : Ω → ℝ) (hZ : ∀ ω, 0 ≤ Z ω) :
    P.expectationReal Z ≤ Real.sqrt (P.expectationReal (fun ω => Z ω ^ 2)) := by
  have hsq := expectationReal_sq_le_expectationReal_sq P Z
  have hEZ_nonneg : 0 ≤ P.expectationReal Z := by
    unfold expectationReal
    exact Finset.sum_nonneg fun ω _ =>
      mul_nonneg (P.prob_nonneg ω) (hZ ω)
  have hEZ2_nonneg : 0 ≤ P.expectationReal (fun ω => Z ω ^ 2) := by
    unfold expectationReal
    exact Finset.sum_nonneg fun ω _ =>
      mul_nonneg (P.prob_nonneg ω) (sq_nonneg (Z ω))
  have hsq_sqrt : P.expectationReal Z ^ 2 ≤
      (Real.sqrt (P.expectationReal (fun ω => Z ω ^ 2))) ^ 2 := by
    rw [Real.sq_sqrt hEZ2_nonneg]
    exact hsq
  have habs := (sq_le_sq).mp hsq_sqrt
  simpa [abs_of_nonneg hEZ_nonneg, abs_of_nonneg (Real.sqrt_nonneg _)] using habs

/-- A square has nonnegative finite expectation. -/
theorem expectationReal_sq_nonneg
    (P : FiniteProbability Ω) (Z : Ω → ℝ) :
    0 ≤ P.expectationReal (fun ω => Z ω ^ 2) := by
  unfold expectationReal
  exact Finset.sum_nonneg fun ω _ =>
    mul_nonneg (P.prob_nonneg ω) (sq_nonneg (Z ω))

/-- Finite Cauchy--Schwarz for mixed second moments. -/
theorem abs_expectationReal_mul_le_sqrt_mul_sqrt
    (P : FiniteProbability Ω) (X Y : Ω → ℝ) :
    |P.expectationReal (fun ω => X ω * Y ω)| ≤
      Real.sqrt (P.expectationReal (fun ω => X ω ^ 2)) *
        Real.sqrt (P.expectationReal (fun ω => Y ω ^ 2)) := by
  classical
  have hcs := Finset.sum_mul_sq_le_sq_mul_sq
    (s := (Finset.univ : Finset Ω))
    (f := fun ω => Real.sqrt (P.prob ω) * X ω)
    (g := fun ω => Real.sqrt (P.prob ω) * Y ω)
  have hleft :
      (∑ ω : Ω,
        (Real.sqrt (P.prob ω) * X ω) *
          (Real.sqrt (P.prob ω) * Y ω)) =
        P.expectationReal (fun ω => X ω * Y ω) := by
    unfold expectationReal
    apply Finset.sum_congr rfl
    intro ω _
    calc
      (Real.sqrt (P.prob ω) * X ω) *
          (Real.sqrt (P.prob ω) * Y ω)
          = (Real.sqrt (P.prob ω) * Real.sqrt (P.prob ω)) *
              (X ω * Y ω) := by ring
      _ = P.prob ω * (X ω * Y ω) := by
            rw [Real.mul_self_sqrt (P.prob_nonneg ω)]
  have hfirst :
      (∑ ω : Ω, (Real.sqrt (P.prob ω) * X ω) ^ 2) =
        P.expectationReal (fun ω => X ω ^ 2) := by
    unfold expectationReal
    apply Finset.sum_congr rfl
    intro ω _
    rw [mul_pow, Real.sq_sqrt (P.prob_nonneg ω)]
  have hsecond :
      (∑ ω : Ω, (Real.sqrt (P.prob ω) * Y ω) ^ 2) =
        P.expectationReal (fun ω => Y ω ^ 2) := by
    unfold expectationReal
    apply Finset.sum_congr rfl
    intro ω _
    rw [mul_pow, Real.sq_sqrt (P.prob_nonneg ω)]
  rw [hleft, hfirst, hsecond] at hcs
  have hX_nonneg := expectationReal_sq_nonneg P X
  have hY_nonneg := expectationReal_sq_nonneg P Y
  have hprod_nonneg :
      0 ≤ Real.sqrt (P.expectationReal (fun ω => X ω ^ 2)) *
        Real.sqrt (P.expectationReal (fun ω => Y ω ^ 2)) :=
    mul_nonneg (Real.sqrt_nonneg _) (Real.sqrt_nonneg _)
  have hrewrite :
      P.expectationReal (fun ω => X ω ^ 2) *
          P.expectationReal (fun ω => Y ω ^ 2) =
        (Real.sqrt (P.expectationReal (fun ω => X ω ^ 2)) *
          Real.sqrt (P.expectationReal (fun ω => Y ω ^ 2))) ^ 2 := by
    rw [show
        (Real.sqrt (P.expectationReal (fun ω => X ω ^ 2)) *
          Real.sqrt (P.expectationReal (fun ω => Y ω ^ 2))) ^ 2 =
          (Real.sqrt (P.expectationReal (fun ω => X ω ^ 2))) ^ 2 *
            (Real.sqrt (P.expectationReal (fun ω => Y ω ^ 2))) ^ 2 from by ring,
      Real.sq_sqrt hX_nonneg, Real.sq_sqrt hY_nonneg]
  rw [hrewrite] at hcs
  have hupper :
      P.expectationReal (fun ω => X ω * Y ω) ≤
        Real.sqrt (P.expectationReal (fun ω => X ω ^ 2)) *
          Real.sqrt (P.expectationReal (fun ω => Y ω ^ 2)) := by
    nlinarith [sq_abs (P.expectationReal (fun ω => X ω * Y ω))]
  have hlower :
      -(Real.sqrt (P.expectationReal (fun ω => X ω ^ 2)) *
          Real.sqrt (P.expectationReal (fun ω => Y ω ^ 2))) ≤
        P.expectationReal (fun ω => X ω * Y ω) := by
    nlinarith [sq_abs (P.expectationReal (fun ω => X ω * Y ω))]
  exact abs_le.mpr ⟨hlower, hupper⟩

/-- Triangle inequality for the finite probability `L²` seminorm. -/
theorem sqrt_expectationReal_sq_add_le
    (P : FiniteProbability Ω) (X Y : Ω → ℝ) :
    Real.sqrt (P.expectationReal (fun ω => (X ω + Y ω) ^ 2)) ≤
      Real.sqrt (P.expectationReal (fun ω => X ω ^ 2)) +
        Real.sqrt (P.expectationReal (fun ω => Y ω ^ 2)) := by
  classical
  have hcross := abs_expectationReal_mul_le_sqrt_mul_sqrt P X Y
  have hcross_le :
      P.expectationReal (fun ω => X ω * Y ω) ≤
        Real.sqrt (P.expectationReal (fun ω => X ω ^ 2)) *
          Real.sqrt (P.expectationReal (fun ω => Y ω ^ 2)) :=
    (abs_le.mp hcross).2
  have hsum :
      P.expectationReal (fun ω => (X ω + Y ω) ^ 2) =
        P.expectationReal (fun ω => X ω ^ 2) +
          2 * P.expectationReal (fun ω => X ω * Y ω) +
            P.expectationReal (fun ω => Y ω ^ 2) := by
    unfold expectationReal
    calc
      ∑ ω : Ω, P.prob ω * (X ω + Y ω) ^ 2 =
          ∑ ω : Ω,
            (P.prob ω * X ω ^ 2 +
              2 * (P.prob ω * (X ω * Y ω)) +
                P.prob ω * Y ω ^ 2) := by
            apply Finset.sum_congr rfl
            intro ω _
            ring
      _ =
          (∑ ω : Ω, P.prob ω * X ω ^ 2) +
            2 * (∑ ω : Ω, P.prob ω * (X ω * Y ω)) +
              (∑ ω : Ω, P.prob ω * Y ω ^ 2) := by
            rw [Finset.sum_add_distrib, Finset.sum_add_distrib,
              ← Finset.mul_sum]
  have hleft_nonneg :
      0 ≤ P.expectationReal (fun ω => (X ω + Y ω) ^ 2) :=
    expectationReal_sq_nonneg P (fun ω => X ω + Y ω)
  have hright_nonneg :
      0 ≤ Real.sqrt (P.expectationReal (fun ω => X ω ^ 2)) +
        Real.sqrt (P.expectationReal (fun ω => Y ω ^ 2)) :=
    add_nonneg (Real.sqrt_nonneg _) (Real.sqrt_nonneg _)
  rw [← Real.sqrt_sq hright_nonneg]
  apply Real.sqrt_le_sqrt
  rw [hsum]
  have hX_nonneg := expectationReal_sq_nonneg P X
  have hY_nonneg := expectationReal_sq_nonneg P Y
  rw [show
      (Real.sqrt (P.expectationReal (fun ω => X ω ^ 2)) +
        Real.sqrt (P.expectationReal (fun ω => Y ω ^ 2))) ^ 2 =
        P.expectationReal (fun ω => X ω ^ 2) +
          2 * (Real.sqrt (P.expectationReal (fun ω => X ω ^ 2)) *
            Real.sqrt (P.expectationReal (fun ω => Y ω ^ 2))) +
          P.expectationReal (fun ω => Y ω ^ 2) by
        rw [show (Real.sqrt (P.expectationReal (fun ω => X ω ^ 2)) +
            Real.sqrt (P.expectationReal (fun ω => Y ω ^ 2))) ^ 2 =
            (Real.sqrt (P.expectationReal (fun ω => X ω ^ 2))) ^ 2 +
              2 * (Real.sqrt (P.expectationReal (fun ω => X ω ^ 2)) *
                Real.sqrt (P.expectationReal (fun ω => Y ω ^ 2))) +
              (Real.sqrt (P.expectationReal (fun ω => Y ω ^ 2))) ^ 2 from by ring,
          Real.sq_sqrt hX_nonneg, Real.sq_sqrt hY_nonneg]]
  linarith

/-- Reverse triangle inequality for the finite probability `L²` seminorm.

This is the L2-section norm bridge needed in the Bernoulli-cube tensorization
route: the map `X ↦ sqrt(E X^2)` is 1-Lipschitz with respect to the same
finite `L²` seminorm. -/
theorem abs_sqrt_expectationReal_sq_sub_le_sqrt_expectationReal_sub_sq
    (P : FiniteProbability Ω) (X Y : Ω → ℝ) :
    |Real.sqrt (P.expectationReal (fun ω => X ω ^ 2)) -
        Real.sqrt (P.expectationReal (fun ω => Y ω ^ 2))| ≤
      Real.sqrt (P.expectationReal (fun ω => (X ω - Y ω) ^ 2)) := by
  have hxy0 := sqrt_expectationReal_sq_add_le P
    (fun ω => X ω - Y ω) Y
  have hxy :
      Real.sqrt (P.expectationReal (fun ω => X ω ^ 2)) ≤
        Real.sqrt (P.expectationReal (fun ω => (X ω - Y ω) ^ 2)) +
          Real.sqrt (P.expectationReal (fun ω => Y ω ^ 2)) := by
    have hx :
        (fun ω => ((X ω - Y ω) + Y ω) ^ 2) =
          fun ω => X ω ^ 2 := by
      funext ω
      ring
    simpa [hx] using hxy0
  have hyx0 := sqrt_expectationReal_sq_add_le P
    (fun ω => Y ω - X ω) X
  have hdiff :
      P.expectationReal (fun ω => (Y ω - X ω) ^ 2) =
        P.expectationReal (fun ω => (X ω - Y ω) ^ 2) := by
    apply congrArg P.expectationReal
    funext ω
    ring
  have hyx :
      Real.sqrt (P.expectationReal (fun ω => Y ω ^ 2)) ≤
        Real.sqrt (P.expectationReal (fun ω => (X ω - Y ω) ^ 2)) +
          Real.sqrt (P.expectationReal (fun ω => X ω ^ 2)) := by
    have hy :
        (fun ω => ((Y ω - X ω) + X ω) ^ 2) =
          fun ω => Y ω ^ 2 := by
      funext ω
      ring
    simpa [hy, hdiff] using hyx0
  exact abs_le.mpr ⟨by linarith, by linarith⟩

-- ============================================================
-- Finite exponential moments and entropy algebra
-- ============================================================

/-- Positivity of a finite exponential moment under a probability law. -/
theorem expectationReal_exp_pos
    (P : FiniteProbability Ω) (X : Ω → ℝ) (lam : ℝ) :
    0 < P.expectationReal (fun ω => Real.exp (lam * X ω)) := by
  classical
  rcases P.exists_prob_pos with ⟨ω₀, hω₀⟩
  unfold expectationReal
  have hterm_pos :
      0 < P.prob ω₀ * Real.exp (lam * X ω₀) :=
    mul_pos hω₀ (Real.exp_pos _)
  have hterm_nonneg :
      ∀ ω, 0 ≤ P.prob ω * Real.exp (lam * X ω) := by
    intro ω
    exact mul_nonneg (P.prob_nonneg ω) (le_of_lt (Real.exp_pos _))
  have hle :
      P.prob ω₀ * Real.exp (lam * X ω₀) ≤
        ∑ ω, P.prob ω * Real.exp (lam * X ω) :=
    Finset.single_le_sum (fun ω _ => hterm_nonneg ω) (Finset.mem_univ ω₀)
  exact lt_of_lt_of_le hterm_pos hle

/-- Derivative of a finite real exponential moment. -/
theorem hasDerivAt_expectationReal_exp_mul
    (P : FiniteProbability Ω) (X : Ω → ℝ) (lam : ℝ) :
    HasDerivAt
      (fun t : ℝ => P.expectationReal (fun ω => Real.exp (t * X ω)))
      (P.expectationReal (fun ω => X ω * Real.exp (lam * X ω))) lam := by
  classical
  unfold expectationReal
  have hsum :
      HasDerivAt
        (fun t : ℝ => ∑ ω : Ω, P.prob ω * Real.exp (t * X ω))
        (∑ ω : Ω, P.prob ω * (Real.exp (lam * X ω) * X ω)) lam := by
    apply HasDerivAt.fun_sum
    intro ω _
    have hlin : HasDerivAt (fun t : ℝ => t * X ω) (X ω) lam := by
      simpa using (hasDerivAt_id lam).mul_const (X ω)
    have hexp :
        HasDerivAt (fun t : ℝ => Real.exp (t * X ω))
          (Real.exp (lam * X ω) * X ω) lam :=
      hlin.exp
    simpa [mul_assoc] using (HasDerivAt.const_mul (P.prob ω) hexp)
  simpa [mul_comm, mul_left_comm, mul_assoc] using hsum

/-- Log-derivative of a finite real exponential moment. -/
theorem hasDerivAt_log_expectationReal_exp_mul
    (P : FiniteProbability Ω) (X : Ω → ℝ) (lam : ℝ) :
    HasDerivAt
      (fun t : ℝ =>
        Real.log (P.expectationReal (fun ω => Real.exp (t * X ω))))
      (P.expectationReal (fun ω => X ω * Real.exp (lam * X ω)) /
        P.expectationReal (fun ω => Real.exp (lam * X ω))) lam := by
  have hderiv := hasDerivAt_expectationReal_exp_mul P X lam
  have hpos := expectationReal_exp_pos P X lam
  exact hderiv.log (ne_of_gt hpos)

/-- Finite entropy functional, in the elementary real form used by the
Herbst/log-Sobolev route. -/
noncomputable def entropyReal (P : FiniteProbability Ω) (Z : Ω → ℝ) : ℝ :=
  P.expectationReal (fun ω => Z ω * Real.log (Z ω)) -
    P.expectationReal Z * Real.log (P.expectationReal Z)

/-- A constant random variable has zero finite entropy. -/
theorem entropyReal_const (P : FiniteProbability Ω) (c : ℝ) :
    entropyReal P (fun _ => c) = 0 := by
  unfold entropyReal
  rw [expectationReal_const, expectationReal_const]
  ring

/-- The unbiased Bernoulli coordinate law on `Bool`.

This is the coordinate probability measure used when specializing finite
product-law entropy algebra to the Bernoulli cube in the Ledoux route. -/
noncomputable def boolUniformProbability : FiniteProbability Bool where
  prob := fun _ => (1 : ℝ) / 2
  prob_nonneg := by
    intro _
    norm_num
  prob_sum := by
    simp [Fintype.univ_bool]

theorem boolUniformProbability_prob (b : Bool) :
    boolUniformProbability.prob b = (1 : ℝ) / 2 := rfl

/-- Expectation under the unbiased Bernoulli coordinate law. -/
theorem boolUniformProbability_expectationReal (X : Bool → ℝ) :
    boolUniformProbability.expectationReal X =
      (X false + X true) / 2 := by
  unfold expectationReal boolUniformProbability
  simp [Fintype.univ_bool]
  ring

/-- Entropy under the unbiased Bernoulli coordinate law, expanded into the
two coordinate values. -/
theorem entropyReal_boolUniformProbability_eq (Z : Bool → ℝ) :
    entropyReal boolUniformProbability Z =
      (Z false * Real.log (Z false) + Z true * Real.log (Z true)) / 2 -
        ((Z false + Z true) / 2) *
          Real.log ((Z false + Z true) / 2) := by
  unfold entropyReal
  rw [boolUniformProbability_expectationReal
    (fun b => Z b * Real.log (Z b))]
  rw [boolUniformProbability_expectationReal Z]

/-- Bool-coordinate specialization of the finite probability `L²` reverse
triangle inequality. -/
theorem boolUniformProbability_abs_sqrt_expectationReal_sq_sub_le_sqrt_expectationReal_sub_sq
    (u v : Bool → ℝ) :
    |Real.sqrt (boolUniformProbability.expectationReal (fun b => u b ^ 2)) -
        Real.sqrt (boolUniformProbability.expectationReal (fun b => v b ^ 2))| ≤
      Real.sqrt
        (boolUniformProbability.expectationReal (fun b => (u b - v b) ^ 2)) :=
  abs_sqrt_expectationReal_sq_sub_le_sqrt_expectationReal_sub_sq
    boolUniformProbability u v

/-- Two-point entropy bound from the elementary inequality
`log x <= x - 1`.

For positive masses `a` and `b`, this bounds the entropy of the two-point
function by its chi-square scale.  It is the scalar estimate used below for the
Bernoulli coordinate log-Sobolev step. -/
theorem twoPointEntropy_le_sq_sub_div_of_pos
    {a b : ℝ} (ha : 0 < a) (hb : 0 < b) :
    (a * Real.log a + b * Real.log b) / 2 -
        ((a + b) / 2) * Real.log ((a + b) / 2) ≤
      (a - b) ^ 2 / (2 * (a + b)) := by
  let m : ℝ := (a + b) / 2
  have hm_pos : 0 < m := by
    dsimp [m]
    linarith
  have hloga : Real.log (a / m) ≤ a / m - 1 :=
    Real.log_le_sub_one_of_pos (div_pos ha hm_pos)
  have hlogb : Real.log (b / m) ≤ b / m - 1 :=
    Real.log_le_sub_one_of_pos (div_pos hb hm_pos)
  have ha_mul :
      a * Real.log (a / m) ≤ a * (a / m - 1) :=
    mul_le_mul_of_nonneg_left hloga ha.le
  have hb_mul :
      b * Real.log (b / m) ≤ b * (b / m - 1) :=
    mul_le_mul_of_nonneg_left hlogb hb.le
  have hsum :
      a * Real.log (a / m) + b * Real.log (b / m) ≤
        a * (a / m - 1) + b * (b / m - 1) := by
    exact add_le_add ha_mul hb_mul
  have hleft :
      (a * Real.log a + b * Real.log b) / 2 -
          m * Real.log m =
        (a * Real.log (a / m) + b * Real.log (b / m)) / 2 := by
    have hloga_eq : Real.log (a / m) = Real.log a - Real.log m :=
      Real.log_div (ne_of_gt ha) (ne_of_gt hm_pos)
    have hlogb_eq : Real.log (b / m) = Real.log b - Real.log m :=
      Real.log_div (ne_of_gt hb) (ne_of_gt hm_pos)
    rw [hloga_eq, hlogb_eq]
    dsimp [m]
    ring
  have hright :
      (a * (a / m - 1) + b * (b / m - 1)) / 2 =
        (a - b) ^ 2 / (2 * (a + b)) := by
    dsimp [m]
    field_simp [show a + b ≠ 0 by linarith]
    ring
  calc
    (a * Real.log a + b * Real.log b) / 2 -
        ((a + b) / 2) * Real.log ((a + b) / 2)
        = (a * Real.log a + b * Real.log b) / 2 -
            m * Real.log m := by rfl
    _ = (a * Real.log (a / m) + b * Real.log (b / m)) / 2 := hleft
    _ ≤ (a * (a / m - 1) + b * (b / m - 1)) / 2 := by
          exact div_le_div_of_nonneg_right hsum (by norm_num)
    _ = (a - b) ^ 2 / (2 * (a + b)) := hright

/-- Two-point Bernoulli log-Sobolev inequality for positive functions.

This is the first actual coordinate log-Sobolev dependency on the
Ledoux/Tropp route.  It is stated for strictly positive functions, matching
Ledoux's `g^2 > 0` hypothesis. -/
theorem entropyReal_boolUniformProbability_sq_le_sq_sub_of_pos
    (g : Bool → ℝ) (hg : ∀ b, 0 < g b) :
    entropyReal boolUniformProbability (fun b => g b ^ 2) ≤
      (g true - g false) ^ 2 := by
  have hscalar :=
    twoPointEntropy_le_sq_sub_div_of_pos
      (a := g false ^ 2) (b := g true ^ 2)
      (sq_pos_of_pos (hg false)) (sq_pos_of_pos (hg true))
  rw [entropyReal_boolUniformProbability_eq]
  have hden_pos : 0 < 2 * (g false ^ 2 + g true ^ 2) := by
    nlinarith [sq_pos_of_pos (hg false), sq_pos_of_pos (hg true)]
  have hsum_pos : 0 < g false ^ 2 + g true ^ 2 := by
    nlinarith [sq_pos_of_pos (hg false), sq_pos_of_pos (hg true)]
  have hratio :
      ((g false ^ 2 - g true ^ 2) ^ 2) /
          (2 * (g false ^ 2 + g true ^ 2)) ≤
        (g true - g false) ^ 2 := by
    have hsum_sq :
        (g false + g true) ^ 2 ≤ 2 * (g false ^ 2 + g true ^ 2) := by
      nlinarith [sq_nonneg (g false - g true)]
    have hnonneg : 0 ≤ (g false - g true) ^ 2 := sq_nonneg _
    rw [sq_sub_sq]
    rw [mul_pow]
    have hdiv :
        ((g false + g true) ^ 2 * (g false - g true) ^ 2) /
            (2 * (g false ^ 2 + g true ^ 2)) ≤
          ((2 * (g false ^ 2 + g true ^ 2)) *
              (g false - g true) ^ 2) /
            (2 * (g false ^ 2 + g true ^ 2)) := by
      exact div_le_div_of_nonneg_right
        (mul_le_mul_of_nonneg_right hsum_sq hnonneg) hden_pos.le
    have hsimp :
        ((2 * (g false ^ 2 + g true ^ 2)) *
            (g false - g true) ^ 2) /
          (2 * (g false ^ 2 + g true ^ 2)) =
        (g true - g false) ^ 2 := by
      field_simp [ne_of_gt hden_pos, ne_of_gt hsum_pos]
      ring
    exact hdiv.trans_eq hsimp
  exact hscalar.trans hratio

/-- Entropy of an exponential tilt, expanded as the usual
`λ E[X exp(λX)] - E[exp(λX)] log E[exp(λX)]` identity. -/
theorem entropyReal_exp_mul_eq
    (P : FiniteProbability Ω) (X : Ω → ℝ) (lam : ℝ) :
    entropyReal P (fun ω => Real.exp (lam * X ω)) =
      lam * P.expectationReal (fun ω => X ω * Real.exp (lam * X ω)) -
        P.expectationReal (fun ω => Real.exp (lam * X ω)) *
          Real.log (P.expectationReal (fun ω => Real.exp (lam * X ω))) := by
  unfold entropyReal expectationReal
  congr 1
  calc
    ∑ ω : Ω, P.prob ω *
        (Real.exp (lam * X ω) * Real.log (Real.exp (lam * X ω)))
        = ∑ ω : Ω, P.prob ω * (Real.exp (lam * X ω) * (lam * X ω)) := by
          apply Finset.sum_congr rfl
          intro ω _
          rw [Real.log_exp]
    _ = lam * ∑ ω : Ω, P.prob ω * (X ω * Real.exp (lam * X ω)) := by
          rw [Finset.mul_sum]
          apply Finset.sum_congr rfl
          intro ω _
          ring

/-- Pointwise Herbst differential inequality extracted from an exponential
entropy bound.

This theorem is deliberately conditional: it does not prove Ledoux's
log-Sobolev/entropy inequality. It only formalizes the algebraic step turning
such an entropy bound into the usual differential inequality for the
log-moment-generating function. -/
theorem log_mgf_differential_le_of_entropyReal_exp_mul_le
    (P : FiniteProbability Ω) (X : Ω → ℝ) (lam c : ℝ)
    (hEnt :
      entropyReal P (fun ω => Real.exp (lam * X ω)) ≤
        c * lam ^ 2 * P.expectationReal (fun ω => Real.exp (lam * X ω))) :
    lam *
          (P.expectationReal (fun ω => X ω * Real.exp (lam * X ω)) /
            P.expectationReal (fun ω => Real.exp (lam * X ω))) -
        Real.log (P.expectationReal (fun ω => Real.exp (lam * X ω))) ≤
      c * lam ^ 2 := by
  classical
  let M : ℝ := P.expectationReal (fun ω => Real.exp (lam * X ω))
  let A : ℝ := P.expectationReal (fun ω => X ω * Real.exp (lam * X ω))
  have hMpos : 0 < M := by
    simpa [M] using expectationReal_exp_pos P X lam
  have hEntEq :
      entropyReal P (fun ω => Real.exp (lam * X ω)) =
        lam * A - M * Real.log M := by
    simpa [M, A] using entropyReal_exp_mul_eq P X lam
  have hleft :
      lam * (A / M) - Real.log M =
        entropyReal P (fun ω => Real.exp (lam * X ω)) / M := by
    rw [hEntEq]
    field_simp [hMpos.ne']
  have hdiv :
      entropyReal P (fun ω => Real.exp (lam * X ω)) / M ≤
        (c * lam ^ 2 * M) / M :=
    div_le_div_of_nonneg_right (by simpa [M] using hEnt) (le_of_lt hMpos)
  calc
    lam * (A / M) - Real.log M
        = entropyReal P (fun ω => Real.exp (lam * X ω)) / M := hleft
    _ ≤ (c * lam ^ 2 * M) / M := hdiv
    _ = c * lam ^ 2 := by
        field_simp [hMpos.ne']

/-- Herbst integration, first finite-calculus step.

If the pointwise Herbst differential inequality
`λ (log M)'(λ) - log M(λ) ≤ c λ^2` is available for the finite MGF
`M(λ) = E exp(λX)`, then the corrected quotient
`λ ↦ log M(λ) / λ - c λ` is antitone on positive `λ`.

This is a real integration step on the Ledoux route.  It still does not prove
Ledoux's entropy inequality or the right-limit value at `λ = 0`; those are the
remaining ingredients needed to turn the antitone quotient into the full
log-Laplace estimate. -/
theorem log_mgf_div_sub_quadratic_antitoneOn_of_differential_le
    (P : FiniteProbability Ω) (X : Ω → ℝ) (c : ℝ)
    (hdiff : ∀ lam : ℝ, 0 < lam →
      lam *
          (P.expectationReal (fun ω => X ω * Real.exp (lam * X ω)) /
            P.expectationReal (fun ω => Real.exp (lam * X ω))) -
        Real.log (P.expectationReal (fun ω => Real.exp (lam * X ω))) ≤
        c * lam ^ 2) :
    AntitoneOn
      (fun lam : ℝ =>
        Real.log (P.expectationReal (fun ω => Real.exp (lam * X ω))) / lam -
          c * lam)
      (Set.Ioi 0) := by
  classical
  let F : ℝ → ℝ :=
    fun lam => Real.log (P.expectationReal (fun ω => Real.exp (lam * X ω)))
  let A : ℝ → ℝ :=
    fun lam => P.expectationReal (fun ω => X ω * Real.exp (lam * X ω))
  let M : ℝ → ℝ :=
    fun lam => P.expectationReal (fun ω => Real.exp (lam * X ω))
  let G : ℝ → ℝ := fun lam => F lam / lam - c * lam
  have hderivAt : ∀ lam ∈ Set.Ioi (0 : ℝ),
      HasDerivAt G (((A lam / M lam) * lam - F lam) / lam ^ 2 - c) lam := by
    intro lam hlam
    have hlam_ne : lam ≠ 0 := ne_of_gt hlam
    have hF :
        HasDerivAt F (A lam / M lam) lam := by
      simpa [F, A, M] using hasDerivAt_log_expectationReal_exp_mul P X lam
    have hdiv :
        HasDerivAt (fun t : ℝ => F t / t)
          (((A lam / M lam) * lam - F lam * 1) / lam ^ 2) lam := by
      simpa using hF.div (hasDerivAt_id lam) hlam_ne
    have hlin :
        HasDerivAt (fun t : ℝ => c * t) c lam := by
      simpa using (hasDerivAt_id lam).const_mul c
    have hG := hdiv.sub hlin
    simpa [G, one_mul] using hG
  have hcont : ContinuousOn G (Set.Ioi (0 : ℝ)) := by
    intro lam hlam
    exact (hderivAt lam hlam).continuousAt.continuousWithinAt
  have hantiG : AntitoneOn G (Set.Ioi (0 : ℝ)) := by
    refine
      (antitoneOn_of_hasDerivWithinAt_nonpos
        (D := Set.Ioi (0 : ℝ))
        (f := G)
        (f' := fun lam => ((A lam / M lam) * lam - F lam) / lam ^ 2 - c)
        (convex_Ioi (0 : ℝ)) hcont ?_ ?_)
    · intro lam hlam
      rw [interior_Ioi] at hlam
      exact (hderivAt lam hlam).hasDerivWithinAt
    · intro lam hlam
      rw [interior_Ioi] at hlam
      have hlam_sq_pos : 0 < lam ^ 2 := sq_pos_of_pos hlam
      have hbase := hdiff lam hlam
      have hdiv_le :
          ((A lam / M lam) * lam - F lam) / lam ^ 2 ≤ c := by
        rw [div_le_iff₀ hlam_sq_pos]
        simpa [F, A, M, mul_comm, mul_left_comm, mul_assoc] using hbase
      linarith
  simpa [G, F, A, M] using hantiG

/-- Right-limit at zero for the finite log-MGF quotient.

For a real random variable on a finite probability space,
`log E exp(λX) / λ` tends to `E X` as `λ -> 0+`.  This is the
missing endpoint value needed after the corrected-quotient monotonicity step in
Herbst's argument. -/
theorem tendsto_log_mgf_div_nhdsGT_zero
    (P : FiniteProbability Ω) (X : Ω → ℝ) :
    Filter.Tendsto
      (fun lam : ℝ =>
        Real.log (P.expectationReal (fun ω => Real.exp (lam * X ω))) / lam)
      (nhdsWithin (0 : ℝ) (Set.Ioi 0))
      (nhds (P.expectationReal X)) := by
  classical
  let F : ℝ → ℝ :=
    fun lam => Real.log (P.expectationReal (fun ω => Real.exp (lam * X ω)))
  have hnum :
      P.expectationReal (fun ω => X ω * Real.exp (0 * X ω)) =
        P.expectationReal X := by
    unfold expectationReal
    simp
  have hden :
      P.expectationReal (fun ω => Real.exp (0 * X ω)) = 1 := by
    simpa using expectationReal_const P (1 : ℝ)
  have hden_one :
      P.expectationReal (fun _ : Ω => (1 : ℝ)) = 1 :=
    expectationReal_const P 1
  have hderiv0 :
      HasDerivAt F (P.expectationReal X) 0 := by
    simpa [F, hnum, hden_one] using
      (hasDerivAt_log_expectationReal_exp_mul P X 0)
  have hF0 : F 0 = 0 := by
    calc
      F 0 = Real.log (P.expectationReal (fun _ : Ω => (1 : ℝ))) := by
        simp [F]
      _ = Real.log 1 := by
        rw [hden_one]
      _ = 0 := Real.log_one
  have hslope := hderiv0.tendsto_slope_zero_right
  simpa [F, hF0, div_eq_mul_inv, zero_add, sub_eq_add_neg, mul_comm] using hslope

/-- Finite Herbst extraction from the differential inequality to a
log-Laplace bound.

Once the pointwise Herbst differential inequality is proved for all positive
`λ`, the corrected-quotient monotonicity and the right-limit at zero imply
`log E exp(λX) ≤ λ E X + c λ^2` for every positive `λ`. -/
theorem log_mgf_le_mean_add_quadratic_of_differential_le
    (P : FiniteProbability Ω) (X : Ω → ℝ) (c : ℝ)
    (hdiff : ∀ lam : ℝ, 0 < lam →
      lam *
          (P.expectationReal (fun ω => X ω * Real.exp (lam * X ω)) /
            P.expectationReal (fun ω => Real.exp (lam * X ω))) -
        Real.log (P.expectationReal (fun ω => Real.exp (lam * X ω))) ≤
        c * lam ^ 2) :
    ∀ lam : ℝ, 0 < lam →
      Real.log (P.expectationReal (fun ω => Real.exp (lam * X ω))) ≤
        lam * P.expectationReal X + c * lam ^ 2 := by
  classical
  let F : ℝ → ℝ :=
    fun lam => Real.log (P.expectationReal (fun ω => Real.exp (lam * X ω)))
  let G : ℝ → ℝ := fun lam => F lam / lam - c * lam
  have hanti :
      AntitoneOn G (Set.Ioi (0 : ℝ)) := by
    simpa [G, F] using
      (log_mgf_div_sub_quadratic_antitoneOn_of_differential_le P X c hdiff)
  have hlim_base :
      Filter.Tendsto (fun lam : ℝ => F lam / lam)
        (nhdsWithin (0 : ℝ) (Set.Ioi 0))
        (nhds (P.expectationReal X)) := by
    simpa [F] using tendsto_log_mgf_div_nhdsGT_zero P X
  have hlim_linear :
      Filter.Tendsto (fun lam : ℝ => c * lam)
        (nhdsWithin (0 : ℝ) (Set.Ioi 0)) (nhds 0) := by
    have h_id :
        Filter.Tendsto (fun lam : ℝ => lam)
          (nhdsWithin (0 : ℝ) (Set.Ioi 0)) (nhds 0) :=
      (Filter.tendsto_id : Filter.Tendsto (fun lam : ℝ => lam) (nhds 0) (nhds 0)).mono_left
        nhdsWithin_le_nhds
    simpa using h_id.const_mul c
  have hlimG :
      Filter.Tendsto G (nhdsWithin (0 : ℝ) (Set.Ioi 0))
        (nhds (P.expectationReal X)) := by
    simpa [G] using hlim_base.sub hlim_linear
  intro lam hlam
  have hevent :
      ∀ᶠ eps in nhdsWithin (0 : ℝ) (Set.Ioi 0), G lam ≤ G eps := by
    filter_upwards [Ioo_mem_nhdsGT hlam] with eps heps
    exact hanti heps.1 hlam heps.2.le
  have hG_le_mean : G lam ≤ P.expectationReal X :=
    ge_of_tendsto hlimG hevent
  have hquot : F lam / lam ≤ P.expectationReal X + c * lam := by
    dsimp [G] at hG_le_mean
    linarith
  have hmul : F lam ≤ (P.expectationReal X + c * lam) * lam :=
    (div_le_iff₀ hlam).mp hquot
  calc
    Real.log (P.expectationReal (fun ω => Real.exp (lam * X ω)))
        = F lam := rfl
    _ ≤ (P.expectationReal X + c * lam) * lam := hmul
    _ = lam * P.expectationReal X + c * lam ^ 2 := by
        ring

/-- Finite Herbst extraction from an exponential-entropy bound to a
log-Laplace bound.

This is the first endpoint that can consume a future local proof of Ledoux's
finite product-measure entropy inequality.  It does not prove that entropy
inequality; instead, it removes the remaining calculus from the future
Ledoux/Talagrand concentration step. -/
theorem log_mgf_le_mean_add_quadratic_of_entropyReal_exp_mul_le
    (P : FiniteProbability Ω) (X : Ω → ℝ) (c : ℝ)
    (hEnt : ∀ lam : ℝ, 0 < lam →
      entropyReal P (fun ω => Real.exp (lam * X ω)) ≤
        c * lam ^ 2 *
          P.expectationReal (fun ω => Real.exp (lam * X ω))) :
    ∀ lam : ℝ, 0 < lam →
      Real.log (P.expectationReal (fun ω => Real.exp (lam * X ω))) ≤
        lam * P.expectationReal X + c * lam ^ 2 := by
  refine log_mgf_le_mean_add_quadratic_of_differential_le P X c ?_
  intro lam hlam
  exact
    log_mgf_differential_le_of_entropyReal_exp_mul_le P X lam c
      (hEnt lam hlam)

/-- A log-Laplace bound implies the centered MGF bound used by Chernoff.

This is the finite-probability algebraic step after Herbst/Ledoux has produced
`log E exp(λX) ≤ λ μ + R`. It does not prove that log-Laplace bound. -/
theorem expectationReal_exp_centered_le_exp_of_log_mgf_le
    (P : FiniteProbability Ω) (X : Ω → ℝ) (μ R lam : ℝ)
    (hlog :
      Real.log (P.expectationReal (fun ω => Real.exp (lam * X ω))) ≤
        lam * μ + R) :
    P.expectationReal (fun ω => Real.exp (lam * (X ω - μ))) ≤
      Real.exp R := by
  classical
  let M : ℝ := P.expectationReal (fun ω => Real.exp (lam * X ω))
  have hMpos : 0 < M := by
    simpa [M] using expectationReal_exp_pos P X lam
  have hM_le : M ≤ Real.exp (lam * μ + R) := by
    exact (Real.log_le_iff_le_exp hMpos).mp (by simpa [M] using hlog)
  have hcenter :
      P.expectationReal (fun ω => Real.exp (lam * (X ω - μ))) =
        Real.exp (-(lam * μ)) * M := by
    calc
      P.expectationReal (fun ω => Real.exp (lam * (X ω - μ)))
          = P.expectationReal
              (fun ω => Real.exp (-(lam * μ)) * Real.exp (lam * X ω)) := by
              apply congrArg
              funext ω
              rw [← Real.exp_add]
              congr 1
              ring
      _ = Real.exp (-(lam * μ)) *
            P.expectationReal (fun ω => Real.exp (lam * X ω)) := by
              rw [expectationReal_const_mul]
      _ = Real.exp (-(lam * μ)) * M := rfl
  calc
    P.expectationReal (fun ω => Real.exp (lam * (X ω - μ)))
        = Real.exp (-(lam * μ)) * M := hcenter
    _ ≤ Real.exp (-(lam * μ)) * Real.exp (lam * μ + R) :=
        mul_le_mul_of_nonneg_left hM_le (le_of_lt (Real.exp_pos _))
    _ = Real.exp R := by
        rw [← Real.exp_add]
        congr 1
        ring

theorem eventProb_nonneg (P : FiniteProbability Ω) (E : Set Ω) :
    0 ≤ P.eventProb E := by
  classical
  unfold eventProb
  exact Finset.sum_nonneg fun ω _ => by
    by_cases hω : ω ∈ E
    · simp [hω, P.prob_nonneg ω]
    · simp [hω]

theorem eventProb_mono (P : FiniteProbability Ω) {E F : Set Ω}
    (hEF : E ⊆ F) :
    P.eventProb E ≤ P.eventProb F := by
  classical
  unfold eventProb
  apply Finset.sum_le_sum
  intro ω _
  by_cases hE : ω ∈ E
  · have hF : ω ∈ F := hEF hE
    simp [hE, hF]
  · by_cases hF : ω ∈ F
    · simp [hE, hF, P.prob_nonneg ω]
    · simp [hE, hF]

/-- The probability mass of an outcome is bounded by the probability of any
event containing that outcome. -/
theorem prob_le_eventProb_of_mem (P : FiniteProbability Ω) {E : Set Ω}
    {ω : Ω} (hω : ω ∈ E) :
    P.prob ω ≤ P.eventProb E := by
  classical
  let S : Set Ω := {η | η = ω}
  have hS : S ⊆ E := by
    intro η hη
    exact hη ▸ hω
  have hsingle : P.eventProb S = P.prob ω := by
    unfold eventProb S
    rw [Finset.sum_eq_single ω]
    · simp
    · intro η _ hη
      simp [hη]
    · intro hnot
      exact (hnot (Finset.mem_univ ω)).elim
  rw [← hsingle]
  exact P.eventProb_mono hS

theorem eventProb_add_eventProb_compl (P : FiniteProbability Ω) (E : Set Ω) :
    P.eventProb E + P.eventProb Eᶜ = 1 := by
  classical
  unfold eventProb
  rw [← Finset.sum_add_distrib]
  rw [← P.prob_sum]
  apply Finset.sum_congr rfl
  intro ω _
  by_cases hω : ω ∈ E <;> simp [hω]

/-- The whole finite sample space has probability one. -/
theorem eventProb_univ (P : FiniteProbability Ω) :
    P.eventProb Set.univ = 1 := by
  classical
  unfold eventProb
  simpa using P.prob_sum

/-- If an event contains every outcome, it has probability one. -/
theorem eventProb_eq_one_of_forall (P : FiniteProbability Ω) {E : Set Ω}
    (hE : ∀ ω, ω ∈ E) :
    P.eventProb E = 1 := by
  classical
  unfold eventProb
  simpa [hE] using P.prob_sum

/-- Every event in a finite probability space has probability at most one. -/
theorem eventProb_le_one (P : FiniteProbability Ω) (E : Set Ω) :
    P.eventProb E ≤ 1 := by
  have hsplit := P.eventProb_add_eventProb_compl E
  have hcompl_nonneg := P.eventProb_nonneg Eᶜ
  linarith

/-- Finite union-bound rearrangement:
    `P(E) + P(F) ≤ P(E ∩ F) + 1`. -/
theorem eventProb_add_le_eventProb_inter_add_one
    (P : FiniteProbability Ω) (E F : Set Ω) :
    P.eventProb E + P.eventProb F ≤ P.eventProb (E ∩ F) + 1 := by
  classical
  calc
    P.eventProb E + P.eventProb F
        = ∑ ω,
            ((if ω ∈ E then P.prob ω else 0) +
              (if ω ∈ F then P.prob ω else 0)) := by
            unfold eventProb
            rw [Finset.sum_add_distrib]
    _ ≤ ∑ ω,
          ((if ω ∈ E ∩ F then P.prob ω else 0) + P.prob ω) := by
            apply Finset.sum_le_sum
            intro ω _
            by_cases hE : ω ∈ E <;> by_cases hF : ω ∈ F <;>
              simp [hE, hF, P.prob_nonneg ω]
    _ = P.eventProb (E ∩ F) + 1 := by
            unfold eventProb
            rw [Finset.sum_add_distrib, P.prob_sum]
            congr 1
            apply Finset.sum_congr rfl
            intro ω _
            by_cases hω : ω ∈ E ∩ F <;> simp [hω]

/-- If two events each hold with probabilities at least `1 - δ₁` and
    `1 - δ₂`, then their intersection holds with probability at least
    `1 - (δ₁ + δ₂)`. -/
theorem eventProb_inter_ge_one_sub_add
    (P : FiniteProbability Ω) (E F : Set Ω) (δ₁ δ₂ : ℝ)
    (hE : 1 - δ₁ ≤ P.eventProb E)
    (hF : 1 - δ₂ ≤ P.eventProb F) :
    1 - (δ₁ + δ₂) ≤ P.eventProb (E ∩ F) := by
  have hsum := eventProb_add_le_eventProb_inter_add_one P E F
  linarith

/-- The intersection of two probability-one events has probability one. -/
theorem eventProb_inter_eq_one_of_eq_one
    (P : FiniteProbability Ω) (E F : Set Ω)
    (hE : P.eventProb E = 1) (hF : P.eventProb F = 1) :
    P.eventProb (E ∩ F) = 1 := by
  have hge :
      1 - ((0 : ℝ) + 0) ≤ P.eventProb (E ∩ F) := by
    exact eventProb_inter_ge_one_sub_add P E F 0 0
      (by simp [hE]) (by simp [hF])
  have hle : P.eventProb (E ∩ F) ≤ 1 := eventProb_le_one P (E ∩ F)
  linarith

/-- Product of two repository-native finite probability spaces. -/
noncomputable def prod {Ω Λ : Type*} [Fintype Ω] [Fintype Λ]
    (P : FiniteProbability Ω) (Q : FiniteProbability Λ) :
    FiniteProbability (Ω × Λ) where
  prob := fun x => P.prob x.1 * Q.prob x.2
  prob_nonneg := by
    intro x
    exact mul_nonneg (P.prob_nonneg x.1) (Q.prob_nonneg x.2)
  prob_sum := by
    classical
    rw [Fintype.sum_prod_type]
    calc
      ∑ a : Ω, ∑ b : Λ, P.prob a * Q.prob b
          = ∑ a : Ω, P.prob a * (∑ b : Λ, Q.prob b) := by
              apply Finset.sum_congr rfl
              intro a _
              rw [Finset.mul_sum]
      _ = ∑ a : Ω, P.prob a * 1 := by
              rw [Q.prob_sum]
      _ = 1 := by
              simp [P.prob_sum]

/-- Product-law Fubini identity for finite real expectations. -/
theorem prod_expectationReal_eq {Ω Λ : Type*} [Fintype Ω] [Fintype Λ]
    (P : FiniteProbability Ω) (Q : FiniteProbability Λ)
    (X : Ω × Λ → ℝ) :
    (P.prod Q).expectationReal X =
      P.expectationReal (fun a => Q.expectationReal (fun b => X (a, b))) := by
  classical
  unfold expectationReal prod
  rw [Fintype.sum_prod_type]
  apply Finset.sum_congr rfl
  intro a _
  calc
    ∑ b : Λ, P.prob a * Q.prob b * X (a, b)
        = ∑ b : Λ, P.prob a * (Q.prob b * X (a, b)) := by
            apply Finset.sum_congr rfl
            intro b _
            ring
    _ = P.prob a * ∑ b : Λ, Q.prob b * X (a, b) := by
            rw [Finset.mul_sum]

/-- Product-law Fubini identity for functions depending only on the first
coordinate. -/
theorem prod_expectationReal_fst_eq {Ω Λ : Type*} [Fintype Ω] [Fintype Λ]
    (P : FiniteProbability Ω) (Q : FiniteProbability Λ) (X : Ω → ℝ) :
    (P.prod Q).expectationReal (fun x : Ω × Λ => X x.1) =
      P.expectationReal X := by
  rw [prod_expectationReal_eq P Q]
  apply congrArg P.expectationReal
  funext a
  exact expectationReal_const Q (X a)

/-- Product-law Fubini identity for functions depending only on the second
coordinate. -/
theorem prod_expectationReal_snd_eq {Ω Λ : Type*} [Fintype Ω] [Fintype Λ]
    (P : FiniteProbability Ω) (Q : FiniteProbability Λ) (X : Λ → ℝ) :
    (P.prod Q).expectationReal (fun x : Ω × Λ => X x.2) =
      Q.expectationReal X := by
  rw [prod_expectationReal_eq P Q]
  simpa using expectationReal_const P (Q.expectationReal X)

/-- Finite scalar symmetrization around the mean.

For a real statistic `X`, the expected absolute centered deviation is bounded
by the expected absolute difference of two independent copies.  This is the
first scalar symmetrization layer used before Rademacher/Khintchine routes. -/
theorem expectationReal_abs_sub_mean_le_prod_expectationReal_abs_sub
    {Ω : Type*} [Fintype Ω] (P : FiniteProbability Ω) (X : Ω → ℝ) :
    P.expectationReal (fun ω => |X ω - P.expectationReal X|) ≤
      (P.prod P).expectationReal
        (fun x : Ω × Ω => |X x.1 - X x.2|) := by
  classical
  rw [prod_expectationReal_eq P P]
  apply expectationReal_mono P
  intro ω
  have hcenter :
      P.expectationReal (fun η => X ω - X η) =
        X ω - P.expectationReal X := by
    calc
      P.expectationReal (fun η => X ω - X η)
          = P.expectationReal (fun _η => X ω) -
              P.expectationReal X := by
              simpa using
                (expectationReal_sub P (fun _η => X ω) X)
      _ = X ω - P.expectationReal X := by
              rw [expectationReal_const]
  have habs :=
    abs_expectationReal_le_expectationReal_abs P
      (fun η => X ω - X η)
  simpa [hcenter] using habs

/-- Centered finite scalar symmetrization.

If `X` has mean zero, then `E |X|` is bounded by the expected absolute
difference of two independent copies. -/
theorem expectationReal_abs_le_prod_expectationReal_abs_sub_of_expectation_eq_zero
    {Ω : Type*} [Fintype Ω] (P : FiniteProbability Ω) (X : Ω → ℝ)
    (hmean : P.expectationReal X = 0) :
    P.expectationReal (fun ω => |X ω|) ≤
      (P.prod P).expectationReal
        (fun x : Ω × Ω => |X x.1 - X x.2|) := by
  simpa [hmean] using
    expectationReal_abs_sub_mean_le_prod_expectationReal_abs_sub P X

/-- Entropy chain rule for repository-native finite product laws.

This is the finite product-measure tensorization algebra needed by the
Ledoux/log-Sobolev route.  It does not prove any coordinate log-Sobolev
inequality; it only separates the product entropy into the average conditional
entropy plus the entropy of the conditional mean. -/
theorem entropyReal_prod_eq_expectation_entropyReal_add_entropyReal_expectation
    {Ω Λ : Type*} [Fintype Ω] [Fintype Λ]
    (P : FiniteProbability Ω) (Q : FiniteProbability Λ)
    (Z : Ω × Λ → ℝ) :
    entropyReal (P.prod Q) Z =
      P.expectationReal
        (fun a => entropyReal Q (fun b => Z (a, b))) +
        entropyReal P (fun a => Q.expectationReal (fun b => Z (a, b))) := by
  classical
  unfold entropyReal
  rw [prod_expectationReal_eq P Q
    (fun x : Ω × Λ => Z x * Real.log (Z x))]
  rw [prod_expectationReal_eq P Q Z]
  rw [expectationReal_sub]
  ring

/-- One-coordinate tensorization step for the fair Bernoulli log-Sobolev
route.

For a product law `P × ν`, where `ν` is the fair Bernoulli coordinate law, the
entropy of `g^2` is bounded by the Bernoulli-coordinate squared difference plus
the entropy of the conditional second moment.  This is the peel-off step used
before an induction over the full Bernoulli cube; it does not yet bound the
remaining entropy term. -/
theorem entropyReal_prod_boolUniformProbability_sq_le_coordinate_add_entropy
    {Ω : Type*} [Fintype Ω]
    (P : FiniteProbability Ω) (g : Ω × Bool → ℝ)
    (hg : ∀ x, 0 < g x) :
    entropyReal (P.prod boolUniformProbability) (fun x => g x ^ 2) ≤
      P.expectationReal
          (fun a => (g (a, true) - g (a, false)) ^ 2) +
        entropyReal P
          (fun a =>
            boolUniformProbability.expectationReal
              (fun b => g (a, b) ^ 2)) := by
  rw [entropyReal_prod_eq_expectation_entropyReal_add_entropyReal_expectation]
  have hcoord :
      P.expectationReal
          (fun a => entropyReal boolUniformProbability
            (fun b => g (a, b) ^ 2)) ≤
        P.expectationReal
          (fun a => (g (a, true) - g (a, false)) ^ 2) :=
    P.expectationReal_mono
      (fun a =>
        entropyReal_boolUniformProbability_sq_le_sq_sub_of_pos
          (fun b => g (a, b)) (fun b => hg (a, b)))
  exact add_le_add hcoord (le_refl _)

/-- Abstract Bernoulli-product induction lift for the Ledoux tensorization
route.

If a finite probability law `P` satisfies an entropy-gradient bound for a
family of coordinate moves `step`, then `P x boolUniformProbability` satisfies
the corresponding bound after adding the new Bernoulli coordinate.  The proof
uses the one-coordinate peel-off above and the finite `L2` reverse-triangle
bridge to control old-coordinate section norms. -/
theorem entropyReal_prod_boolUniformProbability_sq_le_lifted_diff_sum_add
    {Ω ι : Type*} [Fintype Ω] [Fintype ι]
    (P : FiniteProbability Ω) (step : ι → Ω → Ω)
    (g : Ω × Bool → ℝ) (hg : ∀ x, 0 < g x)
    (hP : ∀ h : Ω → ℝ, (∀ a, 0 < h a) →
      entropyReal P (fun a => h a ^ 2) ≤
        ∑ i : ι, P.expectationReal
          (fun a => (h a - h (step i a)) ^ 2)) :
    entropyReal (P.prod boolUniformProbability) (fun x => g x ^ 2) ≤
      P.expectationReal
          (fun a => (g (a, true) - g (a, false)) ^ 2) +
        ∑ i : ι, (P.prod boolUniformProbability).expectationReal
          (fun x => (g x - g (step i x.1, x.2)) ^ 2) := by
  classical
  let h : Ω → ℝ := fun a =>
    Real.sqrt (boolUniformProbability.expectationReal
      (fun b => g (a, b) ^ 2))
  have hinner_nonneg :
      ∀ a, 0 ≤ boolUniformProbability.expectationReal
        (fun b => g (a, b) ^ 2) := by
    intro a
    exact expectationReal_sq_nonneg boolUniformProbability (fun b => g (a, b))
  have hpos : ∀ a, 0 < h a := by
    intro a
    dsimp [h]
    apply Real.sqrt_pos.2
    rw [boolUniformProbability_expectationReal]
    have hfalse : 0 < g (a, false) ^ 2 := sq_pos_of_pos (hg (a, false))
    have htrue : 0 < g (a, true) ^ 2 := sq_pos_of_pos (hg (a, true))
    nlinarith
  have hsquare :
      (fun a => h a ^ 2) =
        fun a =>
          boolUniformProbability.expectationReal
            (fun b => g (a, b) ^ 2) := by
    funext a
    dsimp [h]
    exact Real.sq_sqrt (hinner_nonneg a)
  have hind :=
    hP h hpos
  have hind' :
      entropyReal P
          (fun a =>
            boolUniformProbability.expectationReal
              (fun b => g (a, b) ^ 2)) ≤
        ∑ i : ι, P.expectationReal
          (fun a => (h a - h (step i a)) ^ 2) := by
    simpa [hsquare] using hind
  have hcost :
      (∑ i : ι, P.expectationReal
          (fun a => (h a - h (step i a)) ^ 2)) ≤
        ∑ i : ι, (P.prod boolUniformProbability).expectationReal
          (fun x => (g x - g (step i x.1, x.2)) ^ 2) := by
    apply Finset.sum_le_sum
    intro i _
    have hpoint :
        ∀ a,
          (h a - h (step i a)) ^ 2 ≤
            boolUniformProbability.expectationReal
              (fun b => (g (a, b) - g (step i a, b)) ^ 2) := by
      intro a
      have hbridge :=
        boolUniformProbability_abs_sqrt_expectationReal_sq_sub_le_sqrt_expectationReal_sub_sq
          (fun b => g (a, b)) (fun b => g (step i a, b))
      have hright_nonneg :
          0 ≤ boolUniformProbability.expectationReal
            (fun b => (g (a, b) - g (step i a, b)) ^ 2) :=
        expectationReal_sq_nonneg boolUniformProbability
          (fun b => g (a, b) - g (step i a, b))
      have habs_le :
          |h a - h (step i a)| ≤
            Real.sqrt
              (boolUniformProbability.expectationReal
                (fun b => (g (a, b) - g (step i a, b)) ^ 2)) := by
        simpa [h] using hbridge
      have habs_le_abs :
          |h a - h (step i a)| ≤
            |Real.sqrt
              (boolUniformProbability.expectationReal
                (fun b => (g (a, b) - g (step i a, b)) ^ 2))| := by
        simpa [abs_of_nonneg (Real.sqrt_nonneg _)] using habs_le
      have hsq := (sq_le_sq).mpr habs_le_abs
      rw [Real.sq_sqrt hright_nonneg] at hsq
      exact hsq
    calc
      P.expectationReal (fun a => (h a - h (step i a)) ^ 2)
          ≤ P.expectationReal
              (fun a =>
                boolUniformProbability.expectationReal
                  (fun b => (g (a, b) - g (step i a, b)) ^ 2)) :=
            P.expectationReal_mono hpoint
      _ = (P.prod boolUniformProbability).expectationReal
          (fun x => (g x - g (step i x.1, x.2)) ^ 2) := by
            rw [prod_expectationReal_eq P boolUniformProbability]
  have hpeel :=
    entropyReal_prod_boolUniformProbability_sq_le_coordinate_add_entropy
      P g hg
  calc
    entropyReal (P.prod boolUniformProbability) (fun x => g x ^ 2)
        ≤ P.expectationReal
            (fun a => (g (a, true) - g (a, false)) ^ 2) +
          entropyReal P
            (fun a =>
              boolUniformProbability.expectationReal
                (fun b => g (a, b) ^ 2)) := hpeel
    _ ≤ P.expectationReal
            (fun a => (g (a, true) - g (a, false)) ^ 2) +
          ∑ i : ι, P.expectationReal
            (fun a => (h a - h (step i a)) ^ 2) := by
          exact add_le_add (le_refl _) hind'
    _ ≤ P.expectationReal
            (fun a => (g (a, true) - g (a, false)) ^ 2) +
          ∑ i : ι, (P.prod boolUniformProbability).expectationReal
            (fun x => (g x - g (step i x.1, x.2)) ^ 2) := by
          exact add_le_add (le_refl _) hcost

/-- In a product probability space, the probability of an event depending only
on the first coordinate is the first marginal probability. -/
theorem prod_eventProb_fst_eq {Ω Λ : Type*} [Fintype Ω] [Fintype Λ]
    (P : FiniteProbability Ω) (Q : FiniteProbability Λ) (E : Set Ω) :
    (P.prod Q).eventProb {x : Ω × Λ | x.1 ∈ E} = P.eventProb E := by
  classical
  unfold eventProb prod
  rw [Fintype.sum_prod_type]
  apply Finset.sum_congr rfl
  intro a _
  by_cases ha : a ∈ E
  · calc
      ∑ b : Λ, (if (a, b).1 ∈ E then P.prob a * Q.prob b else 0)
          = ∑ b : Λ, P.prob a * Q.prob b := by
              apply Finset.sum_congr rfl
              intro b _
              simp [ha]
      _ = P.prob a * (∑ b : Λ, Q.prob b) := by
              rw [Finset.mul_sum]
      _ = if a ∈ E then P.prob a else 0 := by
              simp [ha, Q.prob_sum]
  · calc
      ∑ b : Λ, (if (a, b).1 ∈ E then P.prob a * Q.prob b else 0)
          = ∑ _b : Λ, 0 := by
              apply Finset.sum_congr rfl
              intro b _
              simp [ha]
      _ = if a ∈ E then P.prob a else 0 := by
              simp [ha]

/-- Product-law Fubini identity for an event whose second-coordinate slice may
depend on the first coordinate. -/
theorem prod_eventProb_dependent_snd_eq {Ω Λ : Type*} [Fintype Ω] [Fintype Λ]
    (P : FiniteProbability Ω) (Q : FiniteProbability Λ) (F : Ω → Set Λ) :
    (P.prod Q).eventProb {x : Ω × Λ | x.2 ∈ F x.1} =
      P.expectationReal (fun a => Q.eventProb (F a)) := by
  classical
  unfold eventProb expectationReal prod
  rw [Fintype.sum_prod_type]
  apply Finset.sum_congr rfl
  intro a _
  calc
    ∑ b : Λ, (if (a, b).2 ∈ F (a, b).1 then P.prob a * Q.prob b else 0)
        = ∑ b : Λ, P.prob a * (if b ∈ F a then Q.prob b else 0) := by
            apply Finset.sum_congr rfl
            intro b _
            by_cases hb : b ∈ F a
            · simp [hb]
            · simp [hb]
    _ = P.prob a * ∑ b : Λ, (if b ∈ F a then Q.prob b else 0) := by
            rw [Finset.mul_sum]

/-- If every second-coordinate slice has probability at least `1 - δ`, then
the dependent second-coordinate event has product probability at least
`1 - δ`. -/
theorem prod_eventProb_dependent_snd_ge {Ω Λ : Type*} [Fintype Ω] [Fintype Λ]
    (P : FiniteProbability Ω) (Q : FiniteProbability Λ)
    (F : Ω → Set Λ) (δ : ℝ)
    (hF : ∀ a, 1 - δ ≤ Q.eventProb (F a)) :
    1 - δ ≤ (P.prod Q).eventProb {x : Ω × Λ | x.2 ∈ F x.1} := by
  classical
  rw [prod_eventProb_dependent_snd_eq P Q F]
  calc
    1 - δ = P.expectationReal (fun _a => 1 - δ) := by
        exact (expectationReal_const P (1 - δ)).symm
    _ ≤ P.expectationReal (fun a => Q.eventProb (F a)) :=
        expectationReal_mono P hF

/-- Product-law composition for a first-coordinate event and a dependent
second-coordinate event.  Outside the first-coordinate event the second
coordinate slice is treated as the whole space, so only the stated conditional
slice probabilities are needed. -/
theorem prod_eventProb_inter_dependent_ge_one_sub_add
    {Ω Λ : Type*} [Fintype Ω] [Fintype Λ]
    (P : FiniteProbability Ω) (Q : FiniteProbability Λ)
    (E : Set Ω) (F : Ω → Set Λ) (δE δF : ℝ)
    (hδF : 0 ≤ δF)
    (hE : 1 - δE ≤ P.eventProb E)
    (hF : ∀ a, a ∈ E → 1 - δF ≤ Q.eventProb (F a)) :
    1 - (δE + δF) ≤
      (P.prod Q).eventProb {x : Ω × Λ | x.1 ∈ E ∧ x.2 ∈ F x.1} := by
  classical
  let F' : Ω → Set Λ := fun a => if a ∈ E then F a else Set.univ
  let A : Set (Ω × Λ) := {x | x.1 ∈ E}
  let B : Set (Ω × Λ) := {x | x.2 ∈ F' x.1}
  have hA : 1 - δE ≤ (P.prod Q).eventProb A := by
    simpa [A] using (hE.trans_eq (prod_eventProb_fst_eq P Q E).symm)
  have hslice : ∀ a, 1 - δF ≤ Q.eventProb (F' a) := by
    intro a
    by_cases ha : a ∈ E
    · simpa [F', ha] using hF a ha
    · have hle : 1 - δF ≤ 1 := by linarith
      simpa [F', ha, eventProb_univ Q] using hle
  have hB : 1 - δF ≤ (P.prod Q).eventProb B := by
    simpa [B] using prod_eventProb_dependent_snd_ge P Q F' δF hslice
  have hinter :
      1 - (δE + δF) ≤ (P.prod Q).eventProb (A ∩ B) :=
    eventProb_inter_ge_one_sub_add (P.prod Q) A B δE δF hA hB
  have hsubset :
      A ∩ B ⊆ {x : Ω × Λ | x.1 ∈ E ∧ x.2 ∈ F x.1} := by
    intro x hx
    rcases hx with ⟨hxA, hxB⟩
    have hxA' : x.1 ∈ E := by simpa [A] using hxA
    have hxB' : x.2 ∈ F' x.1 := by simpa [B] using hxB
    exact ⟨hxA', by simpa [F', hxA'] using hxB'⟩
  exact hinter.trans (eventProb_mono (P.prod Q) hsubset)

/-- Finite union-bound form for intersections over a finite set of events:
    if each `E i` holds with probability at least `1 - δ i`, then all events
    in `s` hold simultaneously with probability at least `1 - ∑ i in s, δ i`.

This theorem is intentionally stated for an explicit `Finset`; the `Fintype`
wrapper below is the common all-indices case. -/
theorem eventProb_finset_forall_ge_one_sub_sum {ι : Type*} [DecidableEq ι]
    (P : FiniteProbability Ω) (s : Finset ι) (E : ι → Set Ω) (δ : ι → ℝ)
    (hE : ∀ i, i ∈ s → 1 - δ i ≤ P.eventProb (E i)) :
    1 - (∑ i ∈ s, δ i) ≤
      P.eventProb {ω | ∀ i, i ∈ s → ω ∈ E i} := by
  classical
  induction s using Finset.induction_on with
  | empty =>
      have hset : {ω : Ω | ∀ i, i ∈ (∅ : Finset ι) → ω ∈ E i} = Set.univ := by
        ext ω
        simp
      rw [hset, eventProb_univ]
      simp
  | insert a s ha ih =>
      let Es : Set Ω := {ω | ∀ i, i ∈ s → ω ∈ E i}
      have ha_prob : 1 - δ a ≤ P.eventProb (E a) :=
        hE a (Finset.mem_insert_self a s)
      have hs_prob : 1 - (∑ i ∈ s, δ i) ≤ P.eventProb Es :=
        ih (fun i hi => hE i (Finset.mem_insert_of_mem hi))
      have hinter :=
        eventProb_inter_ge_one_sub_add P (E a) Es
          (δ a) (∑ i ∈ s, δ i) ha_prob hs_prob
      have hset :
          E a ∩ Es =
            {ω : Ω | ∀ i, i ∈ insert a s → ω ∈ E i} := by
        ext ω
        constructor
        · intro hω i hi
          rcases hω with ⟨haω, hsω⟩
          rcases Finset.mem_insert.mp hi with rfl | his
          · exact haω
          · exact hsω i his
        · intro hω
          constructor
          · exact hω a (Finset.mem_insert_self a s)
          · intro i hi
            exact hω i (Finset.mem_insert_of_mem hi)
      have hsum : ∑ i ∈ insert a s, δ i = δ a + ∑ i ∈ s, δ i := by
        exact Finset.sum_insert ha
      simpa [hset, hsum] using hinter

/-- Finite union-bound form over all indices of a finite type. -/
theorem eventProb_forall_ge_one_sub_sum {ι : Type*} [Fintype ι] [DecidableEq ι]
    (P : FiniteProbability Ω) (E : ι → Set Ω) (δ : ι → ℝ)
    (hE : ∀ i, 1 - δ i ≤ P.eventProb (E i)) :
    1 - (∑ i, δ i) ≤ P.eventProb {ω | ∀ i, ω ∈ E i} := by
  classical
  have h :=
    eventProb_finset_forall_ge_one_sub_sum P (Finset.univ : Finset ι)
      E δ (fun i _ => hE i)
  have hset :
      {ω : Ω | ∀ i, i ∈ (Finset.univ : Finset ι) → ω ∈ E i} =
        {ω : Ω | ∀ i, ω ∈ E i} := by
    ext ω
    constructor
    · intro hω i
      exact hω i (Finset.mem_univ i)
    · intro hω i _
      exact hω i
  simpa [hset] using h

/-- Finite Markov inequality for nonnegative real-valued random variables. -/
theorem eventProb_real_ge_le_expectationReal_div
    (P : FiniteProbability Ω) (X : Ω → ℝ) {T : ℝ}
    (hX : ∀ ω, 0 ≤ X ω) (hT : 0 < T) :
    P.eventProb {ω | T ≤ X ω} ≤ P.expectationReal X / T := by
  classical
  let M : ℝ := ∑ ω, P.prob ω * (X ω / T)
  have hle : P.eventProb {ω | T ≤ X ω} ≤ M := by
    unfold eventProb M
    apply Finset.sum_le_sum
    intro ω _
    by_cases hω : ω ∈ {ω | T ≤ X ω}
    · have hone : 1 ≤ X ω / T := by
        rw [one_le_div hT]
        exact hω
      have hmain : P.prob ω ≤ P.prob ω * (X ω / T) := by
        calc
          P.prob ω = P.prob ω * 1 := by ring
          _ ≤ P.prob ω * (X ω / T) :=
              mul_le_mul_of_nonneg_left hone (P.prob_nonneg ω)
      simpa [hω] using hmain
    · have hratio_nonneg : 0 ≤ X ω / T :=
        div_nonneg (hX ω) (le_of_lt hT)
      have hmain : 0 ≤ P.prob ω * (X ω / T) :=
        mul_nonneg (P.prob_nonneg ω) hratio_nonneg
      simpa [hω] using hmain
  have hM : M = P.expectationReal X / T := by
    unfold M expectationReal
    calc
      ∑ ω, P.prob ω * (X ω / T)
          = ∑ ω, (P.prob ω * X ω) * T⁻¹ := by
              apply Finset.sum_congr rfl
              intro ω _
              ring_nf
      _ = (∑ ω, P.prob ω * X ω) * T⁻¹ := by
              rw [Finset.sum_mul]
      _ = (∑ ω, P.prob ω * X ω) / T := by
              rw [div_eq_mul_inv]
  exact hle.trans_eq hM

/-- Lower-tail Markov form for nonnegative real-valued random variables. -/
theorem eventProb_real_le_ge_one_sub_expectationReal_div
    (P : FiniteProbability Ω) (X : Ω → ℝ) (T : ℝ)
    (hX : ∀ ω, 0 ≤ X ω) (hT : 0 < T) :
    1 - P.expectationReal X / T ≤ P.eventProb {ω | X ω ≤ T} := by
  classical
  let E : Set Ω := {ω | X ω ≤ T}
  have htail :=
    eventProb_real_ge_le_expectationReal_div P X hX hT
  have hcompl_subset : Eᶜ ⊆ {ω | T ≤ X ω} := by
    intro ω hω
    simp [E] at hω
    exact le_of_lt hω
  have htailE :
      P.eventProb Eᶜ ≤ P.expectationReal X / T :=
    (eventProb_mono P hcompl_subset).trans htail
  have hsplit := eventProb_add_eventProb_compl P E
  linarith

/-- High-probability squared-moment bound:
    `Pr[Z ≤ η] ≥ 1 - E[Z²]/η²` for nonnegative `Z`. -/
theorem eventProb_le_ge_one_sub_expectationReal_sq_div
    (P : FiniteProbability Ω) (Z : Ω → ℝ) (η : ℝ)
    (hZ : ∀ ω, 0 ≤ Z ω) (hη : 0 < η) :
    1 - P.expectationReal (fun ω => Z ω ^ 2) / η ^ 2 ≤
      P.eventProb {ω | Z ω ≤ η} := by
  classical
  have hηsq : 0 < η ^ 2 := sq_pos_of_pos hη
  have hmarkov :=
    eventProb_real_le_ge_one_sub_expectationReal_div
      P (fun ω => Z ω ^ 2) (η ^ 2)
      (fun ω => sq_nonneg (Z ω)) hηsq
  have hsubset : {ω | Z ω ^ 2 ≤ η ^ 2} ⊆ {ω | Z ω ≤ η} := by
    intro ω hω
    change Z ω ^ 2 ≤ η ^ 2 at hω
    have habs := (sq_le_sq).mp hω
    simpa [abs_of_nonneg (hZ ω), abs_of_nonneg (le_of_lt hη)] using habs
  exact hmarkov.trans (eventProb_mono P hsubset)

/-- Finite Markov inequality for natural-valued random variables. -/
theorem eventProb_nat_ge_le_expectationNat_div
    (P : FiniteProbability Ω) (X : Ω → ℕ) {T : ℕ} (hT : 0 < T) :
    P.eventProb {ω | T ≤ X ω} ≤ P.expectationNat X / (T : ℝ) := by
  classical
  have hTreal : 0 < (T : ℝ) := by exact_mod_cast hT
  let M : ℝ := ∑ ω, P.prob ω * ((X ω : ℝ) / (T : ℝ))
  have hle : P.eventProb {ω | T ≤ X ω} ≤ M := by
    unfold eventProb M
    apply Finset.sum_le_sum
    intro ω _
    by_cases hω : ω ∈ {ω | T ≤ X ω}
    · have hXT : (T : ℝ) ≤ X ω := by exact_mod_cast hω
      have hone : 1 ≤ (X ω : ℝ) / (T : ℝ) := by
        rw [one_le_div hTreal]
        exact hXT
      have hmain :
          P.prob ω ≤ P.prob ω * ((X ω : ℝ) / (T : ℝ)) := by
        calc
          P.prob ω = P.prob ω * 1 := by ring
          _ ≤ P.prob ω * ((X ω : ℝ) / (T : ℝ)) :=
              mul_le_mul_of_nonneg_left hone (P.prob_nonneg ω)
      simpa [hω] using hmain
    · have hX_nonneg : 0 ≤ (X ω : ℝ) / (T : ℝ) :=
        div_nonneg (by exact_mod_cast Nat.zero_le (X ω)) (le_of_lt hTreal)
      have hmain : 0 ≤ P.prob ω * ((X ω : ℝ) / (T : ℝ)) :=
        mul_nonneg (P.prob_nonneg ω) hX_nonneg
      simpa [hω] using hmain
  have hM : M = P.expectationNat X / (T : ℝ) := by
    unfold M expectationNat
    calc
      ∑ ω, P.prob ω * ((X ω : ℝ) / (T : ℝ))
          = ∑ ω, (P.prob ω * (X ω : ℝ)) * (T : ℝ)⁻¹ := by
              apply Finset.sum_congr rfl
              intro ω _
              ring_nf
      _ = (∑ ω, P.prob ω * (X ω : ℝ)) * (T : ℝ)⁻¹ := by
              rw [Finset.sum_mul]
      _ = (∑ ω, P.prob ω * (X ω : ℝ)) / (T : ℝ) := by
              rw [div_eq_mul_inv]
  exact hle.trans_eq hM

/-- Lower-tail form of Markov: with probability at least
    `1 - E[X] / (Q+1)`, a natural-valued random variable is at most `Q`. -/
theorem eventProb_nat_le_ge_one_sub_expectationNat_div_succ
    (P : FiniteProbability Ω) (X : Ω → ℕ) (Q : ℕ) :
    1 - P.expectationNat X / ((Q + 1 : ℕ) : ℝ) ≤
      P.eventProb {ω | X ω ≤ Q} := by
  classical
  let E : Set Ω := {ω | X ω ≤ Q}
  have hT : 0 < Q + 1 := Nat.succ_pos Q
  have htail :=
    eventProb_nat_ge_le_expectationNat_div P X hT
  have hcompl :
      Eᶜ = {ω | Q + 1 ≤ X ω} := by
    ext ω
    simp [E]
  have htailE :
      P.eventProb Eᶜ ≤ P.expectationNat X / ((Q + 1 : ℕ) : ℝ) := by
    simpa [hcompl] using htail
  have hsplit := eventProb_add_eventProb_compl P E
  linarith

/-- Chebyshev from finite Markov: the probability of a strict deviation from
    `μ` by more than `ε` is bounded by the centered second moment divided by
    `ε²`. -/
theorem eventProb_abs_sub_gt_le_expectationReal_sq_div
    (P : FiniteProbability Ω) (X : Ω → ℝ) (μ ε : ℝ) (hε : 0 < ε) :
    P.eventProb {ω | ε < |X ω - μ|} ≤
      P.expectationReal (fun ω => (X ω - μ) ^ 2) / ε ^ 2 := by
  classical
  have hε2 : 0 < ε ^ 2 := sq_pos_of_pos hε
  let M : ℝ := ∑ ω, P.prob ω * (((X ω - μ) ^ 2) / ε ^ 2)
  have hle : P.eventProb {ω | ε < |X ω - μ|} ≤ M := by
    unfold eventProb M
    apply Finset.sum_le_sum
    intro ω _
    by_cases hω : ω ∈ {ω | ε < |X ω - μ|}
    · have hdev : ε < |X ω - μ| := hω
      have hsq : ε ^ 2 ≤ (X ω - μ) ^ 2 := by
        have hsq_abs : ε ^ 2 ≤ |X ω - μ| ^ 2 := by
          nlinarith [le_of_lt hdev, le_of_lt hε, abs_nonneg (X ω - μ)]
        simpa [sq_abs] using hsq_abs
      have hone : 1 ≤ ((X ω - μ) ^ 2) / ε ^ 2 := by
        rw [one_le_div hε2]
        exact hsq
      have hmain :
          P.prob ω ≤ P.prob ω * (((X ω - μ) ^ 2) / ε ^ 2) := by
        calc
          P.prob ω = P.prob ω * 1 := by ring
          _ ≤ P.prob ω * (((X ω - μ) ^ 2) / ε ^ 2) :=
              mul_le_mul_of_nonneg_left hone (P.prob_nonneg ω)
      simpa [hω] using hmain
    · have hsq_nonneg : 0 ≤ ((X ω - μ) ^ 2) / ε ^ 2 :=
        div_nonneg (sq_nonneg _) (le_of_lt hε2)
      have hmain :
          0 ≤ P.prob ω * (((X ω - μ) ^ 2) / ε ^ 2) :=
        mul_nonneg (P.prob_nonneg ω) hsq_nonneg
      simpa [hω] using hmain
  have hM : M = P.expectationReal (fun ω => (X ω - μ) ^ 2) / ε ^ 2 := by
    unfold M expectationReal
    calc
      ∑ ω, P.prob ω * (((X ω - μ) ^ 2) / ε ^ 2)
          = ∑ ω, (P.prob ω * ((X ω - μ) ^ 2)) * (ε ^ 2)⁻¹ := by
              apply Finset.sum_congr rfl
              intro ω _
              ring_nf
      _ = (∑ ω, P.prob ω * ((X ω - μ) ^ 2)) * (ε ^ 2)⁻¹ := by
              rw [Finset.sum_mul]
      _ = (∑ ω, P.prob ω * ((X ω - μ) ^ 2)) / ε ^ 2 := by
              rw [div_eq_mul_inv]
  exact hle.trans_eq hM

/-- `1 - δ` Chebyshev form: if the centered second moment divided by `ε²` is
    at most `δ`, then the random variable lies within `ε` of `μ` with
    probability at least `1 - δ`. -/
theorem eventProb_abs_sub_le_ge_one_sub_of_second_moment
    (P : FiniteProbability Ω) (X : Ω → ℝ) (μ ε δ : ℝ) (hε : 0 < ε)
    (hmoment : P.expectationReal (fun ω => (X ω - μ) ^ 2) / ε ^ 2 ≤ δ) :
    1 - δ ≤ P.eventProb {ω | |X ω - μ| ≤ ε} := by
  classical
  let E : Set Ω := {ω | |X ω - μ| ≤ ε}
  have htail :=
    eventProb_abs_sub_gt_le_expectationReal_sq_div P X μ ε hε
  have hcompl :
      Eᶜ = {ω | ε < |X ω - μ|} := by
    ext ω
    simp [E, not_le]
  have htailE :
      P.eventProb Eᶜ ≤
        P.expectationReal (fun ω => (X ω - μ) ^ 2) / ε ^ 2 := by
    simpa [hcompl] using htail
  have hsplit := eventProb_add_eventProb_compl P E
  linarith

/-- Exponential Markov inequality for real-valued random variables.  This is
    the finite-probability kernel needed before spectral or matrix-valued
    concentration can be developed. -/
theorem eventProb_real_ge_le_exp_mul_mgf
    (P : FiniteProbability Ω) (X : Ω → ℝ) {T lam : ℝ}
    (hlam : 0 < lam) :
    P.eventProb {ω | T ≤ X ω} ≤
      Real.exp (-(lam * T)) *
        P.expectationReal (fun ω => Real.exp (lam * X ω)) := by
  classical
  let M : ℝ :=
    ∑ ω, P.prob ω * Real.exp (lam * X ω - lam * T)
  have hle : P.eventProb {ω | T ≤ X ω} ≤ M := by
    unfold eventProb M
    apply Finset.sum_le_sum
    intro ω _
    by_cases hω : ω ∈ {ω | T ≤ X ω}
    · have hlamT : lam * T ≤ lam * X ω :=
        mul_le_mul_of_nonneg_left hω (le_of_lt hlam)
      have hone :
          1 ≤ Real.exp (lam * X ω - lam * T) := by
        calc
          (1 : ℝ) = Real.exp 0 := by rw [Real.exp_zero]
          _ ≤ Real.exp (lam * X ω - lam * T) :=
              Real.exp_le_exp.mpr (by linarith)
      have hmain :
          P.prob ω ≤ P.prob ω * Real.exp (lam * X ω - lam * T) := by
        calc
          P.prob ω = P.prob ω * 1 := by ring
          _ ≤ P.prob ω * Real.exp (lam * X ω - lam * T) :=
              mul_le_mul_of_nonneg_left hone (P.prob_nonneg ω)
      simpa [hω] using hmain
    · have hmain :
          0 ≤ P.prob ω * Real.exp (lam * X ω - lam * T) :=
        mul_nonneg (P.prob_nonneg ω) (le_of_lt (Real.exp_pos _))
      simpa [hω] using hmain
  have hM :
      M =
        Real.exp (-(lam * T)) *
          P.expectationReal (fun ω => Real.exp (lam * X ω)) := by
    unfold M expectationReal
    rw [Finset.mul_sum]
    apply Finset.sum_congr rfl
    intro ω _
    have hexp :
        Real.exp (lam * X ω - lam * T) =
          Real.exp (-(lam * T)) * Real.exp (lam * X ω) := by
      calc
        Real.exp (lam * X ω - lam * T)
            = Real.exp (-(lam * T) + lam * X ω) := by
                congr 1
                ring
        _ = Real.exp (-(lam * T)) * Real.exp (lam * X ω) := by
                rw [Real.exp_add]
    rw [hexp]
    ring
  exact hle.trans_eq hM

/-- Lower-tail complement form of real-valued exponential Markov. -/
theorem eventProb_real_le_ge_one_sub_exp_mul_mgf
    (P : FiniteProbability Ω) (X : Ω → ℝ) (T : ℝ) {lam : ℝ}
    (hlam : 0 < lam) :
    1 - Real.exp (-(lam * T)) *
        P.expectationReal (fun ω => Real.exp (lam * X ω)) ≤
      P.eventProb {ω | X ω ≤ T} := by
  classical
  let E : Set Ω := {ω | X ω ≤ T}
  have htail :=
    eventProb_real_ge_le_exp_mul_mgf P X (T := T) (lam := lam) hlam
  have hcompl_subset :
      Eᶜ ⊆ {ω | T ≤ X ω} := by
    intro ω hω
    exact le_of_lt (by simpa [E, not_le] using hω)
  have htailE :
      P.eventProb Eᶜ ≤
        Real.exp (-(lam * T)) *
          P.expectationReal (fun ω => Real.exp (lam * X ω)) :=
    (eventProb_mono P hcompl_subset).trans htail
  have hsplit := eventProb_add_eventProb_compl P E
  linarith

/-- If a real-valued random variable has an exponential-moment bound at a
positive parameter, then exponential Markov gives a one-sided lower bound for
the corresponding sublevel event.  This is the reusable Chernoff step used after
subgaussian MGF estimates such as the Ledoux/Talagrand convex-Lipschitz
Rademacher bound. -/
theorem eventProb_real_le_ge_one_sub_exp_of_mgf_bound
    (P : FiniteProbability Ω) (X : Ω → ℝ) (T lam R : ℝ)
    (hlam : 0 < lam)
    (hmgf : P.expectationReal (fun ω => Real.exp (lam * X ω)) ≤
      Real.exp R) :
    1 - Real.exp (R - lam * T) ≤ P.eventProb {ω | X ω ≤ T} := by
  have hbase :=
    eventProb_real_le_ge_one_sub_exp_mul_mgf P X T (lam := lam) hlam
  have hfactor :
      Real.exp (-(lam * T)) *
          P.expectationReal (fun ω => Real.exp (lam * X ω)) ≤
        Real.exp (R - lam * T) := by
    calc
      Real.exp (-(lam * T)) *
          P.expectationReal (fun ω => Real.exp (lam * X ω))
          ≤ Real.exp (-(lam * T)) * Real.exp R :=
            mul_le_mul_of_nonneg_left hmgf (le_of_lt (Real.exp_pos _))
      _ = Real.exp (R - lam * T) := by
            rw [← Real.exp_add]
            congr 1
            ring
  linarith

/-- Optimized one-sided subgaussian tail from a centered MGF bound.  The
statement is deliberately finite-probability-native: the hard input is only the
MGF estimate, while this theorem performs the Chernoff optimization
`λ = t / σ^2`. -/
theorem eventProb_real_le_mean_add_ge_one_sub_exp_sq_of_subgaussian_mgf
    (P : FiniteProbability Ω) (X : Ω → ℝ) (μ σ t : ℝ)
    (hσ : 0 < σ) (ht : 0 < t)
    (hmgf : ∀ lam : ℝ, 0 < lam →
      P.expectationReal (fun ω => Real.exp (lam * (X ω - μ))) ≤
        Real.exp (lam ^ 2 * σ ^ 2 / 2)) :
    1 - Real.exp (-(t ^ 2 / (2 * σ ^ 2))) ≤
      P.eventProb {ω | X ω ≤ μ + t} := by
  let lam : ℝ := t / σ ^ 2
  have hσsq_pos : 0 < σ ^ 2 := sq_pos_of_pos hσ
  have hσsq_ne : σ ^ 2 ≠ 0 := ne_of_gt hσsq_pos
  have hlam : 0 < lam := by
    exact div_pos ht hσsq_pos
  have hchernoff :=
    eventProb_real_le_ge_one_sub_exp_of_mgf_bound P
      (fun ω => X ω - μ) t lam (lam ^ 2 * σ ^ 2 / 2) hlam
      (hmgf lam hlam)
  have hexp :
      lam ^ 2 * σ ^ 2 / 2 - lam * t =
        -(t ^ 2 / (2 * σ ^ 2)) := by
    dsimp [lam]
    field_simp [hσsq_ne]
    ring
  have hset :
      {ω | X ω - μ ≤ t} = {ω | X ω ≤ μ + t} := by
    ext ω
    simp
    constructor
    · intro hω
      linarith
    · intro hω
      linarith
  simpa [hset, hexp, add_comm, add_left_comm, add_assoc] using hchernoff

/-- Chernoff tail from a log-Laplace bound.

This composes the visible log-MGF/Laplace hypothesis with the repository's
finite subgaussian Chernoff optimizer. It is the reusable endpoint for a future
formalized Ledoux/Talagrand Laplace estimate. -/
theorem eventProb_real_le_mean_add_ge_one_sub_exp_sq_of_log_mgf_bound
    (P : FiniteProbability Ω) (X : Ω → ℝ) (μ σ t : ℝ)
    (hσ : 0 < σ) (ht : 0 < t)
    (hlog :
      ∀ lam : ℝ, 0 < lam →
        Real.log (P.expectationReal (fun ω => Real.exp (lam * X ω))) ≤
          lam * μ + lam ^ 2 * σ ^ 2 / 2) :
    1 - Real.exp (-(t ^ 2 / (2 * σ ^ 2))) ≤
      P.eventProb {ω | X ω ≤ μ + t} := by
  refine
    eventProb_real_le_mean_add_ge_one_sub_exp_sq_of_subgaussian_mgf
      P X μ σ t hσ ht ?_
  intro lam hlam
  exact
    expectationReal_exp_centered_le_exp_of_log_mgf_le
      P X μ (lam ^ 2 * σ ^ 2 / 2) lam (hlog lam hlam)

/-- One-sided finite concentration from an exponential-entropy bound.

If the visible entropy inequality
`Ent(exp(λX)) <= (σ^2 / 2) λ^2 E exp(λX)` holds for all positive `λ`, then
Herbst's argument and Chernoff optimization give the usual upper-tail
subgaussian event.  This theorem is intentionally still conditional on the
entropy inequality; the active Ledoux/Talagrand bottleneck is to prove that
entropy inequality for separately convex 1-Lipschitz functions under the
finite product law. -/
theorem eventProb_real_le_mean_add_ge_one_sub_exp_sq_of_entropyReal_exp_mul_le
    (P : FiniteProbability Ω) (X : Ω → ℝ) (σ t : ℝ)
    (hσ : 0 < σ) (ht : 0 < t)
    (hEnt : ∀ lam : ℝ, 0 < lam →
      entropyReal P (fun ω => Real.exp (lam * X ω)) ≤
        (σ ^ 2 / 2) * lam ^ 2 *
          P.expectationReal (fun ω => Real.exp (lam * X ω))) :
    1 - Real.exp (-(t ^ 2 / (2 * σ ^ 2))) ≤
      P.eventProb {ω | X ω ≤ P.expectationReal X + t} := by
  refine
    eventProb_real_le_mean_add_ge_one_sub_exp_sq_of_log_mgf_bound
      P X (P.expectationReal X) σ t hσ ht ?_
  intro lam hlam
  have hlog :=
    log_mgf_le_mean_add_quadratic_of_entropyReal_exp_mul_le
      P X (σ ^ 2 / 2) hEnt lam hlam
  calc
    Real.log (P.expectationReal (fun ω => Real.exp (lam * X ω)))
        ≤ lam * P.expectationReal X + (σ ^ 2 / 2) * lam ^ 2 := hlog
    _ = lam * P.expectationReal X + lam ^ 2 * σ ^ 2 / 2 := by
        ring

/-- Exponential Markov inequality for natural-valued random variables. This is
    the finite-probability kernel behind the Chernoff upper-tail bound. -/
theorem eventProb_nat_ge_le_exp_mul_mgf
    (P : FiniteProbability Ω) (X : Ω → ℕ) {T : ℕ} {lam : ℝ}
    (hlam : 0 < lam) :
    P.eventProb {ω | T ≤ X ω} ≤
      Real.exp (-(lam * (T : ℝ))) *
        P.expectationReal (fun ω => Real.exp (lam * (X ω : ℝ))) := by
  classical
  let M : ℝ :=
    ∑ ω, P.prob ω * Real.exp (lam * (X ω : ℝ) - lam * (T : ℝ))
  have hle : P.eventProb {ω | T ≤ X ω} ≤ M := by
    unfold eventProb M
    apply Finset.sum_le_sum
    intro ω _
    by_cases hω : ω ∈ {ω | T ≤ X ω}
    · have hXT : (T : ℝ) ≤ X ω := by exact_mod_cast hω
      have hlamT : lam * (T : ℝ) ≤ lam * (X ω : ℝ) :=
        mul_le_mul_of_nonneg_left hXT (le_of_lt hlam)
      have hone :
          1 ≤ Real.exp (lam * (X ω : ℝ) - lam * (T : ℝ)) := by
        calc
          (1 : ℝ) = Real.exp 0 := by rw [Real.exp_zero]
          _ ≤ Real.exp (lam * (X ω : ℝ) - lam * (T : ℝ)) :=
              Real.exp_le_exp.mpr (by linarith)
      have hmain :
          P.prob ω ≤
            P.prob ω * Real.exp (lam * (X ω : ℝ) - lam * (T : ℝ)) := by
        calc
          P.prob ω = P.prob ω * 1 := by ring
          _ ≤ P.prob ω *
              Real.exp (lam * (X ω : ℝ) - lam * (T : ℝ)) :=
              mul_le_mul_of_nonneg_left hone (P.prob_nonneg ω)
      simpa [hω] using hmain
    · have hmain :
          0 ≤ P.prob ω *
            Real.exp (lam * (X ω : ℝ) - lam * (T : ℝ)) :=
        mul_nonneg (P.prob_nonneg ω)
          (le_of_lt (Real.exp_pos _))
      simpa [hω] using hmain
  have hM :
      M =
        Real.exp (-(lam * (T : ℝ))) *
          P.expectationReal (fun ω => Real.exp (lam * (X ω : ℝ))) := by
    unfold M expectationReal
    rw [Finset.mul_sum]
    apply Finset.sum_congr rfl
    intro ω _
    have hexp :
        Real.exp (lam * (X ω : ℝ) - lam * (T : ℝ)) =
          Real.exp (-(lam * (T : ℝ))) *
            Real.exp (lam * (X ω : ℝ)) := by
      calc
        Real.exp (lam * (X ω : ℝ) - lam * (T : ℝ))
            = Real.exp (-(lam * (T : ℝ)) + lam * (X ω : ℝ)) := by
                congr 1
                ring
        _ = Real.exp (-(lam * (T : ℝ))) *
            Real.exp (lam * (X ω : ℝ)) := by
                rw [Real.exp_add]
    rw [hexp]
    ring
  exact hle.trans_eq hM

/-- Chernoff upper tail from an exponential-moment bound. If
    `E exp(lamX) ≤ exp(μ(exp lam - 1))`, then
    `Pr(T ≤ X) ≤ exp(μ(exp lam - 1) - lamT)`. -/
theorem eventProb_nat_ge_le_chernoff_of_mgf_bound
    (P : FiniteProbability Ω) (X : Ω → ℕ) {T : ℕ} {lam μ : ℝ}
    (hlam : 0 < lam)
    (hmgf :
      P.expectationReal (fun ω => Real.exp (lam * (X ω : ℝ))) ≤
        Real.exp (μ * (Real.exp lam - 1))) :
    P.eventProb {ω | T ≤ X ω} ≤
      Real.exp (μ * (Real.exp lam - 1) - lam * (T : ℝ)) := by
  have hmarkov := eventProb_nat_ge_le_exp_mul_mgf P X (T := T) hlam
  have hmul :
      Real.exp (-(lam * (T : ℝ))) *
          P.expectationReal (fun ω => Real.exp (lam * (X ω : ℝ))) ≤
        Real.exp (-(lam * (T : ℝ))) *
          Real.exp (μ * (Real.exp lam - 1)) :=
    mul_le_mul_of_nonneg_left hmgf (le_of_lt (Real.exp_pos _))
  have hexp :
      Real.exp (-(lam * (T : ℝ))) *
          Real.exp (μ * (Real.exp lam - 1)) =
        Real.exp (μ * (Real.exp lam - 1) - lam * (T : ℝ)) := by
    calc
      Real.exp (-(lam * (T : ℝ))) *
          Real.exp (μ * (Real.exp lam - 1))
          = Real.exp (-(lam * (T : ℝ)) +
              μ * (Real.exp lam - 1)) := by
              rw [← Real.exp_add]
      _ = Real.exp (μ * (Real.exp lam - 1) - lam * (T : ℝ)) := by
              congr 1
              ring
  exact hmarkov.trans (hmul.trans_eq hexp)

/-- Lower-tail complement form of the Chernoff upper-tail bound. -/
theorem eventProb_nat_le_ge_one_sub_chernoff_of_mgf_bound
    (P : FiniteProbability Ω) (X : Ω → ℕ) (Q : ℕ) {lam μ : ℝ}
    (hlam : 0 < lam)
    (hmgf :
      P.expectationReal (fun ω => Real.exp (lam * (X ω : ℝ))) ≤
        Real.exp (μ * (Real.exp lam - 1))) :
    1 - Real.exp (μ * (Real.exp lam - 1) -
        lam * (((Q + 1 : ℕ) : ℝ))) ≤
      P.eventProb {ω | X ω ≤ Q} := by
  classical
  let E : Set Ω := {ω | X ω ≤ Q}
  have htail :=
    eventProb_nat_ge_le_chernoff_of_mgf_bound P X
      (T := Q + 1) hlam hmgf
  have hcompl :
      Eᶜ = {ω | Q + 1 ≤ X ω} := by
    ext ω
    simp [E]
  have htailE :
      P.eventProb Eᶜ ≤
        Real.exp (μ * (Real.exp lam - 1) -
          lam * (((Q + 1 : ℕ) : ℝ))) := by
    simpa [hcompl] using htail
  have hsplit := eventProb_add_eventProb_compl P E
  linarith

end FiniteProbability

end NumStability
