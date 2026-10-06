-- Analysis/Problem2_24.lean
--
-- Problem-specific theorem surface for Higham Chapter 2, Problem 2.24.

import Mathlib.Tactic.NormNum
import Mathlib.Tactic.Ring
import NumStability.Analysis.Problem2_10

namespace NumStability

noncomputable section

namespace FloatingPointFormat

/-!
# Higham Chapter 2, Problem 2.24

Problem 2.24 asks for the Kahan observation that evaluating
`f(x) = (((x - 0.5) + x) - 0.5) + x` exactly as parenthesized in single or
double precision binary IEEE arithmetic never gives zero on floating-point
inputs.

This file records the literal finite round-to-even operation path.  It first
closes the exact-intermediate branch: if the four exact real intermediates are
finite representable, the rounded path is exactly `3*x - 1`, hence it cannot
vanish for a finite IEEE single/double input because `1/3` is not
representable.  It then proves zero-result audit lemmas: for finite inputs, any
zero result forces exact final cancellation `y3 = -x`, localizes the input, and
eventually forces the exact third real intermediate to be both nonfinite and
finite in the modeled IEEE single/double finite systems.  Thus the modeled
finite round-to-even single/double path never evaluates to zero; a full IEEE
flags/special-values lift is tracked separately in the Chapter 2 ledger.
-/

/-- The literal finite round-to-even evaluation path from Problem 2.24. -/
def problem2_24_eval (fmt : FloatingPointFormat) (x : ℝ) : ℝ :=
  let y1 := fmt.finiteRoundToEvenOp BasicOp.sub x (1 / 2 : ℝ)
  let y2 := fmt.finiteRoundToEvenOp BasicOp.add y1 x
  let y3 := fmt.finiteRoundToEvenOp BasicOp.sub y2 (1 / 2 : ℝ)
  fmt.finiteRoundToEvenOp BasicOp.add y3 x

/-- First rounded intermediate in the Problem 2.24 path. -/
def problem2_24_y1 (fmt : FloatingPointFormat) (x : ℝ) : ℝ :=
  fmt.finiteRoundToEvenOp BasicOp.sub x (1 / 2 : ℝ)

/-- Second rounded intermediate in the Problem 2.24 path. -/
def problem2_24_y2 (fmt : FloatingPointFormat) (x : ℝ) : ℝ :=
  fmt.finiteRoundToEvenOp BasicOp.add (fmt.problem2_24_y1 x) x

/-- Third rounded intermediate in the Problem 2.24 path. -/
def problem2_24_y3 (fmt : FloatingPointFormat) (x : ℝ) : ℝ :=
  fmt.finiteRoundToEvenOp BasicOp.sub (fmt.problem2_24_y2 x) (1 / 2 : ℝ)

/-- The literal path is final round-to-even addition from the third rounded
intermediate. -/
theorem problem2_24_eval_eq_rounded_last_sum
    {fmt : FloatingPointFormat} {x : ℝ} :
    fmt.problem2_24_eval x =
      fmt.finiteRoundToEvenOp BasicOp.add (fmt.problem2_24_y3 x) x := by
  rfl

/-- The exact real expression underlying the displayed Problem 2.24 path. -/
def problem2_24_exactExpr (x : ℝ) : ℝ :=
  (((x - (1 / 2 : ℝ)) + x) - (1 / 2 : ℝ)) + x

theorem problem2_24_exactExpr_eq_three_mul_sub_one (x : ℝ) :
    problem2_24_exactExpr x = 3 * x - 1 := by
  rw [problem2_24_exactExpr]
  ring

theorem problem2_24_exactExpr_eq_zero_iff (x : ℝ) :
    problem2_24_exactExpr x = 0 ↔ x = (1 / 3 : ℝ) := by
  rw [problem2_24_exactExpr_eq_three_mul_sub_one]
  constructor <;> intro h <;> linarith

theorem problem2_24_exactExpr_ne_zero_of_ne_one_third
    {x : ℝ} (hx : x ≠ (1 / 3 : ℝ)) :
    problem2_24_exactExpr x ≠ 0 := by
  intro hzero
  exact hx ((problem2_24_exactExpr_eq_zero_iff x).mp hzero)

/-- If the last exact sum is finite representable, the final rounded addition is
exact. -/
theorem problem2_24_eval_eq_last_exact_of_finiteSystem_last_sum
    {fmt : FloatingPointFormat} {x : ℝ}
    (hlast : fmt.finiteSystem (fmt.problem2_24_y3 x + x)) :
    fmt.problem2_24_eval x = fmt.problem2_24_y3 x + x := by
  rw [problem2_24_eval_eq_rounded_last_sum]
  simpa [BasicOp.exact] using
    (fmt.finiteRoundToEvenOp_eq_exact_of_finiteSystem
      (op := BasicOp.add) (x := fmt.problem2_24_y3 x) (y := x) hlast)

/-- In the final-exact branch, rounded zero is equivalent to exact zero of the
last real sum. -/
theorem problem2_24_eval_eq_zero_iff_last_sum_eq_zero_of_finiteSystem_last_sum
    {fmt : FloatingPointFormat} {x : ℝ}
    (hlast : fmt.finiteSystem (fmt.problem2_24_y3 x + x)) :
    fmt.problem2_24_eval x = 0 ↔ fmt.problem2_24_y3 x + x = 0 := by
  rw [fmt.problem2_24_eval_eq_last_exact_of_finiteSystem_last_sum hlast]

/-- In the final-exact branch, a zero result forces the third rounded
intermediate to be `-x`. -/
theorem problem2_24_y3_eq_neg_x_of_eval_eq_zero_of_finiteSystem_last_sum
    {fmt : FloatingPointFormat} {x : ℝ}
    (hlast : fmt.finiteSystem (fmt.problem2_24_y3 x + x))
    (hzero : fmt.problem2_24_eval x = 0) :
    fmt.problem2_24_y3 x = -x := by
  have heval := fmt.problem2_24_eval_eq_last_exact_of_finiteSystem_last_sum hlast
  linarith

/-- In the final-exact branch, it is enough to prove that the last exact sum is
nonzero. -/
theorem problem2_24_eval_ne_zero_of_finiteSystem_last_sum_of_last_sum_ne_zero
    {fmt : FloatingPointFormat} {x : ℝ}
    (hlast : fmt.finiteSystem (fmt.problem2_24_y3 x + x))
    (hne : fmt.problem2_24_y3 x + x ≠ 0) :
    fmt.problem2_24_eval x ≠ 0 := by
  intro hzero
  have heval := fmt.problem2_24_eval_eq_last_exact_of_finiteSystem_last_sum hlast
  rw [heval] at hzero
  exact hne hzero

/-- If every exact intermediate in the displayed path is finite representable,
the finite round-to-even evaluation computes the exact polynomial `3*x - 1`. -/
theorem problem2_24_eval_eq_three_mul_sub_one_of_finiteSystem_intermediates
    {fmt : FloatingPointFormat} {x : ℝ}
    (h1 : fmt.finiteSystem (x - (1 / 2 : ℝ)))
    (h2 : fmt.finiteSystem ((x - (1 / 2 : ℝ)) + x))
    (h3 : fmt.finiteSystem (((x - (1 / 2 : ℝ)) + x) - (1 / 2 : ℝ)))
    (h4 : fmt.finiteSystem ((((x - (1 / 2 : ℝ)) + x) - (1 / 2 : ℝ)) + x)) :
    fmt.problem2_24_eval x = 3 * x - 1 := by
  have hy1 :
      fmt.finiteRoundToEvenOp BasicOp.sub x (1 / 2 : ℝ) =
        x - (1 / 2 : ℝ) := by
    simpa [BasicOp.exact] using
      (fmt.finiteRoundToEvenOp_eq_exact_of_finiteSystem
        (op := BasicOp.sub) (x := x) (y := (1 / 2 : ℝ)) h1)
  have hy2 :
      fmt.finiteRoundToEvenOp BasicOp.add
          (fmt.finiteRoundToEvenOp BasicOp.sub x (1 / 2 : ℝ)) x =
        (x - (1 / 2 : ℝ)) + x := by
    rw [hy1]
    simpa [BasicOp.exact] using
      (fmt.finiteRoundToEvenOp_eq_exact_of_finiteSystem
        (op := BasicOp.add) (x := x - (1 / 2 : ℝ)) (y := x) h2)
  have hy3 :
      fmt.finiteRoundToEvenOp BasicOp.sub
          (fmt.finiteRoundToEvenOp BasicOp.add
            (fmt.finiteRoundToEvenOp BasicOp.sub x (1 / 2 : ℝ)) x)
          (1 / 2 : ℝ) =
        ((x - (1 / 2 : ℝ)) + x) - (1 / 2 : ℝ) := by
    rw [hy2]
    simpa [BasicOp.exact] using
      (fmt.finiteRoundToEvenOp_eq_exact_of_finiteSystem
        (op := BasicOp.sub) (x := (x - (1 / 2 : ℝ)) + x)
        (y := (1 / 2 : ℝ)) h3)
  have hy4 :
      fmt.finiteRoundToEvenOp BasicOp.add
          (fmt.finiteRoundToEvenOp BasicOp.sub
            (fmt.finiteRoundToEvenOp BasicOp.add
              (fmt.finiteRoundToEvenOp BasicOp.sub x (1 / 2 : ℝ)) x)
            (1 / 2 : ℝ)) x =
        (((x - (1 / 2 : ℝ)) + x) - (1 / 2 : ℝ)) + x := by
    rw [hy3]
    simpa [BasicOp.exact] using
      (fmt.finiteRoundToEvenOp_eq_exact_of_finiteSystem
        (op := BasicOp.add)
        (x := ((x - (1 / 2 : ℝ)) + x) - (1 / 2 : ℝ)) (y := x) h4)
  change
    fmt.finiteRoundToEvenOp BasicOp.add
        (fmt.finiteRoundToEvenOp BasicOp.sub
          (fmt.finiteRoundToEvenOp BasicOp.add
            (fmt.finiteRoundToEvenOp BasicOp.sub x (1 / 2 : ℝ)) x)
          (1 / 2 : ℝ)) x = 3 * x - 1
  calc
    fmt.finiteRoundToEvenOp BasicOp.add
        (fmt.finiteRoundToEvenOp BasicOp.sub
          (fmt.finiteRoundToEvenOp BasicOp.add
            (fmt.finiteRoundToEvenOp BasicOp.sub x (1 / 2 : ℝ)) x)
          (1 / 2 : ℝ)) x
        = (((x - (1 / 2 : ℝ)) + x) - (1 / 2 : ℝ)) + x := hy4
    _ = problem2_24_exactExpr x := rfl
    _ = 3 * x - 1 := problem2_24_exactExpr_eq_three_mul_sub_one x

/-- If every exact intermediate in the displayed path is finite representable,
the rounded path computes the literal exact expression before simplification. -/
theorem problem2_24_eval_eq_exactExpr_of_finiteSystem_intermediates
    {fmt : FloatingPointFormat} {x : ℝ}
    (h1 : fmt.finiteSystem (x - (1 / 2 : ℝ)))
    (h2 : fmt.finiteSystem ((x - (1 / 2 : ℝ)) + x))
    (h3 : fmt.finiteSystem (((x - (1 / 2 : ℝ)) + x) - (1 / 2 : ℝ)))
    (h4 : fmt.finiteSystem ((((x - (1 / 2 : ℝ)) + x) - (1 / 2 : ℝ)) + x)) :
    fmt.problem2_24_eval x = problem2_24_exactExpr x := by
  rw [fmt.problem2_24_eval_eq_three_mul_sub_one_of_finiteSystem_intermediates
    h1 h2 h3 h4, problem2_24_exactExpr_eq_three_mul_sub_one]

/-- In the exact-intermediate branch, a zero final value would force `x = 1/3`. -/
theorem problem2_24_eq_one_third_of_eval_eq_zero_of_finiteSystem_intermediates
    {fmt : FloatingPointFormat} {x : ℝ}
    (h1 : fmt.finiteSystem (x - (1 / 2 : ℝ)))
    (h2 : fmt.finiteSystem ((x - (1 / 2 : ℝ)) + x))
    (h3 : fmt.finiteSystem (((x - (1 / 2 : ℝ)) + x) - (1 / 2 : ℝ)))
    (h4 : fmt.finiteSystem ((((x - (1 / 2 : ℝ)) + x) - (1 / 2 : ℝ)) + x))
    (hzero : fmt.problem2_24_eval x = 0) :
    x = (1 / 3 : ℝ) := by
  have heval :=
    fmt.problem2_24_eval_eq_three_mul_sub_one_of_finiteSystem_intermediates
      h1 h2 h3 h4
  linarith

/-- In the exact-intermediate branch, any input known not to be `1/3` gives a
nonzero Problem 2.24 value. -/
theorem problem2_24_eval_ne_zero_of_finiteSystem_intermediates_of_ne_one_third
    {fmt : FloatingPointFormat} {x : ℝ}
    (hxthird : x ≠ (1 / 3 : ℝ))
    (h1 : fmt.finiteSystem (x - (1 / 2 : ℝ)))
    (h2 : fmt.finiteSystem ((x - (1 / 2 : ℝ)) + x))
    (h3 : fmt.finiteSystem (((x - (1 / 2 : ℝ)) + x) - (1 / 2 : ℝ)))
    (h4 : fmt.finiteSystem ((((x - (1 / 2 : ℝ)) + x) - (1 / 2 : ℝ)) + x)) :
    fmt.problem2_24_eval x ≠ 0 := by
  intro hzero
  exact hxthird
    (fmt.problem2_24_eq_one_third_of_eval_eq_zero_of_finiteSystem_intermediates
      h1 h2 h3 h4 hzero)

/-- Contrapositive form of the exact-intermediate branch: for any input known
not to be `1/3`, a zero result can occur only if at least one of the four exact
intermediates is not finite representable. -/
theorem problem2_24_eval_eq_zero_implies_not_all_finiteSystem_intermediates_of_ne_one_third
    {fmt : FloatingPointFormat} {x : ℝ}
    (hxthird : x ≠ (1 / 3 : ℝ))
    (hzero : fmt.problem2_24_eval x = 0) :
    ¬ (fmt.finiteSystem (x - (1 / 2 : ℝ)) ∧
      fmt.finiteSystem ((x - (1 / 2 : ℝ)) + x) ∧
      fmt.finiteSystem (((x - (1 / 2 : ℝ)) + x) - (1 / 2 : ℝ)) ∧
      fmt.finiteSystem ((((x - (1 / 2 : ℝ)) + x) - (1 / 2 : ℝ)) + x)) := by
  intro hfin
  exact
    (fmt.problem2_24_eval_ne_zero_of_finiteSystem_intermediates_of_ne_one_third
      hxthird hfin.1 hfin.2.1 hfin.2.2.1 hfin.2.2.2) hzero

/-- Disjunctive branch-audit form of
`problem2_24_eval_eq_zero_implies_not_all_finiteSystem_intermediates_of_ne_one_third`. -/
theorem problem2_24_eval_eq_zero_implies_exists_nonfinite_exact_intermediate_of_ne_one_third
    {fmt : FloatingPointFormat} {x : ℝ}
    (hxthird : x ≠ (1 / 3 : ℝ))
    (hzero : fmt.problem2_24_eval x = 0) :
    ¬ fmt.finiteSystem (x - (1 / 2 : ℝ)) ∨
      ¬ fmt.finiteSystem ((x - (1 / 2 : ℝ)) + x) ∨
      ¬ fmt.finiteSystem (((x - (1 / 2 : ℝ)) + x) - (1 / 2 : ℝ)) ∨
      ¬ fmt.finiteSystem
        ((((x - (1 / 2 : ℝ)) + x) - (1 / 2 : ℝ)) + x) := by
  classical
  by_cases h1 : fmt.finiteSystem (x - (1 / 2 : ℝ))
  · by_cases h2 : fmt.finiteSystem ((x - (1 / 2 : ℝ)) + x)
    · by_cases h3 :
        fmt.finiteSystem (((x - (1 / 2 : ℝ)) + x) - (1 / 2 : ℝ))
      · by_cases h4 :
          fmt.finiteSystem ((((x - (1 / 2 : ℝ)) + x) - (1 / 2 : ℝ)) + x)
        · exact False.elim
            ((fmt.problem2_24_eval_eq_zero_implies_not_all_finiteSystem_intermediates_of_ne_one_third
              hxthird hzero) ⟨h1, h2, h3, h4⟩)
        · exact Or.inr (Or.inr (Or.inr h4))
      · exact Or.inr (Or.inr (Or.inl h3))
    · exact Or.inr (Or.inl h2)
  · exact Or.inl h1

/-- If finite round-to-even returns zero and the smallest subnormal value is
present in the format, then the exact input was within half a smallest
subnormal spacing of zero.  This is the converse direction needed to sharpen
Problem 2.24 zero-result branches. -/
theorem finiteRoundToEven_eq_zero_abs_le_half_minSubnormalMagnitude_of_subnormalMantissa_one
    {fmt : FloatingPointFormat} {s : ℝ}
    (hsub : fmt.subnormalMantissa 1)
    (hzero : fmt.finiteRoundToEven s = 0) :
    |s| ≤ (1 / 2 : ℝ) * fmt.minSubnormalMagnitude := by
  have hround : fmt.nearestRoundingToFinite s 0 := by
    simpa [hzero] using fmt.finiteRoundToEven_nearestRoundingToFinite s
  have hminpos : fmt.finiteSystem fmt.minSubnormalMagnitude := by
    exact Or.inr (Or.inr
      (fmt.minSubnormalMagnitude_mem_subnormalSystem_of_subnormalMantissa_one
        hsub))
  have hminneg : fmt.finiteSystem (-fmt.minSubnormalMagnitude) := by
    exact fmt.finiteSystem_neg hminpos
  by_cases hs_nonneg : 0 ≤ s
  · have hdist := nearestRoundingIn_minimal hround hminpos
    have hs_abs : |s| = s := abs_of_nonneg hs_nonneg
    have hdist' : s ≤ |s - fmt.minSubnormalMagnitude| := by
      simpa [hs_abs] using hdist
    by_cases hs_min_nonpos : s - fmt.minSubnormalMagnitude ≤ 0
    · have hdist_expr :
          |s - fmt.minSubnormalMagnitude| =
            fmt.minSubnormalMagnitude - s := by
        rw [abs_of_nonpos hs_min_nonpos]
        ring
      rw [hdist_expr] at hdist'
      nlinarith
    · have hpos : 0 < s - fmt.minSubnormalMagnitude :=
        lt_of_not_ge hs_min_nonpos
      have hdist_expr :
          |s - fmt.minSubnormalMagnitude| =
            s - fmt.minSubnormalMagnitude := by
        rw [abs_of_pos hpos]
      rw [hdist_expr] at hdist'
      nlinarith [fmt.minSubnormalMagnitude_pos]
  · have hs_nonpos : s ≤ 0 := le_of_not_ge hs_nonneg
    have hdist := nearestRoundingIn_minimal hround hminneg
    have hs_abs : |s| = -s := abs_of_nonpos hs_nonpos
    have hdist' : -s ≤ |s - (-fmt.minSubnormalMagnitude)| := by
      simpa [hs_abs] using hdist
    by_cases hs_negmin_nonneg : 0 ≤ s - (-fmt.minSubnormalMagnitude)
    · have hdist_expr :
          |s - (-fmt.minSubnormalMagnitude)| =
            s + fmt.minSubnormalMagnitude := by
        rw [abs_of_nonneg hs_negmin_nonneg]
        ring
      rw [hdist_expr] at hdist'
      nlinarith
    · have hneg : s - (-fmt.minSubnormalMagnitude) < 0 :=
        lt_of_not_ge hs_negmin_nonneg
      have hdist_expr :
          |s - (-fmt.minSubnormalMagnitude)| =
            -(s + fmt.minSubnormalMagnitude) := by
        rw [abs_of_neg hneg]
        ring
      rw [hdist_expr] at hdist'
      nlinarith [fmt.minSubnormalMagnitude_pos]

/-- Every finite-system value lies on the integer lattice generated by the
smallest subnormal spacing `minSubnormalMagnitude`. -/
theorem finiteSystem_exists_int_mul_minSubnormalMagnitude
    {fmt : FloatingPointFormat} {y : ℝ}
    (hy : fmt.finiteSystem y) :
    ∃ k : ℤ, y = (k : ℝ) * fmt.minSubnormalMagnitude := by
  rcases hy with hzero | hnorm | hsub
  · subst y
    exact ⟨0, by simp⟩
  · rcases hnorm with ⟨negative, m, e, hm, he, rfl⟩
    let shift : ℕ := Int.toNat (e - fmt.emin)
    have hshift_cast : ((shift : ℕ) : ℤ) = e - fmt.emin := by
      have hnonneg : 0 ≤ e - fmt.emin := sub_nonneg.mpr he.1
      simpa [shift] using Int.toNat_of_nonneg hnonneg
    have hshift_endpoint : e - (shift : ℤ) = fmt.emin := by
      omega
    let coeff : ℕ := m * fmt.beta ^ shift
    let k : ℤ := if negative then -((coeff : ℤ)) else (coeff : ℤ)
    refine ⟨k, ?_⟩
    have hrepr :
        fmt.normalizedValue negative m e =
          fmt.subnormalValue negative coeff := by
      simpa [coeff] using
        fmt.normalizedValue_eq_subnormalValue_mul_beta_pow_of_subExponent_eq_emin
          negative m shift e hshift_endpoint
    rw [hrepr]
    cases negative <;>
      simp [k, coeff, subnormalValue, signValue, minSubnormalMagnitude]
  · rcases hsub with ⟨negative, m, _hm, rfl⟩
    let k : ℤ := if negative then -((m : ℤ)) else (m : ℤ)
    refine ⟨k, ?_⟩
    cases negative <;>
      simp [k, subnormalValue, signValue, minSubnormalMagnitude]

/-- A nonzero integer multiple of the smallest subnormal spacing has magnitude
at least one smallest-subnormal spacing. -/
theorem int_mul_minSubnormalMagnitude_abs_ge_of_ne_zero
    {fmt : FloatingPointFormat} {k : ℤ}
    (hk : (k : ℝ) * fmt.minSubnormalMagnitude ≠ 0) :
    fmt.minSubnormalMagnitude ≤
      |(k : ℝ) * fmt.minSubnormalMagnitude| := by
  have hk_ne : k ≠ 0 := by
    intro hkzero
    exact hk (by simp [hkzero])
  have hk_abs_ge_int : (1 : ℤ) ≤ |k| := Int.one_le_abs hk_ne
  have hk_abs_ge : (1 : ℝ) ≤ |(k : ℝ)| := by
    rw [← Int.cast_abs]
    exact_mod_cast hk_abs_ge_int
  have hmul :=
    mul_le_mul_of_nonneg_right hk_abs_ge
      (le_of_lt fmt.minSubnormalMagnitude_pos)
  simpa [abs_mul, abs_of_pos fmt.minSubnormalMagnitude_pos] using hmul

/-- Two finite-system values cannot have a nonzero sum whose magnitude is at
most half the smallest subnormal spacing. -/
theorem finiteSystem_add_eq_zero_of_abs_le_half_minSubnormalMagnitude
    {fmt : FloatingPointFormat} {x y : ℝ}
    (hx : fmt.finiteSystem x) (hy : fmt.finiteSystem y)
    (hsmall :
      |x + y| ≤ (1 / 2 : ℝ) * fmt.minSubnormalMagnitude) :
    x + y = 0 := by
  rcases fmt.finiteSystem_exists_int_mul_minSubnormalMagnitude hx with
    ⟨kx, hxgrid⟩
  rcases fmt.finiteSystem_exists_int_mul_minSubnormalMagnitude hy with
    ⟨ky, hygrid⟩
  let k : ℤ := kx + ky
  have hsum_grid :
      x + y = (k : ℝ) * fmt.minSubnormalMagnitude := by
    rw [hxgrid, hygrid]
    simp [k]
    ring
  by_contra hne
  have hgrid_ne : (k : ℝ) * fmt.minSubnormalMagnitude ≠ 0 := by
    intro hzero
    exact hne (by rw [hsum_grid, hzero])
  have hge :=
    fmt.int_mul_minSubnormalMagnitude_abs_ge_of_ne_zero hgrid_ne
  have hsmall_grid :
      |(k : ℝ) * fmt.minSubnormalMagnitude| ≤
        (1 / 2 : ℝ) * fmt.minSubnormalMagnitude := by
    simpa [hsum_grid] using hsmall
  nlinarith [fmt.minSubnormalMagnitude_pos]

/-- Problem 2.24 zero-result last-sum sharpening: if the final rounded addition
returns zero, then the exact last sum is within half a smallest subnormal
spacing, provided that smallest subnormal is present in the format. -/
theorem problem2_24_eval_eq_zero_last_sum_abs_le_half_minSubnormalMagnitude
    {fmt : FloatingPointFormat} {x : ℝ}
    (hsub : fmt.subnormalMantissa 1)
    (hzero : fmt.problem2_24_eval x = 0) :
    |fmt.problem2_24_y3 x + x| ≤
      (1 / 2 : ℝ) * fmt.minSubnormalMagnitude := by
  have hrounded :
      fmt.finiteRoundToEvenOp BasicOp.add (fmt.problem2_24_y3 x) x = 0 := by
    simpa [problem2_24_eval_eq_rounded_last_sum] using hzero
  have hround :
      fmt.finiteRoundToEven (fmt.problem2_24_y3 x + x) = 0 := by
    simpa [finiteRoundToEvenOp, BasicOp.exact] using hrounded
  exact
    fmt.finiteRoundToEven_eq_zero_abs_le_half_minSubnormalMagnitude_of_subnormalMantissa_one
      hsub hround

/-- The third rounded intermediate in the Problem 2.24 path is a finite-system
value. -/
theorem problem2_24_y3_finiteSystem
    {fmt : FloatingPointFormat} (x : ℝ) :
    fmt.finiteSystem (fmt.problem2_24_y3 x) := by
  simpa [problem2_24_y3] using
    fmt.finiteRoundToEvenOp_finiteSystem BasicOp.sub
      (fmt.problem2_24_y2 x) (1 / 2 : ℝ)

/-- The first rounded intermediate in the Problem 2.24 path is a finite-system
value. -/
theorem problem2_24_y1_finiteSystem
    {fmt : FloatingPointFormat} (x : ℝ) :
    fmt.finiteSystem (fmt.problem2_24_y1 x) := by
  simpa [problem2_24_y1] using
    fmt.finiteRoundToEvenOp_finiteSystem BasicOp.sub x (1 / 2 : ℝ)

/-- The second rounded intermediate in the Problem 2.24 path is a finite-system
value. -/
theorem problem2_24_y2_finiteSystem
    {fmt : FloatingPointFormat} (x : ℝ) :
    fmt.finiteSystem (fmt.problem2_24_y2 x) := by
  simpa [problem2_24_y2] using
    fmt.finiteRoundToEvenOp_finiteSystem BasicOp.add
      (fmt.problem2_24_y1 x) x

/-- The first rounded intermediate is a nearest finite value to the exact
first-step input `x - 1/2`. -/
theorem problem2_24_y1_first_sub_nearestRoundingToFinite
    {fmt : FloatingPointFormat} (x : ℝ) :
    fmt.nearestRoundingToFinite
      (x - (1 / 2 : ℝ)) (fmt.problem2_24_y1 x) := by
  have hround :=
    fmt.finiteRoundToEvenOp_nearestRoundingToFinite BasicOp.sub
      x (1 / 2 : ℝ)
  simpa [problem2_24_y1, BasicOp.exact] using hround

/-- For a finite-system input, the first rounded intermediate is within `1/2`
of the exact first-step input after comparing with the finite candidate `x`. -/
theorem problem2_24_y1_first_sub_distance_to_x_le_half
    {fmt : FloatingPointFormat} {x : ℝ}
    (hx : fmt.finiteSystem x) :
    |(x - (1 / 2 : ℝ)) - fmt.problem2_24_y1 x| ≤ (1 / 2 : ℝ) := by
  have hmin :=
    nearestRoundingIn_minimal
      (fmt.problem2_24_y1_first_sub_nearestRoundingToFinite x) hx
  have hright :
      |(x - (1 / 2 : ℝ)) - x| = (1 / 2 : ℝ) := by
    have hrewrite : (x - (1 / 2 : ℝ)) - x = -(1 / 2 : ℝ) := by
      ring
    rw [hrewrite]
    norm_num
  simpa [hright] using hmin

/-- Comparing the first rounded intermediate against the finite candidate zero
gives an algebraic sign-cell constraint around `x = 1/2`. -/
theorem problem2_24_y1_first_sub_distance_to_zero_product_le
    {fmt : FloatingPointFormat} {x : ℝ} :
    fmt.problem2_24_y1 x *
        (fmt.problem2_24_y1 x - (2 * x - 1)) ≤ 0 := by
  have hmin :=
    nearestRoundingIn_minimal
      (fmt.problem2_24_y1_first_sub_nearestRoundingToFinite x)
      fmt.finiteSystem_zero
  have hright :
      |(x - (1 / 2 : ℝ)) - (0 : ℝ)| =
        |x - (1 / 2 : ℝ)| := by
    ring_nf
  rw [hright] at hmin
  have hsquares :
      ((x - (1 / 2 : ℝ)) - fmt.problem2_24_y1 x) ^ 2 ≤
        (x - (1 / 2 : ℝ)) ^ 2 := by
    exact sq_le_sq.mpr hmin
  nlinarith

/-- For a finite-system input, comparing the first rounded subtraction against
the finite candidate `-x` gives a lower-half product constraint. -/
theorem problem2_24_y1_first_sub_distance_to_neg_x_product_nonneg_of_finiteSystem_input
    {fmt : FloatingPointFormat} {x : ℝ}
    (hx : fmt.finiteSystem x) :
    0 ≤ (fmt.problem2_24_y1 x + x) *
        (3 * x - 1 - fmt.problem2_24_y1 x) := by
  have hnegx : fmt.finiteSystem (-x) :=
    fmt.finiteSystem_neg hx
  have hmin :=
    nearestRoundingIn_minimal
      (fmt.problem2_24_y1_first_sub_nearestRoundingToFinite x) hnegx
  have hright :
      |(x - (1 / 2 : ℝ)) - (-x)| =
        |2 * x - (1 / 2 : ℝ)| := by
    congr 1
    ring
  rw [hright] at hmin
  have hsquares :
      ((x - (1 / 2 : ℝ)) - fmt.problem2_24_y1 x) ^ 2 ≤
        (2 * x - (1 / 2 : ℝ)) ^ 2 := by
    exact sq_le_sq.mpr hmin
  nlinarith

/-- On any branch where the exact second-step input `y1+x` is positive, the
first-step `-x` comparison forces `y1 <= 3*x - 1`. -/
theorem problem2_24_y1_le_three_mul_x_sub_one_of_y1_add_x_pos_finiteSystem_input
    {fmt : FloatingPointFormat} {x : ℝ}
    (hx : fmt.finiteSystem x)
    (hpos : 0 < fmt.problem2_24_y1 x + x) :
    fmt.problem2_24_y1 x ≤ 3 * x - 1 := by
  have hprod :=
    fmt.problem2_24_y1_first_sub_distance_to_neg_x_product_nonneg_of_finiteSystem_input
      hx
  nlinarith

/-- If `x >= 1/2`, then the first rounded intermediate is nonnegative. -/
theorem problem2_24_y1_nonneg_of_half_le
    {fmt : FloatingPointFormat} {x : ℝ}
    (hx : (1 / 2 : ℝ) ≤ x) :
    0 ≤ fmt.problem2_24_y1 x := by
  have hprod :=
    fmt.problem2_24_y1_first_sub_distance_to_zero_product_le (x := x)
  by_contra hneg
  have hyneg : fmt.problem2_24_y1 x < 0 := lt_of_not_ge hneg
  nlinarith

/-- If `x >= 1/2`, then `y1` stays below the opposite endpoint of the
zero-candidate cell. -/
theorem problem2_24_y1_le_two_mul_x_sub_one_of_half_le
    {fmt : FloatingPointFormat} {x : ℝ}
    (hx : (1 / 2 : ℝ) ≤ x) :
    fmt.problem2_24_y1 x ≤ 2 * x - 1 := by
  have hprod :=
    fmt.problem2_24_y1_first_sub_distance_to_zero_product_le (x := x)
  have hy_nonneg : 0 ≤ fmt.problem2_24_y1 x :=
    fmt.problem2_24_y1_nonneg_of_half_le hx
  by_contra hle
  have hygt : 2 * x - 1 < fmt.problem2_24_y1 x := lt_of_not_ge hle
  nlinarith

/-- First-step sign-cell form above the midpoint. -/
theorem problem2_24_y1_between_zero_and_two_mul_x_sub_one_of_half_le
    {fmt : FloatingPointFormat} {x : ℝ}
    (hx : (1 / 2 : ℝ) ≤ x) :
    0 ≤ fmt.problem2_24_y1 x ∧
      fmt.problem2_24_y1 x ≤ 2 * x - 1 :=
  ⟨fmt.problem2_24_y1_nonneg_of_half_le hx,
    fmt.problem2_24_y1_le_two_mul_x_sub_one_of_half_le hx⟩

/-- If `x <= 1/2`, then the first rounded intermediate is nonpositive. -/
theorem problem2_24_y1_nonpos_of_le_half
    {fmt : FloatingPointFormat} {x : ℝ}
    (hx : x ≤ (1 / 2 : ℝ)) :
    fmt.problem2_24_y1 x ≤ 0 := by
  have hprod :=
    fmt.problem2_24_y1_first_sub_distance_to_zero_product_le (x := x)
  by_contra hle
  have hypos : 0 < fmt.problem2_24_y1 x := lt_of_not_ge hle
  nlinarith

/-- If `x <= 1/2`, then `y1` stays above the opposite endpoint of the
zero-candidate cell. -/
theorem problem2_24_two_mul_x_sub_one_le_y1_of_le_half
    {fmt : FloatingPointFormat} {x : ℝ}
    (hx : x ≤ (1 / 2 : ℝ)) :
    2 * x - 1 ≤ fmt.problem2_24_y1 x := by
  have hprod :=
    fmt.problem2_24_y1_first_sub_distance_to_zero_product_le (x := x)
  have hy_nonpos : fmt.problem2_24_y1 x ≤ 0 :=
    fmt.problem2_24_y1_nonpos_of_le_half hx
  by_contra hle
  have hylt : fmt.problem2_24_y1 x < 2 * x - 1 := lt_of_not_ge hle
  nlinarith

/-- First-step sign-cell form below the midpoint. -/
theorem problem2_24_y1_between_two_mul_x_sub_one_and_zero_of_le_half
    {fmt : FloatingPointFormat} {x : ℝ}
    (hx : x ≤ (1 / 2 : ℝ)) :
    2 * x - 1 ≤ fmt.problem2_24_y1 x ∧
      fmt.problem2_24_y1 x ≤ 0 :=
  ⟨fmt.problem2_24_two_mul_x_sub_one_le_y1_of_le_half hx,
    fmt.problem2_24_y1_nonpos_of_le_half hx⟩

/-- For a finite-system input, the first rounded intermediate lies in the
closed interval `[x - 1, x]`. -/
theorem problem2_24_y1_between_x_sub_one_and_x_of_finiteSystem_input
    {fmt : FloatingPointFormat} {x : ℝ}
    (hx : fmt.finiteSystem x) :
    x - 1 ≤ fmt.problem2_24_y1 x ∧
      fmt.problem2_24_y1 x ≤ x := by
  have hdist :=
    fmt.problem2_24_y1_first_sub_distance_to_x_le_half hx
  rcases abs_le.mp hdist with ⟨hlo, hhi⟩
  constructor <;> linarith

/-- Sterbenz exactness for the first subtraction in the Problem 2.24 path. -/
theorem problem2_24_y1_eq_x_sub_half_of_finiteSystem_input_of_quarter_lt_of_lt_one
    {fmt : FloatingPointFormat} {x : ℝ}
    (hhalf : fmt.finiteSystem (1 / 2 : ℝ))
    (hx : fmt.finiteSystem x)
    (hxquarter : (1 / 4 : ℝ) < x)
    (hxlt_one : x < (1 : ℝ)) :
    fmt.problem2_24_y1 x = x - (1 / 2 : ℝ) := by
  have hsterbenz :
      fmt.sterbenzRatioCondition x (1 / 2 : ℝ) := by
    unfold sterbenzRatioCondition
    constructor
    · norm_num
      exact hxquarter
    · norm_num
      exact hxlt_one
  simpa [problem2_24_y1] using
    (fmt.finiteRoundToEvenOp_sub_finiteSystem_eq_exact_of_sterbenzRatioCondition
      (x := x) (y := (1 / 2 : ℝ)) hx hhalf hsterbenz)

/-- On the Sterbenz-exact first-subtraction range, the exact first
intermediate `x - 1/2` is itself finite-system representable. -/
theorem problem2_24_first_exact_intermediate_finiteSystem_of_quarter_lt_of_lt_one
    {fmt : FloatingPointFormat} {x : ℝ}
    (hhalf : fmt.finiteSystem (1 / 2 : ℝ))
    (hx : fmt.finiteSystem x)
    (hxquarter : (1 / 4 : ℝ) < x)
    (hxlt_one : x < (1 : ℝ)) :
    fmt.finiteSystem (x - (1 / 2 : ℝ)) := by
  have hy1eq :
      fmt.problem2_24_y1 x = x - (1 / 2 : ℝ) :=
    fmt.problem2_24_y1_eq_x_sub_half_of_finiteSystem_input_of_quarter_lt_of_lt_one
      hhalf hx hxquarter hxlt_one
  rw [← hy1eq]
  exact fmt.problem2_24_y1_finiteSystem x

/-- The second rounded intermediate is a nearest finite value to the exact
second-step input `y1 + x`. -/
theorem problem2_24_y2_second_add_nearestRoundingToFinite
    {fmt : FloatingPointFormat} (x : ℝ) :
    fmt.nearestRoundingToFinite
      (fmt.problem2_24_y1 x + x) (fmt.problem2_24_y2 x) := by
  have hround :=
    fmt.finiteRoundToEvenOp_nearestRoundingToFinite BasicOp.add
      (fmt.problem2_24_y1 x) x
  simpa [problem2_24_y2, BasicOp.exact] using hround

/-- Sterbenz exactness for the second addition in the lower sub-third branch
of the Problem 2.24 path. -/
theorem problem2_24_y2_eq_two_mul_x_sub_half_of_finiteSystem_input_of_quarter_lt_of_lt_one_third
    {fmt : FloatingPointFormat} {x : ℝ}
    (hhalf : fmt.finiteSystem (1 / 2 : ℝ))
    (hx : fmt.finiteSystem x)
    (hxquarter : (1 / 4 : ℝ) < x)
    (hxlt_third : x < (1 / 3 : ℝ)) :
    fmt.problem2_24_y2 x = 2 * x - (1 / 2 : ℝ) := by
  have hy1eq :
      fmt.problem2_24_y1 x = x - (1 / 2 : ℝ) :=
    fmt.problem2_24_y1_eq_x_sub_half_of_finiteSystem_input_of_quarter_lt_of_lt_one
      hhalf hx hxquarter (by nlinarith : x < (1 : ℝ))
  have hneg_y1 : fmt.finiteSystem (-(fmt.problem2_24_y1 x)) :=
    fmt.finiteSystem_neg (fmt.problem2_24_y1_finiteSystem x)
  have hcomp : fmt.finiteSystem ((1 / 2 : ℝ) - x) := by
    convert hneg_y1 using 1
    rw [hy1eq]
    ring
  have hsterbenz :
      fmt.sterbenzRatioCondition x ((1 / 2 : ℝ) - x) := by
    unfold sterbenzRatioCondition
    constructor <;> nlinarith
  have hdiff :
      fmt.finiteSystem (x - ((1 / 2 : ℝ) - x)) :=
    fmt.finiteSystem_sub_finiteSystem_of_sterbenzRatioCondition
      hx hcomp hsterbenz
  have hsum :
      fmt.finiteSystem (fmt.problem2_24_y1 x + x) := by
    convert hdiff using 1
    rw [hy1eq]
    ring
  have hy2exact :
      fmt.problem2_24_y2 x = fmt.problem2_24_y1 x + x := by
    simpa [problem2_24_y2, BasicOp.exact] using
      (fmt.finiteRoundToEvenOp_eq_exact_of_finiteSystem
        (op := BasicOp.add) (x := fmt.problem2_24_y1 x) (y := x) hsum)
  rw [hy2exact, hy1eq]
  ring

/-- In the lower sub-third Sterbenz branch, the second exact real
intermediate `(x - 1/2) + x` is finite-system representable. -/
theorem problem2_24_second_exact_intermediate_finiteSystem_of_quarter_lt_of_lt_one_third
    {fmt : FloatingPointFormat} {x : ℝ}
    (hhalf : fmt.finiteSystem (1 / 2 : ℝ))
    (hx : fmt.finiteSystem x)
    (hxquarter : (1 / 4 : ℝ) < x)
    (hxlt_third : x < (1 / 3 : ℝ)) :
    fmt.finiteSystem ((x - (1 / 2 : ℝ)) + x) := by
  have hy2eq :
      fmt.problem2_24_y2 x = 2 * x - (1 / 2 : ℝ) :=
    fmt.problem2_24_y2_eq_two_mul_x_sub_half_of_finiteSystem_input_of_quarter_lt_of_lt_one_third
      hhalf hx hxquarter hxlt_third
  have hsum : (x - (1 / 2 : ℝ)) + x = 2 * x - (1 / 2 : ℝ) := by
    ring
  rw [hsum, ← hy2eq]
  exact fmt.problem2_24_y2_finiteSystem x

/-- The second rounded intermediate is at least as close to `y1 + x` as zero
is. -/
theorem problem2_24_y2_second_add_distance_to_zero_le_self
    {fmt : FloatingPointFormat} {x : ℝ} :
    |(fmt.problem2_24_y1 x + x) - fmt.problem2_24_y2 x| ≤
      |fmt.problem2_24_y1 x + x| := by
  have hmin :=
    nearestRoundingIn_minimal
      (fmt.problem2_24_y2_second_add_nearestRoundingToFinite x)
      fmt.finiteSystem_zero
  simpa using hmin

/-- Comparing the second rounded intermediate against the finite candidate zero
gives a sign-cell constraint around the exact second-step input `y1 + x`. -/
theorem problem2_24_y2_second_add_distance_to_zero_product_le
    {fmt : FloatingPointFormat} {x : ℝ} :
    fmt.problem2_24_y2 x *
        (fmt.problem2_24_y2 x - 2 * (fmt.problem2_24_y1 x + x)) ≤ 0 := by
  have hmin :=
    problem2_24_y2_second_add_distance_to_zero_le_self
      (fmt := fmt) (x := x)
  have hsquares :
      ((fmt.problem2_24_y1 x + x) - fmt.problem2_24_y2 x) ^ 2 ≤
        (fmt.problem2_24_y1 x + x) ^ 2 := by
    exact sq_le_sq.mpr hmin
  nlinarith

/-- If the exact second-step input is nonnegative, then the second rounded
intermediate is nonnegative. -/
theorem problem2_24_y2_nonneg_of_y1_add_x_nonneg
    {fmt : FloatingPointFormat} {x : ℝ}
    (h : 0 ≤ fmt.problem2_24_y1 x + x) :
    0 ≤ fmt.problem2_24_y2 x := by
  have hprod :=
    fmt.problem2_24_y2_second_add_distance_to_zero_product_le (x := x)
  by_contra hneg
  have hyneg : fmt.problem2_24_y2 x < 0 := lt_of_not_ge hneg
  nlinarith

/-- If the exact second-step input is nonnegative, then `y2` stays below twice
that input. -/
theorem problem2_24_y2_le_two_mul_y1_add_x_of_y1_add_x_nonneg
    {fmt : FloatingPointFormat} {x : ℝ}
    (h : 0 ≤ fmt.problem2_24_y1 x + x) :
    fmt.problem2_24_y2 x ≤ 2 * (fmt.problem2_24_y1 x + x) := by
  have hprod :=
    fmt.problem2_24_y2_second_add_distance_to_zero_product_le (x := x)
  have hy_nonneg : 0 ≤ fmt.problem2_24_y2 x :=
    fmt.problem2_24_y2_nonneg_of_y1_add_x_nonneg h
  by_contra hle
  have hygt :
      2 * (fmt.problem2_24_y1 x + x) < fmt.problem2_24_y2 x :=
    lt_of_not_ge hle
  nlinarith

/-- Second-step sign-cell form for nonnegative exact second-step input. -/
theorem problem2_24_y2_between_zero_and_two_mul_y1_add_x_of_y1_add_x_nonneg
    {fmt : FloatingPointFormat} {x : ℝ}
    (h : 0 ≤ fmt.problem2_24_y1 x + x) :
    0 ≤ fmt.problem2_24_y2 x ∧
      fmt.problem2_24_y2 x ≤ 2 * (fmt.problem2_24_y1 x + x) :=
  ⟨fmt.problem2_24_y2_nonneg_of_y1_add_x_nonneg h,
    fmt.problem2_24_y2_le_two_mul_y1_add_x_of_y1_add_x_nonneg h⟩

/-- If the exact second-step input is nonpositive, then the second rounded
intermediate is nonpositive. -/
theorem problem2_24_y2_nonpos_of_y1_add_x_nonpos
    {fmt : FloatingPointFormat} {x : ℝ}
    (h : fmt.problem2_24_y1 x + x ≤ 0) :
    fmt.problem2_24_y2 x ≤ 0 := by
  have hprod :=
    fmt.problem2_24_y2_second_add_distance_to_zero_product_le (x := x)
  by_contra hle
  have hypos : 0 < fmt.problem2_24_y2 x := lt_of_not_ge hle
  nlinarith

/-- If the exact second-step input is nonpositive, then `y2` stays above twice
that input. -/
theorem problem2_24_two_mul_y1_add_x_le_y2_of_y1_add_x_nonpos
    {fmt : FloatingPointFormat} {x : ℝ}
    (h : fmt.problem2_24_y1 x + x ≤ 0) :
    2 * (fmt.problem2_24_y1 x + x) ≤ fmt.problem2_24_y2 x := by
  have hprod :=
    fmt.problem2_24_y2_second_add_distance_to_zero_product_le (x := x)
  have hy_nonpos : fmt.problem2_24_y2 x ≤ 0 :=
    fmt.problem2_24_y2_nonpos_of_y1_add_x_nonpos h
  by_contra hle
  have hylt :
      fmt.problem2_24_y2 x < 2 * (fmt.problem2_24_y1 x + x) :=
    lt_of_not_ge hle
  nlinarith

/-- Second-step sign-cell form for nonpositive exact second-step input. -/
theorem problem2_24_y2_between_two_mul_y1_add_x_and_zero_of_y1_add_x_nonpos
    {fmt : FloatingPointFormat} {x : ℝ}
    (h : fmt.problem2_24_y1 x + x ≤ 0) :
    2 * (fmt.problem2_24_y1 x + x) ≤ fmt.problem2_24_y2 x ∧
      fmt.problem2_24_y2 x ≤ 0 :=
  ⟨fmt.problem2_24_two_mul_y1_add_x_le_y2_of_y1_add_x_nonpos h,
    fmt.problem2_24_y2_nonpos_of_y1_add_x_nonpos h⟩

/-- The second rounded intermediate is at least as close to `y1 + x` as the
finite candidate `y1` is. -/
theorem problem2_24_y2_second_add_distance_to_y1_le_abs_x
    {fmt : FloatingPointFormat} {x : ℝ} :
    |(fmt.problem2_24_y1 x + x) - fmt.problem2_24_y2 x| ≤ |x| := by
  have hmin :=
    nearestRoundingIn_minimal
      (fmt.problem2_24_y2_second_add_nearestRoundingToFinite x)
      (fmt.problem2_24_y1_finiteSystem x)
  have hright :
      |(fmt.problem2_24_y1 x + x) - fmt.problem2_24_y1 x| = |x| := by
    ring_nf
  simpa [hright] using hmin

/-- For a finite-system input, the second rounded intermediate is at least as
close to `y1 + x` as the finite candidate `x` is. -/
theorem problem2_24_y2_second_add_distance_to_x_le_abs_y1
    {fmt : FloatingPointFormat} {x : ℝ}
    (hx : fmt.finiteSystem x) :
    |(fmt.problem2_24_y1 x + x) - fmt.problem2_24_y2 x| ≤
      |fmt.problem2_24_y1 x| := by
  have hmin :=
    nearestRoundingIn_minimal
      (fmt.problem2_24_y2_second_add_nearestRoundingToFinite x) hx
  have hright :
      |(fmt.problem2_24_y1 x + x) - x| =
        |fmt.problem2_24_y1 x| := by
    ring_nf
  simpa [hright] using hmin

/-- Comparing the second rounded intermediate against the finite candidate `x`
gives a second-step product constraint used to rule out upper-half zero
counterexamples. -/
theorem problem2_24_y2_second_add_distance_to_x_product_le_of_finiteSystem_input
    {fmt : FloatingPointFormat} {x : ℝ}
    (hx : fmt.finiteSystem x) :
    (x - fmt.problem2_24_y2 x) *
        (2 * fmt.problem2_24_y1 x + x - fmt.problem2_24_y2 x) ≤ 0 := by
  have hmin :=
    fmt.problem2_24_y2_second_add_distance_to_x_le_abs_y1 hx
  have hsquares :
      ((fmt.problem2_24_y1 x + x) - fmt.problem2_24_y2 x) ^ 2 ≤
        (fmt.problem2_24_y1 x) ^ 2 := by
    exact sq_le_sq.mpr hmin
  nlinarith

/-- For a finite-system input, a zero Problem 2.24 result forces exact
cancellation in the last real sum. -/
theorem problem2_24_eval_eq_zero_last_sum_eq_zero_of_finiteSystem_input
    {fmt : FloatingPointFormat} {x : ℝ}
    (hsub : fmt.subnormalMantissa 1)
    (hx : fmt.finiteSystem x)
    (hzero : fmt.problem2_24_eval x = 0) :
    fmt.problem2_24_y3 x + x = 0 := by
  have hy3 : fmt.finiteSystem (fmt.problem2_24_y3 x) :=
    fmt.problem2_24_y3_finiteSystem x
  have hsmall :
      |fmt.problem2_24_y3 x + x| ≤
        (1 / 2 : ℝ) * fmt.minSubnormalMagnitude :=
    fmt.problem2_24_eval_eq_zero_last_sum_abs_le_half_minSubnormalMagnitude
      hsub hzero
  exact
    fmt.finiteSystem_add_eq_zero_of_abs_le_half_minSubnormalMagnitude
      hy3 hx hsmall

/-- For a finite-system input, a zero Problem 2.24 result forces the third
rounded intermediate to be `-x`. -/
theorem problem2_24_y3_eq_neg_x_of_eval_eq_zero_of_finiteSystem_input
    {fmt : FloatingPointFormat} {x : ℝ}
    (hsub : fmt.subnormalMantissa 1)
    (hx : fmt.finiteSystem x)
    (hzero : fmt.problem2_24_eval x = 0) :
    fmt.problem2_24_y3 x = -x := by
  have hsum :
      fmt.problem2_24_y3 x + x = 0 :=
    fmt.problem2_24_eval_eq_zero_last_sum_eq_zero_of_finiteSystem_input
      hsub hx hzero
  linarith

/-- If the third rounded intermediate is exactly `-x`, then `-x` is a finite
nearest-rounded value of the exact third-step input `y2 - 1/2`. -/
theorem problem2_24_y3_eq_neg_x_last_sub_nearestRoundingToFinite
    {fmt : FloatingPointFormat} {x : ℝ}
    (hcancel : fmt.problem2_24_y3 x = -x) :
    fmt.nearestRoundingToFinite
      (fmt.problem2_24_y2 x - (1 / 2 : ℝ)) (-x) := by
  have hround :=
    fmt.finiteRoundToEvenOp_nearestRoundingToFinite BasicOp.sub
      (fmt.problem2_24_y2 x) (1 / 2 : ℝ)
  rw [← hcancel]
  simpa [problem2_24_y3, BasicOp.exact] using hround

/-- If the third rounded intermediate is exactly `-x`, then `-x` is at least as
close to the exact third-step input `y2 - 1/2` as every finite candidate. -/
theorem problem2_24_y3_eq_neg_x_last_sub_minimal
    {fmt : FloatingPointFormat} {x c : ℝ}
    (hcancel : fmt.problem2_24_y3 x = -x)
    (hc : fmt.finiteSystem c) :
    |(fmt.problem2_24_y2 x - (1 / 2 : ℝ)) - (-x)| ≤
      |(fmt.problem2_24_y2 x - (1 / 2 : ℝ)) - c| :=
  nearestRoundingIn_minimal
    (fmt.problem2_24_y3_eq_neg_x_last_sub_nearestRoundingToFinite hcancel) hc

/-- Exact final cancellation forces the exact third-step input to be within
`1/2` of `-x`, by comparing against the finite candidate `y2`. -/
theorem problem2_24_y3_eq_neg_x_last_sub_distance_to_y2_le_half
    {fmt : FloatingPointFormat} {x : ℝ}
    (hcancel : fmt.problem2_24_y3 x = -x) :
    |fmt.problem2_24_y2 x + x - (1 / 2 : ℝ)| ≤ (1 / 2 : ℝ) := by
  have hmin :=
    fmt.problem2_24_y3_eq_neg_x_last_sub_minimal
      (x := x) (c := fmt.problem2_24_y2 x) hcancel
      (fmt.problem2_24_y2_finiteSystem x)
  have hleft :
      (fmt.problem2_24_y2 x - (1 / 2 : ℝ)) - (-x) =
        fmt.problem2_24_y2 x + x - (1 / 2 : ℝ) := by
    ring
  have hright :
      (fmt.problem2_24_y2 x - (1 / 2 : ℝ)) -
          fmt.problem2_24_y2 x =
        -(1 / 2 : ℝ) := by
    ring
  rw [hleft, hright] at hmin
  norm_num at hmin
  exact hmin

/-- Exact final cancellation makes `-x` at least as close to the exact
third-step input as zero is; algebraically this gives a product constraint on
the remaining zero-counterexample branch. -/
theorem problem2_24_y3_eq_neg_x_last_sub_distance_to_zero_product_le
    {fmt : FloatingPointFormat} {x : ℝ}
    (hcancel : fmt.problem2_24_y3 x = -x) :
    x * (2 * fmt.problem2_24_y2 x + x - 1) ≤ 0 := by
  have hmin :=
    fmt.problem2_24_y3_eq_neg_x_last_sub_minimal
      (x := x) (c := 0) hcancel fmt.finiteSystem_zero
  have hleft :
      (fmt.problem2_24_y2 x - (1 / 2 : ℝ)) - (-x) =
        fmt.problem2_24_y2 x + x - (1 / 2 : ℝ) := by
    ring
  have hright :
      (fmt.problem2_24_y2 x - (1 / 2 : ℝ)) - (0 : ℝ) =
        fmt.problem2_24_y2 x - (1 / 2 : ℝ) := by
    ring
  rw [hleft, hright] at hmin
  have hsquares :
      (fmt.problem2_24_y2 x + x - (1 / 2 : ℝ)) ^ 2 ≤
        (fmt.problem2_24_y2 x - (1 / 2 : ℝ)) ^ 2 := by
    exact sq_le_sq.mpr hmin
  nlinarith

/-- Exact final cancellation makes `-x` at least as close to the exact
third-step input as the finite candidate `-1/2` is.  Algebraically this gives
a lower-side product constraint for the lower-half zero branch. -/
theorem problem2_24_y3_eq_neg_x_last_sub_distance_to_neg_half_product_nonneg
    {fmt : FloatingPointFormat} {x : ℝ}
    (hhalf : fmt.finiteSystem (1 / 2 : ℝ))
    (hcancel : fmt.problem2_24_y3 x = -x) :
    0 ≤ ((1 / 2 : ℝ) - x) *
        (2 * fmt.problem2_24_y2 x + x - (1 / 2 : ℝ)) := by
  have hneg_half : fmt.finiteSystem (-(1 / 2 : ℝ)) :=
    fmt.finiteSystem_neg hhalf
  have hmin :=
    fmt.problem2_24_y3_eq_neg_x_last_sub_minimal
      (x := x) (c := -(1 / 2 : ℝ)) hcancel hneg_half
  have hleft :
      (fmt.problem2_24_y2 x - (1 / 2 : ℝ)) - (-x) =
        fmt.problem2_24_y2 x + x - (1 / 2 : ℝ) := by
    ring
  have hright :
      (fmt.problem2_24_y2 x - (1 / 2 : ℝ)) - (-(1 / 2 : ℝ)) =
        fmt.problem2_24_y2 x := by
    ring
  rw [hleft, hright] at hmin
  have hsquares :
      (fmt.problem2_24_y2 x + x - (1 / 2 : ℝ)) ^ 2 ≤
        (fmt.problem2_24_y2 x) ^ 2 := by
    exact sq_le_sq.mpr hmin
  nlinarith

/-- Exact final cancellation makes `-x` at least as close to the exact
third-step input as the finite candidate `y1` is. -/
theorem problem2_24_y3_eq_neg_x_last_sub_distance_to_y1_product_nonneg
    {fmt : FloatingPointFormat} {x : ℝ}
    (hcancel : fmt.problem2_24_y3 x = -x) :
    0 ≤ (fmt.problem2_24_y1 x + x) *
        (1 + fmt.problem2_24_y1 x - x - 2 * fmt.problem2_24_y2 x) := by
  have hmin :=
    fmt.problem2_24_y3_eq_neg_x_last_sub_minimal
      (x := x) (c := fmt.problem2_24_y1 x) hcancel
      (fmt.problem2_24_y1_finiteSystem x)
  have hleft :
      (fmt.problem2_24_y2 x - (1 / 2 : ℝ)) - (-x) =
        fmt.problem2_24_y2 x + x - (1 / 2 : ℝ) := by
    ring
  have hright :
      (fmt.problem2_24_y2 x - (1 / 2 : ℝ)) -
          fmt.problem2_24_y1 x =
        fmt.problem2_24_y2 x - (1 / 2 : ℝ) -
          fmt.problem2_24_y1 x := by
    ring
  rw [hleft, hright] at hmin
  have hsquares :
      (fmt.problem2_24_y2 x + x - (1 / 2 : ℝ)) ^ 2 ≤
        (fmt.problem2_24_y2 x - (1 / 2 : ℝ) -
          fmt.problem2_24_y1 x) ^ 2 := by
    exact sq_le_sq.mpr hmin
  nlinarith

/-- Exact final cancellation makes `-x` at least as close to the exact
third-step input as any finite negative constant candidate `-a` is. -/
theorem problem2_24_y3_eq_neg_x_last_sub_distance_to_neg_const_product_le
    {fmt : FloatingPointFormat} {x a : ℝ}
    (ha : fmt.finiteSystem (-a))
    (hcancel : fmt.problem2_24_y3 x = -x) :
    (x - a) * (2 * fmt.problem2_24_y2 x + x + a - 1) ≤ 0 := by
  have hmin :=
    fmt.problem2_24_y3_eq_neg_x_last_sub_minimal
      (x := x) (c := -a) hcancel ha
  have hleft :
      (fmt.problem2_24_y2 x - (1 / 2 : ℝ)) - (-x) =
        fmt.problem2_24_y2 x + x - (1 / 2 : ℝ) := by
    ring
  have hright :
      (fmt.problem2_24_y2 x - (1 / 2 : ℝ)) - (-a) =
        fmt.problem2_24_y2 x + a - (1 / 2 : ℝ) := by
    ring
  rw [hleft, hright] at hmin
  have hsquares :
      (fmt.problem2_24_y2 x + x - (1 / 2 : ℝ)) ^ 2 ≤
        (fmt.problem2_24_y2 x + a - (1 / 2 : ℝ)) ^ 2 := by
    exact sq_le_sq.mpr hmin
  nlinarith

/-- On the positive lower branch, the third-step comparison with `y1` gives
`2*y2 - y1 + x <= 1`. -/
theorem problem2_24_y3_eq_neg_x_last_sub_y2_y1_bound_of_y1_add_x_pos
    {fmt : FloatingPointFormat} {x : ℝ}
    (hcancel : fmt.problem2_24_y3 x = -x)
    (hpos : 0 < fmt.problem2_24_y1 x + x) :
    2 * fmt.problem2_24_y2 x - fmt.problem2_24_y1 x + x ≤ 1 := by
  have hprod :=
    fmt.problem2_24_y3_eq_neg_x_last_sub_distance_to_y1_product_nonneg
      hcancel
  have hfactor_nonneg :
      0 ≤ 1 + fmt.problem2_24_y1 x - x -
        2 * fmt.problem2_24_y2 x := by
    by_contra hfactor
    have hfactor_neg :
        1 + fmt.problem2_24_y1 x - x -
          2 * fmt.problem2_24_y2 x < 0 :=
      lt_of_not_ge hfactor
    have hmul_neg :
        (fmt.problem2_24_y1 x + x) *
            (1 + fmt.problem2_24_y1 x - x -
              2 * fmt.problem2_24_y2 x) < 0 :=
      mul_neg_of_pos_of_neg hpos hfactor_neg
    linarith
  linarith

/-- If exact final cancellation happened at a positive input, the second
rounded intermediate must satisfy the one-sided third-step bound
`2*y2 + x <= 1`. -/
theorem problem2_24_y3_eq_neg_x_last_sub_y2_bound_of_pos
    {fmt : FloatingPointFormat} {x : ℝ}
    (hcancel : fmt.problem2_24_y3 x = -x)
    (hxpos : 0 < x) :
    2 * fmt.problem2_24_y2 x + x ≤ 1 := by
  have hprod :=
    fmt.problem2_24_y3_eq_neg_x_last_sub_distance_to_zero_product_le hcancel
  nlinarith

/-- In the lower half, exact final cancellation forces the second rounded
intermediate to sit above the `-1/2` candidate threshold. -/
theorem problem2_24_y3_eq_neg_x_last_sub_y2_lower_bound_of_lt_half
    {fmt : FloatingPointFormat} {x : ℝ}
    (hhalf : fmt.finiteSystem (1 / 2 : ℝ))
    (hcancel : fmt.problem2_24_y3 x = -x)
    (hxlt : x < (1 / 2 : ℝ)) :
    (1 / 2 : ℝ) ≤ 2 * fmt.problem2_24_y2 x + x := by
  have hprod :=
    fmt.problem2_24_y3_eq_neg_x_last_sub_distance_to_neg_half_product_nonneg
      hhalf hcancel
  nlinarith

/-- A finite-input zero result makes `-x` at least as close to the exact
third-step input `y2 - 1/2` as every finite candidate. -/
theorem problem2_24_eval_eq_zero_last_sub_minimal_of_finiteSystem_input
    {fmt : FloatingPointFormat} {x c : ℝ}
    (hsub : fmt.subnormalMantissa 1)
    (hx : fmt.finiteSystem x)
    (hzero : fmt.problem2_24_eval x = 0)
    (hc : fmt.finiteSystem c) :
    |(fmt.problem2_24_y2 x - (1 / 2 : ℝ)) - (-x)| ≤
      |(fmt.problem2_24_y2 x - (1 / 2 : ℝ)) - c| := by
  have hcancel :
      fmt.problem2_24_y3 x = -x :=
    fmt.problem2_24_y3_eq_neg_x_of_eval_eq_zero_of_finiteSystem_input
      hsub hx hzero
  exact
    fmt.problem2_24_y3_eq_neg_x_last_sub_minimal hcancel hc

/-- A finite-input zero result forces the exact third-step input to be within
`1/2` of `-x`, by comparing against the finite candidate `y2`. -/
theorem problem2_24_eval_eq_zero_last_sub_distance_to_y2_le_half_of_finiteSystem_input
    {fmt : FloatingPointFormat} {x : ℝ}
    (hsub : fmt.subnormalMantissa 1)
    (hx : fmt.finiteSystem x)
    (hzero : fmt.problem2_24_eval x = 0) :
    |fmt.problem2_24_y2 x + x - (1 / 2 : ℝ)| ≤ (1 / 2 : ℝ) := by
  have hcancel :
      fmt.problem2_24_y3 x = -x :=
    fmt.problem2_24_y3_eq_neg_x_of_eval_eq_zero_of_finiteSystem_input
      hsub hx hzero
  exact
    fmt.problem2_24_y3_eq_neg_x_last_sub_distance_to_y2_le_half hcancel

/-- A finite-input zero result satisfies the third-step product constraint
obtained by comparing the exact-cancellation candidate `-x` with zero. -/
theorem problem2_24_eval_eq_zero_last_sub_distance_to_zero_product_le_of_finiteSystem_input
    {fmt : FloatingPointFormat} {x : ℝ}
    (hsub : fmt.subnormalMantissa 1)
    (hx : fmt.finiteSystem x)
    (hzero : fmt.problem2_24_eval x = 0) :
    x * (2 * fmt.problem2_24_y2 x + x - 1) ≤ 0 := by
  have hcancel :
      fmt.problem2_24_y3 x = -x :=
    fmt.problem2_24_y3_eq_neg_x_of_eval_eq_zero_of_finiteSystem_input
      hsub hx hzero
  exact
    fmt.problem2_24_y3_eq_neg_x_last_sub_distance_to_zero_product_le hcancel

/-- At a positive finite input, a zero result satisfies the one-sided
third-step bound `2*y2 + x <= 1`. -/
theorem problem2_24_eval_eq_zero_last_sub_y2_bound_of_pos_finiteSystem_input
    {fmt : FloatingPointFormat} {x : ℝ}
    (hsub : fmt.subnormalMantissa 1)
    (hx : fmt.finiteSystem x)
    (hzero : fmt.problem2_24_eval x = 0)
    (hxpos : 0 < x) :
    2 * fmt.problem2_24_y2 x + x ≤ 1 := by
  have hcancel :
      fmt.problem2_24_y3 x = -x :=
    fmt.problem2_24_y3_eq_neg_x_of_eval_eq_zero_of_finiteSystem_input
      hsub hx hzero
  exact
    fmt.problem2_24_y3_eq_neg_x_last_sub_y2_bound_of_pos hcancel hxpos

/-- In the lower half, a finite-input zero result forces
`1/2 <= 2*y2+x`. -/
theorem problem2_24_eval_eq_zero_last_sub_y2_lower_bound_of_lt_half_finiteSystem_input
    {fmt : FloatingPointFormat} {x : ℝ}
    (hsub : fmt.subnormalMantissa 1)
    (hhalf : fmt.finiteSystem (1 / 2 : ℝ))
    (hx : fmt.finiteSystem x)
    (hzero : fmt.problem2_24_eval x = 0)
    (hxlt : x < (1 / 2 : ℝ)) :
    (1 / 2 : ℝ) ≤ 2 * fmt.problem2_24_y2 x + x := by
  have hcancel :
      fmt.problem2_24_y3 x = -x :=
    fmt.problem2_24_y3_eq_neg_x_of_eval_eq_zero_of_finiteSystem_input
      hsub hx hzero
  exact
    fmt.problem2_24_y3_eq_neg_x_last_sub_y2_lower_bound_of_lt_half
      hhalf hcancel hxlt

/-- In the lower half, a finite-input zero result must have positive `y2`. -/
theorem problem2_24_eval_eq_zero_y2_pos_of_lt_half_finiteSystem_input
    {fmt : FloatingPointFormat} {x : ℝ}
    (hsub : fmt.subnormalMantissa 1)
    (hhalf : fmt.finiteSystem (1 / 2 : ℝ))
    (hx : fmt.finiteSystem x)
    (hzero : fmt.problem2_24_eval x = 0)
    (hxlt : x < (1 / 2 : ℝ)) :
    0 < fmt.problem2_24_y2 x := by
  have hylower :=
    fmt.problem2_24_eval_eq_zero_last_sub_y2_lower_bound_of_lt_half_finiteSystem_input
      hsub hhalf hx hzero hxlt
  nlinarith

/-- In the lower half, a finite-input zero result must have positive exact
second-step input `y1+x`. -/
theorem problem2_24_eval_eq_zero_y1_add_x_pos_of_lt_half_finiteSystem_input
    {fmt : FloatingPointFormat} {x : ℝ}
    (hsub : fmt.subnormalMantissa 1)
    (hhalf : fmt.finiteSystem (1 / 2 : ℝ))
    (hx : fmt.finiteSystem x)
    (hzero : fmt.problem2_24_eval x = 0)
    (hxlt : x < (1 / 2 : ℝ)) :
    0 < fmt.problem2_24_y1 x + x := by
  have hy2pos :=
    fmt.problem2_24_eval_eq_zero_y2_pos_of_lt_half_finiteSystem_input
      hsub hhalf hx hzero hxlt
  by_contra hspos
  have hsnonpos : fmt.problem2_24_y1 x + x ≤ 0 := le_of_not_gt hspos
  have hy2nonpos : fmt.problem2_24_y2 x ≤ 0 :=
    fmt.problem2_24_y2_nonpos_of_y1_add_x_nonpos hsnonpos
  nlinarith

/-- In the lower half, a finite-input zero result satisfies the third-step
comparison-with-`y1` bound `2*y2 - y1 + x <= 1`. -/
theorem problem2_24_eval_eq_zero_last_sub_y2_y1_bound_of_lt_half_finiteSystem_input
    {fmt : FloatingPointFormat} {x : ℝ}
    (hsub : fmt.subnormalMantissa 1)
    (hhalf : fmt.finiteSystem (1 / 2 : ℝ))
    (hx : fmt.finiteSystem x)
    (hzero : fmt.problem2_24_eval x = 0)
    (hxlt : x < (1 / 2 : ℝ)) :
    2 * fmt.problem2_24_y2 x - fmt.problem2_24_y1 x + x ≤ 1 := by
  have hcancel :
      fmt.problem2_24_y3 x = -x :=
    fmt.problem2_24_y3_eq_neg_x_of_eval_eq_zero_of_finiteSystem_input
      hsub hx hzero
  have hpos :=
    fmt.problem2_24_eval_eq_zero_y1_add_x_pos_of_lt_half_finiteSystem_input
      hsub hhalf hx hzero hxlt
  exact
    fmt.problem2_24_y3_eq_neg_x_last_sub_y2_y1_bound_of_y1_add_x_pos
      hcancel hpos

/-- A finite-input zero result satisfies the third-step comparison against any
finite negative constant candidate `-a`. -/
theorem problem2_24_eval_eq_zero_last_sub_distance_to_neg_const_product_le_of_finiteSystem_input
    {fmt : FloatingPointFormat} {x a : ℝ}
    (hsub : fmt.subnormalMantissa 1)
    (hx : fmt.finiteSystem x)
    (hzero : fmt.problem2_24_eval x = 0)
    (ha : fmt.finiteSystem (-a)) :
    (x - a) * (2 * fmt.problem2_24_y2 x + x + a - 1) ≤ 0 := by
  have hcancel :
      fmt.problem2_24_y3 x = -x :=
    fmt.problem2_24_y3_eq_neg_x_of_eval_eq_zero_of_finiteSystem_input
      hsub hx hzero
  exact
    fmt.problem2_24_y3_eq_neg_x_last_sub_distance_to_neg_const_product_le
      ha hcancel

/-- A finite-input zero result forces `y2 + x` into the unit interval. -/
theorem problem2_24_eval_eq_zero_y2_add_x_between_zero_and_one_of_finiteSystem_input
    {fmt : FloatingPointFormat} {x : ℝ}
    (hsub : fmt.subnormalMantissa 1)
    (hx : fmt.finiteSystem x)
    (hzero : fmt.problem2_24_eval x = 0) :
    0 ≤ fmt.problem2_24_y2 x + x ∧
      fmt.problem2_24_y2 x + x ≤ 1 := by
  have hdist :=
    fmt.problem2_24_eval_eq_zero_last_sub_distance_to_y2_le_half_of_finiteSystem_input
      hsub hx hzero
  rcases abs_le.mp hdist with ⟨hlo, hhi⟩
  constructor <;> linarith

/-- A finite-system zero counterexample to Problem 2.24 must have nonnegative
input. -/
theorem problem2_24_eval_eq_zero_input_nonneg_of_finiteSystem_input
    {fmt : FloatingPointFormat} {x : ℝ}
    (hsub : fmt.subnormalMantissa 1)
    (hx : fmt.finiteSystem x)
    (hzero : fmt.problem2_24_eval x = 0) :
    0 ≤ x := by
  have hy1_le_x :
      fmt.problem2_24_y1 x ≤ x :=
    (fmt.problem2_24_y1_between_x_sub_one_and_x_of_finiteSystem_input hx).2
  have hy2x_nonneg :
      0 ≤ fmt.problem2_24_y2 x + x :=
    (fmt.problem2_24_eval_eq_zero_y2_add_x_between_zero_and_one_of_finiteSystem_input
      hsub hx hzero).1
  have hmin0 :
      |(fmt.problem2_24_y1 x + x) - fmt.problem2_24_y2 x| ≤
        |fmt.problem2_24_y1 x + x| :=
    fmt.problem2_24_y2_second_add_distance_to_zero_le_self
  by_contra hx_nonneg
  have hx_neg : x < 0 := lt_of_not_ge hx_nonneg
  have hy1x_neg : fmt.problem2_24_y1 x + x < 0 := by
    linarith
  have hy2_pos : 0 < fmt.problem2_24_y2 x := by
    linarith
  have hleft_neg :
      (fmt.problem2_24_y1 x + x) - fmt.problem2_24_y2 x < 0 := by
    linarith
  rw [abs_of_neg hleft_neg, abs_of_neg hy1x_neg] at hmin0
  linarith

/-- A finite-system zero counterexample to Problem 2.24 must have input at most
one. -/
theorem problem2_24_eval_eq_zero_input_le_one_of_finiteSystem_input
    {fmt : FloatingPointFormat} {x : ℝ}
    (hsub : fmt.subnormalMantissa 1)
    (hx : fmt.finiteSystem x)
    (hzero : fmt.problem2_24_eval x = 0) :
    x ≤ 1 := by
  have hx_sub_one_le_y1 :
      x - 1 ≤ fmt.problem2_24_y1 x :=
    (fmt.problem2_24_y1_between_x_sub_one_and_x_of_finiteSystem_input hx).1
  have hy2x_le_one :
      fmt.problem2_24_y2 x + x ≤ 1 :=
    (fmt.problem2_24_eval_eq_zero_y2_add_x_between_zero_and_one_of_finiteSystem_input
      hsub hx hzero).2
  have hminy1 :
      |(fmt.problem2_24_y1 x + x) - fmt.problem2_24_y2 x| ≤ |x| :=
    fmt.problem2_24_y2_second_add_distance_to_y1_le_abs_x
  by_contra hx_le
  have hx_gt_one : 1 < x := lt_of_not_ge hx_le
  have hx_pos : 0 < x := by
    linarith
  have hexpr_gt_x :
      x < (fmt.problem2_24_y1 x + x) - fmt.problem2_24_y2 x := by
    linarith
  have hexpr_pos :
      0 < (fmt.problem2_24_y1 x + x) - fmt.problem2_24_y2 x := by
    linarith
  rw [abs_of_pos hexpr_pos, abs_of_pos hx_pos] at hminy1
  linarith

/-- A finite-system zero counterexample to Problem 2.24 must lie in the unit
interval. -/
theorem problem2_24_eval_eq_zero_input_mem_unit_interval_of_finiteSystem_input
    {fmt : FloatingPointFormat} {x : ℝ}
    (hsub : fmt.subnormalMantissa 1)
    (hx : fmt.finiteSystem x)
    (hzero : fmt.problem2_24_eval x = 0) :
    0 ≤ x ∧ x ≤ 1 :=
  ⟨fmt.problem2_24_eval_eq_zero_input_nonneg_of_finiteSystem_input
      hsub hx hzero,
    fmt.problem2_24_eval_eq_zero_input_le_one_of_finiteSystem_input
      hsub hx hzero⟩

/-- No finite-system zero counterexample can lie in the upper half of the unit
interval.  The candidate-`x` second-step product constraint conflicts with the
third-step positive-input bound once `x >= 1/2`. -/
theorem problem2_24_eval_ne_zero_of_finiteSystem_input_of_half_le
    {fmt : FloatingPointFormat} {x : ℝ}
    (hsub : fmt.subnormalMantissa 1)
    (hx : fmt.finiteSystem x)
    (hxhalf : (1 / 2 : ℝ) ≤ x) :
    fmt.problem2_24_eval x ≠ 0 := by
  intro hzero
  have hxpos : 0 < x := by
    linarith
  have hy2_bound : 2 * fmt.problem2_24_y2 x + x ≤ 1 :=
    fmt.problem2_24_eval_eq_zero_last_sub_y2_bound_of_pos_finiteSystem_input
      hsub hx hzero hxpos
  have hy2_le : fmt.problem2_24_y2 x ≤ (1 - x) / 2 := by
    linarith
  have hy1_nonneg : 0 ≤ fmt.problem2_24_y1 x :=
    fmt.problem2_24_y1_nonneg_of_half_le hxhalf
  have hprod :=
    fmt.problem2_24_y2_second_add_distance_to_x_product_le_of_finiteSystem_input
      hx
  have hfirst_pos : 0 < x - fmt.problem2_24_y2 x := by
    nlinarith
  have hsecond_pos :
      0 < 2 * fmt.problem2_24_y1 x + x - fmt.problem2_24_y2 x := by
    nlinarith
  nlinarith

/-- If `1/2` and `1` are finite-system values, the modeled Problem 2.24 path at
`x = 0` evaluates to `-1`, hence not to zero. -/
theorem problem2_24_eval_zero_ne_zero_of_half_and_one_finiteSystem
    {fmt : FloatingPointFormat}
    (hhalf : fmt.finiteSystem (1 / 2 : ℝ))
    (hone : fmt.finiteSystem (1 : ℝ)) :
    fmt.problem2_24_eval 0 ≠ 0 := by
  have hneg_half : fmt.finiteSystem (-(1 / 2 : ℝ)) :=
    fmt.finiteSystem_neg hhalf
  have hneg_one : fmt.finiteSystem (-(1 : ℝ)) :=
    fmt.finiteSystem_neg hone
  have h1 : fmt.finiteSystem ((0 : ℝ) - (1 / 2 : ℝ)) := by
    simpa using hneg_half
  have h2 : fmt.finiteSystem (((0 : ℝ) - (1 / 2 : ℝ)) + (0 : ℝ)) := by
    simpa using hneg_half
  have h3 :
      fmt.finiteSystem ((((0 : ℝ) - (1 / 2 : ℝ)) + (0 : ℝ)) - (1 / 2 : ℝ)) := by
    convert hneg_one using 1
    norm_num
  have h4 :
      fmt.finiteSystem
        (((((0 : ℝ) - (1 / 2 : ℝ)) + (0 : ℝ)) - (1 / 2 : ℝ)) + (0 : ℝ)) := by
    convert hneg_one using 1
    norm_num
  have heval :=
    fmt.problem2_24_eval_eq_three_mul_sub_one_of_finiteSystem_intermediates
      (x := (0 : ℝ)) h1 h2 h3 h4
  intro hzero
  norm_num at heval
  rw [heval] at hzero
  norm_num at hzero

/-- Once `x = 0` is excluded, every finite-system zero counterexample has
strictly positive input. -/
theorem problem2_24_eval_eq_zero_input_pos_of_finiteSystem_input
    {fmt : FloatingPointFormat} {x : ℝ}
    (hsub : fmt.subnormalMantissa 1)
    (hhalf : fmt.finiteSystem (1 / 2 : ℝ))
    (hone : fmt.finiteSystem (1 : ℝ))
    (hx : fmt.finiteSystem x)
    (hzero : fmt.problem2_24_eval x = 0) :
    0 < x := by
  have hx_nonneg : 0 ≤ x :=
    fmt.problem2_24_eval_eq_zero_input_nonneg_of_finiteSystem_input
      hsub hx hzero
  by_cases hxzero : x = 0
  · subst x
    exact False.elim
      ((fmt.problem2_24_eval_zero_ne_zero_of_half_and_one_finiteSystem
        hhalf hone) hzero)
  · exact lt_of_le_of_ne hx_nonneg (Ne.symm hxzero)

/-- The remaining modeled finite-system zero-counterexample branch, if any,
must lie strictly in the lower half of the unit interval. -/
theorem problem2_24_eval_eq_zero_input_mem_open_lower_half_of_finiteSystem_input
    {fmt : FloatingPointFormat} {x : ℝ}
    (hsub : fmt.subnormalMantissa 1)
    (hhalf : fmt.finiteSystem (1 / 2 : ℝ))
    (hone : fmt.finiteSystem (1 : ℝ))
    (hx : fmt.finiteSystem x)
    (hzero : fmt.problem2_24_eval x = 0) :
    0 < x ∧ x < (1 / 2 : ℝ) := by
  refine ⟨?_, ?_⟩
  · exact
      fmt.problem2_24_eval_eq_zero_input_pos_of_finiteSystem_input
        hsub hhalf hone hx hzero
  · by_contra hlt
    have hxhalf : (1 / 2 : ℝ) ≤ x := le_of_not_gt hlt
    exact
      (fmt.problem2_24_eval_ne_zero_of_finiteSystem_input_of_half_le
        hsub hx hxhalf) hzero

/-- The remaining modeled finite-system zero-counterexample branch, if any,
lies in `[1/10, 1/2)`. -/
theorem problem2_24_eval_eq_zero_input_mem_tenth_to_half_of_finiteSystem_input
    {fmt : FloatingPointFormat} {x : ℝ}
    (hsub : fmt.subnormalMantissa 1)
    (hhalf : fmt.finiteSystem (1 / 2 : ℝ))
    (hone : fmt.finiteSystem (1 : ℝ))
    (hx : fmt.finiteSystem x)
    (hzero : fmt.problem2_24_eval x = 0) :
    (1 / 10 : ℝ) ≤ x ∧ x < (1 / 2 : ℝ) := by
  have hxlt :
      x < (1 / 2 : ℝ) :=
    (fmt.problem2_24_eval_eq_zero_input_mem_open_lower_half_of_finiteSystem_input
      hsub hhalf hone hx hzero).2
  have hylower :=
    fmt.problem2_24_eval_eq_zero_last_sub_y2_lower_bound_of_lt_half_finiteSystem_input
      hsub hhalf hx hzero hxlt
  have hspos :=
    fmt.problem2_24_eval_eq_zero_y1_add_x_pos_of_lt_half_finiteSystem_input
      hsub hhalf hx hzero hxlt
  have hy2_le :
      fmt.problem2_24_y2 x ≤ 2 * (fmt.problem2_24_y1 x + x) :=
    fmt.problem2_24_y2_le_two_mul_y1_add_x_of_y1_add_x_nonneg
      (le_of_lt hspos)
  have hy1_nonpos : fmt.problem2_24_y1 x ≤ 0 :=
    fmt.problem2_24_y1_nonpos_of_le_half (le_of_lt hxlt)
  constructor
  · nlinarith
  · exact hxlt

/-- No finite-system zero counterexample can lie below `1/6`.  Below `1/6`,
the `-1/2` third-step comparison forces `y2 > x`, while the second-step
candidate-`x` product and `y1 <= 0` force `y2 <= x`. -/
theorem problem2_24_eval_ne_zero_of_finiteSystem_input_of_lt_one_six
    {fmt : FloatingPointFormat} {x : ℝ}
    (hsub : fmt.subnormalMantissa 1)
    (hhalf : fmt.finiteSystem (1 / 2 : ℝ))
    (hx : fmt.finiteSystem x)
    (hxlt : x < (1 / 6 : ℝ)) :
    fmt.problem2_24_eval x ≠ 0 := by
  intro hzero
  have hxlt_half : x < (1 / 2 : ℝ) := by
    nlinarith
  have hylower :=
    fmt.problem2_24_eval_eq_zero_last_sub_y2_lower_bound_of_lt_half_finiteSystem_input
      hsub hhalf hx hzero hxlt_half
  have hy2_gt_x : x < fmt.problem2_24_y2 x := by
    nlinarith
  have hprod :=
    fmt.problem2_24_y2_second_add_distance_to_x_product_le_of_finiteSystem_input
      hx
  have hy1_nonpos : fmt.problem2_24_y1 x ≤ 0 :=
    fmt.problem2_24_y1_nonpos_of_le_half (by nlinarith : x ≤ (1 / 2 : ℝ))
  by_cases hsecond_nonneg :
      0 ≤ 2 * fmt.problem2_24_y1 x + x - fmt.problem2_24_y2 x
  · nlinarith
  · have hsecond_neg :
        2 * fmt.problem2_24_y1 x + x - fmt.problem2_24_y2 x < 0 :=
      lt_of_not_ge hsecond_nonneg
    have hfirst_neg : x - fmt.problem2_24_y2 x < 0 := by
      nlinarith
    nlinarith

/-- Every finite-system zero counterexample must have input at least `1/6`. -/
theorem problem2_24_eval_eq_zero_input_ge_one_six_of_finiteSystem_input
    {fmt : FloatingPointFormat} {x : ℝ}
    (hsub : fmt.subnormalMantissa 1)
    (hhalf : fmt.finiteSystem (1 / 2 : ℝ))
    (hx : fmt.finiteSystem x)
    (hzero : fmt.problem2_24_eval x = 0) :
    (1 / 6 : ℝ) ≤ x := by
  by_contra hge
  have hxlt : x < (1 / 6 : ℝ) := lt_of_not_ge hge
  exact
    (fmt.problem2_24_eval_ne_zero_of_finiteSystem_input_of_lt_one_six
      hsub hhalf hx hxlt) hzero

/-- The remaining modeled finite-system zero-counterexample branch, if any,
lies in `[1/6, 1/2)`. -/
theorem problem2_24_eval_eq_zero_input_mem_one_six_to_half_of_finiteSystem_input
    {fmt : FloatingPointFormat} {x : ℝ}
    (hsub : fmt.subnormalMantissa 1)
    (hhalf : fmt.finiteSystem (1 / 2 : ℝ))
    (hone : fmt.finiteSystem (1 : ℝ))
    (hx : fmt.finiteSystem x)
    (hzero : fmt.problem2_24_eval x = 0) :
    (1 / 6 : ℝ) ≤ x ∧ x < (1 / 2 : ℝ) :=
  ⟨fmt.problem2_24_eval_eq_zero_input_ge_one_six_of_finiteSystem_input
      hsub hhalf hx hzero,
    (fmt.problem2_24_eval_eq_zero_input_mem_open_lower_half_of_finiteSystem_input
      hsub hhalf hone hx hzero).2⟩

/-- No finite-system zero counterexample can lie below `9/34`.  The first-step
comparison against `-x` gives `y1 <= 3*x-1` on the positive second-step branch;
combined with the second-step sign cell and the third-step `-1/2` lower bound,
this contradicts `x < 9/34`. -/
theorem problem2_24_eval_ne_zero_of_finiteSystem_input_of_lt_nine_thirty_four
    {fmt : FloatingPointFormat} {x : ℝ}
    (hsub : fmt.subnormalMantissa 1)
    (hhalf : fmt.finiteSystem (1 / 2 : ℝ))
    (hx : fmt.finiteSystem x)
    (hxlt : x < (9 / 34 : ℝ)) :
    fmt.problem2_24_eval x ≠ 0 := by
  intro hzero
  have hxlt_half : x < (1 / 2 : ℝ) := by
    nlinarith
  have hylower :=
    fmt.problem2_24_eval_eq_zero_last_sub_y2_lower_bound_of_lt_half_finiteSystem_input
      hsub hhalf hx hzero hxlt_half
  have hspos :=
    fmt.problem2_24_eval_eq_zero_y1_add_x_pos_of_lt_half_finiteSystem_input
      hsub hhalf hx hzero hxlt_half
  have hy2_le :
      fmt.problem2_24_y2 x ≤ 2 * (fmt.problem2_24_y1 x + x) :=
    fmt.problem2_24_y2_le_two_mul_y1_add_x_of_y1_add_x_nonneg
      (le_of_lt hspos)
  have hy1_le :
      fmt.problem2_24_y1 x ≤ 3 * x - 1 :=
    fmt.problem2_24_y1_le_three_mul_x_sub_one_of_y1_add_x_pos_finiteSystem_input
      hx hspos
  nlinarith

/-- Every finite-system zero counterexample must have input at least `9/34`. -/
theorem problem2_24_eval_eq_zero_input_ge_nine_thirty_four_of_finiteSystem_input
    {fmt : FloatingPointFormat} {x : ℝ}
    (hsub : fmt.subnormalMantissa 1)
    (hhalf : fmt.finiteSystem (1 / 2 : ℝ))
    (hx : fmt.finiteSystem x)
    (hzero : fmt.problem2_24_eval x = 0) :
    (9 / 34 : ℝ) ≤ x := by
  by_contra hge
  have hxlt : x < (9 / 34 : ℝ) := lt_of_not_ge hge
  exact
    (fmt.problem2_24_eval_ne_zero_of_finiteSystem_input_of_lt_nine_thirty_four
      hsub hhalf hx hxlt) hzero

/-- The remaining modeled finite-system zero-counterexample branch, if any,
lies in `[9/34, 1/2)`. -/
theorem problem2_24_eval_eq_zero_input_mem_nine_thirty_four_to_half_of_finiteSystem_input
    {fmt : FloatingPointFormat} {x : ℝ}
    (hsub : fmt.subnormalMantissa 1)
    (hhalf : fmt.finiteSystem (1 / 2 : ℝ))
    (hone : fmt.finiteSystem (1 : ℝ))
    (hx : fmt.finiteSystem x)
    (hzero : fmt.problem2_24_eval x = 0) :
    (9 / 34 : ℝ) ≤ x ∧ x < (1 / 2 : ℝ) :=
  ⟨fmt.problem2_24_eval_eq_zero_input_ge_nine_thirty_four_of_finiteSystem_input
      hsub hhalf hx hzero,
    (fmt.problem2_24_eval_eq_zero_input_mem_open_lower_half_of_finiteSystem_input
      hsub hhalf hone hx hzero).2⟩

/-- No finite-system zero counterexample can lie below `5/18`.  On the
remaining lower-half branch, the first subtraction is Sterbenz-exact, so
`y1 = x - 1/2`; the second-step sign cell and third-step lower bound then
force `x >= 5/18`. -/
theorem problem2_24_eval_ne_zero_of_finiteSystem_input_of_lt_five_eighteen
    {fmt : FloatingPointFormat} {x : ℝ}
    (hsub : fmt.subnormalMantissa 1)
    (hhalf : fmt.finiteSystem (1 / 2 : ℝ))
    (hx : fmt.finiteSystem x)
    (hxlt : x < (5 / 18 : ℝ)) :
    fmt.problem2_24_eval x ≠ 0 := by
  intro hzero
  have hxge_nine :
      (9 / 34 : ℝ) ≤ x :=
    fmt.problem2_24_eval_eq_zero_input_ge_nine_thirty_four_of_finiteSystem_input
      hsub hhalf hx hzero
  have hxlt_half : x < (1 / 2 : ℝ) := by
    nlinarith
  have hy1eq :
      fmt.problem2_24_y1 x = x - (1 / 2 : ℝ) :=
    fmt.problem2_24_y1_eq_x_sub_half_of_finiteSystem_input_of_quarter_lt_of_lt_one
      hhalf hx (by nlinarith : (1 / 4 : ℝ) < x)
      (by nlinarith : x < (1 : ℝ))
  have hylower :=
    fmt.problem2_24_eval_eq_zero_last_sub_y2_lower_bound_of_lt_half_finiteSystem_input
      hsub hhalf hx hzero hxlt_half
  have hspos :=
    fmt.problem2_24_eval_eq_zero_y1_add_x_pos_of_lt_half_finiteSystem_input
      hsub hhalf hx hzero hxlt_half
  have hy2_le :
      fmt.problem2_24_y2 x ≤ 2 * (fmt.problem2_24_y1 x + x) :=
    fmt.problem2_24_y2_le_two_mul_y1_add_x_of_y1_add_x_nonneg
      (le_of_lt hspos)
  rw [hy1eq] at hy2_le
  nlinarith

/-- Every finite-system zero counterexample must have input at least `5/18`. -/
theorem problem2_24_eval_eq_zero_input_ge_five_eighteen_of_finiteSystem_input
    {fmt : FloatingPointFormat} {x : ℝ}
    (hsub : fmt.subnormalMantissa 1)
    (hhalf : fmt.finiteSystem (1 / 2 : ℝ))
    (hx : fmt.finiteSystem x)
    (hzero : fmt.problem2_24_eval x = 0) :
    (5 / 18 : ℝ) ≤ x := by
  by_contra hge
  have hxlt : x < (5 / 18 : ℝ) := lt_of_not_ge hge
  exact
    (fmt.problem2_24_eval_ne_zero_of_finiteSystem_input_of_lt_five_eighteen
      hsub hhalf hx hxlt) hzero

/-- The remaining modeled finite-system zero-counterexample branch, if any,
lies in `[5/18, 1/2)`. -/
theorem problem2_24_eval_eq_zero_input_mem_five_eighteen_to_half_of_finiteSystem_input
    {fmt : FloatingPointFormat} {x : ℝ}
    (hsub : fmt.subnormalMantissa 1)
    (hhalf : fmt.finiteSystem (1 / 2 : ℝ))
    (hone : fmt.finiteSystem (1 : ℝ))
    (hx : fmt.finiteSystem x)
    (hzero : fmt.problem2_24_eval x = 0) :
    (5 / 18 : ℝ) ≤ x ∧ x < (1 / 2 : ℝ) :=
  ⟨fmt.problem2_24_eval_eq_zero_input_ge_five_eighteen_of_finiteSystem_input
      hsub hhalf hx hzero,
    (fmt.problem2_24_eval_eq_zero_input_mem_open_lower_half_of_finiteSystem_input
      hsub hhalf hone hx hzero).2⟩

/-- On any modeled finite zero branch, the second rounded intermediate is at
most `1/4`. -/
theorem problem2_24_eval_eq_zero_y2_le_quarter_of_finiteSystem_input
    {fmt : FloatingPointFormat} {x : ℝ}
    (hsub : fmt.subnormalMantissa 1)
    (hhalf : fmt.finiteSystem (1 / 2 : ℝ))
    (hx : fmt.finiteSystem x)
    (hzero : fmt.problem2_24_eval x = 0) :
    fmt.problem2_24_y2 x ≤ (1 / 4 : ℝ) := by
  have hxge_five :
      (5 / 18 : ℝ) ≤ x :=
    fmt.problem2_24_eval_eq_zero_input_ge_five_eighteen_of_finiteSystem_input
      hsub hhalf hx hzero
  have hxlt_half : x < (1 / 2 : ℝ) := by
    by_contra hlt
    have hxhalf : (1 / 2 : ℝ) ≤ x := le_of_not_gt hlt
    exact
      (fmt.problem2_24_eval_ne_zero_of_finiteSystem_input_of_half_le
        hsub hx hxhalf) hzero
  have hy1eq :
      fmt.problem2_24_y1 x = x - (1 / 2 : ℝ) :=
    fmt.problem2_24_y1_eq_x_sub_half_of_finiteSystem_input_of_quarter_lt_of_lt_one
      hhalf hx (by nlinarith : (1 / 4 : ℝ) < x)
      (by nlinarith : x < (1 : ℝ))
  have hbound :=
    fmt.problem2_24_eval_eq_zero_last_sub_y2_y1_bound_of_lt_half_finiteSystem_input
      hsub hhalf hx hzero hxlt_half
  rw [hy1eq] at hbound
  nlinarith

/-- No finite-system zero counterexample can lie above `5/12`. -/
theorem problem2_24_eval_ne_zero_of_finiteSystem_input_of_five_twelfths_lt
    {fmt : FloatingPointFormat} {x : ℝ}
    (hsub : fmt.subnormalMantissa 1)
    (hhalf : fmt.finiteSystem (1 / 2 : ℝ))
    (hx : fmt.finiteSystem x)
    (hxgt : (5 / 12 : ℝ) < x) :
    fmt.problem2_24_eval x ≠ 0 := by
  intro hzero
  by_cases hxhalf : (1 / 2 : ℝ) ≤ x
  · exact
      (fmt.problem2_24_eval_ne_zero_of_finiteSystem_input_of_half_le
        hsub hx hxhalf) hzero
  · have hxlt_half : x < (1 / 2 : ℝ) := lt_of_not_ge hxhalf
    have hy2_le :
        fmt.problem2_24_y2 x ≤ (1 / 4 : ℝ) :=
      fmt.problem2_24_eval_eq_zero_y2_le_quarter_of_finiteSystem_input
        hsub hhalf hx hzero
    have hy1eq :
        fmt.problem2_24_y1 x = x - (1 / 2 : ℝ) :=
      fmt.problem2_24_y1_eq_x_sub_half_of_finiteSystem_input_of_quarter_lt_of_lt_one
        hhalf hx (by nlinarith : (1 / 4 : ℝ) < x)
        (by nlinarith : x < (1 : ℝ))
    have hprod :=
      fmt.problem2_24_y2_second_add_distance_to_x_product_le_of_finiteSystem_input
        hx
    rw [hy1eq] at hprod
    have hfirst_pos : 0 < x - fmt.problem2_24_y2 x := by
      nlinarith
    have hsecond_pos :
        0 < 2 * (x - (1 / 2 : ℝ)) + x -
          fmt.problem2_24_y2 x := by
      nlinarith
    have hmul_pos :
        0 < (x - fmt.problem2_24_y2 x) *
          (2 * (x - (1 / 2 : ℝ)) + x -
            fmt.problem2_24_y2 x) :=
      mul_pos hfirst_pos hsecond_pos
    nlinarith

/-- Every finite-system zero counterexample must have input at most `5/12`. -/
theorem problem2_24_eval_eq_zero_input_le_five_twelfths_of_finiteSystem_input
    {fmt : FloatingPointFormat} {x : ℝ}
    (hsub : fmt.subnormalMantissa 1)
    (hhalf : fmt.finiteSystem (1 / 2 : ℝ))
    (hx : fmt.finiteSystem x)
    (hzero : fmt.problem2_24_eval x = 0) :
    x ≤ (5 / 12 : ℝ) := by
  by_contra hle
  have hxgt : (5 / 12 : ℝ) < x := lt_of_not_ge hle
  exact
    (fmt.problem2_24_eval_ne_zero_of_finiteSystem_input_of_five_twelfths_lt
      hsub hhalf hx hxgt) hzero

/-- The remaining modeled finite-system zero-counterexample branch, if any,
lies in `[5/18, 5/12]`. -/
theorem problem2_24_eval_eq_zero_input_mem_five_eighteen_to_five_twelfths_of_finiteSystem_input
    {fmt : FloatingPointFormat} {x : ℝ}
    (hsub : fmt.subnormalMantissa 1)
    (hhalf : fmt.finiteSystem (1 / 2 : ℝ))
    (hx : fmt.finiteSystem x)
    (hzero : fmt.problem2_24_eval x = 0) :
    (5 / 18 : ℝ) ≤ x ∧ x ≤ (5 / 12 : ℝ) :=
  ⟨fmt.problem2_24_eval_eq_zero_input_ge_five_eighteen_of_finiteSystem_input
      hsub hhalf hx hzero,
    fmt.problem2_24_eval_eq_zero_input_le_five_twelfths_of_finiteSystem_input
      hsub hhalf hx hzero⟩

/-- No finite-system zero counterexample can lie below `3/10`.  In the
sub-third branch, the second addition is Sterbenz-exact, so the third-step
lower bound forces `x >= 3/10`. -/
theorem problem2_24_eval_ne_zero_of_finiteSystem_input_of_lt_three_tenths
    {fmt : FloatingPointFormat} {x : ℝ}
    (hsub : fmt.subnormalMantissa 1)
    (hhalf : fmt.finiteSystem (1 / 2 : ℝ))
    (hx : fmt.finiteSystem x)
    (hxlt : x < (3 / 10 : ℝ)) :
    fmt.problem2_24_eval x ≠ 0 := by
  intro hzero
  have hxge_five :
      (5 / 18 : ℝ) ≤ x :=
    fmt.problem2_24_eval_eq_zero_input_ge_five_eighteen_of_finiteSystem_input
      hsub hhalf hx hzero
  have hxlt_half : x < (1 / 2 : ℝ) := by
    nlinarith
  have hxlt_third : x < (1 / 3 : ℝ) := by
    nlinarith
  have hy2eq :
      fmt.problem2_24_y2 x = 2 * x - (1 / 2 : ℝ) :=
    fmt.problem2_24_y2_eq_two_mul_x_sub_half_of_finiteSystem_input_of_quarter_lt_of_lt_one_third
      hhalf hx (by nlinarith : (1 / 4 : ℝ) < x) hxlt_third
  have hylower :=
    fmt.problem2_24_eval_eq_zero_last_sub_y2_lower_bound_of_lt_half_finiteSystem_input
      hsub hhalf hx hzero hxlt_half
  rw [hy2eq] at hylower
  nlinarith

/-- Every finite-system zero counterexample must have input at least `3/10`. -/
theorem problem2_24_eval_eq_zero_input_ge_three_tenths_of_finiteSystem_input
    {fmt : FloatingPointFormat} {x : ℝ}
    (hsub : fmt.subnormalMantissa 1)
    (hhalf : fmt.finiteSystem (1 / 2 : ℝ))
    (hx : fmt.finiteSystem x)
    (hzero : fmt.problem2_24_eval x = 0) :
    (3 / 10 : ℝ) ≤ x := by
  by_contra hge
  have hxlt : x < (3 / 10 : ℝ) := lt_of_not_ge hge
  exact
    (fmt.problem2_24_eval_ne_zero_of_finiteSystem_input_of_lt_three_tenths
      hsub hhalf hx hxlt) hzero

/-- The remaining modeled finite-system zero-counterexample branch, if any,
lies in `[3/10, 5/12]`. -/
theorem problem2_24_eval_eq_zero_input_mem_three_tenths_to_five_twelfths_of_finiteSystem_input
    {fmt : FloatingPointFormat} {x : ℝ}
    (hsub : fmt.subnormalMantissa 1)
    (hhalf : fmt.finiteSystem (1 / 2 : ℝ))
    (hx : fmt.finiteSystem x)
    (hzero : fmt.problem2_24_eval x = 0) :
    (3 / 10 : ℝ) ≤ x ∧ x ≤ (5 / 12 : ℝ) :=
  ⟨fmt.problem2_24_eval_eq_zero_input_ge_three_tenths_of_finiteSystem_input
      hsub hhalf hx hzero,
    fmt.problem2_24_eval_eq_zero_input_le_five_twelfths_of_finiteSystem_input
      hsub hhalf hx hzero⟩

/-- Every finite-system zero counterexample is in the Sterbenz-exact first
subtraction range, so its first exact real intermediate is finite-system
representable. -/
theorem problem2_24_eval_eq_zero_first_exact_intermediate_finiteSystem_of_finiteSystem_input
    {fmt : FloatingPointFormat} {x : ℝ}
    (hsub : fmt.subnormalMantissa 1)
    (hhalf : fmt.finiteSystem (1 / 2 : ℝ))
    (hx : fmt.finiteSystem x)
    (hzero : fmt.problem2_24_eval x = 0) :
    fmt.finiteSystem (x - (1 / 2 : ℝ)) := by
  have hmem :
      (3 / 10 : ℝ) ≤ x ∧ x ≤ (5 / 12 : ℝ) :=
    fmt.problem2_24_eval_eq_zero_input_mem_three_tenths_to_five_twelfths_of_finiteSystem_input
      hsub hhalf hx hzero
  exact
    fmt.problem2_24_first_exact_intermediate_finiteSystem_of_quarter_lt_of_lt_one
      hhalf hx (by nlinarith) (by nlinarith)

/-- Finite-system zero counterexamples away from `1/3` cannot leave the
exact-intermediate branch at the first subtraction; any nonfinite exact
intermediate must be one of the later three real intermediates. -/
theorem problem2_24_eval_eq_zero_implies_later_nonfinite_exact_intermediate_of_finiteSystem_input_of_ne_one_third
    {fmt : FloatingPointFormat} {x : ℝ}
    (hsub : fmt.subnormalMantissa 1)
    (hhalf : fmt.finiteSystem (1 / 2 : ℝ))
    (hx : fmt.finiteSystem x)
    (hxthird : x ≠ (1 / 3 : ℝ))
    (hzero : fmt.problem2_24_eval x = 0) :
    ¬ fmt.finiteSystem ((x - (1 / 2 : ℝ)) + x) ∨
      ¬ fmt.finiteSystem (((x - (1 / 2 : ℝ)) + x) - (1 / 2 : ℝ)) ∨
      ¬ fmt.finiteSystem
        ((((x - (1 / 2 : ℝ)) + x) - (1 / 2 : ℝ)) + x) := by
  have hfirst :
      fmt.finiteSystem (x - (1 / 2 : ℝ)) :=
    fmt.problem2_24_eval_eq_zero_first_exact_intermediate_finiteSystem_of_finiteSystem_input
      hsub hhalf hx hzero
  have hbranch :=
    fmt.problem2_24_eval_eq_zero_implies_exists_nonfinite_exact_intermediate_of_ne_one_third
      hxthird hzero
  rcases hbranch with hfirst_bad | hlater
  · exact False.elim (hfirst_bad hfirst)
  · exact hlater

/-- On any finite-system zero branch away from `1/3`, the second and third
exact real intermediates cannot both be finite-system representable.  If they
were both finite, the first subtraction is already exact on the narrowed zero
branch, the next two operations would also be exact, and final cancellation
would force `x = 1/3`. -/
theorem problem2_24_eval_ne_zero_of_finiteSystem_input_of_ne_one_third_of_second_third_exact_intermediates
    {fmt : FloatingPointFormat} {x : ℝ}
    (hsub : fmt.subnormalMantissa 1)
    (hhalf : fmt.finiteSystem (1 / 2 : ℝ))
    (hx : fmt.finiteSystem x)
    (hxthird : x ≠ (1 / 3 : ℝ))
    (hsecond : fmt.finiteSystem ((x - (1 / 2 : ℝ)) + x))
    (hthird : fmt.finiteSystem
      (((x - (1 / 2 : ℝ)) + x) - (1 / 2 : ℝ))) :
    fmt.problem2_24_eval x ≠ 0 := by
  intro hzero
  have hfirst :
      fmt.finiteSystem (x - (1 / 2 : ℝ)) :=
    fmt.problem2_24_eval_eq_zero_first_exact_intermediate_finiteSystem_of_finiteSystem_input
      hsub hhalf hx hzero
  have hy1exact :
      fmt.problem2_24_y1 x = x - (1 / 2 : ℝ) := by
    simpa [problem2_24_y1, BasicOp.exact] using
      (fmt.finiteRoundToEvenOp_eq_exact_of_finiteSystem
        (op := BasicOp.sub) (x := x) (y := (1 / 2 : ℝ)) hfirst)
  have hsecond_y1 :
      fmt.finiteSystem (fmt.problem2_24_y1 x + x) := by
    convert hsecond using 1
    rw [hy1exact]
  have hy2exact :
      fmt.problem2_24_y2 x = fmt.problem2_24_y1 x + x := by
    simpa [problem2_24_y2, BasicOp.exact] using
      (fmt.finiteRoundToEvenOp_eq_exact_of_finiteSystem
        (op := BasicOp.add) (x := fmt.problem2_24_y1 x) (y := x)
        hsecond_y1)
  have hy2poly :
      fmt.problem2_24_y2 x = 2 * x - (1 / 2 : ℝ) := by
    rw [hy2exact, hy1exact]
    ring
  have hthird_y2 :
      fmt.finiteSystem (fmt.problem2_24_y2 x - (1 / 2 : ℝ)) := by
    convert hthird using 1
    rw [hy2poly]
    ring
  have hy3exact :
      fmt.problem2_24_y3 x = fmt.problem2_24_y2 x - (1 / 2 : ℝ) := by
    simpa [problem2_24_y3, BasicOp.exact] using
      (fmt.finiteRoundToEvenOp_eq_exact_of_finiteSystem
        (op := BasicOp.sub) (x := fmt.problem2_24_y2 x)
        (y := (1 / 2 : ℝ)) hthird_y2)
  have hy3poly :
      fmt.problem2_24_y3 x = 2 * x - 1 := by
    rw [hy3exact, hy2poly]
    ring
  have hcancel :
      fmt.problem2_24_y3 x = -x :=
    fmt.problem2_24_y3_eq_neg_x_of_eval_eq_zero_of_finiteSystem_input
      hsub hx hzero
  exact hxthird (by nlinarith)

/-- Finite-system zero branches away from `1/3` must leave the
exact-intermediate branch at the second or third exact real intermediate. -/
theorem problem2_24_eval_eq_zero_implies_second_or_third_nonfinite_exact_intermediate_of_finiteSystem_input_of_ne_one_third
    {fmt : FloatingPointFormat} {x : ℝ}
    (hsub : fmt.subnormalMantissa 1)
    (hhalf : fmt.finiteSystem (1 / 2 : ℝ))
    (hx : fmt.finiteSystem x)
    (hxthird : x ≠ (1 / 3 : ℝ))
    (hzero : fmt.problem2_24_eval x = 0) :
    ¬ fmt.finiteSystem ((x - (1 / 2 : ℝ)) + x) ∨
      ¬ fmt.finiteSystem (((x - (1 / 2 : ℝ)) + x) - (1 / 2 : ℝ)) := by
  by_cases hsecond : fmt.finiteSystem ((x - (1 / 2 : ℝ)) + x)
  · by_cases hthird :
        fmt.finiteSystem (((x - (1 / 2 : ℝ)) + x) - (1 / 2 : ℝ))
    · exact False.elim
        ((fmt.problem2_24_eval_ne_zero_of_finiteSystem_input_of_ne_one_third_of_second_third_exact_intermediates
          hsub hhalf hx hxthird hsecond hthird) hzero)
    · exact Or.inr hthird
  · exact Or.inl hsecond

/-- In the lower sub-third part of any finite-system zero branch, the second
exact real intermediate is also finite-system representable. -/
theorem problem2_24_eval_eq_zero_second_exact_intermediate_finiteSystem_of_finiteSystem_input_of_lt_one_third
    {fmt : FloatingPointFormat} {x : ℝ}
    (hsub : fmt.subnormalMantissa 1)
    (hhalf : fmt.finiteSystem (1 / 2 : ℝ))
    (hx : fmt.finiteSystem x)
    (hzero : fmt.problem2_24_eval x = 0)
    (hxlt_third : x < (1 / 3 : ℝ)) :
    fmt.finiteSystem ((x - (1 / 2 : ℝ)) + x) := by
  have hxge :
      (3 / 10 : ℝ) ≤ x :=
    fmt.problem2_24_eval_eq_zero_input_ge_three_tenths_of_finiteSystem_input
      hsub hhalf hx hzero
  exact
    fmt.problem2_24_second_exact_intermediate_finiteSystem_of_quarter_lt_of_lt_one_third
      hhalf hx (by nlinarith) hxlt_third

/-- In the lower sub-third part of any finite-system zero branch, the
nonfinite exact-intermediate witness cannot be either of the first two exact
intermediates; it must be the third or final exact real intermediate. -/
theorem problem2_24_eval_eq_zero_implies_last_two_nonfinite_exact_intermediate_of_finiteSystem_input_of_lt_one_third
    {fmt : FloatingPointFormat} {x : ℝ}
    (hsub : fmt.subnormalMantissa 1)
    (hhalf : fmt.finiteSystem (1 / 2 : ℝ))
    (hx : fmt.finiteSystem x)
    (hxlt_third : x < (1 / 3 : ℝ))
    (hzero : fmt.problem2_24_eval x = 0) :
    ¬ fmt.finiteSystem (((x - (1 / 2 : ℝ)) + x) - (1 / 2 : ℝ)) ∨
      ¬ fmt.finiteSystem
        ((((x - (1 / 2 : ℝ)) + x) - (1 / 2 : ℝ)) + x) := by
  have hsecond :
      fmt.finiteSystem ((x - (1 / 2 : ℝ)) + x) :=
    fmt.problem2_24_eval_eq_zero_second_exact_intermediate_finiteSystem_of_finiteSystem_input_of_lt_one_third
      hsub hhalf hx hzero hxlt_third
  have hlater :=
    fmt.problem2_24_eval_eq_zero_implies_later_nonfinite_exact_intermediate_of_finiteSystem_input_of_ne_one_third
      hsub hhalf hx (by nlinarith : x ≠ (1 / 3 : ℝ)) hzero
  rcases hlater with hsecond_bad | hlast
  · exact False.elim (hsecond_bad hsecond)
  · exact hlast

/-- In the lower sub-third branch, a zero result is impossible if the third
exact real intermediate is finite-system representable. -/
theorem problem2_24_eval_ne_zero_of_finiteSystem_input_of_lt_one_third_of_third_exact_intermediate_finiteSystem
    {fmt : FloatingPointFormat} {x : ℝ}
    (hsub : fmt.subnormalMantissa 1)
    (hhalf : fmt.finiteSystem (1 / 2 : ℝ))
    (hx : fmt.finiteSystem x)
    (hxlt_third : x < (1 / 3 : ℝ))
    (hthird : fmt.finiteSystem
      (((x - (1 / 2 : ℝ)) + x) - (1 / 2 : ℝ))) :
    fmt.problem2_24_eval x ≠ 0 := by
  intro hzero
  have hxge :
      (3 / 10 : ℝ) ≤ x :=
    fmt.problem2_24_eval_eq_zero_input_ge_three_tenths_of_finiteSystem_input
      hsub hhalf hx hzero
  have hy2eq :
      fmt.problem2_24_y2 x = 2 * x - (1 / 2 : ℝ) :=
    fmt.problem2_24_y2_eq_two_mul_x_sub_half_of_finiteSystem_input_of_quarter_lt_of_lt_one_third
      hhalf hx (by nlinarith : (1 / 4 : ℝ) < x) hxlt_third
  have hthird_y2 :
      fmt.finiteSystem (fmt.problem2_24_y2 x - (1 / 2 : ℝ)) := by
    convert hthird using 1
    rw [hy2eq]
    ring
  have hy3exact :
      fmt.problem2_24_y3 x = fmt.problem2_24_y2 x - (1 / 2 : ℝ) := by
    simpa [problem2_24_y3, BasicOp.exact] using
      (fmt.finiteRoundToEvenOp_eq_exact_of_finiteSystem
        (op := BasicOp.sub) (x := fmt.problem2_24_y2 x)
        (y := (1 / 2 : ℝ)) hthird_y2)
  have hy3poly :
      fmt.problem2_24_y3 x = 2 * x - 1 := by
    rw [hy3exact, hy2eq]
    ring
  have hcancel :
      fmt.problem2_24_y3 x = -x :=
    fmt.problem2_24_y3_eq_neg_x_of_eval_eq_zero_of_finiteSystem_input
      hsub hx hzero
  nlinarith

/-- In the lower sub-third part of any finite-system zero branch, the third
exact real intermediate must be nonfinite. -/
theorem problem2_24_eval_eq_zero_implies_third_exact_intermediate_nonfinite_of_finiteSystem_input_of_lt_one_third
    {fmt : FloatingPointFormat} {x : ℝ}
    (hsub : fmt.subnormalMantissa 1)
    (hhalf : fmt.finiteSystem (1 / 2 : ℝ))
    (hx : fmt.finiteSystem x)
    (hxlt_third : x < (1 / 3 : ℝ))
    (hzero : fmt.problem2_24_eval x = 0) :
    ¬ fmt.finiteSystem (((x - (1 / 2 : ℝ)) + x) - (1 / 2 : ℝ)) := by
  intro hthird
  exact
    (fmt.problem2_24_eval_ne_zero_of_finiteSystem_input_of_lt_one_third_of_third_exact_intermediate_finiteSystem
      hsub hhalf hx hxlt_third hthird) hzero

/-- Parametric lower exclusion: any finite negative constant candidate `-a`
with `a > 1/3` rules out zero counterexamples below `(2-a)/5`.  Dyadic
candidates can therefore push the lower endpoint of the remaining branch
arbitrarily close to `1/3` when the format represents them. -/
theorem problem2_24_eval_ne_zero_of_finiteSystem_input_of_const_gt_one_third_of_lt_two_sub_const_div_five
    {fmt : FloatingPointFormat} {x a : ℝ}
    (hsub : fmt.subnormalMantissa 1)
    (hhalf : fmt.finiteSystem (1 / 2 : ℝ))
    (ha : fmt.finiteSystem (-a))
    (hx : fmt.finiteSystem x)
    (hagt : (1 / 3 : ℝ) < a)
    (hxlt : x < (2 - a) / 5) :
    fmt.problem2_24_eval x ≠ 0 := by
  intro hzero
  have hxge_three_tenths :
      (3 / 10 : ℝ) ≤ x :=
    fmt.problem2_24_eval_eq_zero_input_ge_three_tenths_of_finiteSystem_input
      hsub hhalf hx hzero
  have hxlt_third : x < (1 / 3 : ℝ) := by
    nlinarith
  have hxlt_const : x < a := by
    nlinarith
  have hy2eq :
      fmt.problem2_24_y2 x = 2 * x - (1 / 2 : ℝ) :=
    fmt.problem2_24_y2_eq_two_mul_x_sub_half_of_finiteSystem_input_of_quarter_lt_of_lt_one_third
      hhalf hx (by nlinarith : (1 / 4 : ℝ) < x) hxlt_third
  have hconst :=
    fmt.problem2_24_eval_eq_zero_last_sub_distance_to_neg_const_product_le_of_finiteSystem_input
      (a := a) hsub hx hzero ha
  have hfactor_nonneg :
      0 ≤ 2 * fmt.problem2_24_y2 x + x + a - 1 := by
    by_contra hge
    have hfactor_neg :
        2 * fmt.problem2_24_y2 x + x + a - 1 < 0 :=
      lt_of_not_ge hge
    have hx_minus_neg : x - a < 0 := by
      nlinarith
    have hmul_pos :
        0 < (x - a) * (2 * fmt.problem2_24_y2 x + x + a - 1) :=
      mul_pos_of_neg_of_neg hx_minus_neg hfactor_neg
    nlinarith
  rw [hy2eq] at hfactor_nonneg
  nlinarith

/-- Parametric lower endpoint for finite-system zero counterexamples. -/
theorem problem2_24_eval_eq_zero_input_ge_two_sub_const_div_five_of_finiteSystem_input
    {fmt : FloatingPointFormat} {x a : ℝ}
    (hsub : fmt.subnormalMantissa 1)
    (hhalf : fmt.finiteSystem (1 / 2 : ℝ))
    (ha : fmt.finiteSystem (-a))
    (hx : fmt.finiteSystem x)
    (hagt : (1 / 3 : ℝ) < a)
    (hzero : fmt.problem2_24_eval x = 0) :
    (2 - a) / 5 ≤ x := by
  by_contra hge
  have hxlt : x < (2 - a) / 5 := lt_of_not_ge hge
  exact
    (fmt.problem2_24_eval_ne_zero_of_finiteSystem_input_of_const_gt_one_third_of_lt_two_sub_const_div_five
      hsub hhalf ha hx hagt hxlt) hzero

/-- No finite-system zero counterexample can lie above `3/8`, provided the
dyadic candidate `-3/8` is finite in the format. -/
theorem problem2_24_eval_ne_zero_of_finiteSystem_input_of_three_eighths_lt
    {fmt : FloatingPointFormat} {x : ℝ}
    (hsub : fmt.subnormalMantissa 1)
    (hhalf : fmt.finiteSystem (1 / 2 : ℝ))
    (hneg_three_eighths : fmt.finiteSystem (-(3 / 8 : ℝ)))
    (hx : fmt.finiteSystem x)
    (hxgt : (3 / 8 : ℝ) < x) :
    fmt.problem2_24_eval x ≠ 0 := by
  intro hzero
  have hconst :=
    fmt.problem2_24_eval_eq_zero_last_sub_distance_to_neg_const_product_le_of_finiteSystem_input
      (a := (3 / 8 : ℝ)) hsub hx hzero hneg_three_eighths
  have hconst_factor :
      2 * fmt.problem2_24_y2 x + x + (3 / 8 : ℝ) - 1 ≤ 0 := by
    by_contra hle
    have hfactor_pos :
        0 < 2 * fmt.problem2_24_y2 x + x + (3 / 8 : ℝ) - 1 :=
      lt_of_not_ge hle
    have hx_minus_pos : 0 < x - (3 / 8 : ℝ) := by
      nlinarith
    have hmul_pos :
        0 < (x - (3 / 8 : ℝ)) *
          (2 * fmt.problem2_24_y2 x + x + (3 / 8 : ℝ) - 1) :=
      mul_pos hx_minus_pos hfactor_pos
    nlinarith
  have hy2_upper :
      fmt.problem2_24_y2 x ≤ ((5 / 8 : ℝ) - x) / 2 := by
    nlinarith
  have hxlt_half : x < (1 / 2 : ℝ) := by
    by_contra hlt
    have hxhalf : (1 / 2 : ℝ) ≤ x := le_of_not_gt hlt
    exact
      (fmt.problem2_24_eval_ne_zero_of_finiteSystem_input_of_half_le
        hsub hx hxhalf) hzero
  have hy1eq :
      fmt.problem2_24_y1 x = x - (1 / 2 : ℝ) :=
    fmt.problem2_24_y1_eq_x_sub_half_of_finiteSystem_input_of_quarter_lt_of_lt_one
      hhalf hx (by nlinarith : (1 / 4 : ℝ) < x)
      (by nlinarith : x < (1 : ℝ))
  have hprod :=
    fmt.problem2_24_y2_second_add_distance_to_x_product_le_of_finiteSystem_input
      hx
  rw [hy1eq] at hprod
  have hfirst_pos : 0 < x - fmt.problem2_24_y2 x := by
    nlinarith
  have hsecond_pos :
      0 < 2 * (x - (1 / 2 : ℝ)) + x - fmt.problem2_24_y2 x := by
    nlinarith
  have hmul_pos :
      0 < (x - fmt.problem2_24_y2 x) *
        (2 * (x - (1 / 2 : ℝ)) + x - fmt.problem2_24_y2 x) :=
    mul_pos hfirst_pos hsecond_pos
  nlinarith

/-- Every finite-system zero counterexample has input at most `3/8`, provided
the dyadic candidate `-3/8` is finite in the format. -/
theorem problem2_24_eval_eq_zero_input_le_three_eighths_of_finiteSystem_input
    {fmt : FloatingPointFormat} {x : ℝ}
    (hsub : fmt.subnormalMantissa 1)
    (hhalf : fmt.finiteSystem (1 / 2 : ℝ))
    (hneg_three_eighths : fmt.finiteSystem (-(3 / 8 : ℝ)))
    (hx : fmt.finiteSystem x)
    (hzero : fmt.problem2_24_eval x = 0) :
    x ≤ (3 / 8 : ℝ) := by
  by_contra hle
  have hxgt : (3 / 8 : ℝ) < x := lt_of_not_ge hle
  exact
    (fmt.problem2_24_eval_ne_zero_of_finiteSystem_input_of_three_eighths_lt
      hsub hhalf hneg_three_eighths hx hxgt) hzero

/-- No finite-system zero counterexample can lie below `53/160`, provided the
dyadic candidate `-11/32` is finite in the format. -/
theorem problem2_24_eval_ne_zero_of_finiteSystem_input_of_lt_fifty_three_one_sixty
    {fmt : FloatingPointFormat} {x : ℝ}
    (hsub : fmt.subnormalMantissa 1)
    (hhalf : fmt.finiteSystem (1 / 2 : ℝ))
    (hneg_eleven_thirty_two : fmt.finiteSystem (-(11 / 32 : ℝ)))
    (hx : fmt.finiteSystem x)
    (hxlt : x < (53 / 160 : ℝ)) :
    fmt.problem2_24_eval x ≠ 0 := by
  intro hzero
  have hxge_three_tenths :
      (3 / 10 : ℝ) ≤ x :=
    fmt.problem2_24_eval_eq_zero_input_ge_three_tenths_of_finiteSystem_input
      hsub hhalf hx hzero
  have hxlt_third : x < (1 / 3 : ℝ) := by
    nlinarith
  have hxlt_const : x < (11 / 32 : ℝ) := by
    nlinarith
  have hy2eq :
      fmt.problem2_24_y2 x = 2 * x - (1 / 2 : ℝ) :=
    fmt.problem2_24_y2_eq_two_mul_x_sub_half_of_finiteSystem_input_of_quarter_lt_of_lt_one_third
      hhalf hx (by nlinarith : (1 / 4 : ℝ) < x) hxlt_third
  have hconst :=
    fmt.problem2_24_eval_eq_zero_last_sub_distance_to_neg_const_product_le_of_finiteSystem_input
      (a := (11 / 32 : ℝ)) hsub hx hzero hneg_eleven_thirty_two
  have hfactor_nonneg :
      0 ≤ 2 * fmt.problem2_24_y2 x + x + (11 / 32 : ℝ) - 1 := by
    by_contra hge
    have hfactor_neg :
        2 * fmt.problem2_24_y2 x + x + (11 / 32 : ℝ) - 1 < 0 :=
      lt_of_not_ge hge
    have hx_minus_neg : x - (11 / 32 : ℝ) < 0 := by
      nlinarith
    have hmul_pos :
        0 < (x - (11 / 32 : ℝ)) *
          (2 * fmt.problem2_24_y2 x + x + (11 / 32 : ℝ) - 1) :=
      mul_pos_of_neg_of_neg hx_minus_neg hfactor_neg
    nlinarith
  rw [hy2eq] at hfactor_nonneg
  nlinarith

/-- Every finite-system zero counterexample has input at least `53/160`,
provided the dyadic candidate `-11/32` is finite in the format. -/
theorem problem2_24_eval_eq_zero_input_ge_fifty_three_one_sixty_of_finiteSystem_input
    {fmt : FloatingPointFormat} {x : ℝ}
    (hsub : fmt.subnormalMantissa 1)
    (hhalf : fmt.finiteSystem (1 / 2 : ℝ))
    (hneg_eleven_thirty_two : fmt.finiteSystem (-(11 / 32 : ℝ)))
    (hx : fmt.finiteSystem x)
    (hzero : fmt.problem2_24_eval x = 0) :
    (53 / 160 : ℝ) ≤ x := by
  by_contra hge
  have hxlt : x < (53 / 160 : ℝ) := lt_of_not_ge hge
  exact
    (fmt.problem2_24_eval_ne_zero_of_finiteSystem_input_of_lt_fifty_three_one_sixty
      hsub hhalf hneg_eleven_thirty_two hx hxlt) hzero

/-- The remaining modeled finite-system zero-counterexample branch, if any,
lies in `[53/160, 3/8]`, provided the two dyadic candidates are finite. -/
theorem problem2_24_eval_eq_zero_input_mem_fifty_three_one_sixty_to_three_eighths_of_finiteSystem_input
    {fmt : FloatingPointFormat} {x : ℝ}
    (hsub : fmt.subnormalMantissa 1)
    (hhalf : fmt.finiteSystem (1 / 2 : ℝ))
    (hneg_eleven_thirty_two : fmt.finiteSystem (-(11 / 32 : ℝ)))
    (hneg_three_eighths : fmt.finiteSystem (-(3 / 8 : ℝ)))
    (hx : fmt.finiteSystem x)
    (hzero : fmt.problem2_24_eval x = 0) :
    (53 / 160 : ℝ) ≤ x ∧ x ≤ (3 / 8 : ℝ) :=
  ⟨fmt.problem2_24_eval_eq_zero_input_ge_fifty_three_one_sixty_of_finiteSystem_input
      hsub hhalf hneg_eleven_thirty_two hx hzero,
    fmt.problem2_24_eval_eq_zero_input_le_three_eighths_of_finiteSystem_input
      hsub hhalf hneg_three_eighths hx hzero⟩

theorem problem2_24_ieeeSingle_half_finiteSystem :
    ieeeSingleFormat.finiteSystem (1 / 2 : ℝ) := by
  refine Or.inr (Or.inl ?_)
  refine ⟨false, 8388608, (0 : ℤ), ?_, ?_, ?_⟩
  · norm_num [ieeeSingleFormat, normalizedMantissa, mantissaInRange,
      minNormalMantissa]
  · norm_num [ieeeSingleFormat, exponentInRange]
  · norm_num [ieeeSingleFormat, normalizedValue, signValue, betaR, zpow_neg]

theorem problem2_24_ieeeDouble_half_finiteSystem :
    ieeeDoubleFormat.finiteSystem (1 / 2 : ℝ) := by
  refine Or.inr (Or.inl ?_)
  refine ⟨false, 4503599627370496, (0 : ℤ), ?_, ?_, ?_⟩
  · norm_num [ieeeDoubleFormat, normalizedMantissa, mantissaInRange,
      minNormalMantissa]
  · norm_num [ieeeDoubleFormat, exponentInRange]
  · norm_num [ieeeDoubleFormat, normalizedValue, signValue, betaR, zpow_neg]

theorem problem2_24_ieeeSingle_three_eighths_finiteSystem :
    ieeeSingleFormat.finiteSystem (3 / 8 : ℝ) := by
  refine Or.inr (Or.inl ?_)
  refine ⟨false, 12582912, (-1 : ℤ), ?_, ?_, ?_⟩
  · norm_num [ieeeSingleFormat, normalizedMantissa, mantissaInRange,
      minNormalMantissa]
  · norm_num [ieeeSingleFormat, exponentInRange]
  · norm_num [ieeeSingleFormat, normalizedValue, signValue, betaR, zpow_neg]

theorem problem2_24_ieeeDouble_three_eighths_finiteSystem :
    ieeeDoubleFormat.finiteSystem (3 / 8 : ℝ) := by
  refine Or.inr (Or.inl ?_)
  refine ⟨false, 6755399441055744, (-1 : ℤ), ?_, ?_, ?_⟩
  · norm_num [ieeeDoubleFormat, normalizedMantissa, mantissaInRange,
      minNormalMantissa]
  · norm_num [ieeeDoubleFormat, exponentInRange]
  · norm_num [ieeeDoubleFormat, normalizedValue, signValue, betaR, zpow_neg]

theorem problem2_24_ieeeSingle_eleven_thirty_two_finiteSystem :
    ieeeSingleFormat.finiteSystem (11 / 32 : ℝ) := by
  refine Or.inr (Or.inl ?_)
  refine ⟨false, 11534336, (-1 : ℤ), ?_, ?_, ?_⟩
  · norm_num [ieeeSingleFormat, normalizedMantissa, mantissaInRange,
      minNormalMantissa]
  · norm_num [ieeeSingleFormat, exponentInRange]
  · norm_num [ieeeSingleFormat, normalizedValue, signValue, betaR, zpow_neg]

theorem problem2_24_ieeeDouble_eleven_thirty_two_finiteSystem :
    ieeeDoubleFormat.finiteSystem (11 / 32 : ℝ) := by
  refine Or.inr (Or.inl ?_)
  refine ⟨false, 6192449487634432, (-1 : ℤ), ?_, ?_, ?_⟩
  · norm_num [ieeeDoubleFormat, normalizedMantissa, mantissaInRange,
      minNormalMantissa]
  · norm_num [ieeeDoubleFormat, exponentInRange]
  · norm_num [ieeeDoubleFormat, normalizedValue, signValue, betaR, zpow_neg]

/-- The single-precision value immediately above `1/3` is finite. -/
theorem problem2_24_ieeeSingle_one_third_upper_neighbor_finiteSystem :
    ieeeSingleFormat.finiteSystem
      ((11184811 : ℝ) * (2 : ℝ) ^ (-25 : ℤ)) := by
  refine Or.inr (Or.inl ?_)
  refine ⟨false, 11184811, (-1 : ℤ), ?_, ?_, ?_⟩
  · norm_num [ieeeSingleFormat, normalizedMantissa, mantissaInRange,
      minNormalMantissa]
  · norm_num [ieeeSingleFormat, exponentInRange]
  · norm_num [ieeeSingleFormat, normalizedValue, signValue, betaR, zpow_neg]

/-- The double-precision value immediately above `1/3` is finite. -/
theorem problem2_24_ieeeDouble_one_third_upper_neighbor_finiteSystem :
    ieeeDoubleFormat.finiteSystem
      ((6004799503160662 : ℝ) * (2 : ℝ) ^ (-54 : ℤ)) := by
  refine Or.inr (Or.inl ?_)
  refine ⟨false, 6004799503160662, (-1 : ℤ), ?_, ?_, ?_⟩
  · norm_num [ieeeDoubleFormat, normalizedMantissa, mantissaInRange,
      minNormalMantissa]
  · norm_num [ieeeDoubleFormat, exponentInRange]
  · norm_num [ieeeDoubleFormat, normalizedValue, signValue, betaR, zpow_neg]

theorem problem2_24_ieeeSingle_one_quarter_finiteSystem :
    ieeeSingleFormat.finiteSystem (1 / 4 : ℝ) := by
  refine Or.inr (Or.inl ?_)
  refine ⟨false, 8388608, (-1 : ℤ), ?_, ?_, ?_⟩
  · norm_num [ieeeSingleFormat, normalizedMantissa, mantissaInRange,
      minNormalMantissa]
  · norm_num [ieeeSingleFormat, exponentInRange]
  · norm_num [ieeeSingleFormat, normalizedValue, signValue, betaR, zpow_neg]

theorem problem2_24_ieeeDouble_one_quarter_finiteSystem :
    ieeeDoubleFormat.finiteSystem (1 / 4 : ℝ) := by
  refine Or.inr (Or.inl ?_)
  refine ⟨false, 4503599627370496, (-1 : ℤ), ?_, ?_, ?_⟩
  · norm_num [ieeeDoubleFormat, normalizedMantissa, mantissaInRange,
      minNormalMantissa]
  · norm_num [ieeeDoubleFormat, exponentInRange]
  · norm_num [ieeeDoubleFormat, normalizedValue, signValue, betaR, zpow_neg]

/-- IEEE-single finite-grid adapter for the remaining Problem 2.24 adjacent
branch.  A positive normalized value with exponent `-1` and mantissa between
the upper finite value above `1/3` and the finite value `3/8` has a finite
exact second real intermediate `(x-0.5)+x`. -/
theorem problem2_24_ieeeSingle_second_exact_intermediate_finiteSystem_of_neg_one_mantissa_mem_upper_branch
    {m : ℕ}
    (hmlo : 11184811 ≤ m)
    (hmhi : m ≤ 12582912) :
    ieeeSingleFormat.finiteSystem
      (((ieeeSingleFormat.normalizedValue false m (-1) - (1 / 2 : ℝ)) +
        ieeeSingleFormat.normalizedValue false m (-1))) := by
  by_cases htop : m = 12582912
  · subst m
    convert problem2_24_ieeeSingle_one_quarter_finiteSystem using 1
    norm_num [ieeeSingleFormat, normalizedValue, signValue, betaR, zpow_neg]
  · have hlt : m < 12582912 := Nat.lt_of_le_of_ne hmhi htop
    have hle_sub : 33554432 ≤ 4 * m := by omega
    refine Or.inr (Or.inl ?_)
    refine ⟨false, 4 * m - 33554432, (-2 : ℤ), ?_, ?_, ?_⟩
    · constructor
      · norm_num [ieeeSingleFormat, minNormalMantissa]
        omega
      · norm_num [ieeeSingleFormat, mantissaInRange]
        omega
    · norm_num [ieeeSingleFormat, exponentInRange]
    · have hcast :
          ((4 * m - 33554432 : ℕ) : ℝ) =
            4 * (m : ℝ) - 33554432 := by
        rw [Nat.cast_sub hle_sub]
        norm_num
      norm_num [ieeeSingleFormat, normalizedValue, signValue, betaR, zpow_neg]
      rw [hcast]
      ring

/-- IEEE-double finite-grid adapter for the remaining Problem 2.24 adjacent
branch.  A positive normalized value with exponent `-1` and mantissa between
the upper finite value above `1/3` and the finite value `3/8` has a finite
exact second real intermediate `(x-0.5)+x`. -/
theorem problem2_24_ieeeDouble_second_exact_intermediate_finiteSystem_of_neg_one_mantissa_mem_upper_branch
    {m : ℕ}
    (hmlo : 6004799503160662 ≤ m)
    (hmhi : m ≤ 6755399441055744) :
    ieeeDoubleFormat.finiteSystem
      (((ieeeDoubleFormat.normalizedValue false m (-1) - (1 / 2 : ℝ)) +
        ieeeDoubleFormat.normalizedValue false m (-1))) := by
  by_cases htop : m = 6755399441055744
  · subst m
    convert problem2_24_ieeeDouble_one_quarter_finiteSystem using 1
    norm_num [ieeeDoubleFormat, normalizedValue, signValue, betaR, zpow_neg]
  · have hlt : m < 6755399441055744 := Nat.lt_of_le_of_ne hmhi htop
    have hle_sub : 18014398509481984 ≤ 4 * m := by omega
    refine Or.inr (Or.inl ?_)
    refine ⟨false, 4 * m - 18014398509481984, (-2 : ℤ), ?_, ?_, ?_⟩
    · constructor
      · norm_num [ieeeDoubleFormat, minNormalMantissa]
        omega
      · norm_num [ieeeDoubleFormat, mantissaInRange]
        omega
    · norm_num [ieeeDoubleFormat, exponentInRange]
    · have hcast :
          ((4 * m - 18014398509481984 : ℕ) : ℝ) =
            4 * (m : ℝ) - 18014398509481984 := by
        rw [Nat.cast_sub hle_sub]
        norm_num
      norm_num [ieeeDoubleFormat, normalizedValue, signValue, betaR, zpow_neg]
      rw [hcast]
      ring

/-- IEEE-single interval-to-mantissa adapter for the upper adjacent
Problem 2.24 branch.  Any finite single value between the upper finite value
above `1/3` and `3/8` is a positive normalized exponent-`-1` value with
mantissa in the matching integer interval. -/
theorem problem2_24_ieeeSingle_finiteSystem_upper_branch_exists_neg_one_mantissa
    {x : ℝ}
    (hx : ieeeSingleFormat.finiteSystem x)
    (hlo : (11184811 : ℝ) * (2 : ℝ) ^ (-25 : ℤ) ≤ x)
    (hhi : x ≤ (3 / 8 : ℝ)) :
    ∃ m : ℕ,
      11184811 ≤ m ∧ m ≤ 12582912 ∧
        x = ieeeSingleFormat.normalizedValue false m (-1) := by
  rcases hx with hzero | hnorm | hsub
  · subst x
    norm_num [zpow_neg] at hlo
  · rcases hnorm with ⟨negative, m, e, hm, _he, rfl⟩
    have hlower_pos :
        0 < (11184811 : ℝ) * (2 : ℝ) ^ (-25 : ℤ) := by
      norm_num [zpow_neg]
    cases negative
    · rcases lt_trichotomy e (-1 : ℤ) with hlt | heq | hgt
      · have hbelow_quarter :
            ieeeSingleFormat.normalizedValue false m e < (1 / 4 : ℝ) := by
          have hlt' :
              ieeeSingleFormat.normalizedValue false m e <
                ieeeSingleFormat.normalizedValue false
                  ieeeSingleFormat.minNormalMantissa (-1) :=
            ieeeSingleFormat.normalizedValue_false_lt_of_exp_lt hm
              ieeeSingleFormat.minNormalMantissa_normalized hlt
          have hquarter :
              ieeeSingleFormat.normalizedValue false
                  ieeeSingleFormat.minNormalMantissa (-1) =
                (1 / 4 : ℝ) := by
            norm_num [ieeeSingleFormat, normalizedValue, signValue, betaR,
              minNormalMantissa, zpow_neg]
          simpa [hquarter] using hlt'
        have hquarter_lt_lower :
            (1 / 4 : ℝ) <
              (11184811 : ℝ) * (2 : ℝ) ^ (-25 : ℤ) := by
          norm_num [zpow_neg]
        exact False.elim
          ((not_lt_of_ge hlo)
            (lt_trans hbelow_quarter hquarter_lt_lower))
      · subst e
        have hscale_pos : 0 < (2 : ℝ) ^ (-25 : ℤ) := by
          norm_num [zpow_neg]
        have hmlo : 11184811 ≤ m := by
          have hscaled :
              (11184811 : ℝ) * (2 : ℝ) ^ (-25 : ℤ) ≤
                (m : ℝ) * (2 : ℝ) ^ (-25 : ℤ) := by
            simpa [ieeeSingleFormat, normalizedValue, signValue, betaR] using hlo
          have hcast : (11184811 : ℝ) ≤ (m : ℝ) :=
            le_of_mul_le_mul_right hscaled hscale_pos
          exact Nat.cast_le.mp hcast
        have hmhi : m ≤ 12582912 := by
          have hupper_eq :
              (3 / 8 : ℝ) =
                (12582912 : ℝ) * (2 : ℝ) ^ (-25 : ℤ) := by
            norm_num [zpow_neg]
          have hscaled :
              (m : ℝ) * (2 : ℝ) ^ (-25 : ℤ) ≤
                (12582912 : ℝ) * (2 : ℝ) ^ (-25 : ℤ) := by
            rw [hupper_eq] at hhi
            simpa [ieeeSingleFormat, normalizedValue, signValue, betaR] using hhi
          have hcast : (m : ℝ) ≤ (12582912 : ℝ) :=
            le_of_mul_le_mul_right hscaled hscale_pos
          exact Nat.cast_le.mp hcast
        exact ⟨m, hmlo, hmhi, rfl⟩
      · have hhalf_le :
            (1 / 2 : ℝ) ≤ ieeeSingleFormat.normalizedValue false m e := by
          have hle_exp : (-1 : ℤ) + 1 ≤ e := by
            omega
          have hle :
              ieeeSingleFormat.normalizedValue false
                  ieeeSingleFormat.minNormalMantissa ((-1 : ℤ) + 1) ≤
                ieeeSingleFormat.normalizedValue false m e :=
            ieeeSingleFormat.normalizedValue_false_minNormalMantissa_le_of_exp_le
              (m := m) (e := (-1 : ℤ)) (e' := e) hm hle_exp
          have hle0 :
              ieeeSingleFormat.normalizedValue false
                  ieeeSingleFormat.minNormalMantissa 0 ≤
                ieeeSingleFormat.normalizedValue false m e := by
            simpa using hle
          have hhalf :
              ieeeSingleFormat.normalizedValue false
                  ieeeSingleFormat.minNormalMantissa 0 =
                (1 / 2 : ℝ) := by
            norm_num [ieeeSingleFormat, normalizedValue, signValue, betaR,
              minNormalMantissa, zpow_neg]
          rw [hhalf] at hle0
          exact hle0
        linarith
    · have hneg :
          ieeeSingleFormat.normalizedValue true m e < 0 :=
        ieeeSingleFormat.normalizedValue_true_neg hm
      linarith
  · have hsub_le :
        x ≤ ieeeSingleFormat.minNormalMagnitude :=
      ieeeSingleFormat.subnormalSystem_le_minNormalMagnitude hsub
    have hmin_lt_lower :
        ieeeSingleFormat.minNormalMagnitude <
          (11184811 : ℝ) * (2 : ℝ) ^ (-25 : ℤ) := by
      norm_num [ieeeSingleFormat, minNormalMagnitude, betaR, zpow_neg]
    linarith

/-- IEEE-double interval-to-mantissa adapter for the upper adjacent
Problem 2.24 branch.  Any finite double value between the upper finite value
above `1/3` and `3/8` is a positive normalized exponent-`-1` value with
mantissa in the matching integer interval. -/
theorem problem2_24_ieeeDouble_finiteSystem_upper_branch_exists_neg_one_mantissa
    {x : ℝ}
    (hx : ieeeDoubleFormat.finiteSystem x)
    (hlo : (6004799503160662 : ℝ) * (2 : ℝ) ^ (-54 : ℤ) ≤ x)
    (hhi : x ≤ (3 / 8 : ℝ)) :
    ∃ m : ℕ,
      6004799503160662 ≤ m ∧ m ≤ 6755399441055744 ∧
        x = ieeeDoubleFormat.normalizedValue false m (-1) := by
  rcases hx with hzero | hnorm | hsub
  · subst x
    norm_num [zpow_neg] at hlo
  · rcases hnorm with ⟨negative, m, e, hm, _he, rfl⟩
    have hlower_pos :
        0 < (6004799503160662 : ℝ) * (2 : ℝ) ^ (-54 : ℤ) := by
      norm_num [zpow_neg]
    cases negative
    · rcases lt_trichotomy e (-1 : ℤ) with hlt | heq | hgt
      · have hbelow_quarter :
            ieeeDoubleFormat.normalizedValue false m e < (1 / 4 : ℝ) := by
          have hlt' :
              ieeeDoubleFormat.normalizedValue false m e <
                ieeeDoubleFormat.normalizedValue false
                  ieeeDoubleFormat.minNormalMantissa (-1) :=
            ieeeDoubleFormat.normalizedValue_false_lt_of_exp_lt hm
              ieeeDoubleFormat.minNormalMantissa_normalized hlt
          have hquarter :
              ieeeDoubleFormat.normalizedValue false
                  ieeeDoubleFormat.minNormalMantissa (-1) =
                (1 / 4 : ℝ) := by
            norm_num [ieeeDoubleFormat, normalizedValue, signValue, betaR,
              minNormalMantissa, zpow_neg]
          simpa [hquarter] using hlt'
        have hquarter_lt_lower :
            (1 / 4 : ℝ) <
              (6004799503160662 : ℝ) * (2 : ℝ) ^ (-54 : ℤ) := by
          norm_num [zpow_neg]
        exact False.elim
          ((not_lt_of_ge hlo)
            (lt_trans hbelow_quarter hquarter_lt_lower))
      · subst e
        have hscale_pos : 0 < (2 : ℝ) ^ (-54 : ℤ) := by
          norm_num [zpow_neg]
        have hmlo : 6004799503160662 ≤ m := by
          have hscaled :
              (6004799503160662 : ℝ) * (2 : ℝ) ^ (-54 : ℤ) ≤
                (m : ℝ) * (2 : ℝ) ^ (-54 : ℤ) := by
            simpa [ieeeDoubleFormat, normalizedValue, signValue, betaR] using hlo
          have hcast : (6004799503160662 : ℝ) ≤ (m : ℝ) :=
            le_of_mul_le_mul_right hscaled hscale_pos
          exact Nat.cast_le.mp hcast
        have hmhi : m ≤ 6755399441055744 := by
          have hupper_eq :
              (3 / 8 : ℝ) =
                (6755399441055744 : ℝ) * (2 : ℝ) ^ (-54 : ℤ) := by
            norm_num [zpow_neg]
          have hscaled :
              (m : ℝ) * (2 : ℝ) ^ (-54 : ℤ) ≤
                (6755399441055744 : ℝ) * (2 : ℝ) ^ (-54 : ℤ) := by
            rw [hupper_eq] at hhi
            simpa [ieeeDoubleFormat, normalizedValue, signValue, betaR] using hhi
          have hcast : (m : ℝ) ≤ (6755399441055744 : ℝ) :=
            le_of_mul_le_mul_right hscaled hscale_pos
          exact Nat.cast_le.mp hcast
        exact ⟨m, hmlo, hmhi, rfl⟩
      · have hhalf_le :
            (1 / 2 : ℝ) ≤ ieeeDoubleFormat.normalizedValue false m e := by
          have hle_exp : (-1 : ℤ) + 1 ≤ e := by
            omega
          have hle :
              ieeeDoubleFormat.normalizedValue false
                  ieeeDoubleFormat.minNormalMantissa ((-1 : ℤ) + 1) ≤
                ieeeDoubleFormat.normalizedValue false m e :=
            ieeeDoubleFormat.normalizedValue_false_minNormalMantissa_le_of_exp_le
              (m := m) (e := (-1 : ℤ)) (e' := e) hm hle_exp
          have hle0 :
              ieeeDoubleFormat.normalizedValue false
                  ieeeDoubleFormat.minNormalMantissa 0 ≤
                ieeeDoubleFormat.normalizedValue false m e := by
            simpa using hle
          have hhalf :
              ieeeDoubleFormat.normalizedValue false
                  ieeeDoubleFormat.minNormalMantissa 0 =
                (1 / 2 : ℝ) := by
            norm_num [ieeeDoubleFormat, normalizedValue, signValue, betaR,
              minNormalMantissa, zpow_neg]
          rw [hhalf] at hle0
          exact hle0
        linarith
    · have hneg :
          ieeeDoubleFormat.normalizedValue true m e < 0 :=
        ieeeDoubleFormat.normalizedValue_true_neg hm
      linarith
  · have hsub_le :
        x ≤ ieeeDoubleFormat.minNormalMagnitude :=
      ieeeDoubleFormat.subnormalSystem_le_minNormalMagnitude hsub
    have hmin_lt_lower :
        ieeeDoubleFormat.minNormalMagnitude <
          (6004799503160662 : ℝ) * (2 : ℝ) ^ (-54 : ℤ) := by
      have hmin_lt_quarter :
          ieeeDoubleFormat.minNormalMagnitude < (1 / 4 : ℝ) := by
        have hpow :
            (4 : ℝ) < (2 : ℝ) ^ (1022 : ℕ) := by
          have hpow_lt :
              (2 : ℝ) ^ (2 : ℕ) < (2 : ℝ) ^ (1022 : ℕ) :=
            pow_lt_pow_right₀ (by norm_num : (1 : ℝ) < 2)
              (by norm_num : (2 : ℕ) < 1022)
          norm_num at hpow_lt ⊢
          exact hpow_lt
        simpa [ieeeDoubleFormat, minNormalMagnitude, betaR, zpow_neg] using
          one_div_lt_one_div_of_lt (by norm_num : (0 : ℝ) < 4) hpow
      have hquarter_lt_lower :
          (1 / 4 : ℝ) <
            (6004799503160662 : ℝ) * (2 : ℝ) ^ (-54 : ℤ) := by
        norm_num [zpow_neg]
      exact lt_trans hmin_lt_quarter hquarter_lt_lower
    linarith

/-- IEEE-single upper-branch second-exact closure for Problem 2.24.  Once a
finite input is known to lie between the upper finite value above `1/3` and
`3/8`, the exact second real intermediate `(x-0.5)+x` is finite representable. -/
theorem problem2_24_ieeeSingle_second_exact_intermediate_finiteSystem_of_finiteSystem_upper_branch
    {x : ℝ}
    (hx : ieeeSingleFormat.finiteSystem x)
    (hlo : (11184811 : ℝ) * (2 : ℝ) ^ (-25 : ℤ) ≤ x)
    (hhi : x ≤ (3 / 8 : ℝ)) :
    ieeeSingleFormat.finiteSystem ((x - (1 / 2 : ℝ)) + x) := by
  rcases
      problem2_24_ieeeSingle_finiteSystem_upper_branch_exists_neg_one_mantissa
        hx hlo hhi with
    ⟨m, hmlo, hmhi, rfl⟩
  exact
    problem2_24_ieeeSingle_second_exact_intermediate_finiteSystem_of_neg_one_mantissa_mem_upper_branch
      hmlo hmhi

/-- IEEE-double upper-branch second-exact closure for Problem 2.24.  Once a
finite input is known to lie between the upper finite value above `1/3` and
`3/8`, the exact second real intermediate `(x-0.5)+x` is finite representable. -/
theorem problem2_24_ieeeDouble_second_exact_intermediate_finiteSystem_of_finiteSystem_upper_branch
    {x : ℝ}
    (hx : ieeeDoubleFormat.finiteSystem x)
    (hlo : (6004799503160662 : ℝ) * (2 : ℝ) ^ (-54 : ℤ) ≤ x)
    (hhi : x ≤ (3 / 8 : ℝ)) :
    ieeeDoubleFormat.finiteSystem ((x - (1 / 2 : ℝ)) + x) := by
  rcases
      problem2_24_ieeeDouble_finiteSystem_upper_branch_exists_neg_one_mantissa
        hx hlo hhi with
    ⟨m, hmlo, hmhi, rfl⟩
  exact
    problem2_24_ieeeDouble_second_exact_intermediate_finiteSystem_of_neg_one_mantissa_mem_upper_branch
      hmlo hmhi

/-- IEEE-single finite-grid adapter for the full localized zero branch in
Problem 2.24.  A positive normalized exponent-`-1` value in `[3/10, 3/8]`
has finite exact third real intermediate `((x-0.5)+x)-0.5 = 2*x-1`. -/
theorem problem2_24_ieeeSingle_third_exact_intermediate_finiteSystem_of_neg_one_mantissa_mem_zero_branch
    {m : ℕ}
    (hmlo : 10066330 ≤ m)
    (hmhi : m ≤ 12582912) :
    ieeeSingleFormat.finiteSystem
      (((ieeeSingleFormat.normalizedValue false m (-1) - (1 / 2 : ℝ)) +
        ieeeSingleFormat.normalizedValue false m (-1)) - (1 / 2 : ℝ)) := by
  have hle_sub : 2 * m ≤ 33554432 := by omega
  refine Or.inr (Or.inl ?_)
  refine ⟨true, 33554432 - 2 * m, (-1 : ℤ), ?_, ?_, ?_⟩
  · constructor
    · norm_num [ieeeSingleFormat, minNormalMantissa]
      omega
    · norm_num [ieeeSingleFormat, mantissaInRange]
      omega
  · norm_num [ieeeSingleFormat, exponentInRange]
  · have hcast :
        ((33554432 - 2 * m : ℕ) : ℝ) =
          33554432 - 2 * (m : ℝ) := by
      rw [Nat.cast_sub hle_sub]
      norm_num
    norm_num [ieeeSingleFormat, normalizedValue, signValue, betaR, zpow_neg]
    rw [hcast]
    ring

/-- IEEE-double finite-grid adapter for the full localized zero branch in
Problem 2.24.  A positive normalized exponent-`-1` value in `[3/10, 3/8]`
has finite exact third real intermediate `((x-0.5)+x)-0.5 = 2*x-1`. -/
theorem problem2_24_ieeeDouble_third_exact_intermediate_finiteSystem_of_neg_one_mantissa_mem_zero_branch
    {m : ℕ}
    (hmlo : 5404319552844596 ≤ m)
    (hmhi : m ≤ 6755399441055744) :
    ieeeDoubleFormat.finiteSystem
      (((ieeeDoubleFormat.normalizedValue false m (-1) - (1 / 2 : ℝ)) +
        ieeeDoubleFormat.normalizedValue false m (-1)) - (1 / 2 : ℝ)) := by
  have hle_sub : 2 * m ≤ 18014398509481984 := by omega
  refine Or.inr (Or.inl ?_)
  refine ⟨true, 18014398509481984 - 2 * m, (-1 : ℤ), ?_, ?_, ?_⟩
  · constructor
    · norm_num [ieeeDoubleFormat, minNormalMantissa]
      omega
    · norm_num [ieeeDoubleFormat, mantissaInRange]
      omega
  · norm_num [ieeeDoubleFormat, exponentInRange]
  · have hcast :
        ((18014398509481984 - 2 * m : ℕ) : ℝ) =
          18014398509481984 - 2 * (m : ℝ) := by
      rw [Nat.cast_sub hle_sub]
      norm_num
    norm_num [ieeeDoubleFormat, normalizedValue, signValue, betaR, zpow_neg]
    rw [hcast]
    ring

/-- IEEE-single interval-to-mantissa adapter for the complete localized
Problem 2.24 zero branch. -/
theorem problem2_24_ieeeSingle_finiteSystem_zero_branch_exists_neg_one_mantissa
    {x : ℝ}
    (hx : ieeeSingleFormat.finiteSystem x)
    (hlo : (3 / 10 : ℝ) ≤ x)
    (hhi : x ≤ (3 / 8 : ℝ)) :
    ∃ m : ℕ,
      10066330 ≤ m ∧ m ≤ 12582912 ∧
        x = ieeeSingleFormat.normalizedValue false m (-1) := by
  rcases hx with hzero | hnorm | hsub
  · subst x
    norm_num at hlo
  · rcases hnorm with ⟨negative, m, e, hm, _he, rfl⟩
    cases negative
    · rcases lt_trichotomy e (-1 : ℤ) with hlt | heq | hgt
      · have hbelow_quarter :
            ieeeSingleFormat.normalizedValue false m e < (1 / 4 : ℝ) := by
          have hlt' :
              ieeeSingleFormat.normalizedValue false m e <
                ieeeSingleFormat.normalizedValue false
                  ieeeSingleFormat.minNormalMantissa (-1) :=
            ieeeSingleFormat.normalizedValue_false_lt_of_exp_lt hm
              ieeeSingleFormat.minNormalMantissa_normalized hlt
          have hquarter :
              ieeeSingleFormat.normalizedValue false
                  ieeeSingleFormat.minNormalMantissa (-1) =
                (1 / 4 : ℝ) := by
            norm_num [ieeeSingleFormat, normalizedValue, signValue, betaR,
              minNormalMantissa, zpow_neg]
          simpa [hquarter] using hlt'
        have hquarter_lt_lower : (1 / 4 : ℝ) < (3 / 10 : ℝ) := by
          norm_num
        exact False.elim
          ((not_lt_of_ge hlo)
            (lt_trans hbelow_quarter hquarter_lt_lower))
      · subst e
        have hscale_pos : 0 < (2 : ℝ) ^ (-25 : ℤ) := by
          norm_num [zpow_neg]
        have hscaled_lower :
            (3 / 10 : ℝ) ≤ (m : ℝ) * (2 : ℝ) ^ (-25 : ℤ) := by
          simpa [ieeeSingleFormat, normalizedValue, signValue, betaR] using hlo
        have hmlo : 10066330 ≤ m := by
          by_contra hnot
          have hmle : m ≤ 10066329 := by omega
          have hmbound :
              (m : ℝ) * (2 : ℝ) ^ (-25 : ℤ) ≤
                (10066329 : ℝ) * (2 : ℝ) ^ (-25 : ℤ) :=
            mul_le_mul_of_nonneg_right (Nat.cast_le.mpr hmle)
              (le_of_lt hscale_pos)
          have hbelow :
              (10066329 : ℝ) * (2 : ℝ) ^ (-25 : ℤ) < (3 / 10 : ℝ) := by
            norm_num [zpow_neg]
          exact (not_lt_of_ge hscaled_lower) (lt_of_le_of_lt hmbound hbelow)
        have hmhi : m ≤ 12582912 := by
          have hupper_eq :
              (3 / 8 : ℝ) =
                (12582912 : ℝ) * (2 : ℝ) ^ (-25 : ℤ) := by
            norm_num [zpow_neg]
          have hscaled :
              (m : ℝ) * (2 : ℝ) ^ (-25 : ℤ) ≤
                (12582912 : ℝ) * (2 : ℝ) ^ (-25 : ℤ) := by
            rw [hupper_eq] at hhi
            simpa [ieeeSingleFormat, normalizedValue, signValue, betaR] using hhi
          have hcast : (m : ℝ) ≤ (12582912 : ℝ) :=
            le_of_mul_le_mul_right hscaled hscale_pos
          exact Nat.cast_le.mp hcast
        exact ⟨m, hmlo, hmhi, rfl⟩
      · have hhalf_le :
            (1 / 2 : ℝ) ≤ ieeeSingleFormat.normalizedValue false m e := by
          have hle_exp : (-1 : ℤ) + 1 ≤ e := by
            omega
          have hle :
              ieeeSingleFormat.normalizedValue false
                  ieeeSingleFormat.minNormalMantissa ((-1 : ℤ) + 1) ≤
                ieeeSingleFormat.normalizedValue false m e :=
            ieeeSingleFormat.normalizedValue_false_minNormalMantissa_le_of_exp_le
              (m := m) (e := (-1 : ℤ)) (e' := e) hm hle_exp
          have hle0 :
              ieeeSingleFormat.normalizedValue false
                  ieeeSingleFormat.minNormalMantissa 0 ≤
                ieeeSingleFormat.normalizedValue false m e := by
            simpa using hle
          have hhalf :
              ieeeSingleFormat.normalizedValue false
                  ieeeSingleFormat.minNormalMantissa 0 =
                (1 / 2 : ℝ) := by
            norm_num [ieeeSingleFormat, normalizedValue, signValue, betaR,
              minNormalMantissa, zpow_neg]
          rw [hhalf] at hle0
          exact hle0
        linarith
    · have hneg :
          ieeeSingleFormat.normalizedValue true m e < 0 :=
        ieeeSingleFormat.normalizedValue_true_neg hm
      linarith
  · have hsub_le :
        x ≤ ieeeSingleFormat.minNormalMagnitude :=
      ieeeSingleFormat.subnormalSystem_le_minNormalMagnitude hsub
    have hmin_lt_lower :
        ieeeSingleFormat.minNormalMagnitude < (3 / 10 : ℝ) := by
      have hmin_lt_quarter :
          ieeeSingleFormat.minNormalMagnitude < (1 / 4 : ℝ) := by
        norm_num [ieeeSingleFormat, minNormalMagnitude, betaR, zpow_neg]
      linarith
    linarith

/-- IEEE-double interval-to-mantissa adapter for the complete localized
Problem 2.24 zero branch. -/
theorem problem2_24_ieeeDouble_finiteSystem_zero_branch_exists_neg_one_mantissa
    {x : ℝ}
    (hx : ieeeDoubleFormat.finiteSystem x)
    (hlo : (3 / 10 : ℝ) ≤ x)
    (hhi : x ≤ (3 / 8 : ℝ)) :
    ∃ m : ℕ,
      5404319552844596 ≤ m ∧ m ≤ 6755399441055744 ∧
        x = ieeeDoubleFormat.normalizedValue false m (-1) := by
  rcases hx with hzero | hnorm | hsub
  · subst x
    norm_num at hlo
  · rcases hnorm with ⟨negative, m, e, hm, _he, rfl⟩
    cases negative
    · rcases lt_trichotomy e (-1 : ℤ) with hlt | heq | hgt
      · have hbelow_quarter :
            ieeeDoubleFormat.normalizedValue false m e < (1 / 4 : ℝ) := by
          have hlt' :
              ieeeDoubleFormat.normalizedValue false m e <
                ieeeDoubleFormat.normalizedValue false
                  ieeeDoubleFormat.minNormalMantissa (-1) :=
            ieeeDoubleFormat.normalizedValue_false_lt_of_exp_lt hm
              ieeeDoubleFormat.minNormalMantissa_normalized hlt
          have hquarter :
              ieeeDoubleFormat.normalizedValue false
                  ieeeDoubleFormat.minNormalMantissa (-1) =
                (1 / 4 : ℝ) := by
            norm_num [ieeeDoubleFormat, normalizedValue, signValue, betaR,
              minNormalMantissa, zpow_neg]
          simpa [hquarter] using hlt'
        have hquarter_lt_lower : (1 / 4 : ℝ) < (3 / 10 : ℝ) := by
          norm_num
        exact False.elim
          ((not_lt_of_ge hlo)
            (lt_trans hbelow_quarter hquarter_lt_lower))
      · subst e
        have hscale_pos : 0 < (2 : ℝ) ^ (-54 : ℤ) := by
          norm_num [zpow_neg]
        have hscaled_lower :
            (3 / 10 : ℝ) ≤ (m : ℝ) * (2 : ℝ) ^ (-54 : ℤ) := by
          simpa [ieeeDoubleFormat, normalizedValue, signValue, betaR] using hlo
        have hmlo : 5404319552844596 ≤ m := by
          by_contra hnot
          have hmle : m ≤ 5404319552844595 := by omega
          have hmbound :
              (m : ℝ) * (2 : ℝ) ^ (-54 : ℤ) ≤
                (5404319552844595 : ℝ) * (2 : ℝ) ^ (-54 : ℤ) :=
            mul_le_mul_of_nonneg_right (Nat.cast_le.mpr hmle)
              (le_of_lt hscale_pos)
          have hbelow :
              (5404319552844595 : ℝ) * (2 : ℝ) ^ (-54 : ℤ) < (3 / 10 : ℝ) := by
            norm_num [zpow_neg]
          exact (not_lt_of_ge hscaled_lower) (lt_of_le_of_lt hmbound hbelow)
        have hmhi : m ≤ 6755399441055744 := by
          have hupper_eq :
              (3 / 8 : ℝ) =
                (6755399441055744 : ℝ) * (2 : ℝ) ^ (-54 : ℤ) := by
            norm_num [zpow_neg]
          have hscaled :
              (m : ℝ) * (2 : ℝ) ^ (-54 : ℤ) ≤
                (6755399441055744 : ℝ) * (2 : ℝ) ^ (-54 : ℤ) := by
            rw [hupper_eq] at hhi
            simpa [ieeeDoubleFormat, normalizedValue, signValue, betaR] using hhi
          have hcast : (m : ℝ) ≤ (6755399441055744 : ℝ) :=
            le_of_mul_le_mul_right hscaled hscale_pos
          exact Nat.cast_le.mp hcast
        exact ⟨m, hmlo, hmhi, rfl⟩
      · have hhalf_le :
            (1 / 2 : ℝ) ≤ ieeeDoubleFormat.normalizedValue false m e := by
          have hle_exp : (-1 : ℤ) + 1 ≤ e := by
            omega
          have hle :
              ieeeDoubleFormat.normalizedValue false
                  ieeeDoubleFormat.minNormalMantissa ((-1 : ℤ) + 1) ≤
                ieeeDoubleFormat.normalizedValue false m e :=
            ieeeDoubleFormat.normalizedValue_false_minNormalMantissa_le_of_exp_le
              (m := m) (e := (-1 : ℤ)) (e' := e) hm hle_exp
          have hle0 :
              ieeeDoubleFormat.normalizedValue false
                  ieeeDoubleFormat.minNormalMantissa 0 ≤
                ieeeDoubleFormat.normalizedValue false m e := by
            simpa using hle
          have hhalf :
              ieeeDoubleFormat.normalizedValue false
                  ieeeDoubleFormat.minNormalMantissa 0 =
                (1 / 2 : ℝ) := by
            norm_num [ieeeDoubleFormat, normalizedValue, signValue, betaR,
              minNormalMantissa, zpow_neg]
          rw [hhalf] at hle0
          exact hle0
        linarith
    · have hneg :
          ieeeDoubleFormat.normalizedValue true m e < 0 :=
        ieeeDoubleFormat.normalizedValue_true_neg hm
      linarith
  · have hsub_le :
        x ≤ ieeeDoubleFormat.minNormalMagnitude :=
      ieeeDoubleFormat.subnormalSystem_le_minNormalMagnitude hsub
    have hmin_lt_lower :
        ieeeDoubleFormat.minNormalMagnitude < (3 / 10 : ℝ) := by
      have hmin_lt_quarter :
          ieeeDoubleFormat.minNormalMagnitude < (1 / 4 : ℝ) := by
        have hpow :
            (4 : ℝ) < (2 : ℝ) ^ (1022 : ℕ) := by
          have hpow_lt :
              (2 : ℝ) ^ (2 : ℕ) < (2 : ℝ) ^ (1022 : ℕ) :=
            pow_lt_pow_right₀ (by norm_num : (1 : ℝ) < 2)
              (by norm_num : (2 : ℕ) < 1022)
          norm_num at hpow_lt ⊢
          exact hpow_lt
        simpa [ieeeDoubleFormat, minNormalMagnitude, betaR, zpow_neg] using
          one_div_lt_one_div_of_lt (by norm_num : (0 : ℝ) < 4) hpow
      linarith
    linarith

/-- IEEE-single third-exact representability on the localized zero-branch
interval `[3/10, 3/8]`. -/
theorem problem2_24_ieeeSingle_third_exact_intermediate_finiteSystem_of_finiteSystem_zero_branch
    {x : ℝ}
    (hx : ieeeSingleFormat.finiteSystem x)
    (hlo : (3 / 10 : ℝ) ≤ x)
    (hhi : x ≤ (3 / 8 : ℝ)) :
    ieeeSingleFormat.finiteSystem
      (((x - (1 / 2 : ℝ)) + x) - (1 / 2 : ℝ)) := by
  rcases
      problem2_24_ieeeSingle_finiteSystem_zero_branch_exists_neg_one_mantissa
        hx hlo hhi with
    ⟨m, hmlo, hmhi, rfl⟩
  exact
    problem2_24_ieeeSingle_third_exact_intermediate_finiteSystem_of_neg_one_mantissa_mem_zero_branch
      hmlo hmhi

/-- IEEE-double third-exact representability on the localized zero-branch
interval `[3/10, 3/8]`. -/
theorem problem2_24_ieeeDouble_third_exact_intermediate_finiteSystem_of_finiteSystem_zero_branch
    {x : ℝ}
    (hx : ieeeDoubleFormat.finiteSystem x)
    (hlo : (3 / 10 : ℝ) ≤ x)
    (hhi : x ≤ (3 / 8 : ℝ)) :
    ieeeDoubleFormat.finiteSystem
      (((x - (1 / 2 : ℝ)) + x) - (1 / 2 : ℝ)) := by
  rcases
      problem2_24_ieeeDouble_finiteSystem_zero_branch_exists_neg_one_mantissa
        hx hlo hhi with
    ⟨m, hmlo, hmhi, rfl⟩
  exact
    problem2_24_ieeeDouble_third_exact_intermediate_finiteSystem_of_neg_one_mantissa_mem_zero_branch
      hmlo hmhi

theorem problem2_24_ieeeSingle_one_finiteSystem :
    ieeeSingleFormat.finiteSystem (1 : ℝ) := by
  refine Or.inr (Or.inl ?_)
  refine ⟨false, 8388608, (1 : ℤ), ?_, ?_, ?_⟩
  · norm_num [ieeeSingleFormat, normalizedMantissa, mantissaInRange,
      minNormalMantissa]
  · norm_num [ieeeSingleFormat, exponentInRange]
  · norm_num [ieeeSingleFormat, normalizedValue, signValue, betaR, zpow_neg]
    rfl

theorem problem2_24_ieeeDouble_one_finiteSystem :
    ieeeDoubleFormat.finiteSystem (1 : ℝ) :=
  problem2_10_ieeeDouble_finiteSystem_one

theorem problem2_24_ieeeSingle_subnormalMantissa_one :
    ieeeSingleFormat.subnormalMantissa 1 := by
  norm_num [ieeeSingleFormat, subnormalMantissa, minNormalMantissa]

theorem problem2_24_ieeeDouble_subnormalMantissa_one :
    ieeeDoubleFormat.subnormalMantissa 1 := by
  norm_num [ieeeDoubleFormat, subnormalMantissa, minNormalMantissa]

private theorem problem2_24_ieeeSingleFormat_minNormalMagnitude_le_one_third :
    ieeeSingleFormat.minNormalMagnitude ≤ (1 / 3 : ℝ) := by
  norm_num [ieeeSingleFormat, minNormalMagnitude, betaR, zpow_neg]

private theorem problem2_24_one_le_ieeeSingleFormat_maxFiniteMagnitude :
    (1 : ℝ) ≤ ieeeSingleFormat.maxFiniteMagnitude := by
  rw [maxFiniteMagnitude, ieeeSingleFormat, betaR]
  change (1 : ℝ) ≤ (2 : ℝ) ^ (128 : ℤ) *
    (1 - (2 : ℝ) ^ (-24 : ℤ))
  have hfactor : (1 / 2 : ℝ) ≤ 1 - (2 : ℝ) ^ (-24 : ℤ) := by
    rw [zpow_neg]
    have hden : (2 : ℝ) ≤ (2 : ℝ) ^ (24 : ℕ) := by
      exact le_self_pow₀ (by norm_num : (1 : ℝ) ≤ 2)
        (by norm_num : (24 : ℕ) ≠ 0)
    have hinv : 1 / ((2 : ℝ) ^ (24 : ℕ)) ≤ 1 / (2 : ℝ) :=
      one_div_le_one_div_of_le (by norm_num : (0 : ℝ) < 2) hden
    norm_num at hinv ⊢
  have hpow_nat : (2 : ℝ) ≤ (2 : ℝ) ^ (128 : ℕ) := by
    exact le_self_pow₀ (by norm_num : (1 : ℝ) ≤ 2)
      (by norm_num : (128 : ℕ) ≠ 0)
  have hpow : (2 : ℝ) ≤ (2 : ℝ) ^ (128 : ℤ) := by
    simpa [zpow_natCast] using hpow_nat
  have hmul := mul_le_mul hpow hfactor
    (by norm_num : (0 : ℝ) ≤ (1 / 2 : ℝ))
    (by positivity : (0 : ℝ) ≤ (2 : ℝ) ^ (128 : ℤ))
  simpa using hmul

private theorem problem2_24_ieeeSingle_oneThird_finiteNormalRange :
    ieeeSingleFormat.finiteNormalRange (1 / 3 : ℝ) := by
  rw [finiteNormalRange]
  rw [abs_of_nonneg (by norm_num : (0 : ℝ) ≤ 1 / 3)]
  constructor
  · exact problem2_24_ieeeSingleFormat_minNormalMagnitude_le_one_third
  · exact le_trans (by norm_num : (1 / 3 : ℝ) ≤ 1)
      problem2_24_one_le_ieeeSingleFormat_maxFiniteMagnitude

/-- IEEE-single finite round-to-even sends `1/3` to the upper adjacent
single-precision value. -/
theorem problem2_24_ieeeSingle_oneThird_rounds_to_upper :
    ieeeSingleFormat.finiteRoundToEven (1 / 3 : ℝ) =
      (11184811 : ℝ) * (2 : ℝ) ^ (-25 : ℤ) := by
  let fmt := ieeeSingleFormat
  let a : ℝ := fmt.normalizedValue false 11184810 (-1)
  let b : ℝ := fmt.normalizedValue false 11184811 (-1)
  let x : ℝ := (1 / 3 : ℝ)
  have hm : fmt.normalizedMantissa 11184810 := by
    norm_num [fmt, ieeeSingleFormat, normalizedMantissa, mantissaInRange,
      minNormalMantissa]
  have hmnext : fmt.normalizedMantissa (11184810 + 1) := by
    norm_num [fmt, ieeeSingleFormat, normalizedMantissa, mantissaInRange,
      minNormalMantissa]
  have hadj : fmt.realOrderAdjacentNormalized a b :=
    fmt.realOrderAdjacentNormalized_of_sameExponentAdjacentNormalized
      ⟨false, 11184810, (-1 : ℤ), hm, hmnext, Or.inl ⟨rfl, rfl⟩⟩
  have ha_value :
      a = (11184810 : ℝ) * (2 : ℝ) ^ (-25 : ℤ) := by
    norm_num [a, fmt, ieeeSingleFormat, normalizedValue, signValue, betaR,
      zpow_neg]
  have hb_value :
      b = (11184811 : ℝ) * (2 : ℝ) ^ (-25 : ℤ) := by
    norm_num [b, fmt, ieeeSingleFormat, normalizedValue, signValue, betaR,
      zpow_neg]
  have hstrict : a < x ∧ x < b := by
    rw [ha_value, hb_value]
    norm_num [x, zpow_neg]
  have hpolicy :
      fmt.sourceRoundToEvenEvidence x (fmt.finiteRoundToEven x) :=
    fmt.finiteRoundToEven_sourceRoundToEvenEvidence_of_finiteNormalRange
      problem2_24_ieeeSingle_oneThird_finiteNormalRange
  have hrightCloser : |x - b| < |x - a| := by
    rw [ha_value, hb_value]
    norm_num [x, zpow_neg]
  have hround : fmt.finiteRoundToEven x = b :=
    fmt.sourceRoundToEvenEvidence_eq_right_of_realOrderAdjacent_strict_between_right_closer
      hpolicy hadj hstrict hrightCloser
  simpa [x, fmt, hb_value] using hround

theorem problem2_24_ieeeSingle_one_third_not_finiteSystem :
    ¬ ieeeSingleFormat.finiteSystem (1 / 3 : ℝ) := by
  intro hfin
  have hfix :
      ieeeSingleFormat.finiteRoundToEven (1 / 3 : ℝ) = (1 / 3 : ℝ) :=
    ieeeSingleFormat.finiteRoundToEven_eq_self_of_finiteSystem hfin
  rw [problem2_24_ieeeSingle_oneThird_rounds_to_upper] at hfix
  norm_num [zpow_neg] at hfix

theorem problem2_24_ieeeDouble_one_third_not_finiteSystem :
    ¬ ieeeDoubleFormat.finiteSystem (1 / 3 : ℝ) := by
  intro hfin
  have hfix :
      ieeeDoubleFormat.finiteRoundToEven (1 / 3 : ℝ) = (1 / 3 : ℝ) :=
    ieeeDoubleFormat.finiteRoundToEven_eq_self_of_finiteSystem hfin
  rw [problem2_10_ieeeDouble_oneThird_rounds_to_lower] at hfix
  norm_num [zpow_neg] at hfix

theorem problem2_24_ieeeSingle_finiteSystem_ne_one_third {x : ℝ}
    (hx : ieeeSingleFormat.finiteSystem x) :
    x ≠ (1 / 3 : ℝ) := by
  intro hxthird
  exact problem2_24_ieeeSingle_one_third_not_finiteSystem (by
    simpa [hxthird] using hx)

theorem problem2_24_ieeeDouble_finiteSystem_ne_one_third {x : ℝ}
    (hx : ieeeDoubleFormat.finiteSystem x) :
    x ≠ (1 / 3 : ℝ) := by
  intro hxthird
  exact problem2_24_ieeeDouble_one_third_not_finiteSystem (by
    simpa [hxthird] using hx)

/-- No finite IEEE-single value lies strictly between `1/3` and the adjacent
single value immediately above it. -/
theorem problem2_24_ieeeSingle_upper_neighbor_le_of_finiteSystem_of_one_third_lt
    {x : ℝ}
    (hx : ieeeSingleFormat.finiteSystem x)
    (hgt : (1 / 3 : ℝ) < x) :
    (11184811 : ℝ) * (2 : ℝ) ^ (-25 : ℤ) ≤ x := by
  let a : ℝ := ieeeSingleFormat.normalizedValue false 11184810 (-1)
  let b : ℝ := ieeeSingleFormat.normalizedValue false 11184811 (-1)
  have hm : ieeeSingleFormat.normalizedMantissa 11184810 := by
    norm_num [ieeeSingleFormat, normalizedMantissa, mantissaInRange,
      minNormalMantissa]
  have hmnext : ieeeSingleFormat.normalizedMantissa (11184810 + 1) := by
    norm_num [ieeeSingleFormat, normalizedMantissa, mantissaInRange,
      minNormalMantissa]
  have hadj : ieeeSingleFormat.realOrderAdjacentNormalized a b :=
    ieeeSingleFormat.realOrderAdjacentNormalized_of_sameExponentAdjacentNormalized
      ⟨false, 11184810, (-1 : ℤ), hm, hmnext, Or.inl ⟨rfl, rfl⟩⟩
  have ha_value :
      a = (11184810 : ℝ) * (2 : ℝ) ^ (-25 : ℤ) := by
    norm_num [a, ieeeSingleFormat, normalizedValue, signValue, betaR,
      zpow_neg]
  have hb_value :
      b = (11184811 : ℝ) * (2 : ℝ) ^ (-25 : ℤ) := by
    norm_num [b, ieeeSingleFormat, normalizedValue, signValue, betaR,
      zpow_neg]
  have ha_lt_third : a < (1 / 3 : ℝ) := by
    rw [ha_value]
    norm_num [zpow_neg]
  have hxG : ieeeSingleFormat.unboundedNormalizedSystem x := by
    rcases hx with hzero | hnorm | hsub
    · subst x
      norm_num at hgt
    · exact ieeeSingleFormat.normalizedSystem_unboundedNormalizedSystem hnorm
    · have hsub_le :
          x ≤ ieeeSingleFormat.minNormalMagnitude :=
        ieeeSingleFormat.subnormalSystem_le_minNormalMagnitude hsub
      have hmin_lt_third :
          ieeeSingleFormat.minNormalMagnitude < (1 / 3 : ℝ) := by
        norm_num [ieeeSingleFormat, minNormalMagnitude, betaR, zpow_neg]
      linarith
  by_contra hle
  have hxb : x < b := by
    have hxb' :
        x < (11184811 : ℝ) * (2 : ℝ) ^ (-25 : ℤ) :=
      lt_of_not_ge hle
    rw [hb_value]
    exact hxb'
  exact False.elim
    ((hadj.2.2.2 x hxG) (Or.inl ⟨lt_trans ha_lt_third hgt, hxb⟩))

/-- No finite IEEE-double value lies strictly between `1/3` and the adjacent
double value immediately above it. -/
theorem problem2_24_ieeeDouble_upper_neighbor_le_of_finiteSystem_of_one_third_lt
    {x : ℝ}
    (hx : ieeeDoubleFormat.finiteSystem x)
    (hgt : (1 / 3 : ℝ) < x) :
    (6004799503160662 : ℝ) * (2 : ℝ) ^ (-54 : ℤ) ≤ x := by
  let a : ℝ := ieeeDoubleFormat.normalizedValue false 6004799503160661 (-1)
  let b : ℝ := ieeeDoubleFormat.normalizedValue false 6004799503160662 (-1)
  have hm : ieeeDoubleFormat.normalizedMantissa 6004799503160661 := by
    norm_num [ieeeDoubleFormat, normalizedMantissa, mantissaInRange,
      minNormalMantissa]
  have hmnext : ieeeDoubleFormat.normalizedMantissa (6004799503160661 + 1) := by
    norm_num [ieeeDoubleFormat, normalizedMantissa, mantissaInRange,
      minNormalMantissa]
  have hadj : ieeeDoubleFormat.realOrderAdjacentNormalized a b :=
    ieeeDoubleFormat.realOrderAdjacentNormalized_of_sameExponentAdjacentNormalized
      ⟨false, 6004799503160661, (-1 : ℤ), hm, hmnext, Or.inl ⟨rfl, rfl⟩⟩
  have ha_value :
      a = (6004799503160661 : ℝ) * (2 : ℝ) ^ (-54 : ℤ) := by
    norm_num [a, ieeeDoubleFormat, normalizedValue, signValue, betaR,
      zpow_neg]
  have hb_value :
      b = (6004799503160662 : ℝ) * (2 : ℝ) ^ (-54 : ℤ) := by
    norm_num [b, ieeeDoubleFormat, normalizedValue, signValue, betaR,
      zpow_neg]
  have ha_lt_third : a < (1 / 3 : ℝ) := by
    rw [ha_value]
    norm_num [zpow_neg]
  have hxG : ieeeDoubleFormat.unboundedNormalizedSystem x := by
    rcases hx with hzero | hnorm | hsub
    · subst x
      norm_num at hgt
    · exact ieeeDoubleFormat.normalizedSystem_unboundedNormalizedSystem hnorm
    · have hsub_le :
          x ≤ ieeeDoubleFormat.minNormalMagnitude :=
        ieeeDoubleFormat.subnormalSystem_le_minNormalMagnitude hsub
      have hmin_lt_third :
          ieeeDoubleFormat.minNormalMagnitude < (1 / 3 : ℝ) := by
        have hmin_lt_quarter :
            ieeeDoubleFormat.minNormalMagnitude < (1 / 4 : ℝ) := by
          have hpow :
              (4 : ℝ) < (2 : ℝ) ^ (1022 : ℕ) := by
            have hpow_lt :
                (2 : ℝ) ^ (2 : ℕ) < (2 : ℝ) ^ (1022 : ℕ) :=
              pow_lt_pow_right₀ (by norm_num : (1 : ℝ) < 2)
                (by norm_num : (2 : ℕ) < 1022)
            norm_num at hpow_lt ⊢
            exact hpow_lt
          simpa [ieeeDoubleFormat, minNormalMagnitude, betaR, zpow_neg] using
            one_div_lt_one_div_of_lt (by norm_num : (0 : ℝ) < 4) hpow
        linarith
      linarith
  by_contra hle
  have hxb : x < b := by
    have hxb' :
        x < (6004799503160662 : ℝ) * (2 : ℝ) ^ (-54 : ℤ) :=
      lt_of_not_ge hle
    rw [hb_value]
    exact hxb'
  exact False.elim
    ((hadj.2.2.2 x hxG) (Or.inl ⟨lt_trans ha_lt_third hgt, hxb⟩))

theorem problem2_24_ieeeSingle_upper_neighbor_le_of_finiteSystem_of_one_third_le
    {x : ℝ}
    (hx : ieeeSingleFormat.finiteSystem x)
    (hge : (1 / 3 : ℝ) ≤ x) :
    (11184811 : ℝ) * (2 : ℝ) ^ (-25 : ℤ) ≤ x := by
  have hgt : (1 / 3 : ℝ) < x :=
    lt_of_le_of_ne hge
      (Ne.symm (problem2_24_ieeeSingle_finiteSystem_ne_one_third hx))
  exact
    problem2_24_ieeeSingle_upper_neighbor_le_of_finiteSystem_of_one_third_lt
      hx hgt

theorem problem2_24_ieeeDouble_upper_neighbor_le_of_finiteSystem_of_one_third_le
    {x : ℝ}
    (hx : ieeeDoubleFormat.finiteSystem x)
    (hge : (1 / 3 : ℝ) ≤ x) :
    (6004799503160662 : ℝ) * (2 : ℝ) ^ (-54 : ℤ) ≤ x := by
  have hgt : (1 / 3 : ℝ) < x :=
    lt_of_le_of_ne hge
      (Ne.symm (problem2_24_ieeeDouble_finiteSystem_ne_one_third hx))
  exact
    problem2_24_ieeeDouble_upper_neighbor_le_of_finiteSystem_of_one_third_lt
      hx hgt

theorem problem2_24_ieeeSingle_exactExpr_ne_zero_of_finiteSystem {x : ℝ}
    (hx : ieeeSingleFormat.finiteSystem x) :
    problem2_24_exactExpr x ≠ 0 :=
  problem2_24_exactExpr_ne_zero_of_ne_one_third
    (problem2_24_ieeeSingle_finiteSystem_ne_one_third hx)

theorem problem2_24_ieeeDouble_exactExpr_ne_zero_of_finiteSystem {x : ℝ}
    (hx : ieeeDoubleFormat.finiteSystem x) :
    problem2_24_exactExpr x ≠ 0 :=
  problem2_24_exactExpr_ne_zero_of_ne_one_third
    (problem2_24_ieeeDouble_finiteSystem_ne_one_third hx)

/-- Problem 2.24, exact-intermediate IEEE-single branch. -/
theorem problem2_24_ieeeSingle_eval_ne_zero_of_finiteSystem_intermediates
    {x : ℝ}
    (hx : ieeeSingleFormat.finiteSystem x)
    (h1 : ieeeSingleFormat.finiteSystem (x - (1 / 2 : ℝ)))
    (h2 : ieeeSingleFormat.finiteSystem ((x - (1 / 2 : ℝ)) + x))
    (h3 : ieeeSingleFormat.finiteSystem
      (((x - (1 / 2 : ℝ)) + x) - (1 / 2 : ℝ)))
    (h4 : ieeeSingleFormat.finiteSystem
      ((((x - (1 / 2 : ℝ)) + x) - (1 / 2 : ℝ)) + x)) :
    ieeeSingleFormat.problem2_24_eval x ≠ 0 := by
  refine
    ieeeSingleFormat.problem2_24_eval_ne_zero_of_finiteSystem_intermediates_of_ne_one_third
      ?_ h1 h2 h3 h4
  exact problem2_24_ieeeSingle_finiteSystem_ne_one_third hx

/-- Problem 2.24, exact-intermediate IEEE-double branch. -/
theorem problem2_24_ieeeDouble_eval_ne_zero_of_finiteSystem_intermediates
    {x : ℝ}
    (hx : ieeeDoubleFormat.finiteSystem x)
    (h1 : ieeeDoubleFormat.finiteSystem (x - (1 / 2 : ℝ)))
    (h2 : ieeeDoubleFormat.finiteSystem ((x - (1 / 2 : ℝ)) + x))
    (h3 : ieeeDoubleFormat.finiteSystem
      (((x - (1 / 2 : ℝ)) + x) - (1 / 2 : ℝ)))
    (h4 : ieeeDoubleFormat.finiteSystem
      ((((x - (1 / 2 : ℝ)) + x) - (1 / 2 : ℝ)) + x)) :
    ieeeDoubleFormat.problem2_24_eval x ≠ 0 := by
  refine
    ieeeDoubleFormat.problem2_24_eval_ne_zero_of_finiteSystem_intermediates_of_ne_one_third
      ?_ h1 h2 h3 h4
  exact problem2_24_ieeeDouble_finiteSystem_ne_one_third hx

/-- Problem 2.24, IEEE-single zero-result branch audit.  Any finite single
input producing zero in the modeled path must leave the exact-intermediate
branch at one of the four displayed exact real intermediates. -/
theorem problem2_24_ieeeSingle_eval_eq_zero_implies_exists_nonfinite_exact_intermediate
    {x : ℝ}
    (hx : ieeeSingleFormat.finiteSystem x)
    (hzero : ieeeSingleFormat.problem2_24_eval x = 0) :
    ¬ ieeeSingleFormat.finiteSystem (x - (1 / 2 : ℝ)) ∨
      ¬ ieeeSingleFormat.finiteSystem ((x - (1 / 2 : ℝ)) + x) ∨
      ¬ ieeeSingleFormat.finiteSystem
        (((x - (1 / 2 : ℝ)) + x) - (1 / 2 : ℝ)) ∨
      ¬ ieeeSingleFormat.finiteSystem
        ((((x - (1 / 2 : ℝ)) + x) - (1 / 2 : ℝ)) + x) :=
  ieeeSingleFormat.problem2_24_eval_eq_zero_implies_exists_nonfinite_exact_intermediate_of_ne_one_third
    (problem2_24_ieeeSingle_finiteSystem_ne_one_third hx) hzero

/-- Problem 2.24, IEEE-double zero-result branch audit.  Any finite double
input producing zero in the modeled path must leave the exact-intermediate
branch at one of the four displayed exact real intermediates. -/
theorem problem2_24_ieeeDouble_eval_eq_zero_implies_exists_nonfinite_exact_intermediate
    {x : ℝ}
    (hx : ieeeDoubleFormat.finiteSystem x)
    (hzero : ieeeDoubleFormat.problem2_24_eval x = 0) :
    ¬ ieeeDoubleFormat.finiteSystem (x - (1 / 2 : ℝ)) ∨
      ¬ ieeeDoubleFormat.finiteSystem ((x - (1 / 2 : ℝ)) + x) ∨
      ¬ ieeeDoubleFormat.finiteSystem
        (((x - (1 / 2 : ℝ)) + x) - (1 / 2 : ℝ)) ∨
      ¬ ieeeDoubleFormat.finiteSystem
        ((((x - (1 / 2 : ℝ)) + x) - (1 / 2 : ℝ)) + x) :=
  ieeeDoubleFormat.problem2_24_eval_eq_zero_implies_exists_nonfinite_exact_intermediate_of_ne_one_third
    (problem2_24_ieeeDouble_finiteSystem_ne_one_third hx) hzero

/-- Problem 2.24, IEEE-single narrowed zero-result branch audit.  The first
exact intermediate is finite on every finite zero branch, so any remaining
nonfinite exact-intermediate witness must occur in one of the later three
intermediates. -/
theorem problem2_24_ieeeSingle_eval_eq_zero_implies_later_nonfinite_exact_intermediate
    {x : ℝ}
    (hx : ieeeSingleFormat.finiteSystem x)
    (hzero : ieeeSingleFormat.problem2_24_eval x = 0) :
    ¬ ieeeSingleFormat.finiteSystem ((x - (1 / 2 : ℝ)) + x) ∨
      ¬ ieeeSingleFormat.finiteSystem
        (((x - (1 / 2 : ℝ)) + x) - (1 / 2 : ℝ)) ∨
      ¬ ieeeSingleFormat.finiteSystem
        ((((x - (1 / 2 : ℝ)) + x) - (1 / 2 : ℝ)) + x) :=
  ieeeSingleFormat.problem2_24_eval_eq_zero_implies_later_nonfinite_exact_intermediate_of_finiteSystem_input_of_ne_one_third
    problem2_24_ieeeSingle_subnormalMantissa_one
    problem2_24_ieeeSingle_half_finiteSystem
    hx
    (problem2_24_ieeeSingle_finiteSystem_ne_one_third hx)
    hzero

/-- Problem 2.24, IEEE-double narrowed zero-result branch audit.  The first
exact intermediate is finite on every finite zero branch, so any remaining
nonfinite exact-intermediate witness must occur in one of the later three
intermediates. -/
theorem problem2_24_ieeeDouble_eval_eq_zero_implies_later_nonfinite_exact_intermediate
    {x : ℝ}
    (hx : ieeeDoubleFormat.finiteSystem x)
    (hzero : ieeeDoubleFormat.problem2_24_eval x = 0) :
    ¬ ieeeDoubleFormat.finiteSystem ((x - (1 / 2 : ℝ)) + x) ∨
      ¬ ieeeDoubleFormat.finiteSystem
        (((x - (1 / 2 : ℝ)) + x) - (1 / 2 : ℝ)) ∨
      ¬ ieeeDoubleFormat.finiteSystem
        ((((x - (1 / 2 : ℝ)) + x) - (1 / 2 : ℝ)) + x) :=
  ieeeDoubleFormat.problem2_24_eval_eq_zero_implies_later_nonfinite_exact_intermediate_of_finiteSystem_input_of_ne_one_third
    problem2_24_ieeeDouble_subnormalMantissa_one
    problem2_24_ieeeDouble_half_finiteSystem
    hx
    (problem2_24_ieeeDouble_finiteSystem_ne_one_third hx)
    hzero

/-- Problem 2.24, IEEE-single sharpened zero-result branch audit.  Any finite
single input producing zero must have a nonfinite second or third exact real
intermediate. -/
theorem problem2_24_ieeeSingle_eval_eq_zero_implies_second_or_third_nonfinite_exact_intermediate
    {x : ℝ}
    (hx : ieeeSingleFormat.finiteSystem x)
    (hzero : ieeeSingleFormat.problem2_24_eval x = 0) :
    ¬ ieeeSingleFormat.finiteSystem ((x - (1 / 2 : ℝ)) + x) ∨
      ¬ ieeeSingleFormat.finiteSystem
        (((x - (1 / 2 : ℝ)) + x) - (1 / 2 : ℝ)) :=
  ieeeSingleFormat.problem2_24_eval_eq_zero_implies_second_or_third_nonfinite_exact_intermediate_of_finiteSystem_input_of_ne_one_third
    problem2_24_ieeeSingle_subnormalMantissa_one
    problem2_24_ieeeSingle_half_finiteSystem
    hx
    (problem2_24_ieeeSingle_finiteSystem_ne_one_third hx)
    hzero

/-- Problem 2.24, IEEE-double sharpened zero-result branch audit.  Any finite
double input producing zero must have a nonfinite second or third exact real
intermediate. -/
theorem problem2_24_ieeeDouble_eval_eq_zero_implies_second_or_third_nonfinite_exact_intermediate
    {x : ℝ}
    (hx : ieeeDoubleFormat.finiteSystem x)
    (hzero : ieeeDoubleFormat.problem2_24_eval x = 0) :
    ¬ ieeeDoubleFormat.finiteSystem ((x - (1 / 2 : ℝ)) + x) ∨
      ¬ ieeeDoubleFormat.finiteSystem
        (((x - (1 / 2 : ℝ)) + x) - (1 / 2 : ℝ)) :=
  ieeeDoubleFormat.problem2_24_eval_eq_zero_implies_second_or_third_nonfinite_exact_intermediate_of_finiteSystem_input_of_ne_one_third
    problem2_24_ieeeDouble_subnormalMantissa_one
    problem2_24_ieeeDouble_half_finiteSystem
    hx
    (problem2_24_ieeeDouble_finiteSystem_ne_one_third hx)
    hzero

/-- Problem 2.24, IEEE-single upper-branch sharpening.  In the upper adjacent
finite interval from the value above `1/3` through `3/8`, the second exact real
intermediate is finite, so any finite zero branch must have a nonfinite third
exact real intermediate. -/
theorem problem2_24_ieeeSingle_eval_eq_zero_implies_third_exact_intermediate_nonfinite_of_finiteSystem_upper_branch
    {x : ℝ}
    (hx : ieeeSingleFormat.finiteSystem x)
    (hlo : (11184811 : ℝ) * (2 : ℝ) ^ (-25 : ℤ) ≤ x)
    (hhi : x ≤ (3 / 8 : ℝ))
    (hzero : ieeeSingleFormat.problem2_24_eval x = 0) :
    ¬ ieeeSingleFormat.finiteSystem
      (((x - (1 / 2 : ℝ)) + x) - (1 / 2 : ℝ)) := by
  have hbranch :
      ¬ ieeeSingleFormat.finiteSystem ((x - (1 / 2 : ℝ)) + x) ∨
        ¬ ieeeSingleFormat.finiteSystem
          (((x - (1 / 2 : ℝ)) + x) - (1 / 2 : ℝ)) :=
    problem2_24_ieeeSingle_eval_eq_zero_implies_second_or_third_nonfinite_exact_intermediate
      hx hzero
  have hsecond :
      ieeeSingleFormat.finiteSystem ((x - (1 / 2 : ℝ)) + x) :=
    problem2_24_ieeeSingle_second_exact_intermediate_finiteSystem_of_finiteSystem_upper_branch
      hx hlo hhi
  rcases hbranch with hsecond_bad | hthird
  · exact False.elim (hsecond_bad hsecond)
  · exact hthird

/-- Problem 2.24, IEEE-double upper-branch sharpening.  In the upper adjacent
finite interval from the value above `1/3` through `3/8`, the second exact real
intermediate is finite, so any finite zero branch must have a nonfinite third
exact real intermediate. -/
theorem problem2_24_ieeeDouble_eval_eq_zero_implies_third_exact_intermediate_nonfinite_of_finiteSystem_upper_branch
    {x : ℝ}
    (hx : ieeeDoubleFormat.finiteSystem x)
    (hlo : (6004799503160662 : ℝ) * (2 : ℝ) ^ (-54 : ℤ) ≤ x)
    (hhi : x ≤ (3 / 8 : ℝ))
    (hzero : ieeeDoubleFormat.problem2_24_eval x = 0) :
    ¬ ieeeDoubleFormat.finiteSystem
      (((x - (1 / 2 : ℝ)) + x) - (1 / 2 : ℝ)) := by
  have hbranch :
      ¬ ieeeDoubleFormat.finiteSystem ((x - (1 / 2 : ℝ)) + x) ∨
        ¬ ieeeDoubleFormat.finiteSystem
          (((x - (1 / 2 : ℝ)) + x) - (1 / 2 : ℝ)) :=
    problem2_24_ieeeDouble_eval_eq_zero_implies_second_or_third_nonfinite_exact_intermediate
      hx hzero
  have hsecond :
      ieeeDoubleFormat.finiteSystem ((x - (1 / 2 : ℝ)) + x) :=
    problem2_24_ieeeDouble_second_exact_intermediate_finiteSystem_of_finiteSystem_upper_branch
      hx hlo hhi
  rcases hbranch with hsecond_bad | hthird
  · exact False.elim (hsecond_bad hsecond)
  · exact hthird

/-- Problem 2.24, IEEE-single adjacent branch at or above `1/3`.  Finite
single inputs cannot lie strictly between `1/3` and the adjacent value above
it, so the explicit upper-neighbor theorem applies and forces a nonfinite
third exact real intermediate. -/
theorem problem2_24_ieeeSingle_eval_eq_zero_implies_third_exact_intermediate_nonfinite_of_one_third_le
    {x : ℝ}
    (hx : ieeeSingleFormat.finiteSystem x)
    (hge : (1 / 3 : ℝ) ≤ x)
    (hhi : x ≤ (3 / 8 : ℝ))
    (hzero : ieeeSingleFormat.problem2_24_eval x = 0) :
    ¬ ieeeSingleFormat.finiteSystem
      (((x - (1 / 2 : ℝ)) + x) - (1 / 2 : ℝ)) := by
  have hlo :
      (11184811 : ℝ) * (2 : ℝ) ^ (-25 : ℤ) ≤ x :=
    problem2_24_ieeeSingle_upper_neighbor_le_of_finiteSystem_of_one_third_le
      hx hge
  exact
    problem2_24_ieeeSingle_eval_eq_zero_implies_third_exact_intermediate_nonfinite_of_finiteSystem_upper_branch
      hx hlo hhi hzero

/-- Problem 2.24, IEEE-double adjacent branch at or above `1/3`.  Finite
double inputs cannot lie strictly between `1/3` and the adjacent value above
it, so the explicit upper-neighbor theorem applies and forces a nonfinite
third exact real intermediate. -/
theorem problem2_24_ieeeDouble_eval_eq_zero_implies_third_exact_intermediate_nonfinite_of_one_third_le
    {x : ℝ}
    (hx : ieeeDoubleFormat.finiteSystem x)
    (hge : (1 / 3 : ℝ) ≤ x)
    (hhi : x ≤ (3 / 8 : ℝ))
    (hzero : ieeeDoubleFormat.problem2_24_eval x = 0) :
    ¬ ieeeDoubleFormat.finiteSystem
      (((x - (1 / 2 : ℝ)) + x) - (1 / 2 : ℝ)) := by
  have hlo :
      (6004799503160662 : ℝ) * (2 : ℝ) ^ (-54 : ℤ) ≤ x :=
    problem2_24_ieeeDouble_upper_neighbor_le_of_finiteSystem_of_one_third_le
      hx hge
  exact
    problem2_24_ieeeDouble_eval_eq_zero_implies_third_exact_intermediate_nonfinite_of_finiteSystem_upper_branch
      hx hlo hhi hzero

/-- Problem 2.24, IEEE-single sub-third branch audit.  Below `1/3`, the
first two exact intermediates are finite on any finite zero branch, so the
nonfinite witness must be the third or final exact real intermediate. -/
theorem problem2_24_ieeeSingle_eval_eq_zero_implies_last_two_nonfinite_exact_intermediate_of_lt_one_third
    {x : ℝ}
    (hx : ieeeSingleFormat.finiteSystem x)
    (hxlt_third : x < (1 / 3 : ℝ))
    (hzero : ieeeSingleFormat.problem2_24_eval x = 0) :
    ¬ ieeeSingleFormat.finiteSystem
        (((x - (1 / 2 : ℝ)) + x) - (1 / 2 : ℝ)) ∨
      ¬ ieeeSingleFormat.finiteSystem
        ((((x - (1 / 2 : ℝ)) + x) - (1 / 2 : ℝ)) + x) :=
  ieeeSingleFormat.problem2_24_eval_eq_zero_implies_last_two_nonfinite_exact_intermediate_of_finiteSystem_input_of_lt_one_third
    problem2_24_ieeeSingle_subnormalMantissa_one
    problem2_24_ieeeSingle_half_finiteSystem
    hx
    hxlt_third
    hzero

/-- Problem 2.24, IEEE-double sub-third branch audit.  Below `1/3`, the
first two exact intermediates are finite on any finite zero branch, so the
nonfinite witness must be the third or final exact real intermediate. -/
theorem problem2_24_ieeeDouble_eval_eq_zero_implies_last_two_nonfinite_exact_intermediate_of_lt_one_third
    {x : ℝ}
    (hx : ieeeDoubleFormat.finiteSystem x)
    (hxlt_third : x < (1 / 3 : ℝ))
    (hzero : ieeeDoubleFormat.problem2_24_eval x = 0) :
    ¬ ieeeDoubleFormat.finiteSystem
        (((x - (1 / 2 : ℝ)) + x) - (1 / 2 : ℝ)) ∨
      ¬ ieeeDoubleFormat.finiteSystem
        ((((x - (1 / 2 : ℝ)) + x) - (1 / 2 : ℝ)) + x) :=
  ieeeDoubleFormat.problem2_24_eval_eq_zero_implies_last_two_nonfinite_exact_intermediate_of_finiteSystem_input_of_lt_one_third
    problem2_24_ieeeDouble_subnormalMantissa_one
    problem2_24_ieeeDouble_half_finiteSystem
    hx
    hxlt_third
    hzero

/-- Problem 2.24, IEEE-single sub-third branch sharpening.  Below `1/3`, any
finite zero branch must have a nonfinite third exact real intermediate. -/
theorem problem2_24_ieeeSingle_eval_eq_zero_implies_third_exact_intermediate_nonfinite_of_lt_one_third
    {x : ℝ}
    (hx : ieeeSingleFormat.finiteSystem x)
    (hxlt_third : x < (1 / 3 : ℝ))
    (hzero : ieeeSingleFormat.problem2_24_eval x = 0) :
    ¬ ieeeSingleFormat.finiteSystem
      (((x - (1 / 2 : ℝ)) + x) - (1 / 2 : ℝ)) :=
  ieeeSingleFormat.problem2_24_eval_eq_zero_implies_third_exact_intermediate_nonfinite_of_finiteSystem_input_of_lt_one_third
    problem2_24_ieeeSingle_subnormalMantissa_one
    problem2_24_ieeeSingle_half_finiteSystem
    hx
    hxlt_third
    hzero

/-- Problem 2.24, IEEE-double sub-third branch sharpening.  Below `1/3`, any
finite zero branch must have a nonfinite third exact real intermediate. -/
theorem problem2_24_ieeeDouble_eval_eq_zero_implies_third_exact_intermediate_nonfinite_of_lt_one_third
    {x : ℝ}
    (hx : ieeeDoubleFormat.finiteSystem x)
    (hxlt_third : x < (1 / 3 : ℝ))
    (hzero : ieeeDoubleFormat.problem2_24_eval x = 0) :
    ¬ ieeeDoubleFormat.finiteSystem
      (((x - (1 / 2 : ℝ)) + x) - (1 / 2 : ℝ)) :=
  ieeeDoubleFormat.problem2_24_eval_eq_zero_implies_third_exact_intermediate_nonfinite_of_finiteSystem_input_of_lt_one_third
    problem2_24_ieeeDouble_subnormalMantissa_one
    problem2_24_ieeeDouble_half_finiteSystem
    hx
    hxlt_third
    hzero

/-- Problem 2.24, IEEE-single zero-branch sharpening.  Any finite single input
that evaluates to zero in the modeled path must have a nonfinite third exact
real intermediate. -/
theorem problem2_24_ieeeSingle_eval_eq_zero_implies_third_exact_intermediate_nonfinite
    {x : ℝ}
    (hx : ieeeSingleFormat.finiteSystem x)
    (hzero : ieeeSingleFormat.problem2_24_eval x = 0) :
    ¬ ieeeSingleFormat.finiteSystem
      (((x - (1 / 2 : ℝ)) + x) - (1 / 2 : ℝ)) := by
  have hhi : x ≤ (3 / 8 : ℝ) :=
    ieeeSingleFormat.problem2_24_eval_eq_zero_input_le_three_eighths_of_finiteSystem_input
      problem2_24_ieeeSingle_subnormalMantissa_one
      problem2_24_ieeeSingle_half_finiteSystem
      (ieeeSingleFormat.finiteSystem_neg
        problem2_24_ieeeSingle_three_eighths_finiteSystem)
      hx hzero
  by_cases hxlt : x < (1 / 3 : ℝ)
  · exact
      problem2_24_ieeeSingle_eval_eq_zero_implies_third_exact_intermediate_nonfinite_of_lt_one_third
        hx hxlt hzero
  · exact
      problem2_24_ieeeSingle_eval_eq_zero_implies_third_exact_intermediate_nonfinite_of_one_third_le
        hx (le_of_not_gt hxlt) hhi hzero

/-- Problem 2.24, IEEE-double zero-branch sharpening.  Any finite double input
that evaluates to zero in the modeled path must have a nonfinite third exact
real intermediate. -/
theorem problem2_24_ieeeDouble_eval_eq_zero_implies_third_exact_intermediate_nonfinite
    {x : ℝ}
    (hx : ieeeDoubleFormat.finiteSystem x)
    (hzero : ieeeDoubleFormat.problem2_24_eval x = 0) :
    ¬ ieeeDoubleFormat.finiteSystem
      (((x - (1 / 2 : ℝ)) + x) - (1 / 2 : ℝ)) := by
  have hhi : x ≤ (3 / 8 : ℝ) :=
    ieeeDoubleFormat.problem2_24_eval_eq_zero_input_le_three_eighths_of_finiteSystem_input
      problem2_24_ieeeDouble_subnormalMantissa_one
      problem2_24_ieeeDouble_half_finiteSystem
      (ieeeDoubleFormat.finiteSystem_neg
        problem2_24_ieeeDouble_three_eighths_finiteSystem)
      hx hzero
  by_cases hxlt : x < (1 / 3 : ℝ)
  · exact
      problem2_24_ieeeDouble_eval_eq_zero_implies_third_exact_intermediate_nonfinite_of_lt_one_third
        hx hxlt hzero
  · exact
      problem2_24_ieeeDouble_eval_eq_zero_implies_third_exact_intermediate_nonfinite_of_one_third_le
        hx (le_of_not_gt hxlt) hhi hzero

/-- Problem 2.24, modeled finite IEEE-single path.  No finite single input
can evaluate to zero in the finite round-to-even model. -/
theorem problem2_24_ieeeSingle_eval_ne_zero_of_finiteSystem_input
    {x : ℝ}
    (hx : ieeeSingleFormat.finiteSystem x) :
    ieeeSingleFormat.problem2_24_eval x ≠ 0 := by
  intro hzero
  have hthird_nonfinite :
      ¬ ieeeSingleFormat.finiteSystem
        (((x - (1 / 2 : ℝ)) + x) - (1 / 2 : ℝ)) :=
    problem2_24_ieeeSingle_eval_eq_zero_implies_third_exact_intermediate_nonfinite
      hx hzero
  have hlo : (3 / 10 : ℝ) ≤ x :=
    ieeeSingleFormat.problem2_24_eval_eq_zero_input_ge_three_tenths_of_finiteSystem_input
      problem2_24_ieeeSingle_subnormalMantissa_one
      problem2_24_ieeeSingle_half_finiteSystem
      hx hzero
  have hhi : x ≤ (3 / 8 : ℝ) :=
    ieeeSingleFormat.problem2_24_eval_eq_zero_input_le_three_eighths_of_finiteSystem_input
      problem2_24_ieeeSingle_subnormalMantissa_one
      problem2_24_ieeeSingle_half_finiteSystem
      (ieeeSingleFormat.finiteSystem_neg
        problem2_24_ieeeSingle_three_eighths_finiteSystem)
      hx hzero
  have hthird_finite :
      ieeeSingleFormat.finiteSystem
        (((x - (1 / 2 : ℝ)) + x) - (1 / 2 : ℝ)) :=
    problem2_24_ieeeSingle_third_exact_intermediate_finiteSystem_of_finiteSystem_zero_branch
      hx hlo hhi
  exact hthird_nonfinite hthird_finite

/-- Problem 2.24, modeled finite IEEE-double path.  No finite double input
can evaluate to zero in the finite round-to-even model. -/
theorem problem2_24_ieeeDouble_eval_ne_zero_of_finiteSystem_input
    {x : ℝ}
    (hx : ieeeDoubleFormat.finiteSystem x) :
    ieeeDoubleFormat.problem2_24_eval x ≠ 0 := by
  intro hzero
  have hthird_nonfinite :
      ¬ ieeeDoubleFormat.finiteSystem
        (((x - (1 / 2 : ℝ)) + x) - (1 / 2 : ℝ)) :=
    problem2_24_ieeeDouble_eval_eq_zero_implies_third_exact_intermediate_nonfinite
      hx hzero
  have hlo : (3 / 10 : ℝ) ≤ x :=
    ieeeDoubleFormat.problem2_24_eval_eq_zero_input_ge_three_tenths_of_finiteSystem_input
      problem2_24_ieeeDouble_subnormalMantissa_one
      problem2_24_ieeeDouble_half_finiteSystem
      hx hzero
  have hhi : x ≤ (3 / 8 : ℝ) :=
    ieeeDoubleFormat.problem2_24_eval_eq_zero_input_le_three_eighths_of_finiteSystem_input
      problem2_24_ieeeDouble_subnormalMantissa_one
      problem2_24_ieeeDouble_half_finiteSystem
      (ieeeDoubleFormat.finiteSystem_neg
        problem2_24_ieeeDouble_three_eighths_finiteSystem)
      hx hzero
  have hthird_finite :
      ieeeDoubleFormat.finiteSystem
        (((x - (1 / 2 : ℝ)) + x) - (1 / 2 : ℝ)) :=
    problem2_24_ieeeDouble_third_exact_intermediate_finiteSystem_of_finiteSystem_zero_branch
      hx hlo hhi
  exact hthird_nonfinite hthird_finite

/-- Problem 2.24, IEEE-single zero-result final-sum sharpening. -/
theorem problem2_24_ieeeSingle_eval_eq_zero_last_sum_abs_le_half_minSubnormalMagnitude
    {x : ℝ}
    (hzero : ieeeSingleFormat.problem2_24_eval x = 0) :
    |ieeeSingleFormat.problem2_24_y3 x + x| ≤
      (1 / 2 : ℝ) * ieeeSingleFormat.minSubnormalMagnitude :=
  ieeeSingleFormat.problem2_24_eval_eq_zero_last_sum_abs_le_half_minSubnormalMagnitude
    problem2_24_ieeeSingle_subnormalMantissa_one hzero

/-- Problem 2.24, IEEE-double zero-result final-sum sharpening. -/
theorem problem2_24_ieeeDouble_eval_eq_zero_last_sum_abs_le_half_minSubnormalMagnitude
    {x : ℝ}
    (hzero : ieeeDoubleFormat.problem2_24_eval x = 0) :
    |ieeeDoubleFormat.problem2_24_y3 x + x| ≤
      (1 / 2 : ℝ) * ieeeDoubleFormat.minSubnormalMagnitude :=
  ieeeDoubleFormat.problem2_24_eval_eq_zero_last_sum_abs_le_half_minSubnormalMagnitude
    problem2_24_ieeeDouble_subnormalMantissa_one hzero

/-- Problem 2.24, IEEE-single zero-result exact-cancellation audit. -/
theorem problem2_24_ieeeSingle_eval_eq_zero_last_sum_eq_zero_of_finiteSystem_input
    {x : ℝ}
    (hx : ieeeSingleFormat.finiteSystem x)
    (hzero : ieeeSingleFormat.problem2_24_eval x = 0) :
    ieeeSingleFormat.problem2_24_y3 x + x = 0 :=
  ieeeSingleFormat.problem2_24_eval_eq_zero_last_sum_eq_zero_of_finiteSystem_input
    problem2_24_ieeeSingle_subnormalMantissa_one hx hzero

/-- Problem 2.24, IEEE-double zero-result exact-cancellation audit. -/
theorem problem2_24_ieeeDouble_eval_eq_zero_last_sum_eq_zero_of_finiteSystem_input
    {x : ℝ}
    (hx : ieeeDoubleFormat.finiteSystem x)
    (hzero : ieeeDoubleFormat.problem2_24_eval x = 0) :
    ieeeDoubleFormat.problem2_24_y3 x + x = 0 :=
  ieeeDoubleFormat.problem2_24_eval_eq_zero_last_sum_eq_zero_of_finiteSystem_input
    problem2_24_ieeeDouble_subnormalMantissa_one hx hzero

/-- Problem 2.24, IEEE-single zero-result third-intermediate cancellation
audit. -/
theorem problem2_24_ieeeSingle_y3_eq_neg_x_of_eval_eq_zero_of_finiteSystem_input
    {x : ℝ}
    (hx : ieeeSingleFormat.finiteSystem x)
    (hzero : ieeeSingleFormat.problem2_24_eval x = 0) :
    ieeeSingleFormat.problem2_24_y3 x = -x :=
  ieeeSingleFormat.problem2_24_y3_eq_neg_x_of_eval_eq_zero_of_finiteSystem_input
    problem2_24_ieeeSingle_subnormalMantissa_one hx hzero

/-- Problem 2.24, IEEE-double zero-result third-intermediate cancellation
audit. -/
theorem problem2_24_ieeeDouble_y3_eq_neg_x_of_eval_eq_zero_of_finiteSystem_input
    {x : ℝ}
    (hx : ieeeDoubleFormat.finiteSystem x)
    (hzero : ieeeDoubleFormat.problem2_24_eval x = 0) :
    ieeeDoubleFormat.problem2_24_y3 x = -x :=
  ieeeDoubleFormat.problem2_24_y3_eq_neg_x_of_eval_eq_zero_of_finiteSystem_input
    problem2_24_ieeeDouble_subnormalMantissa_one hx hzero

/-- Problem 2.24, IEEE-single zero-result combined branch audit: a finite input
counterexample would need exact final cancellation and one of the source exact
intermediates to leave the finite system. -/
theorem problem2_24_ieeeSingle_eval_eq_zero_implies_y3_eq_neg_x_and_exists_nonfinite_exact_intermediate
    {x : ℝ}
    (hx : ieeeSingleFormat.finiteSystem x)
    (hzero : ieeeSingleFormat.problem2_24_eval x = 0) :
    ieeeSingleFormat.problem2_24_y3 x = -x ∧
      (¬ ieeeSingleFormat.finiteSystem (x - (1 / 2 : ℝ)) ∨
        ¬ ieeeSingleFormat.finiteSystem ((x - (1 / 2 : ℝ)) + x) ∨
        ¬ ieeeSingleFormat.finiteSystem
          (((x - (1 / 2 : ℝ)) + x) - (1 / 2 : ℝ)) ∨
        ¬ ieeeSingleFormat.finiteSystem
          ((((x - (1 / 2 : ℝ)) + x) - (1 / 2 : ℝ)) + x)) :=
  ⟨problem2_24_ieeeSingle_y3_eq_neg_x_of_eval_eq_zero_of_finiteSystem_input
      hx hzero,
    problem2_24_ieeeSingle_eval_eq_zero_implies_exists_nonfinite_exact_intermediate
      hx hzero⟩

/-- Problem 2.24, IEEE-double zero-result combined branch audit: a finite input
counterexample would need exact final cancellation and one of the source exact
intermediates to leave the finite system. -/
theorem problem2_24_ieeeDouble_eval_eq_zero_implies_y3_eq_neg_x_and_exists_nonfinite_exact_intermediate
    {x : ℝ}
    (hx : ieeeDoubleFormat.finiteSystem x)
    (hzero : ieeeDoubleFormat.problem2_24_eval x = 0) :
    ieeeDoubleFormat.problem2_24_y3 x = -x ∧
      (¬ ieeeDoubleFormat.finiteSystem (x - (1 / 2 : ℝ)) ∨
        ¬ ieeeDoubleFormat.finiteSystem ((x - (1 / 2 : ℝ)) + x) ∨
        ¬ ieeeDoubleFormat.finiteSystem
          (((x - (1 / 2 : ℝ)) + x) - (1 / 2 : ℝ)) ∨
        ¬ ieeeDoubleFormat.finiteSystem
          ((((x - (1 / 2 : ℝ)) + x) - (1 / 2 : ℝ)) + x)) :=
  ⟨problem2_24_ieeeDouble_y3_eq_neg_x_of_eval_eq_zero_of_finiteSystem_input
      hx hzero,
    problem2_24_ieeeDouble_eval_eq_zero_implies_exists_nonfinite_exact_intermediate
      hx hzero⟩

/-- Problem 2.24, IEEE-single exact-cancellation third-step nearestness audit. -/
theorem problem2_24_ieeeSingle_eval_eq_zero_last_sub_distance_to_y2_le_half_of_finiteSystem_input
    {x : ℝ}
    (hx : ieeeSingleFormat.finiteSystem x)
    (hzero : ieeeSingleFormat.problem2_24_eval x = 0) :
    |ieeeSingleFormat.problem2_24_y2 x + x - (1 / 2 : ℝ)| ≤
      (1 / 2 : ℝ) :=
  ieeeSingleFormat.problem2_24_eval_eq_zero_last_sub_distance_to_y2_le_half_of_finiteSystem_input
    problem2_24_ieeeSingle_subnormalMantissa_one hx hzero

/-- Problem 2.24, IEEE-double exact-cancellation third-step nearestness audit. -/
theorem problem2_24_ieeeDouble_eval_eq_zero_last_sub_distance_to_y2_le_half_of_finiteSystem_input
    {x : ℝ}
    (hx : ieeeDoubleFormat.finiteSystem x)
    (hzero : ieeeDoubleFormat.problem2_24_eval x = 0) :
    |ieeeDoubleFormat.problem2_24_y2 x + x - (1 / 2 : ℝ)| ≤
      (1 / 2 : ℝ) :=
  ieeeDoubleFormat.problem2_24_eval_eq_zero_last_sub_distance_to_y2_le_half_of_finiteSystem_input
    problem2_24_ieeeDouble_subnormalMantissa_one hx hzero

/-- Problem 2.24, IEEE-single third-step product constraint for zero
counterexamples. -/
theorem problem2_24_ieeeSingle_eval_eq_zero_last_sub_distance_to_zero_product_le_of_finiteSystem_input
    {x : ℝ}
    (hx : ieeeSingleFormat.finiteSystem x)
    (hzero : ieeeSingleFormat.problem2_24_eval x = 0) :
    x * (2 * ieeeSingleFormat.problem2_24_y2 x + x - 1) ≤ 0 :=
  ieeeSingleFormat.problem2_24_eval_eq_zero_last_sub_distance_to_zero_product_le_of_finiteSystem_input
    problem2_24_ieeeSingle_subnormalMantissa_one hx hzero

/-- Problem 2.24, IEEE-double third-step product constraint for zero
counterexamples. -/
theorem problem2_24_ieeeDouble_eval_eq_zero_last_sub_distance_to_zero_product_le_of_finiteSystem_input
    {x : ℝ}
    (hx : ieeeDoubleFormat.finiteSystem x)
    (hzero : ieeeDoubleFormat.problem2_24_eval x = 0) :
    x * (2 * ieeeDoubleFormat.problem2_24_y2 x + x - 1) ≤ 0 :=
  ieeeDoubleFormat.problem2_24_eval_eq_zero_last_sub_distance_to_zero_product_le_of_finiteSystem_input
    problem2_24_ieeeDouble_subnormalMantissa_one hx hzero

/-- Problem 2.24, IEEE-single positive-input third-step `y2` bound. -/
theorem problem2_24_ieeeSingle_eval_eq_zero_last_sub_y2_bound_of_pos_finiteSystem_input
    {x : ℝ}
    (hx : ieeeSingleFormat.finiteSystem x)
    (hzero : ieeeSingleFormat.problem2_24_eval x = 0)
    (hxpos : 0 < x) :
    2 * ieeeSingleFormat.problem2_24_y2 x + x ≤ 1 :=
  ieeeSingleFormat.problem2_24_eval_eq_zero_last_sub_y2_bound_of_pos_finiteSystem_input
    problem2_24_ieeeSingle_subnormalMantissa_one hx hzero hxpos

/-- Problem 2.24, IEEE-double positive-input third-step `y2` bound. -/
theorem problem2_24_ieeeDouble_eval_eq_zero_last_sub_y2_bound_of_pos_finiteSystem_input
    {x : ℝ}
    (hx : ieeeDoubleFormat.finiteSystem x)
    (hzero : ieeeDoubleFormat.problem2_24_eval x = 0)
    (hxpos : 0 < x) :
    2 * ieeeDoubleFormat.problem2_24_y2 x + x ≤ 1 :=
  ieeeDoubleFormat.problem2_24_eval_eq_zero_last_sub_y2_bound_of_pos_finiteSystem_input
    problem2_24_ieeeDouble_subnormalMantissa_one hx hzero hxpos

/-- Problem 2.24, IEEE-single zero-result input-range audit. -/
theorem problem2_24_ieeeSingle_eval_eq_zero_input_mem_unit_interval_of_finiteSystem_input
    {x : ℝ}
    (hx : ieeeSingleFormat.finiteSystem x)
    (hzero : ieeeSingleFormat.problem2_24_eval x = 0) :
    0 ≤ x ∧ x ≤ 1 :=
  ieeeSingleFormat.problem2_24_eval_eq_zero_input_mem_unit_interval_of_finiteSystem_input
    problem2_24_ieeeSingle_subnormalMantissa_one hx hzero

/-- Problem 2.24, IEEE-double zero-result input-range audit. -/
theorem problem2_24_ieeeDouble_eval_eq_zero_input_mem_unit_interval_of_finiteSystem_input
    {x : ℝ}
    (hx : ieeeDoubleFormat.finiteSystem x)
    (hzero : ieeeDoubleFormat.problem2_24_eval x = 0) :
    0 ≤ x ∧ x ≤ 1 :=
  ieeeDoubleFormat.problem2_24_eval_eq_zero_input_mem_unit_interval_of_finiteSystem_input
    problem2_24_ieeeDouble_subnormalMantissa_one hx hzero

/-- Problem 2.24, IEEE-single upper-half exclusion for finite inputs. -/
theorem problem2_24_ieeeSingle_eval_ne_zero_of_finiteSystem_input_of_half_le
    {x : ℝ}
    (hx : ieeeSingleFormat.finiteSystem x)
    (hxhalf : (1 / 2 : ℝ) ≤ x) :
    ieeeSingleFormat.problem2_24_eval x ≠ 0 :=
  ieeeSingleFormat.problem2_24_eval_ne_zero_of_finiteSystem_input_of_half_le
    problem2_24_ieeeSingle_subnormalMantissa_one hx hxhalf

/-- Problem 2.24, IEEE-double upper-half exclusion for finite inputs. -/
theorem problem2_24_ieeeDouble_eval_ne_zero_of_finiteSystem_input_of_half_le
    {x : ℝ}
    (hx : ieeeDoubleFormat.finiteSystem x)
    (hxhalf : (1 / 2 : ℝ) ≤ x) :
    ieeeDoubleFormat.problem2_24_eval x ≠ 0 :=
  ieeeDoubleFormat.problem2_24_eval_ne_zero_of_finiteSystem_input_of_half_le
    problem2_24_ieeeDouble_subnormalMantissa_one hx hxhalf

/-- Problem 2.24, IEEE-single endpoint exclusion for `x = 0`. -/
theorem problem2_24_ieeeSingle_eval_zero_ne_zero :
    ieeeSingleFormat.problem2_24_eval 0 ≠ 0 :=
  ieeeSingleFormat.problem2_24_eval_zero_ne_zero_of_half_and_one_finiteSystem
    problem2_24_ieeeSingle_half_finiteSystem
    problem2_24_ieeeSingle_one_finiteSystem

/-- Problem 2.24, IEEE-double endpoint exclusion for `x = 0`. -/
theorem problem2_24_ieeeDouble_eval_zero_ne_zero :
    ieeeDoubleFormat.problem2_24_eval 0 ≠ 0 :=
  ieeeDoubleFormat.problem2_24_eval_zero_ne_zero_of_half_and_one_finiteSystem
    problem2_24_ieeeDouble_half_finiteSystem
    problem2_24_ieeeDouble_one_finiteSystem

/-- Problem 2.24, IEEE-single strict positivity of finite zero counterexamples. -/
theorem problem2_24_ieeeSingle_eval_eq_zero_input_pos_of_finiteSystem_input
    {x : ℝ}
    (hx : ieeeSingleFormat.finiteSystem x)
    (hzero : ieeeSingleFormat.problem2_24_eval x = 0) :
    0 < x :=
  ieeeSingleFormat.problem2_24_eval_eq_zero_input_pos_of_finiteSystem_input
    problem2_24_ieeeSingle_subnormalMantissa_one
    problem2_24_ieeeSingle_half_finiteSystem
    problem2_24_ieeeSingle_one_finiteSystem hx hzero

/-- Problem 2.24, IEEE-double strict positivity of finite zero counterexamples. -/
theorem problem2_24_ieeeDouble_eval_eq_zero_input_pos_of_finiteSystem_input
    {x : ℝ}
    (hx : ieeeDoubleFormat.finiteSystem x)
    (hzero : ieeeDoubleFormat.problem2_24_eval x = 0) :
    0 < x :=
  ieeeDoubleFormat.problem2_24_eval_eq_zero_input_pos_of_finiteSystem_input
    problem2_24_ieeeDouble_subnormalMantissa_one
    problem2_24_ieeeDouble_half_finiteSystem
    problem2_24_ieeeDouble_one_finiteSystem hx hzero

/-- Problem 2.24, IEEE-single lower-half localization for finite zero
counterexamples. -/
theorem problem2_24_ieeeSingle_eval_eq_zero_input_mem_open_lower_half_of_finiteSystem_input
    {x : ℝ}
    (hx : ieeeSingleFormat.finiteSystem x)
    (hzero : ieeeSingleFormat.problem2_24_eval x = 0) :
    0 < x ∧ x < (1 / 2 : ℝ) :=
  ieeeSingleFormat.problem2_24_eval_eq_zero_input_mem_open_lower_half_of_finiteSystem_input
    problem2_24_ieeeSingle_subnormalMantissa_one
    problem2_24_ieeeSingle_half_finiteSystem
    problem2_24_ieeeSingle_one_finiteSystem hx hzero

/-- Problem 2.24, IEEE-double lower-half localization for finite zero
counterexamples. -/
theorem problem2_24_ieeeDouble_eval_eq_zero_input_mem_open_lower_half_of_finiteSystem_input
    {x : ℝ}
    (hx : ieeeDoubleFormat.finiteSystem x)
    (hzero : ieeeDoubleFormat.problem2_24_eval x = 0) :
    0 < x ∧ x < (1 / 2 : ℝ) :=
  ieeeDoubleFormat.problem2_24_eval_eq_zero_input_mem_open_lower_half_of_finiteSystem_input
    problem2_24_ieeeDouble_subnormalMantissa_one
    problem2_24_ieeeDouble_half_finiteSystem
    problem2_24_ieeeDouble_one_finiteSystem hx hzero

/-- Problem 2.24, IEEE-single `[1/10,1/2)` localization for finite zero
counterexamples. -/
theorem problem2_24_ieeeSingle_eval_eq_zero_input_mem_tenth_to_half_of_finiteSystem_input
    {x : ℝ}
    (hx : ieeeSingleFormat.finiteSystem x)
    (hzero : ieeeSingleFormat.problem2_24_eval x = 0) :
    (1 / 10 : ℝ) ≤ x ∧ x < (1 / 2 : ℝ) :=
  ieeeSingleFormat.problem2_24_eval_eq_zero_input_mem_tenth_to_half_of_finiteSystem_input
    problem2_24_ieeeSingle_subnormalMantissa_one
    problem2_24_ieeeSingle_half_finiteSystem
    problem2_24_ieeeSingle_one_finiteSystem hx hzero

/-- Problem 2.24, IEEE-double `[1/10,1/2)` localization for finite zero
counterexamples. -/
theorem problem2_24_ieeeDouble_eval_eq_zero_input_mem_tenth_to_half_of_finiteSystem_input
    {x : ℝ}
    (hx : ieeeDoubleFormat.finiteSystem x)
    (hzero : ieeeDoubleFormat.problem2_24_eval x = 0) :
    (1 / 10 : ℝ) ≤ x ∧ x < (1 / 2 : ℝ) :=
  ieeeDoubleFormat.problem2_24_eval_eq_zero_input_mem_tenth_to_half_of_finiteSystem_input
    problem2_24_ieeeDouble_subnormalMantissa_one
    problem2_24_ieeeDouble_half_finiteSystem
    problem2_24_ieeeDouble_one_finiteSystem hx hzero

/-- Problem 2.24, IEEE-single `[1/6,1/2)` localization for finite zero
counterexamples. -/
theorem problem2_24_ieeeSingle_eval_eq_zero_input_mem_one_six_to_half_of_finiteSystem_input
    {x : ℝ}
    (hx : ieeeSingleFormat.finiteSystem x)
    (hzero : ieeeSingleFormat.problem2_24_eval x = 0) :
    (1 / 6 : ℝ) ≤ x ∧ x < (1 / 2 : ℝ) :=
  ieeeSingleFormat.problem2_24_eval_eq_zero_input_mem_one_six_to_half_of_finiteSystem_input
    problem2_24_ieeeSingle_subnormalMantissa_one
    problem2_24_ieeeSingle_half_finiteSystem
    problem2_24_ieeeSingle_one_finiteSystem hx hzero

/-- Problem 2.24, IEEE-double `[1/6,1/2)` localization for finite zero
counterexamples. -/
theorem problem2_24_ieeeDouble_eval_eq_zero_input_mem_one_six_to_half_of_finiteSystem_input
    {x : ℝ}
    (hx : ieeeDoubleFormat.finiteSystem x)
    (hzero : ieeeDoubleFormat.problem2_24_eval x = 0) :
    (1 / 6 : ℝ) ≤ x ∧ x < (1 / 2 : ℝ) :=
  ieeeDoubleFormat.problem2_24_eval_eq_zero_input_mem_one_six_to_half_of_finiteSystem_input
    problem2_24_ieeeDouble_subnormalMantissa_one
    problem2_24_ieeeDouble_half_finiteSystem
    problem2_24_ieeeDouble_one_finiteSystem hx hzero

/-- Problem 2.24, IEEE-single `[9/34,1/2)` localization for finite zero
counterexamples. -/
theorem problem2_24_ieeeSingle_eval_eq_zero_input_mem_nine_thirty_four_to_half_of_finiteSystem_input
    {x : ℝ}
    (hx : ieeeSingleFormat.finiteSystem x)
    (hzero : ieeeSingleFormat.problem2_24_eval x = 0) :
    (9 / 34 : ℝ) ≤ x ∧ x < (1 / 2 : ℝ) :=
  ieeeSingleFormat.problem2_24_eval_eq_zero_input_mem_nine_thirty_four_to_half_of_finiteSystem_input
    problem2_24_ieeeSingle_subnormalMantissa_one
    problem2_24_ieeeSingle_half_finiteSystem
    problem2_24_ieeeSingle_one_finiteSystem hx hzero

/-- Problem 2.24, IEEE-double `[9/34,1/2)` localization for finite zero
counterexamples. -/
theorem problem2_24_ieeeDouble_eval_eq_zero_input_mem_nine_thirty_four_to_half_of_finiteSystem_input
    {x : ℝ}
    (hx : ieeeDoubleFormat.finiteSystem x)
    (hzero : ieeeDoubleFormat.problem2_24_eval x = 0) :
    (9 / 34 : ℝ) ≤ x ∧ x < (1 / 2 : ℝ) :=
  ieeeDoubleFormat.problem2_24_eval_eq_zero_input_mem_nine_thirty_four_to_half_of_finiteSystem_input
    problem2_24_ieeeDouble_subnormalMantissa_one
    problem2_24_ieeeDouble_half_finiteSystem
    problem2_24_ieeeDouble_one_finiteSystem hx hzero

/-- Problem 2.24, IEEE-single `[5/18,1/2)` localization for finite zero
counterexamples. -/
theorem problem2_24_ieeeSingle_eval_eq_zero_input_mem_five_eighteen_to_half_of_finiteSystem_input
    {x : ℝ}
    (hx : ieeeSingleFormat.finiteSystem x)
    (hzero : ieeeSingleFormat.problem2_24_eval x = 0) :
    (5 / 18 : ℝ) ≤ x ∧ x < (1 / 2 : ℝ) :=
  ieeeSingleFormat.problem2_24_eval_eq_zero_input_mem_five_eighteen_to_half_of_finiteSystem_input
    problem2_24_ieeeSingle_subnormalMantissa_one
    problem2_24_ieeeSingle_half_finiteSystem
    problem2_24_ieeeSingle_one_finiteSystem hx hzero

/-- Problem 2.24, IEEE-double `[5/18,1/2)` localization for finite zero
counterexamples. -/
theorem problem2_24_ieeeDouble_eval_eq_zero_input_mem_five_eighteen_to_half_of_finiteSystem_input
    {x : ℝ}
    (hx : ieeeDoubleFormat.finiteSystem x)
    (hzero : ieeeDoubleFormat.problem2_24_eval x = 0) :
    (5 / 18 : ℝ) ≤ x ∧ x < (1 / 2 : ℝ) :=
  ieeeDoubleFormat.problem2_24_eval_eq_zero_input_mem_five_eighteen_to_half_of_finiteSystem_input
    problem2_24_ieeeDouble_subnormalMantissa_one
    problem2_24_ieeeDouble_half_finiteSystem
    problem2_24_ieeeDouble_one_finiteSystem hx hzero

/-- Problem 2.24, IEEE-single `[5/18,5/12]` localization for finite zero
counterexamples. -/
theorem problem2_24_ieeeSingle_eval_eq_zero_input_mem_five_eighteen_to_five_twelfths_of_finiteSystem_input
    {x : ℝ}
    (hx : ieeeSingleFormat.finiteSystem x)
    (hzero : ieeeSingleFormat.problem2_24_eval x = 0) :
    (5 / 18 : ℝ) ≤ x ∧ x ≤ (5 / 12 : ℝ) :=
  ieeeSingleFormat.problem2_24_eval_eq_zero_input_mem_five_eighteen_to_five_twelfths_of_finiteSystem_input
    problem2_24_ieeeSingle_subnormalMantissa_one
    problem2_24_ieeeSingle_half_finiteSystem hx hzero

/-- Problem 2.24, IEEE-double `[5/18,5/12]` localization for finite zero
counterexamples. -/
theorem problem2_24_ieeeDouble_eval_eq_zero_input_mem_five_eighteen_to_five_twelfths_of_finiteSystem_input
    {x : ℝ}
    (hx : ieeeDoubleFormat.finiteSystem x)
    (hzero : ieeeDoubleFormat.problem2_24_eval x = 0) :
    (5 / 18 : ℝ) ≤ x ∧ x ≤ (5 / 12 : ℝ) :=
  ieeeDoubleFormat.problem2_24_eval_eq_zero_input_mem_five_eighteen_to_five_twelfths_of_finiteSystem_input
    problem2_24_ieeeDouble_subnormalMantissa_one
    problem2_24_ieeeDouble_half_finiteSystem hx hzero

/-- Problem 2.24, IEEE-single `[3/10,5/12]` localization for finite zero
counterexamples. -/
theorem problem2_24_ieeeSingle_eval_eq_zero_input_mem_three_tenths_to_five_twelfths_of_finiteSystem_input
    {x : ℝ}
    (hx : ieeeSingleFormat.finiteSystem x)
    (hzero : ieeeSingleFormat.problem2_24_eval x = 0) :
    (3 / 10 : ℝ) ≤ x ∧ x ≤ (5 / 12 : ℝ) :=
  ieeeSingleFormat.problem2_24_eval_eq_zero_input_mem_three_tenths_to_five_twelfths_of_finiteSystem_input
    problem2_24_ieeeSingle_subnormalMantissa_one
    problem2_24_ieeeSingle_half_finiteSystem hx hzero

/-- Problem 2.24, IEEE-double `[3/10,5/12]` localization for finite zero
counterexamples. -/
theorem problem2_24_ieeeDouble_eval_eq_zero_input_mem_three_tenths_to_five_twelfths_of_finiteSystem_input
    {x : ℝ}
    (hx : ieeeDoubleFormat.finiteSystem x)
    (hzero : ieeeDoubleFormat.problem2_24_eval x = 0) :
    (3 / 10 : ℝ) ≤ x ∧ x ≤ (5 / 12 : ℝ) :=
  ieeeDoubleFormat.problem2_24_eval_eq_zero_input_mem_three_tenths_to_five_twelfths_of_finiteSystem_input
    problem2_24_ieeeDouble_subnormalMantissa_one
    problem2_24_ieeeDouble_half_finiteSystem hx hzero

/-- Problem 2.24, IEEE-single `[53/160,3/8]` localization for finite zero
counterexamples. -/
theorem problem2_24_ieeeSingle_eval_eq_zero_input_mem_fifty_three_one_sixty_to_three_eighths_of_finiteSystem_input
    {x : ℝ}
    (hx : ieeeSingleFormat.finiteSystem x)
    (hzero : ieeeSingleFormat.problem2_24_eval x = 0) :
    (53 / 160 : ℝ) ≤ x ∧ x ≤ (3 / 8 : ℝ) :=
  ieeeSingleFormat.problem2_24_eval_eq_zero_input_mem_fifty_three_one_sixty_to_three_eighths_of_finiteSystem_input
    problem2_24_ieeeSingle_subnormalMantissa_one
    problem2_24_ieeeSingle_half_finiteSystem
    (ieeeSingleFormat.finiteSystem_neg
      problem2_24_ieeeSingle_eleven_thirty_two_finiteSystem)
    (ieeeSingleFormat.finiteSystem_neg
      problem2_24_ieeeSingle_three_eighths_finiteSystem)
    hx hzero

/-- Problem 2.24, IEEE-double `[53/160,3/8]` localization for finite zero
counterexamples. -/
theorem problem2_24_ieeeDouble_eval_eq_zero_input_mem_fifty_three_one_sixty_to_three_eighths_of_finiteSystem_input
    {x : ℝ}
    (hx : ieeeDoubleFormat.finiteSystem x)
    (hzero : ieeeDoubleFormat.problem2_24_eval x = 0) :
    (53 / 160 : ℝ) ≤ x ∧ x ≤ (3 / 8 : ℝ) :=
  ieeeDoubleFormat.problem2_24_eval_eq_zero_input_mem_fifty_three_one_sixty_to_three_eighths_of_finiteSystem_input
    problem2_24_ieeeDouble_subnormalMantissa_one
    problem2_24_ieeeDouble_half_finiteSystem
    (ieeeDoubleFormat.finiteSystem_neg
      problem2_24_ieeeDouble_eleven_thirty_two_finiteSystem)
    (ieeeDoubleFormat.finiteSystem_neg
      problem2_24_ieeeDouble_three_eighths_finiteSystem)
    hx hzero

/-- Problem 2.24, IEEE-single lower endpoint sharpened with the upper adjacent
single-precision value above `1/3`. -/
theorem problem2_24_ieeeSingle_eval_eq_zero_input_ge_two_sub_one_third_upper_neighbor_div_five_of_finiteSystem_input
    {x : ℝ}
    (hx : ieeeSingleFormat.finiteSystem x)
    (hzero : ieeeSingleFormat.problem2_24_eval x = 0) :
    (2 - ((11184811 : ℝ) * (2 : ℝ) ^ (-25 : ℤ))) / 5 ≤ x :=
  ieeeSingleFormat.problem2_24_eval_eq_zero_input_ge_two_sub_const_div_five_of_finiteSystem_input
    problem2_24_ieeeSingle_subnormalMantissa_one
    problem2_24_ieeeSingle_half_finiteSystem
    (ieeeSingleFormat.finiteSystem_neg
      problem2_24_ieeeSingle_one_third_upper_neighbor_finiteSystem)
    hx
    (by norm_num [zpow_neg])
    hzero

/-- Problem 2.24, IEEE-double lower endpoint sharpened with the upper adjacent
double-precision value above `1/3`. -/
theorem problem2_24_ieeeDouble_eval_eq_zero_input_ge_two_sub_one_third_upper_neighbor_div_five_of_finiteSystem_input
    {x : ℝ}
    (hx : ieeeDoubleFormat.finiteSystem x)
    (hzero : ieeeDoubleFormat.problem2_24_eval x = 0) :
    (2 - ((6004799503160662 : ℝ) * (2 : ℝ) ^ (-54 : ℤ))) / 5 ≤ x :=
  ieeeDoubleFormat.problem2_24_eval_eq_zero_input_ge_two_sub_const_div_five_of_finiteSystem_input
    problem2_24_ieeeDouble_subnormalMantissa_one
    problem2_24_ieeeDouble_half_finiteSystem
    (ieeeDoubleFormat.finiteSystem_neg
      problem2_24_ieeeDouble_one_third_upper_neighbor_finiteSystem)
    hx
    (by norm_num [zpow_neg])
    hzero

/-- Problem 2.24, IEEE-single current modeled finite zero branch using the
adjacent-value lower endpoint and the `3/8` upper endpoint. -/
theorem problem2_24_ieeeSingle_eval_eq_zero_input_mem_one_third_upper_neighbor_lower_to_three_eighths_of_finiteSystem_input
    {x : ℝ}
    (hx : ieeeSingleFormat.finiteSystem x)
    (hzero : ieeeSingleFormat.problem2_24_eval x = 0) :
    (2 - ((11184811 : ℝ) * (2 : ℝ) ^ (-25 : ℤ))) / 5 ≤ x ∧
      x ≤ (3 / 8 : ℝ) :=
  ⟨problem2_24_ieeeSingle_eval_eq_zero_input_ge_two_sub_one_third_upper_neighbor_div_five_of_finiteSystem_input
      hx hzero,
    ieeeSingleFormat.problem2_24_eval_eq_zero_input_le_three_eighths_of_finiteSystem_input
      problem2_24_ieeeSingle_subnormalMantissa_one
      problem2_24_ieeeSingle_half_finiteSystem
      (ieeeSingleFormat.finiteSystem_neg
        problem2_24_ieeeSingle_three_eighths_finiteSystem)
      hx hzero⟩

/-- Problem 2.24, IEEE-double current modeled finite zero branch using the
adjacent-value lower endpoint and the `3/8` upper endpoint. -/
theorem problem2_24_ieeeDouble_eval_eq_zero_input_mem_one_third_upper_neighbor_lower_to_three_eighths_of_finiteSystem_input
    {x : ℝ}
    (hx : ieeeDoubleFormat.finiteSystem x)
    (hzero : ieeeDoubleFormat.problem2_24_eval x = 0) :
    (2 - ((6004799503160662 : ℝ) * (2 : ℝ) ^ (-54 : ℤ))) / 5 ≤ x ∧
      x ≤ (3 / 8 : ℝ) :=
  ⟨problem2_24_ieeeDouble_eval_eq_zero_input_ge_two_sub_one_third_upper_neighbor_div_five_of_finiteSystem_input
      hx hzero,
    ieeeDoubleFormat.problem2_24_eval_eq_zero_input_le_three_eighths_of_finiteSystem_input
      problem2_24_ieeeDouble_subnormalMantissa_one
      problem2_24_ieeeDouble_half_finiteSystem
      (ieeeDoubleFormat.finiteSystem_neg
        problem2_24_ieeeDouble_three_eighths_finiteSystem)
      hx hzero⟩

end FloatingPointFormat

end

end NumStability
