import Mathlib.Tactic
import NumStability.Algorithms.Summation.Recursive.Core
import NumStability.Source.Higham.Chapter02.Problem10.DivisionRoundTrip.Basic

/-!
# Chapter04 Problem02 WilkinsonAttainability Basic

Canonical destination for material split out of
`NumStability.Algorithms.WilkinsonAttainability` by wave W12 of the August 2026 repository reorganization.
Declaration names, statements and proofs are unchanged; only the
module they live in has changed. The historical module still
resolves and re-exports this one.
-/

open scoped BigOperators

namespace NumStability

/-- The value in Wilkinson's `j`th block for Problem 4.2:
`1 - 2^(j-t)`.  The source writes `u = 2^(-t)`, so the first nontrivial
block is `1 - 2^(-t)`, then `1 - 2^(1-t)`, and so on. -/
noncomputable def wilkinsonProblem42BlockValue (t j : ℕ) : ℝ :=
  1 - (2 : ℝ) ^ ((j : ℤ) - (t : ℤ))

/-- Wilkinson's hinted source list for `n = 2^r`.

It starts with `[1]`; for each `j < r`, it appends `2^j` copies of
`1 - 2^(j-t)`.  Thus
`r = 1` gives `[1, 1 - 2^(-t)]`, and
`r = 2` appends two copies of `1 - 2^(1-t)`. -/
noncomputable def wilkinsonProblem42Input (t : ℕ) : ℕ → List ℝ
  | 0 => [1]
  | r + 1 =>
      wilkinsonProblem42Input t r ++
        List.replicate (2 ^ r) (wilkinsonProblem42BlockValue t r)

/-- Exact closed-form sum of the formalized Wilkinson Problem 4.2 source list. -/
noncomputable def wilkinsonProblem42ExactSum (t r : ℕ) : ℝ :=
  1 +
    Finset.sum (Finset.range r)
      (fun j => (2 : ℝ) ^ j * wilkinsonProblem42BlockValue t j)

/-- The exact amount removed from the integer sum by Wilkinson's displayed
low-order powers of two.  If the rounded trace drops every low-order term, the
computed recursive sum is `2^r` and the absolute forward error is exactly this
quantity. -/
noncomputable def wilkinsonProblem42Defect (t r : ℕ) : ℝ :=
  Finset.sum (Finset.range r)
    (fun j => (2 : ℝ) ^ j * (2 : ℝ) ^ ((j : ℤ) - (t : ℤ)))

/-- The formalized Wilkinson source list has the source length `2^r`. -/
theorem wilkinsonProblem42Input_length (t r : ℕ) :
    (wilkinsonProblem42Input t r).length = 2 ^ r := by
  induction r with
  | zero =>
      simp [wilkinsonProblem42Input]
  | succ r ih =>
      simp [wilkinsonProblem42Input, ih, Nat.pow_succ]
      ring

/-- The formalized Wilkinson source list has the expected block-sum formula. -/
theorem wilkinsonProblem42Input_sum_eq (t r : ℕ) :
    (wilkinsonProblem42Input t r).sum =
      wilkinsonProblem42ExactSum t r := by
  induction r with
  | zero =>
      simp [wilkinsonProblem42Input, wilkinsonProblem42ExactSum]
  | succ r ih =>
      simp [wilkinsonProblem42Input, wilkinsonProblem42ExactSum, ih,
        Finset.sum_range_succ]
      ring

/-- First displayed row of the Problem 4.2 hint. -/
theorem wilkinsonProblem42Input_zero (t : ℕ) :
    wilkinsonProblem42Input t 0 = [1] := by
  rfl

/-- Recursive block extension matching the displayed powers-of-two ranges. -/
theorem wilkinsonProblem42Input_succ (t r : ℕ) :
    wilkinsonProblem42Input t (r + 1) =
      wilkinsonProblem42Input t r ++
        List.replicate (2 ^ r) (wilkinsonProblem42BlockValue t r) := by
  rfl

/-- Finite-vector bridge for the Wilkinson source list, with the source length
`2^r` baked into the type used by recursive summation. -/
noncomputable def wilkinsonProblem42Vector (t r : ℕ) : Fin (2 ^ r) → ℝ :=
  fun i => (wilkinsonProblem42Input t r).get
    (Fin.cast (wilkinsonProblem42Input_length t r).symm i)

/-- The vector bridge serializes back to exactly Wilkinson's displayed source
list. -/
theorem wilkinsonProblem42Vector_toList (t r : ℕ) :
    List.ofFn (wilkinsonProblem42Vector t r) =
      wilkinsonProblem42Input t r := by
  let l := wilkinsonProblem42Input t r
  have hlen : l.length = 2 ^ r := by
    simpa [l] using wilkinsonProblem42Input_length t r
  have hcongr := List.ofFn_congr hlen (List.get l)
  calc
    List.ofFn (wilkinsonProblem42Vector t r) = List.ofFn (List.get l) := by
      simpa [wilkinsonProblem42Vector, l] using hcongr.symm
    _ = l := by
      simp
    _ = wilkinsonProblem42Input t r := rfl

/-- Finite-vector sum form of the Wilkinson block-sum formula. -/
theorem wilkinsonProblem42Vector_sum_eq (t r : ℕ) :
    (∑ i : Fin (2 ^ r), wilkinsonProblem42Vector t r i) =
      wilkinsonProblem42ExactSum t r := by
  rw [← List.sum_ofFn, wilkinsonProblem42Vector_toList]
  exact wilkinsonProblem42Input_sum_eq t r

/-- Wilkinson's exact source sum plus the displayed low-order defect is the
integer `2^r`.  This is the algebraic core of the Problem 4.2 hint. -/
theorem wilkinsonProblem42ExactSum_add_defect (t r : ℕ) :
    wilkinsonProblem42ExactSum t r + wilkinsonProblem42Defect t r =
      (2 : ℝ) ^ r := by
  induction r with
  | zero =>
      simp [wilkinsonProblem42ExactSum, wilkinsonProblem42Defect]
  | succ r ih =>
      calc
        wilkinsonProblem42ExactSum t (r + 1) +
            wilkinsonProblem42Defect t (r + 1) =
          (wilkinsonProblem42ExactSum t r +
            wilkinsonProblem42Defect t r) + (2 : ℝ) ^ r := by
          simp [wilkinsonProblem42ExactSum, wilkinsonProblem42Defect,
            Finset.sum_range_succ, wilkinsonProblem42BlockValue]
          ring
        _ = (2 : ℝ) ^ r + (2 : ℝ) ^ r := by
          rw [ih]
        _ = (2 : ℝ) ^ (r + 1) := by
          rw [pow_succ]
          ring

/-- The displayed low-order defect is nonnegative. -/
theorem wilkinsonProblem42Defect_nonneg (t r : ℕ) :
    0 ≤ wilkinsonProblem42Defect t r := by
  unfold wilkinsonProblem42Defect
  refine Finset.sum_nonneg ?_
  intro j _hj
  exact mul_nonneg
    (pow_nonneg (by norm_num : (0 : ℝ) ≤ 2) j)
    (le_of_lt (zpow_pos (by norm_num : (0 : ℝ) < 2)
      ((j : ℤ) - (t : ℤ))))

/-- Closed geometric-series form of Wilkinson's accumulated low-order defect:
`defect = (2^(2*r-t) - 2^(-t)) / 3`.  The statement is multiplied through by
`3` to avoid a division side calculation. -/
theorem wilkinsonProblem42Defect_closed_form (t r : ℕ) :
    3 * wilkinsonProblem42Defect t r + (2 : ℝ) ^ (-(t : ℤ)) =
      (2 : ℝ) ^ (((2 * r : ℕ) : ℤ) - (t : ℤ)) := by
  induction r with
  | zero =>
      simp [wilkinsonProblem42Defect]
  | succ r ih =>
      have hterm :
          (2 : ℝ) ^ r * (2 : ℝ) ^ ((r : ℤ) - (t : ℤ)) =
            (2 : ℝ) ^ (((2 * r : ℕ) : ℤ) - (t : ℤ)) := by
        rw [← zpow_natCast]
        rw [← zpow_add₀ (by norm_num : (2 : ℝ) ≠ 0)]
        congr 1
        omega
      have hexp_succ :
          (((2 * (r + 1) : ℕ) : ℤ) - (t : ℤ)) =
            (((2 * r : ℕ) : ℤ) - (t : ℤ)) + 2 := by
        omega
      calc
        3 * wilkinsonProblem42Defect t (r + 1) + (2 : ℝ) ^ (-(t : ℤ)) =
          (3 * wilkinsonProblem42Defect t r + (2 : ℝ) ^ (-(t : ℤ))) +
            3 * ((2 : ℝ) ^ r * (2 : ℝ) ^ ((r : ℤ) - (t : ℤ))) := by
          simp [wilkinsonProblem42Defect, Finset.sum_range_succ]
          ring
        _ = (2 : ℝ) ^ (((2 * r : ℕ) : ℤ) - (t : ℤ)) +
            3 * (2 : ℝ) ^ (((2 * r : ℕ) : ℤ) - (t : ℤ)) := by
          rw [ih, hterm]
        _ = (2 : ℝ) ^ (((2 * (r + 1) : ℕ) : ℤ) - (t : ℤ)) := by
          rw [hexp_succ]
          rw [zpow_add₀ (by norm_num : (2 : ℝ) ≠ 0)]
          norm_num
          ring

/-- Wilkinson's exact source sum is at most the integer `2^r`; the difference
is the displayed defect. -/
theorem wilkinsonProblem42ExactSum_le_pow (t r : ℕ) :
    wilkinsonProblem42ExactSum t r ≤ (2 : ℝ) ^ r := by
  have hsum := wilkinsonProblem42ExactSum_add_defect t r
  have hdef := wilkinsonProblem42Defect_nonneg t r
  nlinarith

/-- First-order comparison with the specialized equation (4.4) scale.

For `u = 2^(-t)` and `n = 2^r`, the first-order right-hand side
`(n - 1) * u * exactSum` is at most `3 * defect + u`.  This is the algebraic
part of Wilkinson's near-attainability comparison; the exact `gamma` bound and
finite-format rounded trace remain separate obligations. -/
theorem wilkinsonProblem42_first_order_bound_le_three_defect_plus_u (t r : ℕ) :
    (((2 ^ r - 1 : ℕ) : ℝ) * (2 : ℝ) ^ (-(t : ℤ))) *
        wilkinsonProblem42ExactSum t r ≤
      3 * wilkinsonProblem42Defect t r + (2 : ℝ) ^ (-(t : ℤ)) := by
  let u : ℝ := (2 : ℝ) ^ (-(t : ℤ))
  have hu_nonneg : 0 ≤ u :=
    le_of_lt (zpow_pos (by norm_num : (0 : ℝ) < 2) (-(t : ℤ)))
  have hnR_nonneg : 0 ≤ (2 : ℝ) ^ r :=
    pow_nonneg (by norm_num : (0 : ℝ) ≤ 2) r
  have hpred_le : (((2 ^ r - 1 : ℕ) : ℝ)) ≤ (2 : ℝ) ^ r := by
    exact_mod_cast (Nat.sub_le (2 ^ r) 1)
  have hcoef_nonneg : 0 ≤ (((2 ^ r - 1 : ℕ) : ℝ) * u) :=
    mul_nonneg (by exact_mod_cast Nat.zero_le (2 ^ r - 1)) hu_nonneg
  have hcoef_le : (((2 ^ r - 1 : ℕ) : ℝ) * u) ≤ (2 : ℝ) ^ r * u :=
    mul_le_mul_of_nonneg_right hpred_le hu_nonneg
  have hsum_le : wilkinsonProblem42ExactSum t r ≤ (2 : ℝ) ^ r :=
    wilkinsonProblem42ExactSum_le_pow t r
  have hleft_le_sum :
      (((2 ^ r - 1 : ℕ) : ℝ) * u) * wilkinsonProblem42ExactSum t r ≤
        (((2 ^ r - 1 : ℕ) : ℝ) * u) * (2 : ℝ) ^ r :=
    mul_le_mul_of_nonneg_left hsum_le hcoef_nonneg
  have hleft_le_full :
      (((2 ^ r - 1 : ℕ) : ℝ) * u) * (2 : ℝ) ^ r ≤
        ((2 : ℝ) ^ r * u) * (2 : ℝ) ^ r :=
    mul_le_mul_of_nonneg_right hcoef_le hnR_nonneg
  have hscale : ((2 : ℝ) ^ r * u) * (2 : ℝ) ^ r =
      (2 : ℝ) ^ (((2 * r : ℕ) : ℤ) - (t : ℤ)) := by
    dsimp [u]
    calc
      ((2 : ℝ) ^ r * (2 : ℝ) ^ (-(t : ℤ))) * (2 : ℝ) ^ r
          = (2 : ℝ) ^ ((r : ℤ) + (-(t : ℤ))) * (2 : ℝ) ^ r := by
            rw [← zpow_natCast]
            rw [← zpow_add₀ (by norm_num : (2 : ℝ) ≠ 0)]
      _ = (2 : ℝ) ^ (((r : ℤ) + (-(t : ℤ))) + (r : ℤ)) := by
            rw [← zpow_natCast]
            rw [← zpow_add₀ (by norm_num : (2 : ℝ) ≠ 0)]
      _ = (2 : ℝ) ^ (((2 * r : ℕ) : ℤ) - (t : ℤ)) := by
            congr 1
            omega
  calc
    (((2 ^ r - 1 : ℕ) : ℝ) * (2 : ℝ) ^ (-(t : ℤ))) *
        wilkinsonProblem42ExactSum t r
        = (((2 ^ r - 1 : ℕ) : ℝ) * u) * wilkinsonProblem42ExactSum t r := by
          rfl
    _ ≤ (((2 ^ r - 1 : ℕ) : ℝ) * u) * (2 : ℝ) ^ r := hleft_le_sum
    _ ≤ ((2 : ℝ) ^ r * u) * (2 : ℝ) ^ r := hleft_le_full
    _ = (2 : ℝ) ^ (((2 * r : ℕ) : ℤ) - (t : ℤ)) := hscale
    _ = 3 * wilkinsonProblem42Defect t r + (2 : ℝ) ^ (-(t : ℤ)) := by
      rw [← wilkinsonProblem42Defect_closed_form]

/-- Exact-`gamma` comparison with the specialized equation (4.4) scale.

When the abstract model's unit roundoff is the source value `u = 2^(-t)`,
the exact `gamma (2^r - 1)` bound differs from the first-order scale by the
usual denominator `1 - (2^r - 1) * u`. -/
theorem wilkinsonProblem42_gamma_bound_le_three_defect_plus_u_div
    (fp : FPModel) (t r : ℕ)
    (hunit : fp.u = (2 : ℝ) ^ (-(t : ℤ)))
    (hvalid : gammaValid fp (2 ^ r - 1)) :
    gamma fp (2 ^ r - 1) * wilkinsonProblem42ExactSum t r ≤
      (3 * wilkinsonProblem42Defect t r + (2 : ℝ) ^ (-(t : ℤ))) /
        (1 - ((2 ^ r - 1 : ℕ) : ℝ) * (2 : ℝ) ^ (-(t : ℤ))) := by
  let u : ℝ := (2 : ℝ) ^ (-(t : ℤ))
  let k : ℝ := ((2 ^ r - 1 : ℕ) : ℝ)
  have hden_pos : 0 < 1 - k * u := by
    have hv := hvalid
    unfold gammaValid at hv
    rw [hunit] at hv
    simpa [k, u] using hv
  have hfirst :=
    wilkinsonProblem42_first_order_bound_le_three_defect_plus_u t r
  have hgamma_eq :
      gamma fp (2 ^ r - 1) * wilkinsonProblem42ExactSum t r =
        (k * u * wilkinsonProblem42ExactSum t r) / (1 - k * u) := by
    unfold gamma
    rw [hunit]
    dsimp [k, u]
    ring
  calc
    gamma fp (2 ^ r - 1) * wilkinsonProblem42ExactSum t r =
        (k * u * wilkinsonProblem42ExactSum t r) / (1 - k * u) := hgamma_eq
    _ ≤ (3 * wilkinsonProblem42Defect t r + (2 : ℝ) ^ (-(t : ℤ))) /
        (1 - k * u) := by
      exact div_le_div_of_nonneg_right hfirst (le_of_lt hden_pos)
    _ = (3 * wilkinsonProblem42Defect t r + (2 : ℝ) ^ (-(t : ℤ))) /
        (1 - ((2 ^ r - 1 : ℕ) : ℝ) * (2 : ℝ) ^ (-(t : ℤ))) := by
      rfl

/-- If the finite-format recursive trace drops the low-order part at every
Wilkinson step and therefore returns `2^r`, then its absolute forward error is
exactly the displayed low-order defect. -/
theorem wilkinsonProblem42_abs_error_eq_defect_of_recursiveSum_eq_pow
    (fp : FPModel) {t r : ℕ}
    (htrace :
      fl_recursiveSum fp (2 ^ r) (wilkinsonProblem42Vector t r) =
        (2 : ℝ) ^ r) :
    |fl_recursiveSum fp (2 ^ r) (wilkinsonProblem42Vector t r) -
        wilkinsonProblem42ExactSum t r| =
      wilkinsonProblem42Defect t r := by
  have hdiff :
      (2 : ℝ) ^ r - wilkinsonProblem42ExactSum t r =
        wilkinsonProblem42Defect t r := by
    have hsum := wilkinsonProblem42ExactSum_add_defect t r
    linarith
  rw [htrace, hdiff]
  exact abs_of_nonneg (wilkinsonProblem42Defect_nonneg t r)

/-- Base case of the Wilkinson recursive-summation trace.

For `r = 0`, the source contains the single term `1`, and the first addition
from zero is exact in every `FPModel`. -/
theorem wilkinsonProblem42_recursiveSum_eq_pow_zero (fp : FPModel) (t : ℕ) :
    fl_recursiveSum fp (2 ^ 0) (wilkinsonProblem42Vector t 0) =
      (2 : ℝ) ^ 0 := by
  change Fin.foldl 1 (fun acc i => fp.fl_add acc
    (wilkinsonProblem42Vector t 0 i)) 0 = 1
  rw [Fin.foldl_succ]
  simp [wilkinsonProblem42Vector, wilkinsonProblem42Input, fp.fl_add_zero]

/-- Recursive summation driven by the concrete finite round-to-even addition
operation of a source-facing finite format.  This is the trace needed to turn
Wilkinson's abstract Problem 4.2 hint into a finite-format rounding statement. -/
noncomputable def finiteRoundToEvenRecursiveSum
    (fmt : FloatingPointFormat) (n : ℕ) (v : Fin n → ℝ) : ℝ :=
  Fin.foldl n (fun acc i => fmt.finiteRoundToEvenOp BasicOp.add acc (v i)) 0

/-- List-shaped version of the concrete finite round-to-even recursive trace.
This is convenient for source families that are naturally described by list
append and replication before being bridged to a `Fin` vector. -/
noncomputable def finiteRoundToEvenListSum
    (fmt : FloatingPointFormat) (xs : List ℝ) : ℝ :=
  xs.foldl (fun acc x => fmt.finiteRoundToEvenOp BasicOp.add acc x) 0

theorem finiteRoundToEvenFinFold_eq_listFold
    (fmt : FloatingPointFormat) :
    ∀ (n : ℕ) (v : Fin n → ℝ) (start : ℝ),
      Fin.foldl n
        (fun acc i => fmt.finiteRoundToEvenOp BasicOp.add acc (v i))
        start =
      (List.ofFn v).foldl
        (fun acc x => fmt.finiteRoundToEvenOp BasicOp.add acc x)
        start
  | 0, _v, start => by
      simp [List.ofFn_zero]
  | n + 1, v, start => by
      rw [Fin.foldl_succ, List.ofFn_succ, List.foldl_cons]
      exact finiteRoundToEvenFinFold_eq_listFold fmt n (fun i => v i.succ)
        (fmt.finiteRoundToEvenOp BasicOp.add start (v 0))

/-- The concrete `Fin` recursive trace is exactly the list trace of the vector's
serialized entries. -/
theorem finiteRoundToEvenRecursiveSum_eq_listSum
    (fmt : FloatingPointFormat) (n : ℕ) (v : Fin n → ℝ) :
    finiteRoundToEvenRecursiveSum fmt n v =
      finiteRoundToEvenListSum fmt (List.ofFn v) := by
  simpa [finiteRoundToEvenRecursiveSum, finiteRoundToEvenListSum] using
    finiteRoundToEvenFinFold_eq_listFold fmt n v 0

/-- Each displayed Wilkinson block value is finite in any base-2 `t`-digit
format whose exponent range contains `0`.  This is the generic
finite-representability part of Problem 4.2: for `j + 1 <= t`,
`1 - 2^(j-t)` is the normalized value with exponent `0` and mantissa
`2^t - 2^j`. -/
theorem wilkinsonProblem42BlockValue_baseTwo_finiteSystem
    (fmt : FloatingPointFormat) (t : ℕ)
    (hbeta : fmt.beta = 2) (ht : fmt.t = t)
    (he0 : fmt.exponentInRange (0 : ℤ))
    {j : ℕ} (hj : j + 1 ≤ t) :
    fmt.finiteSystem (wilkinsonProblem42BlockValue t j) := by
  let m : ℕ := 2 ^ t - 2 ^ j
  have hj_le_t : j ≤ t := by omega
  have hj_le_pred : j ≤ t - 1 := by omega
  have hm : fmt.normalizedMantissa m := by
    constructor
    · change fmt.beta ^ (fmt.t - 1) ≤ m
      rw [hbeta, ht]
      have hjpow : 2 ^ j ≤ 2 ^ (t - 1) :=
        Nat.pow_le_pow_right (by norm_num : 0 < 2) hj_le_pred
      have hpowt : 2 ^ t = 2 ^ (t - 1) + 2 ^ (t - 1) := by
        calc
          2 ^ t = 2 ^ ((t - 1) + 1) := by
            exact congrArg (fun n : ℕ => 2 ^ n)
              (by omega : t = (t - 1) + 1)
          _ = 2 ^ (t - 1) * 2 := by
            simpa using (Nat.pow_succ 2 (t - 1))
          _ = 2 ^ (t - 1) + 2 ^ (t - 1) := by
            omega
      dsimp [m]
      omega
    · change m < fmt.beta ^ fmt.t
      rw [hbeta, ht]
      have hpos : 0 < 2 ^ j := pow_pos (by norm_num : 0 < 2) j
      have hle : 2 ^ j ≤ 2 ^ t :=
        Nat.pow_le_pow_right (by norm_num : 0 < 2) hj_le_t
      dsimp [m]
      omega
  have hrepr :
      wilkinsonProblem42BlockValue t j =
        fmt.normalizedValue false m (0 : ℤ) := by
    dsimp [wilkinsonProblem42BlockValue, m]
    rw [show ((j : ℤ) - (t : ℤ)) = (j : ℤ) + (-(t : ℤ)) by ring]
    rw [zpow_add₀ (by norm_num : (2 : ℝ) ≠ 0)]
    rw [zpow_natCast]
    simp [FloatingPointFormat.normalizedValue, FloatingPointFormat.signValue,
      FloatingPointFormat.betaR, hbeta, ht]
    rw [Nat.cast_sub]
    · field_simp
      norm_num [Nat.cast_pow]
    · exact Nat.pow_le_pow_right (by norm_num : 0 < 2) hj_le_t
  exact Or.inr (Or.inl ⟨false, m, (0 : ℤ), hm, he0, hrepr⟩)

/-- The initial `1` in Wilkinson's Problem 4.2 family is finite in any base-2
`t`-digit format whose exponent range contains `1`. -/
theorem wilkinsonProblem42One_baseTwo_finiteSystem
    (fmt : FloatingPointFormat) (t : ℕ)
    (hbeta : fmt.beta = 2) (ht : fmt.t = t)
    (he1 : fmt.exponentInRange (1 : ℤ)) :
    fmt.finiteSystem (1 : ℝ) := by
  let m : ℕ := 2 ^ (t - 1)
  have htpos : 0 < t := by
    rw [← ht]
    exact fmt.t_pos
  have hm : fmt.normalizedMantissa m := by
    constructor
    · change fmt.beta ^ (fmt.t - 1) ≤ m
      rw [hbeta, ht]
    · change m < fmt.beta ^ fmt.t
      rw [hbeta, ht]
      dsimp [m]
      exact Nat.pow_lt_pow_right (by norm_num : 1 < 2) (by omega : t - 1 < t)
  have hrepr :
      (1 : ℝ) = fmt.normalizedValue false m (1 : ℤ) := by
    dsimp [m]
    simp [FloatingPointFormat.normalizedValue, FloatingPointFormat.signValue,
      FloatingPointFormat.betaR, hbeta, ht]
    rw [show ((1 : ℤ) - (t : ℤ)) = -(((t - 1 : ℕ) : ℤ)) by omega]
    rw [zpow_neg]
    rw [zpow_natCast]
    field_simp [pow_ne_zero]
  exact Or.inr (Or.inl ⟨false, m, (1 : ℤ), hm, he1, hrepr⟩)

/-- Every entry in Wilkinson's generic base-2 Problem 4.2 source list is finite
when exponents `0` and `1` are in range.  This closes the source-family
representability side of the arbitrary-precision route; it does not yet prove
the generic rounded recursive-summation trace. -/
theorem wilkinsonProblem42Input_baseTwo_all_finiteSystem
    (fmt : FloatingPointFormat) (t : ℕ)
    (hbeta : fmt.beta = 2) (ht : fmt.t = t)
    (he0 : fmt.exponentInRange (0 : ℤ))
    (he1 : fmt.exponentInRange (1 : ℤ))
    {r : ℕ} (hr : r ≤ t) :
    ∀ x ∈ wilkinsonProblem42Input t r, fmt.finiteSystem x := by
  induction r with
  | zero =>
      intro x hx
      simp [wilkinsonProblem42Input] at hx
      subst x
      exact wilkinsonProblem42One_baseTwo_finiteSystem fmt t hbeta ht he1
  | succ r ih =>
      intro x hx
      rw [wilkinsonProblem42Input_succ] at hx
      rw [List.mem_append] at hx
      rcases hx with hx | hx
      · exact ih (by omega) x hx
      · have hxval : x = wilkinsonProblem42BlockValue t r :=
          (List.mem_replicate.mp hx).2
        rw [hxval]
        exact wilkinsonProblem42BlockValue_baseTwo_finiteSystem
          fmt t hbeta ht he0 (j := r) (by omega)

/-- Vector-shaped finite-system certificate for Wilkinson's generic base-2
source family. -/
theorem wilkinsonProblem42Vector_baseTwo_finiteSystem
    (fmt : FloatingPointFormat) (t : ℕ)
    (hbeta : fmt.beta = 2) (ht : fmt.t = t)
    (he0 : fmt.exponentInRange (0 : ℤ))
    (he1 : fmt.exponentInRange (1 : ℤ))
    {r : ℕ} (hr : r ≤ t) (i : Fin (2 ^ r)) :
    fmt.finiteSystem (wilkinsonProblem42Vector t r i) := by
  have hall :=
    wilkinsonProblem42Input_baseTwo_all_finiteSystem
      fmt t hbeta ht he0 he1 (r := r) hr
  unfold wilkinsonProblem42Vector
  exact hall _ (List.get_mem _ _)

/-- Each displayed IEEE-double Wilkinson block value is itself a finite
representable value.  For `j <= 52`, `1 - 2^(j-53)` is the normalized value
with exponent `0` and mantissa `2^53 - 2^j`. -/
theorem wilkinsonProblem42BlockValue_ieeeDouble_finiteSystem
    {j : ℕ} (hj : j ≤ 52) :
    FloatingPointFormat.ieeeDoubleFormat.finiteSystem
      (wilkinsonProblem42BlockValue 53 j) := by
  let fmt := FloatingPointFormat.ieeeDoubleFormat
  let m : ℕ := 2 ^ 53 - 2 ^ j
  have hm : fmt.normalizedMantissa m := by
    constructor
    · change 2 ^ 52 ≤ m
      have hjpow : 2 ^ j ≤ 2 ^ 52 :=
        Nat.pow_le_pow_right (by norm_num : 0 < 2) hj
      have hpow53 : 2 ^ 53 = 2 ^ 52 + 2 ^ 52 := by
        rw [show 53 = 52 + 1 by omega, Nat.pow_succ]
        ring
      dsimp [m]
      omega
    · change m < 2 ^ 53
      have hpos : 0 < 2 ^ j := pow_pos (by norm_num : 0 < 2) j
      dsimp [m]
      omega
  have he : fmt.exponentInRange (0 : ℤ) := by
    norm_num [fmt, FloatingPointFormat.ieeeDoubleFormat,
      FloatingPointFormat.exponentInRange]
  have hrepr :
      wilkinsonProblem42BlockValue 53 j =
        fmt.normalizedValue false m (0 : ℤ) := by
    dsimp [wilkinsonProblem42BlockValue, fmt, m]
    rw [show ((j : ℤ) - (53 : ℤ)) = (j : ℤ) + (-53 : ℤ) by ring]
    rw [zpow_add₀ (by norm_num : (2 : ℝ) ≠ 0)]
    rw [zpow_natCast]
    norm_num [FloatingPointFormat.ieeeDoubleFormat,
      FloatingPointFormat.normalizedValue, FloatingPointFormat.signValue,
      FloatingPointFormat.betaR]
    rw [Nat.cast_sub]
    · field_simp
      norm_num [Nat.cast_pow]
    · exact Nat.pow_le_pow_right (by norm_num : 0 < 2) (by omega : j ≤ 53)
  exact Or.inr (Or.inl ⟨false, m, (0 : ℤ), hm, he, hrepr⟩)

/-- Every entry in Wilkinson's displayed IEEE-double input list is a finite
representable value. -/
theorem wilkinsonProblem42Input_ieeeDouble_all_finiteSystem
    {r : ℕ} (hr : r ≤ 53) :
    ∀ x ∈ wilkinsonProblem42Input 53 r,
      FloatingPointFormat.ieeeDoubleFormat.finiteSystem x := by
  induction r with
  | zero =>
      intro x hx
      simp [wilkinsonProblem42Input] at hx
      subst x
      exact FloatingPointFormat.problem2_10_ieeeDouble_finiteSystem_one
  | succ r ih =>
      intro x hx
      rw [wilkinsonProblem42Input_succ] at hx
      rw [List.mem_append] at hx
      rcases hx with hx | hx
      · exact ih (by omega) x hx
      · have hxval : x = wilkinsonProblem42BlockValue 53 r :=
          (List.mem_replicate.mp hx).2
        rw [hxval]
        exact wilkinsonProblem42BlockValue_ieeeDouble_finiteSystem
          (j := r) (by omega)

/-- Vector-shaped finite-system certificate for Wilkinson's IEEE-double source
family. -/
theorem wilkinsonProblem42Vector_ieeeDouble_finiteSystem
    {r : ℕ} (hr : r ≤ 53) (i : Fin (2 ^ r)) :
    FloatingPointFormat.ieeeDoubleFormat.finiteSystem
      (wilkinsonProblem42Vector 53 r i) := by
  have hall := wilkinsonProblem42Input_ieeeDouble_all_finiteSystem (r := r) hr
  unfold wilkinsonProblem42Vector
  exact hall _ (List.get_mem _ _)

/-- For every positive Wilkinson length, the first low-order term `u = 2^-t`
is already included in the displayed defect. -/
theorem wilkinsonProblem42_unit_roundoff_le_defect_of_pos
    {t r : ℕ} (hrpos : 0 < r) :
    (2 : ℝ) ^ (-(t : ℤ)) ≤ wilkinsonProblem42Defect t r := by
  unfold wilkinsonProblem42Defect
  have hmem : 0 ∈ Finset.range r := Finset.mem_range.mpr hrpos
  have hnonneg :
      ∀ x ∈ Finset.range r,
        0 ≤ (2 : ℝ) ^ x * (2 : ℝ) ^ ((x : ℤ) - (t : ℤ)) := by
    intro x _hx
    positivity
  have hsingle :=
    Finset.single_le_sum hnonneg hmem
  simpa using hsingle

/-- Wilkinson block values are nonnegative whenever the displayed exponent is
nonpositive. -/
theorem wilkinsonProblem42BlockValue_nonneg_of_le {t j : ℕ} (hjt : j ≤ t) :
    0 ≤ wilkinsonProblem42BlockValue t j := by
  have hexp : ((j : ℤ) - (t : ℤ)) ≤ 0 := by
    omega
  have hpow : (2 : ℝ) ^ ((j : ℤ) - (t : ℤ)) ≤ 1 := by
    simpa using
      (zpow_le_one_of_nonpos₀ (by norm_num : (1 : ℝ) ≤ 2) hexp)
  unfold wilkinsonProblem42BlockValue
  linarith

/-- Under the source regime where the last displayed block exponent is
nonpositive, every entry in Wilkinson's input list is nonnegative. -/
theorem wilkinsonProblem42Input_nonneg_of_le {t r : ℕ} (hr : r ≤ t + 1) :
    ∀ x ∈ wilkinsonProblem42Input t r, 0 ≤ x := by
  induction r with
  | zero =>
      intro x hx
      simp [wilkinsonProblem42Input] at hx
      linarith
  | succ r ih =>
      intro x hx
      simp [wilkinsonProblem42Input] at hx
      rcases hx with hx | hx
      · exact ih (by omega) x hx
      · rcases hx with ⟨_hcount, rfl⟩
        exact wilkinsonProblem42BlockValue_nonneg_of_le (t := t) (j := r) (by omega)

/-- Finite-vector nonnegativity for the Wilkinson family. -/
theorem wilkinsonProblem42Vector_nonneg_of_le {t r : ℕ} (hr : r ≤ t + 1) :
    ∀ i : Fin (2 ^ r), 0 ≤ wilkinsonProblem42Vector t r i := by
  intro i
  have hmem :
      wilkinsonProblem42Vector t r i ∈ wilkinsonProblem42Input t r := by
    rw [← wilkinsonProblem42Vector_toList]
    exact List.mem_ofFn.mpr ⟨i, rfl⟩
  exact wilkinsonProblem42Input_nonneg_of_le hr _ hmem

/-- Wilkinson's source vector is one-signed in the nonnegative source regime. -/
theorem wilkinsonProblem42Vector_oneSigned_of_le {t r : ℕ} (hr : r ≤ t + 1) :
    OneSigned (wilkinsonProblem42Vector t r) :=
  Or.inl (wilkinsonProblem42Vector_nonneg_of_le hr)

/-- In the nonnegative source regime, the recursive-summation a priori majorant
uses the exact Wilkinson sum rather than a larger cancellation-sensitive
absolute-value sum. -/
theorem wilkinsonProblem42Vector_sum_abs_eq {t r : ℕ} (hr : r ≤ t + 1) :
    (∑ i : Fin (2 ^ r), |wilkinsonProblem42Vector t r i|) =
      wilkinsonProblem42ExactSum t r := by
  rw [sum_abs_eq_sum_of_nonneg _ (wilkinsonProblem42Vector_nonneg_of_le hr),
    wilkinsonProblem42Vector_sum_eq]

/-- In the nonnegative source regime, Wilkinson's exact source sum is positive,
so relative-error statements have a nonzero denominator without an extra
hypothesis. -/
theorem wilkinsonProblem42ExactSum_pos_of_le {t r : ℕ} (hr : r ≤ t + 1) :
    0 < wilkinsonProblem42ExactSum t r := by
  have hsum_nonneg :
      0 ≤ Finset.sum (Finset.range r)
        (fun j => (2 : ℝ) ^ j * wilkinsonProblem42BlockValue t j) := by
    refine Finset.sum_nonneg ?_
    intro j hj
    have hjlt : j < r := by
      simpa using hj
    have hblock : 0 ≤ wilkinsonProblem42BlockValue t j :=
      wilkinsonProblem42BlockValue_nonneg_of_le (t := t) (j := j) (by omega)
    exact mul_nonneg (pow_nonneg (by norm_num : (0 : ℝ) ≤ 2) j) hblock
  unfold wilkinsonProblem42ExactSum
  linarith

/-- Nonzero-denominator form of `wilkinsonProblem42ExactSum_pos_of_le`. -/
theorem wilkinsonProblem42ExactSum_ne_zero_of_le {t r : ℕ} (hr : r ≤ t + 1) :
    wilkinsonProblem42ExactSum t r ≠ 0 :=
  ne_of_gt (wilkinsonProblem42ExactSum_pos_of_le hr)

/-- Equation (4.3), specialized to Wilkinson's Problem 4.2 source vector. -/
theorem wilkinsonProblem42_recursiveSum_running_error_bound
    (fp : FPModel) (t r : ℕ) :
    |fl_recursiveSum fp (2 ^ r) (wilkinsonProblem42Vector t r) -
        wilkinsonProblem42ExactSum t r| ≤
      fp.u * ∑ i : Fin (2 ^ r),
        |fl_partialSums fp (wilkinsonProblem42Vector t r) i| := by
  simpa [wilkinsonProblem42Vector_sum_eq] using
    (recursiveSum_running_error_bound fp (2 ^ r)
      (wilkinsonProblem42Vector t r))

/-- Equation (4.4), specialized to Wilkinson's source family in the
nonnegative source regime. -/
theorem wilkinsonProblem42_recursiveSum_forward_error_bound
    (fp : FPModel) {t r : ℕ} (hr : r ≤ t + 1)
    (hvalid : gammaValid fp (2 ^ r - 1)) :
    |fl_recursiveSum fp (2 ^ r) (wilkinsonProblem42Vector t r) -
        wilkinsonProblem42ExactSum t r| ≤
      gamma fp (2 ^ r - 1) * wilkinsonProblem42ExactSum t r := by
  have hbound := recursiveSum_forward_error_bound fp (2 ^ r)
    (wilkinsonProblem42Vector t r) hvalid
  simpa [wilkinsonProblem42Vector_sum_eq, wilkinsonProblem42Vector_sum_abs_eq hr]
    using hbound

/-- Relative-error form of the Wilkinson-specialized recursive-summation
`gamma` bound. -/
theorem wilkinsonProblem42_recursiveSum_relError_le_gamma
    (fp : FPModel) {t r : ℕ} (hr : r ≤ t + 1)
    (hvalid : gammaValid fp (2 ^ r - 1)) :
    relError (fl_recursiveSum fp (2 ^ r) (wilkinsonProblem42Vector t r))
        (wilkinsonProblem42ExactSum t r) ≤
      gamma fp (2 ^ r - 1) := by
  have hsum' :
      (∑ i : Fin (2 ^ r), wilkinsonProblem42Vector t r i) ≠ 0 := by
    simpa [wilkinsonProblem42Vector_sum_eq] using
      wilkinsonProblem42ExactSum_ne_zero_of_le hr
  have h := recursiveSum_relError_le_gamma_of_oneSigned fp (2 ^ r)
    (wilkinsonProblem42Vector t r) hvalid
    (wilkinsonProblem42Vector_oneSigned_of_le hr) hsum'
  simpa [wilkinsonProblem42Vector_sum_eq] using h

/-- Source-shaped `n*u` relative-error corollary for the powers-of-two length
`n = 2^r` in Wilkinson's Problem 4.2 family. -/
theorem wilkinsonProblem42_recursiveSum_relError_le_pow_mul_u
    (fp : FPModel) {t r : ℕ} (hr : r ≤ t + 1)
    (hvalid : gammaValid fp (2 ^ r - 1))
    (hsmall : ((2 ^ r : ℕ) : ℝ) *
        (((2 ^ r - 1 : ℕ) : ℝ) * fp.u) ≤ 1) :
    relError (fl_recursiveSum fp (2 ^ r) (wilkinsonProblem42Vector t r))
        (wilkinsonProblem42ExactSum t r) ≤
      ((2 ^ r : ℕ) : ℝ) * fp.u := by
  have hn_pos : 0 < 2 ^ r := Nat.two_pow_pos r
  have hsum' :
      (∑ i : Fin (2 ^ r), wilkinsonProblem42Vector t r i) ≠ 0 := by
    simpa [wilkinsonProblem42Vector_sum_eq] using
      wilkinsonProblem42ExactSum_ne_zero_of_le hr
  have h := recursiveSum_relError_le_n_mul_u_of_oneSigned fp (2 ^ r)
    hn_pos hvalid hsmall (wilkinsonProblem42Vector t r)
    (wilkinsonProblem42Vector_oneSigned_of_le hr) hsum'
  simpa [wilkinsonProblem42Vector_sum_eq] using h

end NumStability
