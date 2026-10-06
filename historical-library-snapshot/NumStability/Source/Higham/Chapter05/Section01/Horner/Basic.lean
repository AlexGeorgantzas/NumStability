import Mathlib.Data.Real.Basic
import Mathlib.Tactic
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Ring
import NumStability.Algorithms.PolynomialEvaluation.ElementaryErrorBounds
import NumStability.Analysis.FloatingPointArithmetic.IeeeSpecialValueOperations.Results
import NumStability.Analysis.ForwardError
import NumStability.Analysis.MatrixAlgebra
import NumStability.Analysis.Rounding
import NumStability.FloatingPoint.Model
import NumStability.Source.Higham.Chapter05.Section03.LejaOrdering.Basic

/-!
# Chapter05 Section01 Horner Basic

Canonical destination for material split out of
`NumStability.Algorithms.Horner` by wave W12 of the August 2026 repository reorganization.
Declaration names, statements and proofs are unchanged; only the
module they live in has changed. The historical module still
resolves and re-exports this one.
-/

open scoped BigOperators

namespace NumStability

/-- Higham, 2nd ed., Chapter 5, Section 5.1:
one exact Horner update `y <- x*y + a`. -/
def hornerStep (x y a : ℝ) : ℝ :=
  x * y + a

/-- Higham, 2nd ed., Chapter 5, Section 5.1:
exact Horner evaluation from coefficients in descending order. -/
def hornerDesc (x : ℝ) : List ℝ → ℝ
  | [] => 0
  | a :: rest => rest.foldl (hornerStep x) a

/-- Higham, 2nd ed., Chapter 5, equation (5.1), written for descending
coefficients `[a_n, ..., a_0]`. -/
noncomputable def polyDesc (x : ℝ) : List ℝ → ℝ
  | [] => 0
  | a :: rest => a * x ^ rest.length + polyDesc x rest

/-- The absolute-coefficient majorant polynomial used in the forward Horner
bound (5.3), written for descending coefficients. -/
noncomputable def polyDescAbs (x : ℝ) : List ℝ → ℝ
  | [] => 0
  | a :: rest => |a| * |x| ^ rest.length + polyDescAbs x rest

lemma hornerFold_eq_acc_mul_pow_add_polyDesc (x : ℝ) :
    ∀ (rest : List ℝ) (y : ℝ),
      rest.foldl (hornerStep x) y =
        y * x ^ rest.length + polyDesc x rest := by
  intro rest
  induction rest with
  | nil =>
      intro y
      simp [polyDesc]
  | cons a rest ih =>
      intro y
      simp [List.foldl, hornerStep, polyDesc, ih, pow_succ]
      ring

/-- Exact Horner evaluation is the displayed monomial polynomial (5.1), for
descending coefficient lists. -/
theorem hornerDesc_eq_polyDesc (x : ℝ) (coeffsDesc : List ℝ) :
    hornerDesc x coeffsDesc = polyDesc x coeffsDesc := by
  cases coeffsDesc with
  | nil => rfl
  | cons a rest =>
      simpa [hornerDesc, polyDesc]
        using hornerFold_eq_acc_mul_pow_add_polyDesc x rest a

/-- The absolute majorant polynomial has nonnegative value. -/
theorem polyDescAbs_nonneg (x : ℝ) :
    ∀ coeffsDesc : List ℝ, 0 ≤ polyDescAbs x coeffsDesc := by
  intro coeffsDesc
  induction coeffsDesc with
  | nil =>
      simp [polyDescAbs]
  | cons a rest ih =>
      have hterm : 0 ≤ |a| * |x| ^ rest.length :=
        mul_nonneg (abs_nonneg a) (pow_nonneg (abs_nonneg x) _)
      simp [polyDescAbs]
      exact add_nonneg hterm ih

/-- The absolute value of a polynomial is bounded by its absolute-coefficient
majorant. -/
theorem abs_polyDesc_le_polyDescAbs (x : ℝ) :
    ∀ coeffsDesc : List ℝ, |polyDesc x coeffsDesc| ≤ polyDescAbs x coeffsDesc := by
  intro coeffsDesc
  induction coeffsDesc with
  | nil =>
      simp [polyDesc, polyDescAbs]
  | cons a rest ih =>
      have hterm :
          |a * x ^ rest.length| ≤ |a| * |x| ^ rest.length := by
        rw [abs_mul, abs_pow]
      have htri :
          |a * x ^ rest.length + polyDesc x rest| ≤
            |a * x ^ rest.length| + |polyDesc x rest| :=
        abs_add_le _ _
      have hsum :
          |a * x ^ rest.length| + |polyDesc x rest| ≤
            |a| * |x| ^ rest.length + polyDescAbs x rest :=
        add_le_add hterm ih
      simpa [polyDesc, polyDescAbs] using le_trans htri hsum

/-- One exact differentiated-Horner update on the unscaled Taylor coefficients
`c_i = p^(i)(alpha)/i!`.  The zero coefficient follows ordinary Horner, while
`c_{i+1}` follows the differentiated recurrence
`c_{i+1} <- alpha*c_{i+1} + c_i`. -/
noncomputable def hornerTaylorFunctionStep
    (alpha a : ℝ) (coeff : ℕ → ℝ) : ℕ → ℝ
  | 0 => alpha * coeff 0 + a
  | i + 1 => alpha * coeff (i + 1) + coeff i

/-- The unscaled Taylor-coefficient state obtained by differentiating Horner's
recurrence through all coefficients.  Entry `i` is the quantity that Algorithm
5.2 stores before the final multiplication by `i!`. -/
noncomputable def hornerTaylorFunctionDesc
    (alpha : ℝ) : List ℝ → ℕ → ℝ
  | [] => fun _ => 0
  | a :: rest =>
      rest.foldl
        (fun coeff b => hornerTaylorFunctionStep alpha b coeff)
        (fun
          | 0 => a
          | _ + 1 => 0)

theorem hornerTaylorFunctionStep_zero
    (alpha a : ℝ) (coeff : ℕ → ℝ) :
    hornerTaylorFunctionStep alpha a coeff 0 = alpha * coeff 0 + a := rfl

theorem hornerTaylorFunctionStep_succ
    (alpha a : ℝ) (coeff : ℕ → ℝ) (i : ℕ) :
    hornerTaylorFunctionStep alpha a coeff (i + 1) =
      alpha * coeff (i + 1) + coeff i := rfl

lemma hornerTaylorFunctionFold_zero_eq_hornerFold
    (alpha : ℝ) :
    ∀ (rest : List ℝ) (coeff : ℕ → ℝ),
      (rest.foldl
          (fun c b => hornerTaylorFunctionStep alpha b c) coeff) 0 =
        rest.foldl (hornerStep alpha) (coeff 0) := by
  intro rest
  induction rest with
  | nil =>
      intro coeff
      simp
  | cons a rest ih =>
      intro coeff
      simpa [List.foldl, hornerTaylorFunctionStep, hornerStep] using
        ih (hornerTaylorFunctionStep alpha a coeff)

/-- The zeroth differentiated-Horner Taylor coefficient is the polynomial value. -/
theorem hornerTaylorFunctionDesc_zero_eq_polyDesc
    (alpha : ℝ) (coeffsDesc : List ℝ) :
    hornerTaylorFunctionDesc alpha coeffsDesc 0 =
      polyDesc alpha coeffsDesc := by
  cases coeffsDesc with
  | nil =>
      simp [hornerTaylorFunctionDesc, polyDesc]
  | cons a rest =>
      have hfold :=
        hornerTaylorFunctionFold_zero_eq_hornerFold alpha rest
          (fun
            | 0 => a
            | _ + 1 => 0)
      have hhorner := hornerDesc_eq_polyDesc alpha (a :: rest)
      simpa [hornerTaylorFunctionDesc, hornerDesc] using
        Eq.trans hfold hhorner

theorem IsLejaOrdering.first_abs_max
    {nodes : ℕ → ℝ} {n i : ℕ}
    (hLeja : IsLejaOrdering nodes n) (hi : i ≤ n) :
    |nodes i| ≤ |nodes 0| :=
  hLeja.1 i hi

theorem IsLejaOrdering.step_product_max
    {nodes : ℕ → ℝ} {n j i : ℕ}
    (hLeja : IsLejaOrdering nodes n)
    (hj0 : 1 ≤ j) (hjn : j < n)
    (hji : j ≤ i) (hin : i ≤ n) :
    lejaPrefixProduct nodes j i ≤ lejaPrefixProduct nodes j j :=
  hLeja.2 j hj0 hjn i hji hin

/-- Coefficients in ascending order `[a_0, a_1, ..., a_n]` denote
`a_0 + a_1*x + ... + a_n*x^n`. -/
noncomputable def polyAsc (x : ℝ) : List ℝ → ℝ
  | [] => 0
  | a :: rest => a + x * polyAsc x rest

/-- Horner evaluation for ascending coefficient lists, implemented by recursing
to the tail and then applying one Horner update `a + x*tail`. -/
noncomputable def fl_hornerAsc
    (fp : FPModel) (x : ℝ) : List ℝ → ℝ
  | [] => 0
  | a :: rest => fp.fl_add a (fp.fl_mul x (fl_hornerAsc fp x rest))

/-- Recursive finite forward-error budget for `fl_hornerAsc`. -/
noncomputable def hornerAscForwardBudget
    (fp : FPModel) (x : ℝ) : List ℝ → ℝ
  | [] => 0
  | a :: rest =>
      let tailhat := fl_hornerAsc fp x rest
      let epsTail := hornerAscForwardBudget fp x rest
      let prodhat := fp.fl_mul x tailhat
      let epsProd := fp.u * |x * tailhat| + |x| * epsTail
      fp.u * |a + prodhat| + epsProd

/-- Finite forward-error bound for Horner evaluation of ascending coefficient
lists. -/
theorem fl_hornerAsc_forward_error_bound
    (fp : FPModel) (x : ℝ) :
    ∀ coeffsAsc : List ℝ,
      |fl_hornerAsc fp x coeffsAsc - polyAsc x coeffsAsc| ≤
        hornerAscForwardBudget fp x coeffsAsc := by
  intro coeffsAsc
  induction coeffsAsc with
  | nil =>
      simp [fl_hornerAsc, polyAsc, hornerAscForwardBudget]
  | cons a rest ih =>
      let tailhat : ℝ := fl_hornerAsc fp x rest
      let tail : ℝ := polyAsc x rest
      let epsTail : ℝ := hornerAscForwardBudget fp x rest
      let prodhat : ℝ := fp.fl_mul x tailhat
      let prod : ℝ := x * tail
      let epsProd : ℝ := fp.u * |x * tailhat| + |x| * epsTail
      have hprod : |prodhat - prod| ≤ epsProd := by
        simpa [tailhat, tail, epsTail, prodhat, prod, epsProd] using
          fl_mul_error_of_operand_error fp x tailhat tail epsTail ih
      have hadd :
          |fp.fl_add a prodhat - (a + prod)| ≤
            fp.u * |a + prodhat| + epsProd := by
        have h :=
          fl_add_error_of_operand_errors fp a a prodhat prod 0 epsProd
            (by simp) hprod
        linarith
      simpa [fl_hornerAsc, polyAsc, hornerAscForwardBudget,
        tailhat, tail, epsTail, prodhat, prod, epsProd] using hadd

/-- Recursive argument-perturbation budget for an exact ascending polynomial. -/
noncomputable def polyAscArgErrorBudget
    (xhat x : ℝ) : List ℝ → ℝ → ℝ
  | [], _epsX => 0
  | _a :: rest, epsX =>
      |xhat| * polyAscArgErrorBudget xhat x rest epsX +
        epsX * |polyAsc x rest|

theorem polyAsc_arg_error_bound
    (xhat x epsX : ℝ) :
    ∀ coeffsAsc : List ℝ,
      |xhat - x| ≤ epsX →
      |polyAsc xhat coeffsAsc - polyAsc x coeffsAsc| ≤
        polyAscArgErrorBudget xhat x coeffsAsc epsX := by
  intro coeffsAsc
  induction coeffsAsc with
  | nil =>
      intro _h
      simp [polyAsc, polyAscArgErrorBudget]
  | cons a rest ih =>
      intro harg
      have ihrest := ih harg
      have hdecomp :
          polyAsc xhat (a :: rest) - polyAsc x (a :: rest) =
            xhat * (polyAsc xhat rest - polyAsc x rest) +
              (xhat - x) * polyAsc x rest := by
        simp [polyAsc]
        ring
      have hfirst :
          |xhat * (polyAsc xhat rest - polyAsc x rest)| ≤
            |xhat| * polyAscArgErrorBudget xhat x rest epsX := by
        rw [abs_mul]
        exact mul_le_mul_of_nonneg_left ihrest (abs_nonneg xhat)
      have hsecond :
          |(xhat - x) * polyAsc x rest| ≤
            epsX * |polyAsc x rest| := by
        rw [abs_mul]
        exact mul_le_mul_of_nonneg_right harg (abs_nonneg _)
      calc
        |polyAsc xhat (a :: rest) - polyAsc x (a :: rest)|
            = |xhat * (polyAsc xhat rest - polyAsc x rest) +
                (xhat - x) * polyAsc x rest| := by
              rw [hdecomp]
        _ ≤ |xhat * (polyAsc xhat rest - polyAsc x rest)| +
              |(xhat - x) * polyAsc x rest| :=
            abs_add_le _ _
        _ ≤ |xhat| * polyAscArgErrorBudget xhat x rest epsX +
              epsX * |polyAsc x rest| :=
            add_le_add hfirst hsecond
        _ = polyAscArgErrorBudget xhat x (a :: rest) epsX := by
            simp [polyAscArgErrorBudget]

/-- A pair-list version of the descending polynomial, used to state
coefficientwise perturbation bounds without extra length hypotheses. -/
noncomputable def polyDescPairs (x : ℝ) : List (ℝ × ℝ) → ℝ
  | [] => 0
  | p :: rest => p.1 * x ^ rest.length + polyDescPairs x rest

/-- A pair-list polynomial in which each coefficient is scaled by `1 + theta`. -/
noncomputable def polyDescPairsPerturbed (x : ℝ) : List (ℝ × ℝ) → ℝ
  | [] => 0
  | p :: rest => p.1 * (1 + p.2) * x ^ rest.length +
      polyDescPairsPerturbed x rest

/-- The absolute-coefficient majorant for `polyDescPairs`. -/
noncomputable def polyDescPairsAbs (x : ℝ) : List (ℝ × ℝ) → ℝ
  | [] => 0
  | p :: rest => |p.1| * |x| ^ rest.length + polyDescPairsAbs x rest

theorem polyDescPairs_eq_polyDesc_map_fst (x : ℝ) :
    ∀ pairs : List (ℝ × ℝ),
      polyDescPairs x pairs = polyDesc x (pairs.map Prod.fst) := by
  intro pairs
  induction pairs with
  | nil =>
      simp [polyDescPairs, polyDesc]
  | cons p rest ih =>
      simp [polyDescPairs, polyDesc, ih]

theorem polyDescPairsAbs_eq_polyDescAbs_map_fst (x : ℝ) :
    ∀ pairs : List (ℝ × ℝ),
      polyDescPairsAbs x pairs = polyDescAbs x (pairs.map Prod.fst) := by
  intro pairs
  induction pairs with
  | nil =>
      simp [polyDescPairsAbs, polyDescAbs]
  | cons p rest ih =>
      simp [polyDescPairsAbs, polyDescAbs, ih]

/-- Forward-error adapter for Higham (5.3): once a backward-error expansion
has coefficient factors `1 + theta_i`, uniformly bounded `theta_i` perturb the
polynomial value by at most the bound times the absolute-coefficient majorant. -/
theorem abs_polyDescPairsPerturbed_sub_polyDescPairs_le
    (x eta : ℝ) (_heta : 0 ≤ eta) :
    ∀ pairs : List (ℝ × ℝ),
      (∀ p ∈ pairs, |p.2| ≤ eta) →
      |polyDescPairsPerturbed x pairs - polyDescPairs x pairs| ≤
        eta * polyDescPairsAbs x pairs := by
  intro pairs
  induction pairs with
  | nil =>
      intro _
      simp [polyDescPairsPerturbed, polyDescPairs, polyDescPairsAbs]
  | cons p rest ih =>
      intro htheta
      have hp : |p.2| ≤ eta := htheta p (by simp)
      have hrest : ∀ q ∈ rest, |q.2| ≤ eta := by
        intro q hq
        exact htheta q (by simp [hq])
      have ihrest := ih hrest
      have hdiff :
          polyDescPairsPerturbed x (p :: rest) -
              polyDescPairs x (p :: rest) =
            p.1 * p.2 * x ^ rest.length +
              (polyDescPairsPerturbed x rest - polyDescPairs x rest) := by
        simp [polyDescPairsPerturbed, polyDescPairs]
        ring
      have hfirst :
          |p.1 * p.2 * x ^ rest.length| ≤
            eta * (|p.1| * |x| ^ rest.length) := by
        calc
          |p.1 * p.2 * x ^ rest.length| =
              |p.2| * (|p.1| * |x| ^ rest.length) := by
                rw [abs_mul, abs_mul, abs_pow]
                ring
          _ ≤ eta * (|p.1| * |x| ^ rest.length) :=
              mul_le_mul_of_nonneg_right hp
                (mul_nonneg (abs_nonneg p.1)
                  (pow_nonneg (abs_nonneg x) rest.length))
      have htri :
          |p.1 * p.2 * x ^ rest.length +
              (polyDescPairsPerturbed x rest - polyDescPairs x rest)| ≤
            |p.1 * p.2 * x ^ rest.length| +
              |polyDescPairsPerturbed x rest - polyDescPairs x rest| :=
        abs_add_le _ _
      have hsum :
          |p.1 * p.2 * x ^ rest.length| +
              |polyDescPairsPerturbed x rest - polyDescPairs x rest| ≤
            eta * (|p.1| * |x| ^ rest.length) +
              eta * polyDescPairsAbs x rest :=
        add_le_add hfirst ihrest
      have hfactor :
          eta * (|p.1| * |x| ^ rest.length) +
              eta * polyDescPairsAbs x rest =
            eta * (|p.1| * |x| ^ rest.length +
              polyDescPairsAbs x rest) := by
        ring
      rw [hdiff]
      exact le_trans htri
        (by simpa [polyDescPairsAbs, hfactor] using hsum)

/-- Higham, 2nd ed., Chapter 5, Section 5.1:
one rounded Horner update `y <- fl(x*y + a)`. -/
noncomputable def fl_hornerStep (fp : FPModel) (x y a : ℝ) : ℝ :=
  fp.fl_add (fp.fl_mul x y) a

/-- Higham, 2nd ed., Chapter 5, Section 5.1, local Horner step model:
one rounded Horner update is a rounded multiplication followed by a rounded
addition, with each local relative error bounded by the unit roundoff. -/
theorem fl_hornerStep_unroll (fp : FPModel) (x y a : ℝ) :
    ∃ δmul δadd : ℝ,
      |δmul| ≤ fp.u ∧
      |δadd| ≤ fp.u ∧
      fl_hornerStep fp x y a =
        ((x * y) * (1 + δmul) + a) * (1 + δadd) := by
  obtain ⟨δmul, hδmul, hmul⟩ := fp.model_mul x y
  obtain ⟨δadd, hδadd, hadd⟩ := fp.model_add (fp.fl_mul x y) a
  refine ⟨δmul, δadd, hδmul, hδadd, ?_⟩
  unfold fl_hornerStep
  rw [hadd, hmul]

/-- Forward-form local error bound for one rounded Horner step.  This is the
direct consequence of the `FPModel` standard model; the source running-error
recurrence additionally needs the inverse-form replacement of the pre-add
quantity by the rounded step value. -/
theorem fl_hornerStep_forward_local_error_bound
    (fp : FPModel) (x y a : ℝ) :
    |fl_hornerStep fp x y a - hornerStep x y a| ≤
      fp.u * (|x| * |y| + |fp.fl_mul x y + a|) := by
  obtain ⟨deltaMul, hdeltaMul, hmul⟩ := fp.model_mul x y
  obtain ⟨deltaAdd, hdeltaAdd, hadd⟩ := fp.model_add (fp.fl_mul x y) a
  have hdiff :
      fl_hornerStep fp x y a - hornerStep x y a =
        (x * y) * deltaMul + (fp.fl_mul x y + a) * deltaAdd := by
    unfold fl_hornerStep hornerStep
    rw [hadd, hmul]
    ring
  rw [hdiff]
  calc
    |x * y * deltaMul + (fp.fl_mul x y + a) * deltaAdd| ≤
        |x * y * deltaMul| + |(fp.fl_mul x y + a) * deltaAdd| :=
          abs_add_le _ _
    _ = |x| * |y| * |deltaMul| +
        |fp.fl_mul x y + a| * |deltaAdd| := by
          rw [abs_mul, abs_mul, abs_mul]
    _ ≤ |x| * |y| * fp.u + |fp.fl_mul x y + a| * fp.u := by
          exact add_le_add
            (mul_le_mul_of_nonneg_left hdeltaMul
              (mul_nonneg (abs_nonneg x) (abs_nonneg y)))
            (mul_le_mul_of_nonneg_left hdeltaAdd (abs_nonneg _))
    _ = fp.u * (|x| * |y| + |fp.fl_mul x y + a|) := by
          ring

/-- Algebraic Horner-step bridge used by Higham (5.4): a forward
multiplication estimate plus an inverse addition estimate give the local
source-shaped inverse Horner estimate. -/
theorem hornerStep_abs_error_le_of_mul_forward_add_inverse
    {u x y a m yr : ℝ}
    (hmul : |m - x * y| ≤ u * |x * y|)
    (hadd : |m + a - yr| ≤ u * |yr|) :
    |yr - hornerStep x y a| ≤ u * (|x| * |y| + |yr|) := by
  have hadd' : |yr - (m + a)| ≤ u * |yr| := by
    simpa [abs_sub_comm] using hadd
  have hsplit :
      yr - hornerStep x y a = (yr - (m + a)) + (m - x * y) := by
    unfold hornerStep
    ring
  have htri :
      |yr - hornerStep x y a| ≤ |yr - (m + a)| + |m - x * y| := by
    rw [hsplit]
    exact abs_add_le _ _
  calc
    |yr - hornerStep x y a| ≤ |yr - (m + a)| + |m - x * y| := htri
    _ ≤ u * |yr| + u * |x * y| := add_le_add hadd' hmul
    _ = u * (|x| * |y| + |yr|) := by
        rw [abs_mul]
        ring

/-- Additive-residual variant of the local Horner-step bridge.  This is the
shape needed when underflow is modeled by absolute error terms instead of pure
relative-error estimates. -/
theorem hornerStep_abs_error_le_of_mul_add_error_bounds
    {u x y a m yr τmul τadd : ℝ}
    (hmul : |m - x * y| ≤ u * |x * y| + τmul)
    (hadd : |m + a - yr| ≤ u * |yr| + τadd) :
    |yr - hornerStep x y a| ≤
      u * (|x| * |y| + |yr|) + τmul + τadd := by
  have hadd' : |yr - (m + a)| ≤ u * |yr| + τadd := by
    simpa [abs_sub_comm] using hadd
  have hsplit :
      yr - hornerStep x y a = (yr - (m + a)) + (m - x * y) := by
    unfold hornerStep
    ring
  have htri :
      |yr - hornerStep x y a| ≤ |yr - (m + a)| + |m - x * y| := by
    rw [hsplit]
    exact abs_add_le _ _
  calc
    |yr - hornerStep x y a| ≤ |yr - (m + a)| + |m - x * y| := htri
    _ ≤ (u * |yr| + τadd) + (u * |x * y| + τmul) :=
        add_le_add hadd' hmul
    _ = u * (|x| * |y| + |yr|) + τmul + τadd := by
        rw [abs_mul]
        ring

/-- Higham, 2nd ed., Chapter 5, equation (5.4), for the concrete finite
round-to-even primitive-operation branch.

The inverse local Horner estimate follows from the finite-normal branch of
Higham's models (2.4) and (2.5): the multiplication result must be in finite
normal range, and the exact addition input formed from the rounded product
must also be in finite normal range. -/
theorem finiteRoundToEvenOp_hornerStep_inverseLocalError_of_finiteNormalRange
    {fmt : FloatingPointFormat} {x y a : ℝ}
    (hmul : fmt.finiteNormalRange (x * y))
    (hadd : fmt.finiteNormalRange
      (fmt.finiteRoundToEvenOp BasicOp.mul x y + a)) :
    |fmt.finiteRoundToEvenOp BasicOp.add
        (fmt.finiteRoundToEvenOp BasicOp.mul x y) a -
      hornerStep x y a| ≤
    fmt.unitRoundoff *
      (|x| * |y| +
       |fmt.finiteRoundToEvenOp BasicOp.add
          (fmt.finiteRoundToEvenOp BasicOp.mul x y) a|) := by
  let m := fmt.finiteRoundToEvenOp BasicOp.mul x y
  let yr := fmt.finiteRoundToEvenOp BasicOp.add m a
  rcases
    fmt.finiteRoundToEvenOp_standardModel_lt_of_finiteNormalRange
      (op := BasicOp.mul) (x := x) (y := y) hmul with
    ⟨δm, hδm_lt, hm_eq⟩
  have hδm : |δm| ≤ fmt.unitRoundoff := le_of_lt hδm_lt
  have hmul_abs : |m - x * y| ≤ fmt.unitRoundoff * |x * y| := by
    have hdiff : m - x * y = (x * y) * δm := by
      simp [m, hm_eq, BasicOp.exact]
      ring
    calc
      |m - x * y| = |x * y| * |δm| := by rw [hdiff, abs_mul]
      _ ≤ |x * y| * fmt.unitRoundoff :=
          mul_le_mul_of_nonneg_left hδm (abs_nonneg _)
      _ = fmt.unitRoundoff * |x * y| := by ring
  have hadd_inv :
      inverseRelErrorModel yr (m + a) fmt.unitRoundoff := by
    rcases
      fmt.finiteRoundToEvenOp_inverseRelErrorWitness_of_finiteNormalRange
        (op := BasicOp.add) (x := m) (y := a) hadd with
      ⟨δa, _hr, hδa, hwit⟩
    exact ⟨δa, hδa, hwit⟩
  have hadd_abs : |(m + a) - yr| ≤ fmt.unitRoundoff * |yr| :=
    inverseRelErrorModel_abs_exact_sub_computed_le yr (m + a)
      fmt.unitRoundoff hadd_inv
  simpa [m, yr] using
    hornerStep_abs_error_le_of_mul_forward_add_inverse
      (u := fmt.unitRoundoff) (x := x) (y := y) (a := a)
      (m := m) (yr := yr) hmul_abs hadd_abs

/-- Higham, 2nd ed., Chapter 5, Section 5.1:
rounded Horner evaluation from coefficients in descending order. -/
noncomputable def fl_hornerDesc (fp : FPModel) (x : ℝ) : List ℝ → ℝ
  | [] => 0
  | a :: rest => rest.foldl (fl_hornerStep fp x) a

/-- Rounded Horner evaluation that starts from a zero accumulator.

This is the form naturally produced by the derivative component of
Algorithm 5.2 when it evaluates the synthetic-division quotient coefficients:
the first derivative update is still a rounded multiply/add applied to the
initial zero derivative accumulator. -/
noncomputable def fl_hornerFoldFromZeroDesc
    (fp : FPModel) (x : ℝ) (coeffsDesc : List ℝ) : ℝ :=
  coeffsDesc.foldl (fl_hornerStep fp x) 0

/-- Exact Horner evaluation from a zero accumulator is still the displayed
descending polynomial. -/
theorem hornerFoldFromZeroDesc_eq_polyDesc (x : ℝ)
    (coeffsDesc : List ℝ) :
    coeffsDesc.foldl (hornerStep x) 0 = polyDesc x coeffsDesc := by
  simpa using hornerFold_eq_acc_mul_pow_add_polyDesc x coeffsDesc 0

/-- One rounded all-order Taylor-coefficient update from Algorithm 5.2.
All successor entries read the old state, matching the source's descending
inner loop.  Each entry performs the same rounded multiply-then-add sequence
as `fl_hornerStep`. -/
noncomputable def fl_hornerTaylorFunctionStep
    (fp : FPModel) (alpha a : ℝ) (coeff : ℕ → ℝ) : ℕ → ℝ
  | 0 => fl_hornerStep fp alpha (coeff 0) a
  | i + 1 => fl_hornerStep fp alpha (coeff (i + 1)) (coeff i)

/-- The actual rounded all-order Horner/Taylor state before factorial scaling. -/
noncomputable def fl_hornerTaylorFunctionDesc
    (fp : FPModel) (alpha : ℝ) : List ℝ → ℕ → ℝ
  | [] => fun _ => 0
  | a :: rest =>
      rest.foldl
        (fun coeff b => fl_hornerTaylorFunctionStep fp alpha b coeff)
        (fun
          | 0 => a
          | _ + 1 => 0)

/-- One forward-error budget update for the rounded all-order state.  It
contains both primitive-operation residuals and propagation of the incoming
state errors. -/
noncomputable def fl_hornerTaylorFunctionForwardBudgetStep
    (fp : FPModel) (alpha a : ℝ)
    (coeffHat budget : ℕ → ℝ) : ℕ → ℝ
  | 0 =>
      fp.u * |fp.fl_mul alpha (coeffHat 0) + a| +
        fp.u * |alpha * coeffHat 0| + |alpha| * budget 0
  | i + 1 =>
      fp.u * |fp.fl_mul alpha (coeffHat (i + 1)) + coeffHat i| +
        fp.u * |alpha * coeffHat (i + 1)| +
          |alpha| * budget (i + 1) + budget i

/-- Propagate the all-order budget through a remaining descending coefficient
list, alongside the actual rounded state that determines each local residual. -/
noncomputable def fl_hornerTaylorFunctionForwardBudgetFold
    (fp : FPModel) (alpha : ℝ) :
    List ℝ → (ℕ → ℝ) → (ℕ → ℝ) → ℕ → ℝ
  | [], _coeffHat, budget => budget
  | a :: rest, coeffHat, budget =>
      fl_hornerTaylorFunctionForwardBudgetFold fp alpha rest
        (fl_hornerTaylorFunctionStep fp alpha a coeffHat)
        (fl_hornerTaylorFunctionForwardBudgetStep fp alpha a coeffHat budget)

/-- End-to-end all-order forward budget, initialized at the exactly represented
leading coefficient and zero higher-order entries. -/
noncomputable def fl_hornerTaylorFunctionForwardBudgetDesc
    (fp : FPModel) (alpha : ℝ) : List ℝ → ℕ → ℝ
  | [] => fun _ => 0
  | a :: rest =>
      fl_hornerTaylorFunctionForwardBudgetFold fp alpha rest
        (fun
          | 0 => a
          | _ + 1 => 0)
        (fun _ => 0)

lemma fl_hornerTaylorFunctionStep_error_bound
    (fp : FPModel) (alpha a : ℝ)
    (coeffHat coeff budget : ℕ → ℝ)
    (hbound : ∀ i, |coeffHat i - coeff i| ≤ budget i) :
    ∀ i,
      |fl_hornerTaylorFunctionStep fp alpha a coeffHat i -
          hornerTaylorFunctionStep alpha a coeff i| ≤
        fl_hornerTaylorFunctionForwardBudgetStep
          fp alpha a coeffHat budget i := by
  intro i
  cases i with
  | zero =>
      have hmul :=
        fl_mul_error_of_operand_error fp alpha
          (coeffHat 0) (coeff 0) (budget 0) (hbound 0)
      have hadd :=
        fl_add_error_of_operand_errors fp
          (fp.fl_mul alpha (coeffHat 0)) (alpha * coeff 0)
          a a
          (fp.u * |alpha * coeffHat 0| + |alpha| * budget 0) 0
          hmul (by simp)
      simpa [fl_hornerTaylorFunctionStep, hornerTaylorFunctionStep,
        fl_hornerStep, fl_hornerTaylorFunctionForwardBudgetStep,
        add_assoc] using hadd
  | succ i =>
      have hmul :=
        fl_mul_error_of_operand_error fp alpha
          (coeffHat (i + 1)) (coeff (i + 1)) (budget (i + 1))
          (hbound (i + 1))
      have hadd :=
        fl_add_error_of_operand_errors fp
          (fp.fl_mul alpha (coeffHat (i + 1))) (alpha * coeff (i + 1))
          (coeffHat i) (coeff i)
          (fp.u * |alpha * coeffHat (i + 1)| +
            |alpha| * budget (i + 1))
          (budget i) hmul (hbound i)
      simpa [fl_hornerTaylorFunctionStep, hornerTaylorFunctionStep,
        fl_hornerStep, fl_hornerTaylorFunctionForwardBudgetStep,
        add_assoc] using hadd

lemma fl_hornerTaylorFunctionFold_error_bound
    (fp : FPModel) (alpha : ℝ) :
    ∀ (rest : List ℝ)
      (coeffHat coeff budget : ℕ → ℝ),
      (∀ i, |coeffHat i - coeff i| ≤ budget i) →
      ∀ i,
        |(rest.foldl
              (fun c b => fl_hornerTaylorFunctionStep fp alpha b c)
              coeffHat) i -
            (rest.foldl
              (fun c b => hornerTaylorFunctionStep alpha b c)
              coeff) i| ≤
          fl_hornerTaylorFunctionForwardBudgetFold
            fp alpha rest coeffHat budget i := by
  intro rest
  induction rest with
  | nil =>
      intro coeffHat coeff budget hbound i
      simpa [fl_hornerTaylorFunctionForwardBudgetFold] using hbound i
  | cons a rest ih =>
      intro coeffHat coeff budget hbound i
      simp only [List.foldl,
        fl_hornerTaylorFunctionForwardBudgetFold]
      exact ih
        (fl_hornerTaylorFunctionStep fp alpha a coeffHat)
        (hornerTaylorFunctionStep alpha a coeff)
        (fl_hornerTaylorFunctionForwardBudgetStep
          fp alpha a coeffHat budget)
        (fl_hornerTaylorFunctionStep_error_bound
          fp alpha a coeffHat coeff budget hbound) i

/-- A genuine executor-to-specification error theorem for every derivative
order.  The left side is the rounded Algorithm 5.2 state; the right side is
the exact Taylor recurrence, and the budget is generated from the same
rounded execution. -/
theorem fl_hornerTaylorFunctionDesc_error_bound
    (fp : FPModel) (alpha : ℝ) (coeffsDesc : List ℝ) (i : ℕ) :
    |fl_hornerTaylorFunctionDesc fp alpha coeffsDesc i -
        hornerTaylorFunctionDesc alpha coeffsDesc i| ≤
      fl_hornerTaylorFunctionForwardBudgetDesc fp alpha coeffsDesc i := by
  cases coeffsDesc with
  | nil =>
      simp [fl_hornerTaylorFunctionDesc, hornerTaylorFunctionDesc,
        fl_hornerTaylorFunctionForwardBudgetDesc]
  | cons a rest =>
      apply fl_hornerTaylorFunctionFold_error_bound fp alpha rest
      intro j
      cases j <;> simp

/-- Higham, 2nd ed., Chapter 5, Algorithm 5.1:
one rounded running-bound state update.  The state is `(y, mu)` before the
final scaling by the unit roundoff, and the `y` component is the rounded Horner
value produced by the same step. -/
noncomputable def fl_hornerRunningStep
    (fp : FPModel) (x : ℝ) (state : ℝ × ℝ) (a : ℝ) : ℝ × ℝ :=
  let y := fl_hornerStep fp x state.1 a
  (y, |x| * state.2 + |y|)

/-- Higham, 2nd ed., Chapter 5, Algorithm 5.1:
rounded state corresponding to the displayed running error-bound recurrence,
before the last assignment `mu = u * (2*mu - |y|)`. -/
noncomputable def fl_hornerRunningState
    (fp : FPModel) (x : ℝ) : List ℝ → ℝ × ℝ
  | [] => (0, 0)
  | a :: rest => rest.foldl (fl_hornerRunningStep fp x) (a, |a| / 2)

/-- Higham, 2nd ed., Chapter 5, Algorithm 5.1:
the final rounded running-bound quantity `u * (2*mu - |y|)`. -/
noncomputable def fl_hornerRunningBound
    (fp : FPModel) (x : ℝ) (coeffsDesc : List ℝ) : ℝ :=
  let state := fl_hornerRunningState fp x coeffsDesc
  fp.u * (2 * state.2 - |state.1|)

lemma fl_hornerRunningFold_fst_eq (fp : FPModel) (x : ℝ) :
    ∀ (rest : List ℝ) (y mu : ℝ),
      (rest.foldl (fl_hornerRunningStep fp x) (y, mu)).1 =
        rest.foldl (fl_hornerStep fp x) y := by
  intro rest
  induction rest with
  | nil =>
      intro y mu
      rfl
  | cons a rest ih =>
      intro y mu
      simp [List.foldl, fl_hornerRunningStep, ih]

/-- In Algorithm 5.1's rounded running-bound state, the first component is the
rounded Horner value. -/
theorem fl_hornerRunningState_fst_eq_fl_hornerDesc
    (fp : FPModel) (x : ℝ) (coeffsDesc : List ℝ) :
    (fl_hornerRunningState fp x coeffsDesc).1 =
      fl_hornerDesc fp x coeffsDesc := by
  cases coeffsDesc with
  | nil => rfl
  | cons a rest =>
      simpa [fl_hornerRunningState, fl_hornerDesc]
        using fl_hornerRunningFold_fst_eq fp x rest a (|a| / 2)

lemma fl_hornerRunningStep_snd_nonneg
    (fp : FPModel) (x a : ℝ) {state : ℝ × ℝ} (hmu : 0 ≤ state.2) :
    0 ≤ (fl_hornerRunningStep fp x state a).2 := by
  simp [fl_hornerRunningStep]
  exact add_nonneg (mul_nonneg (abs_nonneg x) hmu) (abs_nonneg _)

lemma fl_hornerRunningStep_abs_fst_le_two_snd
    (fp : FPModel) (x a : ℝ) {state : ℝ × ℝ} (hmu : 0 ≤ state.2) :
    |(fl_hornerRunningStep fp x state a).1| ≤
      2 * (fl_hornerRunningStep fp x state a).2 := by
  simp [fl_hornerRunningStep]
  have hterm : 0 ≤ |x| * state.2 :=
    mul_nonneg (abs_nonneg x) hmu
  have hy : 0 ≤ |fl_hornerStep fp x state.1 a| := abs_nonneg _
  nlinarith

lemma fl_hornerRunningFold_snd_nonneg (fp : FPModel) (x : ℝ) :
    ∀ (rest : List ℝ) (state : ℝ × ℝ),
      0 ≤ state.2 →
      0 ≤ (rest.foldl (fl_hornerRunningStep fp x) state).2 := by
  intro rest
  induction rest with
  | nil =>
      intro state hmu
      simpa using hmu
  | cons a rest ih =>
      intro state hmu
      exact ih (fl_hornerRunningStep fp x state a)
        (fl_hornerRunningStep_snd_nonneg fp x a hmu)

/-- The unscaled rounded running-bound accumulator in Algorithm 5.1 is
nonnegative. -/
theorem fl_hornerRunningState_mu_nonneg
    (fp : FPModel) (x : ℝ) (coeffsDesc : List ℝ) :
    0 ≤ (fl_hornerRunningState fp x coeffsDesc).2 := by
  cases coeffsDesc with
  | nil =>
      simp [fl_hornerRunningState]
  | cons a rest =>
      have hinit : 0 ≤ |a| / 2 := by positivity
      simpa [fl_hornerRunningState]
        using fl_hornerRunningFold_snd_nonneg fp x rest (a, |a| / 2) hinit

lemma fl_hornerRunningFold_abs_fst_le_two_snd
    (fp : FPModel) (x : ℝ) :
    ∀ (rest : List ℝ) (state : ℝ × ℝ),
      0 ≤ state.2 →
      |state.1| ≤ 2 * state.2 →
      |(rest.foldl (fl_hornerRunningStep fp x) state).1| ≤
        2 * (rest.foldl (fl_hornerRunningStep fp x) state).2 := by
  intro rest
  induction rest with
  | nil =>
      intro state _ hstate
      simpa using hstate
  | cons a rest ih =>
      intro state hmu _hstate
      exact ih (fl_hornerRunningStep fp x state a)
        (fl_hornerRunningStep_snd_nonneg fp x a hmu)
        (fl_hornerRunningStep_abs_fst_le_two_snd fp x a hmu)

/-- In Algorithm 5.1's rounded running-bound state, the final value satisfies
`|y| <= 2*mu`. -/
theorem fl_hornerRunningState_abs_fst_le_two_mu
    (fp : FPModel) (x : ℝ) (coeffsDesc : List ℝ) :
    |(fl_hornerRunningState fp x coeffsDesc).1| ≤
      2 * (fl_hornerRunningState fp x coeffsDesc).2 := by
  cases coeffsDesc with
  | nil =>
      simp [fl_hornerRunningState]
  | cons a rest =>
      have hinit_mu : 0 ≤ |a| / 2 := by positivity
      have hinit_abs : |(a, |a| / 2).1| ≤ 2 * (a, |a| / 2).2 := by
        change |a| ≤ 2 * (|a| / 2)
        have h : (2 : ℝ) * (|a| / 2) = |a| := by ring
        rw [h]
      simpa [fl_hornerRunningState]
        using fl_hornerRunningFold_abs_fst_le_two_snd fp x rest
          (a, |a| / 2) hinit_mu hinit_abs

/-- The Algorithm 5.1 rounded running-bound quantity is nonnegative. -/
theorem fl_hornerRunningBound_nonneg
    (fp : FPModel) (x : ℝ) (coeffsDesc : List ℝ) :
    0 ≤ fl_hornerRunningBound fp x coeffsDesc := by
  unfold fl_hornerRunningBound
  let state := fl_hornerRunningState fp x coeffsDesc
  have hstate :
      |state.1| ≤ 2 * state.2 := by
    simpa [state]
      using fl_hornerRunningState_abs_fst_le_two_mu fp x coeffsDesc
  have hinner : 0 ≤ 2 * state.2 - |state.1| := by
    linarith
  exact mul_nonneg fp.u_nonneg hinner

/-- Source-shaped local inverse-error hypothesis for Higham (5.4).

The abstract `FPModel` gives the standard forward relative-error form for the
two primitive operations in a Horner step.  Algorithm 5.1's a posteriori running
bound uses the inverse local estimate in which the rounded step value appears
on the right-hand side.  This predicate records exactly that local estimate,
without claiming it follows from `FPModel` alone. -/
def hornerStepInverseLocalError (fp : FPModel) (x : ℝ) : Prop :=
  ∀ y a : ℝ,
    |fl_hornerStep fp x y a - hornerStep x y a| ≤
      fp.u * (|x| * |y| + |fl_hornerStep fp x y a|)

lemma fl_hornerRunningStep_error_bound_of_inverseLocal
    (fp : FPModel) (x : ℝ)
    (hlocal : hornerStepInverseLocalError fp x)
    {state : ℝ × ℝ} {yExact : ℝ}
    (_hmu : 0 ≤ state.2)
    (_hstate : |state.1| ≤ 2 * state.2)
    (herr : |state.1 - yExact| ≤
      fp.u * (2 * state.2 - |state.1|))
    (a : ℝ) :
    let next := fl_hornerRunningStep fp x state a
    |next.1 - hornerStep x yExact a| ≤
      fp.u * (2 * next.2 - |next.1|) := by
  let yRound := fl_hornerStep fp x state.1 a
  have hlocalStep :
      |yRound - hornerStep x state.1 a| ≤
        fp.u * (|x| * |state.1| + |yRound|) := by
    simpa [hornerStepInverseLocalError, yRound] using hlocal state.1 a
  have hExactDiff :
      |hornerStep x state.1 a - hornerStep x yExact a| =
        |x| * |state.1 - yExact| := by
    have h :
        hornerStep x state.1 a - hornerStep x yExact a =
          x * (state.1 - yExact) := by
      unfold hornerStep
      ring
    rw [h, abs_mul]
  have hExactBound :
      |hornerStep x state.1 a - hornerStep x yExact a| ≤
        |x| * (fp.u * (2 * state.2 - |state.1|)) := by
    rw [hExactDiff]
    exact mul_le_mul_of_nonneg_left herr (abs_nonneg x)
  have htri :
      |yRound - hornerStep x yExact a| ≤
        |yRound - hornerStep x state.1 a| +
          |hornerStep x state.1 a - hornerStep x yExact a| := by
    have hsplit :
        yRound - hornerStep x yExact a =
          (yRound - hornerStep x state.1 a) +
            (hornerStep x state.1 a - hornerStep x yExact a) := by
      ring
    rw [hsplit]
    exact abs_add_le _ _
  have hsum :
      |yRound - hornerStep x state.1 a| +
          |hornerStep x state.1 a - hornerStep x yExact a| ≤
        fp.u * (|x| * |state.1| + |yRound|) +
          |x| * (fp.u * (2 * state.2 - |state.1|)) :=
    add_le_add hlocalStep hExactBound
  have htarget :
      fp.u * (|x| * |state.1| + |yRound|) +
          |x| * (fp.u * (2 * state.2 - |state.1|)) =
        fp.u * (2 * (|x| * state.2 + |yRound|) - |yRound|) := by
    ring
  have hnext :
      (fl_hornerRunningStep fp x state a).1 = yRound ∧
        (fl_hornerRunningStep fp x state a).2 =
          |x| * state.2 + |yRound| := by
    simp [fl_hornerRunningStep, yRound]
  dsimp
  rw [hnext.1, hnext.2]
  exact le_trans htri (by simpa [htarget] using hsum)

lemma fl_hornerRunningFold_error_bound_of_inverseLocal
    (fp : FPModel) (x : ℝ)
    (hlocal : hornerStepInverseLocalError fp x) :
    ∀ (rest : List ℝ) (yRound yExact mu : ℝ),
      0 ≤ mu →
      |yRound| ≤ 2 * mu →
      |yRound - yExact| ≤ fp.u * (2 * mu - |yRound|) →
      let state := rest.foldl (fl_hornerRunningStep fp x) (yRound, mu)
      |state.1 - rest.foldl (hornerStep x) yExact| ≤
        fp.u * (2 * state.2 - |state.1|) := by
  intro rest
  induction rest with
  | nil =>
      intro yRound yExact mu _hmu _hstate herr
      simpa using herr
  | cons a rest ih =>
      intro yRound yExact mu hmu hstate herr
      let next := fl_hornerRunningStep fp x (yRound, mu) a
      have hstep :
          |next.1 - hornerStep x yExact a| ≤
            fp.u * (2 * next.2 - |next.1|) := by
        simpa [next]
          using fl_hornerRunningStep_error_bound_of_inverseLocal fp x hlocal
            (state := (yRound, mu)) (yExact := yExact)
            hmu hstate herr a
      have hnext_mu : 0 ≤ next.2 := by
        simpa [next]
          using fl_hornerRunningStep_snd_nonneg fp x a
            (state := (yRound, mu)) hmu
      have hnext_abs : |next.1| ≤ 2 * next.2 := by
        simpa [next]
          using fl_hornerRunningStep_abs_fst_le_two_snd fp x a
            (state := (yRound, mu)) hmu
      simpa [List.foldl, next] using
        ih next.1 (hornerStep x yExact a) next.2
          hnext_mu hnext_abs hstep

/-- Higham Algorithm 5.1, source-shaped a posteriori running bound.

Under the inverse local Horner-step estimate (5.4), the final Algorithm 5.1
quantity bounds the actual Horner evaluation error. -/
theorem fl_hornerDesc_running_error_bound_of_inverseLocal
    (fp : FPModel) (x : ℝ) (coeffsDesc : List ℝ)
    (hlocal : hornerStepInverseLocalError fp x) :
    |fl_hornerDesc fp x coeffsDesc - polyDesc x coeffsDesc| ≤
      fl_hornerRunningBound fp x coeffsDesc := by
  cases coeffsDesc with
  | nil =>
      simp [fl_hornerDesc, polyDesc, fl_hornerRunningBound,
        fl_hornerRunningState]
  | cons a rest =>
      have hmu : 0 ≤ |a| / 2 := by positivity
      have hstate : |a| ≤ 2 * (|a| / 2) := by
        have h : (2 : ℝ) * (|a| / 2) = |a| := by ring
        rw [h]
      have herr : |a - a| ≤ fp.u * (2 * (|a| / 2) - |a|) := by
        have hzero : 2 * (|a| / 2) - |a| = 0 := by ring
        simp [hzero]
      have hfold :=
        fl_hornerRunningFold_error_bound_of_inverseLocal fp x hlocal
          rest a a (|a| / 2) hmu hstate herr
      have hpoly :
          polyDesc x (a :: rest) = rest.foldl (hornerStep x) a := by
        rw [← hornerDesc_eq_polyDesc x (a :: rest)]
        rfl
      let state := rest.foldl (fl_hornerRunningStep fp x) (a, |a| / 2)
      have hfst : state.1 = rest.foldl (fl_hornerStep fp x) a := by
        simpa [state]
          using fl_hornerRunningFold_fst_eq fp x rest a (|a| / 2)
      simpa [fl_hornerDesc, fl_hornerRunningBound,
        fl_hornerRunningState, hpoly, state, hfst] using hfold

theorem fl_hornerFold_backward_error_coefficients
    (fp : FPModel) (x : ℝ) :
    ∀ (rest : List ℝ) (y : ℝ),
      gammaValid fp (2 * rest.length) →
      ∃ thetaY : ℝ, ∃ pairs : List (ℝ × ℝ),
        |thetaY| ≤ gamma fp (2 * rest.length) ∧
        pairs.map Prod.fst = rest ∧
        (∀ p ∈ pairs, |p.2| ≤ gamma fp (2 * rest.length)) ∧
        rest.foldl (fl_hornerStep fp x) y =
          y * (1 + thetaY) * x ^ rest.length +
            polyDescPairsPerturbed x pairs := by
  intro rest
  induction rest with
  | nil =>
      intro y hvalid
      refine ⟨0, [], ?_, ?_, ?_, ?_⟩
      · simpa using gamma_nonneg fp hvalid
      · simp
      · intro p hp
        simp at hp
      · simp [polyDescPairsPerturbed]
  | cons a rest ih =>
      intro y hvalid
      have htailValid : gammaValid fp (2 * rest.length) :=
        gammaValid_mono fp (by simp) hvalid
      obtain ⟨thetaTail, pairsTail, hthetaTail, hpairsTail,
        hpairsTailBound, hfoldTail⟩ :=
          ih (fl_hornerStep fp x y a) htailValid
      obtain ⟨deltaMul, hdeltaMul, hmul⟩ := fp.model_mul x y
      obtain ⟨deltaAdd, hdeltaAdd, hadd⟩ := fp.model_add (fp.fl_mul x y) a
      have hstep :
          fl_hornerStep fp x y a =
            ((x * y) * (1 + deltaMul) + a) * (1 + deltaAdd) := by
        unfold fl_hornerStep
        rw [hadd, hmul]
      have hvalid1 : gammaValid fp 1 :=
        gammaValid_mono fp (by simp; omega) hvalid
      have hvalid2 : gammaValid fp 2 :=
        gammaValid_mono fp (by simp) hvalid
      have hvalid1Tail : gammaValid fp (1 + 2 * rest.length) :=
        gammaValid_mono fp (by simp; omega) hvalid
      have hvalid2Tail : gammaValid fp (2 + 2 * rest.length) := by
        have hle : 2 + 2 * rest.length ≤ 2 * (a :: rest).length := by
          simp
          omega
        exact gammaValid_mono fp hle hvalid
      have hdeltaMul1 : |deltaMul| ≤ gamma fp 1 :=
        le_trans hdeltaMul (u_le_gamma fp one_pos hvalid1)
      have hdeltaAdd1 : |deltaAdd| ≤ gamma fp 1 :=
        le_trans hdeltaAdd (u_le_gamma fp one_pos hvalid1)
      obtain ⟨thetaMulAdd, hthetaMulAdd, hthetaMulAddEq⟩ :=
        gamma_mul fp 1 1 deltaMul deltaAdd hdeltaMul1 hdeltaAdd1 hvalid2
      obtain ⟨thetaHead, hthetaHead, hthetaHeadEq⟩ :=
        gamma_mul fp 1 (2 * rest.length) deltaAdd thetaTail hdeltaAdd1
          hthetaTail hvalid1Tail
      obtain ⟨thetaAcc, hthetaAcc, hthetaAccEq⟩ :=
        gamma_mul fp 2 (2 * rest.length) thetaMulAdd thetaTail
          hthetaMulAdd hthetaTail hvalid2Tail
      refine ⟨thetaAcc, (a, thetaHead) :: pairsTail, ?_, ?_, ?_, ?_⟩
      · exact le_trans hthetaAcc (gamma_mono fp (by simp; omega) hvalid)
      · simp [hpairsTail]
      · intro p hp
        simp only [List.mem_cons] at hp
        rcases hp with hp | hp
        · rcases hp
          exact le_trans hthetaHead (gamma_mono fp (by simp; omega) hvalid)
        · exact le_trans (hpairsTailBound p hp)
            (gamma_mono fp (by simp) hvalid)
      · have hpairsLen : pairsTail.length = rest.length := by
          have hlen := congrArg List.length hpairsTail
          simpa using hlen
        have haccProd :
            (1 + deltaMul) * (1 + deltaAdd) * (1 + thetaTail) =
              1 + thetaAcc := by
          rw [hthetaMulAddEq, hthetaAccEq]
        have hheadProd :
            (1 + deltaAdd) * (1 + thetaTail) = 1 + thetaHead :=
          hthetaHeadEq
        simp only [List.foldl]
        rw [hfoldTail, hstep]
        simp [polyDescPairsPerturbed, hpairsLen]
        rw [← haccProd, ← hheadProd, pow_succ]
        ring_nf

/-- Higham (5.2), uniform `gamma_(2n)` form for descending coefficient lists:
rounded Horner evaluation is exact evaluation of a coefficientwise-perturbed
polynomial. -/
theorem fl_hornerDesc_backward_error_coefficients
    (fp : FPModel) (x : ℝ) (coeffsDesc : List ℝ)
    (hvalid : gammaValid fp (2 * (coeffsDesc.length - 1))) :
    ∃ pairs : List (ℝ × ℝ),
      pairs.map Prod.fst = coeffsDesc ∧
      (∀ p ∈ pairs, |p.2| ≤ gamma fp (2 * (coeffsDesc.length - 1))) ∧
      fl_hornerDesc fp x coeffsDesc = polyDescPairsPerturbed x pairs := by
  cases coeffsDesc with
  | nil =>
      refine ⟨[], ?_, ?_, ?_⟩
      · simp
      · intro p hp
        simp at hp
      · rfl
  | cons a rest =>
      have hrestValid : gammaValid fp (2 * rest.length) := by
        simpa using hvalid
      obtain ⟨thetaA, pairsRest, hthetaA, hpairsRest,
        hpairsRestBound, hfold⟩ :=
          fl_hornerFold_backward_error_coefficients fp x rest a hrestValid
      refine ⟨(a, thetaA) :: pairsRest, ?_, ?_, ?_⟩
      · simp [hpairsRest]
      · intro p hp
        simp only [List.mem_cons] at hp
        rcases hp with hp | hp
        · rcases hp
          simpa using hthetaA
        · exact hpairsRestBound p hp
      · have hpairsLen : pairsRest.length = rest.length := by
          have hlen := congrArg List.length hpairsRest
          simpa using hlen
        simpa [fl_hornerDesc, polyDescPairsPerturbed, hpairsLen] using hfold

/-- Higham (5.3), forward-error form following from the coefficientwise
backward-error expansion (5.2). -/
theorem fl_hornerDesc_forward_error_bound
    (fp : FPModel) (x : ℝ) (coeffsDesc : List ℝ)
    (hvalid : gammaValid fp (2 * (coeffsDesc.length - 1))) :
    |fl_hornerDesc fp x coeffsDesc - polyDesc x coeffsDesc| ≤
      gamma fp (2 * (coeffsDesc.length - 1)) * polyDescAbs x coeffsDesc := by
  obtain ⟨pairs, hpairs, hpairsBound, hfl⟩ :=
    fl_hornerDesc_backward_error_coefficients fp x coeffsDesc hvalid
  have hpert :=
    abs_polyDescPairsPerturbed_sub_polyDescPairs_le x
      (gamma fp (2 * (coeffsDesc.length - 1)))
      (gamma_nonneg fp hvalid) pairs hpairsBound
  have hpoly :
      polyDescPairs x pairs = polyDesc x coeffsDesc := by
    rw [polyDescPairs_eq_polyDesc_map_fst, hpairs]
  have habs :
      polyDescPairsAbs x pairs = polyDescAbs x coeffsDesc := by
    rw [polyDescPairsAbs_eq_polyDescAbs_map_fst, hpairs]
  simpa [hfl, hpoly, habs] using hpert

/-- Backward-error expansion for rounded Horner evaluation from a zero
accumulator.  This is the form used by the first-derivative component of
Algorithm 5.2 when it evaluates the computed synthetic-division quotient. -/
theorem fl_hornerFoldFromZeroDesc_backward_error_coefficients
    (fp : FPModel) (x : ℝ) (coeffsDesc : List ℝ)
    (hvalid : gammaValid fp (2 * coeffsDesc.length)) :
    ∃ pairs : List (ℝ × ℝ),
      pairs.map Prod.fst = coeffsDesc ∧
      (∀ p ∈ pairs, |p.2| ≤ gamma fp (2 * coeffsDesc.length)) ∧
      fl_hornerFoldFromZeroDesc fp x coeffsDesc =
        polyDescPairsPerturbed x pairs := by
  obtain ⟨_thetaZero, pairs, _hthetaZero, hpairs, hpairsBound,
    hfold⟩ :=
      fl_hornerFold_backward_error_coefficients fp x coeffsDesc 0 hvalid
  refine ⟨pairs, hpairs, hpairsBound, ?_⟩
  simpa [fl_hornerFoldFromZeroDesc] using hfold

/-- Forward-error bound for rounded Horner evaluation from a zero accumulator. -/
theorem fl_hornerFoldFromZeroDesc_forward_error_bound
    (fp : FPModel) (x : ℝ) (coeffsDesc : List ℝ)
    (hvalid : gammaValid fp (2 * coeffsDesc.length)) :
    |fl_hornerFoldFromZeroDesc fp x coeffsDesc -
        polyDesc x coeffsDesc| ≤
      gamma fp (2 * coeffsDesc.length) * polyDescAbs x coeffsDesc := by
  obtain ⟨pairs, hpairs, hpairsBound, hfl⟩ :=
    fl_hornerFoldFromZeroDesc_backward_error_coefficients fp x coeffsDesc
      hvalid
  have hpert :=
    abs_polyDescPairsPerturbed_sub_polyDescPairs_le x
      (gamma fp (2 * coeffsDesc.length)) (gamma_nonneg fp hvalid)
      pairs hpairsBound
  have hpoly :
      polyDescPairs x pairs = polyDesc x coeffsDesc := by
    rw [polyDescPairs_eq_polyDesc_map_fst, hpairs]
  have habs :
      polyDescPairsAbs x pairs = polyDescAbs x coeffsDesc := by
    rw [polyDescPairsAbs_eq_polyDescAbs_map_fst, hpairs]
  simpa [hfl, hpoly, habs] using hpert

/-- The direct forward local budget supplied by the abstract `FPModel` for one
rounded Horner step. -/
noncomputable def fl_hornerStepForwardErrorBudget
    (fp : FPModel) (x y a : ℝ) : ℝ :=
  fp.u * (|x| * |y| + |fp.fl_mul x y + a|)

lemma fl_hornerStepForwardErrorBudget_nonneg
    (fp : FPModel) (x y a : ℝ) :
    0 ≤ fl_hornerStepForwardErrorBudget fp x y a := by
  unfold fl_hornerStepForwardErrorBudget
  exact mul_nonneg fp.u_nonneg
    (add_nonneg
      (mul_nonneg (abs_nonneg x) (abs_nonneg y))
      (abs_nonneg _))

/-- Local rounded-data bound for the one-step Horner forward-error budget.
This is the first ingredient for replacing the recursive quotient budget in
(5.5)-(5.7) by a first-order source-shaped majorant. -/
lemma fl_hornerStepForwardErrorBudget_le_abs_inputs
    (fp : FPModel) (x y a : ℝ) :
    fl_hornerStepForwardErrorBudget fp x y a ≤
      fp.u * ((2 + fp.u) * (|x| * |y|) + |a|) := by
  obtain ⟨δ, hδ, hfl⟩ := fp.model_mul x y
  have hdelta_abs : |1 + δ| ≤ 1 + fp.u := by
    have htri : |1 + δ| ≤ |(1 : ℝ)| + |δ| := abs_add_le _ _
    norm_num at htri
    linarith
  have hxy_nonneg : 0 ≤ |x| * |y| :=
    mul_nonneg (abs_nonneg x) (abs_nonneg y)
  have hfl_abs : |fp.fl_mul x y| ≤ |x| * |y| * (1 + fp.u) := by
    calc
      |fp.fl_mul x y| = |x| * |y| * |1 + δ| := by
        rw [hfl, abs_mul, abs_mul]
      _ ≤ |x| * |y| * (1 + fp.u) :=
        mul_le_mul_of_nonneg_left hdelta_abs hxy_nonneg
  have hpre :
      |fp.fl_mul x y + a| ≤ |x| * |y| * (1 + fp.u) + |a| :=
    le_trans (abs_add_le _ _) (add_le_add hfl_abs (le_refl _))
  have hinside :
      |x| * |y| + |fp.fl_mul x y + a| ≤
        (2 + fp.u) * (|x| * |y|) + |a| := by
    nlinarith [hpre, hxy_nonneg, fp.u_nonneg]
  unfold fl_hornerStepForwardErrorBudget
  exact mul_le_mul_of_nonneg_left hinside fp.u_nonneg

lemma fl_hornerStepForwardErrorBudget_le_exact_abs_plus_error
    (fp : FPModel) (x yhat y a eps : ℝ)
    (_heps_nonneg : 0 ≤ eps) (herr : |yhat - y| ≤ eps) :
    fl_hornerStepForwardErrorBudget fp x yhat a ≤
      fp.u * ((2 + fp.u) * (|x| * (|y| + eps)) + |a|) := by
  have hbase :=
    fl_hornerStepForwardErrorBudget_le_abs_inputs fp x yhat a
  have hyhat : |yhat| ≤ |y| + eps := by
    have htri : |yhat| ≤ |y| + |yhat - y| := by
      calc
        |yhat| = |y + (yhat - y)| := by
          congr 1
          ring
        _ ≤ |y| + |yhat - y| := abs_add_le _ _
    linarith
  have hprod :
      |x| * |yhat| ≤ |x| * (|y| + eps) :=
    mul_le_mul_of_nonneg_left hyhat (abs_nonneg x)
  have hcoef : 0 ≤ 2 + fp.u := by nlinarith [fp.u_nonneg]
  have hinside :
      (2 + fp.u) * (|x| * |yhat|) + |a| ≤
        (2 + fp.u) * (|x| * (|y| + eps)) + |a| := by
    have h :=
      add_le_add_right (mul_le_mul_of_nonneg_left hprod hcoef) |a|
    simpa [add_comm, add_left_comm, add_assoc] using h
  exact le_trans hbase (mul_le_mul_of_nonneg_left hinside fp.u_nonneg)

lemma fl_hornerStep_error_bound_of_accumulator_error
    (fp : FPModel) (x yhat y a eps : ℝ)
    (heps : |yhat - y| ≤ eps) :
    |fl_hornerStep fp x yhat a - hornerStep x y a| ≤
      fl_hornerStepForwardErrorBudget fp x yhat a + |x| * eps := by
  have hlocal :
      |fl_hornerStep fp x yhat a - hornerStep x yhat a| ≤
        fl_hornerStepForwardErrorBudget fp x yhat a := by
    simpa [fl_hornerStepForwardErrorBudget]
      using fl_hornerStep_forward_local_error_bound fp x yhat a
  have hexact :
      |hornerStep x yhat a - hornerStep x y a| ≤ |x| * eps := by
    have hdiff :
        hornerStep x yhat a - hornerStep x y a =
          x * (yhat - y) := by
      unfold hornerStep
      ring
    rw [hdiff, abs_mul]
    exact mul_le_mul_of_nonneg_left heps (abs_nonneg x)
  have htri :
      |fl_hornerStep fp x yhat a - hornerStep x y a| ≤
        |fl_hornerStep fp x yhat a - hornerStep x yhat a| +
          |hornerStep x yhat a - hornerStep x y a| := by
    have hsplit :
        fl_hornerStep fp x yhat a - hornerStep x y a =
          (fl_hornerStep fp x yhat a - hornerStep x yhat a) +
            (hornerStep x yhat a - hornerStep x y a) := by
      ring
    rw [hsplit]
    exact abs_add_le _ _
  exact le_trans htri (add_le_add hlocal hexact)

/-- Higham, 2nd ed., Chapter 5, Algorithm 5.1:
one exact running-bound state update.  The state is `(y, mu)` before the
final scaling by the unit roundoff. -/
def hornerRunningStep (x : ℝ) (state : ℝ × ℝ) (a : ℝ) : ℝ × ℝ :=
  let y := hornerStep x state.1 a
  (y, |x| * state.2 + |y|)

/-- Higham, 2nd ed., Chapter 5, Algorithm 5.1:
exact state corresponding to the running error-bound recurrence, before the
last assignment `mu = u * (2*mu - |y|)`. -/
noncomputable def hornerRunningState (x : ℝ) : List ℝ → ℝ × ℝ
  | [] => (0, 0)
  | a :: rest => rest.foldl (hornerRunningStep x) (a, |a| / 2)

/-- Higham, 2nd ed., Chapter 5, Algorithm 5.1:
the final exact running-bound quantity `u * (2*mu - |y|)` attached to the
exact running-bound state. -/
noncomputable def hornerRunningBound (u x : ℝ) (coeffsDesc : List ℝ) : ℝ :=
  let state := hornerRunningState x coeffsDesc
  u * (2 * state.2 - |state.1|)

lemma hornerRunningFold_fst_eq (x : ℝ) :
    ∀ (rest : List ℝ) (y mu : ℝ),
      (rest.foldl (hornerRunningStep x) (y, mu)).1 =
        rest.foldl (hornerStep x) y := by
  intro rest
  induction rest with
  | nil =>
      intro y mu
      rfl
  | cons a rest ih =>
      intro y mu
      simp [List.foldl, hornerRunningStep, hornerStep, ih]

/-- The running-bound state in Algorithm 5.1 carries the same exact Horner
value in its first component. -/
theorem hornerRunningState_fst_eq_hornerDesc (x : ℝ)
    (coeffsDesc : List ℝ) :
    (hornerRunningState x coeffsDesc).1 = hornerDesc x coeffsDesc := by
  cases coeffsDesc with
  | nil => rfl
  | cons a rest =>
      simpa [hornerRunningState, hornerDesc]
        using hornerRunningFold_fst_eq x rest a (|a| / 2)

lemma hornerRunningStep_snd_nonneg (x a : ℝ) {state : ℝ × ℝ}
    (hmu : 0 ≤ state.2) :
    0 ≤ (hornerRunningStep x state a).2 := by
  simp [hornerRunningStep]
  exact add_nonneg (mul_nonneg (abs_nonneg x) hmu) (abs_nonneg _)

lemma hornerRunningStep_abs_fst_le_two_snd (x a : ℝ)
    {state : ℝ × ℝ} (hmu : 0 ≤ state.2) :
    |(hornerRunningStep x state a).1| ≤
      2 * (hornerRunningStep x state a).2 := by
  simp [hornerRunningStep]
  have hterm : 0 ≤ |x| * state.2 :=
    mul_nonneg (abs_nonneg x) hmu
  have hy : 0 ≤ |hornerStep x state.1 a| := abs_nonneg _
  nlinarith

lemma hornerRunningFold_snd_nonneg (x : ℝ) :
    ∀ (rest : List ℝ) (state : ℝ × ℝ),
      0 ≤ state.2 →
      0 ≤ (rest.foldl (hornerRunningStep x) state).2 := by
  intro rest
  induction rest with
  | nil =>
      intro state hmu
      simpa using hmu
  | cons a rest ih =>
      intro state hmu
      exact ih (hornerRunningStep x state a)
        (hornerRunningStep_snd_nonneg x a hmu)

/-- The unscaled running-bound accumulator in Algorithm 5.1 is nonnegative. -/
theorem hornerRunningState_mu_nonneg (x : ℝ) (coeffsDesc : List ℝ) :
    0 ≤ (hornerRunningState x coeffsDesc).2 := by
  cases coeffsDesc with
  | nil =>
      simp [hornerRunningState]
  | cons a rest =>
      have hinit : 0 ≤ |a| / 2 := by positivity
      simpa [hornerRunningState]
        using hornerRunningFold_snd_nonneg x rest (a, |a| / 2) hinit

lemma hornerRunningFold_abs_fst_le_two_snd (x : ℝ) :
    ∀ (rest : List ℝ) (state : ℝ × ℝ),
      0 ≤ state.2 →
      |state.1| ≤ 2 * state.2 →
      |(rest.foldl (hornerRunningStep x) state).1| ≤
        2 * (rest.foldl (hornerRunningStep x) state).2 := by
  intro rest
  induction rest with
  | nil =>
      intro state _ hstate
      simpa using hstate
  | cons a rest ih =>
      intro state hmu _hstate
      exact ih (hornerRunningStep x state a)
        (hornerRunningStep_snd_nonneg x a hmu)
        (hornerRunningStep_abs_fst_le_two_snd x a hmu)

/-- In Algorithm 5.1's exact running-bound state, the final value satisfies
`|y| <= 2*mu`.  This makes the final quantity `u*(2*mu - |y|)` nonnegative
whenever `u >= 0`. -/
theorem hornerRunningState_abs_fst_le_two_mu (x : ℝ)
    (coeffsDesc : List ℝ) :
    |(hornerRunningState x coeffsDesc).1| ≤
      2 * (hornerRunningState x coeffsDesc).2 := by
  cases coeffsDesc with
  | nil =>
      simp [hornerRunningState]
  | cons a rest =>
      have hinit_mu : 0 ≤ |a| / 2 := by positivity
      have hinit_abs : |(a, |a| / 2).1| ≤ 2 * (a, |a| / 2).2 := by
        change |a| ≤ 2 * (|a| / 2)
        have h : (2 : ℝ) * (|a| / 2) = |a| := by ring
        rw [h]
      simpa [hornerRunningState]
        using hornerRunningFold_abs_fst_le_two_snd x rest (a, |a| / 2)
          hinit_mu hinit_abs

/-- The Algorithm 5.1 running-bound quantity is nonnegative for nonnegative
unit roundoff. -/
theorem hornerRunningBound_nonneg {u x : ℝ} (hu : 0 ≤ u)
    (coeffsDesc : List ℝ) :
    0 ≤ hornerRunningBound u x coeffsDesc := by
  unfold hornerRunningBound
  let state := hornerRunningState x coeffsDesc
  have hstate :
      |state.1| ≤ 2 * state.2 := by
    simpa [state] using hornerRunningState_abs_fst_le_two_mu x coeffsDesc
  have hinner : 0 ≤ 2 * state.2 - |state.1| := by
    linarith
  exact mul_nonneg hu hinner

lemma fl_hornerExactFold_eq (u0 : ℝ) (hu0 : 0 ≤ u0) (x : ℝ) :
    ∀ (rest : List ℝ) (y : ℝ),
      rest.foldl (fl_hornerStep (FPModel.exactWithUnitRoundoff u0 hu0) x) y =
        rest.foldl (hornerStep x) y := by
  intro rest
  induction rest with
  | nil =>
      intro y
      rfl
  | cons a rest ih =>
      intro y
      simpa [List.foldl, fl_hornerStep, hornerStep,
        FPModel.exactWithUnitRoundoff] using ih (x * y + a)

/-- Exact arithmetic, packaged as an `FPModel`, evaluates Horner's method as
the exact Horner recurrence. -/
theorem fl_hornerDesc_exactWithUnitRoundoff (u0 : ℝ) (hu0 : 0 ≤ u0)
    (x : ℝ) (coeffsDesc : List ℝ) :
    fl_hornerDesc (FPModel.exactWithUnitRoundoff u0 hu0) x coeffsDesc =
      hornerDesc x coeffsDesc := by
  cases coeffsDesc with
  | nil => rfl
  | cons a rest =>
      simpa [fl_hornerDesc, hornerDesc]
        using fl_hornerExactFold_eq u0 hu0 x rest a

end NumStability
